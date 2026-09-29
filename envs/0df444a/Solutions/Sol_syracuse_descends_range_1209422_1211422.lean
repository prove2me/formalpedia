-- Prove2me | solution 1 for syracuse_descends_range_1209422_1211422
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:48:34.250378+00:00
-- url     : https://prove2.me/submissions/61c0936d-2025-49ff-b1a2-14901678b6f7

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


theorem B3063845 : Blo 1209422 3063845 := bbase (se 4 (by rfl) ⟨287235, by rfl⟩ : syracuseStep 3063845 = 574471) (by norm_num)
theorem B1531973 : Blo 1209422 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B1532029 : Blo 1209422 1532029 := bbase (se 3 (by rfl) ⟨287255, by rfl⟩ : syracuseStep 1532029 = 574511) (by norm_num)
theorem B1532125 : Blo 1209422 1532125 := bbase (se 3 (by rfl) ⟨287273, by rfl⟩ : syracuseStep 1532125 = 574547) (by norm_num)
theorem B4088069 : Blo 1209422 4088069 := bbase (se 4 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 4088069 = 766513) (by norm_num)
theorem B6127973 : Blo 1209422 6127973 := bbase (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) (by norm_num)
theorem B3064189 : Blo 1209422 3064189 := bbase (se 3 (by rfl) ⟨574535, by rfl⟩ : syracuseStep 3064189 = 1149071) (by norm_num)
theorem B1532297 : Blo 1209422 1532297 := bbase (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) (by norm_num)
theorem B19620245 : Blo 1209422 19620245 := bbase (se 6 (by rfl) ⟨459849, by rfl⟩ : syracuseStep 19620245 = 919699) (by norm_num)
theorem B2761133 : Blo 1209422 2761133 := bbase (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) (by norm_num)
theorem B1532353 : Blo 1209422 1532353 := bbase (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) (by norm_num)
theorem B3064301 : Blo 1209422 3064301 := bbase (se 3 (by rfl) ⟨574556, by rfl⟩ : syracuseStep 3064301 = 1149113) (by norm_num)
theorem B6291989 : Blo 1209422 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B1532449 : Blo 1209422 1532449 := bbase (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) (by norm_num)
theorem B3064493 : Blo 1209422 3064493 := bbase (se 3 (by rfl) ⟨574592, by rfl⟩ : syracuseStep 3064493 = 1149185) (by norm_num)
theorem B4088501 : Blo 1209422 4088501 := bbase (se 5 (by rfl) ⟨191648, by rfl⟩ : syracuseStep 4088501 = 383297) (by norm_num)
theorem B1532621 : Blo 1209422 1532621 := bbase (se 3 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 1532621 = 574733) (by norm_num)
theorem B1360633 : Blo 1209422 1360633 := bbase (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) (by norm_num)
theorem B1532677 : Blo 1209422 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B1360669 : Blo 1209422 1360669 := bbase (se 3 (by rfl) ⟨255125, by rfl⟩ : syracuseStep 1360669 = 510251) (by norm_num)
theorem B1360705 : Blo 1209422 1360705 := bbase (se 2 (by rfl) ⟨510264, by rfl⟩ : syracuseStep 1360705 = 1020529) (by norm_num)
theorem B1360741 : Blo 1209422 1360741 := bbase (se 4 (by rfl) ⟨127569, by rfl⟩ : syracuseStep 1360741 = 255139) (by norm_num)
theorem B2909029 : Blo 1209422 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B1532773 : Blo 1209422 1532773 := bbase (se 4 (by rfl) ⟨143697, by rfl⟩ : syracuseStep 1532773 = 287395) (by norm_num)
theorem B1360777 : Blo 1209422 1360777 := bbase (se 2 (by rfl) ⟨510291, by rfl⟩ : syracuseStep 1360777 = 1020583) (by norm_num)
theorem B1360813 : Blo 1209422 1360813 := bbase (se 3 (by rfl) ⟨255152, by rfl⟩ : syracuseStep 1360813 = 510305) (by norm_num)
theorem B1360849 : Blo 1209422 1360849 := bbase (se 2 (by rfl) ⟨510318, by rfl⟩ : syracuseStep 1360849 = 1020637) (by norm_num)
theorem B4596709 : Blo 1209422 4596709 := bbase (se 4 (by rfl) ⟨430941, by rfl⟩ : syracuseStep 4596709 = 861883) (by norm_num)
theorem B1360885 : Blo 1209422 1360885 := bbase (se 5 (by rfl) ⟨63791, by rfl⟩ : syracuseStep 1360885 = 127583) (by norm_num)
theorem B3064837 : Blo 1209422 3064837 := bbase (se 4 (by rfl) ⟨287328, by rfl⟩ : syracuseStep 3064837 = 574657) (by norm_num)
theorem B1532945 : Blo 1209422 1532945 := bbase (se 2 (by rfl) ⟨574854, by rfl⟩ : syracuseStep 1532945 = 1149709) (by norm_num)
theorem B6898709 : Blo 1209422 6898709 := bbase (se 6 (by rfl) ⟨161688, by rfl⟩ : syracuseStep 6898709 = 323377) (by norm_num)
theorem B1360921 : Blo 1209422 1360921 := bbase (se 2 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 1360921 = 1020691) (by norm_num)
theorem B1360957 : Blo 1209422 1360957 := bbase (se 3 (by rfl) ⟨255179, by rfl⟩ : syracuseStep 1360957 = 510359) (by norm_num)
theorem B1533001 : Blo 1209422 1533001 := bbase (se 2 (by rfl) ⟨574875, by rfl⟩ : syracuseStep 1533001 = 1149751) (by norm_num)
theorem B1360993 : Blo 1209422 1360993 := bbase (se 2 (by rfl) ⟨510372, by rfl⟩ : syracuseStep 1360993 = 1020745) (by norm_num)
theorem B3064949 : Blo 1209422 3064949 := bbase (se 5 (by rfl) ⟨143669, by rfl⟩ : syracuseStep 3064949 = 287339) (by norm_num)
theorem B1361029 : Blo 1209422 1361029 := bbase (se 4 (by rfl) ⟨127596, by rfl⟩ : syracuseStep 1361029 = 255193) (by norm_num)
theorem B2040997 : Blo 1209422 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B1746085 : Blo 1209422 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B1361065 : Blo 1209422 1361065 := bbase (se 2 (by rfl) ⟨510399, by rfl⟩ : syracuseStep 1361065 = 1020799) (by norm_num)
theorem B1533097 : Blo 1209422 1533097 := bbase (se 2 (by rfl) ⟨574911, by rfl⟩ : syracuseStep 1533097 = 1149823) (by norm_num)
theorem B4359365 : Blo 1209422 4359365 := bbase (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) (by norm_num)
theorem B5817541 : Blo 1209422 5817541 := bbase (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) (by norm_num)
theorem B1361101 : Blo 1209422 1361101 := bbase (se 3 (by rfl) ⟨255206, by rfl⟩ : syracuseStep 1361101 = 510413) (by norm_num)
theorem B5817557 : Blo 1209422 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B1361137 : Blo 1209422 1361137 := bbase (se 2 (by rfl) ⟨510426, by rfl⟩ : syracuseStep 1361137 = 1020853) (by norm_num)
theorem B2041085 : Blo 1209422 2041085 := bbase (se 3 (by rfl) ⟨382703, by rfl⟩ : syracuseStep 2041085 = 765407) (by norm_num)
theorem B1361173 : Blo 1209422 1361173 := bbase (se 6 (by rfl) ⟨31902, by rfl⟩ : syracuseStep 1361173 = 63805) (by norm_num)
theorem B4597013 : Blo 1209422 4597013 := bbase (se 6 (by rfl) ⟨107742, by rfl⟩ : syracuseStep 4597013 = 215485) (by norm_num)
theorem B3065141 : Blo 1209422 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B1361209 : Blo 1209422 1361209 := bbase (se 2 (by rfl) ⟨510453, by rfl⟩ : syracuseStep 1361209 = 1020907) (by norm_num)
theorem B1361245 : Blo 1209422 1361245 := bbase (se 3 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 1361245 = 510467) (by norm_num)
theorem B2041213 : Blo 1209422 2041213 := bbase (se 3 (by rfl) ⟨382727, by rfl⟩ : syracuseStep 2041213 = 765455) (by norm_num)
theorem B1361281 : Blo 1209422 1361281 := bbase (se 2 (by rfl) ⟨510480, by rfl⟩ : syracuseStep 1361281 = 1020961) (by norm_num)
theorem B3876245 : Blo 1209422 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B1361317 : Blo 1209422 1361317 := bbase (se 4 (by rfl) ⟨127623, by rfl⟩ : syracuseStep 1361317 = 255247) (by norm_num)
theorem B2721221 : Blo 1209422 2721221 := bbase (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) (by norm_num)
theorem B1361353 : Blo 1209422 1361353 := bbase (se 2 (by rfl) ⟨510507, by rfl⟩ : syracuseStep 1361353 = 1021015) (by norm_num)
theorem B2909645 : Blo 1209422 2909645 := bbase (se 3 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 2909645 = 1091117) (by norm_num)
theorem B2041301 : Blo 1209422 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B4359653 : Blo 1209422 4359653 := bbase (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) (by norm_num)
theorem B1361389 : Blo 1209422 1361389 := bbase (se 3 (by rfl) ⟨255260, by rfl⟩ : syracuseStep 1361389 = 510521) (by norm_num)
theorem B7366133 : Blo 1209422 7366133 := bbase (se 5 (by rfl) ⟨345287, by rfl⟩ : syracuseStep 7366133 = 690575) (by norm_num)
theorem B2909701 : Blo 1209422 2909701 := bbase (se 4 (by rfl) ⟨272784, by rfl⟩ : syracuseStep 2909701 = 545569) (by norm_num)
theorem B2721293 : Blo 1209422 2721293 := bbase (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) (by norm_num)
theorem B1361425 : Blo 1209422 1361425 := bbase (se 2 (by rfl) ⟨510534, by rfl⟩ : syracuseStep 1361425 = 1021069) (by norm_num)
theorem B1361461 : Blo 1209422 1361461 := bbase (se 5 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 1361461 = 127637) (by norm_num)
theorem B2721365 : Blo 1209422 2721365 := bbase (se 8 (by rfl) ⟨15945, by rfl⟩ : syracuseStep 2721365 = 31891) (by norm_num)
theorem B2041429 : Blo 1209422 2041429 := bbase (se 8 (by rfl) ⟨11961, by rfl⟩ : syracuseStep 2041429 = 23923) (by norm_num)
theorem B1361497 : Blo 1209422 1361497 := bbase (se 2 (by rfl) ⟨510561, by rfl⟩ : syracuseStep 1361497 = 1021123) (by norm_num)
theorem B6129269 : Blo 1209422 6129269 := bbase (se 5 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 6129269 = 574619) (by norm_num)
theorem B1361533 : Blo 1209422 1361533 := bbase (se 3 (by rfl) ⟨255287, by rfl⟩ : syracuseStep 1361533 = 510575) (by norm_num)
theorem B3065485 : Blo 1209422 3065485 := bbase (se 3 (by rfl) ⟨574778, by rfl⟩ : syracuseStep 3065485 = 1149557) (by norm_num)
theorem B2721437 : Blo 1209422 2721437 := bbase (se 3 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 2721437 = 1020539) (by norm_num)
theorem B1361569 : Blo 1209422 1361569 := bbase (se 2 (by rfl) ⟨510588, by rfl⟩ : syracuseStep 1361569 = 1021177) (by norm_num)
theorem B2041517 : Blo 1209422 2041517 := bbase (se 3 (by rfl) ⟨382784, by rfl⟩ : syracuseStep 2041517 = 765569) (by norm_num)
theorem B1361605 : Blo 1209422 1361605 := bbase (se 4 (by rfl) ⟨127650, by rfl⟩ : syracuseStep 1361605 = 255301) (by norm_num)
theorem B2721509 : Blo 1209422 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B1361641 : Blo 1209422 1361641 := bbase (se 2 (by rfl) ⟨510615, by rfl⟩ : syracuseStep 1361641 = 1021231) (by norm_num)
theorem B3065597 : Blo 1209422 3065597 := bbase (se 3 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 3065597 = 1149599) (by norm_num)
theorem B1361677 : Blo 1209422 1361677 := bbase (se 3 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 1361677 = 510629) (by norm_num)
theorem B2721581 : Blo 1209422 2721581 := bbase (se 3 (by rfl) ⟨510296, by rfl⟩ : syracuseStep 2721581 = 1020593) (by norm_num)
theorem B2041645 : Blo 1209422 2041645 := bbase (se 3 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 2041645 = 765617) (by norm_num)
theorem B1361713 : Blo 1209422 1361713 := bbase (se 2 (by rfl) ⟨510642, by rfl⟩ : syracuseStep 1361713 = 1021285) (by norm_num)
theorem B1361749 : Blo 1209422 1361749 := bbase (se 9 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 1361749 = 7979) (by norm_num)
theorem B2328421 : Blo 1209422 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B2721653 : Blo 1209422 2721653 := bbase (se 5 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 2721653 = 255155) (by norm_num)
theorem B1361785 : Blo 1209422 1361785 := bbase (se 2 (by rfl) ⟨510669, by rfl⟩ : syracuseStep 1361785 = 1021339) (by norm_num)
theorem B2041733 : Blo 1209422 2041733 := bbase (se 4 (by rfl) ⟨191412, by rfl⟩ : syracuseStep 2041733 = 382825) (by norm_num)
theorem B1361821 : Blo 1209422 1361821 := bbase (se 3 (by rfl) ⟨255341, by rfl⟩ : syracuseStep 1361821 = 510683) (by norm_num)
theorem B2721725 : Blo 1209422 2721725 := bbase (se 3 (by rfl) ⟨510323, by rfl⟩ : syracuseStep 2721725 = 1020647) (by norm_num)
theorem B3065789 : Blo 1209422 3065789 := bbase (se 3 (by rfl) ⟨574835, by rfl⟩ : syracuseStep 3065789 = 1149671) (by norm_num)
theorem B1361857 : Blo 1209422 1361857 := bbase (se 2 (by rfl) ⟨510696, by rfl⟩ : syracuseStep 1361857 = 1021393) (by norm_num)
theorem B1361893 : Blo 1209422 1361893 := bbase (se 4 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 1361893 = 255355) (by norm_num)
theorem B2721797 : Blo 1209422 2721797 := bbase (se 4 (by rfl) ⟨255168, by rfl⟩ : syracuseStep 2721797 = 510337) (by norm_num)
theorem B2041861 : Blo 1209422 2041861 := bbase (se 4 (by rfl) ⟨191424, by rfl⟩ : syracuseStep 2041861 = 382849) (by norm_num)
theorem B1361929 : Blo 1209422 1361929 := bbase (se 2 (by rfl) ⟨510723, by rfl⟩ : syracuseStep 1361929 = 1021447) (by norm_num)
theorem B1361965 : Blo 1209422 1361965 := bbase (se 3 (by rfl) ⟨255368, by rfl⟩ : syracuseStep 1361965 = 510737) (by norm_num)
theorem B2181181 : Blo 1209422 2181181 := bbase (se 3 (by rfl) ⟨408971, by rfl⟩ : syracuseStep 2181181 = 817943) (by norm_num)
theorem B2721869 : Blo 1209422 2721869 := bbase (se 3 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 2721869 = 1020701) (by norm_num)
theorem B1362001 : Blo 1209422 1362001 := bbase (se 2 (by rfl) ⟨510750, by rfl⟩ : syracuseStep 1362001 = 1021501) (by norm_num)
theorem B2041949 : Blo 1209422 2041949 := bbase (se 3 (by rfl) ⟨382865, by rfl⟩ : syracuseStep 2041949 = 765731) (by norm_num)
theorem B1722485 : Blo 1209422 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1362037 : Blo 1209422 1362037 := bbase (se 5 (by rfl) ⟨63845, by rfl⟩ : syracuseStep 1362037 = 127691) (by norm_num)
theorem B2721941 : Blo 1209422 2721941 := bbase (se 6 (by rfl) ⟨63795, by rfl⟩ : syracuseStep 2721941 = 127591) (by norm_num)
theorem B1362073 : Blo 1209422 1362073 := bbase (se 2 (by rfl) ⟨510777, by rfl⟩ : syracuseStep 1362073 = 1021555) (by norm_num)
theorem B1362109 : Blo 1209422 1362109 := bbase (se 3 (by rfl) ⟨255395, by rfl⟩ : syracuseStep 1362109 = 510791) (by norm_num)
theorem B2181325 : Blo 1209422 2181325 := bbase (se 3 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 2181325 = 817997) (by norm_num)
theorem B2722013 : Blo 1209422 2722013 := bbase (se 3 (by rfl) ⟨510377, by rfl⟩ : syracuseStep 2722013 = 1020755) (by norm_num)
theorem B2042077 : Blo 1209422 2042077 := bbase (se 3 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 2042077 = 765779) (by norm_num)
theorem B1362145 : Blo 1209422 1362145 := bbase (se 2 (by rfl) ⟨510804, by rfl⟩ : syracuseStep 1362145 = 1021609) (by norm_num)
theorem B1362181 : Blo 1209422 1362181 := bbase (se 4 (by rfl) ⟨127704, by rfl⟩ : syracuseStep 1362181 = 255409) (by norm_num)
theorem B3877141 : Blo 1209422 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B3066133 : Blo 1209422 3066133 := bbase (se 6 (by rfl) ⟨71862, by rfl⟩ : syracuseStep 3066133 = 143725) (by norm_num)
theorem B2722085 : Blo 1209422 2722085 := bbase (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) (by norm_num)
theorem B1362217 : Blo 1209422 1362217 := bbase (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) (by norm_num)
theorem B2042165 : Blo 1209422 2042165 := bbase (se 5 (by rfl) ⟨95726, by rfl⟩ : syracuseStep 2042165 = 191453) (by norm_num)
theorem B4360517 : Blo 1209422 4360517 := bbase (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) (by norm_num)
theorem B1362253 : Blo 1209422 1362253 := bbase (se 3 (by rfl) ⟨255422, by rfl⟩ : syracuseStep 1362253 = 510845) (by norm_num)
theorem B4082021 : Blo 1209422 4082021 := bbase (se 4 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 4082021 = 765379) (by norm_num)
theorem B2722157 : Blo 1209422 2722157 := bbase (se 3 (by rfl) ⟨510404, by rfl⟩ : syracuseStep 2722157 = 1020809) (by norm_num)
theorem B1362289 : Blo 1209422 1362289 := bbase (se 2 (by rfl) ⟨510858, by rfl⟩ : syracuseStep 1362289 = 1021717) (by norm_num)
theorem B3066245 : Blo 1209422 3066245 := bbase (se 4 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 3066245 = 574921) (by norm_num)
theorem B1362325 : Blo 1209422 1362325 := bbase (se 6 (by rfl) ⟨31929, by rfl⟩ : syracuseStep 1362325 = 63859) (by norm_num)
theorem B2394541 : Blo 1209422 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B2722229 : Blo 1209422 2722229 := bbase (se 5 (by rfl) ⟨127604, by rfl⟩ : syracuseStep 2722229 = 255209) (by norm_num)
theorem B2042293 : Blo 1209422 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B1362361 : Blo 1209422 1362361 := bbase (se 2 (by rfl) ⟨510885, by rfl⟩ : syracuseStep 1362361 = 1021771) (by norm_num)
theorem B3107261 : Blo 1209422 3107261 := bbase (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) (by norm_num)
theorem B1362397 : Blo 1209422 1362397 := bbase (se 3 (by rfl) ⟨255449, by rfl⟩ : syracuseStep 1362397 = 510899) (by norm_num)
theorem B2722301 : Blo 1209422 2722301 := bbase (se 3 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 2722301 = 1020863) (by norm_num)
theorem B1362433 : Blo 1209422 1362433 := bbase (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) (by norm_num)
theorem B2042381 : Blo 1209422 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B4975141 : Blo 1209422 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B1362469 : Blo 1209422 1362469 := bbase (se 4 (by rfl) ⟨127731, by rfl⟩ : syracuseStep 1362469 = 255463) (by norm_num)
theorem B2722373 : Blo 1209422 2722373 := bbase (se 4 (by rfl) ⟨255222, by rfl⟩ : syracuseStep 2722373 = 510445) (by norm_num)
theorem B1362505 : Blo 1209422 1362505 := bbase (se 2 (by rfl) ⟨510939, by rfl⟩ : syracuseStep 1362505 = 1021879) (by norm_num)
theorem B1362541 : Blo 1209422 1362541 := bbase (se 3 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 1362541 = 510953) (by norm_num)
theorem B5171845 : Blo 1209422 5171845 := bbase (se 4 (by rfl) ⟨484860, by rfl⟩ : syracuseStep 5171845 = 969721) (by norm_num)
theorem B2583181 : Blo 1209422 2583181 := bbase (se 3 (by rfl) ⟨484346, by rfl⟩ : syracuseStep 2583181 = 968693) (by norm_num)
theorem B2722445 : Blo 1209422 2722445 := bbase (se 3 (by rfl) ⟨510458, by rfl⟩ : syracuseStep 2722445 = 1020917) (by norm_num)
theorem B2042509 : Blo 1209422 2042509 := bbase (se 3 (by rfl) ⟨382970, by rfl⟩ : syracuseStep 2042509 = 765941) (by norm_num)
theorem B1362577 : Blo 1209422 1362577 := bbase (se 2 (by rfl) ⟨510966, by rfl⟩ : syracuseStep 1362577 = 1021933) (by norm_num)
theorem B1723037 : Blo 1209422 1723037 := bbase (se 3 (by rfl) ⟨323069, by rfl⟩ : syracuseStep 1723037 = 646139) (by norm_num)
theorem B3877541 : Blo 1209422 3877541 := bbase (se 4 (by rfl) ⟨363519, by rfl⟩ : syracuseStep 3877541 = 727039) (by norm_num)
theorem B1362613 : Blo 1209422 1362613 := bbase (se 5 (by rfl) ⟨63872, by rfl⟩ : syracuseStep 1362613 = 127745) (by norm_num)
theorem B2296525 : Blo 1209422 2296525 := bbase (se 3 (by rfl) ⟨430598, by rfl⟩ : syracuseStep 2296525 = 861197) (by norm_num)
theorem B2722517 : Blo 1209422 2722517 := bbase (se 7 (by rfl) ⟨31904, by rfl⟩ : syracuseStep 2722517 = 63809) (by norm_num)
theorem B1362649 : Blo 1209422 1362649 := bbase (se 2 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 1362649 = 1021987) (by norm_num)
theorem B2042597 : Blo 1209422 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B1362685 : Blo 1209422 1362685 := bbase (se 3 (by rfl) ⟨255503, by rfl⟩ : syracuseStep 1362685 = 511007) (by norm_num)
theorem B4082453 : Blo 1209422 4082453 := bbase (se 6 (by rfl) ⟨95682, by rfl⟩ : syracuseStep 4082453 = 191365) (by norm_num)
theorem B2722589 : Blo 1209422 2722589 := bbase (se 3 (by rfl) ⟨510485, by rfl⟩ : syracuseStep 2722589 = 1020971) (by norm_num)
theorem B1362721 : Blo 1209422 1362721 := bbase (se 2 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 1362721 = 1022041) (by norm_num)
theorem B1362757 : Blo 1209422 1362757 := bbase (se 4 (by rfl) ⟨127758, by rfl⟩ : syracuseStep 1362757 = 255517) (by norm_num)
theorem B2796373 : Blo 1209422 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B2296669 : Blo 1209422 2296669 := bbase (se 3 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 2296669 = 861251) (by norm_num)
theorem B2722661 : Blo 1209422 2722661 := bbase (se 4 (by rfl) ⟨255249, by rfl⟩ : syracuseStep 2722661 = 510499) (by norm_num)
theorem B2042725 : Blo 1209422 2042725 := bbase (se 4 (by rfl) ⟨191505, by rfl⟩ : syracuseStep 2042725 = 383011) (by norm_num)
theorem B1362793 : Blo 1209422 1362793 := bbase (se 2 (by rfl) ⟨511047, by rfl⟩ : syracuseStep 1362793 = 1022095) (by norm_num)
theorem B4361093 : Blo 1209422 4361093 := bbase (se 4 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 4361093 = 817705) (by norm_num)
theorem B6130565 : Blo 1209422 6130565 := bbase (se 4 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 6130565 = 1149481) (by norm_num)
theorem B1362829 : Blo 1209422 1362829 := bbase (se 3 (by rfl) ⟨255530, by rfl⟩ : syracuseStep 1362829 = 511061) (by norm_num)
theorem B2722733 : Blo 1209422 2722733 := bbase (se 3 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 2722733 = 1021025) (by norm_num)
theorem B2042813 : Blo 1209422 2042813 := bbase (se 3 (by rfl) ⟨383027, by rfl⟩ : syracuseStep 2042813 = 766055) (by norm_num)
theorem B2722805 : Blo 1209422 2722805 := bbase (se 5 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 2722805 = 255263) (by norm_num)
theorem B2182133 : Blo 1209422 2182133 := bbase (se 5 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 2182133 = 204575) (by norm_num)
theorem B2296829 : Blo 1209422 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B2722877 : Blo 1209422 2722877 := bbase (se 3 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 2722877 = 1021079) (by norm_num)
theorem B2042941 : Blo 1209422 2042941 := bbase (se 3 (by rfl) ⟨383051, by rfl⟩ : syracuseStep 2042941 = 766103) (by norm_num)
theorem B1379449 : Blo 1209422 1379449 := bbase (se 2 (by rfl) ⟨517293, by rfl⟩ : syracuseStep 1379449 = 1034587) (by norm_num)
theorem B2722949 : Blo 1209422 2722949 := bbase (se 4 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 2722949 = 510553) (by norm_num)
theorem B2296973 : Blo 1209422 2296973 := bbase (se 3 (by rfl) ⟨430682, by rfl⟩ : syracuseStep 2296973 = 861365) (by norm_num)
theorem B2043029 : Blo 1209422 2043029 := bbase (se 6 (by rfl) ⟨47883, by rfl⟩ : syracuseStep 2043029 = 95767) (by norm_num)
theorem B4082885 : Blo 1209422 4082885 := bbase (se 4 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 4082885 = 765541) (by norm_num)
theorem B2723021 : Blo 1209422 2723021 := bbase (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) (by norm_num)
theorem B2182349 : Blo 1209422 2182349 := bbase (se 3 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 2182349 = 818381) (by norm_num)
theorem B1551593 : Blo 1209422 1551593 := bbase (se 2 (by rfl) ⟨581847, by rfl⟩ : syracuseStep 1551593 = 1163695) (by norm_num)
theorem B1453313 : Blo 1209422 1453313 := bbase (se 2 (by rfl) ⟨544992, by rfl⟩ : syracuseStep 1453313 = 1089985) (by norm_num)
theorem B2723093 : Blo 1209422 2723093 := bbase (se 6 (by rfl) ⟨63822, by rfl⟩ : syracuseStep 2723093 = 127645) (by norm_num)
theorem B2043157 : Blo 1209422 2043157 := bbase (se 6 (by rfl) ⟨47886, by rfl⟩ : syracuseStep 2043157 = 95773) (by norm_num)
theorem B2182421 : Blo 1209422 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B6122789 : Blo 1209422 6122789 := bbase (se 4 (by rfl) ⟨574011, by rfl⟩ : syracuseStep 6122789 = 1148023) (by norm_num)
theorem B4599125 : Blo 1209422 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B2723165 : Blo 1209422 2723165 := bbase (se 3 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 2723165 = 1021187) (by norm_num)
theorem B2182501 : Blo 1209422 2182501 := bbase (se 4 (by rfl) ⟨204609, by rfl⟩ : syracuseStep 2182501 = 409219) (by norm_num)
theorem B2043245 : Blo 1209422 2043245 := bbase (se 3 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 2043245 = 766217) (by norm_num)
theorem B1723789 : Blo 1209422 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B4656533 : Blo 1209422 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B2723237 : Blo 1209422 2723237 := bbase (se 4 (by rfl) ⟨255303, by rfl⟩ : syracuseStep 2723237 = 510607) (by norm_num)
theorem B2182565 : Blo 1209422 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B2297261 : Blo 1209422 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B1453501 : Blo 1209422 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B2723309 : Blo 1209422 2723309 := bbase (se 3 (by rfl) ⟨510620, by rfl⟩ : syracuseStep 2723309 = 1021241) (by norm_num)
theorem B2043373 : Blo 1209422 2043373 := bbase (se 3 (by rfl) ⟨383132, by rfl⟩ : syracuseStep 2043373 = 766265) (by norm_num)
theorem B5819941 : Blo 1209422 5819941 := bbase (se 4 (by rfl) ⟨545619, by rfl⟩ : syracuseStep 5819941 = 1091239) (by norm_num)
theorem B2723381 : Blo 1209422 2723381 := bbase (se 5 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 2723381 = 255317) (by norm_num)
theorem B2297413 : Blo 1209422 2297413 := bbase (se 4 (by rfl) ⟨215382, by rfl⟩ : syracuseStep 2297413 = 430765) (by norm_num)
theorem B2043461 : Blo 1209422 2043461 := bbase (se 4 (by rfl) ⟨191574, by rfl⟩ : syracuseStep 2043461 = 383149) (by norm_num)
theorem B4083317 : Blo 1209422 4083317 := bbase (se 5 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 4083317 = 382811) (by norm_num)
theorem B4599413 : Blo 1209422 4599413 := bbase (se 5 (by rfl) ⟨215597, by rfl⟩ : syracuseStep 4599413 = 431195) (by norm_num)
theorem B1814141 : Blo 1209422 1814141 := bbase (se 3 (by rfl) ⟨340151, by rfl⟩ : syracuseStep 1814141 = 680303) (by norm_num)
theorem B2723453 : Blo 1209422 2723453 := bbase (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) (by norm_num)
theorem B1814165 : Blo 1209422 1814165 := bbase (se 6 (by rfl) ⟨42519, by rfl⟩ : syracuseStep 1814165 = 85039) (by norm_num)
theorem B1453717 : Blo 1209422 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B1552033 : Blo 1209422 1552033 := bbase (se 2 (by rfl) ⟨582012, by rfl⟩ : syracuseStep 1552033 = 1164025) (by norm_num)
theorem B3444389 : Blo 1209422 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B1814189 : Blo 1209422 1814189 := bbase (se 3 (by rfl) ⟨340160, by rfl⟩ : syracuseStep 1814189 = 680321) (by norm_num)
theorem B4140725 : Blo 1209422 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B1814213 : Blo 1209422 1814213 := bbase (se 4 (by rfl) ⟨170082, by rfl⟩ : syracuseStep 1814213 = 340165) (by norm_num)
theorem B2723525 : Blo 1209422 2723525 := bbase (se 4 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 2723525 = 510661) (by norm_num)
theorem B2043589 : Blo 1209422 2043589 := bbase (se 4 (by rfl) ⟨191586, by rfl⟩ : syracuseStep 2043589 = 383173) (by norm_num)
theorem B2182853 : Blo 1209422 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B1814237 : Blo 1209422 1814237 := bbase (se 3 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 1814237 = 680339) (by norm_num)
theorem B1814261 : Blo 1209422 1814261 := bbase (se 5 (by rfl) ⟨85043, by rfl⟩ : syracuseStep 1814261 = 170087) (by norm_num)
theorem B2838277 : Blo 1209422 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B1814285 : Blo 1209422 1814285 := bbase (se 3 (by rfl) ⟨340178, by rfl⟩ : syracuseStep 1814285 = 680357) (by norm_num)
theorem B2723597 : Blo 1209422 2723597 := bbase (se 3 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 2723597 = 1021349) (by norm_num)
theorem B6893333 : Blo 1209422 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B2043677 : Blo 1209422 2043677 := bbase (se 3 (by rfl) ⟨383189, by rfl⟩ : syracuseStep 2043677 = 766379) (by norm_num)
theorem B1814309 : Blo 1209422 1814309 := bbase (se 4 (by rfl) ⟨170091, by rfl⟩ : syracuseStep 1814309 = 340183) (by norm_num)
theorem B5812021 : Blo 1209422 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B1814333 : Blo 1209422 1814333 := bbase (se 3 (by rfl) ⟨340187, by rfl⟩ : syracuseStep 1814333 = 680375) (by norm_num)
theorem B1814357 : Blo 1209422 1814357 := bbase (se 9 (by rfl) ⟨5315, by rfl⟩ : syracuseStep 1814357 = 10631) (by norm_num)
theorem B2723669 : Blo 1209422 2723669 := bbase (se 9 (by rfl) ⟨7979, by rfl⟩ : syracuseStep 2723669 = 15959) (by norm_num)
theorem B1814381 : Blo 1209422 1814381 := bbase (se 3 (by rfl) ⟨340196, by rfl⟩ : syracuseStep 1814381 = 680393) (by norm_num)
theorem B2297717 : Blo 1209422 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B1814405 : Blo 1209422 1814405 := bbase (se 4 (by rfl) ⟨170100, by rfl⟩ : syracuseStep 1814405 = 340201) (by norm_num)
theorem B1814429 : Blo 1209422 1814429 := bbase (se 3 (by rfl) ⟨340205, by rfl⟩ : syracuseStep 1814429 = 680411) (by norm_num)
theorem B2723741 : Blo 1209422 2723741 := bbase (se 3 (by rfl) ⟨510701, by rfl⟩ : syracuseStep 2723741 = 1021403) (by norm_num)
theorem B2043805 : Blo 1209422 2043805 := bbase (se 3 (by rfl) ⟨383213, by rfl⟩ : syracuseStep 2043805 = 766427) (by norm_num)
theorem B1814453 : Blo 1209422 1814453 := bbase (se 5 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 1814453 = 170105) (by norm_num)
theorem B1454005 : Blo 1209422 1454005 := bbase (se 5 (by rfl) ⟨68156, by rfl⟩ : syracuseStep 1454005 = 136313) (by norm_num)
theorem B7761845 : Blo 1209422 7761845 := bbase (se 5 (by rfl) ⟨363836, by rfl⟩ : syracuseStep 7761845 = 727673) (by norm_num)
theorem B1552321 : Blo 1209422 1552321 := bbase (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) (by norm_num)
theorem B1814477 : Blo 1209422 1814477 := bbase (se 3 (by rfl) ⟨340214, by rfl⟩ : syracuseStep 1814477 = 680429) (by norm_num)
theorem B1814501 : Blo 1209422 1814501 := bbase (se 4 (by rfl) ⟨170109, by rfl⟩ : syracuseStep 1814501 = 340219) (by norm_num)
theorem B2723813 : Blo 1209422 2723813 := bbase (se 4 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 2723813 = 510715) (by norm_num)
theorem B2043893 : Blo 1209422 2043893 := bbase (se 5 (by rfl) ⟨95807, by rfl⟩ : syracuseStep 2043893 = 191615) (by norm_num)
theorem B1814525 : Blo 1209422 1814525 := bbase (se 3 (by rfl) ⟨340223, by rfl⟩ : syracuseStep 1814525 = 680447) (by norm_num)
theorem B1937405 : Blo 1209422 1937405 := bbase (se 3 (by rfl) ⟨363263, by rfl⟩ : syracuseStep 1937405 = 726527) (by norm_num)
theorem B1814549 : Blo 1209422 1814549 := bbase (se 6 (by rfl) ⟨42528, by rfl⟩ : syracuseStep 1814549 = 85057) (by norm_num)
theorem B4083749 : Blo 1209422 4083749 := bbase (se 4 (by rfl) ⟨382851, by rfl⟩ : syracuseStep 4083749 = 765703) (by norm_num)
theorem B1814573 : Blo 1209422 1814573 := bbase (se 3 (by rfl) ⟨340232, by rfl⟩ : syracuseStep 1814573 = 680465) (by norm_num)
theorem B2723885 : Blo 1209422 2723885 := bbase (se 3 (by rfl) ⟨510728, by rfl⟩ : syracuseStep 2723885 = 1021457) (by norm_num)
theorem B1814597 : Blo 1209422 1814597 := bbase (se 4 (by rfl) ⟨170118, by rfl⟩ : syracuseStep 1814597 = 340237) (by norm_num)
theorem B12423253 : Blo 1209422 12423253 := bbase (se 8 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 12423253 = 145585) (by norm_num)
theorem B9195605 : Blo 1209422 9195605 := bbase (se 8 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 9195605 = 107761) (by norm_num)
theorem B1814621 : Blo 1209422 1814621 := bbase (se 3 (by rfl) ⟨340241, by rfl⟩ : syracuseStep 1814621 = 680483) (by norm_num)
theorem B2584685 : Blo 1209422 2584685 := bbase (se 3 (by rfl) ⟨484628, by rfl⟩ : syracuseStep 2584685 = 969257) (by norm_num)
theorem B1814645 : Blo 1209422 1814645 := bbase (se 5 (by rfl) ⟨85061, by rfl⟩ : syracuseStep 1814645 = 170123) (by norm_num)
theorem B2723957 : Blo 1209422 2723957 := bbase (se 5 (by rfl) ⟨127685, by rfl⟩ : syracuseStep 2723957 = 255371) (by norm_num)
theorem B2044021 : Blo 1209422 2044021 := bbase (se 5 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 2044021 = 191627) (by norm_num)
theorem B1814669 : Blo 1209422 1814669 := bbase (se 3 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 1814669 = 680501) (by norm_num)
theorem B6131861 : Blo 1209422 6131861 := bbase (se 6 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 6131861 = 287431) (by norm_num)
theorem B1814693 : Blo 1209422 1814693 := bbase (se 4 (by rfl) ⟨170127, by rfl⟩ : syracuseStep 1814693 = 340255) (by norm_num)
theorem B1724581 : Blo 1209422 1724581 := bbase (se 4 (by rfl) ⟨161679, by rfl⟩ : syracuseStep 1724581 = 323359) (by norm_num)
theorem B1814717 : Blo 1209422 1814717 := bbase (se 3 (by rfl) ⟨340259, by rfl⟩ : syracuseStep 1814717 = 680519) (by norm_num)
theorem B2724029 : Blo 1209422 2724029 := bbase (se 3 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 2724029 = 1021511) (by norm_num)
theorem B2044109 : Blo 1209422 2044109 := bbase (se 3 (by rfl) ⟨383270, by rfl⟩ : syracuseStep 2044109 = 766541) (by norm_num)
theorem B1814741 : Blo 1209422 1814741 := bbase (se 7 (by rfl) ⟨21266, by rfl⟩ : syracuseStep 1814741 = 42533) (by norm_num)
theorem B1814765 : Blo 1209422 1814765 := bbase (se 3 (by rfl) ⟨340268, by rfl⟩ : syracuseStep 1814765 = 680537) (by norm_num)
theorem B2584829 : Blo 1209422 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B1814789 : Blo 1209422 1814789 := bbase (se 4 (by rfl) ⟨170136, by rfl⟩ : syracuseStep 1814789 = 340273) (by norm_num)
theorem B2724101 : Blo 1209422 2724101 := bbase (se 4 (by rfl) ⟨255384, by rfl⟩ : syracuseStep 2724101 = 510769) (by norm_num)
theorem B1814813 : Blo 1209422 1814813 := bbase (se 3 (by rfl) ⟨340277, by rfl⟩ : syracuseStep 1814813 = 680555) (by norm_num)
theorem B1814837 : Blo 1209422 1814837 := bbase (se 5 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 1814837 = 170141) (by norm_num)
theorem B1814861 : Blo 1209422 1814861 := bbase (se 3 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 1814861 = 680573) (by norm_num)
theorem B2724173 : Blo 1209422 2724173 := bbase (se 3 (by rfl) ⟨510782, by rfl⟩ : syracuseStep 2724173 = 1021565) (by norm_num)
theorem B2044237 : Blo 1209422 2044237 := bbase (se 3 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 2044237 = 766589) (by norm_num)
theorem B1814885 : Blo 1209422 1814885 := bbase (se 4 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 1814885 = 340291) (by norm_num)
theorem B1814909 : Blo 1209422 1814909 := bbase (se 3 (by rfl) ⟨340295, by rfl⟩ : syracuseStep 1814909 = 680591) (by norm_num)
theorem B2068885 : Blo 1209422 2068885 := bbase (se 6 (by rfl) ⟨48489, by rfl⟩ : syracuseStep 2068885 = 96979) (by norm_num)
theorem B1814933 : Blo 1209422 1814933 := bbase (se 6 (by rfl) ⟨42537, by rfl⟩ : syracuseStep 1814933 = 85075) (by norm_num)
theorem B2724245 : Blo 1209422 2724245 := bbase (se 6 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 2724245 = 127699) (by norm_num)
theorem B1814957 : Blo 1209422 1814957 := bbase (se 3 (by rfl) ⟨340304, by rfl⟩ : syracuseStep 1814957 = 680609) (by norm_num)
theorem B1814981 : Blo 1209422 1814981 := bbase (se 4 (by rfl) ⟨170154, by rfl⟩ : syracuseStep 1814981 = 340309) (by norm_num)
theorem B4084181 : Blo 1209422 4084181 := bbase (se 7 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 4084181 = 95723) (by norm_num)
theorem B1815005 : Blo 1209422 1815005 := bbase (se 3 (by rfl) ⟨340313, by rfl⟩ : syracuseStep 1815005 = 680627) (by norm_num)
theorem B2724317 : Blo 1209422 2724317 := bbase (se 3 (by rfl) ⟨510809, by rfl⟩ : syracuseStep 2724317 = 1021619) (by norm_num)
theorem B9187829 : Blo 1209422 9187829 := bbase (se 5 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 9187829 = 861359) (by norm_num)
theorem B1815029 : Blo 1209422 1815029 := bbase (se 5 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 1815029 = 170159) (by norm_num)
theorem B1815053 : Blo 1209422 1815053 := bbase (se 3 (by rfl) ⟨340322, by rfl⟩ : syracuseStep 1815053 = 680645) (by norm_num)
theorem B11637269 : Blo 1209422 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B1815077 : Blo 1209422 1815077 := bbase (se 4 (by rfl) ⟨170163, by rfl⟩ : syracuseStep 1815077 = 340327) (by norm_num)
theorem B2724389 : Blo 1209422 2724389 := bbase (se 4 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 2724389 = 510823) (by norm_num)
theorem B1552937 : Blo 1209422 1552937 := bbase (se 2 (by rfl) ⟨582351, by rfl⟩ : syracuseStep 1552937 = 1164703) (by norm_num)
theorem B6124085 : Blo 1209422 6124085 := bbase (se 5 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 6124085 = 574133) (by norm_num)
theorem B1815101 : Blo 1209422 1815101 := bbase (se 3 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 1815101 = 680663) (by norm_num)
theorem B9810517 : Blo 1209422 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B1815125 : Blo 1209422 1815125 := bbase (se 8 (by rfl) ⟨10635, by rfl⟩ : syracuseStep 1815125 = 21271) (by norm_num)
theorem B2585189 : Blo 1209422 2585189 := bbase (se 4 (by rfl) ⟨242361, by rfl⟩ : syracuseStep 2585189 = 484723) (by norm_num)
theorem B2298469 : Blo 1209422 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B1815149 : Blo 1209422 1815149 := bbase (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) (by norm_num)
theorem B2724461 : Blo 1209422 2724461 := bbase (se 3 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 2724461 = 1021673) (by norm_num)
theorem B1815173 : Blo 1209422 1815173 := bbase (se 4 (by rfl) ⟨170172, by rfl⟩ : syracuseStep 1815173 = 340345) (by norm_num)
theorem B17453717 : Blo 1209422 17453717 := bbase (se 6 (by rfl) ⟨409071, by rfl⟩ : syracuseStep 17453717 = 818143) (by norm_num)
theorem B1815197 : Blo 1209422 1815197 := bbase (se 3 (by rfl) ⟨340349, by rfl⟩ : syracuseStep 1815197 = 680699) (by norm_num)
theorem B1815221 : Blo 1209422 1815221 := bbase (se 5 (by rfl) ⟨85088, by rfl⟩ : syracuseStep 1815221 = 170177) (by norm_num)
theorem B2724533 : Blo 1209422 2724533 := bbase (se 5 (by rfl) ⟨127712, by rfl⟩ : syracuseStep 2724533 = 255425) (by norm_num)
theorem B1815245 : Blo 1209422 1815245 := bbase (se 3 (by rfl) ⟨340358, by rfl⟩ : syracuseStep 1815245 = 680717) (by norm_num)
theorem B1815269 : Blo 1209422 1815269 := bbase (se 4 (by rfl) ⟨170181, by rfl⟩ : syracuseStep 1815269 = 340363) (by norm_num)
theorem B4362997 : Blo 1209422 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B2298613 : Blo 1209422 2298613 := bbase (se 5 (by rfl) ⟨107747, by rfl⟩ : syracuseStep 2298613 = 215495) (by norm_num)
theorem B1815293 : Blo 1209422 1815293 := bbase (se 3 (by rfl) ⟨340367, by rfl⟩ : syracuseStep 1815293 = 680735) (by norm_num)
theorem B2724605 : Blo 1209422 2724605 := bbase (se 3 (by rfl) ⟨510863, by rfl⟩ : syracuseStep 2724605 = 1021727) (by norm_num)
theorem B1815317 : Blo 1209422 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B1815341 : Blo 1209422 1815341 := bbase (se 3 (by rfl) ⟨340376, by rfl⟩ : syracuseStep 1815341 = 680753) (by norm_num)
theorem B3445573 : Blo 1209422 3445573 := bbase (se 4 (by rfl) ⟨323022, by rfl⟩ : syracuseStep 3445573 = 646045) (by norm_num)
theorem B1815365 : Blo 1209422 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B2724677 : Blo 1209422 2724677 := bbase (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) (by norm_num)
theorem B1815389 : Blo 1209422 1815389 := bbase (se 3 (by rfl) ⟨340385, by rfl⟩ : syracuseStep 1815389 = 680771) (by norm_num)
theorem B1815413 : Blo 1209422 1815413 := bbase (se 5 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 1815413 = 170195) (by norm_num)
theorem B4084613 : Blo 1209422 4084613 := bbase (se 4 (by rfl) ⟨382932, by rfl⟩ : syracuseStep 4084613 = 765865) (by norm_num)
theorem B2945933 : Blo 1209422 2945933 := bbase (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) (by norm_num)
theorem B1815437 : Blo 1209422 1815437 := bbase (se 3 (by rfl) ⟨340394, by rfl⟩ : syracuseStep 1815437 = 680789) (by norm_num)
theorem B2724749 : Blo 1209422 2724749 := bbase (se 3 (by rfl) ⟨510890, by rfl⟩ : syracuseStep 2724749 = 1021781) (by norm_num)
theorem B2298773 : Blo 1209422 2298773 := bbase (se 6 (by rfl) ⟨53877, by rfl⟩ : syracuseStep 2298773 = 107755) (by norm_num)
theorem B1815461 : Blo 1209422 1815461 := bbase (se 4 (by rfl) ⟨170199, by rfl⟩ : syracuseStep 1815461 = 340399) (by norm_num)
theorem B6894517 : Blo 1209422 6894517 := bbase (se 5 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 6894517 = 646361) (by norm_num)
theorem B1815485 : Blo 1209422 1815485 := bbase (se 3 (by rfl) ⟨340403, by rfl⟩ : syracuseStep 1815485 = 680807) (by norm_num)
theorem B1815509 : Blo 1209422 1815509 := bbase (se 7 (by rfl) ⟨21275, by rfl⟩ : syracuseStep 1815509 = 42551) (by norm_num)
theorem B2724821 : Blo 1209422 2724821 := bbase (se 7 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 2724821 = 63863) (by norm_num)
theorem B3445733 : Blo 1209422 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B1815533 : Blo 1209422 1815533 := bbase (se 3 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 1815533 = 680825) (by norm_num)
theorem B1815557 : Blo 1209422 1815557 := bbase (se 4 (by rfl) ⟨170208, by rfl⟩ : syracuseStep 1815557 = 340417) (by norm_num)
theorem B1553429 : Blo 1209422 1553429 := bbase (se 6 (by rfl) ⟨36408, by rfl⟩ : syracuseStep 1553429 = 72817) (by norm_num)
theorem B1815581 : Blo 1209422 1815581 := bbase (se 3 (by rfl) ⟨340421, by rfl⟩ : syracuseStep 1815581 = 680843) (by norm_num)
theorem B2724893 : Blo 1209422 2724893 := bbase (se 3 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 2724893 = 1021835) (by norm_num)
theorem B2298917 : Blo 1209422 2298917 := bbase (se 4 (by rfl) ⟨215523, by rfl⟩ : syracuseStep 2298917 = 431047) (by norm_num)
theorem B1815605 : Blo 1209422 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B1815629 : Blo 1209422 1815629 := bbase (se 3 (by rfl) ⟨340430, by rfl⟩ : syracuseStep 1815629 = 680861) (by norm_num)
theorem B1815653 : Blo 1209422 1815653 := bbase (se 4 (by rfl) ⟨170217, by rfl⟩ : syracuseStep 1815653 = 340435) (by norm_num)
theorem B2724965 : Blo 1209422 2724965 := bbase (se 4 (by rfl) ⟨255465, by rfl⟩ : syracuseStep 2724965 = 510931) (by norm_num)
theorem B1815677 : Blo 1209422 1815677 := bbase (se 3 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 1815677 = 680879) (by norm_num)
theorem B1815701 : Blo 1209422 1815701 := bbase (se 6 (by rfl) ⟨42555, by rfl⟩ : syracuseStep 1815701 = 85111) (by norm_num)
theorem B1815725 : Blo 1209422 1815725 := bbase (se 3 (by rfl) ⟨340448, by rfl⟩ : syracuseStep 1815725 = 680897) (by norm_num)
theorem B2725037 : Blo 1209422 2725037 := bbase (se 3 (by rfl) ⟨510944, by rfl⟩ : syracuseStep 2725037 = 1021889) (by norm_num)
theorem B4592821 : Blo 1209422 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B1455293 : Blo 1209422 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B1815749 : Blo 1209422 1815749 := bbase (se 4 (by rfl) ⟨170226, by rfl⟩ : syracuseStep 1815749 = 340453) (by norm_num)
theorem B3445973 : Blo 1209422 3445973 := bbase (se 7 (by rfl) ⟨40382, by rfl⟩ : syracuseStep 3445973 = 80765) (by norm_num)
theorem B1815773 : Blo 1209422 1815773 := bbase (se 3 (by rfl) ⟨340457, by rfl⟩ : syracuseStep 1815773 = 680915) (by norm_num)
theorem B1815797 : Blo 1209422 1815797 := bbase (se 5 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 1815797 = 170231) (by norm_num)
theorem B2725109 : Blo 1209422 2725109 := bbase (se 5 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 2725109 = 255479) (by norm_num)
theorem B1815821 : Blo 1209422 1815821 := bbase (se 3 (by rfl) ⟨340466, by rfl⟩ : syracuseStep 1815821 = 680933) (by norm_num)
theorem B1938725 : Blo 1209422 1938725 := bbase (se 4 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 1938725 = 363511) (by norm_num)
theorem B1840421 : Blo 1209422 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1815845 : Blo 1209422 1815845 := bbase (se 4 (by rfl) ⟨170235, by rfl⟩ : syracuseStep 1815845 = 340471) (by norm_num)
theorem B1635637 : Blo 1209422 1635637 := bbase (se 5 (by rfl) ⟨76670, by rfl⟩ : syracuseStep 1635637 = 153341) (by norm_num)
theorem B4085045 : Blo 1209422 4085045 := bbase (se 5 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 4085045 = 382973) (by norm_num)
theorem B1815869 : Blo 1209422 1815869 := bbase (se 3 (by rfl) ⟨340475, by rfl⟩ : syracuseStep 1815869 = 680951) (by norm_num)
theorem B2725181 : Blo 1209422 2725181 := bbase (se 3 (by rfl) ⟨510971, by rfl⟩ : syracuseStep 2725181 = 1021943) (by norm_num)
theorem B2299205 : Blo 1209422 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1815893 : Blo 1209422 1815893 := bbase (se 13 (by rfl) ⟨332, by rfl⟩ : syracuseStep 1815893 = 665) (by norm_num)
theorem B1815917 : Blo 1209422 1815917 := bbase (se 3 (by rfl) ⟨340484, by rfl⟩ : syracuseStep 1815917 = 680969) (by norm_num)
theorem B2069885 : Blo 1209422 2069885 := bbase (se 3 (by rfl) ⟨388103, by rfl⟩ : syracuseStep 2069885 = 776207) (by norm_num)
theorem B1938821 : Blo 1209422 1938821 := bbase (se 4 (by rfl) ⟨181764, by rfl⟩ : syracuseStep 1938821 = 363529) (by norm_num)
theorem B1815941 : Blo 1209422 1815941 := bbase (se 4 (by rfl) ⟨170244, by rfl⟩ : syracuseStep 1815941 = 340489) (by norm_num)
theorem B2725253 : Blo 1209422 2725253 := bbase (se 4 (by rfl) ⟨255492, by rfl⟩ : syracuseStep 2725253 = 510985) (by norm_num)
theorem B3446165 : Blo 1209422 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1815965 : Blo 1209422 1815965 := bbase (se 3 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 1815965 = 680987) (by norm_num)
theorem B1938853 : Blo 1209422 1938853 := bbase (se 4 (by rfl) ⟨181767, by rfl⟩ : syracuseStep 1938853 = 363535) (by norm_num)
theorem B1815989 : Blo 1209422 1815989 := bbase (se 5 (by rfl) ⟨85124, by rfl⟩ : syracuseStep 1815989 = 170249) (by norm_num)
theorem B1816013 : Blo 1209422 1816013 := bbase (se 3 (by rfl) ⟨340502, by rfl⟩ : syracuseStep 1816013 = 681005) (by norm_num)
theorem B2725325 : Blo 1209422 2725325 := bbase (se 3 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 2725325 = 1021997) (by norm_num)
theorem B4363733 : Blo 1209422 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B2586077 : Blo 1209422 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B2299357 : Blo 1209422 2299357 := bbase (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) (by norm_num)
theorem B1226209 : Blo 1209422 1226209 := bbase (se 2 (by rfl) ⟨459828, by rfl⟩ : syracuseStep 1226209 = 919657) (by norm_num)
theorem B4593125 : Blo 1209422 4593125 := bbase (se 4 (by rfl) ⟨430605, by rfl⟩ : syracuseStep 4593125 = 861211) (by norm_num)
theorem B1816037 : Blo 1209422 1816037 := bbase (se 4 (by rfl) ⟨170253, by rfl⟩ : syracuseStep 1816037 = 340507) (by norm_num)
theorem B1816061 : Blo 1209422 1816061 := bbase (se 3 (by rfl) ⟨340511, by rfl⟩ : syracuseStep 1816061 = 681023) (by norm_num)
theorem B1816085 : Blo 1209422 1816085 := bbase (se 6 (by rfl) ⟨42564, by rfl⟩ : syracuseStep 1816085 = 85129) (by norm_num)
theorem B2725397 : Blo 1209422 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B1816109 : Blo 1209422 1816109 := bbase (se 3 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 1816109 = 681041) (by norm_num)
theorem B6207029 : Blo 1209422 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B1816133 : Blo 1209422 1816133 := bbase (se 4 (by rfl) ⟨170262, by rfl⟩ : syracuseStep 1816133 = 340525) (by norm_num)
theorem B2487901 : Blo 1209422 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B1816157 : Blo 1209422 1816157 := bbase (se 3 (by rfl) ⟨340529, by rfl⟩ : syracuseStep 1816157 = 681059) (by norm_num)
theorem B2725469 : Blo 1209422 2725469 := bbase (se 3 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 2725469 = 1022051) (by norm_num)
theorem B3929717 : Blo 1209422 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1816181 : Blo 1209422 1816181 := bbase (se 5 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 1816181 = 170267) (by norm_num)
theorem B1816205 : Blo 1209422 1816205 := bbase (se 3 (by rfl) ⟨340538, by rfl⟩ : syracuseStep 1816205 = 681077) (by norm_num)
theorem B1816229 : Blo 1209422 1816229 := bbase (se 4 (by rfl) ⟨170271, by rfl⟩ : syracuseStep 1816229 = 340543) (by norm_num)
theorem B1291945 : Blo 1209422 1291945 := bbase (se 2 (by rfl) ⟨484479, by rfl⟩ : syracuseStep 1291945 = 968959) (by norm_num)
theorem B2725541 : Blo 1209422 2725541 := bbase (se 4 (by rfl) ⟨255519, by rfl⟩ : syracuseStep 2725541 = 511039) (by norm_num)
theorem B5166773 : Blo 1209422 5166773 := bbase (se 5 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 5166773 = 484385) (by norm_num)
theorem B1816253 : Blo 1209422 1816253 := bbase (se 3 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 1816253 = 681095) (by norm_num)
theorem B1816277 : Blo 1209422 1816277 := bbase (se 7 (by rfl) ⟨21284, by rfl⟩ : syracuseStep 1816277 = 42569) (by norm_num)
theorem B2586325 : Blo 1209422 2586325 := bbase (se 7 (by rfl) ⟨30308, by rfl⟩ : syracuseStep 2586325 = 60617) (by norm_num)
theorem B4085477 : Blo 1209422 4085477 := bbase (se 4 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 4085477 = 766027) (by norm_num)
theorem B1816301 : Blo 1209422 1816301 := bbase (se 3 (by rfl) ⟨340556, by rfl⟩ : syracuseStep 1816301 = 681113) (by norm_num)
theorem B2725613 : Blo 1209422 2725613 := bbase (se 3 (by rfl) ⟨511052, by rfl⟩ : syracuseStep 2725613 = 1022105) (by norm_num)
theorem B1816325 : Blo 1209422 1816325 := bbase (se 4 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 1816325 = 340561) (by norm_num)
theorem B2299661 : Blo 1209422 2299661 := bbase (se 3 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 2299661 = 862373) (by norm_num)
theorem B1816349 : Blo 1209422 1816349 := bbase (se 3 (by rfl) ⟨340565, by rfl⟩ : syracuseStep 1816349 = 681131) (by norm_num)
theorem B1292069 : Blo 1209422 1292069 := bbase (se 4 (by rfl) ⟨121131, by rfl⟩ : syracuseStep 1292069 = 242263) (by norm_num)
theorem B1816373 : Blo 1209422 1816373 := bbase (se 5 (by rfl) ⟨85142, by rfl⟩ : syracuseStep 1816373 = 170285) (by norm_num)
theorem B2725685 : Blo 1209422 2725685 := bbase (se 5 (by rfl) ⟨127766, by rfl⟩ : syracuseStep 2725685 = 255533) (by norm_num)
theorem B6125381 : Blo 1209422 6125381 := bbase (se 4 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 6125381 = 1148509) (by norm_num)
theorem B1816397 : Blo 1209422 1816397 := bbase (se 3 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 1816397 = 681149) (by norm_num)
theorem B3061597 : Blo 1209422 3061597 := bbase (se 3 (by rfl) ⟨574049, by rfl⟩ : syracuseStep 3061597 = 1148099) (by norm_num)
theorem B1816421 : Blo 1209422 1816421 := bbase (se 4 (by rfl) ⟨170289, by rfl⟩ : syracuseStep 1816421 = 340579) (by norm_num)
theorem B2905973 : Blo 1209422 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B1816445 : Blo 1209422 1816445 := bbase (se 3 (by rfl) ⟨340583, by rfl⟩ : syracuseStep 1816445 = 681167) (by norm_num)
theorem B1816469 : Blo 1209422 1816469 := bbase (se 6 (by rfl) ⟨42573, by rfl⟩ : syracuseStep 1816469 = 85147) (by norm_num)
theorem B1816493 : Blo 1209422 1816493 := bbase (se 3 (by rfl) ⟨340592, by rfl⟩ : syracuseStep 1816493 = 681185) (by norm_num)
theorem B1841077 : Blo 1209422 1841077 := bbase (se 5 (by rfl) ⟨86300, by rfl⟩ : syracuseStep 1841077 = 172601) (by norm_num)
theorem B1816517 : Blo 1209422 1816517 := bbase (se 4 (by rfl) ⟨170298, by rfl⟩ : syracuseStep 1816517 = 340597) (by norm_num)
theorem B3061709 : Blo 1209422 3061709 := bbase (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) (by norm_num)
theorem B5167061 : Blo 1209422 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B1816541 : Blo 1209422 1816541 := bbase (se 3 (by rfl) ⟨340601, by rfl⟩ : syracuseStep 1816541 = 681203) (by norm_num)
theorem B1816565 : Blo 1209422 1816565 := bbase (se 5 (by rfl) ⟨85151, by rfl⟩ : syracuseStep 1816565 = 170303) (by norm_num)
theorem B1816589 : Blo 1209422 1816589 := bbase (se 3 (by rfl) ⟨340610, by rfl⟩ : syracuseStep 1816589 = 681221) (by norm_num)
theorem B1292321 : Blo 1209422 1292321 := bbase (se 2 (by rfl) ⟨484620, by rfl⟩ : syracuseStep 1292321 = 969241) (by norm_num)
theorem B1816613 : Blo 1209422 1816613 := bbase (se 4 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 1816613 = 340615) (by norm_num)
theorem B2906165 : Blo 1209422 2906165 := bbase (se 5 (by rfl) ⟨136226, by rfl⟩ : syracuseStep 2906165 = 272453) (by norm_num)
theorem B1816637 : Blo 1209422 1816637 := bbase (se 3 (by rfl) ⟨340619, by rfl⟩ : syracuseStep 1816637 = 681239) (by norm_num)
theorem B1816661 : Blo 1209422 1816661 := bbase (se 8 (by rfl) ⟨10644, by rfl⟩ : syracuseStep 1816661 = 21289) (by norm_num)
theorem B1816685 : Blo 1209422 1816685 := bbase (se 3 (by rfl) ⟨340628, by rfl⟩ : syracuseStep 1816685 = 681257) (by norm_num)
theorem B1816709 : Blo 1209422 1816709 := bbase (se 4 (by rfl) ⟨170316, by rfl⟩ : syracuseStep 1816709 = 340633) (by norm_num)
theorem B3061901 : Blo 1209422 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B4085909 : Blo 1209422 4085909 := bbase (se 6 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 4085909 = 191527) (by norm_num)
theorem B1816733 : Blo 1209422 1816733 := bbase (se 3 (by rfl) ⟨340637, by rfl⟩ : syracuseStep 1816733 = 681275) (by norm_num)
theorem B1816757 : Blo 1209422 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B1816781 : Blo 1209422 1816781 := bbase (se 3 (by rfl) ⟨340646, by rfl⟩ : syracuseStep 1816781 = 681293) (by norm_num)
theorem B2586829 : Blo 1209422 2586829 := bbase (se 3 (by rfl) ⟨485030, by rfl⟩ : syracuseStep 2586829 = 970061) (by norm_num)
theorem B1816805 : Blo 1209422 1816805 := bbase (se 4 (by rfl) ⟨170325, by rfl⟩ : syracuseStep 1816805 = 340651) (by norm_num)
theorem B1816829 : Blo 1209422 1816829 := bbase (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) (by norm_num)
theorem B1816853 : Blo 1209422 1816853 := bbase (se 6 (by rfl) ⟨42582, by rfl⟩ : syracuseStep 1816853 = 85165) (by norm_num)
theorem B1816877 : Blo 1209422 1816877 := bbase (se 3 (by rfl) ⟨340664, by rfl⟩ : syracuseStep 1816877 = 681329) (by norm_num)
theorem B1816901 : Blo 1209422 1816901 := bbase (se 4 (by rfl) ⟨170334, by rfl⟩ : syracuseStep 1816901 = 340669) (by norm_num)
theorem B1816925 : Blo 1209422 1816925 := bbase (se 3 (by rfl) ⟨340673, by rfl⟩ : syracuseStep 1816925 = 681347) (by norm_num)
theorem B3447157 : Blo 1209422 3447157 := bbase (se 5 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 3447157 = 323171) (by norm_num)
theorem B1227125 : Blo 1209422 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1816949 : Blo 1209422 1816949 := bbase (se 5 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 1816949 = 170339) (by norm_num)
theorem B1816973 : Blo 1209422 1816973 := bbase (se 3 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 1816973 = 681365) (by norm_num)
theorem B7756181 : Blo 1209422 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B1816997 : Blo 1209422 1816997 := bbase (se 4 (by rfl) ⟨170343, by rfl⟩ : syracuseStep 1816997 = 340687) (by norm_num)
theorem B1817021 : Blo 1209422 1817021 := bbase (se 3 (by rfl) ⟨340691, by rfl⟩ : syracuseStep 1817021 = 681383) (by norm_num)
theorem B1817045 : Blo 1209422 1817045 := bbase (se 7 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 1817045 = 42587) (by norm_num)
theorem B1292765 : Blo 1209422 1292765 := bbase (se 3 (by rfl) ⟨242393, by rfl⟩ : syracuseStep 1292765 = 484787) (by norm_num)
theorem B3062245 : Blo 1209422 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B1817069 : Blo 1209422 1817069 := bbase (se 3 (by rfl) ⟨340700, by rfl⟩ : syracuseStep 1817069 = 681401) (by norm_num)
theorem B1817093 : Blo 1209422 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B1817117 : Blo 1209422 1817117 := bbase (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) (by norm_num)
theorem B4086341 : Blo 1209422 4086341 := bbase (se 4 (by rfl) ⟨383094, by rfl⟩ : syracuseStep 4086341 = 766189) (by norm_num)
theorem B3062357 : Blo 1209422 3062357 := bbase (se 8 (by rfl) ⟨17943, by rfl⟩ : syracuseStep 3062357 = 35887) (by norm_num)
theorem B4659797 : Blo 1209422 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B2210413 : Blo 1209422 2210413 := bbase (se 3 (by rfl) ⟨414452, by rfl⟩ : syracuseStep 2210413 = 828905) (by norm_num)
theorem B1637021 : Blo 1209422 1637021 := bbase (se 3 (by rfl) ⟨306941, by rfl⟩ : syracuseStep 1637021 = 613883) (by norm_num)
theorem B1637053 : Blo 1209422 1637053 := bbase (se 3 (by rfl) ⟨306947, by rfl⟩ : syracuseStep 1637053 = 613895) (by norm_num)
theorem B5167813 : Blo 1209422 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B1293013 : Blo 1209422 1293013 := bbase (se 7 (by rfl) ⟨15152, by rfl⟩ : syracuseStep 1293013 = 30305) (by norm_num)
theorem B4365013 : Blo 1209422 4365013 := bbase (se 7 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 4365013 = 102305) (by norm_num)
theorem B3062549 : Blo 1209422 3062549 := bbase (se 6 (by rfl) ⟨71778, by rfl⟩ : syracuseStep 3062549 = 143557) (by norm_num)
theorem B1530677 : Blo 1209422 1530677 := bbase (se 5 (by rfl) ⟨71750, by rfl⟩ : syracuseStep 1530677 = 143501) (by norm_num)
theorem B2906933 : Blo 1209422 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B1530733 : Blo 1209422 1530733 := bbase (se 3 (by rfl) ⟨287012, by rfl⟩ : syracuseStep 1530733 = 574025) (by norm_num)
theorem B6896501 : Blo 1209422 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B1940365 : Blo 1209422 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B1530829 : Blo 1209422 1530829 := bbase (se 3 (by rfl) ⟨287030, by rfl⟩ : syracuseStep 1530829 = 574061) (by norm_num)
theorem B2948069 : Blo 1209422 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B4086773 : Blo 1209422 4086773 := bbase (se 5 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 4086773 = 383135) (by norm_num)
theorem B6126677 : Blo 1209422 6126677 := bbase (se 8 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 6126677 = 71797) (by norm_num)
theorem B3062893 : Blo 1209422 3062893 := bbase (se 3 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 3062893 = 1148585) (by norm_num)
theorem B1531001 : Blo 1209422 1531001 := bbase (se 2 (by rfl) ⟨574125, by rfl⟩ : syracuseStep 1531001 = 1148251) (by norm_num)
theorem B1227917 : Blo 1209422 1227917 := bbase (se 3 (by rfl) ⟨230234, by rfl⟩ : syracuseStep 1227917 = 460469) (by norm_num)
theorem B1293457 : Blo 1209422 1293457 := bbase (se 2 (by rfl) ⟨485046, by rfl⟩ : syracuseStep 1293457 = 970093) (by norm_num)
theorem B1531057 : Blo 1209422 1531057 := bbase (se 2 (by rfl) ⟨574146, by rfl⟩ : syracuseStep 1531057 = 1148293) (by norm_num)
theorem B1293517 : Blo 1209422 1293517 := bbase (se 3 (by rfl) ⟨242534, by rfl⟩ : syracuseStep 1293517 = 485069) (by norm_num)
theorem B3063005 : Blo 1209422 3063005 := bbase (se 3 (by rfl) ⟨574313, by rfl⟩ : syracuseStep 3063005 = 1148627) (by norm_num)
theorem B1531153 : Blo 1209422 1531153 := bbase (se 2 (by rfl) ⟨574182, by rfl⟩ : syracuseStep 1531153 = 1148365) (by norm_num)
theorem B5815637 : Blo 1209422 5815637 := bbase (se 11 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5815637 = 8519) (by norm_num)
theorem B2522477 : Blo 1209422 2522477 := bbase (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) (by norm_num)
theorem B8723861 : Blo 1209422 8723861 := bbase (se 6 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 8723861 = 408931) (by norm_num)
theorem B10345877 : Blo 1209422 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B3063197 : Blo 1209422 3063197 := bbase (se 3 (by rfl) ⟨574349, by rfl⟩ : syracuseStep 3063197 = 1148699) (by norm_num)
theorem B5168549 : Blo 1209422 5168549 := bbase (se 4 (by rfl) ⟨484551, by rfl⟩ : syracuseStep 5168549 = 969103) (by norm_num)
theorem B4087205 : Blo 1209422 4087205 := bbase (se 4 (by rfl) ⟨383175, by rfl⟩ : syracuseStep 4087205 = 766351) (by norm_num)
theorem B1531325 : Blo 1209422 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B1400257 : Blo 1209422 1400257 := bbase (se 2 (by rfl) ⟨525096, by rfl⟩ : syracuseStep 1400257 = 1050193) (by norm_num)
theorem B3448261 : Blo 1209422 3448261 := bbase (se 4 (by rfl) ⟨323274, by rfl⟩ : syracuseStep 3448261 = 646549) (by norm_num)
theorem B2211293 : Blo 1209422 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B1531381 : Blo 1209422 1531381 := bbase (se 5 (by rfl) ⟨71783, by rfl⟩ : syracuseStep 1531381 = 143567) (by norm_num)
theorem B10337813 : Blo 1209422 10337813 := bbase (se 6 (by rfl) ⟨242292, by rfl⟩ : syracuseStep 10337813 = 484585) (by norm_num)
theorem B4595237 : Blo 1209422 4595237 := bbase (se 4 (by rfl) ⟨430803, by rfl⟩ : syracuseStep 4595237 = 861607) (by norm_num)
theorem B1531477 : Blo 1209422 1531477 := bbase (se 8 (by rfl) ⟨8973, by rfl⟩ : syracuseStep 1531477 = 17947) (by norm_num)
theorem B3677813 : Blo 1209422 3677813 := bbase (se 5 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 3677813 = 344795) (by norm_num)
theorem B1892045 : Blo 1209422 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B3063541 : Blo 1209422 3063541 := bbase (se 5 (by rfl) ⟨143603, by rfl⟩ : syracuseStep 3063541 = 287207) (by norm_num)
theorem B1531649 : Blo 1209422 1531649 := bbase (se 2 (by rfl) ⟨574368, by rfl⟩ : syracuseStep 1531649 = 1148737) (by norm_num)
theorem B3931909 : Blo 1209422 3931909 := bbase (se 4 (by rfl) ⟨368616, by rfl⟩ : syracuseStep 3931909 = 737233) (by norm_num)
theorem B1531705 : Blo 1209422 1531705 := bbase (se 2 (by rfl) ⟨574389, by rfl⟩ : syracuseStep 1531705 = 1148779) (by norm_num)
theorem B4595525 : Blo 1209422 4595525 := bbase (se 4 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 4595525 = 861661) (by norm_num)
theorem B4087637 : Blo 1209422 4087637 := bbase (se 9 (by rfl) ⟨11975, by rfl⟩ : syracuseStep 4087637 = 23951) (by norm_num)
theorem B3063653 : Blo 1209422 3063653 := bbase (se 4 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 3063653 = 574435) (by norm_num)
theorem B1531801 : Blo 1209422 1531801 := bbase (se 2 (by rfl) ⟨574425, by rfl⟩ : syracuseStep 1531801 = 1148851) (by norm_num)
theorem B4087853 : Blo 1209422 4087853 := bstep (se 3 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 4087853 = 1532945) B1532945
theorem B2908241 : Blo 1209422 2908241 := bstep (se 2 (by rfl) ⟨1090590, by rfl⟩ : syracuseStep 2908241 = 2181181) B2181181
theorem B4087907 : Blo 1209422 4087907 := bstep (se 1 (by rfl) ⟨3065930, by rfl⟩ : syracuseStep 4087907 = 6131861) B6131861
theorem B16564337 : Blo 1209422 16564337 := bstep (se 2 (by rfl) ⟨6211626, by rfl⟩ : syracuseStep 16564337 = 12423253) B12423253
theorem B2908433 : Blo 1209422 2908433 := bstep (se 2 (by rfl) ⟨1090662, by rfl⟩ : syracuseStep 2908433 = 2181325) B2181325
theorem B3449105 : Blo 1209422 3449105 := bstep (se 2 (by rfl) ⟨1293414, by rfl⟩ : syracuseStep 3449105 = 2586829) B2586829
theorem B4194659 : Blo 1209422 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B7758179 : Blo 1209422 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B5169521 : Blo 1209422 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B4088177 : Blo 1209422 4088177 := bstep (se 2 (by rfl) ⟨1533066, by rfl⟩ : syracuseStep 4088177 = 3066133) B3066133
theorem B4596209 : Blo 1209422 4596209 := bstep (se 2 (by rfl) ⟨1723578, by rfl⟩ : syracuseStep 4596209 = 3447157) B3447157
theorem B31007285 : Blo 1209422 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B1532515 : Blo 1209422 1532515 := bstep (se 1 (by rfl) ⟨1149386, by rfl⟩ : syracuseStep 1532515 = 2298773) B2298773
theorem B4137581 : Blo 1209422 4137581 := bstep (se 3 (by rfl) ⟨775796, by rfl⟩ : syracuseStep 4137581 = 1551593) B1551593
theorem B7357061 : Blo 1209422 7357061 := bstep (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) B1379449
theorem B3875501 : Blo 1209422 3875501 := bstep (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) B1453313
theorem B1532611 : Blo 1209422 1532611 := bstep (se 1 (by rfl) ⟨1149458, by rfl⟩ : syracuseStep 1532611 = 2298917) B2298917
theorem B4907789 : Blo 1209422 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B3064625 : Blo 1209422 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B1360723 : Blo 1209422 1360723 := bstep (se 1 (by rfl) ⟨1020542, by rfl⟩ : syracuseStep 1360723 = 2041085) B2041085
theorem B3064675 : Blo 1209422 3064675 := bstep (se 1 (by rfl) ⟨2298506, by rfl⟩ : syracuseStep 3064675 = 4597013) B4597013
theorem B6890417 : Blo 1209422 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B1360867 : Blo 1209422 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B2909155 : Blo 1209422 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B5817329 : Blo 1209422 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B3064817 : Blo 1209422 3064817 := bstep (se 2 (by rfl) ⟨1149306, by rfl⟩ : syracuseStep 3064817 = 2298613) B2298613
theorem B5170189 : Blo 1209422 5170189 := bstep (se 3 (by rfl) ⟨969410, by rfl⟩ : syracuseStep 5170189 = 1938821) B1938821
theorem B4138019 : Blo 1209422 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B1361011 : Blo 1209422 1361011 := bstep (se 1 (by rfl) ⟨1020758, by rfl⟩ : syracuseStep 1361011 = 2041517) B2041517
theorem B2040977 : Blo 1209422 2040977 := bstep (se 2 (by rfl) ⟨765366, by rfl⟩ : syracuseStep 2040977 = 1530733) B1530733
theorem B1533107 : Blo 1209422 1533107 := bstep (se 1 (by rfl) ⟨1149830, by rfl⟩ : syracuseStep 1533107 = 2299661) B2299661
theorem B9192689 : Blo 1209422 9192689 := bstep (se 2 (by rfl) ⟨3447258, by rfl⟩ : syracuseStep 9192689 = 6894517) B6894517
theorem B1361155 : Blo 1209422 1361155 := bstep (se 1 (by rfl) ⟨1020866, by rfl⟩ : syracuseStep 1361155 = 2041733) B2041733
theorem B2041105 : Blo 1209422 2041105 := bstep (se 2 (by rfl) ⟨765414, by rfl⟩ : syracuseStep 2041105 = 1530829) B1530829
theorem B6128945 : Blo 1209422 6128945 := bstep (se 2 (by rfl) ⟨2298354, by rfl⟩ : syracuseStep 6128945 = 4596709) B4596709
theorem B2041139 : Blo 1209422 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B1361299 : Blo 1209422 1361299 := bstep (se 1 (by rfl) ⟨1020974, by rfl⟩ : syracuseStep 1361299 = 2041949) B2041949
theorem B2041267 : Blo 1209422 2041267 := bstep (se 1 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 2041267 = 3061901) B3061901
theorem B1361443 : Blo 1209422 1361443 := bstep (se 1 (by rfl) ⟨1021082, by rfl⟩ : syracuseStep 1361443 = 2042165) B2042165
theorem B2721329 : Blo 1209422 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B2328113 : Blo 1209422 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B2041409 : Blo 1209422 2041409 := bstep (se 2 (by rfl) ⟨765528, by rfl⟩ : syracuseStep 2041409 = 1531057) B1531057
theorem B2721347 : Blo 1209422 2721347 := bstep (se 1 (by rfl) ⟨2041010, by rfl⟩ : syracuseStep 2721347 = 4082021) B4082021
theorem B5170787 : Blo 1209422 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B1361587 : Blo 1209422 1361587 := bstep (se 1 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 1361587 = 2042381) B2042381
theorem B2041537 : Blo 1209422 2041537 := bstep (se 2 (by rfl) ⟨765576, by rfl⟩ : syracuseStep 2041537 = 1531153) B1531153
theorem B2041571 : Blo 1209422 2041571 := bstep (se 1 (by rfl) ⟨1531178, by rfl⟩ : syracuseStep 2041571 = 3062357) B3062357
theorem B3106531 : Blo 1209422 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B2180849 : Blo 1209422 2180849 := bstep (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) B1635637
theorem B2910001 : Blo 1209422 2910001 := bstep (se 2 (by rfl) ⟨1091250, by rfl⟩ : syracuseStep 2910001 = 2182501) B2182501
theorem B1361731 : Blo 1209422 1361731 := bstep (se 1 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 1361731 = 2042597) B2042597
theorem B2721617 : Blo 1209422 2721617 := bstep (se 2 (by rfl) ⟨1020606, by rfl⟩ : syracuseStep 2721617 = 2041213) B2041213
theorem B2721635 : Blo 1209422 2721635 := bstep (se 1 (by rfl) ⟨2041226, by rfl⟩ : syracuseStep 2721635 = 4082453) B4082453
theorem B2041699 : Blo 1209422 2041699 := bstep (se 1 (by rfl) ⟨1531274, by rfl⟩ : syracuseStep 2041699 = 3062549) B3062549
theorem B4597667 : Blo 1209422 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B4597681 : Blo 1209422 4597681 := bstep (se 2 (by rfl) ⟨1724130, by rfl⟩ : syracuseStep 4597681 = 3448261) B3448261
theorem B3065809 : Blo 1209422 3065809 := bstep (se 2 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 3065809 = 2299357) B2299357
theorem B1361875 : Blo 1209422 1361875 := bstep (se 1 (by rfl) ⟨1021406, by rfl⟩ : syracuseStep 1361875 = 2042813) B2042813
theorem B2041841 : Blo 1209422 2041841 := bstep (se 2 (by rfl) ⟨765690, by rfl⟩ : syracuseStep 2041841 = 1531381) B1531381
theorem B7759921 : Blo 1209422 7759921 := bstep (se 2 (by rfl) ⟨2909970, by rfl⟩ : syracuseStep 7759921 = 5819941) B5819941
theorem B1362019 : Blo 1209422 1362019 := bstep (se 1 (by rfl) ⟨1021514, by rfl⟩ : syracuseStep 1362019 = 2043029) B2043029
theorem B2721905 : Blo 1209422 2721905 := bstep (se 2 (by rfl) ⟨1020714, by rfl⟩ : syracuseStep 2721905 = 2041429) B2041429
theorem B2041969 : Blo 1209422 2041969 := bstep (se 2 (by rfl) ⟨765738, by rfl⟩ : syracuseStep 2041969 = 1531477) B1531477
theorem B2721923 : Blo 1209422 2721923 := bstep (se 1 (by rfl) ⟨2041442, by rfl⟩ : syracuseStep 2721923 = 4082885) B4082885
theorem B4081805 : Blo 1209422 4081805 := bstep (se 3 (by rfl) ⟨765338, by rfl⟩ : syracuseStep 4081805 = 1530677) B1530677
theorem B2042003 : Blo 1209422 2042003 := bstep (se 1 (by rfl) ⟨1531502, by rfl⟩ : syracuseStep 2042003 = 3063005) B3063005
theorem B4081859 : Blo 1209422 4081859 := bstep (se 1 (by rfl) ⟨3061394, by rfl⟩ : syracuseStep 4081859 = 6122789) B6122789
theorem B1722593 : Blo 1209422 1722593 := bstep (se 2 (by rfl) ⟨645972, by rfl⟩ : syracuseStep 1722593 = 1291945) B1291945
theorem B3877091 : Blo 1209422 3877091 := bstep (se 1 (by rfl) ⟨2907818, by rfl⟩ : syracuseStep 3877091 = 5815637) B5815637
theorem B3066083 : Blo 1209422 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1362163 : Blo 1209422 1362163 := bstep (se 1 (by rfl) ⟨1021622, by rfl⟩ : syracuseStep 1362163 = 2043245) B2043245
theorem B1681651 : Blo 1209422 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B2042131 : Blo 1209422 2042131 := bstep (se 1 (by rfl) ⟨1531598, by rfl⟩ : syracuseStep 2042131 = 3063197) B3063197
theorem B6891875 : Blo 1209422 6891875 := bstep (se 1 (by rfl) ⟨5168906, by rfl⟩ : syracuseStep 6891875 = 10337813) B10337813
theorem B1362307 : Blo 1209422 1362307 := bstep (se 1 (by rfl) ⟨1021730, by rfl⟩ : syracuseStep 1362307 = 2043461) B2043461
theorem B2722193 : Blo 1209422 2722193 := bstep (se 2 (by rfl) ⟨1020822, by rfl⟩ : syracuseStep 2722193 = 2041645) B2041645
theorem B2042273 : Blo 1209422 2042273 := bstep (se 2 (by rfl) ⟨765852, by rfl⟩ : syracuseStep 2042273 = 1531705) B1531705
theorem B2451875 : Blo 1209422 2451875 := bstep (se 1 (by rfl) ⟨1838906, by rfl⟩ : syracuseStep 2451875 = 3677813) B3677813
theorem B2722211 : Blo 1209422 2722211 := bstep (se 1 (by rfl) ⟨2041658, by rfl⟩ : syracuseStep 2722211 = 4083317) B4083317
theorem B3066275 : Blo 1209422 3066275 := bstep (se 1 (by rfl) ⟨2299706, by rfl⟩ : syracuseStep 3066275 = 4599413) B4599413
theorem B2296259 : Blo 1209422 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B4082129 : Blo 1209422 4082129 := bstep (se 2 (by rfl) ⟨1530798, by rfl⟩ : syracuseStep 4082129 = 3061597) B3061597
theorem B1362451 : Blo 1209422 1362451 := bstep (se 1 (by rfl) ⟨1021838, by rfl⟩ : syracuseStep 1362451 = 2043677) B2043677
theorem B2042401 : Blo 1209422 2042401 := bstep (se 2 (by rfl) ⟨765900, by rfl⟩ : syracuseStep 2042401 = 1531801) B1531801
theorem B2042435 : Blo 1209422 2042435 := bstep (se 1 (by rfl) ⟨1531826, by rfl⟩ : syracuseStep 2042435 = 3063653) B3063653
theorem B1362595 : Blo 1209422 1362595 := bstep (se 1 (by rfl) ⟨1021946, by rfl⟩ : syracuseStep 1362595 = 2043893) B2043893
theorem B2722481 : Blo 1209422 2722481 := bstep (se 2 (by rfl) ⟨1020930, by rfl⟩ : syracuseStep 2722481 = 2041861) B2041861
theorem B2722499 : Blo 1209422 2722499 := bstep (se 1 (by rfl) ⟨2041874, by rfl⟩ : syracuseStep 2722499 = 4083749) B4083749
theorem B2042563 : Blo 1209422 2042563 := bstep (se 1 (by rfl) ⟨1531922, by rfl⟩ : syracuseStep 2042563 = 3063845) B3063845
theorem B15518405 : Blo 1209422 15518405 := bstep (se 4 (by rfl) ⟨1454850, by rfl⟩ : syracuseStep 15518405 = 2909701) B2909701
theorem B6130403 : Blo 1209422 6130403 := bstep (se 1 (by rfl) ⟨4597802, by rfl⟩ : syracuseStep 6130403 = 9195605) B9195605
theorem B1723123 : Blo 1209422 1723123 := bstep (se 1 (by rfl) ⟨1292342, by rfl⟩ : syracuseStep 1723123 = 2584685) B2584685
theorem B1362739 : Blo 1209422 1362739 := bstep (se 1 (by rfl) ⟨1022054, by rfl⟩ : syracuseStep 1362739 = 2044109) B2044109
theorem B2042705 : Blo 1209422 2042705 := bstep (se 2 (by rfl) ⟨766014, by rfl⟩ : syracuseStep 2042705 = 1532029) B1532029
theorem B2722769 : Blo 1209422 2722769 := bstep (se 2 (by rfl) ⟨1021038, by rfl⟩ : syracuseStep 2722769 = 2042077) B2042077
theorem B2042833 : Blo 1209422 2042833 := bstep (se 2 (by rfl) ⟨766062, by rfl⟩ : syracuseStep 2042833 = 1532125) B1532125
theorem B2722787 : Blo 1209422 2722787 := bstep (se 1 (by rfl) ⟨2042090, by rfl⟩ : syracuseStep 2722787 = 4084181) B4084181
theorem B4082669 : Blo 1209422 4082669 := bstep (se 3 (by rfl) ⟨765500, by rfl⟩ : syracuseStep 4082669 = 1531001) B1531001
theorem B2042867 : Blo 1209422 2042867 := bstep (se 1 (by rfl) ⟨1532150, by rfl⟩ : syracuseStep 2042867 = 3064301) B3064301
theorem B4082723 : Blo 1209422 4082723 := bstep (se 1 (by rfl) ⟨3062042, by rfl⟩ : syracuseStep 4082723 = 6124085) B6124085
theorem B1723459 : Blo 1209422 1723459 := bstep (se 1 (by rfl) ⟨1292594, by rfl⟩ : syracuseStep 1723459 = 2585189) B2585189
theorem B11635811 : Blo 1209422 11635811 := bstep (se 1 (by rfl) ⟨8726858, by rfl⟩ : syracuseStep 11635811 = 17453717) B17453717
theorem B2042995 : Blo 1209422 2042995 := bstep (se 1 (by rfl) ⟨1532246, by rfl⟩ : syracuseStep 2042995 = 3064493) B3064493
theorem B5819597 : Blo 1209422 5819597 := bstep (se 3 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 5819597 = 2182349) B2182349
theorem B2723057 : Blo 1209422 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B2043137 : Blo 1209422 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B2723075 : Blo 1209422 2723075 := bstep (se 1 (by rfl) ⟨2042306, by rfl⟩ : syracuseStep 2723075 = 4084613) B4084613
theorem B4082993 : Blo 1209422 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B2297155 : Blo 1209422 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B6892877 : Blo 1209422 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B4599139 : Blo 1209422 4599139 := bstep (se 1 (by rfl) ⟨3449354, by rfl⟩ : syracuseStep 4599139 = 6898709) B6898709
theorem B2043265 : Blo 1209422 2043265 := bstep (se 2 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 2043265 = 1532449) B1532449
theorem B5819789 : Blo 1209422 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B2043299 : Blo 1209422 2043299 := bstep (se 1 (by rfl) ⟨1532474, by rfl⟩ : syracuseStep 2043299 = 3064949) B3064949
theorem B7753157 : Blo 1209422 7753157 := bstep (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) B1453717
theorem B2297315 : Blo 1209422 2297315 := bstep (se 1 (by rfl) ⟨1722986, by rfl⟩ : syracuseStep 2297315 = 3445973) B3445973
theorem B3878371 : Blo 1209422 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B8277509 : Blo 1209422 8277509 := bstep (se 4 (by rfl) ⟨776016, by rfl⟩ : syracuseStep 8277509 = 1552033) B1552033
theorem B6131213 : Blo 1209422 6131213 := bstep (se 3 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 6131213 = 2299205) B2299205
theorem B3444241 : Blo 1209422 3444241 := bstep (se 2 (by rfl) ⟨1291590, by rfl⟩ : syracuseStep 3444241 = 2583181) B2583181
theorem B2723345 : Blo 1209422 2723345 := bstep (se 2 (by rfl) ⟨1021254, by rfl⟩ : syracuseStep 2723345 = 2042509) B2042509
theorem B2723363 : Blo 1209422 2723363 := bstep (se 1 (by rfl) ⟨2042522, by rfl⟩ : syracuseStep 2723363 = 4085045) B4085045
theorem B2043427 : Blo 1209422 2043427 := bstep (se 1 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 2043427 = 3065141) B3065141
theorem B1379923 : Blo 1209422 1379923 := bstep (se 1 (by rfl) ⟨1034942, by rfl⟩ : syracuseStep 1379923 = 2069885) B2069885
theorem B2584163 : Blo 1209422 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B1724017 : Blo 1209422 1724017 := bstep (se 2 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 1724017 = 1293013) B1293013
theorem B5820017 : Blo 1209422 5820017 := bstep (se 2 (by rfl) ⟨2182506, by rfl⟩ : syracuseStep 5820017 = 4365013) B4365013
theorem B1814147 : Blo 1209422 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B3272333 : Blo 1209422 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B1724051 : Blo 1209422 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B1814177 : Blo 1209422 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B4910755 : Blo 1209422 4910755 := bstep (se 1 (by rfl) ⟨3683066, by rfl⟩ : syracuseStep 4910755 = 7366133) B7366133
theorem B2043569 : Blo 1209422 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B1814195 : Blo 1209422 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B1814225 : Blo 1209422 1814225 := bstep (se 2 (by rfl) ⟨680334, by rfl⟩ : syracuseStep 1814225 = 1360669) B1360669
theorem B1814243 : Blo 1209422 1814243 := bstep (se 1 (by rfl) ⟨1360682, by rfl⟩ : syracuseStep 1814243 = 2721365) B2721365
theorem B1814273 : Blo 1209422 1814273 := bstep (se 2 (by rfl) ⟨680352, by rfl⟩ : syracuseStep 1814273 = 1360705) B1360705
theorem B5820173 : Blo 1209422 5820173 := bstep (se 3 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 5820173 = 2182565) B2182565
theorem B1814291 : Blo 1209422 1814291 := bstep (se 1 (by rfl) ⟨1360718, by rfl⟩ : syracuseStep 1814291 = 2721437) B2721437
theorem B3444515 : Blo 1209422 3444515 := bstep (se 1 (by rfl) ⟨2583386, by rfl⟩ : syracuseStep 3444515 = 5166773) B5166773
theorem B1814321 : Blo 1209422 1814321 := bstep (se 2 (by rfl) ⟨680370, by rfl⟩ : syracuseStep 1814321 = 1360741) B1360741
theorem B2723633 : Blo 1209422 2723633 := bstep (se 2 (by rfl) ⟨1021362, by rfl⟩ : syracuseStep 2723633 = 2042725) B2042725
theorem B3878705 : Blo 1209422 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B2043697 : Blo 1209422 2043697 := bstep (se 2 (by rfl) ⟨766386, by rfl⟩ : syracuseStep 2043697 = 1532773) B1532773
theorem B1814339 : Blo 1209422 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B2723651 : Blo 1209422 2723651 := bstep (se 1 (by rfl) ⟨2042738, by rfl⟩ : syracuseStep 2723651 = 4085477) B4085477
theorem B4083533 : Blo 1209422 4083533 := bstep (se 3 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 4083533 = 1531325) B1531325
theorem B2043731 : Blo 1209422 2043731 := bstep (se 1 (by rfl) ⟨1532798, by rfl⟩ : syracuseStep 2043731 = 3065597) B3065597
theorem B1814369 : Blo 1209422 1814369 := bstep (se 2 (by rfl) ⟨680388, by rfl⟩ : syracuseStep 1814369 = 1360777) B1360777
theorem B1814387 : Blo 1209422 1814387 := bstep (se 1 (by rfl) ⟨1360790, by rfl⟩ : syracuseStep 1814387 = 2721581) B2721581
theorem B4083587 : Blo 1209422 4083587 := bstep (se 1 (by rfl) ⟨3062690, by rfl⟩ : syracuseStep 4083587 = 6125381) B6125381
theorem B1814417 : Blo 1209422 1814417 := bstep (se 2 (by rfl) ⟨680406, by rfl⟩ : syracuseStep 1814417 = 1360813) B1360813
theorem B1937315 : Blo 1209422 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B1814435 : Blo 1209422 1814435 := bstep (se 1 (by rfl) ⟨1360826, by rfl⟩ : syracuseStep 1814435 = 2721653) B2721653
theorem B1814465 : Blo 1209422 1814465 := bstep (se 2 (by rfl) ⟨680424, by rfl⟩ : syracuseStep 1814465 = 1360849) B1360849
theorem B1814483 : Blo 1209422 1814483 := bstep (se 1 (by rfl) ⟨1360862, by rfl⟩ : syracuseStep 1814483 = 2721725) B2721725
theorem B2043859 : Blo 1209422 2043859 := bstep (se 1 (by rfl) ⟨1532894, by rfl⟩ : syracuseStep 2043859 = 3065789) B3065789
theorem B3444707 : Blo 1209422 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B1814513 : Blo 1209422 1814513 := bstep (se 2 (by rfl) ⟨680442, by rfl⟩ : syracuseStep 1814513 = 1360885) B1360885
theorem B1814531 : Blo 1209422 1814531 := bstep (se 1 (by rfl) ⟨1360898, by rfl⟩ : syracuseStep 1814531 = 2721797) B2721797
theorem B1814561 : Blo 1209422 1814561 := bstep (se 2 (by rfl) ⟨680460, by rfl⟩ : syracuseStep 1814561 = 1360921) B1360921
theorem B1937443 : Blo 1209422 1937443 := bstep (se 1 (by rfl) ⟨1453082, by rfl⟩ : syracuseStep 1937443 = 2906165) B2906165
theorem B1814579 : Blo 1209422 1814579 := bstep (se 1 (by rfl) ⟨1360934, by rfl⟩ : syracuseStep 1814579 = 2721869) B2721869
theorem B1814609 : Blo 1209422 1814609 := bstep (se 2 (by rfl) ⟨680478, by rfl⟩ : syracuseStep 1814609 = 1360957) B1360957
theorem B2723921 : Blo 1209422 2723921 := bstep (se 2 (by rfl) ⟨1021470, by rfl⟩ : syracuseStep 2723921 = 2042941) B2042941
theorem B2044001 : Blo 1209422 2044001 := bstep (se 2 (by rfl) ⟨766500, by rfl⟩ : syracuseStep 2044001 = 1533001) B1533001
theorem B1814627 : Blo 1209422 1814627 := bstep (se 1 (by rfl) ⟨1360970, by rfl⟩ : syracuseStep 1814627 = 2721941) B2721941
theorem B2723939 : Blo 1209422 2723939 := bstep (se 1 (by rfl) ⟨2042954, by rfl⟩ : syracuseStep 2723939 = 4085909) B4085909
theorem B4141165 : Blo 1209422 4141165 := bstep (se 3 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 4141165 = 1552937) B1552937
theorem B1814657 : Blo 1209422 1814657 := bstep (se 2 (by rfl) ⟨680496, by rfl⟩ : syracuseStep 1814657 = 1360993) B1360993
theorem B4083857 : Blo 1209422 4083857 := bstep (se 2 (by rfl) ⟨1531446, by rfl⟩ : syracuseStep 4083857 = 3062893) B3062893
theorem B1814675 : Blo 1209422 1814675 := bstep (se 1 (by rfl) ⟨1361006, by rfl⟩ : syracuseStep 1814675 = 2722013) B2722013
theorem B1814705 : Blo 1209422 1814705 := bstep (se 2 (by rfl) ⟨680514, by rfl⟩ : syracuseStep 1814705 = 1361029) B1361029
theorem B1724609 : Blo 1209422 1724609 := bstep (se 2 (by rfl) ⟨646728, by rfl⟩ : syracuseStep 1724609 = 1293457) B1293457
theorem B1814723 : Blo 1209422 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B1814753 : Blo 1209422 1814753 := bstep (se 2 (by rfl) ⟨680532, by rfl⟩ : syracuseStep 1814753 = 1361065) B1361065
theorem B2044129 : Blo 1209422 2044129 := bstep (se 2 (by rfl) ⟨766548, by rfl⟩ : syracuseStep 2044129 = 1533097) B1533097
theorem B6123761 : Blo 1209422 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B1814771 : Blo 1209422 1814771 := bstep (se 1 (by rfl) ⟨1361078, by rfl⟩ : syracuseStep 1814771 = 2722157) B2722157
theorem B2044163 : Blo 1209422 2044163 := bstep (se 1 (by rfl) ⟨1533122, by rfl⟩ : syracuseStep 2044163 = 3066245) B3066245
theorem B1814801 : Blo 1209422 1814801 := bstep (se 2 (by rfl) ⟨680550, by rfl⟩ : syracuseStep 1814801 = 1361101) B1361101
theorem B1724689 : Blo 1209422 1724689 := bstep (se 2 (by rfl) ⟨646758, by rfl⟩ : syracuseStep 1724689 = 1293517) B1293517
theorem B1814819 : Blo 1209422 1814819 := bstep (se 1 (by rfl) ⟨1361114, by rfl⟩ : syracuseStep 1814819 = 2722229) B2722229
theorem B1814849 : Blo 1209422 1814849 := bstep (se 2 (by rfl) ⟨680568, by rfl⟩ : syracuseStep 1814849 = 1361137) B1361137
theorem B1814867 : Blo 1209422 1814867 := bstep (se 1 (by rfl) ⟨1361150, by rfl⟩ : syracuseStep 1814867 = 2722301) B2722301
theorem B1814897 : Blo 1209422 1814897 := bstep (se 2 (by rfl) ⟨680586, by rfl⟩ : syracuseStep 1814897 = 1361173) B1361173
theorem B2724209 : Blo 1209422 2724209 := bstep (se 2 (by rfl) ⟨1021578, by rfl⟩ : syracuseStep 2724209 = 2043157) B2043157
theorem B1814915 : Blo 1209422 1814915 := bstep (se 1 (by rfl) ⟨1361186, by rfl⟩ : syracuseStep 1814915 = 2722373) B2722373
theorem B2724227 : Blo 1209422 2724227 := bstep (se 1 (by rfl) ⟨2043170, by rfl⟩ : syracuseStep 2724227 = 4086341) B4086341
theorem B1814945 : Blo 1209422 1814945 := bstep (se 2 (by rfl) ⟨680604, by rfl⟩ : syracuseStep 1814945 = 1361209) B1361209
theorem B1814963 : Blo 1209422 1814963 := bstep (se 1 (by rfl) ⟨1361222, by rfl⟩ : syracuseStep 1814963 = 2722445) B2722445
theorem B2585027 : Blo 1209422 2585027 := bstep (se 1 (by rfl) ⟨1938770, by rfl⟩ : syracuseStep 2585027 = 3877541) B3877541
theorem B14913989 : Blo 1209422 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B1814993 : Blo 1209422 1814993 := bstep (se 2 (by rfl) ⟨680622, by rfl⟩ : syracuseStep 1814993 = 1361245) B1361245
theorem B1815011 : Blo 1209422 1815011 := bstep (se 1 (by rfl) ⟨1361258, by rfl⟩ : syracuseStep 1815011 = 2722517) B2722517
theorem B1815041 : Blo 1209422 1815041 := bstep (se 2 (by rfl) ⟨680640, by rfl⟩ : syracuseStep 1815041 = 1361281) B1361281
theorem B2298385 : Blo 1209422 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B1815059 : Blo 1209422 1815059 := bstep (se 1 (by rfl) ⟨1361294, by rfl⟩ : syracuseStep 1815059 = 2722589) B2722589
theorem B1815089 : Blo 1209422 1815089 := bstep (se 2 (by rfl) ⟨680658, by rfl⟩ : syracuseStep 1815089 = 1361317) B1361317
theorem B2585137 : Blo 1209422 2585137 := bstep (se 2 (by rfl) ⟨969426, by rfl⟩ : syracuseStep 2585137 = 1938853) B1938853
theorem B1815107 : Blo 1209422 1815107 := bstep (se 1 (by rfl) ⟨1361330, by rfl⟩ : syracuseStep 1815107 = 2722661) B2722661
theorem B1938001 : Blo 1209422 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B1815137 : Blo 1209422 1815137 := bstep (se 2 (by rfl) ⟨680676, by rfl⟩ : syracuseStep 1815137 = 1361353) B1361353
theorem B1815155 : Blo 1209422 1815155 := bstep (se 1 (by rfl) ⟨1361366, by rfl⟩ : syracuseStep 1815155 = 2722733) B2722733
theorem B1634945 : Blo 1209422 1634945 := bstep (se 2 (by rfl) ⟨613104, by rfl⟩ : syracuseStep 1634945 = 1226209) B1226209
theorem B1815185 : Blo 1209422 1815185 := bstep (se 2 (by rfl) ⟨680694, by rfl⟩ : syracuseStep 1815185 = 1361389) B1361389
theorem B2724497 : Blo 1209422 2724497 := bstep (se 2 (by rfl) ⟨1021686, by rfl⟩ : syracuseStep 2724497 = 2043373) B2043373
theorem B1815203 : Blo 1209422 1815203 := bstep (se 1 (by rfl) ⟨1361402, by rfl⟩ : syracuseStep 1815203 = 2722805) B2722805
theorem B2724515 : Blo 1209422 2724515 := bstep (se 1 (by rfl) ⟨2043386, by rfl⟩ : syracuseStep 2724515 = 4086773) B4086773
theorem B1454755 : Blo 1209422 1454755 := bstep (se 1 (by rfl) ⟨1091066, by rfl⟩ : syracuseStep 1454755 = 2182133) B2182133
theorem B4084397 : Blo 1209422 4084397 := bstep (se 3 (by rfl) ⟨765824, by rfl⟩ : syracuseStep 4084397 = 1531649) B1531649
theorem B1815233 : Blo 1209422 1815233 := bstep (se 2 (by rfl) ⟨680712, by rfl⟩ : syracuseStep 1815233 = 1361425) B1361425
theorem B1815251 : Blo 1209422 1815251 := bstep (se 1 (by rfl) ⟨1361438, by rfl⟩ : syracuseStep 1815251 = 2722877) B2722877
theorem B4084451 : Blo 1209422 4084451 := bstep (se 1 (by rfl) ⟨3063338, by rfl⟩ : syracuseStep 4084451 = 6126677) B6126677
theorem B1815281 : Blo 1209422 1815281 := bstep (se 2 (by rfl) ⟨680730, by rfl⟩ : syracuseStep 1815281 = 1361461) B1361461
theorem B1815299 : Blo 1209422 1815299 := bstep (se 1 (by rfl) ⟨1361474, by rfl⟩ : syracuseStep 1815299 = 2722949) B2722949
theorem B3445517 : Blo 1209422 3445517 := bstep (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) B1292069
theorem B1815329 : Blo 1209422 1815329 := bstep (se 2 (by rfl) ⟨680748, by rfl⟩ : syracuseStep 1815329 = 1361497) B1361497
theorem B1815347 : Blo 1209422 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B1815377 : Blo 1209422 1815377 := bstep (se 2 (by rfl) ⟨680766, by rfl⟩ : syracuseStep 1815377 = 1361533) B1361533
theorem B1815395 : Blo 1209422 1815395 := bstep (se 1 (by rfl) ⟨1361546, by rfl⟩ : syracuseStep 1815395 = 2723093) B2723093
theorem B1815425 : Blo 1209422 1815425 := bstep (se 2 (by rfl) ⟨680784, by rfl⟩ : syracuseStep 1815425 = 1361569) B1361569
theorem B1815443 : Blo 1209422 1815443 := bstep (se 1 (by rfl) ⟨1361582, by rfl⟩ : syracuseStep 1815443 = 2723165) B2723165
theorem B1815473 : Blo 1209422 1815473 := bstep (se 2 (by rfl) ⟨680802, by rfl⟩ : syracuseStep 1815473 = 1361605) B1361605
theorem B2724785 : Blo 1209422 2724785 := bstep (se 2 (by rfl) ⟨1021794, by rfl⟩ : syracuseStep 2724785 = 2043589) B2043589
theorem B3445699 : Blo 1209422 3445699 := bstep (se 1 (by rfl) ⟨2584274, by rfl⟩ : syracuseStep 3445699 = 5168549) B5168549
theorem B1815491 : Blo 1209422 1815491 := bstep (se 1 (by rfl) ⟨1361618, by rfl⟩ : syracuseStep 1815491 = 2723237) B2723237
theorem B2724803 : Blo 1209422 2724803 := bstep (se 1 (by rfl) ⟨2043602, by rfl⟩ : syracuseStep 2724803 = 4087205) B4087205
theorem B1815521 : Blo 1209422 1815521 := bstep (se 2 (by rfl) ⟨680820, by rfl⟩ : syracuseStep 1815521 = 1361641) B1361641
theorem B4084721 : Blo 1209422 4084721 := bstep (se 2 (by rfl) ⟨1531770, by rfl⟩ : syracuseStep 4084721 = 3063541) B3063541
theorem B1815539 : Blo 1209422 1815539 := bstep (se 1 (by rfl) ⟨1361654, by rfl⟩ : syracuseStep 1815539 = 2723309) B2723309
theorem B1815569 : Blo 1209422 1815569 := bstep (se 2 (by rfl) ⟨680838, by rfl⟩ : syracuseStep 1815569 = 1361677) B1361677
theorem B1815587 : Blo 1209422 1815587 := bstep (se 1 (by rfl) ⟨1361690, by rfl⟩ : syracuseStep 1815587 = 2723381) B2723381
theorem B1815617 : Blo 1209422 1815617 := bstep (se 2 (by rfl) ⟨680856, by rfl⟩ : syracuseStep 1815617 = 1361713) B1361713
theorem B1209427 : Blo 1209422 1209427 := bstep (se 1 (by rfl) ⟨907070, by rfl⟩ : syracuseStep 1209427 = 1814141) B1814141
theorem B1815635 : Blo 1209422 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B1209443 : Blo 1209422 1209443 := bstep (se 1 (by rfl) ⟨907082, by rfl⟩ : syracuseStep 1209443 = 1814165) B1814165
theorem B1815665 : Blo 1209422 1815665 := bstep (se 2 (by rfl) ⟨680874, by rfl⟩ : syracuseStep 1815665 = 1361749) B1361749
theorem B1209459 : Blo 1209422 1209459 := bstep (se 1 (by rfl) ⟨907094, by rfl⟩ : syracuseStep 1209459 = 1814189) B1814189
theorem B1209475 : Blo 1209422 1209475 := bstep (se 1 (by rfl) ⟨907106, by rfl⟩ : syracuseStep 1209475 = 1814213) B1814213
theorem B1815683 : Blo 1209422 1815683 := bstep (se 1 (by rfl) ⟨1361762, by rfl⟩ : syracuseStep 1815683 = 2723525) B2723525
theorem B1455235 : Blo 1209422 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B1209491 : Blo 1209422 1209491 := bstep (se 1 (by rfl) ⟨907118, by rfl⟩ : syracuseStep 1209491 = 1814237) B1814237
theorem B1815713 : Blo 1209422 1815713 := bstep (se 2 (by rfl) ⟨680892, by rfl⟩ : syracuseStep 1815713 = 1361785) B1361785
theorem B1209507 : Blo 1209422 1209507 := bstep (se 1 (by rfl) ⟨907130, by rfl⟩ : syracuseStep 1209507 = 1814261) B1814261
theorem B1209523 : Blo 1209422 1209523 := bstep (se 1 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 1209523 = 1814285) B1814285
theorem B1815731 : Blo 1209422 1815731 := bstep (se 1 (by rfl) ⟨1361798, by rfl⟩ : syracuseStep 1815731 = 2723597) B2723597
theorem B1209539 : Blo 1209422 1209539 := bstep (se 1 (by rfl) ⟨907154, by rfl⟩ : syracuseStep 1209539 = 1814309) B1814309
theorem B1815761 : Blo 1209422 1815761 := bstep (se 2 (by rfl) ⟨680910, by rfl⟩ : syracuseStep 1815761 = 1361821) B1361821
theorem B2725073 : Blo 1209422 2725073 := bstep (se 2 (by rfl) ⟨1021902, by rfl⟩ : syracuseStep 2725073 = 2043805) B2043805
theorem B1209555 : Blo 1209422 1209555 := bstep (se 1 (by rfl) ⟨907166, by rfl⟩ : syracuseStep 1209555 = 1814333) B1814333
theorem B1209571 : Blo 1209422 1209571 := bstep (se 1 (by rfl) ⟨907178, by rfl⟩ : syracuseStep 1209571 = 1814357) B1814357
theorem B1815779 : Blo 1209422 1815779 := bstep (se 1 (by rfl) ⟨1361834, by rfl⟩ : syracuseStep 1815779 = 2723669) B2723669
theorem B2725091 : Blo 1209422 2725091 := bstep (se 1 (by rfl) ⟨2043818, by rfl⟩ : syracuseStep 2725091 = 4087637) B4087637
theorem B1938673 : Blo 1209422 1938673 := bstep (se 2 (by rfl) ⟨727002, by rfl⟩ : syracuseStep 1938673 = 1454005) B1454005
theorem B2454769 : Blo 1209422 2454769 := bstep (se 2 (by rfl) ⟨920538, by rfl⟩ : syracuseStep 2454769 = 1841077) B1841077
theorem B1209587 : Blo 1209422 1209587 := bstep (se 1 (by rfl) ⟨907190, by rfl⟩ : syracuseStep 1209587 = 1814381) B1814381
theorem B2069761 : Blo 1209422 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1815809 : Blo 1209422 1815809 := bstep (se 2 (by rfl) ⟨680928, by rfl⟩ : syracuseStep 1815809 = 1361857) B1361857
theorem B1209603 : Blo 1209422 1209603 := bstep (se 1 (by rfl) ⟨907202, by rfl⟩ : syracuseStep 1209603 = 1814405) B1814405
theorem B1209619 : Blo 1209422 1209619 := bstep (se 1 (by rfl) ⟨907214, by rfl⟩ : syracuseStep 1209619 = 1814429) B1814429
theorem B1815827 : Blo 1209422 1815827 := bstep (se 1 (by rfl) ⟨1361870, by rfl⟩ : syracuseStep 1815827 = 2723741) B2723741
theorem B1209635 : Blo 1209422 1209635 := bstep (se 1 (by rfl) ⟨907226, by rfl⟩ : syracuseStep 1209635 = 1814453) B1814453
theorem B5174563 : Blo 1209422 5174563 := bstep (se 1 (by rfl) ⟨3880922, by rfl⟩ : syracuseStep 5174563 = 7761845) B7761845
theorem B1815857 : Blo 1209422 1815857 := bstep (se 2 (by rfl) ⟨680946, by rfl⟩ : syracuseStep 1815857 = 1361893) B1361893
theorem B1209651 : Blo 1209422 1209651 := bstep (se 1 (by rfl) ⟨907238, by rfl⟩ : syracuseStep 1209651 = 1814477) B1814477
theorem B1209667 : Blo 1209422 1209667 := bstep (se 1 (by rfl) ⟨907250, by rfl⟩ : syracuseStep 1209667 = 1814501) B1814501
theorem B1815875 : Blo 1209422 1815875 := bstep (se 1 (by rfl) ⟨1361906, by rfl⟩ : syracuseStep 1815875 = 2723813) B2723813
theorem B5166413 : Blo 1209422 5166413 := bstep (se 3 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 5166413 = 1937405) B1937405
theorem B1209683 : Blo 1209422 1209683 := bstep (se 1 (by rfl) ⟨907262, by rfl⟩ : syracuseStep 1209683 = 1814525) B1814525
theorem B1815905 : Blo 1209422 1815905 := bstep (se 2 (by rfl) ⟨680964, by rfl⟩ : syracuseStep 1815905 = 1361929) B1361929
theorem B1209699 : Blo 1209422 1209699 := bstep (se 1 (by rfl) ⟨907274, by rfl⟩ : syracuseStep 1209699 = 1814549) B1814549
theorem B1209715 : Blo 1209422 1209715 := bstep (se 1 (by rfl) ⟨907286, by rfl⟩ : syracuseStep 1209715 = 1814573) B1814573
theorem B1815923 : Blo 1209422 1815923 := bstep (se 1 (by rfl) ⟨1361942, by rfl⟩ : syracuseStep 1815923 = 2723885) B2723885
theorem B1209731 : Blo 1209422 1209731 := bstep (se 1 (by rfl) ⟨907298, by rfl⟩ : syracuseStep 1209731 = 1814597) B1814597
theorem B4142477 : Blo 1209422 4142477 := bstep (se 3 (by rfl) ⟨776714, by rfl⟩ : syracuseStep 4142477 = 1553429) B1553429
theorem B1815953 : Blo 1209422 1815953 := bstep (se 2 (by rfl) ⟨680982, by rfl⟩ : syracuseStep 1815953 = 1361965) B1361965
theorem B1209747 : Blo 1209422 1209747 := bstep (se 1 (by rfl) ⟨907310, by rfl⟩ : syracuseStep 1209747 = 1814621) B1814621
theorem B1209763 : Blo 1209422 1209763 := bstep (se 1 (by rfl) ⟨907322, by rfl⟩ : syracuseStep 1209763 = 1814645) B1814645
theorem B1815971 : Blo 1209422 1815971 := bstep (se 1 (by rfl) ⟨1361978, by rfl⟩ : syracuseStep 1815971 = 2723957) B2723957
theorem B3446189 : Blo 1209422 3446189 := bstep (se 3 (by rfl) ⟨646160, by rfl⟩ : syracuseStep 3446189 = 1292321) B1292321
theorem B1209779 : Blo 1209422 1209779 := bstep (se 1 (by rfl) ⟨907334, by rfl⟩ : syracuseStep 1209779 = 1814669) B1814669
theorem B1816001 : Blo 1209422 1816001 := bstep (se 2 (by rfl) ⟨681000, by rfl⟩ : syracuseStep 1816001 = 1362001) B1362001
theorem B1209795 : Blo 1209422 1209795 := bstep (se 1 (by rfl) ⟨907346, by rfl⟩ : syracuseStep 1209795 = 1814693) B1814693
theorem B1209811 : Blo 1209422 1209811 := bstep (se 1 (by rfl) ⟨907358, by rfl⟩ : syracuseStep 1209811 = 1814717) B1814717
theorem B1816019 : Blo 1209422 1816019 := bstep (se 1 (by rfl) ⟨1362014, by rfl⟩ : syracuseStep 1816019 = 2724029) B2724029
theorem B1209827 : Blo 1209422 1209827 := bstep (se 1 (by rfl) ⟨907370, by rfl⟩ : syracuseStep 1209827 = 1814741) B1814741
theorem B1816049 : Blo 1209422 1816049 := bstep (se 2 (by rfl) ⟨681018, by rfl⟩ : syracuseStep 1816049 = 1362037) B1362037
theorem B2725361 : Blo 1209422 2725361 := bstep (se 2 (by rfl) ⟨1022010, by rfl⟩ : syracuseStep 2725361 = 2044021) B2044021
theorem B1209843 : Blo 1209422 1209843 := bstep (se 1 (by rfl) ⟨907382, by rfl⟩ : syracuseStep 1209843 = 1814765) B1814765
theorem B1209859 : Blo 1209422 1209859 := bstep (se 1 (by rfl) ⟨907394, by rfl⟩ : syracuseStep 1209859 = 1814789) B1814789
theorem B1816067 : Blo 1209422 1816067 := bstep (se 1 (by rfl) ⟨1362050, by rfl⟩ : syracuseStep 1816067 = 2724101) B2724101
theorem B2725379 : Blo 1209422 2725379 := bstep (se 1 (by rfl) ⟨2044034, by rfl⟩ : syracuseStep 2725379 = 4088069) B4088069
theorem B4085261 : Blo 1209422 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B1209875 : Blo 1209422 1209875 := bstep (se 1 (by rfl) ⟨907406, by rfl⟩ : syracuseStep 1209875 = 1814813) B1814813
theorem B1816097 : Blo 1209422 1816097 := bstep (se 2 (by rfl) ⟨681036, by rfl⟩ : syracuseStep 1816097 = 1362073) B1362073
theorem B1209891 : Blo 1209422 1209891 := bstep (se 1 (by rfl) ⟨907418, by rfl⟩ : syracuseStep 1209891 = 1814837) B1814837
theorem B2299441 : Blo 1209422 2299441 := bstep (se 2 (by rfl) ⟨862290, by rfl⟩ : syracuseStep 2299441 = 1724581) B1724581
theorem B1209907 : Blo 1209422 1209907 := bstep (se 1 (by rfl) ⟨907430, by rfl⟩ : syracuseStep 1209907 = 1814861) B1814861
theorem B1816115 : Blo 1209422 1816115 := bstep (se 1 (by rfl) ⟨1362086, by rfl⟩ : syracuseStep 1816115 = 2724173) B2724173
theorem B1209923 : Blo 1209422 1209923 := bstep (se 1 (by rfl) ⟨907442, by rfl⟩ : syracuseStep 1209923 = 1814885) B1814885
theorem B4085315 : Blo 1209422 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B1816145 : Blo 1209422 1816145 := bstep (se 2 (by rfl) ⟨681054, by rfl⟩ : syracuseStep 1816145 = 1362109) B1362109
theorem B1209939 : Blo 1209422 1209939 := bstep (se 1 (by rfl) ⟨907454, by rfl⟩ : syracuseStep 1209939 = 1814909) B1814909
theorem B13080163 : Blo 1209422 13080163 := bstep (se 1 (by rfl) ⟨9810122, by rfl⟩ : syracuseStep 13080163 = 19620245) B19620245
theorem B1209955 : Blo 1209422 1209955 := bstep (se 1 (by rfl) ⟨907466, by rfl⟩ : syracuseStep 1209955 = 1814933) B1814933
theorem B1816163 : Blo 1209422 1816163 := bstep (se 1 (by rfl) ⟨1362122, by rfl⟩ : syracuseStep 1816163 = 2724245) B2724245
theorem B1209971 : Blo 1209422 1209971 := bstep (se 1 (by rfl) ⟨907478, by rfl⟩ : syracuseStep 1209971 = 1814957) B1814957
theorem B1816193 : Blo 1209422 1816193 := bstep (se 2 (by rfl) ⟨681072, by rfl⟩ : syracuseStep 1816193 = 1362145) B1362145
theorem B1209987 : Blo 1209422 1209987 := bstep (se 1 (by rfl) ⟨907490, by rfl⟩ : syracuseStep 1209987 = 1814981) B1814981
theorem B4593293 : Blo 1209422 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B1210003 : Blo 1209422 1210003 := bstep (se 1 (by rfl) ⟨907502, by rfl⟩ : syracuseStep 1210003 = 1815005) B1815005
theorem B1816211 : Blo 1209422 1816211 := bstep (se 1 (by rfl) ⟨1362158, by rfl⟩ : syracuseStep 1816211 = 2724317) B2724317
theorem B6125219 : Blo 1209422 6125219 := bstep (se 1 (by rfl) ⟨4593914, by rfl⟩ : syracuseStep 6125219 = 9187829) B9187829
theorem B1210019 : Blo 1209422 1210019 := bstep (se 1 (by rfl) ⟨907514, by rfl⟩ : syracuseStep 1210019 = 1815029) B1815029
theorem B1816241 : Blo 1209422 1816241 := bstep (se 2 (by rfl) ⟨681090, by rfl⟩ : syracuseStep 1816241 = 1362181) B1362181
theorem B1210035 : Blo 1209422 1210035 := bstep (se 1 (by rfl) ⟨907526, by rfl⟩ : syracuseStep 1210035 = 1815053) B1815053
theorem B1210051 : Blo 1209422 1210051 := bstep (se 1 (by rfl) ⟨907538, by rfl⟩ : syracuseStep 1210051 = 1815077) B1815077
theorem B1816259 : Blo 1209422 1816259 := bstep (se 1 (by rfl) ⟨1362194, by rfl⟩ : syracuseStep 1816259 = 2724389) B2724389
theorem B3274445 : Blo 1209422 3274445 := bstep (se 3 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 3274445 = 1227917) B1227917
theorem B1210067 : Blo 1209422 1210067 := bstep (se 1 (by rfl) ⟨907550, by rfl⟩ : syracuseStep 1210067 = 1815101) B1815101
theorem B1816289 : Blo 1209422 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B1210083 : Blo 1209422 1210083 := bstep (se 1 (by rfl) ⟨907562, by rfl⟩ : syracuseStep 1210083 = 1815125) B1815125
theorem B1210099 : Blo 1209422 1210099 := bstep (se 1 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 1210099 = 1815149) B1815149
theorem B1816307 : Blo 1209422 1816307 := bstep (se 1 (by rfl) ⟨1362230, by rfl⟩ : syracuseStep 1816307 = 2724461) B2724461
theorem B1210115 : Blo 1209422 1210115 := bstep (se 1 (by rfl) ⟨907586, by rfl⟩ : syracuseStep 1210115 = 1815173) B1815173
theorem B1816337 : Blo 1209422 1816337 := bstep (se 2 (by rfl) ⟨681126, by rfl⟩ : syracuseStep 1816337 = 1362253) B1362253
theorem B1210131 : Blo 1209422 1210131 := bstep (se 1 (by rfl) ⟨907598, by rfl⟩ : syracuseStep 1210131 = 1815197) B1815197
theorem B2725649 : Blo 1209422 2725649 := bstep (se 2 (by rfl) ⟨1022118, by rfl⟩ : syracuseStep 2725649 = 2044237) B2044237
theorem B1210147 : Blo 1209422 1210147 := bstep (se 1 (by rfl) ⟨907610, by rfl⟩ : syracuseStep 1210147 = 1815221) B1815221
theorem B1816355 : Blo 1209422 1816355 := bstep (se 1 (by rfl) ⟨1362266, by rfl⟩ : syracuseStep 1816355 = 2724533) B2724533
theorem B2725667 : Blo 1209422 2725667 := bstep (se 1 (by rfl) ⟨2044250, by rfl⟩ : syracuseStep 2725667 = 4088501) B4088501
theorem B1210163 : Blo 1209422 1210163 := bstep (se 1 (by rfl) ⟨907622, by rfl⟩ : syracuseStep 1210163 = 1815245) B1815245
theorem B1816385 : Blo 1209422 1816385 := bstep (se 2 (by rfl) ⟨681144, by rfl⟩ : syracuseStep 1816385 = 1362289) B1362289
theorem B1210179 : Blo 1209422 1210179 := bstep (se 1 (by rfl) ⟨907634, by rfl⟩ : syracuseStep 1210179 = 1815269) B1815269
theorem B3880781 : Blo 1209422 3880781 := bstep (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) B1455293
theorem B4085585 : Blo 1209422 4085585 := bstep (se 2 (by rfl) ⟨1532094, by rfl⟩ : syracuseStep 4085585 = 3064189) B3064189
theorem B1210195 : Blo 1209422 1210195 := bstep (se 1 (by rfl) ⟨907646, by rfl⟩ : syracuseStep 1210195 = 1815293) B1815293
theorem B1816403 : Blo 1209422 1816403 := bstep (se 1 (by rfl) ⟨1362302, by rfl⟩ : syracuseStep 1816403 = 2724605) B2724605
theorem B1210211 : Blo 1209422 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B1816433 : Blo 1209422 1816433 := bstep (se 2 (by rfl) ⟨681162, by rfl⟩ : syracuseStep 1816433 = 1362325) B1362325
theorem B1210227 : Blo 1209422 1210227 := bstep (se 1 (by rfl) ⟨907670, by rfl⟩ : syracuseStep 1210227 = 1815341) B1815341
theorem B1210243 : Blo 1209422 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B1816451 : Blo 1209422 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B3192721 : Blo 1209422 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B1210259 : Blo 1209422 1210259 := bstep (se 1 (by rfl) ⟨907694, by rfl⟩ : syracuseStep 1210259 = 1815389) B1815389
theorem B1816481 : Blo 1209422 1816481 := bstep (se 2 (by rfl) ⟨681180, by rfl⟩ : syracuseStep 1816481 = 1362361) B1362361
theorem B1210275 : Blo 1209422 1210275 := bstep (se 1 (by rfl) ⟨907706, by rfl⟩ : syracuseStep 1210275 = 1815413) B1815413
theorem B1963955 : Blo 1209422 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B1210291 : Blo 1209422 1210291 := bstep (se 1 (by rfl) ⟨907718, by rfl⟩ : syracuseStep 1210291 = 1815437) B1815437
theorem B1816499 : Blo 1209422 1816499 := bstep (se 1 (by rfl) ⟨1362374, by rfl⟩ : syracuseStep 1816499 = 2724749) B2724749
theorem B1210307 : Blo 1209422 1210307 := bstep (se 1 (by rfl) ⟨907730, by rfl⟩ : syracuseStep 1210307 = 1815461) B1815461
theorem B1816529 : Blo 1209422 1816529 := bstep (se 2 (by rfl) ⟨681198, by rfl⟩ : syracuseStep 1816529 = 1362397) B1362397
theorem B1210323 : Blo 1209422 1210323 := bstep (se 1 (by rfl) ⟨907742, by rfl⟩ : syracuseStep 1210323 = 1815485) B1815485
theorem B1210339 : Blo 1209422 1210339 := bstep (se 1 (by rfl) ⟨907754, by rfl⟩ : syracuseStep 1210339 = 1815509) B1815509
theorem B1816547 : Blo 1209422 1816547 := bstep (se 1 (by rfl) ⟨1362410, by rfl⟩ : syracuseStep 1816547 = 2724821) B2724821
theorem B1210355 : Blo 1209422 1210355 := bstep (se 1 (by rfl) ⟨907766, by rfl⟩ : syracuseStep 1210355 = 1815533) B1815533
theorem B1816577 : Blo 1209422 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B1210371 : Blo 1209422 1210371 := bstep (se 1 (by rfl) ⟨907778, by rfl⟩ : syracuseStep 1210371 = 1815557) B1815557
theorem B1210387 : Blo 1209422 1210387 := bstep (se 1 (by rfl) ⟨907790, by rfl⟩ : syracuseStep 1210387 = 1815581) B1815581
theorem B1816595 : Blo 1209422 1816595 := bstep (se 1 (by rfl) ⟨1362446, by rfl⟩ : syracuseStep 1816595 = 2724893) B2724893
theorem B1210403 : Blo 1209422 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B6633521 : Blo 1209422 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B1816625 : Blo 1209422 1816625 := bstep (se 2 (by rfl) ⟨681234, by rfl⟩ : syracuseStep 1816625 = 1362469) B1362469
theorem B1210419 : Blo 1209422 1210419 := bstep (se 1 (by rfl) ⟨907814, by rfl⟩ : syracuseStep 1210419 = 1815629) B1815629
theorem B1210435 : Blo 1209422 1210435 := bstep (se 1 (by rfl) ⟨907826, by rfl⟩ : syracuseStep 1210435 = 1815653) B1815653
theorem B1816643 : Blo 1209422 1816643 := bstep (se 1 (by rfl) ⟨1362482, by rfl⟩ : syracuseStep 1816643 = 2724965) B2724965
theorem B1210451 : Blo 1209422 1210451 := bstep (se 1 (by rfl) ⟨907838, by rfl⟩ : syracuseStep 1210451 = 1815677) B1815677
theorem B1816673 : Blo 1209422 1816673 := bstep (se 2 (by rfl) ⟨681252, by rfl⟩ : syracuseStep 1816673 = 1362505) B1362505
theorem B1210467 : Blo 1209422 1210467 := bstep (se 1 (by rfl) ⟨907850, by rfl⟩ : syracuseStep 1210467 = 1815701) B1815701
theorem B13080689 : Blo 1209422 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B1210483 : Blo 1209422 1210483 := bstep (se 1 (by rfl) ⟨907862, by rfl⟩ : syracuseStep 1210483 = 1815725) B1815725
theorem B1816691 : Blo 1209422 1816691 := bstep (se 1 (by rfl) ⟨1362518, by rfl⟩ : syracuseStep 1816691 = 2725037) B2725037
theorem B2906243 : Blo 1209422 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B1210499 : Blo 1209422 1210499 := bstep (se 1 (by rfl) ⟨907874, by rfl⟩ : syracuseStep 1210499 = 1815749) B1815749
theorem B2947217 : Blo 1209422 2947217 := bstep (se 2 (by rfl) ⟨1105206, by rfl⟩ : syracuseStep 2947217 = 2210413) B2210413
theorem B1816721 : Blo 1209422 1816721 := bstep (se 2 (by rfl) ⟨681270, by rfl⟩ : syracuseStep 1816721 = 1362541) B1362541
theorem B1210515 : Blo 1209422 1210515 := bstep (se 1 (by rfl) ⟨907886, by rfl⟩ : syracuseStep 1210515 = 1815773) B1815773
theorem B1210531 : Blo 1209422 1210531 := bstep (se 1 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 1210531 = 1815797) B1815797
theorem B1816739 : Blo 1209422 1816739 := bstep (se 1 (by rfl) ⟨1362554, by rfl⟩ : syracuseStep 1816739 = 2725109) B2725109
theorem B6895793 : Blo 1209422 6895793 := bstep (se 2 (by rfl) ⟨2585922, by rfl⟩ : syracuseStep 6895793 = 5171845) B5171845
theorem B1210547 : Blo 1209422 1210547 := bstep (se 1 (by rfl) ⟨907910, by rfl⟩ : syracuseStep 1210547 = 1815821) B1815821
theorem B1816769 : Blo 1209422 1816769 := bstep (se 2 (by rfl) ⟨681288, by rfl⟩ : syracuseStep 1816769 = 1362577) B1362577
theorem B1292483 : Blo 1209422 1292483 := bstep (se 1 (by rfl) ⟨969362, by rfl⟩ : syracuseStep 1292483 = 1938725) B1938725
theorem B1210563 : Blo 1209422 1210563 := bstep (se 1 (by rfl) ⟨907922, by rfl⟩ : syracuseStep 1210563 = 1815845) B1815845
theorem B1210579 : Blo 1209422 1210579 := bstep (se 1 (by rfl) ⟨907934, by rfl⟩ : syracuseStep 1210579 = 1815869) B1815869
theorem B1816787 : Blo 1209422 1816787 := bstep (se 1 (by rfl) ⟨1362590, by rfl⟩ : syracuseStep 1816787 = 2725181) B2725181
theorem B1210595 : Blo 1209422 1210595 := bstep (se 1 (by rfl) ⟨907946, by rfl⟩ : syracuseStep 1210595 = 1815893) B1815893
theorem B1816817 : Blo 1209422 1816817 := bstep (se 2 (by rfl) ⟨681306, by rfl⟩ : syracuseStep 1816817 = 1362613) B1362613
theorem B1210611 : Blo 1209422 1210611 := bstep (se 1 (by rfl) ⟨907958, by rfl⟩ : syracuseStep 1210611 = 1815917) B1815917
theorem B1210627 : Blo 1209422 1210627 := bstep (se 1 (by rfl) ⟨907970, by rfl⟩ : syracuseStep 1210627 = 1815941) B1815941
theorem B1816835 : Blo 1209422 1816835 := bstep (se 1 (by rfl) ⟨1362626, by rfl⟩ : syracuseStep 1816835 = 2725253) B2725253
theorem B3062033 : Blo 1209422 3062033 := bstep (se 2 (by rfl) ⟨1148262, by rfl⟩ : syracuseStep 3062033 = 2296525) B2296525
theorem B1210643 : Blo 1209422 1210643 := bstep (se 1 (by rfl) ⟨907982, by rfl⟩ : syracuseStep 1210643 = 1815965) B1815965
theorem B1816865 : Blo 1209422 1816865 := bstep (se 2 (by rfl) ⟨681324, by rfl⟩ : syracuseStep 1816865 = 1362649) B1362649
theorem B1210659 : Blo 1209422 1210659 := bstep (se 1 (by rfl) ⟨907994, by rfl⟩ : syracuseStep 1210659 = 1815989) B1815989
theorem B1210675 : Blo 1209422 1210675 := bstep (se 1 (by rfl) ⟨908006, by rfl⟩ : syracuseStep 1210675 = 1816013) B1816013
theorem B1939763 : Blo 1209422 1939763 := bstep (se 1 (by rfl) ⟨1454822, by rfl⟩ : syracuseStep 1939763 = 2909645) B2909645
theorem B1816883 : Blo 1209422 1816883 := bstep (se 1 (by rfl) ⟨1362662, by rfl⟩ : syracuseStep 1816883 = 2725325) B2725325
theorem B2906435 : Blo 1209422 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B3062083 : Blo 1209422 3062083 := bstep (se 1 (by rfl) ⟨2296562, by rfl⟩ : syracuseStep 3062083 = 4593125) B4593125
theorem B1210691 : Blo 1209422 1210691 := bstep (se 1 (by rfl) ⟨908018, by rfl⟩ : syracuseStep 1210691 = 1816037) B1816037
theorem B8730949 : Blo 1209422 8730949 := bstep (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) B1637053
theorem B1816913 : Blo 1209422 1816913 := bstep (se 2 (by rfl) ⟨681342, by rfl⟩ : syracuseStep 1816913 = 1362685) B1362685
theorem B1210707 : Blo 1209422 1210707 := bstep (se 1 (by rfl) ⟨908030, by rfl⟩ : syracuseStep 1210707 = 1816061) B1816061
theorem B1210723 : Blo 1209422 1210723 := bstep (se 1 (by rfl) ⟨908042, by rfl⟩ : syracuseStep 1210723 = 1816085) B1816085
theorem B1816931 : Blo 1209422 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B4086125 : Blo 1209422 4086125 := bstep (se 3 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 4086125 = 1532297) B1532297
theorem B1210739 : Blo 1209422 1210739 := bstep (se 1 (by rfl) ⟨908054, by rfl⟩ : syracuseStep 1210739 = 1816109) B1816109
theorem B1816961 : Blo 1209422 1816961 := bstep (se 2 (by rfl) ⟨681360, by rfl⟩ : syracuseStep 1816961 = 1362721) B1362721
theorem B1210755 : Blo 1209422 1210755 := bstep (se 1 (by rfl) ⟨908066, by rfl⟩ : syracuseStep 1210755 = 1816133) B1816133
theorem B12417421 : Blo 1209422 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B9189773 : Blo 1209422 9189773 := bstep (se 3 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 9189773 = 3446165) B3446165
theorem B1210771 : Blo 1209422 1210771 := bstep (se 1 (by rfl) ⟨908078, by rfl⟩ : syracuseStep 1210771 = 1816157) B1816157
theorem B1816979 : Blo 1209422 1816979 := bstep (se 1 (by rfl) ⟨1362734, by rfl⟩ : syracuseStep 1816979 = 2725469) B2725469
theorem B2619811 : Blo 1209422 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B4086179 : Blo 1209422 4086179 := bstep (se 1 (by rfl) ⟨3064634, by rfl⟩ : syracuseStep 4086179 = 6129269) B6129269
theorem B1210787 : Blo 1209422 1210787 := bstep (se 1 (by rfl) ⟨908090, by rfl⟩ : syracuseStep 1210787 = 1816181) B1816181
theorem B4594097 : Blo 1209422 4594097 := bstep (se 2 (by rfl) ⟨1722786, by rfl⟩ : syracuseStep 4594097 = 3445573) B3445573
theorem B1817009 : Blo 1209422 1817009 := bstep (se 2 (by rfl) ⟨681378, by rfl⟩ : syracuseStep 1817009 = 1362757) B1362757
theorem B1210803 : Blo 1209422 1210803 := bstep (se 1 (by rfl) ⟨908102, by rfl⟩ : syracuseStep 1210803 = 1816205) B1816205
theorem B1210819 : Blo 1209422 1210819 := bstep (se 1 (by rfl) ⟨908114, by rfl⟩ : syracuseStep 1210819 = 1816229) B1816229
theorem B1817027 : Blo 1209422 1817027 := bstep (se 1 (by rfl) ⟨1362770, by rfl⟩ : syracuseStep 1817027 = 2725541) B2725541
theorem B6126029 : Blo 1209422 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B7363021 : Blo 1209422 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B3062225 : Blo 1209422 3062225 := bstep (se 2 (by rfl) ⟨1148334, by rfl⟩ : syracuseStep 3062225 = 2296669) B2296669
theorem B1210835 : Blo 1209422 1210835 := bstep (se 1 (by rfl) ⟨908126, by rfl⟩ : syracuseStep 1210835 = 1816253) B1816253
theorem B1817057 : Blo 1209422 1817057 := bstep (se 2 (by rfl) ⟨681396, by rfl⟩ : syracuseStep 1817057 = 1362793) B1362793
theorem B1210851 : Blo 1209422 1210851 := bstep (se 1 (by rfl) ⟨908138, by rfl⟩ : syracuseStep 1210851 = 1816277) B1816277
theorem B1210867 : Blo 1209422 1210867 := bstep (se 1 (by rfl) ⟨908150, by rfl⟩ : syracuseStep 1210867 = 1816301) B1816301
theorem B1817075 : Blo 1209422 1817075 := bstep (se 1 (by rfl) ⟨1362806, by rfl⟩ : syracuseStep 1817075 = 2725613) B2725613
theorem B1210883 : Blo 1209422 1210883 := bstep (se 1 (by rfl) ⟨908162, by rfl⟩ : syracuseStep 1210883 = 1816325) B1816325
theorem B2587153 : Blo 1209422 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B1817105 : Blo 1209422 1817105 := bstep (se 2 (by rfl) ⟨681414, by rfl⟩ : syracuseStep 1817105 = 1362829) B1362829
theorem B1210899 : Blo 1209422 1210899 := bstep (se 1 (by rfl) ⟨908174, by rfl⟩ : syracuseStep 1210899 = 1816349) B1816349
theorem B1210915 : Blo 1209422 1210915 := bstep (se 1 (by rfl) ⟨908186, by rfl⟩ : syracuseStep 1210915 = 1816373) B1816373
theorem B1817123 : Blo 1209422 1817123 := bstep (se 1 (by rfl) ⟨1362842, by rfl⟩ : syracuseStep 1817123 = 2725685) B2725685
theorem B1210931 : Blo 1209422 1210931 := bstep (se 1 (by rfl) ⟨908198, by rfl⟩ : syracuseStep 1210931 = 1816397) B1816397
theorem B1210947 : Blo 1209422 1210947 := bstep (se 1 (by rfl) ⟨908210, by rfl⟩ : syracuseStep 1210947 = 1816421) B1816421
theorem B3447373 : Blo 1209422 3447373 := bstep (se 3 (by rfl) ⟨646382, by rfl⟩ : syracuseStep 3447373 = 1292765) B1292765
theorem B1210963 : Blo 1209422 1210963 := bstep (se 1 (by rfl) ⟨908222, by rfl⟩ : syracuseStep 1210963 = 1816445) B1816445
theorem B1210979 : Blo 1209422 1210979 := bstep (se 1 (by rfl) ⟨908234, by rfl⟩ : syracuseStep 1210979 = 1816469) B1816469
theorem B1210995 : Blo 1209422 1210995 := bstep (se 1 (by rfl) ⟨908246, by rfl⟩ : syracuseStep 1210995 = 1816493) B1816493
theorem B1211011 : Blo 1209422 1211011 := bstep (se 1 (by rfl) ⟨908258, by rfl⟩ : syracuseStep 1211011 = 1816517) B1816517
theorem B1211027 : Blo 1209422 1211027 := bstep (se 1 (by rfl) ⟨908270, by rfl⟩ : syracuseStep 1211027 = 1816541) B1816541
theorem B1211043 : Blo 1209422 1211043 := bstep (se 1 (by rfl) ⟨908282, by rfl⟩ : syracuseStep 1211043 = 1816565) B1816565
theorem B4086449 : Blo 1209422 4086449 := bstep (se 2 (by rfl) ⟨1532418, by rfl⟩ : syracuseStep 4086449 = 3064837) B3064837
theorem B1211059 : Blo 1209422 1211059 := bstep (se 1 (by rfl) ⟨908294, by rfl⟩ : syracuseStep 1211059 = 1816589) B1816589
theorem B1211075 : Blo 1209422 1211075 := bstep (se 1 (by rfl) ⟨908306, by rfl⟩ : syracuseStep 1211075 = 1816613) B1816613
theorem B20970181 : Blo 1209422 20970181 := bstep (se 4 (by rfl) ⟨1965954, by rfl⟩ : syracuseStep 20970181 = 3931909) B3931909
theorem B1211091 : Blo 1209422 1211091 := bstep (se 1 (by rfl) ⟨908318, by rfl⟩ : syracuseStep 1211091 = 1816637) B1816637
theorem B1211107 : Blo 1209422 1211107 := bstep (se 1 (by rfl) ⟨908330, by rfl⟩ : syracuseStep 1211107 = 1816661) B1816661
theorem B1211123 : Blo 1209422 1211123 := bstep (se 1 (by rfl) ⟨908342, by rfl⟩ : syracuseStep 1211123 = 1816685) B1816685
theorem B1211139 : Blo 1209422 1211139 := bstep (se 1 (by rfl) ⟨908354, by rfl⟩ : syracuseStep 1211139 = 1816709) B1816709
theorem B1211155 : Blo 1209422 1211155 := bstep (se 1 (by rfl) ⟨908366, by rfl⟩ : syracuseStep 1211155 = 1816733) B1816733
theorem B1211171 : Blo 1209422 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B1211187 : Blo 1209422 1211187 := bstep (se 1 (by rfl) ⟨908390, by rfl⟩ : syracuseStep 1211187 = 1816781) B1816781
theorem B1211203 : Blo 1209422 1211203 := bstep (se 1 (by rfl) ⟨908402, by rfl⟩ : syracuseStep 1211203 = 1816805) B1816805
theorem B1211219 : Blo 1209422 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B1211235 : Blo 1209422 1211235 := bstep (se 1 (by rfl) ⟨908426, by rfl⟩ : syracuseStep 1211235 = 1816853) B1816853
theorem B1211251 : Blo 1209422 1211251 := bstep (se 1 (by rfl) ⟨908438, by rfl⟩ : syracuseStep 1211251 = 1816877) B1816877
theorem B2907011 : Blo 1209422 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B1211267 : Blo 1209422 1211267 := bstep (se 1 (by rfl) ⟨908450, by rfl⟩ : syracuseStep 1211267 = 1816901) B1816901
theorem B1211283 : Blo 1209422 1211283 := bstep (se 1 (by rfl) ⟨908462, by rfl⟩ : syracuseStep 1211283 = 1816925) B1816925
theorem B1211299 : Blo 1209422 1211299 := bstep (se 1 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 1211299 = 1816949) B1816949
theorem B7756721 : Blo 1209422 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B1211315 : Blo 1209422 1211315 := bstep (se 1 (by rfl) ⟨908486, by rfl⟩ : syracuseStep 1211315 = 1816973) B1816973
theorem B1211331 : Blo 1209422 1211331 := bstep (se 1 (by rfl) ⟨908498, by rfl⟩ : syracuseStep 1211331 = 1816997) B1816997
theorem B2071507 : Blo 1209422 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B1211347 : Blo 1209422 1211347 := bstep (se 1 (by rfl) ⟨908510, by rfl⟩ : syracuseStep 1211347 = 1817021) B1817021
theorem B1211363 : Blo 1209422 1211363 := bstep (se 1 (by rfl) ⟨908522, by rfl⟩ : syracuseStep 1211363 = 1817045) B1817045
theorem B1211379 : Blo 1209422 1211379 := bstep (se 1 (by rfl) ⟨908534, by rfl⟩ : syracuseStep 1211379 = 1817069) B1817069
theorem B1211395 : Blo 1209422 1211395 := bstep (se 1 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 1211395 = 1817093) B1817093
theorem B1211411 : Blo 1209422 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B4594765 : Blo 1209422 4594765 := bstep (se 3 (by rfl) ⟨861518, by rfl⟩ : syracuseStep 4594765 = 1723037) B1723037
theorem B4365389 : Blo 1209422 4365389 := bstep (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) B1637021
theorem B11041933 : Blo 1209422 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B4086989 : Blo 1209422 4086989 := bstep (se 3 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 4086989 = 1532621) B1532621
theorem B1867009 : Blo 1209422 1867009 := bstep (se 2 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 1867009 = 1400257) B1400257
theorem B2907395 : Blo 1209422 2907395 := bstep (se 1 (by rfl) ⟨2180546, by rfl⟩ : syracuseStep 2907395 = 4361093) B4361093
theorem B4087043 : Blo 1209422 4087043 := bstep (se 1 (by rfl) ⟨3065282, by rfl⟩ : syracuseStep 4087043 = 6130565) B6130565
theorem B1965379 : Blo 1209422 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B1531219 : Blo 1209422 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B3063217 : Blo 1209422 3063217 := bstep (se 2 (by rfl) ⟨1148706, by rfl⟩ : syracuseStep 3063217 = 2297413) B2297413
theorem B1531315 : Blo 1209422 1531315 := bstep (se 1 (by rfl) ⟨1148486, by rfl⟩ : syracuseStep 1531315 = 2296973) B2296973
theorem B11034053 : Blo 1209422 11034053 := bstep (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) B2068885
theorem B3317201 : Blo 1209422 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B4087313 : Blo 1209422 4087313 := bstep (se 2 (by rfl) ⟨1532742, by rfl⟩ : syracuseStep 4087313 = 3065485) B3065485
theorem B5815907 : Blo 1209422 5815907 := bstep (se 1 (by rfl) ⟨4361930, by rfl⟩ : syracuseStep 5815907 = 8723861) B8723861
theorem B6897251 : Blo 1209422 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B3448433 : Blo 1209422 3448433 := bstep (se 2 (by rfl) ⟨1293162, by rfl⟩ : syracuseStep 3448433 = 2586325) B2586325
theorem B1474195 : Blo 1209422 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B3784369 : Blo 1209422 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B3063491 : Blo 1209422 3063491 := bstep (se 1 (by rfl) ⟨2297618, by rfl⟩ : syracuseStep 3063491 = 4595237) B4595237
theorem B7749361 : Blo 1209422 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B3104561 : Blo 1209422 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B1261363 : Blo 1209422 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B4595555 : Blo 1209422 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B3063683 : Blo 1209422 3063683 := bstep (se 1 (by rfl) ⟨2297762, by rfl⟩ : syracuseStep 3063683 = 4595525) B4595525
theorem B1531811 : Blo 1209422 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B10346561 : Blo 1209422 10346561 := bstep (se 2 (by rfl) ⟨3879960, by rfl⟩ : syracuseStep 10346561 = 7759921) B7759921
theorem B11042891 : Blo 1209422 11042891 := bstep (se 1 (by rfl) ⟨8282168, by rfl⟩ : syracuseStep 11042891 = 16564337) B16564337
theorem B5521553 : Blo 1209422 5521553 := bstep (se 2 (by rfl) ⟨2070582, by rfl⟩ : syracuseStep 5521553 = 4141165) B4141165
theorem B3064139 : Blo 1209422 3064139 := bstep (se 1 (by rfl) ⟨2298104, by rfl⟩ : syracuseStep 3064139 = 4596209) B4596209
theorem B11641265 : Blo 1209422 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B4088285 : Blo 1209422 4088285 := bstep (se 3 (by rfl) ⟨766553, by rfl⟩ : syracuseStep 4088285 = 1533107) B1533107
theorem B16556561 : Blo 1209422 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B3064513 : Blo 1209422 3064513 := bstep (se 2 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 3064513 = 2298385) B2298385
theorem B3449537 : Blo 1209422 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B1360651 : Blo 1209422 1360651 := bstep (se 1 (by rfl) ⟨1020488, by rfl⟩ : syracuseStep 1360651 = 2040977) B2040977
theorem B4596497 : Blo 1209422 4596497 := bstep (se 2 (by rfl) ⟨1723686, by rfl⟩ : syracuseStep 4596497 = 3447373) B3447373
theorem B6128459 : Blo 1209422 6128459 := bstep (se 1 (by rfl) ⟨4596344, by rfl⟩ : syracuseStep 6128459 = 9192689) B9192689
theorem B1360759 : Blo 1209422 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B27960241 : Blo 1209422 27960241 := bstep (se 2 (by rfl) ⟨10485090, by rfl⟩ : syracuseStep 27960241 = 20970181) B20970181
theorem B2761651 : Blo 1209422 2761651 := bstep (se 1 (by rfl) ⟨2071238, by rfl⟩ : syracuseStep 2761651 = 4142477) B4142477
theorem B1360939 : Blo 1209422 1360939 := bstep (se 1 (by rfl) ⟨1020704, by rfl⟩ : syracuseStep 1360939 = 2041409) B2041409
theorem B6538333 : Blo 1209422 6538333 := bstep (se 3 (by rfl) ⟨1225937, by rfl⟩ : syracuseStep 6538333 = 2451875) B2451875
theorem B1361047 : Blo 1209422 1361047 := bstep (se 1 (by rfl) ⟨1020785, by rfl⟩ : syracuseStep 1361047 = 2041571) B2041571
theorem B10339589 : Blo 1209422 10339589 := bstep (se 4 (by rfl) ⟨969336, by rfl⟩ : syracuseStep 10339589 = 1938673) B1938673
theorem B13092101 : Blo 1209422 13092101 := bstep (se 4 (by rfl) ⟨1227384, by rfl⟩ : syracuseStep 13092101 = 2454769) B2454769
theorem B3065111 : Blo 1209422 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B2762009 : Blo 1209422 2762009 := bstep (se 2 (by rfl) ⟨1035753, by rfl⟩ : syracuseStep 2762009 = 2071507) B2071507
theorem B1361227 : Blo 1209422 1361227 := bstep (se 1 (by rfl) ⟨1020920, by rfl⟩ : syracuseStep 1361227 = 2041841) B2041841
theorem B2721203 : Blo 1209422 2721203 := bstep (se 1 (by rfl) ⟨2040902, by rfl⟩ : syracuseStep 2721203 = 4081805) B4081805
theorem B1361335 : Blo 1209422 1361335 := bstep (se 1 (by rfl) ⟨1021001, by rfl⟩ : syracuseStep 1361335 = 2042003) B2042003
theorem B4597195 : Blo 1209422 4597195 := bstep (se 1 (by rfl) ⟨3447896, by rfl⟩ : syracuseStep 4597195 = 6895793) B6895793
theorem B2721239 : Blo 1209422 2721239 := bstep (se 1 (by rfl) ⟨2040929, by rfl⟩ : syracuseStep 2721239 = 4081859) B4081859
theorem B2041355 : Blo 1209422 2041355 := bstep (se 1 (by rfl) ⟨1531016, by rfl⟩ : syracuseStep 2041355 = 3062033) B3062033
theorem B14722577 : Blo 1209422 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B6891101 : Blo 1209422 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B1361515 : Blo 1209422 1361515 := bstep (se 1 (by rfl) ⟨1021136, by rfl⟩ : syracuseStep 1361515 = 2042273) B2042273
theorem B2721419 : Blo 1209422 2721419 := bstep (se 1 (by rfl) ⟨2041064, by rfl⟩ : syracuseStep 2721419 = 4082129) B4082129
theorem B2041483 : Blo 1209422 2041483 := bstep (se 1 (by rfl) ⟨1531112, by rfl⟩ : syracuseStep 2041483 = 3062225) B3062225
theorem B4359853 : Blo 1209422 4359853 := bstep (se 3 (by rfl) ⟨817472, by rfl⟩ : syracuseStep 4359853 = 1634945) B1634945
theorem B2721473 : Blo 1209422 2721473 := bstep (se 2 (by rfl) ⟨1020552, by rfl⟩ : syracuseStep 2721473 = 2041105) B2041105
theorem B8726221 : Blo 1209422 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B1361623 : Blo 1209422 1361623 := bstep (se 1 (by rfl) ⟨1021217, by rfl⟩ : syracuseStep 1361623 = 2042435) B2042435
theorem B6899417 : Blo 1209422 6899417 := bstep (se 2 (by rfl) ⟨2587281, by rfl⟩ : syracuseStep 6899417 = 5174563) B5174563
theorem B4597469 : Blo 1209422 4597469 := bstep (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) B1724051
theorem B2041625 : Blo 1209422 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B1361803 : Blo 1209422 1361803 := bstep (se 1 (by rfl) ⟨1021352, by rfl⟩ : syracuseStep 1361803 = 2042705) B2042705
theorem B2721689 : Blo 1209422 2721689 := bstep (se 2 (by rfl) ⟨1020633, by rfl⟩ : syracuseStep 2721689 = 2041267) B2041267
theorem B2041753 : Blo 1209422 2041753 := bstep (se 2 (by rfl) ⟨765657, by rfl⟩ : syracuseStep 2041753 = 1531315) B1531315
theorem B5171147 : Blo 1209422 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B2721779 : Blo 1209422 2721779 := bstep (se 1 (by rfl) ⟨2041334, by rfl⟩ : syracuseStep 2721779 = 4082669) B4082669
theorem B1361911 : Blo 1209422 1361911 := bstep (se 1 (by rfl) ⟨1021433, by rfl⟩ : syracuseStep 1361911 = 2042867) B2042867
theorem B2721815 : Blo 1209422 2721815 := bstep (se 1 (by rfl) ⟨2041361, by rfl⟩ : syracuseStep 2721815 = 4082723) B4082723
theorem B2910259 : Blo 1209422 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B3065921 : Blo 1209422 3065921 := bstep (se 2 (by rfl) ⟨1149720, by rfl⟩ : syracuseStep 3065921 = 2299441) B2299441
theorem B1362091 : Blo 1209422 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B2721995 : Blo 1209422 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B6547673 : Blo 1209422 6547673 := bstep (se 2 (by rfl) ⟨2455377, by rfl⟩ : syracuseStep 6547673 = 4910755) B4910755
theorem B2722049 : Blo 1209422 2722049 := bstep (se 2 (by rfl) ⟨1020768, by rfl⟩ : syracuseStep 2722049 = 2041537) B2041537
theorem B1362199 : Blo 1209422 1362199 := bstep (se 1 (by rfl) ⟨1021649, by rfl⟩ : syracuseStep 1362199 = 2043299) B2043299
theorem B10332481 : Blo 1209422 10332481 := bstep (se 2 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 10332481 = 7749361) B7749361
theorem B3877271 : Blo 1209422 3877271 := bstep (se 1 (by rfl) ⟨2907953, by rfl⟩ : syracuseStep 3877271 = 5815907) B5815907
theorem B4598167 : Blo 1209422 4598167 := bstep (se 1 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 4598167 = 6897251) B6897251
theorem B1681817 : Blo 1209422 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1362379 : Blo 1209422 1362379 := bstep (se 1 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 1362379 = 2043569) B2043569
theorem B2042327 : Blo 1209422 2042327 := bstep (se 1 (by rfl) ⟨1531745, by rfl⟩ : syracuseStep 2042327 = 3063491) B3063491
theorem B2722265 : Blo 1209422 2722265 := bstep (se 2 (by rfl) ⟨1020849, by rfl⟩ : syracuseStep 2722265 = 2041699) B2041699
theorem B2296343 : Blo 1209422 2296343 := bstep (se 1 (by rfl) ⟨1722257, by rfl⟩ : syracuseStep 2296343 = 3444515) B3444515
theorem B2722355 : Blo 1209422 2722355 := bstep (se 1 (by rfl) ⟨2041766, by rfl⟩ : syracuseStep 2722355 = 4083533) B4083533
theorem B1362487 : Blo 1209422 1362487 := bstep (se 1 (by rfl) ⟨1021865, by rfl⟩ : syracuseStep 1362487 = 2043731) B2043731
theorem B6130241 : Blo 1209422 6130241 := bstep (se 2 (by rfl) ⟨2298840, by rfl⟩ : syracuseStep 6130241 = 4597681) B4597681
theorem B2722391 : Blo 1209422 2722391 := bstep (se 1 (by rfl) ⟨2041793, by rfl⟩ : syracuseStep 2722391 = 4083587) B4083587
theorem B2042455 : Blo 1209422 2042455 := bstep (se 1 (by rfl) ⟨1531841, by rfl⟩ : syracuseStep 2042455 = 3063683) B3063683
theorem B9185885 : Blo 1209422 9185885 := bstep (se 3 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 9185885 = 3444707) B3444707
theorem B2583257 : Blo 1209422 2583257 := bstep (se 2 (by rfl) ⟨968721, by rfl⟩ : syracuseStep 2583257 = 1937443) B1937443
theorem B1362667 : Blo 1209422 1362667 := bstep (se 1 (by rfl) ⟨1022000, by rfl⟩ : syracuseStep 1362667 = 2044001) B2044001
theorem B2722571 : Blo 1209422 2722571 := bstep (se 1 (by rfl) ⟨2041928, by rfl⟩ : syracuseStep 2722571 = 4083857) B4083857
theorem B2722625 : Blo 1209422 2722625 := bstep (se 2 (by rfl) ⟨1020984, by rfl⟩ : syracuseStep 2722625 = 2041969) B2041969
theorem B4082507 : Blo 1209422 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B1362775 : Blo 1209422 1362775 := bstep (se 1 (by rfl) ⟨1022081, by rfl⟩ : syracuseStep 1362775 = 2044163) B2044163
theorem B2796439 : Blo 1209422 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B5172119 : Blo 1209422 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B1723351 : Blo 1209422 1723351 := bstep (se 1 (by rfl) ⟨1292513, by rfl⟩ : syracuseStep 1723351 = 2585027) B2585027
theorem B68111381 : Blo 1209422 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B2722841 : Blo 1209422 2722841 := bstep (se 2 (by rfl) ⟨1021065, by rfl⟩ : syracuseStep 2722841 = 2042131) B2042131
theorem B20671523 : Blo 1209422 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B4082777 : Blo 1209422 4082777 := bstep (se 2 (by rfl) ⟨1531041, by rfl⟩ : syracuseStep 4082777 = 3062083) B3062083
theorem B7359589 : Blo 1209422 7359589 := bstep (se 4 (by rfl) ⟨689961, by rfl⟩ : syracuseStep 7359589 = 1379923) B1379923
theorem B2583667 : Blo 1209422 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B2722931 : Blo 1209422 2722931 := bstep (se 1 (by rfl) ⟨2042198, by rfl⟩ : syracuseStep 2722931 = 4084397) B4084397
theorem B2722967 : Blo 1209422 2722967 := bstep (se 1 (by rfl) ⟨2042225, by rfl⟩ : syracuseStep 2722967 = 4084451) B4084451
theorem B4598957 : Blo 1209422 4598957 := bstep (se 3 (by rfl) ⟨862304, by rfl⟩ : syracuseStep 4598957 = 1724609) B1724609
theorem B2297011 : Blo 1209422 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B3271859 : Blo 1209422 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B2043083 : Blo 1209422 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B3493081 : Blo 1209422 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B9817361 : Blo 1209422 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B2723147 : Blo 1209422 2723147 := bstep (se 1 (by rfl) ⟨2042360, by rfl⟩ : syracuseStep 2723147 = 4084721) B4084721
theorem B3878219 : Blo 1209422 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B2043211 : Blo 1209422 2043211 := bstep (se 1 (by rfl) ⟨1532408, by rfl⟩ : syracuseStep 2043211 = 3064817) B3064817
theorem B7761253 : Blo 1209422 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B2723201 : Blo 1209422 2723201 := bstep (se 2 (by rfl) ⟨1021200, by rfl⟩ : syracuseStep 2723201 = 2042401) B2042401
theorem B2584001 : Blo 1209422 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B2043353 : Blo 1209422 2043353 := bstep (se 2 (by rfl) ⟨766257, by rfl⟩ : syracuseStep 2043353 = 1532515) B1532515
theorem B3444275 : Blo 1209422 3444275 := bstep (se 1 (by rfl) ⟨2583206, by rfl⟩ : syracuseStep 3444275 = 5166413) B5166413
theorem B2723417 : Blo 1209422 2723417 := bstep (se 2 (by rfl) ⟨1021281, by rfl⟩ : syracuseStep 2723417 = 2042563) B2042563
theorem B2043481 : Blo 1209422 2043481 := bstep (se 2 (by rfl) ⟨766305, by rfl⟩ : syracuseStep 2043481 = 1532611) B1532611
theorem B2297459 : Blo 1209422 2297459 := bstep (se 1 (by rfl) ⟨1723094, by rfl⟩ : syracuseStep 2297459 = 3446189) B3446189
theorem B2297497 : Blo 1209422 2297497 := bstep (se 2 (by rfl) ⟨861561, by rfl⟩ : syracuseStep 2297497 = 1723123) B1723123
theorem B2723507 : Blo 1209422 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B1814219 : Blo 1209422 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B1814231 : Blo 1209422 1814231 := bstep (se 1 (by rfl) ⟨1360673, by rfl⟩ : syracuseStep 1814231 = 2721347) B2721347
theorem B2723543 : Blo 1209422 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B4083479 : Blo 1209422 4083479 := bstep (se 1 (by rfl) ⟨3062609, by rfl⟩ : syracuseStep 4083479 = 6125219) B6125219
theorem B1814297 : Blo 1209422 1814297 := bstep (se 2 (by rfl) ⟨680361, by rfl⟩ : syracuseStep 1814297 = 1360723) B1360723
theorem B2182963 : Blo 1209422 2182963 := bstep (se 1 (by rfl) ⟨1637222, by rfl⟩ : syracuseStep 2182963 = 3274445) B3274445
theorem B16568165 : Blo 1209422 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B1814411 : Blo 1209422 1814411 := bstep (se 1 (by rfl) ⟨1360808, by rfl⟩ : syracuseStep 1814411 = 2721617) B2721617
theorem B2723723 : Blo 1209422 2723723 := bstep (se 1 (by rfl) ⟨2042792, by rfl⟩ : syracuseStep 2723723 = 4085585) B4085585
theorem B1814423 : Blo 1209422 1814423 := bstep (se 1 (by rfl) ⟨1360817, by rfl⟩ : syracuseStep 1814423 = 2721635) B2721635
theorem B2723777 : Blo 1209422 2723777 := bstep (se 2 (by rfl) ⟨1021416, by rfl⟩ : syracuseStep 2723777 = 2042833) B2042833
theorem B1814489 : Blo 1209422 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B3878873 : Blo 1209422 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B22073357 : Blo 1209422 22073357 := bstep (se 3 (by rfl) ⟨4138754, by rfl⟩ : syracuseStep 22073357 = 8277509) B8277509
theorem B6893585 : Blo 1209422 6893585 := bstep (se 2 (by rfl) ⟨2585094, by rfl⟩ : syracuseStep 6893585 = 5170189) B5170189
theorem B1814603 : Blo 1209422 1814603 := bstep (se 1 (by rfl) ⟨1360952, by rfl⟩ : syracuseStep 1814603 = 2721905) B2721905
theorem B8720459 : Blo 1209422 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B1937495 : Blo 1209422 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B1814615 : Blo 1209422 1814615 := bstep (se 1 (by rfl) ⟨1360961, by rfl⟩ : syracuseStep 1814615 = 2721923) B2721923
theorem B2297945 : Blo 1209422 2297945 := bstep (se 2 (by rfl) ⟨861729, by rfl⟩ : syracuseStep 2297945 = 1723459) B1723459
theorem B2584727 : Blo 1209422 2584727 := bstep (se 1 (by rfl) ⟨1938545, by rfl⟩ : syracuseStep 2584727 = 3877091) B3877091
theorem B2044055 : Blo 1209422 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B1814681 : Blo 1209422 1814681 := bstep (se 2 (by rfl) ⟨680505, by rfl⟩ : syracuseStep 1814681 = 1361011) B1361011
theorem B2723993 : Blo 1209422 2723993 := bstep (se 2 (by rfl) ⟨1021497, by rfl⟩ : syracuseStep 2723993 = 2042995) B2042995
theorem B31436981 : Blo 1209422 31436981 := bstep (se 5 (by rfl) ⟨1473608, by rfl⟩ : syracuseStep 31436981 = 2947217) B2947217
theorem B1937623 : Blo 1209422 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B2724083 : Blo 1209422 2724083 := bstep (se 1 (by rfl) ⟨2043062, by rfl⟩ : syracuseStep 2724083 = 4086125) B4086125
theorem B1814795 : Blo 1209422 1814795 := bstep (se 1 (by rfl) ⟨1361096, by rfl⟩ : syracuseStep 1814795 = 2722193) B2722193
theorem B1814807 : Blo 1209422 1814807 := bstep (se 1 (by rfl) ⟨1361105, by rfl⟩ : syracuseStep 1814807 = 2722211) B2722211
theorem B2724119 : Blo 1209422 2724119 := bstep (se 1 (by rfl) ⟨2043089, by rfl⟩ : syracuseStep 2724119 = 4086179) B4086179
theorem B2044183 : Blo 1209422 2044183 := bstep (se 1 (by rfl) ⟨1533137, by rfl⟩ : syracuseStep 2044183 = 3066275) B3066275
theorem B15520045 : Blo 1209422 15520045 := bstep (se 3 (by rfl) ⟨2910008, by rfl⟩ : syracuseStep 15520045 = 5820017) B5820017
theorem B4084019 : Blo 1209422 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B1814873 : Blo 1209422 1814873 := bstep (se 2 (by rfl) ⟨680577, by rfl⟩ : syracuseStep 1814873 = 1361155) B1361155
theorem B1814987 : Blo 1209422 1814987 := bstep (se 1 (by rfl) ⟨1361240, by rfl⟩ : syracuseStep 1814987 = 2722481) B2722481
theorem B2724299 : Blo 1209422 2724299 := bstep (se 1 (by rfl) ⟨2043224, by rfl⟩ : syracuseStep 2724299 = 4086449) B4086449
theorem B1814999 : Blo 1209422 1814999 := bstep (se 1 (by rfl) ⟨1361249, by rfl⟩ : syracuseStep 1814999 = 2722499) B2722499
theorem B6132185 : Blo 1209422 6132185 := bstep (se 2 (by rfl) ⟨2299569, by rfl⟩ : syracuseStep 6132185 = 4599139) B4599139
theorem B2724353 : Blo 1209422 2724353 := bstep (se 2 (by rfl) ⟨1021632, by rfl⟩ : syracuseStep 2724353 = 2043265) B2043265
theorem B1815065 : Blo 1209422 1815065 := bstep (se 2 (by rfl) ⟨680649, by rfl⟩ : syracuseStep 1815065 = 1361299) B1361299
theorem B4084289 : Blo 1209422 4084289 := bstep (se 2 (by rfl) ⟨1531608, by rfl⟩ : syracuseStep 4084289 = 3063217) B3063217
theorem B1938007 : Blo 1209422 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B1815179 : Blo 1209422 1815179 := bstep (se 1 (by rfl) ⟨1361384, by rfl⟩ : syracuseStep 1815179 = 2722769) B2722769
theorem B1815191 : Blo 1209422 1815191 := bstep (se 1 (by rfl) ⟨1361393, by rfl⟩ : syracuseStep 1815191 = 2722787) B2722787
theorem B4592321 : Blo 1209422 4592321 := bstep (se 2 (by rfl) ⟨1722120, by rfl⟩ : syracuseStep 4592321 = 3444241) B3444241
theorem B1815257 : Blo 1209422 1815257 := bstep (se 2 (by rfl) ⟨680721, by rfl⟩ : syracuseStep 1815257 = 1361443) B1361443
theorem B2724569 : Blo 1209422 2724569 := bstep (se 2 (by rfl) ⟨1021713, by rfl⟩ : syracuseStep 2724569 = 2043427) B2043427
theorem B10343213 : Blo 1209422 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B2724659 : Blo 1209422 2724659 := bstep (se 1 (by rfl) ⟨2043494, by rfl⟩ : syracuseStep 2724659 = 4086989) B4086989
theorem B3879731 : Blo 1209422 3879731 := bstep (se 1 (by rfl) ⟨2909798, by rfl⟩ : syracuseStep 3879731 = 5819597) B5819597
theorem B2298689 : Blo 1209422 2298689 := bstep (se 2 (by rfl) ⟨862008, by rfl⟩ : syracuseStep 2298689 = 1724017) B1724017
theorem B1815371 : Blo 1209422 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B1938263 : Blo 1209422 1938263 := bstep (se 1 (by rfl) ⟨1453697, by rfl⟩ : syracuseStep 1938263 = 2907395) B2907395
theorem B1815383 : Blo 1209422 1815383 := bstep (se 1 (by rfl) ⟨1361537, by rfl⟩ : syracuseStep 1815383 = 2723075) B2723075
theorem B2724695 : Blo 1209422 2724695 := bstep (se 1 (by rfl) ⟨2043521, by rfl⟩ : syracuseStep 2724695 = 4087043) B4087043
theorem B1815449 : Blo 1209422 1815449 := bstep (se 2 (by rfl) ⟨680793, by rfl⟩ : syracuseStep 1815449 = 1361587) B1361587
theorem B3879859 : Blo 1209422 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B1815563 : Blo 1209422 1815563 := bstep (se 1 (by rfl) ⟨1361672, by rfl⟩ : syracuseStep 1815563 = 2723345) B2723345
theorem B2724875 : Blo 1209422 2724875 := bstep (se 1 (by rfl) ⟨2043656, by rfl⟩ : syracuseStep 2724875 = 4087313) B4087313
theorem B1815575 : Blo 1209422 1815575 := bstep (se 1 (by rfl) ⟨1361681, by rfl⟩ : syracuseStep 1815575 = 2723363) B2723363
theorem B2724929 : Blo 1209422 2724929 := bstep (se 2 (by rfl) ⟨1021848, by rfl⟩ : syracuseStep 2724929 = 2043697) B2043697
theorem B3880001 : Blo 1209422 3880001 := bstep (se 2 (by rfl) ⟨1455000, by rfl⟩ : syracuseStep 3880001 = 2910001) B2910001
theorem B2298955 : Blo 1209422 2298955 := bstep (se 1 (by rfl) ⟨1724216, by rfl⟩ : syracuseStep 2298955 = 3448433) B3448433
theorem B1209431 : Blo 1209422 1209431 := bstep (se 1 (by rfl) ⟨907073, by rfl⟩ : syracuseStep 1209431 = 1814147) B1814147
theorem B1815641 : Blo 1209422 1815641 := bstep (se 2 (by rfl) ⟨680865, by rfl⟩ : syracuseStep 1815641 = 1361731) B1361731
theorem B5166173 : Blo 1209422 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B4084829 : Blo 1209422 4084829 := bstep (se 3 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 4084829 = 1531811) B1531811
theorem B1209451 : Blo 1209422 1209451 := bstep (se 1 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 1209451 = 1814177) B1814177
theorem B1209463 : Blo 1209422 1209463 := bstep (se 1 (by rfl) ⟨907097, by rfl⟩ : syracuseStep 1209463 = 1814195) B1814195
theorem B1209483 : Blo 1209422 1209483 := bstep (se 1 (by rfl) ⟨907112, by rfl⟩ : syracuseStep 1209483 = 1814225) B1814225
theorem B1209495 : Blo 1209422 1209495 := bstep (se 1 (by rfl) ⟨907121, by rfl⟩ : syracuseStep 1209495 = 1814243) B1814243
theorem B1209515 : Blo 1209422 1209515 := bstep (se 1 (by rfl) ⟨907136, by rfl⟩ : syracuseStep 1209515 = 1814273) B1814273
theorem B23262389 : Blo 1209422 23262389 := bstep (se 5 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 23262389 = 2180849) B2180849
theorem B1209527 : Blo 1209422 1209527 := bstep (se 1 (by rfl) ⟨907145, by rfl⟩ : syracuseStep 1209527 = 1814291) B1814291
theorem B3880115 : Blo 1209422 3880115 := bstep (se 1 (by rfl) ⟨2910086, by rfl⟩ : syracuseStep 3880115 = 5820173) B5820173
theorem B1209547 : Blo 1209422 1209547 := bstep (se 1 (by rfl) ⟨907160, by rfl⟩ : syracuseStep 1209547 = 1814321) B1814321
theorem B2069707 : Blo 1209422 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B1815755 : Blo 1209422 1815755 := bstep (se 1 (by rfl) ⟨1361816, by rfl⟩ : syracuseStep 1815755 = 2723633) B2723633
theorem B1209559 : Blo 1209422 1209559 := bstep (se 1 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 1209559 = 1814339) B1814339
theorem B1815767 : Blo 1209422 1815767 := bstep (se 1 (by rfl) ⟨1361825, by rfl⟩ : syracuseStep 1815767 = 2723651) B2723651
theorem B1209579 : Blo 1209422 1209579 := bstep (se 1 (by rfl) ⟨907184, by rfl⟩ : syracuseStep 1209579 = 1814369) B1814369
theorem B1209591 : Blo 1209422 1209591 := bstep (se 1 (by rfl) ⟨907193, by rfl⟩ : syracuseStep 1209591 = 1814387) B1814387
theorem B1209611 : Blo 1209422 1209611 := bstep (se 1 (by rfl) ⟨907208, by rfl⟩ : syracuseStep 1209611 = 1814417) B1814417
theorem B1209623 : Blo 1209422 1209623 := bstep (se 1 (by rfl) ⟨907217, by rfl⟩ : syracuseStep 1209623 = 1814435) B1814435
theorem B1815833 : Blo 1209422 1815833 := bstep (se 2 (by rfl) ⟨680937, by rfl⟩ : syracuseStep 1815833 = 1361875) B1361875
theorem B2725145 : Blo 1209422 2725145 := bstep (se 2 (by rfl) ⟨1021929, by rfl⟩ : syracuseStep 2725145 = 2043859) B2043859
theorem B1209643 : Blo 1209422 1209643 := bstep (se 1 (by rfl) ⟨907232, by rfl⟩ : syracuseStep 1209643 = 1814465) B1814465
theorem B1209655 : Blo 1209422 1209655 := bstep (se 1 (by rfl) ⟨907241, by rfl⟩ : syracuseStep 1209655 = 1814483) B1814483
theorem B1209675 : Blo 1209422 1209675 := bstep (se 1 (by rfl) ⟨907256, by rfl⟩ : syracuseStep 1209675 = 1814513) B1814513
theorem B1209687 : Blo 1209422 1209687 := bstep (se 1 (by rfl) ⟨907265, by rfl⟩ : syracuseStep 1209687 = 1814531) B1814531
theorem B1209707 : Blo 1209422 1209707 := bstep (se 1 (by rfl) ⟨907280, by rfl⟩ : syracuseStep 1209707 = 1814561) B1814561
theorem B2725235 : Blo 1209422 2725235 := bstep (se 1 (by rfl) ⟨2043926, by rfl⟩ : syracuseStep 2725235 = 4087853) B4087853
theorem B1209719 : Blo 1209422 1209719 := bstep (se 1 (by rfl) ⟨907289, by rfl⟩ : syracuseStep 1209719 = 1814579) B1814579
theorem B1209739 : Blo 1209422 1209739 := bstep (se 1 (by rfl) ⟨907304, by rfl⟩ : syracuseStep 1209739 = 1814609) B1814609
theorem B1938827 : Blo 1209422 1938827 := bstep (se 1 (by rfl) ⟨1454120, by rfl⟩ : syracuseStep 1938827 = 2908241) B2908241
theorem B1815947 : Blo 1209422 1815947 := bstep (se 1 (by rfl) ⟨1361960, by rfl⟩ : syracuseStep 1815947 = 2723921) B2723921
theorem B1209751 : Blo 1209422 1209751 := bstep (se 1 (by rfl) ⟨907313, by rfl⟩ : syracuseStep 1209751 = 1814627) B1814627
theorem B1815959 : Blo 1209422 1815959 := bstep (se 1 (by rfl) ⟨1361969, by rfl⟩ : syracuseStep 1815959 = 2723939) B2723939
theorem B2725271 : Blo 1209422 2725271 := bstep (se 1 (by rfl) ⟨2043953, by rfl⟩ : syracuseStep 2725271 = 4087907) B4087907
theorem B1209771 : Blo 1209422 1209771 := bstep (se 1 (by rfl) ⟨907328, by rfl⟩ : syracuseStep 1209771 = 1814657) B1814657
theorem B1209783 : Blo 1209422 1209783 := bstep (se 1 (by rfl) ⟨907337, by rfl⟩ : syracuseStep 1209783 = 1814675) B1814675
theorem B1209803 : Blo 1209422 1209803 := bstep (se 1 (by rfl) ⟨907352, by rfl⟩ : syracuseStep 1209803 = 1814705) B1814705
theorem B1209815 : Blo 1209422 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B1816025 : Blo 1209422 1816025 := bstep (se 2 (by rfl) ⟨681009, by rfl⟩ : syracuseStep 1816025 = 1362019) B1362019
theorem B1209835 : Blo 1209422 1209835 := bstep (se 1 (by rfl) ⟨907376, by rfl⟩ : syracuseStep 1209835 = 1814753) B1814753
theorem B1209847 : Blo 1209422 1209847 := bstep (se 1 (by rfl) ⟨907385, by rfl⟩ : syracuseStep 1209847 = 1814771) B1814771
theorem B1209867 : Blo 1209422 1209867 := bstep (se 1 (by rfl) ⟨907400, by rfl⟩ : syracuseStep 1209867 = 1814801) B1814801
theorem B2299403 : Blo 1209422 2299403 := bstep (se 1 (by rfl) ⟨1724552, by rfl⟩ : syracuseStep 2299403 = 3449105) B3449105
theorem B1209879 : Blo 1209422 1209879 := bstep (se 1 (by rfl) ⟨907409, by rfl⟩ : syracuseStep 1209879 = 1814819) B1814819
theorem B1209899 : Blo 1209422 1209899 := bstep (se 1 (by rfl) ⟨907424, by rfl⟩ : syracuseStep 1209899 = 1814849) B1814849
theorem B1209911 : Blo 1209422 1209911 := bstep (se 1 (by rfl) ⟨907433, by rfl⟩ : syracuseStep 1209911 = 1814867) B1814867
theorem B1209931 : Blo 1209422 1209931 := bstep (se 1 (by rfl) ⟨907448, by rfl⟩ : syracuseStep 1209931 = 1814897) B1814897
theorem B1816139 : Blo 1209422 1816139 := bstep (se 1 (by rfl) ⟨1362104, by rfl⟩ : syracuseStep 1816139 = 2724209) B2724209
theorem B2725451 : Blo 1209422 2725451 := bstep (se 1 (by rfl) ⟨2044088, by rfl⟩ : syracuseStep 2725451 = 4088177) B4088177
theorem B1209943 : Blo 1209422 1209943 := bstep (se 1 (by rfl) ⟨907457, by rfl⟩ : syracuseStep 1209943 = 1814915) B1814915
theorem B1816151 : Blo 1209422 1816151 := bstep (se 1 (by rfl) ⟨1362113, by rfl⟩ : syracuseStep 1816151 = 2724227) B2724227
theorem B1209963 : Blo 1209422 1209963 := bstep (se 1 (by rfl) ⟨907472, by rfl⟩ : syracuseStep 1209963 = 1814945) B1814945
theorem B1209975 : Blo 1209422 1209975 := bstep (se 1 (by rfl) ⟨907481, by rfl⟩ : syracuseStep 1209975 = 1814963) B1814963
theorem B2725505 : Blo 1209422 2725505 := bstep (se 2 (by rfl) ⟨1022064, by rfl⟩ : syracuseStep 2725505 = 2044129) B2044129
theorem B9942659 : Blo 1209422 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B1209995 : Blo 1209422 1209995 := bstep (se 1 (by rfl) ⟨907496, by rfl⟩ : syracuseStep 1209995 = 1814993) B1814993
theorem B1210007 : Blo 1209422 1210007 := bstep (se 1 (by rfl) ⟨907505, by rfl⟩ : syracuseStep 1210007 = 1815011) B1815011
theorem B1816217 : Blo 1209422 1816217 := bstep (se 2 (by rfl) ⟨681081, by rfl⟩ : syracuseStep 1816217 = 1362163) B1362163
theorem B1210027 : Blo 1209422 1210027 := bstep (se 1 (by rfl) ⟨907520, by rfl⟩ : syracuseStep 1210027 = 1815041) B1815041
theorem B1210039 : Blo 1209422 1210039 := bstep (se 1 (by rfl) ⟨907529, by rfl⟩ : syracuseStep 1210039 = 1815059) B1815059
theorem B2299585 : Blo 1209422 2299585 := bstep (se 2 (by rfl) ⟨862344, by rfl⟩ : syracuseStep 2299585 = 1724689) B1724689
theorem B1210059 : Blo 1209422 1210059 := bstep (se 1 (by rfl) ⟨907544, by rfl⟩ : syracuseStep 1210059 = 1815089) B1815089
theorem B1210071 : Blo 1209422 1210071 := bstep (se 1 (by rfl) ⟨907553, by rfl⟩ : syracuseStep 1210071 = 1815107) B1815107
theorem B1210091 : Blo 1209422 1210091 := bstep (se 1 (by rfl) ⟨907568, by rfl⟩ : syracuseStep 1210091 = 1815137) B1815137
theorem B2758387 : Blo 1209422 2758387 := bstep (se 1 (by rfl) ⟨2068790, by rfl⟩ : syracuseStep 2758387 = 4137581) B4137581
theorem B1210103 : Blo 1209422 1210103 := bstep (se 1 (by rfl) ⟨907577, by rfl⟩ : syracuseStep 1210103 = 1815155) B1815155
theorem B4904707 : Blo 1209422 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B1210123 : Blo 1209422 1210123 := bstep (se 1 (by rfl) ⟨907592, by rfl⟩ : syracuseStep 1210123 = 1815185) B1815185
theorem B1816331 : Blo 1209422 1816331 := bstep (se 1 (by rfl) ⟨1362248, by rfl⟩ : syracuseStep 1816331 = 2724497) B2724497
theorem B1210135 : Blo 1209422 1210135 := bstep (se 1 (by rfl) ⟨907601, by rfl⟩ : syracuseStep 1210135 = 1815203) B1815203
theorem B1816343 : Blo 1209422 1816343 := bstep (se 1 (by rfl) ⟨1362257, by rfl⟩ : syracuseStep 1816343 = 2724515) B2724515
theorem B1210155 : Blo 1209422 1210155 := bstep (se 1 (by rfl) ⟨907616, by rfl⟩ : syracuseStep 1210155 = 1815233) B1815233
theorem B1210167 : Blo 1209422 1210167 := bstep (se 1 (by rfl) ⟨907625, by rfl⟩ : syracuseStep 1210167 = 1815251) B1815251
theorem B1210187 : Blo 1209422 1210187 := bstep (se 1 (by rfl) ⟨907640, by rfl⟩ : syracuseStep 1210187 = 1815281) B1815281
theorem B1210199 : Blo 1209422 1210199 := bstep (se 1 (by rfl) ⟨907649, by rfl⟩ : syracuseStep 1210199 = 1815299) B1815299
theorem B1816409 : Blo 1209422 1816409 := bstep (se 2 (by rfl) ⟨681153, by rfl⟩ : syracuseStep 1816409 = 1362307) B1362307
theorem B3446621 : Blo 1209422 3446621 := bstep (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) B1292483
theorem B1210219 : Blo 1209422 1210219 := bstep (se 1 (by rfl) ⟨907664, by rfl⟩ : syracuseStep 1210219 = 1815329) B1815329
theorem B1210231 : Blo 1209422 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B1210251 : Blo 1209422 1210251 := bstep (se 1 (by rfl) ⟨907688, by rfl⟩ : syracuseStep 1210251 = 1815377) B1815377
theorem B1210263 : Blo 1209422 1210263 := bstep (se 1 (by rfl) ⟨907697, by rfl⟩ : syracuseStep 1210263 = 1815395) B1815395
theorem B1210283 : Blo 1209422 1210283 := bstep (se 1 (by rfl) ⟨907712, by rfl⟩ : syracuseStep 1210283 = 1815425) B1815425
theorem B4593581 : Blo 1209422 4593581 := bstep (se 3 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 4593581 = 1722593) B1722593
theorem B1210295 : Blo 1209422 1210295 := bstep (se 1 (by rfl) ⟨907721, by rfl⟩ : syracuseStep 1210295 = 1815443) B1815443
theorem B4593611 : Blo 1209422 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B1210315 : Blo 1209422 1210315 := bstep (se 1 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 1210315 = 1815473) B1815473
theorem B1816523 : Blo 1209422 1816523 := bstep (se 1 (by rfl) ⟨1362392, by rfl⟩ : syracuseStep 1816523 = 2724785) B2724785
theorem B1210327 : Blo 1209422 1210327 := bstep (se 1 (by rfl) ⟨907745, by rfl⟩ : syracuseStep 1210327 = 1815491) B1815491
theorem B1816535 : Blo 1209422 1816535 := bstep (se 1 (by rfl) ⟨1362401, by rfl⟩ : syracuseStep 1816535 = 2724803) B2724803
theorem B1210347 : Blo 1209422 1210347 := bstep (se 1 (by rfl) ⟨907760, by rfl⟩ : syracuseStep 1210347 = 1815521) B1815521
theorem B1210359 : Blo 1209422 1210359 := bstep (se 1 (by rfl) ⟨907769, by rfl⟩ : syracuseStep 1210359 = 1815539) B1815539
theorem B1210379 : Blo 1209422 1210379 := bstep (se 1 (by rfl) ⟨907784, by rfl⟩ : syracuseStep 1210379 = 1815569) B1815569
theorem B2758679 : Blo 1209422 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B1210391 : Blo 1209422 1210391 := bstep (se 1 (by rfl) ⟨907793, by rfl⟩ : syracuseStep 1210391 = 1815587) B1815587
theorem B1816601 : Blo 1209422 1816601 := bstep (se 2 (by rfl) ⟨681225, by rfl⟩ : syracuseStep 1816601 = 1362451) B1362451
theorem B1210411 : Blo 1209422 1210411 := bstep (se 1 (by rfl) ⟨907808, by rfl⟩ : syracuseStep 1210411 = 1815617) B1815617
theorem B7755821 : Blo 1209422 7755821 := bstep (se 3 (by rfl) ⟨1454216, by rfl⟩ : syracuseStep 7755821 = 2908433) B2908433
theorem B1210423 : Blo 1209422 1210423 := bstep (se 1 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 1210423 = 1815635) B1815635
theorem B3446849 : Blo 1209422 3446849 := bstep (se 2 (by rfl) ⟨1292568, by rfl⟩ : syracuseStep 3446849 = 2585137) B2585137
theorem B1210443 : Blo 1209422 1210443 := bstep (se 1 (by rfl) ⟨907832, by rfl⟩ : syracuseStep 1210443 = 1815665) B1815665
theorem B1210455 : Blo 1209422 1210455 := bstep (se 1 (by rfl) ⟨907841, by rfl⟩ : syracuseStep 1210455 = 1815683) B1815683
theorem B1210475 : Blo 1209422 1210475 := bstep (se 1 (by rfl) ⟨907856, by rfl⟩ : syracuseStep 1210475 = 1815713) B1815713
theorem B1210487 : Blo 1209422 1210487 := bstep (se 1 (by rfl) ⟨907865, by rfl⟩ : syracuseStep 1210487 = 1815731) B1815731
theorem B1210507 : Blo 1209422 1210507 := bstep (se 1 (by rfl) ⟨907880, by rfl⟩ : syracuseStep 1210507 = 1815761) B1815761
theorem B1816715 : Blo 1209422 1816715 := bstep (se 1 (by rfl) ⟨1362536, by rfl⟩ : syracuseStep 1816715 = 2725073) B2725073
theorem B1210519 : Blo 1209422 1210519 := bstep (se 1 (by rfl) ⟨907889, by rfl⟩ : syracuseStep 1210519 = 1815779) B1815779
theorem B1816727 : Blo 1209422 1816727 := bstep (se 1 (by rfl) ⟨1362545, by rfl⟩ : syracuseStep 1816727 = 2725091) B2725091
theorem B1210539 : Blo 1209422 1210539 := bstep (se 1 (by rfl) ⟨907904, by rfl⟩ : syracuseStep 1210539 = 1815809) B1815809
theorem B1210551 : Blo 1209422 1210551 := bstep (se 1 (by rfl) ⟨907913, by rfl⟩ : syracuseStep 1210551 = 1815827) B1815827
theorem B1210571 : Blo 1209422 1210571 := bstep (se 1 (by rfl) ⟨907928, by rfl⟩ : syracuseStep 1210571 = 1815857) B1815857
theorem B4085963 : Blo 1209422 4085963 := bstep (se 1 (by rfl) ⟨3064472, by rfl⟩ : syracuseStep 4085963 = 6128945) B6128945
theorem B1210583 : Blo 1209422 1210583 := bstep (se 1 (by rfl) ⟨907937, by rfl⟩ : syracuseStep 1210583 = 1815875) B1815875
theorem B1939673 : Blo 1209422 1939673 := bstep (se 2 (by rfl) ⟨727377, by rfl⟩ : syracuseStep 1939673 = 1454755) B1454755
theorem B1816793 : Blo 1209422 1816793 := bstep (se 2 (by rfl) ⟨681297, by rfl⟩ : syracuseStep 1816793 = 1362595) B1362595
theorem B1210603 : Blo 1209422 1210603 := bstep (se 1 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 1210603 = 1815905) B1815905
theorem B1210615 : Blo 1209422 1210615 := bstep (se 1 (by rfl) ⟨907961, by rfl⟩ : syracuseStep 1210615 = 1815923) B1815923
theorem B1210635 : Blo 1209422 1210635 := bstep (se 1 (by rfl) ⟨907976, by rfl⟩ : syracuseStep 1210635 = 1815953) B1815953
theorem B1210647 : Blo 1209422 1210647 := bstep (se 1 (by rfl) ⟨907985, by rfl⟩ : syracuseStep 1210647 = 1815971) B1815971
theorem B1210667 : Blo 1209422 1210667 := bstep (se 1 (by rfl) ⟨908000, by rfl⟩ : syracuseStep 1210667 = 1816001) B1816001
theorem B13785389 : Blo 1209422 13785389 := bstep (se 3 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 13785389 = 5169521) B5169521
theorem B1210679 : Blo 1209422 1210679 := bstep (se 1 (by rfl) ⟨908009, by rfl⟩ : syracuseStep 1210679 = 1816019) B1816019
theorem B1210699 : Blo 1209422 1210699 := bstep (se 1 (by rfl) ⟨908024, by rfl⟩ : syracuseStep 1210699 = 1816049) B1816049
theorem B1816907 : Blo 1209422 1816907 := bstep (se 1 (by rfl) ⟨1362680, by rfl⟩ : syracuseStep 1816907 = 2725361) B2725361
theorem B1210711 : Blo 1209422 1210711 := bstep (se 1 (by rfl) ⟨908033, by rfl⟩ : syracuseStep 1210711 = 1816067) B1816067
theorem B1816919 : Blo 1209422 1816919 := bstep (se 1 (by rfl) ⟨1362689, by rfl⟩ : syracuseStep 1816919 = 2725379) B2725379
theorem B1210731 : Blo 1209422 1210731 := bstep (se 1 (by rfl) ⟨908048, by rfl⟩ : syracuseStep 1210731 = 1816097) B1816097
theorem B1210743 : Blo 1209422 1210743 := bstep (se 1 (by rfl) ⟨908057, by rfl⟩ : syracuseStep 1210743 = 1816115) B1816115
theorem B1210763 : Blo 1209422 1210763 := bstep (se 1 (by rfl) ⟨908072, by rfl⟩ : syracuseStep 1210763 = 1816145) B1816145
theorem B3447191 : Blo 1209422 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1210775 : Blo 1209422 1210775 := bstep (se 1 (by rfl) ⟨908081, by rfl⟩ : syracuseStep 1210775 = 1816163) B1816163
theorem B1816985 : Blo 1209422 1816985 := bstep (se 2 (by rfl) ⟨681369, by rfl⟩ : syracuseStep 1816985 = 1362739) B1362739
theorem B1210795 : Blo 1209422 1210795 := bstep (se 1 (by rfl) ⟨908096, by rfl⟩ : syracuseStep 1210795 = 1816193) B1816193
theorem B3062195 : Blo 1209422 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B1210807 : Blo 1209422 1210807 := bstep (se 1 (by rfl) ⟨908105, by rfl⟩ : syracuseStep 1210807 = 1816211) B1816211
theorem B1210827 : Blo 1209422 1210827 := bstep (se 1 (by rfl) ⟨908120, by rfl⟩ : syracuseStep 1210827 = 1816241) B1816241
theorem B1210839 : Blo 1209422 1210839 := bstep (se 1 (by rfl) ⟨908129, by rfl⟩ : syracuseStep 1210839 = 1816259) B1816259
theorem B4086233 : Blo 1209422 4086233 := bstep (se 2 (by rfl) ⟨1532337, by rfl⟩ : syracuseStep 4086233 = 3064675) B3064675
theorem B1210859 : Blo 1209422 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B1210871 : Blo 1209422 1210871 := bstep (se 1 (by rfl) ⟨908153, by rfl⟩ : syracuseStep 1210871 = 1816307) B1816307
theorem B1210891 : Blo 1209422 1210891 := bstep (se 1 (by rfl) ⟨908168, by rfl⟩ : syracuseStep 1210891 = 1816337) B1816337
theorem B1817099 : Blo 1209422 1817099 := bstep (se 1 (by rfl) ⟨1362824, by rfl⟩ : syracuseStep 1817099 = 2725649) B2725649
theorem B1210903 : Blo 1209422 1210903 := bstep (se 1 (by rfl) ⟨908177, by rfl⟩ : syracuseStep 1210903 = 1816355) B1816355
theorem B1817111 : Blo 1209422 1817111 := bstep (se 1 (by rfl) ⟨1362833, by rfl⟩ : syracuseStep 1817111 = 2725667) B2725667
theorem B1210923 : Blo 1209422 1210923 := bstep (se 1 (by rfl) ⟨908192, by rfl⟩ : syracuseStep 1210923 = 1816385) B1816385
theorem B2587187 : Blo 1209422 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B1210935 : Blo 1209422 1210935 := bstep (se 1 (by rfl) ⟨908201, by rfl⟩ : syracuseStep 1210935 = 1816403) B1816403
theorem B1210955 : Blo 1209422 1210955 := bstep (se 1 (by rfl) ⟨908216, by rfl⟩ : syracuseStep 1210955 = 1816433) B1816433
theorem B1210967 : Blo 1209422 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B4594265 : Blo 1209422 4594265 := bstep (se 2 (by rfl) ⟨1722849, by rfl⟩ : syracuseStep 4594265 = 3445699) B3445699
theorem B8968805 : Blo 1209422 8968805 := bstep (se 4 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 8968805 = 1681651) B1681651
theorem B1210987 : Blo 1209422 1210987 := bstep (se 1 (by rfl) ⟨908240, by rfl⟩ : syracuseStep 1210987 = 1816481) B1816481
theorem B1309303 : Blo 1209422 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B1210999 : Blo 1209422 1210999 := bstep (se 1 (by rfl) ⟨908249, by rfl⟩ : syracuseStep 1210999 = 1816499) B1816499
theorem B1211019 : Blo 1209422 1211019 := bstep (se 1 (by rfl) ⟨908264, by rfl⟩ : syracuseStep 1211019 = 1816529) B1816529
theorem B1211031 : Blo 1209422 1211031 := bstep (se 1 (by rfl) ⟨908273, by rfl⟩ : syracuseStep 1211031 = 1816547) B1816547
theorem B1211051 : Blo 1209422 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B1211063 : Blo 1209422 1211063 := bstep (se 1 (by rfl) ⟨908297, by rfl⟩ : syracuseStep 1211063 = 1816595) B1816595
theorem B4422347 : Blo 1209422 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B1211083 : Blo 1209422 1211083 := bstep (se 1 (by rfl) ⟨908312, by rfl⟩ : syracuseStep 1211083 = 1816625) B1816625
theorem B1211095 : Blo 1209422 1211095 := bstep (se 1 (by rfl) ⟨908321, by rfl⟩ : syracuseStep 1211095 = 1816643) B1816643
theorem B1211115 : Blo 1209422 1211115 := bstep (se 1 (by rfl) ⟨908336, by rfl⟩ : syracuseStep 1211115 = 1816673) B1816673
theorem B1211127 : Blo 1209422 1211127 := bstep (se 1 (by rfl) ⟨908345, by rfl⟩ : syracuseStep 1211127 = 1816691) B1816691
theorem B1211147 : Blo 1209422 1211147 := bstep (se 1 (by rfl) ⟨908360, by rfl⟩ : syracuseStep 1211147 = 1816721) B1816721
theorem B6126353 : Blo 1209422 6126353 := bstep (se 2 (by rfl) ⟨2297382, by rfl⟩ : syracuseStep 6126353 = 4594765) B4594765
theorem B1211159 : Blo 1209422 1211159 := bstep (se 1 (by rfl) ⟨908369, by rfl⟩ : syracuseStep 1211159 = 1816739) B1816739
theorem B1211179 : Blo 1209422 1211179 := bstep (se 1 (by rfl) ⟨908384, by rfl⟩ : syracuseStep 1211179 = 1816769) B1816769
theorem B6208301 : Blo 1209422 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B1211191 : Blo 1209422 1211191 := bstep (se 1 (by rfl) ⟨908393, by rfl⟩ : syracuseStep 1211191 = 1816787) B1816787
theorem B1211211 : Blo 1209422 1211211 := bstep (se 1 (by rfl) ⟨908408, by rfl⟩ : syracuseStep 1211211 = 1816817) B1816817
theorem B1211223 : Blo 1209422 1211223 := bstep (se 1 (by rfl) ⟨908417, by rfl⟩ : syracuseStep 1211223 = 1816835) B1816835
theorem B1211243 : Blo 1209422 1211243 := bstep (se 1 (by rfl) ⟨908432, by rfl⟩ : syracuseStep 1211243 = 1816865) B1816865
theorem B1293175 : Blo 1209422 1293175 := bstep (se 1 (by rfl) ⟨969881, by rfl⟩ : syracuseStep 1293175 = 1939763) B1939763
theorem B1211255 : Blo 1209422 1211255 := bstep (se 1 (by rfl) ⟨908441, by rfl⟩ : syracuseStep 1211255 = 1816883) B1816883
theorem B1211275 : Blo 1209422 1211275 := bstep (se 1 (by rfl) ⟨908456, by rfl⟩ : syracuseStep 1211275 = 1816913) B1816913
theorem B4594583 : Blo 1209422 4594583 := bstep (se 1 (by rfl) ⟨3445937, by rfl⟩ : syracuseStep 4594583 = 6891875) B6891875
theorem B1211287 : Blo 1209422 1211287 := bstep (se 1 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 1211287 = 1816931) B1816931
theorem B1211307 : Blo 1209422 1211307 := bstep (se 1 (by rfl) ⟨908480, by rfl⟩ : syracuseStep 1211307 = 1816961) B1816961
theorem B6126515 : Blo 1209422 6126515 := bstep (se 1 (by rfl) ⟨4594886, by rfl⟩ : syracuseStep 6126515 = 9189773) B9189773
theorem B1211319 : Blo 1209422 1211319 := bstep (se 1 (by rfl) ⟨908489, by rfl⟩ : syracuseStep 1211319 = 1816979) B1816979
theorem B3062731 : Blo 1209422 3062731 := bstep (se 1 (by rfl) ⟨2297048, by rfl⟩ : syracuseStep 3062731 = 4594097) B4594097
theorem B1211339 : Blo 1209422 1211339 := bstep (se 1 (by rfl) ⟨908504, by rfl⟩ : syracuseStep 1211339 = 1817009) B1817009
theorem B1530839 : Blo 1209422 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B1211351 : Blo 1209422 1211351 := bstep (se 1 (by rfl) ⟨908513, by rfl⟩ : syracuseStep 1211351 = 1817027) B1817027
theorem B1211371 : Blo 1209422 1211371 := bstep (se 1 (by rfl) ⟨908528, by rfl⟩ : syracuseStep 1211371 = 1817057) B1817057
theorem B1211383 : Blo 1209422 1211383 := bstep (se 1 (by rfl) ⟨908537, by rfl⟩ : syracuseStep 1211383 = 1817075) B1817075
theorem B2759681 : Blo 1209422 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B2489345 : Blo 1209422 2489345 := bstep (se 2 (by rfl) ⟨933504, by rfl⟩ : syracuseStep 2489345 = 1867009) B1867009
theorem B1211403 : Blo 1209422 1211403 := bstep (se 1 (by rfl) ⟨908552, by rfl⟩ : syracuseStep 1211403 = 1817105) B1817105
theorem B1211415 : Blo 1209422 1211415 := bstep (se 1 (by rfl) ⟨908561, by rfl⟩ : syracuseStep 1211415 = 1817123) B1817123
theorem B3062873 : Blo 1209422 3062873 := bstep (se 2 (by rfl) ⟨1148577, by rfl⟩ : syracuseStep 3062873 = 2297155) B2297155
theorem B2620505 : Blo 1209422 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B10345603 : Blo 1209422 10345603 := bstep (se 1 (by rfl) ⟨7759202, by rfl⟩ : syracuseStep 10345603 = 15518405) B15518405
theorem B4086935 : Blo 1209422 4086935 := bstep (se 1 (by rfl) ⟨3065201, by rfl⟩ : syracuseStep 4086935 = 6130403) B6130403
theorem B7757207 : Blo 1209422 7757207 := bstep (se 1 (by rfl) ⟨5817905, by rfl⟩ : syracuseStep 7757207 = 11635811) B11635811
theorem B17440217 : Blo 1209422 17440217 := bstep (se 2 (by rfl) ⟨6540081, by rfl⟩ : syracuseStep 17440217 = 13080163) B13080163
theorem B1965593 : Blo 1209422 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B4595251 : Blo 1209422 4595251 := bstep (se 1 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 4595251 = 6892877) B6892877
theorem B5045825 : Blo 1209422 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B7356035 : Blo 1209422 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B5168771 : Blo 1209422 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B2211467 : Blo 1209422 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B1531543 : Blo 1209422 1531543 := bstep (se 1 (by rfl) ⟨1148657, by rfl⟩ : syracuseStep 1531543 = 2297315) B2297315
theorem B4087475 : Blo 1209422 4087475 := bstep (se 1 (by rfl) ⟨3065606, by rfl⟩ : syracuseStep 4087475 = 6131213) B6131213
theorem B20684645 : Blo 1209422 20684645 := bstep (se 4 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 20684645 = 3878371) B3878371
theorem B3063703 : Blo 1209422 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B4087745 : Blo 1209422 4087745 := bstep (se 2 (by rfl) ⟨1532904, by rfl⟩ : syracuseStep 4087745 = 3065809) B3065809
theorem B4595723 : Blo 1209422 4595723 := bstep (se 1 (by rfl) ⟨3446792, by rfl⟩ : syracuseStep 4595723 = 6893585) B6893585
theorem B6897707 : Blo 1209422 6897707 := bstep (se 1 (by rfl) ⟨5173280, by rfl⟩ : syracuseStep 6897707 = 10346561) B10346561
theorem B1531963 : Blo 1209422 1531963 := bstep (se 1 (by rfl) ⟨1148972, by rfl⟩ : syracuseStep 1531963 = 2297945) B2297945
theorem B4088123 : Blo 1209422 4088123 := bstep (se 1 (by rfl) ⟨3066092, by rfl⟩ : syracuseStep 4088123 = 6132185) B6132185
theorem B20693393 : Blo 1209422 20693393 := bstep (se 2 (by rfl) ⟨7760022, by rfl⟩ : syracuseStep 20693393 = 15520045) B15520045
theorem B3064331 : Blo 1209422 3064331 := bstep (se 1 (by rfl) ⟨2298248, by rfl⟩ : syracuseStep 3064331 = 4596497) B4596497
theorem B1532459 : Blo 1209422 1532459 := bstep (se 1 (by rfl) ⟨1149344, by rfl⟩ : syracuseStep 1532459 = 2298689) B2298689
theorem B13779557 : Blo 1209422 13779557 := bstep (se 4 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 13779557 = 2583667) B2583667
theorem B15508259 : Blo 1209422 15508259 := bstep (se 1 (by rfl) ⟨11631194, by rfl⟩ : syracuseStep 15508259 = 23262389) B23262389
theorem B1745737 : Blo 1209422 1745737 := bstep (se 2 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 1745737 = 1309303) B1309303
theorem B1360903 : Blo 1209422 1360903 := bstep (se 1 (by rfl) ⟨1020677, by rfl⟩ : syracuseStep 1360903 = 2041355) B2041355
theorem B1532935 : Blo 1209422 1532935 := bstep (se 1 (by rfl) ⟨1149701, by rfl⟩ : syracuseStep 1532935 = 2299403) B2299403
theorem B9815051 : Blo 1209422 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B5170205 : Blo 1209422 5170205 := bstep (se 3 (by rfl) ⟨969413, by rfl⟩ : syracuseStep 5170205 = 1938827) B1938827
theorem B6628439 : Blo 1209422 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B3064979 : Blo 1209422 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B6890669 : Blo 1209422 6890669 := bstep (se 3 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 6890669 = 2584001) B2584001
theorem B1361083 : Blo 1209422 1361083 := bstep (se 1 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 1361083 = 2041625) B2041625
theorem B3728585 : Blo 1209422 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B5170547 : Blo 1209422 5170547 := bstep (se 1 (by rfl) ⟨3877910, by rfl⟩ : syracuseStep 5170547 = 7755821) B7755821
theorem B3065273 : Blo 1209422 3065273 := bstep (se 2 (by rfl) ⟨1149477, by rfl⟩ : syracuseStep 3065273 = 2298955) B2298955
theorem B8717777 : Blo 1209422 8717777 := bstep (se 2 (by rfl) ⟨3269166, by rfl⟩ : syracuseStep 8717777 = 6538333) B6538333
theorem B6899165 : Blo 1209422 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B2041463 : Blo 1209422 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B1361551 : Blo 1209422 1361551 := bstep (se 1 (by rfl) ⟨1021163, by rfl⟩ : syracuseStep 1361551 = 2042327) B2042327
theorem B10348337 : Blo 1209422 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B4138867 : Blo 1209422 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B2721671 : Blo 1209422 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B6129593 : Blo 1209422 6129593 := bstep (se 2 (by rfl) ⟨2298597, by rfl⟩ : syracuseStep 6129593 = 4597195) B4597195
theorem B13781015 : Blo 1209422 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B2721851 : Blo 1209422 2721851 := bstep (se 1 (by rfl) ⟨2041388, by rfl⟩ : syracuseStep 2721851 = 4082777) B4082777
theorem B2041915 : Blo 1209422 2041915 := bstep (se 1 (by rfl) ⟨1531436, by rfl⟩ : syracuseStep 2041915 = 3062873) B3062873
theorem B1747003 : Blo 1209422 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B3065971 : Blo 1209422 3065971 := bstep (se 1 (by rfl) ⟨2299478, by rfl⟩ : syracuseStep 3065971 = 4598957) B4598957
theorem B2181239 : Blo 1209422 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B1362055 : Blo 1209422 1362055 := bstep (se 1 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 1362055 = 2043083) B2043083
theorem B2721977 : Blo 1209422 2721977 := bstep (se 2 (by rfl) ⟨1020741, by rfl⟩ : syracuseStep 2721977 = 2041483) B2041483
theorem B2042057 : Blo 1209422 2042057 := bstep (se 2 (by rfl) ⟨765771, by rfl⟩ : syracuseStep 2042057 = 1531543) B1531543
theorem B3066113 : Blo 1209422 3066113 := bstep (se 2 (by rfl) ⟨1149792, by rfl⟩ : syracuseStep 3066113 = 2299585) B2299585
theorem B5171471 : Blo 1209422 5171471 := bstep (se 1 (by rfl) ⟨3878603, by rfl⟩ : syracuseStep 5171471 = 7757207) B7757207
theorem B11634961 : Blo 1209422 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B11626811 : Blo 1209422 11626811 := bstep (se 1 (by rfl) ⟨8720108, by rfl⟩ : syracuseStep 11626811 = 17440217) B17440217
theorem B1362235 : Blo 1209422 1362235 := bstep (se 1 (by rfl) ⟨1021676, by rfl⟩ : syracuseStep 1362235 = 2043353) B2043353
theorem B6539609 : Blo 1209422 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B2296183 : Blo 1209422 2296183 := bstep (se 1 (by rfl) ⟨1722137, by rfl⟩ : syracuseStep 2296183 = 3444275) B3444275
theorem B2910617 : Blo 1209422 2910617 := bstep (se 2 (by rfl) ⟨1091481, by rfl⟩ : syracuseStep 2910617 = 2182963) B2182963
theorem B2722319 : Blo 1209422 2722319 := bstep (se 1 (by rfl) ⟨2041739, by rfl⟩ : syracuseStep 2722319 = 4083479) B4083479
theorem B2722337 : Blo 1209422 2722337 := bstep (se 2 (by rfl) ⟨1020876, by rfl⟩ : syracuseStep 2722337 = 2041753) B2041753
theorem B4082237 : Blo 1209422 4082237 := bstep (se 3 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 4082237 = 1530839) B1530839
theorem B13789763 : Blo 1209422 13789763 := bstep (se 1 (by rfl) ⟨10342322, by rfl⟩ : syracuseStep 13789763 = 20684645) B20684645
theorem B11045443 : Blo 1209422 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B7359149 : Blo 1209422 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B58862285 : Blo 1209422 58862285 := bstep (se 3 (by rfl) ⟨11036678, by rfl⟩ : syracuseStep 58862285 = 22073357) B22073357
theorem B3681035 : Blo 1209422 3681035 := bstep (se 1 (by rfl) ⟨2760776, by rfl⟩ : syracuseStep 3681035 = 5521553) B5521553
theorem B1723151 : Blo 1209422 1723151 := bstep (se 1 (by rfl) ⟨1292363, by rfl⟩ : syracuseStep 1723151 = 2584727) B2584727
theorem B1362703 : Blo 1209422 1362703 := bstep (se 1 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 1362703 = 2044055) B2044055
theorem B20957987 : Blo 1209422 20957987 := bstep (se 1 (by rfl) ⟨15718490, by rfl⟩ : syracuseStep 20957987 = 31436981) B31436981
theorem B2722679 : Blo 1209422 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B2042759 : Blo 1209422 2042759 := bstep (se 1 (by rfl) ⟨1532069, by rfl⟩ : syracuseStep 2042759 = 3064139) B3064139
theorem B2583497 : Blo 1209422 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B7760843 : Blo 1209422 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B11037707 : Blo 1209422 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B2722859 : Blo 1209422 2722859 := bstep (se 1 (by rfl) ⟨2042144, by rfl⟩ : syracuseStep 2722859 = 4084289) B4084289
theorem B6130889 : Blo 1209422 6130889 := bstep (se 2 (by rfl) ⟨2299083, by rfl⟩ : syracuseStep 6130889 = 4598167) B4598167
theorem B5172461 : Blo 1209422 5172461 := bstep (se 3 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 5172461 = 1939673) B1939673
theorem B17460461 : Blo 1209422 17460461 := bstep (se 3 (by rfl) ⟨3273836, by rfl⟩ : syracuseStep 17460461 = 6547673) B6547673
theorem B2723219 : Blo 1209422 2723219 := bstep (se 1 (by rfl) ⟨2042414, by rfl⟩ : syracuseStep 2723219 = 4084829) B4084829
theorem B3444115 : Blo 1209422 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B2584009 : Blo 1209422 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B2723273 : Blo 1209422 2723273 := bstep (se 2 (by rfl) ⟨1021227, by rfl⟩ : syracuseStep 2723273 = 2042455) B2042455
theorem B6893059 : Blo 1209422 6893059 := bstep (se 1 (by rfl) ⟨5169794, by rfl⟩ : syracuseStep 6893059 = 10339589) B10339589
theorem B8728067 : Blo 1209422 8728067 := bstep (se 1 (by rfl) ⟨6546050, by rfl⟩ : syracuseStep 8728067 = 13092101) B13092101
theorem B2043407 : Blo 1209422 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B1814135 : Blo 1209422 1814135 := bstep (se 1 (by rfl) ⟨1360601, by rfl⟩ : syracuseStep 1814135 = 2721203) B2721203
theorem B1814159 : Blo 1209422 1814159 := bstep (se 1 (by rfl) ⟨1360619, by rfl⟩ : syracuseStep 1814159 = 2721239) B2721239
theorem B1814201 : Blo 1209422 1814201 := bstep (se 2 (by rfl) ⟨680325, by rfl⟩ : syracuseStep 1814201 = 1360651) B1360651
theorem B4484845 : Blo 1209422 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B1814279 : Blo 1209422 1814279 := bstep (se 1 (by rfl) ⟨1360709, by rfl⟩ : syracuseStep 1814279 = 2721419) B2721419
theorem B1814315 : Blo 1209422 1814315 := bstep (se 1 (by rfl) ⟨1360736, by rfl⟩ : syracuseStep 1814315 = 2721473) B2721473
theorem B4599611 : Blo 1209422 4599611 := bstep (se 1 (by rfl) ⟨3449708, by rfl⟩ : syracuseStep 4599611 = 6899417) B6899417
theorem B1814345 : Blo 1209422 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B2297747 : Blo 1209422 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B5173145 : Blo 1209422 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B4083641 : Blo 1209422 4083641 := bstep (se 2 (by rfl) ⟨1531365, by rfl⟩ : syracuseStep 4083641 = 3062731) B3062731
theorem B1814459 : Blo 1209422 1814459 := bstep (se 1 (by rfl) ⟨1360844, by rfl⟩ : syracuseStep 1814459 = 2721689) B2721689
theorem B2297801 : Blo 1209422 2297801 := bstep (se 2 (by rfl) ⟨861675, by rfl⟩ : syracuseStep 2297801 = 1723351) B1723351
theorem B1814519 : Blo 1209422 1814519 := bstep (se 1 (by rfl) ⟨1360889, by rfl⟩ : syracuseStep 1814519 = 2721779) B2721779
theorem B1839119 : Blo 1209422 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B1814543 : Blo 1209422 1814543 := bstep (se 1 (by rfl) ⟨1360907, by rfl⟩ : syracuseStep 1814543 = 2721815) B2721815
theorem B2297899 : Blo 1209422 2297899 := bstep (se 1 (by rfl) ⟨1723424, by rfl⟩ : syracuseStep 2297899 = 3446849) B3446849
theorem B2043947 : Blo 1209422 2043947 := bstep (se 1 (by rfl) ⟨1532960, by rfl⟩ : syracuseStep 2043947 = 3065921) B3065921
theorem B1814585 : Blo 1209422 1814585 := bstep (se 2 (by rfl) ⟨680469, by rfl⟩ : syracuseStep 1814585 = 1360939) B1360939
theorem B23588981 : Blo 1209422 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B1814663 : Blo 1209422 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B2723975 : Blo 1209422 2723975 := bstep (se 1 (by rfl) ⟨2042981, by rfl⟩ : syracuseStep 2723975 = 4085963) B4085963
theorem B1814699 : Blo 1209422 1814699 := bstep (se 1 (by rfl) ⟨1361024, by rfl⟩ : syracuseStep 1814699 = 2722049) B2722049
theorem B13455533 : Blo 1209422 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B1814729 : Blo 1209422 1814729 := bstep (se 2 (by rfl) ⟨680523, by rfl⟩ : syracuseStep 1814729 = 1361047) B1361047
theorem B2584847 : Blo 1209422 2584847 := bstep (se 1 (by rfl) ⟨1938635, by rfl⟩ : syracuseStep 2584847 = 3877271) B3877271
theorem B2298127 : Blo 1209422 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 1209422 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B1814843 : Blo 1209422 1814843 := bstep (se 1 (by rfl) ⟨1361132, by rfl⟩ : syracuseStep 1814843 = 2722265) B2722265
theorem B2724155 : Blo 1209422 2724155 := bstep (se 1 (by rfl) ⟨2043116, by rfl⟩ : syracuseStep 2724155 = 4086233) B4086233
theorem B19616093 : Blo 1209422 19616093 := bstep (se 3 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 19616093 = 7356035) B7356035
theorem B1814903 : Blo 1209422 1814903 := bstep (se 1 (by rfl) ⟨1361177, by rfl⟩ : syracuseStep 1814903 = 2722355) B2722355
theorem B1814927 : Blo 1209422 1814927 := bstep (se 1 (by rfl) ⟨1361195, by rfl⟩ : syracuseStep 1814927 = 2722391) B2722391
theorem B6123923 : Blo 1209422 6123923 := bstep (se 1 (by rfl) ⟨4592942, by rfl⟩ : syracuseStep 6123923 = 9185885) B9185885
theorem B1814969 : Blo 1209422 1814969 := bstep (se 2 (by rfl) ⟨680613, by rfl⟩ : syracuseStep 1814969 = 1361227) B1361227
theorem B2724281 : Blo 1209422 2724281 := bstep (se 2 (by rfl) ⟨1021605, by rfl⟩ : syracuseStep 2724281 = 2043211) B2043211
theorem B1815047 : Blo 1209422 1815047 := bstep (se 1 (by rfl) ⟨1361285, by rfl⟩ : syracuseStep 1815047 = 2722571) B2722571
theorem B4084235 : Blo 1209422 4084235 := bstep (se 1 (by rfl) ⟨3063176, by rfl⟩ : syracuseStep 4084235 = 6126353) B6126353
theorem B1815083 : Blo 1209422 1815083 := bstep (se 1 (by rfl) ⟨1361312, by rfl⟩ : syracuseStep 1815083 = 2722625) B2722625
theorem B1815113 : Blo 1209422 1815113 := bstep (se 2 (by rfl) ⟨680667, by rfl⟩ : syracuseStep 1815113 = 1361335) B1361335
theorem B4084343 : Blo 1209422 4084343 := bstep (se 1 (by rfl) ⟨3063257, by rfl⟩ : syracuseStep 4084343 = 6126515) B6126515
theorem B1659563 : Blo 1209422 1659563 := bstep (se 1 (by rfl) ⟨1244672, by rfl⟩ : syracuseStep 1659563 = 2489345) B2489345
theorem B1815227 : Blo 1209422 1815227 := bstep (se 1 (by rfl) ⟨1361420, by rfl⟩ : syracuseStep 1815227 = 2722841) B2722841
theorem B1815287 : Blo 1209422 1815287 := bstep (se 1 (by rfl) ⟨1361465, by rfl⟩ : syracuseStep 1815287 = 2722931) B2722931
theorem B1815311 : Blo 1209422 1815311 := bstep (se 1 (by rfl) ⟨1361483, by rfl⟩ : syracuseStep 1815311 = 2722967) B2722967
theorem B2724623 : Blo 1209422 2724623 := bstep (se 1 (by rfl) ⟨2043467, by rfl⟩ : syracuseStep 2724623 = 4086935) B4086935
theorem B2724641 : Blo 1209422 2724641 := bstep (se 2 (by rfl) ⟨1021740, by rfl⟩ : syracuseStep 2724641 = 2043481) B2043481
theorem B1815353 : Blo 1209422 1815353 := bstep (se 2 (by rfl) ⟨680757, by rfl⟩ : syracuseStep 1815353 = 1361515) B1361515
theorem B1815431 : Blo 1209422 1815431 := bstep (se 1 (by rfl) ⟨1361573, by rfl⟩ : syracuseStep 1815431 = 2723147) B2723147
theorem B2585479 : Blo 1209422 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B5813137 : Blo 1209422 5813137 := bstep (se 2 (by rfl) ⟨2179926, by rfl⟩ : syracuseStep 5813137 = 4359853) B4359853
theorem B1815467 : Blo 1209422 1815467 := bstep (se 1 (by rfl) ⟨1361600, by rfl⟩ : syracuseStep 1815467 = 2723201) B2723201
theorem B1815497 : Blo 1209422 1815497 := bstep (se 2 (by rfl) ⟨680811, by rfl⟩ : syracuseStep 1815497 = 1361623) B1361623
theorem B1815611 : Blo 1209422 1815611 := bstep (se 1 (by rfl) ⟨1361708, by rfl⟩ : syracuseStep 1815611 = 2723417) B2723417
theorem B3445847 : Blo 1209422 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1815671 : Blo 1209422 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B2724983 : Blo 1209422 2724983 := bstep (se 1 (by rfl) ⟨2043737, by rfl⟩ : syracuseStep 2724983 = 4087475) B4087475
theorem B1209479 : Blo 1209422 1209479 := bstep (se 1 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 1209479 = 1814219) B1814219
theorem B1209487 : Blo 1209422 1209487 := bstep (se 1 (by rfl) ⟨907115, by rfl⟩ : syracuseStep 1209487 = 1814231) B1814231
theorem B1815695 : Blo 1209422 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B1815737 : Blo 1209422 1815737 := bstep (se 2 (by rfl) ⟨680901, by rfl⟩ : syracuseStep 1815737 = 1361803) B1361803
theorem B1209531 : Blo 1209422 1209531 := bstep (se 1 (by rfl) ⟨907148, by rfl⟩ : syracuseStep 1209531 = 1814297) B1814297
theorem B4084937 : Blo 1209422 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1209607 : Blo 1209422 1209607 := bstep (se 1 (by rfl) ⟨907205, by rfl⟩ : syracuseStep 1209607 = 1814411) B1814411
theorem B1815815 : Blo 1209422 1815815 := bstep (se 1 (by rfl) ⟨1361861, by rfl⟩ : syracuseStep 1815815 = 2723723) B2723723
theorem B1209615 : Blo 1209422 1209615 := bstep (se 1 (by rfl) ⟨907211, by rfl⟩ : syracuseStep 1209615 = 1814423) B1814423
theorem B1815851 : Blo 1209422 1815851 := bstep (se 1 (by rfl) ⟨1361888, by rfl⟩ : syracuseStep 1815851 = 2723777) B2723777
theorem B2725163 : Blo 1209422 2725163 := bstep (se 1 (by rfl) ⟨2043872, by rfl⟩ : syracuseStep 2725163 = 4087745) B4087745
theorem B1209659 : Blo 1209422 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B2585915 : Blo 1209422 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B1815881 : Blo 1209422 1815881 := bstep (se 2 (by rfl) ⟨680955, by rfl⟩ : syracuseStep 1815881 = 1361911) B1361911
theorem B1209735 : Blo 1209422 1209735 := bstep (se 1 (by rfl) ⟨907301, by rfl⟩ : syracuseStep 1209735 = 1814603) B1814603
theorem B5813639 : Blo 1209422 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B7361927 : Blo 1209422 7361927 := bstep (se 1 (by rfl) ⟨5521445, by rfl⟩ : syracuseStep 7361927 = 11042891) B11042891
theorem B1291663 : Blo 1209422 1291663 := bstep (se 1 (by rfl) ⟨968747, by rfl⟩ : syracuseStep 1291663 = 1937495) B1937495
theorem B1209743 : Blo 1209422 1209743 := bstep (se 1 (by rfl) ⟨907307, by rfl⟩ : syracuseStep 1209743 = 1814615) B1814615
theorem B181630349 : Blo 1209422 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B1209787 : Blo 1209422 1209787 := bstep (se 1 (by rfl) ⟨907340, by rfl⟩ : syracuseStep 1209787 = 1814681) B1814681
theorem B1815995 : Blo 1209422 1815995 := bstep (se 1 (by rfl) ⟨1361996, by rfl⟩ : syracuseStep 1815995 = 2723993) B2723993
theorem B1816055 : Blo 1209422 1816055 := bstep (se 1 (by rfl) ⟨1362041, by rfl⟩ : syracuseStep 1816055 = 2724083) B2724083
theorem B1209863 : Blo 1209422 1209863 := bstep (se 1 (by rfl) ⟨907397, by rfl⟩ : syracuseStep 1209863 = 1814795) B1814795
theorem B1209871 : Blo 1209422 1209871 := bstep (se 1 (by rfl) ⟨907403, by rfl⟩ : syracuseStep 1209871 = 1814807) B1814807
theorem B1816079 : Blo 1209422 1816079 := bstep (se 1 (by rfl) ⟨1362059, by rfl⟩ : syracuseStep 1816079 = 2724119) B2724119
theorem B1816121 : Blo 1209422 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B1209915 : Blo 1209422 1209915 := bstep (se 1 (by rfl) ⟨907436, by rfl⟩ : syracuseStep 1209915 = 1814873) B1814873
theorem B15521381 : Blo 1209422 15521381 := bstep (se 4 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 15521381 = 2910259) B2910259
theorem B1209991 : Blo 1209422 1209991 := bstep (se 1 (by rfl) ⟨907493, by rfl⟩ : syracuseStep 1209991 = 1814987) B1814987
theorem B1816199 : Blo 1209422 1816199 := bstep (se 1 (by rfl) ⟨1362149, by rfl⟩ : syracuseStep 1816199 = 2724299) B2724299
theorem B1209999 : Blo 1209422 1209999 := bstep (se 1 (by rfl) ⟨907499, by rfl⟩ : syracuseStep 1209999 = 1814999) B1814999
theorem B2725523 : Blo 1209422 2725523 := bstep (se 1 (by rfl) ⟨2044142, by rfl⟩ : syracuseStep 2725523 = 4088285) B4088285
theorem B1816235 : Blo 1209422 1816235 := bstep (se 1 (by rfl) ⟨1362176, by rfl⟩ : syracuseStep 1816235 = 2724353) B2724353
theorem B1210043 : Blo 1209422 1210043 := bstep (se 1 (by rfl) ⟨907532, by rfl⟩ : syracuseStep 1210043 = 1815065) B1815065
theorem B1816265 : Blo 1209422 1816265 := bstep (se 2 (by rfl) ⟨681099, by rfl⟩ : syracuseStep 1816265 = 1362199) B1362199
theorem B2725577 : Blo 1209422 2725577 := bstep (se 2 (by rfl) ⟨1022091, by rfl⟩ : syracuseStep 2725577 = 2044183) B2044183
theorem B13776641 : Blo 1209422 13776641 := bstep (se 2 (by rfl) ⟨5166240, by rfl⟩ : syracuseStep 13776641 = 10332481) B10332481
theorem B1210119 : Blo 1209422 1210119 := bstep (se 1 (by rfl) ⟨907589, by rfl⟩ : syracuseStep 1210119 = 1815179) B1815179
theorem B1210127 : Blo 1209422 1210127 := bstep (se 1 (by rfl) ⟨907595, by rfl⟩ : syracuseStep 1210127 = 1815191) B1815191
theorem B3061547 : Blo 1209422 3061547 := bstep (se 1 (by rfl) ⟨2296160, by rfl⟩ : syracuseStep 3061547 = 4592321) B4592321
theorem B2299691 : Blo 1209422 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B1210171 : Blo 1209422 1210171 := bstep (se 1 (by rfl) ⟨907628, by rfl⟩ : syracuseStep 1210171 = 1815257) B1815257
theorem B1816379 : Blo 1209422 1816379 := bstep (se 1 (by rfl) ⟨1362284, by rfl⟩ : syracuseStep 1816379 = 2724569) B2724569
theorem B6895475 : Blo 1209422 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B1816439 : Blo 1209422 1816439 := bstep (se 1 (by rfl) ⟨1362329, by rfl⟩ : syracuseStep 1816439 = 2724659) B2724659
theorem B2586487 : Blo 1209422 2586487 := bstep (se 1 (by rfl) ⟨1939865, by rfl⟩ : syracuseStep 2586487 = 3879731) B3879731
theorem B1210247 : Blo 1209422 1210247 := bstep (se 1 (by rfl) ⟨907685, by rfl⟩ : syracuseStep 1210247 = 1815371) B1815371
theorem B4085639 : Blo 1209422 4085639 := bstep (se 1 (by rfl) ⟨3064229, by rfl⟩ : syracuseStep 4085639 = 6128459) B6128459
theorem B1210255 : Blo 1209422 1210255 := bstep (se 1 (by rfl) ⟨907691, by rfl⟩ : syracuseStep 1210255 = 1815383) B1815383
theorem B1816463 : Blo 1209422 1816463 := bstep (se 1 (by rfl) ⟨1362347, by rfl⟩ : syracuseStep 1816463 = 2724695) B2724695
theorem B1816505 : Blo 1209422 1816505 := bstep (se 2 (by rfl) ⟨681189, by rfl⟩ : syracuseStep 1816505 = 1362379) B1362379
theorem B1210299 : Blo 1209422 1210299 := bstep (se 1 (by rfl) ⟨907724, by rfl⟩ : syracuseStep 1210299 = 1815449) B1815449
theorem B1210375 : Blo 1209422 1210375 := bstep (se 1 (by rfl) ⟨907781, by rfl⟩ : syracuseStep 1210375 = 1815563) B1815563
theorem B1816583 : Blo 1209422 1816583 := bstep (se 1 (by rfl) ⟨1362437, by rfl⟩ : syracuseStep 1816583 = 2724875) B2724875
theorem B1210383 : Blo 1209422 1210383 := bstep (se 1 (by rfl) ⟨907787, by rfl⟩ : syracuseStep 1210383 = 1815575) B1815575
theorem B1816619 : Blo 1209422 1816619 := bstep (se 1 (by rfl) ⟨1362464, by rfl⟩ : syracuseStep 1816619 = 2724929) B2724929
theorem B2586667 : Blo 1209422 2586667 := bstep (se 1 (by rfl) ⟨1940000, by rfl⟩ : syracuseStep 2586667 = 3880001) B3880001
theorem B1210427 : Blo 1209422 1210427 := bstep (se 1 (by rfl) ⟨907820, by rfl⟩ : syracuseStep 1210427 = 1815641) B1815641
theorem B1816649 : Blo 1209422 1816649 := bstep (se 2 (by rfl) ⟨681243, by rfl⟩ : syracuseStep 1816649 = 1362487) B1362487
theorem B2586743 : Blo 1209422 2586743 := bstep (se 1 (by rfl) ⟨1940057, by rfl⟩ : syracuseStep 2586743 = 3880115) B3880115
theorem B1210503 : Blo 1209422 1210503 := bstep (se 1 (by rfl) ⟨907877, by rfl⟩ : syracuseStep 1210503 = 1815755) B1815755
theorem B1210511 : Blo 1209422 1210511 := bstep (se 1 (by rfl) ⟨907883, by rfl⟩ : syracuseStep 1210511 = 1815767) B1815767
theorem B1210555 : Blo 1209422 1210555 := bstep (se 1 (by rfl) ⟨907916, by rfl⟩ : syracuseStep 1210555 = 1815833) B1815833
theorem B1841339 : Blo 1209422 1841339 := bstep (se 1 (by rfl) ⟨1381004, by rfl⟩ : syracuseStep 1841339 = 2762009) B2762009
theorem B1816763 : Blo 1209422 1816763 := bstep (se 1 (by rfl) ⟨1362572, by rfl⟩ : syracuseStep 1816763 = 2725145) B2725145
theorem B1816823 : Blo 1209422 1816823 := bstep (se 1 (by rfl) ⟨1362617, by rfl⟩ : syracuseStep 1816823 = 2725235) B2725235
theorem B4086017 : Blo 1209422 4086017 := bstep (se 2 (by rfl) ⟨1532256, by rfl⟩ : syracuseStep 4086017 = 3064513) B3064513
theorem B1210631 : Blo 1209422 1210631 := bstep (se 1 (by rfl) ⟨907973, by rfl⟩ : syracuseStep 1210631 = 1815947) B1815947
theorem B1210639 : Blo 1209422 1210639 := bstep (se 1 (by rfl) ⟨907979, by rfl⟩ : syracuseStep 1210639 = 1815959) B1815959
theorem B1816847 : Blo 1209422 1816847 := bstep (se 1 (by rfl) ⟨1362635, by rfl⟩ : syracuseStep 1816847 = 2725271) B2725271
theorem B1816889 : Blo 1209422 1816889 := bstep (se 2 (by rfl) ⟨681333, by rfl⟩ : syracuseStep 1816889 = 1362667) B1362667
theorem B1210683 : Blo 1209422 1210683 := bstep (se 1 (by rfl) ⟨908012, by rfl⟩ : syracuseStep 1210683 = 1816025) B1816025
theorem B1210759 : Blo 1209422 1210759 := bstep (se 1 (by rfl) ⟨908069, by rfl⟩ : syracuseStep 1210759 = 1816139) B1816139
theorem B1816967 : Blo 1209422 1816967 := bstep (se 1 (by rfl) ⟨1362725, by rfl⟩ : syracuseStep 1816967 = 2725451) B2725451
theorem B1210767 : Blo 1209422 1210767 := bstep (se 1 (by rfl) ⟨908075, by rfl⟩ : syracuseStep 1210767 = 1816151) B1816151
theorem B4594067 : Blo 1209422 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B1817003 : Blo 1209422 1817003 := bstep (se 1 (by rfl) ⟨1362752, by rfl⟩ : syracuseStep 1817003 = 2725505) B2725505
theorem B1210811 : Blo 1209422 1210811 := bstep (se 1 (by rfl) ⟨908108, by rfl⟩ : syracuseStep 1210811 = 1816217) B1816217
theorem B1817033 : Blo 1209422 1817033 := bstep (se 2 (by rfl) ⟨681387, by rfl⟩ : syracuseStep 1817033 = 1362775) B1362775
theorem B1210887 : Blo 1209422 1210887 := bstep (se 1 (by rfl) ⟨908165, by rfl⟩ : syracuseStep 1210887 = 1816331) B1816331
theorem B1210895 : Blo 1209422 1210895 := bstep (se 1 (by rfl) ⟨908171, by rfl⟩ : syracuseStep 1210895 = 1816343) B1816343
theorem B1210939 : Blo 1209422 1210939 := bstep (se 1 (by rfl) ⟨908204, by rfl⟩ : syracuseStep 1210939 = 1816409) B1816409
theorem B37280321 : Blo 1209422 37280321 := bstep (se 2 (by rfl) ⟨13980120, by rfl⟩ : syracuseStep 37280321 = 27960241) B27960241
theorem B3062387 : Blo 1209422 3062387 := bstep (se 1 (by rfl) ⟨2296790, by rfl⟩ : syracuseStep 3062387 = 4593581) B4593581
theorem B3062407 : Blo 1209422 3062407 := bstep (se 1 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 3062407 = 4593611) B4593611
theorem B3447431 : Blo 1209422 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B1211015 : Blo 1209422 1211015 := bstep (se 1 (by rfl) ⟨908261, by rfl⟩ : syracuseStep 1211015 = 1816523) B1816523
theorem B1211023 : Blo 1209422 1211023 := bstep (se 1 (by rfl) ⟨908267, by rfl⟩ : syracuseStep 1211023 = 1816535) B1816535
theorem B1211067 : Blo 1209422 1211067 := bstep (se 1 (by rfl) ⟨908300, by rfl⟩ : syracuseStep 1211067 = 1816601) B1816601
theorem B5241581 : Blo 1209422 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B1211143 : Blo 1209422 1211143 := bstep (se 1 (by rfl) ⟨908357, by rfl⟩ : syracuseStep 1211143 = 1816715) B1816715
theorem B1211151 : Blo 1209422 1211151 := bstep (se 1 (by rfl) ⟨908363, by rfl⟩ : syracuseStep 1211151 = 1816727) B1816727
theorem B9812785 : Blo 1209422 9812785 := bstep (se 2 (by rfl) ⟨3679794, by rfl⟩ : syracuseStep 9812785 = 7359589) B7359589
theorem B1211195 : Blo 1209422 1211195 := bstep (se 1 (by rfl) ⟨908396, by rfl⟩ : syracuseStep 1211195 = 1816793) B1816793
theorem B13794137 : Blo 1209422 13794137 := bstep (se 2 (by rfl) ⟨5172801, by rfl⟩ : syracuseStep 13794137 = 10345603) B10345603
theorem B9190259 : Blo 1209422 9190259 := bstep (se 1 (by rfl) ⟨6892694, by rfl⟩ : syracuseStep 9190259 = 13785389) B13785389
theorem B1211271 : Blo 1209422 1211271 := bstep (se 1 (by rfl) ⟨908453, by rfl⟩ : syracuseStep 1211271 = 1816907) B1816907
theorem B1211279 : Blo 1209422 1211279 := bstep (se 1 (by rfl) ⟨908459, by rfl⟩ : syracuseStep 1211279 = 1816919) B1816919
theorem B3062681 : Blo 1209422 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2759609 : Blo 1209422 2759609 := bstep (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) B2069707
theorem B1211323 : Blo 1209422 1211323 := bstep (se 1 (by rfl) ⟨908492, by rfl⟩ : syracuseStep 1211323 = 1816985) B1816985
theorem B1211399 : Blo 1209422 1211399 := bstep (se 1 (by rfl) ⟨908549, by rfl⟩ : syracuseStep 1211399 = 1817099) B1817099
theorem B1530895 : Blo 1209422 1530895 := bstep (se 1 (by rfl) ⟨1148171, by rfl⟩ : syracuseStep 1530895 = 2296343) B2296343
theorem B1211407 : Blo 1209422 1211407 := bstep (se 1 (by rfl) ⟨908555, by rfl⟩ : syracuseStep 1211407 = 1817111) B1817111
theorem B4086827 : Blo 1209422 4086827 := bstep (se 1 (by rfl) ⟨3065120, by rfl⟩ : syracuseStep 4086827 = 6130241) B6130241
theorem B3062843 : Blo 1209422 3062843 := bstep (se 1 (by rfl) ⟨2297132, by rfl⟩ : syracuseStep 3062843 = 4594265) B4594265
theorem B5979203 : Blo 1209422 5979203 := bstep (se 1 (by rfl) ⟨4484402, by rfl⟩ : syracuseStep 5979203 = 8968805) B8968805
theorem B2948231 : Blo 1209422 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B6888685 : Blo 1209422 6888685 := bstep (se 3 (by rfl) ⟨1291628, by rfl⟩ : syracuseStep 6888685 = 2583257) B2583257
theorem B3063055 : Blo 1209422 3063055 := bstep (se 1 (by rfl) ⟨2297291, by rfl⟩ : syracuseStep 3063055 = 4594583) B4594583
theorem B3448079 : Blo 1209422 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B6896933 : Blo 1209422 6896933 := bstep (se 4 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 6896933 = 1293175) B1293175
theorem B6127001 : Blo 1209422 6127001 := bstep (se 2 (by rfl) ⟨2297625, by rfl⟩ : syracuseStep 6127001 = 4595251) B4595251
theorem B6544907 : Blo 1209422 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B3063329 : Blo 1209422 3063329 := bstep (se 2 (by rfl) ⟨1148748, by rfl⟩ : syracuseStep 3063329 = 2297497) B2297497
theorem B5168701 : Blo 1209422 5168701 := bstep (se 3 (by rfl) ⟨969131, by rfl⟩ : syracuseStep 5168701 = 1938263) B1938263
theorem B14728805 : Blo 1209422 14728805 := bstep (se 4 (by rfl) ⟨1380825, by rfl⟩ : syracuseStep 14728805 = 2761651) B2761651
theorem B3677849 : Blo 1209422 3677849 := bstep (se 2 (by rfl) ⟨1379193, by rfl⟩ : syracuseStep 3677849 = 2758387) B2758387
theorem B1531639 : Blo 1209422 1531639 := bstep (se 1 (by rfl) ⟨1148729, by rfl⟩ : syracuseStep 1531639 = 2297459) B2297459
theorem B3063815 : Blo 1209422 3063815 := bstep (se 1 (by rfl) ⟨2297861, by rfl⟩ : syracuseStep 3063815 = 4595723) B4595723
theorem B26173469 : Blo 1209422 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B3063865 : Blo 1209422 3063865 := bstep (se 2 (by rfl) ⟨1148949, by rfl⟩ : syracuseStep 3063865 = 2297899) B2297899
theorem B3448889 : Blo 1209422 3448889 := bstep (se 2 (by rfl) ⟨1293333, by rfl⟩ : syracuseStep 3448889 = 2586667) B2586667
theorem B8970355 : Blo 1209422 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B4087961 : Blo 1209422 4087961 := bstep (se 2 (by rfl) ⟨1532985, by rfl⟩ : syracuseStep 4087961 = 3065971) B3065971
theorem B13795595 : Blo 1209422 13795595 := bstep (se 1 (by rfl) ⟨10346696, by rfl⟩ : syracuseStep 13795595 = 20693393) B20693393
theorem B3064169 : Blo 1209422 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B6209921 : Blo 1209422 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B10338839 : Blo 1209422 10338839 := bstep (se 1 (by rfl) ⟨7754129, by rfl⟩ : syracuseStep 10338839 = 15508259) B15508259
theorem B3875759 : Blo 1209422 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B4907951 : Blo 1209422 4907951 := bstep (se 1 (by rfl) ⟨3680963, by rfl⟩ : syracuseStep 4907951 = 7361927) B7361927
theorem B121086899 : Blo 1209422 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B13083713 : Blo 1209422 13083713 := bstep (se 2 (by rfl) ⟨4906392, by rfl⟩ : syracuseStep 13083713 = 9812785) B9812785
theorem B10347587 : Blo 1209422 10347587 := bstep (se 1 (by rfl) ⟨7760690, by rfl⟩ : syracuseStep 10347587 = 15521381) B15521381
theorem B1360975 : Blo 1209422 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B9184427 : Blo 1209422 9184427 := bstep (se 1 (by rfl) ⟨6888320, by rfl⟩ : syracuseStep 9184427 = 13776641) B13776641
theorem B7750849 : Blo 1209422 7750849 := bstep (se 2 (by rfl) ⟨2906568, by rfl⟩ : syracuseStep 7750849 = 5813137) B5813137
theorem B2041031 : Blo 1209422 2041031 := bstep (se 1 (by rfl) ⟨1530773, by rfl⟩ : syracuseStep 2041031 = 3061547) B3061547
theorem B6898891 : Blo 1209422 6898891 := bstep (se 1 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 6898891 = 10348337) B10348337
theorem B4596983 : Blo 1209422 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B2041193 : Blo 1209422 2041193 := bstep (se 2 (by rfl) ⟨765447, by rfl⟩ : syracuseStep 2041193 = 1530895) B1530895
theorem B1361371 : Blo 1209422 1361371 := bstep (se 1 (by rfl) ⟨1021028, by rfl⟩ : syracuseStep 1361371 = 2042057) B2042057
theorem B37242389 : Blo 1209422 37242389 := bstep (se 6 (by rfl) ⟨872868, by rfl⟩ : syracuseStep 37242389 = 1745737) B1745737
theorem B7751207 : Blo 1209422 7751207 := bstep (se 1 (by rfl) ⟨5813405, by rfl⟩ : syracuseStep 7751207 = 11626811) B11626811
theorem B4359739 : Blo 1209422 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B9184913 : Blo 1209422 9184913 := bstep (se 2 (by rfl) ⟨3444342, by rfl⟩ : syracuseStep 9184913 = 6888685) B6888685
theorem B2721491 : Blo 1209422 2721491 := bstep (se 1 (by rfl) ⟨2041118, by rfl⟩ : syracuseStep 2721491 = 4082237) B4082237
theorem B9193175 : Blo 1209422 9193175 := bstep (se 1 (by rfl) ⟨6894881, by rfl⟩ : syracuseStep 9193175 = 13789763) B13789763
theorem B2041591 : Blo 1209422 2041591 := bstep (se 1 (by rfl) ⟨1531193, by rfl⟩ : syracuseStep 2041591 = 3062387) B3062387
theorem B39241523 : Blo 1209422 39241523 := bstep (se 1 (by rfl) ⟨29431142, by rfl⟩ : syracuseStep 39241523 = 58862285) B58862285
theorem B1722217 : Blo 1209422 1722217 := bstep (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) B1291663
theorem B1361839 : Blo 1209422 1361839 := bstep (se 1 (by rfl) ⟨1021379, by rfl⟩ : syracuseStep 1361839 = 2042759) B2042759
theorem B2041787 : Blo 1209422 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B1722331 : Blo 1209422 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B7358471 : Blo 1209422 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B2041895 : Blo 1209422 2041895 := bstep (se 1 (by rfl) ⟨1531421, by rfl⟩ : syracuseStep 2041895 = 3062843) B3062843
theorem B6891601 : Blo 1209422 6891601 := bstep (se 2 (by rfl) ⟨2584350, by rfl⟩ : syracuseStep 6891601 = 5168701) B5168701
theorem B55887965 : Blo 1209422 55887965 := bstep (se 3 (by rfl) ⟨10478993, by rfl⟩ : syracuseStep 55887965 = 20957987) B20957987
theorem B4597955 : Blo 1209422 4597955 := bstep (se 1 (by rfl) ⟨3448466, by rfl⟩ : syracuseStep 4597955 = 6896933) B6896933
theorem B2042185 : Blo 1209422 2042185 := bstep (se 2 (by rfl) ⟨765819, by rfl⟩ : syracuseStep 2042185 = 1531639) B1531639
theorem B5818711 : Blo 1209422 5818711 := bstep (se 1 (by rfl) ⟨4364033, by rfl⟩ : syracuseStep 5818711 = 8728067) B8728067
theorem B1362271 : Blo 1209422 1362271 := bstep (se 1 (by rfl) ⟨1021703, by rfl⟩ : syracuseStep 1362271 = 2043407) B2043407
theorem B2042219 : Blo 1209422 2042219 := bstep (se 1 (by rfl) ⟨1531664, by rfl⟩ : syracuseStep 2042219 = 3063329) B3063329
theorem B2451899 : Blo 1209422 2451899 := bstep (se 1 (by rfl) ⟨1838924, by rfl⟩ : syracuseStep 2451899 = 3677849) B3677849
theorem B3066407 : Blo 1209422 3066407 := bstep (se 1 (by rfl) ⟨2299805, by rfl⟩ : syracuseStep 3066407 = 4599611) B4599611
theorem B2722427 : Blo 1209422 2722427 := bstep (se 1 (by rfl) ⟨2041820, by rfl⟩ : syracuseStep 2722427 = 4083641) B4083641
theorem B4598471 : Blo 1209422 4598471 := bstep (se 1 (by rfl) ⟨3448853, by rfl⟩ : syracuseStep 4598471 = 6897707) B6897707
theorem B1362631 : Blo 1209422 1362631 := bstep (se 1 (by rfl) ⟨1021973, by rfl⟩ : syracuseStep 1362631 = 2043947) B2043947
theorem B2722553 : Blo 1209422 2722553 := bstep (se 2 (by rfl) ⟨1020957, by rfl⟩ : syracuseStep 2722553 = 2041915) B2041915
theorem B2042617 : Blo 1209422 2042617 := bstep (se 2 (by rfl) ⟨765981, by rfl⟩ : syracuseStep 2042617 = 1531963) B1531963
theorem B2329337 : Blo 1209422 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B1723231 : Blo 1209422 1723231 := bstep (se 1 (by rfl) ⟨1292423, by rfl⟩ : syracuseStep 1723231 = 2584847) B2584847
theorem B13077395 : Blo 1209422 13077395 := bstep (se 1 (by rfl) ⟨9808046, by rfl⟩ : syracuseStep 13077395 = 19616093) B19616093
theorem B4082615 : Blo 1209422 4082615 := bstep (se 1 (by rfl) ⟨3061961, by rfl⟩ : syracuseStep 4082615 = 6123923) B6123923
theorem B2722823 : Blo 1209422 2722823 := bstep (se 1 (by rfl) ⟨2042117, by rfl⟩ : syracuseStep 2722823 = 4084235) B4084235
theorem B2042887 : Blo 1209422 2042887 := bstep (se 1 (by rfl) ⟨1532165, by rfl⟩ : syracuseStep 2042887 = 3064331) B3064331
theorem B9186371 : Blo 1209422 9186371 := bstep (se 1 (by rfl) ⟨6889778, by rfl⟩ : syracuseStep 9186371 = 13779557) B13779557
theorem B2722895 : Blo 1209422 2722895 := bstep (se 1 (by rfl) ⟨2042171, by rfl⟩ : syracuseStep 2722895 = 4084343) B4084343
theorem B4910237 : Blo 1209422 4910237 := bstep (se 3 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 4910237 = 1841339) B1841339
theorem B4418959 : Blo 1209422 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B2297231 : Blo 1209422 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B2043319 : Blo 1209422 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B2485723 : Blo 1209422 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B2723291 : Blo 1209422 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B4083209 : Blo 1209422 4083209 := bstep (se 2 (by rfl) ⟨1531203, by rfl⟩ : syracuseStep 4083209 = 3062407) B3062407
theorem B1723943 : Blo 1209422 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B2043515 : Blo 1209422 2043515 := bstep (se 1 (by rfl) ⟨1532636, by rfl⟩ : syracuseStep 2043515 = 3065273) B3065273
theorem B5811851 : Blo 1209422 5811851 := bstep (se 1 (by rfl) ⟨4358888, by rfl⟩ : syracuseStep 5811851 = 8717777) B8717777
theorem B4599443 : Blo 1209422 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B1814447 : Blo 1209422 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B2723759 : Blo 1209422 2723759 := bstep (se 1 (by rfl) ⟨2042819, by rfl⟩ : syracuseStep 2723759 = 4085639) B4085639
theorem B1814537 : Blo 1209422 1814537 := bstep (se 2 (by rfl) ⟨680451, by rfl⟩ : syracuseStep 1814537 = 1360903) B1360903
theorem B2043913 : Blo 1209422 2043913 := bstep (se 2 (by rfl) ⟨766467, by rfl⟩ : syracuseStep 2043913 = 1532935) B1532935
theorem B9187343 : Blo 1209422 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B1814567 : Blo 1209422 1814567 := bstep (se 1 (by rfl) ⟨1360925, by rfl⟩ : syracuseStep 1814567 = 2721851) B2721851
theorem B1454159 : Blo 1209422 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B1724495 : Blo 1209422 1724495 := bstep (se 1 (by rfl) ⟨1293371, by rfl⟩ : syracuseStep 1724495 = 2586743) B2586743
theorem B1814651 : Blo 1209422 1814651 := bstep (se 1 (by rfl) ⟨1360988, by rfl⟩ : syracuseStep 1814651 = 2721977) B2721977
theorem B2724011 : Blo 1209422 2724011 := bstep (se 1 (by rfl) ⟨2043008, by rfl⟩ : syracuseStep 2724011 = 4086017) B4086017
theorem B2044075 : Blo 1209422 2044075 := bstep (se 1 (by rfl) ⟨1533056, by rfl⟩ : syracuseStep 2044075 = 3066113) B3066113
theorem B1814777 : Blo 1209422 1814777 := bstep (se 2 (by rfl) ⟨680541, by rfl⟩ : syracuseStep 1814777 = 1361083) B1361083
theorem B1814879 : Blo 1209422 1814879 := bstep (se 1 (by rfl) ⟨1361159, by rfl⟩ : syracuseStep 1814879 = 2722319) B2722319
theorem B4084073 : Blo 1209422 4084073 := bstep (se 2 (by rfl) ⟨1531527, by rfl⟩ : syracuseStep 4084073 = 3063055) B3063055
theorem B1814891 : Blo 1209422 1814891 := bstep (se 1 (by rfl) ⟨1361168, by rfl⟩ : syracuseStep 1814891 = 2722337) B2722337
theorem B2298287 : Blo 1209422 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B70808021 : Blo 1209422 70808021 := bstep (se 7 (by rfl) ⟨829781, by rfl⟩ : syracuseStep 70808021 = 1659563) B1659563
theorem B3494387 : Blo 1209422 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B2454023 : Blo 1209422 2454023 := bstep (se 1 (by rfl) ⟨1840517, by rfl⟩ : syracuseStep 2454023 = 3681035) B3681035
theorem B4592153 : Blo 1209422 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B9196091 : Blo 1209422 9196091 := bstep (se 1 (by rfl) ⟨6897068, by rfl⟩ : syracuseStep 9196091 = 13794137) B13794137
theorem B1815119 : Blo 1209422 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B3445345 : Blo 1209422 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B1839739 : Blo 1209422 1839739 := bstep (se 1 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 1839739 = 2759609) B2759609
theorem B5173895 : Blo 1209422 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B1815239 : Blo 1209422 1815239 := bstep (se 1 (by rfl) ⟨1361429, by rfl⟩ : syracuseStep 1815239 = 2722859) B2722859
theorem B2724551 : Blo 1209422 2724551 := bstep (se 1 (by rfl) ⟨2043413, by rfl⟩ : syracuseStep 2724551 = 4086827) B4086827
theorem B3986135 : Blo 1209422 3986135 := bstep (se 1 (by rfl) ⟨2989601, by rfl⟩ : syracuseStep 3986135 = 5979203) B5979203
theorem B6132509 : Blo 1209422 6132509 := bstep (se 3 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 6132509 = 2299691) B2299691
theorem B2298719 : Blo 1209422 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B1815401 : Blo 1209422 1815401 := bstep (se 2 (by rfl) ⟨680775, by rfl⟩ : syracuseStep 1815401 = 1361551) B1361551
theorem B1815479 : Blo 1209422 1815479 := bstep (se 1 (by rfl) ⟨1361609, by rfl⟩ : syracuseStep 1815479 = 2723219) B2723219
theorem B4084667 : Blo 1209422 4084667 := bstep (se 1 (by rfl) ⟨3063500, by rfl⟩ : syracuseStep 4084667 = 6127001) B6127001
theorem B1815515 : Blo 1209422 1815515 := bstep (se 1 (by rfl) ⟨1361636, by rfl⟩ : syracuseStep 1815515 = 2723273) B2723273
theorem B4363271 : Blo 1209422 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B9819203 : Blo 1209422 9819203 := bstep (se 1 (by rfl) ⟨7364402, by rfl⟩ : syracuseStep 9819203 = 14728805) B14728805
theorem B1209423 : Blo 1209422 1209423 := bstep (se 1 (by rfl) ⟨907067, by rfl⟩ : syracuseStep 1209423 = 1814135) B1814135
theorem B1209439 : Blo 1209422 1209439 := bstep (se 1 (by rfl) ⟨907079, by rfl⟩ : syracuseStep 1209439 = 1814159) B1814159
theorem B1209467 : Blo 1209422 1209467 := bstep (se 1 (by rfl) ⟨907100, by rfl⟩ : syracuseStep 1209467 = 1814201) B1814201
theorem B5518489 : Blo 1209422 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B1209519 : Blo 1209422 1209519 := bstep (se 1 (by rfl) ⟨907139, by rfl⟩ : syracuseStep 1209519 = 1814279) B1814279
theorem B1209543 : Blo 1209422 1209543 := bstep (se 1 (by rfl) ⟨907157, by rfl⟩ : syracuseStep 1209543 = 1814315) B1814315
theorem B1209563 : Blo 1209422 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B1209639 : Blo 1209422 1209639 := bstep (se 1 (by rfl) ⟨907229, by rfl⟩ : syracuseStep 1209639 = 1814459) B1814459
theorem B1209679 : Blo 1209422 1209679 := bstep (se 1 (by rfl) ⟨907259, by rfl⟩ : syracuseStep 1209679 = 1814519) B1814519
theorem B1209695 : Blo 1209422 1209695 := bstep (se 1 (by rfl) ⟨907271, by rfl⟩ : syracuseStep 1209695 = 1814543) B1814543
theorem B1209723 : Blo 1209422 1209723 := bstep (se 1 (by rfl) ⟨907292, by rfl⟩ : syracuseStep 1209723 = 1814585) B1814585
theorem B4904317 : Blo 1209422 4904317 := bstep (se 3 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 4904317 = 1839119) B1839119
theorem B15725987 : Blo 1209422 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B1209775 : Blo 1209422 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B1815983 : Blo 1209422 1815983 := bstep (se 1 (by rfl) ⟨1361987, by rfl⟩ : syracuseStep 1815983 = 2723975) B2723975
theorem B1209799 : Blo 1209422 1209799 := bstep (se 1 (by rfl) ⟨907349, by rfl⟩ : syracuseStep 1209799 = 1814699) B1814699
theorem B1209819 : Blo 1209422 1209819 := bstep (se 1 (by rfl) ⟨907364, by rfl⟩ : syracuseStep 1209819 = 1814729) B1814729
theorem B1816073 : Blo 1209422 1816073 := bstep (se 2 (by rfl) ⟨681027, by rfl⟩ : syracuseStep 1816073 = 1362055) B1362055
theorem B1209895 : Blo 1209422 1209895 := bstep (se 1 (by rfl) ⟨907421, by rfl⟩ : syracuseStep 1209895 = 1814843) B1814843
theorem B1816103 : Blo 1209422 1816103 := bstep (se 1 (by rfl) ⟨1362077, by rfl⟩ : syracuseStep 1816103 = 2724155) B2724155
theorem B2725415 : Blo 1209422 2725415 := bstep (se 1 (by rfl) ⟨2044061, by rfl⟩ : syracuseStep 2725415 = 4088123) B4088123
theorem B1209935 : Blo 1209422 1209935 := bstep (se 1 (by rfl) ⟨907451, by rfl⟩ : syracuseStep 1209935 = 1814903) B1814903
theorem B1209951 : Blo 1209422 1209951 := bstep (se 1 (by rfl) ⟨907463, by rfl⟩ : syracuseStep 1209951 = 1814927) B1814927
theorem B1209979 : Blo 1209422 1209979 := bstep (se 1 (by rfl) ⟨907484, by rfl⟩ : syracuseStep 1209979 = 1814969) B1814969
theorem B1816187 : Blo 1209422 1816187 := bstep (se 1 (by rfl) ⟨1362140, by rfl⟩ : syracuseStep 1816187 = 2724281) B2724281
theorem B1210031 : Blo 1209422 1210031 := bstep (se 1 (by rfl) ⟨907523, by rfl⟩ : syracuseStep 1210031 = 1815047) B1815047
theorem B15513281 : Blo 1209422 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B1210055 : Blo 1209422 1210055 := bstep (se 1 (by rfl) ⟨907541, by rfl⟩ : syracuseStep 1210055 = 1815083) B1815083
theorem B1210075 : Blo 1209422 1210075 := bstep (se 1 (by rfl) ⟨907556, by rfl⟩ : syracuseStep 1210075 = 1815113) B1815113
theorem B1816313 : Blo 1209422 1816313 := bstep (se 2 (by rfl) ⟨681117, by rfl⟩ : syracuseStep 1816313 = 1362235) B1362235
theorem B1210151 : Blo 1209422 1210151 := bstep (se 1 (by rfl) ⟨907613, by rfl⟩ : syracuseStep 1210151 = 1815227) B1815227
theorem B3061577 : Blo 1209422 3061577 := bstep (se 2 (by rfl) ⟨1148091, by rfl⟩ : syracuseStep 3061577 = 2296183) B2296183
theorem B1210191 : Blo 1209422 1210191 := bstep (se 1 (by rfl) ⟨907643, by rfl⟩ : syracuseStep 1210191 = 1815287) B1815287
theorem B1210207 : Blo 1209422 1210207 := bstep (se 1 (by rfl) ⟨907655, by rfl⟩ : syracuseStep 1210207 = 1815311) B1815311
theorem B1816415 : Blo 1209422 1816415 := bstep (se 1 (by rfl) ⟨1362311, by rfl⟩ : syracuseStep 1816415 = 2724623) B2724623
theorem B1816427 : Blo 1209422 1816427 := bstep (se 1 (by rfl) ⟨1362320, by rfl⟩ : syracuseStep 1816427 = 2724641) B2724641
theorem B1210235 : Blo 1209422 1210235 := bstep (se 1 (by rfl) ⟨907676, by rfl⟩ : syracuseStep 1210235 = 1815353) B1815353
theorem B1210287 : Blo 1209422 1210287 := bstep (se 1 (by rfl) ⟨907715, by rfl⟩ : syracuseStep 1210287 = 1815431) B1815431
theorem B1210311 : Blo 1209422 1210311 := bstep (se 1 (by rfl) ⟨907733, by rfl⟩ : syracuseStep 1210311 = 1815467) B1815467
theorem B1210331 : Blo 1209422 1210331 := bstep (se 1 (by rfl) ⟨907748, by rfl⟩ : syracuseStep 1210331 = 1815497) B1815497
theorem B3446803 : Blo 1209422 3446803 := bstep (se 1 (by rfl) ⟨2585102, by rfl⟩ : syracuseStep 3446803 = 5170205) B5170205
theorem B1210407 : Blo 1209422 1210407 := bstep (se 1 (by rfl) ⟨907805, by rfl⟩ : syracuseStep 1210407 = 1815611) B1815611
theorem B1210447 : Blo 1209422 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B1816655 : Blo 1209422 1816655 := bstep (se 1 (by rfl) ⟨1362491, by rfl⟩ : syracuseStep 1816655 = 2724983) B2724983
theorem B14727257 : Blo 1209422 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B1210463 : Blo 1209422 1210463 := bstep (se 1 (by rfl) ⟨907847, by rfl⟩ : syracuseStep 1210463 = 1815695) B1815695
theorem B4593779 : Blo 1209422 4593779 := bstep (se 1 (by rfl) ⟨3445334, by rfl⟩ : syracuseStep 4593779 = 6890669) B6890669
theorem B1210491 : Blo 1209422 1210491 := bstep (se 1 (by rfl) ⟨907868, by rfl⟩ : syracuseStep 1210491 = 1815737) B1815737
theorem B1210543 : Blo 1209422 1210543 := bstep (se 1 (by rfl) ⟨907907, by rfl⟩ : syracuseStep 1210543 = 1815815) B1815815
theorem B1210567 : Blo 1209422 1210567 := bstep (se 1 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 1210567 = 1815851) B1815851
theorem B1816775 : Blo 1209422 1816775 := bstep (se 1 (by rfl) ⟨1362581, by rfl⟩ : syracuseStep 1816775 = 2725163) B2725163
theorem B1210587 : Blo 1209422 1210587 := bstep (se 1 (by rfl) ⟨907940, by rfl⟩ : syracuseStep 1210587 = 1815881) B1815881
theorem B3447031 : Blo 1209422 3447031 := bstep (se 1 (by rfl) ⟨2585273, by rfl⟩ : syracuseStep 3447031 = 5170547) B5170547
theorem B1210663 : Blo 1209422 1210663 := bstep (se 1 (by rfl) ⟨907997, by rfl⟩ : syracuseStep 1210663 = 1815995) B1815995
theorem B1210703 : Blo 1209422 1210703 := bstep (se 1 (by rfl) ⟨908027, by rfl⟩ : syracuseStep 1210703 = 1816055) B1816055
theorem B1210719 : Blo 1209422 1210719 := bstep (se 1 (by rfl) ⟨908039, by rfl⟩ : syracuseStep 1210719 = 1816079) B1816079
theorem B1816937 : Blo 1209422 1816937 := bstep (se 2 (by rfl) ⟨681351, by rfl⟩ : syracuseStep 1816937 = 1362703) B1362703
theorem B1210747 : Blo 1209422 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B1210799 : Blo 1209422 1210799 := bstep (se 1 (by rfl) ⟨908099, by rfl⟩ : syracuseStep 1210799 = 1816199) B1816199
theorem B1817015 : Blo 1209422 1817015 := bstep (se 1 (by rfl) ⟨1362761, by rfl⟩ : syracuseStep 1817015 = 2725523) B2725523
theorem B1210823 : Blo 1209422 1210823 := bstep (se 1 (by rfl) ⟨908117, by rfl⟩ : syracuseStep 1210823 = 1816235) B1816235
theorem B1210843 : Blo 1209422 1210843 := bstep (se 1 (by rfl) ⟨908132, by rfl⟩ : syracuseStep 1210843 = 1816265) B1816265
theorem B1817051 : Blo 1209422 1817051 := bstep (se 1 (by rfl) ⟨1362788, by rfl⟩ : syracuseStep 1817051 = 2725577) B2725577
theorem B3447305 : Blo 1209422 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B1210919 : Blo 1209422 1210919 := bstep (se 1 (by rfl) ⟨908189, by rfl⟩ : syracuseStep 1210919 = 1816379) B1816379
theorem B1210959 : Blo 1209422 1210959 := bstep (se 1 (by rfl) ⟨908219, by rfl⟩ : syracuseStep 1210959 = 1816439) B1816439
theorem B1210975 : Blo 1209422 1210975 := bstep (se 1 (by rfl) ⟨908231, by rfl⟩ : syracuseStep 1210975 = 1816463) B1816463
theorem B4086395 : Blo 1209422 4086395 := bstep (se 1 (by rfl) ⟨3064796, by rfl⟩ : syracuseStep 4086395 = 6129593) B6129593
theorem B1211003 : Blo 1209422 1211003 := bstep (se 1 (by rfl) ⟨908252, by rfl⟩ : syracuseStep 1211003 = 1816505) B1816505
theorem B1211055 : Blo 1209422 1211055 := bstep (se 1 (by rfl) ⟨908291, by rfl⟩ : syracuseStep 1211055 = 1816583) B1816583
theorem B1211079 : Blo 1209422 1211079 := bstep (se 1 (by rfl) ⟨908309, by rfl⟩ : syracuseStep 1211079 = 1816619) B1816619
theorem B1211099 : Blo 1209422 1211099 := bstep (se 1 (by rfl) ⟨908324, by rfl⟩ : syracuseStep 1211099 = 1816649) B1816649
theorem B4086557 : Blo 1209422 4086557 := bstep (se 3 (by rfl) ⟨766229, by rfl⟩ : syracuseStep 4086557 = 1532459) B1532459
theorem B1211175 : Blo 1209422 1211175 := bstep (se 1 (by rfl) ⟨908381, by rfl⟩ : syracuseStep 1211175 = 1816763) B1816763
theorem B1211215 : Blo 1209422 1211215 := bstep (se 1 (by rfl) ⟨908411, by rfl⟩ : syracuseStep 1211215 = 1816823) B1816823
theorem B3447647 : Blo 1209422 3447647 := bstep (se 1 (by rfl) ⟨2585735, by rfl⟩ : syracuseStep 3447647 = 5171471) B5171471
theorem B1211231 : Blo 1209422 1211231 := bstep (se 1 (by rfl) ⟨908423, by rfl⟩ : syracuseStep 1211231 = 1816847) B1816847
theorem B1211259 : Blo 1209422 1211259 := bstep (se 1 (by rfl) ⟨908444, by rfl⟩ : syracuseStep 1211259 = 1816889) B1816889
theorem B1211311 : Blo 1209422 1211311 := bstep (se 1 (by rfl) ⟨908483, by rfl⟩ : syracuseStep 1211311 = 1816967) B1816967
theorem B3062711 : Blo 1209422 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B1940411 : Blo 1209422 1940411 := bstep (se 1 (by rfl) ⟨1455308, by rfl⟩ : syracuseStep 1940411 = 2910617) B2910617
theorem B1211335 : Blo 1209422 1211335 := bstep (se 1 (by rfl) ⟨908501, by rfl⟩ : syracuseStep 1211335 = 1817003) B1817003
theorem B1211355 : Blo 1209422 1211355 := bstep (se 1 (by rfl) ⟨908516, by rfl⟩ : syracuseStep 1211355 = 1817033) B1817033
theorem B24853547 : Blo 1209422 24853547 := bstep (se 1 (by rfl) ⟨18640160, by rfl⟩ : syracuseStep 24853547 = 37280321) B37280321
theorem B4906099 : Blo 1209422 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B6126839 : Blo 1209422 6126839 := bstep (se 1 (by rfl) ⟨4595129, by rfl⟩ : syracuseStep 6126839 = 9190259) B9190259
theorem B9190745 : Blo 1209422 9190745 := bstep (se 2 (by rfl) ⟨3446529, by rfl⟩ : syracuseStep 9190745 = 6893059) B6893059
theorem B4595069 : Blo 1209422 4595069 := bstep (se 3 (by rfl) ⟨861575, by rfl⟩ : syracuseStep 4595069 = 1723151) B1723151
theorem B1965487 : Blo 1209422 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B4087259 : Blo 1209422 4087259 := bstep (se 1 (by rfl) ⟨3065444, by rfl⟩ : syracuseStep 4087259 = 6130889) B6130889
theorem B3448307 : Blo 1209422 3448307 := bstep (se 1 (by rfl) ⟨2586230, by rfl⟩ : syracuseStep 3448307 = 5172461) B5172461
theorem B11640307 : Blo 1209422 11640307 := bstep (se 1 (by rfl) ⟨8730230, by rfl⟩ : syracuseStep 11640307 = 17460461) B17460461
theorem B5979793 : Blo 1209422 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B6127325 : Blo 1209422 6127325 := bstep (se 3 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 6127325 = 2297747) B2297747
theorem B3448649 : Blo 1209422 3448649 := bstep (se 2 (by rfl) ⟨1293243, by rfl⟩ : syracuseStep 3448649 = 2586487) B2586487
theorem B3448763 : Blo 1209422 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B1531867 : Blo 1209422 1531867 := bstep (se 1 (by rfl) ⟨1148900, by rfl⟩ : syracuseStep 1531867 = 2297801) B2297801
theorem B4595737 : Blo 1209422 4595737 := bstep (se 2 (by rfl) ⟨1723401, by rfl⟩ : syracuseStep 4595737 = 3446803) B3446803
theorem B69795917 : Blo 1209422 69795917 := bstep (se 3 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 69795917 = 26173469) B26173469
theorem B11960473 : Blo 1209422 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B1532191 : Blo 1209422 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B4596041 : Blo 1209422 4596041 := bstep (se 2 (by rfl) ⟨1723515, by rfl⟩ : syracuseStep 4596041 = 3447031) B3447031
theorem B7758281 : Blo 1209422 7758281 := bstep (se 2 (by rfl) ⟨2909355, by rfl⟩ : syracuseStep 7758281 = 5818711) B5818711
theorem B4088339 : Blo 1209422 4088339 := bstep (se 1 (by rfl) ⟨3066254, by rfl⟩ : syracuseStep 4088339 = 6132509) B6132509
theorem B26165861 : Blo 1209422 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B80724599 : Blo 1209422 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B2908847 : Blo 1209422 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B6898391 : Blo 1209422 6898391 := bstep (se 1 (by rfl) ⟨5173793, by rfl⟩ : syracuseStep 6898391 = 10347587) B10347587
theorem B1360687 : Blo 1209422 1360687 := bstep (se 1 (by rfl) ⟨1020515, by rfl⟩ : syracuseStep 1360687 = 2041031) B2041031
theorem B3064655 : Blo 1209422 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B1360795 : Blo 1209422 1360795 := bstep (se 1 (by rfl) ⟨1020596, by rfl⟩ : syracuseStep 1360795 = 2041193) B2041193
theorem B6128783 : Blo 1209422 6128783 := bstep (se 1 (by rfl) ⟨4596587, by rfl⟩ : syracuseStep 6128783 = 9193175) B9193175
theorem B2041051 : Blo 1209422 2041051 := bstep (se 1 (by rfl) ⟨1530788, by rfl⟩ : syracuseStep 2041051 = 3061577) B3061577
theorem B1361191 : Blo 1209422 1361191 := bstep (se 1 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 1361191 = 2041787) B2041787
theorem B1361263 : Blo 1209422 1361263 := bstep (se 1 (by rfl) ⟨1020947, by rfl⟩ : syracuseStep 1361263 = 2041895) B2041895
theorem B99313037 : Blo 1209422 99313037 := bstep (se 3 (by rfl) ⟨18621194, by rfl⟩ : syracuseStep 99313037 = 37242389) B37242389
theorem B37258643 : Blo 1209422 37258643 := bstep (se 1 (by rfl) ⟨27943982, by rfl⟩ : syracuseStep 37258643 = 55887965) B55887965
theorem B4597181 : Blo 1209422 4597181 := bstep (se 3 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 4597181 = 1723943) B1723943
theorem B3065303 : Blo 1209422 3065303 := bstep (se 1 (by rfl) ⟨2298977, by rfl⟩ : syracuseStep 3065303 = 4597955) B4597955
theorem B7357985 : Blo 1209422 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B1361479 : Blo 1209422 1361479 := bstep (se 1 (by rfl) ⟨1021109, by rfl⟩ : syracuseStep 1361479 = 2042219) B2042219
theorem B13797053 : Blo 1209422 13797053 := bstep (se 3 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 13797053 = 5173895) B5173895
theorem B3065647 : Blo 1209422 3065647 := bstep (se 1 (by rfl) ⟨2299235, by rfl⟩ : syracuseStep 3065647 = 4598471) B4598471
theorem B6539089 : Blo 1209422 6539089 := bstep (se 2 (by rfl) ⟨2452158, by rfl⟩ : syracuseStep 6539089 = 4904317) B4904317
theorem B5891945 : Blo 1209422 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B8718263 : Blo 1209422 8718263 := bstep (se 1 (by rfl) ⟨6538697, by rfl⟩ : syracuseStep 8718263 = 13077395) B13077395
theorem B2721743 : Blo 1209422 2721743 := bstep (se 1 (by rfl) ⟨2041307, by rfl⟩ : syracuseStep 2721743 = 4082615) B4082615
theorem B2041807 : Blo 1209422 2041807 := bstep (se 1 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 2041807 = 3062711) B3062711
theorem B6211565 : Blo 1209422 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B7973057 : Blo 1209422 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B6129917 : Blo 1209422 6129917 := bstep (se 3 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 6129917 = 2298719) B2298719
theorem B2722121 : Blo 1209422 2722121 := bstep (se 2 (by rfl) ⟨1020795, by rfl⟩ : syracuseStep 2722121 = 2041591) B2041591
theorem B2722139 : Blo 1209422 2722139 := bstep (se 1 (by rfl) ⟨2041604, by rfl⟩ : syracuseStep 2722139 = 4083209) B4083209
theorem B1362343 : Blo 1209422 1362343 := bstep (se 1 (by rfl) ⟨1021757, by rfl⟩ : syracuseStep 1362343 = 2043515) B2043515
theorem B3066295 : Blo 1209422 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B2296289 : Blo 1209422 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B2296441 : Blo 1209422 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B2042489 : Blo 1209422 2042489 := bstep (se 2 (by rfl) ⟨765933, by rfl⟩ : syracuseStep 2042489 = 1531867) B1531867
theorem B2042543 : Blo 1209422 2042543 := bstep (se 1 (by rfl) ⟨1531907, by rfl⟩ : syracuseStep 2042543 = 3063815) B3063815
theorem B26184541 : Blo 1209422 26184541 := bstep (se 3 (by rfl) ⟨4909601, by rfl⟩ : syracuseStep 26184541 = 9819203) B9819203
theorem B3877757 : Blo 1209422 3877757 := bstep (se 3 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 3877757 = 1454159) B1454159
theorem B4598653 : Blo 1209422 4598653 := bstep (se 3 (by rfl) ⟨862247, by rfl⟩ : syracuseStep 4598653 = 1724495) B1724495
theorem B2722715 : Blo 1209422 2722715 := bstep (se 1 (by rfl) ⟨2042036, by rfl⟩ : syracuseStep 2722715 = 4084073) B4084073
theorem B2042779 : Blo 1209422 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B4139947 : Blo 1209422 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B47205347 : Blo 1209422 47205347 := bstep (se 1 (by rfl) ⟨35404010, by rfl⟩ : syracuseStep 47205347 = 70808021) B70808021
theorem B2329591 : Blo 1209422 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B6892559 : Blo 1209422 6892559 := bstep (se 1 (by rfl) ⟨5169419, by rfl⟩ : syracuseStep 6892559 = 10338839) B10338839
theorem B6130727 : Blo 1209422 6130727 := bstep (se 1 (by rfl) ⟨4598045, by rfl⟩ : syracuseStep 6130727 = 9196091) B9196091
theorem B2722913 : Blo 1209422 2722913 := bstep (se 2 (by rfl) ⟨1021092, by rfl⟩ : syracuseStep 2722913 = 2042185) B2042185
theorem B2657423 : Blo 1209422 2657423 := bstep (se 1 (by rfl) ⟨1993067, by rfl⟩ : syracuseStep 2657423 = 3986135) B3986135
theorem B2583839 : Blo 1209422 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B3271967 : Blo 1209422 3271967 := bstep (se 1 (by rfl) ⟨2453975, by rfl⟩ : syracuseStep 3271967 = 4907951) B4907951
theorem B2723111 : Blo 1209422 2723111 := bstep (se 1 (by rfl) ⟨2042333, by rfl⟩ : syracuseStep 2723111 = 4084667) B4084667
theorem B6122951 : Blo 1209422 6122951 := bstep (se 1 (by rfl) ⟨4592213, by rfl⟩ : syracuseStep 6122951 = 9184427) B9184427
theorem B2452985 : Blo 1209422 2452985 := bstep (se 2 (by rfl) ⟨919869, by rfl⟩ : syracuseStep 2452985 = 1839739) B1839739
theorem B2723489 : Blo 1209422 2723489 := bstep (se 2 (by rfl) ⟨1021308, by rfl⟩ : syracuseStep 2723489 = 2042617) B2042617
theorem B6123275 : Blo 1209422 6123275 := bstep (se 1 (by rfl) ⟨4592456, by rfl⟩ : syracuseStep 6123275 = 9184913) B9184913
theorem B2297641 : Blo 1209422 2297641 := bstep (se 2 (by rfl) ⟨861615, by rfl⟩ : syracuseStep 2297641 = 1723231) B1723231
theorem B10342187 : Blo 1209422 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B1814327 : Blo 1209422 1814327 := bstep (se 1 (by rfl) ⟨1360745, by rfl⟩ : syracuseStep 1814327 = 2721491) B2721491
theorem B26161015 : Blo 1209422 26161015 := bstep (se 1 (by rfl) ⟨19620761, by rfl⟩ : syracuseStep 26161015 = 39241523) B39241523
theorem B2723849 : Blo 1209422 2723849 := bstep (se 2 (by rfl) ⟨1021443, by rfl⟩ : syracuseStep 2723849 = 2042887) B2042887
theorem B9818171 : Blo 1209422 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B1814633 : Blo 1209422 1814633 := bstep (se 2 (by rfl) ⟨680487, by rfl⟩ : syracuseStep 1814633 = 1360975) B1360975
theorem B10334465 : Blo 1209422 10334465 := bstep (se 2 (by rfl) ⟨3875424, by rfl⟩ : syracuseStep 10334465 = 7750849) B7750849
theorem B1634599 : Blo 1209422 1634599 := bstep (se 1 (by rfl) ⟨1225949, by rfl⟩ : syracuseStep 1634599 = 2451899) B2451899
theorem B2298203 : Blo 1209422 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B2044271 : Blo 1209422 2044271 := bstep (se 1 (by rfl) ⟨1533203, by rfl⟩ : syracuseStep 2044271 = 3066407) B3066407
theorem B1814951 : Blo 1209422 1814951 := bstep (se 1 (by rfl) ⟨1361213, by rfl⟩ : syracuseStep 1814951 = 2722427) B2722427
theorem B2724263 : Blo 1209422 2724263 := bstep (se 1 (by rfl) ⟨2043197, by rfl⟩ : syracuseStep 2724263 = 4086395) B4086395
theorem B1815035 : Blo 1209422 1815035 := bstep (se 1 (by rfl) ⟨1361276, by rfl⟩ : syracuseStep 1815035 = 2722553) B2722553
theorem B2724371 : Blo 1209422 2724371 := bstep (se 1 (by rfl) ⟨2043278, by rfl⟩ : syracuseStep 2724371 = 4086557) B4086557
theorem B2298431 : Blo 1209422 2298431 := bstep (se 1 (by rfl) ⟨1723823, by rfl⟩ : syracuseStep 2298431 = 3447647) B3447647
theorem B2724425 : Blo 1209422 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B3314297 : Blo 1209422 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B1815161 : Blo 1209422 1815161 := bstep (se 2 (by rfl) ⟨680685, by rfl⟩ : syracuseStep 1815161 = 1361371) B1361371
theorem B15520409 : Blo 1209422 15520409 := bstep (se 2 (by rfl) ⟨5820153, by rfl⟩ : syracuseStep 15520409 = 11640307) B11640307
theorem B1815215 : Blo 1209422 1815215 := bstep (se 1 (by rfl) ⟨1361411, by rfl⟩ : syracuseStep 1815215 = 2722823) B2722823
theorem B16569031 : Blo 1209422 16569031 := bstep (se 1 (by rfl) ⟨12426773, by rfl⟩ : syracuseStep 16569031 = 24853547) B24853547
theorem B6124247 : Blo 1209422 6124247 := bstep (se 1 (by rfl) ⟨4593185, by rfl⟩ : syracuseStep 6124247 = 9186371) B9186371
theorem B1815263 : Blo 1209422 1815263 := bstep (se 1 (by rfl) ⟨1361447, by rfl⟩ : syracuseStep 1815263 = 2722895) B2722895
theorem B5812985 : Blo 1209422 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B3273491 : Blo 1209422 3273491 := bstep (se 1 (by rfl) ⟨2455118, by rfl⟩ : syracuseStep 3273491 = 4910237) B4910237
theorem B4084559 : Blo 1209422 4084559 := bstep (se 1 (by rfl) ⟨3063419, by rfl⟩ : syracuseStep 4084559 = 6126839) B6126839
theorem B1815527 : Blo 1209422 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B2724839 : Blo 1209422 2724839 := bstep (se 1 (by rfl) ⟨2043629, by rfl⟩ : syracuseStep 2724839 = 4087259) B4087259
theorem B2298871 : Blo 1209422 2298871 := bstep (se 1 (by rfl) ⟨1724153, by rfl⟩ : syracuseStep 2298871 = 3448307) B3448307
theorem B4084883 : Blo 1209422 4084883 := bstep (se 1 (by rfl) ⟨3063662, by rfl⟩ : syracuseStep 4084883 = 6127325) B6127325
theorem B2299099 : Blo 1209422 2299099 := bstep (se 1 (by rfl) ⟨1724324, by rfl⟩ : syracuseStep 2299099 = 3448649) B3448649
theorem B1815785 : Blo 1209422 1815785 := bstep (se 2 (by rfl) ⟨680919, by rfl⟩ : syracuseStep 1815785 = 1361839) B1361839
theorem B1209631 : Blo 1209422 1209631 := bstep (se 1 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 1209631 = 1814447) B1814447
theorem B1815839 : Blo 1209422 1815839 := bstep (se 1 (by rfl) ⟨1361879, by rfl⟩ : syracuseStep 1815839 = 2723759) B2723759
theorem B2299175 : Blo 1209422 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B1209691 : Blo 1209422 1209691 := bstep (se 1 (by rfl) ⟨907268, by rfl⟩ : syracuseStep 1209691 = 1814537) B1814537
theorem B6124895 : Blo 1209422 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B2725217 : Blo 1209422 2725217 := bstep (se 2 (by rfl) ⟨1021956, by rfl⟩ : syracuseStep 2725217 = 2043913) B2043913
theorem B1209711 : Blo 1209422 1209711 := bstep (se 1 (by rfl) ⟨907283, by rfl⟩ : syracuseStep 1209711 = 1814567) B1814567
theorem B2299259 : Blo 1209422 2299259 := bstep (se 1 (by rfl) ⟨1724444, by rfl⟩ : syracuseStep 2299259 = 3448889) B3448889
theorem B4085153 : Blo 1209422 4085153 := bstep (se 2 (by rfl) ⟨1531932, by rfl⟩ : syracuseStep 4085153 = 3063865) B3063865
theorem B1209767 : Blo 1209422 1209767 := bstep (se 1 (by rfl) ⟨907325, by rfl⟩ : syracuseStep 1209767 = 1814651) B1814651
theorem B2725307 : Blo 1209422 2725307 := bstep (se 1 (by rfl) ⟨2043980, by rfl⟩ : syracuseStep 2725307 = 4087961) B4087961
theorem B9188801 : Blo 1209422 9188801 := bstep (se 2 (by rfl) ⟨3445800, by rfl⟩ : syracuseStep 9188801 = 6891601) B6891601
theorem B1816007 : Blo 1209422 1816007 := bstep (se 1 (by rfl) ⟨1362005, by rfl⟩ : syracuseStep 1816007 = 2724011) B2724011
theorem B1209851 : Blo 1209422 1209851 := bstep (se 1 (by rfl) ⟨907388, by rfl⟩ : syracuseStep 1209851 = 1814777) B1814777
theorem B9197063 : Blo 1209422 9197063 := bstep (se 1 (by rfl) ⟨6897797, by rfl⟩ : syracuseStep 9197063 = 13795595) B13795595
theorem B2725433 : Blo 1209422 2725433 := bstep (se 2 (by rfl) ⟨1022037, by rfl⟩ : syracuseStep 2725433 = 2044075) B2044075
theorem B1209919 : Blo 1209422 1209919 := bstep (se 1 (by rfl) ⟨907439, by rfl⟩ : syracuseStep 1209919 = 1814879) B1814879
theorem B1209927 : Blo 1209422 1209927 := bstep (se 1 (by rfl) ⟨907445, by rfl⟩ : syracuseStep 1209927 = 1814891) B1814891
theorem B3061435 : Blo 1209422 3061435 := bstep (se 1 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 3061435 = 4592153) B4592153
theorem B1210079 : Blo 1209422 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B1816361 : Blo 1209422 1816361 := bstep (se 2 (by rfl) ⟨681135, by rfl⟩ : syracuseStep 1816361 = 1362271) B1362271
theorem B1210159 : Blo 1209422 1210159 := bstep (se 1 (by rfl) ⟨907619, by rfl⟩ : syracuseStep 1210159 = 1815239) B1815239
theorem B1816367 : Blo 1209422 1816367 := bstep (se 1 (by rfl) ⟨1362275, by rfl⟩ : syracuseStep 1816367 = 2724551) B2724551
theorem B1210267 : Blo 1209422 1210267 := bstep (se 1 (by rfl) ⟨907700, by rfl⟩ : syracuseStep 1210267 = 1815401) B1815401
theorem B1210319 : Blo 1209422 1210319 := bstep (se 1 (by rfl) ⟨907739, by rfl⟩ : syracuseStep 1210319 = 1815479) B1815479
theorem B1210343 : Blo 1209422 1210343 := bstep (se 1 (by rfl) ⟨907757, by rfl⟩ : syracuseStep 1210343 = 1815515) B1815515
theorem B8722475 : Blo 1209422 8722475 := bstep (se 1 (by rfl) ⟨6541856, by rfl⟩ : syracuseStep 8722475 = 13083713) B13083713
theorem B4593793 : Blo 1209422 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B1816841 : Blo 1209422 1816841 := bstep (se 2 (by rfl) ⟨681315, by rfl⟩ : syracuseStep 1816841 = 1362631) B1362631
theorem B10483991 : Blo 1209422 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B1210655 : Blo 1209422 1210655 := bstep (se 1 (by rfl) ⟨907991, by rfl⟩ : syracuseStep 1210655 = 1815983) B1815983
theorem B1210715 : Blo 1209422 1210715 := bstep (se 1 (by rfl) ⟨908036, by rfl⟩ : syracuseStep 1210715 = 1816073) B1816073
theorem B5167471 : Blo 1209422 5167471 := bstep (se 1 (by rfl) ⟨3875603, by rfl⟩ : syracuseStep 5167471 = 7751207) B7751207
theorem B1210735 : Blo 1209422 1210735 := bstep (se 1 (by rfl) ⟨908051, by rfl⟩ : syracuseStep 1210735 = 1816103) B1816103
theorem B1816943 : Blo 1209422 1816943 := bstep (se 1 (by rfl) ⟨1362707, by rfl⟩ : syracuseStep 1816943 = 2725415) B2725415
theorem B1210791 : Blo 1209422 1210791 := bstep (se 1 (by rfl) ⟨908093, by rfl⟩ : syracuseStep 1210791 = 1816187) B1816187
theorem B1210875 : Blo 1209422 1210875 := bstep (se 1 (by rfl) ⟨908156, by rfl⟩ : syracuseStep 1210875 = 1816313) B1816313
theorem B1210943 : Blo 1209422 1210943 := bstep (se 1 (by rfl) ⟨908207, by rfl⟩ : syracuseStep 1210943 = 1816415) B1816415
theorem B1210951 : Blo 1209422 1210951 := bstep (se 1 (by rfl) ⟨908213, by rfl⟩ : syracuseStep 1210951 = 1816427) B1816427
theorem B4905647 : Blo 1209422 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B6544061 : Blo 1209422 6544061 := bstep (se 3 (by rfl) ⟨1227011, by rfl⟩ : syracuseStep 6544061 = 2454023) B2454023
theorem B1211103 : Blo 1209422 1211103 := bstep (se 1 (by rfl) ⟨908327, by rfl⟩ : syracuseStep 1211103 = 1816655) B1816655
theorem B3062519 : Blo 1209422 3062519 := bstep (se 1 (by rfl) ⟨2296889, by rfl⟩ : syracuseStep 3062519 = 4593779) B4593779
theorem B1211183 : Blo 1209422 1211183 := bstep (se 1 (by rfl) ⟨908387, by rfl⟩ : syracuseStep 1211183 = 1816775) B1816775
theorem B1211291 : Blo 1209422 1211291 := bstep (se 1 (by rfl) ⟨908468, by rfl⟩ : syracuseStep 1211291 = 1816937) B1816937
theorem B9198521 : Blo 1209422 9198521 := bstep (se 2 (by rfl) ⟨3449445, by rfl⟩ : syracuseStep 9198521 = 6898891) B6898891
theorem B1211343 : Blo 1209422 1211343 := bstep (se 1 (by rfl) ⟨908507, by rfl⟩ : syracuseStep 1211343 = 1817015) B1817015
theorem B1211367 : Blo 1209422 1211367 := bstep (se 1 (by rfl) ⟨908525, by rfl⟩ : syracuseStep 1211367 = 1817051) B1817051
theorem B2620649 : Blo 1209422 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B1293607 : Blo 1209422 1293607 := bstep (se 1 (by rfl) ⟨970205, by rfl⟩ : syracuseStep 1293607 = 1940411) B1940411
theorem B6127163 : Blo 1209422 6127163 := bstep (se 1 (by rfl) ⟨4595372, by rfl⟩ : syracuseStep 6127163 = 9190745) B9190745
theorem B3063379 : Blo 1209422 3063379 := bstep (se 1 (by rfl) ⟨2297534, by rfl⟩ : syracuseStep 3063379 = 4595069) B4595069
theorem B1531487 : Blo 1209422 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B3874567 : Blo 1209422 3874567 := bstep (se 1 (by rfl) ⟨2905925, by rfl⟩ : syracuseStep 3874567 = 5811851) B5811851
theorem B6127649 : Blo 1209422 6127649 := bstep (se 2 (by rfl) ⟨2297868, by rfl⟩ : syracuseStep 6127649 = 4595737) B4595737
theorem B6545447 : Blo 1209422 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B46530611 : Blo 1209422 46530611 := bstep (se 1 (by rfl) ⟨34897958, by rfl⟩ : syracuseStep 46530611 = 69795917) B69795917
theorem B6889643 : Blo 1209422 6889643 := bstep (se 1 (by rfl) ⟨5167232, by rfl⟩ : syracuseStep 6889643 = 10334465) B10334465
theorem B3064027 : Blo 1209422 3064027 := bstep (se 1 (by rfl) ⟨2298020, by rfl⟩ : syracuseStep 3064027 = 4596041) B4596041
theorem B1532135 : Blo 1209422 1532135 := bstep (se 1 (by rfl) ⟨1149101, by rfl⟩ : syracuseStep 1532135 = 2298203) B2298203
theorem B7086461 : Blo 1209422 7086461 := bstep (se 3 (by rfl) ⟨1328711, by rfl⟩ : syracuseStep 7086461 = 2657423) B2657423
theorem B1532287 : Blo 1209422 1532287 := bstep (se 1 (by rfl) ⟨1149215, by rfl⟩ : syracuseStep 1532287 = 2298431) B2298431
theorem B10346939 : Blo 1209422 10346939 := bstep (se 1 (by rfl) ⟨7760204, by rfl⟩ : syracuseStep 10346939 = 15520409) B15520409
theorem B6889961 : Blo 1209422 6889961 := bstep (se 2 (by rfl) ⟨2583735, by rfl⟩ : syracuseStep 6889961 = 5167471) B5167471
theorem B3875323 : Blo 1209422 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B4088393 : Blo 1209422 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B1532783 : Blo 1209422 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B1532839 : Blo 1209422 1532839 := bstep (se 1 (by rfl) ⟨1149629, by rfl⟩ : syracuseStep 1532839 = 2299259) B2299259
theorem B66208691 : Blo 1209422 66208691 := bstep (se 1 (by rfl) ⟨49656518, by rfl⟩ : syracuseStep 66208691 = 99313037) B99313037
theorem B3064787 : Blo 1209422 3064787 := bstep (se 1 (by rfl) ⟨2298590, by rfl⟩ : syracuseStep 3064787 = 4597181) B4597181
theorem B3106121 : Blo 1209422 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B3065161 : Blo 1209422 3065161 := bstep (se 2 (by rfl) ⟨1149435, by rfl⟩ : syracuseStep 3065161 = 2298871) B2298871
theorem B6989327 : Blo 1209422 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B8717861 : Blo 1209422 8717861 := bstep (se 4 (by rfl) ⟨817299, by rfl⟩ : syracuseStep 8717861 = 1634599) B1634599
theorem B2721401 : Blo 1209422 2721401 := bstep (se 2 (by rfl) ⟨1020525, by rfl⟩ : syracuseStep 2721401 = 2041051) B2041051
theorem B3065465 : Blo 1209422 3065465 := bstep (se 2 (by rfl) ⟨1149549, by rfl⟩ : syracuseStep 3065465 = 2299099) B2299099
theorem B111814357 : Blo 1209422 111814357 := bstep (se 7 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 111814357 = 2620649) B2620649
theorem B1361659 : Blo 1209422 1361659 := bstep (se 1 (by rfl) ⟨1021244, by rfl⟩ : syracuseStep 1361659 = 2042489) B2042489
theorem B3270431 : Blo 1209422 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B1361695 : Blo 1209422 1361695 := bstep (se 1 (by rfl) ⟨1021271, by rfl⟩ : syracuseStep 1361695 = 2042543) B2042543
theorem B2041679 : Blo 1209422 2041679 := bstep (se 1 (by rfl) ⟨1531259, by rfl⟩ : syracuseStep 2041679 = 3062519) B3062519
theorem B1722559 : Blo 1209422 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B2181311 : Blo 1209422 2181311 := bstep (se 1 (by rfl) ⟨1635983, by rfl⟩ : syracuseStep 2181311 = 3271967) B3271967
theorem B4081913 : Blo 1209422 4081913 := bstep (se 2 (by rfl) ⟨1530717, by rfl⟩ : syracuseStep 4081913 = 3061435) B3061435
theorem B4081967 : Blo 1209422 4081967 := bstep (se 1 (by rfl) ⟨3061475, by rfl⟩ : syracuseStep 4081967 = 6122951) B6122951
theorem B8718785 : Blo 1209422 8718785 := bstep (se 2 (by rfl) ⟨3269544, by rfl⟩ : syracuseStep 8718785 = 6539089) B6539089
theorem B4082183 : Blo 1209422 4082183 := bstep (se 1 (by rfl) ⟨3061637, by rfl⟩ : syracuseStep 4082183 = 6123275) B6123275
theorem B125880925 : Blo 1209422 125880925 := bstep (se 3 (by rfl) ⟨23602673, by rfl⟩ : syracuseStep 125880925 = 47205347) B47205347
theorem B2722409 : Blo 1209422 2722409 := bstep (se 2 (by rfl) ⟨1020903, by rfl⟩ : syracuseStep 2722409 = 2041807) B2041807
theorem B1362847 : Blo 1209422 1362847 := bstep (se 1 (by rfl) ⟨1022135, by rfl⟩ : syracuseStep 1362847 = 2044271) B2044271
theorem B5172187 : Blo 1209422 5172187 := bstep (se 1 (by rfl) ⟨3879140, by rfl⟩ : syracuseStep 5172187 = 7758281) B7758281
theorem B2042921 : Blo 1209422 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B17443907 : Blo 1209422 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B53816399 : Blo 1209422 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B4082831 : Blo 1209422 4082831 := bstep (se 1 (by rfl) ⟨3062123, by rfl⟩ : syracuseStep 4082831 = 6124247) B6124247
theorem B4598927 : Blo 1209422 4598927 := bstep (se 1 (by rfl) ⟨3449195, by rfl⟩ : syracuseStep 4598927 = 6898391) B6898391
theorem B2723039 : Blo 1209422 2723039 := bstep (se 1 (by rfl) ⟨2042279, by rfl⟩ : syracuseStep 2723039 = 4084559) B4084559
theorem B2043103 : Blo 1209422 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B2723255 : Blo 1209422 2723255 := bstep (se 1 (by rfl) ⟨2042441, by rfl⟩ : syracuseStep 2723255 = 4084883) B4084883
theorem B4083263 : Blo 1209422 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B2723435 : Blo 1209422 2723435 := bstep (se 1 (by rfl) ⟨2042576, by rfl⟩ : syracuseStep 2723435 = 4085153) B4085153
theorem B2043535 : Blo 1209422 2043535 := bstep (se 1 (by rfl) ⟨1532651, by rfl⟩ : syracuseStep 2043535 = 3065303) B3065303
theorem B6131375 : Blo 1209422 6131375 := bstep (se 1 (by rfl) ⟨4598531, by rfl⟩ : syracuseStep 6131375 = 9197063) B9197063
theorem B99356381 : Blo 1209422 99356381 := bstep (se 3 (by rfl) ⟨18629321, by rfl⟩ : syracuseStep 99356381 = 37258643) B37258643
theorem B1814249 : Blo 1209422 1814249 := bstep (se 2 (by rfl) ⟨680343, by rfl⟩ : syracuseStep 1814249 = 1360687) B1360687
theorem B6131537 : Blo 1209422 6131537 := bstep (se 2 (by rfl) ⟨2299326, by rfl⟩ : syracuseStep 6131537 = 4598653) B4598653
theorem B1814393 : Blo 1209422 1814393 := bstep (se 2 (by rfl) ⟨680397, by rfl⟩ : syracuseStep 1814393 = 1360795) B1360795
theorem B2723705 : Blo 1209422 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B6123437 : Blo 1209422 6123437 := bstep (se 3 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 6123437 = 2296289) B2296289
theorem B5812175 : Blo 1209422 5812175 := bstep (se 1 (by rfl) ⟨4359131, by rfl⟩ : syracuseStep 5812175 = 8718263) B8718263
theorem B1814495 : Blo 1209422 1814495 := bstep (se 1 (by rfl) ⟨1360871, by rfl⟩ : syracuseStep 1814495 = 2721743) B2721743
theorem B4141043 : Blo 1209422 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B1814747 : Blo 1209422 1814747 := bstep (se 1 (by rfl) ⟨1361060, by rfl⟩ : syracuseStep 1814747 = 2722121) B2722121
theorem B1814759 : Blo 1209422 1814759 := bstep (se 1 (by rfl) ⟨1361069, by rfl⟩ : syracuseStep 1814759 = 2722139) B2722139
theorem B4083965 : Blo 1209422 4083965 := bstep (se 3 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 4083965 = 1531487) B1531487
theorem B1814921 : Blo 1209422 1814921 := bstep (se 2 (by rfl) ⟨680595, by rfl⟩ : syracuseStep 1814921 = 1361191) B1361191
theorem B1724809 : Blo 1209422 1724809 := bstep (se 2 (by rfl) ⟨646803, by rfl⟩ : syracuseStep 1724809 = 1293607) B1293607
theorem B4362707 : Blo 1209422 4362707 := bstep (se 1 (by rfl) ⟨3272030, by rfl⟩ : syracuseStep 4362707 = 6544061) B6544061
theorem B1815017 : Blo 1209422 1815017 := bstep (se 2 (by rfl) ⟨680631, by rfl⟩ : syracuseStep 1815017 = 1361263) B1361263
theorem B2585171 : Blo 1209422 2585171 := bstep (se 1 (by rfl) ⟨1938878, by rfl⟩ : syracuseStep 2585171 = 3877757) B3877757
theorem B1815143 : Blo 1209422 1815143 := bstep (se 1 (by rfl) ⟨1361357, by rfl⟩ : syracuseStep 1815143 = 2722715) B2722715
theorem B6132347 : Blo 1209422 6132347 := bstep (se 1 (by rfl) ⟨4599260, by rfl⟩ : syracuseStep 6132347 = 9198521) B9198521
theorem B8729309 : Blo 1209422 8729309 := bstep (se 3 (by rfl) ⟨1636745, by rfl⟩ : syracuseStep 8729309 = 3273491) B3273491
theorem B1815275 : Blo 1209422 1815275 := bstep (se 1 (by rfl) ⟨1361456, by rfl⟩ : syracuseStep 1815275 = 2722913) B2722913
theorem B1815305 : Blo 1209422 1815305 := bstep (se 2 (by rfl) ⟨680739, by rfl⟩ : syracuseStep 1815305 = 1361479) B1361479
theorem B4084505 : Blo 1209422 4084505 := bstep (se 2 (by rfl) ⟨1531689, by rfl⟩ : syracuseStep 4084505 = 3063379) B3063379
theorem B1815407 : Blo 1209422 1815407 := bstep (se 1 (by rfl) ⟨1361555, by rfl⟩ : syracuseStep 1815407 = 2723111) B2723111
theorem B1635323 : Blo 1209422 1635323 := bstep (se 1 (by rfl) ⟨1226492, by rfl⟩ : syracuseStep 1635323 = 2452985) B2452985
theorem B5166089 : Blo 1209422 5166089 := bstep (se 2 (by rfl) ⟨1937283, by rfl⟩ : syracuseStep 5166089 = 3874567) B3874567
theorem B4084775 : Blo 1209422 4084775 := bstep (se 1 (by rfl) ⟨3063581, by rfl⟩ : syracuseStep 4084775 = 6127163) B6127163
theorem B1815659 : Blo 1209422 1815659 := bstep (se 1 (by rfl) ⟨1361744, by rfl⟩ : syracuseStep 1815659 = 2723489) B2723489
theorem B6894791 : Blo 1209422 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B1209551 : Blo 1209422 1209551 := bstep (se 1 (by rfl) ⟨907163, by rfl⟩ : syracuseStep 1209551 = 1814327) B1814327
theorem B1815899 : Blo 1209422 1815899 := bstep (se 1 (by rfl) ⟨1361924, by rfl⟩ : syracuseStep 1815899 = 2723849) B2723849
theorem B1209755 : Blo 1209422 1209755 := bstep (se 1 (by rfl) ⟨907316, by rfl⟩ : syracuseStep 1209755 = 1814633) B1814633
theorem B6125057 : Blo 1209422 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B15947297 : Blo 1209422 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B1209967 : Blo 1209422 1209967 := bstep (se 1 (by rfl) ⟨907475, by rfl⟩ : syracuseStep 1209967 = 1814951) B1814951
theorem B1816175 : Blo 1209422 1816175 := bstep (se 1 (by rfl) ⟨1362131, by rfl⟩ : syracuseStep 1816175 = 2724263) B2724263
theorem B1210023 : Blo 1209422 1210023 := bstep (se 1 (by rfl) ⟨907517, by rfl⟩ : syracuseStep 1210023 = 1815035) B1815035
theorem B1816247 : Blo 1209422 1816247 := bstep (se 1 (by rfl) ⟨1362185, by rfl⟩ : syracuseStep 1816247 = 2724371) B2724371
theorem B2725559 : Blo 1209422 2725559 := bstep (se 1 (by rfl) ⟨2044169, by rfl⟩ : syracuseStep 2725559 = 4088339) B4088339
theorem B1816283 : Blo 1209422 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B2209531 : Blo 1209422 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B1210107 : Blo 1209422 1210107 := bstep (se 1 (by rfl) ⟨907580, by rfl⟩ : syracuseStep 1210107 = 1815161) B1815161
theorem B1210143 : Blo 1209422 1210143 := bstep (se 1 (by rfl) ⟨907607, by rfl⟩ : syracuseStep 1210143 = 1815215) B1815215
theorem B1939231 : Blo 1209422 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B1210175 : Blo 1209422 1210175 := bstep (se 1 (by rfl) ⟨907631, by rfl⟩ : syracuseStep 1210175 = 1815263) B1815263
theorem B1816457 : Blo 1209422 1816457 := bstep (se 2 (by rfl) ⟨681171, by rfl⟩ : syracuseStep 1816457 = 1362343) B1362343
theorem B1210351 : Blo 1209422 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1816559 : Blo 1209422 1816559 := bstep (se 1 (by rfl) ⟨1362419, by rfl⟩ : syracuseStep 1816559 = 2724839) B2724839
theorem B4085855 : Blo 1209422 4085855 := bstep (se 1 (by rfl) ⟨3064391, by rfl⟩ : syracuseStep 4085855 = 6128783) B6128783
theorem B1210523 : Blo 1209422 1210523 := bstep (se 1 (by rfl) ⟨907892, by rfl⟩ : syracuseStep 1210523 = 1815785) B1815785
theorem B3061921 : Blo 1209422 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B1210559 : Blo 1209422 1210559 := bstep (se 1 (by rfl) ⟨907919, by rfl⟩ : syracuseStep 1210559 = 1815839) B1815839
theorem B1816811 : Blo 1209422 1816811 := bstep (se 1 (by rfl) ⟨1362608, by rfl⟩ : syracuseStep 1816811 = 2725217) B2725217
theorem B22092041 : Blo 1209422 22092041 := bstep (se 2 (by rfl) ⟨8284515, by rfl⟩ : syracuseStep 22092041 = 16569031) B16569031
theorem B1816871 : Blo 1209422 1816871 := bstep (se 1 (by rfl) ⟨1362653, by rfl⟩ : syracuseStep 1816871 = 2725307) B2725307
theorem B6125867 : Blo 1209422 6125867 := bstep (se 1 (by rfl) ⟨4594400, by rfl⟩ : syracuseStep 6125867 = 9188801) B9188801
theorem B1210671 : Blo 1209422 1210671 := bstep (se 1 (by rfl) ⟨908003, by rfl⟩ : syracuseStep 1210671 = 1816007) B1816007
theorem B4905323 : Blo 1209422 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B1816955 : Blo 1209422 1816955 := bstep (se 1 (by rfl) ⟨1362716, by rfl⟩ : syracuseStep 1816955 = 2725433) B2725433
theorem B34912721 : Blo 1209422 34912721 := bstep (se 2 (by rfl) ⟨13092270, by rfl⟩ : syracuseStep 34912721 = 26184541) B26184541
theorem B9198035 : Blo 1209422 9198035 := bstep (se 1 (by rfl) ⟨6898526, by rfl⟩ : syracuseStep 9198035 = 13797053) B13797053
theorem B1210907 : Blo 1209422 1210907 := bstep (se 1 (by rfl) ⟨908180, by rfl⟩ : syracuseStep 1210907 = 1816361) B1816361
theorem B1210911 : Blo 1209422 1210911 := bstep (se 1 (by rfl) ⟨908183, by rfl⟩ : syracuseStep 1210911 = 1816367) B1816367
theorem B5519929 : Blo 1209422 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B5814983 : Blo 1209422 5814983 := bstep (se 1 (by rfl) ⟨4361237, by rfl⟩ : syracuseStep 5814983 = 8722475) B8722475
theorem B5315371 : Blo 1209422 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B4086611 : Blo 1209422 4086611 := bstep (se 1 (by rfl) ⟨3064958, by rfl⟩ : syracuseStep 4086611 = 6129917) B6129917
theorem B1211227 : Blo 1209422 1211227 := bstep (se 1 (by rfl) ⟨908420, by rfl⟩ : syracuseStep 1211227 = 1816841) B1816841
theorem B1211295 : Blo 1209422 1211295 := bstep (se 1 (by rfl) ⟨908471, by rfl⟩ : syracuseStep 1211295 = 1816943) B1816943
theorem B4595039 : Blo 1209422 4595039 := bstep (se 1 (by rfl) ⟨3446279, by rfl⟩ : syracuseStep 4595039 = 6892559) B6892559
theorem B4087151 : Blo 1209422 4087151 := bstep (se 1 (by rfl) ⟨3065363, by rfl⟩ : syracuseStep 4087151 = 6130727) B6130727
theorem B15711853 : Blo 1209422 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B3063521 : Blo 1209422 3063521 := bstep (se 2 (by rfl) ⟨1148820, by rfl⟩ : syracuseStep 3063521 = 2297641) B2297641
theorem B4087529 : Blo 1209422 4087529 := bstep (se 2 (by rfl) ⟨1532823, by rfl⟩ : syracuseStep 4087529 = 3065647) B3065647
theorem B34881353 : Blo 1209422 34881353 := bstep (se 2 (by rfl) ⟨13080507, by rfl⟩ : syracuseStep 34881353 = 26161015) B26161015
theorem B6897959 : Blo 1209422 6897959 := bstep (se 1 (by rfl) ⟨5173469, by rfl⟩ : syracuseStep 6897959 = 10346939) B10346939
theorem B2908471 : Blo 1209422 2908471 := bstep (se 1 (by rfl) ⟨2181353, by rfl⟩ : syracuseStep 2908471 = 4362707) B4362707
theorem B4088231 : Blo 1209422 4088231 := bstep (se 1 (by rfl) ⟨3066173, by rfl⟩ : syracuseStep 4088231 = 6132347) B6132347
theorem B4596527 : Blo 1209422 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B8282989 : Blo 1209422 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B2180287 : Blo 1209422 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B1361119 : Blo 1209422 1361119 := bstep (se 1 (by rfl) ⟨1020839, by rfl⟩ : syracuseStep 1361119 = 2041679) B2041679
theorem B2721275 : Blo 1209422 2721275 := bstep (se 1 (by rfl) ⟨2040956, by rfl⟩ : syracuseStep 2721275 = 4081913) B4081913
theorem B2721311 : Blo 1209422 2721311 := bstep (se 1 (by rfl) ⟨2040983, by rfl⟩ : syracuseStep 2721311 = 4081967) B4081967
theorem B3270215 : Blo 1209422 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B23275147 : Blo 1209422 23275147 := bstep (se 1 (by rfl) ⟨17456360, by rfl⟩ : syracuseStep 23275147 = 34912721) B34912721
theorem B2721455 : Blo 1209422 2721455 := bstep (se 1 (by rfl) ⟨2041091, by rfl⟩ : syracuseStep 2721455 = 4082183) B4082183
theorem B3876655 : Blo 1209422 3876655 := bstep (se 1 (by rfl) ⟨2907491, by rfl⟩ : syracuseStep 3876655 = 5814983) B5814983
theorem B1361947 : Blo 1209422 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B2721887 : Blo 1209422 2721887 := bstep (se 1 (by rfl) ⟨2041415, by rfl⟩ : syracuseStep 2721887 = 4082831) B4082831
theorem B3065951 : Blo 1209422 3065951 := bstep (se 1 (by rfl) ⟨2299463, by rfl⟩ : syracuseStep 3065951 = 4598927) B4598927
theorem B20949137 : Blo 1209422 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B2722175 : Blo 1209422 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B176556509 : Blo 1209422 176556509 := bstep (se 3 (by rfl) ⟨33104345, by rfl⟩ : syracuseStep 176556509 = 66208691) B66208691
theorem B2042347 : Blo 1209422 2042347 := bstep (se 1 (by rfl) ⟨1531760, by rfl⟩ : syracuseStep 2042347 = 3063521) B3063521
theorem B4082291 : Blo 1209422 4082291 := bstep (se 1 (by rfl) ⟨3061718, by rfl⟩ : syracuseStep 4082291 = 6123437) B6123437
theorem B4360861 : Blo 1209422 4360861 := bstep (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) B1635323
theorem B2722643 : Blo 1209422 2722643 := bstep (se 1 (by rfl) ⟨2041982, by rfl⟩ : syracuseStep 2722643 = 4083965) B4083965
theorem B4082561 : Blo 1209422 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B2296745 : Blo 1209422 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B1723447 : Blo 1209422 1723447 := bstep (se 1 (by rfl) ⟨1292585, by rfl⟩ : syracuseStep 1723447 = 2585171) B2585171
theorem B5819539 : Blo 1209422 5819539 := bstep (se 1 (by rfl) ⟨4364654, by rfl⟩ : syracuseStep 5819539 = 8729309) B8729309
theorem B2043049 : Blo 1209422 2043049 := bstep (se 2 (by rfl) ⟨766143, by rfl⟩ : syracuseStep 2043049 = 1532287) B1532287
theorem B2723003 : Blo 1209422 2723003 := bstep (se 1 (by rfl) ⟨2042252, by rfl⟩ : syracuseStep 2723003 = 4084505) B4084505
theorem B2043191 : Blo 1209422 2043191 := bstep (se 1 (by rfl) ⟨1532393, by rfl⟩ : syracuseStep 2043191 = 3064787) B3064787
theorem B3444059 : Blo 1209422 3444059 := bstep (se 1 (by rfl) ⟨2583044, by rfl⟩ : syracuseStep 3444059 = 5166089) B5166089
theorem B58912109 : Blo 1209422 58912109 := bstep (se 3 (by rfl) ⟨11046020, by rfl⟩ : syracuseStep 58912109 = 22092041) B22092041
theorem B2723183 : Blo 1209422 2723183 := bstep (se 1 (by rfl) ⟨2042387, by rfl⟩ : syracuseStep 2723183 = 4084775) B4084775
theorem B7359905 : Blo 1209422 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B167841233 : Blo 1209422 167841233 := bstep (se 2 (by rfl) ⟨62940462, by rfl⟩ : syracuseStep 167841233 = 125880925) B125880925
theorem B4083371 : Blo 1209422 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B5811907 : Blo 1209422 5811907 := bstep (se 1 (by rfl) ⟨4358930, by rfl⟩ : syracuseStep 5811907 = 8717861) B8717861
theorem B1814267 : Blo 1209422 1814267 := bstep (se 1 (by rfl) ⟨1360700, by rfl⟩ : syracuseStep 1814267 = 2721401) B2721401
theorem B2043643 : Blo 1209422 2043643 := bstep (se 1 (by rfl) ⟨1532732, by rfl⟩ : syracuseStep 2043643 = 3065465) B3065465
theorem B2043785 : Blo 1209422 2043785 := bstep (se 2 (by rfl) ⟨766419, by rfl⟩ : syracuseStep 2043785 = 1532839) B1532839
theorem B2723903 : Blo 1209422 2723903 := bstep (se 1 (by rfl) ⟨2042927, by rfl⟩ : syracuseStep 2723903 = 4085855) B4085855
theorem B1454207 : Blo 1209422 1454207 := bstep (se 1 (by rfl) ⟨1090655, by rfl⟩ : syracuseStep 1454207 = 2181311) B2181311
theorem B10342565 : Blo 1209422 10342565 := bstep (se 4 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 10342565 = 1939231) B1939231
theorem B4083911 : Blo 1209422 4083911 := bstep (se 1 (by rfl) ⟨3062933, by rfl⟩ : syracuseStep 4083911 = 6125867) B6125867
theorem B28348645 : Blo 1209422 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B2724137 : Blo 1209422 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B5812523 : Blo 1209422 5812523 := bstep (se 1 (by rfl) ⟨4359392, by rfl⟩ : syracuseStep 5812523 = 8718785) B8718785
theorem B6132023 : Blo 1209422 6132023 := bstep (se 1 (by rfl) ⟨4599017, by rfl⟩ : syracuseStep 6132023 = 9198035) B9198035
theorem B1814939 : Blo 1209422 1814939 := bstep (se 1 (by rfl) ⟨1361204, by rfl⟩ : syracuseStep 1814939 = 2722409) B2722409
theorem B2724407 : Blo 1209422 2724407 := bstep (se 1 (by rfl) ⟨2043305, by rfl⟩ : syracuseStep 2724407 = 4086611) B4086611
theorem B11629271 : Blo 1209422 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B35877599 : Blo 1209422 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B1815359 : Blo 1209422 1815359 := bstep (se 1 (by rfl) ⟨1361519, by rfl⟩ : syracuseStep 1815359 = 2723039) B2723039
theorem B2724713 : Blo 1209422 2724713 := bstep (se 2 (by rfl) ⟨1021767, by rfl⟩ : syracuseStep 2724713 = 2043535) B2043535
theorem B2724767 : Blo 1209422 2724767 := bstep (se 1 (by rfl) ⟨2043575, by rfl⟩ : syracuseStep 2724767 = 4087151) B4087151
theorem B1815503 : Blo 1209422 1815503 := bstep (se 1 (by rfl) ⟨1361627, by rfl⟩ : syracuseStep 1815503 = 2723255) B2723255
theorem B2946041 : Blo 1209422 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B1815545 : Blo 1209422 1815545 := bstep (se 2 (by rfl) ⟨680829, by rfl⟩ : syracuseStep 1815545 = 1361659) B1361659
theorem B1815593 : Blo 1209422 1815593 := bstep (se 2 (by rfl) ⟨680847, by rfl⟩ : syracuseStep 1815593 = 1361695) B1361695
theorem B1815623 : Blo 1209422 1815623 := bstep (se 1 (by rfl) ⟨1361717, by rfl⟩ : syracuseStep 1815623 = 2723435) B2723435
theorem B66237587 : Blo 1209422 66237587 := bstep (se 1 (by rfl) ⟨49678190, by rfl⟩ : syracuseStep 66237587 = 99356381) B99356381
theorem B1209499 : Blo 1209422 1209499 := bstep (se 1 (by rfl) ⟨907124, by rfl⟩ : syracuseStep 1209499 = 1814249) B1814249
theorem B2725019 : Blo 1209422 2725019 := bstep (se 1 (by rfl) ⟨2043764, by rfl⟩ : syracuseStep 2725019 = 4087529) B4087529
theorem B23254235 : Blo 1209422 23254235 := bstep (se 1 (by rfl) ⟨17440676, by rfl⟩ : syracuseStep 23254235 = 34881353) B34881353
theorem B1209595 : Blo 1209422 1209595 := bstep (se 1 (by rfl) ⟨907196, by rfl⟩ : syracuseStep 1209595 = 1814393) B1814393
theorem B1815803 : Blo 1209422 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B1209663 : Blo 1209422 1209663 := bstep (se 1 (by rfl) ⟨907247, by rfl⟩ : syracuseStep 1209663 = 1814495) B1814495
theorem B4085099 : Blo 1209422 4085099 := bstep (se 1 (by rfl) ⟨3063824, by rfl⟩ : syracuseStep 4085099 = 6127649) B6127649
theorem B4363631 : Blo 1209422 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B31020407 : Blo 1209422 31020407 := bstep (se 1 (by rfl) ⟨23265305, by rfl⟩ : syracuseStep 31020407 = 46530611) B46530611
theorem B4593095 : Blo 1209422 4593095 := bstep (se 1 (by rfl) ⟨3444821, by rfl⟩ : syracuseStep 4593095 = 6889643) B6889643
theorem B1209831 : Blo 1209422 1209831 := bstep (se 1 (by rfl) ⟨907373, by rfl⟩ : syracuseStep 1209831 = 1814747) B1814747
theorem B1209839 : Blo 1209422 1209839 := bstep (se 1 (by rfl) ⟨907379, by rfl⟩ : syracuseStep 1209839 = 1814759) B1814759
theorem B1209947 : Blo 1209422 1209947 := bstep (se 1 (by rfl) ⟨907460, by rfl⟩ : syracuseStep 1209947 = 1814921) B1814921
theorem B4085369 : Blo 1209422 4085369 := bstep (se 2 (by rfl) ⟨1532013, by rfl⟩ : syracuseStep 4085369 = 3064027) B3064027
theorem B4593307 : Blo 1209422 4593307 := bstep (se 1 (by rfl) ⟨3444980, by rfl⟩ : syracuseStep 4593307 = 6889961) B6889961
theorem B1210011 : Blo 1209422 1210011 := bstep (se 1 (by rfl) ⟨907508, by rfl⟩ : syracuseStep 1210011 = 1815017) B1815017
theorem B2725595 : Blo 1209422 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B1210095 : Blo 1209422 1210095 := bstep (se 1 (by rfl) ⟨907571, by rfl⟩ : syracuseStep 1210095 = 1815143) B1815143
theorem B1210183 : Blo 1209422 1210183 := bstep (se 1 (by rfl) ⟨907637, by rfl⟩ : syracuseStep 1210183 = 1815275) B1815275
theorem B1210203 : Blo 1209422 1210203 := bstep (se 1 (by rfl) ⟨907652, by rfl⟩ : syracuseStep 1210203 = 1815305) B1815305
theorem B2299745 : Blo 1209422 2299745 := bstep (se 2 (by rfl) ⟨862404, by rfl⟩ : syracuseStep 2299745 = 1724809) B1724809
theorem B1210271 : Blo 1209422 1210271 := bstep (se 1 (by rfl) ⟨907703, by rfl⟩ : syracuseStep 1210271 = 1815407) B1815407
theorem B4085693 : Blo 1209422 4085693 := bstep (se 3 (by rfl) ⟨766067, by rfl⟩ : syracuseStep 4085693 = 1532135) B1532135
theorem B5167097 : Blo 1209422 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B1210439 : Blo 1209422 1210439 := bstep (se 1 (by rfl) ⟨907829, by rfl⟩ : syracuseStep 1210439 = 1815659) B1815659
theorem B1210599 : Blo 1209422 1210599 := bstep (se 1 (by rfl) ⟨907949, by rfl⟩ : syracuseStep 1210599 = 1815899) B1815899
theorem B18897229 : Blo 1209422 18897229 := bstep (se 3 (by rfl) ⟨3543230, by rfl⟩ : syracuseStep 18897229 = 7086461) B7086461
theorem B4659551 : Blo 1209422 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B10631531 : Blo 1209422 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B1210783 : Blo 1209422 1210783 := bstep (se 1 (by rfl) ⟨908087, by rfl⟩ : syracuseStep 1210783 = 1816175) B1816175
theorem B1210831 : Blo 1209422 1210831 := bstep (se 1 (by rfl) ⟨908123, by rfl⟩ : syracuseStep 1210831 = 1816247) B1816247
theorem B1817039 : Blo 1209422 1817039 := bstep (se 1 (by rfl) ⟨1362779, by rfl⟩ : syracuseStep 1817039 = 2725559) B2725559
theorem B1210855 : Blo 1209422 1210855 := bstep (se 1 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 1210855 = 1816283) B1816283
theorem B1817129 : Blo 1209422 1817129 := bstep (se 2 (by rfl) ⟨681423, by rfl⟩ : syracuseStep 1817129 = 1362847) B1362847
theorem B1210971 : Blo 1209422 1210971 := bstep (se 1 (by rfl) ⟨908228, by rfl⟩ : syracuseStep 1210971 = 1816457) B1816457
theorem B6896249 : Blo 1209422 6896249 := bstep (se 2 (by rfl) ⟨2586093, by rfl⟩ : syracuseStep 6896249 = 5172187) B5172187
theorem B1211039 : Blo 1209422 1211039 := bstep (se 1 (by rfl) ⟨908279, by rfl⟩ : syracuseStep 1211039 = 1816559) B1816559
theorem B1211207 : Blo 1209422 1211207 := bstep (se 1 (by rfl) ⟨908405, by rfl⟩ : syracuseStep 1211207 = 1816811) B1816811
theorem B1211247 : Blo 1209422 1211247 := bstep (se 1 (by rfl) ⟨908435, by rfl⟩ : syracuseStep 1211247 = 1816871) B1816871
theorem B1211303 : Blo 1209422 1211303 := bstep (se 1 (by rfl) ⟨908477, by rfl⟩ : syracuseStep 1211303 = 1816955) B1816955
theorem B4086881 : Blo 1209422 4086881 := bstep (se 2 (by rfl) ⟨1532580, by rfl⟩ : syracuseStep 4086881 = 3065161) B3065161
theorem B3063359 : Blo 1209422 3063359 := bstep (se 1 (by rfl) ⟨2297519, by rfl⟩ : syracuseStep 3063359 = 4595039) B4595039
theorem B149085809 : Blo 1209422 149085809 := bstep (se 2 (by rfl) ⟨55907178, by rfl⟩ : syracuseStep 149085809 = 111814357) B111814357
theorem B4087421 : Blo 1209422 4087421 := bstep (se 3 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 4087421 = 1532783) B1532783
theorem B4087583 : Blo 1209422 4087583 := bstep (se 1 (by rfl) ⟨3065687, by rfl⟩ : syracuseStep 4087583 = 6131375) B6131375
theorem B15499133 : Blo 1209422 15499133 := bstep (se 3 (by rfl) ⟨2906087, by rfl⟩ : syracuseStep 15499133 = 5812175) B5812175
theorem B4087691 : Blo 1209422 4087691 := bstep (se 1 (by rfl) ⟨3065768, by rfl⟩ : syracuseStep 4087691 = 6131537) B6131537
theorem B2760695 : Blo 1209422 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B3875015 : Blo 1209422 3875015 := bstep (se 1 (by rfl) ⟨2906261, by rfl⟩ : syracuseStep 3875015 = 5812523) B5812523
theorem B4088015 : Blo 1209422 4088015 := bstep (se 1 (by rfl) ⟨3066011, by rfl⟩ : syracuseStep 4088015 = 6132023) B6132023
theorem B9191717 : Blo 1209422 9191717 := bstep (se 4 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 9191717 = 1723447) B1723447
theorem B3064351 : Blo 1209422 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B23257925 : Blo 1209422 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B2909087 : Blo 1209422 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B2180143 : Blo 1209422 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B11043985 : Blo 1209422 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B1533163 : Blo 1209422 1533163 := bstep (se 1 (by rfl) ⟨1149872, by rfl⟩ : syracuseStep 1533163 = 2299745) B2299745
theorem B7759385 : Blo 1209422 7759385 := bstep (se 2 (by rfl) ⟨2909769, by rfl⟩ : syracuseStep 7759385 = 5819539) B5819539
theorem B3106367 : Blo 1209422 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B117704339 : Blo 1209422 117704339 := bstep (se 1 (by rfl) ⟨88278254, by rfl⟩ : syracuseStep 117704339 = 176556509) B176556509
theorem B2721527 : Blo 1209422 2721527 := bstep (se 1 (by rfl) ⟨2041145, by rfl⟩ : syracuseStep 2721527 = 4082291) B4082291
theorem B4597499 : Blo 1209422 4597499 := bstep (se 1 (by rfl) ⟨3448124, by rfl⟩ : syracuseStep 4597499 = 6896249) B6896249
theorem B2721707 : Blo 1209422 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B31033529 : Blo 1209422 31033529 := bstep (se 2 (by rfl) ⟨11637573, by rfl⟩ : syracuseStep 31033529 = 23275147) B23275147
theorem B1362127 : Blo 1209422 1362127 := bstep (se 1 (by rfl) ⟨1021595, by rfl⟩ : syracuseStep 1362127 = 2043191) B2043191
theorem B2296039 : Blo 1209422 2296039 := bstep (se 1 (by rfl) ⟨1722029, by rfl⟩ : syracuseStep 2296039 = 3444059) B3444059
theorem B39274739 : Blo 1209422 39274739 := bstep (se 1 (by rfl) ⟨29456054, by rfl⟩ : syracuseStep 39274739 = 58912109) B58912109
theorem B2042239 : Blo 1209422 2042239 := bstep (se 1 (by rfl) ⟨1531679, by rfl⟩ : syracuseStep 2042239 = 3063359) B3063359
theorem B2722247 : Blo 1209422 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B10332755 : Blo 1209422 10332755 := bstep (se 1 (by rfl) ⟨7749566, by rfl⟩ : syracuseStep 10332755 = 15499133) B15499133
theorem B1362523 : Blo 1209422 1362523 := bstep (se 1 (by rfl) ⟨1021892, by rfl⟩ : syracuseStep 1362523 = 2043785) B2043785
theorem B2722607 : Blo 1209422 2722607 := bstep (se 1 (by rfl) ⟨2041955, by rfl⟩ : syracuseStep 2722607 = 4083911) B4083911
theorem B4598639 : Blo 1209422 4598639 := bstep (se 1 (by rfl) ⟨3448979, by rfl⟩ : syracuseStep 4598639 = 6897959) B6897959
theorem B3877885 : Blo 1209422 3877885 := bstep (se 3 (by rfl) ⟨727103, by rfl⟩ : syracuseStep 3877885 = 1454207) B1454207
theorem B3877961 : Blo 1209422 3877961 := bstep (se 2 (by rfl) ⟨1454235, by rfl⟩ : syracuseStep 3877961 = 2908471) B2908471
theorem B7752847 : Blo 1209422 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B2723129 : Blo 1209422 2723129 := bstep (se 2 (by rfl) ⟨1021173, by rfl⟩ : syracuseStep 2723129 = 2042347) B2042347
theorem B44158391 : Blo 1209422 44158391 := bstep (se 1 (by rfl) ⟨33118793, by rfl⟩ : syracuseStep 44158391 = 66237587) B66237587
theorem B15502823 : Blo 1209422 15502823 := bstep (se 1 (by rfl) ⟨11627117, by rfl⟩ : syracuseStep 15502823 = 23254235) B23254235
theorem B2723399 : Blo 1209422 2723399 := bstep (se 1 (by rfl) ⟨2042549, by rfl⟩ : syracuseStep 2723399 = 4085099) B4085099
theorem B20680271 : Blo 1209422 20680271 := bstep (se 1 (by rfl) ⟨15510203, by rfl⟩ : syracuseStep 20680271 = 31020407) B31020407
theorem B11628197 : Blo 1209422 11628197 := bstep (se 4 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 11628197 = 2180287) B2180287
theorem B1814183 : Blo 1209422 1814183 := bstep (se 1 (by rfl) ⟨1360637, by rfl⟩ : syracuseStep 1814183 = 2721275) B2721275
theorem B1814207 : Blo 1209422 1814207 := bstep (se 1 (by rfl) ⟨1360655, by rfl⟩ : syracuseStep 1814207 = 2721311) B2721311
theorem B2723579 : Blo 1209422 2723579 := bstep (se 1 (by rfl) ⟨2042684, by rfl⟩ : syracuseStep 2723579 = 4085369) B4085369
theorem B1814303 : Blo 1209422 1814303 := bstep (se 1 (by rfl) ⟨1360727, by rfl⟩ : syracuseStep 1814303 = 2721455) B2721455
theorem B2723795 : Blo 1209422 2723795 := bstep (se 1 (by rfl) ⟨2042846, by rfl⟩ : syracuseStep 2723795 = 4085693) B4085693
theorem B3444731 : Blo 1209422 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B1814591 : Blo 1209422 1814591 := bstep (se 1 (by rfl) ⟨1360943, by rfl⟩ : syracuseStep 1814591 = 2721887) B2721887
theorem B2043967 : Blo 1209422 2043967 := bstep (se 1 (by rfl) ⟨1532975, by rfl⟩ : syracuseStep 2043967 = 3065951) B3065951
theorem B2724065 : Blo 1209422 2724065 := bstep (se 2 (by rfl) ⟨1021524, by rfl⟩ : syracuseStep 2724065 = 2043049) B2043049
theorem B1814783 : Blo 1209422 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B1814825 : Blo 1209422 1814825 := bstep (se 2 (by rfl) ⟨680559, by rfl⟩ : syracuseStep 1814825 = 1361119) B1361119
theorem B1815095 : Blo 1209422 1815095 := bstep (se 1 (by rfl) ⟨1361321, by rfl⟩ : syracuseStep 1815095 = 2722643) B2722643
theorem B2724587 : Blo 1209422 2724587 := bstep (se 1 (by rfl) ⟨2043440, by rfl⟩ : syracuseStep 2724587 = 4086881) B4086881
theorem B604771093 : Blo 1209422 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B1815335 : Blo 1209422 1815335 := bstep (se 1 (by rfl) ⟨1361501, by rfl⟩ : syracuseStep 1815335 = 2723003) B2723003
theorem B6124409 : Blo 1209422 6124409 := bstep (se 2 (by rfl) ⟨2296653, by rfl⟩ : syracuseStep 6124409 = 4593307) B4593307
theorem B1815455 : Blo 1209422 1815455 := bstep (se 1 (by rfl) ⟨1361591, by rfl⟩ : syracuseStep 1815455 = 2723183) B2723183
theorem B2724857 : Blo 1209422 2724857 := bstep (se 2 (by rfl) ⟨1021821, by rfl⟩ : syracuseStep 2724857 = 2043643) B2043643
theorem B99390539 : Blo 1209422 99390539 := bstep (se 1 (by rfl) ⟨74542904, by rfl⟩ : syracuseStep 99390539 = 149085809) B149085809
theorem B2724947 : Blo 1209422 2724947 := bstep (se 1 (by rfl) ⟨2043710, by rfl⟩ : syracuseStep 2724947 = 4087421) B4087421
theorem B1209511 : Blo 1209422 1209511 := bstep (se 1 (by rfl) ⟨907133, by rfl⟩ : syracuseStep 1209511 = 1814267) B1814267
theorem B2725055 : Blo 1209422 2725055 := bstep (se 1 (by rfl) ⟨2043791, by rfl⟩ : syracuseStep 2725055 = 4087583) B4087583
theorem B2725127 : Blo 1209422 2725127 := bstep (se 1 (by rfl) ⟨2043845, by rfl⟩ : syracuseStep 2725127 = 4087691) B4087691
theorem B1840463 : Blo 1209422 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B1815929 : Blo 1209422 1815929 := bstep (se 2 (by rfl) ⟨680973, by rfl⟩ : syracuseStep 1815929 = 1361947) B1361947
theorem B1815935 : Blo 1209422 1815935 := bstep (se 1 (by rfl) ⟨1361951, by rfl⟩ : syracuseStep 1815935 = 2723903) B2723903
theorem B6895043 : Blo 1209422 6895043 := bstep (se 1 (by rfl) ⟨5171282, by rfl⟩ : syracuseStep 6895043 = 10342565) B10342565
theorem B1816091 : Blo 1209422 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B1209959 : Blo 1209422 1209959 := bstep (se 1 (by rfl) ⟨907469, by rfl⟩ : syracuseStep 1209959 = 1814939) B1814939
theorem B2725487 : Blo 1209422 2725487 := bstep (se 1 (by rfl) ⟨2044115, by rfl⟩ : syracuseStep 2725487 = 4088231) B4088231
theorem B1816271 : Blo 1209422 1816271 := bstep (se 1 (by rfl) ⟨1362203, by rfl⟩ : syracuseStep 1816271 = 2724407) B2724407
theorem B25196305 : Blo 1209422 25196305 := bstep (se 2 (by rfl) ⟨9448614, by rfl⟩ : syracuseStep 25196305 = 18897229) B18897229
theorem B23918399 : Blo 1209422 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B1210239 : Blo 1209422 1210239 := bstep (se 1 (by rfl) ⟨907679, by rfl⟩ : syracuseStep 1210239 = 1815359) B1815359
theorem B1816475 : Blo 1209422 1816475 := bstep (se 1 (by rfl) ⟨1362356, by rfl⟩ : syracuseStep 1816475 = 2724713) B2724713
theorem B1816511 : Blo 1209422 1816511 := bstep (se 1 (by rfl) ⟨1362383, by rfl⟩ : syracuseStep 1816511 = 2724767) B2724767
theorem B1210335 : Blo 1209422 1210335 := bstep (se 1 (by rfl) ⟨907751, by rfl⟩ : syracuseStep 1210335 = 1815503) B1815503
theorem B1964027 : Blo 1209422 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B1210363 : Blo 1209422 1210363 := bstep (se 1 (by rfl) ⟨907772, by rfl⟩ : syracuseStep 1210363 = 1815545) B1815545
theorem B1210395 : Blo 1209422 1210395 := bstep (se 1 (by rfl) ⟨907796, by rfl⟩ : syracuseStep 1210395 = 1815593) B1815593
theorem B1210415 : Blo 1209422 1210415 := bstep (se 1 (by rfl) ⟨907811, by rfl⟩ : syracuseStep 1210415 = 1815623) B1815623
theorem B1816679 : Blo 1209422 1816679 := bstep (se 1 (by rfl) ⟨1362509, by rfl⟩ : syracuseStep 1816679 = 2725019) B2725019
theorem B1210535 : Blo 1209422 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B28350749 : Blo 1209422 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B3062063 : Blo 1209422 3062063 := bstep (se 1 (by rfl) ⟨2296547, by rfl⟩ : syracuseStep 3062063 = 4593095) B4593095
theorem B1817063 : Blo 1209422 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B13966091 : Blo 1209422 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B1211359 : Blo 1209422 1211359 := bstep (se 1 (by rfl) ⟨908519, by rfl⟩ : syracuseStep 1211359 = 1817039) B1817039
theorem B1211419 : Blo 1209422 1211419 := bstep (se 1 (by rfl) ⟨908564, by rfl⟩ : syracuseStep 1211419 = 1817129) B1817129
theorem B1531163 : Blo 1209422 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B7749209 : Blo 1209422 7749209 := bstep (se 2 (by rfl) ⟨2905953, by rfl⟩ : syracuseStep 7749209 = 5811907) B5811907
theorem B4906603 : Blo 1209422 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B111894155 : Blo 1209422 111894155 := bstep (se 1 (by rfl) ⟨83920616, by rfl⟩ : syracuseStep 111894155 = 167841233) B167841233
theorem B5168873 : Blo 1209422 5168873 := bstep (se 2 (by rfl) ⟨1938327, by rfl⟩ : syracuseStep 5168873 = 3876655) B3876655
theorem B6127811 : Blo 1209422 6127811 := bstep (se 1 (by rfl) ⟨4595858, by rfl⟩ : syracuseStep 6127811 = 9191717) B9191717
theorem B4596695 : Blo 1209422 4596695 := bstep (se 1 (by rfl) ⟨3447521, by rfl⟩ : syracuseStep 4596695 = 6895043) B6895043
theorem B3064999 : Blo 1209422 3064999 := bstep (se 1 (by rfl) ⟨2298749, by rfl⟩ : syracuseStep 3064999 = 4597499) B4597499
theorem B5170513 : Blo 1209422 5170513 := bstep (se 2 (by rfl) ⟨1938942, by rfl⟩ : syracuseStep 5170513 = 3877885) B3877885
theorem B3225445829 : Blo 1209422 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B26183159 : Blo 1209422 26183159 := bstep (se 1 (by rfl) ⟨19637369, by rfl⟩ : syracuseStep 26183159 = 39274739) B39274739
theorem B18900499 : Blo 1209422 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B2041375 : Blo 1209422 2041375 := bstep (se 1 (by rfl) ⟨1531031, by rfl⟩ : syracuseStep 2041375 = 3062063) B3062063
theorem B3065759 : Blo 1209422 3065759 := bstep (se 1 (by rfl) ⟨2299319, by rfl⟩ : syracuseStep 3065759 = 4598639) B4598639
theorem B7752131 : Blo 1209422 7752131 := bstep (se 1 (by rfl) ⟨5814098, by rfl⟩ : syracuseStep 7752131 = 11628197) B11628197
theorem B5237405 : Blo 1209422 5237405 := bstep (se 3 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 5237405 = 1964027) B1964027
theorem B2296487 : Blo 1209422 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B2583343 : Blo 1209422 2583343 := bstep (se 1 (by rfl) ⟨1937507, by rfl⟩ : syracuseStep 2583343 = 3875015) B3875015
theorem B10341229 : Blo 1209422 10341229 := bstep (se 3 (by rfl) ⟨1938980, by rfl⟩ : syracuseStep 10341229 = 3877961) B3877961
theorem B2722985 : Blo 1209422 2722985 := bstep (se 2 (by rfl) ⟨1021119, by rfl⟩ : syracuseStep 2722985 = 2042239) B2042239
theorem B4082939 : Blo 1209422 4082939 := bstep (se 1 (by rfl) ⟨3062204, by rfl⟩ : syracuseStep 4082939 = 6124409) B6124409
theorem B66260359 : Blo 1209422 66260359 := bstep (se 1 (by rfl) ⟨49695269, by rfl⟩ : syracuseStep 66260359 = 99390539) B99390539
theorem B4083101 : Blo 1209422 4083101 := bstep (se 3 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 4083101 = 1531163) B1531163
theorem B19631605 : Blo 1209422 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B5172923 : Blo 1209422 5172923 := bstep (se 1 (by rfl) ⟨3879692, by rfl⟩ : syracuseStep 5172923 = 7759385) B7759385
theorem B1814351 : Blo 1209422 1814351 := bstep (se 1 (by rfl) ⟨1360763, by rfl⟩ : syracuseStep 1814351 = 2721527) B2721527
theorem B15945599 : Blo 1209422 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B1814471 : Blo 1209422 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B20689019 : Blo 1209422 20689019 := bstep (se 1 (by rfl) ⟨15516764, by rfl⟩ : syracuseStep 20689019 = 31033529) B31033529
theorem B14725313 : Blo 1209422 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B1814831 : Blo 1209422 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B2044217 : Blo 1209422 2044217 := bstep (se 2 (by rfl) ⟨766581, by rfl⟩ : syracuseStep 2044217 = 1533163) B1533163
theorem B9310727 : Blo 1209422 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B1815071 : Blo 1209422 1815071 := bstep (se 1 (by rfl) ⟨1361303, by rfl⟩ : syracuseStep 1815071 = 2722607) B2722607
theorem B6542137 : Blo 1209422 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B1815419 : Blo 1209422 1815419 := bstep (se 1 (by rfl) ⟨1361564, by rfl⟩ : syracuseStep 1815419 = 2723129) B2723129
theorem B29438927 : Blo 1209422 29438927 := bstep (se 1 (by rfl) ⟨22079195, by rfl⟩ : syracuseStep 29438927 = 44158391) B44158391
theorem B10335215 : Blo 1209422 10335215 := bstep (se 1 (by rfl) ⟨7751411, by rfl⟩ : syracuseStep 10335215 = 15502823) B15502823
theorem B1815599 : Blo 1209422 1815599 := bstep (se 1 (by rfl) ⟨1361699, by rfl⟩ : syracuseStep 1815599 = 2723399) B2723399
theorem B5166139 : Blo 1209422 5166139 := bstep (se 1 (by rfl) ⟨3874604, by rfl⟩ : syracuseStep 5166139 = 7749209) B7749209
theorem B1209455 : Blo 1209422 1209455 := bstep (se 1 (by rfl) ⟨907091, by rfl⟩ : syracuseStep 1209455 = 1814183) B1814183
theorem B1209471 : Blo 1209422 1209471 := bstep (se 1 (by rfl) ⟨907103, by rfl⟩ : syracuseStep 1209471 = 1814207) B1814207
theorem B3445915 : Blo 1209422 3445915 := bstep (se 1 (by rfl) ⟨2584436, by rfl⟩ : syracuseStep 3445915 = 5168873) B5168873
theorem B1815719 : Blo 1209422 1815719 := bstep (se 1 (by rfl) ⟨1361789, by rfl⟩ : syracuseStep 1815719 = 2723579) B2723579
theorem B1209535 : Blo 1209422 1209535 := bstep (se 1 (by rfl) ⟨907151, by rfl⟩ : syracuseStep 1209535 = 1814303) B1814303
theorem B1815863 : Blo 1209422 1815863 := bstep (se 1 (by rfl) ⟨1361897, by rfl⟩ : syracuseStep 1815863 = 2723795) B2723795
theorem B1209727 : Blo 1209422 1209727 := bstep (se 1 (by rfl) ⟨907295, by rfl⟩ : syracuseStep 1209727 = 1814591) B1814591
theorem B2725289 : Blo 1209422 2725289 := bstep (se 2 (by rfl) ⟨1021983, by rfl⟩ : syracuseStep 2725289 = 2043967) B2043967
theorem B2725343 : Blo 1209422 2725343 := bstep (se 1 (by rfl) ⟨2044007, by rfl⟩ : syracuseStep 2725343 = 4088015) B4088015
theorem B1816043 : Blo 1209422 1816043 := bstep (se 1 (by rfl) ⟨1362032, by rfl⟩ : syracuseStep 1816043 = 2724065) B2724065
theorem B1209855 : Blo 1209422 1209855 := bstep (se 1 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 1209855 = 1814783) B1814783
theorem B1209883 : Blo 1209422 1209883 := bstep (se 1 (by rfl) ⟨907412, by rfl⟩ : syracuseStep 1209883 = 1814825) B1814825
theorem B1816169 : Blo 1209422 1816169 := bstep (se 2 (by rfl) ⟨681063, by rfl⟩ : syracuseStep 1816169 = 1362127) B1362127
theorem B3061385 : Blo 1209422 3061385 := bstep (se 2 (by rfl) ⟨1148019, by rfl⟩ : syracuseStep 3061385 = 2296039) B2296039
theorem B1210063 : Blo 1209422 1210063 := bstep (se 1 (by rfl) ⟨907547, by rfl⟩ : syracuseStep 1210063 = 1815095) B1815095
theorem B1816391 : Blo 1209422 1816391 := bstep (se 1 (by rfl) ⟨1362293, by rfl⟩ : syracuseStep 1816391 = 2724587) B2724587
theorem B1210223 : Blo 1209422 1210223 := bstep (se 1 (by rfl) ⟨907667, by rfl⟩ : syracuseStep 1210223 = 1815335) B1815335
theorem B15505283 : Blo 1209422 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B1210303 : Blo 1209422 1210303 := bstep (se 1 (by rfl) ⟨907727, by rfl⟩ : syracuseStep 1210303 = 1815455) B1815455
theorem B1939391 : Blo 1209422 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B1816571 : Blo 1209422 1816571 := bstep (se 1 (by rfl) ⟨1362428, by rfl⟩ : syracuseStep 1816571 = 2724857) B2724857
theorem B4085801 : Blo 1209422 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B1816631 : Blo 1209422 1816631 := bstep (se 1 (by rfl) ⟨1362473, by rfl⟩ : syracuseStep 1816631 = 2724947) B2724947
theorem B1816697 : Blo 1209422 1816697 := bstep (se 2 (by rfl) ⟨681261, by rfl⟩ : syracuseStep 1816697 = 1362523) B1362523
theorem B1816703 : Blo 1209422 1816703 := bstep (se 1 (by rfl) ⟨1362527, by rfl⟩ : syracuseStep 1816703 = 2725055) B2725055
theorem B1816751 : Blo 1209422 1816751 := bstep (se 1 (by rfl) ⟨1362563, by rfl⟩ : syracuseStep 1816751 = 2725127) B2725127
theorem B1210619 : Blo 1209422 1210619 := bstep (se 1 (by rfl) ⟨907964, by rfl⟩ : syracuseStep 1210619 = 1815929) B1815929
theorem B1210623 : Blo 1209422 1210623 := bstep (se 1 (by rfl) ⟨907967, by rfl⟩ : syracuseStep 1210623 = 1815935) B1815935
theorem B1210727 : Blo 1209422 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B2070911 : Blo 1209422 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B1816991 : Blo 1209422 1816991 := bstep (se 1 (by rfl) ⟨1362743, by rfl⟩ : syracuseStep 1816991 = 2725487) B2725487
theorem B78469559 : Blo 1209422 78469559 := bstep (se 1 (by rfl) ⟨58852169, by rfl⟩ : syracuseStep 78469559 = 117704339) B117704339
theorem B1210847 : Blo 1209422 1210847 := bstep (se 1 (by rfl) ⟨908135, by rfl⟩ : syracuseStep 1210847 = 1816271) B1816271
theorem B1210983 : Blo 1209422 1210983 := bstep (se 1 (by rfl) ⟨908237, by rfl⟩ : syracuseStep 1210983 = 1816475) B1816475
theorem B1211007 : Blo 1209422 1211007 := bstep (se 1 (by rfl) ⟨908255, by rfl⟩ : syracuseStep 1211007 = 1816511) B1816511
theorem B2906857 : Blo 1209422 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B1211119 : Blo 1209422 1211119 := bstep (se 1 (by rfl) ⟨908339, by rfl⟩ : syracuseStep 1211119 = 1816679) B1816679
theorem B10337129 : Blo 1209422 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B1211375 : Blo 1209422 1211375 := bstep (se 1 (by rfl) ⟨908531, by rfl⟩ : syracuseStep 1211375 = 1817063) B1817063
theorem B6888503 : Blo 1209422 6888503 := bstep (se 1 (by rfl) ⟨5166377, by rfl⟩ : syracuseStep 6888503 = 10332755) B10332755
theorem B33595073 : Blo 1209422 33595073 := bstep (se 2 (by rfl) ⟨12598152, by rfl⟩ : syracuseStep 33595073 = 25196305) B25196305
theorem B13786847 : Blo 1209422 13786847 := bstep (se 1 (by rfl) ⟨10340135, by rfl⟩ : syracuseStep 13786847 = 20680271) B20680271
theorem B74596103 : Blo 1209422 74596103 := bstep (se 1 (by rfl) ⟨55947077, by rfl⟩ : syracuseStep 74596103 = 111894155) B111894155
theorem B3064463 : Blo 1209422 3064463 := bstep (se 1 (by rfl) ⟨2298347, by rfl⟩ : syracuseStep 3064463 = 4596695) B4596695
theorem B6890143 : Blo 1209422 6890143 := bstep (se 1 (by rfl) ⟨5167607, by rfl⟩ : syracuseStep 6890143 = 10335215) B10335215
theorem B3875809 : Blo 1209422 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B2040923 : Blo 1209422 2040923 := bstep (se 1 (by rfl) ⟨1530692, by rfl⟩ : syracuseStep 2040923 = 3061385) B3061385
theorem B13788305 : Blo 1209422 13788305 := bstep (se 2 (by rfl) ⟨5170614, by rfl⟩ : syracuseStep 13788305 = 10341229) B10341229
theorem B34891397 : Blo 1209422 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B3491603 : Blo 1209422 3491603 := bstep (se 1 (by rfl) ⟨2618702, by rfl⟩ : syracuseStep 3491603 = 5237405) B5237405
theorem B6891419 : Blo 1209422 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B26175473 : Blo 1209422 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B25200665 : Blo 1209422 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B2721833 : Blo 1209422 2721833 := bstep (se 2 (by rfl) ⟨1020687, by rfl⟩ : syracuseStep 2721833 = 2041375) B2041375
theorem B2721959 : Blo 1209422 2721959 := bstep (se 1 (by rfl) ⟨2041469, by rfl⟩ : syracuseStep 2721959 = 4082939) B4082939
theorem B2722067 : Blo 1209422 2722067 := bstep (se 1 (by rfl) ⟨2041550, by rfl⟩ : syracuseStep 2722067 = 4083101) B4083101
theorem B9816875 : Blo 1209422 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B1362811 : Blo 1209422 1362811 := bstep (se 1 (by rfl) ⟨1022108, by rfl⟩ : syracuseStep 1362811 = 2044217) B2044217
theorem B2150297219 : Blo 1209422 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B3444457 : Blo 1209422 3444457 := bstep (se 2 (by rfl) ⟨1291671, by rfl⟩ : syracuseStep 3444457 = 2583343) B2583343
theorem B2043839 : Blo 1209422 2043839 := bstep (se 1 (by rfl) ⟨1532879, by rfl⟩ : syracuseStep 2043839 = 3065759) B3065759
theorem B2723867 : Blo 1209422 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B1380607 : Blo 1209422 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B6894017 : Blo 1209422 6894017 := bstep (se 2 (by rfl) ⟨2585256, by rfl⟩ : syracuseStep 6894017 = 5170513) B5170513
theorem B88347145 : Blo 1209422 88347145 := bstep (se 2 (by rfl) ⟨33130179, by rfl⟩ : syracuseStep 88347145 = 66260359) B66260359
theorem B4592335 : Blo 1209422 4592335 := bstep (se 1 (by rfl) ⟨3444251, by rfl⟩ : syracuseStep 4592335 = 6888503) B6888503
theorem B1815323 : Blo 1209422 1815323 := bstep (se 1 (by rfl) ⟨1361492, by rfl⟩ : syracuseStep 1815323 = 2722985) B2722985
theorem B49730735 : Blo 1209422 49730735 := bstep (se 1 (by rfl) ⟨37298051, by rfl⟩ : syracuseStep 49730735 = 74596103) B74596103
theorem B1209567 : Blo 1209422 1209567 := bstep (se 1 (by rfl) ⟨907175, by rfl⟩ : syracuseStep 1209567 = 1814351) B1814351
theorem B10630399 : Blo 1209422 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B1209647 : Blo 1209422 1209647 := bstep (se 1 (by rfl) ⟨907235, by rfl⟩ : syracuseStep 1209647 = 1814471) B1814471
theorem B13792679 : Blo 1209422 13792679 := bstep (se 1 (by rfl) ⟨10344509, by rfl⟩ : syracuseStep 13792679 = 20689019) B20689019
theorem B4085207 : Blo 1209422 4085207 := bstep (se 1 (by rfl) ⟨3063905, by rfl⟩ : syracuseStep 4085207 = 6127811) B6127811
theorem B1209887 : Blo 1209422 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B6207151 : Blo 1209422 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B1210047 : Blo 1209422 1210047 := bstep (se 1 (by rfl) ⟨907535, by rfl⟩ : syracuseStep 1210047 = 1815071) B1815071
theorem B1210279 : Blo 1209422 1210279 := bstep (se 1 (by rfl) ⟨907709, by rfl⟩ : syracuseStep 1210279 = 1815419) B1815419
theorem B19625951 : Blo 1209422 19625951 := bstep (se 1 (by rfl) ⟨14719463, by rfl⟩ : syracuseStep 19625951 = 29438927) B29438927
theorem B1210399 : Blo 1209422 1210399 := bstep (se 1 (by rfl) ⟨907799, by rfl⟩ : syracuseStep 1210399 = 1815599) B1815599
theorem B1210479 : Blo 1209422 1210479 := bstep (se 1 (by rfl) ⟨907859, by rfl⟩ : syracuseStep 1210479 = 1815719) B1815719
theorem B1210575 : Blo 1209422 1210575 := bstep (se 1 (by rfl) ⟨907931, by rfl⟩ : syracuseStep 1210575 = 1815863) B1815863
theorem B1816859 : Blo 1209422 1816859 := bstep (se 1 (by rfl) ⟨1362644, by rfl⟩ : syracuseStep 1816859 = 2725289) B2725289
theorem B1816895 : Blo 1209422 1816895 := bstep (se 1 (by rfl) ⟨1362671, by rfl⟩ : syracuseStep 1816895 = 2725343) B2725343
theorem B1210695 : Blo 1209422 1210695 := bstep (se 1 (by rfl) ⟨908021, by rfl⟩ : syracuseStep 1210695 = 1816043) B1816043
theorem B17455439 : Blo 1209422 17455439 := bstep (se 1 (by rfl) ⟨13091579, by rfl⟩ : syracuseStep 17455439 = 26183159) B26183159
theorem B1210779 : Blo 1209422 1210779 := bstep (se 1 (by rfl) ⟨908084, by rfl⟩ : syracuseStep 1210779 = 1816169) B1816169
theorem B1210927 : Blo 1209422 1210927 := bstep (se 1 (by rfl) ⟨908195, by rfl⟩ : syracuseStep 1210927 = 1816391) B1816391
theorem B10336855 : Blo 1209422 10336855 := bstep (se 1 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 10336855 = 15505283) B15505283
theorem B1292927 : Blo 1209422 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B1211047 : Blo 1209422 1211047 := bstep (se 1 (by rfl) ⟨908285, by rfl⟩ : syracuseStep 1211047 = 1816571) B1816571
theorem B1211087 : Blo 1209422 1211087 := bstep (se 1 (by rfl) ⟨908315, by rfl⟩ : syracuseStep 1211087 = 1816631) B1816631
theorem B6888185 : Blo 1209422 6888185 := bstep (se 2 (by rfl) ⟨2583069, by rfl⟩ : syracuseStep 6888185 = 5166139) B5166139
theorem B1211131 : Blo 1209422 1211131 := bstep (se 1 (by rfl) ⟨908348, by rfl⟩ : syracuseStep 1211131 = 1816697) B1816697
theorem B1211135 : Blo 1209422 1211135 := bstep (se 1 (by rfl) ⟨908351, by rfl⟩ : syracuseStep 1211135 = 1816703) B1816703
theorem B1211167 : Blo 1209422 1211167 := bstep (se 1 (by rfl) ⟨908375, by rfl⟩ : syracuseStep 1211167 = 1816751) B1816751
theorem B4594553 : Blo 1209422 4594553 := bstep (se 2 (by rfl) ⟨1722957, by rfl⟩ : syracuseStep 4594553 = 3445915) B3445915
theorem B4086665 : Blo 1209422 4086665 := bstep (se 2 (by rfl) ⟨1532499, by rfl⟩ : syracuseStep 4086665 = 3064999) B3064999
theorem B1211327 : Blo 1209422 1211327 := bstep (se 1 (by rfl) ⟨908495, by rfl⟩ : syracuseStep 1211327 = 1816991) B1816991
theorem B52313039 : Blo 1209422 52313039 := bstep (se 1 (by rfl) ⟨39234779, by rfl⟩ : syracuseStep 52313039 = 78469559) B78469559
theorem B5168087 : Blo 1209422 5168087 := bstep (se 1 (by rfl) ⟨3876065, by rfl⟩ : syracuseStep 5168087 = 7752131) B7752131
theorem B1530991 : Blo 1209422 1530991 := bstep (se 1 (by rfl) ⟨1148243, by rfl⟩ : syracuseStep 1530991 = 2296487) B2296487
theorem B3448615 : Blo 1209422 3448615 := bstep (se 1 (by rfl) ⟨2586461, by rfl⟩ : syracuseStep 3448615 = 5172923) B5172923
theorem B22396715 : Blo 1209422 22396715 := bstep (se 1 (by rfl) ⟨16797536, by rfl⟩ : syracuseStep 22396715 = 33595073) B33595073
theorem B9191231 : Blo 1209422 9191231 := bstep (se 1 (by rfl) ⟨6893423, by rfl⟩ : syracuseStep 9191231 = 13786847) B13786847
theorem B4596011 : Blo 1209422 4596011 := bstep (se 1 (by rfl) ⟨3447008, by rfl⟩ : syracuseStep 4596011 = 6894017) B6894017
theorem B1360615 : Blo 1209422 1360615 := bstep (se 1 (by rfl) ⟨1020461, by rfl⟩ : syracuseStep 1360615 = 2040923) B2040923
theorem B9192203 : Blo 1209422 9192203 := bstep (se 1 (by rfl) ⟨6894152, by rfl⟩ : syracuseStep 9192203 = 13788305) B13788305
theorem B33153823 : Blo 1209422 33153823 := bstep (se 1 (by rfl) ⟨24865367, by rfl⟩ : syracuseStep 33153823 = 49730735) B49730735
theorem B2327735 : Blo 1209422 2327735 := bstep (se 1 (by rfl) ⟨1745801, by rfl⟩ : syracuseStep 2327735 = 3491603) B3491603
theorem B13083967 : Blo 1209422 13083967 := bstep (se 1 (by rfl) ⟨9812975, by rfl⟩ : syracuseStep 13083967 = 19625951) B19625951
theorem B17450315 : Blo 1209422 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B2041321 : Blo 1209422 2041321 := bstep (se 2 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 2041321 = 1530991) B1530991
theorem B14173865 : Blo 1209422 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B34875359 : Blo 1209422 34875359 := bstep (se 1 (by rfl) ⟨26156519, by rfl⟩ : syracuseStep 34875359 = 52313039) B52313039
theorem B8276201 : Blo 1209422 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B4598153 : Blo 1209422 4598153 := bstep (se 2 (by rfl) ⟨1724307, by rfl⟩ : syracuseStep 4598153 = 3448615) B3448615
theorem B1362559 : Blo 1209422 1362559 := bstep (se 1 (by rfl) ⟨1021919, by rfl⟩ : syracuseStep 1362559 = 2043839) B2043839
theorem B2042975 : Blo 1209422 2042975 := bstep (se 1 (by rfl) ⟨1532231, by rfl⟩ : syracuseStep 2042975 = 3064463) B3064463
theorem B117796193 : Blo 1209422 117796193 := bstep (se 2 (by rfl) ⟨44173572, by rfl⟩ : syracuseStep 117796193 = 88347145) B88347145
theorem B13782473 : Blo 1209422 13782473 := bstep (se 2 (by rfl) ⟨5168427, by rfl⟩ : syracuseStep 13782473 = 10336855) B10336855
theorem B9186857 : Blo 1209422 9186857 := bstep (se 2 (by rfl) ⟨3445071, by rfl⟩ : syracuseStep 9186857 = 6890143) B6890143
theorem B6123113 : Blo 1209422 6123113 := bstep (se 2 (by rfl) ⟨2296167, by rfl⟩ : syracuseStep 6123113 = 4592335) B4592335
theorem B9195119 : Blo 1209422 9195119 := bstep (se 1 (by rfl) ⟨6896339, by rfl⟩ : syracuseStep 9195119 = 13792679) B13792679
theorem B2723471 : Blo 1209422 2723471 := bstep (se 1 (by rfl) ⟨2042603, by rfl⟩ : syracuseStep 2723471 = 4085207) B4085207
theorem B23260931 : Blo 1209422 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B13791221 : Blo 1209422 13791221 := bstep (se 5 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 13791221 = 1292927) B1292927
theorem B1814555 : Blo 1209422 1814555 := bstep (se 1 (by rfl) ⟨1360916, by rfl⟩ : syracuseStep 1814555 = 2721833) B2721833
theorem B1814639 : Blo 1209422 1814639 := bstep (se 1 (by rfl) ⟨1360979, by rfl⟩ : syracuseStep 1814639 = 2721959) B2721959
theorem B1814711 : Blo 1209422 1814711 := bstep (se 1 (by rfl) ⟨1361033, by rfl⟩ : syracuseStep 1814711 = 2722067) B2722067
theorem B11636959 : Blo 1209422 11636959 := bstep (se 1 (by rfl) ⟨8727719, by rfl⟩ : syracuseStep 11636959 = 17455439) B17455439
theorem B5734125917 : Blo 1209422 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B4592123 : Blo 1209422 4592123 := bstep (se 1 (by rfl) ⟨3444092, by rfl⟩ : syracuseStep 4592123 = 6888185) B6888185
theorem B2724443 : Blo 1209422 2724443 := bstep (se 1 (by rfl) ⟨2043332, by rfl⟩ : syracuseStep 2724443 = 4086665) B4086665
theorem B3445391 : Blo 1209422 3445391 := bstep (se 1 (by rfl) ⟨2584043, by rfl⟩ : syracuseStep 3445391 = 5168087) B5168087
theorem B4592609 : Blo 1209422 4592609 := bstep (se 2 (by rfl) ⟨1722228, by rfl⟩ : syracuseStep 4592609 = 3444457) B3444457
theorem B14931143 : Blo 1209422 14931143 := bstep (se 1 (by rfl) ⟨11198357, by rfl⟩ : syracuseStep 14931143 = 22396715) B22396715
theorem B1815911 : Blo 1209422 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B1210215 : Blo 1209422 1210215 := bstep (se 1 (by rfl) ⟨907661, by rfl⟩ : syracuseStep 1210215 = 1815323) B1815323
theorem B1817081 : Blo 1209422 1817081 := bstep (se 2 (by rfl) ⟨681405, by rfl⟩ : syracuseStep 1817081 = 1362811) B1362811
theorem B4594279 : Blo 1209422 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B5167745 : Blo 1209422 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B7363237 : Blo 1209422 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B16800443 : Blo 1209422 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B1211239 : Blo 1209422 1211239 := bstep (se 1 (by rfl) ⟨908429, by rfl⟩ : syracuseStep 1211239 = 1816859) B1816859
theorem B1211263 : Blo 1209422 1211263 := bstep (se 1 (by rfl) ⟨908447, by rfl⟩ : syracuseStep 1211263 = 1816895) B1816895
theorem B6544583 : Blo 1209422 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B3063035 : Blo 1209422 3063035 := bstep (se 1 (by rfl) ⟨2297276, by rfl⟩ : syracuseStep 3063035 = 4594553) B4594553
theorem B6127487 : Blo 1209422 6127487 := bstep (se 1 (by rfl) ⟨4595615, by rfl⟩ : syracuseStep 6127487 = 9191231) B9191231
theorem B3064007 : Blo 1209422 3064007 := bstep (se 1 (by rfl) ⟨2298005, by rfl⟩ : syracuseStep 3064007 = 4596011) B4596011
theorem B15515945 : Blo 1209422 15515945 := bstep (se 2 (by rfl) ⟨5818479, by rfl⟩ : syracuseStep 15515945 = 11636959) B11636959
theorem B6128135 : Blo 1209422 6128135 := bstep (se 1 (by rfl) ⟨4596101, by rfl⟩ : syracuseStep 6128135 = 9192203) B9192203
theorem B9954095 : Blo 1209422 9954095 := bstep (se 1 (by rfl) ⟨7465571, by rfl⟩ : syracuseStep 9954095 = 14931143) B14931143
theorem B11633543 : Blo 1209422 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B44205097 : Blo 1209422 44205097 := bstep (se 2 (by rfl) ⟨16576911, by rfl⟩ : syracuseStep 44205097 = 33153823) B33153823
theorem B23250239 : Blo 1209422 23250239 := bstep (se 1 (by rfl) ⟨17437679, by rfl⟩ : syracuseStep 23250239 = 34875359) B34875359
theorem B3065435 : Blo 1209422 3065435 := bstep (se 1 (by rfl) ⟨2299076, by rfl⟩ : syracuseStep 3065435 = 4598153) B4598153
theorem B11200295 : Blo 1209422 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B2721761 : Blo 1209422 2721761 := bstep (se 2 (by rfl) ⟨1020660, by rfl⟩ : syracuseStep 2721761 = 2041321) B2041321
theorem B1361983 : Blo 1209422 1361983 := bstep (se 1 (by rfl) ⟨1021487, by rfl⟩ : syracuseStep 1361983 = 2042975) B2042975
theorem B2042023 : Blo 1209422 2042023 := bstep (se 1 (by rfl) ⟨1531517, by rfl⟩ : syracuseStep 2042023 = 3063035) B3063035
theorem B78530795 : Blo 1209422 78530795 := bstep (se 1 (by rfl) ⟨58898096, by rfl⟩ : syracuseStep 78530795 = 117796193) B117796193
theorem B4082075 : Blo 1209422 4082075 := bstep (se 1 (by rfl) ⟨3061556, by rfl⟩ : syracuseStep 4082075 = 6123113) B6123113
theorem B6130079 : Blo 1209422 6130079 := bstep (se 1 (by rfl) ⟨4597559, by rfl⟩ : syracuseStep 6130079 = 9195119) B9195119
theorem B9194147 : Blo 1209422 9194147 := bstep (se 1 (by rfl) ⟨6895610, by rfl⟩ : syracuseStep 9194147 = 13791221) B13791221
theorem B3822750611 : Blo 1209422 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B2296927 : Blo 1209422 2296927 := bstep (se 1 (by rfl) ⟨1722695, by rfl⟩ : syracuseStep 2296927 = 3445391) B3445391
theorem B9817649 : Blo 1209422 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B1814153 : Blo 1209422 1814153 := bstep (se 2 (by rfl) ⟨680307, by rfl⟩ : syracuseStep 1814153 = 1360615) B1360615
theorem B9449243 : Blo 1209422 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B5517467 : Blo 1209422 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B17445289 : Blo 1209422 17445289 := bstep (se 2 (by rfl) ⟨6541983, by rfl⟩ : syracuseStep 17445289 = 13083967) B13083967
theorem B3445163 : Blo 1209422 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B4363055 : Blo 1209422 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B9188315 : Blo 1209422 9188315 := bstep (se 1 (by rfl) ⟨6891236, by rfl⟩ : syracuseStep 9188315 = 13782473) B13782473
theorem B6124571 : Blo 1209422 6124571 := bstep (se 1 (by rfl) ⟨4593428, by rfl⟩ : syracuseStep 6124571 = 9186857) B9186857
theorem B1815647 : Blo 1209422 1815647 := bstep (se 1 (by rfl) ⟨1361735, by rfl⟩ : syracuseStep 1815647 = 2723471) B2723471
theorem B4084991 : Blo 1209422 4084991 := bstep (se 1 (by rfl) ⟨3063743, by rfl⟩ : syracuseStep 4084991 = 6127487) B6127487
theorem B1209703 : Blo 1209422 1209703 := bstep (se 1 (by rfl) ⟨907277, by rfl⟩ : syracuseStep 1209703 = 1814555) B1814555
theorem B1209759 : Blo 1209422 1209759 := bstep (se 1 (by rfl) ⟨907319, by rfl⟩ : syracuseStep 1209759 = 1814639) B1814639
theorem B1209807 : Blo 1209422 1209807 := bstep (se 1 (by rfl) ⟨907355, by rfl⟩ : syracuseStep 1209807 = 1814711) B1814711
theorem B3061415 : Blo 1209422 3061415 := bstep (se 1 (by rfl) ⟨2296061, by rfl⟩ : syracuseStep 3061415 = 4592123) B4592123
theorem B1816295 : Blo 1209422 1816295 := bstep (se 1 (by rfl) ⟨1362221, by rfl⟩ : syracuseStep 1816295 = 2724443) B2724443
theorem B6207293 : Blo 1209422 6207293 := bstep (se 3 (by rfl) ⟨1163867, by rfl⟩ : syracuseStep 6207293 = 2327735) B2327735
theorem B3061739 : Blo 1209422 3061739 := bstep (se 1 (by rfl) ⟨2296304, by rfl⟩ : syracuseStep 3061739 = 4592609) B4592609
theorem B6125705 : Blo 1209422 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B1816745 : Blo 1209422 1816745 := bstep (se 2 (by rfl) ⟨681279, by rfl⟩ : syracuseStep 1816745 = 1362559) B1362559
theorem B1210607 : Blo 1209422 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B1211387 : Blo 1209422 1211387 := bstep (se 1 (by rfl) ⟨908540, by rfl⟩ : syracuseStep 1211387 = 1817081) B1817081
theorem B15507287 : Blo 1209422 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B3678311 : Blo 1209422 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B106177013 : Blo 1209422 106177013 := bstep (se 5 (by rfl) ⟨4977047, by rfl⟩ : syracuseStep 106177013 = 9954095) B9954095
theorem B2908703 : Blo 1209422 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B15500159 : Blo 1209422 15500159 := bstep (se 1 (by rfl) ⟨11625119, by rfl⟩ : syracuseStep 15500159 = 23250239) B23250239
theorem B2040943 : Blo 1209422 2040943 := bstep (se 1 (by rfl) ⟨1530707, by rfl⟩ : syracuseStep 2040943 = 3061415) B3061415
theorem B2041159 : Blo 1209422 2041159 := bstep (se 1 (by rfl) ⟨1530869, by rfl⟩ : syracuseStep 2041159 = 3061739) B3061739
theorem B2721383 : Blo 1209422 2721383 := bstep (se 1 (by rfl) ⟨2041037, by rfl⟩ : syracuseStep 2721383 = 4082075) B4082075
theorem B6129431 : Blo 1209422 6129431 := bstep (se 1 (by rfl) ⟨4597073, by rfl⟩ : syracuseStep 6129431 = 9194147) B9194147
theorem B2548500407 : Blo 1209422 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B2042671 : Blo 1209422 2042671 := bstep (se 1 (by rfl) ⟨1532003, by rfl⟩ : syracuseStep 2042671 = 3064007) B3064007
theorem B2722697 : Blo 1209422 2722697 := bstep (se 2 (by rfl) ⟨1021011, by rfl⟩ : syracuseStep 2722697 = 2042023) B2042023
theorem B2296775 : Blo 1209422 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B23260385 : Blo 1209422 23260385 := bstep (se 2 (by rfl) ⟨8722644, by rfl⟩ : syracuseStep 23260385 = 17445289) B17445289
theorem B4083047 : Blo 1209422 4083047 := bstep (se 1 (by rfl) ⟨3062285, by rfl⟩ : syracuseStep 4083047 = 6124571) B6124571
theorem B2723327 : Blo 1209422 2723327 := bstep (se 1 (by rfl) ⟨2042495, by rfl⟩ : syracuseStep 2723327 = 4084991) B4084991
theorem B2043623 : Blo 1209422 2043623 := bstep (se 1 (by rfl) ⟨1532717, by rfl⟩ : syracuseStep 2043623 = 3065435) B3065435
theorem B7466863 : Blo 1209422 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B1814507 : Blo 1209422 1814507 := bstep (se 1 (by rfl) ⟨1360880, by rfl⟩ : syracuseStep 1814507 = 2721761) B2721761
theorem B4083803 : Blo 1209422 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B16552781 : Blo 1209422 16552781 := bstep (se 3 (by rfl) ⟨3103646, by rfl⟩ : syracuseStep 16552781 = 6207293) B6207293
theorem B1209435 : Blo 1209422 1209435 := bstep (se 1 (by rfl) ⟨907076, by rfl⟩ : syracuseStep 1209435 = 1814153) B1814153
theorem B1815977 : Blo 1209422 1815977 := bstep (se 2 (by rfl) ⟨680991, by rfl⟩ : syracuseStep 1815977 = 1361983) B1361983
theorem B10343963 : Blo 1209422 10343963 := bstep (se 1 (by rfl) ⟨7757972, by rfl⟩ : syracuseStep 10343963 = 15515945) B15515945
theorem B4085423 : Blo 1209422 4085423 := bstep (se 1 (by rfl) ⟨3064067, by rfl⟩ : syracuseStep 4085423 = 6128135) B6128135
theorem B7755695 : Blo 1209422 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B6125543 : Blo 1209422 6125543 := bstep (se 1 (by rfl) ⟨4594157, by rfl⟩ : syracuseStep 6125543 = 9188315) B9188315
theorem B1210431 : Blo 1209422 1210431 := bstep (se 1 (by rfl) ⟨907823, by rfl⟩ : syracuseStep 1210431 = 1815647) B1815647
theorem B1210863 : Blo 1209422 1210863 := bstep (se 1 (by rfl) ⟨908147, by rfl⟩ : syracuseStep 1210863 = 1816295) B1816295
theorem B58940129 : Blo 1209422 58940129 := bstep (se 2 (by rfl) ⟨22102548, by rfl⟩ : syracuseStep 58940129 = 44205097) B44205097
theorem B1211163 : Blo 1209422 1211163 := bstep (se 1 (by rfl) ⟨908372, by rfl⟩ : syracuseStep 1211163 = 1816745) B1816745
theorem B3062569 : Blo 1209422 3062569 := bstep (se 2 (by rfl) ⟨1148463, by rfl⟩ : syracuseStep 3062569 = 2296927) B2296927
theorem B52353863 : Blo 1209422 52353863 := bstep (se 1 (by rfl) ⟨39265397, by rfl⟩ : syracuseStep 52353863 = 78530795) B78530795
theorem B4086719 : Blo 1209422 4086719 := bstep (se 1 (by rfl) ⟨3065039, by rfl⟩ : syracuseStep 4086719 = 6130079) B6130079
theorem B6545099 : Blo 1209422 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B6299495 : Blo 1209422 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B10338191 : Blo 1209422 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B11035187 : Blo 1209422 11035187 := bstep (se 1 (by rfl) ⟨8276390, by rfl⟩ : syracuseStep 11035187 = 16552781) B16552781
theorem B5170463 : Blo 1209422 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B2721257 : Blo 1209422 2721257 := bstep (se 2 (by rfl) ⟨1020471, by rfl⟩ : syracuseStep 2721257 = 2040943) B2040943
theorem B2721545 : Blo 1209422 2721545 := bstep (se 2 (by rfl) ⟨1020579, by rfl⟩ : syracuseStep 2721545 = 2041159) B2041159
theorem B2722031 : Blo 1209422 2722031 := bstep (se 1 (by rfl) ⟨2041523, by rfl⟩ : syracuseStep 2722031 = 4083047) B4083047
theorem B9955817 : Blo 1209422 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B1362415 : Blo 1209422 1362415 := bstep (se 1 (by rfl) ⟨1021811, by rfl⟩ : syracuseStep 1362415 = 2043623) B2043623
theorem B6892127 : Blo 1209422 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B2722535 : Blo 1209422 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B2452207 : Blo 1209422 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B10333439 : Blo 1209422 10333439 := bstep (se 1 (by rfl) ⟨7750079, by rfl⟩ : syracuseStep 10333439 = 15500159) B15500159
theorem B4083425 : Blo 1209422 4083425 := bstep (se 2 (by rfl) ⟨1531284, by rfl⟩ : syracuseStep 4083425 = 3062569) B3062569
theorem B2723561 : Blo 1209422 2723561 := bstep (se 2 (by rfl) ⟨1021335, by rfl⟩ : syracuseStep 2723561 = 2042671) B2042671
theorem B1814255 : Blo 1209422 1814255 := bstep (se 1 (by rfl) ⟨1360691, by rfl⟩ : syracuseStep 1814255 = 2721383) B2721383
theorem B2723615 : Blo 1209422 2723615 := bstep (se 1 (by rfl) ⟨2042711, by rfl⟩ : syracuseStep 2723615 = 4085423) B4085423
theorem B1699000271 : Blo 1209422 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B4083695 : Blo 1209422 4083695 := bstep (se 1 (by rfl) ⟨3062771, by rfl⟩ : syracuseStep 4083695 = 6125543) B6125543
theorem B39293419 : Blo 1209422 39293419 := bstep (se 1 (by rfl) ⟨29470064, by rfl⟩ : syracuseStep 39293419 = 58940129) B58940129
theorem B34902575 : Blo 1209422 34902575 := bstep (se 1 (by rfl) ⟨26176931, by rfl⟩ : syracuseStep 34902575 = 52353863) B52353863
theorem B1815131 : Blo 1209422 1815131 := bstep (se 1 (by rfl) ⟨1361348, by rfl⟩ : syracuseStep 1815131 = 2722697) B2722697
theorem B2724479 : Blo 1209422 2724479 := bstep (se 1 (by rfl) ⟨2043359, by rfl⟩ : syracuseStep 2724479 = 4086719) B4086719
theorem B1815551 : Blo 1209422 1815551 := bstep (se 1 (by rfl) ⟨1361663, by rfl⟩ : syracuseStep 1815551 = 2723327) B2723327
theorem B4363399 : Blo 1209422 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B6124733 : Blo 1209422 6124733 := bstep (se 3 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 6124733 = 2296775) B2296775
theorem B4199663 : Blo 1209422 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B1209671 : Blo 1209422 1209671 := bstep (se 1 (by rfl) ⟨907253, by rfl⟩ : syracuseStep 1209671 = 1814507) B1814507
theorem B70784675 : Blo 1209422 70784675 := bstep (se 1 (by rfl) ⟨53088506, by rfl⟩ : syracuseStep 70784675 = 106177013) B106177013
theorem B1939135 : Blo 1209422 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B1210651 : Blo 1209422 1210651 := bstep (se 1 (by rfl) ⟨907988, by rfl⟩ : syracuseStep 1210651 = 1815977) B1815977
theorem B6895975 : Blo 1209422 6895975 := bstep (se 1 (by rfl) ⟨5171981, by rfl⟩ : syracuseStep 6895975 = 10343963) B10343963
theorem B4086287 : Blo 1209422 4086287 := bstep (se 1 (by rfl) ⟨3064715, by rfl⟩ : syracuseStep 4086287 = 6129431) B6129431
theorem B15506923 : Blo 1209422 15506923 := bstep (se 1 (by rfl) ⟨11630192, by rfl⟩ : syracuseStep 15506923 = 23260385) B23260385
theorem B7356791 : Blo 1209422 7356791 := bstep (se 1 (by rfl) ⟨5517593, by rfl⟩ : syracuseStep 7356791 = 11035187) B11035187
theorem B3269609 : Blo 1209422 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B5817865 : Blo 1209422 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B6637211 : Blo 1209422 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B2722283 : Blo 1209422 2722283 := bstep (se 1 (by rfl) ⟨2041712, by rfl⟩ : syracuseStep 2722283 = 4083425) B4083425
theorem B2722463 : Blo 1209422 2722463 := bstep (se 1 (by rfl) ⟨2041847, by rfl⟩ : syracuseStep 2722463 = 4083695) B4083695
theorem B23268383 : Blo 1209422 23268383 := bstep (se 1 (by rfl) ⟨17451287, by rfl⟩ : syracuseStep 23268383 = 34902575) B34902575
theorem B9194633 : Blo 1209422 9194633 := bstep (se 2 (by rfl) ⟨3447987, by rfl⟩ : syracuseStep 9194633 = 6895975) B6895975
theorem B52391225 : Blo 1209422 52391225 := bstep (se 2 (by rfl) ⟨19646709, by rfl⟩ : syracuseStep 52391225 = 39293419) B39293419
theorem B4083155 : Blo 1209422 4083155 := bstep (se 1 (by rfl) ⟨3062366, by rfl⟩ : syracuseStep 4083155 = 6124733) B6124733
theorem B1814171 : Blo 1209422 1814171 := bstep (se 1 (by rfl) ⟨1360628, by rfl⟩ : syracuseStep 1814171 = 2721257) B2721257
theorem B47189783 : Blo 1209422 47189783 := bstep (se 1 (by rfl) ⟨35392337, by rfl⟩ : syracuseStep 47189783 = 70784675) B70784675
theorem B1814363 : Blo 1209422 1814363 := bstep (se 1 (by rfl) ⟨1360772, by rfl⟩ : syracuseStep 1814363 = 2721545) B2721545
theorem B1814687 : Blo 1209422 1814687 := bstep (se 1 (by rfl) ⟨1361015, by rfl⟩ : syracuseStep 1814687 = 2722031) B2722031
theorem B2724191 : Blo 1209422 2724191 := bstep (se 1 (by rfl) ⟨2043143, by rfl⟩ : syracuseStep 2724191 = 4086287) B4086287
theorem B1815023 : Blo 1209422 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B2585513 : Blo 1209422 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B1815707 : Blo 1209422 1815707 := bstep (se 1 (by rfl) ⟨1361780, by rfl⟩ : syracuseStep 1815707 = 2723561) B2723561
theorem B1209503 : Blo 1209422 1209503 := bstep (se 1 (by rfl) ⟨907127, by rfl⟩ : syracuseStep 1209503 = 1814255) B1814255
theorem B1815743 : Blo 1209422 1815743 := bstep (se 1 (by rfl) ⟨1361807, by rfl⟩ : syracuseStep 1815743 = 2723615) B2723615
theorem B1210087 : Blo 1209422 1210087 := bstep (se 1 (by rfl) ⟨907565, by rfl⟩ : syracuseStep 1210087 = 1815131) B1815131
theorem B1816319 : Blo 1209422 1816319 := bstep (se 1 (by rfl) ⟨1362239, by rfl⟩ : syracuseStep 1816319 = 2724479) B2724479
theorem B1816553 : Blo 1209422 1816553 := bstep (se 2 (by rfl) ⟨681207, by rfl⟩ : syracuseStep 1816553 = 1362415) B1362415
theorem B1210367 : Blo 1209422 1210367 := bstep (se 1 (by rfl) ⟨907775, by rfl⟩ : syracuseStep 1210367 = 1815551) B1815551
theorem B2799775 : Blo 1209422 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B3446975 : Blo 1209422 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B4594751 : Blo 1209422 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B20675897 : Blo 1209422 20675897 := bstep (se 2 (by rfl) ⟨7753461, by rfl⟩ : syracuseStep 20675897 = 15506923) B15506923
theorem B6888959 : Blo 1209422 6888959 := bstep (se 1 (by rfl) ⟨5166719, by rfl⟩ : syracuseStep 6888959 = 10333439) B10333439
theorem B1132666847 : Blo 1209422 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B2179739 : Blo 1209422 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B4424807 : Blo 1209422 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B6129755 : Blo 1209422 6129755 := bstep (se 1 (by rfl) ⟨4597316, by rfl⟩ : syracuseStep 6129755 = 9194633) B9194633
theorem B2722103 : Blo 1209422 2722103 := bstep (se 1 (by rfl) ⟨2041577, by rfl⟩ : syracuseStep 2722103 = 4083155) B4083155
theorem B31459855 : Blo 1209422 31459855 := bstep (se 1 (by rfl) ⟨23594891, by rfl⟩ : syracuseStep 31459855 = 47189783) B47189783
theorem B1723675 : Blo 1209422 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B2297983 : Blo 1209422 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B1814855 : Blo 1209422 1814855 := bstep (se 1 (by rfl) ⟨1361141, by rfl⟩ : syracuseStep 1814855 = 2722283) B2722283
theorem B1814975 : Blo 1209422 1814975 := bstep (se 1 (by rfl) ⟨1361231, by rfl⟩ : syracuseStep 1814975 = 2722463) B2722463
theorem B15512255 : Blo 1209422 15512255 := bstep (se 1 (by rfl) ⟨11634191, by rfl⟩ : syracuseStep 15512255 = 23268383) B23268383
theorem B13783931 : Blo 1209422 13783931 := bstep (se 1 (by rfl) ⟨10337948, by rfl⟩ : syracuseStep 13783931 = 20675897) B20675897
theorem B34927483 : Blo 1209422 34927483 := bstep (se 1 (by rfl) ⟨26195612, by rfl⟩ : syracuseStep 34927483 = 52391225) B52391225
theorem B4592639 : Blo 1209422 4592639 := bstep (se 1 (by rfl) ⟨3444479, by rfl⟩ : syracuseStep 4592639 = 6888959) B6888959
theorem B1209447 : Blo 1209422 1209447 := bstep (se 1 (by rfl) ⟨907085, by rfl⟩ : syracuseStep 1209447 = 1814171) B1814171
theorem B1209575 : Blo 1209422 1209575 := bstep (se 1 (by rfl) ⟨907181, by rfl⟩ : syracuseStep 1209575 = 1814363) B1814363
theorem B755111231 : Blo 1209422 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B1209791 : Blo 1209422 1209791 := bstep (se 1 (by rfl) ⟨907343, by rfl⟩ : syracuseStep 1209791 = 1814687) B1814687
theorem B3733033 : Blo 1209422 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B1816127 : Blo 1209422 1816127 := bstep (se 1 (by rfl) ⟨1362095, by rfl⟩ : syracuseStep 1816127 = 2724191) B2724191
theorem B1210015 : Blo 1209422 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B1210471 : Blo 1209422 1210471 := bstep (se 1 (by rfl) ⟨907853, by rfl⟩ : syracuseStep 1210471 = 1815707) B1815707
theorem B1210495 : Blo 1209422 1210495 := bstep (se 1 (by rfl) ⟨907871, by rfl⟩ : syracuseStep 1210495 = 1815743) B1815743
theorem B19618109 : Blo 1209422 19618109 := bstep (se 3 (by rfl) ⟨3678395, by rfl⟩ : syracuseStep 19618109 = 7356791) B7356791
theorem B1210879 : Blo 1209422 1210879 := bstep (se 1 (by rfl) ⟨908159, by rfl⟩ : syracuseStep 1210879 = 1816319) B1816319
theorem B1211035 : Blo 1209422 1211035 := bstep (se 1 (by rfl) ⟨908276, by rfl⟩ : syracuseStep 1211035 = 1816553) B1816553
theorem B7757153 : Blo 1209422 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B3063167 : Blo 1209422 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B3063977 : Blo 1209422 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B2949871 : Blo 1209422 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B503407487 : Blo 1209422 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B5171435 : Blo 1209422 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B2042111 : Blo 1209422 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B1453159 : Blo 1209422 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B10341503 : Blo 1209422 10341503 := bstep (se 1 (by rfl) ⟨7756127, by rfl⟩ : syracuseStep 10341503 = 15512255) B15512255
theorem B41946473 : Blo 1209422 41946473 := bstep (se 2 (by rfl) ⟨15729927, by rfl⟩ : syracuseStep 41946473 = 31459855) B31459855
theorem B1814735 : Blo 1209422 1814735 := bstep (se 1 (by rfl) ⟨1361051, by rfl⟩ : syracuseStep 1814735 = 2722103) B2722103
theorem B13078739 : Blo 1209422 13078739 := bstep (se 1 (by rfl) ⟨9809054, by rfl⟩ : syracuseStep 13078739 = 19618109) B19618109
theorem B2298233 : Blo 1209422 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B4977377 : Blo 1209422 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B1209903 : Blo 1209422 1209903 := bstep (se 1 (by rfl) ⟨907427, by rfl⟩ : syracuseStep 1209903 = 1814855) B1814855
theorem B1209983 : Blo 1209422 1209983 := bstep (se 1 (by rfl) ⟨907487, by rfl⟩ : syracuseStep 1209983 = 1814975) B1814975
theorem B9189287 : Blo 1209422 9189287 := bstep (se 1 (by rfl) ⟨6891965, by rfl⟩ : syracuseStep 9189287 = 13783931) B13783931
theorem B3061759 : Blo 1209422 3061759 := bstep (se 1 (by rfl) ⟨2296319, by rfl⟩ : syracuseStep 3061759 = 4592639) B4592639
theorem B1210751 : Blo 1209422 1210751 := bstep (se 1 (by rfl) ⟨908063, by rfl⟩ : syracuseStep 1210751 = 1816127) B1816127
theorem B46569977 : Blo 1209422 46569977 := bstep (se 2 (by rfl) ⟨17463741, by rfl⟩ : syracuseStep 46569977 = 34927483) B34927483
theorem B4086503 : Blo 1209422 4086503 := bstep (se 1 (by rfl) ⟨3064877, by rfl⟩ : syracuseStep 4086503 = 6129755) B6129755
theorem B3318251 : Blo 1209422 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B7750181 : Blo 1209422 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B3933161 : Blo 1209422 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B6128621 : Blo 1209422 6128621 := bstep (se 3 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 6128621 = 2298233) B2298233
theorem B1361407 : Blo 1209422 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B4082345 : Blo 1209422 4082345 := bstep (se 2 (by rfl) ⟨1530879, by rfl⟩ : syracuseStep 4082345 = 3061759) B3061759
theorem B2042651 : Blo 1209422 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B8719159 : Blo 1209422 8719159 := bstep (se 1 (by rfl) ⟨6539369, by rfl⟩ : syracuseStep 8719159 = 13078739) B13078739
theorem B335604991 : Blo 1209422 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B2724335 : Blo 1209422 2724335 := bstep (se 1 (by rfl) ⟨2043251, by rfl⟩ : syracuseStep 2724335 = 4086503) B4086503
theorem B6894335 : Blo 1209422 6894335 := bstep (se 1 (by rfl) ⟨5170751, by rfl⟩ : syracuseStep 6894335 = 10341503) B10341503
theorem B27964315 : Blo 1209422 27964315 := bstep (se 1 (by rfl) ⟨20973236, by rfl⟩ : syracuseStep 27964315 = 41946473) B41946473
theorem B1209823 : Blo 1209422 1209823 := bstep (se 1 (by rfl) ⟨907367, by rfl⟩ : syracuseStep 1209823 = 1814735) B1814735
theorem B6126191 : Blo 1209422 6126191 := bstep (se 1 (by rfl) ⟨4594643, by rfl⟩ : syracuseStep 6126191 = 9189287) B9189287
theorem B3447623 : Blo 1209422 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B31046651 : Blo 1209422 31046651 := bstep (se 1 (by rfl) ⟨23284988, by rfl⟩ : syracuseStep 31046651 = 46569977) B46569977
theorem B4596223 : Blo 1209422 4596223 := bstep (se 1 (by rfl) ⟨3447167, by rfl⟩ : syracuseStep 4596223 = 6894335) B6894335
theorem B2622107 : Blo 1209422 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B11625545 : Blo 1209422 11625545 := bstep (se 2 (by rfl) ⟨4359579, by rfl⟩ : syracuseStep 11625545 = 8719159) B8719159
theorem B8848669 : Blo 1209422 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B447473321 : Blo 1209422 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B2721563 : Blo 1209422 2721563 := bstep (se 1 (by rfl) ⟨2041172, by rfl⟩ : syracuseStep 2721563 = 4082345) B4082345
theorem B1361767 : Blo 1209422 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B9193661 : Blo 1209422 9193661 := bstep (se 3 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 9193661 = 3447623) B3447623
theorem B37285753 : Blo 1209422 37285753 := bstep (se 2 (by rfl) ⟨13982157, by rfl⟩ : syracuseStep 37285753 = 27964315) B27964315
theorem B4084127 : Blo 1209422 4084127 := bstep (se 1 (by rfl) ⟨3063095, by rfl⟩ : syracuseStep 4084127 = 6126191) B6126191
theorem B20697767 : Blo 1209422 20697767 := bstep (se 1 (by rfl) ⟨15523325, by rfl⟩ : syracuseStep 20697767 = 31046651) B31046651
theorem B1815209 : Blo 1209422 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B1816223 : Blo 1209422 1816223 := bstep (se 1 (by rfl) ⟨1362167, by rfl⟩ : syracuseStep 1816223 = 2724335) B2724335
theorem B4085747 : Blo 1209422 4085747 := bstep (se 1 (by rfl) ⟨3064310, by rfl⟩ : syracuseStep 4085747 = 6128621) B6128621
theorem B20667149 : Blo 1209422 20667149 := bstep (se 3 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 20667149 = 7750181) B7750181
theorem B6128297 : Blo 1209422 6128297 := bstep (se 2 (by rfl) ⟨2298111, by rfl⟩ : syracuseStep 6128297 = 4596223) B4596223
theorem B7750363 : Blo 1209422 7750363 := bstep (se 1 (by rfl) ⟨5812772, by rfl⟩ : syracuseStep 7750363 = 11625545) B11625545
theorem B6129107 : Blo 1209422 6129107 := bstep (se 1 (by rfl) ⟨4596830, by rfl⟩ : syracuseStep 6129107 = 9193661) B9193661
theorem B11798225 : Blo 1209422 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B2722751 : Blo 1209422 2722751 := bstep (se 1 (by rfl) ⟨2042063, by rfl⟩ : syracuseStep 2722751 = 4084127) B4084127
theorem B1748071 : Blo 1209422 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B13798511 : Blo 1209422 13798511 := bstep (se 1 (by rfl) ⟨10348883, by rfl⟩ : syracuseStep 13798511 = 20697767) B20697767
theorem B298315547 : Blo 1209422 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B1814375 : Blo 1209422 1814375 := bstep (se 1 (by rfl) ⟨1360781, by rfl⟩ : syracuseStep 1814375 = 2721563) B2721563
theorem B2723831 : Blo 1209422 2723831 := bstep (se 1 (by rfl) ⟨2042873, by rfl⟩ : syracuseStep 2723831 = 4085747) B4085747
theorem B1815689 : Blo 1209422 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B49714337 : Blo 1209422 49714337 := bstep (se 2 (by rfl) ⟨18642876, by rfl⟩ : syracuseStep 49714337 = 37285753) B37285753
theorem B1210139 : Blo 1209422 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B1210815 : Blo 1209422 1210815 := bstep (se 1 (by rfl) ⟨908111, by rfl⟩ : syracuseStep 1210815 = 1816223) B1816223
theorem B13778099 : Blo 1209422 13778099 := bstep (se 1 (by rfl) ⟨10333574, by rfl⟩ : syracuseStep 13778099 = 20667149) B20667149
theorem B9323045 : Blo 1209422 9323045 := bstep (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) B1748071
theorem B7865483 : Blo 1209422 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B9185399 : Blo 1209422 9185399 := bstep (se 1 (by rfl) ⟨6889049, by rfl⟩ : syracuseStep 9185399 = 13778099) B13778099
theorem B10333817 : Blo 1209422 10333817 := bstep (se 2 (by rfl) ⟨3875181, by rfl⟩ : syracuseStep 10333817 = 7750363) B7750363
theorem B1815167 : Blo 1209422 1815167 := bstep (se 1 (by rfl) ⟨1361375, by rfl⟩ : syracuseStep 1815167 = 2722751) B2722751
theorem B1209583 : Blo 1209422 1209583 := bstep (se 1 (by rfl) ⟨907187, by rfl⟩ : syracuseStep 1209583 = 1814375) B1814375
theorem B1815887 : Blo 1209422 1815887 := bstep (se 1 (by rfl) ⟨1361915, by rfl⟩ : syracuseStep 1815887 = 2723831) B2723831
theorem B4085531 : Blo 1209422 4085531 := bstep (se 1 (by rfl) ⟨3064148, by rfl⟩ : syracuseStep 4085531 = 6128297) B6128297
theorem B1210459 : Blo 1209422 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B33142891 : Blo 1209422 33142891 := bstep (se 1 (by rfl) ⟨24857168, by rfl⟩ : syracuseStep 33142891 = 49714337) B49714337
theorem B4086071 : Blo 1209422 4086071 := bstep (se 1 (by rfl) ⟨3064553, by rfl⟩ : syracuseStep 4086071 = 6129107) B6129107
theorem B9199007 : Blo 1209422 9199007 := bstep (se 1 (by rfl) ⟨6899255, by rfl⟩ : syracuseStep 9199007 = 13798511) B13798511
theorem B198877031 : Blo 1209422 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B44190521 : Blo 1209422 44190521 := bstep (se 2 (by rfl) ⟨16571445, by rfl⟩ : syracuseStep 44190521 = 33142891) B33142891
theorem B20974621 : Blo 1209422 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B2723687 : Blo 1209422 2723687 := bstep (se 1 (by rfl) ⟨2042765, by rfl⟩ : syracuseStep 2723687 = 4085531) B4085531
theorem B6123599 : Blo 1209422 6123599 := bstep (se 1 (by rfl) ⟨4592699, by rfl⟩ : syracuseStep 6123599 = 9185399) B9185399
theorem B2724047 : Blo 1209422 2724047 := bstep (se 1 (by rfl) ⟨2043035, by rfl⟩ : syracuseStep 2724047 = 4086071) B4086071
theorem B6132671 : Blo 1209422 6132671 := bstep (se 1 (by rfl) ⟨4599503, by rfl⟩ : syracuseStep 6132671 = 9199007) B9199007
theorem B132584687 : Blo 1209422 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B6215363 : Blo 1209422 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B1210111 : Blo 1209422 1210111 := bstep (se 1 (by rfl) ⟨907583, by rfl⟩ : syracuseStep 1210111 = 1815167) B1815167
theorem B1210591 : Blo 1209422 1210591 := bstep (se 1 (by rfl) ⟨907943, by rfl⟩ : syracuseStep 1210591 = 1815887) B1815887
theorem B6889211 : Blo 1209422 6889211 := bstep (se 1 (by rfl) ⟨5166908, by rfl⟩ : syracuseStep 6889211 = 10333817) B10333817
theorem B4088447 : Blo 1209422 4088447 := bstep (se 1 (by rfl) ⟨3066335, by rfl⟩ : syracuseStep 4088447 = 6132671) B6132671
theorem B29460347 : Blo 1209422 29460347 := bstep (se 1 (by rfl) ⟨22095260, by rfl⟩ : syracuseStep 29460347 = 44190521) B44190521
theorem B4082399 : Blo 1209422 4082399 := bstep (se 1 (by rfl) ⟨3061799, by rfl⟩ : syracuseStep 4082399 = 6123599) B6123599
theorem B4592807 : Blo 1209422 4592807 := bstep (se 1 (by rfl) ⟨3444605, by rfl⟩ : syracuseStep 4592807 = 6889211) B6889211
theorem B1815791 : Blo 1209422 1815791 := bstep (se 1 (by rfl) ⟨1361843, by rfl⟩ : syracuseStep 1815791 = 2723687) B2723687
theorem B1816031 : Blo 1209422 1816031 := bstep (se 1 (by rfl) ⟨1362023, by rfl⟩ : syracuseStep 1816031 = 2724047) B2724047
theorem B88389791 : Blo 1209422 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B4143575 : Blo 1209422 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B27966161 : Blo 1209422 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B58926527 : Blo 1209422 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B2762383 : Blo 1209422 2762383 := bstep (se 1 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 2762383 = 4143575) B4143575
theorem B2721599 : Blo 1209422 2721599 := bstep (se 1 (by rfl) ⟨2041199, by rfl⟩ : syracuseStep 2721599 = 4082399) B4082399
theorem B19640231 : Blo 1209422 19640231 := bstep (se 1 (by rfl) ⟨14730173, by rfl⟩ : syracuseStep 19640231 = 29460347) B29460347
theorem B2725631 : Blo 1209422 2725631 := bstep (se 1 (by rfl) ⟨2044223, by rfl⟩ : syracuseStep 2725631 = 4088447) B4088447
theorem B3061871 : Blo 1209422 3061871 := bstep (se 1 (by rfl) ⟨2296403, by rfl⟩ : syracuseStep 3061871 = 4592807) B4592807
theorem B1210527 : Blo 1209422 1210527 := bstep (se 1 (by rfl) ⟨907895, by rfl⟩ : syracuseStep 1210527 = 1815791) B1815791
theorem B1210687 : Blo 1209422 1210687 := bstep (se 1 (by rfl) ⟨908015, by rfl⟩ : syracuseStep 1210687 = 1816031) B1816031
theorem B18644107 : Blo 1209422 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B2041247 : Blo 1209422 2041247 := bstep (se 1 (by rfl) ⟨1530935, by rfl⟩ : syracuseStep 2041247 = 3061871) B3061871
theorem B13093487 : Blo 1209422 13093487 := bstep (se 1 (by rfl) ⟨9820115, by rfl⟩ : syracuseStep 13093487 = 19640231) B19640231
theorem B39284351 : Blo 1209422 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B1814399 : Blo 1209422 1814399 := bstep (se 1 (by rfl) ⟨1360799, by rfl⟩ : syracuseStep 1814399 = 2721599) B2721599
theorem B24858809 : Blo 1209422 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B3683177 : Blo 1209422 3683177 := bstep (se 2 (by rfl) ⟨1381191, by rfl⟩ : syracuseStep 3683177 = 2762383) B2762383
theorem B1817087 : Blo 1209422 1817087 := bstep (se 1 (by rfl) ⟨1362815, by rfl⟩ : syracuseStep 1817087 = 2725631) B2725631
theorem B16572539 : Blo 1209422 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B1360831 : Blo 1209422 1360831 := bstep (se 1 (by rfl) ⟨1020623, by rfl⟩ : syracuseStep 1360831 = 2041247) B2041247
theorem B8728991 : Blo 1209422 8728991 := bstep (se 1 (by rfl) ⟨6546743, by rfl⟩ : syracuseStep 8728991 = 13093487) B13093487
theorem B1209599 : Blo 1209422 1209599 := bstep (se 1 (by rfl) ⟨907199, by rfl⟩ : syracuseStep 1209599 = 1814399) B1814399
theorem B2455451 : Blo 1209422 2455451 := bstep (se 1 (by rfl) ⟨1841588, by rfl⟩ : syracuseStep 2455451 = 3683177) B3683177
theorem B1211391 : Blo 1209422 1211391 := bstep (se 1 (by rfl) ⟨908543, by rfl⟩ : syracuseStep 1211391 = 1817087) B1817087
theorem B26189567 : Blo 1209422 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B17459711 : Blo 1209422 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B5819327 : Blo 1209422 5819327 := bstep (se 1 (by rfl) ⟨4364495, by rfl⟩ : syracuseStep 5819327 = 8728991) B8728991
theorem B1814441 : Blo 1209422 1814441 := bstep (se 2 (by rfl) ⟨680415, by rfl⟩ : syracuseStep 1814441 = 1360831) B1360831
theorem B11048359 : Blo 1209422 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B1636967 : Blo 1209422 1636967 := bstep (se 1 (by rfl) ⟨1227725, by rfl⟩ : syracuseStep 1636967 = 2455451) B2455451
theorem B14731145 : Blo 1209422 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B3879551 : Blo 1209422 3879551 := bstep (se 1 (by rfl) ⟨2909663, by rfl⟩ : syracuseStep 3879551 = 5819327) B5819327
theorem B1209627 : Blo 1209422 1209627 := bstep (se 1 (by rfl) ⟨907220, by rfl⟩ : syracuseStep 1209627 = 1814441) B1814441
theorem B4365245 : Blo 1209422 4365245 := bstep (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) B1636967
theorem B11639807 : Blo 1209422 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B2910163 : Blo 1209422 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B7759871 : Blo 1209422 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B2586367 : Blo 1209422 2586367 := bstep (se 1 (by rfl) ⟨1939775, by rfl⟩ : syracuseStep 2586367 = 3879551) B3879551
theorem B9820763 : Blo 1209422 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B6547175 : Blo 1209422 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B5173247 : Blo 1209422 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B3880217 : Blo 1209422 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B3448489 : Blo 1209422 3448489 := bstep (se 2 (by rfl) ⟨1293183, by rfl⟩ : syracuseStep 3448489 = 2586367) B2586367
theorem B4597985 : Blo 1209422 4597985 := bstep (se 2 (by rfl) ⟨1724244, by rfl⟩ : syracuseStep 4597985 = 3448489) B3448489
theorem B2586811 : Blo 1209422 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B4364783 : Blo 1209422 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B3448831 : Blo 1209422 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B3449081 : Blo 1209422 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B3065323 : Blo 1209422 3065323 := bstep (se 1 (by rfl) ⟨2298992, by rfl⟩ : syracuseStep 3065323 = 4597985) B4597985
theorem B2909855 : Blo 1209422 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B4598441 : Blo 1209422 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B7759613 : Blo 1209422 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B3065627 : Blo 1209422 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B9197549 : Blo 1209422 9197549 := bstep (se 3 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 9197549 = 3449081) B3449081
theorem B4087097 : Blo 1209422 4087097 := bstep (se 2 (by rfl) ⟨1532661, by rfl⟩ : syracuseStep 4087097 = 3065323) B3065323
theorem B5173075 : Blo 1209422 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B2043751 : Blo 1209422 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B6131699 : Blo 1209422 6131699 := bstep (se 1 (by rfl) ⟨4598774, by rfl⟩ : syracuseStep 6131699 = 9197549) B9197549
theorem B2724731 : Blo 1209422 2724731 := bstep (se 1 (by rfl) ⟨2043548, by rfl⟩ : syracuseStep 2724731 = 4087097) B4087097
theorem B4087799 : Blo 1209422 4087799 := bstep (se 1 (by rfl) ⟨3065849, by rfl⟩ : syracuseStep 4087799 = 6131699) B6131699
theorem B2725001 : Blo 1209422 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B1816487 : Blo 1209422 1816487 := bstep (se 1 (by rfl) ⟨1362365, by rfl⟩ : syracuseStep 1816487 = 2724731) B2724731
theorem B6897433 : Blo 1209422 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B9196577 : Blo 1209422 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B2725199 : Blo 1209422 2725199 := bstep (se 1 (by rfl) ⟨2043899, by rfl⟩ : syracuseStep 2725199 = 4087799) B4087799
theorem B1816667 : Blo 1209422 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B1210991 : Blo 1209422 1210991 := bstep (se 1 (by rfl) ⟨908243, by rfl⟩ : syracuseStep 1210991 = 1816487) B1816487
theorem B6131051 : Blo 1209422 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B1816799 : Blo 1209422 1816799 := bstep (se 1 (by rfl) ⟨1362599, by rfl⟩ : syracuseStep 1816799 = 2725199) B2725199
theorem B1211111 : Blo 1209422 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B1211199 : Blo 1209422 1211199 := bstep (se 1 (by rfl) ⟨908399, by rfl⟩ : syracuseStep 1211199 = 1816799) B1816799
theorem B4087367 : Blo 1209422 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B2724911 : Blo 1209422 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B1816607 : Blo 1209422 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B1211071 : Blo 1209422 1211071 := bstep (se 1 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 1211071 = 1816607) B1816607

theorem C0 (j : ℕ) (h1 : 302355 ≤ j) (h2 : j ≤ 302854) : Blo 1209422 (4 * j + 3) := by
  interval_cases j
  · exact B1209423
  · exact B1209427
  · exact B1209431
  · exact B1209435
  · exact B1209439
  · exact B1209443
  · exact B1209447
  · exact B1209451
  · exact B1209455
  · exact B1209459
  · exact B1209463
  · exact B1209467
  · exact B1209471
  · exact B1209475
  · exact B1209479
  · exact B1209483
  · exact B1209487
  · exact B1209491
  · exact B1209495
  · exact B1209499
  · exact B1209503
  · exact B1209507
  · exact B1209511
  · exact B1209515
  · exact B1209519
  · exact B1209523
  · exact B1209527
  · exact B1209531
  · exact B1209535
  · exact B1209539
  · exact B1209543
  · exact B1209547
  · exact B1209551
  · exact B1209555
  · exact B1209559
  · exact B1209563
  · exact B1209567
  · exact B1209571
  · exact B1209575
  · exact B1209579
  · exact B1209583
  · exact B1209587
  · exact B1209591
  · exact B1209595
  · exact B1209599
  · exact B1209603
  · exact B1209607
  · exact B1209611
  · exact B1209615
  · exact B1209619
  · exact B1209623
  · exact B1209627
  · exact B1209631
  · exact B1209635
  · exact B1209639
  · exact B1209643
  · exact B1209647
  · exact B1209651
  · exact B1209655
  · exact B1209659
  · exact B1209663
  · exact B1209667
  · exact B1209671
  · exact B1209675
  · exact B1209679
  · exact B1209683
  · exact B1209687
  · exact B1209691
  · exact B1209695
  · exact B1209699
  · exact B1209703
  · exact B1209707
  · exact B1209711
  · exact B1209715
  · exact B1209719
  · exact B1209723
  · exact B1209727
  · exact B1209731
  · exact B1209735
  · exact B1209739
  · exact B1209743
  · exact B1209747
  · exact B1209751
  · exact B1209755
  · exact B1209759
  · exact B1209763
  · exact B1209767
  · exact B1209771
  · exact B1209775
  · exact B1209779
  · exact B1209783
  · exact B1209787
  · exact B1209791
  · exact B1209795
  · exact B1209799
  · exact B1209803
  · exact B1209807
  · exact B1209811
  · exact B1209815
  · exact B1209819
  · exact B1209823
  · exact B1209827
  · exact B1209831
  · exact B1209835
  · exact B1209839
  · exact B1209843
  · exact B1209847
  · exact B1209851
  · exact B1209855
  · exact B1209859
  · exact B1209863
  · exact B1209867
  · exact B1209871
  · exact B1209875
  · exact B1209879
  · exact B1209883
  · exact B1209887
  · exact B1209891
  · exact B1209895
  · exact B1209899
  · exact B1209903
  · exact B1209907
  · exact B1209911
  · exact B1209915
  · exact B1209919
  · exact B1209923
  · exact B1209927
  · exact B1209931
  · exact B1209935
  · exact B1209939
  · exact B1209943
  · exact B1209947
  · exact B1209951
  · exact B1209955
  · exact B1209959
  · exact B1209963
  · exact B1209967
  · exact B1209971
  · exact B1209975
  · exact B1209979
  · exact B1209983
  · exact B1209987
  · exact B1209991
  · exact B1209995
  · exact B1209999
  · exact B1210003
  · exact B1210007
  · exact B1210011
  · exact B1210015
  · exact B1210019
  · exact B1210023
  · exact B1210027
  · exact B1210031
  · exact B1210035
  · exact B1210039
  · exact B1210043
  · exact B1210047
  · exact B1210051
  · exact B1210055
  · exact B1210059
  · exact B1210063
  · exact B1210067
  · exact B1210071
  · exact B1210075
  · exact B1210079
  · exact B1210083
  · exact B1210087
  · exact B1210091
  · exact B1210095
  · exact B1210099
  · exact B1210103
  · exact B1210107
  · exact B1210111
  · exact B1210115
  · exact B1210119
  · exact B1210123
  · exact B1210127
  · exact B1210131
  · exact B1210135
  · exact B1210139
  · exact B1210143
  · exact B1210147
  · exact B1210151
  · exact B1210155
  · exact B1210159
  · exact B1210163
  · exact B1210167
  · exact B1210171
  · exact B1210175
  · exact B1210179
  · exact B1210183
  · exact B1210187
  · exact B1210191
  · exact B1210195
  · exact B1210199
  · exact B1210203
  · exact B1210207
  · exact B1210211
  · exact B1210215
  · exact B1210219
  · exact B1210223
  · exact B1210227
  · exact B1210231
  · exact B1210235
  · exact B1210239
  · exact B1210243
  · exact B1210247
  · exact B1210251
  · exact B1210255
  · exact B1210259
  · exact B1210263
  · exact B1210267
  · exact B1210271
  · exact B1210275
  · exact B1210279
  · exact B1210283
  · exact B1210287
  · exact B1210291
  · exact B1210295
  · exact B1210299
  · exact B1210303
  · exact B1210307
  · exact B1210311
  · exact B1210315
  · exact B1210319
  · exact B1210323
  · exact B1210327
  · exact B1210331
  · exact B1210335
  · exact B1210339
  · exact B1210343
  · exact B1210347
  · exact B1210351
  · exact B1210355
  · exact B1210359
  · exact B1210363
  · exact B1210367
  · exact B1210371
  · exact B1210375
  · exact B1210379
  · exact B1210383
  · exact B1210387
  · exact B1210391
  · exact B1210395
  · exact B1210399
  · exact B1210403
  · exact B1210407
  · exact B1210411
  · exact B1210415
  · exact B1210419
  · exact B1210423
  · exact B1210427
  · exact B1210431
  · exact B1210435
  · exact B1210439
  · exact B1210443
  · exact B1210447
  · exact B1210451
  · exact B1210455
  · exact B1210459
  · exact B1210463
  · exact B1210467
  · exact B1210471
  · exact B1210475
  · exact B1210479
  · exact B1210483
  · exact B1210487
  · exact B1210491
  · exact B1210495
  · exact B1210499
  · exact B1210503
  · exact B1210507
  · exact B1210511
  · exact B1210515
  · exact B1210519
  · exact B1210523
  · exact B1210527
  · exact B1210531
  · exact B1210535
  · exact B1210539
  · exact B1210543
  · exact B1210547
  · exact B1210551
  · exact B1210555
  · exact B1210559
  · exact B1210563
  · exact B1210567
  · exact B1210571
  · exact B1210575
  · exact B1210579
  · exact B1210583
  · exact B1210587
  · exact B1210591
  · exact B1210595
  · exact B1210599
  · exact B1210603
  · exact B1210607
  · exact B1210611
  · exact B1210615
  · exact B1210619
  · exact B1210623
  · exact B1210627
  · exact B1210631
  · exact B1210635
  · exact B1210639
  · exact B1210643
  · exact B1210647
  · exact B1210651
  · exact B1210655
  · exact B1210659
  · exact B1210663
  · exact B1210667
  · exact B1210671
  · exact B1210675
  · exact B1210679
  · exact B1210683
  · exact B1210687
  · exact B1210691
  · exact B1210695
  · exact B1210699
  · exact B1210703
  · exact B1210707
  · exact B1210711
  · exact B1210715
  · exact B1210719
  · exact B1210723
  · exact B1210727
  · exact B1210731
  · exact B1210735
  · exact B1210739
  · exact B1210743
  · exact B1210747
  · exact B1210751
  · exact B1210755
  · exact B1210759
  · exact B1210763
  · exact B1210767
  · exact B1210771
  · exact B1210775
  · exact B1210779
  · exact B1210783
  · exact B1210787
  · exact B1210791
  · exact B1210795
  · exact B1210799
  · exact B1210803
  · exact B1210807
  · exact B1210811
  · exact B1210815
  · exact B1210819
  · exact B1210823
  · exact B1210827
  · exact B1210831
  · exact B1210835
  · exact B1210839
  · exact B1210843
  · exact B1210847
  · exact B1210851
  · exact B1210855
  · exact B1210859
  · exact B1210863
  · exact B1210867
  · exact B1210871
  · exact B1210875
  · exact B1210879
  · exact B1210883
  · exact B1210887
  · exact B1210891
  · exact B1210895
  · exact B1210899
  · exact B1210903
  · exact B1210907
  · exact B1210911
  · exact B1210915
  · exact B1210919
  · exact B1210923
  · exact B1210927
  · exact B1210931
  · exact B1210935
  · exact B1210939
  · exact B1210943
  · exact B1210947
  · exact B1210951
  · exact B1210955
  · exact B1210959
  · exact B1210963
  · exact B1210967
  · exact B1210971
  · exact B1210975
  · exact B1210979
  · exact B1210983
  · exact B1210987
  · exact B1210991
  · exact B1210995
  · exact B1210999
  · exact B1211003
  · exact B1211007
  · exact B1211011
  · exact B1211015
  · exact B1211019
  · exact B1211023
  · exact B1211027
  · exact B1211031
  · exact B1211035
  · exact B1211039
  · exact B1211043
  · exact B1211047
  · exact B1211051
  · exact B1211055
  · exact B1211059
  · exact B1211063
  · exact B1211067
  · exact B1211071
  · exact B1211075
  · exact B1211079
  · exact B1211083
  · exact B1211087
  · exact B1211091
  · exact B1211095
  · exact B1211099
  · exact B1211103
  · exact B1211107
  · exact B1211111
  · exact B1211115
  · exact B1211119
  · exact B1211123
  · exact B1211127
  · exact B1211131
  · exact B1211135
  · exact B1211139
  · exact B1211143
  · exact B1211147
  · exact B1211151
  · exact B1211155
  · exact B1211159
  · exact B1211163
  · exact B1211167
  · exact B1211171
  · exact B1211175
  · exact B1211179
  · exact B1211183
  · exact B1211187
  · exact B1211191
  · exact B1211195
  · exact B1211199
  · exact B1211203
  · exact B1211207
  · exact B1211211
  · exact B1211215
  · exact B1211219
  · exact B1211223
  · exact B1211227
  · exact B1211231
  · exact B1211235
  · exact B1211239
  · exact B1211243
  · exact B1211247
  · exact B1211251
  · exact B1211255
  · exact B1211259
  · exact B1211263
  · exact B1211267
  · exact B1211271
  · exact B1211275
  · exact B1211279
  · exact B1211283
  · exact B1211287
  · exact B1211291
  · exact B1211295
  · exact B1211299
  · exact B1211303
  · exact B1211307
  · exact B1211311
  · exact B1211315
  · exact B1211319
  · exact B1211323
  · exact B1211327
  · exact B1211331
  · exact B1211335
  · exact B1211339
  · exact B1211343
  · exact B1211347
  · exact B1211351
  · exact B1211355
  · exact B1211359
  · exact B1211363
  · exact B1211367
  · exact B1211371
  · exact B1211375
  · exact B1211379
  · exact B1211383
  · exact B1211387
  · exact B1211391
  · exact B1211395
  · exact B1211399
  · exact B1211403
  · exact B1211407
  · exact B1211411
  · exact B1211415
  · exact B1211419

theorem solution (m : ℕ) (hlo : 1209422 ≤ m) (hhi : m ≤ 1211422) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 302355 ≤ j := by omega
    have hj2 : j ≤ 302854 := by omega
    have hb : Blo 1209422 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
