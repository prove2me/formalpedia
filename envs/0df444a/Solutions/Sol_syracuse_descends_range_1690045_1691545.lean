-- Prove2me | solution 1 for syracuse_descends_range_1690045_1691545
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:23:57.442326+00:00
-- url     : https://prove2.me/submissions/0d7c5165-e8c9-4e86-ad17-42849bef426b

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


theorem B2031689 : Blo 1690045 2031689 := bbase (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) (by norm_num)
theorem B2285677 : Blo 1690045 2285677 := bbase (se 3 (by rfl) ⟨428564, by rfl⟩ : syracuseStep 2285677 = 857129) (by norm_num)
theorem B4759717 : Blo 1690045 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B9625877 : Blo 1690045 9625877 := bbase (se 6 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 9625877 = 451213) (by norm_num)
theorem B10281269 : Blo 1690045 10281269 := bbase (se 5 (by rfl) ⟨481934, by rfl⟩ : syracuseStep 10281269 = 963869) (by norm_num)
theorem B16253237 : Blo 1690045 16253237 := bbase (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) (by norm_num)
theorem B5489093 : Blo 1690045 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B54821461 : Blo 1690045 54821461 := bbase (se 8 (by rfl) ⟨321219, by rfl⟩ : syracuseStep 54821461 = 642439) (by norm_num)
theorem B2892469 : Blo 1690045 2892469 := bbase (se 5 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 2892469 = 271169) (by norm_num)
theorem B6095573 : Blo 1690045 6095573 := bbase (se 7 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 6095573 = 142865) (by norm_num)
theorem B1901317 : Blo 1690045 1901317 := bbase (se 4 (by rfl) ⟨178248, by rfl⟩ : syracuseStep 1901317 = 356497) (by norm_num)
theorem B1901353 : Blo 1690045 1901353 := bbase (se 2 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 1901353 = 1426015) (by norm_num)
theorem B1901389 : Blo 1690045 1901389 := bbase (se 3 (by rfl) ⟨356510, by rfl⟩ : syracuseStep 1901389 = 713021) (by norm_num)
theorem B2138977 : Blo 1690045 2138977 := bbase (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) (by norm_num)
theorem B1901425 : Blo 1690045 1901425 := bbase (se 2 (by rfl) ⟨713034, by rfl⟩ : syracuseStep 1901425 = 1426069) (by norm_num)
theorem B1901461 : Blo 1690045 1901461 := bbase (se 6 (by rfl) ⟨44565, by rfl⟩ : syracuseStep 1901461 = 89131) (by norm_num)
theorem B2892701 : Blo 1690045 2892701 := bbase (se 3 (by rfl) ⟨542381, by rfl⟩ : syracuseStep 2892701 = 1084763) (by norm_num)
theorem B2605997 : Blo 1690045 2605997 := bbase (se 3 (by rfl) ⟨488624, by rfl⟩ : syracuseStep 2605997 = 977249) (by norm_num)
theorem B1901497 : Blo 1690045 1901497 := bbase (se 2 (by rfl) ⟨713061, by rfl⟩ : syracuseStep 1901497 = 1426123) (by norm_num)
theorem B1901533 : Blo 1690045 1901533 := bbase (se 3 (by rfl) ⟨356537, by rfl⟩ : syracuseStep 1901533 = 713075) (by norm_num)
theorem B1901569 : Blo 1690045 1901569 := bbase (se 2 (by rfl) ⟨713088, by rfl⟩ : syracuseStep 1901569 = 1426177) (by norm_num)
theorem B2139149 : Blo 1690045 2139149 := bbase (se 3 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 2139149 = 802181) (by norm_num)
theorem B1901605 : Blo 1690045 1901605 := bbase (se 4 (by rfl) ⟨178275, by rfl⟩ : syracuseStep 1901605 = 356551) (by norm_num)
theorem B2139205 : Blo 1690045 2139205 := bbase (se 4 (by rfl) ⟨200550, by rfl⟩ : syracuseStep 2139205 = 401101) (by norm_num)
theorem B1901641 : Blo 1690045 1901641 := bbase (se 2 (by rfl) ⟨713115, by rfl⟩ : syracuseStep 1901641 = 1426231) (by norm_num)
theorem B1901677 : Blo 1690045 1901677 := bbase (se 3 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 1901677 = 713129) (by norm_num)
theorem B6095989 : Blo 1690045 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B6096005 : Blo 1690045 6096005 := bbase (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) (by norm_num)
theorem B1901713 : Blo 1690045 1901713 := bbase (se 2 (by rfl) ⟨713142, by rfl⟩ : syracuseStep 1901713 = 1426285) (by norm_num)
theorem B2139301 : Blo 1690045 2139301 := bbase (se 4 (by rfl) ⟨200559, by rfl⟩ : syracuseStep 2139301 = 401119) (by norm_num)
theorem B1901749 : Blo 1690045 1901749 := bbase (se 5 (by rfl) ⟨89144, by rfl⟩ : syracuseStep 1901749 = 178289) (by norm_num)
theorem B8561861 : Blo 1690045 8561861 := bbase (se 4 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 8561861 = 1605349) (by norm_num)
theorem B1901785 : Blo 1690045 1901785 := bbase (se 2 (by rfl) ⟨713169, by rfl⟩ : syracuseStep 1901785 = 1426339) (by norm_num)
theorem B2852077 : Blo 1690045 2852077 := bbase (se 3 (by rfl) ⟨534764, by rfl⟩ : syracuseStep 2852077 = 1069529) (by norm_num)
theorem B1901821 : Blo 1690045 1901821 := bbase (se 3 (by rfl) ⟨356591, by rfl⟩ : syracuseStep 1901821 = 713183) (by norm_num)
theorem B1901857 : Blo 1690045 1901857 := bbase (se 2 (by rfl) ⟨713196, by rfl⟩ : syracuseStep 1901857 = 1426393) (by norm_num)
theorem B2852165 : Blo 1690045 2852165 := bbase (se 4 (by rfl) ⟨267390, by rfl⟩ : syracuseStep 2852165 = 534781) (by norm_num)
theorem B1901893 : Blo 1690045 1901893 := bbase (se 4 (by rfl) ⟨178302, by rfl⟩ : syracuseStep 1901893 = 356605) (by norm_num)
theorem B2139473 : Blo 1690045 2139473 := bbase (se 2 (by rfl) ⟨802302, by rfl⟩ : syracuseStep 2139473 = 1604605) (by norm_num)
theorem B1901929 : Blo 1690045 1901929 := bbase (se 2 (by rfl) ⟨713223, by rfl⟩ : syracuseStep 1901929 = 1426447) (by norm_num)
theorem B2139529 : Blo 1690045 2139529 := bbase (se 2 (by rfl) ⟨802323, by rfl⟩ : syracuseStep 2139529 = 1604647) (by norm_num)
theorem B1901965 : Blo 1690045 1901965 := bbase (se 3 (by rfl) ⟨356618, by rfl⟩ : syracuseStep 1901965 = 713237) (by norm_num)
theorem B6096293 : Blo 1690045 6096293 := bbase (se 4 (by rfl) ⟨571527, by rfl⟩ : syracuseStep 6096293 = 1143055) (by norm_num)
theorem B1902001 : Blo 1690045 1902001 := bbase (se 2 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 1902001 = 1426501) (by norm_num)
theorem B2852293 : Blo 1690045 2852293 := bbase (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) (by norm_num)
theorem B21661141 : Blo 1690045 21661141 := bbase (se 7 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 21661141 = 507683) (by norm_num)
theorem B1902037 : Blo 1690045 1902037 := bbase (se 7 (by rfl) ⟨22289, by rfl⟩ : syracuseStep 1902037 = 44579) (by norm_num)
theorem B1713625 : Blo 1690045 1713625 := bbase (se 2 (by rfl) ⟨642609, by rfl⟩ : syracuseStep 1713625 = 1285219) (by norm_num)
theorem B2139625 : Blo 1690045 2139625 := bbase (se 2 (by rfl) ⟨802359, by rfl⟩ : syracuseStep 2139625 = 1604719) (by norm_num)
theorem B1902073 : Blo 1690045 1902073 := bbase (se 2 (by rfl) ⟨713277, by rfl⟩ : syracuseStep 1902073 = 1426555) (by norm_num)
theorem B2852381 : Blo 1690045 2852381 := bbase (se 3 (by rfl) ⟨534821, by rfl⟩ : syracuseStep 2852381 = 1069643) (by norm_num)
theorem B1902109 : Blo 1690045 1902109 := bbase (se 3 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 1902109 = 713291) (by norm_num)
theorem B3802661 : Blo 1690045 3802661 := bbase (se 4 (by rfl) ⟨356499, by rfl⟩ : syracuseStep 3802661 = 712999) (by norm_num)
theorem B1902145 : Blo 1690045 1902145 := bbase (se 2 (by rfl) ⟨713304, by rfl⟩ : syracuseStep 1902145 = 1426609) (by norm_num)
theorem B1902181 : Blo 1690045 1902181 := bbase (se 4 (by rfl) ⟨178329, by rfl⟩ : syracuseStep 1902181 = 356659) (by norm_num)
theorem B3802733 : Blo 1690045 3802733 := bbase (se 3 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 3802733 = 1426025) (by norm_num)
theorem B1902217 : Blo 1690045 1902217 := bbase (se 2 (by rfl) ⟨713331, by rfl⟩ : syracuseStep 1902217 = 1426663) (by norm_num)
theorem B2139797 : Blo 1690045 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B2852509 : Blo 1690045 2852509 := bbase (se 3 (by rfl) ⟨534845, by rfl⟩ : syracuseStep 2852509 = 1069691) (by norm_num)
theorem B1902253 : Blo 1690045 1902253 := bbase (se 3 (by rfl) ⟨356672, by rfl⟩ : syracuseStep 1902253 = 713345) (by norm_num)
theorem B3802805 : Blo 1690045 3802805 := bbase (se 5 (by rfl) ⟨178256, by rfl⟩ : syracuseStep 3802805 = 356513) (by norm_num)
theorem B5416645 : Blo 1690045 5416645 := bbase (se 4 (by rfl) ⟨507810, by rfl⟩ : syracuseStep 5416645 = 1015621) (by norm_num)
theorem B2139853 : Blo 1690045 2139853 := bbase (se 3 (by rfl) ⟨401222, by rfl⟩ : syracuseStep 2139853 = 802445) (by norm_num)
theorem B1902289 : Blo 1690045 1902289 := bbase (se 2 (by rfl) ⟨713358, by rfl⟩ : syracuseStep 1902289 = 1426717) (by norm_num)
theorem B4278005 : Blo 1690045 4278005 := bbase (se 5 (by rfl) ⟨200531, by rfl⟩ : syracuseStep 4278005 = 401063) (by norm_num)
theorem B2852597 : Blo 1690045 2852597 := bbase (se 5 (by rfl) ⟨133715, by rfl⟩ : syracuseStep 2852597 = 267431) (by norm_num)
theorem B1902325 : Blo 1690045 1902325 := bbase (se 5 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 1902325 = 178343) (by norm_num)
theorem B3802877 : Blo 1690045 3802877 := bbase (se 3 (by rfl) ⟨713039, by rfl⟩ : syracuseStep 3802877 = 1426079) (by norm_num)
theorem B15255317 : Blo 1690045 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B1902361 : Blo 1690045 1902361 := bbase (se 2 (by rfl) ⟨713385, by rfl⟩ : syracuseStep 1902361 = 1426771) (by norm_num)
theorem B2139949 : Blo 1690045 2139949 := bbase (se 3 (by rfl) ⟨401240, by rfl⟩ : syracuseStep 2139949 = 802481) (by norm_num)
theorem B1902397 : Blo 1690045 1902397 := bbase (se 3 (by rfl) ⟨356699, by rfl⟩ : syracuseStep 1902397 = 713399) (by norm_num)
theorem B3475261 : Blo 1690045 3475261 := bbase (se 3 (by rfl) ⟨651611, by rfl⟩ : syracuseStep 3475261 = 1303223) (by norm_num)
theorem B3802949 : Blo 1690045 3802949 := bbase (se 4 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 3802949 = 713053) (by norm_num)
theorem B1902433 : Blo 1690045 1902433 := bbase (se 2 (by rfl) ⟨713412, by rfl⟩ : syracuseStep 1902433 = 1426825) (by norm_num)
theorem B2852725 : Blo 1690045 2852725 := bbase (se 5 (by rfl) ⟨133721, by rfl⟩ : syracuseStep 2852725 = 267443) (by norm_num)
theorem B1902469 : Blo 1690045 1902469 := bbase (se 4 (by rfl) ⟨178356, by rfl⟩ : syracuseStep 1902469 = 356713) (by norm_num)
theorem B3803021 : Blo 1690045 3803021 := bbase (se 3 (by rfl) ⟨713066, by rfl⟩ : syracuseStep 3803021 = 1426133) (by norm_num)
theorem B1902505 : Blo 1690045 1902505 := bbase (se 2 (by rfl) ⟨713439, by rfl⟩ : syracuseStep 1902505 = 1426879) (by norm_num)
theorem B4278197 : Blo 1690045 4278197 := bbase (se 5 (by rfl) ⟨200540, by rfl⟩ : syracuseStep 4278197 = 401081) (by norm_num)
theorem B2852813 : Blo 1690045 2852813 := bbase (se 3 (by rfl) ⟨534902, by rfl⟩ : syracuseStep 2852813 = 1069805) (by norm_num)
theorem B1902541 : Blo 1690045 1902541 := bbase (se 3 (by rfl) ⟨356726, by rfl⟩ : syracuseStep 1902541 = 713453) (by norm_num)
theorem B3803093 : Blo 1690045 3803093 := bbase (se 7 (by rfl) ⟨44567, by rfl⟩ : syracuseStep 3803093 = 89135) (by norm_num)
theorem B2140121 : Blo 1690045 2140121 := bbase (se 2 (by rfl) ⟨802545, by rfl⟩ : syracuseStep 2140121 = 1605091) (by norm_num)
theorem B1902577 : Blo 1690045 1902577 := bbase (se 2 (by rfl) ⟨713466, by rfl⟩ : syracuseStep 1902577 = 1426933) (by norm_num)
theorem B2140177 : Blo 1690045 2140177 := bbase (se 2 (by rfl) ⟨802566, by rfl⟩ : syracuseStep 2140177 = 1605133) (by norm_num)
theorem B1902613 : Blo 1690045 1902613 := bbase (se 6 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 1902613 = 89185) (by norm_num)
theorem B3803165 : Blo 1690045 3803165 := bbase (se 3 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 3803165 = 1426187) (by norm_num)
theorem B1902649 : Blo 1690045 1902649 := bbase (se 2 (by rfl) ⟨713493, by rfl⟩ : syracuseStep 1902649 = 1426987) (by norm_num)
theorem B2852941 : Blo 1690045 2852941 := bbase (se 3 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 2852941 = 1069853) (by norm_num)
theorem B1902685 : Blo 1690045 1902685 := bbase (se 3 (by rfl) ⟨356753, by rfl⟩ : syracuseStep 1902685 = 713507) (by norm_num)
theorem B3803237 : Blo 1690045 3803237 := bbase (se 4 (by rfl) ⟨356553, by rfl⟩ : syracuseStep 3803237 = 713107) (by norm_num)
theorem B2140273 : Blo 1690045 2140273 := bbase (se 2 (by rfl) ⟨802602, by rfl⟩ : syracuseStep 2140273 = 1605205) (by norm_num)
theorem B1902721 : Blo 1690045 1902721 := bbase (se 2 (by rfl) ⟨713520, by rfl⟩ : syracuseStep 1902721 = 1427041) (by norm_num)
theorem B2853029 : Blo 1690045 2853029 := bbase (se 4 (by rfl) ⟨267471, by rfl⟩ : syracuseStep 2853029 = 534943) (by norm_num)
theorem B1902757 : Blo 1690045 1902757 := bbase (se 4 (by rfl) ⟨178383, by rfl⟩ : syracuseStep 1902757 = 356767) (by norm_num)
theorem B3803309 : Blo 1690045 3803309 := bbase (se 3 (by rfl) ⟨713120, by rfl⟩ : syracuseStep 3803309 = 1426241) (by norm_num)
theorem B1902793 : Blo 1690045 1902793 := bbase (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) (by norm_num)
theorem B1902829 : Blo 1690045 1902829 := bbase (se 3 (by rfl) ⟨356780, by rfl⟩ : syracuseStep 1902829 = 713561) (by norm_num)
theorem B3803381 : Blo 1690045 3803381 := bbase (se 5 (by rfl) ⟨178283, by rfl⟩ : syracuseStep 3803381 = 356567) (by norm_num)
theorem B4278541 : Blo 1690045 4278541 := bbase (se 3 (by rfl) ⟨802226, by rfl⟩ : syracuseStep 4278541 = 1604453) (by norm_num)
theorem B1902865 : Blo 1690045 1902865 := bbase (se 2 (by rfl) ⟨713574, by rfl⟩ : syracuseStep 1902865 = 1427149) (by norm_num)
theorem B2140445 : Blo 1690045 2140445 := bbase (se 3 (by rfl) ⟨401333, by rfl⟩ : syracuseStep 2140445 = 802667) (by norm_num)
theorem B7219493 : Blo 1690045 7219493 := bbase (se 4 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 7219493 = 1353655) (by norm_num)
theorem B2853157 : Blo 1690045 2853157 := bbase (se 4 (by rfl) ⟨267483, by rfl⟩ : syracuseStep 2853157 = 534967) (by norm_num)
theorem B1902901 : Blo 1690045 1902901 := bbase (se 5 (by rfl) ⟨89198, by rfl⟩ : syracuseStep 1902901 = 178397) (by norm_num)
theorem B3803453 : Blo 1690045 3803453 := bbase (se 3 (by rfl) ⟨713147, by rfl⟩ : syracuseStep 3803453 = 1426295) (by norm_num)
theorem B11569493 : Blo 1690045 11569493 := bbase (se 10 (by rfl) ⟨16947, by rfl⟩ : syracuseStep 11569493 = 33895) (by norm_num)
theorem B2140501 : Blo 1690045 2140501 := bbase (se 10 (by rfl) ⟨3135, by rfl⟩ : syracuseStep 2140501 = 6271) (by norm_num)
theorem B1902937 : Blo 1690045 1902937 := bbase (se 2 (by rfl) ⟨713601, by rfl⟩ : syracuseStep 1902937 = 1427203) (by norm_num)
theorem B4278653 : Blo 1690045 4278653 := bbase (se 3 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 4278653 = 1604495) (by norm_num)
theorem B2853245 : Blo 1690045 2853245 := bbase (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) (by norm_num)
theorem B1902973 : Blo 1690045 1902973 := bbase (se 3 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 1902973 = 713615) (by norm_num)
theorem B3803525 : Blo 1690045 3803525 := bbase (se 4 (by rfl) ⟨356580, by rfl⟩ : syracuseStep 3803525 = 713161) (by norm_num)
theorem B5786005 : Blo 1690045 5786005 := bbase (se 6 (by rfl) ⟨135609, by rfl⟩ : syracuseStep 5786005 = 271219) (by norm_num)
theorem B9136565 : Blo 1690045 9136565 := bbase (se 5 (by rfl) ⟨428276, by rfl⟩ : syracuseStep 9136565 = 856553) (by norm_num)
theorem B9628085 : Blo 1690045 9628085 := bbase (se 5 (by rfl) ⟨451316, by rfl⟩ : syracuseStep 9628085 = 902633) (by norm_num)
theorem B2140597 : Blo 1690045 2140597 := bbase (se 5 (by rfl) ⟨100340, by rfl⟩ : syracuseStep 2140597 = 200681) (by norm_num)
theorem B3803597 : Blo 1690045 3803597 := bbase (se 3 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 3803597 = 1426349) (by norm_num)
theorem B8563157 : Blo 1690045 8563157 := bbase (se 7 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 8563157 = 200699) (by norm_num)
theorem B5704181 : Blo 1690045 5704181 := bbase (se 5 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 5704181 = 534767) (by norm_num)
theorem B2853373 : Blo 1690045 2853373 := bbase (se 3 (by rfl) ⟨535007, by rfl⟩ : syracuseStep 2853373 = 1070015) (by norm_num)
theorem B3803669 : Blo 1690045 3803669 := bbase (se 6 (by rfl) ⟨89148, by rfl⟩ : syracuseStep 3803669 = 178297) (by norm_num)
theorem B4278845 : Blo 1690045 4278845 := bbase (se 3 (by rfl) ⟨802283, by rfl⟩ : syracuseStep 4278845 = 1604567) (by norm_num)
theorem B2853461 : Blo 1690045 2853461 := bbase (se 8 (by rfl) ⟨16719, by rfl⟩ : syracuseStep 2853461 = 33439) (by norm_num)
theorem B3803741 : Blo 1690045 3803741 := bbase (se 3 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 3803741 = 1426403) (by norm_num)
theorem B2140769 : Blo 1690045 2140769 := bbase (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) (by norm_num)
theorem B1804933 : Blo 1690045 1804933 := bbase (se 4 (by rfl) ⟨169212, by rfl⟩ : syracuseStep 1804933 = 338425) (by norm_num)
theorem B4016773 : Blo 1690045 4016773 := bbase (se 4 (by rfl) ⟨376572, by rfl⟩ : syracuseStep 4016773 = 753145) (by norm_num)
theorem B2140825 : Blo 1690045 2140825 := bbase (se 2 (by rfl) ⟨802809, by rfl⟩ : syracuseStep 2140825 = 1605619) (by norm_num)
theorem B3803813 : Blo 1690045 3803813 := bbase (se 4 (by rfl) ⟨356607, by rfl⟩ : syracuseStep 3803813 = 713215) (by norm_num)
theorem B1829585 : Blo 1690045 1829585 := bbase (se 2 (by rfl) ⟨686094, by rfl⟩ : syracuseStep 1829585 = 1372189) (by norm_num)
theorem B13191893 : Blo 1690045 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B2853589 : Blo 1690045 2853589 := bbase (se 7 (by rfl) ⟨33440, by rfl⟩ : syracuseStep 2853589 = 66881) (by norm_num)
theorem B3803885 : Blo 1690045 3803885 := bbase (se 3 (by rfl) ⟨713228, by rfl⟩ : syracuseStep 3803885 = 1426457) (by norm_num)
theorem B16468757 : Blo 1690045 16468757 := bbase (se 6 (by rfl) ⟨385986, by rfl⟩ : syracuseStep 16468757 = 771973) (by norm_num)
theorem B2853677 : Blo 1690045 2853677 := bbase (se 3 (by rfl) ⟨535064, by rfl⟩ : syracuseStep 2853677 = 1070129) (by norm_num)
theorem B3803957 : Blo 1690045 3803957 := bbase (se 5 (by rfl) ⟨178310, by rfl⟩ : syracuseStep 3803957 = 356621) (by norm_num)
theorem B3804029 : Blo 1690045 3804029 := bbase (se 3 (by rfl) ⟨713255, by rfl⟩ : syracuseStep 3804029 = 1426511) (by norm_num)
theorem B4279189 : Blo 1690045 4279189 := bbase (se 6 (by rfl) ⟨100293, by rfl⟩ : syracuseStep 4279189 = 200587) (by norm_num)
theorem B5704613 : Blo 1690045 5704613 := bbase (se 4 (by rfl) ⟨534807, by rfl⟩ : syracuseStep 5704613 = 1069615) (by norm_num)
theorem B2853805 : Blo 1690045 2853805 := bbase (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) (by norm_num)
theorem B3804101 : Blo 1690045 3804101 := bbase (se 4 (by rfl) ⟨356634, by rfl⟩ : syracuseStep 3804101 = 713269) (by norm_num)
theorem B4279301 : Blo 1690045 4279301 := bbase (se 4 (by rfl) ⟨401184, by rfl⟩ : syracuseStep 4279301 = 802369) (by norm_num)
theorem B2853893 : Blo 1690045 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B3804173 : Blo 1690045 3804173 := bbase (se 3 (by rfl) ⟨713282, by rfl⟩ : syracuseStep 3804173 = 1426565) (by norm_num)
theorem B12184597 : Blo 1690045 12184597 := bbase (se 6 (by rfl) ⟨285576, by rfl⟩ : syracuseStep 12184597 = 571153) (by norm_num)
theorem B1805365 : Blo 1690045 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B3804245 : Blo 1690045 3804245 := bbase (se 8 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 3804245 = 44581) (by norm_num)
theorem B3427445 : Blo 1690045 3427445 := bbase (se 5 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 3427445 = 321323) (by norm_num)
theorem B1805437 : Blo 1690045 1805437 := bbase (se 3 (by rfl) ⟨338519, by rfl⟩ : syracuseStep 1805437 = 677039) (by norm_num)
theorem B2854021 : Blo 1690045 2854021 := bbase (se 4 (by rfl) ⟨267564, by rfl⟩ : syracuseStep 2854021 = 535129) (by norm_num)
theorem B3804317 : Blo 1690045 3804317 := bbase (se 3 (by rfl) ⟨713309, by rfl⟩ : syracuseStep 3804317 = 1426619) (by norm_num)
theorem B4279493 : Blo 1690045 4279493 := bbase (se 4 (by rfl) ⟨401202, by rfl⟩ : syracuseStep 4279493 = 802405) (by norm_num)
theorem B2854109 : Blo 1690045 2854109 := bbase (se 3 (by rfl) ⟨535145, by rfl⟩ : syracuseStep 2854109 = 1070291) (by norm_num)
theorem B3804389 : Blo 1690045 3804389 := bbase (se 4 (by rfl) ⟨356661, by rfl⟩ : syracuseStep 3804389 = 713323) (by norm_num)
theorem B3804461 : Blo 1690045 3804461 := bbase (se 3 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 3804461 = 1426673) (by norm_num)
theorem B5705045 : Blo 1690045 5705045 := bbase (se 11 (by rfl) ⟨4178, by rfl⟩ : syracuseStep 5705045 = 8357) (by norm_num)
theorem B2059609 : Blo 1690045 2059609 := bbase (se 2 (by rfl) ⟨772353, by rfl⟩ : syracuseStep 2059609 = 1544707) (by norm_num)
theorem B2854237 : Blo 1690045 2854237 := bbase (se 3 (by rfl) ⟨535169, by rfl⟩ : syracuseStep 2854237 = 1070339) (by norm_num)
theorem B3804533 : Blo 1690045 3804533 := bbase (se 5 (by rfl) ⟨178337, by rfl⟩ : syracuseStep 3804533 = 356675) (by norm_num)
theorem B2854325 : Blo 1690045 2854325 := bbase (se 5 (by rfl) ⟨133796, by rfl⟩ : syracuseStep 2854325 = 267593) (by norm_num)
theorem B3804605 : Blo 1690045 3804605 := bbase (se 3 (by rfl) ⟨713363, by rfl⟩ : syracuseStep 3804605 = 1426727) (by norm_num)
theorem B1805809 : Blo 1690045 1805809 := bbase (se 2 (by rfl) ⟨677178, by rfl⟩ : syracuseStep 1805809 = 1354357) (by norm_num)
theorem B3804677 : Blo 1690045 3804677 := bbase (se 4 (by rfl) ⟨356688, by rfl⟩ : syracuseStep 3804677 = 713377) (by norm_num)
theorem B4279837 : Blo 1690045 4279837 := bbase (se 3 (by rfl) ⟨802469, by rfl⟩ : syracuseStep 4279837 = 1604939) (by norm_num)
theorem B2854453 : Blo 1690045 2854453 := bbase (se 5 (by rfl) ⟨133802, by rfl⟩ : syracuseStep 2854453 = 267605) (by norm_num)
theorem B1928777 : Blo 1690045 1928777 := bbase (se 2 (by rfl) ⟨723291, by rfl⟩ : syracuseStep 1928777 = 1446583) (by norm_num)
theorem B3804749 : Blo 1690045 3804749 := bbase (se 3 (by rfl) ⟨713390, by rfl⟩ : syracuseStep 3804749 = 1426781) (by norm_num)
theorem B4279949 : Blo 1690045 4279949 := bbase (se 3 (by rfl) ⟨802490, by rfl⟩ : syracuseStep 4279949 = 1604981) (by norm_num)
theorem B3804821 : Blo 1690045 3804821 := bbase (se 6 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 3804821 = 178351) (by norm_num)
theorem B4337309 : Blo 1690045 4337309 := bbase (se 3 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 4337309 = 1626491) (by norm_num)
theorem B2535077 : Blo 1690045 2535077 := bbase (se 4 (by rfl) ⟨237663, by rfl⟩ : syracuseStep 2535077 = 475327) (by norm_num)
theorem B3296941 : Blo 1690045 3296941 := bbase (se 3 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 3296941 = 1236353) (by norm_num)
theorem B2535101 : Blo 1690045 2535101 := bbase (se 3 (by rfl) ⟨475331, by rfl⟩ : syracuseStep 2535101 = 950663) (by norm_num)
theorem B3428029 : Blo 1690045 3428029 := bbase (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) (by norm_num)
theorem B2707157 : Blo 1690045 2707157 := bbase (se 7 (by rfl) ⟨31724, by rfl⟩ : syracuseStep 2707157 = 63449) (by norm_num)
theorem B2535125 : Blo 1690045 2535125 := bbase (se 7 (by rfl) ⟨29708, by rfl⟩ : syracuseStep 2535125 = 59417) (by norm_num)
theorem B3804893 : Blo 1690045 3804893 := bbase (se 3 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 3804893 = 1426835) (by norm_num)
theorem B2535149 : Blo 1690045 2535149 := bbase (se 3 (by rfl) ⟨475340, by rfl⟩ : syracuseStep 2535149 = 950681) (by norm_num)
theorem B2535173 : Blo 1690045 2535173 := bbase (se 4 (by rfl) ⟨237672, by rfl⟩ : syracuseStep 2535173 = 475345) (by norm_num)
theorem B5705477 : Blo 1690045 5705477 := bbase (se 4 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 5705477 = 1069777) (by norm_num)
theorem B2535197 : Blo 1690045 2535197 := bbase (se 3 (by rfl) ⟨475349, by rfl⟩ : syracuseStep 2535197 = 950699) (by norm_num)
theorem B3804965 : Blo 1690045 3804965 := bbase (se 4 (by rfl) ⟨356715, by rfl⟩ : syracuseStep 3804965 = 713431) (by norm_num)
theorem B2535221 : Blo 1690045 2535221 := bbase (se 5 (by rfl) ⟨118838, by rfl⟩ : syracuseStep 2535221 = 237677) (by norm_num)
theorem B2535245 : Blo 1690045 2535245 := bbase (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) (by norm_num)
theorem B4280141 : Blo 1690045 4280141 := bbase (se 3 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 4280141 = 1605053) (by norm_num)
theorem B2535269 : Blo 1690045 2535269 := bbase (se 4 (by rfl) ⟨237681, by rfl⟩ : syracuseStep 2535269 = 475363) (by norm_num)
theorem B1806185 : Blo 1690045 1806185 := bbase (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) (by norm_num)
theorem B3805037 : Blo 1690045 3805037 := bbase (se 3 (by rfl) ⟨713444, by rfl⟩ : syracuseStep 3805037 = 1426889) (by norm_num)
theorem B2535293 : Blo 1690045 2535293 := bbase (se 3 (by rfl) ⟨475367, by rfl⟩ : syracuseStep 2535293 = 950735) (by norm_num)
theorem B2535317 : Blo 1690045 2535317 := bbase (se 6 (by rfl) ⟨59421, by rfl⟩ : syracuseStep 2535317 = 118843) (by norm_num)
theorem B2535341 : Blo 1690045 2535341 := bbase (se 3 (by rfl) ⟨475376, by rfl⟩ : syracuseStep 2535341 = 950753) (by norm_num)
theorem B1806257 : Blo 1690045 1806257 := bbase (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) (by norm_num)
theorem B2707381 : Blo 1690045 2707381 := bbase (se 5 (by rfl) ⟨126908, by rfl⟩ : syracuseStep 2707381 = 253817) (by norm_num)
theorem B3805109 : Blo 1690045 3805109 := bbase (se 5 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 3805109 = 356729) (by norm_num)
theorem B2535365 : Blo 1690045 2535365 := bbase (se 4 (by rfl) ⟨237690, by rfl⟩ : syracuseStep 2535365 = 475381) (by norm_num)
theorem B2535389 : Blo 1690045 2535389 := bbase (se 3 (by rfl) ⟨475385, by rfl⟩ : syracuseStep 2535389 = 950771) (by norm_num)
theorem B2535413 : Blo 1690045 2535413 := bbase (se 5 (by rfl) ⟨118847, by rfl⟩ : syracuseStep 2535413 = 237695) (by norm_num)
theorem B3805181 : Blo 1690045 3805181 := bbase (se 3 (by rfl) ⟨713471, by rfl⟩ : syracuseStep 3805181 = 1426943) (by norm_num)
theorem B2535437 : Blo 1690045 2535437 := bbase (se 3 (by rfl) ⟨475394, by rfl⟩ : syracuseStep 2535437 = 950789) (by norm_num)
theorem B2535461 : Blo 1690045 2535461 := bbase (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) (by norm_num)
theorem B2535485 : Blo 1690045 2535485 := bbase (se 3 (by rfl) ⟨475403, by rfl⟩ : syracuseStep 2535485 = 950807) (by norm_num)
theorem B3805253 : Blo 1690045 3805253 := bbase (se 4 (by rfl) ⟨356742, by rfl⟩ : syracuseStep 3805253 = 713485) (by norm_num)
theorem B2535509 : Blo 1690045 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B39055445 : Blo 1690045 39055445 := bbase (se 8 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 39055445 = 457681) (by norm_num)
theorem B2535533 : Blo 1690045 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B8556677 : Blo 1690045 8556677 := bbase (se 4 (by rfl) ⟨802188, by rfl⟩ : syracuseStep 8556677 = 1604377) (by norm_num)
theorem B2535557 : Blo 1690045 2535557 := bbase (se 4 (by rfl) ⟨237708, by rfl⟩ : syracuseStep 2535557 = 475417) (by norm_num)
theorem B3805325 : Blo 1690045 3805325 := bbase (se 3 (by rfl) ⟨713498, by rfl⟩ : syracuseStep 3805325 = 1426997) (by norm_num)
theorem B4812949 : Blo 1690045 4812949 := bbase (se 6 (by rfl) ⟨112803, by rfl⟩ : syracuseStep 4812949 = 225607) (by norm_num)
theorem B15429781 : Blo 1690045 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B2535581 : Blo 1690045 2535581 := bbase (se 3 (by rfl) ⟨475421, by rfl⟩ : syracuseStep 2535581 = 950843) (by norm_num)
theorem B4280485 : Blo 1690045 4280485 := bbase (se 4 (by rfl) ⟨401295, by rfl⟩ : syracuseStep 4280485 = 802591) (by norm_num)
theorem B2535605 : Blo 1690045 2535605 := bbase (se 5 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 2535605 = 237713) (by norm_num)
theorem B5705909 : Blo 1690045 5705909 := bbase (se 5 (by rfl) ⟨267464, by rfl⟩ : syracuseStep 5705909 = 534929) (by norm_num)
theorem B2535629 : Blo 1690045 2535629 := bbase (se 3 (by rfl) ⟨475430, by rfl⟩ : syracuseStep 2535629 = 950861) (by norm_num)
theorem B3805397 : Blo 1690045 3805397 := bbase (se 7 (by rfl) ⟨44594, by rfl⟩ : syracuseStep 3805397 = 89189) (by norm_num)
theorem B2535653 : Blo 1690045 2535653 := bbase (se 4 (by rfl) ⟨237717, by rfl⟩ : syracuseStep 2535653 = 475435) (by norm_num)
theorem B2535677 : Blo 1690045 2535677 := bbase (se 3 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 2535677 = 950879) (by norm_num)
theorem B2535701 : Blo 1690045 2535701 := bbase (se 6 (by rfl) ⟨59430, by rfl⟩ : syracuseStep 2535701 = 118861) (by norm_num)
theorem B6418709 : Blo 1690045 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B4280597 : Blo 1690045 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B3805469 : Blo 1690045 3805469 := bbase (se 3 (by rfl) ⟨713525, by rfl⟩ : syracuseStep 3805469 = 1427051) (by norm_num)
theorem B2535725 : Blo 1690045 2535725 := bbase (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) (by norm_num)
theorem B2535749 : Blo 1690045 2535749 := bbase (se 4 (by rfl) ⟨237726, by rfl⟩ : syracuseStep 2535749 = 475453) (by norm_num)
theorem B2535773 : Blo 1690045 2535773 := bbase (se 3 (by rfl) ⟨475457, by rfl⟩ : syracuseStep 2535773 = 950915) (by norm_num)
theorem B3805541 : Blo 1690045 3805541 := bbase (se 4 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 3805541 = 713539) (by norm_num)
theorem B2535797 : Blo 1690045 2535797 := bbase (se 5 (by rfl) ⟨118865, by rfl⟩ : syracuseStep 2535797 = 237731) (by norm_num)
theorem B2535821 : Blo 1690045 2535821 := bbase (se 3 (by rfl) ⟨475466, by rfl⟩ : syracuseStep 2535821 = 950933) (by norm_num)
theorem B2535845 : Blo 1690045 2535845 := bbase (se 4 (by rfl) ⟨237735, by rfl⟩ : syracuseStep 2535845 = 475471) (by norm_num)
theorem B3805613 : Blo 1690045 3805613 := bbase (se 3 (by rfl) ⟨713552, by rfl⟩ : syracuseStep 3805613 = 1427105) (by norm_num)
theorem B13709749 : Blo 1690045 13709749 := bbase (se 5 (by rfl) ⟨642644, by rfl⟩ : syracuseStep 13709749 = 1285289) (by norm_num)
theorem B2535869 : Blo 1690045 2535869 := bbase (se 3 (by rfl) ⟨475475, by rfl⟩ : syracuseStep 2535869 = 950951) (by norm_num)
theorem B2535893 : Blo 1690045 2535893 := bbase (se 7 (by rfl) ⟨29717, by rfl⟩ : syracuseStep 2535893 = 59435) (by norm_num)
theorem B4280789 : Blo 1690045 4280789 := bbase (se 7 (by rfl) ⟨50165, by rfl⟩ : syracuseStep 4280789 = 100331) (by norm_num)
theorem B2535917 : Blo 1690045 2535917 := bbase (se 3 (by rfl) ⟨475484, by rfl⟩ : syracuseStep 2535917 = 950969) (by norm_num)
theorem B3805685 : Blo 1690045 3805685 := bbase (se 5 (by rfl) ⟨178391, by rfl⟩ : syracuseStep 3805685 = 356783) (by norm_num)
theorem B2535941 : Blo 1690045 2535941 := bbase (se 4 (by rfl) ⟨237744, by rfl⟩ : syracuseStep 2535941 = 475489) (by norm_num)
theorem B1954325 : Blo 1690045 1954325 := bbase (se 6 (by rfl) ⟨45804, by rfl⟩ : syracuseStep 1954325 = 91609) (by norm_num)
theorem B2535965 : Blo 1690045 2535965 := bbase (se 3 (by rfl) ⟨475493, by rfl⟩ : syracuseStep 2535965 = 950987) (by norm_num)
theorem B8679973 : Blo 1690045 8679973 := bbase (se 4 (by rfl) ⟨813747, by rfl⟩ : syracuseStep 8679973 = 1627495) (by norm_num)
theorem B6418997 : Blo 1690045 6418997 := bbase (se 5 (by rfl) ⟨300890, by rfl⟩ : syracuseStep 6418997 = 601781) (by norm_num)
theorem B2535989 : Blo 1690045 2535989 := bbase (se 5 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 2535989 = 237749) (by norm_num)
theorem B3805757 : Blo 1690045 3805757 := bbase (se 3 (by rfl) ⟨713579, by rfl⟩ : syracuseStep 3805757 = 1427159) (by norm_num)
theorem B2536013 : Blo 1690045 2536013 := bbase (se 3 (by rfl) ⟨475502, by rfl⟩ : syracuseStep 2536013 = 951005) (by norm_num)
theorem B2536037 : Blo 1690045 2536037 := bbase (se 4 (by rfl) ⟨237753, by rfl⟩ : syracuseStep 2536037 = 475507) (by norm_num)
theorem B5706341 : Blo 1690045 5706341 := bbase (se 4 (by rfl) ⟨534969, by rfl⟩ : syracuseStep 5706341 = 1069939) (by norm_num)
theorem B2536061 : Blo 1690045 2536061 := bbase (se 3 (by rfl) ⟨475511, by rfl⟩ : syracuseStep 2536061 = 951023) (by norm_num)
theorem B3805829 : Blo 1690045 3805829 := bbase (se 4 (by rfl) ⟨356796, by rfl⟩ : syracuseStep 3805829 = 713593) (by norm_num)
theorem B2536085 : Blo 1690045 2536085 := bbase (se 6 (by rfl) ⟨59439, by rfl⟩ : syracuseStep 2536085 = 118879) (by norm_num)
theorem B2536109 : Blo 1690045 2536109 := bbase (se 3 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 2536109 = 951041) (by norm_num)
theorem B2536133 : Blo 1690045 2536133 := bbase (se 4 (by rfl) ⟨237762, by rfl⟩ : syracuseStep 2536133 = 475525) (by norm_num)
theorem B3805901 : Blo 1690045 3805901 := bbase (se 3 (by rfl) ⟨713606, by rfl⟩ : syracuseStep 3805901 = 1427213) (by norm_num)
theorem B2536157 : Blo 1690045 2536157 := bbase (se 3 (by rfl) ⟨475529, by rfl⟩ : syracuseStep 2536157 = 951059) (by norm_num)
theorem B2536181 : Blo 1690045 2536181 := bbase (se 5 (by rfl) ⟨118883, by rfl⟩ : syracuseStep 2536181 = 237767) (by norm_num)
theorem B2536205 : Blo 1690045 2536205 := bbase (se 3 (by rfl) ⟨475538, by rfl⟩ : syracuseStep 2536205 = 951077) (by norm_num)
theorem B3805973 : Blo 1690045 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B2536229 : Blo 1690045 2536229 := bbase (se 4 (by rfl) ⟨237771, by rfl⟩ : syracuseStep 2536229 = 475543) (by norm_num)
theorem B4281133 : Blo 1690045 4281133 := bbase (se 3 (by rfl) ⟨802712, by rfl⟩ : syracuseStep 4281133 = 1605425) (by norm_num)
theorem B2536253 : Blo 1690045 2536253 := bbase (se 3 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 2536253 = 951095) (by norm_num)
theorem B2536277 : Blo 1690045 2536277 := bbase (se 9 (by rfl) ⟨7430, by rfl⟩ : syracuseStep 2536277 = 14861) (by norm_num)
theorem B8123237 : Blo 1690045 8123237 := bbase (se 4 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 8123237 = 1523107) (by norm_num)
theorem B2536301 : Blo 1690045 2536301 := bbase (se 3 (by rfl) ⟨475556, by rfl⟩ : syracuseStep 2536301 = 951113) (by norm_num)
theorem B2536325 : Blo 1690045 2536325 := bbase (se 4 (by rfl) ⟨237780, by rfl⟩ : syracuseStep 2536325 = 475561) (by norm_num)
theorem B2536349 : Blo 1690045 2536349 := bbase (se 3 (by rfl) ⟨475565, by rfl⟩ : syracuseStep 2536349 = 951131) (by norm_num)
theorem B4281245 : Blo 1690045 4281245 := bbase (se 3 (by rfl) ⟨802733, by rfl⟩ : syracuseStep 4281245 = 1605467) (by norm_num)
theorem B2536373 : Blo 1690045 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B2536397 : Blo 1690045 2536397 := bbase (se 3 (by rfl) ⟨475574, by rfl⟩ : syracuseStep 2536397 = 951149) (by norm_num)
theorem B2536421 : Blo 1690045 2536421 := bbase (se 4 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 2536421 = 475579) (by norm_num)
theorem B2536445 : Blo 1690045 2536445 := bbase (se 3 (by rfl) ⟨475583, by rfl⟩ : syracuseStep 2536445 = 951167) (by norm_num)
theorem B5706773 : Blo 1690045 5706773 := bbase (se 6 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 5706773 = 267505) (by norm_num)
theorem B2536469 : Blo 1690045 2536469 := bbase (se 6 (by rfl) ⟨59448, by rfl⟩ : syracuseStep 2536469 = 118897) (by norm_num)
theorem B8123429 : Blo 1690045 8123429 := bbase (se 4 (by rfl) ⟨761571, by rfl⟩ : syracuseStep 8123429 = 1523143) (by norm_num)
theorem B2536493 : Blo 1690045 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B2536517 : Blo 1690045 2536517 := bbase (se 4 (by rfl) ⟨237798, by rfl⟩ : syracuseStep 2536517 = 475597) (by norm_num)
theorem B2536541 : Blo 1690045 2536541 := bbase (se 3 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 2536541 = 951203) (by norm_num)
theorem B4281437 : Blo 1690045 4281437 := bbase (se 3 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 4281437 = 1605539) (by norm_num)
theorem B2536565 : Blo 1690045 2536565 := bbase (se 5 (by rfl) ⟨118901, by rfl⟩ : syracuseStep 2536565 = 237803) (by norm_num)
theorem B1954945 : Blo 1690045 1954945 := bbase (se 2 (by rfl) ⟨733104, by rfl⟩ : syracuseStep 1954945 = 1466209) (by norm_num)
theorem B2536589 : Blo 1690045 2536589 := bbase (se 3 (by rfl) ⟨475610, by rfl⟩ : syracuseStep 2536589 = 951221) (by norm_num)
theorem B2536613 : Blo 1690045 2536613 := bbase (se 4 (by rfl) ⟨237807, by rfl⟩ : syracuseStep 2536613 = 475615) (by norm_num)
theorem B2536637 : Blo 1690045 2536637 := bbase (se 3 (by rfl) ⟨475619, by rfl⟩ : syracuseStep 2536637 = 951239) (by norm_num)
theorem B2536661 : Blo 1690045 2536661 := bbase (se 7 (by rfl) ⟨29726, by rfl⟩ : syracuseStep 2536661 = 59453) (by norm_num)
theorem B2536685 : Blo 1690045 2536685 := bbase (se 3 (by rfl) ⟨475628, by rfl⟩ : syracuseStep 2536685 = 951257) (by norm_num)
theorem B2536709 : Blo 1690045 2536709 := bbase (se 4 (by rfl) ⟨237816, by rfl⟩ : syracuseStep 2536709 = 475633) (by norm_num)
theorem B2536733 : Blo 1690045 2536733 := bbase (se 3 (by rfl) ⟨475637, by rfl⟩ : syracuseStep 2536733 = 951275) (by norm_num)
theorem B2536757 : Blo 1690045 2536757 := bbase (se 5 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 2536757 = 237821) (by norm_num)
theorem B2708797 : Blo 1690045 2708797 := bbase (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) (by norm_num)
theorem B2536781 : Blo 1690045 2536781 := bbase (se 3 (by rfl) ⟨475646, by rfl⟩ : syracuseStep 2536781 = 951293) (by norm_num)
theorem B2536805 : Blo 1690045 2536805 := bbase (se 4 (by rfl) ⟨237825, by rfl⟩ : syracuseStep 2536805 = 475651) (by norm_num)
theorem B3208565 : Blo 1690045 3208565 := bbase (se 5 (by rfl) ⟨150401, by rfl⟩ : syracuseStep 3208565 = 300803) (by norm_num)
theorem B2536829 : Blo 1690045 2536829 := bbase (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) (by norm_num)
theorem B5354885 : Blo 1690045 5354885 := bbase (se 4 (by rfl) ⟨502020, by rfl⟩ : syracuseStep 5354885 = 1004041) (by norm_num)
theorem B8557973 : Blo 1690045 8557973 := bbase (se 6 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 8557973 = 401155) (by norm_num)
theorem B2536853 : Blo 1690045 2536853 := bbase (se 6 (by rfl) ⟨59457, by rfl⟩ : syracuseStep 2536853 = 118915) (by norm_num)
theorem B8033701 : Blo 1690045 8033701 := bbase (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) (by norm_num)
theorem B2536877 : Blo 1690045 2536877 := bbase (se 3 (by rfl) ⟨475664, by rfl⟩ : syracuseStep 2536877 = 951329) (by norm_num)
theorem B5707205 : Blo 1690045 5707205 := bbase (se 4 (by rfl) ⟨535050, by rfl⟩ : syracuseStep 5707205 = 1070101) (by norm_num)
theorem B2536901 : Blo 1690045 2536901 := bbase (se 4 (by rfl) ⟨237834, by rfl⟩ : syracuseStep 2536901 = 475669) (by norm_num)
theorem B2536925 : Blo 1690045 2536925 := bbase (se 3 (by rfl) ⟨475673, by rfl⟩ : syracuseStep 2536925 = 951347) (by norm_num)
theorem B2536949 : Blo 1690045 2536949 := bbase (se 5 (by rfl) ⟨118919, by rfl⟩ : syracuseStep 2536949 = 237839) (by norm_num)
theorem B2569733 : Blo 1690045 2569733 := bbase (se 4 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 2569733 = 481825) (by norm_num)
theorem B3208709 : Blo 1690045 3208709 := bbase (se 4 (by rfl) ⟨300816, by rfl⟩ : syracuseStep 3208709 = 601633) (by norm_num)
theorem B2536973 : Blo 1690045 2536973 := bbase (se 3 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 2536973 = 951365) (by norm_num)
theorem B2536997 : Blo 1690045 2536997 := bbase (se 4 (by rfl) ⟨237843, by rfl⟩ : syracuseStep 2536997 = 475687) (by norm_num)
theorem B12842549 : Blo 1690045 12842549 := bbase (se 5 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 12842549 = 1203989) (by norm_num)
theorem B2709053 : Blo 1690045 2709053 := bbase (se 3 (by rfl) ⟨507947, by rfl⟩ : syracuseStep 2709053 = 1015895) (by norm_num)
theorem B2537021 : Blo 1690045 2537021 := bbase (se 3 (by rfl) ⟨475691, by rfl⟩ : syracuseStep 2537021 = 951383) (by norm_num)
theorem B2537045 : Blo 1690045 2537045 := bbase (se 8 (by rfl) ⟨14865, by rfl⟩ : syracuseStep 2537045 = 29731) (by norm_num)
theorem B2537069 : Blo 1690045 2537069 := bbase (se 3 (by rfl) ⟨475700, by rfl⟩ : syracuseStep 2537069 = 951401) (by norm_num)
theorem B4814453 : Blo 1690045 4814453 := bbase (se 5 (by rfl) ⟨225677, by rfl⟩ : syracuseStep 4814453 = 451355) (by norm_num)
theorem B2537093 : Blo 1690045 2537093 := bbase (se 4 (by rfl) ⟨237852, by rfl⟩ : syracuseStep 2537093 = 475705) (by norm_num)
theorem B2537117 : Blo 1690045 2537117 := bbase (se 3 (by rfl) ⟨475709, by rfl⟩ : syracuseStep 2537117 = 951419) (by norm_num)
theorem B2537141 : Blo 1690045 2537141 := bbase (se 5 (by rfl) ⟨118928, by rfl⟩ : syracuseStep 2537141 = 237857) (by norm_num)
theorem B2537165 : Blo 1690045 2537165 := bbase (se 3 (by rfl) ⟨475718, by rfl⟩ : syracuseStep 2537165 = 951437) (by norm_num)
theorem B6420181 : Blo 1690045 6420181 := bbase (se 7 (by rfl) ⟨75236, by rfl⟩ : syracuseStep 6420181 = 150473) (by norm_num)
theorem B2537189 : Blo 1690045 2537189 := bbase (se 4 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 2537189 = 475723) (by norm_num)
theorem B2709245 : Blo 1690045 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B2537213 : Blo 1690045 2537213 := bbase (se 3 (by rfl) ⟨475727, by rfl⟩ : syracuseStep 2537213 = 951455) (by norm_num)
theorem B2537237 : Blo 1690045 2537237 := bbase (se 6 (by rfl) ⟨59466, by rfl⟩ : syracuseStep 2537237 = 118933) (by norm_num)
theorem B3208997 : Blo 1690045 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B2537261 : Blo 1690045 2537261 := bbase (se 3 (by rfl) ⟨475736, by rfl⟩ : syracuseStep 2537261 = 951473) (by norm_num)
theorem B2537285 : Blo 1690045 2537285 := bbase (se 4 (by rfl) ⟨237870, by rfl⟩ : syracuseStep 2537285 = 475741) (by norm_num)
theorem B2537309 : Blo 1690045 2537309 := bbase (se 3 (by rfl) ⟨475745, by rfl⟩ : syracuseStep 2537309 = 951491) (by norm_num)
theorem B5707637 : Blo 1690045 5707637 := bbase (se 5 (by rfl) ⟨267545, by rfl⟩ : syracuseStep 5707637 = 535091) (by norm_num)
theorem B2570141 : Blo 1690045 2570141 := bbase (se 3 (by rfl) ⟨481901, by rfl⟩ : syracuseStep 2570141 = 963803) (by norm_num)
theorem B3209149 : Blo 1690045 3209149 := bbase (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) (by norm_num)
theorem B12834773 : Blo 1690045 12834773 := bbase (se 7 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 12834773 = 300815) (by norm_num)
theorem B6420485 : Blo 1690045 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B3610669 : Blo 1690045 3610669 := bbase (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) (by norm_num)
theorem B2439229 : Blo 1690045 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B1980493 : Blo 1690045 1980493 := bbase (se 3 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 1980493 = 742685) (by norm_num)
theorem B7223525 : Blo 1690045 7223525 := bbase (se 4 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 7223525 = 1354411) (by norm_num)
theorem B3209453 : Blo 1690045 3209453 := bbase (se 3 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 3209453 = 1203545) (by norm_num)
theorem B3569917 : Blo 1690045 3569917 := bbase (se 3 (by rfl) ⟨669359, by rfl⟩ : syracuseStep 3569917 = 1338719) (by norm_num)
theorem B5708069 : Blo 1690045 5708069 := bbase (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) (by norm_num)
theorem B4880693 : Blo 1690045 4880693 := bbase (se 5 (by rfl) ⟨228782, by rfl⟩ : syracuseStep 4880693 = 457565) (by norm_num)
theorem B8673733 : Blo 1690045 8673733 := bbase (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) (by norm_num)
theorem B4569605 : Blo 1690045 4569605 := bbase (se 4 (by rfl) ⟨428400, by rfl⟩ : syracuseStep 4569605 = 856801) (by norm_num)
theorem B2406925 : Blo 1690045 2406925 := bbase (se 3 (by rfl) ⟨451298, by rfl⟩ : syracuseStep 2406925 = 902597) (by norm_num)
theorem B3045941 : Blo 1690045 3045941 := bbase (se 5 (by rfl) ⟨142778, by rfl⟩ : syracuseStep 3045941 = 285557) (by norm_num)
theorem B3046013 : Blo 1690045 3046013 := bbase (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) (by norm_num)
theorem B8559269 : Blo 1690045 8559269 := bbase (se 4 (by rfl) ⟨802431, by rfl⟩ : syracuseStep 8559269 = 1604863) (by norm_num)
theorem B4569797 : Blo 1690045 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B5708501 : Blo 1690045 5708501 := bbase (se 7 (by rfl) ⟨66896, by rfl⟩ : syracuseStep 5708501 = 133793) (by norm_num)
theorem B3046157 : Blo 1690045 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B2407261 : Blo 1690045 2407261 := bbase (se 3 (by rfl) ⟨451361, by rfl⟩ : syracuseStep 2407261 = 902723) (by norm_num)
theorem B3611557 : Blo 1690045 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B3210205 : Blo 1690045 3210205 := bbase (se 3 (by rfl) ⟨601913, by rfl⟩ : syracuseStep 3210205 = 1203827) (by norm_num)
theorem B12352501 : Blo 1690045 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B2030617 : Blo 1690045 2030617 := bbase (se 2 (by rfl) ⟨761481, by rfl⟩ : syracuseStep 2030617 = 1522963) (by norm_num)
theorem B2407477 : Blo 1690045 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B8125525 : Blo 1690045 8125525 := bbase (se 8 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 8125525 = 95221) (by norm_num)
theorem B3210349 : Blo 1690045 3210349 := bbase (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) (by norm_num)
theorem B6855797 : Blo 1690045 6855797 := bbase (se 5 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 6855797 = 642731) (by norm_num)
theorem B2030713 : Blo 1690045 2030713 := bbase (se 2 (by rfl) ⟨761517, by rfl⟩ : syracuseStep 2030713 = 1523035) (by norm_num)
theorem B5708933 : Blo 1690045 5708933 := bbase (se 4 (by rfl) ⟨535212, by rfl⟩ : syracuseStep 5708933 = 1070425) (by norm_num)
theorem B4062349 : Blo 1690045 4062349 := bbase (se 3 (by rfl) ⟨761690, by rfl⟩ : syracuseStep 4062349 = 1523381) (by norm_num)
theorem B4816037 : Blo 1690045 4816037 := bbase (se 4 (by rfl) ⟨451503, by rfl⟩ : syracuseStep 4816037 = 903007) (by norm_num)
theorem B3210509 : Blo 1690045 3210509 := bbase (se 3 (by rfl) ⟨601970, by rfl⟩ : syracuseStep 3210509 = 1203941) (by norm_num)
theorem B4062541 : Blo 1690045 4062541 := bbase (se 3 (by rfl) ⟨761726, by rfl⟩ : syracuseStep 4062541 = 1523453) (by norm_num)
theorem B4570469 : Blo 1690045 4570469 := bbase (se 4 (by rfl) ⟨428481, by rfl⟩ : syracuseStep 4570469 = 856963) (by norm_num)
theorem B4062581 : Blo 1690045 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B3612053 : Blo 1690045 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B3210653 : Blo 1690045 3210653 := bbase (se 3 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 3210653 = 1203995) (by norm_num)
theorem B2407853 : Blo 1690045 2407853 := bbase (se 3 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 2407853 = 902945) (by norm_num)
theorem B4062869 : Blo 1690045 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B3210941 : Blo 1690045 3210941 := bbase (se 3 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 3210941 = 1204103) (by norm_num)
theorem B4816709 : Blo 1690045 4816709 := bbase (se 4 (by rfl) ⟨451566, by rfl⟩ : syracuseStep 4816709 = 903133) (by norm_num)
theorem B3211093 : Blo 1690045 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B2932613 : Blo 1690045 2932613 := bbase (se 4 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 2932613 = 549865) (by norm_num)
theorem B13705109 : Blo 1690045 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B8560565 : Blo 1690045 8560565 := bbase (se 5 (by rfl) ⟨401276, by rfl⟩ : syracuseStep 8560565 = 802553) (by norm_num)
theorem B7225301 : Blo 1690045 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B3252305 : Blo 1690045 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B4759889 : Blo 1690045 4759889 := bstep (se 2 (by rfl) ⟨1784958, by rfl⟩ : syracuseStep 4759889 = 3569917) B3569917
theorem B4063715 : Blo 1690045 4063715 := bstep (se 1 (by rfl) ⟨3047786, by rfl⟩ : syracuseStep 4063715 = 6095573) B6095573
theorem B5415491 : Blo 1690045 5415491 := bstep (se 1 (by rfl) ⟨4061618, by rfl⟩ : syracuseStep 5415491 = 8123237) B8123237
theorem B12190277 : Blo 1690045 12190277 := bstep (se 4 (by rfl) ⟨1142838, by rfl⟩ : syracuseStep 12190277 = 2285677) B2285677
theorem B1737331 : Blo 1690045 1737331 := bstep (se 1 (by rfl) ⟨1302998, by rfl⟩ : syracuseStep 1737331 = 2605997) B2605997
theorem B10830469 : Blo 1690045 10830469 := bstep (se 4 (by rfl) ⟨1015356, by rfl⟩ : syracuseStep 10830469 = 2030713) B2030713
theorem B9626309 : Blo 1690045 9626309 := bstep (se 4 (by rfl) ⟨902466, by rfl⟩ : syracuseStep 9626309 = 1804933) B1804933
theorem B21422789 : Blo 1690045 21422789 := bstep (se 4 (by rfl) ⟨2008386, by rfl⟩ : syracuseStep 21422789 = 4016773) B4016773
theorem B4064003 : Blo 1690045 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B1901443 : Blo 1690045 1901443 := bstep (se 1 (by rfl) ⟨1426082, by rfl⟩ : syracuseStep 1901443 = 2852165) B2852165
theorem B2139043 : Blo 1690045 2139043 := bstep (se 1 (by rfl) ⟨1604282, by rfl⟩ : syracuseStep 2139043 = 3208565) B3208565
theorem B4064195 : Blo 1690045 4064195 := bstep (se 1 (by rfl) ⟨3048146, by rfl⟩ : syracuseStep 4064195 = 6096293) B6096293
theorem B1713155 : Blo 1690045 1713155 := bstep (se 1 (by rfl) ⟨1284866, by rfl⟩ : syracuseStep 1713155 = 2569733) B2569733
theorem B2139139 : Blo 1690045 2139139 := bstep (se 1 (by rfl) ⟨1604354, by rfl⟩ : syracuseStep 2139139 = 3208709) B3208709
theorem B1901587 : Blo 1690045 1901587 := bstep (se 1 (by rfl) ⟨1426190, by rfl⟩ : syracuseStep 1901587 = 2852381) B2852381
theorem B8561699 : Blo 1690045 8561699 := bstep (se 1 (by rfl) ⟨6421274, by rfl⟩ : syracuseStep 8561699 = 12842549) B12842549
theorem B2851969 : Blo 1690045 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B2852003 : Blo 1690045 2852003 := bstep (se 1 (by rfl) ⟨2139002, by rfl⟩ : syracuseStep 2852003 = 4278005) B4278005
theorem B1901731 : Blo 1690045 1901731 := bstep (se 1 (by rfl) ⟨1426298, by rfl⟩ : syracuseStep 1901731 = 2852597) B2852597
theorem B2852131 : Blo 1690045 2852131 := bstep (se 1 (by rfl) ⟨2139098, by rfl⟩ : syracuseStep 2852131 = 4278197) B4278197
theorem B1901875 : Blo 1690045 1901875 := bstep (se 1 (by rfl) ⟨1426406, by rfl⟩ : syracuseStep 1901875 = 2852813) B2852813
theorem B16246129 : Blo 1690045 16246129 := bstep (se 2 (by rfl) ⟨6092298, by rfl⟩ : syracuseStep 16246129 = 12184597) B12184597
theorem B5211533 : Blo 1690045 5211533 := bstep (se 3 (by rfl) ⟨977162, by rfl⟩ : syracuseStep 5211533 = 1954325) B1954325
theorem B2852273 : Blo 1690045 2852273 := bstep (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) B2139205
theorem B1902019 : Blo 1690045 1902019 := bstep (se 1 (by rfl) ⟨1426514, by rfl⟩ : syracuseStep 1902019 = 2853029) B2853029
theorem B2139635 : Blo 1690045 2139635 := bstep (se 1 (by rfl) ⟨1604726, by rfl⟩ : syracuseStep 2139635 = 3209453) B3209453
theorem B2606593 : Blo 1690045 2606593 := bstep (se 2 (by rfl) ⟨977472, by rfl⟩ : syracuseStep 2606593 = 1954945) B1954945
theorem B5416465 : Blo 1690045 5416465 := bstep (se 2 (by rfl) ⟨2031174, by rfl⟩ : syracuseStep 5416465 = 4062349) B4062349
theorem B2852401 : Blo 1690045 2852401 := bstep (se 2 (by rfl) ⟨1069650, by rfl⟩ : syracuseStep 2852401 = 2139301) B2139301
theorem B2852435 : Blo 1690045 2852435 := bstep (se 1 (by rfl) ⟨2139326, by rfl⟩ : syracuseStep 2852435 = 4278653) B4278653
theorem B1902163 : Blo 1690045 1902163 := bstep (se 1 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 1902163 = 2853245) B2853245
theorem B3802769 : Blo 1690045 3802769 := bstep (se 2 (by rfl) ⟨1426038, by rfl⟩ : syracuseStep 3802769 = 2852077) B2852077
theorem B3802787 : Blo 1690045 3802787 := bstep (se 1 (by rfl) ⟨2852090, by rfl⟩ : syracuseStep 3802787 = 5704181) B5704181
theorem B2852563 : Blo 1690045 2852563 := bstep (se 1 (by rfl) ⟨2139422, by rfl⟩ : syracuseStep 2852563 = 4278845) B4278845
theorem B1902307 : Blo 1690045 1902307 := bstep (se 1 (by rfl) ⟨1426730, by rfl⟩ : syracuseStep 1902307 = 2853461) B2853461
theorem B5416721 : Blo 1690045 5416721 := bstep (se 2 (by rfl) ⟨2031270, by rfl⟩ : syracuseStep 5416721 = 4062541) B4062541
theorem B2746145 : Blo 1690045 2746145 := bstep (se 2 (by rfl) ⟨1029804, by rfl⟩ : syracuseStep 2746145 = 2059609) B2059609
theorem B8562509 : Blo 1690045 8562509 := bstep (se 3 (by rfl) ⟨1605470, by rfl⟩ : syracuseStep 8562509 = 3210941) B3210941
theorem B2852705 : Blo 1690045 2852705 := bstep (se 2 (by rfl) ⟨1069764, by rfl⟩ : syracuseStep 2852705 = 2139529) B2139529
theorem B10979171 : Blo 1690045 10979171 := bstep (se 1 (by rfl) ⟨8234378, by rfl⟩ : syracuseStep 10979171 = 16468757) B16468757
theorem B1902451 : Blo 1690045 1902451 := bstep (se 1 (by rfl) ⟨1426838, by rfl⟩ : syracuseStep 1902451 = 2853677) B2853677
theorem B3803057 : Blo 1690045 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B3803075 : Blo 1690045 3803075 := bstep (se 1 (by rfl) ⟨2852306, by rfl⟩ : syracuseStep 3803075 = 5704613) B5704613
theorem B2852833 : Blo 1690045 2852833 := bstep (se 2 (by rfl) ⟨1069812, by rfl⟩ : syracuseStep 2852833 = 2139625) B2139625
theorem B2852867 : Blo 1690045 2852867 := bstep (se 1 (by rfl) ⟨2139650, by rfl⟩ : syracuseStep 2852867 = 4279301) B4279301
theorem B1902595 : Blo 1690045 1902595 := bstep (se 1 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 1902595 = 2853893) B2853893
theorem B2852995 : Blo 1690045 2852995 := bstep (se 1 (by rfl) ⟨2139746, by rfl⟩ : syracuseStep 2852995 = 4279493) B4279493
theorem B1902739 : Blo 1690045 1902739 := bstep (se 1 (by rfl) ⟨1427054, by rfl⟩ : syracuseStep 1902739 = 2854109) B2854109
theorem B2140339 : Blo 1690045 2140339 := bstep (se 1 (by rfl) ⟨1605254, by rfl⟩ : syracuseStep 2140339 = 3210509) B3210509
theorem B19261637 : Blo 1690045 19261637 := bstep (se 4 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 19261637 = 3611557) B3611557
theorem B3803345 : Blo 1690045 3803345 := bstep (se 2 (by rfl) ⟨1426254, by rfl⟩ : syracuseStep 3803345 = 2852509) B2852509
theorem B3803363 : Blo 1690045 3803363 := bstep (se 1 (by rfl) ⟨2852522, by rfl⟩ : syracuseStep 3803363 = 5705045) B5705045
theorem B2853137 : Blo 1690045 2853137 := bstep (se 2 (by rfl) ⟨1069926, by rfl⟩ : syracuseStep 2853137 = 2139853) B2139853
theorem B2140435 : Blo 1690045 2140435 := bstep (se 1 (by rfl) ⟨1605326, by rfl⟩ : syracuseStep 2140435 = 3210653) B3210653
theorem B1902883 : Blo 1690045 1902883 := bstep (se 1 (by rfl) ⟨1427162, by rfl⟩ : syracuseStep 1902883 = 2854325) B2854325
theorem B2853265 : Blo 1690045 2853265 := bstep (se 2 (by rfl) ⟨1069974, by rfl⟩ : syracuseStep 2853265 = 2139949) B2139949
theorem B2853299 : Blo 1690045 2853299 := bstep (se 1 (by rfl) ⟨2139974, by rfl⟩ : syracuseStep 2853299 = 4279949) B4279949
theorem B1690051 : Blo 1690045 1690051 := bstep (se 1 (by rfl) ⟨1267538, by rfl⟩ : syracuseStep 1690051 = 2535077) B2535077
theorem B1690067 : Blo 1690045 1690067 := bstep (se 1 (by rfl) ⟨1267550, by rfl⟩ : syracuseStep 1690067 = 2535101) B2535101
theorem B1804771 : Blo 1690045 1804771 := bstep (se 1 (by rfl) ⟨1353578, by rfl⟩ : syracuseStep 1804771 = 2707157) B2707157
theorem B1690083 : Blo 1690045 1690083 := bstep (se 1 (by rfl) ⟨1267562, by rfl⟩ : syracuseStep 1690083 = 2535125) B2535125
theorem B3803633 : Blo 1690045 3803633 := bstep (se 2 (by rfl) ⟨1426362, by rfl⟩ : syracuseStep 3803633 = 2852725) B2852725
theorem B1690099 : Blo 1690045 1690099 := bstep (se 1 (by rfl) ⟨1267574, by rfl⟩ : syracuseStep 1690099 = 2535149) B2535149
theorem B1690115 : Blo 1690045 1690115 := bstep (se 1 (by rfl) ⟨1267586, by rfl⟩ : syracuseStep 1690115 = 2535173) B2535173
theorem B3803651 : Blo 1690045 3803651 := bstep (se 1 (by rfl) ⟨2852738, by rfl⟩ : syracuseStep 3803651 = 5705477) B5705477
theorem B1690131 : Blo 1690045 1690131 := bstep (se 1 (by rfl) ⟨1267598, by rfl⟩ : syracuseStep 1690131 = 2535197) B2535197
theorem B1690147 : Blo 1690045 1690147 := bstep (se 1 (by rfl) ⟨1267610, by rfl⟩ : syracuseStep 1690147 = 2535221) B2535221
theorem B1690163 : Blo 1690045 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B2853427 : Blo 1690045 2853427 := bstep (se 1 (by rfl) ⟨2140070, by rfl⟩ : syracuseStep 2853427 = 4280141) B4280141
theorem B1690179 : Blo 1690045 1690179 := bstep (se 1 (by rfl) ⟨1267634, by rfl⟩ : syracuseStep 1690179 = 2535269) B2535269
theorem B4278865 : Blo 1690045 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B1690195 : Blo 1690045 1690195 := bstep (se 1 (by rfl) ⟨1267646, by rfl⟩ : syracuseStep 1690195 = 2535293) B2535293
theorem B9136739 : Blo 1690045 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B1690211 : Blo 1690045 1690211 := bstep (se 1 (by rfl) ⟨1267658, by rfl⟩ : syracuseStep 1690211 = 2535317) B2535317
theorem B1690227 : Blo 1690045 1690227 := bstep (se 1 (by rfl) ⟨1267670, by rfl⟩ : syracuseStep 1690227 = 2535341) B2535341
theorem B1690243 : Blo 1690045 1690243 := bstep (se 1 (by rfl) ⟨1267682, by rfl⟩ : syracuseStep 1690243 = 2535365) B2535365
theorem B1690259 : Blo 1690045 1690259 := bstep (se 1 (by rfl) ⟨1267694, by rfl⟩ : syracuseStep 1690259 = 2535389) B2535389
theorem B1690275 : Blo 1690045 1690275 := bstep (se 1 (by rfl) ⟨1267706, by rfl⟩ : syracuseStep 1690275 = 2535413) B2535413
theorem B1690291 : Blo 1690045 1690291 := bstep (se 1 (by rfl) ⟨1267718, by rfl⟩ : syracuseStep 1690291 = 2535437) B2535437
theorem B2853569 : Blo 1690045 2853569 := bstep (se 2 (by rfl) ⟨1070088, by rfl⟩ : syracuseStep 2853569 = 2140177) B2140177
theorem B1690307 : Blo 1690045 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B5704397 : Blo 1690045 5704397 := bstep (se 3 (by rfl) ⟨1069574, by rfl⟩ : syracuseStep 5704397 = 2139149) B2139149
theorem B1690323 : Blo 1690045 1690323 := bstep (se 1 (by rfl) ⟨1267742, by rfl⟩ : syracuseStep 1690323 = 2535485) B2535485
theorem B1690339 : Blo 1690045 1690339 := bstep (se 1 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 1690339 = 2535509) B2535509
theorem B26036963 : Blo 1690045 26036963 := bstep (se 1 (by rfl) ⟨19527722, by rfl⟩ : syracuseStep 26036963 = 39055445) B39055445
theorem B1690355 : Blo 1690045 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B5704451 : Blo 1690045 5704451 := bstep (se 1 (by rfl) ⟨4278338, by rfl⟩ : syracuseStep 5704451 = 8556677) B8556677
theorem B1690371 : Blo 1690045 1690371 := bstep (se 1 (by rfl) ⟨1267778, by rfl⟩ : syracuseStep 1690371 = 2535557) B2535557
theorem B21662477 : Blo 1690045 21662477 := bstep (se 3 (by rfl) ⟨4061714, by rfl⟩ : syracuseStep 21662477 = 8123429) B8123429
theorem B3803921 : Blo 1690045 3803921 := bstep (se 2 (by rfl) ⟨1426470, by rfl⟩ : syracuseStep 3803921 = 2852941) B2852941
theorem B1690387 : Blo 1690045 1690387 := bstep (se 1 (by rfl) ⟨1267790, by rfl⟩ : syracuseStep 1690387 = 2535581) B2535581
theorem B1690403 : Blo 1690045 1690403 := bstep (se 1 (by rfl) ⟨1267802, by rfl⟩ : syracuseStep 1690403 = 2535605) B2535605
theorem B3803939 : Blo 1690045 3803939 := bstep (se 1 (by rfl) ⟨2852954, by rfl⟩ : syracuseStep 3803939 = 5705909) B5705909
theorem B1690419 : Blo 1690045 1690419 := bstep (se 1 (by rfl) ⟨1267814, by rfl⟩ : syracuseStep 1690419 = 2535629) B2535629
theorem B2853697 : Blo 1690045 2853697 := bstep (se 2 (by rfl) ⟨1070136, by rfl⟩ : syracuseStep 2853697 = 2140273) B2140273
theorem B1690435 : Blo 1690045 1690435 := bstep (se 1 (by rfl) ⟨1267826, by rfl⟩ : syracuseStep 1690435 = 2535653) B2535653
theorem B1690451 : Blo 1690045 1690451 := bstep (se 1 (by rfl) ⟨1267838, by rfl⟩ : syracuseStep 1690451 = 2535677) B2535677
theorem B6417251 : Blo 1690045 6417251 := bstep (se 1 (by rfl) ⟨4812938, by rfl⟩ : syracuseStep 6417251 = 9625877) B9625877
theorem B1690467 : Blo 1690045 1690467 := bstep (se 1 (by rfl) ⟨1267850, by rfl⟩ : syracuseStep 1690467 = 2535701) B2535701
theorem B4279139 : Blo 1690045 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B2853731 : Blo 1690045 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B5417837 : Blo 1690045 5417837 := bstep (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) B2031689
theorem B6417265 : Blo 1690045 6417265 := bstep (se 2 (by rfl) ⟨2406474, by rfl⟩ : syracuseStep 6417265 = 4812949) B4812949
theorem B20573041 : Blo 1690045 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B1690483 : Blo 1690045 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B1690499 : Blo 1690045 1690499 := bstep (se 1 (by rfl) ⟨1267874, by rfl⟩ : syracuseStep 1690499 = 2535749) B2535749
theorem B1690515 : Blo 1690045 1690515 := bstep (se 1 (by rfl) ⟨1267886, by rfl⟩ : syracuseStep 1690515 = 2535773) B2535773
theorem B1690531 : Blo 1690045 1690531 := bstep (se 1 (by rfl) ⟨1267898, by rfl⟩ : syracuseStep 1690531 = 2535797) B2535797
theorem B1690547 : Blo 1690045 1690547 := bstep (se 1 (by rfl) ⟨1267910, by rfl⟩ : syracuseStep 1690547 = 2535821) B2535821
theorem B1690563 : Blo 1690045 1690563 := bstep (se 1 (by rfl) ⟨1267922, by rfl⟩ : syracuseStep 1690563 = 2535845) B2535845
theorem B1690579 : Blo 1690045 1690579 := bstep (se 1 (by rfl) ⟨1267934, by rfl⟩ : syracuseStep 1690579 = 2535869) B2535869
theorem B1690595 : Blo 1690045 1690595 := bstep (se 1 (by rfl) ⟨1267946, by rfl⟩ : syracuseStep 1690595 = 2535893) B2535893
theorem B2853859 : Blo 1690045 2853859 := bstep (se 1 (by rfl) ⟨2140394, by rfl⟩ : syracuseStep 2853859 = 4280789) B4280789
theorem B1690611 : Blo 1690045 1690611 := bstep (se 1 (by rfl) ⟨1267958, by rfl⟩ : syracuseStep 1690611 = 2535917) B2535917
theorem B1690627 : Blo 1690045 1690627 := bstep (se 1 (by rfl) ⟨1267970, by rfl⟩ : syracuseStep 1690627 = 2535941) B2535941
theorem B5704721 : Blo 1690045 5704721 := bstep (se 2 (by rfl) ⟨2139270, by rfl⟩ : syracuseStep 5704721 = 4278541) B4278541
theorem B1690643 : Blo 1690045 1690643 := bstep (se 1 (by rfl) ⟨1267982, by rfl⟩ : syracuseStep 1690643 = 2535965) B2535965
theorem B4279331 : Blo 1690045 4279331 := bstep (se 1 (by rfl) ⟨3209498, by rfl⟩ : syracuseStep 4279331 = 6418997) B6418997
theorem B1690659 : Blo 1690045 1690659 := bstep (se 1 (by rfl) ⟨1267994, by rfl⟩ : syracuseStep 1690659 = 2535989) B2535989
theorem B3804209 : Blo 1690045 3804209 := bstep (se 2 (by rfl) ⟨1426578, by rfl⟩ : syracuseStep 3804209 = 2853157) B2853157
theorem B1690675 : Blo 1690045 1690675 := bstep (se 1 (by rfl) ⟨1268006, by rfl⟩ : syracuseStep 1690675 = 2536013) B2536013
theorem B1690691 : Blo 1690045 1690691 := bstep (se 1 (by rfl) ⟨1268018, by rfl⟩ : syracuseStep 1690691 = 2536037) B2536037
theorem B3804227 : Blo 1690045 3804227 := bstep (se 1 (by rfl) ⟨2853170, by rfl⟩ : syracuseStep 3804227 = 5706341) B5706341
theorem B1690707 : Blo 1690045 1690707 := bstep (se 1 (by rfl) ⟨1268030, by rfl⟩ : syracuseStep 1690707 = 2536061) B2536061
theorem B1690723 : Blo 1690045 1690723 := bstep (se 1 (by rfl) ⟨1268042, by rfl⟩ : syracuseStep 1690723 = 2536085) B2536085
theorem B2854001 : Blo 1690045 2854001 := bstep (se 2 (by rfl) ⟨1070250, by rfl⟩ : syracuseStep 2854001 = 2140501) B2140501
theorem B1690739 : Blo 1690045 1690739 := bstep (se 1 (by rfl) ⟨1268054, by rfl⟩ : syracuseStep 1690739 = 2536109) B2536109
theorem B1690755 : Blo 1690045 1690755 := bstep (se 1 (by rfl) ⟨1268066, by rfl⟩ : syracuseStep 1690755 = 2536133) B2536133
theorem B1690771 : Blo 1690045 1690771 := bstep (se 1 (by rfl) ⟨1268078, by rfl⟩ : syracuseStep 1690771 = 2536157) B2536157
theorem B1690787 : Blo 1690045 1690787 := bstep (se 1 (by rfl) ⟨1268090, by rfl⟩ : syracuseStep 1690787 = 2536181) B2536181
theorem B1690803 : Blo 1690045 1690803 := bstep (se 1 (by rfl) ⟨1268102, by rfl⟩ : syracuseStep 1690803 = 2536205) B2536205
theorem B1690819 : Blo 1690045 1690819 := bstep (se 1 (by rfl) ⟨1268114, by rfl⟩ : syracuseStep 1690819 = 2536229) B2536229
theorem B1690835 : Blo 1690045 1690835 := bstep (se 1 (by rfl) ⟨1268126, by rfl⟩ : syracuseStep 1690835 = 2536253) B2536253
theorem B1690851 : Blo 1690045 1690851 := bstep (se 1 (by rfl) ⟨1268138, by rfl⟩ : syracuseStep 1690851 = 2536277) B2536277
theorem B18279665 : Blo 1690045 18279665 := bstep (se 2 (by rfl) ⟨6854874, by rfl⟩ : syracuseStep 18279665 = 13709749) B13709749
theorem B2854129 : Blo 1690045 2854129 := bstep (se 2 (by rfl) ⟨1070298, by rfl⟩ : syracuseStep 2854129 = 2140597) B2140597
theorem B1690867 : Blo 1690045 1690867 := bstep (se 1 (by rfl) ⟨1268150, by rfl⟩ : syracuseStep 1690867 = 2536301) B2536301
theorem B1690883 : Blo 1690045 1690883 := bstep (se 1 (by rfl) ⟨1268162, by rfl⟩ : syracuseStep 1690883 = 2536325) B2536325
theorem B1690899 : Blo 1690045 1690899 := bstep (se 1 (by rfl) ⟨1268174, by rfl⟩ : syracuseStep 1690899 = 2536349) B2536349
theorem B1928467 : Blo 1690045 1928467 := bstep (se 1 (by rfl) ⟨1446350, by rfl⟩ : syracuseStep 1928467 = 2892701) B2892701
theorem B2854163 : Blo 1690045 2854163 := bstep (se 1 (by rfl) ⟨2140622, by rfl⟩ : syracuseStep 2854163 = 4281245) B4281245
theorem B1690915 : Blo 1690045 1690915 := bstep (se 1 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 1690915 = 2536373) B2536373
theorem B1690931 : Blo 1690045 1690931 := bstep (se 1 (by rfl) ⟨1268198, by rfl⟩ : syracuseStep 1690931 = 2536397) B2536397
theorem B1690947 : Blo 1690045 1690947 := bstep (se 1 (by rfl) ⟨1268210, by rfl⟩ : syracuseStep 1690947 = 2536421) B2536421
theorem B3804497 : Blo 1690045 3804497 := bstep (se 2 (by rfl) ⟨1426686, by rfl⟩ : syracuseStep 3804497 = 2853373) B2853373
theorem B1690963 : Blo 1690045 1690963 := bstep (se 1 (by rfl) ⟨1268222, by rfl⟩ : syracuseStep 1690963 = 2536445) B2536445
theorem B3804515 : Blo 1690045 3804515 := bstep (se 1 (by rfl) ⟨2853386, by rfl⟩ : syracuseStep 3804515 = 5706773) B5706773
theorem B1690979 : Blo 1690045 1690979 := bstep (se 1 (by rfl) ⟨1268234, by rfl⟩ : syracuseStep 1690979 = 2536469) B2536469
theorem B1690995 : Blo 1690045 1690995 := bstep (se 1 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 1690995 = 2536493) B2536493
theorem B1691011 : Blo 1690045 1691011 := bstep (se 1 (by rfl) ⟨1268258, by rfl⟩ : syracuseStep 1691011 = 2536517) B2536517
theorem B1691027 : Blo 1690045 1691027 := bstep (se 1 (by rfl) ⟨1268270, by rfl⟩ : syracuseStep 1691027 = 2536541) B2536541
theorem B2854291 : Blo 1690045 2854291 := bstep (se 1 (by rfl) ⟨2140718, by rfl⟩ : syracuseStep 2854291 = 4281437) B4281437
theorem B1691043 : Blo 1690045 1691043 := bstep (se 1 (by rfl) ⟨1268282, by rfl⟩ : syracuseStep 1691043 = 2536565) B2536565
theorem B1691059 : Blo 1690045 1691059 := bstep (se 1 (by rfl) ⟨1268294, by rfl⟩ : syracuseStep 1691059 = 2536589) B2536589
theorem B1691075 : Blo 1690045 1691075 := bstep (se 1 (by rfl) ⟨1268306, by rfl⟩ : syracuseStep 1691075 = 2536613) B2536613
theorem B1691091 : Blo 1690045 1691091 := bstep (se 1 (by rfl) ⟨1268318, by rfl⟩ : syracuseStep 1691091 = 2536637) B2536637
theorem B1691107 : Blo 1690045 1691107 := bstep (se 1 (by rfl) ⟨1268330, by rfl⟩ : syracuseStep 1691107 = 2536661) B2536661
theorem B1691123 : Blo 1690045 1691123 := bstep (se 1 (by rfl) ⟨1268342, by rfl⟩ : syracuseStep 1691123 = 2536685) B2536685
theorem B1691139 : Blo 1690045 1691139 := bstep (se 1 (by rfl) ⟨1268354, by rfl⟩ : syracuseStep 1691139 = 2536709) B2536709
theorem B1691155 : Blo 1690045 1691155 := bstep (se 1 (by rfl) ⟨1268366, by rfl⟩ : syracuseStep 1691155 = 2536733) B2536733
theorem B2854433 : Blo 1690045 2854433 := bstep (se 2 (by rfl) ⟨1070412, by rfl⟩ : syracuseStep 2854433 = 2140825) B2140825
theorem B1691171 : Blo 1690045 1691171 := bstep (se 1 (by rfl) ⟨1268378, by rfl⟩ : syracuseStep 1691171 = 2536757) B2536757
theorem B5705261 : Blo 1690045 5705261 := bstep (se 3 (by rfl) ⟨1069736, by rfl⟩ : syracuseStep 5705261 = 2139473) B2139473
theorem B1691187 : Blo 1690045 1691187 := bstep (se 1 (by rfl) ⟨1268390, by rfl⟩ : syracuseStep 1691187 = 2536781) B2536781
theorem B1691203 : Blo 1690045 1691203 := bstep (se 1 (by rfl) ⟨1268402, by rfl⟩ : syracuseStep 1691203 = 2536805) B2536805
theorem B17583685 : Blo 1690045 17583685 := bstep (se 4 (by rfl) ⟨1648470, by rfl⟩ : syracuseStep 17583685 = 3296941) B3296941
theorem B1691219 : Blo 1690045 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B5705315 : Blo 1690045 5705315 := bstep (se 1 (by rfl) ⟨4278986, by rfl⟩ : syracuseStep 5705315 = 8557973) B8557973
theorem B1691235 : Blo 1690045 1691235 := bstep (se 1 (by rfl) ⟨1268426, by rfl⟩ : syracuseStep 1691235 = 2536853) B2536853
theorem B3804785 : Blo 1690045 3804785 := bstep (se 2 (by rfl) ⟨1426794, by rfl⟩ : syracuseStep 3804785 = 2853589) B2853589
theorem B1691251 : Blo 1690045 1691251 := bstep (se 1 (by rfl) ⟨1268438, by rfl⟩ : syracuseStep 1691251 = 2536877) B2536877
theorem B3804803 : Blo 1690045 3804803 := bstep (se 1 (by rfl) ⟨2853602, by rfl⟩ : syracuseStep 3804803 = 5707205) B5707205
theorem B1691267 : Blo 1690045 1691267 := bstep (se 1 (by rfl) ⟨1268450, by rfl⟩ : syracuseStep 1691267 = 2536901) B2536901
theorem B1691283 : Blo 1690045 1691283 := bstep (se 1 (by rfl) ⟨1268462, by rfl⟩ : syracuseStep 1691283 = 2536925) B2536925
theorem B1691299 : Blo 1690045 1691299 := bstep (se 1 (by rfl) ⟨1268474, by rfl⟩ : syracuseStep 1691299 = 2536949) B2536949
theorem B2535089 : Blo 1690045 2535089 := bstep (se 2 (by rfl) ⟨950658, by rfl⟩ : syracuseStep 2535089 = 1901317) B1901317
theorem B1691315 : Blo 1690045 1691315 := bstep (se 1 (by rfl) ⟨1268486, by rfl⟩ : syracuseStep 1691315 = 2536973) B2536973
theorem B2535107 : Blo 1690045 2535107 := bstep (se 1 (by rfl) ⟨1901330, by rfl⟩ : syracuseStep 2535107 = 3802661) B3802661
theorem B1691331 : Blo 1690045 1691331 := bstep (se 1 (by rfl) ⟨1268498, by rfl⟩ : syracuseStep 1691331 = 2536997) B2536997
theorem B1806035 : Blo 1690045 1806035 := bstep (se 1 (by rfl) ⟨1354526, by rfl⟩ : syracuseStep 1806035 = 2709053) B2709053
theorem B1691347 : Blo 1690045 1691347 := bstep (se 1 (by rfl) ⟨1268510, by rfl⟩ : syracuseStep 1691347 = 2537021) B2537021
theorem B2535137 : Blo 1690045 2535137 := bstep (se 2 (by rfl) ⟨950676, by rfl⟩ : syracuseStep 2535137 = 1901353) B1901353
theorem B1691363 : Blo 1690045 1691363 := bstep (se 1 (by rfl) ⟨1268522, by rfl⟩ : syracuseStep 1691363 = 2537045) B2537045
theorem B2535155 : Blo 1690045 2535155 := bstep (se 1 (by rfl) ⟨1901366, by rfl⟩ : syracuseStep 2535155 = 3802733) B3802733
theorem B1691379 : Blo 1690045 1691379 := bstep (se 1 (by rfl) ⟨1268534, by rfl⟩ : syracuseStep 1691379 = 2537069) B2537069
theorem B1691395 : Blo 1690045 1691395 := bstep (se 1 (by rfl) ⟨1268546, by rfl⟩ : syracuseStep 1691395 = 2537093) B2537093
theorem B2535185 : Blo 1690045 2535185 := bstep (se 2 (by rfl) ⟨950694, by rfl⟩ : syracuseStep 2535185 = 1901389) B1901389
theorem B1691411 : Blo 1690045 1691411 := bstep (se 1 (by rfl) ⟨1268558, by rfl⟩ : syracuseStep 1691411 = 2537117) B2537117
theorem B2535203 : Blo 1690045 2535203 := bstep (se 1 (by rfl) ⟨1901402, by rfl⟩ : syracuseStep 2535203 = 3802805) B3802805
theorem B1691427 : Blo 1690045 1691427 := bstep (se 1 (by rfl) ⟨1268570, by rfl⟩ : syracuseStep 1691427 = 2537141) B2537141
theorem B1691443 : Blo 1690045 1691443 := bstep (se 1 (by rfl) ⟨1268582, by rfl⟩ : syracuseStep 1691443 = 2537165) B2537165
theorem B2535233 : Blo 1690045 2535233 := bstep (se 2 (by rfl) ⟨950712, by rfl⟩ : syracuseStep 2535233 = 1901425) B1901425
theorem B1691459 : Blo 1690045 1691459 := bstep (se 1 (by rfl) ⟨1268594, by rfl⟩ : syracuseStep 1691459 = 2537189) B2537189
theorem B2535251 : Blo 1690045 2535251 := bstep (se 1 (by rfl) ⟨1901438, by rfl⟩ : syracuseStep 2535251 = 3802877) B3802877
theorem B1691475 : Blo 1690045 1691475 := bstep (se 1 (by rfl) ⟨1268606, by rfl⟩ : syracuseStep 1691475 = 2537213) B2537213
theorem B1691491 : Blo 1690045 1691491 := bstep (se 1 (by rfl) ⟨1268618, by rfl⟩ : syracuseStep 1691491 = 2537237) B2537237
theorem B10170211 : Blo 1690045 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B2535281 : Blo 1690045 2535281 := bstep (se 2 (by rfl) ⟨950730, by rfl⟩ : syracuseStep 2535281 = 1901461) B1901461
theorem B5705585 : Blo 1690045 5705585 := bstep (se 2 (by rfl) ⟨2139594, by rfl⟩ : syracuseStep 5705585 = 4279189) B4279189
theorem B1691507 : Blo 1690045 1691507 := bstep (se 1 (by rfl) ⟨1268630, by rfl⟩ : syracuseStep 1691507 = 2537261) B2537261
theorem B2535299 : Blo 1690045 2535299 := bstep (se 1 (by rfl) ⟨1901474, by rfl⟩ : syracuseStep 2535299 = 3802949) B3802949
theorem B1691523 : Blo 1690045 1691523 := bstep (se 1 (by rfl) ⟨1268642, by rfl⟩ : syracuseStep 1691523 = 2537285) B2537285
theorem B3805073 : Blo 1690045 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B1691539 : Blo 1690045 1691539 := bstep (se 1 (by rfl) ⟨1268654, by rfl⟩ : syracuseStep 1691539 = 2537309) B2537309
theorem B2535329 : Blo 1690045 2535329 := bstep (se 2 (by rfl) ⟨950748, by rfl⟩ : syracuseStep 2535329 = 1901497) B1901497
theorem B3805091 : Blo 1690045 3805091 := bstep (se 1 (by rfl) ⟨2853818, by rfl⟩ : syracuseStep 3805091 = 5707637) B5707637
theorem B2535347 : Blo 1690045 2535347 := bstep (se 1 (by rfl) ⟨1901510, by rfl⟩ : syracuseStep 2535347 = 3803021) B3803021
theorem B2535377 : Blo 1690045 2535377 := bstep (se 2 (by rfl) ⟨950766, by rfl⟩ : syracuseStep 2535377 = 1901533) B1901533
theorem B4280273 : Blo 1690045 4280273 := bstep (se 2 (by rfl) ⟨1605102, by rfl⟩ : syracuseStep 4280273 = 3210205) B3210205
theorem B8556515 : Blo 1690045 8556515 := bstep (se 1 (by rfl) ⟨6417386, by rfl⟩ : syracuseStep 8556515 = 12834773) B12834773
theorem B2535395 : Blo 1690045 2535395 := bstep (se 1 (by rfl) ⟨1901546, by rfl⟩ : syracuseStep 2535395 = 3803093) B3803093
theorem B16470001 : Blo 1690045 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B2535425 : Blo 1690045 2535425 := bstep (se 2 (by rfl) ⟨950784, by rfl⟩ : syracuseStep 2535425 = 1901569) B1901569
theorem B4280323 : Blo 1690045 4280323 := bstep (se 1 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 4280323 = 6420485) B6420485
theorem B2535443 : Blo 1690045 2535443 := bstep (se 1 (by rfl) ⟨1901582, by rfl⟩ : syracuseStep 2535443 = 3803165) B3803165
theorem B2707489 : Blo 1690045 2707489 := bstep (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) B2030617
theorem B2535473 : Blo 1690045 2535473 := bstep (se 2 (by rfl) ⟨950802, by rfl⟩ : syracuseStep 2535473 = 1901605) B1901605
theorem B2535491 : Blo 1690045 2535491 := bstep (se 1 (by rfl) ⟨1901618, by rfl⟩ : syracuseStep 2535491 = 3803237) B3803237
theorem B2535521 : Blo 1690045 2535521 := bstep (se 2 (by rfl) ⟨950820, by rfl⟩ : syracuseStep 2535521 = 1901641) B1901641
theorem B10834033 : Blo 1690045 10834033 := bstep (se 2 (by rfl) ⟨4062762, by rfl⟩ : syracuseStep 10834033 = 8125525) B8125525
theorem B2535539 : Blo 1690045 2535539 := bstep (se 1 (by rfl) ⟨1901654, by rfl⟩ : syracuseStep 2535539 = 3803309) B3803309
theorem B2535569 : Blo 1690045 2535569 := bstep (se 2 (by rfl) ⟨950838, by rfl⟩ : syracuseStep 2535569 = 1901677) B1901677
theorem B4280465 : Blo 1690045 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B2535587 : Blo 1690045 2535587 := bstep (se 1 (by rfl) ⟨1901690, by rfl⟩ : syracuseStep 2535587 = 3803381) B3803381
theorem B3805361 : Blo 1690045 3805361 := bstep (se 2 (by rfl) ⟨1427010, by rfl⟩ : syracuseStep 3805361 = 2854021) B2854021
theorem B2535617 : Blo 1690045 2535617 := bstep (se 2 (by rfl) ⟨950856, by rfl⟩ : syracuseStep 2535617 = 1901713) B1901713
theorem B4812995 : Blo 1690045 4812995 := bstep (se 1 (by rfl) ⟨3609746, by rfl⟩ : syracuseStep 4812995 = 7219493) B7219493
theorem B3805379 : Blo 1690045 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B2535635 : Blo 1690045 2535635 := bstep (se 1 (by rfl) ⟨1901726, by rfl⟩ : syracuseStep 2535635 = 3803453) B3803453
theorem B7712995 : Blo 1690045 7712995 := bstep (se 1 (by rfl) ⟨5784746, by rfl⟩ : syracuseStep 7712995 = 11569493) B11569493
theorem B2535665 : Blo 1690045 2535665 := bstep (se 2 (by rfl) ⟨950874, by rfl⟩ : syracuseStep 2535665 = 1901749) B1901749
theorem B2535683 : Blo 1690045 2535683 := bstep (se 1 (by rfl) ⟨1901762, by rfl⟩ : syracuseStep 2535683 = 3803525) B3803525
theorem B42250517 : Blo 1690045 42250517 := bstep (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) B1980493
theorem B2535713 : Blo 1690045 2535713 := bstep (se 2 (by rfl) ⟨950892, by rfl⟩ : syracuseStep 2535713 = 1901785) B1901785
theorem B6091043 : Blo 1690045 6091043 := bstep (se 1 (by rfl) ⟨4568282, by rfl⟩ : syracuseStep 6091043 = 9136565) B9136565
theorem B6418723 : Blo 1690045 6418723 := bstep (se 1 (by rfl) ⟨4814042, by rfl⟩ : syracuseStep 6418723 = 9628085) B9628085
theorem B2535731 : Blo 1690045 2535731 := bstep (se 1 (by rfl) ⟨1901798, by rfl⟩ : syracuseStep 2535731 = 3803597) B3803597
theorem B2535761 : Blo 1690045 2535761 := bstep (se 2 (by rfl) ⟨950910, by rfl⟩ : syracuseStep 2535761 = 1901821) B1901821
theorem B2535779 : Blo 1690045 2535779 := bstep (se 1 (by rfl) ⟨1901834, by rfl⟩ : syracuseStep 2535779 = 3803669) B3803669
theorem B2535809 : Blo 1690045 2535809 := bstep (se 2 (by rfl) ⟨950928, by rfl⟩ : syracuseStep 2535809 = 1901857) B1901857
theorem B5706125 : Blo 1690045 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B2535827 : Blo 1690045 2535827 := bstep (se 1 (by rfl) ⟨1901870, by rfl⟩ : syracuseStep 2535827 = 3803741) B3803741
theorem B2535857 : Blo 1690045 2535857 := bstep (se 2 (by rfl) ⟨950946, by rfl⟩ : syracuseStep 2535857 = 1901893) B1901893
theorem B5706179 : Blo 1690045 5706179 := bstep (se 1 (by rfl) ⟨4279634, by rfl⟩ : syracuseStep 5706179 = 8559269) B8559269
theorem B2535875 : Blo 1690045 2535875 := bstep (se 1 (by rfl) ⟨1901906, by rfl⟩ : syracuseStep 2535875 = 3803813) B3803813
theorem B3805649 : Blo 1690045 3805649 := bstep (se 2 (by rfl) ⟨1427118, by rfl⟩ : syracuseStep 3805649 = 2854237) B2854237
theorem B2535905 : Blo 1690045 2535905 := bstep (se 2 (by rfl) ⟨950964, by rfl⟩ : syracuseStep 2535905 = 1901929) B1901929
theorem B8794595 : Blo 1690045 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B3805667 : Blo 1690045 3805667 := bstep (se 1 (by rfl) ⟨2854250, by rfl⟩ : syracuseStep 3805667 = 5708501) B5708501
theorem B2535923 : Blo 1690045 2535923 := bstep (se 1 (by rfl) ⟨1901942, by rfl⟩ : syracuseStep 2535923 = 3803885) B3803885
theorem B12186125 : Blo 1690045 12186125 := bstep (se 3 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 12186125 = 4569797) B4569797
theorem B2535953 : Blo 1690045 2535953 := bstep (se 2 (by rfl) ⟨950982, by rfl⟩ : syracuseStep 2535953 = 1901965) B1901965
theorem B2535971 : Blo 1690045 2535971 := bstep (se 1 (by rfl) ⟨1901978, by rfl⟩ : syracuseStep 2535971 = 3803957) B3803957
theorem B4878893 : Blo 1690045 4878893 := bstep (se 3 (by rfl) ⟨914792, by rfl⟩ : syracuseStep 4878893 = 1829585) B1829585
theorem B10711601 : Blo 1690045 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B2536001 : Blo 1690045 2536001 := bstep (se 2 (by rfl) ⟨951000, by rfl⟩ : syracuseStep 2536001 = 1902001) B1902001
theorem B2536019 : Blo 1690045 2536019 := bstep (se 1 (by rfl) ⟨1902014, by rfl⟩ : syracuseStep 2536019 = 3804029) B3804029
theorem B28881521 : Blo 1690045 28881521 := bstep (se 2 (by rfl) ⟨10830570, by rfl⟩ : syracuseStep 28881521 = 21661141) B21661141
theorem B2536049 : Blo 1690045 2536049 := bstep (se 2 (by rfl) ⟨951018, by rfl⟩ : syracuseStep 2536049 = 1902037) B1902037
theorem B2536067 : Blo 1690045 2536067 := bstep (se 1 (by rfl) ⟨1902050, by rfl⟩ : syracuseStep 2536067 = 3804101) B3804101
theorem B2536097 : Blo 1690045 2536097 := bstep (se 2 (by rfl) ⟨951036, by rfl⟩ : syracuseStep 2536097 = 1902073) B1902073
theorem B2536115 : Blo 1690045 2536115 := bstep (se 1 (by rfl) ⟨1902086, by rfl⟩ : syracuseStep 2536115 = 3804173) B3804173
theorem B2536145 : Blo 1690045 2536145 := bstep (se 2 (by rfl) ⟨951054, by rfl⟩ : syracuseStep 2536145 = 1902109) B1902109
theorem B5706449 : Blo 1690045 5706449 := bstep (se 2 (by rfl) ⟨2139918, by rfl⟩ : syracuseStep 5706449 = 4279837) B4279837
theorem B2536163 : Blo 1690045 2536163 := bstep (se 1 (by rfl) ⟨1902122, by rfl⟩ : syracuseStep 2536163 = 3804245) B3804245
theorem B3805937 : Blo 1690045 3805937 := bstep (se 2 (by rfl) ⟨1427226, by rfl⟩ : syracuseStep 3805937 = 2854453) B2854453
theorem B2536193 : Blo 1690045 2536193 := bstep (se 2 (by rfl) ⟨951072, by rfl⟩ : syracuseStep 2536193 = 1902145) B1902145
theorem B3805955 : Blo 1690045 3805955 := bstep (se 1 (by rfl) ⟨2854466, by rfl⟩ : syracuseStep 3805955 = 5708933) B5708933
theorem B8557325 : Blo 1690045 8557325 := bstep (se 3 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 8557325 = 3208997) B3208997
theorem B2536211 : Blo 1690045 2536211 := bstep (se 1 (by rfl) ⟨1902158, by rfl⟩ : syracuseStep 2536211 = 3804317) B3804317
theorem B2536241 : Blo 1690045 2536241 := bstep (se 2 (by rfl) ⟨951090, by rfl⟩ : syracuseStep 2536241 = 1902181) B1902181
theorem B2536259 : Blo 1690045 2536259 := bstep (se 1 (by rfl) ⟨1902194, by rfl⟩ : syracuseStep 2536259 = 3804389) B3804389
theorem B2536289 : Blo 1690045 2536289 := bstep (se 2 (by rfl) ⟨951108, by rfl⟩ : syracuseStep 2536289 = 1902217) B1902217
theorem B2536307 : Blo 1690045 2536307 := bstep (se 1 (by rfl) ⟨1902230, by rfl⟩ : syracuseStep 2536307 = 3804461) B3804461
theorem B2536337 : Blo 1690045 2536337 := bstep (se 2 (by rfl) ⟨951126, by rfl⟩ : syracuseStep 2536337 = 1902253) B1902253
theorem B2708387 : Blo 1690045 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B2536355 : Blo 1690045 2536355 := bstep (se 1 (by rfl) ⟨1902266, by rfl⟩ : syracuseStep 2536355 = 3804533) B3804533
theorem B7222193 : Blo 1690045 7222193 := bstep (se 2 (by rfl) ⟨2708322, by rfl⟩ : syracuseStep 7222193 = 5416645) B5416645
theorem B2536385 : Blo 1690045 2536385 := bstep (se 2 (by rfl) ⟨951144, by rfl⟩ : syracuseStep 2536385 = 1902289) B1902289
theorem B2536403 : Blo 1690045 2536403 := bstep (se 1 (by rfl) ⟨1902302, by rfl⟩ : syracuseStep 2536403 = 3804605) B3804605
theorem B2536433 : Blo 1690045 2536433 := bstep (se 2 (by rfl) ⟨951162, by rfl⟩ : syracuseStep 2536433 = 1902325) B1902325
theorem B2536451 : Blo 1690045 2536451 := bstep (se 1 (by rfl) ⟨1902338, by rfl⟩ : syracuseStep 2536451 = 3804677) B3804677
theorem B2536481 : Blo 1690045 2536481 := bstep (se 2 (by rfl) ⟨951180, by rfl⟩ : syracuseStep 2536481 = 1902361) B1902361
theorem B2536499 : Blo 1690045 2536499 := bstep (se 1 (by rfl) ⟨1902374, by rfl⟩ : syracuseStep 2536499 = 3804749) B3804749
theorem B6853709 : Blo 1690045 6853709 := bstep (se 3 (by rfl) ⟨1285070, by rfl⟩ : syracuseStep 6853709 = 2570141) B2570141
theorem B2536529 : Blo 1690045 2536529 := bstep (se 2 (by rfl) ⟨951198, by rfl⟩ : syracuseStep 2536529 = 1902397) B1902397
theorem B4633681 : Blo 1690045 4633681 := bstep (se 2 (by rfl) ⟨1737630, by rfl⟩ : syracuseStep 4633681 = 3475261) B3475261
theorem B2708579 : Blo 1690045 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B2536547 : Blo 1690045 2536547 := bstep (se 1 (by rfl) ⟨1902410, by rfl⟩ : syracuseStep 2536547 = 3804821) B3804821
theorem B4281457 : Blo 1690045 4281457 := bstep (se 2 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 4281457 = 3211093) B3211093
theorem B2536577 : Blo 1690045 2536577 := bstep (se 2 (by rfl) ⟨951216, by rfl⟩ : syracuseStep 2536577 = 1902433) B1902433
theorem B9139333 : Blo 1690045 9139333 := bstep (se 4 (by rfl) ⟨856812, by rfl⟩ : syracuseStep 9139333 = 1713625) B1713625
theorem B2536595 : Blo 1690045 2536595 := bstep (se 1 (by rfl) ⟨1902446, by rfl⟩ : syracuseStep 2536595 = 3804893) B3804893
theorem B2536625 : Blo 1690045 2536625 := bstep (se 2 (by rfl) ⟨951234, by rfl⟩ : syracuseStep 2536625 = 1902469) B1902469
theorem B2536643 : Blo 1690045 2536643 := bstep (se 1 (by rfl) ⟨1902482, by rfl⟩ : syracuseStep 2536643 = 3804965) B3804965
theorem B2536673 : Blo 1690045 2536673 := bstep (se 2 (by rfl) ⟨951252, by rfl⟩ : syracuseStep 2536673 = 1902505) B1902505
theorem B5706989 : Blo 1690045 5706989 := bstep (se 3 (by rfl) ⟨1070060, by rfl⟩ : syracuseStep 5706989 = 2140121) B2140121
theorem B3609841 : Blo 1690045 3609841 := bstep (se 2 (by rfl) ⟨1353690, by rfl⟩ : syracuseStep 3609841 = 2707381) B2707381
theorem B2536691 : Blo 1690045 2536691 := bstep (se 1 (by rfl) ⟨1902518, by rfl⟩ : syracuseStep 2536691 = 3805037) B3805037
theorem B1955075 : Blo 1690045 1955075 := bstep (se 1 (by rfl) ⟨1466306, by rfl⟩ : syracuseStep 1955075 = 2932613) B2932613
theorem B2536721 : Blo 1690045 2536721 := bstep (se 2 (by rfl) ⟨951270, by rfl⟩ : syracuseStep 2536721 = 1902541) B1902541
theorem B5707043 : Blo 1690045 5707043 := bstep (se 1 (by rfl) ⟨4280282, by rfl⟩ : syracuseStep 5707043 = 8560565) B8560565
theorem B2536739 : Blo 1690045 2536739 := bstep (se 1 (by rfl) ⟨1902554, by rfl⟩ : syracuseStep 2536739 = 3805109) B3805109
theorem B2536769 : Blo 1690045 2536769 := bstep (se 2 (by rfl) ⟨951288, by rfl⟩ : syracuseStep 2536769 = 1902577) B1902577
theorem B2536787 : Blo 1690045 2536787 := bstep (se 1 (by rfl) ⟨1902590, by rfl⟩ : syracuseStep 2536787 = 3805181) B3805181
theorem B2536817 : Blo 1690045 2536817 := bstep (se 2 (by rfl) ⟨951306, by rfl⟩ : syracuseStep 2536817 = 1902613) B1902613
theorem B2536835 : Blo 1690045 2536835 := bstep (se 1 (by rfl) ⟨1902626, by rfl⟩ : syracuseStep 2536835 = 3805253) B3805253
theorem B4814225 : Blo 1690045 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B2536865 : Blo 1690045 2536865 := bstep (se 2 (by rfl) ⟨951324, by rfl⟩ : syracuseStep 2536865 = 1902649) B1902649
theorem B2536883 : Blo 1690045 2536883 := bstep (se 1 (by rfl) ⟨1902662, by rfl⟩ : syracuseStep 2536883 = 3805325) B3805325
theorem B2536913 : Blo 1690045 2536913 := bstep (se 2 (by rfl) ⟨951342, by rfl⟩ : syracuseStep 2536913 = 1902685) B1902685
theorem B2536931 : Blo 1690045 2536931 := bstep (se 1 (by rfl) ⟨1902698, by rfl⟩ : syracuseStep 2536931 = 3805397) B3805397
theorem B2536961 : Blo 1690045 2536961 := bstep (se 2 (by rfl) ⟨951360, by rfl⟩ : syracuseStep 2536961 = 1902721) B1902721
theorem B2536979 : Blo 1690045 2536979 := bstep (se 1 (by rfl) ⟨1902734, by rfl⟩ : syracuseStep 2536979 = 3805469) B3805469
theorem B6854179 : Blo 1690045 6854179 := bstep (se 1 (by rfl) ⟨5140634, by rfl⟩ : syracuseStep 6854179 = 10281269) B10281269
theorem B6346289 : Blo 1690045 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B5707313 : Blo 1690045 5707313 := bstep (se 2 (by rfl) ⟨2140242, by rfl⟩ : syracuseStep 5707313 = 4280485) B4280485
theorem B2537009 : Blo 1690045 2537009 := bstep (se 2 (by rfl) ⟨951378, by rfl⟩ : syracuseStep 2537009 = 1902757) B1902757
theorem B2537027 : Blo 1690045 2537027 := bstep (se 1 (by rfl) ⟨1902770, by rfl⟩ : syracuseStep 2537027 = 3805541) B3805541
theorem B2537057 : Blo 1690045 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B2537075 : Blo 1690045 2537075 := bstep (se 1 (by rfl) ⟨1902806, by rfl⟩ : syracuseStep 2537075 = 3805613) B3805613
theorem B9139853 : Blo 1690045 9139853 := bstep (se 3 (by rfl) ⟨1713722, by rfl⟩ : syracuseStep 9139853 = 3427445) B3427445
theorem B18282125 : Blo 1690045 18282125 := bstep (se 3 (by rfl) ⟨3427898, by rfl⟩ : syracuseStep 18282125 = 6855797) B6855797
theorem B2537105 : Blo 1690045 2537105 := bstep (se 2 (by rfl) ⟨951414, by rfl⟩ : syracuseStep 2537105 = 1902829) B1902829
theorem B2537123 : Blo 1690045 2537123 := bstep (se 1 (by rfl) ⟨1902842, by rfl⟩ : syracuseStep 2537123 = 3805685) B3805685
theorem B2537153 : Blo 1690045 2537153 := bstep (se 2 (by rfl) ⟨951432, by rfl⟩ : syracuseStep 2537153 = 1902865) B1902865
theorem B2537171 : Blo 1690045 2537171 := bstep (se 1 (by rfl) ⟨1902878, by rfl⟩ : syracuseStep 2537171 = 3805757) B3805757
theorem B2537201 : Blo 1690045 2537201 := bstep (se 2 (by rfl) ⟨951450, by rfl⟩ : syracuseStep 2537201 = 1902901) B1902901
theorem B2537219 : Blo 1690045 2537219 := bstep (se 1 (by rfl) ⟨1902914, by rfl⟩ : syracuseStep 2537219 = 3805829) B3805829
theorem B2537249 : Blo 1690045 2537249 := bstep (se 2 (by rfl) ⟨951468, by rfl⟩ : syracuseStep 2537249 = 1902937) B1902937
theorem B2537267 : Blo 1690045 2537267 := bstep (se 1 (by rfl) ⟨1902950, by rfl⟩ : syracuseStep 2537267 = 3805901) B3805901
theorem B2537297 : Blo 1690045 2537297 := bstep (se 2 (by rfl) ⟨951486, by rfl⟩ : syracuseStep 2537297 = 1902973) B1902973
theorem B2537315 : Blo 1690045 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B7714673 : Blo 1690045 7714673 := bstep (se 2 (by rfl) ⟨2893002, by rfl⟩ : syracuseStep 7714673 = 5786005) B5786005
theorem B11564977 : Blo 1690045 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B32511941 : Blo 1690045 32511941 := bstep (se 4 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 32511941 = 6095989) B6095989
theorem B3209233 : Blo 1690045 3209233 := bstep (se 2 (by rfl) ⟨1203462, by rfl⟩ : syracuseStep 3209233 = 2406925) B2406925
theorem B11573297 : Blo 1690045 11573297 := bstep (se 2 (by rfl) ⟨4339986, by rfl⟩ : syracuseStep 11573297 = 8679973) B8679973
theorem B5707853 : Blo 1690045 5707853 := bstep (se 3 (by rfl) ⟨1070222, by rfl⟩ : syracuseStep 5707853 = 2140445) B2140445
theorem B73095281 : Blo 1690045 73095281 := bstep (se 2 (by rfl) ⟨27410730, by rfl⟩ : syracuseStep 73095281 = 54821461) B54821461
theorem B5707907 : Blo 1690045 5707907 := bstep (se 1 (by rfl) ⟨4280930, by rfl⟩ : syracuseStep 5707907 = 8561861) B8561861
theorem B13015181 : Blo 1690045 13015181 := bstep (se 3 (by rfl) ⟨2440346, by rfl⟩ : syracuseStep 13015181 = 4880693) B4880693
theorem B43341965 : Blo 1690045 43341965 := bstep (se 3 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 43341965 = 16253237) B16253237
theorem B3856625 : Blo 1690045 3856625 := bstep (se 2 (by rfl) ⟨1446234, by rfl⟩ : syracuseStep 3856625 = 2892469) B2892469
theorem B3569923 : Blo 1690045 3569923 := bstep (se 1 (by rfl) ⟨2677442, by rfl⟩ : syracuseStep 3569923 = 5354885) B5354885
theorem B9632141 : Blo 1690045 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B5708177 : Blo 1690045 5708177 := bstep (se 2 (by rfl) ⟨2140566, by rfl⟩ : syracuseStep 5708177 = 4281133) B4281133
theorem B3209635 : Blo 1690045 3209635 := bstep (se 1 (by rfl) ⟨2407226, by rfl⟩ : syracuseStep 3209635 = 4814453) B4814453
theorem B6420941 : Blo 1690045 6420941 := bstep (se 3 (by rfl) ⟨1203926, by rfl⟩ : syracuseStep 6420941 = 2407853) B2407853
theorem B3209681 : Blo 1690045 3209681 := bstep (se 2 (by rfl) ⟨1203630, by rfl⟩ : syracuseStep 3209681 = 2407261) B2407261
theorem B14637581 : Blo 1690045 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B2407153 : Blo 1690045 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B3209969 : Blo 1690045 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B4815683 : Blo 1690045 4815683 := bstep (se 1 (by rfl) ⟨3611762, by rfl⟩ : syracuseStep 4815683 = 7223525) B7223525
theorem B2407249 : Blo 1690045 2407249 := bstep (se 2 (by rfl) ⟨902718, by rfl⟩ : syracuseStep 2407249 = 1805437) B1805437
theorem B5143405 : Blo 1690045 5143405 := bstep (se 3 (by rfl) ⟨964388, by rfl⟩ : syracuseStep 5143405 = 1928777) B1928777
theorem B5708717 : Blo 1690045 5708717 := bstep (se 3 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 5708717 = 2140769) B2140769
theorem B5708771 : Blo 1690045 5708771 := bstep (se 1 (by rfl) ⟨4281578, by rfl⟩ : syracuseStep 5708771 = 8563157) B8563157
theorem B3046403 : Blo 1690045 3046403 := bstep (se 1 (by rfl) ⟨2284802, by rfl⟩ : syracuseStep 3046403 = 4569605) B4569605
theorem B2030627 : Blo 1690045 2030627 := bstep (se 1 (by rfl) ⟨1522970, by rfl⟩ : syracuseStep 2030627 = 3045941) B3045941
theorem B3611729 : Blo 1690045 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B2030675 : Blo 1690045 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B2030771 : Blo 1690045 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B2407745 : Blo 1690045 2407745 := bstep (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) B1805809
theorem B7224653 : Blo 1690045 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B3210691 : Blo 1690045 3210691 := bstep (se 1 (by rfl) ⟨2408018, by rfl⟩ : syracuseStep 3210691 = 4816037) B4816037
theorem B3046979 : Blo 1690045 3046979 := bstep (se 1 (by rfl) ⟨2285234, by rfl⟩ : syracuseStep 3046979 = 4570469) B4570469
theorem B4570705 : Blo 1690045 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B4816493 : Blo 1690045 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B8560241 : Blo 1690045 8560241 := bstep (se 2 (by rfl) ⟨3210090, by rfl⟩ : syracuseStep 8560241 = 6420181) B6420181
theorem B2891539 : Blo 1690045 2891539 := bstep (se 1 (by rfl) ⟨2168654, by rfl⟩ : syracuseStep 2891539 = 4337309) B4337309
theorem B4816685 : Blo 1690045 4816685 := bstep (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) B1806257
theorem B3211139 : Blo 1690045 3211139 := bstep (se 1 (by rfl) ⟨2408354, by rfl⟩ : syracuseStep 3211139 = 4816709) B4816709
theorem B19267469 : Blo 1690045 19267469 := bstep (se 3 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 19267469 = 7225301) B7225301
theorem B5415005 : Blo 1690045 5415005 := bstep (se 3 (by rfl) ⟨1015313, by rfl⟩ : syracuseStep 5415005 = 2030627) B2030627
theorem B5415133 : Blo 1690045 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B4759897 : Blo 1690045 4759897 := bstep (se 2 (by rfl) ⟨1784961, by rfl⟩ : syracuseStep 4759897 = 3569923) B3569923
theorem B8126851 : Blo 1690045 8126851 := bstep (se 1 (by rfl) ⟨6095138, by rfl⟩ : syracuseStep 8126851 = 12190277) B12190277
theorem B5415389 : Blo 1690045 5415389 := bstep (se 3 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 5415389 = 2030771) B2030771
theorem B9265765 : Blo 1690045 9265765 := bstep (se 4 (by rfl) ⟨868665, by rfl⟩ : syracuseStep 9265765 = 1737331) B1737331
theorem B1901335 : Blo 1690045 1901335 := bstep (se 1 (by rfl) ⟨1426001, by rfl⟩ : syracuseStep 1901335 = 2852003) B2852003
theorem B3474355 : Blo 1690045 3474355 := bstep (se 1 (by rfl) ⟨2605766, by rfl⟩ : syracuseStep 3474355 = 5211533) B5211533
theorem B1901515 : Blo 1690045 1901515 := bstep (se 1 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 1901515 = 2852273) B2852273
theorem B1901623 : Blo 1690045 1901623 := bstep (se 1 (by rfl) ⟨1426217, by rfl⟩ : syracuseStep 1901623 = 2852435) B2852435
theorem B6857873 : Blo 1690045 6857873 := bstep (se 2 (by rfl) ⟨2571702, by rfl⟩ : syracuseStep 6857873 = 5143405) B5143405
theorem B2852057 : Blo 1690045 2852057 := bstep (se 2 (by rfl) ⟨1069521, by rfl⟩ : syracuseStep 2852057 = 2139043) B2139043
theorem B1901803 : Blo 1690045 1901803 := bstep (se 1 (by rfl) ⟨1426352, by rfl⟩ : syracuseStep 1901803 = 2852705) B2852705
theorem B1901911 : Blo 1690045 1901911 := bstep (se 1 (by rfl) ⟨1426433, by rfl⟩ : syracuseStep 1901911 = 2852867) B2852867
theorem B2852185 : Blo 1690045 2852185 := bstep (se 2 (by rfl) ⟨1069569, by rfl⟩ : syracuseStep 2852185 = 2139139) B2139139
theorem B28894643 : Blo 1690045 28894643 := bstep (se 1 (by rfl) ⟨21670982, by rfl⟩ : syracuseStep 28894643 = 43341965) B43341965
theorem B6178241 : Blo 1690045 6178241 := bstep (se 2 (by rfl) ⟨2316840, by rfl⟩ : syracuseStep 6178241 = 4633681) B4633681
theorem B13010381 : Blo 1690045 13010381 := bstep (se 3 (by rfl) ⟨2439446, by rfl⟩ : syracuseStep 13010381 = 4878893) B4878893
theorem B3802625 : Blo 1690045 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B1902091 : Blo 1690045 1902091 := bstep (se 1 (by rfl) ⟨1426568, by rfl⟩ : syracuseStep 1902091 = 2853137) B2853137
theorem B24364637 : Blo 1690045 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B1902199 : Blo 1690045 1902199 := bstep (se 1 (by rfl) ⟨1426649, by rfl⟩ : syracuseStep 1902199 = 2853299) B2853299
theorem B2139787 : Blo 1690045 2139787 := bstep (se 1 (by rfl) ⟨1604840, by rfl⟩ : syracuseStep 2139787 = 3209681) B3209681
theorem B9758387 : Blo 1690045 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B3802841 : Blo 1690045 3802841 := bstep (se 2 (by rfl) ⟨1426065, by rfl⟩ : syracuseStep 3802841 = 2852131) B2852131
theorem B12838661 : Blo 1690045 12838661 := bstep (se 4 (by rfl) ⟨1203624, by rfl⟩ : syracuseStep 12838661 = 2407249) B2407249
theorem B1902379 : Blo 1690045 1902379 := bstep (se 1 (by rfl) ⟨1426784, by rfl⟩ : syracuseStep 1902379 = 2853569) B2853569
theorem B3802931 : Blo 1690045 3802931 := bstep (se 1 (by rfl) ⟨2852198, by rfl⟩ : syracuseStep 3802931 = 5704397) B5704397
theorem B21661505 : Blo 1690045 21661505 := bstep (se 2 (by rfl) ⟨8123064, by rfl⟩ : syracuseStep 21661505 = 16246129) B16246129
theorem B3802967 : Blo 1690045 3802967 := bstep (se 1 (by rfl) ⟨2852225, by rfl⟩ : syracuseStep 3802967 = 5704451) B5704451
theorem B4278167 : Blo 1690045 4278167 := bstep (se 1 (by rfl) ⟨3208625, by rfl⟩ : syracuseStep 4278167 = 6417251) B6417251
theorem B2852759 : Blo 1690045 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B1902487 : Blo 1690045 1902487 := bstep (se 1 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 1902487 = 2853731) B2853731
theorem B3475457 : Blo 1690045 3475457 := bstep (se 2 (by rfl) ⟨1303296, by rfl⟩ : syracuseStep 3475457 = 2606593) B2606593
theorem B3803147 : Blo 1690045 3803147 := bstep (se 1 (by rfl) ⟨2852360, by rfl⟩ : syracuseStep 3803147 = 5704721) B5704721
theorem B2852887 : Blo 1690045 2852887 := bstep (se 1 (by rfl) ⟨2139665, by rfl⟩ : syracuseStep 2852887 = 4279331) B4279331
theorem B3803201 : Blo 1690045 3803201 := bstep (se 2 (by rfl) ⟨1426200, by rfl⟩ : syracuseStep 3803201 = 2852401) B2852401
theorem B1902667 : Blo 1690045 1902667 := bstep (se 1 (by rfl) ⟨1427000, by rfl⟩ : syracuseStep 1902667 = 2854001) B2854001
theorem B1902775 : Blo 1690045 1902775 := bstep (se 1 (by rfl) ⟨1427081, by rfl⟩ : syracuseStep 1902775 = 2854163) B2854163
theorem B3803417 : Blo 1690045 3803417 := bstep (se 2 (by rfl) ⟨1426281, by rfl⟩ : syracuseStep 3803417 = 2852563) B2852563
theorem B1902955 : Blo 1690045 1902955 := bstep (se 1 (by rfl) ⟨1427216, by rfl⟩ : syracuseStep 1902955 = 2854433) B2854433
theorem B3803507 : Blo 1690045 3803507 := bstep (se 1 (by rfl) ⟨2852630, by rfl⟩ : syracuseStep 3803507 = 5705261) B5705261
theorem B3803543 : Blo 1690045 3803543 := bstep (se 1 (by rfl) ⟨2852657, by rfl⟩ : syracuseStep 3803543 = 5705315) B5705315
theorem B1690059 : Blo 1690045 1690059 := bstep (se 1 (by rfl) ⟨1267544, by rfl⟩ : syracuseStep 1690059 = 2535089) B2535089
theorem B1690071 : Blo 1690045 1690071 := bstep (se 1 (by rfl) ⟨1267553, by rfl⟩ : syracuseStep 1690071 = 2535107) B2535107
theorem B13560281 : Blo 1690045 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B1690091 : Blo 1690045 1690091 := bstep (se 1 (by rfl) ⟨1267568, by rfl⟩ : syracuseStep 1690091 = 2535137) B2535137
theorem B1690103 : Blo 1690045 1690103 := bstep (se 1 (by rfl) ⟨1267577, by rfl⟩ : syracuseStep 1690103 = 2535155) B2535155
theorem B1690123 : Blo 1690045 1690123 := bstep (se 1 (by rfl) ⟨1267592, by rfl⟩ : syracuseStep 1690123 = 2535185) B2535185
theorem B1690135 : Blo 1690045 1690135 := bstep (se 1 (by rfl) ⟨1267601, by rfl⟩ : syracuseStep 1690135 = 2535203) B2535203
theorem B1690155 : Blo 1690045 1690155 := bstep (se 1 (by rfl) ⟨1267616, by rfl⟩ : syracuseStep 1690155 = 2535233) B2535233
theorem B1690167 : Blo 1690045 1690167 := bstep (se 1 (by rfl) ⟨1267625, by rfl⟩ : syracuseStep 1690167 = 2535251) B2535251
theorem B15419969 : Blo 1690045 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B1690187 : Blo 1690045 1690187 := bstep (se 1 (by rfl) ⟨1267640, by rfl⟩ : syracuseStep 1690187 = 2535281) B2535281
theorem B3803723 : Blo 1690045 3803723 := bstep (se 1 (by rfl) ⟨2852792, by rfl⟩ : syracuseStep 3803723 = 5705585) B5705585
theorem B1690199 : Blo 1690045 1690199 := bstep (se 1 (by rfl) ⟨1267649, by rfl⟩ : syracuseStep 1690199 = 2535299) B2535299
theorem B2140759 : Blo 1690045 2140759 := bstep (se 1 (by rfl) ⟨1605569, by rfl⟩ : syracuseStep 2140759 = 3211139) B3211139
theorem B1690219 : Blo 1690045 1690219 := bstep (se 1 (by rfl) ⟨1267664, by rfl⟩ : syracuseStep 1690219 = 2535329) B2535329
theorem B1690231 : Blo 1690045 1690231 := bstep (se 1 (by rfl) ⟨1267673, by rfl⟩ : syracuseStep 1690231 = 2535347) B2535347
theorem B3803777 : Blo 1690045 3803777 := bstep (se 2 (by rfl) ⟨1426416, by rfl⟩ : syracuseStep 3803777 = 2852833) B2852833
theorem B1690251 : Blo 1690045 1690251 := bstep (se 1 (by rfl) ⟨1267688, by rfl⟩ : syracuseStep 1690251 = 2535377) B2535377
theorem B2853515 : Blo 1690045 2853515 := bstep (se 1 (by rfl) ⟨2140136, by rfl⟩ : syracuseStep 2853515 = 4280273) B4280273
theorem B5704343 : Blo 1690045 5704343 := bstep (se 1 (by rfl) ⟨4278257, by rfl⟩ : syracuseStep 5704343 = 8556515) B8556515
theorem B1690263 : Blo 1690045 1690263 := bstep (se 1 (by rfl) ⟨1267697, by rfl⟩ : syracuseStep 1690263 = 2535395) B2535395
theorem B1690283 : Blo 1690045 1690283 := bstep (se 1 (by rfl) ⟨1267712, by rfl⟩ : syracuseStep 1690283 = 2535425) B2535425
theorem B1690295 : Blo 1690045 1690295 := bstep (se 1 (by rfl) ⟨1267721, by rfl⟩ : syracuseStep 1690295 = 2535443) B2535443
theorem B4278977 : Blo 1690045 4278977 := bstep (se 2 (by rfl) ⟨1604616, by rfl⟩ : syracuseStep 4278977 = 3209233) B3209233
theorem B1690315 : Blo 1690045 1690315 := bstep (se 1 (by rfl) ⟨1267736, by rfl⟩ : syracuseStep 1690315 = 2535473) B2535473
theorem B1690327 : Blo 1690045 1690327 := bstep (se 1 (by rfl) ⟨1267745, by rfl⟩ : syracuseStep 1690327 = 2535491) B2535491
theorem B1690347 : Blo 1690045 1690347 := bstep (se 1 (by rfl) ⟨1267760, by rfl⟩ : syracuseStep 1690347 = 2535521) B2535521
theorem B1690359 : Blo 1690045 1690359 := bstep (se 1 (by rfl) ⟨1267769, by rfl⟩ : syracuseStep 1690359 = 2535539) B2535539
theorem B1690379 : Blo 1690045 1690379 := bstep (se 1 (by rfl) ⟨1267784, by rfl⟩ : syracuseStep 1690379 = 2535569) B2535569
theorem B2853643 : Blo 1690045 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B1690391 : Blo 1690045 1690391 := bstep (se 1 (by rfl) ⟨1267793, by rfl⟩ : syracuseStep 1690391 = 2535587) B2535587
theorem B1690411 : Blo 1690045 1690411 := bstep (se 1 (by rfl) ⟨1267808, by rfl⟩ : syracuseStep 1690411 = 2535617) B2535617
theorem B1690423 : Blo 1690045 1690423 := bstep (se 1 (by rfl) ⟨1267817, by rfl⟩ : syracuseStep 1690423 = 2535635) B2535635
theorem B14445377 : Blo 1690045 14445377 := bstep (se 2 (by rfl) ⟨5417016, by rfl⟩ : syracuseStep 14445377 = 10834033) B10834033
theorem B1690443 : Blo 1690045 1690443 := bstep (se 1 (by rfl) ⟨1267832, by rfl⟩ : syracuseStep 1690443 = 2535665) B2535665
theorem B1690455 : Blo 1690045 1690455 := bstep (se 1 (by rfl) ⟨1267841, by rfl⟩ : syracuseStep 1690455 = 2535683) B2535683
theorem B3803993 : Blo 1690045 3803993 := bstep (se 2 (by rfl) ⟨1426497, by rfl⟩ : syracuseStep 3803993 = 2852995) B2852995
theorem B28167011 : Blo 1690045 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B1690475 : Blo 1690045 1690475 := bstep (se 1 (by rfl) ⟨1267856, by rfl⟩ : syracuseStep 1690475 = 2535713) B2535713
theorem B1690487 : Blo 1690045 1690487 := bstep (se 1 (by rfl) ⟨1267865, by rfl⟩ : syracuseStep 1690487 = 2535731) B2535731
theorem B1690507 : Blo 1690045 1690507 := bstep (se 1 (by rfl) ⟨1267880, by rfl⟩ : syracuseStep 1690507 = 2535761) B2535761
theorem B1690519 : Blo 1690045 1690519 := bstep (se 1 (by rfl) ⟨1267889, by rfl⟩ : syracuseStep 1690519 = 2535779) B2535779
theorem B2853785 : Blo 1690045 2853785 := bstep (se 2 (by rfl) ⟨1070169, by rfl⟩ : syracuseStep 2853785 = 2140339) B2140339
theorem B1690539 : Blo 1690045 1690539 := bstep (se 1 (by rfl) ⟨1267904, by rfl⟩ : syracuseStep 1690539 = 2535809) B2535809
theorem B3804083 : Blo 1690045 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B1690551 : Blo 1690045 1690551 := bstep (se 1 (by rfl) ⟨1267913, by rfl⟩ : syracuseStep 1690551 = 2535827) B2535827
theorem B1690571 : Blo 1690045 1690571 := bstep (se 1 (by rfl) ⟨1267928, by rfl⟩ : syracuseStep 1690571 = 2535857) B2535857
theorem B1690583 : Blo 1690045 1690583 := bstep (se 1 (by rfl) ⟨1267937, by rfl⟩ : syracuseStep 1690583 = 2535875) B2535875
theorem B3804119 : Blo 1690045 3804119 := bstep (se 1 (by rfl) ⟨2853089, by rfl⟩ : syracuseStep 3804119 = 5706179) B5706179
theorem B10283993 : Blo 1690045 10283993 := bstep (se 2 (by rfl) ⟨3856497, by rfl⟩ : syracuseStep 10283993 = 7712995) B7712995
theorem B1690603 : Blo 1690045 1690603 := bstep (se 1 (by rfl) ⟨1267952, by rfl⟩ : syracuseStep 1690603 = 2535905) B2535905
theorem B1690615 : Blo 1690045 1690615 := bstep (se 1 (by rfl) ⟨1267961, by rfl⟩ : syracuseStep 1690615 = 2535923) B2535923
theorem B1690635 : Blo 1690045 1690635 := bstep (se 1 (by rfl) ⟨1267976, by rfl⟩ : syracuseStep 1690635 = 2535953) B2535953
theorem B1690647 : Blo 1690045 1690647 := bstep (se 1 (by rfl) ⟨1267985, by rfl⟩ : syracuseStep 1690647 = 2535971) B2535971
theorem B2853913 : Blo 1690045 2853913 := bstep (se 2 (by rfl) ⟨1070217, by rfl⟩ : syracuseStep 2853913 = 2140435) B2140435
theorem B1690667 : Blo 1690045 1690667 := bstep (se 1 (by rfl) ⟨1268000, by rfl⟩ : syracuseStep 1690667 = 2536001) B2536001
theorem B1690679 : Blo 1690045 1690679 := bstep (se 1 (by rfl) ⟨1268009, by rfl⟩ : syracuseStep 1690679 = 2536019) B2536019
theorem B19254347 : Blo 1690045 19254347 := bstep (se 1 (by rfl) ⟨14440760, by rfl⟩ : syracuseStep 19254347 = 28881521) B28881521
theorem B1690699 : Blo 1690045 1690699 := bstep (se 1 (by rfl) ⟨1268024, by rfl⟩ : syracuseStep 1690699 = 2536049) B2536049
theorem B1690711 : Blo 1690045 1690711 := bstep (se 1 (by rfl) ⟨1268033, by rfl⟩ : syracuseStep 1690711 = 2536067) B2536067
theorem B1690731 : Blo 1690045 1690731 := bstep (se 1 (by rfl) ⟨1268048, by rfl⟩ : syracuseStep 1690731 = 2536097) B2536097
theorem B1690743 : Blo 1690045 1690743 := bstep (se 1 (by rfl) ⟨1268057, by rfl⟩ : syracuseStep 1690743 = 2536115) B2536115
theorem B6417539 : Blo 1690045 6417539 := bstep (se 1 (by rfl) ⟨4813154, by rfl⟩ : syracuseStep 6417539 = 9626309) B9626309
theorem B14281859 : Blo 1690045 14281859 := bstep (se 1 (by rfl) ⟨10711394, by rfl⟩ : syracuseStep 14281859 = 21422789) B21422789
theorem B1690763 : Blo 1690045 1690763 := bstep (se 1 (by rfl) ⟨1268072, by rfl⟩ : syracuseStep 1690763 = 2536145) B2536145
theorem B3804299 : Blo 1690045 3804299 := bstep (se 1 (by rfl) ⟨2853224, by rfl⟩ : syracuseStep 3804299 = 5706449) B5706449
theorem B1690775 : Blo 1690045 1690775 := bstep (se 1 (by rfl) ⟨1268081, by rfl⟩ : syracuseStep 1690775 = 2536163) B2536163
theorem B1690795 : Blo 1690045 1690795 := bstep (se 1 (by rfl) ⟨1268096, by rfl⟩ : syracuseStep 1690795 = 2536193) B2536193
theorem B5704883 : Blo 1690045 5704883 := bstep (se 1 (by rfl) ⟨4278662, by rfl⟩ : syracuseStep 5704883 = 8557325) B8557325
theorem B1690807 : Blo 1690045 1690807 := bstep (se 1 (by rfl) ⟨1268105, by rfl⟩ : syracuseStep 1690807 = 2536211) B2536211
theorem B3804353 : Blo 1690045 3804353 := bstep (se 2 (by rfl) ⟨1426632, by rfl⟩ : syracuseStep 3804353 = 2853265) B2853265
theorem B1690827 : Blo 1690045 1690827 := bstep (se 1 (by rfl) ⟨1268120, by rfl⟩ : syracuseStep 1690827 = 2536241) B2536241
theorem B1690839 : Blo 1690045 1690839 := bstep (se 1 (by rfl) ⟨1268129, by rfl⟩ : syracuseStep 1690839 = 2536259) B2536259
theorem B4279513 : Blo 1690045 4279513 := bstep (se 2 (by rfl) ⟨1604817, by rfl⟩ : syracuseStep 4279513 = 3209635) B3209635
theorem B1690859 : Blo 1690045 1690859 := bstep (se 1 (by rfl) ⟨1268144, by rfl⟩ : syracuseStep 1690859 = 2536289) B2536289
theorem B1690871 : Blo 1690045 1690871 := bstep (se 1 (by rfl) ⟨1268153, by rfl⟩ : syracuseStep 1690871 = 2536307) B2536307
theorem B1690891 : Blo 1690045 1690891 := bstep (se 1 (by rfl) ⟨1268168, by rfl⟩ : syracuseStep 1690891 = 2536337) B2536337
theorem B1805591 : Blo 1690045 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B1690903 : Blo 1690045 1690903 := bstep (se 1 (by rfl) ⟨1268177, by rfl⟩ : syracuseStep 1690903 = 2536355) B2536355
theorem B1690923 : Blo 1690045 1690923 := bstep (se 1 (by rfl) ⟨1268192, by rfl⟩ : syracuseStep 1690923 = 2536385) B2536385
theorem B1690935 : Blo 1690045 1690935 := bstep (se 1 (by rfl) ⟨1268201, by rfl⟩ : syracuseStep 1690935 = 2536403) B2536403
theorem B1690955 : Blo 1690045 1690955 := bstep (se 1 (by rfl) ⟨1268216, by rfl⟩ : syracuseStep 1690955 = 2536433) B2536433
theorem B1690967 : Blo 1690045 1690967 := bstep (se 1 (by rfl) ⟨1268225, by rfl⟩ : syracuseStep 1690967 = 2536451) B2536451
theorem B5213533 : Blo 1690045 5213533 := bstep (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) B1955075
theorem B1690987 : Blo 1690045 1690987 := bstep (se 1 (by rfl) ⟨1268240, by rfl⟩ : syracuseStep 1690987 = 2536481) B2536481
theorem B1690999 : Blo 1690045 1690999 := bstep (se 1 (by rfl) ⟨1268249, by rfl⟩ : syracuseStep 1690999 = 2536499) B2536499
theorem B1691019 : Blo 1690045 1691019 := bstep (se 1 (by rfl) ⟨1268264, by rfl⟩ : syracuseStep 1691019 = 2536529) B2536529
theorem B1691031 : Blo 1690045 1691031 := bstep (se 1 (by rfl) ⟨1268273, by rfl⟩ : syracuseStep 1691031 = 2536547) B2536547
theorem B3804569 : Blo 1690045 3804569 := bstep (se 2 (by rfl) ⟨1426713, by rfl⟩ : syracuseStep 3804569 = 2853427) B2853427
theorem B1691051 : Blo 1690045 1691051 := bstep (se 1 (by rfl) ⟨1268288, by rfl⟩ : syracuseStep 1691051 = 2536577) B2536577
theorem B1691063 : Blo 1690045 1691063 := bstep (se 1 (by rfl) ⟨1268297, by rfl⟩ : syracuseStep 1691063 = 2536595) B2536595
theorem B5705153 : Blo 1690045 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B1691083 : Blo 1690045 1691083 := bstep (se 1 (by rfl) ⟨1268312, by rfl⟩ : syracuseStep 1691083 = 2536625) B2536625
theorem B1691095 : Blo 1690045 1691095 := bstep (se 1 (by rfl) ⟨1268321, by rfl⟩ : syracuseStep 1691095 = 2536643) B2536643
theorem B1691115 : Blo 1690045 1691115 := bstep (se 1 (by rfl) ⟨1268336, by rfl⟩ : syracuseStep 1691115 = 2536673) B2536673
theorem B3804659 : Blo 1690045 3804659 := bstep (se 1 (by rfl) ⟨2853494, by rfl⟩ : syracuseStep 3804659 = 5706989) B5706989
theorem B1691127 : Blo 1690045 1691127 := bstep (se 1 (by rfl) ⟨1268345, by rfl⟩ : syracuseStep 1691127 = 2536691) B2536691
theorem B1691147 : Blo 1690045 1691147 := bstep (se 1 (by rfl) ⟨1268360, by rfl⟩ : syracuseStep 1691147 = 2536721) B2536721
theorem B3804695 : Blo 1690045 3804695 := bstep (se 1 (by rfl) ⟨2853521, by rfl⟩ : syracuseStep 3804695 = 5707043) B5707043
theorem B1691159 : Blo 1690045 1691159 := bstep (se 1 (by rfl) ⟨1268369, by rfl⟩ : syracuseStep 1691159 = 2536739) B2536739
theorem B1691179 : Blo 1690045 1691179 := bstep (se 1 (by rfl) ⟨1268384, by rfl⟩ : syracuseStep 1691179 = 2536769) B2536769
theorem B12693037 : Blo 1690045 12693037 := bstep (se 3 (by rfl) ⟨2379944, by rfl⟩ : syracuseStep 12693037 = 4759889) B4759889
theorem B1691191 : Blo 1690045 1691191 := bstep (se 1 (by rfl) ⟨1268393, by rfl⟩ : syracuseStep 1691191 = 2536787) B2536787
theorem B1691211 : Blo 1690045 1691211 := bstep (se 1 (by rfl) ⟨1268408, by rfl⟩ : syracuseStep 1691211 = 2536817) B2536817
theorem B1691223 : Blo 1690045 1691223 := bstep (se 1 (by rfl) ⟨1268417, by rfl⟩ : syracuseStep 1691223 = 2536835) B2536835
theorem B1691243 : Blo 1690045 1691243 := bstep (se 1 (by rfl) ⟨1268432, by rfl⟩ : syracuseStep 1691243 = 2536865) B2536865
theorem B1691255 : Blo 1690045 1691255 := bstep (se 1 (by rfl) ⟨1268441, by rfl⟩ : syracuseStep 1691255 = 2536883) B2536883
theorem B1691275 : Blo 1690045 1691275 := bstep (se 1 (by rfl) ⟨1268456, by rfl⟩ : syracuseStep 1691275 = 2536913) B2536913
theorem B1691287 : Blo 1690045 1691287 := bstep (se 1 (by rfl) ⟨1268465, by rfl⟩ : syracuseStep 1691287 = 2536931) B2536931
theorem B1691307 : Blo 1690045 1691307 := bstep (se 1 (by rfl) ⟨1268480, by rfl⟩ : syracuseStep 1691307 = 2536961) B2536961
theorem B1691319 : Blo 1690045 1691319 := bstep (se 1 (by rfl) ⟨1268489, by rfl⟩ : syracuseStep 1691319 = 2536979) B2536979
theorem B4230859 : Blo 1690045 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B3804875 : Blo 1690045 3804875 := bstep (se 1 (by rfl) ⟨2853656, by rfl⟩ : syracuseStep 3804875 = 5707313) B5707313
theorem B1691339 : Blo 1690045 1691339 := bstep (se 1 (by rfl) ⟨1268504, by rfl⟩ : syracuseStep 1691339 = 2537009) B2537009
theorem B1691351 : Blo 1690045 1691351 := bstep (se 1 (by rfl) ⟨1268513, by rfl⟩ : syracuseStep 1691351 = 2537027) B2537027
theorem B1691371 : Blo 1690045 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B1691383 : Blo 1690045 1691383 := bstep (se 1 (by rfl) ⟨1268537, by rfl⟩ : syracuseStep 1691383 = 2537075) B2537075
theorem B3804929 : Blo 1690045 3804929 := bstep (se 2 (by rfl) ⟨1426848, by rfl⟩ : syracuseStep 3804929 = 2853697) B2853697
theorem B2535179 : Blo 1690045 2535179 := bstep (se 1 (by rfl) ⟨1901384, by rfl⟩ : syracuseStep 2535179 = 3802769) B3802769
theorem B1691403 : Blo 1690045 1691403 := bstep (se 1 (by rfl) ⟨1268552, by rfl⟩ : syracuseStep 1691403 = 2537105) B2537105
theorem B2535191 : Blo 1690045 2535191 := bstep (se 1 (by rfl) ⟨1901393, by rfl⟩ : syracuseStep 2535191 = 3802787) B3802787
theorem B1691415 : Blo 1690045 1691415 := bstep (se 1 (by rfl) ⟨1268561, by rfl⟩ : syracuseStep 1691415 = 2537123) B2537123
theorem B1691435 : Blo 1690045 1691435 := bstep (se 1 (by rfl) ⟨1268576, by rfl⟩ : syracuseStep 1691435 = 2537153) B2537153
theorem B1691447 : Blo 1690045 1691447 := bstep (se 1 (by rfl) ⟨1268585, by rfl⟩ : syracuseStep 1691447 = 2537171) B2537171
theorem B8556353 : Blo 1690045 8556353 := bstep (se 2 (by rfl) ⟨3208632, by rfl⟩ : syracuseStep 8556353 = 6417265) B6417265
theorem B27430721 : Blo 1690045 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B1691467 : Blo 1690045 1691467 := bstep (se 1 (by rfl) ⟨1268600, by rfl⟩ : syracuseStep 1691467 = 2537201) B2537201
theorem B1691479 : Blo 1690045 1691479 := bstep (se 1 (by rfl) ⟨1268609, by rfl⟩ : syracuseStep 1691479 = 2537219) B2537219
theorem B2535257 : Blo 1690045 2535257 := bstep (se 2 (by rfl) ⟨950721, by rfl⟩ : syracuseStep 2535257 = 1901443) B1901443
theorem B1830763 : Blo 1690045 1830763 := bstep (se 1 (by rfl) ⟨1373072, by rfl⟩ : syracuseStep 1830763 = 2746145) B2746145
theorem B1691499 : Blo 1690045 1691499 := bstep (se 1 (by rfl) ⟨1268624, by rfl⟩ : syracuseStep 1691499 = 2537249) B2537249
theorem B1691511 : Blo 1690045 1691511 := bstep (se 1 (by rfl) ⟨1268633, by rfl⟩ : syracuseStep 1691511 = 2537267) B2537267
theorem B1691531 : Blo 1690045 1691531 := bstep (se 1 (by rfl) ⟨1268648, by rfl⟩ : syracuseStep 1691531 = 2537297) B2537297
theorem B7319447 : Blo 1690045 7319447 := bstep (se 1 (by rfl) ⟨5489585, by rfl⟩ : syracuseStep 7319447 = 10979171) B10979171
theorem B1691543 : Blo 1690045 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B2535371 : Blo 1690045 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B2535383 : Blo 1690045 2535383 := bstep (se 1 (by rfl) ⟨1901537, by rfl⟩ : syracuseStep 2535383 = 3803075) B3803075
theorem B3805145 : Blo 1690045 3805145 := bstep (se 2 (by rfl) ⟨1426929, by rfl⟩ : syracuseStep 3805145 = 2853859) B2853859
theorem B5705693 : Blo 1690045 5705693 := bstep (se 3 (by rfl) ⟨1069817, by rfl⟩ : syracuseStep 5705693 = 2139635) B2139635
theorem B2535449 : Blo 1690045 2535449 := bstep (se 2 (by rfl) ⟨950793, by rfl⟩ : syracuseStep 2535449 = 1901587) B1901587
theorem B3805235 : Blo 1690045 3805235 := bstep (se 1 (by rfl) ⟨2853926, by rfl⟩ : syracuseStep 3805235 = 5707853) B5707853
theorem B48730187 : Blo 1690045 48730187 := bstep (se 1 (by rfl) ⟨36547640, by rfl⟩ : syracuseStep 48730187 = 73095281) B73095281
theorem B3805271 : Blo 1690045 3805271 := bstep (se 1 (by rfl) ⟨2853953, by rfl⟩ : syracuseStep 3805271 = 5707907) B5707907
theorem B10285157 : Blo 1690045 10285157 := bstep (se 4 (by rfl) ⟨964233, by rfl⟩ : syracuseStep 10285157 = 1928467) B1928467
theorem B12841091 : Blo 1690045 12841091 := bstep (se 1 (by rfl) ⟨9630818, by rfl⟩ : syracuseStep 12841091 = 19261637) B19261637
theorem B2535563 : Blo 1690045 2535563 := bstep (se 1 (by rfl) ⟨1901672, by rfl⟩ : syracuseStep 2535563 = 3803345) B3803345
theorem B2535575 : Blo 1690045 2535575 := bstep (se 1 (by rfl) ⟨1901681, by rfl⟩ : syracuseStep 2535575 = 3803363) B3803363
theorem B12185777 : Blo 1690045 12185777 := bstep (se 2 (by rfl) ⟨4569666, by rfl⟩ : syracuseStep 12185777 = 9139333) B9139333
theorem B2535641 : Blo 1690045 2535641 := bstep (se 2 (by rfl) ⟨950865, by rfl⟩ : syracuseStep 2535641 = 1901731) B1901731
theorem B3805451 : Blo 1690045 3805451 := bstep (se 1 (by rfl) ⟨2854088, by rfl⟩ : syracuseStep 3805451 = 5708177) B5708177
theorem B4280627 : Blo 1690045 4280627 := bstep (se 1 (by rfl) ⟨3210470, by rfl⟩ : syracuseStep 4280627 = 6420941) B6420941
theorem B4813121 : Blo 1690045 4813121 := bstep (se 2 (by rfl) ⟨1804920, by rfl⟩ : syracuseStep 4813121 = 3609841) B3609841
theorem B3805505 : Blo 1690045 3805505 := bstep (se 2 (by rfl) ⟨1427064, by rfl⟩ : syracuseStep 3805505 = 2854129) B2854129
theorem B2535755 : Blo 1690045 2535755 := bstep (se 1 (by rfl) ⟨1901816, by rfl⟩ : syracuseStep 2535755 = 3803633) B3803633
theorem B2535767 : Blo 1690045 2535767 := bstep (se 1 (by rfl) ⟨1901825, by rfl⟩ : syracuseStep 2535767 = 3803651) B3803651
theorem B2535833 : Blo 1690045 2535833 := bstep (se 2 (by rfl) ⟨950937, by rfl⟩ : syracuseStep 2535833 = 1901875) B1901875
theorem B2535947 : Blo 1690045 2535947 := bstep (se 1 (by rfl) ⟨1901960, by rfl⟩ : syracuseStep 2535947 = 3803921) B3803921
theorem B2535959 : Blo 1690045 2535959 := bstep (se 1 (by rfl) ⟨1901969, by rfl⟩ : syracuseStep 2535959 = 3803939) B3803939
theorem B3805721 : Blo 1690045 3805721 := bstep (se 2 (by rfl) ⟨1427145, by rfl⟩ : syracuseStep 3805721 = 2854291) B2854291
theorem B2536025 : Blo 1690045 2536025 := bstep (se 2 (by rfl) ⟨951009, by rfl⟩ : syracuseStep 2536025 = 1902019) B1902019
theorem B4280921 : Blo 1690045 4280921 := bstep (se 2 (by rfl) ⟨1605345, by rfl⟩ : syracuseStep 4280921 = 3210691) B3210691
theorem B3805811 : Blo 1690045 3805811 := bstep (se 1 (by rfl) ⟨2854358, by rfl⟩ : syracuseStep 3805811 = 5708717) B5708717
theorem B3805847 : Blo 1690045 3805847 := bstep (se 1 (by rfl) ⟨2854385, by rfl⟩ : syracuseStep 3805847 = 5708771) B5708771
theorem B7221953 : Blo 1690045 7221953 := bstep (se 2 (by rfl) ⟨2708232, by rfl⟩ : syracuseStep 7221953 = 5416465) B5416465
theorem B2536139 : Blo 1690045 2536139 := bstep (se 1 (by rfl) ⟨1902104, by rfl⟩ : syracuseStep 2536139 = 3804209) B3804209
theorem B2536151 : Blo 1690045 2536151 := bstep (se 1 (by rfl) ⟨1902113, by rfl⟩ : syracuseStep 2536151 = 3804227) B3804227
theorem B9138905 : Blo 1690045 9138905 := bstep (se 2 (by rfl) ⟨3427089, by rfl⟩ : syracuseStep 9138905 = 6854179) B6854179
theorem B2536217 : Blo 1690045 2536217 := bstep (se 2 (by rfl) ⟨951081, by rfl⟩ : syracuseStep 2536217 = 1902163) B1902163
theorem B12186443 : Blo 1690045 12186443 := bstep (se 1 (by rfl) ⟨9139832, by rfl⟩ : syracuseStep 12186443 = 18279665) B18279665
theorem B2536331 : Blo 1690045 2536331 := bstep (se 1 (by rfl) ⟨1902248, by rfl⟩ : syracuseStep 2536331 = 3804497) B3804497
theorem B2536343 : Blo 1690045 2536343 := bstep (se 1 (by rfl) ⟨1902257, by rfl⟩ : syracuseStep 2536343 = 3804515) B3804515
theorem B2536409 : Blo 1690045 2536409 := bstep (se 2 (by rfl) ⟨951153, by rfl⟩ : syracuseStep 2536409 = 1902307) B1902307
theorem B3855385 : Blo 1690045 3855385 := bstep (se 2 (by rfl) ⟨1445769, by rfl⟩ : syracuseStep 3855385 = 2891539) B2891539
theorem B5706827 : Blo 1690045 5706827 := bstep (se 1 (by rfl) ⟨4280120, by rfl⟩ : syracuseStep 5706827 = 8560241) B8560241
theorem B2536523 : Blo 1690045 2536523 := bstep (se 1 (by rfl) ⟨1902392, by rfl⟩ : syracuseStep 2536523 = 3804785) B3804785
theorem B2536535 : Blo 1690045 2536535 := bstep (se 1 (by rfl) ⟨1902401, by rfl⟩ : syracuseStep 2536535 = 3804803) B3804803
theorem B2536601 : Blo 1690045 2536601 := bstep (se 2 (by rfl) ⟨951225, by rfl⟩ : syracuseStep 2536601 = 1902451) B1902451
theorem B2536715 : Blo 1690045 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B2536727 : Blo 1690045 2536727 := bstep (se 1 (by rfl) ⟨1902545, by rfl⟩ : syracuseStep 2536727 = 3805091) B3805091
theorem B21960001 : Blo 1690045 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B5707097 : Blo 1690045 5707097 := bstep (se 2 (by rfl) ⟨2140161, by rfl⟩ : syracuseStep 5707097 = 4280323) B4280323
theorem B2536793 : Blo 1690045 2536793 := bstep (se 2 (by rfl) ⟨951297, by rfl⟩ : syracuseStep 2536793 = 1902595) B1902595
theorem B4568413 : Blo 1690045 4568413 := bstep (se 3 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 4568413 = 1713155) B1713155
theorem B2168203 : Blo 1690045 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B2536907 : Blo 1690045 2536907 := bstep (se 1 (by rfl) ⟨1902680, by rfl⟩ : syracuseStep 2536907 = 3805361) B3805361
theorem B3208663 : Blo 1690045 3208663 := bstep (se 1 (by rfl) ⟨2406497, by rfl⟩ : syracuseStep 3208663 = 4812995) B4812995
theorem B2536919 : Blo 1690045 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B14439941 : Blo 1690045 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B2536985 : Blo 1690045 2536985 := bstep (se 2 (by rfl) ⟨951369, by rfl⟩ : syracuseStep 2536985 = 1902739) B1902739
theorem B7222877 : Blo 1690045 7222877 := bstep (se 3 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 7222877 = 2708579) B2708579
theorem B2537099 : Blo 1690045 2537099 := bstep (se 1 (by rfl) ⟨1902824, by rfl⟩ : syracuseStep 2537099 = 3805649) B3805649
theorem B5863063 : Blo 1690045 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B2709143 : Blo 1690045 2709143 := bstep (se 1 (by rfl) ⟨2031857, by rfl⟩ : syracuseStep 2709143 = 4063715) B4063715
theorem B2537111 : Blo 1690045 2537111 := bstep (se 1 (by rfl) ⟨1902833, by rfl⟩ : syracuseStep 2537111 = 3805667) B3805667
theorem B8124083 : Blo 1690045 8124083 := bstep (se 1 (by rfl) ⟨6093062, by rfl⟩ : syracuseStep 8124083 = 12186125) B12186125
theorem B93779653 : Blo 1690045 93779653 := bstep (se 4 (by rfl) ⟨8791842, by rfl⟩ : syracuseStep 93779653 = 17583685) B17583685
theorem B7141067 : Blo 1690045 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B34707149 : Blo 1690045 34707149 := bstep (se 3 (by rfl) ⟨6507590, by rfl⟩ : syracuseStep 34707149 = 13015181) B13015181
theorem B3610327 : Blo 1690045 3610327 := bstep (se 1 (by rfl) ⟨2707745, by rfl⟩ : syracuseStep 3610327 = 5415491) B5415491
theorem B8558297 : Blo 1690045 8558297 := bstep (se 2 (by rfl) ⟨3209361, by rfl⟩ : syracuseStep 8558297 = 6418723) B6418723
theorem B2537177 : Blo 1690045 2537177 := bstep (se 2 (by rfl) ⟨951441, by rfl⟩ : syracuseStep 2537177 = 1902883) B1902883
theorem B2537291 : Blo 1690045 2537291 := bstep (se 1 (by rfl) ⟨1902968, by rfl⟩ : syracuseStep 2537291 = 3805937) B3805937
theorem B2709335 : Blo 1690045 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B2537303 : Blo 1690045 2537303 := bstep (se 1 (by rfl) ⟨1902977, by rfl⟩ : syracuseStep 2537303 = 3805955) B3805955
theorem B4814795 : Blo 1690045 4814795 := bstep (se 1 (by rfl) ⟨3611096, by rfl⟩ : syracuseStep 4814795 = 7222193) B7222193
theorem B2709463 : Blo 1690045 2709463 := bstep (se 1 (by rfl) ⟨2032097, by rfl⟩ : syracuseStep 2709463 = 4064195) B4064195
theorem B2406361 : Blo 1690045 2406361 := bstep (se 2 (by rfl) ⟨902385, by rfl⟩ : syracuseStep 2406361 = 1804771) B1804771
theorem B5707799 : Blo 1690045 5707799 := bstep (se 1 (by rfl) ⟨4280849, by rfl⟩ : syracuseStep 5707799 = 8561699) B8561699
theorem B4569139 : Blo 1690045 4569139 := bstep (se 1 (by rfl) ⟨3426854, by rfl⟩ : syracuseStep 4569139 = 6853709) B6853709
theorem B16242781 : Blo 1690045 16242781 := bstep (se 3 (by rfl) ⟨3045521, by rfl⟩ : syracuseStep 16242781 = 6091043) B6091043
theorem B6420653 : Blo 1690045 6420653 := bstep (se 3 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 6420653 = 2407745) B2407745
theorem B14440625 : Blo 1690045 14440625 := bstep (se 2 (by rfl) ⟨5415234, by rfl⟩ : syracuseStep 14440625 = 10830469) B10830469
theorem B3209483 : Blo 1690045 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B3209537 : Blo 1690045 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B6093235 : Blo 1690045 6093235 := bstep (se 1 (by rfl) ⟨4569926, by rfl⟩ : syracuseStep 6093235 = 9139853) B9139853
theorem B12188083 : Blo 1690045 12188083 := bstep (se 1 (by rfl) ⟨9141062, by rfl⟩ : syracuseStep 12188083 = 18282125) B18282125
theorem B3611147 : Blo 1690045 3611147 := bstep (se 1 (by rfl) ⟨2708360, by rfl⟩ : syracuseStep 3611147 = 5416721) B5416721
theorem B5708339 : Blo 1690045 5708339 := bstep (se 1 (by rfl) ⟨4281254, by rfl⟩ : syracuseStep 5708339 = 8562509) B8562509
theorem B5143115 : Blo 1690045 5143115 := bstep (se 1 (by rfl) ⟨3857336, by rfl⟩ : syracuseStep 5143115 = 7714673) B7714673
theorem B21674627 : Blo 1690045 21674627 := bstep (se 1 (by rfl) ⟨16255970, by rfl⟩ : syracuseStep 21674627 = 32511941) B32511941
theorem B7715531 : Blo 1690045 7715531 := bstep (se 1 (by rfl) ⟨5786648, by rfl⟩ : syracuseStep 7715531 = 11573297) B11573297
theorem B5708609 : Blo 1690045 5708609 := bstep (se 2 (by rfl) ⟨2140728, by rfl⟩ : syracuseStep 5708609 = 4281457) B4281457
theorem B2571083 : Blo 1690045 2571083 := bstep (se 1 (by rfl) ⟨1928312, by rfl⟩ : syracuseStep 2571083 = 3856625) B3856625
theorem B6421427 : Blo 1690045 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B17357975 : Blo 1690045 17357975 := bstep (se 1 (by rfl) ⟨13018481, by rfl⟩ : syracuseStep 17357975 = 26036963) B26036963
theorem B14441651 : Blo 1690045 14441651 := bstep (se 1 (by rfl) ⟨10831238, by rfl⟩ : syracuseStep 14441651 = 21662477) B21662477
theorem B3210455 : Blo 1690045 3210455 := bstep (se 1 (by rfl) ⟨2407841, by rfl⟩ : syracuseStep 3210455 = 4815683) B4815683
theorem B4816093 : Blo 1690045 4816093 := bstep (se 3 (by rfl) ⟨903017, by rfl⟩ : syracuseStep 4816093 = 1806035) B1806035
theorem B3611891 : Blo 1690045 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B8559917 : Blo 1690045 8559917 := bstep (se 3 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 8559917 = 3209969) B3209969
theorem B2030935 : Blo 1690045 2030935 := bstep (se 1 (by rfl) ⟨1523201, by rfl⟩ : syracuseStep 2030935 = 3046403) B3046403
theorem B2407819 : Blo 1690045 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B6094273 : Blo 1690045 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B12844493 : Blo 1690045 12844493 := bstep (se 3 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 12844493 = 4816685) B4816685
theorem B4816435 : Blo 1690045 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B2031319 : Blo 1690045 2031319 := bstep (se 1 (by rfl) ⟨1523489, by rfl⟩ : syracuseStep 2031319 = 3046979) B3046979
theorem B3210995 : Blo 1690045 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B12844979 : Blo 1690045 12844979 := bstep (se 1 (by rfl) ⟨9633734, by rfl⟩ : syracuseStep 12844979 = 19267469) B19267469
theorem B8560727 : Blo 1690045 8560727 := bstep (se 1 (by rfl) ⟨6420545, by rfl⟩ : syracuseStep 8560727 = 12841091) B12841091
theorem B27427085 : Blo 1690045 27427085 := bstep (se 3 (by rfl) ⟨5142578, by rfl⟩ : syracuseStep 27427085 = 10285157) B10285157
theorem B8561213 : Blo 1690045 8561213 := bstep (se 3 (by rfl) ⟨1605227, by rfl⟩ : syracuseStep 8561213 = 3210455) B3210455
theorem B4571915 : Blo 1690045 4571915 := bstep (se 1 (by rfl) ⟨3428936, by rfl⟩ : syracuseStep 4571915 = 6857873) B6857873
theorem B12354353 : Blo 1690045 12354353 := bstep (se 2 (by rfl) ⟨4632882, by rfl⟩ : syracuseStep 12354353 = 9265765) B9265765
theorem B1901371 : Blo 1690045 1901371 := bstep (se 1 (by rfl) ⟨1426028, by rfl⟩ : syracuseStep 1901371 = 2852057) B2852057
theorem B9626627 : Blo 1690045 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B6505591 : Blo 1690045 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B5416055 : Blo 1690045 5416055 := bstep (se 1 (by rfl) ⟨4062041, by rfl⟩ : syracuseStep 5416055 = 8124083) B8124083
theorem B4760711 : Blo 1690045 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B16475309 : Blo 1690045 16475309 := bstep (se 3 (by rfl) ⟨3089120, by rfl⟩ : syracuseStep 16475309 = 6178241) B6178241
theorem B2852111 : Blo 1690045 2852111 := bstep (se 1 (by rfl) ⟨2139083, by rfl⟩ : syracuseStep 2852111 = 4278167) B4278167
theorem B1901839 : Blo 1690045 1901839 := bstep (se 1 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 1901839 = 2852759) B2852759
theorem B9627083 : Blo 1690045 9627083 := bstep (se 1 (by rfl) ⟨7220312, by rfl⟩ : syracuseStep 9627083 = 14440625) B14440625
theorem B2139691 : Blo 1690045 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B29280001 : Blo 1690045 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B1902343 : Blo 1690045 1902343 := bstep (se 1 (by rfl) ⟨1426757, by rfl⟩ : syracuseStep 1902343 = 2853515) B2853515
theorem B3802895 : Blo 1690045 3802895 := bstep (se 1 (by rfl) ⟨2852171, by rfl⟩ : syracuseStep 3802895 = 5704343) B5704343
theorem B3802913 : Blo 1690045 3802913 := bstep (se 2 (by rfl) ⟨1426092, by rfl⟩ : syracuseStep 3802913 = 2852185) B2852185
theorem B2852651 : Blo 1690045 2852651 := bstep (se 1 (by rfl) ⟨2139488, by rfl⟩ : syracuseStep 2852651 = 4278977) B4278977
theorem B1714055 : Blo 1690045 1714055 := bstep (se 1 (by rfl) ⟨1285541, by rfl⟩ : syracuseStep 1714055 = 2571083) B2571083
theorem B18778007 : Blo 1690045 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B1902523 : Blo 1690045 1902523 := bstep (se 1 (by rfl) ⟨1426892, by rfl⟩ : syracuseStep 1902523 = 2853785) B2853785
theorem B4278217 : Blo 1690045 4278217 := bstep (se 2 (by rfl) ⟨1604331, by rfl⟩ : syracuseStep 4278217 = 3208663) B3208663
theorem B4278359 : Blo 1690045 4278359 := bstep (se 1 (by rfl) ⟨3208769, by rfl⟩ : syracuseStep 4278359 = 6417539) B6417539
theorem B9521239 : Blo 1690045 9521239 := bstep (se 1 (by rfl) ⟨7140929, by rfl⟩ : syracuseStep 9521239 = 14281859) B14281859
theorem B3803255 : Blo 1690045 3803255 := bstep (se 1 (by rfl) ⟨2852441, by rfl⟩ : syracuseStep 3803255 = 5704883) B5704883
theorem B9627767 : Blo 1690045 9627767 := bstep (se 1 (by rfl) ⟨7220825, by rfl⟩ : syracuseStep 9627767 = 14441651) B14441651
theorem B2853049 : Blo 1690045 2853049 := bstep (se 2 (by rfl) ⟨1069893, by rfl⟩ : syracuseStep 2853049 = 2139787) B2139787
theorem B7817417 : Blo 1690045 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B3803435 : Blo 1690045 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B8562995 : Blo 1690045 8562995 := bstep (se 1 (by rfl) ⟨6422246, by rfl⟩ : syracuseStep 8562995 = 12844493) B12844493
theorem B2140663 : Blo 1690045 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B1690119 : Blo 1690045 1690119 := bstep (se 1 (by rfl) ⟨1267589, by rfl⟩ : syracuseStep 1690119 = 2535179) B2535179
theorem B1690127 : Blo 1690045 1690127 := bstep (se 1 (by rfl) ⟨1267595, by rfl⟩ : syracuseStep 1690127 = 2535191) B2535191
theorem B5704235 : Blo 1690045 5704235 := bstep (se 1 (by rfl) ⟨4278176, by rfl⟩ : syracuseStep 5704235 = 8556353) B8556353
theorem B18287147 : Blo 1690045 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B1690171 : Blo 1690045 1690171 := bstep (se 1 (by rfl) ⟨1267628, by rfl⟩ : syracuseStep 1690171 = 2535257) B2535257
theorem B8563319 : Blo 1690045 8563319 := bstep (se 1 (by rfl) ⟨6422489, by rfl⟩ : syracuseStep 8563319 = 12844979) B12844979
theorem B1690247 : Blo 1690045 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B1690255 : Blo 1690045 1690255 := bstep (se 1 (by rfl) ⟨1267691, by rfl⟩ : syracuseStep 1690255 = 2535383) B2535383
theorem B3803795 : Blo 1690045 3803795 := bstep (se 1 (by rfl) ⟨2852846, by rfl⟩ : syracuseStep 3803795 = 5705693) B5705693
theorem B1690299 : Blo 1690045 1690299 := bstep (se 1 (by rfl) ⟨1267724, by rfl⟩ : syracuseStep 1690299 = 2535449) B2535449
theorem B3803849 : Blo 1690045 3803849 := bstep (se 2 (by rfl) ⟨1426443, by rfl⟩ : syracuseStep 3803849 = 2852887) B2852887
theorem B1690375 : Blo 1690045 1690375 := bstep (se 1 (by rfl) ⟨1267781, by rfl⟩ : syracuseStep 1690375 = 2535563) B2535563
theorem B1690383 : Blo 1690045 1690383 := bstep (se 1 (by rfl) ⟨1267787, by rfl⟩ : syracuseStep 1690383 = 2535575) B2535575
theorem B1690427 : Blo 1690045 1690427 := bstep (se 1 (by rfl) ⟨1267820, by rfl⟩ : syracuseStep 1690427 = 2535641) B2535641
theorem B2853751 : Blo 1690045 2853751 := bstep (se 1 (by rfl) ⟨2140313, by rfl⟩ : syracuseStep 2853751 = 4280627) B4280627
theorem B1690503 : Blo 1690045 1690503 := bstep (se 1 (by rfl) ⟨1267877, by rfl⟩ : syracuseStep 1690503 = 2535755) B2535755
theorem B1690511 : Blo 1690045 1690511 := bstep (se 1 (by rfl) ⟨1267883, by rfl⟩ : syracuseStep 1690511 = 2535767) B2535767
theorem B1690555 : Blo 1690045 1690555 := bstep (se 1 (by rfl) ⟨1267916, by rfl⟩ : syracuseStep 1690555 = 2535833) B2535833
theorem B7220177 : Blo 1690045 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B1690631 : Blo 1690045 1690631 := bstep (se 1 (by rfl) ⟨1267973, by rfl⟩ : syracuseStep 1690631 = 2535947) B2535947
theorem B1690639 : Blo 1690045 1690639 := bstep (se 1 (by rfl) ⟨1267979, by rfl⟩ : syracuseStep 1690639 = 2535959) B2535959
theorem B1690683 : Blo 1690045 1690683 := bstep (se 1 (by rfl) ⟨1268012, by rfl⟩ : syracuseStep 1690683 = 2536025) B2536025
theorem B2853947 : Blo 1690045 2853947 := bstep (se 1 (by rfl) ⟨2140460, by rfl⟩ : syracuseStep 2853947 = 4280921) B4280921
theorem B1690759 : Blo 1690045 1690759 := bstep (se 1 (by rfl) ⟨1268069, by rfl⟩ : syracuseStep 1690759 = 2536139) B2536139
theorem B1690767 : Blo 1690045 1690767 := bstep (se 1 (by rfl) ⟨1268075, by rfl⟩ : syracuseStep 1690767 = 2536151) B2536151
theorem B1690811 : Blo 1690045 1690811 := bstep (se 1 (by rfl) ⟨1268108, by rfl⟩ : syracuseStep 1690811 = 2536217) B2536217
theorem B1690887 : Blo 1690045 1690887 := bstep (se 1 (by rfl) ⟨1268165, by rfl⟩ : syracuseStep 1690887 = 2536331) B2536331
theorem B1690895 : Blo 1690045 1690895 := bstep (se 1 (by rfl) ⟨1268171, by rfl⟩ : syracuseStep 1690895 = 2536343) B2536343
theorem B1690939 : Blo 1690045 1690939 := bstep (se 1 (by rfl) ⟨1268204, by rfl⟩ : syracuseStep 1690939 = 2536409) B2536409
theorem B3804551 : Blo 1690045 3804551 := bstep (se 1 (by rfl) ⟨2853413, by rfl⟩ : syracuseStep 3804551 = 5706827) B5706827
theorem B1691015 : Blo 1690045 1691015 := bstep (se 1 (by rfl) ⟨1268261, by rfl⟩ : syracuseStep 1691015 = 2536523) B2536523
theorem B1691023 : Blo 1690045 1691023 := bstep (se 1 (by rfl) ⟨1268267, by rfl⟩ : syracuseStep 1691023 = 2536535) B2536535
theorem B1691067 : Blo 1690045 1691067 := bstep (se 1 (by rfl) ⟨1268300, by rfl⟩ : syracuseStep 1691067 = 2536601) B2536601
theorem B2854345 : Blo 1690045 2854345 := bstep (se 2 (by rfl) ⟨1070379, by rfl⟩ : syracuseStep 2854345 = 2140759) B2140759
theorem B1691143 : Blo 1690045 1691143 := bstep (se 1 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 1691143 = 2536715) B2536715
theorem B1691151 : Blo 1690045 1691151 := bstep (se 1 (by rfl) ⟨1268363, by rfl⟩ : syracuseStep 1691151 = 2536727) B2536727
theorem B3804731 : Blo 1690045 3804731 := bstep (se 1 (by rfl) ⟨2853548, by rfl⟩ : syracuseStep 3804731 = 5707097) B5707097
theorem B1691195 : Blo 1690045 1691195 := bstep (se 1 (by rfl) ⟨1268396, by rfl⟩ : syracuseStep 1691195 = 2536793) B2536793
theorem B19263095 : Blo 1690045 19263095 := bstep (se 1 (by rfl) ⟨14447321, by rfl⟩ : syracuseStep 19263095 = 28894643) B28894643
theorem B1691271 : Blo 1690045 1691271 := bstep (se 1 (by rfl) ⟨1268453, by rfl⟩ : syracuseStep 1691271 = 2536907) B2536907
theorem B1691279 : Blo 1690045 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B2535083 : Blo 1690045 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B3804857 : Blo 1690045 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B1691323 : Blo 1690045 1691323 := bstep (se 1 (by rfl) ⟨1268492, by rfl⟩ : syracuseStep 1691323 = 2536985) B2536985
theorem B2535113 : Blo 1690045 2535113 := bstep (se 2 (by rfl) ⟨950667, by rfl⟩ : syracuseStep 2535113 = 1901335) B1901335
theorem B1691399 : Blo 1690045 1691399 := bstep (se 1 (by rfl) ⟨1268549, by rfl⟩ : syracuseStep 1691399 = 2537099) B2537099
theorem B1806095 : Blo 1690045 1806095 := bstep (se 1 (by rfl) ⟨1354571, by rfl⟩ : syracuseStep 1806095 = 2709143) B2709143
theorem B1691407 : Blo 1690045 1691407 := bstep (se 1 (by rfl) ⟨1268555, by rfl⟩ : syracuseStep 1691407 = 2537111) B2537111
theorem B23138099 : Blo 1690045 23138099 := bstep (se 1 (by rfl) ⟨17353574, by rfl⟩ : syracuseStep 23138099 = 34707149) B34707149
theorem B2535227 : Blo 1690045 2535227 := bstep (se 1 (by rfl) ⟨1901420, by rfl⟩ : syracuseStep 2535227 = 3802841) B3802841
theorem B5705531 : Blo 1690045 5705531 := bstep (se 1 (by rfl) ⟨4279148, by rfl⟩ : syracuseStep 5705531 = 8558297) B8558297
theorem B1691451 : Blo 1690045 1691451 := bstep (se 1 (by rfl) ⟨1268588, by rfl⟩ : syracuseStep 1691451 = 2537177) B2537177
theorem B2535287 : Blo 1690045 2535287 := bstep (se 1 (by rfl) ⟨1901465, by rfl⟩ : syracuseStep 2535287 = 3802931) B3802931
theorem B1691527 : Blo 1690045 1691527 := bstep (se 1 (by rfl) ⟨1268645, by rfl⟩ : syracuseStep 1691527 = 2537291) B2537291
theorem B2535311 : Blo 1690045 2535311 := bstep (se 1 (by rfl) ⟨1901483, by rfl⟩ : syracuseStep 2535311 = 3802967) B3802967
theorem B1806223 : Blo 1690045 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B1691535 : Blo 1690045 1691535 := bstep (se 1 (by rfl) ⟨1268651, by rfl⟩ : syracuseStep 1691535 = 2537303) B2537303
theorem B4632473 : Blo 1690045 4632473 := bstep (se 2 (by rfl) ⟨1737177, by rfl⟩ : syracuseStep 4632473 = 3474355) B3474355
theorem B2535353 : Blo 1690045 2535353 := bstep (se 2 (by rfl) ⟨950757, by rfl⟩ : syracuseStep 2535353 = 1901515) B1901515
theorem B2535431 : Blo 1690045 2535431 := bstep (se 1 (by rfl) ⟨1901573, by rfl⟩ : syracuseStep 2535431 = 3803147) B3803147
theorem B3805199 : Blo 1690045 3805199 := bstep (se 1 (by rfl) ⟨2853899, by rfl⟩ : syracuseStep 3805199 = 5707799) B5707799
theorem B9629725 : Blo 1690045 9629725 := bstep (se 3 (by rfl) ⟨1805573, by rfl⟩ : syracuseStep 9629725 = 3611147) B3611147
theorem B5140513 : Blo 1690045 5140513 := bstep (se 2 (by rfl) ⟨1927692, by rfl⟩ : syracuseStep 5140513 = 3855385) B3855385
theorem B3805217 : Blo 1690045 3805217 := bstep (se 2 (by rfl) ⟨1426956, by rfl⟩ : syracuseStep 3805217 = 2853913) B2853913
theorem B2535467 : Blo 1690045 2535467 := bstep (se 1 (by rfl) ⟨1901600, by rfl⟩ : syracuseStep 2535467 = 3803201) B3803201
theorem B2535497 : Blo 1690045 2535497 := bstep (se 2 (by rfl) ⟨950811, by rfl⟩ : syracuseStep 2535497 = 1901623) B1901623
theorem B4280435 : Blo 1690045 4280435 := bstep (se 1 (by rfl) ⟨3210326, by rfl⟩ : syracuseStep 4280435 = 6420653) B6420653
theorem B2535611 : Blo 1690045 2535611 := bstep (se 1 (by rfl) ⟨1901708, by rfl⟩ : syracuseStep 2535611 = 3803417) B3803417
theorem B2535671 : Blo 1690045 2535671 := bstep (se 1 (by rfl) ⟨1901753, by rfl⟩ : syracuseStep 2535671 = 3803507) B3803507
theorem B2535695 : Blo 1690045 2535695 := bstep (se 1 (by rfl) ⟨1901771, by rfl⟩ : syracuseStep 2535695 = 3803543) B3803543
theorem B5706017 : Blo 1690045 5706017 := bstep (se 2 (by rfl) ⟨2139756, by rfl⟩ : syracuseStep 5706017 = 4279513) B4279513
theorem B2535737 : Blo 1690045 2535737 := bstep (se 2 (by rfl) ⟨950901, by rfl⟩ : syracuseStep 2535737 = 1901803) B1901803
theorem B9040187 : Blo 1690045 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B3805559 : Blo 1690045 3805559 := bstep (se 1 (by rfl) ⟨2854169, by rfl⟩ : syracuseStep 3805559 = 5708339) B5708339
theorem B2535815 : Blo 1690045 2535815 := bstep (se 1 (by rfl) ⟨1901861, by rfl⟩ : syracuseStep 2535815 = 3803723) B3803723
theorem B3428743 : Blo 1690045 3428743 := bstep (se 1 (by rfl) ⟨2571557, by rfl⟩ : syracuseStep 3428743 = 5143115) B5143115
theorem B2535851 : Blo 1690045 2535851 := bstep (se 1 (by rfl) ⟨1901888, by rfl⟩ : syracuseStep 2535851 = 3803777) B3803777
theorem B2707913 : Blo 1690045 2707913 := bstep (se 2 (by rfl) ⟨1015467, by rfl⟩ : syracuseStep 2707913 = 2030935) B2030935
theorem B2535881 : Blo 1690045 2535881 := bstep (se 2 (by rfl) ⟨950955, by rfl⟩ : syracuseStep 2535881 = 1901911) B1901911
theorem B6091217 : Blo 1690045 6091217 := bstep (se 2 (by rfl) ⟨2284206, by rfl⟩ : syracuseStep 6091217 = 4568413) B4568413
theorem B6951377 : Blo 1690045 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B20574749 : Blo 1690045 20574749 := bstep (se 3 (by rfl) ⟨3857765, by rfl⟩ : syracuseStep 20574749 = 7715531) B7715531
theorem B9630251 : Blo 1690045 9630251 := bstep (se 1 (by rfl) ⟨7222688, by rfl⟩ : syracuseStep 9630251 = 14445377) B14445377
theorem B3805739 : Blo 1690045 3805739 := bstep (se 1 (by rfl) ⟨2854304, by rfl⟩ : syracuseStep 3805739 = 5708609) B5708609
theorem B2535995 : Blo 1690045 2535995 := bstep (se 1 (by rfl) ⟨1901996, by rfl⟩ : syracuseStep 2535995 = 3803993) B3803993
theorem B2536055 : Blo 1690045 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B4280951 : Blo 1690045 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B2536079 : Blo 1690045 2536079 := bstep (se 1 (by rfl) ⟨1902059, by rfl⟩ : syracuseStep 2536079 = 3804119) B3804119
theorem B2536121 : Blo 1690045 2536121 := bstep (se 2 (by rfl) ⟨951045, by rfl⟩ : syracuseStep 2536121 = 1902091) B1902091
theorem B2536199 : Blo 1690045 2536199 := bstep (se 1 (by rfl) ⟨1902149, by rfl⟩ : syracuseStep 2536199 = 3804299) B3804299
theorem B11571983 : Blo 1690045 11571983 := bstep (se 1 (by rfl) ⟨8678987, by rfl⟩ : syracuseStep 11571983 = 17357975) B17357975
theorem B2536235 : Blo 1690045 2536235 := bstep (se 1 (by rfl) ⟨1902176, by rfl⟩ : syracuseStep 2536235 = 3804353) B3804353
theorem B2536265 : Blo 1690045 2536265 := bstep (se 2 (by rfl) ⟨951099, by rfl⟩ : syracuseStep 2536265 = 1902199) B1902199
theorem B5706611 : Blo 1690045 5706611 := bstep (se 1 (by rfl) ⟨4279958, by rfl⟩ : syracuseStep 5706611 = 8559917) B8559917
theorem B125039537 : Blo 1690045 125039537 := bstep (se 2 (by rfl) ⟨46889826, by rfl⟩ : syracuseStep 125039537 = 93779653) B93779653
theorem B5641145 : Blo 1690045 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B2536379 : Blo 1690045 2536379 := bstep (se 1 (by rfl) ⟨1902284, by rfl⟩ : syracuseStep 2536379 = 3804569) B3804569
theorem B4813769 : Blo 1690045 4813769 := bstep (se 2 (by rfl) ⟨1805163, by rfl⟩ : syracuseStep 4813769 = 3610327) B3610327
theorem B2708425 : Blo 1690045 2708425 := bstep (se 2 (by rfl) ⟨1015659, by rfl⟩ : syracuseStep 2708425 = 2031319) B2031319
theorem B2536439 : Blo 1690045 2536439 := bstep (se 1 (by rfl) ⟨1902329, by rfl⟩ : syracuseStep 2536439 = 3804659) B3804659
theorem B2536463 : Blo 1690045 2536463 := bstep (se 1 (by rfl) ⟨1902347, by rfl⟩ : syracuseStep 2536463 = 3804695) B3804695
theorem B2536505 : Blo 1690045 2536505 := bstep (se 2 (by rfl) ⟨951189, by rfl⟩ : syracuseStep 2536505 = 1902379) B1902379
theorem B2536583 : Blo 1690045 2536583 := bstep (se 1 (by rfl) ⟨1902437, by rfl⟩ : syracuseStep 2536583 = 3804875) B3804875
theorem B2536619 : Blo 1690045 2536619 := bstep (se 1 (by rfl) ⟨1902464, by rfl⟩ : syracuseStep 2536619 = 3804929) B3804929
theorem B2536649 : Blo 1690045 2536649 := bstep (se 2 (by rfl) ⟨951243, by rfl⟩ : syracuseStep 2536649 = 1902487) B1902487
theorem B4879631 : Blo 1690045 4879631 := bstep (se 1 (by rfl) ⟨3659723, by rfl⟩ : syracuseStep 4879631 = 7319447) B7319447
theorem B3208481 : Blo 1690045 3208481 := bstep (se 2 (by rfl) ⟨1203180, by rfl⟩ : syracuseStep 3208481 = 2406361) B2406361
theorem B2536763 : Blo 1690045 2536763 := bstep (se 1 (by rfl) ⟨1902572, by rfl⟩ : syracuseStep 2536763 = 3805145) B3805145
theorem B2536823 : Blo 1690045 2536823 := bstep (se 1 (by rfl) ⟨1902617, by rfl⟩ : syracuseStep 2536823 = 3805235) B3805235
theorem B32486791 : Blo 1690045 32486791 := bstep (se 1 (by rfl) ⟨24365093, by rfl⟩ : syracuseStep 32486791 = 48730187) B48730187
theorem B2536847 : Blo 1690045 2536847 := bstep (se 1 (by rfl) ⟨1902635, by rfl⟩ : syracuseStep 2536847 = 3805271) B3805271
theorem B3610003 : Blo 1690045 3610003 := bstep (se 1 (by rfl) ⟨2707502, by rfl⟩ : syracuseStep 3610003 = 5415005) B5415005
theorem B6092185 : Blo 1690045 6092185 := bstep (se 2 (by rfl) ⟨2284569, by rfl⟩ : syracuseStep 6092185 = 4569139) B4569139
theorem B2536889 : Blo 1690045 2536889 := bstep (se 2 (by rfl) ⟨951333, by rfl⟩ : syracuseStep 2536889 = 1902667) B1902667
theorem B8123851 : Blo 1690045 8123851 := bstep (se 1 (by rfl) ⟨6092888, by rfl⟩ : syracuseStep 8123851 = 12185777) B12185777
theorem B21657041 : Blo 1690045 21657041 := bstep (se 2 (by rfl) ⟨8121390, by rfl⟩ : syracuseStep 21657041 = 16242781) B16242781
theorem B2536967 : Blo 1690045 2536967 := bstep (se 1 (by rfl) ⟨1902725, by rfl⟩ : syracuseStep 2536967 = 3805451) B3805451
theorem B3208747 : Blo 1690045 3208747 := bstep (se 1 (by rfl) ⟨2406560, by rfl⟩ : syracuseStep 3208747 = 4813121) B4813121
theorem B2537003 : Blo 1690045 2537003 := bstep (se 1 (by rfl) ⟨1902752, by rfl⟩ : syracuseStep 2537003 = 3805505) B3805505
theorem B2537033 : Blo 1690045 2537033 := bstep (se 2 (by rfl) ⟨951387, by rfl⟩ : syracuseStep 2537033 = 1902775) B1902775
theorem B3610259 : Blo 1690045 3610259 := bstep (se 1 (by rfl) ⟨2707694, by rfl⟩ : syracuseStep 3610259 = 5415389) B5415389
theorem B2537147 : Blo 1690045 2537147 := bstep (se 1 (by rfl) ⟨1902860, by rfl⟩ : syracuseStep 2537147 = 3805721) B3805721
theorem B2537207 : Blo 1690045 2537207 := bstep (se 1 (by rfl) ⟨1902905, by rfl⟩ : syracuseStep 2537207 = 3805811) B3805811
theorem B2537231 : Blo 1690045 2537231 := bstep (se 1 (by rfl) ⟨1902923, by rfl⟩ : syracuseStep 2537231 = 3805847) B3805847
theorem B6346529 : Blo 1690045 6346529 := bstep (se 2 (by rfl) ⟨2379948, by rfl⟩ : syracuseStep 6346529 = 4759897) B4759897
theorem B4814635 : Blo 1690045 4814635 := bstep (se 1 (by rfl) ⟨3610976, by rfl⟩ : syracuseStep 4814635 = 7221953) B7221953
theorem B2537273 : Blo 1690045 2537273 := bstep (se 2 (by rfl) ⟨951477, by rfl⟩ : syracuseStep 2537273 = 1902955) B1902955
theorem B6092603 : Blo 1690045 6092603 := bstep (se 1 (by rfl) ⟨4569452, by rfl⟩ : syracuseStep 6092603 = 9138905) B9138905
theorem B10835801 : Blo 1690045 10835801 := bstep (se 2 (by rfl) ⟨4063425, by rfl⟩ : syracuseStep 10835801 = 8126851) B8126851
theorem B8124295 : Blo 1690045 8124295 := bstep (se 1 (by rfl) ⟨6093221, by rfl⟩ : syracuseStep 8124295 = 12186443) B12186443
theorem B8124313 : Blo 1690045 8124313 := bstep (se 2 (by rfl) ⟨3046617, by rfl⟩ : syracuseStep 8124313 = 6093235) B6093235
theorem B16250777 : Blo 1690045 16250777 := bstep (se 2 (by rfl) ⟨6094041, by rfl⟩ : syracuseStep 16250777 = 12188083) B12188083
theorem B9631709 : Blo 1690045 9631709 := bstep (se 3 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 9631709 = 3611891) B3611891
theorem B8558621 : Blo 1690045 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B4814909 : Blo 1690045 4814909 := bstep (se 3 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 4814909 = 1805591) B1805591
theorem B8673587 : Blo 1690045 8673587 := bstep (se 1 (by rfl) ⟨6505190, by rfl⟩ : syracuseStep 8673587 = 13010381) B13010381
theorem B16243091 : Blo 1690045 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B4815251 : Blo 1690045 4815251 := bstep (se 1 (by rfl) ⟨3611438, by rfl⟩ : syracuseStep 4815251 = 7222877) B7222877
theorem B8559107 : Blo 1690045 8559107 := bstep (se 1 (by rfl) ⟨6419330, by rfl⟩ : syracuseStep 8559107 = 12838661) B12838661
theorem B14441003 : Blo 1690045 14441003 := bstep (se 1 (by rfl) ⟨10830752, by rfl⟩ : syracuseStep 14441003 = 21661505) B21661505
theorem B3209863 : Blo 1690045 3209863 := bstep (se 1 (by rfl) ⟨2407397, by rfl⟩ : syracuseStep 3209863 = 4814795) B4814795
theorem B2316971 : Blo 1690045 2316971 := bstep (se 1 (by rfl) ⟨1737728, by rfl⟩ : syracuseStep 2316971 = 3475457) B3475457
theorem B6421457 : Blo 1690045 6421457 := bstep (se 2 (by rfl) ⟨2408046, by rfl⟩ : syracuseStep 6421457 = 4816093) B4816093
theorem B10279979 : Blo 1690045 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B14449751 : Blo 1690045 14449751 := bstep (se 1 (by rfl) ⟨10837313, by rfl⟩ : syracuseStep 14449751 = 21674627) B21674627
theorem B2890937 : Blo 1690045 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B3210425 : Blo 1690045 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B8125697 : Blo 1690045 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B6855995 : Blo 1690045 6855995 := bstep (se 1 (by rfl) ⟨5141996, by rfl⟩ : syracuseStep 6855995 = 10283993) B10283993
theorem B12836231 : Blo 1690045 12836231 := bstep (se 1 (by rfl) ⟨9627173, by rfl⟩ : syracuseStep 12836231 = 19254347) B19254347
theorem B16924049 : Blo 1690045 16924049 := bstep (se 2 (by rfl) ⟨6346518, by rfl⟩ : syracuseStep 16924049 = 12693037) B12693037
theorem B6421913 : Blo 1690045 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B2441017 : Blo 1690045 2441017 := bstep (se 2 (by rfl) ⟨915381, by rfl⟩ : syracuseStep 2441017 = 1830763) B1830763
theorem B3612617 : Blo 1690045 3612617 := bstep (se 2 (by rfl) ⟨1354731, by rfl⟩ : syracuseStep 3612617 = 2709463) B2709463
theorem B48767093 : Blo 1690045 48767093 := bstep (se 5 (by rfl) ⟨2285957, by rfl⟩ : syracuseStep 48767093 = 4571915) B4571915
theorem B18284723 : Blo 1690045 18284723 := bstep (se 1 (by rfl) ⟨13713542, by rfl⟩ : syracuseStep 18284723 = 27427085) B27427085
theorem B7709165 : Blo 1690045 7709165 := bstep (se 3 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 7709165 = 2890937) B2890937
theorem B4571657 : Blo 1690045 4571657 := bstep (se 2 (by rfl) ⟨1714371, by rfl⟩ : syracuseStep 4571657 = 3428743) B3428743
theorem B3760763 : Blo 1690045 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B1901407 : Blo 1690045 1901407 := bstep (se 1 (by rfl) ⟨1426055, by rfl⟩ : syracuseStep 1901407 = 2852111) B2852111
theorem B3253087 : Blo 1690045 3253087 := bstep (se 1 (by rfl) ⟨2439815, by rfl⟩ : syracuseStep 3253087 = 4879631) B4879631
theorem B2138987 : Blo 1690045 2138987 := bstep (se 1 (by rfl) ⟨1604240, by rfl⟩ : syracuseStep 2138987 = 3208481) B3208481
theorem B1901767 : Blo 1690045 1901767 := bstep (se 1 (by rfl) ⟨1426325, by rfl⟩ : syracuseStep 1901767 = 2852651) B2852651
theorem B12518671 : Blo 1690045 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B2852239 : Blo 1690045 2852239 := bstep (se 1 (by rfl) ⟨2139179, by rfl⟩ : syracuseStep 2852239 = 4278359) B4278359
theorem B5211611 : Blo 1690045 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B3802823 : Blo 1690045 3802823 := bstep (se 1 (by rfl) ⟨2852117, by rfl⟩ : syracuseStep 3802823 = 5704235) B5704235
theorem B9627335 : Blo 1690045 9627335 := bstep (se 1 (by rfl) ⟨7220501, by rfl⟩ : syracuseStep 9627335 = 14441003) B14441003
theorem B12191431 : Blo 1690045 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B6178589 : Blo 1690045 6178589 := bstep (se 3 (by rfl) ⟨1158485, by rfl⟩ : syracuseStep 6178589 = 2316971) B2316971
theorem B10831801 : Blo 1690045 10831801 := bstep (se 2 (by rfl) ⟨4061925, by rfl⟩ : syracuseStep 10831801 = 8123851) B8123851
theorem B1902631 : Blo 1690045 1902631 := bstep (se 1 (by rfl) ⟨1426973, by rfl⟩ : syracuseStep 1902631 = 2853947) B2853947
theorem B4278329 : Blo 1690045 4278329 := bstep (se 2 (by rfl) ⟨1604373, by rfl⟩ : syracuseStep 4278329 = 3208747) B3208747
theorem B2852921 : Blo 1690045 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B2140283 : Blo 1690045 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B5417131 : Blo 1690045 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B11282699 : Blo 1690045 11282699 := bstep (se 1 (by rfl) ⟨8462024, by rfl⟩ : syracuseStep 11282699 = 16924049) B16924049
theorem B3254689 : Blo 1690045 3254689 := bstep (se 2 (by rfl) ⟨1220508, by rfl⟩ : syracuseStep 3254689 = 2441017) B2441017
theorem B1690055 : Blo 1690045 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B1690075 : Blo 1690045 1690075 := bstep (se 1 (by rfl) ⟨1267556, by rfl⟩ : syracuseStep 1690075 = 2535113) B2535113
theorem B10832393 : Blo 1690045 10832393 := bstep (se 2 (by rfl) ⟨4062147, by rfl⟩ : syracuseStep 10832393 = 8124295) B8124295
theorem B10832417 : Blo 1690045 10832417 := bstep (se 2 (by rfl) ⟨4062156, by rfl⟩ : syracuseStep 10832417 = 8124313) B8124313
theorem B1690151 : Blo 1690045 1690151 := bstep (se 1 (by rfl) ⟨1267613, by rfl⟩ : syracuseStep 1690151 = 2535227) B2535227
theorem B3803687 : Blo 1690045 3803687 := bstep (se 1 (by rfl) ⟨2852765, by rfl⟩ : syracuseStep 3803687 = 5705531) B5705531
theorem B1690191 : Blo 1690045 1690191 := bstep (se 1 (by rfl) ⟨1267643, by rfl⟩ : syracuseStep 1690191 = 2535287) B2535287
theorem B1690207 : Blo 1690045 1690207 := bstep (se 1 (by rfl) ⟨1267655, by rfl⟩ : syracuseStep 1690207 = 2535311) B2535311
theorem B5704289 : Blo 1690045 5704289 := bstep (se 2 (by rfl) ⟨2139108, by rfl⟩ : syracuseStep 5704289 = 4278217) B4278217
theorem B1690235 : Blo 1690045 1690235 := bstep (se 1 (by rfl) ⟨1267676, by rfl⟩ : syracuseStep 1690235 = 2535353) B2535353
theorem B1690287 : Blo 1690045 1690287 := bstep (se 1 (by rfl) ⟨1267715, by rfl⟩ : syracuseStep 1690287 = 2535431) B2535431
theorem B1690311 : Blo 1690045 1690311 := bstep (se 1 (by rfl) ⟨1267733, by rfl⟩ : syracuseStep 1690311 = 2535467) B2535467
theorem B12839633 : Blo 1690045 12839633 := bstep (se 2 (by rfl) ⟨4814862, by rfl⟩ : syracuseStep 12839633 = 9629725) B9629725
theorem B1690331 : Blo 1690045 1690331 := bstep (se 1 (by rfl) ⟨1267748, by rfl⟩ : syracuseStep 1690331 = 2535497) B2535497
theorem B2853623 : Blo 1690045 2853623 := bstep (se 1 (by rfl) ⟨2140217, by rfl⟩ : syracuseStep 2853623 = 4280435) B4280435
theorem B1690407 : Blo 1690045 1690407 := bstep (se 1 (by rfl) ⟨1267805, by rfl⟩ : syracuseStep 1690407 = 2535611) B2535611
theorem B1690447 : Blo 1690045 1690447 := bstep (se 1 (by rfl) ⟨1267835, by rfl⟩ : syracuseStep 1690447 = 2535671) B2535671
theorem B1690463 : Blo 1690045 1690463 := bstep (se 1 (by rfl) ⟨1267847, by rfl⟩ : syracuseStep 1690463 = 2535695) B2535695
theorem B3804011 : Blo 1690045 3804011 := bstep (se 1 (by rfl) ⟨2853008, by rfl⟩ : syracuseStep 3804011 = 5706017) B5706017
theorem B1690491 : Blo 1690045 1690491 := bstep (se 1 (by rfl) ⟨1267868, by rfl⟩ : syracuseStep 1690491 = 2535737) B2535737
theorem B3804065 : Blo 1690045 3804065 := bstep (se 2 (by rfl) ⟨1426524, by rfl⟩ : syracuseStep 3804065 = 2853049) B2853049
theorem B1690543 : Blo 1690045 1690543 := bstep (se 1 (by rfl) ⟨1267907, by rfl⟩ : syracuseStep 1690543 = 2535815) B2535815
theorem B1690567 : Blo 1690045 1690567 := bstep (se 1 (by rfl) ⟨1267925, by rfl⟩ : syracuseStep 1690567 = 2535851) B2535851
theorem B1805275 : Blo 1690045 1805275 := bstep (se 1 (by rfl) ⟨1353956, by rfl⟩ : syracuseStep 1805275 = 2707913) B2707913
theorem B1690587 : Blo 1690045 1690587 := bstep (se 1 (by rfl) ⟨1267940, by rfl⟩ : syracuseStep 1690587 = 2535881) B2535881
theorem B13716499 : Blo 1690045 13716499 := bstep (se 1 (by rfl) ⟨10287374, by rfl⟩ : syracuseStep 13716499 = 20574749) B20574749
theorem B1690663 : Blo 1690045 1690663 := bstep (se 1 (by rfl) ⟨1267997, by rfl⟩ : syracuseStep 1690663 = 2535995) B2535995
theorem B1690703 : Blo 1690045 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B2853967 : Blo 1690045 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B1690719 : Blo 1690045 1690719 := bstep (se 1 (by rfl) ⟨1268039, by rfl⟩ : syracuseStep 1690719 = 2536079) B2536079
theorem B1690747 : Blo 1690045 1690747 := bstep (se 1 (by rfl) ⟨1268060, by rfl⟩ : syracuseStep 1690747 = 2536121) B2536121
theorem B1690799 : Blo 1690045 1690799 := bstep (se 1 (by rfl) ⟨1268099, by rfl⟩ : syracuseStep 1690799 = 2536199) B2536199
theorem B1690823 : Blo 1690045 1690823 := bstep (se 1 (by rfl) ⟨1268117, by rfl⟩ : syracuseStep 1690823 = 2536235) B2536235
theorem B8236235 : Blo 1690045 8236235 := bstep (se 1 (by rfl) ⟨6177176, by rfl⟩ : syracuseStep 8236235 = 12354353) B12354353
theorem B1690843 : Blo 1690045 1690843 := bstep (se 1 (by rfl) ⟨1268132, by rfl⟩ : syracuseStep 1690843 = 2536265) B2536265
theorem B3804407 : Blo 1690045 3804407 := bstep (se 1 (by rfl) ⟨2853305, by rfl⟩ : syracuseStep 3804407 = 5706611) B5706611
theorem B1690919 : Blo 1690045 1690919 := bstep (se 1 (by rfl) ⟨1268189, by rfl⟩ : syracuseStep 1690919 = 2536379) B2536379
theorem B2854217 : Blo 1690045 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B1690959 : Blo 1690045 1690959 := bstep (se 1 (by rfl) ⟨1268219, by rfl⟩ : syracuseStep 1690959 = 2536439) B2536439
theorem B6417751 : Blo 1690045 6417751 := bstep (se 1 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 6417751 = 9626627) B9626627
theorem B1690975 : Blo 1690045 1690975 := bstep (se 1 (by rfl) ⟨1268231, by rfl⟩ : syracuseStep 1690975 = 2536463) B2536463
theorem B1691003 : Blo 1690045 1691003 := bstep (se 1 (by rfl) ⟨1268252, by rfl⟩ : syracuseStep 1691003 = 2536505) B2536505
theorem B1691055 : Blo 1690045 1691055 := bstep (se 1 (by rfl) ⟨1268291, by rfl⟩ : syracuseStep 1691055 = 2536583) B2536583
theorem B3173807 : Blo 1690045 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B1691079 : Blo 1690045 1691079 := bstep (se 1 (by rfl) ⟨1268309, by rfl⟩ : syracuseStep 1691079 = 2536619) B2536619
theorem B1691099 : Blo 1690045 1691099 := bstep (se 1 (by rfl) ⟨1268324, by rfl⟩ : syracuseStep 1691099 = 2536649) B2536649
theorem B4279817 : Blo 1690045 4279817 := bstep (se 2 (by rfl) ⟨1604931, by rfl⟩ : syracuseStep 4279817 = 3209863) B3209863
theorem B1691175 : Blo 1690045 1691175 := bstep (se 1 (by rfl) ⟨1268381, by rfl⟩ : syracuseStep 1691175 = 2536763) B2536763
theorem B1691215 : Blo 1690045 1691215 := bstep (se 1 (by rfl) ⟨1268411, by rfl⟩ : syracuseStep 1691215 = 2536823) B2536823
theorem B1691231 : Blo 1690045 1691231 := bstep (se 1 (by rfl) ⟨1268423, by rfl⟩ : syracuseStep 1691231 = 2536847) B2536847
theorem B1691259 : Blo 1690045 1691259 := bstep (se 1 (by rfl) ⟨1268444, by rfl⟩ : syracuseStep 1691259 = 2536889) B2536889
theorem B6418055 : Blo 1690045 6418055 := bstep (se 1 (by rfl) ⟨4813541, by rfl⟩ : syracuseStep 6418055 = 9627083) B9627083
theorem B14438027 : Blo 1690045 14438027 := bstep (se 1 (by rfl) ⟨10828520, by rfl⟩ : syracuseStep 14438027 = 21657041) B21657041
theorem B1691311 : Blo 1690045 1691311 := bstep (se 1 (by rfl) ⟨1268483, by rfl⟩ : syracuseStep 1691311 = 2536967) B2536967
theorem B1691335 : Blo 1690045 1691335 := bstep (se 1 (by rfl) ⟨1268501, by rfl⟩ : syracuseStep 1691335 = 2537003) B2537003
theorem B1691355 : Blo 1690045 1691355 := bstep (se 1 (by rfl) ⟨1268516, by rfl⟩ : syracuseStep 1691355 = 2537033) B2537033
theorem B2535161 : Blo 1690045 2535161 := bstep (se 2 (by rfl) ⟨950685, by rfl⟩ : syracuseStep 2535161 = 1901371) B1901371
theorem B1691431 : Blo 1690045 1691431 := bstep (se 1 (by rfl) ⟨1268573, by rfl⟩ : syracuseStep 1691431 = 2537147) B2537147
theorem B3805001 : Blo 1690045 3805001 := bstep (se 2 (by rfl) ⟨1426875, by rfl⟩ : syracuseStep 3805001 = 2853751) B2853751
theorem B1691471 : Blo 1690045 1691471 := bstep (se 1 (by rfl) ⟨1268603, by rfl⟩ : syracuseStep 1691471 = 2537207) B2537207
theorem B2535263 : Blo 1690045 2535263 := bstep (se 1 (by rfl) ⟨1901447, by rfl⟩ : syracuseStep 2535263 = 3802895) B3802895
theorem B1691487 : Blo 1690045 1691487 := bstep (se 1 (by rfl) ⟨1268615, by rfl⟩ : syracuseStep 1691487 = 2537231) B2537231
theorem B2535275 : Blo 1690045 2535275 := bstep (se 1 (by rfl) ⟨1901456, by rfl⟩ : syracuseStep 2535275 = 3802913) B3802913
theorem B4231019 : Blo 1690045 4231019 := bstep (se 1 (by rfl) ⟨3173264, by rfl⟩ : syracuseStep 4231019 = 6346529) B6346529
theorem B1691515 : Blo 1690045 1691515 := bstep (se 1 (by rfl) ⟨1268636, by rfl⟩ : syracuseStep 1691515 = 2537273) B2537273
theorem B10833851 : Blo 1690045 10833851 := bstep (se 1 (by rfl) ⟨8125388, by rfl⟩ : syracuseStep 10833851 = 16250777) B16250777
theorem B5705747 : Blo 1690045 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B2535503 : Blo 1690045 2535503 := bstep (se 1 (by rfl) ⟨1901627, by rfl⟩ : syracuseStep 2535503 = 3803255) B3803255
theorem B6418511 : Blo 1690045 6418511 := bstep (se 1 (by rfl) ⟨4813883, by rfl⟩ : syracuseStep 6418511 = 9627767) B9627767
theorem B2535623 : Blo 1690045 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B5706071 : Blo 1690045 5706071 := bstep (se 1 (by rfl) ⟨4279553, by rfl⟩ : syracuseStep 5706071 = 8559107) B8559107
theorem B2535785 : Blo 1690045 2535785 := bstep (se 2 (by rfl) ⟨950919, by rfl⟩ : syracuseStep 2535785 = 1901839) B1901839
theorem B2535863 : Blo 1690045 2535863 := bstep (se 1 (by rfl) ⟨1901897, by rfl⟩ : syracuseStep 2535863 = 3803795) B3803795
theorem B2535899 : Blo 1690045 2535899 := bstep (se 1 (by rfl) ⟨1901924, by rfl⟩ : syracuseStep 2535899 = 3803849) B3803849
theorem B43315721 : Blo 1690045 43315721 := bstep (se 2 (by rfl) ⟨16243395, by rfl⟩ : syracuseStep 43315721 = 32486791) B32486791
theorem B4813337 : Blo 1690045 4813337 := bstep (se 2 (by rfl) ⟨1805001, by rfl⟩ : syracuseStep 4813337 = 3610003) B3610003
theorem B8122913 : Blo 1690045 8122913 := bstep (se 2 (by rfl) ⟨3046092, by rfl⟩ : syracuseStep 8122913 = 6092185) B6092185
theorem B3805793 : Blo 1690045 3805793 := bstep (se 2 (by rfl) ⟨1427172, by rfl⟩ : syracuseStep 3805793 = 2854345) B2854345
theorem B4813451 : Blo 1690045 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B4280971 : Blo 1690045 4280971 := bstep (se 1 (by rfl) ⟨3210728, by rfl⟩ : syracuseStep 4280971 = 6421457) B6421457
theorem B6853319 : Blo 1690045 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B8557487 : Blo 1690045 8557487 := bstep (se 1 (by rfl) ⟨6418115, by rfl⟩ : syracuseStep 8557487 = 12836231) B12836231
theorem B2536367 : Blo 1690045 2536367 := bstep (se 1 (by rfl) ⟨1902275, by rfl⟩ : syracuseStep 2536367 = 3804551) B3804551
theorem B4281275 : Blo 1690045 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B39040001 : Blo 1690045 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B2536457 : Blo 1690045 2536457 := bstep (se 2 (by rfl) ⟨951171, by rfl⟩ : syracuseStep 2536457 = 1902343) B1902343
theorem B2536487 : Blo 1690045 2536487 := bstep (se 1 (by rfl) ⟨1902365, by rfl⟩ : syracuseStep 2536487 = 3804731) B3804731
theorem B6419513 : Blo 1690045 6419513 := bstep (se 2 (by rfl) ⟨2407317, by rfl⟩ : syracuseStep 6419513 = 4814635) B4814635
theorem B12842063 : Blo 1690045 12842063 := bstep (se 1 (by rfl) ⟨9631547, by rfl⟩ : syracuseStep 12842063 = 19263095) B19263095
theorem B2536571 : Blo 1690045 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B2536697 : Blo 1690045 2536697 := bstep (se 2 (by rfl) ⟨951261, by rfl⟩ : syracuseStep 2536697 = 1902523) B1902523
theorem B2536799 : Blo 1690045 2536799 := bstep (se 1 (by rfl) ⟨1902599, by rfl⟩ : syracuseStep 2536799 = 3805199) B3805199
theorem B2536811 : Blo 1690045 2536811 := bstep (se 1 (by rfl) ⟨1902608, by rfl⟩ : syracuseStep 2536811 = 3805217) B3805217
theorem B6854017 : Blo 1690045 6854017 := bstep (se 2 (by rfl) ⟨2570256, by rfl⟩ : syracuseStep 6854017 = 5140513) B5140513
theorem B5707151 : Blo 1690045 5707151 := bstep (se 1 (by rfl) ⟨4280363, by rfl⟩ : syracuseStep 5707151 = 8560727) B8560727
theorem B12694985 : Blo 1690045 12694985 := bstep (se 2 (by rfl) ⟨4760619, by rfl⟩ : syracuseStep 12694985 = 9521239) B9521239
theorem B2537039 : Blo 1690045 2537039 := bstep (se 1 (by rfl) ⟨1902779, by rfl⟩ : syracuseStep 2537039 = 3805559) B3805559
theorem B4060811 : Blo 1690045 4060811 := bstep (se 1 (by rfl) ⟨3045608, by rfl⟩ : syracuseStep 4060811 = 6091217) B6091217
theorem B6420167 : Blo 1690045 6420167 := bstep (se 1 (by rfl) ⟨4815125, by rfl⟩ : syracuseStep 6420167 = 9630251) B9630251
theorem B2537159 : Blo 1690045 2537159 := bstep (se 1 (by rfl) ⟨1902869, by rfl⟩ : syracuseStep 2537159 = 3805739) B3805739
theorem B5707475 : Blo 1690045 5707475 := bstep (se 1 (by rfl) ⟨4280606, by rfl⟩ : syracuseStep 5707475 = 8561213) B8561213
theorem B7714655 : Blo 1690045 7714655 := bstep (se 1 (by rfl) ⟨5785991, by rfl⟩ : syracuseStep 7714655 = 11571983) B11571983
theorem B83359691 : Blo 1690045 83359691 := bstep (se 1 (by rfl) ⟨62519768, by rfl⟩ : syracuseStep 83359691 = 125039537) B125039537
theorem B3610703 : Blo 1690045 3610703 := bstep (se 1 (by rfl) ⟨2708027, by rfl⟩ : syracuseStep 3610703 = 5416055) B5416055
theorem B10983539 : Blo 1690045 10983539 := bstep (se 1 (by rfl) ⟨8237654, by rfl⟩ : syracuseStep 10983539 = 16475309) B16475309
theorem B24107165 : Blo 1690045 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B2406839 : Blo 1690045 2406839 := bstep (se 1 (by rfl) ⟨1805129, by rfl⟩ : syracuseStep 2406839 = 3610259) B3610259
theorem B4061735 : Blo 1690045 4061735 := bstep (se 1 (by rfl) ⟨3046301, by rfl⟩ : syracuseStep 4061735 = 6092603) B6092603
theorem B18537005 : Blo 1690045 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B7223867 : Blo 1690045 7223867 := bstep (se 1 (by rfl) ⟨5417900, by rfl⟩ : syracuseStep 7223867 = 10835801) B10835801
theorem B3611233 : Blo 1690045 3611233 := bstep (se 2 (by rfl) ⟨1354212, by rfl⟩ : syracuseStep 3611233 = 2708425) B2708425
theorem B6421139 : Blo 1690045 6421139 := bstep (se 1 (by rfl) ⟨4815854, by rfl⟩ : syracuseStep 6421139 = 9631709) B9631709
theorem B3209939 : Blo 1690045 3209939 := bstep (se 1 (by rfl) ⟨2407454, by rfl⟩ : syracuseStep 3209939 = 4814909) B4814909
theorem B8674121 : Blo 1690045 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B5782391 : Blo 1690045 5782391 := bstep (se 1 (by rfl) ⟨4336793, by rfl⟩ : syracuseStep 5782391 = 8673587) B8673587
theorem B5708663 : Blo 1690045 5708663 := bstep (se 1 (by rfl) ⟨4281497, by rfl⟩ : syracuseStep 5708663 = 8562995) B8562995
theorem B10828727 : Blo 1690045 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B3210167 : Blo 1690045 3210167 := bstep (se 1 (by rfl) ⟨2407625, by rfl⟩ : syracuseStep 3210167 = 4815251) B4815251
theorem B5708879 : Blo 1690045 5708879 := bstep (se 1 (by rfl) ⟨4281659, by rfl⟩ : syracuseStep 5708879 = 8563319) B8563319
theorem B4816253 : Blo 1690045 4816253 := bstep (se 3 (by rfl) ⟨903047, by rfl⟩ : syracuseStep 4816253 = 1806095) B1806095
theorem B9633167 : Blo 1690045 9633167 := bstep (se 1 (by rfl) ⟨7224875, by rfl⟩ : syracuseStep 9633167 = 14449751) B14449751
theorem B4570663 : Blo 1690045 4570663 := bstep (se 1 (by rfl) ⟨3427997, by rfl⟩ : syracuseStep 4570663 = 6855995) B6855995
theorem B4570813 : Blo 1690045 4570813 := bstep (se 3 (by rfl) ⟨857027, by rfl⟩ : syracuseStep 4570813 = 1714055) B1714055
theorem B12353261 : Blo 1690045 12353261 := bstep (se 3 (by rfl) ⟨2316236, by rfl⟩ : syracuseStep 12353261 = 4632473) B4632473
theorem B2408297 : Blo 1690045 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B12836717 : Blo 1690045 12836717 := bstep (se 3 (by rfl) ⟨2406884, by rfl⟩ : syracuseStep 12836717 = 4813769) B4813769
theorem B15425399 : Blo 1690045 15425399 := bstep (se 1 (by rfl) ⟨11569049, by rfl⟩ : syracuseStep 15425399 = 23138099) B23138099
theorem B2408411 : Blo 1690045 2408411 := bstep (se 1 (by rfl) ⟨1806308, by rfl⟩ : syracuseStep 2408411 = 3612617) B3612617
theorem B12189815 : Blo 1690045 12189815 := bstep (se 1 (by rfl) ⟨9142361, by rfl⟩ : syracuseStep 12189815 = 18284723) B18284723
theorem B28877147 : Blo 1690045 28877147 := bstep (se 1 (by rfl) ⟨21657860, by rfl⟩ : syracuseStep 28877147 = 43315721) B43315721
theorem B3047771 : Blo 1690045 3047771 := bstep (se 1 (by rfl) ⟨2285828, by rfl⟩ : syracuseStep 3047771 = 4571657) B4571657
theorem B5415275 : Blo 1690045 5415275 := bstep (se 1 (by rfl) ⟨4061456, by rfl⟩ : syracuseStep 5415275 = 8122913) B8122913
theorem B26026667 : Blo 1690045 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B8561375 : Blo 1690045 8561375 := bstep (se 1 (by rfl) ⟨6421031, by rfl⟩ : syracuseStep 8561375 = 12842063) B12842063
theorem B8463323 : Blo 1690045 8463323 := bstep (se 1 (by rfl) ⟨6347492, by rfl⟩ : syracuseStep 8463323 = 12694985) B12694985
theorem B3474407 : Blo 1690045 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B8463485 : Blo 1690045 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B2852219 : Blo 1690045 2852219 := bstep (se 1 (by rfl) ⟨2139164, by rfl⟩ : syracuseStep 2852219 = 4278329) B4278329
theorem B1901947 : Blo 1690045 1901947 := bstep (se 1 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 1901947 = 2852921) B2852921
theorem B10028701 : Blo 1690045 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B3802859 : Blo 1690045 3802859 := bstep (se 1 (by rfl) ⟨2852144, by rfl⟩ : syracuseStep 3802859 = 5704289) B5704289
theorem B2139959 : Blo 1690045 2139959 := bstep (se 1 (by rfl) ⟨1604969, by rfl⟩ : syracuseStep 2139959 = 3209939) B3209939
theorem B1902415 : Blo 1690045 1902415 := bstep (se 1 (by rfl) ⟨1426811, by rfl⟩ : syracuseStep 1902415 = 2853623) B2853623
theorem B3802985 : Blo 1690045 3802985 := bstep (se 2 (by rfl) ⟨1426119, by rfl⟩ : syracuseStep 3802985 = 2852239) B2852239
theorem B7219151 : Blo 1690045 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B2140111 : Blo 1690045 2140111 := bstep (se 1 (by rfl) ⟨1605083, by rfl⟩ : syracuseStep 2140111 = 3210167) B3210167
theorem B5490823 : Blo 1690045 5490823 := bstep (se 1 (by rfl) ⟨4118117, by rfl⟩ : syracuseStep 5490823 = 8236235) B8236235
theorem B1902811 : Blo 1690045 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B16255241 : Blo 1690045 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B5703965 : Blo 1690045 5703965 := bstep (se 3 (by rfl) ⟨1069493, by rfl⟩ : syracuseStep 5703965 = 2138987) B2138987
theorem B11282717 : Blo 1690045 11282717 := bstep (se 3 (by rfl) ⟨2115509, by rfl⟩ : syracuseStep 11282717 = 4231019) B4231019
theorem B2853211 : Blo 1690045 2853211 := bstep (se 1 (by rfl) ⟨2139908, by rfl⟩ : syracuseStep 2853211 = 4279817) B4279817
theorem B4278703 : Blo 1690045 4278703 := bstep (se 1 (by rfl) ⟨3209027, by rfl⟩ : syracuseStep 4278703 = 6418055) B6418055
theorem B1690107 : Blo 1690045 1690107 := bstep (se 1 (by rfl) ⟨1267580, by rfl⟩ : syracuseStep 1690107 = 2535161) B2535161
theorem B1690175 : Blo 1690045 1690175 := bstep (se 1 (by rfl) ⟨1267631, by rfl⟩ : syracuseStep 1690175 = 2535263) B2535263
theorem B1690183 : Blo 1690045 1690183 := bstep (se 1 (by rfl) ⟨1267637, by rfl⟩ : syracuseStep 1690183 = 2535275) B2535275
theorem B10283599 : Blo 1690045 10283599 := bstep (se 1 (by rfl) ⟨7712699, by rfl⟩ : syracuseStep 10283599 = 15425399) B15425399
theorem B3803831 : Blo 1690045 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B1690335 : Blo 1690045 1690335 := bstep (se 1 (by rfl) ⟨1267751, by rfl⟩ : syracuseStep 1690335 = 2535503) B2535503
theorem B4279007 : Blo 1690045 4279007 := bstep (se 1 (by rfl) ⟨3209255, by rfl⟩ : syracuseStep 4279007 = 6418511) B6418511
theorem B1690415 : Blo 1690045 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B9628541 : Blo 1690045 9628541 := bstep (se 3 (by rfl) ⟨1805351, by rfl⟩ : syracuseStep 9628541 = 3610703) B3610703
theorem B3804047 : Blo 1690045 3804047 := bstep (se 1 (by rfl) ⟨2853035, by rfl⟩ : syracuseStep 3804047 = 5706071) B5706071
theorem B1690523 : Blo 1690045 1690523 := bstep (se 1 (by rfl) ⟨1267892, by rfl⟩ : syracuseStep 1690523 = 2535785) B2535785
theorem B1690575 : Blo 1690045 1690575 := bstep (se 1 (by rfl) ⟨1267931, by rfl⟩ : syracuseStep 1690575 = 2535863) B2535863
theorem B1690599 : Blo 1690045 1690599 := bstep (se 1 (by rfl) ⟨1267949, by rfl⟩ : syracuseStep 1690599 = 2535899) B2535899
theorem B5139443 : Blo 1690045 5139443 := bstep (se 1 (by rfl) ⟨3854582, by rfl⟩ : syracuseStep 5139443 = 7709165) B7709165
theorem B5704991 : Blo 1690045 5704991 := bstep (se 1 (by rfl) ⟨4278743, by rfl⟩ : syracuseStep 5704991 = 8557487) B8557487
theorem B1690911 : Blo 1690045 1690911 := bstep (se 1 (by rfl) ⟨1268183, by rfl⟩ : syracuseStep 1690911 = 2536367) B2536367
theorem B2854183 : Blo 1690045 2854183 := bstep (se 1 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 2854183 = 4281275) B4281275
theorem B1690971 : Blo 1690045 1690971 := bstep (se 1 (by rfl) ⟨1268228, by rfl⟩ : syracuseStep 1690971 = 2536457) B2536457
theorem B1690991 : Blo 1690045 1690991 := bstep (se 1 (by rfl) ⟨1268243, by rfl⟩ : syracuseStep 1690991 = 2536487) B2536487
theorem B4279675 : Blo 1690045 4279675 := bstep (se 1 (by rfl) ⟨3209756, by rfl⟩ : syracuseStep 4279675 = 6419513) B6419513
theorem B1691047 : Blo 1690045 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B1691131 : Blo 1690045 1691131 := bstep (se 1 (by rfl) ⟨1268348, by rfl⟩ : syracuseStep 1691131 = 2536697) B2536697
theorem B1691199 : Blo 1690045 1691199 := bstep (se 1 (by rfl) ⟨1268399, by rfl⟩ : syracuseStep 1691199 = 2536799) B2536799
theorem B1691207 : Blo 1690045 1691207 := bstep (se 1 (by rfl) ⟨1268405, by rfl⟩ : syracuseStep 1691207 = 2536811) B2536811
theorem B3804767 : Blo 1690045 3804767 := bstep (se 1 (by rfl) ⟨2853575, by rfl⟩ : syracuseStep 3804767 = 5707151) B5707151
theorem B1691359 : Blo 1690045 1691359 := bstep (se 1 (by rfl) ⟨1268519, by rfl⟩ : syracuseStep 1691359 = 2537039) B2537039
theorem B2535209 : Blo 1690045 2535209 := bstep (se 2 (by rfl) ⟨950703, by rfl⟩ : syracuseStep 2535209 = 1901407) B1901407
theorem B4337449 : Blo 1690045 4337449 := bstep (se 2 (by rfl) ⟨1626543, by rfl⟩ : syracuseStep 4337449 = 3253087) B3253087
theorem B2535215 : Blo 1690045 2535215 := bstep (se 1 (by rfl) ⟨1901411, by rfl⟩ : syracuseStep 2535215 = 3802823) B3802823
theorem B6418223 : Blo 1690045 6418223 := bstep (se 1 (by rfl) ⟨4813667, by rfl⟩ : syracuseStep 6418223 = 9627335) B9627335
theorem B4280111 : Blo 1690045 4280111 := bstep (se 1 (by rfl) ⟨3210083, by rfl⟩ : syracuseStep 4280111 = 6420167) B6420167
theorem B1691439 : Blo 1690045 1691439 := bstep (se 1 (by rfl) ⟨1268579, by rfl⟩ : syracuseStep 1691439 = 2537159) B2537159
theorem B3804983 : Blo 1690045 3804983 := bstep (se 1 (by rfl) ⟨2853737, by rfl⟩ : syracuseStep 3804983 = 5707475) B5707475
theorem B6418237 : Blo 1690045 6418237 := bstep (se 3 (by rfl) ⟨1203419, by rfl⟩ : syracuseStep 6418237 = 2406839) B2406839
theorem B18288665 : Blo 1690045 18288665 := bstep (se 2 (by rfl) ⟨6858249, by rfl⟩ : syracuseStep 18288665 = 13716499) B13716499
theorem B3805289 : Blo 1690045 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B2535689 : Blo 1690045 2535689 := bstep (se 2 (by rfl) ⟨950883, by rfl⟩ : syracuseStep 2535689 = 1901767) B1901767
theorem B7221595 : Blo 1690045 7221595 := bstep (se 1 (by rfl) ⟨5416196, by rfl⟩ : syracuseStep 7221595 = 10832393) B10832393
theorem B16691561 : Blo 1690045 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B7221611 : Blo 1690045 7221611 := bstep (se 1 (by rfl) ⟨5416208, by rfl⟩ : syracuseStep 7221611 = 10832417) B10832417
theorem B2707823 : Blo 1690045 2707823 := bstep (se 1 (by rfl) ⟨2030867, by rfl⟩ : syracuseStep 2707823 = 4061735) B4061735
theorem B2535791 : Blo 1690045 2535791 := bstep (se 1 (by rfl) ⟨1901843, by rfl⟩ : syracuseStep 2535791 = 3803687) B3803687
theorem B12358003 : Blo 1690045 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B4280759 : Blo 1690045 4280759 := bstep (se 1 (by rfl) ⟨3210569, by rfl⟩ : syracuseStep 4280759 = 6421139) B6421139
theorem B8557001 : Blo 1690045 8557001 := bstep (se 2 (by rfl) ⟨3208875, by rfl⟩ : syracuseStep 8557001 = 6417751) B6417751
theorem B9138689 : Blo 1690045 9138689 := bstep (se 2 (by rfl) ⟨3427008, by rfl⟩ : syracuseStep 9138689 = 6854017) B6854017
theorem B2536007 : Blo 1690045 2536007 := bstep (se 1 (by rfl) ⟨1902005, by rfl⟩ : syracuseStep 2536007 = 3804011) B3804011
theorem B3854927 : Blo 1690045 3854927 := bstep (se 1 (by rfl) ⟨2891195, by rfl⟩ : syracuseStep 3854927 = 5782391) B5782391
theorem B3805775 : Blo 1690045 3805775 := bstep (se 1 (by rfl) ⟨2854331, by rfl⟩ : syracuseStep 3805775 = 5708663) B5708663
theorem B2536043 : Blo 1690045 2536043 := bstep (se 1 (by rfl) ⟨1902032, by rfl⟩ : syracuseStep 2536043 = 3804065) B3804065
theorem B3805919 : Blo 1690045 3805919 := bstep (se 1 (by rfl) ⟨2854439, by rfl⟩ : syracuseStep 3805919 = 5708879) B5708879
theorem B2536271 : Blo 1690045 2536271 := bstep (se 1 (by rfl) ⟨1902203, by rfl⟩ : syracuseStep 2536271 = 3804407) B3804407
theorem B28890269 : Blo 1690045 28890269 := bstep (se 3 (by rfl) ⟨5416925, by rfl⟩ : syracuseStep 28890269 = 10833851) B10833851
theorem B2536667 : Blo 1690045 2536667 := bstep (se 1 (by rfl) ⟨1902500, by rfl⟩ : syracuseStep 2536667 = 3805001) B3805001
theorem B8557811 : Blo 1690045 8557811 := bstep (se 1 (by rfl) ⟨6418358, by rfl⟩ : syracuseStep 8557811 = 12836717) B12836717
theorem B2536841 : Blo 1690045 2536841 := bstep (se 2 (by rfl) ⟨951315, by rfl⟩ : syracuseStep 2536841 = 1902631) B1902631
theorem B32511395 : Blo 1690045 32511395 := bstep (se 1 (by rfl) ⟨24383546, by rfl⟩ : syracuseStep 32511395 = 48767093) B48767093
theorem B7222841 : Blo 1690045 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B5707421 : Blo 1690045 5707421 := bstep (se 3 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 5707421 = 2140283) B2140283
theorem B3208891 : Blo 1690045 3208891 := bstep (se 1 (by rfl) ⟨2406668, by rfl⟩ : syracuseStep 3208891 = 4813337) B4813337
theorem B2537195 : Blo 1690045 2537195 := bstep (se 1 (by rfl) ⟨1902896, by rfl⟩ : syracuseStep 2537195 = 3805793) B3805793
theorem B3208967 : Blo 1690045 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B4568879 : Blo 1690045 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B4339585 : Blo 1690045 4339585 := bstep (se 2 (by rfl) ⟨1627344, by rfl⟩ : syracuseStep 4339585 = 3254689) B3254689
theorem B30087197 : Blo 1690045 30087197 := bstep (se 3 (by rfl) ⟨5641349, by rfl⟩ : syracuseStep 30087197 = 11282699) B11282699
theorem B4814977 : Blo 1690045 4814977 := bstep (se 2 (by rfl) ⟨1805616, by rfl⟩ : syracuseStep 4814977 = 3611233) B3611233
theorem B5707961 : Blo 1690045 5707961 := bstep (se 2 (by rfl) ⟨2140485, by rfl⟩ : syracuseStep 5707961 = 4280971) B4280971
theorem B24377669 : Blo 1690045 24377669 := bstep (se 4 (by rfl) ⟨2285406, by rfl⟩ : syracuseStep 24377669 = 4570813) B4570813
theorem B4119059 : Blo 1690045 4119059 := bstep (se 1 (by rfl) ⟨3089294, by rfl⟩ : syracuseStep 4119059 = 6178589) B6178589
theorem B5143103 : Blo 1690045 5143103 := bstep (se 1 (by rfl) ⟨3857327, by rfl⟩ : syracuseStep 5143103 = 7714655) B7714655
theorem B2407033 : Blo 1690045 2407033 := bstep (se 2 (by rfl) ⟨902637, by rfl⟩ : syracuseStep 2407033 = 1805275) B1805275
theorem B55573127 : Blo 1690045 55573127 := bstep (se 1 (by rfl) ⟨41679845, by rfl⟩ : syracuseStep 55573127 = 83359691) B83359691
theorem B7322359 : Blo 1690045 7322359 := bstep (se 1 (by rfl) ⟨5491769, by rfl⟩ : syracuseStep 7322359 = 10983539) B10983539
theorem B16071443 : Blo 1690045 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B10828829 : Blo 1690045 10828829 := bstep (se 3 (by rfl) ⟨2030405, by rfl⟩ : syracuseStep 10828829 = 4060811) B4060811
theorem B4815911 : Blo 1690045 4815911 := bstep (se 1 (by rfl) ⟨3611933, by rfl⟩ : syracuseStep 4815911 = 7223867) B7223867
theorem B8559755 : Blo 1690045 8559755 := bstep (se 1 (by rfl) ⟨6419816, by rfl⟩ : syracuseStep 8559755 = 12839633) B12839633
theorem B5782747 : Blo 1690045 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B6094217 : Blo 1690045 6094217 := bstep (se 2 (by rfl) ⟨2285331, by rfl⟩ : syracuseStep 6094217 = 4570663) B4570663
theorem B3210835 : Blo 1690045 3210835 := bstep (se 1 (by rfl) ⟨2408126, by rfl⟩ : syracuseStep 3210835 = 4816253) B4816253
theorem B6422111 : Blo 1690045 6422111 := bstep (se 1 (by rfl) ⟨4816583, by rfl⟩ : syracuseStep 6422111 = 9633167) B9633167
theorem B6422125 : Blo 1690045 6422125 := bstep (se 3 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 6422125 = 2408297) B2408297
theorem B9625351 : Blo 1690045 9625351 := bstep (se 1 (by rfl) ⟨7219013, by rfl⟩ : syracuseStep 9625351 = 14438027) B14438027
theorem B131768117 : Blo 1690045 131768117 := bstep (se 5 (by rfl) ⟨6176630, by rfl⟩ : syracuseStep 131768117 = 12353261) B12353261
theorem B6422429 : Blo 1690045 6422429 := bstep (se 3 (by rfl) ⟨1204205, by rfl⟩ : syracuseStep 6422429 = 2408411) B2408411
theorem B14442401 : Blo 1690045 14442401 := bstep (se 2 (by rfl) ⟨5415900, by rfl⟩ : syracuseStep 14442401 = 10831801) B10831801
theorem B8126543 : Blo 1690045 8126543 := bstep (se 1 (by rfl) ⟨6094907, by rfl⟩ : syracuseStep 8126543 = 12189815) B12189815
theorem B19251431 : Blo 1690045 19251431 := bstep (se 1 (by rfl) ⟨14438573, by rfl⟩ : syracuseStep 19251431 = 28877147) B28877147
theorem B2031847 : Blo 1690045 2031847 := bstep (se 1 (by rfl) ⟨1523885, by rfl⟩ : syracuseStep 2031847 = 3047771) B3047771
theorem B22569293 : Blo 1690045 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B17351111 : Blo 1690045 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B19260179 : Blo 1690045 19260179 := bstep (se 1 (by rfl) ⟨14445134, by rfl⟩ : syracuseStep 19260179 = 28890269) B28890269
theorem B1901479 : Blo 1690045 1901479 := bstep (se 1 (by rfl) ⟨1426109, by rfl⟩ : syracuseStep 1901479 = 2852219) B2852219
theorem B2139311 : Blo 1690045 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B3802643 : Blo 1690045 3802643 := bstep (se 1 (by rfl) ⟨2851982, by rfl⟩ : syracuseStep 3802643 = 5703965) B5703965
theorem B7710329 : Blo 1690045 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B2852671 : Blo 1690045 2852671 := bstep (se 1 (by rfl) ⟨2139503, by rfl⟩ : syracuseStep 2852671 = 4279007) B4279007
theorem B3426295 : Blo 1690045 3426295 := bstep (se 1 (by rfl) ⟨2569721, by rfl⟩ : syracuseStep 3426295 = 5139443) B5139443
theorem B23144453 : Blo 1690045 23144453 := bstep (se 4 (by rfl) ⟨2169792, by rfl⟩ : syracuseStep 23144453 = 4339585) B4339585
theorem B7219219 : Blo 1690045 7219219 := bstep (se 1 (by rfl) ⟨5414414, by rfl⟩ : syracuseStep 7219219 = 10828829) B10828829
theorem B8562833 : Blo 1690045 8562833 := bstep (se 2 (by rfl) ⟨3211062, by rfl⟩ : syracuseStep 8562833 = 6422125) B6422125
theorem B3803327 : Blo 1690045 3803327 := bstep (se 1 (by rfl) ⟨2852495, by rfl⟩ : syracuseStep 3803327 = 5704991) B5704991
theorem B13371601 : Blo 1690045 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B4278521 : Blo 1690045 4278521 := bstep (se 2 (by rfl) ⟨1604445, by rfl⟩ : syracuseStep 4278521 = 3208891) B3208891
theorem B1690139 : Blo 1690045 1690139 := bstep (se 1 (by rfl) ⟨1267604, by rfl⟩ : syracuseStep 1690139 = 2535209) B2535209
theorem B1690143 : Blo 1690045 1690143 := bstep (se 1 (by rfl) ⟨1267607, by rfl⟩ : syracuseStep 1690143 = 2535215) B2535215
theorem B4278815 : Blo 1690045 4278815 := bstep (se 1 (by rfl) ⟨3209111, by rfl⟩ : syracuseStep 4278815 = 6418223) B6418223
theorem B2853407 : Blo 1690045 2853407 := bstep (se 1 (by rfl) ⟨2140055, by rfl⟩ : syracuseStep 2853407 = 4280111) B4280111
theorem B87845411 : Blo 1690045 87845411 := bstep (se 1 (by rfl) ⟨65884058, by rfl⟩ : syracuseStep 87845411 = 131768117) B131768117
theorem B2853481 : Blo 1690045 2853481 := bstep (se 2 (by rfl) ⟨1070055, by rfl⟩ : syracuseStep 2853481 = 2140111) B2140111
theorem B9628267 : Blo 1690045 9628267 := bstep (se 1 (by rfl) ⟨7221200, by rfl⟩ : syracuseStep 9628267 = 14442401) B14442401
theorem B12192443 : Blo 1690045 12192443 := bstep (se 1 (by rfl) ⟨9144332, by rfl⟩ : syracuseStep 12192443 = 18288665) B18288665
theorem B1690459 : Blo 1690045 1690459 := bstep (se 1 (by rfl) ⟨1267844, by rfl⟩ : syracuseStep 1690459 = 2535689) B2535689
theorem B11127707 : Blo 1690045 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B1805215 : Blo 1690045 1805215 := bstep (se 1 (by rfl) ⟨1353911, by rfl⟩ : syracuseStep 1805215 = 2707823) B2707823
theorem B1690527 : Blo 1690045 1690527 := bstep (se 1 (by rfl) ⟨1267895, by rfl⟩ : syracuseStep 1690527 = 2535791) B2535791
theorem B2853839 : Blo 1690045 2853839 := bstep (se 1 (by rfl) ⟨2140379, by rfl⟩ : syracuseStep 2853839 = 4280759) B4280759
theorem B5704667 : Blo 1690045 5704667 := bstep (se 1 (by rfl) ⟨4278500, by rfl⟩ : syracuseStep 5704667 = 8557001) B8557001
theorem B1690671 : Blo 1690045 1690671 := bstep (se 1 (by rfl) ⟨1268003, by rfl⟩ : syracuseStep 1690671 = 2536007) B2536007
theorem B1690695 : Blo 1690045 1690695 := bstep (se 1 (by rfl) ⟨1268021, by rfl⟩ : syracuseStep 1690695 = 2536043) B2536043
theorem B9628793 : Blo 1690045 9628793 := bstep (se 2 (by rfl) ⟨3610797, by rfl⟩ : syracuseStep 9628793 = 7221595) B7221595
theorem B3804281 : Blo 1690045 3804281 := bstep (se 2 (by rfl) ⟨1426605, by rfl⟩ : syracuseStep 3804281 = 2853211) B2853211
theorem B16477337 : Blo 1690045 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B1690847 : Blo 1690045 1690847 := bstep (se 1 (by rfl) ⟨1268135, by rfl⟩ : syracuseStep 1690847 = 2536271) B2536271
theorem B5704937 : Blo 1690045 5704937 := bstep (se 2 (by rfl) ⟨2139351, by rfl⟩ : syracuseStep 5704937 = 4278703) B4278703
theorem B1691111 : Blo 1690045 1691111 := bstep (se 1 (by rfl) ⟨1268333, by rfl⟩ : syracuseStep 1691111 = 2536667) B2536667
theorem B5705207 : Blo 1690045 5705207 := bstep (se 1 (by rfl) ⟨4278905, by rfl⟩ : syracuseStep 5705207 = 8557811) B8557811
theorem B1691227 : Blo 1690045 1691227 := bstep (se 1 (by rfl) ⟨1268420, by rfl⟩ : syracuseStep 1691227 = 2536841) B2536841
theorem B3804947 : Blo 1690045 3804947 := bstep (se 1 (by rfl) ⟨2853710, by rfl⟩ : syracuseStep 3804947 = 5707421) B5707421
theorem B2535239 : Blo 1690045 2535239 := bstep (se 1 (by rfl) ⟨1901429, by rfl⟩ : syracuseStep 2535239 = 3802859) B3802859
theorem B1691463 : Blo 1690045 1691463 := bstep (se 1 (by rfl) ⟨1268597, by rfl⟩ : syracuseStep 1691463 = 2537195) B2537195
theorem B2535323 : Blo 1690045 2535323 := bstep (se 1 (by rfl) ⟨1901492, by rfl⟩ : syracuseStep 2535323 = 3802985) B3802985
theorem B4812767 : Blo 1690045 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B20058131 : Blo 1690045 20058131 := bstep (se 1 (by rfl) ⟨15043598, by rfl⟩ : syracuseStep 20058131 = 30087197) B30087197
theorem B3805307 : Blo 1690045 3805307 := bstep (se 1 (by rfl) ⟨2853980, by rfl⟩ : syracuseStep 3805307 = 5707961) B5707961
theorem B3428735 : Blo 1690045 3428735 := bstep (se 1 (by rfl) ⟨2571551, by rfl⟩ : syracuseStep 3428735 = 5143103) B5143103
theorem B3805577 : Blo 1690045 3805577 := bstep (se 2 (by rfl) ⟨1427091, by rfl⟩ : syracuseStep 3805577 = 2854183) B2854183
theorem B37048751 : Blo 1690045 37048751 := bstep (se 1 (by rfl) ⟨27786563, by rfl⟩ : syracuseStep 37048751 = 55573127) B55573127
theorem B2535887 : Blo 1690045 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B2535929 : Blo 1690045 2535929 := bstep (se 2 (by rfl) ⟨950973, by rfl⟩ : syracuseStep 2535929 = 1901947) B1901947
theorem B5706233 : Blo 1690045 5706233 := bstep (se 2 (by rfl) ⟨2139837, by rfl⟩ : syracuseStep 5706233 = 4279675) B4279675
theorem B6419027 : Blo 1690045 6419027 := bstep (se 1 (by rfl) ⟨4814270, by rfl⟩ : syracuseStep 6419027 = 9628541) B9628541
theorem B2536031 : Blo 1690045 2536031 := bstep (se 1 (by rfl) ⟨1902023, by rfl⟩ : syracuseStep 2536031 = 3804047) B3804047
theorem B5706503 : Blo 1690045 5706503 := bstep (se 1 (by rfl) ⟨4279877, by rfl⟩ : syracuseStep 5706503 = 8559755) B8559755
theorem B4281113 : Blo 1690045 4281113 := bstep (se 2 (by rfl) ⟨1605417, by rfl⟩ : syracuseStep 4281113 = 3210835) B3210835
theorem B5706557 : Blo 1690045 5706557 := bstep (se 3 (by rfl) ⟨1069979, by rfl⟩ : syracuseStep 5706557 = 2139959) B2139959
theorem B12833801 : Blo 1690045 12833801 := bstep (se 2 (by rfl) ⟨4812675, by rfl⟩ : syracuseStep 12833801 = 9625351) B9625351
theorem B2536511 : Blo 1690045 2536511 := bstep (se 1 (by rfl) ⟨1902383, by rfl⟩ : syracuseStep 2536511 = 3804767) B3804767
theorem B4281407 : Blo 1690045 4281407 := bstep (se 1 (by rfl) ⟨3211055, by rfl⟩ : syracuseStep 4281407 = 6422111) B6422111
theorem B8557649 : Blo 1690045 8557649 := bstep (se 2 (by rfl) ⟨3209118, by rfl⟩ : syracuseStep 8557649 = 6418237) B6418237
theorem B2536553 : Blo 1690045 2536553 := bstep (se 2 (by rfl) ⟨951207, by rfl⟩ : syracuseStep 2536553 = 1902415) B1902415
theorem B2536655 : Blo 1690045 2536655 := bstep (se 1 (by rfl) ⟨1902491, by rfl⟩ : syracuseStep 2536655 = 3804983) B3804983
theorem B4281619 : Blo 1690045 4281619 := bstep (se 1 (by rfl) ⟨3211214, by rfl⟩ : syracuseStep 4281619 = 6422429) B6422429
theorem B2536859 : Blo 1690045 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B6419969 : Blo 1690045 6419969 := bstep (se 2 (by rfl) ⟨2407488, by rfl⟩ : syracuseStep 6419969 = 4814977) B4814977
theorem B7321097 : Blo 1690045 7321097 := bstep (se 2 (by rfl) ⟨2745411, by rfl⟩ : syracuseStep 7321097 = 5490823) B5490823
theorem B3610183 : Blo 1690045 3610183 := bstep (se 1 (by rfl) ⟨2707637, by rfl⟩ : syracuseStep 3610183 = 5415275) B5415275
theorem B4814407 : Blo 1690045 4814407 := bstep (se 1 (by rfl) ⟨3610805, by rfl⟩ : syracuseStep 4814407 = 7221611) B7221611
theorem B2537081 : Blo 1690045 2537081 := bstep (se 2 (by rfl) ⟨951405, by rfl⟩ : syracuseStep 2537081 = 1902811) B1902811
theorem B6092459 : Blo 1690045 6092459 := bstep (se 1 (by rfl) ⟨4569344, by rfl⟩ : syracuseStep 6092459 = 9138689) B9138689
theorem B2569951 : Blo 1690045 2569951 := bstep (se 1 (by rfl) ⟨1927463, by rfl⟩ : syracuseStep 2569951 = 3854927) B3854927
theorem B2537183 : Blo 1690045 2537183 := bstep (se 1 (by rfl) ⟨1902887, by rfl⟩ : syracuseStep 2537183 = 3805775) B3805775
theorem B5707583 : Blo 1690045 5707583 := bstep (se 1 (by rfl) ⟨4280687, by rfl⟩ : syracuseStep 5707583 = 8561375) B8561375
theorem B2537279 : Blo 1690045 2537279 := bstep (se 1 (by rfl) ⟨1902959, by rfl⟩ : syracuseStep 2537279 = 3805919) B3805919
theorem B2316271 : Blo 1690045 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B30087245 : Blo 1690045 30087245 := bstep (se 3 (by rfl) ⟨5641358, by rfl⟩ : syracuseStep 30087245 = 11282717) B11282717
theorem B13711465 : Blo 1690045 13711465 := bstep (se 2 (by rfl) ⟨5141799, by rfl⟩ : syracuseStep 13711465 = 10283599) B10283599
theorem B3209377 : Blo 1690045 3209377 := bstep (se 2 (by rfl) ⟨1203516, by rfl⟩ : syracuseStep 3209377 = 2407033) B2407033
theorem B21674263 : Blo 1690045 21674263 := bstep (se 1 (by rfl) ⟨16255697, by rfl⟩ : syracuseStep 21674263 = 32511395) B32511395
theorem B9763145 : Blo 1690045 9763145 := bstep (se 2 (by rfl) ⟨3661179, by rfl⟩ : syracuseStep 9763145 = 7322359) B7322359
theorem B4815227 : Blo 1690045 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B3045919 : Blo 1690045 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B10984157 : Blo 1690045 10984157 := bstep (se 3 (by rfl) ⟨2059529, by rfl⟩ : syracuseStep 10984157 = 4119059) B4119059
theorem B10836827 : Blo 1690045 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B16251779 : Blo 1690045 16251779 := bstep (se 1 (by rfl) ⟨12188834, by rfl⟩ : syracuseStep 16251779 = 24377669) B24377669
theorem B23133061 : Blo 1690045 23133061 := bstep (se 4 (by rfl) ⟨2168724, by rfl⟩ : syracuseStep 23133061 = 4337449) B4337449
theorem B10714295 : Blo 1690045 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B3210607 : Blo 1690045 3210607 := bstep (se 1 (by rfl) ⟨2407955, by rfl⟩ : syracuseStep 3210607 = 4815911) B4815911
theorem B4062811 : Blo 1690045 4062811 := bstep (se 1 (by rfl) ⟨3047108, by rfl⟩ : syracuseStep 4062811 = 6094217) B6094217
theorem B22568861 : Blo 1690045 22568861 := bstep (se 3 (by rfl) ⟨4231661, by rfl⟩ : syracuseStep 22568861 = 8463323) B8463323
theorem B9625625 : Blo 1690045 9625625 := bstep (se 2 (by rfl) ⟨3609609, by rfl⟩ : syracuseStep 9625625 = 7219219) B7219219
theorem B80232653 : Blo 1690045 80232653 := bstep (se 3 (by rfl) ⟨15043622, by rfl⟩ : syracuseStep 80232653 = 30087245) B30087245
theorem B24699167 : Blo 1690045 24699167 := bstep (se 1 (by rfl) ⟨18524375, by rfl⟩ : syracuseStep 24699167 = 37048751) B37048751
theorem B11567407 : Blo 1690045 11567407 := bstep (se 1 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 11567407 = 17351111) B17351111
theorem B12837689 : Blo 1690045 12837689 := bstep (se 2 (by rfl) ⟨4814133, by rfl⟩ : syracuseStep 12837689 = 9628267) B9628267
theorem B9143293 : Blo 1690045 9143293 := bstep (se 3 (by rfl) ⟨1714367, by rfl⟩ : syracuseStep 9143293 = 3428735) B3428735
theorem B13706405 : Blo 1690045 13706405 := bstep (se 4 (by rfl) ⟨1284975, by rfl⟩ : syracuseStep 13706405 = 2569951) B2569951
theorem B30844081 : Blo 1690045 30844081 := bstep (se 2 (by rfl) ⟨11566530, by rfl⟩ : syracuseStep 30844081 = 23133061) B23133061
theorem B2852347 : Blo 1690045 2852347 := bstep (se 1 (by rfl) ⟨2139260, by rfl⟩ : syracuseStep 2852347 = 4278521) B4278521
theorem B2852543 : Blo 1690045 2852543 := bstep (se 1 (by rfl) ⟨2139407, by rfl⟩ : syracuseStep 2852543 = 4278815) B4278815
theorem B1902271 : Blo 1690045 1902271 := bstep (se 1 (by rfl) ⟨1426703, by rfl⟩ : syracuseStep 1902271 = 2853407) B2853407
theorem B8128295 : Blo 1690045 8128295 := bstep (se 1 (by rfl) ⟨6096221, by rfl⟩ : syracuseStep 8128295 = 12192443) B12192443
theorem B1902559 : Blo 1690045 1902559 := bstep (se 1 (by rfl) ⟨1426919, by rfl⟩ : syracuseStep 1902559 = 2853839) B2853839
theorem B3803111 : Blo 1690045 3803111 := bstep (se 1 (by rfl) ⟨2852333, by rfl⟩ : syracuseStep 3803111 = 5704667) B5704667
theorem B5417081 : Blo 1690045 5417081 := bstep (se 2 (by rfl) ⟨2031405, by rfl⟩ : syracuseStep 5417081 = 4062811) B4062811
theorem B3803291 : Blo 1690045 3803291 := bstep (se 1 (by rfl) ⟨2852468, by rfl⟩ : syracuseStep 3803291 = 5704937) B5704937
theorem B3803471 : Blo 1690045 3803471 := bstep (se 1 (by rfl) ⟨2852603, by rfl⟩ : syracuseStep 3803471 = 5705207) B5705207
theorem B3803561 : Blo 1690045 3803561 := bstep (se 2 (by rfl) ⟨1426335, by rfl⟩ : syracuseStep 3803561 = 2852671) B2852671
theorem B1690159 : Blo 1690045 1690159 := bstep (se 1 (by rfl) ⟨1267619, by rfl⟩ : syracuseStep 1690159 = 2535239) B2535239
theorem B1690215 : Blo 1690045 1690215 := bstep (se 1 (by rfl) ⟨1267661, by rfl⟩ : syracuseStep 1690215 = 2535323) B2535323
theorem B53488349 : Blo 1690045 53488349 := bstep (se 3 (by rfl) ⟨10029065, by rfl⟩ : syracuseStep 53488349 = 20058131) B20058131
theorem B5417695 : Blo 1690045 5417695 := bstep (se 1 (by rfl) ⟨4063271, by rfl⟩ : syracuseStep 5417695 = 8126543) B8126543
theorem B4279169 : Blo 1690045 4279169 := bstep (se 2 (by rfl) ⟨1604688, by rfl⟩ : syracuseStep 4279169 = 3209377) B3209377
theorem B17828801 : Blo 1690045 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B1690591 : Blo 1690045 1690591 := bstep (se 1 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 1690591 = 2535887) B2535887
theorem B1690619 : Blo 1690045 1690619 := bstep (se 1 (by rfl) ⟨1267964, by rfl⟩ : syracuseStep 1690619 = 2535929) B2535929
theorem B3804155 : Blo 1690045 3804155 := bstep (se 1 (by rfl) ⟨2853116, by rfl⟩ : syracuseStep 3804155 = 5706233) B5706233
theorem B4279351 : Blo 1690045 4279351 := bstep (se 1 (by rfl) ⟨3209513, by rfl⟩ : syracuseStep 4279351 = 6419027) B6419027
theorem B1690687 : Blo 1690045 1690687 := bstep (se 1 (by rfl) ⟨1268015, by rfl⟩ : syracuseStep 1690687 = 2536031) B2536031
theorem B5704829 : Blo 1690045 5704829 := bstep (se 3 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 5704829 = 2139311) B2139311
theorem B3804335 : Blo 1690045 3804335 := bstep (se 1 (by rfl) ⟨2853251, by rfl⟩ : syracuseStep 3804335 = 5706503) B5706503
theorem B12840119 : Blo 1690045 12840119 := bstep (se 1 (by rfl) ⟨9630089, by rfl⟩ : syracuseStep 12840119 = 19260179) B19260179
theorem B2854075 : Blo 1690045 2854075 := bstep (se 1 (by rfl) ⟨2140556, by rfl⟩ : syracuseStep 2854075 = 4281113) B4281113
theorem B3804371 : Blo 1690045 3804371 := bstep (se 1 (by rfl) ⟨2853278, by rfl⟩ : syracuseStep 3804371 = 5706557) B5706557
theorem B8555867 : Blo 1690045 8555867 := bstep (se 1 (by rfl) ⟨6416900, by rfl⟩ : syracuseStep 8555867 = 12833801) B12833801
theorem B1691007 : Blo 1690045 1691007 := bstep (se 1 (by rfl) ⟨1268255, by rfl⟩ : syracuseStep 1691007 = 2536511) B2536511
theorem B2854271 : Blo 1690045 2854271 := bstep (se 1 (by rfl) ⟨2140703, by rfl⟩ : syracuseStep 2854271 = 4281407) B4281407
theorem B5705099 : Blo 1690045 5705099 := bstep (se 1 (by rfl) ⟨4278824, by rfl⟩ : syracuseStep 5705099 = 8557649) B8557649
theorem B1691035 : Blo 1690045 1691035 := bstep (se 1 (by rfl) ⟨1268276, by rfl⟩ : syracuseStep 1691035 = 2536553) B2536553
theorem B1691103 : Blo 1690045 1691103 := bstep (se 1 (by rfl) ⟨1268327, by rfl⟩ : syracuseStep 1691103 = 2536655) B2536655
theorem B3804641 : Blo 1690045 3804641 := bstep (se 2 (by rfl) ⟨1426740, by rfl⟩ : syracuseStep 3804641 = 2853481) B2853481
theorem B1691239 : Blo 1690045 1691239 := bstep (se 1 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 1691239 = 2536859) B2536859
theorem B12840605 : Blo 1690045 12840605 := bstep (se 3 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 12840605 = 4815227) B4815227
theorem B4279979 : Blo 1690045 4279979 := bstep (se 1 (by rfl) ⟨3209984, by rfl⟩ : syracuseStep 4279979 = 6419969) B6419969
theorem B2535095 : Blo 1690045 2535095 := bstep (se 1 (by rfl) ⟨1901321, by rfl⟩ : syracuseStep 2535095 = 3802643) B3802643
theorem B1691387 : Blo 1690045 1691387 := bstep (se 1 (by rfl) ⟨1268540, by rfl⟩ : syracuseStep 1691387 = 2537081) B2537081
theorem B1691455 : Blo 1690045 1691455 := bstep (se 1 (by rfl) ⟨1268591, by rfl⟩ : syracuseStep 1691455 = 2537183) B2537183
theorem B3805055 : Blo 1690045 3805055 := bstep (se 1 (by rfl) ⟨2853791, by rfl⟩ : syracuseStep 3805055 = 5707583) B5707583
theorem B1691519 : Blo 1690045 1691519 := bstep (se 1 (by rfl) ⟨1268639, by rfl⟩ : syracuseStep 1691519 = 2537279) B2537279
theorem B2535305 : Blo 1690045 2535305 := bstep (se 2 (by rfl) ⟨950739, by rfl⟩ : syracuseStep 2535305 = 1901479) B1901479
theorem B15429635 : Blo 1690045 15429635 := bstep (se 1 (by rfl) ⟨11572226, by rfl⟩ : syracuseStep 15429635 = 23144453) B23144453
theorem B2535551 : Blo 1690045 2535551 := bstep (se 1 (by rfl) ⟨1901663, by rfl⟩ : syracuseStep 2535551 = 3803327) B3803327
theorem B6508763 : Blo 1690045 6508763 := bstep (se 1 (by rfl) ⟨4881572, by rfl⟩ : syracuseStep 6508763 = 9763145) B9763145
theorem B4280809 : Blo 1690045 4280809 := bstep (se 2 (by rfl) ⟨1605303, by rfl⟩ : syracuseStep 4280809 = 3210607) B3210607
theorem B10834519 : Blo 1690045 10834519 := bstep (se 1 (by rfl) ⟨8125889, by rfl⟩ : syracuseStep 10834519 = 16251779) B16251779
theorem B7418471 : Blo 1690045 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B6419195 : Blo 1690045 6419195 := bstep (se 1 (by rfl) ⟨4814396, by rfl⟩ : syracuseStep 6419195 = 9628793) B9628793
theorem B2536187 : Blo 1690045 2536187 := bstep (se 1 (by rfl) ⟨1902140, by rfl⟩ : syracuseStep 2536187 = 3804281) B3804281
theorem B4813577 : Blo 1690045 4813577 := bstep (se 2 (by rfl) ⟨1805091, by rfl⟩ : syracuseStep 4813577 = 3610183) B3610183
theorem B6419209 : Blo 1690045 6419209 := bstep (se 2 (by rfl) ⟨2407203, by rfl⟩ : syracuseStep 6419209 = 4814407) B4814407
theorem B2536631 : Blo 1690045 2536631 := bstep (se 1 (by rfl) ⟨1902473, by rfl⟩ : syracuseStep 2536631 = 3804947) B3804947
theorem B15045907 : Blo 1690045 15045907 := bstep (se 1 (by rfl) ⟨11284430, by rfl⟩ : syracuseStep 15045907 = 22568861) B22568861
theorem B3208511 : Blo 1690045 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B4568393 : Blo 1690045 4568393 := bstep (se 2 (by rfl) ⟨1713147, by rfl⟩ : syracuseStep 4568393 = 3426295) B3426295
theorem B2536871 : Blo 1690045 2536871 := bstep (se 1 (by rfl) ⟨1902653, by rfl⟩ : syracuseStep 2536871 = 3805307) B3805307
theorem B18281953 : Blo 1690045 18281953 := bstep (se 2 (by rfl) ⟨6855732, by rfl⟩ : syracuseStep 18281953 = 13711465) B13711465
theorem B12834287 : Blo 1690045 12834287 := bstep (se 1 (by rfl) ⟨9625715, by rfl⟩ : syracuseStep 12834287 = 19251431) B19251431
theorem B15046195 : Blo 1690045 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B2537051 : Blo 1690045 2537051 := bstep (se 1 (by rfl) ⟨1902788, by rfl⟩ : syracuseStep 2537051 = 3805577) B3805577
theorem B28899017 : Blo 1690045 28899017 := bstep (se 2 (by rfl) ⟨10837131, by rfl⟩ : syracuseStep 28899017 = 21674263) B21674263
theorem B4061225 : Blo 1690045 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B4880731 : Blo 1690045 4880731 := bstep (se 1 (by rfl) ⟨3660548, by rfl⟩ : syracuseStep 4880731 = 7321097) B7321097
theorem B4061639 : Blo 1690045 4061639 := bstep (se 1 (by rfl) ⟨3046229, by rfl⟩ : syracuseStep 4061639 = 6092459) B6092459
theorem B10836517 : Blo 1690045 10836517 := bstep (se 4 (by rfl) ⟨1015923, by rfl⟩ : syracuseStep 10836517 = 2031847) B2031847
theorem B2406953 : Blo 1690045 2406953 := bstep (se 2 (by rfl) ⟨902607, by rfl⟩ : syracuseStep 2406953 = 1805215) B1805215
theorem B5708555 : Blo 1690045 5708555 := bstep (se 1 (by rfl) ⟨4281416, by rfl⟩ : syracuseStep 5708555 = 8562833) B8562833
theorem B20560877 : Blo 1690045 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B58563607 : Blo 1690045 58563607 := bstep (se 1 (by rfl) ⟨43922705, by rfl⟩ : syracuseStep 58563607 = 87845411) B87845411
theorem B5708825 : Blo 1690045 5708825 := bstep (se 2 (by rfl) ⟨2140809, by rfl⟩ : syracuseStep 5708825 = 4281619) B4281619
theorem B7322771 : Blo 1690045 7322771 := bstep (se 1 (by rfl) ⟨5492078, by rfl⟩ : syracuseStep 7322771 = 10984157) B10984157
theorem B7224551 : Blo 1690045 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B10984891 : Blo 1690045 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B7142863 : Blo 1690045 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B3088361 : Blo 1690045 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B10829933 : Blo 1690045 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B16466111 : Blo 1690045 16466111 := bstep (se 1 (by rfl) ⟨12349583, by rfl⟩ : syracuseStep 16466111 = 24699167) B24699167
theorem B1901695 : Blo 1690045 1901695 := bstep (se 1 (by rfl) ⟨1426271, by rfl⟩ : syracuseStep 1901695 = 2852543) B2852543
theorem B12191057 : Blo 1690045 12191057 := bstep (se 2 (by rfl) ⟨4571646, by rfl⟩ : syracuseStep 12191057 = 9143293) B9143293
theorem B41125441 : Blo 1690045 41125441 := bstep (se 2 (by rfl) ⟨15422040, by rfl⟩ : syracuseStep 41125441 = 30844081) B30844081
theorem B2852779 : Blo 1690045 2852779 := bstep (se 1 (by rfl) ⟨2139584, by rfl⟩ : syracuseStep 2852779 = 4279169) B4279169
theorem B13707251 : Blo 1690045 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B3803129 : Blo 1690045 3803129 := bstep (se 2 (by rfl) ⟨1426173, by rfl⟩ : syracuseStep 3803129 = 2852347) B2852347
theorem B3803219 : Blo 1690045 3803219 := bstep (se 1 (by rfl) ⟨2852414, by rfl⟩ : syracuseStep 3803219 = 5704829) B5704829
theorem B5703911 : Blo 1690045 5703911 := bstep (se 1 (by rfl) ⟨4277933, by rfl⟩ : syracuseStep 5703911 = 8555867) B8555867
theorem B1902847 : Blo 1690045 1902847 := bstep (se 1 (by rfl) ⟨1427135, by rfl⟩ : syracuseStep 1902847 = 2854271) B2854271
theorem B3803399 : Blo 1690045 3803399 := bstep (se 1 (by rfl) ⟨2852549, by rfl⟩ : syracuseStep 3803399 = 5705099) B5705099
theorem B2853319 : Blo 1690045 2853319 := bstep (se 1 (by rfl) ⟨2139989, by rfl⟩ : syracuseStep 2853319 = 4279979) B4279979
theorem B1690063 : Blo 1690045 1690063 := bstep (se 1 (by rfl) ⟨1267547, by rfl⟩ : syracuseStep 1690063 = 2535095) B2535095
theorem B1690203 : Blo 1690045 1690203 := bstep (se 1 (by rfl) ⟨1267652, by rfl⟩ : syracuseStep 1690203 = 2535305) B2535305
theorem B2058907 : Blo 1690045 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B6417083 : Blo 1690045 6417083 := bstep (se 1 (by rfl) ⟨4812812, by rfl⟩ : syracuseStep 6417083 = 9625625) B9625625
theorem B1690367 : Blo 1690045 1690367 := bstep (se 1 (by rfl) ⟨1267775, by rfl⟩ : syracuseStep 1690367 = 2535551) B2535551
theorem B53488435 : Blo 1690045 53488435 := bstep (se 1 (by rfl) ⟨40116326, by rfl⟩ : syracuseStep 53488435 = 80232653) B80232653
theorem B6507641 : Blo 1690045 6507641 := bstep (se 2 (by rfl) ⟨2440365, by rfl⟩ : syracuseStep 6507641 = 4880731) B4880731
theorem B4279463 : Blo 1690045 4279463 := bstep (se 1 (by rfl) ⟨3209597, by rfl⟩ : syracuseStep 4279463 = 6419195) B6419195
theorem B1690791 : Blo 1690045 1690791 := bstep (se 1 (by rfl) ⟨1268093, by rfl⟩ : syracuseStep 1690791 = 2536187) B2536187
theorem B9137603 : Blo 1690045 9137603 := bstep (se 1 (by rfl) ⟨6853202, by rfl⟩ : syracuseStep 9137603 = 13706405) B13706405
theorem B14446025 : Blo 1690045 14446025 := bstep (se 2 (by rfl) ⟨5417259, by rfl⟩ : syracuseStep 14446025 = 10834519) B10834519
theorem B1691087 : Blo 1690045 1691087 := bstep (se 1 (by rfl) ⟨1268315, by rfl⟩ : syracuseStep 1691087 = 2536631) B2536631
theorem B8556029 : Blo 1690045 8556029 := bstep (se 3 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 8556029 = 3208511) B3208511
theorem B1691247 : Blo 1690045 1691247 := bstep (se 1 (by rfl) ⟨1268435, by rfl⟩ : syracuseStep 1691247 = 2536871) B2536871
theorem B8556191 : Blo 1690045 8556191 := bstep (se 1 (by rfl) ⟨6417143, by rfl⟩ : syracuseStep 8556191 = 12834287) B12834287
theorem B1691367 : Blo 1690045 1691367 := bstep (se 1 (by rfl) ⟨1268525, by rfl⟩ : syracuseStep 1691367 = 2537051) B2537051
theorem B5418863 : Blo 1690045 5418863 := bstep (se 1 (by rfl) ⟨4064147, by rfl⟩ : syracuseStep 5418863 = 8128295) B8128295
theorem B2535407 : Blo 1690045 2535407 := bstep (se 1 (by rfl) ⟨1901555, by rfl⟩ : syracuseStep 2535407 = 3803111) B3803111
theorem B5705801 : Blo 1690045 5705801 := bstep (se 2 (by rfl) ⟨2139675, by rfl⟩ : syracuseStep 5705801 = 4279351) B4279351
theorem B2535527 : Blo 1690045 2535527 := bstep (se 1 (by rfl) ⟨1901645, by rfl⟩ : syracuseStep 2535527 = 3803291) B3803291
theorem B6418541 : Blo 1690045 6418541 := bstep (se 3 (by rfl) ⟨1203476, by rfl⟩ : syracuseStep 6418541 = 2406953) B2406953
theorem B2535647 : Blo 1690045 2535647 := bstep (se 1 (by rfl) ⟨1901735, by rfl⟩ : syracuseStep 2535647 = 3803471) B3803471
theorem B3805433 : Blo 1690045 3805433 := bstep (se 2 (by rfl) ⟨1427037, by rfl⟩ : syracuseStep 3805433 = 2854075) B2854075
theorem B2535707 : Blo 1690045 2535707 := bstep (se 1 (by rfl) ⟨1901780, by rfl⟩ : syracuseStep 2535707 = 3803561) B3803561
theorem B2707759 : Blo 1690045 2707759 := bstep (se 1 (by rfl) ⟨2030819, by rfl⟩ : syracuseStep 2707759 = 4061639) B4061639
theorem B3805703 : Blo 1690045 3805703 := bstep (se 1 (by rfl) ⟨2854277, by rfl⟩ : syracuseStep 3805703 = 5708555) B5708555
theorem B9523817 : Blo 1690045 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B24375937 : Blo 1690045 24375937 := bstep (se 2 (by rfl) ⟨9140976, by rfl⟩ : syracuseStep 24375937 = 18281953) B18281953
theorem B2536103 : Blo 1690045 2536103 := bstep (se 1 (by rfl) ⟨1902077, by rfl⟩ : syracuseStep 2536103 = 3804155) B3804155
theorem B3805883 : Blo 1690045 3805883 := bstep (se 1 (by rfl) ⟨2854412, by rfl⟩ : syracuseStep 3805883 = 5708825) B5708825
theorem B2536223 : Blo 1690045 2536223 := bstep (se 1 (by rfl) ⟨1902167, by rfl⟩ : syracuseStep 2536223 = 3804335) B3804335
theorem B2536247 : Blo 1690045 2536247 := bstep (se 1 (by rfl) ⟨1902185, by rfl⟩ : syracuseStep 2536247 = 3804371) B3804371
theorem B2536361 : Blo 1690045 2536361 := bstep (se 2 (by rfl) ⟨951135, by rfl⟩ : syracuseStep 2536361 = 1902271) B1902271
theorem B2536427 : Blo 1690045 2536427 := bstep (se 1 (by rfl) ⟨1902320, by rfl⟩ : syracuseStep 2536427 = 3804641) B3804641
theorem B2536703 : Blo 1690045 2536703 := bstep (se 1 (by rfl) ⟨1902527, by rfl⟩ : syracuseStep 2536703 = 3805055) B3805055
theorem B2536745 : Blo 1690045 2536745 := bstep (se 2 (by rfl) ⟨951279, by rfl⟩ : syracuseStep 2536745 = 1902559) B1902559
theorem B10286423 : Blo 1690045 10286423 := bstep (se 1 (by rfl) ⟨7714817, by rfl⟩ : syracuseStep 10286423 = 15429635) B15429635
theorem B4339175 : Blo 1690045 4339175 := bstep (se 1 (by rfl) ⟨3254381, by rfl⟩ : syracuseStep 4339175 = 6508763) B6508763
theorem B19527389 : Blo 1690045 19527389 := bstep (se 3 (by rfl) ⟨3661385, by rfl⟩ : syracuseStep 19527389 = 7322771) B7322771
theorem B15423209 : Blo 1690045 15423209 := bstep (se 2 (by rfl) ⟨5783703, by rfl⟩ : syracuseStep 15423209 = 11567407) B11567407
theorem B3209051 : Blo 1690045 3209051 := bstep (se 1 (by rfl) ⟨2406788, by rfl⟩ : syracuseStep 3209051 = 4813577) B4813577
theorem B8558459 : Blo 1690045 8558459 := bstep (se 1 (by rfl) ⟨6418844, by rfl⟩ : syracuseStep 8558459 = 12837689) B12837689
theorem B5707745 : Blo 1690045 5707745 := bstep (se 2 (by rfl) ⟨2140404, by rfl⟩ : syracuseStep 5707745 = 4280809) B4280809
theorem B14448689 : Blo 1690045 14448689 := bstep (se 2 (by rfl) ⟨5418258, by rfl⟩ : syracuseStep 14448689 = 10836517) B10836517
theorem B3045595 : Blo 1690045 3045595 := bstep (se 1 (by rfl) ⟨2284196, by rfl⟩ : syracuseStep 3045595 = 4568393) B4568393
theorem B7223593 : Blo 1690045 7223593 := bstep (se 2 (by rfl) ⟨2708847, by rfl⟩ : syracuseStep 7223593 = 5417695) B5417695
theorem B8558945 : Blo 1690045 8558945 := bstep (se 2 (by rfl) ⟨3209604, by rfl⟩ : syracuseStep 8558945 = 6419209) B6419209
theorem B19266011 : Blo 1690045 19266011 := bstep (se 1 (by rfl) ⟨14449508, by rfl⟩ : syracuseStep 19266011 = 28899017) B28899017
theorem B78084809 : Blo 1690045 78084809 := bstep (se 2 (by rfl) ⟨29281803, by rfl⟩ : syracuseStep 78084809 = 58563607) B58563607
theorem B3611387 : Blo 1690045 3611387 := bstep (se 1 (by rfl) ⟨2708540, by rfl⟩ : syracuseStep 3611387 = 5417081) B5417081
theorem B19782589 : Blo 1690045 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B20061209 : Blo 1690045 20061209 := bstep (se 2 (by rfl) ⟨7522953, by rfl⟩ : syracuseStep 20061209 = 15045907) B15045907
theorem B35658899 : Blo 1690045 35658899 := bstep (se 1 (by rfl) ⟨26744174, by rfl⟩ : syracuseStep 35658899 = 53488349) B53488349
theorem B14646521 : Blo 1690045 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B11885867 : Blo 1690045 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B20061593 : Blo 1690045 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B8560079 : Blo 1690045 8560079 := bstep (se 1 (by rfl) ⟨6420059, by rfl⟩ : syracuseStep 8560079 = 12840119) B12840119
theorem B4816367 : Blo 1690045 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B8560403 : Blo 1690045 8560403 := bstep (se 1 (by rfl) ⟨6420302, by rfl⟩ : syracuseStep 8560403 = 12840605) B12840605
theorem B10977407 : Blo 1690045 10977407 := bstep (se 1 (by rfl) ⟨8233055, by rfl⟩ : syracuseStep 10977407 = 16466111) B16466111
theorem B6349211 : Blo 1690045 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B2745209 : Blo 1690045 2745209 := bstep (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) B2058907
theorem B8127371 : Blo 1690045 8127371 := bstep (se 1 (by rfl) ⟨6095528, by rfl⟩ : syracuseStep 8127371 = 12191057) B12191057
theorem B6857615 : Blo 1690045 6857615 := bstep (se 1 (by rfl) ⟨5143211, by rfl⟩ : syracuseStep 6857615 = 10286423) B10286423
theorem B13018259 : Blo 1690045 13018259 := bstep (se 1 (by rfl) ⟨9763694, by rfl⟩ : syracuseStep 13018259 = 19527389) B19527389
theorem B10282139 : Blo 1690045 10282139 := bstep (se 1 (by rfl) ⟨7711604, by rfl⟩ : syracuseStep 10282139 = 15423209) B15423209
theorem B2139367 : Blo 1690045 2139367 := bstep (se 1 (by rfl) ⟨1604525, by rfl⟩ : syracuseStep 2139367 = 3209051) B3209051
theorem B3802607 : Blo 1690045 3802607 := bstep (se 1 (by rfl) ⟨2851955, by rfl⟩ : syracuseStep 3802607 = 5703911) B5703911
theorem B4278055 : Blo 1690045 4278055 := bstep (se 1 (by rfl) ⟨3208541, by rfl⟩ : syracuseStep 4278055 = 6417083) B6417083
theorem B2852975 : Blo 1690045 2852975 := bstep (se 1 (by rfl) ⟨2139731, by rfl⟩ : syracuseStep 2852975 = 4279463) B4279463
theorem B7923911 : Blo 1690045 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B5704019 : Blo 1690045 5704019 := bstep (se 1 (by rfl) ⟨4278014, by rfl⟩ : syracuseStep 5704019 = 8556029) B8556029
theorem B5704127 : Blo 1690045 5704127 := bstep (se 1 (by rfl) ⟨4278095, by rfl⟩ : syracuseStep 5704127 = 8556191) B8556191
theorem B3803705 : Blo 1690045 3803705 := bstep (se 2 (by rfl) ⟨1426389, by rfl⟩ : syracuseStep 3803705 = 2852779) B2852779
theorem B1690271 : Blo 1690045 1690271 := bstep (se 1 (by rfl) ⟨1267703, by rfl⟩ : syracuseStep 1690271 = 2535407) B2535407
theorem B3803867 : Blo 1690045 3803867 := bstep (se 1 (by rfl) ⟨2852900, by rfl⟩ : syracuseStep 3803867 = 5705801) B5705801
theorem B53496557 : Blo 1690045 53496557 := bstep (se 3 (by rfl) ⟨10030604, by rfl⟩ : syracuseStep 53496557 = 20061209) B20061209
theorem B1690351 : Blo 1690045 1690351 := bstep (se 1 (by rfl) ⟨1267763, by rfl⟩ : syracuseStep 1690351 = 2535527) B2535527
theorem B7219955 : Blo 1690045 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B4279027 : Blo 1690045 4279027 := bstep (se 1 (by rfl) ⟨3209270, by rfl⟩ : syracuseStep 4279027 = 6418541) B6418541
theorem B1690431 : Blo 1690045 1690431 := bstep (se 1 (by rfl) ⟨1267823, by rfl⟩ : syracuseStep 1690431 = 2535647) B2535647
theorem B1690471 : Blo 1690045 1690471 := bstep (se 1 (by rfl) ⟨1267853, by rfl⟩ : syracuseStep 1690471 = 2535707) B2535707
theorem B17353709 : Blo 1690045 17353709 := bstep (se 3 (by rfl) ⟨3253820, by rfl⟩ : syracuseStep 17353709 = 6507641) B6507641
theorem B1690735 : Blo 1690045 1690735 := bstep (se 1 (by rfl) ⟨1268051, by rfl⟩ : syracuseStep 1690735 = 2536103) B2536103
theorem B1690815 : Blo 1690045 1690815 := bstep (se 1 (by rfl) ⟨1268111, by rfl⟩ : syracuseStep 1690815 = 2536223) B2536223
theorem B1690831 : Blo 1690045 1690831 := bstep (se 1 (by rfl) ⟨1268123, by rfl⟩ : syracuseStep 1690831 = 2536247) B2536247
theorem B3804425 : Blo 1690045 3804425 := bstep (se 2 (by rfl) ⟨1426659, by rfl⟩ : syracuseStep 3804425 = 2853319) B2853319
theorem B1690907 : Blo 1690045 1690907 := bstep (se 1 (by rfl) ⟨1268180, by rfl⟩ : syracuseStep 1690907 = 2536361) B2536361
theorem B1690951 : Blo 1690045 1690951 := bstep (se 1 (by rfl) ⟨1268213, by rfl⟩ : syracuseStep 1690951 = 2536427) B2536427
theorem B1691135 : Blo 1690045 1691135 := bstep (se 1 (by rfl) ⟨1268351, by rfl⟩ : syracuseStep 1691135 = 2536703) B2536703
theorem B32501249 : Blo 1690045 32501249 := bstep (se 2 (by rfl) ⟨12187968, by rfl⟩ : syracuseStep 32501249 = 24375937) B24375937
theorem B1691163 : Blo 1690045 1691163 := bstep (se 1 (by rfl) ⟨1268372, by rfl⟩ : syracuseStep 1691163 = 2536745) B2536745
theorem B5705639 : Blo 1690045 5705639 := bstep (se 1 (by rfl) ⟨4279229, by rfl⟩ : syracuseStep 5705639 = 8558459) B8558459
theorem B11571133 : Blo 1690045 11571133 := bstep (se 3 (by rfl) ⟨2169587, by rfl⟩ : syracuseStep 11571133 = 4339175) B4339175
theorem B3805163 : Blo 1690045 3805163 := bstep (se 1 (by rfl) ⟨2853872, by rfl⟩ : syracuseStep 3805163 = 5707745) B5707745
theorem B9138167 : Blo 1690045 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B2535419 : Blo 1690045 2535419 := bstep (se 1 (by rfl) ⟨1901564, by rfl⟩ : syracuseStep 2535419 = 3803129) B3803129
theorem B2535479 : Blo 1690045 2535479 := bstep (se 1 (by rfl) ⟨1901609, by rfl⟩ : syracuseStep 2535479 = 3803219) B3803219
theorem B2535593 : Blo 1690045 2535593 := bstep (se 2 (by rfl) ⟨950847, by rfl⟩ : syracuseStep 2535593 = 1901695) B1901695
theorem B2535599 : Blo 1690045 2535599 := bstep (se 1 (by rfl) ⟨1901699, by rfl⟩ : syracuseStep 2535599 = 3803399) B3803399
theorem B5705963 : Blo 1690045 5705963 := bstep (se 1 (by rfl) ⟨4279472, by rfl⟩ : syracuseStep 5705963 = 8558945) B8558945
theorem B52056539 : Blo 1690045 52056539 := bstep (se 1 (by rfl) ⟨39042404, by rfl⟩ : syracuseStep 52056539 = 78084809) B78084809
theorem B54833921 : Blo 1690045 54833921 := bstep (se 2 (by rfl) ⟨20562720, by rfl⟩ : syracuseStep 54833921 = 41125441) B41125441
theorem B13374395 : Blo 1690045 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B6091735 : Blo 1690045 6091735 := bstep (se 1 (by rfl) ⟨4568801, by rfl⟩ : syracuseStep 6091735 = 9137603) B9137603
theorem B9630683 : Blo 1690045 9630683 := bstep (se 1 (by rfl) ⟨7223012, by rfl⟩ : syracuseStep 9630683 = 14446025) B14446025
theorem B5706719 : Blo 1690045 5706719 := bstep (se 1 (by rfl) ⟨4280039, by rfl⟩ : syracuseStep 5706719 = 8560079) B8560079
theorem B5706935 : Blo 1690045 5706935 := bstep (se 1 (by rfl) ⟨4280201, by rfl⟩ : syracuseStep 5706935 = 8560403) B8560403
theorem B2536955 : Blo 1690045 2536955 := bstep (se 1 (by rfl) ⟨1902716, by rfl⟩ : syracuseStep 2536955 = 3805433) B3805433
theorem B4060793 : Blo 1690045 4060793 := bstep (se 2 (by rfl) ⟨1522797, by rfl⟩ : syracuseStep 4060793 = 3045595) B3045595
theorem B2537129 : Blo 1690045 2537129 := bstep (se 2 (by rfl) ⟨951423, by rfl⟩ : syracuseStep 2537129 = 1902847) B1902847
theorem B2537135 : Blo 1690045 2537135 := bstep (se 1 (by rfl) ⟨1902851, by rfl⟩ : syracuseStep 2537135 = 3805703) B3805703
theorem B9631457 : Blo 1690045 9631457 := bstep (se 2 (by rfl) ⟨3611796, by rfl⟩ : syracuseStep 9631457 = 7223593) B7223593
theorem B3610345 : Blo 1690045 3610345 := bstep (se 2 (by rfl) ⟨1353879, by rfl⟩ : syracuseStep 3610345 = 2707759) B2707759
theorem B2537255 : Blo 1690045 2537255 := bstep (se 1 (by rfl) ⟨1902941, by rfl⟩ : syracuseStep 2537255 = 3805883) B3805883
theorem B71317913 : Blo 1690045 71317913 := bstep (se 2 (by rfl) ⟨26744217, by rfl⟩ : syracuseStep 71317913 = 53488435) B53488435
theorem B26376785 : Blo 1690045 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B9632459 : Blo 1690045 9632459 := bstep (se 1 (by rfl) ⟨7224344, by rfl⟩ : syracuseStep 9632459 = 14448689) B14448689
theorem B12844007 : Blo 1690045 12844007 := bstep (se 1 (by rfl) ⟨9633005, by rfl⟩ : syracuseStep 12844007 = 19266011) B19266011
theorem B2407591 : Blo 1690045 2407591 := bstep (se 1 (by rfl) ⟨1805693, by rfl⟩ : syracuseStep 2407591 = 3611387) B3611387
theorem B23772599 : Blo 1690045 23772599 := bstep (se 1 (by rfl) ⟨17829449, by rfl⟩ : syracuseStep 23772599 = 35658899) B35658899
theorem B9764347 : Blo 1690045 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B3210911 : Blo 1690045 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B3612575 : Blo 1690045 3612575 := bstep (se 1 (by rfl) ⟨2709431, by rfl⟩ : syracuseStep 3612575 = 5418863) B5418863
theorem B4571743 : Blo 1690045 4571743 := bstep (se 1 (by rfl) ⟨3428807, by rfl⟩ : syracuseStep 4571743 = 6857615) B6857615
theorem B1901983 : Blo 1690045 1901983 := bstep (se 1 (by rfl) ⟨1426487, by rfl⟩ : syracuseStep 1901983 = 2852975) B2852975
theorem B3802679 : Blo 1690045 3802679 := bstep (se 1 (by rfl) ⟨2852009, by rfl⟩ : syracuseStep 3802679 = 5704019) B5704019
theorem B3802751 : Blo 1690045 3802751 := bstep (se 1 (by rfl) ⟨2852063, by rfl⟩ : syracuseStep 3802751 = 5704127) B5704127
theorem B2852489 : Blo 1690045 2852489 := bstep (se 2 (by rfl) ⟨1069683, by rfl⟩ : syracuseStep 2852489 = 2139367) B2139367
theorem B8562671 : Blo 1690045 8562671 := bstep (se 1 (by rfl) ⟨6422003, by rfl⟩ : syracuseStep 8562671 = 12844007) B12844007
theorem B11569139 : Blo 1690045 11569139 := bstep (se 1 (by rfl) ⟨8676854, by rfl⟩ : syracuseStep 11569139 = 17353709) B17353709
theorem B13019129 : Blo 1690045 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B5704073 : Blo 1690045 5704073 := bstep (se 2 (by rfl) ⟨2139027, by rfl⟩ : syracuseStep 5704073 = 4278055) B4278055
theorem B2140607 : Blo 1690045 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B15428177 : Blo 1690045 15428177 := bstep (se 2 (by rfl) ⟨5785566, by rfl⟩ : syracuseStep 15428177 = 11571133) B11571133
theorem B3803759 : Blo 1690045 3803759 := bstep (se 1 (by rfl) ⟨2852819, by rfl⟩ : syracuseStep 3803759 = 5705639) B5705639
theorem B1690279 : Blo 1690045 1690279 := bstep (se 1 (by rfl) ⟨1267709, by rfl⟩ : syracuseStep 1690279 = 2535419) B2535419
theorem B1690319 : Blo 1690045 1690319 := bstep (se 1 (by rfl) ⟨1267739, by rfl⟩ : syracuseStep 1690319 = 2535479) B2535479
theorem B7318271 : Blo 1690045 7318271 := bstep (se 1 (by rfl) ⟨5488703, by rfl⟩ : syracuseStep 7318271 = 10977407) B10977407
theorem B1690395 : Blo 1690045 1690395 := bstep (se 1 (by rfl) ⟨1267796, by rfl⟩ : syracuseStep 1690395 = 2535593) B2535593
theorem B1690399 : Blo 1690045 1690399 := bstep (se 1 (by rfl) ⟨1267799, by rfl⟩ : syracuseStep 1690399 = 2535599) B2535599
theorem B3803975 : Blo 1690045 3803975 := bstep (se 1 (by rfl) ⟨2852981, by rfl⟩ : syracuseStep 3803975 = 5705963) B5705963
theorem B34704359 : Blo 1690045 34704359 := bstep (se 1 (by rfl) ⟨26028269, by rfl⟩ : syracuseStep 34704359 = 52056539) B52056539
theorem B36555947 : Blo 1690045 36555947 := bstep (se 1 (by rfl) ⟨27416960, by rfl⟩ : syracuseStep 36555947 = 54833921) B54833921
theorem B21130429 : Blo 1690045 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B5418247 : Blo 1690045 5418247 := bstep (se 1 (by rfl) ⟨4063685, by rfl⟩ : syracuseStep 5418247 = 8127371) B8127371
theorem B8916263 : Blo 1690045 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B3804479 : Blo 1690045 3804479 := bstep (se 1 (by rfl) ⟨2853359, by rfl⟩ : syracuseStep 3804479 = 5706719) B5706719
theorem B8678839 : Blo 1690045 8678839 := bstep (se 1 (by rfl) ⟨6509129, by rfl⟩ : syracuseStep 8678839 = 13018259) B13018259
theorem B3804623 : Blo 1690045 3804623 := bstep (se 1 (by rfl) ⟨2853467, by rfl⟩ : syracuseStep 3804623 = 5706935) B5706935
theorem B5705369 : Blo 1690045 5705369 := bstep (se 2 (by rfl) ⟨2139513, by rfl⟩ : syracuseStep 5705369 = 4279027) B4279027
theorem B2535071 : Blo 1690045 2535071 := bstep (se 1 (by rfl) ⟨1901303, by rfl⟩ : syracuseStep 2535071 = 3802607) B3802607
theorem B1691303 : Blo 1690045 1691303 := bstep (se 1 (by rfl) ⟨1268477, by rfl⟩ : syracuseStep 1691303 = 2536955) B2536955
theorem B2707195 : Blo 1690045 2707195 := bstep (se 1 (by rfl) ⟨2030396, by rfl⟩ : syracuseStep 2707195 = 4060793) B4060793
theorem B1691419 : Blo 1690045 1691419 := bstep (se 1 (by rfl) ⟨1268564, by rfl⟩ : syracuseStep 1691419 = 2537129) B2537129
theorem B1691423 : Blo 1690045 1691423 := bstep (se 1 (by rfl) ⟨1268567, by rfl⟩ : syracuseStep 1691423 = 2537135) B2537135
theorem B1691503 : Blo 1690045 1691503 := bstep (se 1 (by rfl) ⟨1268627, by rfl⟩ : syracuseStep 1691503 = 2537255) B2537255
theorem B8122313 : Blo 1690045 8122313 := bstep (se 2 (by rfl) ⟨3045867, by rfl⟩ : syracuseStep 8122313 = 6091735) B6091735
theorem B2535803 : Blo 1690045 2535803 := bstep (se 1 (by rfl) ⟨1901852, by rfl⟩ : syracuseStep 2535803 = 3803705) B3803705
theorem B17584523 : Blo 1690045 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B2535911 : Blo 1690045 2535911 := bstep (se 1 (by rfl) ⟨1901933, by rfl⟩ : syracuseStep 2535911 = 3803867) B3803867
theorem B35664371 : Blo 1690045 35664371 := bstep (se 1 (by rfl) ⟨26748278, by rfl⟩ : syracuseStep 35664371 = 53496557) B53496557
theorem B4813303 : Blo 1690045 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B2536283 : Blo 1690045 2536283 := bstep (se 1 (by rfl) ⟨1902212, by rfl⟩ : syracuseStep 2536283 = 3804425) B3804425
theorem B15848399 : Blo 1690045 15848399 := bstep (se 1 (by rfl) ⟨11886299, by rfl⟩ : syracuseStep 15848399 = 23772599) B23772599
theorem B4813793 : Blo 1690045 4813793 := bstep (se 2 (by rfl) ⟨1805172, by rfl⟩ : syracuseStep 4813793 = 3610345) B3610345
theorem B7320557 : Blo 1690045 7320557 := bstep (se 3 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 7320557 = 2745209) B2745209
theorem B2536775 : Blo 1690045 2536775 := bstep (se 1 (by rfl) ⟨1902581, by rfl⟩ : syracuseStep 2536775 = 3805163) B3805163
theorem B6092111 : Blo 1690045 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B4232807 : Blo 1690045 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B6420455 : Blo 1690045 6420455 := bstep (se 1 (by rfl) ⟨4815341, by rfl⟩ : syracuseStep 6420455 = 9630683) B9630683
theorem B6854759 : Blo 1690045 6854759 := bstep (se 1 (by rfl) ⟨5141069, by rfl⟩ : syracuseStep 6854759 = 10282139) B10282139
theorem B6420971 : Blo 1690045 6420971 := bstep (se 1 (by rfl) ⟨4815728, by rfl⟩ : syracuseStep 6420971 = 9631457) B9631457
theorem B3210121 : Blo 1690045 3210121 := bstep (se 2 (by rfl) ⟨1203795, by rfl⟩ : syracuseStep 3210121 = 2407591) B2407591
theorem B760724405 : Blo 1690045 760724405 := bstep (se 5 (by rfl) ⟨35658956, by rfl⟩ : syracuseStep 760724405 = 71317913) B71317913
theorem B6421639 : Blo 1690045 6421639 := bstep (se 1 (by rfl) ⟨4816229, by rfl⟩ : syracuseStep 6421639 = 9632459) B9632459
theorem B21667499 : Blo 1690045 21667499 := bstep (se 1 (by rfl) ⟨16250624, by rfl⟩ : syracuseStep 21667499 = 32501249) B32501249
theorem B2408383 : Blo 1690045 2408383 := bstep (se 1 (by rfl) ⟨1806287, by rfl⟩ : syracuseStep 2408383 = 3612575) B3612575
theorem B11723015 : Blo 1690045 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B6095657 : Blo 1690045 6095657 := bstep (se 2 (by rfl) ⟨2285871, by rfl⟩ : syracuseStep 6095657 = 4571743) B4571743
theorem B16245629 : Blo 1690045 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B1901659 : Blo 1690045 1901659 := bstep (se 1 (by rfl) ⟨1426244, by rfl⟩ : syracuseStep 1901659 = 2852489) B2852489
theorem B8562185 : Blo 1690045 8562185 := bstep (se 2 (by rfl) ⟨3210819, by rfl⟩ : syracuseStep 8562185 = 6421639) B6421639
theorem B28173905 : Blo 1690045 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B3802715 : Blo 1690045 3802715 := bstep (se 1 (by rfl) ⟨2852036, by rfl⟩ : syracuseStep 3802715 = 5704073) B5704073
theorem B23136239 : Blo 1690045 23136239 := bstep (se 1 (by rfl) ⟨17352179, by rfl⟩ : syracuseStep 23136239 = 34704359) B34704359
theorem B3803579 : Blo 1690045 3803579 := bstep (se 1 (by rfl) ⟨2852684, by rfl⟩ : syracuseStep 3803579 = 5705369) B5705369
theorem B1690047 : Blo 1690045 1690047 := bstep (se 1 (by rfl) ⟨1267535, by rfl⟩ : syracuseStep 1690047 = 2535071) B2535071
theorem B14444999 : Blo 1690045 14444999 := bstep (se 1 (by rfl) ⟨10833749, by rfl⟩ : syracuseStep 14444999 = 21667499) B21667499
theorem B1690535 : Blo 1690045 1690535 := bstep (se 1 (by rfl) ⟨1267901, by rfl⟩ : syracuseStep 1690535 = 2535803) B2535803
theorem B1690607 : Blo 1690045 1690607 := bstep (se 1 (by rfl) ⟨1267955, by rfl⟩ : syracuseStep 1690607 = 2535911) B2535911
theorem B23776247 : Blo 1690045 23776247 := bstep (se 1 (by rfl) ⟨17832185, by rfl⟩ : syracuseStep 23776247 = 35664371) B35664371
theorem B1690855 : Blo 1690045 1690855 := bstep (se 1 (by rfl) ⟨1268141, by rfl⟩ : syracuseStep 1690855 = 2536283) B2536283
theorem B6417737 : Blo 1690045 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B1691183 : Blo 1690045 1691183 := bstep (se 1 (by rfl) ⟨1268387, by rfl⟩ : syracuseStep 1691183 = 2536775) B2536775
theorem B2535119 : Blo 1690045 2535119 := bstep (se 1 (by rfl) ⟨1901339, by rfl⟩ : syracuseStep 2535119 = 3802679) B3802679
theorem B2821871 : Blo 1690045 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B2535167 : Blo 1690045 2535167 := bstep (se 1 (by rfl) ⟨1901375, by rfl⟩ : syracuseStep 2535167 = 3802751) B3802751
theorem B4280161 : Blo 1690045 4280161 := bstep (se 2 (by rfl) ⟨1605060, by rfl⟩ : syracuseStep 4280161 = 3210121) B3210121
theorem B4280303 : Blo 1690045 4280303 := bstep (se 1 (by rfl) ⟨3210227, by rfl⟩ : syracuseStep 4280303 = 6420455) B6420455
theorem B7712759 : Blo 1690045 7712759 := bstep (se 1 (by rfl) ⟨5784569, by rfl⟩ : syracuseStep 7712759 = 11569139) B11569139
theorem B8679419 : Blo 1690045 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B4280647 : Blo 1690045 4280647 := bstep (se 1 (by rfl) ⟨3210485, by rfl⟩ : syracuseStep 4280647 = 6420971) B6420971
theorem B10285451 : Blo 1690045 10285451 := bstep (se 1 (by rfl) ⟨7714088, by rfl⟩ : syracuseStep 10285451 = 15428177) B15428177
theorem B2535839 : Blo 1690045 2535839 := bstep (se 1 (by rfl) ⟨1901879, by rfl⟩ : syracuseStep 2535839 = 3803759) B3803759
theorem B4878847 : Blo 1690045 4878847 := bstep (se 1 (by rfl) ⟨3659135, by rfl⟩ : syracuseStep 4878847 = 7318271) B7318271
theorem B2535977 : Blo 1690045 2535977 := bstep (se 2 (by rfl) ⟨950991, by rfl⟩ : syracuseStep 2535977 = 1901983) B1901983
theorem B2535983 : Blo 1690045 2535983 := bstep (se 1 (by rfl) ⟨1901987, by rfl⟩ : syracuseStep 2535983 = 3803975) B3803975
theorem B11571785 : Blo 1690045 11571785 := bstep (se 2 (by rfl) ⟨4339419, by rfl⟩ : syracuseStep 11571785 = 8678839) B8678839
theorem B5944175 : Blo 1690045 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B2536319 : Blo 1690045 2536319 := bstep (se 1 (by rfl) ⟨1902239, by rfl⟩ : syracuseStep 2536319 = 3804479) B3804479
theorem B2536415 : Blo 1690045 2536415 := bstep (se 1 (by rfl) ⟨1902311, by rfl⟩ : syracuseStep 2536415 = 3804623) B3804623
theorem B3609593 : Blo 1690045 3609593 := bstep (se 2 (by rfl) ⟨1353597, by rfl⟩ : syracuseStep 3609593 = 2707195) B2707195
theorem B10565599 : Blo 1690045 10565599 := bstep (se 1 (by rfl) ⟨7924199, by rfl⟩ : syracuseStep 10565599 = 15848399) B15848399
theorem B3209195 : Blo 1690045 3209195 := bstep (se 1 (by rfl) ⟨2406896, by rfl⟩ : syracuseStep 3209195 = 4813793) B4813793
theorem B4880371 : Blo 1690045 4880371 := bstep (se 1 (by rfl) ⟨3660278, by rfl⟩ : syracuseStep 4880371 = 7320557) B7320557
theorem B5708285 : Blo 1690045 5708285 := bstep (se 3 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 5708285 = 2140607) B2140607
theorem B5708447 : Blo 1690045 5708447 := bstep (se 1 (by rfl) ⟨4281335, by rfl⟩ : syracuseStep 5708447 = 8562671) B8562671
theorem B4569839 : Blo 1690045 4569839 := bstep (se 1 (by rfl) ⟨3427379, by rfl⟩ : syracuseStep 4569839 = 6854759) B6854759
theorem B7224329 : Blo 1690045 7224329 := bstep (se 2 (by rfl) ⟨2709123, by rfl⟩ : syracuseStep 7224329 = 5418247) B5418247
theorem B507149603 : Blo 1690045 507149603 := bstep (se 1 (by rfl) ⟨380362202, by rfl⟩ : syracuseStep 507149603 = 760724405) B760724405
theorem B24370631 : Blo 1690045 24370631 := bstep (se 1 (by rfl) ⟨18277973, by rfl⟩ : syracuseStep 24370631 = 36555947) B36555947
theorem B21659501 : Blo 1690045 21659501 := bstep (se 3 (by rfl) ⟨4061156, by rfl⟩ : syracuseStep 21659501 = 8122313) B8122313
theorem B3211177 : Blo 1690045 3211177 := bstep (se 2 (by rfl) ⟨1204191, by rfl⟩ : syracuseStep 3211177 = 2408383) B2408383
theorem B6856967 : Blo 1690045 6856967 := bstep (se 1 (by rfl) ⟨5142725, by rfl⟩ : syracuseStep 6856967 = 10285451) B10285451
theorem B4063771 : Blo 1690045 4063771 := bstep (se 1 (by rfl) ⟨3047828, by rfl⟩ : syracuseStep 4063771 = 6095657) B6095657
theorem B10830419 : Blo 1690045 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B6505129 : Blo 1690045 6505129 := bstep (se 2 (by rfl) ⟨2439423, by rfl⟩ : syracuseStep 6505129 = 4878847) B4878847
theorem B31261373 : Blo 1690045 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B2139463 : Blo 1690045 2139463 := bstep (se 1 (by rfl) ⟨1604597, by rfl⟩ : syracuseStep 2139463 = 3209195) B3209195
theorem B4278491 : Blo 1690045 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B16247087 : Blo 1690045 16247087 := bstep (se 1 (by rfl) ⟨12185315, by rfl⟩ : syracuseStep 16247087 = 24370631) B24370631
theorem B1690079 : Blo 1690045 1690079 := bstep (se 1 (by rfl) ⟨1267559, by rfl⟩ : syracuseStep 1690079 = 2535119) B2535119
theorem B48744949 : Blo 1690045 48744949 := bstep (se 5 (by rfl) ⟨2284919, by rfl⟩ : syracuseStep 48744949 = 4569839) B4569839
theorem B1690111 : Blo 1690045 1690111 := bstep (se 1 (by rfl) ⟨1267583, by rfl⟩ : syracuseStep 1690111 = 2535167) B2535167
theorem B61696637 : Blo 1690045 61696637 := bstep (se 3 (by rfl) ⟨11568119, by rfl⟩ : syracuseStep 61696637 = 23136239) B23136239
theorem B6507161 : Blo 1690045 6507161 := bstep (se 2 (by rfl) ⟨2440185, by rfl⟩ : syracuseStep 6507161 = 4880371) B4880371
theorem B2853535 : Blo 1690045 2853535 := bstep (se 1 (by rfl) ⟨2140151, by rfl⟩ : syracuseStep 2853535 = 4280303) B4280303
theorem B5786279 : Blo 1690045 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B1690559 : Blo 1690045 1690559 := bstep (se 1 (by rfl) ⟨1267919, by rfl⟩ : syracuseStep 1690559 = 2535839) B2535839
theorem B1690651 : Blo 1690045 1690651 := bstep (se 1 (by rfl) ⟨1267988, by rfl⟩ : syracuseStep 1690651 = 2535977) B2535977
theorem B1690655 : Blo 1690045 1690655 := bstep (se 1 (by rfl) ⟨1267991, by rfl⟩ : syracuseStep 1690655 = 2535983) B2535983
theorem B1690879 : Blo 1690045 1690879 := bstep (se 1 (by rfl) ⟨1268159, by rfl⟩ : syracuseStep 1690879 = 2536319) B2536319
theorem B1690943 : Blo 1690045 1690943 := bstep (se 1 (by rfl) ⟨1268207, by rfl⟩ : syracuseStep 1690943 = 2536415) B2536415
theorem B2535143 : Blo 1690045 2535143 := bstep (se 1 (by rfl) ⟨1901357, by rfl⟩ : syracuseStep 2535143 = 3802715) B3802715
theorem B2535545 : Blo 1690045 2535545 := bstep (se 2 (by rfl) ⟨950829, by rfl⟩ : syracuseStep 2535545 = 1901659) B1901659
theorem B2535719 : Blo 1690045 2535719 := bstep (se 1 (by rfl) ⟨1901789, by rfl⟩ : syracuseStep 2535719 = 3803579) B3803579
theorem B9629999 : Blo 1690045 9629999 := bstep (se 1 (by rfl) ⟨7222499, by rfl⟩ : syracuseStep 9629999 = 14444999) B14444999
theorem B3805523 : Blo 1690045 3805523 := bstep (se 1 (by rfl) ⟨2854142, by rfl⟩ : syracuseStep 3805523 = 5708285) B5708285
theorem B3805631 : Blo 1690045 3805631 := bstep (se 1 (by rfl) ⟨2854223, by rfl⟩ : syracuseStep 3805631 = 5708447) B5708447
theorem B7524989 : Blo 1690045 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B5706881 : Blo 1690045 5706881 := bstep (se 2 (by rfl) ⟨2140080, by rfl⟩ : syracuseStep 5706881 = 4280161) B4280161
theorem B4281569 : Blo 1690045 4281569 := bstep (se 2 (by rfl) ⟨1605588, by rfl⟩ : syracuseStep 4281569 = 3211177) B3211177
theorem B14439667 : Blo 1690045 14439667 := bstep (se 1 (by rfl) ⟨10829750, by rfl⟩ : syracuseStep 14439667 = 21659501) B21659501
theorem B14087465 : Blo 1690045 14087465 := bstep (se 2 (by rfl) ⟨5282799, by rfl⟩ : syracuseStep 14087465 = 10565599) B10565599
theorem B5141839 : Blo 1690045 5141839 := bstep (se 1 (by rfl) ⟨3856379, by rfl⟩ : syracuseStep 5141839 = 7712759) B7712759
theorem B7714523 : Blo 1690045 7714523 := bstep (se 1 (by rfl) ⟨5785892, by rfl⟩ : syracuseStep 7714523 = 11571785) B11571785
theorem B5707529 : Blo 1690045 5707529 := bstep (se 2 (by rfl) ⟨2140323, by rfl⟩ : syracuseStep 5707529 = 4280647) B4280647
theorem B3962783 : Blo 1690045 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B2406395 : Blo 1690045 2406395 := bstep (se 1 (by rfl) ⟨1804796, by rfl⟩ : syracuseStep 2406395 = 3609593) B3609593
theorem B5708123 : Blo 1690045 5708123 := bstep (se 1 (by rfl) ⟨4281092, by rfl⟩ : syracuseStep 5708123 = 8562185) B8562185
theorem B18782603 : Blo 1690045 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B15850831 : Blo 1690045 15850831 := bstep (se 1 (by rfl) ⟨11888123, by rfl⟩ : syracuseStep 15850831 = 23776247) B23776247
theorem B4816219 : Blo 1690045 4816219 := bstep (se 1 (by rfl) ⟨3612164, by rfl⟩ : syracuseStep 4816219 = 7224329) B7224329
theorem B338099735 : Blo 1690045 338099735 := bstep (se 1 (by rfl) ⟨253574801, by rfl⟩ : syracuseStep 338099735 = 507149603) B507149603
theorem B4571311 : Blo 1690045 4571311 := bstep (se 1 (by rfl) ⟨3428483, by rfl⟩ : syracuseStep 4571311 = 6856967) B6856967
theorem B20840915 : Blo 1690045 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B34694021 : Blo 1690045 34694021 := bstep (se 4 (by rfl) ⟨3252564, by rfl⟩ : syracuseStep 34694021 = 6505129) B6505129
theorem B2852327 : Blo 1690045 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B10831391 : Blo 1690045 10831391 := bstep (se 1 (by rfl) ⟨8123543, by rfl⟩ : syracuseStep 10831391 = 16247087) B16247087
theorem B19252889 : Blo 1690045 19252889 := bstep (se 2 (by rfl) ⟨7219833, by rfl⟩ : syracuseStep 19252889 = 14439667) B14439667
theorem B2852617 : Blo 1690045 2852617 := bstep (se 2 (by rfl) ⟨1069731, by rfl⟩ : syracuseStep 2852617 = 2139463) B2139463
theorem B20572061 : Blo 1690045 20572061 := bstep (se 3 (by rfl) ⟨3857261, by rfl⟩ : syracuseStep 20572061 = 7714523) B7714523
theorem B1690095 : Blo 1690045 1690095 := bstep (se 1 (by rfl) ⟨1267571, by rfl⟩ : syracuseStep 1690095 = 2535143) B2535143
theorem B6417053 : Blo 1690045 6417053 := bstep (se 3 (by rfl) ⟨1203197, by rfl⟩ : syracuseStep 6417053 = 2406395) B2406395
theorem B1690363 : Blo 1690045 1690363 := bstep (se 1 (by rfl) ⟨1267772, by rfl⟩ : syracuseStep 1690363 = 2535545) B2535545
theorem B1690479 : Blo 1690045 1690479 := bstep (se 1 (by rfl) ⟨1267859, by rfl⟩ : syracuseStep 1690479 = 2535719) B2535719
theorem B7220279 : Blo 1690045 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B5016659 : Blo 1690045 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B5418361 : Blo 1690045 5418361 := bstep (se 2 (by rfl) ⟨2031885, by rfl⟩ : syracuseStep 5418361 = 4063771) B4063771
theorem B3804587 : Blo 1690045 3804587 := bstep (se 1 (by rfl) ⟨2853440, by rfl⟩ : syracuseStep 3804587 = 5706881) B5706881
theorem B2854379 : Blo 1690045 2854379 := bstep (se 1 (by rfl) ⟨2140784, by rfl⟩ : syracuseStep 2854379 = 4281569) B4281569
theorem B9391643 : Blo 1690045 9391643 := bstep (se 1 (by rfl) ⟨7043732, by rfl⟩ : syracuseStep 9391643 = 14087465) B14087465
theorem B3804713 : Blo 1690045 3804713 := bstep (se 2 (by rfl) ⟨1426767, by rfl⟩ : syracuseStep 3804713 = 2853535) B2853535
theorem B3805019 : Blo 1690045 3805019 := bstep (se 1 (by rfl) ⟨2853764, by rfl⟩ : syracuseStep 3805019 = 5707529) B5707529
theorem B2641855 : Blo 1690045 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B901599293 : Blo 1690045 901599293 := bstep (se 3 (by rfl) ⟨169049867, by rfl⟩ : syracuseStep 901599293 = 338099735) B338099735
theorem B3805415 : Blo 1690045 3805415 := bstep (se 1 (by rfl) ⟨2854061, by rfl⟩ : syracuseStep 3805415 = 5708123) B5708123
theorem B12521735 : Blo 1690045 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B4338107 : Blo 1690045 4338107 := bstep (se 1 (by rfl) ⟨3253580, by rfl⟩ : syracuseStep 4338107 = 6507161) B6507161
theorem B6419999 : Blo 1690045 6419999 := bstep (se 1 (by rfl) ⟨4814999, by rfl⟩ : syracuseStep 6419999 = 9629999) B9629999
theorem B2537015 : Blo 1690045 2537015 := bstep (se 1 (by rfl) ⟨1902761, by rfl⟩ : syracuseStep 2537015 = 3805523) B3805523
theorem B2537087 : Blo 1690045 2537087 := bstep (se 1 (by rfl) ⟨1902815, by rfl⟩ : syracuseStep 2537087 = 3805631) B3805631
theorem B64993265 : Blo 1690045 64993265 := bstep (se 2 (by rfl) ⟨24372474, by rfl⟩ : syracuseStep 64993265 = 48744949) B48744949
theorem B41131091 : Blo 1690045 41131091 := bstep (se 1 (by rfl) ⟨30848318, by rfl⟩ : syracuseStep 41131091 = 61696637) B61696637
theorem B6855785 : Blo 1690045 6855785 := bstep (se 2 (by rfl) ⟨2570919, by rfl⟩ : syracuseStep 6855785 = 5141839) B5141839
theorem B21134441 : Blo 1690045 21134441 := bstep (se 2 (by rfl) ⟨7925415, by rfl⟩ : syracuseStep 21134441 = 15850831) B15850831
theorem B3857519 : Blo 1690045 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B6421625 : Blo 1690045 6421625 := bstep (se 2 (by rfl) ⟨2408109, by rfl⟩ : syracuseStep 6421625 = 4816219) B4816219
theorem B8347823 : Blo 1690045 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B6095081 : Blo 1690045 6095081 := bstep (se 2 (by rfl) ⟨2285655, by rfl⟩ : syracuseStep 6095081 = 4571311) B4571311
theorem B2892071 : Blo 1690045 2892071 := bstep (se 1 (by rfl) ⟨2169053, by rfl⟩ : syracuseStep 2892071 = 4338107) B4338107
theorem B13893943 : Blo 1690045 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B53511029 : Blo 1690045 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B1901551 : Blo 1690045 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B43328843 : Blo 1690045 43328843 := bstep (se 1 (by rfl) ⟨32496632, by rfl⟩ : syracuseStep 43328843 = 64993265) B64993265
theorem B4278035 : Blo 1690045 4278035 := bstep (se 1 (by rfl) ⟨3208526, by rfl⟩ : syracuseStep 4278035 = 6417053) B6417053
theorem B27420727 : Blo 1690045 27420727 := bstep (se 1 (by rfl) ⟨20565545, by rfl⟩ : syracuseStep 27420727 = 41131091) B41131091
theorem B1902919 : Blo 1690045 1902919 := bstep (se 1 (by rfl) ⟨1427189, by rfl⟩ : syracuseStep 1902919 = 2854379) B2854379
theorem B3803489 : Blo 1690045 3803489 := bstep (se 2 (by rfl) ⟨1426308, by rfl⟩ : syracuseStep 3803489 = 2852617) B2852617
theorem B6261095 : Blo 1690045 6261095 := bstep (se 1 (by rfl) ⟨4695821, by rfl⟩ : syracuseStep 6261095 = 9391643) B9391643
theorem B2404264781 : Blo 1690045 2404264781 := bstep (se 3 (by rfl) ⟨450799646, by rfl⟩ : syracuseStep 2404264781 = 901599293) B901599293
theorem B23129347 : Blo 1690045 23129347 := bstep (se 1 (by rfl) ⟨17347010, by rfl⟩ : syracuseStep 23129347 = 34694021) B34694021
theorem B7220927 : Blo 1690045 7220927 := bstep (se 1 (by rfl) ⟨5415695, by rfl⟩ : syracuseStep 7220927 = 10831391) B10831391
theorem B4279999 : Blo 1690045 4279999 := bstep (se 1 (by rfl) ⟨3209999, by rfl⟩ : syracuseStep 4279999 = 6419999) B6419999
theorem B1691343 : Blo 1690045 1691343 := bstep (se 1 (by rfl) ⟨1268507, by rfl⟩ : syracuseStep 1691343 = 2537015) B2537015
theorem B1691391 : Blo 1690045 1691391 := bstep (se 1 (by rfl) ⟨1268543, by rfl⟩ : syracuseStep 1691391 = 2537087) B2537087
theorem B4813519 : Blo 1690045 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B4281083 : Blo 1690045 4281083 := bstep (se 1 (by rfl) ⟨3210812, by rfl⟩ : syracuseStep 4281083 = 6421625) B6421625
theorem B2536391 : Blo 1690045 2536391 := bstep (se 1 (by rfl) ⟨1902293, by rfl⟩ : syracuseStep 2536391 = 3804587) B3804587
theorem B2536475 : Blo 1690045 2536475 := bstep (se 1 (by rfl) ⟨1902356, by rfl⟩ : syracuseStep 2536475 = 3804713) B3804713
theorem B54858829 : Blo 1690045 54858829 := bstep (se 3 (by rfl) ⟨10286030, by rfl⟩ : syracuseStep 54858829 = 20572061) B20572061
theorem B2536679 : Blo 1690045 2536679 := bstep (se 1 (by rfl) ⟨1902509, by rfl⟩ : syracuseStep 2536679 = 3805019) B3805019
theorem B2536943 : Blo 1690045 2536943 := bstep (se 1 (by rfl) ⟨1902707, by rfl⟩ : syracuseStep 2536943 = 3805415) B3805415
theorem B12835259 : Blo 1690045 12835259 := bstep (se 1 (by rfl) ⟨9626444, by rfl⟩ : syracuseStep 12835259 = 19252889) B19252889
theorem B7224481 : Blo 1690045 7224481 := bstep (se 2 (by rfl) ⟨2709180, by rfl⟩ : syracuseStep 7224481 = 5418361) B5418361
theorem B4570523 : Blo 1690045 4570523 := bstep (se 1 (by rfl) ⟨3427892, by rfl⟩ : syracuseStep 4570523 = 6855785) B6855785
theorem B14089627 : Blo 1690045 14089627 := bstep (se 1 (by rfl) ⟨10567220, by rfl⟩ : syracuseStep 14089627 = 21134441) B21134441
theorem B2571679 : Blo 1690045 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B3522473 : Blo 1690045 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B36560969 : Blo 1690045 36560969 := bstep (se 2 (by rfl) ⟨13710363, by rfl⟩ : syracuseStep 36560969 = 27420727) B27420727
theorem B4063387 : Blo 1690045 4063387 := bstep (se 1 (by rfl) ⟨3047540, by rfl⟩ : syracuseStep 4063387 = 6095081) B6095081
theorem B28885895 : Blo 1690045 28885895 := bstep (se 1 (by rfl) ⟨21664421, by rfl⟩ : syracuseStep 28885895 = 43328843) B43328843
theorem B16696253 : Blo 1690045 16696253 := bstep (se 3 (by rfl) ⟨3130547, by rfl⟩ : syracuseStep 16696253 = 6261095) B6261095
theorem B2852023 : Blo 1690045 2852023 := bstep (se 1 (by rfl) ⟨2139017, by rfl⟩ : syracuseStep 2852023 = 4278035) B4278035
theorem B18786169 : Blo 1690045 18786169 := bstep (se 2 (by rfl) ⟨7044813, by rfl⟩ : syracuseStep 18786169 = 14089627) B14089627
theorem B5565215 : Blo 1690045 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B18525257 : Blo 1690045 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B2854055 : Blo 1690045 2854055 := bstep (se 1 (by rfl) ⟨2140541, by rfl⟩ : syracuseStep 2854055 = 4281083) B4281083
theorem B1690927 : Blo 1690045 1690927 := bstep (se 1 (by rfl) ⟨1268195, by rfl⟩ : syracuseStep 1690927 = 2536391) B2536391
theorem B1690983 : Blo 1690045 1690983 := bstep (se 1 (by rfl) ⟨1268237, by rfl⟩ : syracuseStep 1690983 = 2536475) B2536475
theorem B7712189 : Blo 1690045 7712189 := bstep (se 3 (by rfl) ⟨1446035, by rfl⟩ : syracuseStep 7712189 = 2892071) B2892071
theorem B1691119 : Blo 1690045 1691119 := bstep (se 1 (by rfl) ⟨1268339, by rfl⟩ : syracuseStep 1691119 = 2536679) B2536679
theorem B6418025 : Blo 1690045 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B1691295 : Blo 1690045 1691295 := bstep (se 1 (by rfl) ⟨1268471, by rfl⟩ : syracuseStep 1691295 = 2536943) B2536943
theorem B2535401 : Blo 1690045 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B2535659 : Blo 1690045 2535659 := bstep (se 1 (by rfl) ⟨1901744, by rfl⟩ : syracuseStep 2535659 = 3803489) B3803489
theorem B8556839 : Blo 1690045 8556839 := bstep (se 1 (by rfl) ⟨6417629, by rfl⟩ : syracuseStep 8556839 = 12835259) B12835259
theorem B30839129 : Blo 1690045 30839129 := bstep (se 2 (by rfl) ⟨11564673, by rfl⟩ : syracuseStep 30839129 = 23129347) B23129347
theorem B19255805 : Blo 1690045 19255805 := bstep (se 3 (by rfl) ⟨3610463, by rfl⟩ : syracuseStep 19255805 = 7220927) B7220927
theorem B3428905 : Blo 1690045 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B1602843187 : Blo 1690045 1602843187 := bstep (se 1 (by rfl) ⟨1202132390, by rfl⟩ : syracuseStep 1602843187 = 2404264781) B2404264781
theorem B5706665 : Blo 1690045 5706665 := bstep (se 2 (by rfl) ⟨2139999, by rfl⟩ : syracuseStep 5706665 = 4279999) B4279999
theorem B2348315 : Blo 1690045 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B2537225 : Blo 1690045 2537225 := bstep (se 2 (by rfl) ⟨951459, by rfl⟩ : syracuseStep 2537225 = 1902919) B1902919
theorem B35674019 : Blo 1690045 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B73145105 : Blo 1690045 73145105 := bstep (se 2 (by rfl) ⟨27429414, by rfl⟩ : syracuseStep 73145105 = 54858829) B54858829
theorem B9632641 : Blo 1690045 9632641 := bstep (se 2 (by rfl) ⟨3612240, by rfl⟩ : syracuseStep 9632641 = 7224481) B7224481
theorem B3047015 : Blo 1690045 3047015 := bstep (se 1 (by rfl) ⟨2285261, by rfl⟩ : syracuseStep 3047015 = 4570523) B4570523
theorem B12837203 : Blo 1690045 12837203 := bstep (se 1 (by rfl) ⟨9627902, by rfl⟩ : syracuseStep 12837203 = 19255805) B19255805
theorem B4571873 : Blo 1690045 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B23782679 : Blo 1690045 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B3802697 : Blo 1690045 3802697 := bstep (se 2 (by rfl) ⟨1426011, by rfl⟩ : syracuseStep 3802697 = 2852023) B2852023
theorem B1902703 : Blo 1690045 1902703 := bstep (se 1 (by rfl) ⟨1427027, by rfl⟩ : syracuseStep 1902703 = 2854055) B2854055
theorem B4278683 : Blo 1690045 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B1690267 : Blo 1690045 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B24373979 : Blo 1690045 24373979 := bstep (se 1 (by rfl) ⟨18280484, by rfl⟩ : syracuseStep 24373979 = 36560969) B36560969
theorem B1690439 : Blo 1690045 1690439 := bstep (se 1 (by rfl) ⟨1267829, by rfl⟩ : syracuseStep 1690439 = 2535659) B2535659
theorem B5704559 : Blo 1690045 5704559 := bstep (se 1 (by rfl) ⟨4278419, by rfl⟩ : syracuseStep 5704559 = 8556839) B8556839
theorem B5417849 : Blo 1690045 5417849 := bstep (se 2 (by rfl) ⟨2031693, by rfl⟩ : syracuseStep 5417849 = 4063387) B4063387
theorem B3804443 : Blo 1690045 3804443 := bstep (se 1 (by rfl) ⟨2853332, by rfl⟩ : syracuseStep 3804443 = 5706665) B5706665
theorem B2137124249 : Blo 1690045 2137124249 := bstep (se 2 (by rfl) ⟨801421593, by rfl⟩ : syracuseStep 2137124249 = 1602843187) B1602843187
theorem B1691483 : Blo 1690045 1691483 := bstep (se 1 (by rfl) ⟨1268612, by rfl⟩ : syracuseStep 1691483 = 2537225) B2537225
theorem B48763403 : Blo 1690045 48763403 := bstep (se 1 (by rfl) ⟨36572552, by rfl⟩ : syracuseStep 48763403 = 73145105) B73145105
theorem B12350171 : Blo 1690045 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B5141459 : Blo 1690045 5141459 := bstep (se 1 (by rfl) ⟨3856094, by rfl⟩ : syracuseStep 5141459 = 7712189) B7712189
theorem B25048225 : Blo 1690045 25048225 := bstep (se 2 (by rfl) ⟨9393084, by rfl⟩ : syracuseStep 25048225 = 18786169) B18786169
theorem B20559419 : Blo 1690045 20559419 := bstep (se 1 (by rfl) ⟨15419564, by rfl⟩ : syracuseStep 20559419 = 30839129) B30839129
theorem B25048693 : Blo 1690045 25048693 := bstep (se 5 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 25048693 = 2348315) B2348315
theorem B19257263 : Blo 1690045 19257263 := bstep (se 1 (by rfl) ⟨14442947, by rfl⟩ : syracuseStep 19257263 = 28885895) B28885895
theorem B12843521 : Blo 1690045 12843521 := bstep (se 2 (by rfl) ⟨4816320, by rfl⟩ : syracuseStep 12843521 = 9632641) B9632641
theorem B8125373 : Blo 1690045 8125373 := bstep (se 3 (by rfl) ⟨1523507, by rfl⟩ : syracuseStep 8125373 = 3047015) B3047015
theorem B3710143 : Blo 1690045 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B44523341 : Blo 1690045 44523341 := bstep (se 3 (by rfl) ⟨8348126, by rfl⟩ : syracuseStep 44523341 = 16696253) B16696253
theorem B8233447 : Blo 1690045 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B3047915 : Blo 1690045 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B13706279 : Blo 1690045 13706279 := bstep (se 1 (by rfl) ⟨10279709, by rfl⟩ : syracuseStep 13706279 = 20559419) B20559419
theorem B12838175 : Blo 1690045 12838175 := bstep (se 1 (by rfl) ⟨9628631, by rfl⟩ : syracuseStep 12838175 = 19257263) B19257263
theorem B2852455 : Blo 1690045 2852455 := bstep (se 1 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 2852455 = 4278683) B4278683
theorem B8562347 : Blo 1690045 8562347 := bstep (se 1 (by rfl) ⟨6421760, by rfl⟩ : syracuseStep 8562347 = 12843521) B12843521
theorem B3803039 : Blo 1690045 3803039 := bstep (se 1 (by rfl) ⟨2852279, by rfl⟩ : syracuseStep 3803039 = 5704559) B5704559
theorem B5416915 : Blo 1690045 5416915 := bstep (se 1 (by rfl) ⟨4062686, by rfl⟩ : syracuseStep 5416915 = 8125373) B8125373
theorem B29682227 : Blo 1690045 29682227 := bstep (se 1 (by rfl) ⟨22261670, by rfl⟩ : syracuseStep 29682227 = 44523341) B44523341
theorem B32508935 : Blo 1690045 32508935 := bstep (se 1 (by rfl) ⟨24381701, by rfl⟩ : syracuseStep 32508935 = 48763403) B48763403
theorem B3427639 : Blo 1690045 3427639 := bstep (se 1 (by rfl) ⟨2570729, by rfl⟩ : syracuseStep 3427639 = 5141459) B5141459
theorem B15855119 : Blo 1690045 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B19787429 : Blo 1690045 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B2535131 : Blo 1690045 2535131 := bstep (se 1 (by rfl) ⟨1901348, by rfl⟩ : syracuseStep 2535131 = 3802697) B3802697
theorem B16249319 : Blo 1690045 16249319 := bstep (se 1 (by rfl) ⟨12186989, by rfl⟩ : syracuseStep 16249319 = 24373979) B24373979
theorem B2536295 : Blo 1690045 2536295 := bstep (se 1 (by rfl) ⟨1902221, by rfl⟩ : syracuseStep 2536295 = 3804443) B3804443
theorem B1424749499 : Blo 1690045 1424749499 := bstep (se 1 (by rfl) ⟨1068562124, by rfl⟩ : syracuseStep 1424749499 = 2137124249) B2137124249
theorem B2536937 : Blo 1690045 2536937 := bstep (se 2 (by rfl) ⟨951351, by rfl⟩ : syracuseStep 2536937 = 1902703) B1902703
theorem B8558135 : Blo 1690045 8558135 := bstep (se 1 (by rfl) ⟨6418601, by rfl⟩ : syracuseStep 8558135 = 12837203) B12837203
theorem B33397633 : Blo 1690045 33397633 := bstep (se 2 (by rfl) ⟨12524112, by rfl⟩ : syracuseStep 33397633 = 25048225) B25048225
theorem B3611899 : Blo 1690045 3611899 := bstep (se 1 (by rfl) ⟨2708924, by rfl⟩ : syracuseStep 3611899 = 5417849) B5417849
theorem B33398257 : Blo 1690045 33398257 := bstep (se 2 (by rfl) ⟨12524346, by rfl⟩ : syracuseStep 33398257 = 25048693) B25048693
theorem B10977929 : Blo 1690045 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B8127773 : Blo 1690045 8127773 := bstep (se 3 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 8127773 = 3047915) B3047915
theorem B3803273 : Blo 1690045 3803273 := bstep (se 2 (by rfl) ⟨1426227, by rfl⟩ : syracuseStep 3803273 = 2852455) B2852455
theorem B10570079 : Blo 1690045 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B13191619 : Blo 1690045 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B1690087 : Blo 1690045 1690087 := bstep (se 1 (by rfl) ⟨1267565, by rfl⟩ : syracuseStep 1690087 = 2535131) B2535131
theorem B10832879 : Blo 1690045 10832879 := bstep (se 1 (by rfl) ⟨8124659, by rfl⟩ : syracuseStep 10832879 = 16249319) B16249319
theorem B1690863 : Blo 1690045 1690863 := bstep (se 1 (by rfl) ⟨1268147, by rfl⟩ : syracuseStep 1690863 = 2536295) B2536295
theorem B949832999 : Blo 1690045 949832999 := bstep (se 1 (by rfl) ⟨712374749, by rfl⟩ : syracuseStep 949832999 = 1424749499) B1424749499
theorem B9137519 : Blo 1690045 9137519 := bstep (se 1 (by rfl) ⟨6853139, by rfl⟩ : syracuseStep 9137519 = 13706279) B13706279
theorem B1691291 : Blo 1690045 1691291 := bstep (se 1 (by rfl) ⟨1268468, by rfl⟩ : syracuseStep 1691291 = 2536937) B2536937
theorem B5705423 : Blo 1690045 5705423 := bstep (se 1 (by rfl) ⟨4279067, by rfl⟩ : syracuseStep 5705423 = 8558135) B8558135
theorem B2535359 : Blo 1690045 2535359 := bstep (se 1 (by rfl) ⟨1901519, by rfl⟩ : syracuseStep 2535359 = 3803039) B3803039
theorem B18280741 : Blo 1690045 18280741 := bstep (se 4 (by rfl) ⟨1713819, by rfl⟩ : syracuseStep 18280741 = 3427639) B3427639
theorem B19788151 : Blo 1690045 19788151 := bstep (se 1 (by rfl) ⟨14841113, by rfl⟩ : syracuseStep 19788151 = 29682227) B29682227
theorem B21672623 : Blo 1690045 21672623 := bstep (se 1 (by rfl) ⟨16254467, by rfl⟩ : syracuseStep 21672623 = 32508935) B32508935
theorem B7222553 : Blo 1690045 7222553 := bstep (se 2 (by rfl) ⟨2708457, by rfl⟩ : syracuseStep 7222553 = 5416915) B5416915
theorem B8558783 : Blo 1690045 8558783 := bstep (se 1 (by rfl) ⟨6419087, by rfl⟩ : syracuseStep 8558783 = 12838175) B12838175
theorem B5708231 : Blo 1690045 5708231 := bstep (se 1 (by rfl) ⟨4281173, by rfl⟩ : syracuseStep 5708231 = 8562347) B8562347
theorem B44530177 : Blo 1690045 44530177 := bstep (se 2 (by rfl) ⟨16698816, by rfl⟩ : syracuseStep 44530177 = 33397633) B33397633
theorem B4815865 : Blo 1690045 4815865 := bstep (se 2 (by rfl) ⟨1805949, by rfl⟩ : syracuseStep 4815865 = 3611899) B3611899
theorem B44531009 : Blo 1690045 44531009 := bstep (se 2 (by rfl) ⟨16699128, by rfl⟩ : syracuseStep 44531009 = 33398257) B33398257
theorem B17588825 : Blo 1690045 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B7046719 : Blo 1690045 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B3803615 : Blo 1690045 3803615 := bstep (se 1 (by rfl) ⟨2852711, by rfl⟩ : syracuseStep 3803615 = 5705423) B5705423
theorem B1690239 : Blo 1690045 1690239 := bstep (se 1 (by rfl) ⟨1267679, by rfl⟩ : syracuseStep 1690239 = 2535359) B2535359
theorem B24374321 : Blo 1690045 24374321 := bstep (se 2 (by rfl) ⟨9140370, by rfl⟩ : syracuseStep 24374321 = 18280741) B18280741
theorem B7318619 : Blo 1690045 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B5418515 : Blo 1690045 5418515 := bstep (se 1 (by rfl) ⟨4063886, by rfl⟩ : syracuseStep 5418515 = 8127773) B8127773
theorem B2535515 : Blo 1690045 2535515 := bstep (se 1 (by rfl) ⟨1901636, by rfl⟩ : syracuseStep 2535515 = 3803273) B3803273
theorem B5705855 : Blo 1690045 5705855 := bstep (se 1 (by rfl) ⟨4279391, by rfl⟩ : syracuseStep 5705855 = 8558783) B8558783
theorem B3805487 : Blo 1690045 3805487 := bstep (se 1 (by rfl) ⟨2854115, by rfl⟩ : syracuseStep 3805487 = 5708231) B5708231
theorem B7221919 : Blo 1690045 7221919 := bstep (se 1 (by rfl) ⟨5416439, by rfl⟩ : syracuseStep 7221919 = 10832879) B10832879
theorem B633221999 : Blo 1690045 633221999 := bstep (se 1 (by rfl) ⟨474916499, by rfl⟩ : syracuseStep 633221999 = 949832999) B949832999
theorem B6091679 : Blo 1690045 6091679 := bstep (se 1 (by rfl) ⟨4568759, by rfl⟩ : syracuseStep 6091679 = 9137519) B9137519
theorem B14448415 : Blo 1690045 14448415 := bstep (se 1 (by rfl) ⟨10836311, by rfl⟩ : syracuseStep 14448415 = 21672623) B21672623
theorem B26384201 : Blo 1690045 26384201 := bstep (se 2 (by rfl) ⟨9894075, by rfl⟩ : syracuseStep 26384201 = 19788151) B19788151
theorem B59373569 : Blo 1690045 59373569 := bstep (se 2 (by rfl) ⟨22265088, by rfl⟩ : syracuseStep 59373569 = 44530177) B44530177
theorem B4815035 : Blo 1690045 4815035 := bstep (se 1 (by rfl) ⟨3611276, by rfl⟩ : syracuseStep 4815035 = 7222553) B7222553
theorem B6421153 : Blo 1690045 6421153 := bstep (se 2 (by rfl) ⟨2407932, by rfl⟩ : syracuseStep 6421153 = 4815865) B4815865
theorem B29687339 : Blo 1690045 29687339 := bstep (se 1 (by rfl) ⟨22265504, by rfl⟩ : syracuseStep 29687339 = 44531009) B44531009
theorem B8561537 : Blo 1690045 8561537 := bstep (se 2 (by rfl) ⟨3210576, by rfl⟩ : syracuseStep 8561537 = 6421153) B6421153
theorem B17589467 : Blo 1690045 17589467 := bstep (se 1 (by rfl) ⟨13192100, by rfl⟩ : syracuseStep 17589467 = 26384201) B26384201
theorem B1690343 : Blo 1690045 1690343 := bstep (se 1 (by rfl) ⟨1267757, by rfl⟩ : syracuseStep 1690343 = 2535515) B2535515
theorem B3803903 : Blo 1690045 3803903 := bstep (se 1 (by rfl) ⟨2852927, by rfl⟩ : syracuseStep 3803903 = 5705855) B5705855
theorem B11725883 : Blo 1690045 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B9629225 : Blo 1690045 9629225 := bstep (se 2 (by rfl) ⟨3610959, by rfl⟩ : syracuseStep 9629225 = 7221919) B7221919
theorem B2535743 : Blo 1690045 2535743 := bstep (se 1 (by rfl) ⟨1901807, by rfl⟩ : syracuseStep 2535743 = 3803615) B3803615
theorem B16249547 : Blo 1690045 16249547 := bstep (se 1 (by rfl) ⟨12187160, by rfl⟩ : syracuseStep 16249547 = 24374321) B24374321
theorem B4879079 : Blo 1690045 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B19264553 : Blo 1690045 19264553 := bstep (se 2 (by rfl) ⟨7224207, by rfl⟩ : syracuseStep 19264553 = 14448415) B14448415
theorem B2536991 : Blo 1690045 2536991 := bstep (se 1 (by rfl) ⟨1902743, by rfl⟩ : syracuseStep 2536991 = 3805487) B3805487
theorem B37582501 : Blo 1690045 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B422147999 : Blo 1690045 422147999 := bstep (se 1 (by rfl) ⟨316610999, by rfl⟩ : syracuseStep 422147999 = 633221999) B633221999
theorem B4061119 : Blo 1690045 4061119 := bstep (se 1 (by rfl) ⟨3045839, by rfl⟩ : syracuseStep 4061119 = 6091679) B6091679
theorem B39582379 : Blo 1690045 39582379 := bstep (se 1 (by rfl) ⟨29686784, by rfl⟩ : syracuseStep 39582379 = 59373569) B59373569
theorem B14449373 : Blo 1690045 14449373 := bstep (se 3 (by rfl) ⟨2709257, by rfl⟩ : syracuseStep 14449373 = 5418515) B5418515
theorem B3210023 : Blo 1690045 3210023 := bstep (se 1 (by rfl) ⟨2407517, by rfl⟩ : syracuseStep 3210023 = 4815035) B4815035
theorem B19791559 : Blo 1690045 19791559 := bstep (se 1 (by rfl) ⟨14843669, by rfl⟩ : syracuseStep 19791559 = 29687339) B29687339
theorem B3252719 : Blo 1690045 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B105554981 : Blo 1690045 105554981 := bstep (se 4 (by rfl) ⟨9895779, by rfl⟩ : syracuseStep 105554981 = 19791559) B19791559
theorem B2140015 : Blo 1690045 2140015 := bstep (se 1 (by rfl) ⟨1605011, by rfl⟩ : syracuseStep 2140015 = 3210023) B3210023
theorem B7817255 : Blo 1690045 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B1690495 : Blo 1690045 1690495 := bstep (se 1 (by rfl) ⟨1267871, by rfl⟩ : syracuseStep 1690495 = 2535743) B2535743
theorem B10833031 : Blo 1690045 10833031 := bstep (se 1 (by rfl) ⟨8124773, by rfl⟩ : syracuseStep 10833031 = 16249547) B16249547
theorem B11726311 : Blo 1690045 11726311 := bstep (se 1 (by rfl) ⟨8794733, by rfl⟩ : syracuseStep 11726311 = 17589467) B17589467
theorem B52776505 : Blo 1690045 52776505 := bstep (se 2 (by rfl) ⟨19791189, by rfl⟩ : syracuseStep 52776505 = 39582379) B39582379
theorem B1691327 : Blo 1690045 1691327 := bstep (se 1 (by rfl) ⟨1268495, by rfl⟩ : syracuseStep 1691327 = 2536991) B2536991
theorem B281431999 : Blo 1690045 281431999 := bstep (se 1 (by rfl) ⟨211073999, by rfl⟩ : syracuseStep 281431999 = 422147999) B422147999
theorem B2535935 : Blo 1690045 2535935 := bstep (se 1 (by rfl) ⟨1901951, by rfl⟩ : syracuseStep 2535935 = 3803903) B3803903
theorem B6419483 : Blo 1690045 6419483 := bstep (se 1 (by rfl) ⟨4814612, by rfl⟩ : syracuseStep 6419483 = 9629225) B9629225
theorem B5707691 : Blo 1690045 5707691 := bstep (se 1 (by rfl) ⟨4280768, by rfl⟩ : syracuseStep 5707691 = 8561537) B8561537
theorem B12843035 : Blo 1690045 12843035 := bstep (se 1 (by rfl) ⟨9632276, by rfl⟩ : syracuseStep 12843035 = 19264553) B19264553
theorem B9632915 : Blo 1690045 9632915 := bstep (se 1 (by rfl) ⟨7224686, by rfl⟩ : syracuseStep 9632915 = 14449373) B14449373
theorem B50110001 : Blo 1690045 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B5414825 : Blo 1690045 5414825 := bstep (se 2 (by rfl) ⟨2030559, by rfl⟩ : syracuseStep 5414825 = 4061119) B4061119
theorem B70369987 : Blo 1690045 70369987 := bstep (se 1 (by rfl) ⟨52777490, by rfl⟩ : syracuseStep 70369987 = 105554981) B105554981
theorem B8562023 : Blo 1690045 8562023 := bstep (se 1 (by rfl) ⟨6421517, by rfl⟩ : syracuseStep 8562023 = 12843035) B12843035
theorem B5211503 : Blo 1690045 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B14444041 : Blo 1690045 14444041 := bstep (se 2 (by rfl) ⟨5416515, by rfl⟩ : syracuseStep 14444041 = 10833031) B10833031
theorem B2853353 : Blo 1690045 2853353 := bstep (se 2 (by rfl) ⟨1070007, by rfl⟩ : syracuseStep 2853353 = 2140015) B2140015
theorem B1690623 : Blo 1690045 1690623 := bstep (se 1 (by rfl) ⟨1267967, by rfl⟩ : syracuseStep 1690623 = 2535935) B2535935
theorem B4279655 : Blo 1690045 4279655 := bstep (se 1 (by rfl) ⟨3209741, by rfl⟩ : syracuseStep 4279655 = 6419483) B6419483
theorem B3805127 : Blo 1690045 3805127 := bstep (se 1 (by rfl) ⟨2853845, by rfl⟩ : syracuseStep 3805127 = 5707691) B5707691
theorem B15635081 : Blo 1690045 15635081 := bstep (se 2 (by rfl) ⟨5863155, by rfl⟩ : syracuseStep 15635081 = 11726311) B11726311
theorem B3609883 : Blo 1690045 3609883 := bstep (se 1 (by rfl) ⟨2707412, by rfl⟩ : syracuseStep 3609883 = 5414825) B5414825
theorem B2168479 : Blo 1690045 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B70368673 : Blo 1690045 70368673 := bstep (se 2 (by rfl) ⟨26388252, by rfl⟩ : syracuseStep 70368673 = 52776505) B52776505
theorem B6421943 : Blo 1690045 6421943 := bstep (se 1 (by rfl) ⟨4816457, by rfl⟩ : syracuseStep 6421943 = 9632915) B9632915
theorem B33406667 : Blo 1690045 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B375242665 : Blo 1690045 375242665 := bstep (se 2 (by rfl) ⟨140715999, by rfl⟩ : syracuseStep 375242665 = 281431999) B281431999
theorem B3474335 : Blo 1690045 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B1902235 : Blo 1690045 1902235 := bstep (se 1 (by rfl) ⟨1426676, by rfl⟩ : syracuseStep 1902235 = 2853353) B2853353
theorem B93824897 : Blo 1690045 93824897 := bstep (se 2 (by rfl) ⟨35184336, by rfl⟩ : syracuseStep 93824897 = 70368673) B70368673
theorem B2853103 : Blo 1690045 2853103 := bstep (se 1 (by rfl) ⟨2139827, by rfl⟩ : syracuseStep 2853103 = 4279655) B4279655
theorem B93826649 : Blo 1690045 93826649 := bstep (se 2 (by rfl) ⟨35184993, by rfl⟩ : syracuseStep 93826649 = 70369987) B70369987
theorem B41693549 : Blo 1690045 41693549 := bstep (se 3 (by rfl) ⟨7817540, by rfl⟩ : syracuseStep 41693549 = 15635081) B15635081
theorem B4813177 : Blo 1690045 4813177 := bstep (se 2 (by rfl) ⟨1804941, by rfl⟩ : syracuseStep 4813177 = 3609883) B3609883
theorem B4281295 : Blo 1690045 4281295 := bstep (se 1 (by rfl) ⟨3210971, by rfl⟩ : syracuseStep 4281295 = 6421943) B6421943
theorem B22271111 : Blo 1690045 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B500323553 : Blo 1690045 500323553 := bstep (se 2 (by rfl) ⟨187621332, by rfl⟩ : syracuseStep 500323553 = 375242665) B375242665
theorem B2536751 : Blo 1690045 2536751 := bstep (se 1 (by rfl) ⟨1902563, by rfl⟩ : syracuseStep 2536751 = 3805127) B3805127
theorem B5708015 : Blo 1690045 5708015 := bstep (se 1 (by rfl) ⟨4281011, by rfl⟩ : syracuseStep 5708015 = 8562023) B8562023
theorem B19258721 : Blo 1690045 19258721 := bstep (se 2 (by rfl) ⟨7222020, by rfl⟩ : syracuseStep 19258721 = 14444041) B14444041
theorem B2891305 : Blo 1690045 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B111182797 : Blo 1690045 111182797 := bstep (se 3 (by rfl) ⟨20846774, by rfl⟩ : syracuseStep 111182797 = 41693549) B41693549
theorem B12839147 : Blo 1690045 12839147 := bstep (se 1 (by rfl) ⟨9629360, by rfl⟩ : syracuseStep 12839147 = 19258721) B19258721
theorem B15420293 : Blo 1690045 15420293 := bstep (se 4 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 15420293 = 2891305) B2891305
theorem B3804137 : Blo 1690045 3804137 := bstep (se 2 (by rfl) ⟨1426551, by rfl⟩ : syracuseStep 3804137 = 2853103) B2853103
theorem B6417569 : Blo 1690045 6417569 := bstep (se 2 (by rfl) ⟨2406588, by rfl⟩ : syracuseStep 6417569 = 4813177) B4813177
theorem B14847407 : Blo 1690045 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B333549035 : Blo 1690045 333549035 := bstep (se 1 (by rfl) ⟨250161776, by rfl⟩ : syracuseStep 333549035 = 500323553) B500323553
theorem B1691167 : Blo 1690045 1691167 := bstep (se 1 (by rfl) ⟨1268375, by rfl⟩ : syracuseStep 1691167 = 2536751) B2536751
theorem B3805343 : Blo 1690045 3805343 := bstep (se 1 (by rfl) ⟨2854007, by rfl⟩ : syracuseStep 3805343 = 5708015) B5708015
theorem B2536313 : Blo 1690045 2536313 := bstep (se 2 (by rfl) ⟨951117, by rfl⟩ : syracuseStep 2536313 = 1902235) B1902235
theorem B62551099 : Blo 1690045 62551099 := bstep (se 1 (by rfl) ⟨46913324, by rfl⟩ : syracuseStep 62551099 = 93826649) B93826649
theorem B2316223 : Blo 1690045 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B5708393 : Blo 1690045 5708393 := bstep (se 2 (by rfl) ⟨2140647, by rfl⟩ : syracuseStep 5708393 = 4281295) B4281295
theorem B1000798901 : Blo 1690045 1000798901 := bstep (se 5 (by rfl) ⟨46912448, by rfl⟩ : syracuseStep 1000798901 = 93824897) B93824897
theorem B148243729 : Blo 1690045 148243729 := bstep (se 2 (by rfl) ⟨55591398, by rfl⟩ : syracuseStep 148243729 = 111182797) B111182797
theorem B667199267 : Blo 1690045 667199267 := bstep (se 1 (by rfl) ⟨500399450, by rfl⟩ : syracuseStep 667199267 = 1000798901) B1000798901
theorem B4278379 : Blo 1690045 4278379 := bstep (se 1 (by rfl) ⟨3208784, by rfl⟩ : syracuseStep 4278379 = 6417569) B6417569
theorem B9898271 : Blo 1690045 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B222366023 : Blo 1690045 222366023 := bstep (se 1 (by rfl) ⟨166774517, by rfl⟩ : syracuseStep 222366023 = 333549035) B333549035
theorem B333605861 : Blo 1690045 333605861 := bstep (se 4 (by rfl) ⟨31275549, by rfl⟩ : syracuseStep 333605861 = 62551099) B62551099
theorem B1690875 : Blo 1690045 1690875 := bstep (se 1 (by rfl) ⟨1268156, by rfl⟩ : syracuseStep 1690875 = 2536313) B2536313
theorem B3805595 : Blo 1690045 3805595 := bstep (se 1 (by rfl) ⟨2854196, by rfl⟩ : syracuseStep 3805595 = 5708393) B5708393
theorem B2536091 : Blo 1690045 2536091 := bstep (se 1 (by rfl) ⟨1902068, by rfl⟩ : syracuseStep 2536091 = 3804137) B3804137
theorem B2536895 : Blo 1690045 2536895 := bstep (se 1 (by rfl) ⟨1902671, by rfl⟩ : syracuseStep 2536895 = 3805343) B3805343
theorem B8559431 : Blo 1690045 8559431 := bstep (se 1 (by rfl) ⟨6419573, by rfl⟩ : syracuseStep 8559431 = 12839147) B12839147
theorem B10280195 : Blo 1690045 10280195 := bstep (se 1 (by rfl) ⟨7710146, by rfl⟩ : syracuseStep 10280195 = 15420293) B15420293
theorem B3088297 : Blo 1690045 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B148244015 : Blo 1690045 148244015 := bstep (se 1 (by rfl) ⟨111183011, by rfl⟩ : syracuseStep 148244015 = 222366023) B222366023
theorem B197658305 : Blo 1690045 197658305 := bstep (se 2 (by rfl) ⟨74121864, by rfl⟩ : syracuseStep 197658305 = 148243729) B148243729
theorem B5704505 : Blo 1690045 5704505 := bstep (se 2 (by rfl) ⟨2139189, by rfl⟩ : syracuseStep 5704505 = 4278379) B4278379
theorem B1690727 : Blo 1690045 1690727 := bstep (se 1 (by rfl) ⟨1268045, by rfl⟩ : syracuseStep 1690727 = 2536091) B2536091
theorem B1691263 : Blo 1690045 1691263 := bstep (se 1 (by rfl) ⟨1268447, by rfl⟩ : syracuseStep 1691263 = 2536895) B2536895
theorem B6598847 : Blo 1690045 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B5706287 : Blo 1690045 5706287 := bstep (se 1 (by rfl) ⟨4279715, by rfl⟩ : syracuseStep 5706287 = 8559431) B8559431
theorem B6853463 : Blo 1690045 6853463 := bstep (se 1 (by rfl) ⟨5140097, by rfl⟩ : syracuseStep 6853463 = 10280195) B10280195
theorem B4117729 : Blo 1690045 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B2537063 : Blo 1690045 2537063 := bstep (se 1 (by rfl) ⟨1902797, by rfl⟩ : syracuseStep 2537063 = 3805595) B3805595
theorem B444799511 : Blo 1690045 444799511 := bstep (se 1 (by rfl) ⟨333599633, by rfl⟩ : syracuseStep 444799511 = 667199267) B667199267
theorem B222403907 : Blo 1690045 222403907 := bstep (se 1 (by rfl) ⟨166802930, by rfl⟩ : syracuseStep 222403907 = 333605861) B333605861
theorem B4399231 : Blo 1690045 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B593077085 : Blo 1690045 593077085 := bstep (se 3 (by rfl) ⟨111201953, by rfl⟩ : syracuseStep 593077085 = 222403907) B222403907
theorem B98829343 : Blo 1690045 98829343 := bstep (se 1 (by rfl) ⟨74122007, by rfl⟩ : syracuseStep 98829343 = 148244015) B148244015
theorem B5490305 : Blo 1690045 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B3803003 : Blo 1690045 3803003 := bstep (se 1 (by rfl) ⟨2852252, by rfl⟩ : syracuseStep 3803003 = 5704505) B5704505
theorem B3804191 : Blo 1690045 3804191 := bstep (se 1 (by rfl) ⟨2853143, by rfl⟩ : syracuseStep 3804191 = 5706287) B5706287
theorem B1691375 : Blo 1690045 1691375 := bstep (se 1 (by rfl) ⟨1268531, by rfl⟩ : syracuseStep 1691375 = 2537063) B2537063
theorem B131772203 : Blo 1690045 131772203 := bstep (se 1 (by rfl) ⟨98829152, by rfl⟩ : syracuseStep 131772203 = 197658305) B197658305
theorem B4568975 : Blo 1690045 4568975 := bstep (se 1 (by rfl) ⟨3426731, by rfl⟩ : syracuseStep 4568975 = 6853463) B6853463
theorem B296533007 : Blo 1690045 296533007 := bstep (se 1 (by rfl) ⟨222399755, by rfl⟩ : syracuseStep 296533007 = 444799511) B444799511
theorem B5865641 : Blo 1690045 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B2535335 : Blo 1690045 2535335 := bstep (se 1 (by rfl) ⟨1901501, by rfl⟩ : syracuseStep 2535335 = 3803003) B3803003
theorem B131772457 : Blo 1690045 131772457 := bstep (se 2 (by rfl) ⟨49414671, by rfl⟩ : syracuseStep 131772457 = 98829343) B98829343
theorem B2536127 : Blo 1690045 2536127 := bstep (se 1 (by rfl) ⟨1902095, by rfl⟩ : syracuseStep 2536127 = 3804191) B3804191
theorem B87848135 : Blo 1690045 87848135 := bstep (se 1 (by rfl) ⟨65886101, by rfl⟩ : syracuseStep 87848135 = 131772203) B131772203
theorem B395384723 : Blo 1690045 395384723 := bstep (se 1 (by rfl) ⟨296538542, by rfl⟩ : syracuseStep 395384723 = 593077085) B593077085
theorem B3660203 : Blo 1690045 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B3045983 : Blo 1690045 3045983 := bstep (se 1 (by rfl) ⟨2284487, by rfl⟩ : syracuseStep 3045983 = 4568975) B4568975
theorem B197688671 : Blo 1690045 197688671 := bstep (se 1 (by rfl) ⟨148266503, by rfl⟩ : syracuseStep 197688671 = 296533007) B296533007
theorem B58565423 : Blo 1690045 58565423 := bstep (se 1 (by rfl) ⟨43924067, by rfl⟩ : syracuseStep 58565423 = 87848135) B87848135
theorem B1690223 : Blo 1690045 1690223 := bstep (se 1 (by rfl) ⟨1267667, by rfl⟩ : syracuseStep 1690223 = 2535335) B2535335
theorem B175696609 : Blo 1690045 175696609 := bstep (se 2 (by rfl) ⟨65886228, by rfl⟩ : syracuseStep 175696609 = 131772457) B131772457
theorem B3910427 : Blo 1690045 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B1690751 : Blo 1690045 1690751 := bstep (se 1 (by rfl) ⟨1268063, by rfl⟩ : syracuseStep 1690751 = 2536127) B2536127
theorem B263589815 : Blo 1690045 263589815 := bstep (se 1 (by rfl) ⟨197692361, by rfl⟩ : syracuseStep 263589815 = 395384723) B395384723
theorem B8122621 : Blo 1690045 8122621 := bstep (se 3 (by rfl) ⟨1522991, by rfl⟩ : syracuseStep 8122621 = 3045983) B3045983
theorem B2440135 : Blo 1690045 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B131792447 : Blo 1690045 131792447 := bstep (se 1 (by rfl) ⟨98844335, by rfl⟩ : syracuseStep 131792447 = 197688671) B197688671
theorem B10830161 : Blo 1690045 10830161 := bstep (se 2 (by rfl) ⟨4061310, by rfl⟩ : syracuseStep 10830161 = 8122621) B8122621
theorem B39043615 : Blo 1690045 39043615 := bstep (se 1 (by rfl) ⟨29282711, by rfl⟩ : syracuseStep 39043615 = 58565423) B58565423
theorem B2606951 : Blo 1690045 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B87861631 : Blo 1690045 87861631 := bstep (se 1 (by rfl) ⟨65896223, by rfl⟩ : syracuseStep 87861631 = 131792447) B131792447
theorem B234262145 : Blo 1690045 234262145 := bstep (se 2 (by rfl) ⟨87848304, by rfl⟩ : syracuseStep 234262145 = 175696609) B175696609
theorem B13014053 : Blo 1690045 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B175726543 : Blo 1690045 175726543 := bstep (se 1 (by rfl) ⟨131794907, by rfl⟩ : syracuseStep 175726543 = 263589815) B263589815
theorem B8676035 : Blo 1690045 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B1737967 : Blo 1690045 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B624699053 : Blo 1690045 624699053 := bstep (se 3 (by rfl) ⟨117131072, by rfl⟩ : syracuseStep 624699053 = 234262145) B234262145
theorem B234302057 : Blo 1690045 234302057 := bstep (se 2 (by rfl) ⟨87863271, by rfl⟩ : syracuseStep 234302057 = 175726543) B175726543
theorem B7220107 : Blo 1690045 7220107 := bstep (se 1 (by rfl) ⟨5415080, by rfl⟩ : syracuseStep 7220107 = 10830161) B10830161
theorem B117148841 : Blo 1690045 117148841 := bstep (se 2 (by rfl) ⟨43930815, by rfl⟩ : syracuseStep 117148841 = 87861631) B87861631
theorem B52058153 : Blo 1690045 52058153 := bstep (se 2 (by rfl) ⟨19521807, by rfl⟩ : syracuseStep 52058153 = 39043615) B39043615
theorem B5784023 : Blo 1690045 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B416466035 : Blo 1690045 416466035 := bstep (se 1 (by rfl) ⟨312349526, by rfl⟩ : syracuseStep 416466035 = 624699053) B624699053
theorem B9626809 : Blo 1690045 9626809 := bstep (se 2 (by rfl) ⟨3610053, by rfl⟩ : syracuseStep 9626809 = 7220107) B7220107
theorem B34705435 : Blo 1690045 34705435 := bstep (se 1 (by rfl) ⟨26029076, by rfl⟩ : syracuseStep 34705435 = 52058153) B52058153
theorem B156201371 : Blo 1690045 156201371 := bstep (se 1 (by rfl) ⟨117151028, by rfl⟩ : syracuseStep 156201371 = 234302057) B234302057
theorem B78099227 : Blo 1690045 78099227 := bstep (se 1 (by rfl) ⟨58574420, by rfl⟩ : syracuseStep 78099227 = 117148841) B117148841
theorem B2317289 : Blo 1690045 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B277644023 : Blo 1690045 277644023 := bstep (se 1 (by rfl) ⟨208233017, by rfl⟩ : syracuseStep 277644023 = 416466035) B416466035
theorem B6179437 : Blo 1690045 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B46273913 : Blo 1690045 46273913 := bstep (se 2 (by rfl) ⟨17352717, by rfl⟩ : syracuseStep 46273913 = 34705435) B34705435
theorem B104134247 : Blo 1690045 104134247 := bstep (se 1 (by rfl) ⟨78100685, by rfl⟩ : syracuseStep 104134247 = 156201371) B156201371
theorem B3856015 : Blo 1690045 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B52066151 : Blo 1690045 52066151 := bstep (se 1 (by rfl) ⟨39049613, by rfl⟩ : syracuseStep 52066151 = 78099227) B78099227
theorem B12835745 : Blo 1690045 12835745 := bstep (se 2 (by rfl) ⟨4813404, by rfl⟩ : syracuseStep 12835745 = 9626809) B9626809
theorem B34710767 : Blo 1690045 34710767 := bstep (se 1 (by rfl) ⟨26033075, by rfl⟩ : syracuseStep 34710767 = 52066151) B52066151
theorem B69422831 : Blo 1690045 69422831 := bstep (se 1 (by rfl) ⟨52067123, by rfl⟩ : syracuseStep 69422831 = 104134247) B104134247
theorem B8557163 : Blo 1690045 8557163 := bstep (se 1 (by rfl) ⟨6417872, by rfl⟩ : syracuseStep 8557163 = 12835745) B12835745
theorem B5141353 : Blo 1690045 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B185096015 : Blo 1690045 185096015 := bstep (se 1 (by rfl) ⟨138822011, by rfl⟩ : syracuseStep 185096015 = 277644023) B277644023
theorem B8239249 : Blo 1690045 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B30849275 : Blo 1690045 30849275 := bstep (se 1 (by rfl) ⟨23136956, by rfl⟩ : syracuseStep 30849275 = 46273913) B46273913
theorem B43942661 : Blo 1690045 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B123397343 : Blo 1690045 123397343 := bstep (se 1 (by rfl) ⟨92548007, by rfl⟩ : syracuseStep 123397343 = 185096015) B185096015
theorem B5704775 : Blo 1690045 5704775 := bstep (se 1 (by rfl) ⟨4278581, by rfl⟩ : syracuseStep 5704775 = 8557163) B8557163
theorem B20566183 : Blo 1690045 20566183 := bstep (se 1 (by rfl) ⟨15424637, by rfl⟩ : syracuseStep 20566183 = 30849275) B30849275
theorem B46281887 : Blo 1690045 46281887 := bstep (se 1 (by rfl) ⟨34711415, by rfl⟩ : syracuseStep 46281887 = 69422831) B69422831
theorem B23140511 : Blo 1690045 23140511 := bstep (se 1 (by rfl) ⟨17355383, by rfl⟩ : syracuseStep 23140511 = 34710767) B34710767
theorem B6855137 : Blo 1690045 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B29295107 : Blo 1690045 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B82264895 : Blo 1690045 82264895 := bstep (se 1 (by rfl) ⟨61698671, by rfl⟩ : syracuseStep 82264895 = 123397343) B123397343
theorem B15427007 : Blo 1690045 15427007 := bstep (se 1 (by rfl) ⟨11570255, by rfl⟩ : syracuseStep 15427007 = 23140511) B23140511
theorem B3803183 : Blo 1690045 3803183 := bstep (se 1 (by rfl) ⟨2852387, by rfl⟩ : syracuseStep 3803183 = 5704775) B5704775
theorem B27421577 : Blo 1690045 27421577 := bstep (se 2 (by rfl) ⟨10283091, by rfl⟩ : syracuseStep 27421577 = 20566183) B20566183
theorem B30854591 : Blo 1690045 30854591 := bstep (se 1 (by rfl) ⟨23140943, by rfl⟩ : syracuseStep 30854591 = 46281887) B46281887
theorem B4570091 : Blo 1690045 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B19530071 : Blo 1690045 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B10284671 : Blo 1690045 10284671 := bstep (se 1 (by rfl) ⟨7713503, by rfl⟩ : syracuseStep 10284671 = 15427007) B15427007
theorem B2535455 : Blo 1690045 2535455 := bstep (se 1 (by rfl) ⟨1901591, by rfl⟩ : syracuseStep 2535455 = 3803183) B3803183
theorem B18281051 : Blo 1690045 18281051 := bstep (se 1 (by rfl) ⟨13710788, by rfl⟩ : syracuseStep 18281051 = 27421577) B27421577
theorem B54843263 : Blo 1690045 54843263 := bstep (se 1 (by rfl) ⟨41132447, by rfl⟩ : syracuseStep 54843263 = 82264895) B82264895
theorem B3046727 : Blo 1690045 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B20569727 : Blo 1690045 20569727 := bstep (se 1 (by rfl) ⟨15427295, by rfl⟩ : syracuseStep 20569727 = 30854591) B30854591
theorem B36562175 : Blo 1690045 36562175 := bstep (se 1 (by rfl) ⟨27421631, by rfl⟩ : syracuseStep 36562175 = 54843263) B54843263
theorem B1690303 : Blo 1690045 1690303 := bstep (se 1 (by rfl) ⟨1267727, by rfl⟩ : syracuseStep 1690303 = 2535455) B2535455
theorem B13020047 : Blo 1690045 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B12187367 : Blo 1690045 12187367 := bstep (se 1 (by rfl) ⟨9140525, by rfl⟩ : syracuseStep 12187367 = 18281051) B18281051
theorem B2031151 : Blo 1690045 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B6856447 : Blo 1690045 6856447 := bstep (se 1 (by rfl) ⟨5142335, by rfl⟩ : syracuseStep 6856447 = 10284671) B10284671
theorem B13713151 : Blo 1690045 13713151 := bstep (se 1 (by rfl) ⟨10284863, by rfl⟩ : syracuseStep 13713151 = 20569727) B20569727
theorem B24374783 : Blo 1690045 24374783 := bstep (se 1 (by rfl) ⟨18281087, by rfl⟩ : syracuseStep 24374783 = 36562175) B36562175
theorem B8680031 : Blo 1690045 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B2708201 : Blo 1690045 2708201 := bstep (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) B2031151
theorem B8124911 : Blo 1690045 8124911 := bstep (se 1 (by rfl) ⟨6093683, by rfl⟩ : syracuseStep 8124911 = 12187367) B12187367
theorem B9141929 : Blo 1690045 9141929 := bstep (se 2 (by rfl) ⟨3428223, by rfl⟩ : syracuseStep 9141929 = 6856447) B6856447
theorem B18284201 : Blo 1690045 18284201 := bstep (se 2 (by rfl) ⟨6856575, by rfl⟩ : syracuseStep 18284201 = 13713151) B13713151
theorem B5416607 : Blo 1690045 5416607 := bstep (se 1 (by rfl) ⟨4062455, by rfl⟩ : syracuseStep 5416607 = 8124911) B8124911
theorem B5786687 : Blo 1690045 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B7221869 : Blo 1690045 7221869 := bstep (se 3 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 7221869 = 2708201) B2708201
theorem B16249855 : Blo 1690045 16249855 := bstep (se 1 (by rfl) ⟨12187391, by rfl⟩ : syracuseStep 16249855 = 24374783) B24374783
theorem B6094619 : Blo 1690045 6094619 := bstep (se 1 (by rfl) ⟨4570964, by rfl⟩ : syracuseStep 6094619 = 9141929) B9141929
theorem B12189467 : Blo 1690045 12189467 := bstep (se 1 (by rfl) ⟨9142100, by rfl⟩ : syracuseStep 12189467 = 18284201) B18284201
theorem B15431165 : Blo 1690045 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B4814579 : Blo 1690045 4814579 := bstep (se 1 (by rfl) ⟨3610934, by rfl⟩ : syracuseStep 4814579 = 7221869) B7221869
theorem B3611071 : Blo 1690045 3611071 := bstep (se 1 (by rfl) ⟨2708303, by rfl⟩ : syracuseStep 3611071 = 5416607) B5416607
theorem B21666473 : Blo 1690045 21666473 := bstep (se 2 (by rfl) ⟨8124927, by rfl⟩ : syracuseStep 21666473 = 16249855) B16249855
theorem B32505245 : Blo 1690045 32505245 := bstep (se 3 (by rfl) ⟨6094733, by rfl⟩ : syracuseStep 32505245 = 12189467) B12189467
theorem B4063079 : Blo 1690045 4063079 := bstep (se 1 (by rfl) ⟨3047309, by rfl⟩ : syracuseStep 4063079 = 6094619) B6094619
theorem B14444315 : Blo 1690045 14444315 := bstep (se 1 (by rfl) ⟨10833236, by rfl⟩ : syracuseStep 14444315 = 21666473) B21666473
theorem B21670163 : Blo 1690045 21670163 := bstep (se 1 (by rfl) ⟨16252622, by rfl⟩ : syracuseStep 21670163 = 32505245) B32505245
theorem B10834877 : Blo 1690045 10834877 := bstep (se 3 (by rfl) ⟨2031539, by rfl⟩ : syracuseStep 10834877 = 4063079) B4063079
theorem B4814761 : Blo 1690045 4814761 := bstep (se 2 (by rfl) ⟨1805535, by rfl⟩ : syracuseStep 4814761 = 3611071) B3611071
theorem B10287443 : Blo 1690045 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B3209719 : Blo 1690045 3209719 := bstep (se 1 (by rfl) ⟨2407289, by rfl⟩ : syracuseStep 3209719 = 4814579) B4814579
theorem B4279625 : Blo 1690045 4279625 := bstep (se 2 (by rfl) ⟨1604859, by rfl⟩ : syracuseStep 4279625 = 3209719) B3209719
theorem B9629543 : Blo 1690045 9629543 := bstep (se 1 (by rfl) ⟨7222157, by rfl⟩ : syracuseStep 9629543 = 14444315) B14444315
theorem B14446775 : Blo 1690045 14446775 := bstep (se 1 (by rfl) ⟨10835081, by rfl⟩ : syracuseStep 14446775 = 21670163) B21670163
theorem B6419681 : Blo 1690045 6419681 := bstep (se 2 (by rfl) ⟨2407380, by rfl⟩ : syracuseStep 6419681 = 4814761) B4814761
theorem B7223251 : Blo 1690045 7223251 := bstep (se 1 (by rfl) ⟨5417438, by rfl⟩ : syracuseStep 7223251 = 10834877) B10834877
theorem B27433181 : Blo 1690045 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B73155149 : Blo 1690045 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B2853083 : Blo 1690045 2853083 := bstep (se 1 (by rfl) ⟨2139812, by rfl⟩ : syracuseStep 2853083 = 4279625) B4279625
theorem B4279787 : Blo 1690045 4279787 := bstep (se 1 (by rfl) ⟨3209840, by rfl⟩ : syracuseStep 4279787 = 6419681) B6419681
theorem B6419695 : Blo 1690045 6419695 := bstep (se 1 (by rfl) ⟨4814771, by rfl⟩ : syracuseStep 6419695 = 9629543) B9629543
theorem B9631001 : Blo 1690045 9631001 := bstep (se 2 (by rfl) ⟨3611625, by rfl⟩ : syracuseStep 9631001 = 7223251) B7223251
theorem B9631183 : Blo 1690045 9631183 := bstep (se 1 (by rfl) ⟨7223387, by rfl⟩ : syracuseStep 9631183 = 14446775) B14446775
theorem B1902055 : Blo 1690045 1902055 := bstep (se 1 (by rfl) ⟨1426541, by rfl⟩ : syracuseStep 1902055 = 2853083) B2853083
theorem B2853191 : Blo 1690045 2853191 := bstep (se 1 (by rfl) ⟨2139893, by rfl⟩ : syracuseStep 2853191 = 4279787) B4279787
theorem B48770099 : Blo 1690045 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B12841577 : Blo 1690045 12841577 := bstep (se 2 (by rfl) ⟨4815591, by rfl⟩ : syracuseStep 12841577 = 9631183) B9631183
theorem B6420667 : Blo 1690045 6420667 := bstep (se 1 (by rfl) ⟨4815500, by rfl⟩ : syracuseStep 6420667 = 9631001) B9631001
theorem B8559593 : Blo 1690045 8559593 := bstep (se 2 (by rfl) ⟨3209847, by rfl⟩ : syracuseStep 8559593 = 6419695) B6419695
theorem B8560889 : Blo 1690045 8560889 := bstep (se 2 (by rfl) ⟨3210333, by rfl⟩ : syracuseStep 8560889 = 6420667) B6420667
theorem B8561051 : Blo 1690045 8561051 := bstep (se 1 (by rfl) ⟨6420788, by rfl⟩ : syracuseStep 8561051 = 12841577) B12841577
theorem B1902127 : Blo 1690045 1902127 := bstep (se 1 (by rfl) ⟨1426595, by rfl⟩ : syracuseStep 1902127 = 2853191) B2853191
theorem B2536073 : Blo 1690045 2536073 := bstep (se 2 (by rfl) ⟨951027, by rfl⟩ : syracuseStep 2536073 = 1902055) B1902055
theorem B5706395 : Blo 1690045 5706395 := bstep (se 1 (by rfl) ⟨4279796, by rfl⟩ : syracuseStep 5706395 = 8559593) B8559593
theorem B32513399 : Blo 1690045 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B1690715 : Blo 1690045 1690715 := bstep (se 1 (by rfl) ⟨1268036, by rfl⟩ : syracuseStep 1690715 = 2536073) B2536073
theorem B3804263 : Blo 1690045 3804263 := bstep (se 1 (by rfl) ⟨2853197, by rfl⟩ : syracuseStep 3804263 = 5706395) B5706395
theorem B2536169 : Blo 1690045 2536169 := bstep (se 2 (by rfl) ⟨951063, by rfl⟩ : syracuseStep 2536169 = 1902127) B1902127
theorem B5707259 : Blo 1690045 5707259 := bstep (se 1 (by rfl) ⟨4280444, by rfl⟩ : syracuseStep 5707259 = 8560889) B8560889
theorem B5707367 : Blo 1690045 5707367 := bstep (se 1 (by rfl) ⟨4280525, by rfl⟩ : syracuseStep 5707367 = 8561051) B8561051
theorem B21675599 : Blo 1690045 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B1690779 : Blo 1690045 1690779 := bstep (se 1 (by rfl) ⟨1268084, by rfl⟩ : syracuseStep 1690779 = 2536169) B2536169
theorem B3804839 : Blo 1690045 3804839 := bstep (se 1 (by rfl) ⟨2853629, by rfl⟩ : syracuseStep 3804839 = 5707259) B5707259
theorem B3804911 : Blo 1690045 3804911 := bstep (se 1 (by rfl) ⟨2853683, by rfl⟩ : syracuseStep 3804911 = 5707367) B5707367
theorem B2536175 : Blo 1690045 2536175 := bstep (se 1 (by rfl) ⟨1902131, by rfl⟩ : syracuseStep 2536175 = 3804263) B3804263
theorem B14450399 : Blo 1690045 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B1690783 : Blo 1690045 1690783 := bstep (se 1 (by rfl) ⟨1268087, by rfl⟩ : syracuseStep 1690783 = 2536175) B2536175
theorem B2536559 : Blo 1690045 2536559 := bstep (se 1 (by rfl) ⟨1902419, by rfl⟩ : syracuseStep 2536559 = 3804839) B3804839
theorem B2536607 : Blo 1690045 2536607 := bstep (se 1 (by rfl) ⟨1902455, by rfl⟩ : syracuseStep 2536607 = 3804911) B3804911
theorem B9633599 : Blo 1690045 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B1691039 : Blo 1690045 1691039 := bstep (se 1 (by rfl) ⟨1268279, by rfl⟩ : syracuseStep 1691039 = 2536559) B2536559
theorem B1691071 : Blo 1690045 1691071 := bstep (se 1 (by rfl) ⟨1268303, by rfl⟩ : syracuseStep 1691071 = 2536607) B2536607
theorem B6422399 : Blo 1690045 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B4281599 : Blo 1690045 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B2854399 : Blo 1690045 2854399 := bstep (se 1 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 2854399 = 4281599) B4281599
theorem B3805865 : Blo 1690045 3805865 := bstep (se 2 (by rfl) ⟨1427199, by rfl⟩ : syracuseStep 3805865 = 2854399) B2854399
theorem B2537243 : Blo 1690045 2537243 := bstep (se 1 (by rfl) ⟨1902932, by rfl⟩ : syracuseStep 2537243 = 3805865) B3805865
theorem B1691495 : Blo 1690045 1691495 := bstep (se 1 (by rfl) ⟨1268621, by rfl⟩ : syracuseStep 1691495 = 2537243) B2537243

theorem C0 (j : ℕ) (h1 : 422511 ≤ j) (h2 : j ≤ 422885) : Blo 1690045 (4 * j + 3) := by
  interval_cases j
  · exact B1690047
  · exact B1690051
  · exact B1690055
  · exact B1690059
  · exact B1690063
  · exact B1690067
  · exact B1690071
  · exact B1690075
  · exact B1690079
  · exact B1690083
  · exact B1690087
  · exact B1690091
  · exact B1690095
  · exact B1690099
  · exact B1690103
  · exact B1690107
  · exact B1690111
  · exact B1690115
  · exact B1690119
  · exact B1690123
  · exact B1690127
  · exact B1690131
  · exact B1690135
  · exact B1690139
  · exact B1690143
  · exact B1690147
  · exact B1690151
  · exact B1690155
  · exact B1690159
  · exact B1690163
  · exact B1690167
  · exact B1690171
  · exact B1690175
  · exact B1690179
  · exact B1690183
  · exact B1690187
  · exact B1690191
  · exact B1690195
  · exact B1690199
  · exact B1690203
  · exact B1690207
  · exact B1690211
  · exact B1690215
  · exact B1690219
  · exact B1690223
  · exact B1690227
  · exact B1690231
  · exact B1690235
  · exact B1690239
  · exact B1690243
  · exact B1690247
  · exact B1690251
  · exact B1690255
  · exact B1690259
  · exact B1690263
  · exact B1690267
  · exact B1690271
  · exact B1690275
  · exact B1690279
  · exact B1690283
  · exact B1690287
  · exact B1690291
  · exact B1690295
  · exact B1690299
  · exact B1690303
  · exact B1690307
  · exact B1690311
  · exact B1690315
  · exact B1690319
  · exact B1690323
  · exact B1690327
  · exact B1690331
  · exact B1690335
  · exact B1690339
  · exact B1690343
  · exact B1690347
  · exact B1690351
  · exact B1690355
  · exact B1690359
  · exact B1690363
  · exact B1690367
  · exact B1690371
  · exact B1690375
  · exact B1690379
  · exact B1690383
  · exact B1690387
  · exact B1690391
  · exact B1690395
  · exact B1690399
  · exact B1690403
  · exact B1690407
  · exact B1690411
  · exact B1690415
  · exact B1690419
  · exact B1690423
  · exact B1690427
  · exact B1690431
  · exact B1690435
  · exact B1690439
  · exact B1690443
  · exact B1690447
  · exact B1690451
  · exact B1690455
  · exact B1690459
  · exact B1690463
  · exact B1690467
  · exact B1690471
  · exact B1690475
  · exact B1690479
  · exact B1690483
  · exact B1690487
  · exact B1690491
  · exact B1690495
  · exact B1690499
  · exact B1690503
  · exact B1690507
  · exact B1690511
  · exact B1690515
  · exact B1690519
  · exact B1690523
  · exact B1690527
  · exact B1690531
  · exact B1690535
  · exact B1690539
  · exact B1690543
  · exact B1690547
  · exact B1690551
  · exact B1690555
  · exact B1690559
  · exact B1690563
  · exact B1690567
  · exact B1690571
  · exact B1690575
  · exact B1690579
  · exact B1690583
  · exact B1690587
  · exact B1690591
  · exact B1690595
  · exact B1690599
  · exact B1690603
  · exact B1690607
  · exact B1690611
  · exact B1690615
  · exact B1690619
  · exact B1690623
  · exact B1690627
  · exact B1690631
  · exact B1690635
  · exact B1690639
  · exact B1690643
  · exact B1690647
  · exact B1690651
  · exact B1690655
  · exact B1690659
  · exact B1690663
  · exact B1690667
  · exact B1690671
  · exact B1690675
  · exact B1690679
  · exact B1690683
  · exact B1690687
  · exact B1690691
  · exact B1690695
  · exact B1690699
  · exact B1690703
  · exact B1690707
  · exact B1690711
  · exact B1690715
  · exact B1690719
  · exact B1690723
  · exact B1690727
  · exact B1690731
  · exact B1690735
  · exact B1690739
  · exact B1690743
  · exact B1690747
  · exact B1690751
  · exact B1690755
  · exact B1690759
  · exact B1690763
  · exact B1690767
  · exact B1690771
  · exact B1690775
  · exact B1690779
  · exact B1690783
  · exact B1690787
  · exact B1690791
  · exact B1690795
  · exact B1690799
  · exact B1690803
  · exact B1690807
  · exact B1690811
  · exact B1690815
  · exact B1690819
  · exact B1690823
  · exact B1690827
  · exact B1690831
  · exact B1690835
  · exact B1690839
  · exact B1690843
  · exact B1690847
  · exact B1690851
  · exact B1690855
  · exact B1690859
  · exact B1690863
  · exact B1690867
  · exact B1690871
  · exact B1690875
  · exact B1690879
  · exact B1690883
  · exact B1690887
  · exact B1690891
  · exact B1690895
  · exact B1690899
  · exact B1690903
  · exact B1690907
  · exact B1690911
  · exact B1690915
  · exact B1690919
  · exact B1690923
  · exact B1690927
  · exact B1690931
  · exact B1690935
  · exact B1690939
  · exact B1690943
  · exact B1690947
  · exact B1690951
  · exact B1690955
  · exact B1690959
  · exact B1690963
  · exact B1690967
  · exact B1690971
  · exact B1690975
  · exact B1690979
  · exact B1690983
  · exact B1690987
  · exact B1690991
  · exact B1690995
  · exact B1690999
  · exact B1691003
  · exact B1691007
  · exact B1691011
  · exact B1691015
  · exact B1691019
  · exact B1691023
  · exact B1691027
  · exact B1691031
  · exact B1691035
  · exact B1691039
  · exact B1691043
  · exact B1691047
  · exact B1691051
  · exact B1691055
  · exact B1691059
  · exact B1691063
  · exact B1691067
  · exact B1691071
  · exact B1691075
  · exact B1691079
  · exact B1691083
  · exact B1691087
  · exact B1691091
  · exact B1691095
  · exact B1691099
  · exact B1691103
  · exact B1691107
  · exact B1691111
  · exact B1691115
  · exact B1691119
  · exact B1691123
  · exact B1691127
  · exact B1691131
  · exact B1691135
  · exact B1691139
  · exact B1691143
  · exact B1691147
  · exact B1691151
  · exact B1691155
  · exact B1691159
  · exact B1691163
  · exact B1691167
  · exact B1691171
  · exact B1691175
  · exact B1691179
  · exact B1691183
  · exact B1691187
  · exact B1691191
  · exact B1691195
  · exact B1691199
  · exact B1691203
  · exact B1691207
  · exact B1691211
  · exact B1691215
  · exact B1691219
  · exact B1691223
  · exact B1691227
  · exact B1691231
  · exact B1691235
  · exact B1691239
  · exact B1691243
  · exact B1691247
  · exact B1691251
  · exact B1691255
  · exact B1691259
  · exact B1691263
  · exact B1691267
  · exact B1691271
  · exact B1691275
  · exact B1691279
  · exact B1691283
  · exact B1691287
  · exact B1691291
  · exact B1691295
  · exact B1691299
  · exact B1691303
  · exact B1691307
  · exact B1691311
  · exact B1691315
  · exact B1691319
  · exact B1691323
  · exact B1691327
  · exact B1691331
  · exact B1691335
  · exact B1691339
  · exact B1691343
  · exact B1691347
  · exact B1691351
  · exact B1691355
  · exact B1691359
  · exact B1691363
  · exact B1691367
  · exact B1691371
  · exact B1691375
  · exact B1691379
  · exact B1691383
  · exact B1691387
  · exact B1691391
  · exact B1691395
  · exact B1691399
  · exact B1691403
  · exact B1691407
  · exact B1691411
  · exact B1691415
  · exact B1691419
  · exact B1691423
  · exact B1691427
  · exact B1691431
  · exact B1691435
  · exact B1691439
  · exact B1691443
  · exact B1691447
  · exact B1691451
  · exact B1691455
  · exact B1691459
  · exact B1691463
  · exact B1691467
  · exact B1691471
  · exact B1691475
  · exact B1691479
  · exact B1691483
  · exact B1691487
  · exact B1691491
  · exact B1691495
  · exact B1691499
  · exact B1691503
  · exact B1691507
  · exact B1691511
  · exact B1691515
  · exact B1691519
  · exact B1691523
  · exact B1691527
  · exact B1691531
  · exact B1691535
  · exact B1691539
  · exact B1691543

theorem solution (m : ℕ) (hlo : 1690045 ≤ m) (hhi : m ≤ 1691545) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 422511 ≤ j := by omega
    have hj2 : j ≤ 422885 := by omega
    have hb : Blo 1690045 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
