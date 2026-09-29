-- Prove2me | solution 1 for syracuse_descends_range_1657528_1659528
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:18:45.631576+00:00
-- url     : https://prove2.me/submissions/710acb86-5217-4b5c-8cdc-88e1d8ad673a

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


theorem B6299653 : Blo 1657528 6299653 := bbase (se 4 (by rfl) ⟨590592, by rfl⟩ : syracuseStep 6299653 = 1181185) (by norm_num)
theorem B28712981 : Blo 1657528 28712981 := bbase (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) (by norm_num)
theorem B4481093 : Blo 1657528 4481093 := bbase (se 4 (by rfl) ⟨420102, by rfl⟩ : syracuseStep 4481093 = 840205) (by norm_num)
theorem B5595317 : Blo 1657528 5595317 := bbase (se 5 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 5595317 = 524561) (by norm_num)
theorem B40337621 : Blo 1657528 40337621 := bbase (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) (by norm_num)
theorem B7086325 : Blo 1657528 7086325 := bbase (se 5 (by rfl) ⟨332171, by rfl⟩ : syracuseStep 7086325 = 664343) (by norm_num)
theorem B6299957 : Blo 1657528 6299957 := bbase (se 5 (by rfl) ⟨295310, by rfl⟩ : syracuseStep 6299957 = 590621) (by norm_num)
theorem B2990509 : Blo 1657528 2990509 := bbase (se 3 (by rfl) ⟨560720, by rfl⟩ : syracuseStep 2990509 = 1121441) (by norm_num)
theorem B8511925 : Blo 1657528 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B8397269 : Blo 1657528 8397269 := bbase (se 7 (by rfl) ⟨98405, by rfl⟩ : syracuseStep 8397269 = 196811) (by norm_num)
theorem B8970709 : Blo 1657528 8970709 := bbase (se 7 (by rfl) ⟨105125, by rfl⟩ : syracuseStep 8970709 = 210251) (by norm_num)
theorem B5980661 : Blo 1657528 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B11960885 : Blo 1657528 11960885 := bbase (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) (by norm_num)
theorem B5595749 : Blo 1657528 5595749 := bbase (se 4 (by rfl) ⟨524601, by rfl⟩ : syracuseStep 5595749 = 1049203) (by norm_num)
theorem B1991309 : Blo 1657528 1991309 := bbase (se 3 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 1991309 = 746741) (by norm_num)
theorem B2097829 : Blo 1657528 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B14172853 : Blo 1657528 14172853 := bbase (se 5 (by rfl) ⟨664352, by rfl⟩ : syracuseStep 14172853 = 1328705) (by norm_num)
theorem B13443797 : Blo 1657528 13443797 := bbase (se 7 (by rfl) ⟨157544, by rfl⟩ : syracuseStep 13443797 = 315089) (by norm_num)
theorem B1991405 : Blo 1657528 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B2098001 : Blo 1657528 2098001 := bbase (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) (by norm_num)
theorem B1770373 : Blo 1657528 1770373 := bbase (se 4 (by rfl) ⟨165972, by rfl⟩ : syracuseStep 1770373 = 331945) (by norm_num)
theorem B2098057 : Blo 1657528 2098057 := bbase (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) (by norm_num)
theorem B1991569 : Blo 1657528 1991569 := bbase (se 2 (by rfl) ⟨746838, by rfl⟩ : syracuseStep 1991569 = 1493677) (by norm_num)
theorem B5530565 : Blo 1657528 5530565 := bbase (se 4 (by rfl) ⟨518490, by rfl⟩ : syracuseStep 5530565 = 1036981) (by norm_num)
theorem B2360269 : Blo 1657528 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B1770445 : Blo 1657528 1770445 := bbase (se 3 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 1770445 = 663917) (by norm_num)
theorem B2098153 : Blo 1657528 2098153 := bbase (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) (by norm_num)
theorem B5596181 : Blo 1657528 5596181 := bbase (se 6 (by rfl) ⟨131160, by rfl⟩ : syracuseStep 5596181 = 262321) (by norm_num)
theorem B3146789 : Blo 1657528 3146789 := bbase (se 4 (by rfl) ⟨295011, by rfl⟩ : syracuseStep 3146789 = 590023) (by norm_num)
theorem B11658325 : Blo 1657528 11658325 := bbase (se 8 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 11658325 = 136621) (by norm_num)
theorem B18900053 : Blo 1657528 18900053 := bbase (se 8 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 18900053 = 221485) (by norm_num)
theorem B1991785 : Blo 1657528 1991785 := bbase (se 2 (by rfl) ⟨746919, by rfl⟩ : syracuseStep 1991785 = 1493839) (by norm_num)
theorem B2098325 : Blo 1657528 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B3146941 : Blo 1657528 3146941 := bbase (se 3 (by rfl) ⟨590051, by rfl⟩ : syracuseStep 3146941 = 1180103) (by norm_num)
theorem B1680589 : Blo 1657528 1680589 := bbase (se 3 (by rfl) ⟨315110, by rfl⟩ : syracuseStep 1680589 = 630221) (by norm_num)
theorem B2098381 : Blo 1657528 2098381 := bbase (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) (by norm_num)
theorem B1991953 : Blo 1657528 1991953 := bbase (se 2 (by rfl) ⟨746982, by rfl⟩ : syracuseStep 1991953 = 1493965) (by norm_num)
theorem B2360605 : Blo 1657528 2360605 := bbase (se 3 (by rfl) ⟨442613, by rfl⟩ : syracuseStep 2360605 = 885227) (by norm_num)
theorem B2098477 : Blo 1657528 2098477 := bbase (se 3 (by rfl) ⟨393464, by rfl⟩ : syracuseStep 2098477 = 786929) (by norm_num)
theorem B1770817 : Blo 1657528 1770817 := bbase (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) (by norm_num)
theorem B4195709 : Blo 1657528 4195709 := bbase (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) (by norm_num)
theorem B5596613 : Blo 1657528 5596613 := bbase (se 4 (by rfl) ⟨524682, by rfl⟩ : syracuseStep 5596613 = 1049365) (by norm_num)
theorem B2098649 : Blo 1657528 2098649 := bbase (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) (by norm_num)
theorem B3147245 : Blo 1657528 3147245 := bbase (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) (by norm_num)
theorem B2360821 : Blo 1657528 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B4040189 : Blo 1657528 4040189 := bbase (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) (by norm_num)
theorem B2098705 : Blo 1657528 2098705 := bbase (se 2 (by rfl) ⟨787014, by rfl⟩ : syracuseStep 2098705 = 1574029) (by norm_num)
theorem B6727205 : Blo 1657528 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B4195901 : Blo 1657528 4195901 := bbase (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) (by norm_num)
theorem B15754837 : Blo 1657528 15754837 := bbase (se 8 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 15754837 = 184627) (by norm_num)
theorem B3884645 : Blo 1657528 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B2098801 : Blo 1657528 2098801 := bbase (se 2 (by rfl) ⟨787050, by rfl⟩ : syracuseStep 2098801 = 1574101) (by norm_num)
theorem B2393725 : Blo 1657528 2393725 := bbase (se 3 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 2393725 = 897647) (by norm_num)
theorem B6727349 : Blo 1657528 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B1771193 : Blo 1657528 1771193 := bbase (se 2 (by rfl) ⟨664197, by rfl⟩ : syracuseStep 1771193 = 1328395) (by norm_num)
theorem B3540685 : Blo 1657528 3540685 := bbase (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) (by norm_num)
theorem B9570005 : Blo 1657528 9570005 := bbase (se 7 (by rfl) ⟨112148, by rfl⟩ : syracuseStep 9570005 = 224297) (by norm_num)
theorem B8398565 : Blo 1657528 8398565 := bbase (se 4 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 8398565 = 1574731) (by norm_num)
theorem B1771265 : Blo 1657528 1771265 := bbase (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) (by norm_num)
theorem B1681165 : Blo 1657528 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B2098973 : Blo 1657528 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B1992481 : Blo 1657528 1992481 := bbase (se 2 (by rfl) ⟨747180, by rfl⟩ : syracuseStep 1992481 = 1494361) (by norm_num)
theorem B1681205 : Blo 1657528 1681205 := bbase (se 5 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 1681205 = 157613) (by norm_num)
theorem B2099029 : Blo 1657528 2099029 := bbase (se 9 (by rfl) ⟨6149, by rfl⟩ : syracuseStep 2099029 = 12299) (by norm_num)
theorem B2361197 : Blo 1657528 2361197 := bbase (se 3 (by rfl) ⟨442724, by rfl⟩ : syracuseStep 2361197 = 885449) (by norm_num)
theorem B5597045 : Blo 1657528 5597045 := bbase (se 5 (by rfl) ⟨262361, by rfl⟩ : syracuseStep 5597045 = 524723) (by norm_num)
theorem B4196245 : Blo 1657528 4196245 := bbase (se 6 (by rfl) ⟨98349, by rfl⟩ : syracuseStep 4196245 = 196699) (by norm_num)
theorem B2099125 : Blo 1657528 2099125 := bbase (se 5 (by rfl) ⟨98396, by rfl⟩ : syracuseStep 2099125 = 196793) (by norm_num)
theorem B1771453 : Blo 1657528 1771453 := bbase (se 3 (by rfl) ⟨332147, by rfl⟩ : syracuseStep 1771453 = 664295) (by norm_num)
theorem B8513525 : Blo 1657528 8513525 := bbase (se 5 (by rfl) ⟨399071, by rfl⟩ : syracuseStep 8513525 = 798143) (by norm_num)
theorem B4196357 : Blo 1657528 4196357 := bbase (se 4 (by rfl) ⟨393408, by rfl⟩ : syracuseStep 4196357 = 786817) (by norm_num)
theorem B2656309 : Blo 1657528 2656309 := bbase (se 5 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 2656309 = 249029) (by norm_num)
theorem B2099297 : Blo 1657528 2099297 := bbase (se 2 (by rfl) ⟨787236, by rfl⟩ : syracuseStep 2099297 = 1574473) (by norm_num)
theorem B3729509 : Blo 1657528 3729509 := bbase (se 4 (by rfl) ⟨349641, by rfl⟩ : syracuseStep 3729509 = 699283) (by norm_num)
theorem B1771637 : Blo 1657528 1771637 := bbase (se 5 (by rfl) ⟨83045, by rfl⟩ : syracuseStep 1771637 = 166091) (by norm_num)
theorem B12601493 : Blo 1657528 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B2099353 : Blo 1657528 2099353 := bbase (se 2 (by rfl) ⟨787257, by rfl⟩ : syracuseStep 2099353 = 1574515) (by norm_num)
theorem B3729581 : Blo 1657528 3729581 := bbase (se 3 (by rfl) ⟨699296, by rfl⟩ : syracuseStep 3729581 = 1398593) (by norm_num)
theorem B4196549 : Blo 1657528 4196549 := bbase (se 4 (by rfl) ⟨393426, by rfl⟩ : syracuseStep 4196549 = 786853) (by norm_num)
theorem B3147997 : Blo 1657528 3147997 := bbase (se 3 (by rfl) ⟨590249, by rfl⟩ : syracuseStep 3147997 = 1180499) (by norm_num)
theorem B3729653 : Blo 1657528 3729653 := bbase (se 5 (by rfl) ⟨174827, by rfl⟩ : syracuseStep 3729653 = 349655) (by norm_num)
theorem B2099449 : Blo 1657528 2099449 := bbase (se 2 (by rfl) ⟨787293, by rfl⟩ : syracuseStep 2099449 = 1574587) (by norm_num)
theorem B5597477 : Blo 1657528 5597477 := bbase (se 4 (by rfl) ⟨524763, by rfl⟩ : syracuseStep 5597477 = 1049527) (by norm_num)
theorem B2656565 : Blo 1657528 2656565 := bbase (se 5 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 2656565 = 249053) (by norm_num)
theorem B3729725 : Blo 1657528 3729725 := bbase (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) (by norm_num)
theorem B3148141 : Blo 1657528 3148141 := bbase (se 3 (by rfl) ⟨590276, by rfl⟩ : syracuseStep 3148141 = 1180553) (by norm_num)
theorem B3729797 : Blo 1657528 3729797 := bbase (se 4 (by rfl) ⟨349668, by rfl⟩ : syracuseStep 3729797 = 699337) (by norm_num)
theorem B2099621 : Blo 1657528 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B2591165 : Blo 1657528 2591165 := bbase (se 3 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 2591165 = 971687) (by norm_num)
theorem B3729869 : Blo 1657528 3729869 := bbase (se 3 (by rfl) ⟨699350, by rfl⟩ : syracuseStep 3729869 = 1398701) (by norm_num)
theorem B2099677 : Blo 1657528 2099677 := bbase (se 3 (by rfl) ⟨393689, by rfl⟩ : syracuseStep 2099677 = 787379) (by norm_num)
theorem B7965157 : Blo 1657528 7965157 := bbase (se 4 (by rfl) ⟨746733, by rfl⟩ : syracuseStep 7965157 = 1493467) (by norm_num)
theorem B4721141 : Blo 1657528 4721141 := bbase (se 5 (by rfl) ⟨221303, by rfl⟩ : syracuseStep 4721141 = 442607) (by norm_num)
theorem B2656757 : Blo 1657528 2656757 := bbase (se 5 (by rfl) ⟨124535, by rfl⟩ : syracuseStep 2656757 = 249071) (by norm_num)
theorem B3148301 : Blo 1657528 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B3729941 : Blo 1657528 3729941 := bbase (se 6 (by rfl) ⟨87420, by rfl⟩ : syracuseStep 3729941 = 174841) (by norm_num)
theorem B4196893 : Blo 1657528 4196893 := bbase (se 3 (by rfl) ⟨786917, by rfl⟩ : syracuseStep 4196893 = 1573835) (by norm_num)
theorem B12593717 : Blo 1657528 12593717 := bbase (se 5 (by rfl) ⟨590330, by rfl⟩ : syracuseStep 12593717 = 1180661) (by norm_num)
theorem B2099773 : Blo 1657528 2099773 := bbase (se 3 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 2099773 = 787415) (by norm_num)
theorem B3541573 : Blo 1657528 3541573 := bbase (se 4 (by rfl) ⟨332022, by rfl⟩ : syracuseStep 3541573 = 664045) (by norm_num)
theorem B3730013 : Blo 1657528 3730013 := bbase (se 3 (by rfl) ⟨699377, by rfl⟩ : syracuseStep 3730013 = 1398755) (by norm_num)
theorem B15944309 : Blo 1657528 15944309 := bbase (se 5 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 15944309 = 1494779) (by norm_num)
theorem B14174837 : Blo 1657528 14174837 := bbase (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) (by norm_num)
theorem B4197005 : Blo 1657528 4197005 := bbase (se 3 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 4197005 = 1573877) (by norm_num)
theorem B4311701 : Blo 1657528 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B3148445 : Blo 1657528 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B3730085 : Blo 1657528 3730085 := bbase (se 4 (by rfl) ⟨349695, by rfl⟩ : syracuseStep 3730085 = 699391) (by norm_num)
theorem B5597909 : Blo 1657528 5597909 := bbase (se 7 (by rfl) ⟨65600, by rfl⟩ : syracuseStep 5597909 = 131201) (by norm_num)
theorem B2099945 : Blo 1657528 2099945 := bbase (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) (by norm_num)
theorem B3730157 : Blo 1657528 3730157 := bbase (se 3 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 3730157 = 1398809) (by norm_num)
theorem B6294293 : Blo 1657528 6294293 := bbase (se 6 (by rfl) ⟨147522, by rfl⟩ : syracuseStep 6294293 = 295045) (by norm_num)
theorem B11504405 : Blo 1657528 11504405 := bbase (se 6 (by rfl) ⟨269634, by rfl⟩ : syracuseStep 11504405 = 539269) (by norm_num)
theorem B2100001 : Blo 1657528 2100001 := bbase (se 2 (by rfl) ⟨787500, by rfl⟩ : syracuseStep 2100001 = 1575001) (by norm_num)
theorem B3730229 : Blo 1657528 3730229 := bbase (se 5 (by rfl) ⟨174854, by rfl⟩ : syracuseStep 3730229 = 349709) (by norm_num)
theorem B4197197 : Blo 1657528 4197197 := bbase (se 3 (by rfl) ⟨786974, by rfl⟩ : syracuseStep 4197197 = 1573949) (by norm_num)
theorem B1993577 : Blo 1657528 1993577 := bbase (se 2 (by rfl) ⟨747591, by rfl⟩ : syracuseStep 1993577 = 1495183) (by norm_num)
theorem B3730301 : Blo 1657528 3730301 := bbase (se 3 (by rfl) ⟨699431, by rfl⟩ : syracuseStep 3730301 = 1398863) (by norm_num)
theorem B2100097 : Blo 1657528 2100097 := bbase (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) (by norm_num)
theorem B2837405 : Blo 1657528 2837405 := bbase (se 3 (by rfl) ⟨532013, by rfl⟩ : syracuseStep 2837405 = 1064027) (by norm_num)
theorem B3148733 : Blo 1657528 3148733 := bbase (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) (by norm_num)
theorem B3730373 : Blo 1657528 3730373 := bbase (se 4 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 3730373 = 699445) (by norm_num)
theorem B8399861 : Blo 1657528 8399861 := bbase (se 5 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 8399861 = 787487) (by norm_num)
theorem B3730445 : Blo 1657528 3730445 := bbase (se 3 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 3730445 = 1398917) (by norm_num)
theorem B2100269 : Blo 1657528 2100269 := bbase (se 3 (by rfl) ⟨393800, by rfl⟩ : syracuseStep 2100269 = 787601) (by norm_num)
theorem B6294581 : Blo 1657528 6294581 := bbase (se 5 (by rfl) ⟨295058, by rfl⟩ : syracuseStep 6294581 = 590117) (by norm_num)
theorem B3542069 : Blo 1657528 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B3730517 : Blo 1657528 3730517 := bbase (se 8 (by rfl) ⟨21858, by rfl⟩ : syracuseStep 3730517 = 43717) (by norm_num)
theorem B3148885 : Blo 1657528 3148885 := bbase (se 8 (by rfl) ⟨18450, by rfl⟩ : syracuseStep 3148885 = 36901) (by norm_num)
theorem B9579605 : Blo 1657528 9579605 := bbase (se 8 (by rfl) ⟨56130, by rfl⟩ : syracuseStep 9579605 = 112261) (by norm_num)
theorem B2100325 : Blo 1657528 2100325 := bbase (se 4 (by rfl) ⟨196905, by rfl⟩ : syracuseStep 2100325 = 393811) (by norm_num)
theorem B5598341 : Blo 1657528 5598341 := bbase (se 4 (by rfl) ⟨524844, by rfl⟩ : syracuseStep 5598341 = 1049689) (by norm_num)
theorem B3730589 : Blo 1657528 3730589 := bbase (se 3 (by rfl) ⟨699485, by rfl⟩ : syracuseStep 3730589 = 1398971) (by norm_num)
theorem B4197541 : Blo 1657528 4197541 := bbase (se 4 (by rfl) ⟨393519, by rfl⟩ : syracuseStep 4197541 = 787039) (by norm_num)
theorem B5311669 : Blo 1657528 5311669 := bbase (se 5 (by rfl) ⟨248984, by rfl⟩ : syracuseStep 5311669 = 497969) (by norm_num)
theorem B11349173 : Blo 1657528 11349173 := bbase (se 5 (by rfl) ⟨531992, by rfl⟩ : syracuseStep 11349173 = 1063985) (by norm_num)
theorem B3730661 : Blo 1657528 3730661 := bbase (se 4 (by rfl) ⟨349749, by rfl⟩ : syracuseStep 3730661 = 699499) (by norm_num)
theorem B2362621 : Blo 1657528 2362621 := bbase (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) (by norm_num)
theorem B4197653 : Blo 1657528 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B3730733 : Blo 1657528 3730733 := bbase (se 3 (by rfl) ⟨699512, by rfl⟩ : syracuseStep 3730733 = 1399025) (by norm_num)
theorem B3730805 : Blo 1657528 3730805 := bbase (se 5 (by rfl) ⟨174881, by rfl⟩ : syracuseStep 3730805 = 349763) (by norm_num)
theorem B3149189 : Blo 1657528 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B8392085 : Blo 1657528 8392085 := bbase (se 6 (by rfl) ⟨196689, by rfl⟩ : syracuseStep 8392085 = 393379) (by norm_num)
theorem B7564693 : Blo 1657528 7564693 := bbase (se 6 (by rfl) ⟨177297, by rfl⟩ : syracuseStep 7564693 = 354595) (by norm_num)
theorem B2657693 : Blo 1657528 2657693 := bbase (se 3 (by rfl) ⟨498317, by rfl⟩ : syracuseStep 2657693 = 996635) (by norm_num)
theorem B3730877 : Blo 1657528 3730877 := bbase (se 3 (by rfl) ⟨699539, by rfl⟩ : syracuseStep 3730877 = 1399079) (by norm_num)
theorem B4197845 : Blo 1657528 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B3730949 : Blo 1657528 3730949 := bbase (se 4 (by rfl) ⟨349776, by rfl⟩ : syracuseStep 3730949 = 699553) (by norm_num)
theorem B4312597 : Blo 1657528 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B2797085 : Blo 1657528 2797085 := bbase (se 3 (by rfl) ⟨524453, by rfl⟩ : syracuseStep 2797085 = 1048907) (by norm_num)
theorem B5598773 : Blo 1657528 5598773 := bbase (se 5 (by rfl) ⟨262442, by rfl⟩ : syracuseStep 5598773 = 524885) (by norm_num)
theorem B3731021 : Blo 1657528 3731021 := bbase (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) (by norm_num)
theorem B6721157 : Blo 1657528 6721157 := bbase (se 4 (by rfl) ⟨630108, by rfl⟩ : syracuseStep 6721157 = 1260217) (by norm_num)
theorem B3731093 : Blo 1657528 3731093 := bbase (se 6 (by rfl) ⟨87447, by rfl⟩ : syracuseStep 3731093 = 174895) (by norm_num)
theorem B2797213 : Blo 1657528 2797213 := bbase (se 3 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 2797213 = 1048955) (by norm_num)
theorem B3731165 : Blo 1657528 3731165 := bbase (se 3 (by rfl) ⟨699593, by rfl⟩ : syracuseStep 3731165 = 1399187) (by norm_num)
theorem B2797301 : Blo 1657528 2797301 := bbase (se 5 (by rfl) ⟨131123, by rfl⟩ : syracuseStep 2797301 = 262247) (by norm_num)
theorem B3362573 : Blo 1657528 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B2658077 : Blo 1657528 2658077 := bbase (se 3 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 2658077 = 996779) (by norm_num)
theorem B3731237 : Blo 1657528 3731237 := bbase (se 4 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 3731237 = 699607) (by norm_num)
theorem B4198189 : Blo 1657528 4198189 := bbase (se 3 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 4198189 = 1574321) (by norm_num)
theorem B3731309 : Blo 1657528 3731309 := bbase (se 3 (by rfl) ⟨699620, by rfl⟩ : syracuseStep 3731309 = 1399241) (by norm_num)
theorem B2797429 : Blo 1657528 2797429 := bbase (se 5 (by rfl) ⟨131129, by rfl⟩ : syracuseStep 2797429 = 262259) (by norm_num)
theorem B3542933 : Blo 1657528 3542933 := bbase (se 6 (by rfl) ⟨83037, by rfl⟩ : syracuseStep 3542933 = 166075) (by norm_num)
theorem B4198301 : Blo 1657528 4198301 := bbase (se 3 (by rfl) ⟨787181, by rfl⟩ : syracuseStep 4198301 = 1574363) (by norm_num)
theorem B2658205 : Blo 1657528 2658205 := bbase (se 3 (by rfl) ⟨498413, by rfl⟩ : syracuseStep 2658205 = 996827) (by norm_num)
theorem B3731381 : Blo 1657528 3731381 := bbase (se 5 (by rfl) ⟨174908, by rfl⟩ : syracuseStep 3731381 = 349817) (by norm_num)
theorem B2797517 : Blo 1657528 2797517 := bbase (se 3 (by rfl) ⟨524534, by rfl⟩ : syracuseStep 2797517 = 1049069) (by norm_num)
theorem B5599205 : Blo 1657528 5599205 := bbase (se 4 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 5599205 = 1049851) (by norm_num)
theorem B3731453 : Blo 1657528 3731453 := bbase (se 3 (by rfl) ⟨699647, by rfl⟩ : syracuseStep 3731453 = 1399295) (by norm_num)
theorem B2486309 : Blo 1657528 2486309 := bbase (se 4 (by rfl) ⟨233091, by rfl⟩ : syracuseStep 2486309 = 466183) (by norm_num)
theorem B4722725 : Blo 1657528 4722725 := bbase (se 4 (by rfl) ⟨442755, by rfl⟩ : syracuseStep 4722725 = 885511) (by norm_num)
theorem B3543077 : Blo 1657528 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B2486333 : Blo 1657528 2486333 := bbase (se 3 (by rfl) ⟨466187, by rfl⟩ : syracuseStep 2486333 = 932375) (by norm_num)
theorem B3731525 : Blo 1657528 3731525 := bbase (se 4 (by rfl) ⟨349830, by rfl⟩ : syracuseStep 3731525 = 699661) (by norm_num)
theorem B2797645 : Blo 1657528 2797645 := bbase (se 3 (by rfl) ⟨524558, by rfl⟩ : syracuseStep 2797645 = 1049117) (by norm_num)
theorem B2486357 : Blo 1657528 2486357 := bbase (se 8 (by rfl) ⟨14568, by rfl⟩ : syracuseStep 2486357 = 29137) (by norm_num)
theorem B4198493 : Blo 1657528 4198493 := bbase (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) (by norm_num)
theorem B2486381 : Blo 1657528 2486381 := bbase (se 3 (by rfl) ⟨466196, by rfl⟩ : syracuseStep 2486381 = 932393) (by norm_num)
theorem B3149941 : Blo 1657528 3149941 := bbase (se 5 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 3149941 = 295307) (by norm_num)
theorem B2486405 : Blo 1657528 2486405 := bbase (se 4 (by rfl) ⟨233100, by rfl⟩ : syracuseStep 2486405 = 466201) (by norm_num)
theorem B3731597 : Blo 1657528 3731597 := bbase (se 3 (by rfl) ⟨699674, by rfl⟩ : syracuseStep 3731597 = 1399349) (by norm_num)
theorem B2486429 : Blo 1657528 2486429 := bbase (se 3 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 2486429 = 932411) (by norm_num)
theorem B2797733 : Blo 1657528 2797733 := bbase (se 4 (by rfl) ⟨262287, by rfl⟩ : syracuseStep 2797733 = 524575) (by norm_num)
theorem B2486453 : Blo 1657528 2486453 := bbase (se 5 (by rfl) ⟨116552, by rfl⟩ : syracuseStep 2486453 = 233105) (by norm_num)
theorem B9441461 : Blo 1657528 9441461 := bbase (se 5 (by rfl) ⟨442568, by rfl⟩ : syracuseStep 9441461 = 885137) (by norm_num)
theorem B2486477 : Blo 1657528 2486477 := bbase (se 3 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 2486477 = 932429) (by norm_num)
theorem B6295765 : Blo 1657528 6295765 := bbase (se 7 (by rfl) ⟨73778, by rfl⟩ : syracuseStep 6295765 = 147557) (by norm_num)
theorem B3731669 : Blo 1657528 3731669 := bbase (se 7 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 3731669 = 87461) (by norm_num)
theorem B2486501 : Blo 1657528 2486501 := bbase (se 4 (by rfl) ⟨233109, by rfl⟩ : syracuseStep 2486501 = 466219) (by norm_num)
theorem B2486525 : Blo 1657528 2486525 := bbase (se 3 (by rfl) ⟨466223, by rfl⟩ : syracuseStep 2486525 = 932447) (by norm_num)
theorem B3150085 : Blo 1657528 3150085 := bbase (se 4 (by rfl) ⟨295320, by rfl⟩ : syracuseStep 3150085 = 590641) (by norm_num)
theorem B8401157 : Blo 1657528 8401157 := bbase (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) (by norm_num)
theorem B2486549 : Blo 1657528 2486549 := bbase (se 6 (by rfl) ⟨58278, by rfl⟩ : syracuseStep 2486549 = 116557) (by norm_num)
theorem B3731741 : Blo 1657528 3731741 := bbase (se 3 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 3731741 = 1399403) (by norm_num)
theorem B2797861 : Blo 1657528 2797861 := bbase (se 4 (by rfl) ⟨262299, by rfl⟩ : syracuseStep 2797861 = 524599) (by norm_num)
theorem B2486573 : Blo 1657528 2486573 := bbase (se 3 (by rfl) ⟨466232, by rfl⟩ : syracuseStep 2486573 = 932465) (by norm_num)
theorem B2486597 : Blo 1657528 2486597 := bbase (se 4 (by rfl) ⟨233118, by rfl⟩ : syracuseStep 2486597 = 466237) (by norm_num)
theorem B2486621 : Blo 1657528 2486621 := bbase (se 3 (by rfl) ⟨466241, by rfl⟩ : syracuseStep 2486621 = 932483) (by norm_num)
theorem B3731813 : Blo 1657528 3731813 := bbase (se 4 (by rfl) ⟨349857, by rfl⟩ : syracuseStep 3731813 = 699715) (by norm_num)
theorem B2486645 : Blo 1657528 2486645 := bbase (se 5 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 2486645 = 233123) (by norm_num)
theorem B2797949 : Blo 1657528 2797949 := bbase (se 3 (by rfl) ⟨524615, by rfl⟩ : syracuseStep 2797949 = 1049231) (by norm_num)
theorem B2240893 : Blo 1657528 2240893 := bbase (se 3 (by rfl) ⟨420167, by rfl⟩ : syracuseStep 2240893 = 840335) (by norm_num)
theorem B2486669 : Blo 1657528 2486669 := bbase (se 3 (by rfl) ⟨466250, by rfl⟩ : syracuseStep 2486669 = 932501) (by norm_num)
theorem B5599637 : Blo 1657528 5599637 := bbase (se 6 (by rfl) ⟨131241, by rfl⟩ : syracuseStep 5599637 = 262483) (by norm_num)
theorem B2486693 : Blo 1657528 2486693 := bbase (se 4 (by rfl) ⟨233127, by rfl⟩ : syracuseStep 2486693 = 466255) (by norm_num)
theorem B3150245 : Blo 1657528 3150245 := bbase (se 4 (by rfl) ⟨295335, by rfl⟩ : syracuseStep 3150245 = 590671) (by norm_num)
theorem B3731885 : Blo 1657528 3731885 := bbase (se 3 (by rfl) ⟨699728, by rfl⟩ : syracuseStep 3731885 = 1399457) (by norm_num)
theorem B4198837 : Blo 1657528 4198837 := bbase (se 5 (by rfl) ⟨196820, by rfl⟩ : syracuseStep 4198837 = 393641) (by norm_num)
theorem B2486717 : Blo 1657528 2486717 := bbase (se 3 (by rfl) ⟨466259, by rfl⟩ : syracuseStep 2486717 = 932519) (by norm_num)
theorem B2486741 : Blo 1657528 2486741 := bbase (se 7 (by rfl) ⟨29141, by rfl⟩ : syracuseStep 2486741 = 58283) (by norm_num)
theorem B54514133 : Blo 1657528 54514133 := bbase (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) (by norm_num)
theorem B3985885 : Blo 1657528 3985885 := bbase (se 3 (by rfl) ⟨747353, by rfl⟩ : syracuseStep 3985885 = 1494707) (by norm_num)
theorem B2486765 : Blo 1657528 2486765 := bbase (se 3 (by rfl) ⟨466268, by rfl⟩ : syracuseStep 2486765 = 932537) (by norm_num)
theorem B3731957 : Blo 1657528 3731957 := bbase (se 5 (by rfl) ⟨174935, by rfl⟩ : syracuseStep 3731957 = 349871) (by norm_num)
theorem B2798077 : Blo 1657528 2798077 := bbase (se 3 (by rfl) ⟨524639, by rfl⟩ : syracuseStep 2798077 = 1049279) (by norm_num)
theorem B2486789 : Blo 1657528 2486789 := bbase (se 4 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 2486789 = 466273) (by norm_num)
theorem B6296069 : Blo 1657528 6296069 := bbase (se 4 (by rfl) ⟨590256, by rfl⟩ : syracuseStep 6296069 = 1180513) (by norm_num)
theorem B2486813 : Blo 1657528 2486813 := bbase (se 3 (by rfl) ⟨466277, by rfl⟩ : syracuseStep 2486813 = 932555) (by norm_num)
theorem B4198949 : Blo 1657528 4198949 := bbase (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) (by norm_num)
theorem B2486837 : Blo 1657528 2486837 := bbase (se 5 (by rfl) ⟨116570, by rfl⟩ : syracuseStep 2486837 = 233141) (by norm_num)
theorem B3150389 : Blo 1657528 3150389 := bbase (se 5 (by rfl) ⟨147674, by rfl⟩ : syracuseStep 3150389 = 295349) (by norm_num)
theorem B3732029 : Blo 1657528 3732029 := bbase (se 3 (by rfl) ⟨699755, by rfl⟩ : syracuseStep 3732029 = 1399511) (by norm_num)
theorem B2486861 : Blo 1657528 2486861 := bbase (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) (by norm_num)
theorem B2798165 : Blo 1657528 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B2486885 : Blo 1657528 2486885 := bbase (se 4 (by rfl) ⟨233145, by rfl⟩ : syracuseStep 2486885 = 466291) (by norm_num)
theorem B2486909 : Blo 1657528 2486909 := bbase (se 3 (by rfl) ⟨466295, by rfl⟩ : syracuseStep 2486909 = 932591) (by norm_num)
theorem B3732101 : Blo 1657528 3732101 := bbase (se 4 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 3732101 = 699769) (by norm_num)
theorem B2486933 : Blo 1657528 2486933 := bbase (se 6 (by rfl) ⟨58287, by rfl⟩ : syracuseStep 2486933 = 116575) (by norm_num)
theorem B8393381 : Blo 1657528 8393381 := bbase (se 4 (by rfl) ⟨786879, by rfl⟩ : syracuseStep 8393381 = 1573759) (by norm_num)
theorem B2486957 : Blo 1657528 2486957 := bbase (se 3 (by rfl) ⟨466304, by rfl⟩ : syracuseStep 2486957 = 932609) (by norm_num)
theorem B8966837 : Blo 1657528 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B2486981 : Blo 1657528 2486981 := bbase (se 4 (by rfl) ⟨233154, by rfl⟩ : syracuseStep 2486981 = 466309) (by norm_num)
theorem B4723397 : Blo 1657528 4723397 := bbase (se 4 (by rfl) ⟨442818, by rfl⟩ : syracuseStep 4723397 = 885637) (by norm_num)
theorem B3732173 : Blo 1657528 3732173 := bbase (se 3 (by rfl) ⟨699782, by rfl⟩ : syracuseStep 3732173 = 1399565) (by norm_num)
theorem B2798293 : Blo 1657528 2798293 := bbase (se 7 (by rfl) ⟨32792, by rfl⟩ : syracuseStep 2798293 = 65585) (by norm_num)
theorem B2487005 : Blo 1657528 2487005 := bbase (se 3 (by rfl) ⟨466313, by rfl⟩ : syracuseStep 2487005 = 932627) (by norm_num)
theorem B4199141 : Blo 1657528 4199141 := bbase (se 4 (by rfl) ⟨393669, by rfl⟩ : syracuseStep 4199141 = 787339) (by norm_num)
theorem B2487029 : Blo 1657528 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B2487053 : Blo 1657528 2487053 := bbase (se 3 (by rfl) ⟨466322, by rfl⟩ : syracuseStep 2487053 = 932645) (by norm_num)
theorem B3543821 : Blo 1657528 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B3732245 : Blo 1657528 3732245 := bbase (se 6 (by rfl) ⟨87474, by rfl⟩ : syracuseStep 3732245 = 174949) (by norm_num)
theorem B2487077 : Blo 1657528 2487077 := bbase (se 4 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 2487077 = 466327) (by norm_num)
theorem B2798381 : Blo 1657528 2798381 := bbase (se 3 (by rfl) ⟨524696, by rfl⟩ : syracuseStep 2798381 = 1049393) (by norm_num)
theorem B2241325 : Blo 1657528 2241325 := bbase (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) (by norm_num)
theorem B2487101 : Blo 1657528 2487101 := bbase (se 3 (by rfl) ⟨466331, by rfl⟩ : syracuseStep 2487101 = 932663) (by norm_num)
theorem B5600069 : Blo 1657528 5600069 := bbase (se 4 (by rfl) ⟨525006, by rfl⟩ : syracuseStep 5600069 = 1050013) (by norm_num)
theorem B2487125 : Blo 1657528 2487125 := bbase (se 9 (by rfl) ⟨7286, by rfl⟩ : syracuseStep 2487125 = 14573) (by norm_num)
theorem B3732317 : Blo 1657528 3732317 := bbase (se 3 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 3732317 = 1399619) (by norm_num)
theorem B2487149 : Blo 1657528 2487149 := bbase (se 3 (by rfl) ⟨466340, by rfl⟩ : syracuseStep 2487149 = 932681) (by norm_num)
theorem B2487173 : Blo 1657528 2487173 := bbase (se 4 (by rfl) ⟨233172, by rfl⟩ : syracuseStep 2487173 = 466345) (by norm_num)
theorem B3986309 : Blo 1657528 3986309 := bbase (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) (by norm_num)
theorem B2487197 : Blo 1657528 2487197 := bbase (se 3 (by rfl) ⟨466349, by rfl⟩ : syracuseStep 2487197 = 932699) (by norm_num)
theorem B3732389 : Blo 1657528 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B2798509 : Blo 1657528 2798509 := bbase (se 3 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 2798509 = 1049441) (by norm_num)
theorem B2487221 : Blo 1657528 2487221 := bbase (se 5 (by rfl) ⟨116588, by rfl⟩ : syracuseStep 2487221 = 233177) (by norm_num)
theorem B2487245 : Blo 1657528 2487245 := bbase (se 3 (by rfl) ⟨466358, by rfl⟩ : syracuseStep 2487245 = 932717) (by norm_num)
theorem B2487269 : Blo 1657528 2487269 := bbase (se 4 (by rfl) ⟨233181, by rfl⟩ : syracuseStep 2487269 = 466363) (by norm_num)
theorem B3732461 : Blo 1657528 3732461 := bbase (se 3 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 3732461 = 1399673) (by norm_num)
theorem B2487293 : Blo 1657528 2487293 := bbase (se 3 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 2487293 = 932735) (by norm_num)
theorem B2798597 : Blo 1657528 2798597 := bbase (se 4 (by rfl) ⟨262368, by rfl⟩ : syracuseStep 2798597 = 524737) (by norm_num)
theorem B2987021 : Blo 1657528 2987021 := bbase (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) (by norm_num)
theorem B2487317 : Blo 1657528 2487317 := bbase (se 6 (by rfl) ⟨58296, by rfl⟩ : syracuseStep 2487317 = 116593) (by norm_num)
theorem B13448213 : Blo 1657528 13448213 := bbase (se 6 (by rfl) ⟨315192, by rfl⟩ : syracuseStep 13448213 = 630385) (by norm_num)
theorem B21263381 : Blo 1657528 21263381 := bbase (se 6 (by rfl) ⟨498360, by rfl⟩ : syracuseStep 21263381 = 996721) (by norm_num)
theorem B1864741 : Blo 1657528 1864741 := bbase (se 4 (by rfl) ⟨174819, by rfl⟩ : syracuseStep 1864741 = 349639) (by norm_num)
theorem B2126893 : Blo 1657528 2126893 := bbase (se 3 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 2126893 = 797585) (by norm_num)
theorem B2487341 : Blo 1657528 2487341 := bbase (se 3 (by rfl) ⟨466376, by rfl⟩ : syracuseStep 2487341 = 932753) (by norm_num)
theorem B3732533 : Blo 1657528 3732533 := bbase (se 5 (by rfl) ⟨174962, by rfl⟩ : syracuseStep 3732533 = 349925) (by norm_num)
theorem B4199485 : Blo 1657528 4199485 := bbase (se 3 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 4199485 = 1574807) (by norm_num)
theorem B2487365 : Blo 1657528 2487365 := bbase (se 4 (by rfl) ⟨233190, by rfl⟩ : syracuseStep 2487365 = 466381) (by norm_num)
theorem B1864777 : Blo 1657528 1864777 := bbase (se 2 (by rfl) ⟨699291, by rfl⟩ : syracuseStep 1864777 = 1398583) (by norm_num)
theorem B2487389 : Blo 1657528 2487389 := bbase (se 3 (by rfl) ⟨466385, by rfl⟩ : syracuseStep 2487389 = 932771) (by norm_num)
theorem B1864813 : Blo 1657528 1864813 := bbase (se 3 (by rfl) ⟨349652, by rfl⟩ : syracuseStep 1864813 = 699305) (by norm_num)
theorem B2487413 : Blo 1657528 2487413 := bbase (se 5 (by rfl) ⟨116597, by rfl⟩ : syracuseStep 2487413 = 233195) (by norm_num)
theorem B4723829 : Blo 1657528 4723829 := bbase (se 5 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 4723829 = 442859) (by norm_num)
theorem B3732605 : Blo 1657528 3732605 := bbase (se 3 (by rfl) ⟨699863, by rfl⟩ : syracuseStep 3732605 = 1399727) (by norm_num)
theorem B2798725 : Blo 1657528 2798725 := bbase (se 4 (by rfl) ⟨262380, by rfl⟩ : syracuseStep 2798725 = 524761) (by norm_num)
theorem B2487437 : Blo 1657528 2487437 := bbase (se 3 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 2487437 = 932789) (by norm_num)
theorem B1864849 : Blo 1657528 1864849 := bbase (se 2 (by rfl) ⟨699318, by rfl⟩ : syracuseStep 1864849 = 1398637) (by norm_num)
theorem B2987165 : Blo 1657528 2987165 := bbase (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) (by norm_num)
theorem B7967909 : Blo 1657528 7967909 := bbase (se 4 (by rfl) ⟨746991, by rfl⟩ : syracuseStep 7967909 = 1493983) (by norm_num)
theorem B2487461 : Blo 1657528 2487461 := bbase (se 4 (by rfl) ⟨233199, by rfl⟩ : syracuseStep 2487461 = 466399) (by norm_num)
theorem B3986597 : Blo 1657528 3986597 := bbase (se 4 (by rfl) ⟨373743, by rfl⟩ : syracuseStep 3986597 = 747487) (by norm_num)
theorem B4199597 : Blo 1657528 4199597 := bbase (se 3 (by rfl) ⟨787424, by rfl⟩ : syracuseStep 4199597 = 1574849) (by norm_num)
theorem B1864885 : Blo 1657528 1864885 := bbase (se 5 (by rfl) ⟨87416, by rfl⟩ : syracuseStep 1864885 = 174833) (by norm_num)
theorem B2487485 : Blo 1657528 2487485 := bbase (se 3 (by rfl) ⟨466403, by rfl⟩ : syracuseStep 2487485 = 932807) (by norm_num)
theorem B3732677 : Blo 1657528 3732677 := bbase (se 4 (by rfl) ⟨349938, by rfl⟩ : syracuseStep 3732677 = 699877) (by norm_num)
theorem B2487509 : Blo 1657528 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B1864921 : Blo 1657528 1864921 := bbase (se 2 (by rfl) ⟨699345, by rfl⟩ : syracuseStep 1864921 = 1398691) (by norm_num)
theorem B2798813 : Blo 1657528 2798813 := bbase (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) (by norm_num)
theorem B2987237 : Blo 1657528 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B2487533 : Blo 1657528 2487533 := bbase (se 3 (by rfl) ⟨466412, by rfl⟩ : syracuseStep 2487533 = 932825) (by norm_num)
theorem B5600501 : Blo 1657528 5600501 := bbase (se 5 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 5600501 = 525047) (by norm_num)
theorem B1864957 : Blo 1657528 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B2487557 : Blo 1657528 2487557 := bbase (se 4 (by rfl) ⟨233208, by rfl⟩ : syracuseStep 2487557 = 466417) (by norm_num)
theorem B3732749 : Blo 1657528 3732749 := bbase (se 3 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 3732749 = 1399781) (by norm_num)
theorem B2692381 : Blo 1657528 2692381 := bbase (se 3 (by rfl) ⟨504821, by rfl⟩ : syracuseStep 2692381 = 1009643) (by norm_num)
theorem B2487581 : Blo 1657528 2487581 := bbase (se 3 (by rfl) ⟨466421, by rfl⟩ : syracuseStep 2487581 = 932843) (by norm_num)
theorem B1864993 : Blo 1657528 1864993 := bbase (se 2 (by rfl) ⟨699372, by rfl⟩ : syracuseStep 1864993 = 1398745) (by norm_num)
theorem B2487605 : Blo 1657528 2487605 := bbase (se 5 (by rfl) ⟨116606, by rfl⟩ : syracuseStep 2487605 = 233213) (by norm_num)
theorem B1865029 : Blo 1657528 1865029 := bbase (se 4 (by rfl) ⟨174846, by rfl⟩ : syracuseStep 1865029 = 349693) (by norm_num)
theorem B2487629 : Blo 1657528 2487629 := bbase (se 3 (by rfl) ⟨466430, by rfl⟩ : syracuseStep 2487629 = 932861) (by norm_num)
theorem B3732821 : Blo 1657528 3732821 := bbase (se 13 (by rfl) ⟨683, by rfl⟩ : syracuseStep 3732821 = 1367) (by norm_num)
theorem B2798941 : Blo 1657528 2798941 := bbase (se 3 (by rfl) ⟨524801, by rfl⟩ : syracuseStep 2798941 = 1049603) (by norm_num)
theorem B2487653 : Blo 1657528 2487653 := bbase (se 4 (by rfl) ⟨233217, by rfl⟩ : syracuseStep 2487653 = 466435) (by norm_num)
theorem B1865065 : Blo 1657528 1865065 := bbase (se 2 (by rfl) ⟨699399, by rfl⟩ : syracuseStep 1865065 = 1398799) (by norm_num)
theorem B4199789 : Blo 1657528 4199789 := bbase (se 3 (by rfl) ⟨787460, by rfl⟩ : syracuseStep 4199789 = 1574921) (by norm_num)
theorem B2127217 : Blo 1657528 2127217 := bbase (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) (by norm_num)
theorem B2487677 : Blo 1657528 2487677 := bbase (se 3 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 2487677 = 932879) (by norm_num)
theorem B1865101 : Blo 1657528 1865101 := bbase (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) (by norm_num)
theorem B2487701 : Blo 1657528 2487701 := bbase (se 6 (by rfl) ⟨58305, by rfl⟩ : syracuseStep 2487701 = 116611) (by norm_num)
theorem B3732893 : Blo 1657528 3732893 := bbase (se 3 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 3732893 = 1399835) (by norm_num)
theorem B2487725 : Blo 1657528 2487725 := bbase (se 3 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 2487725 = 932897) (by norm_num)
theorem B1865137 : Blo 1657528 1865137 := bbase (se 2 (by rfl) ⟨699426, by rfl⟩ : syracuseStep 1865137 = 1398853) (by norm_num)
theorem B2799029 : Blo 1657528 2799029 := bbase (se 5 (by rfl) ⟨131204, by rfl⟩ : syracuseStep 2799029 = 262409) (by norm_num)
theorem B2487749 : Blo 1657528 2487749 := bbase (se 4 (by rfl) ⟨233226, by rfl⟩ : syracuseStep 2487749 = 466453) (by norm_num)
theorem B1865173 : Blo 1657528 1865173 := bbase (se 7 (by rfl) ⟨21857, by rfl⟩ : syracuseStep 1865173 = 43715) (by norm_num)
theorem B2487773 : Blo 1657528 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B3732965 : Blo 1657528 3732965 := bbase (se 4 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 3732965 = 699931) (by norm_num)
theorem B2487797 : Blo 1657528 2487797 := bbase (se 5 (by rfl) ⟨116615, by rfl⟩ : syracuseStep 2487797 = 233231) (by norm_num)
theorem B1865209 : Blo 1657528 1865209 := bbase (se 2 (by rfl) ⟨699453, by rfl⟩ : syracuseStep 1865209 = 1398907) (by norm_num)
theorem B2487821 : Blo 1657528 2487821 := bbase (se 3 (by rfl) ⟨466466, by rfl⟩ : syracuseStep 2487821 = 932933) (by norm_num)
theorem B1865245 : Blo 1657528 1865245 := bbase (se 3 (by rfl) ⟨349733, by rfl⟩ : syracuseStep 1865245 = 699467) (by norm_num)
theorem B7083557 : Blo 1657528 7083557 := bbase (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) (by norm_num)
theorem B2487845 : Blo 1657528 2487845 := bbase (se 4 (by rfl) ⟨233235, by rfl⟩ : syracuseStep 2487845 = 466471) (by norm_num)
theorem B3733037 : Blo 1657528 3733037 := bbase (se 3 (by rfl) ⟨699944, by rfl⟩ : syracuseStep 3733037 = 1399889) (by norm_num)
theorem B2799157 : Blo 1657528 2799157 := bbase (se 5 (by rfl) ⟨131210, by rfl⟩ : syracuseStep 2799157 = 262421) (by norm_num)
theorem B2487869 : Blo 1657528 2487869 := bbase (se 3 (by rfl) ⟨466475, by rfl⟩ : syracuseStep 2487869 = 932951) (by norm_num)
theorem B1865281 : Blo 1657528 1865281 := bbase (se 2 (by rfl) ⟨699480, by rfl⟩ : syracuseStep 1865281 = 1398961) (by norm_num)
theorem B2487893 : Blo 1657528 2487893 := bbase (se 8 (by rfl) ⟨14577, by rfl⟩ : syracuseStep 2487893 = 29155) (by norm_num)
theorem B1865317 : Blo 1657528 1865317 := bbase (se 4 (by rfl) ⟨174873, by rfl⟩ : syracuseStep 1865317 = 349747) (by norm_num)
theorem B2487917 : Blo 1657528 2487917 := bbase (se 3 (by rfl) ⟨466484, by rfl⟩ : syracuseStep 2487917 = 932969) (by norm_num)
theorem B3733109 : Blo 1657528 3733109 := bbase (se 5 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 3733109 = 349979) (by norm_num)
theorem B2487941 : Blo 1657528 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B1865353 : Blo 1657528 1865353 := bbase (se 2 (by rfl) ⟨699507, by rfl⟩ : syracuseStep 1865353 = 1399015) (by norm_num)
theorem B2799245 : Blo 1657528 2799245 := bbase (se 3 (by rfl) ⟨524858, by rfl⟩ : syracuseStep 2799245 = 1049717) (by norm_num)
theorem B2487965 : Blo 1657528 2487965 := bbase (se 3 (by rfl) ⟨466493, by rfl⟩ : syracuseStep 2487965 = 932987) (by norm_num)
theorem B1865389 : Blo 1657528 1865389 := bbase (se 3 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 1865389 = 699521) (by norm_num)
theorem B2487989 : Blo 1657528 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B3733181 : Blo 1657528 3733181 := bbase (se 3 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 3733181 = 1399943) (by norm_num)
theorem B4200133 : Blo 1657528 4200133 := bbase (se 4 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 4200133 = 787525) (by norm_num)
theorem B2488013 : Blo 1657528 2488013 := bbase (se 3 (by rfl) ⟨466502, by rfl⟩ : syracuseStep 2488013 = 933005) (by norm_num)
theorem B1865425 : Blo 1657528 1865425 := bbase (se 2 (by rfl) ⟨699534, by rfl⟩ : syracuseStep 1865425 = 1399069) (by norm_num)
theorem B2488037 : Blo 1657528 2488037 := bbase (se 4 (by rfl) ⟨233253, by rfl⟩ : syracuseStep 2488037 = 466507) (by norm_num)
theorem B1865461 : Blo 1657528 1865461 := bbase (se 5 (by rfl) ⟨87443, by rfl⟩ : syracuseStep 1865461 = 174887) (by norm_num)
theorem B2488061 : Blo 1657528 2488061 := bbase (se 3 (by rfl) ⟨466511, by rfl⟩ : syracuseStep 2488061 = 933023) (by norm_num)
theorem B3733253 : Blo 1657528 3733253 := bbase (se 4 (by rfl) ⟨349992, by rfl⟩ : syracuseStep 3733253 = 699985) (by norm_num)
theorem B2799373 : Blo 1657528 2799373 := bbase (se 3 (by rfl) ⟨524882, by rfl⟩ : syracuseStep 2799373 = 1049765) (by norm_num)
theorem B2488085 : Blo 1657528 2488085 := bbase (se 6 (by rfl) ⟨58314, by rfl⟩ : syracuseStep 2488085 = 116629) (by norm_num)
theorem B1865497 : Blo 1657528 1865497 := bbase (se 2 (by rfl) ⟨699561, by rfl⟩ : syracuseStep 1865497 = 1399123) (by norm_num)
theorem B7567141 : Blo 1657528 7567141 := bbase (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) (by norm_num)
theorem B2488109 : Blo 1657528 2488109 := bbase (se 3 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 2488109 = 933041) (by norm_num)
theorem B4200245 : Blo 1657528 4200245 := bbase (se 5 (by rfl) ⟨196886, by rfl⟩ : syracuseStep 4200245 = 393773) (by norm_num)
theorem B1865533 : Blo 1657528 1865533 := bbase (se 3 (by rfl) ⟨349787, by rfl⟩ : syracuseStep 1865533 = 699575) (by norm_num)
theorem B2488133 : Blo 1657528 2488133 := bbase (se 4 (by rfl) ⟨233262, by rfl⟩ : syracuseStep 2488133 = 466525) (by norm_num)
theorem B3733325 : Blo 1657528 3733325 := bbase (se 3 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 3733325 = 1399997) (by norm_num)
theorem B9451349 : Blo 1657528 9451349 := bbase (se 9 (by rfl) ⟨27689, by rfl⟩ : syracuseStep 9451349 = 55379) (by norm_num)
theorem B2488157 : Blo 1657528 2488157 := bbase (se 3 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 2488157 = 933059) (by norm_num)
theorem B1865569 : Blo 1657528 1865569 := bbase (se 2 (by rfl) ⟨699588, by rfl⟩ : syracuseStep 1865569 = 1399177) (by norm_num)
theorem B2799461 : Blo 1657528 2799461 := bbase (se 4 (by rfl) ⟨262449, by rfl⟩ : syracuseStep 2799461 = 524899) (by norm_num)
theorem B4724581 : Blo 1657528 4724581 := bbase (se 4 (by rfl) ⟨442929, by rfl⟩ : syracuseStep 4724581 = 885859) (by norm_num)
theorem B4790117 : Blo 1657528 4790117 := bbase (se 4 (by rfl) ⟨449073, by rfl⟩ : syracuseStep 4790117 = 898147) (by norm_num)
theorem B2488181 : Blo 1657528 2488181 := bbase (se 5 (by rfl) ⟨116633, by rfl⟩ : syracuseStep 2488181 = 233267) (by norm_num)
theorem B1865605 : Blo 1657528 1865605 := bbase (se 4 (by rfl) ⟨174900, by rfl⟩ : syracuseStep 1865605 = 349801) (by norm_num)
theorem B2488205 : Blo 1657528 2488205 := bbase (se 3 (by rfl) ⟨466538, by rfl⟩ : syracuseStep 2488205 = 933077) (by norm_num)
theorem B3733397 : Blo 1657528 3733397 := bbase (se 6 (by rfl) ⟨87501, by rfl⟩ : syracuseStep 3733397 = 175003) (by norm_num)
theorem B2488229 : Blo 1657528 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1865641 : Blo 1657528 1865641 := bbase (se 2 (by rfl) ⟨699615, by rfl⟩ : syracuseStep 1865641 = 1399231) (by norm_num)
theorem B8394677 : Blo 1657528 8394677 := bbase (se 5 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 8394677 = 787001) (by norm_num)
theorem B2488253 : Blo 1657528 2488253 := bbase (se 3 (by rfl) ⟨466547, by rfl⟩ : syracuseStep 2488253 = 933095) (by norm_num)
theorem B5314501 : Blo 1657528 5314501 := bbase (se 4 (by rfl) ⟨498234, by rfl⟩ : syracuseStep 5314501 = 996469) (by norm_num)
theorem B1865677 : Blo 1657528 1865677 := bbase (se 3 (by rfl) ⟨349814, by rfl⟩ : syracuseStep 1865677 = 699629) (by norm_num)
theorem B25524181 : Blo 1657528 25524181 := bbase (se 7 (by rfl) ⟨299111, by rfl⟩ : syracuseStep 25524181 = 598223) (by norm_num)
theorem B2488277 : Blo 1657528 2488277 := bbase (se 7 (by rfl) ⟨29159, by rfl⟩ : syracuseStep 2488277 = 58319) (by norm_num)
theorem B3733469 : Blo 1657528 3733469 := bbase (se 3 (by rfl) ⟨700025, by rfl⟩ : syracuseStep 3733469 = 1400051) (by norm_num)
theorem B2799589 : Blo 1657528 2799589 := bbase (se 4 (by rfl) ⟨262461, by rfl⟩ : syracuseStep 2799589 = 524923) (by norm_num)
theorem B2488301 : Blo 1657528 2488301 := bbase (se 3 (by rfl) ⟨466556, by rfl⟩ : syracuseStep 2488301 = 933113) (by norm_num)
theorem B1865713 : Blo 1657528 1865713 := bbase (se 2 (by rfl) ⟨699642, by rfl⟩ : syracuseStep 1865713 = 1399285) (by norm_num)
theorem B4200437 : Blo 1657528 4200437 := bbase (se 5 (by rfl) ⟨196895, by rfl⟩ : syracuseStep 4200437 = 393791) (by norm_num)
theorem B2488325 : Blo 1657528 2488325 := bbase (se 4 (by rfl) ⟨233280, by rfl⟩ : syracuseStep 2488325 = 466561) (by norm_num)
theorem B5314565 : Blo 1657528 5314565 := bbase (se 4 (by rfl) ⟨498240, by rfl⟩ : syracuseStep 5314565 = 996481) (by norm_num)
theorem B1865749 : Blo 1657528 1865749 := bbase (se 6 (by rfl) ⟨43728, by rfl⟩ : syracuseStep 1865749 = 87457) (by norm_num)
theorem B2488349 : Blo 1657528 2488349 := bbase (se 3 (by rfl) ⟨466565, by rfl⟩ : syracuseStep 2488349 = 933131) (by norm_num)
theorem B3733541 : Blo 1657528 3733541 := bbase (se 4 (by rfl) ⟨350019, by rfl⟩ : syracuseStep 3733541 = 700039) (by norm_num)
theorem B2488373 : Blo 1657528 2488373 := bbase (se 5 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 2488373 = 233285) (by norm_num)
theorem B1865785 : Blo 1657528 1865785 := bbase (se 2 (by rfl) ⟨699669, by rfl⟩ : syracuseStep 1865785 = 1399339) (by norm_num)
theorem B2799677 : Blo 1657528 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B2488397 : Blo 1657528 2488397 := bbase (se 3 (by rfl) ⟨466574, by rfl⟩ : syracuseStep 2488397 = 933149) (by norm_num)
theorem B1865821 : Blo 1657528 1865821 := bbase (se 3 (by rfl) ⟨349841, by rfl⟩ : syracuseStep 1865821 = 699683) (by norm_num)
theorem B2488421 : Blo 1657528 2488421 := bbase (se 4 (by rfl) ⟨233289, by rfl⟩ : syracuseStep 2488421 = 466579) (by norm_num)
theorem B3733613 : Blo 1657528 3733613 := bbase (se 3 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 3733613 = 1400105) (by norm_num)
theorem B10090613 : Blo 1657528 10090613 := bbase (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) (by norm_num)
theorem B2046073 : Blo 1657528 2046073 := bbase (se 2 (by rfl) ⟨767277, by rfl⟩ : syracuseStep 2046073 = 1534555) (by norm_num)
theorem B2488445 : Blo 1657528 2488445 := bbase (se 3 (by rfl) ⟨466583, by rfl⟩ : syracuseStep 2488445 = 933167) (by norm_num)
theorem B1865857 : Blo 1657528 1865857 := bbase (se 2 (by rfl) ⟨699696, by rfl⟩ : syracuseStep 1865857 = 1399393) (by norm_num)
theorem B2488469 : Blo 1657528 2488469 := bbase (se 6 (by rfl) ⟨58323, by rfl⟩ : syracuseStep 2488469 = 116647) (by norm_num)
theorem B1865893 : Blo 1657528 1865893 := bbase (se 4 (by rfl) ⟨174927, by rfl⟩ : syracuseStep 1865893 = 349855) (by norm_num)
theorem B2488493 : Blo 1657528 2488493 := bbase (se 3 (by rfl) ⟨466592, by rfl⟩ : syracuseStep 2488493 = 933185) (by norm_num)
theorem B3733685 : Blo 1657528 3733685 := bbase (se 5 (by rfl) ⟨175016, by rfl⟩ : syracuseStep 3733685 = 350033) (by norm_num)
theorem B2799805 : Blo 1657528 2799805 := bbase (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) (by norm_num)
theorem B2488517 : Blo 1657528 2488517 := bbase (se 4 (by rfl) ⟨233298, by rfl⟩ : syracuseStep 2488517 = 466597) (by norm_num)
theorem B1865929 : Blo 1657528 1865929 := bbase (se 2 (by rfl) ⟨699723, by rfl⟩ : syracuseStep 1865929 = 1399447) (by norm_num)
theorem B2488541 : Blo 1657528 2488541 := bbase (se 3 (by rfl) ⟨466601, by rfl⟩ : syracuseStep 2488541 = 933203) (by norm_num)
theorem B1865965 : Blo 1657528 1865965 := bbase (se 3 (by rfl) ⟨349868, by rfl⟩ : syracuseStep 1865965 = 699737) (by norm_num)
theorem B2488565 : Blo 1657528 2488565 := bbase (se 5 (by rfl) ⟨116651, by rfl⟩ : syracuseStep 2488565 = 233303) (by norm_num)
theorem B3733757 : Blo 1657528 3733757 := bbase (se 3 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 3733757 = 1400159) (by norm_num)
theorem B2488589 : Blo 1657528 2488589 := bbase (se 3 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 2488589 = 933221) (by norm_num)
theorem B1866001 : Blo 1657528 1866001 := bbase (se 2 (by rfl) ⟨699750, by rfl⟩ : syracuseStep 1866001 = 1399501) (by norm_num)
theorem B2799893 : Blo 1657528 2799893 := bbase (se 6 (by rfl) ⟨65622, by rfl⟩ : syracuseStep 2799893 = 131245) (by norm_num)
theorem B2488613 : Blo 1657528 2488613 := bbase (se 4 (by rfl) ⟨233307, by rfl⟩ : syracuseStep 2488613 = 466615) (by norm_num)
theorem B5388581 : Blo 1657528 5388581 := bbase (se 4 (by rfl) ⟨505179, by rfl⟩ : syracuseStep 5388581 = 1010359) (by norm_num)
theorem B1866037 : Blo 1657528 1866037 := bbase (se 5 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 1866037 = 174941) (by norm_num)
theorem B2488637 : Blo 1657528 2488637 := bbase (se 3 (by rfl) ⟨466619, by rfl⟩ : syracuseStep 2488637 = 933239) (by norm_num)
theorem B3733829 : Blo 1657528 3733829 := bbase (se 4 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 3733829 = 700093) (by norm_num)
theorem B2488661 : Blo 1657528 2488661 := bbase (se 10 (by rfl) ⟨3645, by rfl⟩ : syracuseStep 2488661 = 7291) (by norm_num)
theorem B1866073 : Blo 1657528 1866073 := bbase (se 2 (by rfl) ⟨699777, by rfl⟩ : syracuseStep 1866073 = 1399555) (by norm_num)
theorem B1890653 : Blo 1657528 1890653 := bbase (se 3 (by rfl) ⟨354497, by rfl⟩ : syracuseStep 1890653 = 708995) (by norm_num)
theorem B2488685 : Blo 1657528 2488685 := bbase (se 3 (by rfl) ⟨466628, by rfl⟩ : syracuseStep 2488685 = 933257) (by norm_num)
theorem B1866109 : Blo 1657528 1866109 := bbase (se 3 (by rfl) ⟨349895, by rfl⟩ : syracuseStep 1866109 = 699791) (by norm_num)
theorem B2488709 : Blo 1657528 2488709 := bbase (se 4 (by rfl) ⟨233316, by rfl⟩ : syracuseStep 2488709 = 466633) (by norm_num)
theorem B3733901 : Blo 1657528 3733901 := bbase (se 3 (by rfl) ⟨700106, by rfl⟩ : syracuseStep 3733901 = 1400213) (by norm_num)
theorem B2800021 : Blo 1657528 2800021 := bbase (se 6 (by rfl) ⟨65625, by rfl⟩ : syracuseStep 2800021 = 131251) (by norm_num)
theorem B1890713 : Blo 1657528 1890713 := bbase (se 2 (by rfl) ⟨709017, by rfl⟩ : syracuseStep 1890713 = 1418035) (by norm_num)
theorem B2128285 : Blo 1657528 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B2488733 : Blo 1657528 2488733 := bbase (se 3 (by rfl) ⟨466637, by rfl⟩ : syracuseStep 2488733 = 933275) (by norm_num)
theorem B1866145 : Blo 1657528 1866145 := bbase (se 2 (by rfl) ⟨699804, by rfl⟩ : syracuseStep 1866145 = 1399609) (by norm_num)
theorem B2488757 : Blo 1657528 2488757 := bbase (se 5 (by rfl) ⟨116660, by rfl⟩ : syracuseStep 2488757 = 233321) (by norm_num)
theorem B2988485 : Blo 1657528 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B1866181 : Blo 1657528 1866181 := bbase (se 4 (by rfl) ⟨174954, by rfl⟩ : syracuseStep 1866181 = 349909) (by norm_num)
theorem B2488781 : Blo 1657528 2488781 := bbase (se 3 (by rfl) ⟨466646, by rfl⟩ : syracuseStep 2488781 = 933293) (by norm_num)
theorem B2488805 : Blo 1657528 2488805 := bbase (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) (by norm_num)
theorem B1866217 : Blo 1657528 1866217 := bbase (se 2 (by rfl) ⟨699831, by rfl⟩ : syracuseStep 1866217 = 1399663) (by norm_num)
theorem B2800109 : Blo 1657528 2800109 := bbase (se 3 (by rfl) ⟨525020, by rfl⟩ : syracuseStep 2800109 = 1050041) (by norm_num)
theorem B2488829 : Blo 1657528 2488829 := bbase (se 3 (by rfl) ⟨466655, by rfl⟩ : syracuseStep 2488829 = 933311) (by norm_num)
theorem B1866253 : Blo 1657528 1866253 := bbase (se 3 (by rfl) ⟨349922, by rfl⟩ : syracuseStep 1866253 = 699845) (by norm_num)
theorem B2488853 : Blo 1657528 2488853 := bbase (se 6 (by rfl) ⟨58332, by rfl⟩ : syracuseStep 2488853 = 116665) (by norm_num)
theorem B2488877 : Blo 1657528 2488877 := bbase (se 3 (by rfl) ⟨466664, by rfl⟩ : syracuseStep 2488877 = 933329) (by norm_num)
theorem B1866289 : Blo 1657528 1866289 := bbase (se 2 (by rfl) ⟨699858, by rfl⟩ : syracuseStep 1866289 = 1399717) (by norm_num)
theorem B6298181 : Blo 1657528 6298181 := bbase (se 4 (by rfl) ⟨590454, by rfl⟩ : syracuseStep 6298181 = 1180909) (by norm_num)
theorem B2488901 : Blo 1657528 2488901 := bbase (se 4 (by rfl) ⟨233334, by rfl⟩ : syracuseStep 2488901 = 466669) (by norm_num)
theorem B1866325 : Blo 1657528 1866325 := bbase (se 8 (by rfl) ⟨10935, by rfl⟩ : syracuseStep 1866325 = 21871) (by norm_num)
theorem B2488925 : Blo 1657528 2488925 := bbase (se 3 (by rfl) ⟨466673, by rfl⟩ : syracuseStep 2488925 = 933347) (by norm_num)
theorem B2800237 : Blo 1657528 2800237 := bbase (se 3 (by rfl) ⟨525044, by rfl⟩ : syracuseStep 2800237 = 1050089) (by norm_num)
theorem B2488949 : Blo 1657528 2488949 := bbase (se 5 (by rfl) ⟨116669, by rfl⟩ : syracuseStep 2488949 = 233339) (by norm_num)
theorem B1866361 : Blo 1657528 1866361 := bbase (se 2 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 1866361 = 1399771) (by norm_num)
theorem B5675653 : Blo 1657528 5675653 := bbase (se 4 (by rfl) ⟨532092, by rfl⟩ : syracuseStep 5675653 = 1064185) (by norm_num)
theorem B2488973 : Blo 1657528 2488973 := bbase (se 3 (by rfl) ⟨466682, by rfl⟩ : syracuseStep 2488973 = 933365) (by norm_num)
theorem B1866397 : Blo 1657528 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B2488997 : Blo 1657528 2488997 := bbase (se 4 (by rfl) ⟨233343, by rfl⟩ : syracuseStep 2488997 = 466687) (by norm_num)
theorem B12114613 : Blo 1657528 12114613 := bbase (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) (by norm_num)
theorem B2489021 : Blo 1657528 2489021 := bbase (se 3 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 2489021 = 933383) (by norm_num)
theorem B1891009 : Blo 1657528 1891009 := bbase (se 2 (by rfl) ⟨709128, by rfl⟩ : syracuseStep 1891009 = 1418257) (by norm_num)
theorem B1866433 : Blo 1657528 1866433 := bbase (se 2 (by rfl) ⟨699912, by rfl⟩ : syracuseStep 1866433 = 1399825) (by norm_num)
theorem B2800325 : Blo 1657528 2800325 := bbase (se 4 (by rfl) ⟨262530, by rfl⟩ : syracuseStep 2800325 = 525061) (by norm_num)
theorem B2489045 : Blo 1657528 2489045 := bbase (se 7 (by rfl) ⟨29168, by rfl⟩ : syracuseStep 2489045 = 58337) (by norm_num)
theorem B1891045 : Blo 1657528 1891045 := bbase (se 4 (by rfl) ⟨177285, by rfl⟩ : syracuseStep 1891045 = 354571) (by norm_num)
theorem B1866469 : Blo 1657528 1866469 := bbase (se 4 (by rfl) ⟨174981, by rfl⟩ : syracuseStep 1866469 = 349963) (by norm_num)
theorem B2489069 : Blo 1657528 2489069 := bbase (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) (by norm_num)
theorem B2489093 : Blo 1657528 2489093 := bbase (se 4 (by rfl) ⟨233352, by rfl⟩ : syracuseStep 2489093 = 466705) (by norm_num)
theorem B1866505 : Blo 1657528 1866505 := bbase (se 2 (by rfl) ⟨699939, by rfl⟩ : syracuseStep 1866505 = 1399879) (by norm_num)
theorem B2489117 : Blo 1657528 2489117 := bbase (se 3 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 2489117 = 933419) (by norm_num)
theorem B1866541 : Blo 1657528 1866541 := bbase (se 3 (by rfl) ⟨349976, by rfl⟩ : syracuseStep 1866541 = 699953) (by norm_num)
theorem B2489141 : Blo 1657528 2489141 := bbase (se 5 (by rfl) ⟨116678, by rfl⟩ : syracuseStep 2489141 = 233357) (by norm_num)
theorem B2800453 : Blo 1657528 2800453 := bbase (se 4 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 2800453 = 525085) (by norm_num)
theorem B2489165 : Blo 1657528 2489165 := bbase (se 3 (by rfl) ⟨466718, by rfl⟩ : syracuseStep 2489165 = 933437) (by norm_num)
theorem B1866577 : Blo 1657528 1866577 := bbase (se 2 (by rfl) ⟨699966, by rfl⟩ : syracuseStep 1866577 = 1399933) (by norm_num)
theorem B6298469 : Blo 1657528 6298469 := bbase (se 4 (by rfl) ⟨590481, by rfl⟩ : syracuseStep 6298469 = 1180963) (by norm_num)
theorem B2489189 : Blo 1657528 2489189 := bbase (se 4 (by rfl) ⟨233361, by rfl⟩ : syracuseStep 2489189 = 466723) (by norm_num)
theorem B1866613 : Blo 1657528 1866613 := bbase (se 5 (by rfl) ⟨87497, by rfl⟩ : syracuseStep 1866613 = 174995) (by norm_num)
theorem B2489213 : Blo 1657528 2489213 := bbase (se 3 (by rfl) ⟨466727, by rfl⟩ : syracuseStep 2489213 = 933455) (by norm_num)
theorem B5045125 : Blo 1657528 5045125 := bbase (se 4 (by rfl) ⟨472980, by rfl⟩ : syracuseStep 5045125 = 945961) (by norm_num)
theorem B2489237 : Blo 1657528 2489237 := bbase (se 6 (by rfl) ⟨58341, by rfl⟩ : syracuseStep 2489237 = 116683) (by norm_num)
theorem B1866649 : Blo 1657528 1866649 := bbase (se 2 (by rfl) ⟨699993, by rfl⟩ : syracuseStep 1866649 = 1399987) (by norm_num)
theorem B2522021 : Blo 1657528 2522021 := bbase (se 4 (by rfl) ⟨236439, by rfl⟩ : syracuseStep 2522021 = 472879) (by norm_num)
theorem B2489261 : Blo 1657528 2489261 := bbase (se 3 (by rfl) ⟨466736, by rfl⟩ : syracuseStep 2489261 = 933473) (by norm_num)
theorem B1866685 : Blo 1657528 1866685 := bbase (se 3 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 1866685 = 700007) (by norm_num)
theorem B2489285 : Blo 1657528 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B1891297 : Blo 1657528 1891297 := bbase (se 2 (by rfl) ⟨709236, by rfl⟩ : syracuseStep 1891297 = 1418473) (by norm_num)
theorem B1866721 : Blo 1657528 1866721 := bbase (se 2 (by rfl) ⟨700020, by rfl⟩ : syracuseStep 1866721 = 1400041) (by norm_num)
theorem B1866757 : Blo 1657528 1866757 := bbase (se 4 (by rfl) ⟨175008, by rfl⟩ : syracuseStep 1866757 = 350017) (by norm_num)
theorem B5045269 : Blo 1657528 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B1866793 : Blo 1657528 1866793 := bbase (se 2 (by rfl) ⟨700047, by rfl⟩ : syracuseStep 1866793 = 1400095) (by norm_num)
theorem B2522173 : Blo 1657528 2522173 := bbase (se 3 (by rfl) ⟨472907, by rfl⟩ : syracuseStep 2522173 = 945815) (by norm_num)
theorem B1866829 : Blo 1657528 1866829 := bbase (se 3 (by rfl) ⟨350030, by rfl⟩ : syracuseStep 1866829 = 700061) (by norm_num)
theorem B86170709 : Blo 1657528 86170709 := bbase (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) (by norm_num)
theorem B1866865 : Blo 1657528 1866865 := bbase (se 2 (by rfl) ⟨700074, by rfl⟩ : syracuseStep 1866865 = 1400149) (by norm_num)
theorem B1866901 : Blo 1657528 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B1866937 : Blo 1657528 1866937 := bbase (se 2 (by rfl) ⟨700101, by rfl⟩ : syracuseStep 1866937 = 1400203) (by norm_num)
theorem B8395973 : Blo 1657528 8395973 := bbase (se 4 (by rfl) ⟨787122, by rfl⟩ : syracuseStep 8395973 = 1574245) (by norm_num)
theorem B3783917 : Blo 1657528 3783917 := bbase (se 3 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 3783917 = 1418969) (by norm_num)
theorem B8961301 : Blo 1657528 8961301 := bbase (se 6 (by rfl) ⟨210030, by rfl⟩ : syracuseStep 8961301 = 420061) (by norm_num)
theorem B7085333 : Blo 1657528 7085333 := bbase (se 6 (by rfl) ⟨166062, by rfl⟩ : syracuseStep 7085333 = 332125) (by norm_num)
theorem B3783989 : Blo 1657528 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B5594453 : Blo 1657528 5594453 := bbase (se 11 (by rfl) ⟨4097, by rfl⟩ : syracuseStep 5594453 = 8195) (by norm_num)
theorem B21241237 : Blo 1657528 21241237 := bbase (se 6 (by rfl) ⟨497841, by rfl⟩ : syracuseStep 21241237 = 995683) (by norm_num)
theorem B7970309 : Blo 1657528 7970309 := bbase (se 4 (by rfl) ⟨747216, by rfl⟩ : syracuseStep 7970309 = 1494433) (by norm_num)
theorem B1916605 : Blo 1657528 1916605 := bbase (se 3 (by rfl) ⟨359363, by rfl⟩ : syracuseStep 1916605 = 718727) (by norm_num)
theorem B5594885 : Blo 1657528 5594885 := bbase (se 4 (by rfl) ⟨524520, by rfl⟩ : syracuseStep 5594885 = 1049041) (by norm_num)
theorem B4038437 : Blo 1657528 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B3030901 : Blo 1657528 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B9445517 : Blo 1657528 9445517 := bstep (se 3 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 9445517 = 3542069) B3542069
theorem B2728097 : Blo 1657528 2728097 := bstep (se 2 (by rfl) ⟨1023036, by rfl⟩ : syracuseStep 2728097 = 2046073) B2046073
theorem B5595533 : Blo 1657528 5595533 := bstep (se 3 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 5595533 = 2098325) B2098325
theorem B5595587 : Blo 1657528 5595587 := bstep (se 1 (by rfl) ⟨4196690, by rfl⟩ : syracuseStep 5595587 = 8393381) B8393381
theorem B8962531 : Blo 1657528 8962531 := bstep (se 1 (by rfl) ⟨6721898, by rfl⟩ : syracuseStep 8962531 = 13443797) B13443797
theorem B17932853 : Blo 1657528 17932853 := bstep (se 5 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 17932853 = 1681205) B1681205
theorem B11960945 : Blo 1657528 11960945 := bstep (se 2 (by rfl) ⟨4485354, by rfl⟩ : syracuseStep 11960945 = 8970709) B8970709
theorem B3687043 : Blo 1657528 3687043 := bstep (se 1 (by rfl) ⟨2765282, by rfl⟩ : syracuseStep 3687043 = 5530565) B5530565
theorem B1991347 : Blo 1657528 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B30270149 : Blo 1657528 30270149 := bstep (se 4 (by rfl) ⟨2837826, by rfl⟩ : syracuseStep 30270149 = 5675653) B5675653
theorem B5595857 : Blo 1657528 5595857 := bstep (se 2 (by rfl) ⟨2098446, by rfl⟩ : syracuseStep 5595857 = 4196893) B4196893
theorem B12600035 : Blo 1657528 12600035 := bstep (se 1 (by rfl) ⟨9450026, by rfl⟩ : syracuseStep 12600035 = 18900053) B18900053
theorem B2098163 : Blo 1657528 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B10085381 : Blo 1657528 10085381 := bstep (se 4 (by rfl) ⟨945504, by rfl⟩ : syracuseStep 10085381 = 1891009) B1891009
theorem B2589763 : Blo 1657528 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B2360497 : Blo 1657528 2360497 := bstep (se 2 (by rfl) ⟨885186, by rfl⟩ : syracuseStep 2360497 = 1770373) B1770373
theorem B6726833 : Blo 1657528 6726833 := bstep (se 2 (by rfl) ⟨2522562, by rfl⟩ : syracuseStep 6726833 = 5045125) B5045125
theorem B2655425 : Blo 1657528 2655425 := bstep (se 2 (by rfl) ⟨995784, by rfl⟩ : syracuseStep 2655425 = 1991569) B1991569
theorem B10085573 : Blo 1657528 10085573 := bstep (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) B1891045
theorem B6300899 : Blo 1657528 6300899 := bstep (se 1 (by rfl) ⟨4725674, by rfl⟩ : syracuseStep 6300899 = 9451349) B9451349
theorem B5596397 : Blo 1657528 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B3147025 : Blo 1657528 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B2360593 : Blo 1657528 2360593 := bstep (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) B1770445
theorem B5596451 : Blo 1657528 5596451 := bstep (se 1 (by rfl) ⟨4197338, by rfl⟩ : syracuseStep 5596451 = 8394677) B8394677
theorem B6727025 : Blo 1657528 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B2835857 : Blo 1657528 2835857 := bstep (se 2 (by rfl) ⟨1063446, by rfl⟩ : syracuseStep 2835857 = 2126893) B2126893
theorem B2655713 : Blo 1657528 2655713 := bstep (se 2 (by rfl) ⟨995892, by rfl⟩ : syracuseStep 2655713 = 1991785) B1991785
theorem B10626565 : Blo 1657528 10626565 := bstep (se 4 (by rfl) ⟨996240, by rfl⟩ : syracuseStep 10626565 = 1992481) B1992481
theorem B1771043 : Blo 1657528 1771043 := bstep (se 1 (by rfl) ⟨1328282, by rfl⟩ : syracuseStep 1771043 = 2656565) B2656565
theorem B5596721 : Blo 1657528 5596721 := bstep (se 2 (by rfl) ⟨2098770, by rfl⟩ : syracuseStep 5596721 = 4197541) B4197541
theorem B4195921 : Blo 1657528 4195921 := bstep (se 2 (by rfl) ⟨1573470, by rfl⟩ : syracuseStep 4195921 = 3146941) B3146941
theorem B1992323 : Blo 1657528 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B3147427 : Blo 1657528 3147427 := bstep (se 1 (by rfl) ⟨2360570, by rfl⟩ : syracuseStep 3147427 = 4721141) B4721141
theorem B2098867 : Blo 1657528 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B2655937 : Blo 1657528 2655937 := bstep (se 2 (by rfl) ⟨995976, by rfl⟩ : syracuseStep 2655937 = 1991953) B1991953
theorem B5310157 : Blo 1657528 5310157 := bstep (se 3 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 5310157 = 1991309) B1991309
theorem B3147473 : Blo 1657528 3147473 := bstep (se 2 (by rfl) ⟨1180302, by rfl⟩ : syracuseStep 3147473 = 2360605) B2360605
theorem B3589841 : Blo 1657528 3589841 := bstep (se 2 (by rfl) ⟨1346190, by rfl⟩ : syracuseStep 3589841 = 2692381) B2692381
theorem B2361089 : Blo 1657528 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2098963 : Blo 1657528 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B2836289 : Blo 1657528 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B4196195 : Blo 1657528 4196195 := bstep (se 1 (by rfl) ⟨3147146, by rfl⟩ : syracuseStep 4196195 = 6294293) B6294293
theorem B7669603 : Blo 1657528 7669603 := bstep (se 1 (by rfl) ⟨5752202, by rfl⟩ : syracuseStep 7669603 = 11504405) B11504405
theorem B28321649 : Blo 1657528 28321649 := bstep (se 2 (by rfl) ⟨10620618, by rfl⟩ : syracuseStep 28321649 = 21241237) B21241237
theorem B10086257 : Blo 1657528 10086257 := bstep (se 2 (by rfl) ⟨3782346, by rfl⟩ : syracuseStep 10086257 = 7564693) B7564693
theorem B5310413 : Blo 1657528 5310413 := bstep (se 3 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 5310413 = 1991405) B1991405
theorem B3147761 : Blo 1657528 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B4196387 : Blo 1657528 4196387 := bstep (se 1 (by rfl) ⟨3147290, by rfl⟩ : syracuseStep 4196387 = 6294581) B6294581
theorem B5597261 : Blo 1657528 5597261 := bstep (se 3 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 5597261 = 2098973) B2098973
theorem B21006449 : Blo 1657528 21006449 := bstep (se 2 (by rfl) ⟨7877418, by rfl⟩ : syracuseStep 21006449 = 15754837) B15754837
theorem B5597315 : Blo 1657528 5597315 := bstep (se 1 (by rfl) ⟨4197986, by rfl⟩ : syracuseStep 5597315 = 8395973) B8395973
theorem B3729617 : Blo 1657528 3729617 := bstep (se 2 (by rfl) ⟨1398606, by rfl⟩ : syracuseStep 3729617 = 2797213) B2797213
theorem B3729635 : Blo 1657528 3729635 := bstep (se 1 (by rfl) ⟨2797226, by rfl⟩ : syracuseStep 3729635 = 5594453) B5594453
theorem B2099459 : Blo 1657528 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B12773645 : Blo 1657528 12773645 := bstep (se 3 (by rfl) ⟨2395058, by rfl⟩ : syracuseStep 12773645 = 4790117) B4790117
theorem B4720913 : Blo 1657528 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B1771795 : Blo 1657528 1771795 := bstep (se 1 (by rfl) ⟨1328846, by rfl⟩ : syracuseStep 1771795 = 2657693) B2657693
theorem B9447749 : Blo 1657528 9447749 := bstep (se 4 (by rfl) ⟨885726, by rfl⟩ : syracuseStep 9447749 = 1771453) B1771453
theorem B5597585 : Blo 1657528 5597585 := bstep (se 2 (by rfl) ⟨2099094, by rfl⟩ : syracuseStep 5597585 = 4198189) B4198189
theorem B3729905 : Blo 1657528 3729905 := bstep (se 2 (by rfl) ⟨1398714, by rfl⟩ : syracuseStep 3729905 = 2797429) B2797429
theorem B3729923 : Blo 1657528 3729923 := bstep (se 1 (by rfl) ⟨2797442, by rfl⟩ : syracuseStep 3729923 = 5594885) B5594885
theorem B1772051 : Blo 1657528 1772051 := bstep (se 1 (by rfl) ⟨1329038, by rfl⟩ : syracuseStep 1772051 = 2658077) B2658077
theorem B2361955 : Blo 1657528 2361955 := bstep (se 1 (by rfl) ⟨1771466, by rfl⟩ : syracuseStep 2361955 = 3542933) B3542933
theorem B34032241 : Blo 1657528 34032241 := bstep (se 2 (by rfl) ⟨12762090, by rfl⟩ : syracuseStep 34032241 = 25524181) B25524181
theorem B8399537 : Blo 1657528 8399537 := bstep (se 2 (by rfl) ⟨3149826, by rfl⟩ : syracuseStep 8399537 = 6299653) B6299653
theorem B1657539 : Blo 1657528 1657539 := bstep (se 1 (by rfl) ⟨1243154, by rfl⟩ : syracuseStep 1657539 = 2486309) B2486309
theorem B3148483 : Blo 1657528 3148483 := bstep (se 1 (by rfl) ⟨2361362, by rfl⟩ : syracuseStep 3148483 = 4722725) B4722725
theorem B2362051 : Blo 1657528 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B1657555 : Blo 1657528 1657555 := bstep (se 1 (by rfl) ⟨1243166, by rfl⟩ : syracuseStep 1657555 = 2486333) B2486333
theorem B1657571 : Blo 1657528 1657571 := bstep (se 1 (by rfl) ⟨1243178, by rfl⟩ : syracuseStep 1657571 = 2486357) B2486357
theorem B3541745 : Blo 1657528 3541745 := bstep (se 2 (by rfl) ⟨1328154, by rfl⟩ : syracuseStep 3541745 = 2656309) B2656309
theorem B1657587 : Blo 1657528 1657587 := bstep (se 1 (by rfl) ⟨1243190, by rfl⟩ : syracuseStep 1657587 = 2486381) B2486381
theorem B1657603 : Blo 1657528 1657603 := bstep (se 1 (by rfl) ⟨1243202, by rfl⟩ : syracuseStep 1657603 = 2486405) B2486405
theorem B8391437 : Blo 1657528 8391437 := bstep (se 3 (by rfl) ⟨1573394, by rfl⟩ : syracuseStep 8391437 = 3146789) B3146789
theorem B3730193 : Blo 1657528 3730193 := bstep (se 2 (by rfl) ⟨1398822, by rfl⟩ : syracuseStep 3730193 = 2797645) B2797645
theorem B1657619 : Blo 1657528 1657619 := bstep (se 1 (by rfl) ⟨1243214, by rfl⟩ : syracuseStep 1657619 = 2486429) B2486429
theorem B1657635 : Blo 1657528 1657635 := bstep (se 1 (by rfl) ⟨1243226, by rfl⟩ : syracuseStep 1657635 = 2486453) B2486453
theorem B6294307 : Blo 1657528 6294307 := bstep (se 1 (by rfl) ⟨4720730, by rfl⟩ : syracuseStep 6294307 = 9441461) B9441461
theorem B3730211 : Blo 1657528 3730211 := bstep (se 1 (by rfl) ⟨2797658, by rfl⟩ : syracuseStep 3730211 = 5595317) B5595317
theorem B1657651 : Blo 1657528 1657651 := bstep (se 1 (by rfl) ⟨1243238, by rfl⟩ : syracuseStep 1657651 = 2486477) B2486477
theorem B1657667 : Blo 1657528 1657667 := bstep (se 1 (by rfl) ⟨1243250, by rfl⟩ : syracuseStep 1657667 = 2486501) B2486501
theorem B1657683 : Blo 1657528 1657683 := bstep (se 1 (by rfl) ⟨1243262, by rfl⟩ : syracuseStep 1657683 = 2486525) B2486525
theorem B1657699 : Blo 1657528 1657699 := bstep (se 1 (by rfl) ⟨1243274, by rfl⟩ : syracuseStep 1657699 = 2486549) B2486549
theorem B1657715 : Blo 1657528 1657715 := bstep (se 1 (by rfl) ⟨1243286, by rfl⟩ : syracuseStep 1657715 = 2486573) B2486573
theorem B1657731 : Blo 1657528 1657731 := bstep (se 1 (by rfl) ⟨1243298, by rfl⟩ : syracuseStep 1657731 = 2486597) B2486597
theorem B25545613 : Blo 1657528 25545613 := bstep (se 3 (by rfl) ⟨4789802, by rfl⟩ : syracuseStep 25545613 = 9579605) B9579605
theorem B1657747 : Blo 1657528 1657747 := bstep (se 1 (by rfl) ⟨1243310, by rfl⟩ : syracuseStep 1657747 = 2486621) B2486621
theorem B1657763 : Blo 1657528 1657763 := bstep (se 1 (by rfl) ⟨1243322, by rfl⟩ : syracuseStep 1657763 = 2486645) B2486645
theorem B5598125 : Blo 1657528 5598125 := bstep (se 3 (by rfl) ⟨1049648, by rfl⟩ : syracuseStep 5598125 = 2099297) B2099297
theorem B1657779 : Blo 1657528 1657779 := bstep (se 1 (by rfl) ⟨1243334, by rfl⟩ : syracuseStep 1657779 = 2486669) B2486669
theorem B1657795 : Blo 1657528 1657795 := bstep (se 1 (by rfl) ⟨1243346, by rfl⟩ : syracuseStep 1657795 = 2486693) B2486693
theorem B2100163 : Blo 1657528 2100163 := bstep (se 1 (by rfl) ⟨1575122, by rfl⟩ : syracuseStep 2100163 = 3150245) B3150245
theorem B4197329 : Blo 1657528 4197329 := bstep (se 2 (by rfl) ⟨1573998, by rfl⟩ : syracuseStep 4197329 = 3147997) B3147997
theorem B1657811 : Blo 1657528 1657811 := bstep (se 1 (by rfl) ⟨1243358, by rfl⟩ : syracuseStep 1657811 = 2486717) B2486717
theorem B1657827 : Blo 1657528 1657827 := bstep (se 1 (by rfl) ⟨1243370, by rfl⟩ : syracuseStep 1657827 = 2486741) B2486741
theorem B36342755 : Blo 1657528 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B5598179 : Blo 1657528 5598179 := bstep (se 1 (by rfl) ⟨4198634, by rfl⟩ : syracuseStep 5598179 = 8397269) B8397269
theorem B9448433 : Blo 1657528 9448433 := bstep (se 2 (by rfl) ⟨3543162, by rfl⟩ : syracuseStep 9448433 = 7086325) B7086325
theorem B1657843 : Blo 1657528 1657843 := bstep (se 1 (by rfl) ⟨1243382, by rfl⟩ : syracuseStep 1657843 = 2486765) B2486765
theorem B1657859 : Blo 1657528 1657859 := bstep (se 1 (by rfl) ⟨1243394, by rfl⟩ : syracuseStep 1657859 = 2486789) B2486789
theorem B4197379 : Blo 1657528 4197379 := bstep (se 1 (by rfl) ⟨3148034, by rfl⟩ : syracuseStep 4197379 = 6296069) B6296069
theorem B1657875 : Blo 1657528 1657875 := bstep (se 1 (by rfl) ⟨1243406, by rfl⟩ : syracuseStep 1657875 = 2486813) B2486813
theorem B1657891 : Blo 1657528 1657891 := bstep (se 1 (by rfl) ⟨1243418, by rfl⟩ : syracuseStep 1657891 = 2486837) B2486837
theorem B7973923 : Blo 1657528 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B2100259 : Blo 1657528 2100259 := bstep (se 1 (by rfl) ⟨1575194, by rfl⟩ : syracuseStep 2100259 = 3150389) B3150389
theorem B3730481 : Blo 1657528 3730481 := bstep (se 2 (by rfl) ⟨1398930, by rfl⟩ : syracuseStep 3730481 = 2797861) B2797861
theorem B1657907 : Blo 1657528 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1657923 : Blo 1657528 1657923 := bstep (se 1 (by rfl) ⟨1243442, by rfl⟩ : syracuseStep 1657923 = 2486885) B2486885
theorem B3730499 : Blo 1657528 3730499 := bstep (se 1 (by rfl) ⟨2797874, by rfl⟩ : syracuseStep 3730499 = 5595749) B5595749
theorem B7965773 : Blo 1657528 7965773 := bstep (se 3 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 7965773 = 2987165) B2987165
theorem B1657939 : Blo 1657528 1657939 := bstep (se 1 (by rfl) ⟨1243454, by rfl⟩ : syracuseStep 1657939 = 2486909) B2486909
theorem B1657955 : Blo 1657528 1657955 := bstep (se 1 (by rfl) ⟨1243466, by rfl⟩ : syracuseStep 1657955 = 2486933) B2486933
theorem B1657971 : Blo 1657528 1657971 := bstep (se 1 (by rfl) ⟨1243478, by rfl⟩ : syracuseStep 1657971 = 2486957) B2486957
theorem B1657987 : Blo 1657528 1657987 := bstep (se 1 (by rfl) ⟨1243490, by rfl⟩ : syracuseStep 1657987 = 2486981) B2486981
theorem B3148931 : Blo 1657528 3148931 := bstep (se 1 (by rfl) ⟨2361698, by rfl⟩ : syracuseStep 3148931 = 4723397) B4723397
theorem B4197521 : Blo 1657528 4197521 := bstep (se 2 (by rfl) ⟨1574070, by rfl⟩ : syracuseStep 4197521 = 3148141) B3148141
theorem B1658003 : Blo 1657528 1658003 := bstep (se 1 (by rfl) ⟨1243502, by rfl⟩ : syracuseStep 1658003 = 2487005) B2487005
theorem B1658019 : Blo 1657528 1658019 := bstep (se 1 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 1658019 = 2487029) B2487029
theorem B1658035 : Blo 1657528 1658035 := bstep (se 1 (by rfl) ⟨1243526, by rfl⟩ : syracuseStep 1658035 = 2487053) B2487053
theorem B2362547 : Blo 1657528 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B1658051 : Blo 1657528 1658051 := bstep (se 1 (by rfl) ⟨1243538, by rfl⟩ : syracuseStep 1658051 = 2487077) B2487077
theorem B2837713 : Blo 1657528 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B1658067 : Blo 1657528 1658067 := bstep (se 1 (by rfl) ⟨1243550, by rfl⟩ : syracuseStep 1658067 = 2487101) B2487101
theorem B1658083 : Blo 1657528 1658083 := bstep (se 1 (by rfl) ⟨1243562, by rfl⟩ : syracuseStep 1658083 = 2487125) B2487125
theorem B11349233 : Blo 1657528 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B5598449 : Blo 1657528 5598449 := bstep (se 2 (by rfl) ⟨2099418, by rfl⟩ : syracuseStep 5598449 = 4198837) B4198837
theorem B1658099 : Blo 1657528 1658099 := bstep (se 1 (by rfl) ⟨1243574, by rfl⟩ : syracuseStep 1658099 = 2487149) B2487149
theorem B1658115 : Blo 1657528 1658115 := bstep (se 1 (by rfl) ⟨1243586, by rfl⟩ : syracuseStep 1658115 = 2487173) B2487173
theorem B2657539 : Blo 1657528 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B7965965 : Blo 1657528 7965965 := bstep (se 3 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 7965965 = 2987237) B2987237
theorem B1658131 : Blo 1657528 1658131 := bstep (se 1 (by rfl) ⟨1243598, by rfl⟩ : syracuseStep 1658131 = 2487197) B2487197
theorem B1658147 : Blo 1657528 1658147 := bstep (se 1 (by rfl) ⟨1243610, by rfl⟩ : syracuseStep 1658147 = 2487221) B2487221
theorem B10620209 : Blo 1657528 10620209 := bstep (se 2 (by rfl) ⟨3982578, by rfl⟩ : syracuseStep 10620209 = 7965157) B7965157
theorem B1658163 : Blo 1657528 1658163 := bstep (se 1 (by rfl) ⟨1243622, by rfl⟩ : syracuseStep 1658163 = 2487245) B2487245
theorem B1658179 : Blo 1657528 1658179 := bstep (se 1 (by rfl) ⟨1243634, by rfl⟩ : syracuseStep 1658179 = 2487269) B2487269
theorem B3730769 : Blo 1657528 3730769 := bstep (se 2 (by rfl) ⟨1399038, by rfl⟩ : syracuseStep 3730769 = 2798077) B2798077
theorem B1658195 : Blo 1657528 1658195 := bstep (se 1 (by rfl) ⟨1243646, by rfl⟩ : syracuseStep 1658195 = 2487293) B2487293
theorem B3730787 : Blo 1657528 3730787 := bstep (se 1 (by rfl) ⟨2798090, by rfl⟩ : syracuseStep 3730787 = 5596181) B5596181
theorem B1658211 : Blo 1657528 1658211 := bstep (se 1 (by rfl) ⟨1243658, by rfl⟩ : syracuseStep 1658211 = 2487317) B2487317
theorem B8965475 : Blo 1657528 8965475 := bstep (se 1 (by rfl) ⟨6724106, by rfl⟩ : syracuseStep 8965475 = 13448213) B13448213
theorem B14175587 : Blo 1657528 14175587 := bstep (se 1 (by rfl) ⟨10631690, by rfl⟩ : syracuseStep 14175587 = 21263381) B21263381
theorem B1658227 : Blo 1657528 1658227 := bstep (se 1 (by rfl) ⟨1243670, by rfl⟩ : syracuseStep 1658227 = 2487341) B2487341
theorem B1658243 : Blo 1657528 1658243 := bstep (se 1 (by rfl) ⟨1243682, by rfl⟩ : syracuseStep 1658243 = 2487365) B2487365
theorem B18894221 : Blo 1657528 18894221 := bstep (se 3 (by rfl) ⟨3542666, by rfl⟩ : syracuseStep 18894221 = 7085333) B7085333
theorem B1658259 : Blo 1657528 1658259 := bstep (se 1 (by rfl) ⟨1243694, by rfl⟩ : syracuseStep 1658259 = 2487389) B2487389
theorem B1658275 : Blo 1657528 1658275 := bstep (se 1 (by rfl) ⟨1243706, by rfl⟩ : syracuseStep 1658275 = 2487413) B2487413
theorem B3149219 : Blo 1657528 3149219 := bstep (se 1 (by rfl) ⟨2361914, by rfl⟩ : syracuseStep 3149219 = 4723829) B4723829
theorem B1658291 : Blo 1657528 1658291 := bstep (se 1 (by rfl) ⟨1243718, by rfl⟩ : syracuseStep 1658291 = 2487437) B2487437
theorem B5311939 : Blo 1657528 5311939 := bstep (se 1 (by rfl) ⟨3983954, by rfl⟩ : syracuseStep 5311939 = 7967909) B7967909
theorem B1658307 : Blo 1657528 1658307 := bstep (se 1 (by rfl) ⟨1243730, by rfl⟩ : syracuseStep 1658307 = 2487461) B2487461
theorem B1658323 : Blo 1657528 1658323 := bstep (se 1 (by rfl) ⟨1243742, by rfl⟩ : syracuseStep 1658323 = 2487485) B2487485
theorem B1658339 : Blo 1657528 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B1658355 : Blo 1657528 1658355 := bstep (se 1 (by rfl) ⟨1243766, by rfl⟩ : syracuseStep 1658355 = 2487533) B2487533
theorem B1658371 : Blo 1657528 1658371 := bstep (se 1 (by rfl) ⟨1243778, by rfl⟩ : syracuseStep 1658371 = 2487557) B2487557
theorem B1658387 : Blo 1657528 1658387 := bstep (se 1 (by rfl) ⟨1243790, by rfl⟩ : syracuseStep 1658387 = 2487581) B2487581
theorem B1658403 : Blo 1657528 1658403 := bstep (se 1 (by rfl) ⟨1243802, by rfl⟩ : syracuseStep 1658403 = 2487605) B2487605
theorem B2797105 : Blo 1657528 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B1658419 : Blo 1657528 1658419 := bstep (se 1 (by rfl) ⟨1243814, by rfl⟩ : syracuseStep 1658419 = 2487629) B2487629
theorem B1658435 : Blo 1657528 1658435 := bstep (se 1 (by rfl) ⟨1243826, by rfl⟩ : syracuseStep 1658435 = 2487653) B2487653
theorem B2797139 : Blo 1657528 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B1658451 : Blo 1657528 1658451 := bstep (se 1 (by rfl) ⟨1243838, by rfl⟩ : syracuseStep 1658451 = 2487677) B2487677
theorem B1658467 : Blo 1657528 1658467 := bstep (se 1 (by rfl) ⟨1243850, by rfl⟩ : syracuseStep 1658467 = 2487701) B2487701
theorem B3731057 : Blo 1657528 3731057 := bstep (se 2 (by rfl) ⟨1399146, by rfl⟩ : syracuseStep 3731057 = 2798293) B2798293
theorem B1658483 : Blo 1657528 1658483 := bstep (se 1 (by rfl) ⟨1243862, by rfl⟩ : syracuseStep 1658483 = 2487725) B2487725
theorem B3731075 : Blo 1657528 3731075 := bstep (se 1 (by rfl) ⟨2798306, by rfl⟩ : syracuseStep 3731075 = 5596613) B5596613
theorem B1658499 : Blo 1657528 1658499 := bstep (se 1 (by rfl) ⟨1243874, by rfl⟩ : syracuseStep 1658499 = 2487749) B2487749
theorem B1658515 : Blo 1657528 1658515 := bstep (se 1 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 1658515 = 2487773) B2487773
theorem B1658531 : Blo 1657528 1658531 := bstep (se 1 (by rfl) ⟨1243898, by rfl⟩ : syracuseStep 1658531 = 2487797) B2487797
theorem B1658547 : Blo 1657528 1658547 := bstep (se 1 (by rfl) ⟨1243910, by rfl⟩ : syracuseStep 1658547 = 2487821) B2487821
theorem B4722371 : Blo 1657528 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B1658563 : Blo 1657528 1658563 := bstep (se 1 (by rfl) ⟨1243922, by rfl⟩ : syracuseStep 1658563 = 2487845) B2487845
theorem B4484803 : Blo 1657528 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B2797267 : Blo 1657528 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B1658579 : Blo 1657528 1658579 := bstep (se 1 (by rfl) ⟨1243934, by rfl⟩ : syracuseStep 1658579 = 2487869) B2487869
theorem B1658595 : Blo 1657528 1658595 := bstep (se 1 (by rfl) ⟨1243946, by rfl⟩ : syracuseStep 1658595 = 2487893) B2487893
theorem B5041901 : Blo 1657528 5041901 := bstep (se 3 (by rfl) ⟨945356, by rfl⟩ : syracuseStep 5041901 = 1890713) B1890713
theorem B1658611 : Blo 1657528 1658611 := bstep (se 1 (by rfl) ⟨1243958, by rfl⟩ : syracuseStep 1658611 = 2487917) B2487917
theorem B1658627 : Blo 1657528 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B5598989 : Blo 1657528 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B1658643 : Blo 1657528 1658643 := bstep (se 1 (by rfl) ⟨1243982, by rfl⟩ : syracuseStep 1658643 = 2487965) B2487965
theorem B1658659 : Blo 1657528 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B4484899 : Blo 1657528 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B1658675 : Blo 1657528 1658675 := bstep (se 1 (by rfl) ⟨1244006, by rfl⟩ : syracuseStep 1658675 = 2488013) B2488013
theorem B1658691 : Blo 1657528 1658691 := bstep (se 1 (by rfl) ⟨1244018, by rfl⟩ : syracuseStep 1658691 = 2488037) B2488037
theorem B5599043 : Blo 1657528 5599043 := bstep (se 1 (by rfl) ⟨4199282, by rfl⟩ : syracuseStep 5599043 = 8398565) B8398565
theorem B1658707 : Blo 1657528 1658707 := bstep (se 1 (by rfl) ⟨1244030, by rfl⟩ : syracuseStep 1658707 = 2488061) B2488061
theorem B2797409 : Blo 1657528 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B1658723 : Blo 1657528 1658723 := bstep (se 1 (by rfl) ⟨1244042, by rfl⟩ : syracuseStep 1658723 = 2488085) B2488085
theorem B1658739 : Blo 1657528 1658739 := bstep (se 1 (by rfl) ⟨1244054, by rfl⟩ : syracuseStep 1658739 = 2488109) B2488109
theorem B1658755 : Blo 1657528 1658755 := bstep (se 1 (by rfl) ⟨1244066, by rfl⟩ : syracuseStep 1658755 = 2488133) B2488133
theorem B3731345 : Blo 1657528 3731345 := bstep (se 2 (by rfl) ⟨1399254, by rfl⟩ : syracuseStep 3731345 = 2798509) B2798509
theorem B1658771 : Blo 1657528 1658771 := bstep (se 1 (by rfl) ⟨1244078, by rfl⟩ : syracuseStep 1658771 = 2488157) B2488157
theorem B3731363 : Blo 1657528 3731363 := bstep (se 1 (by rfl) ⟨2798522, by rfl⟩ : syracuseStep 3731363 = 5597045) B5597045
theorem B1658787 : Blo 1657528 1658787 := bstep (se 1 (by rfl) ⟨1244090, by rfl⟩ : syracuseStep 1658787 = 2488181) B2488181
theorem B1658803 : Blo 1657528 1658803 := bstep (se 1 (by rfl) ⟨1244102, by rfl⟩ : syracuseStep 1658803 = 2488205) B2488205
theorem B1658819 : Blo 1657528 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B1658835 : Blo 1657528 1658835 := bstep (se 1 (by rfl) ⟨1244126, by rfl⟩ : syracuseStep 1658835 = 2488253) B2488253
theorem B2797537 : Blo 1657528 2797537 := bstep (se 2 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 2797537 = 2098153) B2098153
theorem B1658851 : Blo 1657528 1658851 := bstep (se 1 (by rfl) ⟨1244138, by rfl⟩ : syracuseStep 1658851 = 2488277) B2488277
theorem B1658867 : Blo 1657528 1658867 := bstep (se 1 (by rfl) ⟨1244150, by rfl⟩ : syracuseStep 1658867 = 2488301) B2488301
theorem B2797571 : Blo 1657528 2797571 := bstep (se 1 (by rfl) ⟨2098178, by rfl⟩ : syracuseStep 2797571 = 4196357) B4196357
theorem B1658883 : Blo 1657528 1658883 := bstep (se 1 (by rfl) ⟨1244162, by rfl⟩ : syracuseStep 1658883 = 2488325) B2488325
theorem B3543043 : Blo 1657528 3543043 := bstep (se 1 (by rfl) ⟨2657282, by rfl⟩ : syracuseStep 3543043 = 5314565) B5314565
theorem B1658899 : Blo 1657528 1658899 := bstep (se 1 (by rfl) ⟨1244174, by rfl⟩ : syracuseStep 1658899 = 2488349) B2488349
theorem B1658915 : Blo 1657528 1658915 := bstep (se 1 (by rfl) ⟨1244186, by rfl⟩ : syracuseStep 1658915 = 2488373) B2488373
theorem B2486321 : Blo 1657528 2486321 := bstep (se 2 (by rfl) ⟨932370, by rfl⟩ : syracuseStep 2486321 = 1864741) B1864741
theorem B1658931 : Blo 1657528 1658931 := bstep (se 1 (by rfl) ⟨1244198, by rfl⟩ : syracuseStep 1658931 = 2488397) B2488397
theorem B2486339 : Blo 1657528 2486339 := bstep (se 1 (by rfl) ⟨1864754, by rfl⟩ : syracuseStep 2486339 = 3729509) B3729509
theorem B1658947 : Blo 1657528 1658947 := bstep (se 1 (by rfl) ⟨1244210, by rfl⟩ : syracuseStep 1658947 = 2488421) B2488421
theorem B8966213 : Blo 1657528 8966213 := bstep (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) B1681165
theorem B3362897 : Blo 1657528 3362897 := bstep (se 2 (by rfl) ⟨1261086, by rfl⟩ : syracuseStep 3362897 = 2522173) B2522173
theorem B5599313 : Blo 1657528 5599313 := bstep (se 2 (by rfl) ⟨2099742, by rfl⟩ : syracuseStep 5599313 = 4199485) B4199485
theorem B1658963 : Blo 1657528 1658963 := bstep (se 1 (by rfl) ⟨1244222, by rfl⟩ : syracuseStep 1658963 = 2488445) B2488445
theorem B2486369 : Blo 1657528 2486369 := bstep (se 2 (by rfl) ⟨932388, by rfl⟩ : syracuseStep 2486369 = 1864777) B1864777
theorem B1658979 : Blo 1657528 1658979 := bstep (se 1 (by rfl) ⟨1244234, by rfl⟩ : syracuseStep 1658979 = 2488469) B2488469
theorem B8400995 : Blo 1657528 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B15544433 : Blo 1657528 15544433 := bstep (se 2 (by rfl) ⟨5829162, by rfl⟩ : syracuseStep 15544433 = 11658325) B11658325
theorem B2486387 : Blo 1657528 2486387 := bstep (se 1 (by rfl) ⟨1864790, by rfl⟩ : syracuseStep 2486387 = 3729581) B3729581
theorem B4198513 : Blo 1657528 4198513 := bstep (se 2 (by rfl) ⟨1574442, by rfl⟩ : syracuseStep 4198513 = 3148885) B3148885
theorem B1658995 : Blo 1657528 1658995 := bstep (se 1 (by rfl) ⟨1244246, by rfl⟩ : syracuseStep 1658995 = 2488493) B2488493
theorem B2797699 : Blo 1657528 2797699 := bstep (se 1 (by rfl) ⟨2098274, by rfl⟩ : syracuseStep 2797699 = 4196549) B4196549
theorem B1659011 : Blo 1657528 1659011 := bstep (se 1 (by rfl) ⟨1244258, by rfl⟩ : syracuseStep 1659011 = 2488517) B2488517
theorem B2486417 : Blo 1657528 2486417 := bstep (se 2 (by rfl) ⟨932406, by rfl⟩ : syracuseStep 2486417 = 1864813) B1864813
theorem B1659027 : Blo 1657528 1659027 := bstep (se 1 (by rfl) ⟨1244270, by rfl⟩ : syracuseStep 1659027 = 2488541) B2488541
theorem B2486435 : Blo 1657528 2486435 := bstep (se 1 (by rfl) ⟨1864826, by rfl⟩ : syracuseStep 2486435 = 3729653) B3729653
theorem B1659043 : Blo 1657528 1659043 := bstep (se 1 (by rfl) ⟨1244282, by rfl⟩ : syracuseStep 1659043 = 2488565) B2488565
theorem B3731633 : Blo 1657528 3731633 := bstep (se 2 (by rfl) ⟨1399362, by rfl⟩ : syracuseStep 3731633 = 2798725) B2798725
theorem B1659059 : Blo 1657528 1659059 := bstep (se 1 (by rfl) ⟨1244294, by rfl⟩ : syracuseStep 1659059 = 2488589) B2488589
theorem B2486465 : Blo 1657528 2486465 := bstep (se 2 (by rfl) ⟨932424, by rfl⟩ : syracuseStep 2486465 = 1864849) B1864849
theorem B3731651 : Blo 1657528 3731651 := bstep (se 1 (by rfl) ⟨2798738, by rfl⟩ : syracuseStep 3731651 = 5597477) B5597477
theorem B1659075 : Blo 1657528 1659075 := bstep (se 1 (by rfl) ⟨1244306, by rfl⟩ : syracuseStep 1659075 = 2488613) B2488613
theorem B3592387 : Blo 1657528 3592387 := bstep (se 1 (by rfl) ⟨2694290, by rfl⟩ : syracuseStep 3592387 = 5388581) B5388581
theorem B2486483 : Blo 1657528 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B1659091 : Blo 1657528 1659091 := bstep (se 1 (by rfl) ⟨1244318, by rfl⟩ : syracuseStep 1659091 = 2488637) B2488637
theorem B1659107 : Blo 1657528 1659107 := bstep (se 1 (by rfl) ⟨1244330, by rfl⟩ : syracuseStep 1659107 = 2488661) B2488661
theorem B2486513 : Blo 1657528 2486513 := bstep (se 2 (by rfl) ⟨932442, by rfl⟩ : syracuseStep 2486513 = 1864885) B1864885
theorem B7082225 : Blo 1657528 7082225 := bstep (se 2 (by rfl) ⟨2655834, by rfl⟩ : syracuseStep 7082225 = 5311669) B5311669
theorem B1659123 : Blo 1657528 1659123 := bstep (se 1 (by rfl) ⟨1244342, by rfl⟩ : syracuseStep 1659123 = 2488685) B2488685
theorem B2486531 : Blo 1657528 2486531 := bstep (se 1 (by rfl) ⟨1864898, by rfl⟩ : syracuseStep 2486531 = 3729797) B3729797
theorem B1659139 : Blo 1657528 1659139 := bstep (se 1 (by rfl) ⟨1244354, by rfl⟩ : syracuseStep 1659139 = 2488709) B2488709
theorem B2240785 : Blo 1657528 2240785 := bstep (se 2 (by rfl) ⟨840294, by rfl⟩ : syracuseStep 2240785 = 1680589) B1680589
theorem B2797841 : Blo 1657528 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B1659155 : Blo 1657528 1659155 := bstep (se 1 (by rfl) ⟨1244366, by rfl⟩ : syracuseStep 1659155 = 2488733) B2488733
theorem B2486561 : Blo 1657528 2486561 := bstep (se 2 (by rfl) ⟨932460, by rfl⟩ : syracuseStep 2486561 = 1864921) B1864921
theorem B1659171 : Blo 1657528 1659171 := bstep (se 1 (by rfl) ⟨1244378, by rfl⟩ : syracuseStep 1659171 = 2488757) B2488757
theorem B2486579 : Blo 1657528 2486579 := bstep (se 1 (by rfl) ⟨1864934, by rfl⟩ : syracuseStep 2486579 = 3729869) B3729869
theorem B1659187 : Blo 1657528 1659187 := bstep (se 1 (by rfl) ⟨1244390, by rfl⟩ : syracuseStep 1659187 = 2488781) B2488781
theorem B1659203 : Blo 1657528 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B2486609 : Blo 1657528 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B3150161 : Blo 1657528 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B1659219 : Blo 1657528 1659219 := bstep (se 1 (by rfl) ⟨1244414, by rfl⟩ : syracuseStep 1659219 = 2488829) B2488829
theorem B2486627 : Blo 1657528 2486627 := bstep (se 1 (by rfl) ⟨1864970, by rfl⟩ : syracuseStep 2486627 = 3729941) B3729941
theorem B1659235 : Blo 1657528 1659235 := bstep (se 1 (by rfl) ⟨1244426, by rfl⟩ : syracuseStep 1659235 = 2488853) B2488853
theorem B11948401 : Blo 1657528 11948401 := bstep (se 2 (by rfl) ⟨4480650, by rfl⟩ : syracuseStep 11948401 = 8961301) B8961301
theorem B1659251 : Blo 1657528 1659251 := bstep (se 1 (by rfl) ⟨1244438, by rfl⟩ : syracuseStep 1659251 = 2488877) B2488877
theorem B2486657 : Blo 1657528 2486657 := bstep (se 2 (by rfl) ⟨932496, by rfl⟩ : syracuseStep 2486657 = 1864993) B1864993
theorem B4198787 : Blo 1657528 4198787 := bstep (se 1 (by rfl) ⟨3149090, by rfl⟩ : syracuseStep 4198787 = 6298181) B6298181
theorem B1659267 : Blo 1657528 1659267 := bstep (se 1 (by rfl) ⟨1244450, by rfl⟩ : syracuseStep 1659267 = 2488901) B2488901
theorem B2797969 : Blo 1657528 2797969 := bstep (se 2 (by rfl) ⟨1049238, by rfl⟩ : syracuseStep 2797969 = 2098477) B2098477
theorem B2486675 : Blo 1657528 2486675 := bstep (se 1 (by rfl) ⟨1865006, by rfl⟩ : syracuseStep 2486675 = 3730013) B3730013
theorem B1659283 : Blo 1657528 1659283 := bstep (se 1 (by rfl) ⟨1244462, by rfl⟩ : syracuseStep 1659283 = 2488925) B2488925
theorem B10629539 : Blo 1657528 10629539 := bstep (se 1 (by rfl) ⟨7972154, by rfl⟩ : syracuseStep 10629539 = 15944309) B15944309
theorem B9449891 : Blo 1657528 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B1659299 : Blo 1657528 1659299 := bstep (se 1 (by rfl) ⟨1244474, by rfl⟩ : syracuseStep 1659299 = 2488949) B2488949
theorem B2486705 : Blo 1657528 2486705 := bstep (se 2 (by rfl) ⟨932514, by rfl⟩ : syracuseStep 2486705 = 1865029) B1865029
theorem B2798003 : Blo 1657528 2798003 := bstep (se 1 (by rfl) ⟨2098502, by rfl⟩ : syracuseStep 2798003 = 4197005) B4197005
theorem B1659315 : Blo 1657528 1659315 := bstep (se 1 (by rfl) ⟨1244486, by rfl⟩ : syracuseStep 1659315 = 2488973) B2488973
theorem B2486723 : Blo 1657528 2486723 := bstep (se 1 (by rfl) ⟨1865042, by rfl⟩ : syracuseStep 2486723 = 3730085) B3730085
theorem B1659331 : Blo 1657528 1659331 := bstep (se 1 (by rfl) ⟨1244498, by rfl⟩ : syracuseStep 1659331 = 2488997) B2488997
theorem B3731921 : Blo 1657528 3731921 := bstep (se 2 (by rfl) ⟨1399470, by rfl⟩ : syracuseStep 3731921 = 2798941) B2798941
theorem B1659347 : Blo 1657528 1659347 := bstep (se 1 (by rfl) ⟨1244510, by rfl⟩ : syracuseStep 1659347 = 2489021) B2489021
theorem B2486753 : Blo 1657528 2486753 := bstep (se 2 (by rfl) ⟨932532, by rfl⟩ : syracuseStep 2486753 = 1865065) B1865065
theorem B3731939 : Blo 1657528 3731939 := bstep (se 1 (by rfl) ⟨2798954, by rfl⟩ : syracuseStep 3731939 = 5597909) B5597909
theorem B1659363 : Blo 1657528 1659363 := bstep (se 1 (by rfl) ⟨1244522, by rfl⟩ : syracuseStep 1659363 = 2489045) B2489045
theorem B4723181 : Blo 1657528 4723181 := bstep (se 3 (by rfl) ⟨885596, by rfl⟩ : syracuseStep 4723181 = 1771193) B1771193
theorem B2486771 : Blo 1657528 2486771 := bstep (se 1 (by rfl) ⟨1865078, by rfl⟩ : syracuseStep 2486771 = 3730157) B3730157
theorem B1659379 : Blo 1657528 1659379 := bstep (se 1 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 1659379 = 2489069) B2489069
theorem B1659395 : Blo 1657528 1659395 := bstep (se 1 (by rfl) ⟨1244546, by rfl⟩ : syracuseStep 1659395 = 2489093) B2489093
theorem B2486801 : Blo 1657528 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1659411 : Blo 1657528 1659411 := bstep (se 1 (by rfl) ⟨1244558, by rfl⟩ : syracuseStep 1659411 = 2489117) B2489117
theorem B2486819 : Blo 1657528 2486819 := bstep (se 1 (by rfl) ⟨1865114, by rfl⟩ : syracuseStep 2486819 = 3730229) B3730229
theorem B1659427 : Blo 1657528 1659427 := bstep (se 1 (by rfl) ⟨1244570, by rfl⟩ : syracuseStep 1659427 = 2489141) B2489141
theorem B2798131 : Blo 1657528 2798131 := bstep (se 1 (by rfl) ⟨2098598, by rfl⟩ : syracuseStep 2798131 = 4197197) B4197197
theorem B1659443 : Blo 1657528 1659443 := bstep (se 1 (by rfl) ⟨1244582, by rfl⟩ : syracuseStep 1659443 = 2489165) B2489165
theorem B2486849 : Blo 1657528 2486849 := bstep (se 2 (by rfl) ⟨932568, by rfl⟩ : syracuseStep 2486849 = 1865137) B1865137
theorem B4198979 : Blo 1657528 4198979 := bstep (se 1 (by rfl) ⟨3149234, by rfl⟩ : syracuseStep 4198979 = 6298469) B6298469
theorem B1659459 : Blo 1657528 1659459 := bstep (se 1 (by rfl) ⟨1244594, by rfl⟩ : syracuseStep 1659459 = 2489189) B2489189
theorem B2486867 : Blo 1657528 2486867 := bstep (se 1 (by rfl) ⟨1865150, by rfl⟩ : syracuseStep 2486867 = 3730301) B3730301
theorem B1659475 : Blo 1657528 1659475 := bstep (se 1 (by rfl) ⟨1244606, by rfl⟩ : syracuseStep 1659475 = 2489213) B2489213
theorem B1659491 : Blo 1657528 1659491 := bstep (se 1 (by rfl) ⟨1244618, by rfl⟩ : syracuseStep 1659491 = 2489237) B2489237
theorem B5599853 : Blo 1657528 5599853 := bstep (se 3 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 5599853 = 2099945) B2099945
theorem B2486897 : Blo 1657528 2486897 := bstep (se 2 (by rfl) ⟨932586, by rfl⟩ : syracuseStep 2486897 = 1865173) B1865173
theorem B1659507 : Blo 1657528 1659507 := bstep (se 1 (by rfl) ⟨1244630, by rfl⟩ : syracuseStep 1659507 = 2489261) B2489261
theorem B2486915 : Blo 1657528 2486915 := bstep (se 1 (by rfl) ⟨1865186, by rfl⟩ : syracuseStep 2486915 = 3730373) B3730373
theorem B1659523 : Blo 1657528 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B2486945 : Blo 1657528 2486945 := bstep (se 2 (by rfl) ⟨932604, by rfl⟩ : syracuseStep 2486945 = 1865209) B1865209
theorem B5599907 : Blo 1657528 5599907 := bstep (se 1 (by rfl) ⟨4199930, by rfl⟩ : syracuseStep 5599907 = 8399861) B8399861
theorem B4723373 : Blo 1657528 4723373 := bstep (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) B1771265
theorem B2486963 : Blo 1657528 2486963 := bstep (se 1 (by rfl) ⟨1865222, by rfl⟩ : syracuseStep 2486963 = 3730445) B3730445
theorem B2798273 : Blo 1657528 2798273 := bstep (se 2 (by rfl) ⟨1049352, by rfl⟩ : syracuseStep 2798273 = 2098705) B2098705
theorem B8966861 : Blo 1657528 8966861 := bstep (se 3 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 8966861 = 3362573) B3362573
theorem B2486993 : Blo 1657528 2486993 := bstep (se 2 (by rfl) ⟨932622, by rfl⟩ : syracuseStep 2486993 = 1865245) B1865245
theorem B2487011 : Blo 1657528 2487011 := bstep (se 1 (by rfl) ⟨1865258, by rfl⟩ : syracuseStep 2487011 = 3730517) B3730517
theorem B57447139 : Blo 1657528 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B3732209 : Blo 1657528 3732209 := bstep (se 2 (by rfl) ⟨1399578, by rfl⟩ : syracuseStep 3732209 = 2799157) B2799157
theorem B2487041 : Blo 1657528 2487041 := bstep (se 2 (by rfl) ⟨932640, by rfl⟩ : syracuseStep 2487041 = 1865281) B1865281
theorem B3732227 : Blo 1657528 3732227 := bstep (se 1 (by rfl) ⟨2799170, by rfl⟩ : syracuseStep 3732227 = 5598341) B5598341
theorem B10769165 : Blo 1657528 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B2487059 : Blo 1657528 2487059 := bstep (se 1 (by rfl) ⟨1865294, by rfl⟩ : syracuseStep 2487059 = 3730589) B3730589
theorem B7566115 : Blo 1657528 7566115 := bstep (se 1 (by rfl) ⟨5674586, by rfl⟩ : syracuseStep 7566115 = 11349173) B11349173
theorem B2487089 : Blo 1657528 2487089 := bstep (se 2 (by rfl) ⟨932658, by rfl⟩ : syracuseStep 2487089 = 1865317) B1865317
theorem B2798401 : Blo 1657528 2798401 := bstep (se 2 (by rfl) ⟨1049400, by rfl⟩ : syracuseStep 2798401 = 2098801) B2098801
theorem B2487107 : Blo 1657528 2487107 := bstep (se 1 (by rfl) ⟨1865330, by rfl⟩ : syracuseStep 2487107 = 3730661) B3730661
theorem B3191633 : Blo 1657528 3191633 := bstep (se 2 (by rfl) ⟨1196862, by rfl⟩ : syracuseStep 3191633 = 2393725) B2393725
theorem B2487137 : Blo 1657528 2487137 := bstep (se 2 (by rfl) ⟨932676, by rfl⟩ : syracuseStep 2487137 = 1865353) B1865353
theorem B2798435 : Blo 1657528 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B2487155 : Blo 1657528 2487155 := bstep (se 1 (by rfl) ⟨1865366, by rfl⟩ : syracuseStep 2487155 = 3730733) B3730733
theorem B2487185 : Blo 1657528 2487185 := bstep (se 2 (by rfl) ⟨932694, by rfl⟩ : syracuseStep 2487185 = 1865389) B1865389
theorem B2487203 : Blo 1657528 2487203 := bstep (se 1 (by rfl) ⟨1865402, by rfl⟩ : syracuseStep 2487203 = 3730805) B3730805
theorem B5600177 : Blo 1657528 5600177 := bstep (se 2 (by rfl) ⟨2100066, by rfl⟩ : syracuseStep 5600177 = 4200133) B4200133
theorem B2487233 : Blo 1657528 2487233 := bstep (se 2 (by rfl) ⟨932712, by rfl⟩ : syracuseStep 2487233 = 1865425) B1865425
theorem B6296525 : Blo 1657528 6296525 := bstep (se 3 (by rfl) ⟨1180598, by rfl⟩ : syracuseStep 6296525 = 2361197) B2361197
theorem B2487251 : Blo 1657528 2487251 := bstep (se 1 (by rfl) ⟨1865438, by rfl⟩ : syracuseStep 2487251 = 3730877) B3730877
theorem B2798563 : Blo 1657528 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B2487281 : Blo 1657528 2487281 := bstep (se 2 (by rfl) ⟨932730, by rfl⟩ : syracuseStep 2487281 = 1865461) B1865461
theorem B2487299 : Blo 1657528 2487299 := bstep (se 1 (by rfl) ⟨1865474, by rfl⟩ : syracuseStep 2487299 = 3730949) B3730949
theorem B5313539 : Blo 1657528 5313539 := bstep (se 1 (by rfl) ⟨3985154, by rfl⟩ : syracuseStep 5313539 = 7970309) B7970309
theorem B3732497 : Blo 1657528 3732497 := bstep (se 2 (by rfl) ⟨1399686, by rfl⟩ : syracuseStep 3732497 = 2799373) B2799373
theorem B1864723 : Blo 1657528 1864723 := bstep (se 1 (by rfl) ⟨1398542, by rfl⟩ : syracuseStep 1864723 = 2797085) B2797085
theorem B2487329 : Blo 1657528 2487329 := bstep (se 2 (by rfl) ⟨932748, by rfl⟩ : syracuseStep 2487329 = 1865497) B1865497
theorem B3732515 : Blo 1657528 3732515 := bstep (se 1 (by rfl) ⟨2799386, by rfl⟩ : syracuseStep 3732515 = 5598773) B5598773
theorem B10089521 : Blo 1657528 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B2487347 : Blo 1657528 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B2487377 : Blo 1657528 2487377 := bstep (se 2 (by rfl) ⟨932766, by rfl⟩ : syracuseStep 2487377 = 1865533) B1865533
theorem B2487395 : Blo 1657528 2487395 := bstep (se 1 (by rfl) ⟨1865546, by rfl⟩ : syracuseStep 2487395 = 3731093) B3731093
theorem B2798705 : Blo 1657528 2798705 := bstep (se 2 (by rfl) ⟨1049514, by rfl⟩ : syracuseStep 2798705 = 2099029) B2099029
theorem B2487425 : Blo 1657528 2487425 := bstep (se 2 (by rfl) ⟨932784, by rfl⟩ : syracuseStep 2487425 = 1865569) B1865569
theorem B2487443 : Blo 1657528 2487443 := bstep (se 1 (by rfl) ⟨1865582, by rfl⟩ : syracuseStep 2487443 = 3731165) B3731165
theorem B1864867 : Blo 1657528 1864867 := bstep (se 1 (by rfl) ⟨1398650, by rfl⟩ : syracuseStep 1864867 = 2797301) B2797301
theorem B2487473 : Blo 1657528 2487473 := bstep (se 2 (by rfl) ⟨932802, by rfl⟩ : syracuseStep 2487473 = 1865605) B1865605
theorem B2487491 : Blo 1657528 2487491 := bstep (se 1 (by rfl) ⟨1865618, by rfl⟩ : syracuseStep 2487491 = 3731237) B3731237
theorem B3544273 : Blo 1657528 3544273 := bstep (se 2 (by rfl) ⟨1329102, by rfl⟩ : syracuseStep 3544273 = 2658205) B2658205
theorem B2487521 : Blo 1657528 2487521 := bstep (se 2 (by rfl) ⟨932820, by rfl⟩ : syracuseStep 2487521 = 1865641) B1865641
theorem B2798833 : Blo 1657528 2798833 := bstep (se 2 (by rfl) ⟨1049562, by rfl⟩ : syracuseStep 2798833 = 2099125) B2099125
theorem B2487539 : Blo 1657528 2487539 := bstep (se 1 (by rfl) ⟨1865654, by rfl⟩ : syracuseStep 2487539 = 3731309) B3731309
theorem B2487569 : Blo 1657528 2487569 := bstep (se 2 (by rfl) ⟨932838, by rfl⟩ : syracuseStep 2487569 = 1865677) B1865677
theorem B2798867 : Blo 1657528 2798867 := bstep (se 1 (by rfl) ⟨2099150, by rfl⟩ : syracuseStep 2798867 = 4198301) B4198301
theorem B2487587 : Blo 1657528 2487587 := bstep (se 1 (by rfl) ⟨1865690, by rfl⟩ : syracuseStep 2487587 = 3731381) B3731381
theorem B3732785 : Blo 1657528 3732785 := bstep (se 2 (by rfl) ⟨1399794, by rfl⟩ : syracuseStep 3732785 = 2799589) B2799589
theorem B1865011 : Blo 1657528 1865011 := bstep (se 1 (by rfl) ⟨1398758, by rfl⟩ : syracuseStep 1865011 = 2797517) B2797517
theorem B2487617 : Blo 1657528 2487617 := bstep (se 2 (by rfl) ⟨932856, by rfl⟩ : syracuseStep 2487617 = 1865713) B1865713
theorem B3732803 : Blo 1657528 3732803 := bstep (se 1 (by rfl) ⟨2799602, by rfl⟩ : syracuseStep 3732803 = 5599205) B5599205
theorem B2487635 : Blo 1657528 2487635 := bstep (se 1 (by rfl) ⟨1865726, by rfl⟩ : syracuseStep 2487635 = 3731453) B3731453
theorem B2487665 : Blo 1657528 2487665 := bstep (se 2 (by rfl) ⟨932874, by rfl⟩ : syracuseStep 2487665 = 1865749) B1865749
theorem B2487683 : Blo 1657528 2487683 := bstep (se 1 (by rfl) ⟨1865762, by rfl⟩ : syracuseStep 2487683 = 3731525) B3731525
theorem B76567949 : Blo 1657528 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B2798995 : Blo 1657528 2798995 := bstep (se 1 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 2798995 = 4198493) B4198493
theorem B2487713 : Blo 1657528 2487713 := bstep (se 2 (by rfl) ⟨932892, by rfl⟩ : syracuseStep 2487713 = 1865785) B1865785
theorem B2487731 : Blo 1657528 2487731 := bstep (se 1 (by rfl) ⟨1865798, by rfl⟩ : syracuseStep 2487731 = 3731597) B3731597
theorem B1865155 : Blo 1657528 1865155 := bstep (se 1 (by rfl) ⟨1398866, by rfl⟩ : syracuseStep 1865155 = 2797733) B2797733
theorem B5600717 : Blo 1657528 5600717 := bstep (se 3 (by rfl) ⟨1050134, by rfl⟩ : syracuseStep 5600717 = 2100269) B2100269
theorem B2487761 : Blo 1657528 2487761 := bstep (se 2 (by rfl) ⟨932910, by rfl⟩ : syracuseStep 2487761 = 1865821) B1865821
theorem B26891747 : Blo 1657528 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B2487779 : Blo 1657528 2487779 := bstep (se 1 (by rfl) ⟨1865834, by rfl⟩ : syracuseStep 2487779 = 3731669) B3731669
theorem B4199921 : Blo 1657528 4199921 := bstep (se 2 (by rfl) ⟨1574970, by rfl⟩ : syracuseStep 4199921 = 3149941) B3149941
theorem B2487809 : Blo 1657528 2487809 := bstep (se 2 (by rfl) ⟨932928, by rfl⟩ : syracuseStep 2487809 = 1865857) B1865857
theorem B5600771 : Blo 1657528 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B11949581 : Blo 1657528 11949581 := bstep (se 3 (by rfl) ⟨2240546, by rfl⟩ : syracuseStep 11949581 = 4481093) B4481093
theorem B2487827 : Blo 1657528 2487827 := bstep (se 1 (by rfl) ⟨1865870, by rfl⟩ : syracuseStep 2487827 = 3731741) B3731741
theorem B2799137 : Blo 1657528 2799137 := bstep (se 2 (by rfl) ⟨1049676, by rfl⟩ : syracuseStep 2799137 = 2099353) B2099353
theorem B4199971 : Blo 1657528 4199971 := bstep (se 1 (by rfl) ⟨3149978, by rfl⟩ : syracuseStep 4199971 = 6299957) B6299957
theorem B2487857 : Blo 1657528 2487857 := bstep (se 2 (by rfl) ⟨932946, by rfl⟩ : syracuseStep 2487857 = 1865893) B1865893
theorem B2487875 : Blo 1657528 2487875 := bstep (se 1 (by rfl) ⟨1865906, by rfl⟩ : syracuseStep 2487875 = 3731813) B3731813
theorem B3733073 : Blo 1657528 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B1865299 : Blo 1657528 1865299 := bstep (se 1 (by rfl) ⟨1398974, by rfl⟩ : syracuseStep 1865299 = 2797949) B2797949
theorem B2487905 : Blo 1657528 2487905 := bstep (se 2 (by rfl) ⟨932964, by rfl⟩ : syracuseStep 2487905 = 1865929) B1865929
theorem B3733091 : Blo 1657528 3733091 := bstep (se 1 (by rfl) ⟨2799818, by rfl⟩ : syracuseStep 3733091 = 5599637) B5599637
theorem B8394353 : Blo 1657528 8394353 := bstep (se 2 (by rfl) ⟨3147882, by rfl⟩ : syracuseStep 8394353 = 6295765) B6295765
theorem B2487923 : Blo 1657528 2487923 := bstep (se 1 (by rfl) ⟨1865942, by rfl⟩ : syracuseStep 2487923 = 3731885) B3731885
theorem B4724365 : Blo 1657528 4724365 := bstep (se 3 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 4724365 = 1771637) B1771637
theorem B26908301 : Blo 1657528 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B2487953 : Blo 1657528 2487953 := bstep (se 2 (by rfl) ⟨932982, by rfl⟩ : syracuseStep 2487953 = 1865965) B1865965
theorem B2487971 : Blo 1657528 2487971 := bstep (se 1 (by rfl) ⟨1865978, by rfl⟩ : syracuseStep 2487971 = 3731957) B3731957
theorem B2799265 : Blo 1657528 2799265 := bstep (se 2 (by rfl) ⟨1049724, by rfl⟩ : syracuseStep 2799265 = 2099449) B2099449
theorem B3987107 : Blo 1657528 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B4200113 : Blo 1657528 4200113 := bstep (se 2 (by rfl) ⟨1575042, by rfl⟩ : syracuseStep 4200113 = 3150085) B3150085
theorem B2488001 : Blo 1657528 2488001 := bstep (se 2 (by rfl) ⟨933000, by rfl⟩ : syracuseStep 2488001 = 1866001) B1866001
theorem B2799299 : Blo 1657528 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B18888389 : Blo 1657528 18888389 := bstep (se 4 (by rfl) ⟨1770786, by rfl⟩ : syracuseStep 18888389 = 3541573) B3541573
theorem B2488019 : Blo 1657528 2488019 := bstep (se 1 (by rfl) ⟨1866014, by rfl⟩ : syracuseStep 2488019 = 3732029) B3732029
theorem B1865443 : Blo 1657528 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B2488049 : Blo 1657528 2488049 := bstep (se 2 (by rfl) ⟨933018, by rfl⟩ : syracuseStep 2488049 = 1866037) B1866037
theorem B2488067 : Blo 1657528 2488067 := bstep (se 1 (by rfl) ⟨1866050, by rfl⟩ : syracuseStep 2488067 = 3732101) B3732101
theorem B10630925 : Blo 1657528 10630925 := bstep (se 3 (by rfl) ⟨1993298, by rfl⟩ : syracuseStep 10630925 = 3986597) B3986597
theorem B2488097 : Blo 1657528 2488097 := bstep (se 2 (by rfl) ⟨933036, by rfl⟩ : syracuseStep 2488097 = 1866073) B1866073
theorem B5977891 : Blo 1657528 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B2488115 : Blo 1657528 2488115 := bstep (se 1 (by rfl) ⟨1866086, by rfl⟩ : syracuseStep 2488115 = 3732173) B3732173
theorem B2799427 : Blo 1657528 2799427 := bstep (se 1 (by rfl) ⟨2099570, by rfl⟩ : syracuseStep 2799427 = 4199141) B4199141
theorem B2987857 : Blo 1657528 2987857 := bstep (se 2 (by rfl) ⟨1120446, by rfl⟩ : syracuseStep 2987857 = 2240893) B2240893
theorem B2488145 : Blo 1657528 2488145 := bstep (se 2 (by rfl) ⟨933054, by rfl⟩ : syracuseStep 2488145 = 1866109) B1866109
theorem B2488163 : Blo 1657528 2488163 := bstep (se 1 (by rfl) ⟨1866122, by rfl⟩ : syracuseStep 2488163 = 3732245) B3732245
theorem B3733361 : Blo 1657528 3733361 := bstep (se 2 (by rfl) ⟨1400010, by rfl⟩ : syracuseStep 3733361 = 2800021) B2800021
theorem B1865587 : Blo 1657528 1865587 := bstep (se 1 (by rfl) ⟨1399190, by rfl⟩ : syracuseStep 1865587 = 2798381) B2798381
theorem B2488193 : Blo 1657528 2488193 := bstep (se 2 (by rfl) ⟨933072, by rfl⟩ : syracuseStep 2488193 = 1866145) B1866145
theorem B3733379 : Blo 1657528 3733379 := bstep (se 1 (by rfl) ⟨2800034, by rfl⟩ : syracuseStep 3733379 = 5600069) B5600069
theorem B2488211 : Blo 1657528 2488211 := bstep (se 1 (by rfl) ⟨1866158, by rfl⟩ : syracuseStep 2488211 = 3732317) B3732317
theorem B2488241 : Blo 1657528 2488241 := bstep (se 2 (by rfl) ⟨933090, by rfl⟩ : syracuseStep 2488241 = 1866181) B1866181
theorem B2488259 : Blo 1657528 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B5314513 : Blo 1657528 5314513 := bstep (se 2 (by rfl) ⟨1992942, by rfl⟩ : syracuseStep 5314513 = 3985885) B3985885
theorem B2799569 : Blo 1657528 2799569 := bstep (se 2 (by rfl) ⟨1049838, by rfl⟩ : syracuseStep 2799569 = 2099677) B2099677
theorem B2488289 : Blo 1657528 2488289 := bstep (se 2 (by rfl) ⟨933108, by rfl⟩ : syracuseStep 2488289 = 1866217) B1866217
theorem B2488307 : Blo 1657528 2488307 := bstep (se 1 (by rfl) ⟨1866230, by rfl⟩ : syracuseStep 2488307 = 3732461) B3732461
theorem B1865731 : Blo 1657528 1865731 := bstep (se 1 (by rfl) ⟨1399298, by rfl⟩ : syracuseStep 1865731 = 2798597) B2798597
theorem B2488337 : Blo 1657528 2488337 := bstep (se 2 (by rfl) ⟨933126, by rfl⟩ : syracuseStep 2488337 = 1866253) B1866253
theorem B2488355 : Blo 1657528 2488355 := bstep (se 1 (by rfl) ⟨1866266, by rfl⟩ : syracuseStep 2488355 = 3732533) B3732533
theorem B2488385 : Blo 1657528 2488385 := bstep (se 2 (by rfl) ⟨933144, by rfl⟩ : syracuseStep 2488385 = 1866289) B1866289
theorem B2799697 : Blo 1657528 2799697 := bstep (se 2 (by rfl) ⟨1049886, by rfl⟩ : syracuseStep 2799697 = 2099773) B2099773
theorem B2488403 : Blo 1657528 2488403 := bstep (se 1 (by rfl) ⟨1866302, by rfl⟩ : syracuseStep 2488403 = 3732605) B3732605
theorem B2488433 : Blo 1657528 2488433 := bstep (se 2 (by rfl) ⟨933162, by rfl⟩ : syracuseStep 2488433 = 1866325) B1866325
theorem B2799731 : Blo 1657528 2799731 := bstep (se 1 (by rfl) ⟨2099798, by rfl⟩ : syracuseStep 2799731 = 4199597) B4199597
theorem B2488451 : Blo 1657528 2488451 := bstep (se 1 (by rfl) ⟨1866338, by rfl⟩ : syracuseStep 2488451 = 3732677) B3732677
theorem B3733649 : Blo 1657528 3733649 := bstep (se 2 (by rfl) ⟨1400118, by rfl⟩ : syracuseStep 3733649 = 2800237) B2800237
theorem B1865875 : Blo 1657528 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B2488481 : Blo 1657528 2488481 := bstep (se 2 (by rfl) ⟨933180, by rfl⟩ : syracuseStep 2488481 = 1866361) B1866361
theorem B3733667 : Blo 1657528 3733667 := bstep (se 1 (by rfl) ⟨2800250, by rfl⟩ : syracuseStep 3733667 = 5600501) B5600501
theorem B2488499 : Blo 1657528 2488499 := bstep (se 1 (by rfl) ⟨1866374, by rfl⟩ : syracuseStep 2488499 = 3732749) B3732749
theorem B2488529 : Blo 1657528 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B2488547 : Blo 1657528 2488547 := bstep (se 1 (by rfl) ⟨1866410, by rfl⟩ : syracuseStep 2488547 = 3732821) B3732821
theorem B16152817 : Blo 1657528 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B18897137 : Blo 1657528 18897137 := bstep (se 2 (by rfl) ⟨7086426, by rfl⟩ : syracuseStep 18897137 = 14172853) B14172853
theorem B2799859 : Blo 1657528 2799859 := bstep (se 1 (by rfl) ⟨2099894, by rfl⟩ : syracuseStep 2799859 = 4199789) B4199789
theorem B2488577 : Blo 1657528 2488577 := bstep (se 2 (by rfl) ⟨933216, by rfl⟩ : syracuseStep 2488577 = 1866433) B1866433
theorem B2488595 : Blo 1657528 2488595 := bstep (se 1 (by rfl) ⟨1866446, by rfl⟩ : syracuseStep 2488595 = 3732893) B3732893
theorem B1866019 : Blo 1657528 1866019 := bstep (se 1 (by rfl) ⟨1399514, by rfl⟩ : syracuseStep 1866019 = 2799029) B2799029
theorem B2488625 : Blo 1657528 2488625 := bstep (se 2 (by rfl) ⟨933234, by rfl⟩ : syracuseStep 2488625 = 1866469) B1866469
theorem B20166965 : Blo 1657528 20166965 := bstep (se 5 (by rfl) ⟨945326, by rfl⟩ : syracuseStep 20166965 = 1890653) B1890653
theorem B2488643 : Blo 1657528 2488643 := bstep (se 1 (by rfl) ⟨1866482, by rfl⟩ : syracuseStep 2488643 = 3732965) B3732965
theorem B10221893 : Blo 1657528 10221893 := bstep (se 4 (by rfl) ⟨958302, by rfl⟩ : syracuseStep 10221893 = 1916605) B1916605
theorem B2693459 : Blo 1657528 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B2488673 : Blo 1657528 2488673 := bstep (se 2 (by rfl) ⟨933252, by rfl⟩ : syracuseStep 2488673 = 1866505) B1866505
theorem B2488691 : Blo 1657528 2488691 := bstep (se 1 (by rfl) ⟨1866518, by rfl⟩ : syracuseStep 2488691 = 3733037) B3733037
theorem B2800001 : Blo 1657528 2800001 := bstep (se 2 (by rfl) ⟨1050000, by rfl⟩ : syracuseStep 2800001 = 2100001) B2100001
theorem B2988433 : Blo 1657528 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B2488721 : Blo 1657528 2488721 := bstep (se 2 (by rfl) ⟨933270, by rfl⟩ : syracuseStep 2488721 = 1866541) B1866541
theorem B2488739 : Blo 1657528 2488739 := bstep (se 1 (by rfl) ⟨1866554, by rfl⟩ : syracuseStep 2488739 = 3733109) B3733109
theorem B3733937 : Blo 1657528 3733937 := bstep (se 2 (by rfl) ⟨1400226, by rfl⟩ : syracuseStep 3733937 = 2800453) B2800453
theorem B1866163 : Blo 1657528 1866163 := bstep (se 1 (by rfl) ⟨1399622, by rfl⟩ : syracuseStep 1866163 = 2799245) B2799245
theorem B2488769 : Blo 1657528 2488769 := bstep (se 2 (by rfl) ⟨933288, by rfl⟩ : syracuseStep 2488769 = 1866577) B1866577
theorem B2488787 : Blo 1657528 2488787 := bstep (se 1 (by rfl) ⟨1866590, by rfl⟩ : syracuseStep 2488787 = 3733181) B3733181
theorem B6380003 : Blo 1657528 6380003 := bstep (se 1 (by rfl) ⟨4785002, by rfl⟩ : syracuseStep 6380003 = 9570005) B9570005
theorem B2488817 : Blo 1657528 2488817 := bstep (se 2 (by rfl) ⟨933306, by rfl⟩ : syracuseStep 2488817 = 1866613) B1866613
theorem B2800129 : Blo 1657528 2800129 := bstep (se 2 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 2800129 = 2100097) B2100097
theorem B2488835 : Blo 1657528 2488835 := bstep (se 1 (by rfl) ⟨1866626, by rfl⟩ : syracuseStep 2488835 = 3733253) B3733253
theorem B2488865 : Blo 1657528 2488865 := bstep (se 2 (by rfl) ⟨933324, by rfl⟩ : syracuseStep 2488865 = 1866649) B1866649
theorem B2800163 : Blo 1657528 2800163 := bstep (se 1 (by rfl) ⟨2100122, by rfl⟩ : syracuseStep 2800163 = 4200245) B4200245
theorem B2488883 : Blo 1657528 2488883 := bstep (se 1 (by rfl) ⟨1866662, by rfl⟩ : syracuseStep 2488883 = 3733325) B3733325
theorem B1866307 : Blo 1657528 1866307 := bstep (se 1 (by rfl) ⟨1399730, by rfl⟩ : syracuseStep 1866307 = 2799461) B2799461
theorem B2488913 : Blo 1657528 2488913 := bstep (se 2 (by rfl) ⟨933342, by rfl⟩ : syracuseStep 2488913 = 1866685) B1866685
theorem B2488931 : Blo 1657528 2488931 := bstep (se 1 (by rfl) ⟨1866698, by rfl⟩ : syracuseStep 2488931 = 3733397) B3733397
theorem B2521729 : Blo 1657528 2521729 := bstep (se 2 (by rfl) ⟨945648, by rfl⟩ : syracuseStep 2521729 = 1891297) B1891297
theorem B2488961 : Blo 1657528 2488961 := bstep (se 2 (by rfl) ⟨933360, by rfl⟩ : syracuseStep 2488961 = 1866721) B1866721
theorem B7084685 : Blo 1657528 7084685 := bstep (se 3 (by rfl) ⟨1328378, by rfl⟩ : syracuseStep 7084685 = 2656757) B2656757
theorem B2488979 : Blo 1657528 2488979 := bstep (se 1 (by rfl) ⟨1866734, by rfl⟩ : syracuseStep 2488979 = 3733469) B3733469
theorem B5675683 : Blo 1657528 5675683 := bstep (se 1 (by rfl) ⟨4256762, by rfl⟩ : syracuseStep 5675683 = 8513525) B8513525
theorem B2800291 : Blo 1657528 2800291 := bstep (se 1 (by rfl) ⟨2100218, by rfl⟩ : syracuseStep 2800291 = 4200437) B4200437
theorem B2489009 : Blo 1657528 2489009 := bstep (se 2 (by rfl) ⟨933378, by rfl⟩ : syracuseStep 2489009 = 1866757) B1866757
theorem B2489027 : Blo 1657528 2489027 := bstep (se 1 (by rfl) ⟨1866770, by rfl⟩ : syracuseStep 2489027 = 3733541) B3733541
theorem B1866451 : Blo 1657528 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B2489057 : Blo 1657528 2489057 := bstep (se 2 (by rfl) ⟨933396, by rfl⟩ : syracuseStep 2489057 = 1866793) B1866793
theorem B2489075 : Blo 1657528 2489075 := bstep (se 1 (by rfl) ⟨1866806, by rfl⟩ : syracuseStep 2489075 = 3733613) B3733613
theorem B2489105 : Blo 1657528 2489105 := bstep (se 2 (by rfl) ⟨933414, by rfl⟩ : syracuseStep 2489105 = 1866829) B1866829
theorem B2489123 : Blo 1657528 2489123 := bstep (se 1 (by rfl) ⟨1866842, by rfl⟩ : syracuseStep 2489123 = 3733685) B3733685
theorem B2800433 : Blo 1657528 2800433 := bstep (se 2 (by rfl) ⟨1050162, by rfl⟩ : syracuseStep 2800433 = 2100325) B2100325
theorem B2489153 : Blo 1657528 2489153 := bstep (se 2 (by rfl) ⟨933432, by rfl⟩ : syracuseStep 2489153 = 1866865) B1866865
theorem B2489171 : Blo 1657528 2489171 := bstep (se 1 (by rfl) ⟨1866878, by rfl⟩ : syracuseStep 2489171 = 3733757) B3733757
theorem B1866595 : Blo 1657528 1866595 := bstep (se 1 (by rfl) ⟨1399946, by rfl⟩ : syracuseStep 1866595 = 2799893) B2799893
theorem B2489201 : Blo 1657528 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B2489219 : Blo 1657528 2489219 := bstep (se 1 (by rfl) ⟨1866914, by rfl⟩ : syracuseStep 2489219 = 3733829) B3733829
theorem B2489249 : Blo 1657528 2489249 := bstep (se 2 (by rfl) ⟨933468, by rfl⟩ : syracuseStep 2489249 = 1866937) B1866937
theorem B2489267 : Blo 1657528 2489267 := bstep (se 1 (by rfl) ⟨1866950, by rfl⟩ : syracuseStep 2489267 = 3733901) B3733901
theorem B1727443 : Blo 1657528 1727443 := bstep (se 1 (by rfl) ⟨1295582, by rfl⟩ : syracuseStep 1727443 = 2591165) B2591165
theorem B1866739 : Blo 1657528 1866739 := bstep (se 1 (by rfl) ⟨1400054, by rfl⟩ : syracuseStep 1866739 = 2800109) B2800109
theorem B8395811 : Blo 1657528 8395811 := bstep (se 1 (by rfl) ⟨6296858, by rfl⟩ : syracuseStep 8395811 = 12593717) B12593717
theorem B26901557 : Blo 1657528 26901557 := bstep (se 5 (by rfl) ⟨1261010, by rfl⟩ : syracuseStep 26901557 = 2522021) B2522021
theorem B2874467 : Blo 1657528 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B1866883 : Blo 1657528 1866883 := bstep (se 1 (by rfl) ⟨1400162, by rfl⟩ : syracuseStep 1866883 = 2800325) B2800325
theorem B1891603 : Blo 1657528 1891603 := bstep (se 1 (by rfl) ⟨1418702, by rfl⟩ : syracuseStep 1891603 = 2837405) B2837405
theorem B5750129 : Blo 1657528 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B2522611 : Blo 1657528 2522611 := bstep (se 1 (by rfl) ⟨1891958, by rfl⟩ : syracuseStep 2522611 = 3783917) B3783917
theorem B2522659 : Blo 1657528 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B5594669 : Blo 1657528 5594669 := bstep (se 3 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 5594669 = 2098001) B2098001
theorem B15949381 : Blo 1657528 15949381 := bstep (se 4 (by rfl) ⟨1495254, by rfl⟩ : syracuseStep 15949381 = 2990509) B2990509
theorem B5594723 : Blo 1657528 5594723 := bstep (se 1 (by rfl) ⟨4196042, by rfl⟩ : syracuseStep 5594723 = 8392085) B8392085
theorem B5316205 : Blo 1657528 5316205 := bstep (se 3 (by rfl) ⟨996788, by rfl⟩ : syracuseStep 5316205 = 1993577) B1993577
theorem B4480771 : Blo 1657528 4480771 := bstep (se 1 (by rfl) ⟨3360578, by rfl⟩ : syracuseStep 4480771 = 6721157) B6721157
theorem B64659221 : Blo 1657528 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B6299441 : Blo 1657528 6299441 := bstep (se 2 (by rfl) ⟨2362290, by rfl⟩ : syracuseStep 6299441 = 4724581) B4724581
theorem B8396621 : Blo 1657528 8396621 := bstep (se 3 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 8396621 = 3148733) B3148733
theorem B5594993 : Blo 1657528 5594993 := bstep (se 2 (by rfl) ⟨2098122, by rfl⟩ : syracuseStep 5594993 = 4196245) B4196245
theorem B7086001 : Blo 1657528 7086001 := bstep (se 2 (by rfl) ⟨2657250, by rfl⟩ : syracuseStep 7086001 = 5314501) B5314501
theorem B10362955 : Blo 1657528 10362955 := bstep (se 1 (by rfl) ⟨7772216, by rfl⟩ : syracuseStep 10362955 = 15544433) B15544433
theorem B1818731 : Blo 1657528 1818731 := bstep (se 1 (by rfl) ⟨1364048, by rfl⟩ : syracuseStep 1818731 = 2728097) B2728097
theorem B7086359 : Blo 1657528 7086359 := bstep (se 1 (by rfl) ⟨5314769, by rfl⟩ : syracuseStep 7086359 = 10629539) B10629539
theorem B6299927 : Blo 1657528 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B21537089 : Blo 1657528 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B6300125 : Blo 1657528 6300125 := bstep (se 3 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 6300125 = 2362547) B2362547
theorem B26894861 : Blo 1657528 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B6726347 : Blo 1657528 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B21242573 : Blo 1657528 21242573 := bstep (se 3 (by rfl) ⟨3982982, by rfl⟩ : syracuseStep 21242573 = 7965965) B7965965
theorem B1770283 : Blo 1657528 1770283 := bstep (se 1 (by rfl) ⟨1327712, by rfl⟩ : syracuseStep 1770283 = 2655425) B2655425
theorem B45376321 : Blo 1657528 45376321 := bstep (se 2 (by rfl) ⟨17016120, by rfl⟩ : syracuseStep 45376321 = 34032241) B34032241
theorem B4916057 : Blo 1657528 4916057 := bstep (se 2 (by rfl) ⟨1843521, by rfl⟩ : syracuseStep 4916057 = 3687043) B3687043
theorem B51045299 : Blo 1657528 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B76596185 : Blo 1657528 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B7562285 : Blo 1657528 7562285 := bstep (se 3 (by rfl) ⟨1417928, by rfl⟩ : syracuseStep 7562285 = 2835857) B2835857
theorem B5596235 : Blo 1657528 5596235 := bstep (se 1 (by rfl) ⟨4197176, by rfl⟩ : syracuseStep 5596235 = 8394353) B8394353
theorem B8397917 : Blo 1657528 8397917 := bstep (se 3 (by rfl) ⟨1574609, by rfl⟩ : syracuseStep 8397917 = 3149219) B3149219
theorem B12592259 : Blo 1657528 12592259 := bstep (se 1 (by rfl) ⟨9444194, by rfl⟩ : syracuseStep 12592259 = 18888389) B18888389
theorem B2098315 : Blo 1657528 2098315 := bstep (se 1 (by rfl) ⟨1573736, by rfl⟩ : syracuseStep 2098315 = 3147473) B3147473
theorem B7087283 : Blo 1657528 7087283 := bstep (se 1 (by rfl) ⟨5315462, by rfl⟩ : syracuseStep 7087283 = 10630925) B10630925
theorem B2303257 : Blo 1657528 2303257 := bstep (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) B1727443
theorem B3540275 : Blo 1657528 3540275 := bstep (se 1 (by rfl) ⟨2655206, by rfl⟩ : syracuseStep 3540275 = 5310413) B5310413
theorem B5596505 : Blo 1657528 5596505 := bstep (se 2 (by rfl) ⟨2098689, by rfl⟩ : syracuseStep 5596505 = 4197379) B4197379
theorem B55248277 : Blo 1657528 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B3147275 : Blo 1657528 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B13444643 : Blo 1657528 13444643 := bstep (se 1 (by rfl) ⟨10083482, by rfl⟩ : syracuseStep 13444643 = 20166965) B20166965
theorem B3147329 : Blo 1657528 3147329 := bstep (se 2 (by rfl) ⟨1180248, by rfl⟩ : syracuseStep 3147329 = 2360497) B2360497
theorem B4196033 : Blo 1657528 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B2361163 : Blo 1657528 2361163 := bstep (se 1 (by rfl) ⟨1770872, by rfl⟩ : syracuseStep 2361163 = 3541745) B3541745
theorem B5597207 : Blo 1657528 5597207 := bstep (se 1 (by rfl) ⟨4197905, by rfl⟩ : syracuseStep 5597207 = 8395811) B8395811
theorem B17934371 : Blo 1657528 17934371 := bstep (se 1 (by rfl) ⟨13450778, by rfl⟩ : syracuseStep 17934371 = 26901557) B26901557
theorem B5310515 : Blo 1657528 5310515 := bstep (se 1 (by rfl) ⟨3982886, by rfl⟩ : syracuseStep 5310515 = 7965773) B7965773
theorem B3729473 : Blo 1657528 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B2099287 : Blo 1657528 2099287 := bstep (se 1 (by rfl) ⟨1574465, by rfl⟩ : syracuseStep 2099287 = 3148931) B3148931
theorem B7088273 : Blo 1657528 7088273 := bstep (se 2 (by rfl) ⟨2658102, by rfl⟩ : syracuseStep 7088273 = 5316205) B5316205
theorem B7080139 : Blo 1657528 7080139 := bstep (se 1 (by rfl) ⟨5310104, by rfl⟩ : syracuseStep 7080139 = 10620209) B10620209
theorem B4196569 : Blo 1657528 4196569 := bstep (se 2 (by rfl) ⟨1573713, by rfl⟩ : syracuseStep 4196569 = 3147427) B3147427
theorem B3541249 : Blo 1657528 3541249 := bstep (se 2 (by rfl) ⟨1327968, by rfl⟩ : syracuseStep 3541249 = 2655937) B2655937
theorem B7080209 : Blo 1657528 7080209 := bstep (se 2 (by rfl) ⟨2655078, by rfl⟩ : syracuseStep 7080209 = 5310157) B5310157
theorem B3729689 : Blo 1657528 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B5974361 : Blo 1657528 5974361 := bstep (se 2 (by rfl) ⟨2240385, by rfl⟩ : syracuseStep 5974361 = 4480771) B4480771
theorem B3729779 : Blo 1657528 3729779 := bstep (se 1 (by rfl) ⟨2797334, by rfl⟩ : syracuseStep 3729779 = 5594669) B5594669
theorem B3729815 : Blo 1657528 3729815 := bstep (se 1 (by rfl) ⟨2797361, by rfl⟩ : syracuseStep 3729815 = 5594723) B5594723
theorem B3983809 : Blo 1657528 3983809 := bstep (se 2 (by rfl) ⟨1493928, by rfl⟩ : syracuseStep 3983809 = 2987857) B2987857
theorem B3148247 : Blo 1657528 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B10226137 : Blo 1657528 10226137 := bstep (se 2 (by rfl) ⟨3834801, by rfl⟩ : syracuseStep 10226137 = 7669603) B7669603
theorem B3361267 : Blo 1657528 3361267 := bstep (se 1 (by rfl) ⟨2520950, by rfl⟩ : syracuseStep 3361267 = 5041901) B5041901
theorem B5597747 : Blo 1657528 5597747 := bstep (se 1 (by rfl) ⟨4198310, by rfl⟩ : syracuseStep 5597747 = 8396621) B8396621
theorem B9448001 : Blo 1657528 9448001 := bstep (se 2 (by rfl) ⟨3543000, by rfl⟩ : syracuseStep 9448001 = 7086001) B7086001
theorem B3729995 : Blo 1657528 3729995 := bstep (se 1 (by rfl) ⟨2797496, by rfl⟩ : syracuseStep 3729995 = 5594993) B5594993
theorem B3730049 : Blo 1657528 3730049 := bstep (se 2 (by rfl) ⟨1398768, by rfl⟩ : syracuseStep 3730049 = 2797537) B2797537
theorem B1657547 : Blo 1657528 1657547 := bstep (se 1 (by rfl) ⟨1243160, by rfl⟩ : syracuseStep 1657547 = 2486321) B2486321
theorem B1657559 : Blo 1657528 1657559 := bstep (se 1 (by rfl) ⟨1243169, by rfl⟩ : syracuseStep 1657559 = 2486339) B2486339
theorem B1657579 : Blo 1657528 1657579 := bstep (se 1 (by rfl) ⟨1243184, by rfl⟩ : syracuseStep 1657579 = 2486369) B2486369
theorem B1657591 : Blo 1657528 1657591 := bstep (se 1 (by rfl) ⟨1243193, by rfl⟩ : syracuseStep 1657591 = 2486387) B2486387
theorem B1657611 : Blo 1657528 1657611 := bstep (se 1 (by rfl) ⟨1243208, by rfl⟩ : syracuseStep 1657611 = 2486417) B2486417
theorem B1657623 : Blo 1657528 1657623 := bstep (se 1 (by rfl) ⟨1243217, by rfl⟩ : syracuseStep 1657623 = 2486435) B2486435
theorem B1657643 : Blo 1657528 1657643 := bstep (se 1 (by rfl) ⟨1243232, by rfl⟩ : syracuseStep 1657643 = 2486465) B2486465
theorem B1657655 : Blo 1657528 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B5598017 : Blo 1657528 5598017 := bstep (se 2 (by rfl) ⟨2099256, by rfl⟩ : syracuseStep 5598017 = 4198513) B4198513
theorem B1657675 : Blo 1657528 1657675 := bstep (se 1 (by rfl) ⟨1243256, by rfl⟩ : syracuseStep 1657675 = 2486513) B2486513
theorem B4721483 : Blo 1657528 4721483 := bstep (se 1 (by rfl) ⟨3541112, by rfl⟩ : syracuseStep 4721483 = 7082225) B7082225
theorem B1657687 : Blo 1657528 1657687 := bstep (se 1 (by rfl) ⟨1243265, by rfl⟩ : syracuseStep 1657687 = 2486531) B2486531
theorem B3730265 : Blo 1657528 3730265 := bstep (se 2 (by rfl) ⟨1398849, by rfl⟩ : syracuseStep 3730265 = 2797699) B2797699
theorem B1657707 : Blo 1657528 1657707 := bstep (se 1 (by rfl) ⟨1243280, by rfl⟩ : syracuseStep 1657707 = 2486561) B2486561
theorem B1657719 : Blo 1657528 1657719 := bstep (se 1 (by rfl) ⟨1243289, by rfl⟩ : syracuseStep 1657719 = 2486579) B2486579
theorem B1657739 : Blo 1657528 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B2100107 : Blo 1657528 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B1657751 : Blo 1657528 1657751 := bstep (se 1 (by rfl) ⟨1243313, by rfl⟩ : syracuseStep 1657751 = 2486627) B2486627
theorem B1657771 : Blo 1657528 1657771 := bstep (se 1 (by rfl) ⟨1243328, by rfl⟩ : syracuseStep 1657771 = 2486657) B2486657
theorem B3730355 : Blo 1657528 3730355 := bstep (se 1 (by rfl) ⟨2797766, by rfl⟩ : syracuseStep 3730355 = 5595533) B5595533
theorem B1657783 : Blo 1657528 1657783 := bstep (se 1 (by rfl) ⟨1243337, by rfl⟩ : syracuseStep 1657783 = 2486675) B2486675
theorem B1657803 : Blo 1657528 1657803 := bstep (se 1 (by rfl) ⟨1243352, by rfl⟩ : syracuseStep 1657803 = 2486705) B2486705
theorem B1657815 : Blo 1657528 1657815 := bstep (se 1 (by rfl) ⟨1243361, by rfl⟩ : syracuseStep 1657815 = 2486723) B2486723
theorem B3730391 : Blo 1657528 3730391 := bstep (se 1 (by rfl) ⟨2797793, by rfl⟩ : syracuseStep 3730391 = 5595587) B5595587
theorem B1657835 : Blo 1657528 1657835 := bstep (se 1 (by rfl) ⟨1243376, by rfl⟩ : syracuseStep 1657835 = 2486753) B2486753
theorem B3148787 : Blo 1657528 3148787 := bstep (se 1 (by rfl) ⟨2361590, by rfl⟩ : syracuseStep 3148787 = 4723181) B4723181
theorem B1657847 : Blo 1657528 1657847 := bstep (se 1 (by rfl) ⟨1243385, by rfl⟩ : syracuseStep 1657847 = 2486771) B2486771
theorem B1657867 : Blo 1657528 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B1657879 : Blo 1657528 1657879 := bstep (se 1 (by rfl) ⟨1243409, by rfl⟩ : syracuseStep 1657879 = 2486819) B2486819
theorem B2362393 : Blo 1657528 2362393 := bstep (se 2 (by rfl) ⟨885897, by rfl⟩ : syracuseStep 2362393 = 1771795) B1771795
theorem B11955235 : Blo 1657528 11955235 := bstep (se 1 (by rfl) ⟨8966426, by rfl⟩ : syracuseStep 11955235 = 17932853) B17932853
theorem B1657899 : Blo 1657528 1657899 := bstep (se 1 (by rfl) ⟨1243424, by rfl⟩ : syracuseStep 1657899 = 2486849) B2486849
theorem B1657911 : Blo 1657528 1657911 := bstep (se 1 (by rfl) ⟨1243433, by rfl⟩ : syracuseStep 1657911 = 2486867) B2486867
theorem B1657931 : Blo 1657528 1657931 := bstep (se 1 (by rfl) ⟨1243448, by rfl⟩ : syracuseStep 1657931 = 2486897) B2486897
theorem B7973963 : Blo 1657528 7973963 := bstep (se 1 (by rfl) ⟨5980472, by rfl⟩ : syracuseStep 7973963 = 11960945) B11960945
theorem B1657943 : Blo 1657528 1657943 := bstep (se 1 (by rfl) ⟨1243457, by rfl⟩ : syracuseStep 1657943 = 2486915) B2486915
theorem B1657963 : Blo 1657528 1657963 := bstep (se 1 (by rfl) ⟨1243472, by rfl⟩ : syracuseStep 1657963 = 2486945) B2486945
theorem B1657975 : Blo 1657528 1657975 := bstep (se 1 (by rfl) ⟨1243481, by rfl⟩ : syracuseStep 1657975 = 2486963) B2486963
theorem B20180099 : Blo 1657528 20180099 := bstep (se 1 (by rfl) ⟨15135074, by rfl⟩ : syracuseStep 20180099 = 30270149) B30270149
theorem B1657995 : Blo 1657528 1657995 := bstep (se 1 (by rfl) ⟨1243496, by rfl⟩ : syracuseStep 1657995 = 2486993) B2486993
theorem B3730571 : Blo 1657528 3730571 := bstep (se 1 (by rfl) ⟨2797928, by rfl⟩ : syracuseStep 3730571 = 5595857) B5595857
theorem B1658007 : Blo 1657528 1658007 := bstep (se 1 (by rfl) ⟨1243505, by rfl⟩ : syracuseStep 1658007 = 2487011) B2487011
theorem B8400023 : Blo 1657528 8400023 := bstep (se 1 (by rfl) ⟨6300017, by rfl⟩ : syracuseStep 8400023 = 12600035) B12600035
theorem B1658027 : Blo 1657528 1658027 := bstep (se 1 (by rfl) ⟨1243520, by rfl⟩ : syracuseStep 1658027 = 2487041) B2487041
theorem B7179443 : Blo 1657528 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B1658039 : Blo 1657528 1658039 := bstep (se 1 (by rfl) ⟨1243529, by rfl⟩ : syracuseStep 1658039 = 2487059) B2487059
theorem B3730625 : Blo 1657528 3730625 := bstep (se 2 (by rfl) ⟨1398984, by rfl⟩ : syracuseStep 3730625 = 2797969) B2797969
theorem B1658059 : Blo 1657528 1658059 := bstep (se 1 (by rfl) ⟨1243544, by rfl⟩ : syracuseStep 1658059 = 2487089) B2487089
theorem B1658071 : Blo 1657528 1658071 := bstep (se 1 (by rfl) ⟨1243553, by rfl⟩ : syracuseStep 1658071 = 2487107) B2487107
theorem B1658091 : Blo 1657528 1658091 := bstep (se 1 (by rfl) ⟨1243568, by rfl⟩ : syracuseStep 1658091 = 2487137) B2487137
theorem B1658103 : Blo 1657528 1658103 := bstep (se 1 (by rfl) ⟨1243577, by rfl⟩ : syracuseStep 1658103 = 2487155) B2487155
theorem B1658123 : Blo 1657528 1658123 := bstep (se 1 (by rfl) ⟨1243592, by rfl⟩ : syracuseStep 1658123 = 2487185) B2487185
theorem B1658135 : Blo 1657528 1658135 := bstep (se 1 (by rfl) ⟨1243601, by rfl⟩ : syracuseStep 1658135 = 2487203) B2487203
theorem B1658155 : Blo 1657528 1658155 := bstep (se 1 (by rfl) ⟨1243616, by rfl⟩ : syracuseStep 1658155 = 2487233) B2487233
theorem B4197683 : Blo 1657528 4197683 := bstep (se 1 (by rfl) ⟨3148262, by rfl⟩ : syracuseStep 4197683 = 6296525) B6296525
theorem B1658167 : Blo 1657528 1658167 := bstep (se 1 (by rfl) ⟨1243625, by rfl⟩ : syracuseStep 1658167 = 2487251) B2487251
theorem B1658187 : Blo 1657528 1658187 := bstep (se 1 (by rfl) ⟨1243640, by rfl⟩ : syracuseStep 1658187 = 2487281) B2487281
theorem B1658199 : Blo 1657528 1658199 := bstep (se 1 (by rfl) ⟨1243649, by rfl⟩ : syracuseStep 1658199 = 2487299) B2487299
theorem B5598557 : Blo 1657528 5598557 := bstep (se 3 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 5598557 = 2099459) B2099459
theorem B1658219 : Blo 1657528 1658219 := bstep (se 1 (by rfl) ⟨1243664, by rfl⟩ : syracuseStep 1658219 = 2487329) B2487329
theorem B1658231 : Blo 1657528 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B1658251 : Blo 1657528 1658251 := bstep (se 1 (by rfl) ⟨1243688, by rfl⟩ : syracuseStep 1658251 = 2487377) B2487377
theorem B1658263 : Blo 1657528 1658263 := bstep (se 1 (by rfl) ⟨1243697, by rfl⟩ : syracuseStep 1658263 = 2487395) B2487395
theorem B3730841 : Blo 1657528 3730841 := bstep (se 2 (by rfl) ⟨1399065, by rfl⟩ : syracuseStep 3730841 = 2798131) B2798131
theorem B1658283 : Blo 1657528 1658283 := bstep (se 1 (by rfl) ⟨1243712, by rfl⟩ : syracuseStep 1658283 = 2487425) B2487425
theorem B1658295 : Blo 1657528 1658295 := bstep (se 1 (by rfl) ⟨1243721, by rfl⟩ : syracuseStep 1658295 = 2487443) B2487443
theorem B1658315 : Blo 1657528 1658315 := bstep (se 1 (by rfl) ⟨1243736, by rfl⟩ : syracuseStep 1658315 = 2487473) B2487473
theorem B4484555 : Blo 1657528 4484555 := bstep (se 1 (by rfl) ⟨3363416, by rfl⟩ : syracuseStep 4484555 = 6726833) B6726833
theorem B1658327 : Blo 1657528 1658327 := bstep (se 1 (by rfl) ⟨1243745, by rfl⟩ : syracuseStep 1658327 = 2487491) B2487491
theorem B3149273 : Blo 1657528 3149273 := bstep (se 2 (by rfl) ⟨1180977, by rfl⟩ : syracuseStep 3149273 = 2361955) B2361955
theorem B1658347 : Blo 1657528 1658347 := bstep (se 1 (by rfl) ⟨1243760, by rfl⟩ : syracuseStep 1658347 = 2487521) B2487521
theorem B3730931 : Blo 1657528 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B1658359 : Blo 1657528 1658359 := bstep (se 1 (by rfl) ⟨1243769, by rfl⟩ : syracuseStep 1658359 = 2487539) B2487539
theorem B3362305 : Blo 1657528 3362305 := bstep (se 2 (by rfl) ⟨1260864, by rfl⟩ : syracuseStep 3362305 = 2521729) B2521729
theorem B1658379 : Blo 1657528 1658379 := bstep (se 1 (by rfl) ⟨1243784, by rfl⟩ : syracuseStep 1658379 = 2487569) B2487569
theorem B3730967 : Blo 1657528 3730967 := bstep (se 1 (by rfl) ⟨2798225, by rfl⟩ : syracuseStep 3730967 = 5596451) B5596451
theorem B1658391 : Blo 1657528 1658391 := bstep (se 1 (by rfl) ⟨1243793, by rfl⟩ : syracuseStep 1658391 = 2487587) B2487587
theorem B1658411 : Blo 1657528 1658411 := bstep (se 1 (by rfl) ⟨1243808, by rfl⟩ : syracuseStep 1658411 = 2487617) B2487617
theorem B1658423 : Blo 1657528 1658423 := bstep (se 1 (by rfl) ⟨1243817, by rfl⟩ : syracuseStep 1658423 = 2487635) B2487635
theorem B1658443 : Blo 1657528 1658443 := bstep (se 1 (by rfl) ⟨1243832, by rfl⟩ : syracuseStep 1658443 = 2487665) B2487665
theorem B4484683 : Blo 1657528 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B1658455 : Blo 1657528 1658455 := bstep (se 1 (by rfl) ⟨1243841, by rfl⟩ : syracuseStep 1658455 = 2487683) B2487683
theorem B4197977 : Blo 1657528 4197977 := bstep (se 2 (by rfl) ⟨1574241, by rfl⟩ : syracuseStep 4197977 = 3148483) B3148483
theorem B10620517 : Blo 1657528 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B1658475 : Blo 1657528 1658475 := bstep (se 1 (by rfl) ⟨1243856, by rfl⟩ : syracuseStep 1658475 = 2487713) B2487713
theorem B1658487 : Blo 1657528 1658487 := bstep (se 1 (by rfl) ⟨1243865, by rfl⟩ : syracuseStep 1658487 = 2487731) B2487731
theorem B1658507 : Blo 1657528 1658507 := bstep (se 1 (by rfl) ⟨1243880, by rfl⟩ : syracuseStep 1658507 = 2487761) B2487761
theorem B17927831 : Blo 1657528 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B1658519 : Blo 1657528 1658519 := bstep (se 1 (by rfl) ⟨1243889, by rfl⟩ : syracuseStep 1658519 = 2487779) B2487779
theorem B1658539 : Blo 1657528 1658539 := bstep (se 1 (by rfl) ⟨1243904, by rfl⟩ : syracuseStep 1658539 = 2487809) B2487809
theorem B7966387 : Blo 1657528 7966387 := bstep (se 1 (by rfl) ⟨5974790, by rfl⟩ : syracuseStep 7966387 = 11949581) B11949581
theorem B1658551 : Blo 1657528 1658551 := bstep (se 1 (by rfl) ⟨1243913, by rfl⟩ : syracuseStep 1658551 = 2487827) B2487827
theorem B3731147 : Blo 1657528 3731147 := bstep (se 1 (by rfl) ⟨2798360, by rfl⟩ : syracuseStep 3731147 = 5596721) B5596721
theorem B1658571 : Blo 1657528 1658571 := bstep (se 1 (by rfl) ⟨1243928, by rfl⟩ : syracuseStep 1658571 = 2487857) B2487857
theorem B1658583 : Blo 1657528 1658583 := bstep (se 1 (by rfl) ⟨1243937, by rfl⟩ : syracuseStep 1658583 = 2487875) B2487875
theorem B8392409 : Blo 1657528 8392409 := bstep (se 2 (by rfl) ⟨3147153, by rfl⟩ : syracuseStep 8392409 = 6294307) B6294307
theorem B10088153 : Blo 1657528 10088153 := bstep (se 2 (by rfl) ⟨3783057, by rfl⟩ : syracuseStep 10088153 = 7566115) B7566115
theorem B1658603 : Blo 1657528 1658603 := bstep (se 1 (by rfl) ⟨1243952, by rfl⟩ : syracuseStep 1658603 = 2487905) B2487905
theorem B1658615 : Blo 1657528 1658615 := bstep (se 1 (by rfl) ⟨1243961, by rfl⟩ : syracuseStep 1658615 = 2487923) B2487923
theorem B3731201 : Blo 1657528 3731201 := bstep (se 2 (by rfl) ⟨1399200, by rfl⟩ : syracuseStep 3731201 = 2798401) B2798401
theorem B1658635 : Blo 1657528 1658635 := bstep (se 1 (by rfl) ⟨1243976, by rfl⟩ : syracuseStep 1658635 = 2487953) B2487953
theorem B1658647 : Blo 1657528 1658647 := bstep (se 1 (by rfl) ⟨1243985, by rfl⟩ : syracuseStep 1658647 = 2487971) B2487971
theorem B2658071 : Blo 1657528 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B1658667 : Blo 1657528 1658667 := bstep (se 1 (by rfl) ⟨1244000, by rfl⟩ : syracuseStep 1658667 = 2488001) B2488001
theorem B1658679 : Blo 1657528 1658679 := bstep (se 1 (by rfl) ⟨1244009, by rfl⟩ : syracuseStep 1658679 = 2488019) B2488019
theorem B1658699 : Blo 1657528 1658699 := bstep (se 1 (by rfl) ⟨1244024, by rfl⟩ : syracuseStep 1658699 = 2488049) B2488049
theorem B1658711 : Blo 1657528 1658711 := bstep (se 1 (by rfl) ⟨1244033, by rfl⟩ : syracuseStep 1658711 = 2488067) B2488067
theorem B1658731 : Blo 1657528 1658731 := bstep (se 1 (by rfl) ⟨1244048, by rfl⟩ : syracuseStep 1658731 = 2488097) B2488097
theorem B1658743 : Blo 1657528 1658743 := bstep (se 1 (by rfl) ⟨1244057, by rfl⟩ : syracuseStep 1658743 = 2488115) B2488115
theorem B1658763 : Blo 1657528 1658763 := bstep (se 1 (by rfl) ⟨1244072, by rfl⟩ : syracuseStep 1658763 = 2488145) B2488145
theorem B2797463 : Blo 1657528 2797463 := bstep (se 1 (by rfl) ⟨2098097, by rfl⟩ : syracuseStep 2797463 = 4196195) B4196195
theorem B1658775 : Blo 1657528 1658775 := bstep (se 1 (by rfl) ⟨1244081, by rfl⟩ : syracuseStep 1658775 = 2488163) B2488163
theorem B1658795 : Blo 1657528 1658795 := bstep (se 1 (by rfl) ⟨1244096, by rfl⟩ : syracuseStep 1658795 = 2488193) B2488193
theorem B7081901 : Blo 1657528 7081901 := bstep (se 3 (by rfl) ⟨1327856, by rfl⟩ : syracuseStep 7081901 = 2655713) B2655713
theorem B1658807 : Blo 1657528 1658807 := bstep (se 1 (by rfl) ⟨1244105, by rfl⟩ : syracuseStep 1658807 = 2488211) B2488211
theorem B1658827 : Blo 1657528 1658827 := bstep (se 1 (by rfl) ⟨1244120, by rfl⟩ : syracuseStep 1658827 = 2488241) B2488241
theorem B1658839 : Blo 1657528 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B3731417 : Blo 1657528 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B1658859 : Blo 1657528 1658859 := bstep (se 1 (by rfl) ⟨1244144, by rfl⟩ : syracuseStep 1658859 = 2488289) B2488289
theorem B1658871 : Blo 1657528 1658871 := bstep (se 1 (by rfl) ⟨1244153, by rfl⟩ : syracuseStep 1658871 = 2488307) B2488307
theorem B1658891 : Blo 1657528 1658891 := bstep (se 1 (by rfl) ⟨1244168, by rfl⟩ : syracuseStep 1658891 = 2488337) B2488337
theorem B2797591 : Blo 1657528 2797591 := bstep (se 1 (by rfl) ⟨2098193, by rfl⟩ : syracuseStep 2797591 = 4196387) B4196387
theorem B2486297 : Blo 1657528 2486297 := bstep (se 2 (by rfl) ⟨932361, by rfl⟩ : syracuseStep 2486297 = 1864723) B1864723
theorem B1658903 : Blo 1657528 1658903 := bstep (se 1 (by rfl) ⟨1244177, by rfl⟩ : syracuseStep 1658903 = 2488355) B2488355
theorem B1658923 : Blo 1657528 1658923 := bstep (se 1 (by rfl) ⟨1244192, by rfl⟩ : syracuseStep 1658923 = 2488385) B2488385
theorem B3731507 : Blo 1657528 3731507 := bstep (se 1 (by rfl) ⟨2798630, by rfl⟩ : syracuseStep 3731507 = 5597261) B5597261
theorem B1658935 : Blo 1657528 1658935 := bstep (se 1 (by rfl) ⟨1244201, by rfl⟩ : syracuseStep 1658935 = 2488403) B2488403
theorem B14004299 : Blo 1657528 14004299 := bstep (se 1 (by rfl) ⟨10503224, by rfl⟩ : syracuseStep 14004299 = 21006449) B21006449
theorem B1658955 : Blo 1657528 1658955 := bstep (se 1 (by rfl) ⟨1244216, by rfl⟩ : syracuseStep 1658955 = 2488433) B2488433
theorem B3731543 : Blo 1657528 3731543 := bstep (se 1 (by rfl) ⟨2798657, by rfl⟩ : syracuseStep 3731543 = 5597315) B5597315
theorem B1658967 : Blo 1657528 1658967 := bstep (se 1 (by rfl) ⟨1244225, by rfl⟩ : syracuseStep 1658967 = 2488451) B2488451
theorem B4722781 : Blo 1657528 4722781 := bstep (se 3 (by rfl) ⟨885521, by rfl⟩ : syracuseStep 4722781 = 1771043) B1771043
theorem B10088549 : Blo 1657528 10088549 := bstep (se 4 (by rfl) ⟨945801, by rfl⟩ : syracuseStep 10088549 = 1891603) B1891603
theorem B1658987 : Blo 1657528 1658987 := bstep (se 1 (by rfl) ⟨1244240, by rfl⟩ : syracuseStep 1658987 = 2488481) B2488481
theorem B1658999 : Blo 1657528 1658999 := bstep (se 1 (by rfl) ⟨1244249, by rfl⟩ : syracuseStep 1658999 = 2488499) B2488499
theorem B2486411 : Blo 1657528 2486411 := bstep (se 1 (by rfl) ⟨1864808, by rfl⟩ : syracuseStep 2486411 = 3729617) B3729617
theorem B1659019 : Blo 1657528 1659019 := bstep (se 1 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 1659019 = 2488529) B2488529
theorem B2486423 : Blo 1657528 2486423 := bstep (se 1 (by rfl) ⟨1864817, by rfl⟩ : syracuseStep 2486423 = 3729635) B3729635
theorem B1659031 : Blo 1657528 1659031 := bstep (se 1 (by rfl) ⟨1244273, by rfl⟩ : syracuseStep 1659031 = 2488547) B2488547
theorem B1659051 : Blo 1657528 1659051 := bstep (se 1 (by rfl) ⟨1244288, by rfl⟩ : syracuseStep 1659051 = 2488577) B2488577
theorem B8515763 : Blo 1657528 8515763 := bstep (se 1 (by rfl) ⟨6386822, by rfl⟩ : syracuseStep 8515763 = 12773645) B12773645
theorem B1659063 : Blo 1657528 1659063 := bstep (se 1 (by rfl) ⟨1244297, by rfl⟩ : syracuseStep 1659063 = 2488595) B2488595
theorem B1659083 : Blo 1657528 1659083 := bstep (se 1 (by rfl) ⟨1244312, by rfl⟩ : syracuseStep 1659083 = 2488625) B2488625
theorem B1659095 : Blo 1657528 1659095 := bstep (se 1 (by rfl) ⟨1244321, by rfl⟩ : syracuseStep 1659095 = 2488643) B2488643
theorem B2486489 : Blo 1657528 2486489 := bstep (se 2 (by rfl) ⟨932433, by rfl⟩ : syracuseStep 2486489 = 1864867) B1864867
theorem B1659115 : Blo 1657528 1659115 := bstep (se 1 (by rfl) ⟨1244336, by rfl⟩ : syracuseStep 1659115 = 2488673) B2488673
theorem B1659127 : Blo 1657528 1659127 := bstep (se 1 (by rfl) ⟨1244345, by rfl⟩ : syracuseStep 1659127 = 2488691) B2488691
theorem B3731723 : Blo 1657528 3731723 := bstep (se 1 (by rfl) ⟨2798792, by rfl⟩ : syracuseStep 3731723 = 5597585) B5597585
theorem B1659147 : Blo 1657528 1659147 := bstep (se 1 (by rfl) ⟨1244360, by rfl⟩ : syracuseStep 1659147 = 2488721) B2488721
theorem B1659159 : Blo 1657528 1659159 := bstep (se 1 (by rfl) ⟨1244369, by rfl⟩ : syracuseStep 1659159 = 2488739) B2488739
theorem B1659179 : Blo 1657528 1659179 := bstep (se 1 (by rfl) ⟨1244384, by rfl⟩ : syracuseStep 1659179 = 2488769) B2488769
theorem B1659191 : Blo 1657528 1659191 := bstep (se 1 (by rfl) ⟨1244393, by rfl⟩ : syracuseStep 1659191 = 2488787) B2488787
theorem B3731777 : Blo 1657528 3731777 := bstep (se 2 (by rfl) ⟨1399416, by rfl⟩ : syracuseStep 3731777 = 2798833) B2798833
theorem B2486603 : Blo 1657528 2486603 := bstep (se 1 (by rfl) ⟨1864952, by rfl⟩ : syracuseStep 2486603 = 3729905) B3729905
theorem B1659211 : Blo 1657528 1659211 := bstep (se 1 (by rfl) ⟨1244408, by rfl⟩ : syracuseStep 1659211 = 2488817) B2488817
theorem B2486615 : Blo 1657528 2486615 := bstep (se 1 (by rfl) ⟨1864961, by rfl⟩ : syracuseStep 2486615 = 3729923) B3729923
theorem B1659223 : Blo 1657528 1659223 := bstep (se 1 (by rfl) ⟨1244417, by rfl⟩ : syracuseStep 1659223 = 2488835) B2488835
theorem B3543385 : Blo 1657528 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B5312861 : Blo 1657528 5312861 := bstep (se 3 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 5312861 = 1992323) B1992323
theorem B1659243 : Blo 1657528 1659243 := bstep (se 1 (by rfl) ⟨1244432, by rfl⟩ : syracuseStep 1659243 = 2488865) B2488865
theorem B1659255 : Blo 1657528 1659255 := bstep (se 1 (by rfl) ⟨1244441, by rfl⟩ : syracuseStep 1659255 = 2488883) B2488883
theorem B1659275 : Blo 1657528 1659275 := bstep (se 1 (by rfl) ⟨1244456, by rfl⟩ : syracuseStep 1659275 = 2488913) B2488913
theorem B1659287 : Blo 1657528 1659287 := bstep (se 1 (by rfl) ⟨1244465, by rfl⟩ : syracuseStep 1659287 = 2488931) B2488931
theorem B2486681 : Blo 1657528 2486681 := bstep (se 2 (by rfl) ⟨932505, by rfl⟩ : syracuseStep 2486681 = 1865011) B1865011
theorem B1659307 : Blo 1657528 1659307 := bstep (se 1 (by rfl) ⟨1244480, by rfl⟩ : syracuseStep 1659307 = 2488961) B2488961
theorem B4723123 : Blo 1657528 4723123 := bstep (se 1 (by rfl) ⟨3542342, by rfl⟩ : syracuseStep 4723123 = 7084685) B7084685
theorem B1659319 : Blo 1657528 1659319 := bstep (se 1 (by rfl) ⟨1244489, by rfl⟩ : syracuseStep 1659319 = 2488979) B2488979
theorem B5599691 : Blo 1657528 5599691 := bstep (se 1 (by rfl) ⟨4199768, by rfl⟩ : syracuseStep 5599691 = 8399537) B8399537
theorem B1659339 : Blo 1657528 1659339 := bstep (se 1 (by rfl) ⟨1244504, by rfl⟩ : syracuseStep 1659339 = 2489009) B2489009
theorem B12595661 : Blo 1657528 12595661 := bstep (se 3 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 12595661 = 4723373) B4723373
theorem B1659351 : Blo 1657528 1659351 := bstep (se 1 (by rfl) ⟨1244513, by rfl⟩ : syracuseStep 1659351 = 2489027) B2489027
theorem B1659371 : Blo 1657528 1659371 := bstep (se 1 (by rfl) ⟨1244528, by rfl⟩ : syracuseStep 1659371 = 2489057) B2489057
theorem B1659383 : Blo 1657528 1659383 := bstep (se 1 (by rfl) ⟨1244537, by rfl⟩ : syracuseStep 1659383 = 2489075) B2489075
theorem B2486795 : Blo 1657528 2486795 := bstep (se 1 (by rfl) ⟨1865096, by rfl⟩ : syracuseStep 2486795 = 3730193) B3730193
theorem B1659403 : Blo 1657528 1659403 := bstep (se 1 (by rfl) ⟨1244552, by rfl⟩ : syracuseStep 1659403 = 2489105) B2489105
theorem B2486807 : Blo 1657528 2486807 := bstep (se 1 (by rfl) ⟨1865105, by rfl⟩ : syracuseStep 2486807 = 3730211) B3730211
theorem B1659415 : Blo 1657528 1659415 := bstep (se 1 (by rfl) ⟨1244561, by rfl⟩ : syracuseStep 1659415 = 2489123) B2489123
theorem B3731993 : Blo 1657528 3731993 := bstep (se 2 (by rfl) ⟨1399497, by rfl⟩ : syracuseStep 3731993 = 2798995) B2798995
theorem B1659435 : Blo 1657528 1659435 := bstep (se 1 (by rfl) ⟨1244576, by rfl⟩ : syracuseStep 1659435 = 2489153) B2489153
theorem B9572909 : Blo 1657528 9572909 := bstep (se 3 (by rfl) ⟨1794920, by rfl⟩ : syracuseStep 9572909 = 3589841) B3589841
theorem B1659447 : Blo 1657528 1659447 := bstep (se 1 (by rfl) ⟨1244585, by rfl⟩ : syracuseStep 1659447 = 2489171) B2489171
theorem B1659467 : Blo 1657528 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B1659479 : Blo 1657528 1659479 := bstep (se 1 (by rfl) ⟨1244609, by rfl⟩ : syracuseStep 1659479 = 2489219) B2489219
theorem B2486873 : Blo 1657528 2486873 := bstep (se 2 (by rfl) ⟨932577, by rfl⟩ : syracuseStep 2486873 = 1865155) B1865155
theorem B7082585 : Blo 1657528 7082585 := bstep (se 2 (by rfl) ⟨2655969, by rfl⟩ : syracuseStep 7082585 = 5311939) B5311939
theorem B1659499 : Blo 1657528 1659499 := bstep (se 1 (by rfl) ⟨1244624, by rfl⟩ : syracuseStep 1659499 = 2489249) B2489249
theorem B3732083 : Blo 1657528 3732083 := bstep (se 1 (by rfl) ⟨2799062, by rfl⟩ : syracuseStep 3732083 = 5598125) B5598125
theorem B1659511 : Blo 1657528 1659511 := bstep (se 1 (by rfl) ⟨1244633, by rfl⟩ : syracuseStep 1659511 = 2489267) B2489267
theorem B2798219 : Blo 1657528 2798219 := bstep (se 1 (by rfl) ⟨2098664, by rfl⟩ : syracuseStep 2798219 = 4197329) B4197329
theorem B24228503 : Blo 1657528 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B3732119 : Blo 1657528 3732119 := bstep (se 1 (by rfl) ⟨2799089, by rfl⟩ : syracuseStep 3732119 = 5598179) B5598179
theorem B3363481 : Blo 1657528 3363481 := bstep (se 2 (by rfl) ⟨1261305, by rfl⟩ : syracuseStep 3363481 = 2522611) B2522611
theorem B6296237 : Blo 1657528 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B14168753 : Blo 1657528 14168753 := bstep (se 2 (by rfl) ⟨5313282, by rfl⟩ : syracuseStep 14168753 = 10626565) B10626565
theorem B2486987 : Blo 1657528 2486987 := bstep (se 1 (by rfl) ⟨1865240, by rfl⟩ : syracuseStep 2486987 = 3730481) B3730481
theorem B2486999 : Blo 1657528 2486999 := bstep (se 1 (by rfl) ⟨1865249, by rfl⟩ : syracuseStep 2486999 = 3730499) B3730499
theorem B3363545 : Blo 1657528 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B5599961 : Blo 1657528 5599961 := bstep (se 2 (by rfl) ⟨2099985, by rfl⟩ : syracuseStep 5599961 = 4199971) B4199971
theorem B15938309 : Blo 1657528 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B2798347 : Blo 1657528 2798347 := bstep (se 1 (by rfl) ⟨2098760, by rfl⟩ : syracuseStep 2798347 = 4197521) B4197521
theorem B2487065 : Blo 1657528 2487065 := bstep (se 2 (by rfl) ⟨932649, by rfl⟩ : syracuseStep 2487065 = 1865299) B1865299
theorem B7566155 : Blo 1657528 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B3732299 : Blo 1657528 3732299 := bstep (se 1 (by rfl) ⟨2799224, by rfl⟩ : syracuseStep 3732299 = 5598449) B5598449
theorem B3732353 : Blo 1657528 3732353 := bstep (se 2 (by rfl) ⟨1399632, by rfl⟩ : syracuseStep 3732353 = 2799265) B2799265
theorem B2487179 : Blo 1657528 2487179 := bstep (se 1 (by rfl) ⟨1865384, by rfl⟩ : syracuseStep 2487179 = 3730769) B3730769
theorem B2487191 : Blo 1657528 2487191 := bstep (se 1 (by rfl) ⟨1865393, by rfl⟩ : syracuseStep 2487191 = 3730787) B3730787
theorem B5976983 : Blo 1657528 5976983 := bstep (se 1 (by rfl) ⟨4482737, by rfl⟩ : syracuseStep 5976983 = 8965475) B8965475
theorem B2798489 : Blo 1657528 2798489 := bstep (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) B2098867
theorem B9450391 : Blo 1657528 9450391 := bstep (se 1 (by rfl) ⟨7087793, by rfl⟩ : syracuseStep 9450391 = 14175587) B14175587
theorem B12596147 : Blo 1657528 12596147 := bstep (se 1 (by rfl) ⟨9447110, by rfl⟩ : syracuseStep 12596147 = 18894221) B18894221
theorem B2487257 : Blo 1657528 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B2798617 : Blo 1657528 2798617 := bstep (se 2 (by rfl) ⟨1049481, by rfl⟩ : syracuseStep 2798617 = 2098963) B2098963
theorem B1864759 : Blo 1657528 1864759 := bstep (se 1 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 1864759 = 2797139) B2797139
theorem B2487371 : Blo 1657528 2487371 := bstep (se 1 (by rfl) ⟨1865528, by rfl⟩ : syracuseStep 2487371 = 3731057) B3731057
theorem B2487383 : Blo 1657528 2487383 := bstep (se 1 (by rfl) ⟨1865537, by rfl⟩ : syracuseStep 2487383 = 3731075) B3731075
theorem B3732569 : Blo 1657528 3732569 := bstep (se 2 (by rfl) ⟨1399713, by rfl⟩ : syracuseStep 3732569 = 2799427) B2799427
theorem B2487449 : Blo 1657528 2487449 := bstep (se 2 (by rfl) ⟨932793, by rfl⟩ : syracuseStep 2487449 = 1865587) B1865587
theorem B3732659 : Blo 1657528 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B4199627 : Blo 1657528 4199627 := bstep (se 1 (by rfl) ⟨3149720, by rfl⟩ : syracuseStep 4199627 = 6299441) B6299441
theorem B3732695 : Blo 1657528 3732695 := bstep (se 1 (by rfl) ⟨2799521, by rfl⟩ : syracuseStep 3732695 = 5599043) B5599043
theorem B1864939 : Blo 1657528 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B2487563 : Blo 1657528 2487563 := bstep (se 1 (by rfl) ⟨1865672, by rfl⟩ : syracuseStep 2487563 = 3731345) B3731345
theorem B2487575 : Blo 1657528 2487575 := bstep (se 1 (by rfl) ⟨1865681, by rfl⟩ : syracuseStep 2487575 = 3731363) B3731363
theorem B8394029 : Blo 1657528 8394029 := bstep (se 3 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 8394029 = 3147761) B3147761
theorem B1865047 : Blo 1657528 1865047 := bstep (se 1 (by rfl) ⟨1398785, by rfl⟩ : syracuseStep 1865047 = 2797571) B2797571
theorem B2487641 : Blo 1657528 2487641 := bstep (se 2 (by rfl) ⟨932865, by rfl⟩ : syracuseStep 2487641 = 1865731) B1865731
theorem B4724057 : Blo 1657528 4724057 := bstep (se 2 (by rfl) ⟨1771521, by rfl⟩ : syracuseStep 4724057 = 3543043) B3543043
theorem B14169437 : Blo 1657528 14169437 := bstep (se 3 (by rfl) ⟨2656769, by rfl⟩ : syracuseStep 14169437 = 5313539) B5313539
theorem B5977475 : Blo 1657528 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B2241931 : Blo 1657528 2241931 := bstep (se 1 (by rfl) ⟨1681448, by rfl⟩ : syracuseStep 2241931 = 3362897) B3362897
theorem B3732875 : Blo 1657528 3732875 := bstep (se 1 (by rfl) ⟨2799656, by rfl⟩ : syracuseStep 3732875 = 5599313) B5599313
theorem B5600663 : Blo 1657528 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B6297011 : Blo 1657528 6297011 := bstep (se 1 (by rfl) ⟨4722758, by rfl⟩ : syracuseStep 6297011 = 9445517) B9445517
theorem B3732929 : Blo 1657528 3732929 := bstep (se 2 (by rfl) ⟨1399848, by rfl⟩ : syracuseStep 3732929 = 2799697) B2799697
theorem B2487755 : Blo 1657528 2487755 := bstep (se 1 (by rfl) ⟨1865816, by rfl⟩ : syracuseStep 2487755 = 3731633) B3731633
theorem B2487767 : Blo 1657528 2487767 := bstep (se 1 (by rfl) ⟨1865825, by rfl⟩ : syracuseStep 2487767 = 3731651) B3731651
theorem B1865227 : Blo 1657528 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B2487833 : Blo 1657528 2487833 := bstep (se 2 (by rfl) ⟨932937, by rfl⟩ : syracuseStep 2487833 = 1865875) B1865875
theorem B2799191 : Blo 1657528 2799191 := bstep (se 1 (by rfl) ⟨2099393, by rfl⟩ : syracuseStep 2799191 = 4198787) B4198787
theorem B4789849 : Blo 1657528 4789849 := bstep (se 2 (by rfl) ⟨1796193, by rfl⟩ : syracuseStep 4789849 = 3592387) B3592387
theorem B1865335 : Blo 1657528 1865335 := bstep (se 1 (by rfl) ⟨1399001, by rfl⟩ : syracuseStep 1865335 = 2798003) B2798003
theorem B2487947 : Blo 1657528 2487947 := bstep (se 1 (by rfl) ⟨1865960, by rfl⟩ : syracuseStep 2487947 = 3731921) B3731921
theorem B2487959 : Blo 1657528 2487959 := bstep (se 1 (by rfl) ⟨1865969, by rfl⟩ : syracuseStep 2487959 = 3731939) B3731939
theorem B3733145 : Blo 1657528 3733145 := bstep (se 2 (by rfl) ⟨1399929, by rfl⟩ : syracuseStep 3733145 = 2799859) B2799859
theorem B2987713 : Blo 1657528 2987713 := bstep (se 2 (by rfl) ⟨1120392, by rfl⟩ : syracuseStep 2987713 = 2240785) B2240785
theorem B2799319 : Blo 1657528 2799319 := bstep (se 1 (by rfl) ⟨2099489, by rfl⟩ : syracuseStep 2799319 = 4198979) B4198979
theorem B2488025 : Blo 1657528 2488025 := bstep (se 2 (by rfl) ⟨933009, by rfl⟩ : syracuseStep 2488025 = 1866019) B1866019
theorem B3733235 : Blo 1657528 3733235 := bstep (se 1 (by rfl) ⟨2799926, by rfl⟩ : syracuseStep 3733235 = 5599853) B5599853
theorem B3733271 : Blo 1657528 3733271 := bstep (se 1 (by rfl) ⟨2799953, by rfl⟩ : syracuseStep 3733271 = 5599907) B5599907
theorem B1865515 : Blo 1657528 1865515 := bstep (se 1 (by rfl) ⟨1399136, by rfl⟩ : syracuseStep 1865515 = 2798273) B2798273
theorem B5977907 : Blo 1657528 5977907 := bstep (se 1 (by rfl) ⟨4483430, by rfl⟩ : syracuseStep 5977907 = 8966861) B8966861
theorem B15931201 : Blo 1657528 15931201 := bstep (se 2 (by rfl) ⟨5974200, by rfl⟩ : syracuseStep 15931201 = 11948401) B11948401
theorem B2488139 : Blo 1657528 2488139 := bstep (se 1 (by rfl) ⟨1866104, by rfl⟩ : syracuseStep 2488139 = 3732209) B3732209
theorem B2488151 : Blo 1657528 2488151 := bstep (se 1 (by rfl) ⟨1866113, by rfl⟩ : syracuseStep 2488151 = 3732227) B3732227
theorem B2127755 : Blo 1657528 2127755 := bstep (se 1 (by rfl) ⟨1595816, by rfl⟩ : syracuseStep 2127755 = 3191633) B3191633
theorem B1865623 : Blo 1657528 1865623 := bstep (se 1 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 1865623 = 2798435) B2798435
theorem B2488217 : Blo 1657528 2488217 := bstep (se 2 (by rfl) ⟨933081, by rfl⟩ : syracuseStep 2488217 = 1866163) B1866163
theorem B3733451 : Blo 1657528 3733451 := bstep (se 1 (by rfl) ⟨2800088, by rfl⟩ : syracuseStep 3733451 = 5600177) B5600177
theorem B3733505 : Blo 1657528 3733505 := bstep (se 2 (by rfl) ⟨1400064, by rfl⟩ : syracuseStep 3733505 = 2800129) B2800129
theorem B6723587 : Blo 1657528 6723587 := bstep (se 1 (by rfl) ⟨5042690, by rfl⟩ : syracuseStep 6723587 = 10085381) B10085381
theorem B2488331 : Blo 1657528 2488331 := bstep (se 1 (by rfl) ⟨1866248, by rfl⟩ : syracuseStep 2488331 = 3732497) B3732497
theorem B2488343 : Blo 1657528 2488343 := bstep (se 1 (by rfl) ⟨1866257, by rfl⟩ : syracuseStep 2488343 = 3732515) B3732515
theorem B1865803 : Blo 1657528 1865803 := bstep (se 1 (by rfl) ⟨1399352, by rfl⟩ : syracuseStep 1865803 = 2798705) B2798705
theorem B2488409 : Blo 1657528 2488409 := bstep (se 2 (by rfl) ⟨933153, by rfl⟩ : syracuseStep 2488409 = 1866307) B1866307
theorem B4200599 : Blo 1657528 4200599 := bstep (se 1 (by rfl) ⟨3150449, by rfl⟩ : syracuseStep 4200599 = 6300899) B6300899
theorem B1865911 : Blo 1657528 1865911 := bstep (se 1 (by rfl) ⟨1399433, by rfl⟩ : syracuseStep 1865911 = 2798867) B2798867
theorem B2488523 : Blo 1657528 2488523 := bstep (se 1 (by rfl) ⟨1866392, by rfl⟩ : syracuseStep 2488523 = 3732785) B3732785
theorem B2488535 : Blo 1657528 2488535 := bstep (se 1 (by rfl) ⟨1866401, by rfl⟩ : syracuseStep 2488535 = 3732803) B3732803
theorem B7567577 : Blo 1657528 7567577 := bstep (se 2 (by rfl) ⟨2837841, by rfl⟩ : syracuseStep 7567577 = 5675683) B5675683
theorem B3733721 : Blo 1657528 3733721 := bstep (se 2 (by rfl) ⟨1400145, by rfl⟩ : syracuseStep 3733721 = 2800291) B2800291
theorem B7182557 : Blo 1657528 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B2488601 : Blo 1657528 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B3733811 : Blo 1657528 3733811 := bstep (se 1 (by rfl) ⟨2800358, by rfl⟩ : syracuseStep 3733811 = 5600717) B5600717
theorem B2799947 : Blo 1657528 2799947 := bstep (se 1 (by rfl) ⟨2099960, by rfl⟩ : syracuseStep 2799947 = 4199921) B4199921
theorem B3733847 : Blo 1657528 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B12597605 : Blo 1657528 12597605 := bstep (se 4 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 12597605 = 2362051) B2362051
theorem B1866091 : Blo 1657528 1866091 := bstep (se 1 (by rfl) ⟨1399568, by rfl⟩ : syracuseStep 1866091 = 2799137) B2799137
theorem B2488715 : Blo 1657528 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B2488727 : Blo 1657528 2488727 := bstep (se 1 (by rfl) ⟨1866545, by rfl⟩ : syracuseStep 2488727 = 3733091) B3733091
theorem B17938867 : Blo 1657528 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B2800075 : Blo 1657528 2800075 := bstep (se 1 (by rfl) ⟨2100056, by rfl⟩ : syracuseStep 2800075 = 4200113) B4200113
theorem B1866199 : Blo 1657528 1866199 := bstep (se 1 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 1866199 = 2799299) B2799299
theorem B2488793 : Blo 1657528 2488793 := bstep (se 2 (by rfl) ⟨933297, by rfl⟩ : syracuseStep 2488793 = 1866595) B1866595
theorem B34060817 : Blo 1657528 34060817 := bstep (se 2 (by rfl) ⟨12772806, by rfl⟩ : syracuseStep 34060817 = 25545613) B25545613
theorem B1890859 : Blo 1657528 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B18881099 : Blo 1657528 18881099 := bstep (se 1 (by rfl) ⟨14160824, by rfl⟩ : syracuseStep 18881099 = 28321649) B28321649
theorem B6724171 : Blo 1657528 6724171 := bstep (se 1 (by rfl) ⟨5043128, by rfl⟩ : syracuseStep 6724171 = 10086257) B10086257
theorem B2488907 : Blo 1657528 2488907 := bstep (se 1 (by rfl) ⟨1866680, by rfl⟩ : syracuseStep 2488907 = 3733361) B3733361
theorem B2488919 : Blo 1657528 2488919 := bstep (se 1 (by rfl) ⟨1866689, by rfl⟩ : syracuseStep 2488919 = 3733379) B3733379
theorem B2800217 : Blo 1657528 2800217 := bstep (se 2 (by rfl) ⟨1050081, by rfl⟩ : syracuseStep 2800217 = 2100163) B2100163
theorem B17013341 : Blo 1657528 17013341 := bstep (se 3 (by rfl) ⟨3190001, by rfl⟩ : syracuseStep 17013341 = 6380003) B6380003
theorem B1866379 : Blo 1657528 1866379 := bstep (se 1 (by rfl) ⟨1399784, by rfl⟩ : syracuseStep 1866379 = 2799569) B2799569
theorem B2488985 : Blo 1657528 2488985 := bstep (se 2 (by rfl) ⟨933369, by rfl⟩ : syracuseStep 2488985 = 1866739) B1866739
theorem B10631897 : Blo 1657528 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B4725469 : Blo 1657528 4725469 := bstep (se 3 (by rfl) ⟨886025, by rfl⟩ : syracuseStep 4725469 = 1772051) B1772051
theorem B2800345 : Blo 1657528 2800345 := bstep (se 2 (by rfl) ⟨1050129, by rfl⟩ : syracuseStep 2800345 = 2100259) B2100259
theorem B1866487 : Blo 1657528 1866487 := bstep (se 1 (by rfl) ⟨1399865, by rfl⟩ : syracuseStep 1866487 = 2799731) B2799731
theorem B12589829 : Blo 1657528 12589829 := bstep (se 4 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 12589829 = 2360593) B2360593
theorem B2489099 : Blo 1657528 2489099 := bstep (se 1 (by rfl) ⟨1866824, by rfl⟩ : syracuseStep 2489099 = 3733649) B3733649
theorem B2489111 : Blo 1657528 2489111 := bstep (se 1 (by rfl) ⟨1866833, by rfl⟩ : syracuseStep 2489111 = 3733667) B3733667
theorem B12598091 : Blo 1657528 12598091 := bstep (se 1 (by rfl) ⟨9448568, by rfl⟩ : syracuseStep 12598091 = 18897137) B18897137
theorem B2489177 : Blo 1657528 2489177 := bstep (se 2 (by rfl) ⟨933441, by rfl⟩ : syracuseStep 2489177 = 1866883) B1866883
theorem B31882085 : Blo 1657528 31882085 := bstep (se 4 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 31882085 = 5977891) B5977891
theorem B23919461 : Blo 1657528 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B6814595 : Blo 1657528 6814595 := bstep (se 1 (by rfl) ⟨5110946, by rfl⟩ : syracuseStep 6814595 = 10221893) B10221893
theorem B6298499 : Blo 1657528 6298499 := bstep (se 1 (by rfl) ⟨4723874, by rfl⟩ : syracuseStep 6298499 = 9447749) B9447749
theorem B1866667 : Blo 1657528 1866667 := bstep (se 1 (by rfl) ⟨1400000, by rfl⟩ : syracuseStep 1866667 = 2800001) B2800001
theorem B3783617 : Blo 1657528 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B4725697 : Blo 1657528 4725697 := bstep (se 2 (by rfl) ⟨1772136, by rfl⟩ : syracuseStep 4725697 = 3544273) B3544273
theorem B2489291 : Blo 1657528 2489291 := bstep (se 1 (by rfl) ⟨1866968, by rfl⟩ : syracuseStep 2489291 = 3733937) B3733937
theorem B1866775 : Blo 1657528 1866775 := bstep (se 1 (by rfl) ⟨1400081, by rfl⟩ : syracuseStep 1866775 = 2800163) B2800163
theorem B5594291 : Blo 1657528 5594291 := bstep (se 1 (by rfl) ⟨4195718, by rfl⟩ : syracuseStep 5594291 = 8391437) B8391437
theorem B1866955 : Blo 1657528 1866955 := bstep (se 1 (by rfl) ⟨1400216, by rfl⟩ : syracuseStep 1866955 = 2800433) B2800433
theorem B6298955 : Blo 1657528 6298955 := bstep (se 1 (by rfl) ⟨4724216, by rfl⟩ : syracuseStep 6298955 = 9448433) B9448433
theorem B1916311 : Blo 1657528 1916311 := bstep (se 1 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 1916311 = 2874467) B2874467
theorem B21265841 : Blo 1657528 21265841 := bstep (se 2 (by rfl) ⟨7974690, by rfl⟩ : syracuseStep 21265841 = 15949381) B15949381
theorem B5594561 : Blo 1657528 5594561 := bstep (se 2 (by rfl) ⟨2097960, by rfl⟩ : syracuseStep 5594561 = 4195921) B4195921
theorem B6299153 : Blo 1657528 6299153 := bstep (se 2 (by rfl) ⟨2362182, by rfl⟩ : syracuseStep 6299153 = 4724365) B4724365
theorem B3833419 : Blo 1657528 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B5979737 : Blo 1657528 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B43106147 : Blo 1657528 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B47800165 : Blo 1657528 47800165 := bstep (se 4 (by rfl) ⟨4481265, by rfl⟩ : syracuseStep 47800165 = 8962531) B8962531
theorem B7086017 : Blo 1657528 7086017 := bstep (se 2 (by rfl) ⟨2657256, by rfl⟩ : syracuseStep 7086017 = 5314513) B5314513
theorem B5595101 : Blo 1657528 5595101 := bstep (se 3 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 5595101 = 2098163) B2098163
theorem B6725699 : Blo 1657528 6725699 := bstep (se 1 (by rfl) ⟨5044274, by rfl⟩ : syracuseStep 6725699 = 10088549) B10088549
theorem B5677175 : Blo 1657528 5677175 := bstep (se 1 (by rfl) ⟨4257881, by rfl⟩ : syracuseStep 5677175 = 8515763) B8515763
theorem B4849949 : Blo 1657528 4849949 := bstep (se 3 (by rfl) ⟨909365, by rfl⟩ : syracuseStep 4849949 = 1818731) B1818731
theorem B5595425 : Blo 1657528 5595425 := bstep (se 2 (by rfl) ⟨2098284, by rfl⟩ : syracuseStep 5595425 = 4196569) B4196569
theorem B8397107 : Blo 1657528 8397107 := bstep (se 1 (by rfl) ⟨6297830, by rfl⟩ : syracuseStep 8397107 = 12595661) B12595661
theorem B9445835 : Blo 1657528 9445835 := bstep (se 1 (by rfl) ⟨7084376, by rfl⟩ : syracuseStep 9445835 = 14168753) B14168753
theorem B49136149 : Blo 1657528 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B34030199 : Blo 1657528 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B8397431 : Blo 1657528 8397431 := bstep (se 1 (by rfl) ⟨6298073, by rfl⟩ : syracuseStep 8397431 = 12596147) B12596147
theorem B5596019 : Blo 1657528 5596019 := bstep (se 1 (by rfl) ⟨4197014, by rfl⟩ : syracuseStep 5596019 = 8394029) B8394029
theorem B2360183 : Blo 1657528 2360183 := bstep (se 1 (by rfl) ⟨1770137, by rfl⟩ : syracuseStep 2360183 = 3540275) B3540275
theorem B9446291 : Blo 1657528 9446291 := bstep (se 1 (by rfl) ⟨7084718, by rfl⟩ : syracuseStep 9446291 = 14169437) B14169437
theorem B52437941 : Blo 1657528 52437941 := bstep (se 5 (by rfl) ⟨2458028, by rfl⟩ : syracuseStep 52437941 = 4916057) B4916057
theorem B6300625 : Blo 1657528 6300625 := bstep (se 2 (by rfl) ⟨2362734, by rfl⟩ : syracuseStep 6300625 = 4725469) B4725469
theorem B2098219 : Blo 1657528 2098219 := bstep (se 1 (by rfl) ⟨1573664, by rfl⟩ : syracuseStep 2098219 = 3147329) B3147329
theorem B2360377 : Blo 1657528 2360377 := bstep (se 2 (by rfl) ⟨885141, by rfl⟩ : syracuseStep 2360377 = 1770283) B1770283
theorem B12600521 : Blo 1657528 12600521 := bstep (se 2 (by rfl) ⟨4725195, by rfl⟩ : syracuseStep 12600521 = 9450391) B9450391
theorem B6300929 : Blo 1657528 6300929 := bstep (se 2 (by rfl) ⟨2362848, by rfl⟩ : syracuseStep 6300929 = 4725697) B4725697
theorem B4482391 : Blo 1657528 4482391 := bstep (se 1 (by rfl) ⟨3361793, by rfl⟩ : syracuseStep 4482391 = 6723587) B6723587
theorem B3540343 : Blo 1657528 3540343 := bstep (se 1 (by rfl) ⟨2655257, by rfl⟩ : syracuseStep 3540343 = 5310515) B5310515
theorem B4720139 : Blo 1657528 4720139 := bstep (se 1 (by rfl) ⟨3540104, by rfl⟩ : syracuseStep 4720139 = 7080209) B7080209
theorem B3982907 : Blo 1657528 3982907 := bstep (se 1 (by rfl) ⟨2987180, by rfl⟩ : syracuseStep 3982907 = 5974361) B5974361
theorem B8398403 : Blo 1657528 8398403 := bstep (se 1 (by rfl) ⟨6298802, by rfl⟩ : syracuseStep 8398403 = 12597605) B12597605
theorem B7087931 : Blo 1657528 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B73664369 : Blo 1657528 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B3147655 : Blo 1657528 3147655 := bstep (se 1 (by rfl) ⟨2360741, by rfl⟩ : syracuseStep 3147655 = 4721483) B4721483
theorem B8398727 : Blo 1657528 8398727 := bstep (se 1 (by rfl) ⟨6299045, by rfl⟩ : syracuseStep 8398727 = 12598091) B12598091
theorem B2099191 : Blo 1657528 2099191 := bstep (se 1 (by rfl) ⟨1574393, by rfl⟩ : syracuseStep 2099191 = 3148787) B3148787
theorem B4483073 : Blo 1657528 4483073 := bstep (se 2 (by rfl) ⟨1681152, by rfl⟩ : syracuseStep 4483073 = 3362305) B3362305
theorem B42502157 : Blo 1657528 42502157 := bstep (se 3 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 42502157 = 15938309) B15938309
theorem B13453399 : Blo 1657528 13453399 := bstep (se 1 (by rfl) ⟨10090049, by rfl⟩ : syracuseStep 13453399 = 20180099) B20180099
theorem B3729527 : Blo 1657528 3729527 := bstep (se 1 (by rfl) ⟨2797145, by rfl⟩ : syracuseStep 3729527 = 5594291) B5594291
theorem B4786295 : Blo 1657528 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B3983617 : Blo 1657528 3983617 := bstep (se 2 (by rfl) ⟨1493856, by rfl⟩ : syracuseStep 3983617 = 2987713) B2987713
theorem B3729707 : Blo 1657528 3729707 := bstep (se 1 (by rfl) ⟨2797280, by rfl⟩ : syracuseStep 3729707 = 5594561) B5594561
theorem B2099515 : Blo 1657528 2099515 := bstep (se 1 (by rfl) ⟨1574636, by rfl⟩ : syracuseStep 2099515 = 3149273) B3149273
theorem B18172253 : Blo 1657528 18172253 := bstep (se 3 (by rfl) ⟨3407297, by rfl⟩ : syracuseStep 18172253 = 6814595) B6814595
theorem B3148217 : Blo 1657528 3148217 := bstep (se 2 (by rfl) ⟨1180581, by rfl⟩ : syracuseStep 3148217 = 2361163) B2361163
theorem B1772047 : Blo 1657528 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B17926757 : Blo 1657528 17926757 := bstep (se 4 (by rfl) ⟨1680633, by rfl⟩ : syracuseStep 17926757 = 3361267) B3361267
theorem B4721267 : Blo 1657528 4721267 := bstep (se 1 (by rfl) ⟨3540950, by rfl⟩ : syracuseStep 4721267 = 7081901) B7081901
theorem B3730067 : Blo 1657528 3730067 := bstep (se 1 (by rfl) ⟨2797550, by rfl⟩ : syracuseStep 3730067 = 5595101) B5595101
theorem B1657531 : Blo 1657528 1657531 := bstep (se 1 (by rfl) ⟨1243148, by rfl⟩ : syracuseStep 1657531 = 2486297) B2486297
theorem B3730121 : Blo 1657528 3730121 := bstep (se 2 (by rfl) ⟨1398795, by rfl⟩ : syracuseStep 3730121 = 2797591) B2797591
theorem B1657607 : Blo 1657528 1657607 := bstep (se 1 (by rfl) ⟨1243205, by rfl⟩ : syracuseStep 1657607 = 2486411) B2486411
theorem B1657615 : Blo 1657528 1657615 := bstep (se 1 (by rfl) ⟨1243211, by rfl⟩ : syracuseStep 1657615 = 2486423) B2486423
theorem B1657659 : Blo 1657528 1657659 := bstep (se 1 (by rfl) ⟨1243244, by rfl⟩ : syracuseStep 1657659 = 2486489) B2486489
theorem B1657735 : Blo 1657528 1657735 := bstep (se 1 (by rfl) ⟨1243301, by rfl⟩ : syracuseStep 1657735 = 2486603) B2486603
theorem B1657743 : Blo 1657528 1657743 := bstep (se 1 (by rfl) ⟨1243307, by rfl⟩ : syracuseStep 1657743 = 2486615) B2486615
theorem B3541907 : Blo 1657528 3541907 := bstep (se 1 (by rfl) ⟨2656430, by rfl⟩ : syracuseStep 3541907 = 5312861) B5312861
theorem B9440185 : Blo 1657528 9440185 := bstep (se 2 (by rfl) ⟨3540069, by rfl⟩ : syracuseStep 9440185 = 7080139) B7080139
theorem B1657787 : Blo 1657528 1657787 := bstep (se 1 (by rfl) ⟨1243340, by rfl⟩ : syracuseStep 1657787 = 2486681) B2486681
theorem B4721665 : Blo 1657528 4721665 := bstep (se 2 (by rfl) ⟨1770624, by rfl⟩ : syracuseStep 4721665 = 3541249) B3541249
theorem B1657863 : Blo 1657528 1657863 := bstep (se 1 (by rfl) ⟨1243397, by rfl⟩ : syracuseStep 1657863 = 2486795) B2486795
theorem B1657871 : Blo 1657528 1657871 := bstep (se 1 (by rfl) ⟨1243403, by rfl⟩ : syracuseStep 1657871 = 2486807) B2486807
theorem B1657915 : Blo 1657528 1657915 := bstep (se 1 (by rfl) ⟨1243436, by rfl⟩ : syracuseStep 1657915 = 2486873) B2486873
theorem B4721723 : Blo 1657528 4721723 := bstep (se 1 (by rfl) ⟨3541292, by rfl⟩ : syracuseStep 4721723 = 7082585) B7082585
theorem B4197491 : Blo 1657528 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B1657991 : Blo 1657528 1657991 := bstep (se 1 (by rfl) ⟨1243493, by rfl⟩ : syracuseStep 1657991 = 2486987) B2486987
theorem B4484231 : Blo 1657528 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B1657999 : Blo 1657528 1657999 := bstep (se 1 (by rfl) ⟨1243499, by rfl⟩ : syracuseStep 1657999 = 2486999) B2486999
theorem B1658043 : Blo 1657528 1658043 := bstep (se 1 (by rfl) ⟨1243532, by rfl⟩ : syracuseStep 1658043 = 2487065) B2487065
theorem B5311745 : Blo 1657528 5311745 := bstep (se 2 (by rfl) ⟨1991904, by rfl⟩ : syracuseStep 5311745 = 3983809) B3983809
theorem B1658119 : Blo 1657528 1658119 := bstep (se 1 (by rfl) ⟨1243589, by rfl⟩ : syracuseStep 1658119 = 2487179) B2487179
theorem B1658127 : Blo 1657528 1658127 := bstep (se 1 (by rfl) ⟨1243595, by rfl⟩ : syracuseStep 1658127 = 2487191) B2487191
theorem B3984655 : Blo 1657528 3984655 := bstep (se 1 (by rfl) ⟨2988491, by rfl⟩ : syracuseStep 3984655 = 5976983) B5976983
theorem B13634849 : Blo 1657528 13634849 := bstep (se 2 (by rfl) ⟨5113068, by rfl⟩ : syracuseStep 13634849 = 10226137) B10226137
theorem B1658171 : Blo 1657528 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B51064123 : Blo 1657528 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B5041523 : Blo 1657528 5041523 := bstep (se 1 (by rfl) ⟨3781142, by rfl⟩ : syracuseStep 5041523 = 7562285) B7562285
theorem B3730823 : Blo 1657528 3730823 := bstep (se 1 (by rfl) ⟨2798117, by rfl⟩ : syracuseStep 3730823 = 5596235) B5596235
theorem B1658247 : Blo 1657528 1658247 := bstep (se 1 (by rfl) ⟨1243685, by rfl⟩ : syracuseStep 1658247 = 2487371) B2487371
theorem B1658255 : Blo 1657528 1658255 := bstep (se 1 (by rfl) ⟨1243691, by rfl⟩ : syracuseStep 1658255 = 2487383) B2487383
theorem B5598611 : Blo 1657528 5598611 := bstep (se 1 (by rfl) ⟨4198958, by rfl⟩ : syracuseStep 5598611 = 8397917) B8397917
theorem B8965561 : Blo 1657528 8965561 := bstep (se 2 (by rfl) ⟨3362085, by rfl⟩ : syracuseStep 8965561 = 6724171) B6724171
theorem B1658299 : Blo 1657528 1658299 := bstep (se 1 (by rfl) ⟨1243724, by rfl⟩ : syracuseStep 1658299 = 2487449) B2487449
theorem B1658375 : Blo 1657528 1658375 := bstep (se 1 (by rfl) ⟨1243781, by rfl⟩ : syracuseStep 1658375 = 2487563) B2487563
theorem B1658383 : Blo 1657528 1658383 := bstep (se 1 (by rfl) ⟨1243787, by rfl⟩ : syracuseStep 1658383 = 2487575) B2487575
theorem B4484641 : Blo 1657528 4484641 := bstep (se 2 (by rfl) ⟨1681740, by rfl⟩ : syracuseStep 4484641 = 3363481) B3363481
theorem B3731003 : Blo 1657528 3731003 := bstep (se 1 (by rfl) ⟨2798252, by rfl⟩ : syracuseStep 3731003 = 5596505) B5596505
theorem B1658427 : Blo 1657528 1658427 := bstep (se 1 (by rfl) ⟨1243820, by rfl⟩ : syracuseStep 1658427 = 2487641) B2487641
theorem B3149371 : Blo 1657528 3149371 := bstep (se 1 (by rfl) ⟨2362028, by rfl⟩ : syracuseStep 3149371 = 4724057) B4724057
theorem B3984983 : Blo 1657528 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B4198007 : Blo 1657528 4198007 := bstep (se 1 (by rfl) ⟨3148505, by rfl⟩ : syracuseStep 4198007 = 6297011) B6297011
theorem B1658503 : Blo 1657528 1658503 := bstep (se 1 (by rfl) ⟨1243877, by rfl⟩ : syracuseStep 1658503 = 2487755) B2487755
theorem B1658511 : Blo 1657528 1658511 := bstep (se 1 (by rfl) ⟨1243883, by rfl⟩ : syracuseStep 1658511 = 2487767) B2487767
theorem B3731129 : Blo 1657528 3731129 := bstep (se 2 (by rfl) ⟨1399173, by rfl⟩ : syracuseStep 3731129 = 2798347) B2798347
theorem B1658555 : Blo 1657528 1658555 := bstep (se 1 (by rfl) ⟨1243916, by rfl⟩ : syracuseStep 1658555 = 2487833) B2487833
theorem B60501761 : Blo 1657528 60501761 := bstep (se 2 (by rfl) ⟨22688160, by rfl⟩ : syracuseStep 60501761 = 45376321) B45376321
theorem B1658631 : Blo 1657528 1658631 := bstep (se 1 (by rfl) ⟨1243973, by rfl⟩ : syracuseStep 1658631 = 2487947) B2487947
theorem B1658639 : Blo 1657528 1658639 := bstep (se 1 (by rfl) ⟨1243979, by rfl⟩ : syracuseStep 1658639 = 2487959) B2487959
theorem B2797355 : Blo 1657528 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B1658683 : Blo 1657528 1658683 := bstep (se 1 (by rfl) ⟨1244012, by rfl⟩ : syracuseStep 1658683 = 2488025) B2488025
theorem B3985271 : Blo 1657528 3985271 := bstep (se 1 (by rfl) ⟨2988953, by rfl⟩ : syracuseStep 3985271 = 5977907) B5977907
theorem B1658759 : Blo 1657528 1658759 := bstep (se 1 (by rfl) ⟨1244069, by rfl⟩ : syracuseStep 1658759 = 2488139) B2488139
theorem B1658767 : Blo 1657528 1658767 := bstep (se 1 (by rfl) ⟨1244075, by rfl⟩ : syracuseStep 1658767 = 2488151) B2488151
theorem B1658811 : Blo 1657528 1658811 := bstep (se 1 (by rfl) ⟨1244108, by rfl⟩ : syracuseStep 1658811 = 2488217) B2488217
theorem B1658887 : Blo 1657528 1658887 := bstep (se 1 (by rfl) ⟨1244165, by rfl⟩ : syracuseStep 1658887 = 2488331) B2488331
theorem B3731471 : Blo 1657528 3731471 := bstep (se 1 (by rfl) ⟨2798603, by rfl⟩ : syracuseStep 3731471 = 5597207) B5597207
theorem B1658895 : Blo 1657528 1658895 := bstep (se 1 (by rfl) ⟨1244171, by rfl⟩ : syracuseStep 1658895 = 2488343) B2488343
theorem B11956247 : Blo 1657528 11956247 := bstep (se 1 (by rfl) ⟨8967185, by rfl⟩ : syracuseStep 11956247 = 17934371) B17934371
theorem B8392733 : Blo 1657528 8392733 := bstep (se 3 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 8392733 = 3147275) B3147275
theorem B3731489 : Blo 1657528 3731489 := bstep (se 2 (by rfl) ⟨1399308, by rfl⟩ : syracuseStep 3731489 = 2798617) B2798617
theorem B3149857 : Blo 1657528 3149857 := bstep (se 2 (by rfl) ⟨1181196, by rfl⟩ : syracuseStep 3149857 = 2362393) B2362393
theorem B2486315 : Blo 1657528 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B1658939 : Blo 1657528 1658939 := bstep (se 1 (by rfl) ⟨1244204, by rfl⟩ : syracuseStep 1658939 = 2488409) B2488409
theorem B2486345 : Blo 1657528 2486345 := bstep (se 2 (by rfl) ⟨932379, by rfl⟩ : syracuseStep 2486345 = 1864759) B1864759
theorem B35852381 : Blo 1657528 35852381 := bstep (se 3 (by rfl) ⟨6722321, by rfl⟩ : syracuseStep 35852381 = 13444643) B13444643
theorem B1659015 : Blo 1657528 1659015 := bstep (se 1 (by rfl) ⟨1244261, by rfl⟩ : syracuseStep 1659015 = 2488523) B2488523
theorem B1659023 : Blo 1657528 1659023 := bstep (se 1 (by rfl) ⟨1244267, by rfl⟩ : syracuseStep 1659023 = 2488535) B2488535
theorem B4788371 : Blo 1657528 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B2797753 : Blo 1657528 2797753 := bstep (se 2 (by rfl) ⟨1049157, by rfl⟩ : syracuseStep 2797753 = 2098315) B2098315
theorem B2486459 : Blo 1657528 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B1659067 : Blo 1657528 1659067 := bstep (se 1 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 1659067 = 2488601) B2488601
theorem B2486519 : Blo 1657528 2486519 := bstep (se 1 (by rfl) ⟨1864889, by rfl⟩ : syracuseStep 2486519 = 3729779) B3729779
theorem B1659143 : Blo 1657528 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B2486543 : Blo 1657528 2486543 := bstep (se 1 (by rfl) ⟨1864907, by rfl⟩ : syracuseStep 2486543 = 3729815) B3729815
theorem B1659151 : Blo 1657528 1659151 := bstep (se 1 (by rfl) ⟨1244363, by rfl⟩ : syracuseStep 1659151 = 2488727) B2488727
theorem B2486585 : Blo 1657528 2486585 := bstep (se 2 (by rfl) ⟨932469, by rfl⟩ : syracuseStep 2486585 = 1864939) B1864939
theorem B1659195 : Blo 1657528 1659195 := bstep (se 1 (by rfl) ⟨1244396, by rfl⟩ : syracuseStep 1659195 = 2488793) B2488793
theorem B3731831 : Blo 1657528 3731831 := bstep (se 1 (by rfl) ⟨2798873, by rfl⟩ : syracuseStep 3731831 = 5597747) B5597747
theorem B12587399 : Blo 1657528 12587399 := bstep (se 1 (by rfl) ⟨9440549, by rfl⟩ : syracuseStep 12587399 = 18881099) B18881099
theorem B2486663 : Blo 1657528 2486663 := bstep (se 1 (by rfl) ⟨1864997, by rfl⟩ : syracuseStep 2486663 = 3729995) B3729995
theorem B1659271 : Blo 1657528 1659271 := bstep (se 1 (by rfl) ⟨1244453, by rfl⟩ : syracuseStep 1659271 = 2488907) B2488907
theorem B1659279 : Blo 1657528 1659279 := bstep (se 1 (by rfl) ⟨1244459, by rfl⟩ : syracuseStep 1659279 = 2488919) B2488919
theorem B11342227 : Blo 1657528 11342227 := bstep (se 1 (by rfl) ⟨8506670, by rfl⟩ : syracuseStep 11342227 = 17013341) B17013341
theorem B2486699 : Blo 1657528 2486699 := bstep (se 1 (by rfl) ⟨1865024, by rfl⟩ : syracuseStep 2486699 = 3730049) B3730049
theorem B1659323 : Blo 1657528 1659323 := bstep (se 1 (by rfl) ⟨1244492, by rfl⟩ : syracuseStep 1659323 = 2488985) B2488985
theorem B2486729 : Blo 1657528 2486729 := bstep (se 2 (by rfl) ⟨932523, by rfl⟩ : syracuseStep 2486729 = 1865047) B1865047
theorem B8393219 : Blo 1657528 8393219 := bstep (se 1 (by rfl) ⟨6294914, by rfl⟩ : syracuseStep 8393219 = 12589829) B12589829
theorem B1659399 : Blo 1657528 1659399 := bstep (se 1 (by rfl) ⟨1244549, by rfl⟩ : syracuseStep 1659399 = 2489099) B2489099
theorem B1659407 : Blo 1657528 1659407 := bstep (se 1 (by rfl) ⟨1244555, by rfl⟩ : syracuseStep 1659407 = 2489111) B2489111
theorem B3732011 : Blo 1657528 3732011 := bstep (se 1 (by rfl) ⟨2799008, by rfl⟩ : syracuseStep 3732011 = 5598017) B5598017
theorem B2486843 : Blo 1657528 2486843 := bstep (se 1 (by rfl) ⟨1865132, by rfl⟩ : syracuseStep 2486843 = 3730265) B3730265
theorem B1659451 : Blo 1657528 1659451 := bstep (se 1 (by rfl) ⟨1244588, by rfl⟩ : syracuseStep 1659451 = 2489177) B2489177
theorem B21254723 : Blo 1657528 21254723 := bstep (se 1 (by rfl) ⟨15941042, by rfl⟩ : syracuseStep 21254723 = 31882085) B31882085
theorem B15946307 : Blo 1657528 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B4198999 : Blo 1657528 4198999 := bstep (se 1 (by rfl) ⟨3149249, by rfl⟩ : syracuseStep 4198999 = 6298499) B6298499
theorem B2486903 : Blo 1657528 2486903 := bstep (se 1 (by rfl) ⟨1865177, by rfl⟩ : syracuseStep 2486903 = 3730355) B3730355
theorem B1659527 : Blo 1657528 1659527 := bstep (se 1 (by rfl) ⟨1244645, by rfl⟩ : syracuseStep 1659527 = 2489291) B2489291
theorem B2486927 : Blo 1657528 2486927 := bstep (se 1 (by rfl) ⟨1865195, by rfl⟩ : syracuseStep 2486927 = 3730391) B3730391
theorem B2486969 : Blo 1657528 2486969 := bstep (se 2 (by rfl) ⟨932613, by rfl⟩ : syracuseStep 2486969 = 1865227) B1865227
theorem B2487047 : Blo 1657528 2487047 := bstep (se 1 (by rfl) ⟨1865285, by rfl⟩ : syracuseStep 2487047 = 3730571) B3730571
theorem B5600015 : Blo 1657528 5600015 := bstep (se 1 (by rfl) ⟨4200011, by rfl⟩ : syracuseStep 5600015 = 8400023) B8400023
theorem B6386465 : Blo 1657528 6386465 := bstep (se 2 (by rfl) ⟨2394924, by rfl⟩ : syracuseStep 6386465 = 4789849) B4789849
theorem B2487083 : Blo 1657528 2487083 := bstep (se 1 (by rfl) ⟨1865312, by rfl⟩ : syracuseStep 2487083 = 3730625) B3730625
theorem B14160689 : Blo 1657528 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B2487113 : Blo 1657528 2487113 := bstep (se 2 (by rfl) ⟨932667, by rfl⟩ : syracuseStep 2487113 = 1865335) B1865335
theorem B2798455 : Blo 1657528 2798455 := bstep (se 1 (by rfl) ⟨2098841, by rfl⟩ : syracuseStep 2798455 = 4197683) B4197683
theorem B4199303 : Blo 1657528 4199303 := bstep (se 1 (by rfl) ⟨3149477, by rfl⟩ : syracuseStep 4199303 = 6298955) B6298955
theorem B3732371 : Blo 1657528 3732371 := bstep (se 1 (by rfl) ⟨2799278, by rfl⟩ : syracuseStep 3732371 = 5598557) B5598557
theorem B10621849 : Blo 1657528 10621849 := bstep (se 2 (by rfl) ⟨3983193, by rfl⟩ : syracuseStep 10621849 = 7966387) B7966387
theorem B2487227 : Blo 1657528 2487227 := bstep (se 1 (by rfl) ⟨1865420, by rfl⟩ : syracuseStep 2487227 = 3730841) B3730841
theorem B3732425 : Blo 1657528 3732425 := bstep (se 2 (by rfl) ⟨1399659, by rfl⟩ : syracuseStep 3732425 = 2799319) B2799319
theorem B14177227 : Blo 1657528 14177227 := bstep (se 1 (by rfl) ⟨10632920, by rfl⟩ : syracuseStep 14177227 = 21265841) B21265841
theorem B2487287 : Blo 1657528 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B4199435 : Blo 1657528 4199435 := bstep (se 1 (by rfl) ⟨3149576, by rfl⟩ : syracuseStep 4199435 = 6299153) B6299153
theorem B2487311 : Blo 1657528 2487311 := bstep (se 1 (by rfl) ⟨1865483, by rfl⟩ : syracuseStep 2487311 = 3730967) B3730967
theorem B5674013 : Blo 1657528 5674013 := bstep (se 3 (by rfl) ⟨1063877, by rfl⟩ : syracuseStep 5674013 = 2127755) B2127755
theorem B5600285 : Blo 1657528 5600285 := bstep (se 3 (by rfl) ⟨1050053, by rfl⟩ : syracuseStep 5600285 = 2100107) B2100107
theorem B2487353 : Blo 1657528 2487353 := bstep (se 2 (by rfl) ⟨932757, by rfl⟩ : syracuseStep 2487353 = 1865515) B1865515
theorem B2798651 : Blo 1657528 2798651 := bstep (se 1 (by rfl) ⟨2098988, by rfl⟩ : syracuseStep 2798651 = 4197977) B4197977
theorem B3986491 : Blo 1657528 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B2487431 : Blo 1657528 2487431 := bstep (se 1 (by rfl) ⟨1865573, by rfl⟩ : syracuseStep 2487431 = 3731147) B3731147
theorem B2487467 : Blo 1657528 2487467 := bstep (se 1 (by rfl) ⟨1865600, by rfl⟩ : syracuseStep 2487467 = 3731201) B3731201
theorem B2487497 : Blo 1657528 2487497 := bstep (se 2 (by rfl) ⟨932811, by rfl⟩ : syracuseStep 2487497 = 1865623) B1865623
theorem B1864975 : Blo 1657528 1864975 := bstep (se 1 (by rfl) ⟨1398731, by rfl⟩ : syracuseStep 1864975 = 2797463) B2797463
theorem B4724011 : Blo 1657528 4724011 := bstep (se 1 (by rfl) ⟨3543008, by rfl⟩ : syracuseStep 4724011 = 7086017) B7086017
theorem B2487611 : Blo 1657528 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B2487671 : Blo 1657528 2487671 := bstep (se 1 (by rfl) ⟨1865753, by rfl⟩ : syracuseStep 2487671 = 3731507) B3731507
theorem B2487695 : Blo 1657528 2487695 := bstep (se 1 (by rfl) ⟨1865771, by rfl⟩ : syracuseStep 2487695 = 3731543) B3731543
theorem B2487737 : Blo 1657528 2487737 := bstep (se 2 (by rfl) ⟨932901, by rfl⟩ : syracuseStep 2487737 = 1865803) B1865803
theorem B2799049 : Blo 1657528 2799049 := bstep (se 2 (by rfl) ⟨1049643, by rfl⟩ : syracuseStep 2799049 = 2099287) B2099287
theorem B6297041 : Blo 1657528 6297041 := bstep (se 2 (by rfl) ⟨2361390, by rfl⟩ : syracuseStep 6297041 = 4722781) B4722781
theorem B2487815 : Blo 1657528 2487815 := bstep (se 1 (by rfl) ⟨1865861, by rfl⟩ : syracuseStep 2487815 = 3731723) B3731723
theorem B4724239 : Blo 1657528 4724239 := bstep (se 1 (by rfl) ⟨3543179, by rfl⟩ : syracuseStep 4724239 = 7086359) B7086359
theorem B4199951 : Blo 1657528 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B37344797 : Blo 1657528 37344797 := bstep (se 3 (by rfl) ⟨7002149, by rfl⟩ : syracuseStep 37344797 = 14004299) B14004299
theorem B14358059 : Blo 1657528 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2487851 : Blo 1657528 2487851 := bstep (se 1 (by rfl) ⟨1865888, by rfl⟩ : syracuseStep 2487851 = 3731777) B3731777
theorem B2487881 : Blo 1657528 2487881 := bstep (se 2 (by rfl) ⟨932955, by rfl⟩ : syracuseStep 2487881 = 1865911) B1865911
theorem B3733127 : Blo 1657528 3733127 := bstep (se 1 (by rfl) ⟨2799845, by rfl⟩ : syracuseStep 3733127 = 5599691) B5599691
theorem B4200083 : Blo 1657528 4200083 := bstep (se 1 (by rfl) ⟨3150062, by rfl⟩ : syracuseStep 4200083 = 6300125) B6300125
theorem B17929907 : Blo 1657528 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B2487995 : Blo 1657528 2487995 := bstep (se 1 (by rfl) ⟨1865996, by rfl⟩ : syracuseStep 2487995 = 3731993) B3731993
theorem B2488055 : Blo 1657528 2488055 := bstep (se 1 (by rfl) ⟨1866041, by rfl⟩ : syracuseStep 2488055 = 3732083) B3732083
theorem B1865479 : Blo 1657528 1865479 := bstep (se 1 (by rfl) ⟨1399109, by rfl⟩ : syracuseStep 1865479 = 2798219) B2798219
theorem B16152335 : Blo 1657528 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B2488079 : Blo 1657528 2488079 := bstep (se 1 (by rfl) ⟨1866059, by rfl⟩ : syracuseStep 2488079 = 3732119) B3732119
theorem B4724513 : Blo 1657528 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B14161715 : Blo 1657528 14161715 := bstep (se 1 (by rfl) ⟨10621286, by rfl⟩ : syracuseStep 14161715 = 21242573) B21242573
theorem B102111029 : Blo 1657528 102111029 := bstep (se 5 (by rfl) ⟨4786454, by rfl⟩ : syracuseStep 102111029 = 9572909) B9572909
theorem B2488121 : Blo 1657528 2488121 := bstep (se 2 (by rfl) ⟨933045, by rfl⟩ : syracuseStep 2488121 = 1866091) B1866091
theorem B3733307 : Blo 1657528 3733307 := bstep (se 1 (by rfl) ⟨2799980, by rfl⟩ : syracuseStep 3733307 = 5599961) B5599961
theorem B5044103 : Blo 1657528 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B2488199 : Blo 1657528 2488199 := bstep (se 1 (by rfl) ⟨1866149, by rfl⟩ : syracuseStep 2488199 = 3732299) B3732299
theorem B6297497 : Blo 1657528 6297497 := bstep (se 2 (by rfl) ⟨2361561, by rfl⟩ : syracuseStep 6297497 = 4723123) B4723123
theorem B23918489 : Blo 1657528 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B2488235 : Blo 1657528 2488235 := bstep (se 1 (by rfl) ⟨1866176, by rfl⟩ : syracuseStep 2488235 = 3732353) B3732353
theorem B3733433 : Blo 1657528 3733433 := bstep (se 2 (by rfl) ⟨1400037, by rfl⟩ : syracuseStep 3733433 = 2800075) B2800075
theorem B1865659 : Blo 1657528 1865659 := bstep (se 1 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 1865659 = 2798489) B2798489
theorem B2488265 : Blo 1657528 2488265 := bstep (se 2 (by rfl) ⟨933099, by rfl⟩ : syracuseStep 2488265 = 1866199) B1866199
theorem B2521145 : Blo 1657528 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B2488379 : Blo 1657528 2488379 := bstep (se 1 (by rfl) ⟨1866284, by rfl⟩ : syracuseStep 2488379 = 3732569) B3732569
theorem B8394839 : Blo 1657528 8394839 := bstep (se 1 (by rfl) ⟨6296129, by rfl⟩ : syracuseStep 8394839 = 12592259) B12592259
theorem B2488439 : Blo 1657528 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B4724855 : Blo 1657528 4724855 := bstep (se 1 (by rfl) ⟨3543641, by rfl⟩ : syracuseStep 4724855 = 7087283) B7087283
theorem B2799751 : Blo 1657528 2799751 := bstep (se 1 (by rfl) ⟨2099813, by rfl⟩ : syracuseStep 2799751 = 4199627) B4199627
theorem B2488463 : Blo 1657528 2488463 := bstep (se 1 (by rfl) ⟨1866347, by rfl⟩ : syracuseStep 2488463 = 3732695) B3732695
theorem B2488505 : Blo 1657528 2488505 := bstep (se 2 (by rfl) ⟨933189, by rfl⟩ : syracuseStep 2488505 = 1866379) B1866379
theorem B2488583 : Blo 1657528 2488583 := bstep (se 1 (by rfl) ⟨1866437, by rfl⟩ : syracuseStep 2488583 = 3732875) B3732875
theorem B3733775 : Blo 1657528 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B3733793 : Blo 1657528 3733793 := bstep (se 2 (by rfl) ⟨1400172, by rfl⟩ : syracuseStep 3733793 = 2800345) B2800345
theorem B2488619 : Blo 1657528 2488619 := bstep (se 1 (by rfl) ⟨1866464, by rfl⟩ : syracuseStep 2488619 = 3732929) B3732929
theorem B2488649 : Blo 1657528 2488649 := bstep (se 2 (by rfl) ⟨933243, by rfl⟩ : syracuseStep 2488649 = 1866487) B1866487
theorem B1866127 : Blo 1657528 1866127 := bstep (se 1 (by rfl) ⟨1399595, by rfl⟩ : syracuseStep 1866127 = 2799191) B2799191
theorem B2488763 : Blo 1657528 2488763 := bstep (se 1 (by rfl) ⟨1866572, by rfl⟩ : syracuseStep 2488763 = 3733145) B3733145
theorem B2488823 : Blo 1657528 2488823 := bstep (se 1 (by rfl) ⟨1866617, by rfl⟩ : syracuseStep 2488823 = 3733235) B3733235
theorem B2488847 : Blo 1657528 2488847 := bstep (se 1 (by rfl) ⟨1866635, by rfl⟩ : syracuseStep 2488847 = 3733271) B3733271
theorem B2488889 : Blo 1657528 2488889 := bstep (se 2 (by rfl) ⟨933333, by rfl⟩ : syracuseStep 2488889 = 1866667) B1866667
theorem B8395325 : Blo 1657528 8395325 := bstep (se 3 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 8395325 = 3148247) B3148247
theorem B2488967 : Blo 1657528 2488967 := bstep (se 1 (by rfl) ⟨1866725, by rfl⟩ : syracuseStep 2488967 = 3733451) B3733451
theorem B2489003 : Blo 1657528 2489003 := bstep (se 1 (by rfl) ⟨1866752, by rfl⟩ : syracuseStep 2489003 = 3733505) B3733505
theorem B2489033 : Blo 1657528 2489033 := bstep (se 2 (by rfl) ⟨933387, by rfl⟩ : syracuseStep 2489033 = 1866775) B1866775
theorem B15940313 : Blo 1657528 15940313 := bstep (se 2 (by rfl) ⟨5977617, by rfl⟩ : syracuseStep 15940313 = 11955235) B11955235
theorem B4725515 : Blo 1657528 4725515 := bstep (se 1 (by rfl) ⟨3544136, by rfl⟩ : syracuseStep 4725515 = 7088273) B7088273
theorem B2800399 : Blo 1657528 2800399 := bstep (se 1 (by rfl) ⟨2100299, by rfl⟩ : syracuseStep 2800399 = 4200599) B4200599
theorem B5045051 : Blo 1657528 5045051 := bstep (se 1 (by rfl) ⟨3783788, by rfl⟩ : syracuseStep 5045051 = 7567577) B7567577
theorem B2489147 : Blo 1657528 2489147 := bstep (se 1 (by rfl) ⟨1866860, by rfl⟩ : syracuseStep 2489147 = 3733721) B3733721
theorem B2489207 : Blo 1657528 2489207 := bstep (se 1 (by rfl) ⟨1866905, by rfl⟩ : syracuseStep 2489207 = 3733811) B3733811
theorem B1866631 : Blo 1657528 1866631 := bstep (se 1 (by rfl) ⟨1399973, by rfl⟩ : syracuseStep 1866631 = 2799947) B2799947
theorem B2489231 : Blo 1657528 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B221076373 : Blo 1657528 221076373 := bstep (se 6 (by rfl) ⟨5181477, by rfl⟩ : syracuseStep 221076373 = 10362955) B10362955
theorem B2489273 : Blo 1657528 2489273 := bstep (se 2 (by rfl) ⟨933477, by rfl⟩ : syracuseStep 2489273 = 1866955) B1866955
theorem B22707211 : Blo 1657528 22707211 := bstep (se 1 (by rfl) ⟨17030408, by rfl⟩ : syracuseStep 22707211 = 34060817) B34060817
theorem B6298667 : Blo 1657528 6298667 := bstep (se 1 (by rfl) ⟨4724000, by rfl⟩ : syracuseStep 6298667 = 9448001) B9448001
theorem B1866811 : Blo 1657528 1866811 := bstep (se 1 (by rfl) ⟨1400108, by rfl⟩ : syracuseStep 1866811 = 2800217) B2800217
theorem B2989241 : Blo 1657528 2989241 := bstep (se 2 (by rfl) ⟨1120965, by rfl⟩ : syracuseStep 2989241 = 2241931) B2241931
theorem B2555081 : Blo 1657528 2555081 := bstep (se 2 (by rfl) ⟨958155, by rfl⟩ : syracuseStep 2555081 = 1916311) B1916311
theorem B8969453 : Blo 1657528 8969453 := bstep (se 3 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 8969453 = 3363545) B3363545
theorem B2522411 : Blo 1657528 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B5315975 : Blo 1657528 5315975 := bstep (se 1 (by rfl) ⟨3986981, by rfl⟩ : syracuseStep 5315975 = 7973963) B7973963
theorem B5111225 : Blo 1657528 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B5979577 : Blo 1657528 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B2989703 : Blo 1657528 2989703 := bstep (se 1 (by rfl) ⟨2242277, by rfl⟩ : syracuseStep 2989703 = 4484555) B4484555
theorem B21241601 : Blo 1657528 21241601 := bstep (se 2 (by rfl) ⟨7965600, by rfl⟩ : syracuseStep 21241601 = 15931201) B15931201
theorem B11951887 : Blo 1657528 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B63733553 : Blo 1657528 63733553 := bstep (se 2 (by rfl) ⟨23900082, by rfl⟩ : syracuseStep 63733553 = 47800165) B47800165
theorem B5594939 : Blo 1657528 5594939 := bstep (se 1 (by rfl) ⟨4196204, by rfl⟩ : syracuseStep 5594939 = 8392409) B8392409
theorem B6725435 : Blo 1657528 6725435 := bstep (se 1 (by rfl) ⟨5044076, by rfl⟩ : syracuseStep 6725435 = 10088153) B10088153
theorem B28737431 : Blo 1657528 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B7970831 : Blo 1657528 7970831 := bstep (se 1 (by rfl) ⟨5978123, by rfl⟩ : syracuseStep 7970831 = 11956247) B11956247
theorem B5595155 : Blo 1657528 5595155 := bstep (se 1 (by rfl) ⟨4196366, by rfl⟩ : syracuseStep 5595155 = 8392733) B8392733
theorem B12763453 : Blo 1657528 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B15139133 : Blo 1657528 15139133 := bstep (se 3 (by rfl) ⟨2838587, by rfl⟩ : syracuseStep 15139133 = 5677175) B5677175
theorem B5595479 : Blo 1657528 5595479 := bstep (se 1 (by rfl) ⟨4196609, by rfl⟩ : syracuseStep 5595479 = 8393219) B8393219
theorem B15122969 : Blo 1657528 15122969 := bstep (se 2 (by rfl) ⟨5671113, by rfl⟩ : syracuseStep 15122969 = 11342227) B11342227
theorem B71737973 : Blo 1657528 71737973 := bstep (se 5 (by rfl) ⟨3362717, by rfl⟩ : syracuseStep 71737973 = 6725435) B6725435
theorem B3146759 : Blo 1657528 3146759 := bstep (se 1 (by rfl) ⟨2360069, by rfl⟩ : syracuseStep 3146759 = 4720139) B4720139
theorem B24896531 : Blo 1657528 24896531 := bstep (se 1 (by rfl) ⟨18672398, by rfl⟩ : syracuseStep 24896531 = 37344797) B37344797
theorem B2655271 : Blo 1657528 2655271 := bstep (se 1 (by rfl) ⟨1991453, by rfl⟩ : syracuseStep 2655271 = 3982907) B3982907
theorem B11953271 : Blo 1657528 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B5596559 : Blo 1657528 5596559 := bstep (se 1 (by rfl) ⟨4197419, by rfl⟩ : syracuseStep 5596559 = 8394839) B8394839
theorem B3147169 : Blo 1657528 3147169 := bstep (se 2 (by rfl) ⟨1180188, by rfl⟩ : syracuseStep 3147169 = 2360377) B2360377
theorem B2098811 : Blo 1657528 2098811 := bstep (se 1 (by rfl) ⟨1574108, by rfl⟩ : syracuseStep 2098811 = 3148217) B3148217
theorem B5596883 : Blo 1657528 5596883 := bstep (se 1 (by rfl) ⟨4197662, by rfl⟩ : syracuseStep 5596883 = 8395325) B8395325
theorem B3147511 : Blo 1657528 3147511 := bstep (se 1 (by rfl) ⟨2360633, by rfl⟩ : syracuseStep 3147511 = 4721267) B4721267
theorem B68085497 : Blo 1657528 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B10626875 : Blo 1657528 10626875 := bstep (se 1 (by rfl) ⟨7970156, by rfl⟩ : syracuseStep 10626875 = 15940313) B15940313
theorem B4720457 : Blo 1657528 4720457 := bstep (se 2 (by rfl) ⟨1770171, by rfl⟩ : syracuseStep 4720457 = 3540343) B3540343
theorem B11954081 : Blo 1657528 11954081 := bstep (se 2 (by rfl) ⟨4482780, by rfl⟩ : syracuseStep 11954081 = 8965561) B8965561
theorem B7972769 : Blo 1657528 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B3147815 : Blo 1657528 3147815 := bstep (se 1 (by rfl) ⟨2360861, by rfl⟩ : syracuseStep 3147815 = 4721723) B4721723
theorem B1992827 : Blo 1657528 1992827 := bstep (se 1 (by rfl) ⟨1494620, by rfl⟩ : syracuseStep 1992827 = 2989241) B2989241
theorem B3541163 : Blo 1657528 3541163 := bstep (se 1 (by rfl) ⟨2655872, by rfl⟩ : syracuseStep 3541163 = 5311745) B5311745
theorem B1681607 : Blo 1657528 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B3361015 : Blo 1657528 3361015 := bstep (se 1 (by rfl) ⟨2520761, by rfl⟩ : syracuseStep 3361015 = 5041523) B5041523
theorem B6293821 : Blo 1657528 6293821 := bstep (se 3 (by rfl) ⟨1180091, by rfl⟩ : syracuseStep 6293821 = 2360183) B2360183
theorem B15935849 : Blo 1657528 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B2656655 : Blo 1657528 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B1993135 : Blo 1657528 1993135 := bstep (se 1 (by rfl) ⟨1494851, by rfl⟩ : syracuseStep 1993135 = 2989703) B2989703
theorem B4196873 : Blo 1657528 4196873 := bstep (se 2 (by rfl) ⟨1573827, by rfl⟩ : syracuseStep 4196873 = 3147655) B3147655
theorem B3729959 : Blo 1657528 3729959 := bstep (se 1 (by rfl) ⟨2797469, by rfl⟩ : syracuseStep 3729959 = 5594939) B5594939
theorem B2656847 : Blo 1657528 2656847 := bstep (se 1 (by rfl) ⟨1992635, by rfl⟩ : syracuseStep 2656847 = 3985271) B3985271
theorem B11954861 : Blo 1657528 11954861 := bstep (se 3 (by rfl) ⟨2241536, by rfl⟩ : syracuseStep 11954861 = 4483073) B4483073
theorem B1657543 : Blo 1657528 1657543 := bstep (se 1 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 1657543 = 2486315) B2486315
theorem B4483799 : Blo 1657528 4483799 := bstep (se 1 (by rfl) ⟨3362849, by rfl⟩ : syracuseStep 4483799 = 6725699) B6725699
theorem B1657563 : Blo 1657528 1657563 := bstep (se 1 (by rfl) ⟨1243172, by rfl⟩ : syracuseStep 1657563 = 2486345) B2486345
theorem B1657639 : Blo 1657528 1657639 := bstep (se 1 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 1657639 = 2486459) B2486459
theorem B1657679 : Blo 1657528 1657679 := bstep (se 1 (by rfl) ⟨1243259, by rfl⟩ : syracuseStep 1657679 = 2486519) B2486519
theorem B1657695 : Blo 1657528 1657695 := bstep (se 1 (by rfl) ⟨1243271, by rfl⟩ : syracuseStep 1657695 = 2486543) B2486543
theorem B3730283 : Blo 1657528 3730283 := bstep (se 1 (by rfl) ⟨2797712, by rfl⟩ : syracuseStep 3730283 = 5595425) B5595425
theorem B5598071 : Blo 1657528 5598071 := bstep (se 1 (by rfl) ⟨4198553, by rfl⟩ : syracuseStep 5598071 = 8397107) B8397107
theorem B1657723 : Blo 1657528 1657723 := bstep (se 1 (by rfl) ⟨1243292, by rfl⟩ : syracuseStep 1657723 = 2486585) B2486585
theorem B3730337 : Blo 1657528 3730337 := bstep (se 2 (by rfl) ⟨1398876, by rfl⟩ : syracuseStep 3730337 = 2797753) B2797753
theorem B8391599 : Blo 1657528 8391599 := bstep (se 1 (by rfl) ⟨6293699, by rfl⟩ : syracuseStep 8391599 = 12587399) B12587399
theorem B1657775 : Blo 1657528 1657775 := bstep (se 1 (by rfl) ⟨1243331, by rfl⟩ : syracuseStep 1657775 = 2486663) B2486663
theorem B1657799 : Blo 1657528 1657799 := bstep (se 1 (by rfl) ⟨1243349, by rfl⟩ : syracuseStep 1657799 = 2486699) B2486699
theorem B1657819 : Blo 1657528 1657819 := bstep (se 1 (by rfl) ⟨1243364, by rfl⟩ : syracuseStep 1657819 = 2486729) B2486729
theorem B5311489 : Blo 1657528 5311489 := bstep (se 2 (by rfl) ⟨1991808, by rfl⟩ : syracuseStep 5311489 = 3983617) B3983617
theorem B1657895 : Blo 1657528 1657895 := bstep (se 1 (by rfl) ⟨1243421, by rfl⟩ : syracuseStep 1657895 = 2486843) B2486843
theorem B22686799 : Blo 1657528 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B1657935 : Blo 1657528 1657935 := bstep (se 1 (by rfl) ⟨1243451, by rfl⟩ : syracuseStep 1657935 = 2486903) B2486903
theorem B5598287 : Blo 1657528 5598287 := bstep (se 1 (by rfl) ⟨4198715, by rfl⟩ : syracuseStep 5598287 = 8397431) B8397431
theorem B1657951 : Blo 1657528 1657951 := bstep (se 1 (by rfl) ⟨1243463, by rfl⟩ : syracuseStep 1657951 = 2486927) B2486927
theorem B1657979 : Blo 1657528 1657979 := bstep (se 1 (by rfl) ⟨1243484, by rfl⟩ : syracuseStep 1657979 = 2486969) B2486969
theorem B1658031 : Blo 1657528 1658031 := bstep (se 1 (by rfl) ⟨1243523, by rfl⟩ : syracuseStep 1658031 = 2487047) B2487047
theorem B1658055 : Blo 1657528 1658055 := bstep (se 1 (by rfl) ⟨1243541, by rfl⟩ : syracuseStep 1658055 = 2487083) B2487083
theorem B9440459 : Blo 1657528 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B1658075 : Blo 1657528 1658075 := bstep (se 1 (by rfl) ⟨1243556, by rfl⟩ : syracuseStep 1658075 = 2487113) B2487113
theorem B3730679 : Blo 1657528 3730679 := bstep (se 1 (by rfl) ⟨2798009, by rfl⟩ : syracuseStep 3730679 = 5596019) B5596019
theorem B34958627 : Blo 1657528 34958627 := bstep (se 1 (by rfl) ⟨26218970, by rfl⟩ : syracuseStep 34958627 = 52437941) B52437941
theorem B1658151 : Blo 1657528 1658151 := bstep (se 1 (by rfl) ⟨1243613, by rfl⟩ : syracuseStep 1658151 = 2487227) B2487227
theorem B1658191 : Blo 1657528 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1658207 : Blo 1657528 1658207 := bstep (se 1 (by rfl) ⟨1243655, by rfl⟩ : syracuseStep 1658207 = 2487311) B2487311
theorem B65514865 : Blo 1657528 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B1658235 : Blo 1657528 1658235 := bstep (se 1 (by rfl) ⟨1243676, by rfl⟩ : syracuseStep 1658235 = 2487353) B2487353
theorem B36359597 : Blo 1657528 36359597 := bstep (se 3 (by rfl) ⟨6817424, by rfl⟩ : syracuseStep 36359597 = 13634849) B13634849
theorem B1658287 : Blo 1657528 1658287 := bstep (se 1 (by rfl) ⟨1243715, by rfl⟩ : syracuseStep 1658287 = 2487431) B2487431
theorem B1658311 : Blo 1657528 1658311 := bstep (se 1 (by rfl) ⟨1243733, by rfl⟩ : syracuseStep 1658311 = 2487467) B2487467
theorem B5598665 : Blo 1657528 5598665 := bstep (se 2 (by rfl) ⟨2099499, by rfl⟩ : syracuseStep 5598665 = 4198999) B4198999
theorem B1658331 : Blo 1657528 1658331 := bstep (se 1 (by rfl) ⟨1243748, by rfl⟩ : syracuseStep 1658331 = 2487497) B2487497
theorem B8400347 : Blo 1657528 8400347 := bstep (se 1 (by rfl) ⟨6300260, by rfl⟩ : syracuseStep 8400347 = 12600521) B12600521
theorem B1658407 : Blo 1657528 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B48459341 : Blo 1657528 48459341 := bstep (se 3 (by rfl) ⟨9086126, by rfl⟩ : syracuseStep 48459341 = 18172253) B18172253
theorem B1658447 : Blo 1657528 1658447 := bstep (se 1 (by rfl) ⟨1243835, by rfl⟩ : syracuseStep 1658447 = 2487671) B2487671
theorem B1658463 : Blo 1657528 1658463 := bstep (se 1 (by rfl) ⟨1243847, by rfl⟩ : syracuseStep 1658463 = 2487695) B2487695
theorem B1658491 : Blo 1657528 1658491 := bstep (se 1 (by rfl) ⟨1243868, by rfl⟩ : syracuseStep 1658491 = 2487737) B2487737
theorem B4198027 : Blo 1657528 4198027 := bstep (se 1 (by rfl) ⟨3148520, by rfl⟩ : syracuseStep 4198027 = 6297041) B6297041
theorem B1658543 : Blo 1657528 1658543 := bstep (se 1 (by rfl) ⟨1243907, by rfl⟩ : syracuseStep 1658543 = 2487815) B2487815
theorem B9572039 : Blo 1657528 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1658567 : Blo 1657528 1658567 := bstep (se 1 (by rfl) ⟨1243925, by rfl⟩ : syracuseStep 1658567 = 2487851) B2487851
theorem B5598935 : Blo 1657528 5598935 := bstep (se 1 (by rfl) ⟨4199201, by rfl⟩ : syracuseStep 5598935 = 8398403) B8398403
theorem B1658587 : Blo 1657528 1658587 := bstep (se 1 (by rfl) ⟨1243940, by rfl⟩ : syracuseStep 1658587 = 2487881) B2487881
theorem B1658663 : Blo 1657528 1658663 := bstep (se 1 (by rfl) ⟨1243997, by rfl⟩ : syracuseStep 1658663 = 2487995) B2487995
theorem B3731273 : Blo 1657528 3731273 := bstep (se 2 (by rfl) ⟨1399227, by rfl⟩ : syracuseStep 3731273 = 2798455) B2798455
theorem B1658703 : Blo 1657528 1658703 := bstep (se 1 (by rfl) ⟨1244027, by rfl⟩ : syracuseStep 1658703 = 2488055) B2488055
theorem B10768223 : Blo 1657528 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B1658719 : Blo 1657528 1658719 := bstep (se 1 (by rfl) ⟨1244039, by rfl⟩ : syracuseStep 1658719 = 2488079) B2488079
theorem B3149675 : Blo 1657528 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B294768497 : Blo 1657528 294768497 := bstep (se 2 (by rfl) ⟨110538186, by rfl⟩ : syracuseStep 294768497 = 221076373) B221076373
theorem B9441143 : Blo 1657528 9441143 := bstep (se 1 (by rfl) ⟨7080857, by rfl⟩ : syracuseStep 9441143 = 14161715) B14161715
theorem B1658747 : Blo 1657528 1658747 := bstep (se 1 (by rfl) ⟨1244060, by rfl⟩ : syracuseStep 1658747 = 2488121) B2488121
theorem B12586913 : Blo 1657528 12586913 := bstep (se 2 (by rfl) ⟨4720092, by rfl⟩ : syracuseStep 12586913 = 9440185) B9440185
theorem B3362735 : Blo 1657528 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B1658799 : Blo 1657528 1658799 := bstep (se 1 (by rfl) ⟨1244099, by rfl⟩ : syracuseStep 1658799 = 2488199) B2488199
theorem B5599151 : Blo 1657528 5599151 := bstep (se 1 (by rfl) ⟨4199363, by rfl⟩ : syracuseStep 5599151 = 8398727) B8398727
theorem B18902969 : Blo 1657528 18902969 := bstep (se 2 (by rfl) ⟨7088613, by rfl⟩ : syracuseStep 18902969 = 14177227) B14177227
theorem B4198331 : Blo 1657528 4198331 := bstep (se 1 (by rfl) ⟨3148748, by rfl⟩ : syracuseStep 4198331 = 6297497) B6297497
theorem B15945659 : Blo 1657528 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B8400833 : Blo 1657528 8400833 := bstep (se 2 (by rfl) ⟨3150312, by rfl⟩ : syracuseStep 8400833 = 6300625) B6300625
theorem B1658823 : Blo 1657528 1658823 := bstep (se 1 (by rfl) ⟨1244117, by rfl⟩ : syracuseStep 1658823 = 2488235) B2488235
theorem B1658843 : Blo 1657528 1658843 := bstep (se 1 (by rfl) ⟨1244132, by rfl⟩ : syracuseStep 1658843 = 2488265) B2488265
theorem B6295553 : Blo 1657528 6295553 := bstep (se 2 (by rfl) ⟨2360832, by rfl⟩ : syracuseStep 6295553 = 4721665) B4721665
theorem B1658919 : Blo 1657528 1658919 := bstep (se 1 (by rfl) ⟨1244189, by rfl⟩ : syracuseStep 1658919 = 2488379) B2488379
theorem B2797625 : Blo 1657528 2797625 := bstep (se 2 (by rfl) ⟨1049109, by rfl⟩ : syracuseStep 2797625 = 2098219) B2098219
theorem B2486351 : Blo 1657528 2486351 := bstep (se 1 (by rfl) ⟨1864763, by rfl⟩ : syracuseStep 2486351 = 3729527) B3729527
theorem B1658959 : Blo 1657528 1658959 := bstep (se 1 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 1658959 = 2488439) B2488439
theorem B3149903 : Blo 1657528 3149903 := bstep (se 1 (by rfl) ⟨2362427, by rfl⟩ : syracuseStep 3149903 = 4724855) B4724855
theorem B1658975 : Blo 1657528 1658975 := bstep (se 1 (by rfl) ⟨1244231, by rfl⟩ : syracuseStep 1658975 = 2488463) B2488463
theorem B1659003 : Blo 1657528 1659003 := bstep (se 1 (by rfl) ⟨1244252, by rfl⟩ : syracuseStep 1659003 = 2488505) B2488505
theorem B1659055 : Blo 1657528 1659055 := bstep (se 1 (by rfl) ⟨1244291, by rfl⟩ : syracuseStep 1659055 = 2488583) B2488583
theorem B2486471 : Blo 1657528 2486471 := bstep (se 1 (by rfl) ⟨1864853, by rfl⟩ : syracuseStep 2486471 = 3729707) B3729707
theorem B1659079 : Blo 1657528 1659079 := bstep (se 1 (by rfl) ⟨1244309, by rfl⟩ : syracuseStep 1659079 = 2488619) B2488619
theorem B1659099 : Blo 1657528 1659099 := bstep (se 1 (by rfl) ⟨1244324, by rfl⟩ : syracuseStep 1659099 = 2488649) B2488649
theorem B1659175 : Blo 1657528 1659175 := bstep (se 1 (by rfl) ⟨1244381, by rfl⟩ : syracuseStep 1659175 = 2488763) B2488763
theorem B1659215 : Blo 1657528 1659215 := bstep (se 1 (by rfl) ⟨1244411, by rfl⟩ : syracuseStep 1659215 = 2488823) B2488823
theorem B1659231 : Blo 1657528 1659231 := bstep (se 1 (by rfl) ⟨1244423, by rfl⟩ : syracuseStep 1659231 = 2488847) B2488847
theorem B2486633 : Blo 1657528 2486633 := bstep (se 2 (by rfl) ⟨932487, by rfl⟩ : syracuseStep 2486633 = 1864975) B1864975
theorem B5312873 : Blo 1657528 5312873 := bstep (se 2 (by rfl) ⟨1992327, by rfl⟩ : syracuseStep 5312873 = 3984655) B3984655
theorem B1659259 : Blo 1657528 1659259 := bstep (se 1 (by rfl) ⟨1244444, by rfl⟩ : syracuseStep 1659259 = 2488889) B2488889
theorem B1659311 : Blo 1657528 1659311 := bstep (se 1 (by rfl) ⟨1244483, by rfl⟩ : syracuseStep 1659311 = 2488967) B2488967
theorem B2486711 : Blo 1657528 2486711 := bstep (se 1 (by rfl) ⟨1865033, by rfl⟩ : syracuseStep 2486711 = 3730067) B3730067
theorem B1659335 : Blo 1657528 1659335 := bstep (se 1 (by rfl) ⟨1244501, by rfl⟩ : syracuseStep 1659335 = 2489003) B2489003
theorem B5976521 : Blo 1657528 5976521 := bstep (se 2 (by rfl) ⟨2241195, by rfl⟩ : syracuseStep 5976521 = 4482391) B4482391
theorem B2486747 : Blo 1657528 2486747 := bstep (se 1 (by rfl) ⟨1865060, by rfl⟩ : syracuseStep 2486747 = 3730121) B3730121
theorem B1659355 : Blo 1657528 1659355 := bstep (se 1 (by rfl) ⟨1244516, by rfl⟩ : syracuseStep 1659355 = 2489033) B2489033
theorem B3150343 : Blo 1657528 3150343 := bstep (se 1 (by rfl) ⟨2362757, by rfl⟩ : syracuseStep 3150343 = 4725515) B4725515
theorem B3363367 : Blo 1657528 3363367 := bstep (se 1 (by rfl) ⟨2522525, by rfl⟩ : syracuseStep 3363367 = 5045051) B5045051
theorem B1659431 : Blo 1657528 1659431 := bstep (se 1 (by rfl) ⟨1244573, by rfl⟩ : syracuseStep 1659431 = 2489147) B2489147
theorem B1659471 : Blo 1657528 1659471 := bstep (se 1 (by rfl) ⟨1244603, by rfl⟩ : syracuseStep 1659471 = 2489207) B2489207
theorem B1659487 : Blo 1657528 1659487 := bstep (se 1 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 1659487 = 2489231) B2489231
theorem B3732065 : Blo 1657528 3732065 := bstep (se 2 (by rfl) ⟨1399524, by rfl⟩ : syracuseStep 3732065 = 2799049) B2799049
theorem B1659515 : Blo 1657528 1659515 := bstep (se 1 (by rfl) ⟨1244636, by rfl⟩ : syracuseStep 1659515 = 2489273) B2489273
theorem B4199111 : Blo 1657528 4199111 := bstep (se 1 (by rfl) ⟨3149333, by rfl⟩ : syracuseStep 4199111 = 6298667) B6298667
theorem B2798327 : Blo 1657528 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B4199161 : Blo 1657528 4199161 := bstep (se 2 (by rfl) ⟨1574685, by rfl⟩ : syracuseStep 4199161 = 3149371) B3149371
theorem B2487215 : Blo 1657528 2487215 := bstep (se 1 (by rfl) ⟨1865411, by rfl⟩ : syracuseStep 2487215 = 3730823) B3730823
theorem B3543983 : Blo 1657528 3543983 := bstep (se 1 (by rfl) ⟨2657987, by rfl⟩ : syracuseStep 3543983 = 5315975) B5315975
theorem B3732407 : Blo 1657528 3732407 := bstep (se 1 (by rfl) ⟨2799305, by rfl⟩ : syracuseStep 3732407 = 5598611) B5598611
theorem B2487305 : Blo 1657528 2487305 := bstep (se 2 (by rfl) ⟨932739, by rfl⟩ : syracuseStep 2487305 = 1865479) B1865479
theorem B2487335 : Blo 1657528 2487335 := bstep (se 1 (by rfl) ⟨1865501, by rfl⟩ : syracuseStep 2487335 = 3731003) B3731003
theorem B2798671 : Blo 1657528 2798671 := bstep (se 1 (by rfl) ⟨2099003, by rfl⟩ : syracuseStep 2798671 = 4198007) B4198007
theorem B2487419 : Blo 1657528 2487419 := bstep (se 1 (by rfl) ⟨1865564, by rfl⟩ : syracuseStep 2487419 = 3731129) B3731129
theorem B14161067 : Blo 1657528 14161067 := bstep (se 1 (by rfl) ⟨10620800, by rfl⟩ : syracuseStep 14161067 = 21241601) B21241601
theorem B40334507 : Blo 1657528 40334507 := bstep (se 1 (by rfl) ⟨30250880, by rfl⟩ : syracuseStep 40334507 = 60501761) B60501761
theorem B1864903 : Blo 1657528 1864903 := bstep (se 1 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 1864903 = 2797355) B2797355
theorem B42489035 : Blo 1657528 42489035 := bstep (se 1 (by rfl) ⟨31866776, by rfl⟩ : syracuseStep 42489035 = 63733553) B63733553
theorem B2487545 : Blo 1657528 2487545 := bstep (se 2 (by rfl) ⟨932829, by rfl⟩ : syracuseStep 2487545 = 1865659) B1865659
theorem B19158287 : Blo 1657528 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B2798921 : Blo 1657528 2798921 := bstep (se 2 (by rfl) ⟨1049595, by rfl⟩ : syracuseStep 2798921 = 2099191) B2099191
theorem B2487647 : Blo 1657528 2487647 := bstep (se 1 (by rfl) ⟨1865735, by rfl⟩ : syracuseStep 2487647 = 3731471) B3731471
theorem B2487659 : Blo 1657528 2487659 := bstep (se 1 (by rfl) ⟨1865744, by rfl⟩ : syracuseStep 2487659 = 3731489) B3731489
theorem B4199809 : Blo 1657528 4199809 := bstep (se 2 (by rfl) ⟨1574928, by rfl⟩ : syracuseStep 4199809 = 3149857) B3149857
theorem B23901587 : Blo 1657528 23901587 := bstep (se 1 (by rfl) ⟨17926190, by rfl⟩ : syracuseStep 23901587 = 35852381) B35852381
theorem B9450917 : Blo 1657528 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B3192247 : Blo 1657528 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B17937865 : Blo 1657528 17937865 := bstep (se 2 (by rfl) ⟨6726699, by rfl⟩ : syracuseStep 17937865 = 13453399) B13453399
theorem B6723053 : Blo 1657528 6723053 := bstep (se 3 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 6723053 = 2521145) B2521145
theorem B3733001 : Blo 1657528 3733001 := bstep (se 2 (by rfl) ⟨1399875, by rfl⟩ : syracuseStep 3733001 = 2799751) B2799751
theorem B3233299 : Blo 1657528 3233299 := bstep (se 1 (by rfl) ⟨2424974, by rfl⟩ : syracuseStep 3233299 = 4849949) B4849949
theorem B2487887 : Blo 1657528 2487887 := bstep (se 1 (by rfl) ⟨1865915, by rfl⟩ : syracuseStep 2487887 = 3731831) B3731831
theorem B6297223 : Blo 1657528 6297223 := bstep (se 1 (by rfl) ⟨4722917, by rfl⟩ : syracuseStep 6297223 = 9445835) B9445835
theorem B2488007 : Blo 1657528 2488007 := bstep (se 1 (by rfl) ⟨1866005, by rfl⟩ : syracuseStep 2488007 = 3732011) B3732011
theorem B14169815 : Blo 1657528 14169815 := bstep (se 1 (by rfl) ⟨10627361, by rfl⟩ : syracuseStep 14169815 = 21254723) B21254723
theorem B10630871 : Blo 1657528 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B2799353 : Blo 1657528 2799353 := bstep (se 2 (by rfl) ⟨1049757, by rfl⟩ : syracuseStep 2799353 = 2099515) B2099515
theorem B3733343 : Blo 1657528 3733343 := bstep (se 1 (by rfl) ⟨2800007, by rfl⟩ : syracuseStep 3733343 = 5600015) B5600015
theorem B2488169 : Blo 1657528 2488169 := bstep (se 2 (by rfl) ⟨933063, by rfl⟩ : syracuseStep 2488169 = 1866127) B1866127
theorem B2799535 : Blo 1657528 2799535 := bstep (se 1 (by rfl) ⟨2099651, by rfl⟩ : syracuseStep 2799535 = 4199303) B4199303
theorem B6297527 : Blo 1657528 6297527 := bstep (se 1 (by rfl) ⟨4723145, by rfl⟩ : syracuseStep 6297527 = 9446291) B9446291
theorem B2488247 : Blo 1657528 2488247 := bstep (se 1 (by rfl) ⟨1866185, by rfl⟩ : syracuseStep 2488247 = 3732371) B3732371
theorem B2488283 : Blo 1657528 2488283 := bstep (se 1 (by rfl) ⟨1866212, by rfl⟩ : syracuseStep 2488283 = 3732425) B3732425
theorem B2799623 : Blo 1657528 2799623 := bstep (se 1 (by rfl) ⟨2099717, by rfl⟩ : syracuseStep 2799623 = 4199435) B4199435
theorem B3782675 : Blo 1657528 3782675 := bstep (se 1 (by rfl) ⟨2837006, by rfl⟩ : syracuseStep 3782675 = 5674013) B5674013
theorem B3733523 : Blo 1657528 3733523 := bstep (se 1 (by rfl) ⟨2800142, by rfl⟩ : syracuseStep 3733523 = 5600285) B5600285
theorem B1865767 : Blo 1657528 1865767 := bstep (se 1 (by rfl) ⟨1399325, by rfl⟩ : syracuseStep 1865767 = 2798651) B2798651
theorem B4200619 : Blo 1657528 4200619 := bstep (se 1 (by rfl) ⟨3150464, by rfl⟩ : syracuseStep 4200619 = 6300929) B6300929
theorem B2799967 : Blo 1657528 2799967 := bstep (se 1 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 2799967 = 4199951) B4199951
theorem B3733865 : Blo 1657528 3733865 := bstep (se 2 (by rfl) ⟨1400199, by rfl⟩ : syracuseStep 3733865 = 2800399) B2800399
theorem B2488751 : Blo 1657528 2488751 := bstep (se 1 (by rfl) ⟨1866563, by rfl⟩ : syracuseStep 2488751 = 3733127) B3733127
theorem B2800055 : Blo 1657528 2800055 := bstep (se 1 (by rfl) ⟨2100041, by rfl⟩ : syracuseStep 2800055 = 4200083) B4200083
theorem B2488841 : Blo 1657528 2488841 := bstep (se 2 (by rfl) ⟨933315, by rfl⟩ : syracuseStep 2488841 = 1866631) B1866631
theorem B14162465 : Blo 1657528 14162465 := bstep (se 2 (by rfl) ⟨5310924, by rfl⟩ : syracuseStep 14162465 = 10621849) B10621849
theorem B68074019 : Blo 1657528 68074019 := bstep (se 1 (by rfl) ⟨51055514, by rfl⟩ : syracuseStep 68074019 = 102111029) B102111029
theorem B2488871 : Blo 1657528 2488871 := bstep (se 1 (by rfl) ⟨1866653, by rfl⟩ : syracuseStep 2488871 = 3733307) B3733307
theorem B4725287 : Blo 1657528 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B49109579 : Blo 1657528 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B2488955 : Blo 1657528 2488955 := bstep (se 1 (by rfl) ⟨1866716, by rfl⟩ : syracuseStep 2488955 = 3733433) B3733433
theorem B28334771 : Blo 1657528 28334771 := bstep (se 1 (by rfl) ⟨21251078, by rfl⟩ : syracuseStep 28334771 = 42502157) B42502157
theorem B30276281 : Blo 1657528 30276281 := bstep (se 2 (by rfl) ⟨11353605, by rfl⟩ : syracuseStep 30276281 = 22707211) B22707211
theorem B5315321 : Blo 1657528 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B2489081 : Blo 1657528 2489081 := bstep (se 2 (by rfl) ⟨933405, by rfl⟩ : syracuseStep 2489081 = 1866811) B1866811
theorem B2489183 : Blo 1657528 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B2489195 : Blo 1657528 2489195 := bstep (se 1 (by rfl) ⟨1866896, by rfl⟩ : syracuseStep 2489195 = 3733793) B3733793
theorem B6298681 : Blo 1657528 6298681 := bstep (se 2 (by rfl) ⟨2362005, by rfl⟩ : syracuseStep 6298681 = 4724011) B4724011
theorem B11951171 : Blo 1657528 11951171 := bstep (se 1 (by rfl) ⟨8963378, by rfl⟩ : syracuseStep 11951171 = 17926757) B17926757
theorem B6298985 : Blo 1657528 6298985 := bstep (se 2 (by rfl) ⟨2362119, by rfl⟩ : syracuseStep 6298985 = 4724239) B4724239
theorem B5979521 : Blo 1657528 5979521 := bstep (se 2 (by rfl) ⟨2242320, by rfl⟩ : syracuseStep 5979521 = 4484641) B4484641
theorem B17030573 : Blo 1657528 17030573 := bstep (se 3 (by rfl) ⟨3193232, by rfl⟩ : syracuseStep 17030573 = 6386465) B6386465
theorem B2989487 : Blo 1657528 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B1703387 : Blo 1657528 1703387 := bstep (se 1 (by rfl) ⟨1277540, by rfl⟩ : syracuseStep 1703387 = 2555081) B2555081
theorem B5979635 : Blo 1657528 5979635 := bstep (se 1 (by rfl) ⟨4484726, by rfl⟩ : syracuseStep 5979635 = 8969453) B8969453
theorem B3407483 : Blo 1657528 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B9445085 : Blo 1657528 9445085 := bstep (se 3 (by rfl) ⟨1770953, by rfl⟩ : syracuseStep 9445085 = 3541907) B3541907
theorem B10092755 : Blo 1657528 10092755 := bstep (se 1 (by rfl) ⟨7569566, by rfl⟩ : syracuseStep 10092755 = 15139133) B15139133
theorem B31875389 : Blo 1657528 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B4481353 : Blo 1657528 4481353 := bstep (se 2 (by rfl) ⟨1680507, by rfl⟩ : syracuseStep 4481353 = 3361015) B3361015
theorem B47825315 : Blo 1657528 47825315 := bstep (se 1 (by rfl) ⟨35868986, by rfl⟩ : syracuseStep 47825315 = 71737973) B71737973
theorem B2097839 : Blo 1657528 2097839 := bstep (se 1 (by rfl) ⟨1573379, by rfl⟩ : syracuseStep 2097839 = 3146759) B3146759
theorem B15934391 : Blo 1657528 15934391 := bstep (se 1 (by rfl) ⟨11950793, by rfl⟩ : syracuseStep 15934391 = 23901587) B23901587
theorem B6300611 : Blo 1657528 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B4482035 : Blo 1657528 4482035 := bstep (se 1 (by rfl) ⟨3361526, by rfl⟩ : syracuseStep 4482035 = 6723053) B6723053
theorem B7971965 : Blo 1657528 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B9446543 : Blo 1657528 9446543 := bstep (se 1 (by rfl) ⟨7084907, by rfl⟩ : syracuseStep 9446543 = 14169815) B14169815
theorem B7087247 : Blo 1657528 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B2098543 : Blo 1657528 2098543 := bstep (se 1 (by rfl) ⟨1573907, by rfl⟩ : syracuseStep 2098543 = 3147815) B3147815
theorem B3540361 : Blo 1657528 3540361 := bstep (se 2 (by rfl) ⟨1327635, by rfl⟩ : syracuseStep 3540361 = 2655271) B2655271
theorem B8398241 : Blo 1657528 8398241 := bstep (se 2 (by rfl) ⟨3149340, by rfl⟩ : syracuseStep 8398241 = 6298681) B6298681
theorem B1771103 : Blo 1657528 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B5596829 : Blo 1657528 5596829 := bstep (se 3 (by rfl) ⟨1049405, by rfl⟩ : syracuseStep 5596829 = 2098811) B2098811
theorem B1771231 : Blo 1657528 1771231 := bstep (se 1 (by rfl) ⟨1328423, by rfl⟩ : syracuseStep 1771231 = 2656847) B2656847
theorem B87353153 : Blo 1657528 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B4196225 : Blo 1657528 4196225 := bstep (se 2 (by rfl) ⟨1573584, by rfl⟩ : syracuseStep 4196225 = 3147169) B3147169
theorem B14174189 : Blo 1657528 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B4311065 : Blo 1657528 4311065 := bstep (se 2 (by rfl) ⟨1616649, by rfl⟩ : syracuseStep 4311065 = 3233299) B3233299
theorem B6293639 : Blo 1657528 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B5597369 : Blo 1657528 5597369 := bstep (se 2 (by rfl) ⟨2099013, by rfl⟩ : syracuseStep 5597369 = 4198027) B4198027
theorem B4196681 : Blo 1657528 4196681 := bstep (se 2 (by rfl) ⟨1573755, by rfl⟩ : syracuseStep 4196681 = 3147511) B3147511
theorem B2271655 : Blo 1657528 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B21260717 : Blo 1657528 21260717 := bstep (se 3 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 21260717 = 7972769) B7972769
theorem B7178815 : Blo 1657528 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B2099783 : Blo 1657528 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B196512331 : Blo 1657528 196512331 := bstep (se 1 (by rfl) ⟨147384248, by rfl⟩ : syracuseStep 196512331 = 294768497) B294768497
theorem B6294095 : Blo 1657528 6294095 := bstep (se 1 (by rfl) ⟨4720571, by rfl⟩ : syracuseStep 6294095 = 9441143) B9441143
theorem B8391275 : Blo 1657528 8391275 := bstep (se 1 (by rfl) ⟨6293456, by rfl⟩ : syracuseStep 8391275 = 12586913) B12586913
theorem B12601979 : Blo 1657528 12601979 := bstep (se 1 (by rfl) ⟨9451484, by rfl⟩ : syracuseStep 12601979 = 18902969) B18902969
theorem B4197035 : Blo 1657528 4197035 := bstep (se 1 (by rfl) ⟨3147776, by rfl⟩ : syracuseStep 4197035 = 6295553) B6295553
theorem B3730103 : Blo 1657528 3730103 := bstep (se 1 (by rfl) ⟨2797577, by rfl⟩ : syracuseStep 3730103 = 5595155) B5595155
theorem B66390749 : Blo 1657528 66390749 := bstep (se 3 (by rfl) ⟨12448265, by rfl⟩ : syracuseStep 66390749 = 24896531) B24896531
theorem B1657567 : Blo 1657528 1657567 := bstep (se 1 (by rfl) ⟨1243175, by rfl⟩ : syracuseStep 1657567 = 2486351) B2486351
theorem B2099935 : Blo 1657528 2099935 := bstep (se 1 (by rfl) ⟨1574951, by rfl⟩ : syracuseStep 2099935 = 3149903) B3149903
theorem B1657647 : Blo 1657528 1657647 := bstep (se 1 (by rfl) ⟨1243235, by rfl⟩ : syracuseStep 1657647 = 2486471) B2486471
theorem B3730319 : Blo 1657528 3730319 := bstep (se 1 (by rfl) ⟨2797739, by rfl⟩ : syracuseStep 3730319 = 5595479) B5595479
theorem B1657755 : Blo 1657528 1657755 := bstep (se 1 (by rfl) ⟨1243316, by rfl⟩ : syracuseStep 1657755 = 2486633) B2486633
theorem B3541915 : Blo 1657528 3541915 := bstep (se 1 (by rfl) ⟨2656436, by rfl⟩ : syracuseStep 3541915 = 5312873) B5312873
theorem B1657807 : Blo 1657528 1657807 := bstep (se 1 (by rfl) ⟨1243355, by rfl⟩ : syracuseStep 1657807 = 2486711) B2486711
theorem B3984347 : Blo 1657528 3984347 := bstep (se 1 (by rfl) ⟨2988260, by rfl⟩ : syracuseStep 3984347 = 5976521) B5976521
theorem B1657831 : Blo 1657528 1657831 := bstep (se 1 (by rfl) ⟨1243373, by rfl⟩ : syracuseStep 1657831 = 2486747) B2486747
theorem B8391761 : Blo 1657528 8391761 := bstep (se 2 (by rfl) ⟨3146910, by rfl⟩ : syracuseStep 8391761 = 6293821) B6293821
theorem B17017937 : Blo 1657528 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B4484285 : Blo 1657528 4484285 := bstep (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) B1681607
theorem B2657513 : Blo 1657528 2657513 := bstep (se 2 (by rfl) ⟨996567, by rfl⟩ : syracuseStep 2657513 = 1993135) B1993135
theorem B1658143 : Blo 1657528 1658143 := bstep (se 1 (by rfl) ⟨1243607, by rfl⟩ : syracuseStep 1658143 = 2487215) B2487215
theorem B2362655 : Blo 1657528 2362655 := bstep (se 1 (by rfl) ⟨1771991, by rfl⟩ : syracuseStep 2362655 = 3543983) B3543983
theorem B1658203 : Blo 1657528 1658203 := bstep (se 1 (by rfl) ⟨1243652, by rfl⟩ : syracuseStep 1658203 = 2487305) B2487305
theorem B1658223 : Blo 1657528 1658223 := bstep (se 1 (by rfl) ⟨1243667, by rfl⟩ : syracuseStep 1658223 = 2487335) B2487335
theorem B51088765 : Blo 1657528 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B4484489 : Blo 1657528 4484489 := bstep (se 2 (by rfl) ⟨1681683, by rfl⟩ : syracuseStep 4484489 = 3363367) B3363367
theorem B1658279 : Blo 1657528 1658279 := bstep (se 1 (by rfl) ⟨1243709, by rfl⟩ : syracuseStep 1658279 = 2487419) B2487419
theorem B9440711 : Blo 1657528 9440711 := bstep (se 1 (by rfl) ⟨7080533, by rfl⟩ : syracuseStep 9440711 = 14161067) B14161067
theorem B26889671 : Blo 1657528 26889671 := bstep (se 1 (by rfl) ⟨20167253, by rfl⟩ : syracuseStep 26889671 = 40334507) B40334507
theorem B1658363 : Blo 1657528 1658363 := bstep (se 1 (by rfl) ⟨1243772, by rfl⟩ : syracuseStep 1658363 = 2487545) B2487545
theorem B1658431 : Blo 1657528 1658431 := bstep (se 1 (by rfl) ⟨1243823, by rfl⟩ : syracuseStep 1658431 = 2487647) B2487647
theorem B1658439 : Blo 1657528 1658439 := bstep (se 1 (by rfl) ⟨1243829, by rfl⟩ : syracuseStep 1658439 = 2487659) B2487659
theorem B3731039 : Blo 1657528 3731039 := bstep (se 1 (by rfl) ⟨2798279, by rfl⟩ : syracuseStep 3731039 = 5596559) B5596559
theorem B5598881 : Blo 1657528 5598881 := bstep (se 2 (by rfl) ⟨2099580, by rfl⟩ : syracuseStep 5598881 = 4199161) B4199161
theorem B1658591 : Blo 1657528 1658591 := bstep (se 1 (by rfl) ⟨1243943, by rfl⟩ : syracuseStep 1658591 = 2487887) B2487887
theorem B1658671 : Blo 1657528 1658671 := bstep (se 1 (by rfl) ⟨1244003, by rfl⟩ : syracuseStep 1658671 = 2488007) B2488007
theorem B3731255 : Blo 1657528 3731255 := bstep (se 1 (by rfl) ⟨2798441, by rfl⟩ : syracuseStep 3731255 = 5596883) B5596883
theorem B1658779 : Blo 1657528 1658779 := bstep (se 1 (by rfl) ⟨1244084, by rfl⟩ : syracuseStep 1658779 = 2488169) B2488169
theorem B4542365 : Blo 1657528 4542365 := bstep (se 3 (by rfl) ⟨851693, by rfl⟩ : syracuseStep 4542365 = 1703387) B1703387
theorem B4198351 : Blo 1657528 4198351 := bstep (se 1 (by rfl) ⟨3148763, by rfl⟩ : syracuseStep 4198351 = 6297527) B6297527
theorem B1658831 : Blo 1657528 1658831 := bstep (se 1 (by rfl) ⟨1244123, by rfl⟩ : syracuseStep 1658831 = 2488247) B2488247
theorem B1658855 : Blo 1657528 1658855 := bstep (se 1 (by rfl) ⟨1244141, by rfl⟩ : syracuseStep 1658855 = 2488283) B2488283
theorem B7081985 : Blo 1657528 7081985 := bstep (se 2 (by rfl) ⟨2655744, by rfl⟩ : syracuseStep 7081985 = 5311489) B5311489
theorem B30249065 : Blo 1657528 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B3731561 : Blo 1657528 3731561 := bstep (se 2 (by rfl) ⟨1399335, by rfl⟩ : syracuseStep 3731561 = 2798671) B2798671
theorem B129224909 : Blo 1657528 129224909 := bstep (se 3 (by rfl) ⟨24229670, by rfl⟩ : syracuseStep 129224909 = 48459341) B48459341
theorem B2486537 : Blo 1657528 2486537 := bstep (se 2 (by rfl) ⟨932451, by rfl⟩ : syracuseStep 2486537 = 1864903) B1864903
theorem B1659167 : Blo 1657528 1659167 := bstep (se 1 (by rfl) ⟨1244375, by rfl⟩ : syracuseStep 1659167 = 2488751) B2488751
theorem B2797915 : Blo 1657528 2797915 := bstep (se 1 (by rfl) ⟨2098436, by rfl⟩ : syracuseStep 2797915 = 4196873) B4196873
theorem B1659227 : Blo 1657528 1659227 := bstep (se 1 (by rfl) ⟨1244420, by rfl⟩ : syracuseStep 1659227 = 2488841) B2488841
theorem B9441643 : Blo 1657528 9441643 := bstep (se 1 (by rfl) ⟨7081232, by rfl⟩ : syracuseStep 9441643 = 14162465) B14162465
theorem B2486639 : Blo 1657528 2486639 := bstep (se 1 (by rfl) ⟨1864979, by rfl⟩ : syracuseStep 2486639 = 3729959) B3729959
theorem B1659247 : Blo 1657528 1659247 := bstep (se 1 (by rfl) ⟨1244435, by rfl⟩ : syracuseStep 1659247 = 2488871) B2488871
theorem B3150191 : Blo 1657528 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B32739719 : Blo 1657528 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B1659303 : Blo 1657528 1659303 := bstep (se 1 (by rfl) ⟨1244477, by rfl⟩ : syracuseStep 1659303 = 2488955) B2488955
theorem B80736749 : Blo 1657528 80736749 := bstep (se 3 (by rfl) ⟨15138140, by rfl⟩ : syracuseStep 80736749 = 30276281) B30276281
theorem B1659387 : Blo 1657528 1659387 := bstep (se 1 (by rfl) ⟨1244540, by rfl⟩ : syracuseStep 1659387 = 2489081) B2489081
theorem B5599745 : Blo 1657528 5599745 := bstep (se 2 (by rfl) ⟨2099904, by rfl⟩ : syracuseStep 5599745 = 4199809) B4199809
theorem B1659455 : Blo 1657528 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B2486855 : Blo 1657528 2486855 := bstep (se 1 (by rfl) ⟨1865141, by rfl⟩ : syracuseStep 2486855 = 3730283) B3730283
theorem B1659463 : Blo 1657528 1659463 := bstep (se 1 (by rfl) ⟨1244597, by rfl⟩ : syracuseStep 1659463 = 2489195) B2489195
theorem B4256329 : Blo 1657528 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B3732047 : Blo 1657528 3732047 := bstep (se 1 (by rfl) ⟨2799035, by rfl⟩ : syracuseStep 3732047 = 5598071) B5598071
theorem B23917153 : Blo 1657528 23917153 := bstep (se 2 (by rfl) ⟨8968932, by rfl⟩ : syracuseStep 23917153 = 17937865) B17937865
theorem B2486891 : Blo 1657528 2486891 := bstep (se 1 (by rfl) ⟨1865168, by rfl⟩ : syracuseStep 2486891 = 3730337) B3730337
theorem B7967447 : Blo 1657528 7967447 := bstep (se 1 (by rfl) ⟨5975585, by rfl⟩ : syracuseStep 7967447 = 11951171) B11951171
theorem B3732191 : Blo 1657528 3732191 := bstep (se 1 (by rfl) ⟨2799143, by rfl⟩ : syracuseStep 3732191 = 5598287) B5598287
theorem B2487119 : Blo 1657528 2487119 := bstep (se 1 (by rfl) ⟨1865339, by rfl⟩ : syracuseStep 2487119 = 3730679) B3730679
theorem B12587885 : Blo 1657528 12587885 := bstep (se 3 (by rfl) ⟨2360228, by rfl⟩ : syracuseStep 12587885 = 4720457) B4720457
theorem B4199323 : Blo 1657528 4199323 := bstep (se 1 (by rfl) ⟨3149492, by rfl⟩ : syracuseStep 4199323 = 6298985) B6298985
theorem B3986347 : Blo 1657528 3986347 := bstep (se 1 (by rfl) ⟨2989760, by rfl⟩ : syracuseStep 3986347 = 5979521) B5979521
theorem B3732443 : Blo 1657528 3732443 := bstep (se 1 (by rfl) ⟨2799332, by rfl⟩ : syracuseStep 3732443 = 5598665) B5598665
theorem B5600231 : Blo 1657528 5600231 := bstep (se 1 (by rfl) ⟨4200173, by rfl⟩ : syracuseStep 5600231 = 8400347) B8400347
theorem B3986423 : Blo 1657528 3986423 := bstep (se 1 (by rfl) ⟨2989817, by rfl⟩ : syracuseStep 3986423 = 5979635) B5979635
theorem B8967293 : Blo 1657528 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B3732623 : Blo 1657528 3732623 := bstep (se 1 (by rfl) ⟨2799467, by rfl⟩ : syracuseStep 3732623 = 5598935) B5598935
theorem B6296723 : Blo 1657528 6296723 := bstep (se 1 (by rfl) ⟨4722542, by rfl⟩ : syracuseStep 6296723 = 9445085) B9445085
theorem B2487515 : Blo 1657528 2487515 := bstep (se 1 (by rfl) ⟨1865636, by rfl⟩ : syracuseStep 2487515 = 3731273) B3731273
theorem B3732713 : Blo 1657528 3732713 := bstep (se 2 (by rfl) ⟨1399767, by rfl⟩ : syracuseStep 3732713 = 2799535) B2799535
theorem B3732767 : Blo 1657528 3732767 := bstep (se 1 (by rfl) ⟨2799575, by rfl⟩ : syracuseStep 3732767 = 5599151) B5599151
theorem B2798887 : Blo 1657528 2798887 := bstep (se 1 (by rfl) ⟨2099165, by rfl⟩ : syracuseStep 2798887 = 4198331) B4198331
theorem B10630439 : Blo 1657528 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B5600555 : Blo 1657528 5600555 := bstep (se 1 (by rfl) ⟨4200416, by rfl⟩ : syracuseStep 5600555 = 8400833) B8400833
theorem B5313887 : Blo 1657528 5313887 := bstep (se 1 (by rfl) ⟨3985415, by rfl⟩ : syracuseStep 5313887 = 7970831) B7970831
theorem B1865083 : Blo 1657528 1865083 := bstep (se 1 (by rfl) ⟨1398812, by rfl⟩ : syracuseStep 1865083 = 2797625) B2797625
theorem B2487689 : Blo 1657528 2487689 := bstep (se 2 (by rfl) ⟨932883, by rfl⟩ : syracuseStep 2487689 = 1865767) B1865767
theorem B5600825 : Blo 1657528 5600825 := bstep (se 2 (by rfl) ⟨2100309, by rfl⟩ : syracuseStep 5600825 = 4200619) B4200619
theorem B5314205 : Blo 1657528 5314205 := bstep (se 3 (by rfl) ⟨996413, by rfl⟩ : syracuseStep 5314205 = 1992827) B1992827
theorem B10081979 : Blo 1657528 10081979 := bstep (se 1 (by rfl) ⟨7561484, by rfl⟩ : syracuseStep 10081979 = 15122969) B15122969
theorem B2488043 : Blo 1657528 2488043 := bstep (se 1 (by rfl) ⟨1866032, by rfl⟩ : syracuseStep 2488043 = 3732065) B3732065
theorem B9443101 : Blo 1657528 9443101 := bstep (se 3 (by rfl) ⟨1770581, by rfl⟩ : syracuseStep 9443101 = 3541163) B3541163
theorem B3733289 : Blo 1657528 3733289 := bstep (se 2 (by rfl) ⟨1399983, by rfl⟩ : syracuseStep 3733289 = 2799967) B2799967
theorem B2799407 : Blo 1657528 2799407 := bstep (se 1 (by rfl) ⟨2099555, by rfl⟩ : syracuseStep 2799407 = 4199111) B4199111
theorem B1865551 : Blo 1657528 1865551 := bstep (se 1 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 1865551 = 2798327) B2798327
theorem B2488271 : Blo 1657528 2488271 := bstep (se 1 (by rfl) ⟨1866203, by rfl⟩ : syracuseStep 2488271 = 3732407) B3732407
theorem B4200457 : Blo 1657528 4200457 := bstep (se 2 (by rfl) ⟨1575171, by rfl⟩ : syracuseStep 4200457 = 3150343) B3150343
theorem B28326023 : Blo 1657528 28326023 := bstep (se 1 (by rfl) ⟨21244517, by rfl⟩ : syracuseStep 28326023 = 42489035) B42489035
theorem B1865947 : Blo 1657528 1865947 := bstep (se 1 (by rfl) ⟨1399460, by rfl⟩ : syracuseStep 1865947 = 2798921) B2798921
theorem B2488667 : Blo 1657528 2488667 := bstep (se 1 (by rfl) ⟨1866500, by rfl⟩ : syracuseStep 2488667 = 3733001) B3733001
theorem B45390331 : Blo 1657528 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B1866235 : Blo 1657528 1866235 := bstep (se 1 (by rfl) ⟨1399676, by rfl⟩ : syracuseStep 1866235 = 2799353) B2799353
theorem B7084583 : Blo 1657528 7084583 := bstep (se 1 (by rfl) ⟨5313437, by rfl⟩ : syracuseStep 7084583 = 10626875) B10626875
theorem B2488895 : Blo 1657528 2488895 := bstep (se 1 (by rfl) ⟨1866671, by rfl⟩ : syracuseStep 2488895 = 3733343) B3733343
theorem B7969387 : Blo 1657528 7969387 := bstep (se 1 (by rfl) ⟨5977040, by rfl⟩ : syracuseStep 7969387 = 11954081) B11954081
theorem B1866415 : Blo 1657528 1866415 := bstep (se 1 (by rfl) ⟨1399811, by rfl⟩ : syracuseStep 1866415 = 2799623) B2799623
theorem B2521783 : Blo 1657528 2521783 := bstep (se 1 (by rfl) ⟨1891337, by rfl⟩ : syracuseStep 2521783 = 3782675) B3782675
theorem B2489015 : Blo 1657528 2489015 := bstep (se 1 (by rfl) ⟨1866761, by rfl⟩ : syracuseStep 2489015 = 3733523) B3733523
theorem B10623899 : Blo 1657528 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B2489243 : Blo 1657528 2489243 := bstep (se 1 (by rfl) ⟨1866932, by rfl⟩ : syracuseStep 2489243 = 3733865) B3733865
theorem B1866703 : Blo 1657528 1866703 := bstep (se 1 (by rfl) ⟨1400027, by rfl⟩ : syracuseStep 1866703 = 2800055) B2800055
theorem B45382679 : Blo 1657528 45382679 := bstep (se 1 (by rfl) ⟨34037009, by rfl⟩ : syracuseStep 45382679 = 68074019) B68074019
theorem B7969907 : Blo 1657528 7969907 := bstep (se 1 (by rfl) ⟨5977430, by rfl⟩ : syracuseStep 7969907 = 11954861) B11954861
theorem B18889847 : Blo 1657528 18889847 := bstep (se 1 (by rfl) ⟨14167385, by rfl⟩ : syracuseStep 18889847 = 28334771) B28334771
theorem B2989199 : Blo 1657528 2989199 := bstep (se 1 (by rfl) ⟨2241899, by rfl⟩ : syracuseStep 2989199 = 4483799) B4483799
theorem B5594399 : Blo 1657528 5594399 := bstep (se 1 (by rfl) ⟨4195799, by rfl⟩ : syracuseStep 5594399 = 8391599) B8391599
theorem B8396297 : Blo 1657528 8396297 := bstep (se 2 (by rfl) ⟨3148611, by rfl⟩ : syracuseStep 8396297 = 6297223) B6297223
theorem B23305751 : Blo 1657528 23305751 := bstep (se 1 (by rfl) ⟨17479313, by rfl⟩ : syracuseStep 23305751 = 34958627) B34958627
theorem B24239731 : Blo 1657528 24239731 := bstep (se 1 (by rfl) ⟨18179798, by rfl⟩ : syracuseStep 24239731 = 36359597) B36359597
theorem B11353715 : Blo 1657528 11353715 := bstep (se 1 (by rfl) ⟨8515286, by rfl⟩ : syracuseStep 11353715 = 17030573) B17030573
theorem B6381359 : Blo 1657528 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B21250259 : Blo 1657528 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B31883543 : Blo 1657528 31883543 := bstep (se 1 (by rfl) ⟨23912657, by rfl⟩ : syracuseStep 31883543 = 47825315) B47825315
theorem B6300413 : Blo 1657528 6300413 := bstep (se 3 (by rfl) ⟨1181327, by rfl⟩ : syracuseStep 6300413 = 2362655) B2362655
theorem B10625849 : Blo 1657528 10625849 := bstep (se 2 (by rfl) ⟨3984693, by rfl⟩ : syracuseStep 10625849 = 7969387) B7969387
theorem B7086959 : Blo 1657528 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B4195759 : Blo 1657528 4195759 := bstep (se 1 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 4195759 = 6293639) B6293639
theorem B18884015 : Blo 1657528 18884015 := bstep (se 1 (by rfl) ⟨14163011, by rfl⟩ : syracuseStep 18884015 = 28326023) B28326023
theorem B14173811 : Blo 1657528 14173811 := bstep (se 1 (by rfl) ⟨10630358, by rfl⟩ : syracuseStep 14173811 = 21260717) B21260717
theorem B4196063 : Blo 1657528 4196063 := bstep (se 1 (by rfl) ⟨3147047, by rfl⟩ : syracuseStep 4196063 = 6294095) B6294095
theorem B68118353 : Blo 1657528 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B4720481 : Blo 1657528 4720481 := bstep (se 2 (by rfl) ⟨1770180, by rfl⟩ : syracuseStep 4720481 = 3540361) B3540361
theorem B30255119 : Blo 1657528 30255119 := bstep (se 1 (by rfl) ⟨22691339, by rfl⟩ : syracuseStep 30255119 = 45382679) B45382679
theorem B12593231 : Blo 1657528 12593231 := bstep (se 1 (by rfl) ⟨9444923, by rfl⟩ : syracuseStep 12593231 = 18889847) B18889847
theorem B1992799 : Blo 1657528 1992799 := bstep (se 1 (by rfl) ⟨1494599, by rfl⟩ : syracuseStep 1992799 = 2989199) B2989199
theorem B32319641 : Blo 1657528 32319641 := bstep (se 2 (by rfl) ⟨12119865, by rfl⟩ : syracuseStep 32319641 = 24239731) B24239731
theorem B1771675 : Blo 1657528 1771675 := bstep (se 1 (by rfl) ⟨1328756, by rfl⟩ : syracuseStep 1771675 = 2657513) B2657513
theorem B3729599 : Blo 1657528 3729599 := bstep (se 1 (by rfl) ⟨2797199, by rfl⟩ : syracuseStep 3729599 = 5594399) B5594399
theorem B2361641 : Blo 1657528 2361641 := bstep (se 2 (by rfl) ⟨885615, by rfl⟩ : syracuseStep 2361641 = 1771231) B1771231
theorem B6293807 : Blo 1657528 6293807 := bstep (se 1 (by rfl) ⟨4720355, by rfl⟩ : syracuseStep 6293807 = 9440711) B9440711
theorem B17926447 : Blo 1657528 17926447 := bstep (se 1 (by rfl) ⟨13444835, by rfl⟩ : syracuseStep 17926447 = 26889671) B26889671
theorem B5597531 : Blo 1657528 5597531 := bstep (se 1 (by rfl) ⟨4198148, by rfl⟩ : syracuseStep 5597531 = 8396297) B8396297
theorem B28330397 : Blo 1657528 28330397 := bstep (se 3 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 28330397 = 10623899) B10623899
theorem B4254239 : Blo 1657528 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B5597801 : Blo 1657528 5597801 := bstep (se 2 (by rfl) ⟨2099175, by rfl⟩ : syracuseStep 5597801 = 4198351) B4198351
theorem B4721323 : Blo 1657528 4721323 := bstep (se 1 (by rfl) ⟨3540992, by rfl⟩ : syracuseStep 4721323 = 7081985) B7081985
theorem B86149939 : Blo 1657528 86149939 := bstep (se 1 (by rfl) ⟨64612454, by rfl⟩ : syracuseStep 86149939 = 129224909) B129224909
theorem B6728503 : Blo 1657528 6728503 := bstep (se 1 (by rfl) ⟨5046377, by rfl⟩ : syracuseStep 6728503 = 10092755) B10092755
theorem B1657691 : Blo 1657528 1657691 := bstep (se 1 (by rfl) ⟨1243268, by rfl⟩ : syracuseStep 1657691 = 2486537) B2486537
theorem B1657759 : Blo 1657528 1657759 := bstep (se 1 (by rfl) ⟨1243319, by rfl⟩ : syracuseStep 1657759 = 2486639) B2486639
theorem B53824499 : Blo 1657528 53824499 := bstep (se 1 (by rfl) ⟨40368374, by rfl⟩ : syracuseStep 53824499 = 80736749) B80736749
theorem B1657903 : Blo 1657528 1657903 := bstep (se 1 (by rfl) ⟨1243427, by rfl⟩ : syracuseStep 1657903 = 2486855) B2486855
theorem B1657927 : Blo 1657528 1657927 := bstep (se 1 (by rfl) ⟨1243445, by rfl⟩ : syracuseStep 1657927 = 2486891) B2486891
theorem B5975137 : Blo 1657528 5975137 := bstep (se 2 (by rfl) ⟨2240676, by rfl⟩ : syracuseStep 5975137 = 4481353) B4481353
theorem B3730553 : Blo 1657528 3730553 := bstep (se 2 (by rfl) ⟨1398957, by rfl⟩ : syracuseStep 3730553 = 2797915) B2797915
theorem B5311631 : Blo 1657528 5311631 := bstep (se 1 (by rfl) ⟨3983723, by rfl⟩ : syracuseStep 5311631 = 7967447) B7967447
theorem B1658079 : Blo 1657528 1658079 := bstep (se 1 (by rfl) ⟨1243559, by rfl⟩ : syracuseStep 1658079 = 2487119) B2487119
theorem B8391923 : Blo 1657528 8391923 := bstep (se 1 (by rfl) ⟨6293942, by rfl⟩ : syracuseStep 8391923 = 12587885) B12587885
theorem B2657615 : Blo 1657528 2657615 := bstep (se 1 (by rfl) ⟨1993211, by rfl⟩ : syracuseStep 2657615 = 3986423) B3986423
theorem B9571753 : Blo 1657528 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B4197815 : Blo 1657528 4197815 := bstep (se 1 (by rfl) ⟨3148361, by rfl⟩ : syracuseStep 4197815 = 6296723) B6296723
theorem B262016441 : Blo 1657528 262016441 := bstep (se 2 (by rfl) ⟨98256165, by rfl⟩ : syracuseStep 262016441 = 196512331) B196512331
theorem B1658343 : Blo 1657528 1658343 := bstep (se 1 (by rfl) ⟨1243757, by rfl⟩ : syracuseStep 1658343 = 2487515) B2487515
theorem B3542591 : Blo 1657528 3542591 := bstep (se 1 (by rfl) ⟨2656943, by rfl⟩ : syracuseStep 3542591 = 5313887) B5313887
theorem B1658459 : Blo 1657528 1658459 := bstep (se 1 (by rfl) ⟨1243844, by rfl⟩ : syracuseStep 1658459 = 2487689) B2487689
theorem B5598827 : Blo 1657528 5598827 := bstep (se 1 (by rfl) ⟨4199120, by rfl⟩ : syracuseStep 5598827 = 8398241) B8398241
theorem B8400509 : Blo 1657528 8400509 := bstep (se 3 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 8400509 = 3150191) B3150191
theorem B3731219 : Blo 1657528 3731219 := bstep (se 1 (by rfl) ⟨2798414, by rfl⟩ : syracuseStep 3731219 = 5596829) B5596829
theorem B6721319 : Blo 1657528 6721319 := bstep (se 1 (by rfl) ⟨5040989, by rfl⟩ : syracuseStep 6721319 = 10081979) B10081979
theorem B1658695 : Blo 1657528 1658695 := bstep (se 1 (by rfl) ⟨1244021, by rfl⟩ : syracuseStep 1658695 = 2488043) B2488043
theorem B4722553 : Blo 1657528 4722553 := bstep (se 2 (by rfl) ⟨1770957, by rfl⟩ : syracuseStep 4722553 = 3541915) B3541915
theorem B5599097 : Blo 1657528 5599097 := bstep (se 2 (by rfl) ⟨2099661, by rfl⟩ : syracuseStep 5599097 = 4199323) B4199323
theorem B2797483 : Blo 1657528 2797483 := bstep (se 1 (by rfl) ⟨2098112, by rfl⟩ : syracuseStep 2797483 = 4196225) B4196225
theorem B1658847 : Blo 1657528 1658847 := bstep (se 1 (by rfl) ⟨1244135, by rfl⟩ : syracuseStep 1658847 = 2488271) B2488271
theorem B9449459 : Blo 1657528 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B3731579 : Blo 1657528 3731579 := bstep (se 1 (by rfl) ⟨2798684, by rfl⟩ : syracuseStep 3731579 = 5597369) B5597369
theorem B5599421 : Blo 1657528 5599421 := bstep (se 3 (by rfl) ⟨1049891, by rfl⟩ : syracuseStep 5599421 = 2099783) B2099783
theorem B2797787 : Blo 1657528 2797787 := bstep (se 1 (by rfl) ⟨2098340, by rfl⟩ : syracuseStep 2797787 = 4196681) B4196681
theorem B1659111 : Blo 1657528 1659111 := bstep (se 1 (by rfl) ⟨1244333, by rfl⟩ : syracuseStep 1659111 = 2488667) B2488667
theorem B4722941 : Blo 1657528 4722941 := bstep (se 3 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 4722941 = 1771103) B1771103
theorem B4723055 : Blo 1657528 4723055 := bstep (se 1 (by rfl) ⟨3542291, by rfl⟩ : syracuseStep 4723055 = 7084583) B7084583
theorem B1659263 : Blo 1657528 1659263 := bstep (se 1 (by rfl) ⟨1244447, by rfl⟩ : syracuseStep 1659263 = 2488895) B2488895
theorem B3731849 : Blo 1657528 3731849 := bstep (se 2 (by rfl) ⟨1399443, by rfl⟩ : syracuseStep 3731849 = 2798887) B2798887
theorem B8401319 : Blo 1657528 8401319 := bstep (se 1 (by rfl) ⟨6300989, by rfl⟩ : syracuseStep 8401319 = 12601979) B12601979
theorem B2798023 : Blo 1657528 2798023 := bstep (se 1 (by rfl) ⟨2098517, by rfl⟩ : syracuseStep 2798023 = 4197035) B4197035
theorem B2486735 : Blo 1657528 2486735 := bstep (se 1 (by rfl) ⟨1865051, by rfl⟩ : syracuseStep 2486735 = 3730103) B3730103
theorem B1659343 : Blo 1657528 1659343 := bstep (se 1 (by rfl) ⟨1244507, by rfl⟩ : syracuseStep 1659343 = 2489015) B2489015
theorem B2798057 : Blo 1657528 2798057 := bstep (se 2 (by rfl) ⟨1049271, by rfl⟩ : syracuseStep 2798057 = 2098543) B2098543
theorem B2486777 : Blo 1657528 2486777 := bstep (se 2 (by rfl) ⟨932541, by rfl⟩ : syracuseStep 2486777 = 1865083) B1865083
theorem B2486879 : Blo 1657528 2486879 := bstep (se 1 (by rfl) ⟨1865159, by rfl⟩ : syracuseStep 2486879 = 3730319) B3730319
theorem B1659495 : Blo 1657528 1659495 := bstep (se 1 (by rfl) ⟨1244621, by rfl⟩ : syracuseStep 1659495 = 2489243) B2489243
theorem B5313271 : Blo 1657528 5313271 := bstep (se 1 (by rfl) ⟨3984953, by rfl⟩ : syracuseStep 5313271 = 7969907) B7969907
theorem B15537167 : Blo 1657528 15537167 := bstep (se 1 (by rfl) ⟨11652875, by rfl⟩ : syracuseStep 15537167 = 23305751) B23305751
theorem B2487359 : Blo 1657528 2487359 := bstep (se 1 (by rfl) ⟨1865519, by rfl⟩ : syracuseStep 2487359 = 3731039) B3731039
theorem B12112973 : Blo 1657528 12112973 := bstep (se 3 (by rfl) ⟨2271182, by rfl⟩ : syracuseStep 12112973 = 4542365) B4542365
theorem B2487401 : Blo 1657528 2487401 := bstep (se 2 (by rfl) ⟨932775, by rfl⟩ : syracuseStep 2487401 = 1865551) B1865551
theorem B3732587 : Blo 1657528 3732587 := bstep (se 1 (by rfl) ⟨2799440, by rfl⟩ : syracuseStep 3732587 = 5598881) B5598881
theorem B2487503 : Blo 1657528 2487503 := bstep (se 1 (by rfl) ⟨1865627, by rfl⟩ : syracuseStep 2487503 = 3731255) B3731255
theorem B5600609 : Blo 1657528 5600609 := bstep (se 2 (by rfl) ⟨2100228, by rfl⟩ : syracuseStep 5600609 = 4200457) B4200457
theorem B20166043 : Blo 1657528 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B2487707 : Blo 1657528 2487707 := bstep (se 1 (by rfl) ⟨1865780, by rfl⟩ : syracuseStep 2487707 = 3731561) B3731561
theorem B2487929 : Blo 1657528 2487929 := bstep (se 2 (by rfl) ⟨932973, by rfl⟩ : syracuseStep 2487929 = 1865947) B1865947
theorem B3733163 : Blo 1657528 3733163 := bstep (se 1 (by rfl) ⟨2799872, by rfl⟩ : syracuseStep 3733163 = 5599745) B5599745
theorem B2488031 : Blo 1657528 2488031 := bstep (se 1 (by rfl) ⟨1866023, by rfl⟩ : syracuseStep 2488031 = 3732047) B3732047
theorem B12588857 : Blo 1657528 12588857 := bstep (se 2 (by rfl) ⟨4720821, by rfl⟩ : syracuseStep 12588857 = 9441643) B9441643
theorem B2488127 : Blo 1657528 2488127 := bstep (se 1 (by rfl) ⟨1866095, by rfl⟩ : syracuseStep 2488127 = 3732191) B3732191
theorem B10622927 : Blo 1657528 10622927 := bstep (se 1 (by rfl) ⟨7967195, by rfl⟩ : syracuseStep 10622927 = 15934391) B15934391
theorem B4200407 : Blo 1657528 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B2488295 : Blo 1657528 2488295 := bstep (se 1 (by rfl) ⟨1866221, by rfl⟩ : syracuseStep 2488295 = 3732443) B3732443
theorem B3733487 : Blo 1657528 3733487 := bstep (se 1 (by rfl) ⟨2800115, by rfl⟩ : syracuseStep 3733487 = 5600231) B5600231
theorem B2988023 : Blo 1657528 2988023 := bstep (se 1 (by rfl) ⟨2241017, by rfl⟩ : syracuseStep 2988023 = 4482035) B4482035
theorem B60520441 : Blo 1657528 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B2488313 : Blo 1657528 2488313 := bstep (se 2 (by rfl) ⟨933117, by rfl⟩ : syracuseStep 2488313 = 1866235) B1866235
theorem B5978195 : Blo 1657528 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B5314643 : Blo 1657528 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B6297695 : Blo 1657528 6297695 := bstep (se 1 (by rfl) ⟨4723271, by rfl⟩ : syracuseStep 6297695 = 9446543) B9446543
theorem B2488415 : Blo 1657528 2488415 := bstep (se 1 (by rfl) ⟨1866311, by rfl⟩ : syracuseStep 2488415 = 3732623) B3732623
theorem B5675105 : Blo 1657528 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B4724831 : Blo 1657528 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B31889537 : Blo 1657528 31889537 := bstep (se 2 (by rfl) ⟨11958576, by rfl⟩ : syracuseStep 31889537 = 23917153) B23917153
theorem B2488475 : Blo 1657528 2488475 := bstep (se 1 (by rfl) ⟨1866356, by rfl⟩ : syracuseStep 2488475 = 3732713) B3732713
theorem B2488511 : Blo 1657528 2488511 := bstep (se 1 (by rfl) ⟨1866383, by rfl⟩ : syracuseStep 2488511 = 3732767) B3732767
theorem B3733703 : Blo 1657528 3733703 := bstep (se 1 (by rfl) ⟨2800277, by rfl⟩ : syracuseStep 3733703 = 5600555) B5600555
theorem B2488553 : Blo 1657528 2488553 := bstep (se 2 (by rfl) ⟨933207, by rfl⟩ : syracuseStep 2488553 = 1866415) B1866415
theorem B13449509 : Blo 1657528 13449509 := bstep (se 4 (by rfl) ⟨1260891, by rfl⟩ : syracuseStep 13449509 = 2521783) B2521783
theorem B2799913 : Blo 1657528 2799913 := bstep (se 2 (by rfl) ⟨1049967, by rfl⟩ : syracuseStep 2799913 = 2099935) B2099935
theorem B11958637 : Blo 1657528 11958637 := bstep (se 3 (by rfl) ⟨2242244, by rfl⟩ : syracuseStep 11958637 = 4484489) B4484489
theorem B3733883 : Blo 1657528 3733883 := bstep (se 1 (by rfl) ⟨2800412, by rfl⟩ : syracuseStep 3733883 = 5600825) B5600825
theorem B2488859 : Blo 1657528 2488859 := bstep (se 1 (by rfl) ⟨1866644, by rfl⟩ : syracuseStep 2488859 = 3733289) B3733289
theorem B1866271 : Blo 1657528 1866271 := bstep (se 1 (by rfl) ⟨1399703, by rfl⟩ : syracuseStep 1866271 = 2799407) B2799407
theorem B58235435 : Blo 1657528 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B5315129 : Blo 1657528 5315129 := bstep (se 2 (by rfl) ⟨1993173, by rfl⟩ : syracuseStep 5315129 = 3986347) B3986347
theorem B2488937 : Blo 1657528 2488937 := bstep (se 2 (by rfl) ⟨933351, by rfl⟩ : syracuseStep 2488937 = 1866703) B1866703
theorem B2874043 : Blo 1657528 2874043 := bstep (se 1 (by rfl) ⟨2155532, by rfl⟩ : syracuseStep 2874043 = 4311065) B4311065
theorem B349223669 : Blo 1657528 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B5594183 : Blo 1657528 5594183 := bstep (se 1 (by rfl) ⟨4195637, by rfl⟩ : syracuseStep 5594183 = 8391275) B8391275
theorem B14171213 : Blo 1657528 14171213 := bstep (se 3 (by rfl) ⟨2657102, by rfl⟩ : syracuseStep 14171213 = 5314205) B5314205
theorem B5594237 : Blo 1657528 5594237 := bstep (se 3 (by rfl) ⟨1048919, by rfl⟩ : syracuseStep 5594237 = 2097839) B2097839
theorem B44260499 : Blo 1657528 44260499 := bstep (se 1 (by rfl) ⟨33195374, by rfl⟩ : syracuseStep 44260499 = 66390749) B66390749
theorem B5594507 : Blo 1657528 5594507 := bstep (se 1 (by rfl) ⟨4195880, by rfl⟩ : syracuseStep 5594507 = 8391761) B8391761
theorem B11345291 : Blo 1657528 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B2989523 : Blo 1657528 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B12115493 : Blo 1657528 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B12590801 : Blo 1657528 12590801 := bstep (se 2 (by rfl) ⟨4721550, by rfl⟩ : syracuseStep 12590801 = 9443101) B9443101
theorem B7569143 : Blo 1657528 7569143 := bstep (se 1 (by rfl) ⟨5676857, by rfl⟩ : syracuseStep 7569143 = 11353715) B11353715
theorem B10624925 : Blo 1657528 10624925 := bstep (se 3 (by rfl) ⟨1992173, by rfl⟩ : syracuseStep 10624925 = 3984347) B3984347
theorem B12599549 : Blo 1657528 12599549 := bstep (se 3 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 12599549 = 4724831) B4724831
theorem B8971337 : Blo 1657528 8971337 := bstep (se 2 (by rfl) ⟨3364251, by rfl⟩ : syracuseStep 8971337 = 6728503) B6728503
theorem B3146987 : Blo 1657528 3146987 := bstep (se 1 (by rfl) ⟨2360240, by rfl⟩ : syracuseStep 3146987 = 4720481) B4720481
theorem B20170079 : Blo 1657528 20170079 := bstep (se 1 (by rfl) ⟨15127559, by rfl⟩ : syracuseStep 20170079 = 30255119) B30255119
theorem B21259691 : Blo 1657528 21259691 := bstep (se 1 (by rfl) ⟨15944768, by rfl⟩ : syracuseStep 21259691 = 31889537) B31889537
theorem B21546427 : Blo 1657528 21546427 := bstep (se 1 (by rfl) ⟨16159820, by rfl⟩ : syracuseStep 21546427 = 32319641) B32319641
theorem B4195871 : Blo 1657528 4195871 := bstep (se 1 (by rfl) ⟨3146903, by rfl⟩ : syracuseStep 4195871 = 6293807) B6293807
theorem B38823623 : Blo 1657528 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B26888057 : Blo 1657528 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B35882999 : Blo 1657528 35882999 := bstep (se 1 (by rfl) ⟨26912249, by rfl⟩ : syracuseStep 35882999 = 53824499) B53824499
theorem B3729455 : Blo 1657528 3729455 := bstep (se 1 (by rfl) ⟨2797091, by rfl⟩ : syracuseStep 3729455 = 5594183) B5594183
theorem B9447475 : Blo 1657528 9447475 := bstep (se 1 (by rfl) ⟨7085606, by rfl⟩ : syracuseStep 9447475 = 14171213) B14171213
theorem B3729491 : Blo 1657528 3729491 := bstep (se 1 (by rfl) ⟨2797118, by rfl⟩ : syracuseStep 3729491 = 5594237) B5594237
theorem B3541087 : Blo 1657528 3541087 := bstep (se 1 (by rfl) ⟨2655815, by rfl⟩ : syracuseStep 3541087 = 5311631) B5311631
theorem B3729671 : Blo 1657528 3729671 := bstep (se 1 (by rfl) ⟨2797253, by rfl⟩ : syracuseStep 3729671 = 5594507) B5594507
theorem B7563527 : Blo 1657528 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B1993015 : Blo 1657528 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B2361727 : Blo 1657528 2361727 := bstep (se 1 (by rfl) ⟨1771295, by rfl⟩ : syracuseStep 2361727 = 3542591) B3542591
theorem B3729977 : Blo 1657528 3729977 := bstep (se 2 (by rfl) ⟨1398741, by rfl⟩ : syracuseStep 3729977 = 2797483) B2797483
theorem B80693921 : Blo 1657528 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B2657065 : Blo 1657528 2657065 := bstep (se 2 (by rfl) ⟨996399, by rfl⟩ : syracuseStep 2657065 = 1992799) B1992799
theorem B14166839 : Blo 1657528 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B3148627 : Blo 1657528 3148627 := bstep (se 1 (by rfl) ⟨2361470, by rfl⟩ : syracuseStep 3148627 = 4722941) B4722941
theorem B3148703 : Blo 1657528 3148703 := bstep (se 1 (by rfl) ⟨2361527, by rfl⟩ : syracuseStep 3148703 = 4723055) B4723055
theorem B15133613 : Blo 1657528 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B1657823 : Blo 1657528 1657823 := bstep (se 1 (by rfl) ⟨1243367, by rfl⟩ : syracuseStep 1657823 = 2486735) B2486735
theorem B1657851 : Blo 1657528 1657851 := bstep (se 1 (by rfl) ⟨1243388, by rfl⟩ : syracuseStep 1657851 = 2486777) B2486777
theorem B1657919 : Blo 1657528 1657919 := bstep (se 1 (by rfl) ⟨1243439, by rfl⟩ : syracuseStep 1657919 = 2486879) B2486879
theorem B15944849 : Blo 1657528 15944849 := bstep (se 2 (by rfl) ⟨5979318, by rfl⟩ : syracuseStep 15944849 = 11958637) B11958637
theorem B3730697 : Blo 1657528 3730697 := bstep (se 2 (by rfl) ⟨1399011, by rfl⟩ : syracuseStep 3730697 = 2798023) B2798023
theorem B10358111 : Blo 1657528 10358111 := bstep (se 1 (by rfl) ⟨7768583, by rfl⟩ : syracuseStep 10358111 = 15537167) B15537167
theorem B1658239 : Blo 1657528 1658239 := bstep (se 1 (by rfl) ⟨1243679, by rfl⟩ : syracuseStep 1658239 = 2487359) B2487359
theorem B1658267 : Blo 1657528 1658267 := bstep (se 1 (by rfl) ⟨1243700, by rfl⟩ : syracuseStep 1658267 = 2487401) B2487401
theorem B1658335 : Blo 1657528 1658335 := bstep (se 1 (by rfl) ⟨1243751, by rfl⟩ : syracuseStep 1658335 = 2487503) B2487503
theorem B9448933 : Blo 1657528 9448933 := bstep (se 4 (by rfl) ⟨885837, by rfl⟩ : syracuseStep 9448933 = 1771675) B1771675
theorem B28347893 : Blo 1657528 28347893 := bstep (se 5 (by rfl) ⟨1328807, by rfl⟩ : syracuseStep 28347893 = 2657615) B2657615
theorem B6295097 : Blo 1657528 6295097 := bstep (se 2 (by rfl) ⟨2360661, by rfl⟩ : syracuseStep 6295097 = 4721323) B4721323
theorem B1658471 : Blo 1657528 1658471 := bstep (se 1 (by rfl) ⟨1243853, by rfl⟩ : syracuseStep 1658471 = 2487707) B2487707
theorem B9449207 : Blo 1657528 9449207 := bstep (se 1 (by rfl) ⟨7086905, by rfl⟩ : syracuseStep 9449207 = 14173811) B14173811
theorem B1658619 : Blo 1657528 1658619 := bstep (se 1 (by rfl) ⟨1243964, by rfl⟩ : syracuseStep 1658619 = 2487929) B2487929
theorem B2797375 : Blo 1657528 2797375 := bstep (se 1 (by rfl) ⟨2098031, by rfl⟩ : syracuseStep 2797375 = 4196063) B4196063
theorem B1658687 : Blo 1657528 1658687 := bstep (se 1 (by rfl) ⟨1244015, by rfl⟩ : syracuseStep 1658687 = 2488031) B2488031
theorem B8392571 : Blo 1657528 8392571 := bstep (se 1 (by rfl) ⟨6294428, by rfl⟩ : syracuseStep 8392571 = 12588857) B12588857
theorem B1658751 : Blo 1657528 1658751 := bstep (se 1 (by rfl) ⟨1244063, by rfl⟩ : syracuseStep 1658751 = 2488127) B2488127
theorem B45412235 : Blo 1657528 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B7081951 : Blo 1657528 7081951 := bstep (se 1 (by rfl) ⟨5311463, by rfl⟩ : syracuseStep 7081951 = 10622927) B10622927
theorem B1658863 : Blo 1657528 1658863 := bstep (se 1 (by rfl) ⟨1244147, by rfl⟩ : syracuseStep 1658863 = 2488295) B2488295
theorem B1658875 : Blo 1657528 1658875 := bstep (se 1 (by rfl) ⟨1244156, by rfl⟩ : syracuseStep 1658875 = 2488313) B2488313
theorem B3985463 : Blo 1657528 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B3543095 : Blo 1657528 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B4198463 : Blo 1657528 4198463 := bstep (se 1 (by rfl) ⟨3148847, by rfl⟩ : syracuseStep 4198463 = 6297695) B6297695
theorem B1658943 : Blo 1657528 1658943 := bstep (se 1 (by rfl) ⟨1244207, by rfl⟩ : syracuseStep 1658943 = 2488415) B2488415
theorem B1658983 : Blo 1657528 1658983 := bstep (se 1 (by rfl) ⟨1244237, by rfl⟩ : syracuseStep 1658983 = 2488475) B2488475
theorem B2486399 : Blo 1657528 2486399 := bstep (se 1 (by rfl) ⟨1864799, by rfl⟩ : syracuseStep 2486399 = 3729599) B3729599
theorem B1659007 : Blo 1657528 1659007 := bstep (se 1 (by rfl) ⟨1244255, by rfl⟩ : syracuseStep 1659007 = 2488511) B2488511
theorem B7966849 : Blo 1657528 7966849 := bstep (se 2 (by rfl) ⟨2987568, by rfl⟩ : syracuseStep 7966849 = 5975137) B5975137
theorem B1659035 : Blo 1657528 1659035 := bstep (se 1 (by rfl) ⟨1244276, by rfl⟩ : syracuseStep 1659035 = 2488553) B2488553
theorem B8966339 : Blo 1657528 8966339 := bstep (se 1 (by rfl) ⟨6724754, by rfl⟩ : syracuseStep 8966339 = 13449509) B13449509
theorem B3731687 : Blo 1657528 3731687 := bstep (se 1 (by rfl) ⟨2798765, by rfl⟩ : syracuseStep 3731687 = 5597531) B5597531
theorem B18886931 : Blo 1657528 18886931 := bstep (se 1 (by rfl) ⟨14165198, by rfl⟩ : syracuseStep 18886931 = 28330397) B28330397
theorem B1659239 : Blo 1657528 1659239 := bstep (se 1 (by rfl) ⟨1244429, by rfl⟩ : syracuseStep 1659239 = 2488859) B2488859
theorem B3543419 : Blo 1657528 3543419 := bstep (se 1 (by rfl) ⟨2657564, by rfl⟩ : syracuseStep 3543419 = 5315129) B5315129
theorem B3731867 : Blo 1657528 3731867 := bstep (se 1 (by rfl) ⟨2798900, by rfl⟩ : syracuseStep 3731867 = 5597801) B5597801
theorem B1659291 : Blo 1657528 1659291 := bstep (se 1 (by rfl) ⟨1244468, by rfl⟩ : syracuseStep 1659291 = 2488937) B2488937
theorem B2487035 : Blo 1657528 2487035 := bstep (se 1 (by rfl) ⟨1865276, by rfl⟩ : syracuseStep 2487035 = 3730553) B3730553
theorem B51049349 : Blo 1657528 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B2798543 : Blo 1657528 2798543 := bstep (se 1 (by rfl) ⟨2098907, by rfl⟩ : syracuseStep 2798543 = 4197815) B4197815
theorem B3732551 : Blo 1657528 3732551 := bstep (se 1 (by rfl) ⟨2799413, by rfl⟩ : syracuseStep 3732551 = 5598827) B5598827
theorem B5600339 : Blo 1657528 5600339 := bstep (se 1 (by rfl) ⟨4200254, by rfl⟩ : syracuseStep 5600339 = 8400509) B8400509
theorem B8393867 : Blo 1657528 8393867 := bstep (se 1 (by rfl) ⟨6295400, by rfl⟩ : syracuseStep 8393867 = 12590801) B12590801
theorem B6296737 : Blo 1657528 6296737 := bstep (se 2 (by rfl) ⟨2361276, by rfl⟩ : syracuseStep 6296737 = 4722553) B4722553
theorem B2487479 : Blo 1657528 2487479 := bstep (se 1 (by rfl) ⟨1865609, by rfl⟩ : syracuseStep 2487479 = 3731219) B3731219
theorem B3732731 : Blo 1657528 3732731 := bstep (se 1 (by rfl) ⟨2799548, by rfl⟩ : syracuseStep 3732731 = 5599097) B5599097
theorem B7083283 : Blo 1657528 7083283 := bstep (se 1 (by rfl) ⟨5312462, by rfl⟩ : syracuseStep 7083283 = 10624925) B10624925
theorem B7968061 : Blo 1657528 7968061 := bstep (se 3 (by rfl) ⟨1494011, by rfl⟩ : syracuseStep 7968061 = 2988023) B2988023
theorem B2487719 : Blo 1657528 2487719 := bstep (se 1 (by rfl) ⟨1865789, by rfl⟩ : syracuseStep 2487719 = 3731579) B3731579
theorem B3732947 : Blo 1657528 3732947 := bstep (se 1 (by rfl) ⟨2799710, by rfl⟩ : syracuseStep 3732947 = 5599421) B5599421
theorem B1865191 : Blo 1657528 1865191 := bstep (se 1 (by rfl) ⟨1398893, by rfl⟩ : syracuseStep 1865191 = 2797787) B2797787
theorem B21255695 : Blo 1657528 21255695 := bstep (se 1 (by rfl) ⟨15941771, by rfl⟩ : syracuseStep 21255695 = 31883543) B31883543
theorem B2487899 : Blo 1657528 2487899 := bstep (se 1 (by rfl) ⟨1865924, by rfl⟩ : syracuseStep 2487899 = 3731849) B3731849
theorem B5600879 : Blo 1657528 5600879 := bstep (se 1 (by rfl) ⟨4200659, by rfl⟩ : syracuseStep 5600879 = 8401319) B8401319
theorem B1865371 : Blo 1657528 1865371 := bstep (se 1 (by rfl) ⟨1399028, by rfl⟩ : syracuseStep 1865371 = 2798057) B2798057
theorem B3733217 : Blo 1657528 3733217 := bstep (se 2 (by rfl) ⟨1399956, by rfl⟩ : syracuseStep 3733217 = 2799913) B2799913
theorem B23901929 : Blo 1657528 23901929 := bstep (se 2 (by rfl) ⟨8963223, by rfl⟩ : syracuseStep 23901929 = 17926447) B17926447
theorem B4200275 : Blo 1657528 4200275 := bstep (se 1 (by rfl) ⟨3150206, by rfl⟩ : syracuseStep 4200275 = 6300413) B6300413
theorem B7083899 : Blo 1657528 7083899 := bstep (se 1 (by rfl) ⟨5312924, by rfl⟩ : syracuseStep 7083899 = 10625849) B10625849
theorem B4724639 : Blo 1657528 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B2488361 : Blo 1657528 2488361 := bstep (se 2 (by rfl) ⟨933135, by rfl⟩ : syracuseStep 2488361 = 1866271) B1866271
theorem B8075315 : Blo 1657528 8075315 := bstep (se 1 (by rfl) ⟨6056486, by rfl⟩ : syracuseStep 8075315 = 12112973) B12112973
theorem B2488391 : Blo 1657528 2488391 := bstep (se 1 (by rfl) ⟨1866293, by rfl⟩ : syracuseStep 2488391 = 3732587) B3732587
theorem B6297709 : Blo 1657528 6297709 := bstep (se 3 (by rfl) ⟨1180820, by rfl⟩ : syracuseStep 6297709 = 2361641) B2361641
theorem B3733739 : Blo 1657528 3733739 := bstep (se 1 (by rfl) ⟨2800304, by rfl⟩ : syracuseStep 3733739 = 5600609) B5600609
theorem B3832057 : Blo 1657528 3832057 := bstep (se 2 (by rfl) ⟨1437021, by rfl⟩ : syracuseStep 3832057 = 2874043) B2874043
theorem B12589343 : Blo 1657528 12589343 := bstep (se 1 (by rfl) ⟨9442007, by rfl⟩ : syracuseStep 12589343 = 18884015) B18884015
theorem B7084361 : Blo 1657528 7084361 := bstep (se 2 (by rfl) ⟨2656635, by rfl⟩ : syracuseStep 7084361 = 5313271) B5313271
theorem B114866585 : Blo 1657528 114866585 := bstep (se 2 (by rfl) ⟨43074969, by rfl⟩ : syracuseStep 114866585 = 86149939) B86149939
theorem B2488775 : Blo 1657528 2488775 := bstep (se 1 (by rfl) ⟨1866581, by rfl⟩ : syracuseStep 2488775 = 3733163) B3733163
theorem B2800271 : Blo 1657528 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B2488991 : Blo 1657528 2488991 := bstep (se 1 (by rfl) ⟨1866743, by rfl⟩ : syracuseStep 2488991 = 3733487) B3733487
theorem B8395487 : Blo 1657528 8395487 := bstep (se 1 (by rfl) ⟨6296615, by rfl⟩ : syracuseStep 8395487 = 12593231) B12593231
theorem B11344637 : Blo 1657528 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2489135 : Blo 1657528 2489135 := bstep (se 1 (by rfl) ⟨1866851, by rfl⟩ : syracuseStep 2489135 = 3733703) B3733703
theorem B2489255 : Blo 1657528 2489255 := bstep (se 1 (by rfl) ⟨1866941, by rfl⟩ : syracuseStep 2489255 = 3733883) B3733883
theorem B232815779 : Blo 1657528 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B5594345 : Blo 1657528 5594345 := bstep (se 2 (by rfl) ⟨2097879, by rfl⟩ : syracuseStep 5594345 = 4195759) B4195759
theorem B29506999 : Blo 1657528 29506999 := bstep (se 1 (by rfl) ⟨22130249, by rfl⟩ : syracuseStep 29506999 = 44260499) B44260499
theorem B5594615 : Blo 1657528 5594615 := bstep (se 1 (by rfl) ⟨4195961, by rfl⟩ : syracuseStep 5594615 = 8391923) B8391923
theorem B174677627 : Blo 1657528 174677627 := bstep (se 1 (by rfl) ⟨131008220, by rfl⟩ : syracuseStep 174677627 = 262016441) B262016441
theorem B8076995 : Blo 1657528 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B5046095 : Blo 1657528 5046095 := bstep (se 1 (by rfl) ⟨3784571, by rfl⟩ : syracuseStep 5046095 = 7569143) B7569143
theorem B4480879 : Blo 1657528 4480879 := bstep (se 1 (by rfl) ⟨3360659, by rfl⟩ : syracuseStep 4480879 = 6721319) B6721319
theorem B6299639 : Blo 1657528 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B8396945 : Blo 1657528 8396945 := bstep (se 2 (by rfl) ⟨3148854, by rfl⟩ : syracuseStep 8396945 = 6297709) B6297709
theorem B12591287 : Blo 1657528 12591287 := bstep (se 1 (by rfl) ⟨9443465, by rfl⟩ : syracuseStep 12591287 = 18886931) B18886931
theorem B5980891 : Blo 1657528 5980891 := bstep (se 1 (by rfl) ⟨4485668, by rfl⟩ : syracuseStep 5980891 = 8971337) B8971337
theorem B5595911 : Blo 1657528 5595911 := bstep (se 1 (by rfl) ⟨4196933, by rfl⟩ : syracuseStep 5595911 = 8393867) B8393867
theorem B2097991 : Blo 1657528 2097991 := bstep (se 1 (by rfl) ⟨1573493, by rfl⟩ : syracuseStep 2097991 = 3146987) B3146987
theorem B14173127 : Blo 1657528 14173127 := bstep (se 1 (by rfl) ⟨10629845, by rfl⟩ : syracuseStep 14173127 = 21259691) B21259691
theorem B15934619 : Blo 1657528 15934619 := bstep (se 1 (by rfl) ⟨11950964, by rfl⟩ : syracuseStep 15934619 = 23901929) B23901929
theorem B17925371 : Blo 1657528 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B23921999 : Blo 1657528 23921999 := bstep (se 1 (by rfl) ⟨17941499, by rfl⟩ : syracuseStep 23921999 = 35882999) B35882999
theorem B5383543 : Blo 1657528 5383543 := bstep (se 1 (by rfl) ⟨4037657, by rfl⟩ : syracuseStep 5383543 = 8075315) B8075315
theorem B5596991 : Blo 1657528 5596991 := bstep (se 1 (by rfl) ⟨4197743, by rfl⟩ : syracuseStep 5596991 = 8395487) B8395487
theorem B7563091 : Blo 1657528 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B2099135 : Blo 1657528 2099135 := bstep (se 1 (by rfl) ⟨1574351, by rfl⟩ : syracuseStep 2099135 = 3148703) B3148703
theorem B3729563 : Blo 1657528 3729563 := bstep (se 1 (by rfl) ⟨2797172, by rfl⟩ : syracuseStep 3729563 = 5594345) B5594345
theorem B3729743 : Blo 1657528 3729743 := bstep (se 1 (by rfl) ⟨2797307, by rfl⟩ : syracuseStep 3729743 = 5594615) B5594615
theorem B4196731 : Blo 1657528 4196731 := bstep (se 1 (by rfl) ⟨3147548, by rfl⟩ : syracuseStep 4196731 = 6295097) B6295097
theorem B116451751 : Blo 1657528 116451751 := bstep (se 1 (by rfl) ⟨87338813, by rfl⟩ : syracuseStep 116451751 = 174677627) B174677627
theorem B3729833 : Blo 1657528 3729833 := bstep (se 2 (by rfl) ⟨1398687, by rfl⟩ : syracuseStep 3729833 = 2797375) B2797375
theorem B40356301 : Blo 1657528 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B5384663 : Blo 1657528 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B5974505 : Blo 1657528 5974505 := bstep (se 2 (by rfl) ⟨2240439, by rfl⟩ : syracuseStep 5974505 = 4480879) B4480879
theorem B2656975 : Blo 1657528 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B2362063 : Blo 1657528 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B1657599 : Blo 1657528 1657599 := bstep (se 1 (by rfl) ⟨1243199, by rfl⟩ : syracuseStep 1657599 = 2486399) B2486399
theorem B4721449 : Blo 1657528 4721449 := bstep (se 2 (by rfl) ⟨1770543, by rfl⟩ : syracuseStep 4721449 = 3541087) B3541087
theorem B8399699 : Blo 1657528 8399699 := bstep (se 1 (by rfl) ⟨6299774, by rfl⟩ : syracuseStep 8399699 = 12599549) B12599549
theorem B2362279 : Blo 1657528 2362279 := bstep (se 1 (by rfl) ⟨1771709, by rfl⟩ : syracuseStep 2362279 = 3543419) B3543419
theorem B1658023 : Blo 1657528 1658023 := bstep (se 1 (by rfl) ⟨1243517, by rfl⟩ : syracuseStep 1658023 = 2487035) B2487035
theorem B3148969 : Blo 1657528 3148969 := bstep (se 2 (by rfl) ⟨1180863, by rfl⟩ : syracuseStep 3148969 = 2361727) B2361727
theorem B34032899 : Blo 1657528 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B1658319 : Blo 1657528 1658319 := bstep (se 1 (by rfl) ⟨1243739, by rfl⟩ : syracuseStep 1658319 = 2487479) B2487479
theorem B13446719 : Blo 1657528 13446719 := bstep (se 1 (by rfl) ⟨10085039, by rfl⟩ : syracuseStep 13446719 = 20170079) B20170079
theorem B1658479 : Blo 1657528 1658479 := bstep (se 1 (by rfl) ⟨1243859, by rfl⟩ : syracuseStep 1658479 = 2487719) B2487719
theorem B2797247 : Blo 1657528 2797247 := bstep (se 1 (by rfl) ⟨2097935, by rfl⟩ : syracuseStep 2797247 = 4195871) B4195871
theorem B3542753 : Blo 1657528 3542753 := bstep (se 2 (by rfl) ⟨1328532, by rfl⟩ : syracuseStep 3542753 = 2657065) B2657065
theorem B1658599 : Blo 1657528 1658599 := bstep (se 1 (by rfl) ⟨1243949, by rfl⟩ : syracuseStep 1658599 = 2487899) B2487899
theorem B4198169 : Blo 1657528 4198169 := bstep (se 2 (by rfl) ⟨1574313, by rfl⟩ : syracuseStep 4198169 = 3148627) B3148627
theorem B25882415 : Blo 1657528 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B4722599 : Blo 1657528 4722599 := bstep (se 1 (by rfl) ⟨3541949, by rfl⟩ : syracuseStep 4722599 = 7083899) B7083899
theorem B3149759 : Blo 1657528 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B1658907 : Blo 1657528 1658907 := bstep (se 1 (by rfl) ⟨1244180, by rfl⟩ : syracuseStep 1658907 = 2488361) B2488361
theorem B2486303 : Blo 1657528 2486303 := bstep (se 1 (by rfl) ⟨1864727, by rfl⟩ : syracuseStep 2486303 = 3729455) B3729455
theorem B1658927 : Blo 1657528 1658927 := bstep (se 1 (by rfl) ⟨1244195, by rfl⟩ : syracuseStep 1658927 = 2488391) B2488391
theorem B2486327 : Blo 1657528 2486327 := bstep (se 1 (by rfl) ⟨1864745, by rfl⟩ : syracuseStep 2486327 = 3729491) B3729491
theorem B2486447 : Blo 1657528 2486447 := bstep (se 1 (by rfl) ⟨1864835, by rfl⟩ : syracuseStep 2486447 = 3729671) B3729671
theorem B5042351 : Blo 1657528 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B8392895 : Blo 1657528 8392895 := bstep (se 1 (by rfl) ⟨6294671, by rfl⟩ : syracuseStep 8392895 = 12589343) B12589343
theorem B4722907 : Blo 1657528 4722907 := bstep (se 1 (by rfl) ⟨3542180, by rfl⟩ : syracuseStep 4722907 = 7084361) B7084361
theorem B10629413 : Blo 1657528 10629413 := bstep (se 4 (by rfl) ⟨996507, by rfl⟩ : syracuseStep 10629413 = 1993015) B1993015
theorem B1659183 : Blo 1657528 1659183 := bstep (se 1 (by rfl) ⟨1244387, by rfl⟩ : syracuseStep 1659183 = 2488775) B2488775
theorem B2486651 : Blo 1657528 2486651 := bstep (se 1 (by rfl) ⟨1864988, by rfl⟩ : syracuseStep 2486651 = 3729977) B3729977
theorem B1659327 : Blo 1657528 1659327 := bstep (se 1 (by rfl) ⟨1244495, by rfl⟩ : syracuseStep 1659327 = 2488991) B2488991
theorem B1659423 : Blo 1657528 1659423 := bstep (se 1 (by rfl) ⟨1244567, by rfl⟩ : syracuseStep 1659423 = 2489135) B2489135
theorem B39342665 : Blo 1657528 39342665 := bstep (se 2 (by rfl) ⟨14753499, by rfl⟩ : syracuseStep 39342665 = 29506999) B29506999
theorem B1659503 : Blo 1657528 1659503 := bstep (se 1 (by rfl) ⟨1244627, by rfl⟩ : syracuseStep 1659503 = 2489255) B2489255
theorem B2486921 : Blo 1657528 2486921 := bstep (se 2 (by rfl) ⟨932595, by rfl⟩ : syracuseStep 2486921 = 1865191) B1865191
theorem B10629899 : Blo 1657528 10629899 := bstep (se 1 (by rfl) ⟨7972424, by rfl⟩ : syracuseStep 10629899 = 15944849) B15944849
theorem B155210519 : Blo 1657528 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B2487131 : Blo 1657528 2487131 := bstep (se 1 (by rfl) ⟨1865348, by rfl⟩ : syracuseStep 2487131 = 3730697) B3730697
theorem B2487161 : Blo 1657528 2487161 := bstep (se 2 (by rfl) ⟨932685, by rfl⟩ : syracuseStep 2487161 = 1865371) B1865371
theorem B13456253 : Blo 1657528 13456253 := bstep (se 3 (by rfl) ⟨2523047, by rfl⟩ : syracuseStep 13456253 = 5046095) B5046095
theorem B30274823 : Blo 1657528 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B9442601 : Blo 1657528 9442601 := bstep (se 2 (by rfl) ⟨3540975, by rfl⟩ : syracuseStep 9442601 = 7081951) B7081951
theorem B4199759 : Blo 1657528 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B2798975 : Blo 1657528 2798975 := bstep (se 1 (by rfl) ⟨2099231, by rfl⟩ : syracuseStep 2798975 = 4198463) B4198463
theorem B12596633 : Blo 1657528 12596633 := bstep (se 2 (by rfl) ⟨4723737, by rfl⟩ : syracuseStep 12596633 = 9447475) B9447475
theorem B5977559 : Blo 1657528 5977559 := bstep (se 1 (by rfl) ⟨4483169, by rfl⟩ : syracuseStep 5977559 = 8966339) B8966339
theorem B2487791 : Blo 1657528 2487791 := bstep (se 1 (by rfl) ⟨1865843, by rfl⟩ : syracuseStep 2487791 = 3731687) B3731687
theorem B10622465 : Blo 1657528 10622465 := bstep (se 2 (by rfl) ⟨3983424, by rfl⟩ : syracuseStep 10622465 = 7966849) B7966849
theorem B2487911 : Blo 1657528 2487911 := bstep (se 1 (by rfl) ⟨1865933, by rfl⟩ : syracuseStep 2487911 = 3731867) B3731867
theorem B5109409 : Blo 1657528 5109409 := bstep (se 2 (by rfl) ⟨1916028, by rfl⟩ : syracuseStep 5109409 = 3832057) B3832057
theorem B1865695 : Blo 1657528 1865695 := bstep (se 1 (by rfl) ⟨1399271, by rfl⟩ : syracuseStep 1865695 = 2798543) B2798543
theorem B2488367 : Blo 1657528 2488367 := bstep (se 1 (by rfl) ⟨1866275, by rfl⟩ : syracuseStep 2488367 = 3732551) B3732551
theorem B3733559 : Blo 1657528 3733559 := bstep (se 1 (by rfl) ⟨2800169, by rfl⟩ : syracuseStep 3733559 = 5600339) B5600339
theorem B2488487 : Blo 1657528 2488487 := bstep (se 1 (by rfl) ⟨1866365, by rfl⟩ : syracuseStep 2488487 = 3732731) B3732731
theorem B2488631 : Blo 1657528 2488631 := bstep (se 1 (by rfl) ⟨1866473, by rfl⟩ : syracuseStep 2488631 = 3732947) B3732947
theorem B14170463 : Blo 1657528 14170463 := bstep (se 1 (by rfl) ⟨10627847, by rfl⟩ : syracuseStep 14170463 = 21255695) B21255695
theorem B3733919 : Blo 1657528 3733919 := bstep (se 1 (by rfl) ⟨2800439, by rfl⟩ : syracuseStep 3733919 = 5600879) B5600879
theorem B2488811 : Blo 1657528 2488811 := bstep (se 1 (by rfl) ⟨1866608, by rfl⟩ : syracuseStep 2488811 = 3733217) B3733217
theorem B2800183 : Blo 1657528 2800183 := bstep (se 1 (by rfl) ⟨2100137, by rfl⟩ : syracuseStep 2800183 = 4200275) B4200275
theorem B2489159 : Blo 1657528 2489159 := bstep (se 1 (by rfl) ⟨1866869, by rfl⟩ : syracuseStep 2489159 = 3733739) B3733739
theorem B8395649 : Blo 1657528 8395649 := bstep (se 2 (by rfl) ⟨3148368, by rfl⟩ : syracuseStep 8395649 = 6296737) B6296737
theorem B76577723 : Blo 1657528 76577723 := bstep (se 1 (by rfl) ⟨57433292, by rfl⟩ : syracuseStep 76577723 = 114866585) B114866585
theorem B9444377 : Blo 1657528 9444377 := bstep (se 2 (by rfl) ⟨3541641, by rfl⟩ : syracuseStep 9444377 = 7083283) B7083283
theorem B10624081 : Blo 1657528 10624081 := bstep (se 2 (by rfl) ⟨3984030, by rfl⟩ : syracuseStep 10624081 = 7968061) B7968061
theorem B1866847 : Blo 1657528 1866847 := bstep (se 1 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 1866847 = 2800271) B2800271
theorem B53795947 : Blo 1657528 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B9444559 : Blo 1657528 9444559 := bstep (se 1 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 9444559 = 14166839) B14166839
theorem B28728569 : Blo 1657528 28728569 := bstep (se 2 (by rfl) ⟨10773213, by rfl⟩ : syracuseStep 28728569 = 21546427) B21546427
theorem B12598577 : Blo 1657528 12598577 := bstep (se 2 (by rfl) ⟨4724466, by rfl⟩ : syracuseStep 12598577 = 9448933) B9448933
theorem B6905407 : Blo 1657528 6905407 := bstep (se 1 (by rfl) ⟨5179055, by rfl⟩ : syracuseStep 6905407 = 10358111) B10358111
theorem B18898595 : Blo 1657528 18898595 := bstep (se 1 (by rfl) ⟨14173946, by rfl⟩ : syracuseStep 18898595 = 28347893) B28347893
theorem B6299471 : Blo 1657528 6299471 := bstep (se 1 (by rfl) ⟨4724603, by rfl⟩ : syracuseStep 6299471 = 9449207) B9449207
theorem B5595047 : Blo 1657528 5595047 := bstep (se 1 (by rfl) ⟨4196285, by rfl⟩ : syracuseStep 5595047 = 8392571) B8392571
theorem B5595263 : Blo 1657528 5595263 := bstep (se 1 (by rfl) ⟨4196447, by rfl⟩ : syracuseStep 5595263 = 8392895) B8392895
theorem B7086275 : Blo 1657528 7086275 := bstep (se 1 (by rfl) ⟨5314706, by rfl⟩ : syracuseStep 7086275 = 10629413) B10629413
theorem B5595641 : Blo 1657528 5595641 := bstep (se 2 (by rfl) ⟨2098365, by rfl⟩ : syracuseStep 5595641 = 4196731) B4196731
theorem B7086599 : Blo 1657528 7086599 := bstep (se 1 (by rfl) ⟨5314949, by rfl⟩ : syracuseStep 7086599 = 10629899) B10629899
theorem B8970835 : Blo 1657528 8970835 := bstep (se 1 (by rfl) ⟨6728126, by rfl⟩ : syracuseStep 8970835 = 13456253) B13456253
theorem B8397755 : Blo 1657528 8397755 := bstep (se 1 (by rfl) ⟨6298316, by rfl⟩ : syracuseStep 8397755 = 12596633) B12596633
theorem B14165441 : Blo 1657528 14165441 := bstep (se 2 (by rfl) ⟨5312040, by rfl⟩ : syracuseStep 14165441 = 10624081) B10624081
theorem B9446975 : Blo 1657528 9446975 := bstep (se 1 (by rfl) ⟨7085231, by rfl⟩ : syracuseStep 9446975 = 14170463) B14170463
theorem B12592745 : Blo 1657528 12592745 := bstep (se 2 (by rfl) ⟨4722279, by rfl⟩ : syracuseStep 12592745 = 9444559) B9444559
theorem B3589775 : Blo 1657528 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B3983003 : Blo 1657528 3983003 := bstep (se 1 (by rfl) ⟨2987252, by rfl⟩ : syracuseStep 3983003 = 5974505) B5974505
theorem B7178057 : Blo 1657528 7178057 := bstep (se 2 (by rfl) ⟨2691771, by rfl⟩ : syracuseStep 7178057 = 5383543) B5383543
theorem B5597099 : Blo 1657528 5597099 := bstep (se 1 (by rfl) ⟨4197824, by rfl⟩ : syracuseStep 5597099 = 8395649) B8395649
theorem B413894717 : Blo 1657528 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B8399051 : Blo 1657528 8399051 := bstep (se 1 (by rfl) ⟨6299288, by rfl⟩ : syracuseStep 8399051 = 12598577) B12598577
theorem B8964479 : Blo 1657528 8964479 := bstep (se 1 (by rfl) ⟨6723359, by rfl⟩ : syracuseStep 8964479 = 13446719) B13446719
theorem B2361835 : Blo 1657528 2361835 := bstep (se 1 (by rfl) ⟨1771376, by rfl⟩ : syracuseStep 2361835 = 3542753) B3542753
theorem B5597693 : Blo 1657528 5597693 := bstep (se 3 (by rfl) ⟨1049567, by rfl⟩ : syracuseStep 5597693 = 2099135) B2099135
theorem B17254943 : Blo 1657528 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B3730031 : Blo 1657528 3730031 := bstep (se 1 (by rfl) ⟨2797523, by rfl⟩ : syracuseStep 3730031 = 5595047) B5595047
theorem B3148399 : Blo 1657528 3148399 := bstep (se 1 (by rfl) ⟨2361299, by rfl⟩ : syracuseStep 3148399 = 4722599) B4722599
theorem B2099839 : Blo 1657528 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B1657535 : Blo 1657528 1657535 := bstep (se 1 (by rfl) ⟨1243151, by rfl⟩ : syracuseStep 1657535 = 2486303) B2486303
theorem B1657551 : Blo 1657528 1657551 := bstep (se 1 (by rfl) ⟨1243163, by rfl⟩ : syracuseStep 1657551 = 2486327) B2486327
theorem B5597963 : Blo 1657528 5597963 := bstep (se 1 (by rfl) ⟨4198472, by rfl⟩ : syracuseStep 5597963 = 8396945) B8396945
theorem B1657631 : Blo 1657528 1657631 := bstep (se 1 (by rfl) ⟨1243223, by rfl⟩ : syracuseStep 1657631 = 2486447) B2486447
theorem B1657767 : Blo 1657528 1657767 := bstep (se 1 (by rfl) ⟨1243325, by rfl⟩ : syracuseStep 1657767 = 2486651) B2486651
theorem B1657947 : Blo 1657528 1657947 := bstep (se 1 (by rfl) ⟨1243460, by rfl⟩ : syracuseStep 1657947 = 2486921) B2486921
theorem B13446269 : Blo 1657528 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B3730607 : Blo 1657528 3730607 := bstep (se 1 (by rfl) ⟨2797955, by rfl⟩ : syracuseStep 3730607 = 5595911) B5595911
theorem B1658087 : Blo 1657528 1658087 := bstep (se 1 (by rfl) ⟨1243565, by rfl⟩ : syracuseStep 1658087 = 2487131) B2487131
theorem B1658107 : Blo 1657528 1658107 := bstep (se 1 (by rfl) ⟨1243580, by rfl⟩ : syracuseStep 1658107 = 2487161) B2487161
theorem B53808401 : Blo 1657528 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B9448751 : Blo 1657528 9448751 := bstep (se 1 (by rfl) ⟨7086563, by rfl⟩ : syracuseStep 9448751 = 14173127) B14173127
theorem B27250181 : Blo 1657528 27250181 := bstep (se 4 (by rfl) ⟨2554704, by rfl⟩ : syracuseStep 27250181 = 5109409) B5109409
theorem B6295067 : Blo 1657528 6295067 := bstep (se 1 (by rfl) ⟨4721300, by rfl⟩ : syracuseStep 6295067 = 9442601) B9442601
theorem B3542633 : Blo 1657528 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B3149417 : Blo 1657528 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B7974521 : Blo 1657528 7974521 := bstep (se 2 (by rfl) ⟨2990445, by rfl⟩ : syracuseStep 7974521 = 5980891) B5980891
theorem B3985039 : Blo 1657528 3985039 := bstep (se 1 (by rfl) ⟨2988779, by rfl⟩ : syracuseStep 3985039 = 5977559) B5977559
theorem B1658527 : Blo 1657528 1658527 := bstep (se 1 (by rfl) ⟨1243895, by rfl⟩ : syracuseStep 1658527 = 2487791) B2487791
theorem B7081643 : Blo 1657528 7081643 := bstep (se 1 (by rfl) ⟨5311232, by rfl⟩ : syracuseStep 7081643 = 10622465) B10622465
theorem B6295265 : Blo 1657528 6295265 := bstep (se 2 (by rfl) ⟨2360724, by rfl⟩ : syracuseStep 6295265 = 4721449) B4721449
theorem B1658607 : Blo 1657528 1658607 := bstep (se 1 (by rfl) ⟨1243955, by rfl⟩ : syracuseStep 1658607 = 2487911) B2487911
theorem B2797321 : Blo 1657528 2797321 := bstep (se 2 (by rfl) ⟨1048995, by rfl⟩ : syracuseStep 2797321 = 2097991) B2097991
theorem B3731327 : Blo 1657528 3731327 := bstep (se 1 (by rfl) ⟨2798495, by rfl⟩ : syracuseStep 3731327 = 5596991) B5596991
theorem B3149705 : Blo 1657528 3149705 := bstep (se 2 (by rfl) ⟨1181139, by rfl⟩ : syracuseStep 3149705 = 2362279) B2362279
theorem B1658911 : Blo 1657528 1658911 := bstep (se 1 (by rfl) ⟨1244183, by rfl⟩ : syracuseStep 1658911 = 2488367) B2488367
theorem B2486375 : Blo 1657528 2486375 := bstep (se 1 (by rfl) ⟨1864781, by rfl⟩ : syracuseStep 2486375 = 3729563) B3729563
theorem B1658991 : Blo 1657528 1658991 := bstep (se 1 (by rfl) ⟨1244243, by rfl⟩ : syracuseStep 1658991 = 2488487) B2488487
theorem B1659087 : Blo 1657528 1659087 := bstep (se 1 (by rfl) ⟨1244315, by rfl⟩ : syracuseStep 1659087 = 2488631) B2488631
theorem B2486495 : Blo 1657528 2486495 := bstep (se 1 (by rfl) ⟨1864871, by rfl⟩ : syracuseStep 2486495 = 3729743) B3729743
theorem B4198625 : Blo 1657528 4198625 := bstep (se 2 (by rfl) ⟨1574484, by rfl⟩ : syracuseStep 4198625 = 3148969) B3148969
theorem B2486555 : Blo 1657528 2486555 := bstep (se 1 (by rfl) ⟨1864916, by rfl⟩ : syracuseStep 2486555 = 3729833) B3729833
theorem B1659207 : Blo 1657528 1659207 := bstep (se 1 (by rfl) ⟨1244405, by rfl⟩ : syracuseStep 1659207 = 2488811) B2488811
theorem B1659439 : Blo 1657528 1659439 := bstep (se 1 (by rfl) ⟨1244579, by rfl⟩ : syracuseStep 1659439 = 2489159) B2489159
theorem B5599799 : Blo 1657528 5599799 := bstep (se 1 (by rfl) ⟨4199849, by rfl⟩ : syracuseStep 5599799 = 8399699) B8399699
theorem B6296251 : Blo 1657528 6296251 := bstep (se 1 (by rfl) ⟨4722188, by rfl⟩ : syracuseStep 6296251 = 9444377) B9444377
theorem B22688599 : Blo 1657528 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B1864831 : Blo 1657528 1864831 := bstep (se 1 (by rfl) ⟨1398623, by rfl⟩ : syracuseStep 1864831 = 2797247) B2797247
theorem B2798779 : Blo 1657528 2798779 := bstep (se 1 (by rfl) ⟨2099084, by rfl⟩ : syracuseStep 2798779 = 4198169) B4198169
theorem B4199647 : Blo 1657528 4199647 := bstep (se 1 (by rfl) ⟨3149735, by rfl⟩ : syracuseStep 4199647 = 6299471) B6299471
theorem B2487593 : Blo 1657528 2487593 := bstep (se 2 (by rfl) ⟨932847, by rfl⟩ : syracuseStep 2487593 = 1865695) B1865695
theorem B8394191 : Blo 1657528 8394191 := bstep (se 1 (by rfl) ⟨6295643, by rfl⟩ : syracuseStep 8394191 = 12591287) B12591287
theorem B6297209 : Blo 1657528 6297209 := bstep (se 2 (by rfl) ⟨2361453, by rfl⟩ : syracuseStep 6297209 = 4722907) B4722907
theorem B155269001 : Blo 1657528 155269001 := bstep (se 2 (by rfl) ⟨58225875, by rfl⟩ : syracuseStep 155269001 = 116451751) B116451751
theorem B3733577 : Blo 1657528 3733577 := bstep (se 2 (by rfl) ⟨1400091, by rfl⟩ : syracuseStep 3733577 = 2800183) B2800183
theorem B10623079 : Blo 1657528 10623079 := bstep (se 1 (by rfl) ⟨7967309, by rfl⟩ : syracuseStep 10623079 = 15934619) B15934619
theorem B11950247 : Blo 1657528 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B20183215 : Blo 1657528 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B2799839 : Blo 1657528 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B15947999 : Blo 1657528 15947999 := bstep (se 1 (by rfl) ⟨11960999, by rfl⟩ : syracuseStep 15947999 = 23921999) B23921999
theorem B1865983 : Blo 1657528 1865983 := bstep (se 1 (by rfl) ⟨1399487, by rfl⟩ : syracuseStep 1865983 = 2798975) B2798975
theorem B2489039 : Blo 1657528 2489039 := bstep (se 1 (by rfl) ⟨1866779, by rfl⟩ : syracuseStep 2489039 = 3733559) B3733559
theorem B2489129 : Blo 1657528 2489129 := bstep (se 2 (by rfl) ⟨933423, by rfl⟩ : syracuseStep 2489129 = 1866847) B1866847
theorem B71727929 : Blo 1657528 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B104913773 : Blo 1657528 104913773 := bstep (se 3 (by rfl) ⟨19671332, by rfl⟩ : syracuseStep 104913773 = 39342665) B39342665
theorem B2489279 : Blo 1657528 2489279 := bstep (se 1 (by rfl) ⟨1866959, by rfl⟩ : syracuseStep 2489279 = 3733919) B3733919
theorem B51051815 : Blo 1657528 51051815 := bstep (se 1 (by rfl) ⟨38288861, by rfl⟩ : syracuseStep 51051815 = 76577723) B76577723
theorem B9207209 : Blo 1657528 9207209 := bstep (se 2 (by rfl) ⟨3452703, by rfl⟩ : syracuseStep 9207209 = 6905407) B6905407
theorem B19152379 : Blo 1657528 19152379 := bstep (se 1 (by rfl) ⟨14364284, by rfl⟩ : syracuseStep 19152379 = 28728569) B28728569
theorem B12599063 : Blo 1657528 12599063 := bstep (se 1 (by rfl) ⟨9449297, by rfl⟩ : syracuseStep 12599063 = 18898595) B18898595
theorem B10084121 : Blo 1657528 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B14164105 : Blo 1657528 14164105 := bstep (se 2 (by rfl) ⟨5311539, by rfl⟩ : syracuseStep 14164105 = 10623079) B10623079
theorem B26910953 : Blo 1657528 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B11961113 : Blo 1657528 11961113 := bstep (se 2 (by rfl) ⟨4485417, by rfl⟩ : syracuseStep 11961113 = 8970835) B8970835
theorem B5596127 : Blo 1657528 5596127 := bstep (se 1 (by rfl) ⟨4197095, by rfl⟩ : syracuseStep 5596127 = 8394191) B8394191
theorem B23905277 : Blo 1657528 23905277 := bstep (se 3 (by rfl) ⟨4482239, by rfl⟩ : syracuseStep 23905277 = 8964479) B8964479
theorem B2393183 : Blo 1657528 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B2655335 : Blo 1657528 2655335 := bstep (se 1 (by rfl) ⟨1991501, by rfl⟩ : syracuseStep 2655335 = 3983003) B3983003
theorem B24552557 : Blo 1657528 24552557 := bstep (se 3 (by rfl) ⟨4603604, by rfl⟩ : syracuseStep 24552557 = 9207209) B9207209
theorem B4785371 : Blo 1657528 4785371 := bstep (se 1 (by rfl) ⟨3589028, by rfl⟩ : syracuseStep 4785371 = 7178057) B7178057
theorem B11503295 : Blo 1657528 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B47818619 : Blo 1657528 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B25536505 : Blo 1657528 25536505 := bstep (se 2 (by rfl) ⟨9576189, by rfl⟩ : syracuseStep 25536505 = 19152379) B19152379
theorem B8964179 : Blo 1657528 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B3729761 : Blo 1657528 3729761 := bstep (se 2 (by rfl) ⟨1398660, by rfl⟩ : syracuseStep 3729761 = 2797321) B2797321
theorem B4196711 : Blo 1657528 4196711 := bstep (se 1 (by rfl) ⟨3147533, by rfl⟩ : syracuseStep 4196711 = 6295067) B6295067
theorem B8399213 : Blo 1657528 8399213 := bstep (se 3 (by rfl) ⟨1574852, by rfl⟩ : syracuseStep 8399213 = 3149705) B3149705
theorem B2361755 : Blo 1657528 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B2099611 : Blo 1657528 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B4721095 : Blo 1657528 4721095 := bstep (se 1 (by rfl) ⟨3540821, by rfl⟩ : syracuseStep 4721095 = 7081643) B7081643
theorem B4196843 : Blo 1657528 4196843 := bstep (se 1 (by rfl) ⟨3147632, by rfl⟩ : syracuseStep 4196843 = 6295265) B6295265
theorem B8399375 : Blo 1657528 8399375 := bstep (se 1 (by rfl) ⟨6299531, by rfl⟩ : syracuseStep 8399375 = 12599063) B12599063
theorem B1657583 : Blo 1657528 1657583 := bstep (se 1 (by rfl) ⟨1243187, by rfl⟩ : syracuseStep 1657583 = 2486375) B2486375
theorem B3730175 : Blo 1657528 3730175 := bstep (se 1 (by rfl) ⟨2797631, by rfl⟩ : syracuseStep 3730175 = 5595263) B5595263
theorem B1657663 : Blo 1657528 1657663 := bstep (se 1 (by rfl) ⟨1243247, by rfl⟩ : syracuseStep 1657663 = 2486495) B2486495
theorem B1657703 : Blo 1657528 1657703 := bstep (se 1 (by rfl) ⟨1243277, by rfl⟩ : syracuseStep 1657703 = 2486555) B2486555
theorem B3730427 : Blo 1657528 3730427 := bstep (se 1 (by rfl) ⟨2797820, by rfl⟩ : syracuseStep 3730427 = 5595641) B5595641
theorem B5598503 : Blo 1657528 5598503 := bstep (se 1 (by rfl) ⟨4198877, by rfl⟩ : syracuseStep 5598503 = 8397755) B8397755
theorem B3149113 : Blo 1657528 3149113 := bstep (se 2 (by rfl) ⟨1180917, by rfl⟩ : syracuseStep 3149113 = 2361835) B2361835
theorem B4197865 : Blo 1657528 4197865 := bstep (se 2 (by rfl) ⟨1574199, by rfl⟩ : syracuseStep 4197865 = 3148399) B3148399
theorem B1658395 : Blo 1657528 1658395 := bstep (se 1 (by rfl) ⟨1243796, by rfl⟩ : syracuseStep 1658395 = 2487593) B2487593
theorem B4198139 : Blo 1657528 4198139 := bstep (se 1 (by rfl) ⟨3148604, by rfl⟩ : syracuseStep 4198139 = 6297209) B6297209
theorem B3731399 : Blo 1657528 3731399 := bstep (se 1 (by rfl) ⟨2798549, by rfl⟩ : syracuseStep 3731399 = 5597099) B5597099
theorem B7966831 : Blo 1657528 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B5599367 : Blo 1657528 5599367 := bstep (se 1 (by rfl) ⟨4199525, by rfl⟩ : syracuseStep 5599367 = 8399051) B8399051
theorem B2486441 : Blo 1657528 2486441 := bstep (se 2 (by rfl) ⟨932415, by rfl⟩ : syracuseStep 2486441 = 1864831) B1864831
theorem B3731705 : Blo 1657528 3731705 := bstep (se 2 (by rfl) ⟨1399389, by rfl⟩ : syracuseStep 3731705 = 2798779) B2798779
theorem B5599529 : Blo 1657528 5599529 := bstep (se 2 (by rfl) ⟨2099823, by rfl⟩ : syracuseStep 5599529 = 4199647) B4199647
theorem B3731795 : Blo 1657528 3731795 := bstep (se 1 (by rfl) ⟨2798846, by rfl⟩ : syracuseStep 3731795 = 5597693) B5597693
theorem B2486687 : Blo 1657528 2486687 := bstep (se 1 (by rfl) ⟨1865015, by rfl⟩ : syracuseStep 2486687 = 3730031) B3730031
theorem B1659359 : Blo 1657528 1659359 := bstep (se 1 (by rfl) ⟨1244519, by rfl⟩ : syracuseStep 1659359 = 2489039) B2489039
theorem B3731975 : Blo 1657528 3731975 := bstep (se 1 (by rfl) ⟨2798981, by rfl⟩ : syracuseStep 3731975 = 5597963) B5597963
theorem B1659419 : Blo 1657528 1659419 := bstep (se 1 (by rfl) ⟨1244564, by rfl⟩ : syracuseStep 1659419 = 2489129) B2489129
theorem B1659519 : Blo 1657528 1659519 := bstep (se 1 (by rfl) ⟨1244639, by rfl⟩ : syracuseStep 1659519 = 2489279) B2489279
theorem B2487071 : Blo 1657528 2487071 := bstep (se 1 (by rfl) ⟨1865303, by rfl⟩ : syracuseStep 2487071 = 3730607) B3730607
theorem B5313385 : Blo 1657528 5313385 := bstep (se 2 (by rfl) ⟨1992519, by rfl⟩ : syracuseStep 5313385 = 3985039) B3985039
theorem B34034543 : Blo 1657528 34034543 := bstep (se 1 (by rfl) ⟨25525907, by rfl⟩ : syracuseStep 34034543 = 51051815) B51051815
theorem B18166787 : Blo 1657528 18166787 := bstep (se 1 (by rfl) ⟨13625090, by rfl⟩ : syracuseStep 18166787 = 27250181) B27250181
theorem B6722747 : Blo 1657528 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B2487551 : Blo 1657528 2487551 := bstep (se 1 (by rfl) ⟨1865663, by rfl⟩ : syracuseStep 2487551 = 3731327) B3731327
theorem B4724183 : Blo 1657528 4724183 := bstep (se 1 (by rfl) ⟨3543137, by rfl⟩ : syracuseStep 4724183 = 7086275) B7086275
theorem B2799083 : Blo 1657528 2799083 := bstep (se 1 (by rfl) ⟨2099312, by rfl⟩ : syracuseStep 2799083 = 4198625) B4198625
theorem B2487977 : Blo 1657528 2487977 := bstep (se 2 (by rfl) ⟨932991, by rfl⟩ : syracuseStep 2487977 = 1865983) B1865983
theorem B4724399 : Blo 1657528 4724399 := bstep (se 1 (by rfl) ⟨3543299, by rfl⟩ : syracuseStep 4724399 = 7086599) B7086599
theorem B3733199 : Blo 1657528 3733199 := bstep (se 1 (by rfl) ⟨2799899, by rfl⟩ : syracuseStep 3733199 = 5599799) B5599799
theorem B143489069 : Blo 1657528 143489069 := bstep (se 3 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 143489069 = 53808401) B53808401
theorem B2799785 : Blo 1657528 2799785 := bstep (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) B2099839
theorem B8395001 : Blo 1657528 8395001 := bstep (se 2 (by rfl) ⟨3148125, by rfl⟩ : syracuseStep 8395001 = 6296251) B6296251
theorem B9443627 : Blo 1657528 9443627 := bstep (se 1 (by rfl) ⟨7082720, by rfl⟩ : syracuseStep 9443627 = 14165441) B14165441
theorem B6297983 : Blo 1657528 6297983 := bstep (se 1 (by rfl) ⟨4723487, by rfl⟩ : syracuseStep 6297983 = 9446975) B9446975
theorem B8395163 : Blo 1657528 8395163 := bstep (se 1 (by rfl) ⟨6296372, by rfl⟩ : syracuseStep 8395163 = 12592745) B12592745
theorem B30251465 : Blo 1657528 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B103512667 : Blo 1657528 103512667 := bstep (se 1 (by rfl) ⟨77634500, by rfl⟩ : syracuseStep 103512667 = 155269001) B155269001
theorem B275929811 : Blo 1657528 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B2489051 : Blo 1657528 2489051 := bstep (se 1 (by rfl) ⟨1866788, by rfl⟩ : syracuseStep 2489051 = 3733577) B3733577
theorem B1866559 : Blo 1657528 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B10631999 : Blo 1657528 10631999 := bstep (se 1 (by rfl) ⟨7973999, by rfl⟩ : syracuseStep 10631999 = 15947999) B15947999
theorem B4476320981 : Blo 1657528 4476320981 := bstep (se 7 (by rfl) ⟨52456886, by rfl⟩ : syracuseStep 4476320981 = 104913773) B104913773
theorem B6299167 : Blo 1657528 6299167 := bstep (se 1 (by rfl) ⟨4724375, by rfl⟩ : syracuseStep 6299167 = 9448751) B9448751
theorem B5316347 : Blo 1657528 5316347 := bstep (se 1 (by rfl) ⟨3987260, by rfl⟩ : syracuseStep 5316347 = 7974521) B7974521
theorem B17940635 : Blo 1657528 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B6381821 : Blo 1657528 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B1770223 : Blo 1657528 1770223 := bstep (se 1 (by rfl) ⟨1327667, by rfl⟩ : syracuseStep 1770223 = 2655335) B2655335
theorem B16368371 : Blo 1657528 16368371 := bstep (se 1 (by rfl) ⟨12276278, by rfl⟩ : syracuseStep 16368371 = 24552557) B24552557
theorem B4481831 : Blo 1657528 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B7668863 : Blo 1657528 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B95659379 : Blo 1657528 95659379 := bstep (se 1 (by rfl) ⟨71744534, by rfl⟩ : syracuseStep 95659379 = 143489069) B143489069
theorem B5596667 : Blo 1657528 5596667 := bstep (se 1 (by rfl) ⟨4197500, by rfl⟩ : syracuseStep 5596667 = 8395001) B8395001
theorem B5596775 : Blo 1657528 5596775 := bstep (se 1 (by rfl) ⟨4197581, by rfl⟩ : syracuseStep 5596775 = 8395163) B8395163
theorem B183953207 : Blo 1657528 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B7087999 : Blo 1657528 7087999 := bstep (se 1 (by rfl) ⟨5315999, by rfl⟩ : syracuseStep 7087999 = 10631999) B10631999
theorem B5597153 : Blo 1657528 5597153 := bstep (se 2 (by rfl) ⟨2098932, by rfl⟩ : syracuseStep 5597153 = 4197865) B4197865
theorem B8398889 : Blo 1657528 8398889 := bstep (se 2 (by rfl) ⟨3149583, by rfl⟩ : syracuseStep 8398889 = 6299167) B6299167
theorem B34048673 : Blo 1657528 34048673 := bstep (se 2 (by rfl) ⟨12768252, by rfl⟩ : syracuseStep 34048673 = 25536505) B25536505
theorem B1657627 : Blo 1657528 1657627 := bstep (se 1 (by rfl) ⟨1243220, by rfl⟩ : syracuseStep 1657627 = 2486441) B2486441
theorem B18885473 : Blo 1657528 18885473 := bstep (se 2 (by rfl) ⟨7082052, by rfl⟩ : syracuseStep 18885473 = 14164105) B14164105
theorem B1657791 : Blo 1657528 1657791 := bstep (se 1 (by rfl) ⟨1243343, by rfl⟩ : syracuseStep 1657791 = 2486687) B2486687
theorem B1658047 : Blo 1657528 1658047 := bstep (se 1 (by rfl) ⟨1243535, by rfl⟩ : syracuseStep 1658047 = 2487071) B2487071
theorem B6294793 : Blo 1657528 6294793 := bstep (se 2 (by rfl) ⟨2360547, by rfl⟩ : syracuseStep 6294793 = 4721095) B4721095
theorem B3730751 : Blo 1657528 3730751 := bstep (se 1 (by rfl) ⟨2798063, by rfl⟩ : syracuseStep 3730751 = 5596127) B5596127
theorem B15936851 : Blo 1657528 15936851 := bstep (se 1 (by rfl) ⟨11952638, by rfl⟩ : syracuseStep 15936851 = 23905277) B23905277
theorem B12111191 : Blo 1657528 12111191 := bstep (se 1 (by rfl) ⟨9083393, by rfl⟩ : syracuseStep 12111191 = 18166787) B18166787
theorem B3190247 : Blo 1657528 3190247 := bstep (se 1 (by rfl) ⟨2392685, by rfl⟩ : syracuseStep 3190247 = 4785371) B4785371
theorem B1658367 : Blo 1657528 1658367 := bstep (se 1 (by rfl) ⟨1243775, by rfl⟩ : syracuseStep 1658367 = 2487551) B2487551
theorem B3149455 : Blo 1657528 3149455 := bstep (se 1 (by rfl) ⟨2362091, by rfl⟩ : syracuseStep 3149455 = 4724183) B4724183
theorem B1658651 : Blo 1657528 1658651 := bstep (se 1 (by rfl) ⟨1243988, by rfl⟩ : syracuseStep 1658651 = 2487977) B2487977
theorem B3149599 : Blo 1657528 3149599 := bstep (se 1 (by rfl) ⟨2362199, by rfl⟩ : syracuseStep 3149599 = 4724399) B4724399
theorem B31879079 : Blo 1657528 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B5976119 : Blo 1657528 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B6295751 : Blo 1657528 6295751 := bstep (se 1 (by rfl) ⟨4721813, by rfl⟩ : syracuseStep 6295751 = 9443627) B9443627
theorem B2486507 : Blo 1657528 2486507 := bstep (se 1 (by rfl) ⟨1864880, by rfl⟩ : syracuseStep 2486507 = 3729761) B3729761
theorem B2797807 : Blo 1657528 2797807 := bstep (se 1 (by rfl) ⟨2098355, by rfl⟩ : syracuseStep 2797807 = 4196711) B4196711
theorem B5599475 : Blo 1657528 5599475 := bstep (se 1 (by rfl) ⟨4199606, by rfl⟩ : syracuseStep 5599475 = 8399213) B8399213
theorem B4198655 : Blo 1657528 4198655 := bstep (se 1 (by rfl) ⟨3148991, by rfl⟩ : syracuseStep 4198655 = 6297983) B6297983
theorem B2797895 : Blo 1657528 2797895 := bstep (se 1 (by rfl) ⟨2098421, by rfl⟩ : syracuseStep 2797895 = 4196843) B4196843
theorem B5599583 : Blo 1657528 5599583 := bstep (se 1 (by rfl) ⟨4199687, by rfl⟩ : syracuseStep 5599583 = 8399375) B8399375
theorem B4198817 : Blo 1657528 4198817 := bstep (se 2 (by rfl) ⟨1574556, by rfl⟩ : syracuseStep 4198817 = 3149113) B3149113
theorem B1659367 : Blo 1657528 1659367 := bstep (se 1 (by rfl) ⟨1244525, by rfl⟩ : syracuseStep 1659367 = 2489051) B2489051
theorem B2486783 : Blo 1657528 2486783 := bstep (se 1 (by rfl) ⟨1865087, by rfl⟩ : syracuseStep 2486783 = 3730175) B3730175
theorem B2486951 : Blo 1657528 2486951 := bstep (se 1 (by rfl) ⟨1865213, by rfl⟩ : syracuseStep 2486951 = 3730427) B3730427
theorem B31896301 : Blo 1657528 31896301 := bstep (se 3 (by rfl) ⟨5980556, by rfl⟩ : syracuseStep 31896301 = 11961113) B11961113
theorem B3732335 : Blo 1657528 3732335 := bstep (se 1 (by rfl) ⟨2799251, by rfl⟩ : syracuseStep 3732335 = 5598503) B5598503
theorem B2798759 : Blo 1657528 2798759 := bstep (se 1 (by rfl) ⟨2099069, by rfl⟩ : syracuseStep 2798759 = 4198139) B4198139
theorem B3544231 : Blo 1657528 3544231 := bstep (se 1 (by rfl) ⟨2658173, by rfl⟩ : syracuseStep 3544231 = 5316347) B5316347
theorem B2487599 : Blo 1657528 2487599 := bstep (se 1 (by rfl) ⟨1865699, by rfl⟩ : syracuseStep 2487599 = 3731399) B3731399
theorem B3732911 : Blo 1657528 3732911 := bstep (se 1 (by rfl) ⟨2799683, by rfl⟩ : syracuseStep 3732911 = 5599367) B5599367
theorem B10622441 : Blo 1657528 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B2487803 : Blo 1657528 2487803 := bstep (se 1 (by rfl) ⟨1865852, by rfl⟩ : syracuseStep 2487803 = 3731705) B3731705
theorem B3733019 : Blo 1657528 3733019 := bstep (se 1 (by rfl) ⟨2799764, by rfl⟩ : syracuseStep 3733019 = 5599529) B5599529
theorem B2487863 : Blo 1657528 2487863 := bstep (se 1 (by rfl) ⟨1865897, by rfl⟩ : syracuseStep 2487863 = 3731795) B3731795
theorem B2487983 : Blo 1657528 2487983 := bstep (se 1 (by rfl) ⟨1865987, by rfl⟩ : syracuseStep 2487983 = 3731975) B3731975
theorem B2799481 : Blo 1657528 2799481 := bstep (se 2 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 2799481 = 2099611) B2099611
theorem B22689695 : Blo 1657528 22689695 := bstep (se 1 (by rfl) ⟨17017271, by rfl⟩ : syracuseStep 22689695 = 34034543) B34034543
theorem B138016889 : Blo 1657528 138016889 := bstep (se 2 (by rfl) ⟨51756333, by rfl⟩ : syracuseStep 138016889 = 103512667) B103512667
theorem B1866055 : Blo 1657528 1866055 := bstep (se 1 (by rfl) ⟨1399541, by rfl⟩ : syracuseStep 1866055 = 2799083) B2799083
theorem B6298013 : Blo 1657528 6298013 := bstep (se 3 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 6298013 = 2361755) B2361755
theorem B2488745 : Blo 1657528 2488745 := bstep (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) B1866559
theorem B2488799 : Blo 1657528 2488799 := bstep (se 1 (by rfl) ⟨1866599, by rfl⟩ : syracuseStep 2488799 = 3733199) B3733199
theorem B7084513 : Blo 1657528 7084513 := bstep (se 2 (by rfl) ⟨2656692, by rfl⟩ : syracuseStep 7084513 = 5313385) B5313385
theorem B1866523 : Blo 1657528 1866523 := bstep (se 1 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 1866523 = 2799785) B2799785
theorem B20167643 : Blo 1657528 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B2984213987 : Blo 1657528 2984213987 := bstep (se 1 (by rfl) ⟨2238160490, by rfl⟩ : syracuseStep 2984213987 = 4476320981) B4476320981
theorem B11960423 : Blo 1657528 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B10912247 : Blo 1657528 10912247 := bstep (se 1 (by rfl) ⟨8184185, by rfl⟩ : syracuseStep 10912247 = 16368371) B16368371
theorem B9446017 : Blo 1657528 9446017 := bstep (se 2 (by rfl) ⟨3542256, by rfl⟩ : syracuseStep 9446017 = 7084513) B7084513
theorem B5112575 : Blo 1657528 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B2360297 : Blo 1657528 2360297 := bstep (se 2 (by rfl) ⟨885111, by rfl⟩ : syracuseStep 2360297 = 1770223) B1770223
theorem B122635471 : Blo 1657528 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B21252719 : Blo 1657528 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B3984079 : Blo 1657528 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B4197167 : Blo 1657528 4197167 := bstep (se 1 (by rfl) ⟨3147875, by rfl⟩ : syracuseStep 4197167 = 6295751) B6295751
theorem B1657671 : Blo 1657528 1657671 := bstep (se 1 (by rfl) ⟨1243253, by rfl⟩ : syracuseStep 1657671 = 2486507) B2486507
theorem B4254547 : Blo 1657528 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B3730409 : Blo 1657528 3730409 := bstep (se 2 (by rfl) ⟨1398903, by rfl⟩ : syracuseStep 3730409 = 2797807) B2797807
theorem B1657855 : Blo 1657528 1657855 := bstep (se 1 (by rfl) ⟨1243391, by rfl⟩ : syracuseStep 1657855 = 2486783) B2486783
theorem B1657967 : Blo 1657528 1657967 := bstep (se 1 (by rfl) ⟨1243475, by rfl⟩ : syracuseStep 1657967 = 2486951) B2486951
theorem B1658399 : Blo 1657528 1658399 := bstep (se 1 (by rfl) ⟨1243799, by rfl⟩ : syracuseStep 1658399 = 2487599) B2487599
theorem B42528401 : Blo 1657528 42528401 := bstep (se 2 (by rfl) ⟨15948150, by rfl⟩ : syracuseStep 42528401 = 31896301) B31896301
theorem B7081627 : Blo 1657528 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B3731111 : Blo 1657528 3731111 := bstep (se 1 (by rfl) ⟨2798333, by rfl⟩ : syracuseStep 3731111 = 5596667) B5596667
theorem B1658535 : Blo 1657528 1658535 := bstep (se 1 (by rfl) ⟨1243901, by rfl⟩ : syracuseStep 1658535 = 2487803) B2487803
theorem B1658575 : Blo 1657528 1658575 := bstep (se 1 (by rfl) ⟨1243931, by rfl⟩ : syracuseStep 1658575 = 2487863) B2487863
theorem B3731183 : Blo 1657528 3731183 := bstep (se 1 (by rfl) ⟨2798387, by rfl⟩ : syracuseStep 3731183 = 5596775) B5596775
theorem B1658655 : Blo 1657528 1658655 := bstep (se 1 (by rfl) ⟨1243991, by rfl⟩ : syracuseStep 1658655 = 2487983) B2487983
theorem B15126463 : Blo 1657528 15126463 := bstep (se 1 (by rfl) ⟨11344847, by rfl⟩ : syracuseStep 15126463 = 22689695) B22689695
theorem B3731435 : Blo 1657528 3731435 := bstep (se 1 (by rfl) ⟨2798576, by rfl⟩ : syracuseStep 3731435 = 5597153) B5597153
theorem B5599259 : Blo 1657528 5599259 := bstep (se 1 (by rfl) ⟨4199444, by rfl⟩ : syracuseStep 5599259 = 8398889) B8398889
theorem B4198675 : Blo 1657528 4198675 := bstep (se 1 (by rfl) ⟨3149006, by rfl⟩ : syracuseStep 4198675 = 6298013) B6298013
theorem B1659163 : Blo 1657528 1659163 := bstep (se 1 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 1659163 = 2488745) B2488745
theorem B1659199 : Blo 1657528 1659199 := bstep (se 1 (by rfl) ⟨1244399, by rfl⟩ : syracuseStep 1659199 = 2488799) B2488799
theorem B8393057 : Blo 1657528 8393057 := bstep (se 2 (by rfl) ⟨3147396, by rfl⟩ : syracuseStep 8393057 = 6294793) B6294793
theorem B4199273 : Blo 1657528 4199273 := bstep (se 2 (by rfl) ⟨1574727, by rfl⟩ : syracuseStep 4199273 = 3149455) B3149455
theorem B2487167 : Blo 1657528 2487167 := bstep (se 1 (by rfl) ⟨1865375, by rfl⟩ : syracuseStep 2487167 = 3730751) B3730751
theorem B8074127 : Blo 1657528 8074127 := bstep (se 1 (by rfl) ⟨6055595, by rfl⟩ : syracuseStep 8074127 = 12111191) B12111191
theorem B2126831 : Blo 1657528 2126831 := bstep (se 1 (by rfl) ⟨1595123, by rfl⟩ : syracuseStep 2126831 = 3190247) B3190247
theorem B4199465 : Blo 1657528 4199465 := bstep (se 2 (by rfl) ⟨1574799, by rfl⟩ : syracuseStep 4199465 = 3149599) B3149599
theorem B3732641 : Blo 1657528 3732641 := bstep (se 2 (by rfl) ⟨1399740, by rfl⟩ : syracuseStep 3732641 = 2799481) B2799481
theorem B9450665 : Blo 1657528 9450665 := bstep (se 2 (by rfl) ⟨3543999, by rfl⟩ : syracuseStep 9450665 = 7087999) B7087999
theorem B3732983 : Blo 1657528 3732983 := bstep (se 1 (by rfl) ⟨2799737, by rfl⟩ : syracuseStep 3732983 = 5599475) B5599475
theorem B2799103 : Blo 1657528 2799103 := bstep (se 1 (by rfl) ⟨2099327, by rfl⟩ : syracuseStep 2799103 = 4198655) B4198655
theorem B1865263 : Blo 1657528 1865263 := bstep (se 1 (by rfl) ⟨1398947, by rfl⟩ : syracuseStep 1865263 = 2797895) B2797895
theorem B3733055 : Blo 1657528 3733055 := bstep (se 1 (by rfl) ⟨2799791, by rfl⟩ : syracuseStep 3733055 = 5599583) B5599583
theorem B2799211 : Blo 1657528 2799211 := bstep (se 1 (by rfl) ⟨2099408, by rfl⟩ : syracuseStep 2799211 = 4198817) B4198817
theorem B2488073 : Blo 1657528 2488073 := bstep (se 2 (by rfl) ⟨933027, by rfl⟩ : syracuseStep 2488073 = 1866055) B1866055
theorem B2987887 : Blo 1657528 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2488223 : Blo 1657528 2488223 := bstep (se 1 (by rfl) ⟨1866167, by rfl⟩ : syracuseStep 2488223 = 3732335) B3732335
theorem B1865839 : Blo 1657528 1865839 := bstep (se 1 (by rfl) ⟨1399379, by rfl⟩ : syracuseStep 1865839 = 2798759) B2798759
theorem B63772919 : Blo 1657528 63772919 := bstep (se 1 (by rfl) ⟨47829689, by rfl⟩ : syracuseStep 63772919 = 95659379) B95659379
theorem B2488607 : Blo 1657528 2488607 := bstep (se 1 (by rfl) ⟨1866455, by rfl⟩ : syracuseStep 2488607 = 3732911) B3732911
theorem B2488679 : Blo 1657528 2488679 := bstep (se 1 (by rfl) ⟨1866509, by rfl⟩ : syracuseStep 2488679 = 3733019) B3733019
theorem B2488697 : Blo 1657528 2488697 := bstep (se 2 (by rfl) ⟨933261, by rfl⟩ : syracuseStep 2488697 = 1866523) B1866523
theorem B92011259 : Blo 1657528 92011259 := bstep (se 1 (by rfl) ⟨69008444, by rfl⟩ : syracuseStep 92011259 = 138016889) B138016889
theorem B4725641 : Blo 1657528 4725641 := bstep (se 2 (by rfl) ⟨1772115, by rfl⟩ : syracuseStep 4725641 = 3544231) B3544231
theorem B22699115 : Blo 1657528 22699115 := bstep (se 1 (by rfl) ⟨17024336, by rfl⟩ : syracuseStep 22699115 = 34048673) B34048673
theorem B12590315 : Blo 1657528 12590315 := bstep (se 1 (by rfl) ⟨9442736, by rfl⟩ : syracuseStep 12590315 = 18885473) B18885473
theorem B10624567 : Blo 1657528 10624567 := bstep (se 1 (by rfl) ⟨7968425, by rfl⟩ : syracuseStep 10624567 = 15936851) B15936851
theorem B1989475991 : Blo 1657528 1989475991 := bstep (se 1 (by rfl) ⟨1492106993, by rfl⟩ : syracuseStep 1989475991 = 2984213987) B2984213987
theorem B53780381 : Blo 1657528 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B5595371 : Blo 1657528 5595371 := bstep (se 1 (by rfl) ⟨4196528, by rfl⟩ : syracuseStep 5595371 = 8393057) B8393057
theorem B7274831 : Blo 1657528 7274831 := bstep (se 1 (by rfl) ⟨5456123, by rfl⟩ : syracuseStep 7274831 = 10912247) B10912247
theorem B3408383 : Blo 1657528 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B6300443 : Blo 1657528 6300443 := bstep (se 1 (by rfl) ⟨4725332, by rfl⟩ : syracuseStep 6300443 = 9450665) B9450665
theorem B163513961 : Blo 1657528 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B15132743 : Blo 1657528 15132743 := bstep (se 1 (by rfl) ⟨11349557, by rfl⟩ : syracuseStep 15132743 = 22699115) B22699115
theorem B14166089 : Blo 1657528 14166089 := bstep (se 2 (by rfl) ⟨5312283, by rfl⟩ : syracuseStep 14166089 = 10624567) B10624567
theorem B21531005 : Blo 1657528 21531005 := bstep (se 3 (by rfl) ⟨4037063, by rfl⟩ : syracuseStep 21531005 = 8074127) B8074127
theorem B3983849 : Blo 1657528 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B6294125 : Blo 1657528 6294125 := bstep (se 3 (by rfl) ⟨1180148, by rfl⟩ : syracuseStep 6294125 = 2360297) B2360297
theorem B5671549 : Blo 1657528 5671549 := bstep (se 3 (by rfl) ⟨1063415, by rfl⟩ : syracuseStep 5671549 = 2126831) B2126831
theorem B7973615 : Blo 1657528 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B5598233 : Blo 1657528 5598233 := bstep (se 2 (by rfl) ⟨2099337, by rfl⟩ : syracuseStep 5598233 = 4198675) B4198675
theorem B1658111 : Blo 1657528 1658111 := bstep (se 1 (by rfl) ⟨1243583, by rfl⟩ : syracuseStep 1658111 = 2487167) B2487167
theorem B12594689 : Blo 1657528 12594689 := bstep (se 2 (by rfl) ⟨4723008, by rfl⟩ : syracuseStep 12594689 = 9446017) B9446017
theorem B5312105 : Blo 1657528 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B5672729 : Blo 1657528 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B1658715 : Blo 1657528 1658715 := bstep (se 1 (by rfl) ⟨1244036, by rfl⟩ : syracuseStep 1658715 = 2488073) B2488073
theorem B1658815 : Blo 1657528 1658815 := bstep (se 1 (by rfl) ⟨1244111, by rfl⟩ : syracuseStep 1658815 = 2488223) B2488223
theorem B1659071 : Blo 1657528 1659071 := bstep (se 1 (by rfl) ⟨1244303, by rfl⟩ : syracuseStep 1659071 = 2488607) B2488607
theorem B1659119 : Blo 1657528 1659119 := bstep (se 1 (by rfl) ⟨1244339, by rfl⟩ : syracuseStep 1659119 = 2488679) B2488679
theorem B1659131 : Blo 1657528 1659131 := bstep (se 1 (by rfl) ⟨1244348, by rfl⟩ : syracuseStep 1659131 = 2488697) B2488697
theorem B14168479 : Blo 1657528 14168479 := bstep (se 1 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 14168479 = 21252719) B21252719
theorem B2798111 : Blo 1657528 2798111 := bstep (se 1 (by rfl) ⟨2098583, by rfl⟩ : syracuseStep 2798111 = 4197167) B4197167
theorem B3150427 : Blo 1657528 3150427 := bstep (se 1 (by rfl) ⟨2362820, by rfl⟩ : syracuseStep 3150427 = 4725641) B4725641
theorem B2486939 : Blo 1657528 2486939 := bstep (se 1 (by rfl) ⟨1865204, by rfl⟩ : syracuseStep 2486939 = 3730409) B3730409
theorem B245363357 : Blo 1657528 245363357 := bstep (se 3 (by rfl) ⟨46005629, by rfl⟩ : syracuseStep 245363357 = 92011259) B92011259
theorem B3732137 : Blo 1657528 3732137 := bstep (se 2 (by rfl) ⟨1399551, by rfl⟩ : syracuseStep 3732137 = 2799103) B2799103
theorem B2487017 : Blo 1657528 2487017 := bstep (se 2 (by rfl) ⟨932631, by rfl⟩ : syracuseStep 2487017 = 1865263) B1865263
theorem B3732281 : Blo 1657528 3732281 := bstep (se 2 (by rfl) ⟨1399605, by rfl⟩ : syracuseStep 3732281 = 2799211) B2799211
theorem B8393543 : Blo 1657528 8393543 := bstep (se 1 (by rfl) ⟨6295157, by rfl⟩ : syracuseStep 8393543 = 12590315) B12590315
theorem B9442169 : Blo 1657528 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B2487407 : Blo 1657528 2487407 := bstep (se 1 (by rfl) ⟨1865555, by rfl⟩ : syracuseStep 2487407 = 3731111) B3731111
theorem B2487455 : Blo 1657528 2487455 := bstep (se 1 (by rfl) ⟨1865591, by rfl⟩ : syracuseStep 2487455 = 3731183) B3731183
theorem B35853587 : Blo 1657528 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B2487623 : Blo 1657528 2487623 := bstep (se 1 (by rfl) ⟨1865717, by rfl⟩ : syracuseStep 2487623 = 3731435) B3731435
theorem B3732839 : Blo 1657528 3732839 := bstep (se 1 (by rfl) ⟨2799629, by rfl⟩ : syracuseStep 3732839 = 5599259) B5599259
theorem B2487785 : Blo 1657528 2487785 := bstep (se 2 (by rfl) ⟨932919, by rfl⟩ : syracuseStep 2487785 = 1865839) B1865839
theorem B2799515 : Blo 1657528 2799515 := bstep (se 1 (by rfl) ⟨2099636, by rfl⟩ : syracuseStep 2799515 = 4199273) B4199273
theorem B2799643 : Blo 1657528 2799643 := bstep (se 1 (by rfl) ⟨2099732, by rfl⟩ : syracuseStep 2799643 = 4199465) B4199465
theorem B2488427 : Blo 1657528 2488427 := bstep (se 1 (by rfl) ⟨1866320, by rfl⟩ : syracuseStep 2488427 = 3732641) B3732641
theorem B2488655 : Blo 1657528 2488655 := bstep (se 1 (by rfl) ⟨1866491, by rfl⟩ : syracuseStep 2488655 = 3732983) B3732983
theorem B2488703 : Blo 1657528 2488703 := bstep (se 1 (by rfl) ⟨1866527, by rfl⟩ : syracuseStep 2488703 = 3733055) B3733055
theorem B42515279 : Blo 1657528 42515279 := bstep (se 1 (by rfl) ⟨31886459, by rfl⟩ : syracuseStep 42515279 = 63772919) B63772919
theorem B28352267 : Blo 1657528 28352267 := bstep (se 1 (by rfl) ⟨21264200, by rfl⟩ : syracuseStep 28352267 = 42528401) B42528401
theorem B1326317327 : Blo 1657528 1326317327 := bstep (se 1 (by rfl) ⟨994737995, by rfl⟩ : syracuseStep 1326317327 = 1989475991) B1989475991
theorem B20168617 : Blo 1657528 20168617 := bstep (se 2 (by rfl) ⟨7563231, by rfl⟩ : syracuseStep 20168617 = 15126463) B15126463
theorem B18891305 : Blo 1657528 18891305 := bstep (se 2 (by rfl) ⟨7084239, by rfl⟩ : syracuseStep 18891305 = 14168479) B14168479
theorem B5595695 : Blo 1657528 5595695 := bstep (se 1 (by rfl) ⟨4196771, by rfl⟩ : syracuseStep 5595695 = 8393543) B8393543
theorem B19399549 : Blo 1657528 19399549 := bstep (se 3 (by rfl) ⟨3637415, by rfl⟩ : syracuseStep 19399549 = 7274831) B7274831
theorem B14354003 : Blo 1657528 14354003 := bstep (se 1 (by rfl) ⟨10765502, by rfl⟩ : syracuseStep 14354003 = 21531005) B21531005
theorem B2655899 : Blo 1657528 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B4196083 : Blo 1657528 4196083 := bstep (se 1 (by rfl) ⟨3147062, by rfl⟩ : syracuseStep 4196083 = 6294125) B6294125
theorem B3541403 : Blo 1657528 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B18901511 : Blo 1657528 18901511 := bstep (se 1 (by rfl) ⟨14176133, by rfl⟩ : syracuseStep 18901511 = 28352267) B28352267
theorem B3730247 : Blo 1657528 3730247 := bstep (se 1 (by rfl) ⟨2797685, by rfl⟩ : syracuseStep 3730247 = 5595371) B5595371
theorem B2272255 : Blo 1657528 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B1657959 : Blo 1657528 1657959 := bstep (se 1 (by rfl) ⟨1243469, by rfl⟩ : syracuseStep 1657959 = 2486939) B2486939
theorem B1658011 : Blo 1657528 1658011 := bstep (se 1 (by rfl) ⟨1243508, by rfl⟩ : syracuseStep 1658011 = 2487017) B2487017
theorem B6294779 : Blo 1657528 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B30248261 : Blo 1657528 30248261 := bstep (se 4 (by rfl) ⟨2835774, by rfl⟩ : syracuseStep 30248261 = 5671549) B5671549
theorem B1658271 : Blo 1657528 1658271 := bstep (se 1 (by rfl) ⟨1243703, by rfl⟩ : syracuseStep 1658271 = 2487407) B2487407
theorem B1658303 : Blo 1657528 1658303 := bstep (se 1 (by rfl) ⟨1243727, by rfl⟩ : syracuseStep 1658303 = 2487455) B2487455
theorem B1658415 : Blo 1657528 1658415 := bstep (se 1 (by rfl) ⟨1243811, by rfl⟩ : syracuseStep 1658415 = 2487623) B2487623
theorem B1658523 : Blo 1657528 1658523 := bstep (se 1 (by rfl) ⟨1243892, by rfl⟩ : syracuseStep 1658523 = 2487785) B2487785
theorem B10088495 : Blo 1657528 10088495 := bstep (se 1 (by rfl) ⟨7566371, by rfl⟩ : syracuseStep 10088495 = 15132743) B15132743
theorem B1658951 : Blo 1657528 1658951 := bstep (se 1 (by rfl) ⟨1244213, by rfl⟩ : syracuseStep 1658951 = 2488427) B2488427
theorem B1659103 : Blo 1657528 1659103 := bstep (se 1 (by rfl) ⟨1244327, by rfl⟩ : syracuseStep 1659103 = 2488655) B2488655
theorem B1659135 : Blo 1657528 1659135 := bstep (se 1 (by rfl) ⟨1244351, by rfl⟩ : syracuseStep 1659135 = 2488703) B2488703
theorem B3732155 : Blo 1657528 3732155 := bstep (se 1 (by rfl) ⟨2799116, by rfl⟩ : syracuseStep 3732155 = 5598233) B5598233
theorem B3781819 : Blo 1657528 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B26891489 : Blo 1657528 26891489 := bstep (se 2 (by rfl) ⟨10084308, by rfl⟩ : syracuseStep 26891489 = 20168617) B20168617
theorem B3732857 : Blo 1657528 3732857 := bstep (se 2 (by rfl) ⟨1399821, by rfl⟩ : syracuseStep 3732857 = 2799643) B2799643
theorem B1865407 : Blo 1657528 1865407 := bstep (se 1 (by rfl) ⟨1399055, by rfl⟩ : syracuseStep 1865407 = 2798111) B2798111
theorem B163575571 : Blo 1657528 163575571 := bstep (se 1 (by rfl) ⟨122681678, by rfl⟩ : syracuseStep 163575571 = 245363357) B245363357
theorem B2488091 : Blo 1657528 2488091 := bstep (se 1 (by rfl) ⟨1866068, by rfl⟩ : syracuseStep 2488091 = 3732137) B3732137
theorem B4200295 : Blo 1657528 4200295 := bstep (se 1 (by rfl) ⟨3150221, by rfl⟩ : syracuseStep 4200295 = 6300443) B6300443
theorem B2488187 : Blo 1657528 2488187 := bstep (se 1 (by rfl) ⟨1866140, by rfl⟩ : syracuseStep 2488187 = 3732281) B3732281
theorem B4200569 : Blo 1657528 4200569 := bstep (se 2 (by rfl) ⟨1575213, by rfl⟩ : syracuseStep 4200569 = 3150427) B3150427
theorem B23902391 : Blo 1657528 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B2488559 : Blo 1657528 2488559 := bstep (se 1 (by rfl) ⟨1866419, by rfl⟩ : syracuseStep 2488559 = 3732839) B3732839
theorem B109009307 : Blo 1657528 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B1866343 : Blo 1657528 1866343 := bstep (se 1 (by rfl) ⟨1399757, by rfl⟩ : syracuseStep 1866343 = 2799515) B2799515
theorem B9444059 : Blo 1657528 9444059 := bstep (se 1 (by rfl) ⟨7083044, by rfl⟩ : syracuseStep 9444059 = 14166089) B14166089
theorem B5315743 : Blo 1657528 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B28343519 : Blo 1657528 28343519 := bstep (se 1 (by rfl) ⟨21257639, by rfl⟩ : syracuseStep 28343519 = 42515279) B42515279
theorem B8396459 : Blo 1657528 8396459 := bstep (se 1 (by rfl) ⟨6297344, by rfl⟩ : syracuseStep 8396459 = 12594689) B12594689
theorem B884211551 : Blo 1657528 884211551 := bstep (se 1 (by rfl) ⟨663158663, by rfl⟩ : syracuseStep 884211551 = 1326317327) B1326317327
theorem B6725663 : Blo 1657528 6725663 := bstep (se 1 (by rfl) ⟨5044247, by rfl⟩ : syracuseStep 6725663 = 10088495) B10088495
theorem B9569335 : Blo 1657528 9569335 := bstep (se 1 (by rfl) ⟨7177001, by rfl⟩ : syracuseStep 9569335 = 14354003) B14354003
theorem B1770599 : Blo 1657528 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B15934927 : Blo 1657528 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B7087657 : Blo 1657528 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B72672871 : Blo 1657528 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B2360935 : Blo 1657528 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B12601007 : Blo 1657528 12601007 := bstep (se 1 (by rfl) ⟨9450755, by rfl⟩ : syracuseStep 12601007 = 18901511) B18901511
theorem B4196519 : Blo 1657528 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B5597639 : Blo 1657528 5597639 := bstep (se 1 (by rfl) ⟨4198229, by rfl⟩ : syracuseStep 5597639 = 8396459) B8396459
theorem B589474367 : Blo 1657528 589474367 := bstep (se 1 (by rfl) ⟨442105775, by rfl⟩ : syracuseStep 589474367 = 884211551) B884211551
theorem B48474773 : Blo 1657528 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B12594203 : Blo 1657528 12594203 := bstep (se 1 (by rfl) ⟨9445652, by rfl⟩ : syracuseStep 12594203 = 18891305) B18891305
theorem B3730463 : Blo 1657528 3730463 := bstep (se 1 (by rfl) ⟨2797847, by rfl⟩ : syracuseStep 3730463 = 5595695) B5595695
theorem B17927659 : Blo 1657528 17927659 := bstep (se 1 (by rfl) ⟨13445744, by rfl⟩ : syracuseStep 17927659 = 26891489) B26891489
theorem B25866065 : Blo 1657528 25866065 := bstep (se 2 (by rfl) ⟨9699774, by rfl⟩ : syracuseStep 25866065 = 19399549) B19399549
theorem B1658727 : Blo 1657528 1658727 := bstep (se 1 (by rfl) ⟨1244045, by rfl⟩ : syracuseStep 1658727 = 2488091) B2488091
theorem B1658791 : Blo 1657528 1658791 := bstep (se 1 (by rfl) ⟨1244093, by rfl⟩ : syracuseStep 1658791 = 2488187) B2488187
theorem B1659039 : Blo 1657528 1659039 := bstep (se 1 (by rfl) ⟨1244279, by rfl⟩ : syracuseStep 1659039 = 2488559) B2488559
theorem B5042425 : Blo 1657528 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B6296039 : Blo 1657528 6296039 := bstep (se 1 (by rfl) ⟨4722029, by rfl⟩ : syracuseStep 6296039 = 9444059) B9444059
theorem B2486831 : Blo 1657528 2486831 := bstep (se 1 (by rfl) ⟨1865123, by rfl⟩ : syracuseStep 2486831 = 3730247) B3730247
theorem B18895679 : Blo 1657528 18895679 := bstep (se 1 (by rfl) ⟨14171759, by rfl⟩ : syracuseStep 18895679 = 28343519) B28343519
theorem B20165507 : Blo 1657528 20165507 := bstep (se 1 (by rfl) ⟨15124130, by rfl⟩ : syracuseStep 20165507 = 30248261) B30248261
theorem B2487209 : Blo 1657528 2487209 := bstep (se 2 (by rfl) ⟨932703, by rfl⟩ : syracuseStep 2487209 = 1865407) B1865407
theorem B218100761 : Blo 1657528 218100761 := bstep (se 2 (by rfl) ⟨81787785, by rfl⟩ : syracuseStep 218100761 = 163575571) B163575571
theorem B5600393 : Blo 1657528 5600393 := bstep (se 2 (by rfl) ⟨2100147, by rfl⟩ : syracuseStep 5600393 = 4200295) B4200295
theorem B2488103 : Blo 1657528 2488103 := bstep (se 1 (by rfl) ⟨1866077, by rfl⟩ : syracuseStep 2488103 = 3732155) B3732155
theorem B2488457 : Blo 1657528 2488457 := bstep (se 2 (by rfl) ⟨933171, by rfl⟩ : syracuseStep 2488457 = 1866343) B1866343
theorem B2488571 : Blo 1657528 2488571 := bstep (se 1 (by rfl) ⟨1866428, by rfl⟩ : syracuseStep 2488571 = 3732857) B3732857
theorem B2800379 : Blo 1657528 2800379 := bstep (se 1 (by rfl) ⟨2100284, by rfl⟩ : syracuseStep 2800379 = 4200569) B4200569
theorem B5594777 : Blo 1657528 5594777 := bstep (se 2 (by rfl) ⟨2098041, by rfl⟩ : syracuseStep 5594777 = 4196083) B4196083
theorem B13443671 : Blo 1657528 13443671 := bstep (se 1 (by rfl) ⟨10082753, by rfl⟩ : syracuseStep 13443671 = 20165507) B20165507
theorem B145400507 : Blo 1657528 145400507 := bstep (se 1 (by rfl) ⟨109050380, by rfl⟩ : syracuseStep 145400507 = 218100761) B218100761
theorem B96897161 : Blo 1657528 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B3147913 : Blo 1657528 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B3729851 : Blo 1657528 3729851 := bstep (se 1 (by rfl) ⟨2797388, by rfl⟩ : syracuseStep 3729851 = 5594777) B5594777
theorem B4483775 : Blo 1657528 4483775 := bstep (se 1 (by rfl) ⟨3362831, by rfl⟩ : syracuseStep 4483775 = 6725663) B6725663
theorem B4721597 : Blo 1657528 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B4197359 : Blo 1657528 4197359 := bstep (se 1 (by rfl) ⟨3148019, by rfl⟩ : syracuseStep 4197359 = 6296039) B6296039
theorem B1657887 : Blo 1657528 1657887 := bstep (se 1 (by rfl) ⟨1243415, by rfl⟩ : syracuseStep 1657887 = 2486831) B2486831
theorem B1658139 : Blo 1657528 1658139 := bstep (se 1 (by rfl) ⟨1243604, by rfl⟩ : syracuseStep 1658139 = 2487209) B2487209
theorem B8400671 : Blo 1657528 8400671 := bstep (se 1 (by rfl) ⟨6300503, by rfl⟩ : syracuseStep 8400671 = 12601007) B12601007
theorem B1658735 : Blo 1657528 1658735 := bstep (se 1 (by rfl) ⟨1244051, by rfl⟩ : syracuseStep 1658735 = 2488103) B2488103
theorem B12759113 : Blo 1657528 12759113 := bstep (se 2 (by rfl) ⟨4784667, by rfl⟩ : syracuseStep 12759113 = 9569335) B9569335
theorem B1658971 : Blo 1657528 1658971 := bstep (se 1 (by rfl) ⟨1244228, by rfl⟩ : syracuseStep 1658971 = 2488457) B2488457
theorem B2797679 : Blo 1657528 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B1659047 : Blo 1657528 1659047 := bstep (se 1 (by rfl) ⟨1244285, by rfl⟩ : syracuseStep 1659047 = 2488571) B2488571
theorem B3731759 : Blo 1657528 3731759 := bstep (se 1 (by rfl) ⟨2798819, by rfl⟩ : syracuseStep 3731759 = 5597639) B5597639
theorem B392982911 : Blo 1657528 392982911 := bstep (se 1 (by rfl) ⟨294737183, by rfl⟩ : syracuseStep 392982911 = 589474367) B589474367
theorem B21246569 : Blo 1657528 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B2486975 : Blo 1657528 2486975 := bstep (se 1 (by rfl) ⟨1865231, by rfl⟩ : syracuseStep 2486975 = 3730463) B3730463
theorem B9450209 : Blo 1657528 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B6723233 : Blo 1657528 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B12597119 : Blo 1657528 12597119 := bstep (se 1 (by rfl) ⟨9447839, by rfl⟩ : syracuseStep 12597119 = 18895679) B18895679
theorem B3733595 : Blo 1657528 3733595 := bstep (se 1 (by rfl) ⟨2800196, by rfl⟩ : syracuseStep 3733595 = 5600393) B5600393
theorem B32316515 : Blo 1657528 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B1866919 : Blo 1657528 1866919 := bstep (se 1 (by rfl) ⟨1400189, by rfl⟩ : syracuseStep 1866919 = 2800379) B2800379
theorem B23903545 : Blo 1657528 23903545 := bstep (se 2 (by rfl) ⟨8963829, by rfl⟩ : syracuseStep 23903545 = 17927659) B17927659
theorem B8396135 : Blo 1657528 8396135 := bstep (se 1 (by rfl) ⟨6297101, by rfl⟩ : syracuseStep 8396135 = 12594203) B12594203
theorem B68976173 : Blo 1657528 68976173 := bstep (se 3 (by rfl) ⟨12933032, by rfl⟩ : syracuseStep 68976173 = 25866065) B25866065
theorem B261988607 : Blo 1657528 261988607 := bstep (se 1 (by rfl) ⟨196491455, by rfl⟩ : syracuseStep 261988607 = 392982911) B392982911
theorem B258392429 : Blo 1657528 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B8962447 : Blo 1657528 8962447 := bstep (se 1 (by rfl) ⟨6721835, by rfl⟩ : syracuseStep 8962447 = 13443671) B13443671
theorem B14164379 : Blo 1657528 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B6300139 : Blo 1657528 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B4482155 : Blo 1657528 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B8398079 : Blo 1657528 8398079 := bstep (se 1 (by rfl) ⟨6298559, by rfl⟩ : syracuseStep 8398079 = 12597119) B12597119
theorem B3147731 : Blo 1657528 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B5597423 : Blo 1657528 5597423 := bstep (se 1 (by rfl) ⟨4198067, by rfl⟩ : syracuseStep 5597423 = 8396135) B8396135
theorem B45984115 : Blo 1657528 45984115 := bstep (se 1 (by rfl) ⟨34488086, by rfl⟩ : syracuseStep 45984115 = 68976173) B68976173
theorem B8506075 : Blo 1657528 8506075 := bstep (se 1 (by rfl) ⟨6379556, by rfl⟩ : syracuseStep 8506075 = 12759113) B12759113
theorem B4197217 : Blo 1657528 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B1657983 : Blo 1657528 1657983 := bstep (se 1 (by rfl) ⟨1243487, by rfl⟩ : syracuseStep 1657983 = 2486975) B2486975
theorem B2486567 : Blo 1657528 2486567 := bstep (se 1 (by rfl) ⟨1864925, by rfl⟩ : syracuseStep 2486567 = 3729851) B3729851
theorem B31871393 : Blo 1657528 31871393 := bstep (se 2 (by rfl) ⟨11951772, by rfl⟩ : syracuseStep 31871393 = 23903545) B23903545
theorem B11956733 : Blo 1657528 11956733 := bstep (se 3 (by rfl) ⟨2241887, by rfl⟩ : syracuseStep 11956733 = 4483775) B4483775
theorem B2798239 : Blo 1657528 2798239 := bstep (se 1 (by rfl) ⟨2098679, by rfl⟩ : syracuseStep 2798239 = 4197359) B4197359
theorem B5600447 : Blo 1657528 5600447 := bstep (se 1 (by rfl) ⟨4200335, by rfl⟩ : syracuseStep 5600447 = 8400671) B8400671
theorem B1865119 : Blo 1657528 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B2487839 : Blo 1657528 2487839 := bstep (se 1 (by rfl) ⟨1865879, by rfl⟩ : syracuseStep 2487839 = 3731759) B3731759
theorem B96933671 : Blo 1657528 96933671 := bstep (se 1 (by rfl) ⟨72700253, by rfl⟩ : syracuseStep 96933671 = 145400507) B145400507
theorem B2489063 : Blo 1657528 2489063 := bstep (se 1 (by rfl) ⟨1866797, by rfl⟩ : syracuseStep 2489063 = 3733595) B3733595
theorem B2489225 : Blo 1657528 2489225 := bstep (se 2 (by rfl) ⟨933459, by rfl⟩ : syracuseStep 2489225 = 1866919) B1866919
theorem B21544343 : Blo 1657528 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B172261619 : Blo 1657528 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B7971155 : Blo 1657528 7971155 := bstep (se 1 (by rfl) ⟨5978366, by rfl⟩ : syracuseStep 7971155 = 11956733) B11956733
theorem B5596289 : Blo 1657528 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B2098487 : Blo 1657528 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B14362895 : Blo 1657528 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B1657711 : Blo 1657528 1657711 := bstep (se 1 (by rfl) ⟨1243283, by rfl⟩ : syracuseStep 1657711 = 2486567) B2486567
theorem B61312153 : Blo 1657528 61312153 := bstep (se 2 (by rfl) ⟨22992057, by rfl⟩ : syracuseStep 61312153 = 45984115) B45984115
theorem B8400185 : Blo 1657528 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B5598719 : Blo 1657528 5598719 := bstep (se 1 (by rfl) ⟨4199039, by rfl⟩ : syracuseStep 5598719 = 8398079) B8398079
theorem B3730985 : Blo 1657528 3730985 := bstep (se 2 (by rfl) ⟨1399119, by rfl⟩ : syracuseStep 3730985 = 2798239) B2798239
theorem B11341433 : Blo 1657528 11341433 := bstep (se 2 (by rfl) ⟨4253037, by rfl⟩ : syracuseStep 11341433 = 8506075) B8506075
theorem B1658559 : Blo 1657528 1658559 := bstep (se 1 (by rfl) ⟨1243919, by rfl⟩ : syracuseStep 1658559 = 2487839) B2487839
theorem B64622447 : Blo 1657528 64622447 := bstep (se 1 (by rfl) ⟨48466835, by rfl⟩ : syracuseStep 64622447 = 96933671) B96933671
theorem B3731615 : Blo 1657528 3731615 := bstep (se 1 (by rfl) ⟨2798711, by rfl⟩ : syracuseStep 3731615 = 5597423) B5597423
theorem B1659375 : Blo 1657528 1659375 := bstep (se 1 (by rfl) ⟨1244531, by rfl⟩ : syracuseStep 1659375 = 2489063) B2489063
theorem B2486825 : Blo 1657528 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B1659483 : Blo 1657528 1659483 := bstep (se 1 (by rfl) ⟨1244612, by rfl⟩ : syracuseStep 1659483 = 2489225) B2489225
theorem B9442919 : Blo 1657528 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B21247595 : Blo 1657528 21247595 := bstep (se 1 (by rfl) ⟨15935696, by rfl⟩ : syracuseStep 21247595 = 31871393) B31871393
theorem B11949929 : Blo 1657528 11949929 := bstep (se 2 (by rfl) ⟨4481223, by rfl⟩ : syracuseStep 11949929 = 8962447) B8962447
theorem B698636285 : Blo 1657528 698636285 := bstep (se 3 (by rfl) ⟨130994303, by rfl⟩ : syracuseStep 698636285 = 261988607) B261988607
theorem B2988103 : Blo 1657528 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B3733631 : Blo 1657528 3733631 := bstep (se 1 (by rfl) ⟨2800223, by rfl⟩ : syracuseStep 3733631 = 5600447) B5600447
theorem B5595965 : Blo 1657528 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B14165063 : Blo 1657528 14165063 := bstep (se 1 (by rfl) ⟨10623797, by rfl⟩ : syracuseStep 14165063 = 21247595) B21247595
theorem B465757523 : Blo 1657528 465757523 := bstep (se 1 (by rfl) ⟨349318142, by rfl⟩ : syracuseStep 465757523 = 698636285) B698636285
theorem B81749537 : Blo 1657528 81749537 := bstep (se 2 (by rfl) ⟨30656076, by rfl⟩ : syracuseStep 81749537 = 61312153) B61312153
theorem B3984137 : Blo 1657528 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B1657883 : Blo 1657528 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B3730859 : Blo 1657528 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B6295279 : Blo 1657528 6295279 := bstep (se 1 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 6295279 = 9442919) B9442919
theorem B7966619 : Blo 1657528 7966619 := bstep (se 1 (by rfl) ⟨5974964, by rfl⟩ : syracuseStep 7966619 = 11949929) B11949929
theorem B5600123 : Blo 1657528 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B3732479 : Blo 1657528 3732479 := bstep (se 1 (by rfl) ⟨2799359, by rfl⟩ : syracuseStep 3732479 = 5598719) B5598719
theorem B2487323 : Blo 1657528 2487323 := bstep (se 1 (by rfl) ⟨1865492, by rfl⟩ : syracuseStep 2487323 = 3730985) B3730985
theorem B2487743 : Blo 1657528 2487743 := bstep (se 1 (by rfl) ⟨1865807, by rfl⟩ : syracuseStep 2487743 = 3731615) B3731615
theorem B114841079 : Blo 1657528 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B5314103 : Blo 1657528 5314103 := bstep (se 1 (by rfl) ⟨3985577, by rfl⟩ : syracuseStep 5314103 = 7971155) B7971155
theorem B2489087 : Blo 1657528 2489087 := bstep (se 1 (by rfl) ⟨1866815, by rfl⟩ : syracuseStep 2489087 = 3733631) B3733631
theorem B9575263 : Blo 1657528 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B7560955 : Blo 1657528 7560955 := bstep (se 1 (by rfl) ⟨5670716, by rfl⟩ : syracuseStep 7560955 = 11341433) B11341433
theorem B43081631 : Blo 1657528 43081631 := bstep (se 1 (by rfl) ⟨32311223, by rfl⟩ : syracuseStep 43081631 = 64622447) B64622447
theorem B2656091 : Blo 1657528 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B5311079 : Blo 1657528 5311079 := bstep (se 1 (by rfl) ⟨3983309, by rfl⟩ : syracuseStep 5311079 = 7966619) B7966619
theorem B3730643 : Blo 1657528 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B1658215 : Blo 1657528 1658215 := bstep (se 1 (by rfl) ⟨1243661, by rfl⟩ : syracuseStep 1658215 = 2487323) B2487323
theorem B310505015 : Blo 1657528 310505015 := bstep (se 1 (by rfl) ⟨232878761, by rfl⟩ : syracuseStep 310505015 = 465757523) B465757523
theorem B1658495 : Blo 1657528 1658495 := bstep (se 1 (by rfl) ⟨1243871, by rfl⟩ : syracuseStep 1658495 = 2487743) B2487743
theorem B3542735 : Blo 1657528 3542735 := bstep (se 1 (by rfl) ⟨2657051, by rfl⟩ : syracuseStep 3542735 = 5314103) B5314103
theorem B1659391 : Blo 1657528 1659391 := bstep (se 1 (by rfl) ⟨1244543, by rfl⟩ : syracuseStep 1659391 = 2489087) B2489087
theorem B2487239 : Blo 1657528 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B8393705 : Blo 1657528 8393705 := bstep (se 2 (by rfl) ⟨3147639, by rfl⟩ : syracuseStep 8393705 = 6295279) B6295279
theorem B10081273 : Blo 1657528 10081273 := bstep (se 2 (by rfl) ⟨3780477, by rfl⟩ : syracuseStep 10081273 = 7560955) B7560955
theorem B3733415 : Blo 1657528 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B2488319 : Blo 1657528 2488319 := bstep (se 1 (by rfl) ⟨1866239, by rfl⟩ : syracuseStep 2488319 = 3732479) B3732479
theorem B9443375 : Blo 1657528 9443375 := bstep (se 1 (by rfl) ⟨7082531, by rfl⟩ : syracuseStep 9443375 = 14165063) B14165063
theorem B76560719 : Blo 1657528 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B54499691 : Blo 1657528 54499691 := bstep (se 1 (by rfl) ⟨40874768, by rfl⟩ : syracuseStep 54499691 = 81749537) B81749537
theorem B51068069 : Blo 1657528 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B28721087 : Blo 1657528 28721087 := bstep (se 1 (by rfl) ⟨21540815, by rfl⟩ : syracuseStep 28721087 = 43081631) B43081631
theorem B5595803 : Blo 1657528 5595803 := bstep (se 1 (by rfl) ⟨4196852, by rfl⟩ : syracuseStep 5595803 = 8393705) B8393705
theorem B204161917 : Blo 1657528 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B36333127 : Blo 1657528 36333127 := bstep (se 1 (by rfl) ⟨27249845, by rfl⟩ : syracuseStep 36333127 = 54499691) B54499691
theorem B3540719 : Blo 1657528 3540719 := bstep (se 1 (by rfl) ⟨2655539, by rfl⟩ : syracuseStep 3540719 = 5311079) B5311079
theorem B9447293 : Blo 1657528 9447293 := bstep (se 3 (by rfl) ⟨1771367, by rfl⟩ : syracuseStep 9447293 = 3542735) B3542735
theorem B19147391 : Blo 1657528 19147391 := bstep (se 1 (by rfl) ⟨14360543, by rfl⟩ : syracuseStep 19147391 = 28721087) B28721087
theorem B1658159 : Blo 1657528 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B1658879 : Blo 1657528 1658879 := bstep (se 1 (by rfl) ⟨1244159, by rfl⟩ : syracuseStep 1658879 = 2488319) B2488319
theorem B6295583 : Blo 1657528 6295583 := bstep (se 1 (by rfl) ⟨4721687, by rfl⟩ : syracuseStep 6295583 = 9443375) B9443375
theorem B2487095 : Blo 1657528 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B7082909 : Blo 1657528 7082909 := bstep (se 3 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 7082909 = 2656091) B2656091
theorem B2488943 : Blo 1657528 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B13441697 : Blo 1657528 13441697 := bstep (se 2 (by rfl) ⟨5040636, by rfl⟩ : syracuseStep 13441697 = 10081273) B10081273
theorem B828013373 : Blo 1657528 828013373 := bstep (se 3 (by rfl) ⟨155252507, by rfl⟩ : syracuseStep 828013373 = 310505015) B310505015
theorem B34045379 : Blo 1657528 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B12764927 : Blo 1657528 12764927 := bstep (se 1 (by rfl) ⟨9573695, by rfl⟩ : syracuseStep 12764927 = 19147391) B19147391
theorem B4197055 : Blo 1657528 4197055 := bstep (se 1 (by rfl) ⟨3147791, by rfl⟩ : syracuseStep 4197055 = 6295583) B6295583
theorem B3730535 : Blo 1657528 3730535 := bstep (se 1 (by rfl) ⟨2797901, by rfl⟩ : syracuseStep 3730535 = 5595803) B5595803
theorem B1658063 : Blo 1657528 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B4721939 : Blo 1657528 4721939 := bstep (se 1 (by rfl) ⟨3541454, by rfl⟩ : syracuseStep 4721939 = 7082909) B7082909
theorem B272215889 : Blo 1657528 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1659295 : Blo 1657528 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B9441917 : Blo 1657528 9441917 := bstep (se 3 (by rfl) ⟨1770359, by rfl⟩ : syracuseStep 9441917 = 3540719) B3540719
theorem B48444169 : Blo 1657528 48444169 := bstep (se 2 (by rfl) ⟨18166563, by rfl⟩ : syracuseStep 48444169 = 36333127) B36333127
theorem B22696919 : Blo 1657528 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B6298195 : Blo 1657528 6298195 := bstep (se 1 (by rfl) ⟨4723646, by rfl⟩ : syracuseStep 6298195 = 9447293) B9447293
theorem B8961131 : Blo 1657528 8961131 := bstep (se 1 (by rfl) ⟨6720848, by rfl⟩ : syracuseStep 8961131 = 13441697) B13441697
theorem B552008915 : Blo 1657528 552008915 := bstep (se 1 (by rfl) ⟨414006686, by rfl⟩ : syracuseStep 552008915 = 828013373) B828013373
theorem B15131279 : Blo 1657528 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B8397593 : Blo 1657528 8397593 := bstep (se 2 (by rfl) ⟨3149097, by rfl⟩ : syracuseStep 8397593 = 6298195) B6298195
theorem B5596073 : Blo 1657528 5596073 := bstep (se 2 (by rfl) ⟨2098527, by rfl⟩ : syracuseStep 5596073 = 4197055) B4197055
theorem B5974087 : Blo 1657528 5974087 := bstep (se 1 (by rfl) ⟨4480565, by rfl⟩ : syracuseStep 5974087 = 8961131) B8961131
theorem B3147959 : Blo 1657528 3147959 := bstep (se 1 (by rfl) ⟨2360969, by rfl⟩ : syracuseStep 3147959 = 4721939) B4721939
theorem B6294611 : Blo 1657528 6294611 := bstep (se 1 (by rfl) ⟨4720958, by rfl⟩ : syracuseStep 6294611 = 9441917) B9441917
theorem B2487023 : Blo 1657528 2487023 := bstep (se 1 (by rfl) ⟨1865267, by rfl⟩ : syracuseStep 2487023 = 3730535) B3730535
theorem B368005943 : Blo 1657528 368005943 := bstep (se 1 (by rfl) ⟨276004457, by rfl⟩ : syracuseStep 368005943 = 552008915) B552008915
theorem B64592225 : Blo 1657528 64592225 := bstep (se 2 (by rfl) ⟨24222084, by rfl⟩ : syracuseStep 64592225 = 48444169) B48444169
theorem B8509951 : Blo 1657528 8509951 := bstep (se 1 (by rfl) ⟨6382463, by rfl⟩ : syracuseStep 8509951 = 12764927) B12764927
theorem B181477259 : Blo 1657528 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B11346601 : Blo 1657528 11346601 := bstep (se 2 (by rfl) ⟨4254975, by rfl⟩ : syracuseStep 11346601 = 8509951) B8509951
theorem B2098639 : Blo 1657528 2098639 := bstep (se 1 (by rfl) ⟨1573979, by rfl⟩ : syracuseStep 2098639 = 3147959) B3147959
theorem B4196407 : Blo 1657528 4196407 := bstep (se 1 (by rfl) ⟨3147305, by rfl⟩ : syracuseStep 4196407 = 6294611) B6294611
theorem B7965449 : Blo 1657528 7965449 := bstep (se 2 (by rfl) ⟨2987043, by rfl⟩ : syracuseStep 7965449 = 5974087) B5974087
theorem B10087519 : Blo 1657528 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B1658015 : Blo 1657528 1658015 := bstep (se 1 (by rfl) ⟨1243511, by rfl⟩ : syracuseStep 1658015 = 2487023) B2487023
theorem B5598395 : Blo 1657528 5598395 := bstep (se 1 (by rfl) ⟨4198796, by rfl⟩ : syracuseStep 5598395 = 8397593) B8397593
theorem B245337295 : Blo 1657528 245337295 := bstep (se 1 (by rfl) ⟨184002971, by rfl⟩ : syracuseStep 245337295 = 368005943) B368005943
theorem B3730715 : Blo 1657528 3730715 := bstep (se 1 (by rfl) ⟨2798036, by rfl⟩ : syracuseStep 3730715 = 5596073) B5596073
theorem B43061483 : Blo 1657528 43061483 := bstep (se 1 (by rfl) ⟨32296112, by rfl⟩ : syracuseStep 43061483 = 64592225) B64592225
theorem B120984839 : Blo 1657528 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B5595209 : Blo 1657528 5595209 := bstep (se 2 (by rfl) ⟨2098203, by rfl⟩ : syracuseStep 5595209 = 4196407) B4196407
theorem B327116393 : Blo 1657528 327116393 := bstep (se 2 (by rfl) ⟨122668647, by rfl⟩ : syracuseStep 327116393 = 245337295) B245337295
theorem B5310299 : Blo 1657528 5310299 := bstep (se 1 (by rfl) ⟨3982724, by rfl⟩ : syracuseStep 5310299 = 7965449) B7965449
theorem B28707655 : Blo 1657528 28707655 := bstep (se 1 (by rfl) ⟨21530741, by rfl⟩ : syracuseStep 28707655 = 43061483) B43061483
theorem B2798185 : Blo 1657528 2798185 := bstep (se 2 (by rfl) ⟨1049319, by rfl⟩ : syracuseStep 2798185 = 2098639) B2098639
theorem B3732263 : Blo 1657528 3732263 := bstep (se 1 (by rfl) ⟨2799197, by rfl⟩ : syracuseStep 3732263 = 5598395) B5598395
theorem B2487143 : Blo 1657528 2487143 := bstep (se 1 (by rfl) ⟨1865357, by rfl⟩ : syracuseStep 2487143 = 3730715) B3730715
theorem B80656559 : Blo 1657528 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B15128801 : Blo 1657528 15128801 := bstep (se 2 (by rfl) ⟨5673300, by rfl⟩ : syracuseStep 15128801 = 11346601) B11346601
theorem B13450025 : Blo 1657528 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B3540199 : Blo 1657528 3540199 := bstep (se 1 (by rfl) ⟨2655149, by rfl⟩ : syracuseStep 3540199 = 5310299) B5310299
theorem B10085867 : Blo 1657528 10085867 := bstep (se 1 (by rfl) ⟨7564400, by rfl⟩ : syracuseStep 10085867 = 15128801) B15128801
theorem B3730139 : Blo 1657528 3730139 := bstep (se 1 (by rfl) ⟨2797604, by rfl⟩ : syracuseStep 3730139 = 5595209) B5595209
theorem B1658095 : Blo 1657528 1658095 := bstep (se 1 (by rfl) ⟨1243571, by rfl⟩ : syracuseStep 1658095 = 2487143) B2487143
theorem B3730913 : Blo 1657528 3730913 := bstep (se 2 (by rfl) ⟨1399092, by rfl⟩ : syracuseStep 3730913 = 2798185) B2798185
theorem B38276873 : Blo 1657528 38276873 := bstep (se 2 (by rfl) ⟨14353827, by rfl⟩ : syracuseStep 38276873 = 28707655) B28707655
theorem B8966683 : Blo 1657528 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B2488175 : Blo 1657528 2488175 := bstep (se 1 (by rfl) ⟨1866131, by rfl⟩ : syracuseStep 2488175 = 3732263) B3732263
theorem B218077595 : Blo 1657528 218077595 := bstep (se 1 (by rfl) ⟨163558196, by rfl⟩ : syracuseStep 218077595 = 327116393) B327116393
theorem B53771039 : Blo 1657528 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B145385063 : Blo 1657528 145385063 := bstep (se 1 (by rfl) ⟨109038797, by rfl⟩ : syracuseStep 145385063 = 218077595) B218077595
theorem B4720265 : Blo 1657528 4720265 := bstep (se 2 (by rfl) ⟨1770099, by rfl⟩ : syracuseStep 4720265 = 3540199) B3540199
theorem B1658783 : Blo 1657528 1658783 := bstep (se 1 (by rfl) ⟨1244087, by rfl⟩ : syracuseStep 1658783 = 2488175) B2488175
theorem B2486759 : Blo 1657528 2486759 := bstep (se 1 (by rfl) ⟨1865069, by rfl⟩ : syracuseStep 2486759 = 3730139) B3730139
theorem B2487275 : Blo 1657528 2487275 := bstep (se 1 (by rfl) ⟨1865456, by rfl⟩ : syracuseStep 2487275 = 3730913) B3730913
theorem B47822309 : Blo 1657528 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B6723911 : Blo 1657528 6723911 := bstep (se 1 (by rfl) ⟨5042933, by rfl⟩ : syracuseStep 6723911 = 10085867) B10085867
theorem B35847359 : Blo 1657528 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B25517915 : Blo 1657528 25517915 := bstep (se 1 (by rfl) ⟨19138436, by rfl⟩ : syracuseStep 25517915 = 38276873) B38276873
theorem B3146843 : Blo 1657528 3146843 := bstep (se 1 (by rfl) ⟨2360132, by rfl⟩ : syracuseStep 3146843 = 4720265) B4720265
theorem B23898239 : Blo 1657528 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B1657839 : Blo 1657528 1657839 := bstep (se 1 (by rfl) ⟨1243379, by rfl⟩ : syracuseStep 1657839 = 2486759) B2486759
theorem B1658183 : Blo 1657528 1658183 := bstep (se 1 (by rfl) ⟨1243637, by rfl⟩ : syracuseStep 1658183 = 2487275) B2487275
theorem B96923375 : Blo 1657528 96923375 := bstep (se 1 (by rfl) ⟨72692531, by rfl⟩ : syracuseStep 96923375 = 145385063) B145385063
theorem B17011943 : Blo 1657528 17011943 := bstep (se 1 (by rfl) ⟨12758957, by rfl⟩ : syracuseStep 17011943 = 25517915) B25517915
theorem B17930429 : Blo 1657528 17930429 := bstep (se 3 (by rfl) ⟨3361955, by rfl⟩ : syracuseStep 17930429 = 6723911) B6723911
theorem B31881539 : Blo 1657528 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B2097895 : Blo 1657528 2097895 := bstep (se 1 (by rfl) ⟨1573421, by rfl⟩ : syracuseStep 2097895 = 3146843) B3146843
theorem B11953619 : Blo 1657528 11953619 := bstep (se 1 (by rfl) ⟨8965214, by rfl⟩ : syracuseStep 11953619 = 17930429) B17930429
theorem B11341295 : Blo 1657528 11341295 := bstep (se 1 (by rfl) ⟨8505971, by rfl⟩ : syracuseStep 11341295 = 17011943) B17011943
theorem B21254359 : Blo 1657528 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B64615583 : Blo 1657528 64615583 := bstep (se 1 (by rfl) ⟨48461687, by rfl⟩ : syracuseStep 64615583 = 96923375) B96923375
theorem B15932159 : Blo 1657528 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B28339145 : Blo 1657528 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B43077055 : Blo 1657528 43077055 := bstep (se 1 (by rfl) ⟨32307791, by rfl⟩ : syracuseStep 43077055 = 64615583) B64615583
theorem B2797193 : Blo 1657528 2797193 := bstep (se 2 (by rfl) ⟨1048947, by rfl⟩ : syracuseStep 2797193 = 2097895) B2097895
theorem B10621439 : Blo 1657528 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B7969079 : Blo 1657528 7969079 := bstep (se 1 (by rfl) ⟨5976809, by rfl⟩ : syracuseStep 7969079 = 11953619) B11953619
theorem B7560863 : Blo 1657528 7560863 := bstep (se 1 (by rfl) ⟨5670647, by rfl⟩ : syracuseStep 7560863 = 11341295) B11341295
theorem B57436073 : Blo 1657528 57436073 := bstep (se 2 (by rfl) ⟨21538527, by rfl⟩ : syracuseStep 57436073 = 43077055) B43077055
theorem B18892763 : Blo 1657528 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B5040575 : Blo 1657528 5040575 := bstep (se 1 (by rfl) ⟨3780431, by rfl⟩ : syracuseStep 5040575 = 7560863) B7560863
theorem B7080959 : Blo 1657528 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B5312719 : Blo 1657528 5312719 := bstep (se 1 (by rfl) ⟨3984539, by rfl⟩ : syracuseStep 5312719 = 7969079) B7969079
theorem B1864795 : Blo 1657528 1864795 := bstep (se 1 (by rfl) ⟨1398596, by rfl⟩ : syracuseStep 1864795 = 2797193) B2797193
theorem B38290715 : Blo 1657528 38290715 := bstep (se 1 (by rfl) ⟨28718036, by rfl⟩ : syracuseStep 38290715 = 57436073) B57436073
theorem B3360383 : Blo 1657528 3360383 := bstep (se 1 (by rfl) ⟨2520287, by rfl⟩ : syracuseStep 3360383 = 5040575) B5040575
theorem B12595175 : Blo 1657528 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B2486393 : Blo 1657528 2486393 := bstep (se 2 (by rfl) ⟨932397, by rfl⟩ : syracuseStep 2486393 = 1864795) B1864795
theorem B7083625 : Blo 1657528 7083625 := bstep (se 2 (by rfl) ⟨2656359, by rfl⟩ : syracuseStep 7083625 = 5312719) B5312719
theorem B18882557 : Blo 1657528 18882557 := bstep (se 3 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 18882557 = 7080959) B7080959
theorem B25527143 : Blo 1657528 25527143 := bstep (se 1 (by rfl) ⟨19145357, by rfl⟩ : syracuseStep 25527143 = 38290715) B38290715
theorem B1657595 : Blo 1657528 1657595 := bstep (se 1 (by rfl) ⟨1243196, by rfl⟩ : syracuseStep 1657595 = 2486393) B2486393
theorem B2240255 : Blo 1657528 2240255 := bstep (se 1 (by rfl) ⟨1680191, by rfl⟩ : syracuseStep 2240255 = 3360383) B3360383
theorem B12588371 : Blo 1657528 12588371 := bstep (se 1 (by rfl) ⟨9441278, by rfl⟩ : syracuseStep 12588371 = 18882557) B18882557
theorem B9444833 : Blo 1657528 9444833 := bstep (se 2 (by rfl) ⟨3541812, by rfl⟩ : syracuseStep 9444833 = 7083625) B7083625
theorem B8396783 : Blo 1657528 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B5974013 : Blo 1657528 5974013 := bstep (se 3 (by rfl) ⟨1120127, by rfl⟩ : syracuseStep 5974013 = 2240255) B2240255
theorem B5597855 : Blo 1657528 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B17018095 : Blo 1657528 17018095 := bstep (se 1 (by rfl) ⟨12763571, by rfl⟩ : syracuseStep 17018095 = 25527143) B25527143
theorem B8392247 : Blo 1657528 8392247 := bstep (se 1 (by rfl) ⟨6294185, by rfl⟩ : syracuseStep 8392247 = 12588371) B12588371
theorem B6296555 : Blo 1657528 6296555 := bstep (se 1 (by rfl) ⟨4722416, by rfl⟩ : syracuseStep 6296555 = 9444833) B9444833
theorem B4197703 : Blo 1657528 4197703 := bstep (se 1 (by rfl) ⟨3148277, by rfl⟩ : syracuseStep 4197703 = 6296555) B6296555
theorem B3731903 : Blo 1657528 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B15930701 : Blo 1657528 15930701 := bstep (se 3 (by rfl) ⟨2987006, by rfl⟩ : syracuseStep 15930701 = 5974013) B5974013
theorem B22690793 : Blo 1657528 22690793 := bstep (se 2 (by rfl) ⟨8509047, by rfl⟩ : syracuseStep 22690793 = 17018095) B17018095
theorem B5594831 : Blo 1657528 5594831 := bstep (se 1 (by rfl) ⟨4196123, by rfl⟩ : syracuseStep 5594831 = 8392247) B8392247
theorem B5596937 : Blo 1657528 5596937 := bstep (se 2 (by rfl) ⟨2098851, by rfl⟩ : syracuseStep 5596937 = 4197703) B4197703
theorem B3729887 : Blo 1657528 3729887 := bstep (se 1 (by rfl) ⟨2797415, by rfl⟩ : syracuseStep 3729887 = 5594831) B5594831
theorem B10620467 : Blo 1657528 10620467 := bstep (se 1 (by rfl) ⟨7965350, by rfl⟩ : syracuseStep 10620467 = 15930701) B15930701
theorem B15127195 : Blo 1657528 15127195 := bstep (se 1 (by rfl) ⟨11345396, by rfl⟩ : syracuseStep 15127195 = 22690793) B22690793
theorem B2487935 : Blo 1657528 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B20169593 : Blo 1657528 20169593 := bstep (se 2 (by rfl) ⟨7563597, by rfl⟩ : syracuseStep 20169593 = 15127195) B15127195
theorem B7080311 : Blo 1657528 7080311 := bstep (se 1 (by rfl) ⟨5310233, by rfl⟩ : syracuseStep 7080311 = 10620467) B10620467
theorem B1658623 : Blo 1657528 1658623 := bstep (se 1 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 1658623 = 2487935) B2487935
theorem B3731291 : Blo 1657528 3731291 := bstep (se 1 (by rfl) ⟨2798468, by rfl⟩ : syracuseStep 3731291 = 5596937) B5596937
theorem B2486591 : Blo 1657528 2486591 := bstep (se 1 (by rfl) ⟨1864943, by rfl⟩ : syracuseStep 2486591 = 3729887) B3729887
theorem B4720207 : Blo 1657528 4720207 := bstep (se 1 (by rfl) ⟨3540155, by rfl⟩ : syracuseStep 4720207 = 7080311) B7080311
theorem B1657727 : Blo 1657528 1657727 := bstep (se 1 (by rfl) ⟨1243295, by rfl⟩ : syracuseStep 1657727 = 2486591) B2486591
theorem B13446395 : Blo 1657528 13446395 := bstep (se 1 (by rfl) ⟨10084796, by rfl⟩ : syracuseStep 13446395 = 20169593) B20169593
theorem B2487527 : Blo 1657528 2487527 := bstep (se 1 (by rfl) ⟨1865645, by rfl⟩ : syracuseStep 2487527 = 3731291) B3731291
theorem B6293609 : Blo 1657528 6293609 := bstep (se 2 (by rfl) ⟨2360103, by rfl⟩ : syracuseStep 6293609 = 4720207) B4720207
theorem B8964263 : Blo 1657528 8964263 := bstep (se 1 (by rfl) ⟨6723197, by rfl⟩ : syracuseStep 8964263 = 13446395) B13446395
theorem B1658351 : Blo 1657528 1658351 := bstep (se 1 (by rfl) ⟨1243763, by rfl⟩ : syracuseStep 1658351 = 2487527) B2487527
theorem B4195739 : Blo 1657528 4195739 := bstep (se 1 (by rfl) ⟨3146804, by rfl⟩ : syracuseStep 4195739 = 6293609) B6293609
theorem B5976175 : Blo 1657528 5976175 := bstep (se 1 (by rfl) ⟨4482131, by rfl⟩ : syracuseStep 5976175 = 8964263) B8964263
theorem B2797159 : Blo 1657528 2797159 := bstep (se 1 (by rfl) ⟨2097869, by rfl⟩ : syracuseStep 2797159 = 4195739) B4195739
theorem B7968233 : Blo 1657528 7968233 := bstep (se 2 (by rfl) ⟨2988087, by rfl⟩ : syracuseStep 7968233 = 5976175) B5976175
theorem B3729545 : Blo 1657528 3729545 := bstep (se 2 (by rfl) ⟨1398579, by rfl⟩ : syracuseStep 3729545 = 2797159) B2797159
theorem B5312155 : Blo 1657528 5312155 := bstep (se 1 (by rfl) ⟨3984116, by rfl⟩ : syracuseStep 5312155 = 7968233) B7968233
theorem B2486363 : Blo 1657528 2486363 := bstep (se 1 (by rfl) ⟨1864772, by rfl⟩ : syracuseStep 2486363 = 3729545) B3729545
theorem B7082873 : Blo 1657528 7082873 := bstep (se 2 (by rfl) ⟨2656077, by rfl⟩ : syracuseStep 7082873 = 5312155) B5312155
theorem B1657575 : Blo 1657528 1657575 := bstep (se 1 (by rfl) ⟨1243181, by rfl⟩ : syracuseStep 1657575 = 2486363) B2486363
theorem B4721915 : Blo 1657528 4721915 := bstep (se 1 (by rfl) ⟨3541436, by rfl⟩ : syracuseStep 4721915 = 7082873) B7082873
theorem B12591773 : Blo 1657528 12591773 := bstep (se 3 (by rfl) ⟨2360957, by rfl⟩ : syracuseStep 12591773 = 4721915) B4721915
theorem B8394515 : Blo 1657528 8394515 := bstep (se 1 (by rfl) ⟨6295886, by rfl⟩ : syracuseStep 8394515 = 12591773) B12591773
theorem B5596343 : Blo 1657528 5596343 := bstep (se 1 (by rfl) ⟨4197257, by rfl⟩ : syracuseStep 5596343 = 8394515) B8394515
theorem B3730895 : Blo 1657528 3730895 := bstep (se 1 (by rfl) ⟨2798171, by rfl⟩ : syracuseStep 3730895 = 5596343) B5596343
theorem B2487263 : Blo 1657528 2487263 := bstep (se 1 (by rfl) ⟨1865447, by rfl⟩ : syracuseStep 2487263 = 3730895) B3730895
theorem B1658175 : Blo 1657528 1658175 := bstep (se 1 (by rfl) ⟨1243631, by rfl⟩ : syracuseStep 1658175 = 2487263) B2487263

theorem C0 (j : ℕ) (h1 : 414382 ≤ j) (h2 : j ≤ 414881) : Blo 1657528 (4 * j + 3) := by
  interval_cases j
  · exact B1657531
  · exact B1657535
  · exact B1657539
  · exact B1657543
  · exact B1657547
  · exact B1657551
  · exact B1657555
  · exact B1657559
  · exact B1657563
  · exact B1657567
  · exact B1657571
  · exact B1657575
  · exact B1657579
  · exact B1657583
  · exact B1657587
  · exact B1657591
  · exact B1657595
  · exact B1657599
  · exact B1657603
  · exact B1657607
  · exact B1657611
  · exact B1657615
  · exact B1657619
  · exact B1657623
  · exact B1657627
  · exact B1657631
  · exact B1657635
  · exact B1657639
  · exact B1657643
  · exact B1657647
  · exact B1657651
  · exact B1657655
  · exact B1657659
  · exact B1657663
  · exact B1657667
  · exact B1657671
  · exact B1657675
  · exact B1657679
  · exact B1657683
  · exact B1657687
  · exact B1657691
  · exact B1657695
  · exact B1657699
  · exact B1657703
  · exact B1657707
  · exact B1657711
  · exact B1657715
  · exact B1657719
  · exact B1657723
  · exact B1657727
  · exact B1657731
  · exact B1657735
  · exact B1657739
  · exact B1657743
  · exact B1657747
  · exact B1657751
  · exact B1657755
  · exact B1657759
  · exact B1657763
  · exact B1657767
  · exact B1657771
  · exact B1657775
  · exact B1657779
  · exact B1657783
  · exact B1657787
  · exact B1657791
  · exact B1657795
  · exact B1657799
  · exact B1657803
  · exact B1657807
  · exact B1657811
  · exact B1657815
  · exact B1657819
  · exact B1657823
  · exact B1657827
  · exact B1657831
  · exact B1657835
  · exact B1657839
  · exact B1657843
  · exact B1657847
  · exact B1657851
  · exact B1657855
  · exact B1657859
  · exact B1657863
  · exact B1657867
  · exact B1657871
  · exact B1657875
  · exact B1657879
  · exact B1657883
  · exact B1657887
  · exact B1657891
  · exact B1657895
  · exact B1657899
  · exact B1657903
  · exact B1657907
  · exact B1657911
  · exact B1657915
  · exact B1657919
  · exact B1657923
  · exact B1657927
  · exact B1657931
  · exact B1657935
  · exact B1657939
  · exact B1657943
  · exact B1657947
  · exact B1657951
  · exact B1657955
  · exact B1657959
  · exact B1657963
  · exact B1657967
  · exact B1657971
  · exact B1657975
  · exact B1657979
  · exact B1657983
  · exact B1657987
  · exact B1657991
  · exact B1657995
  · exact B1657999
  · exact B1658003
  · exact B1658007
  · exact B1658011
  · exact B1658015
  · exact B1658019
  · exact B1658023
  · exact B1658027
  · exact B1658031
  · exact B1658035
  · exact B1658039
  · exact B1658043
  · exact B1658047
  · exact B1658051
  · exact B1658055
  · exact B1658059
  · exact B1658063
  · exact B1658067
  · exact B1658071
  · exact B1658075
  · exact B1658079
  · exact B1658083
  · exact B1658087
  · exact B1658091
  · exact B1658095
  · exact B1658099
  · exact B1658103
  · exact B1658107
  · exact B1658111
  · exact B1658115
  · exact B1658119
  · exact B1658123
  · exact B1658127
  · exact B1658131
  · exact B1658135
  · exact B1658139
  · exact B1658143
  · exact B1658147
  · exact B1658151
  · exact B1658155
  · exact B1658159
  · exact B1658163
  · exact B1658167
  · exact B1658171
  · exact B1658175
  · exact B1658179
  · exact B1658183
  · exact B1658187
  · exact B1658191
  · exact B1658195
  · exact B1658199
  · exact B1658203
  · exact B1658207
  · exact B1658211
  · exact B1658215
  · exact B1658219
  · exact B1658223
  · exact B1658227
  · exact B1658231
  · exact B1658235
  · exact B1658239
  · exact B1658243
  · exact B1658247
  · exact B1658251
  · exact B1658255
  · exact B1658259
  · exact B1658263
  · exact B1658267
  · exact B1658271
  · exact B1658275
  · exact B1658279
  · exact B1658283
  · exact B1658287
  · exact B1658291
  · exact B1658295
  · exact B1658299
  · exact B1658303
  · exact B1658307
  · exact B1658311
  · exact B1658315
  · exact B1658319
  · exact B1658323
  · exact B1658327
  · exact B1658331
  · exact B1658335
  · exact B1658339
  · exact B1658343
  · exact B1658347
  · exact B1658351
  · exact B1658355
  · exact B1658359
  · exact B1658363
  · exact B1658367
  · exact B1658371
  · exact B1658375
  · exact B1658379
  · exact B1658383
  · exact B1658387
  · exact B1658391
  · exact B1658395
  · exact B1658399
  · exact B1658403
  · exact B1658407
  · exact B1658411
  · exact B1658415
  · exact B1658419
  · exact B1658423
  · exact B1658427
  · exact B1658431
  · exact B1658435
  · exact B1658439
  · exact B1658443
  · exact B1658447
  · exact B1658451
  · exact B1658455
  · exact B1658459
  · exact B1658463
  · exact B1658467
  · exact B1658471
  · exact B1658475
  · exact B1658479
  · exact B1658483
  · exact B1658487
  · exact B1658491
  · exact B1658495
  · exact B1658499
  · exact B1658503
  · exact B1658507
  · exact B1658511
  · exact B1658515
  · exact B1658519
  · exact B1658523
  · exact B1658527
  · exact B1658531
  · exact B1658535
  · exact B1658539
  · exact B1658543
  · exact B1658547
  · exact B1658551
  · exact B1658555
  · exact B1658559
  · exact B1658563
  · exact B1658567
  · exact B1658571
  · exact B1658575
  · exact B1658579
  · exact B1658583
  · exact B1658587
  · exact B1658591
  · exact B1658595
  · exact B1658599
  · exact B1658603
  · exact B1658607
  · exact B1658611
  · exact B1658615
  · exact B1658619
  · exact B1658623
  · exact B1658627
  · exact B1658631
  · exact B1658635
  · exact B1658639
  · exact B1658643
  · exact B1658647
  · exact B1658651
  · exact B1658655
  · exact B1658659
  · exact B1658663
  · exact B1658667
  · exact B1658671
  · exact B1658675
  · exact B1658679
  · exact B1658683
  · exact B1658687
  · exact B1658691
  · exact B1658695
  · exact B1658699
  · exact B1658703
  · exact B1658707
  · exact B1658711
  · exact B1658715
  · exact B1658719
  · exact B1658723
  · exact B1658727
  · exact B1658731
  · exact B1658735
  · exact B1658739
  · exact B1658743
  · exact B1658747
  · exact B1658751
  · exact B1658755
  · exact B1658759
  · exact B1658763
  · exact B1658767
  · exact B1658771
  · exact B1658775
  · exact B1658779
  · exact B1658783
  · exact B1658787
  · exact B1658791
  · exact B1658795
  · exact B1658799
  · exact B1658803
  · exact B1658807
  · exact B1658811
  · exact B1658815
  · exact B1658819
  · exact B1658823
  · exact B1658827
  · exact B1658831
  · exact B1658835
  · exact B1658839
  · exact B1658843
  · exact B1658847
  · exact B1658851
  · exact B1658855
  · exact B1658859
  · exact B1658863
  · exact B1658867
  · exact B1658871
  · exact B1658875
  · exact B1658879
  · exact B1658883
  · exact B1658887
  · exact B1658891
  · exact B1658895
  · exact B1658899
  · exact B1658903
  · exact B1658907
  · exact B1658911
  · exact B1658915
  · exact B1658919
  · exact B1658923
  · exact B1658927
  · exact B1658931
  · exact B1658935
  · exact B1658939
  · exact B1658943
  · exact B1658947
  · exact B1658951
  · exact B1658955
  · exact B1658959
  · exact B1658963
  · exact B1658967
  · exact B1658971
  · exact B1658975
  · exact B1658979
  · exact B1658983
  · exact B1658987
  · exact B1658991
  · exact B1658995
  · exact B1658999
  · exact B1659003
  · exact B1659007
  · exact B1659011
  · exact B1659015
  · exact B1659019
  · exact B1659023
  · exact B1659027
  · exact B1659031
  · exact B1659035
  · exact B1659039
  · exact B1659043
  · exact B1659047
  · exact B1659051
  · exact B1659055
  · exact B1659059
  · exact B1659063
  · exact B1659067
  · exact B1659071
  · exact B1659075
  · exact B1659079
  · exact B1659083
  · exact B1659087
  · exact B1659091
  · exact B1659095
  · exact B1659099
  · exact B1659103
  · exact B1659107
  · exact B1659111
  · exact B1659115
  · exact B1659119
  · exact B1659123
  · exact B1659127
  · exact B1659131
  · exact B1659135
  · exact B1659139
  · exact B1659143
  · exact B1659147
  · exact B1659151
  · exact B1659155
  · exact B1659159
  · exact B1659163
  · exact B1659167
  · exact B1659171
  · exact B1659175
  · exact B1659179
  · exact B1659183
  · exact B1659187
  · exact B1659191
  · exact B1659195
  · exact B1659199
  · exact B1659203
  · exact B1659207
  · exact B1659211
  · exact B1659215
  · exact B1659219
  · exact B1659223
  · exact B1659227
  · exact B1659231
  · exact B1659235
  · exact B1659239
  · exact B1659243
  · exact B1659247
  · exact B1659251
  · exact B1659255
  · exact B1659259
  · exact B1659263
  · exact B1659267
  · exact B1659271
  · exact B1659275
  · exact B1659279
  · exact B1659283
  · exact B1659287
  · exact B1659291
  · exact B1659295
  · exact B1659299
  · exact B1659303
  · exact B1659307
  · exact B1659311
  · exact B1659315
  · exact B1659319
  · exact B1659323
  · exact B1659327
  · exact B1659331
  · exact B1659335
  · exact B1659339
  · exact B1659343
  · exact B1659347
  · exact B1659351
  · exact B1659355
  · exact B1659359
  · exact B1659363
  · exact B1659367
  · exact B1659371
  · exact B1659375
  · exact B1659379
  · exact B1659383
  · exact B1659387
  · exact B1659391
  · exact B1659395
  · exact B1659399
  · exact B1659403
  · exact B1659407
  · exact B1659411
  · exact B1659415
  · exact B1659419
  · exact B1659423
  · exact B1659427
  · exact B1659431
  · exact B1659435
  · exact B1659439
  · exact B1659443
  · exact B1659447
  · exact B1659451
  · exact B1659455
  · exact B1659459
  · exact B1659463
  · exact B1659467
  · exact B1659471
  · exact B1659475
  · exact B1659479
  · exact B1659483
  · exact B1659487
  · exact B1659491
  · exact B1659495
  · exact B1659499
  · exact B1659503
  · exact B1659507
  · exact B1659511
  · exact B1659515
  · exact B1659519
  · exact B1659523
  · exact B1659527

theorem solution (m : ℕ) (hlo : 1657528 ≤ m) (hhi : m ≤ 1659528) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 414382 ≤ j := by omega
    have hj2 : j ≤ 414881 := by omega
    have hb : Blo 1657528 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
