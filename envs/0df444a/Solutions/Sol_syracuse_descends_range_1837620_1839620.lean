-- Prove2me | solution 1 for syracuse_descends_range_1837620_1839620
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:02:41.161122+00:00
-- url     : https://prove2.me/submissions/f97a83d3-ddc5-43d7-8ad0-e4e5bc083497

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


theorem B7856149 : Blo 1837620 7856149 := bbase (se 6 (by rfl) ⟨184128, by rfl⟩ : syracuseStep 7856149 = 368257) (by norm_num)
theorem B4653085 : Blo 1837620 4653085 := bbase (se 3 (by rfl) ⟨872453, by rfl⟩ : syracuseStep 4653085 = 1744907) (by norm_num)
theorem B2326573 : Blo 1837620 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B4137029 : Blo 1837620 4137029 := bbase (se 4 (by rfl) ⟨387846, by rfl⟩ : syracuseStep 4137029 = 775693) (by norm_num)
theorem B2097257 : Blo 1837620 2097257 := bbase (se 2 (by rfl) ⟨786471, by rfl⟩ : syracuseStep 2097257 = 1572943) (by norm_num)
theorem B4653197 : Blo 1837620 4653197 := bbase (se 3 (by rfl) ⟨872474, by rfl⟩ : syracuseStep 4653197 = 1744949) (by norm_num)
theorem B4137101 : Blo 1837620 4137101 := bbase (se 3 (by rfl) ⟨775706, by rfl⟩ : syracuseStep 4137101 = 1551413) (by norm_num)
theorem B5890229 : Blo 1837620 5890229 := bbase (se 5 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 5890229 = 552209) (by norm_num)
theorem B4137173 : Blo 1837620 4137173 := bbase (se 7 (by rfl) ⟨48482, by rfl⟩ : syracuseStep 4137173 = 96965) (by norm_num)
theorem B2326745 : Blo 1837620 2326745 := bbase (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) (by norm_num)
theorem B15712501 : Blo 1837620 15712501 := bbase (se 5 (by rfl) ⟨736523, by rfl⟩ : syracuseStep 15712501 = 1473047) (by norm_num)
theorem B2326801 : Blo 1837620 2326801 := bbase (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) (by norm_num)
theorem B4137245 : Blo 1837620 4137245 := bbase (se 3 (by rfl) ⟨775733, by rfl⟩ : syracuseStep 4137245 = 1551467) (by norm_num)
theorem B2359589 : Blo 1837620 2359589 := bbase (se 4 (by rfl) ⟨221211, by rfl⟩ : syracuseStep 2359589 = 442423) (by norm_num)
theorem B4653389 : Blo 1837620 4653389 := bbase (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) (by norm_num)
theorem B3490141 : Blo 1837620 3490141 := bbase (se 3 (by rfl) ⟨654401, by rfl⟩ : syracuseStep 3490141 = 1308803) (by norm_num)
theorem B4137317 : Blo 1837620 4137317 := bbase (se 4 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 4137317 = 775747) (by norm_num)
theorem B2326897 : Blo 1837620 2326897 := bbase (se 2 (by rfl) ⟨872586, by rfl⟩ : syracuseStep 2326897 = 1745173) (by norm_num)
theorem B3981685 : Blo 1837620 3981685 := bbase (se 5 (by rfl) ⟨186641, by rfl⟩ : syracuseStep 3981685 = 373283) (by norm_num)
theorem B2359697 : Blo 1837620 2359697 := bbase (se 2 (by rfl) ⟨884886, by rfl⟩ : syracuseStep 2359697 = 1769773) (by norm_num)
theorem B4137389 : Blo 1837620 4137389 := bbase (se 3 (by rfl) ⟨775760, by rfl⟩ : syracuseStep 4137389 = 1551521) (by norm_num)
theorem B4415933 : Blo 1837620 4415933 := bbase (se 3 (by rfl) ⟨827987, by rfl⟩ : syracuseStep 4415933 = 1655975) (by norm_num)
theorem B6980053 : Blo 1837620 6980053 := bbase (se 7 (by rfl) ⟨81797, by rfl⟩ : syracuseStep 6980053 = 163595) (by norm_num)
theorem B3490285 : Blo 1837620 3490285 := bbase (se 3 (by rfl) ⟨654428, by rfl⟩ : syracuseStep 3490285 = 1308857) (by norm_num)
theorem B4137461 : Blo 1837620 4137461 := bbase (se 5 (by rfl) ⟨193943, by rfl⟩ : syracuseStep 4137461 = 387887) (by norm_num)
theorem B4416029 : Blo 1837620 4416029 := bbase (se 3 (by rfl) ⟨828005, by rfl⟩ : syracuseStep 4416029 = 1656011) (by norm_num)
theorem B2327069 : Blo 1837620 2327069 := bbase (se 3 (by rfl) ⟨436325, by rfl⟩ : syracuseStep 2327069 = 872651) (by norm_num)
theorem B3187253 : Blo 1837620 3187253 := bbase (se 5 (by rfl) ⟨149402, by rfl⟩ : syracuseStep 3187253 = 298805) (by norm_num)
theorem B4137533 : Blo 1837620 4137533 := bbase (se 3 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 4137533 = 1551575) (by norm_num)
theorem B2327125 : Blo 1837620 2327125 := bbase (se 8 (by rfl) ⟨13635, by rfl⟩ : syracuseStep 2327125 = 27271) (by norm_num)
theorem B4194917 : Blo 1837620 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B3359341 : Blo 1837620 3359341 := bbase (se 3 (by rfl) ⟨629876, by rfl⟩ : syracuseStep 3359341 = 1259753) (by norm_num)
theorem B4137605 : Blo 1837620 4137605 := bbase (se 4 (by rfl) ⟨387900, by rfl⟩ : syracuseStep 4137605 = 775801) (by norm_num)
theorem B3490445 : Blo 1837620 3490445 := bbase (se 3 (by rfl) ⟨654458, by rfl⟩ : syracuseStep 3490445 = 1308917) (by norm_num)
theorem B4653733 : Blo 1837620 4653733 := bbase (se 4 (by rfl) ⟨436287, by rfl⟩ : syracuseStep 4653733 = 872575) (by norm_num)
theorem B2327221 : Blo 1837620 2327221 := bbase (se 5 (by rfl) ⟨109088, by rfl⟩ : syracuseStep 2327221 = 218177) (by norm_num)
theorem B4137677 : Blo 1837620 4137677 := bbase (se 3 (by rfl) ⟨775814, by rfl⟩ : syracuseStep 4137677 = 1551629) (by norm_num)
theorem B3728101 : Blo 1837620 3728101 := bbase (se 4 (by rfl) ⟨349509, by rfl⟩ : syracuseStep 3728101 = 699019) (by norm_num)
theorem B3539693 : Blo 1837620 3539693 := bbase (se 3 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 3539693 = 1327385) (by norm_num)
theorem B6980357 : Blo 1837620 6980357 := bbase (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) (by norm_num)
theorem B4653845 : Blo 1837620 4653845 := bbase (se 6 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 4653845 = 218149) (by norm_num)
theorem B4137749 : Blo 1837620 4137749 := bbase (se 6 (by rfl) ⟨96978, by rfl⟩ : syracuseStep 4137749 = 193957) (by norm_num)
theorem B3490589 : Blo 1837620 3490589 := bbase (se 3 (by rfl) ⟨654485, by rfl⟩ : syracuseStep 3490589 = 1308971) (by norm_num)
theorem B3728197 : Blo 1837620 3728197 := bbase (se 4 (by rfl) ⟨349518, by rfl⟩ : syracuseStep 3728197 = 699037) (by norm_num)
theorem B17662805 : Blo 1837620 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B53715797 : Blo 1837620 53715797 := bbase (se 9 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 53715797 = 314741) (by norm_num)
theorem B4137821 : Blo 1837620 4137821 := bbase (se 3 (by rfl) ⟨775841, by rfl⟩ : syracuseStep 4137821 = 1551683) (by norm_num)
theorem B2327393 : Blo 1837620 2327393 := bbase (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) (by norm_num)
theorem B2327449 : Blo 1837620 2327449 := bbase (se 2 (by rfl) ⟨872793, by rfl⟩ : syracuseStep 2327449 = 1745587) (by norm_num)
theorem B6202277 : Blo 1837620 6202277 := bbase (se 4 (by rfl) ⟨581463, by rfl⟩ : syracuseStep 6202277 = 1162927) (by norm_num)
theorem B4137893 : Blo 1837620 4137893 := bbase (se 4 (by rfl) ⟨387927, by rfl⟩ : syracuseStep 4137893 = 775855) (by norm_num)
theorem B9307061 : Blo 1837620 9307061 := bbase (se 5 (by rfl) ⟨436268, by rfl⟩ : syracuseStep 9307061 = 872537) (by norm_num)
theorem B4654037 : Blo 1837620 4654037 := bbase (se 7 (by rfl) ⟨54539, by rfl⟩ : syracuseStep 4654037 = 109079) (by norm_num)
theorem B4137965 : Blo 1837620 4137965 := bbase (se 3 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 4137965 = 1551737) (by norm_num)
theorem B2327545 : Blo 1837620 2327545 := bbase (se 2 (by rfl) ⟨872829, by rfl⟩ : syracuseStep 2327545 = 1745659) (by norm_num)
theorem B4138037 : Blo 1837620 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B3490877 : Blo 1837620 3490877 := bbase (se 3 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 3490877 = 1309079) (by norm_num)
theorem B16999541 : Blo 1837620 16999541 := bbase (se 5 (by rfl) ⟨796853, by rfl⟩ : syracuseStep 16999541 = 1593707) (by norm_num)
theorem B4138109 : Blo 1837620 4138109 := bbase (se 3 (by rfl) ⟨775895, by rfl⟩ : syracuseStep 4138109 = 1551791) (by norm_num)
theorem B2327717 : Blo 1837620 2327717 := bbase (se 4 (by rfl) ⟨218223, by rfl⟩ : syracuseStep 2327717 = 436447) (by norm_num)
theorem B11781301 : Blo 1837620 11781301 := bbase (se 5 (by rfl) ⟨552248, by rfl⟩ : syracuseStep 11781301 = 1104497) (by norm_num)
theorem B4138181 : Blo 1837620 4138181 := bbase (se 4 (by rfl) ⟨387954, by rfl⟩ : syracuseStep 4138181 = 775909) (by norm_num)
theorem B3491029 : Blo 1837620 3491029 := bbase (se 7 (by rfl) ⟨40910, by rfl⟩ : syracuseStep 3491029 = 81821) (by norm_num)
theorem B2327773 : Blo 1837620 2327773 := bbase (se 3 (by rfl) ⟨436457, by rfl⟩ : syracuseStep 2327773 = 872915) (by norm_num)
theorem B5235941 : Blo 1837620 5235941 := bbase (se 4 (by rfl) ⟨490869, by rfl⟩ : syracuseStep 5235941 = 981739) (by norm_num)
theorem B4138253 : Blo 1837620 4138253 := bbase (se 3 (by rfl) ⟨775922, by rfl⟩ : syracuseStep 4138253 = 1551845) (by norm_num)
theorem B4654381 : Blo 1837620 4654381 := bbase (se 3 (by rfl) ⟨872696, by rfl⟩ : syracuseStep 4654381 = 1745393) (by norm_num)
theorem B2327869 : Blo 1837620 2327869 := bbase (se 3 (by rfl) ⟨436475, by rfl⟩ : syracuseStep 2327869 = 872951) (by norm_num)
theorem B6202709 : Blo 1837620 6202709 := bbase (se 12 (by rfl) ⟨2271, by rfl⟩ : syracuseStep 6202709 = 4543) (by norm_num)
theorem B4138325 : Blo 1837620 4138325 := bbase (se 12 (by rfl) ⟨1515, by rfl⟩ : syracuseStep 4138325 = 3031) (by norm_num)
theorem B4654493 : Blo 1837620 4654493 := bbase (se 3 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 4654493 = 1745435) (by norm_num)
theorem B4138397 : Blo 1837620 4138397 := bbase (se 3 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 4138397 = 1551899) (by norm_num)
theorem B4138469 : Blo 1837620 4138469 := bbase (se 4 (by rfl) ⟨387981, by rfl⟩ : syracuseStep 4138469 = 775963) (by norm_num)
theorem B2328041 : Blo 1837620 2328041 := bbase (se 2 (by rfl) ⟨873015, by rfl⟩ : syracuseStep 2328041 = 1746031) (by norm_num)
theorem B5891573 : Blo 1837620 5891573 := bbase (se 5 (by rfl) ⟨276167, by rfl⟩ : syracuseStep 5891573 = 552335) (by norm_num)
theorem B3491333 : Blo 1837620 3491333 := bbase (se 4 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 3491333 = 654625) (by norm_num)
theorem B2328097 : Blo 1837620 2328097 := bbase (se 2 (by rfl) ⟨873036, by rfl⟩ : syracuseStep 2328097 = 1746073) (by norm_num)
theorem B4138541 : Blo 1837620 4138541 := bbase (se 3 (by rfl) ⟨775976, by rfl⟩ : syracuseStep 4138541 = 1551953) (by norm_num)
theorem B8291909 : Blo 1837620 8291909 := bbase (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) (by norm_num)
theorem B3925597 : Blo 1837620 3925597 := bbase (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) (by norm_num)
theorem B4654685 : Blo 1837620 4654685 := bbase (se 3 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 4654685 = 1745507) (by norm_num)
theorem B4138613 : Blo 1837620 4138613 := bbase (se 5 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 4138613 = 387995) (by norm_num)
theorem B2328193 : Blo 1837620 2328193 := bbase (se 2 (by rfl) ⟨873072, by rfl⟩ : syracuseStep 2328193 = 1746145) (by norm_num)
theorem B4138685 : Blo 1837620 4138685 := bbase (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) (by norm_num)
theorem B2795237 : Blo 1837620 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B6203141 : Blo 1837620 6203141 := bbase (se 4 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 6203141 = 1163089) (by norm_num)
theorem B4138757 : Blo 1837620 4138757 := bbase (se 4 (by rfl) ⟨388008, by rfl⟩ : syracuseStep 4138757 = 776017) (by norm_num)
theorem B2484005 : Blo 1837620 2484005 := bbase (se 4 (by rfl) ⟨232875, by rfl⟩ : syracuseStep 2484005 = 465751) (by norm_num)
theorem B4138829 : Blo 1837620 4138829 := bbase (se 3 (by rfl) ⟨776030, by rfl⟩ : syracuseStep 4138829 = 1552061) (by norm_num)
theorem B4417373 : Blo 1837620 4417373 := bbase (se 3 (by rfl) ⟨828257, by rfl⟩ : syracuseStep 4417373 = 1656515) (by norm_num)
theorem B8832901 : Blo 1837620 8832901 := bbase (se 4 (by rfl) ⟨828084, by rfl⟩ : syracuseStep 8832901 = 1656169) (by norm_num)
theorem B5236613 : Blo 1837620 5236613 := bbase (se 4 (by rfl) ⟨490932, by rfl⟩ : syracuseStep 5236613 = 981865) (by norm_num)
theorem B4138901 : Blo 1837620 4138901 := bbase (se 6 (by rfl) ⟨97005, by rfl⟩ : syracuseStep 4138901 = 194011) (by norm_num)
theorem B3311525 : Blo 1837620 3311525 := bbase (se 4 (by rfl) ⟨310455, by rfl⟩ : syracuseStep 3311525 = 620911) (by norm_num)
theorem B4655029 : Blo 1837620 4655029 := bbase (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) (by norm_num)
theorem B16779221 : Blo 1837620 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B4138973 : Blo 1837620 4138973 := bbase (se 3 (by rfl) ⟨776057, by rfl⟩ : syracuseStep 4138973 = 1552115) (by norm_num)
theorem B4655141 : Blo 1837620 4655141 := bbase (se 4 (by rfl) ⟨436419, by rfl⟩ : syracuseStep 4655141 = 872839) (by norm_num)
theorem B4139045 : Blo 1837620 4139045 := bbase (se 4 (by rfl) ⟨388035, by rfl⟩ : syracuseStep 4139045 = 776071) (by norm_num)
theorem B4139117 : Blo 1837620 4139117 := bbase (se 3 (by rfl) ⟨776084, by rfl⟩ : syracuseStep 4139117 = 1552169) (by norm_num)
theorem B12585077 : Blo 1837620 12585077 := bbase (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) (by norm_num)
theorem B6203573 : Blo 1837620 6203573 := bbase (se 5 (by rfl) ⟨290792, by rfl⟩ : syracuseStep 6203573 = 581585) (by norm_num)
theorem B15714485 : Blo 1837620 15714485 := bbase (se 5 (by rfl) ⟨736616, by rfl⟩ : syracuseStep 15714485 = 1473233) (by norm_num)
theorem B3311813 : Blo 1837620 3311813 := bbase (se 4 (by rfl) ⟨310482, by rfl⟩ : syracuseStep 3311813 = 620965) (by norm_num)
theorem B9308357 : Blo 1837620 9308357 := bbase (se 4 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 9308357 = 1745317) (by norm_num)
theorem B4655333 : Blo 1837620 4655333 := bbase (se 4 (by rfl) ⟨436437, by rfl⟩ : syracuseStep 4655333 = 872875) (by norm_num)
theorem B3492085 : Blo 1837620 3492085 := bbase (se 5 (by rfl) ⟨163691, by rfl⟩ : syracuseStep 3492085 = 327383) (by norm_num)
theorem B5237045 : Blo 1837620 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B3492229 : Blo 1837620 3492229 := bbase (se 4 (by rfl) ⟨327396, by rfl⟩ : syracuseStep 3492229 = 654793) (by norm_num)
theorem B8391109 : Blo 1837620 8391109 := bbase (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) (by norm_num)
theorem B3926485 : Blo 1837620 3926485 := bbase (se 7 (by rfl) ⟨46013, by rfl⟩ : syracuseStep 3926485 = 92027) (by norm_num)
theorem B3492389 : Blo 1837620 3492389 := bbase (se 4 (by rfl) ⟨327411, by rfl⟩ : syracuseStep 3492389 = 654823) (by norm_num)
theorem B4655677 : Blo 1837620 4655677 := bbase (se 3 (by rfl) ⟨872939, by rfl⟩ : syracuseStep 4655677 = 1745879) (by norm_num)
theorem B6204005 : Blo 1837620 6204005 := bbase (se 4 (by rfl) ⟨581625, by rfl⟩ : syracuseStep 6204005 = 1163251) (by norm_num)
theorem B4655789 : Blo 1837620 4655789 := bbase (se 3 (by rfl) ⟨872960, by rfl⟩ : syracuseStep 4655789 = 1745921) (by norm_num)
theorem B2943685 : Blo 1837620 2943685 := bbase (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) (by norm_num)
theorem B6982469 : Blo 1837620 6982469 := bbase (se 4 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 6982469 = 1309213) (by norm_num)
theorem B9431909 : Blo 1837620 9431909 := bbase (se 4 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 9431909 = 1768483) (by norm_num)
theorem B4655981 : Blo 1837620 4655981 := bbase (se 3 (by rfl) ⟨872996, by rfl⟩ : syracuseStep 4655981 = 1745993) (by norm_num)
theorem B2067349 : Blo 1837620 2067349 := bbase (se 6 (by rfl) ⟨48453, by rfl⟩ : syracuseStep 2067349 = 96907) (by norm_num)
theorem B2067385 : Blo 1837620 2067385 := bbase (se 2 (by rfl) ⟨775269, by rfl⟩ : syracuseStep 2067385 = 1550539) (by norm_num)
theorem B3926981 : Blo 1837620 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B44731349 : Blo 1837620 44731349 := bbase (se 7 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 44731349 = 1048391) (by norm_num)
theorem B2067421 : Blo 1837620 2067421 := bbase (se 3 (by rfl) ⟨387641, by rfl⟩ : syracuseStep 2067421 = 775283) (by norm_num)
theorem B4664317 : Blo 1837620 4664317 := bbase (se 3 (by rfl) ⟨874559, by rfl⟩ : syracuseStep 4664317 = 1749119) (by norm_num)
theorem B2067457 : Blo 1837620 2067457 := bbase (se 2 (by rfl) ⟨775296, by rfl⟩ : syracuseStep 2067457 = 1550593) (by norm_num)
theorem B6204437 : Blo 1837620 6204437 := bbase (se 6 (by rfl) ⟨145416, by rfl⟩ : syracuseStep 6204437 = 290833) (by norm_num)
theorem B2067493 : Blo 1837620 2067493 := bbase (se 4 (by rfl) ⟨193827, by rfl⟩ : syracuseStep 2067493 = 387655) (by norm_num)
theorem B5237797 : Blo 1837620 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B13962293 : Blo 1837620 13962293 := bbase (se 5 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 13962293 = 1308965) (by norm_num)
theorem B2067529 : Blo 1837620 2067529 := bbase (se 2 (by rfl) ⟨775323, by rfl⟩ : syracuseStep 2067529 = 1550647) (by norm_num)
theorem B6982757 : Blo 1837620 6982757 := bbase (se 4 (by rfl) ⟨654633, by rfl⟩ : syracuseStep 6982757 = 1309267) (by norm_num)
theorem B2067565 : Blo 1837620 2067565 := bbase (se 3 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 2067565 = 775337) (by norm_num)
theorem B2944109 : Blo 1837620 2944109 := bbase (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) (by norm_num)
theorem B2067601 : Blo 1837620 2067601 := bbase (se 2 (by rfl) ⟨775350, by rfl⟩ : syracuseStep 2067601 = 1550701) (by norm_num)
theorem B2067637 : Blo 1837620 2067637 := bbase (se 5 (by rfl) ⟨96920, by rfl⟩ : syracuseStep 2067637 = 193841) (by norm_num)
theorem B3312829 : Blo 1837620 3312829 := bbase (se 3 (by rfl) ⟨621155, by rfl⟩ : syracuseStep 3312829 = 1242311) (by norm_num)
theorem B4656325 : Blo 1837620 4656325 := bbase (se 4 (by rfl) ⟨436530, by rfl⟩ : syracuseStep 4656325 = 873061) (by norm_num)
theorem B2067673 : Blo 1837620 2067673 := bbase (se 2 (by rfl) ⟨775377, by rfl⟩ : syracuseStep 2067673 = 1550755) (by norm_num)
theorem B2067709 : Blo 1837620 2067709 := bbase (se 3 (by rfl) ⟨387695, by rfl⟩ : syracuseStep 2067709 = 775391) (by norm_num)
theorem B11775253 : Blo 1837620 11775253 := bbase (se 6 (by rfl) ⟨275982, by rfl⟩ : syracuseStep 11775253 = 551965) (by norm_num)
theorem B2067745 : Blo 1837620 2067745 := bbase (se 2 (by rfl) ⟨775404, by rfl⟩ : syracuseStep 2067745 = 1550809) (by norm_num)
theorem B4656437 : Blo 1837620 4656437 := bbase (se 5 (by rfl) ⟨218270, by rfl⟩ : syracuseStep 4656437 = 436541) (by norm_num)
theorem B2067781 : Blo 1837620 2067781 := bbase (se 4 (by rfl) ⟨193854, by rfl⟩ : syracuseStep 2067781 = 387709) (by norm_num)
theorem B5107013 : Blo 1837620 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B2067817 : Blo 1837620 2067817 := bbase (se 2 (by rfl) ⟨775431, by rfl⟩ : syracuseStep 2067817 = 1550863) (by norm_num)
theorem B2067853 : Blo 1837620 2067853 := bbase (se 3 (by rfl) ⟨387722, by rfl⟩ : syracuseStep 2067853 = 775445) (by norm_num)
theorem B2944397 : Blo 1837620 2944397 := bbase (se 3 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 2944397 = 1104149) (by norm_num)
theorem B2067889 : Blo 1837620 2067889 := bbase (se 2 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 2067889 = 1550917) (by norm_num)
theorem B6204869 : Blo 1837620 6204869 := bbase (se 4 (by rfl) ⟨581706, by rfl⟩ : syracuseStep 6204869 = 1163413) (by norm_num)
theorem B13954517 : Blo 1837620 13954517 := bbase (se 7 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 13954517 = 327059) (by norm_num)
theorem B2067925 : Blo 1837620 2067925 := bbase (se 7 (by rfl) ⟨24233, by rfl⟩ : syracuseStep 2067925 = 48467) (by norm_num)
theorem B9309653 : Blo 1837620 9309653 := bbase (se 7 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 9309653 = 218195) (by norm_num)
theorem B2067961 : Blo 1837620 2067961 := bbase (se 2 (by rfl) ⟨775485, by rfl⟩ : syracuseStep 2067961 = 1550971) (by norm_num)
theorem B2067997 : Blo 1837620 2067997 := bbase (se 3 (by rfl) ⟨387749, by rfl⟩ : syracuseStep 2067997 = 775499) (by norm_num)
theorem B2616877 : Blo 1837620 2616877 := bbase (se 3 (by rfl) ⟨490664, by rfl⟩ : syracuseStep 2616877 = 981329) (by norm_num)
theorem B2068033 : Blo 1837620 2068033 := bbase (se 2 (by rfl) ⟨775512, by rfl⟩ : syracuseStep 2068033 = 1551025) (by norm_num)
theorem B2240069 : Blo 1837620 2240069 := bbase (se 4 (by rfl) ⟨210006, by rfl⟩ : syracuseStep 2240069 = 420013) (by norm_num)
theorem B2068069 : Blo 1837620 2068069 := bbase (se 4 (by rfl) ⟨193881, by rfl⟩ : syracuseStep 2068069 = 387763) (by norm_num)
theorem B2944621 : Blo 1837620 2944621 := bbase (se 3 (by rfl) ⟨552116, by rfl⟩ : syracuseStep 2944621 = 1104233) (by norm_num)
theorem B3313261 : Blo 1837620 3313261 := bbase (se 3 (by rfl) ⟨621236, by rfl⟩ : syracuseStep 3313261 = 1242473) (by norm_num)
theorem B2068105 : Blo 1837620 2068105 := bbase (se 2 (by rfl) ⟨775539, by rfl⟩ : syracuseStep 2068105 = 1551079) (by norm_num)
theorem B2240165 : Blo 1837620 2240165 := bbase (se 4 (by rfl) ⟨210015, by rfl⟩ : syracuseStep 2240165 = 420031) (by norm_num)
theorem B2068141 : Blo 1837620 2068141 := bbase (se 3 (by rfl) ⟨387776, by rfl⟩ : syracuseStep 2068141 = 775553) (by norm_num)
theorem B2068177 : Blo 1837620 2068177 := bbase (se 2 (by rfl) ⟨775566, by rfl⟩ : syracuseStep 2068177 = 1551133) (by norm_num)
theorem B1863401 : Blo 1837620 1863401 := bbase (se 2 (by rfl) ⟨698775, by rfl⟩ : syracuseStep 1863401 = 1397551) (by norm_num)
theorem B2068213 : Blo 1837620 2068213 := bbase (se 5 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 2068213 = 193895) (by norm_num)
theorem B2068249 : Blo 1837620 2068249 := bbase (se 2 (by rfl) ⟨775593, by rfl⟩ : syracuseStep 2068249 = 1551187) (by norm_num)
theorem B3927845 : Blo 1837620 3927845 := bbase (se 4 (by rfl) ⟨368235, by rfl⟩ : syracuseStep 3927845 = 736471) (by norm_num)
theorem B4419373 : Blo 1837620 4419373 := bbase (se 3 (by rfl) ⟨828632, by rfl⟩ : syracuseStep 4419373 = 1657265) (by norm_num)
theorem B2068285 : Blo 1837620 2068285 := bbase (se 3 (by rfl) ⟨387803, by rfl⟩ : syracuseStep 2068285 = 775607) (by norm_num)
theorem B2068321 : Blo 1837620 2068321 := bbase (se 2 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 2068321 = 1551241) (by norm_num)
theorem B2756453 : Blo 1837620 2756453 := bbase (se 4 (by rfl) ⟨258417, by rfl⟩ : syracuseStep 2756453 = 516835) (by norm_num)
theorem B6205301 : Blo 1837620 6205301 := bbase (se 5 (by rfl) ⟨290873, by rfl⟩ : syracuseStep 6205301 = 581747) (by norm_num)
theorem B2756477 : Blo 1837620 2756477 := bbase (se 3 (by rfl) ⟨516839, by rfl⟩ : syracuseStep 2756477 = 1033679) (by norm_num)
theorem B2617213 : Blo 1837620 2617213 := bbase (se 3 (by rfl) ⟨490727, by rfl⟩ : syracuseStep 2617213 = 981455) (by norm_num)
theorem B2068357 : Blo 1837620 2068357 := bbase (se 4 (by rfl) ⟨193908, by rfl⟩ : syracuseStep 2068357 = 387817) (by norm_num)
theorem B3313549 : Blo 1837620 3313549 := bbase (se 3 (by rfl) ⟨621290, by rfl⟩ : syracuseStep 3313549 = 1242581) (by norm_num)
theorem B2756501 : Blo 1837620 2756501 := bbase (se 6 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 2756501 = 129211) (by norm_num)
theorem B2068393 : Blo 1837620 2068393 := bbase (se 2 (by rfl) ⟨775647, by rfl⟩ : syracuseStep 2068393 = 1551295) (by norm_num)
theorem B2756525 : Blo 1837620 2756525 := bbase (se 3 (by rfl) ⟨516848, by rfl⟩ : syracuseStep 2756525 = 1033697) (by norm_num)
theorem B3927989 : Blo 1837620 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B4419517 : Blo 1837620 4419517 := bbase (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) (by norm_num)
theorem B2756549 : Blo 1837620 2756549 := bbase (se 4 (by rfl) ⟨258426, by rfl⟩ : syracuseStep 2756549 = 516853) (by norm_num)
theorem B2068429 : Blo 1837620 2068429 := bbase (se 3 (by rfl) ⟨387830, by rfl⟩ : syracuseStep 2068429 = 775661) (by norm_num)
theorem B11784149 : Blo 1837620 11784149 := bbase (se 7 (by rfl) ⟨138095, by rfl⟩ : syracuseStep 11784149 = 276191) (by norm_num)
theorem B2756573 : Blo 1837620 2756573 := bbase (se 3 (by rfl) ⟨516857, by rfl⟩ : syracuseStep 2756573 = 1033715) (by norm_num)
theorem B2068465 : Blo 1837620 2068465 := bbase (se 2 (by rfl) ⟨775674, by rfl⟩ : syracuseStep 2068465 = 1551349) (by norm_num)
theorem B2756597 : Blo 1837620 2756597 := bbase (se 5 (by rfl) ⟨129215, by rfl⟩ : syracuseStep 2756597 = 258431) (by norm_num)
theorem B2756621 : Blo 1837620 2756621 := bbase (se 3 (by rfl) ⟨516866, by rfl⟩ : syracuseStep 2756621 = 1033733) (by norm_num)
theorem B2068501 : Blo 1837620 2068501 := bbase (se 6 (by rfl) ⟨48480, by rfl⟩ : syracuseStep 2068501 = 96961) (by norm_num)
theorem B2756645 : Blo 1837620 2756645 := bbase (se 4 (by rfl) ⟨258435, by rfl⟩ : syracuseStep 2756645 = 516871) (by norm_num)
theorem B2068537 : Blo 1837620 2068537 := bbase (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) (by norm_num)
theorem B2756669 : Blo 1837620 2756669 := bbase (se 3 (by rfl) ⟨516875, by rfl⟩ : syracuseStep 2756669 = 1033751) (by norm_num)
theorem B2756693 : Blo 1837620 2756693 := bbase (se 8 (by rfl) ⟨16152, by rfl⟩ : syracuseStep 2756693 = 32305) (by norm_num)
theorem B2617429 : Blo 1837620 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B2068573 : Blo 1837620 2068573 := bbase (se 3 (by rfl) ⟨387857, by rfl⟩ : syracuseStep 2068573 = 775715) (by norm_num)
theorem B2756717 : Blo 1837620 2756717 := bbase (se 3 (by rfl) ⟨516884, by rfl⟩ : syracuseStep 2756717 = 1033769) (by norm_num)
theorem B2068609 : Blo 1837620 2068609 := bbase (se 2 (by rfl) ⟨775728, by rfl⟩ : syracuseStep 2068609 = 1551457) (by norm_num)
theorem B2756741 : Blo 1837620 2756741 := bbase (se 4 (by rfl) ⟨258444, by rfl⟩ : syracuseStep 2756741 = 516889) (by norm_num)
theorem B2756765 : Blo 1837620 2756765 := bbase (se 3 (by rfl) ⟨516893, by rfl⟩ : syracuseStep 2756765 = 1033787) (by norm_num)
theorem B2068645 : Blo 1837620 2068645 := bbase (se 4 (by rfl) ⟨193935, by rfl⟩ : syracuseStep 2068645 = 387871) (by norm_num)
theorem B2756789 : Blo 1837620 2756789 := bbase (se 5 (by rfl) ⟨129224, by rfl⟩ : syracuseStep 2756789 = 258449) (by norm_num)
theorem B2068681 : Blo 1837620 2068681 := bbase (se 2 (by rfl) ⟨775755, by rfl⟩ : syracuseStep 2068681 = 1551511) (by norm_num)
theorem B2756813 : Blo 1837620 2756813 := bbase (se 3 (by rfl) ⟨516902, by rfl⟩ : syracuseStep 2756813 = 1033805) (by norm_num)
theorem B2756837 : Blo 1837620 2756837 := bbase (se 4 (by rfl) ⟨258453, by rfl⟩ : syracuseStep 2756837 = 516907) (by norm_num)
theorem B2068717 : Blo 1837620 2068717 := bbase (se 3 (by rfl) ⟨387884, by rfl⟩ : syracuseStep 2068717 = 775769) (by norm_num)
theorem B2756861 : Blo 1837620 2756861 := bbase (se 3 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 2756861 = 1033823) (by norm_num)
theorem B6983941 : Blo 1837620 6983941 := bbase (se 4 (by rfl) ⟨654744, by rfl⟩ : syracuseStep 6983941 = 1309489) (by norm_num)
theorem B2068753 : Blo 1837620 2068753 := bbase (se 2 (by rfl) ⟨775782, by rfl⟩ : syracuseStep 2068753 = 1551565) (by norm_num)
theorem B2756885 : Blo 1837620 2756885 := bbase (se 6 (by rfl) ⟨64614, by rfl⟩ : syracuseStep 2756885 = 129229) (by norm_num)
theorem B1863965 : Blo 1837620 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B6205733 : Blo 1837620 6205733 := bbase (se 4 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 6205733 = 1163575) (by norm_num)
theorem B2756909 : Blo 1837620 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B2068789 : Blo 1837620 2068789 := bbase (se 5 (by rfl) ⟨96974, by rfl⟩ : syracuseStep 2068789 = 193949) (by norm_num)
theorem B3100997 : Blo 1837620 3100997 := bbase (se 4 (by rfl) ⟨290718, by rfl⟩ : syracuseStep 3100997 = 581437) (by norm_num)
theorem B2756933 : Blo 1837620 2756933 := bbase (se 4 (by rfl) ⟨258462, by rfl⟩ : syracuseStep 2756933 = 516925) (by norm_num)
theorem B2068825 : Blo 1837620 2068825 := bbase (se 2 (by rfl) ⟨775809, by rfl⟩ : syracuseStep 2068825 = 1551619) (by norm_num)
theorem B2756957 : Blo 1837620 2756957 := bbase (se 3 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 2756957 = 1033859) (by norm_num)
theorem B2756981 : Blo 1837620 2756981 := bbase (se 5 (by rfl) ⟨129233, by rfl⟩ : syracuseStep 2756981 = 258467) (by norm_num)
theorem B2068861 : Blo 1837620 2068861 := bbase (se 3 (by rfl) ⟨387911, by rfl⟩ : syracuseStep 2068861 = 775823) (by norm_num)
theorem B2757005 : Blo 1837620 2757005 := bbase (se 3 (by rfl) ⟨516938, by rfl⟩ : syracuseStep 2757005 = 1033877) (by norm_num)
theorem B13250965 : Blo 1837620 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B1962397 : Blo 1837620 1962397 := bbase (se 3 (by rfl) ⟨367949, by rfl⟩ : syracuseStep 1962397 = 735899) (by norm_num)
theorem B2068897 : Blo 1837620 2068897 := bbase (se 2 (by rfl) ⟨775836, by rfl⟩ : syracuseStep 2068897 = 1551673) (by norm_num)
theorem B2757029 : Blo 1837620 2757029 := bbase (se 4 (by rfl) ⟨258471, by rfl⟩ : syracuseStep 2757029 = 516943) (by norm_num)
theorem B2757053 : Blo 1837620 2757053 := bbase (se 3 (by rfl) ⟨516947, by rfl⟩ : syracuseStep 2757053 = 1033895) (by norm_num)
theorem B3101125 : Blo 1837620 3101125 := bbase (se 4 (by rfl) ⟨290730, by rfl⟩ : syracuseStep 3101125 = 581461) (by norm_num)
theorem B2068933 : Blo 1837620 2068933 := bbase (se 4 (by rfl) ⟨193962, by rfl⟩ : syracuseStep 2068933 = 387925) (by norm_num)
theorem B2617805 : Blo 1837620 2617805 := bbase (se 3 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 2617805 = 981677) (by norm_num)
theorem B2757077 : Blo 1837620 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B2068969 : Blo 1837620 2068969 := bbase (se 2 (by rfl) ⟨775863, by rfl⟩ : syracuseStep 2068969 = 1551727) (by norm_num)
theorem B2757101 : Blo 1837620 2757101 := bbase (se 3 (by rfl) ⟨516956, by rfl⟩ : syracuseStep 2757101 = 1033913) (by norm_num)
theorem B2757125 : Blo 1837620 2757125 := bbase (se 4 (by rfl) ⟨258480, by rfl⟩ : syracuseStep 2757125 = 516961) (by norm_num)
theorem B2069005 : Blo 1837620 2069005 := bbase (se 3 (by rfl) ⟨387938, by rfl⟩ : syracuseStep 2069005 = 775877) (by norm_num)
theorem B3101213 : Blo 1837620 3101213 := bbase (se 3 (by rfl) ⟨581477, by rfl⟩ : syracuseStep 3101213 = 1162955) (by norm_num)
theorem B2757149 : Blo 1837620 2757149 := bbase (se 3 (by rfl) ⟨516965, by rfl⟩ : syracuseStep 2757149 = 1033931) (by norm_num)
theorem B1864225 : Blo 1837620 1864225 := bbase (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) (by norm_num)
theorem B3314213 : Blo 1837620 3314213 := bbase (se 4 (by rfl) ⟨310707, by rfl⟩ : syracuseStep 3314213 = 621415) (by norm_num)
theorem B2069041 : Blo 1837620 2069041 := bbase (se 2 (by rfl) ⟨775890, by rfl⟩ : syracuseStep 2069041 = 1551781) (by norm_num)
theorem B2757173 : Blo 1837620 2757173 := bbase (se 5 (by rfl) ⟨129242, by rfl⟩ : syracuseStep 2757173 = 258485) (by norm_num)
theorem B6984245 : Blo 1837620 6984245 := bbase (se 5 (by rfl) ⟨327386, by rfl⟩ : syracuseStep 6984245 = 654773) (by norm_num)
theorem B2757197 : Blo 1837620 2757197 := bbase (se 3 (by rfl) ⟨516974, by rfl⟩ : syracuseStep 2757197 = 1033949) (by norm_num)
theorem B2069077 : Blo 1837620 2069077 := bbase (se 8 (by rfl) ⟨12123, by rfl⟩ : syracuseStep 2069077 = 24247) (by norm_num)
theorem B2126425 : Blo 1837620 2126425 := bbase (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) (by norm_num)
theorem B2757221 : Blo 1837620 2757221 := bbase (se 4 (by rfl) ⟨258489, by rfl⟩ : syracuseStep 2757221 = 516979) (by norm_num)
theorem B2069113 : Blo 1837620 2069113 := bbase (se 2 (by rfl) ⟨775917, by rfl⟩ : syracuseStep 2069113 = 1551835) (by norm_num)
theorem B2757245 : Blo 1837620 2757245 := bbase (se 3 (by rfl) ⟨516983, by rfl⟩ : syracuseStep 2757245 = 1033967) (by norm_num)
theorem B2208389 : Blo 1837620 2208389 := bbase (se 4 (by rfl) ⟨207036, by rfl⟩ : syracuseStep 2208389 = 414073) (by norm_num)
theorem B2757269 : Blo 1837620 2757269 := bbase (se 6 (by rfl) ⟨64623, by rfl⟩ : syracuseStep 2757269 = 129247) (by norm_num)
theorem B3101341 : Blo 1837620 3101341 := bbase (se 3 (by rfl) ⟨581501, by rfl⟩ : syracuseStep 3101341 = 1163003) (by norm_num)
theorem B2069149 : Blo 1837620 2069149 := bbase (se 3 (by rfl) ⟨387965, by rfl⟩ : syracuseStep 2069149 = 775931) (by norm_num)
theorem B3928733 : Blo 1837620 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B3027613 : Blo 1837620 3027613 := bbase (se 3 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 3027613 = 1135355) (by norm_num)
theorem B2757293 : Blo 1837620 2757293 := bbase (se 3 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 2757293 = 1033985) (by norm_num)
theorem B2069185 : Blo 1837620 2069185 := bbase (se 2 (by rfl) ⟨775944, by rfl⟩ : syracuseStep 2069185 = 1551889) (by norm_num)
theorem B2757317 : Blo 1837620 2757317 := bbase (se 4 (by rfl) ⟨258498, by rfl⟩ : syracuseStep 2757317 = 516997) (by norm_num)
theorem B6206165 : Blo 1837620 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B2945749 : Blo 1837620 2945749 := bbase (se 7 (by rfl) ⟨34520, by rfl⟩ : syracuseStep 2945749 = 69041) (by norm_num)
theorem B2757341 : Blo 1837620 2757341 := bbase (se 3 (by rfl) ⟨517001, by rfl⟩ : syracuseStep 2757341 = 1034003) (by norm_num)
theorem B4969189 : Blo 1837620 4969189 := bbase (se 4 (by rfl) ⟨465861, by rfl⟩ : syracuseStep 4969189 = 931723) (by norm_num)
theorem B9310949 : Blo 1837620 9310949 := bbase (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) (by norm_num)
theorem B2069221 : Blo 1837620 2069221 := bbase (se 4 (by rfl) ⟨193989, by rfl⟩ : syracuseStep 2069221 = 387979) (by norm_num)
theorem B3101429 : Blo 1837620 3101429 := bbase (se 5 (by rfl) ⟨145379, by rfl⟩ : syracuseStep 3101429 = 290759) (by norm_num)
theorem B2757365 : Blo 1837620 2757365 := bbase (se 5 (by rfl) ⟨129251, by rfl⟩ : syracuseStep 2757365 = 258503) (by norm_num)
theorem B2069257 : Blo 1837620 2069257 := bbase (se 2 (by rfl) ⟨775971, by rfl⟩ : syracuseStep 2069257 = 1551943) (by norm_num)
theorem B2757389 : Blo 1837620 2757389 := bbase (se 3 (by rfl) ⟨517010, by rfl⟩ : syracuseStep 2757389 = 1034021) (by norm_num)
theorem B2757413 : Blo 1837620 2757413 := bbase (se 4 (by rfl) ⟨258507, by rfl⟩ : syracuseStep 2757413 = 517015) (by norm_num)
theorem B2069293 : Blo 1837620 2069293 := bbase (se 3 (by rfl) ⟨387992, by rfl⟩ : syracuseStep 2069293 = 775985) (by norm_num)
theorem B1864505 : Blo 1837620 1864505 := bbase (se 2 (by rfl) ⟨699189, by rfl⟩ : syracuseStep 1864505 = 1398379) (by norm_num)
theorem B2757437 : Blo 1837620 2757437 := bbase (se 3 (by rfl) ⟨517019, by rfl⟩ : syracuseStep 2757437 = 1034039) (by norm_num)
theorem B1962829 : Blo 1837620 1962829 := bbase (se 3 (by rfl) ⟨368030, by rfl⟩ : syracuseStep 1962829 = 736061) (by norm_num)
theorem B2069329 : Blo 1837620 2069329 := bbase (se 2 (by rfl) ⟨775998, by rfl⟩ : syracuseStep 2069329 = 1551997) (by norm_num)
theorem B2757461 : Blo 1837620 2757461 := bbase (se 9 (by rfl) ⟨8078, by rfl⟩ : syracuseStep 2757461 = 16157) (by norm_num)
theorem B5591909 : Blo 1837620 5591909 := bbase (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) (by norm_num)
theorem B2757485 : Blo 1837620 2757485 := bbase (se 3 (by rfl) ⟨517028, by rfl⟩ : syracuseStep 2757485 = 1034057) (by norm_num)
theorem B3101557 : Blo 1837620 3101557 := bbase (se 5 (by rfl) ⟨145385, by rfl⟩ : syracuseStep 3101557 = 290771) (by norm_num)
theorem B2069365 : Blo 1837620 2069365 := bbase (se 5 (by rfl) ⟨97001, by rfl⟩ : syracuseStep 2069365 = 194003) (by norm_num)
theorem B6714245 : Blo 1837620 6714245 := bbase (se 4 (by rfl) ⟨629460, by rfl⟩ : syracuseStep 6714245 = 1258921) (by norm_num)
theorem B2757509 : Blo 1837620 2757509 := bbase (se 4 (by rfl) ⟨258516, by rfl⟩ : syracuseStep 2757509 = 517033) (by norm_num)
theorem B1962901 : Blo 1837620 1962901 := bbase (se 6 (by rfl) ⟨46005, by rfl⟩ : syracuseStep 1962901 = 92011) (by norm_num)
theorem B2069401 : Blo 1837620 2069401 := bbase (se 2 (by rfl) ⟨776025, by rfl⟩ : syracuseStep 2069401 = 1552051) (by norm_num)
theorem B2757533 : Blo 1837620 2757533 := bbase (se 3 (by rfl) ⟨517037, by rfl⟩ : syracuseStep 2757533 = 1034075) (by norm_num)
theorem B2757557 : Blo 1837620 2757557 := bbase (se 5 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 2757557 = 258521) (by norm_num)
theorem B2069437 : Blo 1837620 2069437 := bbase (se 3 (by rfl) ⟨388019, by rfl⟩ : syracuseStep 2069437 = 776039) (by norm_num)
theorem B5968837 : Blo 1837620 5968837 := bbase (se 4 (by rfl) ⟨559578, by rfl⟩ : syracuseStep 5968837 = 1119157) (by norm_num)
theorem B3101645 : Blo 1837620 3101645 := bbase (se 3 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 3101645 = 1163117) (by norm_num)
theorem B2757581 : Blo 1837620 2757581 := bbase (se 3 (by rfl) ⟨517046, by rfl⟩ : syracuseStep 2757581 = 1034093) (by norm_num)
theorem B2069473 : Blo 1837620 2069473 := bbase (se 2 (by rfl) ⟨776052, by rfl⟩ : syracuseStep 2069473 = 1552105) (by norm_num)
theorem B2757605 : Blo 1837620 2757605 := bbase (se 4 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 2757605 = 517051) (by norm_num)
theorem B2208745 : Blo 1837620 2208745 := bbase (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) (by norm_num)
theorem B2757629 : Blo 1837620 2757629 := bbase (se 3 (by rfl) ⟨517055, by rfl⟩ : syracuseStep 2757629 = 1034111) (by norm_num)
theorem B2069509 : Blo 1837620 2069509 := bbase (se 4 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 2069509 = 388033) (by norm_num)
theorem B2757653 : Blo 1837620 2757653 := bbase (se 6 (by rfl) ⟨64632, by rfl⟩ : syracuseStep 2757653 = 129265) (by norm_num)
theorem B2069545 : Blo 1837620 2069545 := bbase (se 2 (by rfl) ⟨776079, by rfl⟩ : syracuseStep 2069545 = 1552159) (by norm_num)
theorem B2757677 : Blo 1837620 2757677 := bbase (se 3 (by rfl) ⟨517064, by rfl⟩ : syracuseStep 2757677 = 1034129) (by norm_num)
theorem B2757701 : Blo 1837620 2757701 := bbase (se 4 (by rfl) ⟨258534, by rfl⟩ : syracuseStep 2757701 = 517069) (by norm_num)
theorem B3101773 : Blo 1837620 3101773 := bbase (se 3 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 3101773 = 1163165) (by norm_num)
theorem B2757725 : Blo 1837620 2757725 := bbase (se 3 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 2757725 = 1034147) (by norm_num)
theorem B2757749 : Blo 1837620 2757749 := bbase (se 5 (by rfl) ⟨129269, by rfl⟩ : syracuseStep 2757749 = 258539) (by norm_num)
theorem B9303173 : Blo 1837620 9303173 := bbase (se 4 (by rfl) ⟨872172, by rfl⟩ : syracuseStep 9303173 = 1744345) (by norm_num)
theorem B6206597 : Blo 1837620 6206597 := bbase (se 4 (by rfl) ⟨581868, by rfl⟩ : syracuseStep 6206597 = 1163737) (by norm_num)
theorem B2757773 : Blo 1837620 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B2946197 : Blo 1837620 2946197 := bbase (se 6 (by rfl) ⟨69051, by rfl⟩ : syracuseStep 2946197 = 138103) (by norm_num)
theorem B3101861 : Blo 1837620 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B2757797 : Blo 1837620 2757797 := bbase (se 4 (by rfl) ⟨258543, by rfl⟩ : syracuseStep 2757797 = 517087) (by norm_num)
theorem B2208937 : Blo 1837620 2208937 := bbase (se 2 (by rfl) ⟨828351, by rfl⟩ : syracuseStep 2208937 = 1656703) (by norm_num)
theorem B2757821 : Blo 1837620 2757821 := bbase (se 3 (by rfl) ⟨517091, by rfl⟩ : syracuseStep 2757821 = 1034183) (by norm_num)
theorem B2757845 : Blo 1837620 2757845 := bbase (se 7 (by rfl) ⟨32318, by rfl⟩ : syracuseStep 2757845 = 64637) (by norm_num)
theorem B2757869 : Blo 1837620 2757869 := bbase (se 3 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 2757869 = 1034201) (by norm_num)
theorem B3314933 : Blo 1837620 3314933 := bbase (se 5 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 3314933 = 310775) (by norm_num)
theorem B2757893 : Blo 1837620 2757893 := bbase (se 4 (by rfl) ⟨258552, by rfl⟩ : syracuseStep 2757893 = 517105) (by norm_num)
theorem B1963273 : Blo 1837620 1963273 := bbase (se 2 (by rfl) ⟨736227, by rfl⟩ : syracuseStep 1963273 = 1472455) (by norm_num)
theorem B2757917 : Blo 1837620 2757917 := bbase (se 3 (by rfl) ⟨517109, by rfl⟩ : syracuseStep 2757917 = 1034219) (by norm_num)
theorem B3978533 : Blo 1837620 3978533 := bbase (se 4 (by rfl) ⟨372987, by rfl⟩ : syracuseStep 3978533 = 745975) (by norm_num)
theorem B3101989 : Blo 1837620 3101989 := bbase (se 4 (by rfl) ⟨290811, by rfl⟩ : syracuseStep 3101989 = 581623) (by norm_num)
theorem B2757941 : Blo 1837620 2757941 := bbase (se 5 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 2757941 = 258557) (by norm_num)
theorem B2209081 : Blo 1837620 2209081 := bbase (se 2 (by rfl) ⟨828405, by rfl⟩ : syracuseStep 2209081 = 1656811) (by norm_num)
theorem B7853381 : Blo 1837620 7853381 := bbase (se 4 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 7853381 = 1472509) (by norm_num)
theorem B2757965 : Blo 1837620 2757965 := bbase (se 3 (by rfl) ⟨517118, by rfl⟩ : syracuseStep 2757965 = 1034237) (by norm_num)
theorem B2757989 : Blo 1837620 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B3102077 : Blo 1837620 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B2758013 : Blo 1837620 2758013 := bbase (se 3 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 2758013 = 1034255) (by norm_num)
theorem B2758037 : Blo 1837620 2758037 := bbase (se 6 (by rfl) ⟨64641, by rfl⟩ : syracuseStep 2758037 = 129283) (by norm_num)
theorem B5887397 : Blo 1837620 5887397 := bbase (se 4 (by rfl) ⟨551943, by rfl⟩ : syracuseStep 5887397 = 1103887) (by norm_num)
theorem B2758061 : Blo 1837620 2758061 := bbase (se 3 (by rfl) ⟨517136, by rfl⟩ : syracuseStep 2758061 = 1034273) (by norm_num)
theorem B2758085 : Blo 1837620 2758085 := bbase (se 4 (by rfl) ⟨258570, by rfl⟩ : syracuseStep 2758085 = 517141) (by norm_num)
theorem B2758109 : Blo 1837620 2758109 := bbase (se 3 (by rfl) ⟨517145, by rfl⟩ : syracuseStep 2758109 = 1034291) (by norm_num)
theorem B3978733 : Blo 1837620 3978733 := bbase (se 3 (by rfl) ⟨746012, by rfl⟩ : syracuseStep 3978733 = 1492025) (by norm_num)
theorem B2758133 : Blo 1837620 2758133 := bbase (se 5 (by rfl) ⟨129287, by rfl⟩ : syracuseStep 2758133 = 258575) (by norm_num)
theorem B3102205 : Blo 1837620 3102205 := bbase (se 3 (by rfl) ⟨581663, by rfl⟩ : syracuseStep 3102205 = 1163327) (by norm_num)
theorem B2758157 : Blo 1837620 2758157 := bbase (se 3 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 2758157 = 1034309) (by norm_num)
theorem B5887525 : Blo 1837620 5887525 := bbase (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) (by norm_num)
theorem B2758181 : Blo 1837620 2758181 := bbase (se 4 (by rfl) ⟨258579, by rfl⟩ : syracuseStep 2758181 = 517159) (by norm_num)
theorem B6207029 : Blo 1837620 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B2758205 : Blo 1837620 2758205 := bbase (se 3 (by rfl) ⟨517163, by rfl⟩ : syracuseStep 2758205 = 1034327) (by norm_num)
theorem B3102293 : Blo 1837620 3102293 := bbase (se 8 (by rfl) ⟨18177, by rfl⟩ : syracuseStep 3102293 = 36355) (by norm_num)
theorem B2758229 : Blo 1837620 2758229 := bbase (se 8 (by rfl) ⟨16161, by rfl⟩ : syracuseStep 2758229 = 32323) (by norm_num)
theorem B2758253 : Blo 1837620 2758253 := bbase (se 3 (by rfl) ⟨517172, by rfl⟩ : syracuseStep 2758253 = 1034345) (by norm_num)
theorem B1963649 : Blo 1837620 1963649 := bbase (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) (by norm_num)
theorem B2758277 : Blo 1837620 2758277 := bbase (se 4 (by rfl) ⟨258588, by rfl⟩ : syracuseStep 2758277 = 517177) (by norm_num)
theorem B2758301 : Blo 1837620 2758301 := bbase (se 3 (by rfl) ⟨517181, by rfl⟩ : syracuseStep 2758301 = 1034363) (by norm_num)
theorem B2758325 : Blo 1837620 2758325 := bbase (se 5 (by rfl) ⟨129296, by rfl⟩ : syracuseStep 2758325 = 258593) (by norm_num)
theorem B6624965 : Blo 1837620 6624965 := bbase (se 4 (by rfl) ⟨621090, by rfl⟩ : syracuseStep 6624965 = 1242181) (by norm_num)
theorem B1963721 : Blo 1837620 1963721 := bbase (se 2 (by rfl) ⟨736395, by rfl⟩ : syracuseStep 1963721 = 1472791) (by norm_num)
theorem B2758349 : Blo 1837620 2758349 := bbase (se 3 (by rfl) ⟨517190, by rfl⟩ : syracuseStep 2758349 = 1034381) (by norm_num)
theorem B3102421 : Blo 1837620 3102421 := bbase (se 7 (by rfl) ⟨36356, by rfl⟩ : syracuseStep 3102421 = 72713) (by norm_num)
theorem B2758373 : Blo 1837620 2758373 := bbase (se 4 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 2758373 = 517195) (by norm_num)
theorem B4134653 : Blo 1837620 4134653 := bbase (se 3 (by rfl) ⟨775247, by rfl⟩ : syracuseStep 4134653 = 1550495) (by norm_num)
theorem B2758397 : Blo 1837620 2758397 := bbase (se 3 (by rfl) ⟨517199, by rfl⟩ : syracuseStep 2758397 = 1034399) (by norm_num)
theorem B4970261 : Blo 1837620 4970261 := bbase (se 6 (by rfl) ⟨116490, by rfl⟩ : syracuseStep 4970261 = 232981) (by norm_num)
theorem B2758421 : Blo 1837620 2758421 := bbase (se 6 (by rfl) ⟨64650, by rfl⟩ : syracuseStep 2758421 = 129301) (by norm_num)
theorem B5887781 : Blo 1837620 5887781 := bbase (se 4 (by rfl) ⟨551979, by rfl⟩ : syracuseStep 5887781 = 1103959) (by norm_num)
theorem B3102509 : Blo 1837620 3102509 := bbase (se 3 (by rfl) ⟨581720, by rfl⟩ : syracuseStep 3102509 = 1163441) (by norm_num)
theorem B2758445 : Blo 1837620 2758445 := bbase (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) (by norm_num)
theorem B4134725 : Blo 1837620 4134725 := bbase (se 4 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 4134725 = 775261) (by norm_num)
theorem B2758469 : Blo 1837620 2758469 := bbase (se 4 (by rfl) ⟨258606, by rfl⟩ : syracuseStep 2758469 = 517213) (by norm_num)
theorem B20952917 : Blo 1837620 20952917 := bbase (se 9 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 20952917 = 122771) (by norm_num)
theorem B2758493 : Blo 1837620 2758493 := bbase (se 3 (by rfl) ⟨517217, by rfl⟩ : syracuseStep 2758493 = 1034435) (by norm_num)
theorem B2619229 : Blo 1837620 2619229 := bbase (se 3 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 2619229 = 982211) (by norm_num)
theorem B2758517 : Blo 1837620 2758517 := bbase (se 5 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 2758517 = 258611) (by norm_num)
theorem B1963909 : Blo 1837620 1963909 := bbase (se 4 (by rfl) ⟨184116, by rfl⟩ : syracuseStep 1963909 = 368233) (by norm_num)
theorem B4134797 : Blo 1837620 4134797 := bbase (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) (by norm_num)
theorem B2758541 : Blo 1837620 2758541 := bbase (se 3 (by rfl) ⟨517226, by rfl⟩ : syracuseStep 2758541 = 1034453) (by norm_num)
theorem B2758565 : Blo 1837620 2758565 := bbase (se 4 (by rfl) ⟨258615, by rfl⟩ : syracuseStep 2758565 = 517231) (by norm_num)
theorem B3102637 : Blo 1837620 3102637 := bbase (se 3 (by rfl) ⟨581744, by rfl⟩ : syracuseStep 3102637 = 1163489) (by norm_num)
theorem B2758589 : Blo 1837620 2758589 := bbase (se 3 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 2758589 = 1034471) (by norm_num)
theorem B4134869 : Blo 1837620 4134869 := bbase (se 7 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 4134869 = 96911) (by norm_num)
theorem B2758613 : Blo 1837620 2758613 := bbase (se 7 (by rfl) ⟨32327, by rfl⟩ : syracuseStep 2758613 = 64655) (by norm_num)
theorem B6625253 : Blo 1837620 6625253 := bbase (se 4 (by rfl) ⟨621117, by rfl⟩ : syracuseStep 6625253 = 1242235) (by norm_num)
theorem B6207461 : Blo 1837620 6207461 := bbase (se 4 (by rfl) ⟨581949, by rfl⟩ : syracuseStep 6207461 = 1163899) (by norm_num)
theorem B2758637 : Blo 1837620 2758637 := bbase (se 3 (by rfl) ⟨517244, by rfl⟩ : syracuseStep 2758637 = 1034489) (by norm_num)
theorem B9312245 : Blo 1837620 9312245 := bbase (se 5 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 9312245 = 873023) (by norm_num)
theorem B4249597 : Blo 1837620 4249597 := bbase (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) (by norm_num)
theorem B3102725 : Blo 1837620 3102725 := bbase (se 4 (by rfl) ⟨290880, by rfl⟩ : syracuseStep 3102725 = 581761) (by norm_num)
theorem B2758661 : Blo 1837620 2758661 := bbase (se 4 (by rfl) ⟨258624, by rfl⟩ : syracuseStep 2758661 = 517249) (by norm_num)
theorem B4134941 : Blo 1837620 4134941 := bbase (se 3 (by rfl) ⟨775301, by rfl⟩ : syracuseStep 4134941 = 1550603) (by norm_num)
theorem B2758685 : Blo 1837620 2758685 := bbase (se 3 (by rfl) ⟨517253, by rfl⟩ : syracuseStep 2758685 = 1034507) (by norm_num)
theorem B2758709 : Blo 1837620 2758709 := bbase (se 5 (by rfl) ⟨129314, by rfl⟩ : syracuseStep 2758709 = 258629) (by norm_num)
theorem B1964093 : Blo 1837620 1964093 := bbase (se 3 (by rfl) ⟨368267, by rfl⟩ : syracuseStep 1964093 = 736535) (by norm_num)
theorem B2758733 : Blo 1837620 2758733 := bbase (se 3 (by rfl) ⟨517262, by rfl⟩ : syracuseStep 2758733 = 1034525) (by norm_num)
theorem B19888213 : Blo 1837620 19888213 := bbase (se 8 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 19888213 = 233065) (by norm_num)
theorem B4135013 : Blo 1837620 4135013 := bbase (se 4 (by rfl) ⟨387657, by rfl⟩ : syracuseStep 4135013 = 775315) (by norm_num)
theorem B2758757 : Blo 1837620 2758757 := bbase (se 4 (by rfl) ⟨258633, by rfl⟩ : syracuseStep 2758757 = 517267) (by norm_num)
theorem B2758781 : Blo 1837620 2758781 := bbase (se 3 (by rfl) ⟨517271, by rfl⟩ : syracuseStep 2758781 = 1034543) (by norm_num)
theorem B5036165 : Blo 1837620 5036165 := bbase (se 4 (by rfl) ⟨472140, by rfl⟩ : syracuseStep 5036165 = 944281) (by norm_num)
theorem B3102853 : Blo 1837620 3102853 := bbase (se 4 (by rfl) ⟨290892, by rfl⟩ : syracuseStep 3102853 = 581785) (by norm_num)
theorem B2758805 : Blo 1837620 2758805 := bbase (se 6 (by rfl) ⟨64659, by rfl⟩ : syracuseStep 2758805 = 129319) (by norm_num)
theorem B4135085 : Blo 1837620 4135085 := bbase (se 3 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 4135085 = 1550657) (by norm_num)
theorem B2758829 : Blo 1837620 2758829 := bbase (se 3 (by rfl) ⟨517280, by rfl⟩ : syracuseStep 2758829 = 1034561) (by norm_num)
theorem B2758853 : Blo 1837620 2758853 := bbase (se 4 (by rfl) ⟨258642, by rfl⟩ : syracuseStep 2758853 = 517285) (by norm_num)
theorem B3102941 : Blo 1837620 3102941 := bbase (se 3 (by rfl) ⟨581801, by rfl⟩ : syracuseStep 3102941 = 1163603) (by norm_num)
theorem B2758877 : Blo 1837620 2758877 := bbase (se 3 (by rfl) ⟨517289, by rfl⟩ : syracuseStep 2758877 = 1034579) (by norm_num)
theorem B4135157 : Blo 1837620 4135157 := bbase (se 5 (by rfl) ⟨193835, by rfl⟩ : syracuseStep 4135157 = 387671) (by norm_num)
theorem B2758901 : Blo 1837620 2758901 := bbase (se 5 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 2758901 = 258647) (by norm_num)
theorem B2758925 : Blo 1837620 2758925 := bbase (se 3 (by rfl) ⟨517298, by rfl⟩ : syracuseStep 2758925 = 1034597) (by norm_num)
theorem B2758949 : Blo 1837620 2758949 := bbase (se 4 (by rfl) ⟨258651, by rfl⟩ : syracuseStep 2758949 = 517303) (by norm_num)
theorem B4135229 : Blo 1837620 4135229 := bbase (se 3 (by rfl) ⟨775355, by rfl⟩ : syracuseStep 4135229 = 1550711) (by norm_num)
theorem B2758973 : Blo 1837620 2758973 := bbase (se 3 (by rfl) ⟨517307, by rfl⟩ : syracuseStep 2758973 = 1034615) (by norm_num)
theorem B4479301 : Blo 1837620 4479301 := bbase (se 4 (by rfl) ⟨419934, by rfl⟩ : syracuseStep 4479301 = 839869) (by norm_num)
theorem B2758997 : Blo 1837620 2758997 := bbase (se 10 (by rfl) ⟨4041, by rfl⟩ : syracuseStep 2758997 = 8083) (by norm_num)
theorem B3103069 : Blo 1837620 3103069 := bbase (se 3 (by rfl) ⟨581825, by rfl⟩ : syracuseStep 3103069 = 1163651) (by norm_num)
theorem B2759021 : Blo 1837620 2759021 := bbase (se 3 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 2759021 = 1034633) (by norm_num)
theorem B4135301 : Blo 1837620 4135301 := bbase (se 4 (by rfl) ⟨387684, by rfl⟩ : syracuseStep 4135301 = 775369) (by norm_num)
theorem B2759045 : Blo 1837620 2759045 := bbase (se 4 (by rfl) ⟨258660, by rfl⟩ : syracuseStep 2759045 = 517321) (by norm_num)
theorem B9304469 : Blo 1837620 9304469 := bbase (se 6 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 9304469 = 436147) (by norm_num)
theorem B6207893 : Blo 1837620 6207893 := bbase (se 6 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 6207893 = 290995) (by norm_num)
theorem B2759069 : Blo 1837620 2759069 := bbase (se 3 (by rfl) ⟨517325, by rfl⟩ : syracuseStep 2759069 = 1034651) (by norm_num)
theorem B3103157 : Blo 1837620 3103157 := bbase (se 5 (by rfl) ⟨145460, by rfl⟩ : syracuseStep 3103157 = 290921) (by norm_num)
theorem B2759093 : Blo 1837620 2759093 := bbase (se 5 (by rfl) ⟨129332, by rfl⟩ : syracuseStep 2759093 = 258665) (by norm_num)
theorem B4135373 : Blo 1837620 4135373 := bbase (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) (by norm_num)
theorem B2759117 : Blo 1837620 2759117 := bbase (se 3 (by rfl) ⟨517334, by rfl⟩ : syracuseStep 2759117 = 1034669) (by norm_num)
theorem B3725797 : Blo 1837620 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B2759141 : Blo 1837620 2759141 := bbase (se 4 (by rfl) ⟨258669, by rfl⟩ : syracuseStep 2759141 = 517339) (by norm_num)
theorem B4536829 : Blo 1837620 4536829 := bbase (se 3 (by rfl) ⟨850655, by rfl⟩ : syracuseStep 4536829 = 1701311) (by norm_num)
theorem B2759165 : Blo 1837620 2759165 := bbase (se 3 (by rfl) ⟨517343, by rfl⟩ : syracuseStep 2759165 = 1034687) (by norm_num)
theorem B4135445 : Blo 1837620 4135445 := bbase (se 6 (by rfl) ⟨96924, by rfl⟩ : syracuseStep 4135445 = 193849) (by norm_num)
theorem B2759189 : Blo 1837620 2759189 := bbase (se 6 (by rfl) ⟨64668, by rfl⟩ : syracuseStep 2759189 = 129337) (by norm_num)
theorem B2759213 : Blo 1837620 2759213 := bbase (se 3 (by rfl) ⟨517352, by rfl⟩ : syracuseStep 2759213 = 1034705) (by norm_num)
theorem B10467893 : Blo 1837620 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B3103285 : Blo 1837620 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B2759237 : Blo 1837620 2759237 := bbase (se 4 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 2759237 = 517357) (by norm_num)
theorem B4135517 : Blo 1837620 4135517 := bbase (se 3 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 4135517 = 1550819) (by norm_num)
theorem B2759261 : Blo 1837620 2759261 := bbase (se 3 (by rfl) ⟨517361, by rfl⟩ : syracuseStep 2759261 = 1034723) (by norm_num)
theorem B2759285 : Blo 1837620 2759285 := bbase (se 5 (by rfl) ⟨129341, by rfl⟩ : syracuseStep 2759285 = 258683) (by norm_num)
theorem B3103373 : Blo 1837620 3103373 := bbase (se 3 (by rfl) ⟨581882, by rfl⟩ : syracuseStep 3103373 = 1163765) (by norm_num)
theorem B2759309 : Blo 1837620 2759309 := bbase (se 3 (by rfl) ⟨517370, by rfl⟩ : syracuseStep 2759309 = 1034741) (by norm_num)
theorem B4135589 : Blo 1837620 4135589 := bbase (se 4 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 4135589 = 775423) (by norm_num)
theorem B2759333 : Blo 1837620 2759333 := bbase (se 4 (by rfl) ⟨258687, by rfl⟩ : syracuseStep 2759333 = 517375) (by norm_num)
theorem B2759357 : Blo 1837620 2759357 := bbase (se 3 (by rfl) ⟨517379, by rfl⟩ : syracuseStep 2759357 = 1034759) (by norm_num)
theorem B2759381 : Blo 1837620 2759381 := bbase (se 7 (by rfl) ⟨32336, by rfl⟩ : syracuseStep 2759381 = 64673) (by norm_num)
theorem B4135661 : Blo 1837620 4135661 := bbase (se 3 (by rfl) ⟨775436, by rfl⟩ : syracuseStep 4135661 = 1550873) (by norm_num)
theorem B2759405 : Blo 1837620 2759405 := bbase (se 3 (by rfl) ⟨517388, by rfl⟩ : syracuseStep 2759405 = 1034777) (by norm_num)
theorem B3144437 : Blo 1837620 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B10074869 : Blo 1837620 10074869 := bbase (se 5 (by rfl) ⟨472259, by rfl⟩ : syracuseStep 10074869 = 944519) (by norm_num)
theorem B2759429 : Blo 1837620 2759429 := bbase (se 4 (by rfl) ⟨258696, by rfl⟩ : syracuseStep 2759429 = 517393) (by norm_num)
theorem B4651789 : Blo 1837620 4651789 := bbase (se 3 (by rfl) ⟨872210, by rfl⟩ : syracuseStep 4651789 = 1744421) (by norm_num)
theorem B3103501 : Blo 1837620 3103501 := bbase (se 3 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 3103501 = 1163813) (by norm_num)
theorem B4135733 : Blo 1837620 4135733 := bbase (se 5 (by rfl) ⟨193862, by rfl⟩ : syracuseStep 4135733 = 387725) (by norm_num)
theorem B6208325 : Blo 1837620 6208325 := bbase (se 4 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 6208325 = 1164061) (by norm_num)
theorem B290437973 : Blo 1837620 290437973 := bbase (se 9 (by rfl) ⟨850892, by rfl⟩ : syracuseStep 290437973 = 1701785) (by norm_num)
theorem B23886677 : Blo 1837620 23886677 := bbase (se 9 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 23886677 = 139961) (by norm_num)
theorem B3103589 : Blo 1837620 3103589 := bbase (se 4 (by rfl) ⟨290961, by rfl⟩ : syracuseStep 3103589 = 581923) (by norm_num)
theorem B4651901 : Blo 1837620 4651901 := bbase (se 3 (by rfl) ⟨872231, by rfl⟩ : syracuseStep 4651901 = 1744463) (by norm_num)
theorem B4135805 : Blo 1837620 4135805 := bbase (se 3 (by rfl) ⟨775463, by rfl⟩ : syracuseStep 4135805 = 1550927) (by norm_num)
theorem B3488645 : Blo 1837620 3488645 := bbase (se 4 (by rfl) ⟨327060, by rfl⟩ : syracuseStep 3488645 = 654121) (by norm_num)
theorem B4135877 : Blo 1837620 4135877 := bbase (se 4 (by rfl) ⟨387738, by rfl⟩ : syracuseStep 4135877 = 775477) (by norm_num)
theorem B4193237 : Blo 1837620 4193237 := bbase (se 7 (by rfl) ⟨49139, by rfl⟩ : syracuseStep 4193237 = 98279) (by norm_num)
theorem B3103717 : Blo 1837620 3103717 := bbase (se 4 (by rfl) ⟨290973, by rfl⟩ : syracuseStep 3103717 = 581947) (by norm_num)
theorem B4135949 : Blo 1837620 4135949 := bbase (se 3 (by rfl) ⟨775490, by rfl⟩ : syracuseStep 4135949 = 1550981) (by norm_num)
theorem B6978581 : Blo 1837620 6978581 := bbase (se 6 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 6978581 = 327121) (by norm_num)
theorem B3726373 : Blo 1837620 3726373 := bbase (se 4 (by rfl) ⟨349347, by rfl⟩ : syracuseStep 3726373 = 698695) (by norm_num)
theorem B7855157 : Blo 1837620 7855157 := bbase (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) (by norm_num)
theorem B4652093 : Blo 1837620 4652093 := bbase (se 3 (by rfl) ⟨872267, by rfl⟩ : syracuseStep 4652093 = 1744535) (by norm_num)
theorem B3103805 : Blo 1837620 3103805 := bbase (se 3 (by rfl) ⟨581963, by rfl⟩ : syracuseStep 3103805 = 1163927) (by norm_num)
theorem B4136021 : Blo 1837620 4136021 := bbase (se 8 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 4136021 = 48469) (by norm_num)
theorem B1989725 : Blo 1837620 1989725 := bbase (se 3 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 1989725 = 746147) (by norm_num)
theorem B6626405 : Blo 1837620 6626405 := bbase (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) (by norm_num)
theorem B4136093 : Blo 1837620 4136093 := bbase (se 3 (by rfl) ⟨775517, by rfl⟩ : syracuseStep 4136093 = 1551035) (by norm_num)
theorem B3488933 : Blo 1837620 3488933 := bbase (se 4 (by rfl) ⟨327087, by rfl⟩ : syracuseStep 3488933 = 654175) (by norm_num)
theorem B3103933 : Blo 1837620 3103933 := bbase (se 3 (by rfl) ⟨581987, by rfl⟩ : syracuseStep 3103933 = 1163975) (by norm_num)
theorem B4136165 : Blo 1837620 4136165 := bbase (se 4 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 4136165 = 775531) (by norm_num)
theorem B2358521 : Blo 1837620 2358521 := bbase (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) (by norm_num)
theorem B2325773 : Blo 1837620 2325773 := bbase (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) (by norm_num)
theorem B3104021 : Blo 1837620 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B4136237 : Blo 1837620 4136237 := bbase (se 3 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 4136237 = 1551089) (by norm_num)
theorem B6978869 : Blo 1837620 6978869 := bbase (se 5 (by rfl) ⟨327134, by rfl⟩ : syracuseStep 6978869 = 654269) (by norm_num)
theorem B8502581 : Blo 1837620 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B3489085 : Blo 1837620 3489085 := bbase (se 3 (by rfl) ⟨654203, by rfl⟩ : syracuseStep 3489085 = 1308407) (by norm_num)
theorem B2325829 : Blo 1837620 2325829 := bbase (se 4 (by rfl) ⟨218046, by rfl⟩ : syracuseStep 2325829 = 436093) (by norm_num)
theorem B3145037 : Blo 1837620 3145037 := bbase (se 3 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 3145037 = 1179389) (by norm_num)
theorem B4136309 : Blo 1837620 4136309 := bbase (se 5 (by rfl) ⟨193889, by rfl⟩ : syracuseStep 4136309 = 387779) (by norm_num)
theorem B4652437 : Blo 1837620 4652437 := bbase (se 6 (by rfl) ⟨109041, by rfl⟩ : syracuseStep 4652437 = 218083) (by norm_num)
theorem B3104149 : Blo 1837620 3104149 := bbase (se 6 (by rfl) ⟨72753, by rfl⟩ : syracuseStep 3104149 = 145507) (by norm_num)
theorem B2325925 : Blo 1837620 2325925 := bbase (se 4 (by rfl) ⟨218055, by rfl⟩ : syracuseStep 2325925 = 436111) (by norm_num)
theorem B4136381 : Blo 1837620 4136381 := bbase (se 3 (by rfl) ⟨775571, by rfl⟩ : syracuseStep 4136381 = 1551143) (by norm_num)
theorem B3104237 : Blo 1837620 3104237 := bbase (se 3 (by rfl) ⟨582044, by rfl⟩ : syracuseStep 3104237 = 1164089) (by norm_num)
theorem B4652549 : Blo 1837620 4652549 := bbase (se 4 (by rfl) ⟨436176, by rfl⟩ : syracuseStep 4652549 = 872353) (by norm_num)
theorem B4136453 : Blo 1837620 4136453 := bbase (se 4 (by rfl) ⟨387792, by rfl⟩ : syracuseStep 4136453 = 775585) (by norm_num)
theorem B4136525 : Blo 1837620 4136525 := bbase (se 3 (by rfl) ⟨775598, by rfl⟩ : syracuseStep 4136525 = 1551197) (by norm_num)
theorem B2326097 : Blo 1837620 2326097 := bbase (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) (by norm_num)
theorem B3489389 : Blo 1837620 3489389 := bbase (se 3 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 3489389 = 1308521) (by norm_num)
theorem B3726965 : Blo 1837620 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B2326153 : Blo 1837620 2326153 := bbase (se 2 (by rfl) ⟨872307, by rfl⟩ : syracuseStep 2326153 = 1744615) (by norm_num)
theorem B4136597 : Blo 1837620 4136597 := bbase (se 6 (by rfl) ⟨96951, by rfl⟩ : syracuseStep 4136597 = 193903) (by norm_num)
theorem B9305765 : Blo 1837620 9305765 := bbase (se 4 (by rfl) ⟨872415, by rfl⟩ : syracuseStep 9305765 = 1744831) (by norm_num)
theorem B8838821 : Blo 1837620 8838821 := bbase (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) (by norm_num)
theorem B5234357 : Blo 1837620 5234357 := bbase (se 5 (by rfl) ⟨245360, by rfl⟩ : syracuseStep 5234357 = 490721) (by norm_num)
theorem B1990337 : Blo 1837620 1990337 := bbase (se 2 (by rfl) ⟨746376, by rfl⟩ : syracuseStep 1990337 = 1492753) (by norm_num)
theorem B4652741 : Blo 1837620 4652741 := bbase (se 4 (by rfl) ⟨436194, by rfl⟩ : syracuseStep 4652741 = 872389) (by norm_num)
theorem B4136669 : Blo 1837620 4136669 := bbase (se 3 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 4136669 = 1551251) (by norm_num)
theorem B2326249 : Blo 1837620 2326249 := bbase (se 2 (by rfl) ⟨872343, by rfl⟩ : syracuseStep 2326249 = 1744687) (by norm_num)
theorem B4136741 : Blo 1837620 4136741 := bbase (se 4 (by rfl) ⟨387819, by rfl⟩ : syracuseStep 4136741 = 775639) (by norm_num)
theorem B4136813 : Blo 1837620 4136813 := bbase (se 3 (by rfl) ⟨775652, by rfl⟩ : syracuseStep 4136813 = 1551305) (by norm_num)
theorem B2326421 : Blo 1837620 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B4415413 : Blo 1837620 4415413 := bbase (se 5 (by rfl) ⟨206972, by rfl⟩ : syracuseStep 4415413 = 413945) (by norm_num)
theorem B8830901 : Blo 1837620 8830901 := bbase (se 5 (by rfl) ⟨413948, by rfl⟩ : syracuseStep 8830901 = 827897) (by norm_num)
theorem B4136885 : Blo 1837620 4136885 := bbase (se 5 (by rfl) ⟨193916, by rfl⟩ : syracuseStep 4136885 = 387833) (by norm_num)
theorem B2326477 : Blo 1837620 2326477 := bbase (se 3 (by rfl) ⟨436214, by rfl⟩ : syracuseStep 2326477 = 872429) (by norm_num)
theorem B4136957 : Blo 1837620 4136957 := bbase (se 3 (by rfl) ⟨775679, by rfl⟩ : syracuseStep 4136957 = 1551359) (by norm_num)
theorem B3489905 : Blo 1837620 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B26517617 : Blo 1837620 26517617 := bstep (se 2 (by rfl) ⟨9944106, by rfl⟩ : syracuseStep 26517617 = 19888213) B19888213
theorem B20947085 : Blo 1837620 20947085 := bstep (se 3 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 20947085 = 7855157) B7855157
theorem B4137137 : Blo 1837620 4137137 := bstep (se 2 (by rfl) ⟨1551426, by rfl⟩ : syracuseStep 4137137 = 3102853) B3102853
theorem B4137155 : Blo 1837620 4137155 := bstep (se 1 (by rfl) ⟨3102866, by rfl⟩ : syracuseStep 4137155 = 6205733) B6205733
theorem B17670413 : Blo 1837620 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B5972401 : Blo 1837620 5972401 := bstep (se 2 (by rfl) ⟨2239650, by rfl⟩ : syracuseStep 5972401 = 4479301) B4479301
theorem B2326963 : Blo 1837620 2326963 := bstep (se 1 (by rfl) ⟨1745222, by rfl⟩ : syracuseStep 2326963 = 3490445) B3490445
theorem B4653521 : Blo 1837620 4653521 := bstep (se 2 (by rfl) ⟨1745070, by rfl⟩ : syracuseStep 4653521 = 3490141) B3490141
theorem B4137425 : Blo 1837620 4137425 := bstep (se 2 (by rfl) ⟨1551534, by rfl⟩ : syracuseStep 4137425 = 3103069) B3103069
theorem B4137443 : Blo 1837620 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B5308913 : Blo 1837620 5308913 := bstep (se 2 (by rfl) ⟨1990842, by rfl⟩ : syracuseStep 5308913 = 3981685) B3981685
theorem B2359795 : Blo 1837620 2359795 := bstep (se 1 (by rfl) ⟨1769846, by rfl⟩ : syracuseStep 2359795 = 3539693) B3539693
theorem B4653571 : Blo 1837620 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B8831501 : Blo 1837620 8831501 := bstep (se 3 (by rfl) ⟨1655906, by rfl⟩ : syracuseStep 8831501 = 3311813) B3311813
theorem B2327059 : Blo 1837620 2327059 := bstep (se 1 (by rfl) ⟨1745294, by rfl⟩ : syracuseStep 2327059 = 3490589) B3490589
theorem B3727939 : Blo 1837620 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B17916485 : Blo 1837620 17916485 := bstep (se 4 (by rfl) ⟨1679670, by rfl⟩ : syracuseStep 17916485 = 3359341) B3359341
theorem B9306737 : Blo 1837620 9306737 := bstep (se 2 (by rfl) ⟨3490026, by rfl⟩ : syracuseStep 9306737 = 6980053) B6980053
theorem B4653713 : Blo 1837620 4653713 := bstep (se 2 (by rfl) ⟨1745142, by rfl⟩ : syracuseStep 4653713 = 3490285) B3490285
theorem B6202061 : Blo 1837620 6202061 := bstep (se 3 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 6202061 = 2325773) B2325773
theorem B4137713 : Blo 1837620 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B6202115 : Blo 1837620 6202115 := bstep (se 1 (by rfl) ⟨4651586, by rfl⟩ : syracuseStep 6202115 = 9303173) B9303173
theorem B4137731 : Blo 1837620 4137731 := bstep (se 1 (by rfl) ⟨3103298, by rfl⟩ : syracuseStep 4137731 = 6206597) B6206597
theorem B6292237 : Blo 1837620 6292237 := bstep (se 3 (by rfl) ⟨1179794, by rfl⟩ : syracuseStep 6292237 = 2359589) B2359589
theorem B2835233 : Blo 1837620 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B33547061 : Blo 1837620 33547061 := bstep (se 5 (by rfl) ⟨1572518, by rfl⟩ : syracuseStep 33547061 = 3145037) B3145037
theorem B3490627 : Blo 1837620 3490627 := bstep (se 1 (by rfl) ⟨2617970, by rfl⟩ : syracuseStep 3490627 = 5235941) B5235941
theorem B5235587 : Blo 1837620 5235587 := bstep (se 1 (by rfl) ⟨3926690, by rfl⟩ : syracuseStep 5235587 = 7853381) B7853381
theorem B3924931 : Blo 1837620 3924931 := bstep (se 1 (by rfl) ⟨2943698, by rfl⟩ : syracuseStep 3924931 = 5887397) B5887397
theorem B2327555 : Blo 1837620 2327555 := bstep (se 1 (by rfl) ⟨1745666, by rfl⟩ : syracuseStep 2327555 = 3491333) B3491333
theorem B6202385 : Blo 1837620 6202385 := bstep (se 2 (by rfl) ⟨2325894, by rfl⟩ : syracuseStep 6202385 = 4651789) B4651789
theorem B4138001 : Blo 1837620 4138001 := bstep (se 2 (by rfl) ⟨1551750, by rfl⟩ : syracuseStep 4138001 = 3103501) B3103501
theorem B4138019 : Blo 1837620 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B4416643 : Blo 1837620 4416643 := bstep (se 1 (by rfl) ⟨3312482, by rfl⟩ : syracuseStep 4416643 = 6624965) B6624965
theorem B3925187 : Blo 1837620 3925187 := bstep (se 1 (by rfl) ⟨2943890, by rfl⟩ : syracuseStep 3925187 = 5887781) B5887781
theorem B6980813 : Blo 1837620 6980813 := bstep (se 3 (by rfl) ⟨1308902, by rfl⟩ : syracuseStep 6980813 = 2617805) B2617805
theorem B13968611 : Blo 1837620 13968611 := bstep (se 1 (by rfl) ⟨10476458, by rfl⟩ : syracuseStep 13968611 = 20952917) B20952917
theorem B3491075 : Blo 1837620 3491075 := bstep (se 1 (by rfl) ⟨2618306, by rfl⟩ : syracuseStep 3491075 = 5236613) B5236613
theorem B4138289 : Blo 1837620 4138289 := bstep (se 2 (by rfl) ⟨1551858, by rfl⟩ : syracuseStep 4138289 = 3103717) B3103717
theorem B4416835 : Blo 1837620 4416835 := bstep (se 1 (by rfl) ⟨3312626, by rfl⟩ : syracuseStep 4416835 = 6625253) B6625253
theorem B4138307 : Blo 1837620 4138307 := bstep (se 1 (by rfl) ⟨3103730, by rfl⟩ : syracuseStep 4138307 = 6207461) B6207461
theorem B6219089 : Blo 1837620 6219089 := bstep (se 2 (by rfl) ⟨2332158, by rfl⟩ : syracuseStep 6219089 = 4664317) B4664317
theorem B8390051 : Blo 1837620 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B5973517 : Blo 1837620 5973517 := bstep (se 3 (by rfl) ⟨1120034, by rfl⟩ : syracuseStep 5973517 = 2240069) B2240069
theorem B3491363 : Blo 1837620 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B6202925 : Blo 1837620 6202925 := bstep (se 3 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 6202925 = 2326097) B2326097
theorem B4417105 : Blo 1837620 4417105 := bstep (se 2 (by rfl) ⟨1656414, by rfl⟩ : syracuseStep 4417105 = 3312829) B3312829
theorem B4138577 : Blo 1837620 4138577 := bstep (se 2 (by rfl) ⟨1551966, by rfl⟩ : syracuseStep 4138577 = 3103933) B3103933
theorem B6202979 : Blo 1837620 6202979 := bstep (se 1 (by rfl) ⟨4652234, by rfl⟩ : syracuseStep 6202979 = 9304469) B9304469
theorem B4138595 : Blo 1837620 4138595 := bstep (se 1 (by rfl) ⟨3103946, by rfl⟩ : syracuseStep 4138595 = 6207893) B6207893
theorem B4654705 : Blo 1837620 4654705 := bstep (se 2 (by rfl) ⟨1745514, by rfl⟩ : syracuseStep 4654705 = 3491029) B3491029
theorem B5236397 : Blo 1837620 5236397 := bstep (se 3 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 5236397 = 1963649) B1963649
theorem B2328259 : Blo 1837620 2328259 := bstep (se 1 (by rfl) ⟨1746194, by rfl⟩ : syracuseStep 2328259 = 3492389) B3492389
theorem B19883717 : Blo 1837620 19883717 := bstep (se 4 (by rfl) ⟨1864098, by rfl⟩ : syracuseStep 19883717 = 3728197) B3728197
theorem B23570189 : Blo 1837620 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B5973773 : Blo 1837620 5973773 := bstep (se 3 (by rfl) ⟨1120082, by rfl⟩ : syracuseStep 5973773 = 2240165) B2240165
theorem B5236589 : Blo 1837620 5236589 := bstep (se 3 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 5236589 = 1963721) B1963721
theorem B6203249 : Blo 1837620 6203249 := bstep (se 2 (by rfl) ⟨2326218, by rfl⟩ : syracuseStep 6203249 = 4652437) B4652437
theorem B4138865 : Blo 1837620 4138865 := bstep (se 2 (by rfl) ⟨1552074, by rfl⟩ : syracuseStep 4138865 = 3104149) B3104149
theorem B4654979 : Blo 1837620 4654979 := bstep (se 1 (by rfl) ⟨3491234, by rfl⟩ : syracuseStep 4654979 = 6982469) B6982469
theorem B4138883 : Blo 1837620 4138883 := bstep (se 1 (by rfl) ⟨3104162, by rfl⟩ : syracuseStep 4138883 = 6208325) B6208325
theorem B2795491 : Blo 1837620 2795491 := bstep (se 1 (by rfl) ⟨2096618, by rfl⟩ : syracuseStep 2795491 = 4193237) B4193237
theorem B29820899 : Blo 1837620 29820899 := bstep (se 1 (by rfl) ⟨22365674, by rfl⟩ : syracuseStep 29820899 = 44731349) B44731349
theorem B9308195 : Blo 1837620 9308195 := bstep (se 1 (by rfl) ⟨6981146, by rfl⟩ : syracuseStep 9308195 = 13962293) B13962293
theorem B7850033 : Blo 1837620 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B4655171 : Blo 1837620 4655171 := bstep (se 1 (by rfl) ⟨3491378, by rfl⟩ : syracuseStep 4655171 = 6982757) B6982757
theorem B3926161 : Blo 1837620 3926161 := bstep (se 2 (by rfl) ⟨1472310, by rfl⟩ : syracuseStep 3926161 = 2944621) B2944621
theorem B4417681 : Blo 1837620 4417681 := bstep (se 2 (by rfl) ⟨1656630, by rfl⟩ : syracuseStep 4417681 = 3313261) B3313261
theorem B6203789 : Blo 1837620 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B5892497 : Blo 1837620 5892497 := bstep (se 2 (by rfl) ⟨2209686, by rfl⟩ : syracuseStep 5892497 = 4419373) B4419373
theorem B2484643 : Blo 1837620 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B6203843 : Blo 1837620 6203843 := bstep (se 1 (by rfl) ⟨4652882, by rfl⟩ : syracuseStep 6203843 = 9305765) B9305765
theorem B20941253 : Blo 1837620 20941253 := bstep (se 4 (by rfl) ⟨1963242, by rfl⟩ : syracuseStep 20941253 = 3926485) B3926485
theorem B3492305 : Blo 1837620 3492305 := bstep (se 2 (by rfl) ⟨1309614, by rfl⟩ : syracuseStep 3492305 = 2619229) B2619229
theorem B10471949 : Blo 1837620 10471949 := bstep (se 3 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 10471949 = 3926981) B3926981
theorem B4418065 : Blo 1837620 4418065 := bstep (se 2 (by rfl) ⟨1656774, by rfl⟩ : syracuseStep 4418065 = 3313549) B3313549
theorem B1837635 : Blo 1837620 1837635 := bstep (se 1 (by rfl) ⟨1378226, by rfl⟩ : syracuseStep 1837635 = 2756453) B2756453
theorem B5892689 : Blo 1837620 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B1837651 : Blo 1837620 1837651 := bstep (se 1 (by rfl) ⟨1378238, by rfl⟩ : syracuseStep 1837651 = 2756477) B2756477
theorem B1837667 : Blo 1837620 1837667 := bstep (se 1 (by rfl) ⟨1378250, by rfl⟩ : syracuseStep 1837667 = 2756501) B2756501
theorem B1837683 : Blo 1837620 1837683 := bstep (se 1 (by rfl) ⟨1378262, by rfl⟩ : syracuseStep 1837683 = 2756525) B2756525
theorem B1837699 : Blo 1837620 1837699 := bstep (se 1 (by rfl) ⟨1378274, by rfl⟩ : syracuseStep 1837699 = 2756549) B2756549
theorem B1837715 : Blo 1837620 1837715 := bstep (se 1 (by rfl) ⟨1378286, by rfl⟩ : syracuseStep 1837715 = 2756573) B2756573
theorem B1837731 : Blo 1837620 1837731 := bstep (se 1 (by rfl) ⟨1378298, by rfl⟩ : syracuseStep 1837731 = 2756597) B2756597
theorem B1837747 : Blo 1837620 1837747 := bstep (se 1 (by rfl) ⟨1378310, by rfl⟩ : syracuseStep 1837747 = 2756621) B2756621
theorem B1837763 : Blo 1837620 1837763 := bstep (se 1 (by rfl) ⟨1378322, by rfl⟩ : syracuseStep 1837763 = 2756645) B2756645
theorem B6204113 : Blo 1837620 6204113 := bstep (se 2 (by rfl) ⟨2326542, by rfl⟩ : syracuseStep 6204113 = 4653085) B4653085
theorem B1837779 : Blo 1837620 1837779 := bstep (se 1 (by rfl) ⟨1378334, by rfl⟩ : syracuseStep 1837779 = 2756669) B2756669
theorem B1837795 : Blo 1837620 1837795 := bstep (se 1 (by rfl) ⟨1378346, by rfl⟩ : syracuseStep 1837795 = 2756693) B2756693
theorem B1837811 : Blo 1837620 1837811 := bstep (se 1 (by rfl) ⟨1378358, by rfl⟩ : syracuseStep 1837811 = 2756717) B2756717
theorem B1837827 : Blo 1837620 1837827 := bstep (se 1 (by rfl) ⟨1378370, by rfl⟩ : syracuseStep 1837827 = 2756741) B2756741
theorem B1837843 : Blo 1837620 1837843 := bstep (se 1 (by rfl) ⟨1378382, by rfl⟩ : syracuseStep 1837843 = 2756765) B2756765
theorem B1837859 : Blo 1837620 1837859 := bstep (se 1 (by rfl) ⟨1378394, by rfl⟩ : syracuseStep 1837859 = 2756789) B2756789
theorem B3926819 : Blo 1837620 3926819 := bstep (se 1 (by rfl) ⟨2945114, by rfl⟩ : syracuseStep 3926819 = 5890229) B5890229
theorem B1837875 : Blo 1837620 1837875 := bstep (se 1 (by rfl) ⟨1378406, by rfl⟩ : syracuseStep 1837875 = 2756813) B2756813
theorem B1837891 : Blo 1837620 1837891 := bstep (se 1 (by rfl) ⟨1378418, by rfl⟩ : syracuseStep 1837891 = 2756837) B2756837
theorem B9309005 : Blo 1837620 9309005 := bstep (se 3 (by rfl) ⟨1745438, by rfl⟩ : syracuseStep 9309005 = 3490877) B3490877
theorem B5237581 : Blo 1837620 5237581 := bstep (se 3 (by rfl) ⟨982046, by rfl⟩ : syracuseStep 5237581 = 1964093) B1964093
theorem B1837907 : Blo 1837620 1837907 := bstep (se 1 (by rfl) ⟨1378430, by rfl⟩ : syracuseStep 1837907 = 2756861) B2756861
theorem B1837923 : Blo 1837620 1837923 := bstep (se 1 (by rfl) ⟨1378442, by rfl⟩ : syracuseStep 1837923 = 2756885) B2756885
theorem B1837939 : Blo 1837620 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B2067331 : Blo 1837620 2067331 := bstep (se 1 (by rfl) ⟨1550498, by rfl⟩ : syracuseStep 2067331 = 3100997) B3100997
theorem B1837955 : Blo 1837620 1837955 := bstep (se 1 (by rfl) ⟨1378466, by rfl⟩ : syracuseStep 1837955 = 2756933) B2756933
theorem B1837971 : Blo 1837620 1837971 := bstep (se 1 (by rfl) ⟨1378478, by rfl⟩ : syracuseStep 1837971 = 2756957) B2756957
theorem B1837987 : Blo 1837620 1837987 := bstep (se 1 (by rfl) ⟨1378490, by rfl⟩ : syracuseStep 1837987 = 2756981) B2756981
theorem B1838003 : Blo 1837620 1838003 := bstep (se 1 (by rfl) ⟨1378502, by rfl⟩ : syracuseStep 1838003 = 2757005) B2757005
theorem B1838019 : Blo 1837620 1838019 := bstep (se 1 (by rfl) ⟨1378514, by rfl⟩ : syracuseStep 1838019 = 2757029) B2757029
theorem B2943955 : Blo 1837620 2943955 := bstep (se 1 (by rfl) ⟨2207966, by rfl⟩ : syracuseStep 2943955 = 4415933) B4415933
theorem B1838035 : Blo 1837620 1838035 := bstep (se 1 (by rfl) ⟨1378526, by rfl⟩ : syracuseStep 1838035 = 2757053) B2757053
theorem B1838051 : Blo 1837620 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B20950001 : Blo 1837620 20950001 := bstep (se 2 (by rfl) ⟨7856250, by rfl⟩ : syracuseStep 20950001 = 15712501) B15712501
theorem B1838067 : Blo 1837620 1838067 := bstep (se 1 (by rfl) ⟨1378550, by rfl⟩ : syracuseStep 1838067 = 2757101) B2757101
theorem B4656113 : Blo 1837620 4656113 := bstep (se 2 (by rfl) ⟨1746042, by rfl⟩ : syracuseStep 4656113 = 3492085) B3492085
theorem B1838083 : Blo 1837620 1838083 := bstep (se 1 (by rfl) ⟨1378562, by rfl⟩ : syracuseStep 1838083 = 2757125) B2757125
theorem B2067475 : Blo 1837620 2067475 := bstep (se 1 (by rfl) ⟨1550606, by rfl⟩ : syracuseStep 2067475 = 3101213) B3101213
theorem B2944019 : Blo 1837620 2944019 := bstep (se 1 (by rfl) ⟨2208014, by rfl⟩ : syracuseStep 2944019 = 4416029) B4416029
theorem B1838099 : Blo 1837620 1838099 := bstep (se 1 (by rfl) ⟨1378574, by rfl⟩ : syracuseStep 1838099 = 2757149) B2757149
theorem B1838115 : Blo 1837620 1838115 := bstep (se 1 (by rfl) ⟨1378586, by rfl⟩ : syracuseStep 1838115 = 2757173) B2757173
theorem B2124835 : Blo 1837620 2124835 := bstep (se 1 (by rfl) ⟨1593626, by rfl⟩ : syracuseStep 2124835 = 3187253) B3187253
theorem B4656163 : Blo 1837620 4656163 := bstep (se 1 (by rfl) ⟨3492122, by rfl⟩ : syracuseStep 4656163 = 6984245) B6984245
theorem B1838131 : Blo 1837620 1838131 := bstep (se 1 (by rfl) ⟨1378598, by rfl⟩ : syracuseStep 1838131 = 2757197) B2757197
theorem B1838147 : Blo 1837620 1838147 := bstep (se 1 (by rfl) ⟨1378610, by rfl⟩ : syracuseStep 1838147 = 2757221) B2757221
theorem B2796611 : Blo 1837620 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1838163 : Blo 1837620 1838163 := bstep (se 1 (by rfl) ⟨1378622, by rfl⟩ : syracuseStep 1838163 = 2757245) B2757245
theorem B1838179 : Blo 1837620 1838179 := bstep (se 1 (by rfl) ⟨1378634, by rfl⟩ : syracuseStep 1838179 = 2757269) B2757269
theorem B1838195 : Blo 1837620 1838195 := bstep (se 1 (by rfl) ⟨1378646, by rfl⟩ : syracuseStep 1838195 = 2757293) B2757293
theorem B1838211 : Blo 1837620 1838211 := bstep (se 1 (by rfl) ⟨1378658, by rfl⟩ : syracuseStep 1838211 = 2757317) B2757317
theorem B1838227 : Blo 1837620 1838227 := bstep (se 1 (by rfl) ⟨1378670, by rfl⟩ : syracuseStep 1838227 = 2757341) B2757341
theorem B2067619 : Blo 1837620 2067619 := bstep (se 1 (by rfl) ⟨1550714, by rfl⟩ : syracuseStep 2067619 = 3101429) B3101429
theorem B1838243 : Blo 1837620 1838243 := bstep (se 1 (by rfl) ⟨1378682, by rfl⟩ : syracuseStep 1838243 = 2757365) B2757365
theorem B4656305 : Blo 1837620 4656305 := bstep (se 2 (by rfl) ⟨1746114, by rfl⟩ : syracuseStep 4656305 = 3492229) B3492229
theorem B1838259 : Blo 1837620 1838259 := bstep (se 1 (by rfl) ⟨1378694, by rfl⟩ : syracuseStep 1838259 = 2757389) B2757389
theorem B1838275 : Blo 1837620 1838275 := bstep (se 1 (by rfl) ⟨1378706, by rfl⟩ : syracuseStep 1838275 = 2757413) B2757413
theorem B1838291 : Blo 1837620 1838291 := bstep (se 1 (by rfl) ⟨1378718, by rfl⟩ : syracuseStep 1838291 = 2757437) B2757437
theorem B11775203 : Blo 1837620 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B35810531 : Blo 1837620 35810531 := bstep (se 1 (by rfl) ⟨26857898, by rfl⟩ : syracuseStep 35810531 = 53715797) B53715797
theorem B1838307 : Blo 1837620 1838307 := bstep (se 1 (by rfl) ⟨1378730, by rfl⟩ : syracuseStep 1838307 = 2757461) B2757461
theorem B6204653 : Blo 1837620 6204653 := bstep (se 3 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 6204653 = 2326745) B2326745
theorem B1838323 : Blo 1837620 1838323 := bstep (se 1 (by rfl) ⟨1378742, by rfl⟩ : syracuseStep 1838323 = 2757485) B2757485
theorem B4476163 : Blo 1837620 4476163 := bstep (se 1 (by rfl) ⟨3357122, by rfl⟩ : syracuseStep 4476163 = 6714245) B6714245
theorem B1838339 : Blo 1837620 1838339 := bstep (se 1 (by rfl) ⟨1378754, by rfl⟩ : syracuseStep 1838339 = 2757509) B2757509
theorem B1838355 : Blo 1837620 1838355 := bstep (se 1 (by rfl) ⟨1378766, by rfl⟩ : syracuseStep 1838355 = 2757533) B2757533
theorem B1838371 : Blo 1837620 1838371 := bstep (se 1 (by rfl) ⟨1378778, by rfl⟩ : syracuseStep 1838371 = 2757557) B2757557
theorem B6204707 : Blo 1837620 6204707 := bstep (se 1 (by rfl) ⟨4653530, by rfl⟩ : syracuseStep 6204707 = 9307061) B9307061
theorem B4967729 : Blo 1837620 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B2067763 : Blo 1837620 2067763 := bstep (se 1 (by rfl) ⟨1550822, by rfl⟩ : syracuseStep 2067763 = 3101645) B3101645
theorem B1838387 : Blo 1837620 1838387 := bstep (se 1 (by rfl) ⟨1378790, by rfl⟩ : syracuseStep 1838387 = 2757581) B2757581
theorem B1838403 : Blo 1837620 1838403 := bstep (se 1 (by rfl) ⟨1378802, by rfl⟩ : syracuseStep 1838403 = 2757605) B2757605
theorem B1838419 : Blo 1837620 1838419 := bstep (se 1 (by rfl) ⟨1378814, by rfl⟩ : syracuseStep 1838419 = 2757629) B2757629
theorem B1838435 : Blo 1837620 1838435 := bstep (se 1 (by rfl) ⟨1378826, by rfl⟩ : syracuseStep 1838435 = 2757653) B2757653
theorem B1838451 : Blo 1837620 1838451 := bstep (se 1 (by rfl) ⟨1378838, by rfl⟩ : syracuseStep 1838451 = 2757677) B2757677
theorem B2485633 : Blo 1837620 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B1838467 : Blo 1837620 1838467 := bstep (se 1 (by rfl) ⟨1378850, by rfl⟩ : syracuseStep 1838467 = 2757701) B2757701
theorem B1838483 : Blo 1837620 1838483 := bstep (se 1 (by rfl) ⟨1378862, by rfl⟩ : syracuseStep 1838483 = 2757725) B2757725
theorem B11333027 : Blo 1837620 11333027 := bstep (se 1 (by rfl) ⟨8499770, by rfl⟩ : syracuseStep 11333027 = 16999541) B16999541
theorem B1838499 : Blo 1837620 1838499 := bstep (se 1 (by rfl) ⟨1378874, by rfl⟩ : syracuseStep 1838499 = 2757749) B2757749
theorem B1838515 : Blo 1837620 1838515 := bstep (se 1 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 1838515 = 2757773) B2757773
theorem B2067907 : Blo 1837620 2067907 := bstep (se 1 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 2067907 = 3101861) B3101861
theorem B1838531 : Blo 1837620 1838531 := bstep (se 1 (by rfl) ⟨1378898, by rfl⟩ : syracuseStep 1838531 = 2757797) B2757797
theorem B1838547 : Blo 1837620 1838547 := bstep (se 1 (by rfl) ⟨1378910, by rfl⟩ : syracuseStep 1838547 = 2757821) B2757821
theorem B1838563 : Blo 1837620 1838563 := bstep (se 1 (by rfl) ⟨1378922, by rfl⟩ : syracuseStep 1838563 = 2757845) B2757845
theorem B1838579 : Blo 1837620 1838579 := bstep (se 1 (by rfl) ⟨1378934, by rfl⟩ : syracuseStep 1838579 = 2757869) B2757869
theorem B1838595 : Blo 1837620 1838595 := bstep (se 1 (by rfl) ⟨1378946, by rfl⟩ : syracuseStep 1838595 = 2757893) B2757893
theorem B1838611 : Blo 1837620 1838611 := bstep (se 1 (by rfl) ⟨1378958, by rfl⟩ : syracuseStep 1838611 = 2757917) B2757917
theorem B1838627 : Blo 1837620 1838627 := bstep (se 1 (by rfl) ⟨1378970, by rfl⟩ : syracuseStep 1838627 = 2757941) B2757941
theorem B6204977 : Blo 1837620 6204977 := bstep (se 2 (by rfl) ⟨2326866, by rfl⟩ : syracuseStep 6204977 = 4653733) B4653733
theorem B1838643 : Blo 1837620 1838643 := bstep (se 1 (by rfl) ⟨1378982, by rfl⟩ : syracuseStep 1838643 = 2757965) B2757965
theorem B1838659 : Blo 1837620 1838659 := bstep (se 1 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 1838659 = 2757989) B2757989
theorem B2068051 : Blo 1837620 2068051 := bstep (se 1 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 2068051 = 3102077) B3102077
theorem B1838675 : Blo 1837620 1838675 := bstep (se 1 (by rfl) ⟨1379006, by rfl⟩ : syracuseStep 1838675 = 2758013) B2758013
theorem B1838691 : Blo 1837620 1838691 := bstep (se 1 (by rfl) ⟨1379018, by rfl⟩ : syracuseStep 1838691 = 2758037) B2758037
theorem B3927665 : Blo 1837620 3927665 := bstep (se 2 (by rfl) ⟨1472874, by rfl⟩ : syracuseStep 3927665 = 2945749) B2945749
theorem B1838707 : Blo 1837620 1838707 := bstep (se 1 (by rfl) ⟨1379030, by rfl⟩ : syracuseStep 1838707 = 2758061) B2758061
theorem B1838723 : Blo 1837620 1838723 := bstep (se 1 (by rfl) ⟨1379042, by rfl⟩ : syracuseStep 1838723 = 2758085) B2758085
theorem B1838739 : Blo 1837620 1838739 := bstep (se 1 (by rfl) ⟨1379054, by rfl⟩ : syracuseStep 1838739 = 2758109) B2758109
theorem B1838755 : Blo 1837620 1838755 := bstep (se 1 (by rfl) ⟨1379066, by rfl⟩ : syracuseStep 1838755 = 2758133) B2758133
theorem B1838771 : Blo 1837620 1838771 := bstep (se 1 (by rfl) ⟨1379078, by rfl⟩ : syracuseStep 1838771 = 2758157) B2758157
theorem B1838787 : Blo 1837620 1838787 := bstep (se 1 (by rfl) ⟨1379090, by rfl⟩ : syracuseStep 1838787 = 2758181) B2758181
theorem B15699653 : Blo 1837620 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B7851725 : Blo 1837620 7851725 := bstep (se 3 (by rfl) ⟨1472198, by rfl⟩ : syracuseStep 7851725 = 2944397) B2944397
theorem B1838803 : Blo 1837620 1838803 := bstep (se 1 (by rfl) ⟨1379102, by rfl⟩ : syracuseStep 1838803 = 2758205) B2758205
theorem B2068195 : Blo 1837620 2068195 := bstep (se 1 (by rfl) ⟨1551146, by rfl⟩ : syracuseStep 2068195 = 3102293) B3102293
theorem B1838819 : Blo 1837620 1838819 := bstep (se 1 (by rfl) ⟨1379114, by rfl⟩ : syracuseStep 1838819 = 2758229) B2758229
theorem B1838835 : Blo 1837620 1838835 := bstep (se 1 (by rfl) ⟨1379126, by rfl⟩ : syracuseStep 1838835 = 2758253) B2758253
theorem B1838851 : Blo 1837620 1838851 := bstep (se 1 (by rfl) ⟨1379138, by rfl⟩ : syracuseStep 1838851 = 2758277) B2758277
theorem B2617105 : Blo 1837620 2617105 := bstep (se 2 (by rfl) ⟨981414, by rfl⟩ : syracuseStep 2617105 = 1962829) B1962829
theorem B1838867 : Blo 1837620 1838867 := bstep (se 1 (by rfl) ⟨1379150, by rfl⟩ : syracuseStep 1838867 = 2758301) B2758301
theorem B1838883 : Blo 1837620 1838883 := bstep (se 1 (by rfl) ⟨1379162, by rfl⟩ : syracuseStep 1838883 = 2758325) B2758325
theorem B1838899 : Blo 1837620 1838899 := bstep (se 1 (by rfl) ⟨1379174, by rfl⟩ : syracuseStep 1838899 = 2758349) B2758349
theorem B1863491 : Blo 1837620 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B1838915 : Blo 1837620 1838915 := bstep (se 1 (by rfl) ⟨1379186, by rfl⟩ : syracuseStep 1838915 = 2758373) B2758373
theorem B2756435 : Blo 1837620 2756435 := bstep (se 1 (by rfl) ⟨2067326, by rfl⟩ : syracuseStep 2756435 = 4134653) B4134653
theorem B1838931 : Blo 1837620 1838931 := bstep (se 1 (by rfl) ⟨1379198, by rfl⟩ : syracuseStep 1838931 = 2758397) B2758397
theorem B3313507 : Blo 1837620 3313507 := bstep (se 1 (by rfl) ⟨2485130, by rfl⟩ : syracuseStep 3313507 = 4970261) B4970261
theorem B1838947 : Blo 1837620 1838947 := bstep (se 1 (by rfl) ⟨1379210, by rfl⟩ : syracuseStep 1838947 = 2758421) B2758421
theorem B2756465 : Blo 1837620 2756465 := bstep (se 2 (by rfl) ⟨1033674, by rfl⟩ : syracuseStep 2756465 = 2067349) B2067349
theorem B2617201 : Blo 1837620 2617201 := bstep (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) B1962901
theorem B2068339 : Blo 1837620 2068339 := bstep (se 1 (by rfl) ⟨1551254, by rfl⟩ : syracuseStep 2068339 = 3102509) B3102509
theorem B1838963 : Blo 1837620 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B2756483 : Blo 1837620 2756483 := bstep (se 1 (by rfl) ⟨2067362, by rfl⟩ : syracuseStep 2756483 = 4134725) B4134725
theorem B1838979 : Blo 1837620 1838979 := bstep (se 1 (by rfl) ⟨1379234, by rfl⟩ : syracuseStep 1838979 = 2758469) B2758469
theorem B1838995 : Blo 1837620 1838995 := bstep (se 1 (by rfl) ⟨1379246, by rfl⟩ : syracuseStep 1838995 = 2758493) B2758493
theorem B2756513 : Blo 1837620 2756513 := bstep (se 2 (by rfl) ⟨1033692, by rfl⟩ : syracuseStep 2756513 = 2067385) B2067385
theorem B1839011 : Blo 1837620 1839011 := bstep (se 1 (by rfl) ⟨1379258, by rfl⟩ : syracuseStep 1839011 = 2758517) B2758517
theorem B7958449 : Blo 1837620 7958449 := bstep (se 2 (by rfl) ⟨2984418, by rfl⟩ : syracuseStep 7958449 = 5968837) B5968837
theorem B2756531 : Blo 1837620 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B1839027 : Blo 1837620 1839027 := bstep (se 1 (by rfl) ⟨1379270, by rfl⟩ : syracuseStep 1839027 = 2758541) B2758541
theorem B2207683 : Blo 1837620 2207683 := bstep (se 1 (by rfl) ⟨1655762, by rfl⟩ : syracuseStep 2207683 = 3311525) B3311525
theorem B1839043 : Blo 1837620 1839043 := bstep (se 1 (by rfl) ⟨1379282, by rfl⟩ : syracuseStep 1839043 = 2758565) B2758565
theorem B2756561 : Blo 1837620 2756561 := bstep (se 2 (by rfl) ⟨1033710, by rfl⟩ : syracuseStep 2756561 = 2067421) B2067421
theorem B1839059 : Blo 1837620 1839059 := bstep (se 1 (by rfl) ⟨1379294, by rfl⟩ : syracuseStep 1839059 = 2758589) B2758589
theorem B2944993 : Blo 1837620 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B2756579 : Blo 1837620 2756579 := bstep (se 1 (by rfl) ⟨2067434, by rfl⟩ : syracuseStep 2756579 = 4134869) B4134869
theorem B1839075 : Blo 1837620 1839075 := bstep (se 1 (by rfl) ⟨1379306, by rfl⟩ : syracuseStep 1839075 = 2758613) B2758613
theorem B11186147 : Blo 1837620 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B1839091 : Blo 1837620 1839091 := bstep (se 1 (by rfl) ⟨1379318, by rfl⟩ : syracuseStep 1839091 = 2758637) B2758637
theorem B2756609 : Blo 1837620 2756609 := bstep (se 2 (by rfl) ⟨1033728, by rfl⟩ : syracuseStep 2756609 = 2067457) B2067457
theorem B2068483 : Blo 1837620 2068483 := bstep (se 1 (by rfl) ⟨1551362, by rfl⟩ : syracuseStep 2068483 = 3102725) B3102725
theorem B1839107 : Blo 1837620 1839107 := bstep (se 1 (by rfl) ⟨1379330, by rfl⟩ : syracuseStep 1839107 = 2758661) B2758661
theorem B2756627 : Blo 1837620 2756627 := bstep (se 1 (by rfl) ⟨2067470, by rfl⟩ : syracuseStep 2756627 = 4134941) B4134941
theorem B1839123 : Blo 1837620 1839123 := bstep (se 1 (by rfl) ⟨1379342, by rfl⟩ : syracuseStep 1839123 = 2758685) B2758685
theorem B1839139 : Blo 1837620 1839139 := bstep (se 1 (by rfl) ⟨1379354, by rfl⟩ : syracuseStep 1839139 = 2758709) B2758709
theorem B2756657 : Blo 1837620 2756657 := bstep (se 2 (by rfl) ⟨1033746, by rfl⟩ : syracuseStep 2756657 = 2067493) B2067493
theorem B4968497 : Blo 1837620 4968497 := bstep (se 2 (by rfl) ⟨1863186, by rfl⟩ : syracuseStep 4968497 = 3726373) B3726373
theorem B1839155 : Blo 1837620 1839155 := bstep (se 1 (by rfl) ⟨1379366, by rfl⟩ : syracuseStep 1839155 = 2758733) B2758733
theorem B6983729 : Blo 1837620 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B2756675 : Blo 1837620 2756675 := bstep (se 1 (by rfl) ⟨2067506, by rfl⟩ : syracuseStep 2756675 = 4135013) B4135013
theorem B1839171 : Blo 1837620 1839171 := bstep (se 1 (by rfl) ⟨1379378, by rfl⟩ : syracuseStep 1839171 = 2758757) B2758757
theorem B6205517 : Blo 1837620 6205517 := bstep (se 3 (by rfl) ⟨1163534, by rfl⟩ : syracuseStep 6205517 = 2327069) B2327069
theorem B1839187 : Blo 1837620 1839187 := bstep (se 1 (by rfl) ⟨1379390, by rfl⟩ : syracuseStep 1839187 = 2758781) B2758781
theorem B2756705 : Blo 1837620 2756705 := bstep (se 2 (by rfl) ⟨1033764, by rfl⟩ : syracuseStep 2756705 = 2067529) B2067529
theorem B1839203 : Blo 1837620 1839203 := bstep (se 1 (by rfl) ⟨1379402, by rfl⟩ : syracuseStep 1839203 = 2758805) B2758805
theorem B2756723 : Blo 1837620 2756723 := bstep (se 1 (by rfl) ⟨2067542, by rfl⟩ : syracuseStep 2756723 = 4135085) B4135085
theorem B1839219 : Blo 1837620 1839219 := bstep (se 1 (by rfl) ⟨1379414, by rfl⟩ : syracuseStep 1839219 = 2758829) B2758829
theorem B6205571 : Blo 1837620 6205571 := bstep (se 1 (by rfl) ⟨4654178, by rfl⟩ : syracuseStep 6205571 = 9308357) B9308357
theorem B1839235 : Blo 1837620 1839235 := bstep (se 1 (by rfl) ⟨1379426, by rfl⟩ : syracuseStep 1839235 = 2758853) B2758853
theorem B2756753 : Blo 1837620 2756753 := bstep (se 2 (by rfl) ⟨1033782, by rfl⟩ : syracuseStep 2756753 = 2067565) B2067565
theorem B2068627 : Blo 1837620 2068627 := bstep (se 1 (by rfl) ⟨1551470, by rfl⟩ : syracuseStep 2068627 = 3102941) B3102941
theorem B1839251 : Blo 1837620 1839251 := bstep (se 1 (by rfl) ⟨1379438, by rfl⟩ : syracuseStep 1839251 = 2758877) B2758877
theorem B2756771 : Blo 1837620 2756771 := bstep (se 1 (by rfl) ⟨2067578, by rfl⟩ : syracuseStep 2756771 = 4135157) B4135157
theorem B1839267 : Blo 1837620 1839267 := bstep (se 1 (by rfl) ⟨1379450, by rfl⟩ : syracuseStep 1839267 = 2758901) B2758901
theorem B1839283 : Blo 1837620 1839283 := bstep (se 1 (by rfl) ⟨1379462, by rfl⟩ : syracuseStep 1839283 = 2758925) B2758925
theorem B25170101 : Blo 1837620 25170101 := bstep (se 5 (by rfl) ⟨1179848, by rfl⟩ : syracuseStep 25170101 = 2359697) B2359697
theorem B2756801 : Blo 1837620 2756801 := bstep (se 2 (by rfl) ⟨1033800, by rfl⟩ : syracuseStep 2756801 = 2067601) B2067601
theorem B1839299 : Blo 1837620 1839299 := bstep (se 1 (by rfl) ⟨1379474, by rfl⟩ : syracuseStep 1839299 = 2758949) B2758949
theorem B2756819 : Blo 1837620 2756819 := bstep (se 1 (by rfl) ⟨2067614, by rfl⟩ : syracuseStep 2756819 = 4135229) B4135229
theorem B1839315 : Blo 1837620 1839315 := bstep (se 1 (by rfl) ⟨1379486, by rfl⟩ : syracuseStep 1839315 = 2758973) B2758973
theorem B2945249 : Blo 1837620 2945249 := bstep (se 2 (by rfl) ⟨1104468, by rfl⟩ : syracuseStep 2945249 = 2208937) B2208937
theorem B1839331 : Blo 1837620 1839331 := bstep (se 1 (by rfl) ⟨1379498, by rfl⟩ : syracuseStep 1839331 = 2758997) B2758997
theorem B2756849 : Blo 1837620 2756849 := bstep (se 2 (by rfl) ⟨1033818, by rfl⟩ : syracuseStep 2756849 = 2067637) B2067637
theorem B15708401 : Blo 1837620 15708401 := bstep (se 2 (by rfl) ⟨5890650, by rfl⟩ : syracuseStep 15708401 = 11781301) B11781301
theorem B1839347 : Blo 1837620 1839347 := bstep (se 1 (by rfl) ⟨1379510, by rfl⟩ : syracuseStep 1839347 = 2759021) B2759021
theorem B2756867 : Blo 1837620 2756867 := bstep (se 1 (by rfl) ⟨2067650, by rfl⟩ : syracuseStep 2756867 = 4135301) B4135301
theorem B1839363 : Blo 1837620 1839363 := bstep (se 1 (by rfl) ⟨1379522, by rfl⟩ : syracuseStep 1839363 = 2759045) B2759045
theorem B1839379 : Blo 1837620 1839379 := bstep (se 1 (by rfl) ⟨1379534, by rfl⟩ : syracuseStep 1839379 = 2759069) B2759069
theorem B2756897 : Blo 1837620 2756897 := bstep (se 2 (by rfl) ⟨1033836, by rfl⟩ : syracuseStep 2756897 = 2067673) B2067673
theorem B2068771 : Blo 1837620 2068771 := bstep (se 1 (by rfl) ⟨1551578, by rfl⟩ : syracuseStep 2068771 = 3103157) B3103157
theorem B1839395 : Blo 1837620 1839395 := bstep (se 1 (by rfl) ⟨1379546, by rfl⟩ : syracuseStep 1839395 = 2759093) B2759093
theorem B2756915 : Blo 1837620 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1839411 : Blo 1837620 1839411 := bstep (se 1 (by rfl) ⟨1379558, by rfl⟩ : syracuseStep 1839411 = 2759117) B2759117
theorem B1839427 : Blo 1837620 1839427 := bstep (se 1 (by rfl) ⟨1379570, by rfl⟩ : syracuseStep 1839427 = 2759141) B2759141
theorem B2756945 : Blo 1837620 2756945 := bstep (se 2 (by rfl) ⟨1033854, by rfl⟩ : syracuseStep 2756945 = 2067709) B2067709
theorem B1839443 : Blo 1837620 1839443 := bstep (se 1 (by rfl) ⟨1379582, by rfl⟩ : syracuseStep 1839443 = 2759165) B2759165
theorem B2617697 : Blo 1837620 2617697 := bstep (se 2 (by rfl) ⟨981636, by rfl⟩ : syracuseStep 2617697 = 1963273) B1963273
theorem B2756963 : Blo 1837620 2756963 := bstep (se 1 (by rfl) ⟨2067722, by rfl⟩ : syracuseStep 2756963 = 4135445) B4135445
theorem B1839459 : Blo 1837620 1839459 := bstep (se 1 (by rfl) ⟨1379594, by rfl⟩ : syracuseStep 1839459 = 2759189) B2759189
theorem B15700337 : Blo 1837620 15700337 := bstep (se 2 (by rfl) ⟨5887626, by rfl⟩ : syracuseStep 15700337 = 11775253) B11775253
theorem B1839475 : Blo 1837620 1839475 := bstep (se 1 (by rfl) ⟨1379606, by rfl⟩ : syracuseStep 1839475 = 2759213) B2759213
theorem B2756993 : Blo 1837620 2756993 := bstep (se 2 (by rfl) ⟨1033872, by rfl⟩ : syracuseStep 2756993 = 2067745) B2067745
theorem B1839491 : Blo 1837620 1839491 := bstep (se 1 (by rfl) ⟨1379618, by rfl⟩ : syracuseStep 1839491 = 2759237) B2759237
theorem B6205841 : Blo 1837620 6205841 := bstep (se 2 (by rfl) ⟨2327190, by rfl⟩ : syracuseStep 6205841 = 4654381) B4654381
theorem B2757011 : Blo 1837620 2757011 := bstep (se 1 (by rfl) ⟨2067758, by rfl⟩ : syracuseStep 2757011 = 4135517) B4135517
theorem B1839507 : Blo 1837620 1839507 := bstep (se 1 (by rfl) ⟨1379630, by rfl⟩ : syracuseStep 1839507 = 2759261) B2759261
theorem B2945441 : Blo 1837620 2945441 := bstep (se 2 (by rfl) ⟨1104540, by rfl⟩ : syracuseStep 2945441 = 2209081) B2209081
theorem B1839523 : Blo 1837620 1839523 := bstep (se 1 (by rfl) ⟨1379642, by rfl⟩ : syracuseStep 1839523 = 2759285) B2759285
theorem B3101105 : Blo 1837620 3101105 := bstep (se 2 (by rfl) ⟨1162914, by rfl⟩ : syracuseStep 3101105 = 2325829) B2325829
theorem B2757041 : Blo 1837620 2757041 := bstep (se 2 (by rfl) ⟨1033890, by rfl⟩ : syracuseStep 2757041 = 2067781) B2067781
theorem B2068915 : Blo 1837620 2068915 := bstep (se 1 (by rfl) ⟨1551686, by rfl⟩ : syracuseStep 2068915 = 3103373) B3103373
theorem B1839539 : Blo 1837620 1839539 := bstep (se 1 (by rfl) ⟨1379654, by rfl⟩ : syracuseStep 1839539 = 2759309) B2759309
theorem B2757059 : Blo 1837620 2757059 := bstep (se 1 (by rfl) ⟨2067794, by rfl⟩ : syracuseStep 2757059 = 4135589) B4135589
theorem B1839555 : Blo 1837620 1839555 := bstep (se 1 (by rfl) ⟨1379666, by rfl⟩ : syracuseStep 1839555 = 2759333) B2759333
theorem B1839571 : Blo 1837620 1839571 := bstep (se 1 (by rfl) ⟨1379678, by rfl⟩ : syracuseStep 1839571 = 2759357) B2759357
theorem B2757089 : Blo 1837620 2757089 := bstep (se 2 (by rfl) ⟨1033908, by rfl⟩ : syracuseStep 2757089 = 2067817) B2067817
theorem B1839587 : Blo 1837620 1839587 := bstep (se 1 (by rfl) ⟨1379690, by rfl⟩ : syracuseStep 1839587 = 2759381) B2759381
theorem B2757107 : Blo 1837620 2757107 := bstep (se 1 (by rfl) ⟨2067830, by rfl⟩ : syracuseStep 2757107 = 4135661) B4135661
theorem B1839603 : Blo 1837620 1839603 := bstep (se 1 (by rfl) ⟨1379702, by rfl⟩ : syracuseStep 1839603 = 2759405) B2759405
theorem B1839619 : Blo 1837620 1839619 := bstep (se 1 (by rfl) ⟨1379714, by rfl⟩ : syracuseStep 1839619 = 2759429) B2759429
theorem B2757137 : Blo 1837620 2757137 := bstep (se 2 (by rfl) ⟨1033926, by rfl⟩ : syracuseStep 2757137 = 2067853) B2067853
theorem B2757155 : Blo 1837620 2757155 := bstep (se 1 (by rfl) ⟨2067866, by rfl⟩ : syracuseStep 2757155 = 4135733) B4135733
theorem B3101233 : Blo 1837620 3101233 := bstep (se 2 (by rfl) ⟨1162962, by rfl⟩ : syracuseStep 3101233 = 2325925) B2325925
theorem B2757185 : Blo 1837620 2757185 := bstep (se 2 (by rfl) ⟨1033944, by rfl⟩ : syracuseStep 2757185 = 2067889) B2067889
theorem B6287939 : Blo 1837620 6287939 := bstep (se 1 (by rfl) ⟨4715954, by rfl⟩ : syracuseStep 6287939 = 9431909) B9431909
theorem B2069059 : Blo 1837620 2069059 := bstep (se 1 (by rfl) ⟨1551794, by rfl⟩ : syracuseStep 2069059 = 3103589) B3103589
theorem B3101267 : Blo 1837620 3101267 := bstep (se 1 (by rfl) ⟨2325950, by rfl⟩ : syracuseStep 3101267 = 4651901) B4651901
theorem B2757203 : Blo 1837620 2757203 := bstep (se 1 (by rfl) ⟨2067902, by rfl⟩ : syracuseStep 2757203 = 4135805) B4135805
theorem B4969069 : Blo 1837620 4969069 := bstep (se 3 (by rfl) ⟨931700, by rfl⟩ : syracuseStep 4969069 = 1863401) B1863401
theorem B2757233 : Blo 1837620 2757233 := bstep (se 2 (by rfl) ⟨1033962, by rfl⟩ : syracuseStep 2757233 = 2067925) B2067925
theorem B2757251 : Blo 1837620 2757251 := bstep (se 1 (by rfl) ⟨2067938, by rfl⟩ : syracuseStep 2757251 = 4135877) B4135877
theorem B5304977 : Blo 1837620 5304977 := bstep (se 2 (by rfl) ⟨1989366, by rfl⟩ : syracuseStep 5304977 = 3978733) B3978733
theorem B2757281 : Blo 1837620 2757281 := bstep (se 2 (by rfl) ⟨1033980, by rfl⟩ : syracuseStep 2757281 = 2067961) B2067961
theorem B2757299 : Blo 1837620 2757299 := bstep (se 1 (by rfl) ⟨2067974, by rfl⟩ : syracuseStep 2757299 = 4135949) B4135949
theorem B10474181 : Blo 1837620 10474181 := bstep (se 4 (by rfl) ⟨981954, by rfl⟩ : syracuseStep 10474181 = 1963909) B1963909
theorem B2757329 : Blo 1837620 2757329 := bstep (se 2 (by rfl) ⟨1033998, by rfl⟩ : syracuseStep 2757329 = 2067997) B2067997
theorem B3101395 : Blo 1837620 3101395 := bstep (se 1 (by rfl) ⟨2326046, by rfl⟩ : syracuseStep 3101395 = 4652093) B4652093
theorem B2069203 : Blo 1837620 2069203 := bstep (se 1 (by rfl) ⟨1551902, by rfl⟩ : syracuseStep 2069203 = 3103805) B3103805
theorem B2757347 : Blo 1837620 2757347 := bstep (se 1 (by rfl) ⟨2068010, by rfl⟩ : syracuseStep 2757347 = 4136021) B4136021
theorem B1962739 : Blo 1837620 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B2757377 : Blo 1837620 2757377 := bstep (se 2 (by rfl) ⟨1034016, by rfl⟩ : syracuseStep 2757377 = 2068033) B2068033
theorem B6624013 : Blo 1837620 6624013 := bstep (se 3 (by rfl) ⟨1242002, by rfl⟩ : syracuseStep 6624013 = 2484005) B2484005
theorem B2757395 : Blo 1837620 2757395 := bstep (se 1 (by rfl) ⟨2068046, by rfl⟩ : syracuseStep 2757395 = 4136093) B4136093
theorem B2757425 : Blo 1837620 2757425 := bstep (se 2 (by rfl) ⟨1034034, by rfl⟩ : syracuseStep 2757425 = 2068069) B2068069
theorem B2757443 : Blo 1837620 2757443 := bstep (se 1 (by rfl) ⟨2068082, by rfl⟩ : syracuseStep 2757443 = 4136165) B4136165
theorem B10466117 : Blo 1837620 10466117 := bstep (se 4 (by rfl) ⟨981198, by rfl⟩ : syracuseStep 10466117 = 1962397) B1962397
theorem B3101537 : Blo 1837620 3101537 := bstep (se 2 (by rfl) ⟨1163076, by rfl⟩ : syracuseStep 3101537 = 2326153) B2326153
theorem B2757473 : Blo 1837620 2757473 := bstep (se 2 (by rfl) ⟨1034052, by rfl⟩ : syracuseStep 2757473 = 2068105) B2068105
theorem B2069347 : Blo 1837620 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B2757491 : Blo 1837620 2757491 := bstep (se 1 (by rfl) ⟨2068118, by rfl⟩ : syracuseStep 2757491 = 4136237) B4136237
theorem B3404675 : Blo 1837620 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B2757521 : Blo 1837620 2757521 := bstep (se 2 (by rfl) ⟨1034070, by rfl⟩ : syracuseStep 2757521 = 2068141) B2068141
theorem B2757539 : Blo 1837620 2757539 := bstep (se 1 (by rfl) ⟨2068154, by rfl⟩ : syracuseStep 2757539 = 4136309) B4136309
theorem B6206381 : Blo 1837620 6206381 := bstep (se 3 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 6206381 = 2327393) B2327393
theorem B2757569 : Blo 1837620 2757569 := bstep (se 2 (by rfl) ⟨1034088, by rfl⟩ : syracuseStep 2757569 = 2068177) B2068177
theorem B2757587 : Blo 1837620 2757587 := bstep (se 1 (by rfl) ⟨2068190, by rfl⟩ : syracuseStep 2757587 = 4136381) B4136381
theorem B3101665 : Blo 1837620 3101665 := bstep (se 2 (by rfl) ⟨1163124, by rfl⟩ : syracuseStep 3101665 = 2326249) B2326249
theorem B9303011 : Blo 1837620 9303011 := bstep (se 1 (by rfl) ⟨6977258, by rfl⟩ : syracuseStep 9303011 = 13954517) B13954517
theorem B6206435 : Blo 1837620 6206435 := bstep (se 1 (by rfl) ⟨4654826, by rfl⟩ : syracuseStep 6206435 = 9309653) B9309653
theorem B2757617 : Blo 1837620 2757617 := bstep (se 2 (by rfl) ⟨1034106, by rfl⟩ : syracuseStep 2757617 = 2068213) B2068213
theorem B2069491 : Blo 1837620 2069491 := bstep (se 1 (by rfl) ⟨1552118, by rfl⟩ : syracuseStep 2069491 = 3104237) B3104237
theorem B3101699 : Blo 1837620 3101699 := bstep (se 1 (by rfl) ⟨2326274, by rfl⟩ : syracuseStep 3101699 = 4652549) B4652549
theorem B2757635 : Blo 1837620 2757635 := bstep (se 1 (by rfl) ⟨2068226, by rfl⟩ : syracuseStep 2757635 = 4136453) B4136453
theorem B2757665 : Blo 1837620 2757665 := bstep (se 2 (by rfl) ⟨1034124, by rfl⟩ : syracuseStep 2757665 = 2068249) B2068249
theorem B2757683 : Blo 1837620 2757683 := bstep (se 1 (by rfl) ⟨2068262, by rfl⟩ : syracuseStep 2757683 = 4136525) B4136525
theorem B2757713 : Blo 1837620 2757713 := bstep (se 2 (by rfl) ⟨1034142, by rfl⟩ : syracuseStep 2757713 = 2068285) B2068285
theorem B2757731 : Blo 1837620 2757731 := bstep (se 1 (by rfl) ⟨2068298, by rfl⟩ : syracuseStep 2757731 = 4136597) B4136597
theorem B2757761 : Blo 1837620 2757761 := bstep (se 2 (by rfl) ⟨1034160, by rfl⟩ : syracuseStep 2757761 = 2068321) B2068321
theorem B3101827 : Blo 1837620 3101827 := bstep (se 1 (by rfl) ⟨2326370, by rfl⟩ : syracuseStep 3101827 = 4652741) B4652741
theorem B23549069 : Blo 1837620 23549069 := bstep (se 3 (by rfl) ⟨4415450, by rfl⟩ : syracuseStep 23549069 = 8830901) B8830901
theorem B2757779 : Blo 1837620 2757779 := bstep (se 1 (by rfl) ⟨2068334, by rfl⟩ : syracuseStep 2757779 = 4136669) B4136669
theorem B11777201 : Blo 1837620 11777201 := bstep (se 2 (by rfl) ⟨4416450, by rfl⟩ : syracuseStep 11777201 = 8832901) B8832901
theorem B2757809 : Blo 1837620 2757809 := bstep (se 2 (by rfl) ⟨1034178, by rfl⟩ : syracuseStep 2757809 = 2068357) B2068357
theorem B2757827 : Blo 1837620 2757827 := bstep (se 1 (by rfl) ⟨2068370, by rfl⟩ : syracuseStep 2757827 = 4136741) B4136741
theorem B2618563 : Blo 1837620 2618563 := bstep (se 1 (by rfl) ⟨1963922, by rfl⟩ : syracuseStep 2618563 = 3927845) B3927845
theorem B2757857 : Blo 1837620 2757857 := bstep (se 2 (by rfl) ⟨1034196, by rfl⟩ : syracuseStep 2757857 = 2068393) B2068393
theorem B5887217 : Blo 1837620 5887217 := bstep (se 2 (by rfl) ⟨2207706, by rfl⟩ : syracuseStep 5887217 = 4415413) B4415413
theorem B2757875 : Blo 1837620 2757875 := bstep (se 1 (by rfl) ⟨2068406, by rfl⟩ : syracuseStep 2757875 = 4136813) B4136813
theorem B6206705 : Blo 1837620 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B3101969 : Blo 1837620 3101969 := bstep (se 2 (by rfl) ⟨1163238, by rfl⟩ : syracuseStep 3101969 = 2326477) B2326477
theorem B2757905 : Blo 1837620 2757905 := bstep (se 2 (by rfl) ⟨1034214, by rfl⟩ : syracuseStep 2757905 = 2068429) B2068429
theorem B2757923 : Blo 1837620 2757923 := bstep (se 1 (by rfl) ⟨2068442, by rfl⟩ : syracuseStep 2757923 = 4136885) B4136885
theorem B2618659 : Blo 1837620 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B2757953 : Blo 1837620 2757953 := bstep (se 2 (by rfl) ⟨1034232, by rfl⟩ : syracuseStep 2757953 = 2068465) B2068465
theorem B24196421 : Blo 1837620 24196421 := bstep (se 4 (by rfl) ⟨2268414, by rfl⟩ : syracuseStep 24196421 = 4536829) B4536829
theorem B5666129 : Blo 1837620 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B2757971 : Blo 1837620 2757971 := bstep (se 1 (by rfl) ⟨2068478, by rfl⟩ : syracuseStep 2757971 = 4136957) B4136957
theorem B2758001 : Blo 1837620 2758001 := bstep (se 2 (by rfl) ⟨1034250, by rfl⟩ : syracuseStep 2758001 = 2068501) B2068501
theorem B10474865 : Blo 1837620 10474865 := bstep (se 2 (by rfl) ⟨3928074, by rfl⟩ : syracuseStep 10474865 = 7856149) B7856149
theorem B2758019 : Blo 1837620 2758019 := bstep (se 1 (by rfl) ⟨2068514, by rfl⟩ : syracuseStep 2758019 = 4137029) B4137029
theorem B3102097 : Blo 1837620 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B2758049 : Blo 1837620 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B3102131 : Blo 1837620 3102131 := bstep (se 1 (by rfl) ⟨2326598, by rfl⟩ : syracuseStep 3102131 = 4653197) B4653197
theorem B2758067 : Blo 1837620 2758067 := bstep (se 1 (by rfl) ⟨2068550, by rfl⟩ : syracuseStep 2758067 = 4137101) B4137101
theorem B2758097 : Blo 1837620 2758097 := bstep (se 2 (by rfl) ⟨1034286, by rfl⟩ : syracuseStep 2758097 = 2068573) B2068573
theorem B2758115 : Blo 1837620 2758115 := bstep (se 1 (by rfl) ⟨2068586, by rfl⟩ : syracuseStep 2758115 = 4137173) B4137173
theorem B2758145 : Blo 1837620 2758145 := bstep (se 2 (by rfl) ⟨1034304, by rfl⟩ : syracuseStep 2758145 = 2068609) B2068609
theorem B2758163 : Blo 1837620 2758163 := bstep (se 1 (by rfl) ⟨2068622, by rfl⟩ : syracuseStep 2758163 = 4137245) B4137245
theorem B2758193 : Blo 1837620 2758193 := bstep (se 2 (by rfl) ⟨1034322, by rfl⟩ : syracuseStep 2758193 = 2068645) B2068645
theorem B3102259 : Blo 1837620 3102259 := bstep (se 1 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 3102259 = 4653389) B4653389
theorem B2758211 : Blo 1837620 2758211 := bstep (se 1 (by rfl) ⟨2068658, by rfl⟩ : syracuseStep 2758211 = 4137317) B4137317
theorem B2758241 : Blo 1837620 2758241 := bstep (se 2 (by rfl) ⟨1034340, by rfl⟩ : syracuseStep 2758241 = 2068681) B2068681
theorem B2758259 : Blo 1837620 2758259 := bstep (se 1 (by rfl) ⟨2068694, by rfl⟩ : syracuseStep 2758259 = 4137389) B4137389
theorem B2758289 : Blo 1837620 2758289 := bstep (se 2 (by rfl) ⟨1034358, by rfl⟩ : syracuseStep 2758289 = 2068717) B2068717
theorem B2758307 : Blo 1837620 2758307 := bstep (se 1 (by rfl) ⟨2068730, by rfl⟩ : syracuseStep 2758307 = 4137461) B4137461
theorem B9311921 : Blo 1837620 9311921 := bstep (se 2 (by rfl) ⟨3491970, by rfl⟩ : syracuseStep 9311921 = 6983941) B6983941
theorem B3102401 : Blo 1837620 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B2758337 : Blo 1837620 2758337 := bstep (se 2 (by rfl) ⟨1034376, by rfl⟩ : syracuseStep 2758337 = 2068753) B2068753
theorem B2209475 : Blo 1837620 2209475 := bstep (se 1 (by rfl) ⟨1657106, by rfl⟩ : syracuseStep 2209475 = 3314213) B3314213
theorem B2758355 : Blo 1837620 2758355 := bstep (se 1 (by rfl) ⟨2068766, by rfl⟩ : syracuseStep 2758355 = 4137533) B4137533
theorem B2758385 : Blo 1837620 2758385 := bstep (se 2 (by rfl) ⟨1034394, by rfl⟩ : syracuseStep 2758385 = 2068789) B2068789
theorem B2758403 : Blo 1837620 2758403 := bstep (se 1 (by rfl) ⟨2068802, by rfl⟩ : syracuseStep 2758403 = 4137605) B4137605
theorem B9303821 : Blo 1837620 9303821 := bstep (se 3 (by rfl) ⟨1744466, by rfl⟩ : syracuseStep 9303821 = 3488933) B3488933
theorem B6207245 : Blo 1837620 6207245 := bstep (se 3 (by rfl) ⟨1163858, by rfl⟩ : syracuseStep 6207245 = 2327717) B2327717
theorem B2619155 : Blo 1837620 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2758433 : Blo 1837620 2758433 := bstep (se 2 (by rfl) ⟨1034412, by rfl⟩ : syracuseStep 2758433 = 2068825) B2068825
theorem B2758451 : Blo 1837620 2758451 := bstep (se 1 (by rfl) ⟨2068838, by rfl⟩ : syracuseStep 2758451 = 4137677) B4137677
theorem B3102529 : Blo 1837620 3102529 := bstep (se 2 (by rfl) ⟨1163448, by rfl⟩ : syracuseStep 3102529 = 2326897) B2326897
theorem B6207299 : Blo 1837620 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B2758481 : Blo 1837620 2758481 := bstep (se 2 (by rfl) ⟨1034430, by rfl⟩ : syracuseStep 2758481 = 2068861) B2068861
theorem B3102563 : Blo 1837620 3102563 := bstep (se 1 (by rfl) ⟨2326922, by rfl⟩ : syracuseStep 3102563 = 4653845) B4653845
theorem B2758499 : Blo 1837620 2758499 := bstep (se 1 (by rfl) ⟨2068874, by rfl⟩ : syracuseStep 2758499 = 4137749) B4137749
theorem B17667953 : Blo 1837620 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B2758529 : Blo 1837620 2758529 := bstep (se 2 (by rfl) ⟨1034448, by rfl⟩ : syracuseStep 2758529 = 2068897) B2068897
theorem B2758547 : Blo 1837620 2758547 := bstep (se 1 (by rfl) ⟨2068910, by rfl⟩ : syracuseStep 2758547 = 4137821) B4137821
theorem B4134833 : Blo 1837620 4134833 := bstep (se 2 (by rfl) ⟨1550562, by rfl⟩ : syracuseStep 4134833 = 3101125) B3101125
theorem B2758577 : Blo 1837620 2758577 := bstep (se 2 (by rfl) ⟨1034466, by rfl⟩ : syracuseStep 2758577 = 2068933) B2068933
theorem B11188145 : Blo 1837620 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B4134851 : Blo 1837620 4134851 := bstep (se 1 (by rfl) ⟨3101138, by rfl⟩ : syracuseStep 4134851 = 6202277) B6202277
theorem B2758595 : Blo 1837620 2758595 := bstep (se 1 (by rfl) ⟨2068946, by rfl⟩ : syracuseStep 2758595 = 4137893) B4137893
theorem B2758625 : Blo 1837620 2758625 := bstep (se 2 (by rfl) ⟨1034484, by rfl⟩ : syracuseStep 2758625 = 2068969) B2068969
theorem B3102691 : Blo 1837620 3102691 := bstep (se 1 (by rfl) ⟨2327018, by rfl⟩ : syracuseStep 3102691 = 4654037) B4654037
theorem B2758643 : Blo 1837620 2758643 := bstep (se 1 (by rfl) ⟨2068982, by rfl⟩ : syracuseStep 2758643 = 4137965) B4137965
theorem B2758673 : Blo 1837620 2758673 := bstep (se 2 (by rfl) ⟨1034502, by rfl⟩ : syracuseStep 2758673 = 2069005) B2069005
theorem B2758691 : Blo 1837620 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B2758721 : Blo 1837620 2758721 := bstep (se 2 (by rfl) ⟨1034520, by rfl⟩ : syracuseStep 2758721 = 2069041) B2069041
theorem B4970573 : Blo 1837620 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B2758739 : Blo 1837620 2758739 := bstep (se 1 (by rfl) ⟨2069054, by rfl⟩ : syracuseStep 2758739 = 4138109) B4138109
theorem B6207569 : Blo 1837620 6207569 := bstep (se 2 (by rfl) ⟨2327838, by rfl⟩ : syracuseStep 6207569 = 4655677) B4655677
theorem B1964131 : Blo 1837620 1964131 := bstep (se 1 (by rfl) ⟨1473098, by rfl⟩ : syracuseStep 1964131 = 2946197) B2946197
theorem B3102833 : Blo 1837620 3102833 := bstep (se 2 (by rfl) ⟨1163562, by rfl⟩ : syracuseStep 3102833 = 2327125) B2327125
theorem B2758769 : Blo 1837620 2758769 := bstep (se 2 (by rfl) ⟨1034538, by rfl⟩ : syracuseStep 2758769 = 2069077) B2069077
theorem B2758787 : Blo 1837620 2758787 := bstep (se 1 (by rfl) ⟨2069090, by rfl⟩ : syracuseStep 2758787 = 4138181) B4138181
theorem B2758817 : Blo 1837620 2758817 := bstep (se 2 (by rfl) ⟨1034556, by rfl⟩ : syracuseStep 2758817 = 2069113) B2069113
theorem B2209955 : Blo 1837620 2209955 := bstep (se 1 (by rfl) ⟨1657466, by rfl⟩ : syracuseStep 2209955 = 3314933) B3314933
theorem B2758835 : Blo 1837620 2758835 := bstep (se 1 (by rfl) ⟨2069126, by rfl⟩ : syracuseStep 2758835 = 4138253) B4138253
theorem B2652355 : Blo 1837620 2652355 := bstep (se 1 (by rfl) ⟨1989266, by rfl⟩ : syracuseStep 2652355 = 3978533) B3978533
theorem B4135121 : Blo 1837620 4135121 := bstep (se 2 (by rfl) ⟨1550670, by rfl⟩ : syracuseStep 4135121 = 3101341) B3101341
theorem B2758865 : Blo 1837620 2758865 := bstep (se 2 (by rfl) ⟨1034574, by rfl⟩ : syracuseStep 2758865 = 2069149) B2069149
theorem B4036817 : Blo 1837620 4036817 := bstep (se 2 (by rfl) ⟨1513806, by rfl⟩ : syracuseStep 4036817 = 3027613) B3027613
theorem B4135139 : Blo 1837620 4135139 := bstep (se 1 (by rfl) ⟨3101354, by rfl⟩ : syracuseStep 4135139 = 6202709) B6202709
theorem B2758883 : Blo 1837620 2758883 := bstep (se 1 (by rfl) ⟨2069162, by rfl⟩ : syracuseStep 2758883 = 4138325) B4138325
theorem B3102961 : Blo 1837620 3102961 := bstep (se 2 (by rfl) ⟨1163610, by rfl⟩ : syracuseStep 3102961 = 2327221) B2327221
theorem B2758913 : Blo 1837620 2758913 := bstep (se 2 (by rfl) ⟨1034592, by rfl⟩ : syracuseStep 2758913 = 2069185) B2069185
theorem B3102995 : Blo 1837620 3102995 := bstep (se 1 (by rfl) ⟨2327246, by rfl⟩ : syracuseStep 3102995 = 4654493) B4654493
theorem B2758931 : Blo 1837620 2758931 := bstep (se 1 (by rfl) ⟨2069198, by rfl⟩ : syracuseStep 2758931 = 4138397) B4138397
theorem B6625585 : Blo 1837620 6625585 := bstep (se 2 (by rfl) ⟨2484594, by rfl⟩ : syracuseStep 6625585 = 4969189) B4969189
theorem B4970801 : Blo 1837620 4970801 := bstep (se 2 (by rfl) ⟨1864050, by rfl⟩ : syracuseStep 4970801 = 3728101) B3728101
theorem B2758961 : Blo 1837620 2758961 := bstep (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) B2069221
theorem B21223733 : Blo 1837620 21223733 := bstep (se 5 (by rfl) ⟨994862, by rfl⟩ : syracuseStep 21223733 = 1989725) B1989725
theorem B2758979 : Blo 1837620 2758979 := bstep (se 1 (by rfl) ⟨2069234, by rfl⟩ : syracuseStep 2758979 = 4138469) B4138469
theorem B2759009 : Blo 1837620 2759009 := bstep (se 2 (by rfl) ⟨1034628, by rfl⟩ : syracuseStep 2759009 = 2069257) B2069257
theorem B2759027 : Blo 1837620 2759027 := bstep (se 1 (by rfl) ⟨2069270, by rfl⟩ : syracuseStep 2759027 = 4138541) B4138541
theorem B5527939 : Blo 1837620 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B2759057 : Blo 1837620 2759057 := bstep (se 2 (by rfl) ⟨1034646, by rfl⟩ : syracuseStep 2759057 = 2069293) B2069293
theorem B3103123 : Blo 1837620 3103123 := bstep (se 1 (by rfl) ⟨2327342, by rfl⟩ : syracuseStep 3103123 = 4654685) B4654685
theorem B2759075 : Blo 1837620 2759075 := bstep (se 1 (by rfl) ⟨2069306, by rfl⟩ : syracuseStep 2759075 = 4138613) B4138613
theorem B22370741 : Blo 1837620 22370741 := bstep (se 5 (by rfl) ⟨1048628, by rfl⟩ : syracuseStep 22370741 = 2097257) B2097257
theorem B2759105 : Blo 1837620 2759105 := bstep (se 2 (by rfl) ⟨1034664, by rfl⟩ : syracuseStep 2759105 = 2069329) B2069329
theorem B2759123 : Blo 1837620 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B4135409 : Blo 1837620 4135409 := bstep (se 2 (by rfl) ⟨1550778, by rfl⟩ : syracuseStep 4135409 = 3101557) B3101557
theorem B2759153 : Blo 1837620 2759153 := bstep (se 2 (by rfl) ⟨1034682, by rfl⟩ : syracuseStep 2759153 = 2069365) B2069365
theorem B4135427 : Blo 1837620 4135427 := bstep (se 1 (by rfl) ⟨3101570, by rfl⟩ : syracuseStep 4135427 = 6203141) B6203141
theorem B2759171 : Blo 1837620 2759171 := bstep (se 1 (by rfl) ⟨2069378, by rfl⟩ : syracuseStep 2759171 = 4138757) B4138757
theorem B3103265 : Blo 1837620 3103265 := bstep (se 2 (by rfl) ⟨1163724, by rfl⟩ : syracuseStep 3103265 = 2327449) B2327449
theorem B2759201 : Blo 1837620 2759201 := bstep (se 2 (by rfl) ⟨1034700, by rfl⟩ : syracuseStep 2759201 = 2069401) B2069401
theorem B2759219 : Blo 1837620 2759219 := bstep (se 1 (by rfl) ⟨2069414, by rfl⟩ : syracuseStep 2759219 = 4138829) B4138829
theorem B2759249 : Blo 1837620 2759249 := bstep (se 2 (by rfl) ⟨1034718, by rfl⟩ : syracuseStep 2759249 = 2069437) B2069437
theorem B2759267 : Blo 1837620 2759267 := bstep (se 1 (by rfl) ⟨2069450, by rfl⟩ : syracuseStep 2759267 = 4138901) B4138901
theorem B6208109 : Blo 1837620 6208109 := bstep (se 3 (by rfl) ⟨1164020, by rfl⟩ : syracuseStep 6208109 = 2328041) B2328041
theorem B2759297 : Blo 1837620 2759297 := bstep (se 2 (by rfl) ⟨1034736, by rfl⟩ : syracuseStep 2759297 = 2069473) B2069473
theorem B15710861 : Blo 1837620 15710861 := bstep (se 3 (by rfl) ⟨2945786, by rfl⟩ : syracuseStep 15710861 = 5891573) B5891573
theorem B2759315 : Blo 1837620 2759315 := bstep (se 1 (by rfl) ⟨2069486, by rfl⟩ : syracuseStep 2759315 = 4138973) B4138973
theorem B3103393 : Blo 1837620 3103393 := bstep (se 2 (by rfl) ⟨1163772, by rfl⟩ : syracuseStep 3103393 = 2327545) B2327545
theorem B6208163 : Blo 1837620 6208163 := bstep (se 1 (by rfl) ⟨4656122, by rfl⟩ : syracuseStep 6208163 = 9312245) B9312245
theorem B2759345 : Blo 1837620 2759345 := bstep (se 2 (by rfl) ⟨1034754, by rfl⟩ : syracuseStep 2759345 = 2069509) B2069509
theorem B3103427 : Blo 1837620 3103427 := bstep (se 1 (by rfl) ⟨2327570, by rfl⟩ : syracuseStep 3103427 = 4655141) B4655141
theorem B2759363 : Blo 1837620 2759363 := bstep (se 1 (by rfl) ⟨2069522, by rfl⟩ : syracuseStep 2759363 = 4139045) B4139045
theorem B2759393 : Blo 1837620 2759393 := bstep (se 2 (by rfl) ⟨1034772, by rfl⟩ : syracuseStep 2759393 = 2069545) B2069545
theorem B2759411 : Blo 1837620 2759411 := bstep (se 1 (by rfl) ⟨2069558, by rfl⟩ : syracuseStep 2759411 = 4139117) B4139117
theorem B3357443 : Blo 1837620 3357443 := bstep (se 1 (by rfl) ⟨2518082, by rfl⟩ : syracuseStep 3357443 = 5036165) B5036165
theorem B4135697 : Blo 1837620 4135697 := bstep (se 2 (by rfl) ⟨1550886, by rfl⟩ : syracuseStep 4135697 = 3101773) B3101773
theorem B4135715 : Blo 1837620 4135715 := bstep (se 1 (by rfl) ⟨3101786, by rfl⟩ : syracuseStep 4135715 = 6203573) B6203573
theorem B10476323 : Blo 1837620 10476323 := bstep (se 1 (by rfl) ⟨7857242, by rfl⟩ : syracuseStep 10476323 = 15714485) B15714485
theorem B3103555 : Blo 1837620 3103555 := bstep (se 1 (by rfl) ⟨2327666, by rfl⟩ : syracuseStep 3103555 = 4655333) B4655333
theorem B6208433 : Blo 1837620 6208433 := bstep (se 2 (by rfl) ⟨2328162, by rfl⟩ : syracuseStep 6208433 = 4656325) B4656325
theorem B3103697 : Blo 1837620 3103697 := bstep (se 2 (by rfl) ⟨1163886, by rfl⟩ : syracuseStep 3103697 = 2327773) B2327773
theorem B5889037 : Blo 1837620 5889037 := bstep (se 3 (by rfl) ⟨1104194, by rfl⟩ : syracuseStep 5889037 = 2208389) B2208389
theorem B6978595 : Blo 1837620 6978595 := bstep (se 1 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 6978595 = 10467893) B10467893
theorem B4135985 : Blo 1837620 4135985 := bstep (se 2 (by rfl) ⟨1550994, by rfl⟩ : syracuseStep 4135985 = 3101989) B3101989
theorem B4136003 : Blo 1837620 4136003 := bstep (se 1 (by rfl) ⟨3102002, by rfl⟩ : syracuseStep 4136003 = 6204005) B6204005
theorem B4652113 : Blo 1837620 4652113 := bstep (se 2 (by rfl) ⟨1744542, by rfl⟩ : syracuseStep 4652113 = 3489085) B3489085
theorem B3103825 : Blo 1837620 3103825 := bstep (se 2 (by rfl) ⟨1163934, by rfl⟩ : syracuseStep 3103825 = 2327869) B2327869
theorem B3103859 : Blo 1837620 3103859 := bstep (se 1 (by rfl) ⟨2327894, by rfl⟩ : syracuseStep 3103859 = 4655789) B4655789
theorem B2096291 : Blo 1837620 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B6716579 : Blo 1837620 6716579 := bstep (se 1 (by rfl) ⟨5037434, by rfl⟩ : syracuseStep 6716579 = 10074869) B10074869
theorem B5307565 : Blo 1837620 5307565 := bstep (se 3 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 5307565 = 1990337) B1990337
theorem B193625315 : Blo 1837620 193625315 := bstep (se 1 (by rfl) ⟨145218986, by rfl⟩ : syracuseStep 193625315 = 290437973) B290437973
theorem B15924451 : Blo 1837620 15924451 := bstep (se 1 (by rfl) ⟨11943338, by rfl⟩ : syracuseStep 15924451 = 23886677) B23886677
theorem B3103987 : Blo 1837620 3103987 := bstep (se 1 (by rfl) ⟨2327990, by rfl⟩ : syracuseStep 3103987 = 4655981) B4655981
theorem B2325763 : Blo 1837620 2325763 := bstep (se 1 (by rfl) ⟨1744322, by rfl⟩ : syracuseStep 2325763 = 3488645) B3488645
theorem B4136273 : Blo 1837620 4136273 := bstep (se 2 (by rfl) ⟨1551102, by rfl⟩ : syracuseStep 4136273 = 3102205) B3102205
theorem B4652387 : Blo 1837620 4652387 := bstep (se 1 (by rfl) ⟨3489290, by rfl⟩ : syracuseStep 4652387 = 6978581) B6978581
theorem B4136291 : Blo 1837620 4136291 := bstep (se 1 (by rfl) ⟨3102218, by rfl⟩ : syracuseStep 4136291 = 6204437) B6204437
theorem B3104129 : Blo 1837620 3104129 := bstep (se 2 (by rfl) ⟨1164048, by rfl⟩ : syracuseStep 3104129 = 2328097) B2328097
theorem B3489169 : Blo 1837620 3489169 := bstep (se 2 (by rfl) ⟨1308438, by rfl⟩ : syracuseStep 3489169 = 2616877) B2616877
theorem B5234129 : Blo 1837620 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B4972013 : Blo 1837620 4972013 := bstep (se 3 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 4972013 = 1864505) B1864505
theorem B3104257 : Blo 1837620 3104257 := bstep (se 2 (by rfl) ⟨1164096, by rfl⟩ : syracuseStep 3104257 = 2328193) B2328193
theorem B4652579 : Blo 1837620 4652579 := bstep (se 1 (by rfl) ⟨3489434, by rfl⟩ : syracuseStep 4652579 = 6978869) B6978869
theorem B5668387 : Blo 1837620 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B3104291 : Blo 1837620 3104291 := bstep (se 1 (by rfl) ⟨2328218, by rfl⟩ : syracuseStep 3104291 = 4656437) B4656437
theorem B11779661 : Blo 1837620 11779661 := bstep (se 3 (by rfl) ⟨2208686, by rfl⟩ : syracuseStep 11779661 = 4417373) B4417373
theorem B4136561 : Blo 1837620 4136561 := bstep (se 2 (by rfl) ⟨1551210, by rfl⟩ : syracuseStep 4136561 = 3102421) B3102421
theorem B4136579 : Blo 1837620 4136579 := bstep (se 1 (by rfl) ⟨3102434, by rfl⟩ : syracuseStep 4136579 = 6204869) B6204869
theorem B2326259 : Blo 1837620 2326259 := bstep (se 1 (by rfl) ⟨1744694, by rfl⟩ : syracuseStep 2326259 = 3489389) B3489389
theorem B3489571 : Blo 1837620 3489571 := bstep (se 1 (by rfl) ⟨2617178, by rfl⟩ : syracuseStep 3489571 = 5234357) B5234357
theorem B3489617 : Blo 1837620 3489617 := bstep (se 2 (by rfl) ⟨1308606, by rfl⟩ : syracuseStep 3489617 = 2617213) B2617213
theorem B4136849 : Blo 1837620 4136849 := bstep (se 2 (by rfl) ⟨1551318, by rfl⟩ : syracuseStep 4136849 = 3102637) B3102637
theorem B4136867 : Blo 1837620 4136867 := bstep (se 1 (by rfl) ⟨3102650, by rfl⟩ : syracuseStep 4136867 = 6205301) B6205301
theorem B25157557 : Blo 1837620 25157557 := bstep (se 5 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 25157557 = 2358521) B2358521
theorem B7856099 : Blo 1837620 7856099 := bstep (se 1 (by rfl) ⟨5892074, by rfl⟩ : syracuseStep 7856099 = 11784149) B11784149
theorem B4137011 : Blo 1837620 4137011 := bstep (se 1 (by rfl) ⟨3102758, by rfl⟩ : syracuseStep 4137011 = 6205517) B6205517
theorem B17678411 : Blo 1837620 17678411 := bstep (se 1 (by rfl) ⟨13258808, by rfl⟩ : syracuseStep 17678411 = 26517617) B26517617
theorem B4137047 : Blo 1837620 4137047 := bstep (se 1 (by rfl) ⟨3102785, by rfl⟩ : syracuseStep 4137047 = 6205571) B6205571
theorem B5234881 : Blo 1837620 5234881 := bstep (se 2 (by rfl) ⟨1963080, by rfl⟩ : syracuseStep 5234881 = 3926161) B3926161
theorem B5890241 : Blo 1837620 5890241 := bstep (se 2 (by rfl) ⟨2208840, by rfl⟩ : syracuseStep 5890241 = 4417681) B4417681
theorem B4137227 : Blo 1837620 4137227 := bstep (se 1 (by rfl) ⟨3102920, by rfl⟩ : syracuseStep 4137227 = 6205841) B6205841
theorem B9306413 : Blo 1837620 9306413 := bstep (se 3 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 9306413 = 3489905) B3489905
theorem B4137281 : Blo 1837620 4137281 := bstep (se 2 (by rfl) ⟨1551480, by rfl⟩ : syracuseStep 4137281 = 3102961) B3102961
theorem B4137497 : Blo 1837620 4137497 := bstep (se 2 (by rfl) ⟨1551561, by rfl⟩ : syracuseStep 4137497 = 3103123) B3103123
theorem B22364707 : Blo 1837620 22364707 := bstep (se 1 (by rfl) ⟨16773530, by rfl⟩ : syracuseStep 22364707 = 33547061) B33547061
theorem B10764845 : Blo 1837620 10764845 := bstep (se 3 (by rfl) ⟨2018408, by rfl⟩ : syracuseStep 10764845 = 4036817) B4036817
theorem B226386485 : Blo 1837620 226386485 := bstep (se 5 (by rfl) ⟨10611866, by rfl⟩ : syracuseStep 226386485 = 21223733) B21223733
theorem B7963201 : Blo 1837620 7963201 := bstep (se 2 (by rfl) ⟨2986200, by rfl⟩ : syracuseStep 7963201 = 5972401) B5972401
theorem B26501701 : Blo 1837620 26501701 := bstep (se 4 (by rfl) ⟨2484534, by rfl⟩ : syracuseStep 26501701 = 4969069) B4969069
theorem B3490391 : Blo 1837620 3490391 := bstep (se 1 (by rfl) ⟨2617793, by rfl⟩ : syracuseStep 3490391 = 5235587) B5235587
theorem B2269783 : Blo 1837620 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B4137587 : Blo 1837620 4137587 := bstep (se 1 (by rfl) ⟨3103190, by rfl⟩ : syracuseStep 4137587 = 6206381) B6206381
theorem B6202007 : Blo 1837620 6202007 := bstep (se 1 (by rfl) ⟨4651505, by rfl⟩ : syracuseStep 6202007 = 9303011) B9303011
theorem B4137623 : Blo 1837620 4137623 := bstep (se 1 (by rfl) ⟨3103217, by rfl⟩ : syracuseStep 4137623 = 6206435) B6206435
theorem B3146393 : Blo 1837620 3146393 := bstep (se 2 (by rfl) ⟨1179897, by rfl⟩ : syracuseStep 3146393 = 2359795) B2359795
theorem B5890753 : Blo 1837620 5890753 := bstep (se 2 (by rfl) ⟨2209032, by rfl⟩ : syracuseStep 5890753 = 4418065) B4418065
theorem B47121101 : Blo 1837620 47121101 := bstep (se 3 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 47121101 = 17670413) B17670413
theorem B4653875 : Blo 1837620 4653875 := bstep (se 1 (by rfl) ⟨3490406, by rfl⟩ : syracuseStep 4653875 = 6980813) B6980813
theorem B3924811 : Blo 1837620 3924811 := bstep (se 1 (by rfl) ⟨2943608, by rfl⟩ : syracuseStep 3924811 = 5887217) B5887217
theorem B4137803 : Blo 1837620 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B2327383 : Blo 1837620 2327383 := bstep (se 1 (by rfl) ⟨1745537, by rfl⟩ : syracuseStep 2327383 = 3491075) B3491075
theorem B4137857 : Blo 1837620 4137857 := bstep (se 2 (by rfl) ⟨1551696, by rfl⟩ : syracuseStep 4137857 = 3103393) B3103393
theorem B16130947 : Blo 1837620 16130947 := bstep (se 1 (by rfl) ⟨12098210, by rfl⟩ : syracuseStep 16130947 = 24196421) B24196421
theorem B3777419 : Blo 1837620 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B4146059 : Blo 1837620 4146059 := bstep (se 1 (by rfl) ⟨3109544, by rfl⟩ : syracuseStep 4146059 = 6219089) B6219089
theorem B6980525 : Blo 1837620 6980525 := bstep (se 3 (by rfl) ⟨1308848, by rfl⟩ : syracuseStep 6980525 = 2617697) B2617697
theorem B8832017 : Blo 1837620 8832017 := bstep (se 2 (by rfl) ⟨3312006, by rfl⟩ : syracuseStep 8832017 = 6624013) B6624013
theorem B8389649 : Blo 1837620 8389649 := bstep (se 2 (by rfl) ⟨3146118, by rfl⟩ : syracuseStep 8389649 = 6292237) B6292237
theorem B4654169 : Blo 1837620 4654169 := bstep (se 2 (by rfl) ⟨1745313, by rfl⟩ : syracuseStep 4654169 = 3490627) B3490627
theorem B4138073 : Blo 1837620 4138073 := bstep (se 2 (by rfl) ⟨1551777, by rfl⟩ : syracuseStep 4138073 = 3103555) B3103555
theorem B3490931 : Blo 1837620 3490931 := bstep (se 1 (by rfl) ⟨2618198, by rfl⟩ : syracuseStep 3490931 = 5236397) B5236397
theorem B13255811 : Blo 1837620 13255811 := bstep (se 1 (by rfl) ⟨9941858, by rfl⟩ : syracuseStep 13255811 = 19883717) B19883717
theorem B6202547 : Blo 1837620 6202547 := bstep (se 1 (by rfl) ⟨4651910, by rfl⟩ : syracuseStep 6202547 = 9303821) B9303821
theorem B4138163 : Blo 1837620 4138163 := bstep (se 1 (by rfl) ⟨3103622, by rfl⟩ : syracuseStep 4138163 = 6207245) B6207245
theorem B15713459 : Blo 1837620 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B4138199 : Blo 1837620 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B3925273 : Blo 1837620 3925273 := bstep (se 2 (by rfl) ⟨1471977, by rfl⟩ : syracuseStep 3925273 = 2943955) B2943955
theorem B14157101 : Blo 1837620 14157101 := bstep (se 3 (by rfl) ⟨2654456, by rfl⟩ : syracuseStep 14157101 = 5308913) B5308913
theorem B4138379 : Blo 1837620 4138379 := bstep (se 1 (by rfl) ⟨3103784, by rfl⟩ : syracuseStep 4138379 = 6207569) B6207569
theorem B6202817 : Blo 1837620 6202817 := bstep (se 2 (by rfl) ⟨2326056, by rfl⟩ : syracuseStep 6202817 = 4652113) B4652113
theorem B4138433 : Blo 1837620 4138433 := bstep (se 2 (by rfl) ⟨1551912, by rfl⟩ : syracuseStep 4138433 = 3103825) B3103825
theorem B47777293 : Blo 1837620 47777293 := bstep (se 3 (by rfl) ⟨8958242, by rfl⟩ : syracuseStep 47777293 = 17916485) B17916485
theorem B15713837 : Blo 1837620 15713837 := bstep (se 3 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 15713837 = 5892689) B5892689
theorem B3491417 : Blo 1837620 3491417 := bstep (se 2 (by rfl) ⟨1309281, by rfl⟩ : syracuseStep 3491417 = 2618563) B2618563
theorem B13960835 : Blo 1837620 13960835 := bstep (se 1 (by rfl) ⟨10470626, by rfl⟩ : syracuseStep 13960835 = 20941253) B20941253
theorem B2328203 : Blo 1837620 2328203 := bstep (se 1 (by rfl) ⟨1746152, by rfl⟩ : syracuseStep 2328203 = 3492305) B3492305
theorem B4138649 : Blo 1837620 4138649 := bstep (se 2 (by rfl) ⟨1551993, by rfl⟩ : syracuseStep 4138649 = 3103987) B3103987
theorem B6981299 : Blo 1837620 6981299 := bstep (se 1 (by rfl) ⟨5235974, by rfl⟩ : syracuseStep 6981299 = 10471949) B10471949
theorem B4138739 : Blo 1837620 4138739 := bstep (se 1 (by rfl) ⟨3104054, by rfl⟩ : syracuseStep 4138739 = 6208109) B6208109
theorem B4138775 : Blo 1837620 4138775 := bstep (se 1 (by rfl) ⟨3104081, by rfl⟩ : syracuseStep 4138775 = 6208163) B6208163
theorem B2238295 : Blo 1837620 2238295 := bstep (se 1 (by rfl) ⟨1678721, by rfl⟩ : syracuseStep 2238295 = 3357443) B3357443
theorem B5891933 : Blo 1837620 5891933 := bstep (se 3 (by rfl) ⟨1104737, by rfl⟩ : syracuseStep 5891933 = 2209475) B2209475
theorem B4138955 : Blo 1837620 4138955 := bstep (se 1 (by rfl) ⟨3104216, by rfl⟩ : syracuseStep 4138955 = 6208433) B6208433
theorem B6203357 : Blo 1837620 6203357 := bstep (se 3 (by rfl) ⟨1163129, by rfl⟩ : syracuseStep 6203357 = 2326259) B2326259
theorem B4139009 : Blo 1837620 4139009 := bstep (se 2 (by rfl) ⟨1552128, by rfl⟩ : syracuseStep 4139009 = 3104257) B3104257
theorem B7964689 : Blo 1837620 7964689 := bstep (se 2 (by rfl) ⟨2986758, by rfl⟩ : syracuseStep 7964689 = 5973517) B5973517
theorem B10471517 : Blo 1837620 10471517 := bstep (se 3 (by rfl) ⟨1963409, by rfl⟩ : syracuseStep 10471517 = 3926819) B3926819
theorem B7850135 : Blo 1837620 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B23873687 : Blo 1837620 23873687 := bstep (se 1 (by rfl) ⟨17905265, by rfl⟩ : syracuseStep 23873687 = 35810531) B35810531
theorem B129083543 : Blo 1837620 129083543 := bstep (se 1 (by rfl) ⟨96812657, by rfl⟩ : syracuseStep 129083543 = 193625315) B193625315
theorem B3311819 : Blo 1837620 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B7555351 : Blo 1837620 7555351 := bstep (se 1 (by rfl) ⟨5666513, by rfl⟩ : syracuseStep 7555351 = 11333027) B11333027
theorem B4418009 : Blo 1837620 4418009 := bstep (se 2 (by rfl) ⟨1656753, by rfl⟩ : syracuseStep 4418009 = 3313507) B3313507
theorem B1837623 : Blo 1837620 1837623 := bstep (se 1 (by rfl) ⟨1378217, by rfl⟩ : syracuseStep 1837623 = 2756435) B2756435
theorem B10611265 : Blo 1837620 10611265 := bstep (se 2 (by rfl) ⟨3979224, by rfl⟩ : syracuseStep 10611265 = 7958449) B7958449
theorem B1837643 : Blo 1837620 1837643 := bstep (se 1 (by rfl) ⟨1378232, by rfl⟩ : syracuseStep 1837643 = 2756465) B2756465
theorem B1837655 : Blo 1837620 1837655 := bstep (se 1 (by rfl) ⟨1378241, by rfl⟩ : syracuseStep 1837655 = 2756483) B2756483
theorem B2943577 : Blo 1837620 2943577 := bstep (se 2 (by rfl) ⟨1103841, by rfl⟩ : syracuseStep 2943577 = 2207683) B2207683
theorem B79522397 : Blo 1837620 79522397 := bstep (se 3 (by rfl) ⟨14910449, by rfl⟩ : syracuseStep 79522397 = 29820899) B29820899
theorem B1837675 : Blo 1837620 1837675 := bstep (se 1 (by rfl) ⟨1378256, by rfl⟩ : syracuseStep 1837675 = 2756513) B2756513
theorem B1837687 : Blo 1837620 1837687 := bstep (se 1 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 1837687 = 2756531) B2756531
theorem B3926657 : Blo 1837620 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B1837707 : Blo 1837620 1837707 := bstep (se 1 (by rfl) ⟨1378280, by rfl⟩ : syracuseStep 1837707 = 2756561) B2756561
theorem B1837719 : Blo 1837620 1837719 := bstep (se 1 (by rfl) ⟨1378289, by rfl⟩ : syracuseStep 1837719 = 2756579) B2756579
theorem B5237399 : Blo 1837620 5237399 := bstep (se 1 (by rfl) ⟨3928049, by rfl⟩ : syracuseStep 5237399 = 7856099) B7856099
theorem B7457431 : Blo 1837620 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B1837739 : Blo 1837620 1837739 := bstep (se 1 (by rfl) ⟨1378304, by rfl⟩ : syracuseStep 1837739 = 2756609) B2756609
theorem B1837751 : Blo 1837620 1837751 := bstep (se 1 (by rfl) ⟨1378313, by rfl⟩ : syracuseStep 1837751 = 2756627) B2756627
theorem B1837771 : Blo 1837620 1837771 := bstep (se 1 (by rfl) ⟨1378328, by rfl⟩ : syracuseStep 1837771 = 2756657) B2756657
theorem B4655819 : Blo 1837620 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1837783 : Blo 1837620 1837783 := bstep (se 1 (by rfl) ⟨1378337, by rfl⟩ : syracuseStep 1837783 = 2756675) B2756675
theorem B1837803 : Blo 1837620 1837803 := bstep (se 1 (by rfl) ⟨1378352, by rfl⟩ : syracuseStep 1837803 = 2756705) B2756705
theorem B1837815 : Blo 1837620 1837815 := bstep (se 1 (by rfl) ⟨1378361, by rfl⟩ : syracuseStep 1837815 = 2756723) B2756723
theorem B1837835 : Blo 1837620 1837835 := bstep (se 1 (by rfl) ⟨1378376, by rfl⟩ : syracuseStep 1837835 = 2756753) B2756753
theorem B1837847 : Blo 1837620 1837847 := bstep (se 1 (by rfl) ⟨1378385, by rfl⟩ : syracuseStep 1837847 = 2756771) B2756771
theorem B16780067 : Blo 1837620 16780067 := bstep (se 1 (by rfl) ⟨12585050, by rfl⟩ : syracuseStep 16780067 = 25170101) B25170101
theorem B1837867 : Blo 1837620 1837867 := bstep (se 1 (by rfl) ⟨1378400, by rfl⟩ : syracuseStep 1837867 = 2756801) B2756801
theorem B13249325 : Blo 1837620 13249325 := bstep (se 3 (by rfl) ⟨2484248, by rfl⟩ : syracuseStep 13249325 = 4968497) B4968497
theorem B63720245 : Blo 1837620 63720245 := bstep (se 5 (by rfl) ⟨2986886, by rfl⟩ : syracuseStep 63720245 = 5973773) B5973773
theorem B1837879 : Blo 1837620 1837879 := bstep (se 1 (by rfl) ⟨1378409, by rfl⟩ : syracuseStep 1837879 = 2756819) B2756819
theorem B1837899 : Blo 1837620 1837899 := bstep (se 1 (by rfl) ⟨1378424, by rfl⟩ : syracuseStep 1837899 = 2756849) B2756849
theorem B10472267 : Blo 1837620 10472267 := bstep (se 1 (by rfl) ⟨7854200, by rfl⟩ : syracuseStep 10472267 = 15708401) B15708401
theorem B1837911 : Blo 1837620 1837911 := bstep (se 1 (by rfl) ⟨1378433, by rfl⟩ : syracuseStep 1837911 = 2756867) B2756867
theorem B7457629 : Blo 1837620 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B30231397 : Blo 1837620 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B1837931 : Blo 1837620 1837931 := bstep (se 1 (by rfl) ⟨1378448, by rfl⟩ : syracuseStep 1837931 = 2756897) B2756897
theorem B1837943 : Blo 1837620 1837943 := bstep (se 1 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 1837943 = 2756915) B2756915
theorem B1837963 : Blo 1837620 1837963 := bstep (se 1 (by rfl) ⟨1378472, by rfl⟩ : syracuseStep 1837963 = 2756945) B2756945
theorem B1837975 : Blo 1837620 1837975 := bstep (se 1 (by rfl) ⟨1378481, by rfl⟩ : syracuseStep 1837975 = 2756963) B2756963
theorem B1837995 : Blo 1837620 1837995 := bstep (se 1 (by rfl) ⟨1378496, by rfl⟩ : syracuseStep 1837995 = 2756993) B2756993
theorem B1838007 : Blo 1837620 1838007 := bstep (se 1 (by rfl) ⟨1378505, by rfl⟩ : syracuseStep 1838007 = 2757011) B2757011
theorem B2067403 : Blo 1837620 2067403 := bstep (se 1 (by rfl) ⟨1550552, by rfl⟩ : syracuseStep 2067403 = 3101105) B3101105
theorem B1838027 : Blo 1837620 1838027 := bstep (se 1 (by rfl) ⟨1378520, by rfl⟩ : syracuseStep 1838027 = 2757041) B2757041
theorem B1838039 : Blo 1837620 1838039 := bstep (se 1 (by rfl) ⟨1378529, by rfl⟩ : syracuseStep 1838039 = 2757059) B2757059
theorem B1838059 : Blo 1837620 1838059 := bstep (se 1 (by rfl) ⟨1378544, by rfl⟩ : syracuseStep 1838059 = 2757089) B2757089
theorem B1838071 : Blo 1837620 1838071 := bstep (se 1 (by rfl) ⟨1378553, by rfl⟩ : syracuseStep 1838071 = 2757107) B2757107
theorem B1838091 : Blo 1837620 1838091 := bstep (se 1 (by rfl) ⟨1378568, by rfl⟩ : syracuseStep 1838091 = 2757137) B2757137
theorem B1838103 : Blo 1837620 1838103 := bstep (se 1 (by rfl) ⟨1378577, by rfl⟩ : syracuseStep 1838103 = 2757155) B2757155
theorem B1838123 : Blo 1837620 1838123 := bstep (se 1 (by rfl) ⟨1378592, by rfl⟩ : syracuseStep 1838123 = 2757185) B2757185
theorem B2067511 : Blo 1837620 2067511 := bstep (se 1 (by rfl) ⟨1550633, by rfl⟩ : syracuseStep 2067511 = 3101267) B3101267
theorem B1838135 : Blo 1837620 1838135 := bstep (se 1 (by rfl) ⟨1378601, by rfl⟩ : syracuseStep 1838135 = 2757203) B2757203
theorem B8834113 : Blo 1837620 8834113 := bstep (se 2 (by rfl) ⟨3312792, by rfl⟩ : syracuseStep 8834113 = 6625585) B6625585
theorem B1838155 : Blo 1837620 1838155 := bstep (se 1 (by rfl) ⟨1378616, by rfl⟩ : syracuseStep 1838155 = 2757233) B2757233
theorem B6204491 : Blo 1837620 6204491 := bstep (se 1 (by rfl) ⟨4653368, by rfl⟩ : syracuseStep 6204491 = 9306737) B9306737
theorem B1838167 : Blo 1837620 1838167 := bstep (se 1 (by rfl) ⟨1378625, by rfl⟩ : syracuseStep 1838167 = 2757251) B2757251
theorem B5590109 : Blo 1837620 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B17910877 : Blo 1837620 17910877 := bstep (se 3 (by rfl) ⟨3358289, by rfl⟩ : syracuseStep 17910877 = 6716579) B6716579
theorem B1838187 : Blo 1837620 1838187 := bstep (se 1 (by rfl) ⟨1378640, by rfl⟩ : syracuseStep 1838187 = 2757281) B2757281
theorem B1838199 : Blo 1837620 1838199 := bstep (se 1 (by rfl) ⟨1378649, by rfl⟩ : syracuseStep 1838199 = 2757299) B2757299
theorem B6982787 : Blo 1837620 6982787 := bstep (se 1 (by rfl) ⟨5237090, by rfl⟩ : syracuseStep 6982787 = 10474181) B10474181
theorem B1838219 : Blo 1837620 1838219 := bstep (se 1 (by rfl) ⟨1378664, by rfl⟩ : syracuseStep 1838219 = 2757329) B2757329
theorem B1838231 : Blo 1837620 1838231 := bstep (se 1 (by rfl) ⟨1378673, by rfl⟩ : syracuseStep 1838231 = 2757347) B2757347
theorem B1838251 : Blo 1837620 1838251 := bstep (se 1 (by rfl) ⟨1378688, by rfl⟩ : syracuseStep 1838251 = 2757377) B2757377
theorem B1838263 : Blo 1837620 1838263 := bstep (se 1 (by rfl) ⟨1378697, by rfl⟩ : syracuseStep 1838263 = 2757395) B2757395
theorem B1838283 : Blo 1837620 1838283 := bstep (se 1 (by rfl) ⟨1378712, by rfl⟩ : syracuseStep 1838283 = 2757425) B2757425
theorem B1838295 : Blo 1837620 1838295 := bstep (se 1 (by rfl) ⟨1378721, by rfl⟩ : syracuseStep 1838295 = 2757443) B2757443
theorem B3312857 : Blo 1837620 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B2067691 : Blo 1837620 2067691 := bstep (se 1 (by rfl) ⟨1550768, by rfl⟩ : syracuseStep 2067691 = 3101537) B3101537
theorem B1838315 : Blo 1837620 1838315 := bstep (se 1 (by rfl) ⟨1378736, by rfl⟩ : syracuseStep 1838315 = 2757473) B2757473
theorem B1838327 : Blo 1837620 1838327 := bstep (se 1 (by rfl) ⟨1378745, by rfl⟩ : syracuseStep 1838327 = 2757491) B2757491
theorem B1838347 : Blo 1837620 1838347 := bstep (se 1 (by rfl) ⟨1378760, by rfl⟩ : syracuseStep 1838347 = 2757521) B2757521
theorem B1838359 : Blo 1837620 1838359 := bstep (se 1 (by rfl) ⟨1378769, by rfl⟩ : syracuseStep 1838359 = 2757539) B2757539
theorem B1838379 : Blo 1837620 1838379 := bstep (se 1 (by rfl) ⟨1378784, by rfl⟩ : syracuseStep 1838379 = 2757569) B2757569
theorem B1838391 : Blo 1837620 1838391 := bstep (se 1 (by rfl) ⟨1378793, by rfl⟩ : syracuseStep 1838391 = 2757587) B2757587
theorem B1838411 : Blo 1837620 1838411 := bstep (se 1 (by rfl) ⟨1378808, by rfl⟩ : syracuseStep 1838411 = 2757617) B2757617
theorem B2067799 : Blo 1837620 2067799 := bstep (se 1 (by rfl) ⟨1550849, by rfl⟩ : syracuseStep 2067799 = 3101699) B3101699
theorem B1838423 : Blo 1837620 1838423 := bstep (se 1 (by rfl) ⟨1378817, by rfl⟩ : syracuseStep 1838423 = 2757635) B2757635
theorem B6204761 : Blo 1837620 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1838443 : Blo 1837620 1838443 := bstep (se 1 (by rfl) ⟨1378832, by rfl⟩ : syracuseStep 1838443 = 2757665) B2757665
theorem B1838455 : Blo 1837620 1838455 := bstep (se 1 (by rfl) ⟨1378841, by rfl⟩ : syracuseStep 1838455 = 2757683) B2757683
theorem B1838475 : Blo 1837620 1838475 := bstep (se 1 (by rfl) ⟨1378856, by rfl⟩ : syracuseStep 1838475 = 2757713) B2757713
theorem B45329813 : Blo 1837620 45329813 := bstep (se 6 (by rfl) ⟨1062417, by rfl⟩ : syracuseStep 45329813 = 2124835) B2124835
theorem B1838487 : Blo 1837620 1838487 := bstep (se 1 (by rfl) ⟨1378865, by rfl⟩ : syracuseStep 1838487 = 2757731) B2757731
theorem B1838507 : Blo 1837620 1838507 := bstep (se 1 (by rfl) ⟨1378880, by rfl⟩ : syracuseStep 1838507 = 2757761) B2757761
theorem B15699379 : Blo 1837620 15699379 := bstep (se 1 (by rfl) ⟨11774534, by rfl⟩ : syracuseStep 15699379 = 23549069) B23549069
theorem B1838519 : Blo 1837620 1838519 := bstep (se 1 (by rfl) ⟨1378889, by rfl⟩ : syracuseStep 1838519 = 2757779) B2757779
theorem B7851467 : Blo 1837620 7851467 := bstep (se 1 (by rfl) ⟨5888600, by rfl⟩ : syracuseStep 7851467 = 11777201) B11777201
theorem B1838539 : Blo 1837620 1838539 := bstep (se 1 (by rfl) ⟨1378904, by rfl⟩ : syracuseStep 1838539 = 2757809) B2757809
theorem B2616791 : Blo 1837620 2616791 := bstep (se 1 (by rfl) ⟨1962593, by rfl⟩ : syracuseStep 2616791 = 3925187) B3925187
theorem B1838551 : Blo 1837620 1838551 := bstep (se 1 (by rfl) ⟨1378913, by rfl⟩ : syracuseStep 1838551 = 2757827) B2757827
theorem B1838571 : Blo 1837620 1838571 := bstep (se 1 (by rfl) ⟨1378928, by rfl⟩ : syracuseStep 1838571 = 2757857) B2757857
theorem B1838583 : Blo 1837620 1838583 := bstep (se 1 (by rfl) ⟨1378937, by rfl⟩ : syracuseStep 1838583 = 2757875) B2757875
theorem B2067979 : Blo 1837620 2067979 := bstep (se 1 (by rfl) ⟨1550984, by rfl⟩ : syracuseStep 2067979 = 3101969) B3101969
theorem B1838603 : Blo 1837620 1838603 := bstep (se 1 (by rfl) ⟨1378952, by rfl⟩ : syracuseStep 1838603 = 2757905) B2757905
theorem B1838615 : Blo 1837620 1838615 := bstep (se 1 (by rfl) ⟨1378961, by rfl⟩ : syracuseStep 1838615 = 2757923) B2757923
theorem B1838635 : Blo 1837620 1838635 := bstep (se 1 (by rfl) ⟨1378976, by rfl⟩ : syracuseStep 1838635 = 2757953) B2757953
theorem B1838647 : Blo 1837620 1838647 := bstep (se 1 (by rfl) ⟨1378985, by rfl⟩ : syracuseStep 1838647 = 2757971) B2757971
theorem B1838667 : Blo 1837620 1838667 := bstep (se 1 (by rfl) ⟨1379000, by rfl⟩ : syracuseStep 1838667 = 2758001) B2758001
theorem B6983243 : Blo 1837620 6983243 := bstep (se 1 (by rfl) ⟨5237432, by rfl⟩ : syracuseStep 6983243 = 10474865) B10474865
theorem B1838679 : Blo 1837620 1838679 := bstep (se 1 (by rfl) ⟨1379009, by rfl⟩ : syracuseStep 1838679 = 2758019) B2758019
theorem B1838699 : Blo 1837620 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B2068087 : Blo 1837620 2068087 := bstep (se 1 (by rfl) ⟨1551065, by rfl⟩ : syracuseStep 2068087 = 3102131) B3102131
theorem B1838711 : Blo 1837620 1838711 := bstep (se 1 (by rfl) ⟨1379033, by rfl⟩ : syracuseStep 1838711 = 2758067) B2758067
theorem B1838731 : Blo 1837620 1838731 := bstep (se 1 (by rfl) ⟨1379048, by rfl⟩ : syracuseStep 1838731 = 2758097) B2758097
theorem B1838743 : Blo 1837620 1838743 := bstep (se 1 (by rfl) ⟨1379057, by rfl⟩ : syracuseStep 1838743 = 2758115) B2758115
theorem B2616985 : Blo 1837620 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B1838763 : Blo 1837620 1838763 := bstep (se 1 (by rfl) ⟨1379072, by rfl⟩ : syracuseStep 1838763 = 2758145) B2758145
theorem B1838775 : Blo 1837620 1838775 := bstep (se 1 (by rfl) ⟨1379081, by rfl⟩ : syracuseStep 1838775 = 2758163) B2758163
theorem B1838795 : Blo 1837620 1838795 := bstep (se 1 (by rfl) ⟨1379096, by rfl⟩ : syracuseStep 1838795 = 2758193) B2758193
theorem B1838807 : Blo 1837620 1838807 := bstep (se 1 (by rfl) ⟨1379105, by rfl⟩ : syracuseStep 1838807 = 2758211) B2758211
theorem B1838827 : Blo 1837620 1838827 := bstep (se 1 (by rfl) ⟨1379120, by rfl⟩ : syracuseStep 1838827 = 2758241) B2758241
theorem B1838839 : Blo 1837620 1838839 := bstep (se 1 (by rfl) ⟨1379129, by rfl⟩ : syracuseStep 1838839 = 2758259) B2758259
theorem B1838859 : Blo 1837620 1838859 := bstep (se 1 (by rfl) ⟨1379144, by rfl⟩ : syracuseStep 1838859 = 2758289) B2758289
theorem B6983441 : Blo 1837620 6983441 := bstep (se 2 (by rfl) ⟨2618790, by rfl⟩ : syracuseStep 6983441 = 5237581) B5237581
theorem B1838871 : Blo 1837620 1838871 := bstep (se 1 (by rfl) ⟨1379153, by rfl⟩ : syracuseStep 1838871 = 2758307) B2758307
theorem B2068267 : Blo 1837620 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B1838891 : Blo 1837620 1838891 := bstep (se 1 (by rfl) ⟨1379168, by rfl⟩ : syracuseStep 1838891 = 2758337) B2758337
theorem B1838903 : Blo 1837620 1838903 := bstep (se 1 (by rfl) ⟨1379177, by rfl⟩ : syracuseStep 1838903 = 2758355) B2758355
theorem B1838923 : Blo 1837620 1838923 := bstep (se 1 (by rfl) ⟨1379192, by rfl⟩ : syracuseStep 1838923 = 2758385) B2758385
theorem B1838935 : Blo 1837620 1838935 := bstep (se 1 (by rfl) ⟨1379201, by rfl⟩ : syracuseStep 1838935 = 2758403) B2758403
theorem B2756441 : Blo 1837620 2756441 := bstep (se 2 (by rfl) ⟨1033665, by rfl⟩ : syracuseStep 2756441 = 2067331) B2067331
theorem B1838955 : Blo 1837620 1838955 := bstep (se 1 (by rfl) ⟨1379216, by rfl⟩ : syracuseStep 1838955 = 2758433) B2758433
theorem B1838967 : Blo 1837620 1838967 := bstep (se 1 (by rfl) ⟨1379225, by rfl⟩ : syracuseStep 1838967 = 2758451) B2758451
theorem B1838987 : Blo 1837620 1838987 := bstep (se 1 (by rfl) ⟨1379240, by rfl⟩ : syracuseStep 1838987 = 2758481) B2758481
theorem B2068375 : Blo 1837620 2068375 := bstep (se 1 (by rfl) ⟨1551281, by rfl⟩ : syracuseStep 2068375 = 3102563) B3102563
theorem B1838999 : Blo 1837620 1838999 := bstep (se 1 (by rfl) ⟨1379249, by rfl⟩ : syracuseStep 1838999 = 2758499) B2758499
theorem B1839019 : Blo 1837620 1839019 := bstep (se 1 (by rfl) ⟨1379264, by rfl⟩ : syracuseStep 1839019 = 2758529) B2758529
theorem B1839031 : Blo 1837620 1839031 := bstep (se 1 (by rfl) ⟨1379273, by rfl⟩ : syracuseStep 1839031 = 2758547) B2758547
theorem B2756555 : Blo 1837620 2756555 := bstep (se 1 (by rfl) ⟨2067416, by rfl⟩ : syracuseStep 2756555 = 4134833) B4134833
theorem B1839051 : Blo 1837620 1839051 := bstep (se 1 (by rfl) ⟨1379288, by rfl⟩ : syracuseStep 1839051 = 2758577) B2758577
theorem B2756567 : Blo 1837620 2756567 := bstep (se 1 (by rfl) ⟨2067425, by rfl⟩ : syracuseStep 2756567 = 4134851) B4134851
theorem B1839063 : Blo 1837620 1839063 := bstep (se 1 (by rfl) ⟨1379297, by rfl⟩ : syracuseStep 1839063 = 2758595) B2758595
theorem B1839083 : Blo 1837620 1839083 := bstep (se 1 (by rfl) ⟨1379312, by rfl⟩ : syracuseStep 1839083 = 2758625) B2758625
theorem B1839095 : Blo 1837620 1839095 := bstep (se 1 (by rfl) ⟨1379321, by rfl⟩ : syracuseStep 1839095 = 2758643) B2758643
theorem B1839115 : Blo 1837620 1839115 := bstep (se 1 (by rfl) ⟨1379336, by rfl⟩ : syracuseStep 1839115 = 2758673) B2758673
theorem B7852049 : Blo 1837620 7852049 := bstep (se 2 (by rfl) ⟨2944518, by rfl⟩ : syracuseStep 7852049 = 5889037) B5889037
theorem B6205463 : Blo 1837620 6205463 := bstep (se 1 (by rfl) ⟨4654097, by rfl⟩ : syracuseStep 6205463 = 9308195) B9308195
theorem B1839127 : Blo 1837620 1839127 := bstep (se 1 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 1839127 = 2758691) B2758691
theorem B2756633 : Blo 1837620 2756633 := bstep (se 2 (by rfl) ⟨1033737, by rfl⟩ : syracuseStep 2756633 = 2067475) B2067475
theorem B1839147 : Blo 1837620 1839147 := bstep (se 1 (by rfl) ⟨1379360, by rfl⟩ : syracuseStep 1839147 = 2758721) B2758721
theorem B3313715 : Blo 1837620 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B1839159 : Blo 1837620 1839159 := bstep (se 1 (by rfl) ⟨1379369, by rfl⟩ : syracuseStep 1839159 = 2758739) B2758739
theorem B2068555 : Blo 1837620 2068555 := bstep (se 1 (by rfl) ⟨1551416, by rfl⟩ : syracuseStep 2068555 = 3102833) B3102833
theorem B1839179 : Blo 1837620 1839179 := bstep (se 1 (by rfl) ⟨1379384, by rfl⟩ : syracuseStep 1839179 = 2758769) B2758769
theorem B1839191 : Blo 1837620 1839191 := bstep (se 1 (by rfl) ⟨1379393, by rfl⟩ : syracuseStep 1839191 = 2758787) B2758787
theorem B9310301 : Blo 1837620 9310301 := bstep (se 3 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 9310301 = 3491363) B3491363
theorem B1839211 : Blo 1837620 1839211 := bstep (se 1 (by rfl) ⟨1379408, by rfl⟩ : syracuseStep 1839211 = 2758817) B2758817
theorem B1839223 : Blo 1837620 1839223 := bstep (se 1 (by rfl) ⟨1379417, by rfl⟩ : syracuseStep 1839223 = 2758835) B2758835
theorem B2756747 : Blo 1837620 2756747 := bstep (se 1 (by rfl) ⟨2067560, by rfl⟩ : syracuseStep 2756747 = 4135121) B4135121
theorem B1839243 : Blo 1837620 1839243 := bstep (se 1 (by rfl) ⟨1379432, by rfl⟩ : syracuseStep 1839243 = 2758865) B2758865
theorem B2756759 : Blo 1837620 2756759 := bstep (se 1 (by rfl) ⟨2067569, by rfl⟩ : syracuseStep 2756759 = 4135139) B4135139
theorem B1839255 : Blo 1837620 1839255 := bstep (se 1 (by rfl) ⟨1379441, by rfl⟩ : syracuseStep 1839255 = 2758883) B2758883
theorem B1839275 : Blo 1837620 1839275 := bstep (se 1 (by rfl) ⟨1379456, by rfl⟩ : syracuseStep 1839275 = 2758913) B2758913
theorem B2068663 : Blo 1837620 2068663 := bstep (se 1 (by rfl) ⟨1551497, by rfl⟩ : syracuseStep 2068663 = 3102995) B3102995
theorem B1839287 : Blo 1837620 1839287 := bstep (se 1 (by rfl) ⟨1379465, by rfl⟩ : syracuseStep 1839287 = 2758931) B2758931
theorem B3313867 : Blo 1837620 3313867 := bstep (se 1 (by rfl) ⟨2485400, by rfl⟩ : syracuseStep 3313867 = 4970801) B4970801
theorem B1839307 : Blo 1837620 1839307 := bstep (se 1 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 1839307 = 2758961) B2758961
theorem B1839319 : Blo 1837620 1839319 := bstep (se 1 (by rfl) ⟨1379489, by rfl⟩ : syracuseStep 1839319 = 2758979) B2758979
theorem B2756825 : Blo 1837620 2756825 := bstep (se 2 (by rfl) ⟨1033809, by rfl⟩ : syracuseStep 2756825 = 2067619) B2067619
theorem B1839339 : Blo 1837620 1839339 := bstep (se 1 (by rfl) ⟨1379504, by rfl⟩ : syracuseStep 1839339 = 2759009) B2759009
theorem B1839351 : Blo 1837620 1839351 := bstep (se 1 (by rfl) ⟨1379513, by rfl⟩ : syracuseStep 1839351 = 2759027) B2759027
theorem B3928331 : Blo 1837620 3928331 := bstep (se 1 (by rfl) ⟨2946248, by rfl⟩ : syracuseStep 3928331 = 5892497) B5892497
theorem B1839371 : Blo 1837620 1839371 := bstep (se 1 (by rfl) ⟨1379528, by rfl⟩ : syracuseStep 1839371 = 2759057) B2759057
theorem B1839383 : Blo 1837620 1839383 := bstep (se 1 (by rfl) ⟨1379537, by rfl⟩ : syracuseStep 1839383 = 2759075) B2759075
theorem B14913827 : Blo 1837620 14913827 := bstep (se 1 (by rfl) ⟨11185370, by rfl⟩ : syracuseStep 14913827 = 22370741) B22370741
theorem B1839403 : Blo 1837620 1839403 := bstep (se 1 (by rfl) ⟨1379552, by rfl⟩ : syracuseStep 1839403 = 2759105) B2759105
theorem B1839415 : Blo 1837620 1839415 := bstep (se 1 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 1839415 = 2759123) B2759123
theorem B2756939 : Blo 1837620 2756939 := bstep (se 1 (by rfl) ⟨2067704, by rfl⟩ : syracuseStep 2756939 = 4135409) B4135409
theorem B1839435 : Blo 1837620 1839435 := bstep (se 1 (by rfl) ⟨1379576, by rfl⟩ : syracuseStep 1839435 = 2759153) B2759153
theorem B2756951 : Blo 1837620 2756951 := bstep (se 1 (by rfl) ⟨2067713, by rfl⟩ : syracuseStep 2756951 = 4135427) B4135427
theorem B1839447 : Blo 1837620 1839447 := bstep (se 1 (by rfl) ⟨1379585, by rfl⟩ : syracuseStep 1839447 = 2759171) B2759171
theorem B3101017 : Blo 1837620 3101017 := bstep (se 2 (by rfl) ⟨1162881, by rfl⟩ : syracuseStep 3101017 = 2325763) B2325763
theorem B5968217 : Blo 1837620 5968217 := bstep (se 2 (by rfl) ⟨2238081, by rfl⟩ : syracuseStep 5968217 = 4476163) B4476163
theorem B2068843 : Blo 1837620 2068843 := bstep (se 1 (by rfl) ⟨1551632, by rfl⟩ : syracuseStep 2068843 = 3103265) B3103265
theorem B1839467 : Blo 1837620 1839467 := bstep (se 1 (by rfl) ⟨1379600, by rfl⟩ : syracuseStep 1839467 = 2759201) B2759201
theorem B23572853 : Blo 1837620 23572853 := bstep (se 5 (by rfl) ⟨1104977, by rfl⟩ : syracuseStep 23572853 = 2209955) B2209955
theorem B1839479 : Blo 1837620 1839479 := bstep (se 1 (by rfl) ⟨1379609, by rfl⟩ : syracuseStep 1839479 = 2759219) B2759219
theorem B1839499 : Blo 1837620 1839499 := bstep (se 1 (by rfl) ⟨1379624, by rfl⟩ : syracuseStep 1839499 = 2759249) B2759249
theorem B1839511 : Blo 1837620 1839511 := bstep (se 1 (by rfl) ⟨1379633, by rfl⟩ : syracuseStep 1839511 = 2759267) B2759267
theorem B2757017 : Blo 1837620 2757017 := bstep (se 2 (by rfl) ⟨1033881, by rfl⟩ : syracuseStep 2757017 = 2067763) B2067763
theorem B1839531 : Blo 1837620 1839531 := bstep (se 1 (by rfl) ⟨1379648, by rfl⟩ : syracuseStep 1839531 = 2759297) B2759297
theorem B10473907 : Blo 1837620 10473907 := bstep (se 1 (by rfl) ⟨7855430, by rfl⟩ : syracuseStep 10473907 = 15710861) B15710861
theorem B1839543 : Blo 1837620 1839543 := bstep (se 1 (by rfl) ⟨1379657, by rfl⟩ : syracuseStep 1839543 = 2759315) B2759315
theorem B1839563 : Blo 1837620 1839563 := bstep (se 1 (by rfl) ⟨1379672, by rfl⟩ : syracuseStep 1839563 = 2759345) B2759345
theorem B2068951 : Blo 1837620 2068951 := bstep (se 1 (by rfl) ⟨1551713, by rfl⟩ : syracuseStep 2068951 = 3103427) B3103427
theorem B1839575 : Blo 1837620 1839575 := bstep (se 1 (by rfl) ⟨1379681, by rfl⟩ : syracuseStep 1839575 = 2759363) B2759363
theorem B1839595 : Blo 1837620 1839595 := bstep (se 1 (by rfl) ⟨1379696, by rfl⟩ : syracuseStep 1839595 = 2759393) B2759393
theorem B1839607 : Blo 1837620 1839607 := bstep (se 1 (by rfl) ⟨1379705, by rfl⟩ : syracuseStep 1839607 = 2759411) B2759411
theorem B3314177 : Blo 1837620 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2757131 : Blo 1837620 2757131 := bstep (se 1 (by rfl) ⟨2067848, by rfl⟩ : syracuseStep 2757131 = 4135697) B4135697
theorem B2757143 : Blo 1837620 2757143 := bstep (se 1 (by rfl) ⟨2067857, by rfl⟩ : syracuseStep 2757143 = 4135715) B4135715
theorem B6984215 : Blo 1837620 6984215 := bstep (se 1 (by rfl) ⟨5238161, by rfl⟩ : syracuseStep 6984215 = 10476323) B10476323
theorem B6206003 : Blo 1837620 6206003 := bstep (se 1 (by rfl) ⟨4654502, by rfl⟩ : syracuseStep 6206003 = 9309005) B9309005
theorem B2757209 : Blo 1837620 2757209 := bstep (se 2 (by rfl) ⟨1033953, by rfl⟩ : syracuseStep 2757209 = 2067907) B2067907
theorem B2069131 : Blo 1837620 2069131 := bstep (se 1 (by rfl) ⟨1551848, by rfl⟩ : syracuseStep 2069131 = 3103697) B3103697
theorem B1962679 : Blo 1837620 1962679 := bstep (se 1 (by rfl) ⟨1472009, by rfl⟩ : syracuseStep 1962679 = 2944019) B2944019
theorem B2757323 : Blo 1837620 2757323 := bstep (se 1 (by rfl) ⟨2067992, by rfl⟩ : syracuseStep 2757323 = 4135985) B4135985
theorem B2757335 : Blo 1837620 2757335 := bstep (se 1 (by rfl) ⟨2068001, by rfl⟩ : syracuseStep 2757335 = 4136003) B4136003
theorem B6984413 : Blo 1837620 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B2069239 : Blo 1837620 2069239 := bstep (se 1 (by rfl) ⟨1551929, by rfl⟩ : syracuseStep 2069239 = 3103859) B3103859
theorem B2757401 : Blo 1837620 2757401 := bstep (se 2 (by rfl) ⟨1034025, by rfl⟩ : syracuseStep 2757401 = 2068051) B2068051
theorem B6206273 : Blo 1837620 6206273 := bstep (se 2 (by rfl) ⟨2327352, by rfl⟩ : syracuseStep 6206273 = 4654705) B4654705
theorem B4969309 : Blo 1837620 4969309 := bstep (se 3 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 4969309 = 1863491) B1863491
theorem B2757515 : Blo 1837620 2757515 := bstep (se 1 (by rfl) ⟨2068136, by rfl⟩ : syracuseStep 2757515 = 4136273) B4136273
theorem B3101591 : Blo 1837620 3101591 := bstep (se 1 (by rfl) ⟨2326193, by rfl⟩ : syracuseStep 3101591 = 4652387) B4652387
theorem B2757527 : Blo 1837620 2757527 := bstep (se 1 (by rfl) ⟨2068145, by rfl⟩ : syracuseStep 2757527 = 4136291) B4136291
theorem B2069419 : Blo 1837620 2069419 := bstep (se 1 (by rfl) ⟨1552064, by rfl⟩ : syracuseStep 2069419 = 3104129) B3104129
theorem B13964237 : Blo 1837620 13964237 := bstep (se 3 (by rfl) ⟨2618294, by rfl⟩ : syracuseStep 13964237 = 5236589) B5236589
theorem B2757593 : Blo 1837620 2757593 := bstep (se 2 (by rfl) ⟨1034097, by rfl⟩ : syracuseStep 2757593 = 2068195) B2068195
theorem B3314675 : Blo 1837620 3314675 := bstep (se 1 (by rfl) ⟨2486006, by rfl⟩ : syracuseStep 3314675 = 4972013) B4972013
theorem B3101719 : Blo 1837620 3101719 := bstep (se 1 (by rfl) ⟨2326289, by rfl⟩ : syracuseStep 3101719 = 4652579) B4652579
theorem B2069527 : Blo 1837620 2069527 := bstep (se 1 (by rfl) ⟨1552145, by rfl⟩ : syracuseStep 2069527 = 3104291) B3104291
theorem B7853107 : Blo 1837620 7853107 := bstep (se 1 (by rfl) ⟨5889830, by rfl⟩ : syracuseStep 7853107 = 11779661) B11779661
theorem B2757707 : Blo 1837620 2757707 := bstep (se 1 (by rfl) ⟨2068280, by rfl⟩ : syracuseStep 2757707 = 4136561) B4136561
theorem B2618443 : Blo 1837620 2618443 := bstep (se 1 (by rfl) ⟨1963832, by rfl⟩ : syracuseStep 2618443 = 3927665) B3927665
theorem B2757719 : Blo 1837620 2757719 := bstep (se 1 (by rfl) ⟨2068289, by rfl⟩ : syracuseStep 2757719 = 4136579) B4136579
theorem B10466435 : Blo 1837620 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B2757785 : Blo 1837620 2757785 := bstep (se 2 (by rfl) ⟨1034169, by rfl⟩ : syracuseStep 2757785 = 2068339) B2068339
theorem B33543409 : Blo 1837620 33543409 := bstep (se 2 (by rfl) ⟨12578778, by rfl⟩ : syracuseStep 33543409 = 25157557) B25157557
theorem B2757899 : Blo 1837620 2757899 := bstep (se 1 (by rfl) ⟨2068424, by rfl⟩ : syracuseStep 2757899 = 4136849) B4136849
theorem B2757911 : Blo 1837620 2757911 := bstep (se 1 (by rfl) ⟨2068433, by rfl⟩ : syracuseStep 2757911 = 4136867) B4136867
theorem B2757977 : Blo 1837620 2757977 := bstep (se 2 (by rfl) ⟨1034241, by rfl⟩ : syracuseStep 2757977 = 2068483) B2068483
theorem B6206813 : Blo 1837620 6206813 := bstep (se 3 (by rfl) ⟨1163777, by rfl⟩ : syracuseStep 6206813 = 2327555) B2327555
theorem B13964723 : Blo 1837620 13964723 := bstep (se 1 (by rfl) ⟨10473542, by rfl⟩ : syracuseStep 13964723 = 20947085) B20947085
theorem B2758091 : Blo 1837620 2758091 := bstep (se 1 (by rfl) ⟨2068568, by rfl⟩ : syracuseStep 2758091 = 4137137) B4137137
theorem B2758103 : Blo 1837620 2758103 := bstep (se 1 (by rfl) ⟨2068577, by rfl⟩ : syracuseStep 2758103 = 4137155) B4137155
theorem B1963499 : Blo 1837620 1963499 := bstep (se 1 (by rfl) ⟨1472624, by rfl⟩ : syracuseStep 1963499 = 2945249) B2945249
theorem B2758169 : Blo 1837620 2758169 := bstep (se 2 (by rfl) ⟨1034313, by rfl⟩ : syracuseStep 2758169 = 2068627) B2068627
theorem B10466891 : Blo 1837620 10466891 := bstep (se 1 (by rfl) ⟨7850168, by rfl⟩ : syracuseStep 10466891 = 15700337) B15700337
theorem B3102347 : Blo 1837620 3102347 := bstep (se 1 (by rfl) ⟨2326760, by rfl⟩ : syracuseStep 3102347 = 4653521) B4653521
theorem B2758283 : Blo 1837620 2758283 := bstep (se 1 (by rfl) ⟨2068712, by rfl⟩ : syracuseStep 2758283 = 4137425) B4137425
theorem B2758295 : Blo 1837620 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B5887667 : Blo 1837620 5887667 := bstep (se 1 (by rfl) ⟨4415750, by rfl⟩ : syracuseStep 5887667 = 8831501) B8831501
theorem B4191959 : Blo 1837620 4191959 := bstep (se 1 (by rfl) ⟨3143969, by rfl⟩ : syracuseStep 4191959 = 6287939) B6287939
theorem B2758361 : Blo 1837620 2758361 := bstep (se 2 (by rfl) ⟨1034385, by rfl⟩ : syracuseStep 2758361 = 2068771) B2068771
theorem B3536651 : Blo 1837620 3536651 := bstep (se 1 (by rfl) ⟨2652488, by rfl⟩ : syracuseStep 3536651 = 5304977) B5304977
theorem B3102475 : Blo 1837620 3102475 := bstep (se 1 (by rfl) ⟨2326856, by rfl⟩ : syracuseStep 3102475 = 4653713) B4653713
theorem B4134707 : Blo 1837620 4134707 := bstep (se 1 (by rfl) ⟨3101030, by rfl⟩ : syracuseStep 4134707 = 6202061) B6202061
theorem B2758475 : Blo 1837620 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B4134743 : Blo 1837620 4134743 := bstep (se 1 (by rfl) ⟨3101057, by rfl⟩ : syracuseStep 4134743 = 6202115) B6202115
theorem B2758487 : Blo 1837620 2758487 := bstep (se 1 (by rfl) ⟨2068865, by rfl⟩ : syracuseStep 2758487 = 4137731) B4137731
theorem B7370585 : Blo 1837620 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B10475365 : Blo 1837620 10475365 := bstep (se 4 (by rfl) ⟨982065, by rfl⟩ : syracuseStep 10475365 = 1964131) B1964131
theorem B6977411 : Blo 1837620 6977411 := bstep (se 1 (by rfl) ⟨5233058, by rfl⟩ : syracuseStep 6977411 = 10466117) B10466117
theorem B3102617 : Blo 1837620 3102617 := bstep (se 2 (by rfl) ⟨1163481, by rfl⟩ : syracuseStep 3102617 = 2326963) B2326963
theorem B2758553 : Blo 1837620 2758553 := bstep (se 2 (by rfl) ⟨1034457, by rfl⟩ : syracuseStep 2758553 = 2068915) B2068915
theorem B4134923 : Blo 1837620 4134923 := bstep (se 1 (by rfl) ⟨3101192, by rfl⟩ : syracuseStep 4134923 = 6202385) B6202385
theorem B2758667 : Blo 1837620 2758667 := bstep (se 1 (by rfl) ⟨2069000, by rfl⟩ : syracuseStep 2758667 = 4138001) B4138001
theorem B2758679 : Blo 1837620 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B3102745 : Blo 1837620 3102745 := bstep (se 2 (by rfl) ⟨1163529, by rfl⟩ : syracuseStep 3102745 = 2327059) B2327059
theorem B4134977 : Blo 1837620 4134977 := bstep (se 2 (by rfl) ⟨1550616, by rfl⟩ : syracuseStep 4134977 = 3101233) B3101233
theorem B4970585 : Blo 1837620 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B2758745 : Blo 1837620 2758745 := bstep (se 2 (by rfl) ⟨1034529, by rfl⟩ : syracuseStep 2758745 = 2069059) B2069059
theorem B9312407 : Blo 1837620 9312407 := bstep (se 1 (by rfl) ⟨6984305, by rfl⟩ : syracuseStep 9312407 = 13968611) B13968611
theorem B2758859 : Blo 1837620 2758859 := bstep (se 1 (by rfl) ⟨2069144, by rfl⟩ : syracuseStep 2758859 = 4138289) B4138289
theorem B2758871 : Blo 1837620 2758871 := bstep (se 1 (by rfl) ⟨2069153, by rfl⟩ : syracuseStep 2758871 = 4138307) B4138307
theorem B5593367 : Blo 1837620 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B4135193 : Blo 1837620 4135193 := bstep (se 2 (by rfl) ⟨1550697, by rfl⟩ : syracuseStep 4135193 = 3101395) B3101395
theorem B2758937 : Blo 1837620 2758937 := bstep (se 2 (by rfl) ⟨1034601, by rfl⟩ : syracuseStep 2758937 = 2069203) B2069203
theorem B14145893 : Blo 1837620 14145893 := bstep (se 4 (by rfl) ⟨1326177, by rfl⟩ : syracuseStep 14145893 = 2652355) B2652355
theorem B4135283 : Blo 1837620 4135283 := bstep (se 1 (by rfl) ⟨3101462, by rfl⟩ : syracuseStep 4135283 = 6202925) B6202925
theorem B2759051 : Blo 1837620 2759051 := bstep (se 1 (by rfl) ⟨2069288, by rfl⟩ : syracuseStep 2759051 = 4138577) B4138577
theorem B4135319 : Blo 1837620 4135319 := bstep (se 1 (by rfl) ⟨3101489, by rfl⟩ : syracuseStep 4135319 = 6202979) B6202979
theorem B2759063 : Blo 1837620 2759063 := bstep (se 1 (by rfl) ⟨2069297, by rfl⟩ : syracuseStep 2759063 = 4138595) B4138595
theorem B7854509 : Blo 1837620 7854509 := bstep (se 3 (by rfl) ⟨1472720, by rfl⟩ : syracuseStep 7854509 = 2945441) B2945441
theorem B6207947 : Blo 1837620 6207947 := bstep (se 1 (by rfl) ⟨4655960, by rfl⟩ : syracuseStep 6207947 = 9311921) B9311921
theorem B2759129 : Blo 1837620 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B4135499 : Blo 1837620 4135499 := bstep (se 1 (by rfl) ⟨3101624, by rfl⟩ : syracuseStep 4135499 = 6203249) B6203249
theorem B11778635 : Blo 1837620 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B2759243 : Blo 1837620 2759243 := bstep (se 1 (by rfl) ⟨2069432, by rfl⟩ : syracuseStep 2759243 = 4138865) B4138865
theorem B3103319 : Blo 1837620 3103319 := bstep (se 1 (by rfl) ⟨2327489, by rfl⟩ : syracuseStep 3103319 = 4654979) B4654979
theorem B5233241 : Blo 1837620 5233241 := bstep (se 2 (by rfl) ⟨1962465, by rfl⟩ : syracuseStep 5233241 = 3924931) B3924931
theorem B2759255 : Blo 1837620 2759255 := bstep (se 1 (by rfl) ⟨2069441, by rfl⟩ : syracuseStep 2759255 = 4138883) B4138883
theorem B4135553 : Blo 1837620 4135553 := bstep (se 2 (by rfl) ⟨1550832, by rfl⟩ : syracuseStep 4135553 = 3101665) B3101665
theorem B2759321 : Blo 1837620 2759321 := bstep (se 2 (by rfl) ⟨1034745, by rfl⟩ : syracuseStep 2759321 = 2069491) B2069491
theorem B5233355 : Blo 1837620 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B120969941 : Blo 1837620 120969941 := bstep (se 7 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 120969941 = 2835233) B2835233
theorem B3103447 : Blo 1837620 3103447 := bstep (se 1 (by rfl) ⟨2327585, by rfl⟩ : syracuseStep 3103447 = 4655171) B4655171
theorem B9304793 : Blo 1837620 9304793 := bstep (se 2 (by rfl) ⟨3489297, by rfl⟩ : syracuseStep 9304793 = 6978595) B6978595
theorem B6208217 : Blo 1837620 6208217 := bstep (se 2 (by rfl) ⟨2328081, by rfl⟩ : syracuseStep 6208217 = 4656163) B4656163
theorem B4135769 : Blo 1837620 4135769 := bstep (se 2 (by rfl) ⟨1550913, by rfl⟩ : syracuseStep 4135769 = 3101827) B3101827
theorem B5888857 : Blo 1837620 5888857 := bstep (se 2 (by rfl) ⟨2208321, by rfl⟩ : syracuseStep 5888857 = 4416643) B4416643
theorem B13966181 : Blo 1837620 13966181 := bstep (se 4 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 13966181 = 2618659) B2618659
theorem B7076753 : Blo 1837620 7076753 := bstep (se 2 (by rfl) ⟨2653782, by rfl⟩ : syracuseStep 7076753 = 5307565) B5307565
theorem B4135859 : Blo 1837620 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B4135895 : Blo 1837620 4135895 := bstep (se 1 (by rfl) ⟨3101921, by rfl⟩ : syracuseStep 4135895 = 6203843) B6203843
theorem B21232601 : Blo 1837620 21232601 := bstep (se 2 (by rfl) ⟨7962225, by rfl⟩ : syracuseStep 21232601 = 15924451) B15924451
theorem B5889113 : Blo 1837620 5889113 := bstep (se 2 (by rfl) ⟨2208417, by rfl⟩ : syracuseStep 5889113 = 4416835) B4416835
theorem B4136075 : Blo 1837620 4136075 := bstep (se 1 (by rfl) ⟨3102056, by rfl⟩ : syracuseStep 4136075 = 6204113) B6204113
theorem B4652225 : Blo 1837620 4652225 := bstep (se 2 (by rfl) ⟨1744584, by rfl⟩ : syracuseStep 4652225 = 3489169) B3489169
theorem B4136129 : Blo 1837620 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B13958405 : Blo 1837620 13958405 := bstep (se 4 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 13958405 = 2617201) B2617201
theorem B13966667 : Blo 1837620 13966667 := bstep (se 1 (by rfl) ⟨10475000, by rfl⟩ : syracuseStep 13966667 = 20950001) B20950001
theorem B3104075 : Blo 1837620 3104075 := bstep (se 1 (by rfl) ⟨2328056, by rfl⟩ : syracuseStep 3104075 = 4656113) B4656113
theorem B4136345 : Blo 1837620 4136345 := bstep (se 2 (by rfl) ⟨1551129, by rfl⟩ : syracuseStep 4136345 = 3102259) B3102259
theorem B5889473 : Blo 1837620 5889473 := bstep (se 2 (by rfl) ⟨2208552, by rfl⟩ : syracuseStep 5889473 = 4417105) B4417105
theorem B3104203 : Blo 1837620 3104203 := bstep (se 1 (by rfl) ⟨2328152, by rfl⟩ : syracuseStep 3104203 = 4656305) B4656305
theorem B4136435 : Blo 1837620 4136435 := bstep (se 1 (by rfl) ⟨3102326, by rfl⟩ : syracuseStep 4136435 = 6204653) B6204653
theorem B4136471 : Blo 1837620 4136471 := bstep (se 1 (by rfl) ⟨3102353, by rfl⟩ : syracuseStep 4136471 = 6204707) B6204707
theorem B3104345 : Blo 1837620 3104345 := bstep (se 2 (by rfl) ⟨1164129, by rfl⟩ : syracuseStep 3104345 = 2328259) B2328259
theorem B3489419 : Blo 1837620 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B3489473 : Blo 1837620 3489473 := bstep (se 2 (by rfl) ⟨1308552, by rfl⟩ : syracuseStep 3489473 = 2617105) B2617105
theorem B4136651 : Blo 1837620 4136651 := bstep (se 1 (by rfl) ⟨3102488, by rfl⟩ : syracuseStep 4136651 = 6204977) B6204977
theorem B4652761 : Blo 1837620 4652761 := bstep (se 2 (by rfl) ⟨1744785, by rfl⟩ : syracuseStep 4652761 = 3489571) B3489571
theorem B4136705 : Blo 1837620 4136705 := bstep (se 2 (by rfl) ⟨1551264, by rfl⟩ : syracuseStep 4136705 = 3102529) B3102529
theorem B29835053 : Blo 1837620 29835053 := bstep (se 3 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 29835053 = 11188145) B11188145
theorem B5234483 : Blo 1837620 5234483 := bstep (se 1 (by rfl) ⟨3925862, by rfl⟩ : syracuseStep 5234483 = 7851725) B7851725
theorem B14909285 : Blo 1837620 14909285 := bstep (se 4 (by rfl) ⟨1397745, by rfl⟩ : syracuseStep 14909285 = 2795491) B2795491
theorem B2326411 : Blo 1837620 2326411 := bstep (se 1 (by rfl) ⟨1744808, by rfl⟩ : syracuseStep 2326411 = 3489617) B3489617
theorem B4136921 : Blo 1837620 4136921 := bstep (se 2 (by rfl) ⟨1551345, by rfl⟩ : syracuseStep 4136921 = 3102691) B3102691
theorem B5234699 : Blo 1837620 5234699 := bstep (se 1 (by rfl) ⟨3926024, by rfl⟩ : syracuseStep 5234699 = 7852049) B7852049
theorem B4136975 : Blo 1837620 4136975 := bstep (se 1 (by rfl) ⟨3102731, by rfl⟩ : syracuseStep 4136975 = 6205463) B6205463
theorem B4136993 : Blo 1837620 4136993 := bstep (se 2 (by rfl) ⟨1551372, by rfl⟩ : syracuseStep 4136993 = 3102745) B3102745
theorem B23552045 : Blo 1837620 23552045 := bstep (se 3 (by rfl) ⟨4416008, by rfl⟩ : syracuseStep 23552045 = 8832017) B8832017
theorem B6979841 : Blo 1837620 6979841 := bstep (se 2 (by rfl) ⟨2617440, by rfl⟩ : syracuseStep 6979841 = 5234881) B5234881
theorem B7176563 : Blo 1837620 7176563 := bstep (se 1 (by rfl) ⟨5382422, by rfl⟩ : syracuseStep 7176563 = 10764845) B10764845
theorem B4137335 : Blo 1837620 4137335 := bstep (se 1 (by rfl) ⟨3103001, by rfl⟩ : syracuseStep 4137335 = 6206003) B6206003
theorem B2097595 : Blo 1837620 2097595 := bstep (se 1 (by rfl) ⟨1573196, by rfl⟩ : syracuseStep 2097595 = 3146393) B3146393
theorem B4137515 : Blo 1837620 4137515 := bstep (se 1 (by rfl) ⟨3103136, by rfl⟩ : syracuseStep 4137515 = 6206273) B6206273
theorem B4653683 : Blo 1837620 4653683 := bstep (se 1 (by rfl) ⟨3490262, by rfl⟩ : syracuseStep 4653683 = 6980525) B6980525
theorem B29819609 : Blo 1837620 29819609 := bstep (se 2 (by rfl) ⟨11182353, by rfl⟩ : syracuseStep 29819609 = 22364707) B22364707
theorem B2327287 : Blo 1837620 2327287 := bstep (se 1 (by rfl) ⟨1745465, by rfl⟩ : syracuseStep 2327287 = 3490931) B3490931
theorem B14148353 : Blo 1837620 14148353 := bstep (se 2 (by rfl) ⟨5305632, by rfl⟩ : syracuseStep 14148353 = 10611265) B10611265
theorem B10617601 : Blo 1837620 10617601 := bstep (se 2 (by rfl) ⟨3981600, by rfl⟩ : syracuseStep 10617601 = 7963201) B7963201
theorem B3924769 : Blo 1837620 3924769 := bstep (se 2 (by rfl) ⟨1471788, by rfl⟩ : syracuseStep 3924769 = 2943577) B2943577
theorem B9438067 : Blo 1837620 9438067 := bstep (se 1 (by rfl) ⟨7078550, by rfl⟩ : syracuseStep 9438067 = 14157101) B14157101
theorem B4137875 : Blo 1837620 4137875 := bstep (se 1 (by rfl) ⟨3103406, by rfl⟩ : syracuseStep 4137875 = 6206813) B6206813
theorem B4137929 : Blo 1837620 4137929 := bstep (se 2 (by rfl) ⟨1551723, by rfl⟩ : syracuseStep 4137929 = 3103447) B3103447
theorem B2327611 : Blo 1837620 2327611 := bstep (se 1 (by rfl) ⟨1745708, by rfl⟩ : syracuseStep 2327611 = 3491417) B3491417
theorem B9307223 : Blo 1837620 9307223 := bstep (se 1 (by rfl) ⟨6980417, by rfl⟩ : syracuseStep 9307223 = 13960835) B13960835
theorem B3925111 : Blo 1837620 3925111 := bstep (se 1 (by rfl) ⟨2943833, by rfl⟩ : syracuseStep 3925111 = 5887667) B5887667
theorem B4654199 : Blo 1837620 4654199 := bstep (se 1 (by rfl) ⟨3490649, by rfl⟩ : syracuseStep 4654199 = 6981299) B6981299
theorem B5235997 : Blo 1837620 5235997 := bstep (se 3 (by rfl) ⟨981749, by rfl⟩ : syracuseStep 5235997 = 1963499) B1963499
theorem B6981011 : Blo 1837620 6981011 := bstep (se 1 (by rfl) ⟨5235758, by rfl⟩ : syracuseStep 6981011 = 10471517) B10471517
theorem B10470809 : Blo 1837620 10470809 := bstep (se 2 (by rfl) ⟨3926553, by rfl⟩ : syracuseStep 10470809 = 7853107) B7853107
theorem B3491257 : Blo 1837620 3491257 := bstep (se 2 (by rfl) ⟨1309221, by rfl⟩ : syracuseStep 3491257 = 2618443) B2618443
theorem B23881169 : Blo 1837620 23881169 := bstep (se 2 (by rfl) ⟨8955438, by rfl⟩ : syracuseStep 23881169 = 17910877) B17910877
theorem B3728911 : Blo 1837620 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B31409693 : Blo 1837620 31409693 := bstep (se 3 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 31409693 = 11778635) B11778635
theorem B9307709 : Blo 1837620 9307709 := bstep (se 3 (by rfl) ⟨1745195, by rfl⟩ : syracuseStep 9307709 = 3490391) B3490391
theorem B9430595 : Blo 1837620 9430595 := bstep (se 1 (by rfl) ⟨7072946, by rfl⟩ : syracuseStep 9430595 = 14145893) B14145893
theorem B5236339 : Blo 1837620 5236339 := bstep (se 1 (by rfl) ⟨3927254, by rfl⟩ : syracuseStep 5236339 = 7854509) B7854509
theorem B4138631 : Blo 1837620 4138631 := bstep (se 1 (by rfl) ⟨3103973, by rfl⟩ : syracuseStep 4138631 = 6207947) B6207947
theorem B3491599 : Blo 1837620 3491599 := bstep (se 1 (by rfl) ⟨2618699, by rfl⟩ : syracuseStep 3491599 = 5237399) B5237399
theorem B6203195 : Blo 1837620 6203195 := bstep (se 1 (by rfl) ⟨4652396, by rfl⟩ : syracuseStep 6203195 = 9304793) B9304793
theorem B4138811 : Blo 1837620 4138811 := bstep (se 1 (by rfl) ⟨3104108, by rfl⟩ : syracuseStep 4138811 = 6208217) B6208217
theorem B8832883 : Blo 1837620 8832883 := bstep (se 1 (by rfl) ⟨6624662, by rfl⟩ : syracuseStep 8832883 = 13249325) B13249325
theorem B6981511 : Blo 1837620 6981511 := bstep (se 1 (by rfl) ⟨5236133, by rfl⟩ : syracuseStep 6981511 = 10472267) B10472267
theorem B322586509 : Blo 1837620 322586509 := bstep (se 3 (by rfl) ⟨60484970, by rfl⟩ : syracuseStep 322586509 = 120969941) B120969941
theorem B20932505 : Blo 1837620 20932505 := bstep (se 2 (by rfl) ⟨7849689, by rfl⟩ : syracuseStep 20932505 = 15699379) B15699379
theorem B4138937 : Blo 1837620 4138937 := bstep (se 2 (by rfl) ⟨1552101, by rfl⟩ : syracuseStep 4138937 = 3104203) B3104203
theorem B63703057 : Blo 1837620 63703057 := bstep (se 2 (by rfl) ⟨23888646, by rfl⟩ : syracuseStep 63703057 = 47777293) B47777293
theorem B3926075 : Blo 1837620 3926075 := bstep (se 1 (by rfl) ⟨2944556, by rfl⟩ : syracuseStep 3926075 = 5889113) B5889113
theorem B4655191 : Blo 1837620 4655191 := bstep (se 1 (by rfl) ⟨3491393, by rfl⟩ : syracuseStep 4655191 = 6982787) B6982787
theorem B6203681 : Blo 1837620 6203681 := bstep (se 2 (by rfl) ⟨2326380, by rfl⟩ : syracuseStep 6203681 = 4652761) B4652761
theorem B3926315 : Blo 1837620 3926315 := bstep (se 1 (by rfl) ⟨2944736, by rfl⟩ : syracuseStep 3926315 = 5889473) B5889473
theorem B4655495 : Blo 1837620 4655495 := bstep (se 1 (by rfl) ⟨3491621, by rfl⟩ : syracuseStep 4655495 = 6983243) B6983243
theorem B2984393 : Blo 1837620 2984393 := bstep (se 2 (by rfl) ⟨1119147, by rfl⟩ : syracuseStep 2984393 = 2238295) B2238295
theorem B4655627 : Blo 1837620 4655627 := bstep (se 1 (by rfl) ⟨3491720, by rfl⟩ : syracuseStep 4655627 = 6983441) B6983441
theorem B1837627 : Blo 1837620 1837627 := bstep (se 1 (by rfl) ⟨1378220, by rfl⟩ : syracuseStep 1837627 = 2756441) B2756441
theorem B9939523 : Blo 1837620 9939523 := bstep (se 1 (by rfl) ⟨7454642, by rfl⟩ : syracuseStep 9939523 = 14909285) B14909285
theorem B1837703 : Blo 1837620 1837703 := bstep (se 1 (by rfl) ⟨1378277, by rfl⟩ : syracuseStep 1837703 = 2756555) B2756555
theorem B1837711 : Blo 1837620 1837711 := bstep (se 1 (by rfl) ⟨1378283, by rfl⟩ : syracuseStep 1837711 = 2756567) B2756567
theorem B1837755 : Blo 1837620 1837755 := bstep (se 1 (by rfl) ⟨1378316, by rfl⟩ : syracuseStep 1837755 = 2756633) B2756633
theorem B10619585 : Blo 1837620 10619585 := bstep (se 2 (by rfl) ⟨3982344, by rfl⟩ : syracuseStep 10619585 = 7964689) B7964689
theorem B1837831 : Blo 1837620 1837831 := bstep (se 1 (by rfl) ⟨1378373, by rfl⟩ : syracuseStep 1837831 = 2756747) B2756747
theorem B1837839 : Blo 1837620 1837839 := bstep (se 1 (by rfl) ⟨1378379, by rfl⟩ : syracuseStep 1837839 = 2756759) B2756759
theorem B3926827 : Blo 1837620 3926827 := bstep (se 1 (by rfl) ⟨2945120, by rfl⟩ : syracuseStep 3926827 = 5890241) B5890241
theorem B1837883 : Blo 1837620 1837883 := bstep (se 1 (by rfl) ⟨1378412, by rfl⟩ : syracuseStep 1837883 = 2756825) B2756825
theorem B6204275 : Blo 1837620 6204275 := bstep (se 1 (by rfl) ⟨4653206, by rfl⟩ : syracuseStep 6204275 = 9306413) B9306413
theorem B1837959 : Blo 1837620 1837959 := bstep (se 1 (by rfl) ⟨1378469, by rfl⟩ : syracuseStep 1837959 = 2756939) B2756939
theorem B1837967 : Blo 1837620 1837967 := bstep (se 1 (by rfl) ⟨1378475, by rfl⟩ : syracuseStep 1837967 = 2756951) B2756951
theorem B15715235 : Blo 1837620 15715235 := bstep (se 1 (by rfl) ⟨11786426, by rfl⟩ : syracuseStep 15715235 = 23572853) B23572853
theorem B4418489 : Blo 1837620 4418489 := bstep (se 2 (by rfl) ⟨1656933, by rfl⟩ : syracuseStep 4418489 = 3313867) B3313867
theorem B1838011 : Blo 1837620 1838011 := bstep (se 1 (by rfl) ⟨1378508, by rfl⟩ : syracuseStep 1838011 = 2757017) B2757017
theorem B1838087 : Blo 1837620 1838087 := bstep (se 1 (by rfl) ⟨1378565, by rfl⟩ : syracuseStep 1838087 = 2757131) B2757131
theorem B1838095 : Blo 1837620 1838095 := bstep (se 1 (by rfl) ⟨1378571, by rfl⟩ : syracuseStep 1838095 = 2757143) B2757143
theorem B4656143 : Blo 1837620 4656143 := bstep (se 1 (by rfl) ⟨3492107, by rfl⟩ : syracuseStep 4656143 = 6984215) B6984215
theorem B150924323 : Blo 1837620 150924323 := bstep (se 1 (by rfl) ⟨113193242, by rfl⟩ : syracuseStep 150924323 = 226386485) B226386485
theorem B1838139 : Blo 1837620 1838139 := bstep (se 1 (by rfl) ⟨1378604, by rfl⟩ : syracuseStep 1838139 = 2757209) B2757209
theorem B1838215 : Blo 1837620 1838215 := bstep (se 1 (by rfl) ⟨1378661, by rfl⟩ : syracuseStep 1838215 = 2757323) B2757323
theorem B1838223 : Blo 1837620 1838223 := bstep (se 1 (by rfl) ⟨1378667, by rfl⟩ : syracuseStep 1838223 = 2757335) B2757335
theorem B4656275 : Blo 1837620 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B1838267 : Blo 1837620 1838267 := bstep (se 1 (by rfl) ⟨1378700, by rfl⟩ : syracuseStep 1838267 = 2757401) B2757401
theorem B8834285 : Blo 1837620 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B1838343 : Blo 1837620 1838343 := bstep (se 1 (by rfl) ⟨1378757, by rfl⟩ : syracuseStep 1838343 = 2757515) B2757515
theorem B2067727 : Blo 1837620 2067727 := bstep (se 1 (by rfl) ⟨1550795, by rfl⟩ : syracuseStep 2067727 = 3101591) B3101591
theorem B1838351 : Blo 1837620 1838351 := bstep (se 1 (by rfl) ⟨1378763, by rfl⟩ : syracuseStep 1838351 = 2757527) B2757527
theorem B9309491 : Blo 1837620 9309491 := bstep (se 1 (by rfl) ⟨6982118, by rfl⟩ : syracuseStep 9309491 = 13964237) B13964237
theorem B1838395 : Blo 1837620 1838395 := bstep (se 1 (by rfl) ⟨1378796, by rfl⟩ : syracuseStep 1838395 = 2757593) B2757593
theorem B1838471 : Blo 1837620 1838471 := bstep (se 1 (by rfl) ⟨1378853, by rfl⟩ : syracuseStep 1838471 = 2757707) B2757707
theorem B1838479 : Blo 1837620 1838479 := bstep (se 1 (by rfl) ⟨1378859, by rfl⟩ : syracuseStep 1838479 = 2757719) B2757719
theorem B35335601 : Blo 1837620 35335601 := bstep (se 2 (by rfl) ⟨13250850, by rfl⟩ : syracuseStep 35335601 = 26501701) B26501701
theorem B1838523 : Blo 1837620 1838523 := bstep (se 1 (by rfl) ⟨1378892, by rfl⟩ : syracuseStep 1838523 = 2757785) B2757785
theorem B3026377 : Blo 1837620 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B1838599 : Blo 1837620 1838599 := bstep (se 1 (by rfl) ⟨1378949, by rfl⟩ : syracuseStep 1838599 = 2757899) B2757899
theorem B1838607 : Blo 1837620 1838607 := bstep (se 1 (by rfl) ⟨1378955, by rfl⟩ : syracuseStep 1838607 = 2757911) B2757911
theorem B1838651 : Blo 1837620 1838651 := bstep (se 1 (by rfl) ⟨1378988, by rfl⟩ : syracuseStep 1838651 = 2757977) B2757977
theorem B2616905 : Blo 1837620 2616905 := bstep (se 2 (by rfl) ⟨981339, by rfl⟩ : syracuseStep 2616905 = 1962679) B1962679
theorem B9309815 : Blo 1837620 9309815 := bstep (se 1 (by rfl) ⟨6982361, by rfl⟩ : syracuseStep 9309815 = 13964723) B13964723
theorem B1838727 : Blo 1837620 1838727 := bstep (se 1 (by rfl) ⟨1379045, by rfl⟩ : syracuseStep 1838727 = 2758091) B2758091
theorem B1838735 : Blo 1837620 1838735 := bstep (se 1 (by rfl) ⟨1379051, by rfl⟩ : syracuseStep 1838735 = 2758103) B2758103
theorem B1838779 : Blo 1837620 1838779 := bstep (se 1 (by rfl) ⟨1379084, by rfl⟩ : syracuseStep 1838779 = 2758169) B2758169
theorem B2068231 : Blo 1837620 2068231 := bstep (se 1 (by rfl) ⟨1551173, by rfl⟩ : syracuseStep 2068231 = 3102347) B3102347
theorem B1838855 : Blo 1837620 1838855 := bstep (se 1 (by rfl) ⟨1379141, by rfl⟩ : syracuseStep 1838855 = 2758283) B2758283
theorem B1838863 : Blo 1837620 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B7851809 : Blo 1837620 7851809 := bstep (se 2 (by rfl) ⟨2944428, by rfl⟩ : syracuseStep 7851809 = 5888857) B5888857
theorem B40308529 : Blo 1837620 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B1838907 : Blo 1837620 1838907 := bstep (se 1 (by rfl) ⟨1379180, by rfl⟩ : syracuseStep 1838907 = 2758361) B2758361
theorem B21507929 : Blo 1837620 21507929 := bstep (se 2 (by rfl) ⟨8065473, by rfl⟩ : syracuseStep 21507929 = 16130947) B16130947
theorem B2756471 : Blo 1837620 2756471 := bstep (se 1 (by rfl) ⟨2067353, by rfl⟩ : syracuseStep 2756471 = 4134707) B4134707
theorem B1838983 : Blo 1837620 1838983 := bstep (se 1 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 1838983 = 2758475) B2758475
theorem B2756495 : Blo 1837620 2756495 := bstep (se 1 (by rfl) ⟨2067371, by rfl⟩ : syracuseStep 2756495 = 4134743) B4134743
theorem B1838991 : Blo 1837620 1838991 := bstep (se 1 (by rfl) ⟨1379243, by rfl⟩ : syracuseStep 1838991 = 2758487) B2758487
theorem B3927955 : Blo 1837620 3927955 := bstep (se 1 (by rfl) ⟨2945966, by rfl⟩ : syracuseStep 3927955 = 5891933) B5891933
theorem B2756537 : Blo 1837620 2756537 := bstep (se 2 (by rfl) ⟨1033701, by rfl⟩ : syracuseStep 2756537 = 2067403) B2067403
theorem B2068411 : Blo 1837620 2068411 := bstep (se 1 (by rfl) ⟨1551308, by rfl⟩ : syracuseStep 2068411 = 3102617) B3102617
theorem B1839035 : Blo 1837620 1839035 := bstep (se 1 (by rfl) ⟨1379276, by rfl⟩ : syracuseStep 1839035 = 2758553) B2758553
theorem B2756615 : Blo 1837620 2756615 := bstep (se 1 (by rfl) ⟨2067461, by rfl⟩ : syracuseStep 2756615 = 4134923) B4134923
theorem B1839111 : Blo 1837620 1839111 := bstep (se 1 (by rfl) ⟨1379333, by rfl⟩ : syracuseStep 1839111 = 2758667) B2758667
theorem B1839119 : Blo 1837620 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B2756651 : Blo 1837620 2756651 := bstep (se 1 (by rfl) ⟨2067488, by rfl⟩ : syracuseStep 2756651 = 4134977) B4134977
theorem B3313723 : Blo 1837620 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B1839163 : Blo 1837620 1839163 := bstep (se 1 (by rfl) ⟨1379372, by rfl⟩ : syracuseStep 1839163 = 2758745) B2758745
theorem B2756681 : Blo 1837620 2756681 := bstep (se 2 (by rfl) ⟨1033755, by rfl⟩ : syracuseStep 2756681 = 2067511) B2067511
theorem B2207879 : Blo 1837620 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B1839239 : Blo 1837620 1839239 := bstep (se 1 (by rfl) ⟨1379429, by rfl⟩ : syracuseStep 1839239 = 2758859) B2758859
theorem B1839247 : Blo 1837620 1839247 := bstep (se 1 (by rfl) ⟨1379435, by rfl⟩ : syracuseStep 1839247 = 2758871) B2758871
theorem B2756795 : Blo 1837620 2756795 := bstep (se 1 (by rfl) ⟨2067596, by rfl⟩ : syracuseStep 2756795 = 4135193) B4135193
theorem B1839291 : Blo 1837620 1839291 := bstep (se 1 (by rfl) ⟨1379468, by rfl⟩ : syracuseStep 1839291 = 2758937) B2758937
theorem B2756855 : Blo 1837620 2756855 := bstep (se 1 (by rfl) ⟨2067641, by rfl⟩ : syracuseStep 2756855 = 4135283) B4135283
theorem B1839367 : Blo 1837620 1839367 := bstep (se 1 (by rfl) ⟨1379525, by rfl⟩ : syracuseStep 1839367 = 2759051) B2759051
theorem B2756879 : Blo 1837620 2756879 := bstep (se 1 (by rfl) ⟨2067659, by rfl⟩ : syracuseStep 2756879 = 4135319) B4135319
theorem B1839375 : Blo 1837620 1839375 := bstep (se 1 (by rfl) ⟨1379531, by rfl⟩ : syracuseStep 1839375 = 2759063) B2759063
theorem B2756921 : Blo 1837620 2756921 := bstep (se 2 (by rfl) ⟨1033845, by rfl⟩ : syracuseStep 2756921 = 2067691) B2067691
theorem B2945339 : Blo 1837620 2945339 := bstep (se 1 (by rfl) ⟨2209004, by rfl⟩ : syracuseStep 2945339 = 4418009) B4418009
theorem B1839419 : Blo 1837620 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B44724545 : Blo 1837620 44724545 := bstep (se 2 (by rfl) ⟨16771704, by rfl⟩ : syracuseStep 44724545 = 33543409) B33543409
theorem B2756999 : Blo 1837620 2756999 := bstep (se 1 (by rfl) ⟨2067749, by rfl⟩ : syracuseStep 2756999 = 4135499) B4135499
theorem B1839495 : Blo 1837620 1839495 := bstep (se 1 (by rfl) ⟨1379621, by rfl⟩ : syracuseStep 1839495 = 2759243) B2759243
theorem B2068879 : Blo 1837620 2068879 := bstep (se 1 (by rfl) ⟨1551659, by rfl⟩ : syracuseStep 2068879 = 3103319) B3103319
theorem B53014931 : Blo 1837620 53014931 := bstep (se 1 (by rfl) ⟨39761198, by rfl⟩ : syracuseStep 53014931 = 79522397) B79522397
theorem B1839503 : Blo 1837620 1839503 := bstep (se 1 (by rfl) ⟨1379627, by rfl⟩ : syracuseStep 1839503 = 2759255) B2759255
theorem B2757035 : Blo 1837620 2757035 := bstep (se 1 (by rfl) ⟨2067776, by rfl⟩ : syracuseStep 2757035 = 4135553) B4135553
theorem B2617771 : Blo 1837620 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B1839547 : Blo 1837620 1839547 := bstep (se 1 (by rfl) ⟨1379660, by rfl⟩ : syracuseStep 1839547 = 2759321) B2759321
theorem B2757065 : Blo 1837620 2757065 := bstep (se 2 (by rfl) ⟨1033899, by rfl⟩ : syracuseStep 2757065 = 2067799) B2067799
theorem B11186711 : Blo 1837620 11186711 := bstep (se 1 (by rfl) ⟨8390033, by rfl⟩ : syracuseStep 11186711 = 16780067) B16780067
theorem B42480163 : Blo 1837620 42480163 := bstep (se 1 (by rfl) ⟨31860122, by rfl⟩ : syracuseStep 42480163 = 63720245) B63720245
theorem B2757179 : Blo 1837620 2757179 := bstep (se 1 (by rfl) ⟨2067884, by rfl⟩ : syracuseStep 2757179 = 4135769) B4135769
theorem B11178557 : Blo 1837620 11178557 := bstep (se 3 (by rfl) ⟨2095979, by rfl⟩ : syracuseStep 11178557 = 4191959) B4191959
theorem B9310787 : Blo 1837620 9310787 := bstep (se 1 (by rfl) ⟨6983090, by rfl⟩ : syracuseStep 9310787 = 13966181) B13966181
theorem B2757239 : Blo 1837620 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B2757263 : Blo 1837620 2757263 := bstep (se 1 (by rfl) ⟨2067947, by rfl⟩ : syracuseStep 2757263 = 4135895) B4135895
theorem B2757305 : Blo 1837620 2757305 := bstep (se 2 (by rfl) ⟨1033989, by rfl⟩ : syracuseStep 2757305 = 2067979) B2067979
theorem B2757383 : Blo 1837620 2757383 := bstep (se 1 (by rfl) ⟨2068037, by rfl⟩ : syracuseStep 2757383 = 4136075) B4136075
theorem B3101483 : Blo 1837620 3101483 := bstep (se 1 (by rfl) ⟨2326112, by rfl⟩ : syracuseStep 3101483 = 4652225) B4652225
theorem B2757419 : Blo 1837620 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B2757449 : Blo 1837620 2757449 := bstep (se 2 (by rfl) ⟨1034043, by rfl⟩ : syracuseStep 2757449 = 2068087) B2068087
theorem B9311111 : Blo 1837620 9311111 := bstep (se 1 (by rfl) ⟨6983333, by rfl⟩ : syracuseStep 9311111 = 13966667) B13966667
theorem B2069383 : Blo 1837620 2069383 := bstep (se 1 (by rfl) ⟨1552037, by rfl⟩ : syracuseStep 2069383 = 3104075) B3104075
theorem B2757563 : Blo 1837620 2757563 := bstep (se 1 (by rfl) ⟨2068172, by rfl⟩ : syracuseStep 2757563 = 4136345) B4136345
theorem B2757623 : Blo 1837620 2757623 := bstep (se 1 (by rfl) ⟨2068217, by rfl⟩ : syracuseStep 2757623 = 4136435) B4136435
theorem B2757647 : Blo 1837620 2757647 := bstep (se 1 (by rfl) ⟨2068235, by rfl⟩ : syracuseStep 2757647 = 4136471) B4136471
theorem B10073117 : Blo 1837620 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B11056157 : Blo 1837620 11056157 := bstep (se 3 (by rfl) ⟨2073029, by rfl⟩ : syracuseStep 11056157 = 4146059) B4146059
theorem B2757689 : Blo 1837620 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B2069563 : Blo 1837620 2069563 := bstep (se 1 (by rfl) ⟨1552172, by rfl⟩ : syracuseStep 2069563 = 3104345) B3104345
theorem B2757767 : Blo 1837620 2757767 := bstep (se 1 (by rfl) ⟨2068325, by rfl⟩ : syracuseStep 2757767 = 4136651) B4136651
theorem B2757803 : Blo 1837620 2757803 := bstep (se 1 (by rfl) ⟨2068352, by rfl⟩ : syracuseStep 2757803 = 4136705) B4136705
theorem B3101881 : Blo 1837620 3101881 := bstep (se 2 (by rfl) ⟨1163205, by rfl⟩ : syracuseStep 3101881 = 2326411) B2326411
theorem B2757833 : Blo 1837620 2757833 := bstep (se 2 (by rfl) ⟨1034187, by rfl⟩ : syracuseStep 2757833 = 2068375) B2068375
theorem B2757947 : Blo 1837620 2757947 := bstep (se 1 (by rfl) ⟨2068460, by rfl⟩ : syracuseStep 2757947 = 4136921) B4136921
theorem B2758007 : Blo 1837620 2758007 := bstep (se 1 (by rfl) ⟨2068505, by rfl⟩ : syracuseStep 2758007 = 4137011) B4137011
theorem B11785607 : Blo 1837620 11785607 := bstep (se 1 (by rfl) ⟨8839205, by rfl⟩ : syracuseStep 11785607 = 17678411) B17678411
theorem B2758031 : Blo 1837620 2758031 := bstep (se 1 (by rfl) ⟨2068523, by rfl⟩ : syracuseStep 2758031 = 4137047) B4137047
theorem B6206867 : Blo 1837620 6206867 := bstep (se 1 (by rfl) ⟨4655150, by rfl⟩ : syracuseStep 6206867 = 9310301) B9310301
theorem B2758073 : Blo 1837620 2758073 := bstep (se 2 (by rfl) ⟨1034277, by rfl⟩ : syracuseStep 2758073 = 2068555) B2068555
theorem B2758151 : Blo 1837620 2758151 := bstep (se 1 (by rfl) ⟨2068613, by rfl⟩ : syracuseStep 2758151 = 4137227) B4137227
theorem B2618887 : Blo 1837620 2618887 := bstep (se 1 (by rfl) ⟨1964165, by rfl⟩ : syracuseStep 2618887 = 3928331) B3928331
theorem B9942551 : Blo 1837620 9942551 := bstep (se 1 (by rfl) ⟨7456913, by rfl⟩ : syracuseStep 9942551 = 14913827) B14913827
theorem B2758187 : Blo 1837620 2758187 := bstep (se 1 (by rfl) ⟨2068640, by rfl⟩ : syracuseStep 2758187 = 4137281) B4137281
theorem B3978811 : Blo 1837620 3978811 := bstep (se 1 (by rfl) ⟨2984108, by rfl⟩ : syracuseStep 3978811 = 5968217) B5968217
theorem B2758217 : Blo 1837620 2758217 := bstep (se 2 (by rfl) ⟨1034331, by rfl⟩ : syracuseStep 2758217 = 2068663) B2068663
theorem B2209451 : Blo 1837620 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B2758331 : Blo 1837620 2758331 := bstep (se 1 (by rfl) ⟨2068748, by rfl⟩ : syracuseStep 2758331 = 4137497) B4137497
theorem B10073801 : Blo 1837620 10073801 := bstep (se 2 (by rfl) ⟨3777675, by rfl⟩ : syracuseStep 10073801 = 7555351) B7555351
theorem B2758391 : Blo 1837620 2758391 := bstep (se 1 (by rfl) ⟨2068793, by rfl⟩ : syracuseStep 2758391 = 4137587) B4137587
theorem B4134671 : Blo 1837620 4134671 := bstep (se 1 (by rfl) ⟨3101003, by rfl⟩ : syracuseStep 4134671 = 6202007) B6202007
theorem B2758415 : Blo 1837620 2758415 := bstep (se 1 (by rfl) ⟨2068811, by rfl⟩ : syracuseStep 2758415 = 4137623) B4137623
theorem B4134689 : Blo 1837620 4134689 := bstep (se 2 (by rfl) ⟨1550508, by rfl⟩ : syracuseStep 4134689 = 3101017) B3101017
theorem B31414067 : Blo 1837620 31414067 := bstep (se 1 (by rfl) ⟨23560550, by rfl⟩ : syracuseStep 31414067 = 47121101) B47121101
theorem B2758457 : Blo 1837620 2758457 := bstep (se 2 (by rfl) ⟨1034421, by rfl⟩ : syracuseStep 2758457 = 2068843) B2068843
theorem B35346293 : Blo 1837620 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B3102583 : Blo 1837620 3102583 := bstep (se 1 (by rfl) ⟨2326937, by rfl⟩ : syracuseStep 3102583 = 4653875) B4653875
theorem B2758535 : Blo 1837620 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B13965209 : Blo 1837620 13965209 := bstep (se 2 (by rfl) ⟨5236953, by rfl⟩ : syracuseStep 13965209 = 10473907) B10473907
theorem B2758571 : Blo 1837620 2758571 := bstep (se 1 (by rfl) ⟨2068928, by rfl⟩ : syracuseStep 2758571 = 4137857) B4137857
theorem B2758601 : Blo 1837620 2758601 := bstep (se 2 (by rfl) ⟨1034475, by rfl⟩ : syracuseStep 2758601 = 2068951) B2068951
theorem B2209783 : Blo 1837620 2209783 := bstep (se 1 (by rfl) ⟨1657337, by rfl⟩ : syracuseStep 2209783 = 3314675) B3314675
theorem B5593099 : Blo 1837620 5593099 := bstep (se 1 (by rfl) ⟨4194824, by rfl⟩ : syracuseStep 5593099 = 8389649) B8389649
theorem B3102779 : Blo 1837620 3102779 := bstep (se 1 (by rfl) ⟨2327084, by rfl⟩ : syracuseStep 3102779 = 4654169) B4654169
theorem B2758715 : Blo 1837620 2758715 := bstep (se 1 (by rfl) ⟨2069036, by rfl⟩ : syracuseStep 2758715 = 4138073) B4138073
theorem B6977623 : Blo 1837620 6977623 := bstep (se 1 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 6977623 = 10466435) B10466435
theorem B8837207 : Blo 1837620 8837207 := bstep (se 1 (by rfl) ⟨6627905, by rfl⟩ : syracuseStep 8837207 = 13255811) B13255811
theorem B4135031 : Blo 1837620 4135031 := bstep (se 1 (by rfl) ⟨3101273, by rfl⟩ : syracuseStep 4135031 = 6202547) B6202547
theorem B2758775 : Blo 1837620 2758775 := bstep (se 1 (by rfl) ⟨2069081, by rfl⟩ : syracuseStep 2758775 = 4138163) B4138163
theorem B10475639 : Blo 1837620 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B2758799 : Blo 1837620 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B2758841 : Blo 1837620 2758841 := bstep (se 2 (by rfl) ⟨1034565, by rfl⟩ : syracuseStep 2758841 = 2069131) B2069131
theorem B9943241 : Blo 1837620 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B7854337 : Blo 1837620 7854337 := bstep (se 2 (by rfl) ⟨2945376, by rfl⟩ : syracuseStep 7854337 = 5890753) B5890753
theorem B2758919 : Blo 1837620 2758919 := bstep (se 1 (by rfl) ⟨2069189, by rfl⟩ : syracuseStep 2758919 = 4138379) B4138379
theorem B4135211 : Blo 1837620 4135211 := bstep (se 1 (by rfl) ⟨3101408, by rfl⟩ : syracuseStep 4135211 = 6202817) B6202817
theorem B2758955 : Blo 1837620 2758955 := bstep (se 1 (by rfl) ⟨2069216, by rfl⟩ : syracuseStep 2758955 = 4138433) B4138433
theorem B2758985 : Blo 1837620 2758985 := bstep (se 2 (by rfl) ⟨1034619, by rfl⟩ : syracuseStep 2758985 = 2069239) B2069239
theorem B10475891 : Blo 1837620 10475891 := bstep (se 1 (by rfl) ⟨7856918, by rfl⟩ : syracuseStep 10475891 = 15713837) B15713837
theorem B6977927 : Blo 1837620 6977927 := bstep (se 1 (by rfl) ⟨5233445, by rfl⟩ : syracuseStep 6977927 = 10466891) B10466891
theorem B5233081 : Blo 1837620 5233081 := bstep (se 2 (by rfl) ⟨1962405, by rfl⟩ : syracuseStep 5233081 = 3924811) B3924811
theorem B2759099 : Blo 1837620 2759099 := bstep (se 1 (by rfl) ⟨2069324, by rfl⟩ : syracuseStep 2759099 = 4138649) B4138649
theorem B3103177 : Blo 1837620 3103177 := bstep (se 2 (by rfl) ⟨1163691, by rfl⟩ : syracuseStep 3103177 = 2327383) B2327383
theorem B6625745 : Blo 1837620 6625745 := bstep (se 2 (by rfl) ⟨2484654, by rfl⟩ : syracuseStep 6625745 = 4969309) B4969309
theorem B9943505 : Blo 1837620 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B2759159 : Blo 1837620 2759159 := bstep (se 1 (by rfl) ⟨2069369, by rfl⟩ : syracuseStep 2759159 = 4138739) B4138739
theorem B2357767 : Blo 1837620 2357767 := bstep (se 1 (by rfl) ⟨1768325, by rfl⟩ : syracuseStep 2357767 = 3536651) B3536651
theorem B2759183 : Blo 1837620 2759183 := bstep (se 1 (by rfl) ⟨2069387, by rfl⟩ : syracuseStep 2759183 = 4138775) B4138775
theorem B4913723 : Blo 1837620 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B6978109 : Blo 1837620 6978109 := bstep (se 3 (by rfl) ⟨1308395, by rfl⟩ : syracuseStep 6978109 = 2616791) B2616791
theorem B2759225 : Blo 1837620 2759225 := bstep (se 2 (by rfl) ⟨1034709, by rfl⟩ : syracuseStep 2759225 = 2069419) B2069419
theorem B4651607 : Blo 1837620 4651607 := bstep (se 1 (by rfl) ⟨3488705, by rfl⟩ : syracuseStep 4651607 = 6977411) B6977411
theorem B2759303 : Blo 1837620 2759303 := bstep (se 1 (by rfl) ⟨2069477, by rfl⟩ : syracuseStep 2759303 = 4138955) B4138955
theorem B4135571 : Blo 1837620 4135571 := bstep (se 1 (by rfl) ⟨3101678, by rfl⟩ : syracuseStep 4135571 = 6203357) B6203357
theorem B2759339 : Blo 1837620 2759339 := bstep (se 1 (by rfl) ⟨2069504, by rfl⟩ : syracuseStep 2759339 = 4139009) B4139009
theorem B4135625 : Blo 1837620 4135625 := bstep (se 2 (by rfl) ⟨1550859, by rfl⟩ : syracuseStep 4135625 = 3101719) B3101719
theorem B2759369 : Blo 1837620 2759369 := bstep (se 2 (by rfl) ⟨1034763, by rfl⟩ : syracuseStep 2759369 = 2069527) B2069527
theorem B11778817 : Blo 1837620 11778817 := bstep (se 2 (by rfl) ⟨4417056, by rfl⟩ : syracuseStep 11778817 = 8834113) B8834113
theorem B5233423 : Blo 1837620 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B15915791 : Blo 1837620 15915791 := bstep (se 1 (by rfl) ⟨11936843, by rfl⟩ : syracuseStep 15915791 = 23873687) B23873687
theorem B86055695 : Blo 1837620 86055695 := bstep (se 1 (by rfl) ⟨64541771, by rfl⟩ : syracuseStep 86055695 = 129083543) B129083543
theorem B6208271 : Blo 1837620 6208271 := bstep (se 1 (by rfl) ⟨4656203, by rfl⟩ : syracuseStep 6208271 = 9312407) B9312407
theorem B9305117 : Blo 1837620 9305117 := bstep (se 3 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 9305117 = 3489419) B3489419
theorem B6208541 : Blo 1837620 6208541 := bstep (se 3 (by rfl) ⟨1164101, by rfl⟩ : syracuseStep 6208541 = 2328203) B2328203
theorem B5233697 : Blo 1837620 5233697 := bstep (se 2 (by rfl) ⟨1962636, by rfl⟩ : syracuseStep 5233697 = 3925273) B3925273
theorem B3488827 : Blo 1837620 3488827 := bstep (se 1 (by rfl) ⟨2616620, by rfl⟩ : syracuseStep 3488827 = 5233241) B5233241
theorem B3488903 : Blo 1837620 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B3103879 : Blo 1837620 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B4717835 : Blo 1837620 4717835 := bstep (se 1 (by rfl) ⟨3538376, by rfl⟩ : syracuseStep 4717835 = 7076753) B7076753
theorem B14155067 : Blo 1837620 14155067 := bstep (se 1 (by rfl) ⟨10616300, by rfl⟩ : syracuseStep 14155067 = 21232601) B21232601
theorem B4136327 : Blo 1837620 4136327 := bstep (se 1 (by rfl) ⟨3102245, by rfl⟩ : syracuseStep 4136327 = 6204491) B6204491
theorem B3726739 : Blo 1837620 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B9305603 : Blo 1837620 9305603 := bstep (se 1 (by rfl) ⟨6979202, by rfl⟩ : syracuseStep 9305603 = 13958405) B13958405
theorem B3489313 : Blo 1837620 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B4136507 : Blo 1837620 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B30219875 : Blo 1837620 30219875 := bstep (se 1 (by rfl) ⟨22664906, by rfl⟩ : syracuseStep 30219875 = 45329813) B45329813
theorem B5234311 : Blo 1837620 5234311 := bstep (se 1 (by rfl) ⟨3925733, by rfl⟩ : syracuseStep 5234311 = 7851467) B7851467
theorem B4136633 : Blo 1837620 4136633 := bstep (se 2 (by rfl) ⟨1551237, by rfl⟩ : syracuseStep 4136633 = 3102475) B3102475
theorem B2326315 : Blo 1837620 2326315 := bstep (se 1 (by rfl) ⟨1744736, by rfl⟩ : syracuseStep 2326315 = 3489473) B3489473
theorem B13967153 : Blo 1837620 13967153 := bstep (se 2 (by rfl) ⟨5237682, by rfl⟩ : syracuseStep 13967153 = 10475365) B10475365
theorem B19890035 : Blo 1837620 19890035 := bstep (se 1 (by rfl) ⟨14917526, by rfl⟩ : syracuseStep 19890035 = 29835053) B29835053
theorem B3489655 : Blo 1837620 3489655 := bstep (se 1 (by rfl) ⟨2617241, by rfl⟩ : syracuseStep 3489655 = 5234483) B5234483
theorem B3489799 : Blo 1837620 3489799 := bstep (se 1 (by rfl) ⟨2617349, by rfl⟩ : syracuseStep 3489799 = 5234699) B5234699
theorem B12574757 : Blo 1837620 12574757 := bstep (se 4 (by rfl) ⟨1178883, by rfl⟩ : syracuseStep 12574757 = 2357767) B2357767
theorem B26861645 : Blo 1837620 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B10469533 : Blo 1837620 10469533 := bstep (se 3 (by rfl) ⟨1963037, by rfl⟩ : syracuseStep 10469533 = 3926075) B3926075
theorem B4653227 : Blo 1837620 4653227 := bstep (se 1 (by rfl) ⟨3489920, by rfl⟩ : syracuseStep 4653227 = 6979841) B6979841
theorem B4784375 : Blo 1837620 4784375 := bstep (se 1 (by rfl) ⟨3588281, by rfl⟩ : syracuseStep 4784375 = 7176563) B7176563
theorem B3490361 : Blo 1837620 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B4137569 : Blo 1837620 4137569 := bstep (se 2 (by rfl) ⟨1551588, by rfl⟩ : syracuseStep 4137569 = 3103177) B3103177
theorem B56640217 : Blo 1837620 56640217 := bstep (se 2 (by rfl) ⟨21240081, by rfl⟩ : syracuseStep 56640217 = 42480163) B42480163
theorem B7857071 : Blo 1837620 7857071 := bstep (se 1 (by rfl) ⟨5892803, by rfl⟩ : syracuseStep 7857071 = 11785607) B11785607
theorem B4654007 : Blo 1837620 4654007 := bstep (se 1 (by rfl) ⟨3490505, by rfl⟩ : syracuseStep 4654007 = 6981011) B6981011
theorem B4137911 : Blo 1837620 4137911 := bstep (se 1 (by rfl) ⟨3103433, by rfl⟩ : syracuseStep 4137911 = 6206867) B6206867
theorem B6980539 : Blo 1837620 6980539 := bstep (se 1 (by rfl) ⟨5235404, by rfl⟩ : syracuseStep 6980539 = 10470809) B10470809
theorem B15705089 : Blo 1837620 15705089 := bstep (se 2 (by rfl) ⟨5889408, by rfl⟩ : syracuseStep 15705089 = 11778817) B11778817
theorem B14156801 : Blo 1837620 14156801 := bstep (se 2 (by rfl) ⟨5308800, by rfl⟩ : syracuseStep 14156801 = 10617601) B10617601
theorem B6628367 : Blo 1837620 6628367 := bstep (se 1 (by rfl) ⟨4971275, by rfl⟩ : syracuseStep 6628367 = 9942551) B9942551
theorem B20939795 : Blo 1837620 20939795 := bstep (se 1 (by rfl) ⟨15704846, by rfl⟩ : syracuseStep 20939795 = 31409693) B31409693
theorem B5235769 : Blo 1837620 5235769 := bstep (se 2 (by rfl) ⟨1963413, by rfl⟩ : syracuseStep 5235769 = 3926827) B3926827
theorem B12584089 : Blo 1837620 12584089 := bstep (se 2 (by rfl) ⟨4719033, by rfl⟩ : syracuseStep 12584089 = 9438067) B9438067
theorem B5891471 : Blo 1837620 5891471 := bstep (se 1 (by rfl) ⟨4418603, by rfl⟩ : syracuseStep 5891471 = 8837207) B8837207
theorem B4138505 : Blo 1837620 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B4417163 : Blo 1837620 4417163 := bstep (se 1 (by rfl) ⟨3312872, by rfl⟩ : syracuseStep 4417163 = 6625745) B6625745
theorem B6629003 : Blo 1837620 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B6981329 : Blo 1837620 6981329 := bstep (se 2 (by rfl) ⟨2617998, by rfl⟩ : syracuseStep 6981329 = 5235997) B5235997
theorem B5891869 : Blo 1837620 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B7079723 : Blo 1837620 7079723 := bstep (se 1 (by rfl) ⟨5309792, by rfl⟩ : syracuseStep 7079723 = 10619585) B10619585
theorem B10610527 : Blo 1837620 10610527 := bstep (se 1 (by rfl) ⟨7957895, by rfl⟩ : syracuseStep 10610527 = 15915791) B15915791
theorem B57370463 : Blo 1837620 57370463 := bstep (se 1 (by rfl) ⟨43027847, by rfl⟩ : syracuseStep 57370463 = 86055695) B86055695
theorem B4138847 : Blo 1837620 4138847 := bstep (se 1 (by rfl) ⟨3104135, by rfl⟩ : syracuseStep 4138847 = 6208271) B6208271
theorem B4655009 : Blo 1837620 4655009 := bstep (se 2 (by rfl) ⟨1745628, by rfl⟩ : syracuseStep 4655009 = 3491257) B3491257
theorem B3491849 : Blo 1837620 3491849 := bstep (se 2 (by rfl) ⟨1309443, by rfl⟩ : syracuseStep 3491849 = 2618887) B2618887
theorem B6203411 : Blo 1837620 6203411 := bstep (se 1 (by rfl) ⟨4652558, by rfl⟩ : syracuseStep 6203411 = 9305117) B9305117
theorem B4139027 : Blo 1837620 4139027 := bstep (se 1 (by rfl) ⟨3104270, by rfl⟩ : syracuseStep 4139027 = 6208541) B6208541
theorem B100616215 : Blo 1837620 100616215 := bstep (se 1 (by rfl) ⟨75462161, by rfl⟩ : syracuseStep 100616215 = 150924323) B150924323
theorem B6981785 : Blo 1837620 6981785 := bstep (se 2 (by rfl) ⟨2618169, by rfl⟩ : syracuseStep 6981785 = 5236339) B5236339
theorem B6203735 : Blo 1837620 6203735 := bstep (se 1 (by rfl) ⟨4652801, by rfl⟩ : syracuseStep 6203735 = 9305603) B9305603
theorem B4655465 : Blo 1837620 4655465 := bstep (se 2 (by rfl) ⟨1745799, by rfl⟩ : syracuseStep 4655465 = 3491599) B3491599
theorem B20146583 : Blo 1837620 20146583 := bstep (se 1 (by rfl) ⟨15109937, by rfl⟩ : syracuseStep 20146583 = 30219875) B30219875
theorem B9308681 : Blo 1837620 9308681 := bstep (se 2 (by rfl) ⟨3490755, by rfl⟩ : syracuseStep 9308681 = 6981511) B6981511
theorem B430115345 : Blo 1837620 430115345 := bstep (se 2 (by rfl) ⟨161293254, by rfl⟩ : syracuseStep 430115345 = 322586509) B322586509
theorem B5237273 : Blo 1837620 5237273 := bstep (se 2 (by rfl) ⟨1963977, by rfl⟩ : syracuseStep 5237273 = 3927955) B3927955
theorem B14338619 : Blo 1837620 14338619 := bstep (se 1 (by rfl) ⟨10753964, by rfl⟩ : syracuseStep 14338619 = 21507929) B21507929
theorem B1837647 : Blo 1837620 1837647 := bstep (se 1 (by rfl) ⟨1378235, by rfl⟩ : syracuseStep 1837647 = 2756471) B2756471
theorem B1837663 : Blo 1837620 1837663 := bstep (se 1 (by rfl) ⟨1378247, by rfl⟩ : syracuseStep 1837663 = 2756495) B2756495
theorem B1837691 : Blo 1837620 1837691 := bstep (se 1 (by rfl) ⟨1378268, by rfl⟩ : syracuseStep 1837691 = 2756537) B2756537
theorem B1837743 : Blo 1837620 1837743 := bstep (se 1 (by rfl) ⟨1378307, by rfl⟩ : syracuseStep 1837743 = 2756615) B2756615
theorem B7457465 : Blo 1837620 7457465 := bstep (se 2 (by rfl) ⟨2796549, by rfl⟩ : syracuseStep 7457465 = 5593099) B5593099
theorem B84937409 : Blo 1837620 84937409 := bstep (se 2 (by rfl) ⟨31851528, by rfl⟩ : syracuseStep 84937409 = 63703057) B63703057
theorem B1837767 : Blo 1837620 1837767 := bstep (se 1 (by rfl) ⟨1378325, by rfl⟩ : syracuseStep 1837767 = 2756651) B2756651
theorem B1837787 : Blo 1837620 1837787 := bstep (se 1 (by rfl) ⟨1378340, by rfl⟩ : syracuseStep 1837787 = 2756681) B2756681
theorem B4418297 : Blo 1837620 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B1837863 : Blo 1837620 1837863 := bstep (se 1 (by rfl) ⟨1378397, by rfl⟩ : syracuseStep 1837863 = 2756795) B2756795
theorem B1837903 : Blo 1837620 1837903 := bstep (se 1 (by rfl) ⟨1378427, by rfl⟩ : syracuseStep 1837903 = 2756855) B2756855
theorem B1837919 : Blo 1837620 1837919 := bstep (se 1 (by rfl) ⟨1378439, by rfl⟩ : syracuseStep 1837919 = 2756879) B2756879
theorem B1837947 : Blo 1837620 1837947 := bstep (se 1 (by rfl) ⟨1378460, by rfl⟩ : syracuseStep 1837947 = 2756921) B2756921
theorem B1837999 : Blo 1837620 1837999 := bstep (se 1 (by rfl) ⟨1378499, by rfl⟩ : syracuseStep 1837999 = 2756999) B2756999
theorem B35343287 : Blo 1837620 35343287 := bstep (se 1 (by rfl) ⟨26507465, by rfl⟩ : syracuseStep 35343287 = 53014931) B53014931
theorem B1838023 : Blo 1837620 1838023 := bstep (se 1 (by rfl) ⟨1378517, by rfl⟩ : syracuseStep 1838023 = 2757035) B2757035
theorem B1838043 : Blo 1837620 1838043 := bstep (se 1 (by rfl) ⟨1378532, by rfl⟩ : syracuseStep 1838043 = 2757065) B2757065
theorem B21220325 : Blo 1837620 21220325 := bstep (se 4 (by rfl) ⟨1989405, by rfl⟩ : syracuseStep 21220325 = 3978811) B3978811
theorem B10472449 : Blo 1837620 10472449 := bstep (se 2 (by rfl) ⟨3927168, by rfl⟩ : syracuseStep 10472449 = 7854337) B7854337
theorem B7457807 : Blo 1837620 7457807 := bstep (se 1 (by rfl) ⟨5593355, by rfl⟩ : syracuseStep 7457807 = 11186711) B11186711
theorem B1838119 : Blo 1837620 1838119 := bstep (se 1 (by rfl) ⟨1378589, by rfl⟩ : syracuseStep 1838119 = 2757179) B2757179
theorem B1838159 : Blo 1837620 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B1838175 : Blo 1837620 1838175 := bstep (se 1 (by rfl) ⟨1378631, by rfl⟩ : syracuseStep 1838175 = 2757263) B2757263
theorem B1838203 : Blo 1837620 1838203 := bstep (se 1 (by rfl) ⟨1378652, by rfl⟩ : syracuseStep 1838203 = 2757305) B2757305
theorem B9432235 : Blo 1837620 9432235 := bstep (se 1 (by rfl) ⟨7074176, by rfl⟩ : syracuseStep 9432235 = 14148353) B14148353
theorem B1838255 : Blo 1837620 1838255 := bstep (se 1 (by rfl) ⟨1378691, by rfl⟩ : syracuseStep 1838255 = 2757383) B2757383
theorem B2067655 : Blo 1837620 2067655 := bstep (se 1 (by rfl) ⟨1550741, by rfl⟩ : syracuseStep 2067655 = 3101483) B3101483
theorem B1838279 : Blo 1837620 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1838299 : Blo 1837620 1838299 := bstep (se 1 (by rfl) ⟨1378724, by rfl⟩ : syracuseStep 1838299 = 2757449) B2757449
theorem B1838375 : Blo 1837620 1838375 := bstep (se 1 (by rfl) ⟨1378781, by rfl⟩ : syracuseStep 1838375 = 2757563) B2757563
theorem B1838415 : Blo 1837620 1838415 := bstep (se 1 (by rfl) ⟨1378811, by rfl⟩ : syracuseStep 1838415 = 2757623) B2757623
theorem B1838431 : Blo 1837620 1838431 := bstep (se 1 (by rfl) ⟨1378823, by rfl⟩ : syracuseStep 1838431 = 2757647) B2757647
theorem B1838459 : Blo 1837620 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B6204815 : Blo 1837620 6204815 := bstep (se 1 (by rfl) ⟨4653611, by rfl⟩ : syracuseStep 6204815 = 9307223) B9307223
theorem B1838511 : Blo 1837620 1838511 := bstep (se 1 (by rfl) ⟨1378883, by rfl⟩ : syracuseStep 1838511 = 2757767) B2757767
theorem B1838535 : Blo 1837620 1838535 := bstep (se 1 (by rfl) ⟨1378901, by rfl⟩ : syracuseStep 1838535 = 2757803) B2757803
theorem B1838555 : Blo 1837620 1838555 := bstep (se 1 (by rfl) ⟨1378916, by rfl⟩ : syracuseStep 1838555 = 2757833) B2757833
theorem B1838631 : Blo 1837620 1838631 := bstep (se 1 (by rfl) ⟨1378973, by rfl⟩ : syracuseStep 1838631 = 2757947) B2757947
theorem B1838671 : Blo 1837620 1838671 := bstep (se 1 (by rfl) ⟨1379003, by rfl⟩ : syracuseStep 1838671 = 2758007) B2758007
theorem B1838687 : Blo 1837620 1838687 := bstep (se 1 (by rfl) ⟨1379015, by rfl⟩ : syracuseStep 1838687 = 2758031) B2758031
theorem B1838715 : Blo 1837620 1838715 := bstep (se 1 (by rfl) ⟨1379036, by rfl⟩ : syracuseStep 1838715 = 2758073) B2758073
theorem B1838767 : Blo 1837620 1838767 := bstep (se 1 (by rfl) ⟨1379075, by rfl⟩ : syracuseStep 1838767 = 2758151) B2758151
theorem B1838791 : Blo 1837620 1838791 := bstep (se 1 (by rfl) ⟨1379093, by rfl⟩ : syracuseStep 1838791 = 2758187) B2758187
theorem B6205139 : Blo 1837620 6205139 := bstep (se 1 (by rfl) ⟨4653854, by rfl⟩ : syracuseStep 6205139 = 9307709) B9307709
theorem B6287063 : Blo 1837620 6287063 := bstep (se 1 (by rfl) ⟨4715297, by rfl⟩ : syracuseStep 6287063 = 9430595) B9430595
theorem B1838811 : Blo 1837620 1838811 := bstep (se 1 (by rfl) ⟨1379108, by rfl⟩ : syracuseStep 1838811 = 2758217) B2758217
theorem B1838887 : Blo 1837620 1838887 := bstep (se 1 (by rfl) ⟨1379165, by rfl⟩ : syracuseStep 1838887 = 2758331) B2758331
theorem B1838927 : Blo 1837620 1838927 := bstep (se 1 (by rfl) ⟨1379195, by rfl⟩ : syracuseStep 1838927 = 2758391) B2758391
theorem B2756447 : Blo 1837620 2756447 := bstep (se 1 (by rfl) ⟨2067335, by rfl⟩ : syracuseStep 2756447 = 4134671) B4134671
theorem B1838943 : Blo 1837620 1838943 := bstep (se 1 (by rfl) ⟨1379207, by rfl⟩ : syracuseStep 1838943 = 2758415) B2758415
theorem B2756459 : Blo 1837620 2756459 := bstep (se 1 (by rfl) ⟨2067344, by rfl⟩ : syracuseStep 2756459 = 4134689) B4134689
theorem B7958381 : Blo 1837620 7958381 := bstep (se 3 (by rfl) ⟨1492196, by rfl⟩ : syracuseStep 7958381 = 2984393) B2984393
theorem B20942711 : Blo 1837620 20942711 := bstep (se 1 (by rfl) ⟨15707033, by rfl⟩ : syracuseStep 20942711 = 31414067) B31414067
theorem B1838971 : Blo 1837620 1838971 := bstep (se 1 (by rfl) ⟨1379228, by rfl⟩ : syracuseStep 1838971 = 2758457) B2758457
theorem B23564195 : Blo 1837620 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B1839023 : Blo 1837620 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B13955003 : Blo 1837620 13955003 := bstep (se 1 (by rfl) ⟨10466252, by rfl⟩ : syracuseStep 13955003 = 20932505) B20932505
theorem B9310139 : Blo 1837620 9310139 := bstep (se 1 (by rfl) ⟨6982604, by rfl⟩ : syracuseStep 9310139 = 13965209) B13965209
theorem B1839047 : Blo 1837620 1839047 := bstep (se 1 (by rfl) ⟨1379285, by rfl⟩ : syracuseStep 1839047 = 2758571) B2758571
theorem B1839067 : Blo 1837620 1839067 := bstep (se 1 (by rfl) ⟨1379300, by rfl⟩ : syracuseStep 1839067 = 2758601) B2758601
theorem B2068519 : Blo 1837620 2068519 := bstep (se 1 (by rfl) ⟨1551389, by rfl⟩ : syracuseStep 2068519 = 3102779) B3102779
theorem B1839143 : Blo 1837620 1839143 := bstep (se 1 (by rfl) ⟨1379357, by rfl⟩ : syracuseStep 1839143 = 2758715) B2758715
theorem B2756687 : Blo 1837620 2756687 := bstep (se 1 (by rfl) ⟨2067515, by rfl⟩ : syracuseStep 2756687 = 4135031) B4135031
theorem B1839183 : Blo 1837620 1839183 := bstep (se 1 (by rfl) ⟨1379387, by rfl⟩ : syracuseStep 1839183 = 2758775) B2758775
theorem B6983759 : Blo 1837620 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B1839199 : Blo 1837620 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B1839227 : Blo 1837620 1839227 := bstep (se 1 (by rfl) ⟨1379420, by rfl⟩ : syracuseStep 1839227 = 2758841) B2758841
theorem B1839279 : Blo 1837620 1839279 := bstep (se 1 (by rfl) ⟨1379459, by rfl⟩ : syracuseStep 1839279 = 2758919) B2758919
theorem B2756807 : Blo 1837620 2756807 := bstep (se 1 (by rfl) ⟨2067605, by rfl⟩ : syracuseStep 2756807 = 4135211) B4135211
theorem B2617543 : Blo 1837620 2617543 := bstep (se 1 (by rfl) ⟨1963157, by rfl⟩ : syracuseStep 2617543 = 3926315) B3926315
theorem B1839303 : Blo 1837620 1839303 := bstep (se 1 (by rfl) ⟨1379477, by rfl⟩ : syracuseStep 1839303 = 2758955) B2758955
theorem B1839323 : Blo 1837620 1839323 := bstep (se 1 (by rfl) ⟨1379492, by rfl⟩ : syracuseStep 1839323 = 2758985) B2758985
theorem B6983927 : Blo 1837620 6983927 := bstep (se 1 (by rfl) ⟨5237945, by rfl⟩ : syracuseStep 6983927 = 10475891) B10475891
theorem B1839399 : Blo 1837620 1839399 := bstep (se 1 (by rfl) ⟨1379549, by rfl⟩ : syracuseStep 1839399 = 2759099) B2759099
theorem B1839439 : Blo 1837620 1839439 := bstep (se 1 (by rfl) ⟨1379579, by rfl⟩ : syracuseStep 1839439 = 2759159) B2759159
theorem B1839455 : Blo 1837620 1839455 := bstep (se 1 (by rfl) ⟨1379591, by rfl⟩ : syracuseStep 1839455 = 2759183) B2759183
theorem B2756969 : Blo 1837620 2756969 := bstep (se 2 (by rfl) ⟨1033863, by rfl⟩ : syracuseStep 2756969 = 2067727) B2067727
theorem B1839483 : Blo 1837620 1839483 := bstep (se 1 (by rfl) ⟨1379612, by rfl⟩ : syracuseStep 1839483 = 2759225) B2759225
theorem B3101071 : Blo 1837620 3101071 := bstep (se 1 (by rfl) ⟨2325803, by rfl⟩ : syracuseStep 3101071 = 4651607) B4651607
theorem B1839535 : Blo 1837620 1839535 := bstep (se 1 (by rfl) ⟨1379651, by rfl⟩ : syracuseStep 1839535 = 2759303) B2759303
theorem B2757047 : Blo 1837620 2757047 := bstep (se 1 (by rfl) ⟨2067785, by rfl⟩ : syracuseStep 2757047 = 4135571) B4135571
theorem B1839559 : Blo 1837620 1839559 := bstep (se 1 (by rfl) ⟨1379669, by rfl⟩ : syracuseStep 1839559 = 2759339) B2759339
theorem B2757083 : Blo 1837620 2757083 := bstep (se 1 (by rfl) ⟨2067812, by rfl⟩ : syracuseStep 2757083 = 4135625) B4135625
theorem B1839579 : Blo 1837620 1839579 := bstep (se 1 (by rfl) ⟨1379684, by rfl⟩ : syracuseStep 1839579 = 2759369) B2759369
theorem B4968985 : Blo 1837620 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B4035169 : Blo 1837620 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B2945659 : Blo 1837620 2945659 := bstep (se 1 (by rfl) ⟨2209244, by rfl⟩ : syracuseStep 2945659 = 4418489) B4418489
theorem B6206327 : Blo 1837620 6206327 := bstep (se 1 (by rfl) ⟨4654745, by rfl⟩ : syracuseStep 6206327 = 9309491) B9309491
theorem B2757551 : Blo 1837620 2757551 := bstep (se 1 (by rfl) ⟨2068163, by rfl⟩ : syracuseStep 2757551 = 4136327) B4136327
theorem B23557067 : Blo 1837620 23557067 := bstep (se 1 (by rfl) ⟨17667800, by rfl⟩ : syracuseStep 23557067 = 35335601) B35335601
theorem B11187173 : Blo 1837620 11187173 := bstep (se 4 (by rfl) ⟨1048797, by rfl⟩ : syracuseStep 11187173 = 2097595) B2097595
theorem B2757641 : Blo 1837620 2757641 := bstep (se 2 (by rfl) ⟨1034115, by rfl⟩ : syracuseStep 2757641 = 2068231) B2068231
theorem B2757671 : Blo 1837620 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B3101753 : Blo 1837620 3101753 := bstep (se 2 (by rfl) ⟨1163157, by rfl⟩ : syracuseStep 3101753 = 2326315) B2326315
theorem B53744705 : Blo 1837620 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B6206543 : Blo 1837620 6206543 := bstep (se 1 (by rfl) ⟨4654907, by rfl⟩ : syracuseStep 6206543 = 9309815) B9309815
theorem B2757755 : Blo 1837620 2757755 := bstep (se 1 (by rfl) ⟨2068316, by rfl⟩ : syracuseStep 2757755 = 4136633) B4136633
theorem B11777177 : Blo 1837620 11777177 := bstep (se 2 (by rfl) ⟨4416441, by rfl⟩ : syracuseStep 11777177 = 8832883) B8832883
theorem B9311435 : Blo 1837620 9311435 := bstep (se 1 (by rfl) ⟨6983576, by rfl⟩ : syracuseStep 9311435 = 13967153) B13967153
theorem B13260023 : Blo 1837620 13260023 := bstep (se 1 (by rfl) ⟨9945017, by rfl⟩ : syracuseStep 13260023 = 19890035) B19890035
theorem B2757881 : Blo 1837620 2757881 := bstep (se 2 (by rfl) ⟨1034205, by rfl⟩ : syracuseStep 2757881 = 2068411) B2068411
theorem B2946377 : Blo 1837620 2946377 := bstep (se 2 (by rfl) ⟨1104891, by rfl⟩ : syracuseStep 2946377 = 2209783) B2209783
theorem B2757983 : Blo 1837620 2757983 := bstep (se 1 (by rfl) ⟨2068487, by rfl⟩ : syracuseStep 2757983 = 4136975) B4136975
theorem B2757995 : Blo 1837620 2757995 := bstep (se 1 (by rfl) ⟨2068496, by rfl⟩ : syracuseStep 2757995 = 4136993) B4136993
theorem B15701363 : Blo 1837620 15701363 := bstep (se 1 (by rfl) ⟨11776022, by rfl⟩ : syracuseStep 15701363 = 23552045) B23552045
theorem B9303497 : Blo 1837620 9303497 := bstep (se 2 (by rfl) ⟨3488811, by rfl⟩ : syracuseStep 9303497 = 6977623) B6977623
theorem B6206921 : Blo 1837620 6206921 := bstep (se 2 (by rfl) ⟨2327595, by rfl⟩ : syracuseStep 6206921 = 4655191) B4655191
theorem B1963559 : Blo 1837620 1963559 := bstep (se 1 (by rfl) ⟨1472669, by rfl⟩ : syracuseStep 1963559 = 2945339) B2945339
theorem B29816363 : Blo 1837620 29816363 := bstep (se 1 (by rfl) ⟨22362272, by rfl⟩ : syracuseStep 29816363 = 44724545) B44724545
theorem B2758223 : Blo 1837620 2758223 := bstep (se 1 (by rfl) ⟨2068667, by rfl⟩ : syracuseStep 2758223 = 4137335) B4137335
theorem B2758343 : Blo 1837620 2758343 := bstep (se 1 (by rfl) ⟨2068757, by rfl⟩ : syracuseStep 2758343 = 4137515) B4137515
theorem B7452371 : Blo 1837620 7452371 := bstep (se 1 (by rfl) ⟨5589278, by rfl⟩ : syracuseStep 7452371 = 11178557) B11178557
theorem B6207191 : Blo 1837620 6207191 := bstep (se 1 (by rfl) ⟨4655393, by rfl⟩ : syracuseStep 6207191 = 9310787) B9310787
theorem B3102455 : Blo 1837620 3102455 := bstep (se 1 (by rfl) ⟨2326841, by rfl⟩ : syracuseStep 3102455 = 4653683) B4653683
theorem B19879739 : Blo 1837620 19879739 := bstep (se 1 (by rfl) ⟨14909804, by rfl⟩ : syracuseStep 19879739 = 29819609) B29819609
theorem B2758505 : Blo 1837620 2758505 := bstep (se 2 (by rfl) ⟨1034439, by rfl⟩ : syracuseStep 2758505 = 2068879) B2068879
theorem B26515309 : Blo 1837620 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B6977441 : Blo 1837620 6977441 := bstep (se 2 (by rfl) ⟨2616540, by rfl⟩ : syracuseStep 6977441 = 5233081) B5233081
theorem B6207407 : Blo 1837620 6207407 := bstep (se 1 (by rfl) ⟨4655555, by rfl⟩ : syracuseStep 6207407 = 9311111) B9311111
theorem B2758583 : Blo 1837620 2758583 := bstep (se 1 (by rfl) ⟨2068937, by rfl⟩ : syracuseStep 2758583 = 4137875) B4137875
theorem B2758619 : Blo 1837620 2758619 := bstep (se 1 (by rfl) ⟨2068964, by rfl⟩ : syracuseStep 2758619 = 4137929) B4137929
theorem B7370771 : Blo 1837620 7370771 := bstep (se 1 (by rfl) ⟨5528078, by rfl⟩ : syracuseStep 7370771 = 11056157) B11056157
theorem B3102799 : Blo 1837620 3102799 := bstep (se 1 (by rfl) ⟨2327099, by rfl⟩ : syracuseStep 3102799 = 4654199) B4654199
theorem B9304145 : Blo 1837620 9304145 := bstep (se 2 (by rfl) ⟨3489054, by rfl⟩ : syracuseStep 9304145 = 6978109) B6978109
theorem B13252697 : Blo 1837620 13252697 := bstep (se 2 (by rfl) ⟨4969761, by rfl⟩ : syracuseStep 13252697 = 9939523) B9939523
theorem B3103049 : Blo 1837620 3103049 := bstep (se 2 (by rfl) ⟨1163643, by rfl⟩ : syracuseStep 3103049 = 2327287) B2327287
theorem B6977897 : Blo 1837620 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B5233025 : Blo 1837620 5233025 := bstep (se 2 (by rfl) ⟨1962384, by rfl⟩ : syracuseStep 5233025 = 3924769) B3924769
theorem B2759087 : Blo 1837620 2759087 := bstep (se 1 (by rfl) ⟨2069315, by rfl⟩ : syracuseStep 2759087 = 4138631) B4138631
theorem B6715867 : Blo 1837620 6715867 := bstep (se 1 (by rfl) ⟨5036900, by rfl⟩ : syracuseStep 6715867 = 10073801) B10073801
theorem B2759177 : Blo 1837620 2759177 := bstep (se 2 (by rfl) ⟨1034691, by rfl⟩ : syracuseStep 2759177 = 2069383) B2069383
theorem B4135463 : Blo 1837620 4135463 := bstep (se 1 (by rfl) ⟨3101597, by rfl⟩ : syracuseStep 4135463 = 6203195) B6203195
theorem B2759207 : Blo 1837620 2759207 := bstep (se 1 (by rfl) ⟨2069405, by rfl⟩ : syracuseStep 2759207 = 4138811) B4138811
theorem B63683117 : Blo 1837620 63683117 := bstep (se 3 (by rfl) ⟨11940584, by rfl⟩ : syracuseStep 63683117 = 23881169) B23881169
theorem B2759291 : Blo 1837620 2759291 := bstep (se 1 (by rfl) ⟨2069468, by rfl⟩ : syracuseStep 2759291 = 4138937) B4138937
theorem B23550709 : Blo 1837620 23550709 := bstep (se 5 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 23550709 = 2207879) B2207879
theorem B4651769 : Blo 1837620 4651769 := bstep (se 2 (by rfl) ⟨1744413, by rfl⟩ : syracuseStep 4651769 = 3488827) B3488827
theorem B3103481 : Blo 1837620 3103481 := bstep (se 2 (by rfl) ⟨1163805, by rfl⟩ : syracuseStep 3103481 = 2327611) B2327611
theorem B2759417 : Blo 1837620 2759417 := bstep (se 2 (by rfl) ⟨1034781, by rfl⟩ : syracuseStep 2759417 = 2069563) B2069563
theorem B5233481 : Blo 1837620 5233481 := bstep (se 2 (by rfl) ⟨1962555, by rfl⟩ : syracuseStep 5233481 = 3925111) B3925111
theorem B4135787 : Blo 1837620 4135787 := bstep (se 1 (by rfl) ⟨3101840, by rfl⟩ : syracuseStep 4135787 = 6203681) B6203681
theorem B6978413 : Blo 1837620 6978413 := bstep (se 3 (by rfl) ⟨1308452, by rfl⟩ : syracuseStep 6978413 = 2616905) B2616905
theorem B4135841 : Blo 1837620 4135841 := bstep (se 2 (by rfl) ⟨1550940, by rfl⟩ : syracuseStep 4135841 = 3101881) B3101881
theorem B4651951 : Blo 1837620 4651951 := bstep (se 1 (by rfl) ⟨3488963, by rfl⟩ : syracuseStep 4651951 = 6977927) B6977927
theorem B3103663 : Blo 1837620 3103663 := bstep (se 1 (by rfl) ⟨2327747, by rfl⟩ : syracuseStep 3103663 = 4655495) B4655495
theorem B3103751 : Blo 1837620 3103751 := bstep (se 1 (by rfl) ⟨2327813, by rfl⟩ : syracuseStep 3103751 = 4655627) B4655627
theorem B3275815 : Blo 1837620 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B4136183 : Blo 1837620 4136183 := bstep (se 1 (by rfl) ⟨3102137, by rfl⟩ : syracuseStep 4136183 = 6204275) B6204275
theorem B10476823 : Blo 1837620 10476823 := bstep (se 1 (by rfl) ⟨7857617, by rfl⟩ : syracuseStep 10476823 = 15715235) B15715235
theorem B3104095 : Blo 1837620 3104095 := bstep (se 1 (by rfl) ⟨2328071, by rfl⟩ : syracuseStep 3104095 = 4656143) B4656143
theorem B4971881 : Blo 1837620 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B3489131 : Blo 1837620 3489131 := bstep (se 1 (by rfl) ⟨2616848, by rfl⟩ : syracuseStep 3489131 = 5233697) B5233697
theorem B4652417 : Blo 1837620 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B2325935 : Blo 1837620 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B3104183 : Blo 1837620 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B5889523 : Blo 1837620 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B3145223 : Blo 1837620 3145223 := bstep (se 1 (by rfl) ⟨2358917, by rfl⟩ : syracuseStep 3145223 = 4717835) B4717835
theorem B6979081 : Blo 1837620 6979081 := bstep (se 2 (by rfl) ⟨2617155, by rfl⟩ : syracuseStep 6979081 = 5234311) B5234311
theorem B9436711 : Blo 1837620 9436711 := bstep (se 1 (by rfl) ⟨7077533, by rfl⟩ : syracuseStep 9436711 = 14155067) B14155067
theorem B4652873 : Blo 1837620 4652873 := bstep (se 2 (by rfl) ⟨1744827, by rfl⟩ : syracuseStep 4652873 = 3489655) B3489655
theorem B4136777 : Blo 1837620 4136777 := bstep (se 2 (by rfl) ⟨1551291, by rfl⟩ : syracuseStep 4136777 = 3102583) B3102583
theorem B5234539 : Blo 1837620 5234539 := bstep (se 1 (by rfl) ⟨3925904, by rfl⟩ : syracuseStep 5234539 = 7851809) B7851809
theorem B4653065 : Blo 1837620 4653065 := bstep (se 2 (by rfl) ⟨1744899, by rfl⟩ : syracuseStep 4653065 = 3489799) B3489799
theorem B4137065 : Blo 1837620 4137065 := bstep (se 2 (by rfl) ⟨1551399, by rfl⟩ : syracuseStep 4137065 = 3102799) B3102799
theorem B71631053 : Blo 1837620 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B13959377 : Blo 1837620 13959377 := bstep (se 2 (by rfl) ⟨5234766, by rfl⟩ : syracuseStep 13959377 = 10469533) B10469533
theorem B3490057 : Blo 1837620 3490057 := bstep (se 2 (by rfl) ⟨1308771, by rfl⟩ : syracuseStep 3490057 = 2617543) B2617543
theorem B2326907 : Blo 1837620 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B4137551 : Blo 1837620 4137551 := bstep (se 1 (by rfl) ⟨3103163, by rfl⟩ : syracuseStep 4137551 = 6206327) B6206327
theorem B8954489 : Blo 1837620 8954489 := bstep (se 2 (by rfl) ⟨3357933, by rfl⟩ : syracuseStep 8954489 = 6715867) B6715867
theorem B15704711 : Blo 1837620 15704711 := bstep (se 1 (by rfl) ⟨11778533, by rfl⟩ : syracuseStep 15704711 = 23557067) B23557067
theorem B10470059 : Blo 1837620 10470059 := bstep (se 1 (by rfl) ⟨7852544, by rfl⟩ : syracuseStep 10470059 = 15705089) B15705089
theorem B9437867 : Blo 1837620 9437867 := bstep (se 1 (by rfl) ⟨7078400, by rfl⟩ : syracuseStep 9437867 = 14156801) B14156801
theorem B13959863 : Blo 1837620 13959863 := bstep (se 1 (by rfl) ⟨10469897, by rfl⟩ : syracuseStep 13959863 = 20939795) B20939795
theorem B4137695 : Blo 1837620 4137695 := bstep (se 1 (by rfl) ⟨3103271, by rfl⟩ : syracuseStep 4137695 = 6206543) B6206543
theorem B8840015 : Blo 1837620 8840015 := bstep (se 1 (by rfl) ⟨6630011, by rfl⟩ : syracuseStep 8840015 = 13260023) B13260023
theorem B6202331 : Blo 1837620 6202331 := bstep (se 1 (by rfl) ⟨4651748, by rfl⟩ : syracuseStep 6202331 = 9303497) B9303497
theorem B4137947 : Blo 1837620 4137947 := bstep (se 1 (by rfl) ⟨3103460, by rfl⟩ : syracuseStep 4137947 = 6206921) B6206921
theorem B31400945 : Blo 1837620 31400945 := bstep (se 2 (by rfl) ⟨11775354, by rfl⟩ : syracuseStep 31400945 = 23550709) B23550709
theorem B6202493 : Blo 1837620 6202493 := bstep (se 3 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 6202493 = 2325935) B2325935
theorem B4654219 : Blo 1837620 4654219 := bstep (se 1 (by rfl) ⟨3490664, by rfl⟩ : syracuseStep 4654219 = 6981329) B6981329
theorem B4138127 : Blo 1837620 4138127 := bstep (se 1 (by rfl) ⟨3103595, by rfl⟩ : syracuseStep 4138127 = 6207191) B6207191
theorem B4719815 : Blo 1837620 4719815 := bstep (se 1 (by rfl) ⟨3539861, by rfl⟩ : syracuseStep 4719815 = 7079723) B7079723
theorem B6202601 : Blo 1837620 6202601 := bstep (se 2 (by rfl) ⟨2325975, by rfl⟩ : syracuseStep 6202601 = 4651951) B4651951
theorem B4138217 : Blo 1837620 4138217 := bstep (se 2 (by rfl) ⟨1551831, by rfl⟩ : syracuseStep 4138217 = 3103663) B3103663
theorem B9307385 : Blo 1837620 9307385 := bstep (se 2 (by rfl) ⟨3490269, by rfl⟩ : syracuseStep 9307385 = 6980539) B6980539
theorem B4138271 : Blo 1837620 4138271 := bstep (se 1 (by rfl) ⟨3103703, by rfl⟩ : syracuseStep 4138271 = 6207407) B6207407
theorem B4367753 : Blo 1837620 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B6202763 : Blo 1837620 6202763 := bstep (se 1 (by rfl) ⟨4652072, by rfl⟩ : syracuseStep 6202763 = 9304145) B9304145
theorem B6981025 : Blo 1837620 6981025 := bstep (se 2 (by rfl) ⟨2617884, by rfl⟩ : syracuseStep 6981025 = 5235769) B5235769
theorem B4654523 : Blo 1837620 4654523 := bstep (se 1 (by rfl) ⟨3490892, by rfl⟩ : syracuseStep 4654523 = 6981785) B6981785
theorem B5236157 : Blo 1837620 5236157 := bstep (se 3 (by rfl) ⟨981779, by rfl⟩ : syracuseStep 5236157 = 1963559) B1963559
theorem B16778785 : Blo 1837620 16778785 := bstep (se 2 (by rfl) ⟨6292044, by rfl⟩ : syracuseStep 16778785 = 12584089) B12584089
theorem B12576313 : Blo 1837620 12576313 := bstep (se 2 (by rfl) ⟨4716117, by rfl⟩ : syracuseStep 12576313 = 9432235) B9432235
theorem B3491515 : Blo 1837620 3491515 := bstep (se 1 (by rfl) ⟨2618636, by rfl⟩ : syracuseStep 3491515 = 5237273) B5237273
theorem B13969097 : Blo 1837620 13969097 := bstep (se 2 (by rfl) ⟨5238411, by rfl⟩ : syracuseStep 13969097 = 10476823) B10476823
theorem B4138793 : Blo 1837620 4138793 := bstep (se 2 (by rfl) ⟨1552047, by rfl⟩ : syracuseStep 4138793 = 3104095) B3104095
theorem B56624939 : Blo 1837620 56624939 := bstep (se 1 (by rfl) ⟨42468704, by rfl⟩ : syracuseStep 56624939 = 84937409) B84937409
theorem B23562191 : Blo 1837620 23562191 := bstep (se 1 (by rfl) ⟨17671643, by rfl⟩ : syracuseStep 23562191 = 35343287) B35343287
theorem B1837631 : Blo 1837620 1837631 := bstep (se 1 (by rfl) ⟨1378223, by rfl⟩ : syracuseStep 1837631 = 2756447) B2756447
theorem B1837639 : Blo 1837620 1837639 := bstep (se 1 (by rfl) ⟨1378229, by rfl⟩ : syracuseStep 1837639 = 2756459) B2756459
theorem B13961807 : Blo 1837620 13961807 := bstep (se 1 (by rfl) ⟨10471355, by rfl⟩ : syracuseStep 13961807 = 20942711) B20942711
theorem B8383171 : Blo 1837620 8383171 := bstep (se 1 (by rfl) ⟨6287378, by rfl⟩ : syracuseStep 8383171 = 12574757) B12574757
theorem B134154953 : Blo 1837620 134154953 := bstep (se 2 (by rfl) ⟨50308107, by rfl⟩ : syracuseStep 134154953 = 100616215) B100616215
theorem B19655389 : Blo 1837620 19655389 := bstep (se 3 (by rfl) ⟨3685385, by rfl⟩ : syracuseStep 19655389 = 7370771) B7370771
theorem B1837791 : Blo 1837620 1837791 := bstep (se 1 (by rfl) ⟨1378343, by rfl⟩ : syracuseStep 1837791 = 2756687) B2756687
theorem B4655839 : Blo 1837620 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B1837871 : Blo 1837620 1837871 := bstep (se 1 (by rfl) ⟨1378403, by rfl⟩ : syracuseStep 1837871 = 2756807) B2756807
theorem B4655951 : Blo 1837620 4655951 := bstep (se 1 (by rfl) ⟨3491963, by rfl⟩ : syracuseStep 4655951 = 6983927) B6983927
theorem B3189583 : Blo 1837620 3189583 := bstep (se 1 (by rfl) ⟨2392187, by rfl⟩ : syracuseStep 3189583 = 4784375) B4784375
theorem B1837979 : Blo 1837620 1837979 := bstep (se 1 (by rfl) ⟨1378484, by rfl⟩ : syracuseStep 1837979 = 2756969) B2756969
theorem B1838031 : Blo 1837620 1838031 := bstep (se 1 (by rfl) ⟨1378523, by rfl⟩ : syracuseStep 1838031 = 2757047) B2757047
theorem B1838055 : Blo 1837620 1838055 := bstep (se 1 (by rfl) ⟨1378541, by rfl⟩ : syracuseStep 1838055 = 2757083) B2757083
theorem B1838367 : Blo 1837620 1838367 := bstep (se 1 (by rfl) ⟨1378775, by rfl⟩ : syracuseStep 1838367 = 2757551) B2757551
theorem B5238047 : Blo 1837620 5238047 := bstep (se 1 (by rfl) ⟨3928535, by rfl⟩ : syracuseStep 5238047 = 7857071) B7857071
theorem B7458115 : Blo 1837620 7458115 := bstep (se 1 (by rfl) ⟨5593586, by rfl⟩ : syracuseStep 7458115 = 11187173) B11187173
theorem B1838427 : Blo 1837620 1838427 := bstep (se 1 (by rfl) ⟨1378820, by rfl⟩ : syracuseStep 1838427 = 2757641) B2757641
theorem B4418911 : Blo 1837620 4418911 := bstep (se 1 (by rfl) ⟨3314183, by rfl⟩ : syracuseStep 4418911 = 6628367) B6628367
theorem B1838447 : Blo 1837620 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B2067835 : Blo 1837620 2067835 := bstep (se 1 (by rfl) ⟨1550876, by rfl⟩ : syracuseStep 2067835 = 3101753) B3101753
theorem B1838503 : Blo 1837620 1838503 := bstep (se 1 (by rfl) ⟨1378877, by rfl⟩ : syracuseStep 1838503 = 2757755) B2757755
theorem B7851451 : Blo 1837620 7851451 := bstep (se 1 (by rfl) ⟨5888588, by rfl⟩ : syracuseStep 7851451 = 11777177) B11777177
theorem B3927545 : Blo 1837620 3927545 := bstep (se 2 (by rfl) ⟨1472829, by rfl⟩ : syracuseStep 3927545 = 2945659) B2945659
theorem B1838587 : Blo 1837620 1838587 := bstep (se 1 (by rfl) ⟨1378940, by rfl⟩ : syracuseStep 1838587 = 2757881) B2757881
theorem B1838655 : Blo 1837620 1838655 := bstep (se 1 (by rfl) ⟨1378991, by rfl⟩ : syracuseStep 1838655 = 2757983) B2757983
theorem B1838663 : Blo 1837620 1838663 := bstep (se 1 (by rfl) ⟨1378997, by rfl⟩ : syracuseStep 1838663 = 2757995) B2757995
theorem B3927647 : Blo 1837620 3927647 := bstep (se 1 (by rfl) ⟨2945735, by rfl⟩ : syracuseStep 3927647 = 5891471) B5891471
theorem B19877575 : Blo 1837620 19877575 := bstep (se 1 (by rfl) ⟨14908181, by rfl⟩ : syracuseStep 19877575 = 29816363) B29816363
theorem B1838815 : Blo 1837620 1838815 := bstep (se 1 (by rfl) ⟨1379111, by rfl⟩ : syracuseStep 1838815 = 2758223) B2758223
theorem B2944775 : Blo 1837620 2944775 := bstep (se 1 (by rfl) ⟨2208581, by rfl⟩ : syracuseStep 2944775 = 4417163) B4417163
theorem B4419335 : Blo 1837620 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B1838895 : Blo 1837620 1838895 := bstep (se 1 (by rfl) ⟨1379171, by rfl⟩ : syracuseStep 1838895 = 2758343) B2758343
theorem B84889397 : Blo 1837620 84889397 := bstep (se 5 (by rfl) ⟨3979190, by rfl⟩ : syracuseStep 84889397 = 7958381) B7958381
theorem B2068303 : Blo 1837620 2068303 := bstep (se 1 (by rfl) ⟨1551227, by rfl⟩ : syracuseStep 2068303 = 3102455) B3102455
theorem B1839003 : Blo 1837620 1839003 := bstep (se 1 (by rfl) ⟨1379252, by rfl⟩ : syracuseStep 1839003 = 2758505) B2758505
theorem B1839055 : Blo 1837620 1839055 := bstep (se 1 (by rfl) ⟨1379291, by rfl⟩ : syracuseStep 1839055 = 2758583) B2758583
theorem B1839079 : Blo 1837620 1839079 := bstep (se 1 (by rfl) ⟨1379309, by rfl⟩ : syracuseStep 1839079 = 2758619) B2758619
theorem B13963265 : Blo 1837620 13963265 := bstep (se 2 (by rfl) ⟨5236224, by rfl⟩ : syracuseStep 13963265 = 10472449) B10472449
theorem B8835131 : Blo 1837620 8835131 := bstep (se 1 (by rfl) ⟨6626348, by rfl⟩ : syracuseStep 8835131 = 13252697) B13252697
theorem B2068699 : Blo 1837620 2068699 := bstep (se 1 (by rfl) ⟨1551524, by rfl⟩ : syracuseStep 2068699 = 3103049) B3103049
theorem B2756873 : Blo 1837620 2756873 := bstep (se 2 (by rfl) ⟨1033827, by rfl⟩ : syracuseStep 2756873 = 2067655) B2067655
theorem B13431055 : Blo 1837620 13431055 := bstep (se 1 (by rfl) ⟨10073291, by rfl⟩ : syracuseStep 13431055 = 20146583) B20146583
theorem B1839391 : Blo 1837620 1839391 := bstep (se 1 (by rfl) ⟨1379543, by rfl⟩ : syracuseStep 1839391 = 2759087) B2759087
theorem B6205787 : Blo 1837620 6205787 := bstep (se 1 (by rfl) ⟨4654340, by rfl⟩ : syracuseStep 6205787 = 9308681) B9308681
theorem B1839451 : Blo 1837620 1839451 := bstep (se 1 (by rfl) ⟨1379588, by rfl⟩ : syracuseStep 1839451 = 2759177) B2759177
theorem B2756975 : Blo 1837620 2756975 := bstep (se 1 (by rfl) ⟨2067731, by rfl⟩ : syracuseStep 2756975 = 4135463) B4135463
theorem B1839471 : Blo 1837620 1839471 := bstep (se 1 (by rfl) ⟨1379603, by rfl⟩ : syracuseStep 1839471 = 2759207) B2759207
theorem B42455411 : Blo 1837620 42455411 := bstep (se 1 (by rfl) ⟨31841558, by rfl⟩ : syracuseStep 42455411 = 63683117) B63683117
theorem B1839527 : Blo 1837620 1839527 := bstep (se 1 (by rfl) ⟨1379645, by rfl⟩ : syracuseStep 1839527 = 2759291) B2759291
theorem B19886573 : Blo 1837620 19886573 := bstep (se 3 (by rfl) ⟨3728732, by rfl⟩ : syracuseStep 19886573 = 7457465) B7457465
theorem B3101179 : Blo 1837620 3101179 := bstep (se 1 (by rfl) ⟨2325884, by rfl⟩ : syracuseStep 3101179 = 4651769) B4651769
theorem B2945531 : Blo 1837620 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B2068987 : Blo 1837620 2068987 := bstep (se 1 (by rfl) ⟨1551740, by rfl⟩ : syracuseStep 2068987 = 3103481) B3103481
theorem B1839611 : Blo 1837620 1839611 := bstep (se 1 (by rfl) ⟨1379708, by rfl⟩ : syracuseStep 1839611 = 2759417) B2759417
theorem B16765501 : Blo 1837620 16765501 := bstep (se 3 (by rfl) ⟨3143531, by rfl⟩ : syracuseStep 16765501 = 6287063) B6287063
theorem B2757191 : Blo 1837620 2757191 := bstep (se 1 (by rfl) ⟨2067893, by rfl⟩ : syracuseStep 2757191 = 4135787) B4135787
theorem B2757227 : Blo 1837620 2757227 := bstep (se 1 (by rfl) ⟨2067920, by rfl⟩ : syracuseStep 2757227 = 4135841) B4135841
theorem B7852697 : Blo 1837620 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B2069167 : Blo 1837620 2069167 := bstep (se 1 (by rfl) ⟨1551875, by rfl⟩ : syracuseStep 2069167 = 3103751) B3103751
theorem B2757455 : Blo 1837620 2757455 := bstep (se 1 (by rfl) ⟨2068091, by rfl⟩ : syracuseStep 2757455 = 4136183) B4136183
theorem B3314587 : Blo 1837620 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B3101611 : Blo 1837620 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B2069455 : Blo 1837620 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B35353745 : Blo 1837620 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B3101915 : Blo 1837620 3101915 := bstep (se 1 (by rfl) ⟨2326436, by rfl⟩ : syracuseStep 3101915 = 4652873) B4652873
theorem B2757851 : Blo 1837620 2757851 := bstep (se 1 (by rfl) ⟨2068388, by rfl⟩ : syracuseStep 2757851 = 4136777) B4136777
theorem B15709463 : Blo 1837620 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B9303335 : Blo 1837620 9303335 := bstep (se 1 (by rfl) ⟨6977501, by rfl⟩ : syracuseStep 9303335 = 13955003) B13955003
theorem B6206759 : Blo 1837620 6206759 := bstep (se 1 (by rfl) ⟨4655069, by rfl⟩ : syracuseStep 6206759 = 9310139) B9310139
theorem B9311597 : Blo 1837620 9311597 := bstep (se 3 (by rfl) ⟨1745924, by rfl⟩ : syracuseStep 9311597 = 3491849) B3491849
theorem B2758025 : Blo 1837620 2758025 := bstep (se 2 (by rfl) ⟨1034259, by rfl⟩ : syracuseStep 2758025 = 2068519) B2068519
theorem B3102151 : Blo 1837620 3102151 := bstep (se 1 (by rfl) ⟨2326613, by rfl⟩ : syracuseStep 3102151 = 4653227) B4653227
theorem B2758379 : Blo 1837620 2758379 := bstep (se 1 (by rfl) ⟨2068784, by rfl⟩ : syracuseStep 2758379 = 4137569) B4137569
theorem B4134761 : Blo 1837620 4134761 := bstep (se 2 (by rfl) ⟨1550535, by rfl⟩ : syracuseStep 4134761 = 3101071) B3101071
theorem B3102671 : Blo 1837620 3102671 := bstep (se 1 (by rfl) ⟨2327003, by rfl⟩ : syracuseStep 3102671 = 4654007) B4654007
theorem B2758607 : Blo 1837620 2758607 := bstep (se 1 (by rfl) ⟨2068955, by rfl⟩ : syracuseStep 2758607 = 4137911) B4137911
theorem B6625313 : Blo 1837620 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B35829803 : Blo 1837620 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B5380225 : Blo 1837620 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B6207623 : Blo 1837620 6207623 := bstep (se 1 (by rfl) ⟨4655717, by rfl⟩ : syracuseStep 6207623 = 9311435) B9311435
theorem B1964251 : Blo 1837620 1964251 := bstep (se 1 (by rfl) ⟨1473188, by rfl⟩ : syracuseStep 1964251 = 2946377) B2946377
theorem B10467575 : Blo 1837620 10467575 := bstep (se 1 (by rfl) ⟨7850681, by rfl⟩ : syracuseStep 10467575 = 15701363) B15701363
theorem B75520289 : Blo 1837620 75520289 := bstep (se 2 (by rfl) ⟨28320108, by rfl⟩ : syracuseStep 75520289 = 56640217) B56640217
theorem B2759003 : Blo 1837620 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B13253159 : Blo 1837620 13253159 := bstep (se 1 (by rfl) ⟨9939869, by rfl⟩ : syracuseStep 13253159 = 19879739) B19879739
theorem B38246975 : Blo 1837620 38246975 := bstep (se 1 (by rfl) ⟨28685231, by rfl⟩ : syracuseStep 38246975 = 57370463) B57370463
theorem B2759231 : Blo 1837620 2759231 := bstep (se 1 (by rfl) ⟨2069423, by rfl⟩ : syracuseStep 2759231 = 4138847) B4138847
theorem B4651627 : Blo 1837620 4651627 := bstep (se 1 (by rfl) ⟨3488720, by rfl⟩ : syracuseStep 4651627 = 6977441) B6977441
theorem B3103339 : Blo 1837620 3103339 := bstep (se 1 (by rfl) ⟨2327504, by rfl⟩ : syracuseStep 3103339 = 4655009) B4655009
theorem B4135607 : Blo 1837620 4135607 := bstep (se 1 (by rfl) ⟨3101705, by rfl⟩ : syracuseStep 4135607 = 6203411) B6203411
theorem B2759351 : Blo 1837620 2759351 := bstep (se 1 (by rfl) ⟨2069513, by rfl⟩ : syracuseStep 2759351 = 4139027) B4139027
theorem B4135823 : Blo 1837620 4135823 := bstep (se 1 (by rfl) ⟨3101867, by rfl⟩ : syracuseStep 4135823 = 6203735) B6203735
theorem B4651931 : Blo 1837620 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B3103643 : Blo 1837620 3103643 := bstep (se 1 (by rfl) ⟨2327732, by rfl⟩ : syracuseStep 3103643 = 4655465) B4655465
theorem B3488683 : Blo 1837620 3488683 := bstep (se 1 (by rfl) ⟨2616512, by rfl⟩ : syracuseStep 3488683 = 5233025) B5233025
theorem B286743563 : Blo 1837620 286743563 := bstep (se 1 (by rfl) ⟨215057672, by rfl⟩ : syracuseStep 286743563 = 430115345) B430115345
theorem B9559079 : Blo 1837620 9559079 := bstep (se 1 (by rfl) ⟨7169309, by rfl⟩ : syracuseStep 9559079 = 14338619) B14338619
theorem B3488987 : Blo 1837620 3488987 := bstep (se 1 (by rfl) ⟨2616740, by rfl⟩ : syracuseStep 3488987 = 5233481) B5233481
theorem B19872989 : Blo 1837620 19872989 := bstep (se 3 (by rfl) ⟨3726185, by rfl⟩ : syracuseStep 19872989 = 7452371) B7452371
theorem B4652275 : Blo 1837620 4652275 := bstep (se 1 (by rfl) ⟨3489206, by rfl⟩ : syracuseStep 4652275 = 6978413) B6978413
theorem B14146883 : Blo 1837620 14146883 := bstep (se 1 (by rfl) ⟨10610162, by rfl⟩ : syracuseStep 14146883 = 21220325) B21220325
theorem B4971871 : Blo 1837620 4971871 := bstep (se 1 (by rfl) ⟨3728903, by rfl⟩ : syracuseStep 4971871 = 7457807) B7457807
theorem B9305441 : Blo 1837620 9305441 := bstep (se 2 (by rfl) ⟨3489540, by rfl⟩ : syracuseStep 9305441 = 6979081) B6979081
theorem B12582281 : Blo 1837620 12582281 := bstep (se 2 (by rfl) ⟨4718355, by rfl⟩ : syracuseStep 12582281 = 9436711) B9436711
theorem B2326087 : Blo 1837620 2326087 := bstep (se 1 (by rfl) ⟨1744565, by rfl⟩ : syracuseStep 2326087 = 3489131) B3489131
theorem B4136543 : Blo 1837620 4136543 := bstep (se 1 (by rfl) ⟨3102407, by rfl⟩ : syracuseStep 4136543 = 6204815) B6204815
theorem B2096815 : Blo 1837620 2096815 := bstep (se 1 (by rfl) ⟨1572611, by rfl⟩ : syracuseStep 2096815 = 3145223) B3145223
theorem B7855825 : Blo 1837620 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B14147369 : Blo 1837620 14147369 := bstep (se 2 (by rfl) ⟨5305263, by rfl⟩ : syracuseStep 14147369 = 10610527) B10610527
theorem B4136759 : Blo 1837620 4136759 := bstep (se 1 (by rfl) ⟨3102569, by rfl⟩ : syracuseStep 4136759 = 6205139) B6205139
theorem B6979385 : Blo 1837620 6979385 := bstep (se 2 (by rfl) ⟨2617269, by rfl⟩ : syracuseStep 6979385 = 5234539) B5234539
theorem B5890087 : Blo 1837620 5890087 := bstep (se 1 (by rfl) ⟨4417565, by rfl⟩ : syracuseStep 5890087 = 8835131) B8835131
theorem B9306251 : Blo 1837620 9306251 := bstep (se 1 (by rfl) ⟨6979688, by rfl⟩ : syracuseStep 9306251 = 13959377) B13959377
theorem B4137191 : Blo 1837620 4137191 := bstep (se 1 (by rfl) ⟨3102893, by rfl⟩ : syracuseStep 4137191 = 6205787) B6205787
theorem B28303607 : Blo 1837620 28303607 := bstep (se 1 (by rfl) ⟨21227705, by rfl⟩ : syracuseStep 28303607 = 42455411) B42455411
theorem B4653409 : Blo 1837620 4653409 := bstep (se 2 (by rfl) ⟨1745028, by rfl⟩ : syracuseStep 4653409 = 3490057) B3490057
theorem B17908073 : Blo 1837620 17908073 := bstep (se 2 (by rfl) ⟨6715527, by rfl⟩ : syracuseStep 17908073 = 13431055) B13431055
theorem B10469807 : Blo 1837620 10469807 := bstep (se 1 (by rfl) ⟨7852355, by rfl⟩ : syracuseStep 10469807 = 15704711) B15704711
theorem B5235131 : Blo 1837620 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B6980039 : Blo 1837620 6980039 := bstep (se 1 (by rfl) ⟨5235029, by rfl⟩ : syracuseStep 6980039 = 10470059) B10470059
theorem B6291911 : Blo 1837620 6291911 := bstep (se 1 (by rfl) ⟨4718933, by rfl⟩ : syracuseStep 6291911 = 9437867) B9437867
theorem B9306575 : Blo 1837620 9306575 := bstep (se 1 (by rfl) ⟨6979931, by rfl⟩ : syracuseStep 9306575 = 13959863) B13959863
theorem B13968125 : Blo 1837620 13968125 := bstep (se 3 (by rfl) ⟨2619023, by rfl⟩ : syracuseStep 13968125 = 5238047) B5238047
theorem B23569163 : Blo 1837620 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B3146543 : Blo 1837620 3146543 := bstep (se 1 (by rfl) ⟨2359907, by rfl⟩ : syracuseStep 3146543 = 4719815) B4719815
theorem B6202169 : Blo 1837620 6202169 := bstep (se 2 (by rfl) ⟨2325813, by rfl⟩ : syracuseStep 6202169 = 4651627) B4651627
theorem B4137785 : Blo 1837620 4137785 := bstep (se 2 (by rfl) ⟨1551669, by rfl⟩ : syracuseStep 4137785 = 3103339) B3103339
theorem B6202223 : Blo 1837620 6202223 := bstep (se 1 (by rfl) ⟨4651667, by rfl⟩ : syracuseStep 6202223 = 9303335) B9303335
theorem B4137839 : Blo 1837620 4137839 := bstep (se 1 (by rfl) ⟨3103379, by rfl⟩ : syracuseStep 4137839 = 6206759) B6206759
theorem B3490771 : Blo 1837620 3490771 := bstep (se 1 (by rfl) ⟨2618078, by rfl⟩ : syracuseStep 3490771 = 5236157) B5236157
theorem B37749959 : Blo 1837620 37749959 := bstep (se 1 (by rfl) ⟨28312469, by rfl⟩ : syracuseStep 37749959 = 56624939) B56624939
theorem B4416875 : Blo 1837620 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B4138415 : Blo 1837620 4138415 := bstep (se 1 (by rfl) ⟨3103811, by rfl⟩ : syracuseStep 4138415 = 6207623) B6207623
theorem B6203033 : Blo 1837620 6203033 := bstep (se 2 (by rfl) ⟨2326137, by rfl⟩ : syracuseStep 6203033 = 4652275) B4652275
theorem B9307871 : Blo 1837620 9307871 := bstep (se 1 (by rfl) ⟨6980903, by rfl⟩ : syracuseStep 9307871 = 13961807) B13961807
theorem B5891881 : Blo 1837620 5891881 := bstep (se 2 (by rfl) ⟨2209455, by rfl⟩ : syracuseStep 5891881 = 4418911) B4418911
theorem B9308033 : Blo 1837620 9308033 := bstep (se 2 (by rfl) ⟨3490512, by rfl⟩ : syracuseStep 9308033 = 6981025) B6981025
theorem B191162375 : Blo 1837620 191162375 := bstep (se 1 (by rfl) ⟨143371781, by rfl⟩ : syracuseStep 191162375 = 286743563) B286743563
theorem B13248659 : Blo 1837620 13248659 := bstep (se 1 (by rfl) ⟨9936494, by rfl⟩ : syracuseStep 13248659 = 19872989) B19872989
theorem B9431255 : Blo 1837620 9431255 := bstep (se 1 (by rfl) ⟨7073441, by rfl⟩ : syracuseStep 9431255 = 14146883) B14146883
theorem B2795753 : Blo 1837620 2795753 := bstep (se 2 (by rfl) ⟨1048407, by rfl⟩ : syracuseStep 2795753 = 2096815) B2096815
theorem B6203627 : Blo 1837620 6203627 := bstep (se 1 (by rfl) ⟨4652720, by rfl⟩ : syracuseStep 6203627 = 9305441) B9305441
theorem B4655353 : Blo 1837620 4655353 := bstep (se 2 (by rfl) ⟨1745757, by rfl⟩ : syracuseStep 4655353 = 3491515) B3491515
theorem B26503433 : Blo 1837620 26503433 := bstep (se 2 (by rfl) ⟨9938787, by rfl⟩ : syracuseStep 26503433 = 19877575) B19877575
theorem B9431579 : Blo 1837620 9431579 := bstep (se 1 (by rfl) ⟨7073684, by rfl⟩ : syracuseStep 9431579 = 14147369) B14147369
theorem B56592931 : Blo 1837620 56592931 := bstep (se 1 (by rfl) ⟨42444698, by rfl⟩ : syracuseStep 56592931 = 84889397) B84889397
theorem B9308843 : Blo 1837620 9308843 := bstep (se 1 (by rfl) ⟨6981632, by rfl⟩ : syracuseStep 9308843 = 13963265) B13963265
theorem B47754035 : Blo 1837620 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1837915 : Blo 1837620 1837915 := bstep (se 1 (by rfl) ⟨1378436, by rfl⟩ : syracuseStep 1837915 = 2756873) B2756873
theorem B1837983 : Blo 1837620 1837983 := bstep (se 1 (by rfl) ⟨1378487, by rfl⟩ : syracuseStep 1837983 = 2756975) B2756975
theorem B13257715 : Blo 1837620 13257715 := bstep (se 1 (by rfl) ⟨9943286, by rfl⟩ : syracuseStep 13257715 = 19886573) B19886573
theorem B1838127 : Blo 1837620 1838127 := bstep (se 1 (by rfl) ⟨1378595, by rfl⟩ : syracuseStep 1838127 = 2757191) B2757191
theorem B1838151 : Blo 1837620 1838151 := bstep (se 1 (by rfl) ⟨1378613, by rfl⟩ : syracuseStep 1838151 = 2757227) B2757227
theorem B1838303 : Blo 1837620 1838303 := bstep (se 1 (by rfl) ⟨1378727, by rfl⟩ : syracuseStep 1838303 = 2757455) B2757455
theorem B5893343 : Blo 1837620 5893343 := bstep (se 1 (by rfl) ⟨4420007, by rfl⟩ : syracuseStep 5893343 = 8840015) B8840015
theorem B20933963 : Blo 1837620 20933963 := bstep (se 1 (by rfl) ⟨15700472, by rfl⟩ : syracuseStep 20933963 = 31400945) B31400945
theorem B2067943 : Blo 1837620 2067943 := bstep (se 1 (by rfl) ⟨1550957, by rfl⟩ : syracuseStep 2067943 = 3101915) B3101915
theorem B1838567 : Blo 1837620 1838567 := bstep (se 1 (by rfl) ⟨1378925, by rfl⟩ : syracuseStep 1838567 = 2757851) B2757851
theorem B6204923 : Blo 1837620 6204923 := bstep (se 1 (by rfl) ⟨4653692, by rfl⟩ : syracuseStep 6204923 = 9307385) B9307385
theorem B10472975 : Blo 1837620 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B11177561 : Blo 1837620 11177561 := bstep (se 2 (by rfl) ⟨4191585, by rfl⟩ : syracuseStep 11177561 = 8383171) B8383171
theorem B1838683 : Blo 1837620 1838683 := bstep (se 1 (by rfl) ⟨1379012, by rfl⟩ : syracuseStep 1838683 = 2758025) B2758025
theorem B2911835 : Blo 1837620 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B6205085 : Blo 1837620 6205085 := bstep (se 3 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 6205085 = 2326907) B2326907
theorem B104828741 : Blo 1837620 104828741 := bstep (se 4 (by rfl) ⟨9827694, by rfl⟩ : syracuseStep 104828741 = 19655389) B19655389
theorem B1838919 : Blo 1837620 1838919 := bstep (se 1 (by rfl) ⟨1379189, by rfl⟩ : syracuseStep 1838919 = 2758379) B2758379
theorem B4419449 : Blo 1837620 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B2756507 : Blo 1837620 2756507 := bstep (se 1 (by rfl) ⟨2067380, by rfl⟩ : syracuseStep 2756507 = 4134761) B4134761
theorem B2068447 : Blo 1837620 2068447 := bstep (se 1 (by rfl) ⟨1551335, by rfl⟩ : syracuseStep 2068447 = 3102671) B3102671
theorem B15708127 : Blo 1837620 15708127 := bstep (se 1 (by rfl) ⟨11781095, by rfl⟩ : syracuseStep 15708127 = 23562191) B23562191
theorem B1839071 : Blo 1837620 1839071 := bstep (se 1 (by rfl) ⟨1379303, by rfl⟩ : syracuseStep 1839071 = 2758607) B2758607
theorem B6205625 : Blo 1837620 6205625 := bstep (se 2 (by rfl) ⟨2327109, by rfl⟩ : syracuseStep 6205625 = 4654219) B4654219
theorem B1839335 : Blo 1837620 1839335 := bstep (se 1 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 1839335 = 2759003) B2759003
theorem B10473725 : Blo 1837620 10473725 := bstep (se 3 (by rfl) ⟨1963823, by rfl⟩ : syracuseStep 10473725 = 3927647) B3927647
theorem B8835439 : Blo 1837620 8835439 := bstep (se 1 (by rfl) ⟨6626579, by rfl⟩ : syracuseStep 8835439 = 13253159) B13253159
theorem B25497983 : Blo 1837620 25497983 := bstep (se 1 (by rfl) ⟨19123487, by rfl⟩ : syracuseStep 25497983 = 38246975) B38246975
theorem B1839487 : Blo 1837620 1839487 := bstep (se 1 (by rfl) ⟨1379615, by rfl⟩ : syracuseStep 1839487 = 2759231) B2759231
theorem B17011109 : Blo 1837620 17011109 := bstep (se 4 (by rfl) ⟨1594791, by rfl⟩ : syracuseStep 17011109 = 3189583) B3189583
theorem B2757071 : Blo 1837620 2757071 := bstep (se 1 (by rfl) ⟨2067803, by rfl⟩ : syracuseStep 2757071 = 4135607) B4135607
theorem B1839567 : Blo 1837620 1839567 := bstep (se 1 (by rfl) ⟨1379675, by rfl⟩ : syracuseStep 1839567 = 2759351) B2759351
theorem B89436635 : Blo 1837620 89436635 := bstep (se 1 (by rfl) ⟨67077476, by rfl⟩ : syracuseStep 89436635 = 134154953) B134154953
theorem B2757113 : Blo 1837620 2757113 := bstep (se 2 (by rfl) ⟨1033917, by rfl⟩ : syracuseStep 2757113 = 2067835) B2067835
theorem B2757215 : Blo 1837620 2757215 := bstep (se 1 (by rfl) ⟨2067911, by rfl⟩ : syracuseStep 2757215 = 4135823) B4135823
theorem B3101287 : Blo 1837620 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B2069095 : Blo 1837620 2069095 := bstep (se 1 (by rfl) ⟨1551821, by rfl⟩ : syracuseStep 2069095 = 3103643) B3103643
theorem B7852733 : Blo 1837620 7852733 := bstep (se 3 (by rfl) ⟨1472387, by rfl⟩ : syracuseStep 7852733 = 2944775) B2944775
theorem B3101449 : Blo 1837620 3101449 := bstep (se 2 (by rfl) ⟨1163043, by rfl⟩ : syracuseStep 3101449 = 2326087) B2326087
theorem B10474433 : Blo 1837620 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B2618363 : Blo 1837620 2618363 := bstep (se 1 (by rfl) ⟨1963772, by rfl⟩ : syracuseStep 2618363 = 3927545) B3927545
theorem B2757695 : Blo 1837620 2757695 := bstep (se 1 (by rfl) ⟨2068271, by rfl⟩ : syracuseStep 2757695 = 4136543) B4136543
theorem B2757737 : Blo 1837620 2757737 := bstep (se 2 (by rfl) ⟨1034151, by rfl⟩ : syracuseStep 2757737 = 2068303) B2068303
theorem B2946223 : Blo 1837620 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B2757839 : Blo 1837620 2757839 := bstep (se 1 (by rfl) ⟨2068379, by rfl⟩ : syracuseStep 2757839 = 4136759) B4136759
theorem B3102043 : Blo 1837620 3102043 := bstep (se 1 (by rfl) ⟨2326532, by rfl⟩ : syracuseStep 3102043 = 4653065) B4653065
theorem B2758043 : Blo 1837620 2758043 := bstep (se 1 (by rfl) ⟨2068532, by rfl⟩ : syracuseStep 2758043 = 4137065) B4137065
theorem B2758265 : Blo 1837620 2758265 := bstep (se 2 (by rfl) ⟨1034349, by rfl⟩ : syracuseStep 2758265 = 2068699) B2068699
theorem B2619001 : Blo 1837620 2619001 := bstep (se 2 (by rfl) ⟨982125, by rfl⟩ : syracuseStep 2619001 = 1964251) B1964251
theorem B67073669 : Blo 1837620 67073669 := bstep (se 4 (by rfl) ⟨6288156, by rfl⟩ : syracuseStep 67073669 = 12576313) B12576313
theorem B1963687 : Blo 1837620 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B2758367 : Blo 1837620 2758367 := bstep (se 1 (by rfl) ⟨2068775, by rfl⟩ : syracuseStep 2758367 = 4137551) B4137551
theorem B5969659 : Blo 1837620 5969659 := bstep (se 1 (by rfl) ⟨4477244, by rfl⟩ : syracuseStep 5969659 = 8954489) B8954489
theorem B2758463 : Blo 1837620 2758463 := bstep (se 1 (by rfl) ⟨2068847, by rfl⟩ : syracuseStep 2758463 = 4137695) B4137695
theorem B4134887 : Blo 1837620 4134887 := bstep (se 1 (by rfl) ⟨3101165, by rfl⟩ : syracuseStep 4134887 = 6202331) B6202331
theorem B2758631 : Blo 1837620 2758631 := bstep (se 1 (by rfl) ⟨2068973, by rfl⟩ : syracuseStep 2758631 = 4137947) B4137947
theorem B4134905 : Blo 1837620 4134905 := bstep (se 2 (by rfl) ⟨1550589, by rfl⟩ : syracuseStep 4134905 = 3101179) B3101179
theorem B2758649 : Blo 1837620 2758649 := bstep (se 2 (by rfl) ⟨1034493, by rfl⟩ : syracuseStep 2758649 = 2068987) B2068987
theorem B28694533 : Blo 1837620 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B22354001 : Blo 1837620 22354001 := bstep (se 2 (by rfl) ⟨8382750, by rfl⟩ : syracuseStep 22354001 = 16765501) B16765501
theorem B4134995 : Blo 1837620 4134995 := bstep (se 1 (by rfl) ⟨3101246, by rfl⟩ : syracuseStep 4134995 = 6202493) B6202493
theorem B2758751 : Blo 1837620 2758751 := bstep (se 1 (by rfl) ⟨2069063, by rfl⟩ : syracuseStep 2758751 = 4138127) B4138127
theorem B4135067 : Blo 1837620 4135067 := bstep (se 1 (by rfl) ⟨3101300, by rfl⟩ : syracuseStep 4135067 = 6202601) B6202601
theorem B2758811 : Blo 1837620 2758811 := bstep (se 1 (by rfl) ⟨2069108, by rfl⟩ : syracuseStep 2758811 = 4138217) B4138217
theorem B2758847 : Blo 1837620 2758847 := bstep (se 1 (by rfl) ⟨2069135, by rfl⟩ : syracuseStep 2758847 = 4138271) B4138271
theorem B2758889 : Blo 1837620 2758889 := bstep (se 2 (by rfl) ⟨1034583, by rfl⟩ : syracuseStep 2758889 = 2069167) B2069167
theorem B6207731 : Blo 1837620 6207731 := bstep (se 1 (by rfl) ⟨4655798, by rfl⟩ : syracuseStep 6207731 = 9311597) B9311597
theorem B4135175 : Blo 1837620 4135175 := bstep (se 1 (by rfl) ⟨3101381, by rfl⟩ : syracuseStep 4135175 = 6202763) B6202763
theorem B3103015 : Blo 1837620 3103015 := bstep (se 1 (by rfl) ⟨2327261, by rfl⟩ : syracuseStep 3103015 = 4654523) B4654523
theorem B6207785 : Blo 1837620 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B33552749 : Blo 1837620 33552749 := bstep (se 3 (by rfl) ⟨6291140, by rfl⟩ : syracuseStep 33552749 = 12582281) B12582281
theorem B9312731 : Blo 1837620 9312731 := bstep (se 1 (by rfl) ⟨6984548, by rfl⟩ : syracuseStep 9312731 = 13969097) B13969097
theorem B2759195 : Blo 1837620 2759195 := bstep (se 1 (by rfl) ⟨2069396, by rfl⟩ : syracuseStep 2759195 = 4138793) B4138793
theorem B4651577 : Blo 1837620 4651577 := bstep (se 2 (by rfl) ⟨1744341, by rfl⟩ : syracuseStep 4651577 = 3488683) B3488683
theorem B4135481 : Blo 1837620 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B2759273 : Blo 1837620 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B23886535 : Blo 1837620 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B6978383 : Blo 1837620 6978383 := bstep (se 1 (by rfl) ⟨5233787, by rfl⟩ : syracuseStep 6978383 = 10467575) B10467575
theorem B50346859 : Blo 1837620 50346859 := bstep (se 1 (by rfl) ⟨37760144, by rfl⟩ : syracuseStep 50346859 = 75520289) B75520289
theorem B9944153 : Blo 1837620 9944153 := bstep (se 2 (by rfl) ⟨3729057, by rfl⟩ : syracuseStep 9944153 = 7458115) B7458115
theorem B26516645 : Blo 1837620 26516645 := bstep (se 4 (by rfl) ⟨2485935, by rfl⟩ : syracuseStep 26516645 = 4971871) B4971871
theorem B3103967 : Blo 1837620 3103967 := bstep (se 1 (by rfl) ⟨2327975, by rfl⟩ : syracuseStep 3103967 = 4655951) B4655951
theorem B10468601 : Blo 1837620 10468601 := bstep (se 2 (by rfl) ⟨3925725, by rfl⟩ : syracuseStep 10468601 = 7851451) B7851451
theorem B4136201 : Blo 1837620 4136201 := bstep (se 2 (by rfl) ⟨1551075, by rfl⟩ : syracuseStep 4136201 = 3102151) B3102151
theorem B6372719 : Blo 1837620 6372719 := bstep (se 1 (by rfl) ⟨4779539, by rfl⟩ : syracuseStep 6372719 = 9559079) B9559079
theorem B22371713 : Blo 1837620 22371713 := bstep (se 2 (by rfl) ⟨8389392, by rfl⟩ : syracuseStep 22371713 = 16778785) B16778785
theorem B2325991 : Blo 1837620 2325991 := bstep (se 1 (by rfl) ⟨1744493, by rfl⟩ : syracuseStep 2325991 = 3488987) B3488987
theorem B4652923 : Blo 1837620 4652923 := bstep (se 1 (by rfl) ⟨3489692, by rfl⟩ : syracuseStep 4652923 = 6979385) B6979385
theorem B4137083 : Blo 1837620 4137083 := bstep (se 1 (by rfl) ⟨3102812, by rfl⟩ : syracuseStep 4137083 = 6205625) B6205625
theorem B16998655 : Blo 1837620 16998655 := bstep (se 1 (by rfl) ⟨12748991, by rfl⟩ : syracuseStep 16998655 = 25497983) B25497983
theorem B6979871 : Blo 1837620 6979871 := bstep (se 1 (by rfl) ⟨5234903, by rfl⟩ : syracuseStep 6979871 = 10469807) B10469807
theorem B4653359 : Blo 1837620 4653359 := bstep (se 1 (by rfl) ⟨3490019, by rfl⟩ : syracuseStep 4653359 = 6980039) B6980039
theorem B4194607 : Blo 1837620 4194607 := bstep (se 1 (by rfl) ⟨3145955, by rfl⟩ : syracuseStep 4194607 = 6291911) B6291911
theorem B4137353 : Blo 1837620 4137353 := bstep (se 2 (by rfl) ⟨1551507, by rfl⟩ : syracuseStep 4137353 = 3103015) B3103015
theorem B5235155 : Blo 1837620 5235155 := bstep (se 1 (by rfl) ⟨3926366, by rfl⟩ : syracuseStep 5235155 = 7852733) B7852733
theorem B11780585 : Blo 1837620 11780585 := bstep (se 2 (by rfl) ⟨4417719, by rfl⟩ : syracuseStep 11780585 = 8835439) B8835439
theorem B15712775 : Blo 1837620 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B2097695 : Blo 1837620 2097695 := bstep (se 1 (by rfl) ⟨1573271, by rfl⟩ : syracuseStep 2097695 = 3146543) B3146543
theorem B7455341 : Blo 1837620 7455341 := bstep (se 3 (by rfl) ⟨1397876, by rfl⟩ : syracuseStep 7455341 = 2795753) B2795753
theorem B75457241 : Blo 1837620 75457241 := bstep (se 2 (by rfl) ⟨28296465, by rfl⟩ : syracuseStep 75457241 = 56592931) B56592931
theorem B25166639 : Blo 1837620 25166639 := bstep (se 1 (by rfl) ⟨18874979, by rfl⟩ : syracuseStep 25166639 = 37749959) B37749959
theorem B89473997 : Blo 1837620 89473997 := bstep (se 3 (by rfl) ⟨16776374, by rfl⟩ : syracuseStep 89473997 = 33552749) B33552749
theorem B13960349 : Blo 1837620 13960349 := bstep (se 3 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 13960349 = 5235131) B5235131
theorem B4654361 : Blo 1837620 4654361 := bstep (se 2 (by rfl) ⟨1745385, by rfl⟩ : syracuseStep 4654361 = 3490771) B3490771
theorem B14902667 : Blo 1837620 14902667 := bstep (se 1 (by rfl) ⟨11177000, by rfl⟩ : syracuseStep 14902667 = 22354001) B22354001
theorem B25150877 : Blo 1837620 25150877 := bstep (se 3 (by rfl) ⟨4715789, by rfl⟩ : syracuseStep 25150877 = 9431579) B9431579
theorem B8832439 : Blo 1837620 8832439 := bstep (se 1 (by rfl) ⟨6624329, by rfl⟩ : syracuseStep 8832439 = 13248659) B13248659
theorem B4138487 : Blo 1837620 4138487 := bstep (se 1 (by rfl) ⟨3103865, by rfl⟩ : syracuseStep 4138487 = 6207731) B6207731
theorem B4138523 : Blo 1837620 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B31836023 : Blo 1837620 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B6629435 : Blo 1837620 6629435 := bstep (se 1 (by rfl) ⟨4972076, by rfl⟩ : syracuseStep 6629435 = 9944153) B9944153
theorem B3492001 : Blo 1837620 3492001 := bstep (se 2 (by rfl) ⟨1309500, by rfl⟩ : syracuseStep 3492001 = 2619001) B2619001
theorem B6981983 : Blo 1837620 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B6203897 : Blo 1837620 6203897 := bstep (se 2 (by rfl) ⟨2326461, by rfl⟩ : syracuseStep 6203897 = 4652923) B4652923
theorem B1837671 : Blo 1837620 1837671 := bstep (se 1 (by rfl) ⟨1378253, by rfl⟩ : syracuseStep 1837671 = 2756507) B2756507
theorem B6982301 : Blo 1837620 6982301 := bstep (se 3 (by rfl) ⟨1309181, by rfl⟩ : syracuseStep 6982301 = 2618363) B2618363
theorem B38259377 : Blo 1837620 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B6204167 : Blo 1837620 6204167 := bstep (se 1 (by rfl) ⟨4653125, by rfl⟩ : syracuseStep 6204167 = 9306251) B9306251
theorem B18869071 : Blo 1837620 18869071 := bstep (se 1 (by rfl) ⟨14151803, by rfl⟩ : syracuseStep 18869071 = 28303607) B28303607
theorem B6982483 : Blo 1837620 6982483 := bstep (se 1 (by rfl) ⟨5236862, by rfl⟩ : syracuseStep 6982483 = 10473725) B10473725
theorem B11938715 : Blo 1837620 11938715 := bstep (se 1 (by rfl) ⟨8954036, by rfl⟩ : syracuseStep 11938715 = 17908073) B17908073
theorem B11340739 : Blo 1837620 11340739 := bstep (se 1 (by rfl) ⟨8505554, by rfl⟩ : syracuseStep 11340739 = 17011109) B17011109
theorem B1838047 : Blo 1837620 1838047 := bstep (se 1 (by rfl) ⟨1378535, by rfl⟩ : syracuseStep 1838047 = 2757071) B2757071
theorem B6204383 : Blo 1837620 6204383 := bstep (se 1 (by rfl) ⟨4653287, by rfl⟩ : syracuseStep 6204383 = 9306575) B9306575
theorem B59624423 : Blo 1837620 59624423 := bstep (se 1 (by rfl) ⟨44718317, by rfl⟩ : syracuseStep 59624423 = 89436635) B89436635
theorem B1838075 : Blo 1837620 1838075 := bstep (se 1 (by rfl) ⟨1378556, by rfl⟩ : syracuseStep 1838075 = 2757113) B2757113
theorem B1838143 : Blo 1837620 1838143 := bstep (se 1 (by rfl) ⟨1378607, by rfl⟩ : syracuseStep 1838143 = 2757215) B2757215
theorem B6204545 : Blo 1837620 6204545 := bstep (se 2 (by rfl) ⟨2326704, by rfl⟩ : syracuseStep 6204545 = 4653409) B4653409
theorem B6982955 : Blo 1837620 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B1838463 : Blo 1837620 1838463 := bstep (se 1 (by rfl) ⟨1378847, by rfl⟩ : syracuseStep 1838463 = 2757695) B2757695
theorem B1838491 : Blo 1837620 1838491 := bstep (se 1 (by rfl) ⟨1378868, by rfl⟩ : syracuseStep 1838491 = 2757737) B2757737
theorem B1838559 : Blo 1837620 1838559 := bstep (se 1 (by rfl) ⟨1378919, by rfl⟩ : syracuseStep 1838559 = 2757839) B2757839
theorem B2944583 : Blo 1837620 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B1838695 : Blo 1837620 1838695 := bstep (se 1 (by rfl) ⟨1379021, by rfl⟩ : syracuseStep 1838695 = 2758043) B2758043
theorem B1838843 : Blo 1837620 1838843 := bstep (se 1 (by rfl) ⟨1379132, by rfl⟩ : syracuseStep 1838843 = 2758265) B2758265
theorem B44715779 : Blo 1837620 44715779 := bstep (se 1 (by rfl) ⟨33536834, by rfl⟩ : syracuseStep 44715779 = 67073669) B67073669
theorem B67129145 : Blo 1837620 67129145 := bstep (se 2 (by rfl) ⟨25173429, by rfl⟩ : syracuseStep 67129145 = 50346859) B50346859
theorem B6205247 : Blo 1837620 6205247 := bstep (se 1 (by rfl) ⟨4653935, by rfl⟩ : syracuseStep 6205247 = 9307871) B9307871
theorem B1838911 : Blo 1837620 1838911 := bstep (se 1 (by rfl) ⟨1379183, by rfl⟩ : syracuseStep 1838911 = 2758367) B2758367
theorem B1838975 : Blo 1837620 1838975 := bstep (se 1 (by rfl) ⟨1379231, by rfl⟩ : syracuseStep 1838975 = 2758463) B2758463
theorem B6205355 : Blo 1837620 6205355 := bstep (se 1 (by rfl) ⟨4654016, by rfl⟩ : syracuseStep 6205355 = 9308033) B9308033
theorem B2756591 : Blo 1837620 2756591 := bstep (se 1 (by rfl) ⟨2067443, by rfl⟩ : syracuseStep 2756591 = 4134887) B4134887
theorem B1839087 : Blo 1837620 1839087 := bstep (se 1 (by rfl) ⟨1379315, by rfl⟩ : syracuseStep 1839087 = 2758631) B2758631
theorem B2756603 : Blo 1837620 2756603 := bstep (se 1 (by rfl) ⟨2067452, by rfl⟩ : syracuseStep 2756603 = 4134905) B4134905
theorem B1839099 : Blo 1837620 1839099 := bstep (se 1 (by rfl) ⟨1379324, by rfl⟩ : syracuseStep 1839099 = 2758649) B2758649
theorem B2756663 : Blo 1837620 2756663 := bstep (se 1 (by rfl) ⟨2067497, by rfl⟩ : syracuseStep 2756663 = 4134995) B4134995
theorem B1839167 : Blo 1837620 1839167 := bstep (se 1 (by rfl) ⟨1379375, by rfl⟩ : syracuseStep 1839167 = 2758751) B2758751
theorem B2756711 : Blo 1837620 2756711 := bstep (se 1 (by rfl) ⟨2067533, by rfl⟩ : syracuseStep 2756711 = 4135067) B4135067
theorem B1839207 : Blo 1837620 1839207 := bstep (se 1 (by rfl) ⟨1379405, by rfl⟩ : syracuseStep 1839207 = 2758811) B2758811
theorem B1839231 : Blo 1837620 1839231 := bstep (se 1 (by rfl) ⟨1379423, by rfl⟩ : syracuseStep 1839231 = 2758847) B2758847
theorem B6287503 : Blo 1837620 6287503 := bstep (se 1 (by rfl) ⟨4715627, by rfl⟩ : syracuseStep 6287503 = 9431255) B9431255
theorem B1839259 : Blo 1837620 1839259 := bstep (se 1 (by rfl) ⟨1379444, by rfl⟩ : syracuseStep 1839259 = 2758889) B2758889
theorem B2756783 : Blo 1837620 2756783 := bstep (se 1 (by rfl) ⟨2067587, by rfl⟩ : syracuseStep 2756783 = 4135175) B4135175
theorem B3928297 : Blo 1837620 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B29806829 : Blo 1837620 29806829 := bstep (se 3 (by rfl) ⟨5588780, by rfl⟩ : syracuseStep 29806829 = 11177561) B11177561
theorem B1839463 : Blo 1837620 1839463 := bstep (se 1 (by rfl) ⟨1379597, by rfl⟩ : syracuseStep 1839463 = 2759195) B2759195
theorem B3101051 : Blo 1837620 3101051 := bstep (se 1 (by rfl) ⟨2325788, by rfl⟩ : syracuseStep 3101051 = 4651577) B4651577
theorem B2756987 : Blo 1837620 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B1839515 : Blo 1837620 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B6205895 : Blo 1837620 6205895 := bstep (se 1 (by rfl) ⟨4654421, by rfl⟩ : syracuseStep 6205895 = 9308843) B9308843
theorem B3101321 : Blo 1837620 3101321 := bstep (se 2 (by rfl) ⟨1162995, by rfl⟩ : syracuseStep 3101321 = 2325991) B2325991
theorem B2757257 : Blo 1837620 2757257 := bstep (se 2 (by rfl) ⟨1033971, by rfl⟩ : syracuseStep 2757257 = 2067943) B2067943
theorem B2069311 : Blo 1837620 2069311 := bstep (se 1 (by rfl) ⟨1551983, by rfl⟩ : syracuseStep 2069311 = 3103967) B3103967
theorem B3928895 : Blo 1837620 3928895 := bstep (se 1 (by rfl) ⟨2946671, by rfl⟩ : syracuseStep 3928895 = 5893343) B5893343
theorem B2757467 : Blo 1837620 2757467 := bstep (se 1 (by rfl) ⟨2068100, by rfl⟩ : syracuseStep 2757467 = 4136201) B4136201
theorem B13955975 : Blo 1837620 13955975 := bstep (se 1 (by rfl) ⟨10466981, by rfl⟩ : syracuseStep 13955975 = 20933963) B20933963
theorem B2618249 : Blo 1837620 2618249 := bstep (se 2 (by rfl) ⟨981843, by rfl⟩ : syracuseStep 2618249 = 1963687) B1963687
theorem B4248479 : Blo 1837620 4248479 := bstep (se 1 (by rfl) ⟨3186359, by rfl⟩ : syracuseStep 4248479 = 6372719) B6372719
theorem B14914475 : Blo 1837620 14914475 := bstep (se 1 (by rfl) ⟨11185856, by rfl⟩ : syracuseStep 14914475 = 22371713) B22371713
theorem B7959545 : Blo 1837620 7959545 := bstep (se 2 (by rfl) ⟨2984829, by rfl⟩ : syracuseStep 7959545 = 5969659) B5969659
theorem B2946299 : Blo 1837620 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B2757929 : Blo 1837620 2757929 := bstep (se 2 (by rfl) ⟨1034223, by rfl⟩ : syracuseStep 2757929 = 2068447) B2068447
theorem B20944169 : Blo 1837620 20944169 := bstep (se 2 (by rfl) ⟨7854063, by rfl⟩ : syracuseStep 20944169 = 15708127) B15708127
theorem B7853449 : Blo 1837620 7853449 := bstep (se 2 (by rfl) ⟨2945043, by rfl⟩ : syracuseStep 7853449 = 5890087) B5890087
theorem B2758127 : Blo 1837620 2758127 := bstep (se 1 (by rfl) ⟨2068595, by rfl⟩ : syracuseStep 2758127 = 4137191) B4137191
theorem B6207137 : Blo 1837620 6207137 := bstep (se 2 (by rfl) ⟨2327676, by rfl⟩ : syracuseStep 6207137 = 4655353) B4655353
theorem B9312083 : Blo 1837620 9312083 := bstep (se 1 (by rfl) ⟨6984062, by rfl⟩ : syracuseStep 9312083 = 13968125) B13968125
theorem B4134779 : Blo 1837620 4134779 := bstep (se 1 (by rfl) ⟨3101084, by rfl⟩ : syracuseStep 4134779 = 6202169) B6202169
theorem B2758523 : Blo 1837620 2758523 := bstep (se 1 (by rfl) ⟨2068892, by rfl⟩ : syracuseStep 2758523 = 4137785) B4137785
theorem B4134815 : Blo 1837620 4134815 := bstep (se 1 (by rfl) ⟨3101111, by rfl⟩ : syracuseStep 4134815 = 6202223) B6202223
theorem B2758559 : Blo 1837620 2758559 := bstep (se 1 (by rfl) ⟨2068919, by rfl⟩ : syracuseStep 2758559 = 4137839) B4137839
theorem B4135049 : Blo 1837620 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B2758793 : Blo 1837620 2758793 := bstep (se 2 (by rfl) ⟨1034547, by rfl⟩ : syracuseStep 2758793 = 2069095) B2069095
theorem B31848713 : Blo 1837620 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B2758943 : Blo 1837620 2758943 := bstep (se 1 (by rfl) ⟨2069207, by rfl⟩ : syracuseStep 2758943 = 4138415) B4138415
theorem B4135265 : Blo 1837620 4135265 := bstep (se 2 (by rfl) ⟨1550724, by rfl⟩ : syracuseStep 4135265 = 3101449) B3101449
theorem B4135355 : Blo 1837620 4135355 := bstep (se 1 (by rfl) ⟨3101516, by rfl⟩ : syracuseStep 4135355 = 6203033) B6203033
theorem B17676953 : Blo 1837620 17676953 := bstep (se 2 (by rfl) ⟨6628857, by rfl⟩ : syracuseStep 17676953 = 13257715) B13257715
theorem B127441583 : Blo 1837620 127441583 := bstep (se 1 (by rfl) ⟨95581187, by rfl⟩ : syracuseStep 127441583 = 191162375) B191162375
theorem B4135751 : Blo 1837620 4135751 := bstep (se 1 (by rfl) ⟨3101813, by rfl⟩ : syracuseStep 4135751 = 6203627) B6203627
theorem B17668955 : Blo 1837620 17668955 := bstep (se 1 (by rfl) ⟨13251716, by rfl⟩ : syracuseStep 17668955 = 26503433) B26503433
theorem B6208487 : Blo 1837620 6208487 := bstep (se 1 (by rfl) ⟨4656365, by rfl⟩ : syracuseStep 6208487 = 9312731) B9312731
theorem B4136057 : Blo 1837620 4136057 := bstep (se 2 (by rfl) ⟨1551021, by rfl⟩ : syracuseStep 4136057 = 3102043) B3102043
theorem B4652255 : Blo 1837620 4652255 := bstep (se 1 (by rfl) ⟨3489191, by rfl⟩ : syracuseStep 4652255 = 6978383) B6978383
theorem B17677763 : Blo 1837620 17677763 := bstep (se 1 (by rfl) ⟨13258322, by rfl⟩ : syracuseStep 17677763 = 26516645) B26516645
theorem B6979067 : Blo 1837620 6979067 := bstep (se 1 (by rfl) ⟨5234300, by rfl⟩ : syracuseStep 6979067 = 10468601) B10468601
theorem B4136615 : Blo 1837620 4136615 := bstep (se 1 (by rfl) ⟨3102461, by rfl⟩ : syracuseStep 4136615 = 6204923) B6204923
theorem B7855841 : Blo 1837620 7855841 := bstep (se 2 (by rfl) ⟨2945940, by rfl⟩ : syracuseStep 7855841 = 5891881) B5891881
theorem B1941223 : Blo 1837620 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B4136723 : Blo 1837620 4136723 := bstep (se 1 (by rfl) ⟨3102542, by rfl⟩ : syracuseStep 4136723 = 6205085) B6205085
theorem B69885827 : Blo 1837620 69885827 := bstep (se 1 (by rfl) ⟨52414370, by rfl⟩ : syracuseStep 69885827 = 104828741) B104828741
theorem B4653247 : Blo 1837620 4653247 := bstep (se 1 (by rfl) ⟨3489935, by rfl⟩ : syracuseStep 4653247 = 6979871) B6979871
theorem B4137263 : Blo 1837620 4137263 := bstep (se 1 (by rfl) ⟨3102947, by rfl⟩ : syracuseStep 4137263 = 6205895) B6205895
theorem B3490103 : Blo 1837620 3490103 := bstep (se 1 (by rfl) ⟨2617577, by rfl⟩ : syracuseStep 3490103 = 5235155) B5235155
theorem B16777759 : Blo 1837620 16777759 := bstep (se 1 (by rfl) ⟨12583319, by rfl⟩ : syracuseStep 16777759 = 25166639) B25166639
theorem B9306899 : Blo 1837620 9306899 := bstep (se 1 (by rfl) ⟨6980174, by rfl⟩ : syracuseStep 9306899 = 13960349) B13960349
theorem B25158761 : Blo 1837620 25158761 := bstep (se 2 (by rfl) ⟨9434535, by rfl⟩ : syracuseStep 25158761 = 18869071) B18869071
theorem B4138091 : Blo 1837620 4138091 := bstep (se 1 (by rfl) ⟨3103568, by rfl⟩ : syracuseStep 4138091 = 6207137) B6207137
theorem B4654655 : Blo 1837620 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B4654867 : Blo 1837620 4654867 := bstep (se 1 (by rfl) ⟨3491150, by rfl⟩ : syracuseStep 4654867 = 6982301) B6982301
theorem B84961055 : Blo 1837620 84961055 := bstep (se 1 (by rfl) ⟨63720791, by rfl⟩ : syracuseStep 84961055 = 127441583) B127441583
theorem B10471265 : Blo 1837620 10471265 := bstep (se 2 (by rfl) ⟨3926724, by rfl⟩ : syracuseStep 10471265 = 7853449) B7853449
theorem B39749615 : Blo 1837620 39749615 := bstep (se 1 (by rfl) ⟨29812211, by rfl⟩ : syracuseStep 39749615 = 59624423) B59624423
theorem B4138991 : Blo 1837620 4138991 := bstep (se 1 (by rfl) ⟨3104243, by rfl⟩ : syracuseStep 4138991 = 6208487) B6208487
theorem B4655303 : Blo 1837620 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B6981997 : Blo 1837620 6981997 := bstep (se 3 (by rfl) ⟨1309124, by rfl⟩ : syracuseStep 6981997 = 2618249) B2618249
theorem B5237227 : Blo 1837620 5237227 := bstep (se 1 (by rfl) ⟨3927920, by rfl⟩ : syracuseStep 5237227 = 7855841) B7855841
theorem B46590551 : Blo 1837620 46590551 := bstep (se 1 (by rfl) ⟨34942913, by rfl⟩ : syracuseStep 46590551 = 69885827) B69885827
theorem B31427189 : Blo 1837620 31427189 := bstep (se 5 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 31427189 = 2946299) B2946299
theorem B1837727 : Blo 1837620 1837727 := bstep (se 1 (by rfl) ⟨1378295, by rfl⟩ : syracuseStep 1837727 = 2756591) B2756591
theorem B1837735 : Blo 1837620 1837735 := bstep (se 1 (by rfl) ⟨1378301, by rfl⟩ : syracuseStep 1837735 = 2756603) B2756603
theorem B1837775 : Blo 1837620 1837775 := bstep (se 1 (by rfl) ⟨1378331, by rfl⟩ : syracuseStep 1837775 = 2756663) B2756663
theorem B1837807 : Blo 1837620 1837807 := bstep (se 1 (by rfl) ⟨1378355, by rfl⟩ : syracuseStep 1837807 = 2756711) B2756711
theorem B1837855 : Blo 1837620 1837855 := bstep (se 1 (by rfl) ⟨1378391, by rfl⟩ : syracuseStep 1837855 = 2756783) B2756783
theorem B8383337 : Blo 1837620 8383337 := bstep (se 2 (by rfl) ⟨3143751, by rfl⟩ : syracuseStep 8383337 = 6287503) B6287503
theorem B4656001 : Blo 1837620 4656001 := bstep (se 2 (by rfl) ⟨1746000, by rfl⟩ : syracuseStep 4656001 = 3492001) B3492001
theorem B2067367 : Blo 1837620 2067367 := bstep (se 1 (by rfl) ⟨1550525, by rfl⟩ : syracuseStep 2067367 = 3101051) B3101051
theorem B1837991 : Blo 1837620 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B5237729 : Blo 1837620 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B2067547 : Blo 1837620 2067547 := bstep (se 1 (by rfl) ⟨1550660, by rfl⟩ : syracuseStep 2067547 = 3101321) B3101321
theorem B1838171 : Blo 1837620 1838171 := bstep (se 1 (by rfl) ⟨1378628, by rfl⟩ : syracuseStep 1838171 = 2757257) B2757257
theorem B1838311 : Blo 1837620 1838311 := bstep (se 1 (by rfl) ⟨1378733, by rfl⟩ : syracuseStep 1838311 = 2757467) B2757467
theorem B59649331 : Blo 1837620 59649331 := bstep (se 1 (by rfl) ⟨44736998, by rfl⟩ : syracuseStep 59649331 = 89473997) B89473997
theorem B1838619 : Blo 1837620 1838619 := bstep (se 1 (by rfl) ⟨1378964, by rfl⟩ : syracuseStep 1838619 = 2757929) B2757929
theorem B13962779 : Blo 1837620 13962779 := bstep (se 1 (by rfl) ⟨10472084, by rfl⟩ : syracuseStep 13962779 = 20944169) B20944169
theorem B1838751 : Blo 1837620 1838751 := bstep (se 1 (by rfl) ⟨1379063, by rfl⟩ : syracuseStep 1838751 = 2758127) B2758127
theorem B9309977 : Blo 1837620 9309977 := bstep (se 2 (by rfl) ⟨3491241, by rfl⟩ : syracuseStep 9309977 = 6982483) B6982483
theorem B2756519 : Blo 1837620 2756519 := bstep (se 1 (by rfl) ⟨2067389, by rfl⟩ : syracuseStep 2756519 = 4134779) B4134779
theorem B1839015 : Blo 1837620 1839015 := bstep (se 1 (by rfl) ⟨1379261, by rfl⟩ : syracuseStep 1839015 = 2758523) B2758523
theorem B2756543 : Blo 1837620 2756543 := bstep (se 1 (by rfl) ⟨2067407, by rfl⟩ : syracuseStep 2756543 = 4134815) B4134815
theorem B1839039 : Blo 1837620 1839039 := bstep (se 1 (by rfl) ⟨1379279, by rfl⟩ : syracuseStep 1839039 = 2758559) B2758559
theorem B4419623 : Blo 1837620 4419623 := bstep (se 1 (by rfl) ⟨3314717, by rfl⟩ : syracuseStep 4419623 = 6629435) B6629435
theorem B2756699 : Blo 1837620 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B1839195 : Blo 1837620 1839195 := bstep (se 1 (by rfl) ⟨1379396, by rfl⟩ : syracuseStep 1839195 = 2758793) B2758793
theorem B1839295 : Blo 1837620 1839295 := bstep (se 1 (by rfl) ⟨1379471, by rfl⟩ : syracuseStep 1839295 = 2758943) B2758943
theorem B2756843 : Blo 1837620 2756843 := bstep (se 1 (by rfl) ⟨2067632, by rfl⟩ : syracuseStep 2756843 = 4135265) B4135265
theorem B2756903 : Blo 1837620 2756903 := bstep (se 1 (by rfl) ⟨2067677, by rfl⟩ : syracuseStep 2756903 = 4135355) B4135355
theorem B11784635 : Blo 1837620 11784635 := bstep (se 1 (by rfl) ⟨8838476, by rfl⟩ : syracuseStep 11784635 = 17676953) B17676953
theorem B25506251 : Blo 1837620 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B2757167 : Blo 1837620 2757167 := bstep (se 1 (by rfl) ⟨2067875, by rfl⟩ : syracuseStep 2757167 = 4135751) B4135751
theorem B11776585 : Blo 1837620 11776585 := bstep (se 2 (by rfl) ⟨4416219, by rfl⟩ : syracuseStep 11776585 = 8832439) B8832439
theorem B7959143 : Blo 1837620 7959143 := bstep (se 1 (by rfl) ⟨5969357, by rfl⟩ : syracuseStep 7959143 = 11938715) B11938715
theorem B2757371 : Blo 1837620 2757371 := bstep (se 1 (by rfl) ⟨2068028, by rfl⟩ : syracuseStep 2757371 = 4136057) B4136057
theorem B3101503 : Blo 1837620 3101503 := bstep (se 1 (by rfl) ⟨2326127, by rfl⟩ : syracuseStep 3101503 = 4652255) B4652255
theorem B11785175 : Blo 1837620 11785175 := bstep (se 1 (by rfl) ⟨8838881, by rfl⟩ : syracuseStep 11785175 = 17677763) B17677763
theorem B1963055 : Blo 1837620 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B2757743 : Blo 1837620 2757743 := bstep (se 1 (by rfl) ⟨2068307, by rfl⟩ : syracuseStep 2757743 = 4136615) B4136615
theorem B2757815 : Blo 1837620 2757815 := bstep (se 1 (by rfl) ⟨2068361, by rfl⟩ : syracuseStep 2757815 = 4136723) B4136723
theorem B2758055 : Blo 1837620 2758055 := bstep (se 1 (by rfl) ⟨2068541, by rfl⟩ : syracuseStep 2758055 = 4137083) B4137083
theorem B19871219 : Blo 1837620 19871219 := bstep (se 1 (by rfl) ⟨14903414, by rfl⟩ : syracuseStep 19871219 = 29806829) B29806829
theorem B3102239 : Blo 1837620 3102239 := bstep (se 1 (by rfl) ⟨2326679, by rfl⟩ : syracuseStep 3102239 = 4653359) B4653359
theorem B2758235 : Blo 1837620 2758235 := bstep (se 1 (by rfl) ⟨2068676, by rfl⟩ : syracuseStep 2758235 = 4137353) B4137353
theorem B7853723 : Blo 1837620 7853723 := bstep (se 1 (by rfl) ⟨5890292, by rfl⟩ : syracuseStep 7853723 = 11780585) B11780585
theorem B22664873 : Blo 1837620 22664873 := bstep (se 2 (by rfl) ⟨8499327, by rfl⟩ : syracuseStep 22664873 = 16998655) B16998655
theorem B10475183 : Blo 1837620 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B5592809 : Blo 1837620 5592809 := bstep (se 2 (by rfl) ⟨2097303, by rfl⟩ : syracuseStep 5592809 = 4194607) B4194607
theorem B50304827 : Blo 1837620 50304827 := bstep (se 1 (by rfl) ⟨37728620, by rfl⟩ : syracuseStep 50304827 = 75457241) B75457241
theorem B2619263 : Blo 1837620 2619263 := bstep (se 1 (by rfl) ⟨1964447, by rfl⟩ : syracuseStep 2619263 = 3928895) B3928895
theorem B9303983 : Blo 1837620 9303983 := bstep (se 1 (by rfl) ⟨6977987, by rfl⟩ : syracuseStep 9303983 = 13955975) B13955975
theorem B2832319 : Blo 1837620 2832319 := bstep (se 1 (by rfl) ⟨2124239, by rfl⟩ : syracuseStep 2832319 = 4248479) B4248479
theorem B9942983 : Blo 1837620 9942983 := bstep (se 1 (by rfl) ⟨7457237, by rfl⟩ : syracuseStep 9942983 = 14914475) B14914475
theorem B5306363 : Blo 1837620 5306363 := bstep (se 1 (by rfl) ⟨3979772, by rfl⟩ : syracuseStep 5306363 = 7959545) B7959545
theorem B3102907 : Blo 1837620 3102907 := bstep (se 1 (by rfl) ⟨2327180, by rfl⟩ : syracuseStep 3102907 = 4654361) B4654361
theorem B9935111 : Blo 1837620 9935111 := bstep (se 1 (by rfl) ⟨7451333, by rfl⟩ : syracuseStep 9935111 = 14902667) B14902667
theorem B16767251 : Blo 1837620 16767251 := bstep (se 1 (by rfl) ⟨12575438, by rfl⟩ : syracuseStep 16767251 = 25150877) B25150877
theorem B2758991 : Blo 1837620 2758991 := bstep (se 1 (by rfl) ⟨2069243, by rfl⟩ : syracuseStep 2758991 = 4138487) B4138487
theorem B2759015 : Blo 1837620 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B2759081 : Blo 1837620 2759081 := bstep (se 2 (by rfl) ⟨1034655, by rfl⟩ : syracuseStep 2759081 = 2069311) B2069311
theorem B6208055 : Blo 1837620 6208055 := bstep (se 1 (by rfl) ⟨4656041, by rfl⟩ : syracuseStep 6208055 = 9312083) B9312083
theorem B21224015 : Blo 1837620 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B15120985 : Blo 1837620 15120985 := bstep (se 2 (by rfl) ⟨5670369, by rfl⟩ : syracuseStep 15120985 = 11340739) B11340739
theorem B5593853 : Blo 1837620 5593853 := bstep (se 3 (by rfl) ⟨1048847, by rfl⟩ : syracuseStep 5593853 = 2097695) B2097695
theorem B21232475 : Blo 1837620 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B19880909 : Blo 1837620 19880909 := bstep (se 3 (by rfl) ⟨3727670, by rfl⟩ : syracuseStep 19880909 = 7455341) B7455341
theorem B4135931 : Blo 1837620 4135931 := bstep (se 1 (by rfl) ⟨3101948, by rfl⟩ : syracuseStep 4135931 = 6203897) B6203897
theorem B4136111 : Blo 1837620 4136111 := bstep (se 1 (by rfl) ⟨3102083, by rfl⟩ : syracuseStep 4136111 = 6204167) B6204167
theorem B11779303 : Blo 1837620 11779303 := bstep (se 1 (by rfl) ⟨8834477, by rfl⟩ : syracuseStep 11779303 = 17668955) B17668955
theorem B4136255 : Blo 1837620 4136255 := bstep (se 1 (by rfl) ⟨3102191, by rfl⟩ : syracuseStep 4136255 = 6204383) B6204383
theorem B4136363 : Blo 1837620 4136363 := bstep (se 1 (by rfl) ⟨3102272, by rfl⟩ : syracuseStep 4136363 = 6204545) B6204545
theorem B2588297 : Blo 1837620 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B4652711 : Blo 1837620 4652711 := bstep (se 1 (by rfl) ⟨3489533, by rfl⟩ : syracuseStep 4652711 = 6979067) B6979067
theorem B29810519 : Blo 1837620 29810519 := bstep (se 1 (by rfl) ⟨22357889, by rfl⟩ : syracuseStep 29810519 = 44715779) B44715779
theorem B44752763 : Blo 1837620 44752763 := bstep (se 1 (by rfl) ⟨33564572, by rfl⟩ : syracuseStep 44752763 = 67129145) B67129145
theorem B4136831 : Blo 1837620 4136831 := bstep (se 1 (by rfl) ⟨3102623, by rfl⟩ : syracuseStep 4136831 = 6205247) B6205247
theorem B4136903 : Blo 1837620 4136903 := bstep (se 1 (by rfl) ⟨3102677, by rfl⟩ : syracuseStep 4136903 = 6205355) B6205355
theorem B5234813 : Blo 1837620 5234813 := bstep (se 3 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 5234813 = 1963055) B1963055
theorem B2326735 : Blo 1837620 2326735 := bstep (se 1 (by rfl) ⟨1745051, by rfl⟩ : syracuseStep 2326735 = 3490103) B3490103
theorem B4137209 : Blo 1837620 4137209 := bstep (se 2 (by rfl) ⟨1551453, by rfl⟩ : syracuseStep 4137209 = 3102907) B3102907
theorem B7856423 : Blo 1837620 7856423 := bstep (se 1 (by rfl) ⟨5892317, by rfl⟩ : syracuseStep 7856423 = 11784635) B11784635
theorem B7856783 : Blo 1837620 7856783 := bstep (se 1 (by rfl) ⟨5892587, by rfl⟩ : syracuseStep 7856783 = 11785175) B11785175
theorem B20161313 : Blo 1837620 20161313 := bstep (se 2 (by rfl) ⟨7560492, by rfl⟩ : syracuseStep 20161313 = 15120985) B15120985
theorem B13247479 : Blo 1837620 13247479 := bstep (se 1 (by rfl) ⟨9935609, by rfl⟩ : syracuseStep 13247479 = 19871219) B19871219
theorem B5235815 : Blo 1837620 5235815 := bstep (se 1 (by rfl) ⟨3926861, by rfl⟩ : syracuseStep 5235815 = 7853723) B7853723
theorem B3728539 : Blo 1837620 3728539 := bstep (se 1 (by rfl) ⟨2796404, by rfl⟩ : syracuseStep 3728539 = 5592809) B5592809
theorem B56640703 : Blo 1837620 56640703 := bstep (se 1 (by rfl) ⟨42480527, by rfl⟩ : syracuseStep 56640703 = 84961055) B84961055
theorem B6980843 : Blo 1837620 6980843 := bstep (se 1 (by rfl) ⟨5235632, by rfl⟩ : syracuseStep 6980843 = 10471265) B10471265
theorem B6202655 : Blo 1837620 6202655 := bstep (se 1 (by rfl) ⟨4651991, by rfl⟩ : syracuseStep 6202655 = 9303983) B9303983
theorem B6628655 : Blo 1837620 6628655 := bstep (se 1 (by rfl) ⟨4971491, by rfl⟩ : syracuseStep 6628655 = 9942983) B9942983
theorem B27608501 : Blo 1837620 27608501 := bstep (se 5 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 27608501 = 2588297) B2588297
theorem B15705737 : Blo 1837620 15705737 := bstep (se 2 (by rfl) ⟨5889651, by rfl⟩ : syracuseStep 15705737 = 11779303) B11779303
theorem B4138703 : Blo 1837620 4138703 := bstep (se 1 (by rfl) ⟨3104027, by rfl⟩ : syracuseStep 4138703 = 6208055) B6208055
theorem B14149343 : Blo 1837620 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B3729235 : Blo 1837620 3729235 := bstep (se 1 (by rfl) ⟨2796926, by rfl⟩ : syracuseStep 3729235 = 5593853) B5593853
theorem B5588891 : Blo 1837620 5588891 := bstep (se 1 (by rfl) ⟨4191668, by rfl⟩ : syracuseStep 5588891 = 8383337) B8383337
theorem B3491819 : Blo 1837620 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B9308519 : Blo 1837620 9308519 := bstep (se 1 (by rfl) ⟨6981389, by rfl⟩ : syracuseStep 9308519 = 13962779) B13962779
theorem B1837679 : Blo 1837620 1837679 := bstep (se 1 (by rfl) ⟨1378259, by rfl⟩ : syracuseStep 1837679 = 2756519) B2756519
theorem B1837695 : Blo 1837620 1837695 := bstep (se 1 (by rfl) ⟨1378271, by rfl⟩ : syracuseStep 1837695 = 2756543) B2756543
theorem B1837799 : Blo 1837620 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B1837895 : Blo 1837620 1837895 := bstep (se 1 (by rfl) ⟨1378421, by rfl⟩ : syracuseStep 1837895 = 2756843) B2756843
theorem B1837935 : Blo 1837620 1837935 := bstep (se 1 (by rfl) ⟨1378451, by rfl⟩ : syracuseStep 1837935 = 2756903) B2756903
theorem B6204329 : Blo 1837620 6204329 := bstep (se 2 (by rfl) ⟨2326623, by rfl⟩ : syracuseStep 6204329 = 4653247) B4653247
theorem B1838111 : Blo 1837620 1838111 := bstep (se 1 (by rfl) ⟨1378583, by rfl⟩ : syracuseStep 1838111 = 2757167) B2757167
theorem B9309329 : Blo 1837620 9309329 := bstep (se 2 (by rfl) ⟨3490998, by rfl⟩ : syracuseStep 9309329 = 6981997) B6981997
theorem B1838247 : Blo 1837620 1838247 := bstep (se 1 (by rfl) ⟨1378685, by rfl⟩ : syracuseStep 1838247 = 2757371) B2757371
theorem B6204599 : Blo 1837620 6204599 := bstep (se 1 (by rfl) ⟨4653449, by rfl⟩ : syracuseStep 6204599 = 9306899) B9306899
theorem B6982969 : Blo 1837620 6982969 := bstep (se 2 (by rfl) ⟨2618613, by rfl⟩ : syracuseStep 6982969 = 5237227) B5237227
theorem B16772507 : Blo 1837620 16772507 := bstep (se 1 (by rfl) ⟨12579380, by rfl⟩ : syracuseStep 16772507 = 25158761) B25158761
theorem B1838495 : Blo 1837620 1838495 := bstep (se 1 (by rfl) ⟨1378871, by rfl⟩ : syracuseStep 1838495 = 2757743) B2757743
theorem B1838543 : Blo 1837620 1838543 := bstep (se 1 (by rfl) ⟨1378907, by rfl⟩ : syracuseStep 1838543 = 2757815) B2757815
theorem B1838703 : Blo 1837620 1838703 := bstep (se 1 (by rfl) ⟨1379027, by rfl⟩ : syracuseStep 1838703 = 2758055) B2758055
theorem B2068159 : Blo 1837620 2068159 := bstep (se 1 (by rfl) ⟨1551119, by rfl⟩ : syracuseStep 2068159 = 3102239) B3102239
theorem B1838823 : Blo 1837620 1838823 := bstep (se 1 (by rfl) ⟨1379117, by rfl⟩ : syracuseStep 1838823 = 2758235) B2758235
theorem B15109915 : Blo 1837620 15109915 := bstep (se 1 (by rfl) ⟨11332436, by rfl⟩ : syracuseStep 15109915 = 22664873) B22664873
theorem B6983455 : Blo 1837620 6983455 := bstep (se 1 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 6983455 = 10475183) B10475183
theorem B2756489 : Blo 1837620 2756489 := bstep (se 2 (by rfl) ⟨1033683, by rfl⟩ : syracuseStep 2756489 = 2067367) B2067367
theorem B2756729 : Blo 1837620 2756729 := bstep (se 2 (by rfl) ⟨1033773, by rfl⟩ : syracuseStep 2756729 = 2067547) B2067547
theorem B6623407 : Blo 1837620 6623407 := bstep (se 1 (by rfl) ⟨4967555, by rfl⟩ : syracuseStep 6623407 = 9935111) B9935111
theorem B11178167 : Blo 1837620 11178167 := bstep (se 1 (by rfl) ⟨8383625, by rfl⟩ : syracuseStep 11178167 = 16767251) B16767251
theorem B1839327 : Blo 1837620 1839327 := bstep (se 1 (by rfl) ⟨1379495, by rfl⟩ : syracuseStep 1839327 = 2758991) B2758991
theorem B1839343 : Blo 1837620 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B1839387 : Blo 1837620 1839387 := bstep (se 1 (by rfl) ⟨1379540, by rfl⟩ : syracuseStep 1839387 = 2759081) B2759081
theorem B31060367 : Blo 1837620 31060367 := bstep (se 1 (by rfl) ⟨23295275, by rfl⟩ : syracuseStep 31060367 = 46590551) B46590551
theorem B79532441 : Blo 1837620 79532441 := bstep (se 2 (by rfl) ⟨29824665, by rfl⟩ : syracuseStep 79532441 = 59649331) B59649331
theorem B20951459 : Blo 1837620 20951459 := bstep (se 1 (by rfl) ⟨15713594, by rfl⟩ : syracuseStep 20951459 = 31427189) B31427189
theorem B2757287 : Blo 1837620 2757287 := bstep (se 1 (by rfl) ⟨2067965, by rfl⟩ : syracuseStep 2757287 = 4135931) B4135931
theorem B2757407 : Blo 1837620 2757407 := bstep (se 1 (by rfl) ⟨2068055, by rfl⟩ : syracuseStep 2757407 = 4136111) B4136111
theorem B2757503 : Blo 1837620 2757503 := bstep (se 1 (by rfl) ⟨2068127, by rfl⟩ : syracuseStep 2757503 = 4136255) B4136255
theorem B2757575 : Blo 1837620 2757575 := bstep (se 1 (by rfl) ⟨2068181, by rfl⟩ : syracuseStep 2757575 = 4136363) B4136363
theorem B6984701 : Blo 1837620 6984701 := bstep (se 3 (by rfl) ⟨1309631, by rfl⟩ : syracuseStep 6984701 = 2619263) B2619263
theorem B6206489 : Blo 1837620 6206489 := bstep (se 2 (by rfl) ⟨2327433, by rfl⟩ : syracuseStep 6206489 = 4654867) B4654867
theorem B3101807 : Blo 1837620 3101807 := bstep (se 1 (by rfl) ⟨2326355, by rfl⟩ : syracuseStep 3101807 = 4652711) B4652711
theorem B6206651 : Blo 1837620 6206651 := bstep (se 1 (by rfl) ⟨4654988, by rfl⟩ : syracuseStep 6206651 = 9309977) B9309977
theorem B2757887 : Blo 1837620 2757887 := bstep (se 1 (by rfl) ⟨2068415, by rfl⟩ : syracuseStep 2757887 = 4136831) B4136831
theorem B2757935 : Blo 1837620 2757935 := bstep (se 1 (by rfl) ⟨2068451, by rfl⟩ : syracuseStep 2757935 = 4136903) B4136903
theorem B11785661 : Blo 1837620 11785661 := bstep (se 3 (by rfl) ⟨2209811, by rfl⟩ : syracuseStep 11785661 = 4419623) B4419623
theorem B2758175 : Blo 1837620 2758175 := bstep (se 1 (by rfl) ⟨2068631, by rfl⟩ : syracuseStep 2758175 = 4137263) B4137263
theorem B17004167 : Blo 1837620 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B5306095 : Blo 1837620 5306095 := bstep (se 1 (by rfl) ⟨3979571, by rfl⟩ : syracuseStep 5306095 = 7959143) B7959143
theorem B22370345 : Blo 1837620 22370345 := bstep (se 2 (by rfl) ⟨8388879, by rfl⟩ : syracuseStep 22370345 = 16777759) B16777759
theorem B2758727 : Blo 1837620 2758727 := bstep (se 1 (by rfl) ⟨2069045, by rfl⟩ : syracuseStep 2758727 = 4138091) B4138091
theorem B15702113 : Blo 1837620 15702113 := bstep (se 2 (by rfl) ⟨5888292, by rfl⟩ : syracuseStep 15702113 = 11776585) B11776585
theorem B3103103 : Blo 1837620 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B4135337 : Blo 1837620 4135337 := bstep (se 2 (by rfl) ⟨1550751, by rfl⟩ : syracuseStep 4135337 = 3101503) B3101503
theorem B6208001 : Blo 1837620 6208001 := bstep (se 2 (by rfl) ⟨2328000, by rfl⟩ : syracuseStep 6208001 = 4656001) B4656001
theorem B33536551 : Blo 1837620 33536551 := bstep (se 1 (by rfl) ⟨25152413, by rfl⟩ : syracuseStep 33536551 = 50304827) B50304827
theorem B26499743 : Blo 1837620 26499743 := bstep (se 1 (by rfl) ⟨19874807, by rfl⟩ : syracuseStep 26499743 = 39749615) B39749615
theorem B2759327 : Blo 1837620 2759327 := bstep (se 1 (by rfl) ⟨2069495, by rfl⟩ : syracuseStep 2759327 = 4138991) B4138991
theorem B3537575 : Blo 1837620 3537575 := bstep (se 1 (by rfl) ⟨2653181, by rfl⟩ : syracuseStep 3537575 = 5306363) B5306363
theorem B3103535 : Blo 1837620 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B14154983 : Blo 1837620 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B13253939 : Blo 1837620 13253939 := bstep (se 1 (by rfl) ⟨9940454, by rfl⟩ : syracuseStep 13253939 = 19880909) B19880909
theorem B19873679 : Blo 1837620 19873679 := bstep (se 1 (by rfl) ⟨14905259, by rfl⟩ : syracuseStep 19873679 = 29810519) B29810519
theorem B29835175 : Blo 1837620 29835175 := bstep (se 1 (by rfl) ⟨22376381, by rfl⟩ : syracuseStep 29835175 = 44752763) B44752763
theorem B3776425 : Blo 1837620 3776425 := bstep (se 2 (by rfl) ⟨1416159, by rfl⟩ : syracuseStep 3776425 = 2832319) B2832319
theorem B3489875 : Blo 1837620 3489875 := bstep (se 1 (by rfl) ⟨2617406, by rfl⟩ : syracuseStep 3489875 = 5234813) B5234813
theorem B8831209 : Blo 1837620 8831209 := bstep (se 2 (by rfl) ⟨3311703, by rfl⟩ : syracuseStep 8831209 = 6623407) B6623407
theorem B13967639 : Blo 1837620 13967639 := bstep (se 1 (by rfl) ⟨10475729, by rfl⟩ : syracuseStep 13967639 = 20951459) B20951459
theorem B4137659 : Blo 1837620 4137659 := bstep (se 1 (by rfl) ⟨3103244, by rfl⟩ : syracuseStep 4137659 = 6206489) B6206489
theorem B3490543 : Blo 1837620 3490543 := bstep (se 1 (by rfl) ⟨2617907, by rfl⟩ : syracuseStep 3490543 = 5235815) B5235815
theorem B4137767 : Blo 1837620 4137767 := bstep (se 1 (by rfl) ⟨3103325, by rfl⟩ : syracuseStep 4137767 = 6206651) B6206651
theorem B4653895 : Blo 1837620 4653895 := bstep (se 1 (by rfl) ⟨3490421, by rfl⟩ : syracuseStep 4653895 = 6980843) B6980843
theorem B7857107 : Blo 1837620 7857107 := bstep (se 1 (by rfl) ⟨5892830, by rfl⟩ : syracuseStep 7857107 = 11785661) B11785661
theorem B10470491 : Blo 1837620 10470491 := bstep (se 1 (by rfl) ⟨7852868, by rfl⟩ : syracuseStep 10470491 = 15705737) B15705737
theorem B2327879 : Blo 1837620 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B17663305 : Blo 1837620 17663305 := bstep (se 2 (by rfl) ⟨6623739, by rfl⟩ : syracuseStep 17663305 = 13247479) B13247479
theorem B4138667 : Blo 1837620 4138667 := bstep (se 1 (by rfl) ⟨3104000, by rfl⟩ : syracuseStep 4138667 = 6208001) B6208001
theorem B37734133 : Blo 1837620 37734133 := bstep (se 5 (by rfl) ⟨1768787, by rfl⟩ : syracuseStep 37734133 = 3537575) B3537575
theorem B20146553 : Blo 1837620 20146553 := bstep (se 2 (by rfl) ⟨7554957, by rfl⟩ : syracuseStep 20146553 = 15109915) B15109915
theorem B52996477 : Blo 1837620 52996477 := bstep (se 3 (by rfl) ⟨9936839, by rfl⟩ : syracuseStep 52996477 = 19873679) B19873679
theorem B1837659 : Blo 1837620 1837659 := bstep (se 1 (by rfl) ⟨1378244, by rfl⟩ : syracuseStep 1837659 = 2756489) B2756489
theorem B1837819 : Blo 1837620 1837819 := bstep (se 1 (by rfl) ⟨1378364, by rfl⟩ : syracuseStep 1837819 = 2756729) B2756729
theorem B5237615 : Blo 1837620 5237615 := bstep (se 1 (by rfl) ⟨3928211, by rfl⟩ : syracuseStep 5237615 = 7856423) B7856423
theorem B53021627 : Blo 1837620 53021627 := bstep (se 1 (by rfl) ⟨39766220, by rfl⟩ : syracuseStep 53021627 = 79532441) B79532441
theorem B5237855 : Blo 1837620 5237855 := bstep (se 1 (by rfl) ⟨3928391, by rfl⟩ : syracuseStep 5237855 = 7856783) B7856783
theorem B1838191 : Blo 1837620 1838191 := bstep (se 1 (by rfl) ⟨1378643, by rfl⟩ : syracuseStep 1838191 = 2757287) B2757287
theorem B1838271 : Blo 1837620 1838271 := bstep (se 1 (by rfl) ⟨1378703, by rfl⟩ : syracuseStep 1838271 = 2757407) B2757407
theorem B1838335 : Blo 1837620 1838335 := bstep (se 1 (by rfl) ⟨1378751, by rfl⟩ : syracuseStep 1838335 = 2757503) B2757503
theorem B1838383 : Blo 1837620 1838383 := bstep (se 1 (by rfl) ⟨1378787, by rfl⟩ : syracuseStep 1838383 = 2757575) B2757575
theorem B4656467 : Blo 1837620 4656467 := bstep (se 1 (by rfl) ⟨3492350, by rfl⟩ : syracuseStep 4656467 = 6984701) B6984701
theorem B44715401 : Blo 1837620 44715401 := bstep (se 2 (by rfl) ⟨16768275, by rfl⟩ : syracuseStep 44715401 = 33536551) B33536551
theorem B2067871 : Blo 1837620 2067871 := bstep (se 1 (by rfl) ⟨1550903, by rfl⟩ : syracuseStep 2067871 = 3101807) B3101807
theorem B1838591 : Blo 1837620 1838591 := bstep (se 1 (by rfl) ⟨1378943, by rfl⟩ : syracuseStep 1838591 = 2757887) B2757887
theorem B1838623 : Blo 1837620 1838623 := bstep (se 1 (by rfl) ⟨1378967, by rfl⟩ : syracuseStep 1838623 = 2757935) B2757935
theorem B1838783 : Blo 1837620 1838783 := bstep (se 1 (by rfl) ⟨1379087, by rfl⟩ : syracuseStep 1838783 = 2758175) B2758175
theorem B9432895 : Blo 1837620 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B14913563 : Blo 1837620 14913563 := bstep (se 1 (by rfl) ⟨11185172, by rfl⟩ : syracuseStep 14913563 = 22370345) B22370345
theorem B1839151 : Blo 1837620 1839151 := bstep (se 1 (by rfl) ⟨1379363, by rfl⟩ : syracuseStep 1839151 = 2758727) B2758727
theorem B6205679 : Blo 1837620 6205679 := bstep (se 1 (by rfl) ⟨4654259, by rfl⟩ : syracuseStep 6205679 = 9308519) B9308519
theorem B2068735 : Blo 1837620 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B2756891 : Blo 1837620 2756891 := bstep (se 1 (by rfl) ⟨2067668, by rfl⟩ : syracuseStep 2756891 = 4135337) B4135337
theorem B9310625 : Blo 1837620 9310625 := bstep (se 2 (by rfl) ⟨3491484, by rfl⟩ : syracuseStep 9310625 = 6982969) B6982969
theorem B17666495 : Blo 1837620 17666495 := bstep (se 1 (by rfl) ⟨13249871, by rfl⟩ : syracuseStep 17666495 = 26499743) B26499743
theorem B1839551 : Blo 1837620 1839551 := bstep (se 1 (by rfl) ⟨1379663, by rfl⟩ : syracuseStep 1839551 = 2759327) B2759327
theorem B2069023 : Blo 1837620 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B6206219 : Blo 1837620 6206219 := bstep (se 1 (by rfl) ⟨4654664, by rfl⟩ : syracuseStep 6206219 = 9309329) B9309329
theorem B8835959 : Blo 1837620 8835959 := bstep (se 1 (by rfl) ⟨6626969, by rfl⟩ : syracuseStep 8835959 = 13253939) B13253939
theorem B20140933 : Blo 1837620 20140933 := bstep (se 4 (by rfl) ⟨1888212, by rfl⟩ : syracuseStep 20140933 = 3776425) B3776425
theorem B2757545 : Blo 1837620 2757545 := bstep (se 2 (by rfl) ⟨1034079, by rfl⟩ : syracuseStep 2757545 = 2068159) B2068159
theorem B7074793 : Blo 1837620 7074793 := bstep (se 2 (by rfl) ⟨2653047, by rfl⟩ : syracuseStep 7074793 = 5306095) B5306095
theorem B9311273 : Blo 1837620 9311273 := bstep (se 2 (by rfl) ⟨3491727, by rfl⟩ : syracuseStep 9311273 = 6983455) B6983455
theorem B2758139 : Blo 1837620 2758139 := bstep (se 1 (by rfl) ⟨2068604, by rfl⟩ : syracuseStep 2758139 = 4137209) B4137209
theorem B20706911 : Blo 1837620 20706911 := bstep (se 1 (by rfl) ⟨15530183, by rfl⟩ : syracuseStep 20706911 = 31060367) B31060367
theorem B3102313 : Blo 1837620 3102313 := bstep (se 2 (by rfl) ⟨1163367, by rfl⟩ : syracuseStep 3102313 = 2326735) B2326735
theorem B29808445 : Blo 1837620 29808445 := bstep (se 3 (by rfl) ⟨5589083, by rfl⟩ : syracuseStep 29808445 = 11178167) B11178167
theorem B13440875 : Blo 1837620 13440875 := bstep (se 1 (by rfl) ⟨10080656, by rfl⟩ : syracuseStep 13440875 = 20161313) B20161313
theorem B17676413 : Blo 1837620 17676413 := bstep (se 3 (by rfl) ⟨3314327, by rfl⟩ : syracuseStep 17676413 = 6628655) B6628655
theorem B4135103 : Blo 1837620 4135103 := bstep (se 1 (by rfl) ⟨3101327, by rfl⟩ : syracuseStep 4135103 = 6202655) B6202655
theorem B18405667 : Blo 1837620 18405667 := bstep (se 1 (by rfl) ⟨13804250, by rfl⟩ : syracuseStep 18405667 = 27608501) B27608501
theorem B11336111 : Blo 1837620 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B2759135 : Blo 1837620 2759135 := bstep (se 1 (by rfl) ⟨2069351, by rfl⟩ : syracuseStep 2759135 = 4138703) B4138703
theorem B3725927 : Blo 1837620 3725927 := bstep (se 1 (by rfl) ⟨2794445, by rfl⟩ : syracuseStep 3725927 = 5588891) B5588891
theorem B10468075 : Blo 1837620 10468075 := bstep (se 1 (by rfl) ⟨7851056, by rfl⟩ : syracuseStep 10468075 = 15702113) B15702113
theorem B4971385 : Blo 1837620 4971385 := bstep (se 2 (by rfl) ⟨1864269, by rfl⟩ : syracuseStep 4971385 = 3728539) B3728539
theorem B75520937 : Blo 1837620 75520937 := bstep (se 2 (by rfl) ⟨28320351, by rfl⟩ : syracuseStep 75520937 = 56640703) B56640703
theorem B4136219 : Blo 1837620 4136219 := bstep (se 1 (by rfl) ⟨3102164, by rfl⟩ : syracuseStep 4136219 = 6204329) B6204329
theorem B4136399 : Blo 1837620 4136399 := bstep (se 1 (by rfl) ⟨3102299, by rfl⟩ : syracuseStep 4136399 = 6204599) B6204599
theorem B9436655 : Blo 1837620 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B11181671 : Blo 1837620 11181671 := bstep (se 1 (by rfl) ⟨8386253, by rfl⟩ : syracuseStep 11181671 = 16772507) B16772507
theorem B4972313 : Blo 1837620 4972313 := bstep (se 2 (by rfl) ⟨1864617, by rfl⟩ : syracuseStep 4972313 = 3729235) B3729235
theorem B39780233 : Blo 1837620 39780233 := bstep (se 2 (by rfl) ⟨14917587, by rfl⟩ : syracuseStep 39780233 = 29835175) B29835175
theorem B2326583 : Blo 1837620 2326583 := bstep (se 1 (by rfl) ⟨1744937, by rfl⟩ : syracuseStep 2326583 = 3489875) B3489875
theorem B4137119 : Blo 1837620 4137119 := bstep (se 1 (by rfl) ⟨3102839, by rfl⟩ : syracuseStep 4137119 = 6205679) B6205679
theorem B4137479 : Blo 1837620 4137479 := bstep (se 1 (by rfl) ⟨3103109, by rfl⟩ : syracuseStep 4137479 = 6206219) B6206219
theorem B5890639 : Blo 1837620 5890639 := bstep (se 1 (by rfl) ⟨4417979, by rfl⟩ : syracuseStep 5890639 = 8835959) B8835959
theorem B6980327 : Blo 1837620 6980327 := bstep (se 1 (by rfl) ⟨5235245, by rfl⟩ : syracuseStep 6980327 = 10470491) B10470491
theorem B4654057 : Blo 1837620 4654057 := bstep (se 2 (by rfl) ⟨1745271, by rfl⟩ : syracuseStep 4654057 = 3490543) B3490543
theorem B13804607 : Blo 1837620 13804607 := bstep (se 1 (by rfl) ⟨10353455, by rfl⟩ : syracuseStep 13804607 = 20706911) B20706911
theorem B6628513 : Blo 1837620 6628513 := bstep (se 2 (by rfl) ⟨2485692, by rfl⟩ : syracuseStep 6628513 = 4971385) B4971385
theorem B26854577 : Blo 1837620 26854577 := bstep (se 2 (by rfl) ⟨10070466, by rfl⟩ : syracuseStep 26854577 = 20140933) B20140933
theorem B2483951 : Blo 1837620 2483951 := bstep (se 1 (by rfl) ⟨1862963, by rfl⟩ : syracuseStep 2483951 = 3725927) B3725927
theorem B3491743 : Blo 1837620 3491743 := bstep (se 1 (by rfl) ⟨2618807, by rfl⟩ : syracuseStep 3491743 = 5237615) B5237615
theorem B3491903 : Blo 1837620 3491903 := bstep (se 1 (by rfl) ⟨2618927, by rfl⟩ : syracuseStep 3491903 = 5237855) B5237855
theorem B35842333 : Blo 1837620 35842333 := bstep (se 3 (by rfl) ⟨6720437, by rfl⟩ : syracuseStep 35842333 = 13440875) B13440875
theorem B12577193 : Blo 1837620 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B26520155 : Blo 1837620 26520155 := bstep (se 1 (by rfl) ⟨19890116, by rfl⟩ : syracuseStep 26520155 = 39780233) B39780233
theorem B1837927 : Blo 1837620 1837927 := bstep (se 1 (by rfl) ⟨1378445, by rfl⟩ : syracuseStep 1837927 = 2756891) B2756891
theorem B11774945 : Blo 1837620 11774945 := bstep (se 2 (by rfl) ⟨4415604, by rfl⟩ : syracuseStep 11774945 = 8831209) B8831209
theorem B1838363 : Blo 1837620 1838363 := bstep (se 1 (by rfl) ⟨1378772, by rfl⟩ : syracuseStep 1838363 = 2757545) B2757545
theorem B5238071 : Blo 1837620 5238071 := bstep (se 1 (by rfl) ⟨3928553, by rfl⟩ : syracuseStep 5238071 = 7857107) B7857107
theorem B1838759 : Blo 1837620 1838759 := bstep (se 1 (by rfl) ⟨1379069, by rfl⟩ : syracuseStep 1838759 = 2758139) B2758139
theorem B6205193 : Blo 1837620 6205193 := bstep (se 2 (by rfl) ⟨2326947, by rfl⟩ : syracuseStep 6205193 = 4653895) B4653895
theorem B11784275 : Blo 1837620 11784275 := bstep (se 1 (by rfl) ⟨8838206, by rfl⟩ : syracuseStep 11784275 = 17676413) B17676413
theorem B2756735 : Blo 1837620 2756735 := bstep (se 1 (by rfl) ⟨2067551, by rfl⟩ : syracuseStep 2756735 = 4135103) B4135103
theorem B13431035 : Blo 1837620 13431035 := bstep (se 1 (by rfl) ⟨10073276, by rfl⟩ : syracuseStep 13431035 = 20146553) B20146553
theorem B7557407 : Blo 1837620 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B1839423 : Blo 1837620 1839423 := bstep (se 1 (by rfl) ⟨1379567, by rfl⟩ : syracuseStep 1839423 = 2759135) B2759135
theorem B2757161 : Blo 1837620 2757161 := bstep (se 2 (by rfl) ⟨1033935, by rfl⟩ : syracuseStep 2757161 = 2067871) B2067871
theorem B13259501 : Blo 1837620 13259501 := bstep (se 3 (by rfl) ⟨2486156, by rfl⟩ : syracuseStep 13259501 = 4972313) B4972313
theorem B2757479 : Blo 1837620 2757479 := bstep (se 1 (by rfl) ⟨2068109, by rfl⟩ : syracuseStep 2757479 = 4136219) B4136219
theorem B2757599 : Blo 1837620 2757599 := bstep (se 1 (by rfl) ⟨2068199, by rfl⟩ : syracuseStep 2757599 = 4136399) B4136399
theorem B50312177 : Blo 1837620 50312177 := bstep (se 2 (by rfl) ⟨18867066, by rfl⟩ : syracuseStep 50312177 = 37734133) B37734133
theorem B39744593 : Blo 1837620 39744593 := bstep (se 2 (by rfl) ⟨14904222, by rfl⟩ : syracuseStep 39744593 = 29808445) B29808445
theorem B9311759 : Blo 1837620 9311759 := bstep (se 1 (by rfl) ⟨6983819, by rfl⟩ : syracuseStep 9311759 = 13967639) B13967639
theorem B6207083 : Blo 1837620 6207083 := bstep (se 1 (by rfl) ⟨4655312, by rfl⟩ : syracuseStep 6207083 = 9310625) B9310625
theorem B159078005 : Blo 1837620 159078005 := bstep (se 5 (by rfl) ⟨7456781, by rfl⟩ : syracuseStep 159078005 = 14913563) B14913563
theorem B11777663 : Blo 1837620 11777663 := bstep (se 1 (by rfl) ⟨8833247, by rfl⟩ : syracuseStep 11777663 = 17666495) B17666495
theorem B2758313 : Blo 1837620 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B24540889 : Blo 1837620 24540889 := bstep (se 2 (by rfl) ⟨9202833, by rfl⟩ : syracuseStep 24540889 = 18405667) B18405667
theorem B2758439 : Blo 1837620 2758439 := bstep (se 1 (by rfl) ⟨2068829, by rfl⟩ : syracuseStep 2758439 = 4137659) B4137659
theorem B70661969 : Blo 1837620 70661969 := bstep (se 2 (by rfl) ⟨26498238, by rfl⟩ : syracuseStep 70661969 = 52996477) B52996477
theorem B2758511 : Blo 1837620 2758511 := bstep (se 1 (by rfl) ⟨2068883, by rfl⟩ : syracuseStep 2758511 = 4137767) B4137767
theorem B6207515 : Blo 1837620 6207515 := bstep (se 1 (by rfl) ⟨4655636, by rfl⟩ : syracuseStep 6207515 = 9311273) B9311273
theorem B2758697 : Blo 1837620 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B6207677 : Blo 1837620 6207677 := bstep (se 3 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 6207677 = 2327879) B2327879
theorem B13957433 : Blo 1837620 13957433 := bstep (se 2 (by rfl) ⟨5234037, by rfl⟩ : syracuseStep 13957433 = 10468075) B10468075
theorem B2759111 : Blo 1837620 2759111 := bstep (se 1 (by rfl) ⟨2069333, by rfl⟩ : syracuseStep 2759111 = 4138667) B4138667
theorem B23551073 : Blo 1837620 23551073 := bstep (se 2 (by rfl) ⟨8831652, by rfl⟩ : syracuseStep 23551073 = 17663305) B17663305
theorem B50347291 : Blo 1837620 50347291 := bstep (se 1 (by rfl) ⟨37760468, by rfl⟩ : syracuseStep 50347291 = 75520937) B75520937
theorem B35347751 : Blo 1837620 35347751 := bstep (se 1 (by rfl) ⟨26510813, by rfl⟩ : syracuseStep 35347751 = 53021627) B53021627
theorem B4136417 : Blo 1837620 4136417 := bstep (se 2 (by rfl) ⟨1551156, by rfl⟩ : syracuseStep 4136417 = 3102313) B3102313
theorem B3104311 : Blo 1837620 3104311 := bstep (se 1 (by rfl) ⟨2328233, by rfl⟩ : syracuseStep 3104311 = 4656467) B4656467
theorem B29810267 : Blo 1837620 29810267 := bstep (se 1 (by rfl) ⟨22357700, by rfl⟩ : syracuseStep 29810267 = 44715401) B44715401
theorem B6291103 : Blo 1837620 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B7454447 : Blo 1837620 7454447 := bstep (se 1 (by rfl) ⟨5590835, by rfl⟩ : syracuseStep 7454447 = 11181671) B11181671
theorem B37732229 : Blo 1837620 37732229 := bstep (se 4 (by rfl) ⟨3537396, by rfl⟩ : syracuseStep 37732229 = 7074793) B7074793
theorem B7856183 : Blo 1837620 7856183 := bstep (se 1 (by rfl) ⟨5892137, by rfl⟩ : syracuseStep 7856183 = 11784275) B11784275
theorem B8954023 : Blo 1837620 8954023 := bstep (se 1 (by rfl) ⟨6715517, by rfl⟩ : syracuseStep 8954023 = 13431035) B13431035
theorem B5038271 : Blo 1837620 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B4653551 : Blo 1837620 4653551 := bstep (se 1 (by rfl) ⟨3490163, by rfl⟩ : syracuseStep 4653551 = 6980327) B6980327
theorem B8839667 : Blo 1837620 8839667 := bstep (se 1 (by rfl) ⟨6629750, by rfl⟩ : syracuseStep 8839667 = 13259501) B13259501
theorem B4138055 : Blo 1837620 4138055 := bstep (se 1 (by rfl) ⟨3103541, by rfl⟩ : syracuseStep 4138055 = 6207083) B6207083
theorem B4138343 : Blo 1837620 4138343 := bstep (se 1 (by rfl) ⟨3103757, by rfl⟩ : syracuseStep 4138343 = 6207515) B6207515
theorem B2327935 : Blo 1837620 2327935 := bstep (se 1 (by rfl) ⟨1745951, by rfl⟩ : syracuseStep 2327935 = 3491903) B3491903
theorem B4138451 : Blo 1837620 4138451 := bstep (se 1 (by rfl) ⟨3103838, by rfl⟩ : syracuseStep 4138451 = 6207677) B6207677
theorem B17680103 : Blo 1837620 17680103 := bstep (se 1 (by rfl) ⟨13260077, by rfl⟩ : syracuseStep 17680103 = 26520155) B26520155
theorem B7849963 : Blo 1837620 7849963 := bstep (se 1 (by rfl) ⟨5887472, by rfl⟩ : syracuseStep 7849963 = 11774945) B11774945
theorem B4139081 : Blo 1837620 4139081 := bstep (se 2 (by rfl) ⟨1552155, by rfl⟩ : syracuseStep 4139081 = 3104311) B3104311
theorem B3492047 : Blo 1837620 3492047 := bstep (se 1 (by rfl) ⟨2619035, by rfl⟩ : syracuseStep 3492047 = 5238071) B5238071
theorem B32721185 : Blo 1837620 32721185 := bstep (se 2 (by rfl) ⟨12270444, by rfl⟩ : syracuseStep 32721185 = 24540889) B24540889
theorem B4655657 : Blo 1837620 4655657 := bstep (se 2 (by rfl) ⟨1745871, by rfl⟩ : syracuseStep 4655657 = 3491743) B3491743
theorem B1837823 : Blo 1837620 1837823 := bstep (se 1 (by rfl) ⟨1378367, by rfl⟩ : syracuseStep 1837823 = 2756735) B2756735
theorem B6204221 : Blo 1837620 6204221 := bstep (se 3 (by rfl) ⟨1163291, by rfl⟩ : syracuseStep 6204221 = 2326583) B2326583
theorem B1838107 : Blo 1837620 1838107 := bstep (se 1 (by rfl) ⟨1378580, by rfl⟩ : syracuseStep 1838107 = 2757161) B2757161
theorem B1838319 : Blo 1837620 1838319 := bstep (se 1 (by rfl) ⟨1378739, by rfl⟩ : syracuseStep 1838319 = 2757479) B2757479
theorem B1838399 : Blo 1837620 1838399 := bstep (se 1 (by rfl) ⟨1378799, by rfl⟩ : syracuseStep 1838399 = 2757599) B2757599
theorem B33541451 : Blo 1837620 33541451 := bstep (se 1 (by rfl) ⟨25156088, by rfl⟩ : syracuseStep 33541451 = 50312177) B50312177
theorem B9203071 : Blo 1837620 9203071 := bstep (se 1 (by rfl) ⟨6902303, by rfl⟩ : syracuseStep 9203071 = 13804607) B13804607
theorem B26496395 : Blo 1837620 26496395 := bstep (se 1 (by rfl) ⟨19872296, by rfl⟩ : syracuseStep 26496395 = 39744593) B39744593
theorem B17903051 : Blo 1837620 17903051 := bstep (se 1 (by rfl) ⟨13427288, by rfl⟩ : syracuseStep 17903051 = 26854577) B26854577
theorem B7851775 : Blo 1837620 7851775 := bstep (se 1 (by rfl) ⟨5888831, by rfl⟩ : syracuseStep 7851775 = 11777663) B11777663
theorem B1838875 : Blo 1837620 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B1838959 : Blo 1837620 1838959 := bstep (se 1 (by rfl) ⟨1379219, by rfl⟩ : syracuseStep 1838959 = 2758439) B2758439
theorem B47107979 : Blo 1837620 47107979 := bstep (se 1 (by rfl) ⟨35330984, by rfl⟩ : syracuseStep 47107979 = 70661969) B70661969
theorem B1839007 : Blo 1837620 1839007 := bstep (se 1 (by rfl) ⟨1379255, by rfl⟩ : syracuseStep 1839007 = 2758511) B2758511
theorem B6205409 : Blo 1837620 6205409 := bstep (se 2 (by rfl) ⟨2327028, by rfl⟩ : syracuseStep 6205409 = 4654057) B4654057
theorem B1839131 : Blo 1837620 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B8384795 : Blo 1837620 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B1839407 : Blo 1837620 1839407 := bstep (se 1 (by rfl) ⟨1379555, by rfl⟩ : syracuseStep 1839407 = 2759111) B2759111
theorem B67129721 : Blo 1837620 67129721 := bstep (se 2 (by rfl) ⟨25173645, by rfl⟩ : syracuseStep 67129721 = 50347291) B50347291
theorem B6623869 : Blo 1837620 6623869 := bstep (se 3 (by rfl) ⟨1241975, by rfl⟩ : syracuseStep 6623869 = 2483951) B2483951
theorem B15700715 : Blo 1837620 15700715 := bstep (se 1 (by rfl) ⟨11775536, by rfl⟩ : syracuseStep 15700715 = 23551073) B23551073
theorem B23565167 : Blo 1837620 23565167 := bstep (se 1 (by rfl) ⟨17673875, by rfl⟩ : syracuseStep 23565167 = 35347751) B35347751
theorem B2757611 : Blo 1837620 2757611 := bstep (se 1 (by rfl) ⟨2068208, by rfl⟩ : syracuseStep 2757611 = 4136417) B4136417
theorem B4969631 : Blo 1837620 4969631 := bstep (se 1 (by rfl) ⟨3727223, by rfl⟩ : syracuseStep 4969631 = 7454447) B7454447
theorem B25154819 : Blo 1837620 25154819 := bstep (se 1 (by rfl) ⟨18866114, by rfl⟩ : syracuseStep 25154819 = 37732229) B37732229
theorem B2758079 : Blo 1837620 2758079 := bstep (se 1 (by rfl) ⟨2068559, by rfl⟩ : syracuseStep 2758079 = 4137119) B4137119
theorem B2758319 : Blo 1837620 2758319 := bstep (se 1 (by rfl) ⟨2068739, by rfl⟩ : syracuseStep 2758319 = 4137479) B4137479
theorem B47789777 : Blo 1837620 47789777 := bstep (se 2 (by rfl) ⟨17921166, by rfl⟩ : syracuseStep 47789777 = 35842333) B35842333
theorem B7854185 : Blo 1837620 7854185 := bstep (se 2 (by rfl) ⟨2945319, by rfl⟩ : syracuseStep 7854185 = 5890639) B5890639
theorem B6207839 : Blo 1837620 6207839 := bstep (se 1 (by rfl) ⟨4655879, by rfl⟩ : syracuseStep 6207839 = 9311759) B9311759
theorem B106052003 : Blo 1837620 106052003 := bstep (se 1 (by rfl) ⟨79539002, by rfl⟩ : syracuseStep 106052003 = 159078005) B159078005
theorem B9304955 : Blo 1837620 9304955 := bstep (se 1 (by rfl) ⟨6978716, by rfl⟩ : syracuseStep 9304955 = 13957433) B13957433
theorem B8838017 : Blo 1837620 8838017 := bstep (se 2 (by rfl) ⟨3314256, by rfl⟩ : syracuseStep 8838017 = 6628513) B6628513
theorem B8388137 : Blo 1837620 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B19873511 : Blo 1837620 19873511 := bstep (se 1 (by rfl) ⟨14905133, by rfl⟩ : syracuseStep 19873511 = 29810267) B29810267
theorem B4136795 : Blo 1837620 4136795 := bstep (se 1 (by rfl) ⟨3102596, by rfl⟩ : syracuseStep 4136795 = 6205193) B6205193
theorem B3358847 : Blo 1837620 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B44753147 : Blo 1837620 44753147 := bstep (se 1 (by rfl) ⟨33564860, by rfl⟩ : syracuseStep 44753147 = 67129721) B67129721
theorem B8831825 : Blo 1837620 8831825 := bstep (se 2 (by rfl) ⟨3311934, by rfl⟩ : syracuseStep 8831825 = 6623869) B6623869
theorem B16769879 : Blo 1837620 16769879 := bstep (se 1 (by rfl) ⟨12577409, by rfl⟩ : syracuseStep 16769879 = 25154819) B25154819
theorem B31859851 : Blo 1837620 31859851 := bstep (se 1 (by rfl) ⟨23894888, by rfl⟩ : syracuseStep 31859851 = 47789777) B47789777
theorem B5236123 : Blo 1837620 5236123 := bstep (se 1 (by rfl) ⟨3927092, by rfl⟩ : syracuseStep 5236123 = 7854185) B7854185
theorem B2328031 : Blo 1837620 2328031 := bstep (se 1 (by rfl) ⟨1746023, by rfl⟩ : syracuseStep 2328031 = 3492047) B3492047
theorem B4138559 : Blo 1837620 4138559 := bstep (se 1 (by rfl) ⟨3103919, by rfl⟩ : syracuseStep 4138559 = 6207839) B6207839
theorem B6203303 : Blo 1837620 6203303 := bstep (se 1 (by rfl) ⟨4652477, by rfl⟩ : syracuseStep 6203303 = 9304955) B9304955
theorem B5892011 : Blo 1837620 5892011 := bstep (se 1 (by rfl) ⟨4419008, by rfl⟩ : syracuseStep 5892011 = 8838017) B8838017
theorem B17664263 : Blo 1837620 17664263 := bstep (se 1 (by rfl) ⟨13248197, by rfl⟩ : syracuseStep 17664263 = 26496395) B26496395
theorem B13249007 : Blo 1837620 13249007 := bstep (se 1 (by rfl) ⟨9936755, by rfl⟩ : syracuseStep 13249007 = 19873511) B19873511
theorem B5237455 : Blo 1837620 5237455 := bstep (se 1 (by rfl) ⟨3928091, by rfl⟩ : syracuseStep 5237455 = 7856183) B7856183
theorem B5589863 : Blo 1837620 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B11938697 : Blo 1837620 11938697 := bstep (se 2 (by rfl) ⟨4477011, by rfl⟩ : syracuseStep 11938697 = 8954023) B8954023
theorem B5893111 : Blo 1837620 5893111 := bstep (se 1 (by rfl) ⟨4419833, by rfl⟩ : syracuseStep 5893111 = 8839667) B8839667
theorem B1838407 : Blo 1837620 1838407 := bstep (se 1 (by rfl) ⟨1378805, by rfl⟩ : syracuseStep 1838407 = 2757611) B2757611
theorem B1838719 : Blo 1837620 1838719 := bstep (se 1 (by rfl) ⟨1379039, by rfl⟩ : syracuseStep 1838719 = 2758079) B2758079
theorem B1838879 : Blo 1837620 1838879 := bstep (se 1 (by rfl) ⟨1379159, by rfl⟩ : syracuseStep 1838879 = 2758319) B2758319
theorem B70701335 : Blo 1837620 70701335 := bstep (se 1 (by rfl) ⟨53026001, by rfl⟩ : syracuseStep 70701335 = 106052003) B106052003
theorem B22360967 : Blo 1837620 22360967 := bstep (se 1 (by rfl) ⟨16770725, by rfl⟩ : syracuseStep 22360967 = 33541451) B33541451
theorem B5592091 : Blo 1837620 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B2757863 : Blo 1837620 2757863 := bstep (se 1 (by rfl) ⟨2068397, by rfl⟩ : syracuseStep 2757863 = 4136795) B4136795
theorem B31405319 : Blo 1837620 31405319 := bstep (se 1 (by rfl) ⟨23553989, by rfl⟩ : syracuseStep 31405319 = 47107979) B47107979
theorem B10466617 : Blo 1837620 10466617 := bstep (se 2 (by rfl) ⟨3924981, by rfl⟩ : syracuseStep 10466617 = 7849963) B7849963
theorem B3102367 : Blo 1837620 3102367 := bstep (se 1 (by rfl) ⟨2326775, by rfl⟩ : syracuseStep 3102367 = 4653551) B4653551
theorem B13252349 : Blo 1837620 13252349 := bstep (se 3 (by rfl) ⟨2484815, by rfl⟩ : syracuseStep 13252349 = 4969631) B4969631
theorem B10467143 : Blo 1837620 10467143 := bstep (se 1 (by rfl) ⟨7850357, by rfl⟩ : syracuseStep 10467143 = 15700715) B15700715
theorem B15710111 : Blo 1837620 15710111 := bstep (se 1 (by rfl) ⟨11782583, by rfl⟩ : syracuseStep 15710111 = 23565167) B23565167
theorem B2758703 : Blo 1837620 2758703 := bstep (se 1 (by rfl) ⟨2069027, by rfl⟩ : syracuseStep 2758703 = 4138055) B4138055
theorem B2758895 : Blo 1837620 2758895 := bstep (se 1 (by rfl) ⟨2069171, by rfl⟩ : syracuseStep 2758895 = 4138343) B4138343
theorem B2758967 : Blo 1837620 2758967 := bstep (se 1 (by rfl) ⟨2069225, by rfl⟩ : syracuseStep 2758967 = 4138451) B4138451
theorem B11786735 : Blo 1837620 11786735 := bstep (se 1 (by rfl) ⟨8840051, by rfl⟩ : syracuseStep 11786735 = 17680103) B17680103
theorem B2759387 : Blo 1837620 2759387 := bstep (se 1 (by rfl) ⟨2069540, by rfl⟩ : syracuseStep 2759387 = 4139081) B4139081
theorem B21814123 : Blo 1837620 21814123 := bstep (se 1 (by rfl) ⟨16360592, by rfl⟩ : syracuseStep 21814123 = 32721185) B32721185
theorem B3103771 : Blo 1837620 3103771 := bstep (se 1 (by rfl) ⟨2327828, by rfl⟩ : syracuseStep 3103771 = 4655657) B4655657
theorem B12270761 : Blo 1837620 12270761 := bstep (se 2 (by rfl) ⟨4601535, by rfl⟩ : syracuseStep 12270761 = 9203071) B9203071
theorem B3103913 : Blo 1837620 3103913 := bstep (se 2 (by rfl) ⟨1163967, by rfl⟩ : syracuseStep 3103913 = 2327935) B2327935
theorem B4136147 : Blo 1837620 4136147 := bstep (se 1 (by rfl) ⟨3102110, by rfl⟩ : syracuseStep 4136147 = 6204221) B6204221
theorem B11935367 : Blo 1837620 11935367 := bstep (se 1 (by rfl) ⟨8951525, by rfl⟩ : syracuseStep 11935367 = 17903051) B17903051
theorem B10469033 : Blo 1837620 10469033 := bstep (se 2 (by rfl) ⟨3925887, by rfl⟩ : syracuseStep 10469033 = 7851775) B7851775
theorem B4136939 : Blo 1837620 4136939 := bstep (se 1 (by rfl) ⟨3102704, by rfl⟩ : syracuseStep 4136939 = 6205409) B6205409
theorem B29835431 : Blo 1837620 29835431 := bstep (se 1 (by rfl) ⟨22376573, by rfl⟩ : syracuseStep 29835431 = 44753147) B44753147
theorem B7857481 : Blo 1837620 7857481 := bstep (se 2 (by rfl) ⟨2946555, by rfl⟩ : syracuseStep 7857481 = 5893111) B5893111
theorem B7456121 : Blo 1837620 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B4138361 : Blo 1837620 4138361 := bstep (se 2 (by rfl) ⟨1551885, by rfl⟩ : syracuseStep 4138361 = 3103771) B3103771
theorem B8832671 : Blo 1837620 8832671 := bstep (se 1 (by rfl) ⟨6624503, by rfl⟩ : syracuseStep 8832671 = 13249007) B13249007
theorem B7857823 : Blo 1837620 7857823 := bstep (se 1 (by rfl) ⟨5893367, by rfl⟩ : syracuseStep 7857823 = 11786735) B11786735
theorem B6981497 : Blo 1837620 6981497 := bstep (se 2 (by rfl) ⟨2618061, by rfl⟩ : syracuseStep 6981497 = 5236123) B5236123
theorem B7956911 : Blo 1837620 7956911 := bstep (se 1 (by rfl) ⟨5967683, by rfl⟩ : syracuseStep 7956911 = 11935367) B11935367
theorem B2239231 : Blo 1837620 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B1838575 : Blo 1837620 1838575 := bstep (se 1 (by rfl) ⟨1378931, by rfl⟩ : syracuseStep 1838575 = 2757863) B2757863
theorem B6983273 : Blo 1837620 6983273 := bstep (se 2 (by rfl) ⟨2618727, by rfl⟩ : syracuseStep 6983273 = 5237455) B5237455
theorem B29085497 : Blo 1837620 29085497 := bstep (se 2 (by rfl) ⟨10907061, by rfl⟩ : syracuseStep 29085497 = 21814123) B21814123
theorem B10473407 : Blo 1837620 10473407 := bstep (se 1 (by rfl) ⟨7855055, by rfl⟩ : syracuseStep 10473407 = 15710111) B15710111
theorem B3928007 : Blo 1837620 3928007 := bstep (se 1 (by rfl) ⟨2946005, by rfl⟩ : syracuseStep 3928007 = 5892011) B5892011
theorem B1839135 : Blo 1837620 1839135 := bstep (se 1 (by rfl) ⟨1379351, by rfl⟩ : syracuseStep 1839135 = 2758703) B2758703
theorem B1839263 : Blo 1837620 1839263 := bstep (se 1 (by rfl) ⟨1379447, by rfl⟩ : syracuseStep 1839263 = 2758895) B2758895
theorem B11776175 : Blo 1837620 11776175 := bstep (se 1 (by rfl) ⟨8832131, by rfl⟩ : syracuseStep 11776175 = 17664263) B17664263
theorem B42479801 : Blo 1837620 42479801 := bstep (se 2 (by rfl) ⟨15929925, by rfl⟩ : syracuseStep 42479801 = 31859851) B31859851
theorem B1839311 : Blo 1837620 1839311 := bstep (se 1 (by rfl) ⟨1379483, by rfl⟩ : syracuseStep 1839311 = 2758967) B2758967
theorem B13955489 : Blo 1837620 13955489 := bstep (se 2 (by rfl) ⟨5233308, by rfl⟩ : syracuseStep 13955489 = 10466617) B10466617
theorem B1839591 : Blo 1837620 1839591 := bstep (se 1 (by rfl) ⟨1379693, by rfl⟩ : syracuseStep 1839591 = 2759387) B2759387
theorem B7959131 : Blo 1837620 7959131 := bstep (se 1 (by rfl) ⟨5969348, by rfl⟩ : syracuseStep 7959131 = 11938697) B11938697
theorem B8180507 : Blo 1837620 8180507 := bstep (se 1 (by rfl) ⟨6135380, by rfl⟩ : syracuseStep 8180507 = 12270761) B12270761
theorem B2069275 : Blo 1837620 2069275 := bstep (se 1 (by rfl) ⟨1551956, by rfl⟩ : syracuseStep 2069275 = 3103913) B3103913
theorem B2757431 : Blo 1837620 2757431 := bstep (se 1 (by rfl) ⟨2068073, by rfl⟩ : syracuseStep 2757431 = 4136147) B4136147
theorem B2757959 : Blo 1837620 2757959 := bstep (se 1 (by rfl) ⟨2068469, by rfl⟩ : syracuseStep 2757959 = 4136939) B4136939
theorem B47134223 : Blo 1837620 47134223 := bstep (se 1 (by rfl) ⟨35350667, by rfl⟩ : syracuseStep 47134223 = 70701335) B70701335
theorem B5887883 : Blo 1837620 5887883 := bstep (se 1 (by rfl) ⟨4415912, by rfl⟩ : syracuseStep 5887883 = 8831825) B8831825
theorem B11179919 : Blo 1837620 11179919 := bstep (se 1 (by rfl) ⟨8384939, by rfl⟩ : syracuseStep 11179919 = 16769879) B16769879
theorem B14907311 : Blo 1837620 14907311 := bstep (se 1 (by rfl) ⟨11180483, by rfl⟩ : syracuseStep 14907311 = 22360967) B22360967
theorem B20936879 : Blo 1837620 20936879 := bstep (se 1 (by rfl) ⟨15702659, by rfl⟩ : syracuseStep 20936879 = 31405319) B31405319
theorem B2759039 : Blo 1837620 2759039 := bstep (se 1 (by rfl) ⟨2069279, by rfl⟩ : syracuseStep 2759039 = 4138559) B4138559
theorem B6978095 : Blo 1837620 6978095 := bstep (se 1 (by rfl) ⟨5233571, by rfl⟩ : syracuseStep 6978095 = 10467143) B10467143
theorem B4135535 : Blo 1837620 4135535 := bstep (se 1 (by rfl) ⟨3101651, by rfl⟩ : syracuseStep 4135535 = 6203303) B6203303
theorem B3726575 : Blo 1837620 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B3104041 : Blo 1837620 3104041 := bstep (se 2 (by rfl) ⟨1164015, by rfl⟩ : syracuseStep 3104041 = 2328031) B2328031
theorem B35339597 : Blo 1837620 35339597 := bstep (se 3 (by rfl) ⟨6626174, by rfl⟩ : syracuseStep 35339597 = 13252349) B13252349
theorem B4136489 : Blo 1837620 4136489 := bstep (se 2 (by rfl) ⟨1551183, by rfl⟩ : syracuseStep 4136489 = 3102367) B3102367
theorem B6979355 : Blo 1837620 6979355 := bstep (se 1 (by rfl) ⟨5234516, by rfl⟩ : syracuseStep 6979355 = 10469033) B10469033
theorem B19890287 : Blo 1837620 19890287 := bstep (se 1 (by rfl) ⟨14917715, by rfl⟩ : syracuseStep 19890287 = 29835431) B29835431
theorem B28319867 : Blo 1837620 28319867 := bstep (se 1 (by rfl) ⟨21239900, by rfl⟩ : syracuseStep 28319867 = 42479801) B42479801
theorem B21218429 : Blo 1837620 21218429 := bstep (se 3 (by rfl) ⟨3978455, by rfl⟩ : syracuseStep 21218429 = 7956911) B7956911
theorem B4654331 : Blo 1837620 4654331 := bstep (se 1 (by rfl) ⟨3490748, by rfl⟩ : syracuseStep 4654331 = 6981497) B6981497
theorem B3925255 : Blo 1837620 3925255 := bstep (se 1 (by rfl) ⟨2943941, by rfl⟩ : syracuseStep 3925255 = 5887883) B5887883
theorem B9938207 : Blo 1837620 9938207 := bstep (se 1 (by rfl) ⟨7453655, by rfl⟩ : syracuseStep 9938207 = 14907311) B14907311
theorem B4138721 : Blo 1837620 4138721 := bstep (se 2 (by rfl) ⟨1552020, by rfl⟩ : syracuseStep 4138721 = 3104041) B3104041
theorem B2484383 : Blo 1837620 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B4655515 : Blo 1837620 4655515 := bstep (se 1 (by rfl) ⟨3491636, by rfl⟩ : syracuseStep 4655515 = 6983273) B6983273
theorem B6982271 : Blo 1837620 6982271 := bstep (se 1 (by rfl) ⟨5236703, by rfl⟩ : syracuseStep 6982271 = 10473407) B10473407
theorem B7850783 : Blo 1837620 7850783 := bstep (se 1 (by rfl) ⟨5888087, by rfl⟩ : syracuseStep 7850783 = 11776175) B11776175
theorem B1838287 : Blo 1837620 1838287 := bstep (se 1 (by rfl) ⟨1378715, by rfl⟩ : syracuseStep 1838287 = 2757431) B2757431
theorem B1838639 : Blo 1837620 1838639 := bstep (se 1 (by rfl) ⟨1378979, by rfl⟩ : syracuseStep 1838639 = 2757959) B2757959
theorem B2985641 : Blo 1837620 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B1839359 : Blo 1837620 1839359 := bstep (se 1 (by rfl) ⟨1379519, by rfl⟩ : syracuseStep 1839359 = 2759039) B2759039
theorem B2757023 : Blo 1837620 2757023 := bstep (se 1 (by rfl) ⟨2067767, by rfl⟩ : syracuseStep 2757023 = 4135535) B4135535
theorem B2757659 : Blo 1837620 2757659 := bstep (se 1 (by rfl) ⟨2068244, by rfl⟩ : syracuseStep 2757659 = 4136489) B4136489
theorem B2618671 : Blo 1837620 2618671 := bstep (se 1 (by rfl) ⟨1964003, by rfl⟩ : syracuseStep 2618671 = 3928007) B3928007
theorem B9303659 : Blo 1837620 9303659 := bstep (se 1 (by rfl) ⟨6977744, by rfl⟩ : syracuseStep 9303659 = 13955489) B13955489
theorem B5306087 : Blo 1837620 5306087 := bstep (se 1 (by rfl) ⟨3979565, by rfl⟩ : syracuseStep 5306087 = 7959131) B7959131
theorem B4970747 : Blo 1837620 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B2758907 : Blo 1837620 2758907 := bstep (se 1 (by rfl) ⟨2069180, by rfl⟩ : syracuseStep 2758907 = 4138361) B4138361
theorem B31422815 : Blo 1837620 31422815 := bstep (se 1 (by rfl) ⟨23567111, by rfl⟩ : syracuseStep 31422815 = 47134223) B47134223
theorem B2759033 : Blo 1837620 2759033 := bstep (se 2 (by rfl) ⟨1034637, by rfl⟩ : syracuseStep 2759033 = 2069275) B2069275
theorem B5888447 : Blo 1837620 5888447 := bstep (se 1 (by rfl) ⟨4416335, by rfl⟩ : syracuseStep 5888447 = 8832671) B8832671
theorem B7453279 : Blo 1837620 7453279 := bstep (se 1 (by rfl) ⟨5589959, by rfl⟩ : syracuseStep 7453279 = 11179919) B11179919
theorem B13957919 : Blo 1837620 13957919 := bstep (se 1 (by rfl) ⟨10468439, by rfl⟩ : syracuseStep 13957919 = 20936879) B20936879
theorem B4652063 : Blo 1837620 4652063 := bstep (se 1 (by rfl) ⟨3489047, by rfl⟩ : syracuseStep 4652063 = 6978095) B6978095
theorem B10476641 : Blo 1837620 10476641 := bstep (se 2 (by rfl) ⟨3928740, by rfl⟩ : syracuseStep 10476641 = 7857481) B7857481
theorem B21814685 : Blo 1837620 21814685 := bstep (se 3 (by rfl) ⟨4090253, by rfl⟩ : syracuseStep 21814685 = 8180507) B8180507
theorem B10477097 : Blo 1837620 10477097 := bstep (se 2 (by rfl) ⟨3928911, by rfl⟩ : syracuseStep 10477097 = 7857823) B7857823
theorem B23559731 : Blo 1837620 23559731 := bstep (se 1 (by rfl) ⟨17669798, by rfl⟩ : syracuseStep 23559731 = 35339597) B35339597
theorem B4652903 : Blo 1837620 4652903 := bstep (se 1 (by rfl) ⟨3489677, by rfl⟩ : syracuseStep 4652903 = 6979355) B6979355
theorem B19390331 : Blo 1837620 19390331 := bstep (se 1 (by rfl) ⟨14542748, by rfl⟩ : syracuseStep 19390331 = 29085497) B29085497
theorem B13255325 : Blo 1837620 13255325 := bstep (se 3 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 13255325 = 4970747) B4970747
theorem B6202439 : Blo 1837620 6202439 := bstep (se 1 (by rfl) ⟨4651829, by rfl⟩ : syracuseStep 6202439 = 9303659) B9303659
theorem B20948543 : Blo 1837620 20948543 := bstep (se 1 (by rfl) ⟨15711407, by rfl⟩ : syracuseStep 20948543 = 31422815) B31422815
theorem B3925631 : Blo 1837620 3925631 := bstep (se 1 (by rfl) ⟨2944223, by rfl⟩ : syracuseStep 3925631 = 5888447) B5888447
theorem B3491561 : Blo 1837620 3491561 := bstep (se 2 (by rfl) ⟨1309335, by rfl⟩ : syracuseStep 3491561 = 2618671) B2618671
theorem B4654847 : Blo 1837620 4654847 := bstep (se 1 (by rfl) ⟨3491135, by rfl⟩ : syracuseStep 4654847 = 6982271) B6982271
theorem B14543123 : Blo 1837620 14543123 := bstep (se 1 (by rfl) ⟨10907342, by rfl⟩ : syracuseStep 14543123 = 21814685) B21814685
theorem B15706487 : Blo 1837620 15706487 := bstep (se 1 (by rfl) ⟨11779865, by rfl⟩ : syracuseStep 15706487 = 23559731) B23559731
theorem B1838015 : Blo 1837620 1838015 := bstep (se 1 (by rfl) ⟨1378511, by rfl⟩ : syracuseStep 1838015 = 2757023) B2757023
theorem B39750821 : Blo 1837620 39750821 := bstep (se 4 (by rfl) ⟨3726639, by rfl⟩ : syracuseStep 39750821 = 7453279) B7453279
theorem B1838439 : Blo 1837620 1838439 := bstep (se 1 (by rfl) ⟨1378829, by rfl⟩ : syracuseStep 1838439 = 2757659) B2757659
theorem B1839271 : Blo 1837620 1839271 := bstep (se 1 (by rfl) ⟨1379453, by rfl⟩ : syracuseStep 1839271 = 2758907) B2758907
theorem B1839355 : Blo 1837620 1839355 := bstep (se 1 (by rfl) ⟨1379516, by rfl⟩ : syracuseStep 1839355 = 2759033) B2759033
theorem B3101375 : Blo 1837620 3101375 := bstep (se 1 (by rfl) ⟨2326031, by rfl⟩ : syracuseStep 3101375 = 4652063) B4652063
theorem B6984427 : Blo 1837620 6984427 := bstep (se 1 (by rfl) ⟨5238320, by rfl⟩ : syracuseStep 6984427 = 10476641) B10476641
theorem B20935421 : Blo 1837620 20935421 := bstep (se 3 (by rfl) ⟨3925391, by rfl⟩ : syracuseStep 20935421 = 7850783) B7850783
theorem B6984731 : Blo 1837620 6984731 := bstep (se 1 (by rfl) ⟨5238548, by rfl⟩ : syracuseStep 6984731 = 10477097) B10477097
theorem B3101935 : Blo 1837620 3101935 := bstep (se 1 (by rfl) ⟨2326451, by rfl⟩ : syracuseStep 3101935 = 4652903) B4652903
theorem B13260191 : Blo 1837620 13260191 := bstep (se 1 (by rfl) ⟨9945143, by rfl⟩ : syracuseStep 13260191 = 19890287) B19890287
theorem B18879911 : Blo 1837620 18879911 := bstep (se 1 (by rfl) ⟨14159933, by rfl⟩ : syracuseStep 18879911 = 28319867) B28319867
theorem B6207353 : Blo 1837620 6207353 := bstep (se 2 (by rfl) ⟨2327757, by rfl⟩ : syracuseStep 6207353 = 4655515) B4655515
theorem B14145619 : Blo 1837620 14145619 := bstep (se 1 (by rfl) ⟨10609214, by rfl⟩ : syracuseStep 14145619 = 21218429) B21218429
theorem B3102887 : Blo 1837620 3102887 := bstep (se 1 (by rfl) ⟨2327165, by rfl⟩ : syracuseStep 3102887 = 4654331) B4654331
theorem B6625471 : Blo 1837620 6625471 := bstep (se 1 (by rfl) ⟨4969103, by rfl⟩ : syracuseStep 6625471 = 9938207) B9938207
theorem B2759147 : Blo 1837620 2759147 := bstep (se 1 (by rfl) ⟨2069360, by rfl⟩ : syracuseStep 2759147 = 4138721) B4138721
theorem B3537391 : Blo 1837620 3537391 := bstep (se 1 (by rfl) ⟨2653043, by rfl⟩ : syracuseStep 3537391 = 5306087) B5306087
theorem B26500085 : Blo 1837620 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B5233673 : Blo 1837620 5233673 := bstep (se 2 (by rfl) ⟨1962627, by rfl⟩ : syracuseStep 5233673 = 3925255) B3925255
theorem B9305279 : Blo 1837620 9305279 := bstep (se 1 (by rfl) ⟨6978959, by rfl⟩ : syracuseStep 9305279 = 13957919) B13957919
theorem B51707549 : Blo 1837620 51707549 := bstep (se 3 (by rfl) ⟨9695165, by rfl⟩ : syracuseStep 51707549 = 19390331) B19390331
theorem B1990427 : Blo 1837620 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B38781661 : Blo 1837620 38781661 := bstep (se 3 (by rfl) ⟨7271561, by rfl⟩ : syracuseStep 38781661 = 14543123) B14543123
theorem B2327707 : Blo 1837620 2327707 := bstep (se 1 (by rfl) ⟨1745780, by rfl⟩ : syracuseStep 2327707 = 3491561) B3491561
theorem B4138235 : Blo 1837620 4138235 := bstep (se 1 (by rfl) ⟨3103676, by rfl⟩ : syracuseStep 4138235 = 6207353) B6207353
theorem B10470991 : Blo 1837620 10470991 := bstep (se 1 (by rfl) ⟨7853243, by rfl⟩ : syracuseStep 10470991 = 15706487) B15706487
theorem B6203519 : Blo 1837620 6203519 := bstep (se 1 (by rfl) ⟨4652639, by rfl⟩ : syracuseStep 6203519 = 9305279) B9305279
theorem B18860825 : Blo 1837620 18860825 := bstep (se 2 (by rfl) ⟨7072809, by rfl⟩ : syracuseStep 18860825 = 14145619) B14145619
theorem B8833961 : Blo 1837620 8833961 := bstep (se 2 (by rfl) ⟨3312735, by rfl⟩ : syracuseStep 8833961 = 6625471) B6625471
theorem B2067583 : Blo 1837620 2067583 := bstep (se 1 (by rfl) ⟨1550687, by rfl⟩ : syracuseStep 2067583 = 3101375) B3101375
theorem B4656487 : Blo 1837620 4656487 := bstep (se 1 (by rfl) ⟨3492365, by rfl⟩ : syracuseStep 4656487 = 6984731) B6984731
theorem B12586607 : Blo 1837620 12586607 := bstep (se 1 (by rfl) ⟨9439955, by rfl⟩ : syracuseStep 12586607 = 18879911) B18879911
theorem B35360509 : Blo 1837620 35360509 := bstep (se 3 (by rfl) ⟨6630095, by rfl⟩ : syracuseStep 35360509 = 13260191) B13260191
theorem B2068591 : Blo 1837620 2068591 := bstep (se 1 (by rfl) ⟨1551443, by rfl⟩ : syracuseStep 2068591 = 3102887) B3102887
theorem B1839431 : Blo 1837620 1839431 := bstep (se 1 (by rfl) ⟨1379573, by rfl⟩ : syracuseStep 1839431 = 2759147) B2759147
theorem B17666723 : Blo 1837620 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B13956461 : Blo 1837620 13956461 := bstep (se 3 (by rfl) ⟨2616836, by rfl⟩ : syracuseStep 13956461 = 5233673) B5233673
theorem B8836883 : Blo 1837620 8836883 := bstep (se 1 (by rfl) ⟨6627662, by rfl⟩ : syracuseStep 8836883 = 13255325) B13255325
theorem B13956947 : Blo 1837620 13956947 := bstep (se 1 (by rfl) ⟨10467710, by rfl⟩ : syracuseStep 13956947 = 20935421) B20935421
theorem B4716521 : Blo 1837620 4716521 := bstep (se 2 (by rfl) ⟨1768695, by rfl⟩ : syracuseStep 4716521 = 3537391) B3537391
theorem B4134959 : Blo 1837620 4134959 := bstep (se 1 (by rfl) ⟨3101219, by rfl⟩ : syracuseStep 4134959 = 6202439) B6202439
theorem B9312569 : Blo 1837620 9312569 := bstep (se 2 (by rfl) ⟨3492213, by rfl⟩ : syracuseStep 9312569 = 6984427) B6984427
theorem B13965695 : Blo 1837620 13965695 := bstep (se 1 (by rfl) ⟨10474271, by rfl⟩ : syracuseStep 13965695 = 20948543) B20948543
theorem B3103231 : Blo 1837620 3103231 := bstep (se 1 (by rfl) ⟨2327423, by rfl⟩ : syracuseStep 3103231 = 4654847) B4654847
theorem B4135913 : Blo 1837620 4135913 := bstep (se 2 (by rfl) ⟨1550967, by rfl⟩ : syracuseStep 4135913 = 3101935) B3101935
theorem B10468349 : Blo 1837620 10468349 := bstep (se 3 (by rfl) ⟨1962815, by rfl⟩ : syracuseStep 10468349 = 3925631) B3925631
theorem B5307805 : Blo 1837620 5307805 := bstep (se 3 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 5307805 = 1990427) B1990427
theorem B26500547 : Blo 1837620 26500547 := bstep (se 1 (by rfl) ⟨19875410, by rfl⟩ : syracuseStep 26500547 = 39750821) B39750821
theorem B34471699 : Blo 1837620 34471699 := bstep (se 1 (by rfl) ⟨25853774, by rfl⟩ : syracuseStep 34471699 = 51707549) B51707549
theorem B4137641 : Blo 1837620 4137641 := bstep (se 2 (by rfl) ⟨1551615, by rfl⟩ : syracuseStep 4137641 = 3103231) B3103231
theorem B51708881 : Blo 1837620 51708881 := bstep (se 2 (by rfl) ⟨19390830, by rfl⟩ : syracuseStep 51708881 = 38781661) B38781661
theorem B5891255 : Blo 1837620 5891255 := bstep (se 1 (by rfl) ⟨4418441, by rfl⟩ : syracuseStep 5891255 = 8836883) B8836883
theorem B13961321 : Blo 1837620 13961321 := bstep (se 2 (by rfl) ⟨5235495, by rfl⟩ : syracuseStep 13961321 = 10470991) B10470991
theorem B47147345 : Blo 1837620 47147345 := bstep (se 2 (by rfl) ⟨17680254, by rfl⟩ : syracuseStep 47147345 = 35360509) B35360509
theorem B8391071 : Blo 1837620 8391071 := bstep (se 1 (by rfl) ⟨6293303, by rfl⟩ : syracuseStep 8391071 = 12586607) B12586607
theorem B2756639 : Blo 1837620 2756639 := bstep (se 1 (by rfl) ⟨2067479, by rfl⟩ : syracuseStep 2756639 = 4134959) B4134959
theorem B183849061 : Blo 1837620 183849061 := bstep (se 4 (by rfl) ⟨17235849, by rfl⟩ : syracuseStep 183849061 = 34471699) B34471699
theorem B2756777 : Blo 1837620 2756777 := bstep (se 2 (by rfl) ⟨1033791, by rfl⟩ : syracuseStep 2756777 = 2067583) B2067583
theorem B9310463 : Blo 1837620 9310463 := bstep (se 1 (by rfl) ⟨6982847, by rfl⟩ : syracuseStep 9310463 = 13965695) B13965695
theorem B2757275 : Blo 1837620 2757275 := bstep (se 1 (by rfl) ⟨2067956, by rfl⟩ : syracuseStep 2757275 = 4135913) B4135913
theorem B17667031 : Blo 1837620 17667031 := bstep (se 1 (by rfl) ⟨13250273, by rfl⟩ : syracuseStep 17667031 = 26500547) B26500547
theorem B2758121 : Blo 1837620 2758121 := bstep (se 2 (by rfl) ⟨1034295, by rfl⟩ : syracuseStep 2758121 = 2068591) B2068591
theorem B11777815 : Blo 1837620 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B2758823 : Blo 1837620 2758823 := bstep (se 1 (by rfl) ⟨2069117, by rfl⟩ : syracuseStep 2758823 = 4138235) B4138235
theorem B9304307 : Blo 1837620 9304307 := bstep (se 1 (by rfl) ⟨6978230, by rfl⟩ : syracuseStep 9304307 = 13956461) B13956461
theorem B9304631 : Blo 1837620 9304631 := bstep (se 1 (by rfl) ⟨6978473, by rfl⟩ : syracuseStep 9304631 = 13956947) B13956947
theorem B3144347 : Blo 1837620 3144347 := bstep (se 1 (by rfl) ⟨2358260, by rfl⟩ : syracuseStep 3144347 = 4716521) B4716521
theorem B4135679 : Blo 1837620 4135679 := bstep (se 1 (by rfl) ⟨3101759, by rfl⟩ : syracuseStep 4135679 = 6203519) B6203519
theorem B3103609 : Blo 1837620 3103609 := bstep (se 2 (by rfl) ⟨1163853, by rfl⟩ : syracuseStep 3103609 = 2327707) B2327707
theorem B6208379 : Blo 1837620 6208379 := bstep (se 1 (by rfl) ⟨4656284, by rfl⟩ : syracuseStep 6208379 = 9312569) B9312569
theorem B6208649 : Blo 1837620 6208649 := bstep (se 2 (by rfl) ⟨2328243, by rfl⟩ : syracuseStep 6208649 = 4656487) B4656487
theorem B12573883 : Blo 1837620 12573883 := bstep (se 1 (by rfl) ⟨9430412, by rfl⟩ : syracuseStep 12573883 = 18860825) B18860825
theorem B7077073 : Blo 1837620 7077073 := bstep (se 2 (by rfl) ⟨2653902, by rfl⟩ : syracuseStep 7077073 = 5307805) B5307805
theorem B5889307 : Blo 1837620 5889307 := bstep (se 1 (by rfl) ⟨4416980, by rfl⟩ : syracuseStep 5889307 = 8833961) B8833961
theorem B6978899 : Blo 1837620 6978899 := bstep (se 1 (by rfl) ⟨5234174, by rfl⟩ : syracuseStep 6978899 = 10468349) B10468349
theorem B34472587 : Blo 1837620 34472587 := bstep (se 1 (by rfl) ⟨25854440, by rfl⟩ : syracuseStep 34472587 = 51708881) B51708881
theorem B4138145 : Blo 1837620 4138145 := bstep (se 2 (by rfl) ⟨1551804, by rfl⟩ : syracuseStep 4138145 = 3103609) B3103609
theorem B9307547 : Blo 1837620 9307547 := bstep (se 1 (by rfl) ⟨6980660, by rfl⟩ : syracuseStep 9307547 = 13961321) B13961321
theorem B6202871 : Blo 1837620 6202871 := bstep (se 1 (by rfl) ⟨4652153, by rfl⟩ : syracuseStep 6202871 = 9304307) B9304307
theorem B6203087 : Blo 1837620 6203087 := bstep (se 1 (by rfl) ⟨4652315, by rfl⟩ : syracuseStep 6203087 = 9304631) B9304631
theorem B4138919 : Blo 1837620 4138919 := bstep (se 1 (by rfl) ⟨3104189, by rfl⟩ : syracuseStep 4138919 = 6208379) B6208379
theorem B4139099 : Blo 1837620 4139099 := bstep (se 1 (by rfl) ⟨3104324, by rfl⟩ : syracuseStep 4139099 = 6208649) B6208649
theorem B1837759 : Blo 1837620 1837759 := bstep (se 1 (by rfl) ⟨1378319, by rfl⟩ : syracuseStep 1837759 = 2756639) B2756639
theorem B1837851 : Blo 1837620 1837851 := bstep (se 1 (by rfl) ⟨1378388, by rfl⟩ : syracuseStep 1837851 = 2756777) B2756777
theorem B245132081 : Blo 1837620 245132081 := bstep (se 2 (by rfl) ⟨91924530, by rfl⟩ : syracuseStep 245132081 = 183849061) B183849061
theorem B1838183 : Blo 1837620 1838183 := bstep (se 1 (by rfl) ⟨1378637, by rfl⟩ : syracuseStep 1838183 = 2757275) B2757275
theorem B3927503 : Blo 1837620 3927503 := bstep (se 1 (by rfl) ⟨2945627, by rfl⟩ : syracuseStep 3927503 = 5891255) B5891255
theorem B1838747 : Blo 1837620 1838747 := bstep (se 1 (by rfl) ⟨1379060, by rfl⟩ : syracuseStep 1838747 = 2758121) B2758121
theorem B22376189 : Blo 1837620 22376189 := bstep (se 3 (by rfl) ⟨4195535, by rfl⟩ : syracuseStep 22376189 = 8391071) B8391071
theorem B23556041 : Blo 1837620 23556041 := bstep (se 2 (by rfl) ⟨8833515, by rfl⟩ : syracuseStep 23556041 = 17667031) B17667031
theorem B1839215 : Blo 1837620 1839215 := bstep (se 1 (by rfl) ⟨1379411, by rfl⟩ : syracuseStep 1839215 = 2758823) B2758823
theorem B16765177 : Blo 1837620 16765177 := bstep (se 2 (by rfl) ⟨6286941, by rfl⟩ : syracuseStep 16765177 = 12573883) B12573883
theorem B7852409 : Blo 1837620 7852409 := bstep (se 2 (by rfl) ⟨2944653, by rfl⟩ : syracuseStep 7852409 = 5889307) B5889307
theorem B2757119 : Blo 1837620 2757119 := bstep (se 1 (by rfl) ⟨2067839, by rfl⟩ : syracuseStep 2757119 = 4135679) B4135679
theorem B6206975 : Blo 1837620 6206975 := bstep (se 1 (by rfl) ⟨4655231, by rfl⟩ : syracuseStep 6206975 = 9310463) B9310463
theorem B2758427 : Blo 1837620 2758427 := bstep (se 1 (by rfl) ⟨2068820, by rfl⟩ : syracuseStep 2758427 = 4137641) B4137641
theorem B31431563 : Blo 1837620 31431563 := bstep (se 1 (by rfl) ⟨23573672, by rfl⟩ : syracuseStep 31431563 = 47147345) B47147345
theorem B9436097 : Blo 1837620 9436097 := bstep (se 2 (by rfl) ⟨3538536, by rfl⟩ : syracuseStep 9436097 = 7077073) B7077073
theorem B2096231 : Blo 1837620 2096231 := bstep (se 1 (by rfl) ⟨1572173, by rfl⟩ : syracuseStep 2096231 = 3144347) B3144347
theorem B4652599 : Blo 1837620 4652599 := bstep (se 1 (by rfl) ⟨3489449, by rfl⟩ : syracuseStep 4652599 = 6978899) B6978899
theorem B15703753 : Blo 1837620 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B5234939 : Blo 1837620 5234939 := bstep (se 1 (by rfl) ⟨3926204, by rfl⟩ : syracuseStep 5234939 = 7852409) B7852409
theorem B4137983 : Blo 1837620 4137983 := bstep (se 1 (by rfl) ⟨3103487, by rfl⟩ : syracuseStep 4137983 = 6206975) B6206975
theorem B6203465 : Blo 1837620 6203465 := bstep (se 2 (by rfl) ⟨2326299, by rfl⟩ : syracuseStep 6203465 = 4652599) B4652599
theorem B1838079 : Blo 1837620 1838079 := bstep (se 1 (by rfl) ⟨1378559, by rfl⟩ : syracuseStep 1838079 = 2757119) B2757119
theorem B6205031 : Blo 1837620 6205031 := bstep (se 1 (by rfl) ⟨4653773, by rfl⟩ : syracuseStep 6205031 = 9307547) B9307547
theorem B22359797 : Blo 1837620 22359797 := bstep (se 5 (by rfl) ⟨1048115, by rfl⟩ : syracuseStep 22359797 = 2096231) B2096231
theorem B1838951 : Blo 1837620 1838951 := bstep (se 1 (by rfl) ⟨1379213, by rfl⟩ : syracuseStep 1838951 = 2758427) B2758427
theorem B2618335 : Blo 1837620 2618335 := bstep (se 1 (by rfl) ⟨1963751, by rfl⟩ : syracuseStep 2618335 = 3927503) B3927503
theorem B22353569 : Blo 1837620 22353569 := bstep (se 2 (by rfl) ⟨8382588, by rfl⟩ : syracuseStep 22353569 = 16765177) B16765177
theorem B2758763 : Blo 1837620 2758763 := bstep (se 1 (by rfl) ⟨2069072, by rfl⟩ : syracuseStep 2758763 = 4138145) B4138145
theorem B45963449 : Blo 1837620 45963449 := bstep (se 2 (by rfl) ⟨17236293, by rfl⟩ : syracuseStep 45963449 = 34472587) B34472587
theorem B4135247 : Blo 1837620 4135247 := bstep (se 1 (by rfl) ⟨3101435, by rfl⟩ : syracuseStep 4135247 = 6202871) B6202871
theorem B4135391 : Blo 1837620 4135391 := bstep (se 1 (by rfl) ⟨3101543, by rfl⟩ : syracuseStep 4135391 = 6203087) B6203087
theorem B2759279 : Blo 1837620 2759279 := bstep (se 1 (by rfl) ⟨2069459, by rfl⟩ : syracuseStep 2759279 = 4138919) B4138919
theorem B2759399 : Blo 1837620 2759399 := bstep (se 1 (by rfl) ⟨2069549, by rfl⟩ : syracuseStep 2759399 = 4139099) B4139099
theorem B163421387 : Blo 1837620 163421387 := bstep (se 1 (by rfl) ⟨122566040, by rfl⟩ : syracuseStep 163421387 = 245132081) B245132081
theorem B20954375 : Blo 1837620 20954375 := bstep (se 1 (by rfl) ⟨15715781, by rfl⟩ : syracuseStep 20954375 = 31431563) B31431563
theorem B6290731 : Blo 1837620 6290731 := bstep (se 1 (by rfl) ⟨4718048, by rfl⟩ : syracuseStep 6290731 = 9436097) B9436097
theorem B20938337 : Blo 1837620 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B14917459 : Blo 1837620 14917459 := bstep (se 1 (by rfl) ⟨11188094, by rfl⟩ : syracuseStep 14917459 = 22376189) B22376189
theorem B15704027 : Blo 1837620 15704027 := bstep (se 1 (by rfl) ⟨11778020, by rfl⟩ : syracuseStep 15704027 = 23556041) B23556041
theorem B3489959 : Blo 1837620 3489959 := bstep (se 1 (by rfl) ⟨2617469, by rfl⟩ : syracuseStep 3489959 = 5234939) B5234939
theorem B14902379 : Blo 1837620 14902379 := bstep (se 1 (by rfl) ⟨11176784, by rfl⟩ : syracuseStep 14902379 = 22353569) B22353569
theorem B3491113 : Blo 1837620 3491113 := bstep (se 2 (by rfl) ⟨1309167, by rfl⟩ : syracuseStep 3491113 = 2618335) B2618335
theorem B108947591 : Blo 1837620 108947591 := bstep (se 1 (by rfl) ⟨81710693, by rfl⟩ : syracuseStep 108947591 = 163421387) B163421387
theorem B13969583 : Blo 1837620 13969583 := bstep (se 1 (by rfl) ⟨10477187, by rfl⟩ : syracuseStep 13969583 = 20954375) B20954375
theorem B1839175 : Blo 1837620 1839175 := bstep (se 1 (by rfl) ⟨1379381, by rfl⟩ : syracuseStep 1839175 = 2758763) B2758763
theorem B30642299 : Blo 1837620 30642299 := bstep (se 1 (by rfl) ⟨22981724, by rfl⟩ : syracuseStep 30642299 = 45963449) B45963449
theorem B2756831 : Blo 1837620 2756831 := bstep (se 1 (by rfl) ⟨2067623, by rfl⟩ : syracuseStep 2756831 = 4135247) B4135247
theorem B2756927 : Blo 1837620 2756927 := bstep (se 1 (by rfl) ⟨2067695, by rfl⟩ : syracuseStep 2756927 = 4135391) B4135391
theorem B1839519 : Blo 1837620 1839519 := bstep (se 1 (by rfl) ⟨1379639, by rfl⟩ : syracuseStep 1839519 = 2759279) B2759279
theorem B1839599 : Blo 1837620 1839599 := bstep (se 1 (by rfl) ⟨1379699, by rfl⟩ : syracuseStep 1839599 = 2759399) B2759399
theorem B14906531 : Blo 1837620 14906531 := bstep (se 1 (by rfl) ⟨11179898, by rfl⟩ : syracuseStep 14906531 = 22359797) B22359797
theorem B2758655 : Blo 1837620 2758655 := bstep (se 1 (by rfl) ⟨2068991, by rfl⟩ : syracuseStep 2758655 = 4137983) B4137983
theorem B4135643 : Blo 1837620 4135643 := bstep (se 1 (by rfl) ⟨3101732, by rfl⟩ : syracuseStep 4135643 = 6203465) B6203465
theorem B8387641 : Blo 1837620 8387641 := bstep (se 2 (by rfl) ⟨3145365, by rfl⟩ : syracuseStep 8387641 = 6290731) B6290731
theorem B13958891 : Blo 1837620 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B4136687 : Blo 1837620 4136687 := bstep (se 1 (by rfl) ⟨3102515, by rfl⟩ : syracuseStep 4136687 = 6205031) B6205031
theorem B19889945 : Blo 1837620 19889945 := bstep (se 2 (by rfl) ⟨7458729, by rfl⟩ : syracuseStep 19889945 = 14917459) B14917459
theorem B10469351 : Blo 1837620 10469351 := bstep (se 1 (by rfl) ⟨7852013, by rfl⟩ : syracuseStep 10469351 = 15704027) B15704027
theorem B2326639 : Blo 1837620 2326639 := bstep (se 1 (by rfl) ⟨1744979, by rfl⟩ : syracuseStep 2326639 = 3489959) B3489959
theorem B9937687 : Blo 1837620 9937687 := bstep (se 1 (by rfl) ⟨7453265, by rfl⟩ : syracuseStep 9937687 = 14906531) B14906531
theorem B11183521 : Blo 1837620 11183521 := bstep (se 2 (by rfl) ⟨4193820, by rfl⟩ : syracuseStep 11183521 = 8387641) B8387641
theorem B72631727 : Blo 1837620 72631727 := bstep (se 1 (by rfl) ⟨54473795, by rfl⟩ : syracuseStep 72631727 = 108947591) B108947591
theorem B4654817 : Blo 1837620 4654817 := bstep (se 2 (by rfl) ⟨1745556, by rfl⟩ : syracuseStep 4654817 = 3491113) B3491113
theorem B1837887 : Blo 1837620 1837887 := bstep (se 1 (by rfl) ⟨1378415, by rfl⟩ : syracuseStep 1837887 = 2756831) B2756831
theorem B1837951 : Blo 1837620 1837951 := bstep (se 1 (by rfl) ⟨1378463, by rfl⟩ : syracuseStep 1837951 = 2756927) B2756927
theorem B1839103 : Blo 1837620 1839103 := bstep (se 1 (by rfl) ⟨1379327, by rfl⟩ : syracuseStep 1839103 = 2758655) B2758655
theorem B2757095 : Blo 1837620 2757095 := bstep (se 1 (by rfl) ⟨2067821, by rfl⟩ : syracuseStep 2757095 = 4135643) B4135643
theorem B2757791 : Blo 1837620 2757791 := bstep (se 1 (by rfl) ⟨2068343, by rfl⟩ : syracuseStep 2757791 = 4136687) B4136687
theorem B13259963 : Blo 1837620 13259963 := bstep (se 1 (by rfl) ⟨9944972, by rfl⟩ : syracuseStep 13259963 = 19889945) B19889945
theorem B20428199 : Blo 1837620 20428199 := bstep (se 1 (by rfl) ⟨15321149, by rfl⟩ : syracuseStep 20428199 = 30642299) B30642299
theorem B9934919 : Blo 1837620 9934919 := bstep (se 1 (by rfl) ⟨7451189, by rfl⟩ : syracuseStep 9934919 = 14902379) B14902379
theorem B9313055 : Blo 1837620 9313055 := bstep (se 1 (by rfl) ⟨6984791, by rfl⟩ : syracuseStep 9313055 = 13969583) B13969583
theorem B9305927 : Blo 1837620 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B6979567 : Blo 1837620 6979567 := bstep (se 1 (by rfl) ⟨5234675, by rfl⟩ : syracuseStep 6979567 = 10469351) B10469351
theorem B8839975 : Blo 1837620 8839975 := bstep (se 1 (by rfl) ⟨6629981, by rfl⟩ : syracuseStep 8839975 = 13259963) B13259963
theorem B14911361 : Blo 1837620 14911361 := bstep (se 2 (by rfl) ⟨5591760, by rfl⟩ : syracuseStep 14911361 = 11183521) B11183521
theorem B6203951 : Blo 1837620 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B1838063 : Blo 1837620 1838063 := bstep (se 1 (by rfl) ⟨1378547, by rfl⟩ : syracuseStep 1838063 = 2757095) B2757095
theorem B1838527 : Blo 1837620 1838527 := bstep (se 1 (by rfl) ⟨1378895, by rfl⟩ : syracuseStep 1838527 = 2757791) B2757791
theorem B13618799 : Blo 1837620 13618799 := bstep (se 1 (by rfl) ⟨10214099, by rfl⟩ : syracuseStep 13618799 = 20428199) B20428199
theorem B13250249 : Blo 1837620 13250249 := bstep (se 2 (by rfl) ⟨4968843, by rfl⟩ : syracuseStep 13250249 = 9937687) B9937687
theorem B6623279 : Blo 1837620 6623279 := bstep (se 1 (by rfl) ⟨4967459, by rfl⟩ : syracuseStep 6623279 = 9934919) B9934919
theorem B3102185 : Blo 1837620 3102185 := bstep (se 2 (by rfl) ⟨1163319, by rfl⟩ : syracuseStep 3102185 = 2326639) B2326639
theorem B48421151 : Blo 1837620 48421151 := bstep (se 1 (by rfl) ⟨36315863, by rfl⟩ : syracuseStep 48421151 = 72631727) B72631727
theorem B3103211 : Blo 1837620 3103211 := bstep (se 1 (by rfl) ⟨2327408, by rfl⟩ : syracuseStep 3103211 = 4654817) B4654817
theorem B6208703 : Blo 1837620 6208703 := bstep (se 1 (by rfl) ⟨4656527, by rfl⟩ : syracuseStep 6208703 = 9313055) B9313055
theorem B9306089 : Blo 1837620 9306089 := bstep (se 2 (by rfl) ⟨3489783, by rfl⟩ : syracuseStep 9306089 = 6979567) B6979567
theorem B4415519 : Blo 1837620 4415519 := bstep (se 1 (by rfl) ⟨3311639, by rfl⟩ : syracuseStep 4415519 = 6623279) B6623279
theorem B4139135 : Blo 1837620 4139135 := bstep (se 1 (by rfl) ⟨3104351, by rfl⟩ : syracuseStep 4139135 = 6208703) B6208703
theorem B9079199 : Blo 1837620 9079199 := bstep (se 1 (by rfl) ⟨6809399, by rfl⟩ : syracuseStep 9079199 = 13618799) B13618799
theorem B8833499 : Blo 1837620 8833499 := bstep (se 1 (by rfl) ⟨6625124, by rfl⟩ : syracuseStep 8833499 = 13250249) B13250249
theorem B6204059 : Blo 1837620 6204059 := bstep (se 1 (by rfl) ⟨4653044, by rfl⟩ : syracuseStep 6204059 = 9306089) B9306089
theorem B2068123 : Blo 1837620 2068123 := bstep (se 1 (by rfl) ⟨1551092, by rfl⟩ : syracuseStep 2068123 = 3102185) B3102185
theorem B9940907 : Blo 1837620 9940907 := bstep (se 1 (by rfl) ⟨7455680, by rfl⟩ : syracuseStep 9940907 = 14911361) B14911361
theorem B32280767 : Blo 1837620 32280767 := bstep (se 1 (by rfl) ⟨24210575, by rfl⟩ : syracuseStep 32280767 = 48421151) B48421151
theorem B2068807 : Blo 1837620 2068807 := bstep (se 1 (by rfl) ⟨1551605, by rfl⟩ : syracuseStep 2068807 = 3103211) B3103211
theorem B11786633 : Blo 1837620 11786633 := bstep (se 2 (by rfl) ⟨4419987, by rfl⟩ : syracuseStep 11786633 = 8839975) B8839975
theorem B4135967 : Blo 1837620 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B21520511 : Blo 1837620 21520511 := bstep (se 1 (by rfl) ⟨16140383, by rfl⟩ : syracuseStep 21520511 = 32280767) B32280767
theorem B7857755 : Blo 1837620 7857755 := bstep (se 1 (by rfl) ⟨5893316, by rfl⟩ : syracuseStep 7857755 = 11786633) B11786633
theorem B11774717 : Blo 1837620 11774717 := bstep (se 3 (by rfl) ⟨2207759, by rfl⟩ : syracuseStep 11774717 = 4415519) B4415519
theorem B2757311 : Blo 1837620 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B2757497 : Blo 1837620 2757497 := bstep (se 2 (by rfl) ⟨1034061, by rfl⟩ : syracuseStep 2757497 = 2068123) B2068123
theorem B2758409 : Blo 1837620 2758409 := bstep (se 2 (by rfl) ⟨1034403, by rfl⟩ : syracuseStep 2758409 = 2068807) B2068807
theorem B2759423 : Blo 1837620 2759423 := bstep (se 1 (by rfl) ⟨2069567, by rfl⟩ : syracuseStep 2759423 = 4139135) B4139135
theorem B6052799 : Blo 1837620 6052799 := bstep (se 1 (by rfl) ⟨4539599, by rfl⟩ : syracuseStep 6052799 = 9079199) B9079199
theorem B5888999 : Blo 1837620 5888999 := bstep (se 1 (by rfl) ⟨4416749, by rfl⟩ : syracuseStep 5888999 = 8833499) B8833499
theorem B4136039 : Blo 1837620 4136039 := bstep (se 1 (by rfl) ⟨3102029, by rfl⟩ : syracuseStep 4136039 = 6204059) B6204059
theorem B6627271 : Blo 1837620 6627271 := bstep (se 1 (by rfl) ⟨4970453, by rfl⟩ : syracuseStep 6627271 = 9940907) B9940907
theorem B7849811 : Blo 1837620 7849811 := bstep (se 1 (by rfl) ⟨5887358, by rfl⟩ : syracuseStep 7849811 = 11774717) B11774717
theorem B3925999 : Blo 1837620 3925999 := bstep (se 1 (by rfl) ⟨2944499, by rfl⟩ : syracuseStep 3925999 = 5888999) B5888999
theorem B16140797 : Blo 1837620 16140797 := bstep (se 3 (by rfl) ⟨3026399, by rfl⟩ : syracuseStep 16140797 = 6052799) B6052799
theorem B14347007 : Blo 1837620 14347007 := bstep (se 1 (by rfl) ⟨10760255, by rfl⟩ : syracuseStep 14347007 = 21520511) B21520511
theorem B1838207 : Blo 1837620 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B1838331 : Blo 1837620 1838331 := bstep (se 1 (by rfl) ⟨1378748, by rfl⟩ : syracuseStep 1838331 = 2757497) B2757497
theorem B5238503 : Blo 1837620 5238503 := bstep (se 1 (by rfl) ⟨3928877, by rfl⟩ : syracuseStep 5238503 = 7857755) B7857755
theorem B1838939 : Blo 1837620 1838939 := bstep (se 1 (by rfl) ⟨1379204, by rfl⟩ : syracuseStep 1838939 = 2758409) B2758409
theorem B1839615 : Blo 1837620 1839615 := bstep (se 1 (by rfl) ⟨1379711, by rfl⟩ : syracuseStep 1839615 = 2759423) B2759423
theorem B2757359 : Blo 1837620 2757359 := bstep (se 1 (by rfl) ⟨2068019, by rfl⟩ : syracuseStep 2757359 = 4136039) B4136039
theorem B8836361 : Blo 1837620 8836361 := bstep (se 2 (by rfl) ⟨3313635, by rfl⟩ : syracuseStep 8836361 = 6627271) B6627271
theorem B5890907 : Blo 1837620 5890907 := bstep (se 1 (by rfl) ⟨4418180, by rfl⟩ : syracuseStep 5890907 = 8836361) B8836361
theorem B3492335 : Blo 1837620 3492335 := bstep (se 1 (by rfl) ⟨2619251, by rfl⟩ : syracuseStep 3492335 = 5238503) B5238503
theorem B1838239 : Blo 1837620 1838239 := bstep (se 1 (by rfl) ⟨1378679, by rfl⟩ : syracuseStep 1838239 = 2757359) B2757359
theorem B10760531 : Blo 1837620 10760531 := bstep (se 1 (by rfl) ⟨8070398, by rfl⟩ : syracuseStep 10760531 = 16140797) B16140797
theorem B9564671 : Blo 1837620 9564671 := bstep (se 1 (by rfl) ⟨7173503, by rfl⟩ : syracuseStep 9564671 = 14347007) B14347007
theorem B5233207 : Blo 1837620 5233207 := bstep (se 1 (by rfl) ⟨3924905, by rfl⟩ : syracuseStep 5233207 = 7849811) B7849811
theorem B5234665 : Blo 1837620 5234665 := bstep (se 2 (by rfl) ⟨1962999, by rfl⟩ : syracuseStep 5234665 = 3925999) B3925999
theorem B114778997 : Blo 1837620 114778997 := bstep (se 5 (by rfl) ⟨5380265, by rfl⟩ : syracuseStep 114778997 = 10760531) B10760531
theorem B6376447 : Blo 1837620 6376447 := bstep (se 1 (by rfl) ⟨4782335, by rfl⟩ : syracuseStep 6376447 = 9564671) B9564671
theorem B15709085 : Blo 1837620 15709085 := bstep (se 3 (by rfl) ⟨2945453, by rfl⟩ : syracuseStep 15709085 = 5890907) B5890907
theorem B6977609 : Blo 1837620 6977609 := bstep (se 2 (by rfl) ⟨2616603, by rfl⟩ : syracuseStep 6977609 = 5233207) B5233207
theorem B9312893 : Blo 1837620 9312893 := bstep (se 3 (by rfl) ⟨1746167, by rfl⟩ : syracuseStep 9312893 = 3492335) B3492335
theorem B6979553 : Blo 1837620 6979553 := bstep (se 2 (by rfl) ⟨2617332, by rfl⟩ : syracuseStep 6979553 = 5234665) B5234665
theorem B10472723 : Blo 1837620 10472723 := bstep (se 1 (by rfl) ⟨7854542, by rfl⟩ : syracuseStep 10472723 = 15709085) B15709085
theorem B76519331 : Blo 1837620 76519331 := bstep (se 1 (by rfl) ⟨57389498, by rfl⟩ : syracuseStep 76519331 = 114778997) B114778997
theorem B8501929 : Blo 1837620 8501929 := bstep (se 2 (by rfl) ⟨3188223, by rfl⟩ : syracuseStep 8501929 = 6376447) B6376447
theorem B4651739 : Blo 1837620 4651739 := bstep (se 1 (by rfl) ⟨3488804, by rfl⟩ : syracuseStep 4651739 = 6977609) B6977609
theorem B6208595 : Blo 1837620 6208595 := bstep (se 1 (by rfl) ⟨4656446, by rfl⟩ : syracuseStep 6208595 = 9312893) B9312893
theorem B4653035 : Blo 1837620 4653035 := bstep (se 1 (by rfl) ⟨3489776, by rfl⟩ : syracuseStep 4653035 = 6979553) B6979553
theorem B45343621 : Blo 1837620 45343621 := bstep (se 4 (by rfl) ⟨4250964, by rfl⟩ : syracuseStep 45343621 = 8501929) B8501929
theorem B51012887 : Blo 1837620 51012887 := bstep (se 1 (by rfl) ⟨38259665, by rfl⟩ : syracuseStep 51012887 = 76519331) B76519331
theorem B4139063 : Blo 1837620 4139063 := bstep (se 1 (by rfl) ⟨3104297, by rfl⟩ : syracuseStep 4139063 = 6208595) B6208595
theorem B6981815 : Blo 1837620 6981815 := bstep (se 1 (by rfl) ⟨5236361, by rfl⟩ : syracuseStep 6981815 = 10472723) B10472723
theorem B3101159 : Blo 1837620 3101159 := bstep (se 1 (by rfl) ⟨2325869, by rfl⟩ : syracuseStep 3101159 = 4651739) B4651739
theorem B3102023 : Blo 1837620 3102023 := bstep (se 1 (by rfl) ⟨2326517, by rfl⟩ : syracuseStep 3102023 = 4653035) B4653035
theorem B60458161 : Blo 1837620 60458161 := bstep (se 2 (by rfl) ⟨22671810, by rfl⟩ : syracuseStep 60458161 = 45343621) B45343621
theorem B4654543 : Blo 1837620 4654543 := bstep (se 1 (by rfl) ⟨3490907, by rfl⟩ : syracuseStep 4654543 = 6981815) B6981815
theorem B2067439 : Blo 1837620 2067439 := bstep (se 1 (by rfl) ⟨1550579, by rfl⟩ : syracuseStep 2067439 = 3101159) B3101159
theorem B2068015 : Blo 1837620 2068015 := bstep (se 1 (by rfl) ⟨1551011, by rfl⟩ : syracuseStep 2068015 = 3102023) B3102023
theorem B136034365 : Blo 1837620 136034365 := bstep (se 3 (by rfl) ⟨25506443, by rfl⟩ : syracuseStep 136034365 = 51012887) B51012887
theorem B2759375 : Blo 1837620 2759375 := bstep (se 1 (by rfl) ⟨2069531, by rfl⟩ : syracuseStep 2759375 = 4139063) B4139063
theorem B181379153 : Blo 1837620 181379153 := bstep (se 2 (by rfl) ⟨68017182, by rfl⟩ : syracuseStep 181379153 = 136034365) B136034365
theorem B80610881 : Blo 1837620 80610881 := bstep (se 2 (by rfl) ⟨30229080, by rfl⟩ : syracuseStep 80610881 = 60458161) B60458161
theorem B2756585 : Blo 1837620 2756585 := bstep (se 2 (by rfl) ⟨1033719, by rfl⟩ : syracuseStep 2756585 = 2067439) B2067439
theorem B1839583 : Blo 1837620 1839583 := bstep (se 1 (by rfl) ⟨1379687, by rfl⟩ : syracuseStep 1839583 = 2759375) B2759375
theorem B6206057 : Blo 1837620 6206057 := bstep (se 2 (by rfl) ⟨2327271, by rfl⟩ : syracuseStep 6206057 = 4654543) B4654543
theorem B2757353 : Blo 1837620 2757353 := bstep (se 2 (by rfl) ⟨1034007, by rfl⟩ : syracuseStep 2757353 = 2068015) B2068015
theorem B4137371 : Blo 1837620 4137371 := bstep (se 1 (by rfl) ⟨3103028, by rfl⟩ : syracuseStep 4137371 = 6206057) B6206057
theorem B1837723 : Blo 1837620 1837723 := bstep (se 1 (by rfl) ⟨1378292, by rfl⟩ : syracuseStep 1837723 = 2756585) B2756585
theorem B1838235 : Blo 1837620 1838235 := bstep (se 1 (by rfl) ⟨1378676, by rfl⟩ : syracuseStep 1838235 = 2757353) B2757353
theorem B214962349 : Blo 1837620 214962349 := bstep (se 3 (by rfl) ⟨40305440, by rfl⟩ : syracuseStep 214962349 = 80610881) B80610881
theorem B120919435 : Blo 1837620 120919435 := bstep (se 1 (by rfl) ⟨90689576, by rfl⟩ : syracuseStep 120919435 = 181379153) B181379153
theorem B286616465 : Blo 1837620 286616465 := bstep (se 2 (by rfl) ⟨107481174, by rfl⟩ : syracuseStep 286616465 = 214962349) B214962349
theorem B2579614613 : Blo 1837620 2579614613 := bstep (se 6 (by rfl) ⟨60459717, by rfl⟩ : syracuseStep 2579614613 = 120919435) B120919435
theorem B2758247 : Blo 1837620 2758247 := bstep (se 1 (by rfl) ⟨2068685, by rfl⟩ : syracuseStep 2758247 = 4137371) B4137371
theorem B1838831 : Blo 1837620 1838831 := bstep (se 1 (by rfl) ⟨1379123, by rfl⟩ : syracuseStep 1838831 = 2758247) B2758247
theorem B1719743075 : Blo 1837620 1719743075 := bstep (se 1 (by rfl) ⟨1289807306, by rfl⟩ : syracuseStep 1719743075 = 2579614613) B2579614613
theorem B191077643 : Blo 1837620 191077643 := bstep (se 1 (by rfl) ⟨143308232, by rfl⟩ : syracuseStep 191077643 = 286616465) B286616465
theorem B1146495383 : Blo 1837620 1146495383 := bstep (se 1 (by rfl) ⟨859871537, by rfl⟩ : syracuseStep 1146495383 = 1719743075) B1719743075
theorem B127385095 : Blo 1837620 127385095 := bstep (se 1 (by rfl) ⟨95538821, by rfl⟩ : syracuseStep 127385095 = 191077643) B191077643
theorem B764330255 : Blo 1837620 764330255 := bstep (se 1 (by rfl) ⟨573247691, by rfl⟩ : syracuseStep 764330255 = 1146495383) B1146495383
theorem B169846793 : Blo 1837620 169846793 := bstep (se 2 (by rfl) ⟨63692547, by rfl⟩ : syracuseStep 169846793 = 127385095) B127385095
theorem B113231195 : Blo 1837620 113231195 := bstep (se 1 (by rfl) ⟨84923396, by rfl⟩ : syracuseStep 113231195 = 169846793) B169846793
theorem B509553503 : Blo 1837620 509553503 := bstep (se 1 (by rfl) ⟨382165127, by rfl⟩ : syracuseStep 509553503 = 764330255) B764330255
theorem B339702335 : Blo 1837620 339702335 := bstep (se 1 (by rfl) ⟨254776751, by rfl⟩ : syracuseStep 339702335 = 509553503) B509553503
theorem B75487463 : Blo 1837620 75487463 := bstep (se 1 (by rfl) ⟨56615597, by rfl⟩ : syracuseStep 75487463 = 113231195) B113231195
theorem B226468223 : Blo 1837620 226468223 := bstep (se 1 (by rfl) ⟨169851167, by rfl⟩ : syracuseStep 226468223 = 339702335) B339702335
theorem B50324975 : Blo 1837620 50324975 := bstep (se 1 (by rfl) ⟨37743731, by rfl⟩ : syracuseStep 50324975 = 75487463) B75487463
theorem B150978815 : Blo 1837620 150978815 := bstep (se 1 (by rfl) ⟨113234111, by rfl⟩ : syracuseStep 150978815 = 226468223) B226468223
theorem B33549983 : Blo 1837620 33549983 := bstep (se 1 (by rfl) ⟨25162487, by rfl⟩ : syracuseStep 33549983 = 50324975) B50324975
theorem B22366655 : Blo 1837620 22366655 := bstep (se 1 (by rfl) ⟨16774991, by rfl⟩ : syracuseStep 22366655 = 33549983) B33549983
theorem B100652543 : Blo 1837620 100652543 := bstep (se 1 (by rfl) ⟨75489407, by rfl⟩ : syracuseStep 100652543 = 150978815) B150978815
theorem B67101695 : Blo 1837620 67101695 := bstep (se 1 (by rfl) ⟨50326271, by rfl⟩ : syracuseStep 67101695 = 100652543) B100652543
theorem B14911103 : Blo 1837620 14911103 := bstep (se 1 (by rfl) ⟨11183327, by rfl⟩ : syracuseStep 14911103 = 22366655) B22366655
theorem B9940735 : Blo 1837620 9940735 := bstep (se 1 (by rfl) ⟨7455551, by rfl⟩ : syracuseStep 9940735 = 14911103) B14911103
theorem B44734463 : Blo 1837620 44734463 := bstep (se 1 (by rfl) ⟨33550847, by rfl⟩ : syracuseStep 44734463 = 67101695) B67101695
theorem B29822975 : Blo 1837620 29822975 := bstep (se 1 (by rfl) ⟨22367231, by rfl⟩ : syracuseStep 29822975 = 44734463) B44734463
theorem B13254313 : Blo 1837620 13254313 := bstep (se 2 (by rfl) ⟨4970367, by rfl⟩ : syracuseStep 13254313 = 9940735) B9940735
theorem B17672417 : Blo 1837620 17672417 := bstep (se 2 (by rfl) ⟨6627156, by rfl⟩ : syracuseStep 17672417 = 13254313) B13254313
theorem B19881983 : Blo 1837620 19881983 := bstep (se 1 (by rfl) ⟨14911487, by rfl⟩ : syracuseStep 19881983 = 29822975) B29822975
theorem B11781611 : Blo 1837620 11781611 := bstep (se 1 (by rfl) ⟨8836208, by rfl⟩ : syracuseStep 11781611 = 17672417) B17672417
theorem B53018621 : Blo 1837620 53018621 := bstep (se 3 (by rfl) ⟨9940991, by rfl⟩ : syracuseStep 53018621 = 19881983) B19881983
theorem B35345747 : Blo 1837620 35345747 := bstep (se 1 (by rfl) ⟨26509310, by rfl⟩ : syracuseStep 35345747 = 53018621) B53018621
theorem B7854407 : Blo 1837620 7854407 := bstep (se 1 (by rfl) ⟨5890805, by rfl⟩ : syracuseStep 7854407 = 11781611) B11781611
theorem B5236271 : Blo 1837620 5236271 := bstep (se 1 (by rfl) ⟨3927203, by rfl⟩ : syracuseStep 5236271 = 7854407) B7854407
theorem B23563831 : Blo 1837620 23563831 := bstep (se 1 (by rfl) ⟨17672873, by rfl⟩ : syracuseStep 23563831 = 35345747) B35345747
theorem B3490847 : Blo 1837620 3490847 := bstep (se 1 (by rfl) ⟨2618135, by rfl⟩ : syracuseStep 3490847 = 5236271) B5236271
theorem B31418441 : Blo 1837620 31418441 := bstep (se 2 (by rfl) ⟨11781915, by rfl⟩ : syracuseStep 31418441 = 23563831) B23563831
theorem B2327231 : Blo 1837620 2327231 := bstep (se 1 (by rfl) ⟨1745423, by rfl⟩ : syracuseStep 2327231 = 3490847) B3490847
theorem B20945627 : Blo 1837620 20945627 := bstep (se 1 (by rfl) ⟨15709220, by rfl⟩ : syracuseStep 20945627 = 31418441) B31418441
theorem B13963751 : Blo 1837620 13963751 := bstep (se 1 (by rfl) ⟨10472813, by rfl⟩ : syracuseStep 13963751 = 20945627) B20945627
theorem B6205949 : Blo 1837620 6205949 := bstep (se 3 (by rfl) ⟨1163615, by rfl⟩ : syracuseStep 6205949 = 2327231) B2327231
theorem B4137299 : Blo 1837620 4137299 := bstep (se 1 (by rfl) ⟨3102974, by rfl⟩ : syracuseStep 4137299 = 6205949) B6205949
theorem B9309167 : Blo 1837620 9309167 := bstep (se 1 (by rfl) ⟨6981875, by rfl⟩ : syracuseStep 9309167 = 13963751) B13963751
theorem B6206111 : Blo 1837620 6206111 := bstep (se 1 (by rfl) ⟨4654583, by rfl⟩ : syracuseStep 6206111 = 9309167) B9309167
theorem B2758199 : Blo 1837620 2758199 := bstep (se 1 (by rfl) ⟨2068649, by rfl⟩ : syracuseStep 2758199 = 4137299) B4137299
theorem B4137407 : Blo 1837620 4137407 := bstep (se 1 (by rfl) ⟨3103055, by rfl⟩ : syracuseStep 4137407 = 6206111) B6206111
theorem B1838799 : Blo 1837620 1838799 := bstep (se 1 (by rfl) ⟨1379099, by rfl⟩ : syracuseStep 1838799 = 2758199) B2758199
theorem B2758271 : Blo 1837620 2758271 := bstep (se 1 (by rfl) ⟨2068703, by rfl⟩ : syracuseStep 2758271 = 4137407) B4137407
theorem B1838847 : Blo 1837620 1838847 := bstep (se 1 (by rfl) ⟨1379135, by rfl⟩ : syracuseStep 1838847 = 2758271) B2758271

theorem C0 (j : ℕ) (h1 : 459405 ≤ j) (h2 : j ≤ 459904) : Blo 1837620 (4 * j + 3) := by
  interval_cases j
  · exact B1837623
  · exact B1837627
  · exact B1837631
  · exact B1837635
  · exact B1837639
  · exact B1837643
  · exact B1837647
  · exact B1837651
  · exact B1837655
  · exact B1837659
  · exact B1837663
  · exact B1837667
  · exact B1837671
  · exact B1837675
  · exact B1837679
  · exact B1837683
  · exact B1837687
  · exact B1837691
  · exact B1837695
  · exact B1837699
  · exact B1837703
  · exact B1837707
  · exact B1837711
  · exact B1837715
  · exact B1837719
  · exact B1837723
  · exact B1837727
  · exact B1837731
  · exact B1837735
  · exact B1837739
  · exact B1837743
  · exact B1837747
  · exact B1837751
  · exact B1837755
  · exact B1837759
  · exact B1837763
  · exact B1837767
  · exact B1837771
  · exact B1837775
  · exact B1837779
  · exact B1837783
  · exact B1837787
  · exact B1837791
  · exact B1837795
  · exact B1837799
  · exact B1837803
  · exact B1837807
  · exact B1837811
  · exact B1837815
  · exact B1837819
  · exact B1837823
  · exact B1837827
  · exact B1837831
  · exact B1837835
  · exact B1837839
  · exact B1837843
  · exact B1837847
  · exact B1837851
  · exact B1837855
  · exact B1837859
  · exact B1837863
  · exact B1837867
  · exact B1837871
  · exact B1837875
  · exact B1837879
  · exact B1837883
  · exact B1837887
  · exact B1837891
  · exact B1837895
  · exact B1837899
  · exact B1837903
  · exact B1837907
  · exact B1837911
  · exact B1837915
  · exact B1837919
  · exact B1837923
  · exact B1837927
  · exact B1837931
  · exact B1837935
  · exact B1837939
  · exact B1837943
  · exact B1837947
  · exact B1837951
  · exact B1837955
  · exact B1837959
  · exact B1837963
  · exact B1837967
  · exact B1837971
  · exact B1837975
  · exact B1837979
  · exact B1837983
  · exact B1837987
  · exact B1837991
  · exact B1837995
  · exact B1837999
  · exact B1838003
  · exact B1838007
  · exact B1838011
  · exact B1838015
  · exact B1838019
  · exact B1838023
  · exact B1838027
  · exact B1838031
  · exact B1838035
  · exact B1838039
  · exact B1838043
  · exact B1838047
  · exact B1838051
  · exact B1838055
  · exact B1838059
  · exact B1838063
  · exact B1838067
  · exact B1838071
  · exact B1838075
  · exact B1838079
  · exact B1838083
  · exact B1838087
  · exact B1838091
  · exact B1838095
  · exact B1838099
  · exact B1838103
  · exact B1838107
  · exact B1838111
  · exact B1838115
  · exact B1838119
  · exact B1838123
  · exact B1838127
  · exact B1838131
  · exact B1838135
  · exact B1838139
  · exact B1838143
  · exact B1838147
  · exact B1838151
  · exact B1838155
  · exact B1838159
  · exact B1838163
  · exact B1838167
  · exact B1838171
  · exact B1838175
  · exact B1838179
  · exact B1838183
  · exact B1838187
  · exact B1838191
  · exact B1838195
  · exact B1838199
  · exact B1838203
  · exact B1838207
  · exact B1838211
  · exact B1838215
  · exact B1838219
  · exact B1838223
  · exact B1838227
  · exact B1838231
  · exact B1838235
  · exact B1838239
  · exact B1838243
  · exact B1838247
  · exact B1838251
  · exact B1838255
  · exact B1838259
  · exact B1838263
  · exact B1838267
  · exact B1838271
  · exact B1838275
  · exact B1838279
  · exact B1838283
  · exact B1838287
  · exact B1838291
  · exact B1838295
  · exact B1838299
  · exact B1838303
  · exact B1838307
  · exact B1838311
  · exact B1838315
  · exact B1838319
  · exact B1838323
  · exact B1838327
  · exact B1838331
  · exact B1838335
  · exact B1838339
  · exact B1838343
  · exact B1838347
  · exact B1838351
  · exact B1838355
  · exact B1838359
  · exact B1838363
  · exact B1838367
  · exact B1838371
  · exact B1838375
  · exact B1838379
  · exact B1838383
  · exact B1838387
  · exact B1838391
  · exact B1838395
  · exact B1838399
  · exact B1838403
  · exact B1838407
  · exact B1838411
  · exact B1838415
  · exact B1838419
  · exact B1838423
  · exact B1838427
  · exact B1838431
  · exact B1838435
  · exact B1838439
  · exact B1838443
  · exact B1838447
  · exact B1838451
  · exact B1838455
  · exact B1838459
  · exact B1838463
  · exact B1838467
  · exact B1838471
  · exact B1838475
  · exact B1838479
  · exact B1838483
  · exact B1838487
  · exact B1838491
  · exact B1838495
  · exact B1838499
  · exact B1838503
  · exact B1838507
  · exact B1838511
  · exact B1838515
  · exact B1838519
  · exact B1838523
  · exact B1838527
  · exact B1838531
  · exact B1838535
  · exact B1838539
  · exact B1838543
  · exact B1838547
  · exact B1838551
  · exact B1838555
  · exact B1838559
  · exact B1838563
  · exact B1838567
  · exact B1838571
  · exact B1838575
  · exact B1838579
  · exact B1838583
  · exact B1838587
  · exact B1838591
  · exact B1838595
  · exact B1838599
  · exact B1838603
  · exact B1838607
  · exact B1838611
  · exact B1838615
  · exact B1838619
  · exact B1838623
  · exact B1838627
  · exact B1838631
  · exact B1838635
  · exact B1838639
  · exact B1838643
  · exact B1838647
  · exact B1838651
  · exact B1838655
  · exact B1838659
  · exact B1838663
  · exact B1838667
  · exact B1838671
  · exact B1838675
  · exact B1838679
  · exact B1838683
  · exact B1838687
  · exact B1838691
  · exact B1838695
  · exact B1838699
  · exact B1838703
  · exact B1838707
  · exact B1838711
  · exact B1838715
  · exact B1838719
  · exact B1838723
  · exact B1838727
  · exact B1838731
  · exact B1838735
  · exact B1838739
  · exact B1838743
  · exact B1838747
  · exact B1838751
  · exact B1838755
  · exact B1838759
  · exact B1838763
  · exact B1838767
  · exact B1838771
  · exact B1838775
  · exact B1838779
  · exact B1838783
  · exact B1838787
  · exact B1838791
  · exact B1838795
  · exact B1838799
  · exact B1838803
  · exact B1838807
  · exact B1838811
  · exact B1838815
  · exact B1838819
  · exact B1838823
  · exact B1838827
  · exact B1838831
  · exact B1838835
  · exact B1838839
  · exact B1838843
  · exact B1838847
  · exact B1838851
  · exact B1838855
  · exact B1838859
  · exact B1838863
  · exact B1838867
  · exact B1838871
  · exact B1838875
  · exact B1838879
  · exact B1838883
  · exact B1838887
  · exact B1838891
  · exact B1838895
  · exact B1838899
  · exact B1838903
  · exact B1838907
  · exact B1838911
  · exact B1838915
  · exact B1838919
  · exact B1838923
  · exact B1838927
  · exact B1838931
  · exact B1838935
  · exact B1838939
  · exact B1838943
  · exact B1838947
  · exact B1838951
  · exact B1838955
  · exact B1838959
  · exact B1838963
  · exact B1838967
  · exact B1838971
  · exact B1838975
  · exact B1838979
  · exact B1838983
  · exact B1838987
  · exact B1838991
  · exact B1838995
  · exact B1838999
  · exact B1839003
  · exact B1839007
  · exact B1839011
  · exact B1839015
  · exact B1839019
  · exact B1839023
  · exact B1839027
  · exact B1839031
  · exact B1839035
  · exact B1839039
  · exact B1839043
  · exact B1839047
  · exact B1839051
  · exact B1839055
  · exact B1839059
  · exact B1839063
  · exact B1839067
  · exact B1839071
  · exact B1839075
  · exact B1839079
  · exact B1839083
  · exact B1839087
  · exact B1839091
  · exact B1839095
  · exact B1839099
  · exact B1839103
  · exact B1839107
  · exact B1839111
  · exact B1839115
  · exact B1839119
  · exact B1839123
  · exact B1839127
  · exact B1839131
  · exact B1839135
  · exact B1839139
  · exact B1839143
  · exact B1839147
  · exact B1839151
  · exact B1839155
  · exact B1839159
  · exact B1839163
  · exact B1839167
  · exact B1839171
  · exact B1839175
  · exact B1839179
  · exact B1839183
  · exact B1839187
  · exact B1839191
  · exact B1839195
  · exact B1839199
  · exact B1839203
  · exact B1839207
  · exact B1839211
  · exact B1839215
  · exact B1839219
  · exact B1839223
  · exact B1839227
  · exact B1839231
  · exact B1839235
  · exact B1839239
  · exact B1839243
  · exact B1839247
  · exact B1839251
  · exact B1839255
  · exact B1839259
  · exact B1839263
  · exact B1839267
  · exact B1839271
  · exact B1839275
  · exact B1839279
  · exact B1839283
  · exact B1839287
  · exact B1839291
  · exact B1839295
  · exact B1839299
  · exact B1839303
  · exact B1839307
  · exact B1839311
  · exact B1839315
  · exact B1839319
  · exact B1839323
  · exact B1839327
  · exact B1839331
  · exact B1839335
  · exact B1839339
  · exact B1839343
  · exact B1839347
  · exact B1839351
  · exact B1839355
  · exact B1839359
  · exact B1839363
  · exact B1839367
  · exact B1839371
  · exact B1839375
  · exact B1839379
  · exact B1839383
  · exact B1839387
  · exact B1839391
  · exact B1839395
  · exact B1839399
  · exact B1839403
  · exact B1839407
  · exact B1839411
  · exact B1839415
  · exact B1839419
  · exact B1839423
  · exact B1839427
  · exact B1839431
  · exact B1839435
  · exact B1839439
  · exact B1839443
  · exact B1839447
  · exact B1839451
  · exact B1839455
  · exact B1839459
  · exact B1839463
  · exact B1839467
  · exact B1839471
  · exact B1839475
  · exact B1839479
  · exact B1839483
  · exact B1839487
  · exact B1839491
  · exact B1839495
  · exact B1839499
  · exact B1839503
  · exact B1839507
  · exact B1839511
  · exact B1839515
  · exact B1839519
  · exact B1839523
  · exact B1839527
  · exact B1839531
  · exact B1839535
  · exact B1839539
  · exact B1839543
  · exact B1839547
  · exact B1839551
  · exact B1839555
  · exact B1839559
  · exact B1839563
  · exact B1839567
  · exact B1839571
  · exact B1839575
  · exact B1839579
  · exact B1839583
  · exact B1839587
  · exact B1839591
  · exact B1839595
  · exact B1839599
  · exact B1839603
  · exact B1839607
  · exact B1839611
  · exact B1839615
  · exact B1839619

theorem solution (m : ℕ) (hlo : 1837620 ≤ m) (hhi : m ≤ 1839620) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 459405 ≤ j := by omega
    have hj2 : j ≤ 459904 := by omega
    have hb : Blo 1837620 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
