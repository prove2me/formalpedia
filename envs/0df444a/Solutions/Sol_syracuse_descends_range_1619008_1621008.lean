-- Prove2me | solution 1 for syracuse_descends_range_1619008_1621008
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:13:00.616598+00:00
-- url     : https://prove2.me/submissions/c822dfca-23c9-48f6-aeff-e30cdb90fda0

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


theorem B6152213 : Blo 1619008 6152213 := bbase (se 6 (by rfl) ⟨144192, by rfl⟩ : syracuseStep 6152213 = 288385) (by norm_num)
theorem B4612133 : Blo 1619008 4612133 := bbase (se 4 (by rfl) ⟨432387, by rfl⟩ : syracuseStep 4612133 = 864775) (by norm_num)
theorem B3645485 : Blo 1619008 3645485 := bbase (se 3 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 3645485 = 1367057) (by norm_num)
theorem B8200277 : Blo 1619008 8200277 := bbase (se 8 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 8200277 = 96097) (by norm_num)
theorem B1687649 : Blo 1619008 1687649 := bbase (se 2 (by rfl) ⟨632868, by rfl⟩ : syracuseStep 1687649 = 1265737) (by norm_num)
theorem B3645557 : Blo 1619008 3645557 := bbase (se 5 (by rfl) ⟨170885, by rfl⟩ : syracuseStep 3645557 = 341771) (by norm_num)
theorem B3645629 : Blo 1619008 3645629 := bbase (se 3 (by rfl) ⟨683555, by rfl⟩ : syracuseStep 3645629 = 1367111) (by norm_num)
theorem B3645701 : Blo 1619008 3645701 := bbase (se 4 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 3645701 = 683569) (by norm_num)
theorem B4612373 : Blo 1619008 4612373 := bbase (se 6 (by rfl) ⟨108102, by rfl⟩ : syracuseStep 4612373 = 216205) (by norm_num)
theorem B3506485 : Blo 1619008 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B3645773 : Blo 1619008 3645773 := bbase (se 3 (by rfl) ⟨683582, by rfl⟩ : syracuseStep 3645773 = 1367165) (by norm_num)
theorem B5464421 : Blo 1619008 5464421 := bbase (se 4 (by rfl) ⟨512289, by rfl⟩ : syracuseStep 5464421 = 1024579) (by norm_num)
theorem B1728901 : Blo 1619008 1728901 := bbase (se 4 (by rfl) ⟨162084, by rfl⟩ : syracuseStep 1728901 = 324169) (by norm_num)
theorem B3645845 : Blo 1619008 3645845 := bbase (se 6 (by rfl) ⟨85449, by rfl⟩ : syracuseStep 3645845 = 170899) (by norm_num)
theorem B4612565 : Blo 1619008 4612565 := bbase (se 7 (by rfl) ⟨54053, by rfl⟩ : syracuseStep 4612565 = 108107) (by norm_num)
theorem B3645917 : Blo 1619008 3645917 := bbase (se 3 (by rfl) ⟨683609, by rfl⟩ : syracuseStep 3645917 = 1367219) (by norm_num)
theorem B11084309 : Blo 1619008 11084309 := bbase (se 6 (by rfl) ⟨259788, by rfl⟩ : syracuseStep 11084309 = 519577) (by norm_num)
theorem B3645989 : Blo 1619008 3645989 := bbase (se 4 (by rfl) ⟨341811, by rfl⟩ : syracuseStep 3645989 = 683623) (by norm_num)
theorem B13845077 : Blo 1619008 13845077 := bbase (se 8 (by rfl) ⟨81123, by rfl⟩ : syracuseStep 13845077 = 162247) (by norm_num)
theorem B3646061 : Blo 1619008 3646061 := bbase (se 3 (by rfl) ⟨683636, by rfl⟩ : syracuseStep 3646061 = 1367273) (by norm_num)
theorem B3646133 : Blo 1619008 3646133 := bbase (se 5 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 3646133 = 341825) (by norm_num)
theorem B13837013 : Blo 1619008 13837013 := bbase (se 7 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 13837013 = 324305) (by norm_num)
theorem B3646205 : Blo 1619008 3646205 := bbase (se 3 (by rfl) ⟨683663, by rfl⟩ : syracuseStep 3646205 = 1367327) (by norm_num)
theorem B5464853 : Blo 1619008 5464853 := bbase (se 6 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 5464853 = 256165) (by norm_num)
theorem B1729345 : Blo 1619008 1729345 := bbase (se 2 (by rfl) ⟨648504, by rfl⟩ : syracuseStep 1729345 = 1297009) (by norm_num)
theorem B3646277 : Blo 1619008 3646277 := bbase (se 4 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 3646277 = 683677) (by norm_num)
theorem B2999173 : Blo 1619008 2999173 := bbase (se 4 (by rfl) ⟨281172, by rfl⟩ : syracuseStep 2999173 = 562345) (by norm_num)
theorem B3646349 : Blo 1619008 3646349 := bbase (se 3 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 3646349 = 1367381) (by norm_num)
theorem B3457981 : Blo 1619008 3457981 := bbase (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) (by norm_num)
theorem B1729469 : Blo 1619008 1729469 := bbase (se 3 (by rfl) ⟨324275, by rfl⟩ : syracuseStep 1729469 = 648551) (by norm_num)
theorem B3646421 : Blo 1619008 3646421 := bbase (se 7 (by rfl) ⟨42731, by rfl⟩ : syracuseStep 3646421 = 85463) (by norm_num)
theorem B1663997 : Blo 1619008 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B3646493 : Blo 1619008 3646493 := bbase (se 3 (by rfl) ⟨683717, by rfl⟩ : syracuseStep 3646493 = 1367435) (by norm_num)
theorem B2049077 : Blo 1619008 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B3646565 : Blo 1619008 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B2049133 : Blo 1619008 2049133 := bbase (se 3 (by rfl) ⟨384212, by rfl⟩ : syracuseStep 2049133 = 768425) (by norm_num)
theorem B3646637 : Blo 1619008 3646637 := bbase (se 3 (by rfl) ⟨683744, by rfl⟩ : syracuseStep 3646637 = 1367489) (by norm_num)
theorem B1729721 : Blo 1619008 1729721 := bbase (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) (by norm_num)
theorem B5465285 : Blo 1619008 5465285 := bbase (se 4 (by rfl) ⟨512370, by rfl⟩ : syracuseStep 5465285 = 1024741) (by norm_num)
theorem B2049229 : Blo 1619008 2049229 := bbase (se 3 (by rfl) ⟨384230, by rfl⟩ : syracuseStep 2049229 = 768461) (by norm_num)
theorem B3646709 : Blo 1619008 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B3646781 : Blo 1619008 3646781 := bbase (se 3 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 3646781 = 1367543) (by norm_num)
theorem B7996757 : Blo 1619008 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B8201573 : Blo 1619008 8201573 := bbase (se 4 (by rfl) ⟨768897, by rfl⟩ : syracuseStep 8201573 = 1537795) (by norm_num)
theorem B6571381 : Blo 1619008 6571381 := bbase (se 5 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 6571381 = 616067) (by norm_num)
theorem B2049401 : Blo 1619008 2049401 := bbase (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) (by norm_num)
theorem B3646853 : Blo 1619008 3646853 := bbase (se 4 (by rfl) ⟨341892, by rfl⟩ : syracuseStep 3646853 = 683785) (by norm_num)
theorem B3892621 : Blo 1619008 3892621 := bbase (se 3 (by rfl) ⟨729866, by rfl⟩ : syracuseStep 3892621 = 1459733) (by norm_num)
theorem B6235541 : Blo 1619008 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B2049457 : Blo 1619008 2049457 := bbase (se 2 (by rfl) ⟨768546, by rfl⟩ : syracuseStep 2049457 = 1537093) (by norm_num)
theorem B4613557 : Blo 1619008 4613557 := bbase (se 5 (by rfl) ⟨216260, by rfl⟩ : syracuseStep 4613557 = 432521) (by norm_num)
theorem B3646925 : Blo 1619008 3646925 := bbase (se 3 (by rfl) ⟨683798, by rfl⟩ : syracuseStep 3646925 = 1367597) (by norm_num)
theorem B6571525 : Blo 1619008 6571525 := bbase (se 4 (by rfl) ⟨616080, by rfl⟩ : syracuseStep 6571525 = 1232161) (by norm_num)
theorem B2049553 : Blo 1619008 2049553 := bbase (se 2 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 2049553 = 1537165) (by norm_num)
theorem B3646997 : Blo 1619008 3646997 := bbase (se 6 (by rfl) ⟨85476, by rfl⟩ : syracuseStep 3646997 = 170953) (by norm_num)
theorem B12306005 : Blo 1619008 12306005 := bbase (se 8 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 12306005 = 144211) (by norm_num)
theorem B3647069 : Blo 1619008 3647069 := bbase (se 3 (by rfl) ⟨683825, by rfl⟩ : syracuseStep 3647069 = 1367651) (by norm_num)
theorem B5465717 : Blo 1619008 5465717 := bbase (se 5 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 5465717 = 512411) (by norm_num)
theorem B3892853 : Blo 1619008 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B1730165 : Blo 1619008 1730165 := bbase (se 5 (by rfl) ⟨81101, by rfl⟩ : syracuseStep 1730165 = 162203) (by norm_num)
theorem B3647141 : Blo 1619008 3647141 := bbase (se 4 (by rfl) ⟨341919, by rfl⟩ : syracuseStep 3647141 = 683839) (by norm_num)
theorem B3696301 : Blo 1619008 3696301 := bbase (se 3 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 3696301 = 1386113) (by norm_num)
theorem B2049725 : Blo 1619008 2049725 := bbase (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) (by norm_num)
theorem B3647213 : Blo 1619008 3647213 := bbase (se 3 (by rfl) ⟨683852, by rfl⟩ : syracuseStep 3647213 = 1367705) (by norm_num)
theorem B2049781 : Blo 1619008 2049781 := bbase (se 5 (by rfl) ⟨96083, by rfl⟩ : syracuseStep 2049781 = 192167) (by norm_num)
theorem B3892997 : Blo 1619008 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B4376389 : Blo 1619008 4376389 := bbase (se 4 (by rfl) ⟨410286, by rfl⟩ : syracuseStep 4376389 = 820573) (by norm_num)
theorem B2049877 : Blo 1619008 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B2107225 : Blo 1619008 2107225 := bbase (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) (by norm_num)
theorem B1730413 : Blo 1619008 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B9226133 : Blo 1619008 9226133 := bbase (se 6 (by rfl) ⟨216237, by rfl⟩ : syracuseStep 9226133 = 432475) (by norm_num)
theorem B12298229 : Blo 1619008 12298229 := bbase (se 5 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 12298229 = 1152959) (by norm_num)
theorem B3893237 : Blo 1619008 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B2050049 : Blo 1619008 2050049 := bbase (se 2 (by rfl) ⟨768768, by rfl⟩ : syracuseStep 2050049 = 1537537) (by norm_num)
theorem B5466149 : Blo 1619008 5466149 := bbase (se 4 (by rfl) ⟨512451, by rfl⟩ : syracuseStep 5466149 = 1024903) (by norm_num)
theorem B2050105 : Blo 1619008 2050105 := bbase (se 2 (by rfl) ⟨768789, by rfl⟩ : syracuseStep 2050105 = 1537579) (by norm_num)
theorem B3074125 : Blo 1619008 3074125 := bbase (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) (by norm_num)
theorem B6154325 : Blo 1619008 6154325 := bbase (se 8 (by rfl) ⟨36060, by rfl⟩ : syracuseStep 6154325 = 72121) (by norm_num)
theorem B2918501 : Blo 1619008 2918501 := bbase (se 4 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 2918501 = 547219) (by norm_num)
theorem B4376693 : Blo 1619008 4376693 := bbase (se 5 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 4376693 = 410315) (by norm_num)
theorem B5187701 : Blo 1619008 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B2050201 : Blo 1619008 2050201 := bbase (se 2 (by rfl) ⟨768825, by rfl⟩ : syracuseStep 2050201 = 1537651) (by norm_num)
theorem B3074269 : Blo 1619008 3074269 := bbase (se 3 (by rfl) ⟨576425, by rfl⟩ : syracuseStep 3074269 = 1152851) (by norm_num)
theorem B6916373 : Blo 1619008 6916373 := bbase (se 6 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 6916373 = 324205) (by norm_num)
theorem B1730857 : Blo 1619008 1730857 := bbase (se 2 (by rfl) ⟨649071, by rfl⟩ : syracuseStep 1730857 = 1298143) (by norm_num)
theorem B2050373 : Blo 1619008 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B4098397 : Blo 1619008 4098397 := bbase (se 3 (by rfl) ⟨768449, by rfl⟩ : syracuseStep 4098397 = 1536899) (by norm_num)
theorem B1730917 : Blo 1619008 1730917 := bbase (se 4 (by rfl) ⟨162273, by rfl⟩ : syracuseStep 1730917 = 324547) (by norm_num)
theorem B2107765 : Blo 1619008 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B6154613 : Blo 1619008 6154613 := bbase (se 5 (by rfl) ⟨288497, by rfl⟩ : syracuseStep 6154613 = 576995) (by norm_num)
theorem B3074429 : Blo 1619008 3074429 := bbase (se 3 (by rfl) ⟨576455, by rfl⟩ : syracuseStep 3074429 = 1152911) (by norm_num)
theorem B2050429 : Blo 1619008 2050429 := bbase (se 3 (by rfl) ⟨384455, by rfl⟩ : syracuseStep 2050429 = 768911) (by norm_num)
theorem B3459485 : Blo 1619008 3459485 := bbase (se 3 (by rfl) ⟨648653, by rfl⟩ : syracuseStep 3459485 = 1297307) (by norm_num)
theorem B4098509 : Blo 1619008 4098509 := bbase (se 3 (by rfl) ⟨768470, by rfl⟩ : syracuseStep 4098509 = 1536941) (by norm_num)
theorem B5466581 : Blo 1619008 5466581 := bbase (se 7 (by rfl) ⟨64061, by rfl⟩ : syracuseStep 5466581 = 128123) (by norm_num)
theorem B2050525 : Blo 1619008 2050525 := bbase (se 3 (by rfl) ⟨384473, by rfl⟩ : syracuseStep 2050525 = 768947) (by norm_num)
theorem B4614661 : Blo 1619008 4614661 := bbase (se 4 (by rfl) ⟨432624, by rfl⟩ : syracuseStep 4614661 = 865249) (by norm_num)
theorem B3074573 : Blo 1619008 3074573 := bbase (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) (by norm_num)
theorem B3459629 : Blo 1619008 3459629 := bbase (se 3 (by rfl) ⟨648680, by rfl⟩ : syracuseStep 3459629 = 1297361) (by norm_num)
theorem B6916661 : Blo 1619008 6916661 := bbase (se 5 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 6916661 = 648437) (by norm_num)
theorem B2919005 : Blo 1619008 2919005 := bbase (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) (by norm_num)
theorem B8202869 : Blo 1619008 8202869 := bbase (se 5 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 8202869 = 769019) (by norm_num)
theorem B2050697 : Blo 1619008 2050697 := bbase (se 2 (by rfl) ⟨769011, by rfl⟩ : syracuseStep 2050697 = 1538023) (by norm_num)
theorem B4098701 : Blo 1619008 4098701 := bbase (se 3 (by rfl) ⟨768506, by rfl⟩ : syracuseStep 4098701 = 1537013) (by norm_num)
theorem B2050753 : Blo 1619008 2050753 := bbase (se 2 (by rfl) ⟨769032, by rfl⟩ : syracuseStep 2050753 = 1538065) (by norm_num)
theorem B1821397 : Blo 1619008 1821397 := bbase (se 7 (by rfl) ⟨21344, by rfl⟩ : syracuseStep 1821397 = 42689) (by norm_num)
theorem B3894005 : Blo 1619008 3894005 := bbase (se 5 (by rfl) ⟨182531, by rfl⟩ : syracuseStep 3894005 = 365063) (by norm_num)
theorem B1821433 : Blo 1619008 1821433 := bbase (se 2 (by rfl) ⟨683037, by rfl⟩ : syracuseStep 1821433 = 1366075) (by norm_num)
theorem B1821469 : Blo 1619008 1821469 := bbase (se 3 (by rfl) ⟨341525, by rfl⟩ : syracuseStep 1821469 = 683051) (by norm_num)
theorem B2050849 : Blo 1619008 2050849 := bbase (se 2 (by rfl) ⟨769068, by rfl⟩ : syracuseStep 2050849 = 1538137) (by norm_num)
theorem B3074861 : Blo 1619008 3074861 := bbase (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) (by norm_num)
theorem B1821505 : Blo 1619008 1821505 := bbase (se 2 (by rfl) ⟨683064, by rfl⟩ : syracuseStep 1821505 = 1366129) (by norm_num)
theorem B3943237 : Blo 1619008 3943237 := bbase (se 4 (by rfl) ⟨369678, by rfl⟩ : syracuseStep 3943237 = 739357) (by norm_num)
theorem B1821541 : Blo 1619008 1821541 := bbase (se 4 (by rfl) ⟨170769, by rfl⟩ : syracuseStep 1821541 = 341539) (by norm_num)
theorem B1641341 : Blo 1619008 1641341 := bbase (se 3 (by rfl) ⟨307751, by rfl⟩ : syracuseStep 1641341 = 615503) (by norm_num)
theorem B5467013 : Blo 1619008 5467013 := bbase (se 4 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 5467013 = 1025065) (by norm_num)
theorem B1821577 : Blo 1619008 1821577 := bbase (se 2 (by rfl) ⟨683091, by rfl⟩ : syracuseStep 1821577 = 1366183) (by norm_num)
theorem B3459989 : Blo 1619008 3459989 := bbase (se 6 (by rfl) ⟨81093, by rfl⟩ : syracuseStep 3459989 = 162187) (by norm_num)
theorem B2771869 : Blo 1619008 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B2960285 : Blo 1619008 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B1821613 : Blo 1619008 1821613 := bbase (se 3 (by rfl) ⟨341552, by rfl⟩ : syracuseStep 1821613 = 683105) (by norm_num)
theorem B3075013 : Blo 1619008 3075013 := bbase (se 4 (by rfl) ⟨288282, by rfl⟩ : syracuseStep 3075013 = 576565) (by norm_num)
theorem B2051021 : Blo 1619008 2051021 := bbase (se 3 (by rfl) ⟨384566, by rfl⟩ : syracuseStep 2051021 = 769133) (by norm_num)
theorem B1821649 : Blo 1619008 1821649 := bbase (se 2 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 1821649 = 1366237) (by norm_num)
theorem B4377557 : Blo 1619008 4377557 := bbase (se 7 (by rfl) ⟨51299, by rfl⟩ : syracuseStep 4377557 = 102599) (by norm_num)
theorem B4099045 : Blo 1619008 4099045 := bbase (se 4 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 4099045 = 768571) (by norm_num)
theorem B1821685 : Blo 1619008 1821685 := bbase (se 5 (by rfl) ⟨85391, by rfl⟩ : syracuseStep 1821685 = 170783) (by norm_num)
theorem B2051077 : Blo 1619008 2051077 := bbase (se 4 (by rfl) ⟨192288, by rfl⟩ : syracuseStep 2051077 = 384577) (by norm_num)
theorem B12471317 : Blo 1619008 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B1821721 : Blo 1619008 1821721 := bbase (se 2 (by rfl) ⟨683145, by rfl⟩ : syracuseStep 1821721 = 1366291) (by norm_num)
theorem B9227317 : Blo 1619008 9227317 := bbase (se 5 (by rfl) ⟨432530, by rfl⟩ : syracuseStep 9227317 = 865061) (by norm_num)
theorem B1821757 : Blo 1619008 1821757 := bbase (se 3 (by rfl) ⟨341579, by rfl⟩ : syracuseStep 1821757 = 683159) (by norm_num)
theorem B4099157 : Blo 1619008 4099157 := bbase (se 8 (by rfl) ⟨24018, by rfl⟩ : syracuseStep 4099157 = 48037) (by norm_num)
theorem B1821793 : Blo 1619008 1821793 := bbase (se 2 (by rfl) ⟨683172, by rfl⟩ : syracuseStep 1821793 = 1366345) (by norm_num)
theorem B8309861 : Blo 1619008 8309861 := bbase (se 4 (by rfl) ⟨779049, by rfl⟩ : syracuseStep 8309861 = 1558099) (by norm_num)
theorem B2051173 : Blo 1619008 2051173 := bbase (se 4 (by rfl) ⟨192297, by rfl⟩ : syracuseStep 2051173 = 384595) (by norm_num)
theorem B1846381 : Blo 1619008 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B1821829 : Blo 1619008 1821829 := bbase (se 4 (by rfl) ⟨170796, by rfl⟩ : syracuseStep 1821829 = 341593) (by norm_num)
theorem B1821865 : Blo 1619008 1821865 := bbase (se 2 (by rfl) ⟨683199, by rfl⟩ : syracuseStep 1821865 = 1366399) (by norm_num)
theorem B1821901 : Blo 1619008 1821901 := bbase (se 3 (by rfl) ⟨341606, by rfl⟩ : syracuseStep 1821901 = 683213) (by norm_num)
theorem B1821937 : Blo 1619008 1821937 := bbase (se 2 (by rfl) ⟨683226, by rfl⟩ : syracuseStep 1821937 = 1366453) (by norm_num)
theorem B3075317 : Blo 1619008 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2051345 : Blo 1619008 2051345 := bbase (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) (by norm_num)
theorem B4099349 : Blo 1619008 4099349 := bbase (se 6 (by rfl) ⟨96078, by rfl⟩ : syracuseStep 4099349 = 192157) (by norm_num)
theorem B1821973 : Blo 1619008 1821973 := bbase (se 6 (by rfl) ⟨42702, by rfl⟩ : syracuseStep 1821973 = 85405) (by norm_num)
theorem B6917413 : Blo 1619008 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B5467445 : Blo 1619008 5467445 := bbase (se 5 (by rfl) ⟨256286, by rfl⟩ : syracuseStep 5467445 = 512573) (by norm_num)
theorem B1822009 : Blo 1619008 1822009 := bbase (se 2 (by rfl) ⟨683253, by rfl⟩ : syracuseStep 1822009 = 1366507) (by norm_num)
theorem B2051401 : Blo 1619008 2051401 := bbase (se 2 (by rfl) ⟨769275, by rfl⟩ : syracuseStep 2051401 = 1538551) (by norm_num)
theorem B1822045 : Blo 1619008 1822045 := bbase (se 3 (by rfl) ⟨341633, by rfl⟩ : syracuseStep 1822045 = 683267) (by norm_num)
theorem B1822081 : Blo 1619008 1822081 := bbase (se 2 (by rfl) ⟨683280, by rfl⟩ : syracuseStep 1822081 = 1366561) (by norm_num)
theorem B4377989 : Blo 1619008 4377989 := bbase (se 4 (by rfl) ⟨410436, by rfl⟩ : syracuseStep 4377989 = 820873) (by norm_num)
theorem B1822117 : Blo 1619008 1822117 := bbase (se 4 (by rfl) ⟨170823, by rfl⟩ : syracuseStep 1822117 = 341647) (by norm_num)
theorem B2051497 : Blo 1619008 2051497 := bbase (se 2 (by rfl) ⟨769311, by rfl⟩ : syracuseStep 2051497 = 1538623) (by norm_num)
theorem B10374581 : Blo 1619008 10374581 := bbase (se 5 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 10374581 = 972617) (by norm_num)
theorem B1822153 : Blo 1619008 1822153 := bbase (se 2 (by rfl) ⟨683307, by rfl⟩ : syracuseStep 1822153 = 1366615) (by norm_num)
theorem B1822189 : Blo 1619008 1822189 := bbase (se 3 (by rfl) ⟨341660, by rfl⟩ : syracuseStep 1822189 = 683321) (by norm_num)
theorem B1822225 : Blo 1619008 1822225 := bbase (se 2 (by rfl) ⟨683334, by rfl⟩ : syracuseStep 1822225 = 1366669) (by norm_num)
theorem B1945129 : Blo 1619008 1945129 := bbase (se 2 (by rfl) ⟨729423, by rfl⟩ : syracuseStep 1945129 = 1458847) (by norm_num)
theorem B1822261 : Blo 1619008 1822261 := bbase (se 5 (by rfl) ⟨85418, by rfl⟩ : syracuseStep 1822261 = 170837) (by norm_num)
theorem B1822297 : Blo 1619008 1822297 := bbase (se 2 (by rfl) ⟨683361, by rfl⟩ : syracuseStep 1822297 = 1366723) (by norm_num)
theorem B2428517 : Blo 1619008 2428517 := bbase (se 4 (by rfl) ⟨227673, by rfl⟩ : syracuseStep 2428517 = 455347) (by norm_num)
theorem B4099693 : Blo 1619008 4099693 := bbase (se 3 (by rfl) ⟨768692, by rfl⟩ : syracuseStep 4099693 = 1537385) (by norm_num)
theorem B2428541 : Blo 1619008 2428541 := bbase (se 3 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 2428541 = 910703) (by norm_num)
theorem B1822333 : Blo 1619008 1822333 := bbase (se 3 (by rfl) ⟨341687, by rfl⟩ : syracuseStep 1822333 = 683375) (by norm_num)
theorem B2428565 : Blo 1619008 2428565 := bbase (se 6 (by rfl) ⟨56919, by rfl⟩ : syracuseStep 2428565 = 113839) (by norm_num)
theorem B2305685 : Blo 1619008 2305685 := bbase (se 6 (by rfl) ⟨54039, by rfl⟩ : syracuseStep 2305685 = 108079) (by norm_num)
theorem B1822369 : Blo 1619008 1822369 := bbase (se 2 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 1822369 = 1366777) (by norm_num)
theorem B2428589 : Blo 1619008 2428589 := bbase (se 3 (by rfl) ⟨455360, by rfl⟩ : syracuseStep 2428589 = 910721) (by norm_num)
theorem B7786165 : Blo 1619008 7786165 := bbase (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) (by norm_num)
theorem B2428613 : Blo 1619008 2428613 := bbase (se 4 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 2428613 = 455365) (by norm_num)
theorem B1822405 : Blo 1619008 1822405 := bbase (se 4 (by rfl) ⟨170850, by rfl⟩ : syracuseStep 1822405 = 341701) (by norm_num)
theorem B6565589 : Blo 1619008 6565589 := bbase (se 7 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 6565589 = 153881) (by norm_num)
theorem B2428637 : Blo 1619008 2428637 := bbase (se 3 (by rfl) ⟨455369, by rfl⟩ : syracuseStep 2428637 = 910739) (by norm_num)
theorem B4099805 : Blo 1619008 4099805 := bbase (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) (by norm_num)
theorem B5467877 : Blo 1619008 5467877 := bbase (se 4 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 5467877 = 1025227) (by norm_num)
theorem B1822441 : Blo 1619008 1822441 := bbase (se 2 (by rfl) ⟨683415, by rfl⟩ : syracuseStep 1822441 = 1366831) (by norm_num)
theorem B2428661 : Blo 1619008 2428661 := bbase (se 5 (by rfl) ⟨113843, by rfl⟩ : syracuseStep 2428661 = 227687) (by norm_num)
theorem B7589621 : Blo 1619008 7589621 := bbase (se 5 (by rfl) ⟨355763, by rfl⟩ : syracuseStep 7589621 = 711527) (by norm_num)
theorem B1642241 : Blo 1619008 1642241 := bbase (se 2 (by rfl) ⟨615840, by rfl⟩ : syracuseStep 1642241 = 1231681) (by norm_num)
theorem B2428685 : Blo 1619008 2428685 := bbase (se 3 (by rfl) ⟨455378, by rfl⟩ : syracuseStep 2428685 = 910757) (by norm_num)
theorem B1822477 : Blo 1619008 1822477 := bbase (se 3 (by rfl) ⟨341714, by rfl⟩ : syracuseStep 1822477 = 683429) (by norm_num)
theorem B3460877 : Blo 1619008 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2428709 : Blo 1619008 2428709 := bbase (se 4 (by rfl) ⟨227691, by rfl⟩ : syracuseStep 2428709 = 455383) (by norm_num)
theorem B1822513 : Blo 1619008 1822513 := bbase (se 2 (by rfl) ⟨683442, by rfl⟩ : syracuseStep 1822513 = 1366885) (by norm_num)
theorem B2428733 : Blo 1619008 2428733 := bbase (se 3 (by rfl) ⟨455387, by rfl⟩ : syracuseStep 2428733 = 910775) (by norm_num)
theorem B2428757 : Blo 1619008 2428757 := bbase (se 9 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 2428757 = 14231) (by norm_num)
theorem B1822549 : Blo 1619008 1822549 := bbase (se 9 (by rfl) ⟨5339, by rfl⟩ : syracuseStep 1822549 = 10679) (by norm_num)
theorem B2428781 : Blo 1619008 2428781 := bbase (se 3 (by rfl) ⟨455396, by rfl⟩ : syracuseStep 2428781 = 910793) (by norm_num)
theorem B1822585 : Blo 1619008 1822585 := bbase (se 2 (by rfl) ⟨683469, by rfl⟩ : syracuseStep 1822585 = 1366939) (by norm_num)
theorem B2428805 : Blo 1619008 2428805 := bbase (se 4 (by rfl) ⟨227700, by rfl⟩ : syracuseStep 2428805 = 455401) (by norm_num)
theorem B8204165 : Blo 1619008 8204165 := bbase (se 4 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 8204165 = 1538281) (by norm_num)
theorem B4157333 : Blo 1619008 4157333 := bbase (se 6 (by rfl) ⟨97437, by rfl⟩ : syracuseStep 4157333 = 194875) (by norm_num)
theorem B2428829 : Blo 1619008 2428829 := bbase (se 3 (by rfl) ⟨455405, by rfl⟩ : syracuseStep 2428829 = 910811) (by norm_num)
theorem B4099997 : Blo 1619008 4099997 := bbase (se 3 (by rfl) ⟨768749, by rfl⟩ : syracuseStep 4099997 = 1537499) (by norm_num)
theorem B1822621 : Blo 1619008 1822621 := bbase (se 3 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 1822621 = 683483) (by norm_num)
theorem B6148021 : Blo 1619008 6148021 := bbase (se 5 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 6148021 = 576377) (by norm_num)
theorem B2428853 : Blo 1619008 2428853 := bbase (se 5 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 2428853 = 227705) (by norm_num)
theorem B1822657 : Blo 1619008 1822657 := bbase (se 2 (by rfl) ⟨683496, by rfl⟩ : syracuseStep 1822657 = 1366993) (by norm_num)
theorem B2428877 : Blo 1619008 2428877 := bbase (se 3 (by rfl) ⟨455414, by rfl⟩ : syracuseStep 2428877 = 910829) (by norm_num)
theorem B2428901 : Blo 1619008 2428901 := bbase (se 4 (by rfl) ⟨227709, by rfl⟩ : syracuseStep 2428901 = 455419) (by norm_num)
theorem B1822693 : Blo 1619008 1822693 := bbase (se 4 (by rfl) ⟨170877, by rfl⟩ : syracuseStep 1822693 = 341755) (by norm_num)
theorem B3076069 : Blo 1619008 3076069 := bbase (se 4 (by rfl) ⟨288381, by rfl⟩ : syracuseStep 3076069 = 576763) (by norm_num)
theorem B2428925 : Blo 1619008 2428925 := bbase (se 3 (by rfl) ⟨455423, by rfl⟩ : syracuseStep 2428925 = 910847) (by norm_num)
theorem B6918149 : Blo 1619008 6918149 := bbase (se 4 (by rfl) ⟨648576, by rfl⟩ : syracuseStep 6918149 = 1297153) (by norm_num)
theorem B3461125 : Blo 1619008 3461125 := bbase (se 4 (by rfl) ⟨324480, by rfl⟩ : syracuseStep 3461125 = 648961) (by norm_num)
theorem B1822729 : Blo 1619008 1822729 := bbase (se 2 (by rfl) ⟨683523, by rfl⟩ : syracuseStep 1822729 = 1367047) (by norm_num)
theorem B2428949 : Blo 1619008 2428949 := bbase (se 6 (by rfl) ⟨56928, by rfl⟩ : syracuseStep 2428949 = 113857) (by norm_num)
theorem B2428973 : Blo 1619008 2428973 := bbase (se 3 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 2428973 = 910865) (by norm_num)
theorem B1822765 : Blo 1619008 1822765 := bbase (se 3 (by rfl) ⟨341768, by rfl⟩ : syracuseStep 1822765 = 683537) (by norm_num)
theorem B2428997 : Blo 1619008 2428997 := bbase (se 4 (by rfl) ⟨227718, by rfl⟩ : syracuseStep 2428997 = 455437) (by norm_num)
theorem B1642573 : Blo 1619008 1642573 := bbase (se 3 (by rfl) ⟨307982, by rfl⟩ : syracuseStep 1642573 = 615965) (by norm_num)
theorem B1822801 : Blo 1619008 1822801 := bbase (se 2 (by rfl) ⟨683550, by rfl⟩ : syracuseStep 1822801 = 1367101) (by norm_num)
theorem B2429021 : Blo 1619008 2429021 := bbase (se 3 (by rfl) ⟨455441, by rfl⟩ : syracuseStep 2429021 = 910883) (by norm_num)
theorem B2429045 : Blo 1619008 2429045 := bbase (se 5 (by rfl) ⟨113861, by rfl⟩ : syracuseStep 2429045 = 227723) (by norm_num)
theorem B1822837 : Blo 1619008 1822837 := bbase (se 5 (by rfl) ⟨85445, by rfl⟩ : syracuseStep 1822837 = 170891) (by norm_num)
theorem B3076213 : Blo 1619008 3076213 := bbase (se 5 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 3076213 = 288395) (by norm_num)
theorem B2429069 : Blo 1619008 2429069 := bbase (se 3 (by rfl) ⟨455450, by rfl⟩ : syracuseStep 2429069 = 910901) (by norm_num)
theorem B5468309 : Blo 1619008 5468309 := bbase (se 6 (by rfl) ⟨128163, by rfl⟩ : syracuseStep 5468309 = 256327) (by norm_num)
theorem B1822873 : Blo 1619008 1822873 := bbase (se 2 (by rfl) ⟨683577, by rfl⟩ : syracuseStep 1822873 = 1367155) (by norm_num)
theorem B2732197 : Blo 1619008 2732197 := bbase (se 4 (by rfl) ⟨256143, by rfl⟩ : syracuseStep 2732197 = 512287) (by norm_num)
theorem B2429093 : Blo 1619008 2429093 := bbase (se 4 (by rfl) ⟨227727, by rfl⟩ : syracuseStep 2429093 = 455455) (by norm_num)
theorem B2429117 : Blo 1619008 2429117 := bbase (se 3 (by rfl) ⟨455459, by rfl⟩ : syracuseStep 2429117 = 910919) (by norm_num)
theorem B2306237 : Blo 1619008 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B1822909 : Blo 1619008 1822909 := bbase (se 3 (by rfl) ⟨341795, by rfl⟩ : syracuseStep 1822909 = 683591) (by norm_num)
theorem B2429141 : Blo 1619008 2429141 := bbase (se 7 (by rfl) ⟨28466, by rfl⟩ : syracuseStep 2429141 = 56933) (by norm_num)
theorem B1822945 : Blo 1619008 1822945 := bbase (se 2 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 1822945 = 1367209) (by norm_num)
theorem B6148325 : Blo 1619008 6148325 := bbase (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) (by norm_num)
theorem B2429165 : Blo 1619008 2429165 := bbase (se 3 (by rfl) ⟨455468, by rfl⟩ : syracuseStep 2429165 = 910937) (by norm_num)
theorem B4100341 : Blo 1619008 4100341 := bbase (se 5 (by rfl) ⟨192203, by rfl⟩ : syracuseStep 4100341 = 384407) (by norm_num)
theorem B2732285 : Blo 1619008 2732285 := bbase (se 3 (by rfl) ⟨512303, by rfl⟩ : syracuseStep 2732285 = 1024607) (by norm_num)
theorem B2429189 : Blo 1619008 2429189 := bbase (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) (by norm_num)
theorem B1822981 : Blo 1619008 1822981 := bbase (se 4 (by rfl) ⟨170904, by rfl⟩ : syracuseStep 1822981 = 341809) (by norm_num)
theorem B3076373 : Blo 1619008 3076373 := bbase (se 6 (by rfl) ⟨72102, by rfl⟩ : syracuseStep 3076373 = 144205) (by norm_num)
theorem B2429213 : Blo 1619008 2429213 := bbase (se 3 (by rfl) ⟨455477, by rfl⟩ : syracuseStep 2429213 = 910955) (by norm_num)
theorem B8196389 : Blo 1619008 8196389 := bbase (se 4 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 8196389 = 1536823) (by norm_num)
theorem B1823017 : Blo 1619008 1823017 := bbase (se 2 (by rfl) ⟨683631, by rfl⟩ : syracuseStep 1823017 = 1367263) (by norm_num)
theorem B2429237 : Blo 1619008 2429237 := bbase (se 5 (by rfl) ⟨113870, by rfl⟩ : syracuseStep 2429237 = 227741) (by norm_num)
theorem B5189957 : Blo 1619008 5189957 := bbase (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) (by norm_num)
theorem B1847621 : Blo 1619008 1847621 := bbase (se 4 (by rfl) ⟨173214, by rfl⟩ : syracuseStep 1847621 = 346429) (by norm_num)
theorem B2429261 : Blo 1619008 2429261 := bbase (se 3 (by rfl) ⟨455486, by rfl⟩ : syracuseStep 2429261 = 910973) (by norm_num)
theorem B1823053 : Blo 1619008 1823053 := bbase (se 3 (by rfl) ⟨341822, by rfl⟩ : syracuseStep 1823053 = 683645) (by norm_num)
theorem B2429285 : Blo 1619008 2429285 := bbase (se 4 (by rfl) ⟨227745, by rfl⟩ : syracuseStep 2429285 = 455491) (by norm_num)
theorem B4100453 : Blo 1619008 4100453 := bbase (se 4 (by rfl) ⟨384417, by rfl⟩ : syracuseStep 4100453 = 768835) (by norm_num)
theorem B1823089 : Blo 1619008 1823089 := bbase (se 2 (by rfl) ⟨683658, by rfl⟩ : syracuseStep 1823089 = 1367317) (by norm_num)
theorem B11088245 : Blo 1619008 11088245 := bbase (se 5 (by rfl) ⟨519761, by rfl⟩ : syracuseStep 11088245 = 1039523) (by norm_num)
theorem B2732413 : Blo 1619008 2732413 := bbase (se 3 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 2732413 = 1024655) (by norm_num)
theorem B2429309 : Blo 1619008 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B1642877 : Blo 1619008 1642877 := bbase (se 3 (by rfl) ⟨308039, by rfl⟩ : syracuseStep 1642877 = 616079) (by norm_num)
theorem B2429333 : Blo 1619008 2429333 := bbase (se 6 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 2429333 = 113875) (by norm_num)
theorem B1823125 : Blo 1619008 1823125 := bbase (se 6 (by rfl) ⟨42729, by rfl⟩ : syracuseStep 1823125 = 85459) (by norm_num)
theorem B3076517 : Blo 1619008 3076517 := bbase (se 4 (by rfl) ⟨288423, by rfl⟩ : syracuseStep 3076517 = 576847) (by norm_num)
theorem B2429357 : Blo 1619008 2429357 := bbase (se 3 (by rfl) ⟨455504, by rfl⟩ : syracuseStep 2429357 = 911009) (by norm_num)
theorem B1823161 : Blo 1619008 1823161 := bbase (se 2 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 1823161 = 1367371) (by norm_num)
theorem B2429381 : Blo 1619008 2429381 := bbase (se 4 (by rfl) ⟨227754, by rfl⟩ : syracuseStep 2429381 = 455509) (by norm_num)
theorem B5190085 : Blo 1619008 5190085 := bbase (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) (by norm_num)
theorem B2732501 : Blo 1619008 2732501 := bbase (se 7 (by rfl) ⟨32021, by rfl⟩ : syracuseStep 2732501 = 64043) (by norm_num)
theorem B2339285 : Blo 1619008 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B2429405 : Blo 1619008 2429405 := bbase (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) (by norm_num)
theorem B1823197 : Blo 1619008 1823197 := bbase (se 3 (by rfl) ⟨341849, by rfl⟩ : syracuseStep 1823197 = 683699) (by norm_num)
theorem B2429429 : Blo 1619008 2429429 := bbase (se 5 (by rfl) ⟨113879, by rfl⟩ : syracuseStep 2429429 = 227759) (by norm_num)
theorem B3461629 : Blo 1619008 3461629 := bbase (se 3 (by rfl) ⟨649055, by rfl⟩ : syracuseStep 3461629 = 1298111) (by norm_num)
theorem B1823233 : Blo 1619008 1823233 := bbase (se 2 (by rfl) ⟨683712, by rfl⟩ : syracuseStep 1823233 = 1367425) (by norm_num)
theorem B2429453 : Blo 1619008 2429453 := bbase (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) (by norm_num)
theorem B2429477 : Blo 1619008 2429477 := bbase (se 4 (by rfl) ⟨227763, by rfl⟩ : syracuseStep 2429477 = 455527) (by norm_num)
theorem B4100645 : Blo 1619008 4100645 := bbase (se 4 (by rfl) ⟨384435, by rfl⟩ : syracuseStep 4100645 = 768871) (by norm_num)
theorem B1823269 : Blo 1619008 1823269 := bbase (se 4 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 1823269 = 341863) (by norm_num)
theorem B1946153 : Blo 1619008 1946153 := bbase (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) (by norm_num)
theorem B2429501 : Blo 1619008 2429501 := bbase (se 3 (by rfl) ⟨455531, by rfl⟩ : syracuseStep 2429501 = 911063) (by norm_num)
theorem B5468741 : Blo 1619008 5468741 := bbase (se 4 (by rfl) ⟨512694, by rfl⟩ : syracuseStep 5468741 = 1025389) (by norm_num)
theorem B1823305 : Blo 1619008 1823305 := bbase (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) (by norm_num)
theorem B2732629 : Blo 1619008 2732629 := bbase (se 8 (by rfl) ⟨16011, by rfl⟩ : syracuseStep 2732629 = 32023) (by norm_num)
theorem B2429525 : Blo 1619008 2429525 := bbase (se 8 (by rfl) ⟨14235, by rfl⟩ : syracuseStep 2429525 = 28471) (by norm_num)
theorem B2429549 : Blo 1619008 2429549 := bbase (se 3 (by rfl) ⟨455540, by rfl⟩ : syracuseStep 2429549 = 911081) (by norm_num)
theorem B1823341 : Blo 1619008 1823341 := bbase (se 3 (by rfl) ⟨341876, by rfl⟩ : syracuseStep 1823341 = 683753) (by norm_num)
theorem B16626293 : Blo 1619008 16626293 := bbase (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) (by norm_num)
theorem B2429573 : Blo 1619008 2429573 := bbase (se 4 (by rfl) ⟨227772, by rfl⟩ : syracuseStep 2429573 = 455545) (by norm_num)
theorem B1823377 : Blo 1619008 1823377 := bbase (se 2 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 1823377 = 1367533) (by norm_num)
theorem B2429597 : Blo 1619008 2429597 := bbase (se 3 (by rfl) ⟨455549, by rfl⟩ : syracuseStep 2429597 = 911099) (by norm_num)
theorem B2732717 : Blo 1619008 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B2429621 : Blo 1619008 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B1823413 : Blo 1619008 1823413 := bbase (se 5 (by rfl) ⟨85472, by rfl⟩ : syracuseStep 1823413 = 170945) (by norm_num)
theorem B3076805 : Blo 1619008 3076805 := bbase (se 4 (by rfl) ⟨288450, by rfl⟩ : syracuseStep 3076805 = 576901) (by norm_num)
theorem B2429645 : Blo 1619008 2429645 := bbase (se 3 (by rfl) ⟨455558, by rfl⟩ : syracuseStep 2429645 = 911117) (by norm_num)
theorem B1823449 : Blo 1619008 1823449 := bbase (se 2 (by rfl) ⟨683793, by rfl⟩ : syracuseStep 1823449 = 1367587) (by norm_num)
theorem B2429669 : Blo 1619008 2429669 := bbase (se 4 (by rfl) ⟨227781, by rfl⟩ : syracuseStep 2429669 = 455563) (by norm_num)
theorem B2429693 : Blo 1619008 2429693 := bbase (se 3 (by rfl) ⟨455567, by rfl⟩ : syracuseStep 2429693 = 911135) (by norm_num)
theorem B1823485 : Blo 1619008 1823485 := bbase (se 3 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 1823485 = 683807) (by norm_num)
theorem B2429717 : Blo 1619008 2429717 := bbase (se 6 (by rfl) ⟨56946, by rfl⟩ : syracuseStep 2429717 = 113893) (by norm_num)
theorem B1823521 : Blo 1619008 1823521 := bbase (se 2 (by rfl) ⟨683820, by rfl⟩ : syracuseStep 1823521 = 1367641) (by norm_num)
theorem B2732845 : Blo 1619008 2732845 := bbase (se 3 (by rfl) ⟨512408, by rfl⟩ : syracuseStep 2732845 = 1024817) (by norm_num)
theorem B2429741 : Blo 1619008 2429741 := bbase (se 3 (by rfl) ⟨455576, by rfl⟩ : syracuseStep 2429741 = 911153) (by norm_num)
theorem B2429765 : Blo 1619008 2429765 := bbase (se 4 (by rfl) ⟨227790, by rfl⟩ : syracuseStep 2429765 = 455581) (by norm_num)
theorem B1823557 : Blo 1619008 1823557 := bbase (se 4 (by rfl) ⟨170958, by rfl⟩ : syracuseStep 1823557 = 341917) (by norm_num)
theorem B7385941 : Blo 1619008 7385941 := bbase (se 9 (by rfl) ⟨21638, by rfl⟩ : syracuseStep 7385941 = 43277) (by norm_num)
theorem B2429789 : Blo 1619008 2429789 := bbase (se 3 (by rfl) ⟨455585, by rfl⟩ : syracuseStep 2429789 = 911171) (by norm_num)
theorem B3076957 : Blo 1619008 3076957 := bbase (se 3 (by rfl) ⟨576929, by rfl⟩ : syracuseStep 3076957 = 1153859) (by norm_num)
theorem B1823593 : Blo 1619008 1823593 := bbase (se 2 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 1823593 = 1367695) (by norm_num)
theorem B14603125 : Blo 1619008 14603125 := bbase (se 5 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 14603125 = 1369043) (by norm_num)
theorem B2429813 : Blo 1619008 2429813 := bbase (se 5 (by rfl) ⟨113897, by rfl⟩ : syracuseStep 2429813 = 227795) (by norm_num)
theorem B4100989 : Blo 1619008 4100989 := bbase (se 3 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 4100989 = 1537871) (by norm_num)
theorem B2732933 : Blo 1619008 2732933 := bbase (se 4 (by rfl) ⟨256212, by rfl⟩ : syracuseStep 2732933 = 512425) (by norm_num)
theorem B2429837 : Blo 1619008 2429837 := bbase (se 3 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 2429837 = 911189) (by norm_num)
theorem B1848205 : Blo 1619008 1848205 := bbase (se 3 (by rfl) ⟨346538, by rfl⟩ : syracuseStep 1848205 = 693077) (by norm_num)
theorem B1823629 : Blo 1619008 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B2077589 : Blo 1619008 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B2429861 : Blo 1619008 2429861 := bbase (se 4 (by rfl) ⟨227799, by rfl⟩ : syracuseStep 2429861 = 455599) (by norm_num)
theorem B2306989 : Blo 1619008 2306989 := bbase (se 3 (by rfl) ⟨432560, by rfl⟩ : syracuseStep 2306989 = 865121) (by norm_num)
theorem B2429885 : Blo 1619008 2429885 := bbase (se 3 (by rfl) ⟨455603, by rfl⟩ : syracuseStep 2429885 = 911207) (by norm_num)
theorem B2429909 : Blo 1619008 2429909 := bbase (se 7 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 2429909 = 56951) (by norm_num)
theorem B2429933 : Blo 1619008 2429933 := bbase (se 3 (by rfl) ⟨455612, by rfl⟩ : syracuseStep 2429933 = 911225) (by norm_num)
theorem B4101101 : Blo 1619008 4101101 := bbase (se 3 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 4101101 = 1537913) (by norm_num)
theorem B5469173 : Blo 1619008 5469173 := bbase (se 5 (by rfl) ⟨256367, by rfl⟩ : syracuseStep 5469173 = 512735) (by norm_num)
theorem B9229301 : Blo 1619008 9229301 := bbase (se 5 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 9229301 = 865247) (by norm_num)
theorem B2733061 : Blo 1619008 2733061 := bbase (se 4 (by rfl) ⟨256224, by rfl⟩ : syracuseStep 2733061 = 512449) (by norm_num)
theorem B2429957 : Blo 1619008 2429957 := bbase (se 4 (by rfl) ⟨227808, by rfl⟩ : syracuseStep 2429957 = 455617) (by norm_num)
theorem B2429981 : Blo 1619008 2429981 := bbase (se 3 (by rfl) ⟨455621, by rfl⟩ : syracuseStep 2429981 = 911243) (by norm_num)
theorem B2430005 : Blo 1619008 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B2077753 : Blo 1619008 2077753 := bbase (se 2 (by rfl) ⟨779157, by rfl⟩ : syracuseStep 2077753 = 1558315) (by norm_num)
theorem B2430029 : Blo 1619008 2430029 := bbase (se 3 (by rfl) ⟨455630, by rfl⟩ : syracuseStep 2430029 = 911261) (by norm_num)
theorem B2733149 : Blo 1619008 2733149 := bbase (se 3 (by rfl) ⟨512465, by rfl⟩ : syracuseStep 2733149 = 1024931) (by norm_num)
theorem B2430053 : Blo 1619008 2430053 := bbase (se 4 (by rfl) ⟨227817, by rfl⟩ : syracuseStep 2430053 = 455635) (by norm_num)
theorem B2430077 : Blo 1619008 2430077 := bbase (se 3 (by rfl) ⟨455639, by rfl⟩ : syracuseStep 2430077 = 911279) (by norm_num)
theorem B3077261 : Blo 1619008 3077261 := bbase (se 3 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 3077261 = 1153973) (by norm_num)
theorem B2430101 : Blo 1619008 2430101 := bbase (se 6 (by rfl) ⟨56955, by rfl⟩ : syracuseStep 2430101 = 113911) (by norm_num)
theorem B8205461 : Blo 1619008 8205461 := bbase (se 6 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 8205461 = 384631) (by norm_num)
theorem B2430125 : Blo 1619008 2430125 := bbase (se 3 (by rfl) ⟨455648, by rfl⟩ : syracuseStep 2430125 = 911297) (by norm_num)
theorem B4101293 : Blo 1619008 4101293 := bbase (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) (by norm_num)
theorem B2430149 : Blo 1619008 2430149 := bbase (se 4 (by rfl) ⟨227826, by rfl⟩ : syracuseStep 2430149 = 455653) (by norm_num)
theorem B2733277 : Blo 1619008 2733277 := bbase (se 3 (by rfl) ⟨512489, by rfl⟩ : syracuseStep 2733277 = 1024979) (by norm_num)
theorem B2430173 : Blo 1619008 2430173 := bbase (se 3 (by rfl) ⟨455657, by rfl⟩ : syracuseStep 2430173 = 911315) (by norm_num)
theorem B2430197 : Blo 1619008 2430197 := bbase (se 5 (by rfl) ⟨113915, by rfl⟩ : syracuseStep 2430197 = 227831) (by norm_num)
theorem B2430221 : Blo 1619008 2430221 := bbase (se 3 (by rfl) ⟨455666, by rfl⟩ : syracuseStep 2430221 = 911333) (by norm_num)
theorem B2430245 : Blo 1619008 2430245 := bbase (se 4 (by rfl) ⟨227835, by rfl⟩ : syracuseStep 2430245 = 455671) (by norm_num)
theorem B2594101 : Blo 1619008 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B2733365 : Blo 1619008 2733365 := bbase (se 5 (by rfl) ⟨128126, by rfl⟩ : syracuseStep 2733365 = 256253) (by norm_num)
theorem B2430269 : Blo 1619008 2430269 := bbase (se 3 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 2430269 = 911351) (by norm_num)
theorem B2430293 : Blo 1619008 2430293 := bbase (se 14 (by rfl) ⟨222, by rfl⟩ : syracuseStep 2430293 = 445) (by norm_num)
theorem B2430317 : Blo 1619008 2430317 := bbase (se 3 (by rfl) ⟨455684, by rfl⟩ : syracuseStep 2430317 = 911369) (by norm_num)
theorem B2430341 : Blo 1619008 2430341 := bbase (se 4 (by rfl) ⟨227844, by rfl⟩ : syracuseStep 2430341 = 455689) (by norm_num)
theorem B2430365 : Blo 1619008 2430365 := bbase (se 3 (by rfl) ⟨455693, by rfl⟩ : syracuseStep 2430365 = 911387) (by norm_num)
theorem B5469605 : Blo 1619008 5469605 := bbase (se 4 (by rfl) ⟨512775, by rfl⟩ : syracuseStep 5469605 = 1025551) (by norm_num)
theorem B2463149 : Blo 1619008 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B2733493 : Blo 1619008 2733493 := bbase (se 5 (by rfl) ⟨128132, by rfl⟩ : syracuseStep 2733493 = 256265) (by norm_num)
theorem B2430389 : Blo 1619008 2430389 := bbase (se 5 (by rfl) ⟨113924, by rfl⟩ : syracuseStep 2430389 = 227849) (by norm_num)
theorem B3642821 : Blo 1619008 3642821 := bbase (se 4 (by rfl) ⟨341514, by rfl⟩ : syracuseStep 3642821 = 683029) (by norm_num)
theorem B2430413 : Blo 1619008 2430413 := bbase (se 3 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 2430413 = 911405) (by norm_num)
theorem B2430437 : Blo 1619008 2430437 := bbase (se 4 (by rfl) ⟨227853, by rfl⟩ : syracuseStep 2430437 = 455707) (by norm_num)
theorem B2430461 : Blo 1619008 2430461 := bbase (se 3 (by rfl) ⟨455711, by rfl⟩ : syracuseStep 2430461 = 911423) (by norm_num)
theorem B1873405 : Blo 1619008 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B4101637 : Blo 1619008 4101637 := bbase (se 4 (by rfl) ⟨384528, by rfl⟩ : syracuseStep 4101637 = 769057) (by norm_num)
theorem B3642893 : Blo 1619008 3642893 := bbase (se 3 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 3642893 = 1366085) (by norm_num)
theorem B2733581 : Blo 1619008 2733581 := bbase (se 3 (by rfl) ⟨512546, by rfl⟩ : syracuseStep 2733581 = 1025093) (by norm_num)
theorem B2430485 : Blo 1619008 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B2078245 : Blo 1619008 2078245 := bbase (se 4 (by rfl) ⟨194835, by rfl⟩ : syracuseStep 2078245 = 389671) (by norm_num)
theorem B2430509 : Blo 1619008 2430509 := bbase (se 3 (by rfl) ⟨455720, by rfl⟩ : syracuseStep 2430509 = 911441) (by norm_num)
theorem B8197685 : Blo 1619008 8197685 := bbase (se 5 (by rfl) ⟨384266, by rfl⟩ : syracuseStep 8197685 = 768533) (by norm_num)
theorem B2430533 : Blo 1619008 2430533 := bbase (se 4 (by rfl) ⟨227862, by rfl⟩ : syracuseStep 2430533 = 455725) (by norm_num)
theorem B3642965 : Blo 1619008 3642965 := bbase (se 8 (by rfl) ⟨21345, by rfl⟩ : syracuseStep 3642965 = 42691) (by norm_num)
theorem B2430557 : Blo 1619008 2430557 := bbase (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) (by norm_num)
theorem B3552869 : Blo 1619008 3552869 := bbase (se 4 (by rfl) ⟨333081, by rfl⟩ : syracuseStep 3552869 = 666163) (by norm_num)
theorem B2430581 : Blo 1619008 2430581 := bbase (se 5 (by rfl) ⟨113933, by rfl⟩ : syracuseStep 2430581 = 227867) (by norm_num)
theorem B4101749 : Blo 1619008 4101749 := bbase (se 5 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 4101749 = 384539) (by norm_num)
theorem B2733709 : Blo 1619008 2733709 := bbase (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) (by norm_num)
theorem B2430605 : Blo 1619008 2430605 := bbase (se 3 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 2430605 = 911477) (by norm_num)
theorem B4159117 : Blo 1619008 4159117 := bbase (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) (by norm_num)
theorem B3643037 : Blo 1619008 3643037 := bbase (se 3 (by rfl) ⟨683069, by rfl⟩ : syracuseStep 3643037 = 1366139) (by norm_num)
theorem B2430629 : Blo 1619008 2430629 := bbase (se 4 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 2430629 = 455743) (by norm_num)
theorem B2430653 : Blo 1619008 2430653 := bbase (se 3 (by rfl) ⟨455747, by rfl⟩ : syracuseStep 2430653 = 911495) (by norm_num)
theorem B2307781 : Blo 1619008 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B2430677 : Blo 1619008 2430677 := bbase (se 7 (by rfl) ⟨28484, by rfl⟩ : syracuseStep 2430677 = 56969) (by norm_num)
theorem B1947349 : Blo 1619008 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B3643109 : Blo 1619008 3643109 := bbase (se 4 (by rfl) ⟨341541, by rfl⟩ : syracuseStep 3643109 = 683083) (by norm_num)
theorem B2733797 : Blo 1619008 2733797 := bbase (se 4 (by rfl) ⟨256293, by rfl⟩ : syracuseStep 2733797 = 512587) (by norm_num)
theorem B2430701 : Blo 1619008 2430701 := bbase (se 3 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 2430701 = 911513) (by norm_num)
theorem B2430725 : Blo 1619008 2430725 := bbase (se 4 (by rfl) ⟨227880, by rfl⟩ : syracuseStep 2430725 = 455761) (by norm_num)
theorem B2430749 : Blo 1619008 2430749 := bbase (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) (by norm_num)
theorem B3643181 : Blo 1619008 3643181 := bbase (se 3 (by rfl) ⟨683096, by rfl⟩ : syracuseStep 3643181 = 1366193) (by norm_num)
theorem B2430773 : Blo 1619008 2430773 := bbase (se 5 (by rfl) ⟨113942, by rfl⟩ : syracuseStep 2430773 = 227885) (by norm_num)
theorem B4101941 : Blo 1619008 4101941 := bbase (se 5 (by rfl) ⟨192278, by rfl⟩ : syracuseStep 4101941 = 384557) (by norm_num)
theorem B2430797 : Blo 1619008 2430797 := bbase (se 3 (by rfl) ⟨455774, by rfl⟩ : syracuseStep 2430797 = 911549) (by norm_num)
theorem B5470037 : Blo 1619008 5470037 := bbase (se 9 (by rfl) ⟨16025, by rfl⟩ : syracuseStep 5470037 = 32051) (by norm_num)
theorem B2733925 : Blo 1619008 2733925 := bbase (se 4 (by rfl) ⟨256305, by rfl⟩ : syracuseStep 2733925 = 512611) (by norm_num)
theorem B2430821 : Blo 1619008 2430821 := bbase (se 4 (by rfl) ⟨227889, by rfl⟩ : syracuseStep 2430821 = 455779) (by norm_num)
theorem B3643253 : Blo 1619008 3643253 := bbase (se 5 (by rfl) ⟨170777, by rfl⟩ : syracuseStep 3643253 = 341555) (by norm_num)
theorem B2430845 : Blo 1619008 2430845 := bbase (se 3 (by rfl) ⟨455783, by rfl⟩ : syracuseStep 2430845 = 911567) (by norm_num)
theorem B2430869 : Blo 1619008 2430869 := bbase (se 6 (by rfl) ⟨56973, by rfl⟩ : syracuseStep 2430869 = 113947) (by norm_num)
theorem B2463653 : Blo 1619008 2463653 := bbase (se 4 (by rfl) ⟨230967, by rfl⟩ : syracuseStep 2463653 = 461935) (by norm_num)
theorem B2430893 : Blo 1619008 2430893 := bbase (se 3 (by rfl) ⟨455792, by rfl⟩ : syracuseStep 2430893 = 911585) (by norm_num)
theorem B3643325 : Blo 1619008 3643325 := bbase (se 3 (by rfl) ⟨683123, by rfl⟩ : syracuseStep 3643325 = 1366247) (by norm_num)
theorem B2734013 : Blo 1619008 2734013 := bbase (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) (by norm_num)
theorem B2430917 : Blo 1619008 2430917 := bbase (se 4 (by rfl) ⟨227898, by rfl⟩ : syracuseStep 2430917 = 455797) (by norm_num)
theorem B2594773 : Blo 1619008 2594773 := bbase (se 7 (by rfl) ⟨30407, by rfl⟩ : syracuseStep 2594773 = 60815) (by norm_num)
theorem B2430941 : Blo 1619008 2430941 := bbase (se 3 (by rfl) ⟨455801, by rfl⟩ : syracuseStep 2430941 = 911603) (by norm_num)
theorem B2463733 : Blo 1619008 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B2430965 : Blo 1619008 2430965 := bbase (se 5 (by rfl) ⟨113951, by rfl⟩ : syracuseStep 2430965 = 227903) (by norm_num)
theorem B3643397 : Blo 1619008 3643397 := bbase (se 4 (by rfl) ⟨341568, by rfl⟩ : syracuseStep 3643397 = 683137) (by norm_num)
theorem B2430989 : Blo 1619008 2430989 := bbase (se 3 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 2430989 = 911621) (by norm_num)
theorem B2431013 : Blo 1619008 2431013 := bbase (se 4 (by rfl) ⟨227907, by rfl⟩ : syracuseStep 2431013 = 455815) (by norm_num)
theorem B2734141 : Blo 1619008 2734141 := bbase (se 3 (by rfl) ⟨512651, by rfl⟩ : syracuseStep 2734141 = 1025303) (by norm_num)
theorem B2431037 : Blo 1619008 2431037 := bbase (se 3 (by rfl) ⟨455819, by rfl⟩ : syracuseStep 2431037 = 911639) (by norm_num)
theorem B3643469 : Blo 1619008 3643469 := bbase (se 3 (by rfl) ⟨683150, by rfl⟩ : syracuseStep 3643469 = 1366301) (by norm_num)
theorem B2431061 : Blo 1619008 2431061 := bbase (se 8 (by rfl) ⟨14244, by rfl⟩ : syracuseStep 2431061 = 28489) (by norm_num)
theorem B2431085 : Blo 1619008 2431085 := bbase (se 3 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 2431085 = 911657) (by norm_num)
theorem B2431109 : Blo 1619008 2431109 := bbase (se 4 (by rfl) ⟨227916, by rfl⟩ : syracuseStep 2431109 = 455833) (by norm_num)
theorem B4102285 : Blo 1619008 4102285 := bbase (se 3 (by rfl) ⟨769178, by rfl⟩ : syracuseStep 4102285 = 1538357) (by norm_num)
theorem B3643541 : Blo 1619008 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B2734229 : Blo 1619008 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B2431133 : Blo 1619008 2431133 := bbase (se 3 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 2431133 = 911675) (by norm_num)
theorem B2431157 : Blo 1619008 2431157 := bbase (se 5 (by rfl) ⟨113960, by rfl⟩ : syracuseStep 2431157 = 227921) (by norm_num)
theorem B2431181 : Blo 1619008 2431181 := bbase (se 3 (by rfl) ⟨455846, by rfl⟩ : syracuseStep 2431181 = 911693) (by norm_num)
theorem B3643613 : Blo 1619008 3643613 := bbase (se 3 (by rfl) ⟨683177, by rfl⟩ : syracuseStep 3643613 = 1366355) (by norm_num)
theorem B2431205 : Blo 1619008 2431205 := bbase (se 4 (by rfl) ⟨227925, by rfl⟩ : syracuseStep 2431205 = 455851) (by norm_num)
theorem B10385653 : Blo 1619008 10385653 := bbase (se 5 (by rfl) ⟨486827, by rfl⟩ : syracuseStep 10385653 = 973655) (by norm_num)
theorem B4102397 : Blo 1619008 4102397 := bbase (se 3 (by rfl) ⟨769199, by rfl⟩ : syracuseStep 4102397 = 1538399) (by norm_num)
theorem B2431229 : Blo 1619008 2431229 := bbase (se 3 (by rfl) ⟨455855, by rfl⟩ : syracuseStep 2431229 = 911711) (by norm_num)
theorem B5470469 : Blo 1619008 5470469 := bbase (se 4 (by rfl) ⟨512856, by rfl⟩ : syracuseStep 5470469 = 1025713) (by norm_num)
theorem B2734357 : Blo 1619008 2734357 := bbase (se 6 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 2734357 = 128173) (by norm_num)
theorem B2431253 : Blo 1619008 2431253 := bbase (se 6 (by rfl) ⟨56982, by rfl⟩ : syracuseStep 2431253 = 113965) (by norm_num)
theorem B3643685 : Blo 1619008 3643685 := bbase (se 4 (by rfl) ⟨341595, by rfl⟩ : syracuseStep 3643685 = 683191) (by norm_num)
theorem B6150437 : Blo 1619008 6150437 := bbase (se 4 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 6150437 = 1153207) (by norm_num)
theorem B2431277 : Blo 1619008 2431277 := bbase (se 3 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 2431277 = 911729) (by norm_num)
theorem B2431301 : Blo 1619008 2431301 := bbase (se 4 (by rfl) ⟨227934, by rfl⟩ : syracuseStep 2431301 = 455869) (by norm_num)
theorem B10377557 : Blo 1619008 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B2496853 : Blo 1619008 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B2431325 : Blo 1619008 2431325 := bbase (se 3 (by rfl) ⟨455873, by rfl⟩ : syracuseStep 2431325 = 911747) (by norm_num)
theorem B3643757 : Blo 1619008 3643757 := bbase (se 3 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 3643757 = 1366409) (by norm_num)
theorem B2734445 : Blo 1619008 2734445 := bbase (se 3 (by rfl) ⟨512708, by rfl⟩ : syracuseStep 2734445 = 1025417) (by norm_num)
theorem B2431349 : Blo 1619008 2431349 := bbase (se 5 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 2431349 = 227939) (by norm_num)
theorem B2431373 : Blo 1619008 2431373 := bbase (se 3 (by rfl) ⟨455882, by rfl⟩ : syracuseStep 2431373 = 911765) (by norm_num)
theorem B2431397 : Blo 1619008 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B3643829 : Blo 1619008 3643829 := bbase (se 5 (by rfl) ⟨170804, by rfl⟩ : syracuseStep 3643829 = 341609) (by norm_num)
theorem B4102589 : Blo 1619008 4102589 := bbase (se 3 (by rfl) ⟨769235, by rfl⟩ : syracuseStep 4102589 = 1538471) (by norm_num)
theorem B2431421 : Blo 1619008 2431421 := bbase (se 3 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 2431421 = 911783) (by norm_num)
theorem B2431445 : Blo 1619008 2431445 := bbase (se 7 (by rfl) ⟨28493, by rfl⟩ : syracuseStep 2431445 = 56987) (by norm_num)
theorem B2734573 : Blo 1619008 2734573 := bbase (se 3 (by rfl) ⟨512732, by rfl⟩ : syracuseStep 2734573 = 1025465) (by norm_num)
theorem B2431469 : Blo 1619008 2431469 := bbase (se 3 (by rfl) ⟨455900, by rfl⟩ : syracuseStep 2431469 = 911801) (by norm_num)
theorem B3643901 : Blo 1619008 3643901 := bbase (se 3 (by rfl) ⟨683231, by rfl⟩ : syracuseStep 3643901 = 1366463) (by norm_num)
theorem B2431493 : Blo 1619008 2431493 := bbase (se 4 (by rfl) ⟨227952, by rfl⟩ : syracuseStep 2431493 = 455905) (by norm_num)
theorem B5839381 : Blo 1619008 5839381 := bbase (se 6 (by rfl) ⟨136860, by rfl⟩ : syracuseStep 5839381 = 273721) (by norm_num)
theorem B3643973 : Blo 1619008 3643973 := bbase (se 4 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 3643973 = 683245) (by norm_num)
theorem B6150725 : Blo 1619008 6150725 := bbase (se 4 (by rfl) ⟨576630, by rfl⟩ : syracuseStep 6150725 = 1153261) (by norm_num)
theorem B2734661 : Blo 1619008 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B2079313 : Blo 1619008 2079313 := bbase (se 2 (by rfl) ⟨779742, by rfl⟩ : syracuseStep 2079313 = 1559485) (by norm_num)
theorem B5544533 : Blo 1619008 5544533 := bbase (se 8 (by rfl) ⟨32487, by rfl⟩ : syracuseStep 5544533 = 64975) (by norm_num)
theorem B3283573 : Blo 1619008 3283573 := bbase (se 5 (by rfl) ⟨153917, by rfl⟩ : syracuseStep 3283573 = 307835) (by norm_num)
theorem B3644045 : Blo 1619008 3644045 := bbase (se 3 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 3644045 = 1366517) (by norm_num)
theorem B5470901 : Blo 1619008 5470901 := bbase (se 5 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 5470901 = 512897) (by norm_num)
theorem B2734789 : Blo 1619008 2734789 := bbase (se 4 (by rfl) ⟨256386, by rfl⟩ : syracuseStep 2734789 = 512773) (by norm_num)
theorem B3644117 : Blo 1619008 3644117 := bbase (se 7 (by rfl) ⟨42704, by rfl⟩ : syracuseStep 3644117 = 85409) (by norm_num)
theorem B4610789 : Blo 1619008 4610789 := bbase (se 4 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 4610789 = 864523) (by norm_num)
theorem B4102933 : Blo 1619008 4102933 := bbase (se 6 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 4102933 = 192325) (by norm_num)
theorem B3644189 : Blo 1619008 3644189 := bbase (se 3 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 3644189 = 1366571) (by norm_num)
theorem B2734877 : Blo 1619008 2734877 := bbase (se 3 (by rfl) ⟨512789, by rfl⟩ : syracuseStep 2734877 = 1025579) (by norm_num)
theorem B8198981 : Blo 1619008 8198981 := bbase (se 4 (by rfl) ⟨768654, by rfl⟩ : syracuseStep 8198981 = 1537309) (by norm_num)
theorem B3644261 : Blo 1619008 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B4103045 : Blo 1619008 4103045 := bbase (se 4 (by rfl) ⟨384660, by rfl⟩ : syracuseStep 4103045 = 769321) (by norm_num)
theorem B2735005 : Blo 1619008 2735005 := bbase (se 3 (by rfl) ⟨512813, by rfl⟩ : syracuseStep 2735005 = 1025627) (by norm_num)
theorem B7781285 : Blo 1619008 7781285 := bbase (se 4 (by rfl) ⟨729495, by rfl⟩ : syracuseStep 7781285 = 1458991) (by norm_num)
theorem B3644333 : Blo 1619008 3644333 := bbase (se 3 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 3644333 = 1366625) (by norm_num)
theorem B2595773 : Blo 1619008 2595773 := bbase (se 3 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 2595773 = 973415) (by norm_num)
theorem B3644405 : Blo 1619008 3644405 := bbase (se 5 (by rfl) ⟨170831, by rfl⟩ : syracuseStep 3644405 = 341663) (by norm_num)
theorem B2735093 : Blo 1619008 2735093 := bbase (se 5 (by rfl) ⟨128207, by rfl⟩ : syracuseStep 2735093 = 256415) (by norm_num)
theorem B3644477 : Blo 1619008 3644477 := bbase (se 3 (by rfl) ⟨683339, by rfl⟩ : syracuseStep 3644477 = 1366679) (by norm_num)
theorem B3284077 : Blo 1619008 3284077 := bbase (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) (by norm_num)
theorem B2735221 : Blo 1619008 2735221 := bbase (se 5 (by rfl) ⟨128213, by rfl⟩ : syracuseStep 2735221 = 256427) (by norm_num)
theorem B3644549 : Blo 1619008 3644549 := bbase (se 4 (by rfl) ⟨341676, by rfl⟩ : syracuseStep 3644549 = 683353) (by norm_num)
theorem B9231509 : Blo 1619008 9231509 := bbase (se 6 (by rfl) ⟨216363, by rfl⟩ : syracuseStep 9231509 = 432727) (by norm_num)
theorem B3644621 : Blo 1619008 3644621 := bbase (se 3 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 3644621 = 1366733) (by norm_num)
theorem B2735309 : Blo 1619008 2735309 := bbase (se 3 (by rfl) ⟨512870, by rfl⟩ : syracuseStep 2735309 = 1025741) (by norm_num)
theorem B6921445 : Blo 1619008 6921445 := bbase (se 4 (by rfl) ⟨648885, by rfl⟩ : syracuseStep 6921445 = 1297771) (by norm_num)
theorem B1973489 : Blo 1619008 1973489 := bbase (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) (by norm_num)
theorem B7888117 : Blo 1619008 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B2628877 : Blo 1619008 2628877 := bbase (se 3 (by rfl) ⟨492914, by rfl⟩ : syracuseStep 2628877 = 985829) (by norm_num)
theorem B3644693 : Blo 1619008 3644693 := bbase (se 6 (by rfl) ⟨85422, by rfl⟩ : syracuseStep 3644693 = 170845) (by norm_num)
theorem B5192981 : Blo 1619008 5192981 := bbase (se 6 (by rfl) ⟨121710, by rfl⟩ : syracuseStep 5192981 = 243421) (by norm_num)
theorem B2735437 : Blo 1619008 2735437 := bbase (se 3 (by rfl) ⟨512894, by rfl⟩ : syracuseStep 2735437 = 1025789) (by norm_num)
theorem B3644765 : Blo 1619008 3644765 := bbase (se 3 (by rfl) ⟨683393, by rfl⟩ : syracuseStep 3644765 = 1366787) (by norm_num)
theorem B3644837 : Blo 1619008 3644837 := bbase (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) (by norm_num)
theorem B3644909 : Blo 1619008 3644909 := bbase (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) (by norm_num)
theorem B3743237 : Blo 1619008 3743237 := bbase (se 4 (by rfl) ⟨350928, by rfl⟩ : syracuseStep 3743237 = 701857) (by norm_num)
theorem B4562453 : Blo 1619008 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B3644981 : Blo 1619008 3644981 := bbase (se 5 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 3644981 = 341717) (by norm_num)
theorem B3645053 : Blo 1619008 3645053 := bbase (se 3 (by rfl) ⟨683447, by rfl⟩ : syracuseStep 3645053 = 1366895) (by norm_num)
theorem B1801873 : Blo 1619008 1801873 := bbase (se 2 (by rfl) ⟨675702, by rfl⟩ : syracuseStep 1801873 = 1351405) (by norm_num)
theorem B8756885 : Blo 1619008 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B1973953 : Blo 1619008 1973953 := bbase (se 2 (by rfl) ⟨740232, by rfl⟩ : syracuseStep 1973953 = 1480465) (by norm_num)
theorem B3645125 : Blo 1619008 3645125 := bbase (se 4 (by rfl) ⟨341730, by rfl⟩ : syracuseStep 3645125 = 683461) (by norm_num)
theorem B6151909 : Blo 1619008 6151909 := bbase (se 4 (by rfl) ⟨576741, by rfl⟩ : syracuseStep 6151909 = 1153483) (by norm_num)
theorem B6233861 : Blo 1619008 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B3645197 : Blo 1619008 3645197 := bbase (se 3 (by rfl) ⟨683474, by rfl⟩ : syracuseStep 3645197 = 1366949) (by norm_num)
theorem B2629397 : Blo 1619008 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B5840693 : Blo 1619008 5840693 := bbase (se 5 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 5840693 = 547565) (by norm_num)
theorem B3555133 : Blo 1619008 3555133 := bbase (se 3 (by rfl) ⟨666587, by rfl⟩ : syracuseStep 3555133 = 1333175) (by norm_num)
theorem B3645269 : Blo 1619008 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B4611973 : Blo 1619008 4611973 := bbase (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) (by norm_num)
theorem B3645341 : Blo 1619008 3645341 := bbase (se 3 (by rfl) ⟨683501, by rfl⟩ : syracuseStep 3645341 = 1367003) (by norm_num)
theorem B14770133 : Blo 1619008 14770133 := bbase (se 7 (by rfl) ⟨173087, by rfl⟩ : syracuseStep 14770133 = 346175) (by norm_num)
theorem B26271701 : Blo 1619008 26271701 := bbase (se 7 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 26271701 = 615743) (by norm_num)
theorem B3645413 : Blo 1619008 3645413 := bbase (se 4 (by rfl) ⟨341757, by rfl⟩ : syracuseStep 3645413 = 683515) (by norm_num)
theorem B4612099 : Blo 1619008 4612099 := bstep (se 1 (by rfl) ⟨3459074, by rfl⟩ : syracuseStep 4612099 = 6918149) B6918149
theorem B3645521 : Blo 1619008 3645521 := bstep (se 2 (by rfl) ⟨1367070, by rfl⟩ : syracuseStep 3645521 = 2734141) B2734141
theorem B3645539 : Blo 1619008 3645539 := bstep (se 1 (by rfl) ⟨2734154, by rfl⟩ : syracuseStep 3645539 = 5468309) B5468309
theorem B5464205 : Blo 1619008 5464205 := bstep (se 3 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 5464205 = 2049077) B2049077
theorem B5464259 : Blo 1619008 5464259 := bstep (se 1 (by rfl) ⟨4098194, by rfl⟩ : syracuseStep 5464259 = 8196389) B8196389
theorem B7389539 : Blo 1619008 7389539 := bstep (se 1 (by rfl) ⟨5542154, by rfl⟩ : syracuseStep 7389539 = 11084309) B11084309
theorem B3645809 : Blo 1619008 3645809 := bstep (se 2 (by rfl) ⟨1367178, by rfl⟩ : syracuseStep 3645809 = 2734357) B2734357
theorem B3645827 : Blo 1619008 3645827 := bstep (se 1 (by rfl) ⟨2734370, by rfl⟩ : syracuseStep 3645827 = 5468741) B5468741
theorem B11084195 : Blo 1619008 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B5464529 : Blo 1619008 5464529 := bstep (se 2 (by rfl) ⟨2049198, by rfl⟩ : syracuseStep 5464529 = 4098397) B4098397
theorem B9224675 : Blo 1619008 9224675 := bstep (se 1 (by rfl) ⟨6918506, by rfl⟩ : syracuseStep 9224675 = 13837013) B13837013
theorem B4612589 : Blo 1619008 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B3646097 : Blo 1619008 3646097 := bstep (se 2 (by rfl) ⟨1367286, by rfl⟩ : syracuseStep 3646097 = 2734573) B2734573
theorem B3646115 : Blo 1619008 3646115 := bstep (se 1 (by rfl) ⟨2734586, by rfl⟩ : syracuseStep 3646115 = 5469173) B5469173
theorem B6152867 : Blo 1619008 6152867 := bstep (se 1 (by rfl) ⟨4614650, by rfl⟩ : syracuseStep 6152867 = 9229301) B9229301
theorem B6152881 : Blo 1619008 6152881 := bstep (se 2 (by rfl) ⟨2307330, by rfl⟩ : syracuseStep 6152881 = 4614661) B4614661
theorem B3646385 : Blo 1619008 3646385 := bstep (se 2 (by rfl) ⟨1367394, by rfl⟩ : syracuseStep 3646385 = 2734789) B2734789
theorem B3646403 : Blo 1619008 3646403 := bstep (se 1 (by rfl) ⟨2734802, by rfl⟩ : syracuseStep 3646403 = 5469605) B5469605
theorem B5465069 : Blo 1619008 5465069 := bstep (se 3 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 5465069 = 2049401) B2049401
theorem B10527749 : Blo 1619008 10527749 := bstep (se 4 (by rfl) ⟨986976, by rfl⟩ : syracuseStep 10527749 = 1973953) B1973953
theorem B5465123 : Blo 1619008 5465123 := bstep (se 1 (by rfl) ⟨4098842, by rfl⟩ : syracuseStep 5465123 = 8197685) B8197685
theorem B9847921 : Blo 1619008 9847921 := bstep (se 2 (by rfl) ⟨3692970, by rfl⟩ : syracuseStep 9847921 = 7385941) B7385941
theorem B27665549 : Blo 1619008 27665549 := bstep (se 3 (by rfl) ⟨5187290, by rfl⟩ : syracuseStep 27665549 = 10374581) B10374581
theorem B3998897 : Blo 1619008 3998897 := bstep (se 2 (by rfl) ⟨1499586, by rfl⟩ : syracuseStep 3998897 = 2999173) B2999173
theorem B3695825 : Blo 1619008 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B3646673 : Blo 1619008 3646673 := bstep (se 2 (by rfl) ⟨1367502, by rfl⟩ : syracuseStep 3646673 = 2735005) B2735005
theorem B3646691 : Blo 1619008 3646691 := bstep (se 1 (by rfl) ⟨2735018, by rfl⟩ : syracuseStep 3646691 = 5470037) B5470037
theorem B75842837 : Blo 1619008 75842837 := bstep (se 6 (by rfl) ⟨1777566, by rfl⟩ : syracuseStep 75842837 = 3555133) B3555133
theorem B5465393 : Blo 1619008 5465393 := bstep (se 2 (by rfl) ⟨2049522, by rfl⟩ : syracuseStep 5465393 = 4099045) B4099045
theorem B17524021 : Blo 1619008 17524021 := bstep (se 5 (by rfl) ⟨821438, by rfl⟩ : syracuseStep 17524021 = 1642877) B1642877
theorem B12166541 : Blo 1619008 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B2770337 : Blo 1619008 2770337 := bstep (se 2 (by rfl) ⟨1038876, by rfl⟩ : syracuseStep 2770337 = 2077753) B2077753
theorem B2917795 : Blo 1619008 2917795 := bstep (se 1 (by rfl) ⟨2188346, by rfl⟩ : syracuseStep 2917795 = 4376693) B4376693
theorem B3458467 : Blo 1619008 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B9225677 : Blo 1619008 9225677 := bstep (se 3 (by rfl) ⟨1729814, by rfl⟩ : syracuseStep 9225677 = 3459629) B3459629
theorem B3646961 : Blo 1619008 3646961 := bstep (se 2 (by rfl) ⟨1367610, by rfl⟩ : syracuseStep 3646961 = 2735221) B2735221
theorem B3646979 : Blo 1619008 3646979 := bstep (se 1 (by rfl) ⟨2735234, by rfl⟩ : syracuseStep 3646979 = 5470469) B5470469
theorem B2049619 : Blo 1619008 2049619 := bstep (se 1 (by rfl) ⟨1537214, by rfl⟩ : syracuseStep 2049619 = 3074429) B3074429
theorem B4613773 : Blo 1619008 4613773 := bstep (se 3 (by rfl) ⟨865082, by rfl⟩ : syracuseStep 4613773 = 1730165) B1730165
theorem B2049715 : Blo 1619008 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B3696355 : Blo 1619008 3696355 := bstep (se 1 (by rfl) ⟨2772266, by rfl⟩ : syracuseStep 3696355 = 5544533) B5544533
theorem B3458801 : Blo 1619008 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B3647249 : Blo 1619008 3647249 := bstep (se 2 (by rfl) ⟨1367718, by rfl⟩ : syracuseStep 3647249 = 2735437) B2735437
theorem B3647267 : Blo 1619008 3647267 := bstep (se 1 (by rfl) ⟨2735450, by rfl⟩ : syracuseStep 3647267 = 5470901) B5470901
theorem B3073859 : Blo 1619008 3073859 := bstep (se 1 (by rfl) ⟨2305394, by rfl⟩ : syracuseStep 3073859 = 4610789) B4610789
theorem B5465933 : Blo 1619008 5465933 := bstep (se 3 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 5465933 = 2049725) B2049725
theorem B5465987 : Blo 1619008 5465987 := bstep (se 1 (by rfl) ⟨4099490, by rfl⟩ : syracuseStep 5465987 = 8198981) B8198981
theorem B5187523 : Blo 1619008 5187523 := bstep (se 1 (by rfl) ⟨3890642, by rfl⟩ : syracuseStep 5187523 = 7781285) B7781285
theorem B11241413 : Blo 1619008 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B2918371 : Blo 1619008 2918371 := bstep (se 1 (by rfl) ⟨2188778, by rfl⟩ : syracuseStep 2918371 = 4377557) B4377557
theorem B2770993 : Blo 1619008 2770993 := bstep (se 2 (by rfl) ⟨1039122, by rfl⟩ : syracuseStep 2770993 = 2078245) B2078245
theorem B5539907 : Blo 1619008 5539907 := bstep (se 1 (by rfl) ⟨4154930, by rfl⟩ : syracuseStep 5539907 = 8309861) B8309861
theorem B6154339 : Blo 1619008 6154339 := bstep (se 1 (by rfl) ⟨4615754, by rfl⟩ : syracuseStep 6154339 = 9231509) B9231509
theorem B5466257 : Blo 1619008 5466257 := bstep (se 2 (by rfl) ⟨2049846, by rfl⟩ : syracuseStep 5466257 = 4099693) B4099693
theorem B2050211 : Blo 1619008 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B2402497 : Blo 1619008 2402497 := bstep (se 2 (by rfl) ⟨900936, by rfl⟩ : syracuseStep 2402497 = 1801873) B1801873
theorem B10381553 : Blo 1619008 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B2918659 : Blo 1619008 2918659 := bstep (se 1 (by rfl) ⟨2188994, by rfl⟩ : syracuseStep 2918659 = 4377989) B4377989
theorem B8202545 : Blo 1619008 8202545 := bstep (se 2 (by rfl) ⟨3075954, by rfl⟩ : syracuseStep 8202545 = 6151909) B6151909
theorem B4376909 : Blo 1619008 4376909 := bstep (se 3 (by rfl) ⟨820670, by rfl⟩ : syracuseStep 4376909 = 1641341) B1641341
theorem B5540237 : Blo 1619008 5540237 := bstep (se 3 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 5540237 = 2077589) B2077589
theorem B5835185 : Blo 1619008 5835185 := bstep (se 2 (by rfl) ⟨2188194, by rfl⟩ : syracuseStep 5835185 = 4376389) B4376389
theorem B13838789 : Blo 1619008 13838789 := bstep (se 4 (by rfl) ⟨1297386, by rfl⟩ : syracuseStep 13838789 = 2594773) B2594773
theorem B4377059 : Blo 1619008 4377059 := bstep (se 1 (by rfl) ⟨3282794, by rfl⟩ : syracuseStep 4377059 = 6565589) B6565589
theorem B4155907 : Blo 1619008 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B3893795 : Blo 1619008 3893795 := bstep (se 1 (by rfl) ⟨2920346, by rfl⟩ : syracuseStep 3893795 = 5840693) B5840693
theorem B2771555 : Blo 1619008 2771555 := bstep (se 1 (by rfl) ⟨2078666, by rfl⟩ : syracuseStep 2771555 = 4157333) B4157333
theorem B5466797 : Blo 1619008 5466797 := bstep (se 3 (by rfl) ⟨1025024, by rfl⟩ : syracuseStep 5466797 = 2050049) B2050049
theorem B4614833 : Blo 1619008 4614833 := bstep (se 2 (by rfl) ⟨1730562, by rfl⟩ : syracuseStep 4614833 = 3461125) B3461125
theorem B3074755 : Blo 1619008 3074755 := bstep (se 1 (by rfl) ⟨2306066, by rfl⟩ : syracuseStep 3074755 = 4612133) B4612133
theorem B5466851 : Blo 1619008 5466851 := bstep (se 1 (by rfl) ⟨4100138, by rfl⟩ : syracuseStep 5466851 = 8200277) B8200277
theorem B4098833 : Blo 1619008 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B2190097 : Blo 1619008 2190097 := bstep (se 2 (by rfl) ⟨821286, by rfl⟩ : syracuseStep 2190097 = 1642573) B1642573
theorem B4098883 : Blo 1619008 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B1821523 : Blo 1619008 1821523 := bstep (se 1 (by rfl) ⟨1366142, by rfl⟩ : syracuseStep 1821523 = 2732285) B2732285
theorem B3074915 : Blo 1619008 3074915 := bstep (se 1 (by rfl) ⟨2306186, by rfl⟩ : syracuseStep 3074915 = 4612373) B4612373
theorem B2050915 : Blo 1619008 2050915 := bstep (se 1 (by rfl) ⟨1538186, by rfl⟩ : syracuseStep 2050915 = 3076373) B3076373
theorem B3459971 : Blo 1619008 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B7392163 : Blo 1619008 7392163 := bstep (se 1 (by rfl) ⟨5544122, by rfl⟩ : syracuseStep 7392163 = 11088245) B11088245
theorem B4500397 : Blo 1619008 4500397 := bstep (se 3 (by rfl) ⟨843824, by rfl⟩ : syracuseStep 4500397 = 1687649) B1687649
theorem B2051011 : Blo 1619008 2051011 := bstep (se 1 (by rfl) ⟨1538258, by rfl⟩ : syracuseStep 2051011 = 3076517) B3076517
theorem B4099025 : Blo 1619008 4099025 := bstep (se 2 (by rfl) ⟨1537134, by rfl⟩ : syracuseStep 4099025 = 3074269) B3074269
theorem B1821667 : Blo 1619008 1821667 := bstep (se 1 (by rfl) ⟨1366250, by rfl⟩ : syracuseStep 1821667 = 2732501) B2732501
theorem B5467121 : Blo 1619008 5467121 := bstep (se 2 (by rfl) ⟨2050170, by rfl⟩ : syracuseStep 5467121 = 4100341) B4100341
theorem B13847537 : Blo 1619008 13847537 := bstep (se 2 (by rfl) ⟨5192826, by rfl⟩ : syracuseStep 13847537 = 10385653) B10385653
theorem B3329137 : Blo 1619008 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B1821811 : Blo 1619008 1821811 := bstep (se 1 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 1821811 = 2732717) B2732717
theorem B2305201 : Blo 1619008 2305201 := bstep (se 2 (by rfl) ⟨864450, by rfl⟩ : syracuseStep 2305201 = 1728901) B1728901
theorem B1821955 : Blo 1619008 1821955 := bstep (se 1 (by rfl) ⟨1366466, by rfl⟩ : syracuseStep 1821955 = 2732933) B2732933
theorem B4615505 : Blo 1619008 4615505 := bstep (se 2 (by rfl) ⟨1730814, by rfl⟩ : syracuseStep 4615505 = 3461629) B3461629
theorem B7785841 : Blo 1619008 7785841 := bstep (se 2 (by rfl) ⟨2919690, by rfl⟩ : syracuseStep 7785841 = 5839381) B5839381
theorem B1822099 : Blo 1619008 1822099 := bstep (se 1 (by rfl) ⟨1366574, by rfl⟩ : syracuseStep 1822099 = 2733149) B2733149
theorem B2051507 : Blo 1619008 2051507 := bstep (se 1 (by rfl) ⟨1538630, by rfl⟩ : syracuseStep 2051507 = 3077261) B3077261
theorem B4378097 : Blo 1619008 4378097 := bstep (se 2 (by rfl) ⟨1641786, by rfl⟩ : syracuseStep 4378097 = 3283573) B3283573
theorem B5467661 : Blo 1619008 5467661 := bstep (se 3 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 5467661 = 2050373) B2050373
theorem B4926989 : Blo 1619008 4926989 := bstep (se 3 (by rfl) ⟨923810, by rfl⟩ : syracuseStep 4926989 = 1847621) B1847621
theorem B1822243 : Blo 1619008 1822243 := bstep (se 1 (by rfl) ⟨1366682, by rfl⟩ : syracuseStep 1822243 = 2733365) B2733365
theorem B85298741 : Blo 1619008 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B5467715 : Blo 1619008 5467715 := bstep (se 1 (by rfl) ⟨4100786, by rfl⟩ : syracuseStep 5467715 = 8201573) B8201573
theorem B4157027 : Blo 1619008 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B2428529 : Blo 1619008 2428529 := bstep (se 2 (by rfl) ⟨910698, by rfl⟩ : syracuseStep 2428529 = 1821397) B1821397
theorem B2428547 : Blo 1619008 2428547 := bstep (se 1 (by rfl) ⟨1821410, by rfl⟩ : syracuseStep 2428547 = 3642821) B3642821
theorem B2428577 : Blo 1619008 2428577 := bstep (se 2 (by rfl) ⟨910716, by rfl⟩ : syracuseStep 2428577 = 1821433) B1821433
theorem B2428595 : Blo 1619008 2428595 := bstep (se 1 (by rfl) ⟨1821446, by rfl⟩ : syracuseStep 2428595 = 3642893) B3642893
theorem B1822387 : Blo 1619008 1822387 := bstep (se 1 (by rfl) ⟨1366790, by rfl⟩ : syracuseStep 1822387 = 2733581) B2733581
theorem B2428625 : Blo 1619008 2428625 := bstep (se 2 (by rfl) ⟨910734, by rfl⟩ : syracuseStep 2428625 = 1821469) B1821469
theorem B2428643 : Blo 1619008 2428643 := bstep (se 1 (by rfl) ⟨1821482, by rfl⟩ : syracuseStep 2428643 = 3642965) B3642965
theorem B8204003 : Blo 1619008 8204003 := bstep (se 1 (by rfl) ⟨6153002, by rfl⟩ : syracuseStep 8204003 = 12306005) B12306005
theorem B2428673 : Blo 1619008 2428673 := bstep (se 2 (by rfl) ⟨910752, by rfl⟩ : syracuseStep 2428673 = 1821505) B1821505
theorem B2305793 : Blo 1619008 2305793 := bstep (se 2 (by rfl) ⟨864672, by rfl⟩ : syracuseStep 2305793 = 1729345) B1729345
theorem B2428691 : Blo 1619008 2428691 := bstep (se 1 (by rfl) ⟨1821518, by rfl⟩ : syracuseStep 2428691 = 3643037) B3643037
theorem B2428721 : Blo 1619008 2428721 := bstep (se 2 (by rfl) ⟨910770, by rfl⟩ : syracuseStep 2428721 = 1821541) B1821541
theorem B2428739 : Blo 1619008 2428739 := bstep (se 1 (by rfl) ⟨1821554, by rfl⟩ : syracuseStep 2428739 = 3643109) B3643109
theorem B1822531 : Blo 1619008 1822531 := bstep (se 1 (by rfl) ⟨1366898, by rfl⟩ : syracuseStep 1822531 = 2733797) B2733797
theorem B5467985 : Blo 1619008 5467985 := bstep (se 2 (by rfl) ⟨2050494, by rfl⟩ : syracuseStep 5467985 = 4100989) B4100989
theorem B2428769 : Blo 1619008 2428769 := bstep (se 2 (by rfl) ⟨910788, by rfl⟩ : syracuseStep 2428769 = 1821577) B1821577
theorem B2428787 : Blo 1619008 2428787 := bstep (se 1 (by rfl) ⟨1821590, by rfl⟩ : syracuseStep 2428787 = 3643181) B3643181
theorem B12300173 : Blo 1619008 12300173 := bstep (se 3 (by rfl) ⟨2306282, by rfl⟩ : syracuseStep 12300173 = 4612565) B4612565
theorem B2428817 : Blo 1619008 2428817 := bstep (se 2 (by rfl) ⟨910806, by rfl⟩ : syracuseStep 2428817 = 1821613) B1821613
theorem B3075985 : Blo 1619008 3075985 := bstep (se 2 (by rfl) ⟨1153494, by rfl⟩ : syracuseStep 3075985 = 2306989) B2306989
theorem B2428835 : Blo 1619008 2428835 := bstep (se 1 (by rfl) ⟨1821626, by rfl⟩ : syracuseStep 2428835 = 3643253) B3643253
theorem B4100017 : Blo 1619008 4100017 := bstep (se 2 (by rfl) ⟨1537506, by rfl⟩ : syracuseStep 4100017 = 3075013) B3075013
theorem B2428865 : Blo 1619008 2428865 := bstep (se 2 (by rfl) ⟨910824, by rfl⟩ : syracuseStep 2428865 = 1821649) B1821649
theorem B2428883 : Blo 1619008 2428883 := bstep (se 1 (by rfl) ⟨1821662, by rfl⟩ : syracuseStep 2428883 = 3643325) B3643325
theorem B1822675 : Blo 1619008 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B2428913 : Blo 1619008 2428913 := bstep (se 2 (by rfl) ⟨910842, by rfl⟩ : syracuseStep 2428913 = 1821685) B1821685
theorem B2428931 : Blo 1619008 2428931 := bstep (se 1 (by rfl) ⟨1821698, by rfl⟩ : syracuseStep 2428931 = 3643397) B3643397
theorem B2428961 : Blo 1619008 2428961 := bstep (se 2 (by rfl) ⟨910860, by rfl⟩ : syracuseStep 2428961 = 1821721) B1821721
theorem B2428979 : Blo 1619008 2428979 := bstep (se 1 (by rfl) ⟨1821734, by rfl⟩ : syracuseStep 2428979 = 3643469) B3643469
theorem B1945667 : Blo 1619008 1945667 := bstep (se 1 (by rfl) ⟨1459250, by rfl⟩ : syracuseStep 1945667 = 2918501) B2918501
theorem B2429009 : Blo 1619008 2429009 := bstep (se 2 (by rfl) ⟨910878, by rfl⟩ : syracuseStep 2429009 = 1821757) B1821757
theorem B2429027 : Blo 1619008 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B1822819 : Blo 1619008 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B5189741 : Blo 1619008 5189741 := bstep (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) B1946153
theorem B2429057 : Blo 1619008 2429057 := bstep (se 2 (by rfl) ⟨910896, by rfl⟩ : syracuseStep 2429057 = 1821793) B1821793
theorem B2732177 : Blo 1619008 2732177 := bstep (se 2 (by rfl) ⟨1024566, by rfl⟩ : syracuseStep 2732177 = 2049133) B2049133
theorem B2461841 : Blo 1619008 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B2429075 : Blo 1619008 2429075 := bstep (se 1 (by rfl) ⟨1821806, by rfl⟩ : syracuseStep 2429075 = 3643613) B3643613
theorem B4378769 : Blo 1619008 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B2429105 : Blo 1619008 2429105 := bstep (se 2 (by rfl) ⟨910914, by rfl⟩ : syracuseStep 2429105 = 1821829) B1821829
theorem B2429123 : Blo 1619008 2429123 := bstep (se 1 (by rfl) ⟨1821842, by rfl⟩ : syracuseStep 2429123 = 3643685) B3643685
theorem B4100291 : Blo 1619008 4100291 := bstep (se 1 (by rfl) ⟨3075218, by rfl⟩ : syracuseStep 4100291 = 6150437) B6150437
theorem B2429153 : Blo 1619008 2429153 := bstep (se 2 (by rfl) ⟨910932, by rfl⟩ : syracuseStep 2429153 = 1821865) B1821865
theorem B6918371 : Blo 1619008 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B2429171 : Blo 1619008 2429171 := bstep (se 1 (by rfl) ⟨1821878, by rfl⟩ : syracuseStep 2429171 = 3643757) B3643757
theorem B1822963 : Blo 1619008 1822963 := bstep (se 1 (by rfl) ⟨1367222, by rfl⟩ : syracuseStep 1822963 = 2734445) B2734445
theorem B9474317 : Blo 1619008 9474317 := bstep (se 3 (by rfl) ⟨1776434, by rfl⟩ : syracuseStep 9474317 = 3552869) B3552869
theorem B2732305 : Blo 1619008 2732305 := bstep (se 2 (by rfl) ⟨1024614, by rfl⟩ : syracuseStep 2732305 = 2049229) B2049229
theorem B2429201 : Blo 1619008 2429201 := bstep (se 2 (by rfl) ⟨910950, by rfl⟩ : syracuseStep 2429201 = 1821901) B1821901
theorem B2306323 : Blo 1619008 2306323 := bstep (se 1 (by rfl) ⟨1729742, by rfl⟩ : syracuseStep 2306323 = 3459485) B3459485
theorem B2429219 : Blo 1619008 2429219 := bstep (se 1 (by rfl) ⟨1821914, by rfl⟩ : syracuseStep 2429219 = 3643829) B3643829
theorem B9228593 : Blo 1619008 9228593 := bstep (se 2 (by rfl) ⟨3460722, by rfl⟩ : syracuseStep 9228593 = 6921445) B6921445
theorem B2732339 : Blo 1619008 2732339 := bstep (se 1 (by rfl) ⟨2049254, by rfl⟩ : syracuseStep 2732339 = 4098509) B4098509
theorem B2429249 : Blo 1619008 2429249 := bstep (se 2 (by rfl) ⟨910968, by rfl⟩ : syracuseStep 2429249 = 1821937) B1821937
theorem B2429267 : Blo 1619008 2429267 := bstep (se 1 (by rfl) ⟨1821950, by rfl⟩ : syracuseStep 2429267 = 3643901) B3643901
theorem B5468525 : Blo 1619008 5468525 := bstep (se 3 (by rfl) ⟨1025348, by rfl⟩ : syracuseStep 5468525 = 2050697) B2050697
theorem B2429297 : Blo 1619008 2429297 := bstep (se 2 (by rfl) ⟨910986, by rfl⟩ : syracuseStep 2429297 = 1821973) B1821973
theorem B2429315 : Blo 1619008 2429315 := bstep (se 1 (by rfl) ⟨1821986, by rfl⟩ : syracuseStep 2429315 = 3643973) B3643973
theorem B4100483 : Blo 1619008 4100483 := bstep (se 1 (by rfl) ⟨3075362, by rfl⟩ : syracuseStep 4100483 = 6150725) B6150725
theorem B1823107 : Blo 1619008 1823107 := bstep (se 1 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 1823107 = 2734661) B2734661
theorem B6148493 : Blo 1619008 6148493 := bstep (se 3 (by rfl) ⟨1152842, by rfl⟩ : syracuseStep 6148493 = 2305685) B2305685
theorem B1946003 : Blo 1619008 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B2429345 : Blo 1619008 2429345 := bstep (se 2 (by rfl) ⟨911004, by rfl⟩ : syracuseStep 2429345 = 1822009) B1822009
theorem B5468579 : Blo 1619008 5468579 := bstep (se 1 (by rfl) ⟨4101434, by rfl⟩ : syracuseStep 5468579 = 8202869) B8202869
theorem B2732467 : Blo 1619008 2732467 := bstep (se 1 (by rfl) ⟨2049350, by rfl⟩ : syracuseStep 2732467 = 4098701) B4098701
theorem B2429363 : Blo 1619008 2429363 := bstep (se 1 (by rfl) ⟨1822022, by rfl⟩ : syracuseStep 2429363 = 3644045) B3644045
theorem B2429393 : Blo 1619008 2429393 := bstep (se 2 (by rfl) ⟨911022, by rfl⟩ : syracuseStep 2429393 = 1822045) B1822045
theorem B2429411 : Blo 1619008 2429411 := bstep (se 1 (by rfl) ⟨1822058, by rfl⟩ : syracuseStep 2429411 = 3644117) B3644117
theorem B8761841 : Blo 1619008 8761841 := bstep (se 2 (by rfl) ⟨3285690, by rfl⟩ : syracuseStep 8761841 = 6571381) B6571381
theorem B2429441 : Blo 1619008 2429441 := bstep (se 2 (by rfl) ⟨911040, by rfl⟩ : syracuseStep 2429441 = 1822081) B1822081
theorem B8204813 : Blo 1619008 8204813 := bstep (se 3 (by rfl) ⟨1538402, by rfl⟩ : syracuseStep 8204813 = 3076805) B3076805
theorem B5190161 : Blo 1619008 5190161 := bstep (se 2 (by rfl) ⟨1946310, by rfl⟩ : syracuseStep 5190161 = 3892621) B3892621
theorem B2429459 : Blo 1619008 2429459 := bstep (se 1 (by rfl) ⟨1822094, by rfl⟩ : syracuseStep 2429459 = 3644189) B3644189
theorem B1823251 : Blo 1619008 1823251 := bstep (se 1 (by rfl) ⟨1367438, by rfl⟩ : syracuseStep 1823251 = 2734877) B2734877
theorem B2429489 : Blo 1619008 2429489 := bstep (se 2 (by rfl) ⟨911058, by rfl⟩ : syracuseStep 2429489 = 1822117) B1822117
theorem B2732609 : Blo 1619008 2732609 := bstep (se 2 (by rfl) ⟨1024728, by rfl⟩ : syracuseStep 2732609 = 2049457) B2049457
theorem B2429507 : Blo 1619008 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B2429537 : Blo 1619008 2429537 := bstep (se 2 (by rfl) ⟨911076, by rfl⟩ : syracuseStep 2429537 = 1822153) B1822153
theorem B2306659 : Blo 1619008 2306659 := bstep (se 1 (by rfl) ⟨1729994, by rfl⟩ : syracuseStep 2306659 = 3459989) B3459989
theorem B2429555 : Blo 1619008 2429555 := bstep (se 1 (by rfl) ⟨1822166, by rfl⟩ : syracuseStep 2429555 = 3644333) B3644333
theorem B10384013 : Blo 1619008 10384013 := bstep (se 3 (by rfl) ⟨1947002, by rfl⟩ : syracuseStep 10384013 = 3894005) B3894005
theorem B2429585 : Blo 1619008 2429585 := bstep (se 2 (by rfl) ⟨911094, by rfl⟩ : syracuseStep 2429585 = 1822189) B1822189
theorem B2429603 : Blo 1619008 2429603 := bstep (se 1 (by rfl) ⟨1822202, by rfl⟩ : syracuseStep 2429603 = 3644405) B3644405
theorem B1823395 : Blo 1619008 1823395 := bstep (se 1 (by rfl) ⟨1367546, by rfl⟩ : syracuseStep 1823395 = 2735093) B2735093
theorem B4379309 : Blo 1619008 4379309 := bstep (se 3 (by rfl) ⟨821120, by rfl⟩ : syracuseStep 4379309 = 1642241) B1642241
theorem B5468849 : Blo 1619008 5468849 := bstep (se 2 (by rfl) ⟨2050818, by rfl⟩ : syracuseStep 5468849 = 4101637) B4101637
theorem B8762033 : Blo 1619008 8762033 := bstep (se 2 (by rfl) ⟨3285762, by rfl⟩ : syracuseStep 8762033 = 6571525) B6571525
theorem B2732737 : Blo 1619008 2732737 := bstep (se 2 (by rfl) ⟨1024776, by rfl⟩ : syracuseStep 2732737 = 2049553) B2049553
theorem B2429633 : Blo 1619008 2429633 := bstep (se 2 (by rfl) ⟨911112, by rfl⟩ : syracuseStep 2429633 = 1822225) B1822225
theorem B2429651 : Blo 1619008 2429651 := bstep (se 1 (by rfl) ⟨1822238, by rfl⟩ : syracuseStep 2429651 = 3644477) B3644477
theorem B2593505 : Blo 1619008 2593505 := bstep (se 2 (by rfl) ⟨972564, by rfl⟩ : syracuseStep 2593505 = 1945129) B1945129
theorem B2732771 : Blo 1619008 2732771 := bstep (se 1 (by rfl) ⟨2049578, by rfl⟩ : syracuseStep 2732771 = 4099157) B4099157
theorem B2429681 : Blo 1619008 2429681 := bstep (se 2 (by rfl) ⟨911130, by rfl⟩ : syracuseStep 2429681 = 1822261) B1822261
theorem B2429699 : Blo 1619008 2429699 := bstep (se 1 (by rfl) ⟨1822274, by rfl⟩ : syracuseStep 2429699 = 3644549) B3644549
theorem B2429729 : Blo 1619008 2429729 := bstep (se 2 (by rfl) ⟨911148, by rfl⟩ : syracuseStep 2429729 = 1822297) B1822297
theorem B2429747 : Blo 1619008 2429747 := bstep (se 1 (by rfl) ⟨1822310, by rfl⟩ : syracuseStep 2429747 = 3644621) B3644621
theorem B1823539 : Blo 1619008 1823539 := bstep (se 1 (by rfl) ⟨1367654, by rfl⟩ : syracuseStep 1823539 = 2735309) B2735309
theorem B2429777 : Blo 1619008 2429777 := bstep (se 2 (by rfl) ⟨911166, by rfl⟩ : syracuseStep 2429777 = 1822333) B1822333
theorem B2732899 : Blo 1619008 2732899 := bstep (se 1 (by rfl) ⟨2049674, by rfl⟩ : syracuseStep 2732899 = 4099349) B4099349
theorem B2429795 : Blo 1619008 2429795 := bstep (se 1 (by rfl) ⟨1822346, by rfl⟩ : syracuseStep 2429795 = 3644693) B3644693
theorem B3461987 : Blo 1619008 3461987 := bstep (se 1 (by rfl) ⟨2596490, by rfl⟩ : syracuseStep 3461987 = 5192981) B5192981
theorem B2429825 : Blo 1619008 2429825 := bstep (se 2 (by rfl) ⟨911184, by rfl⟩ : syracuseStep 2429825 = 1822369) B1822369
theorem B4928401 : Blo 1619008 4928401 := bstep (se 2 (by rfl) ⟨1848150, by rfl⟩ : syracuseStep 4928401 = 3696301) B3696301
theorem B2429843 : Blo 1619008 2429843 := bstep (se 1 (by rfl) ⟨1822382, by rfl⟩ : syracuseStep 2429843 = 3644765) B3644765
theorem B2429873 : Blo 1619008 2429873 := bstep (se 2 (by rfl) ⟨911202, by rfl⟩ : syracuseStep 2429873 = 1822405) B1822405
theorem B3077041 : Blo 1619008 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B2429891 : Blo 1619008 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B2429921 : Blo 1619008 2429921 := bstep (se 2 (by rfl) ⟨911220, by rfl⟩ : syracuseStep 2429921 = 1822441) B1822441
theorem B2733041 : Blo 1619008 2733041 := bstep (se 2 (by rfl) ⟨1024890, by rfl⟩ : syracuseStep 2733041 = 2049781) B2049781
theorem B2429939 : Blo 1619008 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B2495491 : Blo 1619008 2495491 := bstep (se 1 (by rfl) ⟨1871618, by rfl⟩ : syracuseStep 2495491 = 3743237) B3743237
theorem B2429969 : Blo 1619008 2429969 := bstep (se 2 (by rfl) ⟨911238, by rfl⟩ : syracuseStep 2429969 = 1822477) B1822477
theorem B2429987 : Blo 1619008 2429987 := bstep (se 1 (by rfl) ⟨1822490, by rfl⟩ : syracuseStep 2429987 = 3644981) B3644981
theorem B2430017 : Blo 1619008 2430017 := bstep (se 2 (by rfl) ⟨911256, by rfl⟩ : syracuseStep 2430017 = 1822513) B1822513
theorem B1619011 : Blo 1619008 1619011 := bstep (se 1 (by rfl) ⟨1214258, by rfl⟩ : syracuseStep 1619011 = 2428517) B2428517
theorem B7894093 : Blo 1619008 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B1619027 : Blo 1619008 1619027 := bstep (se 1 (by rfl) ⟨1214270, by rfl⟩ : syracuseStep 1619027 = 2428541) B2428541
theorem B2430035 : Blo 1619008 2430035 := bstep (se 1 (by rfl) ⟨1822526, by rfl⟩ : syracuseStep 2430035 = 3645053) B3645053
theorem B1619043 : Blo 1619008 1619043 := bstep (se 1 (by rfl) ⟨1214282, by rfl⟩ : syracuseStep 1619043 = 2428565) B2428565
theorem B5837923 : Blo 1619008 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B2733169 : Blo 1619008 2733169 := bstep (se 2 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 2733169 = 2049877) B2049877
theorem B2430065 : Blo 1619008 2430065 := bstep (se 2 (by rfl) ⟨911274, by rfl⟩ : syracuseStep 2430065 = 1822549) B1822549
theorem B1619059 : Blo 1619008 1619059 := bstep (se 1 (by rfl) ⟨1214294, by rfl⟩ : syracuseStep 1619059 = 2428589) B2428589
theorem B1619075 : Blo 1619008 1619075 := bstep (se 1 (by rfl) ⟨1214306, by rfl⟩ : syracuseStep 1619075 = 2428613) B2428613
theorem B2430083 : Blo 1619008 2430083 := bstep (se 1 (by rfl) ⟨1822562, by rfl⟩ : syracuseStep 2430083 = 3645125) B3645125
theorem B2307217 : Blo 1619008 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1619091 : Blo 1619008 1619091 := bstep (se 1 (by rfl) ⟨1214318, by rfl⟩ : syracuseStep 1619091 = 2428637) B2428637
theorem B2733203 : Blo 1619008 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B2430113 : Blo 1619008 2430113 := bstep (se 2 (by rfl) ⟨911292, by rfl⟩ : syracuseStep 2430113 = 1822585) B1822585
theorem B1619107 : Blo 1619008 1619107 := bstep (se 1 (by rfl) ⟨1214330, by rfl⟩ : syracuseStep 1619107 = 2428661) B2428661
theorem B5059747 : Blo 1619008 5059747 := bstep (se 1 (by rfl) ⟨3794810, by rfl⟩ : syracuseStep 5059747 = 7589621) B7589621
theorem B6149297 : Blo 1619008 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B1619123 : Blo 1619008 1619123 := bstep (se 1 (by rfl) ⟨1214342, by rfl⟩ : syracuseStep 1619123 = 2428685) B2428685
theorem B2430131 : Blo 1619008 2430131 := bstep (se 1 (by rfl) ⟨1822598, by rfl⟩ : syracuseStep 2430131 = 3645197) B3645197
theorem B2307251 : Blo 1619008 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B21050549 : Blo 1619008 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B1619139 : Blo 1619008 1619139 := bstep (se 1 (by rfl) ⟨1214354, by rfl⟩ : syracuseStep 1619139 = 2428709) B2428709
theorem B5469389 : Blo 1619008 5469389 := bstep (se 3 (by rfl) ⟨1025510, by rfl⟩ : syracuseStep 5469389 = 2051021) B2051021
theorem B2430161 : Blo 1619008 2430161 := bstep (se 2 (by rfl) ⟨911310, by rfl⟩ : syracuseStep 2430161 = 1822621) B1822621
theorem B1619155 : Blo 1619008 1619155 := bstep (se 1 (by rfl) ⟨1214366, by rfl⟩ : syracuseStep 1619155 = 2428733) B2428733
theorem B1619171 : Blo 1619008 1619171 := bstep (se 1 (by rfl) ⟨1214378, by rfl⟩ : syracuseStep 1619171 = 2428757) B2428757
theorem B2430179 : Blo 1619008 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B8197361 : Blo 1619008 8197361 := bstep (se 2 (by rfl) ⟨3074010, by rfl⟩ : syracuseStep 8197361 = 6148021) B6148021
theorem B1619187 : Blo 1619008 1619187 := bstep (se 1 (by rfl) ⟨1214390, by rfl⟩ : syracuseStep 1619187 = 2428781) B2428781
theorem B2430209 : Blo 1619008 2430209 := bstep (se 2 (by rfl) ⟨911328, by rfl⟩ : syracuseStep 2430209 = 1822657) B1822657
theorem B1619203 : Blo 1619008 1619203 := bstep (se 1 (by rfl) ⟨1214402, by rfl⟩ : syracuseStep 1619203 = 2428805) B2428805
theorem B5469443 : Blo 1619008 5469443 := bstep (se 1 (by rfl) ⟨4102082, by rfl⟩ : syracuseStep 5469443 = 8204165) B8204165
theorem B1619219 : Blo 1619008 1619219 := bstep (se 1 (by rfl) ⟨1214414, by rfl⟩ : syracuseStep 1619219 = 2428829) B2428829
theorem B2733331 : Blo 1619008 2733331 := bstep (se 1 (by rfl) ⟨2049998, by rfl⟩ : syracuseStep 2733331 = 4099997) B4099997
theorem B2430227 : Blo 1619008 2430227 := bstep (se 1 (by rfl) ⟨1822670, by rfl⟩ : syracuseStep 2430227 = 3645341) B3645341
theorem B1619235 : Blo 1619008 1619235 := bstep (se 1 (by rfl) ⟨1214426, by rfl⟩ : syracuseStep 1619235 = 2428853) B2428853
theorem B2430257 : Blo 1619008 2430257 := bstep (se 2 (by rfl) ⟨911346, by rfl⟩ : syracuseStep 2430257 = 1822693) B1822693
theorem B4101425 : Blo 1619008 4101425 := bstep (se 2 (by rfl) ⟨1538034, by rfl⟩ : syracuseStep 4101425 = 3076069) B3076069
theorem B1619251 : Blo 1619008 1619251 := bstep (se 1 (by rfl) ⟨1214438, by rfl⟩ : syracuseStep 1619251 = 2428877) B2428877
theorem B1619267 : Blo 1619008 1619267 := bstep (se 1 (by rfl) ⟨1214450, by rfl⟩ : syracuseStep 1619267 = 2428901) B2428901
theorem B2430275 : Blo 1619008 2430275 := bstep (se 1 (by rfl) ⟨1822706, by rfl⟩ : syracuseStep 2430275 = 3645413) B3645413
theorem B4437325 : Blo 1619008 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B1619283 : Blo 1619008 1619283 := bstep (se 1 (by rfl) ⟨1214462, by rfl⟩ : syracuseStep 1619283 = 2428925) B2428925
theorem B2430305 : Blo 1619008 2430305 := bstep (se 2 (by rfl) ⟨911364, by rfl⟩ : syracuseStep 2430305 = 1822729) B1822729
theorem B1619299 : Blo 1619008 1619299 := bstep (se 1 (by rfl) ⟨1214474, by rfl⟩ : syracuseStep 1619299 = 2428949) B2428949
theorem B4101475 : Blo 1619008 4101475 := bstep (se 1 (by rfl) ⟨3076106, by rfl⟩ : syracuseStep 4101475 = 6152213) B6152213
theorem B1619315 : Blo 1619008 1619315 := bstep (se 1 (by rfl) ⟨1214486, by rfl⟩ : syracuseStep 1619315 = 2428973) B2428973
theorem B2430323 : Blo 1619008 2430323 := bstep (se 1 (by rfl) ⟨1822742, by rfl⟩ : syracuseStep 2430323 = 3645485) B3645485
theorem B1619331 : Blo 1619008 1619331 := bstep (se 1 (by rfl) ⟨1214498, by rfl⟩ : syracuseStep 1619331 = 2428997) B2428997
theorem B2430353 : Blo 1619008 2430353 := bstep (se 2 (by rfl) ⟨911382, by rfl⟩ : syracuseStep 2430353 = 1822765) B1822765
theorem B1619347 : Blo 1619008 1619347 := bstep (se 1 (by rfl) ⟨1214510, by rfl⟩ : syracuseStep 1619347 = 2429021) B2429021
theorem B1619363 : Blo 1619008 1619363 := bstep (se 1 (by rfl) ⟨1214522, by rfl⟩ : syracuseStep 1619363 = 2429045) B2429045
theorem B2733473 : Blo 1619008 2733473 := bstep (se 2 (by rfl) ⟨1025052, by rfl⟩ : syracuseStep 2733473 = 2050105) B2050105
theorem B2430371 : Blo 1619008 2430371 := bstep (se 1 (by rfl) ⟨1822778, by rfl⟩ : syracuseStep 2430371 = 3645557) B3645557
theorem B1619379 : Blo 1619008 1619379 := bstep (se 1 (by rfl) ⟨1214534, by rfl⟩ : syracuseStep 1619379 = 2429069) B2429069
theorem B2430401 : Blo 1619008 2430401 := bstep (se 2 (by rfl) ⟨911400, by rfl⟩ : syracuseStep 2430401 = 1822801) B1822801
theorem B1619395 : Blo 1619008 1619395 := bstep (se 1 (by rfl) ⟨1214546, by rfl⟩ : syracuseStep 1619395 = 2429093) B2429093
theorem B1619411 : Blo 1619008 1619411 := bstep (se 1 (by rfl) ⟨1214558, by rfl⟩ : syracuseStep 1619411 = 2429117) B2429117
theorem B2430419 : Blo 1619008 2430419 := bstep (se 1 (by rfl) ⟨1822814, by rfl⟩ : syracuseStep 2430419 = 3645629) B3645629
theorem B1619427 : Blo 1619008 1619427 := bstep (se 1 (by rfl) ⟨1214570, by rfl⟩ : syracuseStep 1619427 = 2429141) B2429141
theorem B2430449 : Blo 1619008 2430449 := bstep (se 2 (by rfl) ⟨911418, by rfl⟩ : syracuseStep 2430449 = 1822837) B1822837
theorem B1619443 : Blo 1619008 1619443 := bstep (se 1 (by rfl) ⟨1214582, by rfl⟩ : syracuseStep 1619443 = 2429165) B2429165
theorem B4101617 : Blo 1619008 4101617 := bstep (se 2 (by rfl) ⟨1538106, by rfl⟩ : syracuseStep 4101617 = 3076213) B3076213
theorem B1619459 : Blo 1619008 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B2430467 : Blo 1619008 2430467 := bstep (se 1 (by rfl) ⟨1822850, by rfl⟩ : syracuseStep 2430467 = 3645701) B3645701
theorem B5469713 : Blo 1619008 5469713 := bstep (se 2 (by rfl) ⟨2051142, by rfl⟩ : syracuseStep 5469713 = 4102285) B4102285
theorem B1619475 : Blo 1619008 1619475 := bstep (se 1 (by rfl) ⟨1214606, by rfl⟩ : syracuseStep 1619475 = 2429213) B2429213
theorem B2733601 : Blo 1619008 2733601 := bstep (se 2 (by rfl) ⟨1025100, by rfl⟩ : syracuseStep 2733601 = 2050201) B2050201
theorem B2430497 : Blo 1619008 2430497 := bstep (se 2 (by rfl) ⟨911436, by rfl⟩ : syracuseStep 2430497 = 1822873) B1822873
theorem B1619491 : Blo 1619008 1619491 := bstep (se 1 (by rfl) ⟨1214618, by rfl⟩ : syracuseStep 1619491 = 2429237) B2429237
theorem B3642929 : Blo 1619008 3642929 := bstep (se 2 (by rfl) ⟨1366098, by rfl⟩ : syracuseStep 3642929 = 2732197) B2732197
theorem B1619507 : Blo 1619008 1619507 := bstep (se 1 (by rfl) ⟨1214630, by rfl⟩ : syracuseStep 1619507 = 2429261) B2429261
theorem B2430515 : Blo 1619008 2430515 := bstep (se 1 (by rfl) ⟨1822886, by rfl⟩ : syracuseStep 2430515 = 3645773) B3645773
theorem B3642947 : Blo 1619008 3642947 := bstep (se 1 (by rfl) ⟨2732210, by rfl⟩ : syracuseStep 3642947 = 5464421) B5464421
theorem B1619523 : Blo 1619008 1619523 := bstep (se 1 (by rfl) ⟨1214642, by rfl⟩ : syracuseStep 1619523 = 2429285) B2429285
theorem B2733635 : Blo 1619008 2733635 := bstep (se 1 (by rfl) ⟨2050226, by rfl⟩ : syracuseStep 2733635 = 4100453) B4100453
theorem B2430545 : Blo 1619008 2430545 := bstep (se 2 (by rfl) ⟨911454, by rfl⟩ : syracuseStep 2430545 = 1822909) B1822909
theorem B1619539 : Blo 1619008 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B1619555 : Blo 1619008 1619555 := bstep (se 1 (by rfl) ⟨1214666, by rfl⟩ : syracuseStep 1619555 = 2429333) B2429333
theorem B2430563 : Blo 1619008 2430563 := bstep (se 1 (by rfl) ⟨1822922, by rfl⟩ : syracuseStep 2430563 = 3645845) B3645845
theorem B1619571 : Blo 1619008 1619571 := bstep (se 1 (by rfl) ⟨1214678, by rfl⟩ : syracuseStep 1619571 = 2429357) B2429357
theorem B1619587 : Blo 1619008 1619587 := bstep (se 1 (by rfl) ⟨1214690, by rfl⟩ : syracuseStep 1619587 = 2429381) B2429381
theorem B2430593 : Blo 1619008 2430593 := bstep (se 2 (by rfl) ⟨911472, by rfl⟩ : syracuseStep 2430593 = 1822945) B1822945
theorem B1619603 : Blo 1619008 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B2430611 : Blo 1619008 2430611 := bstep (se 1 (by rfl) ⟨1822958, by rfl⟩ : syracuseStep 2430611 = 3645917) B3645917
theorem B1619619 : Blo 1619008 1619619 := bstep (se 1 (by rfl) ⟨1214714, by rfl⟩ : syracuseStep 1619619 = 2429429) B2429429
theorem B2430641 : Blo 1619008 2430641 := bstep (se 2 (by rfl) ⟨911490, by rfl⟩ : syracuseStep 2430641 = 1822981) B1822981
theorem B1619635 : Blo 1619008 1619635 := bstep (se 1 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 1619635 = 2429453) B2429453
theorem B1619651 : Blo 1619008 1619651 := bstep (se 1 (by rfl) ⟨1214738, by rfl⟩ : syracuseStep 1619651 = 2429477) B2429477
theorem B2733763 : Blo 1619008 2733763 := bstep (se 1 (by rfl) ⟨2050322, by rfl⟩ : syracuseStep 2733763 = 4100645) B4100645
theorem B2430659 : Blo 1619008 2430659 := bstep (se 1 (by rfl) ⟨1822994, by rfl⟩ : syracuseStep 2430659 = 3645989) B3645989
theorem B1619667 : Blo 1619008 1619667 := bstep (se 1 (by rfl) ⟨1214750, by rfl⟩ : syracuseStep 1619667 = 2429501) B2429501
theorem B2430689 : Blo 1619008 2430689 := bstep (se 2 (by rfl) ⟨911508, by rfl⟩ : syracuseStep 2430689 = 1823017) B1823017
theorem B1619683 : Blo 1619008 1619683 := bstep (se 1 (by rfl) ⟨1214762, by rfl⟩ : syracuseStep 1619683 = 2429525) B2429525
theorem B9230051 : Blo 1619008 9230051 := bstep (se 1 (by rfl) ⟨6922538, by rfl⟩ : syracuseStep 9230051 = 13845077) B13845077
theorem B2307809 : Blo 1619008 2307809 := bstep (se 2 (by rfl) ⟨865428, by rfl⟩ : syracuseStep 2307809 = 1730857) B1730857
theorem B4675313 : Blo 1619008 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B1619699 : Blo 1619008 1619699 := bstep (se 1 (by rfl) ⟨1214774, by rfl⟩ : syracuseStep 1619699 = 2429549) B2429549
theorem B2430707 : Blo 1619008 2430707 := bstep (se 1 (by rfl) ⟨1823030, by rfl⟩ : syracuseStep 2430707 = 3646061) B3646061
theorem B1619715 : Blo 1619008 1619715 := bstep (se 1 (by rfl) ⟨1214786, by rfl⟩ : syracuseStep 1619715 = 2429573) B2429573
theorem B11089669 : Blo 1619008 11089669 := bstep (se 4 (by rfl) ⟨1039656, by rfl⟩ : syracuseStep 11089669 = 2079313) B2079313
theorem B2430737 : Blo 1619008 2430737 := bstep (se 2 (by rfl) ⟨911526, by rfl⟩ : syracuseStep 2430737 = 1823053) B1823053
theorem B1619731 : Blo 1619008 1619731 := bstep (se 1 (by rfl) ⟨1214798, by rfl⟩ : syracuseStep 1619731 = 2429597) B2429597
theorem B1619747 : Blo 1619008 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B2430755 : Blo 1619008 2430755 := bstep (se 1 (by rfl) ⟨1823066, by rfl⟩ : syracuseStep 2430755 = 3646133) B3646133
theorem B2307889 : Blo 1619008 2307889 := bstep (se 2 (by rfl) ⟨865458, by rfl⟩ : syracuseStep 2307889 = 1730917) B1730917
theorem B1619763 : Blo 1619008 1619763 := bstep (se 1 (by rfl) ⟨1214822, by rfl⟩ : syracuseStep 1619763 = 2429645) B2429645
theorem B2430785 : Blo 1619008 2430785 := bstep (se 2 (by rfl) ⟨911544, by rfl⟩ : syracuseStep 2430785 = 1823089) B1823089
theorem B1619779 : Blo 1619008 1619779 := bstep (se 1 (by rfl) ⟨1214834, by rfl⟩ : syracuseStep 1619779 = 2429669) B2429669
theorem B6149965 : Blo 1619008 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B3643217 : Blo 1619008 3643217 := bstep (se 2 (by rfl) ⟨1366206, by rfl⟩ : syracuseStep 3643217 = 2732413) B2732413
theorem B1619795 : Blo 1619008 1619795 := bstep (se 1 (by rfl) ⟨1214846, by rfl⟩ : syracuseStep 1619795 = 2429693) B2429693
theorem B2733905 : Blo 1619008 2733905 := bstep (se 2 (by rfl) ⟨1025214, by rfl⟩ : syracuseStep 2733905 = 2050429) B2050429
theorem B2430803 : Blo 1619008 2430803 := bstep (se 1 (by rfl) ⟨1823102, by rfl⟩ : syracuseStep 2430803 = 3646205) B3646205
theorem B3643235 : Blo 1619008 3643235 := bstep (se 1 (by rfl) ⟨2732426, by rfl⟩ : syracuseStep 3643235 = 5464853) B5464853
theorem B1619811 : Blo 1619008 1619811 := bstep (se 1 (by rfl) ⟨1214858, by rfl⟩ : syracuseStep 1619811 = 2429717) B2429717
theorem B2430833 : Blo 1619008 2430833 := bstep (se 2 (by rfl) ⟨911562, by rfl⟩ : syracuseStep 2430833 = 1823125) B1823125
theorem B1619827 : Blo 1619008 1619827 := bstep (se 1 (by rfl) ⟨1214870, by rfl⟩ : syracuseStep 1619827 = 2429741) B2429741
theorem B1619843 : Blo 1619008 1619843 := bstep (se 1 (by rfl) ⟨1214882, by rfl⟩ : syracuseStep 1619843 = 2429765) B2429765
theorem B2430851 : Blo 1619008 2430851 := bstep (se 1 (by rfl) ⟨1823138, by rfl⟩ : syracuseStep 2430851 = 3646277) B3646277
theorem B1619859 : Blo 1619008 1619859 := bstep (se 1 (by rfl) ⟨1214894, by rfl⟩ : syracuseStep 1619859 = 2429789) B2429789
theorem B2430881 : Blo 1619008 2430881 := bstep (se 2 (by rfl) ⟨911580, by rfl⟩ : syracuseStep 2430881 = 1823161) B1823161
theorem B1619875 : Blo 1619008 1619875 := bstep (se 1 (by rfl) ⟨1214906, by rfl⟩ : syracuseStep 1619875 = 2429813) B2429813
theorem B6920113 : Blo 1619008 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B1619891 : Blo 1619008 1619891 := bstep (se 1 (by rfl) ⟨1214918, by rfl⟩ : syracuseStep 1619891 = 2429837) B2429837
theorem B2430899 : Blo 1619008 2430899 := bstep (se 1 (by rfl) ⟨1823174, by rfl⟩ : syracuseStep 2430899 = 3646349) B3646349
theorem B1619907 : Blo 1619008 1619907 := bstep (se 1 (by rfl) ⟨1214930, by rfl⟩ : syracuseStep 1619907 = 2429861) B2429861
theorem B2734033 : Blo 1619008 2734033 := bstep (se 2 (by rfl) ⟨1025262, by rfl⟩ : syracuseStep 2734033 = 2050525) B2050525
theorem B1619923 : Blo 1619008 1619923 := bstep (se 1 (by rfl) ⟨1214942, by rfl⟩ : syracuseStep 1619923 = 2429885) B2429885
theorem B2430929 : Blo 1619008 2430929 := bstep (se 2 (by rfl) ⟨911598, by rfl⟩ : syracuseStep 2430929 = 1823197) B1823197
theorem B1619939 : Blo 1619008 1619939 := bstep (se 1 (by rfl) ⟨1214954, by rfl⟩ : syracuseStep 1619939 = 2429909) B2429909
theorem B2430947 : Blo 1619008 2430947 := bstep (se 1 (by rfl) ⟨1823210, by rfl⟩ : syracuseStep 2430947 = 3646421) B3646421
theorem B1619955 : Blo 1619008 1619955 := bstep (se 1 (by rfl) ⟨1214966, by rfl⟩ : syracuseStep 1619955 = 2429933) B2429933
theorem B2734067 : Blo 1619008 2734067 := bstep (se 1 (by rfl) ⟨2050550, by rfl⟩ : syracuseStep 2734067 = 4101101) B4101101
theorem B2430977 : Blo 1619008 2430977 := bstep (se 2 (by rfl) ⟨911616, by rfl⟩ : syracuseStep 2430977 = 1823233) B1823233
theorem B1619971 : Blo 1619008 1619971 := bstep (se 1 (by rfl) ⟨1214978, by rfl⟩ : syracuseStep 1619971 = 2429957) B2429957
theorem B1619987 : Blo 1619008 1619987 := bstep (se 1 (by rfl) ⟨1214990, by rfl⟩ : syracuseStep 1619987 = 2429981) B2429981
theorem B2430995 : Blo 1619008 2430995 := bstep (se 1 (by rfl) ⟨1823246, by rfl⟩ : syracuseStep 2430995 = 3646493) B3646493
theorem B1620003 : Blo 1619008 1620003 := bstep (se 1 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 1620003 = 2430005) B2430005
theorem B5470253 : Blo 1619008 5470253 := bstep (se 3 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 5470253 = 2051345) B2051345
theorem B2431025 : Blo 1619008 2431025 := bstep (se 2 (by rfl) ⟨911634, by rfl⟩ : syracuseStep 2431025 = 1823269) B1823269
theorem B1620019 : Blo 1619008 1620019 := bstep (se 1 (by rfl) ⟨1215014, by rfl⟩ : syracuseStep 1620019 = 2430029) B2430029
theorem B1620035 : Blo 1619008 1620035 := bstep (se 1 (by rfl) ⟨1215026, by rfl⟩ : syracuseStep 1620035 = 2430053) B2430053
theorem B2431043 : Blo 1619008 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B1620051 : Blo 1619008 1620051 := bstep (se 1 (by rfl) ⟨1215038, by rfl⟩ : syracuseStep 1620051 = 2430077) B2430077
theorem B1620067 : Blo 1619008 1620067 := bstep (se 1 (by rfl) ⟨1215050, by rfl⟩ : syracuseStep 1620067 = 2430101) B2430101
theorem B2431073 : Blo 1619008 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B5470307 : Blo 1619008 5470307 := bstep (se 1 (by rfl) ⟨4102730, by rfl⟩ : syracuseStep 5470307 = 8205461) B8205461
theorem B3643505 : Blo 1619008 3643505 := bstep (se 2 (by rfl) ⟨1366314, by rfl⟩ : syracuseStep 3643505 = 2732629) B2732629
theorem B1620083 : Blo 1619008 1620083 := bstep (se 1 (by rfl) ⟨1215062, by rfl⟩ : syracuseStep 1620083 = 2430125) B2430125
theorem B2734195 : Blo 1619008 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B2431091 : Blo 1619008 2431091 := bstep (se 1 (by rfl) ⟨1823318, by rfl⟩ : syracuseStep 2431091 = 3646637) B3646637
theorem B3643523 : Blo 1619008 3643523 := bstep (se 1 (by rfl) ⟨2732642, by rfl⟩ : syracuseStep 3643523 = 5465285) B5465285
theorem B1620099 : Blo 1619008 1620099 := bstep (se 1 (by rfl) ⟨1215074, by rfl⟩ : syracuseStep 1620099 = 2430149) B2430149
theorem B2431121 : Blo 1619008 2431121 := bstep (se 2 (by rfl) ⟨911670, by rfl⟩ : syracuseStep 2431121 = 1823341) B1823341
theorem B1620115 : Blo 1619008 1620115 := bstep (se 1 (by rfl) ⟨1215086, by rfl⟩ : syracuseStep 1620115 = 2430173) B2430173
theorem B1620131 : Blo 1619008 1620131 := bstep (se 1 (by rfl) ⟨1215098, by rfl⟩ : syracuseStep 1620131 = 2430197) B2430197
theorem B2431139 : Blo 1619008 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B1620147 : Blo 1619008 1620147 := bstep (se 1 (by rfl) ⟨1215110, by rfl⟩ : syracuseStep 1620147 = 2430221) B2430221
theorem B2431169 : Blo 1619008 2431169 := bstep (se 2 (by rfl) ⟨911688, by rfl⟩ : syracuseStep 2431169 = 1823377) B1823377
theorem B1620163 : Blo 1619008 1620163 := bstep (se 1 (by rfl) ⟨1215122, by rfl⟩ : syracuseStep 1620163 = 2430245) B2430245
theorem B1620179 : Blo 1619008 1620179 := bstep (se 1 (by rfl) ⟨1215134, by rfl⟩ : syracuseStep 1620179 = 2430269) B2430269
theorem B2431187 : Blo 1619008 2431187 := bstep (se 1 (by rfl) ⟨1823390, by rfl⟩ : syracuseStep 2431187 = 3646781) B3646781
theorem B1620195 : Blo 1619008 1620195 := bstep (se 1 (by rfl) ⟨1215146, by rfl⟩ : syracuseStep 1620195 = 2430293) B2430293
theorem B2431217 : Blo 1619008 2431217 := bstep (se 2 (by rfl) ⟨911706, by rfl⟩ : syracuseStep 2431217 = 1823413) B1823413
theorem B1620211 : Blo 1619008 1620211 := bstep (se 1 (by rfl) ⟨1215158, by rfl⟩ : syracuseStep 1620211 = 2430317) B2430317
theorem B2734337 : Blo 1619008 2734337 := bstep (se 2 (by rfl) ⟨1025376, by rfl⟩ : syracuseStep 2734337 = 2050753) B2050753
theorem B1620227 : Blo 1619008 1620227 := bstep (se 1 (by rfl) ⟨1215170, by rfl⟩ : syracuseStep 1620227 = 2430341) B2430341
theorem B2431235 : Blo 1619008 2431235 := bstep (se 1 (by rfl) ⟨1823426, by rfl⟩ : syracuseStep 2431235 = 3646853) B3646853
theorem B1620243 : Blo 1619008 1620243 := bstep (se 1 (by rfl) ⟨1215182, by rfl⟩ : syracuseStep 1620243 = 2430365) B2430365
theorem B2431265 : Blo 1619008 2431265 := bstep (se 2 (by rfl) ⟨911724, by rfl⟩ : syracuseStep 2431265 = 1823449) B1823449
theorem B1620259 : Blo 1619008 1620259 := bstep (se 1 (by rfl) ⟨1215194, by rfl⟩ : syracuseStep 1620259 = 2430389) B2430389
theorem B1620275 : Blo 1619008 1620275 := bstep (se 1 (by rfl) ⟨1215206, by rfl⟩ : syracuseStep 1620275 = 2430413) B2430413
theorem B2431283 : Blo 1619008 2431283 := bstep (se 1 (by rfl) ⟨1823462, by rfl⟩ : syracuseStep 2431283 = 3646925) B3646925
theorem B1620291 : Blo 1619008 1620291 := bstep (se 1 (by rfl) ⟨1215218, by rfl⟩ : syracuseStep 1620291 = 2430437) B2430437
theorem B2431313 : Blo 1619008 2431313 := bstep (se 2 (by rfl) ⟨911742, by rfl⟩ : syracuseStep 2431313 = 1823485) B1823485
theorem B1620307 : Blo 1619008 1620307 := bstep (se 1 (by rfl) ⟨1215230, by rfl⟩ : syracuseStep 1620307 = 2430461) B2430461
theorem B1620323 : Blo 1619008 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B2431331 : Blo 1619008 2431331 := bstep (se 1 (by rfl) ⟨1823498, by rfl⟩ : syracuseStep 2431331 = 3646997) B3646997
theorem B5470577 : Blo 1619008 5470577 := bstep (se 2 (by rfl) ⟨2051466, by rfl⟩ : syracuseStep 5470577 = 4102933) B4102933
theorem B1620339 : Blo 1619008 1620339 := bstep (se 1 (by rfl) ⟨1215254, by rfl⟩ : syracuseStep 1620339 = 2430509) B2430509
theorem B2734465 : Blo 1619008 2734465 := bstep (se 2 (by rfl) ⟨1025424, by rfl⟩ : syracuseStep 2734465 = 2050849) B2050849
theorem B2431361 : Blo 1619008 2431361 := bstep (se 2 (by rfl) ⟨911760, by rfl⟩ : syracuseStep 2431361 = 1823521) B1823521
theorem B1620355 : Blo 1619008 1620355 := bstep (se 1 (by rfl) ⟨1215266, by rfl⟩ : syracuseStep 1620355 = 2430533) B2430533
theorem B3643793 : Blo 1619008 3643793 := bstep (se 2 (by rfl) ⟨1366422, by rfl⟩ : syracuseStep 3643793 = 2732845) B2732845
theorem B1620371 : Blo 1619008 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B2431379 : Blo 1619008 2431379 := bstep (se 1 (by rfl) ⟨1823534, by rfl⟩ : syracuseStep 2431379 = 3647069) B3647069
theorem B3643811 : Blo 1619008 3643811 := bstep (se 1 (by rfl) ⟨2732858, by rfl⟩ : syracuseStep 3643811 = 5465717) B5465717
theorem B2595235 : Blo 1619008 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B1620387 : Blo 1619008 1620387 := bstep (se 1 (by rfl) ⟨1215290, by rfl⟩ : syracuseStep 1620387 = 2430581) B2430581
theorem B2734499 : Blo 1619008 2734499 := bstep (se 1 (by rfl) ⟨2050874, by rfl⟩ : syracuseStep 2734499 = 4101749) B4101749
theorem B5257649 : Blo 1619008 5257649 := bstep (se 2 (by rfl) ⟨1971618, by rfl⟩ : syracuseStep 5257649 = 3943237) B3943237
theorem B2431409 : Blo 1619008 2431409 := bstep (se 2 (by rfl) ⟨911778, by rfl⟩ : syracuseStep 2431409 = 1823557) B1823557
theorem B1620403 : Blo 1619008 1620403 := bstep (se 1 (by rfl) ⟨1215302, by rfl⟩ : syracuseStep 1620403 = 2430605) B2430605
theorem B1620419 : Blo 1619008 1620419 := bstep (se 1 (by rfl) ⟨1215314, by rfl⟩ : syracuseStep 1620419 = 2430629) B2430629
theorem B2431427 : Blo 1619008 2431427 := bstep (se 1 (by rfl) ⟨1823570, by rfl⟩ : syracuseStep 2431427 = 3647141) B3647141
theorem B6568397 : Blo 1619008 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B4102609 : Blo 1619008 4102609 := bstep (se 2 (by rfl) ⟨1538478, by rfl⟩ : syracuseStep 4102609 = 3076957) B3076957
theorem B1620435 : Blo 1619008 1620435 := bstep (se 1 (by rfl) ⟨1215326, by rfl⟩ : syracuseStep 1620435 = 2430653) B2430653
theorem B2431457 : Blo 1619008 2431457 := bstep (se 2 (by rfl) ⟨911796, by rfl⟩ : syracuseStep 2431457 = 1823593) B1823593
theorem B1620451 : Blo 1619008 1620451 := bstep (se 1 (by rfl) ⟨1215338, by rfl⟩ : syracuseStep 1620451 = 2430677) B2430677
theorem B19470833 : Blo 1619008 19470833 := bstep (se 2 (by rfl) ⟨7301562, by rfl⟩ : syracuseStep 19470833 = 14603125) B14603125
theorem B1620467 : Blo 1619008 1620467 := bstep (se 1 (by rfl) ⟨1215350, by rfl⟩ : syracuseStep 1620467 = 2430701) B2430701
theorem B2431475 : Blo 1619008 2431475 := bstep (se 1 (by rfl) ⟨1823606, by rfl⟩ : syracuseStep 2431475 = 3647213) B3647213
theorem B2595331 : Blo 1619008 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B1620483 : Blo 1619008 1620483 := bstep (se 1 (by rfl) ⟨1215362, by rfl⟩ : syracuseStep 1620483 = 2430725) B2430725
theorem B2464273 : Blo 1619008 2464273 := bstep (se 2 (by rfl) ⟨924102, by rfl⟩ : syracuseStep 2464273 = 1848205) B1848205
theorem B1620499 : Blo 1619008 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B2431505 : Blo 1619008 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B1620515 : Blo 1619008 1620515 := bstep (se 1 (by rfl) ⟨1215386, by rfl⟩ : syracuseStep 1620515 = 2430773) B2430773
theorem B2734627 : Blo 1619008 2734627 := bstep (se 1 (by rfl) ⟨2050970, by rfl⟩ : syracuseStep 2734627 = 4101941) B4101941
theorem B1620531 : Blo 1619008 1620531 := bstep (se 1 (by rfl) ⟨1215398, by rfl⟩ : syracuseStep 1620531 = 2430797) B2430797
theorem B1620547 : Blo 1619008 1620547 := bstep (se 1 (by rfl) ⟨1215410, by rfl⟩ : syracuseStep 1620547 = 2430821) B2430821
theorem B4610641 : Blo 1619008 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B1620563 : Blo 1619008 1620563 := bstep (se 1 (by rfl) ⟨1215422, by rfl⟩ : syracuseStep 1620563 = 2430845) B2430845
theorem B6150755 : Blo 1619008 6150755 := bstep (se 1 (by rfl) ⟨4613066, by rfl⟩ : syracuseStep 6150755 = 9226133) B9226133
theorem B1620579 : Blo 1619008 1620579 := bstep (se 1 (by rfl) ⟨1215434, by rfl⟩ : syracuseStep 1620579 = 2430869) B2430869
theorem B1620595 : Blo 1619008 1620595 := bstep (se 1 (by rfl) ⟨1215446, by rfl⟩ : syracuseStep 1620595 = 2430893) B2430893
theorem B1620611 : Blo 1619008 1620611 := bstep (se 1 (by rfl) ⟨1215458, by rfl⟩ : syracuseStep 1620611 = 2430917) B2430917
theorem B1620627 : Blo 1619008 1620627 := bstep (se 1 (by rfl) ⟨1215470, by rfl⟩ : syracuseStep 1620627 = 2430941) B2430941
theorem B8198819 : Blo 1619008 8198819 := bstep (se 1 (by rfl) ⟨6149114, by rfl⟩ : syracuseStep 8198819 = 12298229) B12298229
theorem B2595491 : Blo 1619008 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B1620643 : Blo 1619008 1620643 := bstep (se 1 (by rfl) ⟨1215482, by rfl⟩ : syracuseStep 1620643 = 2430965) B2430965
theorem B3644081 : Blo 1619008 3644081 := bstep (se 2 (by rfl) ⟨1366530, by rfl⟩ : syracuseStep 3644081 = 2733061) B2733061
theorem B2734769 : Blo 1619008 2734769 := bstep (se 2 (by rfl) ⟨1025538, by rfl⟩ : syracuseStep 2734769 = 2051077) B2051077
theorem B1620659 : Blo 1619008 1620659 := bstep (se 1 (by rfl) ⟨1215494, by rfl⟩ : syracuseStep 1620659 = 2430989) B2430989
theorem B3644099 : Blo 1619008 3644099 := bstep (se 1 (by rfl) ⟨2733074, by rfl⟩ : syracuseStep 3644099 = 5466149) B5466149
theorem B1620675 : Blo 1619008 1620675 := bstep (se 1 (by rfl) ⟨1215506, by rfl⟩ : syracuseStep 1620675 = 2431013) B2431013
theorem B1620691 : Blo 1619008 1620691 := bstep (se 1 (by rfl) ⟨1215518, by rfl⟩ : syracuseStep 1620691 = 2431037) B2431037
theorem B1620707 : Blo 1619008 1620707 := bstep (se 1 (by rfl) ⟨1215530, by rfl⟩ : syracuseStep 1620707 = 2431061) B2431061
theorem B4102883 : Blo 1619008 4102883 := bstep (se 1 (by rfl) ⟨3077162, by rfl⟩ : syracuseStep 4102883 = 6154325) B6154325
theorem B12303089 : Blo 1619008 12303089 := bstep (se 2 (by rfl) ⟨4613658, by rfl⟩ : syracuseStep 12303089 = 9227317) B9227317
theorem B1620723 : Blo 1619008 1620723 := bstep (se 1 (by rfl) ⟨1215542, by rfl⟩ : syracuseStep 1620723 = 2431085) B2431085
theorem B1620739 : Blo 1619008 1620739 := bstep (se 1 (by rfl) ⟨1215554, by rfl⟩ : syracuseStep 1620739 = 2431109) B2431109
theorem B1620755 : Blo 1619008 1620755 := bstep (se 1 (by rfl) ⟨1215566, by rfl⟩ : syracuseStep 1620755 = 2431133) B2431133
theorem B1620771 : Blo 1619008 1620771 := bstep (se 1 (by rfl) ⟨1215578, by rfl⟩ : syracuseStep 1620771 = 2431157) B2431157
theorem B2734897 : Blo 1619008 2734897 := bstep (se 2 (by rfl) ⟨1025586, by rfl⟩ : syracuseStep 2734897 = 2051173) B2051173
theorem B1620787 : Blo 1619008 1620787 := bstep (se 1 (by rfl) ⟨1215590, by rfl⟩ : syracuseStep 1620787 = 2431181) B2431181
theorem B1620803 : Blo 1619008 1620803 := bstep (se 1 (by rfl) ⟨1215602, by rfl⟩ : syracuseStep 1620803 = 2431205) B2431205
theorem B2734931 : Blo 1619008 2734931 := bstep (se 1 (by rfl) ⟨2051198, by rfl⟩ : syracuseStep 2734931 = 4102397) B4102397
theorem B1620819 : Blo 1619008 1620819 := bstep (se 1 (by rfl) ⟨1215614, by rfl⟩ : syracuseStep 1620819 = 2431229) B2431229
theorem B4610915 : Blo 1619008 4610915 := bstep (se 1 (by rfl) ⟨3458186, by rfl⟩ : syracuseStep 4610915 = 6916373) B6916373
theorem B1620835 : Blo 1619008 1620835 := bstep (se 1 (by rfl) ⟨1215626, by rfl⟩ : syracuseStep 1620835 = 2431253) B2431253
theorem B1620851 : Blo 1619008 1620851 := bstep (se 1 (by rfl) ⟨1215638, by rfl⟩ : syracuseStep 1620851 = 2431277) B2431277
theorem B1620867 : Blo 1619008 1620867 := bstep (se 1 (by rfl) ⟨1215650, by rfl⟩ : syracuseStep 1620867 = 2431301) B2431301
theorem B1620883 : Blo 1619008 1620883 := bstep (se 1 (by rfl) ⟨1215662, by rfl⟩ : syracuseStep 1620883 = 2431325) B2431325
theorem B1620899 : Blo 1619008 1620899 := bstep (se 1 (by rfl) ⟨1215674, by rfl⟩ : syracuseStep 1620899 = 2431349) B2431349
theorem B4103075 : Blo 1619008 4103075 := bstep (se 1 (by rfl) ⟨3077306, by rfl⟩ : syracuseStep 4103075 = 6154613) B6154613
theorem B1620915 : Blo 1619008 1620915 := bstep (se 1 (by rfl) ⟨1215686, by rfl⟩ : syracuseStep 1620915 = 2431373) B2431373
theorem B1620931 : Blo 1619008 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B3644369 : Blo 1619008 3644369 := bstep (se 2 (by rfl) ⟨1366638, by rfl⟩ : syracuseStep 3644369 = 2733277) B2733277
theorem B2735059 : Blo 1619008 2735059 := bstep (se 1 (by rfl) ⟨2051294, by rfl⟩ : syracuseStep 2735059 = 4102589) B4102589
theorem B1620947 : Blo 1619008 1620947 := bstep (se 1 (by rfl) ⟨1215710, by rfl⟩ : syracuseStep 1620947 = 2431421) B2431421
theorem B3644387 : Blo 1619008 3644387 := bstep (se 1 (by rfl) ⟨2733290, by rfl⟩ : syracuseStep 3644387 = 5466581) B5466581
theorem B1620963 : Blo 1619008 1620963 := bstep (se 1 (by rfl) ⟨1215722, by rfl⟩ : syracuseStep 1620963 = 2431445) B2431445
theorem B10517489 : Blo 1619008 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B1620979 : Blo 1619008 1620979 := bstep (se 1 (by rfl) ⟨1215734, by rfl⟩ : syracuseStep 1620979 = 2431469) B2431469
theorem B1620995 : Blo 1619008 1620995 := bstep (se 1 (by rfl) ⟨1215746, by rfl⟩ : syracuseStep 1620995 = 2431493) B2431493
theorem B3505169 : Blo 1619008 3505169 := bstep (se 2 (by rfl) ⟨1314438, by rfl⟩ : syracuseStep 3505169 = 2628877) B2628877
theorem B4611107 : Blo 1619008 4611107 := bstep (se 1 (by rfl) ⟨3458330, by rfl⟩ : syracuseStep 4611107 = 6916661) B6916661
theorem B9223217 : Blo 1619008 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B2735201 : Blo 1619008 2735201 := bstep (se 2 (by rfl) ⟨1025700, by rfl⟩ : syracuseStep 2735201 = 2051401) B2051401
theorem B11238533 : Blo 1619008 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B2735329 : Blo 1619008 2735329 := bstep (se 2 (by rfl) ⟨1025748, by rfl⟩ : syracuseStep 2735329 = 2051497) B2051497
theorem B3644657 : Blo 1619008 3644657 := bstep (se 2 (by rfl) ⟨1366746, by rfl⟩ : syracuseStep 3644657 = 2733493) B2733493
theorem B6151409 : Blo 1619008 6151409 := bstep (se 2 (by rfl) ⟨2306778, by rfl⟩ : syracuseStep 6151409 = 4613557) B4613557
theorem B3644675 : Blo 1619008 3644675 := bstep (se 1 (by rfl) ⟨2733506, by rfl⟩ : syracuseStep 3644675 = 5467013) B5467013
theorem B2735363 : Blo 1619008 2735363 := bstep (se 1 (by rfl) ⟨2051522, by rfl⟩ : syracuseStep 2735363 = 4103045) B4103045
theorem B2497873 : Blo 1619008 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B8314211 : Blo 1619008 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B8199629 : Blo 1619008 8199629 := bstep (se 3 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 8199629 = 3074861) B3074861
theorem B3644945 : Blo 1619008 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B5545489 : Blo 1619008 5545489 := bstep (se 2 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 5545489 = 4159117) B4159117
theorem B3644963 : Blo 1619008 3644963 := bstep (se 1 (by rfl) ⟨2733722, by rfl⟩ : syracuseStep 3644963 = 5467445) B5467445
theorem B24952373 : Blo 1619008 24952373 := bstep (se 5 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 24952373 = 2339285) B2339285
theorem B2596465 : Blo 1619008 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B6569741 : Blo 1619008 6569741 := bstep (se 3 (by rfl) ⟨1231826, by rfl⟩ : syracuseStep 6569741 = 2463653) B2463653
theorem B3645233 : Blo 1619008 3645233 := bstep (se 2 (by rfl) ⟨1366962, by rfl⟩ : syracuseStep 3645233 = 2733925) B2733925
theorem B3645251 : Blo 1619008 3645251 := bstep (se 1 (by rfl) ⟨2733938, by rfl⟩ : syracuseStep 3645251 = 5467877) B5467877
theorem B4611917 : Blo 1619008 4611917 := bstep (se 3 (by rfl) ⟨864734, by rfl⟩ : syracuseStep 4611917 = 1729469) B1729469
theorem B6922061 : Blo 1619008 6922061 := bstep (se 3 (by rfl) ⟨1297886, by rfl⟩ : syracuseStep 6922061 = 2595773) B2595773
theorem B1752931 : Blo 1619008 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B9846755 : Blo 1619008 9846755 := bstep (se 1 (by rfl) ⟨7385066, by rfl⟩ : syracuseStep 9846755 = 14770133) B14770133
theorem B17514467 : Blo 1619008 17514467 := bstep (se 1 (by rfl) ⟨13135850, by rfl⟩ : syracuseStep 17514467 = 26271701) B26271701
theorem B3284977 : Blo 1619008 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B3694657 : Blo 1619008 3694657 := bstep (se 2 (by rfl) ⟨1385496, by rfl⟩ : syracuseStep 3694657 = 2770993) B2770993
theorem B12296285 : Blo 1619008 12296285 := bstep (se 3 (by rfl) ⟨2305553, by rfl⟩ : syracuseStep 12296285 = 4611107) B4611107
theorem B4612247 : Blo 1619008 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B3645593 : Blo 1619008 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B6316211 : Blo 1619008 6316211 := bstep (se 1 (by rfl) ⟨4737158, by rfl⟩ : syracuseStep 6316211 = 9474317) B9474317
theorem B6152395 : Blo 1619008 6152395 := bstep (se 1 (by rfl) ⟨4614296, by rfl⟩ : syracuseStep 6152395 = 9228593) B9228593
theorem B3645683 : Blo 1619008 3645683 := bstep (se 1 (by rfl) ⟨2734262, by rfl⟩ : syracuseStep 3645683 = 5468525) B5468525
theorem B3203329 : Blo 1619008 3203329 := bstep (se 2 (by rfl) ⟨1201248, by rfl⟩ : syracuseStep 3203329 = 2402497) B2402497
theorem B7389463 : Blo 1619008 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B3645719 : Blo 1619008 3645719 := bstep (se 1 (by rfl) ⟨2734289, by rfl⟩ : syracuseStep 3645719 = 5468579) B5468579
theorem B5841227 : Blo 1619008 5841227 := bstep (se 1 (by rfl) ⟨4380920, by rfl⟩ : syracuseStep 5841227 = 8761841) B8761841
theorem B3891545 : Blo 1619008 3891545 := bstep (se 2 (by rfl) ⟨1459329, by rfl⟩ : syracuseStep 3891545 = 2918659) B2918659
theorem B6922675 : Blo 1619008 6922675 := bstep (se 1 (by rfl) ⟨5192006, by rfl⟩ : syracuseStep 6922675 = 10384013) B10384013
theorem B3645899 : Blo 1619008 3645899 := bstep (se 1 (by rfl) ⟨2734424, by rfl⟩ : syracuseStep 3645899 = 5468849) B5468849
theorem B5841355 : Blo 1619008 5841355 := bstep (se 1 (by rfl) ⟨4381016, by rfl⟩ : syracuseStep 5841355 = 8762033) B8762033
theorem B6152669 : Blo 1619008 6152669 := bstep (se 3 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 6152669 = 2307251) B2307251
theorem B3645953 : Blo 1619008 3645953 := bstep (se 2 (by rfl) ⟨1367232, by rfl⟩ : syracuseStep 3645953 = 2734465) B2734465
theorem B3285697 : Blo 1619008 3285697 := bstep (se 2 (by rfl) ⟨1232136, by rfl⟩ : syracuseStep 3285697 = 2464273) B2464273
theorem B3646169 : Blo 1619008 3646169 := bstep (se 2 (by rfl) ⟨1367313, by rfl⟩ : syracuseStep 3646169 = 2734627) B2734627
theorem B14033699 : Blo 1619008 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B3646259 : Blo 1619008 3646259 := bstep (se 1 (by rfl) ⟨2734694, by rfl⟩ : syracuseStep 3646259 = 5469389) B5469389
theorem B5464907 : Blo 1619008 5464907 := bstep (se 1 (by rfl) ⟨4098680, by rfl⟩ : syracuseStep 5464907 = 8197361) B8197361
theorem B3646295 : Blo 1619008 3646295 := bstep (se 1 (by rfl) ⟨2734721, by rfl⟩ : syracuseStep 3646295 = 5469443) B5469443
theorem B50561891 : Blo 1619008 50561891 := bstep (se 1 (by rfl) ⟨37921418, by rfl⟩ : syracuseStep 50561891 = 75842837) B75842837
theorem B8111027 : Blo 1619008 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B3646475 : Blo 1619008 3646475 := bstep (se 1 (by rfl) ⟨2734856, by rfl⟩ : syracuseStep 3646475 = 5469713) B5469713
theorem B3646529 : Blo 1619008 3646529 := bstep (se 2 (by rfl) ⟨1367448, by rfl⟩ : syracuseStep 3646529 = 2734897) B2734897
theorem B5465177 : Blo 1619008 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B6153367 : Blo 1619008 6153367 := bstep (se 1 (by rfl) ⟨4615025, by rfl⟩ : syracuseStep 6153367 = 9230051) B9230051
theorem B6571201 : Blo 1619008 6571201 := bstep (se 2 (by rfl) ⟨2464200, by rfl⟩ : syracuseStep 6571201 = 4928401) B4928401
theorem B2049239 : Blo 1619008 2049239 := bstep (se 1 (by rfl) ⟨1536929, by rfl⟩ : syracuseStep 2049239 = 3073859) B3073859
theorem B9856217 : Blo 1619008 9856217 := bstep (se 2 (by rfl) ⟨3696081, by rfl⟩ : syracuseStep 9856217 = 7392163) B7392163
theorem B3646745 : Blo 1619008 3646745 := bstep (se 2 (by rfl) ⟨1367529, by rfl⟩ : syracuseStep 3646745 = 2735059) B2735059
theorem B11674925 : Blo 1619008 11674925 := bstep (se 3 (by rfl) ⟨2189048, by rfl⟩ : syracuseStep 11674925 = 4378097) B4378097
theorem B3646835 : Blo 1619008 3646835 := bstep (se 1 (by rfl) ⟨2735126, by rfl⟩ : syracuseStep 3646835 = 5470253) B5470253
theorem B3646871 : Blo 1619008 3646871 := bstep (se 1 (by rfl) ⟨2735153, by rfl⟩ : syracuseStep 3646871 = 5470307) B5470307
theorem B2917939 : Blo 1619008 2917939 := bstep (se 1 (by rfl) ⟨2188454, by rfl⟩ : syracuseStep 2917939 = 4376909) B4376909
theorem B3073601 : Blo 1619008 3073601 := bstep (se 2 (by rfl) ⟨1152600, by rfl⟩ : syracuseStep 3073601 = 2305201) B2305201
theorem B3647051 : Blo 1619008 3647051 := bstep (se 1 (by rfl) ⟨2735288, by rfl⟩ : syracuseStep 3647051 = 5470577) B5470577
theorem B7390813 : Blo 1619008 7390813 := bstep (se 3 (by rfl) ⟨1385777, by rfl⟩ : syracuseStep 7390813 = 2771555) B2771555
theorem B3647105 : Blo 1619008 3647105 := bstep (se 2 (by rfl) ⟨1367664, by rfl⟩ : syracuseStep 3647105 = 2735329) B2735329
theorem B9225859 : Blo 1619008 9225859 := bstep (se 1 (by rfl) ⟨6919394, by rfl⟩ : syracuseStep 9225859 = 13838789) B13838789
theorem B2918039 : Blo 1619008 2918039 := bstep (se 1 (by rfl) ⟨2188529, by rfl⟩ : syracuseStep 2918039 = 4377059) B4377059
theorem B23365361 : Blo 1619008 23365361 := bstep (se 2 (by rfl) ⟨8762010, by rfl⟩ : syracuseStep 23365361 = 17524021) B17524021
theorem B5916433 : Blo 1619008 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B5465879 : Blo 1619008 5465879 := bstep (se 1 (by rfl) ⟨4099409, by rfl⟩ : syracuseStep 5465879 = 8198819) B8198819
theorem B1730327 : Blo 1619008 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B10381121 : Blo 1619008 10381121 := bstep (se 2 (by rfl) ⟨3892920, by rfl⟩ : syracuseStep 10381121 = 7785841) B7785841
theorem B8202059 : Blo 1619008 8202059 := bstep (se 1 (by rfl) ⟨6151544, by rfl⟩ : syracuseStep 8202059 = 12303089) B12303089
theorem B9348965 : Blo 1619008 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B3073943 : Blo 1619008 3073943 := bstep (se 1 (by rfl) ⟨2305457, by rfl⟩ : syracuseStep 3073943 = 4610915) B4610915
theorem B2049943 : Blo 1619008 2049943 := bstep (se 1 (by rfl) ⟨1537457, by rfl⟩ : syracuseStep 2049943 = 3074915) B3074915
theorem B6916013 : Blo 1619008 6916013 := bstep (se 3 (by rfl) ⟨1296752, by rfl⟩ : syracuseStep 6916013 = 2593505) B2593505
theorem B6154157 : Blo 1619008 6154157 := bstep (se 3 (by rfl) ⟨1153904, by rfl⟩ : syracuseStep 6154157 = 2307809) B2307809
theorem B2336779 : Blo 1619008 2336779 := bstep (se 1 (by rfl) ⟨1752584, by rfl⟩ : syracuseStep 2336779 = 3505169) B3505169
theorem B5466419 : Blo 1619008 5466419 := bstep (se 1 (by rfl) ⟨4099814, by rfl⟩ : syracuseStep 5466419 = 8199629) B8199629
theorem B2771351 : Blo 1619008 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B3074611 : Blo 1619008 3074611 := bstep (se 1 (by rfl) ⟨2305958, by rfl⟩ : syracuseStep 3074611 = 4611917) B4611917
theorem B4614707 : Blo 1619008 4614707 := bstep (se 1 (by rfl) ⟨3461030, by rfl⟩ : syracuseStep 4614707 = 6922061) B6922061
theorem B5466689 : Blo 1619008 5466689 := bstep (se 2 (by rfl) ⟨2050008, by rfl⟩ : syracuseStep 5466689 = 4100017) B4100017
theorem B9226817 : Blo 1619008 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B6916697 : Blo 1619008 6916697 := bstep (se 2 (by rfl) ⟨2593761, by rfl⟩ : syracuseStep 6916697 = 5187523) B5187523
theorem B6564503 : Blo 1619008 6564503 := bstep (se 1 (by rfl) ⟨4923377, by rfl⟩ : syracuseStep 6564503 = 9846755) B9846755
theorem B11676311 : Blo 1619008 11676311 := bstep (se 1 (by rfl) ⟨8757233, by rfl⟩ : syracuseStep 11676311 = 17514467) B17514467
theorem B3459827 : Blo 1619008 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B1821451 : Blo 1619008 1821451 := bstep (se 1 (by rfl) ⟨1366088, by rfl⟩ : syracuseStep 1821451 = 2732177) B2732177
theorem B1641227 : Blo 1619008 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B2919179 : Blo 1619008 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B5188445 : Blo 1619008 5188445 := bstep (se 3 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 5188445 = 1945667) B1945667
theorem B1821559 : Blo 1619008 1821559 := bstep (se 1 (by rfl) ⟨1366169, by rfl⟩ : syracuseStep 1821559 = 2732339) B2732339
theorem B4926359 : Blo 1619008 4926359 := bstep (se 1 (by rfl) ⟨3694769, by rfl⟩ : syracuseStep 4926359 = 7389539) B7389539
theorem B4098995 : Blo 1619008 4098995 := bstep (se 1 (by rfl) ⟨3074246, by rfl⟩ : syracuseStep 4098995 = 6148493) B6148493
theorem B3075059 : Blo 1619008 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B3075097 : Blo 1619008 3075097 := bstep (se 2 (by rfl) ⟨1153161, by rfl⟩ : syracuseStep 3075097 = 2306323) B2306323
theorem B1821739 : Blo 1619008 1821739 := bstep (se 1 (by rfl) ⟨1366304, by rfl⟩ : syracuseStep 1821739 = 2732609) B2732609
theorem B5467229 : Blo 1619008 5467229 := bstep (se 3 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 5467229 = 2050211) B2050211
theorem B2919539 : Blo 1619008 2919539 := bstep (se 1 (by rfl) ⟨2189654, by rfl⟩ : syracuseStep 2919539 = 4379309) B4379309
theorem B1821847 : Blo 1619008 1821847 := bstep (se 1 (by rfl) ⟨1366385, by rfl⟩ : syracuseStep 1821847 = 2732771) B2732771
theorem B3460313 : Blo 1619008 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B1822027 : Blo 1619008 1822027 := bstep (se 1 (by rfl) ⟨1366520, by rfl⟩ : syracuseStep 1822027 = 2733041) B2733041
theorem B5541209 : Blo 1619008 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B18443699 : Blo 1619008 18443699 := bstep (se 1 (by rfl) ⟨13832774, by rfl⟩ : syracuseStep 18443699 = 27665549) B27665549
theorem B1822135 : Blo 1619008 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B6147521 : Blo 1619008 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B4099531 : Blo 1619008 4099531 := bstep (se 1 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 4099531 = 6149297) B6149297
theorem B2665931 : Blo 1619008 2665931 := bstep (se 1 (by rfl) ⟨1999448, by rfl⟩ : syracuseStep 2665931 = 3998897) B3998897
theorem B3075545 : Blo 1619008 3075545 := bstep (se 2 (by rfl) ⟨1153329, by rfl⟩ : syracuseStep 3075545 = 2306659) B2306659
theorem B8203841 : Blo 1619008 8203841 := bstep (se 2 (by rfl) ⟨3076440, by rfl⟩ : syracuseStep 8203841 = 6152881) B6152881
theorem B4099673 : Blo 1619008 4099673 := bstep (se 2 (by rfl) ⟨1537377, by rfl⟩ : syracuseStep 4099673 = 3074755) B3074755
theorem B22171229 : Blo 1619008 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1846891 : Blo 1619008 1846891 := bstep (se 1 (by rfl) ⟨1385168, by rfl⟩ : syracuseStep 1846891 = 2770337) B2770337
theorem B1822315 : Blo 1619008 1822315 := bstep (se 1 (by rfl) ⟨1366736, by rfl⟩ : syracuseStep 1822315 = 2733473) B2733473
theorem B2428619 : Blo 1619008 2428619 := bstep (se 1 (by rfl) ⟨1821464, by rfl⟩ : syracuseStep 2428619 = 3642929) B3642929
theorem B2428631 : Blo 1619008 2428631 := bstep (se 1 (by rfl) ⟨1821473, by rfl⟩ : syracuseStep 2428631 = 3642947) B3642947
theorem B1822423 : Blo 1619008 1822423 := bstep (se 1 (by rfl) ⟨1366817, by rfl⟩ : syracuseStep 1822423 = 2733635) B2733635
theorem B5189341 : Blo 1619008 5189341 := bstep (se 3 (by rfl) ⟨973001, by rfl⟩ : syracuseStep 5189341 = 1946003) B1946003
theorem B2428697 : Blo 1619008 2428697 := bstep (se 2 (by rfl) ⟨910761, by rfl⟩ : syracuseStep 2428697 = 1821523) B1821523
theorem B14020397 : Blo 1619008 14020397 := bstep (se 3 (by rfl) ⟨2628824, by rfl⟩ : syracuseStep 14020397 = 5257649) B5257649
theorem B3116875 : Blo 1619008 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B2428811 : Blo 1619008 2428811 := bstep (se 1 (by rfl) ⟨1821608, by rfl⟩ : syracuseStep 2428811 = 3643217) B3643217
theorem B1822603 : Blo 1619008 1822603 := bstep (se 1 (by rfl) ⟨1366952, by rfl⟩ : syracuseStep 1822603 = 2733905) B2733905
theorem B6000529 : Blo 1619008 6000529 := bstep (se 2 (by rfl) ⟨2250198, by rfl⟩ : syracuseStep 6000529 = 4500397) B4500397
theorem B2428823 : Blo 1619008 2428823 := bstep (se 1 (by rfl) ⟨1821617, by rfl⟩ : syracuseStep 2428823 = 3643235) B3643235
theorem B2428889 : Blo 1619008 2428889 := bstep (se 2 (by rfl) ⟨910833, by rfl⟩ : syracuseStep 2428889 = 1821667) B1821667
theorem B1822711 : Blo 1619008 1822711 := bstep (se 1 (by rfl) ⟨1367033, by rfl⟩ : syracuseStep 1822711 = 2734067) B2734067
theorem B13840429 : Blo 1619008 13840429 := bstep (se 3 (by rfl) ⟨2595080, by rfl⟩ : syracuseStep 13840429 = 5190161) B5190161
theorem B2429003 : Blo 1619008 2429003 := bstep (se 1 (by rfl) ⟨1821752, by rfl⟩ : syracuseStep 2429003 = 3643505) B3643505
theorem B2429015 : Blo 1619008 2429015 := bstep (se 1 (by rfl) ⟨1821761, by rfl⟩ : syracuseStep 2429015 = 3643523) B3643523
theorem B2429081 : Blo 1619008 2429081 := bstep (se 2 (by rfl) ⟨910905, by rfl⟩ : syracuseStep 2429081 = 1821811) B1821811
theorem B1822891 : Blo 1619008 1822891 := bstep (se 1 (by rfl) ⟨1367168, by rfl⟩ : syracuseStep 1822891 = 2734337) B2734337
theorem B3076289 : Blo 1619008 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B5468363 : Blo 1619008 5468363 := bstep (se 1 (by rfl) ⟨4101272, by rfl⟩ : syracuseStep 5468363 = 8202545) B8202545
theorem B6746329 : Blo 1619008 6746329 := bstep (se 2 (by rfl) ⟨2529873, by rfl⟩ : syracuseStep 6746329 = 5059747) B5059747
theorem B2429195 : Blo 1619008 2429195 := bstep (se 1 (by rfl) ⟨1821896, by rfl⟩ : syracuseStep 2429195 = 3643793) B3643793
theorem B2429207 : Blo 1619008 2429207 := bstep (se 1 (by rfl) ⟨1821905, by rfl⟩ : syracuseStep 2429207 = 3643811) B3643811
theorem B1822999 : Blo 1619008 1822999 := bstep (se 1 (by rfl) ⟨1367249, by rfl⟩ : syracuseStep 1822999 = 2734499) B2734499
theorem B4378931 : Blo 1619008 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B12980555 : Blo 1619008 12980555 := bstep (se 1 (by rfl) ⟨9735416, by rfl⟩ : syracuseStep 12980555 = 19470833) B19470833
theorem B2429273 : Blo 1619008 2429273 := bstep (se 2 (by rfl) ⟨910977, by rfl⟩ : syracuseStep 2429273 = 1821955) B1821955
theorem B4100503 : Blo 1619008 4100503 := bstep (se 1 (by rfl) ⟨3075377, by rfl⟩ : syracuseStep 4100503 = 6150755) B6150755
theorem B3330497 : Blo 1619008 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B2429387 : Blo 1619008 2429387 := bstep (se 1 (by rfl) ⟨1822040, by rfl⟩ : syracuseStep 2429387 = 3644081) B3644081
theorem B3076555 : Blo 1619008 3076555 := bstep (se 1 (by rfl) ⟨2307416, by rfl⟩ : syracuseStep 3076555 = 4614833) B4614833
theorem B1823179 : Blo 1619008 1823179 := bstep (se 1 (by rfl) ⟨1367384, by rfl⟩ : syracuseStep 1823179 = 2734769) B2734769
theorem B2429399 : Blo 1619008 2429399 := bstep (se 1 (by rfl) ⟨1822049, by rfl⟩ : syracuseStep 2429399 = 3644099) B3644099
theorem B5468633 : Blo 1619008 5468633 := bstep (se 2 (by rfl) ⟨2050737, by rfl⟩ : syracuseStep 5468633 = 4101475) B4101475
theorem B2732555 : Blo 1619008 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B2429465 : Blo 1619008 2429465 := bstep (se 2 (by rfl) ⟨911049, by rfl⟩ : syracuseStep 2429465 = 1822099) B1822099
theorem B1823287 : Blo 1619008 1823287 := bstep (se 1 (by rfl) ⟨1367465, by rfl⟩ : syracuseStep 1823287 = 2734931) B2734931
theorem B2306647 : Blo 1619008 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B2732683 : Blo 1619008 2732683 := bstep (se 1 (by rfl) ⟨2049512, by rfl⟩ : syracuseStep 2732683 = 4099025) B4099025
theorem B2429579 : Blo 1619008 2429579 := bstep (se 1 (by rfl) ⟨1822184, by rfl⟩ : syracuseStep 2429579 = 3644369) B3644369
theorem B2429591 : Blo 1619008 2429591 := bstep (se 1 (by rfl) ⟨1822193, by rfl⟩ : syracuseStep 2429591 = 3644387) B3644387
theorem B6148781 : Blo 1619008 6148781 := bstep (se 3 (by rfl) ⟨1152896, by rfl⟩ : syracuseStep 6148781 = 2305793) B2305793
theorem B7393985 : Blo 1619008 7393985 := bstep (se 2 (by rfl) ⟨2772744, by rfl⟩ : syracuseStep 7393985 = 5545489) B5545489
theorem B6148811 : Blo 1619008 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B2429657 : Blo 1619008 2429657 := bstep (se 2 (by rfl) ⟨911121, by rfl⟩ : syracuseStep 2429657 = 1822243) B1822243
theorem B1823467 : Blo 1619008 1823467 := bstep (se 1 (by rfl) ⟨1367600, by rfl⟩ : syracuseStep 1823467 = 2735201) B2735201
theorem B7492355 : Blo 1619008 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B2732825 : Blo 1619008 2732825 := bstep (se 2 (by rfl) ⟨1024809, by rfl⟩ : syracuseStep 2732825 = 2049619) B2049619
theorem B3461953 : Blo 1619008 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B2429771 : Blo 1619008 2429771 := bstep (se 1 (by rfl) ⟨1822328, by rfl⟩ : syracuseStep 2429771 = 3644657) B3644657
theorem B4100939 : Blo 1619008 4100939 := bstep (se 1 (by rfl) ⟨3075704, by rfl⟩ : syracuseStep 4100939 = 6151409) B6151409
theorem B2429783 : Blo 1619008 2429783 := bstep (se 1 (by rfl) ⟨1822337, by rfl⟩ : syracuseStep 2429783 = 3644675) B3644675
theorem B1823575 : Blo 1619008 1823575 := bstep (se 1 (by rfl) ⟨1367681, by rfl⟩ : syracuseStep 1823575 = 2735363) B2735363
theorem B18445157 : Blo 1619008 18445157 := bstep (se 4 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 18445157 = 3458467) B3458467
theorem B3077003 : Blo 1619008 3077003 := bstep (se 1 (by rfl) ⟨2307752, by rfl⟩ : syracuseStep 3077003 = 4615505) B4615505
theorem B2732953 : Blo 1619008 2732953 := bstep (se 2 (by rfl) ⟨1024857, by rfl⟩ : syracuseStep 2732953 = 2049715) B2049715
theorem B2429849 : Blo 1619008 2429849 := bstep (se 2 (by rfl) ⟨911193, by rfl⟩ : syracuseStep 2429849 = 1822387) B1822387
theorem B4928473 : Blo 1619008 4928473 := bstep (se 2 (by rfl) ⟨1848177, by rfl⟩ : syracuseStep 4928473 = 3696355) B3696355
theorem B2429963 : Blo 1619008 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B2429975 : Blo 1619008 2429975 := bstep (se 1 (by rfl) ⟨1822481, by rfl⟩ : syracuseStep 2429975 = 3644963) B3644963
theorem B56865827 : Blo 1619008 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B16634915 : Blo 1619008 16634915 := bstep (se 1 (by rfl) ⟨12476186, by rfl⟩ : syracuseStep 16634915 = 24952373) B24952373
theorem B3077185 : Blo 1619008 3077185 := bstep (se 2 (by rfl) ⟨1153944, by rfl⟩ : syracuseStep 3077185 = 2307889) B2307889
theorem B1619019 : Blo 1619008 1619019 := bstep (se 1 (by rfl) ⟨1214264, by rfl⟩ : syracuseStep 1619019 = 2428529) B2428529
theorem B1619031 : Blo 1619008 1619031 := bstep (se 1 (by rfl) ⟨1214273, by rfl⟩ : syracuseStep 1619031 = 2428547) B2428547
theorem B2430041 : Blo 1619008 2430041 := bstep (se 2 (by rfl) ⟨911265, by rfl⟩ : syracuseStep 2430041 = 1822531) B1822531
theorem B1619051 : Blo 1619008 1619051 := bstep (se 1 (by rfl) ⟨1214288, by rfl⟩ : syracuseStep 1619051 = 2428577) B2428577
theorem B1619063 : Blo 1619008 1619063 := bstep (se 1 (by rfl) ⟨1214297, by rfl⟩ : syracuseStep 1619063 = 2428595) B2428595
theorem B1619083 : Blo 1619008 1619083 := bstep (se 1 (by rfl) ⟨1214312, by rfl⟩ : syracuseStep 1619083 = 2428625) B2428625
theorem B1619095 : Blo 1619008 1619095 := bstep (se 1 (by rfl) ⟨1214321, by rfl⟩ : syracuseStep 1619095 = 2428643) B2428643
theorem B5469335 : Blo 1619008 5469335 := bstep (se 1 (by rfl) ⟨4102001, by rfl⟩ : syracuseStep 5469335 = 8204003) B8204003
theorem B1619115 : Blo 1619008 1619115 := bstep (se 1 (by rfl) ⟨1214336, by rfl⟩ : syracuseStep 1619115 = 2428673) B2428673
theorem B4379827 : Blo 1619008 4379827 := bstep (se 1 (by rfl) ⟨3284870, by rfl⟩ : syracuseStep 4379827 = 6569741) B6569741
theorem B1619127 : Blo 1619008 1619127 := bstep (se 1 (by rfl) ⟨1214345, by rfl⟩ : syracuseStep 1619127 = 2428691) B2428691
theorem B4101313 : Blo 1619008 4101313 := bstep (se 2 (by rfl) ⟨1537992, by rfl⟩ : syracuseStep 4101313 = 3075985) B3075985
theorem B1619147 : Blo 1619008 1619147 := bstep (se 1 (by rfl) ⟨1214360, by rfl⟩ : syracuseStep 1619147 = 2428721) B2428721
theorem B2430155 : Blo 1619008 2430155 := bstep (se 1 (by rfl) ⟨1822616, by rfl⟩ : syracuseStep 2430155 = 3645233) B3645233
theorem B1619159 : Blo 1619008 1619159 := bstep (se 1 (by rfl) ⟨1214369, by rfl⟩ : syracuseStep 1619159 = 2428739) B2428739
theorem B2430167 : Blo 1619008 2430167 := bstep (se 1 (by rfl) ⟨1822625, by rfl⟩ : syracuseStep 2430167 = 3645251) B3645251
theorem B1619179 : Blo 1619008 1619179 := bstep (se 1 (by rfl) ⟨1214384, by rfl⟩ : syracuseStep 1619179 = 2428769) B2428769
theorem B1619191 : Blo 1619008 1619191 := bstep (se 1 (by rfl) ⟨1214393, by rfl⟩ : syracuseStep 1619191 = 2428787) B2428787
theorem B1619211 : Blo 1619008 1619211 := bstep (se 1 (by rfl) ⟨1214408, by rfl⟩ : syracuseStep 1619211 = 2428817) B2428817
theorem B1619223 : Blo 1619008 1619223 := bstep (se 1 (by rfl) ⟨1214417, by rfl⟩ : syracuseStep 1619223 = 2428835) B2428835
theorem B2430233 : Blo 1619008 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B1619243 : Blo 1619008 1619243 := bstep (se 1 (by rfl) ⟨1214432, by rfl⟩ : syracuseStep 1619243 = 2428865) B2428865
theorem B1619255 : Blo 1619008 1619255 := bstep (se 1 (by rfl) ⟨1214441, by rfl⟩ : syracuseStep 1619255 = 2428883) B2428883
theorem B4379969 : Blo 1619008 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B1619275 : Blo 1619008 1619275 := bstep (se 1 (by rfl) ⟨1214456, by rfl⟩ : syracuseStep 1619275 = 2428913) B2428913
theorem B1619287 : Blo 1619008 1619287 := bstep (se 1 (by rfl) ⟨1214465, by rfl⟩ : syracuseStep 1619287 = 2428931) B2428931
theorem B6149465 : Blo 1619008 6149465 := bstep (se 2 (by rfl) ⟨2306049, by rfl⟩ : syracuseStep 6149465 = 4612099) B4612099
theorem B13309285 : Blo 1619008 13309285 := bstep (se 4 (by rfl) ⟨1247745, by rfl⟩ : syracuseStep 13309285 = 2495491) B2495491
theorem B13841765 : Blo 1619008 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B1619307 : Blo 1619008 1619307 := bstep (se 1 (by rfl) ⟨1214480, by rfl⟩ : syracuseStep 1619307 = 2428961) B2428961
theorem B1619319 : Blo 1619008 1619319 := bstep (se 1 (by rfl) ⟨1214489, by rfl⟩ : syracuseStep 1619319 = 2428979) B2428979
theorem B1619339 : Blo 1619008 1619339 := bstep (se 1 (by rfl) ⟨1214504, by rfl⟩ : syracuseStep 1619339 = 2429009) B2429009
theorem B2430347 : Blo 1619008 2430347 := bstep (se 1 (by rfl) ⟨1822760, by rfl⟩ : syracuseStep 2430347 = 3645521) B3645521
theorem B1619351 : Blo 1619008 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B2430359 : Blo 1619008 2430359 := bstep (se 1 (by rfl) ⟨1822769, by rfl⟩ : syracuseStep 2430359 = 3645539) B3645539
theorem B1619371 : Blo 1619008 1619371 := bstep (se 1 (by rfl) ⟨1214528, by rfl⟩ : syracuseStep 1619371 = 2429057) B2429057
theorem B3642803 : Blo 1619008 3642803 := bstep (se 1 (by rfl) ⟨2732102, by rfl⟩ : syracuseStep 3642803 = 5464205) B5464205
theorem B1619383 : Blo 1619008 1619383 := bstep (se 1 (by rfl) ⟨1214537, by rfl⟩ : syracuseStep 1619383 = 2429075) B2429075
theorem B1619403 : Blo 1619008 1619403 := bstep (se 1 (by rfl) ⟨1214552, by rfl⟩ : syracuseStep 1619403 = 2429105) B2429105
theorem B3642839 : Blo 1619008 3642839 := bstep (se 1 (by rfl) ⟨2732129, by rfl⟩ : syracuseStep 3642839 = 5464259) B5464259
theorem B1619415 : Blo 1619008 1619415 := bstep (se 1 (by rfl) ⟨1214561, by rfl⟩ : syracuseStep 1619415 = 2429123) B2429123
theorem B2733527 : Blo 1619008 2733527 := bstep (se 1 (by rfl) ⟨2050145, by rfl⟩ : syracuseStep 2733527 = 4100291) B4100291
theorem B2430425 : Blo 1619008 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B8205785 : Blo 1619008 8205785 := bstep (se 2 (by rfl) ⟨3077169, by rfl⟩ : syracuseStep 8205785 = 6154339) B6154339
theorem B1619435 : Blo 1619008 1619435 := bstep (se 1 (by rfl) ⟨1214576, by rfl⟩ : syracuseStep 1619435 = 2429153) B2429153
theorem B1619447 : Blo 1619008 1619447 := bstep (se 1 (by rfl) ⟨1214585, by rfl⟩ : syracuseStep 1619447 = 2429171) B2429171
theorem B1619467 : Blo 1619008 1619467 := bstep (se 1 (by rfl) ⟨1214600, by rfl⟩ : syracuseStep 1619467 = 2429201) B2429201
theorem B1619479 : Blo 1619008 1619479 := bstep (se 1 (by rfl) ⟨1214609, by rfl⟩ : syracuseStep 1619479 = 2429219) B2429219
theorem B1619499 : Blo 1619008 1619499 := bstep (se 1 (by rfl) ⟨1214624, by rfl⟩ : syracuseStep 1619499 = 2429249) B2429249
theorem B1619511 : Blo 1619008 1619511 := bstep (se 1 (by rfl) ⟨1214633, by rfl⟩ : syracuseStep 1619511 = 2429267) B2429267
theorem B1619531 : Blo 1619008 1619531 := bstep (se 1 (by rfl) ⟨1214648, by rfl⟩ : syracuseStep 1619531 = 2429297) B2429297
theorem B2430539 : Blo 1619008 2430539 := bstep (se 1 (by rfl) ⟨1822904, by rfl⟩ : syracuseStep 2430539 = 3645809) B3645809
theorem B1619543 : Blo 1619008 1619543 := bstep (se 1 (by rfl) ⟨1214657, by rfl⟩ : syracuseStep 1619543 = 2429315) B2429315
theorem B2733655 : Blo 1619008 2733655 := bstep (se 1 (by rfl) ⟨2050241, by rfl⟩ : syracuseStep 2733655 = 4100483) B4100483
theorem B2430551 : Blo 1619008 2430551 := bstep (se 1 (by rfl) ⟨1822913, by rfl⟩ : syracuseStep 2430551 = 3645827) B3645827
theorem B1619563 : Blo 1619008 1619563 := bstep (se 1 (by rfl) ⟨1214672, by rfl⟩ : syracuseStep 1619563 = 2429345) B2429345
theorem B1619575 : Blo 1619008 1619575 := bstep (se 1 (by rfl) ⟨1214681, by rfl⟩ : syracuseStep 1619575 = 2429363) B2429363
theorem B3643019 : Blo 1619008 3643019 := bstep (se 1 (by rfl) ⟨2732264, by rfl⟩ : syracuseStep 3643019 = 5464529) B5464529
theorem B1619595 : Blo 1619008 1619595 := bstep (se 1 (by rfl) ⟨1214696, by rfl⟩ : syracuseStep 1619595 = 2429393) B2429393
theorem B1619607 : Blo 1619008 1619607 := bstep (se 1 (by rfl) ⟨1214705, by rfl⟩ : syracuseStep 1619607 = 2429411) B2429411
theorem B6149783 : Blo 1619008 6149783 := bstep (se 1 (by rfl) ⟨4612337, by rfl⟩ : syracuseStep 6149783 = 9224675) B9224675
theorem B2430617 : Blo 1619008 2430617 := bstep (se 2 (by rfl) ⟨911481, by rfl⟩ : syracuseStep 2430617 = 1822963) B1822963
theorem B1619627 : Blo 1619008 1619627 := bstep (se 1 (by rfl) ⟨1214720, by rfl⟩ : syracuseStep 1619627 = 2429441) B2429441
theorem B5469875 : Blo 1619008 5469875 := bstep (se 1 (by rfl) ⟨4102406, by rfl⟩ : syracuseStep 5469875 = 8204813) B8204813
theorem B1619639 : Blo 1619008 1619639 := bstep (se 1 (by rfl) ⟨1214729, by rfl⟩ : syracuseStep 1619639 = 2429459) B2429459
theorem B3643073 : Blo 1619008 3643073 := bstep (se 2 (by rfl) ⟨1366152, by rfl⟩ : syracuseStep 3643073 = 2732305) B2732305
theorem B1619659 : Blo 1619008 1619659 := bstep (se 1 (by rfl) ⟨1214744, by rfl⟩ : syracuseStep 1619659 = 2429489) B2429489
theorem B1619671 : Blo 1619008 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B1619691 : Blo 1619008 1619691 := bstep (se 1 (by rfl) ⟨1214768, by rfl⟩ : syracuseStep 1619691 = 2429537) B2429537
theorem B1619703 : Blo 1619008 1619703 := bstep (se 1 (by rfl) ⟨1214777, by rfl⟩ : syracuseStep 1619703 = 2429555) B2429555
theorem B1619723 : Blo 1619008 1619723 := bstep (se 1 (by rfl) ⟨1214792, by rfl⟩ : syracuseStep 1619723 = 2429585) B2429585
theorem B2430731 : Blo 1619008 2430731 := bstep (se 1 (by rfl) ⟨1823048, by rfl⟩ : syracuseStep 2430731 = 3646097) B3646097
theorem B1619735 : Blo 1619008 1619735 := bstep (se 1 (by rfl) ⟨1214801, by rfl⟩ : syracuseStep 1619735 = 2429603) B2429603
theorem B2430743 : Blo 1619008 2430743 := bstep (se 1 (by rfl) ⟨1823057, by rfl⟩ : syracuseStep 2430743 = 3646115) B3646115
theorem B4101911 : Blo 1619008 4101911 := bstep (se 1 (by rfl) ⟨3076433, by rfl⟩ : syracuseStep 4101911 = 6152867) B6152867
theorem B1619755 : Blo 1619008 1619755 := bstep (se 1 (by rfl) ⟨1214816, by rfl⟩ : syracuseStep 1619755 = 2429633) B2429633
theorem B1619767 : Blo 1619008 1619767 := bstep (se 1 (by rfl) ⟨1214825, by rfl⟩ : syracuseStep 1619767 = 2429651) B2429651
theorem B1619787 : Blo 1619008 1619787 := bstep (se 1 (by rfl) ⟨1214840, by rfl⟩ : syracuseStep 1619787 = 2429681) B2429681
theorem B1619799 : Blo 1619008 1619799 := bstep (se 1 (by rfl) ⟨1214849, by rfl⟩ : syracuseStep 1619799 = 2429699) B2429699
theorem B2430809 : Blo 1619008 2430809 := bstep (se 2 (by rfl) ⟨911553, by rfl⟩ : syracuseStep 2430809 = 1823107) B1823107
theorem B31135589 : Blo 1619008 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B1619819 : Blo 1619008 1619819 := bstep (se 1 (by rfl) ⟨1214864, by rfl⟩ : syracuseStep 1619819 = 2429729) B2429729
theorem B1619831 : Blo 1619008 1619831 := bstep (se 1 (by rfl) ⟨1214873, by rfl⟩ : syracuseStep 1619831 = 2429747) B2429747
theorem B1619851 : Blo 1619008 1619851 := bstep (se 1 (by rfl) ⟨1214888, by rfl⟩ : syracuseStep 1619851 = 2429777) B2429777
theorem B1619863 : Blo 1619008 1619863 := bstep (se 1 (by rfl) ⟨1214897, by rfl⟩ : syracuseStep 1619863 = 2429795) B2429795
theorem B3643289 : Blo 1619008 3643289 := bstep (se 2 (by rfl) ⟨1366233, by rfl⟩ : syracuseStep 3643289 = 2732467) B2732467
theorem B1619883 : Blo 1619008 1619883 := bstep (se 1 (by rfl) ⟨1214912, by rfl⟩ : syracuseStep 1619883 = 2429825) B2429825
theorem B1619895 : Blo 1619008 1619895 := bstep (se 1 (by rfl) ⟨1214921, by rfl⟩ : syracuseStep 1619895 = 2429843) B2429843
theorem B5470145 : Blo 1619008 5470145 := bstep (se 2 (by rfl) ⟨2051304, by rfl⟩ : syracuseStep 5470145 = 4102609) B4102609
theorem B1619915 : Blo 1619008 1619915 := bstep (se 1 (by rfl) ⟨1214936, by rfl⟩ : syracuseStep 1619915 = 2429873) B2429873
theorem B2430923 : Blo 1619008 2430923 := bstep (se 1 (by rfl) ⟨1823192, by rfl⟩ : syracuseStep 2430923 = 3646385) B3646385
theorem B1619927 : Blo 1619008 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B2430935 : Blo 1619008 2430935 := bstep (se 1 (by rfl) ⟨1823201, by rfl⟩ : syracuseStep 2430935 = 3646403) B3646403
theorem B1619947 : Blo 1619008 1619947 := bstep (se 1 (by rfl) ⟨1214960, by rfl⟩ : syracuseStep 1619947 = 2429921) B2429921
theorem B3643379 : Blo 1619008 3643379 := bstep (se 1 (by rfl) ⟨2732534, by rfl⟩ : syracuseStep 3643379 = 5465069) B5465069
theorem B1619959 : Blo 1619008 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B7018499 : Blo 1619008 7018499 := bstep (se 1 (by rfl) ⟨5263874, by rfl⟩ : syracuseStep 7018499 = 10527749) B10527749
theorem B1619979 : Blo 1619008 1619979 := bstep (se 1 (by rfl) ⟨1214984, by rfl⟩ : syracuseStep 1619979 = 2429969) B2429969
theorem B3643415 : Blo 1619008 3643415 := bstep (se 1 (by rfl) ⟨2732561, by rfl⟩ : syracuseStep 3643415 = 5465123) B5465123
theorem B1619991 : Blo 1619008 1619991 := bstep (se 1 (by rfl) ⟨1214993, by rfl⟩ : syracuseStep 1619991 = 2429987) B2429987
theorem B2431001 : Blo 1619008 2431001 := bstep (se 2 (by rfl) ⟨911625, by rfl⟩ : syracuseStep 2431001 = 1823251) B1823251
theorem B1620011 : Blo 1619008 1620011 := bstep (se 1 (by rfl) ⟨1215008, by rfl⟩ : syracuseStep 1620011 = 2430017) B2430017
theorem B1620023 : Blo 1619008 1620023 := bstep (se 1 (by rfl) ⟨1215017, by rfl⟩ : syracuseStep 1620023 = 2430035) B2430035
theorem B1620043 : Blo 1619008 1620043 := bstep (se 1 (by rfl) ⟨1215032, by rfl⟩ : syracuseStep 1620043 = 2430065) B2430065
theorem B1620055 : Blo 1619008 1620055 := bstep (se 1 (by rfl) ⟨1215041, by rfl⟩ : syracuseStep 1620055 = 2430083) B2430083
theorem B1620075 : Blo 1619008 1620075 := bstep (se 1 (by rfl) ⟨1215056, by rfl⟩ : syracuseStep 1620075 = 2430113) B2430113
theorem B1620087 : Blo 1619008 1620087 := bstep (se 1 (by rfl) ⟨1215065, by rfl⟩ : syracuseStep 1620087 = 2430131) B2430131
theorem B1620107 : Blo 1619008 1620107 := bstep (se 1 (by rfl) ⟨1215080, by rfl⟩ : syracuseStep 1620107 = 2430161) B2430161
theorem B2463883 : Blo 1619008 2463883 := bstep (se 1 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 2463883 = 3695825) B3695825
theorem B2431115 : Blo 1619008 2431115 := bstep (se 1 (by rfl) ⟨1823336, by rfl⟩ : syracuseStep 2431115 = 3646673) B3646673
theorem B1620119 : Blo 1619008 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B2431127 : Blo 1619008 2431127 := bstep (se 1 (by rfl) ⟨1823345, by rfl⟩ : syracuseStep 2431127 = 3646691) B3646691
theorem B1620139 : Blo 1619008 1620139 := bstep (se 1 (by rfl) ⟨1215104, by rfl⟩ : syracuseStep 1620139 = 2430209) B2430209
theorem B1620151 : Blo 1619008 1620151 := bstep (se 1 (by rfl) ⟨1215113, by rfl⟩ : syracuseStep 1620151 = 2430227) B2430227
theorem B3643595 : Blo 1619008 3643595 := bstep (se 1 (by rfl) ⟨2732696, by rfl⟩ : syracuseStep 3643595 = 5465393) B5465393
theorem B1620171 : Blo 1619008 1620171 := bstep (se 1 (by rfl) ⟨1215128, by rfl⟩ : syracuseStep 1620171 = 2430257) B2430257
theorem B2734283 : Blo 1619008 2734283 := bstep (se 1 (by rfl) ⟨2050712, by rfl⟩ : syracuseStep 2734283 = 4101425) B4101425
theorem B1620183 : Blo 1619008 1620183 := bstep (se 1 (by rfl) ⟨1215137, by rfl⟩ : syracuseStep 1620183 = 2430275) B2430275
theorem B2431193 : Blo 1619008 2431193 := bstep (se 2 (by rfl) ⟨911697, by rfl⟩ : syracuseStep 2431193 = 1823395) B1823395
theorem B1620203 : Blo 1619008 1620203 := bstep (se 1 (by rfl) ⟨1215152, by rfl⟩ : syracuseStep 1620203 = 2430305) B2430305
theorem B1620215 : Blo 1619008 1620215 := bstep (se 1 (by rfl) ⟨1215161, by rfl⟩ : syracuseStep 1620215 = 2430323) B2430323
theorem B3643649 : Blo 1619008 3643649 := bstep (se 2 (by rfl) ⟨1366368, by rfl⟩ : syracuseStep 3643649 = 2732737) B2732737
theorem B1620235 : Blo 1619008 1620235 := bstep (se 1 (by rfl) ⟨1215176, by rfl⟩ : syracuseStep 1620235 = 2430353) B2430353
theorem B1620247 : Blo 1619008 1620247 := bstep (se 1 (by rfl) ⟨1215185, by rfl⟩ : syracuseStep 1620247 = 2430371) B2430371
theorem B1620267 : Blo 1619008 1620267 := bstep (se 1 (by rfl) ⟨1215200, by rfl⟩ : syracuseStep 1620267 = 2430401) B2430401
theorem B6150451 : Blo 1619008 6150451 := bstep (se 1 (by rfl) ⟨4612838, by rfl⟩ : syracuseStep 6150451 = 9225677) B9225677
theorem B1620279 : Blo 1619008 1620279 := bstep (se 1 (by rfl) ⟨1215209, by rfl⟩ : syracuseStep 1620279 = 2430419) B2430419
theorem B1620299 : Blo 1619008 1620299 := bstep (se 1 (by rfl) ⟨1215224, by rfl⟩ : syracuseStep 1620299 = 2430449) B2430449
theorem B2734411 : Blo 1619008 2734411 := bstep (se 1 (by rfl) ⟨2050808, by rfl⟩ : syracuseStep 2734411 = 4101617) B4101617
theorem B2431307 : Blo 1619008 2431307 := bstep (se 1 (by rfl) ⟨1823480, by rfl⟩ : syracuseStep 2431307 = 3646961) B3646961
theorem B1620311 : Blo 1619008 1620311 := bstep (se 1 (by rfl) ⟨1215233, by rfl⟩ : syracuseStep 1620311 = 2430467) B2430467
theorem B2431319 : Blo 1619008 2431319 := bstep (se 1 (by rfl) ⟨1823489, by rfl⟩ : syracuseStep 2431319 = 3646979) B3646979
theorem B1620331 : Blo 1619008 1620331 := bstep (se 1 (by rfl) ⟨1215248, by rfl⟩ : syracuseStep 1620331 = 2430497) B2430497
theorem B1620343 : Blo 1619008 1620343 := bstep (se 1 (by rfl) ⟨1215257, by rfl⟩ : syracuseStep 1620343 = 2430515) B2430515
theorem B1620363 : Blo 1619008 1620363 := bstep (se 1 (by rfl) ⟨1215272, by rfl⟩ : syracuseStep 1620363 = 2430545) B2430545
theorem B1620375 : Blo 1619008 1620375 := bstep (se 1 (by rfl) ⟨1215281, by rfl⟩ : syracuseStep 1620375 = 2430563) B2430563
theorem B2431385 : Blo 1619008 2431385 := bstep (se 2 (by rfl) ⟨911769, by rfl⟩ : syracuseStep 2431385 = 1823539) B1823539
theorem B1620395 : Blo 1619008 1620395 := bstep (se 1 (by rfl) ⟨1215296, by rfl⟩ : syracuseStep 1620395 = 2430593) B2430593
theorem B1620407 : Blo 1619008 1620407 := bstep (se 1 (by rfl) ⟨1215305, by rfl⟩ : syracuseStep 1620407 = 2430611) B2430611
theorem B1620427 : Blo 1619008 1620427 := bstep (se 1 (by rfl) ⟨1215320, by rfl⟩ : syracuseStep 1620427 = 2430641) B2430641
theorem B1620439 : Blo 1619008 1620439 := bstep (se 1 (by rfl) ⟨1215329, by rfl⟩ : syracuseStep 1620439 = 2430659) B2430659
theorem B3643865 : Blo 1619008 3643865 := bstep (se 2 (by rfl) ⟨1366449, by rfl⟩ : syracuseStep 3643865 = 2732899) B2732899
theorem B2734553 : Blo 1619008 2734553 := bstep (se 2 (by rfl) ⟨1025457, by rfl⟩ : syracuseStep 2734553 = 2050915) B2050915
theorem B5470685 : Blo 1619008 5470685 := bstep (se 3 (by rfl) ⟨1025753, by rfl⟩ : syracuseStep 5470685 = 2051507) B2051507
theorem B1620459 : Blo 1619008 1620459 := bstep (se 1 (by rfl) ⟨1215344, by rfl⟩ : syracuseStep 1620459 = 2430689) B2430689
theorem B1620471 : Blo 1619008 1620471 := bstep (se 1 (by rfl) ⟨1215353, by rfl⟩ : syracuseStep 1620471 = 2430707) B2430707
theorem B1620491 : Blo 1619008 1620491 := bstep (se 1 (by rfl) ⟨1215368, by rfl⟩ : syracuseStep 1620491 = 2430737) B2430737
theorem B2431499 : Blo 1619008 2431499 := bstep (se 1 (by rfl) ⟨1823624, by rfl⟩ : syracuseStep 2431499 = 3647249) B3647249
theorem B1620503 : Blo 1619008 1620503 := bstep (se 1 (by rfl) ⟨1215377, by rfl⟩ : syracuseStep 1620503 = 2430755) B2430755
theorem B2431511 : Blo 1619008 2431511 := bstep (se 1 (by rfl) ⟨1823633, by rfl⟩ : syracuseStep 2431511 = 3647267) B3647267
theorem B1620523 : Blo 1619008 1620523 := bstep (se 1 (by rfl) ⟨1215392, by rfl⟩ : syracuseStep 1620523 = 2430785) B2430785
theorem B3643955 : Blo 1619008 3643955 := bstep (se 1 (by rfl) ⟨2732966, by rfl⟩ : syracuseStep 3643955 = 5465933) B5465933
theorem B1620535 : Blo 1619008 1620535 := bstep (se 1 (by rfl) ⟨1215401, by rfl⟩ : syracuseStep 1620535 = 2430803) B2430803
theorem B4102721 : Blo 1619008 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B1620555 : Blo 1619008 1620555 := bstep (se 1 (by rfl) ⟨1215416, by rfl⟩ : syracuseStep 1620555 = 2430833) B2430833
theorem B3643991 : Blo 1619008 3643991 := bstep (se 1 (by rfl) ⟨2732993, by rfl⟩ : syracuseStep 3643991 = 5465987) B5465987
theorem B1620567 : Blo 1619008 1620567 := bstep (se 1 (by rfl) ⟨1215425, by rfl⟩ : syracuseStep 1620567 = 2430851) B2430851
theorem B2734681 : Blo 1619008 2734681 := bstep (se 2 (by rfl) ⟨1025505, by rfl⟩ : syracuseStep 2734681 = 2051011) B2051011
theorem B1620587 : Blo 1619008 1620587 := bstep (se 1 (by rfl) ⟨1215440, by rfl⟩ : syracuseStep 1620587 = 2430881) B2430881
theorem B1620599 : Blo 1619008 1620599 := bstep (se 1 (by rfl) ⟨1215449, by rfl⟩ : syracuseStep 1620599 = 2430899) B2430899
theorem B7494275 : Blo 1619008 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B1620619 : Blo 1619008 1620619 := bstep (se 1 (by rfl) ⟨1215464, by rfl⟩ : syracuseStep 1620619 = 2430929) B2430929
theorem B1620631 : Blo 1619008 1620631 := bstep (se 1 (by rfl) ⟨1215473, by rfl⟩ : syracuseStep 1620631 = 2430947) B2430947
theorem B1620651 : Blo 1619008 1620651 := bstep (se 1 (by rfl) ⟨1215488, by rfl⟩ : syracuseStep 1620651 = 2430977) B2430977
theorem B1620663 : Blo 1619008 1620663 := bstep (se 1 (by rfl) ⟨1215497, by rfl⟩ : syracuseStep 1620663 = 2430995) B2430995
theorem B1620683 : Blo 1619008 1620683 := bstep (se 1 (by rfl) ⟨1215512, by rfl⟩ : syracuseStep 1620683 = 2431025) B2431025
theorem B3693271 : Blo 1619008 3693271 := bstep (se 1 (by rfl) ⟨2769953, by rfl⟩ : syracuseStep 3693271 = 5539907) B5539907
theorem B1620695 : Blo 1619008 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B1620715 : Blo 1619008 1620715 := bstep (se 1 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 1620715 = 2431073) B2431073
theorem B1620727 : Blo 1619008 1620727 := bstep (se 1 (by rfl) ⟨1215545, by rfl⟩ : syracuseStep 1620727 = 2431091) B2431091
theorem B11680517 : Blo 1619008 11680517 := bstep (se 4 (by rfl) ⟨1095048, by rfl⟩ : syracuseStep 11680517 = 2190097) B2190097
theorem B3644171 : Blo 1619008 3644171 := bstep (se 1 (by rfl) ⟨2733128, by rfl⟩ : syracuseStep 3644171 = 5466257) B5466257
theorem B1620747 : Blo 1619008 1620747 := bstep (se 1 (by rfl) ⟨1215560, by rfl⟩ : syracuseStep 1620747 = 2431121) B2431121
theorem B10525457 : Blo 1619008 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B1620759 : Blo 1619008 1620759 := bstep (se 1 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 1620759 = 2431139) B2431139
theorem B1620779 : Blo 1619008 1620779 := bstep (se 1 (by rfl) ⟨1215584, by rfl⟩ : syracuseStep 1620779 = 2431169) B2431169
theorem B1620791 : Blo 1619008 1620791 := bstep (se 1 (by rfl) ⟨1215593, by rfl⟩ : syracuseStep 1620791 = 2431187) B2431187
theorem B13130561 : Blo 1619008 13130561 := bstep (se 2 (by rfl) ⟨4923960, by rfl⟩ : syracuseStep 13130561 = 9847921) B9847921
theorem B3644225 : Blo 1619008 3644225 := bstep (se 2 (by rfl) ⟨1366584, by rfl⟩ : syracuseStep 3644225 = 2733169) B2733169
theorem B4438849 : Blo 1619008 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B6921035 : Blo 1619008 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1620811 : Blo 1619008 1620811 := bstep (se 1 (by rfl) ⟨1215608, by rfl⟩ : syracuseStep 1620811 = 2431217) B2431217
theorem B1620823 : Blo 1619008 1620823 := bstep (se 1 (by rfl) ⟨1215617, by rfl⟩ : syracuseStep 1620823 = 2431235) B2431235
theorem B1620843 : Blo 1619008 1620843 := bstep (se 1 (by rfl) ⟨1215632, by rfl⟩ : syracuseStep 1620843 = 2431265) B2431265
theorem B1620855 : Blo 1619008 1620855 := bstep (se 1 (by rfl) ⟨1215641, by rfl⟩ : syracuseStep 1620855 = 2431283) B2431283
theorem B1620875 : Blo 1619008 1620875 := bstep (se 1 (by rfl) ⟨1215656, by rfl⟩ : syracuseStep 1620875 = 2431313) B2431313
theorem B1620887 : Blo 1619008 1620887 := bstep (se 1 (by rfl) ⟨1215665, by rfl⟩ : syracuseStep 1620887 = 2431331) B2431331
theorem B1620907 : Blo 1619008 1620907 := bstep (se 1 (by rfl) ⟨1215680, by rfl⟩ : syracuseStep 1620907 = 2431361) B2431361
theorem B3693491 : Blo 1619008 3693491 := bstep (se 1 (by rfl) ⟨2770118, by rfl⟩ : syracuseStep 3693491 = 5540237) B5540237
theorem B1620919 : Blo 1619008 1620919 := bstep (se 1 (by rfl) ⟨1215689, by rfl⟩ : syracuseStep 1620919 = 2431379) B2431379
theorem B3890123 : Blo 1619008 3890123 := bstep (se 1 (by rfl) ⟨2917592, by rfl⟩ : syracuseStep 3890123 = 5835185) B5835185
theorem B1620939 : Blo 1619008 1620939 := bstep (se 1 (by rfl) ⟨1215704, by rfl⟩ : syracuseStep 1620939 = 2431409) B2431409
theorem B1620951 : Blo 1619008 1620951 := bstep (se 1 (by rfl) ⟨1215713, by rfl⟩ : syracuseStep 1620951 = 2431427) B2431427
theorem B1620971 : Blo 1619008 1620971 := bstep (se 1 (by rfl) ⟨1215728, by rfl⟩ : syracuseStep 1620971 = 2431457) B2431457
theorem B1620983 : Blo 1619008 1620983 := bstep (se 1 (by rfl) ⟨1215737, by rfl⟩ : syracuseStep 1620983 = 2431475) B2431475
theorem B1621003 : Blo 1619008 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B2595863 : Blo 1619008 2595863 := bstep (se 1 (by rfl) ⟨1946897, by rfl⟩ : syracuseStep 2595863 = 3893795) B3893795
theorem B3644441 : Blo 1619008 3644441 := bstep (se 2 (by rfl) ⟨1366665, by rfl⟩ : syracuseStep 3644441 = 2733331) B2733331
theorem B3644531 : Blo 1619008 3644531 := bstep (se 1 (by rfl) ⟨2733398, by rfl⟩ : syracuseStep 3644531 = 5466797) B5466797
theorem B3644567 : Blo 1619008 3644567 := bstep (se 1 (by rfl) ⟨2733425, by rfl⟩ : syracuseStep 3644567 = 5466851) B5466851
theorem B2735255 : Blo 1619008 2735255 := bstep (se 1 (by rfl) ⟨2051441, by rfl⟩ : syracuseStep 2735255 = 4102883) B4102883
theorem B3890393 : Blo 1619008 3890393 := bstep (se 2 (by rfl) ⟨1458897, by rfl⟩ : syracuseStep 3890393 = 2917795) B2917795
theorem B2735383 : Blo 1619008 2735383 := bstep (se 1 (by rfl) ⟨2051537, by rfl⟩ : syracuseStep 2735383 = 4103075) B4103075
theorem B9223469 : Blo 1619008 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B7011659 : Blo 1619008 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B3644747 : Blo 1619008 3644747 := bstep (se 1 (by rfl) ⟨2733560, by rfl⟩ : syracuseStep 3644747 = 5467121) B5467121
theorem B9231691 : Blo 1619008 9231691 := bstep (se 1 (by rfl) ⟨6923768, by rfl⟩ : syracuseStep 9231691 = 13847537) B13847537
theorem B3644801 : Blo 1619008 3644801 := bstep (se 2 (by rfl) ⟨1366800, by rfl⟩ : syracuseStep 3644801 = 2733601) B2733601
theorem B6151697 : Blo 1619008 6151697 := bstep (se 2 (by rfl) ⟨2306886, by rfl⟩ : syracuseStep 6151697 = 4613773) B4613773
theorem B3645017 : Blo 1619008 3645017 := bstep (se 2 (by rfl) ⟨1366881, by rfl⟩ : syracuseStep 3645017 = 2733763) B2733763
theorem B9231965 : Blo 1619008 9231965 := bstep (se 3 (by rfl) ⟨1730993, by rfl⟩ : syracuseStep 9231965 = 3461987) B3461987
theorem B14786225 : Blo 1619008 14786225 := bstep (se 2 (by rfl) ⟨5544834, by rfl⟩ : syracuseStep 14786225 = 11089669) B11089669
theorem B3645107 : Blo 1619008 3645107 := bstep (se 1 (by rfl) ⟨2733830, by rfl⟩ : syracuseStep 3645107 = 5467661) B5467661
theorem B3284659 : Blo 1619008 3284659 := bstep (se 1 (by rfl) ⟨2463494, by rfl⟩ : syracuseStep 3284659 = 4926989) B4926989
theorem B3645143 : Blo 1619008 3645143 := bstep (se 1 (by rfl) ⟨2733857, by rfl⟩ : syracuseStep 3645143 = 5467715) B5467715
theorem B8199953 : Blo 1619008 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B3645323 : Blo 1619008 3645323 := bstep (se 1 (by rfl) ⟨2733992, by rfl⟩ : syracuseStep 3645323 = 5467985) B5467985
theorem B8200115 : Blo 1619008 8200115 := bstep (se 1 (by rfl) ⟨6150086, by rfl⟩ : syracuseStep 8200115 = 12300173) B12300173
theorem B3645377 : Blo 1619008 3645377 := bstep (se 2 (by rfl) ⟨1367016, by rfl⟩ : syracuseStep 3645377 = 2734033) B2734033
theorem B3891161 : Blo 1619008 3891161 := bstep (se 2 (by rfl) ⟨1459185, by rfl⟩ : syracuseStep 3891161 = 2918371) B2918371
theorem B4210807 : Blo 1619008 4210807 := bstep (se 1 (by rfl) ⟨3158105, by rfl⟩ : syracuseStep 4210807 = 6316211) B6316211
theorem B3645575 : Blo 1619008 3645575 := bstep (se 1 (by rfl) ⟨2734181, by rfl⟩ : syracuseStep 3645575 = 5468363) B5468363
theorem B18456821 : Blo 1619008 18456821 := bstep (se 5 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 18456821 = 1730327) B1730327
theorem B8995105 : Blo 1619008 8995105 := bstep (se 2 (by rfl) ⟨3373164, by rfl⟩ : syracuseStep 8995105 = 6746329) B6746329
theorem B3645755 : Blo 1619008 3645755 := bstep (se 1 (by rfl) ⟨2734316, by rfl⟩ : syracuseStep 3645755 = 5468633) B5468633
theorem B8200601 : Blo 1619008 8200601 := bstep (se 2 (by rfl) ⟨3075225, by rfl⟩ : syracuseStep 8200601 = 6150451) B6150451
theorem B3645881 : Blo 1619008 3645881 := bstep (se 2 (by rfl) ⟨1367205, by rfl⟩ : syracuseStep 3645881 = 2734411) B2734411
theorem B9355799 : Blo 1619008 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B5464637 : Blo 1619008 5464637 := bstep (se 3 (by rfl) ⟨1024619, by rfl⟩ : syracuseStep 5464637 = 2049239) B2049239
theorem B12296771 : Blo 1619008 12296771 := bstep (se 1 (by rfl) ⟨9222578, by rfl⟩ : syracuseStep 12296771 = 18445157) B18445157
theorem B3646223 : Blo 1619008 3646223 := bstep (se 1 (by rfl) ⟨2734667, by rfl⟩ : syracuseStep 3646223 = 5469335) B5469335
theorem B3646241 : Blo 1619008 3646241 := bstep (se 2 (by rfl) ⟨1367340, by rfl⟩ : syracuseStep 3646241 = 2734681) B2734681
theorem B6570811 : Blo 1619008 6570811 := bstep (se 1 (by rfl) ⟨4928108, by rfl⟩ : syracuseStep 6570811 = 9856217) B9856217
theorem B7783283 : Blo 1619008 7783283 := bstep (se 1 (by rfl) ⟨5837462, by rfl⟩ : syracuseStep 7783283 = 11674925) B11674925
theorem B4924361 : Blo 1619008 4924361 := bstep (se 2 (by rfl) ⟨1846635, by rfl⟩ : syracuseStep 4924361 = 3693271) B3693271
theorem B2049067 : Blo 1619008 2049067 := bstep (se 1 (by rfl) ⟨1536800, by rfl⟩ : syracuseStep 2049067 = 3073601) B3073601
theorem B3646583 : Blo 1619008 3646583 := bstep (se 1 (by rfl) ⟨2734937, by rfl⟩ : syracuseStep 3646583 = 5469875) B5469875
theorem B8881325 : Blo 1619008 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B2049295 : Blo 1619008 2049295 := bstep (se 1 (by rfl) ⟨1536971, by rfl⟩ : syracuseStep 2049295 = 3073943) B3073943
theorem B6571297 : Blo 1619008 6571297 := bstep (se 2 (by rfl) ⟨2464236, by rfl⟩ : syracuseStep 6571297 = 4928473) B4928473
theorem B3646763 : Blo 1619008 3646763 := bstep (se 1 (by rfl) ⟨2735072, by rfl⟩ : syracuseStep 3646763 = 5470145) B5470145
theorem B3647123 : Blo 1619008 3647123 := bstep (se 1 (by rfl) ⟨2735342, by rfl⟩ : syracuseStep 3647123 = 5470685) B5470685
theorem B3647177 : Blo 1619008 3647177 := bstep (se 2 (by rfl) ⟨1367691, by rfl⟩ : syracuseStep 3647177 = 2735383) B2735383
theorem B7784207 : Blo 1619008 7784207 := bstep (se 1 (by rfl) ⟨5838155, by rfl⟩ : syracuseStep 7784207 = 11676311) B11676311
theorem B17745713 : Blo 1619008 17745713 := bstep (se 2 (by rfl) ⟨6654642, by rfl⟩ : syracuseStep 17745713 = 13309285) B13309285
theorem B4614023 : Blo 1619008 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B3458963 : Blo 1619008 3458963 := bstep (se 1 (by rfl) ⟨2594222, by rfl⟩ : syracuseStep 3458963 = 5188445) B5188445
theorem B5466041 : Blo 1619008 5466041 := bstep (se 2 (by rfl) ⟨2049765, by rfl⟩ : syracuseStep 5466041 = 4099531) B4099531
theorem B2050039 : Blo 1619008 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B1730575 : Blo 1619008 1730575 := bstep (se 1 (by rfl) ⟨1297931, by rfl⟩ : syracuseStep 1730575 = 2595863) B2595863
theorem B4376605 : Blo 1619008 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B4098347 : Blo 1619008 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B2050363 : Blo 1619008 2050363 := bstep (se 1 (by rfl) ⟨1537772, by rfl⟩ : syracuseStep 2050363 = 3075545) B3075545
theorem B14780819 : Blo 1619008 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B6154643 : Blo 1619008 6154643 := bstep (se 1 (by rfl) ⟨4615982, by rfl⟩ : syracuseStep 6154643 = 9231965) B9231965
theorem B4155833 : Blo 1619008 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B9857483 : Blo 1619008 9857483 := bstep (se 1 (by rfl) ⟨7393112, by rfl⟩ : syracuseStep 9857483 = 14786225) B14786225
theorem B21629405 : Blo 1619008 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B5466635 : Blo 1619008 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B5466743 : Blo 1619008 5466743 := bstep (se 1 (by rfl) ⟨4100057, by rfl⟩ : syracuseStep 5466743 = 8200115) B8200115
theorem B12462821 : Blo 1619008 12462821 := bstep (se 4 (by rfl) ⟨1168389, by rfl⟩ : syracuseStep 12462821 = 2336779) B2336779
theorem B4926209 : Blo 1619008 4926209 := bstep (se 2 (by rfl) ⟨1847328, by rfl⟩ : syracuseStep 4926209 = 3694657) B3694657
theorem B3074831 : Blo 1619008 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B2050859 : Blo 1619008 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B2919287 : Blo 1619008 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B3894151 : Blo 1619008 3894151 := bstep (se 1 (by rfl) ⟨2920613, by rfl⟩ : syracuseStep 3894151 = 5841227) B5841227
theorem B52562837 : Blo 1619008 52562837 := bstep (se 6 (by rfl) ⟨1231941, by rfl⟩ : syracuseStep 52562837 = 2463883) B2463883
theorem B8203193 : Blo 1619008 8203193 := bstep (se 2 (by rfl) ⟨3076197, by rfl⟩ : syracuseStep 8203193 = 6152395) B6152395
theorem B4271105 : Blo 1619008 4271105 := bstep (se 2 (by rfl) ⟨1601664, by rfl⟩ : syracuseStep 4271105 = 3203329) B3203329
theorem B1821703 : Blo 1619008 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B4099187 : Blo 1619008 4099187 := bstep (se 1 (by rfl) ⟨3074390, by rfl⟩ : syracuseStep 4099187 = 6148781) B6148781
theorem B4099207 : Blo 1619008 4099207 := bstep (se 1 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 4099207 = 6148811) B6148811
theorem B1821883 : Blo 1619008 1821883 := bstep (se 1 (by rfl) ⟨1366412, by rfl⟩ : syracuseStep 1821883 = 2732825) B2732825
theorem B5467337 : Blo 1619008 5467337 := bstep (se 2 (by rfl) ⟨2050251, by rfl⟩ : syracuseStep 5467337 = 4100503) B4100503
theorem B9850085 : Blo 1619008 9850085 := bstep (se 4 (by rfl) ⟨923445, by rfl⟩ : syracuseStep 9850085 = 1846891) B1846891
theorem B2051335 : Blo 1619008 2051335 := bstep (se 1 (by rfl) ⟨1538501, by rfl⟩ : syracuseStep 2051335 = 3077003) B3077003
theorem B4099481 : Blo 1619008 4099481 := bstep (se 2 (by rfl) ⟨1537305, by rfl⟩ : syracuseStep 4099481 = 3074611) B3074611
theorem B2919979 : Blo 1619008 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B4099643 : Blo 1619008 4099643 := bstep (se 1 (by rfl) ⟨3074732, by rfl⟩ : syracuseStep 4099643 = 6149465) B6149465
theorem B9227843 : Blo 1619008 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B2428535 : Blo 1619008 2428535 := bstep (se 1 (by rfl) ⟨1821401, by rfl⟩ : syracuseStep 2428535 = 3642803) B3642803
theorem B2428559 : Blo 1619008 2428559 := bstep (se 1 (by rfl) ⟨1821419, by rfl⟩ : syracuseStep 2428559 = 3642839) B3642839
theorem B1822351 : Blo 1619008 1822351 := bstep (se 1 (by rfl) ⟨1366763, by rfl⟩ : syracuseStep 1822351 = 2733527) B2733527
theorem B2428601 : Blo 1619008 2428601 := bstep (se 2 (by rfl) ⟨910725, by rfl⟩ : syracuseStep 2428601 = 1821451) B1821451
theorem B5918465 : Blo 1619008 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B4615937 : Blo 1619008 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B2428679 : Blo 1619008 2428679 := bstep (se 1 (by rfl) ⟨1821509, by rfl⟩ : syracuseStep 2428679 = 3643019) B3643019
theorem B4099855 : Blo 1619008 4099855 := bstep (se 1 (by rfl) ⟨3074891, by rfl⟩ : syracuseStep 4099855 = 6149783) B6149783
theorem B2428715 : Blo 1619008 2428715 := bstep (se 1 (by rfl) ⟨1821536, by rfl⟩ : syracuseStep 2428715 = 3643073) B3643073
theorem B2428745 : Blo 1619008 2428745 := bstep (se 2 (by rfl) ⟨910779, by rfl⟩ : syracuseStep 2428745 = 1821559) B1821559
theorem B15576907 : Blo 1619008 15576907 := bstep (se 1 (by rfl) ⟨11682680, by rfl⟩ : syracuseStep 15576907 = 23365361) B23365361
theorem B5468039 : Blo 1619008 5468039 := bstep (se 1 (by rfl) ⟨4101029, by rfl⟩ : syracuseStep 5468039 = 8202059) B8202059
theorem B2428859 : Blo 1619008 2428859 := bstep (se 1 (by rfl) ⟨1821644, by rfl⟩ : syracuseStep 2428859 = 3643289) B3643289
theorem B2428919 : Blo 1619008 2428919 := bstep (se 1 (by rfl) ⟨1821689, by rfl⟩ : syracuseStep 2428919 = 3643379) B3643379
theorem B2428943 : Blo 1619008 2428943 := bstep (se 1 (by rfl) ⟨1821707, by rfl⟩ : syracuseStep 2428943 = 3643415) B3643415
theorem B4100129 : Blo 1619008 4100129 := bstep (se 2 (by rfl) ⟨1537548, by rfl⟩ : syracuseStep 4100129 = 3075097) B3075097
theorem B2428985 : Blo 1619008 2428985 := bstep (se 2 (by rfl) ⟨910869, by rfl⟩ : syracuseStep 2428985 = 1821739) B1821739
theorem B504868949 : Blo 1619008 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B2429063 : Blo 1619008 2429063 := bstep (se 1 (by rfl) ⟨1821797, by rfl⟩ : syracuseStep 2429063 = 3643595) B3643595
theorem B1822855 : Blo 1619008 1822855 := bstep (se 1 (by rfl) ⟨1367141, by rfl⟩ : syracuseStep 1822855 = 2734283) B2734283
theorem B2429099 : Blo 1619008 2429099 := bstep (se 1 (by rfl) ⟨1821824, by rfl⟩ : syracuseStep 2429099 = 3643649) B3643649
theorem B2429129 : Blo 1619008 2429129 := bstep (se 2 (by rfl) ⟨910923, by rfl⟩ : syracuseStep 2429129 = 1821847) B1821847
theorem B8204489 : Blo 1619008 8204489 := bstep (se 2 (by rfl) ⟨3076683, by rfl⟩ : syracuseStep 8204489 = 6153367) B6153367
theorem B5468417 : Blo 1619008 5468417 := bstep (se 2 (by rfl) ⟨2050656, by rfl⟩ : syracuseStep 5468417 = 4101313) B4101313
theorem B8761601 : Blo 1619008 8761601 := bstep (se 2 (by rfl) ⟨3285600, by rfl⟩ : syracuseStep 8761601 = 6571201) B6571201
theorem B1847567 : Blo 1619008 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B2429243 : Blo 1619008 2429243 := bstep (se 1 (by rfl) ⟨1821932, by rfl⟩ : syracuseStep 2429243 = 3643865) B3643865
theorem B1823035 : Blo 1619008 1823035 := bstep (se 1 (by rfl) ⟨1367276, by rfl⟩ : syracuseStep 1823035 = 2734553) B2734553
theorem B2429303 : Blo 1619008 2429303 := bstep (se 1 (by rfl) ⟨1821977, by rfl⟩ : syracuseStep 2429303 = 3643955) B3643955
theorem B3076471 : Blo 1619008 3076471 := bstep (se 1 (by rfl) ⟨2307353, by rfl⟩ : syracuseStep 3076471 = 4614707) B4614707
theorem B2429327 : Blo 1619008 2429327 := bstep (se 1 (by rfl) ⟨1821995, by rfl⟩ : syracuseStep 2429327 = 3643991) B3643991
theorem B2429369 : Blo 1619008 2429369 := bstep (se 2 (by rfl) ⟨911013, by rfl⟩ : syracuseStep 2429369 = 1822027) B1822027
theorem B12308921 : Blo 1619008 12308921 := bstep (se 2 (by rfl) ⟨4615845, by rfl⟩ : syracuseStep 12308921 = 9231691) B9231691
theorem B2306551 : Blo 1619008 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B7787011 : Blo 1619008 7787011 := bstep (se 1 (by rfl) ⟨5840258, by rfl⟩ : syracuseStep 7787011 = 11680517) B11680517
theorem B2429447 : Blo 1619008 2429447 := bstep (se 1 (by rfl) ⟨1822085, by rfl⟩ : syracuseStep 2429447 = 3644171) B3644171
theorem B1946119 : Blo 1619008 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B7016971 : Blo 1619008 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B8753707 : Blo 1619008 8753707 := bstep (se 1 (by rfl) ⟨6565280, by rfl⟩ : syracuseStep 8753707 = 13130561) B13130561
theorem B2429483 : Blo 1619008 2429483 := bstep (se 1 (by rfl) ⟨1822112, by rfl⟩ : syracuseStep 2429483 = 3644225) B3644225
theorem B2429513 : Blo 1619008 2429513 := bstep (se 2 (by rfl) ⟨911067, by rfl⟩ : syracuseStep 2429513 = 1822135) B1822135
theorem B2732663 : Blo 1619008 2732663 := bstep (se 1 (by rfl) ⟨2049497, by rfl⟩ : syracuseStep 2732663 = 4098995) B4098995
theorem B2462327 : Blo 1619008 2462327 := bstep (se 1 (by rfl) ⟨1846745, by rfl⟩ : syracuseStep 2462327 = 3693491) B3693491
theorem B2593415 : Blo 1619008 2593415 := bstep (se 1 (by rfl) ⟨1945061, by rfl⟩ : syracuseStep 2593415 = 3890123) B3890123
theorem B2429627 : Blo 1619008 2429627 := bstep (se 1 (by rfl) ⟨1822220, by rfl⟩ : syracuseStep 2429627 = 3644441) B3644441
theorem B2429687 : Blo 1619008 2429687 := bstep (se 1 (by rfl) ⟨1822265, by rfl⟩ : syracuseStep 2429687 = 3644531) B3644531
theorem B1946359 : Blo 1619008 1946359 := bstep (se 1 (by rfl) ⟨1459769, by rfl⟩ : syracuseStep 1946359 = 2919539) B2919539
theorem B2429711 : Blo 1619008 2429711 := bstep (se 1 (by rfl) ⟨1822283, by rfl⟩ : syracuseStep 2429711 = 3644567) B3644567
theorem B1823503 : Blo 1619008 1823503 := bstep (se 1 (by rfl) ⟨1367627, by rfl⟩ : syracuseStep 1823503 = 2735255) B2735255
theorem B2429753 : Blo 1619008 2429753 := bstep (se 2 (by rfl) ⟨911157, by rfl⟩ : syracuseStep 2429753 = 1822315) B1822315
theorem B2593595 : Blo 1619008 2593595 := bstep (se 1 (by rfl) ⟨1945196, by rfl⟩ : syracuseStep 2593595 = 3890393) B3890393
theorem B2306875 : Blo 1619008 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B12301145 : Blo 1619008 12301145 := bstep (se 2 (by rfl) ⟨4612929, by rfl⟩ : syracuseStep 12301145 = 9225859) B9225859
theorem B6148979 : Blo 1619008 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B4674439 : Blo 1619008 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B2429831 : Blo 1619008 2429831 := bstep (se 1 (by rfl) ⟨1822373, by rfl⟩ : syracuseStep 2429831 = 3644747) B3644747
theorem B4379545 : Blo 1619008 4379545 := bstep (se 2 (by rfl) ⟨1642329, by rfl⟩ : syracuseStep 4379545 = 3284659) B3284659
theorem B2429867 : Blo 1619008 2429867 := bstep (se 1 (by rfl) ⟨1822400, by rfl⟩ : syracuseStep 2429867 = 3644801) B3644801
theorem B2429897 : Blo 1619008 2429897 := bstep (se 2 (by rfl) ⟨911211, by rfl⟩ : syracuseStep 2429897 = 1822423) B1822423
theorem B6919121 : Blo 1619008 6919121 := bstep (se 2 (by rfl) ⟨2594670, by rfl⟩ : syracuseStep 6919121 = 5189341) B5189341
theorem B4101131 : Blo 1619008 4101131 := bstep (se 1 (by rfl) ⟨3075848, by rfl⟩ : syracuseStep 4101131 = 6151697) B6151697
theorem B5469227 : Blo 1619008 5469227 := bstep (se 1 (by rfl) ⟨4101920, by rfl⟩ : syracuseStep 5469227 = 8203841) B8203841
theorem B2733115 : Blo 1619008 2733115 := bstep (se 1 (by rfl) ⟨2049836, by rfl⟩ : syracuseStep 2733115 = 4099673) B4099673
theorem B2430011 : Blo 1619008 2430011 := bstep (se 1 (by rfl) ⟨1822508, by rfl⟩ : syracuseStep 2430011 = 3645017) B3645017
theorem B2430071 : Blo 1619008 2430071 := bstep (se 1 (by rfl) ⟨1822553, by rfl⟩ : syracuseStep 2430071 = 3645107) B3645107
theorem B1619079 : Blo 1619008 1619079 := bstep (se 1 (by rfl) ⟨1214309, by rfl⟩ : syracuseStep 1619079 = 2428619) B2428619
theorem B1619087 : Blo 1619008 1619087 := bstep (se 1 (by rfl) ⟨1214315, by rfl⟩ : syracuseStep 1619087 = 2428631) B2428631
theorem B2430095 : Blo 1619008 2430095 := bstep (se 1 (by rfl) ⟨1822571, by rfl⟩ : syracuseStep 2430095 = 3645143) B3645143
theorem B2430137 : Blo 1619008 2430137 := bstep (se 2 (by rfl) ⟨911301, by rfl⟩ : syracuseStep 2430137 = 1822603) B1822603
theorem B1619131 : Blo 1619008 1619131 := bstep (se 1 (by rfl) ⟨1214348, by rfl⟩ : syracuseStep 1619131 = 2428697) B2428697
theorem B8000705 : Blo 1619008 8000705 := bstep (se 2 (by rfl) ⟨3000264, by rfl⟩ : syracuseStep 8000705 = 6000529) B6000529
theorem B2733257 : Blo 1619008 2733257 := bstep (se 2 (by rfl) ⟨1024971, by rfl⟩ : syracuseStep 2733257 = 2049943) B2049943
theorem B1619207 : Blo 1619008 1619207 := bstep (se 1 (by rfl) ⟨1214405, by rfl⟩ : syracuseStep 1619207 = 2428811) B2428811
theorem B2430215 : Blo 1619008 2430215 := bstep (se 1 (by rfl) ⟨1822661, by rfl⟩ : syracuseStep 2430215 = 3645323) B3645323
theorem B1619215 : Blo 1619008 1619215 := bstep (se 1 (by rfl) ⟨1214411, by rfl⟩ : syracuseStep 1619215 = 2428823) B2428823
theorem B2430251 : Blo 1619008 2430251 := bstep (se 1 (by rfl) ⟨1822688, by rfl⟩ : syracuseStep 2430251 = 3645377) B3645377
theorem B1619259 : Blo 1619008 1619259 := bstep (se 1 (by rfl) ⟨1214444, by rfl⟩ : syracuseStep 1619259 = 2428889) B2428889
theorem B2594107 : Blo 1619008 2594107 := bstep (se 1 (by rfl) ⟨1945580, by rfl⟩ : syracuseStep 2594107 = 3891161) B3891161
theorem B2430281 : Blo 1619008 2430281 := bstep (se 2 (by rfl) ⟨911355, by rfl⟩ : syracuseStep 2430281 = 1822711) B1822711
theorem B18715997 : Blo 1619008 18715997 := bstep (se 3 (by rfl) ⟨3509249, by rfl⟩ : syracuseStep 18715997 = 7018499) B7018499
theorem B1619335 : Blo 1619008 1619335 := bstep (se 1 (by rfl) ⟨1214501, by rfl⟩ : syracuseStep 1619335 = 2429003) B2429003
theorem B1619343 : Blo 1619008 1619343 := bstep (se 1 (by rfl) ⟨1214507, by rfl⟩ : syracuseStep 1619343 = 2429015) B2429015
theorem B18453905 : Blo 1619008 18453905 := bstep (se 2 (by rfl) ⟨6920214, by rfl⟩ : syracuseStep 18453905 = 13840429) B13840429
theorem B8197523 : Blo 1619008 8197523 := bstep (se 1 (by rfl) ⟨6148142, by rfl⟩ : syracuseStep 8197523 = 12296285) B12296285
theorem B1619387 : Blo 1619008 1619387 := bstep (se 1 (by rfl) ⟨1214540, by rfl⟩ : syracuseStep 1619387 = 2429081) B2429081
theorem B2430395 : Blo 1619008 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B2430455 : Blo 1619008 2430455 := bstep (se 1 (by rfl) ⟨1822841, by rfl⟩ : syracuseStep 2430455 = 3645683) B3645683
theorem B1619463 : Blo 1619008 1619463 := bstep (se 1 (by rfl) ⟨1214597, by rfl⟩ : syracuseStep 1619463 = 2429195) B2429195
theorem B1619471 : Blo 1619008 1619471 := bstep (se 1 (by rfl) ⟨1214603, by rfl⟩ : syracuseStep 1619471 = 2429207) B2429207
theorem B2430479 : Blo 1619008 2430479 := bstep (se 1 (by rfl) ⟨1822859, by rfl⟩ : syracuseStep 2430479 = 3645719) B3645719
theorem B2430521 : Blo 1619008 2430521 := bstep (se 2 (by rfl) ⟨911445, by rfl⟩ : syracuseStep 2430521 = 1822891) B1822891
theorem B1619515 : Blo 1619008 1619515 := bstep (se 1 (by rfl) ⟨1214636, by rfl⟩ : syracuseStep 1619515 = 2429273) B2429273
theorem B2594363 : Blo 1619008 2594363 := bstep (se 1 (by rfl) ⟨1945772, by rfl⟩ : syracuseStep 2594363 = 3891545) B3891545
theorem B1619591 : Blo 1619008 1619591 := bstep (se 1 (by rfl) ⟨1214693, by rfl⟩ : syracuseStep 1619591 = 2429387) B2429387
theorem B2430599 : Blo 1619008 2430599 := bstep (se 1 (by rfl) ⟨1822949, by rfl⟩ : syracuseStep 2430599 = 3645899) B3645899
theorem B1619599 : Blo 1619008 1619599 := bstep (se 1 (by rfl) ⟨1214699, by rfl⟩ : syracuseStep 1619599 = 2429399) B2429399
theorem B4101779 : Blo 1619008 4101779 := bstep (se 1 (by rfl) ⟨3076334, by rfl⟩ : syracuseStep 4101779 = 6152669) B6152669
theorem B2430635 : Blo 1619008 2430635 := bstep (se 1 (by rfl) ⟨1822976, by rfl⟩ : syracuseStep 2430635 = 3645953) B3645953
theorem B1619643 : Blo 1619008 1619643 := bstep (se 1 (by rfl) ⟨1214732, by rfl⟩ : syracuseStep 1619643 = 2429465) B2429465
theorem B9852617 : Blo 1619008 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B2430665 : Blo 1619008 2430665 := bstep (se 2 (by rfl) ⟨911499, by rfl⟩ : syracuseStep 2430665 = 1822999) B1822999
theorem B1619719 : Blo 1619008 1619719 := bstep (se 1 (by rfl) ⟨1214789, by rfl⟩ : syracuseStep 1619719 = 2429579) B2429579
theorem B1619727 : Blo 1619008 1619727 := bstep (se 1 (by rfl) ⟨1214795, by rfl⟩ : syracuseStep 1619727 = 2429591) B2429591
theorem B12302117 : Blo 1619008 12302117 := bstep (se 4 (by rfl) ⟨1153323, by rfl⟩ : syracuseStep 12302117 = 2306647) B2306647
theorem B4929323 : Blo 1619008 4929323 := bstep (se 1 (by rfl) ⟨3696992, by rfl⟩ : syracuseStep 4929323 = 7393985) B7393985
theorem B1619771 : Blo 1619008 1619771 := bstep (se 1 (by rfl) ⟨1214828, by rfl⟩ : syracuseStep 1619771 = 2429657) B2429657
theorem B2430779 : Blo 1619008 2430779 := bstep (se 1 (by rfl) ⟨1823084, by rfl⟩ : syracuseStep 2430779 = 3646169) B3646169
theorem B4994903 : Blo 1619008 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B2430839 : Blo 1619008 2430839 := bstep (se 1 (by rfl) ⟨1823129, by rfl⟩ : syracuseStep 2430839 = 3646259) B3646259
theorem B3643271 : Blo 1619008 3643271 := bstep (se 1 (by rfl) ⟨2732453, by rfl⟩ : syracuseStep 3643271 = 5464907) B5464907
theorem B1619847 : Blo 1619008 1619847 := bstep (se 1 (by rfl) ⟨1214885, by rfl⟩ : syracuseStep 1619847 = 2429771) B2429771
theorem B2733959 : Blo 1619008 2733959 := bstep (se 1 (by rfl) ⟨2050469, by rfl⟩ : syracuseStep 2733959 = 4100939) B4100939
theorem B1619855 : Blo 1619008 1619855 := bstep (se 1 (by rfl) ⟨1214891, by rfl⟩ : syracuseStep 1619855 = 2429783) B2429783
theorem B2430863 : Blo 1619008 2430863 := bstep (se 1 (by rfl) ⟨1823147, by rfl⟩ : syracuseStep 2430863 = 3646295) B3646295
theorem B33707927 : Blo 1619008 33707927 := bstep (se 1 (by rfl) ⟨25280945, by rfl⟩ : syracuseStep 33707927 = 50561891) B50561891
theorem B9230233 : Blo 1619008 9230233 := bstep (se 2 (by rfl) ⟨3461337, by rfl⟩ : syracuseStep 9230233 = 6922675) B6922675
theorem B4102073 : Blo 1619008 4102073 := bstep (se 2 (by rfl) ⟨1538277, by rfl⟩ : syracuseStep 4102073 = 3076555) B3076555
theorem B2430905 : Blo 1619008 2430905 := bstep (se 2 (by rfl) ⟨911589, by rfl⟩ : syracuseStep 2430905 = 1823179) B1823179
theorem B1619899 : Blo 1619008 1619899 := bstep (se 1 (by rfl) ⟨1214924, by rfl⟩ : syracuseStep 1619899 = 2429849) B2429849
theorem B7788473 : Blo 1619008 7788473 := bstep (se 2 (by rfl) ⟨2920677, by rfl⟩ : syracuseStep 7788473 = 5841355) B5841355
theorem B1619975 : Blo 1619008 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B2430983 : Blo 1619008 2430983 := bstep (se 1 (by rfl) ⟨1823237, by rfl⟩ : syracuseStep 2430983 = 3646475) B3646475
theorem B1619983 : Blo 1619008 1619983 := bstep (se 1 (by rfl) ⟨1214987, by rfl⟩ : syracuseStep 1619983 = 2429975) B2429975
theorem B37910551 : Blo 1619008 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B11089943 : Blo 1619008 11089943 := bstep (se 1 (by rfl) ⟨8317457, by rfl⟩ : syracuseStep 11089943 = 16634915) B16634915
theorem B2431019 : Blo 1619008 2431019 := bstep (se 1 (by rfl) ⟨1823264, by rfl⟩ : syracuseStep 2431019 = 3646529) B3646529
theorem B3643451 : Blo 1619008 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B1620027 : Blo 1619008 1620027 := bstep (se 1 (by rfl) ⟨1215020, by rfl⟩ : syracuseStep 1620027 = 2430041) B2430041
theorem B2431049 : Blo 1619008 2431049 := bstep (se 2 (by rfl) ⟨911643, by rfl⟩ : syracuseStep 2431049 = 1823287) B1823287
theorem B138459253 : Blo 1619008 138459253 := bstep (se 5 (by rfl) ⟨6490277, by rfl⟩ : syracuseStep 138459253 = 12980555) B12980555
theorem B1620103 : Blo 1619008 1620103 := bstep (se 1 (by rfl) ⟨1215077, by rfl⟩ : syracuseStep 1620103 = 2430155) B2430155
theorem B1620111 : Blo 1619008 1620111 := bstep (se 1 (by rfl) ⟨1215083, by rfl⟩ : syracuseStep 1620111 = 2430167) B2430167
theorem B3643577 : Blo 1619008 3643577 := bstep (se 2 (by rfl) ⟨1366341, by rfl⟩ : syracuseStep 3643577 = 2732683) B2732683
theorem B1620155 : Blo 1619008 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B2431163 : Blo 1619008 2431163 := bstep (se 1 (by rfl) ⟨1823372, by rfl⟩ : syracuseStep 2431163 = 3646745) B3646745
theorem B2431223 : Blo 1619008 2431223 := bstep (se 1 (by rfl) ⟨1823417, by rfl⟩ : syracuseStep 2431223 = 3646835) B3646835
theorem B4380929 : Blo 1619008 4380929 := bstep (se 2 (by rfl) ⟨1642848, by rfl⟩ : syracuseStep 4380929 = 3285697) B3285697
theorem B1620231 : Blo 1619008 1620231 := bstep (se 1 (by rfl) ⟨1215173, by rfl⟩ : syracuseStep 1620231 = 2430347) B2430347
theorem B1620239 : Blo 1619008 1620239 := bstep (se 1 (by rfl) ⟨1215179, by rfl⟩ : syracuseStep 1620239 = 2430359) B2430359
theorem B2431247 : Blo 1619008 2431247 := bstep (se 1 (by rfl) ⟨1823435, by rfl⟩ : syracuseStep 2431247 = 3646871) B3646871
theorem B2431289 : Blo 1619008 2431289 := bstep (se 2 (by rfl) ⟨911733, by rfl⟩ : syracuseStep 2431289 = 1823467) B1823467
theorem B1620283 : Blo 1619008 1620283 := bstep (se 1 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 1620283 = 2430425) B2430425
theorem B5470523 : Blo 1619008 5470523 := bstep (se 1 (by rfl) ⟨4102892, by rfl⟩ : syracuseStep 5470523 = 8205785) B8205785
theorem B1620359 : Blo 1619008 1620359 := bstep (se 1 (by rfl) ⟨1215269, by rfl⟩ : syracuseStep 1620359 = 2430539) B2430539
theorem B2431367 : Blo 1619008 2431367 := bstep (se 1 (by rfl) ⟨1823525, by rfl⟩ : syracuseStep 2431367 = 3647051) B3647051
theorem B1620367 : Blo 1619008 1620367 := bstep (se 1 (by rfl) ⟨1215275, by rfl⟩ : syracuseStep 1620367 = 2430551) B2430551
theorem B2431403 : Blo 1619008 2431403 := bstep (se 1 (by rfl) ⟨1823552, by rfl⟩ : syracuseStep 2431403 = 3647105) B3647105
theorem B1620411 : Blo 1619008 1620411 := bstep (se 1 (by rfl) ⟨1215308, by rfl⟩ : syracuseStep 1620411 = 2430617) B2430617
theorem B2431433 : Blo 1619008 2431433 := bstep (se 2 (by rfl) ⟨911787, by rfl⟩ : syracuseStep 2431433 = 1823575) B1823575
theorem B1620487 : Blo 1619008 1620487 := bstep (se 1 (by rfl) ⟨1215365, by rfl⟩ : syracuseStep 1620487 = 2430731) B2430731
theorem B3643919 : Blo 1619008 3643919 := bstep (se 1 (by rfl) ⟨2732939, by rfl⟩ : syracuseStep 3643919 = 5465879) B5465879
theorem B1620495 : Blo 1619008 1620495 := bstep (se 1 (by rfl) ⟨1215371, by rfl⟩ : syracuseStep 1620495 = 2430743) B2430743
theorem B2734607 : Blo 1619008 2734607 := bstep (se 1 (by rfl) ⟨2050955, by rfl⟩ : syracuseStep 2734607 = 4101911) B4101911
theorem B7109149 : Blo 1619008 7109149 := bstep (se 3 (by rfl) ⟨1332965, by rfl⟩ : syracuseStep 7109149 = 2665931) B2665931
theorem B3643937 : Blo 1619008 3643937 := bstep (se 2 (by rfl) ⟨1366476, by rfl⟩ : syracuseStep 3643937 = 2732953) B2732953
theorem B6920747 : Blo 1619008 6920747 := bstep (se 1 (by rfl) ⟨5190560, by rfl⟩ : syracuseStep 6920747 = 10381121) B10381121
theorem B1620539 : Blo 1619008 1620539 := bstep (se 1 (by rfl) ⟨1215404, by rfl⟩ : syracuseStep 1620539 = 2430809) B2430809
theorem B6232643 : Blo 1619008 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B20757059 : Blo 1619008 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B4610675 : Blo 1619008 4610675 := bstep (se 1 (by rfl) ⟨3458006, by rfl⟩ : syracuseStep 4610675 = 6916013) B6916013
theorem B4102771 : Blo 1619008 4102771 := bstep (se 1 (by rfl) ⟨3077078, by rfl⟩ : syracuseStep 4102771 = 6154157) B6154157
theorem B1620615 : Blo 1619008 1620615 := bstep (se 1 (by rfl) ⟨1215461, by rfl⟩ : syracuseStep 1620615 = 2430923) B2430923
theorem B1620623 : Blo 1619008 1620623 := bstep (se 1 (by rfl) ⟨1215467, by rfl⟩ : syracuseStep 1620623 = 2430935) B2430935
theorem B1620667 : Blo 1619008 1620667 := bstep (se 1 (by rfl) ⟨1215500, by rfl⟩ : syracuseStep 1620667 = 2431001) B2431001
theorem B4102913 : Blo 1619008 4102913 := bstep (se 2 (by rfl) ⟨1538592, by rfl⟩ : syracuseStep 4102913 = 3077185) B3077185
theorem B1620743 : Blo 1619008 1620743 := bstep (se 1 (by rfl) ⟨1215557, by rfl⟩ : syracuseStep 1620743 = 2431115) B2431115
theorem B1620751 : Blo 1619008 1620751 := bstep (se 1 (by rfl) ⟨1215563, by rfl⟩ : syracuseStep 1620751 = 2431127) B2431127
theorem B1620795 : Blo 1619008 1620795 := bstep (se 1 (by rfl) ⟨1215596, by rfl⟩ : syracuseStep 1620795 = 2431193) B2431193
theorem B3644279 : Blo 1619008 3644279 := bstep (se 1 (by rfl) ⟨2733209, by rfl⟩ : syracuseStep 3644279 = 5466419) B5466419
theorem B1620871 : Blo 1619008 1620871 := bstep (se 1 (by rfl) ⟨1215653, by rfl⟩ : syracuseStep 1620871 = 2431307) B2431307
theorem B1620879 : Blo 1619008 1620879 := bstep (se 1 (by rfl) ⟨1215659, by rfl⟩ : syracuseStep 1620879 = 2431319) B2431319
theorem B5839769 : Blo 1619008 5839769 := bstep (se 2 (by rfl) ⟨2189913, by rfl⟩ : syracuseStep 5839769 = 4379827) B4379827
theorem B1620923 : Blo 1619008 1620923 := bstep (se 1 (by rfl) ⟨1215692, by rfl⟩ : syracuseStep 1620923 = 2431385) B2431385
theorem B1620999 : Blo 1619008 1620999 := bstep (se 1 (by rfl) ⟨1215749, by rfl⟩ : syracuseStep 1620999 = 2431499) B2431499
theorem B1621007 : Blo 1619008 1621007 := bstep (se 1 (by rfl) ⟨1215755, by rfl⟩ : syracuseStep 1621007 = 2431511) B2431511
theorem B3644459 : Blo 1619008 3644459 := bstep (se 1 (by rfl) ⟨2733344, by rfl⟩ : syracuseStep 3644459 = 5466689) B5466689
theorem B6151211 : Blo 1619008 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B2735147 : Blo 1619008 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B4611131 : Blo 1619008 4611131 := bstep (se 1 (by rfl) ⟨3458348, by rfl⟩ : syracuseStep 4611131 = 6916697) B6916697
theorem B17505341 : Blo 1619008 17505341 := bstep (se 3 (by rfl) ⟨3282251, by rfl⟩ : syracuseStep 17505341 = 6564503) B6564503
theorem B7781437 : Blo 1619008 7781437 := bstep (se 3 (by rfl) ⟨1459019, by rfl⟩ : syracuseStep 7781437 = 2918039) B2918039
theorem B4996183 : Blo 1619008 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B3284239 : Blo 1619008 3284239 := bstep (se 1 (by rfl) ⟨2463179, by rfl⟩ : syracuseStep 3284239 = 4926359) B4926359
theorem B3644819 : Blo 1619008 3644819 := bstep (se 1 (by rfl) ⟨2733614, by rfl⟩ : syracuseStep 3644819 = 5467229) B5467229
theorem B3890585 : Blo 1619008 3890585 := bstep (se 2 (by rfl) ⟨1458969, by rfl⟩ : syracuseStep 3890585 = 2917939) B2917939
theorem B3644873 : Blo 1619008 3644873 := bstep (se 2 (by rfl) ⟨1366827, by rfl⟩ : syracuseStep 3644873 = 2733655) B2733655
theorem B9854417 : Blo 1619008 9854417 := bstep (se 2 (by rfl) ⟨3695406, by rfl⟩ : syracuseStep 9854417 = 7390813) B7390813
theorem B3694139 : Blo 1619008 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B12295799 : Blo 1619008 12295799 := bstep (se 1 (by rfl) ⟨9221849, by rfl⟩ : syracuseStep 12295799 = 18443699) B18443699
theorem B9346931 : Blo 1619008 9346931 := bstep (se 1 (by rfl) ⟨7010198, by rfl⟩ : syracuseStep 9346931 = 14020397) B14020397
theorem B12304547 : Blo 1619008 12304547 := bstep (se 1 (by rfl) ⟨9228410, by rfl⟩ : syracuseStep 12304547 = 18456821) B18456821
theorem B3645611 : Blo 1619008 3645611 := bstep (se 1 (by rfl) ⟨2734208, by rfl⟩ : syracuseStep 3645611 = 5468417) B5468417
theorem B5841067 : Blo 1619008 5841067 := bstep (se 1 (by rfl) ⟨4380800, by rfl⟩ : syracuseStep 5841067 = 8761601) B8761601
theorem B11993473 : Blo 1619008 11993473 := bstep (se 2 (by rfl) ⟨4497552, by rfl⟩ : syracuseStep 11993473 = 8995105) B8995105
theorem B1729063 : Blo 1619008 1729063 := bstep (se 1 (by rfl) ⟨1296797, by rfl⟩ : syracuseStep 1729063 = 2593595) B2593595
theorem B8200763 : Blo 1619008 8200763 := bstep (se 1 (by rfl) ⟨6150572, by rfl⟩ : syracuseStep 8200763 = 12301145) B12301145
theorem B9355961 : Blo 1619008 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B3646151 : Blo 1619008 3646151 := bstep (se 1 (by rfl) ⟨2734613, by rfl⟩ : syracuseStep 3646151 = 5469227) B5469227
theorem B9478865 : Blo 1619008 9478865 := bstep (se 2 (by rfl) ⟨3554574, by rfl⟩ : syracuseStep 9478865 = 7109149) B7109149
theorem B12477331 : Blo 1619008 12477331 := bstep (se 1 (by rfl) ⟨9357998, by rfl⟩ : syracuseStep 12477331 = 18715997) B18715997
theorem B5465015 : Blo 1619008 5465015 := bstep (se 1 (by rfl) ⟨4098761, by rfl⟩ : syracuseStep 5465015 = 8197523) B8197523
theorem B8201411 : Blo 1619008 8201411 := bstep (se 1 (by rfl) ⟨6151058, by rfl⟩ : syracuseStep 8201411 = 12302117) B12302117
theorem B11830475 : Blo 1619008 11830475 := bstep (se 1 (by rfl) ⟨8872856, by rfl⟩ : syracuseStep 11830475 = 17745713) B17745713
theorem B10380581 : Blo 1619008 10380581 := bstep (se 4 (by rfl) ⟨973179, by rfl⟩ : syracuseStep 10380581 = 1946359) B1946359
theorem B6661577 : Blo 1619008 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B35046917 : Blo 1619008 35046917 := bstep (se 4 (by rfl) ⟨3285648, by rfl⟩ : syracuseStep 35046917 = 6571297) B6571297
theorem B5465609 : Blo 1619008 5465609 := bstep (se 2 (by rfl) ⟨2049603, by rfl⟩ : syracuseStep 5465609 = 4099207) B4099207
theorem B3647015 : Blo 1619008 3647015 := bstep (se 1 (by rfl) ⟨2735261, by rfl⟩ : syracuseStep 3647015 = 5470523) B5470523
theorem B6571655 : Blo 1619008 6571655 := bstep (se 1 (by rfl) ⟨4928741, by rfl⟩ : syracuseStep 6571655 = 9857483) B9857483
theorem B14419603 : Blo 1619008 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B6915773 : Blo 1619008 6915773 := bstep (se 3 (by rfl) ⟨1296707, by rfl⟩ : syracuseStep 6915773 = 2593415) B2593415
theorem B4613831 : Blo 1619008 4613831 := bstep (se 1 (by rfl) ⟨3460373, by rfl⟩ : syracuseStep 4613831 = 6920747) B6920747
theorem B4155095 : Blo 1619008 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B13838039 : Blo 1619008 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B3073783 : Blo 1619008 3073783 := bstep (se 1 (by rfl) ⟨2305337, by rfl⟩ : syracuseStep 3073783 = 4610675) B4610675
theorem B3458809 : Blo 1619008 3458809 := bstep (se 2 (by rfl) ⟨1297053, by rfl⟩ : syracuseStep 3458809 = 2594107) B2594107
theorem B8308547 : Blo 1619008 8308547 := bstep (se 1 (by rfl) ⟨6231410, by rfl⟩ : syracuseStep 8308547 = 12462821) B12462821
theorem B2049887 : Blo 1619008 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B3893179 : Blo 1619008 3893179 := bstep (se 1 (by rfl) ⟨2919884, by rfl⟩ : syracuseStep 3893179 = 5839769) B5839769
theorem B3074087 : Blo 1619008 3074087 := bstep (se 1 (by rfl) ⟨2305565, by rfl⟩ : syracuseStep 3074087 = 4611131) B4611131
theorem B3893305 : Blo 1619008 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B5466473 : Blo 1619008 5466473 := bstep (se 2 (by rfl) ⟨2049927, by rfl⟩ : syracuseStep 5466473 = 4099855) B4099855
theorem B20769209 : Blo 1619008 20769209 := bstep (se 2 (by rfl) ⟨7788453, by rfl⟩ : syracuseStep 20769209 = 15576907) B15576907
theorem B12306977 : Blo 1619008 12306977 := bstep (se 2 (by rfl) ⟨4615116, by rfl⟩ : syracuseStep 12306977 = 9230233) B9230233
theorem B18450989 : Blo 1619008 18450989 := bstep (se 3 (by rfl) ⟨3459560, by rfl⟩ : syracuseStep 18450989 = 6919121) B6919121
theorem B52546229 : Blo 1619008 52546229 := bstep (se 5 (by rfl) ⟨2463104, by rfl⟩ : syracuseStep 52546229 = 4926209) B4926209
theorem B50547401 : Blo 1619008 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B5835473 : Blo 1619008 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B336579299 : Blo 1619008 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B5614409 : Blo 1619008 5614409 := bstep (se 2 (by rfl) ⟨2105403, by rfl⟩ : syracuseStep 5614409 = 4210807) B4210807
theorem B5467067 : Blo 1619008 5467067 := bstep (se 1 (by rfl) ⟨4100300, by rfl⟩ : syracuseStep 5467067 = 8200601) B8200601
theorem B6237199 : Blo 1619008 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B1821775 : Blo 1619008 1821775 := bstep (se 1 (by rfl) ⟨1366331, by rfl⟩ : syracuseStep 1821775 = 2732663) B2732663
theorem B1641551 : Blo 1619008 1641551 := bstep (se 1 (by rfl) ⟨1231163, by rfl⟩ : syracuseStep 1641551 = 2462327) B2462327
theorem B21335213 : Blo 1619008 21335213 := bstep (se 3 (by rfl) ⟨4000352, by rfl⟩ : syracuseStep 21335213 = 8000705) B8000705
theorem B4099319 : Blo 1619008 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B5188855 : Blo 1619008 5188855 := bstep (se 1 (by rfl) ⟨3891641, by rfl⟩ : syracuseStep 5188855 = 7783283) B7783283
theorem B3075401 : Blo 1619008 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B10382681 : Blo 1619008 10382681 := bstep (se 2 (by rfl) ⟨3893505, by rfl⟩ : syracuseStep 10382681 = 7787011) B7787011
theorem B4926845 : Blo 1619008 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B1822171 : Blo 1619008 1822171 := bstep (se 1 (by rfl) ⟨1366628, by rfl⟩ : syracuseStep 1822171 = 2733257) B2733257
theorem B39415517 : Blo 1619008 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B3075833 : Blo 1619008 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B8761081 : Blo 1619008 8761081 := bstep (se 2 (by rfl) ⟨3285405, by rfl⟩ : syracuseStep 8761081 = 6570811) B6570811
theorem B5189471 : Blo 1619008 5189471 := bstep (se 1 (by rfl) ⟨3892103, by rfl⟩ : syracuseStep 5189471 = 7784207) B7784207
theorem B2428847 : Blo 1619008 2428847 := bstep (se 1 (by rfl) ⟨1821635, by rfl⟩ : syracuseStep 2428847 = 3643271) B3643271
theorem B1822639 : Blo 1619008 1822639 := bstep (se 1 (by rfl) ⟨1366979, by rfl⟩ : syracuseStep 1822639 = 2733959) B2733959
theorem B2428937 : Blo 1619008 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B7393295 : Blo 1619008 7393295 := bstep (se 1 (by rfl) ⟨5544971, by rfl⟩ : syracuseStep 7393295 = 11089943) B11089943
theorem B2428967 : Blo 1619008 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B2732089 : Blo 1619008 2732089 := bstep (se 2 (by rfl) ⟨1024533, by rfl⟩ : syracuseStep 2732089 = 2049067) B2049067
theorem B10375249 : Blo 1619008 10375249 := bstep (se 2 (by rfl) ⟨3890718, by rfl⟩ : syracuseStep 10375249 = 7781437) B7781437
theorem B2429051 : Blo 1619008 2429051 := bstep (se 1 (by rfl) ⟨1821788, by rfl⟩ : syracuseStep 2429051 = 3643577) B3643577
theorem B6918301 : Blo 1619008 6918301 := bstep (se 3 (by rfl) ⟨1297181, by rfl⟩ : syracuseStep 6918301 = 2594363) B2594363
theorem B2920619 : Blo 1619008 2920619 := bstep (se 1 (by rfl) ⟨2190464, by rfl⟩ : syracuseStep 2920619 = 4380929) B4380929
theorem B2732231 : Blo 1619008 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B2429177 : Blo 1619008 2429177 := bstep (se 2 (by rfl) ⟨910941, by rfl⟩ : syracuseStep 2429177 = 1821883) B1821883
theorem B2429279 : Blo 1619008 2429279 := bstep (se 1 (by rfl) ⟨1821959, by rfl⟩ : syracuseStep 2429279 = 3643919) B3643919
theorem B1823071 : Blo 1619008 1823071 := bstep (se 1 (by rfl) ⟨1367303, by rfl⟩ : syracuseStep 1823071 = 2734607) B2734607
theorem B2732393 : Blo 1619008 2732393 := bstep (se 2 (by rfl) ⟨1024647, by rfl⟩ : syracuseStep 2732393 = 2049295) B2049295
theorem B4378985 : Blo 1619008 4378985 := bstep (se 2 (by rfl) ⟨1642119, by rfl⟩ : syracuseStep 4378985 = 3284239) B3284239
theorem B2429291 : Blo 1619008 2429291 := bstep (se 1 (by rfl) ⟨1821968, by rfl⟩ : syracuseStep 2429291 = 3643937) B3643937
theorem B2429519 : Blo 1619008 2429519 := bstep (se 1 (by rfl) ⟨1822139, by rfl⟩ : syracuseStep 2429519 = 3644279) B3644279
theorem B1946191 : Blo 1619008 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B35041891 : Blo 1619008 35041891 := bstep (se 1 (by rfl) ⟨26281418, by rfl⟩ : syracuseStep 35041891 = 52562837) B52562837
theorem B5468795 : Blo 1619008 5468795 := bstep (se 1 (by rfl) ⟨4101596, by rfl⟩ : syracuseStep 5468795 = 8203193) B8203193
theorem B2847403 : Blo 1619008 2847403 := bstep (se 1 (by rfl) ⟨2135552, by rfl⟩ : syracuseStep 2847403 = 4271105) B4271105
theorem B15782573 : Blo 1619008 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B2429639 : Blo 1619008 2429639 := bstep (se 1 (by rfl) ⟨1822229, by rfl⟩ : syracuseStep 2429639 = 3644459) B3644459
theorem B4100807 : Blo 1619008 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B1823431 : Blo 1619008 1823431 := bstep (se 1 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 1823431 = 2735147) B2735147
theorem B11670227 : Blo 1619008 11670227 := bstep (se 1 (by rfl) ⟨8752670, by rfl⟩ : syracuseStep 11670227 = 17505341) B17505341
theorem B2732791 : Blo 1619008 2732791 := bstep (se 1 (by rfl) ⟨2049593, by rfl⟩ : syracuseStep 2732791 = 4099187) B4099187
theorem B5468957 : Blo 1619008 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B13144861 : Blo 1619008 13144861 := bstep (se 3 (by rfl) ⟨2464661, by rfl⟩ : syracuseStep 13144861 = 4929323) B4929323
theorem B6566723 : Blo 1619008 6566723 := bstep (se 1 (by rfl) ⟨4925042, by rfl⟩ : syracuseStep 6566723 = 9850085) B9850085
theorem B2429801 : Blo 1619008 2429801 := bstep (se 2 (by rfl) ⟨911175, by rfl⟩ : syracuseStep 2429801 = 1822351) B1822351
theorem B2429879 : Blo 1619008 2429879 := bstep (se 1 (by rfl) ⟨1822409, by rfl⟩ : syracuseStep 2429879 = 3644819) B3644819
theorem B2593723 : Blo 1619008 2593723 := bstep (se 1 (by rfl) ⟨1945292, by rfl⟩ : syracuseStep 2593723 = 3890585) B3890585
theorem B2732987 : Blo 1619008 2732987 := bstep (se 1 (by rfl) ⟨2049740, by rfl⟩ : syracuseStep 2732987 = 4099481) B4099481
theorem B2429915 : Blo 1619008 2429915 := bstep (se 1 (by rfl) ⟨1822436, by rfl⟩ : syracuseStep 2429915 = 3644873) B3644873
theorem B2733095 : Blo 1619008 2733095 := bstep (se 1 (by rfl) ⟨2049821, by rfl⟩ : syracuseStep 2733095 = 4099643) B4099643
theorem B2462759 : Blo 1619008 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B89887805 : Blo 1619008 89887805 := bstep (se 3 (by rfl) ⟨16853963, by rfl⟩ : syracuseStep 89887805 = 33707927) B33707927
theorem B1619023 : Blo 1619008 1619023 := bstep (se 1 (by rfl) ⟨1214267, by rfl⟩ : syracuseStep 1619023 = 2428535) B2428535
theorem B8197199 : Blo 1619008 8197199 := bstep (se 1 (by rfl) ⟨6147899, by rfl⟩ : syracuseStep 8197199 = 12295799) B12295799
theorem B1619039 : Blo 1619008 1619039 := bstep (se 1 (by rfl) ⟨1214279, by rfl⟩ : syracuseStep 1619039 = 2428559) B2428559
theorem B1619067 : Blo 1619008 1619067 := bstep (se 1 (by rfl) ⟨1214300, by rfl⟩ : syracuseStep 1619067 = 2428601) B2428601
theorem B3077291 : Blo 1619008 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B1619119 : Blo 1619008 1619119 := bstep (se 1 (by rfl) ⟨1214339, by rfl⟩ : syracuseStep 1619119 = 2428679) B2428679
theorem B1619143 : Blo 1619008 1619143 := bstep (se 1 (by rfl) ⟨1214357, by rfl⟩ : syracuseStep 1619143 = 2428715) B2428715
theorem B1619163 : Blo 1619008 1619163 := bstep (se 1 (by rfl) ⟨1214372, by rfl⟩ : syracuseStep 1619163 = 2428745) B2428745
theorem B6231287 : Blo 1619008 6231287 := bstep (se 1 (by rfl) ⟨4673465, by rfl⟩ : syracuseStep 6231287 = 9346931) B9346931
theorem B1619239 : Blo 1619008 1619239 := bstep (se 1 (by rfl) ⟨1214429, by rfl⟩ : syracuseStep 1619239 = 2428859) B2428859
theorem B2733385 : Blo 1619008 2733385 := bstep (se 2 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 2733385 = 2050039) B2050039
theorem B1619279 : Blo 1619008 1619279 := bstep (se 1 (by rfl) ⟨1214459, by rfl⟩ : syracuseStep 1619279 = 2428919) B2428919
theorem B1619295 : Blo 1619008 1619295 := bstep (se 1 (by rfl) ⟨1214471, by rfl⟩ : syracuseStep 1619295 = 2428943) B2428943
theorem B2733419 : Blo 1619008 2733419 := bstep (se 1 (by rfl) ⟨2050064, by rfl⟩ : syracuseStep 2733419 = 4100129) B4100129
theorem B1619323 : Blo 1619008 1619323 := bstep (se 1 (by rfl) ⟨1214492, by rfl⟩ : syracuseStep 1619323 = 2428985) B2428985
theorem B9229733 : Blo 1619008 9229733 := bstep (se 4 (by rfl) ⟨865287, by rfl⟩ : syracuseStep 9229733 = 1730575) B1730575
theorem B1619375 : Blo 1619008 1619375 := bstep (se 1 (by rfl) ⟨1214531, by rfl⟩ : syracuseStep 1619375 = 2429063) B2429063
theorem B2430383 : Blo 1619008 2430383 := bstep (se 1 (by rfl) ⟨1822787, by rfl⟩ : syracuseStep 2430383 = 3645575) B3645575
theorem B1619399 : Blo 1619008 1619399 := bstep (se 1 (by rfl) ⟨1214549, by rfl⟩ : syracuseStep 1619399 = 2429099) B2429099
theorem B1619419 : Blo 1619008 1619419 := bstep (se 1 (by rfl) ⟨1214564, by rfl⟩ : syracuseStep 1619419 = 2429129) B2429129
theorem B5469659 : Blo 1619008 5469659 := bstep (se 1 (by rfl) ⟨4102244, by rfl⟩ : syracuseStep 5469659 = 8204489) B8204489
theorem B184612337 : Blo 1619008 184612337 := bstep (se 2 (by rfl) ⟨69229626, by rfl⟩ : syracuseStep 184612337 = 138459253) B138459253
theorem B2430473 : Blo 1619008 2430473 := bstep (se 2 (by rfl) ⟨911427, by rfl⟩ : syracuseStep 2430473 = 1822855) B1822855
theorem B1619495 : Blo 1619008 1619495 := bstep (se 1 (by rfl) ⟨1214621, by rfl⟩ : syracuseStep 1619495 = 2429243) B2429243
theorem B2430503 : Blo 1619008 2430503 := bstep (se 1 (by rfl) ⟨1822877, by rfl⟩ : syracuseStep 2430503 = 3645755) B3645755
theorem B1619535 : Blo 1619008 1619535 := bstep (se 1 (by rfl) ⟨1214651, by rfl⟩ : syracuseStep 1619535 = 2429303) B2429303
theorem B1619551 : Blo 1619008 1619551 := bstep (se 1 (by rfl) ⟨1214663, by rfl⟩ : syracuseStep 1619551 = 2429327) B2429327
theorem B1619579 : Blo 1619008 1619579 := bstep (se 1 (by rfl) ⟨1214684, by rfl⟩ : syracuseStep 1619579 = 2429369) B2429369
theorem B2430587 : Blo 1619008 2430587 := bstep (se 1 (by rfl) ⟨1822940, by rfl⟩ : syracuseStep 2430587 = 3645881) B3645881
theorem B1619631 : Blo 1619008 1619631 := bstep (se 1 (by rfl) ⟨1214723, by rfl⟩ : syracuseStep 1619631 = 2429447) B2429447
theorem B1619655 : Blo 1619008 1619655 := bstep (se 1 (by rfl) ⟨1214741, by rfl⟩ : syracuseStep 1619655 = 2429483) B2429483
theorem B3643091 : Blo 1619008 3643091 := bstep (se 1 (by rfl) ⟨2732318, by rfl⟩ : syracuseStep 3643091 = 5464637) B5464637
theorem B8197847 : Blo 1619008 8197847 := bstep (se 1 (by rfl) ⟨6148385, by rfl⟩ : syracuseStep 8197847 = 12296771) B12296771
theorem B1619675 : Blo 1619008 1619675 := bstep (se 1 (by rfl) ⟨1214756, by rfl⟩ : syracuseStep 1619675 = 2429513) B2429513
theorem B2733817 : Blo 1619008 2733817 := bstep (se 2 (by rfl) ⟨1025181, by rfl⟩ : syracuseStep 2733817 = 2050363) B2050363
theorem B2430713 : Blo 1619008 2430713 := bstep (se 2 (by rfl) ⟨911517, by rfl⟩ : syracuseStep 2430713 = 1823035) B1823035
theorem B1619751 : Blo 1619008 1619751 := bstep (se 1 (by rfl) ⟨1214813, by rfl⟩ : syracuseStep 1619751 = 2429627) B2429627
theorem B4101961 : Blo 1619008 4101961 := bstep (se 2 (by rfl) ⟨1538235, by rfl⟩ : syracuseStep 4101961 = 3076471) B3076471
theorem B1619791 : Blo 1619008 1619791 := bstep (se 1 (by rfl) ⟨1214843, by rfl⟩ : syracuseStep 1619791 = 2429687) B2429687
theorem B1619807 : Blo 1619008 1619807 := bstep (se 1 (by rfl) ⟨1214855, by rfl⟩ : syracuseStep 1619807 = 2429711) B2429711
theorem B2430815 : Blo 1619008 2430815 := bstep (se 1 (by rfl) ⟨1823111, by rfl⟩ : syracuseStep 2430815 = 3646223) B3646223
theorem B2430827 : Blo 1619008 2430827 := bstep (se 1 (by rfl) ⟨1823120, by rfl⟩ : syracuseStep 2430827 = 3646241) B3646241
theorem B1619835 : Blo 1619008 1619835 := bstep (se 1 (by rfl) ⟨1214876, by rfl⟩ : syracuseStep 1619835 = 2429753) B2429753
theorem B1619887 : Blo 1619008 1619887 := bstep (se 1 (by rfl) ⟨1214915, by rfl⟩ : syracuseStep 1619887 = 2429831) B2429831
theorem B1619911 : Blo 1619008 1619911 := bstep (se 1 (by rfl) ⟨1214933, by rfl⟩ : syracuseStep 1619911 = 2429867) B2429867
theorem B1619931 : Blo 1619008 1619931 := bstep (se 1 (by rfl) ⟨1214948, by rfl⟩ : syracuseStep 1619931 = 2429897) B2429897
theorem B2734087 : Blo 1619008 2734087 := bstep (se 1 (by rfl) ⟨2050565, by rfl⟩ : syracuseStep 2734087 = 4101131) B4101131
theorem B2594825 : Blo 1619008 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B1620007 : Blo 1619008 1620007 := bstep (se 1 (by rfl) ⟨1215005, by rfl⟩ : syracuseStep 1620007 = 2430011) B2430011
theorem B11671609 : Blo 1619008 11671609 := bstep (se 2 (by rfl) ⟨4376853, by rfl⟩ : syracuseStep 11671609 = 8753707) B8753707
theorem B1620047 : Blo 1619008 1620047 := bstep (se 1 (by rfl) ⟨1215035, by rfl⟩ : syracuseStep 1620047 = 2430071) B2430071
theorem B2431055 : Blo 1619008 2431055 := bstep (se 1 (by rfl) ⟨1823291, by rfl⟩ : syracuseStep 2431055 = 3646583) B3646583
theorem B1620063 : Blo 1619008 1620063 := bstep (se 1 (by rfl) ⟨1215047, by rfl⟩ : syracuseStep 1620063 = 2430095) B2430095
theorem B5920883 : Blo 1619008 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B1620091 : Blo 1619008 1620091 := bstep (se 1 (by rfl) ⟨1215068, by rfl⟩ : syracuseStep 1620091 = 2430137) B2430137
theorem B5470361 : Blo 1619008 5470361 := bstep (se 2 (by rfl) ⟨2051385, by rfl⟩ : syracuseStep 5470361 = 4102771) B4102771
theorem B1620143 : Blo 1619008 1620143 := bstep (se 1 (by rfl) ⟨1215107, by rfl⟩ : syracuseStep 1620143 = 2430215) B2430215
theorem B1620167 : Blo 1619008 1620167 := bstep (se 1 (by rfl) ⟨1215125, by rfl⟩ : syracuseStep 1620167 = 2430251) B2430251
theorem B2431175 : Blo 1619008 2431175 := bstep (se 1 (by rfl) ⟨1823381, by rfl⟩ : syracuseStep 2431175 = 3646763) B3646763
theorem B1620187 : Blo 1619008 1620187 := bstep (se 1 (by rfl) ⟨1215140, by rfl⟩ : syracuseStep 1620187 = 2430281) B2430281
theorem B12302603 : Blo 1619008 12302603 := bstep (se 1 (by rfl) ⟨9226952, by rfl⟩ : syracuseStep 12302603 = 18453905) B18453905
theorem B1620263 : Blo 1619008 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B1620303 : Blo 1619008 1620303 := bstep (se 1 (by rfl) ⟨1215227, by rfl⟩ : syracuseStep 1620303 = 2430455) B2430455
theorem B1620319 : Blo 1619008 1620319 := bstep (se 1 (by rfl) ⟨1215239, by rfl⟩ : syracuseStep 1620319 = 2430479) B2430479
theorem B2431337 : Blo 1619008 2431337 := bstep (se 2 (by rfl) ⟨911751, by rfl⟩ : syracuseStep 2431337 = 1823503) B1823503
theorem B1620347 : Blo 1619008 1620347 := bstep (se 1 (by rfl) ⟨1215260, by rfl⟩ : syracuseStep 1620347 = 2430521) B2430521
theorem B1620399 : Blo 1619008 1620399 := bstep (se 1 (by rfl) ⟨1215299, by rfl⟩ : syracuseStep 1620399 = 2430599) B2430599
theorem B2734519 : Blo 1619008 2734519 := bstep (se 1 (by rfl) ⟨2050889, by rfl⟩ : syracuseStep 2734519 = 4101779) B4101779
theorem B2431415 : Blo 1619008 2431415 := bstep (se 1 (by rfl) ⟨1823561, by rfl⟩ : syracuseStep 2431415 = 3647123) B3647123
theorem B1620423 : Blo 1619008 1620423 := bstep (se 1 (by rfl) ⟨1215317, by rfl⟩ : syracuseStep 1620423 = 2430635) B2430635
theorem B6568411 : Blo 1619008 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B1620443 : Blo 1619008 1620443 := bstep (se 1 (by rfl) ⟨1215332, by rfl⟩ : syracuseStep 1620443 = 2430665) B2430665
theorem B2431451 : Blo 1619008 2431451 := bstep (se 1 (by rfl) ⟨1823588, by rfl⟩ : syracuseStep 2431451 = 3647177) B3647177
theorem B11082221 : Blo 1619008 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B6232585 : Blo 1619008 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B5192201 : Blo 1619008 5192201 := bstep (se 2 (by rfl) ⟨1947075, by rfl⟩ : syracuseStep 5192201 = 3894151) B3894151
theorem B8205947 : Blo 1619008 8205947 := bstep (se 1 (by rfl) ⟨6154460, by rfl⟩ : syracuseStep 8205947 = 12308921) B12308921
theorem B5839393 : Blo 1619008 5839393 := bstep (se 2 (by rfl) ⟨2189772, by rfl⟩ : syracuseStep 5839393 = 4379545) B4379545
theorem B1620519 : Blo 1619008 1620519 := bstep (se 1 (by rfl) ⟨1215389, by rfl⟩ : syracuseStep 1620519 = 2430779) B2430779
theorem B26278445 : Blo 1619008 26278445 := bstep (se 3 (by rfl) ⟨4927208, by rfl⟩ : syracuseStep 26278445 = 9854417) B9854417
theorem B1620559 : Blo 1619008 1620559 := bstep (se 1 (by rfl) ⟨1215419, by rfl⟩ : syracuseStep 1620559 = 2430839) B2430839
theorem B1620575 : Blo 1619008 1620575 := bstep (se 1 (by rfl) ⟨1215431, by rfl⟩ : syracuseStep 1620575 = 2430863) B2430863
theorem B3644027 : Blo 1619008 3644027 := bstep (se 1 (by rfl) ⟨2733020, by rfl⟩ : syracuseStep 3644027 = 5466041) B5466041
theorem B2734715 : Blo 1619008 2734715 := bstep (se 1 (by rfl) ⟨2051036, by rfl⟩ : syracuseStep 2734715 = 4102073) B4102073
theorem B1620603 : Blo 1619008 1620603 := bstep (se 1 (by rfl) ⟨1215452, by rfl⟩ : syracuseStep 1620603 = 2430905) B2430905
theorem B5192315 : Blo 1619008 5192315 := bstep (se 1 (by rfl) ⟨3894236, by rfl⟩ : syracuseStep 5192315 = 7788473) B7788473
theorem B1620655 : Blo 1619008 1620655 := bstep (se 1 (by rfl) ⟨1215491, by rfl⟩ : syracuseStep 1620655 = 2430983) B2430983
theorem B1620679 : Blo 1619008 1620679 := bstep (se 1 (by rfl) ⟨1215509, by rfl⟩ : syracuseStep 1620679 = 2431019) B2431019
theorem B1620699 : Blo 1619008 1620699 := bstep (se 1 (by rfl) ⟨1215524, by rfl⟩ : syracuseStep 1620699 = 2431049) B2431049
theorem B3644153 : Blo 1619008 3644153 := bstep (se 2 (by rfl) ⟨1366557, by rfl⟩ : syracuseStep 3644153 = 2733115) B2733115
theorem B1620775 : Blo 1619008 1620775 := bstep (se 1 (by rfl) ⟨1215581, by rfl⟩ : syracuseStep 1620775 = 2431163) B2431163
theorem B1620815 : Blo 1619008 1620815 := bstep (se 1 (by rfl) ⟨1215611, by rfl⟩ : syracuseStep 1620815 = 2431223) B2431223
theorem B1620831 : Blo 1619008 1620831 := bstep (se 1 (by rfl) ⟨1215623, by rfl⟩ : syracuseStep 1620831 = 2431247) B2431247
theorem B1620859 : Blo 1619008 1620859 := bstep (se 1 (by rfl) ⟨1215644, by rfl⟩ : syracuseStep 1620859 = 2431289) B2431289
theorem B1620911 : Blo 1619008 1620911 := bstep (se 1 (by rfl) ⟨1215683, by rfl⟩ : syracuseStep 1620911 = 2431367) B2431367
theorem B4103095 : Blo 1619008 4103095 := bstep (se 1 (by rfl) ⟨3077321, by rfl⟩ : syracuseStep 4103095 = 6154643) B6154643
theorem B1620935 : Blo 1619008 1620935 := bstep (se 1 (by rfl) ⟨1215701, by rfl⟩ : syracuseStep 1620935 = 2431403) B2431403
theorem B1620955 : Blo 1619008 1620955 := bstep (se 1 (by rfl) ⟨1215716, by rfl⟩ : syracuseStep 1620955 = 2431433) B2431433
theorem B3644423 : Blo 1619008 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B2735113 : Blo 1619008 2735113 := bstep (se 2 (by rfl) ⟨1025667, by rfl⟩ : syracuseStep 2735113 = 2051335) B2051335
theorem B3644495 : Blo 1619008 3644495 := bstep (se 1 (by rfl) ⟨2733371, by rfl⟩ : syracuseStep 3644495 = 5466743) B5466743
theorem B2735275 : Blo 1619008 2735275 := bstep (se 1 (by rfl) ⟨2051456, by rfl⟩ : syracuseStep 2735275 = 4102913) B4102913
theorem B3644891 : Blo 1619008 3644891 := bstep (se 1 (by rfl) ⟨2733668, by rfl⟩ : syracuseStep 3644891 = 5467337) B5467337
theorem B13319741 : Blo 1619008 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B12304061 : Blo 1619008 12304061 := bstep (se 3 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 12304061 = 4614023) B4614023
theorem B6151895 : Blo 1619008 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B9223901 : Blo 1619008 9223901 := bstep (se 3 (by rfl) ⟨1729481, by rfl⟩ : syracuseStep 9223901 = 3458963) B3458963
theorem B13131629 : Blo 1619008 13131629 := bstep (se 3 (by rfl) ⟨2462180, by rfl⟩ : syracuseStep 13131629 = 4924361) B4924361
theorem B3645359 : Blo 1619008 3645359 := bstep (se 1 (by rfl) ⟨2734019, by rfl⟩ : syracuseStep 3645359 = 5468039) B5468039
theorem B3645449 : Blo 1619008 3645449 := bstep (se 2 (by rfl) ⟨1367043, by rfl⟩ : syracuseStep 3645449 = 2734087) B2734087
theorem B9224401 : Blo 1619008 9224401 := bstep (se 2 (by rfl) ⟨3459150, by rfl⟩ : syracuseStep 9224401 = 6918301) B6918301
theorem B3645863 : Blo 1619008 3645863 := bstep (se 1 (by rfl) ⟨2734397, by rfl⟩ : syracuseStep 3645863 = 5468795) B5468795
theorem B3645971 : Blo 1619008 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B3646025 : Blo 1619008 3646025 := bstep (se 2 (by rfl) ⟨1367259, by rfl⟩ : syracuseStep 3646025 = 2734519) B2734519
theorem B8757881 : Blo 1619008 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B59925203 : Blo 1619008 59925203 := bstep (se 1 (by rfl) ⟨44943902, by rfl⟩ : syracuseStep 59925203 = 89887805) B89887805
theorem B5464799 : Blo 1619008 5464799 := bstep (se 1 (by rfl) ⟨4098599, by rfl⟩ : syracuseStep 5464799 = 8197199) B8197199
theorem B6153155 : Blo 1619008 6153155 := bstep (se 1 (by rfl) ⟨4614866, by rfl⟩ : syracuseStep 6153155 = 9229733) B9229733
theorem B4441051 : Blo 1619008 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B3646439 : Blo 1619008 3646439 := bstep (se 1 (by rfl) ⟨2734829, by rfl⟩ : syracuseStep 3646439 = 5469659) B5469659
theorem B23364611 : Blo 1619008 23364611 := bstep (se 1 (by rfl) ⟨17523458, by rfl⟩ : syracuseStep 23364611 = 35046917) B35046917
theorem B5465231 : Blo 1619008 5465231 := bstep (se 1 (by rfl) ⟨4098923, by rfl⟩ : syracuseStep 5465231 = 8197847) B8197847
theorem B9225359 : Blo 1619008 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B5539031 : Blo 1619008 5539031 := bstep (se 1 (by rfl) ⟨4154273, by rfl⟩ : syracuseStep 5539031 = 8308547) B8308547
theorem B3458297 : Blo 1619008 3458297 := bstep (se 2 (by rfl) ⟨1296861, by rfl⟩ : syracuseStep 3458297 = 2593723) B2593723
theorem B1729883 : Blo 1619008 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B3646817 : Blo 1619008 3646817 := bstep (se 2 (by rfl) ⟨1367556, by rfl⟩ : syracuseStep 3646817 = 2735113) B2735113
theorem B8316265 : Blo 1619008 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B2049391 : Blo 1619008 2049391 := bstep (se 1 (by rfl) ⟨1537043, by rfl⟩ : syracuseStep 2049391 = 3074087) B3074087
theorem B3646907 : Blo 1619008 3646907 := bstep (se 1 (by rfl) ⟨2735180, by rfl⟩ : syracuseStep 3646907 = 5470361) B5470361
theorem B8201735 : Blo 1619008 8201735 := bstep (se 1 (by rfl) ⟨6151301, by rfl⟩ : syracuseStep 8201735 = 12302603) B12302603
theorem B3647033 : Blo 1619008 3647033 := bstep (se 2 (by rfl) ⟨1367637, by rfl⟩ : syracuseStep 3647033 = 2735275) B2735275
theorem B13846139 : Blo 1619008 13846139 := bstep (se 1 (by rfl) ⟨10384604, by rfl⟩ : syracuseStep 13846139 = 20769209) B20769209
theorem B35030819 : Blo 1619008 35030819 := bstep (se 1 (by rfl) ⟨26273114, by rfl⟩ : syracuseStep 35030819 = 52546229) B52546229
theorem B8202221 : Blo 1619008 8202221 := bstep (se 3 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 8202221 = 3075833) B3075833
theorem B63965189 : Blo 1619008 63965189 := bstep (se 4 (by rfl) ⟨5996736, by rfl⟩ : syracuseStep 63965189 = 11993473) B11993473
theorem B14223475 : Blo 1619008 14223475 := bstep (se 1 (by rfl) ⟨10667606, by rfl⟩ : syracuseStep 14223475 = 21335213) B21335213
theorem B2050267 : Blo 1619008 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B5466365 : Blo 1619008 5466365 := bstep (se 3 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 5466365 = 2049887) B2049887
theorem B4098377 : Blo 1619008 4098377 := bstep (se 2 (by rfl) ⟨1536891, by rfl⟩ : syracuseStep 4098377 = 3073783) B3073783
theorem B8202707 : Blo 1619008 8202707 := bstep (se 1 (by rfl) ⟨6152030, by rfl⟩ : syracuseStep 8202707 = 12304061) B12304061
theorem B3459647 : Blo 1619008 3459647 := bstep (se 1 (by rfl) ⟨2594735, by rfl⟩ : syracuseStep 3459647 = 5189471) B5189471
theorem B8203031 : Blo 1619008 8203031 := bstep (se 1 (by rfl) ⟨6152273, by rfl⟩ : syracuseStep 8203031 = 12304547) B12304547
theorem B1821487 : Blo 1619008 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B4377469 : Blo 1619008 4377469 := bstep (se 3 (by rfl) ⟨820775, by rfl⟩ : syracuseStep 4377469 = 1641551) B1641551
theorem B1821595 : Blo 1619008 1821595 := bstep (se 1 (by rfl) ⟨1366196, by rfl⟩ : syracuseStep 1821595 = 2732393) B2732393
theorem B2919323 : Blo 1619008 2919323 := bstep (se 1 (by rfl) ⟨2189492, by rfl⟩ : syracuseStep 2919323 = 4378985) B4378985
theorem B5467175 : Blo 1619008 5467175 := bstep (se 1 (by rfl) ⟨4100381, by rfl⟩ : syracuseStep 5467175 = 8200763) B8200763
theorem B6237307 : Blo 1619008 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B6319243 : Blo 1619008 6319243 := bstep (se 1 (by rfl) ⟨4739432, by rfl⟩ : syracuseStep 6319243 = 9478865) B9478865
theorem B4377815 : Blo 1619008 4377815 := bstep (se 1 (by rfl) ⟨3283361, by rfl⟩ : syracuseStep 4377815 = 6566723) B6566723
theorem B1821991 : Blo 1619008 1821991 := bstep (se 1 (by rfl) ⟨1366493, by rfl⟩ : syracuseStep 1821991 = 2732987) B2732987
theorem B16616765 : Blo 1619008 16616765 := bstep (se 3 (by rfl) ⟨3115643, by rfl⟩ : syracuseStep 16616765 = 6231287) B6231287
theorem B8310113 : Blo 1619008 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B1822063 : Blo 1619008 1822063 := bstep (se 1 (by rfl) ⟨1366547, by rfl⟩ : syracuseStep 1822063 = 2733095) B2733095
theorem B1641839 : Blo 1619008 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B7785857 : Blo 1619008 7785857 := bstep (se 2 (by rfl) ⟨2919696, by rfl⟩ : syracuseStep 7785857 = 5839393) B5839393
theorem B2305417 : Blo 1619008 2305417 := bstep (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) B1729063
theorem B5467607 : Blo 1619008 5467607 := bstep (se 1 (by rfl) ⟨4100705, by rfl⟩ : syracuseStep 5467607 = 8201411) B8201411
theorem B46722521 : Blo 1619008 46722521 := bstep (se 2 (by rfl) ⟨17520945, by rfl⟩ : syracuseStep 46722521 = 35041891) B35041891
theorem B1822279 : Blo 1619008 1822279 := bstep (se 1 (by rfl) ⟨1366709, by rfl⟩ : syracuseStep 1822279 = 2733419) B2733419
theorem B3075887 : Blo 1619008 3075887 := bstep (se 1 (by rfl) ⟨2306915, by rfl⟩ : syracuseStep 3075887 = 4613831) B4613831
theorem B2428727 : Blo 1619008 2428727 := bstep (se 1 (by rfl) ⟨1821545, by rfl⟩ : syracuseStep 2428727 = 3643091) B3643091
theorem B2429033 : Blo 1619008 2429033 := bstep (se 2 (by rfl) ⟨910887, by rfl⟩ : syracuseStep 2429033 = 1821775) B1821775
theorem B6918473 : Blo 1619008 6918473 := bstep (se 2 (by rfl) ⟨2594427, by rfl⟩ : syracuseStep 6918473 = 5188855) B5188855
theorem B3461467 : Blo 1619008 3461467 := bstep (se 1 (by rfl) ⟨2596100, by rfl⟩ : syracuseStep 3461467 = 5192201) B5192201
theorem B8204651 : Blo 1619008 8204651 := bstep (se 1 (by rfl) ⟨6153488, by rfl⟩ : syracuseStep 8204651 = 12306977) B12306977
theorem B12300659 : Blo 1619008 12300659 := bstep (se 1 (by rfl) ⟨9225494, by rfl⟩ : syracuseStep 12300659 = 18450989) B18450989
theorem B17518963 : Blo 1619008 17518963 := bstep (se 1 (by rfl) ⟨13139222, by rfl⟩ : syracuseStep 17518963 = 26278445) B26278445
theorem B2429351 : Blo 1619008 2429351 := bstep (se 1 (by rfl) ⟨1822013, by rfl⟩ : syracuseStep 2429351 = 3644027) B3644027
theorem B1823143 : Blo 1619008 1823143 := bstep (se 1 (by rfl) ⟨1367357, by rfl⟩ : syracuseStep 1823143 = 2734715) B2734715
theorem B3461543 : Blo 1619008 3461543 := bstep (se 1 (by rfl) ⟨2596157, by rfl⟩ : syracuseStep 3461543 = 5192315) B5192315
theorem B42086861 : Blo 1619008 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B33698267 : Blo 1619008 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B2429435 : Blo 1619008 2429435 := bstep (se 1 (by rfl) ⟨1822076, by rfl⟩ : syracuseStep 2429435 = 3644153) B3644153
theorem B11080253 : Blo 1619008 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B2429561 : Blo 1619008 2429561 := bstep (se 2 (by rfl) ⟨911085, by rfl⟩ : syracuseStep 2429561 = 1822171) B1822171
theorem B2429615 : Blo 1619008 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B2429663 : Blo 1619008 2429663 := bstep (se 1 (by rfl) ⟨1822247, by rfl⟩ : syracuseStep 2429663 = 3644495) B3644495
theorem B2732879 : Blo 1619008 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B2429927 : Blo 1619008 2429927 := bstep (se 1 (by rfl) ⟨1822445, by rfl⟩ : syracuseStep 2429927 = 3644891) B3644891
theorem B5469281 : Blo 1619008 5469281 := bstep (se 2 (by rfl) ⟨2050980, by rfl⟩ : syracuseStep 5469281 = 4101961) B4101961
theorem B4101263 : Blo 1619008 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B6149267 : Blo 1619008 6149267 := bstep (se 1 (by rfl) ⟨4611950, by rfl⟩ : syracuseStep 6149267 = 9223901) B9223901
theorem B26277011 : Blo 1619008 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B2430185 : Blo 1619008 2430185 := bstep (se 2 (by rfl) ⟨911319, by rfl⟩ : syracuseStep 2430185 = 1822639) B1822639
theorem B8754419 : Blo 1619008 8754419 := bstep (se 1 (by rfl) ⟨6565814, by rfl⟩ : syracuseStep 8754419 = 13131629) B13131629
theorem B5190905 : Blo 1619008 5190905 := bstep (se 2 (by rfl) ⟨1946589, by rfl⟩ : syracuseStep 5190905 = 3893179) B3893179
theorem B1619231 : Blo 1619008 1619231 := bstep (se 1 (by rfl) ⟨1214423, by rfl⟩ : syracuseStep 1619231 = 2428847) B2428847
theorem B2430239 : Blo 1619008 2430239 := bstep (se 1 (by rfl) ⟨1822679, by rfl⟩ : syracuseStep 2430239 = 3645359) B3645359
theorem B1619291 : Blo 1619008 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B4928863 : Blo 1619008 4928863 := bstep (se 1 (by rfl) ⟨3696647, by rfl⟩ : syracuseStep 4928863 = 7393295) B7393295
theorem B1619311 : Blo 1619008 1619311 := bstep (se 1 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 1619311 = 2428967) B2428967
theorem B3642785 : Blo 1619008 3642785 := bstep (se 2 (by rfl) ⟨1366044, by rfl⟩ : syracuseStep 3642785 = 2732089) B2732089
theorem B15562145 : Blo 1619008 15562145 := bstep (se 2 (by rfl) ⟨5835804, by rfl⟩ : syracuseStep 15562145 = 11671609) B11671609
theorem B1619367 : Blo 1619008 1619367 := bstep (se 1 (by rfl) ⟨1214525, by rfl⟩ : syracuseStep 1619367 = 2429051) B2429051
theorem B5191073 : Blo 1619008 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B13833665 : Blo 1619008 13833665 := bstep (se 2 (by rfl) ⟨5187624, by rfl⟩ : syracuseStep 13833665 = 10375249) B10375249
theorem B2430407 : Blo 1619008 2430407 := bstep (se 1 (by rfl) ⟨1822805, by rfl⟩ : syracuseStep 2430407 = 3645611) B3645611
theorem B1619451 : Blo 1619008 1619451 := bstep (se 1 (by rfl) ⟨1214588, by rfl⟩ : syracuseStep 1619451 = 2429177) B2429177
theorem B7788089 : Blo 1619008 7788089 := bstep (se 2 (by rfl) ⟨2920533, by rfl⟩ : syracuseStep 7788089 = 5841067) B5841067
theorem B1619519 : Blo 1619008 1619519 := bstep (se 1 (by rfl) ⟨1214639, by rfl⟩ : syracuseStep 1619519 = 2429279) B2429279
theorem B1619527 : Blo 1619008 1619527 := bstep (se 1 (by rfl) ⟨1214645, by rfl⟩ : syracuseStep 1619527 = 2429291) B2429291
theorem B1619679 : Blo 1619008 1619679 := bstep (se 1 (by rfl) ⟨1214759, by rfl⟩ : syracuseStep 1619679 = 2429519) B2429519
theorem B7788317 : Blo 1619008 7788317 := bstep (se 3 (by rfl) ⟨1460309, by rfl⟩ : syracuseStep 7788317 = 2920619) B2920619
theorem B8206109 : Blo 1619008 8206109 := bstep (se 3 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 8206109 = 3077291) B3077291
theorem B2430761 : Blo 1619008 2430761 := bstep (se 2 (by rfl) ⟨911535, by rfl⟩ : syracuseStep 2430761 = 1823071) B1823071
theorem B1619759 : Blo 1619008 1619759 := bstep (se 1 (by rfl) ⟨1214819, by rfl⟩ : syracuseStep 1619759 = 2429639) B2429639
theorem B2733871 : Blo 1619008 2733871 := bstep (se 1 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 2733871 = 4100807) B4100807
theorem B2430767 : Blo 1619008 2430767 := bstep (se 1 (by rfl) ⟨1823075, by rfl⟩ : syracuseStep 2430767 = 3646151) B3646151
theorem B7780151 : Blo 1619008 7780151 := bstep (se 1 (by rfl) ⟨5835113, by rfl⟩ : syracuseStep 7780151 = 11670227) B11670227
theorem B1619867 : Blo 1619008 1619867 := bstep (se 1 (by rfl) ⟨1214900, by rfl⟩ : syracuseStep 1619867 = 2429801) B2429801
theorem B3643343 : Blo 1619008 3643343 := bstep (se 1 (by rfl) ⟨2732507, by rfl⟩ : syracuseStep 3643343 = 5465015) B5465015
theorem B1619919 : Blo 1619008 1619919 := bstep (se 1 (by rfl) ⟨1214939, by rfl⟩ : syracuseStep 1619919 = 2429879) B2429879
theorem B1619943 : Blo 1619008 1619943 := bstep (se 1 (by rfl) ⟨1214957, by rfl⟩ : syracuseStep 1619943 = 2429915) B2429915
theorem B76904549 : Blo 1619008 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B2594921 : Blo 1619008 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B7886983 : Blo 1619008 7886983 := bstep (se 1 (by rfl) ⟨5915237, by rfl⟩ : syracuseStep 7886983 = 11830475) B11830475
theorem B6920387 : Blo 1619008 6920387 := bstep (se 1 (by rfl) ⟨5190290, by rfl⟩ : syracuseStep 6920387 = 10380581) B10380581
theorem B15186149 : Blo 1619008 15186149 := bstep (se 4 (by rfl) ⟨1423701, by rfl⟩ : syracuseStep 15186149 = 2847403) B2847403
theorem B2431241 : Blo 1619008 2431241 := bstep (se 2 (by rfl) ⟨911715, by rfl⟩ : syracuseStep 2431241 = 1823431) B1823431
theorem B1620255 : Blo 1619008 1620255 := bstep (se 1 (by rfl) ⟨1215191, by rfl⟩ : syracuseStep 1620255 = 2430383) B2430383
theorem B3643721 : Blo 1619008 3643721 := bstep (se 2 (by rfl) ⟨1366395, by rfl⟩ : syracuseStep 3643721 = 2732791) B2732791
theorem B123074891 : Blo 1619008 123074891 := bstep (se 1 (by rfl) ⟨92306168, by rfl⟩ : syracuseStep 123074891 = 184612337) B184612337
theorem B3643739 : Blo 1619008 3643739 := bstep (se 1 (by rfl) ⟨2732804, by rfl⟩ : syracuseStep 3643739 = 5465609) B5465609
theorem B1620315 : Blo 1619008 1620315 := bstep (se 1 (by rfl) ⟨1215236, by rfl⟩ : syracuseStep 1620315 = 2430473) B2430473
theorem B1620335 : Blo 1619008 1620335 := bstep (se 1 (by rfl) ⟨1215251, by rfl⟩ : syracuseStep 1620335 = 2430503) B2430503
theorem B2431343 : Blo 1619008 2431343 := bstep (se 1 (by rfl) ⟨1823507, by rfl⟩ : syracuseStep 2431343 = 3647015) B3647015
theorem B1620391 : Blo 1619008 1620391 := bstep (se 1 (by rfl) ⟨1215293, by rfl⟩ : syracuseStep 1620391 = 2430587) B2430587
theorem B5470631 : Blo 1619008 5470631 := bstep (se 1 (by rfl) ⟨4102973, by rfl⟩ : syracuseStep 5470631 = 8205947) B8205947
theorem B4381103 : Blo 1619008 4381103 := bstep (se 1 (by rfl) ⟨3285827, by rfl⟩ : syracuseStep 4381103 = 6571655) B6571655
theorem B4610515 : Blo 1619008 4610515 := bstep (se 1 (by rfl) ⟨3457886, by rfl⟩ : syracuseStep 4610515 = 6915773) B6915773
theorem B1620475 : Blo 1619008 1620475 := bstep (se 1 (by rfl) ⟨1215356, by rfl⟩ : syracuseStep 1620475 = 2430713) B2430713
theorem B16636441 : Blo 1619008 16636441 := bstep (se 2 (by rfl) ⟨6238665, by rfl⟩ : syracuseStep 16636441 = 12477331) B12477331
theorem B1620543 : Blo 1619008 1620543 := bstep (se 1 (by rfl) ⟨1215407, by rfl⟩ : syracuseStep 1620543 = 2430815) B2430815
theorem B1620551 : Blo 1619008 1620551 := bstep (se 1 (by rfl) ⟨1215413, by rfl⟩ : syracuseStep 1620551 = 2430827) B2430827
theorem B5470793 : Blo 1619008 5470793 := bstep (se 2 (by rfl) ⟨2051547, by rfl⟩ : syracuseStep 5470793 = 4103095) B4103095
theorem B1620703 : Blo 1619008 1620703 := bstep (se 1 (by rfl) ⟨1215527, by rfl⟩ : syracuseStep 1620703 = 2431055) B2431055
theorem B3947255 : Blo 1619008 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B1620783 : Blo 1619008 1620783 := bstep (se 1 (by rfl) ⟨1215587, by rfl⟩ : syracuseStep 1620783 = 2431175) B2431175
theorem B70105925 : Blo 1619008 70105925 := bstep (se 4 (by rfl) ⟨6572430, by rfl⟩ : syracuseStep 70105925 = 13144861) B13144861
theorem B35519309 : Blo 1619008 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B3644315 : Blo 1619008 3644315 := bstep (se 1 (by rfl) ⟨2733236, by rfl⟩ : syracuseStep 3644315 = 5466473) B5466473
theorem B1620891 : Blo 1619008 1620891 := bstep (se 1 (by rfl) ⟨1215668, by rfl⟩ : syracuseStep 1620891 = 2431337) B2431337
theorem B1620943 : Blo 1619008 1620943 := bstep (se 1 (by rfl) ⟨1215707, by rfl⟩ : syracuseStep 1620943 = 2431415) B2431415
theorem B1620967 : Blo 1619008 1620967 := bstep (se 1 (by rfl) ⟨1215725, by rfl⟩ : syracuseStep 1620967 = 2431451) B2431451
theorem B7388147 : Blo 1619008 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B3644513 : Blo 1619008 3644513 := bstep (se 2 (by rfl) ⟨1366692, by rfl⟩ : syracuseStep 3644513 = 2733385) B2733385
theorem B3890315 : Blo 1619008 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B224386199 : Blo 1619008 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B3742939 : Blo 1619008 3742939 := bstep (se 1 (by rfl) ⟨2807204, by rfl⟩ : syracuseStep 3742939 = 5614409) B5614409
theorem B3644711 : Blo 1619008 3644711 := bstep (se 1 (by rfl) ⟨2733533, by rfl⟩ : syracuseStep 3644711 = 5467067) B5467067
theorem B6921787 : Blo 1619008 6921787 := bstep (se 1 (by rfl) ⟨5191340, by rfl⟩ : syracuseStep 6921787 = 10382681) B10382681
theorem B3284563 : Blo 1619008 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B4611745 : Blo 1619008 4611745 := bstep (se 2 (by rfl) ⟨1729404, by rfl⟩ : syracuseStep 4611745 = 3458809) B3458809
theorem B3645089 : Blo 1619008 3645089 := bstep (se 2 (by rfl) ⟨1366908, by rfl⟩ : syracuseStep 3645089 = 2733817) B2733817
theorem B11681441 : Blo 1619008 11681441 := bstep (se 2 (by rfl) ⟨4380540, by rfl⟩ : syracuseStep 11681441 = 8761081) B8761081
theorem B4612315 : Blo 1619008 4612315 := bstep (se 1 (by rfl) ⟨3459236, by rfl⟩ : syracuseStep 4612315 = 6918473) B6918473
theorem B8200439 : Blo 1619008 8200439 := bstep (se 1 (by rfl) ⟨6150329, by rfl⟩ : syracuseStep 8200439 = 12300659) B12300659
theorem B28057907 : Blo 1619008 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B75858533 : Blo 1619008 75858533 := bstep (se 4 (by rfl) ⟨7111737, by rfl⟩ : syracuseStep 75858533 = 14223475) B14223475
theorem B3646187 : Blo 1619008 3646187 := bstep (se 1 (by rfl) ⟨2734640, by rfl⟩ : syracuseStep 3646187 = 5469281) B5469281
theorem B4613021 : Blo 1619008 4613021 := bstep (se 3 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 4613021 = 1729883) B1729883
theorem B5186767 : Blo 1619008 5186767 := bstep (se 1 (by rfl) ⟨3890075, by rfl⟩ : syracuseStep 5186767 = 7780151) B7780151
theorem B4613591 : Blo 1619008 4613591 := bstep (se 1 (by rfl) ⟨3460193, by rfl⟩ : syracuseStep 4613591 = 6920387) B6920387
theorem B3647087 : Blo 1619008 3647087 := bstep (se 1 (by rfl) ⟨2735315, by rfl⟩ : syracuseStep 3647087 = 5470631) B5470631
theorem B3647195 : Blo 1619008 3647195 := bstep (se 1 (by rfl) ⟨2735396, by rfl⟩ : syracuseStep 3647195 = 5470793) B5470793
theorem B6571817 : Blo 1619008 6571817 := bstep (se 2 (by rfl) ⟨2464431, by rfl⟩ : syracuseStep 6571817 = 4928863) B4928863
theorem B2631503 : Blo 1619008 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B3073889 : Blo 1619008 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B46737283 : Blo 1619008 46737283 := bstep (se 1 (by rfl) ⟨35052962, by rfl⟩ : syracuseStep 46737283 = 70105925) B70105925
theorem B4925431 : Blo 1619008 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B20768845 : Blo 1619008 20768845 := bstep (se 3 (by rfl) ⟨3894158, by rfl⟩ : syracuseStep 20768845 = 7788317) B7788317
theorem B93415517 : Blo 1619008 93415517 := bstep (se 3 (by rfl) ⟨17515409, by rfl⟩ : syracuseStep 93415517 = 35030819) B35030819
theorem B2918543 : Blo 1619008 2918543 := bstep (se 1 (by rfl) ⟨2188907, by rfl⟩ : syracuseStep 2918543 = 4377815) B4377815
theorem B11077843 : Blo 1619008 11077843 := bstep (se 1 (by rfl) ⟨8308382, by rfl⟩ : syracuseStep 11077843 = 16616765) B16616765
theorem B5540075 : Blo 1619008 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B31148347 : Blo 1619008 31148347 := bstep (se 1 (by rfl) ⟨23361260, by rfl⟩ : syracuseStep 31148347 = 46722521) B46722521
theorem B23685605 : Blo 1619008 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B2050591 : Blo 1619008 2050591 := bstep (se 1 (by rfl) ⟨1537943, by rfl⟩ : syracuseStep 2050591 = 3075887) B3075887
theorem B12299201 : Blo 1619008 12299201 := bstep (se 2 (by rfl) ⟨4612200, by rfl⟩ : syracuseStep 12299201 = 9224401) B9224401
theorem B22465511 : Blo 1619008 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B4615289 : Blo 1619008 4615289 := bstep (se 2 (by rfl) ⟨1730733, by rfl⟩ : syracuseStep 4615289 = 3461467) B3461467
theorem B23358617 : Blo 1619008 23358617 := bstep (se 2 (by rfl) ⟨8759481, by rfl⟩ : syracuseStep 23358617 = 17518963) B17518963
theorem B1821919 : Blo 1619008 1821919 := bstep (se 1 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 1821919 = 2732879) B2732879
theorem B6147353 : Blo 1619008 6147353 := bstep (se 2 (by rfl) ⟨2305257, by rfl⟩ : syracuseStep 6147353 = 4610515) B4610515
theorem B15576407 : Blo 1619008 15576407 := bstep (se 1 (by rfl) ⟨11682305, by rfl⟩ : syracuseStep 15576407 = 23364611) B23364611
theorem B4099511 : Blo 1619008 4099511 := bstep (se 1 (by rfl) ⟨3074633, by rfl⟩ : syracuseStep 4099511 = 6149267) B6149267
theorem B17518007 : Blo 1619008 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B2305531 : Blo 1619008 2305531 := bstep (se 1 (by rfl) ⟨1729148, by rfl⟩ : syracuseStep 2305531 = 3458297) B3458297
theorem B2428523 : Blo 1619008 2428523 := bstep (se 1 (by rfl) ⟨1821392, by rfl⟩ : syracuseStep 2428523 = 3642785) B3642785
theorem B10374763 : Blo 1619008 10374763 := bstep (se 1 (by rfl) ⟨7781072, by rfl⟩ : syracuseStep 10374763 = 15562145) B15562145
theorem B3460715 : Blo 1619008 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B5467823 : Blo 1619008 5467823 := bstep (se 1 (by rfl) ⟨4100867, by rfl⟩ : syracuseStep 5467823 = 8201735) B8201735
theorem B2428649 : Blo 1619008 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B5836625 : Blo 1619008 5836625 := bstep (se 2 (by rfl) ⟨2188734, by rfl⟩ : syracuseStep 5836625 = 4377469) B4377469
theorem B2428793 : Blo 1619008 2428793 := bstep (se 2 (by rfl) ⟨910797, by rfl⟩ : syracuseStep 2428793 = 1821595) B1821595
theorem B2428895 : Blo 1619008 2428895 := bstep (se 1 (by rfl) ⟨1821671, by rfl⟩ : syracuseStep 2428895 = 3643343) B3643343
theorem B5468147 : Blo 1619008 5468147 := bstep (se 1 (by rfl) ⟨4101110, by rfl⟩ : syracuseStep 5468147 = 8202221) B8202221
theorem B42643459 : Blo 1619008 42643459 := bstep (se 1 (by rfl) ⟨31982594, by rfl⟩ : syracuseStep 42643459 = 63965189) B63965189
theorem B51269699 : Blo 1619008 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B8425657 : Blo 1619008 8425657 := bstep (se 2 (by rfl) ⟨3159621, by rfl⟩ : syracuseStep 8425657 = 6319243) B6319243
theorem B2732251 : Blo 1619008 2732251 := bstep (se 1 (by rfl) ⟨2049188, by rfl⟩ : syracuseStep 2732251 = 4098377) B4098377
theorem B2429147 : Blo 1619008 2429147 := bstep (se 1 (by rfl) ⟨1821860, by rfl⟩ : syracuseStep 2429147 = 3643721) B3643721
theorem B2429159 : Blo 1619008 2429159 := bstep (se 1 (by rfl) ⟨1821869, by rfl⟩ : syracuseStep 2429159 = 3643739) B3643739
theorem B2920735 : Blo 1619008 2920735 := bstep (se 1 (by rfl) ⟨2190551, by rfl⟩ : syracuseStep 2920735 = 4381103) B4381103
theorem B5468471 : Blo 1619008 5468471 := bstep (se 1 (by rfl) ⟨4101353, by rfl⟩ : syracuseStep 5468471 = 8202707) B8202707
theorem B2306431 : Blo 1619008 2306431 := bstep (se 1 (by rfl) ⟨1729823, by rfl⟩ : syracuseStep 2306431 = 3459647) B3459647
theorem B2429321 : Blo 1619008 2429321 := bstep (se 2 (by rfl) ⟨910995, by rfl⟩ : syracuseStep 2429321 = 1821991) B1821991
theorem B11088353 : Blo 1619008 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B2732521 : Blo 1619008 2732521 := bstep (se 2 (by rfl) ⟨1024695, by rfl⟩ : syracuseStep 2732521 = 2049391) B2049391
theorem B2429417 : Blo 1619008 2429417 := bstep (se 2 (by rfl) ⟨911031, by rfl⟩ : syracuseStep 2429417 = 1822063) B1822063
theorem B5468687 : Blo 1619008 5468687 := bstep (se 1 (by rfl) ⟨4101515, by rfl⟩ : syracuseStep 5468687 = 8203031) B8203031
theorem B23679539 : Blo 1619008 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B2429543 : Blo 1619008 2429543 := bstep (se 1 (by rfl) ⟨1822157, by rfl⟩ : syracuseStep 2429543 = 3644315) B3644315
theorem B1946215 : Blo 1619008 1946215 := bstep (se 1 (by rfl) ⟨1459661, by rfl⟩ : syracuseStep 1946215 = 2919323) B2919323
theorem B2429675 : Blo 1619008 2429675 := bstep (se 1 (by rfl) ⟨1822256, by rfl⟩ : syracuseStep 2429675 = 3644513) B3644513
theorem B9229049 : Blo 1619008 9229049 := bstep (se 2 (by rfl) ⟨3460893, by rfl⟩ : syracuseStep 9229049 = 6921787) B6921787
theorem B2593543 : Blo 1619008 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B2429705 : Blo 1619008 2429705 := bstep (se 2 (by rfl) ⟨911139, by rfl⟩ : syracuseStep 2429705 = 1822279) B1822279
theorem B149590799 : Blo 1619008 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B4379417 : Blo 1619008 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2429807 : Blo 1619008 2429807 := bstep (se 1 (by rfl) ⟨1822355, by rfl⟩ : syracuseStep 2429807 = 3644711) B3644711
theorem B6148993 : Blo 1619008 6148993 := bstep (se 2 (by rfl) ⟨2305872, by rfl⟩ : syracuseStep 6148993 = 4611745) B4611745
theorem B5190571 : Blo 1619008 5190571 := bstep (se 1 (by rfl) ⟨3892928, by rfl⟩ : syracuseStep 5190571 = 7785857) B7785857
theorem B2430059 : Blo 1619008 2430059 := bstep (se 1 (by rfl) ⟨1822544, by rfl⟩ : syracuseStep 2430059 = 3645089) B3645089
theorem B7787627 : Blo 1619008 7787627 := bstep (se 1 (by rfl) ⟨5840720, by rfl⟩ : syracuseStep 7787627 = 11681441) B11681441
theorem B1619151 : Blo 1619008 1619151 := bstep (se 1 (by rfl) ⟨1214363, by rfl⟩ : syracuseStep 1619151 = 2428727) B2428727
theorem B2430299 : Blo 1619008 2430299 := bstep (se 1 (by rfl) ⟨1822724, by rfl⟩ : syracuseStep 2430299 = 3645449) B3645449
theorem B1619355 : Blo 1619008 1619355 := bstep (se 1 (by rfl) ⟨1214516, by rfl⟩ : syracuseStep 1619355 = 2429033) B2429033
theorem B10515977 : Blo 1619008 10515977 := bstep (se 2 (by rfl) ⟨3943491, by rfl⟩ : syracuseStep 10515977 = 7886983) B7886983
theorem B5469767 : Blo 1619008 5469767 := bstep (se 1 (by rfl) ⟨4102325, by rfl⟩ : syracuseStep 5469767 = 8204651) B8204651
theorem B6919789 : Blo 1619008 6919789 := bstep (se 3 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 6919789 = 2594921) B2594921
theorem B1619567 : Blo 1619008 1619567 := bstep (se 1 (by rfl) ⟨1214675, by rfl⟩ : syracuseStep 1619567 = 2429351) B2429351
theorem B2430575 : Blo 1619008 2430575 := bstep (se 1 (by rfl) ⟨1822931, by rfl⟩ : syracuseStep 2430575 = 3645863) B3645863
theorem B2307695 : Blo 1619008 2307695 := bstep (se 1 (by rfl) ⟨1730771, by rfl⟩ : syracuseStep 2307695 = 3461543) B3461543
theorem B2733689 : Blo 1619008 2733689 := bstep (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) B2050267
theorem B1619623 : Blo 1619008 1619623 := bstep (se 1 (by rfl) ⟨1214717, by rfl⟩ : syracuseStep 1619623 = 2429435) B2429435
theorem B2430647 : Blo 1619008 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B2430683 : Blo 1619008 2430683 := bstep (se 1 (by rfl) ⟨1823012, by rfl⟩ : syracuseStep 2430683 = 3646025) B3646025
theorem B1619707 : Blo 1619008 1619707 := bstep (se 1 (by rfl) ⟨1214780, by rfl⟩ : syracuseStep 1619707 = 2429561) B2429561
theorem B5838587 : Blo 1619008 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B1619743 : Blo 1619008 1619743 := bstep (se 1 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 1619743 = 2429615) B2429615
theorem B39950135 : Blo 1619008 39950135 := bstep (se 1 (by rfl) ⟨29962601, by rfl⟩ : syracuseStep 39950135 = 59925203) B59925203
theorem B3643199 : Blo 1619008 3643199 := bstep (se 1 (by rfl) ⟨2732399, by rfl⟩ : syracuseStep 3643199 = 5464799) B5464799
theorem B1619775 : Blo 1619008 1619775 := bstep (se 1 (by rfl) ⟨1214831, by rfl⟩ : syracuseStep 1619775 = 2429663) B2429663
theorem B2430857 : Blo 1619008 2430857 := bstep (se 2 (by rfl) ⟨911571, by rfl⟩ : syracuseStep 2430857 = 1823143) B1823143
theorem B4102103 : Blo 1619008 4102103 := bstep (se 1 (by rfl) ⟨3076577, by rfl⟩ : syracuseStep 4102103 = 6153155) B6153155
theorem B23345117 : Blo 1619008 23345117 := bstep (se 3 (by rfl) ⟨4377209, by rfl⟩ : syracuseStep 23345117 = 8754419) B8754419
theorem B33265637 : Blo 1619008 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B13842413 : Blo 1619008 13842413 := bstep (se 3 (by rfl) ⟨2595452, by rfl⟩ : syracuseStep 13842413 = 5190905) B5190905
theorem B1619951 : Blo 1619008 1619951 := bstep (se 1 (by rfl) ⟨1214963, by rfl⟩ : syracuseStep 1619951 = 2429927) B2429927
theorem B2430959 : Blo 1619008 2430959 := bstep (se 1 (by rfl) ⟨1823219, by rfl⟩ : syracuseStep 2430959 = 3646439) B3646439
theorem B22181921 : Blo 1619008 22181921 := bstep (se 2 (by rfl) ⟨8318220, by rfl⟩ : syracuseStep 22181921 = 16636441) B16636441
theorem B3643487 : Blo 1619008 3643487 := bstep (se 1 (by rfl) ⟨2732615, by rfl⟩ : syracuseStep 3643487 = 5465231) B5465231
theorem B6150239 : Blo 1619008 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B2734175 : Blo 1619008 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B3692687 : Blo 1619008 3692687 := bstep (se 1 (by rfl) ⟨2769515, by rfl⟩ : syracuseStep 3692687 = 5539031) B5539031
theorem B1620123 : Blo 1619008 1620123 := bstep (se 1 (by rfl) ⟨1215092, by rfl⟩ : syracuseStep 1620123 = 2430185) B2430185
theorem B1620159 : Blo 1619008 1620159 := bstep (se 1 (by rfl) ⟨1215119, by rfl⟩ : syracuseStep 1620159 = 2430239) B2430239
theorem B2431211 : Blo 1619008 2431211 := bstep (se 1 (by rfl) ⟨1823408, by rfl⟩ : syracuseStep 2431211 = 3646817) B3646817
theorem B2431271 : Blo 1619008 2431271 := bstep (se 1 (by rfl) ⟨1823453, by rfl⟩ : syracuseStep 2431271 = 3646907) B3646907
theorem B9222443 : Blo 1619008 9222443 := bstep (se 1 (by rfl) ⟨6916832, by rfl⟩ : syracuseStep 9222443 = 13833665) B13833665
theorem B1620271 : Blo 1619008 1620271 := bstep (se 1 (by rfl) ⟨1215203, by rfl⟩ : syracuseStep 1620271 = 2430407) B2430407
theorem B5192059 : Blo 1619008 5192059 := bstep (se 1 (by rfl) ⟨3894044, by rfl⟩ : syracuseStep 5192059 = 7788089) B7788089
theorem B2431355 : Blo 1619008 2431355 := bstep (se 1 (by rfl) ⟨1823516, by rfl⟩ : syracuseStep 2431355 = 3647033) B3647033
theorem B9230759 : Blo 1619008 9230759 := bstep (se 1 (by rfl) ⟨6923069, by rfl⟩ : syracuseStep 9230759 = 13846139) B13846139
theorem B19962341 : Blo 1619008 19962341 := bstep (se 4 (by rfl) ⟨1871469, by rfl⟩ : syracuseStep 19962341 = 3742939) B3742939
theorem B17512949 : Blo 1619008 17512949 := bstep (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) B1641839
theorem B5470739 : Blo 1619008 5470739 := bstep (se 1 (by rfl) ⟨4103054, by rfl⟩ : syracuseStep 5470739 = 8206109) B8206109
theorem B1620507 : Blo 1619008 1620507 := bstep (se 1 (by rfl) ⟨1215380, by rfl⟩ : syracuseStep 1620507 = 2430761) B2430761
theorem B1620511 : Blo 1619008 1620511 := bstep (se 1 (by rfl) ⟨1215383, by rfl⟩ : syracuseStep 1620511 = 2430767) B2430767
theorem B10124099 : Blo 1619008 10124099 := bstep (se 1 (by rfl) ⟨7593074, by rfl⟩ : syracuseStep 10124099 = 15186149) B15186149
theorem B29547341 : Blo 1619008 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B3644243 : Blo 1619008 3644243 := bstep (se 1 (by rfl) ⟨2733182, by rfl⟩ : syracuseStep 3644243 = 5466365) B5466365
theorem B1620827 : Blo 1619008 1620827 := bstep (se 1 (by rfl) ⟨1215620, by rfl⟩ : syracuseStep 1620827 = 2431241) B2431241
theorem B82049927 : Blo 1619008 82049927 := bstep (se 1 (by rfl) ⟨61537445, by rfl⟩ : syracuseStep 82049927 = 123074891) B123074891
theorem B1620895 : Blo 1619008 1620895 := bstep (se 1 (by rfl) ⟨1215671, by rfl⟩ : syracuseStep 1620895 = 2431343) B2431343
theorem B3644783 : Blo 1619008 3644783 := bstep (se 1 (by rfl) ⟨2733587, by rfl⟩ : syracuseStep 3644783 = 5467175) B5467175
theorem B3645071 : Blo 1619008 3645071 := bstep (se 1 (by rfl) ⟨2733803, by rfl⟩ : syracuseStep 3645071 = 5467607) B5467607
theorem B3645161 : Blo 1619008 3645161 := bstep (se 2 (by rfl) ⟨1366935, by rfl⟩ : syracuseStep 3645161 = 2733871) B2733871
theorem B3645647 : Blo 1619008 3645647 := bstep (se 1 (by rfl) ⟨2734235, by rfl⟩ : syracuseStep 3645647 = 5468471) B5468471
theorem B14770457 : Blo 1619008 14770457 := bstep (se 2 (by rfl) ⟨5538921, by rfl⟩ : syracuseStep 14770457 = 11077843) B11077843
theorem B3645791 : Blo 1619008 3645791 := bstep (se 1 (by rfl) ⟨2734343, by rfl⟩ : syracuseStep 3645791 = 5468687) B5468687
theorem B15786359 : Blo 1619008 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B9847165 : Blo 1619008 9847165 := bstep (se 3 (by rfl) ⟨1846343, by rfl⟩ : syracuseStep 9847165 = 3692687) B3692687
theorem B6922745 : Blo 1619008 6922745 := bstep (se 2 (by rfl) ⟨2596029, by rfl⟩ : syracuseStep 6922745 = 5192059) B5192059
theorem B6152699 : Blo 1619008 6152699 := bstep (se 1 (by rfl) ⟨4614524, by rfl⟩ : syracuseStep 6152699 = 9229049) B9229049
theorem B3458057 : Blo 1619008 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B3646511 : Blo 1619008 3646511 := bstep (se 1 (by rfl) ⟨2734883, by rfl⟩ : syracuseStep 3646511 = 5469767) B5469767
theorem B3892391 : Blo 1619008 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B26633423 : Blo 1619008 26633423 := bstep (se 1 (by rfl) ⟨19975067, by rfl⟩ : syracuseStep 26633423 = 39950135) B39950135
theorem B1754335 : Blo 1619008 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B22177091 : Blo 1619008 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B14787947 : Blo 1619008 14787947 := bstep (se 1 (by rfl) ⟨11090960, by rfl⟩ : syracuseStep 14787947 = 22181921) B22181921
theorem B62277011 : Blo 1619008 62277011 := bstep (se 1 (by rfl) ⟨46707758, by rfl⟩ : syracuseStep 62277011 = 93415517) B93415517
theorem B31131125 : Blo 1619008 31131125 := bstep (se 5 (by rfl) ⟨1459271, by rfl⟩ : syracuseStep 31131125 = 2918543) B2918543
theorem B6915689 : Blo 1619008 6915689 := bstep (se 2 (by rfl) ⟨2593383, by rfl⟩ : syracuseStep 6915689 = 5186767) B5186767
theorem B6153839 : Blo 1619008 6153839 := bstep (se 1 (by rfl) ⟨4615379, by rfl⟩ : syracuseStep 6153839 = 9230759) B9230759
theorem B6153853 : Blo 1619008 6153853 := bstep (se 3 (by rfl) ⟨1153847, by rfl⟩ : syracuseStep 6153853 = 2307695) B2307695
theorem B3647159 : Blo 1619008 3647159 := bstep (se 1 (by rfl) ⟨2735369, by rfl⟩ : syracuseStep 3647159 = 5470739) B5470739
theorem B14977007 : Blo 1619008 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B3074041 : Blo 1619008 3074041 := bstep (se 2 (by rfl) ⟨1152765, by rfl⟩ : syracuseStep 3074041 = 2305531) B2305531
theorem B9226385 : Blo 1619008 9226385 := bstep (se 2 (by rfl) ⟨3459894, by rfl⟩ : syracuseStep 9226385 = 6919789) B6919789
theorem B4098235 : Blo 1619008 4098235 := bstep (se 1 (by rfl) ⟨3073676, by rfl⟩ : syracuseStep 4098235 = 6147353) B6147353
theorem B27683045 : Blo 1619008 27683045 := bstep (se 4 (by rfl) ⟨2595285, by rfl⟩ : syracuseStep 27683045 = 5190571) B5190571
theorem B27691793 : Blo 1619008 27691793 := bstep (se 2 (by rfl) ⟨10384422, by rfl⟩ : syracuseStep 27691793 = 20768845) B20768845
theorem B5466959 : Blo 1619008 5466959 := bstep (se 1 (by rfl) ⟨4100219, by rfl⟩ : syracuseStep 5466959 = 8200439) B8200439
theorem B136719197 : Blo 1619008 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B18705271 : Blo 1619008 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B11234209 : Blo 1619008 11234209 := bstep (se 2 (by rfl) ⟨4212828, by rfl⟩ : syracuseStep 11234209 = 8425657) B8425657
theorem B7392235 : Blo 1619008 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B3894313 : Blo 1619008 3894313 := bstep (se 2 (by rfl) ⟨1460367, by rfl⟩ : syracuseStep 3894313 = 2920735) B2920735
theorem B50572355 : Blo 1619008 50572355 := bstep (se 1 (by rfl) ⟨37929266, by rfl⟩ : syracuseStep 50572355 = 75858533) B75858533
theorem B3075241 : Blo 1619008 3075241 := bstep (se 2 (by rfl) ⟨1153215, by rfl⟩ : syracuseStep 3075241 = 2306431) B2306431
theorem B2919611 : Blo 1619008 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B3075347 : Blo 1619008 3075347 := bstep (se 1 (by rfl) ⟨2306510, by rfl⟩ : syracuseStep 3075347 = 4613021) B4613021
theorem B3075727 : Blo 1619008 3075727 := bstep (se 1 (by rfl) ⟨2306795, by rfl⟩ : syracuseStep 3075727 = 4613591) B4613591
theorem B1822459 : Blo 1619008 1822459 := bstep (se 1 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 1822459 = 2733689) B2733689
theorem B2428799 : Blo 1619008 2428799 := bstep (se 1 (by rfl) ⟨1821599, by rfl⟩ : syracuseStep 2428799 = 3643199) B3643199
theorem B9228275 : Blo 1619008 9228275 := bstep (se 1 (by rfl) ⟨6921206, by rfl⟩ : syracuseStep 9228275 = 13842413) B13842413
theorem B2428991 : Blo 1619008 2428991 := bstep (se 1 (by rfl) ⟨1821743, by rfl⟩ : syracuseStep 2428991 = 3643487) B3643487
theorem B4100159 : Blo 1619008 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B1822783 : Blo 1619008 1822783 := bstep (se 1 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 1822783 = 2734175) B2734175
theorem B6148295 : Blo 1619008 6148295 := bstep (se 1 (by rfl) ⟨4611221, by rfl⟩ : syracuseStep 6148295 = 9222443) B9222443
theorem B2429225 : Blo 1619008 2429225 := bstep (se 2 (by rfl) ⟨910959, by rfl⟩ : syracuseStep 2429225 = 1821919) B1821919
theorem B13308227 : Blo 1619008 13308227 := bstep (se 1 (by rfl) ⟨9981170, by rfl⟩ : syracuseStep 13308227 = 19962341) B19962341
theorem B15790403 : Blo 1619008 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B19698227 : Blo 1619008 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2429495 : Blo 1619008 2429495 := bstep (se 1 (by rfl) ⟨1822121, by rfl⟩ : syracuseStep 2429495 = 3644243) B3644243
theorem B3076859 : Blo 1619008 3076859 := bstep (se 1 (by rfl) ⟨2307644, by rfl⟩ : syracuseStep 3076859 = 4615289) B4615289
theorem B13833017 : Blo 1619008 13833017 := bstep (se 2 (by rfl) ⟨5187381, by rfl⟩ : syracuseStep 13833017 = 10374763) B10374763
theorem B10384271 : Blo 1619008 10384271 := bstep (se 1 (by rfl) ⟨7788203, by rfl⟩ : syracuseStep 10384271 = 15576407) B15576407
theorem B2429855 : Blo 1619008 2429855 := bstep (se 1 (by rfl) ⟨1822391, by rfl⟩ : syracuseStep 2429855 = 3644783) B3644783
theorem B8197037 : Blo 1619008 8197037 := bstep (se 3 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 8197037 = 3073889) B3073889
theorem B2733007 : Blo 1619008 2733007 := bstep (se 1 (by rfl) ⟨2049755, by rfl⟩ : syracuseStep 2733007 = 4099511) B4099511
theorem B11678671 : Blo 1619008 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B1619015 : Blo 1619008 1619015 := bstep (se 1 (by rfl) ⟨1214261, by rfl⟩ : syracuseStep 1619015 = 2428523) B2428523
theorem B2307143 : Blo 1619008 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B2430047 : Blo 1619008 2430047 := bstep (se 1 (by rfl) ⟨1822535, by rfl⟩ : syracuseStep 2430047 = 3645071) B3645071
theorem B1619099 : Blo 1619008 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B2430107 : Blo 1619008 2430107 := bstep (se 1 (by rfl) ⟨1822580, by rfl⟩ : syracuseStep 2430107 = 3645161) B3645161
theorem B1619195 : Blo 1619008 1619195 := bstep (se 1 (by rfl) ⟨1214396, by rfl⟩ : syracuseStep 1619195 = 2428793) B2428793
theorem B1619263 : Blo 1619008 1619263 := bstep (se 1 (by rfl) ⟨1214447, by rfl⟩ : syracuseStep 1619263 = 2428895) B2428895
theorem B6567241 : Blo 1619008 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B56857945 : Blo 1619008 56857945 := bstep (se 2 (by rfl) ⟨21321729, by rfl⟩ : syracuseStep 56857945 = 42643459) B42643459
theorem B1619431 : Blo 1619008 1619431 := bstep (se 1 (by rfl) ⟨1214573, by rfl⟩ : syracuseStep 1619431 = 2429147) B2429147
theorem B1619439 : Blo 1619008 1619439 := bstep (se 1 (by rfl) ⟨1214579, by rfl⟩ : syracuseStep 1619439 = 2429159) B2429159
theorem B1619547 : Blo 1619008 1619547 := bstep (se 1 (by rfl) ⟨1214660, by rfl⟩ : syracuseStep 1619547 = 2429321) B2429321
theorem B3643001 : Blo 1619008 3643001 := bstep (se 2 (by rfl) ⟨1366125, by rfl⟩ : syracuseStep 3643001 = 2732251) B2732251
theorem B6149753 : Blo 1619008 6149753 := bstep (se 2 (by rfl) ⟨2306157, by rfl⟩ : syracuseStep 6149753 = 4612315) B4612315
theorem B1619611 : Blo 1619008 1619611 := bstep (se 1 (by rfl) ⟨1214708, by rfl⟩ : syracuseStep 1619611 = 2429417) B2429417
theorem B1619695 : Blo 1619008 1619695 := bstep (se 1 (by rfl) ⟨1214771, by rfl⟩ : syracuseStep 1619695 = 2429543) B2429543
theorem B41531129 : Blo 1619008 41531129 := bstep (se 2 (by rfl) ⟨15574173, by rfl⟩ : syracuseStep 41531129 = 31148347) B31148347
theorem B1619783 : Blo 1619008 1619783 := bstep (se 1 (by rfl) ⟨1214837, by rfl⟩ : syracuseStep 1619783 = 2429675) B2429675
theorem B2430791 : Blo 1619008 2430791 := bstep (se 1 (by rfl) ⟨1823093, by rfl⟩ : syracuseStep 2430791 = 3646187) B3646187
theorem B1619803 : Blo 1619008 1619803 := bstep (se 1 (by rfl) ⟨1214852, by rfl⟩ : syracuseStep 1619803 = 2429705) B2429705
theorem B99727199 : Blo 1619008 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B1619871 : Blo 1619008 1619871 := bstep (se 1 (by rfl) ⟨1214903, by rfl⟩ : syracuseStep 1619871 = 2429807) B2429807
theorem B3643361 : Blo 1619008 3643361 := bstep (se 2 (by rfl) ⟨1366260, by rfl⟩ : syracuseStep 3643361 = 2732521) B2732521
theorem B2734121 : Blo 1619008 2734121 := bstep (se 2 (by rfl) ⟨1025295, by rfl⟩ : syracuseStep 2734121 = 2050591) B2050591
theorem B1620039 : Blo 1619008 1620039 := bstep (se 1 (by rfl) ⟨1215029, by rfl⟩ : syracuseStep 1620039 = 2430059) B2430059
theorem B5191751 : Blo 1619008 5191751 := bstep (se 1 (by rfl) ⟨3893813, by rfl⟩ : syracuseStep 5191751 = 7787627) B7787627
theorem B2594953 : Blo 1619008 2594953 := bstep (se 2 (by rfl) ⟨973107, by rfl⟩ : syracuseStep 2594953 = 1946215) B1946215
theorem B1620199 : Blo 1619008 1620199 := bstep (se 1 (by rfl) ⟨1215149, by rfl⟩ : syracuseStep 1620199 = 2430299) B2430299
theorem B7010651 : Blo 1619008 7010651 := bstep (se 1 (by rfl) ⟨5257988, by rfl⟩ : syracuseStep 7010651 = 10515977) B10515977
theorem B1620383 : Blo 1619008 1620383 := bstep (se 1 (by rfl) ⟨1215287, by rfl⟩ : syracuseStep 1620383 = 2430575) B2430575
theorem B2431391 : Blo 1619008 2431391 := bstep (se 1 (by rfl) ⟨1823543, by rfl⟩ : syracuseStep 2431391 = 3647087) B3647087
theorem B1620431 : Blo 1619008 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B1620455 : Blo 1619008 1620455 := bstep (se 1 (by rfl) ⟨1215341, by rfl⟩ : syracuseStep 1620455 = 2430683) B2430683
theorem B2431463 : Blo 1619008 2431463 := bstep (se 1 (by rfl) ⟨1823597, by rfl⟩ : syracuseStep 2431463 = 3647195) B3647195
theorem B8198657 : Blo 1619008 8198657 := bstep (se 2 (by rfl) ⟨3074496, by rfl⟩ : syracuseStep 8198657 = 6148993) B6148993
theorem B4381211 : Blo 1619008 4381211 := bstep (se 1 (by rfl) ⟨3285908, by rfl⟩ : syracuseStep 4381211 = 6571817) B6571817
theorem B1620571 : Blo 1619008 1620571 := bstep (se 1 (by rfl) ⟨1215428, by rfl⟩ : syracuseStep 1620571 = 2430857) B2430857
theorem B46701197 : Blo 1619008 46701197 := bstep (se 3 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 46701197 = 17512949) B17512949
theorem B2734735 : Blo 1619008 2734735 := bstep (se 1 (by rfl) ⟨2051051, by rfl⟩ : syracuseStep 2734735 = 4102103) B4102103
theorem B15563411 : Blo 1619008 15563411 := bstep (se 1 (by rfl) ⟨11672558, by rfl⟩ : syracuseStep 15563411 = 23345117) B23345117
theorem B1620639 : Blo 1619008 1620639 := bstep (se 1 (by rfl) ⟨1215479, by rfl⟩ : syracuseStep 1620639 = 2430959) B2430959
theorem B3693383 : Blo 1619008 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B1620807 : Blo 1619008 1620807 := bstep (se 1 (by rfl) ⟨1215605, by rfl⟩ : syracuseStep 1620807 = 2431211) B2431211
theorem B1620847 : Blo 1619008 1620847 := bstep (se 1 (by rfl) ⟨1215635, by rfl⟩ : syracuseStep 1620847 = 2431271) B2431271
theorem B1620903 : Blo 1619008 1620903 := bstep (se 1 (by rfl) ⟨1215677, by rfl⟩ : syracuseStep 1620903 = 2431355) B2431355
theorem B6749399 : Blo 1619008 6749399 := bstep (se 1 (by rfl) ⟨5062049, by rfl⟩ : syracuseStep 6749399 = 10124099) B10124099
theorem B8199467 : Blo 1619008 8199467 := bstep (se 1 (by rfl) ⟨6149600, by rfl⟩ : syracuseStep 8199467 = 12299201) B12299201
theorem B15572411 : Blo 1619008 15572411 := bstep (se 1 (by rfl) ⟨11679308, by rfl⟩ : syracuseStep 15572411 = 23358617) B23358617
theorem B218799805 : Blo 1619008 218799805 := bstep (se 3 (by rfl) ⟨41024963, by rfl⟩ : syracuseStep 218799805 = 82049927) B82049927
theorem B3645215 : Blo 1619008 3645215 := bstep (se 1 (by rfl) ⟨2733911, by rfl⟩ : syracuseStep 3645215 = 5467823) B5467823
theorem B62316377 : Blo 1619008 62316377 := bstep (se 2 (by rfl) ⟨23368641, by rfl⟩ : syracuseStep 62316377 = 46737283) B46737283
theorem B3891083 : Blo 1619008 3891083 := bstep (se 1 (by rfl) ⟨2918312, by rfl⟩ : syracuseStep 3891083 = 5836625) B5836625
theorem B3645431 : Blo 1619008 3645431 := bstep (se 1 (by rfl) ⟨2734073, by rfl⟩ : syracuseStep 3645431 = 5468147) B5468147
theorem B9846971 : Blo 1619008 9846971 := bstep (se 1 (by rfl) ⟨7385228, by rfl⟩ : syracuseStep 9846971 = 14770457) B14770457
theorem B6152381 : Blo 1619008 6152381 := bstep (se 3 (by rfl) ⟨1153571, by rfl⟩ : syracuseStep 6152381 = 2307143) B2307143
theorem B8872151 : Blo 1619008 8872151 := bstep (se 1 (by rfl) ⟨6654113, by rfl⟩ : syracuseStep 8872151 = 13308227) B13308227
theorem B10526935 : Blo 1619008 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B5464313 : Blo 1619008 5464313 := bstep (se 2 (by rfl) ⟨2049117, by rfl⟩ : syracuseStep 5464313 = 4098235) B4098235
theorem B13132151 : Blo 1619008 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B6922847 : Blo 1619008 6922847 := bstep (se 1 (by rfl) ⟨5192135, by rfl⟩ : syracuseStep 6922847 = 10384271) B10384271
theorem B5464691 : Blo 1619008 5464691 := bstep (se 1 (by rfl) ⟨4098518, by rfl⟩ : syracuseStep 5464691 = 8197037) B8197037
theorem B8200925 : Blo 1619008 8200925 := bstep (se 3 (by rfl) ⟨1537673, by rfl⟩ : syracuseStep 8200925 = 3075347) B3075347
theorem B59138909 : Blo 1619008 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B3646313 : Blo 1619008 3646313 := bstep (se 2 (by rfl) ⟨1367367, by rfl⟩ : syracuseStep 3646313 = 2734735) B2734735
theorem B18695069 : Blo 1619008 18695069 := bstep (se 3 (by rfl) ⟨3505325, by rfl⟩ : syracuseStep 18695069 = 7010651) B7010651
theorem B41518007 : Blo 1619008 41518007 := bstep (se 1 (by rfl) ⟨31138505, by rfl⟩ : syracuseStep 41518007 = 62277011) B62277011
theorem B9856313 : Blo 1619008 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B5465771 : Blo 1619008 5465771 := bstep (se 1 (by rfl) ⟨4099328, by rfl⟩ : syracuseStep 5465771 = 8198657) B8198657
theorem B75810593 : Blo 1619008 75810593 := bstep (se 2 (by rfl) ⟨28428972, by rfl⟩ : syracuseStep 75810593 = 56857945) B56857945
theorem B91146131 : Blo 1619008 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B4499599 : Blo 1619008 4499599 := bstep (se 1 (by rfl) ⟨3374699, by rfl⟩ : syracuseStep 4499599 = 6749399) B6749399
theorem B5466311 : Blo 1619008 5466311 := bstep (se 1 (by rfl) ⟨4099733, by rfl⟩ : syracuseStep 5466311 = 8199467) B8199467
theorem B10381607 : Blo 1619008 10381607 := bstep (se 1 (by rfl) ⟨7786205, by rfl⟩ : syracuseStep 10381607 = 15572411) B15572411
theorem B41544251 : Blo 1619008 41544251 := bstep (se 1 (by rfl) ⟨31158188, by rfl⟩ : syracuseStep 41544251 = 62316377) B62316377
theorem B4098721 : Blo 1619008 4098721 := bstep (se 2 (by rfl) ⟨1537020, by rfl⟩ : syracuseStep 4098721 = 3074041) B3074041
theorem B4098863 : Blo 1619008 4098863 := bstep (se 1 (by rfl) ⟨3074147, by rfl⟩ : syracuseStep 4098863 = 6148295) B6148295
theorem B134859613 : Blo 1619008 134859613 := bstep (se 3 (by rfl) ⟨25286177, by rfl⟩ : syracuseStep 134859613 = 50572355) B50572355
theorem B3459937 : Blo 1619008 3459937 := bstep (se 2 (by rfl) ⟨1297476, by rfl⟩ : syracuseStep 3459937 = 2594953) B2594953
theorem B4615163 : Blo 1619008 4615163 := bstep (se 1 (by rfl) ⟨3461372, by rfl⟩ : syracuseStep 4615163 = 6922745) B6922745
theorem B7785629 : Blo 1619008 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B2051239 : Blo 1619008 2051239 := bstep (se 1 (by rfl) ⟨1538429, by rfl⟩ : syracuseStep 2051239 = 3076859) B3076859
theorem B17755615 : Blo 1619008 17755615 := bstep (se 1 (by rfl) ⟨13316711, by rfl⟩ : syracuseStep 17755615 = 26633423) B26633423
theorem B9858631 : Blo 1619008 9858631 := bstep (se 1 (by rfl) ⟨7393973, by rfl⟩ : syracuseStep 9858631 = 14787947) B14787947
theorem B20754083 : Blo 1619008 20754083 := bstep (se 1 (by rfl) ⟨15565562, by rfl⟩ : syracuseStep 20754083 = 31131125) B31131125
theorem B6152183 : Blo 1619008 6152183 := bstep (se 1 (by rfl) ⟨4614137, by rfl⟩ : syracuseStep 6152183 = 9228275) B9228275
theorem B2428667 : Blo 1619008 2428667 := bstep (se 1 (by rfl) ⟨1821500, by rfl⟩ : syracuseStep 2428667 = 3643001) B3643001
theorem B4099835 : Blo 1619008 4099835 := bstep (se 1 (by rfl) ⟨3074876, by rfl⟩ : syracuseStep 4099835 = 6149753) B6149753
theorem B24940361 : Blo 1619008 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B14978945 : Blo 1619008 14978945 := bstep (se 2 (by rfl) ⟨5617104, by rfl⟩ : syracuseStep 14978945 = 11234209) B11234209
theorem B2428907 : Blo 1619008 2428907 := bstep (se 1 (by rfl) ⟨1821680, by rfl⟩ : syracuseStep 2428907 = 3643361) B3643361
theorem B1822747 : Blo 1619008 1822747 := bstep (se 1 (by rfl) ⟨1367060, by rfl⟩ : syracuseStep 1822747 = 2734121) B2734121
theorem B3461167 : Blo 1619008 3461167 := bstep (se 1 (by rfl) ⟨2595875, by rfl⟩ : syracuseStep 3461167 = 5191751) B5191751
theorem B41504885 : Blo 1619008 41504885 := bstep (se 5 (by rfl) ⟨1945541, by rfl⟩ : syracuseStep 41504885 = 3891083) B3891083
theorem B4100321 : Blo 1619008 4100321 := bstep (se 2 (by rfl) ⟨1537620, by rfl⟩ : syracuseStep 4100321 = 3075241) B3075241
theorem B2339113 : Blo 1619008 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B2920807 : Blo 1619008 2920807 := bstep (se 1 (by rfl) ⟨2190605, by rfl⟩ : syracuseStep 2920807 = 4381211) B4381211
theorem B31134131 : Blo 1619008 31134131 := bstep (se 1 (by rfl) ⟨23350598, by rfl⟩ : syracuseStep 31134131 = 46701197) B46701197
theorem B10375607 : Blo 1619008 10375607 := bstep (se 1 (by rfl) ⟨7781705, by rfl⟩ : syracuseStep 10375607 = 15563411) B15563411
theorem B18461195 : Blo 1619008 18461195 := bstep (se 1 (by rfl) ⟨13845896, by rfl⟩ : syracuseStep 18461195 = 27691793) B27691793
theorem B2462255 : Blo 1619008 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B8205137 : Blo 1619008 8205137 := bstep (se 2 (by rfl) ⟨3076926, by rfl⟩ : syracuseStep 8205137 = 6153853) B6153853
theorem B4100969 : Blo 1619008 4100969 := bstep (se 2 (by rfl) ⟨1537863, by rfl⟩ : syracuseStep 4100969 = 3075727) B3075727
theorem B2429945 : Blo 1619008 2429945 := bstep (se 2 (by rfl) ⟨911229, by rfl⟩ : syracuseStep 2429945 = 1822459) B1822459
theorem B2430143 : Blo 1619008 2430143 := bstep (se 1 (by rfl) ⟨1822607, by rfl⟩ : syracuseStep 2430143 = 3645215) B3645215
theorem B1619199 : Blo 1619008 1619199 := bstep (se 1 (by rfl) ⟨1214399, by rfl⟩ : syracuseStep 1619199 = 2428799) B2428799
theorem B2430287 : Blo 1619008 2430287 := bstep (se 1 (by rfl) ⟨1822715, by rfl⟩ : syracuseStep 2430287 = 3645431) B3645431
theorem B9221485 : Blo 1619008 9221485 := bstep (se 3 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 9221485 = 3458057) B3458057
theorem B1619327 : Blo 1619008 1619327 := bstep (se 1 (by rfl) ⟨1214495, by rfl⟩ : syracuseStep 1619327 = 2428991) B2428991
theorem B2733439 : Blo 1619008 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B2430377 : Blo 1619008 2430377 := bstep (se 2 (by rfl) ⟨911391, by rfl⟩ : syracuseStep 2430377 = 1822783) B1822783
theorem B2430431 : Blo 1619008 2430431 := bstep (se 1 (by rfl) ⟨1822823, by rfl⟩ : syracuseStep 2430431 = 3645647) B3645647
theorem B1619483 : Blo 1619008 1619483 := bstep (se 1 (by rfl) ⟨1214612, by rfl⟩ : syracuseStep 1619483 = 2429225) B2429225
theorem B2430527 : Blo 1619008 2430527 := bstep (se 1 (by rfl) ⟨1822895, by rfl⟩ : syracuseStep 2430527 = 3645791) B3645791
theorem B10524239 : Blo 1619008 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B4101799 : Blo 1619008 4101799 := bstep (se 1 (by rfl) ⟨3076349, by rfl⟩ : syracuseStep 4101799 = 6152699) B6152699
theorem B1619663 : Blo 1619008 1619663 := bstep (se 1 (by rfl) ⟨1214747, by rfl⟩ : syracuseStep 1619663 = 2429495) B2429495
theorem B13129553 : Blo 1619008 13129553 := bstep (se 2 (by rfl) ⟨4923582, by rfl⟩ : syracuseStep 13129553 = 9847165) B9847165
theorem B9222011 : Blo 1619008 9222011 := bstep (se 1 (by rfl) ⟨6916508, by rfl⟩ : syracuseStep 9222011 = 13833017) B13833017
theorem B1619903 : Blo 1619008 1619903 := bstep (se 1 (by rfl) ⟨1214927, by rfl⟩ : syracuseStep 1619903 = 2429855) B2429855
theorem B2431007 : Blo 1619008 2431007 := bstep (se 1 (by rfl) ⟨1823255, by rfl⟩ : syracuseStep 2431007 = 3646511) B3646511
theorem B1620031 : Blo 1619008 1620031 := bstep (se 1 (by rfl) ⟨1215023, by rfl⟩ : syracuseStep 1620031 = 2430047) B2430047
theorem B1620071 : Blo 1619008 1620071 := bstep (se 1 (by rfl) ⟨1215053, by rfl⟩ : syracuseStep 1620071 = 2430107) B2430107
theorem B2594927 : Blo 1619008 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B4610459 : Blo 1619008 4610459 := bstep (se 1 (by rfl) ⟨3457844, by rfl⟩ : syracuseStep 4610459 = 6915689) B6915689
theorem B4102559 : Blo 1619008 4102559 := bstep (se 1 (by rfl) ⟨3076919, by rfl⟩ : syracuseStep 4102559 = 6153839) B6153839
theorem B2431439 : Blo 1619008 2431439 := bstep (se 1 (by rfl) ⟨1823579, by rfl⟩ : syracuseStep 2431439 = 3647159) B3647159
theorem B27687419 : Blo 1619008 27687419 := bstep (se 1 (by rfl) ⟨20765564, by rfl⟩ : syracuseStep 27687419 = 41531129) B41531129
theorem B1620527 : Blo 1619008 1620527 := bstep (se 1 (by rfl) ⟨1215395, by rfl⟩ : syracuseStep 1620527 = 2430791) B2430791
theorem B66484799 : Blo 1619008 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B3644009 : Blo 1619008 3644009 := bstep (se 2 (by rfl) ⟨1366503, by rfl⟩ : syracuseStep 3644009 = 2733007) B2733007
theorem B15571561 : Blo 1619008 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B9984671 : Blo 1619008 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B5192417 : Blo 1619008 5192417 := bstep (se 2 (by rfl) ⟨1947156, by rfl⟩ : syracuseStep 5192417 = 3894313) B3894313
theorem B6150923 : Blo 1619008 6150923 := bstep (se 1 (by rfl) ⟨4613192, by rfl⟩ : syracuseStep 6150923 = 9226385) B9226385
theorem B18455363 : Blo 1619008 18455363 := bstep (se 1 (by rfl) ⟨13841522, by rfl⟩ : syracuseStep 18455363 = 27683045) B27683045
theorem B1620927 : Blo 1619008 1620927 := bstep (se 1 (by rfl) ⟨1215695, by rfl⟩ : syracuseStep 1620927 = 2431391) B2431391
theorem B1620975 : Blo 1619008 1620975 := bstep (se 1 (by rfl) ⟨1215731, by rfl⟩ : syracuseStep 1620975 = 2431463) B2431463
theorem B8756321 : Blo 1619008 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B3644639 : Blo 1619008 3644639 := bstep (se 1 (by rfl) ⟨2733479, by rfl⟩ : syracuseStep 3644639 = 5466959) B5466959
theorem B291733073 : Blo 1619008 291733073 := bstep (se 2 (by rfl) ⟨109399902, by rfl⟩ : syracuseStep 291733073 = 218799805) B218799805
theorem B23659069 : Blo 1619008 23659069 := bstep (se 3 (by rfl) ⟨4436075, by rfl⟩ : syracuseStep 23659069 = 8872151) B8872151
theorem B6570875 : Blo 1619008 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B5464961 : Blo 1619008 5464961 := bstep (se 2 (by rfl) ⟨2049360, by rfl⟩ : syracuseStep 5464961 = 4098721) B4098721
theorem B4613249 : Blo 1619008 4613249 := bstep (se 2 (by rfl) ⟨1729968, by rfl⟩ : syracuseStep 4613249 = 3459937) B3459937
theorem B3073639 : Blo 1619008 3073639 := bstep (se 1 (by rfl) ⟨2305229, by rfl⟩ : syracuseStep 3073639 = 4610459) B4610459
theorem B18458279 : Blo 1619008 18458279 := bstep (se 1 (by rfl) ⟨13843709, by rfl⟩ : syracuseStep 18458279 = 27687419) B27687419
theorem B194488715 : Blo 1619008 194488715 := bstep (se 1 (by rfl) ⟨145866536, by rfl⟩ : syracuseStep 194488715 = 291733073) B291733073
theorem B4614889 : Blo 1619008 4614889 := bstep (se 2 (by rfl) ⟨1730583, by rfl⟩ : syracuseStep 4614889 = 3461167) B3461167
theorem B6564647 : Blo 1619008 6564647 := bstep (se 1 (by rfl) ⟨4923485, by rfl⟩ : syracuseStep 6564647 = 9846971) B9846971
theorem B5999465 : Blo 1619008 5999465 := bstep (se 2 (by rfl) ⟨2249799, by rfl⟩ : syracuseStep 5999465 = 4499599) B4499599
theorem B23350189 : Blo 1619008 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B14035913 : Blo 1619008 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B6917071 : Blo 1619008 6917071 := bstep (se 1 (by rfl) ⟨5187803, by rfl⟩ : syracuseStep 6917071 = 10375607) B10375607
theorem B12307463 : Blo 1619008 12307463 := bstep (se 1 (by rfl) ⟨9230597, by rfl⟩ : syracuseStep 12307463 = 18461195) B18461195
theorem B1641503 : Blo 1619008 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B4615231 : Blo 1619008 4615231 := bstep (se 1 (by rfl) ⟨3461423, by rfl⟩ : syracuseStep 4615231 = 6922847) B6922847
theorem B3894409 : Blo 1619008 3894409 := bstep (se 2 (by rfl) ⟨1460403, by rfl⟩ : syracuseStep 3894409 = 2920807) B2920807
theorem B5467283 : Blo 1619008 5467283 := bstep (se 1 (by rfl) ⟨4100462, by rfl⟩ : syracuseStep 5467283 = 8200925) B8200925
theorem B12463379 : Blo 1619008 12463379 := bstep (se 1 (by rfl) ⟨9347534, by rfl⟩ : syracuseStep 12463379 = 18695069) B18695069
theorem B20762081 : Blo 1619008 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B7016159 : Blo 1619008 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B50540395 : Blo 1619008 50540395 := bstep (se 1 (by rfl) ⟨37905296, by rfl⟩ : syracuseStep 50540395 = 75810593) B75810593
theorem B8753035 : Blo 1619008 8753035 := bstep (se 1 (by rfl) ⟨6564776, by rfl⟩ : syracuseStep 8753035 = 13129553) B13129553
theorem B6148007 : Blo 1619008 6148007 := bstep (se 1 (by rfl) ⟨4611005, by rfl⟩ : syracuseStep 6148007 = 9222011) B9222011
theorem B60764087 : Blo 1619008 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B44323199 : Blo 1619008 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B2429339 : Blo 1619008 2429339 := bstep (se 1 (by rfl) ⟨1822004, by rfl⟩ : syracuseStep 2429339 = 3644009) B3644009
theorem B6656447 : Blo 1619008 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B3461611 : Blo 1619008 3461611 := bstep (se 1 (by rfl) ⟨2596208, by rfl⟩ : syracuseStep 3461611 = 5192417) B5192417
theorem B4100615 : Blo 1619008 4100615 := bstep (se 1 (by rfl) ⟨3075461, by rfl⟩ : syracuseStep 4100615 = 6150923) B6150923
theorem B2732575 : Blo 1619008 2732575 := bstep (se 1 (by rfl) ⟨2049431, by rfl⟩ : syracuseStep 2732575 = 4098863) B4098863
theorem B3076775 : Blo 1619008 3076775 := bstep (se 1 (by rfl) ⟨2307581, by rfl⟩ : syracuseStep 3076775 = 4615163) B4615163
theorem B13144841 : Blo 1619008 13144841 := bstep (se 2 (by rfl) ⟨4929315, by rfl⟩ : syracuseStep 13144841 = 9858631) B9858631
theorem B5190419 : Blo 1619008 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B2429759 : Blo 1619008 2429759 := bstep (se 1 (by rfl) ⟨1822319, by rfl⟩ : syracuseStep 2429759 = 3644639) B3644639
theorem B5469065 : Blo 1619008 5469065 := bstep (se 2 (by rfl) ⟨2050899, by rfl⟩ : syracuseStep 5469065 = 4101799) B4101799
theorem B1619111 : Blo 1619008 1619111 := bstep (se 1 (by rfl) ⟨1214333, by rfl⟩ : syracuseStep 1619111 = 2428667) B2428667
theorem B2733223 : Blo 1619008 2733223 := bstep (se 1 (by rfl) ⟨2049917, by rfl⟩ : syracuseStep 2733223 = 4099835) B4099835
theorem B16626907 : Blo 1619008 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B1619271 : Blo 1619008 1619271 := bstep (se 1 (by rfl) ⟨1214453, by rfl⟩ : syracuseStep 1619271 = 2428907) B2428907
theorem B4101455 : Blo 1619008 4101455 := bstep (se 1 (by rfl) ⟨3076091, by rfl⟩ : syracuseStep 4101455 = 6152183) B6152183
theorem B2430329 : Blo 1619008 2430329 := bstep (se 2 (by rfl) ⟨911373, by rfl⟩ : syracuseStep 2430329 = 1822747) B1822747
theorem B27669923 : Blo 1619008 27669923 := bstep (se 1 (by rfl) ⟨20752442, by rfl⟩ : syracuseStep 27669923 = 41504885) B41504885
theorem B4101587 : Blo 1619008 4101587 := bstep (se 1 (by rfl) ⟨3076190, by rfl⟩ : syracuseStep 4101587 = 6152381) B6152381
theorem B2733547 : Blo 1619008 2733547 := bstep (se 1 (by rfl) ⟨2050160, by rfl⟩ : syracuseStep 2733547 = 4100321) B4100321
theorem B3642875 : Blo 1619008 3642875 := bstep (se 1 (by rfl) ⟨2732156, by rfl⟩ : syracuseStep 3642875 = 5464313) B5464313
theorem B8754767 : Blo 1619008 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B20756087 : Blo 1619008 20756087 := bstep (se 1 (by rfl) ⟨15567065, by rfl⟩ : syracuseStep 20756087 = 31134131) B31134131
theorem B6919805 : Blo 1619008 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B3118817 : Blo 1619008 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B3643127 : Blo 1619008 3643127 := bstep (se 1 (by rfl) ⟨2732345, by rfl⟩ : syracuseStep 3643127 = 5464691) B5464691
theorem B5470091 : Blo 1619008 5470091 := bstep (se 1 (by rfl) ⟨4102568, by rfl⟩ : syracuseStep 5470091 = 8205137) B8205137
theorem B39425939 : Blo 1619008 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B2733979 : Blo 1619008 2733979 := bstep (se 1 (by rfl) ⟨2050484, by rfl⟩ : syracuseStep 2733979 = 4100969) B4100969
theorem B2430875 : Blo 1619008 2430875 := bstep (se 1 (by rfl) ⟨1823156, by rfl⟩ : syracuseStep 2430875 = 3646313) B3646313
theorem B27678671 : Blo 1619008 27678671 := bstep (se 1 (by rfl) ⟨20759003, by rfl⟩ : syracuseStep 27678671 = 41518007) B41518007
theorem B1619963 : Blo 1619008 1619963 := bstep (se 1 (by rfl) ⟨1214972, by rfl⟩ : syracuseStep 1619963 = 2429945) B2429945
theorem B1620095 : Blo 1619008 1620095 := bstep (se 1 (by rfl) ⟨1215071, by rfl⟩ : syracuseStep 1620095 = 2430143) B2430143
theorem B1620191 : Blo 1619008 1620191 := bstep (se 1 (by rfl) ⟨1215143, by rfl⟩ : syracuseStep 1620191 = 2430287) B2430287
theorem B1620251 : Blo 1619008 1620251 := bstep (se 1 (by rfl) ⟨1215188, by rfl⟩ : syracuseStep 1620251 = 2430377) B2430377
theorem B1620287 : Blo 1619008 1620287 := bstep (se 1 (by rfl) ⟨1215215, by rfl⟩ : syracuseStep 1620287 = 2430431) B2430431
theorem B1620351 : Blo 1619008 1620351 := bstep (se 1 (by rfl) ⟨1215263, by rfl⟩ : syracuseStep 1620351 = 2430527) B2430527
theorem B3643847 : Blo 1619008 3643847 := bstep (se 1 (by rfl) ⟨2732885, by rfl⟩ : syracuseStep 3643847 = 5465771) B5465771
theorem B179812817 : Blo 1619008 179812817 := bstep (se 2 (by rfl) ⟨67429806, by rfl⟩ : syracuseStep 179812817 = 134859613) B134859613
theorem B1620671 : Blo 1619008 1620671 := bstep (se 1 (by rfl) ⟨1215503, by rfl⟩ : syracuseStep 1620671 = 2431007) B2431007
theorem B3644207 : Blo 1619008 3644207 := bstep (se 1 (by rfl) ⟨2733155, by rfl⟩ : syracuseStep 3644207 = 5466311) B5466311
theorem B6921071 : Blo 1619008 6921071 := bstep (se 1 (by rfl) ⟨5190803, by rfl⟩ : syracuseStep 6921071 = 10381607) B10381607
theorem B2734985 : Blo 1619008 2734985 := bstep (se 2 (by rfl) ⟨1025619, by rfl⟩ : syracuseStep 2734985 = 2051239) B2051239
theorem B2735039 : Blo 1619008 2735039 := bstep (se 1 (by rfl) ⟨2051279, by rfl⟩ : syracuseStep 2735039 = 4102559) B4102559
theorem B1620959 : Blo 1619008 1620959 := bstep (se 1 (by rfl) ⟨1215719, by rfl⟩ : syracuseStep 1620959 = 2431439) B2431439
theorem B27696167 : Blo 1619008 27696167 := bstep (se 1 (by rfl) ⟨20772125, by rfl⟩ : syracuseStep 27696167 = 41544251) B41544251
theorem B12295313 : Blo 1619008 12295313 := bstep (se 2 (by rfl) ⟨4610742, by rfl⟩ : syracuseStep 12295313 = 9221485) B9221485
theorem B3644585 : Blo 1619008 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B12303575 : Blo 1619008 12303575 := bstep (se 1 (by rfl) ⟨9227681, by rfl⟩ : syracuseStep 12303575 = 18455363) B18455363
theorem B23674153 : Blo 1619008 23674153 := bstep (se 2 (by rfl) ⟨8877807, by rfl⟩ : syracuseStep 23674153 = 17755615) B17755615
theorem B13836055 : Blo 1619008 13836055 := bstep (se 1 (by rfl) ⟨10377041, by rfl⟩ : syracuseStep 13836055 = 20754083) B20754083
theorem B9985963 : Blo 1619008 9985963 := bstep (se 1 (by rfl) ⟨7489472, by rfl⟩ : syracuseStep 9985963 = 14978945) B14978945
theorem B29548799 : Blo 1619008 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B3646043 : Blo 1619008 3646043 := bstep (se 1 (by rfl) ⟨2734532, by rfl⟩ : syracuseStep 3646043 = 5469065) B5469065
theorem B6153185 : Blo 1619008 6153185 := bstep (se 2 (by rfl) ⟨2307444, by rfl⟩ : syracuseStep 6153185 = 4614889) B4614889
theorem B13837391 : Blo 1619008 13837391 := bstep (se 1 (by rfl) ⟨10378043, by rfl⟩ : syracuseStep 13837391 = 20756087) B20756087
theorem B4613203 : Blo 1619008 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B12305519 : Blo 1619008 12305519 := bstep (se 1 (by rfl) ⟨9229139, by rfl⟩ : syracuseStep 12305519 = 18458279) B18458279
theorem B3646727 : Blo 1619008 3646727 := bstep (se 1 (by rfl) ⟨2735045, by rfl⟩ : syracuseStep 3646727 = 5470091) B5470091
theorem B6153641 : Blo 1619008 6153641 := bstep (se 2 (by rfl) ⟨2307615, by rfl⟩ : syracuseStep 6153641 = 4615231) B4615231
theorem B22169209 : Blo 1619008 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B119875211 : Blo 1619008 119875211 := bstep (se 1 (by rfl) ⟨89906408, by rfl⟩ : syracuseStep 119875211 = 179812817) B179812817
theorem B31565537 : Blo 1619008 31565537 := bstep (se 2 (by rfl) ⟨11837076, by rfl⟩ : syracuseStep 31565537 = 23674153) B23674153
theorem B4376431 : Blo 1619008 4376431 := bstep (se 1 (by rfl) ⟨3282323, by rfl⟩ : syracuseStep 4376431 = 6564647) B6564647
theorem B4614047 : Blo 1619008 4614047 := bstep (se 1 (by rfl) ⟨3460535, by rfl⟩ : syracuseStep 4614047 = 6921071) B6921071
theorem B9357275 : Blo 1619008 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B4098185 : Blo 1619008 4098185 := bstep (se 2 (by rfl) ⟨1536819, by rfl⟩ : syracuseStep 4098185 = 3073639) B3073639
theorem B8202383 : Blo 1619008 8202383 := bstep (se 1 (by rfl) ⟨6151787, by rfl⟩ : syracuseStep 8202383 = 12303575) B12303575
theorem B8308919 : Blo 1619008 8308919 := bstep (se 1 (by rfl) ⟨6231689, by rfl⟩ : syracuseStep 8308919 = 12463379) B12463379
theorem B13314617 : Blo 1619008 13314617 := bstep (se 2 (by rfl) ⟨4992981, by rfl⟩ : syracuseStep 13314617 = 9985963) B9985963
theorem B4098671 : Blo 1619008 4098671 := bstep (se 1 (by rfl) ⟨3074003, by rfl⟩ : syracuseStep 4098671 = 6148007) B6148007
theorem B4377341 : Blo 1619008 4377341 := bstep (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) B1641503
theorem B2051183 : Blo 1619008 2051183 := bstep (se 1 (by rfl) ⟨1538387, by rfl⟩ : syracuseStep 2051183 = 3076775) B3076775
theorem B3460279 : Blo 1619008 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B4615481 : Blo 1619008 4615481 := bstep (se 2 (by rfl) ⟨1730805, by rfl⟩ : syracuseStep 4615481 = 3461611) B3461611
theorem B20770181 : Blo 1619008 20770181 := bstep (se 4 (by rfl) ⟨1947204, by rfl⟩ : syracuseStep 20770181 = 3894409) B3894409
theorem B3075499 : Blo 1619008 3075499 := bstep (se 1 (by rfl) ⟨2306624, by rfl⟩ : syracuseStep 3075499 = 4613249) B4613249
theorem B2428583 : Blo 1619008 2428583 := bstep (se 1 (by rfl) ⟨1821437, by rfl⟩ : syracuseStep 2428583 = 3642875) B3642875
theorem B5836511 : Blo 1619008 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B2428751 : Blo 1619008 2428751 := bstep (se 1 (by rfl) ⟨1821563, by rfl⟩ : syracuseStep 2428751 = 3643127) B3643127
theorem B31133585 : Blo 1619008 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B26283959 : Blo 1619008 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B18452447 : Blo 1619008 18452447 := bstep (se 1 (by rfl) ⟨13839335, by rfl⟩ : syracuseStep 18452447 = 27678671) B27678671
theorem B129659143 : Blo 1619008 129659143 := bstep (se 1 (by rfl) ⟨97244357, by rfl⟩ : syracuseStep 129659143 = 194488715) B194488715
theorem B2429231 : Blo 1619008 2429231 := bstep (se 1 (by rfl) ⟨1821923, by rfl⟩ : syracuseStep 2429231 = 3643847) B3643847
theorem B2429471 : Blo 1619008 2429471 := bstep (se 1 (by rfl) ⟨1822103, by rfl⟩ : syracuseStep 2429471 = 3644207) B3644207
theorem B1823323 : Blo 1619008 1823323 := bstep (se 1 (by rfl) ⟨1367492, by rfl⟩ : syracuseStep 1823323 = 2734985) B2734985
theorem B1823359 : Blo 1619008 1823359 := bstep (se 1 (by rfl) ⟨1367519, by rfl⟩ : syracuseStep 1823359 = 2735039) B2735039
theorem B8204975 : Blo 1619008 8204975 := bstep (se 1 (by rfl) ⟨6153731, by rfl⟩ : syracuseStep 8204975 = 12307463) B12307463
theorem B8196875 : Blo 1619008 8196875 := bstep (se 1 (by rfl) ⟨6147656, by rfl⟩ : syracuseStep 8196875 = 12295313) B12295313
theorem B2429723 : Blo 1619008 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B13841387 : Blo 1619008 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B11670713 : Blo 1619008 11670713 := bstep (se 2 (by rfl) ⟨4376517, by rfl⟩ : syracuseStep 11670713 = 8753035) B8753035
theorem B1619559 : Blo 1619008 1619559 := bstep (se 1 (by rfl) ⟨1214669, by rfl⟩ : syracuseStep 1619559 = 2429339) B2429339
theorem B4437631 : Blo 1619008 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B2733743 : Blo 1619008 2733743 := bstep (se 1 (by rfl) ⟨2050307, by rfl⟩ : syracuseStep 2733743 = 4100615) B4100615
theorem B8763227 : Blo 1619008 8763227 := bstep (se 1 (by rfl) ⟨6572420, by rfl⟩ : syracuseStep 8763227 = 13144841) B13144841
theorem B1619839 : Blo 1619008 1619839 := bstep (se 1 (by rfl) ⟨1214879, by rfl⟩ : syracuseStep 1619839 = 2429759) B2429759
theorem B4380583 : Blo 1619008 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B3643307 : Blo 1619008 3643307 := bstep (se 1 (by rfl) ⟨2732480, by rfl⟩ : syracuseStep 3643307 = 5464961) B5464961
theorem B3643433 : Blo 1619008 3643433 := bstep (se 2 (by rfl) ⟨1366287, by rfl⟩ : syracuseStep 3643433 = 2732575) B2732575
theorem B31545425 : Blo 1619008 31545425 := bstep (se 2 (by rfl) ⟨11829534, by rfl⟩ : syracuseStep 31545425 = 23659069) B23659069
theorem B2734303 : Blo 1619008 2734303 := bstep (se 1 (by rfl) ⟨2050727, by rfl⟩ : syracuseStep 2734303 = 4101455) B4101455
theorem B1620219 : Blo 1619008 1620219 := bstep (se 1 (by rfl) ⟨1215164, by rfl⟩ : syracuseStep 1620219 = 2430329) B2430329
theorem B18446615 : Blo 1619008 18446615 := bstep (se 1 (by rfl) ⟨13834961, by rfl⟩ : syracuseStep 18446615 = 27669923) B27669923
theorem B2734391 : Blo 1619008 2734391 := bstep (se 1 (by rfl) ⟨2050793, by rfl⟩ : syracuseStep 2734391 = 4101587) B4101587
theorem B2079211 : Blo 1619008 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B1620583 : Blo 1619008 1620583 := bstep (se 1 (by rfl) ⟨1215437, by rfl⟩ : syracuseStep 1620583 = 2430875) B2430875
theorem B9222761 : Blo 1619008 9222761 := bstep (se 2 (by rfl) ⟨3458535, by rfl⟩ : syracuseStep 9222761 = 6917071) B6917071
theorem B3644297 : Blo 1619008 3644297 := bstep (se 2 (by rfl) ⟨1366611, by rfl⟩ : syracuseStep 3644297 = 2733223) B2733223
theorem B3644729 : Blo 1619008 3644729 := bstep (se 2 (by rfl) ⟨1366773, by rfl⟩ : syracuseStep 3644729 = 2733547) B2733547
theorem B18464111 : Blo 1619008 18464111 := bstep (se 1 (by rfl) ⟨13848083, by rfl⟩ : syracuseStep 18464111 = 27696167) B27696167
theorem B3644855 : Blo 1619008 3644855 := bstep (se 1 (by rfl) ⟨2733641, by rfl⟩ : syracuseStep 3644855 = 5467283) B5467283
theorem B15998573 : Blo 1619008 15998573 := bstep (se 3 (by rfl) ⟨2999732, by rfl⟩ : syracuseStep 15998573 = 5999465) B5999465
theorem B18448073 : Blo 1619008 18448073 := bstep (se 2 (by rfl) ⟨6918027, by rfl⟩ : syracuseStep 18448073 = 13836055) B13836055
theorem B67387193 : Blo 1619008 67387193 := bstep (se 2 (by rfl) ⟨25270197, by rfl⟩ : syracuseStep 67387193 = 50540395) B50540395
theorem B4677439 : Blo 1619008 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B3645305 : Blo 1619008 3645305 := bstep (se 2 (by rfl) ⟨1366989, by rfl⟩ : syracuseStep 3645305 = 2733979) B2733979
theorem B40509391 : Blo 1619008 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B3645737 : Blo 1619008 3645737 := bstep (se 2 (by rfl) ⟨1367151, by rfl⟩ : syracuseStep 3645737 = 2734303) B2734303
theorem B5464583 : Blo 1619008 5464583 := bstep (se 1 (by rfl) ⟨4098437, by rfl⟩ : syracuseStep 5464583 = 8196875) B8196875
theorem B23667365 : Blo 1619008 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B9224927 : Blo 1619008 9224927 := bstep (se 1 (by rfl) ⟨6918695, by rfl⟩ : syracuseStep 9224927 = 13837391) B13837391
theorem B5842151 : Blo 1619008 5842151 := bstep (se 1 (by rfl) ⟨4381613, by rfl⟩ : syracuseStep 5842151 = 8763227) B8763227
theorem B21030283 : Blo 1619008 21030283 := bstep (se 1 (by rfl) ⟨15772712, by rfl⟩ : syracuseStep 21030283 = 31545425) B31545425
theorem B5539279 : Blo 1619008 5539279 := bstep (se 1 (by rfl) ⟨4154459, by rfl⟩ : syracuseStep 5539279 = 8308919) B8308919
theorem B12297743 : Blo 1619008 12297743 := bstep (se 1 (by rfl) ⟨9223307, by rfl⟩ : syracuseStep 12297743 = 18446615) B18446615
theorem B4613705 : Blo 1619008 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B29558945 : Blo 1619008 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B13846787 : Blo 1619008 13846787 := bstep (se 1 (by rfl) ⟨10385090, by rfl⟩ : syracuseStep 13846787 = 20770181) B20770181
theorem B6236585 : Blo 1619008 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B12298715 : Blo 1619008 12298715 := bstep (se 1 (by rfl) ⟨9224036, by rfl⟩ : syracuseStep 12298715 = 18448073) B18448073
theorem B5835241 : Blo 1619008 5835241 := bstep (se 2 (by rfl) ⟨2188215, by rfl⟩ : syracuseStep 5835241 = 4376431) B4376431
theorem B54012521 : Blo 1619008 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B172878857 : Blo 1619008 172878857 := bstep (se 2 (by rfl) ⟨64829571, by rfl⟩ : syracuseStep 172878857 = 129659143) B129659143
theorem B2772281 : Blo 1619008 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B9227591 : Blo 1619008 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B8203679 : Blo 1619008 8203679 := bstep (se 1 (by rfl) ⟨6152759, by rfl⟩ : syracuseStep 8203679 = 12305519) B12305519
theorem B12307949 : Blo 1619008 12307949 := bstep (se 3 (by rfl) ⟨2307740, by rfl⟩ : syracuseStep 12307949 = 4615481) B4615481
theorem B79916807 : Blo 1619008 79916807 := bstep (se 1 (by rfl) ⟨59937605, by rfl⟩ : syracuseStep 79916807 = 119875211) B119875211
theorem B1822495 : Blo 1619008 1822495 := bstep (se 1 (by rfl) ⟨1366871, by rfl⟩ : syracuseStep 1822495 = 2733743) B2733743
theorem B3076031 : Blo 1619008 3076031 := bstep (se 1 (by rfl) ⟨2307023, by rfl⟩ : syracuseStep 3076031 = 4614047) B4614047
theorem B2428871 : Blo 1619008 2428871 := bstep (se 1 (by rfl) ⟨1821653, by rfl⟩ : syracuseStep 2428871 = 3643307) B3643307
theorem B6238183 : Blo 1619008 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B2428955 : Blo 1619008 2428955 := bstep (se 1 (by rfl) ⟨1821716, by rfl⟩ : syracuseStep 2428955 = 3643433) B3643433
theorem B2732123 : Blo 1619008 2732123 := bstep (se 1 (by rfl) ⟨2049092, by rfl⟩ : syracuseStep 2732123 = 4098185) B4098185
theorem B5468255 : Blo 1619008 5468255 := bstep (se 1 (by rfl) ⟨4101191, by rfl⟩ : syracuseStep 5468255 = 8202383) B8202383
theorem B1822927 : Blo 1619008 1822927 := bstep (se 1 (by rfl) ⟨1367195, by rfl⟩ : syracuseStep 1822927 = 2734391) B2734391
theorem B8876411 : Blo 1619008 8876411 := bstep (se 1 (by rfl) ⟨6657308, by rfl⟩ : syracuseStep 8876411 = 13314617) B13314617
theorem B6148507 : Blo 1619008 6148507 := bstep (se 1 (by rfl) ⟨4611380, by rfl⟩ : syracuseStep 6148507 = 9222761) B9222761
theorem B2732447 : Blo 1619008 2732447 := bstep (se 1 (by rfl) ⟨2049335, by rfl⟩ : syracuseStep 2732447 = 4098671) B4098671
theorem B4100665 : Blo 1619008 4100665 := bstep (se 2 (by rfl) ⟨1537749, by rfl⟩ : syracuseStep 4100665 = 3075499) B3075499
theorem B2429531 : Blo 1619008 2429531 := bstep (se 1 (by rfl) ⟨1822148, by rfl⟩ : syracuseStep 2429531 = 3644297) B3644297
theorem B2429819 : Blo 1619008 2429819 := bstep (se 1 (by rfl) ⟨1822364, by rfl⟩ : syracuseStep 2429819 = 3644729) B3644729
theorem B12309407 : Blo 1619008 12309407 := bstep (se 1 (by rfl) ⟨9232055, by rfl⟩ : syracuseStep 12309407 = 18464111) B18464111
theorem B2429903 : Blo 1619008 2429903 := bstep (se 1 (by rfl) ⟨1822427, by rfl⟩ : syracuseStep 2429903 = 3644855) B3644855
theorem B1619055 : Blo 1619008 1619055 := bstep (se 1 (by rfl) ⟨1214291, by rfl⟩ : syracuseStep 1619055 = 2428583) B2428583
theorem B1619167 : Blo 1619008 1619167 := bstep (se 1 (by rfl) ⟨1214375, by rfl⟩ : syracuseStep 1619167 = 2428751) B2428751
theorem B2430203 : Blo 1619008 2430203 := bstep (se 1 (by rfl) ⟨1822652, by rfl⟩ : syracuseStep 2430203 = 3645305) B3645305
theorem B20755723 : Blo 1619008 20755723 := bstep (se 1 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 20755723 = 31133585) B31133585
theorem B12301631 : Blo 1619008 12301631 := bstep (se 1 (by rfl) ⟨9226223, by rfl⟩ : syracuseStep 12301631 = 18452447) B18452447
theorem B19699199 : Blo 1619008 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B1619487 : Blo 1619008 1619487 := bstep (se 1 (by rfl) ⟨1214615, by rfl⟩ : syracuseStep 1619487 = 2429231) B2429231
theorem B5469821 : Blo 1619008 5469821 := bstep (se 3 (by rfl) ⟨1025591, by rfl⟩ : syracuseStep 5469821 = 2051183) B2051183
theorem B1619647 : Blo 1619008 1619647 := bstep (se 1 (by rfl) ⟨1214735, by rfl⟩ : syracuseStep 1619647 = 2429471) B2429471
theorem B2430695 : Blo 1619008 2430695 := bstep (se 1 (by rfl) ⟨1823021, by rfl⟩ : syracuseStep 2430695 = 3646043) B3646043
theorem B5469983 : Blo 1619008 5469983 := bstep (se 1 (by rfl) ⟨4102487, by rfl⟩ : syracuseStep 5469983 = 8204975) B8204975
theorem B1619815 : Blo 1619008 1619815 := bstep (se 1 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 1619815 = 2429723) B2429723
theorem B4102123 : Blo 1619008 4102123 := bstep (se 1 (by rfl) ⟨3076592, by rfl⟩ : syracuseStep 4102123 = 6153185) B6153185
theorem B2431097 : Blo 1619008 2431097 := bstep (se 2 (by rfl) ⟨911661, by rfl⟩ : syracuseStep 2431097 = 1823323) B1823323
theorem B7780475 : Blo 1619008 7780475 := bstep (se 1 (by rfl) ⟨5835356, by rfl⟩ : syracuseStep 7780475 = 11670713) B11670713
theorem B2431145 : Blo 1619008 2431145 := bstep (se 2 (by rfl) ⟨911679, by rfl⟩ : syracuseStep 2431145 = 1823359) B1823359
theorem B2431151 : Blo 1619008 2431151 := bstep (se 1 (by rfl) ⟨1823363, by rfl⟩ : syracuseStep 2431151 = 3646727) B3646727
theorem B4102427 : Blo 1619008 4102427 := bstep (se 1 (by rfl) ⟨3076820, by rfl⟩ : syracuseStep 4102427 = 6153641) B6153641
theorem B21043691 : Blo 1619008 21043691 := bstep (se 1 (by rfl) ⟨15782768, by rfl⟩ : syracuseStep 21043691 = 31565537) B31565537
theorem B6150937 : Blo 1619008 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B11672909 : Blo 1619008 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B10665715 : Blo 1619008 10665715 := bstep (se 1 (by rfl) ⟨7999286, by rfl⟩ : syracuseStep 10665715 = 15998573) B15998573
theorem B3891007 : Blo 1619008 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B44924795 : Blo 1619008 44924795 := bstep (se 1 (by rfl) ⟨33693596, by rfl⟩ : syracuseStep 44924795 = 67387193) B67387193
theorem B5840777 : Blo 1619008 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B17522639 : Blo 1619008 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B3645503 : Blo 1619008 3645503 := bstep (se 1 (by rfl) ⟨2734127, by rfl⟩ : syracuseStep 3645503 = 5468255) B5468255
theorem B78823853 : Blo 1619008 78823853 := bstep (se 3 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 78823853 = 29558945) B29558945
theorem B15778243 : Blo 1619008 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B8201087 : Blo 1619008 8201087 := bstep (se 1 (by rfl) ⟨6150815, by rfl⟩ : syracuseStep 8201087 = 12301631) B12301631
theorem B13132799 : Blo 1619008 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B8201249 : Blo 1619008 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B3646547 : Blo 1619008 3646547 := bstep (se 1 (by rfl) ⟨2734910, by rfl⟩ : syracuseStep 3646547 = 5469821) B5469821
theorem B3646655 : Blo 1619008 3646655 := bstep (se 1 (by rfl) ⟨2734991, by rfl⟩ : syracuseStep 3646655 = 5469983) B5469983
theorem B27674297 : Blo 1619008 27674297 := bstep (se 2 (by rfl) ⟨10377861, by rfl⟩ : syracuseStep 27674297 = 20755723) B20755723
theorem B5188009 : Blo 1619008 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B3893851 : Blo 1619008 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B2050687 : Blo 1619008 2050687 := bstep (se 1 (by rfl) ⟨1538015, by rfl⟩ : syracuseStep 2050687 = 3076031) B3076031
theorem B8317577 : Blo 1619008 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B1821415 : Blo 1619008 1821415 := bstep (se 1 (by rfl) ⟨1366061, by rfl⟩ : syracuseStep 1821415 = 2732123) B2732123
theorem B5917607 : Blo 1619008 5917607 := bstep (se 1 (by rfl) ⟨4438205, by rfl⟩ : syracuseStep 5917607 = 8876411) B8876411
theorem B1821631 : Blo 1619008 1821631 := bstep (se 1 (by rfl) ⟨1366223, by rfl⟩ : syracuseStep 1821631 = 2732447) B2732447
theorem B5467553 : Blo 1619008 5467553 := bstep (se 2 (by rfl) ⟨2050332, by rfl⟩ : syracuseStep 5467553 = 4100665) B4100665
theorem B3894767 : Blo 1619008 3894767 := bstep (se 1 (by rfl) ⟨2921075, by rfl⟩ : syracuseStep 3894767 = 5842151) B5842151
theorem B3075803 : Blo 1619008 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B4157723 : Blo 1619008 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B14029127 : Blo 1619008 14029127 := bstep (se 1 (by rfl) ⟨10521845, by rfl⟩ : syracuseStep 14029127 = 21043691) B21043691
theorem B36008347 : Blo 1619008 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B7385705 : Blo 1619008 7385705 := bstep (se 2 (by rfl) ⟨2769639, by rfl⟩ : syracuseStep 7385705 = 5539279) B5539279
theorem B213111485 : Blo 1619008 213111485 := bstep (se 3 (by rfl) ⟨39958403, by rfl⟩ : syracuseStep 213111485 = 79916807) B79916807
theorem B1848187 : Blo 1619008 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B5469119 : Blo 1619008 5469119 := bstep (se 1 (by rfl) ⟨4101839, by rfl⟩ : syracuseStep 5469119 = 8203679) B8203679
theorem B8205299 : Blo 1619008 8205299 := bstep (se 1 (by rfl) ⟨6153974, by rfl⟩ : syracuseStep 8205299 = 12307949) B12307949
theorem B2429993 : Blo 1619008 2429993 := bstep (se 2 (by rfl) ⟨911247, by rfl⟩ : syracuseStep 2429993 = 1822495) B1822495
theorem B1619247 : Blo 1619008 1619247 := bstep (se 1 (by rfl) ⟨1214435, by rfl⟩ : syracuseStep 1619247 = 2428871) B2428871
theorem B5469497 : Blo 1619008 5469497 := bstep (se 2 (by rfl) ⟨2051061, by rfl⟩ : syracuseStep 5469497 = 4102123) B4102123
theorem B1619303 : Blo 1619008 1619303 := bstep (se 1 (by rfl) ⟨1214477, by rfl⟩ : syracuseStep 1619303 = 2428955) B2428955
theorem B2430491 : Blo 1619008 2430491 := bstep (se 1 (by rfl) ⟨1822868, by rfl⟩ : syracuseStep 2430491 = 3645737) B3645737
theorem B2430569 : Blo 1619008 2430569 := bstep (se 2 (by rfl) ⟨911463, by rfl⟩ : syracuseStep 2430569 = 1822927) B1822927
theorem B20747933 : Blo 1619008 20747933 := bstep (se 3 (by rfl) ⟨3890237, by rfl⟩ : syracuseStep 20747933 = 7780475) B7780475
theorem B3643055 : Blo 1619008 3643055 := bstep (se 1 (by rfl) ⟨2732291, by rfl⟩ : syracuseStep 3643055 = 5464583) B5464583
theorem B1619687 : Blo 1619008 1619687 := bstep (se 1 (by rfl) ⟨1214765, by rfl⟩ : syracuseStep 1619687 = 2429531) B2429531
theorem B6149951 : Blo 1619008 6149951 := bstep (se 1 (by rfl) ⟨4612463, by rfl⟩ : syracuseStep 6149951 = 9224927) B9224927
theorem B8198009 : Blo 1619008 8198009 := bstep (se 2 (by rfl) ⟨3074253, by rfl⟩ : syracuseStep 8198009 = 6148507) B6148507
theorem B1619879 : Blo 1619008 1619879 := bstep (se 1 (by rfl) ⟨1214909, by rfl⟩ : syracuseStep 1619879 = 2429819) B2429819
theorem B8206271 : Blo 1619008 8206271 := bstep (se 1 (by rfl) ⟨6154703, by rfl⟩ : syracuseStep 8206271 = 12309407) B12309407
theorem B1619935 : Blo 1619008 1619935 := bstep (se 1 (by rfl) ⟨1214951, by rfl⟩ : syracuseStep 1619935 = 2429903) B2429903
theorem B7780321 : Blo 1619008 7780321 := bstep (se 2 (by rfl) ⟨2917620, by rfl⟩ : syracuseStep 7780321 = 5835241) B5835241
theorem B1620135 : Blo 1619008 1620135 := bstep (se 1 (by rfl) ⟨1215101, by rfl⟩ : syracuseStep 1620135 = 2430203) B2430203
theorem B8198495 : Blo 1619008 8198495 := bstep (se 1 (by rfl) ⟨6148871, by rfl⟩ : syracuseStep 8198495 = 12297743) B12297743
theorem B1620463 : Blo 1619008 1620463 := bstep (se 1 (by rfl) ⟨1215347, by rfl⟩ : syracuseStep 1620463 = 2430695) B2430695
theorem B1620731 : Blo 1619008 1620731 := bstep (se 1 (by rfl) ⟨1215548, by rfl⟩ : syracuseStep 1620731 = 2431097) B2431097
theorem B1620763 : Blo 1619008 1620763 := bstep (se 1 (by rfl) ⟨1215572, by rfl⟩ : syracuseStep 1620763 = 2431145) B2431145
theorem B1620767 : Blo 1619008 1620767 := bstep (se 1 (by rfl) ⟨1215575, by rfl⟩ : syracuseStep 1620767 = 2431151) B2431151
theorem B9231191 : Blo 1619008 9231191 := bstep (se 1 (by rfl) ⟨6923393, by rfl⟩ : syracuseStep 9231191 = 13846787) B13846787
theorem B2734951 : Blo 1619008 2734951 := bstep (se 1 (by rfl) ⟨2051213, by rfl⟩ : syracuseStep 2734951 = 4102427) B4102427
theorem B8199143 : Blo 1619008 8199143 := bstep (se 1 (by rfl) ⟨6149357, by rfl⟩ : syracuseStep 8199143 = 12298715) B12298715
theorem B28040377 : Blo 1619008 28040377 := bstep (se 2 (by rfl) ⟨10515141, by rfl⟩ : syracuseStep 28040377 = 21030283) B21030283
theorem B115252571 : Blo 1619008 115252571 := bstep (se 1 (by rfl) ⟨86439428, by rfl⟩ : syracuseStep 115252571 = 172878857) B172878857
theorem B6151727 : Blo 1619008 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B7781939 : Blo 1619008 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B14220953 : Blo 1619008 14220953 := bstep (se 2 (by rfl) ⟨5332857, by rfl⟩ : syracuseStep 14220953 = 10665715) B10665715
theorem B29949863 : Blo 1619008 29949863 := bstep (se 1 (by rfl) ⟨22462397, by rfl⟩ : syracuseStep 29949863 = 44924795) B44924795
theorem B11681759 : Blo 1619008 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B4923803 : Blo 1619008 4923803 := bstep (se 1 (by rfl) ⟨3692852, by rfl⟩ : syracuseStep 4923803 = 7385705) B7385705
theorem B142074323 : Blo 1619008 142074323 := bstep (se 1 (by rfl) ⟨106555742, by rfl⟩ : syracuseStep 142074323 = 213111485) B213111485
theorem B20767205 : Blo 1619008 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B21037657 : Blo 1619008 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B3646079 : Blo 1619008 3646079 := bstep (se 1 (by rfl) ⟨2734559, by rfl⟩ : syracuseStep 3646079 = 5469119) B5469119
theorem B3646331 : Blo 1619008 3646331 := bstep (se 1 (by rfl) ⟨2734748, by rfl⟩ : syracuseStep 3646331 = 5469497) B5469497
theorem B307340189 : Blo 1619008 307340189 := bstep (se 3 (by rfl) ⟨57626285, by rfl⟩ : syracuseStep 307340189 = 115252571) B115252571
theorem B18449531 : Blo 1619008 18449531 := bstep (se 1 (by rfl) ⟨13837148, by rfl⟩ : syracuseStep 18449531 = 27674297) B27674297
theorem B3646601 : Blo 1619008 3646601 := bstep (se 2 (by rfl) ⟨1367475, by rfl⟩ : syracuseStep 3646601 = 2734951) B2734951
theorem B5465339 : Blo 1619008 5465339 := bstep (se 1 (by rfl) ⟨4099004, by rfl⟩ : syracuseStep 5465339 = 8198009) B8198009
theorem B5465663 : Blo 1619008 5465663 := bstep (se 1 (by rfl) ⟨4099247, by rfl⟩ : syracuseStep 5465663 = 8198495) B8198495
theorem B319465205 : Blo 1619008 319465205 := bstep (se 5 (by rfl) ⟨14974931, by rfl⟩ : syracuseStep 319465205 = 29949863) B29949863
theorem B6154127 : Blo 1619008 6154127 := bstep (se 1 (by rfl) ⟨4615595, by rfl⟩ : syracuseStep 6154127 = 9231191) B9231191
theorem B5466095 : Blo 1619008 5466095 := bstep (se 1 (by rfl) ⟨4099571, by rfl⟩ : syracuseStep 5466095 = 8199143) B8199143
theorem B5187959 : Blo 1619008 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B9480635 : Blo 1619008 9480635 := bstep (se 1 (by rfl) ⟨7110476, by rfl⟩ : syracuseStep 9480635 = 14220953) B14220953
theorem B2050535 : Blo 1619008 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B10373761 : Blo 1619008 10373761 := bstep (se 2 (by rfl) ⟨3890160, by rfl⟩ : syracuseStep 10373761 = 7780321) B7780321
theorem B2771815 : Blo 1619008 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B6917345 : Blo 1619008 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B5467391 : Blo 1619008 5467391 := bstep (se 1 (by rfl) ⟨4100543, by rfl⟩ : syracuseStep 5467391 = 8201087) B8201087
theorem B5467499 : Blo 1619008 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B2428553 : Blo 1619008 2428553 := bstep (se 2 (by rfl) ⟨910707, by rfl⟩ : syracuseStep 2428553 = 1821415) B1821415
theorem B13831955 : Blo 1619008 13831955 := bstep (se 1 (by rfl) ⟨10373966, by rfl⟩ : syracuseStep 13831955 = 20747933) B20747933
theorem B2428703 : Blo 1619008 2428703 := bstep (se 1 (by rfl) ⟨1821527, by rfl⟩ : syracuseStep 2428703 = 3643055) B3643055
theorem B4099967 : Blo 1619008 4099967 := bstep (se 1 (by rfl) ⟨3074975, by rfl⟩ : syracuseStep 4099967 = 6149951) B6149951
theorem B2428841 : Blo 1619008 2428841 := bstep (se 2 (by rfl) ⟨910815, by rfl⟩ : syracuseStep 2428841 = 1821631) B1821631
theorem B22180205 : Blo 1619008 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B3945071 : Blo 1619008 3945071 := bstep (se 1 (by rfl) ⟨2958803, by rfl⟩ : syracuseStep 3945071 = 5917607) B5917607
theorem B4101151 : Blo 1619008 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B7787839 : Blo 1619008 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B2430335 : Blo 1619008 2430335 := bstep (se 1 (by rfl) ⟨1822751, by rfl⟩ : syracuseStep 2430335 = 3645503) B3645503
theorem B9352751 : Blo 1619008 9352751 := bstep (se 1 (by rfl) ⟨7014563, by rfl⟩ : syracuseStep 9352751 = 14029127) B14029127
theorem B52549235 : Blo 1619008 52549235 := bstep (se 1 (by rfl) ⟨39411926, by rfl⟩ : syracuseStep 52549235 = 78823853) B78823853
theorem B48011129 : Blo 1619008 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B5470199 : Blo 1619008 5470199 := bstep (se 1 (by rfl) ⟨4102649, by rfl⟩ : syracuseStep 5470199 = 8205299) B8205299
theorem B8755199 : Blo 1619008 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B1619995 : Blo 1619008 1619995 := bstep (se 1 (by rfl) ⟨1214996, by rfl⟩ : syracuseStep 1619995 = 2429993) B2429993
theorem B2431031 : Blo 1619008 2431031 := bstep (se 1 (by rfl) ⟨1823273, by rfl⟩ : syracuseStep 2431031 = 3646547) B3646547
theorem B2431103 : Blo 1619008 2431103 := bstep (se 1 (by rfl) ⟨1823327, by rfl⟩ : syracuseStep 2431103 = 3646655) B3646655
theorem B2734249 : Blo 1619008 2734249 := bstep (se 2 (by rfl) ⟨1025343, by rfl⟩ : syracuseStep 2734249 = 2050687) B2050687
theorem B1620327 : Blo 1619008 1620327 := bstep (se 1 (by rfl) ⟨1215245, by rfl⟩ : syracuseStep 1620327 = 2430491) B2430491
theorem B1620379 : Blo 1619008 1620379 := bstep (se 1 (by rfl) ⟨1215284, by rfl⟩ : syracuseStep 1620379 = 2430569) B2430569
theorem B2464249 : Blo 1619008 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B5470847 : Blo 1619008 5470847 := bstep (se 1 (by rfl) ⟨4103135, by rfl⟩ : syracuseStep 5470847 = 8206271) B8206271
theorem B37387169 : Blo 1619008 37387169 := bstep (se 2 (by rfl) ⟨14020188, by rfl⟩ : syracuseStep 37387169 = 28040377) B28040377
theorem B3645035 : Blo 1619008 3645035 := bstep (se 1 (by rfl) ⟨2733776, by rfl⟩ : syracuseStep 3645035 = 5467553) B5467553
theorem B2596511 : Blo 1619008 2596511 := bstep (se 1 (by rfl) ⟨1947383, by rfl⟩ : syracuseStep 2596511 = 3894767) B3894767
theorem B3645665 : Blo 1619008 3645665 := bstep (se 2 (by rfl) ⟨1367124, by rfl⟩ : syracuseStep 3645665 = 2734249) B2734249
theorem B14786803 : Blo 1619008 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B94716215 : Blo 1619008 94716215 := bstep (se 1 (by rfl) ⟨71037161, by rfl⟩ : syracuseStep 94716215 = 142074323) B142074323
theorem B13844803 : Blo 1619008 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B3285665 : Blo 1619008 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B28050209 : Blo 1619008 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B3695753 : Blo 1619008 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B212976803 : Blo 1619008 212976803 := bstep (se 1 (by rfl) ⟨159732602, by rfl⟩ : syracuseStep 212976803 = 319465205) B319465205
theorem B32007419 : Blo 1619008 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B3646799 : Blo 1619008 3646799 := bstep (se 1 (by rfl) ⟨2735099, by rfl⟩ : syracuseStep 3646799 = 5470199) B5470199
theorem B3458639 : Blo 1619008 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B10520189 : Blo 1619008 10520189 := bstep (se 3 (by rfl) ⟨1972535, by rfl⟩ : syracuseStep 10520189 = 3945071) B3945071
theorem B3647231 : Blo 1619008 3647231 := bstep (se 1 (by rfl) ⟨2735423, by rfl⟩ : syracuseStep 3647231 = 5470847) B5470847
theorem B1731007 : Blo 1619008 1731007 := bstep (se 1 (by rfl) ⟨1298255, by rfl⟩ : syracuseStep 1731007 = 2596511) B2596511
theorem B204893459 : Blo 1619008 204893459 := bstep (se 1 (by rfl) ⟨153670094, by rfl⟩ : syracuseStep 204893459 = 307340189) B307340189
theorem B12299687 : Blo 1619008 12299687 := bstep (se 1 (by rfl) ⟨9224765, by rfl⟩ : syracuseStep 12299687 = 18449531) B18449531
theorem B13831681 : Blo 1619008 13831681 := bstep (se 2 (by rfl) ⟨5186880, by rfl⟩ : syracuseStep 13831681 = 10373761) B10373761
theorem B35032823 : Blo 1619008 35032823 := bstep (se 1 (by rfl) ⟨26274617, by rfl⟩ : syracuseStep 35032823 = 52549235) B52549235
theorem B5468093 : Blo 1619008 5468093 := bstep (se 3 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 5468093 = 2050535) B2050535
theorem B5836799 : Blo 1619008 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B5468201 : Blo 1619008 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B24940669 : Blo 1619008 24940669 := bstep (se 3 (by rfl) ⟨4676375, by rfl⟩ : syracuseStep 24940669 = 9352751) B9352751
theorem B6320423 : Blo 1619008 6320423 := bstep (se 1 (by rfl) ⟨4740317, by rfl⟩ : syracuseStep 6320423 = 9480635) B9480635
theorem B10383785 : Blo 1619008 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B24924779 : Blo 1619008 24924779 := bstep (se 1 (by rfl) ⟨18693584, by rfl⟩ : syracuseStep 24924779 = 37387169) B37387169
theorem B2430023 : Blo 1619008 2430023 := bstep (se 1 (by rfl) ⟨1822517, by rfl⟩ : syracuseStep 2430023 = 3645035) B3645035
theorem B1619035 : Blo 1619008 1619035 := bstep (se 1 (by rfl) ⟨1214276, by rfl⟩ : syracuseStep 1619035 = 2428553) B2428553
theorem B9221303 : Blo 1619008 9221303 := bstep (se 1 (by rfl) ⟨6915977, by rfl⟩ : syracuseStep 9221303 = 13831955) B13831955
theorem B1619135 : Blo 1619008 1619135 := bstep (se 1 (by rfl) ⟨1214351, by rfl⟩ : syracuseStep 1619135 = 2428703) B2428703
theorem B2733311 : Blo 1619008 2733311 := bstep (se 1 (by rfl) ⟨2049983, by rfl⟩ : syracuseStep 2733311 = 4099967) B4099967
theorem B1619227 : Blo 1619008 1619227 := bstep (se 1 (by rfl) ⟨1214420, by rfl⟩ : syracuseStep 1619227 = 2428841) B2428841
theorem B3282535 : Blo 1619008 3282535 := bstep (se 1 (by rfl) ⟨2461901, by rfl⟩ : syracuseStep 3282535 = 4923803) B4923803
theorem B2430719 : Blo 1619008 2430719 := bstep (se 1 (by rfl) ⟨1823039, by rfl⟩ : syracuseStep 2430719 = 3646079) B3646079
theorem B2430887 : Blo 1619008 2430887 := bstep (se 1 (by rfl) ⟨1823165, by rfl⟩ : syracuseStep 2430887 = 3646331) B3646331
theorem B2431067 : Blo 1619008 2431067 := bstep (se 1 (by rfl) ⟨1823300, by rfl⟩ : syracuseStep 2431067 = 3646601) B3646601
theorem B3643559 : Blo 1619008 3643559 := bstep (se 1 (by rfl) ⟨2732669, by rfl⟩ : syracuseStep 3643559 = 5465339) B5465339
theorem B1620223 : Blo 1619008 1620223 := bstep (se 1 (by rfl) ⟨1215167, by rfl⟩ : syracuseStep 1620223 = 2430335) B2430335
theorem B3643775 : Blo 1619008 3643775 := bstep (se 1 (by rfl) ⟨2732831, by rfl⟩ : syracuseStep 3643775 = 5465663) B5465663
theorem B4102751 : Blo 1619008 4102751 := bstep (se 1 (by rfl) ⟨3077063, by rfl⟩ : syracuseStep 4102751 = 6154127) B6154127
theorem B3644063 : Blo 1619008 3644063 := bstep (se 1 (by rfl) ⟨2733047, by rfl⟩ : syracuseStep 3644063 = 5466095) B5466095
theorem B1620687 : Blo 1619008 1620687 := bstep (se 1 (by rfl) ⟨1215515, by rfl⟩ : syracuseStep 1620687 = 2431031) B2431031
theorem B1620735 : Blo 1619008 1620735 := bstep (se 1 (by rfl) ⟨1215551, by rfl⟩ : syracuseStep 1620735 = 2431103) B2431103
theorem B4611563 : Blo 1619008 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B3644927 : Blo 1619008 3644927 := bstep (se 1 (by rfl) ⟨2733695, by rfl⟩ : syracuseStep 3644927 = 5467391) B5467391
theorem B3644999 : Blo 1619008 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B3645467 : Blo 1619008 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B63144143 : Blo 1619008 63144143 := bstep (se 1 (by rfl) ⟨47358107, by rfl⟩ : syracuseStep 63144143 = 94716215) B94716215
theorem B6922523 : Blo 1619008 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B9855341 : Blo 1619008 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B17506853 : Blo 1619008 17506853 := bstep (se 4 (by rfl) ⟨1641267, by rfl⟩ : syracuseStep 17506853 = 3282535) B3282535
theorem B141984535 : Blo 1619008 141984535 := bstep (se 1 (by rfl) ⟨106488401, by rfl⟩ : syracuseStep 141984535 = 212976803) B212976803
theorem B7013459 : Blo 1619008 7013459 := bstep (se 1 (by rfl) ⟨5260094, by rfl⟩ : syracuseStep 7013459 = 10520189) B10520189
theorem B18442241 : Blo 1619008 18442241 := bstep (se 2 (by rfl) ⟨6915840, by rfl⟩ : syracuseStep 18442241 = 13831681) B13831681
theorem B136595639 : Blo 1619008 136595639 := bstep (se 1 (by rfl) ⟨102446729, by rfl⟩ : syracuseStep 136595639 = 204893459) B204893459
theorem B3074375 : Blo 1619008 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B33254225 : Blo 1619008 33254225 := bstep (se 2 (by rfl) ⟨12470334, by rfl⟩ : syracuseStep 33254225 = 24940669) B24940669
theorem B4213615 : Blo 1619008 4213615 := bstep (se 1 (by rfl) ⟨3160211, by rfl⟩ : syracuseStep 4213615 = 6320423) B6320423
theorem B16616519 : Blo 1619008 16616519 := bstep (se 1 (by rfl) ⟨12462389, by rfl⟩ : syracuseStep 16616519 = 24924779) B24924779
theorem B18459737 : Blo 1619008 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B2190443 : Blo 1619008 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B6147535 : Blo 1619008 6147535 := bstep (se 1 (by rfl) ⟨4610651, by rfl⟩ : syracuseStep 6147535 = 9221303) B9221303
theorem B1822207 : Blo 1619008 1822207 := bstep (se 1 (by rfl) ⟨1366655, by rfl⟩ : syracuseStep 1822207 = 2733311) B2733311
theorem B2305759 : Blo 1619008 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B2429039 : Blo 1619008 2429039 := bstep (se 1 (by rfl) ⟨1821779, by rfl⟩ : syracuseStep 2429039 = 3643559) B3643559
theorem B2429183 : Blo 1619008 2429183 := bstep (se 1 (by rfl) ⟨1821887, by rfl⟩ : syracuseStep 2429183 = 3643775) B3643775
theorem B2429375 : Blo 1619008 2429375 := bstep (se 1 (by rfl) ⟨1822031, by rfl⟩ : syracuseStep 2429375 = 3644063) B3644063
theorem B2429951 : Blo 1619008 2429951 := bstep (se 1 (by rfl) ⟨1822463, by rfl⟩ : syracuseStep 2429951 = 3644927) B3644927
theorem B2429999 : Blo 1619008 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B2430443 : Blo 1619008 2430443 := bstep (se 1 (by rfl) ⟨1822832, by rfl⟩ : syracuseStep 2430443 = 3645665) B3645665
theorem B19715737 : Blo 1619008 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B18700139 : Blo 1619008 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B2308009 : Blo 1619008 2308009 := bstep (se 2 (by rfl) ⟨865503, by rfl⟩ : syracuseStep 2308009 = 1731007) B1731007
theorem B1620015 : Blo 1619008 1620015 := bstep (se 1 (by rfl) ⟨1215011, by rfl⟩ : syracuseStep 1620015 = 2430023) B2430023
theorem B21338279 : Blo 1619008 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B2431199 : Blo 1619008 2431199 := bstep (se 1 (by rfl) ⟨1823399, by rfl⟩ : syracuseStep 2431199 = 3646799) B3646799
theorem B1620479 : Blo 1619008 1620479 := bstep (se 1 (by rfl) ⟨1215359, by rfl⟩ : syracuseStep 1620479 = 2430719) B2430719
theorem B2431487 : Blo 1619008 2431487 := bstep (se 1 (by rfl) ⟨1823615, by rfl⟩ : syracuseStep 2431487 = 3647231) B3647231
theorem B1620591 : Blo 1619008 1620591 := bstep (se 1 (by rfl) ⟨1215443, by rfl⟩ : syracuseStep 1620591 = 2430887) B2430887
theorem B1620711 : Blo 1619008 1620711 := bstep (se 1 (by rfl) ⟨1215533, by rfl⟩ : syracuseStep 1620711 = 2431067) B2431067
theorem B2735167 : Blo 1619008 2735167 := bstep (se 1 (by rfl) ⟨2051375, by rfl⟩ : syracuseStep 2735167 = 4102751) B4102751
theorem B8199791 : Blo 1619008 8199791 := bstep (se 1 (by rfl) ⟨6149843, by rfl⟩ : syracuseStep 8199791 = 12299687) B12299687
theorem B23355215 : Blo 1619008 23355215 := bstep (se 1 (by rfl) ⟨17516411, by rfl⟩ : syracuseStep 23355215 = 35032823) B35032823
theorem B3645395 : Blo 1619008 3645395 := bstep (se 1 (by rfl) ⟨2734046, by rfl⟩ : syracuseStep 3645395 = 5468093) B5468093
theorem B15564797 : Blo 1619008 15564797 := bstep (se 3 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 15564797 = 5836799) B5836799
theorem B6570227 : Blo 1619008 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B5841181 : Blo 1619008 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B3646889 : Blo 1619008 3646889 := bstep (se 2 (by rfl) ⟨1367583, by rfl⟩ : syracuseStep 3646889 = 2735167) B2735167
theorem B91063759 : Blo 1619008 91063759 := bstep (se 1 (by rfl) ⟨68297819, by rfl⟩ : syracuseStep 91063759 = 136595639) B136595639
theorem B22169483 : Blo 1619008 22169483 := bstep (se 1 (by rfl) ⟨16627112, by rfl⟩ : syracuseStep 22169483 = 33254225) B33254225
theorem B11077679 : Blo 1619008 11077679 := bstep (se 1 (by rfl) ⟨8308259, by rfl⟩ : syracuseStep 11077679 = 16616519) B16616519
theorem B12306491 : Blo 1619008 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B3074345 : Blo 1619008 3074345 := bstep (se 2 (by rfl) ⟨1152879, by rfl⟩ : syracuseStep 3074345 = 2305759) B2305759
theorem B5466527 : Blo 1619008 5466527 := bstep (se 1 (by rfl) ⟨4099895, by rfl⟩ : syracuseStep 5466527 = 8199791) B8199791
theorem B4615015 : Blo 1619008 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B189312713 : Blo 1619008 189312713 := bstep (se 2 (by rfl) ⟨70992267, by rfl⟩ : syracuseStep 189312713 = 141984535) B141984535
theorem B14225519 : Blo 1619008 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B8196713 : Blo 1619008 8196713 := bstep (se 2 (by rfl) ⟨3073767, by rfl⟩ : syracuseStep 8196713 = 6147535) B6147535
theorem B2429609 : Blo 1619008 2429609 := bstep (se 2 (by rfl) ⟨911103, by rfl⟩ : syracuseStep 2429609 = 1822207) B1822207
theorem B15570143 : Blo 1619008 15570143 := bstep (se 1 (by rfl) ⟨11677607, by rfl⟩ : syracuseStep 15570143 = 23355215) B23355215
theorem B3077345 : Blo 1619008 3077345 := bstep (se 2 (by rfl) ⟨1154004, by rfl⟩ : syracuseStep 3077345 = 2308009) B2308009
theorem B2430263 : Blo 1619008 2430263 := bstep (se 1 (by rfl) ⟨1822697, by rfl⟩ : syracuseStep 2430263 = 3645395) B3645395
theorem B10376531 : Blo 1619008 10376531 := bstep (se 1 (by rfl) ⟨7782398, by rfl⟩ : syracuseStep 10376531 = 15564797) B15564797
theorem B2430311 : Blo 1619008 2430311 := bstep (se 1 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 2430311 = 3645467) B3645467
theorem B1619359 : Blo 1619008 1619359 := bstep (se 1 (by rfl) ⟨1214519, by rfl⟩ : syracuseStep 1619359 = 2429039) B2429039
theorem B42096095 : Blo 1619008 42096095 := bstep (se 1 (by rfl) ⟨31572071, by rfl⟩ : syracuseStep 42096095 = 63144143) B63144143
theorem B1619455 : Blo 1619008 1619455 := bstep (se 1 (by rfl) ⟨1214591, by rfl⟩ : syracuseStep 1619455 = 2429183) B2429183
theorem B1619583 : Blo 1619008 1619583 := bstep (se 1 (by rfl) ⟨1214687, by rfl⟩ : syracuseStep 1619583 = 2429375) B2429375
theorem B11671235 : Blo 1619008 11671235 := bstep (se 1 (by rfl) ⟨8753426, by rfl⟩ : syracuseStep 11671235 = 17506853) B17506853
theorem B1619967 : Blo 1619008 1619967 := bstep (se 1 (by rfl) ⟨1214975, by rfl⟩ : syracuseStep 1619967 = 2429951) B2429951
theorem B1619999 : Blo 1619008 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B4675639 : Blo 1619008 4675639 := bstep (se 1 (by rfl) ⟨3506729, by rfl⟩ : syracuseStep 4675639 = 7013459) B7013459
theorem B8198333 : Blo 1619008 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B1620295 : Blo 1619008 1620295 := bstep (se 1 (by rfl) ⟨1215221, by rfl⟩ : syracuseStep 1620295 = 2430443) B2430443
theorem B5618153 : Blo 1619008 5618153 := bstep (se 2 (by rfl) ⟨2106807, by rfl⟩ : syracuseStep 5618153 = 4213615) B4213615
theorem B12466759 : Blo 1619008 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B12294827 : Blo 1619008 12294827 := bstep (se 1 (by rfl) ⟨9221120, by rfl⟩ : syracuseStep 12294827 = 18442241) B18442241
theorem B1620799 : Blo 1619008 1620799 := bstep (se 1 (by rfl) ⟨1215599, by rfl⟩ : syracuseStep 1620799 = 2431199) B2431199
theorem B1620991 : Blo 1619008 1620991 := bstep (se 1 (by rfl) ⟨1215743, by rfl⟩ : syracuseStep 1620991 = 2431487) B2431487
theorem B26287649 : Blo 1619008 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B6234185 : Blo 1619008 6234185 := bstep (se 2 (by rfl) ⟨2337819, by rfl⟩ : syracuseStep 6234185 = 4675639) B4675639
theorem B29540477 : Blo 1619008 29540477 := bstep (se 3 (by rfl) ⟨5538839, by rfl⟩ : syracuseStep 29540477 = 11077679) B11077679
theorem B5464475 : Blo 1619008 5464475 := bstep (se 1 (by rfl) ⟨4098356, by rfl⟩ : syracuseStep 5464475 = 8196713) B8196713
theorem B16622345 : Blo 1619008 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B10380095 : Blo 1619008 10380095 := bstep (se 1 (by rfl) ⟨7785071, by rfl⟩ : syracuseStep 10380095 = 15570143) B15570143
theorem B6153353 : Blo 1619008 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B14779655 : Blo 1619008 14779655 := bstep (se 1 (by rfl) ⟨11084741, by rfl⟩ : syracuseStep 14779655 = 22169483) B22169483
theorem B5465555 : Blo 1619008 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B2049563 : Blo 1619008 2049563 := bstep (se 1 (by rfl) ⟨1537172, by rfl⟩ : syracuseStep 2049563 = 3074345) B3074345
theorem B3745435 : Blo 1619008 3745435 := bstep (se 1 (by rfl) ⟨2809076, by rfl⟩ : syracuseStep 3745435 = 5618153) B5618153
theorem B17525099 : Blo 1619008 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B126208475 : Blo 1619008 126208475 := bstep (se 1 (by rfl) ⟨94656356, by rfl⟩ : syracuseStep 126208475 = 189312713) B189312713
theorem B2051563 : Blo 1619008 2051563 := bstep (se 1 (by rfl) ⟨1538672, by rfl⟩ : syracuseStep 2051563 = 3077345) B3077345
theorem B6917687 : Blo 1619008 6917687 := bstep (se 1 (by rfl) ⟨5188265, by rfl⟩ : syracuseStep 6917687 = 10376531) B10376531
theorem B8204327 : Blo 1619008 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B8196551 : Blo 1619008 8196551 := bstep (se 1 (by rfl) ⟨6147413, by rfl⟩ : syracuseStep 8196551 = 12294827) B12294827
theorem B9483679 : Blo 1619008 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B121418345 : Blo 1619008 121418345 := bstep (se 2 (by rfl) ⟨45531879, by rfl⟩ : syracuseStep 121418345 = 91063759) B91063759
theorem B4380151 : Blo 1619008 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B7788241 : Blo 1619008 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B1619739 : Blo 1619008 1619739 := bstep (se 1 (by rfl) ⟨1214804, by rfl⟩ : syracuseStep 1619739 = 2429609) B2429609
theorem B1620175 : Blo 1619008 1620175 := bstep (se 1 (by rfl) ⟨1215131, by rfl⟩ : syracuseStep 1620175 = 2430263) B2430263
theorem B1620207 : Blo 1619008 1620207 := bstep (se 1 (by rfl) ⟨1215155, by rfl⟩ : syracuseStep 1620207 = 2430311) B2430311
theorem B2431259 : Blo 1619008 2431259 := bstep (se 1 (by rfl) ⟨1823444, by rfl⟩ : syracuseStep 2431259 = 3646889) B3646889
theorem B28064063 : Blo 1619008 28064063 := bstep (se 1 (by rfl) ⟨21048047, by rfl⟩ : syracuseStep 28064063 = 42096095) B42096095
theorem B7780823 : Blo 1619008 7780823 := bstep (se 1 (by rfl) ⟨5835617, by rfl⟩ : syracuseStep 7780823 = 11671235) B11671235
theorem B3644351 : Blo 1619008 3644351 := bstep (se 1 (by rfl) ⟨2733263, by rfl⟩ : syracuseStep 3644351 = 5466527) B5466527
theorem B19693651 : Blo 1619008 19693651 := bstep (se 1 (by rfl) ⟨14770238, by rfl⟩ : syracuseStep 19693651 = 29540477) B29540477
theorem B5464367 : Blo 1619008 5464367 := bstep (se 1 (by rfl) ⟨4098275, by rfl⟩ : syracuseStep 5464367 = 8196551) B8196551
theorem B80945563 : Blo 1619008 80945563 := bstep (se 1 (by rfl) ⟨60709172, by rfl⟩ : syracuseStep 80945563 = 121418345) B121418345
theorem B5465501 : Blo 1619008 5465501 := bstep (se 3 (by rfl) ⟨1024781, by rfl⟩ : syracuseStep 5465501 = 2049563) B2049563
theorem B11683399 : Blo 1619008 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B5187215 : Blo 1619008 5187215 := bstep (se 1 (by rfl) ⟨3890411, by rfl⟩ : syracuseStep 5187215 = 7780823) B7780823
theorem B50579621 : Blo 1619008 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B4156123 : Blo 1619008 4156123 := bstep (se 1 (by rfl) ⟨3117092, by rfl⟩ : syracuseStep 4156123 = 6234185) B6234185
theorem B2429567 : Blo 1619008 2429567 := bstep (se 1 (by rfl) ⟨1822175, by rfl⟩ : syracuseStep 2429567 = 3644351) B3644351
theorem B4993913 : Blo 1619008 4993913 := bstep (se 2 (by rfl) ⟨1872717, by rfl⟩ : syracuseStep 4993913 = 3745435) B3745435
theorem B10384321 : Blo 1619008 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B5469551 : Blo 1619008 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B3642983 : Blo 1619008 3642983 := bstep (se 1 (by rfl) ⟨2732237, by rfl⟩ : syracuseStep 3642983 = 5464475) B5464475
theorem B6920063 : Blo 1619008 6920063 := bstep (se 1 (by rfl) ⟨5190047, by rfl⟩ : syracuseStep 6920063 = 10380095) B10380095
theorem B4102235 : Blo 1619008 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B9853103 : Blo 1619008 9853103 := bstep (se 1 (by rfl) ⟨7389827, by rfl⟩ : syracuseStep 9853103 = 14779655) B14779655
theorem B3643703 : Blo 1619008 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B1620839 : Blo 1619008 1620839 := bstep (se 1 (by rfl) ⟨1215629, by rfl⟩ : syracuseStep 1620839 = 2431259) B2431259
theorem B18709375 : Blo 1619008 18709375 := bstep (se 1 (by rfl) ⟨14032031, by rfl⟩ : syracuseStep 18709375 = 28064063) B28064063
theorem B84138983 : Blo 1619008 84138983 := bstep (se 1 (by rfl) ⟨63104237, by rfl⟩ : syracuseStep 84138983 = 126208475) B126208475
theorem B2735417 : Blo 1619008 2735417 := bstep (se 2 (by rfl) ⟨1025781, by rfl⟩ : syracuseStep 2735417 = 2051563) B2051563
theorem B5840201 : Blo 1619008 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B44326253 : Blo 1619008 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B4611791 : Blo 1619008 4611791 := bstep (se 1 (by rfl) ⟨3458843, by rfl⟩ : syracuseStep 4611791 = 6917687) B6917687
theorem B15573869 : Blo 1619008 15573869 := bstep (se 3 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 15573869 = 5840201) B5840201
theorem B3646367 : Blo 1619008 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B3458143 : Blo 1619008 3458143 := bstep (se 1 (by rfl) ⟨2593607, by rfl⟩ : syracuseStep 3458143 = 5187215) B5187215
theorem B24945833 : Blo 1619008 24945833 := bstep (se 2 (by rfl) ⟨9354687, by rfl⟩ : syracuseStep 24945833 = 18709375) B18709375
theorem B4613375 : Blo 1619008 4613375 := bstep (se 1 (by rfl) ⟨3460031, by rfl⟩ : syracuseStep 4613375 = 6920063) B6920063
theorem B13845761 : Blo 1619008 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B33719747 : Blo 1619008 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B56092655 : Blo 1619008 56092655 := bstep (se 1 (by rfl) ⟨42069491, by rfl⟩ : syracuseStep 56092655 = 84138983) B84138983
theorem B29550835 : Blo 1619008 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B3074527 : Blo 1619008 3074527 := bstep (se 1 (by rfl) ⟨2305895, by rfl⟩ : syracuseStep 3074527 = 4611791) B4611791
theorem B26258201 : Blo 1619008 26258201 := bstep (se 2 (by rfl) ⟨9846825, by rfl⟩ : syracuseStep 26258201 = 19693651) B19693651
theorem B5541497 : Blo 1619008 5541497 := bstep (se 2 (by rfl) ⟨2078061, by rfl⟩ : syracuseStep 5541497 = 4156123) B4156123
theorem B2428655 : Blo 1619008 2428655 := bstep (se 1 (by rfl) ⟨1821491, by rfl⟩ : syracuseStep 2428655 = 3642983) B3642983
theorem B2429135 : Blo 1619008 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B15577865 : Blo 1619008 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B1823611 : Blo 1619008 1823611 := bstep (se 1 (by rfl) ⟨1367708, by rfl⟩ : syracuseStep 1823611 = 2735417) B2735417
theorem B13317101 : Blo 1619008 13317101 := bstep (se 3 (by rfl) ⟨2496956, by rfl⟩ : syracuseStep 13317101 = 4993913) B4993913
theorem B3642911 : Blo 1619008 3642911 := bstep (se 1 (by rfl) ⟨2732183, by rfl⟩ : syracuseStep 3642911 = 5464367) B5464367
theorem B1619711 : Blo 1619008 1619711 := bstep (se 1 (by rfl) ⟨1214783, by rfl⟩ : syracuseStep 1619711 = 2429567) B2429567
theorem B107927417 : Blo 1619008 107927417 := bstep (se 2 (by rfl) ⟨40472781, by rfl⟩ : syracuseStep 107927417 = 80945563) B80945563
theorem B3643667 : Blo 1619008 3643667 := bstep (se 1 (by rfl) ⟨2732750, by rfl⟩ : syracuseStep 3643667 = 5465501) B5465501
theorem B2734823 : Blo 1619008 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B6568735 : Blo 1619008 6568735 := bstep (se 1 (by rfl) ⟨4926551, by rfl⟩ : syracuseStep 6568735 = 9853103) B9853103
theorem B8758313 : Blo 1619008 8758313 := bstep (se 2 (by rfl) ⟨3284367, by rfl⟩ : syracuseStep 8758313 = 6568735) B6568735
theorem B66522221 : Blo 1619008 66522221 := bstep (se 3 (by rfl) ⟨12472916, by rfl⟩ : syracuseStep 66522221 = 24945833) B24945833
theorem B10382579 : Blo 1619008 10382579 := bstep (se 1 (by rfl) ⟨7786934, by rfl⟩ : syracuseStep 10382579 = 15573869) B15573869
theorem B4099369 : Blo 1619008 4099369 := bstep (se 2 (by rfl) ⟨1537263, by rfl⟩ : syracuseStep 4099369 = 3074527) B3074527
theorem B3075583 : Blo 1619008 3075583 := bstep (se 1 (by rfl) ⟨2306687, by rfl⟩ : syracuseStep 3075583 = 4613375) B4613375
theorem B2428607 : Blo 1619008 2428607 := bstep (se 1 (by rfl) ⟨1821455, by rfl⟩ : syracuseStep 2428607 = 3642911) B3642911
theorem B89919325 : Blo 1619008 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B2429111 : Blo 1619008 2429111 := bstep (se 1 (by rfl) ⟨1821833, by rfl⟩ : syracuseStep 2429111 = 3643667) B3643667
theorem B1823215 : Blo 1619008 1823215 := bstep (se 1 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 1823215 = 2734823) B2734823
theorem B287806445 : Blo 1619008 287806445 := bstep (se 3 (by rfl) ⟨53963708, by rfl⟩ : syracuseStep 287806445 = 107927417) B107927417
theorem B1619103 : Blo 1619008 1619103 := bstep (se 1 (by rfl) ⟨1214327, by rfl⟩ : syracuseStep 1619103 = 2428655) B2428655
theorem B1619423 : Blo 1619008 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B39401113 : Blo 1619008 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B10385243 : Blo 1619008 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B2430911 : Blo 1619008 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B8878067 : Blo 1619008 8878067 := bstep (se 1 (by rfl) ⟨6658550, by rfl⟩ : syracuseStep 8878067 = 13317101) B13317101
theorem B9230507 : Blo 1619008 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B2431481 : Blo 1619008 2431481 := bstep (se 2 (by rfl) ⟨911805, by rfl⟩ : syracuseStep 2431481 = 1823611) B1823611
theorem B37395103 : Blo 1619008 37395103 := bstep (se 1 (by rfl) ⟨28046327, by rfl⟩ : syracuseStep 37395103 = 56092655) B56092655
theorem B4610857 : Blo 1619008 4610857 := bstep (se 2 (by rfl) ⟨1729071, by rfl⟩ : syracuseStep 4610857 = 3458143) B3458143
theorem B17505467 : Blo 1619008 17505467 := bstep (se 1 (by rfl) ⟨13129100, by rfl⟩ : syracuseStep 17505467 = 26258201) B26258201
theorem B3694331 : Blo 1619008 3694331 := bstep (se 1 (by rfl) ⟨2770748, by rfl⟩ : syracuseStep 3694331 = 5541497) B5541497
theorem B6923495 : Blo 1619008 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B6153671 : Blo 1619008 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B5465825 : Blo 1619008 5465825 := bstep (se 2 (by rfl) ⟨2049684, by rfl⟩ : syracuseStep 5465825 = 4099369) B4099369
theorem B479569733 : Blo 1619008 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B49860137 : Blo 1619008 49860137 := bstep (se 2 (by rfl) ⟨18697551, by rfl⟩ : syracuseStep 49860137 = 37395103) B37395103
theorem B6147809 : Blo 1619008 6147809 := bstep (se 2 (by rfl) ⟨2305428, by rfl⟩ : syracuseStep 6147809 = 4610857) B4610857
theorem B5918711 : Blo 1619008 5918711 := bstep (se 1 (by rfl) ⟨4439033, by rfl⟩ : syracuseStep 5918711 = 8878067) B8878067
theorem B4100777 : Blo 1619008 4100777 := bstep (se 2 (by rfl) ⟨1537791, by rfl⟩ : syracuseStep 4100777 = 3075583) B3075583
theorem B44348147 : Blo 1619008 44348147 := bstep (se 1 (by rfl) ⟨33261110, by rfl⟩ : syracuseStep 44348147 = 66522221) B66522221
theorem B11670311 : Blo 1619008 11670311 := bstep (se 1 (by rfl) ⟨8752733, by rfl⟩ : syracuseStep 11670311 = 17505467) B17505467
theorem B1619071 : Blo 1619008 1619071 := bstep (se 1 (by rfl) ⟨1214303, by rfl⟩ : syracuseStep 1619071 = 2428607) B2428607
theorem B2462887 : Blo 1619008 2462887 := bstep (se 1 (by rfl) ⟨1847165, by rfl⟩ : syracuseStep 2462887 = 3694331) B3694331
theorem B1619407 : Blo 1619008 1619407 := bstep (se 1 (by rfl) ⟨1214555, by rfl⟩ : syracuseStep 1619407 = 2429111) B2429111
theorem B2430953 : Blo 1619008 2430953 := bstep (se 2 (by rfl) ⟨911607, by rfl⟩ : syracuseStep 2430953 = 1823215) B1823215
theorem B191870963 : Blo 1619008 191870963 := bstep (se 1 (by rfl) ⟨143903222, by rfl⟩ : syracuseStep 191870963 = 287806445) B287806445
theorem B5838875 : Blo 1619008 5838875 := bstep (se 1 (by rfl) ⟨4379156, by rfl⟩ : syracuseStep 5838875 = 8758313) B8758313
theorem B1620607 : Blo 1619008 1620607 := bstep (se 1 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 1620607 = 2430911) B2430911
theorem B1620987 : Blo 1619008 1620987 := bstep (se 1 (by rfl) ⟨1215740, by rfl⟩ : syracuseStep 1620987 = 2431481) B2431481
theorem B6921719 : Blo 1619008 6921719 := bstep (se 1 (by rfl) ⟨5191289, by rfl⟩ : syracuseStep 6921719 = 10382579) B10382579
theorem B52534817 : Blo 1619008 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B29565431 : Blo 1619008 29565431 := bstep (se 1 (by rfl) ⟨22174073, by rfl⟩ : syracuseStep 29565431 = 44348147) B44348147
theorem B3892583 : Blo 1619008 3892583 := bstep (se 1 (by rfl) ⟨2919437, by rfl⟩ : syracuseStep 3892583 = 5838875) B5838875
theorem B4614479 : Blo 1619008 4614479 := bstep (se 1 (by rfl) ⟨3460859, by rfl⟩ : syracuseStep 4614479 = 6921719) B6921719
theorem B35023211 : Blo 1619008 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B4098539 : Blo 1619008 4098539 := bstep (se 1 (by rfl) ⟨3073904, by rfl⟩ : syracuseStep 4098539 = 6147809) B6147809
theorem B319713155 : Blo 1619008 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B127913975 : Blo 1619008 127913975 := bstep (se 1 (by rfl) ⟨95935481, by rfl⟩ : syracuseStep 127913975 = 191870963) B191870963
theorem B33240091 : Blo 1619008 33240091 := bstep (se 1 (by rfl) ⟨24930068, by rfl⟩ : syracuseStep 33240091 = 49860137) B49860137
theorem B15783229 : Blo 1619008 15783229 := bstep (se 3 (by rfl) ⟨2959355, by rfl⟩ : syracuseStep 15783229 = 5918711) B5918711
theorem B2733851 : Blo 1619008 2733851 := bstep (se 1 (by rfl) ⟨2050388, by rfl⟩ : syracuseStep 2733851 = 4100777) B4100777
theorem B7780207 : Blo 1619008 7780207 := bstep (se 1 (by rfl) ⟨5835155, by rfl⟩ : syracuseStep 7780207 = 11670311) B11670311
theorem B18462653 : Blo 1619008 18462653 := bstep (se 3 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 18462653 = 6923495) B6923495
theorem B4102447 : Blo 1619008 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B3643883 : Blo 1619008 3643883 := bstep (se 1 (by rfl) ⟨2732912, by rfl⟩ : syracuseStep 3643883 = 5465825) B5465825
theorem B1620635 : Blo 1619008 1620635 := bstep (se 1 (by rfl) ⟨1215476, by rfl⟩ : syracuseStep 1620635 = 2430953) B2430953
theorem B3283849 : Blo 1619008 3283849 := bstep (se 2 (by rfl) ⟨1231443, by rfl⟩ : syracuseStep 3283849 = 2462887) B2462887
theorem B19710287 : Blo 1619008 19710287 := bstep (se 1 (by rfl) ⟨14782715, by rfl⟩ : syracuseStep 19710287 = 29565431) B29565431
theorem B10380221 : Blo 1619008 10380221 := bstep (se 3 (by rfl) ⟨1946291, by rfl⟩ : syracuseStep 10380221 = 3892583) B3892583
theorem B44320121 : Blo 1619008 44320121 := bstep (se 2 (by rfl) ⟨16620045, by rfl⟩ : syracuseStep 44320121 = 33240091) B33240091
theorem B23348807 : Blo 1619008 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B10373609 : Blo 1619008 10373609 := bstep (se 2 (by rfl) ⟨3890103, by rfl⟩ : syracuseStep 10373609 = 7780207) B7780207
theorem B213142103 : Blo 1619008 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B4378465 : Blo 1619008 4378465 := bstep (se 2 (by rfl) ⟨1641924, by rfl⟩ : syracuseStep 4378465 = 3283849) B3283849
theorem B1822567 : Blo 1619008 1822567 := bstep (se 1 (by rfl) ⟨1366925, by rfl⟩ : syracuseStep 1822567 = 2733851) B2733851
theorem B12308435 : Blo 1619008 12308435 := bstep (se 1 (by rfl) ⟨9231326, by rfl⟩ : syracuseStep 12308435 = 18462653) B18462653
theorem B3076319 : Blo 1619008 3076319 := bstep (se 1 (by rfl) ⟨2307239, by rfl⟩ : syracuseStep 3076319 = 4614479) B4614479
theorem B2732359 : Blo 1619008 2732359 := bstep (se 1 (by rfl) ⟨2049269, by rfl⟩ : syracuseStep 2732359 = 4098539) B4098539
theorem B2429255 : Blo 1619008 2429255 := bstep (se 1 (by rfl) ⟨1821941, by rfl⟩ : syracuseStep 2429255 = 3643883) B3643883
theorem B85275983 : Blo 1619008 85275983 := bstep (se 1 (by rfl) ⟨63956987, by rfl⟩ : syracuseStep 85275983 = 127913975) B127913975
theorem B5469929 : Blo 1619008 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B21044305 : Blo 1619008 21044305 := bstep (se 2 (by rfl) ⟨7891614, by rfl⟩ : syracuseStep 21044305 = 15783229) B15783229
theorem B13140191 : Blo 1619008 13140191 := bstep (se 1 (by rfl) ⟨9855143, by rfl⟩ : syracuseStep 13140191 = 19710287) B19710287
theorem B15565871 : Blo 1619008 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B3646619 : Blo 1619008 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B6915739 : Blo 1619008 6915739 := bstep (se 1 (by rfl) ⟨5186804, by rfl⟩ : syracuseStep 6915739 = 10373609) B10373609
theorem B8203517 : Blo 1619008 8203517 := bstep (se 3 (by rfl) ⟨1538159, by rfl⟩ : syracuseStep 8203517 = 3076319) B3076319
theorem B142094735 : Blo 1619008 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B5837953 : Blo 1619008 5837953 := bstep (se 2 (by rfl) ⟨2189232, by rfl⟩ : syracuseStep 5837953 = 4378465) B4378465
theorem B2430089 : Blo 1619008 2430089 := bstep (se 2 (by rfl) ⟨911283, by rfl⟩ : syracuseStep 2430089 = 1822567) B1822567
theorem B8205623 : Blo 1619008 8205623 := bstep (se 1 (by rfl) ⟨6154217, by rfl⟩ : syracuseStep 8205623 = 12308435) B12308435
theorem B1619503 : Blo 1619008 1619503 := bstep (se 1 (by rfl) ⟨1214627, by rfl⟩ : syracuseStep 1619503 = 2429255) B2429255
theorem B112236293 : Blo 1619008 112236293 := bstep (se 4 (by rfl) ⟨10522152, by rfl⟩ : syracuseStep 112236293 = 21044305) B21044305
theorem B3643145 : Blo 1619008 3643145 := bstep (se 2 (by rfl) ⟨1366179, by rfl⟩ : syracuseStep 3643145 = 2732359) B2732359
theorem B6920147 : Blo 1619008 6920147 := bstep (se 1 (by rfl) ⟨5190110, by rfl⟩ : syracuseStep 6920147 = 10380221) B10380221
theorem B56850655 : Blo 1619008 56850655 := bstep (se 1 (by rfl) ⟨42637991, by rfl⟩ : syracuseStep 56850655 = 85275983) B85275983
theorem B29546747 : Blo 1619008 29546747 := bstep (se 1 (by rfl) ⟨22160060, by rfl⟩ : syracuseStep 29546747 = 44320121) B44320121
theorem B75800873 : Blo 1619008 75800873 := bstep (se 2 (by rfl) ⟨28425327, by rfl⟩ : syracuseStep 75800873 = 56850655) B56850655
theorem B4613431 : Blo 1619008 4613431 := bstep (se 1 (by rfl) ⟨3460073, by rfl⟩ : syracuseStep 4613431 = 6920147) B6920147
theorem B7783937 : Blo 1619008 7783937 := bstep (se 2 (by rfl) ⟨2918976, by rfl⟩ : syracuseStep 7783937 = 5837953) B5837953
theorem B299296781 : Blo 1619008 299296781 := bstep (se 3 (by rfl) ⟨56118146, by rfl⟩ : syracuseStep 299296781 = 112236293) B112236293
theorem B35040509 : Blo 1619008 35040509 := bstep (se 3 (by rfl) ⟨6570095, by rfl⟩ : syracuseStep 35040509 = 13140191) B13140191
theorem B2428763 : Blo 1619008 2428763 := bstep (se 1 (by rfl) ⟨1821572, by rfl⟩ : syracuseStep 2428763 = 3643145) B3643145
theorem B19697831 : Blo 1619008 19697831 := bstep (se 1 (by rfl) ⟨14773373, by rfl⟩ : syracuseStep 19697831 = 29546747) B29546747
theorem B5469011 : Blo 1619008 5469011 := bstep (se 1 (by rfl) ⟨4101758, by rfl⟩ : syracuseStep 5469011 = 8203517) B8203517
theorem B9220985 : Blo 1619008 9220985 := bstep (se 2 (by rfl) ⟨3457869, by rfl⟩ : syracuseStep 9220985 = 6915739) B6915739
theorem B94729823 : Blo 1619008 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B10377247 : Blo 1619008 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B1620059 : Blo 1619008 1620059 := bstep (se 1 (by rfl) ⟨1215044, by rfl⟩ : syracuseStep 1620059 = 2430089) B2430089
theorem B2431079 : Blo 1619008 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B5470415 : Blo 1619008 5470415 := bstep (se 1 (by rfl) ⟨4102811, by rfl⟩ : syracuseStep 5470415 = 8205623) B8205623
theorem B13836329 : Blo 1619008 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B13131887 : Blo 1619008 13131887 := bstep (se 1 (by rfl) ⟨9848915, by rfl⟩ : syracuseStep 13131887 = 19697831) B19697831
theorem B3646007 : Blo 1619008 3646007 := bstep (se 1 (by rfl) ⟨2734505, by rfl⟩ : syracuseStep 3646007 = 5469011) B5469011
theorem B63153215 : Blo 1619008 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B3646943 : Blo 1619008 3646943 := bstep (se 1 (by rfl) ⟨2735207, by rfl⟩ : syracuseStep 3646943 = 5470415) B5470415
theorem B6147323 : Blo 1619008 6147323 := bstep (se 1 (by rfl) ⟨4610492, by rfl⟩ : syracuseStep 6147323 = 9220985) B9220985
theorem B5189291 : Blo 1619008 5189291 := bstep (se 1 (by rfl) ⟨3891968, by rfl⟩ : syracuseStep 5189291 = 7783937) B7783937
theorem B23360339 : Blo 1619008 23360339 := bstep (se 1 (by rfl) ⟨17520254, by rfl⟩ : syracuseStep 23360339 = 35040509) B35040509
theorem B1619175 : Blo 1619008 1619175 := bstep (se 1 (by rfl) ⟨1214381, by rfl⟩ : syracuseStep 1619175 = 2428763) B2428763
theorem B50533915 : Blo 1619008 50533915 := bstep (se 1 (by rfl) ⟨37900436, by rfl⟩ : syracuseStep 50533915 = 75800873) B75800873
theorem B199531187 : Blo 1619008 199531187 := bstep (se 1 (by rfl) ⟨149648390, by rfl⟩ : syracuseStep 199531187 = 299296781) B299296781
theorem B1620719 : Blo 1619008 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B6151241 : Blo 1619008 6151241 := bstep (se 2 (by rfl) ⟨2306715, by rfl⟩ : syracuseStep 6151241 = 4613431) B4613431
theorem B9224219 : Blo 1619008 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B15573559 : Blo 1619008 15573559 := bstep (se 1 (by rfl) ⟨11680169, by rfl⟩ : syracuseStep 15573559 = 23360339) B23360339
theorem B4098215 : Blo 1619008 4098215 := bstep (se 1 (by rfl) ⟨3073661, by rfl⟩ : syracuseStep 4098215 = 6147323) B6147323
theorem B3459527 : Blo 1619008 3459527 := bstep (se 1 (by rfl) ⟨2594645, by rfl⟩ : syracuseStep 3459527 = 5189291) B5189291
theorem B42102143 : Blo 1619008 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B4100827 : Blo 1619008 4100827 := bstep (se 1 (by rfl) ⟨3075620, by rfl⟩ : syracuseStep 4100827 = 6151241) B6151241
theorem B35018365 : Blo 1619008 35018365 := bstep (se 3 (by rfl) ⟨6565943, by rfl⟩ : syracuseStep 35018365 = 13131887) B13131887
theorem B2430671 : Blo 1619008 2430671 := bstep (se 1 (by rfl) ⟨1823003, by rfl⟩ : syracuseStep 2430671 = 3646007) B3646007
theorem B2431295 : Blo 1619008 2431295 := bstep (se 1 (by rfl) ⟨1823471, by rfl⟩ : syracuseStep 2431295 = 3646943) B3646943
theorem B133020791 : Blo 1619008 133020791 := bstep (se 1 (by rfl) ⟨99765593, by rfl⟩ : syracuseStep 133020791 = 199531187) B199531187
theorem B67378553 : Blo 1619008 67378553 := bstep (se 2 (by rfl) ⟨25266957, by rfl⟩ : syracuseStep 67378553 = 50533915) B50533915
theorem B88680527 : Blo 1619008 88680527 := bstep (se 1 (by rfl) ⟨66510395, by rfl⟩ : syracuseStep 88680527 = 133020791) B133020791
theorem B44919035 : Blo 1619008 44919035 := bstep (se 1 (by rfl) ⟨33689276, by rfl⟩ : syracuseStep 44919035 = 67378553) B67378553
theorem B28068095 : Blo 1619008 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B5467769 : Blo 1619008 5467769 := bstep (se 2 (by rfl) ⟨2050413, by rfl⟩ : syracuseStep 5467769 = 4100827) B4100827
theorem B2732143 : Blo 1619008 2732143 := bstep (se 1 (by rfl) ⟨2049107, by rfl⟩ : syracuseStep 2732143 = 4098215) B4098215
theorem B2306351 : Blo 1619008 2306351 := bstep (se 1 (by rfl) ⟨1729763, by rfl⟩ : syracuseStep 2306351 = 3459527) B3459527
theorem B46691153 : Blo 1619008 46691153 := bstep (se 2 (by rfl) ⟨17509182, by rfl⟩ : syracuseStep 46691153 = 35018365) B35018365
theorem B6149479 : Blo 1619008 6149479 := bstep (se 1 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 6149479 = 9224219) B9224219
theorem B20764745 : Blo 1619008 20764745 := bstep (se 2 (by rfl) ⟨7786779, by rfl⟩ : syracuseStep 20764745 = 15573559) B15573559
theorem B1620447 : Blo 1619008 1620447 := bstep (se 1 (by rfl) ⟨1215335, by rfl⟩ : syracuseStep 1620447 = 2430671) B2430671
theorem B1620863 : Blo 1619008 1620863 := bstep (se 1 (by rfl) ⟨1215647, by rfl⟩ : syracuseStep 1620863 = 2431295) B2431295
theorem B18712063 : Blo 1619008 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B29946023 : Blo 1619008 29946023 := bstep (se 1 (by rfl) ⟨22459517, by rfl⟩ : syracuseStep 29946023 = 44919035) B44919035
theorem B3642857 : Blo 1619008 3642857 := bstep (se 2 (by rfl) ⟨1366071, by rfl⟩ : syracuseStep 3642857 = 2732143) B2732143
theorem B31127435 : Blo 1619008 31127435 := bstep (se 1 (by rfl) ⟨23345576, by rfl⟩ : syracuseStep 31127435 = 46691153) B46691153
theorem B6150269 : Blo 1619008 6150269 := bstep (se 3 (by rfl) ⟨1153175, by rfl⟩ : syracuseStep 6150269 = 2306351) B2306351
theorem B13843163 : Blo 1619008 13843163 := bstep (se 1 (by rfl) ⟨10382372, by rfl⟩ : syracuseStep 13843163 = 20764745) B20764745
theorem B59120351 : Blo 1619008 59120351 := bstep (se 1 (by rfl) ⟨44340263, by rfl⟩ : syracuseStep 59120351 = 88680527) B88680527
theorem B8199305 : Blo 1619008 8199305 := bstep (se 2 (by rfl) ⟨3074739, by rfl⟩ : syracuseStep 8199305 = 6149479) B6149479
theorem B3645179 : Blo 1619008 3645179 := bstep (se 1 (by rfl) ⟨2733884, by rfl⟩ : syracuseStep 3645179 = 5467769) B5467769
theorem B19964015 : Blo 1619008 19964015 := bstep (se 1 (by rfl) ⟨14973011, by rfl⟩ : syracuseStep 19964015 = 29946023) B29946023
theorem B20751623 : Blo 1619008 20751623 := bstep (se 1 (by rfl) ⟨15563717, by rfl⟩ : syracuseStep 20751623 = 31127435) B31127435
theorem B39413567 : Blo 1619008 39413567 := bstep (se 1 (by rfl) ⟨29560175, by rfl⟩ : syracuseStep 39413567 = 59120351) B59120351
theorem B5466203 : Blo 1619008 5466203 := bstep (se 1 (by rfl) ⟨4099652, by rfl⟩ : syracuseStep 5466203 = 8199305) B8199305
theorem B2428571 : Blo 1619008 2428571 := bstep (se 1 (by rfl) ⟨1821428, by rfl⟩ : syracuseStep 2428571 = 3642857) B3642857
theorem B4100179 : Blo 1619008 4100179 := bstep (se 1 (by rfl) ⟨3075134, by rfl⟩ : syracuseStep 4100179 = 6150269) B6150269
theorem B9228775 : Blo 1619008 9228775 := bstep (se 1 (by rfl) ⟨6921581, by rfl⟩ : syracuseStep 9228775 = 13843163) B13843163
theorem B24949417 : Blo 1619008 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B2430119 : Blo 1619008 2430119 := bstep (se 1 (by rfl) ⟨1822589, by rfl⟩ : syracuseStep 2430119 = 3645179) B3645179
theorem B12305033 : Blo 1619008 12305033 := bstep (se 2 (by rfl) ⟨4614387, by rfl⟩ : syracuseStep 12305033 = 9228775) B9228775
theorem B5466905 : Blo 1619008 5466905 := bstep (se 2 (by rfl) ⟨2050089, by rfl⟩ : syracuseStep 5466905 = 4100179) B4100179
theorem B1619047 : Blo 1619008 1619047 := bstep (se 1 (by rfl) ⟨1214285, by rfl⟩ : syracuseStep 1619047 = 2428571) B2428571
theorem B13309343 : Blo 1619008 13309343 := bstep (se 1 (by rfl) ⟨9982007, by rfl⟩ : syracuseStep 13309343 = 19964015) B19964015
theorem B1620079 : Blo 1619008 1620079 := bstep (se 1 (by rfl) ⟨1215059, by rfl⟩ : syracuseStep 1620079 = 2430119) B2430119
theorem B13834415 : Blo 1619008 13834415 := bstep (se 1 (by rfl) ⟨10375811, by rfl⟩ : syracuseStep 13834415 = 20751623) B20751623
theorem B33265889 : Blo 1619008 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B3644135 : Blo 1619008 3644135 := bstep (se 1 (by rfl) ⟨2733101, by rfl⟩ : syracuseStep 3644135 = 5466203) B5466203
theorem B105102845 : Blo 1619008 105102845 := bstep (se 3 (by rfl) ⟨19706783, by rfl⟩ : syracuseStep 105102845 = 39413567) B39413567
theorem B8872895 : Blo 1619008 8872895 := bstep (se 1 (by rfl) ⟨6654671, by rfl⟩ : syracuseStep 8872895 = 13309343) B13309343
theorem B22177259 : Blo 1619008 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B70068563 : Blo 1619008 70068563 := bstep (se 1 (by rfl) ⟨52551422, by rfl⟩ : syracuseStep 70068563 = 105102845) B105102845
theorem B8203355 : Blo 1619008 8203355 := bstep (se 1 (by rfl) ⟨6152516, by rfl⟩ : syracuseStep 8203355 = 12305033) B12305033
theorem B2429423 : Blo 1619008 2429423 := bstep (se 1 (by rfl) ⟨1822067, by rfl⟩ : syracuseStep 2429423 = 3644135) B3644135
theorem B9222943 : Blo 1619008 9222943 := bstep (se 1 (by rfl) ⟨6917207, by rfl⟩ : syracuseStep 9222943 = 13834415) B13834415
theorem B3644603 : Blo 1619008 3644603 := bstep (se 1 (by rfl) ⟨2733452, by rfl⟩ : syracuseStep 3644603 = 5466905) B5466905
theorem B5915263 : Blo 1619008 5915263 := bstep (se 1 (by rfl) ⟨4436447, by rfl⟩ : syracuseStep 5915263 = 8872895) B8872895
theorem B12297257 : Blo 1619008 12297257 := bstep (se 2 (by rfl) ⟨4611471, by rfl⟩ : syracuseStep 12297257 = 9222943) B9222943
theorem B46712375 : Blo 1619008 46712375 := bstep (se 1 (by rfl) ⟨35034281, by rfl⟩ : syracuseStep 46712375 = 70068563) B70068563
theorem B5468903 : Blo 1619008 5468903 := bstep (se 1 (by rfl) ⟨4101677, by rfl⟩ : syracuseStep 5468903 = 8203355) B8203355
theorem B2429735 : Blo 1619008 2429735 := bstep (se 1 (by rfl) ⟨1822301, by rfl⟩ : syracuseStep 2429735 = 3644603) B3644603
theorem B1619615 : Blo 1619008 1619615 := bstep (se 1 (by rfl) ⟨1214711, by rfl⟩ : syracuseStep 1619615 = 2429423) B2429423
theorem B14784839 : Blo 1619008 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B3645935 : Blo 1619008 3645935 := bstep (se 1 (by rfl) ⟨2734451, by rfl⟩ : syracuseStep 3645935 = 5468903) B5468903
theorem B9856559 : Blo 1619008 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B31141583 : Blo 1619008 31141583 := bstep (se 1 (by rfl) ⟨23356187, by rfl⟩ : syracuseStep 31141583 = 46712375) B46712375
theorem B1619823 : Blo 1619008 1619823 := bstep (se 1 (by rfl) ⟨1214867, by rfl⟩ : syracuseStep 1619823 = 2429735) B2429735
theorem B8198171 : Blo 1619008 8198171 := bstep (se 1 (by rfl) ⟨6148628, by rfl⟩ : syracuseStep 8198171 = 12297257) B12297257
theorem B7887017 : Blo 1619008 7887017 := bstep (se 2 (by rfl) ⟨2957631, by rfl⟩ : syracuseStep 7887017 = 5915263) B5915263
theorem B6571039 : Blo 1619008 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B5465447 : Blo 1619008 5465447 := bstep (se 1 (by rfl) ⟨4099085, by rfl⟩ : syracuseStep 5465447 = 8198171) B8198171
theorem B20761055 : Blo 1619008 20761055 := bstep (se 1 (by rfl) ⟨15570791, by rfl⟩ : syracuseStep 20761055 = 31141583) B31141583
theorem B21032045 : Blo 1619008 21032045 := bstep (se 3 (by rfl) ⟨3943508, by rfl⟩ : syracuseStep 21032045 = 7887017) B7887017
theorem B2430623 : Blo 1619008 2430623 := bstep (se 1 (by rfl) ⟨1822967, by rfl⟩ : syracuseStep 2430623 = 3645935) B3645935
theorem B8761385 : Blo 1619008 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B13840703 : Blo 1619008 13840703 := bstep (se 1 (by rfl) ⟨10380527, by rfl⟩ : syracuseStep 13840703 = 20761055) B20761055
theorem B14021363 : Blo 1619008 14021363 := bstep (se 1 (by rfl) ⟨10516022, by rfl⟩ : syracuseStep 14021363 = 21032045) B21032045
theorem B3643631 : Blo 1619008 3643631 := bstep (se 1 (by rfl) ⟨2732723, by rfl⟩ : syracuseStep 3643631 = 5465447) B5465447
theorem B1620415 : Blo 1619008 1620415 := bstep (se 1 (by rfl) ⟨1215311, by rfl⟩ : syracuseStep 1620415 = 2430623) B2430623
theorem B5840923 : Blo 1619008 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B37390301 : Blo 1619008 37390301 := bstep (se 3 (by rfl) ⟨7010681, by rfl⟩ : syracuseStep 37390301 = 14021363) B14021363
theorem B9227135 : Blo 1619008 9227135 := bstep (se 1 (by rfl) ⟨6920351, by rfl⟩ : syracuseStep 9227135 = 13840703) B13840703
theorem B2429087 : Blo 1619008 2429087 := bstep (se 1 (by rfl) ⟨1821815, by rfl⟩ : syracuseStep 2429087 = 3643631) B3643631
theorem B7787897 : Blo 1619008 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B1619391 : Blo 1619008 1619391 := bstep (se 1 (by rfl) ⟨1214543, by rfl⟩ : syracuseStep 1619391 = 2429087) B2429087
theorem B24926867 : Blo 1619008 24926867 := bstep (se 1 (by rfl) ⟨18695150, by rfl⟩ : syracuseStep 24926867 = 37390301) B37390301
theorem B6151423 : Blo 1619008 6151423 := bstep (se 1 (by rfl) ⟨4613567, by rfl⟩ : syracuseStep 6151423 = 9227135) B9227135
theorem B8201897 : Blo 1619008 8201897 := bstep (se 2 (by rfl) ⟨3075711, by rfl⟩ : syracuseStep 8201897 = 6151423) B6151423
theorem B16617911 : Blo 1619008 16617911 := bstep (se 1 (by rfl) ⟨12463433, by rfl⟩ : syracuseStep 16617911 = 24926867) B24926867
theorem B5191931 : Blo 1619008 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B5467931 : Blo 1619008 5467931 := bstep (se 1 (by rfl) ⟨4100948, by rfl⟩ : syracuseStep 5467931 = 8201897) B8201897
theorem B3461287 : Blo 1619008 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B177257717 : Blo 1619008 177257717 := bstep (se 5 (by rfl) ⟨8308955, by rfl⟩ : syracuseStep 177257717 = 16617911) B16617911
theorem B118171811 : Blo 1619008 118171811 := bstep (se 1 (by rfl) ⟨88628858, by rfl⟩ : syracuseStep 118171811 = 177257717) B177257717
theorem B4615049 : Blo 1619008 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B3645287 : Blo 1619008 3645287 := bstep (se 1 (by rfl) ⟨2733965, by rfl⟩ : syracuseStep 3645287 = 5467931) B5467931
theorem B3076699 : Blo 1619008 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B2430191 : Blo 1619008 2430191 := bstep (se 1 (by rfl) ⟨1822643, by rfl⟩ : syracuseStep 2430191 = 3645287) B3645287
theorem B78781207 : Blo 1619008 78781207 := bstep (se 1 (by rfl) ⟨59085905, by rfl⟩ : syracuseStep 78781207 = 118171811) B118171811
theorem B105041609 : Blo 1619008 105041609 := bstep (se 2 (by rfl) ⟨39390603, by rfl⟩ : syracuseStep 105041609 = 78781207) B78781207
theorem B4102265 : Blo 1619008 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B1620127 : Blo 1619008 1620127 := bstep (se 1 (by rfl) ⟨1215095, by rfl⟩ : syracuseStep 1620127 = 2430191) B2430191
theorem B70027739 : Blo 1619008 70027739 := bstep (se 1 (by rfl) ⟨52520804, by rfl⟩ : syracuseStep 70027739 = 105041609) B105041609
theorem B2734843 : Blo 1619008 2734843 := bstep (se 1 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 2734843 = 4102265) B4102265
theorem B3646457 : Blo 1619008 3646457 := bstep (se 2 (by rfl) ⟨1367421, by rfl⟩ : syracuseStep 3646457 = 2734843) B2734843
theorem B46685159 : Blo 1619008 46685159 := bstep (se 1 (by rfl) ⟨35013869, by rfl⟩ : syracuseStep 46685159 = 70027739) B70027739
theorem B31123439 : Blo 1619008 31123439 := bstep (se 1 (by rfl) ⟨23342579, by rfl⟩ : syracuseStep 31123439 = 46685159) B46685159
theorem B2430971 : Blo 1619008 2430971 := bstep (se 1 (by rfl) ⟨1823228, by rfl⟩ : syracuseStep 2430971 = 3646457) B3646457
theorem B20748959 : Blo 1619008 20748959 := bstep (se 1 (by rfl) ⟨15561719, by rfl⟩ : syracuseStep 20748959 = 31123439) B31123439
theorem B1620647 : Blo 1619008 1620647 := bstep (se 1 (by rfl) ⟨1215485, by rfl⟩ : syracuseStep 1620647 = 2430971) B2430971
theorem B13832639 : Blo 1619008 13832639 := bstep (se 1 (by rfl) ⟨10374479, by rfl⟩ : syracuseStep 13832639 = 20748959) B20748959
theorem B9221759 : Blo 1619008 9221759 := bstep (se 1 (by rfl) ⟨6916319, by rfl⟩ : syracuseStep 9221759 = 13832639) B13832639
theorem B6147839 : Blo 1619008 6147839 := bstep (se 1 (by rfl) ⟨4610879, by rfl⟩ : syracuseStep 6147839 = 9221759) B9221759
theorem B4098559 : Blo 1619008 4098559 := bstep (se 1 (by rfl) ⟨3073919, by rfl⟩ : syracuseStep 4098559 = 6147839) B6147839
theorem B5464745 : Blo 1619008 5464745 := bstep (se 2 (by rfl) ⟨2049279, by rfl⟩ : syracuseStep 5464745 = 4098559) B4098559
theorem B3643163 : Blo 1619008 3643163 := bstep (se 1 (by rfl) ⟨2732372, by rfl⟩ : syracuseStep 3643163 = 5464745) B5464745
theorem B2428775 : Blo 1619008 2428775 := bstep (se 1 (by rfl) ⟨1821581, by rfl⟩ : syracuseStep 2428775 = 3643163) B3643163
theorem B1619183 : Blo 1619008 1619183 := bstep (se 1 (by rfl) ⟨1214387, by rfl⟩ : syracuseStep 1619183 = 2428775) B2428775

theorem C0 (j : ℕ) (h1 : 404752 ≤ j) (h2 : j ≤ 405251) : Blo 1619008 (4 * j + 3) := by
  interval_cases j
  · exact B1619011
  · exact B1619015
  · exact B1619019
  · exact B1619023
  · exact B1619027
  · exact B1619031
  · exact B1619035
  · exact B1619039
  · exact B1619043
  · exact B1619047
  · exact B1619051
  · exact B1619055
  · exact B1619059
  · exact B1619063
  · exact B1619067
  · exact B1619071
  · exact B1619075
  · exact B1619079
  · exact B1619083
  · exact B1619087
  · exact B1619091
  · exact B1619095
  · exact B1619099
  · exact B1619103
  · exact B1619107
  · exact B1619111
  · exact B1619115
  · exact B1619119
  · exact B1619123
  · exact B1619127
  · exact B1619131
  · exact B1619135
  · exact B1619139
  · exact B1619143
  · exact B1619147
  · exact B1619151
  · exact B1619155
  · exact B1619159
  · exact B1619163
  · exact B1619167
  · exact B1619171
  · exact B1619175
  · exact B1619179
  · exact B1619183
  · exact B1619187
  · exact B1619191
  · exact B1619195
  · exact B1619199
  · exact B1619203
  · exact B1619207
  · exact B1619211
  · exact B1619215
  · exact B1619219
  · exact B1619223
  · exact B1619227
  · exact B1619231
  · exact B1619235
  · exact B1619239
  · exact B1619243
  · exact B1619247
  · exact B1619251
  · exact B1619255
  · exact B1619259
  · exact B1619263
  · exact B1619267
  · exact B1619271
  · exact B1619275
  · exact B1619279
  · exact B1619283
  · exact B1619287
  · exact B1619291
  · exact B1619295
  · exact B1619299
  · exact B1619303
  · exact B1619307
  · exact B1619311
  · exact B1619315
  · exact B1619319
  · exact B1619323
  · exact B1619327
  · exact B1619331
  · exact B1619335
  · exact B1619339
  · exact B1619343
  · exact B1619347
  · exact B1619351
  · exact B1619355
  · exact B1619359
  · exact B1619363
  · exact B1619367
  · exact B1619371
  · exact B1619375
  · exact B1619379
  · exact B1619383
  · exact B1619387
  · exact B1619391
  · exact B1619395
  · exact B1619399
  · exact B1619403
  · exact B1619407
  · exact B1619411
  · exact B1619415
  · exact B1619419
  · exact B1619423
  · exact B1619427
  · exact B1619431
  · exact B1619435
  · exact B1619439
  · exact B1619443
  · exact B1619447
  · exact B1619451
  · exact B1619455
  · exact B1619459
  · exact B1619463
  · exact B1619467
  · exact B1619471
  · exact B1619475
  · exact B1619479
  · exact B1619483
  · exact B1619487
  · exact B1619491
  · exact B1619495
  · exact B1619499
  · exact B1619503
  · exact B1619507
  · exact B1619511
  · exact B1619515
  · exact B1619519
  · exact B1619523
  · exact B1619527
  · exact B1619531
  · exact B1619535
  · exact B1619539
  · exact B1619543
  · exact B1619547
  · exact B1619551
  · exact B1619555
  · exact B1619559
  · exact B1619563
  · exact B1619567
  · exact B1619571
  · exact B1619575
  · exact B1619579
  · exact B1619583
  · exact B1619587
  · exact B1619591
  · exact B1619595
  · exact B1619599
  · exact B1619603
  · exact B1619607
  · exact B1619611
  · exact B1619615
  · exact B1619619
  · exact B1619623
  · exact B1619627
  · exact B1619631
  · exact B1619635
  · exact B1619639
  · exact B1619643
  · exact B1619647
  · exact B1619651
  · exact B1619655
  · exact B1619659
  · exact B1619663
  · exact B1619667
  · exact B1619671
  · exact B1619675
  · exact B1619679
  · exact B1619683
  · exact B1619687
  · exact B1619691
  · exact B1619695
  · exact B1619699
  · exact B1619703
  · exact B1619707
  · exact B1619711
  · exact B1619715
  · exact B1619719
  · exact B1619723
  · exact B1619727
  · exact B1619731
  · exact B1619735
  · exact B1619739
  · exact B1619743
  · exact B1619747
  · exact B1619751
  · exact B1619755
  · exact B1619759
  · exact B1619763
  · exact B1619767
  · exact B1619771
  · exact B1619775
  · exact B1619779
  · exact B1619783
  · exact B1619787
  · exact B1619791
  · exact B1619795
  · exact B1619799
  · exact B1619803
  · exact B1619807
  · exact B1619811
  · exact B1619815
  · exact B1619819
  · exact B1619823
  · exact B1619827
  · exact B1619831
  · exact B1619835
  · exact B1619839
  · exact B1619843
  · exact B1619847
  · exact B1619851
  · exact B1619855
  · exact B1619859
  · exact B1619863
  · exact B1619867
  · exact B1619871
  · exact B1619875
  · exact B1619879
  · exact B1619883
  · exact B1619887
  · exact B1619891
  · exact B1619895
  · exact B1619899
  · exact B1619903
  · exact B1619907
  · exact B1619911
  · exact B1619915
  · exact B1619919
  · exact B1619923
  · exact B1619927
  · exact B1619931
  · exact B1619935
  · exact B1619939
  · exact B1619943
  · exact B1619947
  · exact B1619951
  · exact B1619955
  · exact B1619959
  · exact B1619963
  · exact B1619967
  · exact B1619971
  · exact B1619975
  · exact B1619979
  · exact B1619983
  · exact B1619987
  · exact B1619991
  · exact B1619995
  · exact B1619999
  · exact B1620003
  · exact B1620007
  · exact B1620011
  · exact B1620015
  · exact B1620019
  · exact B1620023
  · exact B1620027
  · exact B1620031
  · exact B1620035
  · exact B1620039
  · exact B1620043
  · exact B1620047
  · exact B1620051
  · exact B1620055
  · exact B1620059
  · exact B1620063
  · exact B1620067
  · exact B1620071
  · exact B1620075
  · exact B1620079
  · exact B1620083
  · exact B1620087
  · exact B1620091
  · exact B1620095
  · exact B1620099
  · exact B1620103
  · exact B1620107
  · exact B1620111
  · exact B1620115
  · exact B1620119
  · exact B1620123
  · exact B1620127
  · exact B1620131
  · exact B1620135
  · exact B1620139
  · exact B1620143
  · exact B1620147
  · exact B1620151
  · exact B1620155
  · exact B1620159
  · exact B1620163
  · exact B1620167
  · exact B1620171
  · exact B1620175
  · exact B1620179
  · exact B1620183
  · exact B1620187
  · exact B1620191
  · exact B1620195
  · exact B1620199
  · exact B1620203
  · exact B1620207
  · exact B1620211
  · exact B1620215
  · exact B1620219
  · exact B1620223
  · exact B1620227
  · exact B1620231
  · exact B1620235
  · exact B1620239
  · exact B1620243
  · exact B1620247
  · exact B1620251
  · exact B1620255
  · exact B1620259
  · exact B1620263
  · exact B1620267
  · exact B1620271
  · exact B1620275
  · exact B1620279
  · exact B1620283
  · exact B1620287
  · exact B1620291
  · exact B1620295
  · exact B1620299
  · exact B1620303
  · exact B1620307
  · exact B1620311
  · exact B1620315
  · exact B1620319
  · exact B1620323
  · exact B1620327
  · exact B1620331
  · exact B1620335
  · exact B1620339
  · exact B1620343
  · exact B1620347
  · exact B1620351
  · exact B1620355
  · exact B1620359
  · exact B1620363
  · exact B1620367
  · exact B1620371
  · exact B1620375
  · exact B1620379
  · exact B1620383
  · exact B1620387
  · exact B1620391
  · exact B1620395
  · exact B1620399
  · exact B1620403
  · exact B1620407
  · exact B1620411
  · exact B1620415
  · exact B1620419
  · exact B1620423
  · exact B1620427
  · exact B1620431
  · exact B1620435
  · exact B1620439
  · exact B1620443
  · exact B1620447
  · exact B1620451
  · exact B1620455
  · exact B1620459
  · exact B1620463
  · exact B1620467
  · exact B1620471
  · exact B1620475
  · exact B1620479
  · exact B1620483
  · exact B1620487
  · exact B1620491
  · exact B1620495
  · exact B1620499
  · exact B1620503
  · exact B1620507
  · exact B1620511
  · exact B1620515
  · exact B1620519
  · exact B1620523
  · exact B1620527
  · exact B1620531
  · exact B1620535
  · exact B1620539
  · exact B1620543
  · exact B1620547
  · exact B1620551
  · exact B1620555
  · exact B1620559
  · exact B1620563
  · exact B1620567
  · exact B1620571
  · exact B1620575
  · exact B1620579
  · exact B1620583
  · exact B1620587
  · exact B1620591
  · exact B1620595
  · exact B1620599
  · exact B1620603
  · exact B1620607
  · exact B1620611
  · exact B1620615
  · exact B1620619
  · exact B1620623
  · exact B1620627
  · exact B1620631
  · exact B1620635
  · exact B1620639
  · exact B1620643
  · exact B1620647
  · exact B1620651
  · exact B1620655
  · exact B1620659
  · exact B1620663
  · exact B1620667
  · exact B1620671
  · exact B1620675
  · exact B1620679
  · exact B1620683
  · exact B1620687
  · exact B1620691
  · exact B1620695
  · exact B1620699
  · exact B1620703
  · exact B1620707
  · exact B1620711
  · exact B1620715
  · exact B1620719
  · exact B1620723
  · exact B1620727
  · exact B1620731
  · exact B1620735
  · exact B1620739
  · exact B1620743
  · exact B1620747
  · exact B1620751
  · exact B1620755
  · exact B1620759
  · exact B1620763
  · exact B1620767
  · exact B1620771
  · exact B1620775
  · exact B1620779
  · exact B1620783
  · exact B1620787
  · exact B1620791
  · exact B1620795
  · exact B1620799
  · exact B1620803
  · exact B1620807
  · exact B1620811
  · exact B1620815
  · exact B1620819
  · exact B1620823
  · exact B1620827
  · exact B1620831
  · exact B1620835
  · exact B1620839
  · exact B1620843
  · exact B1620847
  · exact B1620851
  · exact B1620855
  · exact B1620859
  · exact B1620863
  · exact B1620867
  · exact B1620871
  · exact B1620875
  · exact B1620879
  · exact B1620883
  · exact B1620887
  · exact B1620891
  · exact B1620895
  · exact B1620899
  · exact B1620903
  · exact B1620907
  · exact B1620911
  · exact B1620915
  · exact B1620919
  · exact B1620923
  · exact B1620927
  · exact B1620931
  · exact B1620935
  · exact B1620939
  · exact B1620943
  · exact B1620947
  · exact B1620951
  · exact B1620955
  · exact B1620959
  · exact B1620963
  · exact B1620967
  · exact B1620971
  · exact B1620975
  · exact B1620979
  · exact B1620983
  · exact B1620987
  · exact B1620991
  · exact B1620995
  · exact B1620999
  · exact B1621003
  · exact B1621007

theorem solution (m : ℕ) (hlo : 1619008 ≤ m) (hhi : m ≤ 1621008) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 404752 ≤ j := by omega
    have hj2 : j ≤ 405251 := by omega
    have hb : Blo 1619008 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
