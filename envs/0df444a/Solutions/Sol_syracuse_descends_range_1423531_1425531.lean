-- Prove2me | solution 1 for syracuse_descends_range_1423531_1425531
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:13:59.597134+00:00
-- url     : https://prove2.me/submissions/dc9d5e9b-ed5f-4890-91a0-c0f85521dbcf

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


theorem B1802245 : Blo 1423531 1802245 := bbase (se 4 (by rfl) ⟨168960, by rfl⟩ : syracuseStep 1802245 = 337921) (by norm_num)
theorem B2138117 : Blo 1423531 2138117 := bbase (se 4 (by rfl) ⟨200448, by rfl⟩ : syracuseStep 2138117 = 400897) (by norm_num)
theorem B2138141 : Blo 1423531 2138141 := bbase (se 3 (by rfl) ⟨400901, by rfl⟩ : syracuseStep 2138141 = 801803) (by norm_num)
theorem B3203117 : Blo 1423531 3203117 := bbase (se 3 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 3203117 = 1201169) (by norm_num)
theorem B9125941 : Blo 1423531 9125941 := bbase (se 5 (by rfl) ⟨427778, by rfl⟩ : syracuseStep 9125941 = 855557) (by norm_num)
theorem B2138165 : Blo 1423531 2138165 := bbase (se 5 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 2138165 = 200453) (by norm_num)
theorem B4874309 : Blo 1423531 4874309 := bbase (se 4 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 4874309 = 913933) (by norm_num)
theorem B2138189 : Blo 1423531 2138189 := bbase (se 3 (by rfl) ⟨400910, by rfl⟩ : syracuseStep 2138189 = 801821) (by norm_num)
theorem B1712225 : Blo 1423531 1712225 := bbase (se 2 (by rfl) ⟨642084, by rfl⟩ : syracuseStep 1712225 = 1284169) (by norm_num)
theorem B1802341 : Blo 1423531 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B2138213 : Blo 1423531 2138213 := bbase (se 4 (by rfl) ⟨200457, by rfl⟩ : syracuseStep 2138213 = 400915) (by norm_num)
theorem B9740405 : Blo 1423531 9740405 := bbase (se 5 (by rfl) ⟨456581, by rfl⟩ : syracuseStep 9740405 = 913163) (by norm_num)
theorem B3203189 : Blo 1423531 3203189 := bbase (se 5 (by rfl) ⟨150149, by rfl⟩ : syracuseStep 3203189 = 300299) (by norm_num)
theorem B2138237 : Blo 1423531 2138237 := bbase (se 3 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 2138237 = 801839) (by norm_num)
theorem B3604621 : Blo 1423531 3604621 := bbase (se 3 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 3604621 = 1351733) (by norm_num)
theorem B2138261 : Blo 1423531 2138261 := bbase (se 6 (by rfl) ⟨50115, by rfl⟩ : syracuseStep 2138261 = 100231) (by norm_num)
theorem B2138285 : Blo 1423531 2138285 := bbase (se 3 (by rfl) ⟨400928, by rfl⟩ : syracuseStep 2138285 = 801857) (by norm_num)
theorem B4563125 : Blo 1423531 4563125 := bbase (se 5 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 4563125 = 427793) (by norm_num)
theorem B3203261 : Blo 1423531 3203261 := bbase (se 3 (by rfl) ⟨600611, by rfl⟩ : syracuseStep 3203261 = 1201223) (by norm_num)
theorem B2703557 : Blo 1423531 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B3604733 : Blo 1423531 3604733 := bbase (se 3 (by rfl) ⟨675887, by rfl⟩ : syracuseStep 3604733 = 1351775) (by norm_num)
theorem B3203333 : Blo 1423531 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B1802513 : Blo 1423531 1802513 := bbase (se 2 (by rfl) ⟨675942, by rfl⟩ : syracuseStep 1802513 = 1351885) (by norm_num)
theorem B1802569 : Blo 1423531 1802569 := bbase (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) (by norm_num)
theorem B3203405 : Blo 1423531 3203405 := bbase (se 3 (by rfl) ⟨600638, by rfl⟩ : syracuseStep 3203405 = 1201277) (by norm_num)
theorem B12165461 : Blo 1423531 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B2703709 : Blo 1423531 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B4809077 : Blo 1423531 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B3203477 : Blo 1423531 3203477 := bbase (se 6 (by rfl) ⟨75081, by rfl⟩ : syracuseStep 3203477 = 150163) (by norm_num)
theorem B1802665 : Blo 1423531 1802665 := bbase (se 2 (by rfl) ⟨675999, by rfl⟩ : syracuseStep 1802665 = 1351999) (by norm_num)
theorem B2638253 : Blo 1423531 2638253 := bbase (se 3 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 2638253 = 989345) (by norm_num)
theorem B3604925 : Blo 1423531 3604925 := bbase (se 3 (by rfl) ⟨675923, by rfl⟩ : syracuseStep 3604925 = 1351847) (by norm_num)
theorem B3203549 : Blo 1423531 3203549 := bbase (se 3 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 3203549 = 1201331) (by norm_num)
theorem B1851869 : Blo 1423531 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B14623253 : Blo 1423531 14623253 := bbase (se 6 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 14623253 = 685465) (by norm_num)
theorem B3654173 : Blo 1423531 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B3203621 : Blo 1423531 3203621 := bbase (se 4 (by rfl) ⟨300339, by rfl⟩ : syracuseStep 3203621 = 600679) (by norm_num)
theorem B3424805 : Blo 1423531 3424805 := bbase (se 4 (by rfl) ⟨321075, by rfl⟩ : syracuseStep 3424805 = 642151) (by norm_num)
theorem B1802837 : Blo 1423531 1802837 := bbase (se 8 (by rfl) ⟨10563, by rfl⟩ : syracuseStep 1802837 = 21127) (by norm_num)
theorem B3203693 : Blo 1423531 3203693 := bbase (se 3 (by rfl) ⟨600692, by rfl⟩ : syracuseStep 3203693 = 1201385) (by norm_num)
theorem B2777725 : Blo 1423531 2777725 := bbase (se 3 (by rfl) ⟨520823, by rfl⟩ : syracuseStep 2777725 = 1041647) (by norm_num)
theorem B2704013 : Blo 1423531 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B1802893 : Blo 1423531 1802893 := bbase (se 3 (by rfl) ⟨338042, by rfl⟩ : syracuseStep 1802893 = 676085) (by norm_num)
theorem B3203765 : Blo 1423531 3203765 := bbase (se 5 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 3203765 = 300353) (by norm_num)
theorem B3850949 : Blo 1423531 3850949 := bbase (se 4 (by rfl) ⟨361026, by rfl⟩ : syracuseStep 3850949 = 722053) (by norm_num)
theorem B3424997 : Blo 1423531 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B1802989 : Blo 1423531 1802989 := bbase (se 3 (by rfl) ⟨338060, by rfl⟩ : syracuseStep 1802989 = 676121) (by norm_num)
theorem B6087413 : Blo 1423531 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B3203837 : Blo 1423531 3203837 := bbase (se 3 (by rfl) ⟨600719, by rfl⟩ : syracuseStep 3203837 = 1201439) (by norm_num)
theorem B3605269 : Blo 1423531 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B4809509 : Blo 1423531 4809509 := bbase (se 4 (by rfl) ⟨450891, by rfl⟩ : syracuseStep 4809509 = 901783) (by norm_num)
theorem B3203909 : Blo 1423531 3203909 := bbase (se 4 (by rfl) ⟨300366, by rfl⟩ : syracuseStep 3203909 = 600733) (by norm_num)
theorem B3425093 : Blo 1423531 3425093 := bbase (se 4 (by rfl) ⟨321102, by rfl⟩ : syracuseStep 3425093 = 642205) (by norm_num)
theorem B5137253 : Blo 1423531 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B3605381 : Blo 1423531 3605381 := bbase (se 4 (by rfl) ⟨338004, by rfl⟩ : syracuseStep 3605381 = 676009) (by norm_num)
theorem B3203981 : Blo 1423531 3203981 := bbase (se 3 (by rfl) ⟨600746, by rfl⟩ : syracuseStep 3203981 = 1201493) (by norm_num)
theorem B1803161 : Blo 1423531 1803161 := bbase (se 2 (by rfl) ⟨676185, by rfl⟩ : syracuseStep 1803161 = 1352371) (by norm_num)
theorem B1803217 : Blo 1423531 1803217 := bbase (se 2 (by rfl) ⟨676206, by rfl⟩ : syracuseStep 1803217 = 1352413) (by norm_num)
theorem B3204053 : Blo 1423531 3204053 := bbase (se 7 (by rfl) ⟨37547, by rfl⟩ : syracuseStep 3204053 = 75095) (by norm_num)
theorem B3204125 : Blo 1423531 3204125 := bbase (se 3 (by rfl) ⟨600773, by rfl⟩ : syracuseStep 3204125 = 1201547) (by norm_num)
theorem B6841381 : Blo 1423531 6841381 := bbase (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) (by norm_num)
theorem B1803313 : Blo 1423531 1803313 := bbase (se 2 (by rfl) ⟨676242, by rfl⟩ : syracuseStep 1803313 = 1352485) (by norm_num)
theorem B3605573 : Blo 1423531 3605573 := bbase (se 4 (by rfl) ⟨338022, by rfl⟩ : syracuseStep 3605573 = 676045) (by norm_num)
theorem B5407829 : Blo 1423531 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B17572949 : Blo 1423531 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B3204197 : Blo 1423531 3204197 := bbase (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) (by norm_num)
theorem B7210133 : Blo 1423531 7210133 := bbase (se 6 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 7210133 = 337975) (by norm_num)
theorem B3204269 : Blo 1423531 3204269 := bbase (se 3 (by rfl) ⟨600800, by rfl⟩ : syracuseStep 3204269 = 1201601) (by norm_num)
theorem B2565317 : Blo 1423531 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B4334789 : Blo 1423531 4334789 := bbase (se 4 (by rfl) ⟨406386, by rfl⟩ : syracuseStep 4334789 = 812773) (by norm_num)
theorem B4809941 : Blo 1423531 4809941 := bbase (se 7 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 4809941 = 112733) (by norm_num)
theorem B1803485 : Blo 1423531 1803485 := bbase (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) (by norm_num)
theorem B4056293 : Blo 1423531 4056293 := bbase (se 4 (by rfl) ⟨380277, by rfl⟩ : syracuseStep 4056293 = 760555) (by norm_num)
theorem B3204341 : Blo 1423531 3204341 := bbase (se 5 (by rfl) ⟨150203, by rfl⟩ : syracuseStep 3204341 = 300407) (by norm_num)
theorem B9250037 : Blo 1423531 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B1803541 : Blo 1423531 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B3204413 : Blo 1423531 3204413 := bbase (se 3 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 3204413 = 1201655) (by norm_num)
theorem B1443145 : Blo 1423531 1443145 := bbase (se 2 (by rfl) ⟨541179, by rfl⟩ : syracuseStep 1443145 = 1082359) (by norm_num)
theorem B5408117 : Blo 1423531 5408117 := bbase (se 5 (by rfl) ⟨253505, by rfl⟩ : syracuseStep 5408117 = 507011) (by norm_num)
theorem B1803637 : Blo 1423531 1803637 := bbase (se 5 (by rfl) ⟨84545, by rfl⟩ : syracuseStep 1803637 = 169091) (by norm_num)
theorem B2704765 : Blo 1423531 2704765 := bbase (se 3 (by rfl) ⟨507143, by rfl⟩ : syracuseStep 2704765 = 1014287) (by norm_num)
theorem B3204485 : Blo 1423531 3204485 := bbase (se 4 (by rfl) ⟨300420, by rfl⟩ : syracuseStep 3204485 = 600841) (by norm_num)
theorem B3605917 : Blo 1423531 3605917 := bbase (se 3 (by rfl) ⟨676109, by rfl⟩ : syracuseStep 3605917 = 1352219) (by norm_num)
theorem B3204557 : Blo 1423531 3204557 := bbase (se 3 (by rfl) ⟨600854, by rfl⟩ : syracuseStep 3204557 = 1201709) (by norm_num)
theorem B6497765 : Blo 1423531 6497765 := bbase (se 4 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 6497765 = 1218331) (by norm_num)
theorem B3606029 : Blo 1423531 3606029 := bbase (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) (by norm_num)
theorem B2704909 : Blo 1423531 2704909 := bbase (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) (by norm_num)
theorem B3204629 : Blo 1423531 3204629 := bbase (se 6 (by rfl) ⟨75108, by rfl⟩ : syracuseStep 3204629 = 150217) (by norm_num)
theorem B1803809 : Blo 1423531 1803809 := bbase (se 2 (by rfl) ⟨676428, by rfl⟩ : syracuseStep 1803809 = 1352857) (by norm_num)
theorem B2565685 : Blo 1423531 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B1803865 : Blo 1423531 1803865 := bbase (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) (by norm_num)
theorem B3204701 : Blo 1423531 3204701 := bbase (se 3 (by rfl) ⟨600881, by rfl⟩ : syracuseStep 3204701 = 1201763) (by norm_num)
theorem B6497909 : Blo 1423531 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B4810373 : Blo 1423531 4810373 := bbase (se 4 (by rfl) ⟨450972, by rfl⟩ : syracuseStep 4810373 = 901945) (by norm_num)
theorem B8111765 : Blo 1423531 8111765 := bbase (se 6 (by rfl) ⟨190119, by rfl⟩ : syracuseStep 8111765 = 380239) (by norm_num)
theorem B3204773 : Blo 1423531 3204773 := bbase (se 4 (by rfl) ⟨300447, by rfl⟩ : syracuseStep 3204773 = 600895) (by norm_num)
theorem B2705069 : Blo 1423531 2705069 := bbase (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) (by norm_num)
theorem B1803961 : Blo 1423531 1803961 := bbase (se 2 (by rfl) ⟨676485, by rfl⟩ : syracuseStep 1803961 = 1352971) (by norm_num)
theorem B3040973 : Blo 1423531 3040973 := bbase (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) (by norm_num)
theorem B3606221 : Blo 1423531 3606221 := bbase (se 3 (by rfl) ⟨676166, by rfl⟩ : syracuseStep 3606221 = 1352333) (by norm_num)
theorem B3204845 : Blo 1423531 3204845 := bbase (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) (by norm_num)
theorem B3204917 : Blo 1423531 3204917 := bbase (se 5 (by rfl) ⟨150230, by rfl⟩ : syracuseStep 3204917 = 300461) (by norm_num)
theorem B2705213 : Blo 1423531 2705213 := bbase (se 3 (by rfl) ⟨507227, by rfl⟩ : syracuseStep 2705213 = 1014455) (by norm_num)
theorem B1804133 : Blo 1423531 1804133 := bbase (se 4 (by rfl) ⟨169137, by rfl⟩ : syracuseStep 1804133 = 338275) (by norm_num)
theorem B3204989 : Blo 1423531 3204989 := bbase (se 3 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 3204989 = 1201871) (by norm_num)
theorem B3082117 : Blo 1423531 3082117 := bbase (se 4 (by rfl) ⟨288948, by rfl⟩ : syracuseStep 3082117 = 577897) (by norm_num)
theorem B2312069 : Blo 1423531 2312069 := bbase (se 4 (by rfl) ⟨216756, by rfl⟩ : syracuseStep 2312069 = 433513) (by norm_num)
theorem B1828765 : Blo 1423531 1828765 := bbase (se 3 (by rfl) ⟨342893, by rfl⟩ : syracuseStep 1828765 = 685787) (by norm_num)
theorem B1804189 : Blo 1423531 1804189 := bbase (se 3 (by rfl) ⟨338285, by rfl⟩ : syracuseStep 1804189 = 676571) (by norm_num)
theorem B6588325 : Blo 1423531 6588325 := bbase (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) (by norm_num)
theorem B2402237 : Blo 1423531 2402237 := bbase (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) (by norm_num)
theorem B3041221 : Blo 1423531 3041221 := bbase (se 4 (by rfl) ⟨285114, by rfl⟩ : syracuseStep 3041221 = 570229) (by norm_num)
theorem B3205061 : Blo 1423531 3205061 := bbase (se 4 (by rfl) ⟨300474, by rfl⟩ : syracuseStep 3205061 = 600949) (by norm_num)
theorem B2926573 : Blo 1423531 2926573 := bbase (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) (by norm_num)
theorem B3205133 : Blo 1423531 3205133 := bbase (se 3 (by rfl) ⟨600962, by rfl⟩ : syracuseStep 3205133 = 1201925) (by norm_num)
theorem B3606565 : Blo 1423531 3606565 := bbase (se 4 (by rfl) ⟨338115, by rfl⟩ : syracuseStep 3606565 = 676231) (by norm_num)
theorem B4810805 : Blo 1423531 4810805 := bbase (se 5 (by rfl) ⟨225506, by rfl⟩ : syracuseStep 4810805 = 451013) (by norm_num)
theorem B2402365 : Blo 1423531 2402365 := bbase (se 3 (by rfl) ⟨450443, by rfl⟩ : syracuseStep 2402365 = 900887) (by norm_num)
theorem B5777477 : Blo 1423531 5777477 := bbase (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) (by norm_num)
theorem B3205205 : Blo 1423531 3205205 := bbase (se 8 (by rfl) ⟨18780, by rfl⟩ : syracuseStep 3205205 = 37561) (by norm_num)
theorem B2705501 : Blo 1423531 2705501 := bbase (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) (by norm_num)
theorem B3295349 : Blo 1423531 3295349 := bbase (se 5 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 3295349 = 308939) (by norm_num)
theorem B2402453 : Blo 1423531 2402453 := bbase (se 6 (by rfl) ⟨56307, by rfl⟩ : syracuseStep 2402453 = 112615) (by norm_num)
theorem B3606677 : Blo 1423531 3606677 := bbase (se 6 (by rfl) ⟨84531, by rfl⟩ : syracuseStep 3606677 = 169063) (by norm_num)
theorem B3205277 : Blo 1423531 3205277 := bbase (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) (by norm_num)
theorem B2566325 : Blo 1423531 2566325 := bbase (se 5 (by rfl) ⟨120296, by rfl⟩ : syracuseStep 2566325 = 240593) (by norm_num)
theorem B1444061 : Blo 1423531 1444061 := bbase (se 3 (by rfl) ⟨270761, by rfl⟩ : syracuseStep 1444061 = 541523) (by norm_num)
theorem B3205349 : Blo 1423531 3205349 := bbase (se 4 (by rfl) ⟨300501, by rfl⟩ : syracuseStep 3205349 = 601003) (by norm_num)
theorem B2705653 : Blo 1423531 2705653 := bbase (se 5 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 2705653 = 253655) (by norm_num)
theorem B8669429 : Blo 1423531 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B2402581 : Blo 1423531 2402581 := bbase (se 6 (by rfl) ⟨56310, by rfl⟩ : syracuseStep 2402581 = 112621) (by norm_num)
theorem B3205421 : Blo 1423531 3205421 := bbase (se 3 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 3205421 = 1202033) (by norm_num)
theorem B1624369 : Blo 1423531 1624369 := bbase (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) (by norm_num)
theorem B4565317 : Blo 1423531 4565317 := bbase (se 4 (by rfl) ⟨427998, by rfl⟩ : syracuseStep 4565317 = 855997) (by norm_num)
theorem B3606869 : Blo 1423531 3606869 := bbase (se 10 (by rfl) ⟨5283, by rfl⟩ : syracuseStep 3606869 = 10567) (by norm_num)
theorem B2402669 : Blo 1423531 2402669 := bbase (se 3 (by rfl) ⟨450500, by rfl⟩ : syracuseStep 2402669 = 901001) (by norm_num)
theorem B3205493 : Blo 1423531 3205493 := bbase (se 5 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 3205493 = 300515) (by norm_num)
theorem B22219157 : Blo 1423531 22219157 := bbase (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) (by norm_num)
theorem B7211429 : Blo 1423531 7211429 := bbase (se 4 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 7211429 = 1352143) (by norm_num)
theorem B2927029 : Blo 1423531 2927029 := bbase (se 5 (by rfl) ⟨137204, by rfl⟩ : syracuseStep 2927029 = 274409) (by norm_num)
theorem B3041725 : Blo 1423531 3041725 := bbase (se 3 (by rfl) ⟨570323, by rfl⟩ : syracuseStep 3041725 = 1140647) (by norm_num)
theorem B3205565 : Blo 1423531 3205565 := bbase (se 3 (by rfl) ⟨601043, by rfl⟩ : syracuseStep 3205565 = 1202087) (by norm_num)
theorem B1444321 : Blo 1423531 1444321 := bbase (se 2 (by rfl) ⟨541620, by rfl⟩ : syracuseStep 1444321 = 1083241) (by norm_num)
theorem B2402797 : Blo 1423531 2402797 := bbase (se 3 (by rfl) ⟨450524, by rfl⟩ : syracuseStep 2402797 = 901049) (by norm_num)
theorem B3205637 : Blo 1423531 3205637 := bbase (se 4 (by rfl) ⟨300528, by rfl⟩ : syracuseStep 3205637 = 601057) (by norm_num)
theorem B1542673 : Blo 1423531 1542673 := bbase (se 2 (by rfl) ⟨578502, by rfl⟩ : syracuseStep 1542673 = 1157005) (by norm_num)
theorem B5409301 : Blo 1423531 5409301 := bbase (se 6 (by rfl) ⟨126780, by rfl⟩ : syracuseStep 5409301 = 253561) (by norm_num)
theorem B2705957 : Blo 1423531 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B5130805 : Blo 1423531 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B2402885 : Blo 1423531 2402885 := bbase (se 4 (by rfl) ⟨225270, by rfl⟩ : syracuseStep 2402885 = 450541) (by norm_num)
theorem B3205709 : Blo 1423531 3205709 := bbase (se 3 (by rfl) ⟨601070, by rfl⟩ : syracuseStep 3205709 = 1202141) (by norm_num)
theorem B3205781 : Blo 1423531 3205781 := bbase (se 6 (by rfl) ⟨75135, by rfl⟩ : syracuseStep 3205781 = 150271) (by norm_num)
theorem B3607213 : Blo 1423531 3607213 := bbase (se 3 (by rfl) ⟨676352, by rfl⟩ : syracuseStep 3607213 = 1352705) (by norm_num)
theorem B11553461 : Blo 1423531 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B2403013 : Blo 1423531 2403013 := bbase (se 4 (by rfl) ⟨225282, by rfl⟩ : syracuseStep 2403013 = 450565) (by norm_num)
theorem B3205853 : Blo 1423531 3205853 := bbase (se 3 (by rfl) ⟨601097, by rfl⟩ : syracuseStep 3205853 = 1202195) (by norm_num)
theorem B4057877 : Blo 1423531 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B2403101 : Blo 1423531 2403101 := bbase (se 3 (by rfl) ⟨450581, by rfl⟩ : syracuseStep 2403101 = 901163) (by norm_num)
theorem B3607325 : Blo 1423531 3607325 := bbase (se 3 (by rfl) ⟨676373, by rfl⟩ : syracuseStep 3607325 = 1352747) (by norm_num)
theorem B3205925 : Blo 1423531 3205925 := bbase (se 4 (by rfl) ⟨300555, by rfl⟩ : syracuseStep 3205925 = 601111) (by norm_num)
theorem B5409605 : Blo 1423531 5409605 := bbase (se 4 (by rfl) ⟨507150, by rfl⟩ : syracuseStep 5409605 = 1014301) (by norm_num)
theorem B3205997 : Blo 1423531 3205997 := bbase (se 3 (by rfl) ⟨601124, by rfl⟩ : syracuseStep 3205997 = 1202249) (by norm_num)
theorem B2886533 : Blo 1423531 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B2403229 : Blo 1423531 2403229 := bbase (se 3 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 2403229 = 901211) (by norm_num)
theorem B2567069 : Blo 1423531 2567069 := bbase (se 3 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 2567069 = 962651) (by norm_num)
theorem B2886565 : Blo 1423531 2886565 := bbase (se 4 (by rfl) ⟨270615, by rfl⟩ : syracuseStep 2886565 = 541231) (by norm_num)
theorem B3206069 : Blo 1423531 3206069 := bbase (se 5 (by rfl) ⟨150284, by rfl⟩ : syracuseStep 3206069 = 300569) (by norm_num)
theorem B5483477 : Blo 1423531 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B3607517 : Blo 1423531 3607517 := bbase (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) (by norm_num)
theorem B2403317 : Blo 1423531 2403317 := bbase (se 5 (by rfl) ⟨112655, by rfl⟩ : syracuseStep 2403317 = 225311) (by norm_num)
theorem B3206141 : Blo 1423531 3206141 := bbase (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) (by norm_num)
theorem B3206213 : Blo 1423531 3206213 := bbase (se 4 (by rfl) ⟨300582, by rfl⟩ : syracuseStep 3206213 = 601165) (by norm_num)
theorem B6081637 : Blo 1423531 6081637 := bbase (se 4 (by rfl) ⟨570153, by rfl⟩ : syracuseStep 6081637 = 1140307) (by norm_num)
theorem B2403445 : Blo 1423531 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B4566149 : Blo 1423531 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B3206285 : Blo 1423531 3206285 := bbase (se 3 (by rfl) ⟨601178, by rfl⟩ : syracuseStep 3206285 = 1202357) (by norm_num)
theorem B2403533 : Blo 1423531 2403533 := bbase (se 3 (by rfl) ⟨450662, by rfl⟩ : syracuseStep 2403533 = 901325) (by norm_num)
theorem B3206357 : Blo 1423531 3206357 := bbase (se 7 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 3206357 = 75149) (by norm_num)
theorem B3206429 : Blo 1423531 3206429 := bbase (se 3 (by rfl) ⟨601205, by rfl⟩ : syracuseStep 3206429 = 1202411) (by norm_num)
theorem B3042613 : Blo 1423531 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B3607861 : Blo 1423531 3607861 := bbase (se 5 (by rfl) ⟨169118, by rfl⟩ : syracuseStep 3607861 = 338237) (by norm_num)
theorem B2403661 : Blo 1423531 2403661 := bbase (se 3 (by rfl) ⟨450686, by rfl⟩ : syracuseStep 2403661 = 901373) (by norm_num)
theorem B3206501 : Blo 1423531 3206501 := bbase (se 4 (by rfl) ⟨300609, by rfl⟩ : syracuseStep 3206501 = 601219) (by norm_num)
theorem B2280845 : Blo 1423531 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B2403749 : Blo 1423531 2403749 := bbase (se 4 (by rfl) ⟨225351, by rfl⟩ : syracuseStep 2403749 = 450703) (by norm_num)
theorem B3607973 : Blo 1423531 3607973 := bbase (se 4 (by rfl) ⟨338247, by rfl⟩ : syracuseStep 3607973 = 676495) (by norm_num)
theorem B3206573 : Blo 1423531 3206573 := bbase (se 3 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 3206573 = 1202465) (by norm_num)
theorem B4058549 : Blo 1423531 4058549 := bbase (se 5 (by rfl) ⟨190244, by rfl⟩ : syracuseStep 4058549 = 380489) (by norm_num)
theorem B3206645 : Blo 1423531 3206645 := bbase (se 5 (by rfl) ⟨150311, by rfl⟩ : syracuseStep 3206645 = 300623) (by norm_num)
theorem B2403877 : Blo 1423531 2403877 := bbase (se 4 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 2403877 = 450727) (by norm_num)
theorem B2027053 : Blo 1423531 2027053 := bbase (se 3 (by rfl) ⟨380072, by rfl⟩ : syracuseStep 2027053 = 760145) (by norm_num)
theorem B3247661 : Blo 1423531 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B3206717 : Blo 1423531 3206717 := bbase (se 3 (by rfl) ⟨601259, by rfl⟩ : syracuseStep 3206717 = 1202519) (by norm_num)
theorem B3608165 : Blo 1423531 3608165 := bbase (se 4 (by rfl) ⟨338265, by rfl⟩ : syracuseStep 3608165 = 676531) (by norm_num)
theorem B2403965 : Blo 1423531 2403965 := bbase (se 3 (by rfl) ⟨450743, by rfl⟩ : syracuseStep 2403965 = 901487) (by norm_num)
theorem B3206789 : Blo 1423531 3206789 := bbase (se 4 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 3206789 = 601273) (by norm_num)
theorem B7212725 : Blo 1423531 7212725 := bbase (se 5 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 7212725 = 676193) (by norm_num)
theorem B3206861 : Blo 1423531 3206861 := bbase (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) (by norm_num)
theorem B2404093 : Blo 1423531 2404093 := bbase (se 3 (by rfl) ⟨450767, by rfl⟩ : syracuseStep 2404093 = 901535) (by norm_num)
theorem B3206933 : Blo 1423531 3206933 := bbase (se 6 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 3206933 = 150325) (by norm_num)
theorem B3043109 : Blo 1423531 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B2404181 : Blo 1423531 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B3207005 : Blo 1423531 3207005 := bbase (se 3 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 3207005 = 1202627) (by norm_num)
theorem B4058981 : Blo 1423531 4058981 := bbase (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) (by norm_num)
theorem B6500245 : Blo 1423531 6500245 := bbase (se 6 (by rfl) ⟨152349, by rfl⟩ : syracuseStep 6500245 = 304699) (by norm_num)
theorem B3207077 : Blo 1423531 3207077 := bbase (se 4 (by rfl) ⟨300663, by rfl⟩ : syracuseStep 3207077 = 601327) (by norm_num)
theorem B1601473 : Blo 1423531 1601473 := bbase (se 2 (by rfl) ⟨600552, by rfl⟩ : syracuseStep 1601473 = 1201105) (by norm_num)
theorem B2404309 : Blo 1423531 2404309 := bbase (se 7 (by rfl) ⟨28175, by rfl⟩ : syracuseStep 2404309 = 56351) (by norm_num)
theorem B9129941 : Blo 1423531 9129941 := bbase (se 7 (by rfl) ⟨106991, by rfl⟩ : syracuseStep 9129941 = 213983) (by norm_num)
theorem B1601509 : Blo 1423531 1601509 := bbase (se 4 (by rfl) ⟨150141, by rfl⟩ : syracuseStep 1601509 = 300283) (by norm_num)
theorem B3207149 : Blo 1423531 3207149 := bbase (se 3 (by rfl) ⟨601340, by rfl⟩ : syracuseStep 3207149 = 1202681) (by norm_num)
theorem B1601545 : Blo 1423531 1601545 := bbase (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) (by norm_num)
theorem B2166797 : Blo 1423531 2166797 := bbase (se 3 (by rfl) ⟨406274, by rfl⟩ : syracuseStep 2166797 = 812549) (by norm_num)
theorem B1601581 : Blo 1423531 1601581 := bbase (se 3 (by rfl) ⟨300296, by rfl⟩ : syracuseStep 1601581 = 600593) (by norm_num)
theorem B2404397 : Blo 1423531 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B3207221 : Blo 1423531 3207221 := bbase (se 5 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 3207221 = 300677) (by norm_num)
theorem B1601617 : Blo 1423531 1601617 := bbase (se 2 (by rfl) ⟨600606, by rfl⟩ : syracuseStep 1601617 = 1201213) (by norm_num)
theorem B1601653 : Blo 1423531 1601653 := bbase (se 5 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 1601653 = 150155) (by norm_num)
theorem B3207293 : Blo 1423531 3207293 := bbase (se 3 (by rfl) ⟨601367, by rfl⟩ : syracuseStep 3207293 = 1202735) (by norm_num)
theorem B4804757 : Blo 1423531 4804757 := bbase (se 6 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 4804757 = 225223) (by norm_num)
theorem B1601689 : Blo 1423531 1601689 := bbase (se 2 (by rfl) ⟨600633, by rfl⟩ : syracuseStep 1601689 = 1201267) (by norm_num)
theorem B2404525 : Blo 1423531 2404525 := bbase (se 3 (by rfl) ⟨450848, by rfl⟩ : syracuseStep 2404525 = 901697) (by norm_num)
theorem B1601725 : Blo 1423531 1601725 := bbase (se 3 (by rfl) ⟨300323, by rfl⟩ : syracuseStep 1601725 = 600647) (by norm_num)
theorem B3338437 : Blo 1423531 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B3207365 : Blo 1423531 3207365 := bbase (se 4 (by rfl) ⟨300690, by rfl⟩ : syracuseStep 3207365 = 601381) (by norm_num)
theorem B1601761 : Blo 1423531 1601761 := bbase (se 2 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 1601761 = 1201321) (by norm_num)
theorem B4329701 : Blo 1423531 4329701 := bbase (se 4 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 4329701 = 811819) (by norm_num)
theorem B1601797 : Blo 1423531 1601797 := bbase (se 4 (by rfl) ⟨150168, by rfl⟩ : syracuseStep 1601797 = 300337) (by norm_num)
theorem B2404613 : Blo 1423531 2404613 := bbase (se 4 (by rfl) ⟨225432, by rfl⟩ : syracuseStep 2404613 = 450865) (by norm_num)
theorem B3207437 : Blo 1423531 3207437 := bbase (se 3 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 3207437 = 1202789) (by norm_num)
theorem B1601833 : Blo 1423531 1601833 := bbase (se 2 (by rfl) ⟨600687, by rfl⟩ : syracuseStep 1601833 = 1201375) (by norm_num)
theorem B3420461 : Blo 1423531 3420461 := bbase (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) (by norm_num)
theorem B2027845 : Blo 1423531 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B1601869 : Blo 1423531 1601869 := bbase (se 3 (by rfl) ⟨300350, by rfl⟩ : syracuseStep 1601869 = 600701) (by norm_num)
theorem B19501397 : Blo 1423531 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B1601905 : Blo 1423531 1601905 := bbase (se 2 (by rfl) ⟨600714, by rfl⟩ : syracuseStep 1601905 = 1201429) (by norm_num)
theorem B2404741 : Blo 1423531 2404741 := bbase (se 4 (by rfl) ⟨225444, by rfl⟩ : syracuseStep 2404741 = 450889) (by norm_num)
theorem B1601941 : Blo 1423531 1601941 := bbase (se 6 (by rfl) ⟨37545, by rfl⟩ : syracuseStep 1601941 = 75091) (by norm_num)
theorem B11121077 : Blo 1423531 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B1601977 : Blo 1423531 1601977 := bbase (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) (by norm_num)
theorem B3420605 : Blo 1423531 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B1602013 : Blo 1423531 1602013 := bbase (se 3 (by rfl) ⟨300377, by rfl⟩ : syracuseStep 1602013 = 600755) (by norm_num)
theorem B2404829 : Blo 1423531 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B1602049 : Blo 1423531 1602049 := bbase (se 2 (by rfl) ⟨600768, by rfl⟩ : syracuseStep 1602049 = 1201537) (by norm_num)
theorem B1602085 : Blo 1423531 1602085 := bbase (se 4 (by rfl) ⟨150195, by rfl⟩ : syracuseStep 1602085 = 300391) (by norm_num)
theorem B4805189 : Blo 1423531 4805189 := bbase (se 4 (by rfl) ⟨450486, by rfl⟩ : syracuseStep 4805189 = 900973) (by norm_num)
theorem B1602121 : Blo 1423531 1602121 := bbase (se 2 (by rfl) ⟨600795, by rfl⟩ : syracuseStep 1602121 = 1201591) (by norm_num)
theorem B1520213 : Blo 1423531 1520213 := bbase (se 8 (by rfl) ⟨8907, by rfl⟩ : syracuseStep 1520213 = 17815) (by norm_num)
theorem B2404957 : Blo 1423531 2404957 := bbase (se 3 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 2404957 = 901859) (by norm_num)
theorem B1602157 : Blo 1423531 1602157 := bbase (se 3 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 1602157 = 600809) (by norm_num)
theorem B13873781 : Blo 1423531 13873781 := bbase (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) (by norm_num)
theorem B7705205 : Blo 1423531 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B1602193 : Blo 1423531 1602193 := bbase (se 2 (by rfl) ⟨600822, by rfl⟩ : syracuseStep 1602193 = 1201645) (by norm_num)
theorem B2028181 : Blo 1423531 2028181 := bbase (se 6 (by rfl) ⟨47535, by rfl⟩ : syracuseStep 2028181 = 95071) (by norm_num)
theorem B3043997 : Blo 1423531 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B3420845 : Blo 1423531 3420845 := bbase (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) (by norm_num)
theorem B1602229 : Blo 1423531 1602229 := bbase (se 5 (by rfl) ⟨75104, by rfl⟩ : syracuseStep 1602229 = 150209) (by norm_num)
theorem B2405045 : Blo 1423531 2405045 := bbase (se 5 (by rfl) ⟨112736, by rfl⟩ : syracuseStep 2405045 = 225473) (by norm_num)
theorem B1602265 : Blo 1423531 1602265 := bbase (se 2 (by rfl) ⟨600849, by rfl⟩ : syracuseStep 1602265 = 1201699) (by norm_num)
theorem B1602301 : Blo 1423531 1602301 := bbase (se 3 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 1602301 = 600863) (by norm_num)
theorem B3044117 : Blo 1423531 3044117 := bbase (se 6 (by rfl) ⟨71346, by rfl⟩ : syracuseStep 3044117 = 142693) (by norm_num)
theorem B1602337 : Blo 1423531 1602337 := bbase (se 2 (by rfl) ⟨600876, by rfl⟩ : syracuseStep 1602337 = 1201753) (by norm_num)
theorem B2405173 : Blo 1423531 2405173 := bbase (se 5 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 2405173 = 225485) (by norm_num)
theorem B1602373 : Blo 1423531 1602373 := bbase (se 4 (by rfl) ⟨150222, by rfl⟩ : syracuseStep 1602373 = 300445) (by norm_num)
theorem B1520461 : Blo 1423531 1520461 := bbase (se 3 (by rfl) ⟨285086, by rfl⟩ : syracuseStep 1520461 = 570173) (by norm_num)
theorem B1602409 : Blo 1423531 1602409 := bbase (se 2 (by rfl) ⟨600903, by rfl⟩ : syracuseStep 1602409 = 1201807) (by norm_num)
theorem B2028397 : Blo 1423531 2028397 := bbase (se 3 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 2028397 = 760649) (by norm_num)
theorem B2282357 : Blo 1423531 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B5411717 : Blo 1423531 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B1602445 : Blo 1423531 1602445 := bbase (se 3 (by rfl) ⟨300458, by rfl⟩ : syracuseStep 1602445 = 600917) (by norm_num)
theorem B2405261 : Blo 1423531 2405261 := bbase (se 3 (by rfl) ⟨450986, by rfl⟩ : syracuseStep 2405261 = 901973) (by norm_num)
theorem B1602481 : Blo 1423531 1602481 := bbase (se 2 (by rfl) ⟨600930, by rfl⟩ : syracuseStep 1602481 = 1201861) (by norm_num)
theorem B7214021 : Blo 1423531 7214021 := bbase (se 4 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 7214021 = 1352629) (by norm_num)
theorem B1602517 : Blo 1423531 1602517 := bbase (se 7 (by rfl) ⟨18779, by rfl⟩ : syracuseStep 1602517 = 37559) (by norm_num)
theorem B3085285 : Blo 1423531 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B4805621 : Blo 1423531 4805621 := bbase (se 5 (by rfl) ⟨225263, by rfl⟩ : syracuseStep 4805621 = 450527) (by norm_num)
theorem B1602553 : Blo 1423531 1602553 := bbase (se 2 (by rfl) ⟨600957, by rfl⟩ : syracuseStep 1602553 = 1201915) (by norm_num)
theorem B2405389 : Blo 1423531 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B1602589 : Blo 1423531 1602589 := bbase (se 3 (by rfl) ⟨300485, by rfl⟩ : syracuseStep 1602589 = 600971) (by norm_num)
theorem B1602625 : Blo 1423531 1602625 := bbase (se 2 (by rfl) ⟨600984, by rfl⟩ : syracuseStep 1602625 = 1201969) (by norm_num)
theorem B1602661 : Blo 1423531 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B2405477 : Blo 1423531 2405477 := bbase (se 4 (by rfl) ⟨225513, by rfl⟩ : syracuseStep 2405477 = 451027) (by norm_num)
theorem B6845573 : Blo 1423531 6845573 := bbase (se 4 (by rfl) ⟨641772, by rfl⟩ : syracuseStep 6845573 = 1283545) (by norm_num)
theorem B1602697 : Blo 1423531 1602697 := bbase (se 2 (by rfl) ⟨601011, by rfl⟩ : syracuseStep 1602697 = 1202023) (by norm_num)
theorem B5412005 : Blo 1423531 5412005 := bbase (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) (by norm_num)
theorem B1602733 : Blo 1423531 1602733 := bbase (se 3 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 1602733 = 601025) (by norm_num)
theorem B2888885 : Blo 1423531 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B1602769 : Blo 1423531 1602769 := bbase (se 2 (by rfl) ⟨601038, by rfl⟩ : syracuseStep 1602769 = 1202077) (by norm_num)
theorem B2028773 : Blo 1423531 2028773 := bbase (se 4 (by rfl) ⟨190197, by rfl⟩ : syracuseStep 2028773 = 380395) (by norm_num)
theorem B1602805 : Blo 1423531 1602805 := bbase (se 5 (by rfl) ⟨75131, by rfl⟩ : syracuseStep 1602805 = 150263) (by norm_num)
theorem B1520905 : Blo 1423531 1520905 := bbase (se 2 (by rfl) ⟨570339, by rfl⟩ : syracuseStep 1520905 = 1140679) (by norm_num)
theorem B2135309 : Blo 1423531 2135309 := bbase (se 3 (by rfl) ⟨400370, by rfl⟩ : syracuseStep 2135309 = 800741) (by norm_num)
theorem B1602841 : Blo 1423531 1602841 := bbase (se 2 (by rfl) ⟨601065, by rfl⟩ : syracuseStep 1602841 = 1202131) (by norm_num)
theorem B2135333 : Blo 1423531 2135333 := bbase (se 4 (by rfl) ⟨200187, by rfl⟩ : syracuseStep 2135333 = 400375) (by norm_num)
theorem B2135357 : Blo 1423531 2135357 := bbase (se 3 (by rfl) ⟨400379, by rfl⟩ : syracuseStep 2135357 = 800759) (by norm_num)
theorem B1602877 : Blo 1423531 1602877 := bbase (se 3 (by rfl) ⟨300539, by rfl⟩ : syracuseStep 1602877 = 601079) (by norm_num)
theorem B2282813 : Blo 1423531 2282813 := bbase (se 3 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 2282813 = 856055) (by norm_num)
theorem B1520965 : Blo 1423531 1520965 := bbase (se 4 (by rfl) ⟨142590, by rfl⟩ : syracuseStep 1520965 = 285181) (by norm_num)
theorem B2135381 : Blo 1423531 2135381 := bbase (se 14 (by rfl) ⟨195, by rfl⟩ : syracuseStep 2135381 = 391) (by norm_num)
theorem B1602913 : Blo 1423531 1602913 := bbase (se 2 (by rfl) ⟨601092, by rfl⟩ : syracuseStep 1602913 = 1202185) (by norm_num)
theorem B2135405 : Blo 1423531 2135405 := bbase (se 3 (by rfl) ⟨400388, by rfl⟩ : syracuseStep 2135405 = 800777) (by norm_num)
theorem B3249533 : Blo 1423531 3249533 := bbase (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) (by norm_num)
theorem B2135429 : Blo 1423531 2135429 := bbase (se 4 (by rfl) ⟨200196, by rfl⟩ : syracuseStep 2135429 = 400393) (by norm_num)
theorem B1602949 : Blo 1423531 1602949 := bbase (se 4 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 1602949 = 300553) (by norm_num)
theorem B4871573 : Blo 1423531 4871573 := bbase (se 6 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 4871573 = 228355) (by norm_num)
theorem B2135453 : Blo 1423531 2135453 := bbase (se 3 (by rfl) ⟨400397, by rfl⟩ : syracuseStep 2135453 = 800795) (by norm_num)
theorem B4806053 : Blo 1423531 4806053 := bbase (se 4 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 4806053 = 901135) (by norm_num)
theorem B1602985 : Blo 1423531 1602985 := bbase (se 2 (by rfl) ⟨601119, by rfl⟩ : syracuseStep 1602985 = 1202239) (by norm_num)
theorem B3421613 : Blo 1423531 3421613 := bbase (se 3 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 3421613 = 1283105) (by norm_num)
theorem B2135477 : Blo 1423531 2135477 := bbase (se 5 (by rfl) ⟨100100, by rfl⟩ : syracuseStep 2135477 = 200201) (by norm_num)
theorem B2135501 : Blo 1423531 2135501 := bbase (se 3 (by rfl) ⟨400406, by rfl⟩ : syracuseStep 2135501 = 800813) (by norm_num)
theorem B1603021 : Blo 1423531 1603021 := bbase (se 3 (by rfl) ⟨300566, by rfl⟩ : syracuseStep 1603021 = 601133) (by norm_num)
theorem B2135525 : Blo 1423531 2135525 := bbase (se 4 (by rfl) ⟨200205, by rfl⟩ : syracuseStep 2135525 = 400411) (by norm_num)
theorem B1603057 : Blo 1423531 1603057 := bbase (se 2 (by rfl) ⟨601146, by rfl⟩ : syracuseStep 1603057 = 1202293) (by norm_num)
theorem B2135549 : Blo 1423531 2135549 := bbase (se 3 (by rfl) ⟨400415, by rfl⟩ : syracuseStep 2135549 = 800831) (by norm_num)
theorem B2135573 : Blo 1423531 2135573 := bbase (se 6 (by rfl) ⟨50052, by rfl⟩ : syracuseStep 2135573 = 100105) (by norm_num)
theorem B1603093 : Blo 1423531 1603093 := bbase (se 6 (by rfl) ⟨37572, by rfl⟩ : syracuseStep 1603093 = 75145) (by norm_num)
theorem B2135597 : Blo 1423531 2135597 := bbase (se 3 (by rfl) ⟨400424, by rfl⟩ : syracuseStep 2135597 = 800849) (by norm_num)
theorem B8107573 : Blo 1423531 8107573 := bbase (se 5 (by rfl) ⟨380042, by rfl⟩ : syracuseStep 8107573 = 760085) (by norm_num)
theorem B1734197 : Blo 1423531 1734197 := bbase (se 5 (by rfl) ⟨81290, by rfl⟩ : syracuseStep 1734197 = 162581) (by norm_num)
theorem B1603129 : Blo 1423531 1603129 := bbase (se 2 (by rfl) ⟨601173, by rfl⟩ : syracuseStep 1603129 = 1202347) (by norm_num)
theorem B2135621 : Blo 1423531 2135621 := bbase (se 4 (by rfl) ⟨200214, by rfl⟩ : syracuseStep 2135621 = 400429) (by norm_num)
theorem B2135645 : Blo 1423531 2135645 := bbase (se 3 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 2135645 = 800867) (by norm_num)
theorem B1603165 : Blo 1423531 1603165 := bbase (se 3 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 1603165 = 601187) (by norm_num)
theorem B2135669 : Blo 1423531 2135669 := bbase (se 5 (by rfl) ⟨100109, by rfl⟩ : syracuseStep 2135669 = 200219) (by norm_num)
theorem B1521281 : Blo 1423531 1521281 := bbase (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) (by norm_num)
theorem B1603201 : Blo 1423531 1603201 := bbase (se 2 (by rfl) ⟨601200, by rfl⟩ : syracuseStep 1603201 = 1202401) (by norm_num)
theorem B2135693 : Blo 1423531 2135693 := bbase (se 3 (by rfl) ⟨400442, by rfl⟩ : syracuseStep 2135693 = 800885) (by norm_num)
theorem B2135717 : Blo 1423531 2135717 := bbase (se 4 (by rfl) ⟨200223, by rfl⟩ : syracuseStep 2135717 = 400447) (by norm_num)
theorem B1603237 : Blo 1423531 1603237 := bbase (se 4 (by rfl) ⟨150303, by rfl⟩ : syracuseStep 1603237 = 300607) (by norm_num)
theorem B2135741 : Blo 1423531 2135741 := bbase (se 3 (by rfl) ⟨400451, by rfl⟩ : syracuseStep 2135741 = 800903) (by norm_num)
theorem B1603273 : Blo 1423531 1603273 := bbase (se 2 (by rfl) ⟨601227, by rfl⟩ : syracuseStep 1603273 = 1202455) (by norm_num)
theorem B2135765 : Blo 1423531 2135765 := bbase (se 7 (by rfl) ⟨25028, by rfl⟩ : syracuseStep 2135765 = 50057) (by norm_num)
theorem B2135789 : Blo 1423531 2135789 := bbase (se 3 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 2135789 = 800921) (by norm_num)
theorem B1603309 : Blo 1423531 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B2135813 : Blo 1423531 2135813 := bbase (se 4 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 2135813 = 400465) (by norm_num)
theorem B1603345 : Blo 1423531 1603345 := bbase (se 2 (by rfl) ⟨601254, by rfl⟩ : syracuseStep 1603345 = 1202509) (by norm_num)
theorem B8664853 : Blo 1423531 8664853 := bbase (se 6 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 8664853 = 406165) (by norm_num)
theorem B2135837 : Blo 1423531 2135837 := bbase (se 3 (by rfl) ⟨400469, by rfl⟩ : syracuseStep 2135837 = 800939) (by norm_num)
theorem B2135861 : Blo 1423531 2135861 := bbase (se 5 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 2135861 = 200237) (by norm_num)
theorem B1603381 : Blo 1423531 1603381 := bbase (se 5 (by rfl) ⟨75158, by rfl⟩ : syracuseStep 1603381 = 150317) (by norm_num)
theorem B2135885 : Blo 1423531 2135885 := bbase (se 3 (by rfl) ⟨400478, by rfl⟩ : syracuseStep 2135885 = 800957) (by norm_num)
theorem B4806485 : Blo 1423531 4806485 := bbase (se 9 (by rfl) ⟨14081, by rfl⟩ : syracuseStep 4806485 = 28163) (by norm_num)
theorem B1603417 : Blo 1423531 1603417 := bbase (se 2 (by rfl) ⟨601281, by rfl⟩ : syracuseStep 1603417 = 1202563) (by norm_num)
theorem B2135909 : Blo 1423531 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B2135933 : Blo 1423531 2135933 := bbase (se 3 (by rfl) ⟨400487, by rfl⟩ : syracuseStep 2135933 = 800975) (by norm_num)
theorem B1603453 : Blo 1423531 1603453 := bbase (se 3 (by rfl) ⟨300647, by rfl⟩ : syracuseStep 1603453 = 601295) (by norm_num)
theorem B2135957 : Blo 1423531 2135957 := bbase (se 6 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 2135957 = 100123) (by norm_num)
theorem B1603489 : Blo 1423531 1603489 := bbase (se 2 (by rfl) ⟨601308, by rfl⟩ : syracuseStep 1603489 = 1202617) (by norm_num)
theorem B2135981 : Blo 1423531 2135981 := bbase (se 3 (by rfl) ⟨400496, by rfl⟩ : syracuseStep 2135981 = 800993) (by norm_num)
theorem B2136005 : Blo 1423531 2136005 := bbase (se 4 (by rfl) ⟨200250, by rfl⟩ : syracuseStep 2136005 = 400501) (by norm_num)
theorem B1603525 : Blo 1423531 1603525 := bbase (se 4 (by rfl) ⟨150330, by rfl⟩ : syracuseStep 1603525 = 300661) (by norm_num)
theorem B2742229 : Blo 1423531 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B2136029 : Blo 1423531 2136029 := bbase (se 3 (by rfl) ⟨400505, by rfl⟩ : syracuseStep 2136029 = 801011) (by norm_num)
theorem B1603561 : Blo 1423531 1603561 := bbase (se 2 (by rfl) ⟨601335, by rfl⟩ : syracuseStep 1603561 = 1202671) (by norm_num)
theorem B2136053 : Blo 1423531 2136053 := bbase (se 5 (by rfl) ⟨100127, by rfl⟩ : syracuseStep 2136053 = 200255) (by norm_num)
theorem B2136077 : Blo 1423531 2136077 := bbase (se 3 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 2136077 = 801029) (by norm_num)
theorem B1603597 : Blo 1423531 1603597 := bbase (se 3 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 1603597 = 601349) (by norm_num)
theorem B11548693 : Blo 1423531 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B6084629 : Blo 1423531 6084629 := bbase (se 6 (by rfl) ⟨142608, by rfl⟩ : syracuseStep 6084629 = 285217) (by norm_num)
theorem B2136101 : Blo 1423531 2136101 := bbase (se 4 (by rfl) ⟨200259, by rfl⟩ : syracuseStep 2136101 = 400519) (by norm_num)
theorem B1603633 : Blo 1423531 1603633 := bbase (se 2 (by rfl) ⟨601362, by rfl⟩ : syracuseStep 1603633 = 1202725) (by norm_num)
theorem B2136125 : Blo 1423531 2136125 := bbase (se 3 (by rfl) ⟨400523, by rfl⟩ : syracuseStep 2136125 = 801047) (by norm_num)
theorem B1521725 : Blo 1423531 1521725 := bbase (se 3 (by rfl) ⟨285323, by rfl⟩ : syracuseStep 1521725 = 570647) (by norm_num)
theorem B2136149 : Blo 1423531 2136149 := bbase (se 8 (by rfl) ⟨12516, by rfl⟩ : syracuseStep 2136149 = 25033) (by norm_num)
theorem B1603669 : Blo 1423531 1603669 := bbase (se 8 (by rfl) ⟨9396, by rfl⟩ : syracuseStep 1603669 = 18793) (by norm_num)
theorem B2136173 : Blo 1423531 2136173 := bbase (se 3 (by rfl) ⟨400532, by rfl⟩ : syracuseStep 2136173 = 801065) (by norm_num)
theorem B1521785 : Blo 1423531 1521785 := bbase (se 2 (by rfl) ⟨570669, by rfl⟩ : syracuseStep 1521785 = 1141339) (by norm_num)
theorem B1603705 : Blo 1423531 1603705 := bbase (se 2 (by rfl) ⟨601389, by rfl⟩ : syracuseStep 1603705 = 1202779) (by norm_num)
theorem B2136197 : Blo 1423531 2136197 := bbase (se 4 (by rfl) ⟨200268, by rfl⟩ : syracuseStep 2136197 = 400537) (by norm_num)
theorem B2136221 : Blo 1423531 2136221 := bbase (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) (by norm_num)
theorem B2136245 : Blo 1423531 2136245 := bbase (se 5 (by rfl) ⟨100136, by rfl⟩ : syracuseStep 2136245 = 200273) (by norm_num)
theorem B2136269 : Blo 1423531 2136269 := bbase (se 3 (by rfl) ⟨400550, by rfl⟩ : syracuseStep 2136269 = 801101) (by norm_num)
theorem B7215317 : Blo 1423531 7215317 := bbase (se 7 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 7215317 = 169109) (by norm_num)
theorem B2136293 : Blo 1423531 2136293 := bbase (se 4 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 2136293 = 400555) (by norm_num)
theorem B1521913 : Blo 1423531 1521913 := bbase (se 2 (by rfl) ⟨570717, by rfl⟩ : syracuseStep 1521913 = 1141435) (by norm_num)
theorem B2136317 : Blo 1423531 2136317 := bbase (se 3 (by rfl) ⟨400559, by rfl⟩ : syracuseStep 2136317 = 801119) (by norm_num)
theorem B4806917 : Blo 1423531 4806917 := bbase (se 4 (by rfl) ⟨450648, by rfl⟩ : syracuseStep 4806917 = 901297) (by norm_num)
theorem B2136341 : Blo 1423531 2136341 := bbase (se 6 (by rfl) ⟨50070, by rfl⟩ : syracuseStep 2136341 = 100141) (by norm_num)
theorem B2136365 : Blo 1423531 2136365 := bbase (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) (by norm_num)
theorem B2136389 : Blo 1423531 2136389 := bbase (se 4 (by rfl) ⟨200286, by rfl⟩ : syracuseStep 2136389 = 400573) (by norm_num)
theorem B2136413 : Blo 1423531 2136413 := bbase (se 3 (by rfl) ⟨400577, by rfl⟩ : syracuseStep 2136413 = 801155) (by norm_num)
theorem B2136437 : Blo 1423531 2136437 := bbase (se 5 (by rfl) ⟨100145, by rfl⟩ : syracuseStep 2136437 = 200291) (by norm_num)
theorem B2136461 : Blo 1423531 2136461 := bbase (se 3 (by rfl) ⟨400586, by rfl⟩ : syracuseStep 2136461 = 801173) (by norm_num)
theorem B2136485 : Blo 1423531 2136485 := bbase (se 4 (by rfl) ⟨200295, by rfl⟩ : syracuseStep 2136485 = 400591) (by norm_num)
theorem B8444341 : Blo 1423531 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B2136509 : Blo 1423531 2136509 := bbase (se 3 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 2136509 = 801191) (by norm_num)
theorem B2136533 : Blo 1423531 2136533 := bbase (se 7 (by rfl) ⟨25037, by rfl⟩ : syracuseStep 2136533 = 50075) (by norm_num)
theorem B2136557 : Blo 1423531 2136557 := bbase (se 3 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 2136557 = 801209) (by norm_num)
theorem B2136581 : Blo 1423531 2136581 := bbase (se 4 (by rfl) ⟨200304, by rfl⟩ : syracuseStep 2136581 = 400609) (by norm_num)
theorem B4332037 : Blo 1423531 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B2136605 : Blo 1423531 2136605 := bbase (se 3 (by rfl) ⟨400613, by rfl⟩ : syracuseStep 2136605 = 801227) (by norm_num)
theorem B2136629 : Blo 1423531 2136629 := bbase (se 5 (by rfl) ⟨100154, by rfl⟩ : syracuseStep 2136629 = 200309) (by norm_num)
theorem B2136653 : Blo 1423531 2136653 := bbase (se 3 (by rfl) ⟨400622, by rfl⟩ : syracuseStep 2136653 = 801245) (by norm_num)
theorem B2136677 : Blo 1423531 2136677 := bbase (se 4 (by rfl) ⟨200313, by rfl⟩ : syracuseStep 2136677 = 400627) (by norm_num)
theorem B7207541 : Blo 1423531 7207541 := bbase (se 5 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 7207541 = 675707) (by norm_num)
theorem B14629493 : Blo 1423531 14629493 := bbase (se 5 (by rfl) ⟨685757, by rfl⟩ : syracuseStep 14629493 = 1371515) (by norm_num)
theorem B2136701 : Blo 1423531 2136701 := bbase (se 3 (by rfl) ⟨400631, by rfl⟩ : syracuseStep 2136701 = 801263) (by norm_num)
theorem B2136725 : Blo 1423531 2136725 := bbase (se 6 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 2136725 = 100159) (by norm_num)
theorem B2603677 : Blo 1423531 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B2136749 : Blo 1423531 2136749 := bbase (se 3 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 2136749 = 801281) (by norm_num)
theorem B4807349 : Blo 1423531 4807349 := bbase (se 5 (by rfl) ⟨225344, by rfl⟩ : syracuseStep 4807349 = 450689) (by norm_num)
theorem B2136773 : Blo 1423531 2136773 := bbase (se 4 (by rfl) ⟨200322, by rfl⟩ : syracuseStep 2136773 = 400645) (by norm_num)
theorem B2136797 : Blo 1423531 2136797 := bbase (se 3 (by rfl) ⟨400649, by rfl⟩ : syracuseStep 2136797 = 801299) (by norm_num)
theorem B5405413 : Blo 1423531 5405413 := bbase (se 4 (by rfl) ⟨506757, by rfl⟩ : syracuseStep 5405413 = 1013515) (by norm_num)
theorem B2136821 : Blo 1423531 2136821 := bbase (se 5 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 2136821 = 200327) (by norm_num)
theorem B2136845 : Blo 1423531 2136845 := bbase (se 3 (by rfl) ⟨400658, by rfl⟩ : syracuseStep 2136845 = 801317) (by norm_num)
theorem B3422989 : Blo 1423531 3422989 := bbase (se 3 (by rfl) ⟨641810, by rfl⟩ : syracuseStep 3422989 = 1283621) (by norm_num)
theorem B2136869 : Blo 1423531 2136869 := bbase (se 4 (by rfl) ⟨200331, by rfl⟩ : syracuseStep 2136869 = 400663) (by norm_num)
theorem B2136893 : Blo 1423531 2136893 := bbase (se 3 (by rfl) ⟨400667, by rfl⟩ : syracuseStep 2136893 = 801335) (by norm_num)
theorem B2136917 : Blo 1423531 2136917 := bbase (se 9 (by rfl) ⟨6260, by rfl⟩ : syracuseStep 2136917 = 12521) (by norm_num)
theorem B2136941 : Blo 1423531 2136941 := bbase (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) (by norm_num)
theorem B3603325 : Blo 1423531 3603325 := bbase (se 3 (by rfl) ⟨675623, by rfl⟩ : syracuseStep 3603325 = 1351247) (by norm_num)
theorem B1735553 : Blo 1423531 1735553 := bbase (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) (by norm_num)
theorem B2136965 : Blo 1423531 2136965 := bbase (se 4 (by rfl) ⟨200340, by rfl⟩ : syracuseStep 2136965 = 400681) (by norm_num)
theorem B2136989 : Blo 1423531 2136989 := bbase (se 3 (by rfl) ⟨400685, by rfl⟩ : syracuseStep 2136989 = 801371) (by norm_num)
theorem B2137013 : Blo 1423531 2137013 := bbase (se 5 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 2137013 = 200345) (by norm_num)
theorem B2137037 : Blo 1423531 2137037 := bbase (se 3 (by rfl) ⟨400694, by rfl⟩ : syracuseStep 2137037 = 801389) (by norm_num)
theorem B2137061 : Blo 1423531 2137061 := bbase (se 4 (by rfl) ⟨200349, by rfl⟩ : syracuseStep 2137061 = 400699) (by norm_num)
theorem B3603437 : Blo 1423531 3603437 := bbase (se 3 (by rfl) ⟨675644, by rfl⟩ : syracuseStep 3603437 = 1351289) (by norm_num)
theorem B2137085 : Blo 1423531 2137085 := bbase (se 3 (by rfl) ⟨400703, by rfl⟩ : syracuseStep 2137085 = 801407) (by norm_num)
theorem B6085637 : Blo 1423531 6085637 := bbase (se 4 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 6085637 = 1141057) (by norm_num)
theorem B5405717 : Blo 1423531 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B2137109 : Blo 1423531 2137109 := bbase (se 6 (by rfl) ⟨50088, by rfl⟩ : syracuseStep 2137109 = 100177) (by norm_num)
theorem B2137133 : Blo 1423531 2137133 := bbase (se 3 (by rfl) ⟨400712, by rfl⟩ : syracuseStep 2137133 = 801425) (by norm_num)
theorem B1711153 : Blo 1423531 1711153 := bbase (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) (by norm_num)
theorem B2137157 : Blo 1423531 2137157 := bbase (se 4 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 2137157 = 400717) (by norm_num)
theorem B2137181 : Blo 1423531 2137181 := bbase (se 3 (by rfl) ⟨400721, by rfl⟩ : syracuseStep 2137181 = 801443) (by norm_num)
theorem B4807781 : Blo 1423531 4807781 := bbase (se 4 (by rfl) ⟨450729, by rfl⟩ : syracuseStep 4807781 = 901459) (by norm_num)
theorem B2137205 : Blo 1423531 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B1711225 : Blo 1423531 1711225 := bbase (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) (by norm_num)
theorem B2137229 : Blo 1423531 2137229 := bbase (se 3 (by rfl) ⟨400730, by rfl⟩ : syracuseStep 2137229 = 801461) (by norm_num)
theorem B2137253 : Blo 1423531 2137253 := bbase (se 4 (by rfl) ⟨200367, by rfl⟩ : syracuseStep 2137253 = 400735) (by norm_num)
theorem B3603629 : Blo 1423531 3603629 := bbase (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) (by norm_num)
theorem B10820789 : Blo 1423531 10820789 := bbase (se 5 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 10820789 = 1014449) (by norm_num)
theorem B2137277 : Blo 1423531 2137277 := bbase (se 3 (by rfl) ⟨400739, by rfl⟩ : syracuseStep 2137277 = 801479) (by norm_num)
theorem B2137301 : Blo 1423531 2137301 := bbase (se 7 (by rfl) ⟨25046, by rfl⟩ : syracuseStep 2137301 = 50093) (by norm_num)
theorem B3849445 : Blo 1423531 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B2137325 : Blo 1423531 2137325 := bbase (se 3 (by rfl) ⟨400748, by rfl⟩ : syracuseStep 2137325 = 801497) (by norm_num)
theorem B2137349 : Blo 1423531 2137349 := bbase (se 4 (by rfl) ⟨200376, by rfl⟩ : syracuseStep 2137349 = 400753) (by norm_num)
theorem B2137373 : Blo 1423531 2137373 := bbase (se 3 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 2137373 = 801515) (by norm_num)
theorem B2137397 : Blo 1423531 2137397 := bbase (se 5 (by rfl) ⟨100190, by rfl⟩ : syracuseStep 2137397 = 200381) (by norm_num)
theorem B6495557 : Blo 1423531 6495557 := bbase (se 4 (by rfl) ⟨608958, by rfl⟩ : syracuseStep 6495557 = 1217917) (by norm_num)
theorem B2137421 : Blo 1423531 2137421 := bbase (se 3 (by rfl) ⟨400766, by rfl⟩ : syracuseStep 2137421 = 801533) (by norm_num)
theorem B2137445 : Blo 1423531 2137445 := bbase (se 4 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 2137445 = 400771) (by norm_num)
theorem B2137469 : Blo 1423531 2137469 := bbase (se 3 (by rfl) ⟨400775, by rfl⟩ : syracuseStep 2137469 = 801551) (by norm_num)
theorem B2137493 : Blo 1423531 2137493 := bbase (se 6 (by rfl) ⟨50097, by rfl⟩ : syracuseStep 2137493 = 100195) (by norm_num)
theorem B2137517 : Blo 1423531 2137517 := bbase (se 3 (by rfl) ⟨400784, by rfl⟩ : syracuseStep 2137517 = 801569) (by norm_num)
theorem B2137541 : Blo 1423531 2137541 := bbase (se 4 (by rfl) ⟨200394, by rfl⟩ : syracuseStep 2137541 = 400789) (by norm_num)
theorem B1801693 : Blo 1423531 1801693 := bbase (se 3 (by rfl) ⟨337817, by rfl⟩ : syracuseStep 1801693 = 675635) (by norm_num)
theorem B2137565 : Blo 1423531 2137565 := bbase (se 3 (by rfl) ⟨400793, by rfl⟩ : syracuseStep 2137565 = 801587) (by norm_num)
theorem B2702821 : Blo 1423531 2702821 := bbase (se 4 (by rfl) ⟨253389, by rfl⟩ : syracuseStep 2702821 = 506779) (by norm_num)
theorem B7216613 : Blo 1423531 7216613 := bbase (se 4 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 7216613 = 1353115) (by norm_num)
theorem B8109557 : Blo 1423531 8109557 := bbase (se 5 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 8109557 = 760271) (by norm_num)
theorem B2137589 : Blo 1423531 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B3603973 : Blo 1423531 3603973 := bbase (se 4 (by rfl) ⟨337872, by rfl⟩ : syracuseStep 3603973 = 675745) (by norm_num)
theorem B2137613 : Blo 1423531 2137613 := bbase (se 3 (by rfl) ⟨400802, by rfl⟩ : syracuseStep 2137613 = 801605) (by norm_num)
theorem B4808213 : Blo 1423531 4808213 := bbase (se 6 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 4808213 = 225385) (by norm_num)
theorem B2137637 : Blo 1423531 2137637 := bbase (se 4 (by rfl) ⟨200403, by rfl⟩ : syracuseStep 2137637 = 400807) (by norm_num)
theorem B2137661 : Blo 1423531 2137661 := bbase (se 3 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 2137661 = 801623) (by norm_num)
theorem B10813013 : Blo 1423531 10813013 := bbase (se 8 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 10813013 = 126715) (by norm_num)
theorem B2137685 : Blo 1423531 2137685 := bbase (se 8 (by rfl) ⟨12525, by rfl⟩ : syracuseStep 2137685 = 25051) (by norm_num)
theorem B2137709 : Blo 1423531 2137709 := bbase (se 3 (by rfl) ⟨400820, by rfl⟩ : syracuseStep 2137709 = 801641) (by norm_num)
theorem B2702965 : Blo 1423531 2702965 := bbase (se 5 (by rfl) ⟨126701, by rfl⟩ : syracuseStep 2702965 = 253403) (by norm_num)
theorem B3604085 : Blo 1423531 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B2137733 : Blo 1423531 2137733 := bbase (se 4 (by rfl) ⟨200412, by rfl⟩ : syracuseStep 2137733 = 400825) (by norm_num)
theorem B1801865 : Blo 1423531 1801865 := bbase (se 2 (by rfl) ⟨675699, by rfl⟩ : syracuseStep 1801865 = 1351399) (by norm_num)
theorem B2137757 : Blo 1423531 2137757 := bbase (se 3 (by rfl) ⟨400829, by rfl⟩ : syracuseStep 2137757 = 801659) (by norm_num)
theorem B2137781 : Blo 1423531 2137781 := bbase (se 5 (by rfl) ⟨100208, by rfl⟩ : syracuseStep 2137781 = 200417) (by norm_num)
theorem B1801921 : Blo 1423531 1801921 := bbase (se 2 (by rfl) ⟨675720, by rfl⟩ : syracuseStep 1801921 = 1351441) (by norm_num)
theorem B6938309 : Blo 1423531 6938309 := bbase (se 4 (by rfl) ⟨650466, by rfl⟩ : syracuseStep 6938309 = 1300933) (by norm_num)
theorem B2637517 : Blo 1423531 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B2137805 : Blo 1423531 2137805 := bbase (se 3 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 2137805 = 801677) (by norm_num)
theorem B7315157 : Blo 1423531 7315157 := bbase (se 7 (by rfl) ⟨85724, by rfl⟩ : syracuseStep 7315157 = 171449) (by norm_num)
theorem B2137829 : Blo 1423531 2137829 := bbase (se 4 (by rfl) ⟨200421, by rfl⟩ : syracuseStep 2137829 = 400843) (by norm_num)
theorem B2137853 : Blo 1423531 2137853 := bbase (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) (by norm_num)
theorem B4054789 : Blo 1423531 4054789 := bbase (se 4 (by rfl) ⟨380136, by rfl⟩ : syracuseStep 4054789 = 760273) (by norm_num)
theorem B2703125 : Blo 1423531 2703125 := bbase (se 6 (by rfl) ⟨63354, by rfl⟩ : syracuseStep 2703125 = 126709) (by norm_num)
theorem B1924885 : Blo 1423531 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B2137877 : Blo 1423531 2137877 := bbase (se 6 (by rfl) ⟨50106, by rfl⟩ : syracuseStep 2137877 = 100213) (by norm_num)
theorem B1802017 : Blo 1423531 1802017 := bbase (se 2 (by rfl) ⟨675756, by rfl⟩ : syracuseStep 1802017 = 1351513) (by norm_num)
theorem B2137901 : Blo 1423531 2137901 := bbase (se 3 (by rfl) ⟨400856, by rfl⟩ : syracuseStep 2137901 = 801713) (by norm_num)
theorem B3604277 : Blo 1423531 3604277 := bbase (se 5 (by rfl) ⟨168950, by rfl⟩ : syracuseStep 3604277 = 337901) (by norm_num)
theorem B2137925 : Blo 1423531 2137925 := bbase (se 4 (by rfl) ⟨200430, by rfl⟩ : syracuseStep 2137925 = 400861) (by norm_num)
theorem B2137949 : Blo 1423531 2137949 := bbase (se 3 (by rfl) ⟨400865, by rfl⟩ : syracuseStep 2137949 = 801731) (by norm_num)
theorem B2137973 : Blo 1423531 2137973 := bbase (se 5 (by rfl) ⟨100217, by rfl⟩ : syracuseStep 2137973 = 200435) (by norm_num)
theorem B7208837 : Blo 1423531 7208837 := bbase (se 4 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 7208837 = 1351657) (by norm_num)
theorem B2137997 : Blo 1423531 2137997 := bbase (se 3 (by rfl) ⟨400874, by rfl⟩ : syracuseStep 2137997 = 801749) (by norm_num)
theorem B3202973 : Blo 1423531 3202973 := bbase (se 3 (by rfl) ⟨600557, by rfl⟩ : syracuseStep 3202973 = 1201115) (by norm_num)
theorem B2703269 : Blo 1423531 2703269 := bbase (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) (by norm_num)
theorem B5775269 : Blo 1423531 5775269 := bbase (se 4 (by rfl) ⟨541431, by rfl⟩ : syracuseStep 5775269 = 1082863) (by norm_num)
theorem B2138021 : Blo 1423531 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B3424189 : Blo 1423531 3424189 := bbase (se 3 (by rfl) ⟨642035, by rfl⟩ : syracuseStep 3424189 = 1284071) (by norm_num)
theorem B2138045 : Blo 1423531 2138045 := bbase (se 3 (by rfl) ⟨400883, by rfl⟩ : syracuseStep 2138045 = 801767) (by norm_num)
theorem B4808645 : Blo 1423531 4808645 := bbase (se 4 (by rfl) ⟨450810, by rfl⟩ : syracuseStep 4808645 = 901621) (by norm_num)
theorem B1802189 : Blo 1423531 1802189 := bbase (se 3 (by rfl) ⟨337910, by rfl⟩ : syracuseStep 1802189 = 675821) (by norm_num)
theorem B2138069 : Blo 1423531 2138069 := bbase (se 7 (by rfl) ⟨25055, by rfl⟩ : syracuseStep 2138069 = 50111) (by norm_num)
theorem B3203045 : Blo 1423531 3203045 := bbase (se 4 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 3203045 = 600571) (by norm_num)
theorem B2195437 : Blo 1423531 2195437 := bbase (se 3 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 2195437 = 823289) (by norm_num)
theorem B2138093 : Blo 1423531 2138093 := bbase (se 3 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 2138093 = 801785) (by norm_num)
theorem B6168565 : Blo 1423531 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B1425411 : Blo 1423531 1425411 := bstep (se 1 (by rfl) ⟨1069058, by rfl⟩ : syracuseStep 1425411 = 2138117) B2138117
theorem B2138129 : Blo 1423531 2138129 := bstep (se 2 (by rfl) ⟨801798, by rfl⟩ : syracuseStep 2138129 = 1603597) B1603597
theorem B1425427 : Blo 1423531 1425427 := bstep (se 1 (by rfl) ⟨1069070, by rfl⟩ : syracuseStep 1425427 = 2138141) B2138141
theorem B2138147 : Blo 1423531 2138147 := bstep (se 1 (by rfl) ⟨1603610, by rfl⟩ : syracuseStep 2138147 = 3207221) B3207221
theorem B1425443 : Blo 1423531 1425443 := bstep (se 1 (by rfl) ⟨1069082, by rfl⟩ : syracuseStep 1425443 = 2138165) B2138165
theorem B4808753 : Blo 1423531 4808753 := bstep (se 2 (by rfl) ⟨1803282, by rfl⟩ : syracuseStep 4808753 = 3606565) B3606565
theorem B1425459 : Blo 1423531 1425459 := bstep (se 1 (by rfl) ⟨1069094, by rfl⟩ : syracuseStep 1425459 = 2138189) B2138189
theorem B2138177 : Blo 1423531 2138177 := bstep (se 2 (by rfl) ⟨801816, by rfl⟩ : syracuseStep 2138177 = 1603633) B1603633
theorem B1425475 : Blo 1423531 1425475 := bstep (se 1 (by rfl) ⟨1069106, by rfl⟩ : syracuseStep 1425475 = 2138213) B2138213
theorem B3203153 : Blo 1423531 3203153 := bstep (se 2 (by rfl) ⟨1201182, by rfl⟩ : syracuseStep 3203153 = 2402365) B2402365
theorem B2138195 : Blo 1423531 2138195 := bstep (se 1 (by rfl) ⟨1603646, by rfl⟩ : syracuseStep 2138195 = 3207293) B3207293
theorem B1425491 : Blo 1423531 1425491 := bstep (se 1 (by rfl) ⟨1069118, by rfl⟩ : syracuseStep 1425491 = 2138237) B2138237
theorem B3203171 : Blo 1423531 3203171 := bstep (se 1 (by rfl) ⟨2402378, by rfl⟩ : syracuseStep 3203171 = 4804757) B4804757
theorem B1425507 : Blo 1423531 1425507 := bstep (se 1 (by rfl) ⟨1069130, by rfl⟩ : syracuseStep 1425507 = 2138261) B2138261
theorem B2138225 : Blo 1423531 2138225 := bstep (se 2 (by rfl) ⟨801834, by rfl⟩ : syracuseStep 2138225 = 1603669) B1603669
theorem B1425523 : Blo 1423531 1425523 := bstep (se 1 (by rfl) ⟨1069142, by rfl⟩ : syracuseStep 1425523 = 2138285) B2138285
theorem B2138243 : Blo 1423531 2138243 := bstep (se 1 (by rfl) ⟨1603682, by rfl⟩ : syracuseStep 2138243 = 3207365) B3207365
theorem B2138273 : Blo 1423531 2138273 := bstep (se 2 (by rfl) ⟨801852, by rfl⟩ : syracuseStep 2138273 = 1603705) B1603705
theorem B2138291 : Blo 1423531 2138291 := bstep (se 1 (by rfl) ⟨1603718, by rfl⟩ : syracuseStep 2138291 = 3207437) B3207437
theorem B8110307 : Blo 1423531 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B13000931 : Blo 1423531 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B7414051 : Blo 1423531 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B9748835 : Blo 1423531 9748835 := bstep (se 1 (by rfl) ⟨7311626, by rfl⟩ : syracuseStep 9748835 = 14623253) B14623253
theorem B3203441 : Blo 1423531 3203441 := bstep (se 2 (by rfl) ⟨1201290, by rfl⟩ : syracuseStep 3203441 = 2402581) B2402581
theorem B3203459 : Blo 1423531 3203459 := bstep (se 1 (by rfl) ⟨2402594, by rfl⟩ : syracuseStep 3203459 = 4805189) B4805189
theorem B9249187 : Blo 1423531 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B5136803 : Blo 1423531 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B2703793 : Blo 1423531 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B6087089 : Blo 1423531 6087089 := bstep (se 2 (by rfl) ⟨2282658, by rfl⟩ : syracuseStep 6087089 = 4565317) B4565317
theorem B1802675 : Blo 1423531 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B3604945 : Blo 1423531 3604945 := bstep (se 2 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 3604945 = 2703709) B2703709
theorem B6840845 : Blo 1423531 6840845 := bstep (se 3 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 6840845 = 2565317) B2565317
theorem B7209485 : Blo 1423531 7209485 := bstep (se 3 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 7209485 = 2703557) B2703557
theorem B3424835 : Blo 1423531 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B3850829 : Blo 1423531 3850829 := bstep (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) B1444061
theorem B4809293 : Blo 1423531 4809293 := bstep (se 3 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 4809293 = 1803485) B1803485
theorem B4055633 : Blo 1423531 4055633 := bstep (se 2 (by rfl) ⟨1520862, by rfl⟩ : syracuseStep 4055633 = 3041725) B3041725
theorem B1925761 : Blo 1423531 1925761 := bstep (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) B1444321
theorem B4809347 : Blo 1423531 4809347 := bstep (se 1 (by rfl) ⟨3607010, by rfl⟩ : syracuseStep 4809347 = 7214021) B7214021
theorem B9126533 : Blo 1423531 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B3203729 : Blo 1423531 3203729 := bstep (se 2 (by rfl) ⟨1201398, by rfl⟩ : syracuseStep 3203729 = 2402797) B2402797
theorem B3203747 : Blo 1423531 3203747 := bstep (se 1 (by rfl) ⟨2402810, by rfl⟩ : syracuseStep 3203747 = 4805621) B4805621
theorem B5776049 : Blo 1423531 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B3605219 : Blo 1423531 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B11715299 : Blo 1423531 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B6841073 : Blo 1423531 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B4563715 : Blo 1423531 4563715 := bstep (se 1 (by rfl) ⟨3422786, by rfl⟩ : syracuseStep 4563715 = 6845573) B6845573
theorem B2704195 : Blo 1423531 2704195 := bstep (se 1 (by rfl) ⟨2028146, by rfl⟩ : syracuseStep 2704195 = 4056293) B4056293
theorem B2704241 : Blo 1423531 2704241 := bstep (se 2 (by rfl) ⟨1014090, by rfl⟩ : syracuseStep 2704241 = 2028181) B2028181
theorem B4809617 : Blo 1423531 4809617 := bstep (se 2 (by rfl) ⟨1803606, by rfl⟩ : syracuseStep 4809617 = 3607213) B3607213
theorem B3605411 : Blo 1423531 3605411 := bstep (se 1 (by rfl) ⟨2704058, by rfl⟩ : syracuseStep 3605411 = 5408117) B5408117
theorem B3204017 : Blo 1423531 3204017 := bstep (se 2 (by rfl) ⟨1201506, by rfl⟩ : syracuseStep 3204017 = 2403013) B2403013
theorem B3204035 : Blo 1423531 3204035 := bstep (se 1 (by rfl) ⟨2403026, by rfl⟩ : syracuseStep 3204035 = 4806053) B4806053
theorem B4563985 : Blo 1423531 4563985 := bstep (se 2 (by rfl) ⟨1711494, by rfl⟩ : syracuseStep 4563985 = 3422989) B3422989
theorem B5407843 : Blo 1423531 5407843 := bstep (se 1 (by rfl) ⟨4055882, by rfl⟩ : syracuseStep 5407843 = 8111765) B8111765
theorem B1803379 : Blo 1423531 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B2704529 : Blo 1423531 2704529 := bstep (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) B2028397
theorem B3204305 : Blo 1423531 3204305 := bstep (se 2 (by rfl) ⟨1201614, by rfl⟩ : syracuseStep 3204305 = 2403229) B2403229
theorem B1803475 : Blo 1423531 1803475 := bstep (se 1 (by rfl) ⟨1352606, by rfl⟩ : syracuseStep 1803475 = 2705213) B2705213
theorem B3204323 : Blo 1423531 3204323 := bstep (se 1 (by rfl) ⟨2403242, by rfl⟩ : syracuseStep 3204323 = 4806485) B4806485
theorem B4113713 : Blo 1423531 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B4056419 : Blo 1423531 4056419 := bstep (se 1 (by rfl) ⟨3042314, by rfl⟩ : syracuseStep 4056419 = 6084629) B6084629
theorem B3851651 : Blo 1423531 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B2196899 : Blo 1423531 2196899 := bstep (se 1 (by rfl) ⟨1647674, by rfl⟩ : syracuseStep 2196899 = 3295349) B3295349
theorem B4810157 : Blo 1423531 4810157 := bstep (se 3 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 4810157 = 1803809) B1803809
theorem B8660429 : Blo 1423531 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B4810211 : Blo 1423531 4810211 := bstep (se 1 (by rfl) ⟨3607658, by rfl⟩ : syracuseStep 4810211 = 7215317) B7215317
theorem B3204593 : Blo 1423531 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B3204611 : Blo 1423531 3204611 := bstep (se 1 (by rfl) ⟨2403458, by rfl⟩ : syracuseStep 3204611 = 4806917) B4806917
theorem B4056749 : Blo 1423531 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B1803971 : Blo 1423531 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B4056817 : Blo 1423531 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B4810481 : Blo 1423531 4810481 := bstep (se 2 (by rfl) ⟨1803930, by rfl⟩ : syracuseStep 4810481 = 3607861) B3607861
theorem B3204881 : Blo 1423531 3204881 := bstep (se 2 (by rfl) ⟨1201830, by rfl⟩ : syracuseStep 3204881 = 2403661) B2403661
theorem B3204899 : Blo 1423531 3204899 := bstep (se 1 (by rfl) ⟨2403674, by rfl⟩ : syracuseStep 3204899 = 4807349) B4807349
theorem B7702307 : Blo 1423531 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B3606353 : Blo 1423531 3606353 := bstep (se 2 (by rfl) ⟨1352382, by rfl⟩ : syracuseStep 3606353 = 2704765) B2704765
theorem B2705251 : Blo 1423531 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B3606403 : Blo 1423531 3606403 := bstep (se 1 (by rfl) ⟨2704802, by rfl⟩ : syracuseStep 3606403 = 5409605) B5409605
theorem B2402257 : Blo 1423531 2402257 := bstep (se 2 (by rfl) ⟨900846, by rfl⟩ : syracuseStep 2402257 = 1801693) B1801693
theorem B3655651 : Blo 1423531 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B2402291 : Blo 1423531 2402291 := bstep (se 1 (by rfl) ⟨1801718, by rfl⟩ : syracuseStep 2402291 = 3603437) B3603437
theorem B4057091 : Blo 1423531 4057091 := bstep (se 1 (by rfl) ⟨3042818, by rfl⟩ : syracuseStep 4057091 = 6085637) B6085637
theorem B3606545 : Blo 1423531 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B3205169 : Blo 1423531 3205169 := bstep (se 2 (by rfl) ⟨1201938, by rfl⟩ : syracuseStep 3205169 = 2403877) B2403877
theorem B3205187 : Blo 1423531 3205187 := bstep (se 1 (by rfl) ⟨2403890, by rfl⟩ : syracuseStep 3205187 = 4807781) B4807781
theorem B2402419 : Blo 1423531 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B2402561 : Blo 1423531 2402561 := bstep (se 2 (by rfl) ⟨900960, by rfl⟩ : syracuseStep 2402561 = 1801921) B1801921
theorem B4811021 : Blo 1423531 4811021 := bstep (se 3 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 4811021 = 1804133) B1804133
theorem B3516689 : Blo 1423531 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B2705699 : Blo 1423531 2705699 := bstep (se 1 (by rfl) ⟨2029274, by rfl⟩ : syracuseStep 2705699 = 4058549) B4058549
theorem B4811075 : Blo 1423531 4811075 := bstep (se 1 (by rfl) ⟨3608306, by rfl⟩ : syracuseStep 4811075 = 7216613) B7216613
theorem B3205457 : Blo 1423531 3205457 := bstep (se 2 (by rfl) ⟨1202046, by rfl⟩ : syracuseStep 3205457 = 2404093) B2404093
theorem B3205475 : Blo 1423531 3205475 := bstep (se 1 (by rfl) ⟨2404106, by rfl⟩ : syracuseStep 3205475 = 4808213) B4808213
theorem B2566513 : Blo 1423531 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B11553137 : Blo 1423531 11553137 := bstep (se 2 (by rfl) ⟨4332426, by rfl⟩ : syracuseStep 11553137 = 8664853) B8664853
theorem B2402689 : Blo 1423531 2402689 := bstep (se 2 (by rfl) ⟨901008, by rfl⟩ : syracuseStep 2402689 = 1802017) B1802017
theorem B2402723 : Blo 1423531 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B4876771 : Blo 1423531 4876771 := bstep (se 1 (by rfl) ⟨3657578, by rfl⟩ : syracuseStep 4876771 = 7315157) B7315157
theorem B2402851 : Blo 1423531 2402851 := bstep (se 1 (by rfl) ⟨1802138, by rfl⟩ : syracuseStep 2402851 = 3604277) B3604277
theorem B8784433 : Blo 1423531 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B2705987 : Blo 1423531 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B15608389 : Blo 1423531 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B4565585 : Blo 1423531 4565585 := bstep (se 2 (by rfl) ⟨1712094, by rfl⟩ : syracuseStep 4565585 = 3424189) B3424189
theorem B3205745 : Blo 1423531 3205745 := bstep (se 2 (by rfl) ⟨1202154, by rfl⟩ : syracuseStep 3205745 = 2404309) B2404309
theorem B3656305 : Blo 1423531 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B3205763 : Blo 1423531 3205763 := bstep (se 1 (by rfl) ⟨2404322, by rfl⟩ : syracuseStep 3205763 = 4808645) B4808645
theorem B2927249 : Blo 1423531 2927249 := bstep (se 2 (by rfl) ⟨1097718, by rfl⟩ : syracuseStep 2927249 = 2195437) B2195437
theorem B2402993 : Blo 1423531 2402993 := bstep (se 2 (by rfl) ⟨901122, by rfl⟩ : syracuseStep 2402993 = 1802245) B1802245
theorem B5778125 : Blo 1423531 5778125 := bstep (se 3 (by rfl) ⟨1083398, by rfl⟩ : syracuseStep 5778125 = 2166797) B2166797
theorem B12167921 : Blo 1423531 12167921 := bstep (se 2 (by rfl) ⟨4562970, by rfl⟩ : syracuseStep 12167921 = 9125941) B9125941
theorem B8227589 : Blo 1423531 8227589 := bstep (se 4 (by rfl) ⟨771336, by rfl⟩ : syracuseStep 8227589 = 1542673) B1542673
theorem B3042083 : Blo 1423531 3042083 := bstep (se 1 (by rfl) ⟨2281562, by rfl⟩ : syracuseStep 3042083 = 4563125) B4563125
theorem B2403121 : Blo 1423531 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B2886467 : Blo 1423531 2886467 := bstep (se 1 (by rfl) ⟨2164850, by rfl⟩ : syracuseStep 2886467 = 4329701) B4329701
theorem B4057933 : Blo 1423531 4057933 := bstep (se 3 (by rfl) ⟨760862, by rfl⟩ : syracuseStep 4057933 = 1521725) B1521725
theorem B2403155 : Blo 1423531 2403155 := bstep (se 1 (by rfl) ⟨1802366, by rfl⟩ : syracuseStep 2403155 = 3604733) B3604733
theorem B2280307 : Blo 1423531 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B3206033 : Blo 1423531 3206033 := bstep (se 2 (by rfl) ⟨1202262, by rfl⟩ : syracuseStep 3206033 = 2404525) B2404525
theorem B3206051 : Blo 1423531 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B4565933 : Blo 1423531 4565933 := bstep (se 3 (by rfl) ⟨856112, by rfl⟩ : syracuseStep 4565933 = 1712225) B1712225
theorem B2280403 : Blo 1423531 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B2403283 : Blo 1423531 2403283 := bstep (se 1 (by rfl) ⟨1802462, by rfl⟩ : syracuseStep 2403283 = 3604925) B3604925
theorem B4058093 : Blo 1423531 4058093 := bstep (se 3 (by rfl) ⟨760892, by rfl⟩ : syracuseStep 4058093 = 1521785) B1521785
theorem B3607537 : Blo 1423531 3607537 := bstep (se 2 (by rfl) ⟨1352826, by rfl⟩ : syracuseStep 3607537 = 2705653) B2705653
theorem B2165825 : Blo 1423531 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2403425 : Blo 1423531 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B2280563 : Blo 1423531 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B2567299 : Blo 1423531 2567299 := bstep (se 1 (by rfl) ⟨1925474, by rfl⟩ : syracuseStep 2567299 = 3850949) B3850949
theorem B6843533 : Blo 1423531 6843533 := bstep (se 3 (by rfl) ⟨1283162, by rfl⟩ : syracuseStep 6843533 = 2566325) B2566325
theorem B7703693 : Blo 1423531 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B4058275 : Blo 1423531 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B3206321 : Blo 1423531 3206321 := bstep (se 2 (by rfl) ⟨1202370, by rfl⟩ : syracuseStep 3206321 = 2404741) B2404741
theorem B3206339 : Blo 1423531 3206339 := bstep (se 1 (by rfl) ⟨2404754, by rfl⟩ : syracuseStep 3206339 = 4809509) B4809509
theorem B2403553 : Blo 1423531 2403553 := bstep (se 2 (by rfl) ⟨901332, by rfl⟩ : syracuseStep 2403553 = 1802665) B1802665
theorem B11259121 : Blo 1423531 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B3902705 : Blo 1423531 3902705 := bstep (se 2 (by rfl) ⟨1463514, by rfl⟩ : syracuseStep 3902705 = 2927029) B2927029
theorem B2403587 : Blo 1423531 2403587 := bstep (se 1 (by rfl) ⟨1802690, by rfl⟩ : syracuseStep 2403587 = 3605381) B3605381
theorem B3607811 : Blo 1423531 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B5410061 : Blo 1423531 5410061 := bstep (se 3 (by rfl) ⟨1014386, by rfl⟩ : syracuseStep 5410061 = 2028773) B2028773
theorem B14814533 : Blo 1423531 14814533 := bstep (se 4 (by rfl) ⟨1388862, by rfl⟩ : syracuseStep 14814533 = 2777725) B2777725
theorem B7212401 : Blo 1423531 7212401 := bstep (se 2 (by rfl) ⟨2704650, by rfl⟩ : syracuseStep 7212401 = 5409301) B5409301
theorem B2403715 : Blo 1423531 2403715 := bstep (se 1 (by rfl) ⟨1802786, by rfl⟩ : syracuseStep 2403715 = 3605573) B3605573
theorem B3608003 : Blo 1423531 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B3206609 : Blo 1423531 3206609 := bstep (se 2 (by rfl) ⟨1202478, by rfl⟩ : syracuseStep 3206609 = 2404957) B2404957
theorem B3206627 : Blo 1423531 3206627 := bstep (se 1 (by rfl) ⟨2404970, by rfl⟩ : syracuseStep 3206627 = 4809941) B4809941
theorem B17321485 : Blo 1423531 17321485 := bstep (se 3 (by rfl) ⟨3247778, by rfl⟩ : syracuseStep 17321485 = 6495557) B6495557
theorem B2403857 : Blo 1423531 2403857 := bstep (se 2 (by rfl) ⟨901446, by rfl⟩ : syracuseStep 2403857 = 1802893) B1802893
theorem B2166355 : Blo 1423531 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B3247715 : Blo 1423531 3247715 := bstep (se 1 (by rfl) ⟨2435786, by rfl⟩ : syracuseStep 3247715 = 4871573) B4871573
theorem B2403985 : Blo 1423531 2403985 := bstep (se 2 (by rfl) ⟨901494, by rfl⟩ : syracuseStep 2403985 = 1802989) B1802989
theorem B2404019 : Blo 1423531 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B6082253 : Blo 1423531 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B3206897 : Blo 1423531 3206897 := bstep (se 2 (by rfl) ⟨1202586, by rfl⟩ : syracuseStep 3206897 = 2405173) B2405173
theorem B3206915 : Blo 1423531 3206915 := bstep (se 1 (by rfl) ⟨2405186, by rfl⟩ : syracuseStep 3206915 = 4810373) B4810373
theorem B2027281 : Blo 1423531 2027281 := bstep (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) B1520461
theorem B2027315 : Blo 1423531 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B2404147 : Blo 1423531 2404147 := bstep (se 1 (by rfl) ⟨1803110, by rfl⟩ : syracuseStep 2404147 = 3606221) B3606221
theorem B4804433 : Blo 1423531 4804433 := bstep (se 2 (by rfl) ⟨1801662, by rfl⟩ : syracuseStep 4804433 = 3603325) B3603325
theorem B2404289 : Blo 1423531 2404289 := bstep (se 2 (by rfl) ⟨901608, by rfl⟩ : syracuseStep 2404289 = 1803217) B1803217
theorem B1601491 : Blo 1423531 1601491 := bstep (se 1 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 1601491 = 2402237) B2402237
theorem B3207185 : Blo 1423531 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B3207203 : Blo 1423531 3207203 := bstep (se 1 (by rfl) ⟨2405402, by rfl⟩ : syracuseStep 3207203 = 4810805) B4810805
theorem B9121841 : Blo 1423531 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B2281537 : Blo 1423531 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B2404417 : Blo 1423531 2404417 := bstep (se 2 (by rfl) ⟨901656, by rfl⟩ : syracuseStep 2404417 = 1803313) B1803313
theorem B9744461 : Blo 1423531 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B1601635 : Blo 1423531 1601635 := bstep (se 1 (by rfl) ⟨1201226, by rfl⟩ : syracuseStep 1601635 = 2402453) B2402453
theorem B2404451 : Blo 1423531 2404451 := bstep (se 1 (by rfl) ⟨1803338, by rfl⟩ : syracuseStep 2404451 = 3606677) B3606677
theorem B4624525 : Blo 1423531 4624525 := bstep (se 3 (by rfl) ⟨867098, by rfl⟩ : syracuseStep 4624525 = 1734197) B1734197
theorem B5779619 : Blo 1423531 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B2404579 : Blo 1423531 2404579 := bstep (se 1 (by rfl) ⟨1803434, by rfl⟩ : syracuseStep 2404579 = 3606869) B3606869
theorem B1601779 : Blo 1423531 1601779 := bstep (se 1 (by rfl) ⟨1201334, by rfl⟩ : syracuseStep 1601779 = 2402669) B2402669
theorem B5132593 : Blo 1423531 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B2027873 : Blo 1423531 2027873 := bstep (se 2 (by rfl) ⟨760452, by rfl⟩ : syracuseStep 2027873 = 1520905) B1520905
theorem B4804973 : Blo 1423531 4804973 := bstep (se 3 (by rfl) ⟨900932, by rfl⟩ : syracuseStep 4804973 = 1801865) B1801865
theorem B2404721 : Blo 1423531 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B1601923 : Blo 1423531 1601923 := bstep (se 1 (by rfl) ⟨1201442, by rfl⟩ : syracuseStep 1601923 = 2402885) B2402885
theorem B4805027 : Blo 1423531 4805027 := bstep (se 1 (by rfl) ⟨3603770, by rfl⟩ : syracuseStep 4805027 = 7207541) B7207541
theorem B9752995 : Blo 1423531 9752995 := bstep (se 1 (by rfl) ⟨7314746, by rfl⟩ : syracuseStep 9752995 = 14629493) B14629493
theorem B2027953 : Blo 1423531 2027953 := bstep (se 2 (by rfl) ⟨760482, by rfl⟩ : syracuseStep 2027953 = 1520965) B1520965
theorem B2404849 : Blo 1423531 2404849 := bstep (se 2 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 2404849 = 1803637) B1803637
theorem B18502157 : Blo 1423531 18502157 := bstep (se 3 (by rfl) ⟨3469154, by rfl⟩ : syracuseStep 18502157 = 6938309) B6938309
theorem B1602067 : Blo 1423531 1602067 := bstep (se 1 (by rfl) ⟨1201550, by rfl⟩ : syracuseStep 1602067 = 2403101) B2403101
theorem B2404883 : Blo 1423531 2404883 := bstep (se 1 (by rfl) ⟨1803662, by rfl⟩ : syracuseStep 2404883 = 3607325) B3607325
theorem B2405011 : Blo 1423531 2405011 := bstep (se 1 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 2405011 = 3607517) B3607517
theorem B1602211 : Blo 1423531 1602211 := bstep (se 1 (by rfl) ⟨1201658, by rfl⟩ : syracuseStep 1602211 = 2403317) B2403317
theorem B4805297 : Blo 1423531 4805297 := bstep (se 2 (by rfl) ⟨1801986, by rfl⟩ : syracuseStep 4805297 = 3603973) B3603973
theorem B10810097 : Blo 1423531 10810097 := bstep (se 2 (by rfl) ⟨4053786, by rfl⟩ : syracuseStep 10810097 = 8107573) B8107573
theorem B3420913 : Blo 1423531 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B3044099 : Blo 1423531 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B2405153 : Blo 1423531 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B7213859 : Blo 1423531 7213859 := bstep (se 1 (by rfl) ⟨5410394, by rfl⟩ : syracuseStep 7213859 = 10820789) B10820789
theorem B1602355 : Blo 1423531 1602355 := bstep (se 1 (by rfl) ⟨1201766, by rfl⟩ : syracuseStep 1602355 = 2403533) B2403533
theorem B2405281 : Blo 1423531 2405281 := bstep (se 2 (by rfl) ⟨901980, by rfl⟩ : syracuseStep 2405281 = 1803961) B1803961
theorem B1602499 : Blo 1423531 1602499 := bstep (se 1 (by rfl) ⟨1201874, by rfl⟩ : syracuseStep 1602499 = 2403749) B2403749
theorem B2405315 : Blo 1423531 2405315 := bstep (se 1 (by rfl) ⟨1803986, by rfl⟩ : syracuseStep 2405315 = 3607973) B3607973
theorem B6165517 : Blo 1423531 6165517 := bstep (se 3 (by rfl) ⟨1156034, by rfl⟩ : syracuseStep 6165517 = 2312069) B2312069
theorem B2405443 : Blo 1423531 2405443 := bstep (se 1 (by rfl) ⟨1804082, by rfl⟩ : syracuseStep 2405443 = 3608165) B3608165
theorem B1602643 : Blo 1423531 1602643 := bstep (se 1 (by rfl) ⟨1201982, by rfl⟩ : syracuseStep 1602643 = 2403965) B2403965
theorem B4109489 : Blo 1423531 4109489 := bstep (se 2 (by rfl) ⟨1541058, by rfl⟩ : syracuseStep 4109489 = 3082117) B3082117
theorem B2028739 : Blo 1423531 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B4805837 : Blo 1423531 4805837 := bstep (se 3 (by rfl) ⟨901094, by rfl⟩ : syracuseStep 4805837 = 1802189) B1802189
theorem B2438353 : Blo 1423531 2438353 := bstep (se 2 (by rfl) ⟨914382, by rfl⟩ : syracuseStep 2438353 = 1828765) B1828765
theorem B2405585 : Blo 1423531 2405585 := bstep (se 2 (by rfl) ⟨902094, by rfl⟩ : syracuseStep 2405585 = 1804189) B1804189
theorem B1602787 : Blo 1423531 1602787 := bstep (se 1 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 1602787 = 2404181) B2404181
theorem B2135297 : Blo 1423531 2135297 := bstep (se 2 (by rfl) ⟨800736, by rfl⟩ : syracuseStep 2135297 = 1601473) B1601473
theorem B4805891 : Blo 1423531 4805891 := bstep (se 1 (by rfl) ⟨3604418, by rfl⟩ : syracuseStep 4805891 = 7208837) B7208837
theorem B2135315 : Blo 1423531 2135315 := bstep (se 1 (by rfl) ⟨1601486, by rfl⟩ : syracuseStep 2135315 = 3202973) B3202973
theorem B2135345 : Blo 1423531 2135345 := bstep (se 2 (by rfl) ⟨800754, by rfl⟩ : syracuseStep 2135345 = 1601509) B1601509
theorem B2135363 : Blo 1423531 2135363 := bstep (se 1 (by rfl) ⟨1601522, by rfl⟩ : syracuseStep 2135363 = 3203045) B3203045
theorem B2135393 : Blo 1423531 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B15398257 : Blo 1423531 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B2135411 : Blo 1423531 2135411 := bstep (se 1 (by rfl) ⟨1601558, by rfl⟩ : syracuseStep 2135411 = 3203117) B3203117
theorem B1602931 : Blo 1423531 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B3249539 : Blo 1423531 3249539 := bstep (se 1 (by rfl) ⟨2437154, by rfl⟩ : syracuseStep 3249539 = 4874309) B4874309
theorem B2135441 : Blo 1423531 2135441 := bstep (se 2 (by rfl) ⟨800790, by rfl⟩ : syracuseStep 2135441 = 1601581) B1601581
theorem B6493603 : Blo 1423531 6493603 := bstep (se 1 (by rfl) ⟨4870202, by rfl⟩ : syracuseStep 6493603 = 9740405) B9740405
theorem B2135459 : Blo 1423531 2135459 := bstep (se 1 (by rfl) ⟨1601594, by rfl⟩ : syracuseStep 2135459 = 3203189) B3203189
theorem B2135489 : Blo 1423531 2135489 := bstep (se 2 (by rfl) ⟨800808, by rfl⟩ : syracuseStep 2135489 = 1601617) B1601617
theorem B2135507 : Blo 1423531 2135507 := bstep (se 1 (by rfl) ⟨1601630, by rfl⟩ : syracuseStep 2135507 = 3203261) B3203261
theorem B2135537 : Blo 1423531 2135537 := bstep (se 2 (by rfl) ⟨800826, by rfl⟩ : syracuseStep 2135537 = 1601653) B1601653
theorem B2135555 : Blo 1423531 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B1603075 : Blo 1423531 1603075 := bstep (se 1 (by rfl) ⟨1202306, by rfl⟩ : syracuseStep 1603075 = 2404613) B2404613
theorem B4806161 : Blo 1423531 4806161 := bstep (se 2 (by rfl) ⟨1802310, by rfl⟩ : syracuseStep 4806161 = 3604621) B3604621
theorem B2135585 : Blo 1423531 2135585 := bstep (se 2 (by rfl) ⟨800844, by rfl⟩ : syracuseStep 2135585 = 1601689) B1601689
theorem B2135603 : Blo 1423531 2135603 := bstep (se 1 (by rfl) ⟨1601702, by rfl⟩ : syracuseStep 2135603 = 3203405) B3203405
theorem B7214669 : Blo 1423531 7214669 := bstep (se 3 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 7214669 = 2705501) B2705501
theorem B2135633 : Blo 1423531 2135633 := bstep (se 2 (by rfl) ⟨800862, by rfl⟩ : syracuseStep 2135633 = 1601725) B1601725
theorem B2135651 : Blo 1423531 2135651 := bstep (se 1 (by rfl) ⟨1601738, by rfl⟩ : syracuseStep 2135651 = 3203477) B3203477
theorem B1758835 : Blo 1423531 1758835 := bstep (se 1 (by rfl) ⟨1319126, by rfl⟩ : syracuseStep 1758835 = 2638253) B2638253
theorem B2135681 : Blo 1423531 2135681 := bstep (se 2 (by rfl) ⟨800880, by rfl⟩ : syracuseStep 2135681 = 1601761) B1601761
theorem B2135699 : Blo 1423531 2135699 := bstep (se 1 (by rfl) ⟨1601774, by rfl⟩ : syracuseStep 2135699 = 3203549) B3203549
theorem B1603219 : Blo 1423531 1603219 := bstep (se 1 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 1603219 = 2404829) B2404829
theorem B2029217 : Blo 1423531 2029217 := bstep (se 2 (by rfl) ⟨760956, by rfl⟩ : syracuseStep 2029217 = 1521913) B1521913
theorem B2135729 : Blo 1423531 2135729 := bstep (se 2 (by rfl) ⟨800898, by rfl⟩ : syracuseStep 2135729 = 1601797) B1601797
theorem B2135747 : Blo 1423531 2135747 := bstep (se 1 (by rfl) ⟨1601810, by rfl⟩ : syracuseStep 2135747 = 3203621) B3203621
theorem B2283203 : Blo 1423531 2283203 := bstep (se 1 (by rfl) ⟨1712402, by rfl⟩ : syracuseStep 2283203 = 3424805) B3424805
theorem B2135777 : Blo 1423531 2135777 := bstep (se 2 (by rfl) ⟨800916, by rfl⟩ : syracuseStep 2135777 = 1601833) B1601833
theorem B2135795 : Blo 1423531 2135795 := bstep (se 1 (by rfl) ⟨1601846, by rfl⟩ : syracuseStep 2135795 = 3203693) B3203693
theorem B2135825 : Blo 1423531 2135825 := bstep (se 2 (by rfl) ⟨800934, by rfl⟩ : syracuseStep 2135825 = 1601869) B1601869
theorem B2029331 : Blo 1423531 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B2135843 : Blo 1423531 2135843 := bstep (se 1 (by rfl) ⟨1601882, by rfl⟩ : syracuseStep 2135843 = 3203765) B3203765
theorem B1603363 : Blo 1423531 1603363 := bstep (se 1 (by rfl) ⟨1202522, by rfl⟩ : syracuseStep 1603363 = 2405045) B2405045
theorem B2135873 : Blo 1423531 2135873 := bstep (se 2 (by rfl) ⟨800952, by rfl⟩ : syracuseStep 2135873 = 1601905) B1601905
theorem B2283331 : Blo 1423531 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B2135891 : Blo 1423531 2135891 := bstep (se 1 (by rfl) ⟨1601918, by rfl⟩ : syracuseStep 2135891 = 3203837) B3203837
theorem B2029411 : Blo 1423531 2029411 := bstep (se 1 (by rfl) ⟨1522058, by rfl⟩ : syracuseStep 2029411 = 3044117) B3044117
theorem B2135921 : Blo 1423531 2135921 := bstep (se 2 (by rfl) ⟨800970, by rfl⟩ : syracuseStep 2135921 = 1601941) B1601941
theorem B2135939 : Blo 1423531 2135939 := bstep (se 1 (by rfl) ⟨1601954, by rfl⟩ : syracuseStep 2135939 = 3203909) B3203909
theorem B2283395 : Blo 1423531 2283395 := bstep (se 1 (by rfl) ⟨1712546, by rfl⟩ : syracuseStep 2283395 = 3425093) B3425093
theorem B2135969 : Blo 1423531 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B2135987 : Blo 1423531 2135987 := bstep (se 1 (by rfl) ⟨1601990, by rfl⟩ : syracuseStep 2135987 = 3203981) B3203981
theorem B1603507 : Blo 1423531 1603507 := bstep (se 1 (by rfl) ⟨1202630, by rfl⟩ : syracuseStep 1603507 = 2405261) B2405261
theorem B2136017 : Blo 1423531 2136017 := bstep (se 2 (by rfl) ⟨801006, by rfl⟩ : syracuseStep 2136017 = 1602013) B1602013
theorem B2136035 : Blo 1423531 2136035 := bstep (se 1 (by rfl) ⟨1602026, by rfl⟩ : syracuseStep 2136035 = 3204053) B3204053
theorem B2136065 : Blo 1423531 2136065 := bstep (se 2 (by rfl) ⟨801024, by rfl⟩ : syracuseStep 2136065 = 1602049) B1602049
theorem B2136083 : Blo 1423531 2136083 := bstep (se 1 (by rfl) ⟨1602062, by rfl⟩ : syracuseStep 2136083 = 3204125) B3204125
theorem B4806701 : Blo 1423531 4806701 := bstep (se 3 (by rfl) ⟨901256, by rfl⟩ : syracuseStep 4806701 = 1802513) B1802513
theorem B2136113 : Blo 1423531 2136113 := bstep (se 2 (by rfl) ⟨801042, by rfl⟩ : syracuseStep 2136113 = 1602085) B1602085
theorem B2136131 : Blo 1423531 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B1603651 : Blo 1423531 1603651 := bstep (se 1 (by rfl) ⟨1202738, by rfl⟩ : syracuseStep 1603651 = 2405477) B2405477
theorem B2136161 : Blo 1423531 2136161 := bstep (se 2 (by rfl) ⟨801060, by rfl⟩ : syracuseStep 2136161 = 1602121) B1602121
theorem B4806755 : Blo 1423531 4806755 := bstep (se 1 (by rfl) ⟨3605066, by rfl⟩ : syracuseStep 4806755 = 7210133) B7210133
theorem B2136179 : Blo 1423531 2136179 := bstep (se 1 (by rfl) ⟨1602134, by rfl⟩ : syracuseStep 2136179 = 3204269) B3204269
theorem B2889859 : Blo 1423531 2889859 := bstep (se 1 (by rfl) ⟨2167394, by rfl⟩ : syracuseStep 2889859 = 4334789) B4334789
theorem B2136209 : Blo 1423531 2136209 := bstep (se 2 (by rfl) ⟨801078, by rfl⟩ : syracuseStep 2136209 = 1602157) B1602157
theorem B2136227 : Blo 1423531 2136227 := bstep (se 1 (by rfl) ⟨1602170, by rfl⟩ : syracuseStep 2136227 = 3204341) B3204341
theorem B6166691 : Blo 1423531 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B1423539 : Blo 1423531 1423539 := bstep (se 1 (by rfl) ⟨1067654, by rfl⟩ : syracuseStep 1423539 = 2135309) B2135309
theorem B2136257 : Blo 1423531 2136257 := bstep (se 2 (by rfl) ⟨801096, by rfl⟩ : syracuseStep 2136257 = 1602193) B1602193
theorem B1423555 : Blo 1423531 1423555 := bstep (se 1 (by rfl) ⟨1067666, by rfl⟩ : syracuseStep 1423555 = 2135333) B2135333
theorem B3471569 : Blo 1423531 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B1423571 : Blo 1423531 1423571 := bstep (se 1 (by rfl) ⟨1067678, by rfl⟩ : syracuseStep 1423571 = 2135357) B2135357
theorem B2136275 : Blo 1423531 2136275 := bstep (se 1 (by rfl) ⟨1602206, by rfl⟩ : syracuseStep 2136275 = 3204413) B3204413
theorem B1521875 : Blo 1423531 1521875 := bstep (se 1 (by rfl) ⟨1141406, by rfl⟩ : syracuseStep 1521875 = 2282813) B2282813
theorem B1423587 : Blo 1423531 1423587 := bstep (se 1 (by rfl) ⟨1067690, by rfl⟩ : syracuseStep 1423587 = 2135381) B2135381
theorem B2136305 : Blo 1423531 2136305 := bstep (se 2 (by rfl) ⟨801114, by rfl⟩ : syracuseStep 2136305 = 1602229) B1602229
theorem B1423603 : Blo 1423531 1423603 := bstep (se 1 (by rfl) ⟨1067702, by rfl⟩ : syracuseStep 1423603 = 2135405) B2135405
theorem B1423619 : Blo 1423531 1423619 := bstep (se 1 (by rfl) ⟨1067714, by rfl⟩ : syracuseStep 1423619 = 2135429) B2135429
theorem B2136323 : Blo 1423531 2136323 := bstep (se 1 (by rfl) ⟨1602242, by rfl⟩ : syracuseStep 2136323 = 3204485) B3204485
theorem B1423635 : Blo 1423531 1423635 := bstep (se 1 (by rfl) ⟨1067726, by rfl⟩ : syracuseStep 1423635 = 2135453) B2135453
theorem B2136353 : Blo 1423531 2136353 := bstep (se 2 (by rfl) ⟨801132, by rfl⟩ : syracuseStep 2136353 = 1602265) B1602265
theorem B1423651 : Blo 1423531 1423651 := bstep (se 1 (by rfl) ⟨1067738, by rfl⟩ : syracuseStep 1423651 = 2135477) B2135477
theorem B7207217 : Blo 1423531 7207217 := bstep (se 2 (by rfl) ⟨2702706, by rfl⟩ : syracuseStep 7207217 = 5405413) B5405413
theorem B1423667 : Blo 1423531 1423667 := bstep (se 1 (by rfl) ⟨1067750, by rfl⟩ : syracuseStep 1423667 = 2135501) B2135501
theorem B2136371 : Blo 1423531 2136371 := bstep (se 1 (by rfl) ⟨1602278, by rfl⟩ : syracuseStep 2136371 = 3204557) B3204557
theorem B1423683 : Blo 1423531 1423683 := bstep (se 1 (by rfl) ⟨1067762, by rfl⟩ : syracuseStep 1423683 = 2135525) B2135525
theorem B4331843 : Blo 1423531 4331843 := bstep (se 1 (by rfl) ⟨3248882, by rfl⟩ : syracuseStep 4331843 = 6497765) B6497765
theorem B2136401 : Blo 1423531 2136401 := bstep (se 2 (by rfl) ⟨801150, by rfl⟩ : syracuseStep 2136401 = 1602301) B1602301
theorem B1423699 : Blo 1423531 1423699 := bstep (se 1 (by rfl) ⟨1067774, by rfl⟩ : syracuseStep 1423699 = 2135549) B2135549
theorem B1423715 : Blo 1423531 1423715 := bstep (se 1 (by rfl) ⟨1067786, by rfl⟩ : syracuseStep 1423715 = 2135573) B2135573
theorem B2136419 : Blo 1423531 2136419 := bstep (se 1 (by rfl) ⟨1602314, by rfl⟩ : syracuseStep 2136419 = 3204629) B3204629
theorem B4807025 : Blo 1423531 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B1423731 : Blo 1423531 1423731 := bstep (se 1 (by rfl) ⟨1067798, by rfl⟩ : syracuseStep 1423731 = 2135597) B2135597
theorem B2136449 : Blo 1423531 2136449 := bstep (se 2 (by rfl) ⟨801168, by rfl⟩ : syracuseStep 2136449 = 1602337) B1602337
theorem B1423747 : Blo 1423531 1423747 := bstep (se 1 (by rfl) ⟨1067810, by rfl⟩ : syracuseStep 1423747 = 2135621) B2135621
theorem B59251085 : Blo 1423531 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B1423763 : Blo 1423531 1423763 := bstep (se 1 (by rfl) ⟨1067822, by rfl⟩ : syracuseStep 1423763 = 2135645) B2135645
theorem B2136467 : Blo 1423531 2136467 := bstep (se 1 (by rfl) ⟨1602350, by rfl⟩ : syracuseStep 2136467 = 3204701) B3204701
theorem B1423779 : Blo 1423531 1423779 := bstep (se 1 (by rfl) ⟨1067834, by rfl⟩ : syracuseStep 1423779 = 2135669) B2135669
theorem B4331939 : Blo 1423531 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B2136497 : Blo 1423531 2136497 := bstep (se 2 (by rfl) ⟨801186, by rfl⟩ : syracuseStep 2136497 = 1602373) B1602373
theorem B1423795 : Blo 1423531 1423795 := bstep (se 1 (by rfl) ⟨1067846, by rfl⟩ : syracuseStep 1423795 = 2135693) B2135693
theorem B1423811 : Blo 1423531 1423811 := bstep (se 1 (by rfl) ⟨1067858, by rfl⟩ : syracuseStep 1423811 = 2135717) B2135717
theorem B2136515 : Blo 1423531 2136515 := bstep (se 1 (by rfl) ⟨1602386, by rfl⟩ : syracuseStep 2136515 = 3204773) B3204773
theorem B9124301 : Blo 1423531 9124301 := bstep (se 3 (by rfl) ⟨1710806, by rfl⟩ : syracuseStep 9124301 = 3421613) B3421613
theorem B1423827 : Blo 1423531 1423827 := bstep (se 1 (by rfl) ⟨1067870, by rfl⟩ : syracuseStep 1423827 = 2135741) B2135741
theorem B2136545 : Blo 1423531 2136545 := bstep (se 2 (by rfl) ⟨801204, by rfl⟩ : syracuseStep 2136545 = 1602409) B1602409
theorem B1423843 : Blo 1423531 1423843 := bstep (se 1 (by rfl) ⟨1067882, by rfl⟩ : syracuseStep 1423843 = 2135765) B2135765
theorem B1423859 : Blo 1423531 1423859 := bstep (se 1 (by rfl) ⟨1067894, by rfl⟩ : syracuseStep 1423859 = 2135789) B2135789
theorem B2136563 : Blo 1423531 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B1423875 : Blo 1423531 1423875 := bstep (se 1 (by rfl) ⟨1067906, by rfl⟩ : syracuseStep 1423875 = 2135813) B2135813
theorem B2136593 : Blo 1423531 2136593 := bstep (se 2 (by rfl) ⟨801222, by rfl⟩ : syracuseStep 2136593 = 1602445) B1602445
theorem B1423891 : Blo 1423531 1423891 := bstep (se 1 (by rfl) ⟨1067918, by rfl⟩ : syracuseStep 1423891 = 2135837) B2135837
theorem B1423907 : Blo 1423531 1423907 := bstep (se 1 (by rfl) ⟨1067930, by rfl⟩ : syracuseStep 1423907 = 2135861) B2135861
theorem B2136611 : Blo 1423531 2136611 := bstep (se 1 (by rfl) ⟨1602458, by rfl⟩ : syracuseStep 2136611 = 3204917) B3204917
theorem B3848753 : Blo 1423531 3848753 := bstep (se 2 (by rfl) ⟨1443282, by rfl⟩ : syracuseStep 3848753 = 2886565) B2886565
theorem B1423923 : Blo 1423531 1423923 := bstep (se 1 (by rfl) ⟨1067942, by rfl⟩ : syracuseStep 1423923 = 2135885) B2135885
theorem B2136641 : Blo 1423531 2136641 := bstep (se 2 (by rfl) ⟨801240, by rfl⟩ : syracuseStep 2136641 = 1602481) B1602481
theorem B1423939 : Blo 1423531 1423939 := bstep (se 1 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 1423939 = 2135909) B2135909
theorem B4938317 : Blo 1423531 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B1423955 : Blo 1423531 1423955 := bstep (se 1 (by rfl) ⟨1067966, by rfl⟩ : syracuseStep 1423955 = 2135933) B2135933
theorem B2136659 : Blo 1423531 2136659 := bstep (se 1 (by rfl) ⟨1602494, by rfl⟩ : syracuseStep 2136659 = 3204989) B3204989
theorem B1423971 : Blo 1423531 1423971 := bstep (se 1 (by rfl) ⟨1067978, by rfl⟩ : syracuseStep 1423971 = 2135957) B2135957
theorem B2136689 : Blo 1423531 2136689 := bstep (se 2 (by rfl) ⟨801258, by rfl⟩ : syracuseStep 2136689 = 1602517) B1602517
theorem B1423987 : Blo 1423531 1423987 := bstep (se 1 (by rfl) ⟨1067990, by rfl⟩ : syracuseStep 1423987 = 2135981) B2135981
theorem B1424003 : Blo 1423531 1424003 := bstep (se 1 (by rfl) ⟨1068002, by rfl⟩ : syracuseStep 1424003 = 2136005) B2136005
theorem B2136707 : Blo 1423531 2136707 := bstep (se 1 (by rfl) ⟨1602530, by rfl⟩ : syracuseStep 2136707 = 3205061) B3205061
theorem B1424019 : Blo 1423531 1424019 := bstep (se 1 (by rfl) ⟨1068014, by rfl⟩ : syracuseStep 1424019 = 2136029) B2136029
theorem B2136737 : Blo 1423531 2136737 := bstep (se 2 (by rfl) ⟨801276, by rfl⟩ : syracuseStep 2136737 = 1602553) B1602553
theorem B1424035 : Blo 1423531 1424035 := bstep (se 1 (by rfl) ⟨1068026, by rfl⟩ : syracuseStep 1424035 = 2136053) B2136053
theorem B1424051 : Blo 1423531 1424051 := bstep (se 1 (by rfl) ⟨1068038, by rfl⟩ : syracuseStep 1424051 = 2136077) B2136077
theorem B2136755 : Blo 1423531 2136755 := bstep (se 1 (by rfl) ⟨1602566, by rfl⟩ : syracuseStep 2136755 = 3205133) B3205133
theorem B1424067 : Blo 1423531 1424067 := bstep (se 1 (by rfl) ⟨1068050, by rfl⟩ : syracuseStep 1424067 = 2136101) B2136101
theorem B2136785 : Blo 1423531 2136785 := bstep (se 2 (by rfl) ⟨801294, by rfl⟩ : syracuseStep 2136785 = 1602589) B1602589
theorem B1424083 : Blo 1423531 1424083 := bstep (se 1 (by rfl) ⟨1068062, by rfl⟩ : syracuseStep 1424083 = 2136125) B2136125
theorem B1424099 : Blo 1423531 1424099 := bstep (se 1 (by rfl) ⟨1068074, by rfl⟩ : syracuseStep 1424099 = 2136149) B2136149
theorem B2136803 : Blo 1423531 2136803 := bstep (se 1 (by rfl) ⟨1602602, by rfl⟩ : syracuseStep 2136803 = 3205205) B3205205
theorem B1424115 : Blo 1423531 1424115 := bstep (se 1 (by rfl) ⟨1068086, by rfl⟩ : syracuseStep 1424115 = 2136173) B2136173
theorem B2136833 : Blo 1423531 2136833 := bstep (se 2 (by rfl) ⟨801312, by rfl⟩ : syracuseStep 2136833 = 1602625) B1602625
theorem B1424131 : Blo 1423531 1424131 := bstep (se 1 (by rfl) ⟨1068098, by rfl⟩ : syracuseStep 1424131 = 2136197) B2136197
theorem B1424147 : Blo 1423531 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B2136851 : Blo 1423531 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B71219989 : Blo 1423531 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B1424163 : Blo 1423531 1424163 := bstep (se 1 (by rfl) ⟨1068122, by rfl⟩ : syracuseStep 1424163 = 2136245) B2136245
theorem B8108849 : Blo 1423531 8108849 := bstep (se 2 (by rfl) ⟨3040818, by rfl⟩ : syracuseStep 8108849 = 6081637) B6081637
theorem B2136881 : Blo 1423531 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B1424179 : Blo 1423531 1424179 := bstep (se 1 (by rfl) ⟨1068134, by rfl⟩ : syracuseStep 1424179 = 2136269) B2136269
theorem B1424195 : Blo 1423531 1424195 := bstep (se 1 (by rfl) ⟨1068146, by rfl⟩ : syracuseStep 1424195 = 2136293) B2136293
theorem B2136899 : Blo 1423531 2136899 := bstep (se 1 (by rfl) ⟨1602674, by rfl⟩ : syracuseStep 2136899 = 3205349) B3205349
theorem B1424211 : Blo 1423531 1424211 := bstep (se 1 (by rfl) ⟨1068158, by rfl⟩ : syracuseStep 1424211 = 2136317) B2136317
theorem B2136929 : Blo 1423531 2136929 := bstep (se 2 (by rfl) ⟨801348, by rfl⟩ : syracuseStep 2136929 = 1602697) B1602697
theorem B1424227 : Blo 1423531 1424227 := bstep (se 1 (by rfl) ⟨1068170, by rfl⟩ : syracuseStep 1424227 = 2136341) B2136341
theorem B1424243 : Blo 1423531 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B2136947 : Blo 1423531 2136947 := bstep (se 1 (by rfl) ⟨1602710, by rfl⟩ : syracuseStep 2136947 = 3205421) B3205421
theorem B1424259 : Blo 1423531 1424259 := bstep (se 1 (by rfl) ⟨1068194, by rfl⟩ : syracuseStep 1424259 = 2136389) B2136389
theorem B4053901 : Blo 1423531 4053901 := bstep (se 3 (by rfl) ⟨760106, by rfl⟩ : syracuseStep 4053901 = 1520213) B1520213
theorem B4807565 : Blo 1423531 4807565 := bstep (se 3 (by rfl) ⟨901418, by rfl⟩ : syracuseStep 4807565 = 1802837) B1802837
theorem B2136977 : Blo 1423531 2136977 := bstep (se 2 (by rfl) ⟨801366, by rfl⟩ : syracuseStep 2136977 = 1602733) B1602733
theorem B1424275 : Blo 1423531 1424275 := bstep (se 1 (by rfl) ⟨1068206, by rfl⟩ : syracuseStep 1424275 = 2136413) B2136413
theorem B1424291 : Blo 1423531 1424291 := bstep (se 1 (by rfl) ⟨1068218, by rfl⟩ : syracuseStep 1424291 = 2136437) B2136437
theorem B2136995 : Blo 1423531 2136995 := bstep (se 1 (by rfl) ⟨1602746, by rfl⟩ : syracuseStep 2136995 = 3205493) B3205493
theorem B1424307 : Blo 1423531 1424307 := bstep (se 1 (by rfl) ⟨1068230, by rfl⟩ : syracuseStep 1424307 = 2136461) B2136461
theorem B2137025 : Blo 1423531 2137025 := bstep (se 2 (by rfl) ⟨801384, by rfl⟩ : syracuseStep 2137025 = 1602769) B1602769
theorem B1424323 : Blo 1423531 1424323 := bstep (se 1 (by rfl) ⟨1068242, by rfl⟩ : syracuseStep 1424323 = 2136485) B2136485
theorem B4807619 : Blo 1423531 4807619 := bstep (se 1 (by rfl) ⟨3605714, by rfl⟩ : syracuseStep 4807619 = 7211429) B7211429
theorem B1424339 : Blo 1423531 1424339 := bstep (se 1 (by rfl) ⟨1068254, by rfl⟩ : syracuseStep 1424339 = 2136509) B2136509
theorem B2137043 : Blo 1423531 2137043 := bstep (se 1 (by rfl) ⟨1602782, by rfl⟩ : syracuseStep 2137043 = 3205565) B3205565
theorem B1424355 : Blo 1423531 1424355 := bstep (se 1 (by rfl) ⟨1068266, by rfl⟩ : syracuseStep 1424355 = 2136533) B2136533
theorem B2137073 : Blo 1423531 2137073 := bstep (se 2 (by rfl) ⟨801402, by rfl⟩ : syracuseStep 2137073 = 1602805) B1602805
theorem B1424371 : Blo 1423531 1424371 := bstep (se 1 (by rfl) ⟨1068278, by rfl⟩ : syracuseStep 1424371 = 2136557) B2136557
theorem B1424387 : Blo 1423531 1424387 := bstep (se 1 (by rfl) ⟨1068290, by rfl⟩ : syracuseStep 1424387 = 2136581) B2136581
theorem B2137091 : Blo 1423531 2137091 := bstep (se 1 (by rfl) ⟨1602818, by rfl⟩ : syracuseStep 2137091 = 3205637) B3205637
theorem B1424403 : Blo 1423531 1424403 := bstep (se 1 (by rfl) ⟨1068302, by rfl⟩ : syracuseStep 1424403 = 2136605) B2136605
theorem B2137121 : Blo 1423531 2137121 := bstep (se 2 (by rfl) ⟨801420, by rfl⟩ : syracuseStep 2137121 = 1602841) B1602841
theorem B1424419 : Blo 1423531 1424419 := bstep (se 1 (by rfl) ⟨1068314, by rfl⟩ : syracuseStep 1424419 = 2136629) B2136629
theorem B1424435 : Blo 1423531 1424435 := bstep (se 1 (by rfl) ⟨1068326, by rfl⟩ : syracuseStep 1424435 = 2136653) B2136653
theorem B61602869 : Blo 1423531 61602869 := bstep (se 5 (by rfl) ⟨2887634, by rfl⟩ : syracuseStep 61602869 = 5775269) B5775269
theorem B2137139 : Blo 1423531 2137139 := bstep (se 1 (by rfl) ⟨1602854, by rfl⟩ : syracuseStep 2137139 = 3205709) B3205709
theorem B1424451 : Blo 1423531 1424451 := bstep (se 1 (by rfl) ⟨1068338, by rfl⟩ : syracuseStep 1424451 = 2136677) B2136677
theorem B2137169 : Blo 1423531 2137169 := bstep (se 2 (by rfl) ⟨801438, by rfl⟩ : syracuseStep 2137169 = 1602877) B1602877
theorem B1424467 : Blo 1423531 1424467 := bstep (se 1 (by rfl) ⟨1068350, by rfl⟩ : syracuseStep 1424467 = 2136701) B2136701
theorem B1924193 : Blo 1423531 1924193 := bstep (se 2 (by rfl) ⟨721572, by rfl⟩ : syracuseStep 1924193 = 1443145) B1443145
theorem B1424483 : Blo 1423531 1424483 := bstep (se 1 (by rfl) ⟨1068362, by rfl⟩ : syracuseStep 1424483 = 2136725) B2136725
theorem B2137187 : Blo 1423531 2137187 := bstep (se 1 (by rfl) ⟨1602890, by rfl⟩ : syracuseStep 2137187 = 3205781) B3205781
theorem B1424499 : Blo 1423531 1424499 := bstep (se 1 (by rfl) ⟨1068374, by rfl⟩ : syracuseStep 1424499 = 2136749) B2136749
theorem B2137217 : Blo 1423531 2137217 := bstep (se 2 (by rfl) ⟨801456, by rfl⟩ : syracuseStep 2137217 = 1602913) B1602913
theorem B1424515 : Blo 1423531 1424515 := bstep (se 1 (by rfl) ⟨1068386, by rfl⟩ : syracuseStep 1424515 = 2136773) B2136773
theorem B1424531 : Blo 1423531 1424531 := bstep (se 1 (by rfl) ⟨1068398, by rfl⟩ : syracuseStep 1424531 = 2136797) B2136797
theorem B2137235 : Blo 1423531 2137235 := bstep (se 1 (by rfl) ⟨1602926, by rfl⟩ : syracuseStep 2137235 = 3205853) B3205853
theorem B1424547 : Blo 1423531 1424547 := bstep (se 1 (by rfl) ⟨1068410, by rfl⟩ : syracuseStep 1424547 = 2136821) B2136821
theorem B2137265 : Blo 1423531 2137265 := bstep (se 2 (by rfl) ⟨801474, by rfl⟩ : syracuseStep 2137265 = 1602949) B1602949
theorem B1424563 : Blo 1423531 1424563 := bstep (se 1 (by rfl) ⟨1068422, by rfl⟩ : syracuseStep 1424563 = 2136845) B2136845
theorem B1424579 : Blo 1423531 1424579 := bstep (se 1 (by rfl) ⟨1068434, by rfl⟩ : syracuseStep 1424579 = 2136869) B2136869
theorem B2137283 : Blo 1423531 2137283 := bstep (se 1 (by rfl) ⟨1602962, by rfl⟩ : syracuseStep 2137283 = 3205925) B3205925
theorem B4807889 : Blo 1423531 4807889 := bstep (se 2 (by rfl) ⟨1802958, by rfl⟩ : syracuseStep 4807889 = 3605917) B3605917
theorem B1424595 : Blo 1423531 1424595 := bstep (se 1 (by rfl) ⟨1068446, by rfl⟩ : syracuseStep 1424595 = 2136893) B2136893
theorem B2137313 : Blo 1423531 2137313 := bstep (se 2 (by rfl) ⟨801492, by rfl⟩ : syracuseStep 2137313 = 1602985) B1602985
theorem B1424611 : Blo 1423531 1424611 := bstep (se 1 (by rfl) ⟨1068458, by rfl⟩ : syracuseStep 1424611 = 2136917) B2136917
theorem B1424627 : Blo 1423531 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B2137331 : Blo 1423531 2137331 := bstep (se 1 (by rfl) ⟨1602998, by rfl⟩ : syracuseStep 2137331 = 3205997) B3205997
theorem B1924355 : Blo 1423531 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1424643 : Blo 1423531 1424643 := bstep (se 1 (by rfl) ⟨1068482, by rfl⟩ : syracuseStep 1424643 = 2136965) B2136965
theorem B2137361 : Blo 1423531 2137361 := bstep (se 2 (by rfl) ⟨801510, by rfl⟩ : syracuseStep 2137361 = 1603021) B1603021
theorem B1711379 : Blo 1423531 1711379 := bstep (se 1 (by rfl) ⟨1283534, by rfl⟩ : syracuseStep 1711379 = 2567069) B2567069
theorem B1424659 : Blo 1423531 1424659 := bstep (se 1 (by rfl) ⟨1068494, by rfl⟩ : syracuseStep 1424659 = 2136989) B2136989
theorem B1424675 : Blo 1423531 1424675 := bstep (se 1 (by rfl) ⟨1068506, by rfl⟩ : syracuseStep 1424675 = 2137013) B2137013
theorem B2137379 : Blo 1423531 2137379 := bstep (se 1 (by rfl) ⟨1603034, by rfl⟩ : syracuseStep 2137379 = 3206069) B3206069
theorem B3603761 : Blo 1423531 3603761 := bstep (se 2 (by rfl) ⟨1351410, by rfl⟩ : syracuseStep 3603761 = 2702821) B2702821
theorem B1424691 : Blo 1423531 1424691 := bstep (se 1 (by rfl) ⟨1068518, by rfl⟩ : syracuseStep 1424691 = 2137037) B2137037
theorem B2137409 : Blo 1423531 2137409 := bstep (se 2 (by rfl) ⟨801528, by rfl⟩ : syracuseStep 2137409 = 1603057) B1603057
theorem B1424707 : Blo 1423531 1424707 := bstep (se 1 (by rfl) ⟨1068530, by rfl⟩ : syracuseStep 1424707 = 2137061) B2137061
theorem B1424723 : Blo 1423531 1424723 := bstep (se 1 (by rfl) ⟨1068542, by rfl⟩ : syracuseStep 1424723 = 2137085) B2137085
theorem B2137427 : Blo 1423531 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B3603811 : Blo 1423531 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B1424739 : Blo 1423531 1424739 := bstep (se 1 (by rfl) ⟨1068554, by rfl⟩ : syracuseStep 1424739 = 2137109) B2137109
theorem B2137457 : Blo 1423531 2137457 := bstep (se 2 (by rfl) ⟨801546, by rfl⟩ : syracuseStep 2137457 = 1603093) B1603093
theorem B1424755 : Blo 1423531 1424755 := bstep (se 1 (by rfl) ⟨1068566, by rfl⟩ : syracuseStep 1424755 = 2137133) B2137133
theorem B1424771 : Blo 1423531 1424771 := bstep (se 1 (by rfl) ⟨1068578, by rfl⟩ : syracuseStep 1424771 = 2137157) B2137157
theorem B2137475 : Blo 1423531 2137475 := bstep (se 1 (by rfl) ⟨1603106, by rfl⟩ : syracuseStep 2137475 = 3206213) B3206213
theorem B2702737 : Blo 1423531 2702737 := bstep (se 2 (by rfl) ⟨1013526, by rfl⟩ : syracuseStep 2702737 = 2027053) B2027053
theorem B1424787 : Blo 1423531 1424787 := bstep (se 1 (by rfl) ⟨1068590, by rfl⟩ : syracuseStep 1424787 = 2137181) B2137181
theorem B2137505 : Blo 1423531 2137505 := bstep (se 2 (by rfl) ⟨801564, by rfl⟩ : syracuseStep 2137505 = 1603129) B1603129
theorem B1424803 : Blo 1423531 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1424819 : Blo 1423531 1424819 := bstep (se 1 (by rfl) ⟨1068614, by rfl⟩ : syracuseStep 1424819 = 2137229) B2137229
theorem B2137523 : Blo 1423531 2137523 := bstep (se 1 (by rfl) ⟨1603142, by rfl⟩ : syracuseStep 2137523 = 3206285) B3206285
theorem B1424835 : Blo 1423531 1424835 := bstep (se 1 (by rfl) ⟨1068626, by rfl⟩ : syracuseStep 1424835 = 2137253) B2137253
theorem B2137553 : Blo 1423531 2137553 := bstep (se 2 (by rfl) ⟨801582, by rfl⟩ : syracuseStep 2137553 = 1603165) B1603165
theorem B1424851 : Blo 1423531 1424851 := bstep (se 1 (by rfl) ⟨1068638, by rfl⟩ : syracuseStep 1424851 = 2137277) B2137277
theorem B1424867 : Blo 1423531 1424867 := bstep (se 1 (by rfl) ⟨1068650, by rfl⟩ : syracuseStep 1424867 = 2137301) B2137301
theorem B2137571 : Blo 1423531 2137571 := bstep (se 1 (by rfl) ⟨1603178, by rfl⟩ : syracuseStep 2137571 = 3206357) B3206357
theorem B3603953 : Blo 1423531 3603953 := bstep (se 2 (by rfl) ⟨1351482, by rfl⟩ : syracuseStep 3603953 = 2702965) B2702965
theorem B1424883 : Blo 1423531 1424883 := bstep (se 1 (by rfl) ⟨1068662, by rfl⟩ : syracuseStep 1424883 = 2137325) B2137325
theorem B2137601 : Blo 1423531 2137601 := bstep (se 2 (by rfl) ⟨801600, by rfl⟩ : syracuseStep 2137601 = 1603201) B1603201
theorem B1424899 : Blo 1423531 1424899 := bstep (se 1 (by rfl) ⟨1068674, by rfl⟩ : syracuseStep 1424899 = 2137349) B2137349
theorem B1424915 : Blo 1423531 1424915 := bstep (se 1 (by rfl) ⟨1068686, by rfl⟩ : syracuseStep 1424915 = 2137373) B2137373
theorem B2137619 : Blo 1423531 2137619 := bstep (se 1 (by rfl) ⟨1603214, by rfl⟩ : syracuseStep 2137619 = 3206429) B3206429
theorem B1424931 : Blo 1423531 1424931 := bstep (se 1 (by rfl) ⟨1068698, by rfl⟩ : syracuseStep 1424931 = 2137397) B2137397
theorem B2137649 : Blo 1423531 2137649 := bstep (se 2 (by rfl) ⟨801618, by rfl⟩ : syracuseStep 2137649 = 1603237) B1603237
theorem B1424947 : Blo 1423531 1424947 := bstep (se 1 (by rfl) ⟨1068710, by rfl⟩ : syracuseStep 1424947 = 2137421) B2137421
theorem B1424963 : Blo 1423531 1424963 := bstep (se 1 (by rfl) ⟨1068722, by rfl⟩ : syracuseStep 1424963 = 2137445) B2137445
theorem B2137667 : Blo 1423531 2137667 := bstep (se 1 (by rfl) ⟨1603250, by rfl⟩ : syracuseStep 2137667 = 3206501) B3206501
theorem B1424979 : Blo 1423531 1424979 := bstep (se 1 (by rfl) ⟨1068734, by rfl⟩ : syracuseStep 1424979 = 2137469) B2137469
theorem B2137697 : Blo 1423531 2137697 := bstep (se 2 (by rfl) ⟨801636, by rfl⟩ : syracuseStep 2137697 = 1603273) B1603273
theorem B1424995 : Blo 1423531 1424995 := bstep (se 1 (by rfl) ⟨1068746, by rfl⟩ : syracuseStep 1424995 = 2137493) B2137493
theorem B1425011 : Blo 1423531 1425011 := bstep (se 1 (by rfl) ⟨1068758, by rfl⟩ : syracuseStep 1425011 = 2137517) B2137517
theorem B2137715 : Blo 1423531 2137715 := bstep (se 1 (by rfl) ⟨1603286, by rfl⟩ : syracuseStep 2137715 = 3206573) B3206573
theorem B1425027 : Blo 1423531 1425027 := bstep (se 1 (by rfl) ⟨1068770, by rfl⟩ : syracuseStep 1425027 = 2137541) B2137541
theorem B6086285 : Blo 1423531 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B2137745 : Blo 1423531 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1425043 : Blo 1423531 1425043 := bstep (se 1 (by rfl) ⟨1068782, by rfl⟩ : syracuseStep 1425043 = 2137565) B2137565
theorem B5406371 : Blo 1423531 5406371 := bstep (se 1 (by rfl) ⟨4054778, by rfl⟩ : syracuseStep 5406371 = 8109557) B8109557
theorem B1425059 : Blo 1423531 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B2137763 : Blo 1423531 2137763 := bstep (se 1 (by rfl) ⟨1603322, by rfl⟩ : syracuseStep 2137763 = 3206645) B3206645
theorem B4628141 : Blo 1423531 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B5406385 : Blo 1423531 5406385 := bstep (se 2 (by rfl) ⟨2027394, by rfl⟩ : syracuseStep 5406385 = 4054789) B4054789
theorem B1425075 : Blo 1423531 1425075 := bstep (se 1 (by rfl) ⟨1068806, by rfl⟩ : syracuseStep 1425075 = 2137613) B2137613
theorem B1425091 : Blo 1423531 1425091 := bstep (se 1 (by rfl) ⟨1068818, by rfl⟩ : syracuseStep 1425091 = 2137637) B2137637
theorem B2137793 : Blo 1423531 2137793 := bstep (se 2 (by rfl) ⟨801672, by rfl⟩ : syracuseStep 2137793 = 1603345) B1603345
theorem B1425107 : Blo 1423531 1425107 := bstep (se 1 (by rfl) ⟨1068830, by rfl⟩ : syracuseStep 1425107 = 2137661) B2137661
theorem B2137811 : Blo 1423531 2137811 := bstep (se 1 (by rfl) ⟨1603358, by rfl⟩ : syracuseStep 2137811 = 3206717) B3206717
theorem B7208675 : Blo 1423531 7208675 := bstep (se 1 (by rfl) ⟨5406506, by rfl⟩ : syracuseStep 7208675 = 10813013) B10813013
theorem B1425123 : Blo 1423531 1425123 := bstep (se 1 (by rfl) ⟨1068842, by rfl⟩ : syracuseStep 1425123 = 2137685) B2137685
theorem B4808429 : Blo 1423531 4808429 := bstep (se 3 (by rfl) ⟨901580, by rfl⟩ : syracuseStep 4808429 = 1803161) B1803161
theorem B2137841 : Blo 1423531 2137841 := bstep (se 2 (by rfl) ⟨801690, by rfl⟩ : syracuseStep 2137841 = 1603381) B1603381
theorem B1425139 : Blo 1423531 1425139 := bstep (se 1 (by rfl) ⟨1068854, by rfl⟩ : syracuseStep 1425139 = 2137709) B2137709
theorem B1425155 : Blo 1423531 1425155 := bstep (se 1 (by rfl) ⟨1068866, by rfl⟩ : syracuseStep 1425155 = 2137733) B2137733
theorem B2137859 : Blo 1423531 2137859 := bstep (se 1 (by rfl) ⟨1603394, by rfl⟩ : syracuseStep 2137859 = 3206789) B3206789
theorem B1425171 : Blo 1423531 1425171 := bstep (se 1 (by rfl) ⟨1068878, by rfl⟩ : syracuseStep 1425171 = 2137757) B2137757
theorem B2137889 : Blo 1423531 2137889 := bstep (se 2 (by rfl) ⟨801708, by rfl⟩ : syracuseStep 2137889 = 1603417) B1603417
theorem B4808483 : Blo 1423531 4808483 := bstep (se 1 (by rfl) ⟨3606362, by rfl⟩ : syracuseStep 4808483 = 7212725) B7212725
theorem B1425187 : Blo 1423531 1425187 := bstep (se 1 (by rfl) ⟨1068890, by rfl⟩ : syracuseStep 1425187 = 2137781) B2137781
theorem B1425203 : Blo 1423531 1425203 := bstep (se 1 (by rfl) ⟨1068902, by rfl⟩ : syracuseStep 1425203 = 2137805) B2137805
theorem B2137907 : Blo 1423531 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B1425219 : Blo 1423531 1425219 := bstep (se 1 (by rfl) ⟨1068914, by rfl⟩ : syracuseStep 1425219 = 2137829) B2137829
theorem B2137937 : Blo 1423531 2137937 := bstep (se 2 (by rfl) ⟨801726, by rfl⟩ : syracuseStep 2137937 = 1603453) B1603453
theorem B1425235 : Blo 1423531 1425235 := bstep (se 1 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 1425235 = 2137853) B2137853
theorem B1802083 : Blo 1423531 1802083 := bstep (se 1 (by rfl) ⟨1351562, by rfl⟩ : syracuseStep 1802083 = 2703125) B2703125
theorem B1425251 : Blo 1423531 1425251 := bstep (se 1 (by rfl) ⟨1068938, by rfl⟩ : syracuseStep 1425251 = 2137877) B2137877
theorem B2137955 : Blo 1423531 2137955 := bstep (se 1 (by rfl) ⟨1603466, by rfl⟩ : syracuseStep 2137955 = 3206933) B3206933
theorem B8666993 : Blo 1423531 8666993 := bstep (se 2 (by rfl) ⟨3250122, by rfl⟩ : syracuseStep 8666993 = 6500245) B6500245
theorem B1425267 : Blo 1423531 1425267 := bstep (se 1 (by rfl) ⟨1068950, by rfl⟩ : syracuseStep 1425267 = 2137901) B2137901
theorem B2137985 : Blo 1423531 2137985 := bstep (se 2 (by rfl) ⟨801744, by rfl⟩ : syracuseStep 2137985 = 1603489) B1603489
theorem B1425283 : Blo 1423531 1425283 := bstep (se 1 (by rfl) ⟨1068962, by rfl⟩ : syracuseStep 1425283 = 2137925) B2137925
theorem B1425299 : Blo 1423531 1425299 := bstep (se 1 (by rfl) ⟨1068974, by rfl⟩ : syracuseStep 1425299 = 2137949) B2137949
theorem B2138003 : Blo 1423531 2138003 := bstep (se 1 (by rfl) ⟨1603502, by rfl⟩ : syracuseStep 2138003 = 3207005) B3207005
theorem B1425315 : Blo 1423531 1425315 := bstep (se 1 (by rfl) ⟨1068986, by rfl⟩ : syracuseStep 1425315 = 2137973) B2137973
theorem B4054961 : Blo 1423531 4054961 := bstep (se 2 (by rfl) ⟨1520610, by rfl⟩ : syracuseStep 4054961 = 3041221) B3041221
theorem B2138033 : Blo 1423531 2138033 := bstep (se 2 (by rfl) ⟨801762, by rfl⟩ : syracuseStep 2138033 = 1603525) B1603525
theorem B1425331 : Blo 1423531 1425331 := bstep (se 1 (by rfl) ⟨1068998, by rfl⟩ : syracuseStep 1425331 = 2137997) B2137997
theorem B1802179 : Blo 1423531 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B1425347 : Blo 1423531 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B2138051 : Blo 1423531 2138051 := bstep (se 1 (by rfl) ⟨1603538, by rfl⟩ : syracuseStep 2138051 = 3207077) B3207077
theorem B1425363 : Blo 1423531 1425363 := bstep (se 1 (by rfl) ⟨1069022, by rfl⟩ : syracuseStep 1425363 = 2138045) B2138045
theorem B2138081 : Blo 1423531 2138081 := bstep (se 2 (by rfl) ⟨801780, by rfl⟩ : syracuseStep 2138081 = 1603561) B1603561
theorem B6086627 : Blo 1423531 6086627 := bstep (se 1 (by rfl) ⟨4564970, by rfl⟩ : syracuseStep 6086627 = 9129941) B9129941
theorem B1425379 : Blo 1423531 1425379 := bstep (se 1 (by rfl) ⟨1069034, by rfl⟩ : syracuseStep 1425379 = 2138069) B2138069
theorem B8224753 : Blo 1423531 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B1425395 : Blo 1423531 1425395 := bstep (se 1 (by rfl) ⟨1069046, by rfl⟩ : syracuseStep 1425395 = 2138093) B2138093
theorem B2138099 : Blo 1423531 2138099 := bstep (se 1 (by rfl) ⟨1603574, by rfl⟩ : syracuseStep 2138099 = 3207149) B3207149
theorem B2138123 : Blo 1423531 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B1425419 : Blo 1423531 1425419 := bstep (se 1 (by rfl) ⟨1069064, by rfl⟩ : syracuseStep 1425419 = 2138129) B2138129
theorem B2138135 : Blo 1423531 2138135 := bstep (se 1 (by rfl) ⟨1603601, by rfl⟩ : syracuseStep 2138135 = 3207203) B3207203
theorem B1425431 : Blo 1423531 1425431 := bstep (se 1 (by rfl) ⟨1069073, by rfl⟩ : syracuseStep 1425431 = 2138147) B2138147
theorem B1425451 : Blo 1423531 1425451 := bstep (se 1 (by rfl) ⟨1069088, by rfl⟩ : syracuseStep 1425451 = 2138177) B2138177
theorem B6496307 : Blo 1423531 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B1425463 : Blo 1423531 1425463 := bstep (se 1 (by rfl) ⟨1069097, by rfl⟩ : syracuseStep 1425463 = 2138195) B2138195
theorem B1425483 : Blo 1423531 1425483 := bstep (se 1 (by rfl) ⟨1069112, by rfl⟩ : syracuseStep 1425483 = 2138225) B2138225
theorem B1425495 : Blo 1423531 1425495 := bstep (se 1 (by rfl) ⟨1069121, by rfl⟩ : syracuseStep 1425495 = 2138243) B2138243
theorem B2138201 : Blo 1423531 2138201 := bstep (se 2 (by rfl) ⟨801825, by rfl⟩ : syracuseStep 2138201 = 1603651) B1603651
theorem B1425515 : Blo 1423531 1425515 := bstep (se 1 (by rfl) ⟨1069136, by rfl⟩ : syracuseStep 1425515 = 2138273) B2138273
theorem B1425527 : Blo 1423531 1425527 := bstep (se 1 (by rfl) ⟨1069145, by rfl⟩ : syracuseStep 1425527 = 2138291) B2138291
theorem B5406871 : Blo 1423531 5406871 := bstep (se 1 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 5406871 = 8110307) B8110307
theorem B8667287 : Blo 1423531 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B3203225 : Blo 1423531 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B5775533 : Blo 1423531 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B3203315 : Blo 1423531 3203315 := bstep (se 1 (by rfl) ⟨2402486, by rfl⟩ : syracuseStep 3203315 = 4804973) B4804973
theorem B46850309 : Blo 1423531 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B3203351 : Blo 1423531 3203351 := bstep (se 1 (by rfl) ⟨2402513, by rfl⟩ : syracuseStep 3203351 = 4805027) B4805027
theorem B3424535 : Blo 1423531 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B2703755 : Blo 1423531 2703755 := bstep (se 1 (by rfl) ⟨2027816, by rfl⟩ : syracuseStep 2703755 = 4055633) B4055633
theorem B3203531 : Blo 1423531 3203531 := bstep (se 1 (by rfl) ⟨2402648, by rfl⟩ : syracuseStep 3203531 = 4805297) B4805297
theorem B3203585 : Blo 1423531 3203585 := bstep (se 2 (by rfl) ⟨1201344, by rfl⟩ : syracuseStep 3203585 = 2402689) B2402689
theorem B4809239 : Blo 1423531 4809239 := bstep (se 1 (by rfl) ⟨3606929, by rfl⟩ : syracuseStep 4809239 = 7213859) B7213859
theorem B3605057 : Blo 1423531 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B2703937 : Blo 1423531 2703937 := bstep (se 2 (by rfl) ⟨1013976, by rfl⟩ : syracuseStep 2703937 = 2027953) B2027953
theorem B1802827 : Blo 1423531 1802827 := bstep (se 1 (by rfl) ⟨1352120, by rfl⟩ : syracuseStep 1802827 = 2704241) B2704241
theorem B3203801 : Blo 1423531 3203801 := bstep (se 2 (by rfl) ⟨1201425, by rfl⟩ : syracuseStep 3203801 = 2402851) B2402851
theorem B4563677 : Blo 1423531 4563677 := bstep (se 3 (by rfl) ⟨855689, by rfl⟩ : syracuseStep 4563677 = 1711379) B1711379
theorem B10969901 : Blo 1423531 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B3203891 : Blo 1423531 3203891 := bstep (se 1 (by rfl) ⟨2402918, by rfl⟩ : syracuseStep 3203891 = 4805837) B4805837
theorem B4875073 : Blo 1423531 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B3203927 : Blo 1423531 3203927 := bstep (se 1 (by rfl) ⟨2402945, by rfl⟩ : syracuseStep 3203927 = 4805891) B4805891
theorem B2704279 : Blo 1423531 2704279 := bstep (se 1 (by rfl) ⟨2028209, by rfl⟩ : syracuseStep 2704279 = 4056419) B4056419
theorem B5407661 : Blo 1423531 5407661 := bstep (se 3 (by rfl) ⟨1013936, by rfl⟩ : syracuseStep 5407661 = 2027873) B2027873
theorem B3204107 : Blo 1423531 3204107 := bstep (se 1 (by rfl) ⟨2403080, by rfl⟩ : syracuseStep 3204107 = 4806161) B4806161
theorem B4809779 : Blo 1423531 4809779 := bstep (se 1 (by rfl) ⟨3607334, by rfl⟩ : syracuseStep 4809779 = 7214669) B7214669
theorem B3204161 : Blo 1423531 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B3605593 : Blo 1423531 3605593 := bstep (se 2 (by rfl) ⟨1352097, by rfl⟩ : syracuseStep 3605593 = 2704195) B2704195
theorem B11551837 : Blo 1423531 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B2704499 : Blo 1423531 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B3040409 : Blo 1423531 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B3204377 : Blo 1423531 3204377 := bstep (se 2 (by rfl) ⟨1201641, by rfl⟩ : syracuseStep 3204377 = 2403283) B2403283
theorem B4810049 : Blo 1423531 4810049 := bstep (se 2 (by rfl) ⟨1803768, by rfl⟩ : syracuseStep 4810049 = 3607537) B3607537
theorem B2704727 : Blo 1423531 2704727 := bstep (se 1 (by rfl) ⟨2028545, by rfl⟩ : syracuseStep 2704727 = 4057091) B4057091
theorem B3204467 : Blo 1423531 3204467 := bstep (se 1 (by rfl) ⟨2403350, by rfl⟩ : syracuseStep 3204467 = 4806701) B4806701
theorem B3204503 : Blo 1423531 3204503 := bstep (se 1 (by rfl) ⟨2403377, by rfl⟩ : syracuseStep 3204503 = 4806755) B4806755
theorem B7210457 : Blo 1423531 7210457 := bstep (se 2 (by rfl) ⟨2703921, by rfl⟩ : syracuseStep 7210457 = 5407843) B5407843
theorem B2344459 : Blo 1423531 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B1803799 : Blo 1423531 1803799 := bstep (se 1 (by rfl) ⟨1352849, by rfl⟩ : syracuseStep 1803799 = 2705699) B2705699
theorem B12174893 : Blo 1423531 12174893 := bstep (se 3 (by rfl) ⟨2282792, by rfl⟩ : syracuseStep 12174893 = 4565585) B4565585
theorem B3204683 : Blo 1423531 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B7702091 : Blo 1423531 7702091 := bstep (se 1 (by rfl) ⟨5776568, by rfl⟩ : syracuseStep 7702091 = 11553137) B11553137
theorem B2704985 : Blo 1423531 2704985 := bstep (se 2 (by rfl) ⟨1014369, by rfl⟩ : syracuseStep 2704985 = 2028739) B2028739
theorem B3204737 : Blo 1423531 3204737 := bstep (se 2 (by rfl) ⟨1201776, by rfl⟩ : syracuseStep 3204737 = 2403553) B2403553
theorem B1951499 : Blo 1423531 1951499 := bstep (se 1 (by rfl) ⟨1463624, by rfl⟩ : syracuseStep 1951499 = 2927249) B2927249
theorem B15402797 : Blo 1423531 15402797 := bstep (se 3 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 15402797 = 5776049) B5776049
theorem B3852083 : Blo 1423531 3852083 := bstep (se 1 (by rfl) ⟨2889062, by rfl⟩ : syracuseStep 3852083 = 5778125) B5778125
theorem B20531009 : Blo 1423531 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B8111947 : Blo 1423531 8111947 := bstep (se 1 (by rfl) ⟨6083960, by rfl⟩ : syracuseStep 8111947 = 12167921) B12167921
theorem B3204953 : Blo 1423531 3204953 := bstep (se 2 (by rfl) ⟨1201857, by rfl⟩ : syracuseStep 3204953 = 2403715) B2403715
theorem B4810589 : Blo 1423531 4810589 := bstep (se 3 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 4810589 = 1803971) B1803971
theorem B3205043 : Blo 1423531 3205043 := bstep (se 1 (by rfl) ⟨2403782, by rfl⟩ : syracuseStep 3205043 = 4807565) B4807565
theorem B3205079 : Blo 1423531 3205079 := bstep (se 1 (by rfl) ⟨2403809, by rfl⟩ : syracuseStep 3205079 = 4807619) B4807619
theorem B2705395 : Blo 1423531 2705395 := bstep (se 1 (by rfl) ⟨2029046, by rfl⟩ : syracuseStep 2705395 = 4058093) B4058093
theorem B21940237 : Blo 1423531 21940237 := bstep (se 3 (by rfl) ⟨4113794, by rfl⟩ : syracuseStep 21940237 = 8227589) B8227589
theorem B23095313 : Blo 1423531 23095313 := bstep (se 2 (by rfl) ⟨8660742, by rfl⟩ : syracuseStep 23095313 = 17321485) B17321485
theorem B41068579 : Blo 1423531 41068579 := bstep (se 1 (by rfl) ⟨30801434, by rfl⟩ : syracuseStep 41068579 = 61602869) B61602869
theorem B8112221 : Blo 1423531 8112221 := bstep (se 3 (by rfl) ⟨1521041, by rfl⟩ : syracuseStep 8112221 = 3042083) B3042083
theorem B3205259 : Blo 1423531 3205259 := bstep (se 1 (by rfl) ⟨2403944, by rfl⟩ : syracuseStep 3205259 = 4807889) B4807889
theorem B2345113 : Blo 1423531 2345113 := bstep (se 2 (by rfl) ⟨879417, by rfl⟩ : syracuseStep 2345113 = 1758835) B1758835
theorem B3606707 : Blo 1423531 3606707 := bstep (se 1 (by rfl) ⟨2705030, by rfl⟩ : syracuseStep 3606707 = 5410061) B5410061
theorem B3205313 : Blo 1423531 3205313 := bstep (se 2 (by rfl) ⟨1201992, by rfl⟩ : syracuseStep 3205313 = 2403985) B2403985
theorem B2402507 : Blo 1423531 2402507 := bstep (se 1 (by rfl) ⟨1801880, by rfl⟩ : syracuseStep 2402507 = 3603761) B3603761
theorem B5409089 : Blo 1423531 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B2402635 : Blo 1423531 2402635 := bstep (se 1 (by rfl) ⟨1801976, by rfl⟩ : syracuseStep 2402635 = 3603953) B3603953
theorem B6089053 : Blo 1423531 6089053 := bstep (se 3 (by rfl) ⟨1141697, by rfl⟩ : syracuseStep 6089053 = 2283395) B2283395
theorem B2165143 : Blo 1423531 2165143 := bstep (se 1 (by rfl) ⟨1623857, by rfl⟩ : syracuseStep 2165143 = 3247715) B3247715
theorem B3205529 : Blo 1423531 3205529 := bstep (se 2 (by rfl) ⟨1202073, by rfl⟩ : syracuseStep 3205529 = 2404147) B2404147
theorem B4057523 : Blo 1423531 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B2402777 : Blo 1423531 2402777 := bstep (se 2 (by rfl) ⟨901041, by rfl⟩ : syracuseStep 2402777 = 1802083) B1802083
theorem B3607001 : Blo 1423531 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B2705881 : Blo 1423531 2705881 := bstep (se 2 (by rfl) ⟨1014705, by rfl⟩ : syracuseStep 2705881 = 2029411) B2029411
theorem B3205619 : Blo 1423531 3205619 := bstep (se 1 (by rfl) ⟨2404214, by rfl⟩ : syracuseStep 3205619 = 4808429) B4808429
theorem B3205655 : Blo 1423531 3205655 := bstep (se 1 (by rfl) ⟨2404241, by rfl⟩ : syracuseStep 3205655 = 4808483) B4808483
theorem B5777995 : Blo 1423531 5777995 := bstep (se 1 (by rfl) ⟨4333496, by rfl⟩ : syracuseStep 5777995 = 8666993) B8666993
theorem B2402905 : Blo 1423531 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B4057751 : Blo 1423531 4057751 := bstep (se 1 (by rfl) ⟨3043313, by rfl⟩ : syracuseStep 4057751 = 6086627) B6086627
theorem B6081227 : Blo 1423531 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B3205835 : Blo 1423531 3205835 := bstep (se 1 (by rfl) ⟨2404376, by rfl⟩ : syracuseStep 3205835 = 4808753) B4808753
theorem B3042049 : Blo 1423531 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B3205889 : Blo 1423531 3205889 := bstep (se 2 (by rfl) ⟨1202208, by rfl⟩ : syracuseStep 3205889 = 2404417) B2404417
theorem B3853079 : Blo 1423531 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B3853145 : Blo 1423531 3853145 := bstep (se 2 (by rfl) ⟨1444929, by rfl⟩ : syracuseStep 3853145 = 2889859) B2889859
theorem B6499223 : Blo 1423531 6499223 := bstep (se 1 (by rfl) ⟨4874417, by rfl⟩ : syracuseStep 6499223 = 9748835) B9748835
theorem B5131181 : Blo 1423531 5131181 := bstep (se 3 (by rfl) ⟨962096, by rfl⟩ : syracuseStep 5131181 = 1924193) B1924193
theorem B4058059 : Blo 1423531 4058059 := bstep (se 1 (by rfl) ⟨3043544, by rfl⟩ : syracuseStep 4058059 = 6087089) B6087089
theorem B3206105 : Blo 1423531 3206105 := bstep (se 2 (by rfl) ⟨1202289, by rfl⟩ : syracuseStep 3206105 = 2404579) B2404579
theorem B7212077 : Blo 1423531 7212077 := bstep (se 3 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 7212077 = 2704529) B2704529
theorem B2567219 : Blo 1423531 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B3206195 : Blo 1423531 3206195 := bstep (se 1 (by rfl) ⟨2404646, by rfl⟩ : syracuseStep 3206195 = 4809293) B4809293
theorem B6843457 : Blo 1423531 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B3206231 : Blo 1423531 3206231 := bstep (se 1 (by rfl) ⟨2404673, by rfl⟩ : syracuseStep 3206231 = 4809347) B4809347
theorem B2403479 : Blo 1423531 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B7810199 : Blo 1423531 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B12332249 : Blo 1423531 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B13003993 : Blo 1423531 13003993 := bstep (se 2 (by rfl) ⟨4876497, by rfl⟩ : syracuseStep 13003993 = 9752995) B9752995
theorem B4058333 : Blo 1423531 4058333 := bstep (se 3 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 4058333 = 1521875) B1521875
theorem B3206411 : Blo 1423531 3206411 := bstep (se 1 (by rfl) ⟨2404808, by rfl⟩ : syracuseStep 3206411 = 4809617) B4809617
theorem B2403607 : Blo 1423531 2403607 := bstep (se 1 (by rfl) ⟨1802705, by rfl⟩ : syracuseStep 2403607 = 3605411) B3605411
theorem B3206465 : Blo 1423531 3206465 := bstep (se 2 (by rfl) ⟨1202424, by rfl⟩ : syracuseStep 3206465 = 2404849) B2404849
theorem B5131613 : Blo 1423531 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B30788981 : Blo 1423531 30788981 := bstep (se 5 (by rfl) ⟨1443233, by rfl⟩ : syracuseStep 30788981 = 2886467) B2886467
theorem B20811185 : Blo 1423531 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B2739659 : Blo 1423531 2739659 := bstep (se 1 (by rfl) ⟨2054744, by rfl⟩ : syracuseStep 2739659 = 4109489) B4109489
theorem B1425399 : Blo 1423531 1425399 := bstep (se 1 (by rfl) ⟨1069049, by rfl⟩ : syracuseStep 1425399 = 2138099) B2138099
theorem B2567681 : Blo 1423531 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B39505421 : Blo 1423531 39505421 := bstep (se 3 (by rfl) ⟨7407266, by rfl⟩ : syracuseStep 39505421 = 14814533) B14814533
theorem B3206681 : Blo 1423531 3206681 := bstep (se 2 (by rfl) ⟨1202505, by rfl⟩ : syracuseStep 3206681 = 2405011) B2405011
theorem B2166359 : Blo 1423531 2166359 := bstep (se 1 (by rfl) ⟨1624769, by rfl⟩ : syracuseStep 2166359 = 3249539) B3249539
theorem B3206771 : Blo 1423531 3206771 := bstep (se 1 (by rfl) ⟨2405078, by rfl⟩ : syracuseStep 3206771 = 4810157) B4810157
theorem B3206807 : Blo 1423531 3206807 := bstep (se 1 (by rfl) ⟨2405105, by rfl⟩ : syracuseStep 3206807 = 4810211) B4810211
theorem B5410577 : Blo 1423531 5410577 := bstep (se 2 (by rfl) ⟨2028966, by rfl⟩ : syracuseStep 5410577 = 4057933) B4057933
theorem B3206987 : Blo 1423531 3206987 := bstep (se 1 (by rfl) ⟨2405240, by rfl⟩ : syracuseStep 3206987 = 4810481) B4810481
theorem B3207041 : Blo 1423531 3207041 := bstep (se 2 (by rfl) ⟨1202640, by rfl⟩ : syracuseStep 3207041 = 2405281) B2405281
theorem B2404235 : Blo 1423531 2404235 := bstep (se 1 (by rfl) ⟨1803176, by rfl⟩ : syracuseStep 2404235 = 3606353) B3606353
theorem B1601527 : Blo 1423531 1601527 := bstep (se 1 (by rfl) ⟨1201145, by rfl⟩ : syracuseStep 1601527 = 2402291) B2402291
theorem B2404363 : Blo 1423531 2404363 := bstep (se 1 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 2404363 = 3606545) B3606545
theorem B8220689 : Blo 1423531 8220689 := bstep (se 2 (by rfl) ⟨3082758, by rfl⟩ : syracuseStep 8220689 = 6165517) B6165517
theorem B3207257 : Blo 1423531 3207257 := bstep (se 2 (by rfl) ⟨1202721, by rfl⟩ : syracuseStep 3207257 = 2405443) B2405443
theorem B2314379 : Blo 1423531 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B2404505 : Blo 1423531 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B1601707 : Blo 1423531 1601707 := bstep (se 1 (by rfl) ⟨1201280, by rfl⟩ : syracuseStep 1601707 = 2402561) B2402561
theorem B3207347 : Blo 1423531 3207347 := bstep (se 1 (by rfl) ⟨2405510, by rfl⟩ : syracuseStep 3207347 = 4811021) B4811021
theorem B4804811 : Blo 1423531 4804811 := bstep (se 1 (by rfl) ⟨3603608, by rfl⟩ : syracuseStep 4804811 = 7207217) B7207217
theorem B2887895 : Blo 1423531 2887895 := bstep (se 1 (by rfl) ⟨2165921, by rfl⟩ : syracuseStep 2887895 = 4331843) B4331843
theorem B3207383 : Blo 1423531 3207383 := bstep (se 1 (by rfl) ⟨2405537, by rfl⟩ : syracuseStep 3207383 = 4811075) B4811075
theorem B5411033 : Blo 1423531 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B1601815 : Blo 1423531 1601815 := bstep (se 1 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 1601815 = 2402723) B2402723
theorem B2404633 : Blo 1423531 2404633 := bstep (se 2 (by rfl) ⟨901737, by rfl⟩ : syracuseStep 2404633 = 1803475) B1803475
theorem B6082867 : Blo 1423531 6082867 := bstep (se 1 (by rfl) ⟨4562150, by rfl⟩ : syracuseStep 6082867 = 9124301) B9124301
theorem B15012161 : Blo 1423531 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B5411245 : Blo 1423531 5411245 := bstep (se 3 (by rfl) ⟨1014608, by rfl⟩ : syracuseStep 5411245 = 2029217) B2029217
theorem B1601995 : Blo 1423531 1601995 := bstep (se 1 (by rfl) ⟨1201496, by rfl⟩ : syracuseStep 1601995 = 2402993) B2402993
theorem B4805081 : Blo 1423531 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B1602103 : Blo 1423531 1602103 := bstep (se 1 (by rfl) ⟨1201577, by rfl⟩ : syracuseStep 1602103 = 2403155) B2403155
theorem B3043955 : Blo 1423531 3043955 := bstep (se 1 (by rfl) ⟨2282966, by rfl⟩ : syracuseStep 3043955 = 4565933) B4565933
theorem B5411549 : Blo 1423531 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B1602283 : Blo 1423531 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1520375 : Blo 1423531 1520375 := bstep (se 1 (by rfl) ⟨1140281, by rfl⟩ : syracuseStep 1520375 = 2280563) B2280563
theorem B2888473 : Blo 1423531 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B2601803 : Blo 1423531 2601803 := bstep (se 1 (by rfl) ⟨1951352, by rfl⟩ : syracuseStep 2601803 = 3902705) B3902705
theorem B1602391 : Blo 1423531 1602391 := bstep (se 1 (by rfl) ⟨1201793, by rfl⟩ : syracuseStep 1602391 = 2403587) B2403587
theorem B2405207 : Blo 1423531 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B2405335 : Blo 1423531 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B1602571 : Blo 1423531 1602571 := bstep (se 1 (by rfl) ⟨1201928, by rfl⟩ : syracuseStep 1602571 = 2403857) B2403857
theorem B3044441 : Blo 1423531 3044441 := bstep (se 2 (by rfl) ⟨1141665, by rfl⟩ : syracuseStep 3044441 = 2283331) B2283331
theorem B12162149 : Blo 1423531 12162149 := bstep (se 4 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 12162149 = 2280403) B2280403
theorem B3085427 : Blo 1423531 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1602679 : Blo 1423531 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B4805783 : Blo 1423531 4805783 := bstep (se 1 (by rfl) ⟨3604337, by rfl⟩ : syracuseStep 4805783 = 7208675) B7208675
theorem B2135321 : Blo 1423531 2135321 := bstep (se 2 (by rfl) ⟨800745, by rfl⟩ : syracuseStep 2135321 = 1601491) B1601491
theorem B1602859 : Blo 1423531 1602859 := bstep (se 1 (by rfl) ⟨1202144, by rfl⟩ : syracuseStep 1602859 = 2404289) B2404289
theorem B10966337 : Blo 1423531 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B2135435 : Blo 1423531 2135435 := bstep (se 1 (by rfl) ⟨1601576, by rfl⟩ : syracuseStep 2135435 = 3203153) B3203153
theorem B2135447 : Blo 1423531 2135447 := bstep (se 1 (by rfl) ⟨1601585, by rfl⟩ : syracuseStep 2135447 = 3203171) B3203171
theorem B1602967 : Blo 1423531 1602967 := bstep (se 1 (by rfl) ⟨1202225, by rfl⟩ : syracuseStep 1602967 = 2404451) B2404451
theorem B2135513 : Blo 1423531 2135513 := bstep (se 2 (by rfl) ⟨800817, by rfl⟩ : syracuseStep 2135513 = 1601635) B1601635
theorem B6166033 : Blo 1423531 6166033 := bstep (se 2 (by rfl) ⟨2312262, by rfl⟩ : syracuseStep 6166033 = 4624525) B4624525
theorem B2135627 : Blo 1423531 2135627 := bstep (se 1 (by rfl) ⟨1601720, by rfl⟩ : syracuseStep 2135627 = 3203441) B3203441
theorem B1603147 : Blo 1423531 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B2135639 : Blo 1423531 2135639 := bstep (se 1 (by rfl) ⟨1601729, by rfl⟩ : syracuseStep 2135639 = 3203459) B3203459
theorem B2135705 : Blo 1423531 2135705 := bstep (se 2 (by rfl) ⟨800889, by rfl⟩ : syracuseStep 2135705 = 1601779) B1601779
theorem B4560563 : Blo 1423531 4560563 := bstep (se 1 (by rfl) ⟨3420422, by rfl⟩ : syracuseStep 4560563 = 6840845) B6840845
theorem B4806323 : Blo 1423531 4806323 := bstep (se 1 (by rfl) ⟨3604742, by rfl⟩ : syracuseStep 4806323 = 7209485) B7209485
theorem B12334771 : Blo 1423531 12334771 := bstep (se 1 (by rfl) ⟨9251078, by rfl⟩ : syracuseStep 12334771 = 18502157) B18502157
theorem B1603255 : Blo 1423531 1603255 := bstep (se 1 (by rfl) ⟨1202441, by rfl⟩ : syracuseStep 1603255 = 2404883) B2404883
theorem B18249421 : Blo 1423531 18249421 := bstep (se 3 (by rfl) ⟨3421766, by rfl⟩ : syracuseStep 18249421 = 6843533) B6843533
theorem B2283223 : Blo 1423531 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B9885401 : Blo 1423531 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B6084355 : Blo 1423531 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B2135819 : Blo 1423531 2135819 := bstep (se 1 (by rfl) ⟨1601864, by rfl⟩ : syracuseStep 2135819 = 3203729) B3203729
theorem B2135831 : Blo 1423531 2135831 := bstep (se 1 (by rfl) ⟨1601873, by rfl⟩ : syracuseStep 2135831 = 3203747) B3203747
theorem B3422017 : Blo 1423531 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B7206731 : Blo 1423531 7206731 := bstep (se 1 (by rfl) ⟨5405048, by rfl⟩ : syracuseStep 7206731 = 10810097) B10810097
theorem B4560715 : Blo 1423531 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B2135897 : Blo 1423531 2135897 := bstep (se 2 (by rfl) ⟨800961, by rfl⟩ : syracuseStep 2135897 = 1601923) B1601923
theorem B1603435 : Blo 1423531 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B4806593 : Blo 1423531 4806593 := bstep (se 2 (by rfl) ⟨1802472, by rfl⟩ : syracuseStep 4806593 = 3604945) B3604945
theorem B2136011 : Blo 1423531 2136011 := bstep (se 1 (by rfl) ⟨1602008, by rfl⟩ : syracuseStep 2136011 = 3204017) B3204017
theorem B2136023 : Blo 1423531 2136023 := bstep (se 1 (by rfl) ⟨1602017, by rfl⟩ : syracuseStep 2136023 = 3204035) B3204035
theorem B1603543 : Blo 1423531 1603543 := bstep (se 1 (by rfl) ⟨1202657, by rfl⟩ : syracuseStep 1603543 = 2405315) B2405315
theorem B6502361 : Blo 1423531 6502361 := bstep (se 2 (by rfl) ⟨2438385, by rfl⟩ : syracuseStep 6502361 = 4876771) B4876771
theorem B2136089 : Blo 1423531 2136089 := bstep (se 2 (by rfl) ⟨801033, by rfl⟩ : syracuseStep 2136089 = 1602067) B1602067
theorem B2136203 : Blo 1423531 2136203 := bstep (se 1 (by rfl) ⟨1602152, by rfl⟩ : syracuseStep 2136203 = 3204305) B3204305
theorem B1603723 : Blo 1423531 1603723 := bstep (se 1 (by rfl) ⟨1202792, by rfl⟩ : syracuseStep 1603723 = 2405585) B2405585
theorem B2136215 : Blo 1423531 2136215 := bstep (se 1 (by rfl) ⟨1602161, by rfl⟩ : syracuseStep 2136215 = 3204323) B3204323
theorem B1423531 : Blo 1423531 1423531 := bstep (se 1 (by rfl) ⟨1067648, by rfl⟩ : syracuseStep 1423531 = 2135297) B2135297
theorem B1423543 : Blo 1423531 1423543 := bstep (se 1 (by rfl) ⟨1067657, by rfl⟩ : syracuseStep 1423543 = 2135315) B2135315
theorem B1423563 : Blo 1423531 1423563 := bstep (se 1 (by rfl) ⟨1067672, by rfl⟩ : syracuseStep 1423563 = 2135345) B2135345
theorem B1423575 : Blo 1423531 1423575 := bstep (se 1 (by rfl) ⟨1067681, by rfl⟩ : syracuseStep 1423575 = 2135363) B2135363
theorem B2136281 : Blo 1423531 2136281 := bstep (se 2 (by rfl) ⟨801105, by rfl⟩ : syracuseStep 2136281 = 1602211) B1602211
theorem B1423595 : Blo 1423531 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B1423607 : Blo 1423531 1423607 := bstep (se 1 (by rfl) ⟨1067705, by rfl⟩ : syracuseStep 1423607 = 2135411) B2135411
theorem B1423627 : Blo 1423531 1423627 := bstep (se 1 (by rfl) ⟨1067720, by rfl⟩ : syracuseStep 1423627 = 2135441) B2135441
theorem B1423639 : Blo 1423531 1423639 := bstep (se 1 (by rfl) ⟨1067729, by rfl⟩ : syracuseStep 1423639 = 2135459) B2135459
theorem B1464599 : Blo 1423531 1464599 := bstep (se 1 (by rfl) ⟨1098449, by rfl⟩ : syracuseStep 1464599 = 2196899) B2196899
theorem B1423659 : Blo 1423531 1423659 := bstep (se 1 (by rfl) ⟨1067744, by rfl⟩ : syracuseStep 1423659 = 2135489) B2135489
theorem B5773619 : Blo 1423531 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B1423671 : Blo 1423531 1423671 := bstep (se 1 (by rfl) ⟨1067753, by rfl⟩ : syracuseStep 1423671 = 2135507) B2135507
theorem B4561217 : Blo 1423531 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B1423691 : Blo 1423531 1423691 := bstep (se 1 (by rfl) ⟨1067768, by rfl⟩ : syracuseStep 1423691 = 2135537) B2135537
theorem B2136395 : Blo 1423531 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B1423703 : Blo 1423531 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B2136407 : Blo 1423531 2136407 := bstep (se 1 (by rfl) ⟨1602305, by rfl⟩ : syracuseStep 2136407 = 3204611) B3204611
theorem B6084953 : Blo 1423531 6084953 := bstep (se 2 (by rfl) ⟨2281857, by rfl⟩ : syracuseStep 6084953 = 4563715) B4563715
theorem B10271069 : Blo 1423531 10271069 := bstep (se 3 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 10271069 = 3851651) B3851651
theorem B1423723 : Blo 1423531 1423723 := bstep (se 1 (by rfl) ⟨1067792, by rfl⟩ : syracuseStep 1423723 = 2135585) B2135585
theorem B94959985 : Blo 1423531 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B1423735 : Blo 1423531 1423735 := bstep (se 1 (by rfl) ⟨1067801, by rfl⟩ : syracuseStep 1423735 = 2135603) B2135603
theorem B1423755 : Blo 1423531 1423755 := bstep (se 1 (by rfl) ⟨1067816, by rfl⟩ : syracuseStep 1423755 = 2135633) B2135633
theorem B1423767 : Blo 1423531 1423767 := bstep (se 1 (by rfl) ⟨1067825, by rfl⟩ : syracuseStep 1423767 = 2135651) B2135651
theorem B2136473 : Blo 1423531 2136473 := bstep (se 2 (by rfl) ⟨801177, by rfl⟩ : syracuseStep 2136473 = 1602355) B1602355
theorem B1423787 : Blo 1423531 1423787 := bstep (se 1 (by rfl) ⟨1067840, by rfl⟩ : syracuseStep 1423787 = 2135681) B2135681
theorem B1423799 : Blo 1423531 1423799 := bstep (se 1 (by rfl) ⟨1067849, by rfl⟩ : syracuseStep 1423799 = 2135699) B2135699
theorem B1423819 : Blo 1423531 1423819 := bstep (se 1 (by rfl) ⟨1067864, by rfl⟩ : syracuseStep 1423819 = 2135729) B2135729
theorem B1423831 : Blo 1423531 1423831 := bstep (se 1 (by rfl) ⟨1067873, by rfl⟩ : syracuseStep 1423831 = 2135747) B2135747
theorem B1522135 : Blo 1423531 1522135 := bstep (se 1 (by rfl) ⟨1141601, by rfl⟩ : syracuseStep 1522135 = 2283203) B2283203
theorem B4807133 : Blo 1423531 4807133 := bstep (se 3 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 4807133 = 1802675) B1802675
theorem B1423851 : Blo 1423531 1423851 := bstep (se 1 (by rfl) ⟨1067888, by rfl⟩ : syracuseStep 1423851 = 2135777) B2135777
theorem B1423863 : Blo 1423531 1423863 := bstep (se 1 (by rfl) ⟨1067897, by rfl⟩ : syracuseStep 1423863 = 2135795) B2135795
theorem B1423883 : Blo 1423531 1423883 := bstep (se 1 (by rfl) ⟨1067912, by rfl⟩ : syracuseStep 1423883 = 2135825) B2135825
theorem B2136587 : Blo 1423531 2136587 := bstep (se 1 (by rfl) ⟨1602440, by rfl⟩ : syracuseStep 2136587 = 3204881) B3204881
theorem B5405201 : Blo 1423531 5405201 := bstep (se 2 (by rfl) ⟨2026950, by rfl⟩ : syracuseStep 5405201 = 4053901) B4053901
theorem B1423895 : Blo 1423531 1423895 := bstep (se 1 (by rfl) ⟨1067921, by rfl⟩ : syracuseStep 1423895 = 2135843) B2135843
theorem B2136599 : Blo 1423531 2136599 := bstep (se 1 (by rfl) ⟨1602449, by rfl⟩ : syracuseStep 2136599 = 3204899) B3204899
theorem B5134871 : Blo 1423531 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B1423915 : Blo 1423531 1423915 := bstep (se 1 (by rfl) ⟨1067936, by rfl⟩ : syracuseStep 1423915 = 2135873) B2135873
theorem B1423927 : Blo 1423531 1423927 := bstep (se 1 (by rfl) ⟨1067945, by rfl⟩ : syracuseStep 1423927 = 2135891) B2135891
theorem B1423947 : Blo 1423531 1423947 := bstep (se 1 (by rfl) ⟨1067960, by rfl⟩ : syracuseStep 1423947 = 2135921) B2135921
theorem B1423959 : Blo 1423531 1423959 := bstep (se 1 (by rfl) ⟨1067969, by rfl⟩ : syracuseStep 1423959 = 2135939) B2135939
theorem B2136665 : Blo 1423531 2136665 := bstep (se 2 (by rfl) ⟨801249, by rfl⟩ : syracuseStep 2136665 = 1602499) B1602499
theorem B1423979 : Blo 1423531 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B1423991 : Blo 1423531 1423991 := bstep (se 1 (by rfl) ⟨1067993, by rfl⟩ : syracuseStep 1423991 = 2135987) B2135987
theorem B1424011 : Blo 1423531 1424011 := bstep (se 1 (by rfl) ⟨1068008, by rfl⟩ : syracuseStep 1424011 = 2136017) B2136017
theorem B1424023 : Blo 1423531 1424023 := bstep (se 1 (by rfl) ⟨1068017, by rfl⟩ : syracuseStep 1424023 = 2136035) B2136035
theorem B1424043 : Blo 1423531 1424043 := bstep (se 1 (by rfl) ⟨1068032, by rfl⟩ : syracuseStep 1424043 = 2136065) B2136065
theorem B1424055 : Blo 1423531 1424055 := bstep (se 1 (by rfl) ⟨1068041, by rfl⟩ : syracuseStep 1424055 = 2136083) B2136083
theorem B6085313 : Blo 1423531 6085313 := bstep (se 2 (by rfl) ⟨2281992, by rfl⟩ : syracuseStep 6085313 = 4563985) B4563985
theorem B1424075 : Blo 1423531 1424075 := bstep (se 1 (by rfl) ⟨1068056, by rfl⟩ : syracuseStep 1424075 = 2136113) B2136113
theorem B2136779 : Blo 1423531 2136779 := bstep (se 1 (by rfl) ⟨1602584, by rfl⟩ : syracuseStep 2136779 = 3205169) B3205169
theorem B1424087 : Blo 1423531 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B2136791 : Blo 1423531 2136791 := bstep (se 1 (by rfl) ⟨1602593, by rfl⟩ : syracuseStep 2136791 = 3205187) B3205187
theorem B1424107 : Blo 1423531 1424107 := bstep (se 1 (by rfl) ⟨1068080, by rfl⟩ : syracuseStep 1424107 = 2136161) B2136161
theorem B1424119 : Blo 1423531 1424119 := bstep (se 1 (by rfl) ⟨1068089, by rfl⟩ : syracuseStep 1424119 = 2136179) B2136179
theorem B1424139 : Blo 1423531 1424139 := bstep (se 1 (by rfl) ⟨1068104, by rfl⟩ : syracuseStep 1424139 = 2136209) B2136209
theorem B1424151 : Blo 1423531 1424151 := bstep (se 1 (by rfl) ⟨1068113, by rfl⟩ : syracuseStep 1424151 = 2136227) B2136227
theorem B4111127 : Blo 1423531 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B2136857 : Blo 1423531 2136857 := bstep (se 2 (by rfl) ⟨801321, by rfl⟩ : syracuseStep 2136857 = 1602643) B1602643
theorem B1424171 : Blo 1423531 1424171 := bstep (se 1 (by rfl) ⟨1068128, by rfl⟩ : syracuseStep 1424171 = 2136257) B2136257
theorem B10263341 : Blo 1423531 10263341 := bstep (se 3 (by rfl) ⟨1924376, by rfl⟩ : syracuseStep 10263341 = 3848753) B3848753
theorem B1424183 : Blo 1423531 1424183 := bstep (se 1 (by rfl) ⟨1068137, by rfl⟩ : syracuseStep 1424183 = 2136275) B2136275
theorem B1424203 : Blo 1423531 1424203 := bstep (se 1 (by rfl) ⟨1068152, by rfl⟩ : syracuseStep 1424203 = 2136305) B2136305
theorem B1424215 : Blo 1423531 1424215 := bstep (se 1 (by rfl) ⟨1068161, by rfl⟩ : syracuseStep 1424215 = 2136323) B2136323
theorem B3423065 : Blo 1423531 3423065 := bstep (se 2 (by rfl) ⟨1283649, by rfl⟩ : syracuseStep 3423065 = 2567299) B2567299
theorem B7215965 : Blo 1423531 7215965 := bstep (se 3 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 7215965 = 2705987) B2705987
theorem B1424235 : Blo 1423531 1424235 := bstep (se 1 (by rfl) ⟨1068176, by rfl⟩ : syracuseStep 1424235 = 2136353) B2136353
theorem B1424247 : Blo 1423531 1424247 := bstep (se 1 (by rfl) ⟨1068185, by rfl⟩ : syracuseStep 1424247 = 2136371) B2136371
theorem B1424267 : Blo 1423531 1424267 := bstep (se 1 (by rfl) ⟨1068200, by rfl⟩ : syracuseStep 1424267 = 2136401) B2136401
theorem B2136971 : Blo 1423531 2136971 := bstep (se 1 (by rfl) ⟨1602728, by rfl⟩ : syracuseStep 2136971 = 3205457) B3205457
theorem B1424279 : Blo 1423531 1424279 := bstep (se 1 (by rfl) ⟨1068209, by rfl⟩ : syracuseStep 1424279 = 2136419) B2136419
theorem B2136983 : Blo 1423531 2136983 := bstep (se 1 (by rfl) ⟨1602737, by rfl⟩ : syracuseStep 2136983 = 3205475) B3205475
theorem B1424299 : Blo 1423531 1424299 := bstep (se 1 (by rfl) ⟨1068224, by rfl⟩ : syracuseStep 1424299 = 2136449) B2136449
theorem B39500723 : Blo 1423531 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B1424311 : Blo 1423531 1424311 := bstep (se 1 (by rfl) ⟨1068233, by rfl⟩ : syracuseStep 1424311 = 2136467) B2136467
theorem B3251137 : Blo 1423531 3251137 := bstep (se 2 (by rfl) ⟨1219176, by rfl⟩ : syracuseStep 3251137 = 2438353) B2438353
theorem B1424331 : Blo 1423531 1424331 := bstep (se 1 (by rfl) ⟨1068248, by rfl⟩ : syracuseStep 1424331 = 2136497) B2136497
theorem B1424343 : Blo 1423531 1424343 := bstep (se 1 (by rfl) ⟨1068257, by rfl⟩ : syracuseStep 1424343 = 2136515) B2136515
theorem B2137049 : Blo 1423531 2137049 := bstep (se 2 (by rfl) ⟨801393, by rfl⟩ : syracuseStep 2137049 = 1602787) B1602787
theorem B1424363 : Blo 1423531 1424363 := bstep (se 1 (by rfl) ⟨1068272, by rfl⟩ : syracuseStep 1424363 = 2136545) B2136545
theorem B1424375 : Blo 1423531 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B1424395 : Blo 1423531 1424395 := bstep (se 1 (by rfl) ⟨1068296, by rfl⟩ : syracuseStep 1424395 = 2136593) B2136593
theorem B1424407 : Blo 1423531 1424407 := bstep (se 1 (by rfl) ⟨1068305, by rfl⟩ : syracuseStep 1424407 = 2136611) B2136611
theorem B1424427 : Blo 1423531 1424427 := bstep (se 1 (by rfl) ⟨1068320, by rfl⟩ : syracuseStep 1424427 = 2136641) B2136641
theorem B3292211 : Blo 1423531 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B1424439 : Blo 1423531 1424439 := bstep (se 1 (by rfl) ⟨1068329, by rfl⟩ : syracuseStep 1424439 = 2136659) B2136659
theorem B1424459 : Blo 1423531 1424459 := bstep (se 1 (by rfl) ⟨1068344, by rfl⟩ : syracuseStep 1424459 = 2136689) B2136689
theorem B2137163 : Blo 1423531 2137163 := bstep (se 1 (by rfl) ⟨1602872, by rfl⟩ : syracuseStep 2137163 = 3205745) B3205745
theorem B1424471 : Blo 1423531 1424471 := bstep (se 1 (by rfl) ⟨1068353, by rfl⟩ : syracuseStep 1424471 = 2136707) B2136707
theorem B2137175 : Blo 1423531 2137175 := bstep (se 1 (by rfl) ⟨1602881, by rfl⟩ : syracuseStep 2137175 = 3205763) B3205763
theorem B1424491 : Blo 1423531 1424491 := bstep (se 1 (by rfl) ⟨1068368, by rfl⟩ : syracuseStep 1424491 = 2136737) B2136737
theorem B1424503 : Blo 1423531 1424503 := bstep (se 1 (by rfl) ⟨1068377, by rfl⟩ : syracuseStep 1424503 = 2136755) B2136755
theorem B1424523 : Blo 1423531 1424523 := bstep (se 1 (by rfl) ⟨1068392, by rfl⟩ : syracuseStep 1424523 = 2136785) B2136785
theorem B1424535 : Blo 1423531 1424535 := bstep (se 1 (by rfl) ⟨1068401, by rfl⟩ : syracuseStep 1424535 = 2136803) B2136803
theorem B2137241 : Blo 1423531 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1424555 : Blo 1423531 1424555 := bstep (se 1 (by rfl) ⟨1068416, by rfl⟩ : syracuseStep 1424555 = 2136833) B2136833
theorem B1424567 : Blo 1423531 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B3603649 : Blo 1423531 3603649 := bstep (se 2 (by rfl) ⟨1351368, by rfl⟩ : syracuseStep 3603649 = 2702737) B2702737
theorem B5405899 : Blo 1423531 5405899 := bstep (se 1 (by rfl) ⟨4054424, by rfl⟩ : syracuseStep 5405899 = 8108849) B8108849
theorem B1424587 : Blo 1423531 1424587 := bstep (se 1 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 1424587 = 2136881) B2136881
theorem B1424599 : Blo 1423531 1424599 := bstep (se 1 (by rfl) ⟨1068449, by rfl⟩ : syracuseStep 1424599 = 2136899) B2136899
theorem B8658137 : Blo 1423531 8658137 := bstep (se 2 (by rfl) ⟨3246801, by rfl⟩ : syracuseStep 8658137 = 6493603) B6493603
theorem B1424619 : Blo 1423531 1424619 := bstep (se 1 (by rfl) ⟨1068464, by rfl⟩ : syracuseStep 1424619 = 2136929) B2136929
theorem B1424631 : Blo 1423531 1424631 := bstep (se 1 (by rfl) ⟨1068473, by rfl⟩ : syracuseStep 1424631 = 2136947) B2136947
theorem B1424651 : Blo 1423531 1424651 := bstep (se 1 (by rfl) ⟨1068488, by rfl⟩ : syracuseStep 1424651 = 2136977) B2136977
theorem B2137355 : Blo 1423531 2137355 := bstep (se 1 (by rfl) ⟨1603016, by rfl⟩ : syracuseStep 2137355 = 3206033) B3206033
theorem B1424663 : Blo 1423531 1424663 := bstep (se 1 (by rfl) ⟨1068497, by rfl⟩ : syracuseStep 1424663 = 2136995) B2136995
theorem B2137367 : Blo 1423531 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B1424683 : Blo 1423531 1424683 := bstep (se 1 (by rfl) ⟨1068512, by rfl⟩ : syracuseStep 1424683 = 2137025) B2137025
theorem B1424695 : Blo 1423531 1424695 := bstep (se 1 (by rfl) ⟨1068521, by rfl⟩ : syracuseStep 1424695 = 2137043) B2137043
theorem B1424715 : Blo 1423531 1424715 := bstep (se 1 (by rfl) ⟨1068536, by rfl⟩ : syracuseStep 1424715 = 2137073) B2137073
theorem B1424727 : Blo 1423531 1424727 := bstep (se 1 (by rfl) ⟨1068545, by rfl⟩ : syracuseStep 1424727 = 2137091) B2137091
theorem B2137433 : Blo 1423531 2137433 := bstep (se 2 (by rfl) ⟨801537, by rfl⟩ : syracuseStep 2137433 = 1603075) B1603075
theorem B8117597 : Blo 1423531 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B1424747 : Blo 1423531 1424747 := bstep (se 1 (by rfl) ⟨1068560, by rfl⟩ : syracuseStep 1424747 = 2137121) B2137121
theorem B1424759 : Blo 1423531 1424759 := bstep (se 1 (by rfl) ⟨1068569, by rfl⟩ : syracuseStep 1424759 = 2137139) B2137139
theorem B1424779 : Blo 1423531 1424779 := bstep (se 1 (by rfl) ⟨1068584, by rfl⟩ : syracuseStep 1424779 = 2137169) B2137169
theorem B1424791 : Blo 1423531 1424791 := bstep (se 1 (by rfl) ⟨1068593, by rfl⟩ : syracuseStep 1424791 = 2137187) B2137187
theorem B1424811 : Blo 1423531 1424811 := bstep (se 1 (by rfl) ⟨1068608, by rfl⟩ : syracuseStep 1424811 = 2137217) B2137217
theorem B5135795 : Blo 1423531 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B1424823 : Blo 1423531 1424823 := bstep (se 1 (by rfl) ⟨1068617, by rfl⟩ : syracuseStep 1424823 = 2137235) B2137235
theorem B1424843 : Blo 1423531 1424843 := bstep (se 1 (by rfl) ⟨1068632, by rfl⟩ : syracuseStep 1424843 = 2137265) B2137265
theorem B2137547 : Blo 1423531 2137547 := bstep (se 1 (by rfl) ⟨1603160, by rfl⟩ : syracuseStep 2137547 = 3206321) B3206321
theorem B1424855 : Blo 1423531 1424855 := bstep (se 1 (by rfl) ⟨1068641, by rfl⟩ : syracuseStep 1424855 = 2137283) B2137283
theorem B2137559 : Blo 1423531 2137559 := bstep (se 1 (by rfl) ⟨1603169, by rfl⟩ : syracuseStep 2137559 = 3206339) B3206339
theorem B5406173 : Blo 1423531 5406173 := bstep (se 3 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 5406173 = 2027315) B2027315
theorem B1424875 : Blo 1423531 1424875 := bstep (se 1 (by rfl) ⟨1068656, by rfl⟩ : syracuseStep 1424875 = 2137313) B2137313
theorem B1424887 : Blo 1423531 1424887 := bstep (se 1 (by rfl) ⟨1068665, by rfl⟩ : syracuseStep 1424887 = 2137331) B2137331
theorem B1424907 : Blo 1423531 1424907 := bstep (se 1 (by rfl) ⟨1068680, by rfl⟩ : syracuseStep 1424907 = 2137361) B2137361
theorem B1424919 : Blo 1423531 1424919 := bstep (se 1 (by rfl) ⟨1068689, by rfl⟩ : syracuseStep 1424919 = 2137379) B2137379
theorem B2137625 : Blo 1423531 2137625 := bstep (se 2 (by rfl) ⟨801609, by rfl⟩ : syracuseStep 2137625 = 1603219) B1603219
theorem B1424939 : Blo 1423531 1424939 := bstep (se 1 (by rfl) ⟨1068704, by rfl⟩ : syracuseStep 1424939 = 2137409) B2137409
theorem B1424951 : Blo 1423531 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B7208513 : Blo 1423531 7208513 := bstep (se 2 (by rfl) ⟨2703192, by rfl⟩ : syracuseStep 7208513 = 5406385) B5406385
theorem B4808267 : Blo 1423531 4808267 := bstep (se 1 (by rfl) ⟨3606200, by rfl⟩ : syracuseStep 4808267 = 7212401) B7212401
theorem B1424971 : Blo 1423531 1424971 := bstep (se 1 (by rfl) ⟨1068728, by rfl⟩ : syracuseStep 1424971 = 2137457) B2137457
theorem B1424983 : Blo 1423531 1424983 := bstep (se 1 (by rfl) ⟨1068737, by rfl⟩ : syracuseStep 1424983 = 2137475) B2137475
theorem B1425003 : Blo 1423531 1425003 := bstep (se 1 (by rfl) ⟨1068752, by rfl⟩ : syracuseStep 1425003 = 2137505) B2137505
theorem B1425015 : Blo 1423531 1425015 := bstep (se 1 (by rfl) ⟨1068761, by rfl⟩ : syracuseStep 1425015 = 2137523) B2137523
theorem B1425035 : Blo 1423531 1425035 := bstep (se 1 (by rfl) ⟨1068776, by rfl⟩ : syracuseStep 1425035 = 2137553) B2137553
theorem B2137739 : Blo 1423531 2137739 := bstep (se 1 (by rfl) ⟨1603304, by rfl⟩ : syracuseStep 2137739 = 3206609) B3206609
theorem B1425047 : Blo 1423531 1425047 := bstep (se 1 (by rfl) ⟨1068785, by rfl⟩ : syracuseStep 1425047 = 2137571) B2137571
theorem B2137751 : Blo 1423531 2137751 := bstep (se 1 (by rfl) ⟨1603313, by rfl⟩ : syracuseStep 2137751 = 3206627) B3206627
theorem B1425067 : Blo 1423531 1425067 := bstep (se 1 (by rfl) ⟨1068800, by rfl⟩ : syracuseStep 1425067 = 2137601) B2137601
theorem B1425079 : Blo 1423531 1425079 := bstep (se 1 (by rfl) ⟨1068809, by rfl⟩ : syracuseStep 1425079 = 2137619) B2137619
theorem B2703041 : Blo 1423531 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B1425099 : Blo 1423531 1425099 := bstep (se 1 (by rfl) ⟨1068824, by rfl⟩ : syracuseStep 1425099 = 2137649) B2137649
theorem B1425111 : Blo 1423531 1425111 := bstep (se 1 (by rfl) ⟨1068833, by rfl⟩ : syracuseStep 1425111 = 2137667) B2137667
theorem B2137817 : Blo 1423531 2137817 := bstep (se 2 (by rfl) ⟨801681, by rfl⟩ : syracuseStep 2137817 = 1603363) B1603363
theorem B1425131 : Blo 1423531 1425131 := bstep (se 1 (by rfl) ⟨1068848, by rfl⟩ : syracuseStep 1425131 = 2137697) B2137697
theorem B1425143 : Blo 1423531 1425143 := bstep (se 1 (by rfl) ⟨1068857, by rfl⟩ : syracuseStep 1425143 = 2137715) B2137715
theorem B1425163 : Blo 1423531 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B3604247 : Blo 1423531 3604247 := bstep (se 1 (by rfl) ⟨2703185, by rfl⟩ : syracuseStep 3604247 = 5406371) B5406371
theorem B1425175 : Blo 1423531 1425175 := bstep (se 1 (by rfl) ⟨1068881, by rfl⟩ : syracuseStep 1425175 = 2137763) B2137763
theorem B1425195 : Blo 1423531 1425195 := bstep (se 1 (by rfl) ⟨1068896, by rfl⟩ : syracuseStep 1425195 = 2137793) B2137793
theorem B4054835 : Blo 1423531 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B1425207 : Blo 1423531 1425207 := bstep (se 1 (by rfl) ⟨1068905, by rfl⟩ : syracuseStep 1425207 = 2137811) B2137811
theorem B1425227 : Blo 1423531 1425227 := bstep (se 1 (by rfl) ⟨1068920, by rfl⟩ : syracuseStep 1425227 = 2137841) B2137841
theorem B2137931 : Blo 1423531 2137931 := bstep (se 1 (by rfl) ⟨1603448, by rfl⟩ : syracuseStep 2137931 = 3206897) B3206897
theorem B1425239 : Blo 1423531 1425239 := bstep (se 1 (by rfl) ⟨1068929, by rfl⟩ : syracuseStep 1425239 = 2137859) B2137859
theorem B2137943 : Blo 1423531 2137943 := bstep (se 1 (by rfl) ⟨1603457, by rfl⟩ : syracuseStep 2137943 = 3206915) B3206915
theorem B4808537 : Blo 1423531 4808537 := bstep (se 2 (by rfl) ⟨1803201, by rfl⟩ : syracuseStep 4808537 = 3606403) B3606403
theorem B1425259 : Blo 1423531 1425259 := bstep (se 1 (by rfl) ⟨1068944, by rfl⟩ : syracuseStep 1425259 = 2137889) B2137889
theorem B1425271 : Blo 1423531 1425271 := bstep (se 1 (by rfl) ⟨1068953, by rfl⟩ : syracuseStep 1425271 = 2137907) B2137907
theorem B3202955 : Blo 1423531 3202955 := bstep (se 1 (by rfl) ⟨2402216, by rfl⟩ : syracuseStep 3202955 = 4804433) B4804433
theorem B1425291 : Blo 1423531 1425291 := bstep (se 1 (by rfl) ⟨1068968, by rfl⟩ : syracuseStep 1425291 = 2137937) B2137937
theorem B1425303 : Blo 1423531 1425303 := bstep (se 1 (by rfl) ⟨1068977, by rfl⟩ : syracuseStep 1425303 = 2137955) B2137955
theorem B2138009 : Blo 1423531 2138009 := bstep (se 2 (by rfl) ⟨801753, by rfl⟩ : syracuseStep 2138009 = 1603507) B1603507
theorem B1425323 : Blo 1423531 1425323 := bstep (se 1 (by rfl) ⟨1068992, by rfl⟩ : syracuseStep 1425323 = 2137985) B2137985
theorem B1425335 : Blo 1423531 1425335 := bstep (se 1 (by rfl) ⟨1069001, by rfl⟩ : syracuseStep 1425335 = 2138003) B2138003
theorem B3203009 : Blo 1423531 3203009 := bstep (se 2 (by rfl) ⟨1201128, by rfl⟩ : syracuseStep 3203009 = 2402257) B2402257
theorem B2703307 : Blo 1423531 2703307 := bstep (se 1 (by rfl) ⟨2027480, by rfl⟩ : syracuseStep 2703307 = 4054961) B4054961
theorem B1425355 : Blo 1423531 1425355 := bstep (se 1 (by rfl) ⟨1069016, by rfl⟩ : syracuseStep 1425355 = 2138033) B2138033
theorem B1425367 : Blo 1423531 1425367 := bstep (se 1 (by rfl) ⟨1069025, by rfl⟩ : syracuseStep 1425367 = 2138051) B2138051
theorem B4874201 : Blo 1423531 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B1425387 : Blo 1423531 1425387 := bstep (se 1 (by rfl) ⟨1069040, by rfl⟩ : syracuseStep 1425387 = 2138081) B2138081
theorem B1425415 : Blo 1423531 1425415 := bstep (se 1 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 1425415 = 2138123) B2138123
theorem B5480459 : Blo 1423531 5480459 := bstep (se 1 (by rfl) ⟨4110344, by rfl⟩ : syracuseStep 5480459 = 8220689) B8220689
theorem B1425423 : Blo 1423531 1425423 := bstep (se 1 (by rfl) ⟨1069067, by rfl⟩ : syracuseStep 1425423 = 2138135) B2138135
theorem B29253649 : Blo 1423531 29253649 := bstep (se 2 (by rfl) ⟨10970118, by rfl⟩ : syracuseStep 29253649 = 21940237) B21940237
theorem B2138171 : Blo 1423531 2138171 := bstep (se 1 (by rfl) ⟨1603628, by rfl⟩ : syracuseStep 2138171 = 3207257) B3207257
theorem B1425467 : Blo 1423531 1425467 := bstep (se 1 (by rfl) ⟨1069100, by rfl⟩ : syracuseStep 1425467 = 2138201) B2138201
theorem B3850355 : Blo 1423531 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B2138231 : Blo 1423531 2138231 := bstep (se 1 (by rfl) ⟨1603673, by rfl⟩ : syracuseStep 2138231 = 3207347) B3207347
theorem B3203207 : Blo 1423531 3203207 := bstep (se 1 (by rfl) ⟨2402405, by rfl⟩ : syracuseStep 3203207 = 4804811) B4804811
theorem B1925263 : Blo 1423531 1925263 := bstep (se 1 (by rfl) ⟨1443947, by rfl⟩ : syracuseStep 1925263 = 2887895) B2887895
theorem B2138255 : Blo 1423531 2138255 := bstep (se 1 (by rfl) ⟨1603691, by rfl⟩ : syracuseStep 2138255 = 3207383) B3207383
theorem B2138297 : Blo 1423531 2138297 := bstep (se 2 (by rfl) ⟨801861, by rfl⟩ : syracuseStep 2138297 = 1603723) B1603723
theorem B7209161 : Blo 1423531 7209161 := bstep (se 2 (by rfl) ⟨2703435, by rfl⟩ : syracuseStep 7209161 = 5406871) B5406871
theorem B1802503 : Blo 1423531 1802503 := bstep (se 1 (by rfl) ⟨1351877, by rfl⟩ : syracuseStep 1802503 = 2703755) B2703755
theorem B3203387 : Blo 1423531 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B8110489 : Blo 1423531 8110489 := bstep (se 2 (by rfl) ⟨3041433, by rfl⟩ : syracuseStep 8110489 = 6082867) B6082867
theorem B3203513 : Blo 1423531 3203513 := bstep (se 2 (by rfl) ⟨1201317, by rfl⟩ : syracuseStep 3203513 = 2402635) B2402635
theorem B8118737 : Blo 1423531 8118737 := bstep (se 2 (by rfl) ⟨3044526, by rfl⟩ : syracuseStep 8118737 = 6089053) B6089053
theorem B3605107 : Blo 1423531 3605107 := bstep (se 1 (by rfl) ⟨2703830, by rfl⟩ : syracuseStep 3605107 = 5407661) B5407661
theorem B1802999 : Blo 1423531 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B2056951 : Blo 1423531 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B3605249 : Blo 1423531 3605249 := bstep (se 2 (by rfl) ⟨1351968, by rfl⟩ : syracuseStep 3605249 = 2703937) B2703937
theorem B3203855 : Blo 1423531 3203855 := bstep (se 1 (by rfl) ⟨2402891, by rfl⟩ : syracuseStep 3203855 = 4805783) B4805783
theorem B3203873 : Blo 1423531 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B1803151 : Blo 1423531 1803151 := bstep (se 1 (by rfl) ⟨1352363, by rfl⟩ : syracuseStep 1803151 = 2704727) B2704727
theorem B4056065 : Blo 1423531 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B3851297 : Blo 1423531 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B1803323 : Blo 1423531 1803323 := bstep (se 1 (by rfl) ⟨1352492, by rfl⟩ : syracuseStep 1803323 = 2704985) B2704985
theorem B3040375 : Blo 1423531 3040375 := bstep (se 1 (by rfl) ⟨2280281, by rfl⟩ : syracuseStep 3040375 = 4560563) B4560563
theorem B3204215 : Blo 1423531 3204215 := bstep (se 1 (by rfl) ⟨2403161, by rfl⟩ : syracuseStep 3204215 = 4806323) B4806323
theorem B3605705 : Blo 1423531 3605705 := bstep (se 2 (by rfl) ⟨1352139, by rfl⟩ : syracuseStep 3605705 = 2704279) B2704279
theorem B4334849 : Blo 1423531 4334849 := bstep (se 2 (by rfl) ⟨1625568, by rfl⟩ : syracuseStep 4334849 = 3251137) B3251137
theorem B3204395 : Blo 1423531 3204395 := bstep (se 1 (by rfl) ⟨2403296, by rfl⟩ : syracuseStep 3204395 = 4806593) B4806593
theorem B5408147 : Blo 1423531 5408147 := bstep (se 1 (by rfl) ⟨4056110, by rfl⟩ : syracuseStep 5408147 = 8112221) B8112221
theorem B15402449 : Blo 1423531 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B3040811 : Blo 1423531 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B3606059 : Blo 1423531 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B4056635 : Blo 1423531 4056635 := bstep (se 1 (by rfl) ⟨3042476, by rfl⟩ : syracuseStep 4056635 = 6084953) B6084953
theorem B5776957 : Blo 1423531 5776957 := bstep (se 3 (by rfl) ⟨1083179, by rfl⟩ : syracuseStep 5776957 = 2166359) B2166359
theorem B2705015 : Blo 1423531 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B3204755 : Blo 1423531 3204755 := bstep (se 1 (by rfl) ⟨2403566, by rfl⟩ : syracuseStep 3204755 = 4807133) B4807133
theorem B3204809 : Blo 1423531 3204809 := bstep (se 2 (by rfl) ⟨1201803, by rfl⟩ : syracuseStep 3204809 = 2403607) B2403607
theorem B24323813 : Blo 1423531 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B2705167 : Blo 1423531 2705167 := bstep (se 1 (by rfl) ⟨2028875, by rfl⟩ : syracuseStep 2705167 = 4057751) B4057751
theorem B4056875 : Blo 1423531 4056875 := bstep (se 1 (by rfl) ⟨3042656, by rfl⟩ : syracuseStep 4056875 = 6085313) B6085313
theorem B6842227 : Blo 1423531 6842227 := bstep (se 1 (by rfl) ⟨5131670, by rfl⟩ : syracuseStep 6842227 = 10263341) B10263341
theorem B4810643 : Blo 1423531 4810643 := bstep (se 1 (by rfl) ⟨3607982, by rfl⟩ : syracuseStep 4810643 = 7215965) B7215965
theorem B5203997 : Blo 1423531 5203997 := bstep (se 3 (by rfl) ⟨975749, by rfl⟩ : syracuseStep 5203997 = 1951499) B1951499
theorem B2705555 : Blo 1423531 2705555 := bstep (se 1 (by rfl) ⟨2029166, by rfl⟩ : syracuseStep 2705555 = 4058333) B4058333
theorem B9128173 : Blo 1423531 9128173 := bstep (se 3 (by rfl) ⟨1711532, by rfl⟩ : syracuseStep 9128173 = 3423065) B3423065
theorem B24332561 : Blo 1423531 24332561 := bstep (se 2 (by rfl) ⟨9124710, by rfl⟩ : syracuseStep 24332561 = 18249421) B18249421
theorem B8112473 : Blo 1423531 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B3205511 : Blo 1423531 3205511 := bstep (se 1 (by rfl) ⟨2404133, by rfl⟩ : syracuseStep 3205511 = 4808267) B4808267
theorem B10815929 : Blo 1423531 10815929 := bstep (se 2 (by rfl) ⟨4055973, by rfl⟩ : syracuseStep 10815929 = 8111947) B8111947
theorem B105335261 : Blo 1423531 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B3607051 : Blo 1423531 3607051 := bstep (se 1 (by rfl) ⟨2705288, by rfl⟩ : syracuseStep 3607051 = 5410577) B5410577
theorem B2402831 : Blo 1423531 2402831 := bstep (se 1 (by rfl) ⟨1802123, by rfl⟩ : syracuseStep 2402831 = 3604247) B3604247
theorem B3205691 : Blo 1423531 3205691 := bstep (se 1 (by rfl) ⟨2404268, by rfl⟩ : syracuseStep 3205691 = 4808537) B4808537
theorem B3607193 : Blo 1423531 3607193 := bstep (se 2 (by rfl) ⟨1352697, by rfl⟩ : syracuseStep 3607193 = 2705395) B2705395
theorem B3205817 : Blo 1423531 3205817 := bstep (se 2 (by rfl) ⟨1202181, by rfl⟩ : syracuseStep 3205817 = 2404363) B2404363
theorem B54758105 : Blo 1423531 54758105 := bstep (se 2 (by rfl) ⟨20534289, by rfl⟩ : syracuseStep 54758105 = 41068579) B41068579
theorem B32885509 : Blo 1423531 32885509 := bstep (se 4 (by rfl) ⟨3083016, by rfl⟩ : syracuseStep 32885509 = 6166033) B6166033
theorem B5778191 : Blo 1423531 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B3607355 : Blo 1423531 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B3206159 : Blo 1423531 3206159 := bstep (se 1 (by rfl) ⟨2404619, by rfl⟩ : syracuseStep 3206159 = 4809239) B4809239
theorem B6171677 : Blo 1423531 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B3206177 : Blo 1423531 3206177 := bstep (se 2 (by rfl) ⟨1202316, by rfl⟩ : syracuseStep 3206177 = 2404633) B2404633
theorem B2403371 : Blo 1423531 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B3042451 : Blo 1423531 3042451 := bstep (se 1 (by rfl) ⟨2281838, by rfl⟩ : syracuseStep 3042451 = 4563677) B4563677
theorem B3607699 : Blo 1423531 3607699 := bstep (se 1 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 3607699 = 5411549) B5411549
theorem B2886857 : Blo 1423531 2886857 := bstep (se 2 (by rfl) ⟨1082571, by rfl⟩ : syracuseStep 2886857 = 2165143) B2165143
theorem B23088365 : Blo 1423531 23088365 := bstep (se 3 (by rfl) ⟨4329068, by rfl⟩ : syracuseStep 23088365 = 8658137) B8658137
theorem B3607841 : Blo 1423531 3607841 := bstep (se 2 (by rfl) ⟨1352940, by rfl⟩ : syracuseStep 3607841 = 2705881) B2705881
theorem B3206519 : Blo 1423531 3206519 := bstep (se 1 (by rfl) ⟨2404889, by rfl⟩ : syracuseStep 3206519 = 4809779) B4809779
theorem B2403769 : Blo 1423531 2403769 := bstep (se 2 (by rfl) ⟨901413, by rfl⟩ : syracuseStep 2403769 = 1802827) B1802827
theorem B7703993 : Blo 1423531 7703993 := bstep (se 2 (by rfl) ⟨2888997, by rfl⟩ : syracuseStep 7703993 = 5777995) B5777995
theorem B2026939 : Blo 1423531 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B7310891 : Blo 1423531 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B3206699 : Blo 1423531 3206699 := bstep (se 1 (by rfl) ⟨2405024, by rfl⟩ : syracuseStep 3206699 = 4810049) B4810049
theorem B13684301 : Blo 1423531 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B6590267 : Blo 1423531 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B10268531 : Blo 1423531 10268531 := bstep (se 1 (by rfl) ⟨7701398, by rfl⟩ : syracuseStep 10268531 = 15402797) B15402797
theorem B4804487 : Blo 1423531 4804487 := bstep (se 1 (by rfl) ⟨3603365, by rfl⟩ : syracuseStep 4804487 = 7206731) B7206731
theorem B3207059 : Blo 1423531 3207059 := bstep (se 1 (by rfl) ⟨2405294, by rfl⟩ : syracuseStep 3207059 = 4810589) B4810589
theorem B5410745 : Blo 1423531 5410745 := bstep (se 2 (by rfl) ⟨2029029, by rfl⟩ : syracuseStep 5410745 = 4058059) B4058059
theorem B3207113 : Blo 1423531 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B15396875 : Blo 1423531 15396875 := bstep (se 1 (by rfl) ⟨11547656, by rfl⟩ : syracuseStep 15396875 = 23095313) B23095313
theorem B13692989 : Blo 1423531 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B2404471 : Blo 1423531 2404471 := bstep (se 1 (by rfl) ⟨1803353, by rfl⟩ : syracuseStep 2404471 = 3606707) B3606707
theorem B1601671 : Blo 1423531 1601671 := bstep (se 1 (by rfl) ⟨1201253, by rfl⟩ : syracuseStep 1601671 = 2402507) B2402507
theorem B4804865 : Blo 1423531 4804865 := bstep (se 2 (by rfl) ⟨1801824, by rfl⟩ : syracuseStep 4804865 = 3603649) B3603649
theorem B17338657 : Blo 1423531 17338657 := bstep (se 2 (by rfl) ⟨6501996, by rfl⟩ : syracuseStep 17338657 = 13003993) B13003993
theorem B1601851 : Blo 1423531 1601851 := bstep (se 1 (by rfl) ⟨1201388, by rfl⟩ : syracuseStep 1601851 = 2402777) B2402777
theorem B2404667 : Blo 1423531 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B2740751 : Blo 1423531 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B2568719 : Blo 1423531 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B2568763 : Blo 1423531 2568763 := bstep (se 1 (by rfl) ⟨1926572, by rfl⟩ : syracuseStep 2568763 = 3853145) B3853145
theorem B3420787 : Blo 1423531 3420787 := bstep (se 1 (by rfl) ⟨2565590, by rfl⟩ : syracuseStep 3420787 = 5131181) B5131181
theorem B3125945 : Blo 1423531 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B2405065 : Blo 1423531 2405065 := bstep (se 2 (by rfl) ⟨901899, by rfl⟩ : syracuseStep 2405065 = 1803799) B1803799
theorem B1602319 : Blo 1423531 1602319 := bstep (se 1 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 1602319 = 2403479) B2403479
theorem B5206799 : Blo 1423531 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B8221499 : Blo 1423531 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B5411731 : Blo 1423531 5411731 := bstep (se 1 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 5411731 = 8117597) B8117597
theorem B16446361 : Blo 1423531 16446361 := bstep (se 2 (by rfl) ⟨6167385, by rfl⟩ : syracuseStep 16446361 = 12334771) B12334771
theorem B20525987 : Blo 1423531 20525987 := bstep (se 1 (by rfl) ⟨15394490, by rfl⟩ : syracuseStep 20525987 = 30788981) B30788981
theorem B69358517 : Blo 1423531 69358517 := bstep (se 5 (by rfl) ⟨3251180, by rfl⟩ : syracuseStep 69358517 = 6502361) B6502361
theorem B3044297 : Blo 1423531 3044297 := bstep (se 2 (by rfl) ⟨1141611, by rfl⟩ : syracuseStep 3044297 = 2283223) B2283223
theorem B13874123 : Blo 1423531 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B4805675 : Blo 1423531 4805675 := bstep (se 1 (by rfl) ⟨3604256, by rfl⟩ : syracuseStep 4805675 = 7208513) B7208513
theorem B16217333 : Blo 1423531 16217333 := bstep (se 5 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 16217333 = 1520375) B1520375
theorem B2135303 : Blo 1423531 2135303 := bstep (se 1 (by rfl) ⟨1601477, by rfl⟩ : syracuseStep 2135303 = 3202955) B3202955
theorem B1602823 : Blo 1423531 1602823 := bstep (se 1 (by rfl) ⟨1202117, by rfl⟩ : syracuseStep 1602823 = 2404235) B2404235
theorem B2135339 : Blo 1423531 2135339 := bstep (se 1 (by rfl) ⟨1601504, by rfl⟩ : syracuseStep 2135339 = 3203009) B3203009
theorem B3249467 : Blo 1423531 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B2135369 : Blo 1423531 2135369 := bstep (se 2 (by rfl) ⟨800763, by rfl⟩ : syracuseStep 2135369 = 1601527) B1601527
theorem B4330871 : Blo 1423531 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B2135483 : Blo 1423531 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B1603003 : Blo 1423531 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B8779229 : Blo 1423531 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B2135543 : Blo 1423531 2135543 := bstep (se 1 (by rfl) ⟨1601657, by rfl⟩ : syracuseStep 2135543 = 3203315) B3203315
theorem B31233539 : Blo 1423531 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B2135567 : Blo 1423531 2135567 := bstep (se 1 (by rfl) ⟨1601675, by rfl⟩ : syracuseStep 2135567 = 3203351) B3203351
theorem B2283023 : Blo 1423531 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B3126817 : Blo 1423531 3126817 := bstep (se 2 (by rfl) ⟨1172556, by rfl⟩ : syracuseStep 3126817 = 2345113) B2345113
theorem B10008107 : Blo 1423531 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B2135609 : Blo 1423531 2135609 := bstep (se 2 (by rfl) ⟨800853, by rfl⟩ : syracuseStep 2135609 = 1601707) B1601707
theorem B2135687 : Blo 1423531 2135687 := bstep (se 1 (by rfl) ⟨1601765, by rfl⟩ : syracuseStep 2135687 = 3203531) B3203531
theorem B2135723 : Blo 1423531 2135723 := bstep (se 1 (by rfl) ⟨1601792, by rfl⟩ : syracuseStep 2135723 = 3203585) B3203585
theorem B2135753 : Blo 1423531 2135753 := bstep (se 2 (by rfl) ⟨800907, by rfl⟩ : syracuseStep 2135753 = 1601815) B1601815
theorem B2029303 : Blo 1423531 2029303 := bstep (se 1 (by rfl) ⟨1521977, by rfl⟩ : syracuseStep 2029303 = 3043955) B3043955
theorem B2135867 : Blo 1423531 2135867 := bstep (se 1 (by rfl) ⟨1601900, by rfl⟩ : syracuseStep 2135867 = 3203801) B3203801
theorem B126613313 : Blo 1423531 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B7313267 : Blo 1423531 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B27383669 : Blo 1423531 27383669 := bstep (se 5 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 27383669 = 2567219) B2567219
theorem B2135927 : Blo 1423531 2135927 := bstep (se 1 (by rfl) ⟨1601945, by rfl⟩ : syracuseStep 2135927 = 3203891) B3203891
theorem B1734535 : Blo 1423531 1734535 := bstep (se 1 (by rfl) ⟨1300901, by rfl⟩ : syracuseStep 1734535 = 2601803) B2601803
theorem B2135951 : Blo 1423531 2135951 := bstep (se 1 (by rfl) ⟨1601963, by rfl⟩ : syracuseStep 2135951 = 3203927) B3203927
theorem B1603471 : Blo 1423531 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B7214993 : Blo 1423531 7214993 := bstep (se 2 (by rfl) ⟨2705622, by rfl⟩ : syracuseStep 7214993 = 5411245) B5411245
theorem B2135993 : Blo 1423531 2135993 := bstep (se 2 (by rfl) ⟨800997, by rfl⟩ : syracuseStep 2135993 = 1601995) B1601995
theorem B2136071 : Blo 1423531 2136071 := bstep (se 1 (by rfl) ⟨1602053, by rfl⟩ : syracuseStep 2136071 = 3204107) B3204107
theorem B2136107 : Blo 1423531 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B2029627 : Blo 1423531 2029627 := bstep (se 1 (by rfl) ⟨1522220, by rfl⟩ : syracuseStep 2029627 = 3044441) B3044441
theorem B3905597 : Blo 1423531 3905597 := bstep (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) B1464599
theorem B8108099 : Blo 1423531 8108099 := bstep (se 1 (by rfl) ⟨6081074, by rfl⟩ : syracuseStep 8108099 = 12162149) B12162149
theorem B2136137 : Blo 1423531 2136137 := bstep (se 2 (by rfl) ⟨801051, by rfl⟩ : syracuseStep 2136137 = 1602103) B1602103
theorem B1423547 : Blo 1423531 1423547 := bstep (se 1 (by rfl) ⟨1067660, by rfl⟩ : syracuseStep 1423547 = 2135321) B2135321
theorem B2136251 : Blo 1423531 2136251 := bstep (se 1 (by rfl) ⟨1602188, by rfl⟩ : syracuseStep 2136251 = 3204377) B3204377
theorem B2136311 : Blo 1423531 2136311 := bstep (se 1 (by rfl) ⟨1602233, by rfl⟩ : syracuseStep 2136311 = 3204467) B3204467
theorem B1423623 : Blo 1423531 1423623 := bstep (se 1 (by rfl) ⟨1067717, by rfl⟩ : syracuseStep 1423623 = 2135435) B2135435
theorem B1423631 : Blo 1423531 1423631 := bstep (se 1 (by rfl) ⟨1067723, by rfl⟩ : syracuseStep 1423631 = 2135447) B2135447
theorem B2136335 : Blo 1423531 2136335 := bstep (se 1 (by rfl) ⟨1602251, by rfl⟩ : syracuseStep 2136335 = 3204503) B3204503
theorem B2136377 : Blo 1423531 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B4806971 : Blo 1423531 4806971 := bstep (se 1 (by rfl) ⟨3605228, by rfl⟩ : syracuseStep 4806971 = 7210457) B7210457
theorem B1423675 : Blo 1423531 1423675 := bstep (se 1 (by rfl) ⟨1067756, by rfl⟩ : syracuseStep 1423675 = 2135513) B2135513
theorem B8116595 : Blo 1423531 8116595 := bstep (se 1 (by rfl) ⟨6087446, by rfl⟩ : syracuseStep 8116595 = 12174893) B12174893
theorem B1423751 : Blo 1423531 1423751 := bstep (se 1 (by rfl) ⟨1067813, by rfl⟩ : syracuseStep 1423751 = 2135627) B2135627
theorem B2136455 : Blo 1423531 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B5134727 : Blo 1423531 5134727 := bstep (se 1 (by rfl) ⟨3851045, by rfl⟩ : syracuseStep 5134727 = 7702091) B7702091
theorem B1423759 : Blo 1423531 1423759 := bstep (se 1 (by rfl) ⟨1067819, by rfl⟩ : syracuseStep 1423759 = 2135639) B2135639
theorem B2136491 : Blo 1423531 2136491 := bstep (se 1 (by rfl) ⟨1602368, by rfl⟩ : syracuseStep 2136491 = 3204737) B3204737
theorem B1423803 : Blo 1423531 1423803 := bstep (se 1 (by rfl) ⟨1067852, by rfl⟩ : syracuseStep 1423803 = 2135705) B2135705
theorem B2136521 : Blo 1423531 2136521 := bstep (se 2 (by rfl) ⟨801195, by rfl⟩ : syracuseStep 2136521 = 1602391) B1602391
theorem B1423879 : Blo 1423531 1423879 := bstep (se 1 (by rfl) ⟨1067909, by rfl⟩ : syracuseStep 1423879 = 2135819) B2135819
theorem B1423887 : Blo 1423531 1423887 := bstep (se 1 (by rfl) ⟨1067915, by rfl⟩ : syracuseStep 1423887 = 2135831) B2135831
theorem B7305757 : Blo 1423531 7305757 := bstep (se 3 (by rfl) ⟨1369829, by rfl⟩ : syracuseStep 7305757 = 2739659) B2739659
theorem B13687339 : Blo 1423531 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B1423931 : Blo 1423531 1423931 := bstep (se 1 (by rfl) ⟨1067948, by rfl⟩ : syracuseStep 1423931 = 2135897) B2135897
theorem B2136635 : Blo 1423531 2136635 := bstep (se 1 (by rfl) ⟨1602476, by rfl⟩ : syracuseStep 2136635 = 3204953) B3204953
theorem B2136695 : Blo 1423531 2136695 := bstep (se 1 (by rfl) ⟨1602521, by rfl⟩ : syracuseStep 2136695 = 3205043) B3205043
theorem B1424007 : Blo 1423531 1424007 := bstep (se 1 (by rfl) ⟨1068005, by rfl⟩ : syracuseStep 1424007 = 2136011) B2136011
theorem B1424015 : Blo 1423531 1424015 := bstep (se 1 (by rfl) ⟨1068011, by rfl⟩ : syracuseStep 1424015 = 2136023) B2136023
theorem B2136719 : Blo 1423531 2136719 := bstep (se 1 (by rfl) ⟨1602539, by rfl⟩ : syracuseStep 2136719 = 3205079) B3205079
theorem B2136761 : Blo 1423531 2136761 := bstep (se 2 (by rfl) ⟨801285, by rfl⟩ : syracuseStep 2136761 = 1602571) B1602571
theorem B1424059 : Blo 1423531 1424059 := bstep (se 1 (by rfl) ⟨1068044, by rfl⟩ : syracuseStep 1424059 = 2136089) B2136089
theorem B9124609 : Blo 1423531 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B1424135 : Blo 1423531 1424135 := bstep (se 1 (by rfl) ⟨1068101, by rfl⟩ : syracuseStep 1424135 = 2136203) B2136203
theorem B2136839 : Blo 1423531 2136839 := bstep (se 1 (by rfl) ⟨1602629, by rfl⟩ : syracuseStep 2136839 = 3205259) B3205259
theorem B1424143 : Blo 1423531 1424143 := bstep (se 1 (by rfl) ⟨1068107, by rfl⟩ : syracuseStep 1424143 = 2136215) B2136215
theorem B4807457 : Blo 1423531 4807457 := bstep (se 2 (by rfl) ⟨1802796, by rfl⟩ : syracuseStep 4807457 = 3605593) B3605593
theorem B2136875 : Blo 1423531 2136875 := bstep (se 1 (by rfl) ⟨1602656, by rfl⟩ : syracuseStep 2136875 = 3205313) B3205313
theorem B1424187 : Blo 1423531 1424187 := bstep (se 1 (by rfl) ⟨1068140, by rfl⟩ : syracuseStep 1424187 = 2136281) B2136281
theorem B2136905 : Blo 1423531 2136905 := bstep (se 2 (by rfl) ⟨801339, by rfl⟩ : syracuseStep 2136905 = 1602679) B1602679
theorem B3849079 : Blo 1423531 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B1424263 : Blo 1423531 1424263 := bstep (se 1 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 1424263 = 2136395) B2136395
theorem B1424271 : Blo 1423531 1424271 := bstep (se 1 (by rfl) ⟨1068203, by rfl⟩ : syracuseStep 1424271 = 2136407) B2136407
theorem B6847379 : Blo 1423531 6847379 := bstep (se 1 (by rfl) ⟨5135534, by rfl⟩ : syracuseStep 6847379 = 10271069) B10271069
theorem B7207865 : Blo 1423531 7207865 := bstep (se 2 (by rfl) ⟨2702949, by rfl⟩ : syracuseStep 7207865 = 5405899) B5405899
theorem B1424315 : Blo 1423531 1424315 := bstep (se 1 (by rfl) ⟨1068236, by rfl⟩ : syracuseStep 1424315 = 2136473) B2136473
theorem B2137019 : Blo 1423531 2137019 := bstep (se 1 (by rfl) ⟨1602764, by rfl⟩ : syracuseStep 2137019 = 3205529) B3205529
theorem B2137079 : Blo 1423531 2137079 := bstep (se 1 (by rfl) ⟨1602809, by rfl⟩ : syracuseStep 2137079 = 3205619) B3205619
theorem B18250757 : Blo 1423531 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B1424391 : Blo 1423531 1424391 := bstep (se 1 (by rfl) ⟨1068293, by rfl⟩ : syracuseStep 1424391 = 2136587) B2136587
theorem B26000389 : Blo 1423531 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B3603467 : Blo 1423531 3603467 := bstep (se 1 (by rfl) ⟨2702600, by rfl⟩ : syracuseStep 3603467 = 5405201) B5405201
theorem B1424399 : Blo 1423531 1424399 := bstep (se 1 (by rfl) ⟨1068299, by rfl⟩ : syracuseStep 1424399 = 2136599) B2136599
theorem B2137103 : Blo 1423531 2137103 := bstep (se 1 (by rfl) ⟨1602827, by rfl⟩ : syracuseStep 2137103 = 3205655) B3205655
theorem B2137145 : Blo 1423531 2137145 := bstep (se 2 (by rfl) ⟨801429, by rfl⟩ : syracuseStep 2137145 = 1602859) B1602859
theorem B1424443 : Blo 1423531 1424443 := bstep (se 1 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 1424443 = 2136665) B2136665
theorem B4054151 : Blo 1423531 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B1424519 : Blo 1423531 1424519 := bstep (se 1 (by rfl) ⟨1068389, by rfl⟩ : syracuseStep 1424519 = 2136779) B2136779
theorem B2137223 : Blo 1423531 2137223 := bstep (se 1 (by rfl) ⟨1602917, by rfl⟩ : syracuseStep 2137223 = 3205835) B3205835
theorem B1424527 : Blo 1423531 1424527 := bstep (se 1 (by rfl) ⟨1068395, by rfl⟩ : syracuseStep 1424527 = 2136791) B2136791
theorem B2137259 : Blo 1423531 2137259 := bstep (se 1 (by rfl) ⟨1602944, by rfl⟩ : syracuseStep 2137259 = 3205889) B3205889
theorem B1424571 : Blo 1423531 1424571 := bstep (se 1 (by rfl) ⟨1068428, by rfl⟩ : syracuseStep 1424571 = 2136857) B2136857
theorem B2137289 : Blo 1423531 2137289 := bstep (se 2 (by rfl) ⟨801483, by rfl⟩ : syracuseStep 2137289 = 1602967) B1602967
theorem B1424647 : Blo 1423531 1424647 := bstep (se 1 (by rfl) ⟨1068485, by rfl⟩ : syracuseStep 1424647 = 2136971) B2136971
theorem B1424655 : Blo 1423531 1424655 := bstep (se 1 (by rfl) ⟨1068491, by rfl⟩ : syracuseStep 1424655 = 2136983) B2136983
theorem B4332815 : Blo 1423531 4332815 := bstep (se 1 (by rfl) ⟨3249611, by rfl⟩ : syracuseStep 4332815 = 6499223) B6499223
theorem B1424699 : Blo 1423531 1424699 := bstep (se 1 (by rfl) ⟨1068524, by rfl⟩ : syracuseStep 1424699 = 2137049) B2137049
theorem B2137403 : Blo 1423531 2137403 := bstep (se 1 (by rfl) ⟨1603052, by rfl⟩ : syracuseStep 2137403 = 3206105) B3206105
theorem B4808051 : Blo 1423531 4808051 := bstep (se 1 (by rfl) ⟨3606038, by rfl⟩ : syracuseStep 4808051 = 7212077) B7212077
theorem B2137463 : Blo 1423531 2137463 := bstep (se 1 (by rfl) ⟨1603097, by rfl⟩ : syracuseStep 2137463 = 3206195) B3206195
theorem B1424775 : Blo 1423531 1424775 := bstep (se 1 (by rfl) ⟨1068581, by rfl⟩ : syracuseStep 1424775 = 2137163) B2137163
theorem B1424783 : Blo 1423531 1424783 := bstep (se 1 (by rfl) ⟨1068587, by rfl⟩ : syracuseStep 1424783 = 2137175) B2137175
theorem B2137487 : Blo 1423531 2137487 := bstep (se 1 (by rfl) ⟨1603115, by rfl⟩ : syracuseStep 2137487 = 3206231) B3206231
theorem B2137529 : Blo 1423531 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B1424827 : Blo 1423531 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B10272221 : Blo 1423531 10272221 := bstep (se 3 (by rfl) ⟨1926041, by rfl⟩ : syracuseStep 10272221 = 3852083) B3852083
theorem B1424903 : Blo 1423531 1424903 := bstep (se 1 (by rfl) ⟨1068677, by rfl⟩ : syracuseStep 1424903 = 2137355) B2137355
theorem B2137607 : Blo 1423531 2137607 := bstep (se 1 (by rfl) ⟨1603205, by rfl⟩ : syracuseStep 2137607 = 3206411) B3206411
theorem B1424911 : Blo 1423531 1424911 := bstep (se 1 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 1424911 = 2137367) B2137367
theorem B2137643 : Blo 1423531 2137643 := bstep (se 1 (by rfl) ⟨1603232, by rfl⟩ : syracuseStep 2137643 = 3206465) B3206465
theorem B1424955 : Blo 1423531 1424955 := bstep (se 1 (by rfl) ⟨1068716, by rfl⟩ : syracuseStep 1424955 = 2137433) B2137433
theorem B2137673 : Blo 1423531 2137673 := bstep (se 2 (by rfl) ⟨801627, by rfl⟩ : syracuseStep 2137673 = 1603255) B1603255
theorem B3423863 : Blo 1423531 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B1425031 : Blo 1423531 1425031 := bstep (se 1 (by rfl) ⟨1068773, by rfl⟩ : syracuseStep 1425031 = 2137547) B2137547
theorem B1425039 : Blo 1423531 1425039 := bstep (se 1 (by rfl) ⟨1068779, by rfl⟩ : syracuseStep 1425039 = 2137559) B2137559
theorem B3604115 : Blo 1423531 3604115 := bstep (se 1 (by rfl) ⟨2703086, by rfl⟩ : syracuseStep 3604115 = 5406173) B5406173
theorem B1711787 : Blo 1423531 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B26336947 : Blo 1423531 26336947 := bstep (se 1 (by rfl) ⟨19752710, by rfl⟩ : syracuseStep 26336947 = 39505421) B39505421
theorem B1425083 : Blo 1423531 1425083 := bstep (se 1 (by rfl) ⟨1068812, by rfl⟩ : syracuseStep 1425083 = 2137625) B2137625
theorem B2137787 : Blo 1423531 2137787 := bstep (se 1 (by rfl) ⟨1603340, by rfl⟩ : syracuseStep 2137787 = 3206681) B3206681
theorem B2137847 : Blo 1423531 2137847 := bstep (se 1 (by rfl) ⟨1603385, by rfl⟩ : syracuseStep 2137847 = 3206771) B3206771
theorem B1425159 : Blo 1423531 1425159 := bstep (se 1 (by rfl) ⟨1068869, by rfl⟩ : syracuseStep 1425159 = 2137739) B2137739
theorem B1425167 : Blo 1423531 1425167 := bstep (se 1 (by rfl) ⟨1068875, by rfl⟩ : syracuseStep 1425167 = 2137751) B2137751
theorem B2137871 : Blo 1423531 2137871 := bstep (se 1 (by rfl) ⟨1603403, by rfl⟩ : syracuseStep 2137871 = 3206807) B3206807
theorem B8118053 : Blo 1423531 8118053 := bstep (se 4 (by rfl) ⟨761067, by rfl⟩ : syracuseStep 8118053 = 1522135) B1522135
theorem B1802027 : Blo 1423531 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B2137913 : Blo 1423531 2137913 := bstep (se 2 (by rfl) ⟨801717, by rfl⟩ : syracuseStep 2137913 = 1603435) B1603435
theorem B1425211 : Blo 1423531 1425211 := bstep (se 1 (by rfl) ⟨1068908, by rfl⟩ : syracuseStep 1425211 = 2137817) B2137817
theorem B2703223 : Blo 1423531 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B1425287 : Blo 1423531 1425287 := bstep (se 1 (by rfl) ⟨1068965, by rfl⟩ : syracuseStep 1425287 = 2137931) B2137931
theorem B2137991 : Blo 1423531 2137991 := bstep (se 1 (by rfl) ⟨1603493, by rfl⟩ : syracuseStep 2137991 = 3206987) B3206987
theorem B1425295 : Blo 1423531 1425295 := bstep (se 1 (by rfl) ⟨1068971, by rfl⟩ : syracuseStep 1425295 = 2137943) B2137943
theorem B2138027 : Blo 1423531 2138027 := bstep (se 1 (by rfl) ⟨1603520, by rfl⟩ : syracuseStep 2138027 = 3207041) B3207041
theorem B3604409 : Blo 1423531 3604409 := bstep (se 2 (by rfl) ⟨1351653, by rfl⟩ : syracuseStep 3604409 = 2703307) B2703307
theorem B1425339 : Blo 1423531 1425339 := bstep (se 1 (by rfl) ⟨1069004, by rfl⟩ : syracuseStep 1425339 = 2138009) B2138009
theorem B2138057 : Blo 1423531 2138057 := bstep (se 2 (by rfl) ⟨801771, by rfl⟩ : syracuseStep 2138057 = 1603543) B1603543
theorem B3653639 : Blo 1423531 3653639 := bstep (se 1 (by rfl) ⟨2740229, by rfl⟩ : syracuseStep 3653639 = 5480459) B5480459
theorem B10264583 : Blo 1423531 10264583 := bstep (se 1 (by rfl) ⟨7698437, by rfl⟩ : syracuseStep 10264583 = 15396875) B15396875
theorem B1425447 : Blo 1423531 1425447 := bstep (se 1 (by rfl) ⟨1069085, by rfl⟩ : syracuseStep 1425447 = 2138171) B2138171
theorem B1425487 : Blo 1423531 1425487 := bstep (se 1 (by rfl) ⟨1069115, by rfl⟩ : syracuseStep 1425487 = 2138231) B2138231
theorem B1425503 : Blo 1423531 1425503 := bstep (se 1 (by rfl) ⟨1069127, by rfl⟩ : syracuseStep 1425503 = 2138255) B2138255
theorem B1425531 : Blo 1423531 1425531 := bstep (se 1 (by rfl) ⟨1069148, by rfl⟩ : syracuseStep 1425531 = 2138297) B2138297
theorem B4808861 : Blo 1423531 4808861 := bstep (se 3 (by rfl) ⟨901661, by rfl⟩ : syracuseStep 4808861 = 1803323) B1803323
theorem B3203243 : Blo 1423531 3203243 := bstep (se 1 (by rfl) ⟨2402432, by rfl⟩ : syracuseStep 3203243 = 4804865) B4804865
theorem B23118209 : Blo 1423531 23118209 := bstep (se 2 (by rfl) ⟨8669328, by rfl⟩ : syracuseStep 23118209 = 17338657) B17338657
theorem B10813985 : Blo 1423531 10813985 := bstep (se 2 (by rfl) ⟨4055244, by rfl⟩ : syracuseStep 10813985 = 8110489) B8110489
theorem B5480999 : Blo 1423531 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B2704043 : Blo 1423531 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B4809401 : Blo 1423531 4809401 := bstep (se 2 (by rfl) ⟨1803525, by rfl⟩ : syracuseStep 4809401 = 3607051) B3607051
theorem B3203783 : Blo 1423531 3203783 := bstep (se 1 (by rfl) ⟨2402837, by rfl⟩ : syracuseStep 3203783 = 4805675) B4805675
theorem B3425017 : Blo 1423531 3425017 := bstep (se 2 (by rfl) ⟨1284381, by rfl⟩ : syracuseStep 3425017 = 2568763) B2568763
theorem B3605431 : Blo 1423531 3605431 := bstep (se 1 (by rfl) ⟨2704073, by rfl⟩ : syracuseStep 3605431 = 5408147) B5408147
theorem B12166145 : Blo 1423531 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B2704423 : Blo 1423531 2704423 := bstep (se 1 (by rfl) ⟨2028317, by rfl⟩ : syracuseStep 2704423 = 4056635) B4056635
theorem B2704583 : Blo 1423531 2704583 := bstep (se 1 (by rfl) ⟨2028437, by rfl⟩ : syracuseStep 2704583 = 4056875) B4056875
theorem B4809995 : Blo 1423531 4809995 := bstep (se 1 (by rfl) ⟨3607496, by rfl⟩ : syracuseStep 4809995 = 7214993) B7214993
theorem B6088061 : Blo 1423531 6088061 := bstep (se 3 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 6088061 = 2283023) B2283023
theorem B6849917 : Blo 1423531 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B1803703 : Blo 1423531 1803703 := bstep (se 1 (by rfl) ⟨1352777, by rfl⟩ : syracuseStep 1803703 = 2705555) B2705555
theorem B16221707 : Blo 1423531 16221707 := bstep (se 1 (by rfl) ⟨12166280, by rfl⟩ : syracuseStep 16221707 = 24332561) B24332561
theorem B4056601 : Blo 1423531 4056601 := bstep (se 2 (by rfl) ⟨1521225, by rfl⟩ : syracuseStep 4056601 = 3042451) B3042451
theorem B4810265 : Blo 1423531 4810265 := bstep (se 2 (by rfl) ⟨1803849, by rfl⟩ : syracuseStep 4810265 = 3607699) B3607699
theorem B3204647 : Blo 1423531 3204647 := bstep (se 1 (by rfl) ⟨2403485, by rfl⟩ : syracuseStep 3204647 = 4806971) B4806971
theorem B5408315 : Blo 1423531 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B7210619 : Blo 1423531 7210619 := bstep (se 1 (by rfl) ⟨5407964, by rfl⟩ : syracuseStep 7210619 = 10815929) B10815929
theorem B70223507 : Blo 1423531 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B4564765 : Blo 1423531 4564765 := bstep (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) B1711787
theorem B36505403 : Blo 1423531 36505403 := bstep (se 1 (by rfl) ⟨27379052, by rfl⟩ : syracuseStep 36505403 = 54758105) B54758105
theorem B3852127 : Blo 1423531 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B3204971 : Blo 1423531 3204971 := bstep (se 1 (by rfl) ⟨2403728, by rfl⟩ : syracuseStep 3204971 = 4807457) B4807457
theorem B3205025 : Blo 1423531 3205025 := bstep (se 2 (by rfl) ⟨1201884, by rfl⟩ : syracuseStep 3205025 = 2403769) B2403769
theorem B4564919 : Blo 1423531 4564919 := bstep (se 1 (by rfl) ⟨3423689, by rfl⟩ : syracuseStep 4564919 = 6847379) B6847379
theorem B12167171 : Blo 1423531 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B2402311 : Blo 1423531 2402311 := bstep (se 1 (by rfl) ⟨1801733, by rfl⟩ : syracuseStep 2402311 = 3603467) B3603467
theorem B4114451 : Blo 1423531 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B7702609 : Blo 1423531 7702609 := bstep (se 2 (by rfl) ⟨2888478, by rfl⟩ : syracuseStep 7702609 = 5776957) B5776957
theorem B3205367 : Blo 1423531 3205367 := bstep (se 1 (by rfl) ⟨2404025, by rfl⟩ : syracuseStep 3205367 = 4808051) B4808051
theorem B2705737 : Blo 1423531 2705737 := bstep (se 2 (by rfl) ⟨1014651, by rfl⟩ : syracuseStep 2705737 = 2029303) B2029303
theorem B3606889 : Blo 1423531 3606889 := bstep (se 2 (by rfl) ⟨1352583, by rfl⟩ : syracuseStep 3606889 = 2705167) B2705167
theorem B2402743 : Blo 1423531 2402743 := bstep (se 1 (by rfl) ⟨1802057, by rfl⟩ : syracuseStep 2402743 = 3604115) B3604115
theorem B2312713 : Blo 1423531 2312713 := bstep (se 2 (by rfl) ⟨867267, by rfl⟩ : syracuseStep 2312713 = 1734535) B1734535
theorem B36997661 : Blo 1423531 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B4393511 : Blo 1423531 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B2402939 : Blo 1423531 2402939 := bstep (se 1 (by rfl) ⟨1802204, by rfl⟩ : syracuseStep 2402939 = 3604409) B3604409
theorem B3607163 : Blo 1423531 3607163 := bstep (se 1 (by rfl) ⟨2705372, by rfl⟩ : syracuseStep 3607163 = 5410745) B5410745
theorem B39004865 : Blo 1423531 39004865 := bstep (se 2 (by rfl) ⟨14626824, by rfl⟩ : syracuseStep 39004865 = 29253649) B29253649
theorem B9128659 : Blo 1423531 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B2566903 : Blo 1423531 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B38964037 : Blo 1423531 38964037 := bstep (se 4 (by rfl) ⟨3652878, by rfl⟩ : syracuseStep 38964037 = 7305757) B7305757
theorem B3205961 : Blo 1423531 3205961 := bstep (se 2 (by rfl) ⟨1202235, by rfl⟩ : syracuseStep 3205961 = 2404471) B2404471
theorem B2567017 : Blo 1423531 2567017 := bstep (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) B1925263
theorem B10824677 : Blo 1423531 10824677 := bstep (se 4 (by rfl) ⟨1014813, by rfl⟩ : syracuseStep 10824677 = 2029627) B2029627
theorem B2403337 : Blo 1423531 2403337 := bstep (se 2 (by rfl) ⟨901251, by rfl⟩ : syracuseStep 2403337 = 1802503) B1802503
theorem B2083963 : Blo 1423531 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B2403499 : Blo 1423531 2403499 := bstep (se 1 (by rfl) ⟨1802624, by rfl⟩ : syracuseStep 2403499 = 3605249) B3605249
theorem B13683991 : Blo 1423531 13683991 := bstep (se 1 (by rfl) ⟨10262993, by rfl⟩ : syracuseStep 13683991 = 20525987) B20525987
theorem B46239011 : Blo 1423531 46239011 := bstep (se 1 (by rfl) ⟨34679258, by rfl⟩ : syracuseStep 46239011 = 69358517) B69358517
theorem B2567531 : Blo 1423531 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B2403803 : Blo 1423531 2403803 := bstep (se 1 (by rfl) ⟨1802852, by rfl⟩ : syracuseStep 2403803 = 3605705) B3605705
theorem B2166311 : Blo 1423531 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B2887247 : Blo 1423531 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B3206753 : Blo 1423531 3206753 := bstep (se 2 (by rfl) ⟨1202532, by rfl⟩ : syracuseStep 3206753 = 2405065) B2405065
theorem B10268299 : Blo 1423531 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B5852819 : Blo 1423531 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B43847345 : Blo 1423531 43847345 := bstep (se 2 (by rfl) ⟨16442754, by rfl⟩ : syracuseStep 43847345 = 32885509) B32885509
theorem B6672071 : Blo 1423531 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B2027207 : Blo 1423531 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B2404039 : Blo 1423531 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B16215875 : Blo 1423531 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B5132105 : Blo 1423531 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B2404201 : Blo 1423531 2404201 := bstep (se 2 (by rfl) ⟨901575, by rfl⟩ : syracuseStep 2404201 = 1803151) B1803151
theorem B18255779 : Blo 1423531 18255779 := bstep (se 1 (by rfl) ⟨13691834, by rfl⟩ : syracuseStep 18255779 = 27383669) B27383669
theorem B3207095 : Blo 1423531 3207095 := bstep (se 1 (by rfl) ⟨2405321, by rfl⟩ : syracuseStep 3207095 = 4810643) B4810643
theorem B3469331 : Blo 1423531 3469331 := bstep (se 1 (by rfl) ⟨2601998, by rfl⟩ : syracuseStep 3469331 = 5203997) B5203997
theorem B5411063 : Blo 1423531 5411063 := bstep (se 1 (by rfl) ⟨4058297, by rfl⟩ : syracuseStep 5411063 = 8116595) B8116595
theorem B7213373 : Blo 1423531 7213373 := bstep (se 3 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 7213373 = 2705015) B2705015
theorem B1601887 : Blo 1423531 1601887 := bstep (se 1 (by rfl) ⟨1201415, by rfl⟩ : syracuseStep 1601887 = 2402831) B2402831
theorem B2404795 : Blo 1423531 2404795 := bstep (se 1 (by rfl) ⟨1803596, by rfl⟩ : syracuseStep 2404795 = 3607193) B3607193
theorem B2404903 : Blo 1423531 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B4805243 : Blo 1423531 4805243 := bstep (se 1 (by rfl) ⟨3603932, by rfl⟩ : syracuseStep 4805243 = 7207865) B7207865
theorem B1602247 : Blo 1423531 1602247 := bstep (se 1 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 1602247 = 2403371) B2403371
theorem B4805405 : Blo 1423531 4805405 := bstep (se 3 (by rfl) ⟨901013, by rfl⟩ : syracuseStep 4805405 = 1802027) B1802027
theorem B2888543 : Blo 1423531 2888543 := bstep (se 1 (by rfl) ⟨2166407, by rfl⟩ : syracuseStep 2888543 = 4332815) B4332815
theorem B2405227 : Blo 1423531 2405227 := bstep (se 1 (by rfl) ⟨1803920, by rfl⟩ : syracuseStep 2405227 = 3607841) B3607841
theorem B35115929 : Blo 1423531 35115929 := bstep (se 2 (by rfl) ⟨13168473, by rfl⟩ : syracuseStep 35115929 = 26336947) B26336947
theorem B19502045 : Blo 1423531 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B9122867 : Blo 1423531 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B2282575 : Blo 1423531 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B9122969 : Blo 1423531 9122969 := bstep (se 2 (by rfl) ⟨3421113, by rfl⟩ : syracuseStep 9122969 = 6842227) B6842227
theorem B5412035 : Blo 1423531 5412035 := bstep (se 1 (by rfl) ⟨4059026, by rfl⟩ : syracuseStep 5412035 = 8118053) B8118053
theorem B6845687 : Blo 1423531 6845687 := bstep (se 1 (by rfl) ⟨5134265, by rfl⟩ : syracuseStep 6845687 = 10268531) B10268531
theorem B2135471 : Blo 1423531 2135471 := bstep (se 1 (by rfl) ⟨1601603, by rfl⟩ : syracuseStep 2135471 = 3203207) B3203207
theorem B4806107 : Blo 1423531 4806107 := bstep (se 1 (by rfl) ⟨3604580, by rfl⟩ : syracuseStep 4806107 = 7209161) B7209161
theorem B29234677 : Blo 1423531 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B2135561 : Blo 1423531 2135561 := bstep (se 2 (by rfl) ⟨800835, by rfl⟩ : syracuseStep 2135561 = 1601671) B1601671
theorem B2135591 : Blo 1423531 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B1603111 : Blo 1423531 1603111 := bstep (se 1 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 1603111 = 2404667) B2404667
theorem B2135675 : Blo 1423531 2135675 := bstep (se 1 (by rfl) ⟨1601756, by rfl⟩ : syracuseStep 2135675 = 3203513) B3203513
theorem B5412491 : Blo 1423531 5412491 := bstep (se 1 (by rfl) ⟨4059368, by rfl⟩ : syracuseStep 5412491 = 8118737) B8118737
theorem B12170897 : Blo 1423531 12170897 := bstep (se 2 (by rfl) ⟨4564086, by rfl⟩ : syracuseStep 12170897 = 9128173) B9128173
theorem B10811069 : Blo 1423531 10811069 := bstep (se 3 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 10811069 = 4054151) B4054151
theorem B2135801 : Blo 1423531 2135801 := bstep (se 2 (by rfl) ⟨800925, by rfl⟩ : syracuseStep 2135801 = 1601851) B1601851
theorem B2135903 : Blo 1423531 2135903 := bstep (se 1 (by rfl) ⟨1601927, by rfl⟩ : syracuseStep 2135903 = 3203855) B3203855
theorem B2135915 : Blo 1423531 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B2029531 : Blo 1423531 2029531 := bstep (se 1 (by rfl) ⟨1522148, by rfl⟩ : syracuseStep 2029531 = 3044297) B3044297
theorem B18249785 : Blo 1423531 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B2136143 : Blo 1423531 2136143 := bstep (se 1 (by rfl) ⟨1602107, by rfl⟩ : syracuseStep 2136143 = 3204215) B3204215
theorem B4561049 : Blo 1423531 4561049 := bstep (se 2 (by rfl) ⟨1710393, by rfl⟩ : syracuseStep 4561049 = 3420787) B3420787
theorem B4806809 : Blo 1423531 4806809 := bstep (se 2 (by rfl) ⟨1802553, by rfl⟩ : syracuseStep 4806809 = 3605107) B3605107
theorem B10811555 : Blo 1423531 10811555 := bstep (se 1 (by rfl) ⟨8108666, by rfl⟩ : syracuseStep 10811555 = 16217333) B16217333
theorem B2889899 : Blo 1423531 2889899 := bstep (se 1 (by rfl) ⟨2167424, by rfl⟩ : syracuseStep 2889899 = 4334849) B4334849
theorem B1423535 : Blo 1423531 1423535 := bstep (se 1 (by rfl) ⟨1067651, by rfl⟩ : syracuseStep 1423535 = 2135303) B2135303
theorem B1423559 : Blo 1423531 1423559 := bstep (se 1 (by rfl) ⟨1067669, by rfl⟩ : syracuseStep 1423559 = 2135339) B2135339
theorem B2136263 : Blo 1423531 2136263 := bstep (se 1 (by rfl) ⟨1602197, by rfl⟩ : syracuseStep 2136263 = 3204395) B3204395
theorem B1423579 : Blo 1423531 1423579 := bstep (se 1 (by rfl) ⟨1067684, by rfl⟩ : syracuseStep 1423579 = 2135369) B2135369
theorem B1423655 : Blo 1423531 1423655 := bstep (se 1 (by rfl) ⟨1067741, by rfl⟩ : syracuseStep 1423655 = 2135483) B2135483
theorem B2742601 : Blo 1423531 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B1423695 : Blo 1423531 1423695 := bstep (se 1 (by rfl) ⟨1067771, by rfl⟩ : syracuseStep 1423695 = 2135543) B2135543
theorem B20822359 : Blo 1423531 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B1423711 : Blo 1423531 1423711 := bstep (se 1 (by rfl) ⟨1067783, by rfl⟩ : syracuseStep 1423711 = 2135567) B2135567
theorem B2136425 : Blo 1423531 2136425 := bstep (se 2 (by rfl) ⟨801159, by rfl⟩ : syracuseStep 2136425 = 1602319) B1602319
theorem B1423739 : Blo 1423531 1423739 := bstep (se 1 (by rfl) ⟨1067804, by rfl⟩ : syracuseStep 1423739 = 2135609) B2135609
theorem B1423791 : Blo 1423531 1423791 := bstep (se 1 (by rfl) ⟨1067843, by rfl⟩ : syracuseStep 1423791 = 2135687) B2135687
theorem B2136503 : Blo 1423531 2136503 := bstep (se 1 (by rfl) ⟨1602377, by rfl⟩ : syracuseStep 2136503 = 3204755) B3204755
theorem B1423815 : Blo 1423531 1423815 := bstep (se 1 (by rfl) ⟨1067861, by rfl⟩ : syracuseStep 1423815 = 2135723) B2135723
theorem B1423835 : Blo 1423531 1423835 := bstep (se 1 (by rfl) ⟨1067876, by rfl⟩ : syracuseStep 1423835 = 2135753) B2135753
theorem B2136539 : Blo 1423531 2136539 := bstep (se 1 (by rfl) ⟨1602404, by rfl⟩ : syracuseStep 2136539 = 3204809) B3204809
theorem B7215641 : Blo 1423531 7215641 := bstep (se 2 (by rfl) ⟨2705865, by rfl⟩ : syracuseStep 7215641 = 5411731) B5411731
theorem B21928481 : Blo 1423531 21928481 := bstep (se 2 (by rfl) ⟨8223180, by rfl⟩ : syracuseStep 21928481 = 16446361) B16446361
theorem B1423911 : Blo 1423531 1423911 := bstep (se 1 (by rfl) ⟨1067933, by rfl⟩ : syracuseStep 1423911 = 2135867) B2135867
theorem B84408875 : Blo 1423531 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B1423951 : Blo 1423531 1423951 := bstep (se 1 (by rfl) ⟨1067963, by rfl⟩ : syracuseStep 1423951 = 2135927) B2135927
theorem B1423967 : Blo 1423531 1423967 := bstep (se 1 (by rfl) ⟨1067975, by rfl⟩ : syracuseStep 1423967 = 2135951) B2135951
theorem B1423995 : Blo 1423531 1423995 := bstep (se 1 (by rfl) ⟨1067996, by rfl⟩ : syracuseStep 1423995 = 2135993) B2135993
theorem B1424047 : Blo 1423531 1424047 := bstep (se 1 (by rfl) ⟨1068035, by rfl⟩ : syracuseStep 1424047 = 2136071) B2136071
theorem B34667185 : Blo 1423531 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B1424071 : Blo 1423531 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B2603731 : Blo 1423531 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B5405399 : Blo 1423531 5405399 := bstep (se 1 (by rfl) ⟨4054049, by rfl⟩ : syracuseStep 5405399 = 8108099) B8108099
theorem B1424091 : Blo 1423531 1424091 := bstep (se 1 (by rfl) ⟨1068068, by rfl⟩ : syracuseStep 1424091 = 2136137) B2136137
theorem B1424167 : Blo 1423531 1424167 := bstep (se 1 (by rfl) ⟨1068125, by rfl⟩ : syracuseStep 1424167 = 2136251) B2136251
theorem B4053833 : Blo 1423531 4053833 := bstep (se 2 (by rfl) ⟨1520187, by rfl⟩ : syracuseStep 4053833 = 3040375) B3040375
theorem B1424207 : Blo 1423531 1424207 := bstep (se 1 (by rfl) ⟨1068155, by rfl⟩ : syracuseStep 1424207 = 2136311) B2136311
theorem B1424223 : Blo 1423531 1424223 := bstep (se 1 (by rfl) ⟨1068167, by rfl⟩ : syracuseStep 1424223 = 2136335) B2136335
theorem B1424251 : Blo 1423531 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B1424303 : Blo 1423531 1424303 := bstep (se 1 (by rfl) ⟨1068227, by rfl⟩ : syracuseStep 1424303 = 2136455) B2136455
theorem B2137007 : Blo 1423531 2137007 := bstep (se 1 (by rfl) ⟨1602755, by rfl⟩ : syracuseStep 2137007 = 3205511) B3205511
theorem B3423151 : Blo 1423531 3423151 := bstep (se 1 (by rfl) ⟨2567363, by rfl⟩ : syracuseStep 3423151 = 5134727) B5134727
theorem B1424327 : Blo 1423531 1424327 := bstep (se 1 (by rfl) ⟨1068245, by rfl⟩ : syracuseStep 1424327 = 2136491) B2136491
theorem B1424347 : Blo 1423531 1424347 := bstep (se 1 (by rfl) ⟨1068260, by rfl⟩ : syracuseStep 1424347 = 2136521) B2136521
theorem B2137097 : Blo 1423531 2137097 := bstep (se 2 (by rfl) ⟨801411, by rfl⟩ : syracuseStep 2137097 = 1602823) B1602823
theorem B1424423 : Blo 1423531 1424423 := bstep (se 1 (by rfl) ⟨1068317, by rfl⟩ : syracuseStep 1424423 = 2136635) B2136635
theorem B2137127 : Blo 1423531 2137127 := bstep (se 1 (by rfl) ⟨1602845, by rfl⟩ : syracuseStep 2137127 = 3205691) B3205691
theorem B1424463 : Blo 1423531 1424463 := bstep (se 1 (by rfl) ⟨1068347, by rfl⟩ : syracuseStep 1424463 = 2136695) B2136695
theorem B1424479 : Blo 1423531 1424479 := bstep (se 1 (by rfl) ⟨1068359, by rfl⟩ : syracuseStep 1424479 = 2136719) B2136719
theorem B1424507 : Blo 1423531 1424507 := bstep (se 1 (by rfl) ⟨1068380, by rfl⟩ : syracuseStep 1424507 = 2136761) B2136761
theorem B2137211 : Blo 1423531 2137211 := bstep (se 1 (by rfl) ⟨1602908, by rfl⟩ : syracuseStep 2137211 = 3205817) B3205817
theorem B1424559 : Blo 1423531 1424559 := bstep (se 1 (by rfl) ⟨1068419, by rfl⟩ : syracuseStep 1424559 = 2136839) B2136839
theorem B1424583 : Blo 1423531 1424583 := bstep (se 1 (by rfl) ⟨1068437, by rfl⟩ : syracuseStep 1424583 = 2136875) B2136875
theorem B1424603 : Blo 1423531 1424603 := bstep (se 1 (by rfl) ⟨1068452, by rfl⟩ : syracuseStep 1424603 = 2136905) B2136905
theorem B2702585 : Blo 1423531 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B2137337 : Blo 1423531 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B1424679 : Blo 1423531 1424679 := bstep (se 1 (by rfl) ⟨1068509, by rfl⟩ : syracuseStep 1424679 = 2137019) B2137019
theorem B4807997 : Blo 1423531 4807997 := bstep (se 3 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 4807997 = 1802999) B1802999
theorem B1424719 : Blo 1423531 1424719 := bstep (se 1 (by rfl) ⟨1068539, by rfl⟩ : syracuseStep 1424719 = 2137079) B2137079
theorem B1424735 : Blo 1423531 1424735 := bstep (se 1 (by rfl) ⟨1068551, by rfl⟩ : syracuseStep 1424735 = 2137103) B2137103
theorem B2137439 : Blo 1423531 2137439 := bstep (se 1 (by rfl) ⟨1603079, by rfl⟩ : syracuseStep 2137439 = 3206159) B3206159
theorem B2137451 : Blo 1423531 2137451 := bstep (se 1 (by rfl) ⟨1603088, by rfl⟩ : syracuseStep 2137451 = 3206177) B3206177
theorem B1424763 : Blo 1423531 1424763 := bstep (se 1 (by rfl) ⟨1068572, by rfl⟩ : syracuseStep 1424763 = 2137145) B2137145
theorem B13884797 : Blo 1423531 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B4169089 : Blo 1423531 4169089 := bstep (se 2 (by rfl) ⟨1563408, by rfl⟩ : syracuseStep 4169089 = 3126817) B3126817
theorem B1424815 : Blo 1423531 1424815 := bstep (se 1 (by rfl) ⟨1068611, by rfl⟩ : syracuseStep 1424815 = 2137223) B2137223
theorem B1424839 : Blo 1423531 1424839 := bstep (se 1 (by rfl) ⟨1068629, by rfl⟩ : syracuseStep 1424839 = 2137259) B2137259
theorem B1924571 : Blo 1423531 1924571 := bstep (se 1 (by rfl) ⟨1443428, by rfl⟩ : syracuseStep 1924571 = 2886857) B2886857
theorem B1424859 : Blo 1423531 1424859 := bstep (se 1 (by rfl) ⟨1068644, by rfl⟩ : syracuseStep 1424859 = 2137289) B2137289
theorem B15392243 : Blo 1423531 15392243 := bstep (se 1 (by rfl) ⟨11544182, by rfl⟩ : syracuseStep 15392243 = 23088365) B23088365
theorem B1424935 : Blo 1423531 1424935 := bstep (se 1 (by rfl) ⟨1068701, by rfl⟩ : syracuseStep 1424935 = 2137403) B2137403
theorem B1424975 : Blo 1423531 1424975 := bstep (se 1 (by rfl) ⟨1068731, by rfl⟩ : syracuseStep 1424975 = 2137463) B2137463
theorem B2137679 : Blo 1423531 2137679 := bstep (se 1 (by rfl) ⟨1603259, by rfl⟩ : syracuseStep 2137679 = 3206519) B3206519
theorem B1424991 : Blo 1423531 1424991 := bstep (se 1 (by rfl) ⟨1068743, by rfl⟩ : syracuseStep 1424991 = 2137487) B2137487
theorem B1425019 : Blo 1423531 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B5135995 : Blo 1423531 5135995 := bstep (se 1 (by rfl) ⟨3851996, by rfl⟩ : syracuseStep 5135995 = 7703993) B7703993
theorem B6848147 : Blo 1423531 6848147 := bstep (se 1 (by rfl) ⟨5136110, by rfl⟩ : syracuseStep 6848147 = 10272221) B10272221
theorem B1425071 : Blo 1423531 1425071 := bstep (se 1 (by rfl) ⟨1068803, by rfl⟩ : syracuseStep 1425071 = 2137607) B2137607
theorem B4873927 : Blo 1423531 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B1425095 : Blo 1423531 1425095 := bstep (se 1 (by rfl) ⟨1068821, by rfl⟩ : syracuseStep 1425095 = 2137643) B2137643
theorem B2137799 : Blo 1423531 2137799 := bstep (se 1 (by rfl) ⟨1603349, by rfl⟩ : syracuseStep 2137799 = 3206699) B3206699
theorem B1425115 : Blo 1423531 1425115 := bstep (se 1 (by rfl) ⟨1068836, by rfl⟩ : syracuseStep 1425115 = 2137673) B2137673
theorem B1425191 : Blo 1423531 1425191 := bstep (se 1 (by rfl) ⟨1068893, by rfl⟩ : syracuseStep 1425191 = 2137787) B2137787
theorem B3604297 : Blo 1423531 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B1425231 : Blo 1423531 1425231 := bstep (se 1 (by rfl) ⟨1068923, by rfl⟩ : syracuseStep 1425231 = 2137847) B2137847
theorem B1425247 : Blo 1423531 1425247 := bstep (se 1 (by rfl) ⟨1068935, by rfl⟩ : syracuseStep 1425247 = 2137871) B2137871
theorem B2137961 : Blo 1423531 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B1425275 : Blo 1423531 1425275 := bstep (se 1 (by rfl) ⟨1068956, by rfl⟩ : syracuseStep 1425275 = 2137913) B2137913
theorem B3202991 : Blo 1423531 3202991 := bstep (se 1 (by rfl) ⟨2402243, by rfl⟩ : syracuseStep 3202991 = 4804487) B4804487
theorem B1425327 : Blo 1423531 1425327 := bstep (se 1 (by rfl) ⟨1068995, by rfl⟩ : syracuseStep 1425327 = 2137991) B2137991
theorem B2138039 : Blo 1423531 2138039 := bstep (se 1 (by rfl) ⟨1603529, by rfl⟩ : syracuseStep 2138039 = 3207059) B3207059
theorem B1425351 : Blo 1423531 1425351 := bstep (se 1 (by rfl) ⟨1069013, by rfl⟩ : syracuseStep 1425351 = 2138027) B2138027
theorem B1425371 : Blo 1423531 1425371 := bstep (se 1 (by rfl) ⟨1069028, by rfl⟩ : syracuseStep 1425371 = 2138057) B2138057
theorem B2138075 : Blo 1423531 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B3203081 : Blo 1423531 3203081 := bstep (se 2 (by rfl) ⟨1201155, by rfl⟩ : syracuseStep 3203081 = 2402311) B2402311
theorem B4808915 : Blo 1423531 4808915 := bstep (se 1 (by rfl) ⟨3606686, by rfl⟩ : syracuseStep 4808915 = 7213373) B7213373
theorem B7209323 : Blo 1423531 7209323 := bstep (se 1 (by rfl) ⟨5406992, by rfl⟩ : syracuseStep 7209323 = 10813985) B10813985
theorem B3653999 : Blo 1423531 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B3203495 : Blo 1423531 3203495 := bstep (se 1 (by rfl) ⟨2402621, by rfl⟩ : syracuseStep 3203495 = 4805243) B4805243
theorem B27763145 : Blo 1423531 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B4809185 : Blo 1423531 4809185 := bstep (se 2 (by rfl) ⟨1803444, by rfl⟩ : syracuseStep 4809185 = 3606889) B3606889
theorem B3203603 : Blo 1423531 3203603 := bstep (se 1 (by rfl) ⟨2402702, by rfl⟩ : syracuseStep 3203603 = 4805405) B4805405
theorem B3203657 : Blo 1423531 3203657 := bstep (se 2 (by rfl) ⟨1201371, by rfl⟩ : syracuseStep 3203657 = 2402743) B2402743
theorem B13001363 : Blo 1423531 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B8110763 : Blo 1423531 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B1803055 : Blo 1423531 1803055 := bstep (se 1 (by rfl) ⟨1352291, by rfl⟩ : syracuseStep 1803055 = 2704583) B2704583
theorem B4563791 : Blo 1423531 4563791 := bstep (se 1 (by rfl) ⟨3422843, by rfl⟩ : syracuseStep 4563791 = 6845687) B6845687
theorem B3204071 : Blo 1423531 3204071 := bstep (se 1 (by rfl) ⟨2403053, by rfl⟩ : syracuseStep 3204071 = 4806107) B4806107
theorem B10814471 : Blo 1423531 10814471 := bstep (se 1 (by rfl) ⟨8110853, by rfl⟩ : syracuseStep 10814471 = 16221707) B16221707
theorem B3605543 : Blo 1423531 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B4564201 : Blo 1423531 4564201 := bstep (se 2 (by rfl) ⟨1711575, by rfl⟩ : syracuseStep 4564201 = 3423151) B3423151
theorem B8111447 : Blo 1423531 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B3204449 : Blo 1423531 3204449 := bstep (se 2 (by rfl) ⟨1201668, by rfl⟩ : syracuseStep 3204449 = 2403337) B2403337
theorem B12166523 : Blo 1423531 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B3605897 : Blo 1423531 3605897 := bstep (se 2 (by rfl) ⟨1352211, by rfl⟩ : syracuseStep 3605897 = 2704423) B2704423
theorem B3204539 : Blo 1423531 3204539 := bstep (se 1 (by rfl) ⟨2403404, by rfl⟩ : syracuseStep 3204539 = 4806809) B4806809
theorem B5776829 : Blo 1423531 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B1926599 : Blo 1423531 1926599 := bstep (se 1 (by rfl) ⟨1444949, by rfl⟩ : syracuseStep 1926599 = 2889899) B2889899
theorem B2778617 : Blo 1423531 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B3204665 : Blo 1423531 3204665 := bstep (se 2 (by rfl) ⟨1201749, by rfl⟩ : syracuseStep 3204665 = 2403499) B2403499
theorem B4810427 : Blo 1423531 4810427 := bstep (se 1 (by rfl) ⟨3607820, by rfl⟩ : syracuseStep 4810427 = 7215641) B7215641
theorem B56272583 : Blo 1423531 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B18245321 : Blo 1423531 18245321 := bstep (se 2 (by rfl) ⟨6841995, by rfl⟩ : syracuseStep 18245321 = 13683991) B13683991
theorem B7210781 : Blo 1423531 7210781 := bstep (se 3 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 7210781 = 2704043) B2704043
theorem B26003243 : Blo 1423531 26003243 := bstep (se 1 (by rfl) ⟨19502432, by rfl⟩ : syracuseStep 26003243 = 39004865) B39004865
theorem B13690757 : Blo 1423531 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B38979569 : Blo 1423531 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B22235141 : Blo 1423531 22235141 := bstep (se 4 (by rfl) ⟨2084544, by rfl⟩ : syracuseStep 22235141 = 4169089) B4169089
theorem B5408801 : Blo 1423531 5408801 := bstep (se 2 (by rfl) ⟨2028300, by rfl⟩ : syracuseStep 5408801 = 4056601) B4056601
theorem B13691065 : Blo 1423531 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B3205331 : Blo 1423531 3205331 := bstep (se 1 (by rfl) ⟨2403998, by rfl⟩ : syracuseStep 3205331 = 4807997) B4807997
theorem B7702781 : Blo 1423531 7702781 := bstep (se 3 (by rfl) ⟨1444271, by rfl⟩ : syracuseStep 7702781 = 2888543) B2888543
theorem B3205385 : Blo 1423531 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B6498569 : Blo 1423531 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B3901879 : Blo 1423531 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B4565431 : Blo 1423531 4565431 := bstep (se 1 (by rfl) ⟨3424073, by rfl⟩ : syracuseStep 4565431 = 6848147) B6848147
theorem B29231563 : Blo 1423531 29231563 := bstep (se 1 (by rfl) ⟨21923672, by rfl⟩ : syracuseStep 29231563 = 43847345) B43847345
theorem B3205601 : Blo 1423531 3205601 := bstep (se 2 (by rfl) ⟨1202100, by rfl⟩ : syracuseStep 3205601 = 2404201) B2404201
theorem B2706041 : Blo 1423531 2706041 := bstep (se 2 (by rfl) ⟨1014765, by rfl⟩ : syracuseStep 2706041 = 2029531) B2029531
theorem B2435759 : Blo 1423531 2435759 := bstep (se 1 (by rfl) ⟨1826819, by rfl⟩ : syracuseStep 2435759 = 3653639) B3653639
theorem B6843055 : Blo 1423531 6843055 := bstep (se 1 (by rfl) ⟨5132291, by rfl⟩ : syracuseStep 6843055 = 10264583) B10264583
theorem B2312887 : Blo 1423531 2312887 := bstep (se 1 (by rfl) ⟨1734665, by rfl⟩ : syracuseStep 2312887 = 3469331) B3469331
theorem B3205907 : Blo 1423531 3205907 := bstep (se 1 (by rfl) ⟨2404430, by rfl⟩ : syracuseStep 3205907 = 4808861) B4808861
theorem B3607375 : Blo 1423531 3607375 := bstep (se 1 (by rfl) ⟨2705531, by rfl⟩ : syracuseStep 3607375 = 5411063) B5411063
theorem B15412139 : Blo 1423531 15412139 := bstep (se 1 (by rfl) ⟨11559104, by rfl⟩ : syracuseStep 15412139 = 23118209) B23118209
theorem B3656801 : Blo 1423531 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B3607649 : Blo 1423531 3607649 := bstep (se 2 (by rfl) ⟨1352868, by rfl⟩ : syracuseStep 3607649 = 2705737) B2705737
theorem B3206267 : Blo 1423531 3206267 := bstep (se 1 (by rfl) ⟨2404700, by rfl⟩ : syracuseStep 3206267 = 4809401) B4809401
theorem B3206393 : Blo 1423531 3206393 := bstep (se 2 (by rfl) ⟨1202397, by rfl⟩ : syracuseStep 3206393 = 2404795) B2404795
theorem B3083617 : Blo 1423531 3083617 := bstep (se 2 (by rfl) ⟨1156356, by rfl⟩ : syracuseStep 3083617 = 2312713) B2312713
theorem B6081911 : Blo 1423531 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B3206537 : Blo 1423531 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B6081979 : Blo 1423531 6081979 := bstep (se 1 (by rfl) ⟨4561484, by rfl⟩ : syracuseStep 6081979 = 9122969) B9122969
theorem B3608023 : Blo 1423531 3608023 := bstep (se 1 (by rfl) ⟨2706017, by rfl⟩ : syracuseStep 3608023 = 5412035) B5412035
theorem B3206663 : Blo 1423531 3206663 := bstep (se 1 (by rfl) ⟨2404997, by rfl⟩ : syracuseStep 3206663 = 4809995) B4809995
theorem B46222913 : Blo 1423531 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B4566611 : Blo 1423531 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B4566689 : Blo 1423531 4566689 := bstep (se 2 (by rfl) ⟨1712508, by rfl⟩ : syracuseStep 4566689 = 3425017) B3425017
theorem B3206843 : Blo 1423531 3206843 := bstep (se 1 (by rfl) ⟨2405132, by rfl⟩ : syracuseStep 3206843 = 4810265) B4810265
theorem B3608327 : Blo 1423531 3608327 := bstep (se 1 (by rfl) ⟨2706245, by rfl⟩ : syracuseStep 3608327 = 5412491) B5412491
theorem B8113931 : Blo 1423531 8113931 := bstep (se 1 (by rfl) ⟨6085448, by rfl⟩ : syracuseStep 8113931 = 12170897) B12170897
theorem B3206969 : Blo 1423531 3206969 := bstep (se 2 (by rfl) ⟨1202613, by rfl⟩ : syracuseStep 3206969 = 2405227) B2405227
theorem B5132189 : Blo 1423531 5132189 := bstep (se 3 (by rfl) ⟨962285, by rfl⟩ : syracuseStep 5132189 = 1924571) B1924571
theorem B3043279 : Blo 1423531 3043279 := bstep (se 1 (by rfl) ⟨2282459, by rfl⟩ : syracuseStep 3043279 = 4564919) B4564919
theorem B3043433 : Blo 1423531 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B14618987 : Blo 1423531 14618987 := bstep (se 1 (by rfl) ⟨10964240, by rfl⟩ : syracuseStep 14618987 = 21928481) B21928481
theorem B2929007 : Blo 1423531 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B1601959 : Blo 1423531 1601959 := bstep (se 1 (by rfl) ⟨1201469, by rfl⟩ : syracuseStep 1601959 = 2402939) B2402939
theorem B2404775 : Blo 1423531 2404775 := bstep (se 1 (by rfl) ⟨1803581, by rfl⟩ : syracuseStep 2404775 = 3607163) B3607163
theorem B2404937 : Blo 1423531 2404937 := bstep (se 2 (by rfl) ⟨901851, by rfl⟩ : syracuseStep 2404937 = 1803703) B1803703
theorem B1602535 : Blo 1423531 1602535 := bstep (se 1 (by rfl) ⟨1201901, by rfl⟩ : syracuseStep 1602535 = 2403803) B2403803
theorem B10261495 : Blo 1423531 10261495 := bstep (se 1 (by rfl) ⟨7696121, by rfl⟩ : syracuseStep 10261495 = 15392243) B15392243
theorem B4805729 : Blo 1423531 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B10810583 : Blo 1423531 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B3421403 : Blo 1423531 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B12170519 : Blo 1423531 12170519 := bstep (se 1 (by rfl) ⟨9127889, by rfl⟩ : syracuseStep 12170519 = 18255779) B18255779
theorem B2135327 : Blo 1423531 2135327 := bstep (se 1 (by rfl) ⟨1601495, by rfl⟩ : syracuseStep 2135327 = 3202991) B3202991
theorem B10270145 : Blo 1423531 10270145 := bstep (se 2 (by rfl) ⟨3851304, by rfl⟩ : syracuseStep 10270145 = 7702609) B7702609
theorem B2135495 : Blo 1423531 2135495 := bstep (se 1 (by rfl) ⟨1601621, by rfl⟩ : syracuseStep 2135495 = 3203243) B3203243
theorem B12162797 : Blo 1423531 12162797 := bstep (se 3 (by rfl) ⟨2280524, by rfl⟩ : syracuseStep 12162797 = 4561049) B4561049
theorem B2135849 : Blo 1423531 2135849 := bstep (se 2 (by rfl) ⟨800943, by rfl⟩ : syracuseStep 2135849 = 1601887) B1601887
theorem B2135855 : Blo 1423531 2135855 := bstep (se 1 (by rfl) ⟨1601891, by rfl⟩ : syracuseStep 2135855 = 3203783) B3203783
theorem B702199637 : Blo 1423531 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B23410619 : Blo 1423531 23410619 := bstep (se 1 (by rfl) ⟨17557964, by rfl⟩ : syracuseStep 23410619 = 35115929) B35115929
theorem B7206893 : Blo 1423531 7206893 := bstep (se 3 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 7206893 = 2702585) B2702585
theorem B2136329 : Blo 1423531 2136329 := bstep (se 2 (by rfl) ⟨801123, by rfl⟩ : syracuseStep 2136329 = 1602247) B1602247
theorem B12171545 : Blo 1423531 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B3471641 : Blo 1423531 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B1423647 : Blo 1423531 1423647 := bstep (se 1 (by rfl) ⟨1067735, by rfl⟩ : syracuseStep 1423647 = 2135471) B2135471
theorem B3422537 : Blo 1423531 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B16234829 : Blo 1423531 16234829 := bstep (se 3 (by rfl) ⟨3044030, by rfl⟩ : syracuseStep 16234829 = 6088061) B6088061
theorem B1423707 : Blo 1423531 1423707 := bstep (se 1 (by rfl) ⟨1067780, by rfl⟩ : syracuseStep 1423707 = 2135561) B2135561
theorem B1423727 : Blo 1423531 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B2136431 : Blo 1423531 2136431 := bstep (se 1 (by rfl) ⟨1602323, by rfl⟩ : syracuseStep 2136431 = 3204647) B3204647
theorem B1423783 : Blo 1423531 1423783 := bstep (se 1 (by rfl) ⟨1067837, by rfl⟩ : syracuseStep 1423783 = 2135675) B2135675
theorem B4807079 : Blo 1423531 4807079 := bstep (se 1 (by rfl) ⟨3605309, by rfl⟩ : syracuseStep 4807079 = 7210619) B7210619
theorem B51952049 : Blo 1423531 51952049 := bstep (se 2 (by rfl) ⟨19482018, by rfl⟩ : syracuseStep 51952049 = 38964037) B38964037
theorem B46815671 : Blo 1423531 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B7207379 : Blo 1423531 7207379 := bstep (se 1 (by rfl) ⟨5405534, by rfl⟩ : syracuseStep 7207379 = 10811069) B10811069
theorem B1423867 : Blo 1423531 1423867 := bstep (se 1 (by rfl) ⟨1067900, by rfl⟩ : syracuseStep 1423867 = 2135801) B2135801
theorem B24336935 : Blo 1423531 24336935 := bstep (se 1 (by rfl) ⟨18252701, by rfl⟩ : syracuseStep 24336935 = 36505403) B36505403
theorem B1423935 : Blo 1423531 1423935 := bstep (se 1 (by rfl) ⟨1067951, by rfl⟩ : syracuseStep 1423935 = 2135903) B2135903
theorem B1423943 : Blo 1423531 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B2136647 : Blo 1423531 2136647 := bstep (se 1 (by rfl) ⟨1602485, by rfl⟩ : syracuseStep 2136647 = 3204971) B3204971
theorem B4807241 : Blo 1423531 4807241 := bstep (se 2 (by rfl) ⟨1802715, by rfl⟩ : syracuseStep 4807241 = 3605431) B3605431
theorem B2136683 : Blo 1423531 2136683 := bstep (se 1 (by rfl) ⟨1602512, by rfl⟩ : syracuseStep 2136683 = 3205025) B3205025
theorem B1424095 : Blo 1423531 1424095 := bstep (se 1 (by rfl) ⟨1068071, by rfl⟩ : syracuseStep 1424095 = 2136143) B2136143
theorem B7207703 : Blo 1423531 7207703 := bstep (se 1 (by rfl) ⟨5405777, by rfl⟩ : syracuseStep 7207703 = 10811555) B10811555
theorem B1424175 : Blo 1423531 1424175 := bstep (se 1 (by rfl) ⟨1068131, by rfl⟩ : syracuseStep 1424175 = 2136263) B2136263
theorem B2136911 : Blo 1423531 2136911 := bstep (se 1 (by rfl) ⟨1602683, by rfl⟩ : syracuseStep 2136911 = 3205367) B3205367
theorem B1424283 : Blo 1423531 1424283 := bstep (se 1 (by rfl) ⟨1068212, by rfl⟩ : syracuseStep 1424283 = 2136425) B2136425
theorem B1424335 : Blo 1423531 1424335 := bstep (se 1 (by rfl) ⟨1068251, by rfl⟩ : syracuseStep 1424335 = 2136503) B2136503
theorem B1424359 : Blo 1423531 1424359 := bstep (se 1 (by rfl) ⟨1068269, by rfl⟩ : syracuseStep 1424359 = 2136539) B2136539
theorem B24665107 : Blo 1423531 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B3603599 : Blo 1423531 3603599 := bstep (se 1 (by rfl) ⟨2702699, by rfl⟩ : syracuseStep 3603599 = 5405399) B5405399
theorem B20544677 : Blo 1423531 20544677 := bstep (se 4 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 20544677 = 3852127) B3852127
theorem B5405885 : Blo 1423531 5405885 := bstep (se 3 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 5405885 = 2027207) B2027207
theorem B2702555 : Blo 1423531 2702555 := bstep (se 1 (by rfl) ⟨2026916, by rfl⟩ : syracuseStep 2702555 = 4053833) B4053833
theorem B2137307 : Blo 1423531 2137307 := bstep (se 1 (by rfl) ⟨1602980, by rfl⟩ : syracuseStep 2137307 = 3205961) B3205961
theorem B1424671 : Blo 1423531 1424671 := bstep (se 1 (by rfl) ⟨1068503, by rfl⟩ : syracuseStep 1424671 = 2137007) B2137007
theorem B7216451 : Blo 1423531 7216451 := bstep (se 1 (by rfl) ⟨5412338, by rfl⟩ : syracuseStep 7216451 = 10824677) B10824677
theorem B1424731 : Blo 1423531 1424731 := bstep (se 1 (by rfl) ⟨1068548, by rfl⟩ : syracuseStep 1424731 = 2137097) B2137097
theorem B1424751 : Blo 1423531 1424751 := bstep (se 1 (by rfl) ⟨1068563, by rfl⟩ : syracuseStep 1424751 = 2137127) B2137127
theorem B2137481 : Blo 1423531 2137481 := bstep (se 2 (by rfl) ⟨801555, by rfl⟩ : syracuseStep 2137481 = 1603111) B1603111
theorem B1424807 : Blo 1423531 1424807 := bstep (se 1 (by rfl) ⟨1068605, by rfl⟩ : syracuseStep 1424807 = 2137211) B2137211
theorem B6847993 : Blo 1423531 6847993 := bstep (se 2 (by rfl) ⟨2567997, by rfl⟩ : syracuseStep 6847993 = 5135995) B5135995
theorem B1424891 : Blo 1423531 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B30826007 : Blo 1423531 30826007 := bstep (se 1 (by rfl) ⟨23119505, by rfl⟩ : syracuseStep 30826007 = 46239011) B46239011
theorem B1424959 : Blo 1423531 1424959 := bstep (se 1 (by rfl) ⟨1068719, by rfl⟩ : syracuseStep 1424959 = 2137439) B2137439
theorem B1711687 : Blo 1423531 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B1424967 : Blo 1423531 1424967 := bstep (se 1 (by rfl) ⟨1068725, by rfl⟩ : syracuseStep 1424967 = 2137451) B2137451
theorem B9256531 : Blo 1423531 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B6086353 : Blo 1423531 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B1924831 : Blo 1423531 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B1425119 : Blo 1423531 1425119 := bstep (se 1 (by rfl) ⟨1068839, by rfl⟩ : syracuseStep 1425119 = 2137679) B2137679
theorem B2137835 : Blo 1423531 2137835 := bstep (se 1 (by rfl) ⟨1603376, by rfl⟩ : syracuseStep 2137835 = 3206753) B3206753
theorem B4448047 : Blo 1423531 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B1425199 : Blo 1423531 1425199 := bstep (se 1 (by rfl) ⟨1068899, by rfl⟩ : syracuseStep 1425199 = 2137799) B2137799
theorem B1425307 : Blo 1423531 1425307 := bstep (se 1 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 1425307 = 2137961) B2137961
theorem B1425359 : Blo 1423531 1425359 := bstep (se 1 (by rfl) ⟨1069019, by rfl⟩ : syracuseStep 1425359 = 2138039) B2138039
theorem B2138063 : Blo 1423531 2138063 := bstep (se 1 (by rfl) ⟨1603547, by rfl⟩ : syracuseStep 2138063 = 3207095) B3207095
theorem B1425383 : Blo 1423531 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B8667575 : Blo 1423531 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B5407175 : Blo 1423531 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B5202505 : Blo 1423531 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B6087241 : Blo 1423531 6087241 := bstep (se 2 (by rfl) ⟨2282715, by rfl⟩ : syracuseStep 6087241 = 4565431) B4565431
theorem B7209647 : Blo 1423531 7209647 := bstep (se 1 (by rfl) ⟨5407235, by rfl⟩ : syracuseStep 7209647 = 10814471) B10814471
theorem B3203819 : Blo 1423531 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B5407631 : Blo 1423531 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B8111015 : Blo 1423531 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B3851219 : Blo 1423531 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B1852411 : Blo 1423531 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B4809833 : Blo 1423531 4809833 := bstep (se 2 (by rfl) ⟨1803687, by rfl⟩ : syracuseStep 4809833 = 3607375) B3607375
theorem B5137597 : Blo 1423531 5137597 := bstep (se 3 (by rfl) ⟨963299, by rfl⟩ : syracuseStep 5137597 = 1926599) B1926599
theorem B17335495 : Blo 1423531 17335495 := bstep (se 1 (by rfl) ⟨13001621, by rfl⟩ : syracuseStep 17335495 = 26003243) B26003243
theorem B468133091 : Blo 1423531 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B9127171 : Blo 1423531 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B15607079 : Blo 1423531 15607079 := bstep (se 1 (by rfl) ⟨11705309, by rfl⟩ : syracuseStep 15607079 = 23410619) B23410619
theorem B13681993 : Blo 1423531 13681993 := bstep (se 2 (by rfl) ⟨5130747, by rfl⟩ : syracuseStep 13681993 = 10261495) B10261495
theorem B25986379 : Blo 1423531 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B3605867 : Blo 1423531 3605867 := bstep (se 1 (by rfl) ⟨2704400, by rfl⟩ : syracuseStep 3605867 = 5408801) B5408801
theorem B10823219 : Blo 1423531 10823219 := bstep (se 1 (by rfl) ⟨8117414, by rfl⟩ : syracuseStep 10823219 = 16234829) B16234829
theorem B3204719 : Blo 1423531 3204719 := bstep (se 1 (by rfl) ⟨2403539, by rfl⟩ : syracuseStep 3204719 = 4807079) B4807079
theorem B3204827 : Blo 1423531 3204827 := bstep (se 1 (by rfl) ⟨2403620, by rfl⟩ : syracuseStep 3204827 = 4807241) B4807241
theorem B1804027 : Blo 1423531 1804027 := bstep (se 1 (by rfl) ⟨1353020, by rfl⟩ : syracuseStep 1804027 = 2706041) B2706041
theorem B1623839 : Blo 1423531 1623839 := bstep (se 1 (by rfl) ⟨1217879, by rfl⟩ : syracuseStep 1623839 = 2435759) B2435759
theorem B10274759 : Blo 1423531 10274759 := bstep (se 1 (by rfl) ⟨7706069, by rfl⟩ : syracuseStep 10274759 = 15412139) B15412139
theorem B4810697 : Blo 1423531 4810697 := bstep (se 2 (by rfl) ⟨1804011, by rfl⟩ : syracuseStep 4810697 = 3608023) B3608023
theorem B2402399 : Blo 1423531 2402399 := bstep (se 1 (by rfl) ⟨1801799, by rfl⟩ : syracuseStep 2402399 = 3603599) B3603599
theorem B4810967 : Blo 1423531 4810967 := bstep (se 1 (by rfl) ⟨3608225, by rfl⟩ : syracuseStep 4810967 = 7216451) B7216451
theorem B2566441 : Blo 1423531 2566441 := bstep (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) B1924831
theorem B5409287 : Blo 1423531 5409287 := bstep (se 1 (by rfl) ⟨4056965, by rfl⟩ : syracuseStep 5409287 = 8113931) B8113931
theorem B4057705 : Blo 1423531 4057705 := bstep (se 2 (by rfl) ⟨1521639, by rfl⟩ : syracuseStep 4057705 = 3043279) B3043279
theorem B3205943 : Blo 1423531 3205943 := bstep (se 1 (by rfl) ⟨2404457, by rfl⟩ : syracuseStep 3205943 = 4808915) B4808915
theorem B2435999 : Blo 1423531 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B18254753 : Blo 1423531 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B1952671 : Blo 1423531 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B18508763 : Blo 1423531 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B3206123 : Blo 1423531 3206123 := bstep (se 1 (by rfl) ⟨2404592, by rfl⟩ : syracuseStep 3206123 = 4809185) B4809185
theorem B3042527 : Blo 1423531 3042527 := bstep (se 1 (by rfl) ⟨2281895, by rfl⟩ : syracuseStep 3042527 = 4563791) B4563791
theorem B20540749 : Blo 1423531 20540749 := bstep (se 3 (by rfl) ⟨3851390, by rfl⟩ : syracuseStep 20540749 = 7702781) B7702781
theorem B2403695 : Blo 1423531 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B2280935 : Blo 1423531 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B8113679 : Blo 1423531 8113679 := bstep (se 1 (by rfl) ⟨6085259, by rfl⟩ : syracuseStep 8113679 = 12170519) B12170519
theorem B3083849 : Blo 1423531 3083849 := bstep (se 2 (by rfl) ⟨1156443, by rfl⟩ : syracuseStep 3083849 = 2312887) B2312887
theorem B2403931 : Blo 1423531 2403931 := bstep (se 1 (by rfl) ⟨1802948, by rfl⟩ : syracuseStep 2403931 = 3605897) B3605897
theorem B2404073 : Blo 1423531 2404073 := bstep (se 2 (by rfl) ⟨901527, by rfl⟩ : syracuseStep 2404073 = 1803055) B1803055
theorem B3206951 : Blo 1423531 3206951 := bstep (se 1 (by rfl) ⟨2405213, by rfl⟩ : syracuseStep 3206951 = 4810427) B4810427
theorem B4804595 : Blo 1423531 4804595 := bstep (se 1 (by rfl) ⟨3603446, by rfl⟩ : syracuseStep 4804595 = 7206893) B7206893
theorem B14823427 : Blo 1423531 14823427 := bstep (se 1 (by rfl) ⟨11117570, by rfl⟩ : syracuseStep 14823427 = 22235141) B22235141
theorem B32886809 : Blo 1423531 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B8114363 : Blo 1423531 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B2314427 : Blo 1423531 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B2281691 : Blo 1423531 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B4804919 : Blo 1423531 4804919 := bstep (se 1 (by rfl) ⟨3603689, by rfl⟩ : syracuseStep 4804919 = 7207379) B7207379
theorem B16224623 : Blo 1423531 16224623 := bstep (se 1 (by rfl) ⟨12168467, by rfl⟩ : syracuseStep 16224623 = 24336935) B24336935
theorem B4805135 : Blo 1423531 4805135 := bstep (se 1 (by rfl) ⟨3603851, by rfl⟩ : syracuseStep 4805135 = 7207703) B7207703
theorem B9130657 : Blo 1423531 9130657 := bstep (se 2 (by rfl) ⟨3423996, by rfl⟩ : syracuseStep 9130657 = 6847993) B6847993
theorem B2437867 : Blo 1423531 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B2405099 : Blo 1423531 2405099 := bstep (se 1 (by rfl) ⟨1803824, by rfl⟩ : syracuseStep 2405099 = 3607649) B3607649
theorem B2282249 : Blo 1423531 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B12342041 : Blo 1423531 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B8115137 : Blo 1423531 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B20550671 : Blo 1423531 20550671 := bstep (se 1 (by rfl) ⟨15413003, by rfl⟩ : syracuseStep 20550671 = 30826007) B30826007
theorem B30815275 : Blo 1423531 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B3044407 : Blo 1423531 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B3044459 : Blo 1423531 3044459 := bstep (se 1 (by rfl) ⟨2283344, by rfl⟩ : syracuseStep 3044459 = 4566689) B4566689
theorem B2405551 : Blo 1423531 2405551 := bstep (se 1 (by rfl) ⟨1804163, by rfl⟩ : syracuseStep 2405551 = 3608327) B3608327
theorem B3421459 : Blo 1423531 3421459 := bstep (se 1 (by rfl) ⟨2566094, by rfl⟩ : syracuseStep 3421459 = 5132189) B5132189
theorem B2135387 : Blo 1423531 2135387 := bstep (se 1 (by rfl) ⟨1601540, by rfl⟩ : syracuseStep 2135387 = 3203081) B3203081
theorem B4806215 : Blo 1423531 4806215 := bstep (se 1 (by rfl) ⟨3604661, by rfl⟩ : syracuseStep 4806215 = 7209323) B7209323
theorem B9745991 : Blo 1423531 9745991 := bstep (se 1 (by rfl) ⟨7309493, by rfl⟩ : syracuseStep 9745991 = 14618987) B14618987
theorem B8115821 : Blo 1423531 8115821 := bstep (se 3 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 8115821 = 3043433) B3043433
theorem B2135663 : Blo 1423531 2135663 := bstep (se 1 (by rfl) ⟨1601747, by rfl⟩ : syracuseStep 2135663 = 3203495) B3203495
theorem B1603183 : Blo 1423531 1603183 := bstep (se 1 (by rfl) ⟨1202387, by rfl⟩ : syracuseStep 1603183 = 2404775) B2404775
theorem B2135735 : Blo 1423531 2135735 := bstep (se 1 (by rfl) ⟨1601801, by rfl⟩ : syracuseStep 2135735 = 3203603) B3203603
theorem B2135771 : Blo 1423531 2135771 := bstep (se 1 (by rfl) ⟨1601828, by rfl⟩ : syracuseStep 2135771 = 3203657) B3203657
theorem B1603291 : Blo 1423531 1603291 := bstep (se 1 (by rfl) ⟨1202468, by rfl⟩ : syracuseStep 1603291 = 2404937) B2404937
theorem B2135945 : Blo 1423531 2135945 := bstep (se 2 (by rfl) ⟨800979, by rfl⟩ : syracuseStep 2135945 = 1601959) B1601959
theorem B38975417 : Blo 1423531 38975417 := bstep (se 2 (by rfl) ⟨14615781, by rfl⟩ : syracuseStep 38975417 = 29231563) B29231563
theorem B2136047 : Blo 1423531 2136047 := bstep (se 1 (by rfl) ⟨1602035, by rfl⟩ : syracuseStep 2136047 = 3204071) B3204071
theorem B7207055 : Blo 1423531 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B1423551 : Blo 1423531 1423551 := bstep (se 1 (by rfl) ⟨1067663, by rfl⟩ : syracuseStep 1423551 = 2135327) B2135327
theorem B9124073 : Blo 1423531 9124073 := bstep (se 2 (by rfl) ⟨3421527, by rfl⟩ : syracuseStep 9124073 = 6843055) B6843055
theorem B2136299 : Blo 1423531 2136299 := bstep (se 1 (by rfl) ⟨1602224, by rfl⟩ : syracuseStep 2136299 = 3204449) B3204449
theorem B2136359 : Blo 1423531 2136359 := bstep (se 1 (by rfl) ⟨1602269, by rfl⟩ : syracuseStep 2136359 = 3204539) B3204539
theorem B6846763 : Blo 1423531 6846763 := bstep (se 1 (by rfl) ⟨5135072, by rfl⟩ : syracuseStep 6846763 = 10270145) B10270145
theorem B1423663 : Blo 1423531 1423663 := bstep (se 1 (by rfl) ⟨1067747, by rfl⟩ : syracuseStep 1423663 = 2135495) B2135495
theorem B2136443 : Blo 1423531 2136443 := bstep (se 1 (by rfl) ⟨1602332, by rfl⟩ : syracuseStep 2136443 = 3204665) B3204665
theorem B12163547 : Blo 1423531 12163547 := bstep (se 1 (by rfl) ⟨9122660, by rfl⟩ : syracuseStep 12163547 = 18245321) B18245321
theorem B8108531 : Blo 1423531 8108531 := bstep (se 1 (by rfl) ⟨6081398, by rfl⟩ : syracuseStep 8108531 = 12162797) B12162797
theorem B4807187 : Blo 1423531 4807187 := bstep (se 1 (by rfl) ⟨3605390, by rfl⟩ : syracuseStep 4807187 = 7210781) B7210781
theorem B1423899 : Blo 1423531 1423899 := bstep (se 1 (by rfl) ⟨1067924, by rfl⟩ : syracuseStep 1423899 = 2135849) B2135849
theorem B1423903 : Blo 1423531 1423903 := bstep (se 1 (by rfl) ⟨1067927, by rfl⟩ : syracuseStep 1423903 = 2135855) B2135855
theorem B2136713 : Blo 1423531 2136713 := bstep (se 2 (by rfl) ⟨801267, by rfl⟩ : syracuseStep 2136713 = 1602535) B1602535
theorem B2136887 : Blo 1423531 2136887 := bstep (se 1 (by rfl) ⟨1602665, by rfl⟩ : syracuseStep 2136887 = 3205331) B3205331
theorem B1424219 : Blo 1423531 1424219 := bstep (se 1 (by rfl) ⟨1068164, by rfl⟩ : syracuseStep 1424219 = 2136329) B2136329
theorem B2136923 : Blo 1423531 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B4332379 : Blo 1423531 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B1424287 : Blo 1423531 1424287 := bstep (se 1 (by rfl) ⟨1068215, by rfl⟩ : syracuseStep 1424287 = 2136431) B2136431
theorem B34634699 : Blo 1423531 34634699 := bstep (se 1 (by rfl) ⟨25976024, by rfl⟩ : syracuseStep 34634699 = 51952049) B51952049
theorem B31210447 : Blo 1423531 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B6085601 : Blo 1423531 6085601 := bstep (se 2 (by rfl) ⟨2282100, by rfl⟩ : syracuseStep 6085601 = 4564201) B4564201
theorem B2137067 : Blo 1423531 2137067 := bstep (se 1 (by rfl) ⟨1602800, by rfl⟩ : syracuseStep 2137067 = 3205601) B3205601
theorem B1424431 : Blo 1423531 1424431 := bstep (se 1 (by rfl) ⟨1068323, by rfl⟩ : syracuseStep 1424431 = 2136647) B2136647
theorem B1424455 : Blo 1423531 1424455 := bstep (se 1 (by rfl) ⟨1068341, by rfl⟩ : syracuseStep 1424455 = 2136683) B2136683
theorem B4111489 : Blo 1423531 4111489 := bstep (se 2 (by rfl) ⟨1541808, by rfl⟩ : syracuseStep 4111489 = 3083617) B3083617
theorem B2137271 : Blo 1423531 2137271 := bstep (se 1 (by rfl) ⟨1602953, by rfl⟩ : syracuseStep 2137271 = 3205907) B3205907
theorem B150060221 : Blo 1423531 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B1424607 : Blo 1423531 1424607 := bstep (se 1 (by rfl) ⟨1068455, by rfl⟩ : syracuseStep 1424607 = 2136911) B2136911
theorem B8109305 : Blo 1423531 8109305 := bstep (se 2 (by rfl) ⟨3040989, by rfl⟩ : syracuseStep 8109305 = 6081979) B6081979
theorem B2137511 : Blo 1423531 2137511 := bstep (se 1 (by rfl) ⟨1603133, by rfl⟩ : syracuseStep 2137511 = 3206267) B3206267
theorem B13696451 : Blo 1423531 13696451 := bstep (se 1 (by rfl) ⟨10272338, by rfl⟩ : syracuseStep 13696451 = 20544677) B20544677
theorem B3603923 : Blo 1423531 3603923 := bstep (se 1 (by rfl) ⟨2702942, by rfl⟩ : syracuseStep 3603923 = 5405885) B5405885
theorem B1801703 : Blo 1423531 1801703 := bstep (se 1 (by rfl) ⟨1351277, by rfl⟩ : syracuseStep 1801703 = 2702555) B2702555
theorem B1424871 : Blo 1423531 1424871 := bstep (se 1 (by rfl) ⟨1068653, by rfl⟩ : syracuseStep 1424871 = 2137307) B2137307
theorem B2137595 : Blo 1423531 2137595 := bstep (se 1 (by rfl) ⟨1603196, by rfl⟩ : syracuseStep 2137595 = 3206393) B3206393
theorem B4054607 : Blo 1423531 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1424987 : Blo 1423531 1424987 := bstep (se 1 (by rfl) ⟨1068740, by rfl⟩ : syracuseStep 1424987 = 2137481) B2137481
theorem B2137691 : Blo 1423531 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B2137775 : Blo 1423531 2137775 := bstep (se 1 (by rfl) ⟨1603331, by rfl⟩ : syracuseStep 2137775 = 3206663) B3206663
theorem B5930729 : Blo 1423531 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B2137895 : Blo 1423531 2137895 := bstep (se 1 (by rfl) ⟨1603421, by rfl⟩ : syracuseStep 2137895 = 3206843) B3206843
theorem B1425223 : Blo 1423531 1425223 := bstep (se 1 (by rfl) ⟨1068917, by rfl⟩ : syracuseStep 1425223 = 2137835) B2137835
theorem B2137979 : Blo 1423531 2137979 := bstep (se 1 (by rfl) ⟨1603484, by rfl⟩ : syracuseStep 2137979 = 3206969) B3206969
theorem B1425375 : Blo 1423531 1425375 := bstep (se 1 (by rfl) ⟨1069031, by rfl⟩ : syracuseStep 1425375 = 2138063) B2138063
theorem B3203279 : Blo 1423531 3203279 := bstep (se 1 (by rfl) ⟨2402459, by rfl⟩ : syracuseStep 3203279 = 4804919) B4804919
theorem B3604783 : Blo 1423531 3604783 := bstep (se 1 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 3604783 = 5407175) B5407175
theorem B3203423 : Blo 1423531 3203423 := bstep (se 1 (by rfl) ⟨2402567, by rfl⟩ : syracuseStep 3203423 = 4805135) B4805135
theorem B3605087 : Blo 1423531 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B5407343 : Blo 1423531 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B10404719 : Blo 1423531 10404719 := bstep (se 1 (by rfl) ⟨7803539, by rfl⟩ : syracuseStep 10404719 = 15607079) B15607079
theorem B12174209 : Blo 1423531 12174209 := bstep (se 2 (by rfl) ⟨4565328, by rfl⟩ : syracuseStep 12174209 = 9130657) B9130657
theorem B3204143 : Blo 1423531 3204143 := bstep (se 1 (by rfl) ⟨2403107, by rfl⟩ : syracuseStep 3204143 = 4806215) B4806215
theorem B6497327 : Blo 1423531 6497327 := bstep (se 1 (by rfl) ⟨4872995, by rfl⟩ : syracuseStep 6497327 = 9745991) B9745991
theorem B5776505 : Blo 1423531 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B13001957 : Blo 1423531 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B6849839 : Blo 1423531 6849839 := bstep (se 1 (by rfl) ⟨5137379, by rfl⟩ : syracuseStep 6849839 = 10274759) B10274759
theorem B6850129 : Blo 1423531 6850129 := bstep (se 2 (by rfl) ⟨2568798, by rfl⟩ : syracuseStep 6850129 = 5137597) B5137597
theorem B3606191 : Blo 1423531 3606191 := bstep (se 1 (by rfl) ⟨2704643, by rfl⟩ : syracuseStep 3606191 = 5409287) B5409287
theorem B3204791 : Blo 1423531 3204791 := bstep (se 1 (by rfl) ⟨2403593, by rfl⟩ : syracuseStep 3204791 = 4807187) B4807187
theorem B27387665 : Blo 1423531 27387665 := bstep (se 2 (by rfl) ⟨10270374, by rfl⟩ : syracuseStep 27387665 = 20540749) B20540749
theorem B12339175 : Blo 1423531 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B4057067 : Blo 1423531 4057067 := bstep (se 1 (by rfl) ⟨3042800, by rfl⟩ : syracuseStep 4057067 = 6085601) B6085601
theorem B3205241 : Blo 1423531 3205241 := bstep (se 2 (by rfl) ⟨1201965, by rfl⟩ : syracuseStep 3205241 = 2403931) B2403931
theorem B2402615 : Blo 1423531 2402615 := bstep (se 1 (by rfl) ⟨1801961, by rfl⟩ : syracuseStep 2402615 = 3603923) B3603923
theorem B5409119 : Blo 1423531 5409119 := bstep (se 1 (by rfl) ⟨4056839, by rfl⟩ : syracuseStep 5409119 = 8113679) B8113679
theorem B21924539 : Blo 1423531 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B5409575 : Blo 1423531 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B10816415 : Blo 1423531 10816415 := bstep (se 1 (by rfl) ⟨8112311, by rfl⟩ : syracuseStep 10816415 = 16224623) B16224623
theorem B5778383 : Blo 1423531 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B17320949 : Blo 1423531 17320949 := bstep (se 5 (by rfl) ⟨811919, by rfl⟩ : syracuseStep 17320949 = 1623839) B1623839
theorem B9129017 : Blo 1423531 9129017 := bstep (se 2 (by rfl) ⟨3423381, by rfl⟩ : syracuseStep 9129017 = 6846763) B6846763
theorem B6171805 : Blo 1423531 6171805 := bstep (se 3 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 6171805 = 2314427) B2314427
theorem B8228027 : Blo 1423531 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B8113405 : Blo 1423531 8113405 := bstep (se 3 (by rfl) ⟨1521263, by rfl⟩ : syracuseStep 8113405 = 3042527) B3042527
theorem B5410091 : Blo 1423531 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B2567479 : Blo 1423531 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B13700447 : Blo 1423531 13700447 := bstep (se 1 (by rfl) ⟨10275335, by rfl⟩ : syracuseStep 13700447 = 20550671) B20550671
theorem B3206555 : Blo 1423531 3206555 := bstep (se 1 (by rfl) ⟨2404916, by rfl⟩ : syracuseStep 3206555 = 4809833) B4809833
theorem B5410273 : Blo 1423531 5410273 := bstep (se 2 (by rfl) ⟨2028852, by rfl⟩ : syracuseStep 5410273 = 4057705) B4057705
theorem B2403911 : Blo 1423531 2403911 := bstep (se 1 (by rfl) ⟨1802933, by rfl⟩ : syracuseStep 2403911 = 3605867) B3605867
theorem B5410547 : Blo 1423531 5410547 := bstep (se 1 (by rfl) ⟨4057910, by rfl⟩ : syracuseStep 5410547 = 8115821) B8115821
theorem B4804541 : Blo 1423531 4804541 := bstep (se 3 (by rfl) ⟨900851, by rfl⟩ : syracuseStep 4804541 = 1801703) B1801703
theorem B3207131 : Blo 1423531 3207131 := bstep (se 1 (by rfl) ⟨2405348, by rfl⟩ : syracuseStep 3207131 = 4810697) B4810697
theorem B2469881 : Blo 1423531 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B41087033 : Blo 1423531 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B1601599 : Blo 1423531 1601599 := bstep (se 1 (by rfl) ⟨1201199, by rfl⟩ : syracuseStep 1601599 = 2402399) B2402399
theorem B4059209 : Blo 1423531 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B4804703 : Blo 1423531 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B18247781 : Blo 1423531 18247781 := bstep (se 4 (by rfl) ⟨1710729, by rfl⟩ : syracuseStep 18247781 = 3421459) B3421459
theorem B3207311 : Blo 1423531 3207311 := bstep (se 1 (by rfl) ⟨2405483, by rfl⟩ : syracuseStep 3207311 = 4810967) B4810967
theorem B6082715 : Blo 1423531 6082715 := bstep (se 1 (by rfl) ⟨4562036, by rfl⟩ : syracuseStep 6082715 = 9124073) B9124073
theorem B3207401 : Blo 1423531 3207401 := bstep (se 2 (by rfl) ⟨1202775, by rfl⟩ : syracuseStep 3207401 = 2405551) B2405551
theorem B23113993 : Blo 1423531 23113993 := bstep (se 2 (by rfl) ⟨8667747, by rfl⟩ : syracuseStep 23113993 = 17335495) B17335495
theorem B12169561 : Blo 1423531 12169561 := bstep (se 2 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 12169561 = 9127171) B9127171
theorem B34648505 : Blo 1423531 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B12169835 : Blo 1423531 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B23089799 : Blo 1423531 23089799 := bstep (se 1 (by rfl) ⟨17317349, by rfl⟩ : syracuseStep 23089799 = 34634699) B34634699
theorem B1602463 : Blo 1423531 1602463 := bstep (se 1 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 1602463 = 2403695) B2403695
theorem B9130967 : Blo 1423531 9130967 := bstep (se 1 (by rfl) ⟨6848225, by rfl⟩ : syracuseStep 9130967 = 13696451) B13696451
theorem B1520623 : Blo 1423531 1520623 := bstep (se 1 (by rfl) ⟨1140467, by rfl⟩ : syracuseStep 1520623 = 2280935) B2280935
theorem B2405369 : Blo 1423531 2405369 := bstep (se 2 (by rfl) ⟨902013, by rfl⟩ : syracuseStep 2405369 = 1804027) B1804027
theorem B3953819 : Blo 1423531 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B1602715 : Blo 1423531 1602715 := bstep (se 1 (by rfl) ⟨1202036, by rfl⟩ : syracuseStep 1602715 = 2404073) B2404073
theorem B19764569 : Blo 1423531 19764569 := bstep (se 2 (by rfl) ⟨7411713, by rfl⟩ : syracuseStep 19764569 = 14823427) B14823427
theorem B1521127 : Blo 1423531 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B3421921 : Blo 1423531 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B4806431 : Blo 1423531 4806431 := bstep (se 1 (by rfl) ⟨3604823, by rfl⟩ : syracuseStep 4806431 = 7209647) B7209647
theorem B2135879 : Blo 1423531 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B1603399 : Blo 1423531 1603399 := bstep (se 1 (by rfl) ⟨1202549, by rfl⟩ : syracuseStep 1603399 = 2405099) B2405099
theorem B1521499 : Blo 1423531 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B21927941 : Blo 1423531 21927941 := bstep (se 4 (by rfl) ⟨2055744, by rfl⟩ : syracuseStep 21927941 = 4111489) B4111489
theorem B2029639 : Blo 1423531 2029639 := bstep (se 1 (by rfl) ⟨1522229, by rfl⟩ : syracuseStep 2029639 = 3044459) B3044459
theorem B6936673 : Blo 1423531 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B8116321 : Blo 1423531 8116321 := bstep (se 2 (by rfl) ⟨3043620, by rfl⟩ : syracuseStep 8116321 = 6087241) B6087241
theorem B312088727 : Blo 1423531 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B1423591 : Blo 1423531 1423591 := bstep (se 1 (by rfl) ⟨1067693, by rfl⟩ : syracuseStep 1423591 = 2135387) B2135387
theorem B7215479 : Blo 1423531 7215479 := bstep (se 1 (by rfl) ⟨5411609, by rfl⟩ : syracuseStep 7215479 = 10823219) B10823219
theorem B1423775 : Blo 1423531 1423775 := bstep (se 1 (by rfl) ⟨1067831, by rfl⟩ : syracuseStep 1423775 = 2135663) B2135663
theorem B2136479 : Blo 1423531 2136479 := bstep (se 1 (by rfl) ⟨1602359, by rfl⟩ : syracuseStep 2136479 = 3204719) B3204719
theorem B1423823 : Blo 1423531 1423823 := bstep (se 1 (by rfl) ⟨1067867, by rfl⟩ : syracuseStep 1423823 = 2135735) B2135735
theorem B1423847 : Blo 1423531 1423847 := bstep (se 1 (by rfl) ⟨1067885, by rfl⟩ : syracuseStep 1423847 = 2135771) B2135771
theorem B2136551 : Blo 1423531 2136551 := bstep (se 1 (by rfl) ⟨1602413, by rfl⟩ : syracuseStep 2136551 = 3204827) B3204827
theorem B2603561 : Blo 1423531 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B1423963 : Blo 1423531 1423963 := bstep (se 1 (by rfl) ⟨1067972, by rfl⟩ : syracuseStep 1423963 = 2135945) B2135945
theorem B41613929 : Blo 1423531 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B25983611 : Blo 1423531 25983611 := bstep (se 1 (by rfl) ⟨19487708, by rfl⟩ : syracuseStep 25983611 = 38975417) B38975417
theorem B1424031 : Blo 1423531 1424031 := bstep (se 1 (by rfl) ⟨1068023, by rfl⟩ : syracuseStep 1424031 = 2136047) B2136047
theorem B1424199 : Blo 1423531 1424199 := bstep (se 1 (by rfl) ⟨1068149, by rfl⟩ : syracuseStep 1424199 = 2136299) B2136299
theorem B1424239 : Blo 1423531 1424239 := bstep (se 1 (by rfl) ⟨1068179, by rfl⟩ : syracuseStep 1424239 = 2136359) B2136359
theorem B1424295 : Blo 1423531 1424295 := bstep (se 1 (by rfl) ⟨1068221, by rfl⟩ : syracuseStep 1424295 = 2136443) B2136443
theorem B8109031 : Blo 1423531 8109031 := bstep (se 1 (by rfl) ⟨6081773, by rfl⟩ : syracuseStep 8109031 = 12163547) B12163547
theorem B25983989 : Blo 1423531 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B5405687 : Blo 1423531 5405687 := bstep (se 1 (by rfl) ⟨4054265, by rfl⟩ : syracuseStep 5405687 = 8108531) B8108531
theorem B1424475 : Blo 1423531 1424475 := bstep (se 1 (by rfl) ⟨1068356, by rfl⟩ : syracuseStep 1424475 = 2136713) B2136713
theorem B18242657 : Blo 1423531 18242657 := bstep (se 2 (by rfl) ⟨6840996, by rfl⟩ : syracuseStep 18242657 = 13681993) B13681993
theorem B1424591 : Blo 1423531 1424591 := bstep (se 1 (by rfl) ⟨1068443, by rfl⟩ : syracuseStep 1424591 = 2136887) B2136887
theorem B2137295 : Blo 1423531 2137295 := bstep (se 1 (by rfl) ⟨1602971, by rfl⟩ : syracuseStep 2137295 = 3205943) B3205943
theorem B1424615 : Blo 1423531 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B1424711 : Blo 1423531 1424711 := bstep (se 1 (by rfl) ⟨1068533, by rfl⟩ : syracuseStep 1424711 = 2137067) B2137067
theorem B2137415 : Blo 1423531 2137415 := bstep (se 1 (by rfl) ⟨1603061, by rfl⟩ : syracuseStep 2137415 = 3206123) B3206123
theorem B1424847 : Blo 1423531 1424847 := bstep (se 1 (by rfl) ⟨1068635, by rfl⟩ : syracuseStep 1424847 = 2137271) B2137271
theorem B100040147 : Blo 1423531 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B2137577 : Blo 1423531 2137577 := bstep (se 2 (by rfl) ⟨801591, by rfl⟩ : syracuseStep 2137577 = 1603183) B1603183
theorem B5406203 : Blo 1423531 5406203 := bstep (se 1 (by rfl) ⟨4054652, by rfl⟩ : syracuseStep 5406203 = 8109305) B8109305
theorem B1425007 : Blo 1423531 1425007 := bstep (se 1 (by rfl) ⟨1068755, by rfl⟩ : syracuseStep 1425007 = 2137511) B2137511
theorem B2137721 : Blo 1423531 2137721 := bstep (se 2 (by rfl) ⟨801645, by rfl⟩ : syracuseStep 2137721 = 1603291) B1603291
theorem B1425063 : Blo 1423531 1425063 := bstep (se 1 (by rfl) ⟨1068797, by rfl⟩ : syracuseStep 1425063 = 2137595) B2137595
theorem B2055899 : Blo 1423531 2055899 := bstep (se 1 (by rfl) ⟨1541924, by rfl⟩ : syracuseStep 2055899 = 3083849) B3083849
theorem B2703071 : Blo 1423531 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B1425127 : Blo 1423531 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B1425183 : Blo 1423531 1425183 := bstep (se 1 (by rfl) ⟨1068887, by rfl⟩ : syracuseStep 1425183 = 2137775) B2137775
theorem B1425263 : Blo 1423531 1425263 := bstep (se 1 (by rfl) ⟨1068947, by rfl⟩ : syracuseStep 1425263 = 2137895) B2137895
theorem B2137967 : Blo 1423531 2137967 := bstep (se 1 (by rfl) ⟨1603475, by rfl⟩ : syracuseStep 2137967 = 3206951) B3206951
theorem B1425319 : Blo 1423531 1425319 := bstep (se 1 (by rfl) ⟨1068989, by rfl⟩ : syracuseStep 1425319 = 2137979) B2137979
theorem B3203063 : Blo 1423531 3203063 := bstep (se 1 (by rfl) ⟨2402297, by rfl⟩ : syracuseStep 3203063 = 4804595) B4804595
theorem B3203135 : Blo 1423531 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B12165187 : Blo 1423531 12165187 := bstep (se 1 (by rfl) ⟨9123890, by rfl⟩ : syracuseStep 12165187 = 18247781) B18247781
theorem B2138207 : Blo 1423531 2138207 := bstep (se 1 (by rfl) ⟨1603655, by rfl⟩ : syracuseStep 2138207 = 3207311) B3207311
theorem B4055143 : Blo 1423531 4055143 := bstep (se 1 (by rfl) ⟨3041357, by rfl⟩ : syracuseStep 4055143 = 6082715) B6082715
theorem B9248897 : Blo 1423531 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B10821761 : Blo 1423531 10821761 := bstep (se 2 (by rfl) ⟨4058160, by rfl⟩ : syracuseStep 10821761 = 8116321) B8116321
theorem B2138267 : Blo 1423531 2138267 := bstep (se 1 (by rfl) ⟨1603700, by rfl⟩ : syracuseStep 2138267 = 3207401) B3207401
theorem B30818657 : Blo 1423531 30818657 := bstep (se 2 (by rfl) ⟨11556996, by rfl⟩ : syracuseStep 30818657 = 23113993) B23113993
theorem B10543517 : Blo 1423531 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B3604895 : Blo 1423531 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B15393199 : Blo 1423531 15393199 := bstep (se 1 (by rfl) ⟨11544899, by rfl⟩ : syracuseStep 15393199 = 23089799) B23089799
theorem B6087311 : Blo 1423531 6087311 := bstep (se 1 (by rfl) ⟨4565483, by rfl⟩ : syracuseStep 6087311 = 9130967) B9130967
theorem B3851003 : Blo 1423531 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B8667971 : Blo 1423531 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B3204287 : Blo 1423531 3204287 := bstep (se 1 (by rfl) ⟨2403215, by rfl⟩ : syracuseStep 3204287 = 4806431) B4806431
theorem B3606079 : Blo 1423531 3606079 := bstep (se 1 (by rfl) ⟨2704559, by rfl⟩ : syracuseStep 3606079 = 5409119) B5409119
theorem B4810319 : Blo 1423531 4810319 := bstep (se 1 (by rfl) ⟨3607739, by rfl⟩ : syracuseStep 4810319 = 7215479) B7215479
theorem B14616359 : Blo 1423531 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B3606383 : Blo 1423531 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B5482397 : Blo 1423531 5482397 := bstep (se 3 (by rfl) ⟨1027949, by rfl⟩ : syracuseStep 5482397 = 2055899) B2055899
theorem B7210943 : Blo 1423531 7210943 := bstep (se 1 (by rfl) ⟨5408207, by rfl⟩ : syracuseStep 7210943 = 10816415) B10816415
theorem B3606727 : Blo 1423531 3606727 := bstep (se 1 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 3606727 = 5410091) B5410091
theorem B66693431 : Blo 1423531 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B3607031 : Blo 1423531 3607031 := bstep (se 1 (by rfl) ⟨2705273, by rfl⟩ : syracuseStep 3607031 = 5410547) B5410547
theorem B16452233 : Blo 1423531 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B2706139 : Blo 1423531 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B2706185 : Blo 1423531 2706185 := bstep (se 2 (by rfl) ⟨1014819, by rfl⟩ : syracuseStep 2706185 = 2029639) B2029639
theorem B2403391 : Blo 1423531 2403391 := bstep (se 1 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 2403391 = 3605087) B3605087
theorem B8113223 : Blo 1423531 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B21941405 : Blo 1423531 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B4566559 : Blo 1423531 4566559 := bstep (se 1 (by rfl) ⟨3424919, by rfl⟩ : syracuseStep 4566559 = 6849839) B6849839
theorem B13176379 : Blo 1423531 13176379 := bstep (se 1 (by rfl) ⟨9882284, by rfl⟩ : syracuseStep 13176379 = 19764569) B19764569
theorem B2404127 : Blo 1423531 2404127 := bstep (se 1 (by rfl) ⟨1803095, by rfl⟩ : syracuseStep 2404127 = 3606191) B3606191
theorem B14618627 : Blo 1423531 14618627 := bstep (se 1 (by rfl) ⟨10963970, by rfl⟩ : syracuseStep 14618627 = 21927941) B21927941
theorem B6942829 : Blo 1423531 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B1601743 : Blo 1423531 1601743 := bstep (se 1 (by rfl) ⟨1201307, by rfl⟩ : syracuseStep 1601743 = 2402615) B2402615
theorem B8229073 : Blo 1423531 8229073 := bstep (se 2 (by rfl) ⟨3085902, by rfl⟩ : syracuseStep 8229073 = 6171805) B6171805
theorem B10817873 : Blo 1423531 10817873 := bstep (se 2 (by rfl) ⟨4056702, by rfl⟩ : syracuseStep 10817873 = 8113405) B8113405
theorem B27742619 : Blo 1423531 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B17322407 : Blo 1423531 17322407 := bstep (se 1 (by rfl) ⟨12991805, by rfl⟩ : syracuseStep 17322407 = 25983611) B25983611
theorem B7213697 : Blo 1423531 7213697 := bstep (se 2 (by rfl) ⟨2705136, by rfl⟩ : syracuseStep 7213697 = 5410273) B5410273
theorem B2028169 : Blo 1423531 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B11547299 : Blo 1423531 11547299 := bstep (se 1 (by rfl) ⟨8660474, by rfl⟩ : syracuseStep 11547299 = 17320949) B17320949
theorem B17322659 : Blo 1423531 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B12161771 : Blo 1423531 12161771 := bstep (se 1 (by rfl) ⟨9121328, by rfl⟩ : syracuseStep 12161771 = 18242657) B18242657
theorem B1602607 : Blo 1423531 1602607 := bstep (se 1 (by rfl) ⟨1201955, by rfl⟩ : syracuseStep 1602607 = 2403911) B2403911
theorem B2028665 : Blo 1423531 2028665 := bstep (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) B1521499
theorem B10818845 : Blo 1423531 10818845 := bstep (se 3 (by rfl) ⟨2028533, by rfl⟩ : syracuseStep 10818845 = 4057067) B4057067
theorem B2135375 : Blo 1423531 2135375 := bstep (se 1 (by rfl) ⟨1601531, by rfl⟩ : syracuseStep 2135375 = 3203063) B3203063
theorem B27391355 : Blo 1423531 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B2135465 : Blo 1423531 2135465 := bstep (se 2 (by rfl) ⟨800799, by rfl⟩ : syracuseStep 2135465 = 1601599) B1601599
theorem B2135519 : Blo 1423531 2135519 := bstep (se 1 (by rfl) ⟨1601639, by rfl⟩ : syracuseStep 2135519 = 3203279) B3203279
theorem B2135615 : Blo 1423531 2135615 := bstep (se 1 (by rfl) ⟨1601711, by rfl⟩ : syracuseStep 2135615 = 3203423) B3203423
theorem B23099003 : Blo 1423531 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B4806377 : Blo 1423531 4806377 := bstep (se 2 (by rfl) ⟨1802391, by rfl⟩ : syracuseStep 4806377 = 3604783) B3604783
theorem B16226081 : Blo 1423531 16226081 := bstep (se 2 (by rfl) ⟨6084780, by rfl⟩ : syracuseStep 16226081 = 12169561) B12169561
theorem B6936479 : Blo 1423531 6936479 := bstep (se 1 (by rfl) ⟨5202359, by rfl⟩ : syracuseStep 6936479 = 10404719) B10404719
theorem B8116139 : Blo 1423531 8116139 := bstep (se 1 (by rfl) ⟨6087104, by rfl⟩ : syracuseStep 8116139 = 12174209) B12174209
theorem B1603579 : Blo 1423531 1603579 := bstep (se 1 (by rfl) ⟨1202684, by rfl⟩ : syracuseStep 1603579 = 2405369) B2405369
theorem B2136095 : Blo 1423531 2136095 := bstep (se 1 (by rfl) ⟨1602071, by rfl⟩ : syracuseStep 2136095 = 3204143) B3204143
theorem B4331551 : Blo 1423531 4331551 := bstep (se 1 (by rfl) ⟨3248663, by rfl⟩ : syracuseStep 4331551 = 6497327) B6497327
theorem B2136527 : Blo 1423531 2136527 := bstep (se 1 (by rfl) ⟨1602395, by rfl⟩ : syracuseStep 2136527 = 3204791) B3204791
theorem B18258443 : Blo 1423531 18258443 := bstep (se 1 (by rfl) ⟨13693832, by rfl⟩ : syracuseStep 18258443 = 27387665) B27387665
theorem B2136617 : Blo 1423531 2136617 := bstep (se 2 (by rfl) ⟨801231, by rfl⟩ : syracuseStep 2136617 = 1602463) B1602463
theorem B1423919 : Blo 1423531 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B10812041 : Blo 1423531 10812041 := bstep (se 2 (by rfl) ⟨4054515, by rfl⟩ : syracuseStep 10812041 = 8109031) B8109031
theorem B2136827 : Blo 1423531 2136827 := bstep (se 1 (by rfl) ⟨1602620, by rfl⟩ : syracuseStep 2136827 = 3205241) B3205241
theorem B208059151 : Blo 1423531 208059151 := bstep (se 1 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 208059151 = 312088727) B312088727
theorem B2136953 : Blo 1423531 2136953 := bstep (se 2 (by rfl) ⟨801357, by rfl⟩ : syracuseStep 2136953 = 1602715) B1602715
theorem B1424319 : Blo 1423531 1424319 := bstep (se 1 (by rfl) ⟨1068239, by rfl⟩ : syracuseStep 1424319 = 2136479) B2136479
theorem B1424367 : Blo 1423531 1424367 := bstep (se 1 (by rfl) ⟨1068275, by rfl⟩ : syracuseStep 1424367 = 2136551) B2136551
theorem B3423305 : Blo 1423531 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B7208189 : Blo 1423531 7208189 := bstep (se 3 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 7208189 = 2703071) B2703071
theorem B3603791 : Blo 1423531 3603791 := bstep (se 1 (by rfl) ⟨2702843, by rfl⟩ : syracuseStep 3603791 = 5405687) B5405687
theorem B6086011 : Blo 1423531 6086011 := bstep (se 1 (by rfl) ⟨4564508, by rfl⟩ : syracuseStep 6086011 = 9129017) B9129017
theorem B9133505 : Blo 1423531 9133505 := bstep (se 2 (by rfl) ⟨3425064, by rfl⟩ : syracuseStep 9133505 = 6850129) B6850129
theorem B1424863 : Blo 1423531 1424863 := bstep (se 1 (by rfl) ⟨1068647, by rfl⟩ : syracuseStep 1424863 = 2137295) B2137295
theorem B61636085 : Blo 1423531 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B1424943 : Blo 1423531 1424943 := bstep (se 1 (by rfl) ⟨1068707, by rfl⟩ : syracuseStep 1424943 = 2137415) B2137415
theorem B9133631 : Blo 1423531 9133631 := bstep (se 1 (by rfl) ⟨6850223, by rfl⟩ : syracuseStep 9133631 = 13700447) B13700447
theorem B2137703 : Blo 1423531 2137703 := bstep (se 1 (by rfl) ⟨1603277, by rfl⟩ : syracuseStep 2137703 = 3206555) B3206555
theorem B4562561 : Blo 1423531 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B1425051 : Blo 1423531 1425051 := bstep (se 1 (by rfl) ⟨1068788, by rfl⟩ : syracuseStep 1425051 = 2137577) B2137577
theorem B3604135 : Blo 1423531 3604135 := bstep (se 1 (by rfl) ⟨2703101, by rfl⟩ : syracuseStep 3604135 = 5406203) B5406203
theorem B1425147 : Blo 1423531 1425147 := bstep (se 1 (by rfl) ⟨1068860, by rfl⟩ : syracuseStep 1425147 = 2137721) B2137721
theorem B2137865 : Blo 1423531 2137865 := bstep (se 2 (by rfl) ⟨801699, by rfl⟩ : syracuseStep 2137865 = 1603399) B1603399
theorem B1425311 : Blo 1423531 1425311 := bstep (se 1 (by rfl) ⟨1068983, by rfl⟩ : syracuseStep 1425311 = 2137967) B2137967
theorem B8109989 : Blo 1423531 8109989 := bstep (se 4 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 8109989 = 1520623) B1520623
theorem B3203027 : Blo 1423531 3203027 := bstep (se 1 (by rfl) ⟨2402270, by rfl⟩ : syracuseStep 3203027 = 4804541) B4804541
theorem B2138087 : Blo 1423531 2138087 := bstep (se 1 (by rfl) ⟨1603565, by rfl⟩ : syracuseStep 2138087 = 3207131) B3207131
theorem B1646587 : Blo 1423531 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B5775401 : Blo 1423531 5775401 := bstep (se 2 (by rfl) ⟨2165775, by rfl⟩ : syracuseStep 5775401 = 4331551) B4331551
theorem B1425471 : Blo 1423531 1425471 := bstep (se 1 (by rfl) ⟨1069103, by rfl⟩ : syracuseStep 1425471 = 2138207) B2138207
theorem B16220249 : Blo 1423531 16220249 := bstep (se 2 (by rfl) ⟨6082593, by rfl⟩ : syracuseStep 16220249 = 12165187) B12165187
theorem B1425511 : Blo 1423531 1425511 := bstep (se 1 (by rfl) ⟨1069133, by rfl⟩ : syracuseStep 1425511 = 2138267) B2138267
theorem B5406857 : Blo 1423531 5406857 := bstep (se 2 (by rfl) ⟨2027571, by rfl⟩ : syracuseStep 5406857 = 4055143) B4055143
theorem B9257105 : Blo 1423531 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B20545771 : Blo 1423531 20545771 := bstep (se 1 (by rfl) ⟨15409328, by rfl⟩ : syracuseStep 20545771 = 30818657) B30818657
theorem B4808969 : Blo 1423531 4808969 := bstep (se 2 (by rfl) ⟨1803363, by rfl⟩ : syracuseStep 4808969 = 3606727) B3606727
theorem B7029011 : Blo 1423531 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B4809131 : Blo 1423531 4809131 := bstep (se 1 (by rfl) ⟨3606848, by rfl⟩ : syracuseStep 4809131 = 7213697) B7213697
theorem B18260903 : Blo 1423531 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B3204251 : Blo 1423531 3204251 := bstep (se 1 (by rfl) ⟨2403188, by rfl⟩ : syracuseStep 3204251 = 4806377) B4806377
theorem B3654931 : Blo 1423531 3654931 := bstep (se 1 (by rfl) ⟨2741198, by rfl⟩ : syracuseStep 3654931 = 5482397) B5482397
theorem B3204521 : Blo 1423531 3204521 := bstep (se 2 (by rfl) ⟨1201695, by rfl⟩ : syracuseStep 3204521 = 2403391) B2403391
theorem B1804123 : Blo 1423531 1804123 := bstep (se 1 (by rfl) ⟨1353092, by rfl⟩ : syracuseStep 1804123 = 2706185) B2706185
theorem B6088745 : Blo 1423531 6088745 := bstep (se 2 (by rfl) ⟨2283279, by rfl⟩ : syracuseStep 6088745 = 4566559) B4566559
theorem B5408815 : Blo 1423531 5408815 := bstep (se 1 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 5408815 = 8113223) B8113223
theorem B2402527 : Blo 1423531 2402527 := bstep (se 1 (by rfl) ⟨1801895, by rfl⟩ : syracuseStep 2402527 = 3603791) B3603791
theorem B6089003 : Blo 1423531 6089003 := bstep (se 1 (by rfl) ⟨4566752, by rfl⟩ : syracuseStep 6089003 = 9133505) B9133505
theorem B6089087 : Blo 1423531 6089087 := bstep (se 1 (by rfl) ⟨4566815, by rfl⟩ : syracuseStep 6089087 = 9133631) B9133631
theorem B3041707 : Blo 1423531 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B7211915 : Blo 1423531 7211915 := bstep (se 1 (by rfl) ⟨5408936, by rfl⟩ : syracuseStep 7211915 = 10817873) B10817873
theorem B2403263 : Blo 1423531 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B10972097 : Blo 1423531 10972097 := bstep (se 2 (by rfl) ⟨4114536, by rfl⟩ : syracuseStep 10972097 = 8229073) B8229073
theorem B5409773 : Blo 1423531 5409773 := bstep (se 3 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 5409773 = 2028665) B2028665
theorem B4058207 : Blo 1423531 4058207 := bstep (se 1 (by rfl) ⟨3043655, by rfl⟩ : syracuseStep 4058207 = 6087311) B6087311
theorem B5778647 : Blo 1423531 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B20524265 : Blo 1423531 20524265 := bstep (se 2 (by rfl) ⟨7696599, by rfl⟩ : syracuseStep 20524265 = 15393199) B15393199
theorem B10816901 : Blo 1423531 10816901 := bstep (se 4 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 10816901 = 2028169) B2028169
theorem B7212563 : Blo 1423531 7212563 := bstep (se 1 (by rfl) ⟨5409422, by rfl⟩ : syracuseStep 7212563 = 10818845) B10818845
theorem B3608185 : Blo 1423531 3608185 := bstep (se 2 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 3608185 = 2706139) B2706139
theorem B3206879 : Blo 1423531 3206879 := bstep (se 1 (by rfl) ⟨2405159, by rfl⟩ : syracuseStep 3206879 = 4810319) B4810319
theorem B10817387 : Blo 1423531 10817387 := bstep (se 1 (by rfl) ⟨8113040, by rfl⟩ : syracuseStep 10817387 = 16226081) B16226081
theorem B9744239 : Blo 1423531 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B2404255 : Blo 1423531 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B4624319 : Blo 1423531 4624319 := bstep (se 1 (by rfl) ⟨3468239, by rfl⟩ : syracuseStep 4624319 = 6936479) B6936479
theorem B5410759 : Blo 1423531 5410759 := bstep (se 1 (by rfl) ⟨4058069, by rfl⟩ : syracuseStep 5410759 = 8116139) B8116139
theorem B44462287 : Blo 1423531 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B2404687 : Blo 1423531 2404687 := bstep (se 1 (by rfl) ⟨1803515, by rfl⟩ : syracuseStep 2404687 = 3607031) B3607031
theorem B8114681 : Blo 1423531 8114681 := bstep (se 2 (by rfl) ⟨3043005, by rfl⟩ : syracuseStep 8114681 = 6086011) B6086011
theorem B10269341 : Blo 1423531 10269341 := bstep (se 3 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 10269341 = 3851003) B3851003
theorem B2282203 : Blo 1423531 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B17568505 : Blo 1423531 17568505 := bstep (se 2 (by rfl) ⟨6588189, by rfl⟩ : syracuseStep 17568505 = 13176379) B13176379
theorem B14627603 : Blo 1423531 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B4805459 : Blo 1423531 4805459 := bstep (se 1 (by rfl) ⟨3604094, by rfl⟩ : syracuseStep 4805459 = 7208189) B7208189
theorem B4805513 : Blo 1423531 4805513 := bstep (se 2 (by rfl) ⟨1802067, by rfl⟩ : syracuseStep 4805513 = 3604135) B3604135
theorem B1602751 : Blo 1423531 1602751 := bstep (se 1 (by rfl) ⟨1202063, by rfl⟩ : syracuseStep 1602751 = 2404127) B2404127
theorem B2135351 : Blo 1423531 2135351 := bstep (se 1 (by rfl) ⟨1601513, by rfl⟩ : syracuseStep 2135351 = 3203027) B3203027
theorem B9745751 : Blo 1423531 9745751 := bstep (se 1 (by rfl) ⟨7309313, by rfl⟩ : syracuseStep 9745751 = 14618627) B14618627
theorem B2135423 : Blo 1423531 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B6165931 : Blo 1423531 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B7214507 : Blo 1423531 7214507 := bstep (se 1 (by rfl) ⟨5410880, by rfl⟩ : syracuseStep 7214507 = 10821761) B10821761
theorem B2135657 : Blo 1423531 2135657 := bstep (se 2 (by rfl) ⟨800871, by rfl⟩ : syracuseStep 2135657 = 1601743) B1601743
theorem B11548271 : Blo 1423531 11548271 := bstep (se 1 (by rfl) ⟨8661203, by rfl⟩ : syracuseStep 11548271 = 17322407) B17322407
theorem B7698199 : Blo 1423531 7698199 := bstep (se 1 (by rfl) ⟨5773649, by rfl⟩ : syracuseStep 7698199 = 11547299) B11547299
theorem B11548439 : Blo 1423531 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B8107847 : Blo 1423531 8107847 := bstep (se 1 (by rfl) ⟨6080885, by rfl⟩ : syracuseStep 8107847 = 12161771) B12161771
theorem B2136191 : Blo 1423531 2136191 := bstep (se 1 (by rfl) ⟨1602143, by rfl⟩ : syracuseStep 2136191 = 3204287) B3204287
theorem B1423583 : Blo 1423531 1423583 := bstep (se 1 (by rfl) ⟨1067687, by rfl⟩ : syracuseStep 1423583 = 2135375) B2135375
theorem B1423643 : Blo 1423531 1423643 := bstep (se 1 (by rfl) ⟨1067732, by rfl⟩ : syracuseStep 1423643 = 2135465) B2135465
theorem B1423679 : Blo 1423531 1423679 := bstep (se 1 (by rfl) ⟨1067759, by rfl⟩ : syracuseStep 1423679 = 2135519) B2135519
theorem B277412201 : Blo 1423531 277412201 := bstep (se 2 (by rfl) ⟨104029575, by rfl⟩ : syracuseStep 277412201 = 208059151) B208059151
theorem B1423743 : Blo 1423531 1423743 := bstep (se 1 (by rfl) ⟨1067807, by rfl⟩ : syracuseStep 1423743 = 2135615) B2135615
theorem B73980317 : Blo 1423531 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B15399335 : Blo 1423531 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B4807295 : Blo 1423531 4807295 := bstep (se 1 (by rfl) ⟨3605471, by rfl⟩ : syracuseStep 4807295 = 7210943) B7210943
theorem B1424063 : Blo 1423531 1424063 := bstep (se 1 (by rfl) ⟨1068047, by rfl⟩ : syracuseStep 1424063 = 2136095) B2136095
theorem B2136809 : Blo 1423531 2136809 := bstep (se 2 (by rfl) ⟨801303, by rfl⟩ : syracuseStep 2136809 = 1602607) B1602607
theorem B1424351 : Blo 1423531 1424351 := bstep (se 1 (by rfl) ⟨1068263, by rfl⟩ : syracuseStep 1424351 = 2136527) B2136527
theorem B12172295 : Blo 1423531 12172295 := bstep (se 1 (by rfl) ⟨9129221, by rfl⟩ : syracuseStep 12172295 = 18258443) B18258443
theorem B1424411 : Blo 1423531 1424411 := bstep (se 1 (by rfl) ⟨1068308, by rfl⟩ : syracuseStep 1424411 = 2136617) B2136617
theorem B7208027 : Blo 1423531 7208027 := bstep (se 1 (by rfl) ⟨5406020, by rfl⟩ : syracuseStep 7208027 = 10812041) B10812041
theorem B10968155 : Blo 1423531 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B1424551 : Blo 1423531 1424551 := bstep (se 1 (by rfl) ⟨1068413, by rfl⟩ : syracuseStep 1424551 = 2136827) B2136827
theorem B1424635 : Blo 1423531 1424635 := bstep (se 1 (by rfl) ⟨1068476, by rfl⟩ : syracuseStep 1424635 = 2136953) B2136953
theorem B4808105 : Blo 1423531 4808105 := bstep (se 2 (by rfl) ⟨1803039, by rfl⟩ : syracuseStep 4808105 = 3606079) B3606079
theorem B41090723 : Blo 1423531 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B1425135 : Blo 1423531 1425135 := bstep (se 1 (by rfl) ⟨1068851, by rfl⟩ : syracuseStep 1425135 = 2137703) B2137703
theorem B1425243 : Blo 1423531 1425243 := bstep (se 1 (by rfl) ⟨1068932, by rfl⟩ : syracuseStep 1425243 = 2137865) B2137865
theorem B5406659 : Blo 1423531 5406659 := bstep (se 1 (by rfl) ⟨4054994, by rfl⟩ : syracuseStep 5406659 = 8109989) B8109989
theorem B8781797 : Blo 1423531 8781797 := bstep (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) B1646587
theorem B1425391 : Blo 1423531 1425391 := bstep (se 1 (by rfl) ⟨1069043, by rfl⟩ : syracuseStep 1425391 = 2138087) B2138087
theorem B2138105 : Blo 1423531 2138105 := bstep (se 2 (by rfl) ⟨801789, by rfl⟩ : syracuseStep 2138105 = 1603579) B1603579
theorem B3850267 : Blo 1423531 3850267 := bstep (se 1 (by rfl) ⟨2887700, by rfl⟩ : syracuseStep 3850267 = 5775401) B5775401
theorem B10813499 : Blo 1423531 10813499 := bstep (se 1 (by rfl) ⟨8110124, by rfl⟩ : syracuseStep 10813499 = 16220249) B16220249
theorem B3604571 : Blo 1423531 3604571 := bstep (se 1 (by rfl) ⟨2703428, by rfl⟩ : syracuseStep 3604571 = 5406857) B5406857
theorem B4686007 : Blo 1423531 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B3203369 : Blo 1423531 3203369 := bstep (se 2 (by rfl) ⟨1201263, by rfl⟩ : syracuseStep 3203369 = 2402527) B2402527
theorem B27394361 : Blo 1423531 27394361 := bstep (se 2 (by rfl) ⟨10272885, by rfl⟩ : syracuseStep 27394361 = 20545771) B20545771
theorem B3203639 : Blo 1423531 3203639 := bstep (se 1 (by rfl) ⟨2402729, by rfl⟩ : syracuseStep 3203639 = 4805459) B4805459
theorem B4055609 : Blo 1423531 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B3203675 : Blo 1423531 3203675 := bstep (se 1 (by rfl) ⟨2402756, by rfl⟩ : syracuseStep 3203675 = 4805513) B4805513
theorem B12173935 : Blo 1423531 12173935 := bstep (se 1 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 12173935 = 18260903) B18260903
theorem B6497167 : Blo 1423531 6497167 := bstep (se 1 (by rfl) ⟨4872875, by rfl⟩ : syracuseStep 6497167 = 9745751) B9745751
theorem B4809671 : Blo 1423531 4809671 := bstep (se 1 (by rfl) ⟨3607253, by rfl⟩ : syracuseStep 4809671 = 7214507) B7214507
theorem B10266223 : Blo 1423531 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B30795389 : Blo 1423531 30795389 := bstep (se 3 (by rfl) ⟨5774135, by rfl⟩ : syracuseStep 30795389 = 11548271) B11548271
theorem B3204863 : Blo 1423531 3204863 := bstep (se 1 (by rfl) ⟨2403647, by rfl⟩ : syracuseStep 3204863 = 4807295) B4807295
theorem B3606515 : Blo 1423531 3606515 := bstep (se 1 (by rfl) ⟨2704886, by rfl⟩ : syracuseStep 3606515 = 5409773) B5409773
theorem B2705471 : Blo 1423531 2705471 := bstep (se 1 (by rfl) ⟨2029103, by rfl⟩ : syracuseStep 2705471 = 4058207) B4058207
theorem B3852431 : Blo 1423531 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B13682843 : Blo 1423531 13682843 := bstep (se 1 (by rfl) ⟨10262132, by rfl⟩ : syracuseStep 13682843 = 20524265) B20524265
theorem B4810913 : Blo 1423531 4810913 := bstep (se 2 (by rfl) ⟨1804092, by rfl⟩ : syracuseStep 4810913 = 3608185) B3608185
theorem B7211267 : Blo 1423531 7211267 := bstep (se 1 (by rfl) ⟨5408450, by rfl⟩ : syracuseStep 7211267 = 10816901) B10816901
theorem B3205403 : Blo 1423531 3205403 := bstep (se 1 (by rfl) ⟨2404052, by rfl⟩ : syracuseStep 3205403 = 4808105) B4808105
theorem B3205673 : Blo 1423531 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B7211591 : Blo 1423531 7211591 := bstep (se 1 (by rfl) ⟨5408693, by rfl⟩ : syracuseStep 7211591 = 10817387) B10817387
theorem B3082879 : Blo 1423531 3082879 := bstep (se 1 (by rfl) ⟨2312159, by rfl⟩ : syracuseStep 3082879 = 4624319) B4624319
theorem B7211753 : Blo 1423531 7211753 := bstep (se 2 (by rfl) ⟨2704407, by rfl⟩ : syracuseStep 7211753 = 5408815) B5408815
theorem B6171403 : Blo 1423531 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B3205979 : Blo 1423531 3205979 := bstep (se 1 (by rfl) ⟨2404484, by rfl⟩ : syracuseStep 3205979 = 4808969) B4808969
theorem B3206087 : Blo 1423531 3206087 := bstep (se 1 (by rfl) ⟨2404565, by rfl⟩ : syracuseStep 3206087 = 4809131) B4809131
theorem B5409787 : Blo 1423531 5409787 := bstep (se 1 (by rfl) ⟨4057340, by rfl⟩ : syracuseStep 5409787 = 8114681) B8114681
theorem B3206249 : Blo 1423531 3206249 := bstep (se 2 (by rfl) ⟨1202343, by rfl⟩ : syracuseStep 3206249 = 2404687) B2404687
theorem B9751735 : Blo 1423531 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B1425403 : Blo 1423531 1425403 := bstep (se 1 (by rfl) ⟨1069052, by rfl⟩ : syracuseStep 1425403 = 2138105) B2138105
theorem B3042937 : Blo 1423531 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B23424673 : Blo 1423531 23424673 := bstep (se 2 (by rfl) ⟨8784252, by rfl⟩ : syracuseStep 23424673 = 17568505) B17568505
theorem B4059163 : Blo 1423531 4059163 := bstep (se 1 (by rfl) ⟨3044372, by rfl⟩ : syracuseStep 4059163 = 6088745) B6088745
theorem B4059335 : Blo 1423531 4059335 := bstep (se 1 (by rfl) ⟨3044501, by rfl⟩ : syracuseStep 4059335 = 6089003) B6089003
theorem B4059391 : Blo 1423531 4059391 := bstep (se 1 (by rfl) ⟨3044543, by rfl⟩ : syracuseStep 4059391 = 6089087) B6089087
theorem B49320211 : Blo 1423531 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B8221241 : Blo 1423531 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B1602175 : Blo 1423531 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B8114863 : Blo 1423531 8114863 := bstep (se 1 (by rfl) ⟨6086147, by rfl⟩ : syracuseStep 8114863 = 12172295) B12172295
theorem B4805351 : Blo 1423531 4805351 := bstep (se 1 (by rfl) ⟨3604013, by rfl⟩ : syracuseStep 4805351 = 7208027) B7208027
theorem B7312103 : Blo 1423531 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B2405497 : Blo 1423531 2405497 := bstep (se 2 (by rfl) ⟨902061, by rfl⟩ : syracuseStep 2405497 = 1804123) B1804123
theorem B7214345 : Blo 1423531 7214345 := bstep (se 2 (by rfl) ⟨2705379, by rfl⟩ : syracuseStep 7214345 = 5410759) B5410759
theorem B5854531 : Blo 1423531 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B6846227 : Blo 1423531 6846227 := bstep (se 1 (by rfl) ⟨5134670, by rfl⟩ : syracuseStep 6846227 = 10269341) B10269341
theorem B2136167 : Blo 1423531 2136167 := bstep (se 1 (by rfl) ⟨1602125, by rfl⟩ : syracuseStep 2136167 = 3204251) B3204251
theorem B1423567 : Blo 1423531 1423567 := bstep (se 1 (by rfl) ⟨1067675, by rfl⟩ : syracuseStep 1423567 = 2135351) B2135351
theorem B1423615 : Blo 1423531 1423615 := bstep (se 1 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 1423615 = 2135423) B2135423
theorem B2136347 : Blo 1423531 2136347 := bstep (se 1 (by rfl) ⟨1602260, by rfl⟩ : syracuseStep 2136347 = 3204521) B3204521
theorem B1423771 : Blo 1423531 1423771 := bstep (se 1 (by rfl) ⟨1067828, by rfl⟩ : syracuseStep 1423771 = 2135657) B2135657
theorem B237132197 : Blo 1423531 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B7698959 : Blo 1423531 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B5405231 : Blo 1423531 5405231 := bstep (se 1 (by rfl) ⟨4053923, by rfl⟩ : syracuseStep 5405231 = 8107847) B8107847
theorem B1424127 : Blo 1423531 1424127 := bstep (se 1 (by rfl) ⟨1068095, by rfl⟩ : syracuseStep 1424127 = 2136191) B2136191
theorem B184941467 : Blo 1423531 184941467 := bstep (se 1 (by rfl) ⟨138706100, by rfl⟩ : syracuseStep 184941467 = 277412201) B277412201
theorem B2137001 : Blo 1423531 2137001 := bstep (se 2 (by rfl) ⟨801375, by rfl⟩ : syracuseStep 2137001 = 1602751) B1602751
theorem B4873241 : Blo 1423531 4873241 := bstep (se 2 (by rfl) ⟨1827465, by rfl⟩ : syracuseStep 4873241 = 3654931) B3654931
theorem B1424539 : Blo 1423531 1424539 := bstep (se 1 (by rfl) ⟨1068404, by rfl⟩ : syracuseStep 1424539 = 2136809) B2136809
theorem B4807943 : Blo 1423531 4807943 := bstep (se 1 (by rfl) ⟨3605957, by rfl⟩ : syracuseStep 4807943 = 7211915) B7211915
theorem B7314731 : Blo 1423531 7314731 := bstep (se 1 (by rfl) ⟨5486048, by rfl⟩ : syracuseStep 7314731 = 10972097) B10972097
theorem B25984637 : Blo 1423531 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B4808375 : Blo 1423531 4808375 := bstep (se 1 (by rfl) ⟨3606281, by rfl⟩ : syracuseStep 4808375 = 7212563) B7212563
theorem B10264265 : Blo 1423531 10264265 := bstep (se 2 (by rfl) ⟨3849099, by rfl⟩ : syracuseStep 10264265 = 7698199) B7698199
theorem B27393815 : Blo 1423531 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B2137919 : Blo 1423531 2137919 := bstep (se 1 (by rfl) ⟨1603439, by rfl⟩ : syracuseStep 2137919 = 3206879) B3206879
theorem B3604439 : Blo 1423531 3604439 := bstep (se 1 (by rfl) ⟨2703329, by rfl⟩ : syracuseStep 3604439 = 5406659) B5406659
theorem B7208999 : Blo 1423531 7208999 := bstep (se 1 (by rfl) ⟨5406749, by rfl⟩ : syracuseStep 7208999 = 10813499) B10813499
theorem B5480827 : Blo 1423531 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B3203567 : Blo 1423531 3203567 := bstep (se 1 (by rfl) ⟨2402675, by rfl⟩ : syracuseStep 3203567 = 4805351) B4805351
theorem B4874735 : Blo 1423531 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B16228997 : Blo 1423531 16228997 := bstep (se 4 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 16228997 = 3042937) B3042937
theorem B16442021 : Blo 1423531 16442021 := bstep (se 4 (by rfl) ⟨1541439, by rfl⟩ : syracuseStep 16442021 = 3082879) B3082879
theorem B4809563 : Blo 1423531 4809563 := bstep (se 1 (by rfl) ⟨3607172, by rfl⟩ : syracuseStep 4809563 = 7214345) B7214345
theorem B20530259 : Blo 1423531 20530259 := bstep (se 1 (by rfl) ⟨15397694, by rfl⟩ : syracuseStep 20530259 = 30795389) B30795389
theorem B4564151 : Blo 1423531 4564151 := bstep (se 1 (by rfl) ⟨3423113, by rfl⟩ : syracuseStep 4564151 = 6846227) B6846227
theorem B1803647 : Blo 1423531 1803647 := bstep (se 1 (by rfl) ⟨1352735, by rfl⟩ : syracuseStep 1803647 = 2705471) B2705471
theorem B10814957 : Blo 1423531 10814957 := bstep (se 3 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 10814957 = 4055609) B4055609
theorem B3205295 : Blo 1423531 3205295 := bstep (se 1 (by rfl) ⟨2403971, by rfl⟩ : syracuseStep 3205295 = 4807943) B4807943
theorem B4876487 : Blo 1423531 4876487 := bstep (se 1 (by rfl) ⟨3657365, by rfl⟩ : syracuseStep 4876487 = 7314731) B7314731
theorem B3205583 : Blo 1423531 3205583 := bstep (se 1 (by rfl) ⟨2404187, by rfl⟩ : syracuseStep 3205583 = 4808375) B4808375
theorem B6842843 : Blo 1423531 6842843 := bstep (se 1 (by rfl) ⟨5132132, by rfl⟩ : syracuseStep 6842843 = 10264265) B10264265
theorem B18262543 : Blo 1423531 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B2402959 : Blo 1423531 2402959 := bstep (se 1 (by rfl) ⟨1802219, by rfl⟩ : syracuseStep 2402959 = 3604439) B3604439
theorem B2403047 : Blo 1423531 2403047 := bstep (se 1 (by rfl) ⟨1802285, by rfl⟩ : syracuseStep 2403047 = 3604571) B3604571
theorem B12995309 : Blo 1423531 12995309 := bstep (se 3 (by rfl) ⟨2436620, by rfl⟩ : syracuseStep 12995309 = 4873241) B4873241
theorem B2706223 : Blo 1423531 2706223 := bstep (se 1 (by rfl) ⟨2029667, by rfl⟩ : syracuseStep 2706223 = 4059335) B4059335
theorem B18262907 : Blo 1423531 18262907 := bstep (se 1 (by rfl) ⟨13697180, by rfl⟩ : syracuseStep 18262907 = 27394361) B27394361
theorem B65760281 : Blo 1423531 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B3206447 : Blo 1423531 3206447 := bstep (se 1 (by rfl) ⟨2404835, by rfl⟩ : syracuseStep 3206447 = 4809671) B4809671
theorem B16231913 : Blo 1423531 16231913 := bstep (se 2 (by rfl) ⟨6086967, by rfl⟩ : syracuseStep 16231913 = 12173935) B12173935
theorem B8228537 : Blo 1423531 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B8662889 : Blo 1423531 8662889 := bstep (se 2 (by rfl) ⟨3248583, by rfl⟩ : syracuseStep 8662889 = 6497167) B6497167
theorem B2404343 : Blo 1423531 2404343 := bstep (se 1 (by rfl) ⟨1803257, by rfl⟩ : syracuseStep 2404343 = 3606515) B3606515
theorem B7213049 : Blo 1423531 7213049 := bstep (se 2 (by rfl) ⟨2704893, by rfl⟩ : syracuseStep 7213049 = 5409787) B5409787
theorem B2568287 : Blo 1423531 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B9121895 : Blo 1423531 9121895 := bstep (se 1 (by rfl) ⟨6841421, by rfl⟩ : syracuseStep 9121895 = 13682843) B13682843
theorem B3207275 : Blo 1423531 3207275 := bstep (se 1 (by rfl) ⟨2405456, by rfl⟩ : syracuseStep 3207275 = 4810913) B4810913
theorem B3207329 : Blo 1423531 3207329 := bstep (se 2 (by rfl) ⟨1202748, by rfl⟩ : syracuseStep 3207329 = 2405497) B2405497
theorem B5132639 : Blo 1423531 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B123294311 : Blo 1423531 123294311 := bstep (se 1 (by rfl) ⟨92470733, by rfl⟩ : syracuseStep 123294311 = 184941467) B184941467
theorem B31232897 : Blo 1423531 31232897 := bstep (se 2 (by rfl) ⟨11712336, by rfl⟩ : syracuseStep 31232897 = 23424673) B23424673
theorem B17323091 : Blo 1423531 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B5133689 : Blo 1423531 5133689 := bstep (se 2 (by rfl) ⟨1925133, by rfl⟩ : syracuseStep 5133689 = 3850267) B3850267
theorem B5412217 : Blo 1423531 5412217 := bstep (se 2 (by rfl) ⟨2029581, by rfl⟩ : syracuseStep 5412217 = 4059163) B4059163
theorem B2135579 : Blo 1423531 2135579 := bstep (se 1 (by rfl) ⟨1601684, by rfl⟩ : syracuseStep 2135579 = 3203369) B3203369
theorem B6248009 : Blo 1423531 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B5412521 : Blo 1423531 5412521 := bstep (se 2 (by rfl) ⟨2029695, by rfl⟩ : syracuseStep 5412521 = 4059391) B4059391
theorem B2135759 : Blo 1423531 2135759 := bstep (se 1 (by rfl) ⟨1601819, by rfl⟩ : syracuseStep 2135759 = 3203639) B3203639
theorem B2135783 : Blo 1423531 2135783 := bstep (se 1 (by rfl) ⟨1601837, by rfl⟩ : syracuseStep 2135783 = 3203675) B3203675
theorem B2136233 : Blo 1423531 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B10819817 : Blo 1423531 10819817 := bstep (se 2 (by rfl) ⟨4057431, by rfl⟩ : syracuseStep 10819817 = 8114863) B8114863
theorem B52009253 : Blo 1423531 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B2136575 : Blo 1423531 2136575 := bstep (se 1 (by rfl) ⟨1602431, by rfl⟩ : syracuseStep 2136575 = 3204863) B3204863
theorem B1424111 : Blo 1423531 1424111 := bstep (se 1 (by rfl) ⟨1068083, by rfl⟩ : syracuseStep 1424111 = 2136167) B2136167
theorem B4807511 : Blo 1423531 4807511 := bstep (se 1 (by rfl) ⟨3605633, by rfl⟩ : syracuseStep 4807511 = 7211267) B7211267
theorem B1424231 : Blo 1423531 1424231 := bstep (se 1 (by rfl) ⟨1068173, by rfl⟩ : syracuseStep 1424231 = 2136347) B2136347
theorem B2136935 : Blo 1423531 2136935 := bstep (se 1 (by rfl) ⟨1602701, by rfl⟩ : syracuseStep 2136935 = 3205403) B3205403
theorem B158088131 : Blo 1423531 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B2137115 : Blo 1423531 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B3603487 : Blo 1423531 3603487 := bstep (se 1 (by rfl) ⟨2702615, by rfl⟩ : syracuseStep 3603487 = 5405231) B5405231
theorem B4807727 : Blo 1423531 4807727 := bstep (se 1 (by rfl) ⟨3605795, by rfl⟩ : syracuseStep 4807727 = 7211591) B7211591
theorem B7806041 : Blo 1423531 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B4807835 : Blo 1423531 4807835 := bstep (se 1 (by rfl) ⟨3605876, by rfl⟩ : syracuseStep 4807835 = 7211753) B7211753
theorem B2137319 : Blo 1423531 2137319 := bstep (se 1 (by rfl) ⟨1602989, by rfl⟩ : syracuseStep 2137319 = 3205979) B3205979
theorem B1424667 : Blo 1423531 1424667 := bstep (se 1 (by rfl) ⟨1068500, by rfl⟩ : syracuseStep 1424667 = 2137001) B2137001
theorem B2137391 : Blo 1423531 2137391 := bstep (se 1 (by rfl) ⟨1603043, by rfl⟩ : syracuseStep 2137391 = 3206087) B3206087
theorem B2137499 : Blo 1423531 2137499 := bstep (se 1 (by rfl) ⟨1603124, by rfl⟩ : syracuseStep 2137499 = 3206249) B3206249
theorem B13688297 : Blo 1423531 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B1425279 : Blo 1423531 1425279 := bstep (se 1 (by rfl) ⟨1068959, by rfl⟩ : syracuseStep 1425279 = 2137919) B2137919
theorem B1712191 : Blo 1423531 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B2138183 : Blo 1423531 2138183 := bstep (se 1 (by rfl) ⟨1603637, by rfl⟩ : syracuseStep 2138183 = 3207275) B3207275
theorem B2138219 : Blo 1423531 2138219 := bstep (se 1 (by rfl) ⟨1603664, by rfl⟩ : syracuseStep 2138219 = 3207329) B3207329
theorem B10961347 : Blo 1423531 10961347 := bstep (se 1 (by rfl) ⟨8221010, by rfl⟩ : syracuseStep 10961347 = 16442021) B16442021
theorem B3203945 : Blo 1423531 3203945 := bstep (se 2 (by rfl) ⟨1201479, by rfl⟩ : syracuseStep 3203945 = 2402959) B2402959
theorem B7209971 : Blo 1423531 7209971 := bstep (se 1 (by rfl) ⟨5407478, by rfl⟩ : syracuseStep 7209971 = 10814957) B10814957
theorem B4809725 : Blo 1423531 4809725 := bstep (se 3 (by rfl) ⟨901823, by rfl⟩ : syracuseStep 4809725 = 1803647) B1803647
theorem B3205007 : Blo 1423531 3205007 := bstep (se 1 (by rfl) ⟨2403755, by rfl⟩ : syracuseStep 3205007 = 4807511) B4807511
theorem B12175271 : Blo 1423531 12175271 := bstep (se 1 (by rfl) ⟨9131453, by rfl⟩ : syracuseStep 12175271 = 18262907) B18262907
theorem B105392087 : Blo 1423531 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B29231077 : Blo 1423531 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B3205151 : Blo 1423531 3205151 := bstep (se 1 (by rfl) ⟨2403863, by rfl⟩ : syracuseStep 3205151 = 4807727) B4807727
theorem B5204027 : Blo 1423531 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B3205223 : Blo 1423531 3205223 := bstep (se 1 (by rfl) ⟨2403917, by rfl⟩ : syracuseStep 3205223 = 4807835) B4807835
theorem B4808699 : Blo 1423531 4808699 := bstep (se 1 (by rfl) ⟨3606524, by rfl⟩ : syracuseStep 4808699 = 7213049) B7213049
theorem B6081263 : Blo 1423531 6081263 := bstep (se 1 (by rfl) ⟨4560947, by rfl⟩ : syracuseStep 6081263 = 9121895) B9121895
theorem B3206375 : Blo 1423531 3206375 := bstep (se 1 (by rfl) ⟨2404781, by rfl⟩ : syracuseStep 3206375 = 4809563) B4809563
theorem B24350057 : Blo 1423531 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B3042767 : Blo 1423531 3042767 := bstep (se 1 (by rfl) ⟨2282075, by rfl⟩ : syracuseStep 3042767 = 4564151) B4564151
theorem B4165339 : Blo 1423531 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B3608297 : Blo 1423531 3608297 := bstep (se 2 (by rfl) ⟨1353111, by rfl⟩ : syracuseStep 3608297 = 2706223) B2706223
theorem B3608347 : Blo 1423531 3608347 := bstep (se 1 (by rfl) ⟨2706260, by rfl⟩ : syracuseStep 3608347 = 5412521) B5412521
theorem B4804649 : Blo 1423531 4804649 := bstep (se 2 (by rfl) ⟨1801743, by rfl⟩ : syracuseStep 4804649 = 3603487) B3603487
theorem B7213211 : Blo 1423531 7213211 := bstep (se 1 (by rfl) ⟨5409908, by rfl⟩ : syracuseStep 7213211 = 10819817) B10819817
theorem B34672835 : Blo 1423531 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B1602031 : Blo 1423531 1602031 := bstep (se 1 (by rfl) ⟨1201523, by rfl⟩ : syracuseStep 1602031 = 2403047) B2403047
theorem B8663539 : Blo 1423531 8663539 := bstep (se 1 (by rfl) ⟨6497654, by rfl⟩ : syracuseStep 8663539 = 12995309) B12995309
theorem B43840187 : Blo 1423531 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B5485691 : Blo 1423531 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B1602895 : Blo 1423531 1602895 := bstep (se 1 (by rfl) ⟨1202171, by rfl⟩ : syracuseStep 1602895 = 2404343) B2404343
theorem B4805999 : Blo 1423531 4805999 := bstep (se 1 (by rfl) ⟨3604499, by rfl⟩ : syracuseStep 4805999 = 7208999) B7208999
theorem B3421759 : Blo 1423531 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B2135711 : Blo 1423531 2135711 := bstep (se 1 (by rfl) ⟨1601783, by rfl⟩ : syracuseStep 2135711 = 3203567) B3203567
theorem B3249823 : Blo 1423531 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B82196207 : Blo 1423531 82196207 := bstep (se 1 (by rfl) ⟨61647155, by rfl⟩ : syracuseStep 82196207 = 123294311) B123294311
theorem B10819331 : Blo 1423531 10819331 := bstep (se 1 (by rfl) ⟨8114498, by rfl⟩ : syracuseStep 10819331 = 16228997) B16228997
theorem B20821931 : Blo 1423531 20821931 := bstep (se 1 (by rfl) ⟨15616448, by rfl⟩ : syracuseStep 20821931 = 31232897) B31232897
theorem B13686839 : Blo 1423531 13686839 := bstep (se 1 (by rfl) ⟨10265129, by rfl⟩ : syracuseStep 13686839 = 20530259) B20530259
theorem B11548727 : Blo 1423531 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B3422459 : Blo 1423531 3422459 := bstep (se 1 (by rfl) ⟨2566844, by rfl⟩ : syracuseStep 3422459 = 5133689) B5133689
theorem B1423719 : Blo 1423531 1423719 := bstep (se 1 (by rfl) ⟨1067789, by rfl⟩ : syracuseStep 1423719 = 2135579) B2135579
theorem B1423839 : Blo 1423531 1423839 := bstep (se 1 (by rfl) ⟨1067879, by rfl⟩ : syracuseStep 1423839 = 2135759) B2135759
theorem B1423855 : Blo 1423531 1423855 := bstep (se 1 (by rfl) ⟨1067891, by rfl⟩ : syracuseStep 1423855 = 2135783) B2135783
theorem B1424155 : Blo 1423531 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B2136863 : Blo 1423531 2136863 := bstep (se 1 (by rfl) ⟨1602647, by rfl⟩ : syracuseStep 2136863 = 3205295) B3205295
theorem B3250991 : Blo 1423531 3250991 := bstep (se 1 (by rfl) ⟨2438243, by rfl⟩ : syracuseStep 3250991 = 4876487) B4876487
theorem B2137055 : Blo 1423531 2137055 := bstep (se 1 (by rfl) ⟨1602791, by rfl⟩ : syracuseStep 2137055 = 3205583) B3205583
theorem B4561895 : Blo 1423531 4561895 := bstep (se 1 (by rfl) ⟨3421421, by rfl⟩ : syracuseStep 4561895 = 6842843) B6842843
theorem B1424383 : Blo 1423531 1424383 := bstep (se 1 (by rfl) ⟨1068287, by rfl⟩ : syracuseStep 1424383 = 2136575) B2136575
theorem B7216289 : Blo 1423531 7216289 := bstep (se 2 (by rfl) ⟨2706108, by rfl⟩ : syracuseStep 7216289 = 5412217) B5412217
theorem B1424623 : Blo 1423531 1424623 := bstep (se 1 (by rfl) ⟨1068467, by rfl⟩ : syracuseStep 1424623 = 2136935) B2136935
theorem B1424743 : Blo 1423531 1424743 := bstep (se 1 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 1424743 = 2137115) B2137115
theorem B1424879 : Blo 1423531 1424879 := bstep (se 1 (by rfl) ⟨1068659, by rfl⟩ : syracuseStep 1424879 = 2137319) B2137319
theorem B1424927 : Blo 1423531 1424927 := bstep (se 1 (by rfl) ⟨1068695, by rfl⟩ : syracuseStep 1424927 = 2137391) B2137391
theorem B2137631 : Blo 1423531 2137631 := bstep (se 1 (by rfl) ⟨1603223, by rfl⟩ : syracuseStep 2137631 = 3206447) B3206447
theorem B1424999 : Blo 1423531 1424999 := bstep (se 1 (by rfl) ⟨1068749, by rfl⟩ : syracuseStep 1424999 = 2137499) B2137499
theorem B9125531 : Blo 1423531 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B10821275 : Blo 1423531 10821275 := bstep (se 1 (by rfl) ⟨8115956, by rfl⟩ : syracuseStep 10821275 = 16231913) B16231913
theorem B5775259 : Blo 1423531 5775259 := bstep (se 1 (by rfl) ⟨4331444, by rfl⟩ : syracuseStep 5775259 = 8662889) B8662889
theorem B3203099 : Blo 1423531 3203099 := bstep (se 1 (by rfl) ⟨2402324, by rfl⟩ : syracuseStep 3203099 = 4804649) B4804649
theorem B1425455 : Blo 1423531 1425455 := bstep (se 1 (by rfl) ⟨1069091, by rfl⟩ : syracuseStep 1425455 = 2138183) B2138183
theorem B1425479 : Blo 1423531 1425479 := bstep (se 1 (by rfl) ⟨1069109, by rfl⟩ : syracuseStep 1425479 = 2138219) B2138219
theorem B4808807 : Blo 1423531 4808807 := bstep (se 1 (by rfl) ⟨3606605, by rfl⟩ : syracuseStep 4808807 = 7213211) B7213211
theorem B13877405 : Blo 1423531 13877405 := bstep (se 3 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 13877405 = 5204027) B5204027
theorem B14615129 : Blo 1423531 14615129 := bstep (se 2 (by rfl) ⟨5480673, by rfl⟩ : syracuseStep 14615129 = 10961347) B10961347
theorem B11551385 : Blo 1423531 11551385 := bstep (se 2 (by rfl) ⟨4331769, by rfl⟩ : syracuseStep 11551385 = 8663539) B8663539
theorem B9126557 : Blo 1423531 9126557 := bstep (se 3 (by rfl) ⟨1711229, by rfl⟩ : syracuseStep 9126557 = 3422459) B3422459
theorem B3203999 : Blo 1423531 3203999 := bstep (se 1 (by rfl) ⟨2402999, by rfl⟩ : syracuseStep 3203999 = 4805999) B4805999
theorem B54797471 : Blo 1423531 54797471 := bstep (se 1 (by rfl) ⟨41098103, by rfl⟩ : syracuseStep 54797471 = 82196207) B82196207
theorem B3041263 : Blo 1423531 3041263 := bstep (se 1 (by rfl) ⟨2280947, by rfl⟩ : syracuseStep 3041263 = 4561895) B4561895
theorem B4810859 : Blo 1423531 4810859 := bstep (se 1 (by rfl) ⟨3608144, by rfl⟩ : syracuseStep 4810859 = 7216289) B7216289
theorem B4811129 : Blo 1423531 4811129 := bstep (se 2 (by rfl) ⟨1804173, by rfl⟩ : syracuseStep 4811129 = 3608347) B3608347
theorem B3205799 : Blo 1423531 3205799 := bstep (se 1 (by rfl) ⟨2404349, by rfl⟩ : syracuseStep 3205799 = 4808699) B4808699
theorem B3206483 : Blo 1423531 3206483 := bstep (se 1 (by rfl) ⟨2404862, by rfl⟩ : syracuseStep 3206483 = 4809725) B4809725
theorem B7212887 : Blo 1423531 7212887 := bstep (se 1 (by rfl) ⟨5409665, by rfl⟩ : syracuseStep 7212887 = 10819331) B10819331
theorem B13881287 : Blo 1423531 13881287 := bstep (se 1 (by rfl) ⟨10410965, by rfl⟩ : syracuseStep 13881287 = 20821931) B20821931
theorem B2167327 : Blo 1423531 2167327 := bstep (se 1 (by rfl) ⟨1625495, by rfl⟩ : syracuseStep 2167327 = 3250991) B3250991
theorem B16233371 : Blo 1423531 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B2028511 : Blo 1423531 2028511 := bstep (se 1 (by rfl) ⟨1521383, by rfl⟩ : syracuseStep 2028511 = 3042767) B3042767
theorem B6083687 : Blo 1423531 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B7214183 : Blo 1423531 7214183 := bstep (se 1 (by rfl) ⟨5410637, by rfl⟩ : syracuseStep 7214183 = 10821275) B10821275
theorem B2405531 : Blo 1423531 2405531 := bstep (se 1 (by rfl) ⟨1804148, by rfl⟩ : syracuseStep 2405531 = 3608297) B3608297
theorem B38974769 : Blo 1423531 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B2282921 : Blo 1423531 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B23115223 : Blo 1423531 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B14628509 : Blo 1423531 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B29226791 : Blo 1423531 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B2135963 : Blo 1423531 2135963 := bstep (se 1 (by rfl) ⟨1601972, by rfl⟩ : syracuseStep 2135963 = 3203945) B3203945
theorem B2136041 : Blo 1423531 2136041 := bstep (se 2 (by rfl) ⟨801015, by rfl⟩ : syracuseStep 2136041 = 1602031) B1602031
theorem B4806647 : Blo 1423531 4806647 := bstep (se 1 (by rfl) ⟨3604985, by rfl⟩ : syracuseStep 4806647 = 7209971) B7209971
theorem B1423807 : Blo 1423531 1423807 := bstep (se 1 (by rfl) ⟨1067855, by rfl⟩ : syracuseStep 1423807 = 2135711) B2135711
theorem B2136671 : Blo 1423531 2136671 := bstep (se 1 (by rfl) ⟨1602503, by rfl⟩ : syracuseStep 2136671 = 3205007) B3205007
theorem B8116847 : Blo 1423531 8116847 := bstep (se 1 (by rfl) ⟨6087635, by rfl⟩ : syracuseStep 8116847 = 12175271) B12175271
theorem B70261391 : Blo 1423531 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B2136767 : Blo 1423531 2136767 := bstep (se 1 (by rfl) ⟨1602575, by rfl⟩ : syracuseStep 2136767 = 3205151) B3205151
theorem B9124559 : Blo 1423531 9124559 := bstep (se 1 (by rfl) ⟨6843419, by rfl⟩ : syracuseStep 9124559 = 13686839) B13686839
theorem B7699151 : Blo 1423531 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B2136815 : Blo 1423531 2136815 := bstep (se 1 (by rfl) ⟨1602611, by rfl⟩ : syracuseStep 2136815 = 3205223) B3205223
theorem B2137193 : Blo 1423531 2137193 := bstep (se 2 (by rfl) ⟨801447, by rfl⟩ : syracuseStep 2137193 = 1602895) B1602895
theorem B4054175 : Blo 1423531 4054175 := bstep (se 1 (by rfl) ⟨3040631, by rfl⟩ : syracuseStep 4054175 = 6081263) B6081263
theorem B1424575 : Blo 1423531 1424575 := bstep (se 1 (by rfl) ⟨1068431, by rfl⟩ : syracuseStep 1424575 = 2136863) B2136863
theorem B1424703 : Blo 1423531 1424703 := bstep (se 1 (by rfl) ⟨1068527, by rfl⟩ : syracuseStep 1424703 = 2137055) B2137055
theorem B4562345 : Blo 1423531 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B2137583 : Blo 1423531 2137583 := bstep (se 1 (by rfl) ⟨1603187, by rfl⟩ : syracuseStep 2137583 = 3206375) B3206375
theorem B4333097 : Blo 1423531 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B5553785 : Blo 1423531 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B1425087 : Blo 1423531 1425087 := bstep (se 1 (by rfl) ⟨1068815, by rfl⟩ : syracuseStep 1425087 = 2137631) B2137631
theorem B7700345 : Blo 1423531 7700345 := bstep (se 2 (by rfl) ⟨2887629, by rfl⟩ : syracuseStep 7700345 = 5775259) B5775259
theorem B7700923 : Blo 1423531 7700923 := bstep (se 1 (by rfl) ⟨5775692, by rfl⟩ : syracuseStep 7700923 = 11551385) B11551385
theorem B10822247 : Blo 1423531 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B4809455 : Blo 1423531 4809455 := bstep (se 1 (by rfl) ⟨3607091, by rfl⟩ : syracuseStep 4809455 = 7214183) B7214183
theorem B2704681 : Blo 1423531 2704681 := bstep (se 2 (by rfl) ⟨1014255, by rfl⟩ : syracuseStep 2704681 = 2028511) B2028511
theorem B3204431 : Blo 1423531 3204431 := bstep (se 1 (by rfl) ⟨2403323, by rfl⟩ : syracuseStep 3204431 = 4806647) B4806647
theorem B30820297 : Blo 1423531 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B3041563 : Blo 1423531 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B3205871 : Blo 1423531 3205871 := bstep (se 1 (by rfl) ⟨2404403, by rfl⟩ : syracuseStep 3205871 = 4808807) B4808807
theorem B9251603 : Blo 1423531 9251603 := bstep (se 1 (by rfl) ⟨6938702, by rfl⟩ : syracuseStep 9251603 = 13877405) B13877405
theorem B16223165 : Blo 1423531 16223165 := bstep (se 3 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 16223165 = 6083687) B6083687
theorem B9743419 : Blo 1423531 9743419 := bstep (se 1 (by rfl) ⟨7307564, by rfl⟩ : syracuseStep 9743419 = 14615129) B14615129
theorem B36531647 : Blo 1423531 36531647 := bstep (se 1 (by rfl) ⟨27398735, by rfl⟩ : syracuseStep 36531647 = 54797471) B54797471
theorem B9752339 : Blo 1423531 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B3207239 : Blo 1423531 3207239 := bstep (se 1 (by rfl) ⟨2405429, by rfl⟩ : syracuseStep 3207239 = 4810859) B4810859
theorem B3207419 : Blo 1423531 3207419 := bstep (se 1 (by rfl) ⟨2405564, by rfl⟩ : syracuseStep 3207419 = 4811129) B4811129
theorem B5411231 : Blo 1423531 5411231 := bstep (se 1 (by rfl) ⟨4058423, by rfl⟩ : syracuseStep 5411231 = 8116847) B8116847
theorem B6083039 : Blo 1423531 6083039 := bstep (se 1 (by rfl) ⟨4562279, by rfl⟩ : syracuseStep 6083039 = 9124559) B9124559
theorem B5132767 : Blo 1423531 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B2888731 : Blo 1423531 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B5133563 : Blo 1423531 5133563 := bstep (se 1 (by rfl) ⟨3850172, by rfl⟩ : syracuseStep 5133563 = 7700345) B7700345
theorem B9254191 : Blo 1423531 9254191 := bstep (se 1 (by rfl) ⟨6940643, by rfl⟩ : syracuseStep 9254191 = 13881287) B13881287
theorem B2135399 : Blo 1423531 2135399 := bstep (se 1 (by rfl) ⟨1601549, by rfl⟩ : syracuseStep 2135399 = 3203099) B3203099
theorem B6084371 : Blo 1423531 6084371 := bstep (se 1 (by rfl) ⟨4563278, by rfl⟩ : syracuseStep 6084371 = 9126557) B9126557
theorem B2135999 : Blo 1423531 2135999 := bstep (se 1 (by rfl) ⟨1601999, by rfl⟩ : syracuseStep 2135999 = 3203999) B3203999
theorem B2889769 : Blo 1423531 2889769 := bstep (se 2 (by rfl) ⟨1083663, by rfl⟩ : syracuseStep 2889769 = 2167327) B2167327
theorem B1603687 : Blo 1423531 1603687 := bstep (se 1 (by rfl) ⟨1202765, by rfl⟩ : syracuseStep 1603687 = 2405531) B2405531
theorem B25983179 : Blo 1423531 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B1521947 : Blo 1423531 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B1423975 : Blo 1423531 1423975 := bstep (se 1 (by rfl) ⟨1067981, by rfl⟩ : syracuseStep 1423975 = 2135963) B2135963
theorem B1424027 : Blo 1423531 1424027 := bstep (se 1 (by rfl) ⟨1068020, by rfl⟩ : syracuseStep 1424027 = 2136041) B2136041
theorem B1424447 : Blo 1423531 1424447 := bstep (se 1 (by rfl) ⟨1068335, by rfl⟩ : syracuseStep 1424447 = 2136671) B2136671
theorem B46840927 : Blo 1423531 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B2137199 : Blo 1423531 2137199 := bstep (se 1 (by rfl) ⟨1602899, by rfl⟩ : syracuseStep 2137199 = 3205799) B3205799
theorem B1424511 : Blo 1423531 1424511 := bstep (se 1 (by rfl) ⟨1068383, by rfl⟩ : syracuseStep 1424511 = 2136767) B2136767
theorem B1424543 : Blo 1423531 1424543 := bstep (se 1 (by rfl) ⟨1068407, by rfl⟩ : syracuseStep 1424543 = 2136815) B2136815
theorem B1424795 : Blo 1423531 1424795 := bstep (se 1 (by rfl) ⟨1068596, by rfl⟩ : syracuseStep 1424795 = 2137193) B2137193
theorem B77938109 : Blo 1423531 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B2702783 : Blo 1423531 2702783 := bstep (se 1 (by rfl) ⟨2027087, by rfl⟩ : syracuseStep 2702783 = 4054175) B4054175
theorem B2137655 : Blo 1423531 2137655 := bstep (se 1 (by rfl) ⟨1603241, by rfl⟩ : syracuseStep 2137655 = 3206483) B3206483
theorem B1425055 : Blo 1423531 1425055 := bstep (se 1 (by rfl) ⟨1068791, by rfl⟩ : syracuseStep 1425055 = 2137583) B2137583
theorem B3702523 : Blo 1423531 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B4808591 : Blo 1423531 4808591 := bstep (se 1 (by rfl) ⟨3606443, by rfl⟩ : syracuseStep 4808591 = 7212887) B7212887
theorem B4055017 : Blo 1423531 4055017 := bstep (se 2 (by rfl) ⟨1520631, by rfl⟩ : syracuseStep 4055017 = 3041263) B3041263
theorem B2138159 : Blo 1423531 2138159 := bstep (se 1 (by rfl) ⟨1603619, by rfl⟩ : syracuseStep 2138159 = 3207239) B3207239
theorem B2138249 : Blo 1423531 2138249 := bstep (se 2 (by rfl) ⟨801843, by rfl⟩ : syracuseStep 2138249 = 1603687) B1603687
theorem B2138279 : Blo 1423531 2138279 := bstep (se 1 (by rfl) ⟨1603709, by rfl⟩ : syracuseStep 2138279 = 3207419) B3207419
theorem B4055359 : Blo 1423531 4055359 := bstep (se 1 (by rfl) ⟨3041519, by rfl⟩ : syracuseStep 4055359 = 6083039) B6083039
theorem B4055417 : Blo 1423531 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B4056247 : Blo 1423531 4056247 := bstep (se 1 (by rfl) ⟨3042185, by rfl⟩ : syracuseStep 4056247 = 6084371) B6084371
theorem B3851641 : Blo 1423531 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B3606241 : Blo 1423531 3606241 := bstep (se 2 (by rfl) ⟨1352340, by rfl⟩ : syracuseStep 3606241 = 2704681) B2704681
theorem B12338921 : Blo 1423531 12338921 := bstep (se 2 (by rfl) ⟨4627095, by rfl⟩ : syracuseStep 12338921 = 9254191) B9254191
theorem B10815443 : Blo 1423531 10815443 := bstep (se 1 (by rfl) ⟨8111582, by rfl⟩ : syracuseStep 10815443 = 16223165) B16223165
theorem B3205727 : Blo 1423531 3205727 := bstep (se 1 (by rfl) ⟨2404295, by rfl⟩ : syracuseStep 3205727 = 4808591) B4808591
theorem B41093729 : Blo 1423531 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B3853025 : Blo 1423531 3853025 := bstep (se 2 (by rfl) ⟨1444884, by rfl⟩ : syracuseStep 3853025 = 2889769) B2889769
theorem B3607487 : Blo 1423531 3607487 := bstep (se 1 (by rfl) ⟨2705615, by rfl⟩ : syracuseStep 3607487 = 5411231) B5411231
theorem B3206303 : Blo 1423531 3206303 := bstep (se 1 (by rfl) ⟨2404727, by rfl⟩ : syracuseStep 3206303 = 4809455) B4809455
theorem B10267897 : Blo 1423531 10267897 := bstep (se 2 (by rfl) ⟨3850461, by rfl⟩ : syracuseStep 10267897 = 7700923) B7700923
theorem B6843689 : Blo 1423531 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B4058525 : Blo 1423531 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B17322119 : Blo 1423531 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B51958739 : Blo 1423531 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B4936697 : Blo 1423531 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B6501559 : Blo 1423531 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B7214831 : Blo 1423531 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B3422375 : Blo 1423531 3422375 := bstep (se 1 (by rfl) ⟨2566781, by rfl⟩ : syracuseStep 3422375 = 5133563) B5133563
theorem B2136287 : Blo 1423531 2136287 := bstep (se 1 (by rfl) ⟨1602215, by rfl⟩ : syracuseStep 2136287 = 3204431) B3204431
theorem B1423599 : Blo 1423531 1423599 := bstep (se 1 (by rfl) ⟨1067699, by rfl⟩ : syracuseStep 1423599 = 2135399) B2135399
theorem B1423999 : Blo 1423531 1423999 := bstep (se 1 (by rfl) ⟨1067999, by rfl⟩ : syracuseStep 1423999 = 2135999) B2135999
theorem B12991225 : Blo 1423531 12991225 := bstep (se 2 (by rfl) ⟨4871709, by rfl⟩ : syracuseStep 12991225 = 9743419) B9743419
theorem B62454569 : Blo 1423531 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B2137247 : Blo 1423531 2137247 := bstep (se 1 (by rfl) ⟨1602935, by rfl⟩ : syracuseStep 2137247 = 3205871) B3205871
theorem B6167735 : Blo 1423531 6167735 := bstep (se 1 (by rfl) ⟨4625801, by rfl⟩ : syracuseStep 6167735 = 9251603) B9251603
theorem B1424799 : Blo 1423531 1424799 := bstep (se 1 (by rfl) ⟨1068599, by rfl⟩ : syracuseStep 1424799 = 2137199) B2137199
theorem B1801855 : Blo 1423531 1801855 := bstep (se 1 (by rfl) ⟨1351391, by rfl⟩ : syracuseStep 1801855 = 2702783) B2702783
theorem B24354431 : Blo 1423531 24354431 := bstep (se 1 (by rfl) ⟨18265823, by rfl⟩ : syracuseStep 24354431 = 36531647) B36531647
theorem B1425103 : Blo 1423531 1425103 := bstep (se 1 (by rfl) ⟨1068827, by rfl⟩ : syracuseStep 1425103 = 2137655) B2137655
theorem B5406689 : Blo 1423531 5406689 := bstep (se 2 (by rfl) ⟨2027508, by rfl⟩ : syracuseStep 5406689 = 4055017) B4055017
theorem B1425439 : Blo 1423531 1425439 := bstep (se 1 (by rfl) ⟨1069079, by rfl⟩ : syracuseStep 1425439 = 2138159) B2138159
theorem B1425499 : Blo 1423531 1425499 := bstep (se 1 (by rfl) ⟨1069124, by rfl⟩ : syracuseStep 1425499 = 2138249) B2138249
theorem B1425519 : Blo 1423531 1425519 := bstep (se 1 (by rfl) ⟨1069139, by rfl⟩ : syracuseStep 1425519 = 2138279) B2138279
theorem B2703611 : Blo 1423531 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B5407145 : Blo 1423531 5407145 := bstep (se 2 (by rfl) ⟨2027679, by rfl⟩ : syracuseStep 5407145 = 4055359) B4055359
theorem B10822733 : Blo 1423531 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B8225947 : Blo 1423531 8225947 := bstep (se 1 (by rfl) ⟨6169460, by rfl⟩ : syracuseStep 8225947 = 12338921) B12338921
theorem B4809887 : Blo 1423531 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B7210295 : Blo 1423531 7210295 := bstep (se 1 (by rfl) ⟨5407721, by rfl⟩ : syracuseStep 7210295 = 10815443) B10815443
theorem B5408329 : Blo 1423531 5408329 := bstep (se 2 (by rfl) ⟨2028123, by rfl⟩ : syracuseStep 5408329 = 4056247) B4056247
theorem B8668745 : Blo 1423531 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B13690529 : Blo 1423531 13690529 := bstep (se 2 (by rfl) ⟨5133948, by rfl⟩ : syracuseStep 13690529 = 10267897) B10267897
theorem B27395819 : Blo 1423531 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B166545517 : Blo 1423531 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B2402473 : Blo 1423531 2402473 := bstep (se 2 (by rfl) ⟨900927, by rfl⟩ : syracuseStep 2402473 = 1801855) B1801855
theorem B34639159 : Blo 1423531 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B17321633 : Blo 1423531 17321633 := bstep (se 2 (by rfl) ⟨6495612, by rfl⟩ : syracuseStep 17321633 = 12991225) B12991225
theorem B2281583 : Blo 1423531 2281583 := bstep (se 1 (by rfl) ⟨1711187, by rfl⟩ : syracuseStep 2281583 = 3422375) B3422375
theorem B2568683 : Blo 1423531 2568683 := bstep (se 1 (by rfl) ⟨1926512, by rfl⟩ : syracuseStep 2568683 = 3853025) B3853025
theorem B2404991 : Blo 1423531 2404991 := bstep (se 1 (by rfl) ⟨1803743, by rfl⟩ : syracuseStep 2404991 = 3607487) B3607487
theorem B11548079 : Blo 1423531 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B3291131 : Blo 1423531 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B1424191 : Blo 1423531 1424191 := bstep (se 1 (by rfl) ⟨1068143, by rfl⟩ : syracuseStep 1424191 = 2136287) B2136287
theorem B2137151 : Blo 1423531 2137151 := bstep (se 1 (by rfl) ⟨1602863, by rfl⟩ : syracuseStep 2137151 = 3205727) B3205727
theorem B5135521 : Blo 1423531 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B1424831 : Blo 1423531 1424831 := bstep (se 1 (by rfl) ⟨1068623, by rfl⟩ : syracuseStep 1424831 = 2137247) B2137247
theorem B2137535 : Blo 1423531 2137535 := bstep (se 1 (by rfl) ⟨1603151, by rfl⟩ : syracuseStep 2137535 = 3206303) B3206303
theorem B4111823 : Blo 1423531 4111823 := bstep (se 1 (by rfl) ⟨3083867, by rfl⟩ : syracuseStep 4111823 = 6167735) B6167735
theorem B4562459 : Blo 1423531 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B4808321 : Blo 1423531 4808321 := bstep (se 2 (by rfl) ⟨1803120, by rfl⟩ : syracuseStep 4808321 = 3606241) B3606241
theorem B16236287 : Blo 1423531 16236287 := bstep (se 1 (by rfl) ⟨12177215, by rfl⟩ : syracuseStep 16236287 = 24354431) B24354431
theorem B3604459 : Blo 1423531 3604459 := bstep (se 1 (by rfl) ⟨2703344, by rfl⟩ : syracuseStep 3604459 = 5406689) B5406689
theorem B222060689 : Blo 1423531 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B1802407 : Blo 1423531 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B3203297 : Blo 1423531 3203297 := bstep (se 2 (by rfl) ⟨1201236, by rfl⟩ : syracuseStep 3203297 = 2402473) B2402473
theorem B3604763 : Blo 1423531 3604763 := bstep (se 1 (by rfl) ⟨2703572, by rfl⟩ : syracuseStep 3604763 = 5407145) B5407145
theorem B9127019 : Blo 1423531 9127019 := bstep (se 1 (by rfl) ⟨6845264, by rfl⟩ : syracuseStep 9127019 = 13690529) B13690529
theorem B6849821 : Blo 1423531 6849821 := bstep (se 3 (by rfl) ⟨1284341, by rfl⟩ : syracuseStep 6849821 = 2568683) B2568683
theorem B7211105 : Blo 1423531 7211105 := bstep (se 2 (by rfl) ⟨2704164, by rfl⟩ : syracuseStep 7211105 = 5408329) B5408329
theorem B3041639 : Blo 1423531 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B3205547 : Blo 1423531 3205547 := bstep (se 1 (by rfl) ⟨2404160, by rfl⟩ : syracuseStep 3205547 = 4808321) B4808321
theorem B10824191 : Blo 1423531 10824191 := bstep (se 1 (by rfl) ⟨8118143, by rfl⟩ : syracuseStep 10824191 = 16236287) B16236287
theorem B8776349 : Blo 1423531 8776349 := bstep (se 3 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 8776349 = 3291131) B3291131
theorem B3206591 : Blo 1423531 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B5779163 : Blo 1423531 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B18263879 : Blo 1423531 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B2741215 : Blo 1423531 2741215 := bstep (se 1 (by rfl) ⟨2055911, by rfl⟩ : syracuseStep 2741215 = 4111823) B4111823
theorem B11547755 : Blo 1423531 11547755 := bstep (se 1 (by rfl) ⟨8660816, by rfl⟩ : syracuseStep 11547755 = 17321633) B17321633
theorem B4805945 : Blo 1423531 4805945 := bstep (se 2 (by rfl) ⟨1802229, by rfl⟩ : syracuseStep 4805945 = 3604459) B3604459
theorem B1521055 : Blo 1423531 1521055 := bstep (se 1 (by rfl) ⟨1140791, by rfl⟩ : syracuseStep 1521055 = 2281583) B2281583
theorem B1603327 : Blo 1423531 1603327 := bstep (se 1 (by rfl) ⟨1202495, by rfl⟩ : syracuseStep 1603327 = 2404991) B2404991
theorem B7215155 : Blo 1423531 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B4806863 : Blo 1423531 4806863 := bstep (se 1 (by rfl) ⟨3605147, by rfl⟩ : syracuseStep 4806863 = 7210295) B7210295
theorem B7698719 : Blo 1423531 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B10967929 : Blo 1423531 10967929 := bstep (se 2 (by rfl) ⟨4112973, by rfl⟩ : syracuseStep 10967929 = 8225947) B8225947
theorem B6847361 : Blo 1423531 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B46185545 : Blo 1423531 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B1424767 : Blo 1423531 1424767 := bstep (se 1 (by rfl) ⟨1068575, by rfl⟩ : syracuseStep 1424767 = 2137151) B2137151
theorem B1425023 : Blo 1423531 1425023 := bstep (se 1 (by rfl) ⟨1068767, by rfl⟩ : syracuseStep 1425023 = 2137535) B2137535
theorem B3203963 : Blo 1423531 3203963 := bstep (se 1 (by rfl) ⟨2402972, by rfl⟩ : syracuseStep 3203963 = 4805945) B4805945
theorem B3654953 : Blo 1423531 3654953 := bstep (se 2 (by rfl) ⟨1370607, by rfl⟩ : syracuseStep 3654953 = 2741215) B2741215
theorem B4810103 : Blo 1423531 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B3204575 : Blo 1423531 3204575 := bstep (se 1 (by rfl) ⟨2403431, by rfl⟩ : syracuseStep 3204575 = 4806863) B4806863
theorem B5850899 : Blo 1423531 5850899 := bstep (se 1 (by rfl) ⟨4388174, by rfl⟩ : syracuseStep 5850899 = 8776349) B8776349
theorem B4564907 : Blo 1423531 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B3852775 : Blo 1423531 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B12175919 : Blo 1423531 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B148040459 : Blo 1423531 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B2403175 : Blo 1423531 2403175 := bstep (se 1 (by rfl) ⟨1802381, by rfl⟩ : syracuseStep 2403175 = 3604763) B3604763
theorem B2403209 : Blo 1423531 2403209 := bstep (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) B1802407
theorem B4566547 : Blo 1423531 4566547 := bstep (se 1 (by rfl) ⟨3424910, by rfl⟩ : syracuseStep 4566547 = 6849821) B6849821
theorem B5132479 : Blo 1423531 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B2027759 : Blo 1423531 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B2028073 : Blo 1423531 2028073 := bstep (se 2 (by rfl) ⟨760527, by rfl⟩ : syracuseStep 2028073 = 1521055) B1521055
theorem B58495621 : Blo 1423531 58495621 := bstep (se 4 (by rfl) ⟨5483964, by rfl⟩ : syracuseStep 58495621 = 10967929) B10967929
theorem B30790363 : Blo 1423531 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B2135531 : Blo 1423531 2135531 := bstep (se 1 (by rfl) ⟨1601648, by rfl⟩ : syracuseStep 2135531 = 3203297) B3203297
theorem B7698503 : Blo 1423531 7698503 := bstep (se 1 (by rfl) ⟨5773877, by rfl⟩ : syracuseStep 7698503 = 11547755) B11547755
theorem B6084679 : Blo 1423531 6084679 := bstep (se 1 (by rfl) ⟨4563509, by rfl⟩ : syracuseStep 6084679 = 9127019) B9127019
theorem B4807403 : Blo 1423531 4807403 := bstep (se 1 (by rfl) ⟨3605552, by rfl⟩ : syracuseStep 4807403 = 7211105) B7211105
theorem B2137031 : Blo 1423531 2137031 := bstep (se 1 (by rfl) ⟨1602773, by rfl⟩ : syracuseStep 2137031 = 3205547) B3205547
theorem B7216127 : Blo 1423531 7216127 := bstep (se 1 (by rfl) ⟨5412095, by rfl⟩ : syracuseStep 7216127 = 10824191) B10824191
theorem B2137727 : Blo 1423531 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B2137769 : Blo 1423531 2137769 := bstep (se 2 (by rfl) ⟨801663, by rfl⟩ : syracuseStep 2137769 = 1603327) B1603327
theorem B5407357 : Blo 1423531 5407357 := bstep (se 3 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 5407357 = 2027759) B2027759
theorem B5137033 : Blo 1423531 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B2704097 : Blo 1423531 2704097 := bstep (se 2 (by rfl) ⟨1014036, by rfl⟩ : syracuseStep 2704097 = 2028073) B2028073
theorem B3204233 : Blo 1423531 3204233 := bstep (se 2 (by rfl) ⟨1201587, by rfl⟩ : syracuseStep 3204233 = 2403175) B2403175
theorem B3900599 : Blo 1423531 3900599 := bstep (se 1 (by rfl) ⟨2925449, by rfl⟩ : syracuseStep 3900599 = 5850899) B5850899
theorem B3204935 : Blo 1423531 3204935 := bstep (se 1 (by rfl) ⟨2403701, by rfl⟩ : syracuseStep 3204935 = 4807403) B4807403
theorem B4810751 : Blo 1423531 4810751 := bstep (se 1 (by rfl) ⟨3608063, by rfl⟩ : syracuseStep 4810751 = 7216127) B7216127
theorem B6088729 : Blo 1423531 6088729 := bstep (se 2 (by rfl) ⟨2283273, by rfl⟩ : syracuseStep 6088729 = 4566547) B4566547
theorem B8112905 : Blo 1423531 8112905 := bstep (se 2 (by rfl) ⟨3042339, by rfl⟩ : syracuseStep 8112905 = 6084679) B6084679
theorem B6843305 : Blo 1423531 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B2436635 : Blo 1423531 2436635 := bstep (se 1 (by rfl) ⟨1827476, by rfl⟩ : syracuseStep 2436635 = 3654953) B3654953
theorem B3206735 : Blo 1423531 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B41053817 : Blo 1423531 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B3043271 : Blo 1423531 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B5132335 : Blo 1423531 5132335 := bstep (se 1 (by rfl) ⟨3849251, by rfl⟩ : syracuseStep 5132335 = 7698503) B7698503
theorem B98693639 : Blo 1423531 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B1602139 : Blo 1423531 1602139 := bstep (se 1 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 1602139 = 2403209) B2403209
theorem B2135975 : Blo 1423531 2135975 := bstep (se 1 (by rfl) ⟨1601981, by rfl⟩ : syracuseStep 2135975 = 3203963) B3203963
theorem B77994161 : Blo 1423531 77994161 := bstep (se 2 (by rfl) ⟨29247810, by rfl⟩ : syracuseStep 77994161 = 58495621) B58495621
theorem B2136383 : Blo 1423531 2136383 := bstep (se 1 (by rfl) ⟨1602287, by rfl⟩ : syracuseStep 2136383 = 3204575) B3204575
theorem B1423687 : Blo 1423531 1423687 := bstep (se 1 (by rfl) ⟨1067765, by rfl⟩ : syracuseStep 1423687 = 2135531) B2135531
theorem B8117279 : Blo 1423531 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B1424687 : Blo 1423531 1424687 := bstep (se 1 (by rfl) ⟨1068515, by rfl⟩ : syracuseStep 1424687 = 2137031) B2137031
theorem B1425151 : Blo 1423531 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B1425179 : Blo 1423531 1425179 := bstep (se 1 (by rfl) ⟨1068884, by rfl⟩ : syracuseStep 1425179 = 2137769) B2137769
theorem B8118305 : Blo 1423531 8118305 := bstep (se 2 (by rfl) ⟨3044364, by rfl⟩ : syracuseStep 8118305 = 6088729) B6088729
theorem B1802731 : Blo 1423531 1802731 := bstep (se 1 (by rfl) ⟨1352048, by rfl⟩ : syracuseStep 1802731 = 2704097) B2704097
theorem B7209809 : Blo 1423531 7209809 := bstep (se 2 (by rfl) ⟨2703678, by rfl⟩ : syracuseStep 7209809 = 5407357) B5407357
theorem B6849377 : Blo 1423531 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B51996107 : Blo 1423531 51996107 := bstep (se 1 (by rfl) ⟨38997080, by rfl⟩ : syracuseStep 51996107 = 77994161) B77994161
theorem B5408603 : Blo 1423531 5408603 := bstep (se 1 (by rfl) ⟨4056452, by rfl⟩ : syracuseStep 5408603 = 8112905) B8112905
theorem B1624423 : Blo 1423531 1624423 := bstep (se 1 (by rfl) ⟨1218317, by rfl⟩ : syracuseStep 1624423 = 2436635) B2436635
theorem B6843113 : Blo 1423531 6843113 := bstep (se 2 (by rfl) ⟨2566167, by rfl⟩ : syracuseStep 6843113 = 5132335) B5132335
theorem B2600399 : Blo 1423531 2600399 := bstep (se 1 (by rfl) ⟨1950299, by rfl⟩ : syracuseStep 2600399 = 3900599) B3900599
theorem B3207167 : Blo 1423531 3207167 := bstep (se 1 (by rfl) ⟨2405375, by rfl⟩ : syracuseStep 3207167 = 4810751) B4810751
theorem B5411519 : Blo 1423531 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B8115389 : Blo 1423531 8115389 := bstep (se 3 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 8115389 = 3043271) B3043271
theorem B65795759 : Blo 1423531 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B2136155 : Blo 1423531 2136155 := bstep (se 1 (by rfl) ⟨1602116, by rfl⟩ : syracuseStep 2136155 = 3204233) B3204233
theorem B2136185 : Blo 1423531 2136185 := bstep (se 2 (by rfl) ⟨801069, by rfl⟩ : syracuseStep 2136185 = 1602139) B1602139
theorem B2136623 : Blo 1423531 2136623 := bstep (se 1 (by rfl) ⟨1602467, by rfl⟩ : syracuseStep 2136623 = 3204935) B3204935
theorem B1423983 : Blo 1423531 1423983 := bstep (se 1 (by rfl) ⟨1067987, by rfl⟩ : syracuseStep 1423983 = 2135975) B2135975
theorem B1424255 : Blo 1423531 1424255 := bstep (se 1 (by rfl) ⟨1068191, by rfl⟩ : syracuseStep 1424255 = 2136383) B2136383
theorem B4562203 : Blo 1423531 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B2137823 : Blo 1423531 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B27369211 : Blo 1423531 27369211 := bstep (se 1 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 27369211 = 41053817) B41053817
theorem B3605735 : Blo 1423531 3605735 := bstep (se 1 (by rfl) ⟨2704301, by rfl⟩ : syracuseStep 3605735 = 5408603) B5408603
theorem B2138111 : Blo 1423531 2138111 := bstep (se 1 (by rfl) ⟨1603583, by rfl⟩ : syracuseStep 2138111 = 3207167) B3207167
theorem B3607679 : Blo 1423531 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B2165897 : Blo 1423531 2165897 := bstep (se 2 (by rfl) ⟨812211, by rfl⟩ : syracuseStep 2165897 = 1624423) B1624423
theorem B4566251 : Blo 1423531 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B2403641 : Blo 1423531 2403641 := bstep (se 2 (by rfl) ⟨901365, by rfl⟩ : syracuseStep 2403641 = 1802731) B1802731
theorem B5410259 : Blo 1423531 5410259 := bstep (se 1 (by rfl) ⟨4057694, by rfl⟩ : syracuseStep 5410259 = 8115389) B8115389
theorem B34664071 : Blo 1423531 34664071 := bstep (se 1 (by rfl) ⟨25998053, by rfl⟩ : syracuseStep 34664071 = 51996107) B51996107
theorem B43863839 : Blo 1423531 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B6082937 : Blo 1423531 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B1733599 : Blo 1423531 1733599 := bstep (se 1 (by rfl) ⟨1300199, by rfl⟩ : syracuseStep 1733599 = 2600399) B2600399
theorem B36492281 : Blo 1423531 36492281 := bstep (se 2 (by rfl) ⟨13684605, by rfl⟩ : syracuseStep 36492281 = 27369211) B27369211
theorem B5412203 : Blo 1423531 5412203 := bstep (se 1 (by rfl) ⟨4059152, by rfl⟩ : syracuseStep 5412203 = 8118305) B8118305
theorem B4806539 : Blo 1423531 4806539 := bstep (se 1 (by rfl) ⟨3604904, by rfl⟩ : syracuseStep 4806539 = 7209809) B7209809
theorem B1424103 : Blo 1423531 1424103 := bstep (se 1 (by rfl) ⟨1068077, by rfl⟩ : syracuseStep 1424103 = 2136155) B2136155
theorem B1424123 : Blo 1423531 1424123 := bstep (se 1 (by rfl) ⟨1068092, by rfl⟩ : syracuseStep 1424123 = 2136185) B2136185
theorem B1424415 : Blo 1423531 1424415 := bstep (se 1 (by rfl) ⟨1068311, by rfl⟩ : syracuseStep 1424415 = 2136623) B2136623
theorem B4562075 : Blo 1423531 4562075 := bstep (se 1 (by rfl) ⟨3421556, by rfl⟩ : syracuseStep 4562075 = 6843113) B6843113
theorem B1425215 : Blo 1423531 1425215 := bstep (se 1 (by rfl) ⟨1068911, by rfl⟩ : syracuseStep 1425215 = 2137823) B2137823
theorem B4055291 : Blo 1423531 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B5775725 : Blo 1423531 5775725 := bstep (se 3 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 5775725 = 2165897) B2165897
theorem B3204359 : Blo 1423531 3204359 := bstep (se 1 (by rfl) ⟨2403269, by rfl⟩ : syracuseStep 3204359 = 4806539) B4806539
theorem B2311465 : Blo 1423531 2311465 := bstep (se 2 (by rfl) ⟨866799, by rfl⟩ : syracuseStep 2311465 = 1733599) B1733599
theorem B3041383 : Blo 1423531 3041383 := bstep (se 1 (by rfl) ⟨2281037, by rfl⟩ : syracuseStep 3041383 = 4562075) B4562075
theorem B3606839 : Blo 1423531 3606839 := bstep (se 1 (by rfl) ⟨2705129, by rfl⟩ : syracuseStep 3606839 = 5410259) B5410259
theorem B12176669 : Blo 1423531 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B2403823 : Blo 1423531 2403823 := bstep (se 1 (by rfl) ⟨1802867, by rfl⟩ : syracuseStep 2403823 = 3605735) B3605735
theorem B3608135 : Blo 1423531 3608135 := bstep (se 1 (by rfl) ⟨2706101, by rfl⟩ : syracuseStep 3608135 = 5412203) B5412203
theorem B2405119 : Blo 1423531 2405119 := bstep (se 1 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 2405119 = 3607679) B3607679
theorem B1602427 : Blo 1423531 1602427 := bstep (se 1 (by rfl) ⟨1201820, by rfl⟩ : syracuseStep 1602427 = 2403641) B2403641
theorem B29242559 : Blo 1423531 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B24328187 : Blo 1423531 24328187 := bstep (se 1 (by rfl) ⟨18246140, by rfl⟩ : syracuseStep 24328187 = 36492281) B36492281
theorem B46218761 : Blo 1423531 46218761 := bstep (se 2 (by rfl) ⟨17332035, by rfl⟩ : syracuseStep 46218761 = 34664071) B34664071
theorem B1425407 : Blo 1423531 1425407 := bstep (se 1 (by rfl) ⟨1069055, by rfl⟩ : syracuseStep 1425407 = 2138111) B2138111
theorem B4055177 : Blo 1423531 4055177 := bstep (se 2 (by rfl) ⟨1520691, by rfl⟩ : syracuseStep 4055177 = 3041383) B3041383
theorem B2703527 : Blo 1423531 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B15401933 : Blo 1423531 15401933 := bstep (se 3 (by rfl) ⟨2887862, by rfl⟩ : syracuseStep 15401933 = 5775725) B5775725
theorem B3081953 : Blo 1423531 3081953 := bstep (se 2 (by rfl) ⟨1155732, by rfl⟩ : syracuseStep 3081953 = 2311465) B2311465
theorem B3205097 : Blo 1423531 3205097 := bstep (se 2 (by rfl) ⟨1201911, by rfl⟩ : syracuseStep 3205097 = 2403823) B2403823
theorem B30812507 : Blo 1423531 30812507 := bstep (se 1 (by rfl) ⟨23109380, by rfl⟩ : syracuseStep 30812507 = 46218761) B46218761
theorem B3206825 : Blo 1423531 3206825 := bstep (se 2 (by rfl) ⟨1202559, by rfl⟩ : syracuseStep 3206825 = 2405119) B2405119
theorem B2404559 : Blo 1423531 2404559 := bstep (se 1 (by rfl) ⟨1803419, by rfl⟩ : syracuseStep 2404559 = 3606839) B3606839
theorem B2405423 : Blo 1423531 2405423 := bstep (se 1 (by rfl) ⟨1804067, by rfl⟩ : syracuseStep 2405423 = 3608135) B3608135
theorem B19495039 : Blo 1423531 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B2136239 : Blo 1423531 2136239 := bstep (se 1 (by rfl) ⟨1602179, by rfl⟩ : syracuseStep 2136239 = 3204359) B3204359
theorem B2136569 : Blo 1423531 2136569 := bstep (se 2 (by rfl) ⟨801213, by rfl⟩ : syracuseStep 2136569 = 1602427) B1602427
theorem B16218791 : Blo 1423531 16218791 := bstep (se 1 (by rfl) ⟨12164093, by rfl⟩ : syracuseStep 16218791 = 24328187) B24328187
theorem B8117779 : Blo 1423531 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B2703451 : Blo 1423531 2703451 := bstep (se 1 (by rfl) ⟨2027588, by rfl⟩ : syracuseStep 2703451 = 4055177) B4055177
theorem B1802351 : Blo 1423531 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B25993385 : Blo 1423531 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B8218541 : Blo 1423531 8218541 := bstep (se 3 (by rfl) ⟨1540976, by rfl⟩ : syracuseStep 8218541 = 3081953) B3081953
theorem B10823705 : Blo 1423531 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B10267955 : Blo 1423531 10267955 := bstep (se 1 (by rfl) ⟨7700966, by rfl⟩ : syracuseStep 10267955 = 15401933) B15401933
theorem B20541671 : Blo 1423531 20541671 := bstep (se 1 (by rfl) ⟨15406253, by rfl⟩ : syracuseStep 20541671 = 30812507) B30812507
theorem B1603039 : Blo 1423531 1603039 := bstep (se 1 (by rfl) ⟨1202279, by rfl⟩ : syracuseStep 1603039 = 2404559) B2404559
theorem B1603615 : Blo 1423531 1603615 := bstep (se 1 (by rfl) ⟨1202711, by rfl⟩ : syracuseStep 1603615 = 2405423) B2405423
theorem B2136731 : Blo 1423531 2136731 := bstep (se 1 (by rfl) ⟨1602548, by rfl⟩ : syracuseStep 2136731 = 3205097) B3205097
theorem B1424159 : Blo 1423531 1424159 := bstep (se 1 (by rfl) ⟨1068119, by rfl⟩ : syracuseStep 1424159 = 2136239) B2136239
theorem B1424379 : Blo 1423531 1424379 := bstep (se 1 (by rfl) ⟨1068284, by rfl⟩ : syracuseStep 1424379 = 2136569) B2136569
theorem B10812527 : Blo 1423531 10812527 := bstep (se 1 (by rfl) ⟨8109395, by rfl⟩ : syracuseStep 10812527 = 16218791) B16218791
theorem B2137883 : Blo 1423531 2137883 := bstep (se 1 (by rfl) ⟨1603412, by rfl⟩ : syracuseStep 2137883 = 3206825) B3206825
theorem B2138153 : Blo 1423531 2138153 := bstep (se 2 (by rfl) ⟨801807, by rfl⟩ : syracuseStep 2138153 = 1603615) B1603615
theorem B3604601 : Blo 1423531 3604601 := bstep (se 2 (by rfl) ⟨1351725, by rfl⟩ : syracuseStep 3604601 = 2703451) B2703451
theorem B21916109 : Blo 1423531 21916109 := bstep (se 3 (by rfl) ⟨4109270, by rfl⟩ : syracuseStep 21916109 = 8218541) B8218541
theorem B17328923 : Blo 1423531 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B6845303 : Blo 1423531 6845303 := bstep (se 1 (by rfl) ⟨5133977, by rfl⟩ : syracuseStep 6845303 = 10267955) B10267955
theorem B13694447 : Blo 1423531 13694447 := bstep (se 1 (by rfl) ⟨10270835, by rfl⟩ : syracuseStep 13694447 = 20541671) B20541671
theorem B4806269 : Blo 1423531 4806269 := bstep (se 3 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 4806269 = 1802351) B1802351
theorem B7215803 : Blo 1423531 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B1424487 : Blo 1423531 1424487 := bstep (se 1 (by rfl) ⟨1068365, by rfl⟩ : syracuseStep 1424487 = 2136731) B2136731
theorem B2137385 : Blo 1423531 2137385 := bstep (se 2 (by rfl) ⟨801519, by rfl⟩ : syracuseStep 2137385 = 1603039) B1603039
theorem B7208351 : Blo 1423531 7208351 := bstep (se 1 (by rfl) ⟨5406263, by rfl⟩ : syracuseStep 7208351 = 10812527) B10812527
theorem B1425255 : Blo 1423531 1425255 := bstep (se 1 (by rfl) ⟨1068941, by rfl⟩ : syracuseStep 1425255 = 2137883) B2137883
theorem B1425435 : Blo 1423531 1425435 := bstep (se 1 (by rfl) ⟨1069076, by rfl⟩ : syracuseStep 1425435 = 2138153) B2138153
theorem B4563535 : Blo 1423531 4563535 := bstep (se 1 (by rfl) ⟨3422651, by rfl⟩ : syracuseStep 4563535 = 6845303) B6845303
theorem B3204179 : Blo 1423531 3204179 := bstep (se 1 (by rfl) ⟨2403134, by rfl⟩ : syracuseStep 3204179 = 4806269) B4806269
theorem B4810535 : Blo 1423531 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B11552615 : Blo 1423531 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B2403067 : Blo 1423531 2403067 := bstep (se 1 (by rfl) ⟨1802300, by rfl⟩ : syracuseStep 2403067 = 3604601) B3604601
theorem B14610739 : Blo 1423531 14610739 := bstep (se 1 (by rfl) ⟨10958054, by rfl⟩ : syracuseStep 14610739 = 21916109) B21916109
theorem B4805567 : Blo 1423531 4805567 := bstep (se 1 (by rfl) ⟨3604175, by rfl⟩ : syracuseStep 4805567 = 7208351) B7208351
theorem B36518525 : Blo 1423531 36518525 := bstep (se 3 (by rfl) ⟨6847223, by rfl⟩ : syracuseStep 36518525 = 13694447) B13694447
theorem B1424923 : Blo 1423531 1424923 := bstep (se 1 (by rfl) ⟨1068692, by rfl⟩ : syracuseStep 1424923 = 2137385) B2137385
theorem B19480985 : Blo 1423531 19480985 := bstep (se 2 (by rfl) ⟨7305369, by rfl⟩ : syracuseStep 19480985 = 14610739) B14610739
theorem B3203711 : Blo 1423531 3203711 := bstep (se 1 (by rfl) ⟨2402783, by rfl⟩ : syracuseStep 3203711 = 4805567) B4805567
theorem B3204089 : Blo 1423531 3204089 := bstep (se 2 (by rfl) ⟨1201533, by rfl⟩ : syracuseStep 3204089 = 2403067) B2403067
theorem B7701743 : Blo 1423531 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B3207023 : Blo 1423531 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B2136119 : Blo 1423531 2136119 := bstep (se 1 (by rfl) ⟨1602089, by rfl⟩ : syracuseStep 2136119 = 3204179) B3204179
theorem B6084713 : Blo 1423531 6084713 := bstep (se 2 (by rfl) ⟨2281767, by rfl⟩ : syracuseStep 6084713 = 4563535) B4563535
theorem B24345683 : Blo 1423531 24345683 := bstep (se 1 (by rfl) ⟨18259262, by rfl⟩ : syracuseStep 24345683 = 36518525) B36518525
theorem B20537981 : Blo 1423531 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B4056475 : Blo 1423531 4056475 := bstep (se 1 (by rfl) ⟨3042356, by rfl⟩ : syracuseStep 4056475 = 6084713) B6084713
theorem B16230455 : Blo 1423531 16230455 := bstep (se 1 (by rfl) ⟨12172841, by rfl⟩ : syracuseStep 16230455 = 24345683) B24345683
theorem B12987323 : Blo 1423531 12987323 := bstep (se 1 (by rfl) ⟨9740492, by rfl⟩ : syracuseStep 12987323 = 19480985) B19480985
theorem B2135807 : Blo 1423531 2135807 := bstep (se 1 (by rfl) ⟨1601855, by rfl⟩ : syracuseStep 2135807 = 3203711) B3203711
theorem B2136059 : Blo 1423531 2136059 := bstep (se 1 (by rfl) ⟨1602044, by rfl⟩ : syracuseStep 2136059 = 3204089) B3204089
theorem B1424079 : Blo 1423531 1424079 := bstep (se 1 (by rfl) ⟨1068059, by rfl⟩ : syracuseStep 1424079 = 2136119) B2136119
theorem B2138015 : Blo 1423531 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B5408633 : Blo 1423531 5408633 := bstep (se 2 (by rfl) ⟨2028237, by rfl⟩ : syracuseStep 5408633 = 4056475) B4056475
theorem B13691987 : Blo 1423531 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B1423871 : Blo 1423531 1423871 := bstep (se 1 (by rfl) ⟨1067903, by rfl⟩ : syracuseStep 1423871 = 2135807) B2135807
theorem B1424039 : Blo 1423531 1424039 := bstep (se 1 (by rfl) ⟨1068029, by rfl⟩ : syracuseStep 1424039 = 2136059) B2136059
theorem B10820303 : Blo 1423531 10820303 := bstep (se 1 (by rfl) ⟨8115227, by rfl⟩ : syracuseStep 10820303 = 16230455) B16230455
theorem B8658215 : Blo 1423531 8658215 := bstep (se 1 (by rfl) ⟨6493661, by rfl⟩ : syracuseStep 8658215 = 12987323) B12987323
theorem B1425343 : Blo 1423531 1425343 := bstep (se 1 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 1425343 = 2138015) B2138015
theorem B3605755 : Blo 1423531 3605755 := bstep (se 1 (by rfl) ⟨2704316, by rfl⟩ : syracuseStep 3605755 = 5408633) B5408633
theorem B9127991 : Blo 1423531 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B7213535 : Blo 1423531 7213535 := bstep (se 1 (by rfl) ⟨5410151, by rfl⟩ : syracuseStep 7213535 = 10820303) B10820303
theorem B5772143 : Blo 1423531 5772143 := bstep (se 1 (by rfl) ⟨4329107, by rfl⟩ : syracuseStep 5772143 = 8658215) B8658215
theorem B4809023 : Blo 1423531 4809023 := bstep (se 1 (by rfl) ⟨3606767, by rfl⟩ : syracuseStep 4809023 = 7213535) B7213535
theorem B24341309 : Blo 1423531 24341309 := bstep (se 3 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 24341309 = 9127991) B9127991
theorem B3848095 : Blo 1423531 3848095 := bstep (se 1 (by rfl) ⟨2886071, by rfl⟩ : syracuseStep 3848095 = 5772143) B5772143
theorem B4807673 : Blo 1423531 4807673 := bstep (se 2 (by rfl) ⟨1802877, by rfl⟩ : syracuseStep 4807673 = 3605755) B3605755
theorem B3205115 : Blo 1423531 3205115 := bstep (se 1 (by rfl) ⟨2403836, by rfl⟩ : syracuseStep 3205115 = 4807673) B4807673
theorem B5130793 : Blo 1423531 5130793 := bstep (se 2 (by rfl) ⟨1924047, by rfl⟩ : syracuseStep 5130793 = 3848095) B3848095
theorem B3206015 : Blo 1423531 3206015 := bstep (se 1 (by rfl) ⟨2404511, by rfl⟩ : syracuseStep 3206015 = 4809023) B4809023
theorem B16227539 : Blo 1423531 16227539 := bstep (se 1 (by rfl) ⟨12170654, by rfl⟩ : syracuseStep 16227539 = 24341309) B24341309
theorem B6841057 : Blo 1423531 6841057 := bstep (se 2 (by rfl) ⟨2565396, by rfl⟩ : syracuseStep 6841057 = 5130793) B5130793
theorem B10818359 : Blo 1423531 10818359 := bstep (se 1 (by rfl) ⟨8113769, by rfl⟩ : syracuseStep 10818359 = 16227539) B16227539
theorem B2136743 : Blo 1423531 2136743 := bstep (se 1 (by rfl) ⟨1602557, by rfl⟩ : syracuseStep 2136743 = 3205115) B3205115
theorem B2137343 : Blo 1423531 2137343 := bstep (se 1 (by rfl) ⟨1603007, by rfl⟩ : syracuseStep 2137343 = 3206015) B3206015
theorem B7212239 : Blo 1423531 7212239 := bstep (se 1 (by rfl) ⟨5409179, by rfl⟩ : syracuseStep 7212239 = 10818359) B10818359
theorem B9121409 : Blo 1423531 9121409 := bstep (se 2 (by rfl) ⟨3420528, by rfl⟩ : syracuseStep 9121409 = 6841057) B6841057
theorem B1424495 : Blo 1423531 1424495 := bstep (se 1 (by rfl) ⟨1068371, by rfl⟩ : syracuseStep 1424495 = 2136743) B2136743
theorem B1424895 : Blo 1423531 1424895 := bstep (se 1 (by rfl) ⟨1068671, by rfl⟩ : syracuseStep 1424895 = 2137343) B2137343
theorem B6080939 : Blo 1423531 6080939 := bstep (se 1 (by rfl) ⟨4560704, by rfl⟩ : syracuseStep 6080939 = 9121409) B9121409
theorem B4808159 : Blo 1423531 4808159 := bstep (se 1 (by rfl) ⟨3606119, by rfl⟩ : syracuseStep 4808159 = 7212239) B7212239
theorem B3205439 : Blo 1423531 3205439 := bstep (se 1 (by rfl) ⟨2404079, by rfl⟩ : syracuseStep 3205439 = 4808159) B4808159
theorem B4053959 : Blo 1423531 4053959 := bstep (se 1 (by rfl) ⟨3040469, by rfl⟩ : syracuseStep 4053959 = 6080939) B6080939
theorem B2136959 : Blo 1423531 2136959 := bstep (se 1 (by rfl) ⟨1602719, by rfl⟩ : syracuseStep 2136959 = 3205439) B3205439
theorem B2702639 : Blo 1423531 2702639 := bstep (se 1 (by rfl) ⟨2026979, by rfl⟩ : syracuseStep 2702639 = 4053959) B4053959
theorem B1424639 : Blo 1423531 1424639 := bstep (se 1 (by rfl) ⟨1068479, by rfl⟩ : syracuseStep 1424639 = 2136959) B2136959
theorem B1801759 : Blo 1423531 1801759 := bstep (se 1 (by rfl) ⟨1351319, by rfl⟩ : syracuseStep 1801759 = 2702639) B2702639
theorem B2402345 : Blo 1423531 2402345 := bstep (se 2 (by rfl) ⟨900879, by rfl⟩ : syracuseStep 2402345 = 1801759) B1801759
theorem B1601563 : Blo 1423531 1601563 := bstep (se 1 (by rfl) ⟨1201172, by rfl⟩ : syracuseStep 1601563 = 2402345) B2402345
theorem B2135417 : Blo 1423531 2135417 := bstep (se 2 (by rfl) ⟨800781, by rfl⟩ : syracuseStep 2135417 = 1601563) B1601563
theorem B1423611 : Blo 1423531 1423611 := bstep (se 1 (by rfl) ⟨1067708, by rfl⟩ : syracuseStep 1423611 = 2135417) B2135417

theorem C0 (j : ℕ) (h1 : 355882 ≤ j) (h2 : j ≤ 356382) : Blo 1423531 (4 * j + 3) := by
  interval_cases j
  · exact B1423531
  · exact B1423535
  · exact B1423539
  · exact B1423543
  · exact B1423547
  · exact B1423551
  · exact B1423555
  · exact B1423559
  · exact B1423563
  · exact B1423567
  · exact B1423571
  · exact B1423575
  · exact B1423579
  · exact B1423583
  · exact B1423587
  · exact B1423591
  · exact B1423595
  · exact B1423599
  · exact B1423603
  · exact B1423607
  · exact B1423611
  · exact B1423615
  · exact B1423619
  · exact B1423623
  · exact B1423627
  · exact B1423631
  · exact B1423635
  · exact B1423639
  · exact B1423643
  · exact B1423647
  · exact B1423651
  · exact B1423655
  · exact B1423659
  · exact B1423663
  · exact B1423667
  · exact B1423671
  · exact B1423675
  · exact B1423679
  · exact B1423683
  · exact B1423687
  · exact B1423691
  · exact B1423695
  · exact B1423699
  · exact B1423703
  · exact B1423707
  · exact B1423711
  · exact B1423715
  · exact B1423719
  · exact B1423723
  · exact B1423727
  · exact B1423731
  · exact B1423735
  · exact B1423739
  · exact B1423743
  · exact B1423747
  · exact B1423751
  · exact B1423755
  · exact B1423759
  · exact B1423763
  · exact B1423767
  · exact B1423771
  · exact B1423775
  · exact B1423779
  · exact B1423783
  · exact B1423787
  · exact B1423791
  · exact B1423795
  · exact B1423799
  · exact B1423803
  · exact B1423807
  · exact B1423811
  · exact B1423815
  · exact B1423819
  · exact B1423823
  · exact B1423827
  · exact B1423831
  · exact B1423835
  · exact B1423839
  · exact B1423843
  · exact B1423847
  · exact B1423851
  · exact B1423855
  · exact B1423859
  · exact B1423863
  · exact B1423867
  · exact B1423871
  · exact B1423875
  · exact B1423879
  · exact B1423883
  · exact B1423887
  · exact B1423891
  · exact B1423895
  · exact B1423899
  · exact B1423903
  · exact B1423907
  · exact B1423911
  · exact B1423915
  · exact B1423919
  · exact B1423923
  · exact B1423927
  · exact B1423931
  · exact B1423935
  · exact B1423939
  · exact B1423943
  · exact B1423947
  · exact B1423951
  · exact B1423955
  · exact B1423959
  · exact B1423963
  · exact B1423967
  · exact B1423971
  · exact B1423975
  · exact B1423979
  · exact B1423983
  · exact B1423987
  · exact B1423991
  · exact B1423995
  · exact B1423999
  · exact B1424003
  · exact B1424007
  · exact B1424011
  · exact B1424015
  · exact B1424019
  · exact B1424023
  · exact B1424027
  · exact B1424031
  · exact B1424035
  · exact B1424039
  · exact B1424043
  · exact B1424047
  · exact B1424051
  · exact B1424055
  · exact B1424059
  · exact B1424063
  · exact B1424067
  · exact B1424071
  · exact B1424075
  · exact B1424079
  · exact B1424083
  · exact B1424087
  · exact B1424091
  · exact B1424095
  · exact B1424099
  · exact B1424103
  · exact B1424107
  · exact B1424111
  · exact B1424115
  · exact B1424119
  · exact B1424123
  · exact B1424127
  · exact B1424131
  · exact B1424135
  · exact B1424139
  · exact B1424143
  · exact B1424147
  · exact B1424151
  · exact B1424155
  · exact B1424159
  · exact B1424163
  · exact B1424167
  · exact B1424171
  · exact B1424175
  · exact B1424179
  · exact B1424183
  · exact B1424187
  · exact B1424191
  · exact B1424195
  · exact B1424199
  · exact B1424203
  · exact B1424207
  · exact B1424211
  · exact B1424215
  · exact B1424219
  · exact B1424223
  · exact B1424227
  · exact B1424231
  · exact B1424235
  · exact B1424239
  · exact B1424243
  · exact B1424247
  · exact B1424251
  · exact B1424255
  · exact B1424259
  · exact B1424263
  · exact B1424267
  · exact B1424271
  · exact B1424275
  · exact B1424279
  · exact B1424283
  · exact B1424287
  · exact B1424291
  · exact B1424295
  · exact B1424299
  · exact B1424303
  · exact B1424307
  · exact B1424311
  · exact B1424315
  · exact B1424319
  · exact B1424323
  · exact B1424327
  · exact B1424331
  · exact B1424335
  · exact B1424339
  · exact B1424343
  · exact B1424347
  · exact B1424351
  · exact B1424355
  · exact B1424359
  · exact B1424363
  · exact B1424367
  · exact B1424371
  · exact B1424375
  · exact B1424379
  · exact B1424383
  · exact B1424387
  · exact B1424391
  · exact B1424395
  · exact B1424399
  · exact B1424403
  · exact B1424407
  · exact B1424411
  · exact B1424415
  · exact B1424419
  · exact B1424423
  · exact B1424427
  · exact B1424431
  · exact B1424435
  · exact B1424439
  · exact B1424443
  · exact B1424447
  · exact B1424451
  · exact B1424455
  · exact B1424459
  · exact B1424463
  · exact B1424467
  · exact B1424471
  · exact B1424475
  · exact B1424479
  · exact B1424483
  · exact B1424487
  · exact B1424491
  · exact B1424495
  · exact B1424499
  · exact B1424503
  · exact B1424507
  · exact B1424511
  · exact B1424515
  · exact B1424519
  · exact B1424523
  · exact B1424527
  · exact B1424531
  · exact B1424535
  · exact B1424539
  · exact B1424543
  · exact B1424547
  · exact B1424551
  · exact B1424555
  · exact B1424559
  · exact B1424563
  · exact B1424567
  · exact B1424571
  · exact B1424575
  · exact B1424579
  · exact B1424583
  · exact B1424587
  · exact B1424591
  · exact B1424595
  · exact B1424599
  · exact B1424603
  · exact B1424607
  · exact B1424611
  · exact B1424615
  · exact B1424619
  · exact B1424623
  · exact B1424627
  · exact B1424631
  · exact B1424635
  · exact B1424639
  · exact B1424643
  · exact B1424647
  · exact B1424651
  · exact B1424655
  · exact B1424659
  · exact B1424663
  · exact B1424667
  · exact B1424671
  · exact B1424675
  · exact B1424679
  · exact B1424683
  · exact B1424687
  · exact B1424691
  · exact B1424695
  · exact B1424699
  · exact B1424703
  · exact B1424707
  · exact B1424711
  · exact B1424715
  · exact B1424719
  · exact B1424723
  · exact B1424727
  · exact B1424731
  · exact B1424735
  · exact B1424739
  · exact B1424743
  · exact B1424747
  · exact B1424751
  · exact B1424755
  · exact B1424759
  · exact B1424763
  · exact B1424767
  · exact B1424771
  · exact B1424775
  · exact B1424779
  · exact B1424783
  · exact B1424787
  · exact B1424791
  · exact B1424795
  · exact B1424799
  · exact B1424803
  · exact B1424807
  · exact B1424811
  · exact B1424815
  · exact B1424819
  · exact B1424823
  · exact B1424827
  · exact B1424831
  · exact B1424835
  · exact B1424839
  · exact B1424843
  · exact B1424847
  · exact B1424851
  · exact B1424855
  · exact B1424859
  · exact B1424863
  · exact B1424867
  · exact B1424871
  · exact B1424875
  · exact B1424879
  · exact B1424883
  · exact B1424887
  · exact B1424891
  · exact B1424895
  · exact B1424899
  · exact B1424903
  · exact B1424907
  · exact B1424911
  · exact B1424915
  · exact B1424919
  · exact B1424923
  · exact B1424927
  · exact B1424931
  · exact B1424935
  · exact B1424939
  · exact B1424943
  · exact B1424947
  · exact B1424951
  · exact B1424955
  · exact B1424959
  · exact B1424963
  · exact B1424967
  · exact B1424971
  · exact B1424975
  · exact B1424979
  · exact B1424983
  · exact B1424987
  · exact B1424991
  · exact B1424995
  · exact B1424999
  · exact B1425003
  · exact B1425007
  · exact B1425011
  · exact B1425015
  · exact B1425019
  · exact B1425023
  · exact B1425027
  · exact B1425031
  · exact B1425035
  · exact B1425039
  · exact B1425043
  · exact B1425047
  · exact B1425051
  · exact B1425055
  · exact B1425059
  · exact B1425063
  · exact B1425067
  · exact B1425071
  · exact B1425075
  · exact B1425079
  · exact B1425083
  · exact B1425087
  · exact B1425091
  · exact B1425095
  · exact B1425099
  · exact B1425103
  · exact B1425107
  · exact B1425111
  · exact B1425115
  · exact B1425119
  · exact B1425123
  · exact B1425127
  · exact B1425131
  · exact B1425135
  · exact B1425139
  · exact B1425143
  · exact B1425147
  · exact B1425151
  · exact B1425155
  · exact B1425159
  · exact B1425163
  · exact B1425167
  · exact B1425171
  · exact B1425175
  · exact B1425179
  · exact B1425183
  · exact B1425187
  · exact B1425191
  · exact B1425195
  · exact B1425199
  · exact B1425203
  · exact B1425207
  · exact B1425211
  · exact B1425215
  · exact B1425219
  · exact B1425223
  · exact B1425227
  · exact B1425231
  · exact B1425235
  · exact B1425239
  · exact B1425243
  · exact B1425247
  · exact B1425251
  · exact B1425255
  · exact B1425259
  · exact B1425263
  · exact B1425267
  · exact B1425271
  · exact B1425275
  · exact B1425279
  · exact B1425283
  · exact B1425287
  · exact B1425291
  · exact B1425295
  · exact B1425299
  · exact B1425303
  · exact B1425307
  · exact B1425311
  · exact B1425315
  · exact B1425319
  · exact B1425323
  · exact B1425327
  · exact B1425331
  · exact B1425335
  · exact B1425339
  · exact B1425343
  · exact B1425347
  · exact B1425351
  · exact B1425355
  · exact B1425359
  · exact B1425363
  · exact B1425367
  · exact B1425371
  · exact B1425375
  · exact B1425379
  · exact B1425383
  · exact B1425387
  · exact B1425391
  · exact B1425395
  · exact B1425399
  · exact B1425403
  · exact B1425407
  · exact B1425411
  · exact B1425415
  · exact B1425419
  · exact B1425423
  · exact B1425427
  · exact B1425431
  · exact B1425435
  · exact B1425439
  · exact B1425443
  · exact B1425447
  · exact B1425451
  · exact B1425455
  · exact B1425459
  · exact B1425463
  · exact B1425467
  · exact B1425471
  · exact B1425475
  · exact B1425479
  · exact B1425483
  · exact B1425487
  · exact B1425491
  · exact B1425495
  · exact B1425499
  · exact B1425503
  · exact B1425507
  · exact B1425511
  · exact B1425515
  · exact B1425519
  · exact B1425523
  · exact B1425527
  · exact B1425531

theorem solution (m : ℕ) (hlo : 1423531 ≤ m) (hhi : m ≤ 1425531) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 355882 ≤ j := by omega
    have hj2 : j ≤ 356382 := by omega
    have hb : Blo 1423531 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
