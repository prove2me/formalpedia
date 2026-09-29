-- Prove2me | solution 1 for syracuse_descends_range_1547471_1549471
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:31.73423+00:00
-- url     : https://prove2.me/submissions/c42ad813-e72b-48e0-ad37-1a87da76611d

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


theorem B2613269 : Blo 1547471 2613269 := bbase (se 6 (by rfl) ⟨61248, by rfl⟩ : syracuseStep 2613269 = 122497) (by norm_num)
theorem B2203733 : Blo 1547471 2203733 := bbase (se 8 (by rfl) ⟨12912, by rfl⟩ : syracuseStep 2203733 = 25825) (by norm_num)
theorem B1859717 : Blo 1547471 1859717 := bbase (se 4 (by rfl) ⟨174348, by rfl⟩ : syracuseStep 1859717 = 348697) (by norm_num)
theorem B9412757 : Blo 1547471 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B2613397 : Blo 1547471 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B2515117 : Blo 1547471 2515117 := bbase (se 3 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 2515117 = 943169) (by norm_num)
theorem B3481829 : Blo 1547471 3481829 := bbase (se 4 (by rfl) ⟨326421, by rfl⟩ : syracuseStep 3481829 = 652843) (by norm_num)
theorem B2613485 : Blo 1547471 2613485 := bbase (se 3 (by rfl) ⟨490028, by rfl⟩ : syracuseStep 2613485 = 980057) (by norm_num)
theorem B7839989 : Blo 1547471 7839989 := bbase (se 5 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 7839989 = 734999) (by norm_num)
theorem B2941181 : Blo 1547471 2941181 := bbase (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) (by norm_num)
theorem B3350813 : Blo 1547471 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B3481901 : Blo 1547471 3481901 := bbase (se 3 (by rfl) ⟨652856, by rfl⟩ : syracuseStep 3481901 = 1305713) (by norm_num)
theorem B5882165 : Blo 1547471 5882165 := bbase (se 5 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 5882165 = 551453) (by norm_num)
theorem B2515261 : Blo 1547471 2515261 := bbase (se 3 (by rfl) ⟨471611, by rfl⟩ : syracuseStep 2515261 = 943223) (by norm_num)
theorem B5226821 : Blo 1547471 5226821 := bbase (se 4 (by rfl) ⟨490014, by rfl⟩ : syracuseStep 5226821 = 980029) (by norm_num)
theorem B2613613 : Blo 1547471 2613613 := bbase (se 3 (by rfl) ⟨490052, by rfl⟩ : syracuseStep 2613613 = 980105) (by norm_num)
theorem B3481973 : Blo 1547471 3481973 := bbase (se 5 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 3481973 = 326435) (by norm_num)
theorem B1860025 : Blo 1547471 1860025 := bbase (se 2 (by rfl) ⟨697509, by rfl⟩ : syracuseStep 1860025 = 1395019) (by norm_num)
theorem B3482045 : Blo 1547471 3482045 := bbase (se 3 (by rfl) ⟨652883, by rfl⟩ : syracuseStep 3482045 = 1305767) (by norm_num)
theorem B2613701 : Blo 1547471 2613701 := bbase (se 4 (by rfl) ⟨245034, by rfl⟩ : syracuseStep 2613701 = 490069) (by norm_num)
theorem B4407797 : Blo 1547471 4407797 := bbase (se 5 (by rfl) ⟨206615, by rfl⟩ : syracuseStep 4407797 = 413231) (by norm_num)
theorem B4186613 : Blo 1547471 4186613 := bbase (se 5 (by rfl) ⟨196247, by rfl⟩ : syracuseStep 4186613 = 392495) (by norm_num)
theorem B3482117 : Blo 1547471 3482117 := bbase (se 4 (by rfl) ⟨326448, by rfl⟩ : syracuseStep 3482117 = 652897) (by norm_num)
theorem B1860121 : Blo 1547471 1860121 := bbase (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) (by norm_num)
theorem B2613829 : Blo 1547471 2613829 := bbase (se 4 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 2613829 = 490093) (by norm_num)
theorem B1860169 : Blo 1547471 1860169 := bbase (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) (by norm_num)
theorem B3482189 : Blo 1547471 3482189 := bbase (se 3 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 3482189 = 1305821) (by norm_num)
theorem B5882453 : Blo 1547471 5882453 := bbase (se 8 (by rfl) ⟨34467, by rfl⟩ : syracuseStep 5882453 = 68935) (by norm_num)
theorem B3482261 : Blo 1547471 3482261 := bbase (se 6 (by rfl) ⟨81615, by rfl⟩ : syracuseStep 3482261 = 163231) (by norm_num)
theorem B4711061 : Blo 1547471 4711061 := bbase (se 6 (by rfl) ⟨110415, by rfl⟩ : syracuseStep 4711061 = 220831) (by norm_num)
theorem B2613917 : Blo 1547471 2613917 := bbase (se 3 (by rfl) ⟨490109, by rfl⟩ : syracuseStep 2613917 = 980219) (by norm_num)
theorem B3482333 : Blo 1547471 3482333 := bbase (se 3 (by rfl) ⟨652937, by rfl⟩ : syracuseStep 3482333 = 1305875) (by norm_num)
theorem B5227253 : Blo 1547471 5227253 := bbase (se 5 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 5227253 = 490055) (by norm_num)
theorem B16745237 : Blo 1547471 16745237 := bbase (se 6 (by rfl) ⟨392466, by rfl⟩ : syracuseStep 16745237 = 784933) (by norm_num)
theorem B1958681 : Blo 1547471 1958681 := bbase (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) (by norm_num)
theorem B2614045 : Blo 1547471 2614045 := bbase (se 3 (by rfl) ⟨490133, by rfl⟩ : syracuseStep 2614045 = 980267) (by norm_num)
theorem B3482405 : Blo 1547471 3482405 := bbase (se 4 (by rfl) ⟨326475, by rfl⟩ : syracuseStep 3482405 = 652951) (by norm_num)
theorem B1958737 : Blo 1547471 1958737 := bbase (se 2 (by rfl) ⟨734526, by rfl⟩ : syracuseStep 1958737 = 1469053) (by norm_num)
theorem B3482477 : Blo 1547471 3482477 := bbase (se 3 (by rfl) ⟨652964, by rfl⟩ : syracuseStep 3482477 = 1305929) (by norm_num)
theorem B2614133 : Blo 1547471 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B1958833 : Blo 1547471 1958833 := bbase (se 2 (by rfl) ⟨734562, by rfl⟩ : syracuseStep 1958833 = 1469125) (by norm_num)
theorem B3482549 : Blo 1547471 3482549 := bbase (se 5 (by rfl) ⟨163244, by rfl⟩ : syracuseStep 3482549 = 326489) (by norm_num)
theorem B2614261 : Blo 1547471 2614261 := bbase (se 5 (by rfl) ⟨122543, by rfl⟩ : syracuseStep 2614261 = 245087) (by norm_num)
theorem B3482621 : Blo 1547471 3482621 := bbase (se 3 (by rfl) ⟨652991, by rfl⟩ : syracuseStep 3482621 = 1305983) (by norm_num)
theorem B3482693 : Blo 1547471 3482693 := bbase (se 4 (by rfl) ⟨326502, by rfl⟩ : syracuseStep 3482693 = 653005) (by norm_num)
theorem B2614349 : Blo 1547471 2614349 := bbase (se 3 (by rfl) ⟨490190, by rfl⟩ : syracuseStep 2614349 = 980381) (by norm_num)
theorem B1959005 : Blo 1547471 1959005 := bbase (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) (by norm_num)
theorem B5031013 : Blo 1547471 5031013 := bbase (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) (by norm_num)
theorem B3482765 : Blo 1547471 3482765 := bbase (se 3 (by rfl) ⟨653018, by rfl⟩ : syracuseStep 3482765 = 1306037) (by norm_num)
theorem B1959061 : Blo 1547471 1959061 := bbase (se 6 (by rfl) ⟨45915, by rfl⟩ : syracuseStep 1959061 = 91831) (by norm_num)
theorem B4408469 : Blo 1547471 4408469 := bbase (se 6 (by rfl) ⟨103323, by rfl⟩ : syracuseStep 4408469 = 206647) (by norm_num)
theorem B5227685 : Blo 1547471 5227685 := bbase (se 4 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 5227685 = 980191) (by norm_num)
theorem B2614477 : Blo 1547471 2614477 := bbase (se 3 (by rfl) ⟨490214, by rfl⟩ : syracuseStep 2614477 = 980429) (by norm_num)
theorem B3482837 : Blo 1547471 3482837 := bbase (se 7 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 3482837 = 81629) (by norm_num)
theorem B1885421 : Blo 1547471 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1959157 : Blo 1547471 1959157 := bbase (se 5 (by rfl) ⟨91835, by rfl⟩ : syracuseStep 1959157 = 183671) (by norm_num)
theorem B3917069 : Blo 1547471 3917069 := bbase (se 3 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 3917069 = 1468901) (by norm_num)
theorem B3482909 : Blo 1547471 3482909 := bbase (se 3 (by rfl) ⟨653045, by rfl⟩ : syracuseStep 3482909 = 1306091) (by norm_num)
theorem B2614565 : Blo 1547471 2614565 := bbase (se 4 (by rfl) ⟨245115, by rfl⟩ : syracuseStep 2614565 = 490231) (by norm_num)
theorem B6612293 : Blo 1547471 6612293 := bbase (se 4 (by rfl) ⟨619902, by rfl⟩ : syracuseStep 6612293 = 1239805) (by norm_num)
theorem B3482981 : Blo 1547471 3482981 := bbase (se 4 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 3482981 = 653059) (by norm_num)
theorem B1959329 : Blo 1547471 1959329 := bbase (se 2 (by rfl) ⟨734748, by rfl⟩ : syracuseStep 1959329 = 1469497) (by norm_num)
theorem B2614693 : Blo 1547471 2614693 := bbase (se 4 (by rfl) ⟨245127, by rfl⟩ : syracuseStep 2614693 = 490255) (by norm_num)
theorem B3483053 : Blo 1547471 3483053 := bbase (se 3 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 3483053 = 1306145) (by norm_num)
theorem B6038981 : Blo 1547471 6038981 := bbase (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) (by norm_num)
theorem B3917261 : Blo 1547471 3917261 := bbase (se 3 (by rfl) ⟨734486, by rfl⟩ : syracuseStep 3917261 = 1468973) (by norm_num)
theorem B1959385 : Blo 1547471 1959385 := bbase (se 2 (by rfl) ⟨734769, by rfl⟩ : syracuseStep 1959385 = 1469539) (by norm_num)
theorem B2205157 : Blo 1547471 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B3483125 : Blo 1547471 3483125 := bbase (se 5 (by rfl) ⟨163271, by rfl⟩ : syracuseStep 3483125 = 326543) (by norm_num)
theorem B7841285 : Blo 1547471 7841285 := bbase (se 4 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 7841285 = 1470241) (by norm_num)
theorem B1959481 : Blo 1547471 1959481 := bbase (se 2 (by rfl) ⟨734805, by rfl⟩ : syracuseStep 1959481 = 1469611) (by norm_num)
theorem B3483197 : Blo 1547471 3483197 := bbase (se 3 (by rfl) ⟨653099, by rfl⟩ : syracuseStep 3483197 = 1306199) (by norm_num)
theorem B4408901 : Blo 1547471 4408901 := bbase (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) (by norm_num)
theorem B5228117 : Blo 1547471 5228117 := bbase (se 8 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 5228117 = 61267) (by norm_num)
theorem B6039157 : Blo 1547471 6039157 := bbase (se 5 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 6039157 = 566171) (by norm_num)
theorem B3483269 : Blo 1547471 3483269 := bbase (se 4 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 3483269 = 653113) (by norm_num)
theorem B4957861 : Blo 1547471 4957861 := bbase (se 4 (by rfl) ⟨464799, by rfl⟩ : syracuseStep 4957861 = 929599) (by norm_num)
theorem B3483341 : Blo 1547471 3483341 := bbase (se 3 (by rfl) ⟨653126, by rfl⟩ : syracuseStep 3483341 = 1306253) (by norm_num)
theorem B1959653 : Blo 1547471 1959653 := bbase (se 4 (by rfl) ⟨183717, by rfl⟩ : syracuseStep 1959653 = 367435) (by norm_num)
theorem B1861385 : Blo 1547471 1861385 := bbase (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) (by norm_num)
theorem B3483413 : Blo 1547471 3483413 := bbase (se 6 (by rfl) ⟨81642, by rfl⟩ : syracuseStep 3483413 = 163285) (by norm_num)
theorem B1959709 : Blo 1547471 1959709 := bbase (se 3 (by rfl) ⟨367445, by rfl⟩ : syracuseStep 1959709 = 734891) (by norm_num)
theorem B3917605 : Blo 1547471 3917605 := bbase (se 4 (by rfl) ⟨367275, by rfl⟩ : syracuseStep 3917605 = 734551) (by norm_num)
theorem B3483485 : Blo 1547471 3483485 := bbase (se 3 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 3483485 = 1306307) (by norm_num)
theorem B10594165 : Blo 1547471 10594165 := bbase (se 5 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 10594165 = 993203) (by norm_num)
theorem B14886773 : Blo 1547471 14886773 := bbase (se 5 (by rfl) ⟨697817, by rfl⟩ : syracuseStep 14886773 = 1395635) (by norm_num)
theorem B1959805 : Blo 1547471 1959805 := bbase (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) (by norm_num)
theorem B3975037 : Blo 1547471 3975037 := bbase (se 3 (by rfl) ⟨745319, by rfl⟩ : syracuseStep 3975037 = 1490639) (by norm_num)
theorem B5957509 : Blo 1547471 5957509 := bbase (se 4 (by rfl) ⟨558516, by rfl⟩ : syracuseStep 5957509 = 1117033) (by norm_num)
theorem B3917717 : Blo 1547471 3917717 := bbase (se 6 (by rfl) ⟨91821, by rfl⟩ : syracuseStep 3917717 = 183643) (by norm_num)
theorem B3483557 : Blo 1547471 3483557 := bbase (se 4 (by rfl) ⟨326583, by rfl⟩ : syracuseStep 3483557 = 653167) (by norm_num)
theorem B3483629 : Blo 1547471 3483629 := bbase (se 3 (by rfl) ⟨653180, by rfl⟩ : syracuseStep 3483629 = 1306361) (by norm_num)
theorem B4188149 : Blo 1547471 4188149 := bbase (se 5 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 4188149 = 392639) (by norm_num)
theorem B5228549 : Blo 1547471 5228549 := bbase (se 4 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 5228549 = 980353) (by norm_num)
theorem B1959977 : Blo 1547471 1959977 := bbase (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) (by norm_num)
theorem B3721261 : Blo 1547471 3721261 := bbase (se 3 (by rfl) ⟨697736, by rfl⟩ : syracuseStep 3721261 = 1395473) (by norm_num)
theorem B3483701 : Blo 1547471 3483701 := bbase (se 5 (by rfl) ⟨163298, by rfl⟩ : syracuseStep 3483701 = 326597) (by norm_num)
theorem B2205749 : Blo 1547471 2205749 := bbase (se 5 (by rfl) ⟨103394, by rfl⟩ : syracuseStep 2205749 = 206789) (by norm_num)
theorem B3139661 : Blo 1547471 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B3917909 : Blo 1547471 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B1960033 : Blo 1547471 1960033 := bbase (se 2 (by rfl) ⟨735012, by rfl⟩ : syracuseStep 1960033 = 1470025) (by norm_num)
theorem B3483773 : Blo 1547471 3483773 := bbase (se 3 (by rfl) ⟨653207, by rfl⟩ : syracuseStep 3483773 = 1306415) (by norm_num)
theorem B2205829 : Blo 1547471 2205829 := bbase (se 4 (by rfl) ⟨206796, by rfl⟩ : syracuseStep 2205829 = 413593) (by norm_num)
theorem B5875861 : Blo 1547471 5875861 := bbase (se 6 (by rfl) ⟨137715, by rfl⟩ : syracuseStep 5875861 = 275431) (by norm_num)
theorem B1960129 : Blo 1547471 1960129 := bbase (se 2 (by rfl) ⟨735048, by rfl⟩ : syracuseStep 1960129 = 1470097) (by norm_num)
theorem B3483845 : Blo 1547471 3483845 := bbase (se 4 (by rfl) ⟨326610, by rfl⟩ : syracuseStep 3483845 = 653221) (by norm_num)
theorem B2205949 : Blo 1547471 2205949 := bbase (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) (by norm_num)
theorem B3483917 : Blo 1547471 3483917 := bbase (se 3 (by rfl) ⟨653234, by rfl⟩ : syracuseStep 3483917 = 1306469) (by norm_num)
theorem B4409653 : Blo 1547471 4409653 := bbase (se 5 (by rfl) ⟨206702, by rfl⟩ : syracuseStep 4409653 = 413405) (by norm_num)
theorem B3483989 : Blo 1547471 3483989 := bbase (se 10 (by rfl) ⟨5103, by rfl⟩ : syracuseStep 3483989 = 10207) (by norm_num)
theorem B2206045 : Blo 1547471 2206045 := bbase (se 3 (by rfl) ⟨413633, by rfl⟩ : syracuseStep 2206045 = 827267) (by norm_num)
theorem B1960301 : Blo 1547471 1960301 := bbase (se 3 (by rfl) ⟨367556, by rfl⟩ : syracuseStep 1960301 = 735113) (by norm_num)
theorem B6367621 : Blo 1547471 6367621 := bbase (se 4 (by rfl) ⟨596964, by rfl⟩ : syracuseStep 6367621 = 1193929) (by norm_num)
theorem B3484061 : Blo 1547471 3484061 := bbase (se 3 (by rfl) ⟨653261, by rfl⟩ : syracuseStep 3484061 = 1306523) (by norm_num)
theorem B1960357 : Blo 1547471 1960357 := bbase (se 4 (by rfl) ⟨183783, by rfl⟩ : syracuseStep 1960357 = 367567) (by norm_num)
theorem B3918253 : Blo 1547471 3918253 := bbase (se 3 (by rfl) ⟨734672, by rfl⟩ : syracuseStep 3918253 = 1469345) (by norm_num)
theorem B5228981 : Blo 1547471 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B5876165 : Blo 1547471 5876165 := bbase (se 4 (by rfl) ⟨550890, by rfl⟩ : syracuseStep 5876165 = 1101781) (by norm_num)
theorem B19843541 : Blo 1547471 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B3484133 : Blo 1547471 3484133 := bbase (se 4 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 3484133 = 653275) (by norm_num)
theorem B1960453 : Blo 1547471 1960453 := bbase (se 4 (by rfl) ⟨183792, by rfl⟩ : syracuseStep 1960453 = 367585) (by norm_num)
theorem B3918365 : Blo 1547471 3918365 := bbase (se 3 (by rfl) ⟨734693, by rfl⟩ : syracuseStep 3918365 = 1469387) (by norm_num)
theorem B3484205 : Blo 1547471 3484205 := bbase (se 3 (by rfl) ⟨653288, by rfl⟩ : syracuseStep 3484205 = 1306577) (by norm_num)
theorem B3484277 : Blo 1547471 3484277 := bbase (se 5 (by rfl) ⟨163325, by rfl⟩ : syracuseStep 3484277 = 326651) (by norm_num)
theorem B2091685 : Blo 1547471 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B1960625 : Blo 1547471 1960625 := bbase (se 2 (by rfl) ⟨735234, by rfl⟩ : syracuseStep 1960625 = 1470469) (by norm_num)
theorem B3484349 : Blo 1547471 3484349 := bbase (se 3 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 3484349 = 1306631) (by norm_num)
theorem B3721925 : Blo 1547471 3721925 := bbase (se 4 (by rfl) ⟨348930, by rfl⟩ : syracuseStep 3721925 = 697861) (by norm_num)
theorem B3918557 : Blo 1547471 3918557 := bbase (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) (by norm_num)
theorem B1960681 : Blo 1547471 1960681 := bbase (se 2 (by rfl) ⟨735255, by rfl⟩ : syracuseStep 1960681 = 1470511) (by norm_num)
theorem B2419445 : Blo 1547471 2419445 := bbase (se 5 (by rfl) ⟨113411, by rfl⟩ : syracuseStep 2419445 = 226823) (by norm_num)
theorem B3484421 : Blo 1547471 3484421 := bbase (se 4 (by rfl) ⟨326664, by rfl⟩ : syracuseStep 3484421 = 653329) (by norm_num)
theorem B7842581 : Blo 1547471 7842581 := bbase (se 6 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 7842581 = 367621) (by norm_num)
theorem B3140381 : Blo 1547471 3140381 := bbase (se 3 (by rfl) ⟨588821, by rfl⟩ : syracuseStep 3140381 = 1177643) (by norm_num)
theorem B2321213 : Blo 1547471 2321213 := bbase (se 3 (by rfl) ⟨435227, by rfl⟩ : syracuseStep 2321213 = 870455) (by norm_num)
theorem B1960777 : Blo 1547471 1960777 := bbase (se 2 (by rfl) ⟨735291, by rfl⟩ : syracuseStep 1960777 = 1470583) (by norm_num)
theorem B3484493 : Blo 1547471 3484493 := bbase (se 3 (by rfl) ⟨653342, by rfl⟩ : syracuseStep 3484493 = 1306685) (by norm_num)
theorem B2321237 : Blo 1547471 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B7441253 : Blo 1547471 7441253 := bbase (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) (by norm_num)
theorem B5229413 : Blo 1547471 5229413 := bbase (se 4 (by rfl) ⟨490257, by rfl⟩ : syracuseStep 5229413 = 980515) (by norm_num)
theorem B2321261 : Blo 1547471 2321261 := bbase (se 3 (by rfl) ⟨435236, by rfl⟩ : syracuseStep 2321261 = 870473) (by norm_num)
theorem B2091901 : Blo 1547471 2091901 := bbase (se 3 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 2091901 = 784463) (by norm_num)
theorem B2321285 : Blo 1547471 2321285 := bbase (se 4 (by rfl) ⟨217620, by rfl⟩ : syracuseStep 2321285 = 435241) (by norm_num)
theorem B3230597 : Blo 1547471 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B17640341 : Blo 1547471 17640341 := bbase (se 6 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 17640341 = 826891) (by norm_num)
theorem B3484565 : Blo 1547471 3484565 := bbase (se 6 (by rfl) ⟨81669, by rfl⟩ : syracuseStep 3484565 = 163339) (by norm_num)
theorem B2321309 : Blo 1547471 2321309 := bbase (se 3 (by rfl) ⟨435245, by rfl⟩ : syracuseStep 2321309 = 870491) (by norm_num)
theorem B2321333 : Blo 1547471 2321333 := bbase (se 5 (by rfl) ⟨108812, by rfl⟩ : syracuseStep 2321333 = 217625) (by norm_num)
theorem B2321357 : Blo 1547471 2321357 := bbase (se 3 (by rfl) ⟨435254, by rfl⟩ : syracuseStep 2321357 = 870509) (by norm_num)
theorem B3484637 : Blo 1547471 3484637 := bbase (se 3 (by rfl) ⟨653369, by rfl⟩ : syracuseStep 3484637 = 1306739) (by norm_num)
theorem B2321381 : Blo 1547471 2321381 := bbase (se 4 (by rfl) ⟨217629, by rfl⟩ : syracuseStep 2321381 = 435259) (by norm_num)
theorem B1960949 : Blo 1547471 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B2321405 : Blo 1547471 2321405 := bbase (se 3 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 2321405 = 870527) (by norm_num)
theorem B2321429 : Blo 1547471 2321429 := bbase (se 6 (by rfl) ⟨54408, by rfl⟩ : syracuseStep 2321429 = 108817) (by norm_num)
theorem B2092069 : Blo 1547471 2092069 := bbase (se 4 (by rfl) ⟨196131, by rfl⟩ : syracuseStep 2092069 = 392263) (by norm_num)
theorem B3484709 : Blo 1547471 3484709 := bbase (se 4 (by rfl) ⟨326691, by rfl⟩ : syracuseStep 3484709 = 653383) (by norm_num)
theorem B2321453 : Blo 1547471 2321453 := bbase (se 3 (by rfl) ⟨435272, by rfl⟩ : syracuseStep 2321453 = 870545) (by norm_num)
theorem B1961005 : Blo 1547471 1961005 := bbase (se 3 (by rfl) ⟨367688, by rfl⟩ : syracuseStep 1961005 = 735377) (by norm_num)
theorem B3918901 : Blo 1547471 3918901 := bbase (se 5 (by rfl) ⟨183698, by rfl⟩ : syracuseStep 3918901 = 367397) (by norm_num)
theorem B2321477 : Blo 1547471 2321477 := bbase (se 4 (by rfl) ⟨217638, by rfl⟩ : syracuseStep 2321477 = 435277) (by norm_num)
theorem B2092117 : Blo 1547471 2092117 := bbase (se 8 (by rfl) ⟨12258, by rfl⟩ : syracuseStep 2092117 = 24517) (by norm_num)
theorem B2321501 : Blo 1547471 2321501 := bbase (se 3 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 2321501 = 870563) (by norm_num)
theorem B3484781 : Blo 1547471 3484781 := bbase (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) (by norm_num)
theorem B2321525 : Blo 1547471 2321525 := bbase (se 5 (by rfl) ⟨108821, by rfl⟩ : syracuseStep 2321525 = 217643) (by norm_num)
theorem B7441541 : Blo 1547471 7441541 := bbase (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) (by norm_num)
theorem B2321549 : Blo 1547471 2321549 := bbase (se 3 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 2321549 = 870581) (by norm_num)
theorem B2321573 : Blo 1547471 2321573 := bbase (se 4 (by rfl) ⟨217647, by rfl⟩ : syracuseStep 2321573 = 435295) (by norm_num)
theorem B3919013 : Blo 1547471 3919013 := bbase (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) (by norm_num)
theorem B7834805 : Blo 1547471 7834805 := bbase (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) (by norm_num)
theorem B3484853 : Blo 1547471 3484853 := bbase (se 5 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 3484853 = 326705) (by norm_num)
theorem B2321597 : Blo 1547471 2321597 := bbase (se 3 (by rfl) ⟨435299, by rfl⟩ : syracuseStep 2321597 = 870599) (by norm_num)
theorem B2321621 : Blo 1547471 2321621 := bbase (se 7 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 2321621 = 54413) (by norm_num)
theorem B2321645 : Blo 1547471 2321645 := bbase (se 3 (by rfl) ⟨435308, by rfl⟩ : syracuseStep 2321645 = 870617) (by norm_num)
theorem B3484925 : Blo 1547471 3484925 := bbase (se 3 (by rfl) ⟨653423, by rfl⟩ : syracuseStep 3484925 = 1306847) (by norm_num)
theorem B2321669 : Blo 1547471 2321669 := bbase (se 4 (by rfl) ⟨217656, by rfl⟩ : syracuseStep 2321669 = 435313) (by norm_num)
theorem B3140869 : Blo 1547471 3140869 := bbase (se 4 (by rfl) ⟨294456, by rfl⟩ : syracuseStep 3140869 = 588913) (by norm_num)
theorem B2321693 : Blo 1547471 2321693 := bbase (se 3 (by rfl) ⟨435317, by rfl⟩ : syracuseStep 2321693 = 870635) (by norm_num)
theorem B2321717 : Blo 1547471 2321717 := bbase (se 5 (by rfl) ⟨108830, by rfl⟩ : syracuseStep 2321717 = 217661) (by norm_num)
theorem B3484997 : Blo 1547471 3484997 := bbase (se 4 (by rfl) ⟨326718, by rfl⟩ : syracuseStep 3484997 = 653437) (by norm_num)
theorem B2321741 : Blo 1547471 2321741 := bbase (se 3 (by rfl) ⟨435326, by rfl⟩ : syracuseStep 2321741 = 870653) (by norm_num)
theorem B2321765 : Blo 1547471 2321765 := bbase (se 4 (by rfl) ⟨217665, by rfl⟩ : syracuseStep 2321765 = 435331) (by norm_num)
theorem B3919205 : Blo 1547471 3919205 := bbase (se 4 (by rfl) ⟨367425, by rfl⟩ : syracuseStep 3919205 = 734851) (by norm_num)
theorem B3140965 : Blo 1547471 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B2788733 : Blo 1547471 2788733 := bbase (se 3 (by rfl) ⟨522887, by rfl⟩ : syracuseStep 2788733 = 1045775) (by norm_num)
theorem B2321789 : Blo 1547471 2321789 := bbase (se 3 (by rfl) ⟨435335, by rfl⟩ : syracuseStep 2321789 = 870671) (by norm_num)
theorem B3485069 : Blo 1547471 3485069 := bbase (se 3 (by rfl) ⟨653450, by rfl⟩ : syracuseStep 3485069 = 1306901) (by norm_num)
theorem B2321813 : Blo 1547471 2321813 := bbase (se 6 (by rfl) ⟨54417, by rfl⟩ : syracuseStep 2321813 = 108835) (by norm_num)
theorem B1764769 : Blo 1547471 1764769 := bbase (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) (by norm_num)
theorem B2321837 : Blo 1547471 2321837 := bbase (se 3 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 2321837 = 870689) (by norm_num)
theorem B3181997 : Blo 1547471 3181997 := bbase (se 3 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 3181997 = 1193249) (by norm_num)
theorem B2321861 : Blo 1547471 2321861 := bbase (se 4 (by rfl) ⟨217674, by rfl⟩ : syracuseStep 2321861 = 435349) (by norm_num)
theorem B3485141 : Blo 1547471 3485141 := bbase (se 7 (by rfl) ⟨40841, by rfl⟩ : syracuseStep 3485141 = 81683) (by norm_num)
theorem B2321885 : Blo 1547471 2321885 := bbase (se 3 (by rfl) ⟨435353, by rfl⟩ : syracuseStep 2321885 = 870707) (by norm_num)
theorem B2321909 : Blo 1547471 2321909 := bbase (se 5 (by rfl) ⟨108839, by rfl⟩ : syracuseStep 2321909 = 217679) (by norm_num)
theorem B2321933 : Blo 1547471 2321933 := bbase (se 3 (by rfl) ⟨435362, by rfl⟩ : syracuseStep 2321933 = 870725) (by norm_num)
theorem B3485213 : Blo 1547471 3485213 := bbase (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) (by norm_num)
theorem B2321957 : Blo 1547471 2321957 := bbase (se 4 (by rfl) ⟨217683, by rfl⟩ : syracuseStep 2321957 = 435367) (by norm_num)
theorem B2321981 : Blo 1547471 2321981 := bbase (se 3 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 2321981 = 870743) (by norm_num)
theorem B2322005 : Blo 1547471 2322005 := bbase (se 8 (by rfl) ⟨13605, by rfl⟩ : syracuseStep 2322005 = 27211) (by norm_num)
theorem B3305053 : Blo 1547471 3305053 := bbase (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) (by norm_num)
theorem B3485285 : Blo 1547471 3485285 := bbase (se 4 (by rfl) ⟨326745, by rfl⟩ : syracuseStep 3485285 = 653491) (by norm_num)
theorem B2322029 : Blo 1547471 2322029 := bbase (se 3 (by rfl) ⟨435380, by rfl⟩ : syracuseStep 2322029 = 870761) (by norm_num)
theorem B2322053 : Blo 1547471 2322053 := bbase (se 4 (by rfl) ⟨217692, by rfl⟩ : syracuseStep 2322053 = 435385) (by norm_num)
theorem B2322077 : Blo 1547471 2322077 := bbase (se 3 (by rfl) ⟨435389, by rfl⟩ : syracuseStep 2322077 = 870779) (by norm_num)
theorem B3485357 : Blo 1547471 3485357 := bbase (se 3 (by rfl) ⟨653504, by rfl⟩ : syracuseStep 3485357 = 1307009) (by norm_num)
theorem B2322101 : Blo 1547471 2322101 := bbase (se 5 (by rfl) ⟨108848, by rfl⟩ : syracuseStep 2322101 = 217697) (by norm_num)
theorem B3919549 : Blo 1547471 3919549 := bbase (se 3 (by rfl) ⟨734915, by rfl⟩ : syracuseStep 3919549 = 1469831) (by norm_num)
theorem B2322125 : Blo 1547471 2322125 := bbase (se 3 (by rfl) ⟨435398, by rfl⟩ : syracuseStep 2322125 = 870797) (by norm_num)
theorem B2322149 : Blo 1547471 2322149 := bbase (se 4 (by rfl) ⟨217701, by rfl⟩ : syracuseStep 2322149 = 435403) (by norm_num)
theorem B12553973 : Blo 1547471 12553973 := bbase (se 5 (by rfl) ⟨588467, by rfl⟩ : syracuseStep 12553973 = 1176935) (by norm_num)
theorem B3485429 : Blo 1547471 3485429 := bbase (se 5 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 3485429 = 326759) (by norm_num)
theorem B2322173 : Blo 1547471 2322173 := bbase (se 3 (by rfl) ⟨435407, by rfl⟩ : syracuseStep 2322173 = 870815) (by norm_num)
theorem B2322197 : Blo 1547471 2322197 := bbase (se 6 (by rfl) ⟨54426, by rfl⟩ : syracuseStep 2322197 = 108853) (by norm_num)
theorem B1986329 : Blo 1547471 1986329 := bbase (se 2 (by rfl) ⟨744873, by rfl⟩ : syracuseStep 1986329 = 1489747) (by norm_num)
theorem B2322221 : Blo 1547471 2322221 := bbase (se 3 (by rfl) ⟨435416, by rfl⟩ : syracuseStep 2322221 = 870833) (by norm_num)
theorem B3919661 : Blo 1547471 3919661 := bbase (se 3 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 3919661 = 1469873) (by norm_num)
theorem B5959477 : Blo 1547471 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B3485501 : Blo 1547471 3485501 := bbase (se 3 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 3485501 = 1307063) (by norm_num)
theorem B2322245 : Blo 1547471 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2322269 : Blo 1547471 2322269 := bbase (se 3 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 2322269 = 870851) (by norm_num)
theorem B4771685 : Blo 1547471 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B2322293 : Blo 1547471 2322293 := bbase (se 5 (by rfl) ⟨108857, by rfl⟩ : syracuseStep 2322293 = 217715) (by norm_num)
theorem B3485573 : Blo 1547471 3485573 := bbase (se 4 (by rfl) ⟨326772, by rfl⟩ : syracuseStep 3485573 = 653545) (by norm_num)
theorem B2322317 : Blo 1547471 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B2322341 : Blo 1547471 2322341 := bbase (se 4 (by rfl) ⟨217719, by rfl⟩ : syracuseStep 2322341 = 435439) (by norm_num)
theorem B2322365 : Blo 1547471 2322365 := bbase (se 3 (by rfl) ⟨435443, by rfl⟩ : syracuseStep 2322365 = 870887) (by norm_num)
theorem B3485645 : Blo 1547471 3485645 := bbase (se 3 (by rfl) ⟨653558, by rfl⟩ : syracuseStep 3485645 = 1307117) (by norm_num)
theorem B2322389 : Blo 1547471 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B2322413 : Blo 1547471 2322413 := bbase (se 3 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 2322413 = 870905) (by norm_num)
theorem B3919853 : Blo 1547471 3919853 := bbase (se 3 (by rfl) ⟨734972, by rfl⟩ : syracuseStep 3919853 = 1469945) (by norm_num)
theorem B2322437 : Blo 1547471 2322437 := bbase (se 4 (by rfl) ⟨217728, by rfl⟩ : syracuseStep 2322437 = 435457) (by norm_num)
theorem B3485717 : Blo 1547471 3485717 := bbase (se 6 (by rfl) ⟨81696, by rfl⟩ : syracuseStep 3485717 = 163393) (by norm_num)
theorem B2322461 : Blo 1547471 2322461 := bbase (se 3 (by rfl) ⟨435461, by rfl⟩ : syracuseStep 2322461 = 870923) (by norm_num)
theorem B7843877 : Blo 1547471 7843877 := bbase (se 4 (by rfl) ⟨735363, by rfl⟩ : syracuseStep 7843877 = 1470727) (by norm_num)
theorem B6205493 : Blo 1547471 6205493 := bbase (se 5 (by rfl) ⟨290882, by rfl⟩ : syracuseStep 6205493 = 581765) (by norm_num)
theorem B2322485 : Blo 1547471 2322485 := bbase (se 5 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 2322485 = 217733) (by norm_num)
theorem B3305549 : Blo 1547471 3305549 := bbase (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) (by norm_num)
theorem B2322509 : Blo 1547471 2322509 := bbase (se 3 (by rfl) ⟨435470, by rfl⟩ : syracuseStep 2322509 = 870941) (by norm_num)
theorem B3182669 : Blo 1547471 3182669 := bbase (se 3 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 3182669 = 1193501) (by norm_num)
theorem B3485789 : Blo 1547471 3485789 := bbase (se 3 (by rfl) ⟨653585, by rfl⟩ : syracuseStep 3485789 = 1307171) (by norm_num)
theorem B2322533 : Blo 1547471 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B1568893 : Blo 1547471 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B2322557 : Blo 1547471 2322557 := bbase (se 3 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 2322557 = 870959) (by norm_num)
theorem B1740937 : Blo 1547471 1740937 := bbase (se 2 (by rfl) ⟨652851, by rfl⟩ : syracuseStep 1740937 = 1305703) (by norm_num)
theorem B2322581 : Blo 1547471 2322581 := bbase (se 6 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 2322581 = 108871) (by norm_num)
theorem B7065749 : Blo 1547471 7065749 := bbase (se 6 (by rfl) ⟨165603, by rfl⟩ : syracuseStep 7065749 = 331207) (by norm_num)
theorem B3485861 : Blo 1547471 3485861 := bbase (se 4 (by rfl) ⟨326799, by rfl⟩ : syracuseStep 3485861 = 653599) (by norm_num)
theorem B1740973 : Blo 1547471 1740973 := bbase (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) (by norm_num)
theorem B2322605 : Blo 1547471 2322605 := bbase (se 3 (by rfl) ⟨435488, by rfl⟩ : syracuseStep 2322605 = 870977) (by norm_num)
theorem B2322629 : Blo 1547471 2322629 := bbase (se 4 (by rfl) ⟨217746, by rfl⟩ : syracuseStep 2322629 = 435493) (by norm_num)
theorem B1741009 : Blo 1547471 1741009 := bbase (se 2 (by rfl) ⟨652878, by rfl⟩ : syracuseStep 1741009 = 1305757) (by norm_num)
theorem B2322653 : Blo 1547471 2322653 := bbase (se 3 (by rfl) ⟨435497, by rfl⟩ : syracuseStep 2322653 = 870995) (by norm_num)
theorem B3485933 : Blo 1547471 3485933 := bbase (se 3 (by rfl) ⟨653612, by rfl⟩ : syracuseStep 3485933 = 1307225) (by norm_num)
theorem B1741045 : Blo 1547471 1741045 := bbase (se 5 (by rfl) ⟨81611, by rfl⟩ : syracuseStep 1741045 = 163223) (by norm_num)
theorem B1765621 : Blo 1547471 1765621 := bbase (se 5 (by rfl) ⟨82763, by rfl⟩ : syracuseStep 1765621 = 165527) (by norm_num)
theorem B2322677 : Blo 1547471 2322677 := bbase (se 5 (by rfl) ⟨108875, by rfl⟩ : syracuseStep 2322677 = 217751) (by norm_num)
theorem B2322701 : Blo 1547471 2322701 := bbase (se 3 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 2322701 = 871013) (by norm_num)
theorem B1741081 : Blo 1547471 1741081 := bbase (se 2 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 1741081 = 1305811) (by norm_num)
theorem B2322725 : Blo 1547471 2322725 := bbase (se 4 (by rfl) ⟨217755, by rfl⟩ : syracuseStep 2322725 = 435511) (by norm_num)
theorem B3486005 : Blo 1547471 3486005 := bbase (se 5 (by rfl) ⟨163406, by rfl⟩ : syracuseStep 3486005 = 326813) (by norm_num)
theorem B1741117 : Blo 1547471 1741117 := bbase (se 3 (by rfl) ⟨326459, by rfl⟩ : syracuseStep 1741117 = 652919) (by norm_num)
theorem B2322749 : Blo 1547471 2322749 := bbase (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) (by norm_num)
theorem B3920197 : Blo 1547471 3920197 := bbase (se 4 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 3920197 = 735037) (by norm_num)
theorem B2322773 : Blo 1547471 2322773 := bbase (se 10 (by rfl) ⟨3402, by rfl⟩ : syracuseStep 2322773 = 6805) (by norm_num)
theorem B1741153 : Blo 1547471 1741153 := bbase (se 2 (by rfl) ⟨652932, by rfl⟩ : syracuseStep 1741153 = 1305865) (by norm_num)
theorem B2322797 : Blo 1547471 2322797 := bbase (se 3 (by rfl) ⟨435524, by rfl⟩ : syracuseStep 2322797 = 871049) (by norm_num)
theorem B3486077 : Blo 1547471 3486077 := bbase (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) (by norm_num)
theorem B1741189 : Blo 1547471 1741189 := bbase (se 4 (by rfl) ⟨163236, by rfl⟩ : syracuseStep 1741189 = 326473) (by norm_num)
theorem B2322821 : Blo 1547471 2322821 := bbase (se 4 (by rfl) ⟨217764, by rfl⟩ : syracuseStep 2322821 = 435529) (by norm_num)
theorem B2322845 : Blo 1547471 2322845 := bbase (se 3 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 2322845 = 871067) (by norm_num)
theorem B1741225 : Blo 1547471 1741225 := bbase (se 2 (by rfl) ⟨652959, by rfl⟩ : syracuseStep 1741225 = 1305919) (by norm_num)
theorem B2322869 : Blo 1547471 2322869 := bbase (se 5 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 2322869 = 217769) (by norm_num)
theorem B3920309 : Blo 1547471 3920309 := bbase (se 5 (by rfl) ⟨183764, by rfl⟩ : syracuseStep 3920309 = 367529) (by norm_num)
theorem B7836101 : Blo 1547471 7836101 := bbase (se 4 (by rfl) ⟨734634, by rfl⟩ : syracuseStep 7836101 = 1469269) (by norm_num)
theorem B3486149 : Blo 1547471 3486149 := bbase (se 4 (by rfl) ⟨326826, by rfl⟩ : syracuseStep 3486149 = 653653) (by norm_num)
theorem B1741261 : Blo 1547471 1741261 := bbase (se 3 (by rfl) ⟨326486, by rfl⟩ : syracuseStep 1741261 = 652973) (by norm_num)
theorem B2322893 : Blo 1547471 2322893 := bbase (se 3 (by rfl) ⟨435542, by rfl⟩ : syracuseStep 2322893 = 871085) (by norm_num)
theorem B2322917 : Blo 1547471 2322917 := bbase (se 4 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 2322917 = 435547) (by norm_num)
theorem B1741297 : Blo 1547471 1741297 := bbase (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) (by norm_num)
theorem B2322941 : Blo 1547471 2322941 := bbase (se 3 (by rfl) ⟨435551, by rfl⟩ : syracuseStep 2322941 = 871103) (by norm_num)
theorem B5878277 : Blo 1547471 5878277 := bbase (se 4 (by rfl) ⟨551088, by rfl⟩ : syracuseStep 5878277 = 1102177) (by norm_num)
theorem B2789893 : Blo 1547471 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B3486221 : Blo 1547471 3486221 := bbase (se 3 (by rfl) ⟨653666, by rfl⟩ : syracuseStep 3486221 = 1307333) (by norm_num)
theorem B5222933 : Blo 1547471 5222933 := bbase (se 6 (by rfl) ⟨122412, by rfl⟩ : syracuseStep 5222933 = 244825) (by norm_num)
theorem B1741333 : Blo 1547471 1741333 := bbase (se 6 (by rfl) ⟨40812, by rfl⟩ : syracuseStep 1741333 = 81625) (by norm_num)
theorem B2322965 : Blo 1547471 2322965 := bbase (se 6 (by rfl) ⟨54444, by rfl⟩ : syracuseStep 2322965 = 108889) (by norm_num)
theorem B2322989 : Blo 1547471 2322989 := bbase (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) (by norm_num)
theorem B1741369 : Blo 1547471 1741369 := bbase (se 2 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 1741369 = 1306027) (by norm_num)
theorem B2323013 : Blo 1547471 2323013 := bbase (se 4 (by rfl) ⟨217782, by rfl⟩ : syracuseStep 2323013 = 435565) (by norm_num)
theorem B3486293 : Blo 1547471 3486293 := bbase (se 8 (by rfl) ⟨20427, by rfl⟩ : syracuseStep 3486293 = 40855) (by norm_num)
theorem B1741405 : Blo 1547471 1741405 := bbase (se 3 (by rfl) ⟨326513, by rfl⟩ : syracuseStep 1741405 = 653027) (by norm_num)
theorem B2323037 : Blo 1547471 2323037 := bbase (se 3 (by rfl) ⟨435569, by rfl⟩ : syracuseStep 2323037 = 871139) (by norm_num)
theorem B2323061 : Blo 1547471 2323061 := bbase (se 5 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 2323061 = 217787) (by norm_num)
theorem B3920501 : Blo 1547471 3920501 := bbase (se 5 (by rfl) ⟨183773, by rfl⟩ : syracuseStep 3920501 = 367547) (by norm_num)
theorem B1741441 : Blo 1547471 1741441 := bbase (se 2 (by rfl) ⟨653040, by rfl⟩ : syracuseStep 1741441 = 1306081) (by norm_num)
theorem B2323085 : Blo 1547471 2323085 := bbase (se 3 (by rfl) ⟨435578, by rfl⟩ : syracuseStep 2323085 = 871157) (by norm_num)
theorem B1741477 : Blo 1547471 1741477 := bbase (se 4 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 1741477 = 326527) (by norm_num)
theorem B2323109 : Blo 1547471 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B1569461 : Blo 1547471 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B2323133 : Blo 1547471 2323133 := bbase (se 3 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 2323133 = 871175) (by norm_num)
theorem B1741513 : Blo 1547471 1741513 := bbase (se 2 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 1741513 = 1306135) (by norm_num)
theorem B2323157 : Blo 1547471 2323157 := bbase (se 7 (by rfl) ⟨27224, by rfl⟩ : syracuseStep 2323157 = 54449) (by norm_num)
theorem B7951061 : Blo 1547471 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B1741549 : Blo 1547471 1741549 := bbase (se 3 (by rfl) ⟨326540, by rfl⟩ : syracuseStep 1741549 = 653081) (by norm_num)
theorem B2323181 : Blo 1547471 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B1766137 : Blo 1547471 1766137 := bbase (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) (by norm_num)
theorem B2323205 : Blo 1547471 2323205 := bbase (se 4 (by rfl) ⟨217800, by rfl⟩ : syracuseStep 2323205 = 435601) (by norm_num)
theorem B1839881 : Blo 1547471 1839881 := bbase (se 2 (by rfl) ⟨689955, by rfl⟩ : syracuseStep 1839881 = 1379911) (by norm_num)
theorem B1741585 : Blo 1547471 1741585 := bbase (se 2 (by rfl) ⟨653094, by rfl⟩ : syracuseStep 1741585 = 1306189) (by norm_num)
theorem B2323229 : Blo 1547471 2323229 := bbase (se 3 (by rfl) ⟨435605, by rfl⟩ : syracuseStep 2323229 = 871211) (by norm_num)
theorem B5878565 : Blo 1547471 5878565 := bbase (se 4 (by rfl) ⟨551115, by rfl⟩ : syracuseStep 5878565 = 1102231) (by norm_num)
theorem B1741621 : Blo 1547471 1741621 := bbase (se 5 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 1741621 = 163277) (by norm_num)
theorem B2790197 : Blo 1547471 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B2323253 : Blo 1547471 2323253 := bbase (se 5 (by rfl) ⟨108902, by rfl⟩ : syracuseStep 2323253 = 217805) (by norm_num)
theorem B2323277 : Blo 1547471 2323277 := bbase (se 3 (by rfl) ⟨435614, by rfl⟩ : syracuseStep 2323277 = 871229) (by norm_num)
theorem B1741657 : Blo 1547471 1741657 := bbase (se 2 (by rfl) ⟨653121, by rfl⟩ : syracuseStep 1741657 = 1306243) (by norm_num)
theorem B2323301 : Blo 1547471 2323301 := bbase (se 4 (by rfl) ⟨217809, by rfl⟩ : syracuseStep 2323301 = 435619) (by norm_num)
theorem B2093933 : Blo 1547471 2093933 := bbase (se 3 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 2093933 = 785225) (by norm_num)
theorem B1741693 : Blo 1547471 1741693 := bbase (se 3 (by rfl) ⟨326567, by rfl⟩ : syracuseStep 1741693 = 653135) (by norm_num)
theorem B2323325 : Blo 1547471 2323325 := bbase (se 3 (by rfl) ⟨435623, by rfl⟩ : syracuseStep 2323325 = 871247) (by norm_num)
theorem B2323349 : Blo 1547471 2323349 := bbase (se 6 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 2323349 = 108907) (by norm_num)
theorem B1741729 : Blo 1547471 1741729 := bbase (se 2 (by rfl) ⟨653148, by rfl⟩ : syracuseStep 1741729 = 1306297) (by norm_num)
theorem B2323373 : Blo 1547471 2323373 := bbase (se 3 (by rfl) ⟨435632, by rfl⟩ : syracuseStep 2323373 = 871265) (by norm_num)
theorem B5223365 : Blo 1547471 5223365 := bbase (se 4 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 5223365 = 979381) (by norm_num)
theorem B3306437 : Blo 1547471 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B1741765 : Blo 1547471 1741765 := bbase (se 4 (by rfl) ⟨163290, by rfl⟩ : syracuseStep 1741765 = 326581) (by norm_num)
theorem B2323397 : Blo 1547471 2323397 := bbase (se 4 (by rfl) ⟨217818, by rfl⟩ : syracuseStep 2323397 = 435637) (by norm_num)
theorem B3920845 : Blo 1547471 3920845 := bbase (se 3 (by rfl) ⟨735158, by rfl⟩ : syracuseStep 3920845 = 1470317) (by norm_num)
theorem B1569745 : Blo 1547471 1569745 := bbase (se 2 (by rfl) ⟨588654, by rfl⟩ : syracuseStep 1569745 = 1177309) (by norm_num)
theorem B2323421 : Blo 1547471 2323421 := bbase (se 3 (by rfl) ⟨435641, by rfl⟩ : syracuseStep 2323421 = 871283) (by norm_num)
theorem B1741801 : Blo 1547471 1741801 := bbase (se 2 (by rfl) ⟨653175, by rfl⟩ : syracuseStep 1741801 = 1306351) (by norm_num)
theorem B2266093 : Blo 1547471 2266093 := bbase (se 3 (by rfl) ⟨424892, by rfl⟩ : syracuseStep 2266093 = 849785) (by norm_num)
theorem B2323445 : Blo 1547471 2323445 := bbase (se 5 (by rfl) ⟨108911, by rfl⟩ : syracuseStep 2323445 = 217823) (by norm_num)
theorem B1741837 : Blo 1547471 1741837 := bbase (se 3 (by rfl) ⟨326594, by rfl⟩ : syracuseStep 1741837 = 653189) (by norm_num)
theorem B2323469 : Blo 1547471 2323469 := bbase (se 3 (by rfl) ⟨435650, by rfl⟩ : syracuseStep 2323469 = 871301) (by norm_num)
theorem B2323493 : Blo 1547471 2323493 := bbase (se 4 (by rfl) ⟨217827, by rfl⟩ : syracuseStep 2323493 = 435655) (by norm_num)
theorem B1741873 : Blo 1547471 1741873 := bbase (se 2 (by rfl) ⟨653202, by rfl⟩ : syracuseStep 1741873 = 1306405) (by norm_num)
theorem B3306557 : Blo 1547471 3306557 := bbase (se 3 (by rfl) ⟨619979, by rfl⟩ : syracuseStep 3306557 = 1239959) (by norm_num)
theorem B2323517 : Blo 1547471 2323517 := bbase (se 3 (by rfl) ⟨435659, by rfl⟩ : syracuseStep 2323517 = 871319) (by norm_num)
theorem B3920957 : Blo 1547471 3920957 := bbase (se 3 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 3920957 = 1470359) (by norm_num)
theorem B1741909 : Blo 1547471 1741909 := bbase (se 8 (by rfl) ⟨10206, by rfl⟩ : syracuseStep 1741909 = 20413) (by norm_num)
theorem B2323541 : Blo 1547471 2323541 := bbase (se 8 (by rfl) ⟨13614, by rfl⟩ : syracuseStep 2323541 = 27229) (by norm_num)
theorem B1766497 : Blo 1547471 1766497 := bbase (se 2 (by rfl) ⟨662436, by rfl⟩ : syracuseStep 1766497 = 1324873) (by norm_num)
theorem B2323565 : Blo 1547471 2323565 := bbase (se 3 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 2323565 = 871337) (by norm_num)
theorem B1741945 : Blo 1547471 1741945 := bbase (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) (by norm_num)
theorem B2323589 : Blo 1547471 2323589 := bbase (se 4 (by rfl) ⟨217836, by rfl⟩ : syracuseStep 2323589 = 435673) (by norm_num)
theorem B1741981 : Blo 1547471 1741981 := bbase (se 3 (by rfl) ⟨326621, by rfl⟩ : syracuseStep 1741981 = 653243) (by norm_num)
theorem B2323613 : Blo 1547471 2323613 := bbase (se 3 (by rfl) ⟨435677, by rfl⟩ : syracuseStep 2323613 = 871355) (by norm_num)
theorem B2323637 : Blo 1547471 2323637 := bbase (se 5 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 2323637 = 217841) (by norm_num)
theorem B2938045 : Blo 1547471 2938045 := bbase (se 3 (by rfl) ⟨550883, by rfl⟩ : syracuseStep 2938045 = 1101767) (by norm_num)
theorem B1742017 : Blo 1547471 1742017 := bbase (se 2 (by rfl) ⟨653256, by rfl⟩ : syracuseStep 1742017 = 1306513) (by norm_num)
theorem B2323661 : Blo 1547471 2323661 := bbase (se 3 (by rfl) ⟨435686, by rfl⟩ : syracuseStep 2323661 = 871373) (by norm_num)
theorem B5584085 : Blo 1547471 5584085 := bbase (se 7 (by rfl) ⟨65438, by rfl⟩ : syracuseStep 5584085 = 130877) (by norm_num)
theorem B1742053 : Blo 1547471 1742053 := bbase (se 4 (by rfl) ⟨163317, by rfl⟩ : syracuseStep 1742053 = 326635) (by norm_num)
theorem B2323685 : Blo 1547471 2323685 := bbase (se 4 (by rfl) ⟨217845, by rfl⟩ : syracuseStep 2323685 = 435691) (by norm_num)
theorem B3921149 : Blo 1547471 3921149 := bbase (se 3 (by rfl) ⟨735215, by rfl⟩ : syracuseStep 3921149 = 1470431) (by norm_num)
theorem B2323709 : Blo 1547471 2323709 := bbase (se 3 (by rfl) ⟨435695, by rfl⟩ : syracuseStep 2323709 = 871391) (by norm_num)
theorem B1742089 : Blo 1547471 1742089 := bbase (se 2 (by rfl) ⟨653283, by rfl⟩ : syracuseStep 1742089 = 1306567) (by norm_num)
theorem B2323733 : Blo 1547471 2323733 := bbase (se 6 (by rfl) ⟨54462, by rfl⟩ : syracuseStep 2323733 = 108925) (by norm_num)
theorem B2479405 : Blo 1547471 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B1742125 : Blo 1547471 1742125 := bbase (se 3 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 1742125 = 653297) (by norm_num)
theorem B2323757 : Blo 1547471 2323757 := bbase (se 3 (by rfl) ⟨435704, by rfl⟩ : syracuseStep 2323757 = 871409) (by norm_num)
theorem B2323781 : Blo 1547471 2323781 := bbase (se 4 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 2323781 = 435709) (by norm_num)
theorem B2938189 : Blo 1547471 2938189 := bbase (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) (by norm_num)
theorem B1742161 : Blo 1547471 1742161 := bbase (se 2 (by rfl) ⟨653310, by rfl⟩ : syracuseStep 1742161 = 1306621) (by norm_num)
theorem B9925973 : Blo 1547471 9925973 := bbase (se 13 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 9925973 = 3635) (by norm_num)
theorem B2323805 : Blo 1547471 2323805 := bbase (se 3 (by rfl) ⟨435713, by rfl⟩ : syracuseStep 2323805 = 871427) (by norm_num)
theorem B5223797 : Blo 1547471 5223797 := bbase (se 5 (by rfl) ⟨244865, by rfl⟩ : syracuseStep 5223797 = 489731) (by norm_num)
theorem B1742197 : Blo 1547471 1742197 := bbase (se 5 (by rfl) ⟨81665, by rfl⟩ : syracuseStep 1742197 = 163331) (by norm_num)
theorem B2323829 : Blo 1547471 2323829 := bbase (se 5 (by rfl) ⟨108929, by rfl⟩ : syracuseStep 2323829 = 217859) (by norm_num)
theorem B2323853 : Blo 1547471 2323853 := bbase (se 3 (by rfl) ⟨435722, by rfl⟩ : syracuseStep 2323853 = 871445) (by norm_num)
theorem B1742233 : Blo 1547471 1742233 := bbase (se 2 (by rfl) ⟨653337, by rfl⟩ : syracuseStep 1742233 = 1306675) (by norm_num)
theorem B2323877 : Blo 1547471 2323877 := bbase (se 4 (by rfl) ⟨217863, by rfl⟩ : syracuseStep 2323877 = 435727) (by norm_num)
theorem B1742269 : Blo 1547471 1742269 := bbase (se 3 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 1742269 = 653351) (by norm_num)
theorem B2323901 : Blo 1547471 2323901 := bbase (se 3 (by rfl) ⟨435731, by rfl⟩ : syracuseStep 2323901 = 871463) (by norm_num)
theorem B2323925 : Blo 1547471 2323925 := bbase (se 7 (by rfl) ⟨27233, by rfl⟩ : syracuseStep 2323925 = 54467) (by norm_num)
theorem B1742305 : Blo 1547471 1742305 := bbase (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) (by norm_num)
theorem B2938349 : Blo 1547471 2938349 := bbase (se 3 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 2938349 = 1101881) (by norm_num)
theorem B2323949 : Blo 1547471 2323949 := bbase (se 3 (by rfl) ⟨435740, by rfl⟩ : syracuseStep 2323949 = 871481) (by norm_num)
theorem B6616565 : Blo 1547471 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B1742341 : Blo 1547471 1742341 := bbase (se 4 (by rfl) ⟨163344, by rfl⟩ : syracuseStep 1742341 = 326689) (by norm_num)
theorem B2323973 : Blo 1547471 2323973 := bbase (se 4 (by rfl) ⟨217872, by rfl⟩ : syracuseStep 2323973 = 435745) (by norm_num)
theorem B2323997 : Blo 1547471 2323997 := bbase (se 3 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 2323997 = 871499) (by norm_num)
theorem B1742377 : Blo 1547471 1742377 := bbase (se 2 (by rfl) ⟨653391, by rfl⟩ : syracuseStep 1742377 = 1306783) (by norm_num)
theorem B2324021 : Blo 1547471 2324021 := bbase (se 5 (by rfl) ⟨108938, by rfl⟩ : syracuseStep 2324021 = 217877) (by norm_num)
theorem B1742413 : Blo 1547471 1742413 := bbase (se 3 (by rfl) ⟨326702, by rfl⟩ : syracuseStep 1742413 = 653405) (by norm_num)
theorem B2324045 : Blo 1547471 2324045 := bbase (se 3 (by rfl) ⟨435758, by rfl⟩ : syracuseStep 2324045 = 871517) (by norm_num)
theorem B3921493 : Blo 1547471 3921493 := bbase (se 8 (by rfl) ⟨22977, by rfl⟩ : syracuseStep 3921493 = 45955) (by norm_num)
theorem B2324069 : Blo 1547471 2324069 := bbase (se 4 (by rfl) ⟨217881, by rfl⟩ : syracuseStep 2324069 = 435763) (by norm_num)
theorem B1742449 : Blo 1547471 1742449 := bbase (se 2 (by rfl) ⟨653418, by rfl⟩ : syracuseStep 1742449 = 1306837) (by norm_num)
theorem B2938493 : Blo 1547471 2938493 := bbase (se 3 (by rfl) ⟨550967, by rfl⟩ : syracuseStep 2938493 = 1101935) (by norm_num)
theorem B2324093 : Blo 1547471 2324093 := bbase (se 3 (by rfl) ⟨435767, by rfl⟩ : syracuseStep 2324093 = 871535) (by norm_num)
theorem B1742485 : Blo 1547471 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B2324117 : Blo 1547471 2324117 := bbase (se 6 (by rfl) ⟨54471, by rfl⟩ : syracuseStep 2324117 = 108943) (by norm_num)
theorem B2324141 : Blo 1547471 2324141 := bbase (se 3 (by rfl) ⟨435776, by rfl⟩ : syracuseStep 2324141 = 871553) (by norm_num)
theorem B3307189 : Blo 1547471 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B1742521 : Blo 1547471 1742521 := bbase (se 2 (by rfl) ⟨653445, by rfl⟩ : syracuseStep 1742521 = 1306891) (by norm_num)
theorem B5297861 : Blo 1547471 5297861 := bbase (se 4 (by rfl) ⟨496674, by rfl⟩ : syracuseStep 5297861 = 993349) (by norm_num)
theorem B3921605 : Blo 1547471 3921605 := bbase (se 4 (by rfl) ⟨367650, by rfl⟩ : syracuseStep 3921605 = 735301) (by norm_num)
theorem B2324165 : Blo 1547471 2324165 := bbase (se 4 (by rfl) ⟨217890, by rfl⟩ : syracuseStep 2324165 = 435781) (by norm_num)
theorem B7837397 : Blo 1547471 7837397 := bbase (se 7 (by rfl) ⟨91844, by rfl⟩ : syracuseStep 7837397 = 183689) (by norm_num)
theorem B1742557 : Blo 1547471 1742557 := bbase (se 3 (by rfl) ⟨326729, by rfl⟩ : syracuseStep 1742557 = 653459) (by norm_num)
theorem B2324189 : Blo 1547471 2324189 := bbase (se 3 (by rfl) ⟨435785, by rfl⟩ : syracuseStep 2324189 = 871571) (by norm_num)
theorem B2479853 : Blo 1547471 2479853 := bbase (se 3 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 2479853 = 929945) (by norm_num)
theorem B1742593 : Blo 1547471 1742593 := bbase (se 2 (by rfl) ⟨653472, by rfl⟩ : syracuseStep 1742593 = 1306945) (by norm_num)
theorem B4962053 : Blo 1547471 4962053 := bbase (se 4 (by rfl) ⟨465192, by rfl⟩ : syracuseStep 4962053 = 930385) (by norm_num)
theorem B1652501 : Blo 1547471 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B5224229 : Blo 1547471 5224229 := bbase (se 4 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 5224229 = 979543) (by norm_num)
theorem B1742629 : Blo 1547471 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B1742665 : Blo 1547471 1742665 := bbase (se 2 (by rfl) ⟨653499, by rfl⟩ : syracuseStep 1742665 = 1306999) (by norm_num)
theorem B2791277 : Blo 1547471 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B1742701 : Blo 1547471 1742701 := bbase (se 3 (by rfl) ⟨326756, by rfl⟩ : syracuseStep 1742701 = 653513) (by norm_num)
theorem B2234245 : Blo 1547471 2234245 := bbase (se 4 (by rfl) ⟨209460, by rfl⟩ : syracuseStep 2234245 = 418921) (by norm_num)
theorem B3921797 : Blo 1547471 3921797 := bbase (se 4 (by rfl) ⟨367668, by rfl⟩ : syracuseStep 3921797 = 735337) (by norm_num)
theorem B1742737 : Blo 1547471 1742737 := bbase (se 2 (by rfl) ⟨653526, by rfl⟩ : syracuseStep 1742737 = 1307053) (by norm_num)
theorem B25098133 : Blo 1547471 25098133 := bbase (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) (by norm_num)
theorem B2938781 : Blo 1547471 2938781 := bbase (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) (by norm_num)
theorem B2480053 : Blo 1547471 2480053 := bbase (se 5 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 2480053 = 232505) (by norm_num)
theorem B1742773 : Blo 1547471 1742773 := bbase (se 5 (by rfl) ⟨81692, by rfl⟩ : syracuseStep 1742773 = 163385) (by norm_num)
theorem B5879749 : Blo 1547471 5879749 := bbase (se 4 (by rfl) ⟨551226, by rfl⟩ : syracuseStep 5879749 = 1102453) (by norm_num)
theorem B1742809 : Blo 1547471 1742809 := bbase (se 2 (by rfl) ⟨653553, by rfl⟩ : syracuseStep 1742809 = 1307107) (by norm_num)
theorem B1742845 : Blo 1547471 1742845 := bbase (se 3 (by rfl) ⟨326783, by rfl⟩ : syracuseStep 1742845 = 653567) (by norm_num)
theorem B11155477 : Blo 1547471 11155477 := bbase (se 6 (by rfl) ⟨261456, by rfl⟩ : syracuseStep 11155477 = 522913) (by norm_num)
theorem B11761685 : Blo 1547471 11761685 := bbase (se 6 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 11761685 = 551329) (by norm_num)
theorem B1742881 : Blo 1547471 1742881 := bbase (se 2 (by rfl) ⟨653580, by rfl⟩ : syracuseStep 1742881 = 1307161) (by norm_num)
theorem B2938933 : Blo 1547471 2938933 := bbase (se 5 (by rfl) ⟨137762, by rfl⟩ : syracuseStep 2938933 = 275525) (by norm_num)
theorem B1742917 : Blo 1547471 1742917 := bbase (se 4 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 1742917 = 326797) (by norm_num)
theorem B1742953 : Blo 1547471 1742953 := bbase (se 2 (by rfl) ⟨653607, by rfl⟩ : syracuseStep 1742953 = 1307215) (by norm_num)
theorem B6797429 : Blo 1547471 6797429 := bbase (se 5 (by rfl) ⟨318629, by rfl⟩ : syracuseStep 6797429 = 637259) (by norm_num)
theorem B1742989 : Blo 1547471 1742989 := bbase (se 3 (by rfl) ⟨326810, by rfl⟩ : syracuseStep 1742989 = 653621) (by norm_num)
theorem B1743025 : Blo 1547471 1743025 := bbase (se 2 (by rfl) ⟨653634, by rfl⟩ : syracuseStep 1743025 = 1307269) (by norm_num)
theorem B2480309 : Blo 1547471 2480309 := bbase (se 5 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 2480309 = 232529) (by norm_num)
theorem B1652945 : Blo 1547471 1652945 := bbase (se 2 (by rfl) ⟨619854, by rfl⟩ : syracuseStep 1652945 = 1239709) (by norm_num)
theorem B5224661 : Blo 1547471 5224661 := bbase (se 7 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 5224661 = 122453) (by norm_num)
theorem B26458325 : Blo 1547471 26458325 := bbase (se 7 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 26458325 = 620117) (by norm_num)
theorem B1743061 : Blo 1547471 1743061 := bbase (se 7 (by rfl) ⟨20426, by rfl⟩ : syracuseStep 1743061 = 40853) (by norm_num)
theorem B5880053 : Blo 1547471 5880053 := bbase (se 5 (by rfl) ⟨275627, by rfl⟩ : syracuseStep 5880053 = 551255) (by norm_num)
theorem B1743097 : Blo 1547471 1743097 := bbase (se 2 (by rfl) ⟨653661, by rfl⟩ : syracuseStep 1743097 = 1307323) (by norm_num)
theorem B2611453 : Blo 1547471 2611453 := bbase (se 3 (by rfl) ⟨489647, by rfl⟩ : syracuseStep 2611453 = 979295) (by norm_num)
theorem B1653005 : Blo 1547471 1653005 := bbase (se 3 (by rfl) ⟨309938, by rfl⟩ : syracuseStep 1653005 = 619877) (by norm_num)
theorem B19855637 : Blo 1547471 19855637 := bbase (se 6 (by rfl) ⟨465366, by rfl⟩ : syracuseStep 19855637 = 930733) (by norm_num)
theorem B1743133 : Blo 1547471 1743133 := bbase (se 3 (by rfl) ⟨326837, by rfl⟩ : syracuseStep 1743133 = 653675) (by norm_num)
theorem B2611541 : Blo 1547471 2611541 := bbase (se 10 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 2611541 = 7651) (by norm_num)
theorem B2939237 : Blo 1547471 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B1653133 : Blo 1547471 1653133 := bbase (se 3 (by rfl) ⟨309962, by rfl⟩ : syracuseStep 1653133 = 619925) (by norm_num)
theorem B22329749 : Blo 1547471 22329749 := bbase (se 6 (by rfl) ⟨523353, by rfl⟩ : syracuseStep 22329749 = 1046707) (by norm_num)
theorem B11753909 : Blo 1547471 11753909 := bbase (se 5 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 11753909 = 1101929) (by norm_num)
theorem B2611669 : Blo 1547471 2611669 := bbase (se 7 (by rfl) ⟨30605, by rfl⟩ : syracuseStep 2611669 = 61211) (by norm_num)
theorem B4184581 : Blo 1547471 4184581 := bbase (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) (by norm_num)
theorem B2611757 : Blo 1547471 2611757 := bbase (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) (by norm_num)
theorem B3308077 : Blo 1547471 3308077 := bbase (se 3 (by rfl) ⟨620264, by rfl⟩ : syracuseStep 3308077 = 1240529) (by norm_num)
theorem B7944821 : Blo 1547471 7944821 := bbase (se 5 (by rfl) ⟨372413, by rfl⟩ : syracuseStep 7944821 = 744827) (by norm_num)
theorem B5225093 : Blo 1547471 5225093 := bbase (se 4 (by rfl) ⟨489852, by rfl⟩ : syracuseStep 5225093 = 979705) (by norm_num)
theorem B3308197 : Blo 1547471 3308197 := bbase (se 4 (by rfl) ⟨310143, by rfl⟩ : syracuseStep 3308197 = 620287) (by norm_num)
theorem B2611885 : Blo 1547471 2611885 := bbase (se 3 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 2611885 = 979457) (by norm_num)
theorem B16743125 : Blo 1547471 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B8821493 : Blo 1547471 8821493 := bbase (se 5 (by rfl) ⟨413507, by rfl⟩ : syracuseStep 8821493 = 827015) (by norm_num)
theorem B2611973 : Blo 1547471 2611973 := bbase (se 4 (by rfl) ⟨244872, by rfl⟩ : syracuseStep 2611973 = 489745) (by norm_num)
theorem B1653577 : Blo 1547471 1653577 := bbase (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) (by norm_num)
theorem B2612101 : Blo 1547471 2612101 := bbase (se 4 (by rfl) ⟨244884, by rfl⟩ : syracuseStep 2612101 = 489769) (by norm_num)
theorem B3308453 : Blo 1547471 3308453 := bbase (se 4 (by rfl) ⟨310167, by rfl⟩ : syracuseStep 3308453 = 620335) (by norm_num)
theorem B1653697 : Blo 1547471 1653697 := bbase (se 2 (by rfl) ⟨620136, by rfl⟩ : syracuseStep 1653697 = 1240273) (by norm_num)
theorem B7437253 : Blo 1547471 7437253 := bbase (se 4 (by rfl) ⟨697242, by rfl⟩ : syracuseStep 7437253 = 1394485) (by norm_num)
theorem B4709333 : Blo 1547471 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B2612189 : Blo 1547471 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B7838693 : Blo 1547471 7838693 := bbase (se 4 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 7838693 = 1469755) (by norm_num)
theorem B5225525 : Blo 1547471 5225525 := bbase (se 5 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 5225525 = 489893) (by norm_num)
theorem B2939989 : Blo 1547471 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B2612317 : Blo 1547471 2612317 := bbase (se 3 (by rfl) ⟨489809, by rfl⟩ : syracuseStep 2612317 = 979619) (by norm_num)
theorem B2612405 : Blo 1547471 2612405 := bbase (se 5 (by rfl) ⟨122456, by rfl⟩ : syracuseStep 2612405 = 244913) (by norm_num)
theorem B1653949 : Blo 1547471 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B1653953 : Blo 1547471 1653953 := bbase (se 2 (by rfl) ⟨620232, by rfl⟩ : syracuseStep 1653953 = 1240465) (by norm_num)
theorem B2940133 : Blo 1547471 2940133 := bbase (se 4 (by rfl) ⟨275637, by rfl⟩ : syracuseStep 2940133 = 551275) (by norm_num)
theorem B6618341 : Blo 1547471 6618341 := bbase (se 4 (by rfl) ⟨620469, by rfl⟩ : syracuseStep 6618341 = 1240939) (by norm_num)
theorem B2481437 : Blo 1547471 2481437 := bbase (se 3 (by rfl) ⟨465269, by rfl⟩ : syracuseStep 2481437 = 930539) (by norm_num)
theorem B2612533 : Blo 1547471 2612533 := bbase (se 5 (by rfl) ⟨122462, by rfl⟩ : syracuseStep 2612533 = 244925) (by norm_num)
theorem B4185445 : Blo 1547471 4185445 := bbase (se 4 (by rfl) ⟨392385, by rfl⟩ : syracuseStep 4185445 = 784771) (by norm_num)
theorem B2940293 : Blo 1547471 2940293 := bbase (se 4 (by rfl) ⟨275652, by rfl⟩ : syracuseStep 2940293 = 551305) (by norm_num)
theorem B2612621 : Blo 1547471 2612621 := bbase (se 3 (by rfl) ⟨489866, by rfl⟩ : syracuseStep 2612621 = 979733) (by norm_num)
theorem B6274469 : Blo 1547471 6274469 := bbase (se 4 (by rfl) ⟨588231, by rfl⟩ : syracuseStep 6274469 = 1176463) (by norm_num)
theorem B3628453 : Blo 1547471 3628453 := bbase (se 4 (by rfl) ⟨340167, by rfl⟩ : syracuseStep 3628453 = 680335) (by norm_num)
theorem B5225957 : Blo 1547471 5225957 := bbase (se 4 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 5225957 = 979867) (by norm_num)
theorem B5578229 : Blo 1547471 5578229 := bbase (se 5 (by rfl) ⟨261479, by rfl⟩ : syracuseStep 5578229 = 522959) (by norm_num)
theorem B2612749 : Blo 1547471 2612749 := bbase (se 3 (by rfl) ⟨489890, by rfl⟩ : syracuseStep 2612749 = 979781) (by norm_num)
theorem B2940437 : Blo 1547471 2940437 := bbase (se 6 (by rfl) ⟨68916, by rfl⟩ : syracuseStep 2940437 = 137833) (by norm_num)
theorem B1859117 : Blo 1547471 1859117 := bbase (se 3 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 1859117 = 697169) (by norm_num)
theorem B6610517 : Blo 1547471 6610517 := bbase (se 8 (by rfl) ⟨38733, by rfl⟩ : syracuseStep 6610517 = 77467) (by norm_num)
theorem B2612837 : Blo 1547471 2612837 := bbase (se 4 (by rfl) ⟨244953, by rfl⟩ : syracuseStep 2612837 = 489907) (by norm_num)
theorem B3718781 : Blo 1547471 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B2203357 : Blo 1547471 2203357 := bbase (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) (by norm_num)
theorem B2612965 : Blo 1547471 2612965 := bbase (se 4 (by rfl) ⟨244965, by rfl⟩ : syracuseStep 2612965 = 489931) (by norm_num)
theorem B1654517 : Blo 1547471 1654517 := bbase (se 5 (by rfl) ⟨77555, by rfl⟩ : syracuseStep 1654517 = 155111) (by norm_num)
theorem B3399421 : Blo 1547471 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B2481949 : Blo 1547471 2481949 := bbase (se 3 (by rfl) ⟨465365, by rfl⟩ : syracuseStep 2481949 = 930731) (by norm_num)
theorem B2940725 : Blo 1547471 2940725 := bbase (se 5 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 2940725 = 275693) (by norm_num)
theorem B3718973 : Blo 1547471 3718973 := bbase (se 3 (by rfl) ⟨697307, by rfl⟩ : syracuseStep 3718973 = 1394615) (by norm_num)
theorem B2613053 : Blo 1547471 2613053 := bbase (se 3 (by rfl) ⟨489947, by rfl⟩ : syracuseStep 2613053 = 979895) (by norm_num)
theorem B5226389 : Blo 1547471 5226389 := bbase (se 6 (by rfl) ⟨122493, by rfl⟩ : syracuseStep 5226389 = 244987) (by norm_num)
theorem B2613181 : Blo 1547471 2613181 := bbase (se 3 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 2613181 = 979943) (by norm_num)
theorem B2940877 : Blo 1547471 2940877 := bbase (se 3 (by rfl) ⟨551414, by rfl⟩ : syracuseStep 2940877 = 1102829) (by norm_num)
theorem B44629973 : Blo 1547471 44629973 := bbase (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) (by norm_num)
theorem B1548291 : Blo 1547471 1548291 := bstep (se 1 (by rfl) ⟨1161218, by rfl⟩ : syracuseStep 1548291 = 2322437) B2322437
theorem B1548307 : Blo 1547471 1548307 := bstep (se 1 (by rfl) ⟨1161230, by rfl⟩ : syracuseStep 1548307 = 2322461) B2322461
theorem B4136995 : Blo 1547471 4136995 := bstep (se 1 (by rfl) ⟨3102746, by rfl⟩ : syracuseStep 4136995 = 6205493) B6205493
theorem B1548323 : Blo 1547471 1548323 := bstep (se 1 (by rfl) ⟨1161242, by rfl⟩ : syracuseStep 1548323 = 2322485) B2322485
theorem B2203699 : Blo 1547471 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B1548339 : Blo 1547471 1548339 := bstep (se 1 (by rfl) ⟨1161254, by rfl⟩ : syracuseStep 1548339 = 2322509) B2322509
theorem B2121779 : Blo 1547471 2121779 := bstep (se 1 (by rfl) ⟨1591334, by rfl⟩ : syracuseStep 2121779 = 3182669) B3182669
theorem B1548355 : Blo 1547471 1548355 := bstep (se 1 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 1548355 = 2322533) B2322533
theorem B1548371 : Blo 1547471 1548371 := bstep (se 1 (by rfl) ⟨1161278, by rfl⟩ : syracuseStep 1548371 = 2322557) B2322557
theorem B6275171 : Blo 1547471 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B1548387 : Blo 1547471 1548387 := bstep (se 1 (by rfl) ⟨1161290, by rfl⟩ : syracuseStep 1548387 = 2322581) B2322581
theorem B5226605 : Blo 1547471 5226605 := bstep (se 3 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 5226605 = 1959977) B1959977
theorem B1548403 : Blo 1547471 1548403 := bstep (se 1 (by rfl) ⟨1161302, by rfl⟩ : syracuseStep 1548403 = 2322605) B2322605
theorem B2613377 : Blo 1547471 2613377 := bstep (se 2 (by rfl) ⟨980016, by rfl⟩ : syracuseStep 2613377 = 1960033) B1960033
theorem B1548419 : Blo 1547471 1548419 := bstep (se 1 (by rfl) ⟨1161314, by rfl⟩ : syracuseStep 1548419 = 2322629) B2322629
theorem B5881997 : Blo 1547471 5881997 := bstep (se 3 (by rfl) ⟨1102874, by rfl⟩ : syracuseStep 5881997 = 2205749) B2205749
theorem B1548435 : Blo 1547471 1548435 := bstep (se 1 (by rfl) ⟨1161326, by rfl⟩ : syracuseStep 1548435 = 2322653) B2322653
theorem B1548451 : Blo 1547471 1548451 := bstep (se 1 (by rfl) ⟨1161338, by rfl⟩ : syracuseStep 1548451 = 2322677) B2322677
theorem B5226659 : Blo 1547471 5226659 := bstep (se 1 (by rfl) ⟨3919994, by rfl⟩ : syracuseStep 5226659 = 7839989) B7839989
theorem B2941105 : Blo 1547471 2941105 := bstep (se 2 (by rfl) ⟨1102914, by rfl⟩ : syracuseStep 2941105 = 2205829) B2205829
theorem B1548467 : Blo 1547471 1548467 := bstep (se 1 (by rfl) ⟨1161350, by rfl⟩ : syracuseStep 1548467 = 2322701) B2322701
theorem B1548483 : Blo 1547471 1548483 := bstep (se 1 (by rfl) ⟨1161362, by rfl⟩ : syracuseStep 1548483 = 2322725) B2322725
theorem B8372429 : Blo 1547471 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B1548499 : Blo 1547471 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B1548515 : Blo 1547471 1548515 := bstep (se 1 (by rfl) ⟨1161386, by rfl⟩ : syracuseStep 1548515 = 2322773) B2322773
theorem B1548531 : Blo 1547471 1548531 := bstep (se 1 (by rfl) ⟨1161398, by rfl⟩ : syracuseStep 1548531 = 2322797) B2322797
theorem B2613505 : Blo 1547471 2613505 := bstep (se 2 (by rfl) ⟨980064, by rfl⟩ : syracuseStep 2613505 = 1960129) B1960129
theorem B1548547 : Blo 1547471 1548547 := bstep (se 1 (by rfl) ⟨1161410, by rfl⟩ : syracuseStep 1548547 = 2322821) B2322821
theorem B1548563 : Blo 1547471 1548563 := bstep (se 1 (by rfl) ⟨1161422, by rfl⟩ : syracuseStep 1548563 = 2322845) B2322845
theorem B1548579 : Blo 1547471 1548579 := bstep (se 1 (by rfl) ⟨1161434, by rfl⟩ : syracuseStep 1548579 = 2322869) B2322869
theorem B2613539 : Blo 1547471 2613539 := bstep (se 1 (by rfl) ⟨1960154, by rfl⟩ : syracuseStep 2613539 = 3920309) B3920309
theorem B1548595 : Blo 1547471 1548595 := bstep (se 1 (by rfl) ⟨1161446, by rfl⟩ : syracuseStep 1548595 = 2322893) B2322893
theorem B35742005 : Blo 1547471 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B1548611 : Blo 1547471 1548611 := bstep (se 1 (by rfl) ⟨1161458, by rfl⟩ : syracuseStep 1548611 = 2322917) B2322917
theorem B3481937 : Blo 1547471 3481937 := bstep (se 2 (by rfl) ⟨1305726, by rfl⟩ : syracuseStep 3481937 = 2611453) B2611453
theorem B2941265 : Blo 1547471 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B1548627 : Blo 1547471 1548627 := bstep (se 1 (by rfl) ⟨1161470, by rfl⟩ : syracuseStep 1548627 = 2322941) B2322941
theorem B3481955 : Blo 1547471 3481955 := bstep (se 1 (by rfl) ⟨2611466, by rfl⟩ : syracuseStep 3481955 = 5222933) B5222933
theorem B1548643 : Blo 1547471 1548643 := bstep (se 1 (by rfl) ⟨1161482, by rfl⟩ : syracuseStep 1548643 = 2322965) B2322965
theorem B1548659 : Blo 1547471 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B1548675 : Blo 1547471 1548675 := bstep (se 1 (by rfl) ⟨1161506, by rfl⟩ : syracuseStep 1548675 = 2323013) B2323013
theorem B18841997 : Blo 1547471 18841997 := bstep (se 3 (by rfl) ⟨3532874, by rfl⟩ : syracuseStep 18841997 = 7065749) B7065749
theorem B1548691 : Blo 1547471 1548691 := bstep (se 1 (by rfl) ⟨1161518, by rfl⟩ : syracuseStep 1548691 = 2323037) B2323037
theorem B1548707 : Blo 1547471 1548707 := bstep (se 1 (by rfl) ⟨1161530, by rfl⟩ : syracuseStep 1548707 = 2323061) B2323061
theorem B2613667 : Blo 1547471 2613667 := bstep (se 1 (by rfl) ⟨1960250, by rfl⟩ : syracuseStep 2613667 = 3920501) B3920501
theorem B5226929 : Blo 1547471 5226929 := bstep (se 2 (by rfl) ⟨1960098, by rfl⟩ : syracuseStep 5226929 = 3920197) B3920197
theorem B1548723 : Blo 1547471 1548723 := bstep (se 1 (by rfl) ⟨1161542, by rfl⟩ : syracuseStep 1548723 = 2323085) B2323085
theorem B1548739 : Blo 1547471 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1548755 : Blo 1547471 1548755 := bstep (se 1 (by rfl) ⟨1161566, by rfl⟩ : syracuseStep 1548755 = 2323133) B2323133
theorem B1548771 : Blo 1547471 1548771 := bstep (se 1 (by rfl) ⟨1161578, by rfl⟩ : syracuseStep 1548771 = 2323157) B2323157
theorem B1548787 : Blo 1547471 1548787 := bstep (se 1 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 1548787 = 2323181) B2323181
theorem B1548803 : Blo 1547471 1548803 := bstep (se 1 (by rfl) ⟨1161602, by rfl⟩ : syracuseStep 1548803 = 2323205) B2323205
theorem B2204177 : Blo 1547471 2204177 := bstep (se 2 (by rfl) ⟨826566, by rfl⟩ : syracuseStep 2204177 = 1653133) B1653133
theorem B1548819 : Blo 1547471 1548819 := bstep (se 1 (by rfl) ⟨1161614, by rfl⟩ : syracuseStep 1548819 = 2323229) B2323229
theorem B1860131 : Blo 1547471 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B1548835 : Blo 1547471 1548835 := bstep (se 1 (by rfl) ⟨1161626, by rfl⟩ : syracuseStep 1548835 = 2323253) B2323253
theorem B4407853 : Blo 1547471 4407853 := bstep (se 3 (by rfl) ⟨826472, by rfl⟩ : syracuseStep 4407853 = 1652945) B1652945
theorem B2613809 : Blo 1547471 2613809 := bstep (se 2 (by rfl) ⟨980178, by rfl⟩ : syracuseStep 2613809 = 1960357) B1960357
theorem B1548851 : Blo 1547471 1548851 := bstep (se 1 (by rfl) ⟨1161638, by rfl⟩ : syracuseStep 1548851 = 2323277) B2323277
theorem B1548867 : Blo 1547471 1548867 := bstep (se 1 (by rfl) ⟨1161650, by rfl⟩ : syracuseStep 1548867 = 2323301) B2323301
theorem B1548883 : Blo 1547471 1548883 := bstep (se 1 (by rfl) ⟨1161662, by rfl⟩ : syracuseStep 1548883 = 2323325) B2323325
theorem B1548899 : Blo 1547471 1548899 := bstep (se 1 (by rfl) ⟨1161674, by rfl⟩ : syracuseStep 1548899 = 2323349) B2323349
theorem B3482225 : Blo 1547471 3482225 := bstep (se 2 (by rfl) ⟨1305834, by rfl⟩ : syracuseStep 3482225 = 2611669) B2611669
theorem B1548915 : Blo 1547471 1548915 := bstep (se 1 (by rfl) ⟨1161686, by rfl⟩ : syracuseStep 1548915 = 2323373) B2323373
theorem B3482243 : Blo 1547471 3482243 := bstep (se 1 (by rfl) ⟨2611682, by rfl⟩ : syracuseStep 3482243 = 5223365) B5223365
theorem B2204291 : Blo 1547471 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B1548931 : Blo 1547471 1548931 := bstep (se 1 (by rfl) ⟨1161698, by rfl⟩ : syracuseStep 1548931 = 2323397) B2323397
theorem B1548947 : Blo 1547471 1548947 := bstep (se 1 (by rfl) ⟨1161710, by rfl⟩ : syracuseStep 1548947 = 2323421) B2323421
theorem B1548963 : Blo 1547471 1548963 := bstep (se 1 (by rfl) ⟨1161722, by rfl⟩ : syracuseStep 1548963 = 2323445) B2323445
theorem B5579441 : Blo 1547471 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B3719857 : Blo 1547471 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B1548979 : Blo 1547471 1548979 := bstep (se 1 (by rfl) ⟨1161734, by rfl⟩ : syracuseStep 1548979 = 2323469) B2323469
theorem B2613937 : Blo 1547471 2613937 := bstep (se 2 (by rfl) ⟨980226, by rfl⟩ : syracuseStep 2613937 = 1960453) B1960453
theorem B1548995 : Blo 1547471 1548995 := bstep (se 1 (by rfl) ⟨1161746, by rfl⟩ : syracuseStep 1548995 = 2323493) B2323493
theorem B4408013 : Blo 1547471 4408013 := bstep (se 3 (by rfl) ⟨826502, by rfl⟩ : syracuseStep 4408013 = 1653005) B1653005
theorem B2204371 : Blo 1547471 2204371 := bstep (se 1 (by rfl) ⟨1653278, by rfl⟩ : syracuseStep 2204371 = 3306557) B3306557
theorem B1549011 : Blo 1547471 1549011 := bstep (se 1 (by rfl) ⟨1161758, by rfl⟩ : syracuseStep 1549011 = 2323517) B2323517
theorem B2613971 : Blo 1547471 2613971 := bstep (se 1 (by rfl) ⟨1960478, by rfl⟩ : syracuseStep 2613971 = 3920957) B3920957
theorem B1549027 : Blo 1547471 1549027 := bstep (se 1 (by rfl) ⟨1161770, by rfl⟩ : syracuseStep 1549027 = 2323541) B2323541
theorem B1549043 : Blo 1547471 1549043 := bstep (se 1 (by rfl) ⟨1161782, by rfl⟩ : syracuseStep 1549043 = 2323565) B2323565
theorem B1549059 : Blo 1547471 1549059 := bstep (se 1 (by rfl) ⟨1161794, by rfl⟩ : syracuseStep 1549059 = 2323589) B2323589
theorem B1549075 : Blo 1547471 1549075 := bstep (se 1 (by rfl) ⟨1161806, by rfl⟩ : syracuseStep 1549075 = 2323613) B2323613
theorem B1549091 : Blo 1547471 1549091 := bstep (se 1 (by rfl) ⟨1161818, by rfl⟩ : syracuseStep 1549091 = 2323637) B2323637
theorem B1549107 : Blo 1547471 1549107 := bstep (se 1 (by rfl) ⟨1161830, by rfl⟩ : syracuseStep 1549107 = 2323661) B2323661
theorem B1549123 : Blo 1547471 1549123 := bstep (se 1 (by rfl) ⟨1161842, by rfl⟩ : syracuseStep 1549123 = 2323685) B2323685
theorem B2614099 : Blo 1547471 2614099 := bstep (se 1 (by rfl) ⟨1960574, by rfl⟩ : syracuseStep 2614099 = 3921149) B3921149
theorem B1549139 : Blo 1547471 1549139 := bstep (se 1 (by rfl) ⟨1161854, by rfl⟩ : syracuseStep 1549139 = 2323709) B2323709
theorem B1549155 : Blo 1547471 1549155 := bstep (se 1 (by rfl) ⟨1161866, by rfl⟩ : syracuseStep 1549155 = 2323733) B2323733
theorem B1549171 : Blo 1547471 1549171 := bstep (se 1 (by rfl) ⟨1161878, by rfl⟩ : syracuseStep 1549171 = 2323757) B2323757
theorem B4408195 : Blo 1547471 4408195 := bstep (se 1 (by rfl) ⟨3306146, by rfl⟩ : syracuseStep 4408195 = 6612293) B6612293
theorem B1549187 : Blo 1547471 1549187 := bstep (se 1 (by rfl) ⟨1161890, by rfl⟩ : syracuseStep 1549187 = 2323781) B2323781
theorem B3482513 : Blo 1547471 3482513 := bstep (se 2 (by rfl) ⟨1305942, by rfl⟩ : syracuseStep 3482513 = 2611885) B2611885
theorem B1549203 : Blo 1547471 1549203 := bstep (se 1 (by rfl) ⟨1161902, by rfl⟩ : syracuseStep 1549203 = 2323805) B2323805
theorem B3482531 : Blo 1547471 3482531 := bstep (se 1 (by rfl) ⟨2611898, by rfl⟩ : syracuseStep 3482531 = 5223797) B5223797
theorem B1549219 : Blo 1547471 1549219 := bstep (se 1 (by rfl) ⟨1161914, by rfl⟩ : syracuseStep 1549219 = 2323829) B2323829
theorem B1549235 : Blo 1547471 1549235 := bstep (se 1 (by rfl) ⟨1161926, by rfl⟩ : syracuseStep 1549235 = 2323853) B2323853
theorem B1549251 : Blo 1547471 1549251 := bstep (se 1 (by rfl) ⟨1161938, by rfl⟩ : syracuseStep 1549251 = 2323877) B2323877
theorem B5227469 : Blo 1547471 5227469 := bstep (se 3 (by rfl) ⟨980150, by rfl⟩ : syracuseStep 5227469 = 1960301) B1960301
theorem B1549267 : Blo 1547471 1549267 := bstep (se 1 (by rfl) ⟨1161950, by rfl⟩ : syracuseStep 1549267 = 2323901) B2323901
theorem B2614241 : Blo 1547471 2614241 := bstep (se 2 (by rfl) ⟨980340, by rfl⟩ : syracuseStep 2614241 = 1960681) B1960681
theorem B1549283 : Blo 1547471 1549283 := bstep (se 1 (by rfl) ⟨1161962, by rfl⟩ : syracuseStep 1549283 = 2323925) B2323925
theorem B1958899 : Blo 1547471 1958899 := bstep (se 1 (by rfl) ⟨1469174, by rfl⟩ : syracuseStep 1958899 = 2938349) B2938349
theorem B1549299 : Blo 1547471 1549299 := bstep (se 1 (by rfl) ⟨1161974, by rfl⟩ : syracuseStep 1549299 = 2323949) B2323949
theorem B5227523 : Blo 1547471 5227523 := bstep (se 1 (by rfl) ⟨3920642, by rfl⟩ : syracuseStep 5227523 = 7841285) B7841285
theorem B1549315 : Blo 1547471 1549315 := bstep (se 1 (by rfl) ⟨1161986, by rfl⟩ : syracuseStep 1549315 = 2323973) B2323973
theorem B1549331 : Blo 1547471 1549331 := bstep (se 1 (by rfl) ⟨1161998, by rfl⟩ : syracuseStep 1549331 = 2323997) B2323997
theorem B1549347 : Blo 1547471 1549347 := bstep (se 1 (by rfl) ⟨1162010, by rfl⟩ : syracuseStep 1549347 = 2324021) B2324021
theorem B1549363 : Blo 1547471 1549363 := bstep (se 1 (by rfl) ⟨1162022, by rfl⟩ : syracuseStep 1549363 = 2324045) B2324045
theorem B1549379 : Blo 1547471 1549379 := bstep (se 1 (by rfl) ⟨1162034, by rfl⟩ : syracuseStep 1549379 = 2324069) B2324069
theorem B1958995 : Blo 1547471 1958995 := bstep (se 1 (by rfl) ⟨1469246, by rfl⟩ : syracuseStep 1958995 = 2938493) B2938493
theorem B1549395 : Blo 1547471 1549395 := bstep (se 1 (by rfl) ⟨1162046, by rfl⟩ : syracuseStep 1549395 = 2324093) B2324093
theorem B2614369 : Blo 1547471 2614369 := bstep (se 2 (by rfl) ⟨980388, by rfl⟩ : syracuseStep 2614369 = 1960777) B1960777
theorem B1549411 : Blo 1547471 1549411 := bstep (se 1 (by rfl) ⟨1162058, by rfl⟩ : syracuseStep 1549411 = 2324117) B2324117
theorem B1549427 : Blo 1547471 1549427 := bstep (se 1 (by rfl) ⟨1162070, by rfl⟩ : syracuseStep 1549427 = 2324141) B2324141
theorem B3531907 : Blo 1547471 3531907 := bstep (se 1 (by rfl) ⟨2648930, by rfl⟩ : syracuseStep 3531907 = 5297861) B5297861
theorem B2614403 : Blo 1547471 2614403 := bstep (se 1 (by rfl) ⟨1960802, by rfl⟩ : syracuseStep 2614403 = 3921605) B3921605
theorem B1549443 : Blo 1547471 1549443 := bstep (se 1 (by rfl) ⟨1162082, by rfl⟩ : syracuseStep 1549443 = 2324165) B2324165
theorem B1549459 : Blo 1547471 1549459 := bstep (se 1 (by rfl) ⟨1162094, by rfl⟩ : syracuseStep 1549459 = 2324189) B2324189
theorem B3482801 : Blo 1547471 3482801 := bstep (se 2 (by rfl) ⟨1306050, by rfl⟩ : syracuseStep 3482801 = 2612101) B2612101
theorem B3482819 : Blo 1547471 3482819 := bstep (se 1 (by rfl) ⟨2612114, by rfl⟩ : syracuseStep 3482819 = 5224229) B5224229
theorem B1860851 : Blo 1547471 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B2204929 : Blo 1547471 2204929 := bstep (se 2 (by rfl) ⟨826848, by rfl⟩ : syracuseStep 2204929 = 1653697) B1653697
theorem B2614531 : Blo 1547471 2614531 := bstep (se 1 (by rfl) ⟨1960898, by rfl⟩ : syracuseStep 2614531 = 3921797) B3921797
theorem B5227793 : Blo 1547471 5227793 := bstep (se 2 (by rfl) ⟨1960422, by rfl⟩ : syracuseStep 5227793 = 3920845) B3920845
theorem B7841123 : Blo 1547471 7841123 := bstep (se 1 (by rfl) ⟨5880842, by rfl⟩ : syracuseStep 7841123 = 11761685) B11761685
theorem B2614673 : Blo 1547471 2614673 := bstep (se 2 (by rfl) ⟨980502, by rfl⟩ : syracuseStep 2614673 = 1961005) B1961005
theorem B4531619 : Blo 1547471 4531619 := bstep (se 1 (by rfl) ⟨3398714, by rfl⟩ : syracuseStep 4531619 = 6797429) B6797429
theorem B4957645 : Blo 1547471 4957645 := bstep (se 3 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 4957645 = 1859117) B1859117
theorem B3483089 : Blo 1547471 3483089 := bstep (se 2 (by rfl) ⟨1306158, by rfl⟩ : syracuseStep 3483089 = 2612317) B2612317
theorem B3483107 : Blo 1547471 3483107 := bstep (se 1 (by rfl) ⟨2612330, by rfl⟩ : syracuseStep 3483107 = 5224661) B5224661
theorem B17638883 : Blo 1547471 17638883 := bstep (se 1 (by rfl) ⟨13229162, by rfl⟩ : syracuseStep 17638883 = 26458325) B26458325
theorem B1959491 : Blo 1547471 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B3917393 : Blo 1547471 3917393 := bstep (se 2 (by rfl) ⟨1469022, by rfl⟩ : syracuseStep 3917393 = 2938045) B2938045
theorem B14886499 : Blo 1547471 14886499 := bstep (se 1 (by rfl) ⟨11164874, by rfl⟩ : syracuseStep 14886499 = 22329749) B22329749
theorem B3917443 : Blo 1547471 3917443 := bstep (se 1 (by rfl) ⟨2938082, by rfl⟩ : syracuseStep 3917443 = 5876165) B5876165
theorem B4187825 : Blo 1547471 4187825 := bstep (se 2 (by rfl) ⟨1570434, by rfl⟩ : syracuseStep 4187825 = 3140869) B3140869
theorem B3483377 : Blo 1547471 3483377 := bstep (se 2 (by rfl) ⟨1306266, by rfl⟩ : syracuseStep 3483377 = 2612533) B2612533
theorem B3483395 : Blo 1547471 3483395 := bstep (se 1 (by rfl) ⟨2612546, by rfl⟩ : syracuseStep 3483395 = 5225093) B5225093
theorem B3917585 : Blo 1547471 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B5228333 : Blo 1547471 5228333 := bstep (se 3 (by rfl) ⟨980312, by rfl⟩ : syracuseStep 5228333 = 1960625) B1960625
theorem B5580593 : Blo 1547471 5580593 := bstep (se 2 (by rfl) ⟨2092722, by rfl⟩ : syracuseStep 5580593 = 4185445) B4185445
theorem B4187953 : Blo 1547471 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B11765573 : Blo 1547471 11765573 := bstep (se 4 (by rfl) ⟨1103022, by rfl⟩ : syracuseStep 11765573 = 2206045) B2206045
theorem B5228387 : Blo 1547471 5228387 := bstep (se 1 (by rfl) ⟨3921290, by rfl⟩ : syracuseStep 5228387 = 7842581) B7842581
theorem B2353025 : Blo 1547471 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B21202829 : Blo 1547471 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B2205635 : Blo 1547471 2205635 := bstep (se 1 (by rfl) ⟨1654226, by rfl⟩ : syracuseStep 2205635 = 3308453) B3308453
theorem B6612941 : Blo 1547471 6612941 := bstep (se 3 (by rfl) ⟨1239926, by rfl⟩ : syracuseStep 6612941 = 2479853) B2479853
theorem B3139555 : Blo 1547471 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B3483665 : Blo 1547471 3483665 := bstep (se 2 (by rfl) ⟨1306374, by rfl⟩ : syracuseStep 3483665 = 2612749) B2612749
theorem B3483683 : Blo 1547471 3483683 := bstep (se 1 (by rfl) ⟨2612762, by rfl⟩ : syracuseStep 3483683 = 5225525) B5225525
theorem B5228657 : Blo 1547471 5228657 := bstep (se 2 (by rfl) ⟨1960746, by rfl⟩ : syracuseStep 5228657 = 3921493) B3921493
theorem B7841933 : Blo 1547471 7841933 := bstep (se 3 (by rfl) ⟨1470362, by rfl⟩ : syracuseStep 7841933 = 2940725) B2940725
theorem B4409585 : Blo 1547471 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B1960195 : Blo 1547471 1960195 := bstep (se 1 (by rfl) ⟨1470146, by rfl⟩ : syracuseStep 1960195 = 2940293) B2940293
theorem B3483953 : Blo 1547471 3483953 := bstep (se 2 (by rfl) ⟨1306482, by rfl⟩ : syracuseStep 3483953 = 2612965) B2612965
theorem B3483971 : Blo 1547471 3483971 := bstep (se 1 (by rfl) ⟨2612978, by rfl⟩ : syracuseStep 3483971 = 5225957) B5225957
theorem B4532561 : Blo 1547471 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B1960291 : Blo 1547471 1960291 := bstep (se 1 (by rfl) ⟨1470218, by rfl⟩ : syracuseStep 1960291 = 2940437) B2940437
theorem B14125553 : Blo 1547471 14125553 := bstep (se 2 (by rfl) ⟨5297082, by rfl⟩ : syracuseStep 14125553 = 10594165) B10594165
theorem B3181123 : Blo 1547471 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B3484241 : Blo 1547471 3484241 := bstep (se 2 (by rfl) ⟨1306590, by rfl⟩ : syracuseStep 3484241 = 2613181) B2613181
theorem B3484259 : Blo 1547471 3484259 := bstep (se 1 (by rfl) ⟨2613194, by rfl⟩ : syracuseStep 3484259 = 5226389) B5226389
theorem B5229197 : Blo 1547471 5229197 := bstep (se 3 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 5229197 = 1960949) B1960949
theorem B5229251 : Blo 1547471 5229251 := bstep (se 1 (by rfl) ⟨3921938, by rfl⟩ : syracuseStep 5229251 = 7843877) B7843877
theorem B3918577 : Blo 1547471 3918577 := bstep (se 2 (by rfl) ⟨1469466, by rfl⟩ : syracuseStep 3918577 = 2938933) B2938933
theorem B2321219 : Blo 1547471 2321219 := bstep (se 1 (by rfl) ⟨1740914, by rfl⟩ : syracuseStep 2321219 = 3481829) B3481829
theorem B2091857 : Blo 1547471 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1960787 : Blo 1547471 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B2321249 : Blo 1547471 2321249 := bstep (se 2 (by rfl) ⟨870468, by rfl⟩ : syracuseStep 2321249 = 1740937) B1740937
theorem B7834481 : Blo 1547471 7834481 := bstep (se 2 (by rfl) ⟨2937930, by rfl⟩ : syracuseStep 7834481 = 5875861) B5875861
theorem B3484529 : Blo 1547471 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B2321267 : Blo 1547471 2321267 := bstep (se 1 (by rfl) ⟨1740950, by rfl⟩ : syracuseStep 2321267 = 3481901) B3481901
theorem B3484547 : Blo 1547471 3484547 := bstep (se 1 (by rfl) ⟨2613410, by rfl⟩ : syracuseStep 3484547 = 5226821) B5226821
theorem B5876621 : Blo 1547471 5876621 := bstep (se 3 (by rfl) ⟨1101866, by rfl⟩ : syracuseStep 5876621 = 2203733) B2203733
theorem B2321297 : Blo 1547471 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B3353489 : Blo 1547471 3353489 := bstep (se 2 (by rfl) ⟨1257558, by rfl⟩ : syracuseStep 3353489 = 2515117) B2515117
theorem B2321315 : Blo 1547471 2321315 := bstep (se 1 (by rfl) ⟨1740986, by rfl⟩ : syracuseStep 2321315 = 3481973) B3481973
theorem B2321345 : Blo 1547471 2321345 := bstep (se 2 (by rfl) ⟨870504, by rfl⟩ : syracuseStep 2321345 = 1741009) B1741009
theorem B2321363 : Blo 1547471 2321363 := bstep (se 1 (by rfl) ⟨1741022, by rfl⟩ : syracuseStep 2321363 = 3482045) B3482045
theorem B2321393 : Blo 1547471 2321393 := bstep (se 2 (by rfl) ⟨870522, by rfl⟩ : syracuseStep 2321393 = 1741045) B1741045
theorem B2321411 : Blo 1547471 2321411 := bstep (se 1 (by rfl) ⟨1741058, by rfl⟩ : syracuseStep 2321411 = 3482117) B3482117
theorem B3918851 : Blo 1547471 3918851 := bstep (se 1 (by rfl) ⟨2939138, by rfl⟩ : syracuseStep 3918851 = 5878277) B5878277
theorem B4959245 : Blo 1547471 4959245 := bstep (se 3 (by rfl) ⟨929858, by rfl⟩ : syracuseStep 4959245 = 1859717) B1859717
theorem B2321441 : Blo 1547471 2321441 := bstep (se 2 (by rfl) ⟨870540, by rfl⟩ : syracuseStep 2321441 = 1741081) B1741081
theorem B2321459 : Blo 1547471 2321459 := bstep (se 1 (by rfl) ⟨1741094, by rfl⟩ : syracuseStep 2321459 = 3482189) B3482189
theorem B2321489 : Blo 1547471 2321489 := bstep (se 2 (by rfl) ⟨870558, by rfl⟩ : syracuseStep 2321489 = 1741117) B1741117
theorem B3353681 : Blo 1547471 3353681 := bstep (se 2 (by rfl) ⟨1257630, by rfl⟩ : syracuseStep 3353681 = 2515261) B2515261
theorem B2321507 : Blo 1547471 2321507 := bstep (se 1 (by rfl) ⟨1741130, by rfl⟩ : syracuseStep 2321507 = 3482261) B3482261
theorem B3140707 : Blo 1547471 3140707 := bstep (se 1 (by rfl) ⟨2355530, by rfl⟩ : syracuseStep 3140707 = 4711061) B4711061
theorem B2321537 : Blo 1547471 2321537 := bstep (se 2 (by rfl) ⟨870576, by rfl⟩ : syracuseStep 2321537 = 1741153) B1741153
theorem B3484817 : Blo 1547471 3484817 := bstep (se 2 (by rfl) ⟨1306806, by rfl⟩ : syracuseStep 3484817 = 2613613) B2613613
theorem B2321555 : Blo 1547471 2321555 := bstep (se 1 (by rfl) ⟨1741166, by rfl⟩ : syracuseStep 2321555 = 3482333) B3482333
theorem B3484835 : Blo 1547471 3484835 := bstep (se 1 (by rfl) ⟨2613626, by rfl⟩ : syracuseStep 3484835 = 5227253) B5227253
theorem B4410541 : Blo 1547471 4410541 := bstep (se 3 (by rfl) ⟨826976, by rfl⟩ : syracuseStep 4410541 = 1653953) B1653953
theorem B2321585 : Blo 1547471 2321585 := bstep (se 2 (by rfl) ⟨870594, by rfl⟩ : syracuseStep 2321585 = 1741189) B1741189
theorem B8490161 : Blo 1547471 8490161 := bstep (se 2 (by rfl) ⟨3183810, by rfl⟩ : syracuseStep 8490161 = 6367621) B6367621
theorem B2321603 : Blo 1547471 2321603 := bstep (se 1 (by rfl) ⟨1741202, by rfl⟩ : syracuseStep 2321603 = 3482405) B3482405
theorem B3919043 : Blo 1547471 3919043 := bstep (se 1 (by rfl) ⟨2939282, by rfl⟩ : syracuseStep 3919043 = 5878565) B5878565
theorem B2321633 : Blo 1547471 2321633 := bstep (se 2 (by rfl) ⟨870612, by rfl⟩ : syracuseStep 2321633 = 1741225) B1741225
theorem B2321651 : Blo 1547471 2321651 := bstep (se 1 (by rfl) ⟨1741238, by rfl⟩ : syracuseStep 2321651 = 3482477) B3482477
theorem B2321681 : Blo 1547471 2321681 := bstep (se 2 (by rfl) ⟨870630, by rfl⟩ : syracuseStep 2321681 = 1741261) B1741261
theorem B2321699 : Blo 1547471 2321699 := bstep (se 1 (by rfl) ⟨1741274, by rfl⟩ : syracuseStep 2321699 = 3482549) B3482549
theorem B2321729 : Blo 1547471 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B2321747 : Blo 1547471 2321747 := bstep (se 1 (by rfl) ⟨1741310, by rfl⟩ : syracuseStep 2321747 = 3482621) B3482621
theorem B2321777 : Blo 1547471 2321777 := bstep (se 2 (by rfl) ⟨870666, by rfl⟩ : syracuseStep 2321777 = 1741333) B1741333
theorem B2321795 : Blo 1547471 2321795 := bstep (se 1 (by rfl) ⟨1741346, by rfl⟩ : syracuseStep 2321795 = 3482693) B3482693
theorem B4410769 : Blo 1547471 4410769 := bstep (se 2 (by rfl) ⟨1654038, by rfl⟩ : syracuseStep 4410769 = 3308077) B3308077
theorem B2321825 : Blo 1547471 2321825 := bstep (se 2 (by rfl) ⟨870684, by rfl⟩ : syracuseStep 2321825 = 1741369) B1741369
theorem B3485105 : Blo 1547471 3485105 := bstep (se 2 (by rfl) ⟨1306914, by rfl⟩ : syracuseStep 3485105 = 2613829) B2613829
theorem B2321843 : Blo 1547471 2321843 := bstep (se 1 (by rfl) ⟨1741382, by rfl⟩ : syracuseStep 2321843 = 3482765) B3482765
theorem B3485123 : Blo 1547471 3485123 := bstep (se 1 (by rfl) ⟨2613842, by rfl⟩ : syracuseStep 3485123 = 5227685) B5227685
theorem B2321873 : Blo 1547471 2321873 := bstep (se 2 (by rfl) ⟨870702, by rfl⟩ : syracuseStep 2321873 = 1741405) B1741405
theorem B2321891 : Blo 1547471 2321891 := bstep (se 1 (by rfl) ⟨1741418, by rfl⟩ : syracuseStep 2321891 = 3482837) B3482837
theorem B3722723 : Blo 1547471 3722723 := bstep (se 1 (by rfl) ⟨2792042, by rfl⟩ : syracuseStep 3722723 = 5584085) B5584085
theorem B2321921 : Blo 1547471 2321921 := bstep (se 2 (by rfl) ⟨870720, by rfl⟩ : syracuseStep 2321921 = 1741441) B1741441
theorem B2321939 : Blo 1547471 2321939 := bstep (se 1 (by rfl) ⟨1741454, by rfl⟩ : syracuseStep 2321939 = 3482909) B3482909
theorem B2788913 : Blo 1547471 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B2321969 : Blo 1547471 2321969 := bstep (se 2 (by rfl) ⟨870738, by rfl⟩ : syracuseStep 2321969 = 1741477) B1741477
theorem B4410929 : Blo 1547471 4410929 := bstep (se 2 (by rfl) ⟨1654098, by rfl⟩ : syracuseStep 4410929 = 3308197) B3308197
theorem B2321987 : Blo 1547471 2321987 := bstep (se 1 (by rfl) ⟨1741490, by rfl⟩ : syracuseStep 2321987 = 3482981) B3482981
theorem B2322017 : Blo 1547471 2322017 := bstep (se 2 (by rfl) ⟨870756, by rfl⟩ : syracuseStep 2322017 = 1741513) B1741513
theorem B2322035 : Blo 1547471 2322035 := bstep (se 1 (by rfl) ⟨1741526, by rfl⟩ : syracuseStep 2322035 = 3483053) B3483053
theorem B4025987 : Blo 1547471 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B2322065 : Blo 1547471 2322065 := bstep (se 2 (by rfl) ⟨870774, by rfl⟩ : syracuseStep 2322065 = 1741549) B1741549
theorem B2354849 : Blo 1547471 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B2322083 : Blo 1547471 2322083 := bstep (se 1 (by rfl) ⟨1741562, by rfl⟩ : syracuseStep 2322083 = 3483125) B3483125
theorem B4411043 : Blo 1547471 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B2322113 : Blo 1547471 2322113 := bstep (se 2 (by rfl) ⟨870792, by rfl⟩ : syracuseStep 2322113 = 1741585) B1741585
theorem B3485393 : Blo 1547471 3485393 := bstep (se 2 (by rfl) ⟨1307022, by rfl⟩ : syracuseStep 3485393 = 2614045) B2614045
theorem B2322131 : Blo 1547471 2322131 := bstep (se 1 (by rfl) ⟨1741598, by rfl⟩ : syracuseStep 2322131 = 3483197) B3483197
theorem B3485411 : Blo 1547471 3485411 := bstep (se 1 (by rfl) ⟨2614058, by rfl⟩ : syracuseStep 3485411 = 5228117) B5228117
theorem B2322161 : Blo 1547471 2322161 := bstep (se 2 (by rfl) ⟨870810, by rfl⟩ : syracuseStep 2322161 = 1741621) B1741621
theorem B2322179 : Blo 1547471 2322179 := bstep (se 1 (by rfl) ⟨1741634, by rfl⟩ : syracuseStep 2322179 = 3483269) B3483269
theorem B16731917 : Blo 1547471 16731917 := bstep (se 3 (by rfl) ⟨3137234, by rfl⟩ : syracuseStep 16731917 = 6274469) B6274469
theorem B2322209 : Blo 1547471 2322209 := bstep (se 2 (by rfl) ⟨870828, by rfl⟩ : syracuseStep 2322209 = 1741657) B1741657
theorem B2322227 : Blo 1547471 2322227 := bstep (se 1 (by rfl) ⟨1741670, by rfl⟩ : syracuseStep 2322227 = 3483341) B3483341
theorem B2789201 : Blo 1547471 2789201 := bstep (se 2 (by rfl) ⟨1045950, by rfl⟩ : syracuseStep 2789201 = 2091901) B2091901
theorem B2322257 : Blo 1547471 2322257 := bstep (se 2 (by rfl) ⟨870846, by rfl⟩ : syracuseStep 2322257 = 1741693) B1741693
theorem B2322275 : Blo 1547471 2322275 := bstep (se 1 (by rfl) ⟨1741706, by rfl⟩ : syracuseStep 2322275 = 3483413) B3483413
theorem B2322305 : Blo 1547471 2322305 := bstep (se 2 (by rfl) ⟨870864, by rfl⟩ : syracuseStep 2322305 = 1741729) B1741729
theorem B2322323 : Blo 1547471 2322323 := bstep (se 1 (by rfl) ⟨1741742, by rfl⟩ : syracuseStep 2322323 = 3483485) B3483485
theorem B9924515 : Blo 1547471 9924515 := bstep (se 1 (by rfl) ⟨7443386, by rfl⟩ : syracuseStep 9924515 = 14886773) B14886773
theorem B9916337 : Blo 1547471 9916337 := bstep (se 2 (by rfl) ⟨3718626, by rfl⟩ : syracuseStep 9916337 = 7437253) B7437253
theorem B2322353 : Blo 1547471 2322353 := bstep (se 2 (by rfl) ⟨870882, by rfl⟩ : syracuseStep 2322353 = 1741765) B1741765
theorem B2322371 : Blo 1547471 2322371 := bstep (se 1 (by rfl) ⟨1741778, by rfl⟩ : syracuseStep 2322371 = 3483557) B3483557
theorem B9416645 : Blo 1547471 9416645 := bstep (se 4 (by rfl) ⟨882810, by rfl⟩ : syracuseStep 9416645 = 1765621) B1765621
theorem B2322401 : Blo 1547471 2322401 := bstep (se 2 (by rfl) ⟨870900, by rfl⟩ : syracuseStep 2322401 = 1741801) B1741801
theorem B3485681 : Blo 1547471 3485681 := bstep (se 2 (by rfl) ⟨1307130, by rfl⟩ : syracuseStep 3485681 = 2614261) B2614261
theorem B2322419 : Blo 1547471 2322419 := bstep (se 1 (by rfl) ⟨1741814, by rfl⟩ : syracuseStep 2322419 = 3483629) B3483629
theorem B3485699 : Blo 1547471 3485699 := bstep (se 1 (by rfl) ⟨2614274, by rfl⟩ : syracuseStep 3485699 = 5228549) B5228549
theorem B2322449 : Blo 1547471 2322449 := bstep (se 2 (by rfl) ⟨870918, by rfl⟩ : syracuseStep 2322449 = 1741837) B1741837
theorem B2322467 : Blo 1547471 2322467 := bstep (se 1 (by rfl) ⟨1741850, by rfl⟩ : syracuseStep 2322467 = 3483701) B3483701
theorem B2789425 : Blo 1547471 2789425 := bstep (se 2 (by rfl) ⟨1046034, by rfl⟩ : syracuseStep 2789425 = 2092069) B2092069
theorem B2322497 : Blo 1547471 2322497 := bstep (se 2 (by rfl) ⟨870936, by rfl⟩ : syracuseStep 2322497 = 1741873) B1741873
theorem B2322515 : Blo 1547471 2322515 := bstep (se 1 (by rfl) ⟨1741886, by rfl⟩ : syracuseStep 2322515 = 3483773) B3483773
theorem B2789489 : Blo 1547471 2789489 := bstep (se 2 (by rfl) ⟨1046058, by rfl⟩ : syracuseStep 2789489 = 2092117) B2092117
theorem B2322545 : Blo 1547471 2322545 := bstep (se 2 (by rfl) ⟨870954, by rfl⟩ : syracuseStep 2322545 = 1741909) B1741909
theorem B3919985 : Blo 1547471 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2355329 : Blo 1547471 2355329 := bstep (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) B1766497
theorem B2322563 : Blo 1547471 2322563 := bstep (se 1 (by rfl) ⟨1741922, by rfl⟩ : syracuseStep 2322563 = 3483845) B3483845
theorem B2322593 : Blo 1547471 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B3920035 : Blo 1547471 3920035 := bstep (se 1 (by rfl) ⟨2940026, by rfl⟩ : syracuseStep 3920035 = 5880053) B5880053
theorem B2322611 : Blo 1547471 2322611 := bstep (se 1 (by rfl) ⟨1741958, by rfl⟩ : syracuseStep 2322611 = 3483917) B3483917
theorem B2322641 : Blo 1547471 2322641 := bstep (se 2 (by rfl) ⟨870990, by rfl⟩ : syracuseStep 2322641 = 1741981) B1741981
theorem B1741027 : Blo 1547471 1741027 := bstep (se 1 (by rfl) ⟨1305770, by rfl⟩ : syracuseStep 1741027 = 2611541) B2611541
theorem B2322659 : Blo 1547471 2322659 := bstep (se 1 (by rfl) ⟨1741994, by rfl⟩ : syracuseStep 2322659 = 3483989) B3483989
theorem B2322689 : Blo 1547471 2322689 := bstep (se 2 (by rfl) ⟨871008, by rfl⟩ : syracuseStep 2322689 = 1742017) B1742017
theorem B3485969 : Blo 1547471 3485969 := bstep (se 2 (by rfl) ⟨1307238, by rfl⟩ : syracuseStep 3485969 = 2614477) B2614477
theorem B2322707 : Blo 1547471 2322707 := bstep (se 1 (by rfl) ⟨1742030, by rfl⟩ : syracuseStep 2322707 = 3484061) B3484061
theorem B7835939 : Blo 1547471 7835939 := bstep (se 1 (by rfl) ⟨5876954, by rfl⟩ : syracuseStep 7835939 = 11753909) B11753909
theorem B3485987 : Blo 1547471 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B2322737 : Blo 1547471 2322737 := bstep (se 2 (by rfl) ⟨871026, by rfl⟩ : syracuseStep 2322737 = 1742053) B1742053
theorem B3920177 : Blo 1547471 3920177 := bstep (se 2 (by rfl) ⟨1470066, by rfl⟩ : syracuseStep 3920177 = 2940133) B2940133
theorem B2322755 : Blo 1547471 2322755 := bstep (se 1 (by rfl) ⟨1742066, by rfl⟩ : syracuseStep 2322755 = 3484133) B3484133
theorem B2322785 : Blo 1547471 2322785 := bstep (se 2 (by rfl) ⟨871044, by rfl⟩ : syracuseStep 2322785 = 1742089) B1742089
theorem B1741171 : Blo 1547471 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B2322803 : Blo 1547471 2322803 := bstep (se 1 (by rfl) ⟨1742102, by rfl⟩ : syracuseStep 2322803 = 3484205) B3484205
theorem B8819077 : Blo 1547471 8819077 := bstep (se 4 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 8819077 = 1653577) B1653577
theorem B3305873 : Blo 1547471 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2322833 : Blo 1547471 2322833 := bstep (se 2 (by rfl) ⟨871062, by rfl⟩ : syracuseStep 2322833 = 1742125) B1742125
theorem B5296547 : Blo 1547471 5296547 := bstep (se 1 (by rfl) ⟨3972410, by rfl⟩ : syracuseStep 5296547 = 7944821) B7944821
theorem B2322851 : Blo 1547471 2322851 := bstep (se 1 (by rfl) ⟨1742138, by rfl⟩ : syracuseStep 2322851 = 3484277) B3484277
theorem B2322881 : Blo 1547471 2322881 := bstep (se 2 (by rfl) ⟨871080, by rfl⟩ : syracuseStep 2322881 = 1742161) B1742161
theorem B2322899 : Blo 1547471 2322899 := bstep (se 1 (by rfl) ⟨1742174, by rfl⟩ : syracuseStep 2322899 = 3484349) B3484349
theorem B11162083 : Blo 1547471 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B2322929 : Blo 1547471 2322929 := bstep (se 2 (by rfl) ⟨871098, by rfl⟩ : syracuseStep 2322929 = 1742197) B1742197
theorem B1741315 : Blo 1547471 1741315 := bstep (se 1 (by rfl) ⟨1305986, by rfl⟩ : syracuseStep 1741315 = 2611973) B2611973
theorem B2322947 : Blo 1547471 2322947 := bstep (se 1 (by rfl) ⟨1742210, by rfl⟩ : syracuseStep 2322947 = 3484421) B3484421
theorem B2093587 : Blo 1547471 2093587 := bstep (se 1 (by rfl) ⟨1570190, by rfl⟩ : syracuseStep 2093587 = 3140381) B3140381
theorem B2322977 : Blo 1547471 2322977 := bstep (se 2 (by rfl) ⟨871116, by rfl⟩ : syracuseStep 2322977 = 1742233) B1742233
theorem B4837937 : Blo 1547471 4837937 := bstep (se 2 (by rfl) ⟨1814226, by rfl⟩ : syracuseStep 4837937 = 3628453) B3628453
theorem B3486257 : Blo 1547471 3486257 := bstep (se 2 (by rfl) ⟨1307346, by rfl⟩ : syracuseStep 3486257 = 2614693) B2614693
theorem B2322995 : Blo 1547471 2322995 := bstep (se 1 (by rfl) ⟨1742246, by rfl⟩ : syracuseStep 2322995 = 3484493) B3484493
theorem B16740917 : Blo 1547471 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B4960835 : Blo 1547471 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B3486275 : Blo 1547471 3486275 := bstep (se 1 (by rfl) ⟨2614706, by rfl⟩ : syracuseStep 3486275 = 5229413) B5229413
theorem B2323025 : Blo 1547471 2323025 := bstep (se 2 (by rfl) ⟨871134, by rfl⟩ : syracuseStep 2323025 = 1742269) B1742269
theorem B11760227 : Blo 1547471 11760227 := bstep (se 1 (by rfl) ⟨8820170, by rfl⟩ : syracuseStep 11760227 = 17640341) B17640341
theorem B2323043 : Blo 1547471 2323043 := bstep (se 1 (by rfl) ⟨1742282, by rfl⟩ : syracuseStep 2323043 = 3484565) B3484565
theorem B2323073 : Blo 1547471 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B4412045 : Blo 1547471 4412045 := bstep (se 3 (by rfl) ⟨827258, by rfl⟩ : syracuseStep 4412045 = 1654517) B1654517
theorem B1741459 : Blo 1547471 1741459 := bstep (se 1 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 1741459 = 2612189) B2612189
theorem B2323091 : Blo 1547471 2323091 := bstep (se 1 (by rfl) ⟨1742318, by rfl⟩ : syracuseStep 2323091 = 3484637) B3484637
theorem B2323121 : Blo 1547471 2323121 := bstep (se 2 (by rfl) ⟨871170, by rfl⟩ : syracuseStep 2323121 = 1742341) B1742341
theorem B2323139 : Blo 1547471 2323139 := bstep (se 1 (by rfl) ⟨1742354, by rfl⟩ : syracuseStep 2323139 = 3484709) B3484709
theorem B2323169 : Blo 1547471 2323169 := bstep (se 2 (by rfl) ⟨871188, by rfl⟩ : syracuseStep 2323169 = 1742377) B1742377
theorem B5223149 : Blo 1547471 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B5296877 : Blo 1547471 5296877 := bstep (se 3 (by rfl) ⟨993164, by rfl⟩ : syracuseStep 5296877 = 1986329) B1986329
theorem B2323187 : Blo 1547471 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B4961027 : Blo 1547471 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B2323217 : Blo 1547471 2323217 := bstep (se 2 (by rfl) ⟨871206, by rfl⟩ : syracuseStep 2323217 = 1742413) B1742413
theorem B5223203 : Blo 1547471 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B1741603 : Blo 1547471 1741603 := bstep (se 1 (by rfl) ⟨1306202, by rfl⟩ : syracuseStep 1741603 = 2612405) B2612405
theorem B2323235 : Blo 1547471 2323235 := bstep (se 1 (by rfl) ⟨1742426, by rfl⟩ : syracuseStep 2323235 = 3484853) B3484853
theorem B2323265 : Blo 1547471 2323265 := bstep (se 2 (by rfl) ⟨871224, by rfl⟩ : syracuseStep 2323265 = 1742449) B1742449
theorem B4412227 : Blo 1547471 4412227 := bstep (se 1 (by rfl) ⟨3309170, by rfl⟩ : syracuseStep 4412227 = 6618341) B6618341
theorem B9917261 : Blo 1547471 9917261 := bstep (se 3 (by rfl) ⟨1859486, by rfl⟩ : syracuseStep 9917261 = 3718973) B3718973
theorem B2323283 : Blo 1547471 2323283 := bstep (se 1 (by rfl) ⟨1742462, by rfl⟩ : syracuseStep 2323283 = 3484925) B3484925
theorem B2323313 : Blo 1547471 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B2323331 : Blo 1547471 2323331 := bstep (se 1 (by rfl) ⟨1742498, by rfl⟩ : syracuseStep 2323331 = 3484997) B3484997
theorem B2323361 : Blo 1547471 2323361 := bstep (se 2 (by rfl) ⟨871260, by rfl⟩ : syracuseStep 2323361 = 1742521) B1742521
theorem B1741747 : Blo 1547471 1741747 := bstep (se 1 (by rfl) ⟨1306310, by rfl⟩ : syracuseStep 1741747 = 2612621) B2612621
theorem B2323379 : Blo 1547471 2323379 := bstep (se 1 (by rfl) ⟨1742534, by rfl⟩ : syracuseStep 2323379 = 3485069) B3485069
theorem B5583821 : Blo 1547471 5583821 := bstep (se 3 (by rfl) ⟨1046966, by rfl⟩ : syracuseStep 5583821 = 2093933) B2093933
theorem B2937809 : Blo 1547471 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B2323409 : Blo 1547471 2323409 := bstep (se 2 (by rfl) ⟨871278, by rfl⟩ : syracuseStep 2323409 = 1742557) B1742557
theorem B2323427 : Blo 1547471 2323427 := bstep (se 1 (by rfl) ⟨1742570, by rfl⟩ : syracuseStep 2323427 = 3485141) B3485141
theorem B2323457 : Blo 1547471 2323457 := bstep (se 2 (by rfl) ⟨871296, by rfl⟩ : syracuseStep 2323457 = 1742593) B1742593
theorem B2323475 : Blo 1547471 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B5223473 : Blo 1547471 5223473 := bstep (se 2 (by rfl) ⟨1958802, by rfl⟩ : syracuseStep 5223473 = 3917605) B3917605
theorem B2323505 : Blo 1547471 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1741891 : Blo 1547471 1741891 := bstep (se 1 (by rfl) ⟨1306418, by rfl⟩ : syracuseStep 1741891 = 2612837) B2612837
theorem B2323523 : Blo 1547471 2323523 := bstep (se 1 (by rfl) ⟨1742642, by rfl⟩ : syracuseStep 2323523 = 3485285) B3485285
theorem B7836749 : Blo 1547471 7836749 := bstep (se 3 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 7836749 = 2938781) B2938781
theorem B2479187 : Blo 1547471 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B2323553 : Blo 1547471 2323553 := bstep (se 2 (by rfl) ⟨871332, by rfl⟩ : syracuseStep 2323553 = 1742665) B1742665
theorem B2323571 : Blo 1547471 2323571 := bstep (se 1 (by rfl) ⟨1742678, by rfl⟩ : syracuseStep 2323571 = 3485357) B3485357
theorem B2323601 : Blo 1547471 2323601 := bstep (se 2 (by rfl) ⟨871350, by rfl⟩ : syracuseStep 2323601 = 1742701) B1742701
theorem B8369315 : Blo 1547471 8369315 := bstep (se 1 (by rfl) ⟨6276986, by rfl⟩ : syracuseStep 8369315 = 12553973) B12553973
theorem B2323619 : Blo 1547471 2323619 := bstep (se 1 (by rfl) ⟨1742714, by rfl⟩ : syracuseStep 2323619 = 3485429) B3485429
theorem B7943345 : Blo 1547471 7943345 := bstep (se 2 (by rfl) ⟨2978754, by rfl⟩ : syracuseStep 7943345 = 5957509) B5957509
theorem B2978993 : Blo 1547471 2978993 := bstep (se 2 (by rfl) ⟨1117122, by rfl⟩ : syracuseStep 2978993 = 2234245) B2234245
theorem B2323649 : Blo 1547471 2323649 := bstep (se 2 (by rfl) ⟨871368, by rfl⟩ : syracuseStep 2323649 = 1742737) B1742737
theorem B1742035 : Blo 1547471 1742035 := bstep (se 1 (by rfl) ⟨1306526, by rfl⟩ : syracuseStep 1742035 = 2613053) B2613053
theorem B2323667 : Blo 1547471 2323667 := bstep (se 1 (by rfl) ⟨1742750, by rfl⟩ : syracuseStep 2323667 = 3485501) B3485501
theorem B3306737 : Blo 1547471 3306737 := bstep (se 2 (by rfl) ⟨1240026, by rfl⟩ : syracuseStep 3306737 = 2480053) B2480053
theorem B2323697 : Blo 1547471 2323697 := bstep (se 2 (by rfl) ⟨871386, by rfl⟩ : syracuseStep 2323697 = 1742773) B1742773
theorem B2323715 : Blo 1547471 2323715 := bstep (se 1 (by rfl) ⟨1742786, by rfl⟩ : syracuseStep 2323715 = 3485573) B3485573
theorem B3921169 : Blo 1547471 3921169 := bstep (se 2 (by rfl) ⟨1470438, by rfl⟩ : syracuseStep 3921169 = 2940877) B2940877
theorem B84800789 : Blo 1547471 84800789 := bstep (se 6 (by rfl) ⟨1987518, by rfl⟩ : syracuseStep 84800789 = 3975037) B3975037
theorem B2323745 : Blo 1547471 2323745 := bstep (se 2 (by rfl) ⟨871404, by rfl⟩ : syracuseStep 2323745 = 1742809) B1742809
theorem B2323763 : Blo 1547471 2323763 := bstep (se 1 (by rfl) ⟨1742822, by rfl⟩ : syracuseStep 2323763 = 3485645) B3485645
theorem B2323793 : Blo 1547471 2323793 := bstep (se 2 (by rfl) ⟨871422, by rfl⟩ : syracuseStep 2323793 = 1742845) B1742845
theorem B1742179 : Blo 1547471 1742179 := bstep (se 1 (by rfl) ⟨1306634, by rfl⟩ : syracuseStep 1742179 = 2613269) B2613269
theorem B2323811 : Blo 1547471 2323811 := bstep (se 1 (by rfl) ⟨1742858, by rfl⟩ : syracuseStep 2323811 = 3485717) B3485717
theorem B14873969 : Blo 1547471 14873969 := bstep (se 2 (by rfl) ⟨5577738, by rfl⟩ : syracuseStep 14873969 = 11155477) B11155477
theorem B2323841 : Blo 1547471 2323841 := bstep (se 2 (by rfl) ⟨871440, by rfl⟩ : syracuseStep 2323841 = 1742881) B1742881
theorem B4961681 : Blo 1547471 4961681 := bstep (se 2 (by rfl) ⟨1860630, by rfl⟩ : syracuseStep 4961681 = 3721261) B3721261
theorem B2323859 : Blo 1547471 2323859 := bstep (se 1 (by rfl) ⟨1742894, by rfl⟩ : syracuseStep 2323859 = 3485789) B3485789
theorem B2323889 : Blo 1547471 2323889 := bstep (se 2 (by rfl) ⟨871458, by rfl⟩ : syracuseStep 2323889 = 1742917) B1742917
theorem B2323907 : Blo 1547471 2323907 := bstep (se 1 (by rfl) ⟨1742930, by rfl⟩ : syracuseStep 2323907 = 3485861) B3485861
theorem B2323937 : Blo 1547471 2323937 := bstep (se 2 (by rfl) ⟨871476, by rfl⟩ : syracuseStep 2323937 = 1742953) B1742953
theorem B1742323 : Blo 1547471 1742323 := bstep (se 1 (by rfl) ⟨1306742, by rfl⟩ : syracuseStep 1742323 = 2613485) B2613485
theorem B2323955 : Blo 1547471 2323955 := bstep (se 1 (by rfl) ⟨1742966, by rfl⟩ : syracuseStep 2323955 = 3485933) B3485933
theorem B2323985 : Blo 1547471 2323985 := bstep (se 2 (by rfl) ⟨871494, by rfl⟩ : syracuseStep 2323985 = 1742989) B1742989
theorem B3921443 : Blo 1547471 3921443 := bstep (se 1 (by rfl) ⟨2941082, by rfl⟩ : syracuseStep 3921443 = 5882165) B5882165
theorem B2324003 : Blo 1547471 2324003 := bstep (se 1 (by rfl) ⟨1743002, by rfl⟩ : syracuseStep 2324003 = 3486005) B3486005
theorem B2324033 : Blo 1547471 2324033 := bstep (se 2 (by rfl) ⟨871512, by rfl⟩ : syracuseStep 2324033 = 1743025) B1743025
theorem B5224013 : Blo 1547471 5224013 := bstep (se 3 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 5224013 = 1959005) B1959005
theorem B2324051 : Blo 1547471 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B2324081 : Blo 1547471 2324081 := bstep (se 2 (by rfl) ⟨871530, by rfl⟩ : syracuseStep 2324081 = 1743061) B1743061
theorem B5224067 : Blo 1547471 5224067 := bstep (se 1 (by rfl) ⟨3918050, by rfl⟩ : syracuseStep 5224067 = 7836101) B7836101
theorem B1742467 : Blo 1547471 1742467 := bstep (se 1 (by rfl) ⟨1306850, by rfl⟩ : syracuseStep 1742467 = 2613701) B2613701
theorem B2324099 : Blo 1547471 2324099 := bstep (se 1 (by rfl) ⟨1743074, by rfl⟩ : syracuseStep 2324099 = 3486149) B3486149
theorem B2324129 : Blo 1547471 2324129 := bstep (se 2 (by rfl) ⟨871548, by rfl⟩ : syracuseStep 2324129 = 1743097) B1743097
theorem B2938531 : Blo 1547471 2938531 := bstep (se 1 (by rfl) ⟨2203898, by rfl⟩ : syracuseStep 2938531 = 4407797) B4407797
theorem B2324147 : Blo 1547471 2324147 := bstep (se 1 (by rfl) ⟨1743110, by rfl⟩ : syracuseStep 2324147 = 3486221) B3486221
theorem B2324177 : Blo 1547471 2324177 := bstep (se 2 (by rfl) ⟨871566, by rfl⟩ : syracuseStep 2324177 = 1743133) B1743133
theorem B3921635 : Blo 1547471 3921635 := bstep (se 1 (by rfl) ⟨2941226, by rfl⟩ : syracuseStep 3921635 = 5882453) B5882453
theorem B2324195 : Blo 1547471 2324195 := bstep (se 1 (by rfl) ⟨1743146, by rfl⟩ : syracuseStep 2324195 = 3486293) B3486293
theorem B5879537 : Blo 1547471 5879537 := bstep (se 2 (by rfl) ⟨2204826, by rfl⟩ : syracuseStep 5879537 = 4409653) B4409653
theorem B1742611 : Blo 1547471 1742611 := bstep (se 1 (by rfl) ⟨1306958, by rfl⟩ : syracuseStep 1742611 = 2613917) B2613917
theorem B11163491 : Blo 1547471 11163491 := bstep (se 1 (by rfl) ⟨8372618, by rfl⟩ : syracuseStep 11163491 = 16745237) B16745237
theorem B5224337 : Blo 1547471 5224337 := bstep (se 2 (by rfl) ⟨1959126, by rfl⟩ : syracuseStep 5224337 = 3918253) B3918253
theorem B2480033 : Blo 1547471 2480033 := bstep (se 2 (by rfl) ⟨930012, by rfl⟩ : syracuseStep 2480033 = 1860025) B1860025
theorem B1742755 : Blo 1547471 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B5027789 : Blo 1547471 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2480161 : Blo 1547471 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B1742899 : Blo 1547471 1742899 := bstep (se 1 (by rfl) ⟨1307174, by rfl⟩ : syracuseStep 1742899 = 2614349) B2614349
theorem B2480225 : Blo 1547471 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B2938979 : Blo 1547471 2938979 := bstep (se 1 (by rfl) ⟨2204234, by rfl⟩ : syracuseStep 2938979 = 4408469) B4408469
theorem B2611379 : Blo 1547471 2611379 := bstep (se 1 (by rfl) ⟨1958534, by rfl⟩ : syracuseStep 2611379 = 3917069) B3917069
theorem B1743043 : Blo 1547471 1743043 := bstep (se 1 (by rfl) ⟨1307282, by rfl⟩ : syracuseStep 1743043 = 2614565) B2614565
theorem B6617315 : Blo 1547471 6617315 := bstep (se 1 (by rfl) ⟨4962986, by rfl⟩ : syracuseStep 6617315 = 9925973) B9925973
theorem B2611507 : Blo 1547471 2611507 := bstep (se 1 (by rfl) ⟨1958630, by rfl⟩ : syracuseStep 2611507 = 3917261) B3917261
theorem B8821061 : Blo 1547471 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B2939267 : Blo 1547471 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B5224877 : Blo 1547471 5224877 := bstep (se 3 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 5224877 = 1959329) B1959329
theorem B2611649 : Blo 1547471 2611649 := bstep (se 2 (by rfl) ⟨979368, by rfl⟩ : syracuseStep 2611649 = 1958737) B1958737
theorem B5224931 : Blo 1547471 5224931 := bstep (se 1 (by rfl) ⟨3918698, by rfl⟩ : syracuseStep 5224931 = 7837397) B7837397
theorem B3308035 : Blo 1547471 3308035 := bstep (se 1 (by rfl) ⟨2481026, by rfl⟩ : syracuseStep 3308035 = 4962053) B4962053
theorem B2611777 : Blo 1547471 2611777 := bstep (se 2 (by rfl) ⟨979416, by rfl⟩ : syracuseStep 2611777 = 1958833) B1958833
theorem B2611811 : Blo 1547471 2611811 := bstep (se 1 (by rfl) ⟨1958858, by rfl⟩ : syracuseStep 2611811 = 3917717) B3917717
theorem B11164301 : Blo 1547471 11164301 := bstep (se 3 (by rfl) ⟨2093306, by rfl⟩ : syracuseStep 11164301 = 4186613) B4186613
theorem B3021457 : Blo 1547471 3021457 := bstep (se 2 (by rfl) ⟨1133046, by rfl⟩ : syracuseStep 3021457 = 2266093) B2266093
theorem B2792099 : Blo 1547471 2792099 := bstep (se 1 (by rfl) ⟨2094074, by rfl⟩ : syracuseStep 2792099 = 4188149) B4188149
theorem B2611939 : Blo 1547471 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B5225201 : Blo 1547471 5225201 := bstep (se 2 (by rfl) ⟨1959450, by rfl⟩ : syracuseStep 5225201 = 3918901) B3918901
theorem B1653539 : Blo 1547471 1653539 := bstep (se 1 (by rfl) ⟨1240154, by rfl⟩ : syracuseStep 1653539 = 2480309) B2480309
theorem B6708017 : Blo 1547471 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B13237091 : Blo 1547471 13237091 := bstep (se 1 (by rfl) ⟨9927818, by rfl⟩ : syracuseStep 13237091 = 19855637) B19855637
theorem B2612081 : Blo 1547471 2612081 := bstep (se 2 (by rfl) ⟨979530, by rfl⟩ : syracuseStep 2612081 = 1959061) B1959061
theorem B31783877 : Blo 1547471 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B13229027 : Blo 1547471 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B2612209 : Blo 1547471 2612209 := bstep (se 2 (by rfl) ⟨979578, by rfl⟩ : syracuseStep 2612209 = 1959157) B1959157
theorem B2612243 : Blo 1547471 2612243 := bstep (se 1 (by rfl) ⟨1959182, by rfl⟩ : syracuseStep 2612243 = 3918365) B3918365
theorem B2481283 : Blo 1547471 2481283 := bstep (se 1 (by rfl) ⟨1860962, by rfl⟩ : syracuseStep 2481283 = 3721925) B3721925
theorem B2612371 : Blo 1547471 2612371 := bstep (se 1 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 2612371 = 3918557) B3918557
theorem B1612963 : Blo 1547471 1612963 := bstep (se 1 (by rfl) ⟨1209722, by rfl⟩ : syracuseStep 1612963 = 2419445) B2419445
theorem B5880995 : Blo 1547471 5880995 := bstep (se 1 (by rfl) ⟨4410746, by rfl⟩ : syracuseStep 5880995 = 8821493) B8821493
theorem B1547475 : Blo 1547471 1547475 := bstep (se 1 (by rfl) ⟨1160606, by rfl⟩ : syracuseStep 1547475 = 2321213) B2321213
theorem B1547491 : Blo 1547471 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B1547507 : Blo 1547471 1547507 := bstep (se 1 (by rfl) ⟨1160630, by rfl⟩ : syracuseStep 1547507 = 2321261) B2321261
theorem B1547523 : Blo 1547471 1547523 := bstep (se 1 (by rfl) ⟨1160642, by rfl⟩ : syracuseStep 1547523 = 2321285) B2321285
theorem B2153731 : Blo 1547471 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B5225741 : Blo 1547471 5225741 := bstep (se 3 (by rfl) ⟨979826, by rfl⟩ : syracuseStep 5225741 = 1959653) B1959653
theorem B1547539 : Blo 1547471 1547539 := bstep (se 1 (by rfl) ⟨1160654, by rfl⟩ : syracuseStep 1547539 = 2321309) B2321309
theorem B2612513 : Blo 1547471 2612513 := bstep (se 2 (by rfl) ⟨979692, by rfl⟩ : syracuseStep 2612513 = 1959385) B1959385
theorem B1547555 : Blo 1547471 1547555 := bstep (se 1 (by rfl) ⟨1160666, by rfl⟩ : syracuseStep 1547555 = 2321333) B2321333
theorem B2940209 : Blo 1547471 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B1547571 : Blo 1547471 1547571 := bstep (se 1 (by rfl) ⟨1160678, by rfl⟩ : syracuseStep 1547571 = 2321357) B2321357
theorem B1547587 : Blo 1547471 1547587 := bstep (se 1 (by rfl) ⟨1160690, by rfl⟩ : syracuseStep 1547587 = 2321381) B2321381
theorem B5225795 : Blo 1547471 5225795 := bstep (se 1 (by rfl) ⟨3919346, by rfl⟩ : syracuseStep 5225795 = 7838693) B7838693
theorem B1547603 : Blo 1547471 1547603 := bstep (se 1 (by rfl) ⟨1160702, by rfl⟩ : syracuseStep 1547603 = 2321405) B2321405
theorem B1547619 : Blo 1547471 1547619 := bstep (se 1 (by rfl) ⟨1160714, by rfl⟩ : syracuseStep 1547619 = 2321429) B2321429
theorem B4906349 : Blo 1547471 4906349 := bstep (se 3 (by rfl) ⟨919940, by rfl⟩ : syracuseStep 4906349 = 1839881) B1839881
theorem B4963693 : Blo 1547471 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B1547635 : Blo 1547471 1547635 := bstep (se 1 (by rfl) ⟨1160726, by rfl⟩ : syracuseStep 1547635 = 2321453) B2321453
theorem B1547651 : Blo 1547471 1547651 := bstep (se 1 (by rfl) ⟨1160738, by rfl⟩ : syracuseStep 1547651 = 2321477) B2321477
theorem B4406669 : Blo 1547471 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B1547667 : Blo 1547471 1547667 := bstep (se 1 (by rfl) ⟨1160750, by rfl⟩ : syracuseStep 1547667 = 2321501) B2321501
theorem B2612641 : Blo 1547471 2612641 := bstep (se 2 (by rfl) ⟨979740, by rfl⟩ : syracuseStep 2612641 = 1959481) B1959481
theorem B1547683 : Blo 1547471 1547683 := bstep (se 1 (by rfl) ⟨1160762, by rfl⟩ : syracuseStep 1547683 = 2321525) B2321525
theorem B1547699 : Blo 1547471 1547699 := bstep (se 1 (by rfl) ⟨1160774, by rfl⟩ : syracuseStep 1547699 = 2321549) B2321549
theorem B1547715 : Blo 1547471 1547715 := bstep (se 1 (by rfl) ⟨1160786, by rfl⟩ : syracuseStep 1547715 = 2321573) B2321573
theorem B2612675 : Blo 1547471 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B4406737 : Blo 1547471 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B1547731 : Blo 1547471 1547731 := bstep (se 1 (by rfl) ⟨1160798, by rfl⟩ : syracuseStep 1547731 = 2321597) B2321597
theorem B1547747 : Blo 1547471 1547747 := bstep (se 1 (by rfl) ⟨1160810, by rfl⟩ : syracuseStep 1547747 = 2321621) B2321621
theorem B8052209 : Blo 1547471 8052209 := bstep (se 2 (by rfl) ⟨3019578, by rfl⟩ : syracuseStep 8052209 = 6039157) B6039157
theorem B1547763 : Blo 1547471 1547763 := bstep (se 1 (by rfl) ⟨1160822, by rfl⟩ : syracuseStep 1547763 = 2321645) B2321645
theorem B1547779 : Blo 1547471 1547779 := bstep (se 1 (by rfl) ⟨1160834, by rfl⟩ : syracuseStep 1547779 = 2321669) B2321669
theorem B1547795 : Blo 1547471 1547795 := bstep (se 1 (by rfl) ⟨1160846, by rfl⟩ : syracuseStep 1547795 = 2321693) B2321693
theorem B1654291 : Blo 1547471 1654291 := bstep (se 1 (by rfl) ⟨1240718, by rfl⟩ : syracuseStep 1654291 = 2481437) B2481437
theorem B1547811 : Blo 1547471 1547811 := bstep (se 1 (by rfl) ⟨1160858, by rfl⟩ : syracuseStep 1547811 = 2321717) B2321717
theorem B6610481 : Blo 1547471 6610481 := bstep (se 2 (by rfl) ⟨2478930, by rfl⟩ : syracuseStep 6610481 = 4957861) B4957861
theorem B1547827 : Blo 1547471 1547827 := bstep (se 1 (by rfl) ⟨1160870, by rfl⟩ : syracuseStep 1547827 = 2321741) B2321741
theorem B1547843 : Blo 1547471 1547843 := bstep (se 1 (by rfl) ⟨1160882, by rfl⟩ : syracuseStep 1547843 = 2321765) B2321765
theorem B2612803 : Blo 1547471 2612803 := bstep (se 1 (by rfl) ⟨1959602, by rfl⟩ : syracuseStep 2612803 = 3919205) B3919205
theorem B5226065 : Blo 1547471 5226065 := bstep (se 2 (by rfl) ⟨1959774, by rfl⟩ : syracuseStep 5226065 = 3919549) B3919549
theorem B1859155 : Blo 1547471 1859155 := bstep (se 1 (by rfl) ⟨1394366, by rfl⟩ : syracuseStep 1859155 = 2788733) B2788733
theorem B1547859 : Blo 1547471 1547859 := bstep (se 1 (by rfl) ⟨1160894, by rfl⟩ : syracuseStep 1547859 = 2321789) B2321789
theorem B1547875 : Blo 1547471 1547875 := bstep (se 1 (by rfl) ⟨1160906, by rfl⟩ : syracuseStep 1547875 = 2321813) B2321813
theorem B1547891 : Blo 1547471 1547891 := bstep (se 1 (by rfl) ⟨1160918, by rfl⟩ : syracuseStep 1547891 = 2321837) B2321837
theorem B2121331 : Blo 1547471 2121331 := bstep (se 1 (by rfl) ⟨1590998, by rfl⟩ : syracuseStep 2121331 = 3181997) B3181997
theorem B1547907 : Blo 1547471 1547907 := bstep (se 1 (by rfl) ⟨1160930, by rfl⟩ : syracuseStep 1547907 = 2321861) B2321861
theorem B1547923 : Blo 1547471 1547923 := bstep (se 1 (by rfl) ⟨1160942, by rfl⟩ : syracuseStep 1547923 = 2321885) B2321885
theorem B3718819 : Blo 1547471 3718819 := bstep (se 1 (by rfl) ⟨2789114, by rfl⟩ : syracuseStep 3718819 = 5578229) B5578229
theorem B1547939 : Blo 1547471 1547939 := bstep (se 1 (by rfl) ⟨1160954, by rfl⟩ : syracuseStep 1547939 = 2321909) B2321909
theorem B1547955 : Blo 1547471 1547955 := bstep (se 1 (by rfl) ⟨1160966, by rfl⟩ : syracuseStep 1547955 = 2321933) B2321933
theorem B1547971 : Blo 1547471 1547971 := bstep (se 1 (by rfl) ⟨1160978, by rfl⟩ : syracuseStep 1547971 = 2321957) B2321957
theorem B2612945 : Blo 1547471 2612945 := bstep (se 2 (by rfl) ⟨979854, by rfl⟩ : syracuseStep 2612945 = 1959709) B1959709
theorem B3309265 : Blo 1547471 3309265 := bstep (se 2 (by rfl) ⟨1240974, by rfl⟩ : syracuseStep 3309265 = 2481949) B2481949
theorem B1547987 : Blo 1547471 1547987 := bstep (se 1 (by rfl) ⟨1160990, by rfl⟩ : syracuseStep 1547987 = 2321981) B2321981
theorem B4407011 : Blo 1547471 4407011 := bstep (se 1 (by rfl) ⟨3305258, by rfl⟩ : syracuseStep 4407011 = 6610517) B6610517
theorem B1548003 : Blo 1547471 1548003 := bstep (se 1 (by rfl) ⟨1161002, by rfl⟩ : syracuseStep 1548003 = 2322005) B2322005
theorem B1548019 : Blo 1547471 1548019 := bstep (se 1 (by rfl) ⟨1161014, by rfl⟩ : syracuseStep 1548019 = 2322029) B2322029
theorem B1548035 : Blo 1547471 1548035 := bstep (se 1 (by rfl) ⟨1161026, by rfl⟩ : syracuseStep 1548035 = 2322053) B2322053
theorem B8371973 : Blo 1547471 8371973 := bstep (se 4 (by rfl) ⟨784872, by rfl⟩ : syracuseStep 8371973 = 1569745) B1569745
theorem B1548051 : Blo 1547471 1548051 := bstep (se 1 (by rfl) ⟨1161038, by rfl⟩ : syracuseStep 1548051 = 2322077) B2322077
theorem B1548067 : Blo 1547471 1548067 := bstep (se 1 (by rfl) ⟨1161050, by rfl⟩ : syracuseStep 1548067 = 2322101) B2322101
theorem B1548083 : Blo 1547471 1548083 := bstep (se 1 (by rfl) ⟨1161062, by rfl⟩ : syracuseStep 1548083 = 2322125) B2322125
theorem B1548099 : Blo 1547471 1548099 := bstep (se 1 (by rfl) ⟨1161074, by rfl⟩ : syracuseStep 1548099 = 2322149) B2322149
theorem B2613073 : Blo 1547471 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B1548115 : Blo 1547471 1548115 := bstep (se 1 (by rfl) ⟨1161086, by rfl⟩ : syracuseStep 1548115 = 2322173) B2322173
theorem B1548131 : Blo 1547471 1548131 := bstep (se 1 (by rfl) ⟨1161098, by rfl⟩ : syracuseStep 1548131 = 2322197) B2322197
theorem B33464177 : Blo 1547471 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B1548147 : Blo 1547471 1548147 := bstep (se 1 (by rfl) ⟨1161110, by rfl⟩ : syracuseStep 1548147 = 2322221) B2322221
theorem B2613107 : Blo 1547471 2613107 := bstep (se 1 (by rfl) ⟨1959830, by rfl⟩ : syracuseStep 2613107 = 3919661) B3919661
theorem B1548163 : Blo 1547471 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1548179 : Blo 1547471 1548179 := bstep (se 1 (by rfl) ⟨1161134, by rfl⟩ : syracuseStep 1548179 = 2322269) B2322269
theorem B1548195 : Blo 1547471 1548195 := bstep (se 1 (by rfl) ⟨1161146, by rfl⟩ : syracuseStep 1548195 = 2322293) B2322293
theorem B7839665 : Blo 1547471 7839665 := bstep (se 2 (by rfl) ⟨2939874, by rfl⟩ : syracuseStep 7839665 = 5879749) B5879749
theorem B1548211 : Blo 1547471 1548211 := bstep (se 1 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 1548211 = 2322317) B2322317
theorem B1548227 : Blo 1547471 1548227 := bstep (se 1 (by rfl) ⟨1161170, by rfl⟩ : syracuseStep 1548227 = 2322341) B2322341
theorem B1548243 : Blo 1547471 1548243 := bstep (se 1 (by rfl) ⟨1161182, by rfl⟩ : syracuseStep 1548243 = 2322365) B2322365
theorem B29753315 : Blo 1547471 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B1548259 : Blo 1547471 1548259 := bstep (se 1 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 1548259 = 2322389) B2322389
theorem B1548275 : Blo 1547471 1548275 := bstep (se 1 (by rfl) ⟨1161206, by rfl⟩ : syracuseStep 1548275 = 2322413) B2322413
theorem B2613235 : Blo 1547471 2613235 := bstep (se 1 (by rfl) ⟨1959926, by rfl⟩ : syracuseStep 2613235 = 3919853) B3919853
theorem B1548299 : Blo 1547471 1548299 := bstep (se 1 (by rfl) ⟨1161224, by rfl⟩ : syracuseStep 1548299 = 2322449) B2322449
theorem B1548311 : Blo 1547471 1548311 := bstep (se 1 (by rfl) ⟨1161233, by rfl⟩ : syracuseStep 1548311 = 2322467) B2322467
theorem B1548331 : Blo 1547471 1548331 := bstep (se 1 (by rfl) ⟨1161248, by rfl⟩ : syracuseStep 1548331 = 2322497) B2322497
theorem B1548343 : Blo 1547471 1548343 := bstep (se 1 (by rfl) ⟨1161257, by rfl⟩ : syracuseStep 1548343 = 2322515) B2322515
theorem B3719233 : Blo 1547471 3719233 := bstep (se 2 (by rfl) ⟨1394712, by rfl⟩ : syracuseStep 3719233 = 2789425) B2789425
theorem B1548363 : Blo 1547471 1548363 := bstep (se 1 (by rfl) ⟨1161272, by rfl⟩ : syracuseStep 1548363 = 2322545) B2322545
theorem B2613323 : Blo 1547471 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1548375 : Blo 1547471 1548375 := bstep (se 1 (by rfl) ⟨1161281, by rfl⟩ : syracuseStep 1548375 = 2322563) B2322563
theorem B11165797 : Blo 1547471 11165797 := bstep (se 4 (by rfl) ⟨1046793, by rfl⟩ : syracuseStep 11165797 = 2093587) B2093587
theorem B1548395 : Blo 1547471 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B1548407 : Blo 1547471 1548407 := bstep (se 1 (by rfl) ⟨1161305, by rfl⟩ : syracuseStep 1548407 = 2322611) B2322611
theorem B1548427 : Blo 1547471 1548427 := bstep (se 1 (by rfl) ⟨1161320, by rfl⟩ : syracuseStep 1548427 = 2322641) B2322641
theorem B1548439 : Blo 1547471 1548439 := bstep (se 1 (by rfl) ⟨1161329, by rfl⟩ : syracuseStep 1548439 = 2322659) B2322659
theorem B1548459 : Blo 1547471 1548459 := bstep (se 1 (by rfl) ⟨1161344, by rfl⟩ : syracuseStep 1548459 = 2322689) B2322689
theorem B1548471 : Blo 1547471 1548471 := bstep (se 1 (by rfl) ⟨1161353, by rfl⟩ : syracuseStep 1548471 = 2322707) B2322707
theorem B1548491 : Blo 1547471 1548491 := bstep (se 1 (by rfl) ⟨1161368, by rfl⟩ : syracuseStep 1548491 = 2322737) B2322737
theorem B2613451 : Blo 1547471 2613451 := bstep (se 1 (by rfl) ⟨1960088, by rfl⟩ : syracuseStep 2613451 = 3920177) B3920177
theorem B1548503 : Blo 1547471 1548503 := bstep (se 1 (by rfl) ⟨1161377, by rfl⟩ : syracuseStep 1548503 = 2322755) B2322755
theorem B5226713 : Blo 1547471 5226713 := bstep (se 2 (by rfl) ⟨1960017, by rfl⟩ : syracuseStep 5226713 = 3920035) B3920035
theorem B6611165 : Blo 1547471 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B1548523 : Blo 1547471 1548523 := bstep (se 1 (by rfl) ⟨1161392, by rfl⟩ : syracuseStep 1548523 = 2322785) B2322785
theorem B1548535 : Blo 1547471 1548535 := bstep (se 1 (by rfl) ⟨1161401, by rfl⟩ : syracuseStep 1548535 = 2322803) B2322803
theorem B1548555 : Blo 1547471 1548555 := bstep (se 1 (by rfl) ⟨1161416, by rfl⟩ : syracuseStep 1548555 = 2322833) B2322833
theorem B1548567 : Blo 1547471 1548567 := bstep (se 1 (by rfl) ⟨1161425, by rfl⟩ : syracuseStep 1548567 = 2322851) B2322851
theorem B1548587 : Blo 1547471 1548587 := bstep (se 1 (by rfl) ⟨1161440, by rfl⟩ : syracuseStep 1548587 = 2322881) B2322881
theorem B7438637 : Blo 1547471 7438637 := bstep (se 3 (by rfl) ⟨1394744, by rfl⟩ : syracuseStep 7438637 = 2789489) B2789489
theorem B1548599 : Blo 1547471 1548599 := bstep (se 1 (by rfl) ⟨1161449, by rfl⟩ : syracuseStep 1548599 = 2322899) B2322899
theorem B1548619 : Blo 1547471 1548619 := bstep (se 1 (by rfl) ⟨1161464, by rfl⟩ : syracuseStep 1548619 = 2322929) B2322929
theorem B1548631 : Blo 1547471 1548631 := bstep (se 1 (by rfl) ⟨1161473, by rfl⟩ : syracuseStep 1548631 = 2322947) B2322947
theorem B2613593 : Blo 1547471 2613593 := bstep (se 2 (by rfl) ⟨980097, by rfl⟩ : syracuseStep 2613593 = 1960195) B1960195
theorem B1548651 : Blo 1547471 1548651 := bstep (se 1 (by rfl) ⟨1161488, by rfl⟩ : syracuseStep 1548651 = 2322977) B2322977
theorem B1548663 : Blo 1547471 1548663 := bstep (se 1 (by rfl) ⟨1161497, by rfl⟩ : syracuseStep 1548663 = 2322995) B2322995
theorem B1548683 : Blo 1547471 1548683 := bstep (se 1 (by rfl) ⟨1161512, by rfl⟩ : syracuseStep 1548683 = 2323025) B2323025
theorem B7840151 : Blo 1547471 7840151 := bstep (se 1 (by rfl) ⟨5880113, by rfl⟩ : syracuseStep 7840151 = 11760227) B11760227
theorem B1548695 : Blo 1547471 1548695 := bstep (se 1 (by rfl) ⟨1161521, by rfl⟩ : syracuseStep 1548695 = 2323043) B2323043
theorem B3482009 : Blo 1547471 3482009 := bstep (se 2 (by rfl) ⟨1305753, by rfl⟩ : syracuseStep 3482009 = 2611507) B2611507
theorem B1548715 : Blo 1547471 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B2941363 : Blo 1547471 2941363 := bstep (se 1 (by rfl) ⟨2206022, by rfl⟩ : syracuseStep 2941363 = 4412045) B4412045
theorem B1548727 : Blo 1547471 1548727 := bstep (se 1 (by rfl) ⟨1161545, by rfl⟩ : syracuseStep 1548727 = 2323091) B2323091
theorem B3719627 : Blo 1547471 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B1548747 : Blo 1547471 1548747 := bstep (se 1 (by rfl) ⟨1161560, by rfl⟩ : syracuseStep 1548747 = 2323121) B2323121
theorem B1548759 : Blo 1547471 1548759 := bstep (se 1 (by rfl) ⟨1161569, by rfl⟩ : syracuseStep 1548759 = 2323139) B2323139
theorem B2613721 : Blo 1547471 2613721 := bstep (se 2 (by rfl) ⟨980145, by rfl⟩ : syracuseStep 2613721 = 1960291) B1960291
theorem B1548779 : Blo 1547471 1548779 := bstep (se 1 (by rfl) ⟨1161584, by rfl⟩ : syracuseStep 1548779 = 2323169) B2323169
theorem B3482099 : Blo 1547471 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B3531251 : Blo 1547471 3531251 := bstep (se 1 (by rfl) ⟨2648438, by rfl⟩ : syracuseStep 3531251 = 5296877) B5296877
theorem B1548791 : Blo 1547471 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B1548811 : Blo 1547471 1548811 := bstep (se 1 (by rfl) ⟨1161608, by rfl⟩ : syracuseStep 1548811 = 2323217) B2323217
theorem B3482135 : Blo 1547471 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B1548823 : Blo 1547471 1548823 := bstep (se 1 (by rfl) ⟨1161617, by rfl⟩ : syracuseStep 1548823 = 2323235) B2323235
theorem B1548843 : Blo 1547471 1548843 := bstep (se 1 (by rfl) ⟨1161632, by rfl⟩ : syracuseStep 1548843 = 2323265) B2323265
theorem B6611507 : Blo 1547471 6611507 := bstep (se 1 (by rfl) ⟨4958630, by rfl⟩ : syracuseStep 6611507 = 9917261) B9917261
theorem B1548855 : Blo 1547471 1548855 := bstep (se 1 (by rfl) ⟨1161641, by rfl⟩ : syracuseStep 1548855 = 2323283) B2323283
theorem B1548875 : Blo 1547471 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1548887 : Blo 1547471 1548887 := bstep (se 1 (by rfl) ⟨1161665, by rfl⟩ : syracuseStep 1548887 = 2323331) B2323331
theorem B17646173 : Blo 1547471 17646173 := bstep (se 3 (by rfl) ⟨3308657, by rfl⟩ : syracuseStep 17646173 = 6617315) B6617315
theorem B1548907 : Blo 1547471 1548907 := bstep (se 1 (by rfl) ⟨1161680, by rfl⟩ : syracuseStep 1548907 = 2323361) B2323361
theorem B1548919 : Blo 1547471 1548919 := bstep (se 1 (by rfl) ⟨1161689, by rfl⟩ : syracuseStep 1548919 = 2323379) B2323379
theorem B1548939 : Blo 1547471 1548939 := bstep (se 1 (by rfl) ⟨1161704, by rfl⟩ : syracuseStep 1548939 = 2323409) B2323409
theorem B1548951 : Blo 1547471 1548951 := bstep (se 1 (by rfl) ⟨1161713, by rfl⟩ : syracuseStep 1548951 = 2323427) B2323427
theorem B1548971 : Blo 1547471 1548971 := bstep (se 1 (by rfl) ⟨1161728, by rfl⟩ : syracuseStep 1548971 = 2323457) B2323457
theorem B1548983 : Blo 1547471 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B3482315 : Blo 1547471 3482315 := bstep (se 1 (by rfl) ⟨2611736, by rfl⟩ : syracuseStep 3482315 = 5223473) B5223473
theorem B1549003 : Blo 1547471 1549003 := bstep (se 1 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 1549003 = 2323505) B2323505
theorem B1549015 : Blo 1547471 1549015 := bstep (se 1 (by rfl) ⟨1161761, by rfl⟩ : syracuseStep 1549015 = 2323523) B2323523
theorem B1549035 : Blo 1547471 1549035 := bstep (se 1 (by rfl) ⟨1161776, by rfl⟩ : syracuseStep 1549035 = 2323553) B2323553
theorem B1549047 : Blo 1547471 1549047 := bstep (se 1 (by rfl) ⟨1161785, by rfl⟩ : syracuseStep 1549047 = 2323571) B2323571
theorem B3482369 : Blo 1547471 3482369 := bstep (se 2 (by rfl) ⟨1305888, by rfl⟩ : syracuseStep 3482369 = 2611777) B2611777
theorem B1549067 : Blo 1547471 1549067 := bstep (se 1 (by rfl) ⟨1161800, by rfl⟩ : syracuseStep 1549067 = 2323601) B2323601
theorem B5579543 : Blo 1547471 5579543 := bstep (se 1 (by rfl) ⟨4184657, by rfl⟩ : syracuseStep 5579543 = 8369315) B8369315
theorem B1549079 : Blo 1547471 1549079 := bstep (se 1 (by rfl) ⟨1161809, by rfl⟩ : syracuseStep 1549079 = 2323619) B2323619
theorem B1549099 : Blo 1547471 1549099 := bstep (se 1 (by rfl) ⟨1161824, by rfl⟩ : syracuseStep 1549099 = 2323649) B2323649
theorem B1549111 : Blo 1547471 1549111 := bstep (se 1 (by rfl) ⟨1161833, by rfl⟩ : syracuseStep 1549111 = 2323667) B2323667
theorem B2204491 : Blo 1547471 2204491 := bstep (se 1 (by rfl) ⟨1653368, by rfl⟩ : syracuseStep 2204491 = 3306737) B3306737
theorem B1549131 : Blo 1547471 1549131 := bstep (se 1 (by rfl) ⟨1161848, by rfl⟩ : syracuseStep 1549131 = 2323697) B2323697
theorem B1549143 : Blo 1547471 1549143 := bstep (se 1 (by rfl) ⟨1161857, by rfl⟩ : syracuseStep 1549143 = 2323715) B2323715
theorem B56533859 : Blo 1547471 56533859 := bstep (se 1 (by rfl) ⟨42400394, by rfl⟩ : syracuseStep 56533859 = 84800789) B84800789
theorem B1549163 : Blo 1547471 1549163 := bstep (se 1 (by rfl) ⟨1161872, by rfl⟩ : syracuseStep 1549163 = 2323745) B2323745
theorem B1549175 : Blo 1547471 1549175 := bstep (se 1 (by rfl) ⟨1161881, by rfl⟩ : syracuseStep 1549175 = 2323763) B2323763
theorem B1549195 : Blo 1547471 1549195 := bstep (se 1 (by rfl) ⟨1161896, by rfl⟩ : syracuseStep 1549195 = 2323793) B2323793
theorem B5227415 : Blo 1547471 5227415 := bstep (se 1 (by rfl) ⟨3920561, by rfl⟩ : syracuseStep 5227415 = 7841123) B7841123
theorem B1549207 : Blo 1547471 1549207 := bstep (se 1 (by rfl) ⟨1161905, by rfl⟩ : syracuseStep 1549207 = 2323811) B2323811
theorem B1549227 : Blo 1547471 1549227 := bstep (se 1 (by rfl) ⟨1161920, by rfl⟩ : syracuseStep 1549227 = 2323841) B2323841
theorem B1549239 : Blo 1547471 1549239 := bstep (se 1 (by rfl) ⟨1161929, by rfl⟩ : syracuseStep 1549239 = 2323859) B2323859
theorem B1549259 : Blo 1547471 1549259 := bstep (se 1 (by rfl) ⟨1161944, by rfl⟩ : syracuseStep 1549259 = 2323889) B2323889
theorem B1549271 : Blo 1547471 1549271 := bstep (se 1 (by rfl) ⟨1161953, by rfl⟩ : syracuseStep 1549271 = 2323907) B2323907
theorem B3482585 : Blo 1547471 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B1549291 : Blo 1547471 1549291 := bstep (se 1 (by rfl) ⟨1161968, by rfl⟩ : syracuseStep 1549291 = 2323937) B2323937
theorem B1549303 : Blo 1547471 1549303 := bstep (se 1 (by rfl) ⟨1161977, by rfl⟩ : syracuseStep 1549303 = 2323955) B2323955
theorem B1549323 : Blo 1547471 1549323 := bstep (se 1 (by rfl) ⟨1161992, by rfl⟩ : syracuseStep 1549323 = 2323985) B2323985
theorem B2614295 : Blo 1547471 2614295 := bstep (se 1 (by rfl) ⟨1960721, by rfl⟩ : syracuseStep 2614295 = 3921443) B3921443
theorem B1549335 : Blo 1547471 1549335 := bstep (se 1 (by rfl) ⟨1162001, by rfl⟩ : syracuseStep 1549335 = 2324003) B2324003
theorem B1549355 : Blo 1547471 1549355 := bstep (se 1 (by rfl) ⟨1162016, by rfl⟩ : syracuseStep 1549355 = 2324033) B2324033
theorem B8815661 : Blo 1547471 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B3482675 : Blo 1547471 3482675 := bstep (se 1 (by rfl) ⟨2612006, by rfl⟩ : syracuseStep 3482675 = 5224013) B5224013
theorem B1549367 : Blo 1547471 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B1549387 : Blo 1547471 1549387 := bstep (se 1 (by rfl) ⟨1162040, by rfl⟩ : syracuseStep 1549387 = 2324081) B2324081
theorem B3482711 : Blo 1547471 3482711 := bstep (se 1 (by rfl) ⟨2612033, by rfl⟩ : syracuseStep 3482711 = 5224067) B5224067
theorem B1549399 : Blo 1547471 1549399 := bstep (se 1 (by rfl) ⟨1162049, by rfl⟩ : syracuseStep 1549399 = 2324099) B2324099
theorem B5882969 : Blo 1547471 5882969 := bstep (se 2 (by rfl) ⟨2206113, by rfl⟩ : syracuseStep 5882969 = 4412227) B4412227
theorem B14124125 : Blo 1547471 14124125 := bstep (se 3 (by rfl) ⟨2648273, by rfl⟩ : syracuseStep 14124125 = 5296547) B5296547
theorem B1549419 : Blo 1547471 1549419 := bstep (se 1 (by rfl) ⟨1162064, by rfl⟩ : syracuseStep 1549419 = 2324129) B2324129
theorem B1549431 : Blo 1547471 1549431 := bstep (se 1 (by rfl) ⟨1162073, by rfl⟩ : syracuseStep 1549431 = 2324147) B2324147
theorem B1549451 : Blo 1547471 1549451 := bstep (se 1 (by rfl) ⟨1162088, by rfl⟩ : syracuseStep 1549451 = 2324177) B2324177
theorem B2614423 : Blo 1547471 2614423 := bstep (se 1 (by rfl) ⟨1960817, by rfl⟩ : syracuseStep 2614423 = 3921635) B3921635
theorem B1549463 : Blo 1547471 1549463 := bstep (se 1 (by rfl) ⟨1162097, by rfl⟩ : syracuseStep 1549463 = 2324195) B2324195
theorem B3720395 : Blo 1547471 3720395 := bstep (se 1 (by rfl) ⟨2790296, by rfl⟩ : syracuseStep 3720395 = 5580593) B5580593
theorem B3482891 : Blo 1547471 3482891 := bstep (se 1 (by rfl) ⟨2612168, by rfl⟩ : syracuseStep 3482891 = 5224337) B5224337
theorem B3482945 : Blo 1547471 3482945 := bstep (se 2 (by rfl) ⟨1306104, by rfl⟩ : syracuseStep 3482945 = 2612209) B2612209
theorem B1959319 : Blo 1547471 1959319 := bstep (se 1 (by rfl) ⟨1469489, by rfl⟩ : syracuseStep 1959319 = 2938979) B2938979
theorem B5227955 : Blo 1547471 5227955 := bstep (se 1 (by rfl) ⟨3920966, by rfl⟩ : syracuseStep 5227955 = 7841933) B7841933
theorem B4187609 : Blo 1547471 4187609 := bstep (se 2 (by rfl) ⟨1570353, by rfl⟩ : syracuseStep 4187609 = 3140707) B3140707
theorem B3483161 : Blo 1547471 3483161 := bstep (se 2 (by rfl) ⟨1306185, by rfl⟩ : syracuseStep 3483161 = 2612371) B2612371
theorem B3483251 : Blo 1547471 3483251 := bstep (se 1 (by rfl) ⟨2612438, by rfl⟩ : syracuseStep 3483251 = 5224877) B5224877
theorem B3483287 : Blo 1547471 3483287 := bstep (se 1 (by rfl) ⟨2612465, by rfl⟩ : syracuseStep 3483287 = 5224931) B5224931
theorem B5228225 : Blo 1547471 5228225 := bstep (se 2 (by rfl) ⟨1960584, by rfl⟩ : syracuseStep 5228225 = 3921169) B3921169
theorem B1861399 : Blo 1547471 1861399 := bstep (se 1 (by rfl) ⟨1396049, by rfl⟩ : syracuseStep 1861399 = 2792099) B2792099
theorem B3483467 : Blo 1547471 3483467 := bstep (se 1 (by rfl) ⟨2612600, by rfl⟩ : syracuseStep 3483467 = 5225201) B5225201
theorem B3483521 : Blo 1547471 3483521 := bstep (se 2 (by rfl) ⟨1306320, by rfl⟩ : syracuseStep 3483521 = 2612641) B2612641
theorem B8824727 : Blo 1547471 8824727 := bstep (se 1 (by rfl) ⟨6618545, by rfl⟩ : syracuseStep 8824727 = 13237091) B13237091
theorem B3917747 : Blo 1547471 3917747 := bstep (se 1 (by rfl) ⟨2938310, by rfl⟩ : syracuseStep 3917747 = 5876621) B5876621
theorem B5875649 : Blo 1547471 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B2205721 : Blo 1547471 2205721 := bstep (se 2 (by rfl) ⟨827145, by rfl⟩ : syracuseStep 2205721 = 1654291) B1654291
theorem B3483737 : Blo 1547471 3483737 := bstep (se 2 (by rfl) ⟨1306401, by rfl⟩ : syracuseStep 3483737 = 2612803) B2612803
theorem B4409437 : Blo 1547471 4409437 := bstep (se 3 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 4409437 = 1653539) B1653539
theorem B2828441 : Blo 1547471 2828441 := bstep (se 2 (by rfl) ⟨1060665, by rfl⟩ : syracuseStep 2828441 = 2121331) B2121331
theorem B3483827 : Blo 1547471 3483827 := bstep (se 1 (by rfl) ⟨2612870, by rfl⟩ : syracuseStep 3483827 = 5225741) B5225741
theorem B1960139 : Blo 1547471 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B3483863 : Blo 1547471 3483863 := bstep (se 1 (by rfl) ⟨2612897, by rfl⟩ : syracuseStep 3483863 = 5225795) B5225795
theorem B4958425 : Blo 1547471 4958425 := bstep (se 2 (by rfl) ⟨1859409, by rfl⟩ : syracuseStep 4958425 = 3718819) B3718819
theorem B3918041 : Blo 1547471 3918041 := bstep (se 2 (by rfl) ⟨1469265, by rfl⟩ : syracuseStep 3918041 = 2938531) B2938531
theorem B5228765 : Blo 1547471 5228765 := bstep (se 3 (by rfl) ⟨980393, by rfl⟩ : syracuseStep 5228765 = 1960787) B1960787
theorem B3270899 : Blo 1547471 3270899 := bstep (se 1 (by rfl) ⟨2453174, by rfl⟩ : syracuseStep 3270899 = 4906349) B4906349
theorem B5368139 : Blo 1547471 5368139 := bstep (se 1 (by rfl) ⟨4026104, by rfl⟩ : syracuseStep 5368139 = 8052209) B8052209
theorem B3484043 : Blo 1547471 3484043 := bstep (se 1 (by rfl) ⟨2613032, by rfl⟩ : syracuseStep 3484043 = 5226065) B5226065
theorem B3484097 : Blo 1547471 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B5581315 : Blo 1547471 5581315 := bstep (se 1 (by rfl) ⟨4185986, by rfl⟩ : syracuseStep 5581315 = 8371973) B8371973
theorem B7834157 : Blo 1547471 7834157 := bstep (se 3 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 7834157 = 2937809) B2937809
theorem B22309451 : Blo 1547471 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B6277763 : Blo 1547471 6277763 := bstep (se 1 (by rfl) ⟨4708322, by rfl⟩ : syracuseStep 6277763 = 9416645) B9416645
theorem B19835543 : Blo 1547471 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B3484313 : Blo 1547471 3484313 := bstep (se 2 (by rfl) ⟨1306617, by rfl⟩ : syracuseStep 3484313 = 2613235) B2613235
theorem B13224653 : Blo 1547471 13224653 := bstep (se 3 (by rfl) ⟨2479622, by rfl⟩ : syracuseStep 13224653 = 4959245) B4959245
theorem B5515993 : Blo 1547471 5515993 := bstep (se 2 (by rfl) ⟨2068497, by rfl⟩ : syracuseStep 5515993 = 4136995) B4136995
theorem B3484403 : Blo 1547471 3484403 := bstep (se 1 (by rfl) ⟨2613302, by rfl⟩ : syracuseStep 3484403 = 5226605) B5226605
theorem B3484439 : Blo 1547471 3484439 := bstep (se 1 (by rfl) ⟨2613329, by rfl⟩ : syracuseStep 3484439 = 5226659) B5226659
theorem B5581619 : Blo 1547471 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B2321291 : Blo 1547471 2321291 := bstep (se 1 (by rfl) ⟨1740968, by rfl⟩ : syracuseStep 2321291 = 3481937) B3481937
theorem B1960843 : Blo 1547471 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B2321303 : Blo 1547471 2321303 := bstep (se 1 (by rfl) ⟨1740977, by rfl⟩ : syracuseStep 2321303 = 3481955) B3481955
theorem B6613933 : Blo 1547471 6613933 := bstep (se 3 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 6613933 = 2480225) B2480225
theorem B12561331 : Blo 1547471 12561331 := bstep (se 1 (by rfl) ⟨9420998, by rfl⟩ : syracuseStep 12561331 = 18841997) B18841997
theorem B3484619 : Blo 1547471 3484619 := bstep (se 1 (by rfl) ⟨2613464, by rfl⟩ : syracuseStep 3484619 = 5226929) B5226929
theorem B2321369 : Blo 1547471 2321369 := bstep (se 2 (by rfl) ⟨870513, by rfl⟩ : syracuseStep 2321369 = 1741027) B1741027
theorem B3484673 : Blo 1547471 3484673 := bstep (se 2 (by rfl) ⟨1306752, by rfl⟩ : syracuseStep 3484673 = 2613505) B2613505
theorem B11160611 : Blo 1547471 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B2321483 : Blo 1547471 2321483 := bstep (se 1 (by rfl) ⟨1741112, by rfl⟩ : syracuseStep 2321483 = 3482225) B3482225
theorem B2321495 : Blo 1547471 2321495 := bstep (se 1 (by rfl) ⟨1741121, by rfl⟩ : syracuseStep 2321495 = 3482243) B3482243
theorem B9915493 : Blo 1547471 9915493 := bstep (se 4 (by rfl) ⟨929577, by rfl⟩ : syracuseStep 9915493 = 1859155) B1859155
theorem B2321561 : Blo 1547471 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B11758769 : Blo 1547471 11758769 := bstep (se 2 (by rfl) ⟨4409538, by rfl⟩ : syracuseStep 11758769 = 8819077) B8819077
theorem B3484889 : Blo 1547471 3484889 := bstep (se 2 (by rfl) ⟨1306833, by rfl⟩ : syracuseStep 3484889 = 2613667) B2613667
theorem B2321675 : Blo 1547471 2321675 := bstep (se 1 (by rfl) ⟨1741256, by rfl⟩ : syracuseStep 2321675 = 3482513) B3482513
theorem B2321687 : Blo 1547471 2321687 := bstep (se 1 (by rfl) ⟨1741265, by rfl⟩ : syracuseStep 2321687 = 3482531) B3482531
theorem B3484979 : Blo 1547471 3484979 := bstep (se 1 (by rfl) ⟨2613734, by rfl⟩ : syracuseStep 3484979 = 5227469) B5227469
theorem B3485015 : Blo 1547471 3485015 := bstep (se 1 (by rfl) ⟨2613761, by rfl⟩ : syracuseStep 3485015 = 5227523) B5227523
theorem B2321753 : Blo 1547471 2321753 := bstep (se 2 (by rfl) ⟨870657, by rfl⟩ : syracuseStep 2321753 = 1741315) B1741315
theorem B4410713 : Blo 1547471 4410713 := bstep (se 2 (by rfl) ⟨1654017, by rfl⟩ : syracuseStep 4410713 = 3308035) B3308035
theorem B18836837 : Blo 1547471 18836837 := bstep (se 4 (by rfl) ⟨1765953, by rfl⟩ : syracuseStep 18836837 = 3531907) B3531907
theorem B5877137 : Blo 1547471 5877137 := bstep (se 2 (by rfl) ⟨2203926, by rfl⟩ : syracuseStep 5877137 = 4407853) B4407853
theorem B2321867 : Blo 1547471 2321867 := bstep (se 1 (by rfl) ⟨1741400, by rfl⟩ : syracuseStep 2321867 = 3482801) B3482801
theorem B5295563 : Blo 1547471 5295563 := bstep (se 1 (by rfl) ⟨3971672, by rfl⟩ : syracuseStep 5295563 = 7943345) B7943345
theorem B1985995 : Blo 1547471 1985995 := bstep (se 1 (by rfl) ⟨1489496, by rfl⟩ : syracuseStep 1985995 = 2978993) B2978993
theorem B2321879 : Blo 1547471 2321879 := bstep (se 1 (by rfl) ⟨1741409, by rfl⟩ : syracuseStep 2321879 = 3482819) B3482819
theorem B3485195 : Blo 1547471 3485195 := bstep (se 1 (by rfl) ⟨2613896, by rfl⟩ : syracuseStep 3485195 = 5227793) B5227793
theorem B2321945 : Blo 1547471 2321945 := bstep (se 2 (by rfl) ⟨870729, by rfl⟩ : syracuseStep 2321945 = 1741459) B1741459
theorem B4959809 : Blo 1547471 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B3485249 : Blo 1547471 3485249 := bstep (se 2 (by rfl) ⟨1306968, by rfl⟩ : syracuseStep 3485249 = 2613937) B2613937
theorem B9915979 : Blo 1547471 9915979 := bstep (se 1 (by rfl) ⟨7436984, by rfl⟩ : syracuseStep 9915979 = 14873969) B14873969
theorem B2322059 : Blo 1547471 2322059 := bstep (se 1 (by rfl) ⟨1741544, by rfl⟩ : syracuseStep 2322059 = 3483089) B3483089
theorem B2322071 : Blo 1547471 2322071 := bstep (se 1 (by rfl) ⟨1741553, by rfl⟩ : syracuseStep 2322071 = 3483107) B3483107
theorem B11759255 : Blo 1547471 11759255 := bstep (se 1 (by rfl) ⟨8819441, by rfl⟩ : syracuseStep 11759255 = 17638883) B17638883
theorem B2322137 : Blo 1547471 2322137 := bstep (se 2 (by rfl) ⟨870801, by rfl⟩ : syracuseStep 2322137 = 1741603) B1741603
theorem B3485465 : Blo 1547471 3485465 := bstep (se 2 (by rfl) ⟨1307049, by rfl⟩ : syracuseStep 3485465 = 2614099) B2614099
theorem B2322251 : Blo 1547471 2322251 := bstep (se 1 (by rfl) ⟨1741688, by rfl⟩ : syracuseStep 2322251 = 3483377) B3483377
theorem B3919691 : Blo 1547471 3919691 := bstep (se 1 (by rfl) ⟨2939768, by rfl⟩ : syracuseStep 3919691 = 5879537) B5879537
theorem B2322263 : Blo 1547471 2322263 := bstep (se 1 (by rfl) ⟨1741697, by rfl⟩ : syracuseStep 2322263 = 3483395) B3483395
theorem B5877593 : Blo 1547471 5877593 := bstep (se 2 (by rfl) ⟨2204097, by rfl⟩ : syracuseStep 5877593 = 4408195) B4408195
theorem B3485555 : Blo 1547471 3485555 := bstep (se 1 (by rfl) ⟨2614166, by rfl⟩ : syracuseStep 3485555 = 5228333) B5228333
theorem B7843715 : Blo 1547471 7843715 := bstep (se 1 (by rfl) ⟨5882786, by rfl⟩ : syracuseStep 7843715 = 11765573) B11765573
theorem B7442327 : Blo 1547471 7442327 := bstep (se 1 (by rfl) ⟨5581745, by rfl⟩ : syracuseStep 7442327 = 11163491) B11163491
theorem B3485591 : Blo 1547471 3485591 := bstep (se 1 (by rfl) ⟨2614193, by rfl⟩ : syracuseStep 3485591 = 5228387) B5228387
theorem B2322329 : Blo 1547471 2322329 := bstep (se 2 (by rfl) ⟨870873, by rfl⟩ : syracuseStep 2322329 = 1741747) B1741747
theorem B1568683 : Blo 1547471 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B14135219 : Blo 1547471 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B2322443 : Blo 1547471 2322443 := bstep (se 1 (by rfl) ⟨1741832, by rfl⟩ : syracuseStep 2322443 = 3483665) B3483665
theorem B2322455 : Blo 1547471 2322455 := bstep (se 1 (by rfl) ⟨1741841, by rfl⟩ : syracuseStep 2322455 = 3483683) B3483683
theorem B5877805 : Blo 1547471 5877805 := bstep (se 3 (by rfl) ⟨1102088, by rfl⟩ : syracuseStep 5877805 = 2204177) B2204177
theorem B3485771 : Blo 1547471 3485771 := bstep (se 1 (by rfl) ⟨2614328, by rfl⟩ : syracuseStep 3485771 = 5228657) B5228657
theorem B2322521 : Blo 1547471 2322521 := bstep (se 2 (by rfl) ⟨870945, by rfl⟩ : syracuseStep 2322521 = 1741891) B1741891
theorem B4960349 : Blo 1547471 4960349 := bstep (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) B1860131
theorem B1740919 : Blo 1547471 1740919 := bstep (se 1 (by rfl) ⟨1305689, by rfl⟩ : syracuseStep 1740919 = 2611379) B2611379
theorem B3485825 : Blo 1547471 3485825 := bstep (se 2 (by rfl) ⟨1307184, by rfl⟩ : syracuseStep 3485825 = 2614369) B2614369
theorem B2322635 : Blo 1547471 2322635 := bstep (se 1 (by rfl) ⟨1741976, by rfl⟩ : syracuseStep 2322635 = 3483953) B3483953
theorem B2322647 : Blo 1547471 2322647 := bstep (se 1 (by rfl) ⟨1741985, by rfl⟩ : syracuseStep 2322647 = 3483971) B3483971
theorem B2150617 : Blo 1547471 2150617 := bstep (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) B1612963
theorem B22335749 : Blo 1547471 22335749 := bstep (se 4 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 22335749 = 4187953) B4187953
theorem B2322713 : Blo 1547471 2322713 := bstep (se 2 (by rfl) ⟨871017, by rfl⟩ : syracuseStep 2322713 = 1742035) B1742035
theorem B1741099 : Blo 1547471 1741099 := bstep (se 1 (by rfl) ⟨1305824, by rfl⟩ : syracuseStep 1741099 = 2611649) B2611649
theorem B9417035 : Blo 1547471 9417035 := bstep (se 1 (by rfl) ⟨7062776, by rfl⟩ : syracuseStep 9417035 = 14125553) B14125553
theorem B2871641 : Blo 1547471 2871641 := bstep (se 2 (by rfl) ⟨1076865, by rfl⟩ : syracuseStep 2871641 = 2153731) B2153731
theorem B3486041 : Blo 1547471 3486041 := bstep (se 2 (by rfl) ⟨1307265, by rfl⟩ : syracuseStep 3486041 = 2614531) B2614531
theorem B5878109 : Blo 1547471 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B2322827 : Blo 1547471 2322827 := bstep (se 1 (by rfl) ⟨1742120, by rfl⟩ : syracuseStep 2322827 = 3484241) B3484241
theorem B1741207 : Blo 1547471 1741207 := bstep (se 1 (by rfl) ⟨1305905, by rfl⟩ : syracuseStep 1741207 = 2611811) B2611811
theorem B2322839 : Blo 1547471 2322839 := bstep (se 1 (by rfl) ⟨1742129, by rfl⟩ : syracuseStep 2322839 = 3484259) B3484259
theorem B7442867 : Blo 1547471 7442867 := bstep (se 1 (by rfl) ⟨5582150, by rfl⟩ : syracuseStep 7442867 = 11164301) B11164301
theorem B3486131 : Blo 1547471 3486131 := bstep (se 1 (by rfl) ⟨2614598, by rfl⟩ : syracuseStep 3486131 = 5229197) B5229197
theorem B3486167 : Blo 1547471 3486167 := bstep (se 1 (by rfl) ⟨2614625, by rfl⟩ : syracuseStep 3486167 = 5229251) B5229251
theorem B2322905 : Blo 1547471 2322905 := bstep (se 2 (by rfl) ⟨871089, by rfl⟩ : syracuseStep 2322905 = 1742179) B1742179
theorem B5222987 : Blo 1547471 5222987 := bstep (se 1 (by rfl) ⟨3917240, by rfl⟩ : syracuseStep 5222987 = 7834481) B7834481
theorem B1741387 : Blo 1547471 1741387 := bstep (se 1 (by rfl) ⟨1306040, by rfl⟩ : syracuseStep 1741387 = 2612081) B2612081
theorem B2323019 : Blo 1547471 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B2323031 : Blo 1547471 2323031 := bstep (se 1 (by rfl) ⟨1742273, by rfl⟩ : syracuseStep 2323031 = 3484547) B3484547
theorem B21189251 : Blo 1547471 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B8819351 : Blo 1547471 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B2323097 : Blo 1547471 2323097 := bstep (se 2 (by rfl) ⟨871161, by rfl⟩ : syracuseStep 2323097 = 1742323) B1742323
theorem B1741495 : Blo 1547471 1741495 := bstep (se 1 (by rfl) ⟨1306121, by rfl⟩ : syracuseStep 1741495 = 2612243) B2612243
theorem B2323211 : Blo 1547471 2323211 := bstep (se 1 (by rfl) ⟨1742408, by rfl⟩ : syracuseStep 2323211 = 3484817) B3484817
theorem B2323223 : Blo 1547471 2323223 := bstep (se 1 (by rfl) ⟨1742417, by rfl⟩ : syracuseStep 2323223 = 3484835) B3484835
theorem B3920663 : Blo 1547471 3920663 := bstep (se 1 (by rfl) ⟨2940497, by rfl⟩ : syracuseStep 3920663 = 5880995) B5880995
theorem B59560757 : Blo 1547471 59560757 := bstep (se 5 (by rfl) ⟨2791910, by rfl⟩ : syracuseStep 59560757 = 5583821) B5583821
theorem B5223257 : Blo 1547471 5223257 := bstep (se 2 (by rfl) ⟨1958721, by rfl⟩ : syracuseStep 5223257 = 3917443) B3917443
theorem B2323289 : Blo 1547471 2323289 := bstep (se 2 (by rfl) ⟨871233, by rfl⟩ : syracuseStep 2323289 = 1742467) B1742467
theorem B1741675 : Blo 1547471 1741675 := bstep (se 1 (by rfl) ⟨1306256, by rfl⟩ : syracuseStep 1741675 = 2612513) B2612513
theorem B2937779 : Blo 1547471 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B4412353 : Blo 1547471 4412353 := bstep (se 2 (by rfl) ⟨1654632, by rfl⟩ : syracuseStep 4412353 = 3309265) B3309265
theorem B2323403 : Blo 1547471 2323403 := bstep (se 1 (by rfl) ⟨1742552, by rfl⟩ : syracuseStep 2323403 = 3485105) B3485105
theorem B1741783 : Blo 1547471 1741783 := bstep (se 1 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 1741783 = 2612675) B2612675
theorem B2323415 : Blo 1547471 2323415 := bstep (se 1 (by rfl) ⟨1742561, by rfl⟩ : syracuseStep 2323415 = 3485123) B3485123
theorem B2323481 : Blo 1547471 2323481 := bstep (se 2 (by rfl) ⟨871305, by rfl⟩ : syracuseStep 2323481 = 1742611) B1742611
theorem B2683991 : Blo 1547471 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B1569899 : Blo 1547471 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1741963 : Blo 1547471 1741963 := bstep (se 1 (by rfl) ⟨1306472, by rfl⟩ : syracuseStep 1741963 = 2612945) B2612945
theorem B2323595 : Blo 1547471 2323595 := bstep (se 1 (by rfl) ⟨1742696, by rfl⟩ : syracuseStep 2323595 = 3485393) B3485393
theorem B2938007 : Blo 1547471 2938007 := bstep (se 1 (by rfl) ⟨2203505, by rfl⟩ : syracuseStep 2938007 = 4407011) B4407011
theorem B2323607 : Blo 1547471 2323607 := bstep (se 1 (by rfl) ⟨1742705, by rfl⟩ : syracuseStep 2323607 = 3485411) B3485411
theorem B11154611 : Blo 1547471 11154611 := bstep (se 1 (by rfl) ⟨8365958, by rfl⟩ : syracuseStep 11154611 = 16731917) B16731917
theorem B17634509 : Blo 1547471 17634509 := bstep (se 3 (by rfl) ⟨3306470, by rfl⟩ : syracuseStep 17634509 = 6612941) B6612941
theorem B13407437 : Blo 1547471 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B2323673 : Blo 1547471 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B1742071 : Blo 1547471 1742071 := bstep (se 1 (by rfl) ⟨1306553, by rfl⟩ : syracuseStep 1742071 = 2613107) B2613107
theorem B6616343 : Blo 1547471 6616343 := bstep (se 1 (by rfl) ⟨4962257, by rfl⟩ : syracuseStep 6616343 = 9924515) B9924515
theorem B2323787 : Blo 1547471 2323787 := bstep (se 1 (by rfl) ⟨1742840, by rfl⟩ : syracuseStep 2323787 = 3485681) B3485681
theorem B2323799 : Blo 1547471 2323799 := bstep (se 1 (by rfl) ⟨1742849, by rfl⟩ : syracuseStep 2323799 = 3485699) B3485699
theorem B3306881 : Blo 1547471 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B4183447 : Blo 1547471 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2938265 : Blo 1547471 2938265 := bstep (se 2 (by rfl) ⟨1101849, by rfl⟩ : syracuseStep 2938265 = 2203699) B2203699
theorem B2323865 : Blo 1547471 2323865 := bstep (se 2 (by rfl) ⟨871449, by rfl⟩ : syracuseStep 2323865 = 1742899) B1742899
theorem B1742251 : Blo 1547471 1742251 := bstep (se 1 (by rfl) ⟨1306688, by rfl⟩ : syracuseStep 1742251 = 2613377) B2613377
theorem B3921331 : Blo 1547471 3921331 := bstep (se 1 (by rfl) ⟨2940998, by rfl⟩ : syracuseStep 3921331 = 5881997) B5881997
theorem B5658077 : Blo 1547471 5658077 := bstep (se 3 (by rfl) ⟨1060889, by rfl⟩ : syracuseStep 5658077 = 2121779) B2121779
theorem B2323979 : Blo 1547471 2323979 := bstep (se 1 (by rfl) ⟨1742984, by rfl⟩ : syracuseStep 2323979 = 3485969) B3485969
theorem B5223959 : Blo 1547471 5223959 := bstep (se 1 (by rfl) ⟨3917969, by rfl⟩ : syracuseStep 5223959 = 7835939) B7835939
theorem B1742359 : Blo 1547471 1742359 := bstep (se 1 (by rfl) ⟨1306769, by rfl⟩ : syracuseStep 1742359 = 2613539) B2613539
theorem B2323991 : Blo 1547471 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B23828003 : Blo 1547471 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B8943149 : Blo 1547471 8943149 := bstep (se 3 (by rfl) ⟨1676840, by rfl⟩ : syracuseStep 8943149 = 3353681) B3353681
theorem B3921473 : Blo 1547471 3921473 := bstep (se 2 (by rfl) ⟨1470552, by rfl⟩ : syracuseStep 3921473 = 2941105) B2941105
theorem B2324057 : Blo 1547471 2324057 := bstep (se 2 (by rfl) ⟨871521, by rfl⟩ : syracuseStep 2324057 = 1743043) B1743043
theorem B6280877 : Blo 1547471 6280877 := bstep (se 3 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 6280877 = 2355329) B2355329
theorem B1742539 : Blo 1547471 1742539 := bstep (se 1 (by rfl) ⟨1306904, by rfl⟩ : syracuseStep 1742539 = 2613809) B2613809
theorem B2324171 : Blo 1547471 2324171 := bstep (se 1 (by rfl) ⟨1743128, by rfl⟩ : syracuseStep 2324171 = 3486257) B3486257
theorem B3307223 : Blo 1547471 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B2324183 : Blo 1547471 2324183 := bstep (se 1 (by rfl) ⟨1743137, by rfl⟩ : syracuseStep 2324183 = 3486275) B3486275
theorem B22640429 : Blo 1547471 22640429 := bstep (se 3 (by rfl) ⟨4245080, by rfl⟩ : syracuseStep 22640429 = 8490161) B8490161
theorem B2938675 : Blo 1547471 2938675 := bstep (se 1 (by rfl) ⟨2204006, by rfl⟩ : syracuseStep 2938675 = 4408013) B4408013
theorem B1742647 : Blo 1547471 1742647 := bstep (se 1 (by rfl) ⟨1306985, by rfl⟩ : syracuseStep 1742647 = 2613971) B2613971
theorem B14882777 : Blo 1547471 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B4962269 : Blo 1547471 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B1742827 : Blo 1547471 1742827 := bstep (se 1 (by rfl) ⟨1307120, by rfl⟩ : syracuseStep 1742827 = 2614241) B2614241
theorem B5224499 : Blo 1547471 5224499 := bstep (se 1 (by rfl) ⟨3918374, by rfl⟩ : syracuseStep 5224499 = 7836749) B7836749
theorem B1742935 : Blo 1547471 1742935 := bstep (se 1 (by rfl) ⟨1307201, by rfl⟩ : syracuseStep 1742935 = 2614403) B2614403
theorem B4241497 : Blo 1547471 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B22313141 : Blo 1547471 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B4028609 : Blo 1547471 4028609 := bstep (se 2 (by rfl) ⟨1510728, by rfl⟩ : syracuseStep 4028609 = 3021457) B3021457
theorem B3307787 : Blo 1547471 3307787 := bstep (se 1 (by rfl) ⟨2480840, by rfl⟩ : syracuseStep 3307787 = 4961681) B4961681
theorem B1743115 : Blo 1547471 1743115 := bstep (se 1 (by rfl) ⟨1307336, by rfl⟩ : syracuseStep 1743115 = 2614673) B2614673
theorem B3021079 : Blo 1547471 3021079 := bstep (se 1 (by rfl) ⟨2265809, by rfl⟩ : syracuseStep 3021079 = 4531619) B4531619
theorem B2939161 : Blo 1547471 2939161 := bstep (se 2 (by rfl) ⟨1102185, by rfl⟩ : syracuseStep 2939161 = 2204371) B2204371
theorem B5224769 : Blo 1547471 5224769 := bstep (se 2 (by rfl) ⟨1959288, by rfl⟩ : syracuseStep 5224769 = 3918577) B3918577
theorem B7838045 : Blo 1547471 7838045 := bstep (se 3 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 7838045 = 2939267) B2939267
theorem B2611595 : Blo 1547471 2611595 := bstep (se 1 (by rfl) ⟨1958696, by rfl⟩ : syracuseStep 2611595 = 3917393) B3917393
theorem B2791883 : Blo 1547471 2791883 := bstep (se 1 (by rfl) ⟨2093912, by rfl⟩ : syracuseStep 2791883 = 4187825) B4187825
theorem B2611723 : Blo 1547471 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B1653355 : Blo 1547471 1653355 := bstep (se 1 (by rfl) ⟨1240016, by rfl⟩ : syracuseStep 1653355 = 2480033) B2480033
theorem B2611865 : Blo 1547471 2611865 := bstep (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) B1958899
theorem B2611993 : Blo 1547471 2611993 := bstep (se 2 (by rfl) ⟨979497, by rfl⟩ : syracuseStep 2611993 = 1958995) B1958995
theorem B12901165 : Blo 1547471 12901165 := bstep (se 3 (by rfl) ⟨2418968, by rfl⟩ : syracuseStep 12901165 = 4837937) B4837937
theorem B2939723 : Blo 1547471 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B3308377 : Blo 1547471 3308377 := bstep (se 2 (by rfl) ⟨1240641, by rfl⟩ : syracuseStep 3308377 = 2481283) B2481283
theorem B5225309 : Blo 1547471 5225309 := bstep (se 3 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 5225309 = 1959491) B1959491
theorem B5880707 : Blo 1547471 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B3021707 : Blo 1547471 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B5880721 : Blo 1547471 5880721 := bstep (se 2 (by rfl) ⟨2205270, by rfl⟩ : syracuseStep 5880721 = 4410541) B4410541
theorem B2939905 : Blo 1547471 2939905 := bstep (se 2 (by rfl) ⟨1102464, by rfl⟩ : syracuseStep 2939905 = 2204929) B2204929
theorem B6618257 : Blo 1547471 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B5881025 : Blo 1547471 5881025 := bstep (se 2 (by rfl) ⟨2205384, by rfl⟩ : syracuseStep 5881025 = 4410769) B4410769
theorem B4472011 : Blo 1547471 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B1547479 : Blo 1547471 1547479 := bstep (se 1 (by rfl) ⟨1160609, by rfl⟩ : syracuseStep 1547479 = 2321219) B2321219
theorem B1547499 : Blo 1547471 1547499 := bstep (se 1 (by rfl) ⟨1160624, by rfl⟩ : syracuseStep 1547499 = 2321249) B2321249
theorem B1547511 : Blo 1547471 1547511 := bstep (se 1 (by rfl) ⟨1160633, by rfl⟩ : syracuseStep 1547511 = 2321267) B2321267
theorem B1547531 : Blo 1547471 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B2235659 : Blo 1547471 2235659 := bstep (se 1 (by rfl) ⟨1676744, by rfl⟩ : syracuseStep 2235659 = 3353489) B3353489
theorem B6610193 : Blo 1547471 6610193 := bstep (se 2 (by rfl) ⟨2478822, by rfl⟩ : syracuseStep 6610193 = 4957645) B4957645
theorem B1547543 : Blo 1547471 1547543 := bstep (se 1 (by rfl) ⟨1160657, by rfl⟩ : syracuseStep 1547543 = 2321315) B2321315
theorem B1547563 : Blo 1547471 1547563 := bstep (se 1 (by rfl) ⟨1160672, by rfl⟩ : syracuseStep 1547563 = 2321345) B2321345
theorem B1547575 : Blo 1547471 1547575 := bstep (se 1 (by rfl) ⟨1160681, by rfl⟩ : syracuseStep 1547575 = 2321363) B2321363
theorem B1547595 : Blo 1547471 1547595 := bstep (se 1 (by rfl) ⟨1160696, by rfl⟩ : syracuseStep 1547595 = 2321393) B2321393
theorem B1547607 : Blo 1547471 1547607 := bstep (se 1 (by rfl) ⟨1160705, by rfl⟩ : syracuseStep 1547607 = 2321411) B2321411
theorem B2612567 : Blo 1547471 2612567 := bstep (se 1 (by rfl) ⟨1959425, by rfl⟩ : syracuseStep 2612567 = 3918851) B3918851
theorem B13229405 : Blo 1547471 13229405 := bstep (se 3 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 13229405 = 4961027) B4961027
theorem B1547627 : Blo 1547471 1547627 := bstep (se 1 (by rfl) ⟨1160720, by rfl⟩ : syracuseStep 1547627 = 2321441) B2321441
theorem B1547639 : Blo 1547471 1547639 := bstep (se 1 (by rfl) ⟨1160729, by rfl⟩ : syracuseStep 1547639 = 2321459) B2321459
theorem B1547659 : Blo 1547471 1547659 := bstep (se 1 (by rfl) ⟨1160744, by rfl⟩ : syracuseStep 1547659 = 2321489) B2321489
theorem B1547671 : Blo 1547471 1547671 := bstep (se 1 (by rfl) ⟨1160753, by rfl⟩ : syracuseStep 1547671 = 2321507) B2321507
theorem B1547691 : Blo 1547471 1547691 := bstep (se 1 (by rfl) ⟨1160768, by rfl⟩ : syracuseStep 1547691 = 2321537) B2321537
theorem B1547703 : Blo 1547471 1547703 := bstep (se 1 (by rfl) ⟨1160777, by rfl⟩ : syracuseStep 1547703 = 2321555) B2321555
theorem B1547723 : Blo 1547471 1547723 := bstep (se 1 (by rfl) ⟨1160792, by rfl⟩ : syracuseStep 1547723 = 2321585) B2321585
theorem B1547735 : Blo 1547471 1547735 := bstep (se 1 (by rfl) ⟨1160801, by rfl⟩ : syracuseStep 1547735 = 2321603) B2321603
theorem B2612695 : Blo 1547471 2612695 := bstep (se 1 (by rfl) ⟨1959521, by rfl⟩ : syracuseStep 2612695 = 3919043) B3919043
theorem B19848665 : Blo 1547471 19848665 := bstep (se 2 (by rfl) ⟨7443249, by rfl⟩ : syracuseStep 19848665 = 14886499) B14886499
theorem B1547755 : Blo 1547471 1547755 := bstep (se 1 (by rfl) ⟨1160816, by rfl⟩ : syracuseStep 1547755 = 2321633) B2321633
theorem B1547767 : Blo 1547471 1547767 := bstep (se 1 (by rfl) ⟨1160825, by rfl⟩ : syracuseStep 1547767 = 2321651) B2321651
theorem B1547787 : Blo 1547471 1547787 := bstep (se 1 (by rfl) ⟨1160840, by rfl⟩ : syracuseStep 1547787 = 2321681) B2321681
theorem B1547799 : Blo 1547471 1547799 := bstep (se 1 (by rfl) ⟨1160849, by rfl⟩ : syracuseStep 1547799 = 2321699) B2321699
theorem B1547819 : Blo 1547471 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B7437869 : Blo 1547471 7437869 := bstep (se 3 (by rfl) ⟨1394600, by rfl⟩ : syracuseStep 7437869 = 2789201) B2789201
theorem B1547831 : Blo 1547471 1547831 := bstep (se 1 (by rfl) ⟨1160873, by rfl⟩ : syracuseStep 1547831 = 2321747) B2321747
theorem B1547851 : Blo 1547471 1547851 := bstep (se 1 (by rfl) ⟨1160888, by rfl⟩ : syracuseStep 1547851 = 2321777) B2321777
theorem B1547863 : Blo 1547471 1547863 := bstep (se 1 (by rfl) ⟨1160897, by rfl⟩ : syracuseStep 1547863 = 2321795) B2321795
theorem B1547883 : Blo 1547471 1547883 := bstep (se 1 (by rfl) ⟨1160912, by rfl⟩ : syracuseStep 1547883 = 2321825) B2321825
theorem B1547895 : Blo 1547471 1547895 := bstep (se 1 (by rfl) ⟨1160921, by rfl⟩ : syracuseStep 1547895 = 2321843) B2321843
theorem B1547915 : Blo 1547471 1547915 := bstep (se 1 (by rfl) ⟨1160936, by rfl⟩ : syracuseStep 1547915 = 2321873) B2321873
theorem B1547927 : Blo 1547471 1547927 := bstep (se 1 (by rfl) ⟨1160945, by rfl⟩ : syracuseStep 1547927 = 2321891) B2321891
theorem B2481815 : Blo 1547471 2481815 := bstep (se 1 (by rfl) ⟨1861361, by rfl⟩ : syracuseStep 2481815 = 3722723) B3722723
theorem B1547947 : Blo 1547471 1547947 := bstep (se 1 (by rfl) ⟨1160960, by rfl⟩ : syracuseStep 1547947 = 2321921) B2321921
theorem B1547959 : Blo 1547471 1547959 := bstep (se 1 (by rfl) ⟨1160969, by rfl⟩ : syracuseStep 1547959 = 2321939) B2321939
theorem B4406987 : Blo 1547471 4406987 := bstep (se 1 (by rfl) ⟨3305240, by rfl⟩ : syracuseStep 4406987 = 6610481) B6610481
theorem B1859275 : Blo 1547471 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B1547979 : Blo 1547471 1547979 := bstep (se 1 (by rfl) ⟨1160984, by rfl⟩ : syracuseStep 1547979 = 2321969) B2321969
theorem B2940619 : Blo 1547471 2940619 := bstep (se 1 (by rfl) ⟨2205464, by rfl⟩ : syracuseStep 2940619 = 4410929) B4410929
theorem B1547991 : Blo 1547471 1547991 := bstep (se 1 (by rfl) ⟨1160993, by rfl⟩ : syracuseStep 1547991 = 2321987) B2321987
theorem B1548011 : Blo 1547471 1548011 := bstep (se 1 (by rfl) ⟨1161008, by rfl⟩ : syracuseStep 1548011 = 2322017) B2322017
theorem B1548023 : Blo 1547471 1548023 := bstep (se 1 (by rfl) ⟨1161017, by rfl⟩ : syracuseStep 1548023 = 2322035) B2322035
theorem B1548043 : Blo 1547471 1548043 := bstep (se 1 (by rfl) ⟨1161032, by rfl⟩ : syracuseStep 1548043 = 2322065) B2322065
theorem B1548055 : Blo 1547471 1548055 := bstep (se 1 (by rfl) ⟨1161041, by rfl⟩ : syracuseStep 1548055 = 2322083) B2322083
theorem B2940695 : Blo 1547471 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B1548075 : Blo 1547471 1548075 := bstep (se 1 (by rfl) ⟨1161056, by rfl⟩ : syracuseStep 1548075 = 2322113) B2322113
theorem B1548087 : Blo 1547471 1548087 := bstep (se 1 (by rfl) ⟨1161065, by rfl⟩ : syracuseStep 1548087 = 2322131) B2322131
theorem B1548107 : Blo 1547471 1548107 := bstep (se 1 (by rfl) ⟨1161080, by rfl⟩ : syracuseStep 1548107 = 2322161) B2322161
theorem B1548119 : Blo 1547471 1548119 := bstep (se 1 (by rfl) ⟨1161089, by rfl⟩ : syracuseStep 1548119 = 2322179) B2322179
theorem B5881693 : Blo 1547471 5881693 := bstep (se 3 (by rfl) ⟨1102817, by rfl⟩ : syracuseStep 5881693 = 2205635) B2205635
theorem B1548139 : Blo 1547471 1548139 := bstep (se 1 (by rfl) ⟨1161104, by rfl⟩ : syracuseStep 1548139 = 2322209) B2322209
theorem B1548151 : Blo 1547471 1548151 := bstep (se 1 (by rfl) ⟨1161113, by rfl⟩ : syracuseStep 1548151 = 2322227) B2322227
theorem B1548171 : Blo 1547471 1548171 := bstep (se 1 (by rfl) ⟨1161128, by rfl⟩ : syracuseStep 1548171 = 2322257) B2322257
theorem B1548183 : Blo 1547471 1548183 := bstep (se 1 (by rfl) ⟨1161137, by rfl⟩ : syracuseStep 1548183 = 2322275) B2322275
theorem B1548203 : Blo 1547471 1548203 := bstep (se 1 (by rfl) ⟨1161152, by rfl⟩ : syracuseStep 1548203 = 2322305) B2322305
theorem B1548215 : Blo 1547471 1548215 := bstep (se 1 (by rfl) ⟨1161161, by rfl⟩ : syracuseStep 1548215 = 2322323) B2322323
theorem B6610891 : Blo 1547471 6610891 := bstep (se 1 (by rfl) ⟨4958168, by rfl⟩ : syracuseStep 6610891 = 9916337) B9916337
theorem B1548235 : Blo 1547471 1548235 := bstep (se 1 (by rfl) ⟨1161176, by rfl⟩ : syracuseStep 1548235 = 2322353) B2322353
theorem B5226443 : Blo 1547471 5226443 := bstep (se 1 (by rfl) ⟨3919832, by rfl⟩ : syracuseStep 5226443 = 7839665) B7839665
theorem B1548247 : Blo 1547471 1548247 := bstep (se 1 (by rfl) ⟨1161185, by rfl⟩ : syracuseStep 1548247 = 2322371) B2322371
theorem B4186073 : Blo 1547471 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B1548267 : Blo 1547471 1548267 := bstep (se 1 (by rfl) ⟨1161200, by rfl⟩ : syracuseStep 1548267 = 2322401) B2322401
theorem B1548279 : Blo 1547471 1548279 := bstep (se 1 (by rfl) ⟨1161209, by rfl⟩ : syracuseStep 1548279 = 2322419) B2322419
theorem B1548295 : Blo 1547471 1548295 := bstep (se 1 (by rfl) ⟨1161221, by rfl⟩ : syracuseStep 1548295 = 2322443) B2322443
theorem B1548303 : Blo 1547471 1548303 := bstep (se 1 (by rfl) ⟨1161227, by rfl⟩ : syracuseStep 1548303 = 2322455) B2322455
theorem B2940961 : Blo 1547471 2940961 := bstep (se 2 (by rfl) ⟨1102860, by rfl⟩ : syracuseStep 2940961 = 2205721) B2205721
theorem B1548347 : Blo 1547471 1548347 := bstep (se 1 (by rfl) ⟨1161260, by rfl⟩ : syracuseStep 1548347 = 2322521) B2322521
theorem B1548423 : Blo 1547471 1548423 := bstep (se 1 (by rfl) ⟨1161317, by rfl⟩ : syracuseStep 1548423 = 2322635) B2322635
theorem B1548431 : Blo 1547471 1548431 := bstep (se 1 (by rfl) ⟨1161323, by rfl⟩ : syracuseStep 1548431 = 2322647) B2322647
theorem B4407443 : Blo 1547471 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B1548475 : Blo 1547471 1548475 := bstep (se 1 (by rfl) ⟨1161356, by rfl⟩ : syracuseStep 1548475 = 2322713) B2322713
theorem B1548551 : Blo 1547471 1548551 := bstep (se 1 (by rfl) ⟨1161413, by rfl⟩ : syracuseStep 1548551 = 2322827) B2322827
theorem B1548559 : Blo 1547471 1548559 := bstep (se 1 (by rfl) ⟨1161419, by rfl⟩ : syracuseStep 1548559 = 2322839) B2322839
theorem B5226767 : Blo 1547471 5226767 := bstep (se 1 (by rfl) ⟨3920075, by rfl⟩ : syracuseStep 5226767 = 7840151) B7840151
theorem B4186397 : Blo 1547471 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B6611233 : Blo 1547471 6611233 := bstep (se 2 (by rfl) ⟨2479212, by rfl⟩ : syracuseStep 6611233 = 4958425) B4958425
theorem B2867489 : Blo 1547471 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B1548603 : Blo 1547471 1548603 := bstep (se 1 (by rfl) ⟨1161452, by rfl⟩ : syracuseStep 1548603 = 2322905) B2322905
theorem B4407671 : Blo 1547471 4407671 := bstep (se 1 (by rfl) ⟨3305753, by rfl⟩ : syracuseStep 4407671 = 6611507) B6611507
theorem B3481991 : Blo 1547471 3481991 := bstep (se 1 (by rfl) ⟨2611493, by rfl⟩ : syracuseStep 3481991 = 5222987) B5222987
theorem B1548679 : Blo 1547471 1548679 := bstep (se 1 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 1548679 = 2323019) B2323019
theorem B1548687 : Blo 1547471 1548687 := bstep (se 1 (by rfl) ⟨1161515, by rfl⟩ : syracuseStep 1548687 = 2323031) B2323031
theorem B11764115 : Blo 1547471 11764115 := bstep (se 1 (by rfl) ⟨8823086, by rfl⟩ : syracuseStep 11764115 = 17646173) B17646173
theorem B1548731 : Blo 1547471 1548731 := bstep (se 1 (by rfl) ⟨1161548, by rfl⟩ : syracuseStep 1548731 = 2323097) B2323097
theorem B29745629 : Blo 1547471 29745629 := bstep (se 3 (by rfl) ⟨5577305, by rfl⟩ : syracuseStep 29745629 = 11154611) B11154611
theorem B1548807 : Blo 1547471 1548807 := bstep (se 1 (by rfl) ⟨1161605, by rfl⟩ : syracuseStep 1548807 = 2323211) B2323211
theorem B3719695 : Blo 1547471 3719695 := bstep (se 1 (by rfl) ⟨2789771, by rfl⟩ : syracuseStep 3719695 = 5579543) B5579543
theorem B1548815 : Blo 1547471 1548815 := bstep (se 1 (by rfl) ⟨1161611, by rfl⟩ : syracuseStep 1548815 = 2323223) B2323223
theorem B2613775 : Blo 1547471 2613775 := bstep (se 1 (by rfl) ⟨1960331, by rfl⟩ : syracuseStep 2613775 = 3920663) B3920663
theorem B5227037 : Blo 1547471 5227037 := bstep (se 3 (by rfl) ⟨980069, by rfl⟩ : syracuseStep 5227037 = 1960139) B1960139
theorem B39707171 : Blo 1547471 39707171 := bstep (se 1 (by rfl) ⟨29780378, by rfl⟩ : syracuseStep 39707171 = 59560757) B59560757
theorem B3482171 : Blo 1547471 3482171 := bstep (se 1 (by rfl) ⟨2611628, by rfl⟩ : syracuseStep 3482171 = 5223257) B5223257
theorem B1548859 : Blo 1547471 1548859 := bstep (se 1 (by rfl) ⟨1161644, by rfl⟩ : syracuseStep 1548859 = 2323289) B2323289
theorem B1958519 : Blo 1547471 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1548935 : Blo 1547471 1548935 := bstep (se 1 (by rfl) ⟨1161701, by rfl⟩ : syracuseStep 1548935 = 2323403) B2323403
theorem B1548943 : Blo 1547471 1548943 := bstep (se 1 (by rfl) ⟨1161707, by rfl⟩ : syracuseStep 1548943 = 2323415) B2323415
theorem B3482297 : Blo 1547471 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B1548987 : Blo 1547471 1548987 := bstep (se 1 (by rfl) ⟨1161740, by rfl⟩ : syracuseStep 1548987 = 2323481) B2323481
theorem B1549063 : Blo 1547471 1549063 := bstep (se 1 (by rfl) ⟨1161797, by rfl⟩ : syracuseStep 1549063 = 2323595) B2323595
theorem B1958671 : Blo 1547471 1958671 := bstep (se 1 (by rfl) ⟨1469003, by rfl⟩ : syracuseStep 1958671 = 2938007) B2938007
theorem B1549071 : Blo 1547471 1549071 := bstep (se 1 (by rfl) ⟨1161803, by rfl⟩ : syracuseStep 1549071 = 2323607) B2323607
theorem B11756339 : Blo 1547471 11756339 := bstep (se 1 (by rfl) ⟨8817254, by rfl⟩ : syracuseStep 11756339 = 17634509) B17634509
theorem B8938291 : Blo 1547471 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1549115 : Blo 1547471 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B1549191 : Blo 1547471 1549191 := bstep (se 1 (by rfl) ⟨1161893, by rfl⟩ : syracuseStep 1549191 = 2323787) B2323787
theorem B1549199 : Blo 1547471 1549199 := bstep (se 1 (by rfl) ⟨1161899, by rfl⟩ : syracuseStep 1549199 = 2323799) B2323799
theorem B2204587 : Blo 1547471 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B1958843 : Blo 1547471 1958843 := bstep (se 1 (by rfl) ⟨1469132, by rfl⟩ : syracuseStep 1958843 = 2938265) B2938265
theorem B1549243 : Blo 1547471 1549243 := bstep (se 1 (by rfl) ⟨1161932, by rfl⟩ : syracuseStep 1549243 = 2323865) B2323865
theorem B1549319 : Blo 1547471 1549319 := bstep (se 1 (by rfl) ⟨1161989, by rfl⟩ : syracuseStep 1549319 = 2323979) B2323979
theorem B3482639 : Blo 1547471 3482639 := bstep (se 1 (by rfl) ⟨2611979, by rfl⟩ : syracuseStep 3482639 = 5223959) B5223959
theorem B1549327 : Blo 1547471 1549327 := bstep (se 1 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 1549327 = 2323991) B2323991
theorem B15885335 : Blo 1547471 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B3482657 : Blo 1547471 3482657 := bstep (se 2 (by rfl) ⟨1305996, by rfl⟩ : syracuseStep 3482657 = 2611993) B2611993
theorem B2614315 : Blo 1547471 2614315 := bstep (se 1 (by rfl) ⟨1960736, by rfl⟩ : syracuseStep 2614315 = 3921473) B3921473
theorem B1549371 : Blo 1547471 1549371 := bstep (se 1 (by rfl) ⟨1162028, by rfl⟩ : syracuseStep 1549371 = 2324057) B2324057
theorem B4187251 : Blo 1547471 4187251 := bstep (se 1 (by rfl) ⟨3140438, by rfl⟩ : syracuseStep 4187251 = 6280877) B6280877
theorem B1549447 : Blo 1547471 1549447 := bstep (se 1 (by rfl) ⟨1162085, by rfl⟩ : syracuseStep 1549447 = 2324171) B2324171
theorem B2204815 : Blo 1547471 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B1549455 : Blo 1547471 1549455 := bstep (se 1 (by rfl) ⟨1162091, by rfl⟩ : syracuseStep 1549455 = 2324183) B2324183
theorem B2614457 : Blo 1547471 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B7840961 : Blo 1547471 7840961 := bstep (se 2 (by rfl) ⟨2940360, by rfl⟩ : syracuseStep 7840961 = 5880721) B5880721
theorem B5883137 : Blo 1547471 5883137 := bstep (se 2 (by rfl) ⟨2206176, by rfl⟩ : syracuseStep 5883137 = 4412353) B4412353
theorem B5883151 : Blo 1547471 5883151 := bstep (se 1 (by rfl) ⟨4412363, by rfl⟩ : syracuseStep 5883151 = 8824727) B8824727
theorem B3917099 : Blo 1547471 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B9921851 : Blo 1547471 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B3482999 : Blo 1547471 3482999 := bstep (se 1 (by rfl) ⟨2612249, by rfl⟩ : syracuseStep 3482999 = 5224499) B5224499
theorem B1885627 : Blo 1547471 1885627 := bstep (se 1 (by rfl) ⟨1414220, by rfl⟩ : syracuseStep 1885627 = 2828441) B2828441
theorem B2205191 : Blo 1547471 2205191 := bstep (se 1 (by rfl) ⟨1653893, by rfl⟩ : syracuseStep 2205191 = 3307787) B3307787
theorem B3483179 : Blo 1547471 3483179 := bstep (se 1 (by rfl) ⟨2612384, by rfl⟩ : syracuseStep 3483179 = 5224769) B5224769
theorem B1861255 : Blo 1547471 1861255 := bstep (se 1 (by rfl) ⟨1395941, by rfl⟩ : syracuseStep 1861255 = 2791883) B2791883
theorem B13223695 : Blo 1547471 13223695 := bstep (se 1 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 13223695 = 19835543) B19835543
theorem B8816435 : Blo 1547471 8816435 := bstep (se 1 (by rfl) ⟨6612326, by rfl⟩ : syracuseStep 8816435 = 13224653) B13224653
theorem B3721079 : Blo 1547471 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B1959815 : Blo 1547471 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B3483539 : Blo 1547471 3483539 := bstep (se 1 (by rfl) ⟨2612654, by rfl⟩ : syracuseStep 3483539 = 5225309) B5225309
theorem B5228441 : Blo 1547471 5228441 := bstep (se 2 (by rfl) ⟨1960665, by rfl⟩ : syracuseStep 5228441 = 3921331) B3921331
theorem B3483593 : Blo 1547471 3483593 := bstep (se 2 (by rfl) ⟨1306347, by rfl⟩ : syracuseStep 3483593 = 2612695) B2612695
theorem B7440407 : Blo 1547471 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B3918091 : Blo 1547471 3918091 := bstep (se 1 (by rfl) ⟨2938568, by rfl⟩ : syracuseStep 3918091 = 5877137) B5877137
theorem B13232443 : Blo 1547471 13232443 := bstep (se 1 (by rfl) ⟨9924332, by rfl⟩ : syracuseStep 13232443 = 19848665) B19848665
theorem B4958579 : Blo 1547471 4958579 := bstep (se 1 (by rfl) ⟨3718934, by rfl⟩ : syracuseStep 4958579 = 7437869) B7437869
theorem B3918233 : Blo 1547471 3918233 := bstep (se 2 (by rfl) ⟨1469337, by rfl⟩ : syracuseStep 3918233 = 2938675) B2938675
theorem B7842257 : Blo 1547471 7842257 := bstep (se 2 (by rfl) ⟨2940846, by rfl⟩ : syracuseStep 7842257 = 5881693) B5881693
theorem B1960463 : Blo 1547471 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B2091577 : Blo 1547471 2091577 := bstep (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) B1568683
theorem B3918395 : Blo 1547471 3918395 := bstep (se 1 (by rfl) ⟨2938796, by rfl⟩ : syracuseStep 3918395 = 5877593) B5877593
theorem B13232717 : Blo 1547471 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B5229143 : Blo 1547471 5229143 := bstep (se 1 (by rfl) ⟨3921857, by rfl⟩ : syracuseStep 5229143 = 7843715) B7843715
theorem B9423479 : Blo 1547471 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B3484295 : Blo 1547471 3484295 := bstep (se 1 (by rfl) ⟨2613221, by rfl⟩ : syracuseStep 3484295 = 5226443) B5226443
theorem B4958977 : Blo 1547471 4958977 := bstep (se 2 (by rfl) ⟨1859616, by rfl⟩ : syracuseStep 4958977 = 3719233) B3719233
theorem B5655329 : Blo 1547471 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B14887729 : Blo 1547471 14887729 := bstep (se 2 (by rfl) ⟨5582898, by rfl⟩ : syracuseStep 14887729 = 11165797) B11165797
theorem B3484475 : Blo 1547471 3484475 := bstep (se 1 (by rfl) ⟨2613356, by rfl⟩ : syracuseStep 3484475 = 5226713) B5226713
theorem B2321225 : Blo 1547471 2321225 := bstep (se 2 (by rfl) ⟨870459, by rfl⟩ : syracuseStep 2321225 = 1740919) B1740919
theorem B4959091 : Blo 1547471 4959091 := bstep (se 1 (by rfl) ⟨3719318, by rfl⟩ : syracuseStep 4959091 = 7438637) B7438637
theorem B6278023 : Blo 1547471 6278023 := bstep (se 1 (by rfl) ⟨4708517, by rfl⟩ : syracuseStep 6278023 = 9417035) B9417035
theorem B3918739 : Blo 1547471 3918739 := bstep (se 1 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 3918739 = 5878109) B5878109
theorem B3484601 : Blo 1547471 3484601 := bstep (se 2 (by rfl) ⟨1306725, by rfl⟩ : syracuseStep 3484601 = 2613451) B2613451
theorem B2321339 : Blo 1547471 2321339 := bstep (se 1 (by rfl) ⟨1741004, by rfl⟩ : syracuseStep 2321339 = 3482009) B3482009
theorem B2321399 : Blo 1547471 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B2354167 : Blo 1547471 2354167 := bstep (se 1 (by rfl) ⟨1765625, by rfl⟩ : syracuseStep 2354167 = 3531251) B3531251
theorem B2321423 : Blo 1547471 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B3918881 : Blo 1547471 3918881 := bstep (se 2 (by rfl) ⟨1469580, by rfl⟩ : syracuseStep 3918881 = 2939161) B2939161
theorem B2321465 : Blo 1547471 2321465 := bstep (se 2 (by rfl) ⟨870549, by rfl⟩ : syracuseStep 2321465 = 1741099) B1741099
theorem B14126167 : Blo 1547471 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B2321543 : Blo 1547471 2321543 := bstep (se 1 (by rfl) ⟨1741157, by rfl⟩ : syracuseStep 2321543 = 3482315) B3482315
theorem B2321579 : Blo 1547471 2321579 := bstep (se 1 (by rfl) ⟨1741184, by rfl⟩ : syracuseStep 2321579 = 3482369) B3482369
theorem B2321609 : Blo 1547471 2321609 := bstep (se 2 (by rfl) ⟨870603, by rfl⟩ : syracuseStep 2321609 = 1741207) B1741207
theorem B8817893 : Blo 1547471 8817893 := bstep (se 4 (by rfl) ⟨826677, by rfl⟩ : syracuseStep 8817893 = 1653355) B1653355
theorem B3484943 : Blo 1547471 3484943 := bstep (se 1 (by rfl) ⟨2613707, by rfl⟩ : syracuseStep 3484943 = 5227415) B5227415
theorem B3484961 : Blo 1547471 3484961 := bstep (se 2 (by rfl) ⟨1306860, by rfl⟩ : syracuseStep 3484961 = 2613721) B2613721
theorem B2321723 : Blo 1547471 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B7441753 : Blo 1547471 7441753 := bstep (se 2 (by rfl) ⟨2790657, by rfl⟩ : syracuseStep 7441753 = 5581315) B5581315
theorem B5877107 : Blo 1547471 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B2321783 : Blo 1547471 2321783 := bstep (se 1 (by rfl) ⟨1741337, by rfl⟩ : syracuseStep 2321783 = 3482675) B3482675
theorem B2321807 : Blo 1547471 2321807 := bstep (se 1 (by rfl) ⟨1741355, by rfl⟩ : syracuseStep 2321807 = 3482711) B3482711
theorem B1789327 : Blo 1547471 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B9416083 : Blo 1547471 9416083 := bstep (se 1 (by rfl) ⟨7062062, by rfl⟩ : syracuseStep 9416083 = 14124125) B14124125
theorem B2321849 : Blo 1547471 2321849 := bstep (se 2 (by rfl) ⟨870693, by rfl⟩ : syracuseStep 2321849 = 1741387) B1741387
theorem B2321927 : Blo 1547471 2321927 := bstep (se 1 (by rfl) ⟨1741445, by rfl⟩ : syracuseStep 2321927 = 3482891) B3482891
theorem B4410895 : Blo 1547471 4410895 := bstep (se 1 (by rfl) ⟨3308171, by rfl⟩ : syracuseStep 4410895 = 6616343) B6616343
theorem B2321963 : Blo 1547471 2321963 := bstep (se 1 (by rfl) ⟨1741472, by rfl⟩ : syracuseStep 2321963 = 3482945) B3482945
theorem B2321993 : Blo 1547471 2321993 := bstep (se 2 (by rfl) ⟨870747, by rfl⟩ : syracuseStep 2321993 = 1741495) B1741495
theorem B3485303 : Blo 1547471 3485303 := bstep (se 1 (by rfl) ⟨2613977, by rfl⟩ : syracuseStep 3485303 = 5227955) B5227955
theorem B3772051 : Blo 1547471 3772051 := bstep (se 1 (by rfl) ⟨2829038, by rfl⟩ : syracuseStep 3772051 = 5658077) B5658077
theorem B2322107 : Blo 1547471 2322107 := bstep (se 1 (by rfl) ⟨1741580, by rfl⟩ : syracuseStep 2322107 = 3483161) B3483161
theorem B2322167 : Blo 1547471 2322167 := bstep (se 1 (by rfl) ⟨1741625, by rfl⟩ : syracuseStep 2322167 = 3483251) B3483251
theorem B2322191 : Blo 1547471 2322191 := bstep (se 1 (by rfl) ⟨1741643, by rfl⟩ : syracuseStep 2322191 = 3483287) B3483287
theorem B4411169 : Blo 1547471 4411169 := bstep (se 2 (by rfl) ⟨1654188, by rfl⟩ : syracuseStep 4411169 = 3308377) B3308377
theorem B3485483 : Blo 1547471 3485483 := bstep (se 1 (by rfl) ⟨2614112, by rfl⟩ : syracuseStep 3485483 = 5228225) B5228225
theorem B2322233 : Blo 1547471 2322233 := bstep (se 2 (by rfl) ⟨870837, by rfl⟩ : syracuseStep 2322233 = 1741675) B1741675
theorem B2322311 : Blo 1547471 2322311 := bstep (se 1 (by rfl) ⟨1741733, by rfl⟩ : syracuseStep 2322311 = 3483467) B3483467
theorem B8818577 : Blo 1547471 8818577 := bstep (se 2 (by rfl) ⟨3306966, by rfl⟩ : syracuseStep 8818577 = 6613933) B6613933
theorem B16748441 : Blo 1547471 16748441 := bstep (se 2 (by rfl) ⟨6280665, by rfl⟩ : syracuseStep 16748441 = 12561331) B12561331
theorem B2322347 : Blo 1547471 2322347 := bstep (se 1 (by rfl) ⟨1741760, by rfl⟩ : syracuseStep 2322347 = 3483521) B3483521
theorem B2322377 : Blo 1547471 2322377 := bstep (se 2 (by rfl) ⟨870891, by rfl⟩ : syracuseStep 2322377 = 1741783) B1741783
theorem B3919873 : Blo 1547471 3919873 := bstep (se 2 (by rfl) ⟨1469952, by rfl⟩ : syracuseStep 3919873 = 2939905) B2939905
theorem B2322491 : Blo 1547471 2322491 := bstep (se 1 (by rfl) ⟨1741868, by rfl⟩ : syracuseStep 2322491 = 3483737) B3483737
theorem B2322551 : Blo 1547471 2322551 := bstep (se 1 (by rfl) ⟨1741913, by rfl⟩ : syracuseStep 2322551 = 3483827) B3483827
theorem B2322575 : Blo 1547471 2322575 := bstep (se 1 (by rfl) ⟨1741931, by rfl⟩ : syracuseStep 2322575 = 3483863) B3483863
theorem B3485843 : Blo 1547471 3485843 := bstep (se 1 (by rfl) ⟨2614382, by rfl⟩ : syracuseStep 3485843 = 5228765) B5228765
theorem B2322617 : Blo 1547471 2322617 := bstep (se 2 (by rfl) ⟨870981, by rfl⟩ : syracuseStep 2322617 = 1741963) B1741963
theorem B3485897 : Blo 1547471 3485897 := bstep (se 2 (by rfl) ⟨1307211, by rfl⟩ : syracuseStep 3485897 = 2614423) B2614423
theorem B1741063 : Blo 1547471 1741063 := bstep (se 1 (by rfl) ⟨1305797, by rfl⟩ : syracuseStep 1741063 = 2611595) B2611595
theorem B2322695 : Blo 1547471 2322695 := bstep (se 1 (by rfl) ⟨1742021, by rfl⟩ : syracuseStep 2322695 = 3484043) B3484043
theorem B2322731 : Blo 1547471 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B2322761 : Blo 1547471 2322761 := bstep (se 2 (by rfl) ⟨871035, by rfl⟩ : syracuseStep 2322761 = 1742071) B1742071
theorem B16740701 : Blo 1547471 16740701 := bstep (se 3 (by rfl) ⟨3138881, by rfl⟩ : syracuseStep 16740701 = 6277763) B6277763
theorem B5222771 : Blo 1547471 5222771 := bstep (se 1 (by rfl) ⟨3917078, by rfl⟩ : syracuseStep 5222771 = 7834157) B7834157
theorem B14872967 : Blo 1547471 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B1741243 : Blo 1547471 1741243 := bstep (se 1 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 1741243 = 2611865) B2611865
theorem B2322875 : Blo 1547471 2322875 := bstep (se 1 (by rfl) ⟨1742156, by rfl⟩ : syracuseStep 2322875 = 3484313) B3484313
theorem B2322935 : Blo 1547471 2322935 := bstep (se 1 (by rfl) ⟨1742201, by rfl⟩ : syracuseStep 2322935 = 3484403) B3484403
theorem B2322959 : Blo 1547471 2322959 := bstep (se 1 (by rfl) ⟨1742219, by rfl⟩ : syracuseStep 2322959 = 3484439) B3484439
theorem B11751965 : Blo 1547471 11751965 := bstep (se 3 (by rfl) ⟨2203493, by rfl⟩ : syracuseStep 11751965 = 4406987) B4406987
theorem B2323001 : Blo 1547471 2323001 := bstep (se 2 (by rfl) ⟨871125, by rfl⟩ : syracuseStep 2323001 = 1742251) B1742251
theorem B3920471 : Blo 1547471 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B2323079 : Blo 1547471 2323079 := bstep (se 1 (by rfl) ⟨1742309, by rfl⟩ : syracuseStep 2323079 = 3484619) B3484619
theorem B2323115 : Blo 1547471 2323115 := bstep (se 1 (by rfl) ⟨1742336, by rfl⟩ : syracuseStep 2323115 = 3484673) B3484673
theorem B2323145 : Blo 1547471 2323145 := bstep (se 2 (by rfl) ⟨871179, by rfl⟩ : syracuseStep 2323145 = 1742359) B1742359
theorem B4412171 : Blo 1547471 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B3920683 : Blo 1547471 3920683 := bstep (se 1 (by rfl) ⟨2940512, by rfl⟩ : syracuseStep 3920683 = 5881025) B5881025
theorem B2323259 : Blo 1547471 2323259 := bstep (se 1 (by rfl) ⟨1742444, by rfl⟩ : syracuseStep 2323259 = 3484889) B3484889
theorem B2323319 : Blo 1547471 2323319 := bstep (se 1 (by rfl) ⟨1742489, by rfl⟩ : syracuseStep 2323319 = 3484979) B3484979
theorem B1741711 : Blo 1547471 1741711 := bstep (se 1 (by rfl) ⟨1306283, by rfl⟩ : syracuseStep 1741711 = 2612567) B2612567
theorem B2323343 : Blo 1547471 2323343 := bstep (se 1 (by rfl) ⟨1742507, by rfl⟩ : syracuseStep 2323343 = 3485015) B3485015
theorem B8819603 : Blo 1547471 8819603 := bstep (se 1 (by rfl) ⟨6614702, by rfl⟩ : syracuseStep 8819603 = 13229405) B13229405
theorem B2479033 : Blo 1547471 2479033 := bstep (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) B1859275
theorem B2323385 : Blo 1547471 2323385 := bstep (se 2 (by rfl) ⟨871269, by rfl⟩ : syracuseStep 2323385 = 1742539) B1742539
theorem B3920825 : Blo 1547471 3920825 := bstep (se 2 (by rfl) ⟨1470309, by rfl⟩ : syracuseStep 3920825 = 2940619) B2940619
theorem B2323463 : Blo 1547471 2323463 := bstep (se 1 (by rfl) ⟨1742597, by rfl⟩ : syracuseStep 2323463 = 3485195) B3485195
theorem B3306539 : Blo 1547471 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B2323499 : Blo 1547471 2323499 := bstep (se 1 (by rfl) ⟨1742624, by rfl⟩ : syracuseStep 2323499 = 3485249) B3485249
theorem B19846205 : Blo 1547471 19846205 := bstep (se 3 (by rfl) ⟨3721163, by rfl⟩ : syracuseStep 19846205 = 7442327) B7442327
theorem B2323529 : Blo 1547471 2323529 := bstep (se 2 (by rfl) ⟨871323, by rfl⟩ : syracuseStep 2323529 = 1742647) B1742647
theorem B2323643 : Blo 1547471 2323643 := bstep (se 1 (by rfl) ⟨1742732, by rfl⟩ : syracuseStep 2323643 = 3485465) B3485465
theorem B2323703 : Blo 1547471 2323703 := bstep (se 1 (by rfl) ⟨1742777, by rfl⟩ : syracuseStep 2323703 = 3485555) B3485555
theorem B2323727 : Blo 1547471 2323727 := bstep (se 1 (by rfl) ⟨1742795, by rfl⟩ : syracuseStep 2323727 = 3485591) B3485591
theorem B2323769 : Blo 1547471 2323769 := bstep (se 2 (by rfl) ⟨871413, by rfl⟩ : syracuseStep 2323769 = 1742827) B1742827
theorem B2790715 : Blo 1547471 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B1742215 : Blo 1547471 1742215 := bstep (se 1 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 1742215 = 2613323) B2613323
theorem B2323847 : Blo 1547471 2323847 := bstep (se 1 (by rfl) ⟨1742885, by rfl⟩ : syracuseStep 2323847 = 3485771) B3485771
theorem B7837073 : Blo 1547471 7837073 := bstep (se 2 (by rfl) ⟨2938902, by rfl⟩ : syracuseStep 7837073 = 5877805) B5877805
theorem B3306899 : Blo 1547471 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B2323883 : Blo 1547471 2323883 := bstep (se 1 (by rfl) ⟨1742912, by rfl⟩ : syracuseStep 2323883 = 3485825) B3485825
theorem B2323913 : Blo 1547471 2323913 := bstep (se 2 (by rfl) ⟨871467, by rfl⟩ : syracuseStep 2323913 = 1742935) B1742935
theorem B5879249 : Blo 1547471 5879249 := bstep (se 2 (by rfl) ⟨2204718, by rfl⟩ : syracuseStep 5879249 = 4409437) B4409437
theorem B14890499 : Blo 1547471 14890499 := bstep (se 1 (by rfl) ⟨11167874, by rfl⟩ : syracuseStep 14890499 = 22335749) B22335749
theorem B1914427 : Blo 1547471 1914427 := bstep (se 1 (by rfl) ⟨1435820, by rfl⟩ : syracuseStep 1914427 = 2871641) B2871641
theorem B1742395 : Blo 1547471 1742395 := bstep (se 1 (by rfl) ⟨1306796, by rfl⟩ : syracuseStep 1742395 = 2613593) B2613593
theorem B2324027 : Blo 1547471 2324027 := bstep (se 1 (by rfl) ⟨1743020, by rfl⟩ : syracuseStep 2324027 = 3486041) B3486041
theorem B4961911 : Blo 1547471 4961911 := bstep (se 1 (by rfl) ⟨3721433, by rfl⟩ : syracuseStep 4961911 = 7442867) B7442867
theorem B2324087 : Blo 1547471 2324087 := bstep (se 1 (by rfl) ⟨1743065, by rfl⟩ : syracuseStep 2324087 = 3486131) B3486131
theorem B2479751 : Blo 1547471 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B2324111 : Blo 1547471 2324111 := bstep (se 1 (by rfl) ⟨1743083, by rfl⟩ : syracuseStep 2324111 = 3486167) B3486167
theorem B2324153 : Blo 1547471 2324153 := bstep (se 2 (by rfl) ⟨871557, by rfl⟩ : syracuseStep 2324153 = 1743115) B1743115
theorem B4028105 : Blo 1547471 4028105 := bstep (se 2 (by rfl) ⟨1510539, by rfl⟩ : syracuseStep 4028105 = 3021079) B3021079
theorem B5879567 : Blo 1547471 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B37689239 : Blo 1547471 37689239 := bstep (se 1 (by rfl) ⟨28266929, by rfl⟩ : syracuseStep 37689239 = 56533859) B56533859
theorem B3921817 : Blo 1547471 3921817 := bstep (se 2 (by rfl) ⟨1470681, by rfl⟩ : syracuseStep 3921817 = 2941363) B2941363
theorem B8722397 : Blo 1547471 8722397 := bstep (se 3 (by rfl) ⟨1635449, by rfl⟩ : syracuseStep 8722397 = 3270899) B3270899
theorem B1742863 : Blo 1547471 1742863 := bstep (se 1 (by rfl) ⟨1307147, by rfl⟩ : syracuseStep 1742863 = 2614295) B2614295
theorem B5961757 : Blo 1547471 5961757 := bstep (se 3 (by rfl) ⟨1117829, by rfl⟩ : syracuseStep 5961757 = 2235659) B2235659
theorem B3921979 : Blo 1547471 3921979 := bstep (se 1 (by rfl) ⟨2941484, by rfl⟩ : syracuseStep 3921979 = 5882969) B5882969
theorem B2480263 : Blo 1547471 2480263 := bstep (se 1 (by rfl) ⟨1860197, by rfl⟩ : syracuseStep 2480263 = 3720395) B3720395
theorem B275224853 : Blo 1547471 275224853 := bstep (se 6 (by rfl) ⟨6450582, by rfl⟩ : syracuseStep 275224853 = 12901165) B12901165
theorem B7354657 : Blo 1547471 7354657 := bstep (se 2 (by rfl) ⟨2757996, by rfl⟩ : syracuseStep 7354657 = 5515993) B5515993
theorem B2791739 : Blo 1547471 2791739 := bstep (se 1 (by rfl) ⟨2093804, by rfl⟩ : syracuseStep 2791739 = 4187609) B4187609
theorem B5962099 : Blo 1547471 5962099 := bstep (se 1 (by rfl) ⟨4471574, by rfl⟩ : syracuseStep 5962099 = 8943149) B8943149
theorem B2939321 : Blo 1547471 2939321 := bstep (se 2 (by rfl) ⟨1102245, by rfl⟩ : syracuseStep 2939321 = 2204491) B2204491
theorem B2611831 : Blo 1547471 2611831 := bstep (se 1 (by rfl) ⟨1958873, by rfl⟩ : syracuseStep 2611831 = 3917747) B3917747
theorem B14875427 : Blo 1547471 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B9927461 : Blo 1547471 9927461 := bstep (se 4 (by rfl) ⟨930699, by rfl⟩ : syracuseStep 9927461 = 1861399) B1861399
theorem B2685739 : Blo 1547471 2685739 := bstep (se 1 (by rfl) ⟨2014304, by rfl⟩ : syracuseStep 2685739 = 4028609) B4028609
theorem B13220657 : Blo 1547471 13220657 := bstep (se 2 (by rfl) ⟨4957746, by rfl⟩ : syracuseStep 13220657 = 9915493) B9915493
theorem B2612027 : Blo 1547471 2612027 := bstep (se 1 (by rfl) ⟨1959020, by rfl⟩ : syracuseStep 2612027 = 3918041) B3918041
theorem B3578759 : Blo 1547471 3578759 := bstep (se 1 (by rfl) ⟨2684069, by rfl⟩ : syracuseStep 3578759 = 5368139) B5368139
theorem B5225363 : Blo 1547471 5225363 := bstep (se 1 (by rfl) ⟨3919022, by rfl⟩ : syracuseStep 5225363 = 7838045) B7838045
theorem B5962681 : Blo 1547471 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B5577929 : Blo 1547471 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B2612425 : Blo 1547471 2612425 := bstep (se 2 (by rfl) ⟨979659, by rfl⟩ : syracuseStep 2612425 = 1959319) B1959319
theorem B1547527 : Blo 1547471 1547527 := bstep (se 1 (by rfl) ⟨1160645, by rfl⟩ : syracuseStep 1547527 = 2321291) B2321291
theorem B2014471 : Blo 1547471 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B1547535 : Blo 1547471 1547535 := bstep (se 1 (by rfl) ⟨1160651, by rfl⟩ : syracuseStep 1547535 = 2321303) B2321303
theorem B1547579 : Blo 1547471 1547579 := bstep (se 1 (by rfl) ⟨1160684, by rfl⟩ : syracuseStep 1547579 = 2321369) B2321369
theorem B1547655 : Blo 1547471 1547655 := bstep (se 1 (by rfl) ⟨1160741, by rfl⟩ : syracuseStep 1547655 = 2321483) B2321483
theorem B1547663 : Blo 1547471 1547663 := bstep (se 1 (by rfl) ⟨1160747, by rfl⟩ : syracuseStep 1547663 = 2321495) B2321495
theorem B13221305 : Blo 1547471 13221305 := bstep (se 2 (by rfl) ⟨4957989, by rfl⟩ : syracuseStep 13221305 = 9915979) B9915979
theorem B1547707 : Blo 1547471 1547707 := bstep (se 1 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 1547707 = 2321561) B2321561
theorem B7839179 : Blo 1547471 7839179 := bstep (se 1 (by rfl) ⟨5879384, by rfl⟩ : syracuseStep 7839179 = 11758769) B11758769
theorem B60374477 : Blo 1547471 60374477 := bstep (se 3 (by rfl) ⟨11320214, by rfl⟩ : syracuseStep 60374477 = 22640429) B22640429
theorem B1547783 : Blo 1547471 1547783 := bstep (se 1 (by rfl) ⟨1160837, by rfl⟩ : syracuseStep 1547783 = 2321675) B2321675
theorem B4406795 : Blo 1547471 4406795 := bstep (se 1 (by rfl) ⟨3305096, by rfl⟩ : syracuseStep 4406795 = 6610193) B6610193
theorem B1547791 : Blo 1547471 1547791 := bstep (se 1 (by rfl) ⟨1160843, by rfl⟩ : syracuseStep 1547791 = 2321687) B2321687
theorem B1547835 : Blo 1547471 1547835 := bstep (se 1 (by rfl) ⟨1160876, by rfl⟩ : syracuseStep 1547835 = 2321753) B2321753
theorem B2940475 : Blo 1547471 2940475 := bstep (se 1 (by rfl) ⟨2205356, by rfl⟩ : syracuseStep 2940475 = 4410713) B4410713
theorem B12557891 : Blo 1547471 12557891 := bstep (se 1 (by rfl) ⟨9418418, by rfl⟩ : syracuseStep 12557891 = 18836837) B18836837
theorem B1547911 : Blo 1547471 1547911 := bstep (se 1 (by rfl) ⟨1160933, by rfl⟩ : syracuseStep 1547911 = 2321867) B2321867
theorem B3530375 : Blo 1547471 3530375 := bstep (se 1 (by rfl) ⟨2647781, by rfl⟩ : syracuseStep 3530375 = 5295563) B5295563
theorem B1547919 : Blo 1547471 1547919 := bstep (se 1 (by rfl) ⟨1160939, by rfl⟩ : syracuseStep 1547919 = 2321879) B2321879
theorem B1547963 : Blo 1547471 1547963 := bstep (se 1 (by rfl) ⟨1160972, by rfl⟩ : syracuseStep 1547963 = 2321945) B2321945
theorem B10591973 : Blo 1547471 10591973 := bstep (se 4 (by rfl) ⟨992997, by rfl⟩ : syracuseStep 10591973 = 1985995) B1985995
theorem B1548039 : Blo 1547471 1548039 := bstep (se 1 (by rfl) ⟨1161029, by rfl⟩ : syracuseStep 1548039 = 2322059) B2322059
theorem B1548047 : Blo 1547471 1548047 := bstep (se 1 (by rfl) ⟨1161035, by rfl⟩ : syracuseStep 1548047 = 2322071) B2322071
theorem B7839503 : Blo 1547471 7839503 := bstep (se 1 (by rfl) ⟨5879627, by rfl⟩ : syracuseStep 7839503 = 11759255) B11759255
theorem B1654543 : Blo 1547471 1654543 := bstep (se 1 (by rfl) ⟨1240907, by rfl⟩ : syracuseStep 1654543 = 2481815) B2481815
theorem B1548091 : Blo 1547471 1548091 := bstep (se 1 (by rfl) ⟨1161068, by rfl⟩ : syracuseStep 1548091 = 2322137) B2322137
theorem B1548167 : Blo 1547471 1548167 := bstep (se 1 (by rfl) ⟨1161125, by rfl⟩ : syracuseStep 1548167 = 2322251) B2322251
theorem B2613127 : Blo 1547471 2613127 := bstep (se 1 (by rfl) ⟨1959845, by rfl⟩ : syracuseStep 2613127 = 3919691) B3919691
theorem B1548175 : Blo 1547471 1548175 := bstep (se 1 (by rfl) ⟨1161131, by rfl⟩ : syracuseStep 1548175 = 2322263) B2322263
theorem B8814521 : Blo 1547471 8814521 := bstep (se 2 (by rfl) ⟨3305445, by rfl⟩ : syracuseStep 8814521 = 6610891) B6610891
theorem B1548219 : Blo 1547471 1548219 := bstep (se 1 (by rfl) ⟨1161164, by rfl⟩ : syracuseStep 1548219 = 2322329) B2322329
theorem B5226497 : Blo 1547471 5226497 := bstep (se 2 (by rfl) ⟨1959936, by rfl⟩ : syracuseStep 5226497 = 3919873) B3919873
theorem B1548327 : Blo 1547471 1548327 := bstep (se 1 (by rfl) ⟨1161245, by rfl⟩ : syracuseStep 1548327 = 2322491) B2322491
theorem B42360893 : Blo 1547471 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B1548367 : Blo 1547471 1548367 := bstep (se 1 (by rfl) ⟨1161275, by rfl⟩ : syracuseStep 1548367 = 2322551) B2322551
theorem B1548383 : Blo 1547471 1548383 := bstep (se 1 (by rfl) ⟨1161287, by rfl⟩ : syracuseStep 1548383 = 2322575) B2322575
theorem B1548411 : Blo 1547471 1548411 := bstep (se 1 (by rfl) ⟨1161308, by rfl⟩ : syracuseStep 1548411 = 2322617) B2322617
theorem B1548463 : Blo 1547471 1548463 := bstep (se 1 (by rfl) ⟨1161347, by rfl⟩ : syracuseStep 1548463 = 2322695) B2322695
theorem B1548487 : Blo 1547471 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B1548507 : Blo 1547471 1548507 := bstep (se 1 (by rfl) ⟨1161380, by rfl⟩ : syracuseStep 1548507 = 2322761) B2322761
theorem B3481847 : Blo 1547471 3481847 := bstep (se 1 (by rfl) ⟨2611385, by rfl⟩ : syracuseStep 3481847 = 5222771) B5222771
theorem B1548583 : Blo 1547471 1548583 := bstep (se 1 (by rfl) ⟨1161437, by rfl⟩ : syracuseStep 1548583 = 2322875) B2322875
theorem B1548623 : Blo 1547471 1548623 := bstep (se 1 (by rfl) ⟨1161467, by rfl⟩ : syracuseStep 1548623 = 2322935) B2322935
theorem B1548639 : Blo 1547471 1548639 := bstep (se 1 (by rfl) ⟨1161479, by rfl⟩ : syracuseStep 1548639 = 2322959) B2322959
theorem B1548667 : Blo 1547471 1548667 := bstep (se 1 (by rfl) ⟨1161500, by rfl⟩ : syracuseStep 1548667 = 2323001) B2323001
theorem B8814977 : Blo 1547471 8814977 := bstep (se 2 (by rfl) ⟨3305616, by rfl⟩ : syracuseStep 8814977 = 6611233) B6611233
theorem B2613647 : Blo 1547471 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B1548719 : Blo 1547471 1548719 := bstep (se 1 (by rfl) ⟨1161539, by rfl⟩ : syracuseStep 1548719 = 2323079) B2323079
theorem B1548743 : Blo 1547471 1548743 := bstep (se 1 (by rfl) ⟨1161557, by rfl⟩ : syracuseStep 1548743 = 2323115) B2323115
theorem B1548763 : Blo 1547471 1548763 := bstep (se 1 (by rfl) ⟨1161572, by rfl⟩ : syracuseStep 1548763 = 2323145) B2323145
theorem B2941447 : Blo 1547471 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B1548839 : Blo 1547471 1548839 := bstep (se 1 (by rfl) ⟨1161629, by rfl⟩ : syracuseStep 1548839 = 2323259) B2323259
theorem B1548879 : Blo 1547471 1548879 := bstep (se 1 (by rfl) ⟨1161659, by rfl⟩ : syracuseStep 1548879 = 2323319) B2323319
theorem B1548895 : Blo 1547471 1548895 := bstep (se 1 (by rfl) ⟨1161671, by rfl⟩ : syracuseStep 1548895 = 2323343) B2323343
theorem B1548923 : Blo 1547471 1548923 := bstep (se 1 (by rfl) ⟨1161692, by rfl⟩ : syracuseStep 1548923 = 2323385) B2323385
theorem B2613883 : Blo 1547471 2613883 := bstep (se 1 (by rfl) ⟨1960412, by rfl⟩ : syracuseStep 2613883 = 3920825) B3920825
theorem B1548975 : Blo 1547471 1548975 := bstep (se 1 (by rfl) ⟨1161731, by rfl⟩ : syracuseStep 1548975 = 2323463) B2323463
theorem B1548999 : Blo 1547471 1548999 := bstep (se 1 (by rfl) ⟨1161749, by rfl⟩ : syracuseStep 1548999 = 2323499) B2323499
theorem B13230803 : Blo 1547471 13230803 := bstep (se 1 (by rfl) ⟨9923102, by rfl⟩ : syracuseStep 13230803 = 19846205) B19846205
theorem B1549019 : Blo 1547471 1549019 := bstep (se 1 (by rfl) ⟨1161764, by rfl⟩ : syracuseStep 1549019 = 2323529) B2323529
theorem B1549095 : Blo 1547471 1549095 := bstep (se 1 (by rfl) ⟨1161821, by rfl⟩ : syracuseStep 1549095 = 2323643) B2323643
theorem B5227307 : Blo 1547471 5227307 := bstep (se 1 (by rfl) ⟨3920480, by rfl⟩ : syracuseStep 5227307 = 7840961) B7840961
theorem B3482441 : Blo 1547471 3482441 := bstep (se 2 (by rfl) ⟨1305915, by rfl⟩ : syracuseStep 3482441 = 2611831) B2611831
theorem B1549135 : Blo 1547471 1549135 := bstep (se 1 (by rfl) ⟨1161851, by rfl⟩ : syracuseStep 1549135 = 2323703) B2323703
theorem B1549151 : Blo 1547471 1549151 := bstep (se 1 (by rfl) ⟨1161863, by rfl⟩ : syracuseStep 1549151 = 2323727) B2323727
theorem B1549179 : Blo 1547471 1549179 := bstep (se 1 (by rfl) ⟨1161884, by rfl⟩ : syracuseStep 1549179 = 2323769) B2323769
theorem B1549231 : Blo 1547471 1549231 := bstep (se 1 (by rfl) ⟨1161923, by rfl⟩ : syracuseStep 1549231 = 2323847) B2323847
theorem B2204599 : Blo 1547471 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B1549255 : Blo 1547471 1549255 := bstep (se 1 (by rfl) ⟨1161941, by rfl⟩ : syracuseStep 1549255 = 2323883) B2323883
theorem B1549275 : Blo 1547471 1549275 := bstep (se 1 (by rfl) ⟨1161956, by rfl⟩ : syracuseStep 1549275 = 2323913) B2323913
theorem B6611969 : Blo 1547471 6611969 := bstep (se 2 (by rfl) ⟨2479488, by rfl⟩ : syracuseStep 6611969 = 4958977) B4958977
theorem B1549351 : Blo 1547471 1549351 := bstep (se 1 (by rfl) ⟨1162013, by rfl⟩ : syracuseStep 1549351 = 2324027) B2324027
theorem B5227577 : Blo 1547471 5227577 := bstep (se 2 (by rfl) ⟨1960341, by rfl⟩ : syracuseStep 5227577 = 3920683) B3920683
theorem B3580985 : Blo 1547471 3580985 := bstep (se 2 (by rfl) ⟨1342869, by rfl⟩ : syracuseStep 3580985 = 2685739) B2685739
theorem B19850305 : Blo 1547471 19850305 := bstep (se 2 (by rfl) ⟨7443864, by rfl⟩ : syracuseStep 19850305 = 14887729) B14887729
theorem B1549391 : Blo 1547471 1549391 := bstep (se 1 (by rfl) ⟨1162043, by rfl⟩ : syracuseStep 1549391 = 2324087) B2324087
theorem B1549407 : Blo 1547471 1549407 := bstep (se 1 (by rfl) ⟨1162055, by rfl⟩ : syracuseStep 1549407 = 2324111) B2324111
theorem B1549435 : Blo 1547471 1549435 := bstep (se 1 (by rfl) ⟨1162076, by rfl⟩ : syracuseStep 1549435 = 2324153) B2324153
theorem B6612121 : Blo 1547471 6612121 := bstep (se 2 (by rfl) ⟨2479545, by rfl⟩ : syracuseStep 6612121 = 4959091) B4959091
theorem B25126159 : Blo 1547471 25126159 := bstep (se 1 (by rfl) ⟨18844619, by rfl⟩ : syracuseStep 25126159 = 37689239) B37689239
theorem B5227901 : Blo 1547471 5227901 := bstep (se 3 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 5227901 = 1960463) B1960463
theorem B18834889 : Blo 1547471 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B39224837 : Blo 1547471 39224837 := bstep (se 4 (by rfl) ⟨3677328, by rfl⟩ : syracuseStep 39224837 = 7354657) B7354657
theorem B1861159 : Blo 1547471 1861159 := bstep (se 1 (by rfl) ⟨1395869, by rfl⟩ : syracuseStep 1861159 = 2791739) B2791739
theorem B3483233 : Blo 1547471 3483233 := bstep (se 2 (by rfl) ⟨1306212, by rfl⟩ : syracuseStep 3483233 = 2612425) B2612425
theorem B1959547 : Blo 1547471 1959547 := bstep (se 1 (by rfl) ⟨1469660, by rfl⟩ : syracuseStep 1959547 = 2939321) B2939321
theorem B5228171 : Blo 1547471 5228171 := bstep (se 1 (by rfl) ⟨3921128, by rfl⟩ : syracuseStep 5228171 = 7842257) B7842257
theorem B3720953 : Blo 1547471 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B9922337 : Blo 1547471 9922337 := bstep (se 2 (by rfl) ⟨3720876, by rfl⟩ : syracuseStep 9922337 = 7441753) B7441753
theorem B2385769 : Blo 1547471 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B3770219 : Blo 1547471 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B10741613 : Blo 1547471 10741613 := bstep (se 3 (by rfl) ⟨2014052, by rfl⟩ : syracuseStep 10741613 = 4028105) B4028105
theorem B2385839 : Blo 1547471 2385839 := bstep (se 1 (by rfl) ⟨1789379, by rfl⟩ : syracuseStep 2385839 = 3578759) B3578759
theorem B3483575 : Blo 1547471 3483575 := bstep (se 1 (by rfl) ⟨2612681, by rfl⟩ : syracuseStep 3483575 = 5225363) B5225363
theorem B39667805 : Blo 1547471 39667805 := bstep (se 3 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 39667805 = 14875427) B14875427
theorem B11757797 : Blo 1547471 11757797 := bstep (se 4 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 11757797 = 2204587) B2204587
theorem B3918071 : Blo 1547471 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B40249651 : Blo 1547471 40249651 := bstep (se 1 (by rfl) ⟨30187238, by rfl⟩ : syracuseStep 40249651 = 60374477) B60374477
theorem B17631593 : Blo 1547471 17631593 := bstep (se 2 (by rfl) ⟨6611847, by rfl⟩ : syracuseStep 17631593 = 13223695) B13223695
theorem B2206057 : Blo 1547471 2206057 := bstep (se 2 (by rfl) ⟨827271, by rfl⟩ : syracuseStep 2206057 = 1654543) B1654543
theorem B2353583 : Blo 1547471 2353583 := bstep (se 1 (by rfl) ⟨1765187, by rfl⟩ : syracuseStep 2353583 = 3530375) B3530375
theorem B3484169 : Blo 1547471 3484169 := bstep (se 2 (by rfl) ⟨1306563, by rfl⟩ : syracuseStep 3484169 = 2613127) B2613127
theorem B5229089 : Blo 1547471 5229089 := bstep (se 2 (by rfl) ⟨1960908, by rfl⟩ : syracuseStep 5229089 = 3921817) B3921817
theorem B5876347 : Blo 1547471 5876347 := bstep (se 1 (by rfl) ⟨4407260, by rfl⟩ : syracuseStep 5876347 = 8814521) B8814521
theorem B7949009 : Blo 1547471 7949009 := bstep (se 2 (by rfl) ⟨2980878, by rfl⟩ : syracuseStep 7949009 = 5961757) B5961757
theorem B5229305 : Blo 1547471 5229305 := bstep (se 2 (by rfl) ⟨1960989, by rfl⟩ : syracuseStep 5229305 = 3921979) B3921979
theorem B8817437 : Blo 1547471 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B3484511 : Blo 1547471 3484511 := bstep (se 1 (by rfl) ⟨2613383, by rfl⟩ : syracuseStep 3484511 = 5226767) B5226767
theorem B1911659 : Blo 1547471 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B11160467 : Blo 1547471 11160467 := bstep (se 1 (by rfl) ⟨8370350, by rfl⟩ : syracuseStep 11160467 = 16740701) B16740701
theorem B9915311 : Blo 1547471 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B2321327 : Blo 1547471 2321327 := bstep (se 1 (by rfl) ⟨1740995, by rfl⟩ : syracuseStep 2321327 = 3481991) B3481991
theorem B7842743 : Blo 1547471 7842743 := bstep (se 1 (by rfl) ⟨5882057, by rfl⟩ : syracuseStep 7842743 = 11764115) B11764115
theorem B10210277 : Blo 1547471 10210277 := bstep (se 4 (by rfl) ⟨957213, by rfl⟩ : syracuseStep 10210277 = 1914427) B1914427
theorem B2321417 : Blo 1547471 2321417 := bstep (se 2 (by rfl) ⟨870531, by rfl⟩ : syracuseStep 2321417 = 1741063) B1741063
theorem B7834643 : Blo 1547471 7834643 := bstep (se 1 (by rfl) ⟨5875982, by rfl⟩ : syracuseStep 7834643 = 11751965) B11751965
theorem B3484691 : Blo 1547471 3484691 := bstep (se 1 (by rfl) ⟨2613518, by rfl⟩ : syracuseStep 3484691 = 5227037) B5227037
theorem B26471447 : Blo 1547471 26471447 := bstep (se 1 (by rfl) ⟨19853585, by rfl⟩ : syracuseStep 26471447 = 39707171) B39707171
theorem B2321447 : Blo 1547471 2321447 := bstep (se 1 (by rfl) ⟨1741085, by rfl⟩ : syracuseStep 2321447 = 3482171) B3482171
theorem B2321531 : Blo 1547471 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B7949465 : Blo 1547471 7949465 := bstep (se 2 (by rfl) ⟨2981049, by rfl⟩ : syracuseStep 7949465 = 5962099) B5962099
theorem B2321657 : Blo 1547471 2321657 := bstep (se 2 (by rfl) ⟨870621, by rfl⟩ : syracuseStep 2321657 = 1741243) B1741243
theorem B2321759 : Blo 1547471 2321759 := bstep (se 1 (by rfl) ⟨1741319, by rfl⟩ : syracuseStep 2321759 = 3482639) B3482639
theorem B4959593 : Blo 1547471 4959593 := bstep (se 2 (by rfl) ⟨1859847, by rfl⟩ : syracuseStep 4959593 = 3719695) B3719695
theorem B3485033 : Blo 1547471 3485033 := bstep (se 2 (by rfl) ⟨1306887, by rfl⟩ : syracuseStep 3485033 = 2613775) B2613775
theorem B2321771 : Blo 1547471 2321771 := bstep (se 1 (by rfl) ⟨1741328, by rfl⟩ : syracuseStep 2321771 = 3482657) B3482657
theorem B2788769 : Blo 1547471 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B6614567 : Blo 1547471 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B2321999 : Blo 1547471 2321999 := bstep (se 1 (by rfl) ⟨1741499, by rfl⟩ : syracuseStep 2321999 = 3482999) B3482999
theorem B3919499 : Blo 1547471 3919499 := bstep (se 1 (by rfl) ⟨2939624, by rfl⟩ : syracuseStep 3919499 = 5879249) B5879249
theorem B2322119 : Blo 1547471 2322119 := bstep (se 1 (by rfl) ⟨1741589, by rfl⟩ : syracuseStep 2322119 = 3483179) B3483179
theorem B3919711 : Blo 1547471 3919711 := bstep (se 1 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 3919711 = 5879567) B5879567
theorem B2322281 : Blo 1547471 2322281 := bstep (se 2 (by rfl) ⟨870855, by rfl⟩ : syracuseStep 2322281 = 1741711) B1741711
theorem B5877623 : Blo 1547471 5877623 := bstep (se 1 (by rfl) ⟨4408217, by rfl⟩ : syracuseStep 5877623 = 8816435) B8816435
theorem B3305377 : Blo 1547471 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B7950241 : Blo 1547471 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B2322359 : Blo 1547471 2322359 := bstep (se 1 (by rfl) ⟨1741769, by rfl⟩ : syracuseStep 2322359 = 3483539) B3483539
theorem B3485627 : Blo 1547471 3485627 := bstep (se 1 (by rfl) ⟨2614220, by rfl⟩ : syracuseStep 3485627 = 5228441) B5228441
theorem B2322395 : Blo 1547471 2322395 := bstep (se 1 (by rfl) ⟨1741796, by rfl⟩ : syracuseStep 2322395 = 3483593) B3483593
theorem B4960271 : Blo 1547471 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B3485753 : Blo 1547471 3485753 := bstep (se 2 (by rfl) ⟨1307157, by rfl⟩ : syracuseStep 3485753 = 2614315) B2614315
theorem B5583001 : Blo 1547471 5583001 := bstep (se 2 (by rfl) ⟨2093625, by rfl⟩ : syracuseStep 5583001 = 4187251) B4187251
theorem B3305719 : Blo 1547471 3305719 := bstep (se 1 (by rfl) ⟨2479289, by rfl⟩ : syracuseStep 3305719 = 4958579) B4958579
theorem B5222717 : Blo 1547471 5222717 := bstep (se 3 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 5222717 = 1958519) B1958519
theorem B7844201 : Blo 1547471 7844201 := bstep (se 2 (by rfl) ⟨2941575, by rfl⟩ : syracuseStep 7844201 = 5883151) B5883151
theorem B3486095 : Blo 1547471 3486095 := bstep (se 1 (by rfl) ⟨2614571, by rfl⟩ : syracuseStep 3486095 = 5229143) B5229143
theorem B2322863 : Blo 1547471 2322863 := bstep (se 1 (by rfl) ⟨1742147, by rfl⟩ : syracuseStep 2322863 = 3484295) B3484295
theorem B2322953 : Blo 1547471 2322953 := bstep (se 2 (by rfl) ⟨871107, by rfl⟩ : syracuseStep 2322953 = 1742215) B1742215
theorem B12554777 : Blo 1547471 12554777 := bstep (se 2 (by rfl) ⟨4708041, by rfl⟩ : syracuseStep 12554777 = 9416083) B9416083
theorem B1741351 : Blo 1547471 1741351 := bstep (se 1 (by rfl) ⟨1306013, by rfl⟩ : syracuseStep 1741351 = 2612027) B2612027
theorem B2322983 : Blo 1547471 2322983 := bstep (se 1 (by rfl) ⟨1742237, by rfl⟩ : syracuseStep 2322983 = 3484475) B3484475
theorem B2323067 : Blo 1547471 2323067 := bstep (se 1 (by rfl) ⟨1742300, by rfl⟩ : syracuseStep 2323067 = 3484601) B3484601
theorem B2323193 : Blo 1547471 2323193 := bstep (se 2 (by rfl) ⟨871197, by rfl⟩ : syracuseStep 2323193 = 1742395) B1742395
theorem B3920633 : Blo 1547471 3920633 := bstep (se 2 (by rfl) ⟨1470237, by rfl⟩ : syracuseStep 3920633 = 2940475) B2940475
theorem B5878595 : Blo 1547471 5878595 := bstep (se 1 (by rfl) ⟨4408946, by rfl⟩ : syracuseStep 5878595 = 8817893) B8817893
theorem B6615881 : Blo 1547471 6615881 := bstep (se 2 (by rfl) ⟨2480955, by rfl⟩ : syracuseStep 6615881 = 4961911) B4961911
theorem B2323295 : Blo 1547471 2323295 := bstep (se 1 (by rfl) ⟨1742471, by rfl⟩ : syracuseStep 2323295 = 3484943) B3484943
theorem B2323307 : Blo 1547471 2323307 := bstep (se 1 (by rfl) ⟨1742480, by rfl⟩ : syracuseStep 2323307 = 3484961) B3484961
theorem B2937863 : Blo 1547471 2937863 := bstep (se 1 (by rfl) ⟨2203397, by rfl⟩ : syracuseStep 2937863 = 4406795) B4406795
theorem B2323535 : Blo 1547471 2323535 := bstep (se 1 (by rfl) ⟨1742651, by rfl⟩ : syracuseStep 2323535 = 3485303) B3485303
theorem B5223581 : Blo 1547471 5223581 := bstep (se 3 (by rfl) ⟨979421, by rfl⟩ : syracuseStep 5223581 = 1958843) B1958843
theorem B2323655 : Blo 1547471 2323655 := bstep (se 1 (by rfl) ⟨1742741, by rfl⟩ : syracuseStep 2323655 = 3485483) B3485483
theorem B5879051 : Blo 1547471 5879051 := bstep (se 1 (by rfl) ⟨4409288, by rfl⟩ : syracuseStep 5879051 = 8818577) B8818577
theorem B12555557 : Blo 1547471 12555557 := bstep (se 4 (by rfl) ⟨1177083, by rfl⟩ : syracuseStep 12555557 = 2354167) B2354167
theorem B2323817 : Blo 1547471 2323817 := bstep (se 2 (by rfl) ⟨871431, by rfl⟩ : syracuseStep 2323817 = 1742863) B1742863
theorem B3921281 : Blo 1547471 3921281 := bstep (se 2 (by rfl) ⟨1470480, by rfl⟩ : syracuseStep 3921281 = 2940961) B2940961
theorem B2938295 : Blo 1547471 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B2323895 : Blo 1547471 2323895 := bstep (se 1 (by rfl) ⟨1742921, by rfl⟩ : syracuseStep 2323895 = 3485843) B3485843
theorem B2323931 : Blo 1547471 2323931 := bstep (se 1 (by rfl) ⟨1742948, by rfl⟩ : syracuseStep 2323931 = 3485897) B3485897
theorem B2790931 : Blo 1547471 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2938447 : Blo 1547471 2938447 := bstep (se 1 (by rfl) ⟨2203835, by rfl⟩ : syracuseStep 2938447 = 4407671) B4407671
theorem B19830419 : Blo 1547471 19830419 := bstep (se 1 (by rfl) ⟨14872814, by rfl⟩ : syracuseStep 19830419 = 29745629) B29745629
theorem B5224121 : Blo 1547471 5224121 := bstep (se 2 (by rfl) ⟨1959045, by rfl⟩ : syracuseStep 5224121 = 3918091) B3918091
theorem B17643257 : Blo 1547471 17643257 := bstep (se 2 (by rfl) ⟨6616221, by rfl⟩ : syracuseStep 17643257 = 13232443) B13232443
theorem B7837559 : Blo 1547471 7837559 := bstep (se 1 (by rfl) ⟨5878169, by rfl⟩ : syracuseStep 7837559 = 11756339) B11756339
theorem B5879735 : Blo 1547471 5879735 := bstep (se 1 (by rfl) ⟨4409801, by rfl⟩ : syracuseStep 5879735 = 8819603) B8819603
theorem B13228069 : Blo 1547471 13228069 := bstep (se 4 (by rfl) ⟨1240131, by rfl⟩ : syracuseStep 13228069 = 2480263) B2480263
theorem B20117605 : Blo 1547471 20117605 := bstep (se 4 (by rfl) ⟨1886025, by rfl⟩ : syracuseStep 20117605 = 3772051) B3772051
theorem B1742971 : Blo 1547471 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B3922091 : Blo 1547471 3922091 := bstep (se 1 (by rfl) ⟨2941568, by rfl⟩ : syracuseStep 3922091 = 5883137) B5883137
theorem B2611399 : Blo 1547471 2611399 := bstep (se 1 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 2611399 = 3917099) B3917099
theorem B5224715 : Blo 1547471 5224715 := bstep (se 1 (by rfl) ⟨3918536, by rfl⟩ : syracuseStep 5224715 = 7837073) B7837073
theorem B9926999 : Blo 1547471 9926999 := bstep (se 1 (by rfl) ⟨7445249, by rfl⟩ : syracuseStep 9926999 = 14890499) B14890499
theorem B2611561 : Blo 1547471 2611561 := bstep (se 2 (by rfl) ⟨979335, by rfl⟩ : syracuseStep 2611561 = 1958671) B1958671
theorem B11917721 : Blo 1547471 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B1653167 : Blo 1547471 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B8370697 : Blo 1547471 8370697 := bstep (se 2 (by rfl) ⟨3139011, by rfl⟩ : syracuseStep 8370697 = 6278023) B6278023
theorem B5224985 : Blo 1547471 5224985 := bstep (se 2 (by rfl) ⟨1959369, by rfl⟩ : syracuseStep 5224985 = 3918739) B3918739
theorem B2480719 : Blo 1547471 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B5814931 : Blo 1547471 5814931 := bstep (se 1 (by rfl) ⟨4361198, by rfl⟩ : syracuseStep 5814931 = 8722397) B8722397
theorem B5880509 : Blo 1547471 5880509 := bstep (se 3 (by rfl) ⟨1102595, by rfl⟩ : syracuseStep 5880509 = 2205191) B2205191
theorem B183483235 : Blo 1547471 183483235 := bstep (se 1 (by rfl) ⟨137612426, by rfl⟩ : syracuseStep 183483235 = 275224853) B275224853
theorem B2939753 : Blo 1547471 2939753 := bstep (se 2 (by rfl) ⟨1102407, by rfl⟩ : syracuseStep 2939753 = 2204815) B2204815
theorem B2612155 : Blo 1547471 2612155 := bstep (se 1 (by rfl) ⟨1959116, by rfl⟩ : syracuseStep 2612155 = 3918233) B3918233
theorem B2685961 : Blo 1547471 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B2612263 : Blo 1547471 2612263 := bstep (se 1 (by rfl) ⟨1959197, by rfl⟩ : syracuseStep 2612263 = 3918395) B3918395
theorem B8821811 : Blo 1547471 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B6282319 : Blo 1547471 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B6618307 : Blo 1547471 6618307 := bstep (se 1 (by rfl) ⟨4963730, by rfl⟩ : syracuseStep 6618307 = 9927461) B9927461
theorem B8813771 : Blo 1547471 8813771 := bstep (se 1 (by rfl) ⟨6610328, by rfl⟩ : syracuseStep 8813771 = 13220657) B13220657
theorem B1547483 : Blo 1547471 1547483 := bstep (se 1 (by rfl) ⟨1160612, by rfl⟩ : syracuseStep 1547483 = 2321225) B2321225
theorem B2514169 : Blo 1547471 2514169 := bstep (se 2 (by rfl) ⟨942813, by rfl⟩ : syracuseStep 2514169 = 1885627) B1885627
theorem B1547559 : Blo 1547471 1547559 := bstep (se 1 (by rfl) ⟨1160669, by rfl⟩ : syracuseStep 1547559 = 2321339) B2321339
theorem B1547599 : Blo 1547471 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B1547615 : Blo 1547471 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B5881193 : Blo 1547471 5881193 := bstep (se 2 (by rfl) ⟨2205447, by rfl⟩ : syracuseStep 5881193 = 4410895) B4410895
theorem B2612587 : Blo 1547471 2612587 := bstep (se 1 (by rfl) ⟨1959440, by rfl⟩ : syracuseStep 2612587 = 3918881) B3918881
theorem B1547643 : Blo 1547471 1547643 := bstep (se 1 (by rfl) ⟨1160732, by rfl⟩ : syracuseStep 1547643 = 2321465) B2321465
theorem B1547695 : Blo 1547471 1547695 := bstep (se 1 (by rfl) ⟨1160771, by rfl⟩ : syracuseStep 1547695 = 2321543) B2321543
theorem B1547719 : Blo 1547471 1547719 := bstep (se 1 (by rfl) ⟨1160789, by rfl⟩ : syracuseStep 1547719 = 2321579) B2321579
theorem B3718619 : Blo 1547471 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B1547739 : Blo 1547471 1547739 := bstep (se 1 (by rfl) ⟨1160804, by rfl⟩ : syracuseStep 1547739 = 2321609) B2321609
theorem B2481673 : Blo 1547471 2481673 := bstep (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) B1861255
theorem B1547815 : Blo 1547471 1547815 := bstep (se 1 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 1547815 = 2321723) B2321723
theorem B1547855 : Blo 1547471 1547855 := bstep (se 1 (by rfl) ⟨1160891, by rfl⟩ : syracuseStep 1547855 = 2321783) B2321783
theorem B1547871 : Blo 1547471 1547871 := bstep (se 1 (by rfl) ⟨1160903, by rfl⟩ : syracuseStep 1547871 = 2321807) B2321807
theorem B8814203 : Blo 1547471 8814203 := bstep (se 1 (by rfl) ⟨6610652, by rfl⟩ : syracuseStep 8814203 = 13221305) B13221305
theorem B1547899 : Blo 1547471 1547899 := bstep (se 1 (by rfl) ⟨1160924, by rfl⟩ : syracuseStep 1547899 = 2321849) B2321849
theorem B5226119 : Blo 1547471 5226119 := bstep (se 1 (by rfl) ⟨3919589, by rfl⟩ : syracuseStep 5226119 = 7839179) B7839179
theorem B1547951 : Blo 1547471 1547951 := bstep (se 1 (by rfl) ⟨1160963, by rfl⟩ : syracuseStep 1547951 = 2321927) B2321927
theorem B5226173 : Blo 1547471 5226173 := bstep (se 3 (by rfl) ⟨979907, by rfl⟩ : syracuseStep 5226173 = 1959815) B1959815
theorem B1547975 : Blo 1547471 1547975 := bstep (se 1 (by rfl) ⟨1160981, by rfl⟩ : syracuseStep 1547975 = 2321963) B2321963
theorem B8371927 : Blo 1547471 8371927 := bstep (se 1 (by rfl) ⟨6278945, by rfl⟩ : syracuseStep 8371927 = 12557891) B12557891
theorem B1547995 : Blo 1547471 1547995 := bstep (se 1 (by rfl) ⟨1160996, by rfl⟩ : syracuseStep 1547995 = 2321993) B2321993
theorem B1548071 : Blo 1547471 1548071 := bstep (se 1 (by rfl) ⟨1161053, by rfl⟩ : syracuseStep 1548071 = 2322107) B2322107
theorem B7061315 : Blo 1547471 7061315 := bstep (se 1 (by rfl) ⟨5295986, by rfl⟩ : syracuseStep 7061315 = 10591973) B10591973
theorem B1548111 : Blo 1547471 1548111 := bstep (se 1 (by rfl) ⟨1161083, by rfl⟩ : syracuseStep 1548111 = 2322167) B2322167
theorem B1548127 : Blo 1547471 1548127 := bstep (se 1 (by rfl) ⟨1161095, by rfl⟩ : syracuseStep 1548127 = 2322191) B2322191
theorem B5226335 : Blo 1547471 5226335 := bstep (se 1 (by rfl) ⟨3919751, by rfl⟩ : syracuseStep 5226335 = 7839503) B7839503
theorem B2940779 : Blo 1547471 2940779 := bstep (se 1 (by rfl) ⟨2205584, by rfl⟩ : syracuseStep 2940779 = 4411169) B4411169
theorem B1548155 : Blo 1547471 1548155 := bstep (se 1 (by rfl) ⟨1161116, by rfl⟩ : syracuseStep 1548155 = 2322233) B2322233
theorem B1548207 : Blo 1547471 1548207 := bstep (se 1 (by rfl) ⟨1161155, by rfl⟩ : syracuseStep 1548207 = 2322311) B2322311
theorem B11165627 : Blo 1547471 11165627 := bstep (se 1 (by rfl) ⟨8374220, by rfl⟩ : syracuseStep 11165627 = 16748441) B16748441
theorem B1548231 : Blo 1547471 1548231 := bstep (se 1 (by rfl) ⟨1161173, by rfl⟩ : syracuseStep 1548231 = 2322347) B2322347
theorem B1548251 : Blo 1547471 1548251 := bstep (se 1 (by rfl) ⟨1161188, by rfl⟩ : syracuseStep 1548251 = 2322377) B2322377
theorem B17637425 : Blo 1547471 17637425 := bstep (se 2 (by rfl) ⟨6614034, by rfl⟩ : syracuseStep 17637425 = 13228069) B13228069
theorem B3481811 : Blo 1547471 3481811 := bstep (se 1 (by rfl) ⟨2611358, by rfl⟩ : syracuseStep 3481811 = 5222717) B5222717
theorem B3481865 : Blo 1547471 3481865 := bstep (se 2 (by rfl) ⟨1305699, by rfl⟩ : syracuseStep 3481865 = 2611399) B2611399
theorem B1548575 : Blo 1547471 1548575 := bstep (se 1 (by rfl) ⟨1161431, by rfl⟩ : syracuseStep 1548575 = 2322863) B2322863
theorem B4407625 : Blo 1547471 4407625 := bstep (se 2 (by rfl) ⟨1652859, by rfl⟩ : syracuseStep 4407625 = 3305719) B3305719
theorem B1548635 : Blo 1547471 1548635 := bstep (se 1 (by rfl) ⟨1161476, by rfl⟩ : syracuseStep 1548635 = 2322953) B2322953
theorem B1548655 : Blo 1547471 1548655 := bstep (se 1 (by rfl) ⟨1161491, by rfl⟩ : syracuseStep 1548655 = 2322983) B2322983
theorem B53666201 : Blo 1547471 53666201 := bstep (se 2 (by rfl) ⟨20124825, by rfl⟩ : syracuseStep 53666201 = 40249651) B40249651
theorem B1548711 : Blo 1547471 1548711 := bstep (se 1 (by rfl) ⟨1161533, by rfl⟩ : syracuseStep 1548711 = 2323067) B2323067
theorem B3482081 : Blo 1547471 3482081 := bstep (se 2 (by rfl) ⟨1305780, by rfl⟩ : syracuseStep 3482081 = 2611561) B2611561
theorem B2941409 : Blo 1547471 2941409 := bstep (se 2 (by rfl) ⟨1103028, by rfl⟩ : syracuseStep 2941409 = 2206057) B2206057
theorem B1548795 : Blo 1547471 1548795 := bstep (se 1 (by rfl) ⟨1161596, by rfl⟩ : syracuseStep 1548795 = 2323193) B2323193
theorem B2613755 : Blo 1547471 2613755 := bstep (se 1 (by rfl) ⟨1960316, by rfl⟩ : syracuseStep 2613755 = 3920633) B3920633
theorem B1548863 : Blo 1547471 1548863 := bstep (se 1 (by rfl) ⟨1161647, by rfl⟩ : syracuseStep 1548863 = 2323295) B2323295
theorem B1548871 : Blo 1547471 1548871 := bstep (se 1 (by rfl) ⟨1161653, by rfl⟩ : syracuseStep 1548871 = 2323307) B2323307
theorem B4407979 : Blo 1547471 4407979 := bstep (se 1 (by rfl) ⟨3305984, by rfl⟩ : syracuseStep 4407979 = 6611969) B6611969
theorem B1958575 : Blo 1547471 1958575 := bstep (se 1 (by rfl) ⟨1468931, by rfl⟩ : syracuseStep 1958575 = 2937863) B2937863
theorem B1549023 : Blo 1547471 1549023 := bstep (se 1 (by rfl) ⟨1161767, by rfl⟩ : syracuseStep 1549023 = 2323535) B2323535
theorem B3482387 : Blo 1547471 3482387 := bstep (se 1 (by rfl) ⟨2611790, by rfl⟩ : syracuseStep 3482387 = 5223581) B5223581
theorem B1549103 : Blo 1547471 1549103 := bstep (se 1 (by rfl) ⟨1161827, by rfl⟩ : syracuseStep 1549103 = 2323655) B2323655
theorem B1549211 : Blo 1547471 1549211 := bstep (se 1 (by rfl) ⟨1161908, by rfl⟩ : syracuseStep 1549211 = 2323817) B2323817
theorem B2614187 : Blo 1547471 2614187 := bstep (se 1 (by rfl) ⟨1960640, by rfl⟩ : syracuseStep 2614187 = 3921281) B3921281
theorem B1549263 : Blo 1547471 1549263 := bstep (se 1 (by rfl) ⟨1161947, by rfl⟩ : syracuseStep 1549263 = 2323895) B2323895
theorem B1549287 : Blo 1547471 1549287 := bstep (se 1 (by rfl) ⟨1161965, by rfl⟩ : syracuseStep 1549287 = 2323931) B2323931
theorem B26149891 : Blo 1547471 26149891 := bstep (se 1 (by rfl) ⟨19612418, by rfl⟩ : syracuseStep 26149891 = 39224837) B39224837
theorem B3482747 : Blo 1547471 3482747 := bstep (se 1 (by rfl) ⟨2612060, by rfl⟩ : syracuseStep 3482747 = 5224121) B5224121
theorem B6276221 : Blo 1547471 6276221 := bstep (se 3 (by rfl) ⟨1176791, by rfl⟩ : syracuseStep 6276221 = 2353583) B2353583
theorem B4408445 : Blo 1547471 4408445 := bstep (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) B1653167
theorem B3482873 : Blo 1547471 3482873 := bstep (se 2 (by rfl) ⟨1306077, by rfl⟩ : syracuseStep 3482873 = 2612155) B2612155
theorem B1590559 : Blo 1547471 1590559 := bstep (se 1 (by rfl) ⟨1192919, by rfl⟩ : syracuseStep 1590559 = 2385839) B2385839
theorem B3581281 : Blo 1547471 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B3483017 : Blo 1547471 3483017 := bstep (se 2 (by rfl) ⟨1306131, by rfl⟩ : syracuseStep 3483017 = 2612263) B2612263
theorem B26445203 : Blo 1547471 26445203 := bstep (se 1 (by rfl) ⟨19833902, by rfl⟩ : syracuseStep 26445203 = 39667805) B39667805
theorem B2614727 : Blo 1547471 2614727 := bstep (se 1 (by rfl) ⟨1961045, by rfl⟩ : syracuseStep 2614727 = 3922091) B3922091
theorem B3483143 : Blo 1547471 3483143 := bstep (se 1 (by rfl) ⟨2612357, by rfl⟩ : syracuseStep 3483143 = 5224715) B5224715
theorem B8816161 : Blo 1547471 8816161 := bstep (se 2 (by rfl) ⟨3306060, by rfl⟩ : syracuseStep 8816161 = 6612121) B6612121
theorem B8824409 : Blo 1547471 8824409 := bstep (se 2 (by rfl) ⟨3309153, by rfl⟩ : syracuseStep 8824409 = 6618307) B6618307
theorem B3352225 : Blo 1547471 3352225 := bstep (se 2 (by rfl) ⟨1257084, by rfl⟩ : syracuseStep 3352225 = 2514169) B2514169
theorem B3483323 : Blo 1547471 3483323 := bstep (se 1 (by rfl) ⟨2612492, by rfl⟩ : syracuseStep 3483323 = 5224985) B5224985
theorem B3483449 : Blo 1547471 3483449 := bstep (se 2 (by rfl) ⟨1306293, by rfl⟩ : syracuseStep 3483449 = 2612587) B2612587
theorem B7440311 : Blo 1547471 7440311 := bstep (se 1 (by rfl) ⟨5580233, by rfl⟩ : syracuseStep 7440311 = 11160467) B11160467
theorem B5228495 : Blo 1547471 5228495 := bstep (se 1 (by rfl) ⟨3921371, by rfl⟩ : syracuseStep 5228495 = 7842743) B7842743
theorem B17647631 : Blo 1547471 17647631 := bstep (se 1 (by rfl) ⟨13235723, by rfl⟩ : syracuseStep 17647631 = 26471447) B26471447
theorem B3721241 : Blo 1547471 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B3917929 : Blo 1547471 3917929 := bstep (se 2 (by rfl) ⟨1469223, by rfl⟩ : syracuseStep 3917929 = 2938447) B2938447
theorem B5875847 : Blo 1547471 5875847 := bstep (se 1 (by rfl) ⟨4406885, by rfl⟩ : syracuseStep 5875847 = 8813771) B8813771
theorem B5097757 : Blo 1547471 5097757 := bstep (se 3 (by rfl) ⟨955829, by rfl⟩ : syracuseStep 5097757 = 1911659) B1911659
theorem B4409711 : Blo 1547471 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B5876135 : Blo 1547471 5876135 := bstep (se 1 (by rfl) ⟨4407101, by rfl⟩ : syracuseStep 5876135 = 8814203) B8814203
theorem B3484079 : Blo 1547471 3484079 := bstep (se 1 (by rfl) ⟨2613059, by rfl⟩ : syracuseStep 3484079 = 5226119) B5226119
theorem B3484115 : Blo 1547471 3484115 := bstep (se 1 (by rfl) ⟨2613086, by rfl⟩ : syracuseStep 3484115 = 5226173) B5226173
theorem B3181025 : Blo 1547471 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B3484223 : Blo 1547471 3484223 := bstep (se 1 (by rfl) ⟨2613167, by rfl⟩ : syracuseStep 3484223 = 5226335) B5226335
theorem B1960519 : Blo 1547471 1960519 := bstep (se 1 (by rfl) ⟨1470389, by rfl⟩ : syracuseStep 1960519 = 2940779) B2940779
theorem B3918415 : Blo 1547471 3918415 := bstep (se 1 (by rfl) ⟨2938811, by rfl⟩ : syracuseStep 3918415 = 5877623) B5877623
theorem B3484331 : Blo 1547471 3484331 := bstep (se 1 (by rfl) ⟨2613248, by rfl⟩ : syracuseStep 3484331 = 5226497) B5226497
theorem B28240595 : Blo 1547471 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B26823473 : Blo 1547471 26823473 := bstep (se 2 (by rfl) ⟨10058802, by rfl⟩ : syracuseStep 26823473 = 20117605) B20117605
theorem B2321231 : Blo 1547471 2321231 := bstep (se 1 (by rfl) ⟨1740923, by rfl⟩ : syracuseStep 2321231 = 3481847) B3481847
theorem B5229467 : Blo 1547471 5229467 := bstep (se 1 (by rfl) ⟨3922100, by rfl⟩ : syracuseStep 5229467 = 7844201) B7844201
theorem B5876651 : Blo 1547471 5876651 := bstep (se 1 (by rfl) ⟨4407488, by rfl⟩ : syracuseStep 5876651 = 8814977) B8814977
theorem B3484871 : Blo 1547471 3484871 := bstep (se 1 (by rfl) ⟨2613653, by rfl⟩ : syracuseStep 3484871 = 5227307) B5227307
theorem B3919063 : Blo 1547471 3919063 := bstep (se 1 (by rfl) ⟨2939297, by rfl⟩ : syracuseStep 3919063 = 5878595) B5878595
theorem B2321627 : Blo 1547471 2321627 := bstep (se 1 (by rfl) ⟨1741220, by rfl⟩ : syracuseStep 2321627 = 3482441) B3482441
theorem B4410587 : Blo 1547471 4410587 := bstep (se 1 (by rfl) ⟨3307940, by rfl⟩ : syracuseStep 4410587 = 6615881) B6615881
theorem B11160929 : Blo 1547471 11160929 := bstep (se 2 (by rfl) ⟨4185348, by rfl⟩ : syracuseStep 11160929 = 8370697) B8370697
theorem B3485051 : Blo 1547471 3485051 := bstep (se 1 (by rfl) ⟨2613788, by rfl⟩ : syracuseStep 3485051 = 5227577) B5227577
theorem B2387323 : Blo 1547471 2387323 := bstep (se 1 (by rfl) ⟨1790492, by rfl⟩ : syracuseStep 2387323 = 3580985) B3580985
theorem B2321801 : Blo 1547471 2321801 := bstep (se 2 (by rfl) ⟨870675, by rfl⟩ : syracuseStep 2321801 = 1741351) B1741351
theorem B7835129 : Blo 1547471 7835129 := bstep (se 2 (by rfl) ⟨2938173, by rfl⟩ : syracuseStep 7835129 = 5876347) B5876347
theorem B3485177 : Blo 1547471 3485177 := bstep (se 2 (by rfl) ⟨1306941, by rfl⟩ : syracuseStep 3485177 = 2613883) B2613883
theorem B3919367 : Blo 1547471 3919367 := bstep (se 1 (by rfl) ⟨2939525, by rfl⟩ : syracuseStep 3919367 = 5879051) B5879051
theorem B7753241 : Blo 1547471 7753241 := bstep (se 2 (by rfl) ⟨2907465, by rfl⟩ : syracuseStep 7753241 = 5814931) B5814931
theorem B3485267 : Blo 1547471 3485267 := bstep (se 1 (by rfl) ⟨2613950, by rfl⟩ : syracuseStep 3485267 = 5227901) B5227901
theorem B2322155 : Blo 1547471 2322155 := bstep (se 1 (by rfl) ⟨1741616, by rfl⟩ : syracuseStep 2322155 = 3483233) B3483233
theorem B3485447 : Blo 1547471 3485447 := bstep (se 1 (by rfl) ⟨2614085, by rfl⟩ : syracuseStep 3485447 = 5228171) B5228171
theorem B7835453 : Blo 1547471 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B6614891 : Blo 1547471 6614891 := bstep (se 1 (by rfl) ⟨4961168, by rfl⟩ : syracuseStep 6614891 = 9922337) B9922337
theorem B2322383 : Blo 1547471 2322383 := bstep (se 1 (by rfl) ⟨1741787, by rfl⟩ : syracuseStep 2322383 = 3483575) B3483575
theorem B3919823 : Blo 1547471 3919823 := bstep (se 1 (by rfl) ⟨2939867, by rfl⟩ : syracuseStep 3919823 = 5879735) B5879735
theorem B8376425 : Blo 1547471 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B2322779 : Blo 1547471 2322779 := bstep (se 1 (by rfl) ⟨1742084, by rfl⟩ : syracuseStep 2322779 = 3484169) B3484169
theorem B33501545 : Blo 1547471 33501545 := bstep (se 2 (by rfl) ⟨12563079, by rfl⟩ : syracuseStep 33501545 = 25126159) B25126159
theorem B3486059 : Blo 1547471 3486059 := bstep (se 1 (by rfl) ⟨2614544, by rfl⟩ : syracuseStep 3486059 = 5229089) B5229089
theorem B3920339 : Blo 1547471 3920339 := bstep (se 1 (by rfl) ⟨2940254, by rfl⟩ : syracuseStep 3920339 = 5880509) B5880509
theorem B3486203 : Blo 1547471 3486203 := bstep (se 1 (by rfl) ⟨2614652, by rfl⟩ : syracuseStep 3486203 = 5229305) B5229305
theorem B5878291 : Blo 1547471 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B2323007 : Blo 1547471 2323007 := bstep (se 1 (by rfl) ⟨1742255, by rfl⟩ : syracuseStep 2323007 = 3484511) B3484511
theorem B25113185 : Blo 1547471 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B5223095 : Blo 1547471 5223095 := bstep (se 1 (by rfl) ⟨3917321, by rfl⟩ : syracuseStep 5223095 = 7834643) B7834643
theorem B2323127 : Blo 1547471 2323127 := bstep (se 1 (by rfl) ⟨1742345, by rfl⟩ : syracuseStep 2323127 = 3484691) B3484691
theorem B18830173 : Blo 1547471 18830173 := bstep (se 3 (by rfl) ⟨3530657, by rfl⟩ : syracuseStep 18830173 = 7061315) B7061315
theorem B3306395 : Blo 1547471 3306395 := bstep (se 1 (by rfl) ⟨2479796, by rfl⟩ : syracuseStep 3306395 = 4959593) B4959593
theorem B2323355 : Blo 1547471 2323355 := bstep (se 1 (by rfl) ⟨1742516, by rfl⟩ : syracuseStep 2323355 = 3485033) B3485033
theorem B3920795 : Blo 1547471 3920795 := bstep (se 1 (by rfl) ⟨2940596, by rfl⟩ : syracuseStep 3920795 = 5881193) B5881193
theorem B11162569 : Blo 1547471 11162569 := bstep (se 2 (by rfl) ⟨4185963, by rfl⟩ : syracuseStep 11162569 = 8371927) B8371927
theorem B28644301 : Blo 1547471 28644301 := bstep (se 3 (by rfl) ⟨5370806, by rfl⟩ : syracuseStep 28644301 = 10741613) B10741613
theorem B2479079 : Blo 1547471 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B26440829 : Blo 1547471 26440829 := bstep (se 3 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 26440829 = 9915311) B9915311
theorem B7443751 : Blo 1547471 7443751 := bstep (se 1 (by rfl) ⟨5582813, by rfl⟩ : syracuseStep 7443751 = 11165627) B11165627
theorem B2323751 : Blo 1547471 2323751 := bstep (se 1 (by rfl) ⟨1742813, by rfl⟩ : syracuseStep 2323751 = 3485627) B3485627
theorem B3306847 : Blo 1547471 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B2323835 : Blo 1547471 2323835 := bstep (se 1 (by rfl) ⟨1742876, by rfl⟩ : syracuseStep 2323835 = 3485753) B3485753
theorem B2323961 : Blo 1547471 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B7444001 : Blo 1547471 7444001 := bstep (se 2 (by rfl) ⟨2791500, by rfl⟩ : syracuseStep 7444001 = 5583001) B5583001
theorem B1742431 : Blo 1547471 1742431 := bstep (se 1 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 1742431 = 2613647) B2613647
theorem B2324063 : Blo 1547471 2324063 := bstep (se 1 (by rfl) ⟨1743047, by rfl⟩ : syracuseStep 2324063 = 3486095) B3486095
theorem B8369851 : Blo 1547471 8369851 := bstep (se 1 (by rfl) ⟨6277388, by rfl⟩ : syracuseStep 8369851 = 12554777) B12554777
theorem B8820535 : Blo 1547471 8820535 := bstep (se 1 (by rfl) ⟨6615401, by rfl⟩ : syracuseStep 8820535 = 13230803) B13230803
theorem B3921929 : Blo 1547471 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B3307625 : Blo 1547471 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B8370371 : Blo 1547471 8370371 := bstep (se 1 (by rfl) ⟨6277778, by rfl⟩ : syracuseStep 8370371 = 12555557) B12555557
theorem B7436717 : Blo 1547471 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B13220279 : Blo 1547471 13220279 := bstep (se 1 (by rfl) ⟨9915209, by rfl⟩ : syracuseStep 13220279 = 19830419) B19830419
theorem B244644313 : Blo 1547471 244644313 := bstep (se 2 (by rfl) ⟨91741617, by rfl⟩ : syracuseStep 244644313 = 183483235) B183483235
theorem B2480635 : Blo 1547471 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B11762171 : Blo 1547471 11762171 := bstep (se 1 (by rfl) ⟨8821628, by rfl⟩ : syracuseStep 11762171 = 17643257) B17643257
theorem B2513479 : Blo 1547471 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B2939465 : Blo 1547471 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B5225039 : Blo 1547471 5225039 := bstep (se 1 (by rfl) ⟨3918779, by rfl⟩ : syracuseStep 5225039 = 7837559) B7837559
theorem B26467073 : Blo 1547471 26467073 := bstep (se 2 (by rfl) ⟨9925152, by rfl⟩ : syracuseStep 26467073 = 19850305) B19850305
theorem B7838531 : Blo 1547471 7838531 := bstep (se 1 (by rfl) ⟨5878898, by rfl⟩ : syracuseStep 7838531 = 11757797) B11757797
theorem B2612047 : Blo 1547471 2612047 := bstep (se 1 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 2612047 = 3918071) B3918071
theorem B6617999 : Blo 1547471 6617999 := bstep (se 1 (by rfl) ⟨4963499, by rfl⟩ : syracuseStep 6617999 = 9926999) B9926999
theorem B11754395 : Blo 1547471 11754395 := bstep (se 1 (by rfl) ⟨8815796, by rfl⟩ : syracuseStep 11754395 = 17631593) B17631593
theorem B7945147 : Blo 1547471 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B5299339 : Blo 1547471 5299339 := bstep (se 1 (by rfl) ⟨3974504, by rfl⟩ : syracuseStep 5299339 = 7949009) B7949009
theorem B1547551 : Blo 1547471 1547551 := bstep (se 1 (by rfl) ⟨1160663, by rfl⟩ : syracuseStep 1547551 = 2321327) B2321327
theorem B6806851 : Blo 1547471 6806851 := bstep (se 1 (by rfl) ⟨5105138, by rfl⟩ : syracuseStep 6806851 = 10210277) B10210277
theorem B1547611 : Blo 1547471 1547611 := bstep (se 1 (by rfl) ⟨1160708, by rfl⟩ : syracuseStep 1547611 = 2321417) B2321417
theorem B3308897 : Blo 1547471 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B1547631 : Blo 1547471 1547631 := bstep (se 1 (by rfl) ⟨1160723, by rfl⟩ : syracuseStep 1547631 = 2321447) B2321447
theorem B5881207 : Blo 1547471 5881207 := bstep (se 1 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 5881207 = 8821811) B8821811
theorem B2481545 : Blo 1547471 2481545 := bstep (se 2 (by rfl) ⟨930579, by rfl⟩ : syracuseStep 2481545 = 1861159) B1861159
theorem B1547687 : Blo 1547471 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B5299643 : Blo 1547471 5299643 := bstep (se 1 (by rfl) ⟨3974732, by rfl⟩ : syracuseStep 5299643 = 7949465) B7949465
theorem B2612729 : Blo 1547471 2612729 := bstep (se 2 (by rfl) ⟨979773, by rfl⟩ : syracuseStep 2612729 = 1959547) B1959547
theorem B1547771 : Blo 1547471 1547771 := bstep (se 1 (by rfl) ⟨1160828, by rfl⟩ : syracuseStep 1547771 = 2321657) B2321657
theorem B17628677 : Blo 1547471 17628677 := bstep (se 4 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 17628677 = 3305377) B3305377
theorem B1547839 : Blo 1547471 1547839 := bstep (se 1 (by rfl) ⟨1160879, by rfl⟩ : syracuseStep 1547839 = 2321759) B2321759
theorem B1547847 : Blo 1547471 1547847 := bstep (se 1 (by rfl) ⟨1160885, by rfl⟩ : syracuseStep 1547847 = 2321771) B2321771
theorem B7839341 : Blo 1547471 7839341 := bstep (se 3 (by rfl) ⟨1469876, by rfl⟩ : syracuseStep 7839341 = 2939753) B2939753
theorem B1547999 : Blo 1547471 1547999 := bstep (se 1 (by rfl) ⟨1160999, by rfl⟩ : syracuseStep 1547999 = 2321999) B2321999
theorem B2612999 : Blo 1547471 2612999 := bstep (se 1 (by rfl) ⟨1959749, by rfl⟩ : syracuseStep 2612999 = 3919499) B3919499
theorem B5226281 : Blo 1547471 5226281 := bstep (se 2 (by rfl) ⟨1959855, by rfl⟩ : syracuseStep 5226281 = 3919711) B3919711
theorem B1548079 : Blo 1547471 1548079 := bstep (se 1 (by rfl) ⟨1161059, by rfl⟩ : syracuseStep 1548079 = 2322119) B2322119
theorem B10600321 : Blo 1547471 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B1548187 : Blo 1547471 1548187 := bstep (se 1 (by rfl) ⟨1161140, by rfl⟩ : syracuseStep 1548187 = 2322281) B2322281
theorem B1548239 : Blo 1547471 1548239 := bstep (se 1 (by rfl) ⟨1161179, by rfl⟩ : syracuseStep 1548239 = 2322359) B2322359
theorem B1548263 : Blo 1547471 1548263 := bstep (se 1 (by rfl) ⟨1161197, by rfl⟩ : syracuseStep 1548263 = 2322395) B2322395
theorem B1548519 : Blo 1547471 1548519 := bstep (se 1 (by rfl) ⟨1161389, by rfl⟩ : syracuseStep 1548519 = 2322779) B2322779
theorem B2613559 : Blo 1547471 2613559 := bstep (se 1 (by rfl) ⟨1960169, by rfl⟩ : syracuseStep 2613559 = 3920339) B3920339
theorem B11755853 : Blo 1547471 11755853 := bstep (se 3 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 11755853 = 4408445) B4408445
theorem B1548671 : Blo 1547471 1548671 := bstep (se 1 (by rfl) ⟨1161503, by rfl⟩ : syracuseStep 1548671 = 2323007) B2323007
theorem B3482063 : Blo 1547471 3482063 := bstep (se 1 (by rfl) ⟨2611547, by rfl⟩ : syracuseStep 3482063 = 5223095) B5223095
theorem B1548751 : Blo 1547471 1548751 := bstep (se 1 (by rfl) ⟨1161563, by rfl⟩ : syracuseStep 1548751 = 2323127) B2323127
theorem B2204263 : Blo 1547471 2204263 := bstep (se 1 (by rfl) ⟨1653197, by rfl⟩ : syracuseStep 2204263 = 3306395) B3306395
theorem B1548903 : Blo 1547471 1548903 := bstep (se 1 (by rfl) ⟨1161677, by rfl⟩ : syracuseStep 1548903 = 2323355) B2323355
theorem B2613863 : Blo 1547471 2613863 := bstep (se 1 (by rfl) ⟨1960397, by rfl⟩ : syracuseStep 2613863 = 3920795) B3920795
theorem B3351305 : Blo 1547471 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B2614025 : Blo 1547471 2614025 := bstep (se 2 (by rfl) ⟨980259, by rfl⟩ : syracuseStep 2614025 = 1960519) B1960519
theorem B1549167 : Blo 1547471 1549167 := bstep (se 1 (by rfl) ⟨1161875, by rfl⟩ : syracuseStep 1549167 = 2323751) B2323751
theorem B1549223 : Blo 1547471 1549223 := bstep (se 1 (by rfl) ⟨1161917, by rfl⟩ : syracuseStep 1549223 = 2323835) B2323835
theorem B8823725 : Blo 1547471 8823725 := bstep (se 3 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 8823725 = 3308897) B3308897
theorem B17630135 : Blo 1547471 17630135 := bstep (se 1 (by rfl) ⟨13222601, by rfl⟩ : syracuseStep 17630135 = 26445203) B26445203
theorem B1549307 : Blo 1547471 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B5882939 : Blo 1547471 5882939 := bstep (se 1 (by rfl) ⟨4412204, by rfl⟩ : syracuseStep 5882939 = 8824409) B8824409
theorem B1549375 : Blo 1547471 1549375 := bstep (se 1 (by rfl) ⟨1162031, by rfl⟩ : syracuseStep 1549375 = 2324063) B2324063
theorem B3482729 : Blo 1547471 3482729 := bstep (se 2 (by rfl) ⟨1306023, by rfl⟩ : syracuseStep 3482729 = 2612047) B2612047
theorem B10593529 : Blo 1547471 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B38192401 : Blo 1547471 38192401 := bstep (se 2 (by rfl) ⟨14322150, by rfl⟩ : syracuseStep 38192401 = 28644301) B28644301
theorem B34866521 : Blo 1547471 34866521 := bstep (se 2 (by rfl) ⟨13074945, by rfl⟩ : syracuseStep 34866521 = 26149891) B26149891
theorem B2614619 : Blo 1547471 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B11765087 : Blo 1547471 11765087 := bstep (se 1 (by rfl) ⟨8823815, by rfl⟩ : syracuseStep 11765087 = 17647631) B17647631
theorem B145212821 : Blo 1547471 145212821 := bstep (se 6 (by rfl) ⟨3403425, by rfl⟩ : syracuseStep 145212821 = 6806851) B6806851
theorem B2205083 : Blo 1547471 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B19850669 : Blo 1547471 19850669 := bstep (se 3 (by rfl) ⟨3722000, by rfl⟩ : syracuseStep 19850669 = 7444001) B7444001
theorem B3917231 : Blo 1547471 3917231 := bstep (se 1 (by rfl) ⟨2937923, by rfl⟩ : syracuseStep 3917231 = 5875847) B5875847
theorem B5580247 : Blo 1547471 5580247 := bstep (se 1 (by rfl) ⟨4185185, by rfl⟩ : syracuseStep 5580247 = 8370371) B8370371
theorem B3917423 : Blo 1547471 3917423 := bstep (se 1 (by rfl) ⟨2938067, by rfl⟩ : syracuseStep 3917423 = 5876135) B5876135
theorem B4957811 : Blo 1547471 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B7841447 : Blo 1547471 7841447 := bstep (se 1 (by rfl) ⟨5881085, by rfl⟩ : syracuseStep 7841447 = 11762171) B11762171
theorem B1959643 : Blo 1547471 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B3483359 : Blo 1547471 3483359 := bstep (se 1 (by rfl) ⟨2612519, by rfl⟩ : syracuseStep 3483359 = 5225039) B5225039
theorem B4409129 : Blo 1547471 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B18827063 : Blo 1547471 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B7841609 : Blo 1547471 7841609 := bstep (se 2 (by rfl) ⟨2940603, by rfl⟩ : syracuseStep 7841609 = 5881207) B5881207
theorem B3917767 : Blo 1547471 3917767 := bstep (se 1 (by rfl) ⟨2938325, by rfl⟩ : syracuseStep 3917767 = 5876651) B5876651
theorem B7440619 : Blo 1547471 7440619 := bstep (se 1 (by rfl) ⟨5580464, by rfl⟩ : syracuseStep 7440619 = 11160929) B11160929
theorem B11159801 : Blo 1547471 11159801 := bstep (se 2 (by rfl) ⟨4184925, by rfl⟩ : syracuseStep 11159801 = 8369851) B8369851
theorem B3533095 : Blo 1547471 3533095 := bstep (se 1 (by rfl) ⟨2649821, by rfl⟩ : syracuseStep 3533095 = 5299643) B5299643
theorem B14133761 : Blo 1547471 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B3484187 : Blo 1547471 3484187 := bstep (se 1 (by rfl) ⟨2613140, by rfl⟩ : syracuseStep 3484187 = 5226281) B5226281
theorem B4409927 : Blo 1547471 4409927 := bstep (se 1 (by rfl) ⟨3307445, by rfl⟩ : syracuseStep 4409927 = 6614891) B6614891
theorem B11758283 : Blo 1547471 11758283 := bstep (se 1 (by rfl) ⟨8818712, by rfl⟩ : syracuseStep 11758283 = 17637425) B17637425
theorem B9923309 : Blo 1547471 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B2321207 : Blo 1547471 2321207 := bstep (se 1 (by rfl) ⟨1740905, by rfl⟩ : syracuseStep 2321207 = 3481811) B3481811
theorem B2321243 : Blo 1547471 2321243 := bstep (se 1 (by rfl) ⟨1740932, by rfl⟩ : syracuseStep 2321243 = 3481865) B3481865
theorem B22334363 : Blo 1547471 22334363 := bstep (se 1 (by rfl) ⟨16750772, by rfl⟩ : syracuseStep 22334363 = 33501545) B33501545
theorem B35777467 : Blo 1547471 35777467 := bstep (se 1 (by rfl) ⟨26833100, by rfl⟩ : syracuseStep 35777467 = 53666201) B53666201
theorem B2321387 : Blo 1547471 2321387 := bstep (se 1 (by rfl) ⟨1741040, by rfl⟩ : syracuseStep 2321387 = 3482081) B3482081
theorem B1960939 : Blo 1547471 1960939 := bstep (se 1 (by rfl) ⟨1470704, by rfl⟩ : syracuseStep 1960939 = 2941409) B2941409
theorem B5876833 : Blo 1547471 5876833 := bstep (se 2 (by rfl) ⟨2203812, by rfl⟩ : syracuseStep 5876833 = 4407625) B4407625
theorem B2321591 : Blo 1547471 2321591 := bstep (se 1 (by rfl) ⟨1741193, by rfl⟩ : syracuseStep 2321591 = 3482387) B3482387
theorem B326192417 : Blo 1547471 326192417 := bstep (se 2 (by rfl) ⟨122322156, by rfl⟩ : syracuseStep 326192417 = 244644313) B244644313
theorem B2321831 : Blo 1547471 2321831 := bstep (se 1 (by rfl) ⟨1741373, by rfl⟩ : syracuseStep 2321831 = 3482747) B3482747
theorem B2321915 : Blo 1547471 2321915 := bstep (se 1 (by rfl) ⟨1741436, by rfl⟩ : syracuseStep 2321915 = 3482873) B3482873
theorem B5877305 : Blo 1547471 5877305 := bstep (se 2 (by rfl) ⟨2203989, by rfl⟩ : syracuseStep 5877305 = 4407979) B4407979
theorem B2322011 : Blo 1547471 2322011 := bstep (se 1 (by rfl) ⟨1741508, by rfl⟩ : syracuseStep 2322011 = 3483017) B3483017
theorem B2322095 : Blo 1547471 2322095 := bstep (se 1 (by rfl) ⟨1741571, by rfl⟩ : syracuseStep 2322095 = 3483143) B3483143
theorem B2322215 : Blo 1547471 2322215 := bstep (se 1 (by rfl) ⟨1741661, by rfl⟩ : syracuseStep 2322215 = 3483323) B3483323
theorem B2322299 : Blo 1547471 2322299 := bstep (se 1 (by rfl) ⟨1741724, by rfl⟩ : syracuseStep 2322299 = 3483449) B3483449
theorem B8482733 : Blo 1547471 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B4960207 : Blo 1547471 4960207 := bstep (se 1 (by rfl) ⟨3720155, by rfl⟩ : syracuseStep 4960207 = 7440311) B7440311
theorem B3485663 : Blo 1547471 3485663 := bstep (se 1 (by rfl) ⟨2614247, by rfl⟩ : syracuseStep 3485663 = 5228495) B5228495
theorem B8482981 : Blo 1547471 8482981 := bstep (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) B1590559
theorem B7065785 : Blo 1547471 7065785 := bstep (se 2 (by rfl) ⟨2649669, by rfl⟩ : syracuseStep 7065785 = 5299339) B5299339
theorem B2322719 : Blo 1547471 2322719 := bstep (se 1 (by rfl) ⟨1742039, by rfl⟩ : syracuseStep 2322719 = 3484079) B3484079
theorem B2322743 : Blo 1547471 2322743 := bstep (se 1 (by rfl) ⟨1742057, by rfl⟩ : syracuseStep 2322743 = 3484115) B3484115
theorem B2322815 : Blo 1547471 2322815 := bstep (se 1 (by rfl) ⟨1742111, by rfl⟩ : syracuseStep 2322815 = 3484223) B3484223
theorem B9925001 : Blo 1547471 9925001 := bstep (se 2 (by rfl) ⟨3721875, by rfl⟩ : syracuseStep 9925001 = 7443751) B7443751
theorem B2322887 : Blo 1547471 2322887 := bstep (se 1 (by rfl) ⟨1742165, by rfl⟩ : syracuseStep 2322887 = 3484331) B3484331
theorem B3183097 : Blo 1547471 3183097 := bstep (se 2 (by rfl) ⟨1193661, by rfl⟩ : syracuseStep 3183097 = 2387323) B2387323
theorem B4411999 : Blo 1547471 4411999 := bstep (se 1 (by rfl) ⟨3308999, by rfl⟩ : syracuseStep 4411999 = 6617999) B6617999
theorem B7836263 : Blo 1547471 7836263 := bstep (se 1 (by rfl) ⟨5877197, by rfl⟩ : syracuseStep 7836263 = 11754395) B11754395
theorem B3486311 : Blo 1547471 3486311 := bstep (se 1 (by rfl) ⟨2614733, by rfl⟩ : syracuseStep 3486311 = 5229467) B5229467
theorem B2323241 : Blo 1547471 2323241 := bstep (se 2 (by rfl) ⟨871215, by rfl⟩ : syracuseStep 2323241 = 1742431) B1742431
theorem B2323247 : Blo 1547471 2323247 := bstep (se 1 (by rfl) ⟨1742435, by rfl⟩ : syracuseStep 2323247 = 3484871) B3484871
theorem B4469633 : Blo 1547471 4469633 := bstep (se 2 (by rfl) ⟨1676112, by rfl⟩ : syracuseStep 4469633 = 3352225) B3352225
theorem B2323367 : Blo 1547471 2323367 := bstep (se 1 (by rfl) ⟨1742525, by rfl⟩ : syracuseStep 2323367 = 3485051) B3485051
theorem B5223419 : Blo 1547471 5223419 := bstep (se 1 (by rfl) ⟨3917564, by rfl⟩ : syracuseStep 5223419 = 7835129) B7835129
theorem B1741819 : Blo 1547471 1741819 := bstep (se 1 (by rfl) ⟨1306364, by rfl⟩ : syracuseStep 1741819 = 2612729) B2612729
theorem B2323451 : Blo 1547471 2323451 := bstep (se 1 (by rfl) ⟨1742588, by rfl⟩ : syracuseStep 2323451 = 3485177) B3485177
theorem B11752451 : Blo 1547471 11752451 := bstep (se 1 (by rfl) ⟨8814338, by rfl⟩ : syracuseStep 11752451 = 17628677) B17628677
theorem B2323511 : Blo 1547471 2323511 := bstep (se 1 (by rfl) ⟨1742633, by rfl⟩ : syracuseStep 2323511 = 3485267) B3485267
theorem B11760713 : Blo 1547471 11760713 := bstep (se 2 (by rfl) ⟨4410267, by rfl⟩ : syracuseStep 11760713 = 8820535) B8820535
theorem B1741999 : Blo 1547471 1741999 := bstep (se 1 (by rfl) ⟨1306499, by rfl⟩ : syracuseStep 1741999 = 2612999) B2612999
theorem B2323631 : Blo 1547471 2323631 := bstep (se 1 (by rfl) ⟨1742723, by rfl⟩ : syracuseStep 2323631 = 3485447) B3485447
theorem B5223635 : Blo 1547471 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B5584283 : Blo 1547471 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B5223905 : Blo 1547471 5223905 := bstep (se 2 (by rfl) ⟨1958964, by rfl⟩ : syracuseStep 5223905 = 3917929) B3917929
theorem B2324039 : Blo 1547471 2324039 := bstep (se 1 (by rfl) ⟨1743029, by rfl⟩ : syracuseStep 2324039 = 3486059) B3486059
theorem B1742503 : Blo 1547471 1742503 := bstep (se 1 (by rfl) ⟨1306877, by rfl⟩ : syracuseStep 1742503 = 2613755) B2613755
theorem B2324135 : Blo 1547471 2324135 := bstep (se 1 (by rfl) ⟨1743101, by rfl⟩ : syracuseStep 2324135 = 3486203) B3486203
theorem B6797009 : Blo 1547471 6797009 := bstep (se 2 (by rfl) ⟨2548878, by rfl⟩ : syracuseStep 6797009 = 5097757) B5097757
theorem B16742123 : Blo 1547471 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B1742791 : Blo 1547471 1742791 := bstep (se 1 (by rfl) ⟨1307093, by rfl⟩ : syracuseStep 1742791 = 2614187) B2614187
theorem B1652719 : Blo 1547471 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B7837721 : Blo 1547471 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B17627219 : Blo 1547471 17627219 := bstep (se 1 (by rfl) ⟨13220414, by rfl⟩ : syracuseStep 17627219 = 26440829) B26440829
theorem B4184147 : Blo 1547471 4184147 := bstep (se 1 (by rfl) ⟨3138110, by rfl⟩ : syracuseStep 4184147 = 6276221) B6276221
theorem B5224553 : Blo 1547471 5224553 := bstep (se 2 (by rfl) ⟨1959207, by rfl⟩ : syracuseStep 5224553 = 3918415) B3918415
theorem B2611433 : Blo 1547471 2611433 := bstep (se 2 (by rfl) ⟨979287, by rfl⟩ : syracuseStep 2611433 = 1958575) B1958575
theorem B1743151 : Blo 1547471 1743151 := bstep (se 1 (by rfl) ⟨1307363, by rfl⟩ : syracuseStep 1743151 = 2614727) B2614727
theorem B25106897 : Blo 1547471 25106897 := bstep (se 2 (by rfl) ⟨9415086, by rfl⟩ : syracuseStep 25106897 = 18830173) B18830173
theorem B14883425 : Blo 1547471 14883425 := bstep (se 2 (by rfl) ⟨5581284, by rfl⟩ : syracuseStep 14883425 = 11162569) B11162569
theorem B2939807 : Blo 1547471 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B5225417 : Blo 1547471 5225417 := bstep (se 2 (by rfl) ⟨1959531, by rfl⟩ : syracuseStep 5225417 = 3919063) B3919063
theorem B8813519 : Blo 1547471 8813519 := bstep (se 1 (by rfl) ⟨6610139, by rfl⟩ : syracuseStep 8813519 = 13220279) B13220279
theorem B4775041 : Blo 1547471 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B17644715 : Blo 1547471 17644715 := bstep (se 1 (by rfl) ⟨13233536, by rfl⟩ : syracuseStep 17644715 = 26467073) B26467073
theorem B17882315 : Blo 1547471 17882315 := bstep (se 1 (by rfl) ⟨13411736, by rfl⟩ : syracuseStep 17882315 = 26823473) B26823473
theorem B5225687 : Blo 1547471 5225687 := bstep (se 1 (by rfl) ⟨3919265, by rfl⟩ : syracuseStep 5225687 = 7838531) B7838531
theorem B1547487 : Blo 1547471 1547487 := bstep (se 1 (by rfl) ⟨1160615, by rfl⟩ : syracuseStep 1547487 = 2321231) B2321231
theorem B11754881 : Blo 1547471 11754881 := bstep (se 2 (by rfl) ⟨4408080, by rfl⟩ : syracuseStep 11754881 = 8816161) B8816161
theorem B1547751 : Blo 1547471 1547751 := bstep (se 1 (by rfl) ⟨1160813, by rfl⟩ : syracuseStep 1547751 = 2321627) B2321627
theorem B2940391 : Blo 1547471 2940391 := bstep (se 1 (by rfl) ⟨2205293, by rfl⟩ : syracuseStep 2940391 = 4410587) B4410587
theorem B1547867 : Blo 1547471 1547867 := bstep (se 1 (by rfl) ⟨1160900, by rfl⟩ : syracuseStep 1547867 = 2321801) B2321801
theorem B1654363 : Blo 1547471 1654363 := bstep (se 1 (by rfl) ⟨1240772, by rfl⟩ : syracuseStep 1654363 = 2481545) B2481545
theorem B2612911 : Blo 1547471 2612911 := bstep (se 1 (by rfl) ⟨1959683, by rfl⟩ : syracuseStep 2612911 = 3919367) B3919367
theorem B5168827 : Blo 1547471 5168827 := bstep (se 1 (by rfl) ⟨3876620, by rfl⟩ : syracuseStep 5168827 = 7753241) B7753241
theorem B5226227 : Blo 1547471 5226227 := bstep (se 1 (by rfl) ⟨3919670, by rfl⟩ : syracuseStep 5226227 = 7839341) B7839341
theorem B1548103 : Blo 1547471 1548103 := bstep (se 1 (by rfl) ⟨1161077, by rfl⟩ : syracuseStep 1548103 = 2322155) B2322155
theorem B1548255 : Blo 1547471 1548255 := bstep (se 1 (by rfl) ⟨1161191, by rfl⟩ : syracuseStep 1548255 = 2322383) B2322383
theorem B2613215 : Blo 1547471 2613215 := bstep (se 1 (by rfl) ⟨1959911, by rfl⟩ : syracuseStep 2613215 = 3919823) B3919823
theorem B13230053 : Blo 1547471 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B4710523 : Blo 1547471 4710523 := bstep (se 1 (by rfl) ⟨3532892, by rfl⟩ : syracuseStep 4710523 = 7065785) B7065785
theorem B1548479 : Blo 1547471 1548479 := bstep (se 1 (by rfl) ⟨1161359, by rfl⟩ : syracuseStep 1548479 = 2322719) B2322719
theorem B1548495 : Blo 1547471 1548495 := bstep (se 1 (by rfl) ⟨1161371, by rfl⟩ : syracuseStep 1548495 = 2322743) B2322743
theorem B11157725 : Blo 1547471 11157725 := bstep (se 3 (by rfl) ⟨2092073, by rfl⟩ : syracuseStep 11157725 = 4184147) B4184147
theorem B1548543 : Blo 1547471 1548543 := bstep (se 1 (by rfl) ⟨1161407, by rfl⟩ : syracuseStep 1548543 = 2322815) B2322815
theorem B1548591 : Blo 1547471 1548591 := bstep (se 1 (by rfl) ⟨1161443, by rfl⟩ : syracuseStep 1548591 = 2322887) B2322887
theorem B9920825 : Blo 1547471 9920825 := bstep (se 2 (by rfl) ⟨3720309, by rfl⟩ : syracuseStep 9920825 = 7440619) B7440619
theorem B4710793 : Blo 1547471 4710793 := bstep (se 2 (by rfl) ⟨1766547, by rfl⟩ : syracuseStep 4710793 = 3533095) B3533095
theorem B8823269 : Blo 1547471 8823269 := bstep (se 4 (by rfl) ⟨827181, by rfl⟩ : syracuseStep 8823269 = 1654363) B1654363
theorem B1548827 : Blo 1547471 1548827 := bstep (se 1 (by rfl) ⟨1161620, by rfl⟩ : syracuseStep 1548827 = 2323241) B2323241
theorem B1548831 : Blo 1547471 1548831 := bstep (se 1 (by rfl) ⟨1161623, by rfl⟩ : syracuseStep 1548831 = 2323247) B2323247
theorem B1548911 : Blo 1547471 1548911 := bstep (se 1 (by rfl) ⟨1161683, by rfl⟩ : syracuseStep 1548911 = 2323367) B2323367
theorem B5882483 : Blo 1547471 5882483 := bstep (se 1 (by rfl) ⟨4411862, by rfl⟩ : syracuseStep 5882483 = 8823725) B8823725
theorem B4244129 : Blo 1547471 4244129 := bstep (se 2 (by rfl) ⟨1591548, by rfl⟩ : syracuseStep 4244129 = 3183097) B3183097
theorem B3482279 : Blo 1547471 3482279 := bstep (se 1 (by rfl) ⟨2611709, by rfl⟩ : syracuseStep 3482279 = 5223419) B5223419
theorem B1548967 : Blo 1547471 1548967 := bstep (se 1 (by rfl) ⟨1161725, by rfl⟩ : syracuseStep 1548967 = 2323451) B2323451
theorem B1549007 : Blo 1547471 1549007 := bstep (se 1 (by rfl) ⟨1161755, by rfl⟩ : syracuseStep 1549007 = 2323511) B2323511
theorem B7840475 : Blo 1547471 7840475 := bstep (se 1 (by rfl) ⟨5880356, by rfl⟩ : syracuseStep 7840475 = 11760713) B11760713
theorem B1549087 : Blo 1547471 1549087 := bstep (se 1 (by rfl) ⟨1161815, by rfl⟩ : syracuseStep 1549087 = 2323631) B2323631
theorem B5882665 : Blo 1547471 5882665 := bstep (se 2 (by rfl) ⟨2205999, by rfl⟩ : syracuseStep 5882665 = 4411999) B4411999
theorem B3482423 : Blo 1547471 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B3482603 : Blo 1547471 3482603 := bstep (se 1 (by rfl) ⟨2611952, by rfl⟩ : syracuseStep 3482603 = 5223905) B5223905
theorem B1549359 : Blo 1547471 1549359 := bstep (se 1 (by rfl) ⟨1162019, by rfl⟩ : syracuseStep 1549359 = 2324039) B2324039
theorem B5227631 : Blo 1547471 5227631 := bstep (se 1 (by rfl) ⟨3920723, by rfl⟩ : syracuseStep 5227631 = 7841447) B7841447
theorem B1549423 : Blo 1547471 1549423 := bstep (se 1 (by rfl) ⟨1162067, by rfl⟩ : syracuseStep 1549423 = 2324135) B2324135
theorem B4531339 : Blo 1547471 4531339 := bstep (se 1 (by rfl) ⟨3398504, by rfl⟩ : syracuseStep 4531339 = 6797009) B6797009
theorem B12551375 : Blo 1547471 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B5227739 : Blo 1547471 5227739 := bstep (se 1 (by rfl) ⟨3920804, by rfl⟩ : syracuseStep 5227739 = 7841609) B7841609
theorem B47703289 : Blo 1547471 47703289 := bstep (se 2 (by rfl) ⟨17888733, by rfl⟩ : syracuseStep 47703289 = 35777467) B35777467
theorem B2614585 : Blo 1547471 2614585 := bstep (se 2 (by rfl) ⟨980469, by rfl⟩ : syracuseStep 2614585 = 1960939) B1960939
theorem B3483035 : Blo 1547471 3483035 := bstep (se 1 (by rfl) ⟨2612276, by rfl⟩ : syracuseStep 3483035 = 5224553) B5224553
theorem B7439867 : Blo 1547471 7439867 := bstep (se 1 (by rfl) ⟨5579900, by rfl⟩ : syracuseStep 7439867 = 11159801) B11159801
theorem B6366721 : Blo 1547471 6366721 := bstep (se 2 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 6366721 = 4775041) B4775041
theorem B16737931 : Blo 1547471 16737931 := bstep (se 1 (by rfl) ⟨12553448, by rfl⟩ : syracuseStep 16737931 = 25106897) B25106897
theorem B9422507 : Blo 1547471 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B50923201 : Blo 1547471 50923201 := bstep (se 2 (by rfl) ⟨19096200, by rfl⟩ : syracuseStep 50923201 = 38192401) B38192401
theorem B9922283 : Blo 1547471 9922283 := bstep (se 1 (by rfl) ⟨7441712, by rfl⟩ : syracuseStep 9922283 = 14883425) B14883425
theorem B1959871 : Blo 1547471 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B7440329 : Blo 1547471 7440329 := bstep (se 2 (by rfl) ⟨2790123, by rfl⟩ : syracuseStep 7440329 = 5580247) B5580247
theorem B3483611 : Blo 1547471 3483611 := bstep (se 1 (by rfl) ⟨2612708, by rfl⟩ : syracuseStep 3483611 = 5225417) B5225417
theorem B5875679 : Blo 1547471 5875679 := bstep (se 1 (by rfl) ⟨4406759, by rfl⟩ : syracuseStep 5875679 = 8813519) B8813519
theorem B11921543 : Blo 1547471 11921543 := bstep (se 1 (by rfl) ⟨8941157, by rfl⟩ : syracuseStep 11921543 = 17882315) B17882315
theorem B3483791 : Blo 1547471 3483791 := bstep (se 1 (by rfl) ⟨2612843, by rfl⟩ : syracuseStep 3483791 = 5225687) B5225687
theorem B3483881 : Blo 1547471 3483881 := bstep (se 2 (by rfl) ⟨1306455, by rfl⟩ : syracuseStep 3483881 = 2612911) B2612911
theorem B6891769 : Blo 1547471 6891769 := bstep (se 2 (by rfl) ⟨2584413, by rfl⟩ : syracuseStep 6891769 = 5168827) B5168827
theorem B3918203 : Blo 1547471 3918203 := bstep (se 1 (by rfl) ⟨2938652, by rfl⟩ : syracuseStep 3918203 = 5877305) B5877305
theorem B3484151 : Blo 1547471 3484151 := bstep (se 1 (by rfl) ⟨2613113, by rfl⟩ : syracuseStep 3484151 = 5226227) B5226227
theorem B225995285 : Blo 1547471 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B6613609 : Blo 1547471 6613609 := bstep (se 2 (by rfl) ⟨2480103, by rfl⟩ : syracuseStep 6613609 = 4960207) B4960207
theorem B5655155 : Blo 1547471 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B2321375 : Blo 1547471 2321375 := bstep (se 1 (by rfl) ⟨1741031, by rfl⟩ : syracuseStep 2321375 = 3482063) B3482063
theorem B3484745 : Blo 1547471 3484745 := bstep (se 2 (by rfl) ⟨1306779, by rfl⟩ : syracuseStep 3484745 = 2613559) B2613559
theorem B7834967 : Blo 1547471 7834967 := bstep (se 1 (by rfl) ⟨5876225, by rfl⟩ : syracuseStep 7834967 = 11752451) B11752451
theorem B2321819 : Blo 1547471 2321819 := bstep (se 1 (by rfl) ⟨1741364, by rfl⟩ : syracuseStep 2321819 = 3482729) B3482729
theorem B23244347 : Blo 1547471 23244347 := bstep (se 1 (by rfl) ⟨17433260, by rfl⟩ : syracuseStep 23244347 = 34866521) B34866521
theorem B7843391 : Blo 1547471 7843391 := bstep (se 1 (by rfl) ⟨5882543, by rfl⟩ : syracuseStep 7843391 = 11765087) B11765087
theorem B96808547 : Blo 1547471 96808547 := bstep (se 1 (by rfl) ⟨72606410, by rfl⟩ : syracuseStep 96808547 = 145212821) B145212821
theorem B3722855 : Blo 1547471 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B13233779 : Blo 1547471 13233779 := bstep (se 1 (by rfl) ⟨9925334, by rfl⟩ : syracuseStep 13233779 = 19850669) B19850669
theorem B3305207 : Blo 1547471 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B2322239 : Blo 1547471 2322239 := bstep (se 1 (by rfl) ⟨1741679, by rfl⟩ : syracuseStep 2322239 = 3483359) B3483359
theorem B11161415 : Blo 1547471 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B2322425 : Blo 1547471 2322425 := bstep (se 2 (by rfl) ⟨870909, by rfl⟩ : syracuseStep 2322425 = 1741819) B1741819
theorem B11751479 : Blo 1547471 11751479 := bstep (se 1 (by rfl) ⟨8813609, by rfl⟩ : syracuseStep 11751479 = 17627219) B17627219
theorem B7835777 : Blo 1547471 7835777 := bstep (se 2 (by rfl) ⟨2938416, by rfl⟩ : syracuseStep 7835777 = 5876833) B5876833
theorem B1740955 : Blo 1547471 1740955 := bstep (se 1 (by rfl) ⟨1305716, by rfl⟩ : syracuseStep 1740955 = 2611433) B2611433
theorem B2322665 : Blo 1547471 2322665 := bstep (se 2 (by rfl) ⟨870999, by rfl⟩ : syracuseStep 2322665 = 1741999) B1741999
theorem B2322791 : Blo 1547471 2322791 := bstep (se 1 (by rfl) ⟨1742093, by rfl⟩ : syracuseStep 2322791 = 3484187) B3484187
theorem B6615539 : Blo 1547471 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B14889575 : Blo 1547471 14889575 := bstep (se 1 (by rfl) ⟨11167181, by rfl⟩ : syracuseStep 14889575 = 22334363) B22334363
theorem B3920521 : Blo 1547471 3920521 := bstep (se 2 (by rfl) ⟨1470195, by rfl⟩ : syracuseStep 3920521 = 2940391) B2940391
theorem B217461611 : Blo 1547471 217461611 := bstep (se 1 (by rfl) ⟨163096208, by rfl⟩ : syracuseStep 217461611 = 326192417) B326192417
theorem B2323337 : Blo 1547471 2323337 := bstep (se 2 (by rfl) ⟨871251, by rfl⟩ : syracuseStep 2323337 = 1742503) B1742503
theorem B7836587 : Blo 1547471 7836587 := bstep (se 1 (by rfl) ⟨5877440, by rfl⟩ : syracuseStep 7836587 = 11754881) B11754881
theorem B5223689 : Blo 1547471 5223689 := bstep (se 2 (by rfl) ⟨1958883, by rfl⟩ : syracuseStep 5223689 = 3917767) B3917767
theorem B2323721 : Blo 1547471 2323721 := bstep (se 2 (by rfl) ⟨871395, by rfl⟩ : syracuseStep 2323721 = 1742791) B1742791
theorem B1742143 : Blo 1547471 1742143 := bstep (se 1 (by rfl) ⟨1306607, by rfl⟩ : syracuseStep 1742143 = 2613215) B2613215
theorem B2323775 : Blo 1547471 2323775 := bstep (se 1 (by rfl) ⟨1742831, by rfl⟩ : syracuseStep 2323775 = 3485663) B3485663
theorem B8820035 : Blo 1547471 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B11310641 : Blo 1547471 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B7837235 : Blo 1547471 7837235 := bstep (se 1 (by rfl) ⟨5877926, by rfl⟩ : syracuseStep 7837235 = 11755853) B11755853
theorem B6616667 : Blo 1547471 6616667 := bstep (se 1 (by rfl) ⟨4962500, by rfl⟩ : syracuseStep 6616667 = 9925001) B9925001
theorem B2324201 : Blo 1547471 2324201 := bstep (se 2 (by rfl) ⟨871575, by rfl⟩ : syracuseStep 2324201 = 1743151) B1743151
theorem B5224175 : Blo 1547471 5224175 := bstep (se 1 (by rfl) ⟨3918131, by rfl⟩ : syracuseStep 5224175 = 7836263) B7836263
theorem B1742575 : Blo 1547471 1742575 := bstep (se 1 (by rfl) ⟨1306931, by rfl⟩ : syracuseStep 1742575 = 2613863) B2613863
theorem B2324207 : Blo 1547471 2324207 := bstep (se 1 (by rfl) ⟨1743155, by rfl⟩ : syracuseStep 2324207 = 3486311) B3486311
theorem B1742683 : Blo 1547471 1742683 := bstep (se 1 (by rfl) ⟨1307012, by rfl⟩ : syracuseStep 1742683 = 2614025) B2614025
theorem B2979755 : Blo 1547471 2979755 := bstep (se 1 (by rfl) ⟨2234816, by rfl⟩ : syracuseStep 2979755 = 4469633) B4469633
theorem B11753423 : Blo 1547471 11753423 := bstep (se 1 (by rfl) ⟨8815067, by rfl⟩ : syracuseStep 11753423 = 17630135) B17630135
theorem B3921959 : Blo 1547471 3921959 := bstep (se 1 (by rfl) ⟨2941469, by rfl⟩ : syracuseStep 3921959 = 5882939) B5882939
theorem B2939017 : Blo 1547471 2939017 := bstep (se 2 (by rfl) ⟨1102131, by rfl⟩ : syracuseStep 2939017 = 2204263) B2204263
theorem B1743079 : Blo 1547471 1743079 := bstep (se 1 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 1743079 = 2614619) B2614619
theorem B2611487 : Blo 1547471 2611487 := bstep (se 1 (by rfl) ⟨1958615, by rfl⟩ : syracuseStep 2611487 = 3917231) B3917231
theorem B5880221 : Blo 1547471 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B2611615 : Blo 1547471 2611615 := bstep (se 1 (by rfl) ⟨1958711, by rfl⟩ : syracuseStep 2611615 = 3917423) B3917423
theorem B2939419 : Blo 1547471 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B5225147 : Blo 1547471 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B2939951 : Blo 1547471 2939951 := bstep (se 1 (by rfl) ⟨2204963, by rfl⟩ : syracuseStep 2939951 = 4409927) B4409927
theorem B7838855 : Blo 1547471 7838855 := bstep (se 1 (by rfl) ⟨5879141, by rfl⟩ : syracuseStep 7838855 = 11758283) B11758283
theorem B1547471 : Blo 1547471 1547471 := bstep (se 1 (by rfl) ⟨1160603, by rfl⟩ : syracuseStep 1547471 = 2321207) B2321207
theorem B1547495 : Blo 1547471 1547495 := bstep (se 1 (by rfl) ⟨1160621, by rfl⟩ : syracuseStep 1547495 = 2321243) B2321243
theorem B1547591 : Blo 1547471 1547591 := bstep (se 1 (by rfl) ⟨1160693, by rfl⟩ : syracuseStep 1547591 = 2321387) B2321387
theorem B8936813 : Blo 1547471 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B11763143 : Blo 1547471 11763143 := bstep (se 1 (by rfl) ⟨8822357, by rfl⟩ : syracuseStep 11763143 = 17644715) B17644715
theorem B1547727 : Blo 1547471 1547727 := bstep (se 1 (by rfl) ⟨1160795, by rfl⟩ : syracuseStep 1547727 = 2321591) B2321591
theorem B1547887 : Blo 1547471 1547887 := bstep (se 1 (by rfl) ⟨1160915, by rfl⟩ : syracuseStep 1547887 = 2321831) B2321831
theorem B2612857 : Blo 1547471 2612857 := bstep (se 2 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 2612857 = 1959643) B1959643
theorem B1547943 : Blo 1547471 1547943 := bstep (se 1 (by rfl) ⟨1160957, by rfl⟩ : syracuseStep 1547943 = 2321915) B2321915
theorem B1548007 : Blo 1547471 1548007 := bstep (se 1 (by rfl) ⟨1161005, by rfl⟩ : syracuseStep 1548007 = 2322011) B2322011
theorem B1548063 : Blo 1547471 1548063 := bstep (se 1 (by rfl) ⟨1161047, by rfl⟩ : syracuseStep 1548063 = 2322095) B2322095
theorem B1548143 : Blo 1547471 1548143 := bstep (se 1 (by rfl) ⟨1161107, by rfl⟩ : syracuseStep 1548143 = 2322215) B2322215
theorem B1548199 : Blo 1547471 1548199 := bstep (se 1 (by rfl) ⟨1161149, by rfl⟩ : syracuseStep 1548199 = 2322299) B2322299
theorem B2203625 : Blo 1547471 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B7438483 : Blo 1547471 7438483 := bstep (se 1 (by rfl) ⟨5578862, by rfl⟩ : syracuseStep 7438483 = 11157725) B11157725
theorem B1548443 : Blo 1547471 1548443 := bstep (se 1 (by rfl) ⟨1161332, by rfl⟩ : syracuseStep 1548443 = 2322665) B2322665
theorem B1548527 : Blo 1547471 1548527 := bstep (se 1 (by rfl) ⟨1161395, by rfl⟩ : syracuseStep 1548527 = 2322791) B2322791
theorem B5882179 : Blo 1547471 5882179 := bstep (se 1 (by rfl) ⟨4411634, by rfl⟩ : syracuseStep 5882179 = 8823269) B8823269
theorem B5226983 : Blo 1547471 5226983 := bstep (se 1 (by rfl) ⟨3920237, by rfl⟩ : syracuseStep 5226983 = 7840475) B7840475
theorem B3482153 : Blo 1547471 3482153 := bstep (se 2 (by rfl) ⟨1305807, by rfl⟩ : syracuseStep 3482153 = 2611615) B2611615
theorem B1548891 : Blo 1547471 1548891 := bstep (se 1 (by rfl) ⟨1161668, by rfl⟩ : syracuseStep 1548891 = 2323337) B2323337
theorem B3482459 : Blo 1547471 3482459 := bstep (se 1 (by rfl) ⟨2611844, by rfl⟩ : syracuseStep 3482459 = 5223689) B5223689
theorem B1549147 : Blo 1547471 1549147 := bstep (se 1 (by rfl) ⟨1161860, by rfl⟩ : syracuseStep 1549147 = 2323721) B2323721
theorem B5227361 : Blo 1547471 5227361 := bstep (se 2 (by rfl) ⟨1960260, by rfl⟩ : syracuseStep 5227361 = 3920521) B3920521
theorem B1549183 : Blo 1547471 1549183 := bstep (se 1 (by rfl) ⟨1161887, by rfl⟩ : syracuseStep 1549183 = 2323775) B2323775
theorem B1549467 : Blo 1547471 1549467 := bstep (se 1 (by rfl) ⟨1162100, by rfl⟩ : syracuseStep 1549467 = 2324201) B2324201
theorem B3482783 : Blo 1547471 3482783 := bstep (se 1 (by rfl) ⟨2612087, by rfl⟩ : syracuseStep 3482783 = 5224175) B5224175
theorem B1549471 : Blo 1547471 1549471 := bstep (se 1 (by rfl) ⟨1162103, by rfl⟩ : syracuseStep 1549471 = 2324207) B2324207
theorem B3917119 : Blo 1547471 3917119 := bstep (se 1 (by rfl) ⟨2937839, by rfl⟩ : syracuseStep 3917119 = 5875679) B5875679
theorem B2614639 : Blo 1547471 2614639 := bstep (se 1 (by rfl) ⟨1960979, by rfl⟩ : syracuseStep 2614639 = 3921959) B3921959
theorem B7947695 : Blo 1547471 7947695 := bstep (se 1 (by rfl) ⟨5960771, by rfl⟩ : syracuseStep 7947695 = 11921543) B11921543
theorem B63604385 : Blo 1547471 63604385 := bstep (se 2 (by rfl) ⟨23851644, by rfl⟩ : syracuseStep 63604385 = 47703289) B47703289
theorem B25126685 : Blo 1547471 25126685 := bstep (se 3 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 25126685 = 9422507) B9422507
theorem B3483431 : Blo 1547471 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B8488961 : Blo 1547471 8488961 := bstep (se 2 (by rfl) ⟨3183360, by rfl⟩ : syracuseStep 8488961 = 6366721) B6366721
theorem B1959967 : Blo 1547471 1959967 := bstep (se 1 (by rfl) ⟨1469975, by rfl⟩ : syracuseStep 1959967 = 2939951) B2939951
theorem B3483809 : Blo 1547471 3483809 := bstep (se 2 (by rfl) ⟨1306428, by rfl⟩ : syracuseStep 3483809 = 2612857) B2612857
theorem B22317241 : Blo 1547471 22317241 := bstep (se 2 (by rfl) ⟨8368965, by rfl⟩ : syracuseStep 22317241 = 16737931) B16737931
theorem B29763773 : Blo 1547471 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B5957875 : Blo 1547471 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B67897601 : Blo 1547471 67897601 := bstep (se 2 (by rfl) ⟨25461600, by rfl⟩ : syracuseStep 67897601 = 50923201) B50923201
theorem B579897629 : Blo 1547471 579897629 := bstep (se 3 (by rfl) ⟨108730805, by rfl⟩ : syracuseStep 579897629 = 217461611) B217461611
theorem B7842095 : Blo 1547471 7842095 := bstep (se 1 (by rfl) ⟨5881571, by rfl⟩ : syracuseStep 7842095 = 11763143) B11763143
theorem B5228927 : Blo 1547471 5228927 := bstep (se 1 (by rfl) ⟨3921695, by rfl⟩ : syracuseStep 5228927 = 7843391) B7843391
theorem B64539031 : Blo 1547471 64539031 := bstep (se 1 (by rfl) ⟨48404273, by rfl⟩ : syracuseStep 64539031 = 96808547) B96808547
theorem B5876333 : Blo 1547471 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B7834319 : Blo 1547471 7834319 := bstep (se 1 (by rfl) ⟨5875739, by rfl⟩ : syracuseStep 7834319 = 11751479) B11751479
theorem B3918689 : Blo 1547471 3918689 := bstep (se 2 (by rfl) ⟨1469508, by rfl⟩ : syracuseStep 3918689 = 2939017) B2939017
theorem B2321273 : Blo 1547471 2321273 := bstep (se 2 (by rfl) ⟨870477, by rfl⟩ : syracuseStep 2321273 = 1740955) B1740955
theorem B6613883 : Blo 1547471 6613883 := bstep (se 1 (by rfl) ⟨4960412, by rfl⟩ : syracuseStep 6613883 = 9920825) B9920825
theorem B4410359 : Blo 1547471 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B2829419 : Blo 1547471 2829419 := bstep (se 1 (by rfl) ⟨2122064, by rfl⟩ : syracuseStep 2829419 = 4244129) B4244129
theorem B2321519 : Blo 1547471 2321519 := bstep (se 1 (by rfl) ⟨1741139, by rfl⟩ : syracuseStep 2321519 = 3482279) B3482279
theorem B2321615 : Blo 1547471 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B2321735 : Blo 1547471 2321735 := bstep (se 1 (by rfl) ⟨1741301, by rfl⟩ : syracuseStep 2321735 = 3482603) B3482603
theorem B3919225 : Blo 1547471 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B3485087 : Blo 1547471 3485087 := bstep (se 1 (by rfl) ⟨2613815, by rfl⟩ : syracuseStep 3485087 = 5227631) B5227631
theorem B8367583 : Blo 1547471 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B8818145 : Blo 1547471 8818145 := bstep (se 2 (by rfl) ⟨3306804, by rfl⟩ : syracuseStep 8818145 = 6613609) B6613609
theorem B3485159 : Blo 1547471 3485159 := bstep (se 1 (by rfl) ⟨2613869, by rfl⟩ : syracuseStep 3485159 = 5227739) B5227739
theorem B2322023 : Blo 1547471 2322023 := bstep (se 1 (by rfl) ⟨1741517, by rfl⟩ : syracuseStep 2322023 = 3483035) B3483035
theorem B4959911 : Blo 1547471 4959911 := bstep (se 1 (by rfl) ⟨3719933, by rfl⟩ : syracuseStep 4959911 = 7439867) B7439867
theorem B7540427 : Blo 1547471 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B7843553 : Blo 1547471 7843553 := bstep (se 2 (by rfl) ⟨2941332, by rfl⟩ : syracuseStep 7843553 = 5882665) B5882665
theorem B4411111 : Blo 1547471 4411111 := bstep (se 1 (by rfl) ⟨3308333, by rfl⟩ : syracuseStep 4411111 = 6616667) B6616667
theorem B6614855 : Blo 1547471 6614855 := bstep (se 1 (by rfl) ⟨4961141, by rfl⟩ : syracuseStep 6614855 = 9922283) B9922283
theorem B1986503 : Blo 1547471 1986503 := bstep (se 1 (by rfl) ⟨1489877, by rfl⟩ : syracuseStep 1986503 = 2979755) B2979755
theorem B4960219 : Blo 1547471 4960219 := bstep (se 1 (by rfl) ⟨3720164, by rfl⟩ : syracuseStep 4960219 = 7440329) B7440329
theorem B7835615 : Blo 1547471 7835615 := bstep (se 1 (by rfl) ⟨5876711, by rfl⟩ : syracuseStep 7835615 = 11753423) B11753423
theorem B2322407 : Blo 1547471 2322407 := bstep (se 1 (by rfl) ⟨1741805, by rfl⟩ : syracuseStep 2322407 = 3483611) B3483611
theorem B2322527 : Blo 1547471 2322527 := bstep (se 1 (by rfl) ⟨1741895, by rfl⟩ : syracuseStep 2322527 = 3483791) B3483791
theorem B2322587 : Blo 1547471 2322587 := bstep (se 1 (by rfl) ⟨1741940, by rfl⟩ : syracuseStep 2322587 = 3483881) B3483881
theorem B61984925 : Blo 1547471 61984925 := bstep (se 3 (by rfl) ⟨11622173, by rfl⟩ : syracuseStep 61984925 = 23244347) B23244347
theorem B6041785 : Blo 1547471 6041785 := bstep (se 2 (by rfl) ⟨2265669, by rfl⟩ : syracuseStep 6041785 = 4531339) B4531339
theorem B1740991 : Blo 1547471 1740991 := bstep (se 1 (by rfl) ⟨1305743, by rfl⟩ : syracuseStep 1740991 = 2611487) B2611487
theorem B3920147 : Blo 1547471 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B2322767 : Blo 1547471 2322767 := bstep (se 1 (by rfl) ⟨1742075, by rfl⟩ : syracuseStep 2322767 = 3484151) B3484151
theorem B150663523 : Blo 1547471 150663523 := bstep (se 1 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 150663523 = 225995285) B225995285
theorem B3486113 : Blo 1547471 3486113 := bstep (se 2 (by rfl) ⟨1307292, by rfl⟩ : syracuseStep 3486113 = 2614585) B2614585
theorem B2322857 : Blo 1547471 2322857 := bstep (se 2 (by rfl) ⟨871071, by rfl⟩ : syracuseStep 2322857 = 1742143) B1742143
theorem B2323163 : Blo 1547471 2323163 := bstep (se 1 (by rfl) ⟨1742372, by rfl⟩ : syracuseStep 2323163 = 3484745) B3484745
theorem B5223311 : Blo 1547471 5223311 := bstep (se 1 (by rfl) ⟨3917483, by rfl⟩ : syracuseStep 5223311 = 7834967) B7834967
theorem B2323433 : Blo 1547471 2323433 := bstep (se 2 (by rfl) ⟨871287, by rfl⟩ : syracuseStep 2323433 = 1742575) B1742575
theorem B2323577 : Blo 1547471 2323577 := bstep (se 2 (by rfl) ⟨871341, by rfl⟩ : syracuseStep 2323577 = 1742683) B1742683
theorem B5223851 : Blo 1547471 5223851 := bstep (se 1 (by rfl) ⟨3917888, by rfl⟩ : syracuseStep 5223851 = 7835777) B7835777
theorem B6280697 : Blo 1547471 6280697 := bstep (se 2 (by rfl) ⟨2355261, by rfl⟩ : syracuseStep 6280697 = 4710523) B4710523
theorem B2324105 : Blo 1547471 2324105 := bstep (se 2 (by rfl) ⟨871539, by rfl⟩ : syracuseStep 2324105 = 1743079) B1743079
theorem B9926383 : Blo 1547471 9926383 := bstep (se 1 (by rfl) ⟨7444787, by rfl⟩ : syracuseStep 9926383 = 14889575) B14889575
theorem B3921655 : Blo 1547471 3921655 := bstep (se 1 (by rfl) ⟨2941241, by rfl⟩ : syracuseStep 3921655 = 5882483) B5882483
theorem B6281057 : Blo 1547471 6281057 := bstep (se 2 (by rfl) ⟨2355396, by rfl⟩ : syracuseStep 6281057 = 4710793) B4710793
theorem B5224391 : Blo 1547471 5224391 := bstep (se 1 (by rfl) ⟨3918293, by rfl⟩ : syracuseStep 5224391 = 7836587) B7836587
theorem B5880023 : Blo 1547471 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B5224823 : Blo 1547471 5224823 := bstep (se 1 (by rfl) ⟨3918617, by rfl⟩ : syracuseStep 5224823 = 7837235) B7837235
theorem B36756101 : Blo 1547471 36756101 := bstep (se 4 (by rfl) ⟨3445884, by rfl⟩ : syracuseStep 36756101 = 6891769) B6891769
theorem B2612135 : Blo 1547471 2612135 := bstep (se 1 (by rfl) ⟨1959101, by rfl⟩ : syracuseStep 2612135 = 3918203) B3918203
theorem B9927613 : Blo 1547471 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B15080413 : Blo 1547471 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B1547583 : Blo 1547471 1547583 := bstep (se 1 (by rfl) ⟨1160687, by rfl⟩ : syracuseStep 1547583 = 2321375) B2321375
theorem B5225903 : Blo 1547471 5225903 := bstep (se 1 (by rfl) ⟨3919427, by rfl⟩ : syracuseStep 5225903 = 7838855) B7838855
theorem B1547879 : Blo 1547471 1547879 := bstep (se 1 (by rfl) ⟨1160909, by rfl⟩ : syracuseStep 1547879 = 2321819) B2321819
theorem B8822519 : Blo 1547471 8822519 := bstep (se 1 (by rfl) ⟨6616889, by rfl⟩ : syracuseStep 8822519 = 13233779) B13233779
theorem B2203471 : Blo 1547471 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B1548159 : Blo 1547471 1548159 := bstep (se 1 (by rfl) ⟨1161119, by rfl⟩ : syracuseStep 1548159 = 2322239) B2322239
theorem B2613161 : Blo 1547471 2613161 := bstep (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) B1959871
theorem B1548283 : Blo 1547471 1548283 := bstep (se 1 (by rfl) ⟨1161212, by rfl⟩ : syracuseStep 1548283 = 2322425) B2322425
theorem B2613289 : Blo 1547471 2613289 := bstep (se 2 (by rfl) ⟨979983, by rfl⟩ : syracuseStep 2613289 = 1959967) B1959967
theorem B1548351 : Blo 1547471 1548351 := bstep (se 1 (by rfl) ⟨1161263, by rfl⟩ : syracuseStep 1548351 = 2322527) B2322527
theorem B1548391 : Blo 1547471 1548391 := bstep (se 1 (by rfl) ⟨1161293, by rfl⟩ : syracuseStep 1548391 = 2322587) B2322587
theorem B2613431 : Blo 1547471 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B1548511 : Blo 1547471 1548511 := bstep (se 1 (by rfl) ⟨1161383, by rfl⟩ : syracuseStep 1548511 = 2322767) B2322767
theorem B1548571 : Blo 1547471 1548571 := bstep (se 1 (by rfl) ⟨1161428, by rfl⟩ : syracuseStep 1548571 = 2322857) B2322857
theorem B200884697 : Blo 1547471 200884697 := bstep (se 2 (by rfl) ⟨75331761, by rfl⟩ : syracuseStep 200884697 = 150663523) B150663523
theorem B1548775 : Blo 1547471 1548775 := bstep (se 1 (by rfl) ⟨1161581, by rfl⟩ : syracuseStep 1548775 = 2323163) B2323163
theorem B3482207 : Blo 1547471 3482207 := bstep (se 1 (by rfl) ⟨2611655, by rfl⟩ : syracuseStep 3482207 = 5223311) B5223311
theorem B1548955 : Blo 1547471 1548955 := bstep (se 1 (by rfl) ⟨1161716, by rfl⟩ : syracuseStep 1548955 = 2323433) B2323433
theorem B1549051 : Blo 1547471 1549051 := bstep (se 1 (by rfl) ⟨1161788, by rfl⟩ : syracuseStep 1549051 = 2323577) B2323577
theorem B3482567 : Blo 1547471 3482567 := bstep (se 1 (by rfl) ⟨2611925, by rfl⟩ : syracuseStep 3482567 = 5223851) B5223851
theorem B1549403 : Blo 1547471 1549403 := bstep (se 1 (by rfl) ⟨1162052, by rfl⟩ : syracuseStep 1549403 = 2324105) B2324105
theorem B42402923 : Blo 1547471 42402923 := bstep (se 1 (by rfl) ⟨31802192, by rfl⟩ : syracuseStep 42402923 = 63604385) B63604385
theorem B4187371 : Blo 1547471 4187371 := bstep (se 1 (by rfl) ⟨3140528, by rfl⟩ : syracuseStep 4187371 = 6281057) B6281057
theorem B3482927 : Blo 1547471 3482927 := bstep (se 1 (by rfl) ⟨2612195, by rfl⟩ : syracuseStep 3482927 = 5224391) B5224391
theorem B19842515 : Blo 1547471 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B386598419 : Blo 1547471 386598419 := bstep (se 1 (by rfl) ⟨289948814, by rfl⟩ : syracuseStep 386598419 = 579897629) B579897629
theorem B5228063 : Blo 1547471 5228063 := bstep (se 1 (by rfl) ⟨3921047, by rfl⟩ : syracuseStep 5228063 = 7842095) B7842095
theorem B3483215 : Blo 1547471 3483215 := bstep (se 1 (by rfl) ⟨2612411, by rfl⟩ : syracuseStep 3483215 = 5224823) B5224823
theorem B3917555 : Blo 1547471 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B24504067 : Blo 1547471 24504067 := bstep (se 1 (by rfl) ⟨18378050, by rfl⟩ : syracuseStep 24504067 = 36756101) B36756101
theorem B4409255 : Blo 1547471 4409255 := bstep (se 1 (by rfl) ⟨3306941, by rfl⟩ : syracuseStep 4409255 = 6613883) B6613883
theorem B1886279 : Blo 1547471 1886279 := bstep (se 1 (by rfl) ⟨1414709, by rfl⟩ : syracuseStep 1886279 = 2829419) B2829419
theorem B3483935 : Blo 1547471 3483935 := bstep (se 1 (by rfl) ⟨2612951, by rfl⟩ : syracuseStep 3483935 = 5225903) B5225903
theorem B5228873 : Blo 1547471 5228873 := bstep (se 2 (by rfl) ⟨1960827, by rfl⟩ : syracuseStep 5228873 = 3921655) B3921655
theorem B5229035 : Blo 1547471 5229035 := bstep (se 1 (by rfl) ⟨3921776, by rfl⟩ : syracuseStep 5229035 = 7843553) B7843553
theorem B4409903 : Blo 1547471 4409903 := bstep (se 1 (by rfl) ⟨3307427, by rfl⟩ : syracuseStep 4409903 = 6614855) B6614855
theorem B6613625 : Blo 1547471 6613625 := bstep (se 2 (by rfl) ⟨2480109, by rfl⟩ : syracuseStep 6613625 = 4960219) B4960219
theorem B41323283 : Blo 1547471 41323283 := bstep (se 1 (by rfl) ⟨30992462, by rfl⟩ : syracuseStep 41323283 = 61984925) B61984925
theorem B29756321 : Blo 1547471 29756321 := bstep (se 2 (by rfl) ⟨11158620, by rfl⟩ : syracuseStep 29756321 = 22317241) B22317241
theorem B8055713 : Blo 1547471 8055713 := bstep (se 2 (by rfl) ⟨3020892, by rfl⟩ : syracuseStep 8055713 = 6041785) B6041785
theorem B2321321 : Blo 1547471 2321321 := bstep (se 2 (by rfl) ⟨870495, by rfl⟩ : syracuseStep 2321321 = 1740991) B1740991
theorem B3484655 : Blo 1547471 3484655 := bstep (se 1 (by rfl) ⟨2613491, by rfl⟩ : syracuseStep 3484655 = 5226983) B5226983
theorem B2321435 : Blo 1547471 2321435 := bstep (se 1 (by rfl) ⟨1741076, by rfl⟩ : syracuseStep 2321435 = 3482153) B3482153
theorem B7842905 : Blo 1547471 7842905 := bstep (se 2 (by rfl) ⟨2941089, by rfl⟩ : syracuseStep 7842905 = 5882179) B5882179
theorem B86052041 : Blo 1547471 86052041 := bstep (se 2 (by rfl) ⟨32269515, by rfl⟩ : syracuseStep 86052041 = 64539031) B64539031
theorem B2321639 : Blo 1547471 2321639 := bstep (se 1 (by rfl) ⟨1741229, by rfl⟩ : syracuseStep 2321639 = 3482459) B3482459
theorem B3484907 : Blo 1547471 3484907 := bstep (se 1 (by rfl) ⟨2613680, by rfl⟩ : syracuseStep 3484907 = 5227361) B5227361
theorem B2321855 : Blo 1547471 2321855 := bstep (se 1 (by rfl) ⟨1741391, by rfl⟩ : syracuseStep 2321855 = 3482783) B3482783
theorem B2322287 : Blo 1547471 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B20107217 : Blo 1547471 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B16748525 : Blo 1547471 16748525 := bstep (se 3 (by rfl) ⟨3140348, by rfl⟩ : syracuseStep 16748525 = 6280697) B6280697
theorem B2322539 : Blo 1547471 2322539 := bstep (se 1 (by rfl) ⟨1741904, by rfl⟩ : syracuseStep 2322539 = 3483809) B3483809
theorem B3920015 : Blo 1547471 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B45265067 : Blo 1547471 45265067 := bstep (se 1 (by rfl) ⟨33948800, by rfl⟩ : syracuseStep 45265067 = 67897601) B67897601
theorem B3485951 : Blo 1547471 3485951 := bstep (se 1 (by rfl) ⟨2614463, by rfl⟩ : syracuseStep 3485951 = 5228927) B5228927
theorem B5222825 : Blo 1547471 5222825 := bstep (se 2 (by rfl) ⟨1958559, by rfl⟩ : syracuseStep 5222825 = 3917119) B3917119
theorem B13226429 : Blo 1547471 13226429 := bstep (se 3 (by rfl) ⟨2479955, by rfl⟩ : syracuseStep 13226429 = 4959911) B4959911
theorem B5222879 : Blo 1547471 5222879 := bstep (se 1 (by rfl) ⟨3917159, by rfl⟩ : syracuseStep 5222879 = 7834319) B7834319
theorem B3486185 : Blo 1547471 3486185 := bstep (se 2 (by rfl) ⟨1307319, by rfl⟩ : syracuseStep 3486185 = 2614639) B2614639
theorem B1741423 : Blo 1547471 1741423 := bstep (se 1 (by rfl) ⟨1306067, by rfl⟩ : syracuseStep 1741423 = 2612135) B2612135
theorem B21189365 : Blo 1547471 21189365 := bstep (se 5 (by rfl) ⟨993251, by rfl⟩ : syracuseStep 21189365 = 1986503) B1986503
theorem B2323391 : Blo 1547471 2323391 := bstep (se 1 (by rfl) ⟨1742543, by rfl⟩ : syracuseStep 2323391 = 3485087) B3485087
theorem B5878763 : Blo 1547471 5878763 := bstep (se 1 (by rfl) ⟨4409072, by rfl⟩ : syracuseStep 5878763 = 8818145) B8818145
theorem B13235177 : Blo 1547471 13235177 := bstep (se 2 (by rfl) ⟨4963191, by rfl⟩ : syracuseStep 13235177 = 9926383) B9926383
theorem B2323439 : Blo 1547471 2323439 := bstep (se 1 (by rfl) ⟨1742579, by rfl⟩ : syracuseStep 2323439 = 3485159) B3485159
theorem B2937961 : Blo 1547471 2937961 := bstep (se 2 (by rfl) ⟨1101735, by rfl⟩ : syracuseStep 2937961 = 2203471) B2203471
theorem B5026951 : Blo 1547471 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B1742107 : Blo 1547471 1742107 := bstep (se 1 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 1742107 = 2613161) B2613161
theorem B5223743 : Blo 1547471 5223743 := bstep (se 1 (by rfl) ⟨3917807, by rfl⟩ : syracuseStep 5223743 = 7835615) B7835615
theorem B9917977 : Blo 1547471 9917977 := bstep (se 2 (by rfl) ⟨3719241, by rfl⟩ : syracuseStep 9917977 = 7438483) B7438483
theorem B2324075 : Blo 1547471 2324075 := bstep (se 1 (by rfl) ⟨1743056, by rfl⟩ : syracuseStep 2324075 = 3486113) B3486113
theorem B5298463 : Blo 1547471 5298463 := bstep (se 1 (by rfl) ⟨3973847, by rfl⟩ : syracuseStep 5298463 = 7947695) B7947695
theorem B16751123 : Blo 1547471 16751123 := bstep (se 1 (by rfl) ⟨12563342, by rfl⟩ : syracuseStep 16751123 = 25126685) B25126685
theorem B13236817 : Blo 1547471 13236817 := bstep (se 2 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 13236817 = 9927613) B9927613
theorem B31775333 : Blo 1547471 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B5659307 : Blo 1547471 5659307 := bstep (se 1 (by rfl) ⟨4244480, by rfl⟩ : syracuseStep 5659307 = 8488961) B8488961
theorem B5225633 : Blo 1547471 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B2612459 : Blo 1547471 2612459 := bstep (se 1 (by rfl) ⟨1959344, by rfl⟩ : syracuseStep 2612459 = 3918689) B3918689
theorem B1547515 : Blo 1547471 1547515 := bstep (se 1 (by rfl) ⟨1160636, by rfl⟩ : syracuseStep 1547515 = 2321273) B2321273
theorem B11156777 : Blo 1547471 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B2940239 : Blo 1547471 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B1547679 : Blo 1547471 1547679 := bstep (se 1 (by rfl) ⟨1160759, by rfl⟩ : syracuseStep 1547679 = 2321519) B2321519
theorem B1547743 : Blo 1547471 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B1547823 : Blo 1547471 1547823 := bstep (se 1 (by rfl) ⟨1160867, by rfl⟩ : syracuseStep 1547823 = 2321735) B2321735
theorem B5881481 : Blo 1547471 5881481 := bstep (se 2 (by rfl) ⟨2205555, by rfl⟩ : syracuseStep 5881481 = 4411111) B4411111
theorem B1548015 : Blo 1547471 1548015 := bstep (se 1 (by rfl) ⟨1161011, by rfl⟩ : syracuseStep 1548015 = 2322023) B2322023
theorem B5881679 : Blo 1547471 5881679 := bstep (se 1 (by rfl) ⟨4411259, by rfl⟩ : syracuseStep 5881679 = 8822519) B8822519
theorem B1548271 : Blo 1547471 1548271 := bstep (se 1 (by rfl) ⟨1161203, by rfl⟩ : syracuseStep 1548271 = 2322407) B2322407
theorem B1548359 : Blo 1547471 1548359 := bstep (se 1 (by rfl) ⟨1161269, by rfl⟩ : syracuseStep 1548359 = 2322539) B2322539
theorem B2613343 : Blo 1547471 2613343 := bstep (se 1 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 2613343 = 3920015) B3920015
theorem B3481883 : Blo 1547471 3481883 := bstep (se 1 (by rfl) ⟨2611412, by rfl⟩ : syracuseStep 3481883 = 5222825) B5222825
theorem B133923131 : Blo 1547471 133923131 := bstep (se 1 (by rfl) ⟨100442348, by rfl⟩ : syracuseStep 133923131 = 200884697) B200884697
theorem B3481919 : Blo 1547471 3481919 := bstep (se 1 (by rfl) ⟨2611439, by rfl⟩ : syracuseStep 3481919 = 5222879) B5222879
theorem B1548927 : Blo 1547471 1548927 := bstep (se 1 (by rfl) ⟨1161695, by rfl⟩ : syracuseStep 1548927 = 2323391) B2323391
theorem B8823451 : Blo 1547471 8823451 := bstep (se 1 (by rfl) ⟨6617588, by rfl⟩ : syracuseStep 8823451 = 13235177) B13235177
theorem B1548959 : Blo 1547471 1548959 := bstep (se 1 (by rfl) ⟨1161719, by rfl⟩ : syracuseStep 1548959 = 2323439) B2323439
theorem B20120309 : Blo 1547471 20120309 := bstep (se 5 (by rfl) ⟨943139, by rfl⟩ : syracuseStep 20120309 = 1886279) B1886279
theorem B7840637 : Blo 1547471 7840637 := bstep (se 3 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 7840637 = 2940239) B2940239
theorem B3482495 : Blo 1547471 3482495 := bstep (se 1 (by rfl) ⟨2611871, by rfl⟩ : syracuseStep 3482495 = 5223743) B5223743
theorem B338936885 : Blo 1547471 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B1549383 : Blo 1547471 1549383 := bstep (se 1 (by rfl) ⟨1162037, by rfl⟩ : syracuseStep 1549383 = 2324075) B2324075
theorem B3917281 : Blo 1547471 3917281 := bstep (se 2 (by rfl) ⟨1468980, by rfl⟩ : syracuseStep 3917281 = 2937961) B2937961
theorem B6702601 : Blo 1547471 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B11167415 : Blo 1547471 11167415 := bstep (se 1 (by rfl) ⟨8375561, by rfl⟩ : syracuseStep 11167415 = 16751123) B16751123
theorem B4409083 : Blo 1547471 4409083 := bstep (se 1 (by rfl) ⟨3306812, by rfl⟩ : syracuseStep 4409083 = 6613625) B6613625
theorem B13223969 : Blo 1547471 13223969 := bstep (se 2 (by rfl) ⟨4958988, by rfl⟩ : syracuseStep 13223969 = 9917977) B9917977
theorem B5228603 : Blo 1547471 5228603 := bstep (se 1 (by rfl) ⟨3921452, by rfl⟩ : syracuseStep 5228603 = 7842905) B7842905
theorem B3483755 : Blo 1547471 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B32672089 : Blo 1547471 32672089 := bstep (se 2 (by rfl) ⟨12252033, by rfl⟩ : syracuseStep 32672089 = 24504067) B24504067
theorem B21481901 : Blo 1547471 21481901 := bstep (se 3 (by rfl) ⟨4027856, by rfl⟩ : syracuseStep 21481901 = 8055713) B8055713
theorem B13404811 : Blo 1547471 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B3484385 : Blo 1547471 3484385 := bstep (se 2 (by rfl) ⟨1306644, by rfl⟩ : syracuseStep 3484385 = 2613289) B2613289
theorem B8817619 : Blo 1547471 8817619 := bstep (se 1 (by rfl) ⟨6613214, by rfl⟩ : syracuseStep 8817619 = 13226429) B13226429
theorem B2321471 : Blo 1547471 2321471 := bstep (se 1 (by rfl) ⟨1741103, by rfl⟩ : syracuseStep 2321471 = 3482207) B3482207
theorem B14126243 : Blo 1547471 14126243 := bstep (se 1 (by rfl) ⟨10594682, by rfl⟩ : syracuseStep 14126243 = 21189365) B21189365
theorem B2321711 : Blo 1547471 2321711 := bstep (se 1 (by rfl) ⟨1741283, by rfl⟩ : syracuseStep 2321711 = 3482567) B3482567
theorem B3919175 : Blo 1547471 3919175 := bstep (se 1 (by rfl) ⟨2939381, by rfl⟩ : syracuseStep 3919175 = 5878763) B5878763
theorem B17649089 : Blo 1547471 17649089 := bstep (se 2 (by rfl) ⟨6618408, by rfl⟩ : syracuseStep 17649089 = 13236817) B13236817
theorem B2321897 : Blo 1547471 2321897 := bstep (se 2 (by rfl) ⟨870711, by rfl⟩ : syracuseStep 2321897 = 1741423) B1741423
theorem B2321951 : Blo 1547471 2321951 := bstep (se 1 (by rfl) ⟨1741463, by rfl⟩ : syracuseStep 2321951 = 3482927) B3482927
theorem B257732279 : Blo 1547471 257732279 := bstep (se 1 (by rfl) ⟨193299209, by rfl⟩ : syracuseStep 257732279 = 386598419) B386598419
theorem B3485375 : Blo 1547471 3485375 := bstep (se 1 (by rfl) ⟨2614031, by rfl⟩ : syracuseStep 3485375 = 5228063) B5228063
theorem B2322143 : Blo 1547471 2322143 := bstep (se 1 (by rfl) ⟨1741607, by rfl⟩ : syracuseStep 2322143 = 3483215) B3483215
theorem B11759741 : Blo 1547471 11759741 := bstep (se 3 (by rfl) ⟨2204951, by rfl⟩ : syracuseStep 11759741 = 4409903) B4409903
theorem B28258469 : Blo 1547471 28258469 := bstep (se 4 (by rfl) ⟨2649231, by rfl⟩ : syracuseStep 28258469 = 5298463) B5298463
theorem B2322623 : Blo 1547471 2322623 := bstep (se 1 (by rfl) ⟨1741967, by rfl⟩ : syracuseStep 2322623 = 3483935) B3483935
theorem B3485915 : Blo 1547471 3485915 := bstep (se 1 (by rfl) ⟨2614436, by rfl⟩ : syracuseStep 3485915 = 5228873) B5228873
theorem B5583161 : Blo 1547471 5583161 := bstep (se 2 (by rfl) ⟨2093685, by rfl⟩ : syracuseStep 5583161 = 4187371) B4187371
theorem B3486023 : Blo 1547471 3486023 := bstep (se 1 (by rfl) ⟨2614517, by rfl⟩ : syracuseStep 3486023 = 5229035) B5229035
theorem B2322809 : Blo 1547471 2322809 := bstep (se 2 (by rfl) ⟨871053, by rfl⟩ : syracuseStep 2322809 = 1742107) B1742107
theorem B3772871 : Blo 1547471 3772871 := bstep (se 1 (by rfl) ⟨2829653, by rfl⟩ : syracuseStep 3772871 = 5659307) B5659307
theorem B19837547 : Blo 1547471 19837547 := bstep (se 1 (by rfl) ⟨14878160, by rfl⟩ : syracuseStep 19837547 = 29756321) B29756321
theorem B2323103 : Blo 1547471 2323103 := bstep (se 1 (by rfl) ⟨1742327, by rfl⟩ : syracuseStep 2323103 = 3484655) B3484655
theorem B1741639 : Blo 1547471 1741639 := bstep (se 1 (by rfl) ⟨1306229, by rfl⟩ : syracuseStep 1741639 = 2612459) B2612459
theorem B2323271 : Blo 1547471 2323271 := bstep (se 1 (by rfl) ⟨1742453, by rfl⟩ : syracuseStep 2323271 = 3484907) B3484907
theorem B3920987 : Blo 1547471 3920987 := bstep (se 1 (by rfl) ⟨2940740, by rfl⟩ : syracuseStep 3920987 = 5881481) B5881481
theorem B3921119 : Blo 1547471 3921119 := bstep (se 1 (by rfl) ⟨2940839, by rfl⟩ : syracuseStep 3921119 = 5881679) B5881679
theorem B30176711 : Blo 1547471 30176711 := bstep (se 1 (by rfl) ⟨22632533, by rfl⟩ : syracuseStep 30176711 = 45265067) B45265067
theorem B1742287 : Blo 1547471 1742287 := bstep (se 1 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 1742287 = 2613431) B2613431
theorem B2323967 : Blo 1547471 2323967 := bstep (se 1 (by rfl) ⟨1742975, by rfl⟩ : syracuseStep 2323967 = 3485951) B3485951
theorem B2324123 : Blo 1547471 2324123 := bstep (se 1 (by rfl) ⟨1743092, by rfl⟩ : syracuseStep 2324123 = 3486185) B3486185
theorem B28268615 : Blo 1547471 28268615 := bstep (se 1 (by rfl) ⟨21201461, by rfl⟩ : syracuseStep 28268615 = 42402923) B42402923
theorem B13228343 : Blo 1547471 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B2611703 : Blo 1547471 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B2939503 : Blo 1547471 2939503 := bstep (se 1 (by rfl) ⟨2204627, by rfl⟩ : syracuseStep 2939503 = 4409255) B4409255
theorem B27548855 : Blo 1547471 27548855 := bstep (se 1 (by rfl) ⟨20661641, by rfl⟩ : syracuseStep 27548855 = 41323283) B41323283
theorem B1547547 : Blo 1547471 1547547 := bstep (se 1 (by rfl) ⟨1160660, by rfl⟩ : syracuseStep 1547547 = 2321321) B2321321
theorem B1547623 : Blo 1547471 1547623 := bstep (se 1 (by rfl) ⟨1160717, by rfl⟩ : syracuseStep 1547623 = 2321435) B2321435
theorem B57368027 : Blo 1547471 57368027 := bstep (se 1 (by rfl) ⟨43026020, by rfl⟩ : syracuseStep 57368027 = 86052041) B86052041
theorem B1547759 : Blo 1547471 1547759 := bstep (se 1 (by rfl) ⟨1160819, by rfl⟩ : syracuseStep 1547759 = 2321639) B2321639
theorem B7437851 : Blo 1547471 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B1547903 : Blo 1547471 1547903 := bstep (se 1 (by rfl) ⟨1160927, by rfl⟩ : syracuseStep 1547903 = 2321855) B2321855
theorem B1548191 : Blo 1547471 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B11165683 : Blo 1547471 11165683 := bstep (se 1 (by rfl) ⟨8374262, by rfl⟩ : syracuseStep 11165683 = 16748525) B16748525
theorem B7839827 : Blo 1547471 7839827 := bstep (se 1 (by rfl) ⟨5879870, by rfl⟩ : syracuseStep 7839827 = 11759741) B11759741
theorem B1548415 : Blo 1547471 1548415 := bstep (se 1 (by rfl) ⟨1161311, by rfl⟩ : syracuseStep 1548415 = 2322623) B2322623
theorem B75382973 : Blo 1547471 75382973 := bstep (se 3 (by rfl) ⟨14134307, by rfl⟩ : syracuseStep 75382973 = 28268615) B28268615
theorem B1548539 : Blo 1547471 1548539 := bstep (se 1 (by rfl) ⟨1161404, by rfl⟩ : syracuseStep 1548539 = 2322809) B2322809
theorem B2515247 : Blo 1547471 2515247 := bstep (se 1 (by rfl) ⟨1886435, by rfl⟩ : syracuseStep 2515247 = 3772871) B3772871
theorem B1548735 : Blo 1547471 1548735 := bstep (se 1 (by rfl) ⟨1161551, by rfl⟩ : syracuseStep 1548735 = 2323103) B2323103
theorem B1548847 : Blo 1547471 1548847 := bstep (se 1 (by rfl) ⟨1161635, by rfl⟩ : syracuseStep 1548847 = 2323271) B2323271
theorem B5227091 : Blo 1547471 5227091 := bstep (se 1 (by rfl) ⟨3920318, by rfl⟩ : syracuseStep 5227091 = 7840637) B7840637
theorem B2613991 : Blo 1547471 2613991 := bstep (se 1 (by rfl) ⟨1960493, by rfl⟩ : syracuseStep 2613991 = 3920987) B3920987
theorem B2614079 : Blo 1547471 2614079 := bstep (se 1 (by rfl) ⟨1960559, by rfl⟩ : syracuseStep 2614079 = 3921119) B3921119
theorem B11764601 : Blo 1547471 11764601 := bstep (se 2 (by rfl) ⟨4411725, by rfl⟩ : syracuseStep 11764601 = 8823451) B8823451
theorem B1549311 : Blo 1547471 1549311 := bstep (se 1 (by rfl) ⟨1161983, by rfl⟩ : syracuseStep 1549311 = 2323967) B2323967
theorem B1549415 : Blo 1547471 1549415 := bstep (se 1 (by rfl) ⟨1162061, by rfl⟩ : syracuseStep 1549415 = 2324123) B2324123
theorem B11756825 : Blo 1547471 11756825 := bstep (se 2 (by rfl) ⟨4408809, by rfl⟩ : syracuseStep 11756825 = 8817619) B8817619
theorem B8815979 : Blo 1547471 8815979 := bstep (se 1 (by rfl) ⟨6611984, by rfl⟩ : syracuseStep 8815979 = 13223969) B13223969
theorem B14321267 : Blo 1547471 14321267 := bstep (se 1 (by rfl) ⟨10740950, by rfl⟩ : syracuseStep 14321267 = 21481901) B21481901
theorem B11766059 : Blo 1547471 11766059 := bstep (se 1 (by rfl) ⟨8824544, by rfl⟩ : syracuseStep 11766059 = 17649089) B17649089
theorem B4958567 : Blo 1547471 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B171821519 : Blo 1547471 171821519 := bstep (se 1 (by rfl) ⟨128866139, by rfl⟩ : syracuseStep 171821519 = 257732279) B257732279
theorem B14887577 : Blo 1547471 14887577 := bstep (se 2 (by rfl) ⟨5582841, by rfl⟩ : syracuseStep 14887577 = 11165683) B11165683
theorem B3484457 : Blo 1547471 3484457 := bstep (se 2 (by rfl) ⟨1306671, by rfl⟩ : syracuseStep 3484457 = 2613343) B2613343
theorem B2321255 : Blo 1547471 2321255 := bstep (se 1 (by rfl) ⟨1740941, by rfl⟩ : syracuseStep 2321255 = 3481883) B3481883
theorem B3722107 : Blo 1547471 3722107 := bstep (se 1 (by rfl) ⟨2791580, by rfl⟩ : syracuseStep 3722107 = 5583161) B5583161
theorem B2321279 : Blo 1547471 2321279 := bstep (se 1 (by rfl) ⟨1740959, by rfl⟩ : syracuseStep 2321279 = 3481919) B3481919
theorem B13225031 : Blo 1547471 13225031 := bstep (se 1 (by rfl) ⟨9918773, by rfl⟩ : syracuseStep 13225031 = 19837547) B19837547
theorem B37669981 : Blo 1547471 37669981 := bstep (se 3 (by rfl) ⟨7063121, by rfl⟩ : syracuseStep 37669981 = 14126243) B14126243
theorem B13413539 : Blo 1547471 13413539 := bstep (se 1 (by rfl) ⟨10060154, by rfl⟩ : syracuseStep 13413539 = 20120309) B20120309
theorem B2321663 : Blo 1547471 2321663 := bstep (se 1 (by rfl) ⟨1741247, by rfl⟩ : syracuseStep 2321663 = 3482495) B3482495
theorem B3919337 : Blo 1547471 3919337 := bstep (se 2 (by rfl) ⟨1469751, by rfl⟩ : syracuseStep 3919337 = 2939503) B2939503
theorem B2322185 : Blo 1547471 2322185 := bstep (se 2 (by rfl) ⟨870819, by rfl⟩ : syracuseStep 2322185 = 1741639) B1741639
theorem B3485735 : Blo 1547471 3485735 := bstep (se 1 (by rfl) ⟨2614301, by rfl⟩ : syracuseStep 3485735 = 5228603) B5228603
theorem B2322503 : Blo 1547471 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B8818895 : Blo 1547471 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B1741135 : Blo 1547471 1741135 := bstep (se 1 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 1741135 = 2611703) B2611703
theorem B2322923 : Blo 1547471 2322923 := bstep (se 1 (by rfl) ⟨1742192, by rfl⟩ : syracuseStep 2322923 = 3484385) B3484385
theorem B2323049 : Blo 1547471 2323049 := bstep (se 2 (by rfl) ⟨871143, by rfl⟩ : syracuseStep 2323049 = 1742287) B1742287
theorem B5223041 : Blo 1547471 5223041 := bstep (se 2 (by rfl) ⟨1958640, by rfl⟩ : syracuseStep 5223041 = 3917281) B3917281
theorem B38245351 : Blo 1547471 38245351 := bstep (se 1 (by rfl) ⟨28684013, by rfl⟩ : syracuseStep 38245351 = 57368027) B57368027
theorem B5878777 : Blo 1547471 5878777 := bstep (se 2 (by rfl) ⟨2204541, by rfl⟩ : syracuseStep 5878777 = 4409083) B4409083
theorem B2323583 : Blo 1547471 2323583 := bstep (se 1 (by rfl) ⟨1742687, by rfl⟩ : syracuseStep 2323583 = 3485375) B3485375
theorem B18838979 : Blo 1547471 18838979 := bstep (se 1 (by rfl) ⟨14129234, by rfl⟩ : syracuseStep 18838979 = 28258469) B28258469
theorem B2323943 : Blo 1547471 2323943 := bstep (se 1 (by rfl) ⟨1742957, by rfl⟩ : syracuseStep 2323943 = 3485915) B3485915
theorem B89282087 : Blo 1547471 89282087 := bstep (se 1 (by rfl) ⟨66961565, by rfl⟩ : syracuseStep 89282087 = 133923131) B133923131
theorem B2324015 : Blo 1547471 2324015 := bstep (se 1 (by rfl) ⟨1743011, by rfl⟩ : syracuseStep 2324015 = 3486023) B3486023
theorem B43562785 : Blo 1547471 43562785 := bstep (se 2 (by rfl) ⟨16336044, by rfl⟩ : syracuseStep 43562785 = 32672089) B32672089
theorem B225957923 : Blo 1547471 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B17873081 : Blo 1547471 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B20117807 : Blo 1547471 20117807 := bstep (se 1 (by rfl) ⟨15088355, by rfl⟩ : syracuseStep 20117807 = 30176711) B30176711
theorem B7444943 : Blo 1547471 7444943 := bstep (se 1 (by rfl) ⟨5583707, by rfl⟩ : syracuseStep 7444943 = 11167415) B11167415
theorem B8936801 : Blo 1547471 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B1547647 : Blo 1547471 1547647 := bstep (se 1 (by rfl) ⟨1160735, by rfl⟩ : syracuseStep 1547647 = 2321471) B2321471
theorem B18365903 : Blo 1547471 18365903 := bstep (se 1 (by rfl) ⟨13774427, by rfl⟩ : syracuseStep 18365903 = 27548855) B27548855
theorem B1547807 : Blo 1547471 1547807 := bstep (se 1 (by rfl) ⟨1160855, by rfl⟩ : syracuseStep 1547807 = 2321711) B2321711
theorem B2612783 : Blo 1547471 2612783 := bstep (se 1 (by rfl) ⟨1959587, by rfl⟩ : syracuseStep 2612783 = 3919175) B3919175
theorem B1547931 : Blo 1547471 1547931 := bstep (se 1 (by rfl) ⟨1160948, by rfl⟩ : syracuseStep 1547931 = 2321897) B2321897
theorem B1547967 : Blo 1547471 1547967 := bstep (se 1 (by rfl) ⟨1160975, by rfl⟩ : syracuseStep 1547967 = 2321951) B2321951
theorem B1548095 : Blo 1547471 1548095 := bstep (se 1 (by rfl) ⟨1161071, by rfl⟩ : syracuseStep 1548095 = 2322143) B2322143
theorem B1548335 : Blo 1547471 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B5226551 : Blo 1547471 5226551 := bstep (se 1 (by rfl) ⟨3919913, by rfl⟩ : syracuseStep 5226551 = 7839827) B7839827
theorem B1548615 : Blo 1547471 1548615 := bstep (se 1 (by rfl) ⟨1161461, by rfl⟩ : syracuseStep 1548615 = 2322923) B2322923
theorem B1548699 : Blo 1547471 1548699 := bstep (se 1 (by rfl) ⟨1161524, by rfl⟩ : syracuseStep 1548699 = 2323049) B2323049
theorem B3482027 : Blo 1547471 3482027 := bstep (se 1 (by rfl) ⟨2611520, by rfl⟩ : syracuseStep 3482027 = 5223041) B5223041
theorem B1549055 : Blo 1547471 1549055 := bstep (se 1 (by rfl) ⟨1161791, by rfl⟩ : syracuseStep 1549055 = 2323583) B2323583
theorem B12559319 : Blo 1547471 12559319 := bstep (se 1 (by rfl) ⟨9419489, by rfl⟩ : syracuseStep 12559319 = 18838979) B18838979
theorem B1549295 : Blo 1547471 1549295 := bstep (se 1 (by rfl) ⟨1161971, by rfl⟩ : syracuseStep 1549295 = 2323943) B2323943
theorem B1549343 : Blo 1547471 1549343 := bstep (se 1 (by rfl) ⟨1162007, by rfl⟩ : syracuseStep 1549343 = 2324015) B2324015
theorem B50226641 : Blo 1547471 50226641 := bstep (se 2 (by rfl) ⟨18834990, by rfl⟩ : syracuseStep 50226641 = 37669981) B37669981
theorem B13411871 : Blo 1547471 13411871 := bstep (se 1 (by rfl) ⟨10058903, by rfl⟩ : syracuseStep 13411871 = 20117807) B20117807
theorem B8816687 : Blo 1547471 8816687 := bstep (se 1 (by rfl) ⟨6612515, by rfl⟩ : syracuseStep 8816687 = 13225031) B13225031
theorem B5957867 : Blo 1547471 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B58083713 : Blo 1547471 58083713 := bstep (se 2 (by rfl) ⟨21781392, by rfl⟩ : syracuseStep 58083713 = 43562785) B43562785
theorem B3484727 : Blo 1547471 3484727 := bstep (se 1 (by rfl) ⟨2613545, by rfl⟩ : syracuseStep 3484727 = 5227091) B5227091
theorem B2321513 : Blo 1547471 2321513 := bstep (se 2 (by rfl) ⟨870567, by rfl⟩ : syracuseStep 2321513 = 1741135) B1741135
theorem B7843067 : Blo 1547471 7843067 := bstep (se 1 (by rfl) ⟨5882300, by rfl⟩ : syracuseStep 7843067 = 11764601) B11764601
theorem B5877319 : Blo 1547471 5877319 := bstep (se 1 (by rfl) ⟨4407989, by rfl⟩ : syracuseStep 5877319 = 8815979) B8815979
theorem B3485321 : Blo 1547471 3485321 := bstep (se 2 (by rfl) ⟨1306995, by rfl⟩ : syracuseStep 3485321 = 2613991) B2613991
theorem B9547511 : Blo 1547471 9547511 := bstep (se 1 (by rfl) ⟨7160633, by rfl⟩ : syracuseStep 9547511 = 14321267) B14321267
theorem B150638615 : Blo 1547471 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B11915387 : Blo 1547471 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B7844039 : Blo 1547471 7844039 := bstep (se 1 (by rfl) ⟨5883029, by rfl⟩ : syracuseStep 7844039 = 11766059) B11766059
theorem B3305711 : Blo 1547471 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B9925051 : Blo 1547471 9925051 := bstep (se 1 (by rfl) ⟨7443788, by rfl⟩ : syracuseStep 9925051 = 14887577) B14887577
theorem B2322971 : Blo 1547471 2322971 := bstep (se 1 (by rfl) ⟨1742228, by rfl⟩ : syracuseStep 2322971 = 3484457) B3484457
theorem B8942359 : Blo 1547471 8942359 := bstep (se 1 (by rfl) ⟨6706769, by rfl⟩ : syracuseStep 8942359 = 13413539) B13413539
theorem B12243935 : Blo 1547471 12243935 := bstep (se 1 (by rfl) ⟨9182951, by rfl⟩ : syracuseStep 12243935 = 18365903) B18365903
theorem B1741855 : Blo 1547471 1741855 := bstep (se 1 (by rfl) ⟨1306391, by rfl⟩ : syracuseStep 1741855 = 2612783) B2612783
theorem B2323823 : Blo 1547471 2323823 := bstep (se 1 (by rfl) ⟨1742867, by rfl⟩ : syracuseStep 2323823 = 3485735) B3485735
theorem B50255315 : Blo 1547471 50255315 := bstep (se 1 (by rfl) ⟨37691486, by rfl⟩ : syracuseStep 50255315 = 75382973) B75382973
theorem B5879263 : Blo 1547471 5879263 := bstep (se 1 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 5879263 = 8818895) B8818895
theorem B1676831 : Blo 1547471 1676831 := bstep (se 1 (by rfl) ⟨1257623, by rfl⟩ : syracuseStep 1676831 = 2515247) B2515247
theorem B1742719 : Blo 1547471 1742719 := bstep (se 1 (by rfl) ⟨1307039, by rfl⟩ : syracuseStep 1742719 = 2614079) B2614079
theorem B7837883 : Blo 1547471 7837883 := bstep (se 1 (by rfl) ⟨5878412, by rfl⟩ : syracuseStep 7837883 = 11756825) B11756825
theorem B59521391 : Blo 1547471 59521391 := bstep (se 1 (by rfl) ⟨44641043, by rfl⟩ : syracuseStep 59521391 = 89282087) B89282087
theorem B4962809 : Blo 1547471 4962809 := bstep (se 2 (by rfl) ⟨1861053, by rfl⟩ : syracuseStep 4962809 = 3722107) B3722107
theorem B50993801 : Blo 1547471 50993801 := bstep (se 2 (by rfl) ⟨19122675, by rfl⟩ : syracuseStep 50993801 = 38245351) B38245351
theorem B7838369 : Blo 1547471 7838369 := bstep (se 2 (by rfl) ⟨2939388, by rfl⟩ : syracuseStep 7838369 = 5878777) B5878777
theorem B114547679 : Blo 1547471 114547679 := bstep (se 1 (by rfl) ⟨85910759, by rfl⟩ : syracuseStep 114547679 = 171821519) B171821519
theorem B4963295 : Blo 1547471 4963295 := bstep (se 1 (by rfl) ⟨3722471, by rfl⟩ : syracuseStep 4963295 = 7444943) B7444943
theorem B1547503 : Blo 1547471 1547503 := bstep (se 1 (by rfl) ⟨1160627, by rfl⟩ : syracuseStep 1547503 = 2321255) B2321255
theorem B1547519 : Blo 1547471 1547519 := bstep (se 1 (by rfl) ⟨1160639, by rfl⟩ : syracuseStep 1547519 = 2321279) B2321279
theorem B1547775 : Blo 1547471 1547775 := bstep (se 1 (by rfl) ⟨1160831, by rfl⟩ : syracuseStep 1547775 = 2321663) B2321663
theorem B2612891 : Blo 1547471 2612891 := bstep (se 1 (by rfl) ⟨1959668, by rfl⟩ : syracuseStep 2612891 = 3919337) B3919337
theorem B1548123 : Blo 1547471 1548123 := bstep (se 1 (by rfl) ⟨1161092, by rfl⟩ : syracuseStep 1548123 = 2322185) B2322185
theorem B100425743 : Blo 1547471 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B1548647 : Blo 1547471 1548647 := bstep (se 1 (by rfl) ⟨1161485, by rfl⟩ : syracuseStep 1548647 = 2322971) B2322971
theorem B8815229 : Blo 1547471 8815229 := bstep (se 3 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 8815229 = 3305711) B3305711
theorem B8372879 : Blo 1547471 8372879 := bstep (se 1 (by rfl) ⟨6279659, by rfl⟩ : syracuseStep 8372879 = 12559319) B12559319
theorem B1549215 : Blo 1547471 1549215 := bstep (se 1 (by rfl) ⟨1161911, by rfl⟩ : syracuseStep 1549215 = 2323823) B2323823
theorem B5228711 : Blo 1547471 5228711 := bstep (se 1 (by rfl) ⟨3921533, by rfl⟩ : syracuseStep 5228711 = 7843067) B7843067
theorem B3484367 : Blo 1547471 3484367 := bstep (se 1 (by rfl) ⟨2613275, by rfl⟩ : syracuseStep 3484367 = 5226551) B5226551
theorem B5229359 : Blo 1547471 5229359 := bstep (se 1 (by rfl) ⟨3922019, by rfl⟩ : syracuseStep 5229359 = 7844039) B7844039
theorem B2321351 : Blo 1547471 2321351 := bstep (se 1 (by rfl) ⟨1741013, by rfl⟩ : syracuseStep 2321351 = 3482027) B3482027
theorem B17886197 : Blo 1547471 17886197 := bstep (se 5 (by rfl) ⟨838415, by rfl⟩ : syracuseStep 17886197 = 1676831) B1676831
theorem B13233401 : Blo 1547471 13233401 := bstep (se 2 (by rfl) ⟨4962525, by rfl⟩ : syracuseStep 13233401 = 9925051) B9925051
theorem B8162623 : Blo 1547471 8162623 := bstep (se 1 (by rfl) ⟨6121967, by rfl⟩ : syracuseStep 8162623 = 12243935) B12243935
theorem B33484427 : Blo 1547471 33484427 := bstep (se 1 (by rfl) ⟨25113320, by rfl⟩ : syracuseStep 33484427 = 50226641) B50226641
theorem B8941247 : Blo 1547471 8941247 := bstep (se 1 (by rfl) ⟨6705935, by rfl⟩ : syracuseStep 8941247 = 13411871) B13411871
theorem B11923145 : Blo 1547471 11923145 := bstep (se 2 (by rfl) ⟨4471179, by rfl⟩ : syracuseStep 11923145 = 8942359) B8942359
theorem B5877791 : Blo 1547471 5877791 := bstep (se 1 (by rfl) ⟨4408343, by rfl⟩ : syracuseStep 5877791 = 8816687) B8816687
theorem B2322473 : Blo 1547471 2322473 := bstep (se 2 (by rfl) ⟨870927, by rfl⟩ : syracuseStep 2322473 = 1741855) B1741855
theorem B2323151 : Blo 1547471 2323151 := bstep (se 1 (by rfl) ⟨1742363, by rfl⟩ : syracuseStep 2323151 = 3484727) B3484727
theorem B7836425 : Blo 1547471 7836425 := bstep (se 2 (by rfl) ⟨2938659, by rfl⟩ : syracuseStep 7836425 = 5877319) B5877319
theorem B2323547 : Blo 1547471 2323547 := bstep (se 1 (by rfl) ⟨1742660, by rfl⟩ : syracuseStep 2323547 = 3485321) B3485321
theorem B1741927 : Blo 1547471 1741927 := bstep (se 1 (by rfl) ⟨1306445, by rfl⟩ : syracuseStep 1741927 = 2612891) B2612891
theorem B2323625 : Blo 1547471 2323625 := bstep (se 2 (by rfl) ⟨871359, by rfl⟩ : syracuseStep 2323625 = 1742719) B1742719
theorem B7943591 : Blo 1547471 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B33503543 : Blo 1547471 33503543 := bstep (se 1 (by rfl) ⟨25127657, by rfl⟩ : syracuseStep 33503543 = 50255315) B50255315
theorem B5225255 : Blo 1547471 5225255 := bstep (se 1 (by rfl) ⟨3918941, by rfl⟩ : syracuseStep 5225255 = 7837883) B7837883
theorem B3971911 : Blo 1547471 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B39680927 : Blo 1547471 39680927 := bstep (se 1 (by rfl) ⟨29760695, by rfl⟩ : syracuseStep 39680927 = 59521391) B59521391
theorem B38722475 : Blo 1547471 38722475 := bstep (se 1 (by rfl) ⟨29041856, by rfl⟩ : syracuseStep 38722475 = 58083713) B58083713
theorem B3308539 : Blo 1547471 3308539 := bstep (se 1 (by rfl) ⟨2481404, by rfl⟩ : syracuseStep 3308539 = 4962809) B4962809
theorem B33995867 : Blo 1547471 33995867 := bstep (se 1 (by rfl) ⟨25496900, by rfl⟩ : syracuseStep 33995867 = 50993801) B50993801
theorem B5225579 : Blo 1547471 5225579 := bstep (se 1 (by rfl) ⟨3919184, by rfl⟩ : syracuseStep 5225579 = 7838369) B7838369
theorem B7839017 : Blo 1547471 7839017 := bstep (se 2 (by rfl) ⟨2939631, by rfl⟩ : syracuseStep 7839017 = 5879263) B5879263
theorem B25460029 : Blo 1547471 25460029 := bstep (se 3 (by rfl) ⟨4773755, by rfl⟩ : syracuseStep 25460029 = 9547511) B9547511
theorem B76365119 : Blo 1547471 76365119 := bstep (se 1 (by rfl) ⟨57273839, by rfl⟩ : syracuseStep 76365119 = 114547679) B114547679
theorem B3308863 : Blo 1547471 3308863 := bstep (se 1 (by rfl) ⟨2481647, by rfl⟩ : syracuseStep 3308863 = 4963295) B4963295
theorem B1547675 : Blo 1547471 1547675 := bstep (se 1 (by rfl) ⟨1160756, by rfl⟩ : syracuseStep 1547675 = 2321513) B2321513
theorem B1548315 : Blo 1547471 1548315 := bstep (se 1 (by rfl) ⟨1161236, by rfl⟩ : syracuseStep 1548315 = 2322473) B2322473
theorem B1548767 : Blo 1547471 1548767 := bstep (se 1 (by rfl) ⟨1161575, by rfl⟩ : syracuseStep 1548767 = 2323151) B2323151
theorem B1549031 : Blo 1547471 1549031 := bstep (se 1 (by rfl) ⟨1161773, by rfl⟩ : syracuseStep 1549031 = 2323547) B2323547
theorem B1549083 : Blo 1547471 1549083 := bstep (se 1 (by rfl) ⟨1161812, by rfl⟩ : syracuseStep 1549083 = 2323625) B2323625
theorem B3483503 : Blo 1547471 3483503 := bstep (se 1 (by rfl) ⟨2612627, by rfl⟩ : syracuseStep 3483503 = 5225255) B5225255
theorem B26453951 : Blo 1547471 26453951 := bstep (se 1 (by rfl) ⟨19840463, by rfl⟩ : syracuseStep 26453951 = 39680927) B39680927
theorem B3483719 : Blo 1547471 3483719 := bstep (se 1 (by rfl) ⟨2612789, by rfl⟩ : syracuseStep 3483719 = 5225579) B5225579
theorem B7948763 : Blo 1547471 7948763 := bstep (se 1 (by rfl) ⟨5961572, by rfl⟩ : syracuseStep 7948763 = 11923145) B11923145
theorem B47696525 : Blo 1547471 47696525 := bstep (se 3 (by rfl) ⟨8943098, by rfl⟩ : syracuseStep 47696525 = 17886197) B17886197
theorem B3918527 : Blo 1547471 3918527 := bstep (se 1 (by rfl) ⟨2938895, by rfl⟩ : syracuseStep 3918527 = 5877791) B5877791
theorem B90655645 : Blo 1547471 90655645 := bstep (se 3 (by rfl) ⟨16997933, by rfl⟩ : syracuseStep 90655645 = 33995867) B33995867
theorem B5876819 : Blo 1547471 5876819 := bstep (se 1 (by rfl) ⟨4407614, by rfl⟩ : syracuseStep 5876819 = 8815229) B8815229
theorem B5581919 : Blo 1547471 5581919 := bstep (se 1 (by rfl) ⟨4186439, by rfl⟩ : syracuseStep 5581919 = 8372879) B8372879
theorem B5295727 : Blo 1547471 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B5295881 : Blo 1547471 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B4411385 : Blo 1547471 4411385 := bstep (se 2 (by rfl) ⟨1654269, by rfl⟩ : syracuseStep 4411385 = 3308539) B3308539
theorem B3485807 : Blo 1547471 3485807 := bstep (se 1 (by rfl) ⟨2614355, by rfl⟩ : syracuseStep 3485807 = 5228711) B5228711
theorem B2322569 : Blo 1547471 2322569 := bstep (se 2 (by rfl) ⟨870963, by rfl⟩ : syracuseStep 2322569 = 1741927) B1741927
theorem B22335695 : Blo 1547471 22335695 := bstep (se 1 (by rfl) ⟨16751771, by rfl⟩ : syracuseStep 22335695 = 33503543) B33503543
theorem B10883497 : Blo 1547471 10883497 := bstep (se 2 (by rfl) ⟨4081311, by rfl⟩ : syracuseStep 10883497 = 8162623) B8162623
theorem B4411817 : Blo 1547471 4411817 := bstep (se 2 (by rfl) ⟨1654431, by rfl⟩ : syracuseStep 4411817 = 3308863) B3308863
theorem B2322911 : Blo 1547471 2322911 := bstep (se 1 (by rfl) ⟨1742183, by rfl⟩ : syracuseStep 2322911 = 3484367) B3484367
theorem B3486239 : Blo 1547471 3486239 := bstep (se 1 (by rfl) ⟨2614679, by rfl⟩ : syracuseStep 3486239 = 5229359) B5229359
theorem B50910079 : Blo 1547471 50910079 := bstep (se 1 (by rfl) ⟨38182559, by rfl⟩ : syracuseStep 50910079 = 76365119) B76365119
theorem B5960831 : Blo 1547471 5960831 := bstep (se 1 (by rfl) ⟨4470623, by rfl⟩ : syracuseStep 5960831 = 8941247) B8941247
theorem B66950495 : Blo 1547471 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B5224283 : Blo 1547471 5224283 := bstep (se 1 (by rfl) ⟨3918212, by rfl⟩ : syracuseStep 5224283 = 7836425) B7836425
theorem B33946705 : Blo 1547471 33946705 := bstep (se 2 (by rfl) ⟨12730014, by rfl⟩ : syracuseStep 33946705 = 25460029) B25460029
theorem B1547567 : Blo 1547471 1547567 := bstep (se 1 (by rfl) ⟨1160675, by rfl⟩ : syracuseStep 1547567 = 2321351) B2321351
theorem B8822267 : Blo 1547471 8822267 := bstep (se 1 (by rfl) ⟨6616700, by rfl⟩ : syracuseStep 8822267 = 13233401) B13233401
theorem B5226011 : Blo 1547471 5226011 := bstep (se 1 (by rfl) ⟨3919508, by rfl⟩ : syracuseStep 5226011 = 7839017) B7839017
theorem B22322951 : Blo 1547471 22322951 := bstep (se 1 (by rfl) ⟨16742213, by rfl⟩ : syracuseStep 22322951 = 33484427) B33484427
theorem B103259933 : Blo 1547471 103259933 := bstep (se 3 (by rfl) ⟨19361237, by rfl⟩ : syracuseStep 103259933 = 38722475) B38722475
theorem B1548379 : Blo 1547471 1548379 := bstep (se 1 (by rfl) ⟨1161284, by rfl⟩ : syracuseStep 1548379 = 2322569) B2322569
theorem B14885117 : Blo 1547471 14885117 := bstep (se 3 (by rfl) ⟨2790959, by rfl⟩ : syracuseStep 14885117 = 5581919) B5581919
theorem B2941211 : Blo 1547471 2941211 := bstep (se 1 (by rfl) ⟨2205908, by rfl⟩ : syracuseStep 2941211 = 4411817) B4411817
theorem B1548607 : Blo 1547471 1548607 := bstep (se 1 (by rfl) ⟨1161455, by rfl⟩ : syracuseStep 1548607 = 2322911) B2322911
theorem B67880105 : Blo 1547471 67880105 := bstep (se 2 (by rfl) ⟨25455039, by rfl⟩ : syracuseStep 67880105 = 50910079) B50910079
theorem B120874193 : Blo 1547471 120874193 := bstep (se 2 (by rfl) ⟨45327822, by rfl⟩ : syracuseStep 120874193 = 90655645) B90655645
theorem B3482855 : Blo 1547471 3482855 := bstep (se 1 (by rfl) ⟨2612141, by rfl⟩ : syracuseStep 3482855 = 5224283) B5224283
theorem B45262273 : Blo 1547471 45262273 := bstep (se 2 (by rfl) ⟨16973352, by rfl⟩ : syracuseStep 45262273 = 33946705) B33946705
theorem B2940923 : Blo 1547471 2940923 := bstep (se 1 (by rfl) ⟨2205692, by rfl⟩ : syracuseStep 2940923 = 4411385) B4411385
theorem B3917879 : Blo 1547471 3917879 := bstep (se 1 (by rfl) ⟨2938409, by rfl⟩ : syracuseStep 3917879 = 5876819) B5876819
theorem B3484007 : Blo 1547471 3484007 := bstep (se 1 (by rfl) ⟨2613005, by rfl⟩ : syracuseStep 3484007 = 5226011) B5226011
theorem B68839955 : Blo 1547471 68839955 := bstep (se 1 (by rfl) ⟨51629966, by rfl⟩ : syracuseStep 68839955 = 103259933) B103259933
theorem B15895549 : Blo 1547471 15895549 := bstep (se 3 (by rfl) ⟨2980415, by rfl⟩ : syracuseStep 15895549 = 5960831) B5960831
theorem B14511329 : Blo 1547471 14511329 := bstep (se 2 (by rfl) ⟨5441748, by rfl⟩ : syracuseStep 14511329 = 10883497) B10883497
theorem B44633663 : Blo 1547471 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B2322335 : Blo 1547471 2322335 := bstep (se 1 (by rfl) ⟨1741751, by rfl⟩ : syracuseStep 2322335 = 3483503) B3483503
theorem B2322479 : Blo 1547471 2322479 := bstep (se 1 (by rfl) ⟨1741859, by rfl⟩ : syracuseStep 2322479 = 3483719) B3483719
theorem B31797683 : Blo 1547471 31797683 := bstep (se 1 (by rfl) ⟨23848262, by rfl⟩ : syracuseStep 31797683 = 47696525) B47696525
theorem B14881967 : Blo 1547471 14881967 := bstep (se 1 (by rfl) ⟨11161475, by rfl⟩ : syracuseStep 14881967 = 22322951) B22322951
theorem B2323871 : Blo 1547471 2323871 := bstep (se 1 (by rfl) ⟨1742903, by rfl⟩ : syracuseStep 2323871 = 3485807) B3485807
theorem B14890463 : Blo 1547471 14890463 := bstep (se 1 (by rfl) ⟨11167847, by rfl⟩ : syracuseStep 14890463 = 22335695) B22335695
theorem B2324159 : Blo 1547471 2324159 := bstep (se 1 (by rfl) ⟨1743119, by rfl⟩ : syracuseStep 2324159 = 3486239) B3486239
theorem B17635967 : Blo 1547471 17635967 := bstep (se 1 (by rfl) ⟨13226975, by rfl⟩ : syracuseStep 17635967 = 26453951) B26453951
theorem B5299175 : Blo 1547471 5299175 := bstep (se 1 (by rfl) ⟨3974381, by rfl⟩ : syracuseStep 5299175 = 7948763) B7948763
theorem B2612351 : Blo 1547471 2612351 := bstep (se 1 (by rfl) ⟨1959263, by rfl⟩ : syracuseStep 2612351 = 3918527) B3918527
theorem B14122349 : Blo 1547471 14122349 := bstep (se 3 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 14122349 = 5295881) B5295881
theorem B7060969 : Blo 1547471 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B5881511 : Blo 1547471 5881511 := bstep (se 1 (by rfl) ⟨4411133, by rfl⟩ : syracuseStep 5881511 = 8822267) B8822267
theorem B1548319 : Blo 1547471 1548319 := bstep (se 1 (by rfl) ⟨1161239, by rfl⟩ : syracuseStep 1548319 = 2322479) B2322479
theorem B45253403 : Blo 1547471 45253403 := bstep (se 1 (by rfl) ⟨33940052, by rfl⟩ : syracuseStep 45253403 = 67880105) B67880105
theorem B9921311 : Blo 1547471 9921311 := bstep (se 1 (by rfl) ⟨7440983, by rfl⟩ : syracuseStep 9921311 = 14881967) B14881967
theorem B1549247 : Blo 1547471 1549247 := bstep (se 1 (by rfl) ⟨1161935, by rfl⟩ : syracuseStep 1549247 = 2323871) B2323871
theorem B1549439 : Blo 1547471 1549439 := bstep (se 1 (by rfl) ⟨1162079, by rfl⟩ : syracuseStep 1549439 = 2324159) B2324159
theorem B21194065 : Blo 1547471 21194065 := bstep (se 2 (by rfl) ⟨7947774, by rfl⟩ : syracuseStep 21194065 = 15895549) B15895549
theorem B45893303 : Blo 1547471 45893303 := bstep (se 1 (by rfl) ⟨34419977, by rfl⟩ : syracuseStep 45893303 = 68839955) B68839955
theorem B11757311 : Blo 1547471 11757311 := bstep (se 1 (by rfl) ⟨8817983, by rfl⟩ : syracuseStep 11757311 = 17635967) B17635967
theorem B9414625 : Blo 1547471 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B3532783 : Blo 1547471 3532783 := bstep (se 1 (by rfl) ⟨2649587, by rfl⟩ : syracuseStep 3532783 = 5299175) B5299175
theorem B9414899 : Blo 1547471 9414899 := bstep (se 1 (by rfl) ⟨7061174, by rfl⟩ : syracuseStep 9414899 = 14122349) B14122349
theorem B29755775 : Blo 1547471 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B1960615 : Blo 1547471 1960615 := bstep (se 1 (by rfl) ⟨1470461, by rfl⟩ : syracuseStep 1960615 = 2940923) B2940923
theorem B9923411 : Blo 1547471 9923411 := bstep (se 1 (by rfl) ⟨7442558, by rfl⟩ : syracuseStep 9923411 = 14885117) B14885117
theorem B7843229 : Blo 1547471 7843229 := bstep (se 3 (by rfl) ⟨1470605, by rfl⟩ : syracuseStep 7843229 = 2941211) B2941211
theorem B2321903 : Blo 1547471 2321903 := bstep (se 1 (by rfl) ⟨1741427, by rfl⟩ : syracuseStep 2321903 = 3482855) B3482855
theorem B2322671 : Blo 1547471 2322671 := bstep (se 1 (by rfl) ⟨1742003, by rfl⟩ : syracuseStep 2322671 = 3484007) B3484007
theorem B1741567 : Blo 1547471 1741567 := bstep (se 1 (by rfl) ⟨1306175, by rfl⟩ : syracuseStep 1741567 = 2612351) B2612351
theorem B3921007 : Blo 1547471 3921007 := bstep (se 1 (by rfl) ⟨2940755, by rfl⟩ : syracuseStep 3921007 = 5881511) B5881511
theorem B21198455 : Blo 1547471 21198455 := bstep (se 1 (by rfl) ⟨15898841, by rfl⟩ : syracuseStep 21198455 = 31797683) B31797683
theorem B80582795 : Blo 1547471 80582795 := bstep (se 1 (by rfl) ⟨60437096, by rfl⟩ : syracuseStep 80582795 = 120874193) B120874193
theorem B9926975 : Blo 1547471 9926975 := bstep (se 1 (by rfl) ⟨7445231, by rfl⟩ : syracuseStep 9926975 = 14890463) B14890463
theorem B2611919 : Blo 1547471 2611919 := bstep (se 1 (by rfl) ⟨1958939, by rfl⟩ : syracuseStep 2611919 = 3917879) B3917879
theorem B60349697 : Blo 1547471 60349697 := bstep (se 2 (by rfl) ⟨22631136, by rfl⟩ : syracuseStep 60349697 = 45262273) B45262273
theorem B9674219 : Blo 1547471 9674219 := bstep (se 1 (by rfl) ⟨7255664, by rfl⟩ : syracuseStep 9674219 = 14511329) B14511329
theorem B1548223 : Blo 1547471 1548223 := bstep (se 1 (by rfl) ⟨1161167, by rfl⟩ : syracuseStep 1548223 = 2322335) B2322335
theorem B1548447 : Blo 1547471 1548447 := bstep (se 1 (by rfl) ⟨1161335, by rfl⟩ : syracuseStep 1548447 = 2322671) B2322671
theorem B2614153 : Blo 1547471 2614153 := bstep (se 2 (by rfl) ⟨980307, by rfl⟩ : syracuseStep 2614153 = 1960615) B1960615
theorem B14132303 : Blo 1547471 14132303 := bstep (se 1 (by rfl) ⟨10599227, by rfl⟩ : syracuseStep 14132303 = 21198455) B21198455
theorem B5228009 : Blo 1547471 5228009 := bstep (se 2 (by rfl) ⟨1960503, by rfl⟩ : syracuseStep 5228009 = 3921007) B3921007
theorem B6276599 : Blo 1547471 6276599 := bstep (se 1 (by rfl) ⟨4707449, by rfl⟩ : syracuseStep 6276599 = 9414899) B9414899
theorem B113035013 : Blo 1547471 113035013 := bstep (se 4 (by rfl) ⟨10597032, by rfl⟩ : syracuseStep 113035013 = 21194065) B21194065
theorem B40233131 : Blo 1547471 40233131 := bstep (se 1 (by rfl) ⟨30174848, by rfl⟩ : syracuseStep 40233131 = 60349697) B60349697
theorem B5228819 : Blo 1547471 5228819 := bstep (se 1 (by rfl) ⟨3921614, by rfl⟩ : syracuseStep 5228819 = 7843229) B7843229
theorem B6449479 : Blo 1547471 6449479 := bstep (se 1 (by rfl) ⟨4837109, by rfl⟩ : syracuseStep 6449479 = 9674219) B9674219
theorem B12552833 : Blo 1547471 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B6614207 : Blo 1547471 6614207 := bstep (se 1 (by rfl) ⟨4960655, by rfl⟩ : syracuseStep 6614207 = 9921311) B9921311
theorem B2322089 : Blo 1547471 2322089 := bstep (se 2 (by rfl) ⟨870783, by rfl⟩ : syracuseStep 2322089 = 1741567) B1741567
theorem B19837183 : Blo 1547471 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B1741279 : Blo 1547471 1741279 := bstep (se 1 (by rfl) ⟨1305959, by rfl⟩ : syracuseStep 1741279 = 2611919) B2611919
theorem B6615607 : Blo 1547471 6615607 := bstep (se 1 (by rfl) ⟨4961705, by rfl⟩ : syracuseStep 6615607 = 9923411) B9923411
theorem B30168935 : Blo 1547471 30168935 := bstep (se 1 (by rfl) ⟨22626701, by rfl⟩ : syracuseStep 30168935 = 45253403) B45253403
theorem B30595535 : Blo 1547471 30595535 := bstep (se 1 (by rfl) ⟨22946651, by rfl⟩ : syracuseStep 30595535 = 45893303) B45893303
theorem B7838207 : Blo 1547471 7838207 := bstep (se 1 (by rfl) ⟨5878655, by rfl⟩ : syracuseStep 7838207 = 11757311) B11757311
theorem B53721863 : Blo 1547471 53721863 := bstep (se 1 (by rfl) ⟨40291397, by rfl⟩ : syracuseStep 53721863 = 80582795) B80582795
theorem B6617983 : Blo 1547471 6617983 := bstep (se 1 (by rfl) ⟨4963487, by rfl⟩ : syracuseStep 6617983 = 9926975) B9926975
theorem B1547935 : Blo 1547471 1547935 := bstep (se 1 (by rfl) ⟨1160951, by rfl⟩ : syracuseStep 1547935 = 2321903) B2321903
theorem B4710377 : Blo 1547471 4710377 := bstep (se 2 (by rfl) ⟨1766391, by rfl⟩ : syracuseStep 4710377 = 3532783) B3532783
theorem B9421535 : Blo 1547471 9421535 := bstep (se 1 (by rfl) ⟨7066151, by rfl⟩ : syracuseStep 9421535 = 14132303) B14132303
theorem B8823977 : Blo 1547471 8823977 := bstep (se 2 (by rfl) ⟨3308991, by rfl⟩ : syracuseStep 8823977 = 6617983) B6617983
theorem B20112623 : Blo 1547471 20112623 := bstep (se 1 (by rfl) ⟨15084467, by rfl⟩ : syracuseStep 20112623 = 30168935) B30168935
theorem B26822087 : Blo 1547471 26822087 := bstep (se 1 (by rfl) ⟨20116565, by rfl⟩ : syracuseStep 26822087 = 40233131) B40233131
theorem B33474221 : Blo 1547471 33474221 := bstep (se 3 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 33474221 = 12552833) B12552833
theorem B4409471 : Blo 1547471 4409471 := bstep (se 1 (by rfl) ⟨3307103, by rfl⟩ : syracuseStep 4409471 = 6614207) B6614207
theorem B3140251 : Blo 1547471 3140251 := bstep (se 1 (by rfl) ⟨2355188, by rfl⟩ : syracuseStep 3140251 = 4710377) B4710377
theorem B2321705 : Blo 1547471 2321705 := bstep (se 2 (by rfl) ⟨870639, by rfl⟩ : syracuseStep 2321705 = 1741279) B1741279
theorem B3485339 : Blo 1547471 3485339 := bstep (se 1 (by rfl) ⟨2614004, by rfl⟩ : syracuseStep 3485339 = 5228009) B5228009
theorem B3485537 : Blo 1547471 3485537 := bstep (se 2 (by rfl) ⟨1307076, by rfl⟩ : syracuseStep 3485537 = 2614153) B2614153
theorem B137588885 : Blo 1547471 137588885 := bstep (se 6 (by rfl) ⟨3224739, by rfl⟩ : syracuseStep 137588885 = 6449479) B6449479
theorem B3485879 : Blo 1547471 3485879 := bstep (se 1 (by rfl) ⟨2614409, by rfl⟩ : syracuseStep 3485879 = 5228819) B5228819
theorem B26449577 : Blo 1547471 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B8820809 : Blo 1547471 8820809 := bstep (se 2 (by rfl) ⟨3307803, by rfl⟩ : syracuseStep 8820809 = 6615607) B6615607
theorem B4184399 : Blo 1547471 4184399 := bstep (se 1 (by rfl) ⟨3138299, by rfl⟩ : syracuseStep 4184399 = 6276599) B6276599
theorem B75356675 : Blo 1547471 75356675 := bstep (se 1 (by rfl) ⟨56517506, by rfl⟩ : syracuseStep 75356675 = 113035013) B113035013
theorem B20397023 : Blo 1547471 20397023 := bstep (se 1 (by rfl) ⟨15297767, by rfl⟩ : syracuseStep 20397023 = 30595535) B30595535
theorem B5225471 : Blo 1547471 5225471 := bstep (se 1 (by rfl) ⟨3919103, by rfl⟩ : syracuseStep 5225471 = 7838207) B7838207
theorem B35814575 : Blo 1547471 35814575 := bstep (se 1 (by rfl) ⟨26860931, by rfl⟩ : syracuseStep 35814575 = 53721863) B53721863
theorem B1548059 : Blo 1547471 1548059 := bstep (se 1 (by rfl) ⟨1161044, by rfl⟩ : syracuseStep 1548059 = 2322089) B2322089
theorem B91725923 : Blo 1547471 91725923 := bstep (se 1 (by rfl) ⟨68794442, by rfl⟩ : syracuseStep 91725923 = 137588885) B137588885
theorem B5882651 : Blo 1547471 5882651 := bstep (se 1 (by rfl) ⟨4411988, by rfl⟩ : syracuseStep 5882651 = 8823977) B8823977
theorem B22316147 : Blo 1547471 22316147 := bstep (se 1 (by rfl) ⟨16737110, by rfl⟩ : syracuseStep 22316147 = 33474221) B33474221
theorem B3483647 : Blo 1547471 3483647 := bstep (se 1 (by rfl) ⟨2612735, by rfl⟩ : syracuseStep 3483647 = 5225471) B5225471
theorem B16748005 : Blo 1547471 16748005 := bstep (se 4 (by rfl) ⟨1570125, by rfl⟩ : syracuseStep 16748005 = 3140251) B3140251
theorem B17633051 : Blo 1547471 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B2789599 : Blo 1547471 2789599 := bstep (se 1 (by rfl) ⟨2092199, by rfl⟩ : syracuseStep 2789599 = 4184399) B4184399
theorem B50237783 : Blo 1547471 50237783 := bstep (se 1 (by rfl) ⟨37678337, by rfl⟩ : syracuseStep 50237783 = 75356675) B75356675
theorem B23876383 : Blo 1547471 23876383 := bstep (se 1 (by rfl) ⟨17907287, by rfl⟩ : syracuseStep 23876383 = 35814575) B35814575
theorem B2323559 : Blo 1547471 2323559 := bstep (se 1 (by rfl) ⟨1742669, by rfl⟩ : syracuseStep 2323559 = 3485339) B3485339
theorem B2323691 : Blo 1547471 2323691 := bstep (se 1 (by rfl) ⟨1742768, by rfl⟩ : syracuseStep 2323691 = 3485537) B3485537
theorem B2323919 : Blo 1547471 2323919 := bstep (se 1 (by rfl) ⟨1742939, by rfl⟩ : syracuseStep 2323919 = 3485879) B3485879
theorem B6281023 : Blo 1547471 6281023 := bstep (se 1 (by rfl) ⟨4710767, by rfl⟩ : syracuseStep 6281023 = 9421535) B9421535
theorem B13408415 : Blo 1547471 13408415 := bstep (se 1 (by rfl) ⟨10056311, by rfl⟩ : syracuseStep 13408415 = 20112623) B20112623
theorem B17881391 : Blo 1547471 17881391 := bstep (se 1 (by rfl) ⟨13411043, by rfl⟩ : syracuseStep 17881391 = 26822087) B26822087
theorem B5880539 : Blo 1547471 5880539 := bstep (se 1 (by rfl) ⟨4410404, by rfl⟩ : syracuseStep 5880539 = 8820809) B8820809
theorem B2939647 : Blo 1547471 2939647 := bstep (se 1 (by rfl) ⟨2204735, by rfl⟩ : syracuseStep 2939647 = 4409471) B4409471
theorem B13598015 : Blo 1547471 13598015 := bstep (se 1 (by rfl) ⟨10198511, by rfl⟩ : syracuseStep 13598015 = 20397023) B20397023
theorem B1547803 : Blo 1547471 1547803 := bstep (se 1 (by rfl) ⟨1160852, by rfl⟩ : syracuseStep 1547803 = 2321705) B2321705
theorem B3719465 : Blo 1547471 3719465 := bstep (se 2 (by rfl) ⟨1394799, by rfl⟩ : syracuseStep 3719465 = 2789599) B2789599
theorem B1549039 : Blo 1547471 1549039 := bstep (se 1 (by rfl) ⟨1161779, by rfl⟩ : syracuseStep 1549039 = 2323559) B2323559
theorem B14877431 : Blo 1547471 14877431 := bstep (se 1 (by rfl) ⟨11158073, by rfl⟩ : syracuseStep 14877431 = 22316147) B22316147
theorem B1549127 : Blo 1547471 1549127 := bstep (se 1 (by rfl) ⟨1161845, by rfl⟩ : syracuseStep 1549127 = 2323691) B2323691
theorem B1549279 : Blo 1547471 1549279 := bstep (se 1 (by rfl) ⟨1161959, by rfl⟩ : syracuseStep 1549279 = 2323919) B2323919
theorem B31835177 : Blo 1547471 31835177 := bstep (se 2 (by rfl) ⟨11938191, by rfl⟩ : syracuseStep 31835177 = 23876383) B23876383
theorem B8938943 : Blo 1547471 8938943 := bstep (se 1 (by rfl) ⟨6704207, by rfl⟩ : syracuseStep 8938943 = 13408415) B13408415
theorem B11920927 : Blo 1547471 11920927 := bstep (se 1 (by rfl) ⟨8940695, by rfl⟩ : syracuseStep 11920927 = 17881391) B17881391
theorem B8374697 : Blo 1547471 8374697 := bstep (se 2 (by rfl) ⟨3140511, by rfl⟩ : syracuseStep 8374697 = 6281023) B6281023
theorem B33491855 : Blo 1547471 33491855 := bstep (se 1 (by rfl) ⟨25118891, by rfl⟩ : syracuseStep 33491855 = 50237783) B50237783
theorem B36261373 : Blo 1547471 36261373 := bstep (se 3 (by rfl) ⟨6799007, by rfl⟩ : syracuseStep 36261373 = 13598015) B13598015
theorem B3919529 : Blo 1547471 3919529 := bstep (se 2 (by rfl) ⟨1469823, by rfl⟩ : syracuseStep 3919529 = 2939647) B2939647
theorem B2322431 : Blo 1547471 2322431 := bstep (se 1 (by rfl) ⟨1741823, by rfl⟩ : syracuseStep 2322431 = 3483647) B3483647
theorem B3920359 : Blo 1547471 3920359 := bstep (se 1 (by rfl) ⟨2940269, by rfl⟩ : syracuseStep 3920359 = 5880539) B5880539
theorem B244602461 : Blo 1547471 244602461 := bstep (se 3 (by rfl) ⟨45862961, by rfl⟩ : syracuseStep 244602461 = 91725923) B91725923
theorem B3921767 : Blo 1547471 3921767 := bstep (se 1 (by rfl) ⟨2941325, by rfl⟩ : syracuseStep 3921767 = 5882651) B5882651
theorem B22330673 : Blo 1547471 22330673 := bstep (se 2 (by rfl) ⟨8374002, by rfl⟩ : syracuseStep 22330673 = 16748005) B16748005
theorem B11755367 : Blo 1547471 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B5227145 : Blo 1547471 5227145 := bstep (se 2 (by rfl) ⟨1960179, by rfl⟩ : syracuseStep 5227145 = 3920359) B3920359
theorem B2614511 : Blo 1547471 2614511 := bstep (se 1 (by rfl) ⟨1960883, by rfl⟩ : syracuseStep 2614511 = 3921767) B3921767
theorem B652273229 : Blo 1547471 652273229 := bstep (se 3 (by rfl) ⟨122301230, by rfl⟩ : syracuseStep 652273229 = 244602461) B244602461
theorem B15894569 : Blo 1547471 15894569 := bstep (se 2 (by rfl) ⟨5960463, by rfl⟩ : syracuseStep 15894569 = 11920927) B11920927
theorem B14887115 : Blo 1547471 14887115 := bstep (se 1 (by rfl) ⟨11165336, by rfl⟩ : syracuseStep 14887115 = 22330673) B22330673
theorem B5959295 : Blo 1547471 5959295 := bstep (se 1 (by rfl) ⟨4469471, by rfl⟩ : syracuseStep 5959295 = 8938943) B8938943
theorem B5583131 : Blo 1547471 5583131 := bstep (se 1 (by rfl) ⟨4187348, by rfl⟩ : syracuseStep 5583131 = 8374697) B8374697
theorem B22327903 : Blo 1547471 22327903 := bstep (se 1 (by rfl) ⟨16745927, by rfl⟩ : syracuseStep 22327903 = 33491855) B33491855
theorem B7836911 : Blo 1547471 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B2479643 : Blo 1547471 2479643 := bstep (se 1 (by rfl) ⟨1859732, by rfl⟩ : syracuseStep 2479643 = 3719465) B3719465
theorem B9918287 : Blo 1547471 9918287 := bstep (se 1 (by rfl) ⟨7438715, by rfl⟩ : syracuseStep 9918287 = 14877431) B14877431
theorem B21223451 : Blo 1547471 21223451 := bstep (se 1 (by rfl) ⟨15917588, by rfl⟩ : syracuseStep 21223451 = 31835177) B31835177
theorem B48348497 : Blo 1547471 48348497 := bstep (se 2 (by rfl) ⟨18130686, by rfl⟩ : syracuseStep 48348497 = 36261373) B36261373
theorem B2613019 : Blo 1547471 2613019 := bstep (se 1 (by rfl) ⟨1959764, by rfl⟩ : syracuseStep 2613019 = 3919529) B3919529
theorem B1548287 : Blo 1547471 1548287 := bstep (se 1 (by rfl) ⟨1161215, by rfl⟩ : syracuseStep 1548287 = 2322431) B2322431
theorem B42385517 : Blo 1547471 42385517 := bstep (se 3 (by rfl) ⟨7947284, by rfl⟩ : syracuseStep 42385517 = 15894569) B15894569
theorem B29770537 : Blo 1547471 29770537 := bstep (se 2 (by rfl) ⟨11163951, by rfl⟩ : syracuseStep 29770537 = 22327903) B22327903
theorem B434848819 : Blo 1547471 434848819 := bstep (se 1 (by rfl) ⟨326136614, by rfl⟩ : syracuseStep 434848819 = 652273229) B652273229
theorem B6612191 : Blo 1547471 6612191 := bstep (se 1 (by rfl) ⟨4959143, by rfl⟩ : syracuseStep 6612191 = 9918287) B9918287
theorem B14148967 : Blo 1547471 14148967 := bstep (se 1 (by rfl) ⟨10611725, by rfl⟩ : syracuseStep 14148967 = 21223451) B21223451
theorem B3484025 : Blo 1547471 3484025 := bstep (se 2 (by rfl) ⟨1306509, by rfl⟩ : syracuseStep 3484025 = 2613019) B2613019
theorem B3722087 : Blo 1547471 3722087 := bstep (se 1 (by rfl) ⟨2791565, by rfl⟩ : syracuseStep 3722087 = 5583131) B5583131
theorem B3484763 : Blo 1547471 3484763 := bstep (se 1 (by rfl) ⟨2613572, by rfl⟩ : syracuseStep 3484763 = 5227145) B5227145
theorem B9924743 : Blo 1547471 9924743 := bstep (se 1 (by rfl) ⟨7443557, by rfl⟩ : syracuseStep 9924743 = 14887115) B14887115
theorem B32232331 : Blo 1547471 32232331 := bstep (se 1 (by rfl) ⟨24174248, by rfl⟩ : syracuseStep 32232331 = 48348497) B48348497
theorem B5224607 : Blo 1547471 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B1743007 : Blo 1547471 1743007 := bstep (se 1 (by rfl) ⟨1307255, by rfl⟩ : syracuseStep 1743007 = 2614511) B2614511
theorem B1653095 : Blo 1547471 1653095 := bstep (se 1 (by rfl) ⟨1239821, by rfl⟩ : syracuseStep 1653095 = 2479643) B2479643
theorem B3972863 : Blo 1547471 3972863 := bstep (se 1 (by rfl) ⟨2979647, by rfl⟩ : syracuseStep 3972863 = 5959295) B5959295
theorem B4408127 : Blo 1547471 4408127 := bstep (se 1 (by rfl) ⟨3306095, by rfl⟩ : syracuseStep 4408127 = 6612191) B6612191
theorem B4408253 : Blo 1547471 4408253 := bstep (se 3 (by rfl) ⟨826547, by rfl⟩ : syracuseStep 4408253 = 1653095) B1653095
theorem B42976441 : Blo 1547471 42976441 := bstep (se 2 (by rfl) ⟨16116165, by rfl⟩ : syracuseStep 42976441 = 32232331) B32232331
theorem B579798425 : Blo 1547471 579798425 := bstep (se 2 (by rfl) ⟨217424409, by rfl⟩ : syracuseStep 579798425 = 434848819) B434848819
theorem B3483071 : Blo 1547471 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B2648575 : Blo 1547471 2648575 := bstep (se 1 (by rfl) ⟨1986431, by rfl⟩ : syracuseStep 2648575 = 3972863) B3972863
theorem B28257011 : Blo 1547471 28257011 := bstep (se 1 (by rfl) ⟨21192758, by rfl⟩ : syracuseStep 28257011 = 42385517) B42385517
theorem B39694049 : Blo 1547471 39694049 := bstep (se 2 (by rfl) ⟨14885268, by rfl⟩ : syracuseStep 39694049 = 29770537) B29770537
theorem B2322683 : Blo 1547471 2322683 := bstep (se 1 (by rfl) ⟨1742012, by rfl⟩ : syracuseStep 2322683 = 3484025) B3484025
theorem B2323175 : Blo 1547471 2323175 := bstep (se 1 (by rfl) ⟨1742381, by rfl⟩ : syracuseStep 2323175 = 3484763) B3484763
theorem B6616495 : Blo 1547471 6616495 := bstep (se 1 (by rfl) ⟨4962371, by rfl⟩ : syracuseStep 6616495 = 9924743) B9924743
theorem B2324009 : Blo 1547471 2324009 := bstep (se 2 (by rfl) ⟨871503, by rfl⟩ : syracuseStep 2324009 = 1743007) B1743007
theorem B18865289 : Blo 1547471 18865289 := bstep (se 2 (by rfl) ⟨7074483, by rfl⟩ : syracuseStep 18865289 = 14148967) B14148967
theorem B2481391 : Blo 1547471 2481391 := bstep (se 1 (by rfl) ⟨1861043, by rfl⟩ : syracuseStep 2481391 = 3722087) B3722087
theorem B1548455 : Blo 1547471 1548455 := bstep (se 1 (by rfl) ⟨1161341, by rfl⟩ : syracuseStep 1548455 = 2322683) B2322683
theorem B50307437 : Blo 1547471 50307437 := bstep (se 3 (by rfl) ⟨9432644, by rfl⟩ : syracuseStep 50307437 = 18865289) B18865289
theorem B1548783 : Blo 1547471 1548783 := bstep (se 1 (by rfl) ⟨1161587, by rfl⟩ : syracuseStep 1548783 = 2323175) B2323175
theorem B3531433 : Blo 1547471 3531433 := bstep (se 2 (by rfl) ⟨1324287, by rfl⟩ : syracuseStep 3531433 = 2648575) B2648575
theorem B386532283 : Blo 1547471 386532283 := bstep (se 1 (by rfl) ⟨289899212, by rfl⟩ : syracuseStep 386532283 = 579798425) B579798425
theorem B1549339 : Blo 1547471 1549339 := bstep (se 1 (by rfl) ⟨1162004, by rfl⟩ : syracuseStep 1549339 = 2324009) B2324009
theorem B26462699 : Blo 1547471 26462699 := bstep (se 1 (by rfl) ⟨19847024, by rfl⟩ : syracuseStep 26462699 = 39694049) B39694049
theorem B2322047 : Blo 1547471 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B18838007 : Blo 1547471 18838007 := bstep (se 1 (by rfl) ⟨14128505, by rfl⟩ : syracuseStep 18838007 = 28257011) B28257011
theorem B2938751 : Blo 1547471 2938751 := bstep (se 1 (by rfl) ⟨2204063, by rfl⟩ : syracuseStep 2938751 = 4408127) B4408127
theorem B2938835 : Blo 1547471 2938835 := bstep (se 1 (by rfl) ⟨2204126, by rfl⟩ : syracuseStep 2938835 = 4408253) B4408253
theorem B57301921 : Blo 1547471 57301921 := bstep (se 2 (by rfl) ⟨21488220, by rfl⟩ : syracuseStep 57301921 = 42976441) B42976441
theorem B3308521 : Blo 1547471 3308521 := bstep (se 2 (by rfl) ⟨1240695, by rfl⟩ : syracuseStep 3308521 = 2481391) B2481391
theorem B8821993 : Blo 1547471 8821993 := bstep (se 2 (by rfl) ⟨3308247, by rfl⟩ : syracuseStep 8821993 = 6616495) B6616495
theorem B12558671 : Blo 1547471 12558671 := bstep (se 1 (by rfl) ⟨9419003, by rfl⟩ : syracuseStep 12558671 = 18838007) B18838007
theorem B134153165 : Blo 1547471 134153165 := bstep (se 3 (by rfl) ⟨25153718, by rfl⟩ : syracuseStep 134153165 = 50307437) B50307437
theorem B515376377 : Blo 1547471 515376377 := bstep (se 2 (by rfl) ⟨193266141, by rfl⟩ : syracuseStep 515376377 = 386532283) B386532283
theorem B1959167 : Blo 1547471 1959167 := bstep (se 1 (by rfl) ⟨1469375, by rfl⟩ : syracuseStep 1959167 = 2938751) B2938751
theorem B1959223 : Blo 1547471 1959223 := bstep (se 1 (by rfl) ⟨1469417, by rfl⟩ : syracuseStep 1959223 = 2938835) B2938835
theorem B76402561 : Blo 1547471 76402561 := bstep (se 2 (by rfl) ⟨28650960, by rfl⟩ : syracuseStep 76402561 = 57301921) B57301921
theorem B4411361 : Blo 1547471 4411361 := bstep (se 2 (by rfl) ⟨1654260, by rfl⟩ : syracuseStep 4411361 = 3308521) B3308521
theorem B17641799 : Blo 1547471 17641799 := bstep (se 1 (by rfl) ⟨13231349, by rfl⟩ : syracuseStep 17641799 = 26462699) B26462699
theorem B4708577 : Blo 1547471 4708577 := bstep (se 2 (by rfl) ⟨1765716, by rfl⟩ : syracuseStep 4708577 = 3531433) B3531433
theorem B11762657 : Blo 1547471 11762657 := bstep (se 2 (by rfl) ⟨4410996, by rfl⟩ : syracuseStep 11762657 = 8821993) B8821993
theorem B1548031 : Blo 1547471 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B8372447 : Blo 1547471 8372447 := bstep (se 1 (by rfl) ⟨6279335, by rfl⟩ : syracuseStep 8372447 = 12558671) B12558671
theorem B7841771 : Blo 1547471 7841771 := bstep (se 1 (by rfl) ⟨5881328, by rfl⟩ : syracuseStep 7841771 = 11762657) B11762657
theorem B101870081 : Blo 1547471 101870081 := bstep (se 2 (by rfl) ⟨38201280, by rfl⟩ : syracuseStep 101870081 = 76402561) B76402561
theorem B89435443 : Blo 1547471 89435443 := bstep (se 1 (by rfl) ⟨67076582, by rfl⟩ : syracuseStep 89435443 = 134153165) B134153165
theorem B343584251 : Blo 1547471 343584251 := bstep (se 1 (by rfl) ⟨257688188, by rfl⟩ : syracuseStep 343584251 = 515376377) B515376377
theorem B11761199 : Blo 1547471 11761199 := bstep (se 1 (by rfl) ⟨8820899, by rfl⟩ : syracuseStep 11761199 = 17641799) B17641799
theorem B12556205 : Blo 1547471 12556205 := bstep (se 3 (by rfl) ⟨2354288, by rfl⟩ : syracuseStep 12556205 = 4708577) B4708577
theorem B5224445 : Blo 1547471 5224445 := bstep (se 3 (by rfl) ⟨979583, by rfl⟩ : syracuseStep 5224445 = 1959167) B1959167
theorem B2612297 : Blo 1547471 2612297 := bstep (se 2 (by rfl) ⟨979611, by rfl⟩ : syracuseStep 2612297 = 1959223) B1959223
theorem B11763629 : Blo 1547471 11763629 := bstep (se 3 (by rfl) ⟨2205680, by rfl⟩ : syracuseStep 11763629 = 4411361) B4411361
theorem B7840799 : Blo 1547471 7840799 := bstep (se 1 (by rfl) ⟨5880599, by rfl⟩ : syracuseStep 7840799 = 11761199) B11761199
theorem B5227847 : Blo 1547471 5227847 := bstep (se 1 (by rfl) ⟨3920885, by rfl⟩ : syracuseStep 5227847 = 7841771) B7841771
theorem B3482963 : Blo 1547471 3482963 := bstep (se 1 (by rfl) ⟨2612222, by rfl⟩ : syracuseStep 3482963 = 5224445) B5224445
theorem B67913387 : Blo 1547471 67913387 := bstep (se 1 (by rfl) ⟨50935040, by rfl⟩ : syracuseStep 67913387 = 101870081) B101870081
theorem B7842419 : Blo 1547471 7842419 := bstep (se 1 (by rfl) ⟨5881814, by rfl⟩ : syracuseStep 7842419 = 11763629) B11763629
theorem B5581631 : Blo 1547471 5581631 := bstep (se 1 (by rfl) ⟨4186223, by rfl⟩ : syracuseStep 5581631 = 8372447) B8372447
theorem B119247257 : Blo 1547471 119247257 := bstep (se 2 (by rfl) ⟨44717721, by rfl⟩ : syracuseStep 119247257 = 89435443) B89435443
theorem B1741531 : Blo 1547471 1741531 := bstep (se 1 (by rfl) ⟨1306148, by rfl⟩ : syracuseStep 1741531 = 2612297) B2612297
theorem B8370803 : Blo 1547471 8370803 := bstep (se 1 (by rfl) ⟨6278102, by rfl⟩ : syracuseStep 8370803 = 12556205) B12556205
theorem B229056167 : Blo 1547471 229056167 := bstep (se 1 (by rfl) ⟨171792125, by rfl⟩ : syracuseStep 229056167 = 343584251) B343584251
theorem B5227199 : Blo 1547471 5227199 := bstep (se 1 (by rfl) ⟨3920399, by rfl⟩ : syracuseStep 5227199 = 7840799) B7840799
theorem B5228279 : Blo 1547471 5228279 := bstep (se 1 (by rfl) ⟨3921209, by rfl⟩ : syracuseStep 5228279 = 7842419) B7842419
theorem B3721087 : Blo 1547471 3721087 := bstep (se 1 (by rfl) ⟨2790815, by rfl⟩ : syracuseStep 3721087 = 5581631) B5581631
theorem B79498171 : Blo 1547471 79498171 := bstep (se 1 (by rfl) ⟨59623628, by rfl⟩ : syracuseStep 79498171 = 119247257) B119247257
theorem B3485231 : Blo 1547471 3485231 := bstep (se 1 (by rfl) ⟨2613923, by rfl⟩ : syracuseStep 3485231 = 5227847) B5227847
theorem B2321975 : Blo 1547471 2321975 := bstep (se 1 (by rfl) ⟨1741481, by rfl⟩ : syracuseStep 2321975 = 3482963) B3482963
theorem B2322041 : Blo 1547471 2322041 := bstep (se 2 (by rfl) ⟨870765, by rfl⟩ : syracuseStep 2322041 = 1741531) B1741531
theorem B152704111 : Blo 1547471 152704111 := bstep (se 1 (by rfl) ⟨114528083, by rfl⟩ : syracuseStep 152704111 = 229056167) B229056167
theorem B45275591 : Blo 1547471 45275591 := bstep (se 1 (by rfl) ⟨33956693, by rfl⟩ : syracuseStep 45275591 = 67913387) B67913387
theorem B22322141 : Blo 1547471 22322141 := bstep (se 3 (by rfl) ⟨4185401, by rfl⟩ : syracuseStep 22322141 = 8370803) B8370803
theorem B105997561 : Blo 1547471 105997561 := bstep (se 2 (by rfl) ⟨39749085, by rfl⟩ : syracuseStep 105997561 = 79498171) B79498171
theorem B203605481 : Blo 1547471 203605481 := bstep (se 2 (by rfl) ⟨76352055, by rfl⟩ : syracuseStep 203605481 = 152704111) B152704111
theorem B3484799 : Blo 1547471 3484799 := bstep (se 1 (by rfl) ⟨2613599, by rfl⟩ : syracuseStep 3484799 = 5227199) B5227199
theorem B3485519 : Blo 1547471 3485519 := bstep (se 1 (by rfl) ⟨2614139, by rfl⟩ : syracuseStep 3485519 = 5228279) B5228279
theorem B30183727 : Blo 1547471 30183727 := bstep (se 1 (by rfl) ⟨22637795, by rfl⟩ : syracuseStep 30183727 = 45275591) B45275591
theorem B14881427 : Blo 1547471 14881427 := bstep (se 1 (by rfl) ⟨11161070, by rfl⟩ : syracuseStep 14881427 = 22322141) B22322141
theorem B2323487 : Blo 1547471 2323487 := bstep (se 1 (by rfl) ⟨1742615, by rfl⟩ : syracuseStep 2323487 = 3485231) B3485231
theorem B4961449 : Blo 1547471 4961449 := bstep (se 2 (by rfl) ⟨1860543, by rfl⟩ : syracuseStep 4961449 = 3721087) B3721087
theorem B1547983 : Blo 1547471 1547983 := bstep (se 1 (by rfl) ⟨1160987, by rfl⟩ : syracuseStep 1547983 = 2321975) B2321975
theorem B1548027 : Blo 1547471 1548027 := bstep (se 1 (by rfl) ⟨1161020, by rfl⟩ : syracuseStep 1548027 = 2322041) B2322041
theorem B9920951 : Blo 1547471 9920951 := bstep (se 1 (by rfl) ⟨7440713, by rfl⟩ : syracuseStep 9920951 = 14881427) B14881427
theorem B1548991 : Blo 1547471 1548991 := bstep (se 1 (by rfl) ⟨1161743, by rfl⟩ : syracuseStep 1548991 = 2323487) B2323487
theorem B135736987 : Blo 1547471 135736987 := bstep (se 1 (by rfl) ⟨101802740, by rfl⟩ : syracuseStep 135736987 = 203605481) B203605481
theorem B6615265 : Blo 1547471 6615265 := bstep (se 2 (by rfl) ⟨2480724, by rfl⟩ : syracuseStep 6615265 = 4961449) B4961449
theorem B2323199 : Blo 1547471 2323199 := bstep (se 1 (by rfl) ⟨1742399, by rfl⟩ : syracuseStep 2323199 = 3484799) B3484799
theorem B2323679 : Blo 1547471 2323679 := bstep (se 1 (by rfl) ⟨1742759, by rfl⟩ : syracuseStep 2323679 = 3485519) B3485519
theorem B40244969 : Blo 1547471 40244969 := bstep (se 2 (by rfl) ⟨15091863, by rfl⟩ : syracuseStep 40244969 = 30183727) B30183727
theorem B565320325 : Blo 1547471 565320325 := bstep (se 4 (by rfl) ⟨52998780, by rfl⟩ : syracuseStep 565320325 = 105997561) B105997561
theorem B1548799 : Blo 1547471 1548799 := bstep (se 1 (by rfl) ⟨1161599, by rfl⟩ : syracuseStep 1548799 = 2323199) B2323199
theorem B1549119 : Blo 1547471 1549119 := bstep (se 1 (by rfl) ⟨1161839, by rfl⟩ : syracuseStep 1549119 = 2323679) B2323679
theorem B6613967 : Blo 1547471 6613967 := bstep (se 1 (by rfl) ⟨4960475, by rfl⟩ : syracuseStep 6613967 = 9920951) B9920951
theorem B107319917 : Blo 1547471 107319917 := bstep (se 3 (by rfl) ⟨20122484, by rfl⟩ : syracuseStep 107319917 = 40244969) B40244969
theorem B180982649 : Blo 1547471 180982649 := bstep (se 2 (by rfl) ⟨67868493, by rfl⟩ : syracuseStep 180982649 = 135736987) B135736987
theorem B8820353 : Blo 1547471 8820353 := bstep (se 2 (by rfl) ⟨3307632, by rfl⟩ : syracuseStep 8820353 = 6615265) B6615265
theorem B753760433 : Blo 1547471 753760433 := bstep (se 2 (by rfl) ⟨282660162, by rfl⟩ : syracuseStep 753760433 = 565320325) B565320325
theorem B502506955 : Blo 1547471 502506955 := bstep (se 1 (by rfl) ⟨376880216, by rfl⟩ : syracuseStep 502506955 = 753760433) B753760433
theorem B4409311 : Blo 1547471 4409311 := bstep (se 1 (by rfl) ⟨3306983, by rfl⟩ : syracuseStep 4409311 = 6613967) B6613967
theorem B120655099 : Blo 1547471 120655099 := bstep (se 1 (by rfl) ⟨90491324, by rfl⟩ : syracuseStep 120655099 = 180982649) B180982649
theorem B5880235 : Blo 1547471 5880235 := bstep (se 1 (by rfl) ⟨4410176, by rfl⟩ : syracuseStep 5880235 = 8820353) B8820353
theorem B286186445 : Blo 1547471 286186445 := bstep (se 3 (by rfl) ⟨53659958, by rfl⟩ : syracuseStep 286186445 = 107319917) B107319917
theorem B7840313 : Blo 1547471 7840313 := bstep (se 2 (by rfl) ⟨2940117, by rfl⟩ : syracuseStep 7840313 = 5880235) B5880235
theorem B5879081 : Blo 1547471 5879081 := bstep (se 2 (by rfl) ⟨2204655, by rfl⟩ : syracuseStep 5879081 = 4409311) B4409311
theorem B160873465 : Blo 1547471 160873465 := bstep (se 2 (by rfl) ⟨60327549, by rfl⟩ : syracuseStep 160873465 = 120655099) B120655099
theorem B190790963 : Blo 1547471 190790963 := bstep (se 1 (by rfl) ⟨143093222, by rfl⟩ : syracuseStep 190790963 = 286186445) B286186445
theorem B2680037093 : Blo 1547471 2680037093 := bstep (se 4 (by rfl) ⟨251253477, by rfl⟩ : syracuseStep 2680037093 = 502506955) B502506955
theorem B5226875 : Blo 1547471 5226875 := bstep (se 1 (by rfl) ⟨3920156, by rfl⟩ : syracuseStep 5226875 = 7840313) B7840313
theorem B3919387 : Blo 1547471 3919387 := bstep (se 1 (by rfl) ⟨2939540, by rfl⟩ : syracuseStep 3919387 = 5879081) B5879081
theorem B127193975 : Blo 1547471 127193975 := bstep (se 1 (by rfl) ⟨95395481, by rfl⟩ : syracuseStep 127193975 = 190790963) B190790963
theorem B214497953 : Blo 1547471 214497953 := bstep (se 2 (by rfl) ⟨80436732, by rfl⟩ : syracuseStep 214497953 = 160873465) B160873465
theorem B1786691395 : Blo 1547471 1786691395 := bstep (se 1 (by rfl) ⟨1340018546, by rfl⟩ : syracuseStep 1786691395 = 2680037093) B2680037093
theorem B84795983 : Blo 1547471 84795983 := bstep (se 1 (by rfl) ⟨63596987, by rfl⟩ : syracuseStep 84795983 = 127193975) B127193975
theorem B3484583 : Blo 1547471 3484583 := bstep (se 1 (by rfl) ⟨2613437, by rfl⟩ : syracuseStep 3484583 = 5226875) B5226875
theorem B2382255193 : Blo 1547471 2382255193 := bstep (se 2 (by rfl) ⟨893345697, by rfl⟩ : syracuseStep 2382255193 = 1786691395) B1786691395
theorem B142998635 : Blo 1547471 142998635 := bstep (se 1 (by rfl) ⟨107248976, by rfl⟩ : syracuseStep 142998635 = 214497953) B214497953
theorem B5225849 : Blo 1547471 5225849 := bstep (se 2 (by rfl) ⟨1959693, by rfl⟩ : syracuseStep 5225849 = 3919387) B3919387
theorem B95332423 : Blo 1547471 95332423 := bstep (se 1 (by rfl) ⟨71499317, by rfl⟩ : syracuseStep 95332423 = 142998635) B142998635
theorem B3483899 : Blo 1547471 3483899 := bstep (se 1 (by rfl) ⟨2612924, by rfl⟩ : syracuseStep 3483899 = 5225849) B5225849
theorem B2323055 : Blo 1547471 2323055 := bstep (se 1 (by rfl) ⟨1742291, by rfl⟩ : syracuseStep 2323055 = 3484583) B3484583
theorem B56530655 : Blo 1547471 56530655 := bstep (se 1 (by rfl) ⟨42397991, by rfl⟩ : syracuseStep 56530655 = 84795983) B84795983
theorem B3176340257 : Blo 1547471 3176340257 := bstep (se 2 (by rfl) ⟨1191127596, by rfl⟩ : syracuseStep 3176340257 = 2382255193) B2382255193
theorem B1548703 : Blo 1547471 1548703 := bstep (se 1 (by rfl) ⟨1161527, by rfl⟩ : syracuseStep 1548703 = 2323055) B2323055
theorem B2117560171 : Blo 1547471 2117560171 := bstep (se 1 (by rfl) ⟨1588170128, by rfl⟩ : syracuseStep 2117560171 = 3176340257) B3176340257
theorem B127109897 : Blo 1547471 127109897 := bstep (se 2 (by rfl) ⟨47666211, by rfl⟩ : syracuseStep 127109897 = 95332423) B95332423
theorem B37687103 : Blo 1547471 37687103 := bstep (se 1 (by rfl) ⟨28265327, by rfl⟩ : syracuseStep 37687103 = 56530655) B56530655
theorem B2322599 : Blo 1547471 2322599 := bstep (se 1 (by rfl) ⟨1741949, by rfl⟩ : syracuseStep 2322599 = 3483899) B3483899
theorem B1548399 : Blo 1547471 1548399 := bstep (se 1 (by rfl) ⟨1161299, by rfl⟩ : syracuseStep 1548399 = 2322599) B2322599
theorem B84739931 : Blo 1547471 84739931 := bstep (se 1 (by rfl) ⟨63554948, by rfl⟩ : syracuseStep 84739931 = 127109897) B127109897
theorem B2823413561 : Blo 1547471 2823413561 := bstep (se 2 (by rfl) ⟨1058780085, by rfl⟩ : syracuseStep 2823413561 = 2117560171) B2117560171
theorem B25124735 : Blo 1547471 25124735 := bstep (se 1 (by rfl) ⟨18843551, by rfl⟩ : syracuseStep 25124735 = 37687103) B37687103
theorem B56493287 : Blo 1547471 56493287 := bstep (se 1 (by rfl) ⟨42369965, by rfl⟩ : syracuseStep 56493287 = 84739931) B84739931
theorem B16749823 : Blo 1547471 16749823 := bstep (se 1 (by rfl) ⟨12562367, by rfl⟩ : syracuseStep 16749823 = 25124735) B25124735
theorem B1882275707 : Blo 1547471 1882275707 := bstep (se 1 (by rfl) ⟨1411706780, by rfl⟩ : syracuseStep 1882275707 = 2823413561) B2823413561
theorem B22333097 : Blo 1547471 22333097 := bstep (se 2 (by rfl) ⟨8374911, by rfl⟩ : syracuseStep 22333097 = 16749823) B16749823
theorem B37662191 : Blo 1547471 37662191 := bstep (se 1 (by rfl) ⟨28246643, by rfl⟩ : syracuseStep 37662191 = 56493287) B56493287
theorem B1254850471 : Blo 1547471 1254850471 := bstep (se 1 (by rfl) ⟨941137853, by rfl⟩ : syracuseStep 1254850471 = 1882275707) B1882275707
theorem B14888731 : Blo 1547471 14888731 := bstep (se 1 (by rfl) ⟨11166548, by rfl⟩ : syracuseStep 14888731 = 22333097) B22333097
theorem B6692535845 : Blo 1547471 6692535845 := bstep (se 4 (by rfl) ⟨627425235, by rfl⟩ : syracuseStep 6692535845 = 1254850471) B1254850471
theorem B25108127 : Blo 1547471 25108127 := bstep (se 1 (by rfl) ⟨18831095, by rfl⟩ : syracuseStep 25108127 = 37662191) B37662191
theorem B19851641 : Blo 1547471 19851641 := bstep (se 2 (by rfl) ⟨7444365, by rfl⟩ : syracuseStep 19851641 = 14888731) B14888731
theorem B16738751 : Blo 1547471 16738751 := bstep (se 1 (by rfl) ⟨12554063, by rfl⟩ : syracuseStep 16738751 = 25108127) B25108127
theorem B4461690563 : Blo 1547471 4461690563 := bstep (se 1 (by rfl) ⟨3346267922, by rfl⟩ : syracuseStep 4461690563 = 6692535845) B6692535845
theorem B2974460375 : Blo 1547471 2974460375 := bstep (se 1 (by rfl) ⟨2230845281, by rfl⟩ : syracuseStep 2974460375 = 4461690563) B4461690563
theorem B13234427 : Blo 1547471 13234427 := bstep (se 1 (by rfl) ⟨9925820, by rfl⟩ : syracuseStep 13234427 = 19851641) B19851641
theorem B44636669 : Blo 1547471 44636669 := bstep (se 3 (by rfl) ⟨8369375, by rfl⟩ : syracuseStep 44636669 = 16738751) B16738751
theorem B8822951 : Blo 1547471 8822951 := bstep (se 1 (by rfl) ⟨6617213, by rfl⟩ : syracuseStep 8822951 = 13234427) B13234427
theorem B1982973583 : Blo 1547471 1982973583 := bstep (se 1 (by rfl) ⟨1487230187, by rfl⟩ : syracuseStep 1982973583 = 2974460375) B2974460375
theorem B29757779 : Blo 1547471 29757779 := bstep (se 1 (by rfl) ⟨22318334, by rfl⟩ : syracuseStep 29757779 = 44636669) B44636669
theorem B5881967 : Blo 1547471 5881967 := bstep (se 1 (by rfl) ⟨4411475, by rfl⟩ : syracuseStep 5881967 = 8822951) B8822951
theorem B2643964777 : Blo 1547471 2643964777 := bstep (se 2 (by rfl) ⟨991486791, by rfl⟩ : syracuseStep 2643964777 = 1982973583) B1982973583
theorem B19838519 : Blo 1547471 19838519 := bstep (se 1 (by rfl) ⟨14878889, by rfl⟩ : syracuseStep 19838519 = 29757779) B29757779
theorem B13225679 : Blo 1547471 13225679 := bstep (se 1 (by rfl) ⟨9919259, by rfl⟩ : syracuseStep 13225679 = 19838519) B19838519
theorem B3921311 : Blo 1547471 3921311 := bstep (se 1 (by rfl) ⟨2940983, by rfl⟩ : syracuseStep 3921311 = 5881967) B5881967
theorem B3525286369 : Blo 1547471 3525286369 := bstep (se 2 (by rfl) ⟨1321982388, by rfl⟩ : syracuseStep 3525286369 = 2643964777) B2643964777
theorem B4700381825 : Blo 1547471 4700381825 := bstep (se 2 (by rfl) ⟨1762643184, by rfl⟩ : syracuseStep 4700381825 = 3525286369) B3525286369
theorem B2614207 : Blo 1547471 2614207 := bstep (se 1 (by rfl) ⟨1960655, by rfl⟩ : syracuseStep 2614207 = 3921311) B3921311
theorem B8817119 : Blo 1547471 8817119 := bstep (se 1 (by rfl) ⟨6612839, by rfl⟩ : syracuseStep 8817119 = 13225679) B13225679
theorem B3133587883 : Blo 1547471 3133587883 := bstep (se 1 (by rfl) ⟨2350190912, by rfl⟩ : syracuseStep 3133587883 = 4700381825) B4700381825
theorem B3485609 : Blo 1547471 3485609 := bstep (se 2 (by rfl) ⟨1307103, by rfl⟩ : syracuseStep 3485609 = 2614207) B2614207
theorem B5878079 : Blo 1547471 5878079 := bstep (se 1 (by rfl) ⟨4408559, by rfl⟩ : syracuseStep 5878079 = 8817119) B8817119
theorem B4178117177 : Blo 1547471 4178117177 := bstep (se 2 (by rfl) ⟨1566793941, by rfl⟩ : syracuseStep 4178117177 = 3133587883) B3133587883
theorem B3918719 : Blo 1547471 3918719 := bstep (se 1 (by rfl) ⟨2939039, by rfl⟩ : syracuseStep 3918719 = 5878079) B5878079
theorem B2323739 : Blo 1547471 2323739 := bstep (se 1 (by rfl) ⟨1742804, by rfl⟩ : syracuseStep 2323739 = 3485609) B3485609
theorem B2785411451 : Blo 1547471 2785411451 := bstep (se 1 (by rfl) ⟨2089058588, by rfl⟩ : syracuseStep 2785411451 = 4178117177) B4178117177
theorem B1549159 : Blo 1547471 1549159 := bstep (se 1 (by rfl) ⟨1161869, by rfl⟩ : syracuseStep 1549159 = 2323739) B2323739
theorem B2612479 : Blo 1547471 2612479 := bstep (se 1 (by rfl) ⟨1959359, by rfl⟩ : syracuseStep 2612479 = 3918719) B3918719
theorem B3483305 : Blo 1547471 3483305 := bstep (se 2 (by rfl) ⟨1306239, by rfl⟩ : syracuseStep 3483305 = 2612479) B2612479
theorem B1856940967 : Blo 1547471 1856940967 := bstep (se 1 (by rfl) ⟨1392705725, by rfl⟩ : syracuseStep 1856940967 = 2785411451) B2785411451
theorem B2322203 : Blo 1547471 2322203 := bstep (se 1 (by rfl) ⟨1741652, by rfl⟩ : syracuseStep 2322203 = 3483305) B3483305
theorem B2475921289 : Blo 1547471 2475921289 := bstep (se 2 (by rfl) ⟨928470483, by rfl⟩ : syracuseStep 2475921289 = 1856940967) B1856940967
theorem B3301228385 : Blo 1547471 3301228385 := bstep (se 2 (by rfl) ⟨1237960644, by rfl⟩ : syracuseStep 3301228385 = 2475921289) B2475921289
theorem B1548135 : Blo 1547471 1548135 := bstep (se 1 (by rfl) ⟨1161101, by rfl⟩ : syracuseStep 1548135 = 2322203) B2322203
theorem B2200818923 : Blo 1547471 2200818923 := bstep (se 1 (by rfl) ⟨1650614192, by rfl⟩ : syracuseStep 2200818923 = 3301228385) B3301228385
theorem B1467212615 : Blo 1547471 1467212615 := bstep (se 1 (by rfl) ⟨1100409461, by rfl⟩ : syracuseStep 1467212615 = 2200818923) B2200818923
theorem B978141743 : Blo 1547471 978141743 := bstep (se 1 (by rfl) ⟨733606307, by rfl⟩ : syracuseStep 978141743 = 1467212615) B1467212615
theorem B652094495 : Blo 1547471 652094495 := bstep (se 1 (by rfl) ⟨489070871, by rfl⟩ : syracuseStep 652094495 = 978141743) B978141743
theorem B434729663 : Blo 1547471 434729663 := bstep (se 1 (by rfl) ⟨326047247, by rfl⟩ : syracuseStep 434729663 = 652094495) B652094495
theorem B289819775 : Blo 1547471 289819775 := bstep (se 1 (by rfl) ⟨217364831, by rfl⟩ : syracuseStep 289819775 = 434729663) B434729663
theorem B193213183 : Blo 1547471 193213183 := bstep (se 1 (by rfl) ⟨144909887, by rfl⟩ : syracuseStep 193213183 = 289819775) B289819775
theorem B257617577 : Blo 1547471 257617577 := bstep (se 2 (by rfl) ⟨96606591, by rfl⟩ : syracuseStep 257617577 = 193213183) B193213183
theorem B171745051 : Blo 1547471 171745051 := bstep (se 1 (by rfl) ⟨128808788, by rfl⟩ : syracuseStep 171745051 = 257617577) B257617577
theorem B228993401 : Blo 1547471 228993401 := bstep (se 2 (by rfl) ⟨85872525, by rfl⟩ : syracuseStep 228993401 = 171745051) B171745051
theorem B152662267 : Blo 1547471 152662267 := bstep (se 1 (by rfl) ⟨114496700, by rfl⟩ : syracuseStep 152662267 = 228993401) B228993401
theorem B203549689 : Blo 1547471 203549689 := bstep (se 2 (by rfl) ⟨76331133, by rfl⟩ : syracuseStep 203549689 = 152662267) B152662267
theorem B271399585 : Blo 1547471 271399585 := bstep (se 2 (by rfl) ⟨101774844, by rfl⟩ : syracuseStep 271399585 = 203549689) B203549689
theorem B361866113 : Blo 1547471 361866113 := bstep (se 2 (by rfl) ⟨135699792, by rfl⟩ : syracuseStep 361866113 = 271399585) B271399585
theorem B241244075 : Blo 1547471 241244075 := bstep (se 1 (by rfl) ⟨180933056, by rfl⟩ : syracuseStep 241244075 = 361866113) B361866113
theorem B160829383 : Blo 1547471 160829383 := bstep (se 1 (by rfl) ⟨120622037, by rfl⟩ : syracuseStep 160829383 = 241244075) B241244075
theorem B214439177 : Blo 1547471 214439177 := bstep (se 2 (by rfl) ⟨80414691, by rfl⟩ : syracuseStep 214439177 = 160829383) B160829383
theorem B142959451 : Blo 1547471 142959451 := bstep (se 1 (by rfl) ⟨107219588, by rfl⟩ : syracuseStep 142959451 = 214439177) B214439177
theorem B190612601 : Blo 1547471 190612601 := bstep (se 2 (by rfl) ⟨71479725, by rfl⟩ : syracuseStep 190612601 = 142959451) B142959451
theorem B127075067 : Blo 1547471 127075067 := bstep (se 1 (by rfl) ⟨95306300, by rfl⟩ : syracuseStep 127075067 = 190612601) B190612601
theorem B84716711 : Blo 1547471 84716711 := bstep (se 1 (by rfl) ⟨63537533, by rfl⟩ : syracuseStep 84716711 = 127075067) B127075067
theorem B56477807 : Blo 1547471 56477807 := bstep (se 1 (by rfl) ⟨42358355, by rfl⟩ : syracuseStep 56477807 = 84716711) B84716711
theorem B37651871 : Blo 1547471 37651871 := bstep (se 1 (by rfl) ⟨28238903, by rfl⟩ : syracuseStep 37651871 = 56477807) B56477807
theorem B25101247 : Blo 1547471 25101247 := bstep (se 1 (by rfl) ⟨18825935, by rfl⟩ : syracuseStep 25101247 = 37651871) B37651871
theorem B33468329 : Blo 1547471 33468329 := bstep (se 2 (by rfl) ⟨12550623, by rfl⟩ : syracuseStep 33468329 = 25101247) B25101247
theorem B22312219 : Blo 1547471 22312219 := bstep (se 1 (by rfl) ⟨16734164, by rfl⟩ : syracuseStep 22312219 = 33468329) B33468329
theorem B29749625 : Blo 1547471 29749625 := bstep (se 2 (by rfl) ⟨11156109, by rfl⟩ : syracuseStep 29749625 = 22312219) B22312219
theorem B19833083 : Blo 1547471 19833083 := bstep (se 1 (by rfl) ⟨14874812, by rfl⟩ : syracuseStep 19833083 = 29749625) B29749625
theorem B13222055 : Blo 1547471 13222055 := bstep (se 1 (by rfl) ⟨9916541, by rfl⟩ : syracuseStep 13222055 = 19833083) B19833083
theorem B8814703 : Blo 1547471 8814703 := bstep (se 1 (by rfl) ⟨6611027, by rfl⟩ : syracuseStep 8814703 = 13222055) B13222055
theorem B11752937 : Blo 1547471 11752937 := bstep (se 2 (by rfl) ⟨4407351, by rfl⟩ : syracuseStep 11752937 = 8814703) B8814703
theorem B7835291 : Blo 1547471 7835291 := bstep (se 1 (by rfl) ⟨5876468, by rfl⟩ : syracuseStep 7835291 = 11752937) B11752937
theorem B5223527 : Blo 1547471 5223527 := bstep (se 1 (by rfl) ⟨3917645, by rfl⟩ : syracuseStep 5223527 = 7835291) B7835291
theorem B3482351 : Blo 1547471 3482351 := bstep (se 1 (by rfl) ⟨2611763, by rfl⟩ : syracuseStep 3482351 = 5223527) B5223527
theorem B2321567 : Blo 1547471 2321567 := bstep (se 1 (by rfl) ⟨1741175, by rfl⟩ : syracuseStep 2321567 = 3482351) B3482351
theorem B1547711 : Blo 1547471 1547711 := bstep (se 1 (by rfl) ⟨1160783, by rfl⟩ : syracuseStep 1547711 = 2321567) B2321567

theorem C0 (j : ℕ) (h1 : 386867 ≤ j) (h2 : j ≤ 387367) : Blo 1547471 (4 * j + 3) := by
  interval_cases j
  · exact B1547471
  · exact B1547475
  · exact B1547479
  · exact B1547483
  · exact B1547487
  · exact B1547491
  · exact B1547495
  · exact B1547499
  · exact B1547503
  · exact B1547507
  · exact B1547511
  · exact B1547515
  · exact B1547519
  · exact B1547523
  · exact B1547527
  · exact B1547531
  · exact B1547535
  · exact B1547539
  · exact B1547543
  · exact B1547547
  · exact B1547551
  · exact B1547555
  · exact B1547559
  · exact B1547563
  · exact B1547567
  · exact B1547571
  · exact B1547575
  · exact B1547579
  · exact B1547583
  · exact B1547587
  · exact B1547591
  · exact B1547595
  · exact B1547599
  · exact B1547603
  · exact B1547607
  · exact B1547611
  · exact B1547615
  · exact B1547619
  · exact B1547623
  · exact B1547627
  · exact B1547631
  · exact B1547635
  · exact B1547639
  · exact B1547643
  · exact B1547647
  · exact B1547651
  · exact B1547655
  · exact B1547659
  · exact B1547663
  · exact B1547667
  · exact B1547671
  · exact B1547675
  · exact B1547679
  · exact B1547683
  · exact B1547687
  · exact B1547691
  · exact B1547695
  · exact B1547699
  · exact B1547703
  · exact B1547707
  · exact B1547711
  · exact B1547715
  · exact B1547719
  · exact B1547723
  · exact B1547727
  · exact B1547731
  · exact B1547735
  · exact B1547739
  · exact B1547743
  · exact B1547747
  · exact B1547751
  · exact B1547755
  · exact B1547759
  · exact B1547763
  · exact B1547767
  · exact B1547771
  · exact B1547775
  · exact B1547779
  · exact B1547783
  · exact B1547787
  · exact B1547791
  · exact B1547795
  · exact B1547799
  · exact B1547803
  · exact B1547807
  · exact B1547811
  · exact B1547815
  · exact B1547819
  · exact B1547823
  · exact B1547827
  · exact B1547831
  · exact B1547835
  · exact B1547839
  · exact B1547843
  · exact B1547847
  · exact B1547851
  · exact B1547855
  · exact B1547859
  · exact B1547863
  · exact B1547867
  · exact B1547871
  · exact B1547875
  · exact B1547879
  · exact B1547883
  · exact B1547887
  · exact B1547891
  · exact B1547895
  · exact B1547899
  · exact B1547903
  · exact B1547907
  · exact B1547911
  · exact B1547915
  · exact B1547919
  · exact B1547923
  · exact B1547927
  · exact B1547931
  · exact B1547935
  · exact B1547939
  · exact B1547943
  · exact B1547947
  · exact B1547951
  · exact B1547955
  · exact B1547959
  · exact B1547963
  · exact B1547967
  · exact B1547971
  · exact B1547975
  · exact B1547979
  · exact B1547983
  · exact B1547987
  · exact B1547991
  · exact B1547995
  · exact B1547999
  · exact B1548003
  · exact B1548007
  · exact B1548011
  · exact B1548015
  · exact B1548019
  · exact B1548023
  · exact B1548027
  · exact B1548031
  · exact B1548035
  · exact B1548039
  · exact B1548043
  · exact B1548047
  · exact B1548051
  · exact B1548055
  · exact B1548059
  · exact B1548063
  · exact B1548067
  · exact B1548071
  · exact B1548075
  · exact B1548079
  · exact B1548083
  · exact B1548087
  · exact B1548091
  · exact B1548095
  · exact B1548099
  · exact B1548103
  · exact B1548107
  · exact B1548111
  · exact B1548115
  · exact B1548119
  · exact B1548123
  · exact B1548127
  · exact B1548131
  · exact B1548135
  · exact B1548139
  · exact B1548143
  · exact B1548147
  · exact B1548151
  · exact B1548155
  · exact B1548159
  · exact B1548163
  · exact B1548167
  · exact B1548171
  · exact B1548175
  · exact B1548179
  · exact B1548183
  · exact B1548187
  · exact B1548191
  · exact B1548195
  · exact B1548199
  · exact B1548203
  · exact B1548207
  · exact B1548211
  · exact B1548215
  · exact B1548219
  · exact B1548223
  · exact B1548227
  · exact B1548231
  · exact B1548235
  · exact B1548239
  · exact B1548243
  · exact B1548247
  · exact B1548251
  · exact B1548255
  · exact B1548259
  · exact B1548263
  · exact B1548267
  · exact B1548271
  · exact B1548275
  · exact B1548279
  · exact B1548283
  · exact B1548287
  · exact B1548291
  · exact B1548295
  · exact B1548299
  · exact B1548303
  · exact B1548307
  · exact B1548311
  · exact B1548315
  · exact B1548319
  · exact B1548323
  · exact B1548327
  · exact B1548331
  · exact B1548335
  · exact B1548339
  · exact B1548343
  · exact B1548347
  · exact B1548351
  · exact B1548355
  · exact B1548359
  · exact B1548363
  · exact B1548367
  · exact B1548371
  · exact B1548375
  · exact B1548379
  · exact B1548383
  · exact B1548387
  · exact B1548391
  · exact B1548395
  · exact B1548399
  · exact B1548403
  · exact B1548407
  · exact B1548411
  · exact B1548415
  · exact B1548419
  · exact B1548423
  · exact B1548427
  · exact B1548431
  · exact B1548435
  · exact B1548439
  · exact B1548443
  · exact B1548447
  · exact B1548451
  · exact B1548455
  · exact B1548459
  · exact B1548463
  · exact B1548467
  · exact B1548471
  · exact B1548475
  · exact B1548479
  · exact B1548483
  · exact B1548487
  · exact B1548491
  · exact B1548495
  · exact B1548499
  · exact B1548503
  · exact B1548507
  · exact B1548511
  · exact B1548515
  · exact B1548519
  · exact B1548523
  · exact B1548527
  · exact B1548531
  · exact B1548535
  · exact B1548539
  · exact B1548543
  · exact B1548547
  · exact B1548551
  · exact B1548555
  · exact B1548559
  · exact B1548563
  · exact B1548567
  · exact B1548571
  · exact B1548575
  · exact B1548579
  · exact B1548583
  · exact B1548587
  · exact B1548591
  · exact B1548595
  · exact B1548599
  · exact B1548603
  · exact B1548607
  · exact B1548611
  · exact B1548615
  · exact B1548619
  · exact B1548623
  · exact B1548627
  · exact B1548631
  · exact B1548635
  · exact B1548639
  · exact B1548643
  · exact B1548647
  · exact B1548651
  · exact B1548655
  · exact B1548659
  · exact B1548663
  · exact B1548667
  · exact B1548671
  · exact B1548675
  · exact B1548679
  · exact B1548683
  · exact B1548687
  · exact B1548691
  · exact B1548695
  · exact B1548699
  · exact B1548703
  · exact B1548707
  · exact B1548711
  · exact B1548715
  · exact B1548719
  · exact B1548723
  · exact B1548727
  · exact B1548731
  · exact B1548735
  · exact B1548739
  · exact B1548743
  · exact B1548747
  · exact B1548751
  · exact B1548755
  · exact B1548759
  · exact B1548763
  · exact B1548767
  · exact B1548771
  · exact B1548775
  · exact B1548779
  · exact B1548783
  · exact B1548787
  · exact B1548791
  · exact B1548795
  · exact B1548799
  · exact B1548803
  · exact B1548807
  · exact B1548811
  · exact B1548815
  · exact B1548819
  · exact B1548823
  · exact B1548827
  · exact B1548831
  · exact B1548835
  · exact B1548839
  · exact B1548843
  · exact B1548847
  · exact B1548851
  · exact B1548855
  · exact B1548859
  · exact B1548863
  · exact B1548867
  · exact B1548871
  · exact B1548875
  · exact B1548879
  · exact B1548883
  · exact B1548887
  · exact B1548891
  · exact B1548895
  · exact B1548899
  · exact B1548903
  · exact B1548907
  · exact B1548911
  · exact B1548915
  · exact B1548919
  · exact B1548923
  · exact B1548927
  · exact B1548931
  · exact B1548935
  · exact B1548939
  · exact B1548943
  · exact B1548947
  · exact B1548951
  · exact B1548955
  · exact B1548959
  · exact B1548963
  · exact B1548967
  · exact B1548971
  · exact B1548975
  · exact B1548979
  · exact B1548983
  · exact B1548987
  · exact B1548991
  · exact B1548995
  · exact B1548999
  · exact B1549003
  · exact B1549007
  · exact B1549011
  · exact B1549015
  · exact B1549019
  · exact B1549023
  · exact B1549027
  · exact B1549031
  · exact B1549035
  · exact B1549039
  · exact B1549043
  · exact B1549047
  · exact B1549051
  · exact B1549055
  · exact B1549059
  · exact B1549063
  · exact B1549067
  · exact B1549071
  · exact B1549075
  · exact B1549079
  · exact B1549083
  · exact B1549087
  · exact B1549091
  · exact B1549095
  · exact B1549099
  · exact B1549103
  · exact B1549107
  · exact B1549111
  · exact B1549115
  · exact B1549119
  · exact B1549123
  · exact B1549127
  · exact B1549131
  · exact B1549135
  · exact B1549139
  · exact B1549143
  · exact B1549147
  · exact B1549151
  · exact B1549155
  · exact B1549159
  · exact B1549163
  · exact B1549167
  · exact B1549171
  · exact B1549175
  · exact B1549179
  · exact B1549183
  · exact B1549187
  · exact B1549191
  · exact B1549195
  · exact B1549199
  · exact B1549203
  · exact B1549207
  · exact B1549211
  · exact B1549215
  · exact B1549219
  · exact B1549223
  · exact B1549227
  · exact B1549231
  · exact B1549235
  · exact B1549239
  · exact B1549243
  · exact B1549247
  · exact B1549251
  · exact B1549255
  · exact B1549259
  · exact B1549263
  · exact B1549267
  · exact B1549271
  · exact B1549275
  · exact B1549279
  · exact B1549283
  · exact B1549287
  · exact B1549291
  · exact B1549295
  · exact B1549299
  · exact B1549303
  · exact B1549307
  · exact B1549311
  · exact B1549315
  · exact B1549319
  · exact B1549323
  · exact B1549327
  · exact B1549331
  · exact B1549335
  · exact B1549339
  · exact B1549343
  · exact B1549347
  · exact B1549351
  · exact B1549355
  · exact B1549359
  · exact B1549363
  · exact B1549367
  · exact B1549371
  · exact B1549375
  · exact B1549379
  · exact B1549383
  · exact B1549387
  · exact B1549391
  · exact B1549395
  · exact B1549399
  · exact B1549403
  · exact B1549407
  · exact B1549411
  · exact B1549415
  · exact B1549419
  · exact B1549423
  · exact B1549427
  · exact B1549431
  · exact B1549435
  · exact B1549439
  · exact B1549443
  · exact B1549447
  · exact B1549451
  · exact B1549455
  · exact B1549459
  · exact B1549463
  · exact B1549467
  · exact B1549471

theorem solution (m : ℕ) (hlo : 1547471 ≤ m) (hhi : m ≤ 1549471) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 386867 ≤ j := by omega
    have hj2 : j ≤ 387367 := by omega
    have hb : Blo 1547471 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
