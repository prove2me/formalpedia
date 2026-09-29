-- Prove2me | solution 1 for syracuse_descends_range_1583990_1585490
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:08:08.631541+00:00
-- url     : https://prove2.me/submissions/8b8789eb-0747-4562-80fd-1526b3e353c1

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


theorem B4284485 : Blo 1583990 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B4513877 : Blo 1583990 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B5079125 : Blo 1583990 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B4817029 : Blo 1583990 4817029 := bbase (se 4 (by rfl) ⟨451596, by rfl⟩ : syracuseStep 4817029 = 903193) (by norm_num)
theorem B5349509 : Blo 1583990 5349509 := bbase (se 4 (by rfl) ⟨501516, by rfl⟩ : syracuseStep 5349509 = 1003033) (by norm_num)
theorem B8020133 : Blo 1583990 8020133 := bbase (se 4 (by rfl) ⟨751887, by rfl⟩ : syracuseStep 8020133 = 1503775) (by norm_num)
theorem B22839509 : Blo 1583990 22839509 := bbase (se 7 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 22839509 = 535301) (by norm_num)
theorem B1605953 : Blo 1583990 1605953 := bbase (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) (by norm_num)
theorem B2376005 : Blo 1583990 2376005 := bbase (se 4 (by rfl) ⟨222750, by rfl⟩ : syracuseStep 2376005 = 445501) (by norm_num)
theorem B2376029 : Blo 1583990 2376029 := bbase (se 3 (by rfl) ⟨445505, by rfl⟩ : syracuseStep 2376029 = 891011) (by norm_num)
theorem B2376053 : Blo 1583990 2376053 := bbase (se 5 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 2376053 = 222755) (by norm_num)
theorem B2376077 : Blo 1583990 2376077 := bbase (se 3 (by rfl) ⟨445514, by rfl⟩ : syracuseStep 2376077 = 891029) (by norm_num)
theorem B4284821 : Blo 1583990 4284821 := bbase (se 6 (by rfl) ⟨100425, by rfl⟩ : syracuseStep 4284821 = 200851) (by norm_num)
theorem B2376101 : Blo 1583990 2376101 := bbase (se 4 (by rfl) ⟨222759, by rfl⟩ : syracuseStep 2376101 = 445519) (by norm_num)
theorem B3211693 : Blo 1583990 3211693 := bbase (se 3 (by rfl) ⟨602192, by rfl⟩ : syracuseStep 3211693 = 1204385) (by norm_num)
theorem B2376125 : Blo 1583990 2376125 := bbase (se 3 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 2376125 = 891047) (by norm_num)
theorem B3563981 : Blo 1583990 3563981 := bbase (se 3 (by rfl) ⟨668246, by rfl⟩ : syracuseStep 3563981 = 1336493) (by norm_num)
theorem B2376149 : Blo 1583990 2376149 := bbase (se 7 (by rfl) ⟨27845, by rfl⟩ : syracuseStep 2376149 = 55691) (by norm_num)
theorem B2376173 : Blo 1583990 2376173 := bbase (se 3 (by rfl) ⟨445532, by rfl⟩ : syracuseStep 2376173 = 891065) (by norm_num)
theorem B2376197 : Blo 1583990 2376197 := bbase (se 4 (by rfl) ⟨222768, by rfl⟩ : syracuseStep 2376197 = 445537) (by norm_num)
theorem B3564053 : Blo 1583990 3564053 := bbase (se 6 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 3564053 = 167065) (by norm_num)
theorem B2376221 : Blo 1583990 2376221 := bbase (se 3 (by rfl) ⟨445541, by rfl⟩ : syracuseStep 2376221 = 891083) (by norm_num)
theorem B2376245 : Blo 1583990 2376245 := bbase (se 5 (by rfl) ⟨111386, by rfl⟩ : syracuseStep 2376245 = 222773) (by norm_num)
theorem B5349941 : Blo 1583990 5349941 := bbase (se 5 (by rfl) ⟨250778, by rfl⟩ : syracuseStep 5349941 = 501557) (by norm_num)
theorem B2376269 : Blo 1583990 2376269 := bbase (se 3 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 2376269 = 891101) (by norm_num)
theorem B5423701 : Blo 1583990 5423701 := bbase (se 8 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 5423701 = 63559) (by norm_num)
theorem B3564125 : Blo 1583990 3564125 := bbase (se 3 (by rfl) ⟨668273, by rfl⟩ : syracuseStep 3564125 = 1336547) (by norm_num)
theorem B2376293 : Blo 1583990 2376293 := bbase (se 4 (by rfl) ⟨222777, by rfl⟩ : syracuseStep 2376293 = 445555) (by norm_num)
theorem B7717493 : Blo 1583990 7717493 := bbase (se 5 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 7717493 = 723515) (by norm_num)
theorem B2376317 : Blo 1583990 2376317 := bbase (se 3 (by rfl) ⟨445559, by rfl⟩ : syracuseStep 2376317 = 891119) (by norm_num)
theorem B1606289 : Blo 1583990 1606289 := bbase (se 2 (by rfl) ⟨602358, by rfl⟩ : syracuseStep 1606289 = 1204717) (by norm_num)
theorem B2376341 : Blo 1583990 2376341 := bbase (se 6 (by rfl) ⟨55695, by rfl⟩ : syracuseStep 2376341 = 111391) (by norm_num)
theorem B3564197 : Blo 1583990 3564197 := bbase (se 4 (by rfl) ⟨334143, by rfl⟩ : syracuseStep 3564197 = 668287) (by norm_num)
theorem B2376365 : Blo 1583990 2376365 := bbase (se 3 (by rfl) ⟨445568, by rfl⟩ : syracuseStep 2376365 = 891137) (by norm_num)
theorem B2376389 : Blo 1583990 2376389 := bbase (se 4 (by rfl) ⟨222786, by rfl⟩ : syracuseStep 2376389 = 445573) (by norm_num)
theorem B2376413 : Blo 1583990 2376413 := bbase (se 3 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 2376413 = 891155) (by norm_num)
theorem B3564269 : Blo 1583990 3564269 := bbase (se 3 (by rfl) ⟨668300, by rfl⟩ : syracuseStep 3564269 = 1336601) (by norm_num)
theorem B2376437 : Blo 1583990 2376437 := bbase (se 5 (by rfl) ⟨111395, by rfl⟩ : syracuseStep 2376437 = 222791) (by norm_num)
theorem B2376461 : Blo 1583990 2376461 := bbase (se 3 (by rfl) ⟨445586, by rfl⟩ : syracuseStep 2376461 = 891173) (by norm_num)
theorem B2376485 : Blo 1583990 2376485 := bbase (se 4 (by rfl) ⟨222795, by rfl⟩ : syracuseStep 2376485 = 445591) (by norm_num)
theorem B3007277 : Blo 1583990 3007277 := bbase (se 3 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 3007277 = 1127729) (by norm_num)
theorem B3384109 : Blo 1583990 3384109 := bbase (se 3 (by rfl) ⟨634520, by rfl⟩ : syracuseStep 3384109 = 1269041) (by norm_num)
theorem B3564341 : Blo 1583990 3564341 := bbase (se 5 (by rfl) ⟨167078, by rfl⟩ : syracuseStep 3564341 = 334157) (by norm_num)
theorem B2376509 : Blo 1583990 2376509 := bbase (se 3 (by rfl) ⟨445595, by rfl⟩ : syracuseStep 2376509 = 891191) (by norm_num)
theorem B3613501 : Blo 1583990 3613501 := bbase (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) (by norm_num)
theorem B4514629 : Blo 1583990 4514629 := bbase (se 4 (by rfl) ⟨423246, by rfl⟩ : syracuseStep 4514629 = 846493) (by norm_num)
theorem B2409293 : Blo 1583990 2409293 := bbase (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) (by norm_num)
theorem B2376533 : Blo 1583990 2376533 := bbase (se 9 (by rfl) ⟨6962, by rfl⟩ : syracuseStep 2376533 = 13925) (by norm_num)
theorem B2376557 : Blo 1583990 2376557 := bbase (se 3 (by rfl) ⟨445604, by rfl⟩ : syracuseStep 2376557 = 891209) (by norm_num)
theorem B3212149 : Blo 1583990 3212149 := bbase (se 5 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 3212149 = 301139) (by norm_num)
theorem B3564413 : Blo 1583990 3564413 := bbase (se 3 (by rfl) ⟨668327, by rfl⟩ : syracuseStep 3564413 = 1336655) (by norm_num)
theorem B2376581 : Blo 1583990 2376581 := bbase (se 4 (by rfl) ⟨222804, by rfl⟩ : syracuseStep 2376581 = 445609) (by norm_num)
theorem B2376605 : Blo 1583990 2376605 := bbase (se 3 (by rfl) ⟨445613, by rfl⟩ : syracuseStep 2376605 = 891227) (by norm_num)
theorem B2376629 : Blo 1583990 2376629 := bbase (se 5 (by rfl) ⟨111404, by rfl⟩ : syracuseStep 2376629 = 222809) (by norm_num)
theorem B3564485 : Blo 1583990 3564485 := bbase (se 4 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 3564485 = 668341) (by norm_num)
theorem B2376653 : Blo 1583990 2376653 := bbase (se 3 (by rfl) ⟨445622, by rfl⟩ : syracuseStep 2376653 = 891245) (by norm_num)
theorem B2376677 : Blo 1583990 2376677 := bbase (se 4 (by rfl) ⟨222813, by rfl⟩ : syracuseStep 2376677 = 445627) (by norm_num)
theorem B5350373 : Blo 1583990 5350373 := bbase (se 4 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 5350373 = 1003195) (by norm_num)
theorem B2376701 : Blo 1583990 2376701 := bbase (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) (by norm_num)
theorem B3564557 : Blo 1583990 3564557 := bbase (se 3 (by rfl) ⟨668354, by rfl⟩ : syracuseStep 3564557 = 1336709) (by norm_num)
theorem B2376725 : Blo 1583990 2376725 := bbase (se 6 (by rfl) ⟨55704, by rfl⟩ : syracuseStep 2376725 = 111409) (by norm_num)
theorem B2376749 : Blo 1583990 2376749 := bbase (se 3 (by rfl) ⟨445640, by rfl⟩ : syracuseStep 2376749 = 891281) (by norm_num)
theorem B2376773 : Blo 1583990 2376773 := bbase (se 4 (by rfl) ⟨222822, by rfl⟩ : syracuseStep 2376773 = 445645) (by norm_num)
theorem B3564629 : Blo 1583990 3564629 := bbase (se 8 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 3564629 = 41773) (by norm_num)
theorem B2376797 : Blo 1583990 2376797 := bbase (se 3 (by rfl) ⟨445649, by rfl⟩ : syracuseStep 2376797 = 891299) (by norm_num)
theorem B2376821 : Blo 1583990 2376821 := bbase (se 5 (by rfl) ⟨111413, by rfl⟩ : syracuseStep 2376821 = 222827) (by norm_num)
theorem B2376845 : Blo 1583990 2376845 := bbase (se 3 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 2376845 = 891317) (by norm_num)
theorem B3564701 : Blo 1583990 3564701 := bbase (se 3 (by rfl) ⟨668381, by rfl⟩ : syracuseStep 3564701 = 1336763) (by norm_num)
theorem B2376869 : Blo 1583990 2376869 := bbase (se 4 (by rfl) ⟨222831, by rfl⟩ : syracuseStep 2376869 = 445663) (by norm_num)
theorem B2376893 : Blo 1583990 2376893 := bbase (se 3 (by rfl) ⟨445667, by rfl⟩ : syracuseStep 2376893 = 891335) (by norm_num)
theorem B2376917 : Blo 1583990 2376917 := bbase (se 7 (by rfl) ⟨27854, by rfl⟩ : syracuseStep 2376917 = 55709) (by norm_num)
theorem B1606873 : Blo 1583990 1606873 := bbase (se 2 (by rfl) ⟨602577, by rfl⟩ : syracuseStep 1606873 = 1205155) (by norm_num)
theorem B3564773 : Blo 1583990 3564773 := bbase (se 4 (by rfl) ⟨334197, by rfl⟩ : syracuseStep 3564773 = 668395) (by norm_num)
theorem B2376941 : Blo 1583990 2376941 := bbase (se 3 (by rfl) ⟨445676, by rfl⟩ : syracuseStep 2376941 = 891353) (by norm_num)
theorem B1983745 : Blo 1583990 1983745 := bbase (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) (by norm_num)
theorem B2376965 : Blo 1583990 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B4818197 : Blo 1583990 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B2376989 : Blo 1583990 2376989 := bbase (se 3 (by rfl) ⟨445685, by rfl⟩ : syracuseStep 2376989 = 891371) (by norm_num)
theorem B3384605 : Blo 1583990 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B3564845 : Blo 1583990 3564845 := bbase (se 3 (by rfl) ⟨668408, by rfl⟩ : syracuseStep 3564845 = 1336817) (by norm_num)
theorem B2377013 : Blo 1583990 2377013 := bbase (se 5 (by rfl) ⟨111422, by rfl⟩ : syracuseStep 2377013 = 222845) (by norm_num)
theorem B2377037 : Blo 1583990 2377037 := bbase (se 3 (by rfl) ⟨445694, by rfl⟩ : syracuseStep 2377037 = 891389) (by norm_num)
theorem B2377061 : Blo 1583990 2377061 := bbase (se 4 (by rfl) ⟨222849, by rfl⟩ : syracuseStep 2377061 = 445699) (by norm_num)
theorem B3564917 : Blo 1583990 3564917 := bbase (se 5 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 3564917 = 334211) (by norm_num)
theorem B2377085 : Blo 1583990 2377085 := bbase (se 3 (by rfl) ⟨445703, by rfl⟩ : syracuseStep 2377085 = 891407) (by norm_num)
theorem B6014357 : Blo 1583990 6014357 := bbase (se 6 (by rfl) ⟨140961, by rfl⟩ : syracuseStep 6014357 = 281923) (by norm_num)
theorem B2377109 : Blo 1583990 2377109 := bbase (se 6 (by rfl) ⟨55713, by rfl⟩ : syracuseStep 2377109 = 111427) (by norm_num)
theorem B5350805 : Blo 1583990 5350805 := bbase (se 6 (by rfl) ⟨125409, by rfl⟩ : syracuseStep 5350805 = 250819) (by norm_num)
theorem B2377133 : Blo 1583990 2377133 := bbase (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) (by norm_num)
theorem B8021429 : Blo 1583990 8021429 := bbase (se 5 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 8021429 = 752009) (by norm_num)
theorem B3564989 : Blo 1583990 3564989 := bbase (se 3 (by rfl) ⟨668435, by rfl⟩ : syracuseStep 3564989 = 1336871) (by norm_num)
theorem B2377157 : Blo 1583990 2377157 := bbase (se 4 (by rfl) ⟨222858, by rfl⟩ : syracuseStep 2377157 = 445717) (by norm_num)
theorem B2377181 : Blo 1583990 2377181 := bbase (se 3 (by rfl) ⟨445721, by rfl⟩ : syracuseStep 2377181 = 891443) (by norm_num)
theorem B2377205 : Blo 1583990 2377205 := bbase (se 5 (by rfl) ⟨111431, by rfl⟩ : syracuseStep 2377205 = 222863) (by norm_num)
theorem B3565061 : Blo 1583990 3565061 := bbase (se 4 (by rfl) ⟨334224, by rfl⟩ : syracuseStep 3565061 = 668449) (by norm_num)
theorem B2377229 : Blo 1583990 2377229 := bbase (se 3 (by rfl) ⟨445730, by rfl⟩ : syracuseStep 2377229 = 891461) (by norm_num)
theorem B3008029 : Blo 1583990 3008029 := bbase (se 3 (by rfl) ⟨564005, by rfl⟩ : syracuseStep 3008029 = 1128011) (by norm_num)
theorem B2377253 : Blo 1583990 2377253 := bbase (se 4 (by rfl) ⟨222867, by rfl⟩ : syracuseStep 2377253 = 445735) (by norm_num)
theorem B2573869 : Blo 1583990 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B2377277 : Blo 1583990 2377277 := bbase (se 3 (by rfl) ⟨445739, by rfl⟩ : syracuseStep 2377277 = 891479) (by norm_num)
theorem B3565133 : Blo 1583990 3565133 := bbase (se 3 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 3565133 = 1336925) (by norm_num)
theorem B2377301 : Blo 1583990 2377301 := bbase (se 8 (by rfl) ⟨13929, by rfl⟩ : syracuseStep 2377301 = 27859) (by norm_num)
theorem B13542997 : Blo 1583990 13542997 := bbase (se 8 (by rfl) ⟨79353, by rfl⟩ : syracuseStep 13542997 = 158707) (by norm_num)
theorem B2377325 : Blo 1583990 2377325 := bbase (se 3 (by rfl) ⟨445748, by rfl⟩ : syracuseStep 2377325 = 891497) (by norm_num)
theorem B2377349 : Blo 1583990 2377349 := bbase (se 4 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 2377349 = 445753) (by norm_num)
theorem B3565205 : Blo 1583990 3565205 := bbase (se 6 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 3565205 = 167119) (by norm_num)
theorem B2377373 : Blo 1583990 2377373 := bbase (se 3 (by rfl) ⟨445757, by rfl⟩ : syracuseStep 2377373 = 891515) (by norm_num)
theorem B3008173 : Blo 1583990 3008173 := bbase (se 3 (by rfl) ⟨564032, by rfl⟩ : syracuseStep 3008173 = 1128065) (by norm_num)
theorem B6014645 : Blo 1583990 6014645 := bbase (se 5 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 6014645 = 563873) (by norm_num)
theorem B2377397 : Blo 1583990 2377397 := bbase (se 5 (by rfl) ⟨111440, by rfl⟩ : syracuseStep 2377397 = 222881) (by norm_num)
theorem B2377421 : Blo 1583990 2377421 := bbase (se 3 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 2377421 = 891533) (by norm_num)
theorem B3565277 : Blo 1583990 3565277 := bbase (se 3 (by rfl) ⟨668489, by rfl⟩ : syracuseStep 3565277 = 1336979) (by norm_num)
theorem B2377445 : Blo 1583990 2377445 := bbase (se 4 (by rfl) ⟨222885, by rfl⟩ : syracuseStep 2377445 = 445771) (by norm_num)
theorem B2377469 : Blo 1583990 2377469 := bbase (se 3 (by rfl) ⟨445775, by rfl⟩ : syracuseStep 2377469 = 891551) (by norm_num)
theorem B2377493 : Blo 1583990 2377493 := bbase (se 6 (by rfl) ⟨55722, by rfl⟩ : syracuseStep 2377493 = 111445) (by norm_num)
theorem B3565349 : Blo 1583990 3565349 := bbase (se 4 (by rfl) ⟨334251, by rfl⟩ : syracuseStep 3565349 = 668503) (by norm_num)
theorem B2377517 : Blo 1583990 2377517 := bbase (se 3 (by rfl) ⟨445784, by rfl⟩ : syracuseStep 2377517 = 891569) (by norm_num)
theorem B2377541 : Blo 1583990 2377541 := bbase (se 4 (by rfl) ⟨222894, by rfl⟩ : syracuseStep 2377541 = 445789) (by norm_num)
theorem B3008333 : Blo 1583990 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B87934805 : Blo 1583990 87934805 := bbase (se 9 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 87934805 = 515243) (by norm_num)
theorem B2377565 : Blo 1583990 2377565 := bbase (se 3 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 2377565 = 891587) (by norm_num)
theorem B3565421 : Blo 1583990 3565421 := bbase (se 3 (by rfl) ⟨668516, by rfl⟩ : syracuseStep 3565421 = 1337033) (by norm_num)
theorem B2377589 : Blo 1583990 2377589 := bbase (se 5 (by rfl) ⟨111449, by rfl⟩ : syracuseStep 2377589 = 222899) (by norm_num)
theorem B2377613 : Blo 1583990 2377613 := bbase (se 3 (by rfl) ⟨445802, by rfl⟩ : syracuseStep 2377613 = 891605) (by norm_num)
theorem B5146517 : Blo 1583990 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B7612325 : Blo 1583990 7612325 := bbase (se 4 (by rfl) ⟨713655, by rfl⟩ : syracuseStep 7612325 = 1427311) (by norm_num)
theorem B2377637 : Blo 1583990 2377637 := bbase (se 4 (by rfl) ⟨222903, by rfl⟩ : syracuseStep 2377637 = 445807) (by norm_num)
theorem B3565493 : Blo 1583990 3565493 := bbase (se 5 (by rfl) ⟨167132, by rfl⟩ : syracuseStep 3565493 = 334265) (by norm_num)
theorem B2377661 : Blo 1583990 2377661 := bbase (se 3 (by rfl) ⟨445811, by rfl⟩ : syracuseStep 2377661 = 891623) (by norm_num)
theorem B2377685 : Blo 1583990 2377685 := bbase (se 7 (by rfl) ⟨27863, by rfl⟩ : syracuseStep 2377685 = 55727) (by norm_num)
theorem B3008477 : Blo 1583990 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B2377709 : Blo 1583990 2377709 := bbase (se 3 (by rfl) ⟨445820, by rfl⟩ : syracuseStep 2377709 = 891641) (by norm_num)
theorem B6768629 : Blo 1583990 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B3565565 : Blo 1583990 3565565 := bbase (se 3 (by rfl) ⟨668543, by rfl⟩ : syracuseStep 3565565 = 1337087) (by norm_num)
theorem B2377733 : Blo 1583990 2377733 := bbase (se 4 (by rfl) ⟨222912, by rfl⟩ : syracuseStep 2377733 = 445825) (by norm_num)
theorem B9635861 : Blo 1583990 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B2377757 : Blo 1583990 2377757 := bbase (se 3 (by rfl) ⟨445829, by rfl⟩ : syracuseStep 2377757 = 891659) (by norm_num)
theorem B2377781 : Blo 1583990 2377781 := bbase (se 5 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 2377781 = 222917) (by norm_num)
theorem B3565637 : Blo 1583990 3565637 := bbase (se 4 (by rfl) ⟨334278, by rfl⟩ : syracuseStep 3565637 = 668557) (by norm_num)
theorem B2377805 : Blo 1583990 2377805 := bbase (se 3 (by rfl) ⟨445838, by rfl⟩ : syracuseStep 2377805 = 891677) (by norm_num)
theorem B2377829 : Blo 1583990 2377829 := bbase (se 4 (by rfl) ⟨222921, by rfl⟩ : syracuseStep 2377829 = 445843) (by norm_num)
theorem B9021557 : Blo 1583990 9021557 := bbase (se 5 (by rfl) ⟨422885, by rfl⟩ : syracuseStep 9021557 = 845771) (by norm_num)
theorem B3385469 : Blo 1583990 3385469 := bbase (se 3 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 3385469 = 1269551) (by norm_num)
theorem B2377853 : Blo 1583990 2377853 := bbase (se 3 (by rfl) ⟨445847, by rfl⟩ : syracuseStep 2377853 = 891695) (by norm_num)
theorem B3565709 : Blo 1583990 3565709 := bbase (se 3 (by rfl) ⟨668570, by rfl⟩ : syracuseStep 3565709 = 1337141) (by norm_num)
theorem B2377877 : Blo 1583990 2377877 := bbase (se 6 (by rfl) ⟨55731, by rfl⟩ : syracuseStep 2377877 = 111463) (by norm_num)
theorem B2377901 : Blo 1583990 2377901 := bbase (se 3 (by rfl) ⟨445856, by rfl⟩ : syracuseStep 2377901 = 891713) (by norm_num)
theorem B2377925 : Blo 1583990 2377925 := bbase (se 4 (by rfl) ⟨222930, by rfl⟩ : syracuseStep 2377925 = 445861) (by norm_num)
theorem B3565781 : Blo 1583990 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B2377949 : Blo 1583990 2377949 := bbase (se 3 (by rfl) ⟨445865, by rfl⟩ : syracuseStep 2377949 = 891731) (by norm_num)
theorem B2377973 : Blo 1583990 2377973 := bbase (se 5 (by rfl) ⟨111467, by rfl⟩ : syracuseStep 2377973 = 222935) (by norm_num)
theorem B3008765 : Blo 1583990 3008765 := bbase (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) (by norm_num)
theorem B3385613 : Blo 1583990 3385613 := bbase (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) (by norm_num)
theorem B2377997 : Blo 1583990 2377997 := bbase (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) (by norm_num)
theorem B3565853 : Blo 1583990 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B2378021 : Blo 1583990 2378021 := bbase (se 4 (by rfl) ⟨222939, by rfl⟩ : syracuseStep 2378021 = 445879) (by norm_num)
theorem B2378045 : Blo 1583990 2378045 := bbase (se 3 (by rfl) ⟨445883, by rfl⟩ : syracuseStep 2378045 = 891767) (by norm_num)
theorem B2378069 : Blo 1583990 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B3565925 : Blo 1583990 3565925 := bbase (se 4 (by rfl) ⟨334305, by rfl⟩ : syracuseStep 3565925 = 668611) (by norm_num)
theorem B2378093 : Blo 1583990 2378093 := bbase (se 3 (by rfl) ⟨445892, by rfl⟩ : syracuseStep 2378093 = 891785) (by norm_num)
theorem B2673013 : Blo 1583990 2673013 := bbase (se 5 (by rfl) ⟨125297, by rfl⟩ : syracuseStep 2673013 = 250595) (by norm_num)
theorem B2378117 : Blo 1583990 2378117 := bbase (se 4 (by rfl) ⟨222948, by rfl⟩ : syracuseStep 2378117 = 445897) (by norm_num)
theorem B3049877 : Blo 1583990 3049877 := bbase (se 6 (by rfl) ⟨71481, by rfl⟩ : syracuseStep 3049877 = 142963) (by norm_num)
theorem B3008917 : Blo 1583990 3008917 := bbase (se 6 (by rfl) ⟨70521, by rfl⟩ : syracuseStep 3008917 = 141043) (by norm_num)
theorem B2378141 : Blo 1583990 2378141 := bbase (se 3 (by rfl) ⟨445901, by rfl⟩ : syracuseStep 2378141 = 891803) (by norm_num)
theorem B3565997 : Blo 1583990 3565997 := bbase (se 3 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 3565997 = 1337249) (by norm_num)
theorem B2378165 : Blo 1583990 2378165 := bbase (se 5 (by rfl) ⟨111476, by rfl⟩ : syracuseStep 2378165 = 222953) (by norm_num)
theorem B2673101 : Blo 1583990 2673101 := bbase (se 3 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 2673101 = 1002413) (by norm_num)
theorem B2378189 : Blo 1583990 2378189 := bbase (se 3 (by rfl) ⟨445910, by rfl⟩ : syracuseStep 2378189 = 891821) (by norm_num)
theorem B2378213 : Blo 1583990 2378213 := bbase (se 4 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 2378213 = 445915) (by norm_num)
theorem B3566069 : Blo 1583990 3566069 := bbase (se 5 (by rfl) ⟨167159, by rfl⟩ : syracuseStep 3566069 = 334319) (by norm_num)
theorem B3566141 : Blo 1583990 3566141 := bbase (se 3 (by rfl) ⟨668651, by rfl⟩ : syracuseStep 3566141 = 1337303) (by norm_num)
theorem B2673229 : Blo 1583990 2673229 := bbase (se 3 (by rfl) ⟨501230, by rfl⟩ : syracuseStep 2673229 = 1002461) (by norm_num)
theorem B10152533 : Blo 1583990 10152533 := bbase (se 8 (by rfl) ⟨59487, by rfl⟩ : syracuseStep 10152533 = 118975) (by norm_num)
theorem B3566213 : Blo 1583990 3566213 := bbase (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) (by norm_num)
theorem B2673317 : Blo 1583990 2673317 := bbase (se 4 (by rfl) ⟨250623, by rfl⟩ : syracuseStep 2673317 = 501247) (by norm_num)
theorem B8022725 : Blo 1583990 8022725 := bbase (se 4 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 8022725 = 1504261) (by norm_num)
theorem B3009221 : Blo 1583990 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B3566285 : Blo 1583990 3566285 := bbase (se 3 (by rfl) ⟨668678, by rfl⟩ : syracuseStep 3566285 = 1337357) (by norm_num)
theorem B2255629 : Blo 1583990 2255629 := bbase (se 3 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 2255629 = 845861) (by norm_num)
theorem B11578133 : Blo 1583990 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B3566357 : Blo 1583990 3566357 := bbase (se 6 (by rfl) ⟨83586, by rfl⟩ : syracuseStep 3566357 = 167173) (by norm_num)
theorem B2673445 : Blo 1583990 2673445 := bbase (se 4 (by rfl) ⟨250635, by rfl⟩ : syracuseStep 2673445 = 501271) (by norm_num)
theorem B5712677 : Blo 1583990 5712677 := bbase (se 4 (by rfl) ⟨535563, by rfl⟩ : syracuseStep 5712677 = 1071127) (by norm_num)
theorem B6015829 : Blo 1583990 6015829 := bbase (se 9 (by rfl) ⟨17624, by rfl⟩ : syracuseStep 6015829 = 35249) (by norm_num)
theorem B3566429 : Blo 1583990 3566429 := bbase (se 3 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 3566429 = 1337411) (by norm_num)
theorem B2673533 : Blo 1583990 2673533 := bbase (se 3 (by rfl) ⟨501287, by rfl⟩ : syracuseStep 2673533 = 1002575) (by norm_num)
theorem B3566501 : Blo 1583990 3566501 := bbase (se 4 (by rfl) ⟨334359, by rfl⟩ : syracuseStep 3566501 = 668719) (by norm_num)
theorem B2255845 : Blo 1583990 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B3566573 : Blo 1583990 3566573 := bbase (se 3 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 3566573 = 1337465) (by norm_num)
theorem B2673661 : Blo 1583990 2673661 := bbase (se 3 (by rfl) ⟨501311, by rfl⟩ : syracuseStep 2673661 = 1002623) (by norm_num)
theorem B3566645 : Blo 1583990 3566645 := bbase (se 5 (by rfl) ⟨167186, by rfl⟩ : syracuseStep 3566645 = 334373) (by norm_num)
theorem B2673749 : Blo 1583990 2673749 := bbase (se 8 (by rfl) ⟨15666, by rfl⟩ : syracuseStep 2673749 = 31333) (by norm_num)
theorem B3566717 : Blo 1583990 3566717 := bbase (se 3 (by rfl) ⟨668759, by rfl⟩ : syracuseStep 3566717 = 1337519) (by norm_num)
theorem B6016133 : Blo 1583990 6016133 := bbase (se 4 (by rfl) ⟨564012, by rfl⟩ : syracuseStep 6016133 = 1128025) (by norm_num)
theorem B21679253 : Blo 1583990 21679253 := bbase (se 6 (by rfl) ⟨508107, by rfl⟩ : syracuseStep 21679253 = 1016215) (by norm_num)
theorem B3566789 : Blo 1583990 3566789 := bbase (se 4 (by rfl) ⟨334386, by rfl⟩ : syracuseStep 3566789 = 668773) (by norm_num)
theorem B18541781 : Blo 1583990 18541781 := bbase (se 7 (by rfl) ⟨217286, by rfl⟩ : syracuseStep 18541781 = 434573) (by norm_num)
theorem B2673877 : Blo 1583990 2673877 := bbase (se 7 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 2673877 = 62669) (by norm_num)
theorem B3566861 : Blo 1583990 3566861 := bbase (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) (by norm_num)
theorem B2673965 : Blo 1583990 2673965 := bbase (se 3 (by rfl) ⟨501368, by rfl⟩ : syracuseStep 2673965 = 1002737) (by norm_num)
theorem B2895173 : Blo 1583990 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B3566933 : Blo 1583990 3566933 := bbase (se 11 (by rfl) ⟨2612, by rfl⟩ : syracuseStep 3566933 = 5225) (by norm_num)
theorem B2256221 : Blo 1583990 2256221 := bbase (se 3 (by rfl) ⟨423041, by rfl⟩ : syracuseStep 2256221 = 846083) (by norm_num)
theorem B3567005 : Blo 1583990 3567005 := bbase (se 3 (by rfl) ⟨668813, by rfl⟩ : syracuseStep 3567005 = 1337627) (by norm_num)
theorem B2674093 : Blo 1583990 2674093 := bbase (se 3 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 2674093 = 1002785) (by norm_num)
theorem B7228885 : Blo 1583990 7228885 := bbase (se 7 (by rfl) ⟨84713, by rfl⟩ : syracuseStep 7228885 = 169427) (by norm_num)
theorem B7228901 : Blo 1583990 7228901 := bbase (se 4 (by rfl) ⟨677709, by rfl⟩ : syracuseStep 7228901 = 1355419) (by norm_num)
theorem B3567077 : Blo 1583990 3567077 := bbase (se 4 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 3567077 = 668827) (by norm_num)
theorem B2674181 : Blo 1583990 2674181 := bbase (se 4 (by rfl) ⟨250704, by rfl⟩ : syracuseStep 2674181 = 501409) (by norm_num)
theorem B4820485 : Blo 1583990 4820485 := bbase (se 4 (by rfl) ⟨451920, by rfl⟩ : syracuseStep 4820485 = 903841) (by norm_num)
theorem B3567149 : Blo 1583990 3567149 := bbase (se 3 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 3567149 = 1337681) (by norm_num)
theorem B14462549 : Blo 1583990 14462549 := bbase (se 8 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 14462549 = 169483) (by norm_num)
theorem B3567221 : Blo 1583990 3567221 := bbase (se 5 (by rfl) ⟨167213, by rfl⟩ : syracuseStep 3567221 = 334427) (by norm_num)
theorem B2674309 : Blo 1583990 2674309 := bbase (se 4 (by rfl) ⟨250716, by rfl⟩ : syracuseStep 2674309 = 501433) (by norm_num)
theorem B4009621 : Blo 1583990 4009621 := bbase (se 6 (by rfl) ⟨93975, by rfl⟩ : syracuseStep 4009621 = 187951) (by norm_num)
theorem B3567293 : Blo 1583990 3567293 := bbase (se 3 (by rfl) ⟨668867, by rfl⟩ : syracuseStep 3567293 = 1337735) (by norm_num)
theorem B16076501 : Blo 1583990 16076501 := bbase (se 7 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 16076501 = 376793) (by norm_num)
theorem B2674397 : Blo 1583990 2674397 := bbase (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) (by norm_num)
theorem B6770405 : Blo 1583990 6770405 := bbase (se 4 (by rfl) ⟨634725, by rfl⟩ : syracuseStep 6770405 = 1269451) (by norm_num)
theorem B1904369 : Blo 1583990 1904369 := bbase (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) (by norm_num)
theorem B4009733 : Blo 1583990 4009733 := bbase (se 4 (by rfl) ⟨375912, by rfl⟩ : syracuseStep 4009733 = 751825) (by norm_num)
theorem B5713685 : Blo 1583990 5713685 := bbase (se 6 (by rfl) ⟨133914, by rfl⟩ : syracuseStep 5713685 = 267829) (by norm_num)
theorem B2674525 : Blo 1583990 2674525 := bbase (se 3 (by rfl) ⟨501473, by rfl⟩ : syracuseStep 2674525 = 1002947) (by norm_num)
theorem B1929065 : Blo 1583990 1929065 := bbase (se 2 (by rfl) ⟨723399, by rfl⟩ : syracuseStep 1929065 = 1446799) (by norm_num)
theorem B2748325 : Blo 1583990 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B2674613 : Blo 1583990 2674613 := bbase (se 5 (by rfl) ⟨125372, by rfl⟩ : syracuseStep 2674613 = 250745) (by norm_num)
theorem B4009925 : Blo 1583990 4009925 := bbase (se 4 (by rfl) ⟨375930, by rfl⟩ : syracuseStep 4009925 = 751861) (by norm_num)
theorem B2854853 : Blo 1583990 2854853 := bbase (se 4 (by rfl) ⟨267642, by rfl⟩ : syracuseStep 2854853 = 535285) (by norm_num)
theorem B1904581 : Blo 1583990 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B8024021 : Blo 1583990 8024021 := bbase (se 7 (by rfl) ⟨94031, by rfl⟩ : syracuseStep 8024021 = 188063) (by norm_num)
theorem B1691641 : Blo 1583990 1691641 := bbase (se 2 (by rfl) ⟨634365, by rfl⟩ : syracuseStep 1691641 = 1268731) (by norm_num)
theorem B2674741 : Blo 1583990 2674741 := bbase (se 5 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 2674741 = 250757) (by norm_num)
theorem B1691713 : Blo 1583990 1691713 := bbase (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) (by norm_num)
theorem B2854997 : Blo 1583990 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B1904725 : Blo 1583990 1904725 := bbase (se 8 (by rfl) ⟨11160, by rfl⟩ : syracuseStep 1904725 = 22321) (by norm_num)
theorem B2674829 : Blo 1583990 2674829 := bbase (se 3 (by rfl) ⟨501530, by rfl⟩ : syracuseStep 2674829 = 1003061) (by norm_num)
theorem B1806565 : Blo 1583990 1806565 := bbase (se 4 (by rfl) ⟨169365, by rfl⟩ : syracuseStep 1806565 = 338731) (by norm_num)
theorem B1782013 : Blo 1583990 1782013 := bbase (se 3 (by rfl) ⟨334127, by rfl⟩ : syracuseStep 1782013 = 668255) (by norm_num)
theorem B2674957 : Blo 1583990 2674957 := bbase (se 3 (by rfl) ⟨501554, by rfl⟩ : syracuseStep 2674957 = 1003109) (by norm_num)
theorem B4010269 : Blo 1583990 4010269 := bbase (se 3 (by rfl) ⟨751925, by rfl⟩ : syracuseStep 4010269 = 1503851) (by norm_num)
theorem B1782049 : Blo 1583990 1782049 := bbase (se 2 (by rfl) ⟨668268, by rfl⟩ : syracuseStep 1782049 = 1336537) (by norm_num)
theorem B3256613 : Blo 1583990 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B1782085 : Blo 1583990 1782085 := bbase (se 4 (by rfl) ⟨167070, by rfl⟩ : syracuseStep 1782085 = 334141) (by norm_num)
theorem B2675045 : Blo 1583990 2675045 := bbase (se 4 (by rfl) ⟨250785, by rfl⟩ : syracuseStep 2675045 = 501571) (by norm_num)
theorem B1782121 : Blo 1583990 1782121 := bbase (se 2 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 1782121 = 1336591) (by norm_num)
theorem B1782157 : Blo 1583990 1782157 := bbase (se 3 (by rfl) ⟨334154, by rfl⟩ : syracuseStep 1782157 = 668309) (by norm_num)
theorem B4010381 : Blo 1583990 4010381 := bbase (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) (by norm_num)
theorem B1782193 : Blo 1583990 1782193 := bbase (se 2 (by rfl) ⟨668322, by rfl⟩ : syracuseStep 1782193 = 1336645) (by norm_num)
theorem B1692085 : Blo 1583990 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1782229 : Blo 1583990 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B2675173 : Blo 1583990 2675173 := bbase (se 4 (by rfl) ⟨250797, by rfl⟩ : syracuseStep 2675173 = 501595) (by norm_num)
theorem B1782265 : Blo 1583990 1782265 := bbase (se 2 (by rfl) ⟨668349, by rfl⟩ : syracuseStep 1782265 = 1336699) (by norm_num)
theorem B1782301 : Blo 1583990 1782301 := bbase (se 3 (by rfl) ⟨334181, by rfl⟩ : syracuseStep 1782301 = 668363) (by norm_num)
theorem B2675261 : Blo 1583990 2675261 := bbase (se 3 (by rfl) ⟨501611, by rfl⟩ : syracuseStep 2675261 = 1003223) (by norm_num)
theorem B1782337 : Blo 1583990 1782337 := bbase (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) (by norm_num)
theorem B4010573 : Blo 1583990 4010573 := bbase (se 3 (by rfl) ⟨751982, by rfl⟩ : syracuseStep 4010573 = 1503965) (by norm_num)
theorem B11424341 : Blo 1583990 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B1782373 : Blo 1583990 1782373 := bbase (se 4 (by rfl) ⟨167097, by rfl⟩ : syracuseStep 1782373 = 334195) (by norm_num)
theorem B7615093 : Blo 1583990 7615093 := bbase (se 5 (by rfl) ⟨356957, by rfl⟩ : syracuseStep 7615093 = 713915) (by norm_num)
theorem B1782409 : Blo 1583990 1782409 := bbase (se 2 (by rfl) ⟨668403, by rfl⟩ : syracuseStep 1782409 = 1336807) (by norm_num)
theorem B1782445 : Blo 1583990 1782445 := bbase (se 3 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 1782445 = 668417) (by norm_num)
theorem B2675389 : Blo 1583990 2675389 := bbase (se 3 (by rfl) ⟨501635, by rfl⟩ : syracuseStep 2675389 = 1003271) (by norm_num)
theorem B6771397 : Blo 1583990 6771397 := bbase (se 4 (by rfl) ⟨634818, by rfl⟩ : syracuseStep 6771397 = 1269637) (by norm_num)
theorem B1782481 : Blo 1583990 1782481 := bbase (se 2 (by rfl) ⟨668430, by rfl⟩ : syracuseStep 1782481 = 1336861) (by norm_num)
theorem B3134173 : Blo 1583990 3134173 := bbase (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) (by norm_num)
theorem B1782517 : Blo 1583990 1782517 := bbase (se 5 (by rfl) ⟨83555, by rfl⟩ : syracuseStep 1782517 = 167111) (by norm_num)
theorem B5346053 : Blo 1583990 5346053 := bbase (se 4 (by rfl) ⟨501192, by rfl⟩ : syracuseStep 5346053 = 1002385) (by norm_num)
theorem B2675477 : Blo 1583990 2675477 := bbase (se 6 (by rfl) ⟨62706, by rfl⟩ : syracuseStep 2675477 = 125413) (by norm_num)
theorem B1782553 : Blo 1583990 1782553 := bbase (se 2 (by rfl) ⟨668457, by rfl⟩ : syracuseStep 1782553 = 1336915) (by norm_num)
theorem B1692461 : Blo 1583990 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B1782589 : Blo 1583990 1782589 := bbase (se 3 (by rfl) ⟨334235, by rfl⟩ : syracuseStep 1782589 = 668471) (by norm_num)
theorem B1782625 : Blo 1583990 1782625 := bbase (se 2 (by rfl) ⟨668484, by rfl⟩ : syracuseStep 1782625 = 1336969) (by norm_num)
theorem B1692533 : Blo 1583990 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B1782661 : Blo 1583990 1782661 := bbase (se 4 (by rfl) ⟨167124, by rfl⟩ : syracuseStep 1782661 = 334249) (by norm_num)
theorem B4010917 : Blo 1583990 4010917 := bbase (se 4 (by rfl) ⟨376023, by rfl⟩ : syracuseStep 4010917 = 752047) (by norm_num)
theorem B1782697 : Blo 1583990 1782697 := bbase (se 2 (by rfl) ⟨668511, by rfl⟩ : syracuseStep 1782697 = 1337023) (by norm_num)
theorem B5075909 : Blo 1583990 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B1782733 : Blo 1583990 1782733 := bbase (se 3 (by rfl) ⟨334262, by rfl⟩ : syracuseStep 1782733 = 668525) (by norm_num)
theorem B1782769 : Blo 1583990 1782769 := bbase (se 2 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 1782769 = 1337077) (by norm_num)
theorem B4011029 : Blo 1583990 4011029 := bbase (se 6 (by rfl) ⟨94008, by rfl⟩ : syracuseStep 4011029 = 188017) (by norm_num)
theorem B1782805 : Blo 1583990 1782805 := bbase (se 6 (by rfl) ⟨41784, by rfl⟩ : syracuseStep 1782805 = 83569) (by norm_num)
theorem B1692721 : Blo 1583990 1692721 := bbase (se 2 (by rfl) ⟨634770, by rfl⟩ : syracuseStep 1692721 = 1269541) (by norm_num)
theorem B1782841 : Blo 1583990 1782841 := bbase (se 2 (by rfl) ⟨668565, by rfl⟩ : syracuseStep 1782841 = 1337131) (by norm_num)
theorem B1782877 : Blo 1583990 1782877 := bbase (se 3 (by rfl) ⟨334289, by rfl⟩ : syracuseStep 1782877 = 668579) (by norm_num)
theorem B1782913 : Blo 1583990 1782913 := bbase (se 2 (by rfl) ⟨668592, by rfl⟩ : syracuseStep 1782913 = 1337185) (by norm_num)
theorem B5420197 : Blo 1583990 5420197 := bbase (se 4 (by rfl) ⟨508143, by rfl⟩ : syracuseStep 5420197 = 1016287) (by norm_num)
theorem B1782949 : Blo 1583990 1782949 := bbase (se 4 (by rfl) ⟨167151, by rfl⟩ : syracuseStep 1782949 = 334303) (by norm_num)
theorem B1832113 : Blo 1583990 1832113 := bbase (se 2 (by rfl) ⟨687042, by rfl⟩ : syracuseStep 1832113 = 1374085) (by norm_num)
theorem B5346485 : Blo 1583990 5346485 := bbase (se 5 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 5346485 = 501233) (by norm_num)
theorem B6018245 : Blo 1583990 6018245 := bbase (se 4 (by rfl) ⟨564210, by rfl⟩ : syracuseStep 6018245 = 1128421) (by norm_num)
theorem B1782985 : Blo 1583990 1782985 := bbase (se 2 (by rfl) ⟨668619, by rfl⟩ : syracuseStep 1782985 = 1337239) (by norm_num)
theorem B4011221 : Blo 1583990 4011221 := bbase (se 7 (by rfl) ⟨47006, by rfl⟩ : syracuseStep 4011221 = 94013) (by norm_num)
theorem B8025317 : Blo 1583990 8025317 := bbase (se 4 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 8025317 = 1504747) (by norm_num)
theorem B1692905 : Blo 1583990 1692905 := bbase (se 2 (by rfl) ⟨634839, by rfl⟩ : syracuseStep 1692905 = 1269679) (by norm_num)
theorem B1783021 : Blo 1583990 1783021 := bbase (se 3 (by rfl) ⟨334316, by rfl⟩ : syracuseStep 1783021 = 668633) (by norm_num)
theorem B1783057 : Blo 1583990 1783057 := bbase (se 2 (by rfl) ⟨668646, by rfl⟩ : syracuseStep 1783057 = 1337293) (by norm_num)
theorem B1783093 : Blo 1583990 1783093 := bbase (se 5 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 1783093 = 167165) (by norm_num)
theorem B1783129 : Blo 1583990 1783129 := bbase (se 2 (by rfl) ⟨668673, by rfl⟩ : syracuseStep 1783129 = 1337347) (by norm_num)
theorem B16258421 : Blo 1583990 16258421 := bbase (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) (by norm_num)
theorem B1783165 : Blo 1583990 1783165 := bbase (se 3 (by rfl) ⟨334343, by rfl⟩ : syracuseStep 1783165 = 668687) (by norm_num)
theorem B3806605 : Blo 1583990 3806605 := bbase (se 3 (by rfl) ⟨713738, by rfl⟩ : syracuseStep 3806605 = 1427477) (by norm_num)
theorem B1783201 : Blo 1583990 1783201 := bbase (se 2 (by rfl) ⟨668700, by rfl⟩ : syracuseStep 1783201 = 1337401) (by norm_num)
theorem B1783237 : Blo 1583990 1783237 := bbase (se 4 (by rfl) ⟨167178, by rfl⟩ : syracuseStep 1783237 = 334357) (by norm_num)
theorem B4511189 : Blo 1583990 4511189 := bbase (se 7 (by rfl) ⟨52865, by rfl⟩ : syracuseStep 4511189 = 105731) (by norm_num)
theorem B6018533 : Blo 1583990 6018533 := bbase (se 4 (by rfl) ⟨564237, by rfl⟩ : syracuseStep 6018533 = 1128475) (by norm_num)
theorem B1783273 : Blo 1583990 1783273 := bbase (se 2 (by rfl) ⟨668727, by rfl⟩ : syracuseStep 1783273 = 1337455) (by norm_num)
theorem B1783309 : Blo 1583990 1783309 := bbase (se 3 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 1783309 = 668741) (by norm_num)
theorem B4011565 : Blo 1583990 4011565 := bbase (se 3 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 4011565 = 1504337) (by norm_num)
theorem B1783345 : Blo 1583990 1783345 := bbase (se 2 (by rfl) ⟨668754, by rfl⟩ : syracuseStep 1783345 = 1337509) (by norm_num)
theorem B1783381 : Blo 1583990 1783381 := bbase (se 8 (by rfl) ⟨10449, by rfl⟩ : syracuseStep 1783381 = 20899) (by norm_num)
theorem B1955425 : Blo 1583990 1955425 := bbase (se 2 (by rfl) ⟨733284, by rfl⟩ : syracuseStep 1955425 = 1466569) (by norm_num)
theorem B5346917 : Blo 1583990 5346917 := bbase (se 4 (by rfl) ⟨501273, by rfl⟩ : syracuseStep 5346917 = 1002547) (by norm_num)
theorem B1783417 : Blo 1583990 1783417 := bbase (se 2 (by rfl) ⟨668781, by rfl⟩ : syracuseStep 1783417 = 1337563) (by norm_num)
theorem B4011677 : Blo 1583990 4011677 := bbase (se 3 (by rfl) ⟨752189, by rfl⟩ : syracuseStep 4011677 = 1504379) (by norm_num)
theorem B1783453 : Blo 1583990 1783453 := bbase (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) (by norm_num)
theorem B1783489 : Blo 1583990 1783489 := bbase (se 2 (by rfl) ⟨668808, by rfl⟩ : syracuseStep 1783489 = 1337617) (by norm_num)
theorem B5076677 : Blo 1583990 5076677 := bbase (se 4 (by rfl) ⟨475938, by rfl⟩ : syracuseStep 5076677 = 951877) (by norm_num)
theorem B1783525 : Blo 1583990 1783525 := bbase (se 4 (by rfl) ⟨167205, by rfl⟩ : syracuseStep 1783525 = 334411) (by norm_num)
theorem B2004745 : Blo 1583990 2004745 := bbase (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) (by norm_num)
theorem B1783561 : Blo 1583990 1783561 := bbase (se 2 (by rfl) ⟨668835, by rfl⟩ : syracuseStep 1783561 = 1337671) (by norm_num)
theorem B1783597 : Blo 1583990 1783597 := bbase (se 3 (by rfl) ⟨334424, by rfl⟩ : syracuseStep 1783597 = 668849) (by norm_num)
theorem B1783633 : Blo 1583990 1783633 := bbase (se 2 (by rfl) ⟨668862, by rfl⟩ : syracuseStep 1783633 = 1337725) (by norm_num)
theorem B4011869 : Blo 1583990 4011869 := bbase (se 3 (by rfl) ⟨752225, by rfl⟩ : syracuseStep 4011869 = 1504451) (by norm_num)
theorem B2004841 : Blo 1583990 2004841 := bbase (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) (by norm_num)
theorem B1783669 : Blo 1583990 1783669 := bbase (se 5 (by rfl) ⟨83609, by rfl⟩ : syracuseStep 1783669 = 167219) (by norm_num)
theorem B2709469 : Blo 1583990 2709469 := bbase (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) (by norm_num)
theorem B2005013 : Blo 1583990 2005013 := bbase (se 6 (by rfl) ⟨46992, by rfl⟩ : syracuseStep 2005013 = 93985) (by norm_num)
theorem B5347349 : Blo 1583990 5347349 := bbase (se 6 (by rfl) ⟨125328, by rfl⟩ : syracuseStep 5347349 = 250657) (by norm_num)
theorem B2005069 : Blo 1583990 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B3807317 : Blo 1583990 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B2857045 : Blo 1583990 2857045 := bbase (se 8 (by rfl) ⟨16740, by rfl⟩ : syracuseStep 2857045 = 33481) (by norm_num)
theorem B2005165 : Blo 1583990 2005165 := bbase (se 3 (by rfl) ⟨375968, by rfl⟩ : syracuseStep 2005165 = 751937) (by norm_num)
theorem B4012213 : Blo 1583990 4012213 := bbase (se 5 (by rfl) ⟨188072, by rfl⟩ : syracuseStep 4012213 = 376145) (by norm_num)
theorem B5077189 : Blo 1583990 5077189 := bbase (se 4 (by rfl) ⟨475986, by rfl⟩ : syracuseStep 5077189 = 951973) (by norm_num)
theorem B4012325 : Blo 1583990 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B2005337 : Blo 1583990 2005337 := bbase (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) (by norm_num)
theorem B2005393 : Blo 1583990 2005393 := bbase (se 2 (by rfl) ⟨752022, by rfl⟩ : syracuseStep 2005393 = 1504045) (by norm_num)
theorem B5347781 : Blo 1583990 5347781 := bbase (se 4 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 5347781 = 1002709) (by norm_num)
theorem B3807701 : Blo 1583990 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B4012517 : Blo 1583990 4012517 := bbase (se 4 (by rfl) ⟨376173, by rfl⟩ : syracuseStep 4012517 = 752347) (by norm_num)
theorem B2005489 : Blo 1583990 2005489 := bbase (se 2 (by rfl) ⟨752058, by rfl⟩ : syracuseStep 2005489 = 1504117) (by norm_num)
theorem B6019717 : Blo 1583990 6019717 := bbase (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) (by norm_num)
theorem B2005661 : Blo 1583990 2005661 := bbase (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) (by norm_num)
theorem B2005717 : Blo 1583990 2005717 := bbase (se 7 (by rfl) ⟨23504, by rfl⟩ : syracuseStep 2005717 = 47009) (by norm_num)
theorem B3807989 : Blo 1583990 3807989 := bbase (se 5 (by rfl) ⟨178499, by rfl⟩ : syracuseStep 3807989 = 356999) (by norm_num)
theorem B2005813 : Blo 1583990 2005813 := bbase (se 5 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 2005813 = 188045) (by norm_num)
theorem B4012861 : Blo 1583990 4012861 := bbase (se 3 (by rfl) ⟨752411, by rfl⟩ : syracuseStep 4012861 = 1504823) (by norm_num)
theorem B5348213 : Blo 1583990 5348213 := bbase (se 5 (by rfl) ⟨250697, by rfl⟩ : syracuseStep 5348213 = 501395) (by norm_num)
theorem B4012973 : Blo 1583990 4012973 := bbase (se 3 (by rfl) ⟨752432, by rfl⟩ : syracuseStep 4012973 = 1504865) (by norm_num)
theorem B4283317 : Blo 1583990 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B4021213 : Blo 1583990 4021213 := bbase (se 3 (by rfl) ⟨753977, by rfl⟩ : syracuseStep 4021213 = 1507955) (by norm_num)
theorem B2005985 : Blo 1583990 2005985 := bbase (se 2 (by rfl) ⟨752244, by rfl⟩ : syracuseStep 2005985 = 1504489) (by norm_num)
theorem B4512773 : Blo 1583990 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B2006041 : Blo 1583990 2006041 := bbase (se 2 (by rfl) ⟨752265, by rfl⟩ : syracuseStep 2006041 = 1504531) (by norm_num)
theorem B2538557 : Blo 1583990 2538557 := bbase (se 3 (by rfl) ⟨475979, by rfl⟩ : syracuseStep 2538557 = 951959) (by norm_num)
theorem B4013165 : Blo 1583990 4013165 := bbase (se 3 (by rfl) ⟨752468, by rfl⟩ : syracuseStep 4013165 = 1504937) (by norm_num)
theorem B2006137 : Blo 1583990 2006137 := bbase (se 2 (by rfl) ⟨752301, by rfl⟩ : syracuseStep 2006137 = 1504603) (by norm_num)
theorem B6511765 : Blo 1583990 6511765 := bbase (se 6 (by rfl) ⟨152619, by rfl⟩ : syracuseStep 6511765 = 305239) (by norm_num)
theorem B31284437 : Blo 1583990 31284437 := bbase (se 7 (by rfl) ⟨366614, by rfl⟩ : syracuseStep 31284437 = 733229) (by norm_num)
theorem B2538749 : Blo 1583990 2538749 := bbase (se 3 (by rfl) ⟨476015, by rfl⟩ : syracuseStep 2538749 = 952031) (by norm_num)
theorem B5348645 : Blo 1583990 5348645 := bbase (se 4 (by rfl) ⟨501435, by rfl⟩ : syracuseStep 5348645 = 1002871) (by norm_num)
theorem B2006309 : Blo 1583990 2006309 := bbase (se 4 (by rfl) ⟨188091, by rfl⟩ : syracuseStep 2006309 = 376183) (by norm_num)
theorem B2006365 : Blo 1583990 2006365 := bbase (se 3 (by rfl) ⟨376193, by rfl⟩ : syracuseStep 2006365 = 752387) (by norm_num)
theorem B2538877 : Blo 1583990 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B2006461 : Blo 1583990 2006461 := bbase (se 3 (by rfl) ⟨376211, by rfl⟩ : syracuseStep 2006461 = 752423) (by norm_num)
theorem B3431909 : Blo 1583990 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B2006633 : Blo 1583990 2006633 := bbase (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) (by norm_num)
theorem B4513445 : Blo 1583990 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B5349077 : Blo 1583990 5349077 := bbase (se 7 (by rfl) ⟨62684, by rfl⟩ : syracuseStep 5349077 = 125369) (by norm_num)
theorem B12033845 : Blo 1583990 12033845 := bbase (se 5 (by rfl) ⟨564086, by rfl⟩ : syracuseStep 12033845 = 1128173) (by norm_num)
theorem B2236285 : Blo 1583990 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B5078933 : Blo 1583990 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B3383221 : Blo 1583990 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B2539517 : Blo 1583990 2539517 := bbase (se 3 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 2539517 = 952319) (by norm_num)
theorem B3809393 : Blo 1583990 3809393 := bstep (se 2 (by rfl) ⟨1428522, by rfl⟩ : syracuseStep 3809393 = 2857045) B2857045
theorem B6422705 : Blo 1583990 6422705 := bstep (se 2 (by rfl) ⟨2408514, by rfl⟩ : syracuseStep 6422705 = 4817029) B4817029
theorem B2171075 : Blo 1583990 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B5349617 : Blo 1583990 5349617 := bstep (se 2 (by rfl) ⟨2006106, by rfl⟩ : syracuseStep 5349617 = 4012213) B4012213
theorem B9027845 : Blo 1583990 9027845 := bstep (se 4 (by rfl) ⟨846360, by rfl⟩ : syracuseStep 9027845 = 1692721) B1692721
theorem B2408753 : Blo 1583990 2408753 := bstep (se 2 (by rfl) ⟨903282, by rfl⟩ : syracuseStep 2408753 = 1806565) B1806565
theorem B2375987 : Blo 1583990 2375987 := bstep (se 1 (by rfl) ⟨1781990, by rfl⟩ : syracuseStep 2375987 = 3563981) B3563981
theorem B2376017 : Blo 1583990 2376017 := bstep (se 2 (by rfl) ⟨891006, by rfl⟩ : syracuseStep 2376017 = 1782013) B1782013
theorem B2376035 : Blo 1583990 2376035 := bstep (se 1 (by rfl) ⟨1782026, by rfl⟩ : syracuseStep 2376035 = 3564053) B3564053
theorem B2376065 : Blo 1583990 2376065 := bstep (se 2 (by rfl) ⟨891024, by rfl⟩ : syracuseStep 2376065 = 1782049) B1782049
theorem B2376083 : Blo 1583990 2376083 := bstep (se 1 (by rfl) ⟨1782062, by rfl⟩ : syracuseStep 2376083 = 3564125) B3564125
theorem B5144995 : Blo 1583990 5144995 := bstep (se 1 (by rfl) ⟨3858746, by rfl⟩ : syracuseStep 5144995 = 7717493) B7717493
theorem B2376113 : Blo 1583990 2376113 := bstep (se 2 (by rfl) ⟨891042, by rfl⟩ : syracuseStep 2376113 = 1782085) B1782085
theorem B2376131 : Blo 1583990 2376131 := bstep (se 1 (by rfl) ⟨1782098, by rfl⟩ : syracuseStep 2376131 = 3564197) B3564197
theorem B10158533 : Blo 1583990 10158533 := bstep (se 4 (by rfl) ⟨952362, by rfl⟩ : syracuseStep 10158533 = 1904725) B1904725
theorem B2376161 : Blo 1583990 2376161 := bstep (se 2 (by rfl) ⟨891060, by rfl⟩ : syracuseStep 2376161 = 1782121) B1782121
theorem B3564017 : Blo 1583990 3564017 := bstep (se 2 (by rfl) ⟨1336506, by rfl⟩ : syracuseStep 3564017 = 2673013) B2673013
theorem B2376179 : Blo 1583990 2376179 := bstep (se 1 (by rfl) ⟨1782134, by rfl⟩ : syracuseStep 2376179 = 3564269) B3564269
theorem B3564035 : Blo 1583990 3564035 := bstep (se 1 (by rfl) ⟨2673026, by rfl⟩ : syracuseStep 3564035 = 5346053) B5346053
theorem B2376209 : Blo 1583990 2376209 := bstep (se 2 (by rfl) ⟨891078, by rfl⟩ : syracuseStep 2376209 = 1782157) B1782157
theorem B2376227 : Blo 1583990 2376227 := bstep (se 1 (by rfl) ⟨1782170, by rfl⟩ : syracuseStep 2376227 = 3564341) B3564341
theorem B1606195 : Blo 1583990 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B2376257 : Blo 1583990 2376257 := bstep (se 2 (by rfl) ⟨891096, by rfl⟩ : syracuseStep 2376257 = 1782193) B1782193
theorem B2376275 : Blo 1583990 2376275 := bstep (se 1 (by rfl) ⟨1782206, by rfl⟩ : syracuseStep 2376275 = 3564413) B3564413
theorem B4514413 : Blo 1583990 4514413 := bstep (se 3 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 4514413 = 1692905) B1692905
theorem B2376305 : Blo 1583990 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B2376323 : Blo 1583990 2376323 := bstep (se 1 (by rfl) ⟨1782242, by rfl⟩ : syracuseStep 2376323 = 3564485) B3564485
theorem B3383939 : Blo 1583990 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B2376353 : Blo 1583990 2376353 := bstep (se 2 (by rfl) ⟨891132, by rfl⟩ : syracuseStep 2376353 = 1782265) B1782265
theorem B2376371 : Blo 1583990 2376371 := bstep (se 1 (by rfl) ⟨1782278, by rfl⟩ : syracuseStep 2376371 = 3564557) B3564557
theorem B2376401 : Blo 1583990 2376401 := bstep (se 2 (by rfl) ⟨891150, by rfl⟩ : syracuseStep 2376401 = 1782301) B1782301
theorem B2376419 : Blo 1583990 2376419 := bstep (se 1 (by rfl) ⟨1782314, by rfl⟩ : syracuseStep 2376419 = 3564629) B3564629
theorem B2376449 : Blo 1583990 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B5350157 : Blo 1583990 5350157 := bstep (se 3 (by rfl) ⟨1003154, by rfl⟩ : syracuseStep 5350157 = 2006309) B2006309
theorem B3564305 : Blo 1583990 3564305 := bstep (se 2 (by rfl) ⟨1336614, by rfl⟩ : syracuseStep 3564305 = 2673229) B2673229
theorem B2376467 : Blo 1583990 2376467 := bstep (se 1 (by rfl) ⟨1782350, by rfl⟩ : syracuseStep 2376467 = 3564701) B3564701
theorem B3564323 : Blo 1583990 3564323 := bstep (se 1 (by rfl) ⟨2673242, by rfl⟩ : syracuseStep 3564323 = 5346485) B5346485
theorem B2376497 : Blo 1583990 2376497 := bstep (se 2 (by rfl) ⟨891186, by rfl⟩ : syracuseStep 2376497 = 1782373) B1782373
theorem B2376515 : Blo 1583990 2376515 := bstep (se 1 (by rfl) ⟨1782386, by rfl⟩ : syracuseStep 2376515 = 3564773) B3564773
theorem B5350211 : Blo 1583990 5350211 := bstep (se 1 (by rfl) ⟨4012658, by rfl⟩ : syracuseStep 5350211 = 8025317) B8025317
theorem B2376545 : Blo 1583990 2376545 := bstep (se 2 (by rfl) ⟨891204, by rfl⟩ : syracuseStep 2376545 = 1782409) B1782409
theorem B3212131 : Blo 1583990 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B2376563 : Blo 1583990 2376563 := bstep (se 1 (by rfl) ⟨1782422, by rfl⟩ : syracuseStep 2376563 = 3564845) B3564845
theorem B2376593 : Blo 1583990 2376593 := bstep (se 2 (by rfl) ⟨891222, by rfl⟩ : syracuseStep 2376593 = 1782445) B1782445
theorem B10838947 : Blo 1583990 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B2376611 : Blo 1583990 2376611 := bstep (se 1 (by rfl) ⟨1782458, by rfl⟩ : syracuseStep 2376611 = 3564917) B3564917
theorem B9028529 : Blo 1583990 9028529 := bstep (se 2 (by rfl) ⟨3385698, by rfl⟩ : syracuseStep 9028529 = 6771397) B6771397
theorem B2376641 : Blo 1583990 2376641 := bstep (se 2 (by rfl) ⟨891240, by rfl⟩ : syracuseStep 2376641 = 1782481) B1782481
theorem B4178897 : Blo 1583990 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B2376659 : Blo 1583990 2376659 := bstep (se 1 (by rfl) ⟨1782494, by rfl⟩ : syracuseStep 2376659 = 3564989) B3564989
theorem B3007459 : Blo 1583990 3007459 := bstep (se 1 (by rfl) ⟨2255594, by rfl⟩ : syracuseStep 3007459 = 4511189) B4511189
theorem B2376689 : Blo 1583990 2376689 := bstep (se 2 (by rfl) ⟨891258, by rfl⟩ : syracuseStep 2376689 = 1782517) B1782517
theorem B2376707 : Blo 1583990 2376707 := bstep (se 1 (by rfl) ⟨1782530, by rfl⟩ : syracuseStep 2376707 = 3565061) B3565061
theorem B3007505 : Blo 1583990 3007505 := bstep (se 2 (by rfl) ⟨1127814, by rfl⟩ : syracuseStep 3007505 = 2255629) B2255629
theorem B2376737 : Blo 1583990 2376737 := bstep (se 2 (by rfl) ⟨891276, by rfl⟩ : syracuseStep 2376737 = 1782553) B1782553
theorem B3564593 : Blo 1583990 3564593 := bstep (se 2 (by rfl) ⟨1336722, by rfl⟩ : syracuseStep 3564593 = 2673445) B2673445
theorem B2376755 : Blo 1583990 2376755 := bstep (se 1 (by rfl) ⟨1782566, by rfl⟩ : syracuseStep 2376755 = 3565133) B3565133
theorem B3564611 : Blo 1583990 3564611 := bstep (se 1 (by rfl) ⟨2673458, by rfl⟩ : syracuseStep 3564611 = 5346917) B5346917
theorem B2376785 : Blo 1583990 2376785 := bstep (se 2 (by rfl) ⟨891294, by rfl⟩ : syracuseStep 2376785 = 1782589) B1782589
theorem B5350481 : Blo 1583990 5350481 := bstep (se 2 (by rfl) ⟨2006430, by rfl⟩ : syracuseStep 5350481 = 4012861) B4012861
theorem B2376803 : Blo 1583990 2376803 := bstep (se 1 (by rfl) ⟨1782602, by rfl⟩ : syracuseStep 2376803 = 3565205) B3565205
theorem B8021105 : Blo 1583990 8021105 := bstep (se 2 (by rfl) ⟨3007914, by rfl⟩ : syracuseStep 8021105 = 6015829) B6015829
theorem B2376833 : Blo 1583990 2376833 := bstep (se 2 (by rfl) ⟨891312, by rfl⟩ : syracuseStep 2376833 = 1782625) B1782625
theorem B3384451 : Blo 1583990 3384451 := bstep (se 1 (by rfl) ⟨2538338, by rfl⟩ : syracuseStep 3384451 = 5076677) B5076677
theorem B2376851 : Blo 1583990 2376851 := bstep (se 1 (by rfl) ⟨1782638, by rfl⟩ : syracuseStep 2376851 = 3565277) B3565277
theorem B2376881 : Blo 1583990 2376881 := bstep (se 2 (by rfl) ⟨891330, by rfl⟩ : syracuseStep 2376881 = 1782661) B1782661
theorem B2376899 : Blo 1583990 2376899 := bstep (se 1 (by rfl) ⟨1782674, by rfl⟩ : syracuseStep 2376899 = 3565349) B3565349
theorem B2376929 : Blo 1583990 2376929 := bstep (se 2 (by rfl) ⟨891348, by rfl⟩ : syracuseStep 2376929 = 1782697) B1782697
theorem B58623203 : Blo 1583990 58623203 := bstep (se 1 (by rfl) ⟨43967402, by rfl⟩ : syracuseStep 58623203 = 87934805) B87934805
theorem B5711089 : Blo 1583990 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B2376947 : Blo 1583990 2376947 := bstep (se 1 (by rfl) ⟨1782710, by rfl⟩ : syracuseStep 2376947 = 3565421) B3565421
theorem B9151757 : Blo 1583990 9151757 := bstep (se 3 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 9151757 = 3431909) B3431909
theorem B2376977 : Blo 1583990 2376977 := bstep (se 2 (by rfl) ⟨891366, by rfl⟩ : syracuseStep 2376977 = 1782733) B1782733
theorem B2376995 : Blo 1583990 2376995 := bstep (se 1 (by rfl) ⟨1782746, by rfl⟩ : syracuseStep 2376995 = 3565493) B3565493
theorem B3007793 : Blo 1583990 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B2377025 : Blo 1583990 2377025 := bstep (se 2 (by rfl) ⟨891384, by rfl⟩ : syracuseStep 2377025 = 1782769) B1782769
theorem B3564881 : Blo 1583990 3564881 := bstep (se 2 (by rfl) ⟨1336830, by rfl⟩ : syracuseStep 3564881 = 2673661) B2673661
theorem B2377043 : Blo 1583990 2377043 := bstep (se 1 (by rfl) ⟨1782782, by rfl⟩ : syracuseStep 2377043 = 3565565) B3565565
theorem B6423907 : Blo 1583990 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B3564899 : Blo 1583990 3564899 := bstep (se 1 (by rfl) ⟨2673674, by rfl⟩ : syracuseStep 3564899 = 5347349) B5347349
theorem B2377073 : Blo 1583990 2377073 := bstep (se 2 (by rfl) ⟨891402, by rfl⟩ : syracuseStep 2377073 = 1782805) B1782805
theorem B2377091 : Blo 1583990 2377091 := bstep (se 1 (by rfl) ⟨1782818, by rfl⟩ : syracuseStep 2377091 = 3565637) B3565637
theorem B2377121 : Blo 1583990 2377121 := bstep (se 2 (by rfl) ⟨891420, by rfl⟩ : syracuseStep 2377121 = 1782841) B1782841
theorem B6014371 : Blo 1583990 6014371 := bstep (se 1 (by rfl) ⟨4510778, by rfl⟩ : syracuseStep 6014371 = 9021557) B9021557
theorem B2377139 : Blo 1583990 2377139 := bstep (se 1 (by rfl) ⟨1782854, by rfl⟩ : syracuseStep 2377139 = 3565709) B3565709
theorem B2377169 : Blo 1583990 2377169 := bstep (se 2 (by rfl) ⟨891438, by rfl⟩ : syracuseStep 2377169 = 1782877) B1782877
theorem B2377187 : Blo 1583990 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B2377217 : Blo 1583990 2377217 := bstep (se 2 (by rfl) ⟨891456, by rfl⟩ : syracuseStep 2377217 = 1782913) B1782913
theorem B2377235 : Blo 1583990 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B7226929 : Blo 1583990 7226929 := bstep (se 2 (by rfl) ⟨2710098, by rfl⟩ : syracuseStep 7226929 = 5420197) B5420197
theorem B2377265 : Blo 1583990 2377265 := bstep (se 2 (by rfl) ⟨891474, by rfl⟩ : syracuseStep 2377265 = 1782949) B1782949
theorem B2442817 : Blo 1583990 2442817 := bstep (se 2 (by rfl) ⟨916056, by rfl⟩ : syracuseStep 2442817 = 1832113) B1832113
theorem B2377283 : Blo 1583990 2377283 := bstep (se 1 (by rfl) ⟨1782962, by rfl⟩ : syracuseStep 2377283 = 3565925) B3565925
theorem B18048581 : Blo 1583990 18048581 := bstep (se 4 (by rfl) ⟨1692054, by rfl⟩ : syracuseStep 18048581 = 3384109) B3384109
theorem B2377313 : Blo 1583990 2377313 := bstep (se 2 (by rfl) ⟨891492, by rfl⟩ : syracuseStep 2377313 = 1782985) B1782985
theorem B2033251 : Blo 1583990 2033251 := bstep (se 1 (by rfl) ⟨1524938, by rfl⟩ : syracuseStep 2033251 = 3049877) B3049877
theorem B5351021 : Blo 1583990 5351021 := bstep (se 3 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 5351021 = 2006633) B2006633
theorem B3565169 : Blo 1583990 3565169 := bstep (se 2 (by rfl) ⟨1336938, by rfl⟩ : syracuseStep 3565169 = 2673877) B2673877
theorem B2377331 : Blo 1583990 2377331 := bstep (se 1 (by rfl) ⟨1782998, by rfl⟩ : syracuseStep 2377331 = 3565997) B3565997
theorem B3565187 : Blo 1583990 3565187 := bstep (se 1 (by rfl) ⟨2673890, by rfl⟩ : syracuseStep 3565187 = 5347781) B5347781
theorem B2377361 : Blo 1583990 2377361 := bstep (se 2 (by rfl) ⟨891510, by rfl⟩ : syracuseStep 2377361 = 1783021) B1783021
theorem B2377379 : Blo 1583990 2377379 := bstep (se 1 (by rfl) ⟨1783034, by rfl⟩ : syracuseStep 2377379 = 3566069) B3566069
theorem B2377409 : Blo 1583990 2377409 := bstep (se 2 (by rfl) ⟨891528, by rfl⟩ : syracuseStep 2377409 = 1783057) B1783057
theorem B2377427 : Blo 1583990 2377427 := bstep (se 1 (by rfl) ⟨1783070, by rfl⟩ : syracuseStep 2377427 = 3566141) B3566141
theorem B6768355 : Blo 1583990 6768355 := bstep (se 1 (by rfl) ⟨5076266, by rfl⟩ : syracuseStep 6768355 = 10152533) B10152533
theorem B2377457 : Blo 1583990 2377457 := bstep (se 2 (by rfl) ⟨891546, by rfl⟩ : syracuseStep 2377457 = 1783093) B1783093
theorem B2377475 : Blo 1583990 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B2377505 : Blo 1583990 2377505 := bstep (se 2 (by rfl) ⟨891564, by rfl⟩ : syracuseStep 2377505 = 1783129) B1783129
theorem B2377523 : Blo 1583990 2377523 := bstep (se 1 (by rfl) ⟨1783142, by rfl⟩ : syracuseStep 2377523 = 3566285) B3566285
theorem B3385169 : Blo 1583990 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B2377553 : Blo 1583990 2377553 := bstep (se 2 (by rfl) ⟨891582, by rfl⟩ : syracuseStep 2377553 = 1783165) B1783165
theorem B7718755 : Blo 1583990 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B2377571 : Blo 1583990 2377571 := bstep (se 1 (by rfl) ⟨1783178, by rfl⟩ : syracuseStep 2377571 = 3566357) B3566357
theorem B2377601 : Blo 1583990 2377601 := bstep (se 2 (by rfl) ⟨891600, by rfl⟩ : syracuseStep 2377601 = 1783201) B1783201
theorem B3565457 : Blo 1583990 3565457 := bstep (se 2 (by rfl) ⟨1337046, by rfl⟩ : syracuseStep 3565457 = 2674093) B2674093
theorem B2377619 : Blo 1583990 2377619 := bstep (se 1 (by rfl) ⟨1783214, by rfl⟩ : syracuseStep 2377619 = 3566429) B3566429
theorem B3565475 : Blo 1583990 3565475 := bstep (se 1 (by rfl) ⟨2674106, by rfl⟩ : syracuseStep 3565475 = 5348213) B5348213
theorem B2377649 : Blo 1583990 2377649 := bstep (se 2 (by rfl) ⟨891618, by rfl⟩ : syracuseStep 2377649 = 1783237) B1783237
theorem B2377667 : Blo 1583990 2377667 := bstep (se 1 (by rfl) ⟨1783250, by rfl⟩ : syracuseStep 2377667 = 3566501) B3566501
theorem B2377697 : Blo 1583990 2377697 := bstep (se 2 (by rfl) ⟨891636, by rfl⟩ : syracuseStep 2377697 = 1783273) B1783273
theorem B2377715 : Blo 1583990 2377715 := bstep (se 1 (by rfl) ⟨1783286, by rfl⟩ : syracuseStep 2377715 = 3566573) B3566573
theorem B3008515 : Blo 1583990 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B2377745 : Blo 1583990 2377745 := bstep (se 2 (by rfl) ⟨891654, by rfl⟩ : syracuseStep 2377745 = 1783309) B1783309
theorem B2377763 : Blo 1583990 2377763 := bstep (se 1 (by rfl) ⟨1783322, by rfl⟩ : syracuseStep 2377763 = 3566645) B3566645
theorem B2377793 : Blo 1583990 2377793 := bstep (se 2 (by rfl) ⟨891672, by rfl⟩ : syracuseStep 2377793 = 1783345) B1783345
theorem B2377811 : Blo 1583990 2377811 := bstep (se 1 (by rfl) ⟨1783358, by rfl⟩ : syracuseStep 2377811 = 3566717) B3566717
theorem B14452835 : Blo 1583990 14452835 := bstep (se 1 (by rfl) ⟨10839626, by rfl⟩ : syracuseStep 14452835 = 21679253) B21679253
theorem B2377841 : Blo 1583990 2377841 := bstep (se 2 (by rfl) ⟨891690, by rfl⟩ : syracuseStep 2377841 = 1783381) B1783381
theorem B18057329 : Blo 1583990 18057329 := bstep (se 2 (by rfl) ⟨6771498, by rfl⟩ : syracuseStep 18057329 = 13542997) B13542997
theorem B2607233 : Blo 1583990 2607233 := bstep (se 2 (by rfl) ⟨977712, by rfl⟩ : syracuseStep 2607233 = 1955425) B1955425
theorem B2377859 : Blo 1583990 2377859 := bstep (se 1 (by rfl) ⟨1783394, by rfl⟩ : syracuseStep 2377859 = 3566789) B3566789
theorem B2377889 : Blo 1583990 2377889 := bstep (se 2 (by rfl) ⟨891708, by rfl⟩ : syracuseStep 2377889 = 1783417) B1783417
theorem B3565745 : Blo 1583990 3565745 := bstep (se 2 (by rfl) ⟨1337154, by rfl⟩ : syracuseStep 3565745 = 2674309) B2674309
theorem B2377907 : Blo 1583990 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B3565763 : Blo 1583990 3565763 := bstep (se 1 (by rfl) ⟨2674322, by rfl⟩ : syracuseStep 3565763 = 5348645) B5348645
theorem B2377937 : Blo 1583990 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B2377955 : Blo 1583990 2377955 := bstep (se 1 (by rfl) ⟨1783466, by rfl⟩ : syracuseStep 2377955 = 3566933) B3566933
theorem B2377985 : Blo 1583990 2377985 := bstep (se 2 (by rfl) ⟨891744, by rfl⟩ : syracuseStep 2377985 = 1783489) B1783489
theorem B2378003 : Blo 1583990 2378003 := bstep (se 1 (by rfl) ⟨1783502, by rfl⟩ : syracuseStep 2378003 = 3567005) B3567005
theorem B2378033 : Blo 1583990 2378033 := bstep (se 2 (by rfl) ⟨891762, by rfl⟩ : syracuseStep 2378033 = 1783525) B1783525
theorem B4819267 : Blo 1583990 4819267 := bstep (se 1 (by rfl) ⟨3614450, by rfl⟩ : syracuseStep 4819267 = 7228901) B7228901
theorem B2378051 : Blo 1583990 2378051 := bstep (se 1 (by rfl) ⟨1783538, by rfl⟩ : syracuseStep 2378051 = 3567077) B3567077
theorem B2672993 : Blo 1583990 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B2378081 : Blo 1583990 2378081 := bstep (se 2 (by rfl) ⟨891780, by rfl⟩ : syracuseStep 2378081 = 1783561) B1783561
theorem B2378099 : Blo 1583990 2378099 := bstep (se 1 (by rfl) ⟨1783574, by rfl⟩ : syracuseStep 2378099 = 3567149) B3567149
theorem B2378129 : Blo 1583990 2378129 := bstep (se 2 (by rfl) ⟨891798, by rfl⟩ : syracuseStep 2378129 = 1783597) B1783597
theorem B2378147 : Blo 1583990 2378147 := bstep (se 1 (by rfl) ⟨1783610, by rfl⟩ : syracuseStep 2378147 = 3567221) B3567221
theorem B2378177 : Blo 1583990 2378177 := bstep (se 2 (by rfl) ⟨891816, by rfl⟩ : syracuseStep 2378177 = 1783633) B1783633
theorem B3008963 : Blo 1583990 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B3566033 : Blo 1583990 3566033 := bstep (se 2 (by rfl) ⟨1337262, by rfl⟩ : syracuseStep 3566033 = 2674525) B2674525
theorem B2378195 : Blo 1583990 2378195 := bstep (se 1 (by rfl) ⟨1783646, by rfl⟩ : syracuseStep 2378195 = 3567293) B3567293
theorem B2673121 : Blo 1583990 2673121 := bstep (se 2 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 2673121 = 2004841) B2004841
theorem B10717667 : Blo 1583990 10717667 := bstep (se 1 (by rfl) ⟨8038250, by rfl⟩ : syracuseStep 10717667 = 16076501) B16076501
theorem B3566051 : Blo 1583990 3566051 := bstep (se 1 (by rfl) ⟨2674538, by rfl⟩ : syracuseStep 3566051 = 5349077) B5349077
theorem B2378225 : Blo 1583990 2378225 := bstep (se 2 (by rfl) ⟨891834, by rfl⟩ : syracuseStep 2378225 = 1783669) B1783669
theorem B2673155 : Blo 1583990 2673155 := bstep (se 1 (by rfl) ⟨2004866, by rfl⟩ : syracuseStep 2673155 = 4009733) B4009733
theorem B8022563 : Blo 1583990 8022563 := bstep (se 1 (by rfl) ⟨6016922, by rfl⟩ : syracuseStep 8022563 = 12033845) B12033845
theorem B3664433 : Blo 1583990 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B3385955 : Blo 1583990 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B2673283 : Blo 1583990 2673283 := bstep (se 1 (by rfl) ⟨2004962, by rfl⟩ : syracuseStep 2673283 = 4009925) B4009925
theorem B1903235 : Blo 1583990 1903235 := bstep (se 1 (by rfl) ⟨1427426, by rfl⟩ : syracuseStep 1903235 = 2854853) B2854853
theorem B2255521 : Blo 1583990 2255521 := bstep (se 2 (by rfl) ⟨845820, by rfl⟩ : syracuseStep 2255521 = 1691641) B1691641
theorem B1903331 : Blo 1583990 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B3009251 : Blo 1583990 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B3566321 : Blo 1583990 3566321 := bstep (se 2 (by rfl) ⟨1337370, by rfl⟩ : syracuseStep 3566321 = 2674741) B2674741
theorem B2255617 : Blo 1583990 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B3566339 : Blo 1583990 3566339 := bstep (se 1 (by rfl) ⟨2674754, by rfl⟩ : syracuseStep 3566339 = 5349509) B5349509
theorem B2673425 : Blo 1583990 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B1584003 : Blo 1583990 1584003 := bstep (se 1 (by rfl) ⟨1188002, by rfl⟩ : syracuseStep 1584003 = 2376005) B2376005
theorem B13544333 : Blo 1583990 13544333 := bstep (se 3 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 13544333 = 5079125) B5079125
theorem B2673553 : Blo 1583990 2673553 := bstep (se 2 (by rfl) ⟨1002582, by rfl⟩ : syracuseStep 2673553 = 2005165) B2005165
theorem B1584019 : Blo 1583990 1584019 := bstep (se 1 (by rfl) ⟨1188014, by rfl⟩ : syracuseStep 1584019 = 2376029) B2376029
theorem B1584035 : Blo 1583990 1584035 := bstep (se 1 (by rfl) ⟨1188026, by rfl⟩ : syracuseStep 1584035 = 2376053) B2376053
theorem B6769585 : Blo 1583990 6769585 := bstep (se 2 (by rfl) ⟨2538594, by rfl⟩ : syracuseStep 6769585 = 5077189) B5077189
theorem B1584051 : Blo 1583990 1584051 := bstep (se 1 (by rfl) ⟨1188038, by rfl⟩ : syracuseStep 1584051 = 2376077) B2376077
theorem B2673587 : Blo 1583990 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B1584067 : Blo 1583990 1584067 := bstep (se 1 (by rfl) ⟨1188050, by rfl⟩ : syracuseStep 1584067 = 2376101) B2376101
theorem B1584083 : Blo 1583990 1584083 := bstep (se 1 (by rfl) ⟨1188062, by rfl⟩ : syracuseStep 1584083 = 2376125) B2376125
theorem B1584099 : Blo 1583990 1584099 := bstep (se 1 (by rfl) ⟨1188074, by rfl⟩ : syracuseStep 1584099 = 2376149) B2376149
theorem B1584115 : Blo 1583990 1584115 := bstep (se 1 (by rfl) ⟨1188086, by rfl⟩ : syracuseStep 1584115 = 2376173) B2376173
theorem B1584131 : Blo 1583990 1584131 := bstep (se 1 (by rfl) ⟨1188098, by rfl⟩ : syracuseStep 1584131 = 2376197) B2376197
theorem B3566609 : Blo 1583990 3566609 := bstep (se 2 (by rfl) ⟨1337478, by rfl⟩ : syracuseStep 3566609 = 2674957) B2674957
theorem B1584147 : Blo 1583990 1584147 := bstep (se 1 (by rfl) ⟨1188110, by rfl⟩ : syracuseStep 1584147 = 2376221) B2376221
theorem B1584163 : Blo 1583990 1584163 := bstep (se 1 (by rfl) ⟨1188122, by rfl⟩ : syracuseStep 1584163 = 2376245) B2376245
theorem B3566627 : Blo 1583990 3566627 := bstep (se 1 (by rfl) ⟨2674970, by rfl⟩ : syracuseStep 3566627 = 5349941) B5349941
theorem B1584179 : Blo 1583990 1584179 := bstep (se 1 (by rfl) ⟨1188134, by rfl⟩ : syracuseStep 1584179 = 2376269) B2376269
theorem B2673715 : Blo 1583990 2673715 := bstep (se 1 (by rfl) ⟨2005286, by rfl⟩ : syracuseStep 2673715 = 4010573) B4010573
theorem B1584195 : Blo 1583990 1584195 := bstep (se 1 (by rfl) ⟨1188146, by rfl⟩ : syracuseStep 1584195 = 2376293) B2376293
theorem B1584211 : Blo 1583990 1584211 := bstep (se 1 (by rfl) ⟨1188158, by rfl⟩ : syracuseStep 1584211 = 2376317) B2376317
theorem B1584227 : Blo 1583990 1584227 := bstep (se 1 (by rfl) ⟨1188170, by rfl⟩ : syracuseStep 1584227 = 2376341) B2376341
theorem B1584243 : Blo 1583990 1584243 := bstep (se 1 (by rfl) ⟨1188182, by rfl⟩ : syracuseStep 1584243 = 2376365) B2376365
theorem B1584259 : Blo 1583990 1584259 := bstep (se 1 (by rfl) ⟨1188194, by rfl⟩ : syracuseStep 1584259 = 2376389) B2376389
theorem B1584275 : Blo 1583990 1584275 := bstep (se 1 (by rfl) ⟨1188206, by rfl⟩ : syracuseStep 1584275 = 2376413) B2376413
theorem B1584291 : Blo 1583990 1584291 := bstep (se 1 (by rfl) ⟨1188218, by rfl⟩ : syracuseStep 1584291 = 2376437) B2376437
theorem B1584307 : Blo 1583990 1584307 := bstep (se 1 (by rfl) ⟨1188230, by rfl⟩ : syracuseStep 1584307 = 2376461) B2376461
theorem B2673857 : Blo 1583990 2673857 := bstep (se 2 (by rfl) ⟨1002696, by rfl⟩ : syracuseStep 2673857 = 2005393) B2005393
theorem B1584323 : Blo 1583990 1584323 := bstep (se 1 (by rfl) ⟨1188242, by rfl⟩ : syracuseStep 1584323 = 2376485) B2376485
theorem B1584339 : Blo 1583990 1584339 := bstep (se 1 (by rfl) ⟨1188254, by rfl⟩ : syracuseStep 1584339 = 2376509) B2376509
theorem B1584355 : Blo 1583990 1584355 := bstep (se 1 (by rfl) ⟨1188266, by rfl⟩ : syracuseStep 1584355 = 2376533) B2376533
theorem B2256113 : Blo 1583990 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B1584371 : Blo 1583990 1584371 := bstep (se 1 (by rfl) ⟨1188278, by rfl⟩ : syracuseStep 1584371 = 2376557) B2376557
theorem B1584387 : Blo 1583990 1584387 := bstep (se 1 (by rfl) ⟨1188290, by rfl⟩ : syracuseStep 1584387 = 2376581) B2376581
theorem B1584403 : Blo 1583990 1584403 := bstep (se 1 (by rfl) ⟨1188302, by rfl⟩ : syracuseStep 1584403 = 2376605) B2376605
theorem B1584419 : Blo 1583990 1584419 := bstep (se 1 (by rfl) ⟨1188314, by rfl⟩ : syracuseStep 1584419 = 2376629) B2376629
theorem B3566897 : Blo 1583990 3566897 := bstep (se 2 (by rfl) ⟨1337586, by rfl⟩ : syracuseStep 3566897 = 2675173) B2675173
theorem B1584435 : Blo 1583990 1584435 := bstep (se 1 (by rfl) ⟨1188326, by rfl⟩ : syracuseStep 1584435 = 2376653) B2376653
theorem B2673985 : Blo 1583990 2673985 := bstep (se 2 (by rfl) ⟨1002744, by rfl⟩ : syracuseStep 2673985 = 2005489) B2005489
theorem B1584451 : Blo 1583990 1584451 := bstep (se 1 (by rfl) ⟨1188338, by rfl⟩ : syracuseStep 1584451 = 2376677) B2376677
theorem B3566915 : Blo 1583990 3566915 := bstep (se 1 (by rfl) ⟨2675186, by rfl⟩ : syracuseStep 3566915 = 5350373) B5350373
theorem B8023373 : Blo 1583990 8023373 := bstep (se 3 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 8023373 = 3008765) B3008765
theorem B1584467 : Blo 1583990 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B1584483 : Blo 1583990 1584483 := bstep (se 1 (by rfl) ⟨1188362, by rfl⟩ : syracuseStep 1584483 = 2376725) B2376725
theorem B2674019 : Blo 1583990 2674019 := bstep (se 1 (by rfl) ⟨2005514, by rfl⟩ : syracuseStep 2674019 = 4011029) B4011029
theorem B1584499 : Blo 1583990 1584499 := bstep (se 1 (by rfl) ⟨1188374, by rfl⟩ : syracuseStep 1584499 = 2376749) B2376749
theorem B1584515 : Blo 1583990 1584515 := bstep (se 1 (by rfl) ⟨1188386, by rfl⟩ : syracuseStep 1584515 = 2376773) B2376773
theorem B1584531 : Blo 1583990 1584531 := bstep (se 1 (by rfl) ⟨1188398, by rfl⟩ : syracuseStep 1584531 = 2376797) B2376797
theorem B1584547 : Blo 1583990 1584547 := bstep (se 1 (by rfl) ⟨1188410, by rfl⟩ : syracuseStep 1584547 = 2376821) B2376821
theorem B1584563 : Blo 1583990 1584563 := bstep (se 1 (by rfl) ⟨1188422, by rfl⟩ : syracuseStep 1584563 = 2376845) B2376845
theorem B1584579 : Blo 1583990 1584579 := bstep (se 1 (by rfl) ⟨1188434, by rfl⟩ : syracuseStep 1584579 = 2376869) B2376869
theorem B1584595 : Blo 1583990 1584595 := bstep (se 1 (by rfl) ⟨1188446, by rfl⟩ : syracuseStep 1584595 = 2376893) B2376893
theorem B1584611 : Blo 1583990 1584611 := bstep (se 1 (by rfl) ⟨1188458, by rfl⟩ : syracuseStep 1584611 = 2376917) B2376917
theorem B2674147 : Blo 1583990 2674147 := bstep (se 1 (by rfl) ⟨2005610, by rfl⟩ : syracuseStep 2674147 = 4011221) B4011221
theorem B10153457 : Blo 1583990 10153457 := bstep (se 2 (by rfl) ⟨3807546, by rfl⟩ : syracuseStep 10153457 = 7615093) B7615093
theorem B1584627 : Blo 1583990 1584627 := bstep (se 1 (by rfl) ⟨1188470, by rfl⟩ : syracuseStep 1584627 = 2376941) B2376941
theorem B1584643 : Blo 1583990 1584643 := bstep (se 1 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 1584643 = 2376965) B2376965
theorem B1584659 : Blo 1583990 1584659 := bstep (se 1 (by rfl) ⟨1188494, by rfl⟩ : syracuseStep 1584659 = 2376989) B2376989
theorem B1584675 : Blo 1583990 1584675 := bstep (se 1 (by rfl) ⟨1188506, by rfl⟩ : syracuseStep 1584675 = 2377013) B2377013
theorem B1584691 : Blo 1583990 1584691 := bstep (se 1 (by rfl) ⟨1188518, by rfl⟩ : syracuseStep 1584691 = 2377037) B2377037
theorem B1584707 : Blo 1583990 1584707 := bstep (se 1 (by rfl) ⟨1188530, by rfl⟩ : syracuseStep 1584707 = 2377061) B2377061
theorem B6016589 : Blo 1583990 6016589 := bstep (se 3 (by rfl) ⟨1128110, by rfl⟩ : syracuseStep 6016589 = 2256221) B2256221
theorem B3567185 : Blo 1583990 3567185 := bstep (se 2 (by rfl) ⟨1337694, by rfl⟩ : syracuseStep 3567185 = 2675389) B2675389
theorem B1584723 : Blo 1583990 1584723 := bstep (se 1 (by rfl) ⟨1188542, by rfl⟩ : syracuseStep 1584723 = 2377085) B2377085
theorem B4009571 : Blo 1583990 4009571 := bstep (se 1 (by rfl) ⟨3007178, by rfl⟩ : syracuseStep 4009571 = 6014357) B6014357
theorem B1584739 : Blo 1583990 1584739 := bstep (se 1 (by rfl) ⟨1188554, by rfl⟩ : syracuseStep 1584739 = 2377109) B2377109
theorem B3567203 : Blo 1583990 3567203 := bstep (se 1 (by rfl) ⟨2675402, by rfl⟩ : syracuseStep 3567203 = 5350805) B5350805
theorem B2674289 : Blo 1583990 2674289 := bstep (se 2 (by rfl) ⟨1002858, by rfl⟩ : syracuseStep 2674289 = 2005717) B2005717
theorem B1584755 : Blo 1583990 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B1584771 : Blo 1583990 1584771 := bstep (se 1 (by rfl) ⟨1188578, by rfl⟩ : syracuseStep 1584771 = 2377157) B2377157
theorem B1584787 : Blo 1583990 1584787 := bstep (se 1 (by rfl) ⟨1188590, by rfl⟩ : syracuseStep 1584787 = 2377181) B2377181
theorem B1584803 : Blo 1583990 1584803 := bstep (se 1 (by rfl) ⟨1188602, by rfl⟩ : syracuseStep 1584803 = 2377205) B2377205
theorem B1584819 : Blo 1583990 1584819 := bstep (se 1 (by rfl) ⟨1188614, by rfl⟩ : syracuseStep 1584819 = 2377229) B2377229
theorem B1584835 : Blo 1583990 1584835 := bstep (se 1 (by rfl) ⟨1188626, by rfl⟩ : syracuseStep 1584835 = 2377253) B2377253
theorem B1584851 : Blo 1583990 1584851 := bstep (se 1 (by rfl) ⟨1188638, by rfl⟩ : syracuseStep 1584851 = 2377277) B2377277
theorem B1584867 : Blo 1583990 1584867 := bstep (se 1 (by rfl) ⟨1188650, by rfl⟩ : syracuseStep 1584867 = 2377301) B2377301
theorem B2674417 : Blo 1583990 2674417 := bstep (se 2 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 2674417 = 2005813) B2005813
theorem B1584883 : Blo 1583990 1584883 := bstep (se 1 (by rfl) ⟨1188662, by rfl⟩ : syracuseStep 1584883 = 2377325) B2377325
theorem B1584899 : Blo 1583990 1584899 := bstep (se 1 (by rfl) ⟨1188674, by rfl⟩ : syracuseStep 1584899 = 2377349) B2377349
theorem B2674451 : Blo 1583990 2674451 := bstep (se 1 (by rfl) ⟨2005838, by rfl⟩ : syracuseStep 2674451 = 4011677) B4011677
theorem B1584915 : Blo 1583990 1584915 := bstep (se 1 (by rfl) ⟨1188686, by rfl⟩ : syracuseStep 1584915 = 2377373) B2377373
theorem B4009763 : Blo 1583990 4009763 := bstep (se 1 (by rfl) ⟨3007322, by rfl⟩ : syracuseStep 4009763 = 6014645) B6014645
theorem B1584931 : Blo 1583990 1584931 := bstep (se 1 (by rfl) ⟨1188698, by rfl⟩ : syracuseStep 1584931 = 2377397) B2377397
theorem B1584947 : Blo 1583990 1584947 := bstep (se 1 (by rfl) ⟨1188710, by rfl⟩ : syracuseStep 1584947 = 2377421) B2377421
theorem B1584963 : Blo 1583990 1584963 := bstep (se 1 (by rfl) ⟨1188722, by rfl⟩ : syracuseStep 1584963 = 2377445) B2377445
theorem B1584979 : Blo 1583990 1584979 := bstep (se 1 (by rfl) ⟨1188734, by rfl⟩ : syracuseStep 1584979 = 2377469) B2377469
theorem B1584995 : Blo 1583990 1584995 := bstep (se 1 (by rfl) ⟨1188746, by rfl⟩ : syracuseStep 1584995 = 2377493) B2377493
theorem B1585011 : Blo 1583990 1585011 := bstep (se 1 (by rfl) ⟨1188758, by rfl⟩ : syracuseStep 1585011 = 2377517) B2377517
theorem B1585027 : Blo 1583990 1585027 := bstep (se 1 (by rfl) ⟨1188770, by rfl⟩ : syracuseStep 1585027 = 2377541) B2377541
theorem B2674579 : Blo 1583990 2674579 := bstep (se 1 (by rfl) ⟨2005934, by rfl⟩ : syracuseStep 2674579 = 4011869) B4011869
theorem B1585043 : Blo 1583990 1585043 := bstep (se 1 (by rfl) ⟨1188782, by rfl⟩ : syracuseStep 1585043 = 2377565) B2377565
theorem B1585059 : Blo 1583990 1585059 := bstep (se 1 (by rfl) ⟨1188794, by rfl⟩ : syracuseStep 1585059 = 2377589) B2377589
theorem B1585075 : Blo 1583990 1585075 := bstep (se 1 (by rfl) ⟨1188806, by rfl⟩ : syracuseStep 1585075 = 2377613) B2377613
theorem B5074883 : Blo 1583990 5074883 := bstep (se 1 (by rfl) ⟨3806162, by rfl⟩ : syracuseStep 5074883 = 7612325) B7612325
theorem B1585091 : Blo 1583990 1585091 := bstep (se 1 (by rfl) ⟨1188818, by rfl⟩ : syracuseStep 1585091 = 2377637) B2377637
theorem B5361617 : Blo 1583990 5361617 := bstep (se 2 (by rfl) ⟨2010606, by rfl⟩ : syracuseStep 5361617 = 4021213) B4021213
theorem B1585107 : Blo 1583990 1585107 := bstep (se 1 (by rfl) ⟨1188830, by rfl⟩ : syracuseStep 1585107 = 2377661) B2377661
theorem B1585123 : Blo 1583990 1585123 := bstep (se 1 (by rfl) ⟨1188842, by rfl⟩ : syracuseStep 1585123 = 2377685) B2377685
theorem B1585139 : Blo 1583990 1585139 := bstep (se 1 (by rfl) ⟨1188854, by rfl⟩ : syracuseStep 1585139 = 2377709) B2377709
theorem B1585155 : Blo 1583990 1585155 := bstep (se 1 (by rfl) ⟨1188866, by rfl⟩ : syracuseStep 1585155 = 2377733) B2377733
theorem B1585171 : Blo 1583990 1585171 := bstep (se 1 (by rfl) ⟨1188878, by rfl⟩ : syracuseStep 1585171 = 2377757) B2377757
theorem B2674721 : Blo 1583990 2674721 := bstep (se 2 (by rfl) ⟨1003020, by rfl⟩ : syracuseStep 2674721 = 2006041) B2006041
theorem B1585187 : Blo 1583990 1585187 := bstep (se 1 (by rfl) ⟨1188890, by rfl⟩ : syracuseStep 1585187 = 2377781) B2377781
theorem B1585203 : Blo 1583990 1585203 := bstep (se 1 (by rfl) ⟨1188902, by rfl⟩ : syracuseStep 1585203 = 2377805) B2377805
theorem B1585219 : Blo 1583990 1585219 := bstep (se 1 (by rfl) ⟨1188914, by rfl⟩ : syracuseStep 1585219 = 2377829) B2377829
theorem B2256979 : Blo 1583990 2256979 := bstep (se 1 (by rfl) ⟨1692734, by rfl⟩ : syracuseStep 2256979 = 3385469) B3385469
theorem B1585235 : Blo 1583990 1585235 := bstep (se 1 (by rfl) ⟨1188926, by rfl⟩ : syracuseStep 1585235 = 2377853) B2377853
theorem B1585251 : Blo 1583990 1585251 := bstep (se 1 (by rfl) ⟨1188938, by rfl⟩ : syracuseStep 1585251 = 2377877) B2377877
theorem B1585267 : Blo 1583990 1585267 := bstep (se 1 (by rfl) ⟨1188950, by rfl⟩ : syracuseStep 1585267 = 2377901) B2377901
theorem B1585283 : Blo 1583990 1585283 := bstep (se 1 (by rfl) ⟨1188962, by rfl⟩ : syracuseStep 1585283 = 2377925) B2377925
theorem B1585299 : Blo 1583990 1585299 := bstep (se 1 (by rfl) ⟨1188974, by rfl⟩ : syracuseStep 1585299 = 2377949) B2377949
theorem B2674849 : Blo 1583990 2674849 := bstep (se 2 (by rfl) ⟨1003068, by rfl⟩ : syracuseStep 2674849 = 2006137) B2006137
theorem B1585315 : Blo 1583990 1585315 := bstep (se 1 (by rfl) ⟨1188986, by rfl⟩ : syracuseStep 1585315 = 2377973) B2377973
theorem B2257075 : Blo 1583990 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B1585331 : Blo 1583990 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B2674883 : Blo 1583990 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B1585347 : Blo 1583990 1585347 := bstep (se 1 (by rfl) ⟨1189010, by rfl⟩ : syracuseStep 1585347 = 2378021) B2378021
theorem B1585363 : Blo 1583990 1585363 := bstep (se 1 (by rfl) ⟨1189022, by rfl⟩ : syracuseStep 1585363 = 2378045) B2378045
theorem B1585379 : Blo 1583990 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B1585395 : Blo 1583990 1585395 := bstep (se 1 (by rfl) ⟨1189046, by rfl⟩ : syracuseStep 1585395 = 2378093) B2378093
theorem B1585411 : Blo 1583990 1585411 := bstep (se 1 (by rfl) ⟨1189058, by rfl⟩ : syracuseStep 1585411 = 2378117) B2378117
theorem B1585427 : Blo 1583990 1585427 := bstep (se 1 (by rfl) ⟨1189070, by rfl⟩ : syracuseStep 1585427 = 2378141) B2378141
theorem B2142497 : Blo 1583990 2142497 := bstep (se 2 (by rfl) ⟨803436, by rfl⟩ : syracuseStep 2142497 = 1606873) B1606873
theorem B1585443 : Blo 1583990 1585443 := bstep (se 1 (by rfl) ⟨1189082, by rfl⟩ : syracuseStep 1585443 = 2378165) B2378165
theorem B1782067 : Blo 1583990 1782067 := bstep (se 1 (by rfl) ⟨1336550, by rfl⟩ : syracuseStep 1782067 = 2673101) B2673101
theorem B1585459 : Blo 1583990 1585459 := bstep (se 1 (by rfl) ⟨1189094, by rfl⟩ : syracuseStep 1585459 = 2378189) B2378189
theorem B2675011 : Blo 1583990 2675011 := bstep (se 1 (by rfl) ⟨2006258, by rfl⟩ : syracuseStep 2675011 = 4012517) B4012517
theorem B1585475 : Blo 1583990 1585475 := bstep (se 1 (by rfl) ⟨1189106, by rfl⟩ : syracuseStep 1585475 = 2378213) B2378213
theorem B19272005 : Blo 1583990 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B1782211 : Blo 1583990 1782211 := bstep (se 1 (by rfl) ⟨1336658, by rfl⟩ : syracuseStep 1782211 = 2673317) B2673317
theorem B2675153 : Blo 1583990 2675153 := bstep (se 2 (by rfl) ⟨1003182, by rfl⟩ : syracuseStep 2675153 = 2006365) B2006365
theorem B5075473 : Blo 1583990 5075473 := bstep (se 2 (by rfl) ⟨1903302, by rfl⟩ : syracuseStep 5075473 = 3806605) B3806605
theorem B2675281 : Blo 1583990 2675281 := bstep (se 2 (by rfl) ⟨1003230, by rfl⟩ : syracuseStep 2675281 = 2006461) B2006461
theorem B1782355 : Blo 1583990 1782355 := bstep (se 1 (by rfl) ⟨1336766, by rfl⟩ : syracuseStep 1782355 = 2673533) B2673533
theorem B9638513 : Blo 1583990 9638513 := bstep (se 2 (by rfl) ⟨3614442, by rfl⟩ : syracuseStep 9638513 = 7228885) B7228885
theorem B2675315 : Blo 1583990 2675315 := bstep (se 1 (by rfl) ⟨2006486, by rfl⟩ : syracuseStep 2675315 = 4012973) B4012973
theorem B6427313 : Blo 1583990 6427313 := bstep (se 2 (by rfl) ⟨2410242, by rfl⟩ : syracuseStep 6427313 = 4820485) B4820485
theorem B4010705 : Blo 1583990 4010705 := bstep (se 2 (by rfl) ⟨1504014, by rfl⟩ : syracuseStep 4010705 = 3008029) B3008029
theorem B1692371 : Blo 1583990 1692371 := bstep (se 1 (by rfl) ⟨1269278, by rfl⟩ : syracuseStep 1692371 = 2538557) B2538557
theorem B1782499 : Blo 1583990 1782499 := bstep (se 1 (by rfl) ⟨1336874, by rfl⟩ : syracuseStep 1782499 = 2673749) B2673749
theorem B2675443 : Blo 1583990 2675443 := bstep (se 1 (by rfl) ⟨2006582, by rfl⟩ : syracuseStep 2675443 = 4013165) B4013165
theorem B4010755 : Blo 1583990 4010755 := bstep (se 1 (by rfl) ⟨3008066, by rfl⟩ : syracuseStep 4010755 = 6016133) B6016133
theorem B1692499 : Blo 1583990 1692499 := bstep (se 1 (by rfl) ⟨1269374, by rfl⟩ : syracuseStep 1692499 = 2538749) B2538749
theorem B5346161 : Blo 1583990 5346161 := bstep (se 2 (by rfl) ⟨2004810, by rfl⟩ : syracuseStep 5346161 = 4009621) B4009621
theorem B1782643 : Blo 1583990 1782643 := bstep (se 1 (by rfl) ⟨1336982, by rfl⟩ : syracuseStep 1782643 = 2673965) B2673965
theorem B1930115 : Blo 1583990 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B4010897 : Blo 1583990 4010897 := bstep (se 2 (by rfl) ⟨1504086, by rfl⟩ : syracuseStep 4010897 = 3008173) B3008173
theorem B1782787 : Blo 1583990 1782787 := bstep (se 1 (by rfl) ⟨1337090, by rfl⟩ : syracuseStep 1782787 = 2674181) B2674181
theorem B1782931 : Blo 1583990 1782931 := bstep (se 1 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 1782931 = 2674397) B2674397
theorem B4510961 : Blo 1583990 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B1783075 : Blo 1583990 1783075 := bstep (se 1 (by rfl) ⟨1337306, by rfl⟩ : syracuseStep 1783075 = 2674613) B2674613
theorem B27088181 : Blo 1583990 27088181 := bstep (se 5 (by rfl) ⟨1269758, by rfl⟩ : syracuseStep 27088181 = 2539517) B2539517
theorem B2856323 : Blo 1583990 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B5346701 : Blo 1583990 5346701 := bstep (se 3 (by rfl) ⟨1002506, by rfl⟩ : syracuseStep 5346701 = 2005013) B2005013
theorem B1783219 : Blo 1583990 1783219 := bstep (se 1 (by rfl) ⟨1337414, by rfl⟩ : syracuseStep 1783219 = 2674829) B2674829
theorem B5346755 : Blo 1583990 5346755 := bstep (se 1 (by rfl) ⟨4010066, by rfl⟩ : syracuseStep 5346755 = 8020133) B8020133
theorem B15226339 : Blo 1583990 15226339 := bstep (se 1 (by rfl) ⟨11419754, by rfl⟩ : syracuseStep 15226339 = 22839509) B22839509
theorem B1783363 : Blo 1583990 1783363 := bstep (se 1 (by rfl) ⟨1337522, by rfl⟩ : syracuseStep 1783363 = 2675045) B2675045
theorem B2856547 : Blo 1583990 2856547 := bstep (se 1 (by rfl) ⟨2142410, by rfl⟩ : syracuseStep 2856547 = 4284821) B4284821
theorem B5347025 : Blo 1583990 5347025 := bstep (se 2 (by rfl) ⟨2005134, by rfl⟩ : syracuseStep 5347025 = 4010269) B4010269
theorem B1783507 : Blo 1583990 1783507 := bstep (se 1 (by rfl) ⟨1337630, by rfl⟩ : syracuseStep 1783507 = 2675261) B2675261
theorem B1783651 : Blo 1583990 1783651 := bstep (se 1 (by rfl) ⟨1337738, by rfl⟩ : syracuseStep 1783651 = 2675477) B2675477
theorem B4011889 : Blo 1583990 4011889 := bstep (se 2 (by rfl) ⟨1504458, by rfl⟩ : syracuseStep 4011889 = 3008917) B3008917
theorem B2004851 : Blo 1583990 2004851 := bstep (se 1 (by rfl) ⟨1503638, by rfl⟩ : syracuseStep 2004851 = 3007277) B3007277
theorem B9025613 : Blo 1583990 9025613 := bstep (se 3 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 9025613 = 3384605) B3384605
theorem B7231601 : Blo 1583990 7231601 := bstep (se 2 (by rfl) ⟨2711850, by rfl⟩ : syracuseStep 7231601 = 5423701) B5423701
theorem B4012163 : Blo 1583990 4012163 := bstep (se 1 (by rfl) ⟨3009122, by rfl⟩ : syracuseStep 4012163 = 6018245) B6018245
theorem B4282541 : Blo 1583990 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B8026289 : Blo 1583990 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B5347565 : Blo 1583990 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B5347619 : Blo 1583990 5347619 := bstep (se 1 (by rfl) ⟨4010714, by rfl⟩ : syracuseStep 5347619 = 8021429) B8021429
theorem B4012355 : Blo 1583990 4012355 := bstep (se 1 (by rfl) ⟨3009266, by rfl⟩ : syracuseStep 4012355 = 6018533) B6018533
theorem B6019505 : Blo 1583990 6019505 := bstep (se 2 (by rfl) ⟨2257314, by rfl⟩ : syracuseStep 6019505 = 4514629) B4514629
theorem B20576693 : Blo 1583990 20576693 := bstep (se 5 (by rfl) ⟨964532, by rfl⟩ : syracuseStep 20576693 = 1929065) B1929065
theorem B4282865 : Blo 1583990 4282865 := bstep (se 2 (by rfl) ⟨1606074, by rfl⟩ : syracuseStep 4282865 = 3212149) B3212149
theorem B5347889 : Blo 1583990 5347889 := bstep (se 2 (by rfl) ⟨2005458, by rfl⟩ : syracuseStep 5347889 = 4010917) B4010917
theorem B2005555 : Blo 1583990 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B3431011 : Blo 1583990 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B2005651 : Blo 1583990 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B4512419 : Blo 1583990 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B2538211 : Blo 1583990 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B8682353 : Blo 1583990 8682353 := bstep (se 2 (by rfl) ⟨3255882, by rfl⟩ : syracuseStep 8682353 = 6511765) B6511765
theorem B30464909 : Blo 1583990 30464909 := bstep (se 3 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 30464909 = 11424341) B11424341
theorem B2538467 : Blo 1583990 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B2644993 : Blo 1583990 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B4283437 : Blo 1583990 4283437 := bstep (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) B1606289
theorem B5348429 : Blo 1583990 5348429 := bstep (se 3 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 5348429 = 2005661) B2005661
theorem B5348483 : Blo 1583990 5348483 := bstep (se 1 (by rfl) ⟨4011362, by rfl⟩ : syracuseStep 5348483 = 8022725) B8022725
theorem B2006147 : Blo 1583990 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B2538659 : Blo 1583990 2538659 := bstep (se 1 (by rfl) ⟨1903994, by rfl⟩ : syracuseStep 2538659 = 3807989) B3807989
theorem B3808451 : Blo 1583990 3808451 := bstep (se 1 (by rfl) ⟨2856338, by rfl⟩ : syracuseStep 3808451 = 5712677) B5712677
theorem B18054413 : Blo 1583990 18054413 := bstep (se 3 (by rfl) ⟨3385202, by rfl⟩ : syracuseStep 18054413 = 6770405) B6770405
theorem B5078317 : Blo 1583990 5078317 := bstep (se 3 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 5078317 = 1904369) B1904369
theorem B5348753 : Blo 1583990 5348753 := bstep (se 2 (by rfl) ⟨2005782, by rfl⟩ : syracuseStep 5348753 = 4011565) B4011565
theorem B3431825 : Blo 1583990 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B4513229 : Blo 1583990 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B12361187 : Blo 1583990 12361187 := bstep (se 1 (by rfl) ⟨9270890, by rfl⟩ : syracuseStep 12361187 = 18541781) B18541781
theorem B333700661 : Blo 1583990 333700661 := bstep (se 5 (by rfl) ⟨15642218, by rfl⟩ : syracuseStep 333700661 = 31284437) B31284437
theorem B17129029 : Blo 1583990 17129029 := bstep (se 4 (by rfl) ⟨1605846, by rfl⟩ : syracuseStep 17129029 = 3211693) B3211693
theorem B4513421 : Blo 1583990 4513421 := bstep (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) B1692533
theorem B9641699 : Blo 1583990 9641699 := bstep (se 1 (by rfl) ⟨7231274, by rfl⟩ : syracuseStep 9641699 = 14462549) B14462549
theorem B14450501 : Blo 1583990 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B2981713 : Blo 1583990 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3809123 : Blo 1583990 3809123 := bstep (se 1 (by rfl) ⟨2856842, by rfl⟩ : syracuseStep 3809123 = 5713685) B5713685
theorem B5349293 : Blo 1583990 5349293 := bstep (se 3 (by rfl) ⟨1002992, by rfl⟩ : syracuseStep 5349293 = 2005985) B2005985
theorem B2539441 : Blo 1583990 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B5349347 : Blo 1583990 5349347 := bstep (se 1 (by rfl) ⟨4012010, by rfl⟩ : syracuseStep 5349347 = 8024021) B8024021
theorem B14106629 : Blo 1583990 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B2539595 : Blo 1583990 2539595 := bstep (se 1 (by rfl) ⟨1904696, by rfl⟩ : syracuseStep 2539595 = 3809393) B3809393
theorem B1605835 : Blo 1583990 1605835 := bstep (se 1 (by rfl) ⟨1204376, by rfl⟩ : syracuseStep 1605835 = 2408753) B2408753
theorem B2376011 : Blo 1583990 2376011 := bstep (se 1 (by rfl) ⟨1782008, by rfl⟩ : syracuseStep 2376011 = 3564017) B3564017
theorem B2376023 : Blo 1583990 2376023 := bstep (se 1 (by rfl) ⟨1782017, by rfl⟩ : syracuseStep 2376023 = 3564035) B3564035
theorem B5349725 : Blo 1583990 5349725 := bstep (se 3 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 5349725 = 2006147) B2006147
theorem B2376089 : Blo 1583990 2376089 := bstep (se 2 (by rfl) ⟨891033, by rfl⟩ : syracuseStep 2376089 = 1782067) B1782067
theorem B4284875 : Blo 1583990 4284875 := bstep (se 1 (by rfl) ⟨3213656, by rfl⟩ : syracuseStep 4284875 = 6427313) B6427313
theorem B2376203 : Blo 1583990 2376203 := bstep (se 1 (by rfl) ⟨1782152, by rfl⟩ : syracuseStep 2376203 = 3564305) B3564305
theorem B2376215 : Blo 1583990 2376215 := bstep (se 1 (by rfl) ⟨1782161, by rfl⟩ : syracuseStep 2376215 = 3564323) B3564323
theorem B3564107 : Blo 1583990 3564107 := bstep (se 1 (by rfl) ⟨2673080, by rfl⟩ : syracuseStep 3564107 = 5346161) B5346161
theorem B2376281 : Blo 1583990 2376281 := bstep (se 2 (by rfl) ⟨891105, by rfl⟩ : syracuseStep 2376281 = 1782211) B1782211
theorem B3564161 : Blo 1583990 3564161 := bstep (se 2 (by rfl) ⟨1336560, by rfl⟩ : syracuseStep 3564161 = 2673121) B2673121
theorem B2785931 : Blo 1583990 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B6767297 : Blo 1583990 6767297 := bstep (se 2 (by rfl) ⟨2537736, by rfl⟩ : syracuseStep 6767297 = 5075473) B5075473
theorem B2376395 : Blo 1583990 2376395 := bstep (se 1 (by rfl) ⟨1782296, by rfl⟩ : syracuseStep 2376395 = 3564593) B3564593
theorem B2376407 : Blo 1583990 2376407 := bstep (se 1 (by rfl) ⟨1782305, by rfl⟩ : syracuseStep 2376407 = 3564611) B3564611
theorem B2376473 : Blo 1583990 2376473 := bstep (se 2 (by rfl) ⟨891177, by rfl⟩ : syracuseStep 2376473 = 1782355) B1782355
theorem B8020781 : Blo 1583990 8020781 := bstep (se 3 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 8020781 = 3007793) B3007793
theorem B3007307 : Blo 1583990 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B3564377 : Blo 1583990 3564377 := bstep (se 2 (by rfl) ⟨1336641, by rfl⟩ : syracuseStep 3564377 = 2673283) B2673283
theorem B3007361 : Blo 1583990 3007361 := bstep (se 2 (by rfl) ⟨1127760, by rfl⟩ : syracuseStep 3007361 = 2255521) B2255521
theorem B2376587 : Blo 1583990 2376587 := bstep (se 1 (by rfl) ⟨1782440, by rfl⟩ : syracuseStep 2376587 = 3564881) B3564881
theorem B2376599 : Blo 1583990 2376599 := bstep (se 1 (by rfl) ⟨1782449, by rfl⟩ : syracuseStep 2376599 = 3564899) B3564899
theorem B3564467 : Blo 1583990 3564467 := bstep (se 1 (by rfl) ⟨2673350, by rfl⟩ : syracuseStep 3564467 = 5346701) B5346701
theorem B3564503 : Blo 1583990 3564503 := bstep (se 1 (by rfl) ⟨2673377, by rfl⟩ : syracuseStep 3564503 = 5346755) B5346755
theorem B2376665 : Blo 1583990 2376665 := bstep (se 2 (by rfl) ⟨891249, by rfl⟩ : syracuseStep 2376665 = 1782499) B1782499
theorem B3384281 : Blo 1583990 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B2376779 : Blo 1583990 2376779 := bstep (se 1 (by rfl) ⟨1782584, by rfl⟩ : syracuseStep 2376779 = 3565169) B3565169
theorem B2376791 : Blo 1583990 2376791 := bstep (se 1 (by rfl) ⟨1782593, by rfl⟩ : syracuseStep 2376791 = 3565187) B3565187
theorem B3564683 : Blo 1583990 3564683 := bstep (se 1 (by rfl) ⟨2673512, by rfl⟩ : syracuseStep 3564683 = 5347025) B5347025
theorem B2376857 : Blo 1583990 2376857 := bstep (se 2 (by rfl) ⟨891321, by rfl⟩ : syracuseStep 2376857 = 1782643) B1782643
theorem B3564737 : Blo 1583990 3564737 := bstep (se 2 (by rfl) ⟨1336776, by rfl⟩ : syracuseStep 3564737 = 2673553) B2673553
theorem B14451929 : Blo 1583990 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B2376971 : Blo 1583990 2376971 := bstep (se 1 (by rfl) ⟨1782728, by rfl⟩ : syracuseStep 2376971 = 3565457) B3565457
theorem B2376983 : Blo 1583990 2376983 := bstep (se 1 (by rfl) ⟨1782737, by rfl⟩ : syracuseStep 2376983 = 3565475) B3565475
theorem B2377049 : Blo 1583990 2377049 := bstep (se 2 (by rfl) ⟨891393, by rfl⟩ : syracuseStep 2377049 = 1782787) B1782787
theorem B5711249 : Blo 1583990 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B3564953 : Blo 1583990 3564953 := bstep (se 2 (by rfl) ⟨1336857, by rfl⟩ : syracuseStep 3564953 = 2673715) B2673715
theorem B2377163 : Blo 1583990 2377163 := bstep (se 1 (by rfl) ⟨1782872, by rfl⟩ : syracuseStep 2377163 = 3565745) B3565745
theorem B5350859 : Blo 1583990 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B2377175 : Blo 1583990 2377175 := bstep (se 1 (by rfl) ⟨1782881, by rfl⟩ : syracuseStep 2377175 = 3565763) B3565763
theorem B3565043 : Blo 1583990 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B3565079 : Blo 1583990 3565079 := bstep (se 1 (by rfl) ⟨2673809, by rfl⟩ : syracuseStep 3565079 = 5347619) B5347619
theorem B2377241 : Blo 1583990 2377241 := bstep (se 2 (by rfl) ⟨891465, by rfl⟩ : syracuseStep 2377241 = 1782931) B1782931
theorem B2377355 : Blo 1583990 2377355 := bstep (se 1 (by rfl) ⟨1783016, by rfl⟩ : syracuseStep 2377355 = 3566033) B3566033
theorem B7145111 : Blo 1583990 7145111 := bstep (se 1 (by rfl) ⟨5358833, by rfl⟩ : syracuseStep 7145111 = 10717667) B10717667
theorem B2377367 : Blo 1583990 2377367 := bstep (se 1 (by rfl) ⟨1783025, by rfl⟩ : syracuseStep 2377367 = 3566051) B3566051
theorem B3565259 : Blo 1583990 3565259 := bstep (se 1 (by rfl) ⟨2673944, by rfl⟩ : syracuseStep 3565259 = 5347889) B5347889
theorem B12035789 : Blo 1583990 12035789 := bstep (se 3 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 12035789 = 4513421) B4513421
theorem B2442955 : Blo 1583990 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B2377433 : Blo 1583990 2377433 := bstep (se 2 (by rfl) ⟨891537, by rfl⟩ : syracuseStep 2377433 = 1783075) B1783075
theorem B3565313 : Blo 1583990 3565313 := bstep (se 2 (by rfl) ⟨1336992, by rfl⟩ : syracuseStep 3565313 = 2673985) B2673985
theorem B3008279 : Blo 1583990 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B2377547 : Blo 1583990 2377547 := bstep (se 1 (by rfl) ⟨1783160, by rfl⟩ : syracuseStep 2377547 = 3566321) B3566321
theorem B2377559 : Blo 1583990 2377559 := bstep (se 1 (by rfl) ⟨1783169, by rfl⟩ : syracuseStep 2377559 = 3566339) B3566339
theorem B2377625 : Blo 1583990 2377625 := bstep (se 2 (by rfl) ⟨891609, by rfl⟩ : syracuseStep 2377625 = 1783219) B1783219
theorem B20309939 : Blo 1583990 20309939 := bstep (se 1 (by rfl) ⟨15232454, by rfl⟩ : syracuseStep 20309939 = 30464909) B30464909
theorem B9029555 : Blo 1583990 9029555 := bstep (se 1 (by rfl) ⟨6772166, by rfl⟩ : syracuseStep 9029555 = 13544333) B13544333
theorem B20301785 : Blo 1583990 20301785 := bstep (se 2 (by rfl) ⟨7613169, by rfl⟩ : syracuseStep 20301785 = 15226339) B15226339
theorem B3565529 : Blo 1583990 3565529 := bstep (se 2 (by rfl) ⟨1337073, by rfl⟩ : syracuseStep 3565529 = 2674147) B2674147
theorem B2377739 : Blo 1583990 2377739 := bstep (se 1 (by rfl) ⟨1783304, by rfl⟩ : syracuseStep 2377739 = 3566609) B3566609
theorem B2377751 : Blo 1583990 2377751 := bstep (se 1 (by rfl) ⟨1783313, by rfl⟩ : syracuseStep 2377751 = 3566627) B3566627
theorem B3565619 : Blo 1583990 3565619 := bstep (se 1 (by rfl) ⟨2674214, by rfl⟩ : syracuseStep 3565619 = 5348429) B5348429
theorem B9635905 : Blo 1583990 9635905 := bstep (se 2 (by rfl) ⟨3613464, by rfl⟩ : syracuseStep 9635905 = 7226929) B7226929
theorem B3565655 : Blo 1583990 3565655 := bstep (se 1 (by rfl) ⟨2674241, by rfl⟩ : syracuseStep 3565655 = 5348483) B5348483
theorem B2377817 : Blo 1583990 2377817 := bstep (se 2 (by rfl) ⟨891681, by rfl⟩ : syracuseStep 2377817 = 1783363) B1783363
theorem B12036275 : Blo 1583990 12036275 := bstep (se 1 (by rfl) ⟨9027206, by rfl⟩ : syracuseStep 12036275 = 18054413) B18054413
theorem B2377931 : Blo 1583990 2377931 := bstep (se 1 (by rfl) ⟨1783448, by rfl⟩ : syracuseStep 2377931 = 3566897) B3566897
theorem B2377943 : Blo 1583990 2377943 := bstep (se 1 (by rfl) ⟨1783457, by rfl⟩ : syracuseStep 2377943 = 3566915) B3566915
theorem B3565835 : Blo 1583990 3565835 := bstep (se 1 (by rfl) ⟨2674376, by rfl⟩ : syracuseStep 3565835 = 5348753) B5348753
theorem B2287883 : Blo 1583990 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B2378009 : Blo 1583990 2378009 := bstep (se 2 (by rfl) ⟨891753, by rfl⟩ : syracuseStep 2378009 = 1783507) B1783507
theorem B3008819 : Blo 1583990 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B3565889 : Blo 1583990 3565889 := bstep (se 2 (by rfl) ⟨1337208, by rfl⟩ : syracuseStep 3565889 = 2674417) B2674417
theorem B6768971 : Blo 1583990 6768971 := bstep (se 1 (by rfl) ⟨5076728, by rfl⟩ : syracuseStep 6768971 = 10153457) B10153457
theorem B5146973 : Blo 1583990 5146973 := bstep (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) B1930115
theorem B2378123 : Blo 1583990 2378123 := bstep (se 1 (by rfl) ⟨1783592, by rfl⟩ : syracuseStep 2378123 = 3567185) B3567185
theorem B2673047 : Blo 1583990 2673047 := bstep (se 1 (by rfl) ⟨2004785, by rfl⟩ : syracuseStep 2673047 = 4009571) B4009571
theorem B2378135 : Blo 1583990 2378135 := bstep (se 1 (by rfl) ⟨1783601, by rfl⟩ : syracuseStep 2378135 = 3567203) B3567203
theorem B3975617 : Blo 1583990 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B10291673 : Blo 1583990 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B2378201 : Blo 1583990 2378201 := bstep (se 2 (by rfl) ⟨891825, by rfl⟩ : syracuseStep 2378201 = 1783651) B1783651
theorem B2673175 : Blo 1583990 2673175 := bstep (se 1 (by rfl) ⟨2004881, by rfl⟩ : syracuseStep 2673175 = 4009763) B4009763
theorem B3566105 : Blo 1583990 3566105 := bstep (se 2 (by rfl) ⟨1337289, by rfl⟩ : syracuseStep 3566105 = 2674579) B2674579
theorem B3385921 : Blo 1583990 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B3566195 : Blo 1583990 3566195 := bstep (se 1 (by rfl) ⟨2674646, by rfl⟩ : syracuseStep 3566195 = 5349293) B5349293
theorem B3574411 : Blo 1583990 3574411 := bstep (se 1 (by rfl) ⟨2680808, by rfl⟩ : syracuseStep 3574411 = 5361617) B5361617
theorem B3566231 : Blo 1583990 3566231 := bstep (se 1 (by rfl) ⟨2674673, by rfl⟩ : syracuseStep 3566231 = 5349347) B5349347
theorem B3009305 : Blo 1583990 3009305 := bstep (se 2 (by rfl) ⟨1128489, by rfl⟩ : syracuseStep 3009305 = 2256979) B2256979
theorem B3566411 : Blo 1583990 3566411 := bstep (se 1 (by rfl) ⟨2674808, by rfl⟩ : syracuseStep 3566411 = 5349617) B5349617
theorem B1583991 : Blo 1583990 1583991 := bstep (se 1 (by rfl) ⟨1187993, by rfl⟩ : syracuseStep 1583991 = 2375987) B2375987
theorem B3566465 : Blo 1583990 3566465 := bstep (se 2 (by rfl) ⟨1337424, by rfl⟩ : syracuseStep 3566465 = 2674849) B2674849
theorem B12848003 : Blo 1583990 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B1584011 : Blo 1583990 1584011 := bstep (se 1 (by rfl) ⟨1188008, by rfl⟩ : syracuseStep 1584011 = 2376017) B2376017
theorem B1584023 : Blo 1583990 1584023 := bstep (se 1 (by rfl) ⟨1188017, by rfl⟩ : syracuseStep 1584023 = 2376035) B2376035
theorem B1584043 : Blo 1583990 1584043 := bstep (se 1 (by rfl) ⟨1188032, by rfl⟩ : syracuseStep 1584043 = 2376065) B2376065
theorem B1584055 : Blo 1583990 1584055 := bstep (se 1 (by rfl) ⟨1188041, by rfl⟩ : syracuseStep 1584055 = 2376083) B2376083
theorem B1584075 : Blo 1583990 1584075 := bstep (se 1 (by rfl) ⟨1188056, by rfl⟩ : syracuseStep 1584075 = 2376113) B2376113
theorem B1584087 : Blo 1583990 1584087 := bstep (se 1 (by rfl) ⟨1188065, by rfl⟩ : syracuseStep 1584087 = 2376131) B2376131
theorem B1584107 : Blo 1583990 1584107 := bstep (se 1 (by rfl) ⟨1188080, by rfl⟩ : syracuseStep 1584107 = 2376161) B2376161
theorem B1584119 : Blo 1583990 1584119 := bstep (se 1 (by rfl) ⟨1188089, by rfl⟩ : syracuseStep 1584119 = 2376179) B2376179
theorem B13028357 : Blo 1583990 13028357 := bstep (se 4 (by rfl) ⟨1221408, by rfl⟩ : syracuseStep 13028357 = 2442817) B2442817
theorem B1584139 : Blo 1583990 1584139 := bstep (se 1 (by rfl) ⟨1188104, by rfl⟩ : syracuseStep 1584139 = 2376209) B2376209
theorem B1584151 : Blo 1583990 1584151 := bstep (se 1 (by rfl) ⟨1188113, by rfl⟩ : syracuseStep 1584151 = 2376227) B2376227
theorem B1584171 : Blo 1583990 1584171 := bstep (se 1 (by rfl) ⟨1188128, by rfl⟩ : syracuseStep 1584171 = 2376257) B2376257
theorem B1584183 : Blo 1583990 1584183 := bstep (se 1 (by rfl) ⟨1188137, by rfl⟩ : syracuseStep 1584183 = 2376275) B2376275
theorem B1584203 : Blo 1583990 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B6425675 : Blo 1583990 6425675 := bstep (se 1 (by rfl) ⟨4819256, by rfl⟩ : syracuseStep 6425675 = 9638513) B9638513
theorem B1584215 : Blo 1583990 1584215 := bstep (se 1 (by rfl) ⟨1188161, by rfl⟩ : syracuseStep 1584215 = 2376323) B2376323
theorem B2255959 : Blo 1583990 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B6425689 : Blo 1583990 6425689 := bstep (se 2 (by rfl) ⟨2409633, by rfl⟩ : syracuseStep 6425689 = 4819267) B4819267
theorem B3566681 : Blo 1583990 3566681 := bstep (se 2 (by rfl) ⟨1337505, by rfl⟩ : syracuseStep 3566681 = 2675011) B2675011
theorem B6769757 : Blo 1583990 6769757 := bstep (se 3 (by rfl) ⟨1269329, by rfl⟩ : syracuseStep 6769757 = 2538659) B2538659
theorem B1584235 : Blo 1583990 1584235 := bstep (se 1 (by rfl) ⟨1188176, by rfl⟩ : syracuseStep 1584235 = 2376353) B2376353
theorem B1584247 : Blo 1583990 1584247 := bstep (se 1 (by rfl) ⟨1188185, by rfl⟩ : syracuseStep 1584247 = 2376371) B2376371
theorem B1584267 : Blo 1583990 1584267 := bstep (se 1 (by rfl) ⟨1188200, by rfl⟩ : syracuseStep 1584267 = 2376401) B2376401
theorem B2673803 : Blo 1583990 2673803 := bstep (se 1 (by rfl) ⟨2005352, by rfl⟩ : syracuseStep 2673803 = 4010705) B4010705
theorem B1584279 : Blo 1583990 1584279 := bstep (se 1 (by rfl) ⟨1188209, by rfl⟩ : syracuseStep 1584279 = 2376419) B2376419
theorem B1584299 : Blo 1583990 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B3566771 : Blo 1583990 3566771 := bstep (se 1 (by rfl) ⟨2675078, by rfl⟩ : syracuseStep 3566771 = 5350157) B5350157
theorem B1584311 : Blo 1583990 1584311 := bstep (se 1 (by rfl) ⟨1188233, by rfl⟩ : syracuseStep 1584311 = 2376467) B2376467
theorem B1584331 : Blo 1583990 1584331 := bstep (se 1 (by rfl) ⟨1188248, by rfl⟩ : syracuseStep 1584331 = 2376497) B2376497
theorem B1584343 : Blo 1583990 1584343 := bstep (se 1 (by rfl) ⟨1188257, by rfl⟩ : syracuseStep 1584343 = 2376515) B2376515
theorem B6859993 : Blo 1583990 6859993 := bstep (se 2 (by rfl) ⟨2572497, by rfl⟩ : syracuseStep 6859993 = 5144995) B5144995
theorem B3566807 : Blo 1583990 3566807 := bstep (se 1 (by rfl) ⟨2675105, by rfl⟩ : syracuseStep 3566807 = 5350211) B5350211
theorem B1584363 : Blo 1583990 1584363 := bstep (se 1 (by rfl) ⟨1188272, by rfl⟩ : syracuseStep 1584363 = 2376545) B2376545
theorem B1584375 : Blo 1583990 1584375 := bstep (se 1 (by rfl) ⟨1188281, by rfl⟩ : syracuseStep 1584375 = 2376563) B2376563
theorem B1584395 : Blo 1583990 1584395 := bstep (se 1 (by rfl) ⟨1188296, by rfl⟩ : syracuseStep 1584395 = 2376593) B2376593
theorem B2673931 : Blo 1583990 2673931 := bstep (se 1 (by rfl) ⟨2005448, by rfl⟩ : syracuseStep 2673931 = 4010897) B4010897
theorem B1584407 : Blo 1583990 1584407 := bstep (se 1 (by rfl) ⟨1188305, by rfl⟩ : syracuseStep 1584407 = 2376611) B2376611
theorem B1584427 : Blo 1583990 1584427 := bstep (se 1 (by rfl) ⟨1188320, by rfl⟩ : syracuseStep 1584427 = 2376641) B2376641
theorem B6016301 : Blo 1583990 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B1584439 : Blo 1583990 1584439 := bstep (se 1 (by rfl) ⟨1188329, by rfl⟩ : syracuseStep 1584439 = 2376659) B2376659
theorem B1584459 : Blo 1583990 1584459 := bstep (se 1 (by rfl) ⟨1188344, by rfl⟩ : syracuseStep 1584459 = 2376689) B2376689
theorem B1584471 : Blo 1583990 1584471 := bstep (se 1 (by rfl) ⟨1188353, by rfl⟩ : syracuseStep 1584471 = 2376707) B2376707
theorem B1584491 : Blo 1583990 1584491 := bstep (se 1 (by rfl) ⟨1188368, by rfl⟩ : syracuseStep 1584491 = 2376737) B2376737
theorem B1584503 : Blo 1583990 1584503 := bstep (se 1 (by rfl) ⟨1188377, by rfl⟩ : syracuseStep 1584503 = 2376755) B2376755
theorem B1584523 : Blo 1583990 1584523 := bstep (se 1 (by rfl) ⟨1188392, by rfl⟩ : syracuseStep 1584523 = 2376785) B2376785
theorem B3566987 : Blo 1583990 3566987 := bstep (se 1 (by rfl) ⟨2675240, by rfl⟩ : syracuseStep 3566987 = 5350481) B5350481
theorem B1584535 : Blo 1583990 1584535 := bstep (se 1 (by rfl) ⟨1188401, by rfl⟩ : syracuseStep 1584535 = 2376803) B2376803
theorem B2674073 : Blo 1583990 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B1584555 : Blo 1583990 1584555 := bstep (se 1 (by rfl) ⟨1188416, by rfl⟩ : syracuseStep 1584555 = 2376833) B2376833
theorem B5713325 : Blo 1583990 5713325 := bstep (se 3 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 5713325 = 2142497) B2142497
theorem B1584567 : Blo 1583990 1584567 := bstep (se 1 (by rfl) ⟨1188425, by rfl⟩ : syracuseStep 1584567 = 2376851) B2376851
theorem B3567041 : Blo 1583990 3567041 := bstep (se 2 (by rfl) ⟨1337640, by rfl⟩ : syracuseStep 3567041 = 2675281) B2675281
theorem B1584587 : Blo 1583990 1584587 := bstep (se 1 (by rfl) ⟨1188440, by rfl⟩ : syracuseStep 1584587 = 2376881) B2376881
theorem B1584599 : Blo 1583990 1584599 := bstep (se 1 (by rfl) ⟨1188449, by rfl⟩ : syracuseStep 1584599 = 2376899) B2376899
theorem B4574681 : Blo 1583990 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B1584619 : Blo 1583990 1584619 := bstep (se 1 (by rfl) ⟨1188464, by rfl⟩ : syracuseStep 1584619 = 2376929) B2376929
theorem B1584631 : Blo 1583990 1584631 := bstep (se 1 (by rfl) ⟨1188473, by rfl⟩ : syracuseStep 1584631 = 2376947) B2376947
theorem B1584651 : Blo 1583990 1584651 := bstep (se 1 (by rfl) ⟨1188488, by rfl⟩ : syracuseStep 1584651 = 2376977) B2376977
theorem B1584663 : Blo 1583990 1584663 := bstep (se 1 (by rfl) ⟨1188497, by rfl⟩ : syracuseStep 1584663 = 2376995) B2376995
theorem B2674201 : Blo 1583990 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B18058787 : Blo 1583990 18058787 := bstep (se 1 (by rfl) ⟨13544090, by rfl⟩ : syracuseStep 18058787 = 27088181) B27088181
theorem B1584683 : Blo 1583990 1584683 := bstep (se 1 (by rfl) ⟨1188512, by rfl⟩ : syracuseStep 1584683 = 2377025) B2377025
theorem B1584695 : Blo 1583990 1584695 := bstep (se 1 (by rfl) ⟨1188521, by rfl⟩ : syracuseStep 1584695 = 2377043) B2377043
theorem B1584715 : Blo 1583990 1584715 := bstep (se 1 (by rfl) ⟨1188536, by rfl⟩ : syracuseStep 1584715 = 2377073) B2377073
theorem B1584727 : Blo 1583990 1584727 := bstep (se 1 (by rfl) ⟨1188545, by rfl⟩ : syracuseStep 1584727 = 2377091) B2377091
theorem B12037733 : Blo 1583990 12037733 := bstep (se 4 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 12037733 = 2257075) B2257075
theorem B1584747 : Blo 1583990 1584747 := bstep (se 1 (by rfl) ⟨1188560, by rfl⟩ : syracuseStep 1584747 = 2377121) B2377121
theorem B1584759 : Blo 1583990 1584759 := bstep (se 1 (by rfl) ⟨1188569, by rfl⟩ : syracuseStep 1584759 = 2377139) B2377139
theorem B1584779 : Blo 1583990 1584779 := bstep (se 1 (by rfl) ⟨1188584, by rfl⟩ : syracuseStep 1584779 = 2377169) B2377169
theorem B1584791 : Blo 1583990 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B3567257 : Blo 1583990 3567257 := bstep (se 2 (by rfl) ⟨1337721, by rfl⟩ : syracuseStep 3567257 = 2675443) B2675443
theorem B1584811 : Blo 1583990 1584811 := bstep (se 1 (by rfl) ⟨1188608, by rfl⟩ : syracuseStep 1584811 = 2377217) B2377217
theorem B1584823 : Blo 1583990 1584823 := bstep (se 1 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 1584823 = 2377235) B2377235
theorem B1584843 : Blo 1583990 1584843 := bstep (se 1 (by rfl) ⟨1188632, by rfl⟩ : syracuseStep 1584843 = 2377265) B2377265
theorem B1584855 : Blo 1583990 1584855 := bstep (se 1 (by rfl) ⟨1188641, by rfl⟩ : syracuseStep 1584855 = 2377283) B2377283
theorem B1584875 : Blo 1583990 1584875 := bstep (se 1 (by rfl) ⟨1188656, by rfl⟩ : syracuseStep 1584875 = 2377313) B2377313
theorem B3567347 : Blo 1583990 3567347 := bstep (se 1 (by rfl) ⟨2675510, by rfl⟩ : syracuseStep 3567347 = 5351021) B5351021
theorem B1584887 : Blo 1583990 1584887 := bstep (se 1 (by rfl) ⟨1188665, by rfl⟩ : syracuseStep 1584887 = 2377331) B2377331
theorem B1584907 : Blo 1583990 1584907 := bstep (se 1 (by rfl) ⟨1188680, by rfl⟩ : syracuseStep 1584907 = 2377361) B2377361
theorem B1584919 : Blo 1583990 1584919 := bstep (se 1 (by rfl) ⟨1188689, by rfl⟩ : syracuseStep 1584919 = 2377379) B2377379
theorem B2256665 : Blo 1583990 2256665 := bstep (se 2 (by rfl) ⟨846249, by rfl⟩ : syracuseStep 2256665 = 1692499) B1692499
theorem B1584939 : Blo 1583990 1584939 := bstep (se 1 (by rfl) ⟨1188704, by rfl⟩ : syracuseStep 1584939 = 2377409) B2377409
theorem B1584951 : Blo 1583990 1584951 := bstep (se 1 (by rfl) ⟨1188713, by rfl⟩ : syracuseStep 1584951 = 2377427) B2377427
theorem B1584971 : Blo 1583990 1584971 := bstep (se 1 (by rfl) ⟨1188728, by rfl⟩ : syracuseStep 1584971 = 2377457) B2377457
theorem B1584983 : Blo 1583990 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B1585003 : Blo 1583990 1585003 := bstep (se 1 (by rfl) ⟨1188752, by rfl⟩ : syracuseStep 1585003 = 2377505) B2377505
theorem B1585015 : Blo 1583990 1585015 := bstep (se 1 (by rfl) ⟨1188761, by rfl⟩ : syracuseStep 1585015 = 2377523) B2377523
theorem B2256779 : Blo 1583990 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1585035 : Blo 1583990 1585035 := bstep (se 1 (by rfl) ⟨1188776, by rfl⟩ : syracuseStep 1585035 = 2377553) B2377553
theorem B1585047 : Blo 1583990 1585047 := bstep (se 1 (by rfl) ⟨1188785, by rfl⟩ : syracuseStep 1585047 = 2377571) B2377571
theorem B1585067 : Blo 1583990 1585067 := bstep (se 1 (by rfl) ⟨1188800, by rfl⟩ : syracuseStep 1585067 = 2377601) B2377601
theorem B1585079 : Blo 1583990 1585079 := bstep (se 1 (by rfl) ⟨1188809, by rfl⟩ : syracuseStep 1585079 = 2377619) B2377619
theorem B1585099 : Blo 1583990 1585099 := bstep (se 1 (by rfl) ⟨1188824, by rfl⟩ : syracuseStep 1585099 = 2377649) B2377649
theorem B1585111 : Blo 1583990 1585111 := bstep (se 1 (by rfl) ⟨1188833, by rfl⟩ : syracuseStep 1585111 = 2377667) B2377667
theorem B4009945 : Blo 1583990 4009945 := bstep (se 2 (by rfl) ⟨1503729, by rfl⟩ : syracuseStep 4009945 = 3007459) B3007459
theorem B1585131 : Blo 1583990 1585131 := bstep (se 1 (by rfl) ⟨1188848, by rfl⟩ : syracuseStep 1585131 = 2377697) B2377697
theorem B1585143 : Blo 1583990 1585143 := bstep (se 1 (by rfl) ⟨1188857, by rfl⟩ : syracuseStep 1585143 = 2377715) B2377715
theorem B12029957 : Blo 1583990 12029957 := bstep (se 4 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 12029957 = 2255617) B2255617
theorem B1585163 : Blo 1583990 1585163 := bstep (se 1 (by rfl) ⟨1188872, by rfl⟩ : syracuseStep 1585163 = 2377745) B2377745
theorem B1585175 : Blo 1583990 1585175 := bstep (se 1 (by rfl) ⟨1188881, by rfl⟩ : syracuseStep 1585175 = 2377763) B2377763
theorem B1585195 : Blo 1583990 1585195 := bstep (se 1 (by rfl) ⟨1188896, by rfl⟩ : syracuseStep 1585195 = 2377793) B2377793
theorem B6017075 : Blo 1583990 6017075 := bstep (se 1 (by rfl) ⟨4512806, by rfl⟩ : syracuseStep 6017075 = 9025613) B9025613
theorem B1585207 : Blo 1583990 1585207 := bstep (se 1 (by rfl) ⟨1188905, by rfl⟩ : syracuseStep 1585207 = 2377811) B2377811
theorem B1585227 : Blo 1583990 1585227 := bstep (se 1 (by rfl) ⟨1188920, by rfl⟩ : syracuseStep 1585227 = 2377841) B2377841
theorem B12038219 : Blo 1583990 12038219 := bstep (se 1 (by rfl) ⟨9028664, by rfl⟩ : syracuseStep 12038219 = 18057329) B18057329
theorem B4821067 : Blo 1583990 4821067 := bstep (se 1 (by rfl) ⟨3615800, by rfl⟩ : syracuseStep 4821067 = 7231601) B7231601
theorem B2674775 : Blo 1583990 2674775 := bstep (se 1 (by rfl) ⟨2006081, by rfl⟩ : syracuseStep 2674775 = 4012163) B4012163
theorem B1585239 : Blo 1583990 1585239 := bstep (se 1 (by rfl) ⟨1188929, by rfl⟩ : syracuseStep 1585239 = 2377859) B2377859
theorem B1585259 : Blo 1583990 1585259 := bstep (se 1 (by rfl) ⟨1188944, by rfl⟩ : syracuseStep 1585259 = 2377889) B2377889
theorem B2855027 : Blo 1583990 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B1585271 : Blo 1583990 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B1585291 : Blo 1583990 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B1585303 : Blo 1583990 1585303 := bstep (se 1 (by rfl) ⟨1188977, by rfl⟩ : syracuseStep 1585303 = 2377955) B2377955
theorem B1585323 : Blo 1583990 1585323 := bstep (se 1 (by rfl) ⟨1188992, by rfl⟩ : syracuseStep 1585323 = 2377985) B2377985
theorem B1585335 : Blo 1583990 1585335 := bstep (se 1 (by rfl) ⟨1189001, by rfl⟩ : syracuseStep 1585335 = 2378003) B2378003
theorem B1585355 : Blo 1583990 1585355 := bstep (se 1 (by rfl) ⟨1189016, by rfl⟩ : syracuseStep 1585355 = 2378033) B2378033
theorem B2674903 : Blo 1583990 2674903 := bstep (se 1 (by rfl) ⟨2006177, by rfl⟩ : syracuseStep 2674903 = 4012355) B4012355
theorem B1585367 : Blo 1583990 1585367 := bstep (se 1 (by rfl) ⟨1189025, by rfl⟩ : syracuseStep 1585367 = 2378051) B2378051
theorem B1781995 : Blo 1583990 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B1585387 : Blo 1583990 1585387 := bstep (se 1 (by rfl) ⟨1189040, by rfl⟩ : syracuseStep 1585387 = 2378081) B2378081
theorem B1585399 : Blo 1583990 1585399 := bstep (se 1 (by rfl) ⟨1189049, by rfl⟩ : syracuseStep 1585399 = 2378099) B2378099
theorem B1585419 : Blo 1583990 1585419 := bstep (se 1 (by rfl) ⟨1189064, by rfl⟩ : syracuseStep 1585419 = 2378129) B2378129
theorem B1585431 : Blo 1583990 1585431 := bstep (se 1 (by rfl) ⟨1189073, by rfl⟩ : syracuseStep 1585431 = 2378147) B2378147
theorem B13717795 : Blo 1583990 13717795 := bstep (se 1 (by rfl) ⟨10288346, by rfl⟩ : syracuseStep 13717795 = 20576693) B20576693
theorem B1585451 : Blo 1583990 1585451 := bstep (se 1 (by rfl) ⟨1189088, by rfl⟩ : syracuseStep 1585451 = 2378177) B2378177
theorem B1585463 : Blo 1583990 1585463 := bstep (se 1 (by rfl) ⟨1189097, by rfl⟩ : syracuseStep 1585463 = 2378195) B2378195
theorem B7614785 : Blo 1583990 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B2855243 : Blo 1583990 2855243 := bstep (se 1 (by rfl) ⟨2141432, by rfl⟩ : syracuseStep 2855243 = 4282865) B4282865
theorem B1585483 : Blo 1583990 1585483 := bstep (se 1 (by rfl) ⟨1189112, by rfl⟩ : syracuseStep 1585483 = 2378225) B2378225
theorem B1782103 : Blo 1583990 1782103 := bstep (se 1 (by rfl) ⟨1336577, by rfl⟩ : syracuseStep 1782103 = 2673155) B2673155
theorem B5075293 : Blo 1583990 5075293 := bstep (se 3 (by rfl) ⟨951617, by rfl⟩ : syracuseStep 5075293 = 1903235) B1903235
theorem B6771089 : Blo 1583990 6771089 := bstep (se 2 (by rfl) ⟨2539158, by rfl⟩ : syracuseStep 6771089 = 5078317) B5078317
theorem B2257303 : Blo 1583990 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B8565209 : Blo 1583990 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B1782283 : Blo 1583990 1782283 := bstep (se 1 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 1782283 = 2673425) B2673425
theorem B5788235 : Blo 1583990 5788235 := bstep (se 1 (by rfl) ⟨4341176, by rfl⟩ : syracuseStep 5788235 = 8682353) B8682353
theorem B5075549 : Blo 1583990 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B8024669 : Blo 1583990 8024669 := bstep (se 3 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 8024669 = 3009251) B3009251
theorem B1782391 : Blo 1583990 1782391 := bstep (se 1 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 1782391 = 2673587) B2673587
theorem B1692311 : Blo 1583990 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B1782571 : Blo 1583990 1782571 := bstep (se 1 (by rfl) ⟨1336928, by rfl⟩ : syracuseStep 1782571 = 2673857) B2673857
theorem B1782679 : Blo 1583990 1782679 := bstep (se 1 (by rfl) ⟨1337009, by rfl⟩ : syracuseStep 1782679 = 2674019) B2674019
theorem B9024473 : Blo 1583990 9024473 := bstep (se 2 (by rfl) ⟨3384177, by rfl⟩ : syracuseStep 9024473 = 6768355) B6768355
theorem B5346269 : Blo 1583990 5346269 := bstep (se 3 (by rfl) ⟨1002425, by rfl⟩ : syracuseStep 5346269 = 2004851) B2004851
theorem B222467107 : Blo 1583990 222467107 := bstep (se 1 (by rfl) ⟨166850330, by rfl⟩ : syracuseStep 222467107 = 333700661) B333700661
theorem B4011059 : Blo 1583990 4011059 := bstep (se 1 (by rfl) ⟨3008294, by rfl⟩ : syracuseStep 4011059 = 6016589) B6016589
theorem B1782859 : Blo 1583990 1782859 := bstep (se 1 (by rfl) ⟨1337144, by rfl⟩ : syracuseStep 1782859 = 2674289) B2674289
theorem B6427799 : Blo 1583990 6427799 := bstep (se 1 (by rfl) ⟨4820849, by rfl⟩ : syracuseStep 6427799 = 9641699) B9641699
theorem B1782967 : Blo 1583990 1782967 := bstep (se 1 (by rfl) ⟨1337225, by rfl⟩ : syracuseStep 1782967 = 2674451) B2674451
theorem B4011353 : Blo 1583990 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B1783147 : Blo 1583990 1783147 := bstep (se 1 (by rfl) ⟨1337360, by rfl⟩ : syracuseStep 1783147 = 2674721) B2674721
theorem B4281803 : Blo 1583990 4281803 := bstep (se 1 (by rfl) ⟨3211352, by rfl⟩ : syracuseStep 4281803 = 6422705) B6422705
theorem B1783255 : Blo 1583990 1783255 := bstep (se 1 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 1783255 = 2674883) B2674883
theorem B6018563 : Blo 1583990 6018563 := bstep (se 1 (by rfl) ⟨4513922, by rfl⟩ : syracuseStep 6018563 = 9027845) B9027845
theorem B38540893 : Blo 1583990 38540893 := bstep (se 3 (by rfl) ⟨7226417, by rfl⟩ : syracuseStep 38540893 = 14452835) B14452835
theorem B8566373 : Blo 1583990 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B6772355 : Blo 1583990 6772355 := bstep (se 1 (by rfl) ⟨5079266, by rfl⟩ : syracuseStep 6772355 = 10158533) B10158533
theorem B1783435 : Blo 1583990 1783435 := bstep (se 1 (by rfl) ⟨1337576, by rfl⟩ : syracuseStep 1783435 = 2675153) B2675153
theorem B1783543 : Blo 1583990 1783543 := bstep (se 1 (by rfl) ⟨1337657, by rfl⟩ : syracuseStep 1783543 = 2675315) B2675315
theorem B10844005 : Blo 1583990 10844005 := bstep (se 4 (by rfl) ⟨1016625, by rfl⟩ : syracuseStep 10844005 = 2033251) B2033251
theorem B6019019 : Blo 1583990 6019019 := bstep (se 1 (by rfl) ⟨4514264, by rfl⟩ : syracuseStep 6019019 = 9028529) B9028529
theorem B2005003 : Blo 1583990 2005003 := bstep (se 1 (by rfl) ⟨1503752, by rfl⟩ : syracuseStep 2005003 = 3007505) B3007505
theorem B5347403 : Blo 1583990 5347403 := bstep (se 1 (by rfl) ⟨4010552, by rfl⟩ : syracuseStep 5347403 = 8021105) B8021105
theorem B6019217 : Blo 1583990 6019217 := bstep (se 2 (by rfl) ⟨2257206, by rfl⟩ : syracuseStep 6019217 = 4514413) B4514413
theorem B39082135 : Blo 1583990 39082135 := bstep (se 1 (by rfl) ⟨29311601, by rfl⟩ : syracuseStep 39082135 = 58623203) B58623203
theorem B6101171 : Blo 1583990 6101171 := bstep (se 1 (by rfl) ⟨4575878, by rfl⟩ : syracuseStep 6101171 = 9151757) B9151757
theorem B5347673 : Blo 1583990 5347673 := bstep (se 2 (by rfl) ⟨2005377, by rfl⟩ : syracuseStep 5347673 = 4010755) B4010755
theorem B7616861 : Blo 1583990 7616861 := bstep (se 3 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 7616861 = 2856323) B2856323
theorem B12032387 : Blo 1583990 12032387 := bstep (se 1 (by rfl) ⟨9024290, by rfl⟩ : syracuseStep 12032387 = 18048581) B18048581
theorem B4282841 : Blo 1583990 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B9026113 : Blo 1583990 9026113 := bstep (se 2 (by rfl) ⟨3384792, by rfl⟩ : syracuseStep 9026113 = 6769585) B6769585
theorem B27810485 : Blo 1583990 27810485 := bstep (se 5 (by rfl) ⟨1303616, by rfl⟩ : syracuseStep 27810485 = 2607233) B2607233
theorem B4512601 : Blo 1583990 4512601 := bstep (se 2 (by rfl) ⟨1692225, by rfl⟩ : syracuseStep 4512601 = 3384451) B3384451
theorem B4013003 : Blo 1583990 4013003 := bstep (se 1 (by rfl) ⟨3009752, by rfl⟩ : syracuseStep 4013003 = 6019505) B6019505
theorem B2005975 : Blo 1583990 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B5348375 : Blo 1583990 5348375 := bstep (se 1 (by rfl) ⟨4011281, by rfl⟩ : syracuseStep 5348375 = 8022563) B8022563
theorem B8019161 : Blo 1583990 8019161 := bstep (se 2 (by rfl) ⟨3007185, by rfl⟩ : syracuseStep 8019161 = 6014371) B6014371
theorem B4512989 : Blo 1583990 4512989 := bstep (se 3 (by rfl) ⟨846185, by rfl⟩ : syracuseStep 4512989 = 1692371) B1692371
theorem B23158133 : Blo 1583990 23158133 := bstep (se 5 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 23158133 = 2171075) B2171075
theorem B22838705 : Blo 1583990 22838705 := bstep (se 2 (by rfl) ⟨8564514, by rfl⟩ : syracuseStep 22838705 = 17129029) B17129029
theorem B2538967 : Blo 1583990 2538967 := bstep (se 1 (by rfl) ⟨1904225, by rfl⟩ : syracuseStep 2538967 = 3808451) B3808451
theorem B3808729 : Blo 1583990 3808729 := bstep (se 2 (by rfl) ⟨1428273, by rfl⟩ : syracuseStep 3808729 = 2856547) B2856547
theorem B5348915 : Blo 1583990 5348915 := bstep (se 1 (by rfl) ⟨4011686, by rfl⟩ : syracuseStep 5348915 = 8023373) B8023373
theorem B8240791 : Blo 1583990 8240791 := bstep (se 1 (by rfl) ⟨6180593, by rfl⟩ : syracuseStep 8240791 = 12361187) B12361187
theorem B5349185 : Blo 1583990 5349185 := bstep (se 2 (by rfl) ⟨2005944, by rfl⟩ : syracuseStep 5349185 = 4011889) B4011889
theorem B9633667 : Blo 1583990 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B2539415 : Blo 1583990 2539415 := bstep (se 1 (by rfl) ⟨1904561, by rfl⟩ : syracuseStep 2539415 = 3809123) B3809123
theorem B3383255 : Blo 1583990 3383255 := bstep (se 1 (by rfl) ⟨2537441, by rfl⟩ : syracuseStep 3383255 = 5074883) B5074883
theorem B8019971 : Blo 1583990 8019971 := bstep (se 1 (by rfl) ⟨6014978, by rfl⟩ : syracuseStep 8019971 = 12029957) B12029957
theorem B9404419 : Blo 1583990 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B52109513 : Blo 1583990 52109513 := bstep (se 2 (by rfl) ⟨19541067, by rfl⟩ : syracuseStep 52109513 = 39082135) B39082135
theorem B4514059 : Blo 1583990 4514059 := bstep (se 1 (by rfl) ⟨3385544, by rfl⟩ : syracuseStep 4514059 = 6771089) B6771089
theorem B2375993 : Blo 1583990 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B5710139 : Blo 1583990 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B2376071 : Blo 1583990 2376071 := bstep (se 1 (by rfl) ⟨1782053, by rfl⟩ : syracuseStep 2376071 = 3564107) B3564107
theorem B3858823 : Blo 1583990 3858823 := bstep (se 1 (by rfl) ⟨2894117, by rfl⟩ : syracuseStep 3858823 = 5788235) B5788235
theorem B3383699 : Blo 1583990 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B5349779 : Blo 1583990 5349779 := bstep (se 1 (by rfl) ⟨4012334, by rfl⟩ : syracuseStep 5349779 = 8024669) B8024669
theorem B2376107 : Blo 1583990 2376107 := bstep (se 1 (by rfl) ⟨1782080, by rfl⟩ : syracuseStep 2376107 = 3564161) B3564161
theorem B2376137 : Blo 1583990 2376137 := bstep (se 2 (by rfl) ⟨891051, by rfl⟩ : syracuseStep 2376137 = 1782103) B1782103
theorem B6767057 : Blo 1583990 6767057 := bstep (se 2 (by rfl) ⟨2537646, by rfl⟩ : syracuseStep 6767057 = 5075293) B5075293
theorem B2376251 : Blo 1583990 2376251 := bstep (se 1 (by rfl) ⟨1782188, by rfl⟩ : syracuseStep 2376251 = 3564377) B3564377
theorem B2376311 : Blo 1583990 2376311 := bstep (se 1 (by rfl) ⟨1782233, by rfl⟩ : syracuseStep 2376311 = 3564467) B3564467
theorem B2376335 : Blo 1583990 2376335 := bstep (se 1 (by rfl) ⟨1782251, by rfl⟩ : syracuseStep 2376335 = 3564503) B3564503
theorem B3564179 : Blo 1583990 3564179 := bstep (se 1 (by rfl) ⟨2673134, by rfl⟩ : syracuseStep 3564179 = 5346269) B5346269
theorem B2376377 : Blo 1583990 2376377 := bstep (se 2 (by rfl) ⟨891141, by rfl⟩ : syracuseStep 2376377 = 1782283) B1782283
theorem B3564233 : Blo 1583990 3564233 := bstep (se 2 (by rfl) ⟨1336587, by rfl⟩ : syracuseStep 3564233 = 2673175) B2673175
theorem B19063525 : Blo 1583990 19063525 := bstep (se 4 (by rfl) ⟨1787205, by rfl⟩ : syracuseStep 19063525 = 3574411) B3574411
theorem B12034817 : Blo 1583990 12034817 := bstep (se 2 (by rfl) ⟨4513056, by rfl⟩ : syracuseStep 12034817 = 9026113) B9026113
theorem B4514561 : Blo 1583990 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B2376455 : Blo 1583990 2376455 := bstep (se 1 (by rfl) ⟨1782341, by rfl⟩ : syracuseStep 2376455 = 3564683) B3564683
theorem B4285199 : Blo 1583990 4285199 := bstep (se 1 (by rfl) ⟨3213899, by rfl⟩ : syracuseStep 4285199 = 6427799) B6427799
theorem B2376491 : Blo 1583990 2376491 := bstep (se 1 (by rfl) ⟨1782368, by rfl⟩ : syracuseStep 2376491 = 3564737) B3564737
theorem B9634619 : Blo 1583990 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B2376521 : Blo 1583990 2376521 := bstep (se 2 (by rfl) ⟨891195, by rfl⟩ : syracuseStep 2376521 = 1782391) B1782391
theorem B2376635 : Blo 1583990 2376635 := bstep (se 1 (by rfl) ⟨1782476, by rfl⟩ : syracuseStep 2376635 = 3564953) B3564953
theorem B2376695 : Blo 1583990 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B2376719 : Blo 1583990 2376719 := bstep (se 1 (by rfl) ⟨1782539, by rfl⟩ : syracuseStep 2376719 = 3565079) B3565079
theorem B2376761 : Blo 1583990 2376761 := bstep (se 2 (by rfl) ⟨891285, by rfl⟩ : syracuseStep 2376761 = 1782571) B1782571
theorem B5710915 : Blo 1583990 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B4514903 : Blo 1583990 4514903 := bstep (se 1 (by rfl) ⟨3386177, by rfl⟩ : syracuseStep 4514903 = 6772355) B6772355
theorem B2376839 : Blo 1583990 2376839 := bstep (se 1 (by rfl) ⟨1782629, by rfl⟩ : syracuseStep 2376839 = 3565259) B3565259
theorem B2376875 : Blo 1583990 2376875 := bstep (se 1 (by rfl) ⟨1782656, by rfl⟩ : syracuseStep 2376875 = 3565313) B3565313
theorem B2376905 : Blo 1583990 2376905 := bstep (se 2 (by rfl) ⟨891339, by rfl⟩ : syracuseStep 2376905 = 1782679) B1782679
theorem B11420909 : Blo 1583990 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B13534523 : Blo 1583990 13534523 := bstep (se 1 (by rfl) ⟨10150892, by rfl⟩ : syracuseStep 13534523 = 20301785) B20301785
theorem B2377019 : Blo 1583990 2377019 := bstep (se 1 (by rfl) ⟨1782764, by rfl⟩ : syracuseStep 2377019 = 3565529) B3565529
theorem B2377079 : Blo 1583990 2377079 := bstep (se 1 (by rfl) ⟨1782809, by rfl⟩ : syracuseStep 2377079 = 3565619) B3565619
theorem B3564935 : Blo 1583990 3564935 := bstep (se 1 (by rfl) ⟨2673701, by rfl⟩ : syracuseStep 3564935 = 5347403) B5347403
theorem B2377103 : Blo 1583990 2377103 := bstep (se 1 (by rfl) ⟨1782827, by rfl⟩ : syracuseStep 2377103 = 3565655) B3565655
theorem B2377145 : Blo 1583990 2377145 := bstep (se 2 (by rfl) ⟨891429, by rfl⟩ : syracuseStep 2377145 = 1782859) B1782859
theorem B3007945 : Blo 1583990 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B2377223 : Blo 1583990 2377223 := bstep (se 1 (by rfl) ⟨1782917, by rfl⟩ : syracuseStep 2377223 = 3565835) B3565835
theorem B2377259 : Blo 1583990 2377259 := bstep (se 1 (by rfl) ⟨1782944, by rfl⟩ : syracuseStep 2377259 = 3565889) B3565889
theorem B3565115 : Blo 1583990 3565115 := bstep (se 1 (by rfl) ⟨2673836, by rfl⟩ : syracuseStep 3565115 = 5347673) B5347673
theorem B2377289 : Blo 1583990 2377289 := bstep (se 2 (by rfl) ⟨891483, by rfl⟩ : syracuseStep 2377289 = 1782967) B1782967
theorem B8021591 : Blo 1583990 8021591 := bstep (se 1 (by rfl) ⟨6016193, by rfl⟩ : syracuseStep 8021591 = 12032387) B12032387
theorem B3565241 : Blo 1583990 3565241 := bstep (se 2 (by rfl) ⟨1336965, by rfl⟩ : syracuseStep 3565241 = 2673931) B2673931
theorem B2377403 : Blo 1583990 2377403 := bstep (se 1 (by rfl) ⟨1783052, by rfl⟩ : syracuseStep 2377403 = 3566105) B3566105
theorem B2377463 : Blo 1583990 2377463 := bstep (se 1 (by rfl) ⟨1783097, by rfl⟩ : syracuseStep 2377463 = 3566195) B3566195
theorem B2377487 : Blo 1583990 2377487 := bstep (se 1 (by rfl) ⟨1783115, by rfl⟩ : syracuseStep 2377487 = 3566231) B3566231
theorem B18540323 : Blo 1583990 18540323 := bstep (se 1 (by rfl) ⟨13905242, by rfl⟩ : syracuseStep 18540323 = 27810485) B27810485
theorem B2377529 : Blo 1583990 2377529 := bstep (se 2 (by rfl) ⟨891573, by rfl⟩ : syracuseStep 2377529 = 1783147) B1783147
theorem B2377607 : Blo 1583990 2377607 := bstep (se 1 (by rfl) ⟨1783205, by rfl⟩ : syracuseStep 2377607 = 3566411) B3566411
theorem B2377643 : Blo 1583990 2377643 := bstep (se 1 (by rfl) ⟨1783232, by rfl⟩ : syracuseStep 2377643 = 3566465) B3566465
theorem B3385289 : Blo 1583990 3385289 := bstep (se 2 (by rfl) ⟨1269483, by rfl⟩ : syracuseStep 3385289 = 2538967) B2538967
theorem B2377673 : Blo 1583990 2377673 := bstep (se 2 (by rfl) ⟨891627, by rfl⟩ : syracuseStep 2377673 = 1783255) B1783255
theorem B8685571 : Blo 1583990 8685571 := bstep (se 1 (by rfl) ⟨6514178, by rfl⟩ : syracuseStep 8685571 = 13028357) B13028357
theorem B3565583 : Blo 1583990 3565583 := bstep (se 1 (by rfl) ⟨2674187, by rfl⟩ : syracuseStep 3565583 = 5348375) B5348375
theorem B3565601 : Blo 1583990 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B2377787 : Blo 1583990 2377787 := bstep (se 1 (by rfl) ⟨1783340, by rfl⟩ : syracuseStep 2377787 = 3566681) B3566681
theorem B8022077 : Blo 1583990 8022077 := bstep (se 3 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 8022077 = 3008279) B3008279
theorem B2377847 : Blo 1583990 2377847 := bstep (se 1 (by rfl) ⟨1783385, by rfl⟩ : syracuseStep 2377847 = 3566771) B3566771
theorem B2377871 : Blo 1583990 2377871 := bstep (se 1 (by rfl) ⟨1783403, by rfl⟩ : syracuseStep 2377871 = 3566807) B3566807
theorem B3008659 : Blo 1583990 3008659 := bstep (se 1 (by rfl) ⟨2256494, by rfl⟩ : syracuseStep 3008659 = 4512989) B4512989
theorem B2377913 : Blo 1583990 2377913 := bstep (se 2 (by rfl) ⟨891717, by rfl⟩ : syracuseStep 2377913 = 1783435) B1783435
theorem B10987721 : Blo 1583990 10987721 := bstep (se 2 (by rfl) ⟨4120395, by rfl⟩ : syracuseStep 10987721 = 8240791) B8240791
theorem B2377991 : Blo 1583990 2377991 := bstep (se 1 (by rfl) ⟨1783493, by rfl⟩ : syracuseStep 2377991 = 3566987) B3566987
theorem B2378027 : Blo 1583990 2378027 := bstep (se 1 (by rfl) ⟨1783520, by rfl⟩ : syracuseStep 2378027 = 3567041) B3567041
theorem B3049787 : Blo 1583990 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B2378057 : Blo 1583990 2378057 := bstep (se 2 (by rfl) ⟨891771, by rfl⟩ : syracuseStep 2378057 = 1783543) B1783543
theorem B3565943 : Blo 1583990 3565943 := bstep (se 1 (by rfl) ⟨2674457, by rfl⟩ : syracuseStep 3565943 = 5348915) B5348915
theorem B2378171 : Blo 1583990 2378171 := bstep (se 1 (by rfl) ⟨1783628, by rfl⟩ : syracuseStep 2378171 = 3567257) B3567257
theorem B2378231 : Blo 1583990 2378231 := bstep (se 1 (by rfl) ⟨1783673, by rfl⟩ : syracuseStep 2378231 = 3567347) B3567347
theorem B3566123 : Blo 1583990 3566123 := bstep (se 1 (by rfl) ⟨2674592, by rfl⟩ : syracuseStep 3566123 = 5349185) B5349185
theorem B9022013 : Blo 1583990 9022013 := bstep (se 3 (by rfl) ⟨1691627, by rfl⟩ : syracuseStep 9022013 = 3383255) B3383255
theorem B2673337 : Blo 1583990 2673337 := bstep (se 2 (by rfl) ⟨1002501, by rfl⟩ : syracuseStep 2673337 = 2005003) B2005003
theorem B1903351 : Blo 1583990 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B1584007 : Blo 1583990 1584007 := bstep (se 1 (by rfl) ⟨1188005, by rfl⟩ : syracuseStep 1584007 = 2376011) B2376011
theorem B1903495 : Blo 1583990 1903495 := bstep (se 1 (by rfl) ⟨1427621, by rfl⟩ : syracuseStep 1903495 = 2855243) B2855243
theorem B1584015 : Blo 1583990 1584015 := bstep (se 1 (by rfl) ⟨1188011, by rfl⟩ : syracuseStep 1584015 = 2376023) B2376023
theorem B3566483 : Blo 1583990 3566483 := bstep (se 1 (by rfl) ⟨2674862, by rfl⟩ : syracuseStep 3566483 = 5349725) B5349725
theorem B1584059 : Blo 1583990 1584059 := bstep (se 1 (by rfl) ⟨1188044, by rfl⟩ : syracuseStep 1584059 = 2376089) B2376089
theorem B3566537 : Blo 1583990 3566537 := bstep (se 2 (by rfl) ⟨1337451, by rfl⟩ : syracuseStep 3566537 = 2674903) B2674903
theorem B51391493 : Blo 1583990 51391493 := bstep (se 4 (by rfl) ⟨4817952, by rfl⟩ : syracuseStep 51391493 = 9635905) B9635905
theorem B1584135 : Blo 1583990 1584135 := bstep (se 1 (by rfl) ⟨1188101, by rfl⟩ : syracuseStep 1584135 = 2376203) B2376203
theorem B1584143 : Blo 1583990 1584143 := bstep (se 1 (by rfl) ⟨1188107, by rfl⟩ : syracuseStep 1584143 = 2376215) B2376215
theorem B1584187 : Blo 1583990 1584187 := bstep (se 1 (by rfl) ⟨1188140, by rfl⟩ : syracuseStep 1584187 = 2376281) B2376281
theorem B1584263 : Blo 1583990 1584263 := bstep (se 1 (by rfl) ⟨1188197, by rfl⟩ : syracuseStep 1584263 = 2376395) B2376395
theorem B1584271 : Blo 1583990 1584271 := bstep (se 1 (by rfl) ⟨1188203, by rfl⟩ : syracuseStep 1584271 = 2376407) B2376407
theorem B1584315 : Blo 1583990 1584315 := bstep (se 1 (by rfl) ⟨1188236, by rfl⟩ : syracuseStep 1584315 = 2376473) B2376473
theorem B3009737 : Blo 1583990 3009737 := bstep (se 2 (by rfl) ⟨1128651, by rfl⟩ : syracuseStep 3009737 = 2257303) B2257303
theorem B1584391 : Blo 1583990 1584391 := bstep (se 1 (by rfl) ⟨1188293, by rfl⟩ : syracuseStep 1584391 = 2376587) B2376587
theorem B1584399 : Blo 1583990 1584399 := bstep (se 1 (by rfl) ⟨1188299, by rfl⟩ : syracuseStep 1584399 = 2376599) B2376599
theorem B1584443 : Blo 1583990 1584443 := bstep (se 1 (by rfl) ⟨1188332, by rfl⟩ : syracuseStep 1584443 = 2376665) B2376665
theorem B6016315 : Blo 1583990 6016315 := bstep (se 1 (by rfl) ⟨4512236, by rfl⟩ : syracuseStep 6016315 = 9024473) B9024473
theorem B2256187 : Blo 1583990 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B2674039 : Blo 1583990 2674039 := bstep (se 1 (by rfl) ⟨2005529, by rfl⟩ : syracuseStep 2674039 = 4011059) B4011059
theorem B1584519 : Blo 1583990 1584519 := bstep (se 1 (by rfl) ⟨1188389, by rfl⟩ : syracuseStep 1584519 = 2376779) B2376779
theorem B1584527 : Blo 1583990 1584527 := bstep (se 1 (by rfl) ⟨1188395, by rfl⟩ : syracuseStep 1584527 = 2376791) B2376791
theorem B1584571 : Blo 1583990 1584571 := bstep (se 1 (by rfl) ⟨1188428, by rfl⟩ : syracuseStep 1584571 = 2376857) B2376857
theorem B1584647 : Blo 1583990 1584647 := bstep (se 1 (by rfl) ⟨1188485, by rfl⟩ : syracuseStep 1584647 = 2376971) B2376971
theorem B1584655 : Blo 1583990 1584655 := bstep (se 1 (by rfl) ⟨1188491, by rfl⟩ : syracuseStep 1584655 = 2376983) B2376983
theorem B1584699 : Blo 1583990 1584699 := bstep (se 1 (by rfl) ⟨1188524, by rfl⟩ : syracuseStep 1584699 = 2377049) B2377049
theorem B2674235 : Blo 1583990 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B2854535 : Blo 1583990 2854535 := bstep (se 1 (by rfl) ⟨2140901, by rfl⟩ : syracuseStep 2854535 = 4281803) B4281803
theorem B1584775 : Blo 1583990 1584775 := bstep (se 1 (by rfl) ⟨1188581, by rfl⟩ : syracuseStep 1584775 = 2377163) B2377163
theorem B3567239 : Blo 1583990 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B1584783 : Blo 1583990 1584783 := bstep (se 1 (by rfl) ⟨1188587, by rfl⟩ : syracuseStep 1584783 = 2377175) B2377175
theorem B1584827 : Blo 1583990 1584827 := bstep (se 1 (by rfl) ⟨1188620, by rfl⟩ : syracuseStep 1584827 = 2377241) B2377241
theorem B8564453 : Blo 1583990 8564453 := bstep (se 4 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 8564453 = 1605835) B1605835
theorem B1584903 : Blo 1583990 1584903 := bstep (se 1 (by rfl) ⟨1188677, by rfl⟩ : syracuseStep 1584903 = 2377355) B2377355
theorem B1584911 : Blo 1583990 1584911 := bstep (se 1 (by rfl) ⟨1188683, by rfl⟩ : syracuseStep 1584911 = 2377367) B2377367
theorem B6016801 : Blo 1583990 6016801 := bstep (se 2 (by rfl) ⟨2256300, by rfl⟩ : syracuseStep 6016801 = 4512601) B4512601
theorem B8023859 : Blo 1583990 8023859 := bstep (se 1 (by rfl) ⟨6017894, by rfl⟩ : syracuseStep 8023859 = 12035789) B12035789
theorem B1584955 : Blo 1583990 1584955 := bstep (se 1 (by rfl) ⟨1188716, by rfl⟩ : syracuseStep 1584955 = 2377433) B2377433
theorem B1585031 : Blo 1583990 1585031 := bstep (se 1 (by rfl) ⟨1188773, by rfl⟩ : syracuseStep 1585031 = 2377547) B2377547
theorem B1585039 : Blo 1583990 1585039 := bstep (se 1 (by rfl) ⟨1188779, by rfl⟩ : syracuseStep 1585039 = 2377559) B2377559
theorem B1585083 : Blo 1583990 1585083 := bstep (se 1 (by rfl) ⟨1188812, by rfl⟩ : syracuseStep 1585083 = 2377625) B2377625
theorem B2674633 : Blo 1583990 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B1585159 : Blo 1583990 1585159 := bstep (se 1 (by rfl) ⟨1188869, by rfl⟩ : syracuseStep 1585159 = 2377739) B2377739
theorem B1585167 : Blo 1583990 1585167 := bstep (se 1 (by rfl) ⟨1188875, by rfl⟩ : syracuseStep 1585167 = 2377751) B2377751
theorem B1585211 : Blo 1583990 1585211 := bstep (se 1 (by rfl) ⟨1188908, by rfl⟩ : syracuseStep 1585211 = 2377817) B2377817
theorem B8024183 : Blo 1583990 8024183 := bstep (se 1 (by rfl) ⟨6018137, by rfl⟩ : syracuseStep 8024183 = 12036275) B12036275
theorem B4067447 : Blo 1583990 4067447 := bstep (se 1 (by rfl) ⟨3050585, by rfl⟩ : syracuseStep 4067447 = 6101171) B6101171
theorem B1585287 : Blo 1583990 1585287 := bstep (se 1 (by rfl) ⟨1188965, by rfl⟩ : syracuseStep 1585287 = 2377931) B2377931
theorem B1585295 : Blo 1583990 1585295 := bstep (se 1 (by rfl) ⟨1188971, by rfl⟩ : syracuseStep 1585295 = 2377943) B2377943
theorem B1585339 : Blo 1583990 1585339 := bstep (se 1 (by rfl) ⟨1189004, by rfl⟩ : syracuseStep 1585339 = 2378009) B2378009
theorem B1585415 : Blo 1583990 1585415 := bstep (se 1 (by rfl) ⟨1189061, by rfl⟩ : syracuseStep 1585415 = 2378123) B2378123
theorem B1782031 : Blo 1583990 1782031 := bstep (se 1 (by rfl) ⟨1336523, by rfl⟩ : syracuseStep 1782031 = 2673047) B2673047
theorem B1585423 : Blo 1583990 1585423 := bstep (se 1 (by rfl) ⟨1189067, by rfl⟩ : syracuseStep 1585423 = 2378135) B2378135
theorem B9146657 : Blo 1583990 9146657 := bstep (se 2 (by rfl) ⟨3429996, by rfl⟩ : syracuseStep 9146657 = 6859993) B6859993
theorem B2650411 : Blo 1583990 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B6861115 : Blo 1583990 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B1585467 : Blo 1583990 1585467 := bstep (se 1 (by rfl) ⟨1189100, by rfl⟩ : syracuseStep 1585467 = 2378201) B2378201
theorem B8565335 : Blo 1583990 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B2675335 : Blo 1583990 2675335 := bstep (se 1 (by rfl) ⟨2006501, by rfl⟩ : syracuseStep 2675335 = 4013003) B4013003
theorem B6017773 : Blo 1583990 6017773 := bstep (se 3 (by rfl) ⟨1128332, by rfl⟩ : syracuseStep 6017773 = 2256665) B2256665
theorem B1782535 : Blo 1583990 1782535 := bstep (se 1 (by rfl) ⟨1336901, by rfl⟩ : syracuseStep 1782535 = 2673803) B2673803
theorem B5346107 : Blo 1583990 5346107 := bstep (se 1 (by rfl) ⟨4009580, by rfl⟩ : syracuseStep 5346107 = 8019161) B8019161
theorem B4010867 : Blo 1583990 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B15438755 : Blo 1583990 15438755 := bstep (se 1 (by rfl) ⟨11579066, by rfl⟩ : syracuseStep 15438755 = 23158133) B23158133
theorem B3257273 : Blo 1583990 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B1782715 : Blo 1583990 1782715 := bstep (se 1 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 1782715 = 2674073) B2674073
theorem B15225803 : Blo 1583990 15225803 := bstep (se 1 (by rfl) ⟨11419352, by rfl⟩ : syracuseStep 15225803 = 22838705) B22838705
theorem B12039191 : Blo 1583990 12039191 := bstep (se 1 (by rfl) ⟨9029393, by rfl⟩ : syracuseStep 12039191 = 18058787) B18058787
theorem B6018077 : Blo 1583990 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B8025155 : Blo 1583990 8025155 := bstep (se 1 (by rfl) ⟨6018866, by rfl⟩ : syracuseStep 8025155 = 12037733) B12037733
theorem B1692943 : Blo 1583990 1692943 := bstep (se 1 (by rfl) ⟨1269707, by rfl⟩ : syracuseStep 1692943 = 2539415) B2539415
theorem B5346593 : Blo 1583990 5346593 := bstep (se 2 (by rfl) ⟨2004972, by rfl⟩ : syracuseStep 5346593 = 4009945) B4009945
theorem B4011383 : Blo 1583990 4011383 := bstep (se 1 (by rfl) ⟨3008537, by rfl⟩ : syracuseStep 4011383 = 6017075) B6017075
theorem B8025479 : Blo 1583990 8025479 := bstep (se 1 (by rfl) ⟨6019109, by rfl⟩ : syracuseStep 8025479 = 12038219) B12038219
theorem B1693063 : Blo 1583990 1693063 := bstep (se 1 (by rfl) ⟨1269797, by rfl⟩ : syracuseStep 1693063 = 2539595) B2539595
theorem B1783183 : Blo 1583990 1783183 := bstep (se 1 (by rfl) ⟨1337387, by rfl⟩ : syracuseStep 1783183 = 2674775) B2674775
theorem B6428089 : Blo 1583990 6428089 := bstep (se 2 (by rfl) ⟨2410533, by rfl⟩ : syracuseStep 6428089 = 4821067) B4821067
theorem B5076523 : Blo 1583990 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B2856583 : Blo 1583990 2856583 := bstep (se 1 (by rfl) ⟨2142437, by rfl⟩ : syracuseStep 2856583 = 4284875) B4284875
theorem B18290393 : Blo 1583990 18290393 := bstep (se 2 (by rfl) ⟨6858897, by rfl⟩ : syracuseStep 18290393 = 13717795) B13717795
theorem B1857287 : Blo 1583990 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B4511531 : Blo 1583990 4511531 := bstep (se 1 (by rfl) ⟨3383648, by rfl⟩ : syracuseStep 4511531 = 6767297) B6767297
theorem B5347187 : Blo 1583990 5347187 := bstep (se 1 (by rfl) ⟨4010390, by rfl⟩ : syracuseStep 5347187 = 8020781) B8020781
theorem B2004907 : Blo 1583990 2004907 := bstep (se 1 (by rfl) ⟨1503680, by rfl⟩ : syracuseStep 2004907 = 3007361) B3007361
theorem B6101021 : Blo 1583990 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B3807499 : Blo 1583990 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B4012375 : Blo 1583990 4012375 := bstep (se 1 (by rfl) ⟨3009281, by rfl⟩ : syracuseStep 4012375 = 6018563) B6018563
theorem B13539959 : Blo 1583990 13539959 := bstep (se 1 (by rfl) ⟨10154969, by rfl⟩ : syracuseStep 13539959 = 20309939) B20309939
theorem B6019703 : Blo 1583990 6019703 := bstep (se 1 (by rfl) ⟨4514777, by rfl⟩ : syracuseStep 6019703 = 9029555) B9029555
theorem B4012679 : Blo 1583990 4012679 := bstep (se 1 (by rfl) ⟨3009509, by rfl⟩ : syracuseStep 4012679 = 6019019) B6019019
theorem B296622809 : Blo 1583990 296622809 := bstep (se 2 (by rfl) ⟨111233553, by rfl⟩ : syracuseStep 296622809 = 222467107) B222467107
theorem B4012811 : Blo 1583990 4012811 := bstep (se 1 (by rfl) ⟨3009608, by rfl⟩ : syracuseStep 4012811 = 6019217) B6019217
theorem B8567585 : Blo 1583990 8567585 := bstep (se 2 (by rfl) ⟨3212844, by rfl⟩ : syracuseStep 8567585 = 6425689) B6425689
theorem B2005879 : Blo 1583990 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B4512647 : Blo 1583990 4512647 := bstep (se 1 (by rfl) ⟨3384485, by rfl⟩ : syracuseStep 4512647 = 6768971) B6768971
theorem B3431315 : Blo 1583990 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B5077907 : Blo 1583990 5077907 := bstep (se 1 (by rfl) ⟨3808430, by rfl⟩ : syracuseStep 5077907 = 7616861) B7616861
theorem B19053629 : Blo 1583990 19053629 := bstep (se 3 (by rfl) ⟨3572555, by rfl⟩ : syracuseStep 19053629 = 7145111) B7145111
theorem B4512829 : Blo 1583990 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B2006203 : Blo 1583990 2006203 := bstep (se 1 (by rfl) ⟨1504652, by rfl⟩ : syracuseStep 2006203 = 3009305) B3009305
theorem B5078305 : Blo 1583990 5078305 := bstep (se 2 (by rfl) ⟨1904364, by rfl⟩ : syracuseStep 5078305 = 3808729) B3808729
theorem B4283783 : Blo 1583990 4283783 := bstep (se 1 (by rfl) ⟨3212837, by rfl⟩ : syracuseStep 4283783 = 6425675) B6425675
theorem B4513171 : Blo 1583990 4513171 := bstep (se 1 (by rfl) ⟨3384878, by rfl⟩ : syracuseStep 4513171 = 6769757) B6769757
theorem B51387857 : Blo 1583990 51387857 := bstep (se 2 (by rfl) ⟨19270446, by rfl⟩ : syracuseStep 51387857 = 38540893) B38540893
theorem B8019485 : Blo 1583990 8019485 := bstep (se 3 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 8019485 = 3007307) B3007307
theorem B3808883 : Blo 1583990 3808883 := bstep (se 1 (by rfl) ⟨2856662, by rfl⟩ : syracuseStep 3808883 = 5713325) B5713325
theorem B14458673 : Blo 1583990 14458673 := bstep (se 2 (by rfl) ⟨5422002, by rfl⟩ : syracuseStep 14458673 = 10844005) B10844005
theorem B12844889 : Blo 1583990 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B5349455 : Blo 1583990 5349455 := bstep (se 1 (by rfl) ⟨4012091, by rfl⟩ : syracuseStep 5349455 = 8024183) B8024183
theorem B30458213 : Blo 1583990 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B2376041 : Blo 1583990 2376041 := bstep (se 2 (by rfl) ⟨891015, by rfl⟩ : syracuseStep 2376041 = 1782031) B1782031
theorem B5710223 : Blo 1583990 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B2376119 : Blo 1583990 2376119 := bstep (se 1 (by rfl) ⟨1782089, by rfl⟩ : syracuseStep 2376119 = 3564179) B3564179
theorem B5349833 : Blo 1583990 5349833 := bstep (se 2 (by rfl) ⟨2006187, by rfl⟩ : syracuseStep 5349833 = 4012375) B4012375
theorem B2376155 : Blo 1583990 2376155 := bstep (se 1 (by rfl) ⟨1782116, by rfl⟩ : syracuseStep 2376155 = 3564233) B3564233
theorem B3564071 : Blo 1583990 3564071 := bstep (se 1 (by rfl) ⟨2673053, by rfl⟩ : syracuseStep 3564071 = 5346107) B5346107
theorem B6423079 : Blo 1583990 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B2171515 : Blo 1583990 2171515 := bstep (se 1 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 2171515 = 3257273) B3257273
theorem B10150535 : Blo 1583990 10150535 := bstep (se 1 (by rfl) ⟨7612901, by rfl⟩ : syracuseStep 10150535 = 15225803) B15225803
theorem B5350103 : Blo 1583990 5350103 := bstep (se 1 (by rfl) ⟨4012577, by rfl⟩ : syracuseStep 5350103 = 8025155) B8025155
theorem B3564395 : Blo 1583990 3564395 := bstep (se 1 (by rfl) ⟨2673296, by rfl⟩ : syracuseStep 3564395 = 5346593) B5346593
theorem B3564449 : Blo 1583990 3564449 := bstep (se 2 (by rfl) ⟨1336668, by rfl⟩ : syracuseStep 3564449 = 2673337) B2673337
theorem B2376623 : Blo 1583990 2376623 := bstep (se 1 (by rfl) ⟨1782467, by rfl⟩ : syracuseStep 2376623 = 3564935) B3564935
theorem B5350319 : Blo 1583990 5350319 := bstep (se 1 (by rfl) ⟨4012739, by rfl⟩ : syracuseStep 5350319 = 8025479) B8025479
theorem B2376713 : Blo 1583990 2376713 := bstep (se 2 (by rfl) ⟨891267, by rfl⟩ : syracuseStep 2376713 = 1782535) B1782535
theorem B2376743 : Blo 1583990 2376743 := bstep (se 1 (by rfl) ⟨1782557, by rfl⟩ : syracuseStep 2376743 = 3565115) B3565115
theorem B2376827 : Blo 1583990 2376827 := bstep (se 1 (by rfl) ⟨1782620, by rfl⟩ : syracuseStep 2376827 = 3565241) B3565241
theorem B3007687 : Blo 1583990 3007687 := bstep (se 1 (by rfl) ⟨2255765, by rfl⟩ : syracuseStep 3007687 = 4511531) B4511531
theorem B43386101 : Blo 1583990 43386101 := bstep (se 5 (by rfl) ⟨2033723, by rfl⟩ : syracuseStep 43386101 = 4067447) B4067447
theorem B3564791 : Blo 1583990 3564791 := bstep (se 1 (by rfl) ⟨2673593, by rfl⟩ : syracuseStep 3564791 = 5347187) B5347187
theorem B2376953 : Blo 1583990 2376953 := bstep (se 2 (by rfl) ⟨891357, by rfl⟩ : syracuseStep 2376953 = 1782715) B1782715
theorem B2377055 : Blo 1583990 2377055 := bstep (se 1 (by rfl) ⟨1782791, by rfl⟩ : syracuseStep 2377055 = 3565583) B3565583
theorem B2377067 : Blo 1583990 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B9029029 : Blo 1583990 9029029 := bstep (se 4 (by rfl) ⟨846471, by rfl⟩ : syracuseStep 9029029 = 1692943) B1692943
theorem B7325147 : Blo 1583990 7325147 := bstep (se 1 (by rfl) ⟨5493860, by rfl⟩ : syracuseStep 7325147 = 10987721) B10987721
theorem B2033191 : Blo 1583990 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B2377295 : Blo 1583990 2377295 := bstep (se 1 (by rfl) ⟨1782971, by rfl⟩ : syracuseStep 2377295 = 3565943) B3565943
theorem B7612093 : Blo 1583990 7612093 := bstep (se 3 (by rfl) ⟨1427267, by rfl⟩ : syracuseStep 7612093 = 2854535) B2854535
theorem B2377415 : Blo 1583990 2377415 := bstep (se 1 (by rfl) ⟨1783061, by rfl⟩ : syracuseStep 2377415 = 3566123) B3566123
theorem B6014675 : Blo 1583990 6014675 := bstep (se 1 (by rfl) ⟨4511006, by rfl⟩ : syracuseStep 6014675 = 9022013) B9022013
theorem B8021753 : Blo 1583990 8021753 := bstep (se 2 (by rfl) ⟨3008157, by rfl⟩ : syracuseStep 8021753 = 6016315) B6016315
theorem B3008249 : Blo 1583990 3008249 := bstep (se 2 (by rfl) ⟨1128093, by rfl⟩ : syracuseStep 3008249 = 2256187) B2256187
theorem B197748539 : Blo 1583990 197748539 := bstep (se 1 (by rfl) ⟨148311404, by rfl⟩ : syracuseStep 197748539 = 296622809) B296622809
theorem B3565385 : Blo 1583990 3565385 := bstep (se 2 (by rfl) ⟨1337019, by rfl⟩ : syracuseStep 3565385 = 2674039) B2674039
theorem B2377577 : Blo 1583990 2377577 := bstep (se 2 (by rfl) ⟨891591, by rfl⟩ : syracuseStep 2377577 = 1783183) B1783183
theorem B5711723 : Blo 1583990 5711723 := bstep (se 1 (by rfl) ⟨4283792, by rfl⟩ : syracuseStep 5711723 = 8567585) B8567585
theorem B8570785 : Blo 1583990 8570785 := bstep (se 2 (by rfl) ⟨3214044, by rfl⟩ : syracuseStep 8570785 = 6428089) B6428089
theorem B3008431 : Blo 1583990 3008431 := bstep (se 1 (by rfl) ⟨2256323, by rfl⟩ : syracuseStep 3008431 = 4512647) B4512647
theorem B2287543 : Blo 1583990 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B3385271 : Blo 1583990 3385271 := bstep (se 1 (by rfl) ⟨2538953, by rfl⟩ : syracuseStep 3385271 = 5077907) B5077907
theorem B2377655 : Blo 1583990 2377655 := bstep (se 1 (by rfl) ⟨1783241, by rfl⟩ : syracuseStep 2377655 = 3566483) B3566483
theorem B2377691 : Blo 1583990 2377691 := bstep (se 1 (by rfl) ⟨1783268, by rfl⟩ : syracuseStep 2377691 = 3566537) B3566537
theorem B34260995 : Blo 1583990 34260995 := bstep (se 1 (by rfl) ⟨25695746, by rfl⟩ : syracuseStep 34260995 = 51391493) B51391493
theorem B20580389 : Blo 1583990 20580389 := bstep (se 4 (by rfl) ⟨1929411, by rfl⟩ : syracuseStep 20580389 = 3858823) B3858823
theorem B6768697 : Blo 1583990 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B8022401 : Blo 1583990 8022401 := bstep (se 2 (by rfl) ⟨3008400, by rfl⟩ : syracuseStep 8022401 = 6016801) B6016801
theorem B2378159 : Blo 1583990 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B2673209 : Blo 1583990 2673209 := bstep (se 2 (by rfl) ⟨1002453, by rfl⟩ : syracuseStep 2673209 = 2004907) B2004907
theorem B8563259 : Blo 1583990 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B3566177 : Blo 1583990 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B6097771 : Blo 1583990 6097771 := bstep (se 1 (by rfl) ⟨4573328, by rfl⟩ : syracuseStep 6097771 = 9146657) B9146657
theorem B1583995 : Blo 1583990 1583995 := bstep (se 1 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 1583995 = 2375993) B2375993
theorem B1584047 : Blo 1583990 1584047 := bstep (se 1 (by rfl) ⟨1188035, by rfl⟩ : syracuseStep 1584047 = 2376071) B2376071
theorem B3566519 : Blo 1583990 3566519 := bstep (se 1 (by rfl) ⟨2674889, by rfl⟩ : syracuseStep 3566519 = 5349779) B5349779
theorem B1584071 : Blo 1583990 1584071 := bstep (se 1 (by rfl) ⟨1188053, by rfl⟩ : syracuseStep 1584071 = 2376107) B2376107
theorem B1584091 : Blo 1583990 1584091 := bstep (se 1 (by rfl) ⟨1188068, by rfl⟩ : syracuseStep 1584091 = 2376137) B2376137
theorem B1584167 : Blo 1583990 1584167 := bstep (se 1 (by rfl) ⟨1188125, by rfl⟩ : syracuseStep 1584167 = 2376251) B2376251
theorem B3533881 : Blo 1583990 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B1584207 : Blo 1583990 1584207 := bstep (se 1 (by rfl) ⟨1188155, by rfl⟩ : syracuseStep 1584207 = 2376311) B2376311
theorem B1584223 : Blo 1583990 1584223 := bstep (se 1 (by rfl) ⟨1188167, by rfl⟩ : syracuseStep 1584223 = 2376335) B2376335
theorem B1584251 : Blo 1583990 1584251 := bstep (se 1 (by rfl) ⟨1188188, by rfl⟩ : syracuseStep 1584251 = 2376377) B2376377
theorem B8023211 : Blo 1583990 8023211 := bstep (se 1 (by rfl) ⟨6017408, by rfl⟩ : syracuseStep 8023211 = 12034817) B12034817
theorem B3009707 : Blo 1583990 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B1584303 : Blo 1583990 1584303 := bstep (se 1 (by rfl) ⟨1188227, by rfl⟩ : syracuseStep 1584303 = 2376455) B2376455
theorem B1584327 : Blo 1583990 1584327 := bstep (se 1 (by rfl) ⟨1188245, by rfl⟩ : syracuseStep 1584327 = 2376491) B2376491
theorem B1584347 : Blo 1583990 1584347 := bstep (se 1 (by rfl) ⟨1188260, by rfl⟩ : syracuseStep 1584347 = 2376521) B2376521
theorem B2673911 : Blo 1583990 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B10292503 : Blo 1583990 10292503 := bstep (se 1 (by rfl) ⟨7719377, by rfl⟩ : syracuseStep 10292503 = 15438755) B15438755
theorem B1584423 : Blo 1583990 1584423 := bstep (se 1 (by rfl) ⟨1188317, by rfl⟩ : syracuseStep 1584423 = 2376635) B2376635
theorem B1584463 : Blo 1583990 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B1584479 : Blo 1583990 1584479 := bstep (se 1 (by rfl) ⟨1188359, by rfl⟩ : syracuseStep 1584479 = 2376719) B2376719
theorem B1584507 : Blo 1583990 1584507 := bstep (se 1 (by rfl) ⟨1188380, by rfl⟩ : syracuseStep 1584507 = 2376761) B2376761
theorem B3009935 : Blo 1583990 3009935 := bstep (se 1 (by rfl) ⟨2257451, by rfl⟩ : syracuseStep 3009935 = 4514903) B4514903
theorem B1584559 : Blo 1583990 1584559 := bstep (se 1 (by rfl) ⟨1188419, by rfl⟩ : syracuseStep 1584559 = 2376839) B2376839
theorem B1584583 : Blo 1583990 1584583 := bstep (se 1 (by rfl) ⟨1188437, by rfl⟩ : syracuseStep 1584583 = 2376875) B2376875
theorem B1584603 : Blo 1583990 1584603 := bstep (se 1 (by rfl) ⟨1188452, by rfl⟩ : syracuseStep 1584603 = 2376905) B2376905
theorem B7613939 : Blo 1583990 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B3567113 : Blo 1583990 3567113 := bstep (se 2 (by rfl) ⟨1337667, by rfl⟩ : syracuseStep 3567113 = 2675335) B2675335
theorem B9023015 : Blo 1583990 9023015 := bstep (se 1 (by rfl) ⟨6767261, by rfl⟩ : syracuseStep 9023015 = 13534523) B13534523
theorem B1584679 : Blo 1583990 1584679 := bstep (se 1 (by rfl) ⟨1188509, by rfl⟩ : syracuseStep 1584679 = 2377019) B2377019
theorem B1584719 : Blo 1583990 1584719 := bstep (se 1 (by rfl) ⟨1188539, by rfl⟩ : syracuseStep 1584719 = 2377079) B2377079
theorem B2674255 : Blo 1583990 2674255 := bstep (se 1 (by rfl) ⟨2005691, by rfl⟩ : syracuseStep 2674255 = 4011383) B4011383
theorem B1584735 : Blo 1583990 1584735 := bstep (se 1 (by rfl) ⟨1188551, by rfl⟩ : syracuseStep 1584735 = 2377103) B2377103
theorem B1584763 : Blo 1583990 1584763 := bstep (se 1 (by rfl) ⟨1188572, by rfl⟩ : syracuseStep 1584763 = 2377145) B2377145
theorem B8023697 : Blo 1583990 8023697 := bstep (se 2 (by rfl) ⟨3008886, by rfl⟩ : syracuseStep 8023697 = 6017773) B6017773
theorem B1584815 : Blo 1583990 1584815 := bstep (se 1 (by rfl) ⟨1188611, by rfl⟩ : syracuseStep 1584815 = 2377223) B2377223
theorem B1584839 : Blo 1583990 1584839 := bstep (se 1 (by rfl) ⟨1188629, by rfl⟩ : syracuseStep 1584839 = 2377259) B2377259
theorem B1584859 : Blo 1583990 1584859 := bstep (se 1 (by rfl) ⟨1188644, by rfl⟩ : syracuseStep 1584859 = 2377289) B2377289
theorem B9023197 : Blo 1583990 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B1584935 : Blo 1583990 1584935 := bstep (se 1 (by rfl) ⟨1188701, by rfl⟩ : syracuseStep 1584935 = 2377403) B2377403
theorem B12193595 : Blo 1583990 12193595 := bstep (se 1 (by rfl) ⟨9145196, by rfl⟩ : syracuseStep 12193595 = 18290393) B18290393
theorem B2674505 : Blo 1583990 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B1584975 : Blo 1583990 1584975 := bstep (se 1 (by rfl) ⟨1188731, by rfl⟩ : syracuseStep 1584975 = 2377463) B2377463
theorem B1584991 : Blo 1583990 1584991 := bstep (se 1 (by rfl) ⟨1188743, by rfl⟩ : syracuseStep 1584991 = 2377487) B2377487
theorem B1585019 : Blo 1583990 1585019 := bstep (se 1 (by rfl) ⟨1188764, by rfl⟩ : syracuseStep 1585019 = 2377529) B2377529
theorem B1585071 : Blo 1583990 1585071 := bstep (se 1 (by rfl) ⟨1188803, by rfl⟩ : syracuseStep 1585071 = 2377607) B2377607
theorem B1585095 : Blo 1583990 1585095 := bstep (se 1 (by rfl) ⟨1188821, by rfl⟩ : syracuseStep 1585095 = 2377643) B2377643
theorem B2256859 : Blo 1583990 2256859 := bstep (se 1 (by rfl) ⟨1692644, by rfl⟩ : syracuseStep 2256859 = 3385289) B3385289
theorem B1585115 : Blo 1583990 1585115 := bstep (se 1 (by rfl) ⟨1188836, by rfl⟩ : syracuseStep 1585115 = 2377673) B2377673
theorem B4067347 : Blo 1583990 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B1585191 : Blo 1583990 1585191 := bstep (se 1 (by rfl) ⟨1188893, by rfl⟩ : syracuseStep 1585191 = 2377787) B2377787
theorem B1585231 : Blo 1583990 1585231 := bstep (se 1 (by rfl) ⟨1188923, by rfl⟩ : syracuseStep 1585231 = 2377847) B2377847
theorem B6017105 : Blo 1583990 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B1585247 : Blo 1583990 1585247 := bstep (se 1 (by rfl) ⟨1188935, by rfl⟩ : syracuseStep 1585247 = 2377871) B2377871
theorem B1585275 : Blo 1583990 1585275 := bstep (se 1 (by rfl) ⟨1188956, by rfl⟩ : syracuseStep 1585275 = 2377913) B2377913
theorem B1585327 : Blo 1583990 1585327 := bstep (se 1 (by rfl) ⟨1188995, by rfl⟩ : syracuseStep 1585327 = 2377991) B2377991
theorem B1585351 : Blo 1583990 1585351 := bstep (se 1 (by rfl) ⟨1189013, by rfl⟩ : syracuseStep 1585351 = 2378027) B2378027
theorem B1585371 : Blo 1583990 1585371 := bstep (se 1 (by rfl) ⟨1189028, by rfl⟩ : syracuseStep 1585371 = 2378057) B2378057
theorem B2674937 : Blo 1583990 2674937 := bstep (se 2 (by rfl) ⟨1003101, by rfl⟩ : syracuseStep 2674937 = 2006203) B2006203
theorem B1585447 : Blo 1583990 1585447 := bstep (se 1 (by rfl) ⟨1189085, by rfl⟩ : syracuseStep 1585447 = 2378171) B2378171
theorem B1585487 : Blo 1583990 1585487 := bstep (se 1 (by rfl) ⟨1189115, by rfl⟩ : syracuseStep 1585487 = 2378231) B2378231
theorem B6771073 : Blo 1583990 6771073 := bstep (se 2 (by rfl) ⟨2539152, by rfl⟩ : syracuseStep 6771073 = 5078305) B5078305
theorem B2675119 : Blo 1583990 2675119 := bstep (se 1 (by rfl) ⟨2006339, by rfl⟩ : syracuseStep 2675119 = 4012679) B4012679
theorem B2675207 : Blo 1583990 2675207 := bstep (se 1 (by rfl) ⟨2006405, by rfl⟩ : syracuseStep 2675207 = 4012811) B4012811
theorem B2257417 : Blo 1583990 2257417 := bstep (se 2 (by rfl) ⟨846531, by rfl⟩ : syracuseStep 2257417 = 1693063) B1693063
theorem B6017561 : Blo 1583990 6017561 := bstep (se 2 (by rfl) ⟨2256585, by rfl⟩ : syracuseStep 6017561 = 4513171) B4513171
theorem B4010593 : Blo 1583990 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B4952765 : Blo 1583990 4952765 := bstep (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) B1857287
theorem B12702419 : Blo 1583990 12702419 := bstep (se 1 (by rfl) ⟨9526814, by rfl⟩ : syracuseStep 12702419 = 19053629) B19053629
theorem B38556461 : Blo 1583990 38556461 := bstep (se 3 (by rfl) ⟨7229336, by rfl⟩ : syracuseStep 38556461 = 14458673) B14458673
theorem B2855855 : Blo 1583990 2855855 := bstep (se 1 (by rfl) ⟨2141891, by rfl⟩ : syracuseStep 2855855 = 4283783) B4283783
theorem B5346323 : Blo 1583990 5346323 := bstep (se 1 (by rfl) ⟨4009742, by rfl⟩ : syracuseStep 5346323 = 8019485) B8019485
theorem B1782823 : Blo 1583990 1782823 := bstep (se 1 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 1782823 = 2674235) B2674235
theorem B5346647 : Blo 1583990 5346647 := bstep (se 1 (by rfl) ⟨4009985, by rfl⟩ : syracuseStep 5346647 = 8019971) B8019971
theorem B11580761 : Blo 1583990 11580761 := bstep (se 2 (by rfl) ⟨4342785, by rfl⟩ : syracuseStep 11580761 = 8685571) B8685571
theorem B12539225 : Blo 1583990 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B34739675 : Blo 1583990 34739675 := bstep (se 1 (by rfl) ⟨26054756, by rfl⟩ : syracuseStep 34739675 = 52109513) B52109513
theorem B4011545 : Blo 1583990 4011545 := bstep (se 2 (by rfl) ⟨1504329, by rfl⟩ : syracuseStep 4011545 = 3008659) B3008659
theorem B3806759 : Blo 1583990 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B4511371 : Blo 1583990 4511371 := bstep (se 1 (by rfl) ⟨3383528, by rfl⟩ : syracuseStep 4511371 = 6767057) B6767057
theorem B5076665 : Blo 1583990 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B6018745 : Blo 1583990 6018745 := bstep (se 2 (by rfl) ⟨2257029, by rfl⟩ : syracuseStep 6018745 = 4514059) B4514059
theorem B9148153 : Blo 1583990 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B2856799 : Blo 1583990 2856799 := bstep (se 1 (by rfl) ⟨2142599, by rfl⟩ : syracuseStep 2856799 = 4285199) B4285199
theorem B8025965 : Blo 1583990 8025965 := bstep (se 3 (by rfl) ⟨1504868, by rfl⟩ : syracuseStep 8025965 = 3009737) B3009737
theorem B8026127 : Blo 1583990 8026127 := bstep (se 1 (by rfl) ⟨6019595, by rfl⟩ : syracuseStep 8026127 = 12039191) B12039191
theorem B4012051 : Blo 1583990 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B25418033 : Blo 1583990 25418033 := bstep (se 2 (by rfl) ⟨9531762, by rfl⟩ : syracuseStep 25418033 = 19063525) B19063525
theorem B2537801 : Blo 1583990 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B5347727 : Blo 1583990 5347727 := bstep (se 1 (by rfl) ⟨4010795, by rfl⟩ : syracuseStep 5347727 = 8021591) B8021591
theorem B2537993 : Blo 1583990 2537993 := bstep (se 2 (by rfl) ⟨951747, by rfl⟩ : syracuseStep 2537993 = 1903495) B1903495
theorem B12360215 : Blo 1583990 12360215 := bstep (se 1 (by rfl) ⟨9270161, by rfl⟩ : syracuseStep 12360215 = 18540323) B18540323
theorem B5348051 : Blo 1583990 5348051 := bstep (se 1 (by rfl) ⟨4011038, by rfl⟩ : syracuseStep 5348051 = 8022077) B8022077
theorem B10157021 : Blo 1583990 10157021 := bstep (se 3 (by rfl) ⟨1904441, by rfl⟩ : syracuseStep 10157021 = 3808883) B3808883
theorem B9026639 : Blo 1583990 9026639 := bstep (se 1 (by rfl) ⟨6769979, by rfl⟩ : syracuseStep 9026639 = 13539959) B13539959
theorem B4013135 : Blo 1583990 4013135 := bstep (se 1 (by rfl) ⟨3009851, by rfl⟩ : syracuseStep 4013135 = 6019703) B6019703
theorem B3808777 : Blo 1583990 3808777 := bstep (se 2 (by rfl) ⟨1428291, by rfl⟩ : syracuseStep 3808777 = 2856583) B2856583
theorem B34258571 : Blo 1583990 34258571 := bstep (se 1 (by rfl) ⟨25693928, by rfl⟩ : syracuseStep 34258571 = 51387857) B51387857
theorem B5709635 : Blo 1583990 5709635 := bstep (se 1 (by rfl) ⟨4282226, by rfl⟩ : syracuseStep 5709635 = 8564453) B8564453
theorem B5349239 : Blo 1583990 5349239 := bstep (se 1 (by rfl) ⟨4011929, by rfl⟩ : syracuseStep 5349239 = 8023859) B8023859
theorem B5349401 : Blo 1583990 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B5423129 : Blo 1583990 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B2376047 : Blo 1583990 2376047 := bstep (se 1 (by rfl) ⟨1782035, by rfl⟩ : syracuseStep 2376047 = 3564071) B3564071
theorem B6767023 : Blo 1583990 6767023 := bstep (se 1 (by rfl) ⟨5075267, by rfl⟩ : syracuseStep 6767023 = 10150535) B10150535
theorem B3301843 : Blo 1583990 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B9028097 : Blo 1583990 9028097 := bstep (se 2 (by rfl) ⟨3385536, by rfl⟩ : syracuseStep 9028097 = 6771073) B6771073
theorem B2376263 : Blo 1583990 2376263 := bstep (se 1 (by rfl) ⟨1782197, by rfl⟩ : syracuseStep 2376263 = 3564395) B3564395
theorem B2376299 : Blo 1583990 2376299 := bstep (se 1 (by rfl) ⟨1782224, by rfl⟩ : syracuseStep 2376299 = 3564449) B3564449
theorem B3564215 : Blo 1583990 3564215 := bstep (se 1 (by rfl) ⟨2673161, by rfl⟩ : syracuseStep 3564215 = 5346323) B5346323
theorem B2376527 : Blo 1583990 2376527 := bstep (se 1 (by rfl) ⟨1782395, by rfl⟩ : syracuseStep 2376527 = 3564791) B3564791
theorem B3564431 : Blo 1583990 3564431 := bstep (se 1 (by rfl) ⟨2673323, by rfl⟩ : syracuseStep 3564431 = 5346647) B5346647
theorem B4883431 : Blo 1583990 4883431 := bstep (se 1 (by rfl) ⟨3662573, by rfl⟩ : syracuseStep 4883431 = 7325147) B7325147
theorem B23159783 : Blo 1583990 23159783 := bstep (se 1 (by rfl) ⟨17369837, by rfl⟩ : syracuseStep 23159783 = 34739675) B34739675
theorem B3384443 : Blo 1583990 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B2376923 : Blo 1583990 2376923 := bstep (se 1 (by rfl) ⟨1782692, by rfl⟩ : syracuseStep 2376923 = 3565385) B3565385
theorem B5350643 : Blo 1583990 5350643 := bstep (se 1 (by rfl) ⟨4012982, by rfl⟩ : syracuseStep 5350643 = 8025965) B8025965
theorem B22840663 : Blo 1583990 22840663 := bstep (se 1 (by rfl) ⟨17130497, by rfl⟩ : syracuseStep 22840663 = 34260995) B34260995
theorem B5350751 : Blo 1583990 5350751 := bstep (se 1 (by rfl) ⟨4013063, by rfl⟩ : syracuseStep 5350751 = 8026127) B8026127
theorem B6767981 : Blo 1583990 6767981 := bstep (se 3 (by rfl) ⟨1268996, by rfl⟩ : syracuseStep 6767981 = 2537993) B2537993
theorem B2377097 : Blo 1583990 2377097 := bstep (se 2 (by rfl) ⟨891411, by rfl⟩ : syracuseStep 2377097 = 1782823) B1782823
theorem B4711841 : Blo 1583990 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3565151 : Blo 1583990 3565151 := bstep (se 1 (by rfl) ⟨2673863, by rfl⟩ : syracuseStep 3565151 = 5347727) B5347727
theorem B13723337 : Blo 1583990 13723337 := bstep (se 2 (by rfl) ⟨5146251, by rfl⟩ : syracuseStep 13723337 = 10292503) B10292503
theorem B2377451 : Blo 1583990 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B3565367 : Blo 1583990 3565367 := bstep (se 1 (by rfl) ⟨2674025, by rfl⟩ : syracuseStep 3565367 = 5348051) B5348051
theorem B2377679 : Blo 1583990 2377679 := bstep (se 1 (by rfl) ⟨1783259, by rfl⟩ : syracuseStep 2377679 = 3566519) B3566519
theorem B3565673 : Blo 1583990 3565673 := bstep (se 2 (by rfl) ⟨1337127, by rfl⟩ : syracuseStep 3565673 = 2674255) B2674255
theorem B6015161 : Blo 1583990 6015161 := bstep (se 2 (by rfl) ⟨2255685, by rfl⟩ : syracuseStep 6015161 = 4511371) B4511371
theorem B2378075 : Blo 1583990 2378075 := bstep (se 1 (by rfl) ⟨1783556, by rfl⟩ : syracuseStep 2378075 = 3567113) B3567113
theorem B6015343 : Blo 1583990 6015343 := bstep (se 1 (by rfl) ⟨4511507, by rfl⟩ : syracuseStep 6015343 = 9023015) B9023015
theorem B8129063 : Blo 1583990 8129063 := bstep (se 1 (by rfl) ⟨6096797, by rfl⟩ : syracuseStep 8129063 = 12193595) B12193595
theorem B3050057 : Blo 1583990 3050057 := bstep (se 2 (by rfl) ⟨1143771, by rfl⟩ : syracuseStep 3050057 = 2287543) B2287543
theorem B3566159 : Blo 1583990 3566159 := bstep (se 1 (by rfl) ⟨2674619, by rfl⟩ : syracuseStep 3566159 = 5349239) B5349239
theorem B3009145 : Blo 1583990 3009145 := bstep (se 2 (by rfl) ⟨1128429, by rfl⟩ : syracuseStep 3009145 = 2256859) B2256859
theorem B3566303 : Blo 1583990 3566303 := bstep (se 1 (by rfl) ⟨2674727, by rfl⟩ : syracuseStep 3566303 = 5349455) B5349455
theorem B1584027 : Blo 1583990 1584027 := bstep (se 1 (by rfl) ⟨1188020, by rfl⟩ : syracuseStep 1584027 = 2376041) B2376041
theorem B1584079 : Blo 1583990 1584079 := bstep (se 1 (by rfl) ⟨1188059, by rfl⟩ : syracuseStep 1584079 = 2376119) B2376119
theorem B3566555 : Blo 1583990 3566555 := bstep (se 1 (by rfl) ⟨2674916, by rfl⟩ : syracuseStep 3566555 = 5349833) B5349833
theorem B1584103 : Blo 1583990 1584103 := bstep (se 1 (by rfl) ⟨1188077, by rfl⟩ : syracuseStep 1584103 = 2376155) B2376155
theorem B3566735 : Blo 1583990 3566735 := bstep (se 1 (by rfl) ⟨2675051, by rfl⟩ : syracuseStep 3566735 = 5350103) B5350103
theorem B3566825 : Blo 1583990 3566825 := bstep (se 2 (by rfl) ⟨1337559, by rfl⟩ : syracuseStep 3566825 = 2675119) B2675119
theorem B1584415 : Blo 1583990 1584415 := bstep (se 1 (by rfl) ⟨1188311, by rfl⟩ : syracuseStep 1584415 = 2376623) B2376623
theorem B3566879 : Blo 1583990 3566879 := bstep (se 1 (by rfl) ⟨2675159, by rfl⟩ : syracuseStep 3566879 = 5350319) B5350319
theorem B1584475 : Blo 1583990 1584475 := bstep (se 1 (by rfl) ⟨1188356, by rfl⟩ : syracuseStep 1584475 = 2376713) B2376713
theorem B3009889 : Blo 1583990 3009889 := bstep (se 2 (by rfl) ⟨1128708, by rfl⟩ : syracuseStep 3009889 = 2257417) B2257417
theorem B1584495 : Blo 1583990 1584495 := bstep (se 1 (by rfl) ⟨1188371, by rfl⟩ : syracuseStep 1584495 = 2376743) B2376743
theorem B8564105 : Blo 1583990 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B1584551 : Blo 1583990 1584551 := bstep (se 1 (by rfl) ⟨1188413, by rfl⟩ : syracuseStep 1584551 = 2376827) B2376827
theorem B2895353 : Blo 1583990 2895353 := bstep (se 2 (by rfl) ⟨1085757, by rfl⟩ : syracuseStep 2895353 = 2171515) B2171515
theorem B1584635 : Blo 1583990 1584635 := bstep (se 1 (by rfl) ⟨1188476, by rfl⟩ : syracuseStep 1584635 = 2376953) B2376953
theorem B1584703 : Blo 1583990 1584703 := bstep (se 1 (by rfl) ⟨1188527, by rfl⟩ : syracuseStep 1584703 = 2377055) B2377055
theorem B1584711 : Blo 1583990 1584711 := bstep (se 1 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 1584711 = 2377067) B2377067
theorem B2674363 : Blo 1583990 2674363 := bstep (se 1 (by rfl) ⟨2005772, by rfl⟩ : syracuseStep 2674363 = 4011545) B4011545
theorem B1584863 : Blo 1583990 1584863 := bstep (se 1 (by rfl) ⟨1188647, by rfl⟩ : syracuseStep 1584863 = 2377295) B2377295
theorem B1584943 : Blo 1583990 1584943 := bstep (se 1 (by rfl) ⟨1188707, by rfl⟩ : syracuseStep 1584943 = 2377415) B2377415
theorem B4009783 : Blo 1583990 4009783 := bstep (se 1 (by rfl) ⟨3007337, by rfl⟩ : syracuseStep 4009783 = 6014675) B6014675
theorem B8130361 : Blo 1583990 8130361 := bstep (se 2 (by rfl) ⟨3048885, by rfl⟩ : syracuseStep 8130361 = 6097771) B6097771
theorem B1585051 : Blo 1583990 1585051 := bstep (se 1 (by rfl) ⟨1188788, by rfl⟩ : syracuseStep 1585051 = 2377577) B2377577
theorem B1585103 : Blo 1583990 1585103 := bstep (se 1 (by rfl) ⟨1188827, by rfl⟩ : syracuseStep 1585103 = 2377655) B2377655
theorem B1585127 : Blo 1583990 1585127 := bstep (se 1 (by rfl) ⟨1188845, by rfl⟩ : syracuseStep 1585127 = 2377691) B2377691
theorem B22835357 : Blo 1583990 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B16945355 : Blo 1583990 16945355 := bstep (se 1 (by rfl) ⟨12709016, by rfl⟩ : syracuseStep 16945355 = 25418033) B25418033
theorem B1691867 : Blo 1583990 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B4010249 : Blo 1583990 4010249 := bstep (se 2 (by rfl) ⟨1503843, by rfl⟩ : syracuseStep 4010249 = 3007687) B3007687
theorem B1585439 : Blo 1583990 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B1782139 : Blo 1583990 1782139 := bstep (se 1 (by rfl) ⟨1336604, by rfl⟩ : syracuseStep 1782139 = 2673209) B2673209
theorem B12038705 : Blo 1583990 12038705 := bstep (se 2 (by rfl) ⟨4514514, by rfl⟩ : syracuseStep 12038705 = 9029029) B9029029
theorem B6771347 : Blo 1583990 6771347 := bstep (se 1 (by rfl) ⟨5078510, by rfl⟩ : syracuseStep 6771347 = 10157021) B10157021
theorem B6017759 : Blo 1583990 6017759 := bstep (se 1 (by rfl) ⟨4513319, by rfl⟩ : syracuseStep 6017759 = 9026639) B9026639
theorem B2675423 : Blo 1583990 2675423 := bstep (se 1 (by rfl) ⟨2006567, by rfl⟩ : syracuseStep 2675423 = 4013135) B4013135
theorem B1782607 : Blo 1583990 1782607 := bstep (se 1 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 1782607 = 2673911) B2673911
theorem B8024993 : Blo 1583990 8024993 := bstep (se 2 (by rfl) ⟨3009372, by rfl⟩ : syracuseStep 8024993 = 6018745) B6018745
theorem B12030929 : Blo 1583990 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B5075959 : Blo 1583990 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B7615613 : Blo 1583990 7615613 := bstep (se 3 (by rfl) ⟨1427927, by rfl⟩ : syracuseStep 7615613 = 2855855) B2855855
theorem B3806423 : Blo 1583990 3806423 := bstep (se 1 (by rfl) ⟨2854817, by rfl⟩ : syracuseStep 3806423 = 5709635) B5709635
theorem B1783003 : Blo 1583990 1783003 := bstep (se 1 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 1783003 = 2674505) B2674505
theorem B4011241 : Blo 1583990 4011241 := bstep (se 2 (by rfl) ⟨1504215, by rfl⟩ : syracuseStep 4011241 = 3008431) B3008431
theorem B4011403 : Blo 1583990 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B9024929 : Blo 1583990 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B1783291 : Blo 1583990 1783291 := bstep (se 1 (by rfl) ⟨1337468, by rfl⟩ : syracuseStep 1783291 = 2674937) B2674937
theorem B20305475 : Blo 1583990 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B1783471 : Blo 1583990 1783471 := bstep (se 1 (by rfl) ⟨1337603, by rfl⟩ : syracuseStep 1783471 = 2675207) B2675207
theorem B4011707 : Blo 1583990 4011707 := bstep (se 1 (by rfl) ⟨3008780, by rfl⟩ : syracuseStep 4011707 = 6017561) B6017561
theorem B8468279 : Blo 1583990 8468279 := bstep (se 1 (by rfl) ⟨6351209, by rfl⟩ : syracuseStep 8468279 = 12702419) B12702419
theorem B25704307 : Blo 1583990 25704307 := bstep (se 1 (by rfl) ⟨19278230, by rfl⟩ : syracuseStep 25704307 = 38556461) B38556461
theorem B5347457 : Blo 1583990 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B28924067 : Blo 1583990 28924067 := bstep (se 1 (by rfl) ⟨21693050, by rfl⟩ : syracuseStep 28924067 = 43386101) B43386101
theorem B30882029 : Blo 1583990 30882029 := bstep (se 3 (by rfl) ⟨5790380, by rfl⟩ : syracuseStep 30882029 = 11580761) B11580761
theorem B33437933 : Blo 1583990 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B2537839 : Blo 1583990 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B15227261 : Blo 1583990 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B5347835 : Blo 1583990 5347835 := bstep (se 1 (by rfl) ⟨4010876, by rfl⟩ : syracuseStep 5347835 = 8021753) B8021753
theorem B2005499 : Blo 1583990 2005499 := bstep (se 1 (by rfl) ⟨1504124, by rfl⟩ : syracuseStep 2005499 = 3008249) B3008249
theorem B131832359 : Blo 1583990 131832359 := bstep (se 1 (by rfl) ⟨98874269, by rfl⟩ : syracuseStep 131832359 = 197748539) B197748539
theorem B3807815 : Blo 1583990 3807815 := bstep (se 1 (by rfl) ⟨2855861, by rfl⟩ : syracuseStep 3807815 = 5711723) B5711723
theorem B13720259 : Blo 1583990 13720259 := bstep (se 1 (by rfl) ⟨10290194, by rfl⟩ : syracuseStep 13720259 = 20580389) B20580389
theorem B5348267 : Blo 1583990 5348267 := bstep (se 1 (by rfl) ⟨4011200, by rfl⟩ : syracuseStep 5348267 = 8022401) B8022401
theorem B8240143 : Blo 1583990 8240143 := bstep (se 1 (by rfl) ⟨6180107, by rfl⟩ : syracuseStep 8240143 = 12360215) B12360215
theorem B15236261 : Blo 1583990 15236261 := bstep (se 4 (by rfl) ⟨1428399, by rfl⟩ : syracuseStep 15236261 = 2856799) B2856799
theorem B5078369 : Blo 1583990 5078369 := bstep (se 2 (by rfl) ⟨1904388, by rfl⟩ : syracuseStep 5078369 = 3808777) B3808777
theorem B2710921 : Blo 1583990 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B5348807 : Blo 1583990 5348807 := bstep (se 1 (by rfl) ⟨4011605, by rfl⟩ : syracuseStep 5348807 = 8023211) B8023211
theorem B2006471 : Blo 1583990 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B10149457 : Blo 1583990 10149457 := bstep (se 2 (by rfl) ⟨3806046, by rfl⟩ : syracuseStep 10149457 = 7612093) B7612093
theorem B2006623 : Blo 1583990 2006623 := bstep (se 1 (by rfl) ⟨1504967, by rfl⟩ : syracuseStep 2006623 = 3009935) B3009935
theorem B12197537 : Blo 1583990 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B22839047 : Blo 1583990 22839047 := bstep (se 1 (by rfl) ⟨17129285, by rfl⟩ : syracuseStep 22839047 = 34258571) B34258571
theorem B5349131 : Blo 1583990 5349131 := bstep (se 1 (by rfl) ⟨4011848, by rfl⟩ : syracuseStep 5349131 = 8023697) B8023697
theorem B9027389 : Blo 1583990 9027389 := bstep (se 3 (by rfl) ⟨1692635, by rfl⟩ : syracuseStep 9027389 = 3385271) B3385271
theorem B11427713 : Blo 1583990 11427713 := bstep (se 2 (by rfl) ⟨4285392, by rfl⟩ : syracuseStep 11427713 = 8570785) B8570785
theorem B11296903 : Blo 1583990 11296903 := bstep (se 1 (by rfl) ⟨8472677, by rfl⟩ : syracuseStep 11296903 = 16945355) B16945355
theorem B4514231 : Blo 1583990 4514231 := bstep (se 1 (by rfl) ⟨3385673, by rfl⟩ : syracuseStep 4514231 = 6771347) B6771347
theorem B2376143 : Blo 1583990 2376143 := bstep (se 1 (by rfl) ⟨1782107, by rfl⟩ : syracuseStep 2376143 = 3564215) B3564215
theorem B8020457 : Blo 1583990 8020457 := bstep (se 2 (by rfl) ⟨3007671, by rfl⟩ : syracuseStep 8020457 = 6015343) B6015343
theorem B3383785 : Blo 1583990 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B2376185 : Blo 1583990 2376185 := bstep (se 2 (by rfl) ⟨891069, by rfl⟩ : syracuseStep 2376185 = 1782139) B1782139
theorem B2376287 : Blo 1583990 2376287 := bstep (se 1 (by rfl) ⟨1782215, by rfl⟩ : syracuseStep 2376287 = 3564431) B3564431
theorem B5349995 : Blo 1583990 5349995 := bstep (se 1 (by rfl) ⟨4012496, by rfl⟩ : syracuseStep 5349995 = 8024993) B8024993
theorem B8020619 : Blo 1583990 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B2376767 : Blo 1583990 2376767 := bstep (se 1 (by rfl) ⟨1782575, by rfl⟩ : syracuseStep 2376767 = 3565151) B3565151
theorem B2376809 : Blo 1583990 2376809 := bstep (se 2 (by rfl) ⟨891303, by rfl⟩ : syracuseStep 2376809 = 1782607) B1782607
theorem B5350589 : Blo 1583990 5350589 := bstep (se 3 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 5350589 = 2006471) B2006471
theorem B5645519 : Blo 1583990 5645519 := bstep (se 1 (by rfl) ⟨4234139, by rfl⟩ : syracuseStep 5645519 = 8468279) B8468279
theorem B2376911 : Blo 1583990 2376911 := bstep (se 1 (by rfl) ⟨1782683, by rfl⟩ : syracuseStep 2376911 = 3565367) B3565367
theorem B6767945 : Blo 1583990 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B10986857 : Blo 1583990 10986857 := bstep (se 2 (by rfl) ⟨4120071, by rfl⟩ : syracuseStep 10986857 = 8240143) B8240143
theorem B2377115 : Blo 1583990 2377115 := bstep (se 1 (by rfl) ⟨1782836, by rfl⟩ : syracuseStep 2377115 = 3565673) B3565673
theorem B3564971 : Blo 1583990 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B22291955 : Blo 1583990 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B10151507 : Blo 1583990 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B2377337 : Blo 1583990 2377337 := bstep (se 2 (by rfl) ⟨891501, by rfl⟩ : syracuseStep 2377337 = 1783003) B1783003
theorem B3565223 : Blo 1583990 3565223 := bstep (se 1 (by rfl) ⟨2673917, by rfl⟩ : syracuseStep 3565223 = 5347835) B5347835
theorem B2033371 : Blo 1583990 2033371 := bstep (se 1 (by rfl) ⟨1525028, by rfl⟩ : syracuseStep 2033371 = 3050057) B3050057
theorem B2377439 : Blo 1583990 2377439 := bstep (se 1 (by rfl) ⟨1783079, by rfl⟩ : syracuseStep 2377439 = 3566159) B3566159
theorem B2377535 : Blo 1583990 2377535 := bstep (se 1 (by rfl) ⟨1783151, by rfl⟩ : syracuseStep 2377535 = 3566303) B3566303
theorem B3614561 : Blo 1583990 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B3565511 : Blo 1583990 3565511 := bstep (se 1 (by rfl) ⟨2674133, by rfl⟩ : syracuseStep 3565511 = 5348267) B5348267
theorem B2377703 : Blo 1583990 2377703 := bstep (se 1 (by rfl) ⟨1783277, by rfl⟩ : syracuseStep 2377703 = 3566555) B3566555
theorem B2377721 : Blo 1583990 2377721 := bstep (se 2 (by rfl) ⟨891645, by rfl⟩ : syracuseStep 2377721 = 1783291) B1783291
theorem B2377823 : Blo 1583990 2377823 := bstep (se 1 (by rfl) ⟨1783367, by rfl⟩ : syracuseStep 2377823 = 3566735) B3566735
theorem B2377883 : Blo 1583990 2377883 := bstep (se 1 (by rfl) ⟨1783412, by rfl⟩ : syracuseStep 2377883 = 3566825) B3566825
theorem B2377919 : Blo 1583990 2377919 := bstep (se 1 (by rfl) ⟨1783439, by rfl⟩ : syracuseStep 2377919 = 3566879) B3566879
theorem B2377961 : Blo 1583990 2377961 := bstep (se 2 (by rfl) ⟨891735, by rfl⟩ : syracuseStep 2377961 = 1783471) B1783471
theorem B3385579 : Blo 1583990 3385579 := bstep (se 1 (by rfl) ⟨2539184, by rfl⟩ : syracuseStep 3385579 = 5078369) B5078369
theorem B3565817 : Blo 1583990 3565817 := bstep (se 2 (by rfl) ⟨1337181, by rfl⟩ : syracuseStep 3565817 = 2674363) B2674363
theorem B3565871 : Blo 1583990 3565871 := bstep (se 1 (by rfl) ⟨2674403, by rfl⟩ : syracuseStep 3565871 = 5348807) B5348807
theorem B10840481 : Blo 1583990 10840481 := bstep (se 2 (by rfl) ⟨4065180, by rfl⟩ : syracuseStep 10840481 = 8130361) B8130361
theorem B3566087 : Blo 1583990 3566087 := bstep (se 1 (by rfl) ⟨2674565, by rfl⟩ : syracuseStep 3566087 = 5349131) B5349131
theorem B3566267 : Blo 1583990 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B3615419 : Blo 1583990 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B15223571 : Blo 1583990 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B2673499 : Blo 1583990 2673499 := bstep (se 1 (by rfl) ⟨2005124, by rfl⟩ : syracuseStep 2673499 = 4010249) B4010249
theorem B1584031 : Blo 1583990 1584031 := bstep (se 1 (by rfl) ⟨1188023, by rfl⟩ : syracuseStep 1584031 = 2376047) B2376047
theorem B1584175 : Blo 1583990 1584175 := bstep (se 1 (by rfl) ⟨1188131, by rfl⟩ : syracuseStep 1584175 = 2376263) B2376263
theorem B1584199 : Blo 1583990 1584199 := bstep (se 1 (by rfl) ⟨1188149, by rfl⟩ : syracuseStep 1584199 = 2376299) B2376299
theorem B1584351 : Blo 1583990 1584351 := bstep (se 1 (by rfl) ⟨1188263, by rfl⟩ : syracuseStep 1584351 = 2376527) B2376527
theorem B9022697 : Blo 1583990 9022697 := bstep (se 2 (by rfl) ⟨3383511, by rfl⟩ : syracuseStep 9022697 = 6767023) B6767023
theorem B4402457 : Blo 1583990 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B1584615 : Blo 1583990 1584615 := bstep (se 1 (by rfl) ⟨1188461, by rfl⟩ : syracuseStep 1584615 = 2376923) B2376923
theorem B3567095 : Blo 1583990 3567095 := bstep (se 1 (by rfl) ⟨2675321, by rfl⟩ : syracuseStep 3567095 = 5350643) B5350643
theorem B3567167 : Blo 1583990 3567167 := bstep (se 1 (by rfl) ⟨2675375, by rfl⟩ : syracuseStep 3567167 = 5350751) B5350751
theorem B1584731 : Blo 1583990 1584731 := bstep (se 1 (by rfl) ⟨1188548, by rfl⟩ : syracuseStep 1584731 = 2377097) B2377097
theorem B6016619 : Blo 1583990 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B3141227 : Blo 1583990 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B13536983 : Blo 1583990 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B2674471 : Blo 1583990 2674471 := bstep (se 1 (by rfl) ⟨2005853, by rfl⟩ : syracuseStep 2674471 = 4011707) B4011707
theorem B1584967 : Blo 1583990 1584967 := bstep (se 1 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 1584967 = 2377451) B2377451
theorem B1585119 : Blo 1583990 1585119 := bstep (se 1 (by rfl) ⟨1188839, by rfl⟩ : syracuseStep 1585119 = 2377679) B2377679
theorem B4010107 : Blo 1583990 4010107 := bstep (se 1 (by rfl) ⟨3007580, by rfl⟩ : syracuseStep 4010107 = 6015161) B6015161
theorem B10154173 : Blo 1583990 10154173 := bstep (se 3 (by rfl) ⟨1903907, by rfl⟩ : syracuseStep 10154173 = 3807815) B3807815
theorem B1585383 : Blo 1583990 1585383 := bstep (se 1 (by rfl) ⟨1189037, by rfl⟩ : syracuseStep 1585383 = 2378075) B2378075
theorem B87888239 : Blo 1583990 87888239 := bstep (se 1 (by rfl) ⟨65916179, by rfl⟩ : syracuseStep 87888239 = 131832359) B131832359
theorem B5419375 : Blo 1583990 5419375 := bstep (se 1 (by rfl) ⟨4064531, by rfl⟩ : syracuseStep 5419375 = 8129063) B8129063
theorem B30454217 : Blo 1583990 30454217 := bstep (se 2 (by rfl) ⟨11420331, by rfl⟩ : syracuseStep 30454217 = 22840663) B22840663
theorem B9146839 : Blo 1583990 9146839 := bstep (se 1 (by rfl) ⟨6860129, by rfl⟩ : syracuseStep 9146839 = 13720259) B13720259
theorem B2675497 : Blo 1583990 2675497 := bstep (se 2 (by rfl) ⟨1003311, by rfl⟩ : syracuseStep 2675497 = 2006623) B2006623
theorem B1930235 : Blo 1583990 1930235 := bstep (se 1 (by rfl) ⟨1447676, by rfl⟩ : syracuseStep 1930235 = 2895353) B2895353
theorem B5346377 : Blo 1583990 5346377 := bstep (se 2 (by rfl) ⟨2004891, by rfl⟩ : syracuseStep 5346377 = 4009783) B4009783
theorem B8131691 : Blo 1583990 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B34272409 : Blo 1583990 34272409 := bstep (se 2 (by rfl) ⟨12852153, by rfl⟩ : syracuseStep 34272409 = 25704307) B25704307
theorem B15226031 : Blo 1583990 15226031 := bstep (se 1 (by rfl) ⟨11419523, by rfl⟩ : syracuseStep 15226031 = 22839047) B22839047
theorem B6018259 : Blo 1583990 6018259 := bstep (se 1 (by rfl) ⟨4513694, by rfl⟩ : syracuseStep 6018259 = 9027389) B9027389
theorem B9025181 : Blo 1583990 9025181 := bstep (se 3 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 9025181 = 3384443) B3384443
theorem B6018731 : Blo 1583990 6018731 := bstep (se 1 (by rfl) ⟨4514048, by rfl⟩ : syracuseStep 6018731 = 9028097) B9028097
theorem B8025803 : Blo 1583990 8025803 := bstep (se 1 (by rfl) ⟨6019352, by rfl⟩ : syracuseStep 8025803 = 12038705) B12038705
theorem B4011839 : Blo 1583990 4011839 := bstep (se 1 (by rfl) ⟨3008879, by rfl⟩ : syracuseStep 4011839 = 6017759) B6017759
theorem B1783615 : Blo 1583990 1783615 := bstep (se 1 (by rfl) ⟨1337711, by rfl⟩ : syracuseStep 1783615 = 2675423) B2675423
theorem B4511645 : Blo 1583990 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B15439855 : Blo 1583990 15439855 := bstep (se 1 (by rfl) ⟨11579891, by rfl⟩ : syracuseStep 15439855 = 23159783) B23159783
theorem B5077075 : Blo 1583990 5077075 := bstep (se 1 (by rfl) ⟨3807806, by rfl⟩ : syracuseStep 5077075 = 7615613) B7615613
theorem B2537615 : Blo 1583990 2537615 := bstep (se 1 (by rfl) ⟨1903211, by rfl⟩ : syracuseStep 2537615 = 3806423) B3806423
theorem B4012193 : Blo 1583990 4012193 := bstep (se 2 (by rfl) ⟨1504572, by rfl⟩ : syracuseStep 4012193 = 3009145) B3009145
theorem B4511987 : Blo 1583990 4511987 := bstep (se 1 (by rfl) ⟨3383990, by rfl⟩ : syracuseStep 4511987 = 6767981) B6767981
theorem B9148891 : Blo 1583990 9148891 := bstep (se 1 (by rfl) ⟨6861668, by rfl⟩ : syracuseStep 9148891 = 13723337) B13723337
theorem B6511241 : Blo 1583990 6511241 := bstep (se 2 (by rfl) ⟨2441715, by rfl⟩ : syracuseStep 6511241 = 4883431) B4883431
theorem B5347997 : Blo 1583990 5347997 := bstep (se 3 (by rfl) ⟨1002749, by rfl⟩ : syracuseStep 5347997 = 2005499) B2005499
theorem B19282711 : Blo 1583990 19282711 := bstep (se 1 (by rfl) ⟨14462033, by rfl⟩ : syracuseStep 19282711 = 28924067) B28924067
theorem B5348321 : Blo 1583990 5348321 := bstep (se 2 (by rfl) ⟨2005620, by rfl⟩ : syracuseStep 5348321 = 4011241) B4011241
theorem B4013185 : Blo 1583990 4013185 := bstep (se 2 (by rfl) ⟨1504944, by rfl⟩ : syracuseStep 4013185 = 3009889) B3009889
theorem B5348537 : Blo 1583990 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B13532609 : Blo 1583990 13532609 := bstep (se 2 (by rfl) ⟨5074728, by rfl⟩ : syracuseStep 13532609 = 10149457) B10149457
theorem B10157507 : Blo 1583990 10157507 := bstep (se 1 (by rfl) ⟨7618130, by rfl⟩ : syracuseStep 10157507 = 15236261) B15236261
theorem B5709403 : Blo 1583990 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B329408309 : Blo 1583990 329408309 := bstep (se 5 (by rfl) ⟨15441014, by rfl⟩ : syracuseStep 329408309 = 30882029) B30882029
theorem B7618475 : Blo 1583990 7618475 := bstep (se 1 (by rfl) ⟨5713856, by rfl⟩ : syracuseStep 7618475 = 11427713) B11427713
theorem B21684509 : Blo 1583990 21684509 := bstep (se 3 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 21684509 = 8131691) B8131691
theorem B4514105 : Blo 1583990 4514105 := bstep (se 2 (by rfl) ⟨1692789, by rfl⟩ : syracuseStep 4514105 = 3385579) B3385579
theorem B6766973 : Blo 1583990 6766973 := bstep (se 3 (by rfl) ⟨1268807, by rfl⟩ : syracuseStep 6766973 = 2537615) B2537615
theorem B12198521 : Blo 1583990 12198521 := bstep (se 2 (by rfl) ⟨4574445, by rfl⟩ : syracuseStep 12198521 = 9148891) B9148891
theorem B3564251 : Blo 1583990 3564251 := bstep (se 1 (by rfl) ⟨2673188, by rfl⟩ : syracuseStep 3564251 = 5346377) B5346377
theorem B10150687 : Blo 1583990 10150687 := bstep (se 1 (by rfl) ⟨7613015, by rfl⟩ : syracuseStep 10150687 = 15226031) B15226031
theorem B7324571 : Blo 1583990 7324571 := bstep (se 1 (by rfl) ⟨5493428, by rfl⟩ : syracuseStep 7324571 = 10986857) B10986857
theorem B2376647 : Blo 1583990 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B14861303 : Blo 1583990 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B2376815 : Blo 1583990 2376815 := bstep (se 1 (by rfl) ⟨1782611, by rfl⟩ : syracuseStep 2376815 = 3565223) B3565223
theorem B3564665 : Blo 1583990 3564665 := bstep (se 2 (by rfl) ⟨1336749, by rfl⟩ : syracuseStep 3564665 = 2673499) B2673499
theorem B5350535 : Blo 1583990 5350535 := bstep (se 1 (by rfl) ⟨4012901, by rfl⟩ : syracuseStep 5350535 = 8025803) B8025803
theorem B2409707 : Blo 1583990 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B3007763 : Blo 1583990 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B2377007 : Blo 1583990 2377007 := bstep (se 1 (by rfl) ⟨1782755, by rfl⟩ : syracuseStep 2377007 = 3565511) B3565511
theorem B3007991 : Blo 1583990 3007991 := bstep (se 1 (by rfl) ⟨2255993, by rfl⟩ : syracuseStep 3007991 = 4511987) B4511987
theorem B2377211 : Blo 1583990 2377211 := bstep (se 1 (by rfl) ⟨1782908, by rfl⟩ : syracuseStep 2377211 = 3565817) B3565817
theorem B5350913 : Blo 1583990 5350913 := bstep (se 2 (by rfl) ⟨2006592, by rfl⟩ : syracuseStep 5350913 = 4013185) B4013185
theorem B2377247 : Blo 1583990 2377247 := bstep (se 1 (by rfl) ⟨1782935, by rfl⟩ : syracuseStep 2377247 = 3565871) B3565871
theorem B45696545 : Blo 1583990 45696545 := bstep (se 2 (by rfl) ⟨17136204, by rfl⟩ : syracuseStep 45696545 = 34272409) B34272409
theorem B7226987 : Blo 1583990 7226987 := bstep (se 1 (by rfl) ⟨5420240, by rfl⟩ : syracuseStep 7226987 = 10840481) B10840481
theorem B2377391 : Blo 1583990 2377391 := bstep (se 1 (by rfl) ⟨1783043, by rfl⟩ : syracuseStep 2377391 = 3566087) B3566087
theorem B3565331 : Blo 1583990 3565331 := bstep (se 1 (by rfl) ⟨2673998, by rfl⟩ : syracuseStep 3565331 = 5347997) B5347997
theorem B2377511 : Blo 1583990 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B2410279 : Blo 1583990 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B28903333 : Blo 1583990 28903333 := bstep (se 4 (by rfl) ⟨2709687, by rfl⟩ : syracuseStep 28903333 = 5419375) B5419375
theorem B3565547 : Blo 1583990 3565547 := bstep (se 1 (by rfl) ⟨2674160, by rfl⟩ : syracuseStep 3565547 = 5348321) B5348321
theorem B7612537 : Blo 1583990 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B3565691 : Blo 1583990 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B6015131 : Blo 1583990 6015131 := bstep (se 1 (by rfl) ⟨4511348, by rfl⟩ : syracuseStep 6015131 = 9022697) B9022697
theorem B2934971 : Blo 1583990 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B9021739 : Blo 1583990 9021739 := bstep (se 1 (by rfl) ⟨6766304, by rfl⟩ : syracuseStep 9021739 = 13532609) B13532609
theorem B2378063 : Blo 1583990 2378063 := bstep (se 1 (by rfl) ⟨1783547, by rfl⟩ : syracuseStep 2378063 = 3567095) B3567095
theorem B2378111 : Blo 1583990 2378111 := bstep (se 1 (by rfl) ⟨1783583, by rfl⟩ : syracuseStep 2378111 = 3567167) B3567167
theorem B3565961 : Blo 1583990 3565961 := bstep (se 2 (by rfl) ⟨1337235, by rfl⟩ : syracuseStep 3565961 = 2674471) B2674471
theorem B2378153 : Blo 1583990 2378153 := bstep (se 2 (by rfl) ⟨891807, by rfl⟩ : syracuseStep 2378153 = 1783615) B1783615
theorem B219605539 : Blo 1583990 219605539 := bstep (se 1 (by rfl) ⟨164704154, by rfl⟩ : syracuseStep 219605539 = 329408309) B329408309
theorem B5147293 : Blo 1583990 5147293 := bstep (se 3 (by rfl) ⟨965117, by rfl⟩ : syracuseStep 5147293 = 1930235) B1930235
theorem B6769433 : Blo 1583990 6769433 := bstep (se 2 (by rfl) ⟨2538537, by rfl⟩ : syracuseStep 6769433 = 5077075) B5077075
theorem B58592159 : Blo 1583990 58592159 := bstep (se 1 (by rfl) ⟨43944119, by rfl⟩ : syracuseStep 58592159 = 87888239) B87888239
theorem B3009487 : Blo 1583990 3009487 := bstep (se 1 (by rfl) ⟨2257115, by rfl⟩ : syracuseStep 3009487 = 4514231) B4514231
theorem B20302811 : Blo 1583990 20302811 := bstep (se 1 (by rfl) ⟨15227108, by rfl⟩ : syracuseStep 20302811 = 30454217) B30454217
theorem B1584095 : Blo 1583990 1584095 := bstep (se 1 (by rfl) ⟨1188071, by rfl⟩ : syracuseStep 1584095 = 2376143) B2376143
theorem B1584123 : Blo 1583990 1584123 := bstep (se 1 (by rfl) ⟨1188092, by rfl⟩ : syracuseStep 1584123 = 2376185) B2376185
theorem B1584191 : Blo 1583990 1584191 := bstep (se 1 (by rfl) ⟨1188143, by rfl⟩ : syracuseStep 1584191 = 2376287) B2376287
theorem B3566663 : Blo 1583990 3566663 := bstep (se 1 (by rfl) ⟨2674997, by rfl⟩ : syracuseStep 3566663 = 5349995) B5349995
theorem B1584511 : Blo 1583990 1584511 := bstep (se 1 (by rfl) ⟨1188383, by rfl⟩ : syracuseStep 1584511 = 2376767) B2376767
theorem B1584539 : Blo 1583990 1584539 := bstep (se 1 (by rfl) ⟨1188404, by rfl⟩ : syracuseStep 1584539 = 2376809) B2376809
theorem B3567059 : Blo 1583990 3567059 := bstep (se 1 (by rfl) ⟨2675294, by rfl⟩ : syracuseStep 3567059 = 5350589) B5350589
theorem B3763679 : Blo 1583990 3763679 := bstep (se 1 (by rfl) ⟨2822759, by rfl⟩ : syracuseStep 3763679 = 5645519) B5645519
theorem B1584607 : Blo 1583990 1584607 := bstep (se 1 (by rfl) ⟨1188455, by rfl⟩ : syracuseStep 1584607 = 2376911) B2376911
theorem B1584743 : Blo 1583990 1584743 := bstep (se 1 (by rfl) ⟨1188557, by rfl⟩ : syracuseStep 1584743 = 2377115) B2377115
theorem B25710281 : Blo 1583990 25710281 := bstep (se 2 (by rfl) ⟨9641355, by rfl⟩ : syracuseStep 25710281 = 19282711) B19282711
theorem B3567329 : Blo 1583990 3567329 := bstep (se 2 (by rfl) ⟨1337748, by rfl⟩ : syracuseStep 3567329 = 2675497) B2675497
theorem B1584891 : Blo 1583990 1584891 := bstep (se 1 (by rfl) ⟨1188668, by rfl⟩ : syracuseStep 1584891 = 2377337) B2377337
theorem B6016787 : Blo 1583990 6016787 := bstep (se 1 (by rfl) ⟨4512590, by rfl⟩ : syracuseStep 6016787 = 9025181) B9025181
theorem B1584959 : Blo 1583990 1584959 := bstep (se 1 (by rfl) ⟨1188719, by rfl⟩ : syracuseStep 1584959 = 2377439) B2377439
theorem B2674559 : Blo 1583990 2674559 := bstep (se 1 (by rfl) ⟨2005919, by rfl⟩ : syracuseStep 2674559 = 4011839) B4011839
theorem B1585023 : Blo 1583990 1585023 := bstep (se 1 (by rfl) ⟨1188767, by rfl⟩ : syracuseStep 1585023 = 2377535) B2377535
theorem B1585135 : Blo 1583990 1585135 := bstep (se 1 (by rfl) ⟨1188851, by rfl⟩ : syracuseStep 1585135 = 2377703) B2377703
theorem B1585147 : Blo 1583990 1585147 := bstep (se 1 (by rfl) ⟨1188860, by rfl⟩ : syracuseStep 1585147 = 2377721) B2377721
theorem B1585215 : Blo 1583990 1585215 := bstep (se 1 (by rfl) ⟨1188911, by rfl⟩ : syracuseStep 1585215 = 2377823) B2377823
theorem B1585255 : Blo 1583990 1585255 := bstep (se 1 (by rfl) ⟨1188941, by rfl⟩ : syracuseStep 1585255 = 2377883) B2377883
theorem B2674795 : Blo 1583990 2674795 := bstep (se 1 (by rfl) ⟨2006096, by rfl⟩ : syracuseStep 2674795 = 4012193) B4012193
theorem B1585279 : Blo 1583990 1585279 := bstep (se 1 (by rfl) ⟨1188959, by rfl⟩ : syracuseStep 1585279 = 2377919) B2377919
theorem B1585307 : Blo 1583990 1585307 := bstep (se 1 (by rfl) ⟨1188980, by rfl⟩ : syracuseStep 1585307 = 2377961) B2377961
theorem B27070685 : Blo 1583990 27070685 := bstep (se 3 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 27070685 = 10151507) B10151507
theorem B8024345 : Blo 1583990 8024345 := bstep (se 2 (by rfl) ⟨3009129, by rfl⟩ : syracuseStep 8024345 = 6018259) B6018259
theorem B8376605 : Blo 1583990 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B6771671 : Blo 1583990 6771671 := bstep (se 1 (by rfl) ⟨5078753, by rfl⟩ : syracuseStep 6771671 = 10157507) B10157507
theorem B4011079 : Blo 1583990 4011079 := bstep (se 1 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 4011079 = 6016619) B6016619
theorem B9024655 : Blo 1583990 9024655 := bstep (se 1 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 9024655 = 13536983) B13536983
theorem B5346809 : Blo 1583990 5346809 := bstep (se 2 (by rfl) ⟨2005053, by rfl⟩ : syracuseStep 5346809 = 4010107) B4010107
theorem B15062537 : Blo 1583990 15062537 := bstep (se 2 (by rfl) ⟨5648451, by rfl⟩ : syracuseStep 15062537 = 11296903) B11296903
theorem B13538897 : Blo 1583990 13538897 := bstep (se 2 (by rfl) ⟨5077086, by rfl⟩ : syracuseStep 13538897 = 10154173) B10154173
theorem B5346971 : Blo 1583990 5346971 := bstep (se 1 (by rfl) ⟨4010228, by rfl⟩ : syracuseStep 5346971 = 8020457) B8020457
theorem B5347079 : Blo 1583990 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B12195785 : Blo 1583990 12195785 := bstep (se 2 (by rfl) ⟨4573419, by rfl⟩ : syracuseStep 12195785 = 9146839) B9146839
theorem B4511713 : Blo 1583990 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B4511963 : Blo 1583990 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B4012487 : Blo 1583990 4012487 := bstep (se 1 (by rfl) ⟨3009365, by rfl⟩ : syracuseStep 4012487 = 6018731) B6018731
theorem B4340827 : Blo 1583990 4340827 := bstep (se 1 (by rfl) ⟨3255620, by rfl⟩ : syracuseStep 4340827 = 6511241) B6511241
theorem B10149047 : Blo 1583990 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B2711161 : Blo 1583990 2711161 := bstep (se 2 (by rfl) ⟨1016685, by rfl⟩ : syracuseStep 2711161 = 2033371) B2033371
theorem B20315933 : Blo 1583990 20315933 := bstep (se 3 (by rfl) ⟨3809237, by rfl⟩ : syracuseStep 20315933 = 7618475) B7618475
theorem B20586473 : Blo 1583990 20586473 := bstep (se 2 (by rfl) ⟨7719927, by rfl⟩ : syracuseStep 20586473 = 15439855) B15439855
theorem B18047123 : Blo 1583990 18047123 := bstep (se 1 (by rfl) ⟨13535342, by rfl⟩ : syracuseStep 18047123 = 27070685) B27070685
theorem B10150049 : Blo 1583990 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B5349563 : Blo 1583990 5349563 := bstep (se 1 (by rfl) ⟨4012172, by rfl⟩ : syracuseStep 5349563 = 8024345) B8024345
theorem B2376167 : Blo 1583990 2376167 := bstep (se 1 (by rfl) ⟨1782125, by rfl⟩ : syracuseStep 2376167 = 3564251) B3564251
theorem B4883047 : Blo 1583990 4883047 := bstep (se 1 (by rfl) ⟨3662285, by rfl⟩ : syracuseStep 4883047 = 7324571) B7324571
theorem B4514447 : Blo 1583990 4514447 := bstep (se 1 (by rfl) ⟨3385835, by rfl⟩ : syracuseStep 4514447 = 6771671) B6771671
theorem B292807385 : Blo 1583990 292807385 := bstep (se 2 (by rfl) ⟨109802769, by rfl⟩ : syracuseStep 292807385 = 219605539) B219605539
theorem B2376443 : Blo 1583990 2376443 := bstep (se 1 (by rfl) ⟨1782332, by rfl⟩ : syracuseStep 2376443 = 3564665) B3564665
theorem B3564539 : Blo 1583990 3564539 := bstep (se 1 (by rfl) ⟨2673404, by rfl⟩ : syracuseStep 3564539 = 5346809) B5346809
theorem B13534249 : Blo 1583990 13534249 := bstep (se 2 (by rfl) ⟨5075343, by rfl⟩ : syracuseStep 13534249 = 10150687) B10150687
theorem B3564647 : Blo 1583990 3564647 := bstep (se 1 (by rfl) ⟨2673485, by rfl⟩ : syracuseStep 3564647 = 5346971) B5346971
theorem B3564719 : Blo 1583990 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B2376887 : Blo 1583990 2376887 := bstep (se 1 (by rfl) ⟨1782665, by rfl⟩ : syracuseStep 2376887 = 3565331) B3565331
theorem B10036477 : Blo 1583990 10036477 := bstep (se 3 (by rfl) ⟨1881839, by rfl⟩ : syracuseStep 10036477 = 3763679) B3763679
theorem B2377031 : Blo 1583990 2377031 := bstep (se 1 (by rfl) ⟨1782773, by rfl⟩ : syracuseStep 2377031 = 3565547) B3565547
theorem B2377127 : Blo 1583990 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B12854821 : Blo 1583990 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B2377307 : Blo 1583990 2377307 := bstep (se 1 (by rfl) ⟨1782980, by rfl⟩ : syracuseStep 2377307 = 3565961) B3565961
theorem B39061439 : Blo 1583990 39061439 := bstep (se 1 (by rfl) ⟨29296079, by rfl⟩ : syracuseStep 39061439 = 58592159) B58592159
theorem B13535207 : Blo 1583990 13535207 := bstep (se 1 (by rfl) ⟨10151405, by rfl⟩ : syracuseStep 13535207 = 20302811) B20302811
theorem B2377775 : Blo 1583990 2377775 := bstep (se 1 (by rfl) ⟨1783331, by rfl⟩ : syracuseStep 2377775 = 3566663) B3566663
theorem B3614881 : Blo 1583990 3614881 := bstep (se 2 (by rfl) ⟨1355580, by rfl⟩ : syracuseStep 3614881 = 2711161) B2711161
theorem B2378039 : Blo 1583990 2378039 := bstep (se 1 (by rfl) ⟨1783529, by rfl⟩ : syracuseStep 2378039 = 3567059) B3567059
theorem B17140187 : Blo 1583990 17140187 := bstep (se 1 (by rfl) ⟨12855140, by rfl⟩ : syracuseStep 17140187 = 25710281) B25710281
theorem B2378219 : Blo 1583990 2378219 := bstep (se 1 (by rfl) ⟨1783664, by rfl⟩ : syracuseStep 2378219 = 3567329) B3567329
theorem B13543955 : Blo 1583990 13543955 := bstep (se 1 (by rfl) ⟨10157966, by rfl⟩ : syracuseStep 13543955 = 20315933) B20315933
theorem B38537777 : Blo 1583990 38537777 := bstep (se 2 (by rfl) ⟨14451666, by rfl⟩ : syracuseStep 38537777 = 28903333) B28903333
theorem B6015617 : Blo 1583990 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B13724315 : Blo 1583990 13724315 := bstep (se 1 (by rfl) ⟨10293236, by rfl⟩ : syracuseStep 13724315 = 20586473) B20586473
theorem B3566393 : Blo 1583990 3566393 := bstep (se 2 (by rfl) ⟨1337397, by rfl⟩ : syracuseStep 3566393 = 2674795) B2674795
theorem B3009403 : Blo 1583990 3009403 := bstep (se 1 (by rfl) ⟨2257052, by rfl⟩ : syracuseStep 3009403 = 4514105) B4514105
theorem B12028985 : Blo 1583990 12028985 := bstep (se 2 (by rfl) ⟨4510869, by rfl⟩ : syracuseStep 12028985 = 9021739) B9021739
theorem B6425885 : Blo 1583990 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B1584431 : Blo 1583990 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B9907535 : Blo 1583990 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B1584543 : Blo 1583990 1584543 := bstep (se 1 (by rfl) ⟨1188407, by rfl⟩ : syracuseStep 1584543 = 2376815) B2376815
theorem B3567023 : Blo 1583990 3567023 := bstep (se 1 (by rfl) ⟨2675267, by rfl⟩ : syracuseStep 3567023 = 5350535) B5350535
theorem B1584671 : Blo 1583990 1584671 := bstep (se 1 (by rfl) ⟨1188503, by rfl⟩ : syracuseStep 1584671 = 2377007) B2377007
theorem B1584807 : Blo 1583990 1584807 := bstep (se 1 (by rfl) ⟨1188605, by rfl⟩ : syracuseStep 1584807 = 2377211) B2377211
theorem B3567275 : Blo 1583990 3567275 := bstep (se 1 (by rfl) ⟨2675456, by rfl⟩ : syracuseStep 3567275 = 5350913) B5350913
theorem B1584831 : Blo 1583990 1584831 := bstep (se 1 (by rfl) ⟨1188623, by rfl⟩ : syracuseStep 1584831 = 2377247) B2377247
theorem B1584927 : Blo 1583990 1584927 := bstep (se 1 (by rfl) ⟨1188695, by rfl⟩ : syracuseStep 1584927 = 2377391) B2377391
theorem B1585007 : Blo 1583990 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B4010087 : Blo 1583990 4010087 := bstep (se 1 (by rfl) ⟨3007565, by rfl⟩ : syracuseStep 4010087 = 6015131) B6015131
theorem B5787769 : Blo 1583990 5787769 := bstep (se 2 (by rfl) ⟨2170413, by rfl⟩ : syracuseStep 5787769 = 4340827) B4340827
theorem B1585375 : Blo 1583990 1585375 := bstep (se 1 (by rfl) ⟨1189031, by rfl⟩ : syracuseStep 1585375 = 2378063) B2378063
theorem B1585407 : Blo 1583990 1585407 := bstep (se 1 (by rfl) ⟨1189055, by rfl⟩ : syracuseStep 1585407 = 2378111) B2378111
theorem B1585435 : Blo 1583990 1585435 := bstep (se 1 (by rfl) ⟨1189076, by rfl⟩ : syracuseStep 1585435 = 2378153) B2378153
theorem B19271965 : Blo 1583990 19271965 := bstep (se 3 (by rfl) ⟨3613493, by rfl⟩ : syracuseStep 19271965 = 7226987) B7226987
theorem B2674991 : Blo 1583990 2674991 := bstep (se 1 (by rfl) ⟨2006243, by rfl⟩ : syracuseStep 2674991 = 4012487) B4012487
theorem B31306357 : Blo 1583990 31306357 := bstep (se 5 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 31306357 = 2934971) B2934971
theorem B4011191 : Blo 1583990 4011191 := bstep (se 1 (by rfl) ⟨3008393, by rfl⟩ : syracuseStep 4011191 = 6016787) B6016787
theorem B1783039 : Blo 1583990 1783039 := bstep (se 1 (by rfl) ⟨1337279, by rfl⟩ : syracuseStep 1783039 = 2674559) B2674559
theorem B14456339 : Blo 1583990 14456339 := bstep (se 1 (by rfl) ⟨10842254, by rfl⟩ : syracuseStep 14456339 = 21684509) B21684509
theorem B5584403 : Blo 1583990 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B4511315 : Blo 1583990 4511315 := bstep (se 1 (by rfl) ⟨3383486, by rfl⟩ : syracuseStep 4511315 = 6766973) B6766973
theorem B8132347 : Blo 1583990 8132347 := bstep (se 1 (by rfl) ⟨6099260, by rfl⟩ : syracuseStep 8132347 = 12198521) B12198521
theorem B12031901 : Blo 1583990 12031901 := bstep (se 3 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 12031901 = 4511963) B4511963
theorem B2005175 : Blo 1583990 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B6863057 : Blo 1583990 6863057 := bstep (se 2 (by rfl) ⟨2573646, by rfl⟩ : syracuseStep 6863057 = 5147293) B5147293
theorem B2005327 : Blo 1583990 2005327 := bstep (se 1 (by rfl) ⟨1503995, by rfl⟩ : syracuseStep 2005327 = 3007991) B3007991
theorem B10041691 : Blo 1583990 10041691 := bstep (se 1 (by rfl) ⟨7531268, by rfl⟩ : syracuseStep 10041691 = 15062537) B15062537
theorem B30464363 : Blo 1583990 30464363 := bstep (se 1 (by rfl) ⟨22848272, by rfl⟩ : syracuseStep 30464363 = 45696545) B45696545
theorem B9025931 : Blo 1583990 9025931 := bstep (se 1 (by rfl) ⟨6769448, by rfl⟩ : syracuseStep 9025931 = 13538897) B13538897
theorem B4012649 : Blo 1583990 4012649 := bstep (se 2 (by rfl) ⟨1504743, by rfl⟩ : syracuseStep 4012649 = 3009487) B3009487
theorem B5348105 : Blo 1583990 5348105 := bstep (se 2 (by rfl) ⟨2005539, by rfl⟩ : syracuseStep 5348105 = 4011079) B4011079
theorem B12032873 : Blo 1583990 12032873 := bstep (se 2 (by rfl) ⟨4512327, by rfl⟩ : syracuseStep 12032873 = 9024655) B9024655
theorem B4512955 : Blo 1583990 4512955 := bstep (se 1 (by rfl) ⟨3384716, by rfl⟩ : syracuseStep 4512955 = 6769433) B6769433
theorem B6766031 : Blo 1583990 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B32522093 : Blo 1583990 32522093 := bstep (se 3 (by rfl) ⟨6097892, by rfl⟩ : syracuseStep 32522093 = 12195785) B12195785
theorem B6766699 : Blo 1583990 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B7717025 : Blo 1583990 7717025 := bstep (se 2 (by rfl) ⟨2893884, by rfl⟩ : syracuseStep 7717025 = 5787769) B5787769
theorem B26042917 : Blo 1583990 26042917 := bstep (se 4 (by rfl) ⟨2441523, by rfl⟩ : syracuseStep 26042917 = 4883047) B4883047
theorem B2376359 : Blo 1583990 2376359 := bstep (se 1 (by rfl) ⟨1782269, by rfl⟩ : syracuseStep 2376359 = 3564539) B3564539
theorem B2376431 : Blo 1583990 2376431 := bstep (se 1 (by rfl) ⟨1782323, by rfl⟩ : syracuseStep 2376431 = 3564647) B3564647
theorem B2376479 : Blo 1583990 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B26420093 : Blo 1583990 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B3007543 : Blo 1583990 3007543 := bstep (se 1 (by rfl) ⟨2255657, by rfl⟩ : syracuseStep 3007543 = 4511315) B4511315
theorem B8021267 : Blo 1583990 8021267 := bstep (se 1 (by rfl) ⟨6015950, by rfl⟩ : syracuseStep 8021267 = 12031901) B12031901
theorem B20309575 : Blo 1583990 20309575 := bstep (se 1 (by rfl) ⟨15232181, by rfl⟩ : syracuseStep 20309575 = 30464363) B30464363
theorem B2377385 : Blo 1583990 2377385 := bstep (se 2 (by rfl) ⟨891519, by rfl⟩ : syracuseStep 2377385 = 1783039) B1783039
theorem B9029303 : Blo 1583990 9029303 := bstep (se 1 (by rfl) ⟨6771977, by rfl⟩ : syracuseStep 9029303 = 13543955) B13543955
theorem B25691851 : Blo 1583990 25691851 := bstep (se 1 (by rfl) ⟨19268888, by rfl⟩ : syracuseStep 25691851 = 38537777) B38537777
theorem B3565403 : Blo 1583990 3565403 := bstep (se 1 (by rfl) ⟨2674052, by rfl⟩ : syracuseStep 3565403 = 5348105) B5348105
theorem B2377595 : Blo 1583990 2377595 := bstep (se 1 (by rfl) ⟨1783196, by rfl⟩ : syracuseStep 2377595 = 3566393) B3566393
theorem B8021915 : Blo 1583990 8021915 := bstep (se 1 (by rfl) ⟨6016436, by rfl⟩ : syracuseStep 8021915 = 12032873) B12032873
theorem B17139761 : Blo 1583990 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B2378015 : Blo 1583990 2378015 := bstep (se 1 (by rfl) ⟨1783511, by rfl⟩ : syracuseStep 2378015 = 3567023) B3567023
theorem B2378183 : Blo 1583990 2378183 := bstep (se 1 (by rfl) ⟨1783637, by rfl⟩ : syracuseStep 2378183 = 3567275) B3567275
theorem B2673391 : Blo 1583990 2673391 := bstep (se 1 (by rfl) ⟨2005043, by rfl⟩ : syracuseStep 2673391 = 4010087) B4010087
theorem B3566375 : Blo 1583990 3566375 := bstep (se 1 (by rfl) ⟨2674781, by rfl⟩ : syracuseStep 3566375 = 5349563) B5349563
theorem B4819841 : Blo 1583990 4819841 := bstep (se 2 (by rfl) ⟨1807440, by rfl⟩ : syracuseStep 4819841 = 3614881) B3614881
theorem B1584111 : Blo 1583990 1584111 := bstep (se 1 (by rfl) ⟨1188083, by rfl⟩ : syracuseStep 1584111 = 2376167) B2376167
theorem B3009631 : Blo 1583990 3009631 := bstep (se 1 (by rfl) ⟨2257223, by rfl⟩ : syracuseStep 3009631 = 4514447) B4514447
theorem B2673769 : Blo 1583990 2673769 := bstep (se 2 (by rfl) ⟨1002663, by rfl⟩ : syracuseStep 2673769 = 2005327) B2005327
theorem B13388921 : Blo 1583990 13388921 := bstep (se 2 (by rfl) ⟨5020845, by rfl⟩ : syracuseStep 13388921 = 10041691) B10041691
theorem B1584295 : Blo 1583990 1584295 := bstep (se 1 (by rfl) ⟨1188221, by rfl⟩ : syracuseStep 1584295 = 2376443) B2376443
theorem B1584591 : Blo 1583990 1584591 := bstep (se 1 (by rfl) ⟨1188443, by rfl⟩ : syracuseStep 1584591 = 2376887) B2376887
theorem B2674127 : Blo 1583990 2674127 := bstep (se 1 (by rfl) ⟨2005595, by rfl⟩ : syracuseStep 2674127 = 4011191) B4011191
theorem B1584687 : Blo 1583990 1584687 := bstep (se 1 (by rfl) ⟨1188515, by rfl⟩ : syracuseStep 1584687 = 2377031) B2377031
theorem B1584751 : Blo 1583990 1584751 := bstep (se 1 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 1584751 = 2377127) B2377127
theorem B9637559 : Blo 1583990 9637559 := bstep (se 1 (by rfl) ⟨7228169, by rfl⟩ : syracuseStep 9637559 = 14456339) B14456339
theorem B3722935 : Blo 1583990 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B1584871 : Blo 1583990 1584871 := bstep (se 1 (by rfl) ⟨1188653, by rfl⟩ : syracuseStep 1584871 = 2377307) B2377307
theorem B18042749 : Blo 1583990 18042749 := bstep (se 3 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 18042749 = 6766031) B6766031
theorem B9023471 : Blo 1583990 9023471 := bstep (se 1 (by rfl) ⟨6767603, by rfl⟩ : syracuseStep 9023471 = 13535207) B13535207
theorem B1585183 : Blo 1583990 1585183 := bstep (se 1 (by rfl) ⟨1188887, by rfl⟩ : syracuseStep 1585183 = 2377775) B2377775
theorem B4575371 : Blo 1583990 4575371 := bstep (se 1 (by rfl) ⟨3431528, by rfl⟩ : syracuseStep 4575371 = 6863057) B6863057
theorem B1585359 : Blo 1583990 1585359 := bstep (se 1 (by rfl) ⟨1189019, by rfl⟩ : syracuseStep 1585359 = 2378039) B2378039
theorem B6017273 : Blo 1583990 6017273 := bstep (se 2 (by rfl) ⟨2256477, by rfl⟩ : syracuseStep 6017273 = 4512955) B4512955
theorem B6017287 : Blo 1583990 6017287 := bstep (se 1 (by rfl) ⟨4512965, by rfl⟩ : syracuseStep 6017287 = 9025931) B9025931
theorem B1585479 : Blo 1583990 1585479 := bstep (se 1 (by rfl) ⟨1189109, by rfl⟩ : syracuseStep 1585479 = 2378219) B2378219
theorem B13381969 : Blo 1583990 13381969 := bstep (se 2 (by rfl) ⟨5018238, by rfl⟩ : syracuseStep 13381969 = 10036477) B10036477
theorem B2675099 : Blo 1583990 2675099 := bstep (se 1 (by rfl) ⟨2006324, by rfl⟩ : syracuseStep 2675099 = 4012649) B4012649
theorem B4010411 : Blo 1583990 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B10843129 : Blo 1583990 10843129 := bstep (se 2 (by rfl) ⟨4066173, by rfl⟩ : syracuseStep 10843129 = 8132347) B8132347
theorem B21681395 : Blo 1583990 21681395 := bstep (se 1 (by rfl) ⟨16261046, by rfl⟩ : syracuseStep 21681395 = 32522093) B32522093
theorem B12031415 : Blo 1583990 12031415 := bstep (se 1 (by rfl) ⟨9023561, by rfl⟩ : syracuseStep 12031415 = 18047123) B18047123
theorem B1783327 : Blo 1583990 1783327 := bstep (se 1 (by rfl) ⟨1337495, by rfl⟩ : syracuseStep 1783327 = 2674991) B2674991
theorem B25695953 : Blo 1583990 25695953 := bstep (se 2 (by rfl) ⟨9635982, by rfl⟩ : syracuseStep 25695953 = 19271965) B19271965
theorem B195204923 : Blo 1583990 195204923 := bstep (se 1 (by rfl) ⟨146403692, by rfl⟩ : syracuseStep 195204923 = 292807385) B292807385
theorem B5347133 : Blo 1583990 5347133 := bstep (se 3 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 5347133 = 2005175) B2005175
theorem B166967237 : Blo 1583990 166967237 := bstep (se 4 (by rfl) ⟨15653178, by rfl⟩ : syracuseStep 166967237 = 31306357) B31306357
theorem B4012537 : Blo 1583990 4012537 := bstep (se 2 (by rfl) ⟨1504701, by rfl⟩ : syracuseStep 4012537 = 3009403) B3009403
theorem B26040959 : Blo 1583990 26040959 := bstep (se 1 (by rfl) ⟨19530719, by rfl⟩ : syracuseStep 26040959 = 39061439) B39061439
theorem B18045665 : Blo 1583990 18045665 := bstep (se 2 (by rfl) ⟨6767124, by rfl⟩ : syracuseStep 18045665 = 13534249) B13534249
theorem B11426791 : Blo 1583990 11426791 := bstep (se 1 (by rfl) ⟨8570093, by rfl⟩ : syracuseStep 11426791 = 17140187) B17140187
theorem B9149543 : Blo 1583990 9149543 := bstep (se 1 (by rfl) ⟨6862157, by rfl⟩ : syracuseStep 9149543 = 13724315) B13724315
theorem B8019323 : Blo 1583990 8019323 := bstep (se 1 (by rfl) ⟨6014492, by rfl⟩ : syracuseStep 8019323 = 12028985) B12028985
theorem B4283923 : Blo 1583990 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B5144683 : Blo 1583990 5144683 := bstep (se 1 (by rfl) ⟨3858512, by rfl⟩ : syracuseStep 5144683 = 7717025) B7717025
theorem B17842625 : Blo 1583990 17842625 := bstep (se 2 (by rfl) ⟨6690984, by rfl⟩ : syracuseStep 17842625 = 13381969) B13381969
theorem B17613395 : Blo 1583990 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B5350049 : Blo 1583990 5350049 := bstep (se 2 (by rfl) ⟨2006268, by rfl⟩ : syracuseStep 5350049 = 4012537) B4012537
theorem B8020943 : Blo 1583990 8020943 := bstep (se 1 (by rfl) ⟨6015707, by rfl⟩ : syracuseStep 8020943 = 12031415) B12031415
theorem B3564521 : Blo 1583990 3564521 := bstep (se 2 (by rfl) ⟨1336695, by rfl⟩ : syracuseStep 3564521 = 2673391) B2673391
theorem B17130635 : Blo 1583990 17130635 := bstep (se 1 (by rfl) ⟨12847976, by rfl⟩ : syracuseStep 17130635 = 25695953) B25695953
theorem B3564755 : Blo 1583990 3564755 := bstep (se 1 (by rfl) ⟨2673566, by rfl⟩ : syracuseStep 3564755 = 5347133) B5347133
theorem B2376935 : Blo 1583990 2376935 := bstep (se 1 (by rfl) ⟨1782701, by rfl⟩ : syracuseStep 2376935 = 3565403) B3565403
theorem B3565025 : Blo 1583990 3565025 := bstep (se 2 (by rfl) ⟨1336884, by rfl⟩ : syracuseStep 3565025 = 2673769) B2673769
theorem B17360639 : Blo 1583990 17360639 := bstep (se 1 (by rfl) ⟨13020479, by rfl⟩ : syracuseStep 17360639 = 26040959) B26040959
theorem B2377583 : Blo 1583990 2377583 := bstep (se 1 (by rfl) ⟨1783187, by rfl⟩ : syracuseStep 2377583 = 3566375) B3566375
theorem B3213227 : Blo 1583990 3213227 := bstep (se 1 (by rfl) ⟨2409920, by rfl⟩ : syracuseStep 3213227 = 4819841) B4819841
theorem B5711897 : Blo 1583990 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B2377769 : Blo 1583990 2377769 := bstep (se 2 (by rfl) ⟨891663, by rfl⟩ : syracuseStep 2377769 = 1783327) B1783327
theorem B6425039 : Blo 1583990 6425039 := bstep (se 1 (by rfl) ⟨4818779, by rfl⟩ : syracuseStep 6425039 = 9637559) B9637559
theorem B445245965 : Blo 1583990 445245965 := bstep (se 3 (by rfl) ⟨83483618, by rfl⟩ : syracuseStep 445245965 = 166967237) B166967237
theorem B12028499 : Blo 1583990 12028499 := bstep (se 1 (by rfl) ⟨9021374, by rfl⟩ : syracuseStep 12028499 = 18042749) B18042749
theorem B57830021 : Blo 1583990 57830021 := bstep (se 4 (by rfl) ⟨5421564, by rfl⟩ : syracuseStep 57830021 = 10843129) B10843129
theorem B6015647 : Blo 1583990 6015647 := bstep (se 1 (by rfl) ⟨4511735, by rfl⟩ : syracuseStep 6015647 = 9023471) B9023471
theorem B9022265 : Blo 1583990 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B2673607 : Blo 1583990 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B8023049 : Blo 1583990 8023049 := bstep (se 2 (by rfl) ⟨3008643, by rfl⟩ : syracuseStep 8023049 = 6017287) B6017287
theorem B12200989 : Blo 1583990 12200989 := bstep (se 3 (by rfl) ⟨2287685, by rfl⟩ : syracuseStep 12200989 = 4575371) B4575371
theorem B1584239 : Blo 1583990 1584239 := bstep (se 1 (by rfl) ⟨1188179, by rfl⟩ : syracuseStep 1584239 = 2376359) B2376359
theorem B1584287 : Blo 1583990 1584287 := bstep (se 1 (by rfl) ⟨1188215, by rfl⟩ : syracuseStep 1584287 = 2376431) B2376431
theorem B1584319 : Blo 1583990 1584319 := bstep (se 1 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 1584319 = 2376479) B2376479
theorem B14454263 : Blo 1583990 14454263 := bstep (se 1 (by rfl) ⟨10840697, by rfl⟩ : syracuseStep 14454263 = 21681395) B21681395
theorem B1584923 : Blo 1583990 1584923 := bstep (se 1 (by rfl) ⟨1188692, by rfl⟩ : syracuseStep 1584923 = 2377385) B2377385
theorem B1585063 : Blo 1583990 1585063 := bstep (se 1 (by rfl) ⟨1188797, by rfl⟩ : syracuseStep 1585063 = 2377595) B2377595
theorem B4010057 : Blo 1583990 4010057 := bstep (se 2 (by rfl) ⟨1503771, by rfl⟩ : syracuseStep 4010057 = 3007543) B3007543
theorem B1585343 : Blo 1583990 1585343 := bstep (se 1 (by rfl) ⟨1189007, by rfl⟩ : syracuseStep 1585343 = 2378015) B2378015
theorem B1585455 : Blo 1583990 1585455 := bstep (se 1 (by rfl) ⟨1189091, by rfl⟩ : syracuseStep 1585455 = 2378183) B2378183
theorem B12030443 : Blo 1583990 12030443 := bstep (se 1 (by rfl) ⟨9022832, by rfl⟩ : syracuseStep 12030443 = 18045665) B18045665
theorem B6099695 : Blo 1583990 6099695 := bstep (se 1 (by rfl) ⟨4574771, by rfl⟩ : syracuseStep 6099695 = 9149543) B9149543
theorem B8925947 : Blo 1583990 8925947 := bstep (se 1 (by rfl) ⟨6694460, by rfl⟩ : syracuseStep 8925947 = 13388921) B13388921
theorem B27079433 : Blo 1583990 27079433 := bstep (se 2 (by rfl) ⟨10154787, by rfl⟩ : syracuseStep 27079433 = 20309575) B20309575
theorem B5346215 : Blo 1583990 5346215 := bstep (se 1 (by rfl) ⟨4009661, by rfl⟩ : syracuseStep 5346215 = 8019323) B8019323
theorem B34255801 : Blo 1583990 34255801 := bstep (se 2 (by rfl) ⟨12845925, by rfl⟩ : syracuseStep 34255801 = 25691851) B25691851
theorem B1782751 : Blo 1583990 1782751 := bstep (se 1 (by rfl) ⟨1337063, by rfl⟩ : syracuseStep 1782751 = 2674127) B2674127
theorem B4011515 : Blo 1583990 4011515 := bstep (se 1 (by rfl) ⟨3008636, by rfl⟩ : syracuseStep 4011515 = 6017273) B6017273
theorem B1783399 : Blo 1583990 1783399 := bstep (se 1 (by rfl) ⟨1337549, by rfl⟩ : syracuseStep 1783399 = 2675099) B2675099
theorem B34723889 : Blo 1583990 34723889 := bstep (se 2 (by rfl) ⟨13021458, by rfl⟩ : syracuseStep 34723889 = 26042917) B26042917
theorem B5347511 : Blo 1583990 5347511 := bstep (se 1 (by rfl) ⟨4010633, by rfl⟩ : syracuseStep 5347511 = 8021267) B8021267
theorem B6019535 : Blo 1583990 6019535 := bstep (se 1 (by rfl) ⟨4514651, by rfl⟩ : syracuseStep 6019535 = 9029303) B9029303
theorem B130136615 : Blo 1583990 130136615 := bstep (se 1 (by rfl) ⟨97602461, by rfl⟩ : syracuseStep 130136615 = 195204923) B195204923
theorem B5347943 : Blo 1583990 5347943 := bstep (se 1 (by rfl) ⟨4010957, by rfl⟩ : syracuseStep 5347943 = 8021915) B8021915
theorem B15235721 : Blo 1583990 15235721 := bstep (se 2 (by rfl) ⟨5713395, by rfl⟩ : syracuseStep 15235721 = 11426791) B11426791
theorem B11426507 : Blo 1583990 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B4012841 : Blo 1583990 4012841 := bstep (se 2 (by rfl) ⟨1504815, by rfl⟩ : syracuseStep 4012841 = 3009631) B3009631
theorem B4963913 : Blo 1583990 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B11895083 : Blo 1583990 11895083 := bstep (se 1 (by rfl) ⟨8921312, by rfl⟩ : syracuseStep 11895083 = 17842625) B17842625
theorem B8020295 : Blo 1583990 8020295 := bstep (se 1 (by rfl) ⟨6015221, by rfl⟩ : syracuseStep 8020295 = 12030443) B12030443
theorem B3564143 : Blo 1583990 3564143 := bstep (se 1 (by rfl) ⟨2673107, by rfl⟩ : syracuseStep 3564143 = 5346215) B5346215
theorem B2376347 : Blo 1583990 2376347 := bstep (se 1 (by rfl) ⟨1782260, by rfl⟩ : syracuseStep 2376347 = 3564521) B3564521
theorem B11420423 : Blo 1583990 11420423 := bstep (se 1 (by rfl) ⟨8565317, by rfl⟩ : syracuseStep 11420423 = 17130635) B17130635
theorem B2376503 : Blo 1583990 2376503 := bstep (se 1 (by rfl) ⟨1782377, by rfl⟩ : syracuseStep 2376503 = 3564755) B3564755
theorem B2376683 : Blo 1583990 2376683 := bstep (se 1 (by rfl) ⟨1782512, by rfl⟩ : syracuseStep 2376683 = 3565025) B3565025
theorem B3564809 : Blo 1583990 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B2377001 : Blo 1583990 2377001 := bstep (se 2 (by rfl) ⟨891375, by rfl⟩ : syracuseStep 2377001 = 1782751) B1782751
theorem B3565007 : Blo 1583990 3565007 := bstep (se 1 (by rfl) ⟨2673755, by rfl⟩ : syracuseStep 3565007 = 5347511) B5347511
theorem B3565295 : Blo 1583990 3565295 := bstep (se 1 (by rfl) ⟨2673971, by rfl⟩ : syracuseStep 3565295 = 5347943) B5347943
theorem B38553347 : Blo 1583990 38553347 := bstep (se 1 (by rfl) ⟨28915010, by rfl⟩ : syracuseStep 38553347 = 57830021) B57830021
theorem B6014843 : Blo 1583990 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B2377865 : Blo 1583990 2377865 := bstep (se 2 (by rfl) ⟨891699, by rfl⟩ : syracuseStep 2377865 = 1783399) B1783399
theorem B9636175 : Blo 1583990 9636175 := bstep (se 1 (by rfl) ⟨7227131, by rfl⟩ : syracuseStep 9636175 = 14454263) B14454263
theorem B2673371 : Blo 1583990 2673371 := bstep (se 1 (by rfl) ⟨2005028, by rfl⟩ : syracuseStep 2673371 = 4010057) B4010057
theorem B15231725 : Blo 1583990 15231725 := bstep (se 3 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 15231725 = 5711897) B5711897
theorem B6859577 : Blo 1583990 6859577 := bstep (se 2 (by rfl) ⟨2572341, by rfl⟩ : syracuseStep 6859577 = 5144683) B5144683
theorem B11742263 : Blo 1583990 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B3566699 : Blo 1583990 3566699 := bstep (se 1 (by rfl) ⟨2675024, by rfl⟩ : syracuseStep 3566699 = 5350049) B5350049
theorem B4066463 : Blo 1583990 4066463 := bstep (se 1 (by rfl) ⟨3049847, by rfl⟩ : syracuseStep 4066463 = 6099695) B6099695
theorem B5950631 : Blo 1583990 5950631 := bstep (se 1 (by rfl) ⟨4462973, by rfl⟩ : syracuseStep 5950631 = 8925947) B8925947
theorem B18997161173 : Blo 1583990 18997161173 := bstep (se 7 (by rfl) ⟨222622982, by rfl⟩ : syracuseStep 18997161173 = 445245965) B445245965
theorem B1584623 : Blo 1583990 1584623 := bstep (se 1 (by rfl) ⟨1188467, by rfl⟩ : syracuseStep 1584623 = 2376935) B2376935
theorem B2674343 : Blo 1583990 2674343 := bstep (se 1 (by rfl) ⟨2005757, by rfl⟩ : syracuseStep 2674343 = 4011515) B4011515
theorem B17133437 : Blo 1583990 17133437 := bstep (se 3 (by rfl) ⟨3212519, by rfl⟩ : syracuseStep 17133437 = 6425039) B6425039
theorem B1585055 : Blo 1583990 1585055 := bstep (se 1 (by rfl) ⟨1188791, by rfl⟩ : syracuseStep 1585055 = 2377583) B2377583
theorem B45674401 : Blo 1583990 45674401 := bstep (se 2 (by rfl) ⟨17127900, by rfl⟩ : syracuseStep 45674401 = 34255801) B34255801
theorem B1585179 : Blo 1583990 1585179 := bstep (se 1 (by rfl) ⟨1188884, by rfl⟩ : syracuseStep 1585179 = 2377769) B2377769
theorem B86757743 : Blo 1583990 86757743 := bstep (se 1 (by rfl) ⟨65068307, by rfl⟩ : syracuseStep 86757743 = 130136615) B130136615
theorem B4010431 : Blo 1583990 4010431 := bstep (se 1 (by rfl) ⟨3007823, by rfl⟩ : syracuseStep 4010431 = 6015647) B6015647
theorem B2675227 : Blo 1583990 2675227 := bstep (se 1 (by rfl) ⟨2006420, by rfl⟩ : syracuseStep 2675227 = 4012841) B4012841
theorem B18052955 : Blo 1583990 18052955 := bstep (se 1 (by rfl) ⟨13539716, by rfl⟩ : syracuseStep 18052955 = 27079433) B27079433
theorem B5347295 : Blo 1583990 5347295 := bstep (se 1 (by rfl) ⟨4010471, by rfl⟩ : syracuseStep 5347295 = 8020943) B8020943
theorem B11573759 : Blo 1583990 11573759 := bstep (se 1 (by rfl) ⟨8680319, by rfl⟩ : syracuseStep 11573759 = 17360639) B17360639
theorem B23149259 : Blo 1583990 23149259 := bstep (se 1 (by rfl) ⟨17361944, by rfl⟩ : syracuseStep 23149259 = 34723889) B34723889
theorem B16267985 : Blo 1583990 16267985 := bstep (se 2 (by rfl) ⟨6100494, by rfl⟩ : syracuseStep 16267985 = 12200989) B12200989
theorem B4013023 : Blo 1583990 4013023 := bstep (se 1 (by rfl) ⟨3009767, by rfl⟩ : syracuseStep 4013023 = 6019535) B6019535
theorem B8018999 : Blo 1583990 8018999 := bstep (se 1 (by rfl) ⟨6014249, by rfl⟩ : syracuseStep 8018999 = 12028499) B12028499
theorem B10157147 : Blo 1583990 10157147 := bstep (se 1 (by rfl) ⟨7617860, by rfl⟩ : syracuseStep 10157147 = 15235721) B15235721
theorem B7617671 : Blo 1583990 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B5348699 : Blo 1583990 5348699 := bstep (se 1 (by rfl) ⟨4011524, by rfl⟩ : syracuseStep 5348699 = 8023049) B8023049
theorem B3309275 : Blo 1583990 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B8568605 : Blo 1583990 8568605 := bstep (se 3 (by rfl) ⟨1606613, by rfl⟩ : syracuseStep 8568605 = 3213227) B3213227
theorem B7930055 : Blo 1583990 7930055 := bstep (se 1 (by rfl) ⟨5947541, by rfl⟩ : syracuseStep 7930055 = 11895083) B11895083
theorem B2376095 : Blo 1583990 2376095 := bstep (se 1 (by rfl) ⟨1782071, by rfl⟩ : syracuseStep 2376095 = 3564143) B3564143
theorem B15868349 : Blo 1583990 15868349 := bstep (se 3 (by rfl) ⟨2975315, by rfl⟩ : syracuseStep 15868349 = 5950631) B5950631
theorem B2376539 : Blo 1583990 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B2376671 : Blo 1583990 2376671 := bstep (se 1 (by rfl) ⟨1782503, by rfl⟩ : syracuseStep 2376671 = 3565007) B3565007
theorem B2376863 : Blo 1583990 2376863 := bstep (se 1 (by rfl) ⟨1782647, by rfl⟩ : syracuseStep 2376863 = 3565295) B3565295
theorem B12035303 : Blo 1583990 12035303 := bstep (se 1 (by rfl) ⟨9026477, by rfl⟩ : syracuseStep 12035303 = 18052955) B18052955
theorem B5350697 : Blo 1583990 5350697 := bstep (se 2 (by rfl) ⟨2006511, by rfl⟩ : syracuseStep 5350697 = 4013023) B4013023
theorem B3564863 : Blo 1583990 3564863 := bstep (se 1 (by rfl) ⟨2673647, by rfl⟩ : syracuseStep 3564863 = 5347295) B5347295
theorem B8824733 : Blo 1583990 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B2377799 : Blo 1583990 2377799 := bstep (se 1 (by rfl) ⟨1783349, by rfl⟩ : syracuseStep 2377799 = 3566699) B3566699
theorem B3565799 : Blo 1583990 3565799 := bstep (se 1 (by rfl) ⟨2674349, by rfl⟩ : syracuseStep 3565799 = 5348699) B5348699
theorem B5712403 : Blo 1583990 5712403 := bstep (se 1 (by rfl) ⟨4284302, by rfl⟩ : syracuseStep 5712403 = 8568605) B8568605
theorem B11422291 : Blo 1583990 11422291 := bstep (se 1 (by rfl) ⟨8566718, by rfl⟩ : syracuseStep 11422291 = 17133437) B17133437
theorem B1584231 : Blo 1583990 1584231 := bstep (se 1 (by rfl) ⟨1188173, by rfl⟩ : syracuseStep 1584231 = 2376347) B2376347
theorem B12848233 : Blo 1583990 12848233 := bstep (se 2 (by rfl) ⟨4818087, by rfl⟩ : syracuseStep 12848233 = 9636175) B9636175
theorem B7613615 : Blo 1583990 7613615 := bstep (se 1 (by rfl) ⟨5710211, by rfl⟩ : syracuseStep 7613615 = 11420423) B11420423
theorem B1584335 : Blo 1583990 1584335 := bstep (se 1 (by rfl) ⟨1188251, by rfl⟩ : syracuseStep 1584335 = 2376503) B2376503
theorem B1584455 : Blo 1583990 1584455 := bstep (se 1 (by rfl) ⟨1188341, by rfl⟩ : syracuseStep 1584455 = 2376683) B2376683
theorem B3566969 : Blo 1583990 3566969 := bstep (se 2 (by rfl) ⟨1337613, by rfl⟩ : syracuseStep 3566969 = 2675227) B2675227
theorem B1584667 : Blo 1583990 1584667 := bstep (se 1 (by rfl) ⟨1188500, by rfl⟩ : syracuseStep 1584667 = 2377001) B2377001
theorem B231353981 : Blo 1583990 231353981 := bstep (se 3 (by rfl) ⟨43378871, by rfl⟩ : syracuseStep 231353981 = 86757743) B86757743
theorem B4009895 : Blo 1583990 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B1585243 : Blo 1583990 1585243 := bstep (se 1 (by rfl) ⟨1188932, by rfl⟩ : syracuseStep 1585243 = 2377865) B2377865
theorem B1782247 : Blo 1583990 1782247 := bstep (se 1 (by rfl) ⟨1336685, by rfl⟩ : syracuseStep 1782247 = 2673371) B2673371
theorem B10154483 : Blo 1583990 10154483 := bstep (se 1 (by rfl) ⟨7615862, by rfl⟩ : syracuseStep 10154483 = 15231725) B15231725
theorem B5345999 : Blo 1583990 5345999 := bstep (se 1 (by rfl) ⟨4009499, by rfl⟩ : syracuseStep 5345999 = 8018999) B8018999
theorem B7828175 : Blo 1583990 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B6771431 : Blo 1583990 6771431 := bstep (se 1 (by rfl) ⟨5078573, by rfl⟩ : syracuseStep 6771431 = 10157147) B10157147
theorem B1782895 : Blo 1583990 1782895 := bstep (se 1 (by rfl) ⟨1337171, by rfl⟩ : syracuseStep 1782895 = 2674343) B2674343
theorem B5346863 : Blo 1583990 5346863 := bstep (se 1 (by rfl) ⟨4010147, by rfl⟩ : syracuseStep 5346863 = 8020295) B8020295
theorem B5347241 : Blo 1583990 5347241 := bstep (se 2 (by rfl) ⟨2005215, by rfl⟩ : syracuseStep 5347241 = 4010431) B4010431
theorem B7715839 : Blo 1583990 7715839 := bstep (se 1 (by rfl) ⟨5786879, by rfl⟩ : syracuseStep 7715839 = 11573759) B11573759
theorem B15432839 : Blo 1583990 15432839 := bstep (se 1 (by rfl) ⟨11574629, by rfl⟩ : syracuseStep 15432839 = 23149259) B23149259
theorem B10845323 : Blo 1583990 10845323 := bstep (se 1 (by rfl) ⟨8133992, by rfl⟩ : syracuseStep 10845323 = 16267985) B16267985
theorem B102808925 : Blo 1583990 102808925 := bstep (se 3 (by rfl) ⟨19276673, by rfl⟩ : syracuseStep 102808925 = 38553347) B38553347
theorem B5078447 : Blo 1583990 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B2710975 : Blo 1583990 2710975 := bstep (se 1 (by rfl) ⟨2033231, by rfl⟩ : syracuseStep 2710975 = 4066463) B4066463
theorem B12664774115 : Blo 1583990 12664774115 := bstep (se 1 (by rfl) ⟨9498580586, by rfl⟩ : syracuseStep 12664774115 = 18997161173) B18997161173
theorem B18292205 : Blo 1583990 18292205 := bstep (se 3 (by rfl) ⟨3429788, by rfl⟩ : syracuseStep 18292205 = 6859577) B6859577
theorem B60899201 : Blo 1583990 60899201 := bstep (se 2 (by rfl) ⟨22837200, by rfl⟩ : syracuseStep 60899201 = 45674401) B45674401
theorem B3563999 : Blo 1583990 3563999 := bstep (se 1 (by rfl) ⟨2672999, by rfl⟩ : syracuseStep 3563999 = 5345999) B5345999
theorem B4514287 : Blo 1583990 4514287 := bstep (se 1 (by rfl) ⟨3385715, by rfl⟩ : syracuseStep 4514287 = 6771431) B6771431
theorem B2376329 : Blo 1583990 2376329 := bstep (se 2 (by rfl) ⟨891123, by rfl⟩ : syracuseStep 2376329 = 1782247) B1782247
theorem B15229721 : Blo 1583990 15229721 := bstep (se 2 (by rfl) ⟨5711145, by rfl⟩ : syracuseStep 15229721 = 11422291) B11422291
theorem B2376575 : Blo 1583990 2376575 := bstep (se 1 (by rfl) ⟨1782431, by rfl⟩ : syracuseStep 2376575 = 3564863) B3564863
theorem B3564575 : Blo 1583990 3564575 := bstep (se 1 (by rfl) ⟨2673431, by rfl⟩ : syracuseStep 3564575 = 5346863) B5346863
theorem B5883155 : Blo 1583990 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B3564827 : Blo 1583990 3564827 := bstep (se 1 (by rfl) ⟨2673620, by rfl⟩ : syracuseStep 3564827 = 5347241) B5347241
theorem B17130977 : Blo 1583990 17130977 := bstep (se 2 (by rfl) ⟨6424116, by rfl⟩ : syracuseStep 17130977 = 12848233) B12848233
theorem B2377193 : Blo 1583990 2377193 := bstep (se 2 (by rfl) ⟨891447, by rfl⟩ : syracuseStep 2377193 = 1782895) B1782895
theorem B2377199 : Blo 1583990 2377199 := bstep (se 1 (by rfl) ⟨1782899, by rfl⟩ : syracuseStep 2377199 = 3565799) B3565799
theorem B20875133 : Blo 1583990 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B3614633 : Blo 1583990 3614633 := bstep (se 2 (by rfl) ⟨1355487, by rfl⟩ : syracuseStep 3614633 = 2710975) B2710975
theorem B2377979 : Blo 1583990 2377979 := bstep (se 1 (by rfl) ⟨1783484, by rfl⟩ : syracuseStep 2377979 = 3566969) B3566969
theorem B3385631 : Blo 1583990 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B2673263 : Blo 1583990 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B5286703 : Blo 1583990 5286703 := bstep (se 1 (by rfl) ⟨3965027, by rfl⟩ : syracuseStep 5286703 = 7930055) B7930055
theorem B1584063 : Blo 1583990 1584063 := bstep (se 1 (by rfl) ⟨1188047, by rfl⟩ : syracuseStep 1584063 = 2376095) B2376095
theorem B10578899 : Blo 1583990 10578899 := bstep (se 1 (by rfl) ⟨7934174, by rfl⟩ : syracuseStep 10578899 = 15868349) B15868349
theorem B6769655 : Blo 1583990 6769655 := bstep (se 1 (by rfl) ⟨5077241, by rfl⟩ : syracuseStep 6769655 = 10154483) B10154483
theorem B1584359 : Blo 1583990 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B1584447 : Blo 1583990 1584447 := bstep (se 1 (by rfl) ⟨1188335, by rfl⟩ : syracuseStep 1584447 = 2376671) B2376671
theorem B1584575 : Blo 1583990 1584575 := bstep (se 1 (by rfl) ⟨1188431, by rfl⟩ : syracuseStep 1584575 = 2376863) B2376863
theorem B8023535 : Blo 1583990 8023535 := bstep (se 1 (by rfl) ⟨6017651, by rfl⟩ : syracuseStep 8023535 = 12035303) B12035303
theorem B3567131 : Blo 1583990 3567131 := bstep (se 1 (by rfl) ⟨2675348, by rfl⟩ : syracuseStep 3567131 = 5350697) B5350697
theorem B1585199 : Blo 1583990 1585199 := bstep (se 1 (by rfl) ⟨1188899, by rfl⟩ : syracuseStep 1585199 = 2377799) B2377799
theorem B7230215 : Blo 1583990 7230215 := bstep (se 1 (by rfl) ⟨5422661, by rfl⟩ : syracuseStep 7230215 = 10845323) B10845323
theorem B5075743 : Blo 1583990 5075743 := bstep (se 1 (by rfl) ⟨3806807, by rfl⟩ : syracuseStep 5075743 = 7613615) B7613615
theorem B68539283 : Blo 1583990 68539283 := bstep (se 1 (by rfl) ⟨51404462, by rfl⟩ : syracuseStep 68539283 = 102808925) B102808925
theorem B12194803 : Blo 1583990 12194803 := bstep (se 1 (by rfl) ⟨9146102, by rfl⟩ : syracuseStep 12194803 = 18292205) B18292205
theorem B154235987 : Blo 1583990 154235987 := bstep (se 1 (by rfl) ⟨115676990, by rfl⟩ : syracuseStep 154235987 = 231353981) B231353981
theorem B7616537 : Blo 1583990 7616537 := bstep (se 2 (by rfl) ⟨2856201, by rfl⟩ : syracuseStep 7616537 = 5712403) B5712403
theorem B10287785 : Blo 1583990 10287785 := bstep (se 2 (by rfl) ⟨3857919, by rfl⟩ : syracuseStep 10287785 = 7715839) B7715839
theorem B10288559 : Blo 1583990 10288559 := bstep (se 1 (by rfl) ⟨7716419, by rfl⟩ : syracuseStep 10288559 = 15432839) B15432839
theorem B8443182743 : Blo 1583990 8443182743 := bstep (se 1 (by rfl) ⟨6332387057, by rfl⟩ : syracuseStep 8443182743 = 12664774115) B12664774115
theorem B40599467 : Blo 1583990 40599467 := bstep (se 1 (by rfl) ⟨30449600, by rfl⟩ : syracuseStep 40599467 = 60899201) B60899201
theorem B2375999 : Blo 1583990 2375999 := bstep (se 1 (by rfl) ⟨1781999, by rfl⟩ : syracuseStep 2375999 = 3563999) B3563999
theorem B2376383 : Blo 1583990 2376383 := bstep (se 1 (by rfl) ⟨1782287, by rfl⟩ : syracuseStep 2376383 = 3564575) B3564575
theorem B2376551 : Blo 1583990 2376551 := bstep (se 1 (by rfl) ⟨1782413, by rfl⟩ : syracuseStep 2376551 = 3564827) B3564827
theorem B11420651 : Blo 1583990 11420651 := bstep (se 1 (by rfl) ⟨8565488, by rfl⟩ : syracuseStep 11420651 = 17130977) B17130977
theorem B6767657 : Blo 1583990 6767657 := bstep (se 2 (by rfl) ⟨2537871, by rfl⟩ : syracuseStep 6767657 = 5075743) B5075743
theorem B27436157 : Blo 1583990 27436157 := bstep (se 3 (by rfl) ⟨5144279, by rfl⟩ : syracuseStep 27436157 = 10288559) B10288559
theorem B2409755 : Blo 1583990 2409755 := bstep (se 1 (by rfl) ⟨1807316, by rfl⟩ : syracuseStep 2409755 = 3614633) B3614633
theorem B6858523 : Blo 1583990 6858523 := bstep (se 1 (by rfl) ⟨5143892, by rfl⟩ : syracuseStep 6858523 = 10287785) B10287785
theorem B2378087 : Blo 1583990 2378087 := bstep (se 1 (by rfl) ⟨1783565, by rfl⟩ : syracuseStep 2378087 = 3567131) B3567131
theorem B1584219 : Blo 1583990 1584219 := bstep (se 1 (by rfl) ⟨1188164, by rfl⟩ : syracuseStep 1584219 = 2376329) B2376329
theorem B4820143 : Blo 1583990 4820143 := bstep (se 1 (by rfl) ⟨3615107, by rfl⟩ : syracuseStep 4820143 = 7230215) B7230215
theorem B1584383 : Blo 1583990 1584383 := bstep (se 1 (by rfl) ⟨1188287, by rfl⟩ : syracuseStep 1584383 = 2376575) B2376575
theorem B1584795 : Blo 1583990 1584795 := bstep (se 1 (by rfl) ⟨1188596, by rfl⟩ : syracuseStep 1584795 = 2377193) B2377193
theorem B1584799 : Blo 1583990 1584799 := bstep (se 1 (by rfl) ⟨1188599, by rfl⟩ : syracuseStep 1584799 = 2377199) B2377199
theorem B7048937 : Blo 1583990 7048937 := bstep (se 2 (by rfl) ⟨2643351, by rfl⟩ : syracuseStep 7048937 = 5286703) B5286703
theorem B1585319 : Blo 1583990 1585319 := bstep (se 1 (by rfl) ⟨1188989, by rfl⟩ : syracuseStep 1585319 = 2377979) B2377979
theorem B2257087 : Blo 1583990 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B1782175 : Blo 1583990 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B40612589 : Blo 1583990 40612589 := bstep (se 3 (by rfl) ⟨7614860, by rfl⟩ : syracuseStep 40612589 = 15229721) B15229721
theorem B45692855 : Blo 1583990 45692855 := bstep (se 1 (by rfl) ⟨34269641, by rfl⟩ : syracuseStep 45692855 = 68539283) B68539283
theorem B6019049 : Blo 1583990 6019049 := bstep (se 2 (by rfl) ⟨2257143, by rfl⟩ : syracuseStep 6019049 = 4514287) B4514287
theorem B102823991 : Blo 1583990 102823991 := bstep (se 1 (by rfl) ⟨77117993, by rfl⟩ : syracuseStep 102823991 = 154235987) B154235987
theorem B3922103 : Blo 1583990 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B13916755 : Blo 1583990 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B16259737 : Blo 1583990 16259737 := bstep (se 2 (by rfl) ⟨6097401, by rfl⟩ : syracuseStep 16259737 = 12194803) B12194803
theorem B5077691 : Blo 1583990 5077691 := bstep (se 1 (by rfl) ⟨3808268, by rfl⟩ : syracuseStep 5077691 = 7616537) B7616537
theorem B7052599 : Blo 1583990 7052599 := bstep (se 1 (by rfl) ⟨5289449, by rfl⟩ : syracuseStep 7052599 = 10578899) B10578899
theorem B4513103 : Blo 1583990 4513103 := bstep (se 1 (by rfl) ⟨3384827, by rfl⟩ : syracuseStep 4513103 = 6769655) B6769655
theorem B5349023 : Blo 1583990 5349023 := bstep (se 1 (by rfl) ⟨4011767, by rfl⟩ : syracuseStep 5349023 = 8023535) B8023535
theorem B5628788495 : Blo 1583990 5628788495 := bstep (se 1 (by rfl) ⟨4221591371, by rfl⟩ : syracuseStep 5628788495 = 8443182743) B8443182743
theorem B27066311 : Blo 1583990 27066311 := bstep (se 1 (by rfl) ⟨20299733, by rfl⟩ : syracuseStep 27066311 = 40599467) B40599467
theorem B27075059 : Blo 1583990 27075059 := bstep (se 1 (by rfl) ⟨20306294, by rfl⟩ : syracuseStep 27075059 = 40612589) B40612589
theorem B2376233 : Blo 1583990 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B18555673 : Blo 1583990 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B2614735 : Blo 1583990 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3385127 : Blo 1583990 3385127 := bstep (se 1 (by rfl) ⟨2538845, by rfl⟩ : syracuseStep 3385127 = 5077691) B5077691
theorem B3008735 : Blo 1583990 3008735 := bstep (se 1 (by rfl) ⟨2256551, by rfl⟩ : syracuseStep 3008735 = 4513103) B4513103
theorem B9144697 : Blo 1583990 9144697 := bstep (se 2 (by rfl) ⟨3429261, by rfl⟩ : syracuseStep 9144697 = 6858523) B6858523
theorem B3566015 : Blo 1583990 3566015 := bstep (se 1 (by rfl) ⟨2674511, by rfl⟩ : syracuseStep 3566015 = 5349023) B5349023
theorem B1583999 : Blo 1583990 1583999 := bstep (se 1 (by rfl) ⟨1187999, by rfl⟩ : syracuseStep 1583999 = 2375999) B2375999
theorem B3009449 : Blo 1583990 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B1584255 : Blo 1583990 1584255 := bstep (se 1 (by rfl) ⟨1188191, by rfl⟩ : syracuseStep 1584255 = 2376383) B2376383
theorem B1584367 : Blo 1583990 1584367 := bstep (se 1 (by rfl) ⟨1188275, by rfl⟩ : syracuseStep 1584367 = 2376551) B2376551
theorem B7613767 : Blo 1583990 7613767 := bstep (se 1 (by rfl) ⟨5710325, by rfl⟩ : syracuseStep 7613767 = 11420651) B11420651
theorem B21679649 : Blo 1583990 21679649 := bstep (se 2 (by rfl) ⟨8129868, by rfl⟩ : syracuseStep 21679649 = 16259737) B16259737
theorem B30461903 : Blo 1583990 30461903 := bstep (se 1 (by rfl) ⟨22846427, by rfl⟩ : syracuseStep 30461903 = 45692855) B45692855
theorem B6426857 : Blo 1583990 6426857 := bstep (se 2 (by rfl) ⟨2410071, by rfl⟩ : syracuseStep 6426857 = 4820143) B4820143
theorem B1585391 : Blo 1583990 1585391 := bstep (se 1 (by rfl) ⟨1189043, by rfl⟩ : syracuseStep 1585391 = 2378087) B2378087
theorem B4699291 : Blo 1583990 4699291 := bstep (se 1 (by rfl) ⟨3524468, by rfl⟩ : syracuseStep 4699291 = 7048937) B7048937
theorem B18044207 : Blo 1583990 18044207 := bstep (se 1 (by rfl) ⟨13533155, by rfl⟩ : syracuseStep 18044207 = 27066311) B27066311
theorem B25704053 : Blo 1583990 25704053 := bstep (se 5 (by rfl) ⟨1204877, by rfl⟩ : syracuseStep 25704053 = 2409755) B2409755
theorem B4511771 : Blo 1583990 4511771 := bstep (se 1 (by rfl) ⟨3383828, by rfl⟩ : syracuseStep 4511771 = 6767657) B6767657
theorem B18290771 : Blo 1583990 18290771 := bstep (se 1 (by rfl) ⟨13718078, by rfl⟩ : syracuseStep 18290771 = 27436157) B27436157
theorem B4012699 : Blo 1583990 4012699 := bstep (se 1 (by rfl) ⟨3009524, by rfl⟩ : syracuseStep 4012699 = 6019049) B6019049
theorem B68549327 : Blo 1583990 68549327 := bstep (se 1 (by rfl) ⟨51411995, by rfl⟩ : syracuseStep 68549327 = 102823991) B102823991
theorem B9403465 : Blo 1583990 9403465 := bstep (se 2 (by rfl) ⟨3526299, by rfl⟩ : syracuseStep 9403465 = 7052599) B7052599
theorem B3752525663 : Blo 1583990 3752525663 := bstep (se 1 (by rfl) ⟨2814394247, by rfl⟩ : syracuseStep 3752525663 = 5628788495) B5628788495
theorem B4284571 : Blo 1583990 4284571 := bstep (se 1 (by rfl) ⟨3213428, by rfl⟩ : syracuseStep 4284571 = 6426857) B6426857
theorem B5350265 : Blo 1583990 5350265 := bstep (se 2 (by rfl) ⟨2006349, by rfl⟩ : syracuseStep 5350265 = 4012699) B4012699
theorem B24740897 : Blo 1583990 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B3007847 : Blo 1583990 3007847 := bstep (se 1 (by rfl) ⟨2255885, by rfl⟩ : syracuseStep 3007847 = 4511771) B4511771
theorem B2377343 : Blo 1583990 2377343 := bstep (se 1 (by rfl) ⟨1783007, by rfl⟩ : syracuseStep 2377343 = 3566015) B3566015
theorem B10151689 : Blo 1583990 10151689 := bstep (se 2 (by rfl) ⟨3806883, by rfl⟩ : syracuseStep 10151689 = 7613767) B7613767
theorem B14453099 : Blo 1583990 14453099 := bstep (se 1 (by rfl) ⟨10839824, by rfl⟩ : syracuseStep 14453099 = 21679649) B21679649
theorem B2501683775 : Blo 1583990 2501683775 := bstep (se 1 (by rfl) ⟨1876262831, by rfl⟩ : syracuseStep 2501683775 = 3752525663) B3752525663
theorem B18050039 : Blo 1583990 18050039 := bstep (se 1 (by rfl) ⟨13537529, by rfl⟩ : syracuseStep 18050039 = 27075059) B27075059
theorem B1584155 : Blo 1583990 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B12192929 : Blo 1583990 12192929 := bstep (se 2 (by rfl) ⟨4572348, by rfl⟩ : syracuseStep 12192929 = 9144697) B9144697
theorem B12029471 : Blo 1583990 12029471 := bstep (se 1 (by rfl) ⟨9022103, by rfl⟩ : syracuseStep 12029471 = 18044207) B18044207
theorem B2256751 : Blo 1583990 2256751 := bstep (se 1 (by rfl) ⟨1692563, by rfl⟩ : syracuseStep 2256751 = 3385127) B3385127
theorem B12193847 : Blo 1583990 12193847 := bstep (se 1 (by rfl) ⟨9145385, by rfl⟩ : syracuseStep 12193847 = 18290771) B18290771
theorem B12537953 : Blo 1583990 12537953 := bstep (se 2 (by rfl) ⟨4701732, by rfl⟩ : syracuseStep 12537953 = 9403465) B9403465
theorem B45699551 : Blo 1583990 45699551 := bstep (se 1 (by rfl) ⟨34274663, by rfl⟩ : syracuseStep 45699551 = 68549327) B68549327
theorem B3486313 : Blo 1583990 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B17136035 : Blo 1583990 17136035 := bstep (se 1 (by rfl) ⟨12852026, by rfl⟩ : syracuseStep 17136035 = 25704053) B25704053
theorem B2005823 : Blo 1583990 2005823 := bstep (se 1 (by rfl) ⟨1504367, by rfl⟩ : syracuseStep 2005823 = 3008735) B3008735
theorem B6265721 : Blo 1583990 6265721 := bstep (se 2 (by rfl) ⟨2349645, by rfl⟩ : syracuseStep 6265721 = 4699291) B4699291
theorem B2006299 : Blo 1583990 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B20307935 : Blo 1583990 20307935 := bstep (se 1 (by rfl) ⟨15230951, by rfl⟩ : syracuseStep 20307935 = 30461903) B30461903
theorem B30466367 : Blo 1583990 30466367 := bstep (se 1 (by rfl) ⟨22849775, by rfl⟩ : syracuseStep 30466367 = 45699551) B45699551
theorem B9635399 : Blo 1583990 9635399 := bstep (se 1 (by rfl) ⟨7226549, by rfl⟩ : syracuseStep 9635399 = 14453099) B14453099
theorem B8128619 : Blo 1583990 8128619 := bstep (se 1 (by rfl) ⟨6096464, by rfl⟩ : syracuseStep 8128619 = 12192929) B12192929
theorem B13535585 : Blo 1583990 13535585 := bstep (se 2 (by rfl) ⟨5075844, by rfl⟩ : syracuseStep 13535585 = 10151689) B10151689
theorem B3009001 : Blo 1583990 3009001 := bstep (se 2 (by rfl) ⟨1128375, by rfl⟩ : syracuseStep 3009001 = 2256751) B2256751
theorem B8129231 : Blo 1583990 8129231 := bstep (se 1 (by rfl) ⟨6096923, by rfl⟩ : syracuseStep 8129231 = 12193847) B12193847
theorem B8358635 : Blo 1583990 8358635 := bstep (se 1 (by rfl) ⟨6268976, by rfl⟩ : syracuseStep 8358635 = 12537953) B12537953
theorem B5712761 : Blo 1583990 5712761 := bstep (se 2 (by rfl) ⟨2142285, by rfl⟩ : syracuseStep 5712761 = 4284571) B4284571
theorem B3566843 : Blo 1583990 3566843 := bstep (se 1 (by rfl) ⟨2675132, by rfl⟩ : syracuseStep 3566843 = 5350265) B5350265
theorem B4648417 : Blo 1583990 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B1584895 : Blo 1583990 1584895 := bstep (se 1 (by rfl) ⟨1188671, by rfl⟩ : syracuseStep 1584895 = 2377343) B2377343
theorem B11424023 : Blo 1583990 11424023 := bstep (se 1 (by rfl) ⟨8568017, by rfl⟩ : syracuseStep 11424023 = 17136035) B17136035
theorem B2675065 : Blo 1583990 2675065 := bstep (se 2 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 2675065 = 2006299) B2006299
theorem B1667789183 : Blo 1583990 1667789183 := bstep (se 1 (by rfl) ⟨1250841887, by rfl⟩ : syracuseStep 1667789183 = 2501683775) B2501683775
theorem B16708589 : Blo 1583990 16708589 := bstep (se 3 (by rfl) ⟨3132860, by rfl⟩ : syracuseStep 16708589 = 6265721) B6265721
theorem B13538623 : Blo 1583990 13538623 := bstep (se 1 (by rfl) ⟨10153967, by rfl⟩ : syracuseStep 13538623 = 20307935) B20307935
theorem B65975725 : Blo 1583990 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B2005231 : Blo 1583990 2005231 := bstep (se 1 (by rfl) ⟨1503923, by rfl⟩ : syracuseStep 2005231 = 3007847) B3007847
theorem B12033359 : Blo 1583990 12033359 := bstep (se 1 (by rfl) ⟨9025019, by rfl⟩ : syracuseStep 12033359 = 18050039) B18050039
theorem B5348861 : Blo 1583990 5348861 := bstep (se 3 (by rfl) ⟨1002911, by rfl⟩ : syracuseStep 5348861 = 2005823) B2005823
theorem B8019647 : Blo 1583990 8019647 := bstep (se 1 (by rfl) ⟨6014735, by rfl⟩ : syracuseStep 8019647 = 12029471) B12029471
theorem B1111859455 : Blo 1583990 1111859455 := bstep (se 1 (by rfl) ⟨833894591, by rfl⟩ : syracuseStep 1111859455 = 1667789183) B1667789183
theorem B6423599 : Blo 1583990 6423599 := bstep (se 1 (by rfl) ⟨4817699, by rfl⟩ : syracuseStep 6423599 = 9635399) B9635399
theorem B5572423 : Blo 1583990 5572423 := bstep (se 1 (by rfl) ⟨4179317, by rfl⟩ : syracuseStep 5572423 = 8358635) B8358635
theorem B87967633 : Blo 1583990 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B2377895 : Blo 1583990 2377895 := bstep (se 1 (by rfl) ⟨1783421, by rfl⟩ : syracuseStep 2377895 = 3566843) B3566843
theorem B8022239 : Blo 1583990 8022239 := bstep (se 1 (by rfl) ⟨6016679, by rfl⟩ : syracuseStep 8022239 = 12033359) B12033359
theorem B3565907 : Blo 1583990 3565907 := bstep (se 1 (by rfl) ⟨2674430, by rfl⟩ : syracuseStep 3565907 = 5348861) B5348861
theorem B24791557 : Blo 1583990 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B20310911 : Blo 1583990 20310911 := bstep (se 1 (by rfl) ⟨15233183, by rfl⟩ : syracuseStep 20310911 = 30466367) B30466367
theorem B2673641 : Blo 1583990 2673641 := bstep (se 2 (by rfl) ⟨1002615, by rfl⟩ : syracuseStep 2673641 = 2005231) B2005231
theorem B3566753 : Blo 1583990 3566753 := bstep (se 2 (by rfl) ⟨1337532, by rfl⟩ : syracuseStep 3566753 = 2675065) B2675065
theorem B5419079 : Blo 1583990 5419079 := bstep (se 1 (by rfl) ⟨4064309, by rfl⟩ : syracuseStep 5419079 = 8128619) B8128619
theorem B9023723 : Blo 1583990 9023723 := bstep (se 1 (by rfl) ⟨6767792, by rfl⟩ : syracuseStep 9023723 = 13535585) B13535585
theorem B18051497 : Blo 1583990 18051497 := bstep (se 2 (by rfl) ⟨6769311, by rfl⟩ : syracuseStep 18051497 = 13538623) B13538623
theorem B5419487 : Blo 1583990 5419487 := bstep (se 1 (by rfl) ⟨4064615, by rfl⟩ : syracuseStep 5419487 = 8129231) B8129231
theorem B5346431 : Blo 1583990 5346431 := bstep (se 1 (by rfl) ⟨4009823, by rfl⟩ : syracuseStep 5346431 = 8019647) B8019647
theorem B7616015 : Blo 1583990 7616015 := bstep (se 1 (by rfl) ⟨5712011, by rfl⟩ : syracuseStep 7616015 = 11424023) B11424023
theorem B4012001 : Blo 1583990 4012001 := bstep (se 2 (by rfl) ⟨1504500, by rfl⟩ : syracuseStep 4012001 = 3009001) B3009001
theorem B11139059 : Blo 1583990 11139059 := bstep (se 1 (by rfl) ⟨8354294, by rfl⟩ : syracuseStep 11139059 = 16708589) B16708589
theorem B3808507 : Blo 1583990 3808507 := bstep (se 1 (by rfl) ⟨2856380, by rfl⟩ : syracuseStep 3808507 = 5712761) B5712761
theorem B3612719 : Blo 1583990 3612719 := bstep (se 1 (by rfl) ⟨2709539, by rfl⟩ : syracuseStep 3612719 = 5419079) B5419079
theorem B12034331 : Blo 1583990 12034331 := bstep (se 1 (by rfl) ⟨9025748, by rfl⟩ : syracuseStep 12034331 = 18051497) B18051497
theorem B3612991 : Blo 1583990 3612991 := bstep (se 1 (by rfl) ⟨2709743, by rfl⟩ : syracuseStep 3612991 = 5419487) B5419487
theorem B33055409 : Blo 1583990 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B3564287 : Blo 1583990 3564287 := bstep (se 1 (by rfl) ⟨2673215, by rfl⟩ : syracuseStep 3564287 = 5346431) B5346431
theorem B2377271 : Blo 1583990 2377271 := bstep (se 1 (by rfl) ⟨1782953, by rfl⟩ : syracuseStep 2377271 = 3565907) B3565907
theorem B2377835 : Blo 1583990 2377835 := bstep (se 1 (by rfl) ⟨1783376, by rfl⟩ : syracuseStep 2377835 = 3566753) B3566753
theorem B6015815 : Blo 1583990 6015815 := bstep (se 1 (by rfl) ⟨4511861, by rfl⟩ : syracuseStep 6015815 = 9023723) B9023723
theorem B2674667 : Blo 1583990 2674667 := bstep (se 1 (by rfl) ⟨2006000, by rfl⟩ : syracuseStep 2674667 = 4012001) B4012001
theorem B7426039 : Blo 1583990 7426039 := bstep (se 1 (by rfl) ⟨5569529, by rfl⟩ : syracuseStep 7426039 = 11139059) B11139059
theorem B1585263 : Blo 1583990 1585263 := bstep (se 1 (by rfl) ⟨1188947, by rfl⟩ : syracuseStep 1585263 = 2377895) B2377895
theorem B1782427 : Blo 1583990 1782427 := bstep (se 1 (by rfl) ⟨1336820, by rfl⟩ : syracuseStep 1782427 = 2673641) B2673641
theorem B117290177 : Blo 1583990 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B1482479273 : Blo 1583990 1482479273 := bstep (se 2 (by rfl) ⟨555929727, by rfl⟩ : syracuseStep 1482479273 = 1111859455) B1111859455
theorem B4282399 : Blo 1583990 4282399 := bstep (se 1 (by rfl) ⟨3211799, by rfl⟩ : syracuseStep 4282399 = 6423599) B6423599
theorem B5077343 : Blo 1583990 5077343 := bstep (se 1 (by rfl) ⟨3808007, by rfl⟩ : syracuseStep 5077343 = 7616015) B7616015
theorem B5348159 : Blo 1583990 5348159 := bstep (se 1 (by rfl) ⟨4011119, by rfl⟩ : syracuseStep 5348159 = 8022239) B8022239
theorem B5078009 : Blo 1583990 5078009 := bstep (se 2 (by rfl) ⟨1904253, by rfl⟩ : syracuseStep 5078009 = 3808507) B3808507
theorem B13540607 : Blo 1583990 13540607 := bstep (se 1 (by rfl) ⟨10155455, by rfl⟩ : syracuseStep 13540607 = 20310911) B20310911
theorem B7429897 : Blo 1583990 7429897 := bstep (se 2 (by rfl) ⟨2786211, by rfl⟩ : syracuseStep 7429897 = 5572423) B5572423
theorem B5709865 : Blo 1583990 5709865 := bstep (se 2 (by rfl) ⟨2141199, by rfl⟩ : syracuseStep 5709865 = 4282399) B4282399
theorem B9633917 : Blo 1583990 9633917 := bstep (se 3 (by rfl) ⟨1806359, by rfl⟩ : syracuseStep 9633917 = 3612719) B3612719
theorem B4817321 : Blo 1583990 4817321 := bstep (se 2 (by rfl) ⟨1806495, by rfl⟩ : syracuseStep 4817321 = 3612991) B3612991
theorem B2376191 : Blo 1583990 2376191 := bstep (se 1 (by rfl) ⟨1782143, by rfl⟩ : syracuseStep 2376191 = 3564287) B3564287
theorem B78193451 : Blo 1583990 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B2376569 : Blo 1583990 2376569 := bstep (se 2 (by rfl) ⟨891213, by rfl⟩ : syracuseStep 2376569 = 1782427) B1782427
theorem B88147757 : Blo 1583990 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B3565439 : Blo 1583990 3565439 := bstep (se 1 (by rfl) ⟨2674079, by rfl⟩ : syracuseStep 3565439 = 5348159) B5348159
theorem B9906529 : Blo 1583990 9906529 := bstep (se 2 (by rfl) ⟨3714948, by rfl⟩ : syracuseStep 9906529 = 7429897) B7429897
theorem B8022887 : Blo 1583990 8022887 := bstep (se 1 (by rfl) ⟨6017165, by rfl⟩ : syracuseStep 8022887 = 12034331) B12034331
theorem B1584847 : Blo 1583990 1584847 := bstep (se 1 (by rfl) ⟨1188635, by rfl⟩ : syracuseStep 1584847 = 2377271) B2377271
theorem B988319515 : Blo 1583990 988319515 := bstep (se 1 (by rfl) ⟨741239636, by rfl⟩ : syracuseStep 988319515 = 1482479273) B1482479273
theorem B1585223 : Blo 1583990 1585223 := bstep (se 1 (by rfl) ⟨1188917, by rfl⟩ : syracuseStep 1585223 = 2377835) B2377835
theorem B4010543 : Blo 1583990 4010543 := bstep (se 1 (by rfl) ⟨3007907, by rfl⟩ : syracuseStep 4010543 = 6015815) B6015815
theorem B1783111 : Blo 1583990 1783111 := bstep (se 1 (by rfl) ⟨1337333, by rfl⟩ : syracuseStep 1783111 = 2674667) B2674667
theorem B9901385 : Blo 1583990 9901385 := bstep (se 2 (by rfl) ⟨3713019, by rfl⟩ : syracuseStep 9901385 = 7426039) B7426039
theorem B13539581 : Blo 1583990 13539581 := bstep (se 3 (by rfl) ⟨2538671, by rfl⟩ : syracuseStep 13539581 = 5077343) B5077343
theorem B9027071 : Blo 1583990 9027071 := bstep (se 1 (by rfl) ⟨6770303, by rfl⟩ : syracuseStep 9027071 = 13540607) B13540607
theorem B13541357 : Blo 1583990 13541357 := bstep (se 3 (by rfl) ⟨2539004, by rfl⟩ : syracuseStep 13541357 = 5078009) B5078009
theorem B6422611 : Blo 1583990 6422611 := bstep (se 1 (by rfl) ⟨4816958, by rfl⟩ : syracuseStep 6422611 = 9633917) B9633917
theorem B3211547 : Blo 1583990 3211547 := bstep (se 1 (by rfl) ⟨2408660, by rfl⟩ : syracuseStep 3211547 = 4817321) B4817321
theorem B2376959 : Blo 1583990 2376959 := bstep (se 1 (by rfl) ⟨1782719, by rfl⟩ : syracuseStep 2376959 = 3565439) B3565439
theorem B2377481 : Blo 1583990 2377481 := bstep (se 2 (by rfl) ⟨891555, by rfl⟩ : syracuseStep 2377481 = 1783111) B1783111
theorem B1317759353 : Blo 1583990 1317759353 := bstep (se 2 (by rfl) ⟨494159757, by rfl⟩ : syracuseStep 1317759353 = 988319515) B988319515
theorem B7613153 : Blo 1583990 7613153 := bstep (se 2 (by rfl) ⟨2854932, by rfl⟩ : syracuseStep 7613153 = 5709865) B5709865
theorem B1584127 : Blo 1583990 1584127 := bstep (se 1 (by rfl) ⟨1188095, by rfl⟩ : syracuseStep 1584127 = 2376191) B2376191
theorem B2673695 : Blo 1583990 2673695 := bstep (se 1 (by rfl) ⟨2005271, by rfl⟩ : syracuseStep 2673695 = 4010543) B4010543
theorem B13208705 : Blo 1583990 13208705 := bstep (se 2 (by rfl) ⟨4953264, by rfl⟩ : syracuseStep 13208705 = 9906529) B9906529
theorem B52128967 : Blo 1583990 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B1584379 : Blo 1583990 1584379 := bstep (se 1 (by rfl) ⟨1188284, by rfl⟩ : syracuseStep 1584379 = 2376569) B2376569
theorem B58765171 : Blo 1583990 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B6018047 : Blo 1583990 6018047 := bstep (se 1 (by rfl) ⟨4513535, by rfl⟩ : syracuseStep 6018047 = 9027071) B9027071
theorem B6600923 : Blo 1583990 6600923 := bstep (se 1 (by rfl) ⟨4950692, by rfl⟩ : syracuseStep 6600923 = 9901385) B9901385
theorem B9026387 : Blo 1583990 9026387 := bstep (se 1 (by rfl) ⟨6769790, by rfl⟩ : syracuseStep 9026387 = 13539581) B13539581
theorem B5348591 : Blo 1583990 5348591 := bstep (se 1 (by rfl) ⟨4011443, by rfl⟩ : syracuseStep 5348591 = 8022887) B8022887
theorem B9027571 : Blo 1583990 9027571 := bstep (se 1 (by rfl) ⟨6770678, by rfl⟩ : syracuseStep 9027571 = 13541357) B13541357
theorem B4400615 : Blo 1583990 4400615 := bstep (se 1 (by rfl) ⟨3300461, by rfl⟩ : syracuseStep 4400615 = 6600923) B6600923
theorem B3565727 : Blo 1583990 3565727 := bstep (se 1 (by rfl) ⟨2674295, by rfl⟩ : syracuseStep 3565727 = 5348591) B5348591
theorem B12036761 : Blo 1583990 12036761 := bstep (se 2 (by rfl) ⟨4513785, by rfl⟩ : syracuseStep 12036761 = 9027571) B9027571
theorem B8563481 : Blo 1583990 8563481 := bstep (se 2 (by rfl) ⟨3211305, by rfl⟩ : syracuseStep 8563481 = 6422611) B6422611
theorem B8564125 : Blo 1583990 8564125 := bstep (se 3 (by rfl) ⟨1605773, by rfl⟩ : syracuseStep 8564125 = 3211547) B3211547
theorem B1584639 : Blo 1583990 1584639 := bstep (se 1 (by rfl) ⟨1188479, by rfl⟩ : syracuseStep 1584639 = 2376959) B2376959
theorem B1584987 : Blo 1583990 1584987 := bstep (se 1 (by rfl) ⟨1188740, by rfl⟩ : syracuseStep 1584987 = 2377481) B2377481
theorem B878506235 : Blo 1583990 878506235 := bstep (se 1 (by rfl) ⟨658879676, by rfl⟩ : syracuseStep 878506235 = 1317759353) B1317759353
theorem B69505289 : Blo 1583990 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B5075435 : Blo 1583990 5075435 := bstep (se 1 (by rfl) ⟨3806576, by rfl⟩ : syracuseStep 5075435 = 7613153) B7613153
theorem B6017591 : Blo 1583990 6017591 := bstep (se 1 (by rfl) ⟨4513193, by rfl⟩ : syracuseStep 6017591 = 9026387) B9026387
theorem B1782463 : Blo 1583990 1782463 := bstep (se 1 (by rfl) ⟨1336847, by rfl⟩ : syracuseStep 1782463 = 2673695) B2673695
theorem B78353561 : Blo 1583990 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B4012031 : Blo 1583990 4012031 := bstep (se 1 (by rfl) ⟨3009023, by rfl⟩ : syracuseStep 4012031 = 6018047) B6018047
theorem B8805803 : Blo 1583990 8805803 := bstep (se 1 (by rfl) ⟨6604352, by rfl⟩ : syracuseStep 8805803 = 13208705) B13208705
theorem B585670823 : Blo 1583990 585670823 := bstep (se 1 (by rfl) ⟨439253117, by rfl⟩ : syracuseStep 585670823 = 878506235) B878506235
theorem B3383623 : Blo 1583990 3383623 := bstep (se 1 (by rfl) ⟨2537717, by rfl⟩ : syracuseStep 3383623 = 5075435) B5075435
theorem B2376617 : Blo 1583990 2376617 := bstep (se 2 (by rfl) ⟨891231, by rfl⟩ : syracuseStep 2376617 = 1782463) B1782463
theorem B2933743 : Blo 1583990 2933743 := bstep (se 1 (by rfl) ⟨2200307, by rfl⟩ : syracuseStep 2933743 = 4400615) B4400615
theorem B2377151 : Blo 1583990 2377151 := bstep (se 1 (by rfl) ⟨1782863, by rfl⟩ : syracuseStep 2377151 = 3565727) B3565727
theorem B46336859 : Blo 1583990 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B52235707 : Blo 1583990 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B2674687 : Blo 1583990 2674687 := bstep (se 1 (by rfl) ⟨2006015, by rfl⟩ : syracuseStep 2674687 = 4012031) B4012031
theorem B8024507 : Blo 1583990 8024507 := bstep (se 1 (by rfl) ⟨6018380, by rfl⟩ : syracuseStep 8024507 = 12036761) B12036761
theorem B4011727 : Blo 1583990 4011727 := bstep (se 1 (by rfl) ⟨3008795, by rfl⟩ : syracuseStep 4011727 = 6017591) B6017591
theorem B93928565 : Blo 1583990 93928565 := bstep (se 5 (by rfl) ⟨4402901, by rfl⟩ : syracuseStep 93928565 = 8805803) B8805803
theorem B5708987 : Blo 1583990 5708987 := bstep (se 1 (by rfl) ⟨4281740, by rfl⟩ : syracuseStep 5708987 = 8563481) B8563481
theorem B11418833 : Blo 1583990 11418833 := bstep (se 2 (by rfl) ⟨4282062, by rfl⟩ : syracuseStep 11418833 = 8564125) B8564125
theorem B390447215 : Blo 1583990 390447215 := bstep (se 1 (by rfl) ⟨292835411, by rfl⟩ : syracuseStep 390447215 = 585670823) B585670823
theorem B5349671 : Blo 1583990 5349671 := bstep (se 1 (by rfl) ⟨4012253, by rfl⟩ : syracuseStep 5349671 = 8024507) B8024507
theorem B7612555 : Blo 1583990 7612555 := bstep (se 1 (by rfl) ⟨5709416, by rfl⟩ : syracuseStep 7612555 = 11418833) B11418833
theorem B3566249 : Blo 1583990 3566249 := bstep (se 2 (by rfl) ⟨1337343, by rfl⟩ : syracuseStep 3566249 = 2674687) B2674687
theorem B1584411 : Blo 1583990 1584411 := bstep (se 1 (by rfl) ⟨1188308, by rfl⟩ : syracuseStep 1584411 = 2376617) B2376617
theorem B1584767 : Blo 1583990 1584767 := bstep (se 1 (by rfl) ⟨1188575, by rfl⟩ : syracuseStep 1584767 = 2377151) B2377151
theorem B3911657 : Blo 1583990 3911657 := bstep (se 2 (by rfl) ⟨1466871, by rfl⟩ : syracuseStep 3911657 = 2933743) B2933743
theorem B3805991 : Blo 1583990 3805991 := bstep (se 1 (by rfl) ⟨2854493, by rfl⟩ : syracuseStep 3805991 = 5708987) B5708987
theorem B4511497 : Blo 1583990 4511497 := bstep (se 2 (by rfl) ⟨1691811, by rfl⟩ : syracuseStep 4511497 = 3383623) B3383623
theorem B30891239 : Blo 1583990 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B69647609 : Blo 1583990 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B62619043 : Blo 1583990 62619043 := bstep (se 1 (by rfl) ⟨46964282, by rfl⟩ : syracuseStep 62619043 = 93928565) B93928565
theorem B5348969 : Blo 1583990 5348969 := bstep (se 2 (by rfl) ⟨2005863, by rfl⟩ : syracuseStep 5348969 = 4011727) B4011727
theorem B10150073 : Blo 1583990 10150073 := bstep (se 2 (by rfl) ⟨3806277, by rfl⟩ : syracuseStep 10150073 = 7612555) B7612555
theorem B2377499 : Blo 1583990 2377499 := bstep (se 1 (by rfl) ⟨1783124, by rfl⟩ : syracuseStep 2377499 = 3566249) B3566249
theorem B6015329 : Blo 1583990 6015329 := bstep (se 2 (by rfl) ⟨2255748, by rfl⟩ : syracuseStep 6015329 = 4511497) B4511497
theorem B3565979 : Blo 1583990 3565979 := bstep (se 1 (by rfl) ⟨2674484, by rfl⟩ : syracuseStep 3565979 = 5348969) B5348969
theorem B10431085 : Blo 1583990 10431085 := bstep (se 3 (by rfl) ⟨1955828, by rfl⟩ : syracuseStep 10431085 = 3911657) B3911657
theorem B3566447 : Blo 1583990 3566447 := bstep (se 1 (by rfl) ⟨2674835, by rfl⟩ : syracuseStep 3566447 = 5349671) B5349671
theorem B260298143 : Blo 1583990 260298143 := bstep (se 1 (by rfl) ⟨195223607, by rfl⟩ : syracuseStep 260298143 = 390447215) B390447215
theorem B2537327 : Blo 1583990 2537327 := bstep (se 1 (by rfl) ⟨1902995, by rfl⟩ : syracuseStep 2537327 = 3805991) B3805991
theorem B83492057 : Blo 1583990 83492057 := bstep (se 2 (by rfl) ⟨31309521, by rfl⟩ : syracuseStep 83492057 = 62619043) B62619043
theorem B20594159 : Blo 1583990 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B46431739 : Blo 1583990 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B6766715 : Blo 1583990 6766715 := bstep (se 1 (by rfl) ⟨5075036, by rfl⟩ : syracuseStep 6766715 = 10150073) B10150073
theorem B173532095 : Blo 1583990 173532095 := bstep (se 1 (by rfl) ⟨130149071, by rfl⟩ : syracuseStep 173532095 = 260298143) B260298143
theorem B2377319 : Blo 1583990 2377319 := bstep (se 1 (by rfl) ⟨1782989, by rfl⟩ : syracuseStep 2377319 = 3565979) B3565979
theorem B2377631 : Blo 1583990 2377631 := bstep (se 1 (by rfl) ⟨1783223, by rfl⟩ : syracuseStep 2377631 = 3566447) B3566447
theorem B61908985 : Blo 1583990 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B222645485 : Blo 1583990 222645485 := bstep (se 3 (by rfl) ⟨41746028, by rfl⟩ : syracuseStep 222645485 = 83492057) B83492057
theorem B1584999 : Blo 1583990 1584999 := bstep (se 1 (by rfl) ⟨1188749, by rfl⟩ : syracuseStep 1584999 = 2377499) B2377499
theorem B1691551 : Blo 1583990 1691551 := bstep (se 1 (by rfl) ⟨1268663, by rfl⟩ : syracuseStep 1691551 = 2537327) B2537327
theorem B4010219 : Blo 1583990 4010219 := bstep (se 1 (by rfl) ⟨3007664, by rfl⟩ : syracuseStep 4010219 = 6015329) B6015329
theorem B13908113 : Blo 1583990 13908113 := bstep (se 2 (by rfl) ⟨5215542, by rfl⟩ : syracuseStep 13908113 = 10431085) B10431085
theorem B13729439 : Blo 1583990 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B115688063 : Blo 1583990 115688063 := bstep (se 1 (by rfl) ⟨86766047, by rfl⟩ : syracuseStep 115688063 = 173532095) B173532095
theorem B9152959 : Blo 1583990 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B2255401 : Blo 1583990 2255401 := bstep (se 2 (by rfl) ⟨845775, by rfl⟩ : syracuseStep 2255401 = 1691551) B1691551
theorem B82545313 : Blo 1583990 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B2673479 : Blo 1583990 2673479 := bstep (se 1 (by rfl) ⟨2005109, by rfl⟩ : syracuseStep 2673479 = 4010219) B4010219
theorem B1584879 : Blo 1583990 1584879 := bstep (se 1 (by rfl) ⟨1188659, by rfl⟩ : syracuseStep 1584879 = 2377319) B2377319
theorem B1585087 : Blo 1583990 1585087 := bstep (se 1 (by rfl) ⟨1188815, by rfl⟩ : syracuseStep 1585087 = 2377631) B2377631
theorem B4511143 : Blo 1583990 4511143 := bstep (se 1 (by rfl) ⟨3383357, by rfl⟩ : syracuseStep 4511143 = 6766715) B6766715
theorem B9272075 : Blo 1583990 9272075 := bstep (se 1 (by rfl) ⟨6954056, by rfl⟩ : syracuseStep 9272075 = 13908113) B13908113
theorem B148430323 : Blo 1583990 148430323 := bstep (se 1 (by rfl) ⟨111322742, by rfl⟩ : syracuseStep 148430323 = 222645485) B222645485
theorem B98902133 : Blo 1583990 98902133 := bstep (se 5 (by rfl) ⟨4636037, by rfl⟩ : syracuseStep 98902133 = 9272075) B9272075
theorem B3007201 : Blo 1583990 3007201 := bstep (se 2 (by rfl) ⟨1127700, by rfl⟩ : syracuseStep 3007201 = 2255401) B2255401
theorem B110060417 : Blo 1583990 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B6014857 : Blo 1583990 6014857 := bstep (se 2 (by rfl) ⟨2255571, by rfl⟩ : syracuseStep 6014857 = 4511143) B4511143
theorem B1782319 : Blo 1583990 1782319 := bstep (se 1 (by rfl) ⟨1336739, by rfl⟩ : syracuseStep 1782319 = 2673479) B2673479
theorem B197907097 : Blo 1583990 197907097 := bstep (se 2 (by rfl) ⟨74215161, by rfl⟩ : syracuseStep 197907097 = 148430323) B148430323
theorem B77125375 : Blo 1583990 77125375 := bstep (se 1 (by rfl) ⟨57844031, by rfl⟩ : syracuseStep 77125375 = 115688063) B115688063
theorem B12203945 : Blo 1583990 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B2376425 : Blo 1583990 2376425 := bstep (se 2 (by rfl) ⟨891159, by rfl⟩ : syracuseStep 2376425 = 1782319) B1782319
theorem B8135963 : Blo 1583990 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B263876129 : Blo 1583990 263876129 := bstep (se 2 (by rfl) ⟨98953548, by rfl⟩ : syracuseStep 263876129 = 197907097) B197907097
theorem B4009601 : Blo 1583990 4009601 := bstep (se 2 (by rfl) ⟨1503600, by rfl⟩ : syracuseStep 4009601 = 3007201) B3007201
theorem B65934755 : Blo 1583990 65934755 := bstep (se 1 (by rfl) ⟨49451066, by rfl⟩ : syracuseStep 65934755 = 98902133) B98902133
theorem B73373611 : Blo 1583990 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B102833833 : Blo 1583990 102833833 := bstep (se 2 (by rfl) ⟨38562687, by rfl⟩ : syracuseStep 102833833 = 77125375) B77125375
theorem B8019809 : Blo 1583990 8019809 := bstep (se 2 (by rfl) ⟨3007428, by rfl⟩ : syracuseStep 8019809 = 6014857) B6014857
theorem B5423975 : Blo 1583990 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B137111777 : Blo 1583990 137111777 := bstep (se 2 (by rfl) ⟨51416916, by rfl⟩ : syracuseStep 137111777 = 102833833) B102833833
theorem B175917419 : Blo 1583990 175917419 := bstep (se 1 (by rfl) ⟨131938064, by rfl⟩ : syracuseStep 175917419 = 263876129) B263876129
theorem B2673067 : Blo 1583990 2673067 := bstep (se 1 (by rfl) ⟨2004800, by rfl⟩ : syracuseStep 2673067 = 4009601) B4009601
theorem B97831481 : Blo 1583990 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B1584283 : Blo 1583990 1584283 := bstep (se 1 (by rfl) ⟨1188212, by rfl⟩ : syracuseStep 1584283 = 2376425) B2376425
theorem B5346539 : Blo 1583990 5346539 := bstep (se 1 (by rfl) ⟨4009904, by rfl⟩ : syracuseStep 5346539 = 8019809) B8019809
theorem B43956503 : Blo 1583990 43956503 := bstep (se 1 (by rfl) ⟨32967377, by rfl⟩ : syracuseStep 43956503 = 65934755) B65934755
theorem B3564089 : Blo 1583990 3564089 := bstep (se 2 (by rfl) ⟨1336533, by rfl⟩ : syracuseStep 3564089 = 2673067) B2673067
theorem B3564359 : Blo 1583990 3564359 := bstep (se 1 (by rfl) ⟨2673269, by rfl⟩ : syracuseStep 3564359 = 5346539) B5346539
theorem B91407851 : Blo 1583990 91407851 := bstep (se 1 (by rfl) ⟨68555888, by rfl⟩ : syracuseStep 91407851 = 137111777) B137111777
theorem B29304335 : Blo 1583990 29304335 := bstep (se 1 (by rfl) ⟨21978251, by rfl⟩ : syracuseStep 29304335 = 43956503) B43956503
theorem B117278279 : Blo 1583990 117278279 := bstep (se 1 (by rfl) ⟨87958709, by rfl⟩ : syracuseStep 117278279 = 175917419) B175917419
theorem B3615983 : Blo 1583990 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B1043535797 : Blo 1583990 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B2376059 : Blo 1583990 2376059 := bstep (se 1 (by rfl) ⟨1782044, by rfl⟩ : syracuseStep 2376059 = 3564089) B3564089
theorem B2376239 : Blo 1583990 2376239 := bstep (se 1 (by rfl) ⟨1782179, by rfl⟩ : syracuseStep 2376239 = 3564359) B3564359
theorem B78185519 : Blo 1583990 78185519 := bstep (se 1 (by rfl) ⟨58639139, by rfl⟩ : syracuseStep 78185519 = 117278279) B117278279
theorem B695690531 : Blo 1583990 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B2410655 : Blo 1583990 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B60938567 : Blo 1583990 60938567 := bstep (se 1 (by rfl) ⟨45703925, by rfl⟩ : syracuseStep 60938567 = 91407851) B91407851
theorem B19536223 : Blo 1583990 19536223 := bstep (se 1 (by rfl) ⟨14652167, by rfl⟩ : syracuseStep 19536223 = 29304335) B29304335
theorem B40625711 : Blo 1583990 40625711 := bstep (se 1 (by rfl) ⟨30469283, by rfl⟩ : syracuseStep 40625711 = 60938567) B60938567
theorem B1584039 : Blo 1583990 1584039 := bstep (se 1 (by rfl) ⟨1188029, by rfl⟩ : syracuseStep 1584039 = 2376059) B2376059
theorem B1584159 : Blo 1583990 1584159 := bstep (se 1 (by rfl) ⟨1188119, by rfl⟩ : syracuseStep 1584159 = 2376239) B2376239
theorem B463793687 : Blo 1583990 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B6428413 : Blo 1583990 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B26048297 : Blo 1583990 26048297 := bstep (se 2 (by rfl) ⟨9768111, by rfl⟩ : syracuseStep 26048297 = 19536223) B19536223
theorem B52123679 : Blo 1583990 52123679 := bstep (se 1 (by rfl) ⟨39092759, by rfl⟩ : syracuseStep 52123679 = 78185519) B78185519
theorem B27083807 : Blo 1583990 27083807 := bstep (se 1 (by rfl) ⟨20312855, by rfl⟩ : syracuseStep 27083807 = 40625711) B40625711
theorem B34284869 : Blo 1583990 34284869 := bstep (se 4 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 34284869 = 6428413) B6428413
theorem B69462125 : Blo 1583990 69462125 := bstep (se 3 (by rfl) ⟨13024148, by rfl⟩ : syracuseStep 69462125 = 26048297) B26048297
theorem B309195791 : Blo 1583990 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B34749119 : Blo 1583990 34749119 := bstep (se 1 (by rfl) ⟨26061839, by rfl⟩ : syracuseStep 34749119 = 52123679) B52123679
theorem B18055871 : Blo 1583990 18055871 := bstep (se 1 (by rfl) ⟨13541903, by rfl⟩ : syracuseStep 18055871 = 27083807) B27083807
theorem B22856579 : Blo 1583990 22856579 := bstep (se 1 (by rfl) ⟨17142434, by rfl⟩ : syracuseStep 22856579 = 34284869) B34284869
theorem B206130527 : Blo 1583990 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B92664317 : Blo 1583990 92664317 := bstep (se 3 (by rfl) ⟨17374559, by rfl⟩ : syracuseStep 92664317 = 34749119) B34749119
theorem B46308083 : Blo 1583990 46308083 := bstep (se 1 (by rfl) ⟨34731062, by rfl⟩ : syracuseStep 46308083 = 69462125) B69462125
theorem B61776211 : Blo 1583990 61776211 := bstep (se 1 (by rfl) ⟨46332158, by rfl⟩ : syracuseStep 61776211 = 92664317) B92664317
theorem B15237719 : Blo 1583990 15237719 := bstep (se 1 (by rfl) ⟨11428289, by rfl⟩ : syracuseStep 15237719 = 22856579) B22856579
theorem B123488221 : Blo 1583990 123488221 := bstep (se 3 (by rfl) ⟨23154041, by rfl⟩ : syracuseStep 123488221 = 46308083) B46308083
theorem B12037247 : Blo 1583990 12037247 := bstep (se 1 (by rfl) ⟨9027935, by rfl⟩ : syracuseStep 12037247 = 18055871) B18055871
theorem B137420351 : Blo 1583990 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B10158479 : Blo 1583990 10158479 := bstep (se 1 (by rfl) ⟨7618859, by rfl⟩ : syracuseStep 10158479 = 15237719) B15237719
theorem B91613567 : Blo 1583990 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B8024831 : Blo 1583990 8024831 := bstep (se 1 (by rfl) ⟨6018623, by rfl⟩ : syracuseStep 8024831 = 12037247) B12037247
theorem B82368281 : Blo 1583990 82368281 := bstep (se 2 (by rfl) ⟨30888105, by rfl⟩ : syracuseStep 82368281 = 61776211) B61776211
theorem B164650961 : Blo 1583990 164650961 := bstep (se 2 (by rfl) ⟨61744110, by rfl⟩ : syracuseStep 164650961 = 123488221) B123488221
theorem B5349887 : Blo 1583990 5349887 := bstep (se 1 (by rfl) ⟨4012415, by rfl⟩ : syracuseStep 5349887 = 8024831) B8024831
theorem B54912187 : Blo 1583990 54912187 := bstep (se 1 (by rfl) ⟨41184140, by rfl⟩ : syracuseStep 54912187 = 82368281) B82368281
theorem B109767307 : Blo 1583990 109767307 := bstep (se 1 (by rfl) ⟨82325480, by rfl⟩ : syracuseStep 109767307 = 164650961) B164650961
theorem B61075711 : Blo 1583990 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B6772319 : Blo 1583990 6772319 := bstep (se 1 (by rfl) ⟨5079239, by rfl⟩ : syracuseStep 6772319 = 10158479) B10158479
theorem B292864997 : Blo 1583990 292864997 := bstep (se 4 (by rfl) ⟨27456093, by rfl⟩ : syracuseStep 292864997 = 54912187) B54912187
theorem B4514879 : Blo 1583990 4514879 := bstep (se 1 (by rfl) ⟨3386159, by rfl⟩ : syracuseStep 4514879 = 6772319) B6772319
theorem B3566591 : Blo 1583990 3566591 := bstep (se 1 (by rfl) ⟨2674943, by rfl⟩ : syracuseStep 3566591 = 5349887) B5349887
theorem B81434281 : Blo 1583990 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B146356409 : Blo 1583990 146356409 := bstep (se 2 (by rfl) ⟨54883653, by rfl⟩ : syracuseStep 146356409 = 109767307) B109767307
theorem B2377727 : Blo 1583990 2377727 := bstep (se 1 (by rfl) ⟨1783295, by rfl⟩ : syracuseStep 2377727 = 3566591) B3566591
theorem B108579041 : Blo 1583990 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B195243331 : Blo 1583990 195243331 := bstep (se 1 (by rfl) ⟨146432498, by rfl⟩ : syracuseStep 195243331 = 292864997) B292864997
theorem B97570939 : Blo 1583990 97570939 := bstep (se 1 (by rfl) ⟨73178204, by rfl⟩ : syracuseStep 97570939 = 146356409) B146356409
theorem B12039677 : Blo 1583990 12039677 := bstep (se 3 (by rfl) ⟨2257439, by rfl⟩ : syracuseStep 12039677 = 4514879) B4514879
theorem B72386027 : Blo 1583990 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B1585151 : Blo 1583990 1585151 := bstep (se 1 (by rfl) ⟨1188863, by rfl⟩ : syracuseStep 1585151 = 2377727) B2377727
theorem B130094585 : Blo 1583990 130094585 := bstep (se 2 (by rfl) ⟨48785469, by rfl⟩ : syracuseStep 130094585 = 97570939) B97570939
theorem B8026451 : Blo 1583990 8026451 := bstep (se 1 (by rfl) ⟨6019838, by rfl⟩ : syracuseStep 8026451 = 12039677) B12039677
theorem B260324441 : Blo 1583990 260324441 := bstep (se 2 (by rfl) ⟨97621665, by rfl⟩ : syracuseStep 260324441 = 195243331) B195243331
theorem B86729723 : Blo 1583990 86729723 := bstep (se 1 (by rfl) ⟨65047292, by rfl⟩ : syracuseStep 86729723 = 130094585) B130094585
theorem B5350967 : Blo 1583990 5350967 := bstep (se 1 (by rfl) ⟨4013225, by rfl⟩ : syracuseStep 5350967 = 8026451) B8026451
theorem B173549627 : Blo 1583990 173549627 := bstep (se 1 (by rfl) ⟨130162220, by rfl⟩ : syracuseStep 173549627 = 260324441) B260324441
theorem B48257351 : Blo 1583990 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B57819815 : Blo 1583990 57819815 := bstep (se 1 (by rfl) ⟨43364861, by rfl⟩ : syracuseStep 57819815 = 86729723) B86729723
theorem B32171567 : Blo 1583990 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B3567311 : Blo 1583990 3567311 := bstep (se 1 (by rfl) ⟨2675483, by rfl⟩ : syracuseStep 3567311 = 5350967) B5350967
theorem B115699751 : Blo 1583990 115699751 := bstep (se 1 (by rfl) ⟨86774813, by rfl⟩ : syracuseStep 115699751 = 173549627) B173549627
theorem B2378207 : Blo 1583990 2378207 := bstep (se 1 (by rfl) ⟨1783655, by rfl⟩ : syracuseStep 2378207 = 3567311) B3567311
theorem B38546543 : Blo 1583990 38546543 := bstep (se 1 (by rfl) ⟨28909907, by rfl⟩ : syracuseStep 38546543 = 57819815) B57819815
theorem B85790845 : Blo 1583990 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B77133167 : Blo 1583990 77133167 := bstep (se 1 (by rfl) ⟨57849875, by rfl⟩ : syracuseStep 77133167 = 115699751) B115699751
theorem B51422111 : Blo 1583990 51422111 := bstep (se 1 (by rfl) ⟨38566583, by rfl⟩ : syracuseStep 51422111 = 77133167) B77133167
theorem B457551173 : Blo 1583990 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B1585471 : Blo 1583990 1585471 := bstep (se 1 (by rfl) ⟨1189103, by rfl⟩ : syracuseStep 1585471 = 2378207) B2378207
theorem B25697695 : Blo 1583990 25697695 := bstep (se 1 (by rfl) ⟨19273271, by rfl⟩ : syracuseStep 25697695 = 38546543) B38546543
theorem B34263593 : Blo 1583990 34263593 := bstep (se 2 (by rfl) ⟨12848847, by rfl⟩ : syracuseStep 34263593 = 25697695) B25697695
theorem B305034115 : Blo 1583990 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B34281407 : Blo 1583990 34281407 := bstep (se 1 (by rfl) ⟨25711055, by rfl⟩ : syracuseStep 34281407 = 51422111) B51422111
theorem B22842395 : Blo 1583990 22842395 := bstep (se 1 (by rfl) ⟨17131796, by rfl⟩ : syracuseStep 22842395 = 34263593) B34263593
theorem B406712153 : Blo 1583990 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B22854271 : Blo 1583990 22854271 := bstep (se 1 (by rfl) ⟨17140703, by rfl⟩ : syracuseStep 22854271 = 34281407) B34281407
theorem B271141435 : Blo 1583990 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B30472361 : Blo 1583990 30472361 := bstep (se 2 (by rfl) ⟨11427135, by rfl⟩ : syracuseStep 30472361 = 22854271) B22854271
theorem B15228263 : Blo 1583990 15228263 := bstep (se 1 (by rfl) ⟨11421197, by rfl⟩ : syracuseStep 15228263 = 22842395) B22842395
theorem B10152175 : Blo 1583990 10152175 := bstep (se 1 (by rfl) ⟨7614131, by rfl⟩ : syracuseStep 10152175 = 15228263) B15228263
theorem B1446087653 : Blo 1583990 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B20314907 : Blo 1583990 20314907 := bstep (se 1 (by rfl) ⟨15236180, by rfl⟩ : syracuseStep 20314907 = 30472361) B30472361
theorem B13543271 : Blo 1583990 13543271 := bstep (se 1 (by rfl) ⟨10157453, by rfl⟩ : syracuseStep 13543271 = 20314907) B20314907
theorem B13536233 : Blo 1583990 13536233 := bstep (se 2 (by rfl) ⟨5076087, by rfl⟩ : syracuseStep 13536233 = 10152175) B10152175
theorem B964058435 : Blo 1583990 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B9028847 : Blo 1583990 9028847 := bstep (se 1 (by rfl) ⟨6771635, by rfl⟩ : syracuseStep 9028847 = 13543271) B13543271
theorem B642705623 : Blo 1583990 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B9024155 : Blo 1583990 9024155 := bstep (se 1 (by rfl) ⟨6768116, by rfl⟩ : syracuseStep 9024155 = 13536233) B13536233
theorem B6016103 : Blo 1583990 6016103 := bstep (se 1 (by rfl) ⟨4512077, by rfl⟩ : syracuseStep 6016103 = 9024155) B9024155
theorem B428470415 : Blo 1583990 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B6019231 : Blo 1583990 6019231 := bstep (se 1 (by rfl) ⟨4514423, by rfl⟩ : syracuseStep 6019231 = 9028847) B9028847
theorem B285646943 : Blo 1583990 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B4010735 : Blo 1583990 4010735 := bstep (se 1 (by rfl) ⟨3008051, by rfl⟩ : syracuseStep 4010735 = 6016103) B6016103
theorem B8025641 : Blo 1583990 8025641 := bstep (se 2 (by rfl) ⟨3009615, by rfl⟩ : syracuseStep 8025641 = 6019231) B6019231
theorem B761725181 : Blo 1583990 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B5350427 : Blo 1583990 5350427 := bstep (se 1 (by rfl) ⟨4012820, by rfl⟩ : syracuseStep 5350427 = 8025641) B8025641
theorem B2673823 : Blo 1583990 2673823 := bstep (se 1 (by rfl) ⟨2005367, by rfl⟩ : syracuseStep 2673823 = 4010735) B4010735
theorem B3565097 : Blo 1583990 3565097 := bstep (se 2 (by rfl) ⟨1336911, by rfl⟩ : syracuseStep 3565097 = 2673823) B2673823
theorem B507816787 : Blo 1583990 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B3566951 : Blo 1583990 3566951 := bstep (se 1 (by rfl) ⟨2675213, by rfl⟩ : syracuseStep 3566951 = 5350427) B5350427
theorem B2376731 : Blo 1583990 2376731 := bstep (se 1 (by rfl) ⟨1782548, by rfl⟩ : syracuseStep 2376731 = 3565097) B3565097
theorem B2377967 : Blo 1583990 2377967 := bstep (se 1 (by rfl) ⟨1783475, by rfl⟩ : syracuseStep 2377967 = 3566951) B3566951
theorem B677089049 : Blo 1583990 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1584487 : Blo 1583990 1584487 := bstep (se 1 (by rfl) ⟨1188365, by rfl⟩ : syracuseStep 1584487 = 2376731) B2376731
theorem B1585311 : Blo 1583990 1585311 := bstep (se 1 (by rfl) ⟨1188983, by rfl⟩ : syracuseStep 1585311 = 2377967) B2377967
theorem B1805570797 : Blo 1583990 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 1583990 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 1583990 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 1583990 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 1583990 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 1583990 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 1583990 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 1583990 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 1583990 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1583990 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 1583990 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 1583990 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 1583990 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 1583990 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1583990 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 1583990 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 1583990 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1583990 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 1583990 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1583990 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 1583990 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1583990 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 1583990 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 1583990 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 1583990 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1583990 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 1583990 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 1583990 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 1583990 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 1583990 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 1583990 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 1583990 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 1583990 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 1583990 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 1583990 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 1583990 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 1583990 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 1583990 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 1583990 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 1583990 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 1583990 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B1783579 : Blo 1583990 1783579 := bstep (se 1 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 1783579 = 2675369) B2675369
theorem B2378105 : Blo 1583990 2378105 := bstep (se 2 (by rfl) ⟨891789, by rfl⟩ : syracuseStep 2378105 = 1783579) B1783579
theorem B1585403 : Blo 1583990 1585403 := bstep (se 1 (by rfl) ⟨1189052, by rfl⟩ : syracuseStep 1585403 = 2378105) B2378105

theorem C0 (j : ℕ) (h1 : 395997 ≤ j) (h2 : j ≤ 396371) : Blo 1583990 (4 * j + 3) := by
  interval_cases j
  · exact B1583991
  · exact B1583995
  · exact B1583999
  · exact B1584003
  · exact B1584007
  · exact B1584011
  · exact B1584015
  · exact B1584019
  · exact B1584023
  · exact B1584027
  · exact B1584031
  · exact B1584035
  · exact B1584039
  · exact B1584043
  · exact B1584047
  · exact B1584051
  · exact B1584055
  · exact B1584059
  · exact B1584063
  · exact B1584067
  · exact B1584071
  · exact B1584075
  · exact B1584079
  · exact B1584083
  · exact B1584087
  · exact B1584091
  · exact B1584095
  · exact B1584099
  · exact B1584103
  · exact B1584107
  · exact B1584111
  · exact B1584115
  · exact B1584119
  · exact B1584123
  · exact B1584127
  · exact B1584131
  · exact B1584135
  · exact B1584139
  · exact B1584143
  · exact B1584147
  · exact B1584151
  · exact B1584155
  · exact B1584159
  · exact B1584163
  · exact B1584167
  · exact B1584171
  · exact B1584175
  · exact B1584179
  · exact B1584183
  · exact B1584187
  · exact B1584191
  · exact B1584195
  · exact B1584199
  · exact B1584203
  · exact B1584207
  · exact B1584211
  · exact B1584215
  · exact B1584219
  · exact B1584223
  · exact B1584227
  · exact B1584231
  · exact B1584235
  · exact B1584239
  · exact B1584243
  · exact B1584247
  · exact B1584251
  · exact B1584255
  · exact B1584259
  · exact B1584263
  · exact B1584267
  · exact B1584271
  · exact B1584275
  · exact B1584279
  · exact B1584283
  · exact B1584287
  · exact B1584291
  · exact B1584295
  · exact B1584299
  · exact B1584303
  · exact B1584307
  · exact B1584311
  · exact B1584315
  · exact B1584319
  · exact B1584323
  · exact B1584327
  · exact B1584331
  · exact B1584335
  · exact B1584339
  · exact B1584343
  · exact B1584347
  · exact B1584351
  · exact B1584355
  · exact B1584359
  · exact B1584363
  · exact B1584367
  · exact B1584371
  · exact B1584375
  · exact B1584379
  · exact B1584383
  · exact B1584387
  · exact B1584391
  · exact B1584395
  · exact B1584399
  · exact B1584403
  · exact B1584407
  · exact B1584411
  · exact B1584415
  · exact B1584419
  · exact B1584423
  · exact B1584427
  · exact B1584431
  · exact B1584435
  · exact B1584439
  · exact B1584443
  · exact B1584447
  · exact B1584451
  · exact B1584455
  · exact B1584459
  · exact B1584463
  · exact B1584467
  · exact B1584471
  · exact B1584475
  · exact B1584479
  · exact B1584483
  · exact B1584487
  · exact B1584491
  · exact B1584495
  · exact B1584499
  · exact B1584503
  · exact B1584507
  · exact B1584511
  · exact B1584515
  · exact B1584519
  · exact B1584523
  · exact B1584527
  · exact B1584531
  · exact B1584535
  · exact B1584539
  · exact B1584543
  · exact B1584547
  · exact B1584551
  · exact B1584555
  · exact B1584559
  · exact B1584563
  · exact B1584567
  · exact B1584571
  · exact B1584575
  · exact B1584579
  · exact B1584583
  · exact B1584587
  · exact B1584591
  · exact B1584595
  · exact B1584599
  · exact B1584603
  · exact B1584607
  · exact B1584611
  · exact B1584615
  · exact B1584619
  · exact B1584623
  · exact B1584627
  · exact B1584631
  · exact B1584635
  · exact B1584639
  · exact B1584643
  · exact B1584647
  · exact B1584651
  · exact B1584655
  · exact B1584659
  · exact B1584663
  · exact B1584667
  · exact B1584671
  · exact B1584675
  · exact B1584679
  · exact B1584683
  · exact B1584687
  · exact B1584691
  · exact B1584695
  · exact B1584699
  · exact B1584703
  · exact B1584707
  · exact B1584711
  · exact B1584715
  · exact B1584719
  · exact B1584723
  · exact B1584727
  · exact B1584731
  · exact B1584735
  · exact B1584739
  · exact B1584743
  · exact B1584747
  · exact B1584751
  · exact B1584755
  · exact B1584759
  · exact B1584763
  · exact B1584767
  · exact B1584771
  · exact B1584775
  · exact B1584779
  · exact B1584783
  · exact B1584787
  · exact B1584791
  · exact B1584795
  · exact B1584799
  · exact B1584803
  · exact B1584807
  · exact B1584811
  · exact B1584815
  · exact B1584819
  · exact B1584823
  · exact B1584827
  · exact B1584831
  · exact B1584835
  · exact B1584839
  · exact B1584843
  · exact B1584847
  · exact B1584851
  · exact B1584855
  · exact B1584859
  · exact B1584863
  · exact B1584867
  · exact B1584871
  · exact B1584875
  · exact B1584879
  · exact B1584883
  · exact B1584887
  · exact B1584891
  · exact B1584895
  · exact B1584899
  · exact B1584903
  · exact B1584907
  · exact B1584911
  · exact B1584915
  · exact B1584919
  · exact B1584923
  · exact B1584927
  · exact B1584931
  · exact B1584935
  · exact B1584939
  · exact B1584943
  · exact B1584947
  · exact B1584951
  · exact B1584955
  · exact B1584959
  · exact B1584963
  · exact B1584967
  · exact B1584971
  · exact B1584975
  · exact B1584979
  · exact B1584983
  · exact B1584987
  · exact B1584991
  · exact B1584995
  · exact B1584999
  · exact B1585003
  · exact B1585007
  · exact B1585011
  · exact B1585015
  · exact B1585019
  · exact B1585023
  · exact B1585027
  · exact B1585031
  · exact B1585035
  · exact B1585039
  · exact B1585043
  · exact B1585047
  · exact B1585051
  · exact B1585055
  · exact B1585059
  · exact B1585063
  · exact B1585067
  · exact B1585071
  · exact B1585075
  · exact B1585079
  · exact B1585083
  · exact B1585087
  · exact B1585091
  · exact B1585095
  · exact B1585099
  · exact B1585103
  · exact B1585107
  · exact B1585111
  · exact B1585115
  · exact B1585119
  · exact B1585123
  · exact B1585127
  · exact B1585131
  · exact B1585135
  · exact B1585139
  · exact B1585143
  · exact B1585147
  · exact B1585151
  · exact B1585155
  · exact B1585159
  · exact B1585163
  · exact B1585167
  · exact B1585171
  · exact B1585175
  · exact B1585179
  · exact B1585183
  · exact B1585187
  · exact B1585191
  · exact B1585195
  · exact B1585199
  · exact B1585203
  · exact B1585207
  · exact B1585211
  · exact B1585215
  · exact B1585219
  · exact B1585223
  · exact B1585227
  · exact B1585231
  · exact B1585235
  · exact B1585239
  · exact B1585243
  · exact B1585247
  · exact B1585251
  · exact B1585255
  · exact B1585259
  · exact B1585263
  · exact B1585267
  · exact B1585271
  · exact B1585275
  · exact B1585279
  · exact B1585283
  · exact B1585287
  · exact B1585291
  · exact B1585295
  · exact B1585299
  · exact B1585303
  · exact B1585307
  · exact B1585311
  · exact B1585315
  · exact B1585319
  · exact B1585323
  · exact B1585327
  · exact B1585331
  · exact B1585335
  · exact B1585339
  · exact B1585343
  · exact B1585347
  · exact B1585351
  · exact B1585355
  · exact B1585359
  · exact B1585363
  · exact B1585367
  · exact B1585371
  · exact B1585375
  · exact B1585379
  · exact B1585383
  · exact B1585387
  · exact B1585391
  · exact B1585395
  · exact B1585399
  · exact B1585403
  · exact B1585407
  · exact B1585411
  · exact B1585415
  · exact B1585419
  · exact B1585423
  · exact B1585427
  · exact B1585431
  · exact B1585435
  · exact B1585439
  · exact B1585443
  · exact B1585447
  · exact B1585451
  · exact B1585455
  · exact B1585459
  · exact B1585463
  · exact B1585467
  · exact B1585471
  · exact B1585475
  · exact B1585479
  · exact B1585483
  · exact B1585487

theorem solution (m : ℕ) (hlo : 1583990 ≤ m) (hhi : m ≤ 1585490) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 395997 ≤ j := by omega
    have hj2 : j ≤ 396371 := by omega
    have hb : Blo 1583990 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
