-- Prove2me | solution 1 for syracuse_descends_range_1309973_1311973
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:31.213634+00:00
-- url     : https://prove2.me/submissions/21caad92-7f2e-47d1-b879-d2ff79433e63

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


theorem B1966085 : Blo 1309973 1966085 := bbase (se 4 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 1966085 = 368641) (by norm_num)
theorem B1474573 : Blo 1309973 1474573 := bbase (se 3 (by rfl) ⟨276482, by rfl⟩ : syracuseStep 1474573 = 552965) (by norm_num)
theorem B2211853 : Blo 1309973 2211853 := bbase (se 3 (by rfl) ⟨414722, by rfl⟩ : syracuseStep 2211853 = 829445) (by norm_num)
theorem B1867789 : Blo 1309973 1867789 := bbase (se 3 (by rfl) ⟨350210, by rfl⟩ : syracuseStep 1867789 = 700421) (by norm_num)
theorem B1966109 : Blo 1309973 1966109 := bbase (se 3 (by rfl) ⟨368645, by rfl⟩ : syracuseStep 1966109 = 737291) (by norm_num)
theorem B1474609 : Blo 1309973 1474609 := bbase (se 2 (by rfl) ⟨552978, by rfl⟩ : syracuseStep 1474609 = 1105957) (by norm_num)
theorem B4423733 : Blo 1309973 4423733 := bbase (se 5 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 4423733 = 414725) (by norm_num)
theorem B2949173 : Blo 1309973 2949173 := bbase (se 5 (by rfl) ⟨138242, by rfl⟩ : syracuseStep 2949173 = 276485) (by norm_num)
theorem B1966133 : Blo 1309973 1966133 := bbase (se 5 (by rfl) ⟨92162, by rfl⟩ : syracuseStep 1966133 = 184325) (by norm_num)
theorem B1966157 : Blo 1309973 1966157 := bbase (se 3 (by rfl) ⟨368654, by rfl⟩ : syracuseStep 1966157 = 737309) (by norm_num)
theorem B1474645 : Blo 1309973 1474645 := bbase (se 8 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 1474645 = 17281) (by norm_num)
theorem B3317861 : Blo 1309973 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B2211941 : Blo 1309973 2211941 := bbase (se 4 (by rfl) ⟨207369, by rfl⟩ : syracuseStep 2211941 = 414739) (by norm_num)
theorem B1966181 : Blo 1309973 1966181 := bbase (se 4 (by rfl) ⟨184329, by rfl⟩ : syracuseStep 1966181 = 368659) (by norm_num)
theorem B4259957 : Blo 1309973 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B1474681 : Blo 1309973 1474681 := bbase (se 2 (by rfl) ⟨553005, by rfl⟩ : syracuseStep 1474681 = 1106011) (by norm_num)
theorem B2949245 : Blo 1309973 2949245 := bbase (se 3 (by rfl) ⟨552983, by rfl⟩ : syracuseStep 2949245 = 1105967) (by norm_num)
theorem B1966205 : Blo 1309973 1966205 := bbase (se 3 (by rfl) ⟨368663, by rfl⟩ : syracuseStep 1966205 = 737327) (by norm_num)
theorem B1966229 : Blo 1309973 1966229 := bbase (se 6 (by rfl) ⟨46083, by rfl⟩ : syracuseStep 1966229 = 92167) (by norm_num)
theorem B1474717 : Blo 1309973 1474717 := bbase (se 3 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 1474717 = 553019) (by norm_num)
theorem B2875565 : Blo 1309973 2875565 := bbase (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) (by norm_num)
theorem B1966253 : Blo 1309973 1966253 := bbase (se 3 (by rfl) ⟨368672, by rfl⟩ : syracuseStep 1966253 = 737345) (by norm_num)
theorem B1401013 : Blo 1309973 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1474753 : Blo 1309973 1474753 := bbase (se 2 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 1474753 = 1106065) (by norm_num)
theorem B2949317 : Blo 1309973 2949317 := bbase (se 4 (by rfl) ⟨276498, by rfl⟩ : syracuseStep 2949317 = 552997) (by norm_num)
theorem B1966277 : Blo 1309973 1966277 := bbase (se 4 (by rfl) ⟨184338, by rfl⟩ : syracuseStep 1966277 = 368677) (by norm_num)
theorem B1966301 : Blo 1309973 1966301 := bbase (se 3 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 1966301 = 737363) (by norm_num)
theorem B2212069 : Blo 1309973 2212069 := bbase (se 4 (by rfl) ⟨207381, by rfl⟩ : syracuseStep 2212069 = 414763) (by norm_num)
theorem B1474789 : Blo 1309973 1474789 := bbase (se 4 (by rfl) ⟨138261, by rfl⟩ : syracuseStep 1474789 = 276523) (by norm_num)
theorem B1966325 : Blo 1309973 1966325 := bbase (se 5 (by rfl) ⟨92171, by rfl⟩ : syracuseStep 1966325 = 184343) (by norm_num)
theorem B5603573 : Blo 1309973 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B1474825 : Blo 1309973 1474825 := bbase (se 2 (by rfl) ⟨553059, by rfl⟩ : syracuseStep 1474825 = 1106119) (by norm_num)
theorem B2949389 : Blo 1309973 2949389 := bbase (se 3 (by rfl) ⟨553010, by rfl⟩ : syracuseStep 2949389 = 1106021) (by norm_num)
theorem B1966349 : Blo 1309973 1966349 := bbase (se 3 (by rfl) ⟨368690, by rfl⟩ : syracuseStep 1966349 = 737381) (by norm_num)
theorem B14934293 : Blo 1309973 14934293 := bbase (se 6 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 14934293 = 700045) (by norm_num)
theorem B1966373 : Blo 1309973 1966373 := bbase (se 4 (by rfl) ⟨184347, by rfl⟩ : syracuseStep 1966373 = 368695) (by norm_num)
theorem B2801957 : Blo 1309973 2801957 := bbase (se 4 (by rfl) ⟨262683, by rfl⟩ : syracuseStep 2801957 = 525367) (by norm_num)
theorem B1474861 : Blo 1309973 1474861 := bbase (se 3 (by rfl) ⟨276536, by rfl⟩ : syracuseStep 1474861 = 553073) (by norm_num)
theorem B2212157 : Blo 1309973 2212157 := bbase (se 3 (by rfl) ⟨414779, by rfl⟩ : syracuseStep 2212157 = 829559) (by norm_num)
theorem B1966397 : Blo 1309973 1966397 := bbase (se 3 (by rfl) ⟨368699, by rfl⟩ : syracuseStep 1966397 = 737399) (by norm_num)
theorem B1474897 : Blo 1309973 1474897 := bbase (se 2 (by rfl) ⟨553086, by rfl⟩ : syracuseStep 1474897 = 1106173) (by norm_num)
theorem B2949461 : Blo 1309973 2949461 := bbase (se 10 (by rfl) ⟨4320, by rfl⟩ : syracuseStep 2949461 = 8641) (by norm_num)
theorem B1966421 : Blo 1309973 1966421 := bbase (se 10 (by rfl) ⟨2880, by rfl⟩ : syracuseStep 1966421 = 5761) (by norm_num)
theorem B1966445 : Blo 1309973 1966445 := bbase (se 3 (by rfl) ⟨368708, by rfl⟩ : syracuseStep 1966445 = 737417) (by norm_num)
theorem B1474933 : Blo 1309973 1474933 := bbase (se 5 (by rfl) ⟨69137, by rfl⟩ : syracuseStep 1474933 = 138275) (by norm_num)
theorem B1966469 : Blo 1309973 1966469 := bbase (se 4 (by rfl) ⟨184356, by rfl⟩ : syracuseStep 1966469 = 368713) (by norm_num)
theorem B1474969 : Blo 1309973 1474969 := bbase (se 2 (by rfl) ⟨553113, by rfl⟩ : syracuseStep 1474969 = 1106227) (by norm_num)
theorem B2949533 : Blo 1309973 2949533 := bbase (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) (by norm_num)
theorem B1966493 : Blo 1309973 1966493 := bbase (se 3 (by rfl) ⟨368717, by rfl⟩ : syracuseStep 1966493 = 737435) (by norm_num)
theorem B2523557 : Blo 1309973 2523557 := bbase (se 4 (by rfl) ⟨236583, by rfl⟩ : syracuseStep 2523557 = 473167) (by norm_num)
theorem B1966517 : Blo 1309973 1966517 := bbase (se 5 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 1966517 = 184361) (by norm_num)
theorem B3735989 : Blo 1309973 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B3318205 : Blo 1309973 3318205 := bbase (se 3 (by rfl) ⟨622163, by rfl⟩ : syracuseStep 3318205 = 1244327) (by norm_num)
theorem B2212285 : Blo 1309973 2212285 := bbase (se 3 (by rfl) ⟨414803, by rfl⟩ : syracuseStep 2212285 = 829607) (by norm_num)
theorem B1475005 : Blo 1309973 1475005 := bbase (se 3 (by rfl) ⟨276563, by rfl⟩ : syracuseStep 1475005 = 553127) (by norm_num)
theorem B1966541 : Blo 1309973 1966541 := bbase (se 3 (by rfl) ⟨368726, by rfl⟩ : syracuseStep 1966541 = 737453) (by norm_num)
theorem B8405461 : Blo 1309973 8405461 := bbase (se 7 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 8405461 = 197003) (by norm_num)
theorem B1475041 : Blo 1309973 1475041 := bbase (se 2 (by rfl) ⟨553140, by rfl⟩ : syracuseStep 1475041 = 1106281) (by norm_num)
theorem B6636005 : Blo 1309973 6636005 := bbase (se 4 (by rfl) ⟨622125, by rfl⟩ : syracuseStep 6636005 = 1244251) (by norm_num)
theorem B4424165 : Blo 1309973 4424165 := bbase (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) (by norm_num)
theorem B2949605 : Blo 1309973 2949605 := bbase (se 4 (by rfl) ⟨276525, by rfl⟩ : syracuseStep 2949605 = 553051) (by norm_num)
theorem B1966565 : Blo 1309973 1966565 := bbase (se 4 (by rfl) ⟨184365, by rfl⟩ : syracuseStep 1966565 = 368731) (by norm_num)
theorem B5603813 : Blo 1309973 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B1966589 : Blo 1309973 1966589 := bbase (se 3 (by rfl) ⟨368735, by rfl⟩ : syracuseStep 1966589 = 737471) (by norm_num)
theorem B1475077 : Blo 1309973 1475077 := bbase (se 4 (by rfl) ⟨138288, by rfl⟩ : syracuseStep 1475077 = 276577) (by norm_num)
theorem B2212373 : Blo 1309973 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B1966613 : Blo 1309973 1966613 := bbase (se 6 (by rfl) ⟨46092, by rfl⟩ : syracuseStep 1966613 = 92185) (by norm_num)
theorem B4481573 : Blo 1309973 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B1475113 : Blo 1309973 1475113 := bbase (se 2 (by rfl) ⟨553167, by rfl⟩ : syracuseStep 1475113 = 1106335) (by norm_num)
theorem B3318317 : Blo 1309973 3318317 := bbase (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) (by norm_num)
theorem B2949677 : Blo 1309973 2949677 := bbase (se 3 (by rfl) ⟨553064, by rfl⟩ : syracuseStep 2949677 = 1106129) (by norm_num)
theorem B1966637 : Blo 1309973 1966637 := bbase (se 3 (by rfl) ⟨368744, by rfl⟩ : syracuseStep 1966637 = 737489) (by norm_num)
theorem B1966661 : Blo 1309973 1966661 := bbase (se 4 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 1966661 = 368749) (by norm_num)
theorem B1475149 : Blo 1309973 1475149 := bbase (se 3 (by rfl) ⟨276590, by rfl⟩ : syracuseStep 1475149 = 553181) (by norm_num)
theorem B1966685 : Blo 1309973 1966685 := bbase (se 3 (by rfl) ⟨368753, by rfl⟩ : syracuseStep 1966685 = 737507) (by norm_num)
theorem B5595749 : Blo 1309973 5595749 := bbase (se 4 (by rfl) ⟨524601, by rfl⟩ : syracuseStep 5595749 = 1049203) (by norm_num)
theorem B1475185 : Blo 1309973 1475185 := bbase (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) (by norm_num)
theorem B2949749 : Blo 1309973 2949749 := bbase (se 5 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 2949749 = 276539) (by norm_num)
theorem B1966709 : Blo 1309973 1966709 := bbase (se 5 (by rfl) ⟨92189, by rfl⟩ : syracuseStep 1966709 = 184379) (by norm_num)
theorem B1966733 : Blo 1309973 1966733 := bbase (se 3 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 1966733 = 737525) (by norm_num)
theorem B2212501 : Blo 1309973 2212501 := bbase (se 6 (by rfl) ⟨51855, by rfl⟩ : syracuseStep 2212501 = 103711) (by norm_num)
theorem B1475221 : Blo 1309973 1475221 := bbase (se 6 (by rfl) ⟨34575, by rfl⟩ : syracuseStep 1475221 = 69151) (by norm_num)
theorem B1966757 : Blo 1309973 1966757 := bbase (se 4 (by rfl) ⟨184383, by rfl⟩ : syracuseStep 1966757 = 368767) (by norm_num)
theorem B1475257 : Blo 1309973 1475257 := bbase (se 2 (by rfl) ⟨553221, by rfl⟩ : syracuseStep 1475257 = 1106443) (by norm_num)
theorem B2949821 : Blo 1309973 2949821 := bbase (se 3 (by rfl) ⟨553091, by rfl⟩ : syracuseStep 2949821 = 1106183) (by norm_num)
theorem B1966781 : Blo 1309973 1966781 := bbase (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) (by norm_num)
theorem B1966805 : Blo 1309973 1966805 := bbase (se 7 (by rfl) ⟨23048, by rfl⟩ : syracuseStep 1966805 = 46097) (by norm_num)
theorem B1475293 : Blo 1309973 1475293 := bbase (se 3 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 1475293 = 553235) (by norm_num)
theorem B3318509 : Blo 1309973 3318509 := bbase (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) (by norm_num)
theorem B2212589 : Blo 1309973 2212589 := bbase (se 3 (by rfl) ⟨414860, by rfl⟩ : syracuseStep 2212589 = 829721) (by norm_num)
theorem B1966829 : Blo 1309973 1966829 := bbase (se 3 (by rfl) ⟨368780, by rfl⟩ : syracuseStep 1966829 = 737561) (by norm_num)
theorem B1475329 : Blo 1309973 1475329 := bbase (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) (by norm_num)
theorem B2949893 : Blo 1309973 2949893 := bbase (se 4 (by rfl) ⟨276552, by rfl⟩ : syracuseStep 2949893 = 553105) (by norm_num)
theorem B1966853 : Blo 1309973 1966853 := bbase (se 4 (by rfl) ⟨184392, by rfl⟩ : syracuseStep 1966853 = 368785) (by norm_num)
theorem B1966877 : Blo 1309973 1966877 := bbase (se 3 (by rfl) ⟨368789, by rfl⟩ : syracuseStep 1966877 = 737579) (by norm_num)
theorem B1475365 : Blo 1309973 1475365 := bbase (se 4 (by rfl) ⟨138315, by rfl⟩ : syracuseStep 1475365 = 276631) (by norm_num)
theorem B1966901 : Blo 1309973 1966901 := bbase (se 5 (by rfl) ⟨92198, by rfl⟩ : syracuseStep 1966901 = 184397) (by norm_num)
theorem B5317429 : Blo 1309973 5317429 := bbase (se 5 (by rfl) ⟨249254, by rfl⟩ : syracuseStep 5317429 = 498509) (by norm_num)
theorem B1475401 : Blo 1309973 1475401 := bbase (se 2 (by rfl) ⟨553275, by rfl⟩ : syracuseStep 1475401 = 1106551) (by norm_num)
theorem B2949965 : Blo 1309973 2949965 := bbase (se 3 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 2949965 = 1106237) (by norm_num)
theorem B1966925 : Blo 1309973 1966925 := bbase (se 3 (by rfl) ⟨368798, by rfl⟩ : syracuseStep 1966925 = 737597) (by norm_num)
theorem B1966949 : Blo 1309973 1966949 := bbase (se 4 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 1966949 = 368803) (by norm_num)
theorem B2212717 : Blo 1309973 2212717 := bbase (se 3 (by rfl) ⟨414884, by rfl⟩ : syracuseStep 2212717 = 829769) (by norm_num)
theorem B1475437 : Blo 1309973 1475437 := bbase (se 3 (by rfl) ⟨276644, by rfl⟩ : syracuseStep 1475437 = 553289) (by norm_num)
theorem B12944245 : Blo 1309973 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B1966973 : Blo 1309973 1966973 := bbase (se 3 (by rfl) ⟨368807, by rfl⟩ : syracuseStep 1966973 = 737615) (by norm_num)
theorem B1475473 : Blo 1309973 1475473 := bbase (se 2 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 1475473 = 1106605) (by norm_num)
theorem B4424597 : Blo 1309973 4424597 := bbase (se 6 (by rfl) ⟨103701, by rfl⟩ : syracuseStep 4424597 = 207403) (by norm_num)
theorem B2950037 : Blo 1309973 2950037 := bbase (se 6 (by rfl) ⟨69141, by rfl⟩ : syracuseStep 2950037 = 138283) (by norm_num)
theorem B1966997 : Blo 1309973 1966997 := bbase (se 6 (by rfl) ⟨46101, by rfl⟩ : syracuseStep 1966997 = 92203) (by norm_num)
theorem B1967021 : Blo 1309973 1967021 := bbase (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) (by norm_num)
theorem B1475509 : Blo 1309973 1475509 := bbase (se 5 (by rfl) ⟨69164, by rfl⟩ : syracuseStep 1475509 = 138329) (by norm_num)
theorem B2212805 : Blo 1309973 2212805 := bbase (se 4 (by rfl) ⟨207450, by rfl⟩ : syracuseStep 2212805 = 414901) (by norm_num)
theorem B1967045 : Blo 1309973 1967045 := bbase (se 4 (by rfl) ⟨184410, by rfl⟩ : syracuseStep 1967045 = 368821) (by norm_num)
theorem B1475545 : Blo 1309973 1475545 := bbase (se 2 (by rfl) ⟨553329, by rfl⟩ : syracuseStep 1475545 = 1106659) (by norm_num)
theorem B2950109 : Blo 1309973 2950109 := bbase (se 3 (by rfl) ⟨553145, by rfl⟩ : syracuseStep 2950109 = 1106291) (by norm_num)
theorem B1967069 : Blo 1309973 1967069 := bbase (se 3 (by rfl) ⟨368825, by rfl⟩ : syracuseStep 1967069 = 737651) (by norm_num)
theorem B1328113 : Blo 1309973 1328113 := bbase (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) (by norm_num)
theorem B1967093 : Blo 1309973 1967093 := bbase (se 5 (by rfl) ⟨92207, by rfl⟩ : syracuseStep 1967093 = 184415) (by norm_num)
theorem B1475581 : Blo 1309973 1475581 := bbase (se 3 (by rfl) ⟨276671, by rfl⟩ : syracuseStep 1475581 = 553343) (by norm_num)
theorem B1967117 : Blo 1309973 1967117 := bbase (se 3 (by rfl) ⟨368834, by rfl⟩ : syracuseStep 1967117 = 737669) (by norm_num)
theorem B1475617 : Blo 1309973 1475617 := bbase (se 2 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 1475617 = 1106713) (by norm_num)
theorem B2950181 : Blo 1309973 2950181 := bbase (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) (by norm_num)
theorem B1967141 : Blo 1309973 1967141 := bbase (se 4 (by rfl) ⟨184419, by rfl⟩ : syracuseStep 1967141 = 368839) (by norm_num)
theorem B1967165 : Blo 1309973 1967165 := bbase (se 3 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 1967165 = 737687) (by norm_num)
theorem B3318853 : Blo 1309973 3318853 := bbase (se 4 (by rfl) ⟨311142, by rfl⟩ : syracuseStep 3318853 = 622285) (by norm_num)
theorem B2212933 : Blo 1309973 2212933 := bbase (se 4 (by rfl) ⟨207462, by rfl⟩ : syracuseStep 2212933 = 414925) (by norm_num)
theorem B1475653 : Blo 1309973 1475653 := bbase (se 4 (by rfl) ⟨138342, by rfl⟩ : syracuseStep 1475653 = 276685) (by norm_num)
theorem B1967189 : Blo 1309973 1967189 := bbase (se 8 (by rfl) ⟨11526, by rfl⟩ : syracuseStep 1967189 = 23053) (by norm_num)
theorem B1475689 : Blo 1309973 1475689 := bbase (se 2 (by rfl) ⟨553383, by rfl⟩ : syracuseStep 1475689 = 1106767) (by norm_num)
theorem B2950253 : Blo 1309973 2950253 := bbase (se 3 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 2950253 = 1106345) (by norm_num)
theorem B1967213 : Blo 1309973 1967213 := bbase (se 3 (by rfl) ⟨368852, by rfl⟩ : syracuseStep 1967213 = 737705) (by norm_num)
theorem B1967237 : Blo 1309973 1967237 := bbase (se 4 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 1967237 = 368857) (by norm_num)
theorem B1475725 : Blo 1309973 1475725 := bbase (se 3 (by rfl) ⟨276698, by rfl⟩ : syracuseStep 1475725 = 553397) (by norm_num)
theorem B2213021 : Blo 1309973 2213021 := bbase (se 3 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 2213021 = 829883) (by norm_num)
theorem B1967261 : Blo 1309973 1967261 := bbase (se 3 (by rfl) ⟨368861, by rfl⟩ : syracuseStep 1967261 = 737723) (by norm_num)
theorem B1475761 : Blo 1309973 1475761 := bbase (se 2 (by rfl) ⟨553410, by rfl⟩ : syracuseStep 1475761 = 1106821) (by norm_num)
theorem B3318965 : Blo 1309973 3318965 := bbase (se 5 (by rfl) ⟨155576, by rfl⟩ : syracuseStep 3318965 = 311153) (by norm_num)
theorem B2950325 : Blo 1309973 2950325 := bbase (se 5 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 2950325 = 276593) (by norm_num)
theorem B1967285 : Blo 1309973 1967285 := bbase (se 5 (by rfl) ⟨92216, by rfl⟩ : syracuseStep 1967285 = 184433) (by norm_num)
theorem B1967309 : Blo 1309973 1967309 := bbase (se 3 (by rfl) ⟨368870, by rfl⟩ : syracuseStep 1967309 = 737741) (by norm_num)
theorem B27280597 : Blo 1309973 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B1475797 : Blo 1309973 1475797 := bbase (se 7 (by rfl) ⟨17294, by rfl⟩ : syracuseStep 1475797 = 34589) (by norm_num)
theorem B1967333 : Blo 1309973 1967333 := bbase (se 4 (by rfl) ⟨184437, by rfl⟩ : syracuseStep 1967333 = 368875) (by norm_num)
theorem B1475833 : Blo 1309973 1475833 := bbase (se 2 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 1475833 = 1106875) (by norm_num)
theorem B2950397 : Blo 1309973 2950397 := bbase (se 3 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 2950397 = 1106399) (by norm_num)
theorem B1967357 : Blo 1309973 1967357 := bbase (se 3 (by rfl) ⟨368879, by rfl⟩ : syracuseStep 1967357 = 737759) (by norm_num)
theorem B4973845 : Blo 1309973 4973845 := bbase (se 6 (by rfl) ⟨116574, by rfl⟩ : syracuseStep 4973845 = 233149) (by norm_num)
theorem B1967381 : Blo 1309973 1967381 := bbase (se 6 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 1967381 = 92221) (by norm_num)
theorem B2213149 : Blo 1309973 2213149 := bbase (se 3 (by rfl) ⟨414965, by rfl⟩ : syracuseStep 2213149 = 829931) (by norm_num)
theorem B1475869 : Blo 1309973 1475869 := bbase (se 3 (by rfl) ⟨276725, by rfl⟩ : syracuseStep 1475869 = 553451) (by norm_num)
theorem B1967405 : Blo 1309973 1967405 := bbase (se 3 (by rfl) ⟨368888, by rfl⟩ : syracuseStep 1967405 = 737777) (by norm_num)
theorem B1475905 : Blo 1309973 1475905 := bbase (se 2 (by rfl) ⟨553464, by rfl⟩ : syracuseStep 1475905 = 1106929) (by norm_num)
theorem B1574213 : Blo 1309973 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B4425029 : Blo 1309973 4425029 := bbase (se 4 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 4425029 = 829693) (by norm_num)
theorem B2950469 : Blo 1309973 2950469 := bbase (se 4 (by rfl) ⟨276606, by rfl⟩ : syracuseStep 2950469 = 553213) (by norm_num)
theorem B1967429 : Blo 1309973 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B21251413 : Blo 1309973 21251413 := bbase (se 12 (by rfl) ⟨7782, by rfl⟩ : syracuseStep 21251413 = 15565) (by norm_num)
theorem B7972181 : Blo 1309973 7972181 := bbase (se 12 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 7972181 = 5839) (by norm_num)
theorem B1967453 : Blo 1309973 1967453 := bbase (se 3 (by rfl) ⟨368897, by rfl⟩ : syracuseStep 1967453 = 737795) (by norm_num)
theorem B1475941 : Blo 1309973 1475941 := bbase (se 4 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 1475941 = 276739) (by norm_num)
theorem B2098541 : Blo 1309973 2098541 := bbase (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) (by norm_num)
theorem B3319157 : Blo 1309973 3319157 := bbase (se 5 (by rfl) ⟨155585, by rfl⟩ : syracuseStep 3319157 = 311171) (by norm_num)
theorem B2213237 : Blo 1309973 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B1967477 : Blo 1309973 1967477 := bbase (se 5 (by rfl) ⟨92225, by rfl⟩ : syracuseStep 1967477 = 184451) (by norm_num)
theorem B2950541 : Blo 1309973 2950541 := bbase (se 3 (by rfl) ⟨553226, by rfl⟩ : syracuseStep 2950541 = 1106453) (by norm_num)
theorem B1967501 : Blo 1309973 1967501 := bbase (se 3 (by rfl) ⟨368906, by rfl⟩ : syracuseStep 1967501 = 737813) (by norm_num)
theorem B1967525 : Blo 1309973 1967525 := bbase (se 4 (by rfl) ⟨184455, by rfl⟩ : syracuseStep 1967525 = 368911) (by norm_num)
theorem B1574329 : Blo 1309973 1574329 := bbase (se 2 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 1574329 = 1180747) (by norm_num)
theorem B1967549 : Blo 1309973 1967549 := bbase (se 3 (by rfl) ⟨368915, by rfl⟩ : syracuseStep 1967549 = 737831) (by norm_num)
theorem B2950613 : Blo 1309973 2950613 := bbase (se 7 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 2950613 = 69155) (by norm_num)
theorem B1967573 : Blo 1309973 1967573 := bbase (se 7 (by rfl) ⟨23057, by rfl⟩ : syracuseStep 1967573 = 46115) (by norm_num)
theorem B1705433 : Blo 1309973 1705433 := bbase (se 2 (by rfl) ⟨639537, by rfl⟩ : syracuseStep 1705433 = 1279075) (by norm_num)
theorem B1967597 : Blo 1309973 1967597 := bbase (se 3 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 1967597 = 737849) (by norm_num)
theorem B2213365 : Blo 1309973 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B1967621 : Blo 1309973 1967621 := bbase (se 4 (by rfl) ⟨184464, by rfl⟩ : syracuseStep 1967621 = 368929) (by norm_num)
theorem B2950685 : Blo 1309973 2950685 := bbase (se 3 (by rfl) ⟨553253, by rfl⟩ : syracuseStep 2950685 = 1106507) (by norm_num)
theorem B1967645 : Blo 1309973 1967645 := bbase (se 3 (by rfl) ⟨368933, by rfl⟩ : syracuseStep 1967645 = 737867) (by norm_num)
theorem B6727205 : Blo 1309973 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B1967669 : Blo 1309973 1967669 := bbase (se 5 (by rfl) ⟨92234, by rfl⟩ : syracuseStep 1967669 = 184469) (by norm_num)
theorem B4974149 : Blo 1309973 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B6301253 : Blo 1309973 6301253 := bbase (se 4 (by rfl) ⟨590742, by rfl⟩ : syracuseStep 6301253 = 1181485) (by norm_num)
theorem B2213453 : Blo 1309973 2213453 := bbase (se 3 (by rfl) ⟨415022, by rfl⟩ : syracuseStep 2213453 = 830045) (by norm_num)
theorem B1967693 : Blo 1309973 1967693 := bbase (se 3 (by rfl) ⟨368942, by rfl⟩ : syracuseStep 1967693 = 737885) (by norm_num)
theorem B2950757 : Blo 1309973 2950757 := bbase (se 4 (by rfl) ⟨276633, by rfl⟩ : syracuseStep 2950757 = 553267) (by norm_num)
theorem B1967717 : Blo 1309973 1967717 := bbase (se 4 (by rfl) ⟨184473, by rfl⟩ : syracuseStep 1967717 = 368947) (by norm_num)
theorem B9455221 : Blo 1309973 9455221 := bbase (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) (by norm_num)
theorem B1574525 : Blo 1309973 1574525 := bbase (se 3 (by rfl) ⟨295223, by rfl⟩ : syracuseStep 1574525 = 590447) (by norm_num)
theorem B1328765 : Blo 1309973 1328765 := bbase (se 3 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 1328765 = 498287) (by norm_num)
theorem B1967741 : Blo 1309973 1967741 := bbase (se 3 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 1967741 = 737903) (by norm_num)
theorem B5113477 : Blo 1309973 5113477 := bbase (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) (by norm_num)
theorem B2991757 : Blo 1309973 2991757 := bbase (se 3 (by rfl) ⟨560954, by rfl⟩ : syracuseStep 2991757 = 1121909) (by norm_num)
theorem B2360981 : Blo 1309973 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B1967765 : Blo 1309973 1967765 := bbase (se 6 (by rfl) ⟨46119, by rfl⟩ : syracuseStep 1967765 = 92239) (by norm_num)
theorem B2950829 : Blo 1309973 2950829 := bbase (se 3 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 2950829 = 1106561) (by norm_num)
theorem B1967789 : Blo 1309973 1967789 := bbase (se 3 (by rfl) ⟨368960, by rfl⟩ : syracuseStep 1967789 = 737921) (by norm_num)
theorem B6727349 : Blo 1309973 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B1967813 : Blo 1309973 1967813 := bbase (se 4 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 1967813 = 368965) (by norm_num)
theorem B3319501 : Blo 1309973 3319501 := bbase (se 3 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 3319501 = 1244813) (by norm_num)
theorem B2213581 : Blo 1309973 2213581 := bbase (se 3 (by rfl) ⟨415046, by rfl⟩ : syracuseStep 2213581 = 830093) (by norm_num)
theorem B1967837 : Blo 1309973 1967837 := bbase (se 3 (by rfl) ⟨368969, by rfl⟩ : syracuseStep 1967837 = 737939) (by norm_num)
theorem B2655973 : Blo 1309973 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B4548325 : Blo 1309973 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B6637301 : Blo 1309973 6637301 := bbase (se 5 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 6637301 = 622247) (by norm_num)
theorem B4425461 : Blo 1309973 4425461 := bbase (se 5 (by rfl) ⟨207443, by rfl⟩ : syracuseStep 4425461 = 414887) (by norm_num)
theorem B2950901 : Blo 1309973 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B1967861 : Blo 1309973 1967861 := bbase (se 5 (by rfl) ⟨92243, by rfl⟩ : syracuseStep 1967861 = 184487) (by norm_num)
theorem B1681165 : Blo 1309973 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B1967885 : Blo 1309973 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B2361125 : Blo 1309973 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2213669 : Blo 1309973 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B1967909 : Blo 1309973 1967909 := bbase (se 4 (by rfl) ⟨184491, by rfl⟩ : syracuseStep 1967909 = 368983) (by norm_num)
theorem B3319613 : Blo 1309973 3319613 := bbase (se 3 (by rfl) ⟨622427, by rfl⟩ : syracuseStep 3319613 = 1244855) (by norm_num)
theorem B2950973 : Blo 1309973 2950973 := bbase (se 3 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 2950973 = 1106615) (by norm_num)
theorem B1967933 : Blo 1309973 1967933 := bbase (se 3 (by rfl) ⟨368987, by rfl⟩ : syracuseStep 1967933 = 737975) (by norm_num)
theorem B3147589 : Blo 1309973 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B1967957 : Blo 1309973 1967957 := bbase (se 9 (by rfl) ⟨5765, by rfl⟩ : syracuseStep 1967957 = 11531) (by norm_num)
theorem B4786037 : Blo 1309973 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B2951045 : Blo 1309973 2951045 := bbase (se 4 (by rfl) ⟨276660, by rfl⟩ : syracuseStep 2951045 = 553321) (by norm_num)
theorem B2213797 : Blo 1309973 2213797 := bbase (se 4 (by rfl) ⟨207543, by rfl⟩ : syracuseStep 2213797 = 415087) (by norm_num)
theorem B2951117 : Blo 1309973 2951117 := bbase (se 3 (by rfl) ⟨553334, by rfl⟩ : syracuseStep 2951117 = 1106669) (by norm_num)
theorem B3319805 : Blo 1309973 3319805 := bbase (se 3 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 3319805 = 1244927) (by norm_num)
theorem B2213885 : Blo 1309973 2213885 := bbase (se 3 (by rfl) ⟨415103, by rfl⟩ : syracuseStep 2213885 = 830207) (by norm_num)
theorem B2099213 : Blo 1309973 2099213 := bbase (se 3 (by rfl) ⟨393602, by rfl⟩ : syracuseStep 2099213 = 787205) (by norm_num)
theorem B2951189 : Blo 1309973 2951189 := bbase (se 6 (by rfl) ⟨69168, by rfl⟩ : syracuseStep 2951189 = 138337) (by norm_num)
theorem B2951261 : Blo 1309973 2951261 := bbase (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) (by norm_num)
theorem B2394245 : Blo 1309973 2394245 := bbase (se 4 (by rfl) ⟨224460, by rfl⟩ : syracuseStep 2394245 = 448921) (by norm_num)
theorem B1575073 : Blo 1309973 1575073 := bbase (se 2 (by rfl) ⟨590652, by rfl⟩ : syracuseStep 1575073 = 1181305) (by norm_num)
theorem B4425893 : Blo 1309973 4425893 := bbase (se 4 (by rfl) ⟨414927, by rfl⟩ : syracuseStep 4425893 = 829855) (by norm_num)
theorem B2951333 : Blo 1309973 2951333 := bbase (se 4 (by rfl) ⟨276687, by rfl⟩ : syracuseStep 2951333 = 553375) (by norm_num)
theorem B2951405 : Blo 1309973 2951405 := bbase (se 3 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 2951405 = 1106777) (by norm_num)
theorem B22399253 : Blo 1309973 22399253 := bbase (se 6 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 22399253 = 1049965) (by norm_num)
theorem B1575217 : Blo 1309973 1575217 := bbase (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) (by norm_num)
theorem B2951477 : Blo 1309973 2951477 := bbase (se 5 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 2951477 = 276701) (by norm_num)
theorem B1681729 : Blo 1309973 1681729 := bbase (se 2 (by rfl) ⟨630648, by rfl⟩ : syracuseStep 1681729 = 1261297) (by norm_num)
theorem B5597525 : Blo 1309973 5597525 := bbase (se 10 (by rfl) ⟨8199, by rfl⟩ : syracuseStep 5597525 = 16399) (by norm_num)
theorem B3320149 : Blo 1309973 3320149 := bbase (se 10 (by rfl) ⟨4863, by rfl⟩ : syracuseStep 3320149 = 9727) (by norm_num)
theorem B2951549 : Blo 1309973 2951549 := bbase (se 3 (by rfl) ⟨553415, by rfl⟩ : syracuseStep 2951549 = 1106831) (by norm_num)
theorem B3320261 : Blo 1309973 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B2951621 : Blo 1309973 2951621 := bbase (se 4 (by rfl) ⟨276714, by rfl⟩ : syracuseStep 2951621 = 553429) (by norm_num)
theorem B1329625 : Blo 1309973 1329625 := bbase (se 2 (by rfl) ⟨498609, by rfl⟩ : syracuseStep 1329625 = 997219) (by norm_num)
theorem B2361845 : Blo 1309973 2361845 := bbase (se 5 (by rfl) ⟨110711, by rfl⟩ : syracuseStep 2361845 = 221423) (by norm_num)
theorem B3148301 : Blo 1309973 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B2099725 : Blo 1309973 2099725 := bbase (se 3 (by rfl) ⟨393698, by rfl⟩ : syracuseStep 2099725 = 787397) (by norm_num)
theorem B2951693 : Blo 1309973 2951693 := bbase (se 3 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 2951693 = 1106885) (by norm_num)
theorem B4426325 : Blo 1309973 4426325 := bbase (se 8 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 4426325 = 51871) (by norm_num)
theorem B2951765 : Blo 1309973 2951765 := bbase (se 8 (by rfl) ⟨17295, by rfl⟩ : syracuseStep 2951765 = 34591) (by norm_num)
theorem B3320453 : Blo 1309973 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B2951837 : Blo 1309973 2951837 := bbase (se 3 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 2951837 = 1106939) (by norm_num)
theorem B1400825 : Blo 1309973 1400825 := bbase (se 2 (by rfl) ⟨525309, by rfl⟩ : syracuseStep 1400825 = 1050619) (by norm_num)
theorem B2951909 : Blo 1309973 2951909 := bbase (se 4 (by rfl) ⟨276741, by rfl⟩ : syracuseStep 2951909 = 553483) (by norm_num)
theorem B15944597 : Blo 1309973 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B2100181 : Blo 1309973 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B3320797 : Blo 1309973 3320797 := bbase (se 3 (by rfl) ⟨622649, by rfl⟩ : syracuseStep 3320797 = 1245299) (by norm_num)
theorem B4197349 : Blo 1309973 4197349 := bbase (se 4 (by rfl) ⟨393501, by rfl⟩ : syracuseStep 4197349 = 787003) (by norm_num)
theorem B6638597 : Blo 1309973 6638597 := bbase (se 4 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 6638597 = 1244737) (by norm_num)
theorem B4426757 : Blo 1309973 4426757 := bbase (se 4 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 4426757 = 830017) (by norm_num)
theorem B14756885 : Blo 1309973 14756885 := bbase (se 6 (by rfl) ⟨345864, by rfl⟩ : syracuseStep 14756885 = 691729) (by norm_num)
theorem B3320909 : Blo 1309973 3320909 := bbase (se 3 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 3320909 = 1245341) (by norm_num)
theorem B1993877 : Blo 1309973 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B1658009 : Blo 1309973 1658009 := bbase (se 2 (by rfl) ⟨621753, by rfl⟩ : syracuseStep 1658009 = 1243507) (by norm_num)
theorem B3148973 : Blo 1309973 3148973 := bbase (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) (by norm_num)
theorem B1658065 : Blo 1309973 1658065 := bbase (se 2 (by rfl) ⟨621774, by rfl⟩ : syracuseStep 1658065 = 1243549) (by norm_num)
theorem B1658161 : Blo 1309973 1658161 := bbase (se 2 (by rfl) ⟨621810, by rfl⟩ : syracuseStep 1658161 = 1243621) (by norm_num)
theorem B2657693 : Blo 1309973 2657693 := bbase (se 3 (by rfl) ⟨498317, by rfl⟩ : syracuseStep 2657693 = 996635) (by norm_num)
theorem B4427189 : Blo 1309973 4427189 := bbase (se 5 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 4427189 = 415049) (by norm_num)
theorem B1658333 : Blo 1309973 1658333 := bbase (se 3 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 1658333 = 621875) (by norm_num)
theorem B1658389 : Blo 1309973 1658389 := bbase (se 6 (by rfl) ⟨38868, by rfl⟩ : syracuseStep 1658389 = 77737) (by norm_num)
theorem B1658485 : Blo 1309973 1658485 := bbase (se 5 (by rfl) ⟨77741, by rfl⟩ : syracuseStep 1658485 = 155483) (by norm_num)
theorem B2100853 : Blo 1309973 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B4976261 : Blo 1309973 4976261 := bbase (se 4 (by rfl) ⟨466524, by rfl⟩ : syracuseStep 4976261 = 933049) (by norm_num)
theorem B1494661 : Blo 1309973 1494661 := bbase (se 4 (by rfl) ⟨140124, by rfl⟩ : syracuseStep 1494661 = 280249) (by norm_num)
theorem B1658657 : Blo 1309973 1658657 := bbase (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) (by norm_num)
theorem B3731285 : Blo 1309973 3731285 := bbase (se 9 (by rfl) ⟨10931, by rfl⟩ : syracuseStep 3731285 = 21863) (by norm_num)
theorem B1658713 : Blo 1309973 1658713 := bbase (se 2 (by rfl) ⟨622017, by rfl⟩ : syracuseStep 1658713 = 1244035) (by norm_num)
theorem B4427621 : Blo 1309973 4427621 := bbase (se 4 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 4427621 = 830179) (by norm_num)
theorem B3542933 : Blo 1309973 3542933 := bbase (se 6 (by rfl) ⟨83037, by rfl⟩ : syracuseStep 3542933 = 166075) (by norm_num)
theorem B2658197 : Blo 1309973 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B4976549 : Blo 1309973 4976549 := bbase (se 4 (by rfl) ⟨466551, by rfl⟩ : syracuseStep 4976549 = 933103) (by norm_num)
theorem B1658809 : Blo 1309973 1658809 := bbase (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) (by norm_num)
theorem B5976085 : Blo 1309973 5976085 := bbase (se 6 (by rfl) ⟨140064, by rfl⟩ : syracuseStep 5976085 = 280129) (by norm_num)
theorem B18903061 : Blo 1309973 18903061 := bbase (se 6 (by rfl) ⟨443040, by rfl⟩ : syracuseStep 18903061 = 886081) (by norm_num)
theorem B2101277 : Blo 1309973 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B1617961 : Blo 1309973 1617961 := bbase (se 2 (by rfl) ⟨606735, by rfl⟩ : syracuseStep 1617961 = 1213471) (by norm_num)
theorem B5673029 : Blo 1309973 5673029 := bbase (se 4 (by rfl) ⟨531846, by rfl⟩ : syracuseStep 5673029 = 1063693) (by norm_num)
theorem B1658981 : Blo 1309973 1658981 := bbase (se 4 (by rfl) ⟨155529, by rfl⟩ : syracuseStep 1658981 = 311059) (by norm_num)
theorem B4198517 : Blo 1309973 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B1659037 : Blo 1309973 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B1659133 : Blo 1309973 1659133 := bbase (se 3 (by rfl) ⟨311087, by rfl⟩ : syracuseStep 1659133 = 622175) (by norm_num)
theorem B9957653 : Blo 1309973 9957653 := bbase (se 6 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 9957653 = 466765) (by norm_num)
theorem B6639893 : Blo 1309973 6639893 := bbase (se 6 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 6639893 = 311245) (by norm_num)
theorem B3543365 : Blo 1309973 3543365 := bbase (se 4 (by rfl) ⟨332190, by rfl⟩ : syracuseStep 3543365 = 664381) (by norm_num)
theorem B1659305 : Blo 1309973 1659305 := bbase (se 2 (by rfl) ⟨622239, by rfl⟩ : syracuseStep 1659305 = 1244479) (by norm_num)
theorem B1438133 : Blo 1309973 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B2658757 : Blo 1309973 2658757 := bbase (se 4 (by rfl) ⟨249258, by rfl⟩ : syracuseStep 2658757 = 498517) (by norm_num)
theorem B1659361 : Blo 1309973 1659361 := bbase (se 2 (by rfl) ⟨622260, by rfl⟩ : syracuseStep 1659361 = 1244521) (by norm_num)
theorem B3731957 : Blo 1309973 3731957 := bbase (se 5 (by rfl) ⟨174935, by rfl⟩ : syracuseStep 3731957 = 349871) (by norm_num)
theorem B1659457 : Blo 1309973 1659457 := bbase (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) (by norm_num)
theorem B2798165 : Blo 1309973 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B3986005 : Blo 1309973 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B6632117 : Blo 1309973 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B9949877 : Blo 1309973 9949877 := bbase (se 5 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 9949877 = 932801) (by norm_num)
theorem B7090901 : Blo 1309973 7090901 := bbase (se 7 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 7090901 = 166193) (by norm_num)
theorem B1659629 : Blo 1309973 1659629 := bbase (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) (by norm_num)
theorem B2487037 : Blo 1309973 2487037 := bbase (se 3 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 2487037 = 932639) (by norm_num)
theorem B1659685 : Blo 1309973 1659685 := bbase (se 4 (by rfl) ⟨155595, by rfl⟩ : syracuseStep 1659685 = 311191) (by norm_num)
theorem B8967029 : Blo 1309973 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B1659781 : Blo 1309973 1659781 := bbase (se 4 (by rfl) ⟨155604, by rfl⟩ : syracuseStep 1659781 = 311209) (by norm_num)
theorem B2487181 : Blo 1309973 2487181 := bbase (se 3 (by rfl) ⟨466346, by rfl⟩ : syracuseStep 2487181 = 932693) (by norm_num)
theorem B3150733 : Blo 1309973 3150733 := bbase (se 3 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 3150733 = 1181525) (by norm_num)
theorem B3732389 : Blo 1309973 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B2487341 : Blo 1309973 2487341 := bbase (se 3 (by rfl) ⟨466376, by rfl⟩ : syracuseStep 2487341 = 932753) (by norm_num)
theorem B1659953 : Blo 1309973 1659953 := bbase (se 2 (by rfl) ⟨622482, by rfl⟩ : syracuseStep 1659953 = 1244965) (by norm_num)
theorem B4977733 : Blo 1309973 4977733 := bbase (se 4 (by rfl) ⟨466662, by rfl⟩ : syracuseStep 4977733 = 933325) (by norm_num)
theorem B12604501 : Blo 1309973 12604501 := bbase (se 8 (by rfl) ⟨73854, by rfl⟩ : syracuseStep 12604501 = 147709) (by norm_num)
theorem B1660009 : Blo 1309973 1660009 := bbase (se 2 (by rfl) ⟨622503, by rfl⟩ : syracuseStep 1660009 = 1245007) (by norm_num)
theorem B2126965 : Blo 1309973 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B2659493 : Blo 1309973 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B2487485 : Blo 1309973 2487485 := bbase (se 3 (by rfl) ⟨466403, by rfl⟩ : syracuseStep 2487485 = 932807) (by norm_num)
theorem B1660105 : Blo 1309973 1660105 := bbase (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) (by norm_num)
theorem B6296869 : Blo 1309973 6296869 := bbase (se 4 (by rfl) ⟨590331, by rfl⟩ : syracuseStep 6296869 = 1180663) (by norm_num)
theorem B4978037 : Blo 1309973 4978037 := bbase (se 5 (by rfl) ⟨233345, by rfl⟩ : syracuseStep 4978037 = 466691) (by norm_num)
theorem B1660277 : Blo 1309973 1660277 := bbase (se 5 (by rfl) ⟨77825, by rfl⟩ : syracuseStep 1660277 = 155651) (by norm_num)
theorem B3691925 : Blo 1309973 3691925 := bbase (se 6 (by rfl) ⟨86529, by rfl⟩ : syracuseStep 3691925 = 173059) (by norm_num)
theorem B1660333 : Blo 1309973 1660333 := bbase (se 3 (by rfl) ⟨311312, by rfl⟩ : syracuseStep 1660333 = 622625) (by norm_num)
theorem B7468469 : Blo 1309973 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B2799053 : Blo 1309973 2799053 := bbase (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) (by norm_num)
theorem B2487773 : Blo 1309973 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B3151349 : Blo 1309973 3151349 := bbase (se 5 (by rfl) ⟨147719, by rfl⟩ : syracuseStep 3151349 = 295439) (by norm_num)
theorem B1660429 : Blo 1309973 1660429 := bbase (se 3 (by rfl) ⟨311330, by rfl⟩ : syracuseStep 1660429 = 622661) (by norm_num)
theorem B6641189 : Blo 1309973 6641189 := bbase (se 4 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 6641189 = 1245223) (by norm_num)
theorem B2799173 : Blo 1309973 2799173 := bbase (se 4 (by rfl) ⟨262422, by rfl⟩ : syracuseStep 2799173 = 524845) (by norm_num)
theorem B2487925 : Blo 1309973 2487925 := bbase (se 5 (by rfl) ⟨116621, by rfl⟩ : syracuseStep 2487925 = 233243) (by norm_num)
theorem B3733141 : Blo 1309973 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B1865477 : Blo 1309973 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B3987317 : Blo 1309973 3987317 := bbase (se 5 (by rfl) ⟨186905, by rfl⟩ : syracuseStep 3987317 = 373811) (by norm_num)
theorem B2488229 : Blo 1309973 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B4200373 : Blo 1309973 4200373 := bbase (se 5 (by rfl) ⟨196892, by rfl⟩ : syracuseStep 4200373 = 393785) (by norm_num)
theorem B4421573 : Blo 1309973 4421573 := bbase (se 4 (by rfl) ⟨414522, by rfl⟩ : syracuseStep 4421573 = 829045) (by norm_num)
theorem B6633413 : Blo 1309973 6633413 := bbase (se 4 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 6633413 = 1243765) (by norm_num)
theorem B3545093 : Blo 1309973 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B2799805 : Blo 1309973 2799805 := bbase (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) (by norm_num)
theorem B3315917 : Blo 1309973 3315917 := bbase (se 3 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 3315917 = 1243469) (by norm_num)
theorem B3152117 : Blo 1309973 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B3152125 : Blo 1309973 3152125 := bbase (se 3 (by rfl) ⟨591023, by rfl⟩ : syracuseStep 3152125 = 1182047) (by norm_num)
theorem B2947445 : Blo 1309973 2947445 := bbase (se 5 (by rfl) ⟨138161, by rfl⟩ : syracuseStep 2947445 = 276323) (by norm_num)
theorem B4422005 : Blo 1309973 4422005 := bbase (se 5 (by rfl) ⟨207281, by rfl⟩ : syracuseStep 4422005 = 414563) (by norm_num)
theorem B2128285 : Blo 1309973 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B2947517 : Blo 1309973 2947517 := bbase (se 3 (by rfl) ⟨552659, by rfl⟩ : syracuseStep 2947517 = 1105319) (by norm_num)
theorem B1399253 : Blo 1309973 1399253 := bbase (se 7 (by rfl) ⟨16397, by rfl⟩ : syracuseStep 1399253 = 32795) (by norm_num)
theorem B2947589 : Blo 1309973 2947589 := bbase (se 4 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 2947589 = 552673) (by norm_num)
theorem B5601797 : Blo 1309973 5601797 := bbase (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) (by norm_num)
theorem B1399313 : Blo 1309973 1399313 := bbase (se 2 (by rfl) ⟨524742, by rfl⟩ : syracuseStep 1399313 = 1049485) (by norm_num)
theorem B3316261 : Blo 1309973 3316261 := bbase (se 4 (by rfl) ⟨310899, by rfl⟩ : syracuseStep 3316261 = 621799) (by norm_num)
theorem B2947661 : Blo 1309973 2947661 := bbase (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) (by norm_num)
theorem B1399441 : Blo 1309973 1399441 := bbase (se 2 (by rfl) ⟨524790, by rfl⟩ : syracuseStep 1399441 = 1049581) (by norm_num)
theorem B2947733 : Blo 1309973 2947733 := bbase (se 6 (by rfl) ⟨69087, by rfl⟩ : syracuseStep 2947733 = 138175) (by norm_num)
theorem B3316373 : Blo 1309973 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B2488981 : Blo 1309973 2488981 := bbase (se 6 (by rfl) ⟨58335, by rfl⟩ : syracuseStep 2488981 = 116671) (by norm_num)
theorem B7977653 : Blo 1309973 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B2947805 : Blo 1309973 2947805 := bbase (se 3 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 2947805 = 1105427) (by norm_num)
theorem B2947877 : Blo 1309973 2947877 := bbase (se 4 (by rfl) ⟨276363, by rfl⟩ : syracuseStep 2947877 = 552727) (by norm_num)
theorem B4422437 : Blo 1309973 4422437 := bbase (se 4 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 4422437 = 829207) (by norm_num)
theorem B2489125 : Blo 1309973 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B2210645 : Blo 1309973 2210645 := bbase (se 9 (by rfl) ⟨6476, by rfl⟩ : syracuseStep 2210645 = 12953) (by norm_num)
theorem B3316565 : Blo 1309973 3316565 := bbase (se 9 (by rfl) ⟨9716, by rfl⟩ : syracuseStep 3316565 = 19433) (by norm_num)
theorem B2947949 : Blo 1309973 2947949 := bbase (se 3 (by rfl) ⟨552740, by rfl⟩ : syracuseStep 2947949 = 1105481) (by norm_num)
theorem B1964981 : Blo 1309973 1964981 := bbase (se 5 (by rfl) ⟨92108, by rfl⟩ : syracuseStep 1964981 = 184217) (by norm_num)
theorem B2948021 : Blo 1309973 2948021 := bbase (se 5 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 2948021 = 276377) (by norm_num)
theorem B2489285 : Blo 1309973 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B1965005 : Blo 1309973 1965005 := bbase (se 3 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 1965005 = 736877) (by norm_num)
theorem B2210773 : Blo 1309973 2210773 := bbase (se 7 (by rfl) ⟨25907, by rfl⟩ : syracuseStep 2210773 = 51815) (by norm_num)
theorem B1965029 : Blo 1309973 1965029 := bbase (se 4 (by rfl) ⟨184221, by rfl⟩ : syracuseStep 1965029 = 368443) (by norm_num)
theorem B1965053 : Blo 1309973 1965053 := bbase (se 3 (by rfl) ⟨368447, by rfl⟩ : syracuseStep 1965053 = 736895) (by norm_num)
theorem B2948093 : Blo 1309973 2948093 := bbase (se 3 (by rfl) ⟨552767, by rfl⟩ : syracuseStep 2948093 = 1105535) (by norm_num)
theorem B1965077 : Blo 1309973 1965077 := bbase (se 6 (by rfl) ⟨46056, by rfl⟩ : syracuseStep 1965077 = 92113) (by norm_num)
theorem B3890197 : Blo 1309973 3890197 := bbase (se 6 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 3890197 = 182353) (by norm_num)
theorem B1965101 : Blo 1309973 1965101 := bbase (se 3 (by rfl) ⟨368456, by rfl⟩ : syracuseStep 1965101 = 736913) (by norm_num)
theorem B2210861 : Blo 1309973 2210861 := bbase (se 3 (by rfl) ⟨414536, by rfl⟩ : syracuseStep 2210861 = 829073) (by norm_num)
theorem B2800693 : Blo 1309973 2800693 := bbase (se 5 (by rfl) ⟨131282, by rfl⟩ : syracuseStep 2800693 = 262565) (by norm_num)
theorem B1965125 : Blo 1309973 1965125 := bbase (se 4 (by rfl) ⟨184230, by rfl⟩ : syracuseStep 1965125 = 368461) (by norm_num)
theorem B2948165 : Blo 1309973 2948165 := bbase (se 4 (by rfl) ⟨276390, by rfl⟩ : syracuseStep 2948165 = 552781) (by norm_num)
theorem B1399885 : Blo 1309973 1399885 := bbase (se 3 (by rfl) ⟨262478, by rfl⟩ : syracuseStep 1399885 = 524957) (by norm_num)
theorem B86170709 : Blo 1309973 86170709 := bbase (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) (by norm_num)
theorem B2489429 : Blo 1309973 2489429 := bbase (se 8 (by rfl) ⟨14586, by rfl⟩ : syracuseStep 2489429 = 29173) (by norm_num)
theorem B1965149 : Blo 1309973 1965149 := bbase (se 3 (by rfl) ⟨368465, by rfl⟩ : syracuseStep 1965149 = 736931) (by norm_num)
theorem B1965173 : Blo 1309973 1965173 := bbase (se 5 (by rfl) ⟨92117, by rfl⟩ : syracuseStep 1965173 = 184235) (by norm_num)
theorem B1965197 : Blo 1309973 1965197 := bbase (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) (by norm_num)
theorem B2948237 : Blo 1309973 2948237 := bbase (se 3 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 2948237 = 1105589) (by norm_num)
theorem B1866901 : Blo 1309973 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B1965221 : Blo 1309973 1965221 := bbase (se 4 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 1965221 = 368479) (by norm_num)
theorem B2210989 : Blo 1309973 2210989 := bbase (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) (by norm_num)
theorem B3316909 : Blo 1309973 3316909 := bbase (se 3 (by rfl) ⟨621920, by rfl⟩ : syracuseStep 3316909 = 1243841) (by norm_num)
theorem B2800813 : Blo 1309973 2800813 := bbase (se 3 (by rfl) ⟨525152, by rfl⟩ : syracuseStep 2800813 = 1050305) (by norm_num)
theorem B1965245 : Blo 1309973 1965245 := bbase (se 3 (by rfl) ⟨368483, by rfl⟩ : syracuseStep 1965245 = 736967) (by norm_num)
theorem B1400005 : Blo 1309973 1400005 := bbase (se 4 (by rfl) ⟨131250, by rfl⟩ : syracuseStep 1400005 = 262501) (by norm_num)
theorem B1473745 : Blo 1309973 1473745 := bbase (se 2 (by rfl) ⟨552654, by rfl⟩ : syracuseStep 1473745 = 1105309) (by norm_num)
theorem B1965269 : Blo 1309973 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B2948309 : Blo 1309973 2948309 := bbase (se 7 (by rfl) ⟨34550, by rfl⟩ : syracuseStep 2948309 = 69101) (by norm_num)
theorem B4422869 : Blo 1309973 4422869 := bbase (se 7 (by rfl) ⟨51830, by rfl⟩ : syracuseStep 4422869 = 103661) (by norm_num)
theorem B6634709 : Blo 1309973 6634709 := bbase (se 7 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 6634709 = 155501) (by norm_num)
theorem B43130069 : Blo 1309973 43130069 := bbase (se 7 (by rfl) ⟨505430, by rfl⟩ : syracuseStep 43130069 = 1010861) (by norm_num)
theorem B1965293 : Blo 1309973 1965293 := bbase (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) (by norm_num)
theorem B1473781 : Blo 1309973 1473781 := bbase (se 5 (by rfl) ⟨69083, by rfl⟩ : syracuseStep 1473781 = 138167) (by norm_num)
theorem B1965317 : Blo 1309973 1965317 := bbase (se 4 (by rfl) ⟨184248, by rfl⟩ : syracuseStep 1965317 = 368497) (by norm_num)
theorem B2211077 : Blo 1309973 2211077 := bbase (se 4 (by rfl) ⟨207288, by rfl⟩ : syracuseStep 2211077 = 414577) (by norm_num)
theorem B4201733 : Blo 1309973 4201733 := bbase (se 4 (by rfl) ⟨393912, by rfl⟩ : syracuseStep 4201733 = 787825) (by norm_num)
theorem B4791557 : Blo 1309973 4791557 := bbase (se 4 (by rfl) ⟨449208, by rfl⟩ : syracuseStep 4791557 = 898417) (by norm_num)
theorem B1473817 : Blo 1309973 1473817 := bbase (se 2 (by rfl) ⟨552681, by rfl⟩ : syracuseStep 1473817 = 1105363) (by norm_num)
theorem B1965341 : Blo 1309973 1965341 := bbase (se 3 (by rfl) ⟨368501, by rfl⟩ : syracuseStep 1965341 = 737003) (by norm_num)
theorem B2948381 : Blo 1309973 2948381 := bbase (se 3 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 2948381 = 1105643) (by norm_num)
theorem B3317021 : Blo 1309973 3317021 := bbase (se 3 (by rfl) ⟨621941, by rfl⟩ : syracuseStep 3317021 = 1243883) (by norm_num)
theorem B1965365 : Blo 1309973 1965365 := bbase (se 5 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 1965365 = 184253) (by norm_num)
theorem B1473853 : Blo 1309973 1473853 := bbase (se 3 (by rfl) ⟨276347, by rfl⟩ : syracuseStep 1473853 = 552695) (by norm_num)
theorem B1965389 : Blo 1309973 1965389 := bbase (se 3 (by rfl) ⟨368510, by rfl⟩ : syracuseStep 1965389 = 737021) (by norm_num)
theorem B1473889 : Blo 1309973 1473889 := bbase (se 2 (by rfl) ⟨552708, by rfl⟩ : syracuseStep 1473889 = 1105417) (by norm_num)
theorem B1965413 : Blo 1309973 1965413 := bbase (se 4 (by rfl) ⟨184257, by rfl⟩ : syracuseStep 1965413 = 368515) (by norm_num)
theorem B2948453 : Blo 1309973 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B5389685 : Blo 1309973 5389685 := bbase (se 5 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 5389685 = 505283) (by norm_num)
theorem B2489717 : Blo 1309973 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B1965437 : Blo 1309973 1965437 := bbase (se 3 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 1965437 = 737039) (by norm_num)
theorem B1473925 : Blo 1309973 1473925 := bbase (se 4 (by rfl) ⟨138180, by rfl⟩ : syracuseStep 1473925 = 276361) (by norm_num)
theorem B2211205 : Blo 1309973 2211205 := bbase (se 4 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 2211205 = 414601) (by norm_num)
theorem B1965461 : Blo 1309973 1965461 := bbase (se 6 (by rfl) ⟨46065, by rfl⟩ : syracuseStep 1965461 = 92131) (by norm_num)
theorem B1473961 : Blo 1309973 1473961 := bbase (se 2 (by rfl) ⟨552735, by rfl⟩ : syracuseStep 1473961 = 1105471) (by norm_num)
theorem B1965485 : Blo 1309973 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B2948525 : Blo 1309973 2948525 := bbase (se 3 (by rfl) ⟨552848, by rfl⟩ : syracuseStep 2948525 = 1105697) (by norm_num)
theorem B2801069 : Blo 1309973 2801069 := bbase (se 3 (by rfl) ⟨525200, by rfl⟩ : syracuseStep 2801069 = 1050401) (by norm_num)
theorem B4980149 : Blo 1309973 4980149 := bbase (se 5 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 4980149 = 466889) (by norm_num)
theorem B1400257 : Blo 1309973 1400257 := bbase (se 2 (by rfl) ⟨525096, by rfl⟩ : syracuseStep 1400257 = 1050193) (by norm_num)
theorem B1965509 : Blo 1309973 1965509 := bbase (se 4 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 1965509 = 368533) (by norm_num)
theorem B1400261 : Blo 1309973 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B1473997 : Blo 1309973 1473997 := bbase (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) (by norm_num)
theorem B3317213 : Blo 1309973 3317213 := bbase (se 3 (by rfl) ⟨621977, by rfl⟩ : syracuseStep 3317213 = 1243955) (by norm_num)
theorem B1965533 : Blo 1309973 1965533 := bbase (se 3 (by rfl) ⟨368537, by rfl⟩ : syracuseStep 1965533 = 737075) (by norm_num)
theorem B2211293 : Blo 1309973 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B1474033 : Blo 1309973 1474033 := bbase (se 2 (by rfl) ⟨552762, by rfl⟩ : syracuseStep 1474033 = 1105525) (by norm_num)
theorem B1965557 : Blo 1309973 1965557 := bbase (se 5 (by rfl) ⟨92135, by rfl⟩ : syracuseStep 1965557 = 184271) (by norm_num)
theorem B2948597 : Blo 1309973 2948597 := bbase (se 5 (by rfl) ⟨138215, by rfl⟩ : syracuseStep 2948597 = 276431) (by norm_num)
theorem B1965581 : Blo 1309973 1965581 := bbase (se 3 (by rfl) ⟨368546, by rfl⟩ : syracuseStep 1965581 = 737093) (by norm_num)
theorem B2489869 : Blo 1309973 2489869 := bbase (se 3 (by rfl) ⟨466850, by rfl⟩ : syracuseStep 2489869 = 933701) (by norm_num)
theorem B1474069 : Blo 1309973 1474069 := bbase (se 6 (by rfl) ⟨34548, by rfl⟩ : syracuseStep 1474069 = 69097) (by norm_num)
theorem B1965605 : Blo 1309973 1965605 := bbase (se 4 (by rfl) ⟨184275, by rfl⟩ : syracuseStep 1965605 = 368551) (by norm_num)
theorem B3784229 : Blo 1309973 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B1474105 : Blo 1309973 1474105 := bbase (se 2 (by rfl) ⟨552789, by rfl⟩ : syracuseStep 1474105 = 1105579) (by norm_num)
theorem B1965629 : Blo 1309973 1965629 := bbase (se 3 (by rfl) ⟨368555, by rfl⟩ : syracuseStep 1965629 = 737111) (by norm_num)
theorem B2948669 : Blo 1309973 2948669 := bbase (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) (by norm_num)
theorem B1965653 : Blo 1309973 1965653 := bbase (se 8 (by rfl) ⟨11517, by rfl⟩ : syracuseStep 1965653 = 23035) (by norm_num)
theorem B1474141 : Blo 1309973 1474141 := bbase (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) (by norm_num)
theorem B2211421 : Blo 1309973 2211421 := bbase (se 3 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 2211421 = 829283) (by norm_num)
theorem B1965677 : Blo 1309973 1965677 := bbase (se 3 (by rfl) ⟨368564, by rfl⟩ : syracuseStep 1965677 = 737129) (by norm_num)
theorem B1474177 : Blo 1309973 1474177 := bbase (se 2 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 1474177 = 1105633) (by norm_num)
theorem B2948741 : Blo 1309973 2948741 := bbase (se 4 (by rfl) ⟨276444, by rfl⟩ : syracuseStep 2948741 = 552889) (by norm_num)
theorem B4423301 : Blo 1309973 4423301 := bbase (se 4 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 4423301 = 829369) (by norm_num)
theorem B1965701 : Blo 1309973 1965701 := bbase (se 4 (by rfl) ⟨184284, by rfl⟩ : syracuseStep 1965701 = 368569) (by norm_num)
theorem B12590741 : Blo 1309973 12590741 := bbase (se 6 (by rfl) ⟨295095, by rfl⟩ : syracuseStep 12590741 = 590191) (by norm_num)
theorem B1965725 : Blo 1309973 1965725 := bbase (se 3 (by rfl) ⟨368573, by rfl⟩ : syracuseStep 1965725 = 737147) (by norm_num)
theorem B1474213 : Blo 1309973 1474213 := bbase (se 4 (by rfl) ⟨138207, by rfl⟩ : syracuseStep 1474213 = 276415) (by norm_num)
theorem B1965749 : Blo 1309973 1965749 := bbase (se 5 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 1965749 = 184289) (by norm_num)
theorem B2211509 : Blo 1309973 2211509 := bbase (se 5 (by rfl) ⟨103664, by rfl⟩ : syracuseStep 2211509 = 207329) (by norm_num)
theorem B1474249 : Blo 1309973 1474249 := bbase (se 2 (by rfl) ⟨552843, by rfl⟩ : syracuseStep 1474249 = 1105687) (by norm_num)
theorem B1965773 : Blo 1309973 1965773 := bbase (se 3 (by rfl) ⟨368582, by rfl⟩ : syracuseStep 1965773 = 737165) (by norm_num)
theorem B2948813 : Blo 1309973 2948813 := bbase (se 3 (by rfl) ⟨552902, by rfl⟩ : syracuseStep 2948813 = 1105805) (by norm_num)
theorem B4980437 : Blo 1309973 4980437 := bbase (se 7 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 4980437 = 116729) (by norm_num)
theorem B1965797 : Blo 1309973 1965797 := bbase (se 4 (by rfl) ⟨184293, by rfl⟩ : syracuseStep 1965797 = 368587) (by norm_num)
theorem B1867493 : Blo 1309973 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B1474285 : Blo 1309973 1474285 := bbase (se 3 (by rfl) ⟨276428, by rfl⟩ : syracuseStep 1474285 = 552857) (by norm_num)
theorem B1965821 : Blo 1309973 1965821 := bbase (se 3 (by rfl) ⟨368591, by rfl⟩ : syracuseStep 1965821 = 737183) (by norm_num)
theorem B1474321 : Blo 1309973 1474321 := bbase (se 2 (by rfl) ⟨552870, by rfl⟩ : syracuseStep 1474321 = 1105741) (by norm_num)
theorem B1965845 : Blo 1309973 1965845 := bbase (se 6 (by rfl) ⟨46074, by rfl⟩ : syracuseStep 1965845 = 92149) (by norm_num)
theorem B2948885 : Blo 1309973 2948885 := bbase (se 6 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 2948885 = 138229) (by norm_num)
theorem B1965869 : Blo 1309973 1965869 := bbase (se 3 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 1965869 = 737201) (by norm_num)
theorem B1474357 : Blo 1309973 1474357 := bbase (se 5 (by rfl) ⟨69110, by rfl⟩ : syracuseStep 1474357 = 138221) (by norm_num)
theorem B2211637 : Blo 1309973 2211637 := bbase (se 5 (by rfl) ⟨103670, by rfl⟩ : syracuseStep 2211637 = 207341) (by norm_num)
theorem B3317557 : Blo 1309973 3317557 := bbase (se 5 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 3317557 = 311021) (by norm_num)
theorem B1867573 : Blo 1309973 1867573 := bbase (se 5 (by rfl) ⟨87542, by rfl⟩ : syracuseStep 1867573 = 175085) (by norm_num)
theorem B2490173 : Blo 1309973 2490173 := bbase (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) (by norm_num)
theorem B1965893 : Blo 1309973 1965893 := bbase (se 4 (by rfl) ⟨184302, by rfl⟩ : syracuseStep 1965893 = 368605) (by norm_num)
theorem B1892165 : Blo 1309973 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1474393 : Blo 1309973 1474393 := bbase (se 2 (by rfl) ⟨552897, by rfl⟩ : syracuseStep 1474393 = 1105795) (by norm_num)
theorem B1965917 : Blo 1309973 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B2948957 : Blo 1309973 2948957 := bbase (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) (by norm_num)
theorem B12115829 : Blo 1309973 12115829 := bbase (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) (by norm_num)
theorem B1965941 : Blo 1309973 1965941 := bbase (se 5 (by rfl) ⟨92153, by rfl⟩ : syracuseStep 1965941 = 184307) (by norm_num)
theorem B3030901 : Blo 1309973 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B1474429 : Blo 1309973 1474429 := bbase (se 3 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 1474429 = 552911) (by norm_num)
theorem B1965965 : Blo 1309973 1965965 := bbase (se 3 (by rfl) ⟨368618, by rfl⟩ : syracuseStep 1965965 = 737237) (by norm_num)
theorem B2211725 : Blo 1309973 2211725 := bbase (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) (by norm_num)
theorem B2662301 : Blo 1309973 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B1474465 : Blo 1309973 1474465 := bbase (se 2 (by rfl) ⟨552924, by rfl⟩ : syracuseStep 1474465 = 1105849) (by norm_num)
theorem B1965989 : Blo 1309973 1965989 := bbase (se 4 (by rfl) ⟨184311, by rfl⟩ : syracuseStep 1965989 = 368623) (by norm_num)
theorem B2949029 : Blo 1309973 2949029 := bbase (se 4 (by rfl) ⟨276471, by rfl⟩ : syracuseStep 2949029 = 552943) (by norm_num)
theorem B3317669 : Blo 1309973 3317669 := bbase (se 4 (by rfl) ⟨311031, by rfl⟩ : syracuseStep 3317669 = 622063) (by norm_num)
theorem B1867693 : Blo 1309973 1867693 := bbase (se 3 (by rfl) ⟨350192, by rfl⟩ : syracuseStep 1867693 = 700385) (by norm_num)
theorem B1966013 : Blo 1309973 1966013 := bbase (se 3 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 1966013 = 737255) (by norm_num)
theorem B1474501 : Blo 1309973 1474501 := bbase (se 4 (by rfl) ⟨138234, by rfl⟩ : syracuseStep 1474501 = 276469) (by norm_num)
theorem B1966037 : Blo 1309973 1966037 := bbase (se 7 (by rfl) ⟨23039, by rfl⟩ : syracuseStep 1966037 = 46079) (by norm_num)
theorem B1474537 : Blo 1309973 1474537 := bbase (se 2 (by rfl) ⟨552951, by rfl⟩ : syracuseStep 1474537 = 1105903) (by norm_num)
theorem B1966061 : Blo 1309973 1966061 := bbase (se 3 (by rfl) ⟨368636, by rfl⟩ : syracuseStep 1966061 = 737273) (by norm_num)
theorem B2949101 : Blo 1309973 2949101 := bbase (se 3 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 2949101 = 1105913) (by norm_num)
theorem B1310723 : Blo 1309973 1310723 := bstep (se 1 (by rfl) ⟨983042, by rfl⟩ : syracuseStep 1310723 = 1966085) B1966085
theorem B2949137 : Blo 1309973 2949137 := bstep (se 2 (by rfl) ⟨1105926, by rfl⟩ : syracuseStep 2949137 = 2211853) B2211853
theorem B1966097 : Blo 1309973 1966097 := bstep (se 2 (by rfl) ⟨737286, by rfl⟩ : syracuseStep 1966097 = 1474573) B1474573
theorem B1310739 : Blo 1309973 1310739 := bstep (se 1 (by rfl) ⟨983054, by rfl⟩ : syracuseStep 1310739 = 1966109) B1966109
theorem B9453581 : Blo 1309973 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B2949155 : Blo 1309973 2949155 := bstep (se 1 (by rfl) ⟨2211866, by rfl⟩ : syracuseStep 2949155 = 4423733) B4423733
theorem B1966115 : Blo 1309973 1966115 := bstep (se 1 (by rfl) ⟨1474586, by rfl⟩ : syracuseStep 1966115 = 2949173) B2949173
theorem B1310755 : Blo 1309973 1310755 := bstep (se 1 (by rfl) ⟨983066, by rfl⟩ : syracuseStep 1310755 = 1966133) B1966133
theorem B1310771 : Blo 1309973 1310771 := bstep (se 1 (by rfl) ⟨983078, by rfl⟩ : syracuseStep 1310771 = 1966157) B1966157
theorem B1966145 : Blo 1309973 1966145 := bstep (se 2 (by rfl) ⟨737304, by rfl⟩ : syracuseStep 1966145 = 1474609) B1474609
theorem B2211907 : Blo 1309973 2211907 := bstep (se 1 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 2211907 = 3317861) B3317861
theorem B1474627 : Blo 1309973 1474627 := bstep (se 1 (by rfl) ⟨1105970, by rfl⟩ : syracuseStep 1474627 = 2211941) B2211941
theorem B1310787 : Blo 1309973 1310787 := bstep (se 1 (by rfl) ⟨983090, by rfl⟩ : syracuseStep 1310787 = 1966181) B1966181
theorem B11198533 : Blo 1309973 11198533 := bstep (se 4 (by rfl) ⟨1049862, by rfl⟩ : syracuseStep 11198533 = 2099725) B2099725
theorem B9961541 : Blo 1309973 9961541 := bstep (se 4 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 9961541 = 1867789) B1867789
theorem B1966163 : Blo 1309973 1966163 := bstep (se 1 (by rfl) ⟨1474622, by rfl⟩ : syracuseStep 1966163 = 2949245) B2949245
theorem B1310803 : Blo 1309973 1310803 := bstep (se 1 (by rfl) ⟨983102, by rfl⟩ : syracuseStep 1310803 = 1966205) B1966205
theorem B1310819 : Blo 1309973 1310819 := bstep (se 1 (by rfl) ⟨983114, by rfl⟩ : syracuseStep 1310819 = 1966229) B1966229
theorem B1966193 : Blo 1309973 1966193 := bstep (se 2 (by rfl) ⟨737322, by rfl⟩ : syracuseStep 1966193 = 1474645) B1474645
theorem B1310835 : Blo 1309973 1310835 := bstep (se 1 (by rfl) ⟨983126, by rfl⟩ : syracuseStep 1310835 = 1966253) B1966253
theorem B1966211 : Blo 1309973 1966211 := bstep (se 1 (by rfl) ⟨1474658, by rfl⟩ : syracuseStep 1966211 = 2949317) B2949317
theorem B1310851 : Blo 1309973 1310851 := bstep (se 1 (by rfl) ⟨983138, by rfl⟩ : syracuseStep 1310851 = 1966277) B1966277
theorem B1310867 : Blo 1309973 1310867 := bstep (se 1 (by rfl) ⟨983150, by rfl⟩ : syracuseStep 1310867 = 1966301) B1966301
theorem B1966241 : Blo 1309973 1966241 := bstep (se 2 (by rfl) ⟨737340, by rfl⟩ : syracuseStep 1966241 = 1474681) B1474681
theorem B1310883 : Blo 1309973 1310883 := bstep (se 1 (by rfl) ⟨983162, by rfl⟩ : syracuseStep 1310883 = 1966325) B1966325
theorem B3735715 : Blo 1309973 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B1966259 : Blo 1309973 1966259 := bstep (se 1 (by rfl) ⟨1474694, by rfl⟩ : syracuseStep 1966259 = 2949389) B2949389
theorem B1310899 : Blo 1309973 1310899 := bstep (se 1 (by rfl) ⟨983174, by rfl⟩ : syracuseStep 1310899 = 1966349) B1966349
theorem B1310915 : Blo 1309973 1310915 := bstep (se 1 (by rfl) ⟨983186, by rfl⟩ : syracuseStep 1310915 = 1966373) B1966373
theorem B2212049 : Blo 1309973 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B1966289 : Blo 1309973 1966289 := bstep (se 2 (by rfl) ⟨737358, by rfl⟩ : syracuseStep 1966289 = 1474717) B1474717
theorem B1474771 : Blo 1309973 1474771 := bstep (se 1 (by rfl) ⟨1106078, by rfl⟩ : syracuseStep 1474771 = 2212157) B2212157
theorem B1310931 : Blo 1309973 1310931 := bstep (se 1 (by rfl) ⟨983198, by rfl⟩ : syracuseStep 1310931 = 1966397) B1966397
theorem B1966307 : Blo 1309973 1966307 := bstep (se 1 (by rfl) ⟨1474730, by rfl⟩ : syracuseStep 1966307 = 2949461) B2949461
theorem B1310947 : Blo 1309973 1310947 := bstep (se 1 (by rfl) ⟨983210, by rfl⟩ : syracuseStep 1310947 = 1966421) B1966421
theorem B1868017 : Blo 1309973 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B1310963 : Blo 1309973 1310963 := bstep (se 1 (by rfl) ⟨983222, by rfl⟩ : syracuseStep 1310963 = 1966445) B1966445
theorem B1966337 : Blo 1309973 1966337 := bstep (se 2 (by rfl) ⟨737376, by rfl⟩ : syracuseStep 1966337 = 1474753) B1474753
theorem B1310979 : Blo 1309973 1310979 := bstep (se 1 (by rfl) ⟨983234, by rfl⟩ : syracuseStep 1310979 = 1966469) B1966469
theorem B4423949 : Blo 1309973 4423949 := bstep (se 3 (by rfl) ⟨829490, by rfl⟩ : syracuseStep 4423949 = 1658981) B1658981
theorem B1966355 : Blo 1309973 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B1310995 : Blo 1309973 1310995 := bstep (se 1 (by rfl) ⟨983246, by rfl⟩ : syracuseStep 1310995 = 1966493) B1966493
theorem B1311011 : Blo 1309973 1311011 := bstep (se 1 (by rfl) ⟨983258, by rfl⟩ : syracuseStep 1311011 = 1966517) B1966517
theorem B2490659 : Blo 1309973 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B2949425 : Blo 1309973 2949425 := bstep (se 2 (by rfl) ⟨1106034, by rfl⟩ : syracuseStep 2949425 = 2212069) B2212069
theorem B1966385 : Blo 1309973 1966385 := bstep (se 2 (by rfl) ⟨737394, by rfl⟩ : syracuseStep 1966385 = 1474789) B1474789
theorem B1311027 : Blo 1309973 1311027 := bstep (se 1 (by rfl) ⟨983270, by rfl⟩ : syracuseStep 1311027 = 1966541) B1966541
theorem B4424003 : Blo 1309973 4424003 := bstep (se 1 (by rfl) ⟨3318002, by rfl⟩ : syracuseStep 4424003 = 6636005) B6636005
theorem B2949443 : Blo 1309973 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1966403 : Blo 1309973 1966403 := bstep (se 1 (by rfl) ⟨1474802, by rfl⟩ : syracuseStep 1966403 = 2949605) B2949605
theorem B1311043 : Blo 1309973 1311043 := bstep (se 1 (by rfl) ⟨983282, by rfl⟩ : syracuseStep 1311043 = 1966565) B1966565
theorem B3735875 : Blo 1309973 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B2212177 : Blo 1309973 2212177 := bstep (se 2 (by rfl) ⟨829566, by rfl⟩ : syracuseStep 2212177 = 1659133) B1659133
theorem B1311059 : Blo 1309973 1311059 := bstep (se 1 (by rfl) ⟨983294, by rfl⟩ : syracuseStep 1311059 = 1966589) B1966589
theorem B1966433 : Blo 1309973 1966433 := bstep (se 2 (by rfl) ⟨737412, by rfl⟩ : syracuseStep 1966433 = 1474825) B1474825
theorem B1474915 : Blo 1309973 1474915 := bstep (se 1 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 1474915 = 2212373) B2212373
theorem B1311075 : Blo 1309973 1311075 := bstep (se 1 (by rfl) ⟨983306, by rfl⟩ : syracuseStep 1311075 = 1966613) B1966613
theorem B2212211 : Blo 1309973 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B1966451 : Blo 1309973 1966451 := bstep (se 1 (by rfl) ⟨1474838, by rfl⟩ : syracuseStep 1966451 = 2949677) B2949677
theorem B1311091 : Blo 1309973 1311091 := bstep (se 1 (by rfl) ⟨983318, by rfl⟩ : syracuseStep 1311091 = 1966637) B1966637
theorem B1311107 : Blo 1309973 1311107 := bstep (se 1 (by rfl) ⟨983330, by rfl⟩ : syracuseStep 1311107 = 1966661) B1966661
theorem B1966481 : Blo 1309973 1966481 := bstep (se 2 (by rfl) ⟨737430, by rfl⟩ : syracuseStep 1966481 = 1474861) B1474861
theorem B1311123 : Blo 1309973 1311123 := bstep (se 1 (by rfl) ⟨983342, by rfl⟩ : syracuseStep 1311123 = 1966685) B1966685
theorem B1966499 : Blo 1309973 1966499 := bstep (se 1 (by rfl) ⟨1474874, by rfl⟩ : syracuseStep 1966499 = 2949749) B2949749
theorem B1311139 : Blo 1309973 1311139 := bstep (se 1 (by rfl) ⟨983354, by rfl⟩ : syracuseStep 1311139 = 1966709) B1966709
theorem B1311155 : Blo 1309973 1311155 := bstep (se 1 (by rfl) ⟨983366, by rfl⟩ : syracuseStep 1311155 = 1966733) B1966733
theorem B1966529 : Blo 1309973 1966529 := bstep (se 2 (by rfl) ⟨737448, by rfl⟩ : syracuseStep 1966529 = 1474897) B1474897
theorem B1311171 : Blo 1309973 1311171 := bstep (se 1 (by rfl) ⟨983378, by rfl⟩ : syracuseStep 1311171 = 1966757) B1966757
theorem B7668173 : Blo 1309973 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B1966547 : Blo 1309973 1966547 := bstep (se 1 (by rfl) ⟨1474910, by rfl⟩ : syracuseStep 1966547 = 2949821) B2949821
theorem B1311187 : Blo 1309973 1311187 := bstep (se 1 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 1311187 = 1966781) B1966781
theorem B1311203 : Blo 1309973 1311203 := bstep (se 1 (by rfl) ⟨983402, by rfl⟩ : syracuseStep 1311203 = 1966805) B1966805
theorem B4727267 : Blo 1309973 4727267 := bstep (se 1 (by rfl) ⟨3545450, by rfl⟩ : syracuseStep 4727267 = 7090901) B7090901
theorem B1966577 : Blo 1309973 1966577 := bstep (se 2 (by rfl) ⟨737466, by rfl⟩ : syracuseStep 1966577 = 1474933) B1474933
theorem B2212339 : Blo 1309973 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1475059 : Blo 1309973 1475059 := bstep (se 1 (by rfl) ⟨1106294, by rfl⟩ : syracuseStep 1475059 = 2212589) B2212589
theorem B1311219 : Blo 1309973 1311219 := bstep (se 1 (by rfl) ⟨983414, by rfl⟩ : syracuseStep 1311219 = 1966829) B1966829
theorem B1966595 : Blo 1309973 1966595 := bstep (se 1 (by rfl) ⟨1474946, by rfl⟩ : syracuseStep 1966595 = 2949893) B2949893
theorem B1311235 : Blo 1309973 1311235 := bstep (se 1 (by rfl) ⟨983426, by rfl⟩ : syracuseStep 1311235 = 1966853) B1966853
theorem B1311251 : Blo 1309973 1311251 := bstep (se 1 (by rfl) ⟨983438, by rfl⟩ : syracuseStep 1311251 = 1966877) B1966877
theorem B1966625 : Blo 1309973 1966625 := bstep (se 2 (by rfl) ⟨737484, by rfl⟩ : syracuseStep 1966625 = 1474969) B1474969
theorem B1311267 : Blo 1309973 1311267 := bstep (se 1 (by rfl) ⟨983450, by rfl⟩ : syracuseStep 1311267 = 1966901) B1966901
theorem B1966643 : Blo 1309973 1966643 := bstep (se 1 (by rfl) ⟨1474982, by rfl⟩ : syracuseStep 1966643 = 2949965) B2949965
theorem B1311283 : Blo 1309973 1311283 := bstep (se 1 (by rfl) ⟨983462, by rfl⟩ : syracuseStep 1311283 = 1966925) B1966925
theorem B1311299 : Blo 1309973 1311299 := bstep (se 1 (by rfl) ⟨983474, by rfl⟩ : syracuseStep 1311299 = 1966949) B1966949
theorem B4424273 : Blo 1309973 4424273 := bstep (se 2 (by rfl) ⟨1659102, by rfl⟩ : syracuseStep 4424273 = 3318205) B3318205
theorem B2949713 : Blo 1309973 2949713 := bstep (se 2 (by rfl) ⟨1106142, by rfl⟩ : syracuseStep 2949713 = 2212285) B2212285
theorem B1966673 : Blo 1309973 1966673 := bstep (se 2 (by rfl) ⟨737502, by rfl⟩ : syracuseStep 1966673 = 1475005) B1475005
theorem B1311315 : Blo 1309973 1311315 := bstep (se 1 (by rfl) ⟨983486, by rfl⟩ : syracuseStep 1311315 = 1966973) B1966973
theorem B2949731 : Blo 1309973 2949731 := bstep (se 1 (by rfl) ⟨2212298, by rfl⟩ : syracuseStep 2949731 = 4424597) B4424597
theorem B1966691 : Blo 1309973 1966691 := bstep (se 1 (by rfl) ⟨1475018, by rfl⟩ : syracuseStep 1966691 = 2950037) B2950037
theorem B1311331 : Blo 1309973 1311331 := bstep (se 1 (by rfl) ⟨983498, by rfl⟩ : syracuseStep 1311331 = 1966997) B1966997
theorem B11207281 : Blo 1309973 11207281 := bstep (se 2 (by rfl) ⟨4202730, by rfl⟩ : syracuseStep 11207281 = 8405461) B8405461
theorem B1311347 : Blo 1309973 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B2212481 : Blo 1309973 2212481 := bstep (se 2 (by rfl) ⟨829680, by rfl⟩ : syracuseStep 2212481 = 1659361) B1659361
theorem B1966721 : Blo 1309973 1966721 := bstep (se 2 (by rfl) ⟨737520, by rfl⟩ : syracuseStep 1966721 = 1475041) B1475041
theorem B1475203 : Blo 1309973 1475203 := bstep (se 1 (by rfl) ⟨1106402, by rfl⟩ : syracuseStep 1475203 = 2212805) B2212805
theorem B1311363 : Blo 1309973 1311363 := bstep (se 1 (by rfl) ⟨983522, by rfl⟩ : syracuseStep 1311363 = 1967045) B1967045
theorem B1966739 : Blo 1309973 1966739 := bstep (se 1 (by rfl) ⟨1475054, by rfl⟩ : syracuseStep 1966739 = 2950109) B2950109
theorem B1311379 : Blo 1309973 1311379 := bstep (se 1 (by rfl) ⟨983534, by rfl⟩ : syracuseStep 1311379 = 1967069) B1967069
theorem B1311395 : Blo 1309973 1311395 := bstep (se 1 (by rfl) ⟨983546, by rfl⟩ : syracuseStep 1311395 = 1967093) B1967093
theorem B1966769 : Blo 1309973 1966769 := bstep (se 2 (by rfl) ⟨737538, by rfl⟩ : syracuseStep 1966769 = 1475077) B1475077
theorem B1311411 : Blo 1309973 1311411 := bstep (se 1 (by rfl) ⟨983558, by rfl⟩ : syracuseStep 1311411 = 1967117) B1967117
theorem B1966787 : Blo 1309973 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B1311427 : Blo 1309973 1311427 := bstep (se 1 (by rfl) ⟨983570, by rfl⟩ : syracuseStep 1311427 = 1967141) B1967141
theorem B1311443 : Blo 1309973 1311443 := bstep (se 1 (by rfl) ⟨983582, by rfl⟩ : syracuseStep 1311443 = 1967165) B1967165
theorem B1966817 : Blo 1309973 1966817 := bstep (se 2 (by rfl) ⟨737556, by rfl⟩ : syracuseStep 1966817 = 1475113) B1475113
theorem B1311459 : Blo 1309973 1311459 := bstep (se 1 (by rfl) ⟨983594, by rfl⟩ : syracuseStep 1311459 = 1967189) B1967189
theorem B1966835 : Blo 1309973 1966835 := bstep (se 1 (by rfl) ⟨1475126, by rfl⟩ : syracuseStep 1966835 = 2950253) B2950253
theorem B1311475 : Blo 1309973 1311475 := bstep (se 1 (by rfl) ⟨983606, by rfl⟩ : syracuseStep 1311475 = 1967213) B1967213
theorem B2212609 : Blo 1309973 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B1311491 : Blo 1309973 1311491 := bstep (se 1 (by rfl) ⟨983618, by rfl⟩ : syracuseStep 1311491 = 1967237) B1967237
theorem B7471885 : Blo 1309973 7471885 := bstep (se 3 (by rfl) ⟨1400978, by rfl⟩ : syracuseStep 7471885 = 2801957) B2801957
theorem B1966865 : Blo 1309973 1966865 := bstep (se 2 (by rfl) ⟨737574, by rfl⟩ : syracuseStep 1966865 = 1475149) B1475149
theorem B1475347 : Blo 1309973 1475347 := bstep (se 1 (by rfl) ⟨1106510, by rfl⟩ : syracuseStep 1475347 = 2213021) B2213021
theorem B1311507 : Blo 1309973 1311507 := bstep (se 1 (by rfl) ⟨983630, by rfl⟩ : syracuseStep 1311507 = 1967261) B1967261
theorem B2212643 : Blo 1309973 2212643 := bstep (se 1 (by rfl) ⟨1659482, by rfl⟩ : syracuseStep 2212643 = 3318965) B3318965
theorem B1966883 : Blo 1309973 1966883 := bstep (se 1 (by rfl) ⟨1475162, by rfl⟩ : syracuseStep 1966883 = 2950325) B2950325
theorem B1311523 : Blo 1309973 1311523 := bstep (se 1 (by rfl) ⟨983642, by rfl⟩ : syracuseStep 1311523 = 1967285) B1967285
theorem B1311539 : Blo 1309973 1311539 := bstep (se 1 (by rfl) ⟨983654, by rfl⟩ : syracuseStep 1311539 = 1967309) B1967309
theorem B1966913 : Blo 1309973 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B1311555 : Blo 1309973 1311555 := bstep (se 1 (by rfl) ⟨983666, by rfl⟩ : syracuseStep 1311555 = 1967333) B1967333
theorem B1966931 : Blo 1309973 1966931 := bstep (se 1 (by rfl) ⟨1475198, by rfl⟩ : syracuseStep 1966931 = 2950397) B2950397
theorem B1311571 : Blo 1309973 1311571 := bstep (se 1 (by rfl) ⟨983678, by rfl⟩ : syracuseStep 1311571 = 1967357) B1967357
theorem B1311587 : Blo 1309973 1311587 := bstep (se 1 (by rfl) ⟨983690, by rfl⟩ : syracuseStep 1311587 = 1967381) B1967381
theorem B3318641 : Blo 1309973 3318641 := bstep (se 2 (by rfl) ⟨1244490, by rfl⟩ : syracuseStep 3318641 = 2488981) B2488981
theorem B2950001 : Blo 1309973 2950001 := bstep (se 2 (by rfl) ⟨1106250, by rfl⟩ : syracuseStep 2950001 = 2212501) B2212501
theorem B1966961 : Blo 1309973 1966961 := bstep (se 2 (by rfl) ⟨737610, by rfl⟩ : syracuseStep 1966961 = 1475221) B1475221
theorem B1311603 : Blo 1309973 1311603 := bstep (se 1 (by rfl) ⟨983702, by rfl⟩ : syracuseStep 1311603 = 1967405) B1967405
theorem B2950019 : Blo 1309973 2950019 := bstep (se 1 (by rfl) ⟨2212514, by rfl⟩ : syracuseStep 2950019 = 4425029) B4425029
theorem B1966979 : Blo 1309973 1966979 := bstep (se 1 (by rfl) ⟨1475234, by rfl⟩ : syracuseStep 1966979 = 2950469) B2950469
theorem B1311619 : Blo 1309973 1311619 := bstep (se 1 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 1311619 = 1967429) B1967429
theorem B1311635 : Blo 1309973 1311635 := bstep (se 1 (by rfl) ⟨983726, by rfl⟩ : syracuseStep 1311635 = 1967453) B1967453
theorem B1967009 : Blo 1309973 1967009 := bstep (se 2 (by rfl) ⟨737628, by rfl⟩ : syracuseStep 1967009 = 1475257) B1475257
theorem B3318691 : Blo 1309973 3318691 := bstep (se 1 (by rfl) ⟨2489018, by rfl⟩ : syracuseStep 3318691 = 4978037) B4978037
theorem B2212771 : Blo 1309973 2212771 := bstep (se 1 (by rfl) ⟨1659578, by rfl⟩ : syracuseStep 2212771 = 3319157) B3319157
theorem B1475491 : Blo 1309973 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B1311651 : Blo 1309973 1311651 := bstep (se 1 (by rfl) ⟨983738, by rfl⟩ : syracuseStep 1311651 = 1967477) B1967477
theorem B1967027 : Blo 1309973 1967027 := bstep (se 1 (by rfl) ⟨1475270, by rfl⟩ : syracuseStep 1967027 = 2950541) B2950541
theorem B1311667 : Blo 1309973 1311667 := bstep (se 1 (by rfl) ⟨983750, by rfl⟩ : syracuseStep 1311667 = 1967501) B1967501
theorem B1311683 : Blo 1309973 1311683 := bstep (se 1 (by rfl) ⟨983762, by rfl⟩ : syracuseStep 1311683 = 1967525) B1967525
theorem B1967057 : Blo 1309973 1967057 := bstep (se 2 (by rfl) ⟨737646, by rfl⟩ : syracuseStep 1967057 = 1475293) B1475293
theorem B1311699 : Blo 1309973 1311699 := bstep (se 1 (by rfl) ⟨983774, by rfl⟩ : syracuseStep 1311699 = 1967549) B1967549
theorem B1967075 : Blo 1309973 1967075 := bstep (se 1 (by rfl) ⟨1475306, by rfl⟩ : syracuseStep 1967075 = 2950613) B2950613
theorem B1311715 : Blo 1309973 1311715 := bstep (se 1 (by rfl) ⟨983786, by rfl⟩ : syracuseStep 1311715 = 1967573) B1967573
theorem B1311731 : Blo 1309973 1311731 := bstep (se 1 (by rfl) ⟨983798, by rfl⟩ : syracuseStep 1311731 = 1967597) B1967597
theorem B1967105 : Blo 1309973 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B1311747 : Blo 1309973 1311747 := bstep (se 1 (by rfl) ⟨983810, by rfl⟩ : syracuseStep 1311747 = 1967621) B1967621
theorem B1967123 : Blo 1309973 1967123 := bstep (se 1 (by rfl) ⟨1475342, by rfl⟩ : syracuseStep 1967123 = 2950685) B2950685
theorem B1311763 : Blo 1309973 1311763 := bstep (se 1 (by rfl) ⟨983822, by rfl⟩ : syracuseStep 1311763 = 1967645) B1967645
theorem B1311779 : Blo 1309973 1311779 := bstep (se 1 (by rfl) ⟨983834, by rfl⟩ : syracuseStep 1311779 = 1967669) B1967669
theorem B3318833 : Blo 1309973 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B2212913 : Blo 1309973 2212913 := bstep (se 2 (by rfl) ⟨829842, by rfl⟩ : syracuseStep 2212913 = 1659685) B1659685
theorem B1967153 : Blo 1309973 1967153 := bstep (se 2 (by rfl) ⟨737682, by rfl⟩ : syracuseStep 1967153 = 1475365) B1475365
theorem B1475635 : Blo 1309973 1475635 := bstep (se 1 (by rfl) ⟨1106726, by rfl⟩ : syracuseStep 1475635 = 2213453) B2213453
theorem B1311795 : Blo 1309973 1311795 := bstep (se 1 (by rfl) ⟨983846, by rfl⟩ : syracuseStep 1311795 = 1967693) B1967693
theorem B1967171 : Blo 1309973 1967171 := bstep (se 1 (by rfl) ⟨1475378, by rfl⟩ : syracuseStep 1967171 = 2950757) B2950757
theorem B1311811 : Blo 1309973 1311811 := bstep (se 1 (by rfl) ⟨983858, by rfl⟩ : syracuseStep 1311811 = 1967717) B1967717
theorem B1311827 : Blo 1309973 1311827 := bstep (se 1 (by rfl) ⟨983870, by rfl⟩ : syracuseStep 1311827 = 1967741) B1967741
theorem B1967201 : Blo 1309973 1967201 := bstep (se 2 (by rfl) ⟨737700, by rfl⟩ : syracuseStep 1967201 = 1475401) B1475401
theorem B1573987 : Blo 1309973 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B1311843 : Blo 1309973 1311843 := bstep (se 1 (by rfl) ⟨983882, by rfl⟩ : syracuseStep 1311843 = 1967765) B1967765
theorem B4424813 : Blo 1309973 4424813 := bstep (se 3 (by rfl) ⟨829652, by rfl⟩ : syracuseStep 4424813 = 1659305) B1659305
theorem B1967219 : Blo 1309973 1967219 := bstep (se 1 (by rfl) ⟨1475414, by rfl⟩ : syracuseStep 1967219 = 2950829) B2950829
theorem B1311859 : Blo 1309973 1311859 := bstep (se 1 (by rfl) ⟨983894, by rfl⟩ : syracuseStep 1311859 = 1967789) B1967789
theorem B1311875 : Blo 1309973 1311875 := bstep (se 1 (by rfl) ⟨983906, by rfl⟩ : syracuseStep 1311875 = 1967813) B1967813
theorem B2950289 : Blo 1309973 2950289 := bstep (se 2 (by rfl) ⟨1106358, by rfl⟩ : syracuseStep 2950289 = 2212717) B2212717
theorem B1967249 : Blo 1309973 1967249 := bstep (se 2 (by rfl) ⟨737718, by rfl⟩ : syracuseStep 1967249 = 1475437) B1475437
theorem B1311891 : Blo 1309973 1311891 := bstep (se 1 (by rfl) ⟨983918, by rfl⟩ : syracuseStep 1311891 = 1967837) B1967837
theorem B4424867 : Blo 1309973 4424867 := bstep (se 1 (by rfl) ⟨3318650, by rfl⟩ : syracuseStep 4424867 = 6637301) B6637301
theorem B2950307 : Blo 1309973 2950307 := bstep (se 1 (by rfl) ⟨2212730, by rfl⟩ : syracuseStep 2950307 = 4425461) B4425461
theorem B1967267 : Blo 1309973 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B1311907 : Blo 1309973 1311907 := bstep (se 1 (by rfl) ⟨983930, by rfl⟩ : syracuseStep 1311907 = 1967861) B1967861
theorem B2213041 : Blo 1309973 2213041 := bstep (se 2 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 2213041 = 1659781) B1659781
theorem B1311923 : Blo 1309973 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B1967297 : Blo 1309973 1967297 := bstep (se 2 (by rfl) ⟨737736, by rfl⟩ : syracuseStep 1967297 = 1475473) B1475473
theorem B1574083 : Blo 1309973 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B1475779 : Blo 1309973 1475779 := bstep (se 1 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 1475779 = 2213669) B2213669
theorem B14165189 : Blo 1309973 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B1311939 : Blo 1309973 1311939 := bstep (se 1 (by rfl) ⟨983954, by rfl⟩ : syracuseStep 1311939 = 1967909) B1967909
theorem B2213075 : Blo 1309973 2213075 := bstep (se 1 (by rfl) ⟨1659806, by rfl⟩ : syracuseStep 2213075 = 3319613) B3319613
theorem B1967315 : Blo 1309973 1967315 := bstep (se 1 (by rfl) ⟨1475486, by rfl⟩ : syracuseStep 1967315 = 2950973) B2950973
theorem B1311955 : Blo 1309973 1311955 := bstep (se 1 (by rfl) ⟨983966, by rfl⟩ : syracuseStep 1311955 = 1967933) B1967933
theorem B1311971 : Blo 1309973 1311971 := bstep (se 1 (by rfl) ⟨983978, by rfl⟩ : syracuseStep 1311971 = 1967957) B1967957
theorem B4547821 : Blo 1309973 4547821 := bstep (se 3 (by rfl) ⟨852716, by rfl⟩ : syracuseStep 4547821 = 1705433) B1705433
theorem B1967345 : Blo 1309973 1967345 := bstep (se 2 (by rfl) ⟨737754, by rfl⟩ : syracuseStep 1967345 = 1475509) B1475509
theorem B1967363 : Blo 1309973 1967363 := bstep (se 1 (by rfl) ⟨1475522, by rfl⟩ : syracuseStep 1967363 = 2951045) B2951045
theorem B1967393 : Blo 1309973 1967393 := bstep (se 2 (by rfl) ⟨737772, by rfl⟩ : syracuseStep 1967393 = 1475545) B1475545
theorem B5596465 : Blo 1309973 5596465 := bstep (se 2 (by rfl) ⟨2098674, by rfl⟩ : syracuseStep 5596465 = 4197349) B4197349
theorem B1967411 : Blo 1309973 1967411 := bstep (se 1 (by rfl) ⟨1475558, by rfl⟩ : syracuseStep 1967411 = 2951117) B2951117
theorem B1770817 : Blo 1309973 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B16811333 : Blo 1309973 16811333 := bstep (se 4 (by rfl) ⟨1576062, by rfl⟩ : syracuseStep 16811333 = 3152125) B3152125
theorem B1967441 : Blo 1309973 1967441 := bstep (se 2 (by rfl) ⟨737790, by rfl⟩ : syracuseStep 1967441 = 1475581) B1475581
theorem B2213203 : Blo 1309973 2213203 := bstep (se 1 (by rfl) ⟨1659902, by rfl⟩ : syracuseStep 2213203 = 3319805) B3319805
theorem B1475923 : Blo 1309973 1475923 := bstep (se 1 (by rfl) ⟨1106942, by rfl⟩ : syracuseStep 1475923 = 2213885) B2213885
theorem B1967459 : Blo 1309973 1967459 := bstep (se 1 (by rfl) ⟨1475594, by rfl⟩ : syracuseStep 1967459 = 2951189) B2951189
theorem B5186929 : Blo 1309973 5186929 := bstep (se 2 (by rfl) ⟨1945098, by rfl⟩ : syracuseStep 5186929 = 3890197) B3890197
theorem B1967489 : Blo 1309973 1967489 := bstep (se 2 (by rfl) ⟨737808, by rfl⟩ : syracuseStep 1967489 = 1475617) B1475617
theorem B1967507 : Blo 1309973 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B6636977 : Blo 1309973 6636977 := bstep (se 2 (by rfl) ⟨2488866, by rfl⟩ : syracuseStep 6636977 = 4977733) B4977733
theorem B4425137 : Blo 1309973 4425137 := bstep (se 2 (by rfl) ⟨1659426, by rfl⟩ : syracuseStep 4425137 = 3318853) B3318853
theorem B2950577 : Blo 1309973 2950577 := bstep (se 2 (by rfl) ⟨1106466, by rfl⟩ : syracuseStep 2950577 = 2212933) B2212933
theorem B1967537 : Blo 1309973 1967537 := bstep (se 2 (by rfl) ⟨737826, by rfl⟩ : syracuseStep 1967537 = 1475653) B1475653
theorem B2950595 : Blo 1309973 2950595 := bstep (se 1 (by rfl) ⟨2212946, by rfl⟩ : syracuseStep 2950595 = 4425893) B4425893
theorem B1967555 : Blo 1309973 1967555 := bstep (se 1 (by rfl) ⟨1475666, by rfl⟩ : syracuseStep 1967555 = 2951333) B2951333
theorem B2213345 : Blo 1309973 2213345 := bstep (se 2 (by rfl) ⟨830004, by rfl⟩ : syracuseStep 2213345 = 1660009) B1660009
theorem B1967585 : Blo 1309973 1967585 := bstep (se 2 (by rfl) ⟨737844, by rfl⟩ : syracuseStep 1967585 = 1475689) B1475689
theorem B2835953 : Blo 1309973 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B1967603 : Blo 1309973 1967603 := bstep (se 1 (by rfl) ⟨1475702, by rfl⟩ : syracuseStep 1967603 = 2951405) B2951405
theorem B1967633 : Blo 1309973 1967633 := bstep (se 2 (by rfl) ⟨737862, by rfl⟩ : syracuseStep 1967633 = 1475725) B1475725
theorem B1967651 : Blo 1309973 1967651 := bstep (se 1 (by rfl) ⟨1475738, by rfl⟩ : syracuseStep 1967651 = 2951477) B2951477
theorem B21268021 : Blo 1309973 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B1967681 : Blo 1309973 1967681 := bstep (se 2 (by rfl) ⟨737880, by rfl⟩ : syracuseStep 1967681 = 1475761) B1475761
theorem B1967699 : Blo 1309973 1967699 := bstep (se 1 (by rfl) ⟨1475774, by rfl⟩ : syracuseStep 1967699 = 2951549) B2951549
theorem B2213473 : Blo 1309973 2213473 := bstep (se 2 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 2213473 = 1660105) B1660105
theorem B36374129 : Blo 1309973 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B1967729 : Blo 1309973 1967729 := bstep (se 2 (by rfl) ⟨737898, by rfl⟩ : syracuseStep 1967729 = 1475797) B1475797
theorem B2213507 : Blo 1309973 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B1967747 : Blo 1309973 1967747 := bstep (se 1 (by rfl) ⟨1475810, by rfl⟩ : syracuseStep 1967747 = 2951621) B2951621
theorem B1967777 : Blo 1309973 1967777 := bstep (se 2 (by rfl) ⟨737916, by rfl⟩ : syracuseStep 1967777 = 1475833) B1475833
theorem B2098867 : Blo 1309973 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B1967795 : Blo 1309973 1967795 := bstep (se 1 (by rfl) ⟨1475846, by rfl⟩ : syracuseStep 1967795 = 2951693) B2951693
theorem B2950865 : Blo 1309973 2950865 := bstep (se 2 (by rfl) ⟨1106574, by rfl⟩ : syracuseStep 2950865 = 2213149) B2213149
theorem B1967825 : Blo 1309973 1967825 := bstep (se 2 (by rfl) ⟨737934, by rfl⟩ : syracuseStep 1967825 = 1475869) B1475869
theorem B2950883 : Blo 1309973 2950883 := bstep (se 1 (by rfl) ⟨2213162, by rfl⟩ : syracuseStep 2950883 = 4426325) B4426325
theorem B1967843 : Blo 1309973 1967843 := bstep (se 1 (by rfl) ⟨1475882, by rfl⟩ : syracuseStep 1967843 = 2951765) B2951765
theorem B1967873 : Blo 1309973 1967873 := bstep (se 2 (by rfl) ⟨737952, by rfl⟩ : syracuseStep 1967873 = 1475905) B1475905
theorem B2213635 : Blo 1309973 2213635 := bstep (se 1 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 2213635 = 3320453) B3320453
theorem B1967891 : Blo 1309973 1967891 := bstep (se 1 (by rfl) ⟨1475918, by rfl⟩ : syracuseStep 1967891 = 2951837) B2951837
theorem B5318435 : Blo 1309973 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B1967921 : Blo 1309973 1967921 := bstep (se 2 (by rfl) ⟨737970, by rfl⟩ : syracuseStep 1967921 = 1475941) B1475941
theorem B1967939 : Blo 1309973 1967939 := bstep (se 1 (by rfl) ⟨1475954, by rfl⟩ : syracuseStep 1967939 = 2951909) B2951909
theorem B2213777 : Blo 1309973 2213777 := bstep (se 2 (by rfl) ⟨830166, by rfl⟩ : syracuseStep 2213777 = 1660333) B1660333
theorem B2099105 : Blo 1309973 2099105 := bstep (se 2 (by rfl) ⟨787164, by rfl⟩ : syracuseStep 2099105 = 1574329) B1574329
theorem B4425677 : Blo 1309973 4425677 := bstep (se 3 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 4425677 = 1659629) B1659629
theorem B2951153 : Blo 1309973 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B4425731 : Blo 1309973 4425731 := bstep (se 1 (by rfl) ⟨3319298, by rfl⟩ : syracuseStep 4425731 = 6638597) B6638597
theorem B2951171 : Blo 1309973 2951171 := bstep (se 1 (by rfl) ⟨2213378, by rfl⟩ : syracuseStep 2951171 = 4426757) B4426757
theorem B4974605 : Blo 1309973 4974605 := bstep (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) B1865477
theorem B3319825 : Blo 1309973 3319825 := bstep (se 2 (by rfl) ⟨1244934, by rfl⟩ : syracuseStep 3319825 = 2489869) B2489869
theorem B2213905 : Blo 1309973 2213905 := bstep (se 2 (by rfl) ⟨830214, by rfl⟩ : syracuseStep 2213905 = 1660429) B1660429
theorem B2213939 : Blo 1309973 2213939 := bstep (se 1 (by rfl) ⟨1660454, by rfl⟩ : syracuseStep 2213939 = 3320909) B3320909
theorem B2099315 : Blo 1309973 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B1992881 : Blo 1309973 1992881 := bstep (se 2 (by rfl) ⟨747330, by rfl⟩ : syracuseStep 1992881 = 1494661) B1494661
theorem B6817969 : Blo 1309973 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B4426001 : Blo 1309973 4426001 := bstep (se 2 (by rfl) ⟨1659750, by rfl⟩ : syracuseStep 4426001 = 3319501) B3319501
theorem B2951441 : Blo 1309973 2951441 := bstep (se 2 (by rfl) ⟨1106790, by rfl⟩ : syracuseStep 2951441 = 2213581) B2213581
theorem B1771795 : Blo 1309973 1771795 := bstep (se 1 (by rfl) ⟨1328846, by rfl⟩ : syracuseStep 1771795 = 2657693) B2657693
theorem B3320099 : Blo 1309973 3320099 := bstep (se 1 (by rfl) ⟨2490074, by rfl⟩ : syracuseStep 3320099 = 4980149) B4980149
theorem B2951459 : Blo 1309973 2951459 := bstep (se 1 (by rfl) ⟨2213594, by rfl⟩ : syracuseStep 2951459 = 4427189) B4427189
theorem B6064433 : Blo 1309973 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B4196785 : Blo 1309973 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B3320291 : Blo 1309973 3320291 := bstep (se 1 (by rfl) ⟨2490218, by rfl⟩ : syracuseStep 3320291 = 4980437) B4980437
theorem B2951729 : Blo 1309973 2951729 := bstep (se 2 (by rfl) ⟨1106898, by rfl⟩ : syracuseStep 2951729 = 2213797) B2213797
theorem B2951747 : Blo 1309973 2951747 := bstep (se 1 (by rfl) ⟨2213810, by rfl⟩ : syracuseStep 2951747 = 4427621) B4427621
theorem B2361955 : Blo 1309973 2361955 := bstep (se 1 (by rfl) ⟨1771466, by rfl⟩ : syracuseStep 2361955 = 3542933) B3542933
theorem B1772131 : Blo 1309973 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B2157281 : Blo 1309973 2157281 := bstep (se 2 (by rfl) ⟨808980, by rfl⟩ : syracuseStep 2157281 = 1617961) B1617961
theorem B4426541 : Blo 1309973 4426541 := bstep (se 3 (by rfl) ⟨829976, by rfl⟩ : syracuseStep 4426541 = 1659953) B1659953
theorem B1400851 : Blo 1309973 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B9956195 : Blo 1309973 9956195 := bstep (se 1 (by rfl) ⟨7467146, by rfl⟩ : syracuseStep 9956195 = 14934293) B14934293
theorem B6638435 : Blo 1309973 6638435 := bstep (se 1 (by rfl) ⟨4978826, by rfl⟩ : syracuseStep 6638435 = 9957653) B9957653
theorem B4426595 : Blo 1309973 4426595 := bstep (se 1 (by rfl) ⟨3319946, by rfl⟩ : syracuseStep 4426595 = 6639893) B6639893
theorem B2100097 : Blo 1309973 2100097 := bstep (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) B1575073
theorem B2362243 : Blo 1309973 2362243 := bstep (se 1 (by rfl) ⟨1771682, by rfl⟩ : syracuseStep 2362243 = 3543365) B3543365
theorem B1682371 : Blo 1309973 1682371 := bstep (se 1 (by rfl) ⟨1261778, by rfl⟩ : syracuseStep 1682371 = 2523557) B2523557
theorem B6384653 : Blo 1309973 6384653 := bstep (se 3 (by rfl) ⟨1197122, by rfl⟩ : syracuseStep 6384653 = 2394245) B2394245
theorem B47803445 : Blo 1309973 47803445 := bstep (se 5 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 47803445 = 4481573) B4481573
theorem B3730499 : Blo 1309973 3730499 := bstep (se 1 (by rfl) ⟨2797874, by rfl⟩ : syracuseStep 3730499 = 5595749) B5595749
theorem B7466053 : Blo 1309973 7466053 := bstep (se 4 (by rfl) ⟨699942, by rfl⟩ : syracuseStep 7466053 = 1399885) B1399885
theorem B4426865 : Blo 1309973 4426865 := bstep (se 2 (by rfl) ⟨1660074, by rfl⟩ : syracuseStep 4426865 = 3320149) B3320149
theorem B2837713 : Blo 1309973 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B1658227 : Blo 1309973 1658227 := bstep (se 1 (by rfl) ⟨1243670, by rfl⟩ : syracuseStep 1658227 = 2487341) B2487341
theorem B1658323 : Blo 1309973 1658323 := bstep (se 1 (by rfl) ⟨1243742, by rfl⟩ : syracuseStep 1658323 = 2487485) B2487485
theorem B4197901 : Blo 1309973 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B2461283 : Blo 1309973 2461283 := bstep (se 1 (by rfl) ⟨1845962, by rfl⟩ : syracuseStep 2461283 = 3691925) B3691925
theorem B6639245 : Blo 1309973 6639245 := bstep (se 3 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 6639245 = 2489717) B2489717
theorem B4427405 : Blo 1309973 4427405 := bstep (se 3 (by rfl) ⟨830138, by rfl⟩ : syracuseStep 4427405 = 1660277) B1660277
theorem B2100899 : Blo 1309973 2100899 := bstep (se 1 (by rfl) ⟨1575674, by rfl⟩ : syracuseStep 2100899 = 3151349) B3151349
theorem B4484803 : Blo 1309973 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B4427459 : Blo 1309973 4427459 := bstep (se 1 (by rfl) ⟨3320594, by rfl⟩ : syracuseStep 4427459 = 6641189) B6641189
theorem B7089905 : Blo 1309973 7089905 := bstep (se 2 (by rfl) ⟨2658714, by rfl⟩ : syracuseStep 7089905 = 5317429) B5317429
theorem B4484899 : Blo 1309973 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B3731341 : Blo 1309973 3731341 := bstep (se 3 (by rfl) ⟨699626, by rfl⟩ : syracuseStep 3731341 = 1399253) B1399253
theorem B3190691 : Blo 1309973 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B1658819 : Blo 1309973 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B4427729 : Blo 1309973 4427729 := bstep (se 2 (by rfl) ⟨1660398, by rfl⟩ : syracuseStep 4427729 = 3320797) B3320797
theorem B3731501 : Blo 1309973 3731501 := bstep (se 3 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 3731501 = 1399313) B1399313
theorem B8966213 : Blo 1309973 8966213 := bstep (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) B1681165
theorem B16806001 : Blo 1309973 16806001 := bstep (se 2 (by rfl) ⟨6302250, by rfl⟩ : syracuseStep 16806001 = 12604501) B12604501
theorem B2101411 : Blo 1309973 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B3731683 : Blo 1309973 3731683 := bstep (se 1 (by rfl) ⟨2798762, by rfl⟩ : syracuseStep 3731683 = 5597525) B5597525
theorem B8401157 : Blo 1309973 8401157 := bstep (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) B1575217
theorem B4198733 : Blo 1309973 4198733 := bstep (se 3 (by rfl) ⟨787262, by rfl⟩ : syracuseStep 4198733 = 1574525) B1574525
theorem B3543373 : Blo 1309973 3543373 := bstep (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) B1328765
theorem B6631793 : Blo 1309973 6631793 := bstep (se 2 (by rfl) ⟨2486922, by rfl⟩ : syracuseStep 6631793 = 4973845) B4973845
theorem B15340085 : Blo 1309973 15340085 := bstep (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) B1438133
theorem B10629731 : Blo 1309973 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B1659523 : Blo 1309973 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B57447139 : Blo 1309973 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B1659619 : Blo 1309973 1659619 := bstep (se 1 (by rfl) ⟨1244714, by rfl⟩ : syracuseStep 1659619 = 2489429) B2489429
theorem B4977521 : Blo 1309973 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B3593123 : Blo 1309973 3593123 := bstep (se 1 (by rfl) ⟨2694842, by rfl⟩ : syracuseStep 3593123 = 5389685) B5389685
theorem B7468037 : Blo 1309973 7468037 := bstep (se 4 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 7468037 = 1400257) B1400257
theorem B8393827 : Blo 1309973 8393827 := bstep (se 1 (by rfl) ⟨6295370, by rfl⟩ : syracuseStep 8393827 = 12590741) B12590741
theorem B7091333 : Blo 1309973 7091333 := bstep (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) B1329625
theorem B1660115 : Blo 1309973 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B2487523 : Blo 1309973 2487523 := bstep (se 1 (by rfl) ⟨1865642, by rfl⟩ : syracuseStep 2487523 = 3731285) B3731285
theorem B5600497 : Blo 1309973 5600497 := bstep (se 2 (by rfl) ⟨2100186, by rfl⟩ : syracuseStep 5600497 = 4200373) B4200373
theorem B1774867 : Blo 1309973 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B7968113 : Blo 1309973 7968113 := bstep (se 2 (by rfl) ⟨2988042, by rfl⟩ : syracuseStep 7968113 = 5976085) B5976085
theorem B25204081 : Blo 1309973 25204081 := bstep (se 2 (by rfl) ⟨9451530, by rfl⟩ : syracuseStep 25204081 = 18903061) B18903061
theorem B2799011 : Blo 1309973 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B157406773 : Blo 1309973 157406773 := bstep (se 5 (by rfl) ⟨7378442, by rfl⟩ : syracuseStep 157406773 = 14756885) B14756885
theorem B3733073 : Blo 1309973 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B2487971 : Blo 1309973 2487971 := bstep (se 1 (by rfl) ⟨1865978, by rfl⟩ : syracuseStep 2487971 = 3731957) B3731957
theorem B1865443 : Blo 1309973 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B4421357 : Blo 1309973 4421357 := bstep (se 3 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 4421357 = 1658009) B1658009
theorem B7091981 : Blo 1309973 7091981 := bstep (se 3 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 7091981 = 2659493) B2659493
theorem B4421411 : Blo 1309973 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B6633251 : Blo 1309973 6633251 := bstep (se 1 (by rfl) ⟨4974938, by rfl⟩ : syracuseStep 6633251 = 9949877) B9949877
theorem B3545009 : Blo 1309973 3545009 := bstep (se 2 (by rfl) ⟨1329378, by rfl⟩ : syracuseStep 3545009 = 2658757) B2658757
theorem B2488259 : Blo 1309973 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B50427845 : Blo 1309973 50427845 := bstep (se 4 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 50427845 = 9455221) B9455221
theorem B12777485 : Blo 1309973 12777485 := bstep (se 3 (by rfl) ⟨2395778, by rfl⟩ : syracuseStep 12777485 = 4791557) B4791557
theorem B4421681 : Blo 1309973 4421681 := bstep (se 2 (by rfl) ⟨1658130, by rfl⟩ : syracuseStep 4421681 = 3316261) B3316261
theorem B60512309 : Blo 1309973 60512309 := bstep (se 5 (by rfl) ⟨2836514, by rfl⟩ : syracuseStep 60512309 = 5673029) B5673029
theorem B20183093 : Blo 1309973 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B5314673 : Blo 1309973 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B1865921 : Blo 1309973 1865921 := bstep (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) B1399441
theorem B5314787 : Blo 1309973 5314787 := bstep (se 1 (by rfl) ⟨3986090, by rfl⟩ : syracuseStep 5314787 = 7972181) B7972181
theorem B1399027 : Blo 1309973 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B4978979 : Blo 1309973 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1866035 : Blo 1309973 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B3316049 : Blo 1309973 3316049 := bstep (se 2 (by rfl) ⟨1243518, by rfl⟩ : syracuseStep 3316049 = 2487037) B2487037
theorem B3316099 : Blo 1309973 3316099 := bstep (se 1 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 3316099 = 4974149) B4974149
theorem B1866115 : Blo 1309973 1866115 := bstep (se 1 (by rfl) ⟨1399586, by rfl⟩ : syracuseStep 1866115 = 2799173) B2799173
theorem B4200835 : Blo 1309973 4200835 := bstep (se 1 (by rfl) ⟨3150626, by rfl⟩ : syracuseStep 4200835 = 6301253) B6301253
theorem B17258993 : Blo 1309973 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B3734029 : Blo 1309973 3734029 := bstep (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) B1400261
theorem B3316241 : Blo 1309973 3316241 := bstep (se 2 (by rfl) ⟨1243590, by rfl⟩ : syracuseStep 3316241 = 2487181) B2487181
theorem B4200977 : Blo 1309973 4200977 := bstep (se 2 (by rfl) ⟨1575366, by rfl⟩ : syracuseStep 4200977 = 3150733) B3150733
theorem B95648309 : Blo 1309973 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B45439541 : Blo 1309973 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B4422221 : Blo 1309973 4422221 := bstep (se 3 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 4422221 = 1658333) B1658333
theorem B6634061 : Blo 1309973 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B2947697 : Blo 1309973 2947697 := bstep (se 2 (by rfl) ⟨1105386, by rfl⟩ : syracuseStep 2947697 = 2210773) B2210773
theorem B2800241 : Blo 1309973 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2947715 : Blo 1309973 2947715 := bstep (se 1 (by rfl) ⟨2210786, by rfl⟩ : syracuseStep 2947715 = 4421573) B4421573
theorem B4422275 : Blo 1309973 4422275 := bstep (se 1 (by rfl) ⟨3316706, by rfl⟩ : syracuseStep 4422275 = 6633413) B6633413
theorem B6298253 : Blo 1309973 6298253 := bstep (se 3 (by rfl) ⟨1180922, by rfl⟩ : syracuseStep 6298253 = 2361845) B2361845
theorem B1399475 : Blo 1309973 1399475 := bstep (se 1 (by rfl) ⟨1049606, by rfl⟩ : syracuseStep 1399475 = 2099213) B2099213
theorem B3734257 : Blo 1309973 3734257 := bstep (se 2 (by rfl) ⟨1400346, by rfl⟩ : syracuseStep 3734257 = 2800693) B2800693
theorem B2210611 : Blo 1309973 2210611 := bstep (se 1 (by rfl) ⟨1657958, by rfl⟩ : syracuseStep 2210611 = 3315917) B3315917
theorem B14932835 : Blo 1309973 14932835 := bstep (se 1 (by rfl) ⟨11199626, by rfl⟩ : syracuseStep 14932835 = 22399253) B22399253
theorem B2489201 : Blo 1309973 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B2947985 : Blo 1309973 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B4422545 : Blo 1309973 4422545 := bstep (se 2 (by rfl) ⟨1658454, by rfl⟩ : syracuseStep 4422545 = 3316909) B3316909
theorem B3734417 : Blo 1309973 3734417 := bstep (se 2 (by rfl) ⟨1400406, by rfl⟩ : syracuseStep 3734417 = 2800813) B2800813
theorem B1964963 : Blo 1309973 1964963 := bstep (se 1 (by rfl) ⟨1473722, by rfl⟩ : syracuseStep 1964963 = 2947445) B2947445
theorem B2948003 : Blo 1309973 2948003 := bstep (se 1 (by rfl) ⟨2211002, by rfl⟩ : syracuseStep 2948003 = 4422005) B4422005
theorem B1866673 : Blo 1309973 1866673 := bstep (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) B1400005
theorem B1964993 : Blo 1309973 1964993 := bstep (se 2 (by rfl) ⟨736872, by rfl⟩ : syracuseStep 1964993 = 1473745) B1473745
theorem B2210753 : Blo 1309973 2210753 := bstep (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) B1658065
theorem B1965011 : Blo 1309973 1965011 := bstep (se 1 (by rfl) ⟨1473758, by rfl⟩ : syracuseStep 1965011 = 2947517) B2947517
theorem B1965041 : Blo 1309973 1965041 := bstep (se 2 (by rfl) ⟨736890, by rfl⟩ : syracuseStep 1965041 = 1473781) B1473781
theorem B1965059 : Blo 1309973 1965059 := bstep (se 1 (by rfl) ⟨1473794, by rfl⟩ : syracuseStep 1965059 = 2947589) B2947589
theorem B3734531 : Blo 1309973 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B8969221 : Blo 1309973 8969221 := bstep (se 4 (by rfl) ⟨840864, by rfl⟩ : syracuseStep 8969221 = 1681729) B1681729
theorem B1965089 : Blo 1309973 1965089 := bstep (se 2 (by rfl) ⟨736908, by rfl⟩ : syracuseStep 1965089 = 1473817) B1473817
theorem B8395825 : Blo 1309973 8395825 := bstep (se 2 (by rfl) ⟨3148434, by rfl⟩ : syracuseStep 8395825 = 6296869) B6296869
theorem B1965107 : Blo 1309973 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B2210881 : Blo 1309973 2210881 := bstep (se 2 (by rfl) ⟨829080, by rfl⟩ : syracuseStep 2210881 = 1658161) B1658161
theorem B1965137 : Blo 1309973 1965137 := bstep (se 2 (by rfl) ⟨736926, by rfl⟩ : syracuseStep 1965137 = 1473853) B1473853
theorem B1965155 : Blo 1309973 1965155 := bstep (se 1 (by rfl) ⟨1473866, by rfl⟩ : syracuseStep 1965155 = 2947733) B2947733
theorem B2210915 : Blo 1309973 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B28335217 : Blo 1309973 28335217 := bstep (se 2 (by rfl) ⟨10625706, by rfl⟩ : syracuseStep 28335217 = 21251413) B21251413
theorem B1965185 : Blo 1309973 1965185 := bstep (se 2 (by rfl) ⟨736944, by rfl⟩ : syracuseStep 1965185 = 1473889) B1473889
theorem B1965203 : Blo 1309973 1965203 := bstep (se 1 (by rfl) ⟨1473902, by rfl⟩ : syracuseStep 1965203 = 2947805) B2947805
theorem B1965233 : Blo 1309973 1965233 := bstep (se 2 (by rfl) ⟨736962, by rfl⟩ : syracuseStep 1965233 = 1473925) B1473925
theorem B2948273 : Blo 1309973 2948273 := bstep (se 2 (by rfl) ⟨1105602, by rfl⟩ : syracuseStep 2948273 = 2211205) B2211205
theorem B1965251 : Blo 1309973 1965251 := bstep (se 1 (by rfl) ⟨1473938, by rfl⟩ : syracuseStep 1965251 = 2947877) B2947877
theorem B2948291 : Blo 1309973 2948291 := bstep (se 1 (by rfl) ⟨2211218, by rfl⟩ : syracuseStep 2948291 = 4422437) B4422437
theorem B1965281 : Blo 1309973 1965281 := bstep (se 2 (by rfl) ⟨736980, by rfl⟩ : syracuseStep 1965281 = 1473961) B1473961
theorem B1473763 : Blo 1309973 1473763 := bstep (se 1 (by rfl) ⟨1105322, by rfl⟩ : syracuseStep 1473763 = 2210645) B2210645
theorem B2211043 : Blo 1309973 2211043 := bstep (se 1 (by rfl) ⟨1658282, by rfl⟩ : syracuseStep 2211043 = 3316565) B3316565
theorem B1965299 : Blo 1309973 1965299 := bstep (se 1 (by rfl) ⟨1473974, by rfl⟩ : syracuseStep 1965299 = 2947949) B2947949
theorem B4979981 : Blo 1309973 4979981 := bstep (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) B1867493
theorem B1965329 : Blo 1309973 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B1309987 : Blo 1309973 1309987 := bstep (se 1 (by rfl) ⟨982490, by rfl⟩ : syracuseStep 1309987 = 1964981) B1964981
theorem B1965347 : Blo 1309973 1965347 := bstep (se 1 (by rfl) ⟨1474010, by rfl⟩ : syracuseStep 1965347 = 2948021) B2948021
theorem B1310003 : Blo 1309973 1310003 := bstep (se 1 (by rfl) ⟨982502, by rfl⟩ : syracuseStep 1310003 = 1965005) B1965005
theorem B1965377 : Blo 1309973 1965377 := bstep (se 2 (by rfl) ⟨737016, by rfl⟩ : syracuseStep 1965377 = 1474033) B1474033
theorem B1310019 : Blo 1309973 1310019 := bstep (se 1 (by rfl) ⟨982514, by rfl⟩ : syracuseStep 1310019 = 1965029) B1965029
theorem B1310035 : Blo 1309973 1310035 := bstep (se 1 (by rfl) ⟨982526, by rfl⟩ : syracuseStep 1310035 = 1965053) B1965053
theorem B1965395 : Blo 1309973 1965395 := bstep (se 1 (by rfl) ⟨1474046, by rfl⟩ : syracuseStep 1965395 = 2948093) B2948093
theorem B1310051 : Blo 1309973 1310051 := bstep (se 1 (by rfl) ⟨982538, by rfl⟩ : syracuseStep 1310051 = 1965077) B1965077
theorem B1965425 : Blo 1309973 1965425 := bstep (se 2 (by rfl) ⟨737034, by rfl⟩ : syracuseStep 1965425 = 1474069) B1474069
theorem B2211185 : Blo 1309973 2211185 := bstep (se 2 (by rfl) ⟨829194, by rfl⟩ : syracuseStep 2211185 = 1658389) B1658389
theorem B1310067 : Blo 1309973 1310067 := bstep (se 1 (by rfl) ⟨982550, by rfl⟩ : syracuseStep 1310067 = 1965101) B1965101
theorem B1473907 : Blo 1309973 1473907 := bstep (se 1 (by rfl) ⟨1105430, by rfl⟩ : syracuseStep 1473907 = 2210861) B2210861
theorem B1310083 : Blo 1309973 1310083 := bstep (se 1 (by rfl) ⟨982562, by rfl⟩ : syracuseStep 1310083 = 1965125) B1965125
theorem B1965443 : Blo 1309973 1965443 := bstep (se 1 (by rfl) ⟨1474082, by rfl⟩ : syracuseStep 1965443 = 2948165) B2948165
theorem B1310099 : Blo 1309973 1310099 := bstep (se 1 (by rfl) ⟨982574, by rfl⟩ : syracuseStep 1310099 = 1965149) B1965149
theorem B1965473 : Blo 1309973 1965473 := bstep (se 2 (by rfl) ⟨737052, by rfl⟩ : syracuseStep 1965473 = 1474105) B1474105
theorem B1310115 : Blo 1309973 1310115 := bstep (se 1 (by rfl) ⟨982586, by rfl⟩ : syracuseStep 1310115 = 1965173) B1965173
theorem B4423085 : Blo 1309973 4423085 := bstep (se 3 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 4423085 = 1658657) B1658657
theorem B1310131 : Blo 1309973 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B1965491 : Blo 1309973 1965491 := bstep (se 1 (by rfl) ⟨1474118, by rfl⟩ : syracuseStep 1965491 = 2948237) B2948237
theorem B1310147 : Blo 1309973 1310147 := bstep (se 1 (by rfl) ⟨982610, by rfl⟩ : syracuseStep 1310147 = 1965221) B1965221
theorem B1965521 : Blo 1309973 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B2948561 : Blo 1309973 2948561 := bstep (se 2 (by rfl) ⟨1105710, by rfl⟩ : syracuseStep 2948561 = 2211421) B2211421
theorem B1310163 : Blo 1309973 1310163 := bstep (se 1 (by rfl) ⟨982622, by rfl⟩ : syracuseStep 1310163 = 1965245) B1965245
theorem B1310179 : Blo 1309973 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B1965539 : Blo 1309973 1965539 := bstep (se 1 (by rfl) ⟨1474154, by rfl⟩ : syracuseStep 1965539 = 2948309) B2948309
theorem B2948579 : Blo 1309973 2948579 := bstep (se 1 (by rfl) ⟨2211434, by rfl⟩ : syracuseStep 2948579 = 4422869) B4422869
theorem B4423139 : Blo 1309973 4423139 := bstep (se 1 (by rfl) ⟨3317354, by rfl⟩ : syracuseStep 4423139 = 6634709) B6634709
theorem B28753379 : Blo 1309973 28753379 := bstep (se 1 (by rfl) ⟨21565034, by rfl⟩ : syracuseStep 28753379 = 43130069) B43130069
theorem B2211313 : Blo 1309973 2211313 := bstep (se 2 (by rfl) ⟨829242, by rfl⟩ : syracuseStep 2211313 = 1658485) B1658485
theorem B1310195 : Blo 1309973 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B3317233 : Blo 1309973 3317233 := bstep (se 2 (by rfl) ⟨1243962, by rfl⟩ : syracuseStep 3317233 = 2487925) B2487925
theorem B2801137 : Blo 1309973 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B1965569 : Blo 1309973 1965569 := bstep (se 2 (by rfl) ⟨737088, by rfl⟩ : syracuseStep 1965569 = 1474177) B1474177
theorem B1310211 : Blo 1309973 1310211 := bstep (se 1 (by rfl) ⟨982658, by rfl⟩ : syracuseStep 1310211 = 1965317) B1965317
theorem B1474051 : Blo 1309973 1474051 := bstep (se 1 (by rfl) ⟨1105538, by rfl⟩ : syracuseStep 1474051 = 2211077) B2211077
theorem B2801155 : Blo 1309973 2801155 := bstep (se 1 (by rfl) ⟨2100866, by rfl⟩ : syracuseStep 2801155 = 4201733) B4201733
theorem B3989009 : Blo 1309973 3989009 := bstep (se 2 (by rfl) ⟨1495878, by rfl⟩ : syracuseStep 3989009 = 2991757) B2991757
theorem B1310227 : Blo 1309973 1310227 := bstep (se 1 (by rfl) ⟨982670, by rfl⟩ : syracuseStep 1310227 = 1965341) B1965341
theorem B1965587 : Blo 1309973 1965587 := bstep (se 1 (by rfl) ⟨1474190, by rfl⟩ : syracuseStep 1965587 = 2948381) B2948381
theorem B2211347 : Blo 1309973 2211347 := bstep (se 1 (by rfl) ⟨1658510, by rfl⟩ : syracuseStep 2211347 = 3317021) B3317021
theorem B1310243 : Blo 1309973 1310243 := bstep (se 1 (by rfl) ⟨982682, by rfl⟩ : syracuseStep 1310243 = 1965365) B1965365
theorem B1965617 : Blo 1309973 1965617 := bstep (se 2 (by rfl) ⟨737106, by rfl⟩ : syracuseStep 1965617 = 1474213) B1474213
theorem B1310259 : Blo 1309973 1310259 := bstep (se 1 (by rfl) ⟨982694, by rfl⟩ : syracuseStep 1310259 = 1965389) B1965389
theorem B1310275 : Blo 1309973 1310275 := bstep (se 1 (by rfl) ⟨982706, by rfl⟩ : syracuseStep 1310275 = 1965413) B1965413
theorem B1965635 : Blo 1309973 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B1310291 : Blo 1309973 1310291 := bstep (se 1 (by rfl) ⟨982718, by rfl⟩ : syracuseStep 1310291 = 1965437) B1965437
theorem B1965665 : Blo 1309973 1965665 := bstep (se 2 (by rfl) ⟨737124, by rfl⟩ : syracuseStep 1965665 = 1474249) B1474249
theorem B1310307 : Blo 1309973 1310307 := bstep (se 1 (by rfl) ⟨982730, by rfl⟩ : syracuseStep 1310307 = 1965461) B1965461
theorem B1310323 : Blo 1309973 1310323 := bstep (se 1 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 1310323 = 1965485) B1965485
theorem B1965683 : Blo 1309973 1965683 := bstep (se 1 (by rfl) ⟨1474262, by rfl⟩ : syracuseStep 1965683 = 2948525) B2948525
theorem B1867379 : Blo 1309973 1867379 := bstep (se 1 (by rfl) ⟨1400534, by rfl⟩ : syracuseStep 1867379 = 2801069) B2801069
theorem B1310339 : Blo 1309973 1310339 := bstep (se 1 (by rfl) ⟨982754, by rfl⟩ : syracuseStep 1310339 = 1965509) B1965509
theorem B10632845 : Blo 1309973 10632845 := bstep (se 3 (by rfl) ⟨1993658, by rfl⟩ : syracuseStep 10632845 = 3987317) B3987317
theorem B1965713 : Blo 1309973 1965713 := bstep (se 2 (by rfl) ⟨737142, by rfl⟩ : syracuseStep 1965713 = 1474285) B1474285
theorem B1310355 : Blo 1309973 1310355 := bstep (se 1 (by rfl) ⟨982766, by rfl⟩ : syracuseStep 1310355 = 1965533) B1965533
theorem B1474195 : Blo 1309973 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B2211475 : Blo 1309973 2211475 := bstep (se 1 (by rfl) ⟨1658606, by rfl⟩ : syracuseStep 2211475 = 3317213) B3317213
theorem B1310371 : Blo 1309973 1310371 := bstep (se 1 (by rfl) ⟨982778, by rfl⟩ : syracuseStep 1310371 = 1965557) B1965557
theorem B1965731 : Blo 1309973 1965731 := bstep (se 1 (by rfl) ⟨1474298, by rfl⟩ : syracuseStep 1965731 = 2948597) B2948597
theorem B1310387 : Blo 1309973 1310387 := bstep (se 1 (by rfl) ⟨982790, by rfl⟩ : syracuseStep 1310387 = 1965581) B1965581
theorem B1965761 : Blo 1309973 1965761 := bstep (se 2 (by rfl) ⟨737160, by rfl⟩ : syracuseStep 1965761 = 1474321) B1474321
theorem B1310403 : Blo 1309973 1310403 := bstep (se 1 (by rfl) ⟨982802, by rfl⟩ : syracuseStep 1310403 = 1965605) B1965605
theorem B2522819 : Blo 1309973 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B1310419 : Blo 1309973 1310419 := bstep (se 1 (by rfl) ⟨982814, by rfl⟩ : syracuseStep 1310419 = 1965629) B1965629
theorem B1965779 : Blo 1309973 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B1310435 : Blo 1309973 1310435 := bstep (se 1 (by rfl) ⟨982826, by rfl⟩ : syracuseStep 1310435 = 1965653) B1965653
theorem B4423409 : Blo 1309973 4423409 := bstep (se 2 (by rfl) ⟨1658778, by rfl⟩ : syracuseStep 4423409 = 3317557) B3317557
theorem B1310451 : Blo 1309973 1310451 := bstep (se 1 (by rfl) ⟨982838, by rfl⟩ : syracuseStep 1310451 = 1965677) B1965677
theorem B1965809 : Blo 1309973 1965809 := bstep (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) B1474357
theorem B2948849 : Blo 1309973 2948849 := bstep (se 2 (by rfl) ⟨1105818, by rfl⟩ : syracuseStep 2948849 = 2211637) B2211637
theorem B2490097 : Blo 1309973 2490097 := bstep (se 2 (by rfl) ⟨933786, by rfl⟩ : syracuseStep 2490097 = 1867573) B1867573
theorem B1310467 : Blo 1309973 1310467 := bstep (se 1 (by rfl) ⟨982850, by rfl⟩ : syracuseStep 1310467 = 1965701) B1965701
theorem B1965827 : Blo 1309973 1965827 := bstep (se 1 (by rfl) ⟨1474370, by rfl⟩ : syracuseStep 1965827 = 2948741) B2948741
theorem B2948867 : Blo 1309973 2948867 := bstep (se 1 (by rfl) ⟨2211650, by rfl⟩ : syracuseStep 2948867 = 4423301) B4423301
theorem B3317507 : Blo 1309973 3317507 := bstep (se 1 (by rfl) ⟨2488130, by rfl⟩ : syracuseStep 3317507 = 4976261) B4976261
theorem B1310483 : Blo 1309973 1310483 := bstep (se 1 (by rfl) ⟨982862, by rfl⟩ : syracuseStep 1310483 = 1965725) B1965725
theorem B64659221 : Blo 1309973 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B2211617 : Blo 1309973 2211617 := bstep (se 2 (by rfl) ⟨829356, by rfl⟩ : syracuseStep 2211617 = 1658713) B1658713
theorem B1310499 : Blo 1309973 1310499 := bstep (se 1 (by rfl) ⟨982874, by rfl⟩ : syracuseStep 1310499 = 1965749) B1965749
theorem B1474339 : Blo 1309973 1474339 := bstep (se 1 (by rfl) ⟨1105754, by rfl⟩ : syracuseStep 1474339 = 2211509) B2211509
theorem B1965857 : Blo 1309973 1965857 := bstep (se 2 (by rfl) ⟨737196, by rfl⟩ : syracuseStep 1965857 = 1474393) B1474393
theorem B1310515 : Blo 1309973 1310515 := bstep (se 1 (by rfl) ⟨982886, by rfl⟩ : syracuseStep 1310515 = 1965773) B1965773
theorem B1965875 : Blo 1309973 1965875 := bstep (se 1 (by rfl) ⟨1474406, by rfl⟩ : syracuseStep 1965875 = 2948813) B2948813
theorem B1310531 : Blo 1309973 1310531 := bstep (se 1 (by rfl) ⟨982898, by rfl⟩ : syracuseStep 1310531 = 1965797) B1965797
theorem B1965905 : Blo 1309973 1965905 := bstep (se 2 (by rfl) ⟨737214, by rfl⟩ : syracuseStep 1965905 = 1474429) B1474429
theorem B1310547 : Blo 1309973 1310547 := bstep (se 1 (by rfl) ⟨982910, by rfl⟩ : syracuseStep 1310547 = 1965821) B1965821
theorem B1310563 : Blo 1309973 1310563 := bstep (se 1 (by rfl) ⟨982922, by rfl⟩ : syracuseStep 1310563 = 1965845) B1965845
theorem B1965923 : Blo 1309973 1965923 := bstep (se 1 (by rfl) ⟨1474442, by rfl⟩ : syracuseStep 1965923 = 2948885) B2948885
theorem B1310579 : Blo 1309973 1310579 := bstep (se 1 (by rfl) ⟨982934, by rfl⟩ : syracuseStep 1310579 = 1965869) B1965869
theorem B1965953 : Blo 1309973 1965953 := bstep (se 2 (by rfl) ⟨737232, by rfl⟩ : syracuseStep 1965953 = 1474465) B1474465
theorem B1310595 : Blo 1309973 1310595 := bstep (se 1 (by rfl) ⟨982946, by rfl⟩ : syracuseStep 1310595 = 1965893) B1965893
theorem B2490257 : Blo 1309973 2490257 := bstep (se 2 (by rfl) ⟨933846, by rfl⟩ : syracuseStep 2490257 = 1867693) B1867693
theorem B1310611 : Blo 1309973 1310611 := bstep (se 1 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 1310611 = 1965917) B1965917
theorem B1965971 : Blo 1309973 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B2211745 : Blo 1309973 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B8077219 : Blo 1309973 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B1310627 : Blo 1309973 1310627 := bstep (se 1 (by rfl) ⟨982970, by rfl⟩ : syracuseStep 1310627 = 1965941) B1965941
theorem B1966001 : Blo 1309973 1966001 := bstep (se 2 (by rfl) ⟨737250, by rfl⟩ : syracuseStep 1966001 = 1474501) B1474501
theorem B1310643 : Blo 1309973 1310643 := bstep (se 1 (by rfl) ⟨982982, by rfl⟩ : syracuseStep 1310643 = 1965965) B1965965
theorem B1474483 : Blo 1309973 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B3317699 : Blo 1309973 3317699 := bstep (se 1 (by rfl) ⟨2488274, by rfl⟩ : syracuseStep 3317699 = 4976549) B4976549
theorem B1310659 : Blo 1309973 1310659 := bstep (se 1 (by rfl) ⟨982994, by rfl⟩ : syracuseStep 1310659 = 1965989) B1965989
theorem B1966019 : Blo 1309973 1966019 := bstep (se 1 (by rfl) ⟨1474514, by rfl⟩ : syracuseStep 1966019 = 2949029) B2949029
theorem B2211779 : Blo 1309973 2211779 := bstep (se 1 (by rfl) ⟨1658834, by rfl⟩ : syracuseStep 2211779 = 3317669) B3317669
theorem B1310675 : Blo 1309973 1310675 := bstep (se 1 (by rfl) ⟨983006, by rfl⟩ : syracuseStep 1310675 = 1966013) B1966013
theorem B1966049 : Blo 1309973 1966049 := bstep (se 2 (by rfl) ⟨737268, by rfl⟩ : syracuseStep 1966049 = 1474537) B1474537
theorem B1310691 : Blo 1309973 1310691 := bstep (se 1 (by rfl) ⟨983018, by rfl⟩ : syracuseStep 1310691 = 1966037) B1966037
theorem B3735533 : Blo 1309973 3735533 := bstep (se 3 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 3735533 = 1400825) B1400825
theorem B1310707 : Blo 1309973 1310707 := bstep (se 1 (by rfl) ⟨983030, by rfl⟩ : syracuseStep 1310707 = 1966061) B1966061
theorem B1966067 : Blo 1309973 1966067 := bstep (se 1 (by rfl) ⟨1474550, by rfl⟩ : syracuseStep 1966067 = 2949101) B2949101
theorem B1966091 : Blo 1309973 1966091 := bstep (se 1 (by rfl) ⟨1474568, by rfl⟩ : syracuseStep 1966091 = 2949137) B2949137
theorem B1310731 : Blo 1309973 1310731 := bstep (se 1 (by rfl) ⟨983048, by rfl⟩ : syracuseStep 1310731 = 1966097) B1966097
theorem B1966103 : Blo 1309973 1966103 := bstep (se 1 (by rfl) ⟨1474577, by rfl⟩ : syracuseStep 1966103 = 2949155) B2949155
theorem B1310743 : Blo 1309973 1310743 := bstep (se 1 (by rfl) ⟨983057, by rfl⟩ : syracuseStep 1310743 = 1966115) B1966115
theorem B1867801 : Blo 1309973 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B1310763 : Blo 1309973 1310763 := bstep (se 1 (by rfl) ⟨983072, by rfl⟩ : syracuseStep 1310763 = 1966145) B1966145
theorem B1310775 : Blo 1309973 1310775 := bstep (se 1 (by rfl) ⟨983081, by rfl⟩ : syracuseStep 1310775 = 1966163) B1966163
theorem B1310795 : Blo 1309973 1310795 := bstep (se 1 (by rfl) ⟨983096, by rfl⟩ : syracuseStep 1310795 = 1966193) B1966193
theorem B1310807 : Blo 1309973 1310807 := bstep (se 1 (by rfl) ⟨983105, by rfl⟩ : syracuseStep 1310807 = 1966211) B1966211
theorem B2949209 : Blo 1309973 2949209 := bstep (se 2 (by rfl) ⟨1105953, by rfl⟩ : syracuseStep 2949209 = 2211907) B2211907
theorem B1966169 : Blo 1309973 1966169 := bstep (se 2 (by rfl) ⟨737313, by rfl⟩ : syracuseStep 1966169 = 1474627) B1474627
theorem B1310827 : Blo 1309973 1310827 := bstep (se 1 (by rfl) ⟨983120, by rfl⟩ : syracuseStep 1310827 = 1966241) B1966241
theorem B1310839 : Blo 1309973 1310839 := bstep (se 1 (by rfl) ⟨983129, by rfl⟩ : syracuseStep 1310839 = 1966259) B1966259
theorem B1474699 : Blo 1309973 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B1310859 : Blo 1309973 1310859 := bstep (se 1 (by rfl) ⟨983144, by rfl⟩ : syracuseStep 1310859 = 1966289) B1966289
theorem B1310871 : Blo 1309973 1310871 := bstep (se 1 (by rfl) ⟨983153, by rfl⟩ : syracuseStep 1310871 = 1966307) B1966307
theorem B1310891 : Blo 1309973 1310891 := bstep (se 1 (by rfl) ⟨983168, by rfl⟩ : syracuseStep 1310891 = 1966337) B1966337
theorem B2949299 : Blo 1309973 2949299 := bstep (se 1 (by rfl) ⟨2211974, by rfl⟩ : syracuseStep 2949299 = 4423949) B4423949
theorem B1310903 : Blo 1309973 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1966283 : Blo 1309973 1966283 := bstep (se 1 (by rfl) ⟨1474712, by rfl⟩ : syracuseStep 1966283 = 2949425) B2949425
theorem B1310923 : Blo 1309973 1310923 := bstep (se 1 (by rfl) ⟨983192, by rfl⟩ : syracuseStep 1310923 = 1966385) B1966385
theorem B2949335 : Blo 1309973 2949335 := bstep (se 1 (by rfl) ⟨2212001, by rfl⟩ : syracuseStep 2949335 = 4424003) B4424003
theorem B1966295 : Blo 1309973 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B1310935 : Blo 1309973 1310935 := bstep (se 1 (by rfl) ⟨983201, by rfl⟩ : syracuseStep 1310935 = 1966403) B1966403
theorem B4980953 : Blo 1309973 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B2801881 : Blo 1309973 2801881 := bstep (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) B2101411
theorem B2490583 : Blo 1309973 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B1310955 : Blo 1309973 1310955 := bstep (se 1 (by rfl) ⟨983216, by rfl⟩ : syracuseStep 1310955 = 1966433) B1966433
theorem B1474807 : Blo 1309973 1474807 := bstep (se 1 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 1474807 = 2212211) B2212211
theorem B1310967 : Blo 1309973 1310967 := bstep (se 1 (by rfl) ⟨983225, by rfl⟩ : syracuseStep 1310967 = 1966451) B1966451
theorem B1310987 : Blo 1309973 1310987 := bstep (se 1 (by rfl) ⟨983240, by rfl⟩ : syracuseStep 1310987 = 1966481) B1966481
theorem B1310999 : Blo 1309973 1310999 := bstep (se 1 (by rfl) ⟨983249, by rfl⟩ : syracuseStep 1310999 = 1966499) B1966499
theorem B1966361 : Blo 1309973 1966361 := bstep (se 2 (by rfl) ⟨737385, by rfl⟩ : syracuseStep 1966361 = 1474771) B1474771
theorem B1311019 : Blo 1309973 1311019 := bstep (se 1 (by rfl) ⟨983264, by rfl⟩ : syracuseStep 1311019 = 1966529) B1966529
theorem B5112115 : Blo 1309973 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B1311031 : Blo 1309973 1311031 := bstep (se 1 (by rfl) ⟨983273, by rfl⟩ : syracuseStep 1311031 = 1966547) B1966547
theorem B2490689 : Blo 1309973 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1311051 : Blo 1309973 1311051 := bstep (se 1 (by rfl) ⟨983288, by rfl⟩ : syracuseStep 1311051 = 1966577) B1966577
theorem B1311063 : Blo 1309973 1311063 := bstep (se 1 (by rfl) ⟨983297, by rfl⟩ : syracuseStep 1311063 = 1966595) B1966595
theorem B1311083 : Blo 1309973 1311083 := bstep (se 1 (by rfl) ⟨983312, by rfl⟩ : syracuseStep 1311083 = 1966625) B1966625
theorem B1311095 : Blo 1309973 1311095 := bstep (se 1 (by rfl) ⟨983321, by rfl⟩ : syracuseStep 1311095 = 1966643) B1966643
theorem B2949515 : Blo 1309973 2949515 := bstep (se 1 (by rfl) ⟨2212136, by rfl⟩ : syracuseStep 2949515 = 4424273) B4424273
theorem B1966475 : Blo 1309973 1966475 := bstep (se 1 (by rfl) ⟨1474856, by rfl⟩ : syracuseStep 1966475 = 2949713) B2949713
theorem B1311115 : Blo 1309973 1311115 := bstep (se 1 (by rfl) ⟨983336, by rfl⟩ : syracuseStep 1311115 = 1966673) B1966673
theorem B1966487 : Blo 1309973 1966487 := bstep (se 1 (by rfl) ⟨1474865, by rfl⟩ : syracuseStep 1966487 = 2949731) B2949731
theorem B1311127 : Blo 1309973 1311127 := bstep (se 1 (by rfl) ⟨983345, by rfl⟩ : syracuseStep 1311127 = 1966691) B1966691
theorem B1474987 : Blo 1309973 1474987 := bstep (se 1 (by rfl) ⟨1106240, by rfl⟩ : syracuseStep 1474987 = 2212481) B2212481
theorem B1311147 : Blo 1309973 1311147 := bstep (se 1 (by rfl) ⟨983360, by rfl⟩ : syracuseStep 1311147 = 1966721) B1966721
theorem B1311159 : Blo 1309973 1311159 := bstep (se 1 (by rfl) ⟨983369, by rfl⟩ : syracuseStep 1311159 = 1966739) B1966739
theorem B2949569 : Blo 1309973 2949569 := bstep (se 2 (by rfl) ⟨1106088, by rfl⟩ : syracuseStep 2949569 = 2212177) B2212177
theorem B1311179 : Blo 1309973 1311179 := bstep (se 1 (by rfl) ⟨983384, by rfl⟩ : syracuseStep 1311179 = 1966769) B1966769
theorem B1311191 : Blo 1309973 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B1966553 : Blo 1309973 1966553 := bstep (se 2 (by rfl) ⟨737457, by rfl⟩ : syracuseStep 1966553 = 1474915) B1474915
theorem B1311211 : Blo 1309973 1311211 := bstep (se 1 (by rfl) ⟨983408, by rfl⟩ : syracuseStep 1311211 = 1966817) B1966817
theorem B1311223 : Blo 1309973 1311223 := bstep (se 1 (by rfl) ⟨983417, by rfl⟩ : syracuseStep 1311223 = 1966835) B1966835
theorem B1311243 : Blo 1309973 1311243 := bstep (se 1 (by rfl) ⟨983432, by rfl⟩ : syracuseStep 1311243 = 1966865) B1966865
theorem B1475095 : Blo 1309973 1475095 := bstep (se 1 (by rfl) ⟨1106321, by rfl⟩ : syracuseStep 1475095 = 2212643) B2212643
theorem B1311255 : Blo 1309973 1311255 := bstep (se 1 (by rfl) ⟨983441, by rfl⟩ : syracuseStep 1311255 = 1966883) B1966883
theorem B1311275 : Blo 1309973 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B163627573 : Blo 1309973 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B1311287 : Blo 1309973 1311287 := bstep (se 1 (by rfl) ⟨983465, by rfl⟩ : syracuseStep 1311287 = 1966931) B1966931
theorem B5595713 : Blo 1309973 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B3318347 : Blo 1309973 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B2212427 : Blo 1309973 2212427 := bstep (se 1 (by rfl) ⟨1659320, by rfl⟩ : syracuseStep 2212427 = 3318641) B3318641
theorem B1966667 : Blo 1309973 1966667 := bstep (se 1 (by rfl) ⟨1475000, by rfl⟩ : syracuseStep 1966667 = 2950001) B2950001
theorem B1311307 : Blo 1309973 1311307 := bstep (se 1 (by rfl) ⟨983480, by rfl⟩ : syracuseStep 1311307 = 1966961) B1966961
theorem B1966679 : Blo 1309973 1966679 := bstep (se 1 (by rfl) ⟨1475009, by rfl⟩ : syracuseStep 1966679 = 2950019) B2950019
theorem B1311319 : Blo 1309973 1311319 := bstep (se 1 (by rfl) ⟨983489, by rfl⟩ : syracuseStep 1311319 = 1966979) B1966979
theorem B1311339 : Blo 1309973 1311339 := bstep (se 1 (by rfl) ⟨983504, by rfl⟩ : syracuseStep 1311339 = 1967009) B1967009
theorem B1311351 : Blo 1309973 1311351 := bstep (se 1 (by rfl) ⟨983513, by rfl⟩ : syracuseStep 1311351 = 1967027) B1967027
theorem B1311371 : Blo 1309973 1311371 := bstep (se 1 (by rfl) ⟨983528, by rfl⟩ : syracuseStep 1311371 = 1967057) B1967057
theorem B1311383 : Blo 1309973 1311383 := bstep (se 1 (by rfl) ⟨983537, by rfl⟩ : syracuseStep 1311383 = 1967075) B1967075
theorem B2949785 : Blo 1309973 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1966745 : Blo 1309973 1966745 := bstep (se 2 (by rfl) ⟨737529, by rfl⟩ : syracuseStep 1966745 = 1475059) B1475059
theorem B1311403 : Blo 1309973 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B1311415 : Blo 1309973 1311415 := bstep (se 1 (by rfl) ⟨983561, by rfl⟩ : syracuseStep 1311415 = 1967123) B1967123
theorem B2212555 : Blo 1309973 2212555 := bstep (se 1 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 2212555 = 3318833) B3318833
theorem B1475275 : Blo 1309973 1475275 := bstep (se 1 (by rfl) ⟨1106456, by rfl⟩ : syracuseStep 1475275 = 2212913) B2212913
theorem B1311435 : Blo 1309973 1311435 := bstep (se 1 (by rfl) ⟨983576, by rfl⟩ : syracuseStep 1311435 = 1967153) B1967153
theorem B1311447 : Blo 1309973 1311447 := bstep (se 1 (by rfl) ⟨983585, by rfl⟩ : syracuseStep 1311447 = 1967171) B1967171
theorem B1311467 : Blo 1309973 1311467 := bstep (se 1 (by rfl) ⟨983600, by rfl⟩ : syracuseStep 1311467 = 1967201) B1967201
theorem B2949875 : Blo 1309973 2949875 := bstep (se 1 (by rfl) ⟨2212406, by rfl⟩ : syracuseStep 2949875 = 4424813) B4424813
theorem B1311479 : Blo 1309973 1311479 := bstep (se 1 (by rfl) ⟨983609, by rfl⟩ : syracuseStep 1311479 = 1967219) B1967219
theorem B4727555 : Blo 1309973 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B1966859 : Blo 1309973 1966859 := bstep (se 1 (by rfl) ⟨1475144, by rfl⟩ : syracuseStep 1966859 = 2950289) B2950289
theorem B1311499 : Blo 1309973 1311499 := bstep (se 1 (by rfl) ⟨983624, by rfl⟩ : syracuseStep 1311499 = 1967249) B1967249
theorem B2949911 : Blo 1309973 2949911 := bstep (se 1 (by rfl) ⟨2212433, by rfl⟩ : syracuseStep 2949911 = 4424867) B4424867
theorem B1966871 : Blo 1309973 1966871 := bstep (se 1 (by rfl) ⟨1475153, by rfl⟩ : syracuseStep 1966871 = 2950307) B2950307
theorem B1311511 : Blo 1309973 1311511 := bstep (se 1 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 1311511 = 1967267) B1967267
theorem B1311531 : Blo 1309973 1311531 := bstep (se 1 (by rfl) ⟨983648, by rfl⟩ : syracuseStep 1311531 = 1967297) B1967297
theorem B1475383 : Blo 1309973 1475383 := bstep (se 1 (by rfl) ⟨1106537, by rfl⟩ : syracuseStep 1475383 = 2213075) B2213075
theorem B1311543 : Blo 1309973 1311543 := bstep (se 1 (by rfl) ⟨983657, by rfl⟩ : syracuseStep 1311543 = 1967315) B1967315
theorem B14943041 : Blo 1309973 14943041 := bstep (se 2 (by rfl) ⟨5603640, by rfl⟩ : syracuseStep 14943041 = 11207281) B11207281
theorem B1311563 : Blo 1309973 1311563 := bstep (se 1 (by rfl) ⟨983672, by rfl⟩ : syracuseStep 1311563 = 1967345) B1967345
theorem B1311575 : Blo 1309973 1311575 := bstep (se 1 (by rfl) ⟨983681, by rfl⟩ : syracuseStep 1311575 = 1967363) B1967363
theorem B2212697 : Blo 1309973 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1966937 : Blo 1309973 1966937 := bstep (se 2 (by rfl) ⟨737601, by rfl⟩ : syracuseStep 1966937 = 1475203) B1475203
theorem B1311595 : Blo 1309973 1311595 := bstep (se 1 (by rfl) ⟨983696, by rfl⟩ : syracuseStep 1311595 = 1967393) B1967393
theorem B1311607 : Blo 1309973 1311607 := bstep (se 1 (by rfl) ⟨983705, by rfl⟩ : syracuseStep 1311607 = 1967411) B1967411
theorem B11207555 : Blo 1309973 11207555 := bstep (se 1 (by rfl) ⟨8405666, by rfl⟩ : syracuseStep 11207555 = 16811333) B16811333
theorem B1311627 : Blo 1309973 1311627 := bstep (se 1 (by rfl) ⟨983720, by rfl⟩ : syracuseStep 1311627 = 1967441) B1967441
theorem B1311639 : Blo 1309973 1311639 := bstep (se 1 (by rfl) ⟨983729, by rfl⟩ : syracuseStep 1311639 = 1967459) B1967459
theorem B1311659 : Blo 1309973 1311659 := bstep (se 1 (by rfl) ⟨983744, by rfl⟩ : syracuseStep 1311659 = 1967489) B1967489
theorem B1311671 : Blo 1309973 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B4424651 : Blo 1309973 4424651 := bstep (se 1 (by rfl) ⟨3318488, by rfl⟩ : syracuseStep 4424651 = 6636977) B6636977
theorem B2950091 : Blo 1309973 2950091 := bstep (se 1 (by rfl) ⟨2212568, by rfl⟩ : syracuseStep 2950091 = 4425137) B4425137
theorem B1967051 : Blo 1309973 1967051 := bstep (se 1 (by rfl) ⟨1475288, by rfl⟩ : syracuseStep 1967051 = 2950577) B2950577
theorem B1311691 : Blo 1309973 1311691 := bstep (se 1 (by rfl) ⟨983768, by rfl⟩ : syracuseStep 1311691 = 1967537) B1967537
theorem B1967063 : Blo 1309973 1967063 := bstep (se 1 (by rfl) ⟨1475297, by rfl⟩ : syracuseStep 1967063 = 2950595) B2950595
theorem B1311703 : Blo 1309973 1311703 := bstep (se 1 (by rfl) ⟨983777, by rfl⟩ : syracuseStep 1311703 = 1967555) B1967555
theorem B76596185 : Blo 1309973 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B2212825 : Blo 1309973 2212825 := bstep (se 2 (by rfl) ⟨829809, by rfl⟩ : syracuseStep 2212825 = 1659619) B1659619
theorem B1475563 : Blo 1309973 1475563 := bstep (se 1 (by rfl) ⟨1106672, by rfl⟩ : syracuseStep 1475563 = 2213345) B2213345
theorem B1311723 : Blo 1309973 1311723 := bstep (se 1 (by rfl) ⟨983792, by rfl⟩ : syracuseStep 1311723 = 1967585) B1967585
theorem B1311735 : Blo 1309973 1311735 := bstep (se 1 (by rfl) ⟨983801, by rfl⟩ : syracuseStep 1311735 = 1967603) B1967603
theorem B2950145 : Blo 1309973 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1311755 : Blo 1309973 1311755 := bstep (se 1 (by rfl) ⟨983816, by rfl⟩ : syracuseStep 1311755 = 1967633) B1967633
theorem B9962513 : Blo 1309973 9962513 := bstep (se 2 (by rfl) ⟨3735942, by rfl⟩ : syracuseStep 9962513 = 7471885) B7471885
theorem B1311767 : Blo 1309973 1311767 := bstep (se 1 (by rfl) ⟨983825, by rfl⟩ : syracuseStep 1311767 = 1967651) B1967651
theorem B1967129 : Blo 1309973 1967129 := bstep (se 2 (by rfl) ⟨737673, by rfl⟩ : syracuseStep 1967129 = 1475347) B1475347
theorem B1311787 : Blo 1309973 1311787 := bstep (se 1 (by rfl) ⟨983840, by rfl⟩ : syracuseStep 1311787 = 1967681) B1967681
theorem B1311799 : Blo 1309973 1311799 := bstep (se 1 (by rfl) ⟨983849, by rfl⟩ : syracuseStep 1311799 = 1967699) B1967699
theorem B24249419 : Blo 1309973 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B1311819 : Blo 1309973 1311819 := bstep (se 1 (by rfl) ⟨983864, by rfl⟩ : syracuseStep 1311819 = 1967729) B1967729
theorem B1475671 : Blo 1309973 1475671 := bstep (se 1 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 1475671 = 2213507) B2213507
theorem B1311831 : Blo 1309973 1311831 := bstep (se 1 (by rfl) ⟨983873, by rfl⟩ : syracuseStep 1311831 = 1967747) B1967747
theorem B1311851 : Blo 1309973 1311851 := bstep (se 1 (by rfl) ⟨983888, by rfl⟩ : syracuseStep 1311851 = 1967777) B1967777
theorem B1311863 : Blo 1309973 1311863 := bstep (se 1 (by rfl) ⟨983897, by rfl⟩ : syracuseStep 1311863 = 1967795) B1967795
theorem B1967243 : Blo 1309973 1967243 := bstep (se 1 (by rfl) ⟨1475432, by rfl⟩ : syracuseStep 1967243 = 2950865) B2950865
theorem B1311883 : Blo 1309973 1311883 := bstep (se 1 (by rfl) ⟨983912, by rfl⟩ : syracuseStep 1311883 = 1967825) B1967825
theorem B1967255 : Blo 1309973 1967255 := bstep (se 1 (by rfl) ⟨1475441, by rfl⟩ : syracuseStep 1967255 = 2950883) B2950883
theorem B1311895 : Blo 1309973 1311895 := bstep (se 1 (by rfl) ⟨983921, by rfl⟩ : syracuseStep 1311895 = 1967843) B1967843
theorem B1311915 : Blo 1309973 1311915 := bstep (se 1 (by rfl) ⟨983936, by rfl⟩ : syracuseStep 1311915 = 1967873) B1967873
theorem B4727987 : Blo 1309973 4727987 := bstep (se 1 (by rfl) ⟨3545990, by rfl⟩ : syracuseStep 4727987 = 7091981) B7091981
theorem B1311927 : Blo 1309973 1311927 := bstep (se 1 (by rfl) ⟨983945, by rfl⟩ : syracuseStep 1311927 = 1967891) B1967891
theorem B1311947 : Blo 1309973 1311947 := bstep (se 1 (by rfl) ⟨983960, by rfl⟩ : syracuseStep 1311947 = 1967921) B1967921
theorem B4424921 : Blo 1309973 4424921 := bstep (se 2 (by rfl) ⟨1659345, by rfl⟩ : syracuseStep 4424921 = 3318691) B3318691
theorem B2950361 : Blo 1309973 2950361 := bstep (se 2 (by rfl) ⟨1106385, by rfl⟩ : syracuseStep 2950361 = 2212771) B2212771
theorem B1967321 : Blo 1309973 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B1311959 : Blo 1309973 1311959 := bstep (se 1 (by rfl) ⟨983969, by rfl⟩ : syracuseStep 1311959 = 1967939) B1967939
theorem B1475851 : Blo 1309973 1475851 := bstep (se 1 (by rfl) ⟨1106888, by rfl⟩ : syracuseStep 1475851 = 2213777) B2213777
theorem B2950451 : Blo 1309973 2950451 := bstep (se 1 (by rfl) ⟨2212838, by rfl⟩ : syracuseStep 2950451 = 4425677) B4425677
theorem B1967435 : Blo 1309973 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B2950487 : Blo 1309973 2950487 := bstep (se 1 (by rfl) ⟨2212865, by rfl⟩ : syracuseStep 2950487 = 4425731) B4425731
theorem B1967447 : Blo 1309973 1967447 := bstep (se 1 (by rfl) ⟨1475585, by rfl⟩ : syracuseStep 1967447 = 2951171) B2951171
theorem B1475959 : Blo 1309973 1475959 := bstep (se 1 (by rfl) ⟨1106969, by rfl⟩ : syracuseStep 1475959 = 2213939) B2213939
theorem B1967513 : Blo 1309973 1967513 := bstep (se 2 (by rfl) ⟨737817, by rfl⟩ : syracuseStep 1967513 = 1475635) B1475635
theorem B9954737 : Blo 1309973 9954737 := bstep (se 2 (by rfl) ⟨3733026, by rfl⟩ : syracuseStep 9954737 = 7466053) B7466053
theorem B2098649 : Blo 1309973 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B11191769 : Blo 1309973 11191769 := bstep (se 2 (by rfl) ⟨4196913, by rfl⟩ : syracuseStep 11191769 = 8393827) B8393827
theorem B2950667 : Blo 1309973 2950667 := bstep (se 1 (by rfl) ⟨2213000, by rfl⟩ : syracuseStep 2950667 = 4426001) B4426001
theorem B1967627 : Blo 1309973 1967627 := bstep (se 1 (by rfl) ⟨1475720, by rfl⟩ : syracuseStep 1967627 = 2951441) B2951441
theorem B3319319 : Blo 1309973 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2213399 : Blo 1309973 2213399 := bstep (se 1 (by rfl) ⟨1660049, by rfl⟩ : syracuseStep 2213399 = 3320099) B3320099
theorem B1967639 : Blo 1309973 1967639 := bstep (se 1 (by rfl) ⟨1475729, by rfl⟩ : syracuseStep 1967639 = 2951459) B2951459
theorem B2950721 : Blo 1309973 2950721 := bstep (se 2 (by rfl) ⟨1106520, by rfl⟩ : syracuseStep 2950721 = 2213041) B2213041
theorem B1967705 : Blo 1309973 1967705 := bstep (se 2 (by rfl) ⟨737889, by rfl⟩ : syracuseStep 1967705 = 1475779) B1475779
theorem B28345949 : Blo 1309973 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B6063761 : Blo 1309973 6063761 := bstep (se 2 (by rfl) ⟨2273910, by rfl⟩ : syracuseStep 6063761 = 4547821) B4547821
theorem B2213527 : Blo 1309973 2213527 := bstep (se 1 (by rfl) ⟨1660145, by rfl⟩ : syracuseStep 2213527 = 3320291) B3320291
theorem B1967819 : Blo 1309973 1967819 := bstep (se 1 (by rfl) ⟨1475864, by rfl⟩ : syracuseStep 1967819 = 2951729) B2951729
theorem B1967831 : Blo 1309973 1967831 := bstep (se 1 (by rfl) ⟨1475873, by rfl⟩ : syracuseStep 1967831 = 2951747) B2951747
theorem B2361089 : Blo 1309973 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2950937 : Blo 1309973 2950937 := bstep (se 2 (by rfl) ⟨1106601, by rfl⟩ : syracuseStep 2950937 = 2213203) B2213203
theorem B1967897 : Blo 1309973 1967897 := bstep (se 2 (by rfl) ⟨737961, by rfl⟩ : syracuseStep 1967897 = 1475923) B1475923
theorem B33605441 : Blo 1309973 33605441 := bstep (se 2 (by rfl) ⟨12602040, by rfl⟩ : syracuseStep 33605441 = 25204081) B25204081
theorem B6915905 : Blo 1309973 6915905 := bstep (se 2 (by rfl) ⟨2593464, by rfl⟩ : syracuseStep 6915905 = 5186929) B5186929
theorem B2951027 : Blo 1309973 2951027 := bstep (se 1 (by rfl) ⟨2213270, by rfl⟩ : syracuseStep 2951027 = 4426541) B4426541
theorem B9955223 : Blo 1309973 9955223 := bstep (se 1 (by rfl) ⟨7466417, by rfl⟩ : syracuseStep 9955223 = 14932835) B14932835
theorem B6637463 : Blo 1309973 6637463 := bstep (se 1 (by rfl) ⟨4978097, by rfl⟩ : syracuseStep 6637463 = 9956195) B9956195
theorem B4425623 : Blo 1309973 4425623 := bstep (se 1 (by rfl) ⟨3319217, by rfl⟩ : syracuseStep 4425623 = 6638435) B6638435
theorem B2951063 : Blo 1309973 2951063 := bstep (se 1 (by rfl) ⟨2213297, by rfl⟩ : syracuseStep 2951063 = 4426595) B4426595
theorem B11200517 : Blo 1309973 11200517 := bstep (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) B2100097
theorem B5597201 : Blo 1309973 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B31868963 : Blo 1309973 31868963 := bstep (se 1 (by rfl) ⟨23901722, by rfl⟩ : syracuseStep 31868963 = 47803445) B47803445
theorem B2951243 : Blo 1309973 2951243 := bstep (se 1 (by rfl) ⟨2213432, by rfl⟩ : syracuseStep 2951243 = 4426865) B4426865
theorem B2951297 : Blo 1309973 2951297 := bstep (se 2 (by rfl) ⟨1106736, by rfl⟩ : syracuseStep 2951297 = 2213473) B2213473
theorem B3319987 : Blo 1309973 3319987 := bstep (se 1 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 3319987 = 4979981) B4979981
theorem B3320129 : Blo 1309973 3320129 := bstep (se 2 (by rfl) ⟨1245048, by rfl⟩ : syracuseStep 3320129 = 2490097) B2490097
theorem B2951513 : Blo 1309973 2951513 := bstep (se 2 (by rfl) ⟨1106817, by rfl⟩ : syracuseStep 2951513 = 2213635) B2213635
theorem B1640855 : Blo 1309973 1640855 := bstep (se 1 (by rfl) ⟨1230641, by rfl⟩ : syracuseStep 1640855 = 2461283) B2461283
theorem B7088563 : Blo 1309973 7088563 := bstep (se 1 (by rfl) ⟨5316422, by rfl⟩ : syracuseStep 7088563 = 10632845) B10632845
theorem B4426163 : Blo 1309973 4426163 := bstep (se 1 (by rfl) ⟨3319622, by rfl⟩ : syracuseStep 4426163 = 6639245) B6639245
theorem B2951603 : Blo 1309973 2951603 := bstep (se 1 (by rfl) ⟨2213702, by rfl⟩ : syracuseStep 2951603 = 4427405) B4427405
theorem B1681879 : Blo 1309973 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B2951639 : Blo 1309973 2951639 := bstep (se 1 (by rfl) ⟨2213729, by rfl⟩ : syracuseStep 2951639 = 4427459) B4427459
theorem B4975121 : Blo 1309973 4975121 := bstep (se 2 (by rfl) ⟨1865670, by rfl⟩ : syracuseStep 4975121 = 3731341) B3731341
theorem B2951819 : Blo 1309973 2951819 := bstep (se 1 (by rfl) ⟨2213864, by rfl⟩ : syracuseStep 2951819 = 4427729) B4427729
theorem B6302387 : Blo 1309973 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B4426433 : Blo 1309973 4426433 := bstep (se 2 (by rfl) ⟨1659912, by rfl⟩ : syracuseStep 4426433 = 3319825) B3319825
theorem B2951873 : Blo 1309973 2951873 := bstep (se 2 (by rfl) ⟨1106952, by rfl⟩ : syracuseStep 2951873 = 2213905) B2213905
theorem B34073293 : Blo 1309973 34073293 := bstep (se 3 (by rfl) ⟨6388742, by rfl⟩ : syracuseStep 34073293 = 12777485) B12777485
theorem B22408001 : Blo 1309973 22408001 := bstep (se 2 (by rfl) ⟨8403000, by rfl⟩ : syracuseStep 22408001 = 16806001) B16806001
theorem B4975577 : Blo 1309973 4975577 := bstep (se 2 (by rfl) ⟨1865841, by rfl⟩ : syracuseStep 4975577 = 3731683) B3731683
theorem B5598173 : Blo 1309973 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B2362393 : Blo 1309973 2362393 := bstep (se 2 (by rfl) ⟨885897, by rfl⟩ : syracuseStep 2362393 = 1771795) B1771795
theorem B4975789 : Blo 1309973 4975789 := bstep (se 3 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 4975789 = 1865921) B1865921
theorem B4426973 : Blo 1309973 4426973 := bstep (se 3 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 4426973 = 1660115) B1660115
theorem B2395415 : Blo 1309973 2395415 := bstep (se 1 (by rfl) ⟨1796561, by rfl⟩ : syracuseStep 2395415 = 3593123) B3593123
theorem B3149273 : Blo 1309973 3149273 := bstep (se 2 (by rfl) ⟨1180977, by rfl⟩ : syracuseStep 3149273 = 2361955) B2361955
theorem B2362841 : Blo 1309973 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B4976093 : Blo 1309973 4976093 := bstep (se 3 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 4976093 = 1866035) B1866035
theorem B5312075 : Blo 1309973 5312075 := bstep (se 1 (by rfl) ⟨3984056, by rfl⟩ : syracuseStep 5312075 = 7968113) B7968113
theorem B1658647 : Blo 1309973 1658647 := bstep (se 1 (by rfl) ⟨1243985, by rfl⟩ : syracuseStep 1658647 = 2487971) B2487971
theorem B3149657 : Blo 1309973 3149657 := bstep (se 2 (by rfl) ⟨1181121, by rfl⟩ : syracuseStep 3149657 = 2362243) B2362243
theorem B2363339 : Blo 1309973 2363339 := bstep (se 1 (by rfl) ⟨1772504, by rfl⟩ : syracuseStep 2363339 = 3545009) B3545009
theorem B40341539 : Blo 1309973 40341539 := bstep (se 1 (by rfl) ⟨30256154, by rfl⟩ : syracuseStep 40341539 = 60512309) B60512309
theorem B13455395 : Blo 1309973 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B11194433 : Blo 1309973 11194433 := bstep (se 2 (by rfl) ⟨4197912, by rfl⟩ : syracuseStep 11194433 = 8395825) B8395825
theorem B3543115 : Blo 1309973 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B3543191 : Blo 1309973 3543191 := bstep (se 1 (by rfl) ⟨2657393, by rfl⟩ : syracuseStep 3543191 = 5314787) B5314787
theorem B4042955 : Blo 1309973 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B7467329 : Blo 1309973 7467329 := bstep (se 2 (by rfl) ⟨2800248, by rfl⟩ : syracuseStep 7467329 = 5600497) B5600497
theorem B11505995 : Blo 1309973 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B4198835 : Blo 1309973 4198835 := bstep (se 1 (by rfl) ⟨3149126, by rfl⟩ : syracuseStep 4198835 = 6298253) B6298253
theorem B3731933 : Blo 1309973 3731933 := bstep (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) B1399475
theorem B1438187 : Blo 1309973 1438187 := bstep (se 1 (by rfl) ⟨1078640, by rfl⟩ : syracuseStep 1438187 = 2157281) B2157281
theorem B1659467 : Blo 1309973 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B4256435 : Blo 1309973 4256435 := bstep (se 1 (by rfl) ⟨3192326, by rfl⟩ : syracuseStep 4256435 = 6384653) B6384653
theorem B2486999 : Blo 1309973 2486999 := bstep (se 1 (by rfl) ⟨1865249, by rfl⟩ : syracuseStep 2486999 = 3730499) B3730499
theorem B209875697 : Blo 1309973 209875697 := bstep (se 2 (by rfl) ⟨78703386, by rfl⟩ : syracuseStep 209875697 = 157406773) B157406773
theorem B28357361 : Blo 1309973 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B43078501 : Blo 1309973 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B2798489 : Blo 1309973 2798489 := bstep (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) B2098867
theorem B2487257 : Blo 1309973 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B2659339 : Blo 1309973 2659339 := bstep (se 1 (by rfl) ⟨1994504, by rfl⟩ : syracuseStep 2659339 = 3989009) B3989009
theorem B8508509 : Blo 1309973 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B1660171 : Blo 1309973 1660171 := bstep (se 1 (by rfl) ⟨1245128, by rfl⟩ : syracuseStep 1660171 = 2490257) B2490257
theorem B2487667 : Blo 1309973 2487667 := bstep (se 1 (by rfl) ⟨1865750, by rfl⟩ : syracuseStep 2487667 = 3731501) B3731501
theorem B5977475 : Blo 1309973 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B6641027 : Blo 1309973 6641027 := bstep (se 1 (by rfl) ⟨4980770, by rfl⟩ : syracuseStep 6641027 = 9961541) B9961541
theorem B14931377 : Blo 1309973 14931377 := bstep (se 2 (by rfl) ⟨5599266, by rfl⟩ : syracuseStep 14931377 = 11198533) B11198533
theorem B5600771 : Blo 1309973 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B1660439 : Blo 1309973 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B2799155 : Blo 1309973 2799155 := bstep (se 1 (by rfl) ⟨2099366, by rfl⟩ : syracuseStep 2799155 = 4198733) B4198733
theorem B9090625 : Blo 1309973 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B4421195 : Blo 1309973 4421195 := bstep (se 1 (by rfl) ⟨3315896, by rfl⟩ : syracuseStep 4421195 = 6631793) B6631793
theorem B3151511 : Blo 1309973 3151511 := bstep (se 1 (by rfl) ⟨2363633, by rfl⟩ : syracuseStep 3151511 = 4727267) B4727267
theorem B1865369 : Blo 1309973 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B4724497 : Blo 1309973 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B5314349 : Blo 1309973 5314349 := bstep (se 3 (by rfl) ⟨996440, by rfl⟩ : syracuseStep 5314349 = 1992881) B1992881
theorem B4421465 : Blo 1309973 4421465 := bstep (se 2 (by rfl) ⟨1658049, by rfl⟩ : syracuseStep 4421465 = 3316099) B3316099
theorem B2488153 : Blo 1309973 2488153 := bstep (se 2 (by rfl) ⟨933057, by rfl⟩ : syracuseStep 2488153 = 1866115) B1866115
theorem B5601113 : Blo 1309973 5601113 := bstep (se 2 (by rfl) ⟨2100417, by rfl⟩ : syracuseStep 5601113 = 4200835) B4200835
theorem B4978691 : Blo 1309973 4978691 := bstep (se 1 (by rfl) ⟨3734018, by rfl⟩ : syracuseStep 4978691 = 7468037) B7468037
theorem B4978705 : Blo 1309973 4978705 := bstep (se 2 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 4978705 = 3734029) B3734029
theorem B9443459 : Blo 1309973 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B1866007 : Blo 1309973 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B4979009 : Blo 1309973 4979009 := bstep (se 2 (by rfl) ⟨1867128, by rfl⟩ : syracuseStep 4979009 = 3734257) B3734257
theorem B1890635 : Blo 1309973 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B8395109 : Blo 1309973 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B2488715 : Blo 1309973 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B2947481 : Blo 1309973 2947481 := bstep (se 2 (by rfl) ⟨1105305, by rfl⟩ : syracuseStep 2947481 = 2210611) B2210611
theorem B2947571 : Blo 1309973 2947571 := bstep (se 1 (by rfl) ⟨2210678, by rfl⟩ : syracuseStep 2947571 = 4421357) B4421357
theorem B2947607 : Blo 1309973 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B4422167 : Blo 1309973 4422167 := bstep (se 1 (by rfl) ⟨3316625, by rfl⟩ : syracuseStep 4422167 = 6633251) B6633251
theorem B3545623 : Blo 1309973 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B2488897 : Blo 1309973 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B2243161 : Blo 1309973 2243161 := bstep (se 2 (by rfl) ⟨841185, by rfl⟩ : syracuseStep 2243161 = 1682371) B1682371
theorem B1399403 : Blo 1309973 1399403 := bstep (se 1 (by rfl) ⟨1049552, by rfl⟩ : syracuseStep 1399403 = 2099105) B2099105
theorem B33618563 : Blo 1309973 33618563 := bstep (se 1 (by rfl) ⟨25213922, by rfl⟩ : syracuseStep 33618563 = 50427845) B50427845
theorem B11958961 : Blo 1309973 11958961 := bstep (se 2 (by rfl) ⟨4484610, by rfl⟩ : syracuseStep 11958961 = 8969221) B8969221
theorem B3316403 : Blo 1309973 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B2947787 : Blo 1309973 2947787 := bstep (se 1 (by rfl) ⟨2210840, by rfl⟩ : syracuseStep 2947787 = 4421681) B4421681
theorem B2947841 : Blo 1309973 2947841 := bstep (se 2 (by rfl) ⟨1105440, by rfl⟩ : syracuseStep 2947841 = 2210881) B2210881
theorem B37780289 : Blo 1309973 37780289 := bstep (se 2 (by rfl) ⟨14167608, by rfl⟩ : syracuseStep 37780289 = 28335217) B28335217
theorem B23919461 : Blo 1309973 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B2210699 : Blo 1309973 2210699 := bstep (se 1 (by rfl) ⟨1658024, by rfl⟩ : syracuseStep 2210699 = 3316049) B3316049
theorem B3783617 : Blo 1309973 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B1965017 : Blo 1309973 1965017 := bstep (se 2 (by rfl) ⟨736881, by rfl⟩ : syracuseStep 1965017 = 1473763) B1473763
theorem B2948057 : Blo 1309973 2948057 := bstep (se 2 (by rfl) ⟨1105521, by rfl⟩ : syracuseStep 2948057 = 2211043) B2211043
theorem B3316697 : Blo 1309973 3316697 := bstep (se 2 (by rfl) ⟨1243761, by rfl⟩ : syracuseStep 3316697 = 2487523) B2487523
theorem B4979677 : Blo 1309973 4979677 := bstep (se 3 (by rfl) ⟨933689, by rfl⟩ : syracuseStep 4979677 = 1867379) B1867379
theorem B2210827 : Blo 1309973 2210827 := bstep (se 1 (by rfl) ⟨1658120, by rfl⟩ : syracuseStep 2210827 = 3316241) B3316241
theorem B2800651 : Blo 1309973 2800651 := bstep (se 1 (by rfl) ⟨2100488, by rfl⟩ : syracuseStep 2800651 = 4200977) B4200977
theorem B2366489 : Blo 1309973 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B63765539 : Blo 1309973 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B30293027 : Blo 1309973 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B2948147 : Blo 1309973 2948147 := bstep (se 1 (by rfl) ⟨2211110, by rfl⟩ : syracuseStep 2948147 = 4422221) B4422221
theorem B4422707 : Blo 1309973 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B7461953 : Blo 1309973 7461953 := bstep (se 2 (by rfl) ⟨2798232, by rfl⟩ : syracuseStep 7461953 = 5596465) B5596465
theorem B1965131 : Blo 1309973 1965131 := bstep (se 1 (by rfl) ⟨1473848, by rfl⟩ : syracuseStep 1965131 = 2947697) B2947697
theorem B1866827 : Blo 1309973 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B1965143 : Blo 1309973 1965143 := bstep (se 1 (by rfl) ⟨1473857, by rfl⟩ : syracuseStep 1965143 = 2947715) B2947715
theorem B2948183 : Blo 1309973 2948183 := bstep (se 1 (by rfl) ⟨2211137, by rfl⟩ : syracuseStep 2948183 = 4422275) B4422275
theorem B1965209 : Blo 1309973 1965209 := bstep (se 2 (by rfl) ⟨736953, by rfl⟩ : syracuseStep 1965209 = 1473907) B1473907
theorem B2210969 : Blo 1309973 2210969 := bstep (se 2 (by rfl) ⟨829113, by rfl⟩ : syracuseStep 2210969 = 1658227) B1658227
theorem B1965323 : Blo 1309973 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B2948363 : Blo 1309973 2948363 := bstep (se 1 (by rfl) ⟨2211272, by rfl⟩ : syracuseStep 2948363 = 4422545) B4422545
theorem B2489611 : Blo 1309973 2489611 := bstep (se 1 (by rfl) ⟨1867208, by rfl⟩ : syracuseStep 2489611 = 3734417) B3734417
theorem B1309975 : Blo 1309973 1309975 := bstep (se 1 (by rfl) ⟨982481, by rfl⟩ : syracuseStep 1309975 = 1964963) B1964963
theorem B1965335 : Blo 1309973 1965335 := bstep (se 1 (by rfl) ⟨1474001, by rfl⟩ : syracuseStep 1965335 = 2948003) B2948003
theorem B2211097 : Blo 1309973 2211097 := bstep (se 2 (by rfl) ⟨829161, by rfl⟩ : syracuseStep 2211097 = 1658323) B1658323
theorem B1309995 : Blo 1309973 1309995 := bstep (se 1 (by rfl) ⟨982496, by rfl⟩ : syracuseStep 1309995 = 1964993) B1964993
theorem B1473835 : Blo 1309973 1473835 := bstep (se 1 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 1473835 = 2210753) B2210753
theorem B1310007 : Blo 1309973 1310007 := bstep (se 1 (by rfl) ⟨982505, by rfl⟩ : syracuseStep 1310007 = 1965011) B1965011
theorem B2948417 : Blo 1309973 2948417 := bstep (se 2 (by rfl) ⟨1105656, by rfl⟩ : syracuseStep 2948417 = 2211313) B2211313
theorem B4422977 : Blo 1309973 4422977 := bstep (se 2 (by rfl) ⟨1658616, by rfl⟩ : syracuseStep 4422977 = 3317233) B3317233
theorem B3734849 : Blo 1309973 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B1310027 : Blo 1309973 1310027 := bstep (se 1 (by rfl) ⟨982520, by rfl⟩ : syracuseStep 1310027 = 1965041) B1965041
theorem B1310039 : Blo 1309973 1310039 := bstep (se 1 (by rfl) ⟨982529, by rfl⟩ : syracuseStep 1310039 = 1965059) B1965059
theorem B2489687 : Blo 1309973 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B1965401 : Blo 1309973 1965401 := bstep (se 2 (by rfl) ⟨737025, by rfl⟩ : syracuseStep 1965401 = 1474051) B1474051
theorem B3734873 : Blo 1309973 3734873 := bstep (se 2 (by rfl) ⟨1400577, by rfl⟩ : syracuseStep 3734873 = 2801155) B2801155
theorem B1310059 : Blo 1309973 1310059 := bstep (se 1 (by rfl) ⟨982544, by rfl⟩ : syracuseStep 1310059 = 1965089) B1965089
theorem B1310071 : Blo 1309973 1310071 := bstep (se 1 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 1310071 = 1965107) B1965107
theorem B1310091 : Blo 1309973 1310091 := bstep (se 1 (by rfl) ⟨982568, by rfl⟩ : syracuseStep 1310091 = 1965137) B1965137
theorem B1310103 : Blo 1309973 1310103 := bstep (se 1 (by rfl) ⟨982577, by rfl⟩ : syracuseStep 1310103 = 1965155) B1965155
theorem B1473943 : Blo 1309973 1473943 := bstep (se 1 (by rfl) ⟨1105457, by rfl⟩ : syracuseStep 1473943 = 2210915) B2210915
theorem B1310123 : Blo 1309973 1310123 := bstep (se 1 (by rfl) ⟨982592, by rfl⟩ : syracuseStep 1310123 = 1965185) B1965185
theorem B1310135 : Blo 1309973 1310135 := bstep (se 1 (by rfl) ⟨982601, by rfl⟩ : syracuseStep 1310135 = 1965203) B1965203
theorem B1310155 : Blo 1309973 1310155 := bstep (se 1 (by rfl) ⟨982616, by rfl⟩ : syracuseStep 1310155 = 1965233) B1965233
theorem B1965515 : Blo 1309973 1965515 := bstep (se 1 (by rfl) ⟨1474136, by rfl⟩ : syracuseStep 1965515 = 2948273) B2948273
theorem B1310167 : Blo 1309973 1310167 := bstep (se 1 (by rfl) ⟨982625, by rfl⟩ : syracuseStep 1310167 = 1965251) B1965251
theorem B1965527 : Blo 1309973 1965527 := bstep (se 1 (by rfl) ⟨1474145, by rfl⟩ : syracuseStep 1965527 = 2948291) B2948291
theorem B1310187 : Blo 1309973 1310187 := bstep (se 1 (by rfl) ⟨982640, by rfl⟩ : syracuseStep 1310187 = 1965281) B1965281
theorem B1310199 : Blo 1309973 1310199 := bstep (se 1 (by rfl) ⟨982649, by rfl⟩ : syracuseStep 1310199 = 1965299) B1965299
theorem B1310219 : Blo 1309973 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B1310231 : Blo 1309973 1310231 := bstep (se 1 (by rfl) ⟨982673, by rfl⟩ : syracuseStep 1310231 = 1965347) B1965347
theorem B1965593 : Blo 1309973 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B2948633 : Blo 1309973 2948633 := bstep (se 2 (by rfl) ⟨1105737, by rfl⟩ : syracuseStep 2948633 = 2211475) B2211475
theorem B1310251 : Blo 1309973 1310251 := bstep (se 1 (by rfl) ⟨982688, by rfl⟩ : syracuseStep 1310251 = 1965377) B1965377
theorem B1310263 : Blo 1309973 1310263 := bstep (se 1 (by rfl) ⟨982697, by rfl⟩ : syracuseStep 1310263 = 1965395) B1965395
theorem B1310283 : Blo 1309973 1310283 := bstep (se 1 (by rfl) ⟨982712, by rfl⟩ : syracuseStep 1310283 = 1965425) B1965425
theorem B1474123 : Blo 1309973 1474123 := bstep (se 1 (by rfl) ⟨1105592, by rfl⟩ : syracuseStep 1474123 = 2211185) B2211185
theorem B1310295 : Blo 1309973 1310295 := bstep (se 1 (by rfl) ⟨982721, by rfl⟩ : syracuseStep 1310295 = 1965443) B1965443
theorem B5979737 : Blo 1309973 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B1310315 : Blo 1309973 1310315 := bstep (se 1 (by rfl) ⟨982736, by rfl⟩ : syracuseStep 1310315 = 1965473) B1965473
theorem B2948723 : Blo 1309973 2948723 := bstep (se 1 (by rfl) ⟨2211542, by rfl⟩ : syracuseStep 2948723 = 4423085) B4423085
theorem B1310327 : Blo 1309973 1310327 := bstep (se 1 (by rfl) ⟨982745, by rfl⟩ : syracuseStep 1310327 = 1965491) B1965491
theorem B1310347 : Blo 1309973 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B1965707 : Blo 1309973 1965707 := bstep (se 1 (by rfl) ⟨1474280, by rfl⟩ : syracuseStep 1965707 = 2948561) B2948561
theorem B1310359 : Blo 1309973 1310359 := bstep (se 1 (by rfl) ⟨982769, by rfl⟩ : syracuseStep 1310359 = 1965539) B1965539
theorem B1965719 : Blo 1309973 1965719 := bstep (se 1 (by rfl) ⟨1474289, by rfl⟩ : syracuseStep 1965719 = 2948579) B2948579
theorem B2948759 : Blo 1309973 2948759 := bstep (se 1 (by rfl) ⟨2211569, by rfl⟩ : syracuseStep 2948759 = 4423139) B4423139
theorem B19168919 : Blo 1309973 19168919 := bstep (se 1 (by rfl) ⟨14376689, by rfl⟩ : syracuseStep 19168919 = 28753379) B28753379
theorem B1310379 : Blo 1309973 1310379 := bstep (se 1 (by rfl) ⟨982784, by rfl⟩ : syracuseStep 1310379 = 1965569) B1965569
theorem B1310391 : Blo 1309973 1310391 := bstep (se 1 (by rfl) ⟨982793, by rfl⟩ : syracuseStep 1310391 = 1965587) B1965587
theorem B1474231 : Blo 1309973 1474231 := bstep (se 1 (by rfl) ⟨1105673, by rfl⟩ : syracuseStep 1474231 = 2211347) B2211347
theorem B1310411 : Blo 1309973 1310411 := bstep (se 1 (by rfl) ⟨982808, by rfl⟩ : syracuseStep 1310411 = 1965617) B1965617
theorem B1310423 : Blo 1309973 1310423 := bstep (se 1 (by rfl) ⟨982817, by rfl⟩ : syracuseStep 1310423 = 1965635) B1965635
theorem B1965785 : Blo 1309973 1965785 := bstep (se 2 (by rfl) ⟨737169, by rfl⟩ : syracuseStep 1965785 = 1474339) B1474339
theorem B1310443 : Blo 1309973 1310443 := bstep (se 1 (by rfl) ⟨982832, by rfl⟩ : syracuseStep 1310443 = 1965665) B1965665
theorem B1310455 : Blo 1309973 1310455 := bstep (se 1 (by rfl) ⟨982841, by rfl⟩ : syracuseStep 1310455 = 1965683) B1965683
theorem B1310475 : Blo 1309973 1310475 := bstep (se 1 (by rfl) ⟨982856, by rfl⟩ : syracuseStep 1310475 = 1965713) B1965713
theorem B1310487 : Blo 1309973 1310487 := bstep (se 1 (by rfl) ⟨982865, by rfl⟩ : syracuseStep 1310487 = 1965731) B1965731
theorem B1400599 : Blo 1309973 1400599 := bstep (se 1 (by rfl) ⟨1050449, by rfl⟩ : syracuseStep 1400599 = 2100899) B2100899
theorem B1310507 : Blo 1309973 1310507 := bstep (se 1 (by rfl) ⟨982880, by rfl⟩ : syracuseStep 1310507 = 1965761) B1965761
theorem B1310519 : Blo 1309973 1310519 := bstep (se 1 (by rfl) ⟨982889, by rfl⟩ : syracuseStep 1310519 = 1965779) B1965779
theorem B1310539 : Blo 1309973 1310539 := bstep (se 1 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 1310539 = 1965809) B1965809
theorem B1965899 : Blo 1309973 1965899 := bstep (se 1 (by rfl) ⟨1474424, by rfl⟩ : syracuseStep 1965899 = 2948849) B2948849
theorem B2948939 : Blo 1309973 2948939 := bstep (se 1 (by rfl) ⟨2211704, by rfl⟩ : syracuseStep 2948939 = 4423409) B4423409
theorem B4726603 : Blo 1309973 4726603 := bstep (se 1 (by rfl) ⟨3544952, by rfl⟩ : syracuseStep 4726603 = 7089905) B7089905
theorem B1310551 : Blo 1309973 1310551 := bstep (se 1 (by rfl) ⟨982913, by rfl⟩ : syracuseStep 1310551 = 1965827) B1965827
theorem B1965911 : Blo 1309973 1965911 := bstep (se 1 (by rfl) ⟨1474433, by rfl⟩ : syracuseStep 1965911 = 2948867) B2948867
theorem B2211671 : Blo 1309973 2211671 := bstep (se 1 (by rfl) ⟨1658753, by rfl⟩ : syracuseStep 2211671 = 3317507) B3317507
theorem B6635357 : Blo 1309973 6635357 := bstep (se 3 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 6635357 = 2488259) B2488259
theorem B4423517 : Blo 1309973 4423517 := bstep (se 3 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 4423517 = 1658819) B1658819
theorem B43106147 : Blo 1309973 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B1310571 : Blo 1309973 1310571 := bstep (se 1 (by rfl) ⟨982928, by rfl⟩ : syracuseStep 1310571 = 1965857) B1965857
theorem B1474411 : Blo 1309973 1474411 := bstep (se 1 (by rfl) ⟨1105808, by rfl⟩ : syracuseStep 1474411 = 2211617) B2211617
theorem B1310583 : Blo 1309973 1310583 := bstep (se 1 (by rfl) ⟨982937, by rfl⟩ : syracuseStep 1310583 = 1965875) B1965875
theorem B2948993 : Blo 1309973 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B1310603 : Blo 1309973 1310603 := bstep (se 1 (by rfl) ⟨982952, by rfl⟩ : syracuseStep 1310603 = 1965905) B1965905
theorem B1310615 : Blo 1309973 1310615 := bstep (se 1 (by rfl) ⟨982961, by rfl⟩ : syracuseStep 1310615 = 1965923) B1965923
theorem B1965977 : Blo 1309973 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B1310635 : Blo 1309973 1310635 := bstep (se 1 (by rfl) ⟨982976, by rfl⟩ : syracuseStep 1310635 = 1965953) B1965953
theorem B1310647 : Blo 1309973 1310647 := bstep (se 1 (by rfl) ⟨982985, by rfl⟩ : syracuseStep 1310647 = 1965971) B1965971
theorem B1310667 : Blo 1309973 1310667 := bstep (se 1 (by rfl) ⟨983000, by rfl⟩ : syracuseStep 1310667 = 1966001) B1966001
theorem B1310679 : Blo 1309973 1310679 := bstep (se 1 (by rfl) ⟨983009, by rfl⟩ : syracuseStep 1310679 = 1966019) B1966019
theorem B1474519 : Blo 1309973 1474519 := bstep (se 1 (by rfl) ⟨1105889, by rfl⟩ : syracuseStep 1474519 = 2211779) B2211779
theorem B2211799 : Blo 1309973 2211799 := bstep (se 1 (by rfl) ⟨1658849, by rfl⟩ : syracuseStep 2211799 = 3317699) B3317699
theorem B1310699 : Blo 1309973 1310699 := bstep (se 1 (by rfl) ⟨983024, by rfl⟩ : syracuseStep 1310699 = 1966049) B1966049
theorem B2490355 : Blo 1309973 2490355 := bstep (se 1 (by rfl) ⟨1867766, by rfl⟩ : syracuseStep 2490355 = 3735533) B3735533
theorem B1310711 : Blo 1309973 1310711 := bstep (se 1 (by rfl) ⟨983033, by rfl⟩ : syracuseStep 1310711 = 1966067) B1966067
theorem B1310727 : Blo 1309973 1310727 := bstep (se 1 (by rfl) ⟨983045, by rfl⟩ : syracuseStep 1310727 = 1966091) B1966091
theorem B1310735 : Blo 1309973 1310735 := bstep (se 1 (by rfl) ⟨983051, by rfl⟩ : syracuseStep 1310735 = 1966103) B1966103
theorem B26894359 : Blo 1309973 26894359 := bstep (se 1 (by rfl) ⟨20170769, by rfl⟩ : syracuseStep 26894359 = 40341539) B40341539
theorem B8970263 : Blo 1309973 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B2490401 : Blo 1309973 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B7462955 : Blo 1309973 7462955 := bstep (se 1 (by rfl) ⟨5597216, by rfl⟩ : syracuseStep 7462955 = 11194433) B11194433
theorem B1966139 : Blo 1309973 1966139 := bstep (se 1 (by rfl) ⟨1474604, by rfl⟩ : syracuseStep 1966139 = 2949209) B2949209
theorem B1310779 : Blo 1309973 1310779 := bstep (se 1 (by rfl) ⟨983084, by rfl⟩ : syracuseStep 1310779 = 1966169) B1966169
theorem B1966199 : Blo 1309973 1966199 := bstep (se 1 (by rfl) ⟨1474649, by rfl⟩ : syracuseStep 1966199 = 2949299) B2949299
theorem B1310855 : Blo 1309973 1310855 := bstep (se 1 (by rfl) ⟨983141, by rfl⟩ : syracuseStep 1310855 = 1966283) B1966283
theorem B2695303 : Blo 1309973 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B1966223 : Blo 1309973 1966223 := bstep (se 1 (by rfl) ⟨1474667, by rfl⟩ : syracuseStep 1966223 = 2949335) B2949335
theorem B1310863 : Blo 1309973 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B1966265 : Blo 1309973 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B1310907 : Blo 1309973 1310907 := bstep (se 1 (by rfl) ⟨983180, by rfl⟩ : syracuseStep 1310907 = 1966361) B1966361
theorem B1966343 : Blo 1309973 1966343 := bstep (se 1 (by rfl) ⟨1474757, by rfl⟩ : syracuseStep 1966343 = 2949515) B2949515
theorem B1310983 : Blo 1309973 1310983 := bstep (se 1 (by rfl) ⟨983237, by rfl⟩ : syracuseStep 1310983 = 1966475) B1966475
theorem B1310991 : Blo 1309973 1310991 := bstep (se 1 (by rfl) ⟨983243, by rfl⟩ : syracuseStep 1310991 = 1966487) B1966487
theorem B3735841 : Blo 1309973 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B1966379 : Blo 1309973 1966379 := bstep (se 1 (by rfl) ⟨1474784, by rfl⟩ : syracuseStep 1966379 = 2949569) B2949569
theorem B1311035 : Blo 1309973 1311035 := bstep (se 1 (by rfl) ⟨983276, by rfl⟩ : syracuseStep 1311035 = 1966553) B1966553
theorem B1966409 : Blo 1309973 1966409 := bstep (se 2 (by rfl) ⟨737403, by rfl⟩ : syracuseStep 1966409 = 1474807) B1474807
theorem B2212231 : Blo 1309973 2212231 := bstep (se 1 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 2212231 = 3318347) B3318347
theorem B1474951 : Blo 1309973 1474951 := bstep (se 1 (by rfl) ⟨1106213, by rfl⟩ : syracuseStep 1474951 = 2212427) B2212427
theorem B1311111 : Blo 1309973 1311111 := bstep (se 1 (by rfl) ⟨983333, by rfl⟩ : syracuseStep 1311111 = 1966667) B1966667
theorem B1311119 : Blo 1309973 1311119 := bstep (se 1 (by rfl) ⟨983339, by rfl⟩ : syracuseStep 1311119 = 1966679) B1966679
theorem B1966523 : Blo 1309973 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1311163 : Blo 1309973 1311163 := bstep (se 1 (by rfl) ⟨983372, by rfl⟩ : syracuseStep 1311163 = 1966745) B1966745
theorem B1966583 : Blo 1309973 1966583 := bstep (se 1 (by rfl) ⟨1474937, by rfl⟩ : syracuseStep 1966583 = 2949875) B2949875
theorem B1311239 : Blo 1309973 1311239 := bstep (se 1 (by rfl) ⟨983429, by rfl⟩ : syracuseStep 1311239 = 1966859) B1966859
theorem B1966607 : Blo 1309973 1966607 := bstep (se 1 (by rfl) ⟨1474955, by rfl⟩ : syracuseStep 1966607 = 2949911) B2949911
theorem B1311247 : Blo 1309973 1311247 := bstep (se 1 (by rfl) ⟨983435, by rfl⟩ : syracuseStep 1311247 = 1966871) B1966871
theorem B9962027 : Blo 1309973 9962027 := bstep (se 1 (by rfl) ⟨7471520, by rfl⟩ : syracuseStep 9962027 = 14943041) B14943041
theorem B1966649 : Blo 1309973 1966649 := bstep (se 2 (by rfl) ⟨737493, by rfl⟩ : syracuseStep 1966649 = 1474987) B1474987
theorem B1475131 : Blo 1309973 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B1311291 : Blo 1309973 1311291 := bstep (se 1 (by rfl) ⟨983468, by rfl⟩ : syracuseStep 1311291 = 1966937) B1966937
theorem B7471703 : Blo 1309973 7471703 := bstep (se 1 (by rfl) ⟨5603777, by rfl⟩ : syracuseStep 7471703 = 11207555) B11207555
theorem B2949767 : Blo 1309973 2949767 := bstep (se 1 (by rfl) ⟨2212325, by rfl⟩ : syracuseStep 2949767 = 4424651) B4424651
theorem B1966727 : Blo 1309973 1966727 := bstep (se 1 (by rfl) ⟨1475045, by rfl⟩ : syracuseStep 1966727 = 2950091) B2950091
theorem B1311367 : Blo 1309973 1311367 := bstep (se 1 (by rfl) ⟨983525, by rfl⟩ : syracuseStep 1311367 = 1967051) B1967051
theorem B1311375 : Blo 1309973 1311375 := bstep (se 1 (by rfl) ⟨983531, by rfl⟩ : syracuseStep 1311375 = 1967063) B1967063
theorem B1966763 : Blo 1309973 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B1311419 : Blo 1309973 1311419 := bstep (se 1 (by rfl) ⟨983564, by rfl⟩ : syracuseStep 1311419 = 1967129) B1967129
theorem B1966793 : Blo 1309973 1966793 := bstep (se 2 (by rfl) ⟨737547, by rfl⟩ : syracuseStep 1966793 = 1475095) B1475095
theorem B4727497 : Blo 1309973 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B218170097 : Blo 1309973 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B3318529 : Blo 1309973 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B1311495 : Blo 1309973 1311495 := bstep (se 1 (by rfl) ⟨983621, by rfl⟩ : syracuseStep 1311495 = 1967243) B1967243
theorem B1311503 : Blo 1309973 1311503 := bstep (se 1 (by rfl) ⟨983627, by rfl⟩ : syracuseStep 1311503 = 1967255) B1967255
theorem B2990881 : Blo 1309973 2990881 := bstep (se 2 (by rfl) ⟨1121580, by rfl⟩ : syracuseStep 2990881 = 2243161) B2243161
theorem B2949947 : Blo 1309973 2949947 := bstep (se 1 (by rfl) ⟨2212460, by rfl⟩ : syracuseStep 2949947 = 4424921) B4424921
theorem B1966907 : Blo 1309973 1966907 := bstep (se 1 (by rfl) ⟨1475180, by rfl⟩ : syracuseStep 1966907 = 2950361) B2950361
theorem B1311547 : Blo 1309973 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B1966967 : Blo 1309973 1966967 := bstep (se 1 (by rfl) ⟨1475225, by rfl⟩ : syracuseStep 1966967 = 2950451) B2950451
theorem B1311623 : Blo 1309973 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B1966991 : Blo 1309973 1966991 := bstep (se 1 (by rfl) ⟨1475243, by rfl⟩ : syracuseStep 1966991 = 2950487) B2950487
theorem B1311631 : Blo 1309973 1311631 := bstep (se 1 (by rfl) ⟨983723, by rfl⟩ : syracuseStep 1311631 = 1967447) B1967447
theorem B2950073 : Blo 1309973 2950073 := bstep (se 2 (by rfl) ⟨1106277, by rfl⟩ : syracuseStep 2950073 = 2212555) B2212555
theorem B1967033 : Blo 1309973 1967033 := bstep (se 2 (by rfl) ⟨737637, by rfl⟩ : syracuseStep 1967033 = 1475275) B1475275
theorem B1311675 : Blo 1309973 1311675 := bstep (se 1 (by rfl) ⟨983756, by rfl⟩ : syracuseStep 1311675 = 1967513) B1967513
theorem B9954251 : Blo 1309973 9954251 := bstep (se 1 (by rfl) ⟨7465688, by rfl⟩ : syracuseStep 9954251 = 14931377) B14931377
theorem B6636491 : Blo 1309973 6636491 := bstep (se 1 (by rfl) ⟨4977368, by rfl⟩ : syracuseStep 6636491 = 9954737) B9954737
theorem B1967111 : Blo 1309973 1967111 := bstep (se 1 (by rfl) ⟨1475333, by rfl⟩ : syracuseStep 1967111 = 2950667) B2950667
theorem B1311751 : Blo 1309973 1311751 := bstep (se 1 (by rfl) ⟨983813, by rfl⟩ : syracuseStep 1311751 = 1967627) B1967627
theorem B2212879 : Blo 1309973 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B1475599 : Blo 1309973 1475599 := bstep (se 1 (by rfl) ⟨1106699, by rfl⟩ : syracuseStep 1475599 = 2213399) B2213399
theorem B1311759 : Blo 1309973 1311759 := bstep (se 1 (by rfl) ⟨983819, by rfl⟩ : syracuseStep 1311759 = 1967639) B1967639
theorem B1967147 : Blo 1309973 1967147 := bstep (se 1 (by rfl) ⟨1475360, by rfl⟩ : syracuseStep 1967147 = 2950721) B2950721
theorem B1311803 : Blo 1309973 1311803 := bstep (se 1 (by rfl) ⟨983852, by rfl⟩ : syracuseStep 1311803 = 1967705) B1967705
theorem B4375613 : Blo 1309973 4375613 := bstep (se 3 (by rfl) ⟨820427, by rfl⟩ : syracuseStep 4375613 = 1640855) B1640855
theorem B1967177 : Blo 1309973 1967177 := bstep (se 2 (by rfl) ⟨737691, by rfl⟩ : syracuseStep 1967177 = 1475383) B1475383
theorem B1311879 : Blo 1309973 1311879 := bstep (se 1 (by rfl) ⟨983909, by rfl⟩ : syracuseStep 1311879 = 1967819) B1967819
theorem B1311887 : Blo 1309973 1311887 := bstep (se 1 (by rfl) ⟨983915, by rfl⟩ : syracuseStep 1311887 = 1967831) B1967831
theorem B1967291 : Blo 1309973 1967291 := bstep (se 1 (by rfl) ⟨1475468, by rfl⟩ : syracuseStep 1967291 = 2950937) B2950937
theorem B1311931 : Blo 1309973 1311931 := bstep (se 1 (by rfl) ⟨983948, by rfl⟩ : syracuseStep 1311931 = 1967897) B1967897
theorem B5596397 : Blo 1309973 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B1967351 : Blo 1309973 1967351 := bstep (se 1 (by rfl) ⟨1475513, by rfl⟩ : syracuseStep 1967351 = 2951027) B2951027
theorem B6636815 : Blo 1309973 6636815 := bstep (se 1 (by rfl) ⟨4977611, by rfl⟩ : syracuseStep 6636815 = 9955223) B9955223
theorem B4424975 : Blo 1309973 4424975 := bstep (se 1 (by rfl) ⟨3318731, by rfl⟩ : syracuseStep 4424975 = 6637463) B6637463
theorem B2950415 : Blo 1309973 2950415 := bstep (se 1 (by rfl) ⟨2212811, by rfl⟩ : syracuseStep 2950415 = 4425623) B4425623
theorem B1967375 : Blo 1309973 1967375 := bstep (se 1 (by rfl) ⟨1475531, by rfl⟩ : syracuseStep 1967375 = 2951063) B2951063
theorem B2950433 : Blo 1309973 2950433 := bstep (se 2 (by rfl) ⟨1106412, by rfl⟩ : syracuseStep 2950433 = 2212825) B2212825
theorem B1967417 : Blo 1309973 1967417 := bstep (se 2 (by rfl) ⟨737781, by rfl⟩ : syracuseStep 1967417 = 1475563) B1475563
theorem B3319127 : Blo 1309973 3319127 := bstep (se 1 (by rfl) ⟨2489345, by rfl⟩ : syracuseStep 3319127 = 4978691) B4978691
theorem B1967495 : Blo 1309973 1967495 := bstep (se 1 (by rfl) ⟨1475621, by rfl⟩ : syracuseStep 1967495 = 2951243) B2951243
theorem B1967531 : Blo 1309973 1967531 := bstep (se 1 (by rfl) ⟨1475648, by rfl⟩ : syracuseStep 1967531 = 2951297) B2951297
theorem B1967561 : Blo 1309973 1967561 := bstep (se 2 (by rfl) ⟨737835, by rfl⟩ : syracuseStep 1967561 = 1475671) B1475671
theorem B7464413 : Blo 1309973 7464413 := bstep (se 3 (by rfl) ⟨1399577, by rfl⟩ : syracuseStep 7464413 = 2799155) B2799155
theorem B14165533 : Blo 1309973 14165533 := bstep (se 3 (by rfl) ⟨2656037, by rfl⟩ : syracuseStep 14165533 = 5312075) B5312075
theorem B4425245 : Blo 1309973 4425245 := bstep (se 3 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 4425245 = 1659467) B1659467
theorem B3319339 : Blo 1309973 3319339 := bstep (se 1 (by rfl) ⟨2489504, by rfl⟩ : syracuseStep 3319339 = 4979009) B4979009
theorem B2213419 : Blo 1309973 2213419 := bstep (se 1 (by rfl) ⟨1660064, by rfl⟩ : syracuseStep 2213419 = 3320129) B3320129
theorem B1967675 : Blo 1309973 1967675 := bstep (se 1 (by rfl) ⟨1475756, by rfl⟩ : syracuseStep 1967675 = 2951513) B2951513
theorem B5596739 : Blo 1309973 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B27264613 : Blo 1309973 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B2950775 : Blo 1309973 2950775 := bstep (se 1 (by rfl) ⟨2213081, by rfl⟩ : syracuseStep 2950775 = 4426163) B4426163
theorem B1967735 : Blo 1309973 1967735 := bstep (se 1 (by rfl) ⟨1475801, by rfl⟩ : syracuseStep 1967735 = 2951603) B2951603
theorem B1967759 : Blo 1309973 1967759 := bstep (se 1 (by rfl) ⟨1475819, by rfl⟩ : syracuseStep 1967759 = 2951639) B2951639
theorem B3319481 : Blo 1309973 3319481 := bstep (se 2 (by rfl) ⟨1244805, by rfl⟩ : syracuseStep 3319481 = 2489611) B2489611
theorem B2213561 : Blo 1309973 2213561 := bstep (se 2 (by rfl) ⟨830085, by rfl⟩ : syracuseStep 2213561 = 1660171) B1660171
theorem B1967801 : Blo 1309973 1967801 := bstep (se 2 (by rfl) ⟨737925, by rfl⟩ : syracuseStep 1967801 = 1475851) B1475851
theorem B4974317 : Blo 1309973 4974317 := bstep (se 3 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 4974317 = 1865369) B1865369
theorem B1967879 : Blo 1309973 1967879 := bstep (se 1 (by rfl) ⟨1475909, by rfl⟩ : syracuseStep 1967879 = 2951819) B2951819
theorem B3317051 : Blo 1309973 3317051 := bstep (se 1 (by rfl) ⟨2487788, by rfl⟩ : syracuseStep 3317051 = 4975577) B4975577
theorem B2950955 : Blo 1309973 2950955 := bstep (se 1 (by rfl) ⟨2213216, by rfl⟩ : syracuseStep 2950955 = 4426433) B4426433
theorem B1967915 : Blo 1309973 1967915 := bstep (se 1 (by rfl) ⟨1475936, by rfl⟩ : syracuseStep 1967915 = 2951873) B2951873
theorem B1967945 : Blo 1309973 1967945 := bstep (se 2 (by rfl) ⟨737979, by rfl⟩ : syracuseStep 1967945 = 1475959) B1475959
theorem B42510359 : Blo 1309973 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B20195351 : Blo 1309973 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B4974635 : Blo 1309973 4974635 := bstep (se 1 (by rfl) ⟨3730976, by rfl⟩ : syracuseStep 4974635 = 7461953) B7461953
theorem B2951315 : Blo 1309973 2951315 := bstep (se 1 (by rfl) ⟨2213486, by rfl⟩ : syracuseStep 2951315 = 4426973) B4426973
theorem B2951369 : Blo 1309973 2951369 := bstep (se 2 (by rfl) ⟨1106763, by rfl⟩ : syracuseStep 2951369 = 2213527) B2213527
theorem B2099515 : Blo 1309973 2099515 := bstep (se 1 (by rfl) ⟨1574636, by rfl⟩ : syracuseStep 2099515 = 3149273) B3149273
theorem B1575227 : Blo 1309973 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B6302137 : Blo 1309973 6302137 := bstep (se 2 (by rfl) ⟨2363301, by rfl⟩ : syracuseStep 6302137 = 4726603) B4726603
theorem B2099771 : Blo 1309973 2099771 := bstep (se 1 (by rfl) ⟨1574828, by rfl⟩ : syracuseStep 2099771 = 3149657) B3149657
theorem B14928461 : Blo 1309973 14928461 := bstep (se 3 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 14928461 = 5598173) B5598173
theorem B1575559 : Blo 1309973 1575559 := bstep (se 1 (by rfl) ⟨1181669, by rfl⟩ : syracuseStep 1575559 = 2363339) B2363339
theorem B3320473 : Blo 1309973 3320473 := bstep (se 2 (by rfl) ⟨1245177, by rfl⟩ : syracuseStep 3320473 = 2490355) B2490355
theorem B6638273 : Blo 1309973 6638273 := bstep (se 2 (by rfl) ⟨2489352, by rfl⟩ : syracuseStep 6638273 = 4978705) B4978705
theorem B2362127 : Blo 1309973 2362127 := bstep (se 1 (by rfl) ⟨1771595, by rfl⟩ : syracuseStep 2362127 = 3543191) B3543191
theorem B3320635 : Blo 1309973 3320635 := bstep (se 1 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 3320635 = 4980953) B4980953
theorem B7670663 : Blo 1309973 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B4426649 : Blo 1309973 4426649 := bstep (se 2 (by rfl) ⟨1659993, by rfl⟩ : syracuseStep 4426649 = 3319987) B3319987
theorem B3320777 : Blo 1309973 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B3730475 : Blo 1309973 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B1657999 : Blo 1309973 1657999 := bstep (se 1 (by rfl) ⟨1243499, by rfl⟩ : syracuseStep 1657999 = 2486999) B2486999
theorem B51064123 : Blo 1309973 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B1658171 : Blo 1309973 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B16166279 : Blo 1309973 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B5672339 : Blo 1309973 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B5041693 : Blo 1309973 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B15945281 : Blo 1309973 15945281 := bstep (se 2 (by rfl) ⟨5979480, by rfl⟩ : syracuseStep 15945281 = 11958961) B11958961
theorem B3984983 : Blo 1309973 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B4427351 : Blo 1309973 4427351 := bstep (se 1 (by rfl) ⟨3320513, by rfl⟩ : syracuseStep 4427351 = 6641027) B6641027
theorem B2101007 : Blo 1309973 2101007 := bstep (se 1 (by rfl) ⟨1575755, by rfl⟩ : syracuseStep 2101007 = 3151511) B3151511
theorem B57438001 : Blo 1309973 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B3542899 : Blo 1309973 3542899 := bstep (se 1 (by rfl) ⟨2657174, by rfl⟩ : syracuseStep 3542899 = 5314349) B5314349
theorem B6639569 : Blo 1309973 6639569 := bstep (se 2 (by rfl) ⟨2489838, by rfl⟩ : syracuseStep 6639569 = 4979677) B4979677
theorem B7467011 : Blo 1309973 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B3731467 : Blo 1309973 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B21245975 : Blo 1309973 21245975 := bstep (se 1 (by rfl) ⟨15934481, by rfl⟩ : syracuseStep 21245975 = 31868963) B31868963
theorem B3149857 : Blo 1309973 3149857 := bstep (se 2 (by rfl) ⟨1181196, by rfl⟩ : syracuseStep 3149857 = 2362393) B2362393
theorem B4427837 : Blo 1309973 4427837 := bstep (se 3 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 4427837 = 1660439) B1660439
theorem B6295639 : Blo 1309973 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B1659143 : Blo 1309973 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B3731741 : Blo 1309973 3731741 := bstep (se 3 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 3731741 = 1399403) B1399403
theorem B11350493 : Blo 1309973 11350493 := bstep (se 3 (by rfl) ⟨2128217, by rfl⟩ : syracuseStep 11350493 = 4256435) B4256435
theorem B16806365 : Blo 1309973 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B25186859 : Blo 1309973 25186859 := bstep (se 1 (by rfl) ⟨18890144, by rfl⟩ : syracuseStep 25186859 = 37780289) B37780289
theorem B14938667 : Blo 1309973 14938667 := bstep (se 1 (by rfl) ⟨11204000, by rfl⟩ : syracuseStep 14938667 = 22408001) B22408001
theorem B15946307 : Blo 1309973 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B6296237 : Blo 1309973 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1577659 : Blo 1309973 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B12120833 : Blo 1309973 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B1659791 : Blo 1309973 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B3986491 : Blo 1309973 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B15340661 : Blo 1309973 15340661 := bstep (se 5 (by rfl) ⟨719093, by rfl⟩ : syracuseStep 15340661 = 1438187) B1438187
theorem B4724153 : Blo 1309973 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B4978205 : Blo 1309973 4978205 := bstep (se 3 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 4978205 = 1866827) B1866827
theorem B4978219 : Blo 1309973 4978219 := bstep (se 1 (by rfl) ⟨3733664, by rfl⟩ : syracuseStep 4978219 = 7467329) B7467329
theorem B2488009 : Blo 1309973 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B139917131 : Blo 1309973 139917131 := bstep (se 1 (by rfl) ⟨104937848, by rfl⟩ : syracuseStep 139917131 = 209875697) B209875697
theorem B18904907 : Blo 1309973 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B3151703 : Blo 1309973 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B9451417 : Blo 1309973 9451417 := bstep (se 2 (by rfl) ⟨3544281, by rfl⟩ : syracuseStep 9451417 = 7088563) B7088563
theorem B2242505 : Blo 1309973 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B6641675 : Blo 1309973 6641675 := bstep (se 1 (by rfl) ⟨4981256, by rfl⟩ : syracuseStep 6641675 = 9962513) B9962513
theorem B3151991 : Blo 1309973 3151991 := bstep (se 1 (by rfl) ⟨2363993, by rfl⟩ : syracuseStep 3151991 = 4727987) B4727987
theorem B9959597 : Blo 1309973 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B6641837 : Blo 1309973 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B45431057 : Blo 1309973 45431057 := bstep (se 2 (by rfl) ⟨17036646, by rfl⟩ : syracuseStep 45431057 = 34073293) B34073293
theorem B7461179 : Blo 1309973 7461179 := bstep (se 1 (by rfl) ⟨5595884, by rfl⟩ : syracuseStep 7461179 = 11191769) B11191769
theorem B3733847 : Blo 1309973 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B2947463 : Blo 1309973 2947463 := bstep (se 1 (by rfl) ⟨2210597, by rfl⟩ : syracuseStep 2947463 = 4421195) B4421195
theorem B18897299 : Blo 1309973 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B11196893 : Blo 1309973 11196893 := bstep (se 3 (by rfl) ⟨2099417, by rfl⟩ : syracuseStep 11196893 = 4198835) B4198835
theorem B22403627 : Blo 1309973 22403627 := bstep (se 1 (by rfl) ⟨16802720, by rfl⟩ : syracuseStep 22403627 = 33605441) B33605441
theorem B4610603 : Blo 1309973 4610603 := bstep (se 1 (by rfl) ⟨3457952, by rfl⟩ : syracuseStep 4610603 = 6915905) B6915905
theorem B2947643 : Blo 1309973 2947643 := bstep (se 1 (by rfl) ⟨2210732, by rfl⟩ : syracuseStep 2947643 = 4421465) B4421465
theorem B3734075 : Blo 1309973 3734075 := bstep (se 1 (by rfl) ⟨2800556, by rfl⟩ : syracuseStep 3734075 = 5601113) B5601113
theorem B9951821 : Blo 1309973 9951821 := bstep (se 3 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 9951821 = 3731933) B3731933
theorem B2947769 : Blo 1309973 2947769 := bstep (se 2 (by rfl) ⟨1105413, by rfl⟩ : syracuseStep 2947769 = 2210827) B2210827
theorem B3734201 : Blo 1309973 3734201 := bstep (se 2 (by rfl) ⟨1400325, by rfl⟩ : syracuseStep 3734201 = 2800651) B2800651
theorem B3545785 : Blo 1309973 3545785 := bstep (se 2 (by rfl) ⟨1329669, by rfl⟩ : syracuseStep 3545785 = 2659339) B2659339
theorem B25197317 : Blo 1309973 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B6634385 : Blo 1309973 6634385 := bstep (se 2 (by rfl) ⟨2487894, by rfl⟩ : syracuseStep 6634385 = 4975789) B4975789
theorem B1964987 : Blo 1309973 1964987 := bstep (se 1 (by rfl) ⟨1473740, by rfl⟩ : syracuseStep 1964987 = 2947481) B2947481
theorem B1965047 : Blo 1309973 1965047 := bstep (se 1 (by rfl) ⟨1473785, by rfl⟩ : syracuseStep 1965047 = 2947571) B2947571
theorem B3316747 : Blo 1309973 3316747 := bstep (se 1 (by rfl) ⟨2487560, by rfl⟩ : syracuseStep 3316747 = 4975121) B4975121
theorem B1965071 : Blo 1309973 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B2948111 : Blo 1309973 2948111 := bstep (se 1 (by rfl) ⟨2211083, by rfl⟩ : syracuseStep 2948111 = 4422167) B4422167
theorem B2948129 : Blo 1309973 2948129 := bstep (se 2 (by rfl) ⟨1105548, by rfl⟩ : syracuseStep 2948129 = 2211097) B2211097
theorem B16170029 : Blo 1309973 16170029 := bstep (se 3 (by rfl) ⟨3031880, by rfl⟩ : syracuseStep 16170029 = 6063761) B6063761
theorem B1965113 : Blo 1309973 1965113 := bstep (se 2 (by rfl) ⟨736917, by rfl⟩ : syracuseStep 1965113 = 1473835) B1473835
theorem B22412375 : Blo 1309973 22412375 := bstep (se 1 (by rfl) ⟨16809281, by rfl⟩ : syracuseStep 22412375 = 33618563) B33618563
theorem B2210935 : Blo 1309973 2210935 := bstep (se 1 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 2210935 = 3316403) B3316403
theorem B1965191 : Blo 1309973 1965191 := bstep (se 1 (by rfl) ⟨1473893, by rfl⟩ : syracuseStep 1965191 = 2947787) B2947787
theorem B3316889 : Blo 1309973 3316889 := bstep (se 2 (by rfl) ⟨1243833, by rfl⟩ : syracuseStep 3316889 = 2487667) B2487667
theorem B1965227 : Blo 1309973 1965227 := bstep (se 1 (by rfl) ⟨1473920, by rfl⟩ : syracuseStep 1965227 = 2947841) B2947841
theorem B1965257 : Blo 1309973 1965257 := bstep (se 2 (by rfl) ⟨736971, by rfl⟩ : syracuseStep 1965257 = 1473943) B1473943
theorem B1473799 : Blo 1309973 1473799 := bstep (se 1 (by rfl) ⟨1105349, by rfl⟩ : syracuseStep 1473799 = 2210699) B2210699
theorem B2522411 : Blo 1309973 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B2211131 : Blo 1309973 2211131 := bstep (se 1 (by rfl) ⟨1658348, by rfl⟩ : syracuseStep 2211131 = 3316697) B3316697
theorem B1310011 : Blo 1309973 1310011 := bstep (se 1 (by rfl) ⟨982508, by rfl⟩ : syracuseStep 1310011 = 1965017) B1965017
theorem B1965371 : Blo 1309973 1965371 := bstep (se 1 (by rfl) ⟨1474028, by rfl⟩ : syracuseStep 1965371 = 2948057) B2948057
theorem B1965431 : Blo 1309973 1965431 := bstep (se 1 (by rfl) ⟨1474073, by rfl⟩ : syracuseStep 1965431 = 2948147) B2948147
theorem B2948471 : Blo 1309973 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B1310087 : Blo 1309973 1310087 := bstep (se 1 (by rfl) ⟨982565, by rfl⟩ : syracuseStep 1310087 = 1965131) B1965131
theorem B1310095 : Blo 1309973 1310095 := bstep (se 1 (by rfl) ⟨982571, by rfl⟩ : syracuseStep 1310095 = 1965143) B1965143
theorem B1965455 : Blo 1309973 1965455 := bstep (se 1 (by rfl) ⟨1474091, by rfl⟩ : syracuseStep 1965455 = 2948183) B2948183
theorem B1965497 : Blo 1309973 1965497 := bstep (se 2 (by rfl) ⟨737061, by rfl⟩ : syracuseStep 1965497 = 1474123) B1474123
theorem B1310139 : Blo 1309973 1310139 := bstep (se 1 (by rfl) ⟨982604, by rfl⟩ : syracuseStep 1310139 = 1965209) B1965209
theorem B1473979 : Blo 1309973 1473979 := bstep (se 1 (by rfl) ⟨1105484, by rfl⟩ : syracuseStep 1473979 = 2210969) B2210969
theorem B1310215 : Blo 1309973 1310215 := bstep (se 1 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 1310215 = 1965323) B1965323
theorem B1965575 : Blo 1309973 1965575 := bstep (se 1 (by rfl) ⟨1474181, by rfl⟩ : syracuseStep 1965575 = 2948363) B2948363
theorem B1310223 : Blo 1309973 1310223 := bstep (se 1 (by rfl) ⟨982667, by rfl⟩ : syracuseStep 1310223 = 1965335) B1965335
theorem B1596943 : Blo 1309973 1596943 := bstep (se 1 (by rfl) ⟨1197707, by rfl⟩ : syracuseStep 1596943 = 2395415) B2395415
theorem B1965611 : Blo 1309973 1965611 := bstep (se 1 (by rfl) ⟨1474208, by rfl⟩ : syracuseStep 1965611 = 2948417) B2948417
theorem B2948651 : Blo 1309973 2948651 := bstep (se 1 (by rfl) ⟨2211488, by rfl⟩ : syracuseStep 2948651 = 4422977) B4422977
theorem B1310267 : Blo 1309973 1310267 := bstep (se 1 (by rfl) ⟨982700, by rfl⟩ : syracuseStep 1310267 = 1965401) B1965401
theorem B2489915 : Blo 1309973 2489915 := bstep (se 1 (by rfl) ⟨1867436, by rfl⟩ : syracuseStep 2489915 = 3734873) B3734873
theorem B1965641 : Blo 1309973 1965641 := bstep (se 2 (by rfl) ⟨737115, by rfl⟩ : syracuseStep 1965641 = 1474231) B1474231
theorem B1310343 : Blo 1309973 1310343 := bstep (se 1 (by rfl) ⟨982757, by rfl⟩ : syracuseStep 1310343 = 1965515) B1965515
theorem B1310351 : Blo 1309973 1310351 := bstep (se 1 (by rfl) ⟨982763, by rfl⟩ : syracuseStep 1310351 = 1965527) B1965527
theorem B3317395 : Blo 1309973 3317395 := bstep (se 1 (by rfl) ⟨2488046, by rfl⟩ : syracuseStep 3317395 = 4976093) B4976093
theorem B1310395 : Blo 1309973 1310395 := bstep (se 1 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 1310395 = 1965593) B1965593
theorem B1965755 : Blo 1309973 1965755 := bstep (se 1 (by rfl) ⟨1474316, by rfl⟩ : syracuseStep 1965755 = 2948633) B2948633
theorem B2211529 : Blo 1309973 2211529 := bstep (se 2 (by rfl) ⟨829323, by rfl⟩ : syracuseStep 2211529 = 1658647) B1658647
theorem B1867465 : Blo 1309973 1867465 := bstep (se 2 (by rfl) ⟨700299, by rfl⟩ : syracuseStep 1867465 = 1400599) B1400599
theorem B7462637 : Blo 1309973 7462637 := bstep (se 3 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 7462637 = 2798489) B2798489
theorem B1965815 : Blo 1309973 1965815 := bstep (se 1 (by rfl) ⟨1474361, by rfl⟩ : syracuseStep 1965815 = 2948723) B2948723
theorem B1310471 : Blo 1309973 1310471 := bstep (se 1 (by rfl) ⟨982853, by rfl⟩ : syracuseStep 1310471 = 1965707) B1965707
theorem B1310479 : Blo 1309973 1310479 := bstep (se 1 (by rfl) ⟨982859, by rfl⟩ : syracuseStep 1310479 = 1965719) B1965719
theorem B1965839 : Blo 1309973 1965839 := bstep (se 1 (by rfl) ⟨1474379, by rfl⟩ : syracuseStep 1965839 = 2948759) B2948759
theorem B12779279 : Blo 1309973 12779279 := bstep (se 1 (by rfl) ⟨9584459, by rfl⟩ : syracuseStep 12779279 = 19168919) B19168919
theorem B3317537 : Blo 1309973 3317537 := bstep (se 2 (by rfl) ⟨1244076, by rfl⟩ : syracuseStep 3317537 = 2488153) B2488153
theorem B1965881 : Blo 1309973 1965881 := bstep (se 2 (by rfl) ⟨737205, by rfl⟩ : syracuseStep 1965881 = 1474411) B1474411
theorem B1310523 : Blo 1309973 1310523 := bstep (se 1 (by rfl) ⟨982892, by rfl⟩ : syracuseStep 1310523 = 1965785) B1965785
theorem B1310599 : Blo 1309973 1310599 := bstep (se 1 (by rfl) ⟨982949, by rfl⟩ : syracuseStep 1310599 = 1965899) B1965899
theorem B1965959 : Blo 1309973 1965959 := bstep (se 1 (by rfl) ⟨1474469, by rfl⟩ : syracuseStep 1965959 = 2948939) B2948939
theorem B1310607 : Blo 1309973 1310607 := bstep (se 1 (by rfl) ⟨982955, by rfl⟩ : syracuseStep 1310607 = 1965911) B1965911
theorem B1474447 : Blo 1309973 1474447 := bstep (se 1 (by rfl) ⟨1105835, by rfl⟩ : syracuseStep 1474447 = 2211671) B2211671
theorem B2949011 : Blo 1309973 2949011 := bstep (se 1 (by rfl) ⟨2211758, by rfl⟩ : syracuseStep 2949011 = 4423517) B4423517
theorem B4423571 : Blo 1309973 4423571 := bstep (se 1 (by rfl) ⟨3317678, by rfl⟩ : syracuseStep 4423571 = 6635357) B6635357
theorem B28737431 : Blo 1309973 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B1965995 : Blo 1309973 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B1310651 : Blo 1309973 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B1966025 : Blo 1309973 1966025 := bstep (se 2 (by rfl) ⟨737259, by rfl⟩ : syracuseStep 1966025 = 1474519) B1474519
theorem B2949065 : Blo 1309973 2949065 := bstep (se 2 (by rfl) ⟨1105899, by rfl⟩ : syracuseStep 2949065 = 2211799) B2211799
theorem B14163983 : Blo 1309973 14163983 := bstep (se 1 (by rfl) ⟨10622987, by rfl⟩ : syracuseStep 14163983 = 21245975) B21245975
theorem B5980175 : Blo 1309973 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1310759 : Blo 1309973 1310759 := bstep (se 1 (by rfl) ⟨983069, by rfl⟩ : syracuseStep 1310759 = 1966139) B1966139
theorem B1310799 : Blo 1309973 1310799 := bstep (se 1 (by rfl) ⟨983099, by rfl⟩ : syracuseStep 1310799 = 1966199) B1966199
theorem B1310815 : Blo 1309973 1310815 := bstep (se 1 (by rfl) ⟨983111, by rfl⟩ : syracuseStep 1310815 = 1966223) B1966223
theorem B1310843 : Blo 1309973 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B1310895 : Blo 1309973 1310895 := bstep (se 1 (by rfl) ⟨983171, by rfl⟩ : syracuseStep 1310895 = 1966343) B1966343
theorem B1310919 : Blo 1309973 1310919 := bstep (se 1 (by rfl) ⟨983189, by rfl⟩ : syracuseStep 1310919 = 1966379) B1966379
theorem B1310939 : Blo 1309973 1310939 := bstep (se 1 (by rfl) ⟨983204, by rfl⟩ : syracuseStep 1310939 = 1966409) B1966409
theorem B1311015 : Blo 1309973 1311015 := bstep (se 1 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 1311015 = 1966523) B1966523
theorem B8405309 : Blo 1309973 8405309 := bstep (se 3 (by rfl) ⟨1575995, by rfl⟩ : syracuseStep 8405309 = 3151991) B3151991
theorem B1311055 : Blo 1309973 1311055 := bstep (se 1 (by rfl) ⟨983291, by rfl⟩ : syracuseStep 1311055 = 1966583) B1966583
theorem B1311071 : Blo 1309973 1311071 := bstep (se 1 (by rfl) ⟨983303, by rfl⟩ : syracuseStep 1311071 = 1966607) B1966607
theorem B1311099 : Blo 1309973 1311099 := bstep (se 1 (by rfl) ⟨983324, by rfl⟩ : syracuseStep 1311099 = 1966649) B1966649
theorem B4981121 : Blo 1309973 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B4981135 : Blo 1309973 4981135 := bstep (se 1 (by rfl) ⟨3735851, by rfl⟩ : syracuseStep 4981135 = 7471703) B7471703
theorem B1966511 : Blo 1309973 1966511 := bstep (se 1 (by rfl) ⟨1474883, by rfl⟩ : syracuseStep 1966511 = 2949767) B2949767
theorem B1311151 : Blo 1309973 1311151 := bstep (se 1 (by rfl) ⟨983363, by rfl⟩ : syracuseStep 1311151 = 1966727) B1966727
theorem B1311175 : Blo 1309973 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B1311195 : Blo 1309973 1311195 := bstep (se 1 (by rfl) ⟨983396, by rfl⟩ : syracuseStep 1311195 = 1966793) B1966793
theorem B2949641 : Blo 1309973 2949641 := bstep (se 2 (by rfl) ⟨1106115, by rfl⟩ : syracuseStep 2949641 = 2212231) B2212231
theorem B1966601 : Blo 1309973 1966601 := bstep (se 2 (by rfl) ⟨737475, by rfl⟩ : syracuseStep 1966601 = 1474951) B1474951
theorem B1966631 : Blo 1309973 1966631 := bstep (se 1 (by rfl) ⟨1474973, by rfl⟩ : syracuseStep 1966631 = 2949947) B2949947
theorem B1311271 : Blo 1309973 1311271 := bstep (se 1 (by rfl) ⟨983453, by rfl⟩ : syracuseStep 1311271 = 1966907) B1966907
theorem B1311311 : Blo 1309973 1311311 := bstep (se 1 (by rfl) ⟨983483, by rfl⟩ : syracuseStep 1311311 = 1966967) B1966967
theorem B1311327 : Blo 1309973 1311327 := bstep (se 1 (by rfl) ⟨983495, by rfl⟩ : syracuseStep 1311327 = 1966991) B1966991
theorem B1966715 : Blo 1309973 1966715 := bstep (se 1 (by rfl) ⟨1475036, by rfl⟩ : syracuseStep 1966715 = 2950073) B2950073
theorem B1311355 : Blo 1309973 1311355 := bstep (se 1 (by rfl) ⟨983516, by rfl⟩ : syracuseStep 1311355 = 1967033) B1967033
theorem B6636167 : Blo 1309973 6636167 := bstep (se 1 (by rfl) ⟨4977125, by rfl⟩ : syracuseStep 6636167 = 9954251) B9954251
theorem B4424327 : Blo 1309973 4424327 := bstep (se 1 (by rfl) ⟨3318245, by rfl⟩ : syracuseStep 4424327 = 6636491) B6636491
theorem B1311407 : Blo 1309973 1311407 := bstep (se 1 (by rfl) ⟨983555, by rfl⟩ : syracuseStep 1311407 = 1967111) B1967111
theorem B4424381 : Blo 1309973 4424381 := bstep (se 3 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 4424381 = 1659143) B1659143
theorem B1311431 : Blo 1309973 1311431 := bstep (se 1 (by rfl) ⟨983573, by rfl⟩ : syracuseStep 1311431 = 1967147) B1967147
theorem B2917075 : Blo 1309973 2917075 := bstep (se 1 (by rfl) ⟨2187806, by rfl⟩ : syracuseStep 2917075 = 4375613) B4375613
theorem B1311451 : Blo 1309973 1311451 := bstep (se 1 (by rfl) ⟨983588, by rfl⟩ : syracuseStep 1311451 = 1967177) B1967177
theorem B1966841 : Blo 1309973 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B1311527 : Blo 1309973 1311527 := bstep (se 1 (by rfl) ⟨983645, by rfl⟩ : syracuseStep 1311527 = 1967291) B1967291
theorem B1311567 : Blo 1309973 1311567 := bstep (se 1 (by rfl) ⟨983675, by rfl⟩ : syracuseStep 1311567 = 1967351) B1967351
theorem B4424543 : Blo 1309973 4424543 := bstep (se 1 (by rfl) ⟨3318407, by rfl⟩ : syracuseStep 4424543 = 6636815) B6636815
theorem B2949983 : Blo 1309973 2949983 := bstep (se 1 (by rfl) ⟨2212487, by rfl⟩ : syracuseStep 2949983 = 4424975) B4424975
theorem B1966943 : Blo 1309973 1966943 := bstep (se 1 (by rfl) ⟨1475207, by rfl⟩ : syracuseStep 1966943 = 2950415) B2950415
theorem B1311583 : Blo 1309973 1311583 := bstep (se 1 (by rfl) ⟨983687, by rfl⟩ : syracuseStep 1311583 = 1967375) B1967375
theorem B1966955 : Blo 1309973 1966955 := bstep (se 1 (by rfl) ⟨1475216, by rfl⟩ : syracuseStep 1966955 = 2950433) B2950433
theorem B1311611 : Blo 1309973 1311611 := bstep (se 1 (by rfl) ⟨983708, by rfl⟩ : syracuseStep 1311611 = 1967417) B1967417
theorem B2212751 : Blo 1309973 2212751 := bstep (se 1 (by rfl) ⟨1659563, by rfl⟩ : syracuseStep 2212751 = 3319127) B3319127
theorem B1311663 : Blo 1309973 1311663 := bstep (se 1 (by rfl) ⟨983747, by rfl⟩ : syracuseStep 1311663 = 1967495) B1967495
theorem B1311687 : Blo 1309973 1311687 := bstep (se 1 (by rfl) ⟨983765, by rfl⟩ : syracuseStep 1311687 = 1967531) B1967531
theorem B1311707 : Blo 1309973 1311707 := bstep (se 1 (by rfl) ⟨983780, by rfl⟩ : syracuseStep 1311707 = 1967561) B1967561
theorem B4424705 : Blo 1309973 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B3318803 : Blo 1309973 3318803 := bstep (se 1 (by rfl) ⟨2489102, by rfl⟩ : syracuseStep 3318803 = 4978205) B4978205
theorem B2950163 : Blo 1309973 2950163 := bstep (se 1 (by rfl) ⟨2212622, by rfl⟩ : syracuseStep 2950163 = 4425245) B4425245
theorem B1311783 : Blo 1309973 1311783 := bstep (se 1 (by rfl) ⟨983837, by rfl⟩ : syracuseStep 1311783 = 1967675) B1967675
theorem B1967183 : Blo 1309973 1967183 := bstep (se 1 (by rfl) ⟨1475387, by rfl⟩ : syracuseStep 1967183 = 2950775) B2950775
theorem B1311823 : Blo 1309973 1311823 := bstep (se 1 (by rfl) ⟨983867, by rfl⟩ : syracuseStep 1311823 = 1967735) B1967735
theorem B1311839 : Blo 1309973 1311839 := bstep (se 1 (by rfl) ⟨983879, by rfl⟩ : syracuseStep 1311839 = 1967759) B1967759
theorem B2212987 : Blo 1309973 2212987 := bstep (se 1 (by rfl) ⟨1659740, by rfl⟩ : syracuseStep 2212987 = 3319481) B3319481
theorem B1475707 : Blo 1309973 1475707 := bstep (se 1 (by rfl) ⟨1106780, by rfl⟩ : syracuseStep 1475707 = 2213561) B2213561
theorem B1311867 : Blo 1309973 1311867 := bstep (se 1 (by rfl) ⟨983900, by rfl⟩ : syracuseStep 1311867 = 1967801) B1967801
theorem B1311919 : Blo 1309973 1311919 := bstep (se 1 (by rfl) ⟨983939, by rfl⟩ : syracuseStep 1311919 = 1967879) B1967879
theorem B1967303 : Blo 1309973 1967303 := bstep (se 1 (by rfl) ⟨1475477, by rfl⟩ : syracuseStep 1967303 = 2950955) B2950955
theorem B1311943 : Blo 1309973 1311943 := bstep (se 1 (by rfl) ⟨983957, by rfl⟩ : syracuseStep 1311943 = 1967915) B1967915
theorem B1311963 : Blo 1309973 1311963 := bstep (se 1 (by rfl) ⟨983972, by rfl⟩ : syracuseStep 1311963 = 1967945) B1967945
theorem B2950505 : Blo 1309973 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B1967465 : Blo 1309973 1967465 := bstep (se 2 (by rfl) ⟨737799, by rfl⟩ : syracuseStep 1967465 = 1475599) B1475599
theorem B1967543 : Blo 1309973 1967543 := bstep (se 1 (by rfl) ⟨1475657, by rfl⟩ : syracuseStep 1967543 = 2951315) B2951315
theorem B1967579 : Blo 1309973 1967579 := bstep (se 1 (by rfl) ⟨1475684, by rfl⟩ : syracuseStep 1967579 = 2951369) B2951369
theorem B30287371 : Blo 1309973 30287371 := bstep (se 1 (by rfl) ⟨22715528, by rfl⟩ : syracuseStep 30287371 = 45431057) B45431057
theorem B4974119 : Blo 1309973 4974119 := bstep (se 1 (by rfl) ⟨3730589, by rfl⟩ : syracuseStep 4974119 = 7461179) B7461179
theorem B7464595 : Blo 1309973 7464595 := bstep (se 1 (by rfl) ⟨5598446, by rfl⟩ : syracuseStep 7464595 = 11196893) B11196893
theorem B14935751 : Blo 1309973 14935751 := bstep (se 1 (by rfl) ⟨11201813, by rfl⟩ : syracuseStep 14935751 = 22403627) B22403627
theorem B3073735 : Blo 1309973 3073735 := bstep (se 1 (by rfl) ⟨2305301, by rfl⟩ : syracuseStep 3073735 = 4610603) B4610603
theorem B68085497 : Blo 1309973 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B4425515 : Blo 1309973 4425515 := bstep (se 1 (by rfl) ⟨3319136, by rfl⟩ : syracuseStep 4425515 = 6638273) B6638273
theorem B5113775 : Blo 1309973 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B2951099 : Blo 1309973 2951099 := bstep (se 1 (by rfl) ⟨2213324, by rfl⟩ : syracuseStep 2951099 = 4426649) B4426649
theorem B2213851 : Blo 1309973 2213851 := bstep (se 1 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 2213851 = 3320777) B3320777
theorem B6637625 : Blo 1309973 6637625 := bstep (se 2 (by rfl) ⟨2489109, by rfl⟩ : syracuseStep 6637625 = 4978219) B4978219
theorem B4425785 : Blo 1309973 4425785 := bstep (se 2 (by rfl) ⟨1659669, by rfl⟩ : syracuseStep 4425785 = 3319339) B3319339
theorem B2951225 : Blo 1309973 2951225 := bstep (se 2 (by rfl) ⟨1106709, by rfl⟩ : syracuseStep 2951225 = 2213419) B2213419
theorem B1681607 : Blo 1309973 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B4426109 : Blo 1309973 4426109 := bstep (se 3 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 4426109 = 1659791) B1659791
theorem B2656655 : Blo 1309973 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B2951567 : Blo 1309973 2951567 := bstep (se 1 (by rfl) ⟨2213675, by rfl⟩ : syracuseStep 2951567 = 4427351) B4427351
theorem B4975091 : Blo 1309973 4975091 := bstep (se 1 (by rfl) ⟨3731318, by rfl⟩ : syracuseStep 4975091 = 7462637) B7462637
theorem B12601889 : Blo 1309973 12601889 := bstep (se 2 (by rfl) ⟨4725708, by rfl⟩ : syracuseStep 12601889 = 9451417) B9451417
theorem B4426379 : Blo 1309973 4426379 := bstep (se 1 (by rfl) ⟨3319784, by rfl⟩ : syracuseStep 4426379 = 6639569) B6639569
theorem B4975289 : Blo 1309973 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B4975303 : Blo 1309973 4975303 := bstep (se 1 (by rfl) ⟨3731477, by rfl⟩ : syracuseStep 4975303 = 7462955) B7462955
theorem B35859145 : Blo 1309973 35859145 := bstep (se 2 (by rfl) ⟨13447179, by rfl⟩ : syracuseStep 35859145 = 26894359) B26894359
theorem B2951891 : Blo 1309973 2951891 := bstep (se 1 (by rfl) ⟨2213918, by rfl⟩ : syracuseStep 2951891 = 4427837) B4427837
theorem B9947933 : Blo 1309973 9947933 := bstep (se 3 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 9947933 = 3730475) B3730475
theorem B26889029 : Blo 1309973 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B4197491 : Blo 1309973 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B8080555 : Blo 1309973 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B10227107 : Blo 1309973 10227107 := bstep (se 1 (by rfl) ⟨7670330, by rfl⟩ : syracuseStep 10227107 = 15340661) B15340661
theorem B3730931 : Blo 1309973 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B2100745 : Blo 1309973 2100745 := bstep (se 2 (by rfl) ⟨787779, by rfl⟩ : syracuseStep 2100745 = 1575559) B1575559
theorem B4427297 : Blo 1309973 4427297 := bstep (se 2 (by rfl) ⟨1660236, by rfl⟩ : syracuseStep 4427297 = 3320473) B3320473
theorem B6303329 : Blo 1309973 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B3149435 : Blo 1309973 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B18910853 : Blo 1309973 18910853 := bstep (se 4 (by rfl) ⟨1772892, by rfl⟩ : syracuseStep 18910853 = 3545785) B3545785
theorem B4976275 : Blo 1309973 4976275 := bstep (se 1 (by rfl) ⟨3732206, by rfl⟩ : syracuseStep 4976275 = 7464413) B7464413
theorem B3731159 : Blo 1309973 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B4427513 : Blo 1309973 4427513 := bstep (se 2 (by rfl) ⟨1660317, by rfl⟩ : syracuseStep 4427513 = 3320635) B3320635
theorem B93278087 : Blo 1309973 93278087 := bstep (se 1 (by rfl) ⟨69958565, by rfl⟩ : syracuseStep 93278087 = 139917131) B139917131
theorem B12603271 : Blo 1309973 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B2101135 : Blo 1309973 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B1495003 : Blo 1309973 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B4427783 : Blo 1309973 4427783 := bstep (se 1 (by rfl) ⟨3320837, by rfl⟩ : syracuseStep 4427783 = 6641675) B6641675
theorem B28340239 : Blo 1309973 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B13463567 : Blo 1309973 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B6639731 : Blo 1309973 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B4427891 : Blo 1309973 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B16798211 : Blo 1309973 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B18887377 : Blo 1309973 18887377 := bstep (se 2 (by rfl) ⟨7082766, by rfl⟩ : syracuseStep 18887377 = 14165533) B14165533
theorem B36352817 : Blo 1309973 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B10777519 : Blo 1309973 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B3781559 : Blo 1309973 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B1659943 : Blo 1309973 1659943 := bstep (se 1 (by rfl) ⟨1244957, by rfl⟩ : syracuseStep 1659943 = 2489915) B2489915
theorem B10630187 : Blo 1309973 10630187 := bstep (se 1 (by rfl) ⟨7972640, by rfl⟩ : syracuseStep 10630187 = 15945281) B15945281
theorem B76584001 : Blo 1309973 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B4723865 : Blo 1309973 4723865 := bstep (se 2 (by rfl) ⟨1771449, by rfl⟩ : syracuseStep 4723865 = 3542899) B3542899
theorem B19158287 : Blo 1309973 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B4978007 : Blo 1309973 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B1660267 : Blo 1309973 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B8394185 : Blo 1309973 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B16799237 : Blo 1309973 16799237 := bstep (se 4 (by rfl) ⟨1574928, by rfl⟩ : syracuseStep 16799237 = 3149857) B3149857
theorem B3593737 : Blo 1309973 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B2487827 : Blo 1309973 2487827 := bstep (se 1 (by rfl) ⟨1865870, by rfl⟩ : syracuseStep 2487827 = 3731741) B3731741
theorem B7566995 : Blo 1309973 7566995 := bstep (se 1 (by rfl) ⟨5675246, by rfl⟩ : syracuseStep 7566995 = 11350493) B11350493
theorem B11204243 : Blo 1309973 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B16791239 : Blo 1309973 16791239 := bstep (se 1 (by rfl) ⟨12593429, by rfl⟩ : syracuseStep 16791239 = 25186859) B25186859
theorem B9959111 : Blo 1309973 9959111 := bstep (se 1 (by rfl) ⟨7469333, by rfl⟩ : syracuseStep 9959111 = 14938667) B14938667
theorem B6641351 : Blo 1309973 6641351 := bstep (se 1 (by rfl) ⟨4981013, by rfl⟩ : syracuseStep 6641351 = 9962027) B9962027
theorem B10630871 : Blo 1309973 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B2799353 : Blo 1309973 2799353 := bstep (se 2 (by rfl) ⟨1049757, by rfl⟩ : syracuseStep 2799353 = 2099515) B2099515
theorem B10780019 : Blo 1309973 10780019 := bstep (se 1 (by rfl) ⟨8085014, by rfl⟩ : syracuseStep 10780019 = 16170029) B16170029
theorem B145446731 : Blo 1309973 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B8402849 : Blo 1309973 8402849 := bstep (se 2 (by rfl) ⟨3151068, by rfl⟩ : syracuseStep 8402849 = 6302137) B6302137
theorem B4421789 : Blo 1309973 4421789 := bstep (se 3 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 4421789 = 1658171) B1658171
theorem B4200605 : Blo 1309973 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B2103545 : Blo 1309973 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B3987841 : Blo 1309973 3987841 := bstep (se 2 (by rfl) ⟨1495440, by rfl⟩ : syracuseStep 3987841 = 2990881) B2990881
theorem B3316211 : Blo 1309973 3316211 := bstep (se 1 (by rfl) ⟨2487158, by rfl⟩ : syracuseStep 3316211 = 4974317) B4974317
theorem B4422329 : Blo 1309973 4422329 := bstep (se 2 (by rfl) ⟨1658373, by rfl⟩ : syracuseStep 4422329 = 3316747) B3316747
theorem B3316423 : Blo 1309973 3316423 := bstep (se 1 (by rfl) ⟨2487317, by rfl⟩ : syracuseStep 3316423 = 4974635) B4974635
theorem B5315321 : Blo 1309973 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B2947913 : Blo 1309973 2947913 := bstep (se 2 (by rfl) ⟨1105467, by rfl⟩ : syracuseStep 2947913 = 2210935) B2210935
theorem B2210665 : Blo 1309973 2210665 := bstep (se 2 (by rfl) ⟨828999, by rfl⟩ : syracuseStep 2210665 = 1657999) B1657999
theorem B2489231 : Blo 1309973 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B1964975 : Blo 1309973 1964975 := bstep (se 1 (by rfl) ⟨1473731, by rfl⟩ : syracuseStep 1964975 = 2947463) B2947463
theorem B12598199 : Blo 1309973 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B1965065 : Blo 1309973 1965065 := bstep (se 2 (by rfl) ⟨736899, by rfl⟩ : syracuseStep 1965065 = 1473799) B1473799
theorem B1965095 : Blo 1309973 1965095 := bstep (se 1 (by rfl) ⟨1473821, by rfl⟩ : syracuseStep 1965095 = 2947643) B2947643
theorem B1399847 : Blo 1309973 1399847 := bstep (se 1 (by rfl) ⟨1049885, by rfl⟩ : syracuseStep 1399847 = 2099771) B2099771
theorem B2489383 : Blo 1309973 2489383 := bstep (se 1 (by rfl) ⟨1867037, by rfl⟩ : syracuseStep 2489383 = 3734075) B3734075
theorem B6634547 : Blo 1309973 6634547 := bstep (se 1 (by rfl) ⟨4975910, by rfl⟩ : syracuseStep 6634547 = 9951821) B9951821
theorem B9952307 : Blo 1309973 9952307 := bstep (se 1 (by rfl) ⟨7464230, by rfl⟩ : syracuseStep 9952307 = 14928461) B14928461
theorem B1965179 : Blo 1309973 1965179 := bstep (se 1 (by rfl) ⟨1473884, by rfl⟩ : syracuseStep 1965179 = 2947769) B2947769
theorem B2489467 : Blo 1309973 2489467 := bstep (se 1 (by rfl) ⟨1867100, by rfl⟩ : syracuseStep 2489467 = 3734201) B3734201
theorem B1965305 : Blo 1309973 1965305 := bstep (se 2 (by rfl) ⟨736989, by rfl⟩ : syracuseStep 1965305 = 1473979) B1473979
theorem B4422923 : Blo 1309973 4422923 := bstep (se 1 (by rfl) ⟨3317192, by rfl⟩ : syracuseStep 4422923 = 6634385) B6634385
theorem B1309991 : Blo 1309973 1309991 := bstep (se 1 (by rfl) ⟨982493, by rfl⟩ : syracuseStep 1309991 = 1964987) B1964987
theorem B1310031 : Blo 1309973 1310031 := bstep (se 1 (by rfl) ⟨982523, by rfl⟩ : syracuseStep 1310031 = 1965047) B1965047
theorem B1310047 : Blo 1309973 1310047 := bstep (se 1 (by rfl) ⟨982535, by rfl⟩ : syracuseStep 1310047 = 1965071) B1965071
theorem B1965407 : Blo 1309973 1965407 := bstep (se 1 (by rfl) ⟨1474055, by rfl⟩ : syracuseStep 1965407 = 2948111) B2948111
theorem B2129257 : Blo 1309973 2129257 := bstep (se 2 (by rfl) ⟨798471, by rfl⟩ : syracuseStep 2129257 = 1596943) B1596943
theorem B1965419 : Blo 1309973 1965419 := bstep (se 1 (by rfl) ⟨1474064, by rfl⟩ : syracuseStep 1965419 = 2948129) B2948129
theorem B1310075 : Blo 1309973 1310075 := bstep (se 1 (by rfl) ⟨982556, by rfl⟩ : syracuseStep 1310075 = 1965113) B1965113
theorem B6299005 : Blo 1309973 6299005 := bstep (se 3 (by rfl) ⟨1181063, by rfl⟩ : syracuseStep 6299005 = 2362127) B2362127
theorem B14941583 : Blo 1309973 14941583 := bstep (se 1 (by rfl) ⟨11206187, by rfl⟩ : syracuseStep 14941583 = 22412375) B22412375
theorem B1310127 : Blo 1309973 1310127 := bstep (se 1 (by rfl) ⟨982595, by rfl⟩ : syracuseStep 1310127 = 1965191) B1965191
theorem B2211259 : Blo 1309973 2211259 := bstep (se 1 (by rfl) ⟨1658444, by rfl⟩ : syracuseStep 2211259 = 3316889) B3316889
theorem B1310151 : Blo 1309973 1310151 := bstep (se 1 (by rfl) ⟨982613, by rfl⟩ : syracuseStep 1310151 = 1965227) B1965227
theorem B1310171 : Blo 1309973 1310171 := bstep (se 1 (by rfl) ⟨982628, by rfl⟩ : syracuseStep 1310171 = 1965257) B1965257
theorem B4423193 : Blo 1309973 4423193 := bstep (se 2 (by rfl) ⟨1658697, by rfl⟩ : syracuseStep 4423193 = 3317395) B3317395
theorem B1310247 : Blo 1309973 1310247 := bstep (se 1 (by rfl) ⟨982685, by rfl⟩ : syracuseStep 1310247 = 1965371) B1965371
theorem B1474087 : Blo 1309973 1474087 := bstep (se 1 (by rfl) ⟨1105565, by rfl⟩ : syracuseStep 1474087 = 2211131) B2211131
theorem B2211367 : Blo 1309973 2211367 := bstep (se 1 (by rfl) ⟨1658525, by rfl⟩ : syracuseStep 2211367 = 3317051) B3317051
theorem B1310287 : Blo 1309973 1310287 := bstep (se 1 (by rfl) ⟨982715, by rfl⟩ : syracuseStep 1310287 = 1965431) B1965431
theorem B1965647 : Blo 1309973 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B1310303 : Blo 1309973 1310303 := bstep (se 1 (by rfl) ⟨982727, by rfl⟩ : syracuseStep 1310303 = 1965455) B1965455
theorem B2948705 : Blo 1309973 2948705 := bstep (se 2 (by rfl) ⟨1105764, by rfl⟩ : syracuseStep 2948705 = 2211529) B2211529
theorem B3317345 : Blo 1309973 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B2489953 : Blo 1309973 2489953 := bstep (se 2 (by rfl) ⟨933732, by rfl⟩ : syracuseStep 2489953 = 1867465) B1867465
theorem B1310331 : Blo 1309973 1310331 := bstep (se 1 (by rfl) ⟨982748, by rfl⟩ : syracuseStep 1310331 = 1965497) B1965497
theorem B1310383 : Blo 1309973 1310383 := bstep (se 1 (by rfl) ⟨982787, by rfl⟩ : syracuseStep 1310383 = 1965575) B1965575
theorem B1310407 : Blo 1309973 1310407 := bstep (se 1 (by rfl) ⟨982805, by rfl⟩ : syracuseStep 1310407 = 1965611) B1965611
theorem B1965767 : Blo 1309973 1965767 := bstep (se 1 (by rfl) ⟨1474325, by rfl⟩ : syracuseStep 1965767 = 2948651) B2948651
theorem B1310427 : Blo 1309973 1310427 := bstep (se 1 (by rfl) ⟨982820, by rfl⟩ : syracuseStep 1310427 = 1965641) B1965641
theorem B1310503 : Blo 1309973 1310503 := bstep (se 1 (by rfl) ⟨982877, by rfl⟩ : syracuseStep 1310503 = 1965755) B1965755
theorem B1310543 : Blo 1309973 1310543 := bstep (se 1 (by rfl) ⟨982907, by rfl⟩ : syracuseStep 1310543 = 1965815) B1965815
theorem B1310559 : Blo 1309973 1310559 := bstep (se 1 (by rfl) ⟨982919, by rfl⟩ : syracuseStep 1310559 = 1965839) B1965839
theorem B1400671 : Blo 1309973 1400671 := bstep (se 1 (by rfl) ⟨1050503, by rfl⟩ : syracuseStep 1400671 = 2101007) B2101007
theorem B8519519 : Blo 1309973 8519519 := bstep (se 1 (by rfl) ⟨6389639, by rfl⟩ : syracuseStep 8519519 = 12779279) B12779279
theorem B1965929 : Blo 1309973 1965929 := bstep (se 2 (by rfl) ⟨737223, by rfl⟩ : syracuseStep 1965929 = 1474447) B1474447
theorem B2211691 : Blo 1309973 2211691 := bstep (se 1 (by rfl) ⟨1658768, by rfl⟩ : syracuseStep 2211691 = 3317537) B3317537
theorem B1310587 : Blo 1309973 1310587 := bstep (se 1 (by rfl) ⟨982940, by rfl⟩ : syracuseStep 1310587 = 1965881) B1965881
theorem B1310639 : Blo 1309973 1310639 := bstep (se 1 (by rfl) ⟨982979, by rfl⟩ : syracuseStep 1310639 = 1965959) B1965959
theorem B1966007 : Blo 1309973 1966007 := bstep (se 1 (by rfl) ⟨1474505, by rfl⟩ : syracuseStep 1966007 = 2949011) B2949011
theorem B2949047 : Blo 1309973 2949047 := bstep (se 1 (by rfl) ⟨2211785, by rfl⟩ : syracuseStep 2949047 = 4423571) B4423571
theorem B1310663 : Blo 1309973 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B1310683 : Blo 1309973 1310683 := bstep (se 1 (by rfl) ⟨983012, by rfl⟩ : syracuseStep 1310683 = 1966025) B1966025
theorem B1966043 : Blo 1309973 1966043 := bstep (se 1 (by rfl) ⟨1474532, by rfl⟩ : syracuseStep 1966043 = 2949065) B2949065
theorem B5603539 : Blo 1309973 5603539 := bstep (se 1 (by rfl) ⟨4202654, by rfl⟩ : syracuseStep 5603539 = 8405309) B8405309
theorem B1311007 : Blo 1309973 1311007 := bstep (se 1 (by rfl) ⟨983255, by rfl⟩ : syracuseStep 1311007 = 1966511) B1966511
theorem B11198807 : Blo 1309973 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B1966427 : Blo 1309973 1966427 := bstep (se 1 (by rfl) ⟨1474820, by rfl⟩ : syracuseStep 1966427 = 2949641) B2949641
theorem B1311067 : Blo 1309973 1311067 := bstep (se 1 (by rfl) ⟨983300, by rfl⟩ : syracuseStep 1311067 = 1966601) B1966601
theorem B1311087 : Blo 1309973 1311087 := bstep (se 1 (by rfl) ⟨983315, by rfl⟩ : syracuseStep 1311087 = 1966631) B1966631
theorem B1311143 : Blo 1309973 1311143 := bstep (se 1 (by rfl) ⟨983357, by rfl⟩ : syracuseStep 1311143 = 1966715) B1966715
theorem B4424111 : Blo 1309973 4424111 := bstep (se 1 (by rfl) ⟨3318083, by rfl⟩ : syracuseStep 4424111 = 6636167) B6636167
theorem B2949551 : Blo 1309973 2949551 := bstep (se 1 (by rfl) ⟨2212163, by rfl⟩ : syracuseStep 2949551 = 4424327) B4424327
theorem B2949587 : Blo 1309973 2949587 := bstep (se 1 (by rfl) ⟨2212190, by rfl⟩ : syracuseStep 2949587 = 4424381) B4424381
theorem B1311227 : Blo 1309973 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B5317121 : Blo 1309973 5317121 := bstep (se 2 (by rfl) ⟨1993920, by rfl⟩ : syracuseStep 5317121 = 3987841) B3987841
theorem B2949695 : Blo 1309973 2949695 := bstep (se 1 (by rfl) ⟨2212271, by rfl⟩ : syracuseStep 2949695 = 4424543) B4424543
theorem B1966655 : Blo 1309973 1966655 := bstep (se 1 (by rfl) ⟨1474991, by rfl⟩ : syracuseStep 1966655 = 2949983) B2949983
theorem B1311295 : Blo 1309973 1311295 := bstep (se 1 (by rfl) ⟨983471, by rfl⟩ : syracuseStep 1311295 = 1966943) B1966943
theorem B1311303 : Blo 1309973 1311303 := bstep (se 1 (by rfl) ⟨983477, by rfl⟩ : syracuseStep 1311303 = 1966955) B1966955
theorem B1475167 : Blo 1309973 1475167 := bstep (se 1 (by rfl) ⟨1106375, by rfl⟩ : syracuseStep 1475167 = 2212751) B2212751
theorem B2949803 : Blo 1309973 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B2212535 : Blo 1309973 2212535 := bstep (se 1 (by rfl) ⟨1659401, by rfl⟩ : syracuseStep 2212535 = 3318803) B3318803
theorem B1966775 : Blo 1309973 1966775 := bstep (se 1 (by rfl) ⟨1475081, by rfl⟩ : syracuseStep 1966775 = 2950163) B2950163
theorem B7086791 : Blo 1309973 7086791 := bstep (se 1 (by rfl) ⟨5315093, by rfl⟩ : syracuseStep 7086791 = 10630187) B10630187
theorem B1311455 : Blo 1309973 1311455 := bstep (se 1 (by rfl) ⟨983591, by rfl⟩ : syracuseStep 1311455 = 1967183) B1967183
theorem B1311535 : Blo 1309973 1311535 := bstep (se 1 (by rfl) ⟨983651, by rfl⟩ : syracuseStep 1311535 = 1967303) B1967303
theorem B3318671 : Blo 1309973 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B1967003 : Blo 1309973 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B1311643 : Blo 1309973 1311643 := bstep (se 1 (by rfl) ⟨983732, by rfl⟩ : syracuseStep 1311643 = 1967465) B1967465
theorem B25183169 : Blo 1309973 25183169 := bstep (se 2 (by rfl) ⟨9443688, by rfl⟩ : syracuseStep 25183169 = 18887377) B18887377
theorem B1311695 : Blo 1309973 1311695 := bstep (se 1 (by rfl) ⟨983771, by rfl⟩ : syracuseStep 1311695 = 1967543) B1967543
theorem B5596123 : Blo 1309973 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B1311719 : Blo 1309973 1311719 := bstep (se 1 (by rfl) ⟨983789, by rfl⟩ : syracuseStep 1311719 = 1967579) B1967579
theorem B11199491 : Blo 1309973 11199491 := bstep (se 1 (by rfl) ⟨8399618, by rfl⟩ : syracuseStep 11199491 = 16799237) B16799237
theorem B27272285 : Blo 1309973 27272285 := bstep (se 3 (by rfl) ⟨5113553, by rfl⟩ : syracuseStep 27272285 = 10227107) B10227107
theorem B7087247 : Blo 1309973 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B2950343 : Blo 1309973 2950343 := bstep (se 1 (by rfl) ⟨2212757, by rfl⟩ : syracuseStep 2950343 = 4425515) B4425515
theorem B3409183 : Blo 1309973 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B1967399 : Blo 1309973 1967399 := bstep (se 1 (by rfl) ⟨1475549, by rfl⟩ : syracuseStep 1967399 = 2951099) B2951099
theorem B4425083 : Blo 1309973 4425083 := bstep (se 1 (by rfl) ⟨3318812, by rfl⟩ : syracuseStep 4425083 = 6637625) B6637625
theorem B2950523 : Blo 1309973 2950523 := bstep (se 1 (by rfl) ⟨2212892, by rfl⟩ : syracuseStep 2950523 = 4425785) B4425785
theorem B1967483 : Blo 1309973 1967483 := bstep (se 1 (by rfl) ⟨1475612, by rfl⟩ : syracuseStep 1967483 = 2951225) B2951225
theorem B3319177 : Blo 1309973 3319177 := bstep (se 2 (by rfl) ⟨1244691, by rfl⟩ : syracuseStep 3319177 = 2489383) B2489383
theorem B2213257 : Blo 1309973 2213257 := bstep (se 2 (by rfl) ⟨829971, by rfl⟩ : syracuseStep 2213257 = 1659943) B1659943
theorem B3319289 : Blo 1309973 3319289 := bstep (se 2 (by rfl) ⟨1244733, by rfl⟩ : syracuseStep 3319289 = 2489467) B2489467
theorem B2950649 : Blo 1309973 2950649 := bstep (se 2 (by rfl) ⟨1106493, by rfl⟩ : syracuseStep 2950649 = 2212987) B2212987
theorem B1967609 : Blo 1309973 1967609 := bstep (se 2 (by rfl) ⟨737853, by rfl⟩ : syracuseStep 1967609 = 1475707) B1475707
theorem B10774073 : Blo 1309973 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B2950739 : Blo 1309973 2950739 := bstep (se 1 (by rfl) ⟨2213054, by rfl⟩ : syracuseStep 2950739 = 4426109) B4426109
theorem B1771103 : Blo 1309973 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B1967711 : Blo 1309973 1967711 := bstep (se 1 (by rfl) ⟨1475783, by rfl⟩ : syracuseStep 1967711 = 2951567) B2951567
theorem B2950919 : Blo 1309973 2950919 := bstep (se 1 (by rfl) ⟨2213189, by rfl⟩ : syracuseStep 2950919 = 4426379) B4426379
theorem B1967927 : Blo 1309973 1967927 := bstep (se 1 (by rfl) ⟨1475945, by rfl⟩ : syracuseStep 1967927 = 2951891) B2951891
theorem B2213689 : Blo 1309973 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B8398673 : Blo 1309973 8398673 := bstep (se 2 (by rfl) ⟨3149502, by rfl⟩ : syracuseStep 8398673 = 6299005) B6299005
theorem B17926019 : Blo 1309973 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B11356037 : Blo 1309973 11356037 := bstep (se 4 (by rfl) ⟨1064628, by rfl⟩ : syracuseStep 11356037 = 2129257) B2129257
theorem B8398799 : Blo 1309973 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B14174189 : Blo 1309973 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B3319937 : Blo 1309973 3319937 := bstep (se 2 (by rfl) ⟨1244976, by rfl⟩ : syracuseStep 3319937 = 2489953) B2489953
theorem B7186679 : Blo 1309973 7186679 := bstep (se 1 (by rfl) ⟨5390009, by rfl⟩ : syracuseStep 7186679 = 10780019) B10780019
theorem B22718717 : Blo 1309973 22718717 := bstep (se 3 (by rfl) ⟨4259759, by rfl⟩ : syracuseStep 22718717 = 8519519) B8519519
theorem B4098313 : Blo 1309973 4098313 := bstep (se 2 (by rfl) ⟨1536867, by rfl⟩ : syracuseStep 4098313 = 3073735) B3073735
theorem B2951531 : Blo 1309973 2951531 := bstep (se 1 (by rfl) ⟨2213648, by rfl⟩ : syracuseStep 2951531 = 4427297) B4427297
theorem B6637949 : Blo 1309973 6637949 := bstep (se 3 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 6637949 = 2489231) B2489231
theorem B2099623 : Blo 1309973 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B2951675 : Blo 1309973 2951675 := bstep (se 1 (by rfl) ⟨2213756, by rfl⟩ : syracuseStep 2951675 = 4427513) B4427513
theorem B16804361 : Blo 1309973 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B1993337 : Blo 1309973 1993337 := bstep (se 2 (by rfl) ⟨747501, by rfl⟩ : syracuseStep 1993337 = 1495003) B1495003
theorem B2951801 : Blo 1309973 2951801 := bstep (se 2 (by rfl) ⟨1106925, by rfl⟩ : syracuseStep 2951801 = 2213851) B2213851
theorem B2951855 : Blo 1309973 2951855 := bstep (se 1 (by rfl) ⟨2213891, by rfl⟩ : syracuseStep 2951855 = 4427783) B4427783
theorem B4426487 : Blo 1309973 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B2951927 : Blo 1309973 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B3320747 : Blo 1309973 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B4484285 : Blo 1309973 4484285 := bstep (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) B1681607
theorem B24235211 : Blo 1309973 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B51088765 : Blo 1309973 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B3149243 : Blo 1309973 3149243 := bstep (se 1 (by rfl) ⟨2361932, by rfl⟩ : syracuseStep 3149243 = 4723865) B4723865
theorem B47812193 : Blo 1309973 47812193 := bstep (se 2 (by rfl) ⟨17929572, by rfl⟩ : syracuseStep 47812193 = 35859145) B35859145
theorem B1658551 : Blo 1309973 1658551 := bstep (se 1 (by rfl) ⟨1243913, by rfl⟩ : syracuseStep 1658551 = 2487827) B2487827
theorem B11194159 : Blo 1309973 11194159 := bstep (se 1 (by rfl) ⟨8395619, by rfl⟩ : syracuseStep 11194159 = 16791239) B16791239
theorem B9957167 : Blo 1309973 9957167 := bstep (se 1 (by rfl) ⟨7467875, by rfl⟩ : syracuseStep 9957167 = 14935751) B14935751
theorem B6639407 : Blo 1309973 6639407 := bstep (se 1 (by rfl) ⟨4979555, by rfl⟩ : syracuseStep 6639407 = 9959111) B9959111
theorem B4427567 : Blo 1309973 4427567 := bstep (se 1 (by rfl) ⟨3320675, by rfl⟩ : syracuseStep 4427567 = 6641351) B6641351
theorem B96964487 : Blo 1309973 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B8401259 : Blo 1309973 8401259 := bstep (se 1 (by rfl) ⟨6300944, by rfl⟩ : syracuseStep 8401259 = 12601889) B12601889
theorem B6631955 : Blo 1309973 6631955 := bstep (se 1 (by rfl) ⟨4973966, by rfl⟩ : syracuseStep 6631955 = 9947933) B9947933
theorem B40383161 : Blo 1309973 40383161 := bstep (se 2 (by rfl) ⟨15143685, by rfl⟩ : syracuseStep 40383161 = 30287371) B30287371
theorem B2798327 : Blo 1309973 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B57480101 : Blo 1309973 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B2487287 : Blo 1309973 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B2487439 : Blo 1309973 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B9442655 : Blo 1309973 9442655 := bstep (se 1 (by rfl) ⟨7081991, by rfl⟩ : syracuseStep 9442655 = 14163983) B14163983
theorem B3986783 : Blo 1309973 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B8975711 : Blo 1309973 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B37786985 : Blo 1309973 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B3732925 : Blo 1309973 3732925 := bstep (se 3 (by rfl) ⟨699923, by rfl⟩ : syracuseStep 3732925 = 1399847) B1399847
theorem B6641513 : Blo 1309973 6641513 := bstep (se 2 (by rfl) ⟨2490567, by rfl⟩ : syracuseStep 6641513 = 4981135) B4981135
theorem B2521039 : Blo 1309973 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B5609453 : Blo 1309973 5609453 := bstep (se 3 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 5609453 = 2103545) B2103545
theorem B4421897 : Blo 1309973 4421897 := bstep (se 2 (by rfl) ⟨1658211, by rfl⟩ : syracuseStep 4421897 = 3316423) B3316423
theorem B6633737 : Blo 1309973 6633737 := bstep (se 2 (by rfl) ⟨2487651, by rfl⟩ : syracuseStep 6633737 = 4975303) B4975303
theorem B3889433 : Blo 1309973 3889433 := bstep (se 2 (by rfl) ⟨1458537, by rfl⟩ : syracuseStep 3889433 = 2917075) B2917075
theorem B3316079 : Blo 1309973 3316079 := bstep (se 1 (by rfl) ⟨2487059, by rfl⟩ : syracuseStep 3316079 = 4974119) B4974119
theorem B5044663 : Blo 1309973 5044663 := bstep (se 1 (by rfl) ⟨3783497, by rfl⟩ : syracuseStep 5044663 = 7566995) B7566995
theorem B7469495 : Blo 1309973 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B2947553 : Blo 1309973 2947553 := bstep (se 2 (by rfl) ⟨1105332, by rfl⟩ : syracuseStep 2947553 = 2210665) B2210665
theorem B45390331 : Blo 1309973 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B1866235 : Blo 1309973 1866235 := bstep (se 1 (by rfl) ⟨1399676, by rfl⟩ : syracuseStep 1866235 = 2799353) B2799353
theorem B5601899 : Blo 1309973 5601899 := bstep (se 1 (by rfl) ⟨4201424, by rfl⟩ : syracuseStep 5601899 = 8402849) B8402849
theorem B102112001 : Blo 1309973 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B2947859 : Blo 1309973 2947859 := bstep (se 1 (by rfl) ⟨2210894, by rfl⟩ : syracuseStep 2947859 = 4421789) B4421789
theorem B2800403 : Blo 1309973 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B4202219 : Blo 1309973 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B2210807 : Blo 1309973 2210807 := bstep (se 1 (by rfl) ⟨1658105, by rfl⟩ : syracuseStep 2210807 = 3316211) B3316211
theorem B3316727 : Blo 1309973 3316727 := bstep (se 1 (by rfl) ⟨2487545, by rfl⟩ : syracuseStep 3316727 = 4975091) B4975091
theorem B2948219 : Blo 1309973 2948219 := bstep (se 1 (by rfl) ⟨2211164, by rfl⟩ : syracuseStep 2948219 = 4422329) B4422329
theorem B3316859 : Blo 1309973 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B7470245 : Blo 1309973 7470245 := bstep (se 4 (by rfl) ⟨700335, by rfl⟩ : syracuseStep 7470245 = 1400671) B1400671
theorem B1965275 : Blo 1309973 1965275 := bstep (se 1 (by rfl) ⟨1473956, by rfl⟩ : syracuseStep 1965275 = 2947913) B2947913
theorem B2948345 : Blo 1309973 2948345 := bstep (se 2 (by rfl) ⟨1105629, by rfl⟩ : syracuseStep 2948345 = 2211259) B2211259
theorem B1309983 : Blo 1309973 1309983 := bstep (se 1 (by rfl) ⟨982487, by rfl⟩ : syracuseStep 1309983 = 1964975) B1964975
theorem B1310043 : Blo 1309973 1310043 := bstep (se 1 (by rfl) ⟨982532, by rfl⟩ : syracuseStep 1310043 = 1965065) B1965065
theorem B2800993 : Blo 1309973 2800993 := bstep (se 2 (by rfl) ⟨1050372, by rfl⟩ : syracuseStep 2800993 = 2100745) B2100745
theorem B4791649 : Blo 1309973 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B1310063 : Blo 1309973 1310063 := bstep (se 1 (by rfl) ⟨982547, by rfl⟩ : syracuseStep 1310063 = 1965095) B1965095
theorem B4423031 : Blo 1309973 4423031 := bstep (se 1 (by rfl) ⟨3317273, by rfl⟩ : syracuseStep 4423031 = 6634547) B6634547
theorem B6634871 : Blo 1309973 6634871 := bstep (se 1 (by rfl) ⟨4976153, by rfl⟩ : syracuseStep 6634871 = 9952307) B9952307
theorem B1965449 : Blo 1309973 1965449 := bstep (se 2 (by rfl) ⟨737043, by rfl⟩ : syracuseStep 1965449 = 1474087) B1474087
theorem B2948489 : Blo 1309973 2948489 := bstep (se 2 (by rfl) ⟨1105683, by rfl⟩ : syracuseStep 2948489 = 2211367) B2211367
theorem B1310119 : Blo 1309973 1310119 := bstep (se 1 (by rfl) ⟨982589, by rfl⟩ : syracuseStep 1310119 = 1965179) B1965179
theorem B1310203 : Blo 1309973 1310203 := bstep (se 1 (by rfl) ⟨982652, by rfl⟩ : syracuseStep 1310203 = 1965305) B1965305
theorem B2948615 : Blo 1309973 2948615 := bstep (se 1 (by rfl) ⟨2211461, by rfl⟩ : syracuseStep 2948615 = 4422923) B4422923
theorem B6635033 : Blo 1309973 6635033 := bstep (se 2 (by rfl) ⟨2488137, by rfl⟩ : syracuseStep 6635033 = 4976275) B4976275
theorem B9952793 : Blo 1309973 9952793 := bstep (se 2 (by rfl) ⟨3732297, by rfl⟩ : syracuseStep 9952793 = 7464595) B7464595
theorem B1310271 : Blo 1309973 1310271 := bstep (se 1 (by rfl) ⟨982703, by rfl⟩ : syracuseStep 1310271 = 1965407) B1965407
theorem B1310279 : Blo 1309973 1310279 := bstep (se 1 (by rfl) ⟨982709, by rfl⟩ : syracuseStep 1310279 = 1965419) B1965419
theorem B9961055 : Blo 1309973 9961055 := bstep (se 1 (by rfl) ⟨7470791, by rfl⟩ : syracuseStep 9961055 = 14941583) B14941583
theorem B2948795 : Blo 1309973 2948795 := bstep (se 1 (by rfl) ⟨2211596, by rfl⟩ : syracuseStep 2948795 = 4423193) B4423193
theorem B1310431 : Blo 1309973 1310431 := bstep (se 1 (by rfl) ⟨982823, by rfl⟩ : syracuseStep 1310431 = 1965647) B1965647
theorem B2211563 : Blo 1309973 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B1965803 : Blo 1309973 1965803 := bstep (se 1 (by rfl) ⟨1474352, by rfl⟩ : syracuseStep 1965803 = 2948705) B2948705
theorem B12607235 : Blo 1309973 12607235 := bstep (se 1 (by rfl) ⟨9455426, by rfl⟩ : syracuseStep 12607235 = 18910853) B18910853
theorem B1310511 : Blo 1309973 1310511 := bstep (se 1 (by rfl) ⟨982883, by rfl⟩ : syracuseStep 1310511 = 1965767) B1965767
theorem B2948921 : Blo 1309973 2948921 := bstep (se 2 (by rfl) ⟨1105845, by rfl⟩ : syracuseStep 2948921 = 2211691) B2211691
theorem B2801513 : Blo 1309973 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B1310619 : Blo 1309973 1310619 := bstep (se 1 (by rfl) ⟨982964, by rfl⟩ : syracuseStep 1310619 = 1965929) B1965929
theorem B62185391 : Blo 1309973 62185391 := bstep (se 1 (by rfl) ⟨46639043, by rfl⟩ : syracuseStep 62185391 = 93278087) B93278087
theorem B1310671 : Blo 1309973 1310671 := bstep (se 1 (by rfl) ⟨983003, by rfl⟩ : syracuseStep 1310671 = 1966007) B1966007
theorem B1966031 : Blo 1309973 1966031 := bstep (se 1 (by rfl) ⟨1474523, by rfl⟩ : syracuseStep 1966031 = 2949047) B2949047
theorem B1310695 : Blo 1309973 1310695 := bstep (se 1 (by rfl) ⟨983021, by rfl⟩ : syracuseStep 1310695 = 1966043) B1966043
theorem B1310951 : Blo 1309973 1310951 := bstep (se 1 (by rfl) ⟨983213, by rfl⟩ : syracuseStep 1310951 = 1966427) B1966427
theorem B7471385 : Blo 1309973 7471385 := bstep (se 2 (by rfl) ⟨2801769, by rfl⟩ : syracuseStep 7471385 = 5603539) B5603539
theorem B2949407 : Blo 1309973 2949407 := bstep (se 1 (by rfl) ⟨2212055, by rfl⟩ : syracuseStep 2949407 = 4424111) B4424111
theorem B1966367 : Blo 1309973 1966367 := bstep (se 1 (by rfl) ⟨1474775, by rfl⟩ : syracuseStep 1966367 = 2949551) B2949551
theorem B1966391 : Blo 1309973 1966391 := bstep (se 1 (by rfl) ⟨1474793, by rfl⟩ : syracuseStep 1966391 = 2949587) B2949587
theorem B5464417 : Blo 1309973 5464417 := bstep (se 2 (by rfl) ⟨2049156, by rfl⟩ : syracuseStep 5464417 = 4098313) B4098313
theorem B1966463 : Blo 1309973 1966463 := bstep (se 1 (by rfl) ⟨1474847, by rfl⟩ : syracuseStep 1966463 = 2949695) B2949695
theorem B1311103 : Blo 1309973 1311103 := bstep (se 1 (by rfl) ⟨983327, by rfl⟩ : syracuseStep 1311103 = 1966655) B1966655
theorem B1966535 : Blo 1309973 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B1475023 : Blo 1309973 1475023 := bstep (se 1 (by rfl) ⟨1106267, by rfl⟩ : syracuseStep 1475023 = 2212535) B2212535
theorem B1311183 : Blo 1309973 1311183 := bstep (se 1 (by rfl) ⟨983387, by rfl⟩ : syracuseStep 1311183 = 1966775) B1966775
theorem B64627229 : Blo 1309973 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B2212447 : Blo 1309973 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B1311335 : Blo 1309973 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B1966889 : Blo 1309973 1966889 := bstep (se 2 (by rfl) ⟨737583, by rfl⟩ : syracuseStep 1966889 = 1475167) B1475167
theorem B1966895 : Blo 1309973 1966895 := bstep (se 1 (by rfl) ⟨1475171, by rfl⟩ : syracuseStep 1966895 = 2950343) B2950343
theorem B1311599 : Blo 1309973 1311599 := bstep (se 1 (by rfl) ⟨983699, by rfl⟩ : syracuseStep 1311599 = 1967399) B1967399
theorem B25191323 : Blo 1309973 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B2950055 : Blo 1309973 2950055 := bstep (se 1 (by rfl) ⟨2212541, by rfl⟩ : syracuseStep 2950055 = 4425083) B4425083
theorem B1967015 : Blo 1309973 1967015 := bstep (se 1 (by rfl) ⟨1475261, by rfl⟩ : syracuseStep 1967015 = 2950523) B2950523
theorem B1311655 : Blo 1309973 1311655 := bstep (se 1 (by rfl) ⟨983741, by rfl⟩ : syracuseStep 1311655 = 1967483) B1967483
theorem B2212859 : Blo 1309973 2212859 := bstep (se 1 (by rfl) ⟨1659644, by rfl⟩ : syracuseStep 2212859 = 3319289) B3319289
theorem B1967099 : Blo 1309973 1967099 := bstep (se 1 (by rfl) ⟨1475324, by rfl⟩ : syracuseStep 1967099 = 2950649) B2950649
theorem B1311739 : Blo 1309973 1311739 := bstep (se 1 (by rfl) ⟨983804, by rfl⟩ : syracuseStep 1311739 = 1967609) B1967609
theorem B1967159 : Blo 1309973 1967159 := bstep (se 1 (by rfl) ⟨1475369, by rfl⟩ : syracuseStep 1967159 = 2950739) B2950739
theorem B1311807 : Blo 1309973 1311807 := bstep (se 1 (by rfl) ⟨983855, by rfl⟩ : syracuseStep 1311807 = 1967711) B1967711
theorem B1967279 : Blo 1309973 1967279 := bstep (se 1 (by rfl) ⟨1475459, by rfl⟩ : syracuseStep 1967279 = 2950919) B2950919
theorem B1311951 : Blo 1309973 1311951 := bstep (se 1 (by rfl) ⟨983963, by rfl⟩ : syracuseStep 1311951 = 1967927) B1967927
theorem B7570691 : Blo 1309973 7570691 := bstep (se 1 (by rfl) ⟨5678018, by rfl⟩ : syracuseStep 7570691 = 11356037) B11356037
theorem B2213291 : Blo 1309973 2213291 := bstep (se 1 (by rfl) ⟨1659968, by rfl⟩ : syracuseStep 2213291 = 3319937) B3319937
theorem B28730861 : Blo 1309973 28730861 := bstep (se 3 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 28730861 = 10774073) B10774073
theorem B1967687 : Blo 1309973 1967687 := bstep (se 1 (by rfl) ⟨1475765, by rfl⟩ : syracuseStep 1967687 = 2951531) B2951531
theorem B4425299 : Blo 1309973 4425299 := bstep (se 1 (by rfl) ⟨3318974, by rfl⟩ : syracuseStep 4425299 = 6637949) B6637949
theorem B1967783 : Blo 1309973 1967783 := bstep (se 1 (by rfl) ⟨1475837, by rfl⟩ : syracuseStep 1967783 = 2951675) B2951675
theorem B1328891 : Blo 1309973 1328891 := bstep (se 1 (by rfl) ⟨996668, by rfl⟩ : syracuseStep 1328891 = 1993337) B1993337
theorem B1967867 : Blo 1309973 1967867 := bstep (se 1 (by rfl) ⟨1475900, by rfl⟩ : syracuseStep 1967867 = 2951801) B2951801
theorem B1967903 : Blo 1309973 1967903 := bstep (se 1 (by rfl) ⟨1475927, by rfl⟩ : syracuseStep 1967903 = 2951855) B2951855
theorem B2950991 : Blo 1309973 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B1967951 : Blo 1309973 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B68118353 : Blo 1309973 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B4425569 : Blo 1309973 4425569 := bstep (se 2 (by rfl) ⟨1659588, by rfl⟩ : syracuseStep 4425569 = 3319177) B3319177
theorem B2951009 : Blo 1309973 2951009 := bstep (se 2 (by rfl) ⟨1106628, by rfl⟩ : syracuseStep 2951009 = 2213257) B2213257
theorem B2213831 : Blo 1309973 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B26904869 : Blo 1309973 26904869 := bstep (se 4 (by rfl) ⟨2522331, by rfl⟩ : syracuseStep 26904869 = 5044663) B5044663
theorem B2099495 : Blo 1309973 2099495 := bstep (se 1 (by rfl) ⟨1574621, by rfl⟩ : syracuseStep 2099495 = 3149243) B3149243
theorem B2951585 : Blo 1309973 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B6638111 : Blo 1309973 6638111 := bstep (se 1 (by rfl) ⟨4978583, by rfl⟩ : syracuseStep 6638111 = 9957167) B9957167
theorem B4426271 : Blo 1309973 4426271 := bstep (se 1 (by rfl) ⟨3319703, by rfl⟩ : syracuseStep 4426271 = 6639407) B6639407
theorem B2951711 : Blo 1309973 2951711 := bstep (se 1 (by rfl) ⟨2213783, by rfl⟩ : syracuseStep 2951711 = 4427567) B4427567
theorem B3361385 : Blo 1309973 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B7465871 : Blo 1309973 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B26922107 : Blo 1309973 26922107 := bstep (se 1 (by rfl) ⟨20191580, by rfl⟩ : syracuseStep 26922107 = 40383161) B40383161
theorem B16788779 : Blo 1309973 16788779 := bstep (se 1 (by rfl) ⟨12591584, by rfl⟩ : syracuseStep 16788779 = 25183169) B25183169
theorem B7466327 : Blo 1309973 7466327 := bstep (se 1 (by rfl) ⟨5599745, by rfl⟩ : syracuseStep 7466327 = 11199491) B11199491
theorem B18181523 : Blo 1309973 18181523 := bstep (se 1 (by rfl) ⟨13636142, by rfl⟩ : syracuseStep 18181523 = 27272285) B27272285
theorem B6295103 : Blo 1309973 6295103 := bstep (se 1 (by rfl) ⟨4721327, by rfl⟩ : syracuseStep 6295103 = 9442655) B9442655
theorem B2657855 : Blo 1309973 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B5983807 : Blo 1309973 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B5599115 : Blo 1309973 5599115 := bstep (se 1 (by rfl) ⟨4199336, by rfl⟩ : syracuseStep 5599115 = 8398673) B8398673
theorem B4427675 : Blo 1309973 4427675 := bstep (se 1 (by rfl) ⟨3320756, by rfl⟩ : syracuseStep 4427675 = 6641513) B6641513
theorem B5599199 : Blo 1309973 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B9449459 : Blo 1309973 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B2592955 : Blo 1309973 2592955 := bstep (se 1 (by rfl) ⟨1944716, by rfl⟩ : syracuseStep 2592955 = 3889433) B3889433
theorem B4722941 : Blo 1309973 4722941 := bstep (se 3 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 4722941 = 1771103) B1771103
theorem B11202907 : Blo 1309973 11202907 := bstep (se 1 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 11202907 = 16804361) B16804361
theorem B4977233 : Blo 1309973 4977233 := bstep (se 2 (by rfl) ⟨1866462, by rfl⟩ : syracuseStep 4977233 = 3732925) B3732925
theorem B6640703 : Blo 1309973 6640703 := bstep (se 1 (by rfl) ⟨4980527, by rfl⟩ : syracuseStep 6640703 = 9961055) B9961055
theorem B41456927 : Blo 1309973 41456927 := bstep (se 1 (by rfl) ⟨31092695, by rfl⟩ : syracuseStep 41456927 = 62185391) B62185391
theorem B6632765 : Blo 1309973 6632765 := bstep (se 3 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 6632765 = 2487287) B2487287
theorem B5600839 : Blo 1309973 5600839 := bstep (se 1 (by rfl) ⟨4200629, by rfl⟩ : syracuseStep 5600839 = 8401259) B8401259
theorem B4421303 : Blo 1309973 4421303 := bstep (se 1 (by rfl) ⟨3315977, by rfl⟩ : syracuseStep 4421303 = 6631955) B6631955
theorem B2799497 : Blo 1309973 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B38320067 : Blo 1309973 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B2488313 : Blo 1309973 2488313 := bstep (se 2 (by rfl) ⟨933117, by rfl⟩ : syracuseStep 2488313 = 1866235) B1866235
theorem B60520441 : Blo 1309973 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B4724831 : Blo 1309973 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B11950679 : Blo 1309973 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B7461497 : Blo 1309973 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B14178989 : Blo 1309973 14178989 := bstep (se 3 (by rfl) ⟨2658560, by rfl⟩ : syracuseStep 14178989 = 5317121) B5317121
theorem B4791119 : Blo 1309973 4791119 := bstep (se 1 (by rfl) ⟨3593339, by rfl⟩ : syracuseStep 4791119 = 7186679) B7186679
theorem B15145811 : Blo 1309973 15145811 := bstep (se 1 (by rfl) ⟨11359358, by rfl⟩ : syracuseStep 15145811 = 22718717) B22718717
theorem B2947931 : Blo 1309973 2947931 := bstep (se 1 (by rfl) ⟨2210948, by rfl⟩ : syracuseStep 2947931 = 4421897) B4421897
theorem B4422491 : Blo 1309973 4422491 := bstep (se 1 (by rfl) ⟨3316868, by rfl⟩ : syracuseStep 4422491 = 6633737) B6633737
theorem B3316585 : Blo 1309973 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B2210719 : Blo 1309973 2210719 := bstep (se 1 (by rfl) ⟨1658039, by rfl⟩ : syracuseStep 2210719 = 3316079) B3316079
theorem B4979663 : Blo 1309973 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B1965035 : Blo 1309973 1965035 := bstep (se 1 (by rfl) ⟨1473776, by rfl⟩ : syracuseStep 1965035 = 2947553) B2947553
theorem B4545577 : Blo 1309973 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B3734599 : Blo 1309973 3734599 := bstep (se 1 (by rfl) ⟨2800949, by rfl⟩ : syracuseStep 3734599 = 5601899) B5601899
theorem B3734657 : Blo 1309973 3734657 := bstep (se 2 (by rfl) ⟨1400496, by rfl⟩ : syracuseStep 3734657 = 2800993) B2800993
theorem B6388865 : Blo 1309973 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B68074667 : Blo 1309973 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B1965239 : Blo 1309973 1965239 := bstep (se 1 (by rfl) ⟨1473929, by rfl⟩ : syracuseStep 1965239 = 2947859) B2947859
theorem B1866935 : Blo 1309973 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B18898109 : Blo 1309973 18898109 := bstep (se 3 (by rfl) ⟨3543395, by rfl⟩ : syracuseStep 18898109 = 7086791) B7086791
theorem B7462205 : Blo 1309973 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B1473871 : Blo 1309973 1473871 := bstep (se 1 (by rfl) ⟨1105403, by rfl⟩ : syracuseStep 1473871 = 2210807) B2210807
theorem B2211151 : Blo 1309973 2211151 := bstep (se 1 (by rfl) ⟨1658363, by rfl⟩ : syracuseStep 2211151 = 3316727) B3316727
theorem B1965479 : Blo 1309973 1965479 := bstep (se 1 (by rfl) ⟨1474109, by rfl⟩ : syracuseStep 1965479 = 2948219) B2948219
theorem B2211239 : Blo 1309973 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B4980163 : Blo 1309973 4980163 := bstep (se 1 (by rfl) ⟨3735122, by rfl⟩ : syracuseStep 4980163 = 7470245) B7470245
theorem B2989523 : Blo 1309973 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B1310183 : Blo 1309973 1310183 := bstep (se 1 (by rfl) ⟨982637, by rfl⟩ : syracuseStep 1310183 = 1965275) B1965275
theorem B1965563 : Blo 1309973 1965563 := bstep (se 1 (by rfl) ⟨1474172, by rfl⟩ : syracuseStep 1965563 = 2948345) B2948345
theorem B2211401 : Blo 1309973 2211401 := bstep (se 2 (by rfl) ⟨829275, by rfl⟩ : syracuseStep 2211401 = 1658551) B1658551
theorem B2948687 : Blo 1309973 2948687 := bstep (se 1 (by rfl) ⟨2211515, by rfl⟩ : syracuseStep 2948687 = 4423031) B4423031
theorem B4423247 : Blo 1309973 4423247 := bstep (se 1 (by rfl) ⟨3317435, by rfl⟩ : syracuseStep 4423247 = 6634871) B6634871
theorem B1310299 : Blo 1309973 1310299 := bstep (se 1 (by rfl) ⟨982724, by rfl⟩ : syracuseStep 1310299 = 1965449) B1965449
theorem B1965659 : Blo 1309973 1965659 := bstep (se 1 (by rfl) ⟨1474244, by rfl⟩ : syracuseStep 1965659 = 2948489) B2948489
theorem B7470701 : Blo 1309973 7470701 := bstep (se 3 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 7470701 = 2801513) B2801513
theorem B8404823 : Blo 1309973 8404823 := bstep (se 1 (by rfl) ⟨6303617, by rfl⟩ : syracuseStep 8404823 = 12607235) B12607235
theorem B1965743 : Blo 1309973 1965743 := bstep (se 1 (by rfl) ⟨1474307, by rfl⟩ : syracuseStep 1965743 = 2948615) B2948615
theorem B6635195 : Blo 1309973 6635195 := bstep (se 1 (by rfl) ⟨4976396, by rfl⟩ : syracuseStep 6635195 = 9952793) B9952793
theorem B4423355 : Blo 1309973 4423355 := bstep (se 1 (by rfl) ⟨3317516, by rfl⟩ : syracuseStep 4423355 = 6635033) B6635033
theorem B14925545 : Blo 1309973 14925545 := bstep (se 2 (by rfl) ⟨5597079, by rfl⟩ : syracuseStep 14925545 = 11194159) B11194159
theorem B31874795 : Blo 1309973 31874795 := bstep (se 1 (by rfl) ⟨23906096, by rfl⟩ : syracuseStep 31874795 = 47812193) B47812193
theorem B1965863 : Blo 1309973 1965863 := bstep (se 1 (by rfl) ⟨1474397, by rfl⟩ : syracuseStep 1965863 = 2948795) B2948795
theorem B1310535 : Blo 1309973 1310535 := bstep (se 1 (by rfl) ⟨982901, by rfl⟩ : syracuseStep 1310535 = 1965803) B1965803
theorem B1474375 : Blo 1309973 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B2801479 : Blo 1309973 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B1965947 : Blo 1309973 1965947 := bstep (se 1 (by rfl) ⟨1474460, by rfl⟩ : syracuseStep 1965947 = 2948921) B2948921
theorem B64642991 : Blo 1309973 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B14958541 : Blo 1309973 14958541 := bstep (se 3 (by rfl) ⟨2804726, by rfl⟩ : syracuseStep 14958541 = 5609453) B5609453
theorem B1310687 : Blo 1309973 1310687 := bstep (se 1 (by rfl) ⟨983015, by rfl⟩ : syracuseStep 1310687 = 1966031) B1966031
theorem B4980923 : Blo 1309973 4980923 := bstep (se 1 (by rfl) ⟨3735692, by rfl⟩ : syracuseStep 4980923 = 7471385) B7471385
theorem B1966271 : Blo 1309973 1966271 := bstep (se 1 (by rfl) ⟨1474703, by rfl⟩ : syracuseStep 1966271 = 2949407) B2949407
theorem B1310911 : Blo 1309973 1310911 := bstep (se 1 (by rfl) ⟨983183, by rfl⟩ : syracuseStep 1310911 = 1966367) B1966367
theorem B1310927 : Blo 1309973 1310927 := bstep (se 1 (by rfl) ⟨983195, by rfl⟩ : syracuseStep 1310927 = 1966391) B1966391
theorem B6299639 : Blo 1309973 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B3457273 : Blo 1309973 3457273 := bstep (se 2 (by rfl) ⟨1296477, by rfl⟩ : syracuseStep 3457273 = 2592955) B2592955
theorem B12599549 : Blo 1309973 12599549 := bstep (se 3 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 12599549 = 4724831) B4724831
theorem B1310975 : Blo 1309973 1310975 := bstep (se 1 (by rfl) ⟨983231, by rfl⟩ : syracuseStep 1310975 = 1966463) B1966463
theorem B1311023 : Blo 1309973 1311023 := bstep (se 1 (by rfl) ⟨983267, by rfl⟩ : syracuseStep 1311023 = 1966535) B1966535
theorem B3318155 : Blo 1309973 3318155 := bstep (se 1 (by rfl) ⟨2488616, by rfl⟩ : syracuseStep 3318155 = 4977233) B4977233
theorem B1311259 : Blo 1309973 1311259 := bstep (se 1 (by rfl) ⟨983444, by rfl⟩ : syracuseStep 1311259 = 1966889) B1966889
theorem B1311263 : Blo 1309973 1311263 := bstep (se 1 (by rfl) ⟨983447, by rfl⟩ : syracuseStep 1311263 = 1966895) B1966895
theorem B7978409 : Blo 1309973 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B16794215 : Blo 1309973 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B1966697 : Blo 1309973 1966697 := bstep (se 2 (by rfl) ⟨737511, by rfl⟩ : syracuseStep 1966697 = 1475023) B1475023
theorem B1966703 : Blo 1309973 1966703 := bstep (se 1 (by rfl) ⟨1475027, by rfl⟩ : syracuseStep 1966703 = 2950055) B2950055
theorem B1311343 : Blo 1309973 1311343 := bstep (se 1 (by rfl) ⟨983507, by rfl⟩ : syracuseStep 1311343 = 1967015) B1967015
theorem B1475239 : Blo 1309973 1475239 := bstep (se 1 (by rfl) ⟨1106429, by rfl⟩ : syracuseStep 1475239 = 2212859) B2212859
theorem B1311399 : Blo 1309973 1311399 := bstep (se 1 (by rfl) ⟨983549, by rfl⟩ : syracuseStep 1311399 = 1967099) B1967099
theorem B1311439 : Blo 1309973 1311439 := bstep (se 1 (by rfl) ⟨983579, by rfl⟩ : syracuseStep 1311439 = 1967159) B1967159
theorem B1311519 : Blo 1309973 1311519 := bstep (se 1 (by rfl) ⟨983639, by rfl⟩ : syracuseStep 1311519 = 1967279) B1967279
theorem B2949929 : Blo 1309973 2949929 := bstep (se 2 (by rfl) ⟨1106223, by rfl⟩ : syracuseStep 2949929 = 2212447) B2212447
theorem B17948071 : Blo 1309973 17948071 := bstep (se 1 (by rfl) ⟨13461053, by rfl⟩ : syracuseStep 17948071 = 26922107) B26922107
theorem B5047127 : Blo 1309973 5047127 := bstep (se 1 (by rfl) ⟨3785345, by rfl⟩ : syracuseStep 5047127 = 7570691) B7570691
theorem B1475527 : Blo 1309973 1475527 := bstep (se 1 (by rfl) ⟨1106645, by rfl⟩ : syracuseStep 1475527 = 2213291) B2213291
theorem B19153907 : Blo 1309973 19153907 := bstep (se 1 (by rfl) ⟨14365430, by rfl⟩ : syracuseStep 19153907 = 28730861) B28730861
theorem B1311791 : Blo 1309973 1311791 := bstep (se 1 (by rfl) ⟨983843, by rfl⟩ : syracuseStep 1311791 = 1967687) B1967687
theorem B2950199 : Blo 1309973 2950199 := bstep (se 1 (by rfl) ⟨2212649, by rfl⟩ : syracuseStep 2950199 = 4425299) B4425299
theorem B1311855 : Blo 1309973 1311855 := bstep (se 1 (by rfl) ⟨983891, by rfl⟩ : syracuseStep 1311855 = 1967783) B1967783
theorem B1311911 : Blo 1309973 1311911 := bstep (se 1 (by rfl) ⟨983933, by rfl⟩ : syracuseStep 1311911 = 1967867) B1967867
theorem B1311935 : Blo 1309973 1311935 := bstep (se 1 (by rfl) ⟨983951, by rfl⟩ : syracuseStep 1311935 = 1967903) B1967903
theorem B1967327 : Blo 1309973 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B1311967 : Blo 1309973 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B2950379 : Blo 1309973 2950379 := bstep (se 1 (by rfl) ⟨2212784, by rfl⟩ : syracuseStep 2950379 = 4425569) B4425569
theorem B1967339 : Blo 1309973 1967339 := bstep (se 1 (by rfl) ⟨1475504, by rfl⟩ : syracuseStep 1967339 = 2951009) B2951009
theorem B1475887 : Blo 1309973 1475887 := bstep (se 1 (by rfl) ⟨1106915, by rfl⟩ : syracuseStep 1475887 = 2213831) B2213831
theorem B1967723 : Blo 1309973 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B8963693 : Blo 1309973 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B4425407 : Blo 1309973 4425407 := bstep (se 1 (by rfl) ⟨3319055, by rfl⟩ : syracuseStep 4425407 = 6638111) B6638111
theorem B2950847 : Blo 1309973 2950847 := bstep (se 1 (by rfl) ⟨2213135, by rfl⟩ : syracuseStep 2950847 = 4426271) B4426271
theorem B1967807 : Blo 1309973 1967807 := bstep (se 1 (by rfl) ⟨1475855, by rfl⟩ : syracuseStep 1967807 = 2951711) B2951711
theorem B4974331 : Blo 1309973 4974331 := bstep (se 1 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 4974331 = 7461497) B7461497
theorem B3319775 : Blo 1309973 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B11192519 : Blo 1309973 11192519 := bstep (se 1 (by rfl) ⟨8394389, by rfl⟩ : syracuseStep 11192519 = 16788779) B16788779
theorem B4974803 : Blo 1309973 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B1993015 : Blo 1309973 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B4196735 : Blo 1309973 4196735 := bstep (se 1 (by rfl) ⟨3147551, by rfl⟩ : syracuseStep 4196735 = 6295103) B6295103
theorem B1771903 : Blo 1309973 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B2951783 : Blo 1309973 2951783 := bstep (se 1 (by rfl) ⟨2213837, by rfl⟩ : syracuseStep 2951783 = 4427675) B4427675
theorem B14174837 : Blo 1309973 14174837 := bstep (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) B1328891
theorem B80693921 : Blo 1309973 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B3148627 : Blo 1309973 3148627 := bstep (se 1 (by rfl) ⟨2361470, by rfl⟩ : syracuseStep 3148627 = 4722941) B4722941
theorem B24243077 : Blo 1309973 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B43084819 : Blo 1309973 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B14937209 : Blo 1309973 14937209 := bstep (se 2 (by rfl) ⟨5601453, by rfl⟩ : syracuseStep 14937209 = 11202907) B11202907
theorem B7285889 : Blo 1309973 7285889 := bstep (se 2 (by rfl) ⟨2732208, by rfl⟩ : syracuseStep 7285889 = 5464417) B5464417
theorem B4427135 : Blo 1309973 4427135 := bstep (se 1 (by rfl) ⟨3320351, by rfl⟩ : syracuseStep 4427135 = 6640703) B6640703
theorem B51105269 : Blo 1309973 51105269 := bstep (se 5 (by rfl) ⟨2395559, by rfl⟩ : syracuseStep 51105269 = 4791119) B4791119
theorem B45412235 : Blo 1309973 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B25546711 : Blo 1309973 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1658875 : Blo 1309973 1658875 := bstep (se 1 (by rfl) ⟨1244156, by rfl⟩ : syracuseStep 1658875 = 2488313) B2488313
theorem B17936579 : Blo 1309973 17936579 := bstep (se 1 (by rfl) ⟨13452434, by rfl⟩ : syracuseStep 17936579 = 26904869) B26904869
theorem B7967119 : Blo 1309973 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B689525237 : Blo 1309973 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B10097207 : Blo 1309973 10097207 := bstep (se 1 (by rfl) ⟨7572905, by rfl⟩ : syracuseStep 10097207 = 15145811) B15145811
theorem B6640217 : Blo 1309973 6640217 := bstep (se 2 (by rfl) ⟨2490081, by rfl⟩ : syracuseStep 6640217 = 4980163) B4980163
theorem B4977247 : Blo 1309973 4977247 := bstep (se 1 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 4977247 = 7465871) B7465871
theorem B7467785 : Blo 1309973 7467785 := bstep (se 2 (by rfl) ⟨2800419, by rfl⟩ : syracuseStep 7467785 = 5600839) B5600839
theorem B4977551 : Blo 1309973 4977551 := bstep (se 1 (by rfl) ⟨3733163, by rfl⟩ : syracuseStep 4977551 = 7466327) B7466327
theorem B12121015 : Blo 1309973 12121015 := bstep (se 1 (by rfl) ⟨9090761, by rfl⟩ : syracuseStep 12121015 = 18181523) B18181523
theorem B9950363 : Blo 1309973 9950363 := bstep (se 1 (by rfl) ⟨7462772, by rfl⟩ : syracuseStep 9950363 = 14925545) B14925545
theorem B3732743 : Blo 1309973 3732743 := bstep (se 1 (by rfl) ⟨2799557, by rfl⟩ : syracuseStep 3732743 = 5599115) B5599115
theorem B19944721 : Blo 1309973 19944721 := bstep (se 2 (by rfl) ⟨7479270, by rfl⟩ : syracuseStep 19944721 = 14958541) B14958541
theorem B3732799 : Blo 1309973 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B4978493 : Blo 1309973 4978493 := bstep (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) B1866935
theorem B27637951 : Blo 1309973 27637951 := bstep (se 1 (by rfl) ⟨20728463, by rfl⟩ : syracuseStep 27637951 = 41456927) B41456927
theorem B4421843 : Blo 1309973 4421843 := bstep (se 1 (by rfl) ⟨3316382, by rfl⟩ : syracuseStep 4421843 = 6632765) B6632765
theorem B2947535 : Blo 1309973 2947535 := bstep (se 1 (by rfl) ⟨2210651, by rfl⟩ : syracuseStep 2947535 = 4421303) B4421303
theorem B4422113 : Blo 1309973 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B2947625 : Blo 1309973 2947625 := bstep (se 2 (by rfl) ⟨1105359, by rfl⟩ : syracuseStep 2947625 = 2210719) B2210719
theorem B1866331 : Blo 1309973 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B4979465 : Blo 1309973 4979465 := bstep (se 2 (by rfl) ⟨1867299, by rfl⟩ : syracuseStep 4979465 = 3734599) B3734599
theorem B1399663 : Blo 1309973 1399663 := bstep (se 1 (by rfl) ⟨1049747, by rfl⟩ : syracuseStep 1399663 = 2099495) B2099495
theorem B1965161 : Blo 1309973 1965161 := bstep (se 2 (by rfl) ⟨736935, by rfl⟩ : syracuseStep 1965161 = 1473871) B1473871
theorem B2948201 : Blo 1309973 2948201 := bstep (se 2 (by rfl) ⟨1105575, by rfl⟩ : syracuseStep 2948201 = 2211151) B2211151
theorem B9452659 : Blo 1309973 9452659 := bstep (se 1 (by rfl) ⟨7089494, by rfl⟩ : syracuseStep 9452659 = 14178989) B14178989
theorem B1965287 : Blo 1309973 1965287 := bstep (se 1 (by rfl) ⟨1473965, by rfl⟩ : syracuseStep 1965287 = 2947931) B2947931
theorem B2948327 : Blo 1309973 2948327 := bstep (se 1 (by rfl) ⟨2211245, by rfl⟩ : syracuseStep 2948327 = 4422491) B4422491
theorem B1310023 : Blo 1309973 1310023 := bstep (se 1 (by rfl) ⟨982517, by rfl⟩ : syracuseStep 1310023 = 1965035) B1965035
theorem B2489771 : Blo 1309973 2489771 := bstep (se 1 (by rfl) ⟨1867328, by rfl⟩ : syracuseStep 2489771 = 3734657) B3734657
theorem B4259243 : Blo 1309973 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B45383111 : Blo 1309973 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B1310159 : Blo 1309973 1310159 := bstep (se 1 (by rfl) ⟨982619, by rfl⟩ : syracuseStep 1310159 = 1965239) B1965239
theorem B12598739 : Blo 1309973 12598739 := bstep (se 1 (by rfl) ⟨9449054, by rfl⟩ : syracuseStep 12598739 = 18898109) B18898109
theorem B1310319 : Blo 1309973 1310319 := bstep (se 1 (by rfl) ⟨982739, by rfl⟩ : syracuseStep 1310319 = 1965479) B1965479
theorem B1474159 : Blo 1309973 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B1310375 : Blo 1309973 1310375 := bstep (se 1 (by rfl) ⟨982781, by rfl⟩ : syracuseStep 1310375 = 1965563) B1965563
theorem B1474267 : Blo 1309973 1474267 := bstep (se 1 (by rfl) ⟨1105700, by rfl⟩ : syracuseStep 1474267 = 2211401) B2211401
theorem B1965791 : Blo 1309973 1965791 := bstep (se 1 (by rfl) ⟨1474343, by rfl⟩ : syracuseStep 1965791 = 2948687) B2948687
theorem B2948831 : Blo 1309973 2948831 := bstep (se 1 (by rfl) ⟨2211623, by rfl⟩ : syracuseStep 2948831 = 4423247) B4423247
theorem B1310439 : Blo 1309973 1310439 := bstep (se 1 (by rfl) ⟨982829, by rfl⟩ : syracuseStep 1310439 = 1965659) B1965659
theorem B4980467 : Blo 1309973 4980467 := bstep (se 1 (by rfl) ⟨3735350, by rfl⟩ : syracuseStep 4980467 = 7470701) B7470701
theorem B1965833 : Blo 1309973 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B3735305 : Blo 1309973 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B1310495 : Blo 1309973 1310495 := bstep (se 1 (by rfl) ⟨982871, by rfl⟩ : syracuseStep 1310495 = 1965743) B1965743
theorem B2948903 : Blo 1309973 2948903 := bstep (se 1 (by rfl) ⟨2211677, by rfl⟩ : syracuseStep 2948903 = 4423355) B4423355
theorem B4423463 : Blo 1309973 4423463 := bstep (se 1 (by rfl) ⟨3317597, by rfl⟩ : syracuseStep 4423463 = 6635195) B6635195
theorem B21249863 : Blo 1309973 21249863 := bstep (se 1 (by rfl) ⟨15937397, by rfl⟩ : syracuseStep 21249863 = 31874795) B31874795
theorem B1310575 : Blo 1309973 1310575 := bstep (se 1 (by rfl) ⟨982931, by rfl⟩ : syracuseStep 1310575 = 1965863) B1965863
theorem B5603215 : Blo 1309973 5603215 := bstep (se 1 (by rfl) ⟨4202411, by rfl⟩ : syracuseStep 5603215 = 8404823) B8404823
theorem B1310631 : Blo 1309973 1310631 := bstep (se 1 (by rfl) ⟨982973, by rfl⟩ : syracuseStep 1310631 = 1965947) B1965947
theorem B1310847 : Blo 1309973 1310847 := bstep (se 1 (by rfl) ⟨983135, by rfl⟩ : syracuseStep 1310847 = 1966271) B1966271
theorem B2212103 : Blo 1309973 2212103 := bstep (se 1 (by rfl) ⟨1659077, by rfl⟩ : syracuseStep 2212103 = 3318155) B3318155
theorem B1311131 : Blo 1309973 1311131 := bstep (se 1 (by rfl) ⟨983348, by rfl⟩ : syracuseStep 1311131 = 1966697) B1966697
theorem B1311135 : Blo 1309973 1311135 := bstep (se 1 (by rfl) ⟨983351, by rfl⟩ : syracuseStep 1311135 = 1966703) B1966703
theorem B9953765 : Blo 1309973 9953765 := bstep (se 4 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 9953765 = 1866331) B1866331
theorem B1966619 : Blo 1309973 1966619 := bstep (se 1 (by rfl) ⟨1474964, by rfl⟩ : syracuseStep 1966619 = 2949929) B2949929
theorem B3318367 : Blo 1309973 3318367 := bstep (se 1 (by rfl) ⟨2488775, by rfl⟩ : syracuseStep 3318367 = 4977551) B4977551
theorem B1966799 : Blo 1309973 1966799 := bstep (se 1 (by rfl) ⟨1475099, by rfl⟩ : syracuseStep 1966799 = 2950199) B2950199
theorem B6636329 : Blo 1309973 6636329 := bstep (se 2 (by rfl) ⟨2488623, by rfl⟩ : syracuseStep 6636329 = 4977247) B4977247
theorem B1311551 : Blo 1309973 1311551 := bstep (se 1 (by rfl) ⟨983663, by rfl⟩ : syracuseStep 1311551 = 1967327) B1967327
theorem B1966919 : Blo 1309973 1966919 := bstep (se 1 (by rfl) ⟨1475189, by rfl⟩ : syracuseStep 1966919 = 2950379) B2950379
theorem B1311559 : Blo 1309973 1311559 := bstep (se 1 (by rfl) ⟨983669, by rfl⟩ : syracuseStep 1311559 = 1967339) B1967339
theorem B1966985 : Blo 1309973 1966985 := bstep (se 2 (by rfl) ⟨737619, by rfl⟩ : syracuseStep 1966985 = 1475239) B1475239
theorem B1311815 : Blo 1309973 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B2950271 : Blo 1309973 2950271 := bstep (se 1 (by rfl) ⟨2212703, by rfl⟩ : syracuseStep 2950271 = 4425407) B4425407
theorem B1967231 : Blo 1309973 1967231 := bstep (se 1 (by rfl) ⟨1475423, by rfl⟩ : syracuseStep 1967231 = 2950847) B2950847
theorem B1311871 : Blo 1309973 1311871 := bstep (se 1 (by rfl) ⟨983903, by rfl⟩ : syracuseStep 1311871 = 1967807) B1967807
theorem B3318995 : Blo 1309973 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B1967369 : Blo 1309973 1967369 := bstep (se 2 (by rfl) ⟨737763, by rfl⟩ : syracuseStep 1967369 = 1475527) B1475527
theorem B2213183 : Blo 1309973 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B4857259 : Blo 1309973 4857259 := bstep (se 1 (by rfl) ⟨3642944, by rfl⟩ : syracuseStep 4857259 = 7285889) B7285889
theorem B26592961 : Blo 1309973 26592961 := bstep (se 2 (by rfl) ⟨9972360, by rfl⟩ : syracuseStep 26592961 = 19944721) B19944721
theorem B1967849 : Blo 1309973 1967849 := bstep (se 2 (by rfl) ⟨737943, by rfl⟩ : syracuseStep 1967849 = 1475887) B1475887
theorem B1967855 : Blo 1309973 1967855 := bstep (se 1 (by rfl) ⟨1475891, by rfl⟩ : syracuseStep 1967855 = 2951783) B2951783
theorem B3319643 : Blo 1309973 3319643 := bstep (se 1 (by rfl) ⟨2489732, by rfl⟩ : syracuseStep 3319643 = 4979465) B4979465
theorem B7464869 : Blo 1309973 7464869 := bstep (se 4 (by rfl) ⟨699831, by rfl⟩ : syracuseStep 7464869 = 1399663) B1399663
theorem B295020629 : Blo 1309973 295020629 := bstep (se 8 (by rfl) ⟨1728636, by rfl⟩ : syracuseStep 295020629 = 3457273) B3457273
theorem B2951423 : Blo 1309973 2951423 := bstep (se 1 (by rfl) ⟨2213567, by rfl⟩ : syracuseStep 2951423 = 4427135) B4427135
theorem B5318939 : Blo 1309973 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B30255407 : Blo 1309973 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B8399159 : Blo 1309973 8399159 := bstep (se 1 (by rfl) ⟨6299369, by rfl⟩ : syracuseStep 8399159 = 12598739) B12598739
theorem B3320311 : Blo 1309973 3320311 := bstep (se 1 (by rfl) ⟨2490233, by rfl⟩ : syracuseStep 3320311 = 4980467) B4980467
theorem B14166575 : Blo 1309973 14166575 := bstep (se 1 (by rfl) ⟨10624931, by rfl⟩ : syracuseStep 14166575 = 21249863) B21249863
theorem B3320615 : Blo 1309973 3320615 := bstep (se 1 (by rfl) ⟨2490461, by rfl⟩ : syracuseStep 3320615 = 4980923) B4980923
theorem B8399699 : Blo 1309973 8399699 := bstep (se 1 (by rfl) ⟨6299774, by rfl⟩ : syracuseStep 8399699 = 12599549) B12599549
theorem B36850601 : Blo 1309973 36850601 := bstep (se 2 (by rfl) ⟨13818975, by rfl⟩ : syracuseStep 36850601 = 27637951) B27637951
theorem B4426811 : Blo 1309973 4426811 := bstep (se 1 (by rfl) ⟨3320108, by rfl⟩ : syracuseStep 4426811 = 6640217) B6640217
theorem B2362537 : Blo 1309973 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B5975795 : Blo 1309973 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B4198169 : Blo 1309973 4198169 := bstep (se 2 (by rfl) ⟨1574313, by rfl⟩ : syracuseStep 4198169 = 3148627) B3148627
theorem B11357981 : Blo 1309973 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B57446425 : Blo 1309973 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B12603545 : Blo 1309973 12603545 := bstep (se 2 (by rfl) ⟨4726329, by rfl⟩ : syracuseStep 12603545 = 9452659) B9452659
theorem B2797823 : Blo 1309973 2797823 := bstep (se 1 (by rfl) ⟨2098367, by rfl⟩ : syracuseStep 2797823 = 4196735) B4196735
theorem B10629413 : Blo 1309973 10629413 := bstep (se 4 (by rfl) ⟨996507, by rfl⟩ : syracuseStep 10629413 = 1993015) B1993015
theorem B9449891 : Blo 1309973 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B4977065 : Blo 1309973 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B9958139 : Blo 1309973 9958139 := bstep (se 1 (by rfl) ⟨7468604, by rfl⟩ : syracuseStep 9958139 = 14937209) B14937209
theorem B1659847 : Blo 1309973 1659847 := bstep (se 1 (by rfl) ⟨1244885, by rfl⟩ : syracuseStep 1659847 = 2489771) B2489771
theorem B6632441 : Blo 1309973 6632441 := bstep (se 2 (by rfl) ⟨2487165, by rfl⟩ : syracuseStep 6632441 = 4974331) B4974331
theorem B30274823 : Blo 1309973 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B4199759 : Blo 1309973 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B11957719 : Blo 1309973 11957719 := bstep (se 1 (by rfl) ⟨8968289, by rfl⟩ : syracuseStep 11957719 = 17936579) B17936579
theorem B6731471 : Blo 1309973 6731471 := bstep (se 1 (by rfl) ⟨5048603, by rfl⟩ : syracuseStep 6731471 = 10097207) B10097207
theorem B11196143 : Blo 1309973 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B4978523 : Blo 1309973 4978523 := bstep (se 1 (by rfl) ⟨3733892, by rfl⟩ : syracuseStep 4978523 = 7467785) B7467785
theorem B10622825 : Blo 1309973 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B3364751 : Blo 1309973 3364751 := bstep (se 1 (by rfl) ⟨2523563, by rfl⟩ : syracuseStep 3364751 = 5047127) B5047127
theorem B12769271 : Blo 1309973 12769271 := bstep (se 1 (by rfl) ⟨9576953, by rfl⟩ : syracuseStep 12769271 = 19153907) B19153907
theorem B6633575 : Blo 1309973 6633575 := bstep (se 1 (by rfl) ⟨4975181, by rfl⟩ : syracuseStep 6633575 = 9950363) B9950363
theorem B2488495 : Blo 1309973 2488495 := bstep (se 1 (by rfl) ⟨1866371, by rfl⟩ : syracuseStep 2488495 = 3732743) B3732743
theorem B16161353 : Blo 1309973 16161353 := bstep (se 2 (by rfl) ⟨6060507, by rfl⟩ : syracuseStep 16161353 = 12121015) B12121015
theorem B1838733965 : Blo 1309973 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B136280717 : Blo 1309973 136280717 := bstep (se 3 (by rfl) ⟨25552634, by rfl⟩ : syracuseStep 136280717 = 51105269) B51105269
theorem B7461679 : Blo 1309973 7461679 := bstep (se 1 (by rfl) ⟨5596259, by rfl⟩ : syracuseStep 7461679 = 11192519) B11192519
theorem B2947895 : Blo 1309973 2947895 := bstep (se 1 (by rfl) ⟨2210921, by rfl⟩ : syracuseStep 2947895 = 4421843) B4421843
theorem B3316535 : Blo 1309973 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B1965023 : Blo 1309973 1965023 := bstep (se 1 (by rfl) ⟨1473767, by rfl⟩ : syracuseStep 1965023 = 2947535) B2947535
theorem B2948075 : Blo 1309973 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B1965083 : Blo 1309973 1965083 := bstep (se 1 (by rfl) ⟨1473812, by rfl⟩ : syracuseStep 1965083 = 2947625) B2947625
theorem B53795947 : Blo 1309973 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B16162051 : Blo 1309973 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B1310107 : Blo 1309973 1310107 := bstep (se 1 (by rfl) ⟨982580, by rfl⟩ : syracuseStep 1310107 = 1965161) B1965161
theorem B1965467 : Blo 1309973 1965467 := bstep (se 1 (by rfl) ⟨1474100, by rfl⟩ : syracuseStep 1965467 = 2948201) B2948201
theorem B1965545 : Blo 1309973 1965545 := bstep (se 2 (by rfl) ⟨737079, by rfl⟩ : syracuseStep 1965545 = 1474159) B1474159
theorem B1310191 : Blo 1309973 1310191 := bstep (se 1 (by rfl) ⟨982643, by rfl⟩ : syracuseStep 1310191 = 1965287) B1965287
theorem B1965551 : Blo 1309973 1965551 := bstep (se 1 (by rfl) ⟨1474163, by rfl⟩ : syracuseStep 1965551 = 2948327) B2948327
theorem B95723045 : Blo 1309973 95723045 := bstep (se 4 (by rfl) ⟨8974035, by rfl⟩ : syracuseStep 95723045 = 17948071) B17948071
theorem B1965689 : Blo 1309973 1965689 := bstep (se 2 (by rfl) ⟨737133, by rfl⟩ : syracuseStep 1965689 = 1474267) B1474267
theorem B1310527 : Blo 1309973 1310527 := bstep (se 1 (by rfl) ⟨982895, by rfl⟩ : syracuseStep 1310527 = 1965791) B1965791
theorem B1965887 : Blo 1309973 1965887 := bstep (se 1 (by rfl) ⟨1474415, by rfl⟩ : syracuseStep 1965887 = 2948831) B2948831
theorem B1310555 : Blo 1309973 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B2490203 : Blo 1309973 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B1965935 : Blo 1309973 1965935 := bstep (se 1 (by rfl) ⟨1474451, by rfl⟩ : syracuseStep 1965935 = 2948903) B2948903
theorem B2948975 : Blo 1309973 2948975 := bstep (se 1 (by rfl) ⟨2211731, by rfl⟩ : syracuseStep 2948975 = 4423463) B4423463
theorem B7470953 : Blo 1309973 7470953 := bstep (se 2 (by rfl) ⟨2801607, by rfl⟩ : syracuseStep 7470953 = 5603215) B5603215
theorem B34062281 : Blo 1309973 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B2211833 : Blo 1309973 2211833 := bstep (se 2 (by rfl) ⟨829437, by rfl⟩ : syracuseStep 2211833 = 1658875) B1658875
theorem B76595233 : Blo 1309973 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B1474735 : Blo 1309973 1474735 := bstep (se 1 (by rfl) ⟨1106051, by rfl⟩ : syracuseStep 1474735 = 2212103) B2212103
theorem B7086275 : Blo 1309973 7086275 := bstep (se 1 (by rfl) ⟨5314706, by rfl⟩ : syracuseStep 7086275 = 10629413) B10629413
theorem B3317993 : Blo 1309973 3317993 := bstep (se 2 (by rfl) ⟨1244247, by rfl⟩ : syracuseStep 3317993 = 2488495) B2488495
theorem B6299927 : Blo 1309973 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B3318043 : Blo 1309973 3318043 := bstep (se 1 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 3318043 = 4977065) B4977065
theorem B6635843 : Blo 1309973 6635843 := bstep (se 1 (by rfl) ⟨4976882, by rfl⟩ : syracuseStep 6635843 = 9953765) B9953765
theorem B1311079 : Blo 1309973 1311079 := bstep (se 1 (by rfl) ⟨983309, by rfl⟩ : syracuseStep 1311079 = 1966619) B1966619
theorem B1311199 : Blo 1309973 1311199 := bstep (se 1 (by rfl) ⟨983399, by rfl⟩ : syracuseStep 1311199 = 1966799) B1966799
theorem B4424219 : Blo 1309973 4424219 := bstep (se 1 (by rfl) ⟨3318164, by rfl⟩ : syracuseStep 4424219 = 6636329) B6636329
theorem B1311279 : Blo 1309973 1311279 := bstep (se 1 (by rfl) ⟨983459, by rfl⟩ : syracuseStep 1311279 = 1966919) B1966919
theorem B1311323 : Blo 1309973 1311323 := bstep (se 1 (by rfl) ⟨983492, by rfl⟩ : syracuseStep 1311323 = 1966985) B1966985
theorem B1966847 : Blo 1309973 1966847 := bstep (se 1 (by rfl) ⟨1475135, by rfl⟩ : syracuseStep 1966847 = 2950271) B2950271
theorem B1311487 : Blo 1309973 1311487 := bstep (se 1 (by rfl) ⟨983615, by rfl⟩ : syracuseStep 1311487 = 1967231) B1967231
theorem B4424489 : Blo 1309973 4424489 := bstep (se 2 (by rfl) ⟨1659183, by rfl⟩ : syracuseStep 4424489 = 3318367) B3318367
theorem B2212663 : Blo 1309973 2212663 := bstep (se 1 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 2212663 = 3318995) B3318995
theorem B1311579 : Blo 1309973 1311579 := bstep (se 1 (by rfl) ⟨983684, by rfl⟩ : syracuseStep 1311579 = 1967369) B1967369
theorem B1475455 : Blo 1309973 1475455 := bstep (se 1 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 1475455 = 2213183) B2213183
theorem B12600197 : Blo 1309973 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1311899 : Blo 1309973 1311899 := bstep (se 1 (by rfl) ⟨983924, by rfl⟩ : syracuseStep 1311899 = 1967849) B1967849
theorem B7464095 : Blo 1309973 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B1311903 : Blo 1309973 1311903 := bstep (se 1 (by rfl) ⟨983927, by rfl⟩ : syracuseStep 1311903 = 1967855) B1967855
theorem B3319015 : Blo 1309973 3319015 := bstep (se 1 (by rfl) ⟨2489261, by rfl⟩ : syracuseStep 3319015 = 4978523) B4978523
theorem B2213095 : Blo 1309973 2213095 := bstep (se 1 (by rfl) ⟨1659821, by rfl⟩ : syracuseStep 2213095 = 3319643) B3319643
theorem B2213129 : Blo 1309973 2213129 := bstep (se 2 (by rfl) ⟨829923, by rfl⟩ : syracuseStep 2213129 = 1659847) B1659847
theorem B8512847 : Blo 1309973 8512847 := bstep (se 1 (by rfl) ⟨6384635, by rfl⟩ : syracuseStep 8512847 = 12769271) B12769271
theorem B1967615 : Blo 1309973 1967615 := bstep (se 1 (by rfl) ⟨1475711, by rfl⟩ : syracuseStep 1967615 = 2951423) B2951423
theorem B20170271 : Blo 1309973 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B10774235 : Blo 1309973 10774235 := bstep (se 1 (by rfl) ⟨8080676, by rfl⟩ : syracuseStep 10774235 = 16161353) B16161353
theorem B2213743 : Blo 1309973 2213743 := bstep (se 1 (by rfl) ⟨1660307, by rfl⟩ : syracuseStep 2213743 = 3320615) B3320615
theorem B17950589 : Blo 1309973 17950589 := bstep (se 3 (by rfl) ⟨3365735, by rfl⟩ : syracuseStep 17950589 = 6731471) B6731471
theorem B15943625 : Blo 1309973 15943625 := bstep (se 2 (by rfl) ⟨5978859, by rfl⟩ : syracuseStep 15943625 = 11957719) B11957719
theorem B15935453 : Blo 1309973 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B2951207 : Blo 1309973 2951207 := bstep (se 1 (by rfl) ⟨2213405, by rfl⟩ : syracuseStep 2951207 = 4426811) B4426811
theorem B35457281 : Blo 1309973 35457281 := bstep (se 2 (by rfl) ⟨13296480, by rfl⟩ : syracuseStep 35457281 = 26592961) B26592961
theorem B8972669 : Blo 1309973 8972669 := bstep (se 3 (by rfl) ⟨1682375, by rfl⟩ : syracuseStep 8972669 = 3364751) B3364751
theorem B7571987 : Blo 1309973 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B6638759 : Blo 1309973 6638759 := bstep (se 1 (by rfl) ⟨4979069, by rfl⟩ : syracuseStep 6638759 = 9958139) B9958139
theorem B4427081 : Blo 1309973 4427081 := bstep (se 2 (by rfl) ⟨1660155, by rfl⟩ : syracuseStep 4427081 = 3320311) B3320311
theorem B9948905 : Blo 1309973 9948905 := bstep (se 2 (by rfl) ⟨3730839, by rfl⟩ : syracuseStep 9948905 = 7461679) B7461679
theorem B7081883 : Blo 1309973 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B4976579 : Blo 1309973 4976579 := bstep (se 1 (by rfl) ⟨3732434, by rfl⟩ : syracuseStep 4976579 = 7464869) B7464869
theorem B5599439 : Blo 1309973 5599439 := bstep (se 1 (by rfl) ⟨4199579, by rfl⟩ : syracuseStep 5599439 = 8399159) B8399159
theorem B21549401 : Blo 1309973 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B1225822643 : Blo 1309973 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B90853811 : Blo 1309973 90853811 := bstep (se 1 (by rfl) ⟨68140358, by rfl⟩ : syracuseStep 90853811 = 136280717) B136280717
theorem B5599799 : Blo 1309973 5599799 := bstep (se 1 (by rfl) ⟨4199849, by rfl⟩ : syracuseStep 5599799 = 8399699) B8399699
theorem B6476345 : Blo 1309973 6476345 := bstep (se 2 (by rfl) ⟨2428629, by rfl⟩ : syracuseStep 6476345 = 4857259) B4857259
theorem B11195117 : Blo 1309973 11195117 := bstep (se 3 (by rfl) ⟨2099084, by rfl⟩ : syracuseStep 11195117 = 4198169) B4198169
theorem B6640541 : Blo 1309973 6640541 := bstep (se 3 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 6640541 = 2490203) B2490203
theorem B8402363 : Blo 1309973 8402363 := bstep (se 1 (by rfl) ⟨6301772, by rfl⟩ : syracuseStep 8402363 = 12603545) B12603545
theorem B1865215 : Blo 1309973 1865215 := bstep (se 1 (by rfl) ⟨1398911, by rfl⟩ : syracuseStep 1865215 = 2797823) B2797823
theorem B4421627 : Blo 1309973 4421627 := bstep (se 1 (by rfl) ⟨3316220, by rfl⟩ : syracuseStep 4421627 = 6632441) B6632441
theorem B20183215 : Blo 1309973 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B2799839 : Blo 1309973 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B196680419 : Blo 1309973 196680419 := bstep (se 1 (by rfl) ⟨147510314, by rfl⟩ : syracuseStep 196680419 = 295020629) B295020629
theorem B4422383 : Blo 1309973 4422383 := bstep (se 1 (by rfl) ⟨3316787, by rfl⟩ : syracuseStep 4422383 = 6633575) B6633575
theorem B71727929 : Blo 1309973 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B3545959 : Blo 1309973 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B9444383 : Blo 1309973 9444383 := bstep (se 1 (by rfl) ⟨7083287, by rfl⟩ : syracuseStep 9444383 = 14166575) B14166575
theorem B1965263 : Blo 1309973 1965263 := bstep (se 1 (by rfl) ⟨1473947, by rfl⟩ : syracuseStep 1965263 = 2947895) B2947895
theorem B2211023 : Blo 1309973 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B24567067 : Blo 1309973 24567067 := bstep (se 1 (by rfl) ⟨18425300, by rfl⟩ : syracuseStep 24567067 = 36850601) B36850601
theorem B1310015 : Blo 1309973 1310015 := bstep (se 1 (by rfl) ⟨982511, by rfl⟩ : syracuseStep 1310015 = 1965023) B1965023
theorem B1965383 : Blo 1309973 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B1310055 : Blo 1309973 1310055 := bstep (se 1 (by rfl) ⟨982541, by rfl⟩ : syracuseStep 1310055 = 1965083) B1965083
theorem B1310311 : Blo 1309973 1310311 := bstep (se 1 (by rfl) ⟨982733, by rfl⟩ : syracuseStep 1310311 = 1965467) B1965467
theorem B1310363 : Blo 1309973 1310363 := bstep (se 1 (by rfl) ⟨982772, by rfl⟩ : syracuseStep 1310363 = 1965545) B1965545
theorem B1310367 : Blo 1309973 1310367 := bstep (se 1 (by rfl) ⟨982775, by rfl⟩ : syracuseStep 1310367 = 1965551) B1965551
theorem B63815363 : Blo 1309973 63815363 := bstep (se 1 (by rfl) ⟨47861522, by rfl⟩ : syracuseStep 63815363 = 95723045) B95723045
theorem B1310459 : Blo 1309973 1310459 := bstep (se 1 (by rfl) ⟨982844, by rfl⟩ : syracuseStep 1310459 = 1965689) B1965689
theorem B1310591 : Blo 1309973 1310591 := bstep (se 1 (by rfl) ⟨982943, by rfl⟩ : syracuseStep 1310591 = 1965887) B1965887
theorem B4980635 : Blo 1309973 4980635 := bstep (se 1 (by rfl) ⟨3735476, by rfl⟩ : syracuseStep 4980635 = 7470953) B7470953
theorem B1310623 : Blo 1309973 1310623 := bstep (se 1 (by rfl) ⟨982967, by rfl⟩ : syracuseStep 1310623 = 1965935) B1965935
theorem B1965983 : Blo 1309973 1965983 := bstep (se 1 (by rfl) ⟨1474487, by rfl⟩ : syracuseStep 1965983 = 2948975) B2948975
theorem B22708187 : Blo 1309973 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B1474555 : Blo 1309973 1474555 := bstep (se 1 (by rfl) ⟨1105916, by rfl⟩ : syracuseStep 1474555 = 2211833) B2211833
theorem B2211995 : Blo 1309973 2211995 := bstep (se 1 (by rfl) ⟨1658996, by rfl⟩ : syracuseStep 2211995 = 3317993) B3317993
theorem B4423895 : Blo 1309973 4423895 := bstep (se 1 (by rfl) ⟨3317921, by rfl⟩ : syracuseStep 4423895 = 6635843) B6635843
theorem B1966313 : Blo 1309973 1966313 := bstep (se 2 (by rfl) ⟨737367, by rfl⟩ : syracuseStep 1966313 = 1474735) B1474735
theorem B26910953 : Blo 1309973 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B2949479 : Blo 1309973 2949479 := bstep (se 1 (by rfl) ⟨2212109, by rfl⟩ : syracuseStep 2949479 = 4424219) B4424219
theorem B4424057 : Blo 1309973 4424057 := bstep (se 2 (by rfl) ⟨1659021, by rfl⟩ : syracuseStep 4424057 = 3318043) B3318043
theorem B4317563 : Blo 1309973 4317563 := bstep (se 1 (by rfl) ⟨3238172, by rfl⟩ : syracuseStep 4317563 = 6476345) B6476345
theorem B7463411 : Blo 1309973 7463411 := bstep (se 1 (by rfl) ⟨5597558, by rfl⟩ : syracuseStep 7463411 = 11195117) B11195117
theorem B1311231 : Blo 1309973 1311231 := bstep (se 1 (by rfl) ⟨983423, by rfl⟩ : syracuseStep 1311231 = 1966847) B1966847
theorem B2949659 : Blo 1309973 2949659 := bstep (se 1 (by rfl) ⟨2212244, by rfl⟩ : syracuseStep 2949659 = 4424489) B4424489
theorem B1475419 : Blo 1309973 1475419 := bstep (se 1 (by rfl) ⟨1106564, by rfl⟩ : syracuseStep 1475419 = 2213129) B2213129
theorem B1311743 : Blo 1309973 1311743 := bstep (se 1 (by rfl) ⟨983807, by rfl⟩ : syracuseStep 1311743 = 1967615) B1967615
theorem B2950217 : Blo 1309973 2950217 := bstep (se 2 (by rfl) ⟨1106331, by rfl⟩ : syracuseStep 2950217 = 2212663) B2212663
theorem B4727945 : Blo 1309973 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B1967273 : Blo 1309973 1967273 := bstep (se 2 (by rfl) ⟨737727, by rfl⟩ : syracuseStep 1967273 = 1475455) B1475455
theorem B1967471 : Blo 1309973 1967471 := bstep (se 1 (by rfl) ⟨1475603, by rfl⟩ : syracuseStep 1967471 = 2951207) B2951207
theorem B5981779 : Blo 1309973 5981779 := bstep (se 1 (by rfl) ⟨4486334, by rfl⟩ : syracuseStep 5981779 = 8972669) B8972669
theorem B4425353 : Blo 1309973 4425353 := bstep (se 2 (by rfl) ⟨1659507, by rfl⟩ : syracuseStep 4425353 = 3319015) B3319015
theorem B2950793 : Blo 1309973 2950793 := bstep (se 2 (by rfl) ⟨1106547, by rfl⟩ : syracuseStep 2950793 = 2213095) B2213095
theorem B5047991 : Blo 1309973 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B47818619 : Blo 1309973 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B28731293 : Blo 1309973 28731293 := bstep (se 3 (by rfl) ⟨5387117, by rfl⟩ : syracuseStep 28731293 = 10774235) B10774235
theorem B4425839 : Blo 1309973 4425839 := bstep (se 1 (by rfl) ⟨3319379, by rfl⟩ : syracuseStep 4425839 = 6638759) B6638759
theorem B2951387 : Blo 1309973 2951387 := bstep (se 1 (by rfl) ⟨2213540, by rfl⟩ : syracuseStep 2951387 = 4427081) B4427081
theorem B42543575 : Blo 1309973 42543575 := bstep (se 1 (by rfl) ⟨31907681, by rfl⟩ : syracuseStep 42543575 = 63815363) B63815363
theorem B2951657 : Blo 1309973 2951657 := bstep (se 2 (by rfl) ⟨1106871, by rfl⟩ : syracuseStep 2951657 = 2213743) B2213743
theorem B4721255 : Blo 1309973 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B3320423 : Blo 1309973 3320423 := bstep (se 1 (by rfl) ⟨2490317, by rfl⟩ : syracuseStep 3320423 = 4980635) B4980635
theorem B378210997 : Blo 1309973 378210997 := bstep (se 5 (by rfl) ⟨17728640, by rfl⟩ : syracuseStep 378210997 = 35457281) B35457281
theorem B8400131 : Blo 1309973 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B4427027 : Blo 1309973 4427027 := bstep (se 1 (by rfl) ⟨3320270, by rfl⟩ : syracuseStep 4427027 = 6640541) B6640541
theorem B4976063 : Blo 1309973 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B13446847 : Blo 1309973 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B10629083 : Blo 1309973 10629083 := bstep (se 1 (by rfl) ⟨7971812, by rfl⟩ : syracuseStep 10629083 = 15943625) B15943625
theorem B1966073 : Blo 1309973 1966073 := bstep (se 2 (by rfl) ⟨737277, by rfl⟩ : syracuseStep 1966073 = 1474555) B1474555
theorem B32756089 : Blo 1309973 32756089 := bstep (se 2 (by rfl) ⟨12283533, by rfl⟩ : syracuseStep 32756089 = 24567067) B24567067
theorem B2486953 : Blo 1309973 2486953 := bstep (se 2 (by rfl) ⟨932607, by rfl⟩ : syracuseStep 2486953 = 1865215) B1865215
theorem B6296255 : Blo 1309973 6296255 := bstep (se 1 (by rfl) ⟨4722191, by rfl⟩ : syracuseStep 6296255 = 9444383) B9444383
theorem B6632603 : Blo 1309973 6632603 := bstep (se 1 (by rfl) ⟨4974452, by rfl⟩ : syracuseStep 6632603 = 9948905) B9948905
theorem B102126977 : Blo 1309973 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B4724183 : Blo 1309973 4724183 := bstep (se 1 (by rfl) ⟨3543137, by rfl⟩ : syracuseStep 4724183 = 7086275) B7086275
theorem B3732959 : Blo 1309973 3732959 := bstep (se 1 (by rfl) ⟨2799719, by rfl⟩ : syracuseStep 3732959 = 5599439) B5599439
theorem B4199951 : Blo 1309973 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B14366267 : Blo 1309973 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B817215095 : Blo 1309973 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B60569207 : Blo 1309973 60569207 := bstep (se 1 (by rfl) ⟨45426905, by rfl⟩ : syracuseStep 60569207 = 90853811) B90853811
theorem B3733199 : Blo 1309973 3733199 := bstep (se 1 (by rfl) ⟨2799899, by rfl⟩ : syracuseStep 3733199 = 5599799) B5599799
theorem B15138791 : Blo 1309973 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B5675231 : Blo 1309973 5675231 := bstep (se 1 (by rfl) ⟨4256423, by rfl⟩ : syracuseStep 5675231 = 8512847) B8512847
theorem B5601575 : Blo 1309973 5601575 := bstep (se 1 (by rfl) ⟨4201181, by rfl⟩ : syracuseStep 5601575 = 8402363) B8402363
theorem B11967059 : Blo 1309973 11967059 := bstep (se 1 (by rfl) ⟨8975294, by rfl⟩ : syracuseStep 11967059 = 17950589) B17950589
theorem B10623635 : Blo 1309973 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B2947751 : Blo 1309973 2947751 := bstep (se 1 (by rfl) ⟨2210813, by rfl⟩ : syracuseStep 2947751 = 4421627) B4421627
theorem B1866559 : Blo 1309973 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B131120279 : Blo 1309973 131120279 := bstep (se 1 (by rfl) ⟨98340209, by rfl⟩ : syracuseStep 131120279 = 196680419) B196680419
theorem B2948255 : Blo 1309973 2948255 := bstep (se 1 (by rfl) ⟨2211191, by rfl⟩ : syracuseStep 2948255 = 4422383) B4422383
theorem B1310175 : Blo 1309973 1310175 := bstep (se 1 (by rfl) ⟨982631, by rfl⟩ : syracuseStep 1310175 = 1965263) B1965263
theorem B1474015 : Blo 1309973 1474015 := bstep (se 1 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 1474015 = 2211023) B2211023
theorem B1310255 : Blo 1309973 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B1310655 : Blo 1309973 1310655 := bstep (se 1 (by rfl) ⟨982991, by rfl⟩ : syracuseStep 1310655 = 1965983) B1965983
theorem B3317719 : Blo 1309973 3317719 := bstep (se 1 (by rfl) ⟨2488289, by rfl⟩ : syracuseStep 3317719 = 4976579) B4976579
theorem B1474663 : Blo 1309973 1474663 := bstep (se 1 (by rfl) ⟨1105997, by rfl⟩ : syracuseStep 1474663 = 2211995) B2211995
theorem B2949263 : Blo 1309973 2949263 := bstep (se 1 (by rfl) ⟨2211947, by rfl⟩ : syracuseStep 2949263 = 4423895) B4423895
theorem B1310875 : Blo 1309973 1310875 := bstep (se 1 (by rfl) ⟨983156, by rfl⟩ : syracuseStep 1310875 = 1966313) B1966313
theorem B1966319 : Blo 1309973 1966319 := bstep (se 1 (by rfl) ⟨1474739, by rfl⟩ : syracuseStep 1966319 = 2949479) B2949479
theorem B2949371 : Blo 1309973 2949371 := bstep (se 1 (by rfl) ⟨2212028, by rfl⟩ : syracuseStep 2949371 = 4424057) B4424057
theorem B1966439 : Blo 1309973 1966439 := bstep (se 1 (by rfl) ⟨1474829, by rfl⟩ : syracuseStep 1966439 = 2949659) B2949659
theorem B1966811 : Blo 1309973 1966811 := bstep (se 1 (by rfl) ⟨1475108, by rfl⟩ : syracuseStep 1966811 = 2950217) B2950217
theorem B1311515 : Blo 1309973 1311515 := bstep (se 1 (by rfl) ⟨983636, by rfl⟩ : syracuseStep 1311515 = 1967273) B1967273
theorem B1311647 : Blo 1309973 1311647 := bstep (se 1 (by rfl) ⟨983735, by rfl⟩ : syracuseStep 1311647 = 1967471) B1967471
theorem B68084651 : Blo 1309973 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B2017125317 : Blo 1309973 2017125317 := bstep (se 4 (by rfl) ⟨189105498, by rfl⟩ : syracuseStep 2017125317 = 378210997) B378210997
theorem B9577511 : Blo 1309973 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B544810063 : Blo 1309973 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B40379471 : Blo 1309973 40379471 := bstep (se 1 (by rfl) ⟨30284603, by rfl⟩ : syracuseStep 40379471 = 60569207) B60569207
theorem B2950235 : Blo 1309973 2950235 := bstep (se 1 (by rfl) ⟨2212676, by rfl⟩ : syracuseStep 2950235 = 4425353) B4425353
theorem B1967195 : Blo 1309973 1967195 := bstep (se 1 (by rfl) ⟨1475396, by rfl⟩ : syracuseStep 1967195 = 2950793) B2950793
theorem B1967225 : Blo 1309973 1967225 := bstep (se 2 (by rfl) ⟨737709, by rfl⟩ : syracuseStep 1967225 = 1475419) B1475419
theorem B19154195 : Blo 1309973 19154195 := bstep (se 1 (by rfl) ⟨14365646, by rfl⟩ : syracuseStep 19154195 = 28731293) B28731293
theorem B11199869 : Blo 1309973 11199869 := bstep (se 3 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 11199869 = 4199951) B4199951
theorem B2950559 : Blo 1309973 2950559 := bstep (se 1 (by rfl) ⟨2212919, by rfl⟩ : syracuseStep 2950559 = 4425839) B4425839
theorem B1967591 : Blo 1309973 1967591 := bstep (se 1 (by rfl) ⟨1475693, by rfl⟩ : syracuseStep 1967591 = 2951387) B2951387
theorem B28362383 : Blo 1309973 28362383 := bstep (se 1 (by rfl) ⟨21271787, by rfl⟩ : syracuseStep 28362383 = 42543575) B42543575
theorem B1967771 : Blo 1309973 1967771 := bstep (se 1 (by rfl) ⟨1475828, by rfl⟩ : syracuseStep 1967771 = 2951657) B2951657
theorem B3147503 : Blo 1309973 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2213615 : Blo 1309973 2213615 := bstep (se 1 (by rfl) ⟨1660211, by rfl⟩ : syracuseStep 2213615 = 3320423) B3320423
theorem B2951351 : Blo 1309973 2951351 := bstep (se 1 (by rfl) ⟨2213513, by rfl⟩ : syracuseStep 2951351 = 4427027) B4427027
theorem B2878375 : Blo 1309973 2878375 := bstep (se 1 (by rfl) ⟨2158781, by rfl⟩ : syracuseStep 2878375 = 4317563) B4317563
theorem B4975607 : Blo 1309973 4975607 := bstep (se 1 (by rfl) ⟨3731705, by rfl⟩ : syracuseStep 4975607 = 7463411) B7463411
theorem B4197503 : Blo 1309973 4197503 := bstep (se 1 (by rfl) ⟨3148127, by rfl⟩ : syracuseStep 4197503 = 6296255) B6296255
theorem B43674785 : Blo 1309973 43674785 := bstep (se 2 (by rfl) ⟨16378044, by rfl⟩ : syracuseStep 43674785 = 32756089) B32756089
theorem B15133949 : Blo 1309973 15133949 := bstep (se 3 (by rfl) ⟨2837615, by rfl⟩ : syracuseStep 15133949 = 5675231) B5675231
theorem B3149455 : Blo 1309973 3149455 := bstep (se 1 (by rfl) ⟨2362091, by rfl⟩ : syracuseStep 3149455 = 4724183) B4724183
theorem B31879079 : Blo 1309973 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B31912157 : Blo 1309973 31912157 := bstep (se 3 (by rfl) ⟨5983529, by rfl⟩ : syracuseStep 31912157 = 11967059) B11967059
theorem B17940635 : Blo 1309973 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B7082423 : Blo 1309973 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B87413519 : Blo 1309973 87413519 := bstep (se 1 (by rfl) ⟨65560139, by rfl⟩ : syracuseStep 87413519 = 131120279) B131120279
theorem B7975705 : Blo 1309973 7975705 := bstep (se 2 (by rfl) ⟨2990889, by rfl⟩ : syracuseStep 7975705 = 5981779) B5981779
theorem B5600087 : Blo 1309973 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B17929129 : Blo 1309973 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B3151963 : Blo 1309973 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B4421735 : Blo 1309973 4421735 := bstep (se 1 (by rfl) ⟨3316301, by rfl⟩ : syracuseStep 4421735 = 6632603) B6632603
theorem B3315937 : Blo 1309973 3315937 := bstep (se 2 (by rfl) ⟨1243476, by rfl⟩ : syracuseStep 3315937 = 2486953) B2486953
theorem B2488639 : Blo 1309973 2488639 := bstep (se 1 (by rfl) ⟨1866479, by rfl⟩ : syracuseStep 2488639 = 3732959) B3732959
theorem B2488745 : Blo 1309973 2488745 := bstep (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) B1866559
theorem B3365327 : Blo 1309973 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2488799 : Blo 1309973 2488799 := bstep (se 1 (by rfl) ⟨1866599, by rfl⟩ : syracuseStep 2488799 = 3733199) B3733199
theorem B3734383 : Blo 1309973 3734383 := bstep (se 1 (by rfl) ⟨2800787, by rfl⟩ : syracuseStep 3734383 = 5601575) B5601575
theorem B1965167 : Blo 1309973 1965167 := bstep (se 1 (by rfl) ⟨1473875, by rfl⟩ : syracuseStep 1965167 = 2947751) B2947751
theorem B1965353 : Blo 1309973 1965353 := bstep (se 2 (by rfl) ⟨737007, by rfl⟩ : syracuseStep 1965353 = 1474015) B1474015
theorem B1965503 : Blo 1309973 1965503 := bstep (se 1 (by rfl) ⟨1474127, by rfl⟩ : syracuseStep 1965503 = 2948255) B2948255
theorem B3317375 : Blo 1309973 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B4423625 : Blo 1309973 4423625 := bstep (se 2 (by rfl) ⟨1658859, by rfl⟩ : syracuseStep 4423625 = 3317719) B3317719
theorem B1310715 : Blo 1309973 1310715 := bstep (se 1 (by rfl) ⟨983036, by rfl⟩ : syracuseStep 1310715 = 1966073) B1966073
theorem B7086055 : Blo 1309973 7086055 := bstep (se 1 (by rfl) ⟨5314541, by rfl⟩ : syracuseStep 7086055 = 10629083) B10629083
theorem B10092527 : Blo 1309973 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B1966175 : Blo 1309973 1966175 := bstep (se 1 (by rfl) ⟨1474631, by rfl⟩ : syracuseStep 1966175 = 2949263) B2949263
theorem B11960423 : Blo 1309973 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B4202617 : Blo 1309973 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B1966217 : Blo 1309973 1966217 := bstep (se 2 (by rfl) ⟨737331, by rfl⟩ : syracuseStep 1966217 = 1474663) B1474663
theorem B21274771 : Blo 1309973 21274771 := bstep (se 1 (by rfl) ⟨15956078, by rfl⟩ : syracuseStep 21274771 = 31912157) B31912157
theorem B1310879 : Blo 1309973 1310879 := bstep (se 1 (by rfl) ⟨983159, by rfl⟩ : syracuseStep 1310879 = 1966319) B1966319
theorem B1966247 : Blo 1309973 1966247 := bstep (se 1 (by rfl) ⟨1474685, by rfl⟩ : syracuseStep 1966247 = 2949371) B2949371
theorem B1310959 : Blo 1309973 1310959 := bstep (se 1 (by rfl) ⟨983219, by rfl⟩ : syracuseStep 1310959 = 1966439) B1966439
theorem B3318185 : Blo 1309973 3318185 := bstep (se 2 (by rfl) ⟨1244319, by rfl⟩ : syracuseStep 3318185 = 2488639) B2488639
theorem B1311207 : Blo 1309973 1311207 := bstep (se 1 (by rfl) ⟨983405, by rfl⟩ : syracuseStep 1311207 = 1966811) B1966811
theorem B1344750211 : Blo 1309973 1344750211 := bstep (se 1 (by rfl) ⟨1008562658, by rfl⟩ : syracuseStep 1344750211 = 2017125317) B2017125317
theorem B26919647 : Blo 1309973 26919647 := bstep (se 1 (by rfl) ⟨20189735, by rfl⟩ : syracuseStep 26919647 = 40379471) B40379471
theorem B1966823 : Blo 1309973 1966823 := bstep (se 1 (by rfl) ⟨1475117, by rfl⟩ : syracuseStep 1966823 = 2950235) B2950235
theorem B1311463 : Blo 1309973 1311463 := bstep (se 1 (by rfl) ⟨983597, by rfl⟩ : syracuseStep 1311463 = 1967195) B1967195
theorem B1311483 : Blo 1309973 1311483 := bstep (se 1 (by rfl) ⟨983612, by rfl⟩ : syracuseStep 1311483 = 1967225) B1967225
theorem B1967039 : Blo 1309973 1967039 := bstep (se 1 (by rfl) ⟨1475279, by rfl⟩ : syracuseStep 1967039 = 2950559) B2950559
theorem B1311727 : Blo 1309973 1311727 := bstep (se 1 (by rfl) ⟨983795, by rfl⟩ : syracuseStep 1311727 = 1967591) B1967591
theorem B10634273 : Blo 1309973 10634273 := bstep (se 2 (by rfl) ⟨3987852, by rfl⟩ : syracuseStep 10634273 = 7975705) B7975705
theorem B18908255 : Blo 1309973 18908255 := bstep (se 1 (by rfl) ⟨14181191, by rfl⟩ : syracuseStep 18908255 = 28362383) B28362383
theorem B1311847 : Blo 1309973 1311847 := bstep (se 1 (by rfl) ⟨983885, by rfl⟩ : syracuseStep 1311847 = 1967771) B1967771
theorem B6636653 : Blo 1309973 6636653 := bstep (se 3 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 6636653 = 2488745) B2488745
theorem B1475743 : Blo 1309973 1475743 := bstep (se 1 (by rfl) ⟨1106807, by rfl⟩ : syracuseStep 1475743 = 2213615) B2213615
theorem B23905505 : Blo 1309973 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B1967567 : Blo 1309973 1967567 := bstep (se 1 (by rfl) ⟨1475675, by rfl⟩ : syracuseStep 1967567 = 2951351) B2951351
theorem B29116523 : Blo 1309973 29116523 := bstep (se 1 (by rfl) ⟨21837392, by rfl⟩ : syracuseStep 29116523 = 43674785) B43674785
theorem B21252719 : Blo 1309973 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B9448073 : Blo 1309973 9448073 := bstep (se 2 (by rfl) ⟨3543027, by rfl⟩ : syracuseStep 9448073 = 7086055) B7086055
theorem B6728351 : Blo 1309973 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B4721615 : Blo 1309973 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B6385007 : Blo 1309973 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B7466579 : Blo 1309973 7466579 := bstep (se 1 (by rfl) ⟨5599934, by rfl⟩ : syracuseStep 7466579 = 11199869) B11199869
theorem B3837833 : Blo 1309973 3837833 := bstep (se 2 (by rfl) ⟨1439187, by rfl⟩ : syracuseStep 3837833 = 2878375) B2878375
theorem B726413417 : Blo 1309973 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B1659199 : Blo 1309973 1659199 := bstep (se 1 (by rfl) ⟨1244399, by rfl⟩ : syracuseStep 1659199 = 2488799) B2488799
theorem B8393341 : Blo 1309973 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B2798335 : Blo 1309973 2798335 := bstep (se 1 (by rfl) ⟨2098751, by rfl⟩ : syracuseStep 2798335 = 4197503) B4197503
theorem B10089299 : Blo 1309973 10089299 := bstep (se 1 (by rfl) ⟨7566974, by rfl⟩ : syracuseStep 10089299 = 15133949) B15133949
theorem B4199273 : Blo 1309973 4199273 := bstep (se 2 (by rfl) ⟨1574727, by rfl⟩ : syracuseStep 4199273 = 3149455) B3149455
theorem B4421249 : Blo 1309973 4421249 := bstep (se 2 (by rfl) ⟨1657968, by rfl⟩ : syracuseStep 4421249 = 3315937) B3315937
theorem B3733391 : Blo 1309973 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B12769463 : Blo 1309973 12769463 := bstep (se 1 (by rfl) ⟨9577097, by rfl⟩ : syracuseStep 12769463 = 19154195) B19154195
theorem B4979177 : Blo 1309973 4979177 := bstep (se 2 (by rfl) ⟨1867191, by rfl⟩ : syracuseStep 4979177 = 3734383) B3734383
theorem B2947823 : Blo 1309973 2947823 := bstep (se 1 (by rfl) ⟨2210867, by rfl⟩ : syracuseStep 2947823 = 4421735) B4421735
theorem B2243551 : Blo 1309973 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B3317071 : Blo 1309973 3317071 := bstep (se 1 (by rfl) ⟨2487803, by rfl⟩ : syracuseStep 3317071 = 4975607) B4975607
theorem B233102717 : Blo 1309973 233102717 := bstep (se 3 (by rfl) ⟨43706759, by rfl⟩ : syracuseStep 233102717 = 87413519) B87413519
theorem B1310111 : Blo 1309973 1310111 := bstep (se 1 (by rfl) ⟨982583, by rfl⟩ : syracuseStep 1310111 = 1965167) B1965167
theorem B1310235 : Blo 1309973 1310235 := bstep (se 1 (by rfl) ⟨982676, by rfl⟩ : syracuseStep 1310235 = 1965353) B1965353
theorem B1310335 : Blo 1309973 1310335 := bstep (se 1 (by rfl) ⟨982751, by rfl⟩ : syracuseStep 1310335 = 1965503) B1965503
theorem B2211583 : Blo 1309973 2211583 := bstep (se 1 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 2211583 = 3317375) B3317375
theorem B181559069 : Blo 1309973 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B2949083 : Blo 1309973 2949083 := bstep (se 1 (by rfl) ⟨2211812, by rfl⟩ : syracuseStep 2949083 = 4423625) B4423625
theorem B1310783 : Blo 1309973 1310783 := bstep (se 1 (by rfl) ⟨983087, by rfl⟩ : syracuseStep 1310783 = 1966175) B1966175
theorem B1310811 : Blo 1309973 1310811 := bstep (se 1 (by rfl) ⟨983108, by rfl⟩ : syracuseStep 1310811 = 1966217) B1966217
theorem B1310831 : Blo 1309973 1310831 := bstep (se 1 (by rfl) ⟨983123, by rfl⟩ : syracuseStep 1310831 = 1966247) B1966247
theorem B5603489 : Blo 1309973 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B2212123 : Blo 1309973 2212123 := bstep (se 1 (by rfl) ⟨1659092, by rfl⟩ : syracuseStep 2212123 = 3318185) B3318185
theorem B2212265 : Blo 1309973 2212265 := bstep (se 2 (by rfl) ⟨829599, by rfl⟩ : syracuseStep 2212265 = 1659199) B1659199
theorem B1311215 : Blo 1309973 1311215 := bstep (se 1 (by rfl) ⟨983411, by rfl⟩ : syracuseStep 1311215 = 1966823) B1966823
theorem B6726199 : Blo 1309973 6726199 := bstep (se 1 (by rfl) ⟨5044649, by rfl⟩ : syracuseStep 6726199 = 10089299) B10089299
theorem B1311359 : Blo 1309973 1311359 := bstep (se 1 (by rfl) ⟨983519, by rfl⟩ : syracuseStep 1311359 = 1967039) B1967039
theorem B4424435 : Blo 1309973 4424435 := bstep (se 1 (by rfl) ⟨3318326, by rfl⟩ : syracuseStep 4424435 = 6636653) B6636653
theorem B11191121 : Blo 1309973 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B1793000281 : Blo 1309973 1793000281 := bstep (se 2 (by rfl) ⟨672375105, by rfl⟩ : syracuseStep 1793000281 = 1344750211) B1344750211
theorem B1311711 : Blo 1309973 1311711 := bstep (se 1 (by rfl) ⟨983783, by rfl⟩ : syracuseStep 1311711 = 1967567) B1967567
theorem B2991401 : Blo 1309973 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B8512975 : Blo 1309973 8512975 := bstep (se 1 (by rfl) ⟨6384731, by rfl⟩ : syracuseStep 8512975 = 12769463) B12769463
theorem B1967657 : Blo 1309973 1967657 := bstep (se 2 (by rfl) ⟨737871, by rfl⟩ : syracuseStep 1967657 = 1475743) B1475743
theorem B3319451 : Blo 1309973 3319451 := bstep (se 1 (by rfl) ⟨2489588, by rfl⟩ : syracuseStep 3319451 = 4979177) B4979177
theorem B17942269 : Blo 1309973 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B3147743 : Blo 1309973 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B9955709 : Blo 1309973 9955709 := bstep (se 3 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 9955709 = 3733391) B3733391
theorem B121039379 : Blo 1309973 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B2558555 : Blo 1309973 2558555 := bstep (se 1 (by rfl) ⟨1918916, by rfl⟩ : syracuseStep 2558555 = 3837833) B3837833
theorem B7973615 : Blo 1309973 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B7089515 : Blo 1309973 7089515 := bstep (se 1 (by rfl) ⟨5317136, by rfl⟩ : syracuseStep 7089515 = 10634273) B10634273
theorem B15937003 : Blo 1309973 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B17026685 : Blo 1309973 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B3731113 : Blo 1309973 3731113 := bstep (se 2 (by rfl) ⟨1399167, by rfl⟩ : syracuseStep 3731113 = 2798335) B2798335
theorem B19411015 : Blo 1309973 19411015 := bstep (se 1 (by rfl) ⟨14558261, by rfl⟩ : syracuseStep 19411015 = 29116523) B29116523
theorem B14168479 : Blo 1309973 14168479 := bstep (se 1 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 14168479 = 21252719) B21252719
theorem B4977719 : Blo 1309973 4977719 := bstep (se 1 (by rfl) ⟨3733289, by rfl⟩ : syracuseStep 4977719 = 7466579) B7466579
theorem B484275611 : Blo 1309973 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B28366361 : Blo 1309973 28366361 := bstep (se 2 (by rfl) ⟨10637385, by rfl⟩ : syracuseStep 28366361 = 21274771) B21274771
theorem B17946431 : Blo 1309973 17946431 := bstep (se 1 (by rfl) ⟨13459823, by rfl⟩ : syracuseStep 17946431 = 26919647) B26919647
theorem B2799515 : Blo 1309973 2799515 := bstep (se 1 (by rfl) ⟨2099636, by rfl⟩ : syracuseStep 2799515 = 4199273) B4199273
theorem B12605503 : Blo 1309973 12605503 := bstep (se 1 (by rfl) ⟨9454127, by rfl⟩ : syracuseStep 12605503 = 18908255) B18908255
theorem B2947499 : Blo 1309973 2947499 := bstep (se 1 (by rfl) ⟨2210624, by rfl⟩ : syracuseStep 2947499 = 4421249) B4421249
theorem B6298715 : Blo 1309973 6298715 := bstep (se 1 (by rfl) ⟨4724036, by rfl⟩ : syracuseStep 6298715 = 9448073) B9448073
theorem B4422761 : Blo 1309973 4422761 := bstep (se 2 (by rfl) ⟨1658535, by rfl⟩ : syracuseStep 4422761 = 3317071) B3317071
theorem B1965215 : Blo 1309973 1965215 := bstep (se 1 (by rfl) ⟨1473911, by rfl⟩ : syracuseStep 1965215 = 2947823) B2947823
theorem B155401811 : Blo 1309973 155401811 := bstep (se 1 (by rfl) ⟨116551358, by rfl⟩ : syracuseStep 155401811 = 233102717) B233102717
theorem B2948777 : Blo 1309973 2948777 := bstep (se 2 (by rfl) ⟨1105791, by rfl⟩ : syracuseStep 2948777 = 2211583) B2211583
theorem B1966055 : Blo 1309973 1966055 := bstep (se 1 (by rfl) ⟨1474541, by rfl⟩ : syracuseStep 1966055 = 2949083) B2949083
theorem B3735659 : Blo 1309973 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B1474843 : Blo 1309973 1474843 := bstep (se 1 (by rfl) ⟨1106132, by rfl⟩ : syracuseStep 1474843 = 2212265) B2212265
theorem B2949497 : Blo 1309973 2949497 := bstep (se 2 (by rfl) ⟨1106061, by rfl⟩ : syracuseStep 2949497 = 2212123) B2212123
theorem B2949623 : Blo 1309973 2949623 := bstep (se 1 (by rfl) ⟨2212217, by rfl⟩ : syracuseStep 2949623 = 4424435) B4424435
theorem B18891305 : Blo 1309973 18891305 := bstep (se 2 (by rfl) ⟨7084239, by rfl⟩ : syracuseStep 18891305 = 14168479) B14168479
theorem B3318479 : Blo 1309973 3318479 := bstep (se 1 (by rfl) ⟨2488859, by rfl⟩ : syracuseStep 3318479 = 4977719) B4977719
theorem B1311771 : Blo 1309973 1311771 := bstep (se 1 (by rfl) ⟨983828, by rfl⟩ : syracuseStep 1311771 = 1967657) B1967657
theorem B2212967 : Blo 1309973 2212967 := bstep (se 1 (by rfl) ⟨1659725, by rfl⟩ : syracuseStep 2212967 = 3319451) B3319451
theorem B2098495 : Blo 1309973 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B6637139 : Blo 1309973 6637139 := bstep (se 1 (by rfl) ⟨4977854, by rfl⟩ : syracuseStep 6637139 = 9955709) B9955709
theorem B80692919 : Blo 1309973 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B1705703 : Blo 1309973 1705703 := bstep (se 1 (by rfl) ⟨1279277, by rfl⟩ : syracuseStep 1705703 = 2558555) B2558555
theorem B4974817 : Blo 1309973 4974817 := bstep (se 2 (by rfl) ⟨1865556, by rfl⟩ : syracuseStep 4974817 = 3731113) B3731113
theorem B23923025 : Blo 1309973 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B25881353 : Blo 1309973 25881353 := bstep (se 2 (by rfl) ⟨9705507, by rfl⟩ : syracuseStep 25881353 = 19411015) B19411015
theorem B1994267 : Blo 1309973 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B18910907 : Blo 1309973 18910907 := bstep (se 1 (by rfl) ⟨14183180, by rfl⟩ : syracuseStep 18910907 = 28366361) B28366361
theorem B2390667041 : Blo 1309973 2390667041 := bstep (se 2 (by rfl) ⟨896500140, by rfl⟩ : syracuseStep 2390667041 = 1793000281) B1793000281
theorem B11964287 : Blo 1309973 11964287 := bstep (se 1 (by rfl) ⟨8973215, by rfl⟩ : syracuseStep 11964287 = 17946431) B17946431
theorem B11350633 : Blo 1309973 11350633 := bstep (se 2 (by rfl) ⟨4256487, by rfl⟩ : syracuseStep 11350633 = 8512975) B8512975
theorem B4199143 : Blo 1309973 4199143 := bstep (se 1 (by rfl) ⟨3149357, by rfl⟩ : syracuseStep 4199143 = 6298715) B6298715
theorem B103601207 : Blo 1309973 103601207 := bstep (se 1 (by rfl) ⟨77700905, by rfl⟩ : syracuseStep 103601207 = 155401811) B155401811
theorem B11351123 : Blo 1309973 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B16807337 : Blo 1309973 16807337 := bstep (se 2 (by rfl) ⟨6302751, by rfl⟩ : syracuseStep 16807337 = 12605503) B12605503
theorem B7460747 : Blo 1309973 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B8968265 : Blo 1309973 8968265 := bstep (se 2 (by rfl) ⟨3363099, by rfl⟩ : syracuseStep 8968265 = 6726199) B6726199
theorem B1291401629 : Blo 1309973 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B1866343 : Blo 1309973 1866343 := bstep (se 1 (by rfl) ⟨1399757, by rfl⟩ : syracuseStep 1866343 = 2799515) B2799515
theorem B1964999 : Blo 1309973 1964999 := bstep (se 1 (by rfl) ⟨1473749, by rfl⟩ : syracuseStep 1964999 = 2947499) B2947499
theorem B5315743 : Blo 1309973 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B21249337 : Blo 1309973 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B2948507 : Blo 1309973 2948507 := bstep (se 1 (by rfl) ⟨2211380, by rfl⟩ : syracuseStep 2948507 = 4422761) B4422761
theorem B1310143 : Blo 1309973 1310143 := bstep (se 1 (by rfl) ⟨982607, by rfl⟩ : syracuseStep 1310143 = 1965215) B1965215
theorem B4726343 : Blo 1309973 4726343 := bstep (se 1 (by rfl) ⟨3544757, by rfl⟩ : syracuseStep 4726343 = 7089515) B7089515
theorem B1965851 : Blo 1309973 1965851 := bstep (se 1 (by rfl) ⟨1474388, by rfl⟩ : syracuseStep 1965851 = 2948777) B2948777
theorem B1310703 : Blo 1309973 1310703 := bstep (se 1 (by rfl) ⟨983027, by rfl⟩ : syracuseStep 1310703 = 1966055) B1966055
theorem B2490439 : Blo 1309973 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B1966331 : Blo 1309973 1966331 := bstep (se 1 (by rfl) ⟨1474748, by rfl⟩ : syracuseStep 1966331 = 2949497) B2949497
theorem B1966415 : Blo 1309973 1966415 := bstep (se 1 (by rfl) ⟨1474811, by rfl⟩ : syracuseStep 1966415 = 2949623) B2949623
theorem B1966457 : Blo 1309973 1966457 := bstep (se 2 (by rfl) ⟨737421, by rfl⟩ : syracuseStep 1966457 = 1474843) B1474843
theorem B2212319 : Blo 1309973 2212319 := bstep (se 1 (by rfl) ⟨1659239, by rfl⟩ : syracuseStep 2212319 = 3318479) B3318479
theorem B1475311 : Blo 1309973 1475311 := bstep (se 1 (by rfl) ⟨1106483, by rfl⟩ : syracuseStep 1475311 = 2212967) B2212967
theorem B4424759 : Blo 1309973 4424759 := bstep (se 1 (by rfl) ⟨3318569, by rfl⟩ : syracuseStep 4424759 = 6637139) B6637139
theorem B4973831 : Blo 1309973 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B5318045 : Blo 1309973 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B7087657 : Blo 1309973 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B17254235 : Blo 1309973 17254235 := bstep (se 1 (by rfl) ⟨12940676, by rfl⟩ : syracuseStep 17254235 = 25881353) B25881353
theorem B276269885 : Blo 1309973 276269885 := bstep (se 3 (by rfl) ⟨51800603, by rfl⟩ : syracuseStep 276269885 = 103601207) B103601207
theorem B12594203 : Blo 1309973 12594203 := bstep (se 1 (by rfl) ⟨9445652, by rfl⟩ : syracuseStep 12594203 = 18891305) B18891305
theorem B15134177 : Blo 1309973 15134177 := bstep (se 2 (by rfl) ⟨5675316, by rfl⟩ : syracuseStep 15134177 = 11350633) B11350633
theorem B5598857 : Blo 1309973 5598857 := bstep (se 2 (by rfl) ⟨2099571, by rfl⟩ : syracuseStep 5598857 = 4199143) B4199143
theorem B860934419 : Blo 1309973 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B28332449 : Blo 1309973 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B2797993 : Blo 1309973 2797993 := bstep (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) B2098495
theorem B3150895 : Blo 1309973 3150895 := bstep (se 1 (by rfl) ⟨2363171, by rfl⟩ : syracuseStep 3150895 = 4726343) B4726343
theorem B7976191 : Blo 1309973 7976191 := bstep (se 1 (by rfl) ⟨5982143, by rfl⟩ : syracuseStep 7976191 = 11964287) B11964287
theorem B6633089 : Blo 1309973 6633089 := bstep (se 2 (by rfl) ⟨2487408, by rfl⟩ : syracuseStep 6633089 = 4974817) B4974817
theorem B7567415 : Blo 1309973 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B2488457 : Blo 1309973 2488457 := bstep (se 2 (by rfl) ⟨933171, by rfl⟩ : syracuseStep 2488457 = 1866343) B1866343
theorem B11204891 : Blo 1309973 11204891 := bstep (se 1 (by rfl) ⟨8403668, by rfl⟩ : syracuseStep 11204891 = 16807337) B16807337
theorem B53795279 : Blo 1309973 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B5978843 : Blo 1309973 5978843 := bstep (se 1 (by rfl) ⟨4484132, by rfl⟩ : syracuseStep 5978843 = 8968265) B8968265
theorem B15948683 : Blo 1309973 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B1309999 : Blo 1309973 1309999 := bstep (se 1 (by rfl) ⟨982499, by rfl⟩ : syracuseStep 1309999 = 1964999) B1964999
theorem B1965671 : Blo 1309973 1965671 := bstep (se 1 (by rfl) ⟨1474253, by rfl⟩ : syracuseStep 1965671 = 2948507) B2948507
theorem B18194165 : Blo 1309973 18194165 := bstep (se 5 (by rfl) ⟨852851, by rfl⟩ : syracuseStep 18194165 = 1705703) B1705703
theorem B12607271 : Blo 1309973 12607271 := bstep (se 1 (by rfl) ⟨9455453, by rfl⟩ : syracuseStep 12607271 = 18910907) B18910907
theorem B1310567 : Blo 1309973 1310567 := bstep (se 1 (by rfl) ⟨982925, by rfl⟩ : syracuseStep 1310567 = 1965851) B1965851
theorem B1593778027 : Blo 1309973 1593778027 := bstep (se 1 (by rfl) ⟨1195333520, by rfl⟩ : syracuseStep 1593778027 = 2390667041) B2390667041
theorem B1310887 : Blo 1309973 1310887 := bstep (se 1 (by rfl) ⟨983165, by rfl⟩ : syracuseStep 1310887 = 1966331) B1966331
theorem B573956279 : Blo 1309973 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B1310943 : Blo 1309973 1310943 := bstep (se 1 (by rfl) ⟨983207, by rfl⟩ : syracuseStep 1310943 = 1966415) B1966415
theorem B1310971 : Blo 1309973 1310971 := bstep (se 1 (by rfl) ⟨983228, by rfl⟩ : syracuseStep 1310971 = 1966457) B1966457
theorem B1474879 : Blo 1309973 1474879 := bstep (se 1 (by rfl) ⟨1106159, by rfl⟩ : syracuseStep 1474879 = 2212319) B2212319
theorem B2949839 : Blo 1309973 2949839 := bstep (se 1 (by rfl) ⟨2212379, by rfl⟩ : syracuseStep 2949839 = 4424759) B4424759
theorem B1967081 : Blo 1309973 1967081 := bstep (se 2 (by rfl) ⟨737655, by rfl⟩ : syracuseStep 1967081 = 1475311) B1475311
theorem B11502823 : Blo 1309973 11502823 := bstep (se 1 (by rfl) ⟨8627117, by rfl⟩ : syracuseStep 11502823 = 17254235) B17254235
theorem B10634921 : Blo 1309973 10634921 := bstep (se 2 (by rfl) ⟨3988095, by rfl⟩ : syracuseStep 10634921 = 7976191) B7976191
theorem B3320585 : Blo 1309973 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B1658971 : Blo 1309973 1658971 := bstep (se 1 (by rfl) ⟨1244228, by rfl⟩ : syracuseStep 1658971 = 2488457) B2488457
theorem B3985895 : Blo 1309973 3985895 := bstep (se 1 (by rfl) ⟨2989421, by rfl⟩ : syracuseStep 3985895 = 5978843) B5978843
theorem B9450209 : Blo 1309973 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B14922629 : Blo 1309973 14922629 := bstep (se 4 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 14922629 = 2797993) B2797993
theorem B10089451 : Blo 1309973 10089451 := bstep (se 1 (by rfl) ⟨7567088, by rfl⟩ : syracuseStep 10089451 = 15134177) B15134177
theorem B3732571 : Blo 1309973 3732571 := bstep (se 1 (by rfl) ⟨2799428, by rfl⟩ : syracuseStep 3732571 = 5598857) B5598857
theorem B12129443 : Blo 1309973 12129443 := bstep (se 1 (by rfl) ⟨9097082, by rfl⟩ : syracuseStep 12129443 = 18194165) B18194165
theorem B18888299 : Blo 1309973 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B3315887 : Blo 1309973 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B3545363 : Blo 1309973 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B4422059 : Blo 1309973 4422059 := bstep (se 1 (by rfl) ⟨3316544, by rfl⟩ : syracuseStep 4422059 = 6633089) B6633089
theorem B5044943 : Blo 1309973 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B4201193 : Blo 1309973 4201193 := bstep (se 2 (by rfl) ⟨1575447, by rfl⟩ : syracuseStep 4201193 = 3150895) B3150895
theorem B7469927 : Blo 1309973 7469927 := bstep (se 1 (by rfl) ⟨5602445, by rfl⟩ : syracuseStep 7469927 = 11204891) B11204891
theorem B35863519 : Blo 1309973 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B184179923 : Blo 1309973 184179923 := bstep (se 1 (by rfl) ⟨138134942, by rfl⟩ : syracuseStep 184179923 = 276269885) B276269885
theorem B10632455 : Blo 1309973 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B8396135 : Blo 1309973 8396135 := bstep (se 1 (by rfl) ⟨6297101, by rfl⟩ : syracuseStep 8396135 = 12594203) B12594203
theorem B1310447 : Blo 1309973 1310447 := bstep (se 1 (by rfl) ⟨982835, by rfl⟩ : syracuseStep 1310447 = 1965671) B1965671
theorem B2125037369 : Blo 1309973 2125037369 := bstep (se 2 (by rfl) ⟨796889013, by rfl⟩ : syracuseStep 2125037369 = 1593778027) B1593778027
theorem B8404847 : Blo 1309973 8404847 := bstep (se 1 (by rfl) ⟨6303635, by rfl⟩ : syracuseStep 8404847 = 12607271) B12607271
theorem B2211961 : Blo 1309973 2211961 := bstep (se 2 (by rfl) ⟨829485, by rfl⟩ : syracuseStep 2211961 = 1658971) B1658971
theorem B1966505 : Blo 1309973 1966505 := bstep (se 2 (by rfl) ⟨737439, by rfl⟩ : syracuseStep 1966505 = 1474879) B1474879
theorem B1966559 : Blo 1309973 1966559 := bstep (se 1 (by rfl) ⟨1474919, by rfl⟩ : syracuseStep 1966559 = 2949839) B2949839
theorem B6300139 : Blo 1309973 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B1311387 : Blo 1309973 1311387 := bstep (se 1 (by rfl) ⟨983540, by rfl⟩ : syracuseStep 1311387 = 1967081) B1967081
theorem B8086295 : Blo 1309973 8086295 := bstep (se 1 (by rfl) ⟨6064721, by rfl⟩ : syracuseStep 8086295 = 12129443) B12129443
theorem B12592199 : Blo 1309973 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B47818025 : Blo 1309973 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B15337097 : Blo 1309973 15337097 := bstep (se 2 (by rfl) ⟨5751411, by rfl⟩ : syracuseStep 15337097 = 11502823) B11502823
theorem B2213723 : Blo 1309973 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B7088303 : Blo 1309973 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B5597423 : Blo 1309973 5597423 := bstep (se 1 (by rfl) ⟨4198067, by rfl⟩ : syracuseStep 5597423 = 8396135) B8396135
theorem B5603231 : Blo 1309973 5603231 := bstep (se 1 (by rfl) ⟨4202423, by rfl⟩ : syracuseStep 5603231 = 8404847) B8404847
theorem B9948419 : Blo 1309973 9948419 := bstep (se 1 (by rfl) ⟨7461314, by rfl⟩ : syracuseStep 9948419 = 14922629) B14922629
theorem B7089947 : Blo 1309973 7089947 := bstep (se 1 (by rfl) ⟨5317460, by rfl⟩ : syracuseStep 7089947 = 10634921) B10634921
theorem B10629053 : Blo 1309973 10629053 := bstep (se 3 (by rfl) ⟨1992947, by rfl⟩ : syracuseStep 10629053 = 3985895) B3985895
theorem B4976761 : Blo 1309973 4976761 := bstep (se 2 (by rfl) ⟨1866285, by rfl⟩ : syracuseStep 4976761 = 3732571) B3732571
theorem B2363575 : Blo 1309973 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B3363295 : Blo 1309973 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B11203181 : Blo 1309973 11203181 := bstep (se 3 (by rfl) ⟨2100596, by rfl⟩ : syracuseStep 11203181 = 4201193) B4201193
theorem B122786615 : Blo 1309973 122786615 := bstep (se 1 (by rfl) ⟨92089961, by rfl⟩ : syracuseStep 122786615 = 184179923) B184179923
theorem B53810405 : Blo 1309973 53810405 := bstep (se 4 (by rfl) ⟨5044725, by rfl⟩ : syracuseStep 53810405 = 10089451) B10089451
theorem B382637519 : Blo 1309973 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B2210591 : Blo 1309973 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B2948039 : Blo 1309973 2948039 := bstep (se 1 (by rfl) ⟨2211029, by rfl⟩ : syracuseStep 2948039 = 4422059) B4422059
theorem B4979951 : Blo 1309973 4979951 := bstep (se 1 (by rfl) ⟨3734963, by rfl⟩ : syracuseStep 4979951 = 7469927) B7469927
theorem B1416691579 : Blo 1309973 1416691579 := bstep (se 1 (by rfl) ⟨1062518684, by rfl⟩ : syracuseStep 1416691579 = 2125037369) B2125037369
theorem B6635681 : Blo 1309973 6635681 := bstep (se 2 (by rfl) ⟨2488380, by rfl⟩ : syracuseStep 6635681 = 4976761) B4976761
theorem B2949281 : Blo 1309973 2949281 := bstep (se 2 (by rfl) ⟨1105980, by rfl⟩ : syracuseStep 2949281 = 2211961) B2211961
theorem B33579197 : Blo 1309973 33579197 := bstep (se 3 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 33579197 = 12592199) B12592199
theorem B1311003 : Blo 1309973 1311003 := bstep (se 1 (by rfl) ⟨983252, by rfl⟩ : syracuseStep 1311003 = 1966505) B1966505
theorem B1311039 : Blo 1309973 1311039 := bstep (se 1 (by rfl) ⟨983279, by rfl⟩ : syracuseStep 1311039 = 1966559) B1966559
theorem B35873603 : Blo 1309973 35873603 := bstep (se 1 (by rfl) ⟨26905202, by rfl⟩ : syracuseStep 35873603 = 53810405) B53810405
theorem B255091679 : Blo 1309973 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B10224731 : Blo 1309973 10224731 := bstep (se 1 (by rfl) ⟨7668548, by rfl⟩ : syracuseStep 10224731 = 15337097) B15337097
theorem B1475815 : Blo 1309973 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B21563453 : Blo 1309973 21563453 := bstep (se 3 (by rfl) ⟨4043147, by rfl⟩ : syracuseStep 21563453 = 8086295) B8086295
theorem B3319967 : Blo 1309973 3319967 := bstep (se 1 (by rfl) ⟨2489975, by rfl⟩ : syracuseStep 3319967 = 4979951) B4979951
theorem B1888922105 : Blo 1309973 1888922105 := bstep (se 2 (by rfl) ⟨708345789, by rfl⟩ : syracuseStep 1888922105 = 1416691579) B1416691579
theorem B4484393 : Blo 1309973 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B8400185 : Blo 1309973 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B31878683 : Blo 1309973 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B3731615 : Blo 1309973 3731615 := bstep (se 1 (by rfl) ⟨2798711, by rfl⟩ : syracuseStep 3731615 = 5597423) B5597423
theorem B327430973 : Blo 1309973 327430973 := bstep (se 3 (by rfl) ⟨61393307, by rfl⟩ : syracuseStep 327430973 = 122786615) B122786615
theorem B6632279 : Blo 1309973 6632279 := bstep (se 1 (by rfl) ⟨4974209, by rfl⟩ : syracuseStep 6632279 = 9948419) B9948419
theorem B3151433 : Blo 1309973 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B7468787 : Blo 1309973 7468787 := bstep (se 1 (by rfl) ⟨5601590, by rfl⟩ : syracuseStep 7468787 = 11203181) B11203181
theorem B4725535 : Blo 1309973 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B1473727 : Blo 1309973 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B1965359 : Blo 1309973 1965359 := bstep (se 1 (by rfl) ⟨1474019, by rfl⟩ : syracuseStep 1965359 = 2948039) B2948039
theorem B4726631 : Blo 1309973 4726631 := bstep (se 1 (by rfl) ⟨3544973, by rfl⟩ : syracuseStep 4726631 = 7089947) B7089947
theorem B3735487 : Blo 1309973 3735487 := bstep (se 1 (by rfl) ⟨2801615, by rfl⟩ : syracuseStep 3735487 = 5603231) B5603231
theorem B7086035 : Blo 1309973 7086035 := bstep (se 1 (by rfl) ⟨5314526, by rfl⟩ : syracuseStep 7086035 = 10629053) B10629053
theorem B4423787 : Blo 1309973 4423787 := bstep (se 1 (by rfl) ⟨3317840, by rfl⟩ : syracuseStep 4423787 = 6635681) B6635681
theorem B1966187 : Blo 1309973 1966187 := bstep (se 1 (by rfl) ⟨1474640, by rfl⟩ : syracuseStep 1966187 = 2949281) B2949281
theorem B6816487 : Blo 1309973 6816487 := bstep (se 1 (by rfl) ⟨5112365, by rfl⟩ : syracuseStep 6816487 = 10224731) B10224731
theorem B6300713 : Blo 1309973 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B2213311 : Blo 1309973 2213311 := bstep (se 1 (by rfl) ⟨1659983, by rfl⟩ : syracuseStep 2213311 = 3319967) B3319967
theorem B1967753 : Blo 1309973 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B21252455 : Blo 1309973 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B57502541 : Blo 1309973 57502541 := bstep (se 3 (by rfl) ⟨10781726, by rfl⟩ : syracuseStep 57502541 = 21563453) B21563453
theorem B218287315 : Blo 1309973 218287315 := bstep (se 1 (by rfl) ⟨163715486, by rfl⟩ : syracuseStep 218287315 = 327430973) B327430973
theorem B23915735 : Blo 1309973 23915735 := bstep (se 1 (by rfl) ⟨17936801, by rfl⟩ : syracuseStep 23915735 = 35873603) B35873603
theorem B170061119 : Blo 1309973 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B5600123 : Blo 1309973 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B12604349 : Blo 1309973 12604349 := bstep (se 3 (by rfl) ⟨2363315, by rfl⟩ : syracuseStep 12604349 = 4726631) B4726631
theorem B4724023 : Blo 1309973 4724023 := bstep (se 1 (by rfl) ⟨3543017, by rfl⟩ : syracuseStep 4724023 = 7086035) B7086035
theorem B2487743 : Blo 1309973 2487743 := bstep (se 1 (by rfl) ⟨1865807, by rfl⟩ : syracuseStep 2487743 = 3731615) B3731615
theorem B22386131 : Blo 1309973 22386131 := bstep (se 1 (by rfl) ⟨16789598, by rfl⟩ : syracuseStep 22386131 = 33579197) B33579197
theorem B4421519 : Blo 1309973 4421519 := bstep (se 1 (by rfl) ⟨3316139, by rfl⟩ : syracuseStep 4421519 = 6632279) B6632279
theorem B4979191 : Blo 1309973 4979191 := bstep (se 1 (by rfl) ⟨3734393, by rfl⟩ : syracuseStep 4979191 = 7468787) B7468787
theorem B8403821 : Blo 1309973 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B1964969 : Blo 1309973 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B1259281403 : Blo 1309973 1259281403 := bstep (se 1 (by rfl) ⟨944461052, by rfl⟩ : syracuseStep 1259281403 = 1888922105) B1888922105
theorem B1310239 : Blo 1309973 1310239 := bstep (se 1 (by rfl) ⟨982679, by rfl⟩ : syracuseStep 1310239 = 1965359) B1965359
theorem B2989595 : Blo 1309973 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B4980649 : Blo 1309973 4980649 := bstep (se 2 (by rfl) ⟨1867743, by rfl⟩ : syracuseStep 4980649 = 3735487) B3735487
theorem B2949191 : Blo 1309973 2949191 := bstep (se 1 (by rfl) ⟨2211893, by rfl⟩ : syracuseStep 2949191 = 4423787) B4423787
theorem B1310791 : Blo 1309973 1310791 := bstep (se 1 (by rfl) ⟨983093, by rfl⟩ : syracuseStep 1310791 = 1966187) B1966187
theorem B16801901 : Blo 1309973 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B1311835 : Blo 1309973 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B1164199013 : Blo 1309973 1164199013 := bstep (se 4 (by rfl) ⟨109143657, by rfl⟩ : syracuseStep 1164199013 = 218287315) B218287315
theorem B7972253 : Blo 1309973 7972253 := bstep (se 3 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 7972253 = 2989595) B2989595
theorem B2951081 : Blo 1309973 2951081 := bstep (se 2 (by rfl) ⟨1106655, by rfl⟩ : syracuseStep 2951081 = 2213311) B2213311
theorem B15943823 : Blo 1309973 15943823 := bstep (se 1 (by rfl) ⟨11957867, by rfl⟩ : syracuseStep 15943823 = 23915735) B23915735
theorem B6638921 : Blo 1309973 6638921 := bstep (se 2 (by rfl) ⟨2489595, by rfl⟩ : syracuseStep 6638921 = 4979191) B4979191
theorem B1658495 : Blo 1309973 1658495 := bstep (se 1 (by rfl) ⟨1243871, by rfl⟩ : syracuseStep 1658495 = 2487743) B2487743
theorem B9088649 : Blo 1309973 9088649 := bstep (se 2 (by rfl) ⟨3408243, by rfl⟩ : syracuseStep 9088649 = 6816487) B6816487
theorem B14168303 : Blo 1309973 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B38335027 : Blo 1309973 38335027 := bstep (se 1 (by rfl) ⟨28751270, by rfl⟩ : syracuseStep 38335027 = 57502541) B57502541
theorem B839520935 : Blo 1309973 839520935 := bstep (se 1 (by rfl) ⟨629640701, by rfl⟩ : syracuseStep 839520935 = 1259281403) B1259281403
theorem B113374079 : Blo 1309973 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B6640865 : Blo 1309973 6640865 := bstep (se 2 (by rfl) ⟨2490324, by rfl⟩ : syracuseStep 6640865 = 4980649) B4980649
theorem B3733415 : Blo 1309973 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B8402899 : Blo 1309973 8402899 := bstep (se 1 (by rfl) ⟨6302174, by rfl⟩ : syracuseStep 8402899 = 12604349) B12604349
theorem B14924087 : Blo 1309973 14924087 := bstep (se 1 (by rfl) ⟨11193065, by rfl⟩ : syracuseStep 14924087 = 22386131) B22386131
theorem B2947679 : Blo 1309973 2947679 := bstep (se 1 (by rfl) ⟨2210759, by rfl⟩ : syracuseStep 2947679 = 4421519) B4421519
theorem B6298697 : Blo 1309973 6298697 := bstep (se 2 (by rfl) ⟨2362011, by rfl⟩ : syracuseStep 6298697 = 4724023) B4724023
theorem B5602547 : Blo 1309973 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B1309979 : Blo 1309973 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B1966127 : Blo 1309973 1966127 := bstep (se 1 (by rfl) ⟨1474595, by rfl⟩ : syracuseStep 1966127 = 2949191) B2949191
theorem B9445535 : Blo 1309973 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B1967387 : Blo 1309973 1967387 := bstep (se 1 (by rfl) ⟨1475540, by rfl⟩ : syracuseStep 1967387 = 2951081) B2951081
theorem B4425947 : Blo 1309973 4425947 := bstep (se 1 (by rfl) ⟨3319460, by rfl⟩ : syracuseStep 4425947 = 6638921) B6638921
theorem B11201267 : Blo 1309973 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B559680623 : Blo 1309973 559680623 := bstep (se 1 (by rfl) ⟨419760467, by rfl⟩ : syracuseStep 559680623 = 839520935) B839520935
theorem B75582719 : Blo 1309973 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B51113369 : Blo 1309973 51113369 := bstep (se 2 (by rfl) ⟨19167513, by rfl⟩ : syracuseStep 51113369 = 38335027) B38335027
theorem B4427243 : Blo 1309973 4427243 := bstep (se 1 (by rfl) ⟨3320432, by rfl⟩ : syracuseStep 4427243 = 6640865) B6640865
theorem B10629215 : Blo 1309973 10629215 := bstep (se 1 (by rfl) ⟨7971911, by rfl⟩ : syracuseStep 10629215 = 15943823) B15943823
theorem B9949391 : Blo 1309973 9949391 := bstep (se 1 (by rfl) ⟨7462043, by rfl⟩ : syracuseStep 9949391 = 14924087) B14924087
theorem B4199131 : Blo 1309973 4199131 := bstep (se 1 (by rfl) ⟨3149348, by rfl⟩ : syracuseStep 4199131 = 6298697) B6298697
theorem B6059099 : Blo 1309973 6059099 := bstep (se 1 (by rfl) ⟨4544324, by rfl⟩ : syracuseStep 6059099 = 9088649) B9088649
theorem B11203865 : Blo 1309973 11203865 := bstep (se 2 (by rfl) ⟨4201449, by rfl⟩ : syracuseStep 11203865 = 8402899) B8402899
theorem B14940125 : Blo 1309973 14940125 := bstep (se 3 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 14940125 = 5602547) B5602547
theorem B776132675 : Blo 1309973 776132675 := bstep (se 1 (by rfl) ⟨582099506, by rfl⟩ : syracuseStep 776132675 = 1164199013) B1164199013
theorem B5314835 : Blo 1309973 5314835 := bstep (se 1 (by rfl) ⟨3986126, by rfl⟩ : syracuseStep 5314835 = 7972253) B7972253
theorem B2488943 : Blo 1309973 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B4422653 : Blo 1309973 4422653 := bstep (se 3 (by rfl) ⟨829247, by rfl⟩ : syracuseStep 4422653 = 1658495) B1658495
theorem B1965119 : Blo 1309973 1965119 := bstep (se 1 (by rfl) ⟨1473839, by rfl⟩ : syracuseStep 1965119 = 2947679) B2947679
theorem B1310751 : Blo 1309973 1310751 := bstep (se 1 (by rfl) ⟨983063, by rfl⟩ : syracuseStep 1310751 = 1966127) B1966127
theorem B7086143 : Blo 1309973 7086143 := bstep (se 1 (by rfl) ⟨5314607, by rfl⟩ : syracuseStep 7086143 = 10629215) B10629215
theorem B4039399 : Blo 1309973 4039399 := bstep (se 1 (by rfl) ⟨3029549, by rfl⟩ : syracuseStep 4039399 = 6059099) B6059099
theorem B1311591 : Blo 1309973 1311591 := bstep (se 1 (by rfl) ⟨983693, by rfl⟩ : syracuseStep 1311591 = 1967387) B1967387
theorem B2950631 : Blo 1309973 2950631 := bstep (se 1 (by rfl) ⟨2212973, by rfl⟩ : syracuseStep 2950631 = 4425947) B4425947
theorem B2951495 : Blo 1309973 2951495 := bstep (se 1 (by rfl) ⟨2213621, by rfl⟩ : syracuseStep 2951495 = 4427243) B4427243
theorem B5598841 : Blo 1309973 5598841 := bstep (se 2 (by rfl) ⟨2099565, by rfl⟩ : syracuseStep 5598841 = 4199131) B4199131
theorem B3543223 : Blo 1309973 3543223 := bstep (se 1 (by rfl) ⟨2657417, by rfl⟩ : syracuseStep 3543223 = 5314835) B5314835
theorem B1659295 : Blo 1309973 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B7467511 : Blo 1309973 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B34075579 : Blo 1309973 34075579 := bstep (se 1 (by rfl) ⟨25556684, by rfl⟩ : syracuseStep 34075579 = 51113369) B51113369
theorem B6297023 : Blo 1309973 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B6632927 : Blo 1309973 6632927 := bstep (se 1 (by rfl) ⟨4974695, by rfl⟩ : syracuseStep 6632927 = 9949391) B9949391
theorem B7469243 : Blo 1309973 7469243 := bstep (se 1 (by rfl) ⟨5601932, by rfl⟩ : syracuseStep 7469243 = 11203865) B11203865
theorem B9960083 : Blo 1309973 9960083 := bstep (se 1 (by rfl) ⟨7470062, by rfl⟩ : syracuseStep 9960083 = 14940125) B14940125
theorem B517421783 : Blo 1309973 517421783 := bstep (se 1 (by rfl) ⟨388066337, by rfl⟩ : syracuseStep 517421783 = 776132675) B776132675
theorem B2948435 : Blo 1309973 2948435 := bstep (se 1 (by rfl) ⟨2211326, by rfl⟩ : syracuseStep 2948435 = 4422653) B4422653
theorem B1310079 : Blo 1309973 1310079 := bstep (se 1 (by rfl) ⟨982559, by rfl⟩ : syracuseStep 1310079 = 1965119) B1965119
theorem B373120415 : Blo 1309973 373120415 := bstep (se 1 (by rfl) ⟨279840311, by rfl⟩ : syracuseStep 373120415 = 559680623) B559680623
theorem B50388479 : Blo 1309973 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B2212393 : Blo 1309973 2212393 := bstep (se 2 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 2212393 = 1659295) B1659295
theorem B1967087 : Blo 1309973 1967087 := bstep (se 1 (by rfl) ⟨1475315, by rfl⟩ : syracuseStep 1967087 = 2950631) B2950631
theorem B45434105 : Blo 1309973 45434105 := bstep (se 2 (by rfl) ⟨17037789, by rfl⟩ : syracuseStep 45434105 = 34075579) B34075579
theorem B1967663 : Blo 1309973 1967663 := bstep (se 1 (by rfl) ⟨1475747, by rfl⟩ : syracuseStep 1967663 = 2951495) B2951495
theorem B7465121 : Blo 1309973 7465121 := bstep (se 2 (by rfl) ⟨2799420, by rfl⟩ : syracuseStep 7465121 = 5598841) B5598841
theorem B9956681 : Blo 1309973 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B4198015 : Blo 1309973 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B5385865 : Blo 1309973 5385865 := bstep (se 2 (by rfl) ⟨2019699, by rfl⟩ : syracuseStep 5385865 = 4039399) B4039399
theorem B6640055 : Blo 1309973 6640055 := bstep (se 1 (by rfl) ⟨4980041, by rfl⟩ : syracuseStep 6640055 = 9960083) B9960083
theorem B1379791421 : Blo 1309973 1379791421 := bstep (se 3 (by rfl) ⟨258710891, by rfl⟩ : syracuseStep 1379791421 = 517421783) B517421783
theorem B248746943 : Blo 1309973 248746943 := bstep (se 1 (by rfl) ⟨186560207, by rfl⟩ : syracuseStep 248746943 = 373120415) B373120415
theorem B33592319 : Blo 1309973 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B4724095 : Blo 1309973 4724095 := bstep (se 1 (by rfl) ⟨3543071, by rfl⟩ : syracuseStep 4724095 = 7086143) B7086143
theorem B4724297 : Blo 1309973 4724297 := bstep (se 2 (by rfl) ⟨1771611, by rfl⟩ : syracuseStep 4724297 = 3543223) B3543223
theorem B4421951 : Blo 1309973 4421951 := bstep (se 1 (by rfl) ⟨3316463, by rfl⟩ : syracuseStep 4421951 = 6632927) B6632927
theorem B4979495 : Blo 1309973 4979495 := bstep (se 1 (by rfl) ⟨3734621, by rfl⟩ : syracuseStep 4979495 = 7469243) B7469243
theorem B1965623 : Blo 1309973 1965623 := bstep (se 1 (by rfl) ⟨1474217, by rfl⟩ : syracuseStep 1965623 = 2948435) B2948435
theorem B165831295 : Blo 1309973 165831295 := bstep (se 1 (by rfl) ⟨124373471, by rfl⟩ : syracuseStep 165831295 = 248746943) B248746943
theorem B1311391 : Blo 1309973 1311391 := bstep (se 1 (by rfl) ⟨983543, by rfl⟩ : syracuseStep 1311391 = 1967087) B1967087
theorem B2949857 : Blo 1309973 2949857 := bstep (se 2 (by rfl) ⟨1106196, by rfl⟩ : syracuseStep 2949857 = 2212393) B2212393
theorem B1311775 : Blo 1309973 1311775 := bstep (se 1 (by rfl) ⟨983831, by rfl⟩ : syracuseStep 1311775 = 1967663) B1967663
theorem B3319663 : Blo 1309973 3319663 := bstep (se 1 (by rfl) ⟨2489747, by rfl⟩ : syracuseStep 3319663 = 4979495) B4979495
theorem B5597353 : Blo 1309973 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B6637787 : Blo 1309973 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B4426703 : Blo 1309973 4426703 := bstep (se 1 (by rfl) ⟨3320027, by rfl⟩ : syracuseStep 4426703 = 6640055) B6640055
theorem B30289403 : Blo 1309973 30289403 := bstep (se 1 (by rfl) ⟨22717052, by rfl⟩ : syracuseStep 30289403 = 45434105) B45434105
theorem B3149531 : Blo 1309973 3149531 := bstep (se 1 (by rfl) ⟨2362148, by rfl⟩ : syracuseStep 3149531 = 4724297) B4724297
theorem B4976747 : Blo 1309973 4976747 := bstep (se 1 (by rfl) ⟨3732560, by rfl⟩ : syracuseStep 4976747 = 7465121) B7465121
theorem B7181153 : Blo 1309973 7181153 := bstep (se 2 (by rfl) ⟨2692932, by rfl⟩ : syracuseStep 7181153 = 5385865) B5385865
theorem B919860947 : Blo 1309973 919860947 := bstep (se 1 (by rfl) ⟨689895710, by rfl⟩ : syracuseStep 919860947 = 1379791421) B1379791421
theorem B22394879 : Blo 1309973 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B2947967 : Blo 1309973 2947967 := bstep (se 1 (by rfl) ⟨2210975, by rfl⟩ : syracuseStep 2947967 = 4421951) B4421951
theorem B6298793 : Blo 1309973 6298793 := bstep (se 2 (by rfl) ⟨2362047, by rfl⟩ : syracuseStep 6298793 = 4724095) B4724095
theorem B1310415 : Blo 1309973 1310415 := bstep (se 1 (by rfl) ⟨982811, by rfl⟩ : syracuseStep 1310415 = 1965623) B1965623
theorem B3317831 : Blo 1309973 3317831 := bstep (se 1 (by rfl) ⟨2488373, by rfl⟩ : syracuseStep 3317831 = 4976747) B4976747
theorem B7463137 : Blo 1309973 7463137 := bstep (se 2 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 7463137 = 5597353) B5597353
theorem B1966571 : Blo 1309973 1966571 := bstep (se 1 (by rfl) ⟨1474928, by rfl⟩ : syracuseStep 1966571 = 2949857) B2949857
theorem B4425191 : Blo 1309973 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B2951135 : Blo 1309973 2951135 := bstep (se 1 (by rfl) ⟨2213351, by rfl⟩ : syracuseStep 2951135 = 4426703) B4426703
theorem B2099687 : Blo 1309973 2099687 := bstep (se 1 (by rfl) ⟨1574765, by rfl⟩ : syracuseStep 2099687 = 3149531) B3149531
theorem B4426217 : Blo 1309973 4426217 := bstep (se 2 (by rfl) ⟨1659831, by rfl⟩ : syracuseStep 4426217 = 3319663) B3319663
theorem B4787435 : Blo 1309973 4787435 := bstep (se 1 (by rfl) ⟨3590576, by rfl⟩ : syracuseStep 4787435 = 7181153) B7181153
theorem B613240631 : Blo 1309973 613240631 := bstep (se 1 (by rfl) ⟨459930473, by rfl⟩ : syracuseStep 613240631 = 919860947) B919860947
theorem B14929919 : Blo 1309973 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B4199195 : Blo 1309973 4199195 := bstep (se 1 (by rfl) ⟨3149396, by rfl⟩ : syracuseStep 4199195 = 6298793) B6298793
theorem B221108393 : Blo 1309973 221108393 := bstep (se 2 (by rfl) ⟨82915647, by rfl⟩ : syracuseStep 221108393 = 165831295) B165831295
theorem B1965311 : Blo 1309973 1965311 := bstep (se 1 (by rfl) ⟨1473983, by rfl⟩ : syracuseStep 1965311 = 2947967) B2947967
theorem B20192935 : Blo 1309973 20192935 := bstep (se 1 (by rfl) ⟨15144701, by rfl⟩ : syracuseStep 20192935 = 30289403) B30289403
theorem B2211887 : Blo 1309973 2211887 := bstep (se 1 (by rfl) ⟨1658915, by rfl⟩ : syracuseStep 2211887 = 3317831) B3317831
theorem B1311047 : Blo 1309973 1311047 := bstep (se 1 (by rfl) ⟨983285, by rfl⟩ : syracuseStep 1311047 = 1966571) B1966571
theorem B2950127 : Blo 1309973 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B1967423 : Blo 1309973 1967423 := bstep (se 1 (by rfl) ⟨1475567, by rfl⟩ : syracuseStep 1967423 = 2951135) B2951135
theorem B2950811 : Blo 1309973 2950811 := bstep (se 1 (by rfl) ⟨2213108, by rfl⟩ : syracuseStep 2950811 = 4426217) B4426217
theorem B12766493 : Blo 1309973 12766493 := bstep (se 3 (by rfl) ⟨2393717, by rfl⟩ : syracuseStep 12766493 = 4787435) B4787435
theorem B5599165 : Blo 1309973 5599165 := bstep (se 3 (by rfl) ⟨1049843, by rfl⟩ : syracuseStep 5599165 = 2099687) B2099687
theorem B26923913 : Blo 1309973 26923913 := bstep (se 2 (by rfl) ⟨10096467, by rfl⟩ : syracuseStep 26923913 = 20192935) B20192935
theorem B408827087 : Blo 1309973 408827087 := bstep (se 1 (by rfl) ⟨306620315, by rfl⟩ : syracuseStep 408827087 = 613240631) B613240631
theorem B9950849 : Blo 1309973 9950849 := bstep (se 2 (by rfl) ⟨3731568, by rfl⟩ : syracuseStep 9950849 = 7463137) B7463137
theorem B2799463 : Blo 1309973 2799463 := bstep (se 1 (by rfl) ⟨2099597, by rfl⟩ : syracuseStep 2799463 = 4199195) B4199195
theorem B147405595 : Blo 1309973 147405595 := bstep (se 1 (by rfl) ⟨110554196, by rfl⟩ : syracuseStep 147405595 = 221108393) B221108393
theorem B1310207 : Blo 1309973 1310207 := bstep (se 1 (by rfl) ⟨982655, by rfl⟩ : syracuseStep 1310207 = 1965311) B1965311
theorem B9953279 : Blo 1309973 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B1474591 : Blo 1309973 1474591 := bstep (se 1 (by rfl) ⟨1105943, by rfl⟩ : syracuseStep 1474591 = 2211887) B2211887
theorem B17949275 : Blo 1309973 17949275 := bstep (se 1 (by rfl) ⟨13461956, by rfl⟩ : syracuseStep 17949275 = 26923913) B26923913
theorem B1966751 : Blo 1309973 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B1311615 : Blo 1309973 1311615 := bstep (se 1 (by rfl) ⟨983711, by rfl⟩ : syracuseStep 1311615 = 1967423) B1967423
theorem B1967207 : Blo 1309973 1967207 := bstep (se 1 (by rfl) ⟨1475405, by rfl⟩ : syracuseStep 1967207 = 2950811) B2950811
theorem B6635519 : Blo 1309973 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B7465553 : Blo 1309973 7465553 := bstep (se 2 (by rfl) ⟨2799582, by rfl⟩ : syracuseStep 7465553 = 5599165) B5599165
theorem B272551391 : Blo 1309973 272551391 := bstep (se 1 (by rfl) ⟨204413543, by rfl⟩ : syracuseStep 272551391 = 408827087) B408827087
theorem B3732617 : Blo 1309973 3732617 := bstep (se 2 (by rfl) ⟨1399731, by rfl⟩ : syracuseStep 3732617 = 2799463) B2799463
theorem B34043981 : Blo 1309973 34043981 := bstep (se 3 (by rfl) ⟨6383246, by rfl⟩ : syracuseStep 34043981 = 12766493) B12766493
theorem B196540793 : Blo 1309973 196540793 := bstep (se 2 (by rfl) ⟨73702797, by rfl⟩ : syracuseStep 196540793 = 147405595) B147405595
theorem B6633899 : Blo 1309973 6633899 := bstep (se 1 (by rfl) ⟨4975424, by rfl⟩ : syracuseStep 6633899 = 9950849) B9950849
theorem B1966121 : Blo 1309973 1966121 := bstep (se 2 (by rfl) ⟨737295, by rfl⟩ : syracuseStep 1966121 = 1474591) B1474591
theorem B90783949 : Blo 1309973 90783949 := bstep (se 3 (by rfl) ⟨17021990, by rfl⟩ : syracuseStep 90783949 = 34043981) B34043981
theorem B1311167 : Blo 1309973 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B1311471 : Blo 1309973 1311471 := bstep (se 1 (by rfl) ⟨983603, by rfl⟩ : syracuseStep 1311471 = 1967207) B1967207
theorem B181700927 : Blo 1309973 181700927 := bstep (se 1 (by rfl) ⟨136275695, by rfl⟩ : syracuseStep 181700927 = 272551391) B272551391
theorem B131027195 : Blo 1309973 131027195 := bstep (se 1 (by rfl) ⟨98270396, by rfl⟩ : syracuseStep 131027195 = 196540793) B196540793
theorem B4977035 : Blo 1309973 4977035 := bstep (se 1 (by rfl) ⟨3732776, by rfl⟩ : syracuseStep 4977035 = 7465553) B7465553
theorem B11966183 : Blo 1309973 11966183 := bstep (se 1 (by rfl) ⟨8974637, by rfl⟩ : syracuseStep 11966183 = 17949275) B17949275
theorem B2488411 : Blo 1309973 2488411 := bstep (se 1 (by rfl) ⟨1866308, by rfl⟩ : syracuseStep 2488411 = 3732617) B3732617
theorem B4422599 : Blo 1309973 4422599 := bstep (se 1 (by rfl) ⟨3316949, by rfl⟩ : syracuseStep 4422599 = 6633899) B6633899
theorem B4423679 : Blo 1309973 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B1310747 : Blo 1309973 1310747 := bstep (se 1 (by rfl) ⟨983060, by rfl⟩ : syracuseStep 1310747 = 1966121) B1966121
theorem B3317881 : Blo 1309973 3317881 := bstep (se 2 (by rfl) ⟨1244205, by rfl⟩ : syracuseStep 3317881 = 2488411) B2488411
theorem B87351463 : Blo 1309973 87351463 := bstep (se 1 (by rfl) ⟨65513597, by rfl⟩ : syracuseStep 87351463 = 131027195) B131027195
theorem B3318023 : Blo 1309973 3318023 := bstep (se 1 (by rfl) ⟨2488517, by rfl⟩ : syracuseStep 3318023 = 4977035) B4977035
theorem B121045265 : Blo 1309973 121045265 := bstep (se 2 (by rfl) ⟨45391974, by rfl⟩ : syracuseStep 121045265 = 90783949) B90783949
theorem B2949119 : Blo 1309973 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B7977455 : Blo 1309973 7977455 := bstep (se 1 (by rfl) ⟨5983091, by rfl⟩ : syracuseStep 7977455 = 11966183) B11966183
theorem B121133951 : Blo 1309973 121133951 := bstep (se 1 (by rfl) ⟨90850463, by rfl⟩ : syracuseStep 121133951 = 181700927) B181700927
theorem B2948399 : Blo 1309973 2948399 := bstep (se 1 (by rfl) ⟨2211299, by rfl⟩ : syracuseStep 2948399 = 4422599) B4422599
theorem B4423841 : Blo 1309973 4423841 := bstep (se 2 (by rfl) ⟨1658940, by rfl⟩ : syracuseStep 4423841 = 3317881) B3317881
theorem B2212015 : Blo 1309973 2212015 := bstep (se 1 (by rfl) ⟨1659011, by rfl⟩ : syracuseStep 2212015 = 3318023) B3318023
theorem B5318303 : Blo 1309973 5318303 := bstep (se 1 (by rfl) ⟨3988727, by rfl⟩ : syracuseStep 5318303 = 7977455) B7977455
theorem B116468617 : Blo 1309973 116468617 := bstep (se 2 (by rfl) ⟨43675731, by rfl⟩ : syracuseStep 116468617 = 87351463) B87351463
theorem B1966079 : Blo 1309973 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B80696843 : Blo 1309973 80696843 := bstep (se 1 (by rfl) ⟨60522632, by rfl⟩ : syracuseStep 80696843 = 121045265) B121045265
theorem B80755967 : Blo 1309973 80755967 := bstep (se 1 (by rfl) ⟨60566975, by rfl⟩ : syracuseStep 80755967 = 121133951) B121133951
theorem B1965599 : Blo 1309973 1965599 := bstep (se 1 (by rfl) ⟨1474199, by rfl⟩ : syracuseStep 1965599 = 2948399) B2948399
theorem B2949227 : Blo 1309973 2949227 := bstep (se 1 (by rfl) ⟨2211920, by rfl⟩ : syracuseStep 2949227 = 4423841) B4423841
theorem B2949353 : Blo 1309973 2949353 := bstep (se 2 (by rfl) ⟨1106007, by rfl⟩ : syracuseStep 2949353 = 2212015) B2212015
theorem B53797895 : Blo 1309973 53797895 := bstep (se 1 (by rfl) ⟨40348421, by rfl⟩ : syracuseStep 53797895 = 80696843) B80696843
theorem B1310719 : Blo 1309973 1310719 := bstep (se 1 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 1310719 = 1966079) B1966079
theorem B14182141 : Blo 1309973 14182141 := bstep (se 3 (by rfl) ⟨2659151, by rfl⟩ : syracuseStep 14182141 = 5318303) B5318303
theorem B155291489 : Blo 1309973 155291489 := bstep (se 2 (by rfl) ⟨58234308, by rfl⟩ : syracuseStep 155291489 = 116468617) B116468617
theorem B53837311 : Blo 1309973 53837311 := bstep (se 1 (by rfl) ⟨40377983, by rfl⟩ : syracuseStep 53837311 = 80755967) B80755967
theorem B1310399 : Blo 1309973 1310399 := bstep (se 1 (by rfl) ⟨982799, by rfl⟩ : syracuseStep 1310399 = 1965599) B1965599
theorem B1966151 : Blo 1309973 1966151 := bstep (se 1 (by rfl) ⟨1474613, by rfl⟩ : syracuseStep 1966151 = 2949227) B2949227
theorem B1966235 : Blo 1309973 1966235 := bstep (se 1 (by rfl) ⟨1474676, by rfl⟩ : syracuseStep 1966235 = 2949353) B2949353
theorem B35865263 : Blo 1309973 35865263 := bstep (se 1 (by rfl) ⟨26898947, by rfl⟩ : syracuseStep 35865263 = 53797895) B53797895
theorem B18909521 : Blo 1309973 18909521 := bstep (se 2 (by rfl) ⟨7091070, by rfl⟩ : syracuseStep 18909521 = 14182141) B14182141
theorem B71783081 : Blo 1309973 71783081 := bstep (se 2 (by rfl) ⟨26918655, by rfl⟩ : syracuseStep 71783081 = 53837311) B53837311
theorem B103527659 : Blo 1309973 103527659 := bstep (se 1 (by rfl) ⟨77645744, by rfl⟩ : syracuseStep 103527659 = 155291489) B155291489
theorem B1310767 : Blo 1309973 1310767 := bstep (se 1 (by rfl) ⟨983075, by rfl⟩ : syracuseStep 1310767 = 1966151) B1966151
theorem B1310823 : Blo 1309973 1310823 := bstep (se 1 (by rfl) ⟨983117, by rfl⟩ : syracuseStep 1310823 = 1966235) B1966235
theorem B276073757 : Blo 1309973 276073757 := bstep (se 3 (by rfl) ⟨51763829, by rfl⟩ : syracuseStep 276073757 = 103527659) B103527659
theorem B47855387 : Blo 1309973 47855387 := bstep (se 1 (by rfl) ⟨35891540, by rfl⟩ : syracuseStep 47855387 = 71783081) B71783081
theorem B23910175 : Blo 1309973 23910175 := bstep (se 1 (by rfl) ⟨17932631, by rfl⟩ : syracuseStep 23910175 = 35865263) B35865263
theorem B12606347 : Blo 1309973 12606347 := bstep (se 1 (by rfl) ⟨9454760, by rfl⟩ : syracuseStep 12606347 = 18909521) B18909521
theorem B31903591 : Blo 1309973 31903591 := bstep (se 1 (by rfl) ⟨23927693, by rfl⟩ : syracuseStep 31903591 = 47855387) B47855387
theorem B31880233 : Blo 1309973 31880233 := bstep (se 2 (by rfl) ⟨11955087, by rfl⟩ : syracuseStep 31880233 = 23910175) B23910175
theorem B8404231 : Blo 1309973 8404231 := bstep (se 1 (by rfl) ⟨6303173, by rfl⟩ : syracuseStep 8404231 = 12606347) B12606347
theorem B184049171 : Blo 1309973 184049171 := bstep (se 1 (by rfl) ⟨138036878, by rfl⟩ : syracuseStep 184049171 = 276073757) B276073757
theorem B42538121 : Blo 1309973 42538121 := bstep (se 2 (by rfl) ⟨15951795, by rfl⟩ : syracuseStep 42538121 = 31903591) B31903591
theorem B42506977 : Blo 1309973 42506977 := bstep (se 2 (by rfl) ⟨15940116, by rfl⟩ : syracuseStep 42506977 = 31880233) B31880233
theorem B11205641 : Blo 1309973 11205641 := bstep (se 2 (by rfl) ⟨4202115, by rfl⟩ : syracuseStep 11205641 = 8404231) B8404231
theorem B122699447 : Blo 1309973 122699447 := bstep (se 1 (by rfl) ⟨92024585, by rfl⟩ : syracuseStep 122699447 = 184049171) B184049171
theorem B81799631 : Blo 1309973 81799631 := bstep (se 1 (by rfl) ⟨61349723, by rfl⟩ : syracuseStep 81799631 = 122699447) B122699447
theorem B56675969 : Blo 1309973 56675969 := bstep (se 2 (by rfl) ⟨21253488, by rfl⟩ : syracuseStep 56675969 = 42506977) B42506977
theorem B28358747 : Blo 1309973 28358747 := bstep (se 1 (by rfl) ⟨21269060, by rfl⟩ : syracuseStep 28358747 = 42538121) B42538121
theorem B7470427 : Blo 1309973 7470427 := bstep (se 1 (by rfl) ⟨5602820, by rfl⟩ : syracuseStep 7470427 = 11205641) B11205641
theorem B37783979 : Blo 1309973 37783979 := bstep (se 1 (by rfl) ⟨28337984, by rfl⟩ : syracuseStep 37783979 = 56675969) B56675969
theorem B18905831 : Blo 1309973 18905831 := bstep (se 1 (by rfl) ⟨14179373, by rfl⟩ : syracuseStep 18905831 = 28358747) B28358747
theorem B54533087 : Blo 1309973 54533087 := bstep (se 1 (by rfl) ⟨40899815, by rfl⟩ : syracuseStep 54533087 = 81799631) B81799631
theorem B9960569 : Blo 1309973 9960569 := bstep (se 2 (by rfl) ⟨3735213, by rfl⟩ : syracuseStep 9960569 = 7470427) B7470427
theorem B12603887 : Blo 1309973 12603887 := bstep (se 1 (by rfl) ⟨9452915, by rfl⟩ : syracuseStep 12603887 = 18905831) B18905831
theorem B6640379 : Blo 1309973 6640379 := bstep (se 1 (by rfl) ⟨4980284, by rfl⟩ : syracuseStep 6640379 = 9960569) B9960569
theorem B25189319 : Blo 1309973 25189319 := bstep (se 1 (by rfl) ⟨18891989, by rfl⟩ : syracuseStep 25189319 = 37783979) B37783979
theorem B36355391 : Blo 1309973 36355391 := bstep (se 1 (by rfl) ⟨27266543, by rfl⟩ : syracuseStep 36355391 = 54533087) B54533087
theorem B4426919 : Blo 1309973 4426919 := bstep (se 1 (by rfl) ⟨3320189, by rfl⟩ : syracuseStep 4426919 = 6640379) B6640379
theorem B24236927 : Blo 1309973 24236927 := bstep (se 1 (by rfl) ⟨18177695, by rfl⟩ : syracuseStep 24236927 = 36355391) B36355391
theorem B8402591 : Blo 1309973 8402591 := bstep (se 1 (by rfl) ⟨6301943, by rfl⟩ : syracuseStep 8402591 = 12603887) B12603887
theorem B16792879 : Blo 1309973 16792879 := bstep (se 1 (by rfl) ⟨12594659, by rfl⟩ : syracuseStep 16792879 = 25189319) B25189319
theorem B22390505 : Blo 1309973 22390505 := bstep (se 2 (by rfl) ⟨8396439, by rfl⟩ : syracuseStep 22390505 = 16792879) B16792879
theorem B2951279 : Blo 1309973 2951279 := bstep (se 1 (by rfl) ⟨2213459, by rfl⟩ : syracuseStep 2951279 = 4426919) B4426919
theorem B16157951 : Blo 1309973 16157951 := bstep (se 1 (by rfl) ⟨12118463, by rfl⟩ : syracuseStep 16157951 = 24236927) B24236927
theorem B5601727 : Blo 1309973 5601727 := bstep (se 1 (by rfl) ⟨4201295, by rfl⟩ : syracuseStep 5601727 = 8402591) B8402591
theorem B14927003 : Blo 1309973 14927003 := bstep (se 1 (by rfl) ⟨11195252, by rfl⟩ : syracuseStep 14927003 = 22390505) B22390505
theorem B1967519 : Blo 1309973 1967519 := bstep (se 1 (by rfl) ⟨1475639, by rfl⟩ : syracuseStep 1967519 = 2951279) B2951279
theorem B7468969 : Blo 1309973 7468969 := bstep (se 2 (by rfl) ⟨2800863, by rfl⟩ : syracuseStep 7468969 = 5601727) B5601727
theorem B10771967 : Blo 1309973 10771967 := bstep (se 1 (by rfl) ⟨8078975, by rfl⟩ : syracuseStep 10771967 = 16157951) B16157951
theorem B1311679 : Blo 1309973 1311679 := bstep (se 1 (by rfl) ⟨983759, by rfl⟩ : syracuseStep 1311679 = 1967519) B1967519
theorem B7181311 : Blo 1309973 7181311 := bstep (se 1 (by rfl) ⟨5385983, by rfl⟩ : syracuseStep 7181311 = 10771967) B10771967
theorem B9958625 : Blo 1309973 9958625 := bstep (se 2 (by rfl) ⟨3734484, by rfl⟩ : syracuseStep 9958625 = 7468969) B7468969
theorem B9951335 : Blo 1309973 9951335 := bstep (se 1 (by rfl) ⟨7463501, by rfl⟩ : syracuseStep 9951335 = 14927003) B14927003
theorem B6639083 : Blo 1309973 6639083 := bstep (se 1 (by rfl) ⟨4979312, by rfl⟩ : syracuseStep 6639083 = 9958625) B9958625
theorem B9575081 : Blo 1309973 9575081 := bstep (se 2 (by rfl) ⟨3590655, by rfl⟩ : syracuseStep 9575081 = 7181311) B7181311
theorem B6634223 : Blo 1309973 6634223 := bstep (se 1 (by rfl) ⟨4975667, by rfl⟩ : syracuseStep 6634223 = 9951335) B9951335
theorem B6383387 : Blo 1309973 6383387 := bstep (se 1 (by rfl) ⟨4787540, by rfl⟩ : syracuseStep 6383387 = 9575081) B9575081
theorem B4426055 : Blo 1309973 4426055 := bstep (se 1 (by rfl) ⟨3319541, by rfl⟩ : syracuseStep 4426055 = 6639083) B6639083
theorem B4422815 : Blo 1309973 4422815 := bstep (se 1 (by rfl) ⟨3317111, by rfl⟩ : syracuseStep 4422815 = 6634223) B6634223
theorem B2950703 : Blo 1309973 2950703 := bstep (se 1 (by rfl) ⟨2213027, by rfl⟩ : syracuseStep 2950703 = 4426055) B4426055
theorem B4255591 : Blo 1309973 4255591 := bstep (se 1 (by rfl) ⟨3191693, by rfl⟩ : syracuseStep 4255591 = 6383387) B6383387
theorem B2948543 : Blo 1309973 2948543 := bstep (se 1 (by rfl) ⟨2211407, by rfl⟩ : syracuseStep 2948543 = 4422815) B4422815
theorem B1967135 : Blo 1309973 1967135 := bstep (se 1 (by rfl) ⟨1475351, by rfl⟩ : syracuseStep 1967135 = 2950703) B2950703
theorem B5674121 : Blo 1309973 5674121 := bstep (se 2 (by rfl) ⟨2127795, by rfl⟩ : syracuseStep 5674121 = 4255591) B4255591
theorem B1965695 : Blo 1309973 1965695 := bstep (se 1 (by rfl) ⟨1474271, by rfl⟩ : syracuseStep 1965695 = 2948543) B2948543
theorem B1311423 : Blo 1309973 1311423 := bstep (se 1 (by rfl) ⟨983567, by rfl⟩ : syracuseStep 1311423 = 1967135) B1967135
theorem B3782747 : Blo 1309973 3782747 := bstep (se 1 (by rfl) ⟨2837060, by rfl⟩ : syracuseStep 3782747 = 5674121) B5674121
theorem B1310463 : Blo 1309973 1310463 := bstep (se 1 (by rfl) ⟨982847, by rfl⟩ : syracuseStep 1310463 = 1965695) B1965695
theorem B2521831 : Blo 1309973 2521831 := bstep (se 1 (by rfl) ⟨1891373, by rfl⟩ : syracuseStep 2521831 = 3782747) B3782747
theorem B53799061 : Blo 1309973 53799061 := bstep (se 6 (by rfl) ⟨1260915, by rfl⟩ : syracuseStep 53799061 = 2521831) B2521831
theorem B71732081 : Blo 1309973 71732081 := bstep (se 2 (by rfl) ⟨26899530, by rfl⟩ : syracuseStep 71732081 = 53799061) B53799061
theorem B47821387 : Blo 1309973 47821387 := bstep (se 1 (by rfl) ⟨35866040, by rfl⟩ : syracuseStep 47821387 = 71732081) B71732081
theorem B63761849 : Blo 1309973 63761849 := bstep (se 2 (by rfl) ⟨23910693, by rfl⟩ : syracuseStep 63761849 = 47821387) B47821387
theorem B42507899 : Blo 1309973 42507899 := bstep (se 1 (by rfl) ⟨31880924, by rfl⟩ : syracuseStep 42507899 = 63761849) B63761849
theorem B28338599 : Blo 1309973 28338599 := bstep (se 1 (by rfl) ⟨21253949, by rfl⟩ : syracuseStep 28338599 = 42507899) B42507899
theorem B18892399 : Blo 1309973 18892399 := bstep (se 1 (by rfl) ⟨14169299, by rfl⟩ : syracuseStep 18892399 = 28338599) B28338599
theorem B25189865 : Blo 1309973 25189865 := bstep (se 2 (by rfl) ⟨9446199, by rfl⟩ : syracuseStep 25189865 = 18892399) B18892399
theorem B16793243 : Blo 1309973 16793243 := bstep (se 1 (by rfl) ⟨12594932, by rfl⟩ : syracuseStep 16793243 = 25189865) B25189865
theorem B11195495 : Blo 1309973 11195495 := bstep (se 1 (by rfl) ⟨8396621, by rfl⟩ : syracuseStep 11195495 = 16793243) B16793243
theorem B7463663 : Blo 1309973 7463663 := bstep (se 1 (by rfl) ⟨5597747, by rfl⟩ : syracuseStep 7463663 = 11195495) B11195495
theorem B4975775 : Blo 1309973 4975775 := bstep (se 1 (by rfl) ⟨3731831, by rfl⟩ : syracuseStep 4975775 = 7463663) B7463663
theorem B3317183 : Blo 1309973 3317183 := bstep (se 1 (by rfl) ⟨2487887, by rfl⟩ : syracuseStep 3317183 = 4975775) B4975775
theorem B2211455 : Blo 1309973 2211455 := bstep (se 1 (by rfl) ⟨1658591, by rfl⟩ : syracuseStep 2211455 = 3317183) B3317183
theorem B1474303 : Blo 1309973 1474303 := bstep (se 1 (by rfl) ⟨1105727, by rfl⟩ : syracuseStep 1474303 = 2211455) B2211455
theorem B1965737 : Blo 1309973 1965737 := bstep (se 2 (by rfl) ⟨737151, by rfl⟩ : syracuseStep 1965737 = 1474303) B1474303
theorem B1310491 : Blo 1309973 1310491 := bstep (se 1 (by rfl) ⟨982868, by rfl⟩ : syracuseStep 1310491 = 1965737) B1965737

theorem C0 (j : ℕ) (h1 : 327493 ≤ j) (h2 : j ≤ 327992) : Blo 1309973 (4 * j + 3) := by
  interval_cases j
  · exact B1309975
  · exact B1309979
  · exact B1309983
  · exact B1309987
  · exact B1309991
  · exact B1309995
  · exact B1309999
  · exact B1310003
  · exact B1310007
  · exact B1310011
  · exact B1310015
  · exact B1310019
  · exact B1310023
  · exact B1310027
  · exact B1310031
  · exact B1310035
  · exact B1310039
  · exact B1310043
  · exact B1310047
  · exact B1310051
  · exact B1310055
  · exact B1310059
  · exact B1310063
  · exact B1310067
  · exact B1310071
  · exact B1310075
  · exact B1310079
  · exact B1310083
  · exact B1310087
  · exact B1310091
  · exact B1310095
  · exact B1310099
  · exact B1310103
  · exact B1310107
  · exact B1310111
  · exact B1310115
  · exact B1310119
  · exact B1310123
  · exact B1310127
  · exact B1310131
  · exact B1310135
  · exact B1310139
  · exact B1310143
  · exact B1310147
  · exact B1310151
  · exact B1310155
  · exact B1310159
  · exact B1310163
  · exact B1310167
  · exact B1310171
  · exact B1310175
  · exact B1310179
  · exact B1310183
  · exact B1310187
  · exact B1310191
  · exact B1310195
  · exact B1310199
  · exact B1310203
  · exact B1310207
  · exact B1310211
  · exact B1310215
  · exact B1310219
  · exact B1310223
  · exact B1310227
  · exact B1310231
  · exact B1310235
  · exact B1310239
  · exact B1310243
  · exact B1310247
  · exact B1310251
  · exact B1310255
  · exact B1310259
  · exact B1310263
  · exact B1310267
  · exact B1310271
  · exact B1310275
  · exact B1310279
  · exact B1310283
  · exact B1310287
  · exact B1310291
  · exact B1310295
  · exact B1310299
  · exact B1310303
  · exact B1310307
  · exact B1310311
  · exact B1310315
  · exact B1310319
  · exact B1310323
  · exact B1310327
  · exact B1310331
  · exact B1310335
  · exact B1310339
  · exact B1310343
  · exact B1310347
  · exact B1310351
  · exact B1310355
  · exact B1310359
  · exact B1310363
  · exact B1310367
  · exact B1310371
  · exact B1310375
  · exact B1310379
  · exact B1310383
  · exact B1310387
  · exact B1310391
  · exact B1310395
  · exact B1310399
  · exact B1310403
  · exact B1310407
  · exact B1310411
  · exact B1310415
  · exact B1310419
  · exact B1310423
  · exact B1310427
  · exact B1310431
  · exact B1310435
  · exact B1310439
  · exact B1310443
  · exact B1310447
  · exact B1310451
  · exact B1310455
  · exact B1310459
  · exact B1310463
  · exact B1310467
  · exact B1310471
  · exact B1310475
  · exact B1310479
  · exact B1310483
  · exact B1310487
  · exact B1310491
  · exact B1310495
  · exact B1310499
  · exact B1310503
  · exact B1310507
  · exact B1310511
  · exact B1310515
  · exact B1310519
  · exact B1310523
  · exact B1310527
  · exact B1310531
  · exact B1310535
  · exact B1310539
  · exact B1310543
  · exact B1310547
  · exact B1310551
  · exact B1310555
  · exact B1310559
  · exact B1310563
  · exact B1310567
  · exact B1310571
  · exact B1310575
  · exact B1310579
  · exact B1310583
  · exact B1310587
  · exact B1310591
  · exact B1310595
  · exact B1310599
  · exact B1310603
  · exact B1310607
  · exact B1310611
  · exact B1310615
  · exact B1310619
  · exact B1310623
  · exact B1310627
  · exact B1310631
  · exact B1310635
  · exact B1310639
  · exact B1310643
  · exact B1310647
  · exact B1310651
  · exact B1310655
  · exact B1310659
  · exact B1310663
  · exact B1310667
  · exact B1310671
  · exact B1310675
  · exact B1310679
  · exact B1310683
  · exact B1310687
  · exact B1310691
  · exact B1310695
  · exact B1310699
  · exact B1310703
  · exact B1310707
  · exact B1310711
  · exact B1310715
  · exact B1310719
  · exact B1310723
  · exact B1310727
  · exact B1310731
  · exact B1310735
  · exact B1310739
  · exact B1310743
  · exact B1310747
  · exact B1310751
  · exact B1310755
  · exact B1310759
  · exact B1310763
  · exact B1310767
  · exact B1310771
  · exact B1310775
  · exact B1310779
  · exact B1310783
  · exact B1310787
  · exact B1310791
  · exact B1310795
  · exact B1310799
  · exact B1310803
  · exact B1310807
  · exact B1310811
  · exact B1310815
  · exact B1310819
  · exact B1310823
  · exact B1310827
  · exact B1310831
  · exact B1310835
  · exact B1310839
  · exact B1310843
  · exact B1310847
  · exact B1310851
  · exact B1310855
  · exact B1310859
  · exact B1310863
  · exact B1310867
  · exact B1310871
  · exact B1310875
  · exact B1310879
  · exact B1310883
  · exact B1310887
  · exact B1310891
  · exact B1310895
  · exact B1310899
  · exact B1310903
  · exact B1310907
  · exact B1310911
  · exact B1310915
  · exact B1310919
  · exact B1310923
  · exact B1310927
  · exact B1310931
  · exact B1310935
  · exact B1310939
  · exact B1310943
  · exact B1310947
  · exact B1310951
  · exact B1310955
  · exact B1310959
  · exact B1310963
  · exact B1310967
  · exact B1310971
  · exact B1310975
  · exact B1310979
  · exact B1310983
  · exact B1310987
  · exact B1310991
  · exact B1310995
  · exact B1310999
  · exact B1311003
  · exact B1311007
  · exact B1311011
  · exact B1311015
  · exact B1311019
  · exact B1311023
  · exact B1311027
  · exact B1311031
  · exact B1311035
  · exact B1311039
  · exact B1311043
  · exact B1311047
  · exact B1311051
  · exact B1311055
  · exact B1311059
  · exact B1311063
  · exact B1311067
  · exact B1311071
  · exact B1311075
  · exact B1311079
  · exact B1311083
  · exact B1311087
  · exact B1311091
  · exact B1311095
  · exact B1311099
  · exact B1311103
  · exact B1311107
  · exact B1311111
  · exact B1311115
  · exact B1311119
  · exact B1311123
  · exact B1311127
  · exact B1311131
  · exact B1311135
  · exact B1311139
  · exact B1311143
  · exact B1311147
  · exact B1311151
  · exact B1311155
  · exact B1311159
  · exact B1311163
  · exact B1311167
  · exact B1311171
  · exact B1311175
  · exact B1311179
  · exact B1311183
  · exact B1311187
  · exact B1311191
  · exact B1311195
  · exact B1311199
  · exact B1311203
  · exact B1311207
  · exact B1311211
  · exact B1311215
  · exact B1311219
  · exact B1311223
  · exact B1311227
  · exact B1311231
  · exact B1311235
  · exact B1311239
  · exact B1311243
  · exact B1311247
  · exact B1311251
  · exact B1311255
  · exact B1311259
  · exact B1311263
  · exact B1311267
  · exact B1311271
  · exact B1311275
  · exact B1311279
  · exact B1311283
  · exact B1311287
  · exact B1311291
  · exact B1311295
  · exact B1311299
  · exact B1311303
  · exact B1311307
  · exact B1311311
  · exact B1311315
  · exact B1311319
  · exact B1311323
  · exact B1311327
  · exact B1311331
  · exact B1311335
  · exact B1311339
  · exact B1311343
  · exact B1311347
  · exact B1311351
  · exact B1311355
  · exact B1311359
  · exact B1311363
  · exact B1311367
  · exact B1311371
  · exact B1311375
  · exact B1311379
  · exact B1311383
  · exact B1311387
  · exact B1311391
  · exact B1311395
  · exact B1311399
  · exact B1311403
  · exact B1311407
  · exact B1311411
  · exact B1311415
  · exact B1311419
  · exact B1311423
  · exact B1311427
  · exact B1311431
  · exact B1311435
  · exact B1311439
  · exact B1311443
  · exact B1311447
  · exact B1311451
  · exact B1311455
  · exact B1311459
  · exact B1311463
  · exact B1311467
  · exact B1311471
  · exact B1311475
  · exact B1311479
  · exact B1311483
  · exact B1311487
  · exact B1311491
  · exact B1311495
  · exact B1311499
  · exact B1311503
  · exact B1311507
  · exact B1311511
  · exact B1311515
  · exact B1311519
  · exact B1311523
  · exact B1311527
  · exact B1311531
  · exact B1311535
  · exact B1311539
  · exact B1311543
  · exact B1311547
  · exact B1311551
  · exact B1311555
  · exact B1311559
  · exact B1311563
  · exact B1311567
  · exact B1311571
  · exact B1311575
  · exact B1311579
  · exact B1311583
  · exact B1311587
  · exact B1311591
  · exact B1311595
  · exact B1311599
  · exact B1311603
  · exact B1311607
  · exact B1311611
  · exact B1311615
  · exact B1311619
  · exact B1311623
  · exact B1311627
  · exact B1311631
  · exact B1311635
  · exact B1311639
  · exact B1311643
  · exact B1311647
  · exact B1311651
  · exact B1311655
  · exact B1311659
  · exact B1311663
  · exact B1311667
  · exact B1311671
  · exact B1311675
  · exact B1311679
  · exact B1311683
  · exact B1311687
  · exact B1311691
  · exact B1311695
  · exact B1311699
  · exact B1311703
  · exact B1311707
  · exact B1311711
  · exact B1311715
  · exact B1311719
  · exact B1311723
  · exact B1311727
  · exact B1311731
  · exact B1311735
  · exact B1311739
  · exact B1311743
  · exact B1311747
  · exact B1311751
  · exact B1311755
  · exact B1311759
  · exact B1311763
  · exact B1311767
  · exact B1311771
  · exact B1311775
  · exact B1311779
  · exact B1311783
  · exact B1311787
  · exact B1311791
  · exact B1311795
  · exact B1311799
  · exact B1311803
  · exact B1311807
  · exact B1311811
  · exact B1311815
  · exact B1311819
  · exact B1311823
  · exact B1311827
  · exact B1311831
  · exact B1311835
  · exact B1311839
  · exact B1311843
  · exact B1311847
  · exact B1311851
  · exact B1311855
  · exact B1311859
  · exact B1311863
  · exact B1311867
  · exact B1311871
  · exact B1311875
  · exact B1311879
  · exact B1311883
  · exact B1311887
  · exact B1311891
  · exact B1311895
  · exact B1311899
  · exact B1311903
  · exact B1311907
  · exact B1311911
  · exact B1311915
  · exact B1311919
  · exact B1311923
  · exact B1311927
  · exact B1311931
  · exact B1311935
  · exact B1311939
  · exact B1311943
  · exact B1311947
  · exact B1311951
  · exact B1311955
  · exact B1311959
  · exact B1311963
  · exact B1311967
  · exact B1311971

theorem solution (m : ℕ) (hlo : 1309973 ≤ m) (hhi : m ≤ 1311973) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 327493 ≤ j := by omega
    have hj2 : j ≤ 327992 := by omega
    have hb : Blo 1309973 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
