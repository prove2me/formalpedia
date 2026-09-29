-- Prove2me | solution 1 for syracuse_descends_range_1076618_1080618
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:31.972989+00:00
-- url     : https://prove2.me/submissions/69c1e02f-c163-4f14-9c1d-60b93f70ecdb

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


theorem B1212421 : Blo 1076618 1212421 := bbase (se 4 (by rfl) ⟨113664, by rfl⟩ : syracuseStep 1212421 = 227329) (by norm_num)
theorem B2424869 : Blo 1076618 2424869 := bbase (se 4 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 2424869 = 454663) (by norm_num)
theorem B1212457 : Blo 1076618 1212457 := bbase (se 2 (by rfl) ⟨454671, by rfl⟩ : syracuseStep 1212457 = 909343) (by norm_num)
theorem B1212493 : Blo 1076618 1212493 := bbase (se 3 (by rfl) ⟨227342, by rfl⟩ : syracuseStep 1212493 = 454685) (by norm_num)
theorem B29491285 : Blo 1076618 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B2424941 : Blo 1076618 2424941 := bbase (se 3 (by rfl) ⟨454676, by rfl⟩ : syracuseStep 2424941 = 909353) (by norm_num)
theorem B1212529 : Blo 1076618 1212529 := bbase (se 2 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 1212529 = 909397) (by norm_num)
theorem B3113093 : Blo 1076618 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B1212565 : Blo 1076618 1212565 := bbase (se 6 (by rfl) ⟨28419, by rfl⟩ : syracuseStep 1212565 = 56839) (by norm_num)
theorem B2425013 : Blo 1076618 2425013 := bbase (se 5 (by rfl) ⟨113672, by rfl⟩ : syracuseStep 2425013 = 227345) (by norm_num)
theorem B1212601 : Blo 1076618 1212601 := bbase (se 2 (by rfl) ⟨454725, by rfl⟩ : syracuseStep 1212601 = 909451) (by norm_num)
theorem B1212637 : Blo 1076618 1212637 := bbase (se 3 (by rfl) ⟨227369, by rfl⟩ : syracuseStep 1212637 = 454739) (by norm_num)
theorem B3637493 : Blo 1076618 3637493 := bbase (se 5 (by rfl) ⟨170507, by rfl⟩ : syracuseStep 3637493 = 341015) (by norm_num)
theorem B2425085 : Blo 1076618 2425085 := bbase (se 3 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 2425085 = 909407) (by norm_num)
theorem B1212673 : Blo 1076618 1212673 := bbase (se 2 (by rfl) ⟨454752, by rfl⟩ : syracuseStep 1212673 = 909505) (by norm_num)
theorem B1212709 : Blo 1076618 1212709 := bbase (se 4 (by rfl) ⟨113691, by rfl⟩ : syracuseStep 1212709 = 227383) (by norm_num)
theorem B3506485 : Blo 1076618 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B2425157 : Blo 1076618 2425157 := bbase (se 4 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 2425157 = 454717) (by norm_num)
theorem B1212745 : Blo 1076618 1212745 := bbase (se 2 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 1212745 = 909559) (by norm_num)
theorem B1212781 : Blo 1076618 1212781 := bbase (se 3 (by rfl) ⟨227396, by rfl⟩ : syracuseStep 1212781 = 454793) (by norm_num)
theorem B2457973 : Blo 1076618 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B2425229 : Blo 1076618 2425229 := bbase (se 3 (by rfl) ⟨454730, by rfl⟩ : syracuseStep 2425229 = 909461) (by norm_num)
theorem B1212817 : Blo 1076618 1212817 := bbase (se 2 (by rfl) ⟨454806, by rfl⟩ : syracuseStep 1212817 = 909613) (by norm_num)
theorem B13304213 : Blo 1076618 13304213 := bbase (se 6 (by rfl) ⟨311817, by rfl⟩ : syracuseStep 13304213 = 623635) (by norm_num)
theorem B1212853 : Blo 1076618 1212853 := bbase (se 5 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 1212853 = 113705) (by norm_num)
theorem B2425301 : Blo 1076618 2425301 := bbase (se 7 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 2425301 = 56843) (by norm_num)
theorem B1212889 : Blo 1076618 1212889 := bbase (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) (by norm_num)
theorem B8192501 : Blo 1076618 8192501 := bbase (se 5 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 8192501 = 768047) (by norm_num)
theorem B1212925 : Blo 1076618 1212925 := bbase (se 3 (by rfl) ⟨227423, by rfl⟩ : syracuseStep 1212925 = 454847) (by norm_num)
theorem B2425373 : Blo 1076618 2425373 := bbase (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) (by norm_num)
theorem B1212961 : Blo 1076618 1212961 := bbase (se 2 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 1212961 = 909721) (by norm_num)
theorem B1212997 : Blo 1076618 1212997 := bbase (se 4 (by rfl) ⟨113718, by rfl⟩ : syracuseStep 1212997 = 227437) (by norm_num)
theorem B1638989 : Blo 1076618 1638989 := bbase (se 3 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 1638989 = 614621) (by norm_num)
theorem B2425445 : Blo 1076618 2425445 := bbase (se 4 (by rfl) ⟨227385, by rfl⟩ : syracuseStep 2425445 = 454771) (by norm_num)
theorem B1213033 : Blo 1076618 1213033 := bbase (se 2 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 1213033 = 909775) (by norm_num)
theorem B1213069 : Blo 1076618 1213069 := bbase (se 3 (by rfl) ⟨227450, by rfl⟩ : syracuseStep 1213069 = 454901) (by norm_num)
theorem B3637925 : Blo 1076618 3637925 := bbase (se 4 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 3637925 = 682111) (by norm_num)
theorem B1475245 : Blo 1076618 1475245 := bbase (se 3 (by rfl) ⟨276608, by rfl⟩ : syracuseStep 1475245 = 553217) (by norm_num)
theorem B2425517 : Blo 1076618 2425517 := bbase (se 3 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 2425517 = 909569) (by norm_num)
theorem B1213105 : Blo 1076618 1213105 := bbase (se 2 (by rfl) ⟨454914, by rfl⟩ : syracuseStep 1213105 = 909829) (by norm_num)
theorem B3277493 : Blo 1076618 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B1213141 : Blo 1076618 1213141 := bbase (se 7 (by rfl) ⟨14216, by rfl⟩ : syracuseStep 1213141 = 28433) (by norm_num)
theorem B2425589 : Blo 1076618 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B1213177 : Blo 1076618 1213177 := bbase (se 2 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 1213177 = 909883) (by norm_num)
theorem B1213213 : Blo 1076618 1213213 := bbase (se 3 (by rfl) ⟨227477, by rfl⟩ : syracuseStep 1213213 = 454955) (by norm_num)
theorem B2425661 : Blo 1076618 2425661 := bbase (se 3 (by rfl) ⟨454811, by rfl⟩ : syracuseStep 2425661 = 909623) (by norm_num)
theorem B1213249 : Blo 1076618 1213249 := bbase (se 2 (by rfl) ⟨454968, by rfl⟩ : syracuseStep 1213249 = 909937) (by norm_num)
theorem B1213285 : Blo 1076618 1213285 := bbase (se 4 (by rfl) ⟨113745, by rfl⟩ : syracuseStep 1213285 = 227491) (by norm_num)
theorem B2425733 : Blo 1076618 2425733 := bbase (se 4 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 2425733 = 454825) (by norm_num)
theorem B1213321 : Blo 1076618 1213321 := bbase (se 2 (by rfl) ⟨454995, by rfl⟩ : syracuseStep 1213321 = 909991) (by norm_num)
theorem B1213357 : Blo 1076618 1213357 := bbase (se 3 (by rfl) ⟨227504, by rfl⟩ : syracuseStep 1213357 = 455009) (by norm_num)
theorem B2425805 : Blo 1076618 2425805 := bbase (se 3 (by rfl) ⟨454838, by rfl⟩ : syracuseStep 2425805 = 909677) (by norm_num)
theorem B1213393 : Blo 1076618 1213393 := bbase (se 2 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 1213393 = 910045) (by norm_num)
theorem B2589661 : Blo 1076618 2589661 := bbase (se 3 (by rfl) ⟨485561, by rfl⟩ : syracuseStep 2589661 = 971123) (by norm_num)
theorem B1213429 : Blo 1076618 1213429 := bbase (se 5 (by rfl) ⟨56879, by rfl⟩ : syracuseStep 1213429 = 113759) (by norm_num)
theorem B6554645 : Blo 1076618 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B2425877 : Blo 1076618 2425877 := bbase (se 6 (by rfl) ⟨56856, by rfl⟩ : syracuseStep 2425877 = 113713) (by norm_num)
theorem B1213465 : Blo 1076618 1213465 := bbase (se 2 (by rfl) ⟨455049, by rfl⟩ : syracuseStep 1213465 = 910099) (by norm_num)
theorem B1213501 : Blo 1076618 1213501 := bbase (se 3 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 1213501 = 455063) (by norm_num)
theorem B3638357 : Blo 1076618 3638357 := bbase (se 8 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 3638357 = 42637) (by norm_num)
theorem B2425949 : Blo 1076618 2425949 := bbase (se 3 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 2425949 = 909731) (by norm_num)
theorem B1213537 : Blo 1076618 1213537 := bbase (se 2 (by rfl) ⟨455076, by rfl⟩ : syracuseStep 1213537 = 910153) (by norm_num)
theorem B1967213 : Blo 1076618 1967213 := bbase (se 3 (by rfl) ⟨368852, by rfl⟩ : syracuseStep 1967213 = 737705) (by norm_num)
theorem B1213573 : Blo 1076618 1213573 := bbase (se 4 (by rfl) ⟨113772, by rfl⟩ : syracuseStep 1213573 = 227545) (by norm_num)
theorem B2426021 : Blo 1076618 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1213609 : Blo 1076618 1213609 := bbase (se 2 (by rfl) ⟨455103, by rfl⟩ : syracuseStep 1213609 = 910207) (by norm_num)
theorem B1213645 : Blo 1076618 1213645 := bbase (se 3 (by rfl) ⟨227558, by rfl⟩ : syracuseStep 1213645 = 455117) (by norm_num)
theorem B2426093 : Blo 1076618 2426093 := bbase (se 3 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 2426093 = 909785) (by norm_num)
theorem B1213681 : Blo 1076618 1213681 := bbase (se 2 (by rfl) ⟨455130, by rfl⟩ : syracuseStep 1213681 = 910261) (by norm_num)
theorem B5178629 : Blo 1076618 5178629 := bbase (se 4 (by rfl) ⟨485496, by rfl⟩ : syracuseStep 5178629 = 970993) (by norm_num)
theorem B1213717 : Blo 1076618 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B2426165 : Blo 1076618 2426165 := bbase (se 5 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 2426165 = 227453) (by norm_num)
theorem B1213753 : Blo 1076618 1213753 := bbase (se 2 (by rfl) ⟨455157, by rfl⟩ : syracuseStep 1213753 = 910315) (by norm_num)
theorem B7996757 : Blo 1076618 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B1213789 : Blo 1076618 1213789 := bbase (se 3 (by rfl) ⟨227585, by rfl⟩ : syracuseStep 1213789 = 455171) (by norm_num)
theorem B2426237 : Blo 1076618 2426237 := bbase (se 3 (by rfl) ⟨454919, by rfl⟩ : syracuseStep 2426237 = 909839) (by norm_num)
theorem B1213825 : Blo 1076618 1213825 := bbase (se 2 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 1213825 = 910369) (by norm_num)
theorem B1639829 : Blo 1076618 1639829 := bbase (se 6 (by rfl) ⟨38433, by rfl⟩ : syracuseStep 1639829 = 76867) (by norm_num)
theorem B1213861 : Blo 1076618 1213861 := bbase (se 4 (by rfl) ⟨113799, by rfl⟩ : syracuseStep 1213861 = 227599) (by norm_num)
theorem B2426309 : Blo 1076618 2426309 := bbase (se 4 (by rfl) ⟨227466, by rfl⟩ : syracuseStep 2426309 = 454933) (by norm_num)
theorem B1213897 : Blo 1076618 1213897 := bbase (se 2 (by rfl) ⟨455211, by rfl⟩ : syracuseStep 1213897 = 910423) (by norm_num)
theorem B1213933 : Blo 1076618 1213933 := bbase (se 3 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 1213933 = 455225) (by norm_num)
theorem B3638789 : Blo 1076618 3638789 := bbase (se 4 (by rfl) ⟨341136, by rfl⟩ : syracuseStep 3638789 = 682273) (by norm_num)
theorem B2426381 : Blo 1076618 2426381 := bbase (se 3 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 2426381 = 909893) (by norm_num)
theorem B1213969 : Blo 1076618 1213969 := bbase (se 2 (by rfl) ⟨455238, by rfl⟩ : syracuseStep 1213969 = 910477) (by norm_num)
theorem B4097573 : Blo 1076618 4097573 := bbase (se 4 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 4097573 = 768295) (by norm_num)
theorem B1214005 : Blo 1076618 1214005 := bbase (se 5 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 1214005 = 113813) (by norm_num)
theorem B4916821 : Blo 1076618 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B2426453 : Blo 1076618 2426453 := bbase (se 8 (by rfl) ⟨14217, by rfl⟩ : syracuseStep 2426453 = 28435) (by norm_num)
theorem B1214041 : Blo 1076618 1214041 := bbase (se 2 (by rfl) ⟨455265, by rfl⟩ : syracuseStep 1214041 = 910531) (by norm_num)
theorem B1214077 : Blo 1076618 1214077 := bbase (se 3 (by rfl) ⟨227639, by rfl⟩ : syracuseStep 1214077 = 455279) (by norm_num)
theorem B2426525 : Blo 1076618 2426525 := bbase (se 3 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 2426525 = 909947) (by norm_num)
theorem B1214113 : Blo 1076618 1214113 := bbase (se 2 (by rfl) ⟨455292, by rfl⟩ : syracuseStep 1214113 = 910585) (by norm_num)
theorem B1214149 : Blo 1076618 1214149 := bbase (se 4 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 1214149 = 227653) (by norm_num)
theorem B2426597 : Blo 1076618 2426597 := bbase (se 4 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 2426597 = 454987) (by norm_num)
theorem B1214185 : Blo 1076618 1214185 := bbase (se 2 (by rfl) ⟨455319, by rfl⟩ : syracuseStep 1214185 = 910639) (by norm_num)
theorem B1214221 : Blo 1076618 1214221 := bbase (se 3 (by rfl) ⟨227666, by rfl⟩ : syracuseStep 1214221 = 455333) (by norm_num)
theorem B2426669 : Blo 1076618 2426669 := bbase (se 3 (by rfl) ⟨455000, by rfl⟩ : syracuseStep 2426669 = 910001) (by norm_num)
theorem B1214257 : Blo 1076618 1214257 := bbase (se 2 (by rfl) ⟨455346, by rfl⟩ : syracuseStep 1214257 = 910693) (by norm_num)
theorem B5539637 : Blo 1076618 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B4097861 : Blo 1076618 4097861 := bbase (se 4 (by rfl) ⟨384174, by rfl⟩ : syracuseStep 4097861 = 768349) (by norm_num)
theorem B1214293 : Blo 1076618 1214293 := bbase (se 9 (by rfl) ⟨3557, by rfl⟩ : syracuseStep 1214293 = 7115) (by norm_num)
theorem B2426741 : Blo 1076618 2426741 := bbase (se 5 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 2426741 = 227507) (by norm_num)
theorem B1214329 : Blo 1076618 1214329 := bbase (se 2 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 1214329 = 910747) (by norm_num)
theorem B1214365 : Blo 1076618 1214365 := bbase (se 3 (by rfl) ⟨227693, by rfl⟩ : syracuseStep 1214365 = 455387) (by norm_num)
theorem B3639221 : Blo 1076618 3639221 := bbase (se 5 (by rfl) ⟨170588, by rfl⟩ : syracuseStep 3639221 = 341177) (by norm_num)
theorem B2426813 : Blo 1076618 2426813 := bbase (se 3 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 2426813 = 910055) (by norm_num)
theorem B1214401 : Blo 1076618 1214401 := bbase (se 2 (by rfl) ⟨455400, by rfl⟩ : syracuseStep 1214401 = 910801) (by norm_num)
theorem B1214437 : Blo 1076618 1214437 := bbase (se 4 (by rfl) ⟨113853, by rfl⟩ : syracuseStep 1214437 = 227707) (by norm_num)
theorem B2426885 : Blo 1076618 2426885 := bbase (se 4 (by rfl) ⟨227520, by rfl⟩ : syracuseStep 2426885 = 455041) (by norm_num)
theorem B1214473 : Blo 1076618 1214473 := bbase (se 2 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 1214473 = 910855) (by norm_num)
theorem B1214509 : Blo 1076618 1214509 := bbase (se 3 (by rfl) ⟨227720, by rfl⟩ : syracuseStep 1214509 = 455441) (by norm_num)
theorem B2426957 : Blo 1076618 2426957 := bbase (se 3 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 2426957 = 910109) (by norm_num)
theorem B1214545 : Blo 1076618 1214545 := bbase (se 2 (by rfl) ⟨455454, by rfl⟩ : syracuseStep 1214545 = 910909) (by norm_num)
theorem B1214581 : Blo 1076618 1214581 := bbase (se 5 (by rfl) ⟨56933, by rfl⟩ : syracuseStep 1214581 = 113867) (by norm_num)
theorem B2427029 : Blo 1076618 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B1214617 : Blo 1076618 1214617 := bbase (se 2 (by rfl) ⟨455481, by rfl⟩ : syracuseStep 1214617 = 910963) (by norm_num)
theorem B1214653 : Blo 1076618 1214653 := bbase (se 3 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 1214653 = 455495) (by norm_num)
theorem B2427101 : Blo 1076618 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B1214689 : Blo 1076618 1214689 := bbase (se 2 (by rfl) ⟨455508, by rfl⟩ : syracuseStep 1214689 = 911017) (by norm_num)
theorem B2459909 : Blo 1076618 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1214725 : Blo 1076618 1214725 := bbase (se 4 (by rfl) ⟨113880, by rfl⟩ : syracuseStep 1214725 = 227761) (by norm_num)
theorem B6916373 : Blo 1076618 6916373 := bbase (se 6 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 6916373 = 324205) (by norm_num)
theorem B2427173 : Blo 1076618 2427173 := bbase (se 4 (by rfl) ⟨227547, by rfl⟩ : syracuseStep 2427173 = 455095) (by norm_num)
theorem B1214761 : Blo 1076618 1214761 := bbase (se 2 (by rfl) ⟨455535, by rfl⟩ : syracuseStep 1214761 = 911071) (by norm_num)
theorem B2591045 : Blo 1076618 2591045 := bbase (se 4 (by rfl) ⟨242910, by rfl⟩ : syracuseStep 2591045 = 485821) (by norm_num)
theorem B1214797 : Blo 1076618 1214797 := bbase (se 3 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 1214797 = 455549) (by norm_num)
theorem B3639653 : Blo 1076618 3639653 := bbase (se 4 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 3639653 = 682435) (by norm_num)
theorem B2427245 : Blo 1076618 2427245 := bbase (se 3 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 2427245 = 910217) (by norm_num)
theorem B1214833 : Blo 1076618 1214833 := bbase (se 2 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 1214833 = 911125) (by norm_num)
theorem B1214869 : Blo 1076618 1214869 := bbase (se 6 (by rfl) ⟨28473, by rfl⟩ : syracuseStep 1214869 = 56947) (by norm_num)
theorem B2427317 : Blo 1076618 2427317 := bbase (se 5 (by rfl) ⟨113780, by rfl⟩ : syracuseStep 2427317 = 227561) (by norm_num)
theorem B1214905 : Blo 1076618 1214905 := bbase (se 2 (by rfl) ⟨455589, by rfl⟩ : syracuseStep 1214905 = 911179) (by norm_num)
theorem B1214941 : Blo 1076618 1214941 := bbase (se 3 (by rfl) ⟨227801, by rfl⟩ : syracuseStep 1214941 = 455603) (by norm_num)
theorem B2427389 : Blo 1076618 2427389 := bbase (se 3 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 2427389 = 910271) (by norm_num)
theorem B1214977 : Blo 1076618 1214977 := bbase (se 2 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 1214977 = 911233) (by norm_num)
theorem B2591237 : Blo 1076618 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B1215013 : Blo 1076618 1215013 := bbase (se 4 (by rfl) ⟨113907, by rfl⟩ : syracuseStep 1215013 = 227815) (by norm_num)
theorem B2427461 : Blo 1076618 2427461 := bbase (se 4 (by rfl) ⟨227574, by rfl⟩ : syracuseStep 2427461 = 455149) (by norm_num)
theorem B1215049 : Blo 1076618 1215049 := bbase (se 2 (by rfl) ⟨455643, by rfl⟩ : syracuseStep 1215049 = 911287) (by norm_num)
theorem B1215085 : Blo 1076618 1215085 := bbase (se 3 (by rfl) ⟨227828, by rfl⟩ : syracuseStep 1215085 = 455657) (by norm_num)
theorem B2427533 : Blo 1076618 2427533 := bbase (se 3 (by rfl) ⟨455162, by rfl⟩ : syracuseStep 2427533 = 910325) (by norm_num)
theorem B1215121 : Blo 1076618 1215121 := bbase (se 2 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 1215121 = 911341) (by norm_num)
theorem B1215157 : Blo 1076618 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B2427605 : Blo 1076618 2427605 := bbase (se 7 (by rfl) ⟨28448, by rfl⟩ : syracuseStep 2427605 = 56897) (by norm_num)
theorem B1215193 : Blo 1076618 1215193 := bbase (se 2 (by rfl) ⟨455697, by rfl⟩ : syracuseStep 1215193 = 911395) (by norm_num)
theorem B1215229 : Blo 1076618 1215229 := bbase (se 3 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 1215229 = 455711) (by norm_num)
theorem B1149709 : Blo 1076618 1149709 := bbase (se 3 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 1149709 = 431141) (by norm_num)
theorem B3640085 : Blo 1076618 3640085 := bbase (se 6 (by rfl) ⟨85314, by rfl⟩ : syracuseStep 3640085 = 170629) (by norm_num)
theorem B2427677 : Blo 1076618 2427677 := bbase (se 3 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 2427677 = 910379) (by norm_num)
theorem B1215265 : Blo 1076618 1215265 := bbase (se 2 (by rfl) ⟨455724, by rfl⟩ : syracuseStep 1215265 = 911449) (by norm_num)
theorem B1215301 : Blo 1076618 1215301 := bbase (se 4 (by rfl) ⟨113934, by rfl⟩ : syracuseStep 1215301 = 227869) (by norm_num)
theorem B2427749 : Blo 1076618 2427749 := bbase (se 4 (by rfl) ⟨227601, by rfl⟩ : syracuseStep 2427749 = 455203) (by norm_num)
theorem B1215337 : Blo 1076618 1215337 := bbase (se 2 (by rfl) ⟨455751, by rfl⟩ : syracuseStep 1215337 = 911503) (by norm_num)
theorem B1215373 : Blo 1076618 1215373 := bbase (se 3 (by rfl) ⟨227882, by rfl⟩ : syracuseStep 1215373 = 455765) (by norm_num)
theorem B2427821 : Blo 1076618 2427821 := bbase (se 3 (by rfl) ⟨455216, by rfl⟩ : syracuseStep 2427821 = 910433) (by norm_num)
theorem B1215409 : Blo 1076618 1215409 := bbase (se 2 (by rfl) ⟨455778, by rfl⟩ : syracuseStep 1215409 = 911557) (by norm_num)
theorem B1215445 : Blo 1076618 1215445 := bbase (se 7 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 1215445 = 28487) (by norm_num)
theorem B4099045 : Blo 1076618 4099045 := bbase (se 4 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 4099045 = 768571) (by norm_num)
theorem B2427893 : Blo 1076618 2427893 := bbase (se 5 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 2427893 = 227615) (by norm_num)
theorem B1215481 : Blo 1076618 1215481 := bbase (se 2 (by rfl) ⟨455805, by rfl⟩ : syracuseStep 1215481 = 911611) (by norm_num)
theorem B1215517 : Blo 1076618 1215517 := bbase (se 3 (by rfl) ⟨227909, by rfl⟩ : syracuseStep 1215517 = 455819) (by norm_num)
theorem B2427965 : Blo 1076618 2427965 := bbase (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) (by norm_num)
theorem B1215553 : Blo 1076618 1215553 := bbase (se 2 (by rfl) ⟨455832, by rfl⟩ : syracuseStep 1215553 = 911665) (by norm_num)
theorem B1215589 : Blo 1076618 1215589 := bbase (se 4 (by rfl) ⟨113961, by rfl⟩ : syracuseStep 1215589 = 227923) (by norm_num)
theorem B1150085 : Blo 1076618 1150085 := bbase (se 4 (by rfl) ⟨107820, by rfl⟩ : syracuseStep 1150085 = 215641) (by norm_num)
theorem B2428037 : Blo 1076618 2428037 := bbase (se 4 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 2428037 = 455257) (by norm_num)
theorem B1215625 : Blo 1076618 1215625 := bbase (se 2 (by rfl) ⟨455859, by rfl⟩ : syracuseStep 1215625 = 911719) (by norm_num)
theorem B1215661 : Blo 1076618 1215661 := bbase (se 3 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 1215661 = 455873) (by norm_num)
theorem B3640517 : Blo 1076618 3640517 := bbase (se 4 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 3640517 = 682597) (by norm_num)
theorem B1150157 : Blo 1076618 1150157 := bbase (se 3 (by rfl) ⟨215654, by rfl⟩ : syracuseStep 1150157 = 431309) (by norm_num)
theorem B2428109 : Blo 1076618 2428109 := bbase (se 3 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 2428109 = 910541) (by norm_num)
theorem B2592005 : Blo 1076618 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B2428181 : Blo 1076618 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B4099349 : Blo 1076618 4099349 := bbase (se 6 (by rfl) ⟨96078, by rfl⟩ : syracuseStep 4099349 = 192157) (by norm_num)
theorem B2428253 : Blo 1076618 2428253 := bbase (se 3 (by rfl) ⟨455297, by rfl⟩ : syracuseStep 2428253 = 910595) (by norm_num)
theorem B1150345 : Blo 1076618 1150345 := bbase (se 2 (by rfl) ⟨431379, by rfl⟩ : syracuseStep 1150345 = 862759) (by norm_num)
theorem B2428325 : Blo 1076618 2428325 := bbase (se 4 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 2428325 = 455311) (by norm_num)
theorem B7769557 : Blo 1076618 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B2428397 : Blo 1076618 2428397 := bbase (se 3 (by rfl) ⟨455324, by rfl⟩ : syracuseStep 2428397 = 910649) (by norm_num)
theorem B2428469 : Blo 1076618 2428469 := bbase (se 5 (by rfl) ⟨113834, by rfl⟩ : syracuseStep 2428469 = 227669) (by norm_num)
theorem B1150529 : Blo 1076618 1150529 := bbase (se 2 (by rfl) ⟨431448, by rfl⟩ : syracuseStep 1150529 = 862897) (by norm_num)
theorem B3640949 : Blo 1076618 3640949 := bbase (se 5 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 3640949 = 341339) (by norm_num)
theorem B2428541 : Blo 1076618 2428541 := bbase (se 3 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 2428541 = 910703) (by norm_num)
theorem B2428613 : Blo 1076618 2428613 := bbase (se 4 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 2428613 = 455365) (by norm_num)
theorem B2428685 : Blo 1076618 2428685 := bbase (se 3 (by rfl) ⟨455378, by rfl⟩ : syracuseStep 2428685 = 910757) (by norm_num)
theorem B2428757 : Blo 1076618 2428757 := bbase (se 9 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 2428757 = 14231) (by norm_num)
theorem B2428829 : Blo 1076618 2428829 := bbase (se 3 (by rfl) ⟨455405, by rfl⟩ : syracuseStep 2428829 = 910811) (by norm_num)
theorem B2625461 : Blo 1076618 2625461 := bbase (se 5 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 2625461 = 246137) (by norm_num)
theorem B2428901 : Blo 1076618 2428901 := bbase (se 4 (by rfl) ⟨227709, by rfl⟩ : syracuseStep 2428901 = 455419) (by norm_num)
theorem B1642493 : Blo 1076618 1642493 := bbase (se 3 (by rfl) ⟨307967, by rfl⟩ : syracuseStep 1642493 = 615935) (by norm_num)
theorem B3641381 : Blo 1076618 3641381 := bbase (se 4 (by rfl) ⟨341379, by rfl⟩ : syracuseStep 3641381 = 682759) (by norm_num)
theorem B2428973 : Blo 1076618 2428973 := bbase (se 3 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 2428973 = 910865) (by norm_num)
theorem B1478741 : Blo 1076618 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B2429045 : Blo 1076618 2429045 := bbase (se 5 (by rfl) ⟨113861, by rfl⟩ : syracuseStep 2429045 = 227723) (by norm_num)
theorem B2429117 : Blo 1076618 2429117 := bbase (se 3 (by rfl) ⟨455459, by rfl⟩ : syracuseStep 2429117 = 910919) (by norm_num)
theorem B3281093 : Blo 1076618 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B2429189 : Blo 1076618 2429189 := bbase (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) (by norm_num)
theorem B1151281 : Blo 1076618 1151281 := bbase (se 2 (by rfl) ⟨431730, by rfl⟩ : syracuseStep 1151281 = 863461) (by norm_num)
theorem B5902645 : Blo 1076618 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B2429261 : Blo 1076618 2429261 := bbase (se 3 (by rfl) ⟨455486, by rfl⟩ : syracuseStep 2429261 = 910973) (by norm_num)
theorem B1151353 : Blo 1076618 1151353 := bbase (se 2 (by rfl) ⟨431757, by rfl⟩ : syracuseStep 1151353 = 863515) (by norm_num)
theorem B2429333 : Blo 1076618 2429333 := bbase (se 6 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 2429333 = 113875) (by norm_num)
theorem B3641813 : Blo 1076618 3641813 := bbase (se 7 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 3641813 = 85355) (by norm_num)
theorem B2429405 : Blo 1076618 2429405 := bbase (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) (by norm_num)
theorem B2429477 : Blo 1076618 2429477 := bbase (se 4 (by rfl) ⟨227763, by rfl⟩ : syracuseStep 2429477 = 455527) (by norm_num)
theorem B1151533 : Blo 1076618 1151533 := bbase (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) (by norm_num)
theorem B2429549 : Blo 1076618 2429549 := bbase (se 3 (by rfl) ⟨455540, by rfl⟩ : syracuseStep 2429549 = 911081) (by norm_num)
theorem B2429621 : Blo 1076618 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B5182165 : Blo 1076618 5182165 := bbase (se 7 (by rfl) ⟨60728, by rfl⟩ : syracuseStep 5182165 = 121457) (by norm_num)
theorem B2429693 : Blo 1076618 2429693 := bbase (se 3 (by rfl) ⟨455567, by rfl⟩ : syracuseStep 2429693 = 911135) (by norm_num)
theorem B2429765 : Blo 1076618 2429765 := bbase (se 4 (by rfl) ⟨227790, by rfl⟩ : syracuseStep 2429765 = 455581) (by norm_num)
theorem B3642245 : Blo 1076618 3642245 := bbase (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) (by norm_num)
theorem B2429837 : Blo 1076618 2429837 := bbase (se 3 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 2429837 = 911189) (by norm_num)
theorem B8426389 : Blo 1076618 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B2429909 : Blo 1076618 2429909 := bbase (se 7 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 2429909 = 56951) (by norm_num)
theorem B1151977 : Blo 1076618 1151977 := bbase (se 2 (by rfl) ⟨431991, by rfl⟩ : syracuseStep 1151977 = 863983) (by norm_num)
theorem B2429981 : Blo 1076618 2429981 := bbase (se 3 (by rfl) ⟨455621, by rfl⟩ : syracuseStep 2429981 = 911243) (by norm_num)
theorem B1152101 : Blo 1076618 1152101 := bbase (se 4 (by rfl) ⟨108009, by rfl⟩ : syracuseStep 1152101 = 216019) (by norm_num)
theorem B2430053 : Blo 1076618 2430053 := bbase (se 4 (by rfl) ⟨227817, by rfl⟩ : syracuseStep 2430053 = 455635) (by norm_num)
theorem B2430125 : Blo 1076618 2430125 := bbase (se 3 (by rfl) ⟨455648, by rfl⟩ : syracuseStep 2430125 = 911297) (by norm_num)
theorem B2430197 : Blo 1076618 2430197 := bbase (se 5 (by rfl) ⟨113915, by rfl⟩ : syracuseStep 2430197 = 227831) (by norm_num)
theorem B3642677 : Blo 1076618 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B2594101 : Blo 1076618 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B2430269 : Blo 1076618 2430269 := bbase (se 3 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 2430269 = 911351) (by norm_num)
theorem B4101461 : Blo 1076618 4101461 := bbase (se 14 (by rfl) ⟨375, by rfl⟩ : syracuseStep 4101461 = 751) (by norm_num)
theorem B1152353 : Blo 1076618 1152353 := bbase (se 2 (by rfl) ⟨432132, by rfl⟩ : syracuseStep 1152353 = 864265) (by norm_num)
theorem B2430341 : Blo 1076618 2430341 := bbase (se 4 (by rfl) ⟨227844, by rfl⟩ : syracuseStep 2430341 = 455689) (by norm_num)
theorem B2725285 : Blo 1076618 2725285 := bbase (se 4 (by rfl) ⟨255495, by rfl⟩ : syracuseStep 2725285 = 510991) (by norm_num)
theorem B2430413 : Blo 1076618 2430413 := bbase (se 3 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 2430413 = 911405) (by norm_num)
theorem B1873405 : Blo 1076618 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B2397701 : Blo 1076618 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B2725397 : Blo 1076618 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B2430485 : Blo 1076618 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B2430557 : Blo 1076618 2430557 := bbase (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) (by norm_num)
theorem B4101749 : Blo 1076618 4101749 := bbase (se 5 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 4101749 = 384539) (by norm_num)
theorem B2463365 : Blo 1076618 2463365 := bbase (se 4 (by rfl) ⟨230940, by rfl⟩ : syracuseStep 2463365 = 461881) (by norm_num)
theorem B2430629 : Blo 1076618 2430629 := bbase (se 4 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 2430629 = 455743) (by norm_num)
theorem B2725589 : Blo 1076618 2725589 := bbase (se 7 (by rfl) ⟨31940, by rfl⟩ : syracuseStep 2725589 = 63881) (by norm_num)
theorem B1382113 : Blo 1076618 1382113 := bbase (se 2 (by rfl) ⟨518292, by rfl⟩ : syracuseStep 1382113 = 1036585) (by norm_num)
theorem B3643109 : Blo 1076618 3643109 := bbase (se 4 (by rfl) ⟨341541, by rfl⟩ : syracuseStep 3643109 = 683083) (by norm_num)
theorem B2430701 : Blo 1076618 2430701 := bbase (se 3 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 2430701 = 911513) (by norm_num)
theorem B1152797 : Blo 1076618 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B2430773 : Blo 1076618 2430773 := bbase (se 5 (by rfl) ⟨113942, by rfl⟩ : syracuseStep 2430773 = 227885) (by norm_num)
theorem B2430845 : Blo 1076618 2430845 := bbase (se 3 (by rfl) ⟨455783, by rfl⟩ : syracuseStep 2430845 = 911567) (by norm_num)
theorem B2594717 : Blo 1076618 2594717 := bbase (se 3 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 2594717 = 973019) (by norm_num)
theorem B2430917 : Blo 1076618 2430917 := bbase (se 4 (by rfl) ⟨227898, by rfl⟩ : syracuseStep 2430917 = 455797) (by norm_num)
theorem B2299853 : Blo 1076618 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B2594773 : Blo 1076618 2594773 := bbase (se 7 (by rfl) ⟨30407, by rfl⟩ : syracuseStep 2594773 = 60815) (by norm_num)
theorem B2430989 : Blo 1076618 2430989 := bbase (se 3 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 2430989 = 911621) (by norm_num)
theorem B1153045 : Blo 1076618 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B2725933 : Blo 1076618 2725933 := bbase (se 3 (by rfl) ⟨511112, by rfl⟩ : syracuseStep 2725933 = 1022225) (by norm_num)
theorem B2431061 : Blo 1076618 2431061 := bbase (se 8 (by rfl) ⟨14244, by rfl⟩ : syracuseStep 2431061 = 28489) (by norm_num)
theorem B3643541 : Blo 1076618 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B2726045 : Blo 1076618 2726045 := bbase (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) (by norm_num)
theorem B2431133 : Blo 1076618 2431133 := bbase (se 3 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 2431133 = 911675) (by norm_num)
theorem B2431205 : Blo 1076618 2431205 := bbase (se 4 (by rfl) ⟨227925, by rfl⟩ : syracuseStep 2431205 = 455851) (by norm_num)
theorem B2431277 : Blo 1076618 2431277 := bbase (se 3 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 2431277 = 911729) (by norm_num)
theorem B17733973 : Blo 1076618 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B2496853 : Blo 1076618 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B2726237 : Blo 1076618 2726237 := bbase (se 3 (by rfl) ⟨511169, by rfl⟩ : syracuseStep 2726237 = 1022339) (by norm_num)
theorem B2431349 : Blo 1076618 2431349 := bbase (se 5 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 2431349 = 227939) (by norm_num)
theorem B2365901 : Blo 1076618 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B1153489 : Blo 1076618 1153489 := bbase (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) (by norm_num)
theorem B1153549 : Blo 1076618 1153549 := bbase (se 3 (by rfl) ⟨216290, by rfl⟩ : syracuseStep 1153549 = 432581) (by norm_num)
theorem B3643973 : Blo 1076618 3643973 := bbase (se 4 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 3643973 = 683245) (by norm_num)
theorem B3283573 : Blo 1076618 3283573 := bbase (se 5 (by rfl) ⟨153917, by rfl⟩ : syracuseStep 3283573 = 307835) (by norm_num)
theorem B1940141 : Blo 1076618 1940141 := bbase (se 3 (by rfl) ⟨363776, by rfl⟩ : syracuseStep 1940141 = 727553) (by norm_num)
theorem B2726581 : Blo 1076618 2726581 := bbase (se 5 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 2726581 = 255617) (by norm_num)
theorem B4102933 : Blo 1076618 4102933 := bbase (se 6 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 4102933 = 192325) (by norm_num)
theorem B2726693 : Blo 1076618 2726693 := bbase (se 4 (by rfl) ⟨255627, by rfl⟩ : syracuseStep 2726693 = 511255) (by norm_num)
theorem B2300717 : Blo 1076618 2300717 := bbase (se 3 (by rfl) ⟨431384, by rfl⟩ : syracuseStep 2300717 = 862769) (by norm_num)
theorem B1940285 : Blo 1076618 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B1153865 : Blo 1076618 1153865 := bbase (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) (by norm_num)
theorem B1940365 : Blo 1076618 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B7773077 : Blo 1076618 7773077 := bbase (se 6 (by rfl) ⟨182181, by rfl⟩ : syracuseStep 7773077 = 364363) (by norm_num)
theorem B2300861 : Blo 1076618 2300861 := bbase (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) (by norm_num)
theorem B2595773 : Blo 1076618 2595773 := bbase (se 3 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 2595773 = 973415) (by norm_num)
theorem B2726885 : Blo 1076618 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B3644405 : Blo 1076618 3644405 := bbase (se 5 (by rfl) ⟨170831, by rfl⟩ : syracuseStep 3644405 = 341663) (by norm_num)
theorem B2432197 : Blo 1076618 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B1383637 : Blo 1076618 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B2727229 : Blo 1076618 2727229 := bbase (se 3 (by rfl) ⟨511355, by rfl⟩ : syracuseStep 2727229 = 1022711) (by norm_num)
theorem B1383841 : Blo 1076618 1383841 := bbase (se 2 (by rfl) ⟨518940, by rfl⟩ : syracuseStep 1383841 = 1037881) (by norm_num)
theorem B3644837 : Blo 1076618 3644837 := bbase (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) (by norm_num)
theorem B2727341 : Blo 1076618 2727341 := bbase (se 3 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 2727341 = 1022753) (by norm_num)
theorem B4562453 : Blo 1076618 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B2727533 : Blo 1076618 2727533 := bbase (se 3 (by rfl) ⟨511412, by rfl⟩ : syracuseStep 2727533 = 1022825) (by norm_num)
theorem B10362485 : Blo 1076618 10362485 := bbase (se 5 (by rfl) ⟨485741, by rfl⟩ : syracuseStep 10362485 = 971483) (by norm_num)
theorem B2301605 : Blo 1076618 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B2629397 : Blo 1076618 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B6922037 : Blo 1076618 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B3645269 : Blo 1076618 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B1843069 : Blo 1076618 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B2727877 : Blo 1076618 2727877 := bbase (se 4 (by rfl) ⟨255738, by rfl⟩ : syracuseStep 2727877 = 511477) (by norm_num)
theorem B2727989 : Blo 1076618 2727989 := bbase (se 5 (by rfl) ⟨127874, by rfl⟩ : syracuseStep 2727989 = 255749) (by norm_num)
theorem B8200277 : Blo 1076618 8200277 := bbase (se 8 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 8200277 = 96097) (by norm_num)
theorem B1941749 : Blo 1076618 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B2728181 : Blo 1076618 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B5185781 : Blo 1076618 5185781 := bbase (se 5 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 5185781 = 486167) (by norm_num)
theorem B1384705 : Blo 1076618 1384705 := bbase (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) (by norm_num)
theorem B3645701 : Blo 1076618 3645701 := bbase (se 4 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 3645701 = 683569) (by norm_num)
theorem B2302357 : Blo 1076618 2302357 := bbase (se 6 (by rfl) ⟨53961, by rfl⟩ : syracuseStep 2302357 = 107923) (by norm_num)
theorem B2302501 : Blo 1076618 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B2728525 : Blo 1076618 2728525 := bbase (se 3 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 2728525 = 1023197) (by norm_num)
theorem B3646133 : Blo 1076618 3646133 := bbase (se 5 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 3646133 = 341825) (by norm_num)
theorem B2728637 : Blo 1076618 2728637 := bbase (se 3 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 2728637 = 1023239) (by norm_num)
theorem B2630333 : Blo 1076618 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B2728829 : Blo 1076618 2728829 := bbase (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) (by norm_num)
theorem B2302877 : Blo 1076618 2302877 := bbase (se 3 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 2302877 = 863579) (by norm_num)
theorem B4367429 : Blo 1076618 4367429 := bbase (se 4 (by rfl) ⟨409446, by rfl⟩ : syracuseStep 4367429 = 818893) (by norm_num)
theorem B1614941 : Blo 1076618 1614941 := bbase (se 3 (by rfl) ⟨302801, by rfl⟩ : syracuseStep 1614941 = 605603) (by norm_num)
theorem B3646565 : Blo 1076618 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B1614965 : Blo 1076618 1614965 := bbase (se 5 (by rfl) ⟨75701, by rfl⟩ : syracuseStep 1614965 = 151403) (by norm_num)
theorem B1614989 : Blo 1076618 1614989 := bbase (se 3 (by rfl) ⟨302810, by rfl⟩ : syracuseStep 1614989 = 605621) (by norm_num)
theorem B1615013 : Blo 1076618 1615013 := bbase (se 4 (by rfl) ⟨151407, by rfl⟩ : syracuseStep 1615013 = 302815) (by norm_num)
theorem B1615037 : Blo 1076618 1615037 := bbase (se 3 (by rfl) ⟨302819, by rfl⟩ : syracuseStep 1615037 = 605639) (by norm_num)
theorem B1615061 : Blo 1076618 1615061 := bbase (se 7 (by rfl) ⟨18926, by rfl⟩ : syracuseStep 1615061 = 37853) (by norm_num)
theorem B2729173 : Blo 1076618 2729173 := bbase (se 7 (by rfl) ⟨31982, by rfl⟩ : syracuseStep 2729173 = 63965) (by norm_num)
theorem B1615085 : Blo 1076618 1615085 := bbase (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) (by norm_num)
theorem B2073853 : Blo 1076618 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B1615109 : Blo 1076618 1615109 := bbase (se 4 (by rfl) ⟨151416, by rfl⟩ : syracuseStep 1615109 = 302833) (by norm_num)
theorem B2303245 : Blo 1076618 2303245 := bbase (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) (by norm_num)
theorem B1615133 : Blo 1076618 1615133 := bbase (se 3 (by rfl) ⟨302837, by rfl⟩ : syracuseStep 1615133 = 605675) (by norm_num)
theorem B1615157 : Blo 1076618 1615157 := bbase (se 5 (by rfl) ⟨75710, by rfl⟩ : syracuseStep 1615157 = 151421) (by norm_num)
theorem B2729285 : Blo 1076618 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B1615181 : Blo 1076618 1615181 := bbase (se 3 (by rfl) ⟨302846, by rfl⟩ : syracuseStep 1615181 = 605693) (by norm_num)
theorem B1615205 : Blo 1076618 1615205 := bbase (se 4 (by rfl) ⟨151425, by rfl⟩ : syracuseStep 1615205 = 302851) (by norm_num)
theorem B1615229 : Blo 1076618 1615229 := bbase (se 3 (by rfl) ⟨302855, by rfl⟩ : syracuseStep 1615229 = 605711) (by norm_num)
theorem B1615253 : Blo 1076618 1615253 := bbase (se 6 (by rfl) ⟨37857, by rfl⟩ : syracuseStep 1615253 = 75715) (by norm_num)
theorem B1615277 : Blo 1076618 1615277 := bbase (se 3 (by rfl) ⟨302864, by rfl⟩ : syracuseStep 1615277 = 605729) (by norm_num)
theorem B1615301 : Blo 1076618 1615301 := bbase (se 4 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 1615301 = 302869) (by norm_num)
theorem B1615325 : Blo 1076618 1615325 := bbase (se 3 (by rfl) ⟨302873, by rfl⟩ : syracuseStep 1615325 = 605747) (by norm_num)
theorem B1615349 : Blo 1076618 1615349 := bbase (se 5 (by rfl) ⟨75719, by rfl⟩ : syracuseStep 1615349 = 151439) (by norm_num)
theorem B2729477 : Blo 1076618 2729477 := bbase (se 4 (by rfl) ⟨255888, by rfl⟩ : syracuseStep 2729477 = 511777) (by norm_num)
theorem B1615373 : Blo 1076618 1615373 := bbase (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) (by norm_num)
theorem B3646997 : Blo 1076618 3646997 := bbase (se 6 (by rfl) ⟨85476, by rfl⟩ : syracuseStep 3646997 = 170953) (by norm_num)
theorem B1615397 : Blo 1076618 1615397 := bbase (se 4 (by rfl) ⟨151443, by rfl⟩ : syracuseStep 1615397 = 302887) (by norm_num)
theorem B1615421 : Blo 1076618 1615421 := bbase (se 3 (by rfl) ⟨302891, by rfl⟩ : syracuseStep 1615421 = 605783) (by norm_num)
theorem B1615445 : Blo 1076618 1615445 := bbase (se 8 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 1615445 = 18931) (by norm_num)
theorem B1615469 : Blo 1076618 1615469 := bbase (se 3 (by rfl) ⟨302900, by rfl⟩ : syracuseStep 1615469 = 605801) (by norm_num)
theorem B1615493 : Blo 1076618 1615493 := bbase (se 4 (by rfl) ⟨151452, by rfl⟩ : syracuseStep 1615493 = 302905) (by norm_num)
theorem B1615517 : Blo 1076618 1615517 := bbase (se 3 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 1615517 = 605819) (by norm_num)
theorem B1615541 : Blo 1076618 1615541 := bbase (se 5 (by rfl) ⟨75728, by rfl⟩ : syracuseStep 1615541 = 151457) (by norm_num)
theorem B1615565 : Blo 1076618 1615565 := bbase (se 3 (by rfl) ⟨302918, by rfl⟩ : syracuseStep 1615565 = 605837) (by norm_num)
theorem B1615589 : Blo 1076618 1615589 := bbase (se 4 (by rfl) ⟨151461, by rfl⟩ : syracuseStep 1615589 = 302923) (by norm_num)
theorem B1615613 : Blo 1076618 1615613 := bbase (se 3 (by rfl) ⟨302927, by rfl⟩ : syracuseStep 1615613 = 605855) (by norm_num)
theorem B1615637 : Blo 1076618 1615637 := bbase (se 6 (by rfl) ⟨37866, by rfl⟩ : syracuseStep 1615637 = 75733) (by norm_num)
theorem B1615661 : Blo 1076618 1615661 := bbase (se 3 (by rfl) ⟨302936, by rfl⟩ : syracuseStep 1615661 = 605873) (by norm_num)
theorem B1615685 : Blo 1076618 1615685 := bbase (se 4 (by rfl) ⟨151470, by rfl⟩ : syracuseStep 1615685 = 302941) (by norm_num)
theorem B1615709 : Blo 1076618 1615709 := bbase (se 3 (by rfl) ⟨302945, by rfl⟩ : syracuseStep 1615709 = 605891) (by norm_num)
theorem B2729821 : Blo 1076618 2729821 := bbase (se 3 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 2729821 = 1023683) (by norm_num)
theorem B1615733 : Blo 1076618 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B1615757 : Blo 1076618 1615757 := bbase (se 3 (by rfl) ⟨302954, by rfl⟩ : syracuseStep 1615757 = 605909) (by norm_num)
theorem B1615781 : Blo 1076618 1615781 := bbase (se 4 (by rfl) ⟨151479, by rfl⟩ : syracuseStep 1615781 = 302959) (by norm_num)
theorem B1615805 : Blo 1076618 1615805 := bbase (se 3 (by rfl) ⟨302963, by rfl⟩ : syracuseStep 1615805 = 605927) (by norm_num)
theorem B2729933 : Blo 1076618 2729933 := bbase (se 3 (by rfl) ⟨511862, by rfl⟩ : syracuseStep 2729933 = 1023725) (by norm_num)
theorem B1615829 : Blo 1076618 1615829 := bbase (se 7 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 1615829 = 37871) (by norm_num)
theorem B1615853 : Blo 1076618 1615853 := bbase (se 3 (by rfl) ⟨302972, by rfl⟩ : syracuseStep 1615853 = 605945) (by norm_num)
theorem B1615877 : Blo 1076618 1615877 := bbase (se 4 (by rfl) ⟨151488, by rfl⟩ : syracuseStep 1615877 = 302977) (by norm_num)
theorem B9218069 : Blo 1076618 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B1615901 : Blo 1076618 1615901 := bbase (se 3 (by rfl) ⟨302981, by rfl⟩ : syracuseStep 1615901 = 605963) (by norm_num)
theorem B1615925 : Blo 1076618 1615925 := bbase (se 5 (by rfl) ⟨75746, by rfl⟩ : syracuseStep 1615925 = 151493) (by norm_num)
theorem B1615949 : Blo 1076618 1615949 := bbase (se 3 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 1615949 = 605981) (by norm_num)
theorem B1615973 : Blo 1076618 1615973 := bbase (se 4 (by rfl) ⟨151497, by rfl⟩ : syracuseStep 1615973 = 302995) (by norm_num)
theorem B5187685 : Blo 1076618 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B5187701 : Blo 1076618 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B1615997 : Blo 1076618 1615997 := bbase (se 3 (by rfl) ⟨302999, by rfl⟩ : syracuseStep 1615997 = 605999) (by norm_num)
theorem B2730125 : Blo 1076618 2730125 := bbase (se 3 (by rfl) ⟨511898, by rfl⟩ : syracuseStep 2730125 = 1023797) (by norm_num)
theorem B1616021 : Blo 1076618 1616021 := bbase (se 6 (by rfl) ⟨37875, by rfl⟩ : syracuseStep 1616021 = 75751) (by norm_num)
theorem B1616045 : Blo 1076618 1616045 := bbase (se 3 (by rfl) ⟨303008, by rfl⟩ : syracuseStep 1616045 = 606017) (by norm_num)
theorem B1616069 : Blo 1076618 1616069 := bbase (se 4 (by rfl) ⟨151506, by rfl⟩ : syracuseStep 1616069 = 303013) (by norm_num)
theorem B1616093 : Blo 1076618 1616093 := bbase (se 3 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 1616093 = 606035) (by norm_num)
theorem B1616117 : Blo 1076618 1616117 := bbase (se 5 (by rfl) ⟨75755, by rfl⟩ : syracuseStep 1616117 = 151511) (by norm_num)
theorem B1616141 : Blo 1076618 1616141 := bbase (se 3 (by rfl) ⟨303026, by rfl⟩ : syracuseStep 1616141 = 606053) (by norm_num)
theorem B2074901 : Blo 1076618 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B1616165 : Blo 1076618 1616165 := bbase (se 4 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 1616165 = 303031) (by norm_num)
theorem B1091881 : Blo 1076618 1091881 := bbase (se 2 (by rfl) ⟨409455, by rfl⟩ : syracuseStep 1091881 = 818911) (by norm_num)
theorem B3451189 : Blo 1076618 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1616189 : Blo 1076618 1616189 := bbase (se 3 (by rfl) ⟨303035, by rfl⟩ : syracuseStep 1616189 = 606071) (by norm_num)
theorem B1616213 : Blo 1076618 1616213 := bbase (se 10 (by rfl) ⟨2367, by rfl⟩ : syracuseStep 1616213 = 4735) (by norm_num)
theorem B1616237 : Blo 1076618 1616237 := bbase (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) (by norm_num)
theorem B2107765 : Blo 1076618 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B1616261 : Blo 1076618 1616261 := bbase (se 4 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 1616261 = 303049) (by norm_num)
theorem B1616285 : Blo 1076618 1616285 := bbase (se 3 (by rfl) ⟨303053, by rfl⟩ : syracuseStep 1616285 = 606107) (by norm_num)
theorem B1616309 : Blo 1076618 1616309 := bbase (se 5 (by rfl) ⟨75764, by rfl⟩ : syracuseStep 1616309 = 151529) (by norm_num)
theorem B1616333 : Blo 1076618 1616333 := bbase (se 3 (by rfl) ⟨303062, by rfl⟩ : syracuseStep 1616333 = 606125) (by norm_num)
theorem B1616357 : Blo 1076618 1616357 := bbase (se 4 (by rfl) ⟨151533, by rfl⟩ : syracuseStep 1616357 = 303067) (by norm_num)
theorem B2730469 : Blo 1076618 2730469 := bbase (se 4 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 2730469 = 511963) (by norm_num)
theorem B1616381 : Blo 1076618 1616381 := bbase (se 3 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 1616381 = 606143) (by norm_num)
theorem B1616405 : Blo 1076618 1616405 := bbase (se 6 (by rfl) ⟨37884, by rfl⟩ : syracuseStep 1616405 = 75769) (by norm_num)
theorem B1616429 : Blo 1076618 1616429 := bbase (se 3 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 1616429 = 606161) (by norm_num)
theorem B1616453 : Blo 1076618 1616453 := bbase (se 4 (by rfl) ⟨151542, by rfl⟩ : syracuseStep 1616453 = 303085) (by norm_num)
theorem B2730581 : Blo 1076618 2730581 := bbase (se 8 (by rfl) ⟨15999, by rfl⟩ : syracuseStep 2730581 = 31999) (by norm_num)
theorem B1616477 : Blo 1076618 1616477 := bbase (se 3 (by rfl) ⟨303089, by rfl⟩ : syracuseStep 1616477 = 606179) (by norm_num)
theorem B1616501 : Blo 1076618 1616501 := bbase (se 5 (by rfl) ⟨75773, by rfl⟩ : syracuseStep 1616501 = 151547) (by norm_num)
theorem B2075269 : Blo 1076618 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B1616525 : Blo 1076618 1616525 := bbase (se 3 (by rfl) ⟨303098, by rfl⟩ : syracuseStep 1616525 = 606197) (by norm_num)
theorem B1616549 : Blo 1076618 1616549 := bbase (se 4 (by rfl) ⟨151551, by rfl⟩ : syracuseStep 1616549 = 303103) (by norm_num)
theorem B1616573 : Blo 1076618 1616573 := bbase (se 3 (by rfl) ⟨303107, by rfl⟩ : syracuseStep 1616573 = 606215) (by norm_num)
theorem B1616597 : Blo 1076618 1616597 := bbase (se 7 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 1616597 = 37889) (by norm_num)
theorem B1616621 : Blo 1076618 1616621 := bbase (se 3 (by rfl) ⟨303116, by rfl⟩ : syracuseStep 1616621 = 606233) (by norm_num)
theorem B2304749 : Blo 1076618 2304749 := bbase (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) (by norm_num)
theorem B1616645 : Blo 1076618 1616645 := bbase (se 4 (by rfl) ⟨151560, by rfl⟩ : syracuseStep 1616645 = 303121) (by norm_num)
theorem B17705749 : Blo 1076618 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B2730773 : Blo 1076618 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B1616669 : Blo 1076618 1616669 := bbase (se 3 (by rfl) ⟨303125, by rfl⟩ : syracuseStep 1616669 = 606251) (by norm_num)
theorem B1616693 : Blo 1076618 1616693 := bbase (se 5 (by rfl) ⟨75782, by rfl⟩ : syracuseStep 1616693 = 151565) (by norm_num)
theorem B1616717 : Blo 1076618 1616717 := bbase (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) (by norm_num)
theorem B1616741 : Blo 1076618 1616741 := bbase (se 4 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 1616741 = 303139) (by norm_num)
theorem B1616765 : Blo 1076618 1616765 := bbase (se 3 (by rfl) ⟨303143, by rfl⟩ : syracuseStep 1616765 = 606287) (by norm_num)
theorem B2304893 : Blo 1076618 2304893 := bbase (se 3 (by rfl) ⟨432167, by rfl⟩ : syracuseStep 2304893 = 864335) (by norm_num)
theorem B1682317 : Blo 1076618 1682317 := bbase (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) (by norm_num)
theorem B1616789 : Blo 1076618 1616789 := bbase (se 6 (by rfl) ⟨37893, by rfl⟩ : syracuseStep 1616789 = 75787) (by norm_num)
theorem B6138773 : Blo 1076618 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B1616813 : Blo 1076618 1616813 := bbase (se 3 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 1616813 = 606305) (by norm_num)
theorem B1616837 : Blo 1076618 1616837 := bbase (se 4 (by rfl) ⟨151578, by rfl⟩ : syracuseStep 1616837 = 303157) (by norm_num)
theorem B1616861 : Blo 1076618 1616861 := bbase (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) (by norm_num)
theorem B1616885 : Blo 1076618 1616885 := bbase (se 5 (by rfl) ⟨75791, by rfl⟩ : syracuseStep 1616885 = 151583) (by norm_num)
theorem B1616909 : Blo 1076618 1616909 := bbase (se 3 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 1616909 = 606341) (by norm_num)
theorem B1616933 : Blo 1076618 1616933 := bbase (se 4 (by rfl) ⟨151587, by rfl⟩ : syracuseStep 1616933 = 303175) (by norm_num)
theorem B1616957 : Blo 1076618 1616957 := bbase (se 3 (by rfl) ⟨303179, by rfl⟩ : syracuseStep 1616957 = 606359) (by norm_num)
theorem B1944653 : Blo 1076618 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B1616981 : Blo 1076618 1616981 := bbase (se 8 (by rfl) ⟨9474, by rfl⟩ : syracuseStep 1616981 = 18949) (by norm_num)
theorem B1617005 : Blo 1076618 1617005 := bbase (se 3 (by rfl) ⟨303188, by rfl⟩ : syracuseStep 1617005 = 606377) (by norm_num)
theorem B2731117 : Blo 1076618 2731117 := bbase (se 3 (by rfl) ⟨512084, by rfl⟩ : syracuseStep 2731117 = 1024169) (by norm_num)
theorem B1846381 : Blo 1076618 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B1617029 : Blo 1076618 1617029 := bbase (se 4 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 1617029 = 303193) (by norm_num)
theorem B1617053 : Blo 1076618 1617053 := bbase (se 3 (by rfl) ⟨303197, by rfl⟩ : syracuseStep 1617053 = 606395) (by norm_num)
theorem B1617077 : Blo 1076618 1617077 := bbase (se 5 (by rfl) ⟨75800, by rfl⟩ : syracuseStep 1617077 = 151601) (by norm_num)
theorem B1617101 : Blo 1076618 1617101 := bbase (se 3 (by rfl) ⟨303206, by rfl⟩ : syracuseStep 1617101 = 606413) (by norm_num)
theorem B2731229 : Blo 1076618 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B1617125 : Blo 1076618 1617125 := bbase (se 4 (by rfl) ⟨151605, by rfl⟩ : syracuseStep 1617125 = 303211) (by norm_num)
theorem B2305253 : Blo 1076618 2305253 := bbase (se 4 (by rfl) ⟨216117, by rfl⟩ : syracuseStep 2305253 = 432235) (by norm_num)
theorem B1617149 : Blo 1076618 1617149 := bbase (se 3 (by rfl) ⟨303215, by rfl⟩ : syracuseStep 1617149 = 606431) (by norm_num)
theorem B1617173 : Blo 1076618 1617173 := bbase (se 6 (by rfl) ⟨37902, by rfl⟩ : syracuseStep 1617173 = 75805) (by norm_num)
theorem B2764061 : Blo 1076618 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B1617197 : Blo 1076618 1617197 := bbase (se 3 (by rfl) ⟨303224, by rfl⟩ : syracuseStep 1617197 = 606449) (by norm_num)
theorem B1617221 : Blo 1076618 1617221 := bbase (se 4 (by rfl) ⟨151614, by rfl⟩ : syracuseStep 1617221 = 303229) (by norm_num)
theorem B4599125 : Blo 1076618 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B1617245 : Blo 1076618 1617245 := bbase (se 3 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 1617245 = 606467) (by norm_num)
theorem B1617269 : Blo 1076618 1617269 := bbase (se 5 (by rfl) ⟨75809, by rfl⟩ : syracuseStep 1617269 = 151619) (by norm_num)
theorem B1617293 : Blo 1076618 1617293 := bbase (se 3 (by rfl) ⟨303242, by rfl⟩ : syracuseStep 1617293 = 606485) (by norm_num)
theorem B2731421 : Blo 1076618 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B1617317 : Blo 1076618 1617317 := bbase (se 4 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 1617317 = 303247) (by norm_num)
theorem B1617341 : Blo 1076618 1617341 := bbase (se 3 (by rfl) ⟨303251, by rfl⟩ : syracuseStep 1617341 = 606503) (by norm_num)
theorem B1617365 : Blo 1076618 1617365 := bbase (se 7 (by rfl) ⟨18953, by rfl⟩ : syracuseStep 1617365 = 37907) (by norm_num)
theorem B1617389 : Blo 1076618 1617389 := bbase (se 3 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 1617389 = 606521) (by norm_num)
theorem B1617413 : Blo 1076618 1617413 := bbase (se 4 (by rfl) ⟨151632, by rfl⟩ : syracuseStep 1617413 = 303265) (by norm_num)
theorem B1617437 : Blo 1076618 1617437 := bbase (se 3 (by rfl) ⟨303269, by rfl⟩ : syracuseStep 1617437 = 606539) (by norm_num)
theorem B1617461 : Blo 1076618 1617461 := bbase (se 5 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 1617461 = 151637) (by norm_num)
theorem B1617485 : Blo 1076618 1617485 := bbase (se 3 (by rfl) ⟨303278, by rfl⟩ : syracuseStep 1617485 = 606557) (by norm_num)
theorem B1617509 : Blo 1076618 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B1617533 : Blo 1076618 1617533 := bbase (se 3 (by rfl) ⟨303287, by rfl⟩ : syracuseStep 1617533 = 606575) (by norm_num)
theorem B1617557 : Blo 1076618 1617557 := bbase (se 6 (by rfl) ⟨37911, by rfl⟩ : syracuseStep 1617557 = 75823) (by norm_num)
theorem B1748645 : Blo 1076618 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B1617581 : Blo 1076618 1617581 := bbase (se 3 (by rfl) ⟨303296, by rfl⟩ : syracuseStep 1617581 = 606593) (by norm_num)
theorem B5451461 : Blo 1076618 5451461 := bbase (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) (by norm_num)
theorem B1617605 : Blo 1076618 1617605 := bbase (se 4 (by rfl) ⟨151650, by rfl⟩ : syracuseStep 1617605 = 303301) (by norm_num)
theorem B6565589 : Blo 1076618 6565589 := bbase (se 7 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 6565589 = 153881) (by norm_num)
theorem B1617629 : Blo 1076618 1617629 := bbase (se 3 (by rfl) ⟨303305, by rfl⟩ : syracuseStep 1617629 = 606611) (by norm_num)
theorem B1617653 : Blo 1076618 1617653 := bbase (se 5 (by rfl) ⟨75827, by rfl⟩ : syracuseStep 1617653 = 151655) (by norm_num)
theorem B5254901 : Blo 1076618 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B2731765 : Blo 1076618 2731765 := bbase (se 5 (by rfl) ⟨128051, by rfl⟩ : syracuseStep 2731765 = 256103) (by norm_num)
theorem B1617677 : Blo 1076618 1617677 := bbase (se 3 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 1617677 = 606629) (by norm_num)
theorem B1617701 : Blo 1076618 1617701 := bbase (se 4 (by rfl) ⟨151659, by rfl⟩ : syracuseStep 1617701 = 303319) (by norm_num)
theorem B1617725 : Blo 1076618 1617725 := bbase (se 3 (by rfl) ⟨303323, by rfl⟩ : syracuseStep 1617725 = 606647) (by norm_num)
theorem B1617749 : Blo 1076618 1617749 := bbase (se 9 (by rfl) ⟨4739, by rfl⟩ : syracuseStep 1617749 = 9479) (by norm_num)
theorem B2731877 : Blo 1076618 2731877 := bbase (se 4 (by rfl) ⟨256113, by rfl⟩ : syracuseStep 2731877 = 512227) (by norm_num)
theorem B1617773 : Blo 1076618 1617773 := bbase (se 3 (by rfl) ⟨303332, by rfl⟩ : syracuseStep 1617773 = 606665) (by norm_num)
theorem B4665205 : Blo 1076618 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B1617797 : Blo 1076618 1617797 := bbase (se 4 (by rfl) ⟨151668, by rfl⟩ : syracuseStep 1617797 = 303337) (by norm_num)
theorem B1617821 : Blo 1076618 1617821 := bbase (se 3 (by rfl) ⟨303341, by rfl⟩ : syracuseStep 1617821 = 606683) (by norm_num)
theorem B1617845 : Blo 1076618 1617845 := bbase (se 5 (by rfl) ⟨75836, by rfl⟩ : syracuseStep 1617845 = 151673) (by norm_num)
theorem B1617869 : Blo 1076618 1617869 := bbase (se 3 (by rfl) ⟨303350, by rfl⟩ : syracuseStep 1617869 = 606701) (by norm_num)
theorem B1617893 : Blo 1076618 1617893 := bbase (se 4 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 1617893 = 303355) (by norm_num)
theorem B1617917 : Blo 1076618 1617917 := bbase (se 3 (by rfl) ⟨303359, by rfl⟩ : syracuseStep 1617917 = 606719) (by norm_num)
theorem B1617941 : Blo 1076618 1617941 := bbase (se 6 (by rfl) ⟨37920, by rfl⟩ : syracuseStep 1617941 = 75841) (by norm_num)
theorem B2732069 : Blo 1076618 2732069 := bbase (se 4 (by rfl) ⟨256131, by rfl⟩ : syracuseStep 2732069 = 512263) (by norm_num)
theorem B2043949 : Blo 1076618 2043949 := bbase (se 3 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 2043949 = 766481) (by norm_num)
theorem B1617965 : Blo 1076618 1617965 := bbase (se 3 (by rfl) ⟨303368, by rfl⟩ : syracuseStep 1617965 = 606737) (by norm_num)
theorem B1617989 : Blo 1076618 1617989 := bbase (se 4 (by rfl) ⟨151686, by rfl⟩ : syracuseStep 1617989 = 303373) (by norm_num)
theorem B2306141 : Blo 1076618 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B1618013 : Blo 1076618 1618013 := bbase (se 3 (by rfl) ⟨303377, by rfl⟩ : syracuseStep 1618013 = 606755) (by norm_num)
theorem B1618037 : Blo 1076618 1618037 := bbase (se 5 (by rfl) ⟨75845, by rfl⟩ : syracuseStep 1618037 = 151691) (by norm_num)
theorem B1618061 : Blo 1076618 1618061 := bbase (se 3 (by rfl) ⟨303386, by rfl⟩ : syracuseStep 1618061 = 606773) (by norm_num)
theorem B1618085 : Blo 1076618 1618085 := bbase (se 4 (by rfl) ⟨151695, by rfl⟩ : syracuseStep 1618085 = 303391) (by norm_num)
theorem B1618109 : Blo 1076618 1618109 := bbase (se 3 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 1618109 = 606791) (by norm_num)
theorem B2044109 : Blo 1076618 2044109 := bbase (se 3 (by rfl) ⟨383270, by rfl⟩ : syracuseStep 2044109 = 766541) (by norm_num)
theorem B1618133 : Blo 1076618 1618133 := bbase (se 7 (by rfl) ⟨18962, by rfl⟩ : syracuseStep 1618133 = 37925) (by norm_num)
theorem B1618157 : Blo 1076618 1618157 := bbase (se 3 (by rfl) ⟨303404, by rfl⟩ : syracuseStep 1618157 = 606809) (by norm_num)
theorem B1618181 : Blo 1076618 1618181 := bbase (se 4 (by rfl) ⟨151704, by rfl⟩ : syracuseStep 1618181 = 303409) (by norm_num)
theorem B1618205 : Blo 1076618 1618205 := bbase (se 3 (by rfl) ⟨303413, by rfl⟩ : syracuseStep 1618205 = 606827) (by norm_num)
theorem B1093933 : Blo 1076618 1093933 := bbase (se 3 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 1093933 = 410225) (by norm_num)
theorem B1618229 : Blo 1076618 1618229 := bbase (se 5 (by rfl) ⟨75854, by rfl⟩ : syracuseStep 1618229 = 151709) (by norm_num)
theorem B1618253 : Blo 1076618 1618253 := bbase (se 3 (by rfl) ⟨303422, by rfl⟩ : syracuseStep 1618253 = 606845) (by norm_num)
theorem B2306389 : Blo 1076618 2306389 := bbase (se 10 (by rfl) ⟨3378, by rfl⟩ : syracuseStep 2306389 = 6757) (by norm_num)
theorem B2044253 : Blo 1076618 2044253 := bbase (se 3 (by rfl) ⟨383297, by rfl⟩ : syracuseStep 2044253 = 766595) (by norm_num)
theorem B1618277 : Blo 1076618 1618277 := bbase (se 4 (by rfl) ⟨151713, by rfl⟩ : syracuseStep 1618277 = 303427) (by norm_num)
theorem B1618301 : Blo 1076618 1618301 := bbase (se 3 (by rfl) ⟨303431, by rfl⟩ : syracuseStep 1618301 = 606863) (by norm_num)
theorem B2732413 : Blo 1076618 2732413 := bbase (se 3 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 2732413 = 1024655) (by norm_num)
theorem B1618325 : Blo 1076618 1618325 := bbase (se 6 (by rfl) ⟨37929, by rfl⟩ : syracuseStep 1618325 = 75859) (by norm_num)
theorem B1618349 : Blo 1076618 1618349 := bbase (se 3 (by rfl) ⟨303440, by rfl⟩ : syracuseStep 1618349 = 606881) (by norm_num)
theorem B1618373 : Blo 1076618 1618373 := bbase (se 4 (by rfl) ⟨151722, by rfl⟩ : syracuseStep 1618373 = 303445) (by norm_num)
theorem B5190085 : Blo 1076618 5190085 := bbase (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) (by norm_num)
theorem B2765261 : Blo 1076618 2765261 := bbase (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) (by norm_num)
theorem B2339285 : Blo 1076618 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B1618397 : Blo 1076618 1618397 := bbase (se 3 (by rfl) ⟨303449, by rfl⟩ : syracuseStep 1618397 = 606899) (by norm_num)
theorem B2732525 : Blo 1076618 2732525 := bbase (se 3 (by rfl) ⟨512348, by rfl⟩ : syracuseStep 2732525 = 1024697) (by norm_num)
theorem B1618421 : Blo 1076618 1618421 := bbase (se 5 (by rfl) ⟨75863, by rfl⟩ : syracuseStep 1618421 = 151727) (by norm_num)
theorem B1618445 : Blo 1076618 1618445 := bbase (se 3 (by rfl) ⟨303458, by rfl⟩ : syracuseStep 1618445 = 606917) (by norm_num)
theorem B1618469 : Blo 1076618 1618469 := bbase (se 4 (by rfl) ⟨151731, by rfl⟩ : syracuseStep 1618469 = 303463) (by norm_num)
theorem B1618493 : Blo 1076618 1618493 := bbase (se 3 (by rfl) ⟨303467, by rfl⟩ : syracuseStep 1618493 = 606935) (by norm_num)
theorem B4371029 : Blo 1076618 4371029 := bbase (se 8 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 4371029 = 51223) (by norm_num)
theorem B1618517 : Blo 1076618 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B1094233 : Blo 1076618 1094233 := bbase (se 2 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 1094233 = 820675) (by norm_num)
theorem B1847909 : Blo 1076618 1847909 := bbase (se 4 (by rfl) ⟨173241, by rfl⟩ : syracuseStep 1847909 = 346483) (by norm_num)
theorem B1618541 : Blo 1076618 1618541 := bbase (se 3 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 1618541 = 606953) (by norm_num)
theorem B2044541 : Blo 1076618 2044541 := bbase (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) (by norm_num)
theorem B1618565 : Blo 1076618 1618565 := bbase (se 4 (by rfl) ⟨151740, by rfl⟩ : syracuseStep 1618565 = 303481) (by norm_num)
theorem B1618589 : Blo 1076618 1618589 := bbase (se 3 (by rfl) ⟨303485, by rfl⟩ : syracuseStep 1618589 = 606971) (by norm_num)
theorem B2732717 : Blo 1076618 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B1618613 : Blo 1076618 1618613 := bbase (se 5 (by rfl) ⟨75872, by rfl⟩ : syracuseStep 1618613 = 151745) (by norm_num)
theorem B1618637 : Blo 1076618 1618637 := bbase (se 3 (by rfl) ⟨303494, by rfl⟩ : syracuseStep 1618637 = 606989) (by norm_num)
theorem B1618661 : Blo 1076618 1618661 := bbase (se 4 (by rfl) ⟨151749, by rfl⟩ : syracuseStep 1618661 = 303499) (by norm_num)
theorem B1618685 : Blo 1076618 1618685 := bbase (se 3 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 1618685 = 607007) (by norm_num)
theorem B2667269 : Blo 1076618 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B2044693 : Blo 1076618 2044693 := bbase (se 6 (by rfl) ⟨47922, by rfl⟩ : syracuseStep 2044693 = 95845) (by norm_num)
theorem B1618709 : Blo 1076618 1618709 := bbase (se 6 (by rfl) ⟨37938, by rfl⟩ : syracuseStep 1618709 = 75877) (by norm_num)
theorem B1618733 : Blo 1076618 1618733 := bbase (se 3 (by rfl) ⟨303512, by rfl⟩ : syracuseStep 1618733 = 607025) (by norm_num)
theorem B1618757 : Blo 1076618 1618757 := bbase (se 4 (by rfl) ⟨151758, by rfl⟩ : syracuseStep 1618757 = 303517) (by norm_num)
theorem B2306893 : Blo 1076618 2306893 := bbase (se 3 (by rfl) ⟨432542, by rfl⟩ : syracuseStep 2306893 = 865085) (by norm_num)
theorem B1618781 : Blo 1076618 1618781 := bbase (se 3 (by rfl) ⟨303521, by rfl⟩ : syracuseStep 1618781 = 607043) (by norm_num)
theorem B1618805 : Blo 1076618 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B1618829 : Blo 1076618 1618829 := bbase (se 3 (by rfl) ⟨303530, by rfl⟩ : syracuseStep 1618829 = 607061) (by norm_num)
theorem B1618853 : Blo 1076618 1618853 := bbase (se 4 (by rfl) ⟨151767, by rfl⟩ : syracuseStep 1618853 = 303535) (by norm_num)
theorem B1618877 : Blo 1076618 1618877 := bbase (se 3 (by rfl) ⟨303539, by rfl⟩ : syracuseStep 1618877 = 607079) (by norm_num)
theorem B5452757 : Blo 1076618 5452757 := bbase (se 7 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 5452757 = 127799) (by norm_num)
theorem B1618901 : Blo 1076618 1618901 := bbase (se 7 (by rfl) ⟨18971, by rfl⟩ : syracuseStep 1618901 = 37943) (by norm_num)
theorem B1618925 : Blo 1076618 1618925 := bbase (se 3 (by rfl) ⟨303548, by rfl⟩ : syracuseStep 1618925 = 607097) (by norm_num)
theorem B1618949 : Blo 1076618 1618949 := bbase (se 4 (by rfl) ⟨151776, by rfl⟩ : syracuseStep 1618949 = 303553) (by norm_num)
theorem B2733061 : Blo 1076618 2733061 := bbase (se 4 (by rfl) ⟨256224, by rfl⟩ : syracuseStep 2733061 = 512449) (by norm_num)
theorem B1618973 : Blo 1076618 1618973 := bbase (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) (by norm_num)
theorem B1618997 : Blo 1076618 1618997 := bbase (se 5 (by rfl) ⟨75890, by rfl⟩ : syracuseStep 1618997 = 151781) (by norm_num)
theorem B4600901 : Blo 1076618 4600901 := bbase (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) (by norm_num)
theorem B2044997 : Blo 1076618 2044997 := bbase (se 4 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 2044997 = 383437) (by norm_num)
theorem B1619021 : Blo 1076618 1619021 := bbase (se 3 (by rfl) ⟨303566, by rfl⟩ : syracuseStep 1619021 = 607133) (by norm_num)
theorem B1619045 : Blo 1076618 1619045 := bbase (se 4 (by rfl) ⟨151785, by rfl⟩ : syracuseStep 1619045 = 303571) (by norm_num)
theorem B2733173 : Blo 1076618 2733173 := bbase (se 5 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 2733173 = 256235) (by norm_num)
theorem B1619069 : Blo 1076618 1619069 := bbase (se 3 (by rfl) ⟨303575, by rfl⟩ : syracuseStep 1619069 = 607151) (by norm_num)
theorem B2765957 : Blo 1076618 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B1094797 : Blo 1076618 1094797 := bbase (se 3 (by rfl) ⟨205274, by rfl⟩ : syracuseStep 1094797 = 410549) (by norm_num)
theorem B1619093 : Blo 1076618 1619093 := bbase (se 6 (by rfl) ⟨37947, by rfl⟩ : syracuseStep 1619093 = 75895) (by norm_num)
theorem B1619117 : Blo 1076618 1619117 := bbase (se 3 (by rfl) ⟨303584, by rfl⟩ : syracuseStep 1619117 = 607169) (by norm_num)
theorem B1094833 : Blo 1076618 1094833 := bbase (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) (by norm_num)
theorem B1619141 : Blo 1076618 1619141 := bbase (se 4 (by rfl) ⟨151794, by rfl⟩ : syracuseStep 1619141 = 303589) (by norm_num)
theorem B1619165 : Blo 1076618 1619165 := bbase (se 3 (by rfl) ⟨303593, by rfl⟩ : syracuseStep 1619165 = 607187) (by norm_num)
theorem B1619189 : Blo 1076618 1619189 := bbase (se 5 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 1619189 = 151799) (by norm_num)
theorem B1619213 : Blo 1076618 1619213 := bbase (se 3 (by rfl) ⟨303602, by rfl⟩ : syracuseStep 1619213 = 607205) (by norm_num)
theorem B1619237 : Blo 1076618 1619237 := bbase (se 4 (by rfl) ⟨151803, by rfl⟩ : syracuseStep 1619237 = 303607) (by norm_num)
theorem B2733365 : Blo 1076618 2733365 := bbase (se 5 (by rfl) ⟨128126, by rfl⟩ : syracuseStep 2733365 = 256253) (by norm_num)
theorem B1619261 : Blo 1076618 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B1619285 : Blo 1076618 1619285 := bbase (se 13 (by rfl) ⟨296, by rfl⟩ : syracuseStep 1619285 = 593) (by norm_num)
theorem B1619309 : Blo 1076618 1619309 := bbase (se 3 (by rfl) ⟨303620, by rfl⟩ : syracuseStep 1619309 = 607241) (by norm_num)
theorem B1619333 : Blo 1076618 1619333 := bbase (se 4 (by rfl) ⟨151812, by rfl⟩ : syracuseStep 1619333 = 303625) (by norm_num)
theorem B1455517 : Blo 1076618 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B1619357 : Blo 1076618 1619357 := bbase (se 3 (by rfl) ⟨303629, by rfl⟩ : syracuseStep 1619357 = 607259) (by norm_num)
theorem B1619381 : Blo 1076618 1619381 := bbase (se 5 (by rfl) ⟨75908, by rfl⟩ : syracuseStep 1619381 = 151817) (by norm_num)
theorem B1619405 : Blo 1076618 1619405 := bbase (se 3 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 1619405 = 607277) (by norm_num)
theorem B1095125 : Blo 1076618 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B1619429 : Blo 1076618 1619429 := bbase (se 4 (by rfl) ⟨151821, by rfl⟩ : syracuseStep 1619429 = 303643) (by norm_num)
theorem B1619453 : Blo 1076618 1619453 := bbase (se 3 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 1619453 = 607295) (by norm_num)
theorem B1619477 : Blo 1076618 1619477 := bbase (se 6 (by rfl) ⟨37956, by rfl⟩ : syracuseStep 1619477 = 75913) (by norm_num)
theorem B1619501 : Blo 1076618 1619501 := bbase (se 3 (by rfl) ⟨303656, by rfl⟩ : syracuseStep 1619501 = 607313) (by norm_num)
theorem B1619525 : Blo 1076618 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B1619549 : Blo 1076618 1619549 := bbase (se 3 (by rfl) ⟨303665, by rfl⟩ : syracuseStep 1619549 = 607331) (by norm_num)
theorem B1619573 : Blo 1076618 1619573 := bbase (se 5 (by rfl) ⟨75917, by rfl⟩ : syracuseStep 1619573 = 151835) (by norm_num)
theorem B1619597 : Blo 1076618 1619597 := bbase (se 3 (by rfl) ⟨303674, by rfl⟩ : syracuseStep 1619597 = 607349) (by norm_num)
theorem B2733709 : Blo 1076618 2733709 := bbase (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) (by norm_num)
theorem B1619621 : Blo 1076618 1619621 := bbase (se 4 (by rfl) ⟨151839, by rfl⟩ : syracuseStep 1619621 = 303679) (by norm_num)
theorem B1619645 : Blo 1076618 1619645 := bbase (se 3 (by rfl) ⟨303683, by rfl⟩ : syracuseStep 1619645 = 607367) (by norm_num)
theorem B2307781 : Blo 1076618 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B1619669 : Blo 1076618 1619669 := bbase (se 7 (by rfl) ⟨18980, by rfl⟩ : syracuseStep 1619669 = 37961) (by norm_num)
theorem B1619693 : Blo 1076618 1619693 := bbase (se 3 (by rfl) ⟨303692, by rfl⟩ : syracuseStep 1619693 = 607385) (by norm_num)
theorem B2733821 : Blo 1076618 2733821 := bbase (se 3 (by rfl) ⟨512591, by rfl⟩ : syracuseStep 2733821 = 1025183) (by norm_num)
theorem B1619717 : Blo 1076618 1619717 := bbase (se 4 (by rfl) ⟨151848, by rfl⟩ : syracuseStep 1619717 = 303697) (by norm_num)
theorem B1619741 : Blo 1076618 1619741 := bbase (se 3 (by rfl) ⟨303701, by rfl⟩ : syracuseStep 1619741 = 607403) (by norm_num)
theorem B2045749 : Blo 1076618 2045749 := bbase (se 5 (by rfl) ⟨95894, by rfl⟩ : syracuseStep 2045749 = 191789) (by norm_num)
theorem B1619765 : Blo 1076618 1619765 := bbase (se 5 (by rfl) ⟨75926, by rfl⟩ : syracuseStep 1619765 = 151853) (by norm_num)
theorem B1619789 : Blo 1076618 1619789 := bbase (se 3 (by rfl) ⟨303710, by rfl⟩ : syracuseStep 1619789 = 607421) (by norm_num)
theorem B4372309 : Blo 1076618 4372309 := bbase (se 9 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 4372309 = 25619) (by norm_num)
theorem B1619813 : Blo 1076618 1619813 := bbase (se 4 (by rfl) ⟨151857, by rfl⟩ : syracuseStep 1619813 = 303715) (by norm_num)
theorem B1619837 : Blo 1076618 1619837 := bbase (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) (by norm_num)
theorem B1619861 : Blo 1076618 1619861 := bbase (se 6 (by rfl) ⟨37965, by rfl⟩ : syracuseStep 1619861 = 75931) (by norm_num)
theorem B1619885 : Blo 1076618 1619885 := bbase (se 3 (by rfl) ⟨303728, by rfl⟩ : syracuseStep 1619885 = 607457) (by norm_num)
theorem B2734013 : Blo 1076618 2734013 := bbase (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) (by norm_num)
theorem B2045893 : Blo 1076618 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B1619909 : Blo 1076618 1619909 := bbase (se 4 (by rfl) ⟨151866, by rfl⟩ : syracuseStep 1619909 = 303733) (by norm_num)
theorem B1619933 : Blo 1076618 1619933 := bbase (se 3 (by rfl) ⟨303737, by rfl⟩ : syracuseStep 1619933 = 607475) (by norm_num)
theorem B1619957 : Blo 1076618 1619957 := bbase (se 5 (by rfl) ⟨75935, by rfl⟩ : syracuseStep 1619957 = 151871) (by norm_num)
theorem B1619981 : Blo 1076618 1619981 := bbase (se 3 (by rfl) ⟨303746, by rfl⟩ : syracuseStep 1619981 = 607493) (by norm_num)
theorem B4601893 : Blo 1076618 4601893 := bbase (se 4 (by rfl) ⟨431427, by rfl⟩ : syracuseStep 4601893 = 862855) (by norm_num)
theorem B1620005 : Blo 1076618 1620005 := bbase (se 4 (by rfl) ⟨151875, by rfl⟩ : syracuseStep 1620005 = 303751) (by norm_num)
theorem B1620029 : Blo 1076618 1620029 := bbase (se 3 (by rfl) ⟨303755, by rfl⟩ : syracuseStep 1620029 = 607511) (by norm_num)
theorem B1620053 : Blo 1076618 1620053 := bbase (se 8 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 1620053 = 18985) (by norm_num)
theorem B2046053 : Blo 1076618 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B1620077 : Blo 1076618 1620077 := bbase (se 3 (by rfl) ⟨303764, by rfl⟩ : syracuseStep 1620077 = 607529) (by norm_num)
theorem B1620101 : Blo 1076618 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B1620125 : Blo 1076618 1620125 := bbase (se 3 (by rfl) ⟨303773, by rfl⟩ : syracuseStep 1620125 = 607547) (by norm_num)
theorem B1620149 : Blo 1076618 1620149 := bbase (se 5 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 1620149 = 151889) (by norm_num)
theorem B1620173 : Blo 1076618 1620173 := bbase (se 3 (by rfl) ⟨303782, by rfl⟩ : syracuseStep 1620173 = 607565) (by norm_num)
theorem B5454053 : Blo 1076618 5454053 := bbase (se 4 (by rfl) ⟨511317, by rfl⟩ : syracuseStep 5454053 = 1022635) (by norm_num)
theorem B1620197 : Blo 1076618 1620197 := bbase (se 4 (by rfl) ⟨151893, by rfl⟩ : syracuseStep 1620197 = 303787) (by norm_num)
theorem B2046197 : Blo 1076618 2046197 := bbase (se 5 (by rfl) ⟨95915, by rfl⟩ : syracuseStep 2046197 = 191831) (by norm_num)
theorem B1620221 : Blo 1076618 1620221 := bbase (se 3 (by rfl) ⟨303791, by rfl⟩ : syracuseStep 1620221 = 607583) (by norm_num)
theorem B1620245 : Blo 1076618 1620245 := bbase (se 6 (by rfl) ⟨37974, by rfl⟩ : syracuseStep 1620245 = 75949) (by norm_num)
theorem B2734357 : Blo 1076618 2734357 := bbase (se 6 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 2734357 = 128173) (by norm_num)
theorem B1816877 : Blo 1076618 1816877 := bbase (se 3 (by rfl) ⟨340664, by rfl⟩ : syracuseStep 1816877 = 681329) (by norm_num)
theorem B1620269 : Blo 1076618 1620269 := bbase (se 3 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 1620269 = 607601) (by norm_num)
theorem B1620293 : Blo 1076618 1620293 := bbase (se 4 (by rfl) ⟨151902, by rfl⟩ : syracuseStep 1620293 = 303805) (by norm_num)
theorem B1620317 : Blo 1076618 1620317 := bbase (se 3 (by rfl) ⟨303809, by rfl⟩ : syracuseStep 1620317 = 607619) (by norm_num)
theorem B1620341 : Blo 1076618 1620341 := bbase (se 5 (by rfl) ⟨75953, by rfl⟩ : syracuseStep 1620341 = 151907) (by norm_num)
theorem B2734469 : Blo 1076618 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B1620365 : Blo 1076618 1620365 := bbase (se 3 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 1620365 = 607637) (by norm_num)
theorem B1620389 : Blo 1076618 1620389 := bbase (se 4 (by rfl) ⟨151911, by rfl⟩ : syracuseStep 1620389 = 303823) (by norm_num)
theorem B1817005 : Blo 1076618 1817005 := bbase (se 3 (by rfl) ⟨340688, by rfl⟩ : syracuseStep 1817005 = 681377) (by norm_num)
theorem B1620413 : Blo 1076618 1620413 := bbase (se 3 (by rfl) ⟨303827, by rfl⟩ : syracuseStep 1620413 = 607655) (by norm_num)
theorem B5257685 : Blo 1076618 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1620437 : Blo 1076618 1620437 := bbase (se 7 (by rfl) ⟨18989, by rfl⟩ : syracuseStep 1620437 = 37979) (by norm_num)
theorem B1620461 : Blo 1076618 1620461 := bbase (se 3 (by rfl) ⟨303836, by rfl⟩ : syracuseStep 1620461 = 607673) (by norm_num)
theorem B1817093 : Blo 1076618 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B1620485 : Blo 1076618 1620485 := bbase (se 4 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 1620485 = 303841) (by norm_num)
theorem B2046485 : Blo 1076618 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B1620509 : Blo 1076618 1620509 := bbase (se 3 (by rfl) ⟨303845, by rfl⟩ : syracuseStep 1620509 = 607691) (by norm_num)
theorem B1620533 : Blo 1076618 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2734661 : Blo 1076618 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B1620557 : Blo 1076618 1620557 := bbase (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) (by norm_num)
theorem B4668005 : Blo 1076618 4668005 := bbase (se 4 (by rfl) ⟨437625, by rfl⟩ : syracuseStep 4668005 = 875251) (by norm_num)
theorem B1620581 : Blo 1076618 1620581 := bbase (se 4 (by rfl) ⟨151929, by rfl⟩ : syracuseStep 1620581 = 303859) (by norm_num)
theorem B1620605 : Blo 1076618 1620605 := bbase (se 3 (by rfl) ⟨303863, by rfl⟩ : syracuseStep 1620605 = 607727) (by norm_num)
theorem B1817221 : Blo 1076618 1817221 := bbase (se 4 (by rfl) ⟨170364, by rfl⟩ : syracuseStep 1817221 = 340729) (by norm_num)
theorem B1620629 : Blo 1076618 1620629 := bbase (se 6 (by rfl) ⟨37983, by rfl⟩ : syracuseStep 1620629 = 75967) (by norm_num)
theorem B2079389 : Blo 1076618 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B2046637 : Blo 1076618 2046637 := bbase (se 3 (by rfl) ⟨383744, by rfl⟩ : syracuseStep 2046637 = 767489) (by norm_num)
theorem B1620653 : Blo 1076618 1620653 := bbase (se 3 (by rfl) ⟨303872, by rfl⟩ : syracuseStep 1620653 = 607745) (by norm_num)
theorem B1620677 : Blo 1076618 1620677 := bbase (se 4 (by rfl) ⟨151938, by rfl⟩ : syracuseStep 1620677 = 303877) (by norm_num)
theorem B1817309 : Blo 1076618 1817309 := bbase (se 3 (by rfl) ⟨340745, by rfl⟩ : syracuseStep 1817309 = 681491) (by norm_num)
theorem B1620701 : Blo 1076618 1620701 := bbase (se 3 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 1620701 = 607763) (by norm_num)
theorem B1620725 : Blo 1076618 1620725 := bbase (se 5 (by rfl) ⟨75971, by rfl⟩ : syracuseStep 1620725 = 151943) (by norm_num)
theorem B1620749 : Blo 1076618 1620749 := bbase (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) (by norm_num)
theorem B1620773 : Blo 1076618 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B1620797 : Blo 1076618 1620797 := bbase (se 3 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 1620797 = 607799) (by norm_num)
theorem B1620821 : Blo 1076618 1620821 := bbase (se 9 (by rfl) ⟨4748, by rfl⟩ : syracuseStep 1620821 = 9497) (by norm_num)
theorem B1817437 : Blo 1076618 1817437 := bbase (se 3 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 1817437 = 681539) (by norm_num)
theorem B1620845 : Blo 1076618 1620845 := bbase (se 3 (by rfl) ⟨303908, by rfl⟩ : syracuseStep 1620845 = 607817) (by norm_num)
theorem B1620869 : Blo 1076618 1620869 := bbase (se 4 (by rfl) ⟨151956, by rfl⟩ : syracuseStep 1620869 = 303913) (by norm_num)
theorem B2735005 : Blo 1076618 2735005 := bbase (se 3 (by rfl) ⟨512813, by rfl⟩ : syracuseStep 2735005 = 1025627) (by norm_num)
theorem B1620893 : Blo 1076618 1620893 := bbase (se 3 (by rfl) ⟨303917, by rfl⟩ : syracuseStep 1620893 = 607835) (by norm_num)
theorem B1817525 : Blo 1076618 1817525 := bbase (se 5 (by rfl) ⟨85196, by rfl⟩ : syracuseStep 1817525 = 170393) (by norm_num)
theorem B1620917 : Blo 1076618 1620917 := bbase (se 5 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 1620917 = 151961) (by norm_num)
theorem B2046941 : Blo 1076618 2046941 := bbase (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) (by norm_num)
theorem B2735117 : Blo 1076618 2735117 := bbase (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) (by norm_num)
theorem B1817653 : Blo 1076618 1817653 := bbase (se 5 (by rfl) ⟨85202, by rfl⟩ : syracuseStep 1817653 = 170405) (by norm_num)
theorem B1817741 : Blo 1076618 1817741 := bbase (se 3 (by rfl) ⟨340826, by rfl⟩ : syracuseStep 1817741 = 681653) (by norm_num)
theorem B2735309 : Blo 1076618 2735309 := bbase (se 3 (by rfl) ⟨512870, by rfl⟩ : syracuseStep 2735309 = 1025741) (by norm_num)
theorem B1293581 : Blo 1076618 1293581 := bbase (se 3 (by rfl) ⟨242546, by rfl⟩ : syracuseStep 1293581 = 485093) (by norm_num)
theorem B1817869 : Blo 1076618 1817869 := bbase (se 3 (by rfl) ⟨340850, by rfl⟩ : syracuseStep 1817869 = 681701) (by norm_num)
theorem B3456341 : Blo 1076618 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B1817957 : Blo 1076618 1817957 := bbase (se 4 (by rfl) ⟨170433, by rfl⟩ : syracuseStep 1817957 = 340867) (by norm_num)
theorem B1293745 : Blo 1076618 1293745 := bbase (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) (by norm_num)
theorem B1293773 : Blo 1076618 1293773 := bbase (se 3 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 1293773 = 485165) (by norm_num)
theorem B4144613 : Blo 1076618 4144613 := bbase (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) (by norm_num)
theorem B1818085 : Blo 1076618 1818085 := bbase (se 4 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 1818085 = 340891) (by norm_num)
theorem B5455349 : Blo 1076618 5455349 := bbase (se 5 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 5455349 = 511439) (by norm_num)
theorem B1555957 : Blo 1076618 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1818173 : Blo 1076618 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B1293889 : Blo 1076618 1293889 := bbase (se 2 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 1293889 = 970417) (by norm_num)
theorem B1293985 : Blo 1076618 1293985 := bbase (se 2 (by rfl) ⟨485244, by rfl⟩ : syracuseStep 1293985 = 970489) (by norm_num)
theorem B1818301 : Blo 1076618 1818301 := bbase (se 3 (by rfl) ⟨340931, by rfl⟩ : syracuseStep 1818301 = 681863) (by norm_num)
theorem B2047693 : Blo 1076618 2047693 := bbase (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) (by norm_num)
theorem B1556221 : Blo 1076618 1556221 := bbase (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) (by norm_num)
theorem B1818389 : Blo 1076618 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B2047837 : Blo 1076618 2047837 := bbase (se 3 (by rfl) ⟨383969, by rfl⟩ : syracuseStep 2047837 = 767939) (by norm_num)
theorem B1818517 : Blo 1076618 1818517 := bbase (se 6 (by rfl) ⟨42621, by rfl⟩ : syracuseStep 1818517 = 85243) (by norm_num)
theorem B1818605 : Blo 1076618 1818605 := bbase (se 3 (by rfl) ⟨340988, by rfl⟩ : syracuseStep 1818605 = 681977) (by norm_num)
theorem B2047997 : Blo 1076618 2047997 := bbase (se 3 (by rfl) ⟨383999, by rfl⟩ : syracuseStep 2047997 = 767999) (by norm_num)
theorem B1818733 : Blo 1076618 1818733 := bbase (se 3 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 1818733 = 682025) (by norm_num)
theorem B1294465 : Blo 1076618 1294465 := bbase (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) (by norm_num)
theorem B2048141 : Blo 1076618 2048141 := bbase (se 3 (by rfl) ⟨384026, by rfl⟩ : syracuseStep 2048141 = 768053) (by norm_num)
theorem B1818821 : Blo 1076618 1818821 := bbase (se 4 (by rfl) ⟨170514, by rfl⟩ : syracuseStep 1818821 = 341029) (by norm_num)
theorem B3457237 : Blo 1076618 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B1818949 : Blo 1076618 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B1819037 : Blo 1076618 1819037 := bbase (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) (by norm_num)
theorem B2048429 : Blo 1076618 2048429 := bbase (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) (by norm_num)
theorem B1229261 : Blo 1076618 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B1819165 : Blo 1076618 1819165 := bbase (se 3 (by rfl) ⟨341093, by rfl⟩ : syracuseStep 1819165 = 682187) (by norm_num)
theorem B2048581 : Blo 1076618 2048581 := bbase (se 4 (by rfl) ⟨192054, by rfl⟩ : syracuseStep 2048581 = 384109) (by norm_num)
theorem B3457637 : Blo 1076618 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B1819253 : Blo 1076618 1819253 := bbase (se 5 (by rfl) ⟨85277, by rfl⟩ : syracuseStep 1819253 = 170555) (by norm_num)
theorem B1819381 : Blo 1076618 1819381 := bbase (se 5 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 1819381 = 170567) (by norm_num)
theorem B5456645 : Blo 1076618 5456645 := bbase (se 4 (by rfl) ⟨511560, by rfl⟩ : syracuseStep 5456645 = 1023121) (by norm_num)
theorem B1819469 : Blo 1076618 1819469 := bbase (se 3 (by rfl) ⟨341150, by rfl⟩ : syracuseStep 1819469 = 682301) (by norm_num)
theorem B2048885 : Blo 1076618 2048885 := bbase (se 5 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 2048885 = 192083) (by norm_num)
theorem B1819597 : Blo 1076618 1819597 := bbase (se 3 (by rfl) ⟨341174, by rfl⟩ : syracuseStep 1819597 = 682349) (by norm_num)
theorem B1819685 : Blo 1076618 1819685 := bbase (se 4 (by rfl) ⟨170595, by rfl⟩ : syracuseStep 1819685 = 341191) (by norm_num)
theorem B1459253 : Blo 1076618 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B1819813 : Blo 1076618 1819813 := bbase (se 4 (by rfl) ⟨170607, by rfl⟩ : syracuseStep 1819813 = 341215) (by norm_num)
theorem B3687605 : Blo 1076618 3687605 := bbase (se 5 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 3687605 = 345713) (by norm_num)
theorem B1819901 : Blo 1076618 1819901 := bbase (se 3 (by rfl) ⟨341231, by rfl⟩ : syracuseStep 1819901 = 682463) (by norm_num)
theorem B1459453 : Blo 1076618 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B8176949 : Blo 1076618 8176949 := bbase (se 5 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 8176949 = 766589) (by norm_num)
theorem B2770229 : Blo 1076618 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B6571381 : Blo 1076618 6571381 := bbase (se 5 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 6571381 = 616067) (by norm_num)
theorem B1820029 : Blo 1076618 1820029 := bbase (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) (by norm_num)
theorem B1820117 : Blo 1076618 1820117 := bbase (se 7 (by rfl) ⟨21329, by rfl⟩ : syracuseStep 1820117 = 42659) (by norm_num)
theorem B1459669 : Blo 1076618 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B1295849 : Blo 1076618 1295849 := bbase (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) (by norm_num)
theorem B1459733 : Blo 1076618 1459733 := bbase (se 6 (by rfl) ⟨34212, by rfl⟩ : syracuseStep 1459733 = 68425) (by norm_num)
theorem B1230373 : Blo 1076618 1230373 := bbase (se 4 (by rfl) ⟨115347, by rfl⟩ : syracuseStep 1230373 = 230695) (by norm_num)
theorem B1820245 : Blo 1076618 1820245 := bbase (se 8 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 1820245 = 21331) (by norm_num)
theorem B2049637 : Blo 1076618 2049637 := bbase (se 4 (by rfl) ⟨192153, by rfl⟩ : syracuseStep 2049637 = 384307) (by norm_num)
theorem B1296037 : Blo 1076618 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1820333 : Blo 1076618 1820333 := bbase (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) (by norm_num)
theorem B2049781 : Blo 1076618 2049781 := bbase (se 5 (by rfl) ⟨96083, by rfl⟩ : syracuseStep 2049781 = 192167) (by norm_num)
theorem B1820461 : Blo 1076618 1820461 := bbase (se 3 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 1820461 = 682673) (by norm_num)
theorem B1296253 : Blo 1076618 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B1820549 : Blo 1076618 1820549 := bbase (se 4 (by rfl) ⟨170676, by rfl⟩ : syracuseStep 1820549 = 341353) (by norm_num)
theorem B2049941 : Blo 1076618 2049941 := bbase (se 6 (by rfl) ⟨48045, by rfl⟩ : syracuseStep 2049941 = 96091) (by norm_num)
theorem B9226133 : Blo 1076618 9226133 := bbase (se 6 (by rfl) ⟨216237, by rfl⟩ : syracuseStep 9226133 = 432475) (by norm_num)
theorem B1820677 : Blo 1076618 1820677 := bbase (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) (by norm_num)
theorem B5457941 : Blo 1076618 5457941 := bbase (se 6 (by rfl) ⟨127920, by rfl⟩ : syracuseStep 5457941 = 255841) (by norm_num)
theorem B2050085 : Blo 1076618 2050085 := bbase (se 4 (by rfl) ⟨192195, by rfl⟩ : syracuseStep 2050085 = 384391) (by norm_num)
theorem B1820765 : Blo 1076618 1820765 := bbase (se 3 (by rfl) ⟨341393, by rfl⟩ : syracuseStep 1820765 = 682787) (by norm_num)
theorem B1296541 : Blo 1076618 1296541 := bbase (se 3 (by rfl) ⟨243101, by rfl⟩ : syracuseStep 1296541 = 486203) (by norm_num)
theorem B1820893 : Blo 1076618 1820893 := bbase (se 3 (by rfl) ⟨341417, by rfl⟩ : syracuseStep 1820893 = 682835) (by norm_num)
theorem B1820981 : Blo 1076618 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B2050373 : Blo 1076618 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B31476053 : Blo 1076618 31476053 := bbase (se 10 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 31476053 = 92215) (by norm_num)
theorem B20695445 : Blo 1076618 20695445 := bbase (se 6 (by rfl) ⟨485049, by rfl⟩ : syracuseStep 20695445 = 970099) (by norm_num)
theorem B1821109 : Blo 1076618 1821109 := bbase (se 5 (by rfl) ⟨85364, by rfl⟩ : syracuseStep 1821109 = 170729) (by norm_num)
theorem B2050525 : Blo 1076618 2050525 := bbase (se 3 (by rfl) ⟨384473, by rfl⟩ : syracuseStep 2050525 = 768947) (by norm_num)
theorem B1821197 : Blo 1076618 1821197 := bbase (se 3 (by rfl) ⟨341474, by rfl⟩ : syracuseStep 1821197 = 682949) (by norm_num)
theorem B3066437 : Blo 1076618 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B1821325 : Blo 1076618 1821325 := bbase (se 3 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 1821325 = 682997) (by norm_num)
theorem B1231537 : Blo 1076618 1231537 := bbase (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) (by norm_num)
theorem B1821413 : Blo 1076618 1821413 := bbase (se 4 (by rfl) ⟨170757, by rfl⟩ : syracuseStep 1821413 = 341515) (by norm_num)
theorem B1362673 : Blo 1076618 1362673 := bbase (se 2 (by rfl) ⟨511002, by rfl⟩ : syracuseStep 1362673 = 1022005) (by norm_num)
theorem B2050829 : Blo 1076618 2050829 := bbase (se 3 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 2050829 = 769061) (by norm_num)
theorem B13814549 : Blo 1076618 13814549 := bbase (se 6 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 13814549 = 647557) (by norm_num)
theorem B6146837 : Blo 1076618 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1821541 : Blo 1076618 1821541 := bbase (se 4 (by rfl) ⟨170769, by rfl⟩ : syracuseStep 1821541 = 341539) (by norm_num)
theorem B1362845 : Blo 1076618 1362845 := bbase (se 3 (by rfl) ⟨255533, by rfl⟩ : syracuseStep 1362845 = 511067) (by norm_num)
theorem B2771869 : Blo 1076618 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B4606901 : Blo 1076618 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B1821629 : Blo 1076618 1821629 := bbase (se 3 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 1821629 = 683111) (by norm_num)
theorem B1362901 : Blo 1076618 1362901 := bbase (se 7 (by rfl) ⟨15971, by rfl⟩ : syracuseStep 1362901 = 31943) (by norm_num)
theorem B1362997 : Blo 1076618 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B1821757 : Blo 1076618 1821757 := bbase (se 3 (by rfl) ⟨341579, by rfl⟩ : syracuseStep 1821757 = 683159) (by norm_num)
theorem B4148309 : Blo 1076618 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B1821845 : Blo 1076618 1821845 := bbase (se 6 (by rfl) ⟨42699, by rfl⟩ : syracuseStep 1821845 = 85399) (by norm_num)
theorem B8735957 : Blo 1076618 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B12274901 : Blo 1076618 12274901 := bbase (se 7 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 12274901 = 287693) (by norm_num)
theorem B4607189 : Blo 1076618 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B1363169 : Blo 1076618 1363169 := bbase (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) (by norm_num)
theorem B3067109 : Blo 1076618 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B1821973 : Blo 1076618 1821973 := bbase (se 6 (by rfl) ⟨42702, by rfl⟩ : syracuseStep 1821973 = 85405) (by norm_num)
theorem B1363225 : Blo 1076618 1363225 := bbase (se 2 (by rfl) ⟨511209, by rfl⟩ : syracuseStep 1363225 = 1022419) (by norm_num)
theorem B1232161 : Blo 1076618 1232161 := bbase (se 2 (by rfl) ⟨462060, by rfl⟩ : syracuseStep 1232161 = 924121) (by norm_num)
theorem B5459237 : Blo 1076618 5459237 := bbase (se 4 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 5459237 = 1023607) (by norm_num)
theorem B2805101 : Blo 1076618 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B1822061 : Blo 1076618 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B1363321 : Blo 1076618 1363321 := bbase (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) (by norm_num)
theorem B1297829 : Blo 1076618 1297829 := bbase (se 4 (by rfl) ⟨121671, by rfl⟩ : syracuseStep 1297829 = 243343) (by norm_num)
theorem B2248157 : Blo 1076618 2248157 := bbase (se 3 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 2248157 = 843059) (by norm_num)
theorem B1822189 : Blo 1076618 1822189 := bbase (se 3 (by rfl) ⟨341660, by rfl⟩ : syracuseStep 1822189 = 683321) (by norm_num)
theorem B1363493 : Blo 1076618 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B1822277 : Blo 1076618 1822277 := bbase (se 4 (by rfl) ⟨170838, by rfl⟩ : syracuseStep 1822277 = 341677) (by norm_num)
theorem B1363549 : Blo 1076618 1363549 := bbase (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) (by norm_num)
theorem B3067541 : Blo 1076618 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B7786165 : Blo 1076618 7786165 := bbase (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) (by norm_num)
theorem B1363645 : Blo 1076618 1363645 := bbase (se 3 (by rfl) ⟨255683, by rfl⟩ : syracuseStep 1363645 = 511367) (by norm_num)
theorem B2182853 : Blo 1076618 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B1822405 : Blo 1076618 1822405 := bbase (se 4 (by rfl) ⟨170850, by rfl⟩ : syracuseStep 1822405 = 341701) (by norm_num)
theorem B1822493 : Blo 1076618 1822493 := bbase (se 3 (by rfl) ⟨341717, by rfl⟩ : syracuseStep 1822493 = 683435) (by norm_num)
theorem B1363817 : Blo 1076618 1363817 := bbase (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) (by norm_num)
theorem B1822621 : Blo 1076618 1822621 := bbase (se 3 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 1822621 = 683483) (by norm_num)
theorem B1363873 : Blo 1076618 1363873 := bbase (se 2 (by rfl) ⟨511452, by rfl⟩ : syracuseStep 1363873 = 1022905) (by norm_num)
theorem B2215853 : Blo 1076618 2215853 := bbase (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) (by norm_num)
theorem B6148021 : Blo 1076618 6148021 := bbase (se 5 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 6148021 = 576377) (by norm_num)
theorem B4607941 : Blo 1076618 4607941 := bbase (se 4 (by rfl) ⟨431994, by rfl⟩ : syracuseStep 4607941 = 863989) (by norm_num)
theorem B1822709 : Blo 1076618 1822709 := bbase (se 5 (by rfl) ⟨85439, by rfl⟩ : syracuseStep 1822709 = 170879) (by norm_num)
theorem B1363969 : Blo 1076618 1363969 := bbase (se 2 (by rfl) ⟨511488, by rfl⟩ : syracuseStep 1363969 = 1022977) (by norm_num)
theorem B1822837 : Blo 1076618 1822837 := bbase (se 5 (by rfl) ⟨85445, by rfl⟩ : syracuseStep 1822837 = 170891) (by norm_num)
theorem B1364141 : Blo 1076618 1364141 := bbase (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) (by norm_num)
theorem B1822925 : Blo 1076618 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B1364197 : Blo 1076618 1364197 := bbase (se 4 (by rfl) ⟨127893, by rfl⟩ : syracuseStep 1364197 = 255787) (by norm_num)
theorem B12144917 : Blo 1076618 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B3461429 : Blo 1076618 3461429 := bbase (se 5 (by rfl) ⟨162254, by rfl⟩ : syracuseStep 3461429 = 324509) (by norm_num)
theorem B1364293 : Blo 1076618 1364293 := bbase (se 4 (by rfl) ⟨127902, by rfl⟩ : syracuseStep 1364293 = 255805) (by norm_num)
theorem B1823053 : Blo 1076618 1823053 := bbase (se 3 (by rfl) ⟨341822, by rfl⟩ : syracuseStep 1823053 = 683645) (by norm_num)
theorem B3887461 : Blo 1076618 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B3068293 : Blo 1076618 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B1823141 : Blo 1076618 1823141 := bbase (se 4 (by rfl) ⟨170919, by rfl⟩ : syracuseStep 1823141 = 341839) (by norm_num)
theorem B1266121 : Blo 1076618 1266121 := bbase (se 2 (by rfl) ⟨474795, by rfl⟩ : syracuseStep 1266121 = 949591) (by norm_num)
theorem B1364465 : Blo 1076618 1364465 := bbase (se 2 (by rfl) ⟨511674, by rfl⟩ : syracuseStep 1364465 = 1023349) (by norm_num)
theorem B1823269 : Blo 1076618 1823269 := bbase (se 4 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 1823269 = 341863) (by norm_num)
theorem B1364521 : Blo 1076618 1364521 := bbase (se 2 (by rfl) ⟨511695, by rfl⟩ : syracuseStep 1364521 = 1023391) (by norm_num)
theorem B5460533 : Blo 1076618 5460533 := bbase (se 5 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 5460533 = 511925) (by norm_num)
theorem B1823357 : Blo 1076618 1823357 := bbase (se 3 (by rfl) ⟨341879, by rfl⟩ : syracuseStep 1823357 = 683759) (by norm_num)
theorem B1364617 : Blo 1076618 1364617 := bbase (se 2 (by rfl) ⟨511731, by rfl⟩ : syracuseStep 1364617 = 1023463) (by norm_num)
theorem B4608677 : Blo 1076618 4608677 := bbase (se 4 (by rfl) ⟨432063, by rfl⟩ : syracuseStep 4608677 = 864127) (by norm_num)
theorem B1823485 : Blo 1076618 1823485 := bbase (se 3 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 1823485 = 683807) (by norm_num)
theorem B1364789 : Blo 1076618 1364789 := bbase (se 5 (by rfl) ⟨63974, by rfl⟩ : syracuseStep 1364789 = 127949) (by norm_num)
theorem B1364845 : Blo 1076618 1364845 := bbase (se 3 (by rfl) ⟨255908, by rfl⟩ : syracuseStep 1364845 = 511817) (by norm_num)
theorem B1364941 : Blo 1076618 1364941 := bbase (se 3 (by rfl) ⟨255926, by rfl⟩ : syracuseStep 1364941 = 511853) (by norm_num)
theorem B1365113 : Blo 1076618 1365113 := bbase (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) (by norm_num)
theorem B1365169 : Blo 1076618 1365169 := bbase (se 2 (by rfl) ⟨511938, by rfl⟩ : syracuseStep 1365169 = 1023877) (by norm_num)
theorem B1365265 : Blo 1076618 1365265 := bbase (se 2 (by rfl) ⟨511974, by rfl⟩ : syracuseStep 1365265 = 1023949) (by norm_num)
theorem B2184509 : Blo 1076618 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B3888469 : Blo 1076618 3888469 := bbase (se 17 (by rfl) ⟨44, by rfl⟩ : syracuseStep 3888469 = 89) (by norm_num)
theorem B1725877 : Blo 1076618 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B1365437 : Blo 1076618 1365437 := bbase (se 3 (by rfl) ⟨256019, by rfl⟩ : syracuseStep 1365437 = 512039) (by norm_num)
theorem B2053565 : Blo 1076618 2053565 := bbase (se 3 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 2053565 = 770087) (by norm_num)
theorem B1365493 : Blo 1076618 1365493 := bbase (se 5 (by rfl) ⟨64007, by rfl⟩ : syracuseStep 1365493 = 128015) (by norm_num)
theorem B1365589 : Blo 1076618 1365589 := bbase (se 8 (by rfl) ⟨8001, by rfl⟩ : syracuseStep 1365589 = 16003) (by norm_num)
theorem B1365761 : Blo 1076618 1365761 := bbase (se 2 (by rfl) ⟨512160, by rfl⟩ : syracuseStep 1365761 = 1024321) (by norm_num)
theorem B1365817 : Blo 1076618 1365817 := bbase (se 2 (by rfl) ⟨512181, by rfl⟩ : syracuseStep 1365817 = 1024363) (by norm_num)
theorem B5461829 : Blo 1076618 5461829 := bbase (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) (by norm_num)
theorem B6150005 : Blo 1076618 6150005 := bbase (se 5 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 6150005 = 576563) (by norm_num)
theorem B4151189 : Blo 1076618 4151189 := bbase (se 6 (by rfl) ⟨97293, by rfl⟩ : syracuseStep 4151189 = 194587) (by norm_num)
theorem B1365913 : Blo 1076618 1365913 := bbase (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) (by norm_num)
theorem B2185157 : Blo 1076618 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B2807765 : Blo 1076618 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B1366085 : Blo 1076618 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B1366141 : Blo 1076618 1366141 := bbase (se 3 (by rfl) ⟨256151, by rfl⟩ : syracuseStep 1366141 = 512303) (by norm_num)
theorem B1366237 : Blo 1076618 1366237 := bbase (se 3 (by rfl) ⟨256169, by rfl⟩ : syracuseStep 1366237 = 512339) (by norm_num)
theorem B10377557 : Blo 1076618 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B1366409 : Blo 1076618 1366409 := bbase (se 2 (by rfl) ⟨512403, by rfl⟩ : syracuseStep 1366409 = 1024807) (by norm_num)
theorem B5527973 : Blo 1076618 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B6642101 : Blo 1076618 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B1366465 : Blo 1076618 1366465 := bbase (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) (by norm_num)
theorem B6904277 : Blo 1076618 6904277 := bbase (se 7 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 6904277 = 161819) (by norm_num)
theorem B1366561 : Blo 1076618 1366561 := bbase (se 2 (by rfl) ⟨512460, by rfl⟩ : syracuseStep 1366561 = 1024921) (by norm_num)
theorem B1366733 : Blo 1076618 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B1366789 : Blo 1076618 1366789 := bbase (se 4 (by rfl) ⟨128136, by rfl⟩ : syracuseStep 1366789 = 256273) (by norm_num)
theorem B1727261 : Blo 1076618 1727261 := bbase (se 3 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 1727261 = 647723) (by norm_num)
theorem B1366885 : Blo 1076618 1366885 := bbase (se 4 (by rfl) ⟨128145, by rfl⟩ : syracuseStep 1366885 = 256291) (by norm_num)
theorem B1727453 : Blo 1076618 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B1367057 : Blo 1076618 1367057 := bbase (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) (by norm_num)
theorem B1367113 : Blo 1076618 1367113 := bbase (se 2 (by rfl) ⟨512667, by rfl⟩ : syracuseStep 1367113 = 1025335) (by norm_num)
theorem B5463125 : Blo 1076618 5463125 := bbase (se 8 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 5463125 = 64021) (by norm_num)
theorem B3071141 : Blo 1076618 3071141 := bbase (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) (by norm_num)
theorem B1367209 : Blo 1076618 1367209 := bbase (se 2 (by rfl) ⟨512703, by rfl⟩ : syracuseStep 1367209 = 1025407) (by norm_num)
theorem B1367381 : Blo 1076618 1367381 := bbase (se 11 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1367381 = 2003) (by norm_num)
theorem B1367437 : Blo 1076618 1367437 := bbase (se 3 (by rfl) ⟨256394, by rfl⟩ : syracuseStep 1367437 = 512789) (by norm_num)
theorem B1367533 : Blo 1076618 1367533 := bbase (se 3 (by rfl) ⟨256412, by rfl⟩ : syracuseStep 1367533 = 512825) (by norm_num)
theorem B2186941 : Blo 1076618 2186941 := bbase (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) (by norm_num)
theorem B4611973 : Blo 1076618 4611973 := bbase (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) (by norm_num)
theorem B26271701 : Blo 1076618 26271701 := bbase (se 7 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 26271701 = 615743) (by norm_num)
theorem B6152213 : Blo 1076618 6152213 := bbase (se 6 (by rfl) ⟨144192, by rfl⟩ : syracuseStep 6152213 = 288385) (by norm_num)
theorem B1728773 : Blo 1076618 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B2187581 : Blo 1076618 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B3072325 : Blo 1076618 3072325 := bbase (se 4 (by rfl) ⟨288030, by rfl⟩ : syracuseStep 3072325 = 576061) (by norm_num)
theorem B1728869 : Blo 1076618 1728869 := bbase (se 4 (by rfl) ⟨162081, by rfl⟩ : syracuseStep 1728869 = 324163) (by norm_num)
theorem B5464421 : Blo 1076618 5464421 := bbase (se 4 (by rfl) ⟨512289, by rfl⟩ : syracuseStep 5464421 = 1024579) (by norm_num)
theorem B1728901 : Blo 1076618 1728901 := bbase (se 4 (by rfl) ⟨162084, by rfl⟩ : syracuseStep 1728901 = 324169) (by norm_num)
theorem B3072485 : Blo 1076618 3072485 := bbase (se 4 (by rfl) ⟨288045, by rfl⟩ : syracuseStep 3072485 = 576091) (by norm_num)
theorem B1401517 : Blo 1076618 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B3072725 : Blo 1076618 3072725 := bbase (se 7 (by rfl) ⟨36008, by rfl⟩ : syracuseStep 3072725 = 72017) (by norm_num)
theorem B2188109 : Blo 1076618 2188109 := bbase (se 3 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 2188109 = 820541) (by norm_num)
theorem B8184725 : Blo 1076618 8184725 := bbase (se 6 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 8184725 = 383659) (by norm_num)
theorem B3072917 : Blo 1076618 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B1533053 : Blo 1076618 1533053 := bbase (se 3 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 1533053 = 574895) (by norm_num)
theorem B2188709 : Blo 1076618 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B5465717 : Blo 1076618 5465717 := bbase (se 5 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 5465717 = 512411) (by norm_num)
theorem B3892853 : Blo 1076618 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B3892997 : Blo 1076618 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B1730413 : Blo 1076618 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B3073909 : Blo 1076618 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B4089797 : Blo 1076618 4089797 := bbase (se 4 (by rfl) ⟨383418, by rfl⟩ : syracuseStep 4089797 = 766837) (by norm_num)
theorem B4090085 : Blo 1076618 4090085 := bbase (se 4 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 4090085 = 766891) (by norm_num)
theorem B1534477 : Blo 1076618 1534477 := bbase (se 3 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 1534477 = 575429) (by norm_num)
theorem B1108661 : Blo 1076618 1108661 := bbase (se 5 (by rfl) ⟨51968, by rfl⟩ : syracuseStep 1108661 = 103937) (by norm_num)
theorem B3894005 : Blo 1076618 3894005 := bbase (se 5 (by rfl) ⟨182531, by rfl⟩ : syracuseStep 3894005 = 365063) (by norm_num)
theorem B4614965 : Blo 1076618 4614965 := bbase (se 5 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 4614965 = 432653) (by norm_num)
theorem B5467013 : Blo 1076618 5467013 := bbase (se 4 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 5467013 = 1025065) (by norm_num)
theorem B3075013 : Blo 1076618 3075013 := bbase (se 4 (by rfl) ⟨288282, by rfl⟩ : syracuseStep 3075013 = 576565) (by norm_num)
theorem B1535069 : Blo 1076618 1535069 := bbase (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) (by norm_num)
theorem B5827733 : Blo 1076618 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B1535149 : Blo 1076618 1535149 := bbase (se 3 (by rfl) ⟨287840, by rfl⟩ : syracuseStep 1535149 = 575681) (by norm_num)
theorem B1535269 : Blo 1076618 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B3108149 : Blo 1076618 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B4091269 : Blo 1076618 4091269 := bbase (se 4 (by rfl) ⟨383556, by rfl⟩ : syracuseStep 4091269 = 767113) (by norm_num)
theorem B1535365 : Blo 1076618 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B4091573 : Blo 1076618 4091573 := bbase (se 5 (by rfl) ⟨191792, by rfl⟩ : syracuseStep 4091573 = 383585) (by norm_num)
theorem B1535861 : Blo 1076618 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B4911205 : Blo 1076618 4911205 := bbase (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) (by norm_num)
theorem B5468309 : Blo 1076618 5468309 := bbase (se 6 (by rfl) ⟨128163, by rfl⟩ : syracuseStep 5468309 = 256327) (by norm_num)
theorem B9203989 : Blo 1076618 9203989 := bbase (se 6 (by rfl) ⟨215718, by rfl⟩ : syracuseStep 9203989 = 431437) (by norm_num)
theorem B1536413 : Blo 1076618 1536413 := bbase (se 3 (by rfl) ⟨288077, by rfl⟩ : syracuseStep 1536413 = 576155) (by norm_num)
theorem B3076517 : Blo 1076618 3076517 := bbase (se 4 (by rfl) ⟨288423, by rfl⟩ : syracuseStep 3076517 = 576847) (by norm_num)
theorem B3633605 : Blo 1076618 3633605 := bbase (se 4 (by rfl) ⟨340650, by rfl⟩ : syracuseStep 3633605 = 681301) (by norm_num)
theorem B11072213 : Blo 1076618 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B3634037 : Blo 1076618 3634037 := bbase (se 5 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 3634037 = 340691) (by norm_num)
theorem B2913317 : Blo 1076618 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B1537165 : Blo 1076618 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B3634469 : Blo 1076618 3634469 := bbase (se 4 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 3634469 = 681463) (by norm_num)
theorem B5469605 : Blo 1076618 5469605 := bbase (se 4 (by rfl) ⟨512775, by rfl⟩ : syracuseStep 5469605 = 1025551) (by norm_num)
theorem B2422421 : Blo 1076618 2422421 := bbase (se 6 (by rfl) ⟨56775, by rfl⟩ : syracuseStep 2422421 = 113551) (by norm_num)
theorem B3634901 : Blo 1076618 3634901 := bbase (se 7 (by rfl) ⟨42596, by rfl⟩ : syracuseStep 3634901 = 85193) (by norm_num)
theorem B39319253 : Blo 1076618 39319253 := bbase (se 7 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 39319253 = 921545) (by norm_num)
theorem B2422493 : Blo 1076618 2422493 := bbase (se 3 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 2422493 = 908435) (by norm_num)
theorem B4093685 : Blo 1076618 4093685 := bbase (se 5 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 4093685 = 383783) (by norm_num)
theorem B2422565 : Blo 1076618 2422565 := bbase (se 4 (by rfl) ⟨227115, by rfl⟩ : syracuseStep 2422565 = 454231) (by norm_num)
theorem B2422637 : Blo 1076618 2422637 := bbase (se 3 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 2422637 = 908489) (by norm_num)
theorem B1537957 : Blo 1076618 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B2422709 : Blo 1076618 2422709 := bbase (se 5 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 2422709 = 227129) (by norm_num)
theorem B2422781 : Blo 1076618 2422781 := bbase (se 3 (by rfl) ⟨454271, by rfl⟩ : syracuseStep 2422781 = 908543) (by norm_num)
theorem B4093973 : Blo 1076618 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B2422853 : Blo 1076618 2422853 := bbase (se 4 (by rfl) ⟨227142, by rfl⟩ : syracuseStep 2422853 = 454285) (by norm_num)
theorem B3635333 : Blo 1076618 3635333 := bbase (se 4 (by rfl) ⟨340812, by rfl⟩ : syracuseStep 3635333 = 681625) (by norm_num)
theorem B2422925 : Blo 1076618 2422925 := bbase (se 3 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 2422925 = 908597) (by norm_num)
theorem B9828533 : Blo 1076618 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B2422997 : Blo 1076618 2422997 := bbase (se 7 (by rfl) ⟨28394, by rfl⟩ : syracuseStep 2422997 = 56789) (by norm_num)
theorem B9205973 : Blo 1076618 9205973 := bbase (se 7 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 9205973 = 215765) (by norm_num)
theorem B1538293 : Blo 1076618 1538293 := bbase (se 5 (by rfl) ⟨72107, by rfl⟩ : syracuseStep 1538293 = 144215) (by norm_num)
theorem B2423069 : Blo 1076618 2423069 := bbase (se 3 (by rfl) ⟨454325, by rfl⟩ : syracuseStep 2423069 = 908651) (by norm_num)
theorem B2423141 : Blo 1076618 2423141 := bbase (se 4 (by rfl) ⟨227169, by rfl⟩ : syracuseStep 2423141 = 454339) (by norm_num)
theorem B2914709 : Blo 1076618 2914709 := bbase (se 6 (by rfl) ⟨68313, by rfl⟩ : syracuseStep 2914709 = 136627) (by norm_num)
theorem B2423213 : Blo 1076618 2423213 := bbase (se 3 (by rfl) ⟨454352, by rfl⟩ : syracuseStep 2423213 = 908705) (by norm_num)
theorem B1538509 : Blo 1076618 1538509 := bbase (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) (by norm_num)
theorem B2423285 : Blo 1076618 2423285 := bbase (se 5 (by rfl) ⟨113591, by rfl⟩ : syracuseStep 2423285 = 227183) (by norm_num)
theorem B5175845 : Blo 1076618 5175845 := bbase (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) (by norm_num)
theorem B3635765 : Blo 1076618 3635765 := bbase (se 5 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 3635765 = 340853) (by norm_num)
theorem B2423357 : Blo 1076618 2423357 := bbase (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) (by norm_num)
theorem B78608981 : Blo 1076618 78608981 := bbase (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) (by norm_num)
theorem B2423429 : Blo 1076618 2423429 := bbase (se 4 (by rfl) ⟨227196, by rfl⟩ : syracuseStep 2423429 = 454393) (by norm_num)
theorem B2423501 : Blo 1076618 2423501 := bbase (se 3 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 2423501 = 908813) (by norm_num)
theorem B2423573 : Blo 1076618 2423573 := bbase (se 6 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 2423573 = 113605) (by norm_num)
theorem B1211197 : Blo 1076618 1211197 := bbase (se 3 (by rfl) ⟨227099, by rfl⟩ : syracuseStep 1211197 = 454199) (by norm_num)
theorem B2587469 : Blo 1076618 2587469 := bbase (se 3 (by rfl) ⟨485150, by rfl⟩ : syracuseStep 2587469 = 970301) (by norm_num)
theorem B2423645 : Blo 1076618 2423645 := bbase (se 3 (by rfl) ⟨454433, by rfl⟩ : syracuseStep 2423645 = 908867) (by norm_num)
theorem B1211233 : Blo 1076618 1211233 := bbase (se 2 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 1211233 = 908425) (by norm_num)
theorem B1211269 : Blo 1076618 1211269 := bbase (se 4 (by rfl) ⟨113556, by rfl⟩ : syracuseStep 1211269 = 227113) (by norm_num)
theorem B2423717 : Blo 1076618 2423717 := bbase (se 4 (by rfl) ⟨227223, by rfl⟩ : syracuseStep 2423717 = 454447) (by norm_num)
theorem B1211305 : Blo 1076618 1211305 := bbase (se 2 (by rfl) ⟨454239, by rfl⟩ : syracuseStep 1211305 = 908479) (by norm_num)
theorem B1211341 : Blo 1076618 1211341 := bbase (se 3 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 1211341 = 454253) (by norm_num)
theorem B3636197 : Blo 1076618 3636197 := bbase (se 4 (by rfl) ⟨340893, by rfl⟩ : syracuseStep 3636197 = 681787) (by norm_num)
theorem B2423789 : Blo 1076618 2423789 := bbase (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) (by norm_num)
theorem B1211377 : Blo 1076618 1211377 := bbase (se 2 (by rfl) ⟨454266, by rfl⟩ : syracuseStep 1211377 = 908533) (by norm_num)
theorem B1211413 : Blo 1076618 1211413 := bbase (se 6 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 1211413 = 56785) (by norm_num)
theorem B3505189 : Blo 1076618 3505189 := bbase (se 4 (by rfl) ⟨328611, by rfl⟩ : syracuseStep 3505189 = 657223) (by norm_num)
theorem B2423861 : Blo 1076618 2423861 := bbase (se 5 (by rfl) ⟨113618, by rfl⟩ : syracuseStep 2423861 = 227237) (by norm_num)
theorem B1211449 : Blo 1076618 1211449 := bbase (se 2 (by rfl) ⟨454293, by rfl⟩ : syracuseStep 1211449 = 908587) (by norm_num)
theorem B1211485 : Blo 1076618 1211485 := bbase (se 3 (by rfl) ⟨227153, by rfl⟩ : syracuseStep 1211485 = 454307) (by norm_num)
theorem B2423933 : Blo 1076618 2423933 := bbase (se 3 (by rfl) ⟨454487, by rfl⟩ : syracuseStep 2423933 = 908975) (by norm_num)
theorem B1211521 : Blo 1076618 1211521 := bbase (se 2 (by rfl) ⟨454320, by rfl⟩ : syracuseStep 1211521 = 908641) (by norm_num)
theorem B1211557 : Blo 1076618 1211557 := bbase (se 4 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 1211557 = 227167) (by norm_num)
theorem B4095157 : Blo 1076618 4095157 := bbase (se 5 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 4095157 = 383921) (by norm_num)
theorem B2424005 : Blo 1076618 2424005 := bbase (se 4 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 2424005 = 454501) (by norm_num)
theorem B1211593 : Blo 1076618 1211593 := bbase (se 2 (by rfl) ⟨454347, by rfl⟩ : syracuseStep 1211593 = 908695) (by norm_num)
theorem B1211629 : Blo 1076618 1211629 := bbase (se 3 (by rfl) ⟨227180, by rfl⟩ : syracuseStep 1211629 = 454361) (by norm_num)
theorem B2424077 : Blo 1076618 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B1211665 : Blo 1076618 1211665 := bbase (se 2 (by rfl) ⟨454374, by rfl⟩ : syracuseStep 1211665 = 908749) (by norm_num)
theorem B4914485 : Blo 1076618 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B1211701 : Blo 1076618 1211701 := bbase (se 5 (by rfl) ⟨56798, by rfl⟩ : syracuseStep 1211701 = 113597) (by norm_num)
theorem B2424149 : Blo 1076618 2424149 := bbase (se 11 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 2424149 = 3551) (by norm_num)
theorem B1211737 : Blo 1076618 1211737 := bbase (se 2 (by rfl) ⟨454401, by rfl⟩ : syracuseStep 1211737 = 908803) (by norm_num)
theorem B1211773 : Blo 1076618 1211773 := bbase (se 3 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 1211773 = 454415) (by norm_num)
theorem B3636629 : Blo 1076618 3636629 := bbase (se 6 (by rfl) ⟨85233, by rfl⟩ : syracuseStep 3636629 = 170467) (by norm_num)
theorem B2424221 : Blo 1076618 2424221 := bbase (se 3 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 2424221 = 909083) (by norm_num)
theorem B1211809 : Blo 1076618 1211809 := bbase (se 2 (by rfl) ⟨454428, by rfl⟩ : syracuseStep 1211809 = 908857) (by norm_num)
theorem B1211845 : Blo 1076618 1211845 := bbase (se 4 (by rfl) ⟨113610, by rfl⟩ : syracuseStep 1211845 = 227221) (by norm_num)
theorem B2424293 : Blo 1076618 2424293 := bbase (se 4 (by rfl) ⟨227277, by rfl⟩ : syracuseStep 2424293 = 454555) (by norm_num)
theorem B4095461 : Blo 1076618 4095461 := bbase (se 4 (by rfl) ⟨383949, by rfl⟩ : syracuseStep 4095461 = 767899) (by norm_num)
theorem B1211881 : Blo 1076618 1211881 := bbase (se 2 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 1211881 = 908911) (by norm_num)
theorem B1211917 : Blo 1076618 1211917 := bbase (se 3 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 1211917 = 454469) (by norm_num)
theorem B2424365 : Blo 1076618 2424365 := bbase (se 3 (by rfl) ⟨454568, by rfl⟩ : syracuseStep 2424365 = 909137) (by norm_num)
theorem B1211953 : Blo 1076618 1211953 := bbase (se 2 (by rfl) ⟨454482, by rfl⟩ : syracuseStep 1211953 = 908965) (by norm_num)
theorem B1211989 : Blo 1076618 1211989 := bbase (se 8 (by rfl) ⟨7101, by rfl⟩ : syracuseStep 1211989 = 14203) (by norm_num)
theorem B2424437 : Blo 1076618 2424437 := bbase (se 5 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 2424437 = 227291) (by norm_num)
theorem B1212025 : Blo 1076618 1212025 := bbase (se 2 (by rfl) ⟨454509, by rfl⟩ : syracuseStep 1212025 = 909019) (by norm_num)
theorem B1638029 : Blo 1076618 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B1212061 : Blo 1076618 1212061 := bbase (se 3 (by rfl) ⟨227261, by rfl⟩ : syracuseStep 1212061 = 454523) (by norm_num)
theorem B2424509 : Blo 1076618 2424509 := bbase (se 3 (by rfl) ⟨454595, by rfl⟩ : syracuseStep 2424509 = 909191) (by norm_num)
theorem B1212097 : Blo 1076618 1212097 := bbase (se 2 (by rfl) ⟨454536, by rfl⟩ : syracuseStep 1212097 = 909073) (by norm_num)
theorem B2457317 : Blo 1076618 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B1212133 : Blo 1076618 1212133 := bbase (se 4 (by rfl) ⟨113637, by rfl⟩ : syracuseStep 1212133 = 227275) (by norm_num)
theorem B2424581 : Blo 1076618 2424581 := bbase (se 4 (by rfl) ⟨227304, by rfl⟩ : syracuseStep 2424581 = 454609) (by norm_num)
theorem B1212169 : Blo 1076618 1212169 := bbase (se 2 (by rfl) ⟨454563, by rfl⟩ : syracuseStep 1212169 = 909127) (by norm_num)
theorem B1212205 : Blo 1076618 1212205 := bbase (se 3 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 1212205 = 454577) (by norm_num)
theorem B3637061 : Blo 1076618 3637061 := bbase (se 4 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 3637061 = 681949) (by norm_num)
theorem B2424653 : Blo 1076618 2424653 := bbase (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) (by norm_num)
theorem B1212241 : Blo 1076618 1212241 := bbase (se 2 (by rfl) ⟨454590, by rfl⟩ : syracuseStep 1212241 = 909181) (by norm_num)
theorem B1212277 : Blo 1076618 1212277 := bbase (se 5 (by rfl) ⟨56825, by rfl⟩ : syracuseStep 1212277 = 113651) (by norm_num)
theorem B2424725 : Blo 1076618 2424725 := bbase (se 6 (by rfl) ⟨56829, by rfl⟩ : syracuseStep 2424725 = 113659) (by norm_num)
theorem B1212313 : Blo 1076618 1212313 := bbase (se 2 (by rfl) ⟨454617, by rfl⟩ : syracuseStep 1212313 = 909235) (by norm_num)
theorem B1212349 : Blo 1076618 1212349 := bbase (se 3 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 1212349 = 454631) (by norm_num)
theorem B2424797 : Blo 1076618 2424797 := bbase (se 3 (by rfl) ⟨454649, by rfl⟩ : syracuseStep 2424797 = 909299) (by norm_num)
theorem B1212385 : Blo 1076618 1212385 := bbase (se 2 (by rfl) ⟨454644, by rfl⟩ : syracuseStep 1212385 = 909289) (by norm_num)
theorem B39321713 : Blo 1076618 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B1212547 : Blo 1076618 1212547 := bstep (se 1 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 1212547 = 1818821) B1818821
theorem B2424977 : Blo 1076618 2424977 := bstep (se 2 (by rfl) ⟨909366, by rfl⟩ : syracuseStep 2424977 = 1818733) B1818733
theorem B2424995 : Blo 1076618 2424995 := bstep (se 1 (by rfl) ⟨1818746, by rfl⟩ : syracuseStep 2424995 = 3637493) B3637493
theorem B1212691 : Blo 1076618 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B1212835 : Blo 1076618 1212835 := bstep (se 1 (by rfl) ⟨909626, by rfl⟩ : syracuseStep 1212835 = 1819253) B1819253
theorem B2425265 : Blo 1076618 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B4096433 : Blo 1076618 4096433 := bstep (se 2 (by rfl) ⟨1536162, by rfl⟩ : syracuseStep 4096433 = 3072325) B3072325
theorem B2425283 : Blo 1076618 2425283 := bstep (se 1 (by rfl) ⟨1818962, by rfl⟩ : syracuseStep 2425283 = 3637925) B3637925
theorem B3637709 : Blo 1076618 3637709 := bstep (se 3 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 3637709 = 1364141) B1364141
theorem B3277297 : Blo 1076618 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B3637763 : Blo 1076618 3637763 := bstep (se 1 (by rfl) ⟨2728322, by rfl⟩ : syracuseStep 3637763 = 5456645) B5456645
theorem B1212979 : Blo 1076618 1212979 := bstep (se 1 (by rfl) ⟨909734, by rfl⟩ : syracuseStep 1212979 = 1819469) B1819469
theorem B1213123 : Blo 1076618 1213123 := bstep (se 1 (by rfl) ⟨909842, by rfl⟩ : syracuseStep 1213123 = 1819685) B1819685
theorem B2425553 : Blo 1076618 2425553 := bstep (se 2 (by rfl) ⟨909582, by rfl⟩ : syracuseStep 2425553 = 1819165) B1819165
theorem B2425571 : Blo 1076618 2425571 := bstep (se 1 (by rfl) ⟨1819178, by rfl⟩ : syracuseStep 2425571 = 3638357) B3638357
theorem B1311475 : Blo 1076618 1311475 := bstep (se 1 (by rfl) ⟨983606, by rfl⟩ : syracuseStep 1311475 = 1967213) B1967213
theorem B3638033 : Blo 1076618 3638033 := bstep (se 2 (by rfl) ⟨1364262, by rfl⟩ : syracuseStep 3638033 = 2728525) B2728525
theorem B2458403 : Blo 1076618 2458403 := bstep (se 1 (by rfl) ⟨1843802, by rfl⟩ : syracuseStep 2458403 = 3687605) B3687605
theorem B20742965 : Blo 1076618 20742965 := bstep (se 5 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 20742965 = 1944653) B1944653
theorem B5833549 : Blo 1076618 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B1213267 : Blo 1076618 1213267 := bstep (se 1 (by rfl) ⟨909950, by rfl⟩ : syracuseStep 1213267 = 1819901) B1819901
theorem B1966993 : Blo 1076618 1966993 := bstep (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) B1475245
theorem B1868689 : Blo 1076618 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1213411 : Blo 1076618 1213411 := bstep (se 1 (by rfl) ⟨910058, by rfl⟩ : syracuseStep 1213411 = 1820117) B1820117
theorem B2425841 : Blo 1076618 2425841 := bstep (se 2 (by rfl) ⟨909690, by rfl⟩ : syracuseStep 2425841 = 1819381) B1819381
theorem B2425859 : Blo 1076618 2425859 := bstep (se 1 (by rfl) ⟨1819394, by rfl⟩ : syracuseStep 2425859 = 3638789) B3638789
theorem B4097101 : Blo 1076618 4097101 := bstep (se 3 (by rfl) ⟨768206, by rfl⟩ : syracuseStep 4097101 = 1536413) B1536413
theorem B1213555 : Blo 1076618 1213555 := bstep (se 1 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 1213555 = 1820333) B1820333
theorem B3278029 : Blo 1076618 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B1213699 : Blo 1076618 1213699 := bstep (se 1 (by rfl) ⟨910274, by rfl⟩ : syracuseStep 1213699 = 1820549) B1820549
theorem B2426129 : Blo 1076618 2426129 := bstep (se 2 (by rfl) ⟨909798, by rfl⟩ : syracuseStep 2426129 = 1819597) B1819597
theorem B2426147 : Blo 1076618 2426147 := bstep (se 1 (by rfl) ⟨1819610, by rfl⟩ : syracuseStep 2426147 = 3639221) B3639221
theorem B3638573 : Blo 1076618 3638573 := bstep (se 3 (by rfl) ⟨682232, by rfl⟩ : syracuseStep 3638573 = 1364465) B1364465
theorem B3638627 : Blo 1076618 3638627 := bstep (se 1 (by rfl) ⟨2728970, by rfl⟩ : syracuseStep 3638627 = 5457941) B5457941
theorem B1213843 : Blo 1076618 1213843 := bstep (se 1 (by rfl) ⟨910382, by rfl⟩ : syracuseStep 1213843 = 1820765) B1820765
theorem B1639939 : Blo 1076618 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B1213987 : Blo 1076618 1213987 := bstep (se 1 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 1213987 = 1820981) B1820981
theorem B2426417 : Blo 1076618 2426417 := bstep (se 2 (by rfl) ⟨909906, by rfl⟩ : syracuseStep 2426417 = 1819813) B1819813
theorem B2426435 : Blo 1076618 2426435 := bstep (se 1 (by rfl) ⟨1819826, by rfl⟩ : syracuseStep 2426435 = 3639653) B3639653
theorem B13796963 : Blo 1076618 13796963 := bstep (se 1 (by rfl) ⟨10347722, by rfl⟩ : syracuseStep 13796963 = 20695445) B20695445
theorem B3638897 : Blo 1076618 3638897 := bstep (se 2 (by rfl) ⟨1364586, by rfl⟩ : syracuseStep 3638897 = 2729173) B2729173
theorem B1214131 : Blo 1076618 1214131 := bstep (se 1 (by rfl) ⟨910598, by rfl⟩ : syracuseStep 1214131 = 1821197) B1821197
theorem B1214275 : Blo 1076618 1214275 := bstep (se 1 (by rfl) ⟨910706, by rfl⟩ : syracuseStep 1214275 = 1821413) B1821413
theorem B2426705 : Blo 1076618 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B9209699 : Blo 1076618 9209699 := bstep (se 1 (by rfl) ⟨6907274, by rfl⟩ : syracuseStep 9209699 = 13814549) B13814549
theorem B2426723 : Blo 1076618 2426723 := bstep (se 1 (by rfl) ⟨1820042, by rfl⟩ : syracuseStep 2426723 = 3640085) B3640085
theorem B4097891 : Blo 1076618 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B11241413 : Blo 1076618 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B1214419 : Blo 1076618 1214419 := bstep (se 1 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 1214419 = 1821629) B1821629
theorem B7112717 : Blo 1076618 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B1640497 : Blo 1076618 1640497 := bstep (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) B1230373
theorem B1214563 : Blo 1076618 1214563 := bstep (se 1 (by rfl) ⟨910922, by rfl⟩ : syracuseStep 1214563 = 1821845) B1821845
theorem B6555761 : Blo 1076618 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B2426993 : Blo 1076618 2426993 := bstep (se 2 (by rfl) ⟨910122, by rfl⟩ : syracuseStep 2426993 = 1820245) B1820245
theorem B2427011 : Blo 1076618 2427011 := bstep (se 1 (by rfl) ⟨1820258, by rfl⟩ : syracuseStep 2427011 = 3640517) B3640517
theorem B3639437 : Blo 1076618 3639437 := bstep (se 3 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 3639437 = 1364789) B1364789
theorem B3639491 : Blo 1076618 3639491 := bstep (se 1 (by rfl) ⟨2729618, by rfl⟩ : syracuseStep 3639491 = 5459237) B5459237
theorem B1870067 : Blo 1076618 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1214707 : Blo 1076618 1214707 := bstep (se 1 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 1214707 = 1822061) B1822061
theorem B1214851 : Blo 1076618 1214851 := bstep (se 1 (by rfl) ⟨911138, by rfl⟩ : syracuseStep 1214851 = 1822277) B1822277
theorem B6752645 : Blo 1076618 6752645 := bstep (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) B1266121
theorem B8194445 : Blo 1076618 8194445 := bstep (se 3 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 8194445 = 3072917) B3072917
theorem B2427281 : Blo 1076618 2427281 := bstep (se 2 (by rfl) ⟨910230, by rfl⟩ : syracuseStep 2427281 = 1820461) B1820461
theorem B2427299 : Blo 1076618 2427299 := bstep (se 1 (by rfl) ⟨1820474, by rfl⟩ : syracuseStep 2427299 = 3640949) B3640949
theorem B3639761 : Blo 1076618 3639761 := bstep (se 2 (by rfl) ⟨1364910, by rfl⟩ : syracuseStep 3639761 = 2729821) B2729821
theorem B4098545 : Blo 1076618 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B1214995 : Blo 1076618 1214995 := bstep (se 1 (by rfl) ⟨911246, by rfl⟩ : syracuseStep 1214995 = 1822493) B1822493
theorem B1477235 : Blo 1076618 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B1215139 : Blo 1076618 1215139 := bstep (se 1 (by rfl) ⟨911354, by rfl⟩ : syracuseStep 1215139 = 1822709) B1822709
theorem B2427569 : Blo 1076618 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B2427587 : Blo 1076618 2427587 := bstep (se 1 (by rfl) ⟨1820690, by rfl⟩ : syracuseStep 2427587 = 3641381) B3641381
theorem B6916913 : Blo 1076618 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1215283 : Blo 1076618 1215283 := bstep (se 1 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 1215283 = 1822925) B1822925
theorem B8096611 : Blo 1076618 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B1215427 : Blo 1076618 1215427 := bstep (se 1 (by rfl) ⟨911570, by rfl⟩ : syracuseStep 1215427 = 1823141) B1823141
theorem B2427857 : Blo 1076618 2427857 := bstep (se 2 (by rfl) ⟨910446, by rfl⟩ : syracuseStep 2427857 = 1820893) B1820893
theorem B2427875 : Blo 1076618 2427875 := bstep (se 1 (by rfl) ⟨1820906, by rfl⟩ : syracuseStep 2427875 = 3641813) B3641813
theorem B3640301 : Blo 1076618 3640301 := bstep (se 3 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 3640301 = 1365113) B1365113
theorem B3640355 : Blo 1076618 3640355 := bstep (se 1 (by rfl) ⟨2730266, by rfl⟩ : syracuseStep 3640355 = 5460533) B5460533
theorem B1215571 : Blo 1076618 1215571 := bstep (se 1 (by rfl) ⟨911678, by rfl⟩ : syracuseStep 1215571 = 1823357) B1823357
theorem B2428145 : Blo 1076618 2428145 := bstep (se 2 (by rfl) ⟨910554, by rfl⟩ : syracuseStep 2428145 = 1821109) B1821109
theorem B2428163 : Blo 1076618 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B3640625 : Blo 1076618 3640625 := bstep (se 2 (by rfl) ⟨1365234, by rfl⟩ : syracuseStep 3640625 = 2730469) B2730469
theorem B2428433 : Blo 1076618 2428433 := bstep (se 2 (by rfl) ⟨910662, by rfl⟩ : syracuseStep 2428433 = 1821325) B1821325
theorem B2428451 : Blo 1076618 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B85298741 : Blo 1076618 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B1642049 : Blo 1076618 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B1642243 : Blo 1076618 1642243 := bstep (se 1 (by rfl) ⟨1231682, by rfl⟩ : syracuseStep 1642243 = 2463365) B2463365
theorem B2428721 : Blo 1076618 2428721 := bstep (se 2 (by rfl) ⟨910770, by rfl⟩ : syracuseStep 2428721 = 1821541) B1821541
theorem B2428739 : Blo 1076618 2428739 := bstep (se 1 (by rfl) ⟨1821554, by rfl⟩ : syracuseStep 2428739 = 3643109) B3643109
theorem B3641165 : Blo 1076618 3641165 := bstep (se 3 (by rfl) ⟨682718, by rfl⟩ : syracuseStep 3641165 = 1365437) B1365437
theorem B3641219 : Blo 1076618 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B2920333 : Blo 1076618 2920333 := bstep (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) B1095125
theorem B4100003 : Blo 1076618 4100003 := bstep (se 1 (by rfl) ⟨3075002, by rfl⟩ : syracuseStep 4100003 = 6150005) B6150005
theorem B4100017 : Blo 1076618 4100017 := bstep (se 2 (by rfl) ⟨1537506, by rfl⟩ : syracuseStep 4100017 = 3075013) B3075013
theorem B1871843 : Blo 1076618 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B2429009 : Blo 1076618 2429009 := bstep (se 2 (by rfl) ⟨910878, by rfl⟩ : syracuseStep 2429009 = 1821757) B1821757
theorem B2429027 : Blo 1076618 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B3641489 : Blo 1076618 3641489 := bstep (se 2 (by rfl) ⟨1365558, by rfl⟩ : syracuseStep 3641489 = 2731117) B2731117
theorem B2461841 : Blo 1076618 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B6918371 : Blo 1076618 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B1577267 : Blo 1076618 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B2429297 : Blo 1076618 2429297 := bstep (se 2 (by rfl) ⟨910986, by rfl⟩ : syracuseStep 2429297 = 1821973) B1821973
theorem B2429315 : Blo 1076618 2429315 := bstep (se 1 (by rfl) ⟨1821986, by rfl⟩ : syracuseStep 2429315 = 3643973) B3643973
theorem B1151507 : Blo 1076618 1151507 := bstep (se 1 (by rfl) ⟨863630, by rfl⟩ : syracuseStep 1151507 = 1727261) B1727261
theorem B5182051 : Blo 1076618 5182051 := bstep (se 1 (by rfl) ⟨3886538, by rfl⟩ : syracuseStep 5182051 = 7773077) B7773077
theorem B10359409 : Blo 1076618 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B2429585 : Blo 1076618 2429585 := bstep (se 2 (by rfl) ⟨911094, by rfl⟩ : syracuseStep 2429585 = 1822189) B1822189
theorem B2429603 : Blo 1076618 2429603 := bstep (se 1 (by rfl) ⟨1822202, by rfl⟩ : syracuseStep 2429603 = 3644405) B3644405
theorem B3642029 : Blo 1076618 3642029 := bstep (se 3 (by rfl) ⟨682880, by rfl⟩ : syracuseStep 3642029 = 1365761) B1365761
theorem B3642083 : Blo 1076618 3642083 := bstep (se 1 (by rfl) ⟨2731562, by rfl⟩ : syracuseStep 3642083 = 5463125) B5463125
theorem B2429873 : Blo 1076618 2429873 := bstep (se 2 (by rfl) ⟨911202, by rfl⟩ : syracuseStep 2429873 = 1822405) B1822405
theorem B2429891 : Blo 1076618 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B3642353 : Blo 1076618 3642353 := bstep (se 2 (by rfl) ⟨1365882, by rfl⟩ : syracuseStep 3642353 = 2731765) B2731765
theorem B6132941 : Blo 1076618 6132941 := bstep (se 3 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 6132941 = 2299853) B2299853
theorem B2430161 : Blo 1076618 2430161 := bstep (se 2 (by rfl) ⟨911310, by rfl⟩ : syracuseStep 2430161 = 1822621) B1822621
theorem B2430179 : Blo 1076618 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B8197361 : Blo 1076618 8197361 := bstep (se 2 (by rfl) ⟨3074010, by rfl⟩ : syracuseStep 8197361 = 6148021) B6148021
theorem B4101475 : Blo 1076618 4101475 := bstep (se 1 (by rfl) ⟨3076106, by rfl⟩ : syracuseStep 4101475 = 6152213) B6152213
theorem B2725265 : Blo 1076618 2725265 := bstep (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) B2043949
theorem B2430449 : Blo 1076618 2430449 := bstep (se 2 (by rfl) ⟨911418, by rfl⟩ : syracuseStep 2430449 = 1822837) B1822837
theorem B1152515 : Blo 1076618 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B2430467 : Blo 1076618 2430467 := bstep (se 1 (by rfl) ⟨1822850, by rfl⟩ : syracuseStep 2430467 = 3645701) B3645701
theorem B3642893 : Blo 1076618 3642893 := bstep (se 3 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 3642893 = 1366085) B1366085
theorem B3642947 : Blo 1076618 3642947 := bstep (se 1 (by rfl) ⟨2732210, by rfl⟩ : syracuseStep 3642947 = 5464421) B5464421
theorem B7870193 : Blo 1076618 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B2430737 : Blo 1076618 2430737 := bstep (se 2 (by rfl) ⟨911526, by rfl⟩ : syracuseStep 2430737 = 1823053) B1823053
theorem B2430755 : Blo 1076618 2430755 := bstep (se 1 (by rfl) ⟨1823066, by rfl⟩ : syracuseStep 2430755 = 3646133) B3646133
theorem B5183281 : Blo 1076618 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B3643217 : Blo 1076618 3643217 := bstep (se 2 (by rfl) ⟨1366206, by rfl⟩ : syracuseStep 3643217 = 2732413) B2732413
theorem B6920113 : Blo 1076618 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B2431025 : Blo 1076618 2431025 := bstep (se 2 (by rfl) ⟨911634, by rfl⟩ : syracuseStep 2431025 = 1823269) B1823269
theorem B2431043 : Blo 1076618 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B2431313 : Blo 1076618 2431313 := bstep (se 2 (by rfl) ⟨911742, by rfl⟩ : syracuseStep 2431313 = 1823485) B1823485
theorem B2431331 : Blo 1076618 2431331 := bstep (se 1 (by rfl) ⟨1823498, by rfl⟩ : syracuseStep 2431331 = 3646997) B3646997
theorem B3643757 : Blo 1076618 3643757 := bstep (se 3 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 3643757 = 1366409) B1366409
theorem B2726257 : Blo 1076618 2726257 := bstep (se 2 (by rfl) ⟨1022346, by rfl⟩ : syracuseStep 2726257 = 2044693) B2044693
theorem B7772557 : Blo 1076618 7772557 := bstep (se 3 (by rfl) ⟨1457354, by rfl⟩ : syracuseStep 7772557 = 2914709) B2914709
theorem B3643811 : Blo 1076618 3643811 := bstep (se 1 (by rfl) ⟨2732858, by rfl⟩ : syracuseStep 3643811 = 5465717) B5465717
theorem B2595235 : Blo 1076618 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B2595331 : Blo 1076618 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B2726531 : Blo 1076618 2726531 := bstep (se 1 (by rfl) ⟨2044898, by rfl⟩ : syracuseStep 2726531 = 4089797) B4089797
theorem B3644081 : Blo 1076618 3644081 := bstep (se 2 (by rfl) ⟨1366530, by rfl⟩ : syracuseStep 3644081 = 2733061) B2733061
theorem B2726723 : Blo 1076618 2726723 := bstep (se 1 (by rfl) ⟨2045042, by rfl⟩ : syracuseStep 2726723 = 4090085) B4090085
theorem B5545037 : Blo 1076618 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B2956429 : Blo 1076618 2956429 := bstep (se 3 (by rfl) ⟨554330, by rfl⟩ : syracuseStep 2956429 = 1108661) B1108661
theorem B3644621 : Blo 1076618 3644621 := bstep (se 3 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 3644621 = 1366733) B1366733
theorem B1940689 : Blo 1076618 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B2301169 : Blo 1076618 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B3644675 : Blo 1076618 3644675 := bstep (se 1 (by rfl) ⟨2733506, by rfl⟩ : syracuseStep 3644675 = 5467013) B5467013
theorem B2497873 : Blo 1076618 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B6135173 : Blo 1076618 6135173 := bstep (se 4 (by rfl) ⟨575172, by rfl⟩ : syracuseStep 6135173 = 1150345) B1150345
theorem B7380485 : Blo 1076618 7380485 := bstep (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) B1383841
theorem B3644945 : Blo 1076618 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B1842707 : Blo 1076618 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B2072099 : Blo 1076618 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B2727665 : Blo 1076618 2727665 := bstep (se 2 (by rfl) ⟨1022874, by rfl⟩ : syracuseStep 2727665 = 2045749) B2045749
theorem B2727715 : Blo 1076618 2727715 := bstep (se 1 (by rfl) ⟨2045786, by rfl⟩ : syracuseStep 2727715 = 4091573) B4091573
theorem B6922061 : Blo 1076618 6922061 := bstep (se 3 (by rfl) ⟨1297886, by rfl⟩ : syracuseStep 6922061 = 2595773) B2595773
theorem B2727857 : Blo 1076618 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B3645485 : Blo 1076618 3645485 := bstep (se 3 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 3645485 = 1367057) B1367057
theorem B6135857 : Blo 1076618 6135857 := bstep (se 2 (by rfl) ⟨2300946, by rfl⟩ : syracuseStep 6135857 = 4601893) B4601893
theorem B3645539 : Blo 1076618 3645539 := bstep (se 1 (by rfl) ⟨2734154, by rfl⟩ : syracuseStep 3645539 = 5468309) B5468309
theorem B1843507 : Blo 1076618 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B3645809 : Blo 1076618 3645809 := bstep (se 2 (by rfl) ⟨1367178, by rfl⟩ : syracuseStep 3645809 = 2734357) B2734357
theorem B7381475 : Blo 1076618 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B1942211 : Blo 1076618 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B3449549 : Blo 1076618 3449549 := bstep (se 3 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 3449549 = 1293581) B1293581
theorem B3646349 : Blo 1076618 3646349 := bstep (se 3 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 3646349 = 1367381) B1367381
theorem B2728849 : Blo 1076618 2728849 := bstep (se 2 (by rfl) ⟨1023318, by rfl⟩ : syracuseStep 2728849 = 2046637) B2046637
theorem B3646403 : Blo 1076618 3646403 := bstep (se 1 (by rfl) ⟨2734802, by rfl⟩ : syracuseStep 3646403 = 5469605) B5469605
theorem B1614929 : Blo 1076618 1614929 := bstep (se 2 (by rfl) ⟨605598, by rfl⟩ : syracuseStep 1614929 = 1211197) B1211197
theorem B1614947 : Blo 1076618 1614947 := bstep (se 1 (by rfl) ⟨1211210, by rfl⟩ : syracuseStep 1614947 = 2422421) B2422421
theorem B1614977 : Blo 1076618 1614977 := bstep (se 2 (by rfl) ⟨605616, by rfl⟩ : syracuseStep 1614977 = 1211233) B1211233
theorem B1614995 : Blo 1076618 1614995 := bstep (se 1 (by rfl) ⟨1211246, by rfl⟩ : syracuseStep 1614995 = 2422493) B2422493
theorem B2729123 : Blo 1076618 2729123 := bstep (se 1 (by rfl) ⟨2046842, by rfl⟩ : syracuseStep 2729123 = 4093685) B4093685
theorem B1615025 : Blo 1076618 1615025 := bstep (se 2 (by rfl) ⟨605634, by rfl⟩ : syracuseStep 1615025 = 1211269) B1211269
theorem B1615043 : Blo 1076618 1615043 := bstep (se 1 (by rfl) ⟨1211282, by rfl⟩ : syracuseStep 1615043 = 2422565) B2422565
theorem B3450061 : Blo 1076618 3450061 := bstep (se 3 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 3450061 = 1293773) B1293773
theorem B3646673 : Blo 1076618 3646673 := bstep (se 2 (by rfl) ⟨1367502, by rfl⟩ : syracuseStep 3646673 = 2735005) B2735005
theorem B1615073 : Blo 1076618 1615073 := bstep (se 2 (by rfl) ⟨605652, by rfl⟩ : syracuseStep 1615073 = 1211305) B1211305
theorem B1615091 : Blo 1076618 1615091 := bstep (se 1 (by rfl) ⟨1211318, by rfl⟩ : syracuseStep 1615091 = 2422637) B2422637
theorem B11052301 : Blo 1076618 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B1615121 : Blo 1076618 1615121 := bstep (se 2 (by rfl) ⟨605670, by rfl⟩ : syracuseStep 1615121 = 1211341) B1211341
theorem B1615139 : Blo 1076618 1615139 := bstep (se 1 (by rfl) ⟨1211354, by rfl⟩ : syracuseStep 1615139 = 2422709) B2422709
theorem B1615169 : Blo 1076618 1615169 := bstep (se 2 (by rfl) ⟨605688, by rfl⟩ : syracuseStep 1615169 = 1211377) B1211377
theorem B1615187 : Blo 1076618 1615187 := bstep (se 1 (by rfl) ⟨1211390, by rfl⟩ : syracuseStep 1615187 = 2422781) B2422781
theorem B2729315 : Blo 1076618 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B1615217 : Blo 1076618 1615217 := bstep (se 2 (by rfl) ⟨605706, by rfl⟩ : syracuseStep 1615217 = 1211413) B1211413
theorem B1615235 : Blo 1076618 1615235 := bstep (se 1 (by rfl) ⟨1211426, by rfl⟩ : syracuseStep 1615235 = 2422853) B2422853
theorem B12166541 : Blo 1076618 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1615265 : Blo 1076618 1615265 := bstep (se 2 (by rfl) ⟨605724, by rfl⟩ : syracuseStep 1615265 = 1211449) B1211449
theorem B1615283 : Blo 1076618 1615283 := bstep (se 1 (by rfl) ⟨1211462, by rfl⟩ : syracuseStep 1615283 = 2422925) B2422925
theorem B1615313 : Blo 1076618 1615313 := bstep (se 2 (by rfl) ⟨605742, by rfl⟩ : syracuseStep 1615313 = 1211485) B1211485
theorem B1615331 : Blo 1076618 1615331 := bstep (se 1 (by rfl) ⟨1211498, by rfl⟩ : syracuseStep 1615331 = 2422997) B2422997
theorem B6137315 : Blo 1076618 6137315 := bstep (se 1 (by rfl) ⟨4602986, by rfl⟩ : syracuseStep 6137315 = 9205973) B9205973
theorem B1615361 : Blo 1076618 1615361 := bstep (se 2 (by rfl) ⟨605760, by rfl⟩ : syracuseStep 1615361 = 1211521) B1211521
theorem B1615379 : Blo 1076618 1615379 := bstep (se 1 (by rfl) ⟨1211534, by rfl⟩ : syracuseStep 1615379 = 2423069) B2423069
theorem B1615409 : Blo 1076618 1615409 := bstep (se 2 (by rfl) ⟨605778, by rfl⟩ : syracuseStep 1615409 = 1211557) B1211557
theorem B1615427 : Blo 1076618 1615427 := bstep (se 1 (by rfl) ⟨1211570, by rfl⟩ : syracuseStep 1615427 = 2423141) B2423141
theorem B1615457 : Blo 1076618 1615457 := bstep (se 2 (by rfl) ⟨605796, by rfl⟩ : syracuseStep 1615457 = 1211593) B1211593
theorem B1844849 : Blo 1076618 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B1615475 : Blo 1076618 1615475 := bstep (se 1 (by rfl) ⟨1211606, by rfl⟩ : syracuseStep 1615475 = 2423213) B2423213
theorem B1615505 : Blo 1076618 1615505 := bstep (se 2 (by rfl) ⟨605814, by rfl⟩ : syracuseStep 1615505 = 1211629) B1211629
theorem B1615523 : Blo 1076618 1615523 := bstep (se 1 (by rfl) ⟨1211642, by rfl⟩ : syracuseStep 1615523 = 2423285) B2423285
theorem B1615553 : Blo 1076618 1615553 := bstep (se 2 (by rfl) ⟨605832, by rfl⟩ : syracuseStep 1615553 = 1211665) B1211665
theorem B3450563 : Blo 1076618 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B4368077 : Blo 1076618 4368077 := bstep (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) B1638029
theorem B1615571 : Blo 1076618 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B52405987 : Blo 1076618 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B1615601 : Blo 1076618 1615601 := bstep (se 2 (by rfl) ⟨605850, by rfl⟩ : syracuseStep 1615601 = 1211701) B1211701
theorem B1615619 : Blo 1076618 1615619 := bstep (se 1 (by rfl) ⟨1211714, by rfl⟩ : syracuseStep 1615619 = 2423429) B2423429
theorem B1615649 : Blo 1076618 1615649 := bstep (se 2 (by rfl) ⟨605868, by rfl⟩ : syracuseStep 1615649 = 1211737) B1211737
theorem B1615667 : Blo 1076618 1615667 := bstep (se 1 (by rfl) ⟨1211750, by rfl⟩ : syracuseStep 1615667 = 2423501) B2423501
theorem B1615697 : Blo 1076618 1615697 := bstep (se 2 (by rfl) ⟨605886, by rfl⟩ : syracuseStep 1615697 = 1211773) B1211773
theorem B1615715 : Blo 1076618 1615715 := bstep (se 1 (by rfl) ⟨1211786, by rfl⟩ : syracuseStep 1615715 = 2423573) B2423573
theorem B1615745 : Blo 1076618 1615745 := bstep (se 2 (by rfl) ⟨605904, by rfl⟩ : syracuseStep 1615745 = 1211809) B1211809
theorem B1615763 : Blo 1076618 1615763 := bstep (se 1 (by rfl) ⟨1211822, by rfl⟩ : syracuseStep 1615763 = 2423645) B2423645
theorem B1615793 : Blo 1076618 1615793 := bstep (se 2 (by rfl) ⟨605922, by rfl⟩ : syracuseStep 1615793 = 1211845) B1211845
theorem B1615811 : Blo 1076618 1615811 := bstep (se 1 (by rfl) ⟨1211858, by rfl⟩ : syracuseStep 1615811 = 2423717) B2423717
theorem B1615841 : Blo 1076618 1615841 := bstep (se 2 (by rfl) ⟨605940, by rfl⟩ : syracuseStep 1615841 = 1211881) B1211881
theorem B2074609 : Blo 1076618 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B1615859 : Blo 1076618 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B1615889 : Blo 1076618 1615889 := bstep (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) B1211917
theorem B1615907 : Blo 1076618 1615907 := bstep (se 1 (by rfl) ⟨1211930, by rfl⟩ : syracuseStep 1615907 = 2423861) B2423861
theorem B1615937 : Blo 1076618 1615937 := bstep (se 2 (by rfl) ⟨605976, by rfl⟩ : syracuseStep 1615937 = 1211953) B1211953
theorem B1615955 : Blo 1076618 1615955 := bstep (se 1 (by rfl) ⟨1211966, by rfl⟩ : syracuseStep 1615955 = 2423933) B2423933
theorem B1615985 : Blo 1076618 1615985 := bstep (se 2 (by rfl) ⟨605994, by rfl⟩ : syracuseStep 1615985 = 1211989) B1211989
theorem B1616003 : Blo 1076618 1616003 := bstep (se 1 (by rfl) ⟨1212002, by rfl⟩ : syracuseStep 1616003 = 2424005) B2424005
theorem B1616033 : Blo 1076618 1616033 := bstep (se 2 (by rfl) ⟨606012, by rfl⟩ : syracuseStep 1616033 = 1212025) B1212025
theorem B1616051 : Blo 1076618 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B1616081 : Blo 1076618 1616081 := bstep (se 2 (by rfl) ⟨606030, by rfl⟩ : syracuseStep 1616081 = 1212061) B1212061
theorem B1616099 : Blo 1076618 1616099 := bstep (se 1 (by rfl) ⟨1212074, by rfl⟩ : syracuseStep 1616099 = 2424149) B2424149
theorem B2304227 : Blo 1076618 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B1616129 : Blo 1076618 1616129 := bstep (se 2 (by rfl) ⟨606048, by rfl⟩ : syracuseStep 1616129 = 1212097) B1212097
theorem B2730257 : Blo 1076618 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B1616147 : Blo 1076618 1616147 := bstep (se 1 (by rfl) ⟨1212110, by rfl⟩ : syracuseStep 1616147 = 2424221) B2424221
theorem B1616177 : Blo 1076618 1616177 := bstep (se 2 (by rfl) ⟨606066, by rfl⟩ : syracuseStep 1616177 = 1212133) B1212133
theorem B1616195 : Blo 1076618 1616195 := bstep (se 1 (by rfl) ⟨1212146, by rfl⟩ : syracuseStep 1616195 = 2424293) B2424293
theorem B2730307 : Blo 1076618 2730307 := bstep (se 1 (by rfl) ⟨2047730, by rfl⟩ : syracuseStep 2730307 = 4095461) B4095461
theorem B2074961 : Blo 1076618 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B1616225 : Blo 1076618 1616225 := bstep (se 2 (by rfl) ⟨606084, by rfl⟩ : syracuseStep 1616225 = 1212169) B1212169
theorem B1616243 : Blo 1076618 1616243 := bstep (se 1 (by rfl) ⟨1212182, by rfl⟩ : syracuseStep 1616243 = 2424365) B2424365
theorem B1616273 : Blo 1076618 1616273 := bstep (se 2 (by rfl) ⟨606102, by rfl⟩ : syracuseStep 1616273 = 1212205) B1212205
theorem B1616291 : Blo 1076618 1616291 := bstep (se 1 (by rfl) ⟨1212218, by rfl⟩ : syracuseStep 1616291 = 2424437) B2424437
theorem B1616321 : Blo 1076618 1616321 := bstep (se 2 (by rfl) ⟨606120, by rfl⟩ : syracuseStep 1616321 = 1212241) B1212241
theorem B13838789 : Blo 1076618 13838789 := bstep (se 4 (by rfl) ⟨1297386, by rfl⟩ : syracuseStep 13838789 = 2594773) B2594773
theorem B2730449 : Blo 1076618 2730449 := bstep (se 2 (by rfl) ⟨1023918, by rfl⟩ : syracuseStep 2730449 = 2047837) B2047837
theorem B1616339 : Blo 1076618 1616339 := bstep (se 1 (by rfl) ⟨1212254, by rfl⟩ : syracuseStep 1616339 = 2424509) B2424509
theorem B1616369 : Blo 1076618 1616369 := bstep (se 2 (by rfl) ⟨606138, by rfl⟩ : syracuseStep 1616369 = 1212277) B1212277
theorem B1616387 : Blo 1076618 1616387 := bstep (se 1 (by rfl) ⟨1212290, by rfl⟩ : syracuseStep 1616387 = 2424581) B2424581
theorem B1616417 : Blo 1076618 1616417 := bstep (se 2 (by rfl) ⟨606156, by rfl⟩ : syracuseStep 1616417 = 1212313) B1212313
theorem B1616435 : Blo 1076618 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B1616465 : Blo 1076618 1616465 := bstep (se 2 (by rfl) ⟨606174, by rfl⟩ : syracuseStep 1616465 = 1212349) B1212349
theorem B1616483 : Blo 1076618 1616483 := bstep (se 1 (by rfl) ⟨1212362, by rfl⟩ : syracuseStep 1616483 = 2424725) B2424725
theorem B1616513 : Blo 1076618 1616513 := bstep (se 2 (by rfl) ⟨606192, by rfl⟩ : syracuseStep 1616513 = 1212385) B1212385
theorem B1616531 : Blo 1076618 1616531 := bstep (se 1 (by rfl) ⟨1212398, by rfl⟩ : syracuseStep 1616531 = 2424797) B2424797
theorem B1616561 : Blo 1076618 1616561 := bstep (se 2 (by rfl) ⟨606210, by rfl⟩ : syracuseStep 1616561 = 1212421) B1212421
theorem B1616579 : Blo 1076618 1616579 := bstep (se 1 (by rfl) ⟨1212434, by rfl⟩ : syracuseStep 1616579 = 2424869) B2424869
theorem B1616609 : Blo 1076618 1616609 := bstep (se 2 (by rfl) ⟨606228, by rfl⟩ : syracuseStep 1616609 = 1212457) B1212457
theorem B1616627 : Blo 1076618 1616627 := bstep (se 1 (by rfl) ⟨1212470, by rfl⟩ : syracuseStep 1616627 = 2424941) B2424941
theorem B2075395 : Blo 1076618 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1616657 : Blo 1076618 1616657 := bstep (se 2 (by rfl) ⟨606246, by rfl⟩ : syracuseStep 1616657 = 1212493) B1212493
theorem B1616675 : Blo 1076618 1616675 := bstep (se 1 (by rfl) ⟨1212506, by rfl⟩ : syracuseStep 1616675 = 2425013) B2425013
theorem B1616705 : Blo 1076618 1616705 := bstep (se 2 (by rfl) ⟨606264, by rfl⟩ : syracuseStep 1616705 = 1212529) B1212529
theorem B1616723 : Blo 1076618 1616723 := bstep (se 1 (by rfl) ⟨1212542, by rfl⟩ : syracuseStep 1616723 = 2425085) B2425085
theorem B1616753 : Blo 1076618 1616753 := bstep (se 2 (by rfl) ⟨606282, by rfl⟩ : syracuseStep 1616753 = 1212565) B1212565
theorem B1616771 : Blo 1076618 1616771 := bstep (se 1 (by rfl) ⟨1212578, by rfl⟩ : syracuseStep 1616771 = 2425157) B2425157
theorem B1616801 : Blo 1076618 1616801 := bstep (se 2 (by rfl) ⟨606300, by rfl⟩ : syracuseStep 1616801 = 1212601) B1212601
theorem B1616819 : Blo 1076618 1616819 := bstep (se 1 (by rfl) ⟨1212614, by rfl⟩ : syracuseStep 1616819 = 2425229) B2425229
theorem B1616849 : Blo 1076618 1616849 := bstep (se 2 (by rfl) ⟨606318, by rfl⟩ : syracuseStep 1616849 = 1212637) B1212637
theorem B1616867 : Blo 1076618 1616867 := bstep (se 1 (by rfl) ⟨1212650, by rfl⟩ : syracuseStep 1616867 = 2425301) B2425301
theorem B1616897 : Blo 1076618 1616897 := bstep (se 2 (by rfl) ⟨606336, by rfl⟩ : syracuseStep 1616897 = 1212673) B1212673
theorem B1846273 : Blo 1076618 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B1616915 : Blo 1076618 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1616945 : Blo 1076618 1616945 := bstep (se 2 (by rfl) ⟨606354, by rfl⟩ : syracuseStep 1616945 = 1212709) B1212709
theorem B1092659 : Blo 1076618 1092659 := bstep (se 1 (by rfl) ⟨819494, by rfl⟩ : syracuseStep 1092659 = 1638989) B1638989
theorem B1616963 : Blo 1076618 1616963 := bstep (se 1 (by rfl) ⟨1212722, by rfl⟩ : syracuseStep 1616963 = 2425445) B2425445
theorem B2305091 : Blo 1076618 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B1616993 : Blo 1076618 1616993 := bstep (se 2 (by rfl) ⟨606372, by rfl⟩ : syracuseStep 1616993 = 1212745) B1212745
theorem B1617011 : Blo 1076618 1617011 := bstep (se 1 (by rfl) ⟨1212758, by rfl⟩ : syracuseStep 1617011 = 2425517) B2425517
theorem B1617041 : Blo 1076618 1617041 := bstep (se 2 (by rfl) ⟨606390, by rfl⟩ : syracuseStep 1617041 = 1212781) B1212781
theorem B1617059 : Blo 1076618 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B2305201 : Blo 1076618 2305201 := bstep (se 2 (by rfl) ⟨864450, by rfl⟩ : syracuseStep 2305201 = 1728901) B1728901
theorem B1617089 : Blo 1076618 1617089 := bstep (se 2 (by rfl) ⟨606408, by rfl⟩ : syracuseStep 1617089 = 1212817) B1212817
theorem B1617107 : Blo 1076618 1617107 := bstep (se 1 (by rfl) ⟨1212830, by rfl⟩ : syracuseStep 1617107 = 2425661) B2425661
theorem B1617137 : Blo 1076618 1617137 := bstep (se 2 (by rfl) ⟨606426, by rfl⟩ : syracuseStep 1617137 = 1212853) B1212853
theorem B1617155 : Blo 1076618 1617155 := bstep (se 1 (by rfl) ⟨1212866, by rfl⟩ : syracuseStep 1617155 = 2425733) B2425733
theorem B1617185 : Blo 1076618 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B1617203 : Blo 1076618 1617203 := bstep (se 1 (by rfl) ⟨1212902, by rfl⟩ : syracuseStep 1617203 = 2425805) B2425805
theorem B1617233 : Blo 1076618 1617233 := bstep (se 2 (by rfl) ⟨606462, by rfl⟩ : syracuseStep 1617233 = 1212925) B1212925
theorem B4369763 : Blo 1076618 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B1617251 : Blo 1076618 1617251 := bstep (se 1 (by rfl) ⟨1212938, by rfl⟩ : syracuseStep 1617251 = 2425877) B2425877
theorem B1617281 : Blo 1076618 1617281 := bstep (se 2 (by rfl) ⟨606480, by rfl⟩ : syracuseStep 1617281 = 1212961) B1212961
theorem B1617299 : Blo 1076618 1617299 := bstep (se 1 (by rfl) ⟨1212974, by rfl⟩ : syracuseStep 1617299 = 2425949) B2425949
theorem B1617329 : Blo 1076618 1617329 := bstep (se 2 (by rfl) ⟨606498, by rfl⟩ : syracuseStep 1617329 = 1212997) B1212997
theorem B2731441 : Blo 1076618 2731441 := bstep (se 2 (by rfl) ⟨1024290, by rfl⟩ : syracuseStep 2731441 = 2048581) B2048581
theorem B1617347 : Blo 1076618 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B1617377 : Blo 1076618 1617377 := bstep (se 2 (by rfl) ⟨606516, by rfl⟩ : syracuseStep 1617377 = 1213033) B1213033
theorem B1617395 : Blo 1076618 1617395 := bstep (se 1 (by rfl) ⟨1213046, by rfl⟩ : syracuseStep 1617395 = 2426093) B2426093
theorem B3452419 : Blo 1076618 3452419 := bstep (se 1 (by rfl) ⟨2589314, by rfl⟩ : syracuseStep 3452419 = 5178629) B5178629
theorem B1617425 : Blo 1076618 1617425 := bstep (se 2 (by rfl) ⟨606534, by rfl⟩ : syracuseStep 1617425 = 1213069) B1213069
theorem B1846819 : Blo 1076618 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B5451299 : Blo 1076618 5451299 := bstep (se 1 (by rfl) ⟨4088474, by rfl⟩ : syracuseStep 5451299 = 8176949) B8176949
theorem B1617443 : Blo 1076618 1617443 := bstep (se 1 (by rfl) ⟨1213082, by rfl⟩ : syracuseStep 1617443 = 2426165) B2426165
theorem B15773237 : Blo 1076618 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B1617473 : Blo 1076618 1617473 := bstep (se 2 (by rfl) ⟨606552, by rfl⟩ : syracuseStep 1617473 = 1213105) B1213105
theorem B1617491 : Blo 1076618 1617491 := bstep (se 1 (by rfl) ⟨1213118, by rfl⟩ : syracuseStep 1617491 = 2426237) B2426237
theorem B1093219 : Blo 1076618 1093219 := bstep (se 1 (by rfl) ⟨819914, by rfl⟩ : syracuseStep 1093219 = 1639829) B1639829
theorem B1617521 : Blo 1076618 1617521 := bstep (se 2 (by rfl) ⟨606570, by rfl⟩ : syracuseStep 1617521 = 1213141) B1213141
theorem B1617539 : Blo 1076618 1617539 := bstep (se 1 (by rfl) ⟨1213154, by rfl⟩ : syracuseStep 1617539 = 2426309) B2426309
theorem B1617569 : Blo 1076618 1617569 := bstep (se 2 (by rfl) ⟨606588, by rfl⟩ : syracuseStep 1617569 = 1213177) B1213177
theorem B1617587 : Blo 1076618 1617587 := bstep (se 1 (by rfl) ⟨1213190, by rfl⟩ : syracuseStep 1617587 = 2426381) B2426381
theorem B2731715 : Blo 1076618 2731715 := bstep (se 1 (by rfl) ⟨2048786, by rfl⟩ : syracuseStep 2731715 = 4097573) B4097573
theorem B1617617 : Blo 1076618 1617617 := bstep (se 2 (by rfl) ⟨606606, by rfl⟩ : syracuseStep 1617617 = 1213213) B1213213
theorem B1617635 : Blo 1076618 1617635 := bstep (se 1 (by rfl) ⟨1213226, by rfl⟩ : syracuseStep 1617635 = 2426453) B2426453
theorem B1617665 : Blo 1076618 1617665 := bstep (se 2 (by rfl) ⟨606624, by rfl⟩ : syracuseStep 1617665 = 1213249) B1213249
theorem B1617683 : Blo 1076618 1617683 := bstep (se 1 (by rfl) ⟨1213262, by rfl⟩ : syracuseStep 1617683 = 2426525) B2426525
theorem B1617713 : Blo 1076618 1617713 := bstep (se 2 (by rfl) ⟨606642, by rfl⟩ : syracuseStep 1617713 = 1213285) B1213285
theorem B1617731 : Blo 1076618 1617731 := bstep (se 1 (by rfl) ⟨1213298, by rfl⟩ : syracuseStep 1617731 = 2426597) B2426597
theorem B1617761 : Blo 1076618 1617761 := bstep (se 2 (by rfl) ⟨606660, by rfl⟩ : syracuseStep 1617761 = 1213321) B1213321
theorem B1617779 : Blo 1076618 1617779 := bstep (se 1 (by rfl) ⟨1213334, by rfl⟩ : syracuseStep 1617779 = 2426669) B2426669
theorem B2731907 : Blo 1076618 2731907 := bstep (se 1 (by rfl) ⟨2048930, by rfl⟩ : syracuseStep 2731907 = 4097861) B4097861
theorem B1617809 : Blo 1076618 1617809 := bstep (se 2 (by rfl) ⟨606678, by rfl⟩ : syracuseStep 1617809 = 1213357) B1213357
theorem B1617827 : Blo 1076618 1617827 := bstep (se 1 (by rfl) ⟨1213370, by rfl⟩ : syracuseStep 1617827 = 2426741) B2426741
theorem B1617857 : Blo 1076618 1617857 := bstep (se 2 (by rfl) ⟨606696, by rfl⟩ : syracuseStep 1617857 = 1213393) B1213393
theorem B3452881 : Blo 1076618 3452881 := bstep (se 2 (by rfl) ⟨1294830, by rfl⟩ : syracuseStep 3452881 = 2589661) B2589661
theorem B1617875 : Blo 1076618 1617875 := bstep (se 1 (by rfl) ⟨1213406, by rfl⟩ : syracuseStep 1617875 = 2426813) B2426813
theorem B1617905 : Blo 1076618 1617905 := bstep (se 2 (by rfl) ⟨606714, by rfl⟩ : syracuseStep 1617905 = 1213429) B1213429
theorem B1617923 : Blo 1076618 1617923 := bstep (se 1 (by rfl) ⟨1213442, by rfl⟩ : syracuseStep 1617923 = 2426885) B2426885
theorem B1617953 : Blo 1076618 1617953 := bstep (se 2 (by rfl) ⟨606732, by rfl⟩ : syracuseStep 1617953 = 1213465) B1213465
theorem B1617971 : Blo 1076618 1617971 := bstep (se 1 (by rfl) ⟨1213478, by rfl⟩ : syracuseStep 1617971 = 2426957) B2426957
theorem B29503541 : Blo 1076618 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B1618001 : Blo 1076618 1618001 := bstep (se 2 (by rfl) ⟨606750, by rfl⟩ : syracuseStep 1618001 = 1213501) B1213501
theorem B1618019 : Blo 1076618 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B1618049 : Blo 1076618 1618049 := bstep (se 2 (by rfl) ⟨606768, by rfl⟩ : syracuseStep 1618049 = 1213537) B1213537
theorem B1618067 : Blo 1076618 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1618097 : Blo 1076618 1618097 := bstep (se 2 (by rfl) ⟨606786, by rfl⟩ : syracuseStep 1618097 = 1213573) B1213573
theorem B1618115 : Blo 1076618 1618115 := bstep (se 1 (by rfl) ⟨1213586, by rfl⟩ : syracuseStep 1618115 = 2427173) B2427173
theorem B1618145 : Blo 1076618 1618145 := bstep (se 2 (by rfl) ⟨606804, by rfl⟩ : syracuseStep 1618145 = 1213609) B1213609
theorem B20984035 : Blo 1076618 20984035 := bstep (se 1 (by rfl) ⟨15738026, by rfl⟩ : syracuseStep 20984035 = 31476053) B31476053
theorem B1618163 : Blo 1076618 1618163 := bstep (se 1 (by rfl) ⟨1213622, by rfl⟩ : syracuseStep 1618163 = 2427245) B2427245
theorem B1618193 : Blo 1076618 1618193 := bstep (se 2 (by rfl) ⟨606822, by rfl⟩ : syracuseStep 1618193 = 1213645) B1213645
theorem B1618211 : Blo 1076618 1618211 := bstep (se 1 (by rfl) ⟨1213658, by rfl⟩ : syracuseStep 1618211 = 2427317) B2427317
theorem B1618241 : Blo 1076618 1618241 := bstep (se 2 (by rfl) ⟨606840, by rfl⟩ : syracuseStep 1618241 = 1213681) B1213681
theorem B5452109 : Blo 1076618 5452109 := bstep (se 3 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 5452109 = 2044541) B2044541
theorem B1945937 : Blo 1076618 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B1618259 : Blo 1076618 1618259 := bstep (se 1 (by rfl) ⟨1213694, by rfl⟩ : syracuseStep 1618259 = 2427389) B2427389
theorem B1618289 : Blo 1076618 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B2044291 : Blo 1076618 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B1618307 : Blo 1076618 1618307 := bstep (se 1 (by rfl) ⟨1213730, by rfl⟩ : syracuseStep 1618307 = 2427461) B2427461
theorem B1618337 : Blo 1076618 1618337 := bstep (se 2 (by rfl) ⟨606876, by rfl⟩ : syracuseStep 1618337 = 1213753) B1213753
theorem B1618355 : Blo 1076618 1618355 := bstep (se 1 (by rfl) ⟨1213766, by rfl⟩ : syracuseStep 1618355 = 2427533) B2427533
theorem B1618385 : Blo 1076618 1618385 := bstep (se 2 (by rfl) ⟨606894, by rfl⟩ : syracuseStep 1618385 = 1213789) B1213789
theorem B1618403 : Blo 1076618 1618403 := bstep (se 1 (by rfl) ⟨1213802, by rfl⟩ : syracuseStep 1618403 = 2427605) B2427605
theorem B8761841 : Blo 1076618 8761841 := bstep (se 2 (by rfl) ⟨3285690, by rfl⟩ : syracuseStep 8761841 = 6571381) B6571381
theorem B1618433 : Blo 1076618 1618433 := bstep (se 2 (by rfl) ⟨606912, by rfl⟩ : syracuseStep 1618433 = 1213825) B1213825
theorem B1618451 : Blo 1076618 1618451 := bstep (se 1 (by rfl) ⟨1213838, by rfl⟩ : syracuseStep 1618451 = 2427677) B2427677
theorem B1618481 : Blo 1076618 1618481 := bstep (se 2 (by rfl) ⟨606930, by rfl⟩ : syracuseStep 1618481 = 1213861) B1213861
theorem B1618499 : Blo 1076618 1618499 := bstep (se 1 (by rfl) ⟨1213874, by rfl⟩ : syracuseStep 1618499 = 2427749) B2427749
theorem B1618529 : Blo 1076618 1618529 := bstep (se 2 (by rfl) ⟨606948, by rfl⟩ : syracuseStep 1618529 = 1213897) B1213897
theorem B1946225 : Blo 1076618 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B1618547 : Blo 1076618 1618547 := bstep (se 1 (by rfl) ⟨1213910, by rfl⟩ : syracuseStep 1618547 = 2427821) B2427821
theorem B6140549 : Blo 1076618 6140549 := bstep (se 4 (by rfl) ⟨575676, by rfl⟩ : syracuseStep 6140549 = 1151353) B1151353
theorem B1618577 : Blo 1076618 1618577 := bstep (se 2 (by rfl) ⟨606966, by rfl⟩ : syracuseStep 1618577 = 1213933) B1213933
theorem B1618595 : Blo 1076618 1618595 := bstep (se 1 (by rfl) ⟨1213946, by rfl⟩ : syracuseStep 1618595 = 2427893) B2427893
theorem B1618625 : Blo 1076618 1618625 := bstep (se 2 (by rfl) ⟨606984, by rfl⟩ : syracuseStep 1618625 = 1213969) B1213969
theorem B1618643 : Blo 1076618 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B2765539 : Blo 1076618 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B1618673 : Blo 1076618 1618673 := bstep (se 2 (by rfl) ⟨607002, by rfl⟩ : syracuseStep 1618673 = 1214005) B1214005
theorem B1618691 : Blo 1076618 1618691 := bstep (se 1 (by rfl) ⟨1214018, by rfl⟩ : syracuseStep 1618691 = 2428037) B2428037
theorem B1618721 : Blo 1076618 1618721 := bstep (se 2 (by rfl) ⟨607020, by rfl⟩ : syracuseStep 1618721 = 1214041) B1214041
theorem B2732849 : Blo 1076618 2732849 := bstep (se 2 (by rfl) ⟨1024818, by rfl⟩ : syracuseStep 2732849 = 2049637) B2049637
theorem B1618739 : Blo 1076618 1618739 := bstep (se 1 (by rfl) ⟨1214054, by rfl⟩ : syracuseStep 1618739 = 2428109) B2428109
theorem B2044739 : Blo 1076618 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B1618769 : Blo 1076618 1618769 := bstep (se 2 (by rfl) ⟨607038, by rfl⟩ : syracuseStep 1618769 = 1214077) B1214077
theorem B1618787 : Blo 1076618 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B2732899 : Blo 1076618 2732899 := bstep (se 1 (by rfl) ⟨2049674, by rfl⟩ : syracuseStep 2732899 = 4099349) B4099349
theorem B1618817 : Blo 1076618 1618817 := bstep (se 2 (by rfl) ⟨607056, by rfl⟩ : syracuseStep 1618817 = 1214113) B1214113
theorem B1618835 : Blo 1076618 1618835 := bstep (se 1 (by rfl) ⟨1214126, by rfl⟩ : syracuseStep 1618835 = 2428253) B2428253
theorem B1618865 : Blo 1076618 1618865 := bstep (se 2 (by rfl) ⟨607074, by rfl⟩ : syracuseStep 1618865 = 1214149) B1214149
theorem B1618883 : Blo 1076618 1618883 := bstep (se 1 (by rfl) ⟨1214162, by rfl⟩ : syracuseStep 1618883 = 2428325) B2428325
theorem B1618913 : Blo 1076618 1618913 := bstep (se 2 (by rfl) ⟨607092, by rfl⟩ : syracuseStep 1618913 = 1214185) B1214185
theorem B2733041 : Blo 1076618 2733041 := bstep (se 2 (by rfl) ⟨1024890, by rfl⟩ : syracuseStep 2733041 = 2049781) B2049781
theorem B1618931 : Blo 1076618 1618931 := bstep (se 1 (by rfl) ⟨1214198, by rfl⟩ : syracuseStep 1618931 = 2428397) B2428397
theorem B1618961 : Blo 1076618 1618961 := bstep (se 2 (by rfl) ⟨607110, by rfl⟩ : syracuseStep 1618961 = 1214221) B1214221
theorem B1618979 : Blo 1076618 1618979 := bstep (se 1 (by rfl) ⟨1214234, by rfl⟩ : syracuseStep 1618979 = 2428469) B2428469
theorem B1619009 : Blo 1076618 1619009 := bstep (se 2 (by rfl) ⟨607128, by rfl⟩ : syracuseStep 1619009 = 1214257) B1214257
theorem B6141005 : Blo 1076618 6141005 := bstep (se 3 (by rfl) ⟨1151438, by rfl⟩ : syracuseStep 6141005 = 2302877) B2302877
theorem B1619027 : Blo 1076618 1619027 := bstep (se 1 (by rfl) ⟨1214270, by rfl⟩ : syracuseStep 1619027 = 2428541) B2428541
theorem B2045027 : Blo 1076618 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B1619057 : Blo 1076618 1619057 := bstep (se 2 (by rfl) ⟨607146, by rfl⟩ : syracuseStep 1619057 = 1214293) B1214293
theorem B1455235 : Blo 1076618 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B1619075 : Blo 1076618 1619075 := bstep (se 1 (by rfl) ⟨1214306, by rfl⟩ : syracuseStep 1619075 = 2428613) B2428613
theorem B2307217 : Blo 1076618 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1619105 : Blo 1076618 1619105 := bstep (se 2 (by rfl) ⟨607164, by rfl⟩ : syracuseStep 1619105 = 1214329) B1214329
theorem B1619123 : Blo 1076618 1619123 := bstep (se 1 (by rfl) ⟨1214342, by rfl⟩ : syracuseStep 1619123 = 2428685) B2428685
theorem B1619153 : Blo 1076618 1619153 := bstep (se 2 (by rfl) ⟨607182, by rfl⟩ : syracuseStep 1619153 = 1214365) B1214365
theorem B1619171 : Blo 1076618 1619171 := bstep (se 1 (by rfl) ⟨1214378, by rfl⟩ : syracuseStep 1619171 = 2428757) B2428757
theorem B1619201 : Blo 1076618 1619201 := bstep (se 2 (by rfl) ⟨607200, by rfl⟩ : syracuseStep 1619201 = 1214401) B1214401
theorem B1619219 : Blo 1076618 1619219 := bstep (se 1 (by rfl) ⟨1214414, by rfl⟩ : syracuseStep 1619219 = 2428829) B2428829
theorem B1750307 : Blo 1076618 1750307 := bstep (se 1 (by rfl) ⟨1312730, by rfl⟩ : syracuseStep 1750307 = 2625461) B2625461
theorem B1619249 : Blo 1076618 1619249 := bstep (se 2 (by rfl) ⟨607218, by rfl⟩ : syracuseStep 1619249 = 1214437) B1214437
theorem B1619267 : Blo 1076618 1619267 := bstep (se 1 (by rfl) ⟨1214450, by rfl⟩ : syracuseStep 1619267 = 2428901) B2428901
theorem B1094995 : Blo 1076618 1094995 := bstep (se 1 (by rfl) ⟨821246, by rfl⟩ : syracuseStep 1094995 = 1642493) B1642493
theorem B1619297 : Blo 1076618 1619297 := bstep (se 2 (by rfl) ⟨607236, by rfl⟩ : syracuseStep 1619297 = 1214473) B1214473
theorem B1619315 : Blo 1076618 1619315 := bstep (se 1 (by rfl) ⟨1214486, by rfl⟩ : syracuseStep 1619315 = 2428973) B2428973
theorem B1619345 : Blo 1076618 1619345 := bstep (se 2 (by rfl) ⟨607254, by rfl⟩ : syracuseStep 1619345 = 1214509) B1214509
theorem B1619363 : Blo 1076618 1619363 := bstep (se 1 (by rfl) ⟨1214522, by rfl⟩ : syracuseStep 1619363 = 2429045) B2429045
theorem B1619393 : Blo 1076618 1619393 := bstep (se 2 (by rfl) ⟨607272, by rfl⟩ : syracuseStep 1619393 = 1214545) B1214545
theorem B1619411 : Blo 1076618 1619411 := bstep (se 1 (by rfl) ⟨1214558, by rfl⟩ : syracuseStep 1619411 = 2429117) B2429117
theorem B1619441 : Blo 1076618 1619441 := bstep (se 2 (by rfl) ⟨607290, by rfl⟩ : syracuseStep 1619441 = 1214581) B1214581
theorem B1619459 : Blo 1076618 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B12269069 : Blo 1076618 12269069 := bstep (se 3 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 12269069 = 4600901) B4600901
theorem B1619489 : Blo 1076618 1619489 := bstep (se 2 (by rfl) ⟨607308, by rfl⟩ : syracuseStep 1619489 = 1214617) B1214617
theorem B2307619 : Blo 1076618 2307619 := bstep (se 1 (by rfl) ⟨1730714, by rfl⟩ : syracuseStep 2307619 = 3461429) B3461429
theorem B1619507 : Blo 1076618 1619507 := bstep (se 1 (by rfl) ⟨1214630, by rfl⟩ : syracuseStep 1619507 = 2429261) B2429261
theorem B1619537 : Blo 1076618 1619537 := bstep (se 2 (by rfl) ⟨607326, by rfl⟩ : syracuseStep 1619537 = 1214653) B1214653
theorem B1619555 : Blo 1076618 1619555 := bstep (se 1 (by rfl) ⟨1214666, by rfl⟩ : syracuseStep 1619555 = 2429333) B2429333
theorem B1619585 : Blo 1076618 1619585 := bstep (se 2 (by rfl) ⟨607344, by rfl⟩ : syracuseStep 1619585 = 1214689) B1214689
theorem B1619603 : Blo 1076618 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B1619633 : Blo 1076618 1619633 := bstep (se 2 (by rfl) ⟨607362, by rfl⟩ : syracuseStep 1619633 = 1214725) B1214725
theorem B1619651 : Blo 1076618 1619651 := bstep (se 1 (by rfl) ⟨1214738, by rfl⟩ : syracuseStep 1619651 = 2429477) B2429477
theorem B1455841 : Blo 1076618 1455841 := bstep (se 2 (by rfl) ⟨545940, by rfl⟩ : syracuseStep 1455841 = 1091881) B1091881
theorem B1619681 : Blo 1076618 1619681 := bstep (se 2 (by rfl) ⟨607380, by rfl⟩ : syracuseStep 1619681 = 1214761) B1214761
theorem B4601585 : Blo 1076618 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1619699 : Blo 1076618 1619699 := bstep (se 1 (by rfl) ⟨1214774, by rfl⟩ : syracuseStep 1619699 = 2429549) B2429549
theorem B1619729 : Blo 1076618 1619729 := bstep (se 2 (by rfl) ⟨607398, by rfl⟩ : syracuseStep 1619729 = 1214797) B1214797
theorem B1619747 : Blo 1076618 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B1619777 : Blo 1076618 1619777 := bstep (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) B1214833
theorem B1619795 : Blo 1076618 1619795 := bstep (se 1 (by rfl) ⟨1214846, by rfl⟩ : syracuseStep 1619795 = 2429693) B2429693
theorem B1619825 : Blo 1076618 1619825 := bstep (se 2 (by rfl) ⟨607434, by rfl⟩ : syracuseStep 1619825 = 1214869) B1214869
theorem B1619843 : Blo 1076618 1619843 := bstep (se 1 (by rfl) ⟨1214882, by rfl⟩ : syracuseStep 1619843 = 2429765) B2429765
theorem B1619873 : Blo 1076618 1619873 := bstep (se 2 (by rfl) ⟨607452, by rfl⟩ : syracuseStep 1619873 = 1214905) B1214905
theorem B1619891 : Blo 1076618 1619891 := bstep (se 1 (by rfl) ⟨1214918, by rfl⟩ : syracuseStep 1619891 = 2429837) B2429837
theorem B1619921 : Blo 1076618 1619921 := bstep (se 2 (by rfl) ⟨607470, by rfl⟩ : syracuseStep 1619921 = 1214941) B1214941
theorem B2734033 : Blo 1076618 2734033 := bstep (se 2 (by rfl) ⟨1025262, by rfl⟩ : syracuseStep 2734033 = 2050525) B2050525
theorem B1619939 : Blo 1076618 1619939 := bstep (se 1 (by rfl) ⟨1214954, by rfl⟩ : syracuseStep 1619939 = 2429909) B2429909
theorem B1619969 : Blo 1076618 1619969 := bstep (se 2 (by rfl) ⟨607488, by rfl⟩ : syracuseStep 1619969 = 1214977) B1214977
theorem B2045969 : Blo 1076618 2045969 := bstep (se 2 (by rfl) ⟨767238, by rfl⟩ : syracuseStep 2045969 = 1534477) B1534477
theorem B1619987 : Blo 1076618 1619987 := bstep (se 1 (by rfl) ⟨1214990, by rfl⟩ : syracuseStep 1619987 = 2429981) B2429981
theorem B1620017 : Blo 1076618 1620017 := bstep (se 2 (by rfl) ⟨607506, by rfl⟩ : syracuseStep 1620017 = 1215013) B1215013
theorem B1620035 : Blo 1076618 1620035 := bstep (se 1 (by rfl) ⟨1215026, by rfl⟩ : syracuseStep 1620035 = 2430053) B2430053
theorem B1620065 : Blo 1076618 1620065 := bstep (se 2 (by rfl) ⟨607524, by rfl⟩ : syracuseStep 1620065 = 1215049) B1215049
theorem B1620083 : Blo 1076618 1620083 := bstep (se 1 (by rfl) ⟨1215062, by rfl⟩ : syracuseStep 1620083 = 2430125) B2430125
theorem B1620113 : Blo 1076618 1620113 := bstep (se 2 (by rfl) ⟨607542, by rfl⟩ : syracuseStep 1620113 = 1215085) B1215085
theorem B1620131 : Blo 1076618 1620131 := bstep (se 1 (by rfl) ⟨1215098, by rfl⟩ : syracuseStep 1620131 = 2430197) B2430197
theorem B2767025 : Blo 1076618 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B1620161 : Blo 1076618 1620161 := bstep (se 2 (by rfl) ⟨607560, by rfl⟩ : syracuseStep 1620161 = 1215121) B1215121
theorem B1620179 : Blo 1076618 1620179 := bstep (se 1 (by rfl) ⟨1215134, by rfl⟩ : syracuseStep 1620179 = 2430269) B2430269
theorem B2734307 : Blo 1076618 2734307 := bstep (se 1 (by rfl) ⟨2050730, by rfl⟩ : syracuseStep 2734307 = 4101461) B4101461
theorem B1620209 : Blo 1076618 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B1620227 : Blo 1076618 1620227 := bstep (se 1 (by rfl) ⟨1215170, by rfl⟩ : syracuseStep 1620227 = 2430341) B2430341
theorem B1620257 : Blo 1076618 1620257 := bstep (se 2 (by rfl) ⟨607596, by rfl⟩ : syracuseStep 1620257 = 1215193) B1215193
theorem B1620275 : Blo 1076618 1620275 := bstep (se 1 (by rfl) ⟨1215206, by rfl⟩ : syracuseStep 1620275 = 2430413) B2430413
theorem B1816897 : Blo 1076618 1816897 := bstep (se 2 (by rfl) ⟨681336, by rfl⟩ : syracuseStep 1816897 = 1362673) B1362673
theorem B1620305 : Blo 1076618 1620305 := bstep (se 2 (by rfl) ⟨607614, by rfl⟩ : syracuseStep 1620305 = 1215229) B1215229
theorem B1816931 : Blo 1076618 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B1620323 : Blo 1076618 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B23607665 : Blo 1076618 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B1620353 : Blo 1076618 1620353 := bstep (se 2 (by rfl) ⟨607632, by rfl⟩ : syracuseStep 1620353 = 1215265) B1215265
theorem B1620371 : Blo 1076618 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B2734499 : Blo 1076618 2734499 := bstep (se 1 (by rfl) ⟨2050874, by rfl⟩ : syracuseStep 2734499 = 4101749) B4101749
theorem B1620401 : Blo 1076618 1620401 := bstep (se 2 (by rfl) ⟨607650, by rfl⟩ : syracuseStep 1620401 = 1215301) B1215301
theorem B1620419 : Blo 1076618 1620419 := bstep (se 1 (by rfl) ⟨1215314, by rfl⟩ : syracuseStep 1620419 = 2430629) B2430629
theorem B1620449 : Blo 1076618 1620449 := bstep (se 2 (by rfl) ⟨607668, by rfl⟩ : syracuseStep 1620449 = 1215337) B1215337
theorem B1817059 : Blo 1076618 1817059 := bstep (se 1 (by rfl) ⟨1362794, by rfl⟩ : syracuseStep 1817059 = 2725589) B2725589
theorem B1620467 : Blo 1076618 1620467 := bstep (se 1 (by rfl) ⟨1215350, by rfl⟩ : syracuseStep 1620467 = 2430701) B2430701
theorem B2243089 : Blo 1076618 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B1620497 : Blo 1076618 1620497 := bstep (se 2 (by rfl) ⟨607686, by rfl⟩ : syracuseStep 1620497 = 1215373) B1215373
theorem B1620515 : Blo 1076618 1620515 := bstep (se 1 (by rfl) ⟨1215386, by rfl⟩ : syracuseStep 1620515 = 2430773) B2430773
theorem B1620545 : Blo 1076618 1620545 := bstep (se 2 (by rfl) ⟨607704, by rfl⟩ : syracuseStep 1620545 = 1215409) B1215409
theorem B1620563 : Blo 1076618 1620563 := bstep (se 1 (by rfl) ⟨1215422, by rfl⟩ : syracuseStep 1620563 = 2430845) B2430845
theorem B2767459 : Blo 1076618 2767459 := bstep (se 1 (by rfl) ⟨2075594, by rfl⟩ : syracuseStep 2767459 = 4151189) B4151189
theorem B3455597 : Blo 1076618 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B1817201 : Blo 1076618 1817201 := bstep (se 2 (by rfl) ⟨681450, by rfl⟩ : syracuseStep 1817201 = 1362901) B1362901
theorem B1620593 : Blo 1076618 1620593 := bstep (se 2 (by rfl) ⟨607722, by rfl⟩ : syracuseStep 1620593 = 1215445) B1215445
theorem B1620611 : Blo 1076618 1620611 := bstep (se 1 (by rfl) ⟨1215458, by rfl⟩ : syracuseStep 1620611 = 2430917) B2430917
theorem B1620641 : Blo 1076618 1620641 := bstep (se 2 (by rfl) ⟨607740, by rfl⟩ : syracuseStep 1620641 = 1215481) B1215481
theorem B1620659 : Blo 1076618 1620659 := bstep (se 1 (by rfl) ⟨1215494, by rfl⟩ : syracuseStep 1620659 = 2430989) B2430989
theorem B1620689 : Blo 1076618 1620689 := bstep (se 2 (by rfl) ⟨607758, by rfl⟩ : syracuseStep 1620689 = 1215517) B1215517
theorem B1620707 : Blo 1076618 1620707 := bstep (se 1 (by rfl) ⟨1215530, by rfl⟩ : syracuseStep 1620707 = 2431061) B2431061
theorem B1817329 : Blo 1076618 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B1620737 : Blo 1076618 1620737 := bstep (se 2 (by rfl) ⟨607776, by rfl⟩ : syracuseStep 1620737 = 1215553) B1215553
theorem B1817363 : Blo 1076618 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B1620755 : Blo 1076618 1620755 := bstep (se 1 (by rfl) ⟨1215566, by rfl⟩ : syracuseStep 1620755 = 2431133) B2431133
theorem B1620785 : Blo 1076618 1620785 := bstep (se 2 (by rfl) ⟨607794, by rfl⟩ : syracuseStep 1620785 = 1215589) B1215589
theorem B1620803 : Blo 1076618 1620803 := bstep (se 1 (by rfl) ⟨1215602, by rfl⟩ : syracuseStep 1620803 = 2431205) B2431205
theorem B1620833 : Blo 1076618 1620833 := bstep (se 2 (by rfl) ⟨607812, by rfl⟩ : syracuseStep 1620833 = 1215625) B1215625
theorem B1620851 : Blo 1076618 1620851 := bstep (se 1 (by rfl) ⟨1215638, by rfl⟩ : syracuseStep 1620851 = 2431277) B2431277
theorem B2046865 : Blo 1076618 2046865 := bstep (se 2 (by rfl) ⟨767574, by rfl⟩ : syracuseStep 2046865 = 1535149) B1535149
theorem B1620881 : Blo 1076618 1620881 := bstep (se 2 (by rfl) ⟨607830, by rfl⟩ : syracuseStep 1620881 = 1215661) B1215661
theorem B1817491 : Blo 1076618 1817491 := bstep (se 1 (by rfl) ⟨1363118, by rfl⟩ : syracuseStep 1817491 = 2726237) B2726237
theorem B1620899 : Blo 1076618 1620899 := bstep (se 1 (by rfl) ⟨1215674, by rfl⟩ : syracuseStep 1620899 = 2431349) B2431349
theorem B3685315 : Blo 1076618 3685315 := bstep (se 1 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 3685315 = 5527973) B5527973
theorem B4602851 : Blo 1076618 4602851 := bstep (se 1 (by rfl) ⟨3452138, by rfl⟩ : syracuseStep 4602851 = 6904277) B6904277
theorem B1817633 : Blo 1076618 1817633 := bstep (se 2 (by rfl) ⟨681612, by rfl⟩ : syracuseStep 1817633 = 1363225) B1363225
theorem B2047025 : Blo 1076618 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B1293427 : Blo 1076618 1293427 := bstep (se 1 (by rfl) ⟨970070, by rfl⟩ : syracuseStep 1293427 = 1940141) B1940141
theorem B1817761 : Blo 1076618 1817761 := bstep (se 2 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 1817761 = 1363321) B1363321
theorem B5455025 : Blo 1076618 5455025 := bstep (se 2 (by rfl) ⟨2045634, by rfl⟩ : syracuseStep 5455025 = 4091269) B4091269
theorem B1817795 : Blo 1076618 1817795 := bstep (se 1 (by rfl) ⟨1363346, by rfl⟩ : syracuseStep 1817795 = 2726693) B2726693
theorem B1817923 : Blo 1076618 1817923 := bstep (se 1 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 1817923 = 2726885) B2726885
theorem B2047427 : Blo 1076618 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B1818065 : Blo 1076618 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B24952373 : Blo 1076618 24952373 := bstep (se 5 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 24952373 = 2339285) B2339285
theorem B1818193 : Blo 1076618 1818193 := bstep (se 2 (by rfl) ⟨681822, by rfl⟩ : syracuseStep 1818193 = 1363645) B1363645
theorem B1818227 : Blo 1076618 1818227 := bstep (se 1 (by rfl) ⟨1363670, by rfl⟩ : syracuseStep 1818227 = 2727341) B2727341
theorem B1818355 : Blo 1076618 1818355 := bstep (se 1 (by rfl) ⟨1363766, by rfl⟩ : syracuseStep 1818355 = 2727533) B2727533
theorem B1752931 : Blo 1076618 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B1818497 : Blo 1076618 1818497 := bstep (se 2 (by rfl) ⟨681936, by rfl⟩ : syracuseStep 1818497 = 1363873) B1363873
theorem B6143921 : Blo 1076618 6143921 := bstep (se 2 (by rfl) ⟨2303970, by rfl⟩ : syracuseStep 6143921 = 4607941) B4607941
theorem B17514467 : Blo 1076618 17514467 := bstep (se 1 (by rfl) ⟨13135850, by rfl⟩ : syracuseStep 17514467 = 26271701) B26271701
theorem B1818625 : Blo 1076618 1818625 := bstep (se 2 (by rfl) ⟨681984, by rfl⟩ : syracuseStep 1818625 = 1363969) B1363969
theorem B1818659 : Blo 1076618 1818659 := bstep (se 1 (by rfl) ⟨1363994, by rfl⟩ : syracuseStep 1818659 = 2727989) B2727989
theorem B1294499 : Blo 1076618 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B1818787 : Blo 1076618 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B3457187 : Blo 1076618 3457187 := bstep (se 1 (by rfl) ⟨2592890, by rfl⟩ : syracuseStep 3457187 = 5185781) B5185781
theorem B1818929 : Blo 1076618 1818929 := bstep (se 2 (by rfl) ⟨682098, by rfl⟩ : syracuseStep 1818929 = 1364197) B1364197
theorem B2048323 : Blo 1076618 2048323 := bstep (se 1 (by rfl) ⟨1536242, by rfl⟩ : syracuseStep 2048323 = 3072485) B3072485
theorem B12271985 : Blo 1076618 12271985 := bstep (se 2 (by rfl) ⟨4601994, by rfl⟩ : syracuseStep 12271985 = 9203989) B9203989
theorem B1458577 : Blo 1076618 1458577 := bstep (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) B1093933
theorem B1819057 : Blo 1076618 1819057 := bstep (se 2 (by rfl) ⟨682146, by rfl⟩ : syracuseStep 1819057 = 1364293) B1364293
theorem B1819091 : Blo 1076618 1819091 := bstep (se 1 (by rfl) ⟨1364318, by rfl⟩ : syracuseStep 1819091 = 2728637) B2728637
theorem B1753555 : Blo 1076618 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B2048483 : Blo 1076618 2048483 := bstep (se 1 (by rfl) ⟨1536362, by rfl⟩ : syracuseStep 2048483 = 3072725) B3072725
theorem B1458739 : Blo 1076618 1458739 := bstep (se 1 (by rfl) ⟨1094054, by rfl⟩ : syracuseStep 1458739 = 2188109) B2188109
theorem B1819219 : Blo 1076618 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B5456483 : Blo 1076618 5456483 := bstep (se 1 (by rfl) ⟨4092362, by rfl⟩ : syracuseStep 5456483 = 8184725) B8184725
theorem B1819361 : Blo 1076618 1819361 := bstep (se 2 (by rfl) ⟨682260, by rfl⟩ : syracuseStep 1819361 = 1364521) B1364521
theorem B1458977 : Blo 1076618 1458977 := bstep (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) B1094233
theorem B1819489 : Blo 1076618 1819489 := bstep (se 2 (by rfl) ⟨682308, by rfl⟩ : syracuseStep 1819489 = 1364617) B1364617
theorem B1819523 : Blo 1076618 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B1459139 : Blo 1076618 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B1819651 : Blo 1076618 1819651 := bstep (se 1 (by rfl) ⟨1364738, by rfl⟩ : syracuseStep 1819651 = 2729477) B2729477
theorem B17712269 : Blo 1076618 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B1819793 : Blo 1076618 1819793 := bstep (se 2 (by rfl) ⟨682422, by rfl⟩ : syracuseStep 1819793 = 1364845) B1364845
theorem B1819921 : Blo 1076618 1819921 := bstep (se 2 (by rfl) ⟨682470, by rfl⟩ : syracuseStep 1819921 = 1364941) B1364941
theorem B1819955 : Blo 1076618 1819955 := bstep (se 1 (by rfl) ⟨1364966, by rfl⟩ : syracuseStep 1819955 = 2729933) B2729933
theorem B11060549 : Blo 1076618 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B6145379 : Blo 1076618 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B5457293 : Blo 1076618 5457293 := bstep (se 3 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 5457293 = 2046485) B2046485
theorem B3458467 : Blo 1076618 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B1820083 : Blo 1076618 1820083 := bstep (se 1 (by rfl) ⟨1365062, by rfl⟩ : syracuseStep 1820083 = 2730125) B2730125
theorem B6571525 : Blo 1076618 6571525 := bstep (se 4 (by rfl) ⟨616080, by rfl⟩ : syracuseStep 6571525 = 1232161) B1232161
theorem B2049553 : Blo 1076618 2049553 := bstep (se 2 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 2049553 = 1537165) B1537165
theorem B1459729 : Blo 1076618 1459729 := bstep (se 2 (by rfl) ⟨547398, by rfl⟩ : syracuseStep 1459729 = 1094797) B1094797
theorem B1820225 : Blo 1076618 1820225 := bstep (se 2 (by rfl) ⟨682584, by rfl⟩ : syracuseStep 1820225 = 1365169) B1365169
theorem B1459777 : Blo 1076618 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B1820353 : Blo 1076618 1820353 := bstep (se 2 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 1820353 = 1365265) B1365265
theorem B1820387 : Blo 1076618 1820387 := bstep (se 1 (by rfl) ⟨1365290, by rfl⟩ : syracuseStep 1820387 = 2730581) B2730581
theorem B3458801 : Blo 1076618 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B1820515 : Blo 1076618 1820515 := bstep (se 1 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 1820515 = 2730773) B2730773
theorem B1820657 : Blo 1076618 1820657 := bstep (se 2 (by rfl) ⟨682746, by rfl⟩ : syracuseStep 1820657 = 1365493) B1365493
theorem B3885155 : Blo 1076618 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B1820785 : Blo 1076618 1820785 := bstep (se 2 (by rfl) ⟨682794, by rfl⟩ : syracuseStep 1820785 = 1365589) B1365589
theorem B1820819 : Blo 1076618 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B6899917 : Blo 1076618 6899917 := bstep (se 3 (by rfl) ⟨1293734, by rfl⟩ : syracuseStep 6899917 = 2587469) B2587469
theorem B3066083 : Blo 1076618 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1820947 : Blo 1076618 1820947 := bstep (se 1 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 1820947 = 2731421) B2731421
theorem B6146381 : Blo 1076618 6146381 := bstep (se 3 (by rfl) ⟨1152446, by rfl⟩ : syracuseStep 6146381 = 2304893) B2304893
theorem B1821089 : Blo 1076618 1821089 := bstep (se 2 (by rfl) ⟨682908, by rfl⟩ : syracuseStep 1821089 = 1365817) B1365817
theorem B1165763 : Blo 1076618 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B4377059 : Blo 1076618 4377059 := bstep (se 1 (by rfl) ⟨3282794, by rfl⟩ : syracuseStep 4377059 = 6565589) B6565589
theorem B1821217 : Blo 1076618 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B2050609 : Blo 1076618 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B1821251 : Blo 1076618 1821251 := bstep (se 1 (by rfl) ⟨1365938, by rfl⟩ : syracuseStep 1821251 = 2731877) B2731877
theorem B4606541 : Blo 1076618 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B1821379 : Blo 1076618 1821379 := bstep (se 1 (by rfl) ⟨1366034, by rfl⟩ : syracuseStep 1821379 = 2732069) B2732069
theorem B1362739 : Blo 1076618 1362739 := bstep (se 1 (by rfl) ⟨1022054, by rfl⟩ : syracuseStep 1362739 = 2044109) B2044109
theorem B1821521 : Blo 1076618 1821521 := bstep (se 2 (by rfl) ⟨683070, by rfl⟩ : syracuseStep 1821521 = 1366141) B1366141
theorem B1362835 : Blo 1076618 1362835 := bstep (se 1 (by rfl) ⟨1022126, by rfl⟩ : syracuseStep 1362835 = 2044253) B2044253
theorem B2051011 : Blo 1076618 2051011 := bstep (se 1 (by rfl) ⟨1538258, by rfl⟩ : syracuseStep 2051011 = 3076517) B3076517
theorem B1821649 : Blo 1076618 1821649 := bstep (se 2 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 1821649 = 1366237) B1366237
theorem B2051057 : Blo 1076618 2051057 := bstep (se 2 (by rfl) ⟨769146, by rfl⟩ : syracuseStep 2051057 = 1538293) B1538293
theorem B1821683 : Blo 1076618 1821683 := bstep (se 1 (by rfl) ⟨1366262, by rfl⟩ : syracuseStep 1821683 = 2732525) B2732525
theorem B3066893 : Blo 1076618 3066893 := bstep (se 3 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 3066893 = 1150085) B1150085
theorem B1231939 : Blo 1076618 1231939 := bstep (se 1 (by rfl) ⟨923954, by rfl⟩ : syracuseStep 1231939 = 1847909) B1847909
theorem B23645297 : Blo 1076618 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B3329137 : Blo 1076618 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B1821811 : Blo 1076618 1821811 := bstep (se 1 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 1821811 = 2732717) B2732717
theorem B3067085 : Blo 1076618 3067085 := bstep (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) B1150157
theorem B1821953 : Blo 1076618 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B2051345 : Blo 1076618 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B1822081 : Blo 1076618 1822081 := bstep (se 2 (by rfl) ⟨683280, by rfl⟩ : syracuseStep 1822081 = 1366561) B1366561
theorem B1363331 : Blo 1076618 1363331 := bstep (se 1 (by rfl) ⟨1022498, by rfl⟩ : syracuseStep 1363331 = 2044997) B2044997
theorem B1822115 : Blo 1076618 1822115 := bstep (se 1 (by rfl) ⟨1366586, by rfl⟩ : syracuseStep 1822115 = 2733173) B2733173
theorem B4378097 : Blo 1076618 4378097 := bstep (se 2 (by rfl) ⟨1641786, by rfl⟩ : syracuseStep 4378097 = 3283573) B3283573
theorem B1822243 : Blo 1076618 1822243 := bstep (se 1 (by rfl) ⟨1366682, by rfl⟩ : syracuseStep 1822243 = 2733365) B2733365
theorem B1822385 : Blo 1076618 1822385 := bstep (se 2 (by rfl) ⟨683394, by rfl⟩ : syracuseStep 1822385 = 1366789) B1366789
theorem B3460877 : Blo 1076618 3460877 := bstep (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) B1297829
theorem B1822513 : Blo 1076618 1822513 := bstep (se 2 (by rfl) ⟨683442, by rfl⟩ : syracuseStep 1822513 = 1366885) B1366885
theorem B1822547 : Blo 1076618 1822547 := bstep (se 1 (by rfl) ⟨1366910, by rfl⟩ : syracuseStep 1822547 = 2733821) B2733821
theorem B1822675 : Blo 1076618 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B4673585 : Blo 1076618 4673585 := bstep (se 2 (by rfl) ⟨1752594, by rfl⟩ : syracuseStep 4673585 = 3505189) B3505189
theorem B1364035 : Blo 1076618 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B1822817 : Blo 1076618 1822817 := bstep (se 2 (by rfl) ⟨683556, by rfl⟩ : syracuseStep 1822817 = 1367113) B1367113
theorem B1364131 : Blo 1076618 1364131 := bstep (se 1 (by rfl) ⟨1023098, by rfl⟩ : syracuseStep 1364131 = 2046197) B2046197
theorem B3068077 : Blo 1076618 3068077 := bstep (se 3 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 3068077 = 1150529) B1150529
theorem B1822945 : Blo 1076618 1822945 := bstep (se 2 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 1822945 = 1367209) B1367209
theorem B5460209 : Blo 1076618 5460209 := bstep (se 2 (by rfl) ⟨2047578, by rfl⟩ : syracuseStep 5460209 = 4095157) B4095157
theorem B1822979 : Blo 1076618 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B1823107 : Blo 1076618 1823107 := bstep (se 1 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 1823107 = 2734661) B2734661
theorem B1823249 : Blo 1076618 1823249 := bstep (se 2 (by rfl) ⟨683718, by rfl⟩ : syracuseStep 1823249 = 1367437) B1367437
theorem B1724993 : Blo 1076618 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B1823377 : Blo 1076618 1823377 := bstep (se 2 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 1823377 = 1367533) B1367533
theorem B1364627 : Blo 1076618 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B1823411 : Blo 1076618 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1725185 : Blo 1076618 1725185 := bstep (se 2 (by rfl) ⟨646944, by rfl⟩ : syracuseStep 1725185 = 1293889) B1293889
theorem B1823539 : Blo 1076618 1823539 := bstep (se 1 (by rfl) ⟨1367654, by rfl⟩ : syracuseStep 1823539 = 2735309) B2735309
theorem B1725313 : Blo 1076618 1725313 := bstep (se 2 (by rfl) ⟨646992, by rfl⟩ : syracuseStep 1725313 = 1293985) B1293985
theorem B6149297 : Blo 1076618 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B1365331 : Blo 1076618 1365331 := bstep (se 1 (by rfl) ⟨1023998, by rfl⟩ : syracuseStep 1365331 = 2047997) B2047997
theorem B1365427 : Blo 1076618 1365427 := bstep (se 1 (by rfl) ⟨1024070, by rfl⟩ : syracuseStep 1365427 = 2048141) B2048141
theorem B1725953 : Blo 1076618 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B8869475 : Blo 1076618 8869475 := bstep (se 1 (by rfl) ⟨6652106, by rfl⟩ : syracuseStep 8869475 = 13304213) B13304213
theorem B4609649 : Blo 1076618 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B5461667 : Blo 1076618 5461667 := bstep (se 1 (by rfl) ⟨4096250, by rfl⟩ : syracuseStep 5461667 = 8192501) B8192501
theorem B4675313 : Blo 1076618 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B2184995 : Blo 1076618 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B3069809 : Blo 1076618 3069809 := bstep (se 2 (by rfl) ⟨1151178, by rfl⟩ : syracuseStep 3069809 = 2302357) B2302357
theorem B1365923 : Blo 1076618 1365923 := bstep (se 1 (by rfl) ⟨1024442, by rfl⟩ : syracuseStep 1365923 = 2048885) B2048885
theorem B3070001 : Blo 1076618 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B4610317 : Blo 1076618 4610317 := bstep (se 3 (by rfl) ⟨864434, by rfl⟩ : syracuseStep 4610317 = 1728869) B1728869
theorem B5462477 : Blo 1076618 5462477 := bstep (se 3 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 5462477 = 2048429) B2048429
theorem B1366627 : Blo 1076618 1366627 := bstep (se 1 (by rfl) ⟨1024970, by rfl⟩ : syracuseStep 1366627 = 2049941) B2049941
theorem B6150755 : Blo 1076618 6150755 := bstep (se 1 (by rfl) ⟨4613066, by rfl⟩ : syracuseStep 6150755 = 9226133) B9226133
theorem B1366723 : Blo 1076618 1366723 := bstep (se 1 (by rfl) ⟨1025042, by rfl⟩ : syracuseStep 1366723 = 2050085) B2050085
theorem B4610915 : Blo 1076618 4610915 := bstep (se 1 (by rfl) ⟨3458186, by rfl⟩ : syracuseStep 4610915 = 6916373) B6916373
theorem B1727363 : Blo 1076618 1727363 := bstep (se 1 (by rfl) ⟨1295522, by rfl⟩ : syracuseStep 1727363 = 2591045) B2591045
theorem B1727491 : Blo 1076618 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B3070993 : Blo 1076618 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B1367219 : Blo 1076618 1367219 := bstep (se 1 (by rfl) ⟨1025414, by rfl⟩ : syracuseStep 1367219 = 2050829) B2050829
theorem B3071267 : Blo 1076618 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B5823971 : Blo 1076618 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B8183267 : Blo 1076618 8183267 := bstep (se 1 (by rfl) ⟨6137450, by rfl⟩ : syracuseStep 8183267 = 12274901) B12274901
theorem B3071459 : Blo 1076618 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B1728049 : Blo 1076618 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B1498771 : Blo 1076618 1498771 := bstep (se 1 (by rfl) ⟨1124078, by rfl⟩ : syracuseStep 1498771 = 2248157) B2248157
theorem B27648053 : Blo 1076618 27648053 := bstep (se 5 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 27648053 = 2592005) B2592005
theorem B2187395 : Blo 1076618 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B3891341 : Blo 1076618 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B1728721 : Blo 1076618 1728721 := bstep (se 2 (by rfl) ⟨648270, by rfl⟩ : syracuseStep 1728721 = 1296541) B1296541
theorem B3072269 : Blo 1076618 3072269 := bstep (se 3 (by rfl) ⟨576050, by rfl⟩ : syracuseStep 3072269 = 1152101) B1152101
theorem B4088141 : Blo 1076618 4088141 := bstep (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) B1533053
theorem B3072451 : Blo 1076618 3072451 := bstep (se 1 (by rfl) ⟨2304338, by rfl⟩ : syracuseStep 3072451 = 4608677) B4608677
theorem B5825357 : Blo 1076618 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B3072941 : Blo 1076618 3072941 := bstep (se 3 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 3072941 = 1152353) B1152353
theorem B1369043 : Blo 1076618 1369043 := bstep (se 1 (by rfl) ⟨1026782, by rfl⟩ : syracuseStep 1369043 = 2053565) B2053565
theorem B1598467 : Blo 1076618 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B1532945 : Blo 1076618 1532945 := bstep (se 2 (by rfl) ⟨574854, by rfl⟩ : syracuseStep 1532945 = 1149709) B1149709
theorem B3695825 : Blo 1076618 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B1729811 : Blo 1076618 1729811 := bstep (se 1 (by rfl) ⟨1297358, by rfl⟩ : syracuseStep 1729811 = 2594717) B2594717
theorem B5465393 : Blo 1076618 5465393 := bstep (se 2 (by rfl) ⟨2049522, by rfl⟩ : syracuseStep 5465393 = 4099045) B4099045
theorem B3892621 : Blo 1076618 3892621 := bstep (se 3 (by rfl) ⟨729866, by rfl⟩ : syracuseStep 3892621 = 1459733) B1459733
theorem B1533811 : Blo 1076618 1533811 := bstep (se 1 (by rfl) ⟨1150358, by rfl⟩ : syracuseStep 1533811 = 2300717) B2300717
theorem B1533907 : Blo 1076618 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B3074125 : Blo 1076618 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B14772365 : Blo 1076618 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B10381553 : Blo 1076618 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B6908323 : Blo 1076618 6908323 := bstep (se 1 (by rfl) ⟨5181242, by rfl⟩ : syracuseStep 6908323 = 10362485) B10362485
theorem B1534403 : Blo 1076618 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B6220273 : Blo 1076618 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B5827085 : Blo 1076618 5827085 := bstep (se 3 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 5827085 = 2185157) B2185157
theorem B4614691 : Blo 1076618 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B5466851 : Blo 1076618 5466851 := bstep (se 1 (by rfl) ⟨4100138, by rfl⟩ : syracuseStep 5466851 = 8200277) B8200277
theorem B6548273 : Blo 1076618 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B1535041 : Blo 1076618 1535041 := bstep (se 2 (by rfl) ⟨575640, by rfl⟩ : syracuseStep 1535041 = 1151281) B1151281
theorem B3075185 : Blo 1076618 3075185 := bstep (se 2 (by rfl) ⟨1153194, by rfl⟩ : syracuseStep 3075185 = 2306389) B2306389
theorem B4091057 : Blo 1076618 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B2911619 : Blo 1076618 2911619 := bstep (se 1 (by rfl) ⟨2183714, by rfl⟩ : syracuseStep 2911619 = 4367429) B4367429
theorem B5533069 : Blo 1076618 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B1535377 : Blo 1076618 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1076627 : Blo 1076618 1076627 := bstep (se 1 (by rfl) ⟨807470, by rfl⟩ : syracuseStep 1076627 = 1614941) B1614941
theorem B1076643 : Blo 1076618 1076643 := bstep (se 1 (by rfl) ⟨807482, by rfl⟩ : syracuseStep 1076643 = 1614965) B1614965
theorem B1076659 : Blo 1076618 1076659 := bstep (se 1 (by rfl) ⟨807494, by rfl⟩ : syracuseStep 1076659 = 1614989) B1614989
theorem B1076675 : Blo 1076618 1076675 := bstep (se 1 (by rfl) ⟨807506, by rfl⟩ : syracuseStep 1076675 = 1615013) B1615013
theorem B1076691 : Blo 1076618 1076691 := bstep (se 1 (by rfl) ⟨807518, by rfl⟩ : syracuseStep 1076691 = 1615037) B1615037
theorem B1076707 : Blo 1076618 1076707 := bstep (se 1 (by rfl) ⟨807530, by rfl⟩ : syracuseStep 1076707 = 1615061) B1615061
theorem B1076723 : Blo 1076618 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1076739 : Blo 1076618 1076739 := bstep (se 1 (by rfl) ⟨807554, by rfl⟩ : syracuseStep 1076739 = 1615109) B1615109
theorem B5467661 : Blo 1076618 5467661 := bstep (se 3 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 5467661 = 2050373) B2050373
theorem B1076755 : Blo 1076618 1076755 := bstep (se 1 (by rfl) ⟨807566, by rfl⟩ : syracuseStep 1076755 = 1615133) B1615133
theorem B1076771 : Blo 1076618 1076771 := bstep (se 1 (by rfl) ⟨807578, by rfl⟩ : syracuseStep 1076771 = 1615157) B1615157
theorem B1076787 : Blo 1076618 1076787 := bstep (se 1 (by rfl) ⟨807590, by rfl⟩ : syracuseStep 1076787 = 1615181) B1615181
theorem B1076803 : Blo 1076618 1076803 := bstep (se 1 (by rfl) ⟨807602, by rfl⟩ : syracuseStep 1076803 = 1615205) B1615205
theorem B1076819 : Blo 1076618 1076819 := bstep (se 1 (by rfl) ⟨807614, by rfl⟩ : syracuseStep 1076819 = 1615229) B1615229
theorem B1076835 : Blo 1076618 1076835 := bstep (se 1 (by rfl) ⟨807626, by rfl⟩ : syracuseStep 1076835 = 1615253) B1615253
theorem B6909553 : Blo 1076618 6909553 := bstep (se 2 (by rfl) ⟨2591082, by rfl⟩ : syracuseStep 6909553 = 5182165) B5182165
theorem B1076851 : Blo 1076618 1076851 := bstep (se 1 (by rfl) ⟨807638, by rfl⟩ : syracuseStep 1076851 = 1615277) B1615277
theorem B1076867 : Blo 1076618 1076867 := bstep (se 1 (by rfl) ⟨807650, by rfl⟩ : syracuseStep 1076867 = 1615301) B1615301
theorem B1076883 : Blo 1076618 1076883 := bstep (se 1 (by rfl) ⟨807662, by rfl⟩ : syracuseStep 1076883 = 1615325) B1615325
theorem B1076899 : Blo 1076618 1076899 := bstep (se 1 (by rfl) ⟨807674, by rfl⟩ : syracuseStep 1076899 = 1615349) B1615349
theorem B1076915 : Blo 1076618 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B1076931 : Blo 1076618 1076931 := bstep (se 1 (by rfl) ⟨807698, by rfl⟩ : syracuseStep 1076931 = 1615397) B1615397
theorem B1076947 : Blo 1076618 1076947 := bstep (se 1 (by rfl) ⟨807710, by rfl⟩ : syracuseStep 1076947 = 1615421) B1615421
theorem B1076963 : Blo 1076618 1076963 := bstep (se 1 (by rfl) ⟨807722, by rfl⟩ : syracuseStep 1076963 = 1615445) B1615445
theorem B1076979 : Blo 1076618 1076979 := bstep (se 1 (by rfl) ⟨807734, by rfl⟩ : syracuseStep 1076979 = 1615469) B1615469
theorem B1076995 : Blo 1076618 1076995 := bstep (se 1 (by rfl) ⟨807746, by rfl⟩ : syracuseStep 1076995 = 1615493) B1615493
theorem B3075857 : Blo 1076618 3075857 := bstep (se 2 (by rfl) ⟨1153446, by rfl⟩ : syracuseStep 3075857 = 2306893) B2306893
theorem B1077011 : Blo 1076618 1077011 := bstep (se 1 (by rfl) ⟨807758, by rfl⟩ : syracuseStep 1077011 = 1615517) B1615517
theorem B1077027 : Blo 1076618 1077027 := bstep (se 1 (by rfl) ⟨807770, by rfl⟩ : syracuseStep 1077027 = 1615541) B1615541
theorem B1077043 : Blo 1076618 1077043 := bstep (se 1 (by rfl) ⟨807782, by rfl⟩ : syracuseStep 1077043 = 1615565) B1615565
theorem B1077059 : Blo 1076618 1077059 := bstep (se 1 (by rfl) ⟨807794, by rfl⟩ : syracuseStep 1077059 = 1615589) B1615589
theorem B1077075 : Blo 1076618 1077075 := bstep (se 1 (by rfl) ⟨807806, by rfl⟩ : syracuseStep 1077075 = 1615613) B1615613
theorem B1077091 : Blo 1076618 1077091 := bstep (se 1 (by rfl) ⟨807818, by rfl⟩ : syracuseStep 1077091 = 1615637) B1615637
theorem B11235185 : Blo 1076618 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B1077107 : Blo 1076618 1077107 := bstep (se 1 (by rfl) ⟨807830, by rfl⟩ : syracuseStep 1077107 = 1615661) B1615661
theorem B1077123 : Blo 1076618 1077123 := bstep (se 1 (by rfl) ⟨807842, by rfl⟩ : syracuseStep 1077123 = 1615685) B1615685
theorem B1077139 : Blo 1076618 1077139 := bstep (se 1 (by rfl) ⟨807854, by rfl⟩ : syracuseStep 1077139 = 1615709) B1615709
theorem B1077155 : Blo 1076618 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B1077171 : Blo 1076618 1077171 := bstep (se 1 (by rfl) ⟨807878, by rfl⟩ : syracuseStep 1077171 = 1615757) B1615757
theorem B1077187 : Blo 1076618 1077187 := bstep (se 1 (by rfl) ⟨807890, by rfl⟩ : syracuseStep 1077187 = 1615781) B1615781
theorem B1077203 : Blo 1076618 1077203 := bstep (se 1 (by rfl) ⟨807902, by rfl⟩ : syracuseStep 1077203 = 1615805) B1615805
theorem B1535969 : Blo 1076618 1535969 := bstep (se 2 (by rfl) ⟨575988, by rfl⟩ : syracuseStep 1535969 = 1151977) B1151977
theorem B1077219 : Blo 1076618 1077219 := bstep (se 1 (by rfl) ⟨807914, by rfl⟩ : syracuseStep 1077219 = 1615829) B1615829
theorem B1077235 : Blo 1076618 1077235 := bstep (se 1 (by rfl) ⟨807926, by rfl⟩ : syracuseStep 1077235 = 1615853) B1615853
theorem B1077251 : Blo 1076618 1077251 := bstep (se 1 (by rfl) ⟨807938, by rfl⟩ : syracuseStep 1077251 = 1615877) B1615877
theorem B1077267 : Blo 1076618 1077267 := bstep (se 1 (by rfl) ⟨807950, by rfl⟩ : syracuseStep 1077267 = 1615901) B1615901
theorem B1077283 : Blo 1076618 1077283 := bstep (se 1 (by rfl) ⟨807962, by rfl⟩ : syracuseStep 1077283 = 1615925) B1615925
theorem B1077299 : Blo 1076618 1077299 := bstep (se 1 (by rfl) ⟨807974, by rfl⟩ : syracuseStep 1077299 = 1615949) B1615949
theorem B1077315 : Blo 1076618 1077315 := bstep (se 1 (by rfl) ⟨807986, by rfl⟩ : syracuseStep 1077315 = 1615973) B1615973
theorem B1077331 : Blo 1076618 1077331 := bstep (se 1 (by rfl) ⟨807998, by rfl⟩ : syracuseStep 1077331 = 1615997) B1615997
theorem B1077347 : Blo 1076618 1077347 := bstep (se 1 (by rfl) ⟨808010, by rfl⟩ : syracuseStep 1077347 = 1616021) B1616021
theorem B1077363 : Blo 1076618 1077363 := bstep (se 1 (by rfl) ⟨808022, by rfl⟩ : syracuseStep 1077363 = 1616045) B1616045
theorem B1077379 : Blo 1076618 1077379 := bstep (se 1 (by rfl) ⟨808034, by rfl⟩ : syracuseStep 1077379 = 1616069) B1616069
theorem B1077395 : Blo 1076618 1077395 := bstep (se 1 (by rfl) ⟨808046, by rfl⟩ : syracuseStep 1077395 = 1616093) B1616093
theorem B1077411 : Blo 1076618 1077411 := bstep (se 1 (by rfl) ⟨808058, by rfl⟩ : syracuseStep 1077411 = 1616117) B1616117
theorem B1077427 : Blo 1076618 1077427 := bstep (se 1 (by rfl) ⟨808070, by rfl⟩ : syracuseStep 1077427 = 1616141) B1616141
theorem B1077443 : Blo 1076618 1077443 := bstep (se 1 (by rfl) ⟨808082, by rfl⟩ : syracuseStep 1077443 = 1616165) B1616165
theorem B1077459 : Blo 1076618 1077459 := bstep (se 1 (by rfl) ⟨808094, by rfl⟩ : syracuseStep 1077459 = 1616189) B1616189
theorem B1077475 : Blo 1076618 1077475 := bstep (se 1 (by rfl) ⟨808106, by rfl⟩ : syracuseStep 1077475 = 1616213) B1616213
theorem B1077491 : Blo 1076618 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B1077507 : Blo 1076618 1077507 := bstep (se 1 (by rfl) ⟨808130, by rfl⟩ : syracuseStep 1077507 = 1616261) B1616261
theorem B1077523 : Blo 1076618 1077523 := bstep (se 1 (by rfl) ⟨808142, by rfl⟩ : syracuseStep 1077523 = 1616285) B1616285
theorem B1077539 : Blo 1076618 1077539 := bstep (se 1 (by rfl) ⟨808154, by rfl⟩ : syracuseStep 1077539 = 1616309) B1616309
theorem B1077555 : Blo 1076618 1077555 := bstep (se 1 (by rfl) ⟨808166, by rfl⟩ : syracuseStep 1077555 = 1616333) B1616333
theorem B1077571 : Blo 1076618 1077571 := bstep (se 1 (by rfl) ⟨808178, by rfl⟩ : syracuseStep 1077571 = 1616357) B1616357
theorem B1077587 : Blo 1076618 1077587 := bstep (se 1 (by rfl) ⟨808190, by rfl⟩ : syracuseStep 1077587 = 1616381) B1616381
theorem B1077603 : Blo 1076618 1077603 := bstep (se 1 (by rfl) ⟨808202, by rfl⟩ : syracuseStep 1077603 = 1616405) B1616405
theorem B1077619 : Blo 1076618 1077619 := bstep (se 1 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 1077619 = 1616429) B1616429
theorem B1077635 : Blo 1076618 1077635 := bstep (se 1 (by rfl) ⟨808226, by rfl⟩ : syracuseStep 1077635 = 1616453) B1616453
theorem B1077651 : Blo 1076618 1077651 := bstep (se 1 (by rfl) ⟨808238, by rfl⟩ : syracuseStep 1077651 = 1616477) B1616477
theorem B1077667 : Blo 1076618 1077667 := bstep (se 1 (by rfl) ⟨808250, by rfl⟩ : syracuseStep 1077667 = 1616501) B1616501
theorem B1077683 : Blo 1076618 1077683 := bstep (se 1 (by rfl) ⟨808262, by rfl⟩ : syracuseStep 1077683 = 1616525) B1616525
theorem B1077699 : Blo 1076618 1077699 := bstep (se 1 (by rfl) ⟨808274, by rfl⟩ : syracuseStep 1077699 = 1616549) B1616549
theorem B20738501 : Blo 1076618 20738501 := bstep (se 4 (by rfl) ⟨1944234, by rfl⟩ : syracuseStep 20738501 = 3888469) B3888469
theorem B1077715 : Blo 1076618 1077715 := bstep (se 1 (by rfl) ⟨808286, by rfl⟩ : syracuseStep 1077715 = 1616573) B1616573
theorem B1077731 : Blo 1076618 1077731 := bstep (se 1 (by rfl) ⟨808298, by rfl⟩ : syracuseStep 1077731 = 1616597) B1616597
theorem B1077747 : Blo 1076618 1077747 := bstep (se 1 (by rfl) ⟨808310, by rfl⟩ : syracuseStep 1077747 = 1616621) B1616621
theorem B1536499 : Blo 1076618 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B1077763 : Blo 1076618 1077763 := bstep (se 1 (by rfl) ⟨808322, by rfl⟩ : syracuseStep 1077763 = 1616645) B1616645
theorem B1077779 : Blo 1076618 1077779 := bstep (se 1 (by rfl) ⟨808334, by rfl⟩ : syracuseStep 1077779 = 1616669) B1616669
theorem B1077795 : Blo 1076618 1077795 := bstep (se 1 (by rfl) ⟨808346, by rfl⟩ : syracuseStep 1077795 = 1616693) B1616693
theorem B3076643 : Blo 1076618 3076643 := bstep (se 1 (by rfl) ⟨2307482, by rfl⟩ : syracuseStep 3076643 = 4614965) B4614965
theorem B3633713 : Blo 1076618 3633713 := bstep (se 2 (by rfl) ⟨1362642, by rfl⟩ : syracuseStep 3633713 = 2725285) B2725285
theorem B1077811 : Blo 1076618 1077811 := bstep (se 1 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 1077811 = 1616717) B1616717
theorem B1077827 : Blo 1076618 1077827 := bstep (se 1 (by rfl) ⟨808370, by rfl⟩ : syracuseStep 1077827 = 1616741) B1616741
theorem B1077843 : Blo 1076618 1077843 := bstep (se 1 (by rfl) ⟨808382, by rfl⟩ : syracuseStep 1077843 = 1616765) B1616765
theorem B1077859 : Blo 1076618 1077859 := bstep (se 1 (by rfl) ⟨808394, by rfl⟩ : syracuseStep 1077859 = 1616789) B1616789
theorem B4092515 : Blo 1076618 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B1077875 : Blo 1076618 1077875 := bstep (se 1 (by rfl) ⟨808406, by rfl⟩ : syracuseStep 1077875 = 1616813) B1616813
theorem B1077891 : Blo 1076618 1077891 := bstep (se 1 (by rfl) ⟨808418, by rfl⟩ : syracuseStep 1077891 = 1616837) B1616837
theorem B10384013 : Blo 1076618 10384013 := bstep (se 3 (by rfl) ⟨1947002, by rfl⟩ : syracuseStep 10384013 = 3894005) B3894005
theorem B1077907 : Blo 1076618 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B1077923 : Blo 1076618 1077923 := bstep (se 1 (by rfl) ⟨808442, by rfl⟩ : syracuseStep 1077923 = 1616885) B1616885
theorem B1077939 : Blo 1076618 1077939 := bstep (se 1 (by rfl) ⟨808454, by rfl⟩ : syracuseStep 1077939 = 1616909) B1616909
theorem B1077955 : Blo 1076618 1077955 := bstep (se 1 (by rfl) ⟨808466, by rfl⟩ : syracuseStep 1077955 = 1616933) B1616933
theorem B8188613 : Blo 1076618 8188613 := bstep (se 4 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 8188613 = 1535365) B1535365
theorem B1077971 : Blo 1076618 1077971 := bstep (se 1 (by rfl) ⟨808478, by rfl⟩ : syracuseStep 1077971 = 1616957) B1616957
theorem B1077987 : Blo 1076618 1077987 := bstep (se 1 (by rfl) ⟨808490, by rfl⟩ : syracuseStep 1077987 = 1616981) B1616981
theorem B1078003 : Blo 1076618 1078003 := bstep (se 1 (by rfl) ⟨808502, by rfl⟩ : syracuseStep 1078003 = 1617005) B1617005
theorem B1078019 : Blo 1076618 1078019 := bstep (se 1 (by rfl) ⟨808514, by rfl⟩ : syracuseStep 1078019 = 1617029) B1617029
theorem B1078035 : Blo 1076618 1078035 := bstep (se 1 (by rfl) ⟨808526, by rfl⟩ : syracuseStep 1078035 = 1617053) B1617053
theorem B1078051 : Blo 1076618 1078051 := bstep (se 1 (by rfl) ⟨808538, by rfl⟩ : syracuseStep 1078051 = 1617077) B1617077
theorem B1078067 : Blo 1076618 1078067 := bstep (se 1 (by rfl) ⟨808550, by rfl⟩ : syracuseStep 1078067 = 1617101) B1617101
theorem B1078083 : Blo 1076618 1078083 := bstep (se 1 (by rfl) ⟨808562, by rfl⟩ : syracuseStep 1078083 = 1617125) B1617125
theorem B1536835 : Blo 1076618 1536835 := bstep (se 1 (by rfl) ⟨1152626, by rfl⟩ : syracuseStep 1536835 = 2305253) B2305253
theorem B5174093 : Blo 1076618 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B1078099 : Blo 1076618 1078099 := bstep (se 1 (by rfl) ⟨808574, by rfl⟩ : syracuseStep 1078099 = 1617149) B1617149
theorem B1078115 : Blo 1076618 1078115 := bstep (se 1 (by rfl) ⟨808586, by rfl⟩ : syracuseStep 1078115 = 1617173) B1617173
theorem B3076973 : Blo 1076618 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B1078131 : Blo 1076618 1078131 := bstep (se 1 (by rfl) ⟨808598, by rfl⟩ : syracuseStep 1078131 = 1617197) B1617197
theorem B1078147 : Blo 1076618 1078147 := bstep (se 1 (by rfl) ⟨808610, by rfl⟩ : syracuseStep 1078147 = 1617221) B1617221
theorem B1078163 : Blo 1076618 1078163 := bstep (se 1 (by rfl) ⟨808622, by rfl⟩ : syracuseStep 1078163 = 1617245) B1617245
theorem B1078179 : Blo 1076618 1078179 := bstep (se 1 (by rfl) ⟨808634, by rfl⟩ : syracuseStep 1078179 = 1617269) B1617269
theorem B3077041 : Blo 1076618 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B1078195 : Blo 1076618 1078195 := bstep (se 1 (by rfl) ⟨808646, by rfl⟩ : syracuseStep 1078195 = 1617293) B1617293
theorem B1078211 : Blo 1076618 1078211 := bstep (se 1 (by rfl) ⟨808658, by rfl⟩ : syracuseStep 1078211 = 1617317) B1617317
theorem B1078227 : Blo 1076618 1078227 := bstep (se 1 (by rfl) ⟨808670, by rfl⟩ : syracuseStep 1078227 = 1617341) B1617341
theorem B1078243 : Blo 1076618 1078243 := bstep (se 1 (by rfl) ⟨808682, by rfl⟩ : syracuseStep 1078243 = 1617365) B1617365
theorem B1078259 : Blo 1076618 1078259 := bstep (se 1 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 1078259 = 1617389) B1617389
theorem B1078275 : Blo 1076618 1078275 := bstep (se 1 (by rfl) ⟨808706, by rfl⟩ : syracuseStep 1078275 = 1617413) B1617413
theorem B1078291 : Blo 1076618 1078291 := bstep (se 1 (by rfl) ⟨808718, by rfl⟩ : syracuseStep 1078291 = 1617437) B1617437
theorem B1078307 : Blo 1076618 1078307 := bstep (se 1 (by rfl) ⟨808730, by rfl⟩ : syracuseStep 1078307 = 1617461) B1617461
theorem B1078323 : Blo 1076618 1078323 := bstep (se 1 (by rfl) ⟨808742, by rfl⟩ : syracuseStep 1078323 = 1617485) B1617485
theorem B1078339 : Blo 1076618 1078339 := bstep (se 1 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 1078339 = 1617509) B1617509
theorem B3634253 : Blo 1076618 3634253 := bstep (se 3 (by rfl) ⟨681422, by rfl⟩ : syracuseStep 3634253 = 1362845) B1362845
theorem B1078355 : Blo 1076618 1078355 := bstep (se 1 (by rfl) ⟨808766, by rfl⟩ : syracuseStep 1078355 = 1617533) B1617533
theorem B1078371 : Blo 1076618 1078371 := bstep (se 1 (by rfl) ⟨808778, by rfl⟩ : syracuseStep 1078371 = 1617557) B1617557
theorem B5829745 : Blo 1076618 5829745 := bstep (se 2 (by rfl) ⟨2186154, by rfl⟩ : syracuseStep 5829745 = 4372309) B4372309
theorem B1078387 : Blo 1076618 1078387 := bstep (se 1 (by rfl) ⟨808790, by rfl⟩ : syracuseStep 1078387 = 1617581) B1617581
theorem B3634307 : Blo 1076618 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B1078403 : Blo 1076618 1078403 := bstep (se 1 (by rfl) ⟨808802, by rfl⟩ : syracuseStep 1078403 = 1617605) B1617605
theorem B1078419 : Blo 1076618 1078419 := bstep (se 1 (by rfl) ⟨808814, by rfl⟩ : syracuseStep 1078419 = 1617629) B1617629
theorem B1078435 : Blo 1076618 1078435 := bstep (se 1 (by rfl) ⟨808826, by rfl⟩ : syracuseStep 1078435 = 1617653) B1617653
theorem B3503267 : Blo 1076618 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B1078451 : Blo 1076618 1078451 := bstep (se 1 (by rfl) ⟨808838, by rfl⟩ : syracuseStep 1078451 = 1617677) B1617677
theorem B1078467 : Blo 1076618 1078467 := bstep (se 1 (by rfl) ⟨808850, by rfl⟩ : syracuseStep 1078467 = 1617701) B1617701
theorem B1078483 : Blo 1076618 1078483 := bstep (se 1 (by rfl) ⟨808862, by rfl⟩ : syracuseStep 1078483 = 1617725) B1617725
theorem B1078499 : Blo 1076618 1078499 := bstep (se 1 (by rfl) ⟨808874, by rfl⟩ : syracuseStep 1078499 = 1617749) B1617749
theorem B1078515 : Blo 1076618 1078515 := bstep (se 1 (by rfl) ⟨808886, by rfl⟩ : syracuseStep 1078515 = 1617773) B1617773
theorem B1078531 : Blo 1076618 1078531 := bstep (se 1 (by rfl) ⟨808898, by rfl⟩ : syracuseStep 1078531 = 1617797) B1617797
theorem B1078547 : Blo 1076618 1078547 := bstep (se 1 (by rfl) ⟨808910, by rfl⟩ : syracuseStep 1078547 = 1617821) B1617821
theorem B1078563 : Blo 1076618 1078563 := bstep (se 1 (by rfl) ⟨808922, by rfl⟩ : syracuseStep 1078563 = 1617845) B1617845
theorem B1078579 : Blo 1076618 1078579 := bstep (se 1 (by rfl) ⟨808934, by rfl⟩ : syracuseStep 1078579 = 1617869) B1617869
theorem B1078595 : Blo 1076618 1078595 := bstep (se 1 (by rfl) ⟨808946, by rfl⟩ : syracuseStep 1078595 = 1617893) B1617893
theorem B1078611 : Blo 1076618 1078611 := bstep (se 1 (by rfl) ⟨808958, by rfl⟩ : syracuseStep 1078611 = 1617917) B1617917
theorem B1078627 : Blo 1076618 1078627 := bstep (se 1 (by rfl) ⟨808970, by rfl⟩ : syracuseStep 1078627 = 1617941) B1617941
theorem B1537393 : Blo 1076618 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B1078643 : Blo 1076618 1078643 := bstep (se 1 (by rfl) ⟨808982, by rfl⟩ : syracuseStep 1078643 = 1617965) B1617965
theorem B1078659 : Blo 1076618 1078659 := bstep (se 1 (by rfl) ⟨808994, by rfl⟩ : syracuseStep 1078659 = 1617989) B1617989
theorem B3634577 : Blo 1076618 3634577 := bstep (se 2 (by rfl) ⟨1362966, by rfl⟩ : syracuseStep 3634577 = 2725933) B2725933
theorem B1078675 : Blo 1076618 1078675 := bstep (se 1 (by rfl) ⟨809006, by rfl⟩ : syracuseStep 1078675 = 1618013) B1618013
theorem B1537427 : Blo 1076618 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B1078691 : Blo 1076618 1078691 := bstep (se 1 (by rfl) ⟨809018, by rfl⟩ : syracuseStep 1078691 = 1618037) B1618037
theorem B1078707 : Blo 1076618 1078707 := bstep (se 1 (by rfl) ⟨809030, by rfl⟩ : syracuseStep 1078707 = 1618061) B1618061
theorem B1078723 : Blo 1076618 1078723 := bstep (se 1 (by rfl) ⟨809042, by rfl⟩ : syracuseStep 1078723 = 1618085) B1618085
theorem B1078739 : Blo 1076618 1078739 := bstep (se 1 (by rfl) ⟨809054, by rfl⟩ : syracuseStep 1078739 = 1618109) B1618109
theorem B1078755 : Blo 1076618 1078755 := bstep (se 1 (by rfl) ⟨809066, by rfl⟩ : syracuseStep 1078755 = 1618133) B1618133
theorem B1078771 : Blo 1076618 1078771 := bstep (se 1 (by rfl) ⟨809078, by rfl⟩ : syracuseStep 1078771 = 1618157) B1618157
theorem B1078787 : Blo 1076618 1078787 := bstep (se 1 (by rfl) ⟨809090, by rfl⟩ : syracuseStep 1078787 = 1618181) B1618181
theorem B1078803 : Blo 1076618 1078803 := bstep (se 1 (by rfl) ⟨809102, by rfl⟩ : syracuseStep 1078803 = 1618205) B1618205
theorem B1078819 : Blo 1076618 1078819 := bstep (se 1 (by rfl) ⟨809114, by rfl⟩ : syracuseStep 1078819 = 1618229) B1618229
theorem B1078835 : Blo 1076618 1078835 := bstep (se 1 (by rfl) ⟨809126, by rfl⟩ : syracuseStep 1078835 = 1618253) B1618253
theorem B1078851 : Blo 1076618 1078851 := bstep (se 1 (by rfl) ⟨809138, by rfl⟩ : syracuseStep 1078851 = 1618277) B1618277
theorem B4093517 : Blo 1076618 4093517 := bstep (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) B1535069
theorem B1078867 : Blo 1076618 1078867 := bstep (se 1 (by rfl) ⟨809150, by rfl⟩ : syracuseStep 1078867 = 1618301) B1618301
theorem B1078883 : Blo 1076618 1078883 := bstep (se 1 (by rfl) ⟨809162, by rfl⟩ : syracuseStep 1078883 = 1618325) B1618325
theorem B1078899 : Blo 1076618 1078899 := bstep (se 1 (by rfl) ⟨809174, by rfl⟩ : syracuseStep 1078899 = 1618349) B1618349
theorem B2422403 : Blo 1076618 2422403 := bstep (se 1 (by rfl) ⟨1816802, by rfl⟩ : syracuseStep 2422403 = 3633605) B3633605
theorem B1078915 : Blo 1076618 1078915 := bstep (se 1 (by rfl) ⟨809186, by rfl⟩ : syracuseStep 1078915 = 1618373) B1618373
theorem B1078931 : Blo 1076618 1078931 := bstep (se 1 (by rfl) ⟨809198, by rfl⟩ : syracuseStep 1078931 = 1618397) B1618397
theorem B1078947 : Blo 1076618 1078947 := bstep (se 1 (by rfl) ⟨809210, by rfl⟩ : syracuseStep 1078947 = 1618421) B1618421
theorem B1078963 : Blo 1076618 1078963 := bstep (se 1 (by rfl) ⟨809222, by rfl⟩ : syracuseStep 1078963 = 1618445) B1618445
theorem B1078979 : Blo 1076618 1078979 := bstep (se 1 (by rfl) ⟨809234, by rfl⟩ : syracuseStep 1078979 = 1618469) B1618469
theorem B1078995 : Blo 1076618 1078995 := bstep (se 1 (by rfl) ⟨809246, by rfl⟩ : syracuseStep 1078995 = 1618493) B1618493
theorem B2914019 : Blo 1076618 2914019 := bstep (se 1 (by rfl) ⟨2185514, by rfl⟩ : syracuseStep 2914019 = 4371029) B4371029
theorem B1079011 : Blo 1076618 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B1079027 : Blo 1076618 1079027 := bstep (se 1 (by rfl) ⟨809270, by rfl⟩ : syracuseStep 1079027 = 1618541) B1618541
theorem B1079043 : Blo 1076618 1079043 := bstep (se 1 (by rfl) ⟨809282, by rfl⟩ : syracuseStep 1079043 = 1618565) B1618565
theorem B1079059 : Blo 1076618 1079059 := bstep (se 1 (by rfl) ⟨809294, by rfl⟩ : syracuseStep 1079059 = 1618589) B1618589
theorem B1079075 : Blo 1076618 1079075 := bstep (se 1 (by rfl) ⟨809306, by rfl⟩ : syracuseStep 1079075 = 1618613) B1618613
theorem B1079091 : Blo 1076618 1079091 := bstep (se 1 (by rfl) ⟨809318, by rfl⟩ : syracuseStep 1079091 = 1618637) B1618637
theorem B1079107 : Blo 1076618 1079107 := bstep (se 1 (by rfl) ⟨809330, by rfl⟩ : syracuseStep 1079107 = 1618661) B1618661
theorem B1079123 : Blo 1076618 1079123 := bstep (se 1 (by rfl) ⟨809342, by rfl⟩ : syracuseStep 1079123 = 1618685) B1618685
theorem B1079139 : Blo 1076618 1079139 := bstep (se 1 (by rfl) ⟨809354, by rfl⟩ : syracuseStep 1079139 = 1618709) B1618709
theorem B1079155 : Blo 1076618 1079155 := bstep (se 1 (by rfl) ⟨809366, by rfl⟩ : syracuseStep 1079155 = 1618733) B1618733
theorem B1079171 : Blo 1076618 1079171 := bstep (se 1 (by rfl) ⟨809378, by rfl⟩ : syracuseStep 1079171 = 1618757) B1618757
theorem B2422673 : Blo 1076618 2422673 := bstep (se 2 (by rfl) ⟨908502, by rfl⟩ : syracuseStep 2422673 = 1817005) B1817005
theorem B1079187 : Blo 1076618 1079187 := bstep (se 1 (by rfl) ⟨809390, by rfl⟩ : syracuseStep 1079187 = 1618781) B1618781
theorem B2422691 : Blo 1076618 2422691 := bstep (se 1 (by rfl) ⟨1817018, by rfl⟩ : syracuseStep 2422691 = 3634037) B3634037
theorem B1079203 : Blo 1076618 1079203 := bstep (se 1 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 1079203 = 1618805) B1618805
theorem B3635117 : Blo 1076618 3635117 := bstep (se 3 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 3635117 = 1363169) B1363169
theorem B1079219 : Blo 1076618 1079219 := bstep (se 1 (by rfl) ⟨809414, by rfl⟩ : syracuseStep 1079219 = 1618829) B1618829
theorem B1537985 : Blo 1076618 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B1079235 : Blo 1076618 1079235 := bstep (se 1 (by rfl) ⟨809426, by rfl⟩ : syracuseStep 1079235 = 1618853) B1618853
theorem B1079251 : Blo 1076618 1079251 := bstep (se 1 (by rfl) ⟨809438, by rfl⟩ : syracuseStep 1079251 = 1618877) B1618877
theorem B3635171 : Blo 1076618 3635171 := bstep (se 1 (by rfl) ⟨2726378, by rfl⟩ : syracuseStep 3635171 = 5452757) B5452757
theorem B1079267 : Blo 1076618 1079267 := bstep (se 1 (by rfl) ⟨809450, by rfl⟩ : syracuseStep 1079267 = 1618901) B1618901
theorem B1079283 : Blo 1076618 1079283 := bstep (se 1 (by rfl) ⟨809462, by rfl⟩ : syracuseStep 1079283 = 1618925) B1618925
theorem B1079299 : Blo 1076618 1079299 := bstep (se 1 (by rfl) ⟨809474, by rfl⟩ : syracuseStep 1079299 = 1618949) B1618949
theorem B1538065 : Blo 1076618 1538065 := bstep (se 2 (by rfl) ⟨576774, by rfl⟩ : syracuseStep 1538065 = 1153549) B1153549
theorem B1079315 : Blo 1076618 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B1079331 : Blo 1076618 1079331 := bstep (se 1 (by rfl) ⟨809498, by rfl⟩ : syracuseStep 1079331 = 1618997) B1618997
theorem B1079347 : Blo 1076618 1079347 := bstep (se 1 (by rfl) ⟨809510, by rfl⟩ : syracuseStep 1079347 = 1619021) B1619021
theorem B1079363 : Blo 1076618 1079363 := bstep (se 1 (by rfl) ⟨809522, by rfl⟩ : syracuseStep 1079363 = 1619045) B1619045
theorem B1079379 : Blo 1076618 1079379 := bstep (se 1 (by rfl) ⟨809534, by rfl⟩ : syracuseStep 1079379 = 1619069) B1619069
theorem B1079395 : Blo 1076618 1079395 := bstep (se 1 (by rfl) ⟨809546, by rfl⟩ : syracuseStep 1079395 = 1619093) B1619093
theorem B1079411 : Blo 1076618 1079411 := bstep (se 1 (by rfl) ⟨809558, by rfl⟩ : syracuseStep 1079411 = 1619117) B1619117
theorem B1079427 : Blo 1076618 1079427 := bstep (se 1 (by rfl) ⟨809570, by rfl⟩ : syracuseStep 1079427 = 1619141) B1619141
theorem B1079443 : Blo 1076618 1079443 := bstep (se 1 (by rfl) ⟨809582, by rfl⟩ : syracuseStep 1079443 = 1619165) B1619165
theorem B1079459 : Blo 1076618 1079459 := bstep (se 1 (by rfl) ⟨809594, by rfl⟩ : syracuseStep 1079459 = 1619189) B1619189
theorem B2422961 : Blo 1076618 2422961 := bstep (se 2 (by rfl) ⟨908610, by rfl⟩ : syracuseStep 2422961 = 1817221) B1817221
theorem B1079475 : Blo 1076618 1079475 := bstep (se 1 (by rfl) ⟨809606, by rfl⟩ : syracuseStep 1079475 = 1619213) B1619213
theorem B2422979 : Blo 1076618 2422979 := bstep (se 1 (by rfl) ⟨1817234, by rfl⟩ : syracuseStep 2422979 = 3634469) B3634469
theorem B1079491 : Blo 1076618 1079491 := bstep (se 1 (by rfl) ⟨809618, by rfl⟩ : syracuseStep 1079491 = 1619237) B1619237
theorem B1079507 : Blo 1076618 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B1079523 : Blo 1076618 1079523 := bstep (se 1 (by rfl) ⟨809642, by rfl⟩ : syracuseStep 1079523 = 1619285) B1619285
theorem B3635441 : Blo 1076618 3635441 := bstep (se 2 (by rfl) ⟨1363290, by rfl⟩ : syracuseStep 3635441 = 2726581) B2726581
theorem B1079539 : Blo 1076618 1079539 := bstep (se 1 (by rfl) ⟨809654, by rfl⟩ : syracuseStep 1079539 = 1619309) B1619309
theorem B1079555 : Blo 1076618 1079555 := bstep (se 1 (by rfl) ⟨809666, by rfl⟩ : syracuseStep 1079555 = 1619333) B1619333
theorem B1079571 : Blo 1076618 1079571 := bstep (se 1 (by rfl) ⟨809678, by rfl⟩ : syracuseStep 1079571 = 1619357) B1619357
theorem B1079587 : Blo 1076618 1079587 := bstep (se 1 (by rfl) ⟨809690, by rfl⟩ : syracuseStep 1079587 = 1619381) B1619381
theorem B1079603 : Blo 1076618 1079603 := bstep (se 1 (by rfl) ⟨809702, by rfl⟩ : syracuseStep 1079603 = 1619405) B1619405
theorem B1079619 : Blo 1076618 1079619 := bstep (se 1 (by rfl) ⟨809714, by rfl⟩ : syracuseStep 1079619 = 1619429) B1619429
theorem B1079635 : Blo 1076618 1079635 := bstep (se 1 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 1079635 = 1619453) B1619453
theorem B1079651 : Blo 1076618 1079651 := bstep (se 1 (by rfl) ⟨809738, by rfl⟩ : syracuseStep 1079651 = 1619477) B1619477
theorem B5470577 : Blo 1076618 5470577 := bstep (se 2 (by rfl) ⟨2051466, by rfl⟩ : syracuseStep 5470577 = 4102933) B4102933
theorem B1079667 : Blo 1076618 1079667 := bstep (se 1 (by rfl) ⟨809750, by rfl⟩ : syracuseStep 1079667 = 1619501) B1619501
theorem B1079683 : Blo 1076618 1079683 := bstep (se 1 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 1079683 = 1619525) B1619525
theorem B1079699 : Blo 1076618 1079699 := bstep (se 1 (by rfl) ⟨809774, by rfl⟩ : syracuseStep 1079699 = 1619549) B1619549
theorem B1079715 : Blo 1076618 1079715 := bstep (se 1 (by rfl) ⟨809786, by rfl⟩ : syracuseStep 1079715 = 1619573) B1619573
theorem B1079731 : Blo 1076618 1079731 := bstep (se 1 (by rfl) ⟨809798, by rfl⟩ : syracuseStep 1079731 = 1619597) B1619597
theorem B1079747 : Blo 1076618 1079747 := bstep (se 1 (by rfl) ⟨809810, by rfl⟩ : syracuseStep 1079747 = 1619621) B1619621
theorem B2423249 : Blo 1076618 2423249 := bstep (se 2 (by rfl) ⟨908718, by rfl⟩ : syracuseStep 2423249 = 1817437) B1817437
theorem B1079763 : Blo 1076618 1079763 := bstep (se 1 (by rfl) ⟨809822, by rfl⟩ : syracuseStep 1079763 = 1619645) B1619645
theorem B2423267 : Blo 1076618 2423267 := bstep (se 1 (by rfl) ⟨1817450, by rfl⟩ : syracuseStep 2423267 = 3634901) B3634901
theorem B26212835 : Blo 1076618 26212835 := bstep (se 1 (by rfl) ⟨19659626, by rfl⟩ : syracuseStep 26212835 = 39319253) B39319253
theorem B1079779 : Blo 1076618 1079779 := bstep (se 1 (by rfl) ⟨809834, by rfl⟩ : syracuseStep 1079779 = 1619669) B1619669
theorem B1079795 : Blo 1076618 1079795 := bstep (se 1 (by rfl) ⟨809846, by rfl⟩ : syracuseStep 1079795 = 1619693) B1619693
theorem B1079811 : Blo 1076618 1079811 := bstep (se 1 (by rfl) ⟨809858, by rfl⟩ : syracuseStep 1079811 = 1619717) B1619717
theorem B7371269 : Blo 1076618 7371269 := bstep (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) B1382113
theorem B2587153 : Blo 1076618 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B1079827 : Blo 1076618 1079827 := bstep (se 1 (by rfl) ⟨809870, by rfl⟩ : syracuseStep 1079827 = 1619741) B1619741
theorem B1079843 : Blo 1076618 1079843 := bstep (se 1 (by rfl) ⟨809882, by rfl⟩ : syracuseStep 1079843 = 1619765) B1619765
theorem B1079859 : Blo 1076618 1079859 := bstep (se 1 (by rfl) ⟨809894, by rfl⟩ : syracuseStep 1079859 = 1619789) B1619789
theorem B1079875 : Blo 1076618 1079875 := bstep (se 1 (by rfl) ⟨809906, by rfl⟩ : syracuseStep 1079875 = 1619813) B1619813
theorem B1079891 : Blo 1076618 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B1079907 : Blo 1076618 1079907 := bstep (se 1 (by rfl) ⟨809930, by rfl⟩ : syracuseStep 1079907 = 1619861) B1619861
theorem B1079923 : Blo 1076618 1079923 := bstep (se 1 (by rfl) ⟨809942, by rfl⟩ : syracuseStep 1079923 = 1619885) B1619885
theorem B1079939 : Blo 1076618 1079939 := bstep (se 1 (by rfl) ⟨809954, by rfl⟩ : syracuseStep 1079939 = 1619909) B1619909
theorem B1079955 : Blo 1076618 1079955 := bstep (se 1 (by rfl) ⟨809966, by rfl⟩ : syracuseStep 1079955 = 1619933) B1619933
theorem B1079971 : Blo 1076618 1079971 := bstep (se 1 (by rfl) ⟨809978, by rfl⟩ : syracuseStep 1079971 = 1619957) B1619957
theorem B1079987 : Blo 1076618 1079987 := bstep (se 1 (by rfl) ⟨809990, by rfl⟩ : syracuseStep 1079987 = 1619981) B1619981
theorem B1080003 : Blo 1076618 1080003 := bstep (se 1 (by rfl) ⟨810002, by rfl⟩ : syracuseStep 1080003 = 1620005) B1620005
theorem B1080019 : Blo 1076618 1080019 := bstep (se 1 (by rfl) ⟨810014, by rfl⟩ : syracuseStep 1080019 = 1620029) B1620029
theorem B1080035 : Blo 1076618 1080035 := bstep (se 1 (by rfl) ⟨810026, by rfl⟩ : syracuseStep 1080035 = 1620053) B1620053
theorem B2423537 : Blo 1076618 2423537 := bstep (se 2 (by rfl) ⟨908826, by rfl⟩ : syracuseStep 2423537 = 1817653) B1817653
theorem B1080051 : Blo 1076618 1080051 := bstep (se 1 (by rfl) ⟨810038, by rfl⟩ : syracuseStep 1080051 = 1620077) B1620077
theorem B2423555 : Blo 1076618 2423555 := bstep (se 1 (by rfl) ⟨1817666, by rfl⟩ : syracuseStep 2423555 = 3635333) B3635333
theorem B1080067 : Blo 1076618 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B3635981 : Blo 1076618 3635981 := bstep (se 3 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 3635981 = 1363493) B1363493
theorem B1080083 : Blo 1076618 1080083 := bstep (se 1 (by rfl) ⟨810062, by rfl⟩ : syracuseStep 1080083 = 1620125) B1620125
theorem B6552355 : Blo 1076618 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B1080099 : Blo 1076618 1080099 := bstep (se 1 (by rfl) ⟨810074, by rfl⟩ : syracuseStep 1080099 = 1620149) B1620149
theorem B1080115 : Blo 1076618 1080115 := bstep (se 1 (by rfl) ⟨810086, by rfl⟩ : syracuseStep 1080115 = 1620173) B1620173
theorem B3636035 : Blo 1076618 3636035 := bstep (se 1 (by rfl) ⟨2727026, by rfl⟩ : syracuseStep 3636035 = 5454053) B5454053
theorem B1080131 : Blo 1076618 1080131 := bstep (se 1 (by rfl) ⟨810098, by rfl⟩ : syracuseStep 1080131 = 1620197) B1620197
theorem B1080147 : Blo 1076618 1080147 := bstep (se 1 (by rfl) ⟨810110, by rfl⟩ : syracuseStep 1080147 = 1620221) B1620221
theorem B1080163 : Blo 1076618 1080163 := bstep (se 1 (by rfl) ⟨810122, by rfl⟩ : syracuseStep 1080163 = 1620245) B1620245
theorem B1211251 : Blo 1076618 1211251 := bstep (se 1 (by rfl) ⟨908438, by rfl⟩ : syracuseStep 1211251 = 1816877) B1816877
theorem B1080179 : Blo 1076618 1080179 := bstep (se 1 (by rfl) ⟨810134, by rfl⟩ : syracuseStep 1080179 = 1620269) B1620269
theorem B1080195 : Blo 1076618 1080195 := bstep (se 1 (by rfl) ⟨810146, by rfl⟩ : syracuseStep 1080195 = 1620293) B1620293
theorem B1080211 : Blo 1076618 1080211 := bstep (se 1 (by rfl) ⟨810158, by rfl⟩ : syracuseStep 1080211 = 1620317) B1620317
theorem B1080227 : Blo 1076618 1080227 := bstep (se 1 (by rfl) ⟨810170, by rfl⟩ : syracuseStep 1080227 = 1620341) B1620341
theorem B3242929 : Blo 1076618 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B1080243 : Blo 1076618 1080243 := bstep (se 1 (by rfl) ⟨810182, by rfl⟩ : syracuseStep 1080243 = 1620365) B1620365
theorem B1080259 : Blo 1076618 1080259 := bstep (se 1 (by rfl) ⟨810194, by rfl⟩ : syracuseStep 1080259 = 1620389) B1620389
theorem B1080275 : Blo 1076618 1080275 := bstep (se 1 (by rfl) ⟨810206, by rfl⟩ : syracuseStep 1080275 = 1620413) B1620413
theorem B3505123 : Blo 1076618 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B1080291 : Blo 1076618 1080291 := bstep (se 1 (by rfl) ⟨810218, by rfl⟩ : syracuseStep 1080291 = 1620437) B1620437
theorem B1080307 : Blo 1076618 1080307 := bstep (se 1 (by rfl) ⟨810230, by rfl⟩ : syracuseStep 1080307 = 1620461) B1620461
theorem B1211395 : Blo 1076618 1211395 := bstep (se 1 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 1211395 = 1817093) B1817093
theorem B1080323 : Blo 1076618 1080323 := bstep (se 1 (by rfl) ⟨810242, by rfl⟩ : syracuseStep 1080323 = 1620485) B1620485
theorem B2423825 : Blo 1076618 2423825 := bstep (se 2 (by rfl) ⟨908934, by rfl⟩ : syracuseStep 2423825 = 1817869) B1817869
theorem B1080339 : Blo 1076618 1080339 := bstep (se 1 (by rfl) ⟨810254, by rfl⟩ : syracuseStep 1080339 = 1620509) B1620509
theorem B2423843 : Blo 1076618 2423843 := bstep (se 1 (by rfl) ⟨1817882, by rfl⟩ : syracuseStep 2423843 = 3635765) B3635765
theorem B1080355 : Blo 1076618 1080355 := bstep (se 1 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 1080355 = 1620533) B1620533
theorem B1080371 : Blo 1076618 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B3112003 : Blo 1076618 3112003 := bstep (se 1 (by rfl) ⟨2334002, by rfl⟩ : syracuseStep 3112003 = 4668005) B4668005
theorem B1080387 : Blo 1076618 1080387 := bstep (se 1 (by rfl) ⟨810290, by rfl⟩ : syracuseStep 1080387 = 1620581) B1620581
theorem B3636305 : Blo 1076618 3636305 := bstep (se 2 (by rfl) ⟨1363614, by rfl⟩ : syracuseStep 3636305 = 2727229) B2727229
theorem B1080403 : Blo 1076618 1080403 := bstep (se 1 (by rfl) ⟨810302, by rfl⟩ : syracuseStep 1080403 = 1620605) B1620605
theorem B1080419 : Blo 1076618 1080419 := bstep (se 1 (by rfl) ⟨810314, by rfl⟩ : syracuseStep 1080419 = 1620629) B1620629
theorem B1080435 : Blo 1076618 1080435 := bstep (se 1 (by rfl) ⟨810326, by rfl⟩ : syracuseStep 1080435 = 1620653) B1620653
theorem B1080451 : Blo 1076618 1080451 := bstep (se 1 (by rfl) ⟨810338, by rfl⟩ : syracuseStep 1080451 = 1620677) B1620677
theorem B1211539 : Blo 1076618 1211539 := bstep (se 1 (by rfl) ⟨908654, by rfl⟩ : syracuseStep 1211539 = 1817309) B1817309
theorem B1080467 : Blo 1076618 1080467 := bstep (se 1 (by rfl) ⟨810350, by rfl⟩ : syracuseStep 1080467 = 1620701) B1620701
theorem B1080483 : Blo 1076618 1080483 := bstep (se 1 (by rfl) ⟨810362, by rfl⟩ : syracuseStep 1080483 = 1620725) B1620725
theorem B1080499 : Blo 1076618 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B1080515 : Blo 1076618 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B1080531 : Blo 1076618 1080531 := bstep (se 1 (by rfl) ⟨810398, by rfl⟩ : syracuseStep 1080531 = 1620797) B1620797
theorem B1080547 : Blo 1076618 1080547 := bstep (se 1 (by rfl) ⟨810410, by rfl⟩ : syracuseStep 1080547 = 1620821) B1620821
theorem B1080563 : Blo 1076618 1080563 := bstep (se 1 (by rfl) ⟨810422, by rfl⟩ : syracuseStep 1080563 = 1620845) B1620845
theorem B1080579 : Blo 1076618 1080579 := bstep (se 1 (by rfl) ⟨810434, by rfl⟩ : syracuseStep 1080579 = 1620869) B1620869
theorem B6552845 : Blo 1076618 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1080595 : Blo 1076618 1080595 := bstep (se 1 (by rfl) ⟨810446, by rfl⟩ : syracuseStep 1080595 = 1620893) B1620893
theorem B1211683 : Blo 1076618 1211683 := bstep (se 1 (by rfl) ⟨908762, by rfl⟩ : syracuseStep 1211683 = 1817525) B1817525
theorem B1080611 : Blo 1076618 1080611 := bstep (se 1 (by rfl) ⟨810458, by rfl⟩ : syracuseStep 1080611 = 1620917) B1620917
theorem B2424113 : Blo 1076618 2424113 := bstep (se 2 (by rfl) ⟨909042, by rfl⟩ : syracuseStep 2424113 = 1818085) B1818085
theorem B2424131 : Blo 1076618 2424131 := bstep (se 1 (by rfl) ⟨1818098, by rfl⟩ : syracuseStep 2424131 = 3636197) B3636197
theorem B6913349 : Blo 1076618 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B1211827 : Blo 1076618 1211827 := bstep (se 1 (by rfl) ⟨908870, by rfl⟩ : syracuseStep 1211827 = 1817741) B1817741
theorem B3276323 : Blo 1076618 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B1211971 : Blo 1076618 1211971 := bstep (se 1 (by rfl) ⟨908978, by rfl⟩ : syracuseStep 1211971 = 1817957) B1817957
theorem B2424401 : Blo 1076618 2424401 := bstep (se 2 (by rfl) ⟨909150, by rfl⟩ : syracuseStep 2424401 = 1818301) B1818301
theorem B2915921 : Blo 1076618 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B2424419 : Blo 1076618 2424419 := bstep (se 1 (by rfl) ⟨1818314, by rfl⟩ : syracuseStep 2424419 = 3636629) B3636629
theorem B3636845 : Blo 1076618 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B4095629 : Blo 1076618 4095629 := bstep (se 3 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 4095629 = 1535861) B1535861
theorem B3636899 : Blo 1076618 3636899 := bstep (se 1 (by rfl) ⟨2727674, by rfl⟩ : syracuseStep 3636899 = 5455349) B5455349
theorem B1212115 : Blo 1076618 1212115 := bstep (se 1 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 1212115 = 1818173) B1818173
theorem B2457425 : Blo 1076618 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B1212259 : Blo 1076618 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B2424689 : Blo 1076618 2424689 := bstep (se 2 (by rfl) ⟨909258, by rfl⟩ : syracuseStep 2424689 = 1818517) B1818517
theorem B2424707 : Blo 1076618 2424707 := bstep (se 1 (by rfl) ⟨1818530, by rfl⟩ : syracuseStep 2424707 = 3637061) B3637061
theorem B3637169 : Blo 1076618 3637169 := bstep (se 2 (by rfl) ⟨1363938, by rfl⟩ : syracuseStep 3637169 = 2727877) B2727877
theorem B1212403 : Blo 1076618 1212403 := bstep (se 1 (by rfl) ⟨909302, by rfl⟩ : syracuseStep 1212403 = 1818605) B1818605
theorem B2424833 : Blo 1076618 2424833 := bstep (se 2 (by rfl) ⟨909312, by rfl⟩ : syracuseStep 2424833 = 1818625) B1818625
theorem B1212439 : Blo 1076618 1212439 := bstep (se 1 (by rfl) ⟨909329, by rfl⟩ : syracuseStep 1212439 = 1818659) B1818659
theorem B26214475 : Blo 1076618 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B78676109 : Blo 1076618 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B1212619 : Blo 1076618 1212619 := bstep (se 1 (by rfl) ⟨909464, by rfl⟩ : syracuseStep 1212619 = 1818929) B1818929
theorem B2425049 : Blo 1076618 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B2425139 : Blo 1076618 2425139 := bstep (se 1 (by rfl) ⟨1818854, by rfl⟩ : syracuseStep 2425139 = 3637709) B3637709
theorem B1212727 : Blo 1076618 1212727 := bstep (se 1 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 1212727 = 1819091) B1819091
theorem B2425175 : Blo 1076618 2425175 := bstep (se 1 (by rfl) ⟨1818881, by rfl⟩ : syracuseStep 2425175 = 3637763) B3637763
theorem B3637655 : Blo 1076618 3637655 := bstep (se 1 (by rfl) ⟨2728241, by rfl⟩ : syracuseStep 3637655 = 5456483) B5456483
theorem B2458009 : Blo 1076618 2458009 := bstep (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) B1843507
theorem B1212907 : Blo 1076618 1212907 := bstep (se 1 (by rfl) ⟨909680, by rfl⟩ : syracuseStep 1212907 = 1819361) B1819361
theorem B2425355 : Blo 1076618 2425355 := bstep (se 1 (by rfl) ⟨1819016, by rfl⟩ : syracuseStep 2425355 = 3638033) B3638033
theorem B1638935 : Blo 1076618 1638935 := bstep (se 1 (by rfl) ⟨1229201, by rfl⟩ : syracuseStep 1638935 = 2458403) B2458403
theorem B13828643 : Blo 1076618 13828643 := bstep (se 1 (by rfl) ⟨10371482, by rfl⟩ : syracuseStep 13828643 = 20742965) B20742965
theorem B2425409 : Blo 1076618 2425409 := bstep (se 2 (by rfl) ⟨909528, by rfl⟩ : syracuseStep 2425409 = 1819057) B1819057
theorem B1213015 : Blo 1076618 1213015 := bstep (se 1 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 1213015 = 1819523) B1819523
theorem B4096601 : Blo 1076618 4096601 := bstep (se 2 (by rfl) ⟨1536225, by rfl⟩ : syracuseStep 4096601 = 3072451) B3072451
theorem B1213195 : Blo 1076618 1213195 := bstep (se 1 (by rfl) ⟨909896, by rfl⟩ : syracuseStep 1213195 = 1819793) B1819793
theorem B2425625 : Blo 1076618 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B2425715 : Blo 1076618 2425715 := bstep (se 1 (by rfl) ⟨1819286, by rfl⟩ : syracuseStep 2425715 = 3638573) B3638573
theorem B1213303 : Blo 1076618 1213303 := bstep (se 1 (by rfl) ⟨909977, by rfl⟩ : syracuseStep 1213303 = 1819955) B1819955
theorem B7373699 : Blo 1076618 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B2425751 : Blo 1076618 2425751 := bstep (se 1 (by rfl) ⟨1819313, by rfl⟩ : syracuseStep 2425751 = 3638627) B3638627
theorem B4096919 : Blo 1076618 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B3638195 : Blo 1076618 3638195 := bstep (se 1 (by rfl) ⟨2728646, by rfl⟩ : syracuseStep 3638195 = 5457293) B5457293
theorem B1213483 : Blo 1076618 1213483 := bstep (se 1 (by rfl) ⟨910112, by rfl⟩ : syracuseStep 1213483 = 1820225) B1820225
theorem B2425931 : Blo 1076618 2425931 := bstep (se 1 (by rfl) ⟨1819448, by rfl⟩ : syracuseStep 2425931 = 3638897) B3638897
theorem B2425985 : Blo 1076618 2425985 := bstep (se 2 (by rfl) ⟨909744, by rfl⟩ : syracuseStep 2425985 = 1819489) B1819489
theorem B1213591 : Blo 1076618 1213591 := bstep (se 1 (by rfl) ⟨910193, by rfl⟩ : syracuseStep 1213591 = 1820387) B1820387
theorem B3638465 : Blo 1076618 3638465 := bstep (se 2 (by rfl) ⟨1364424, by rfl⟩ : syracuseStep 3638465 = 2728849) B2728849
theorem B1213771 : Blo 1076618 1213771 := bstep (se 1 (by rfl) ⟨910328, by rfl⟩ : syracuseStep 1213771 = 1820657) B1820657
theorem B2131289 : Blo 1076618 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B2426201 : Blo 1076618 2426201 := bstep (se 2 (by rfl) ⟨909825, by rfl⟩ : syracuseStep 2426201 = 1819651) B1819651
theorem B2590103 : Blo 1076618 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B2426291 : Blo 1076618 2426291 := bstep (se 1 (by rfl) ⟨1819718, by rfl⟩ : syracuseStep 2426291 = 3639437) B3639437
theorem B1213879 : Blo 1076618 1213879 := bstep (se 1 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 1213879 = 1820819) B1820819
theorem B2426327 : Blo 1076618 2426327 := bstep (se 1 (by rfl) ⟨1819745, by rfl⟩ : syracuseStep 2426327 = 3639491) B3639491
theorem B4097587 : Blo 1076618 4097587 := bstep (se 1 (by rfl) ⟨3073190, by rfl⟩ : syracuseStep 4097587 = 6146381) B6146381
theorem B1214059 : Blo 1076618 1214059 := bstep (se 1 (by rfl) ⟨910544, by rfl⟩ : syracuseStep 1214059 = 1821089) B1821089
theorem B2426507 : Blo 1076618 2426507 := bstep (se 1 (by rfl) ⟨1819880, by rfl⟩ : syracuseStep 2426507 = 3639761) B3639761
theorem B2918039 : Blo 1076618 2918039 := bstep (se 1 (by rfl) ⟨2188529, by rfl⟩ : syracuseStep 2918039 = 4377059) B4377059
theorem B2426561 : Blo 1076618 2426561 := bstep (se 2 (by rfl) ⟨909960, by rfl⟩ : syracuseStep 2426561 = 1819921) B1819921
theorem B1214167 : Blo 1076618 1214167 := bstep (se 1 (by rfl) ⟨910625, by rfl⟩ : syracuseStep 1214167 = 1821251) B1821251
theorem B3639005 : Blo 1076618 3639005 := bstep (se 3 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 3639005 = 1364627) B1364627
theorem B1214347 : Blo 1076618 1214347 := bstep (se 1 (by rfl) ⟨910760, by rfl⟩ : syracuseStep 1214347 = 1821521) B1821521
theorem B2426777 : Blo 1076618 2426777 := bstep (se 2 (by rfl) ⟨910041, by rfl⟩ : syracuseStep 2426777 = 1820083) B1820083
theorem B2426867 : Blo 1076618 2426867 := bstep (se 1 (by rfl) ⟨1820150, by rfl⟩ : syracuseStep 2426867 = 3640301) B3640301
theorem B1214455 : Blo 1076618 1214455 := bstep (se 1 (by rfl) ⟨910841, by rfl⟩ : syracuseStep 1214455 = 1821683) B1821683
theorem B2426903 : Blo 1076618 2426903 := bstep (se 1 (by rfl) ⟨1820177, by rfl⟩ : syracuseStep 2426903 = 3640355) B3640355
theorem B15763531 : Blo 1076618 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B1214635 : Blo 1076618 1214635 := bstep (se 1 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 1214635 = 1821953) B1821953
theorem B2427083 : Blo 1076618 2427083 := bstep (se 1 (by rfl) ⟨1820312, by rfl⟩ : syracuseStep 2427083 = 3640625) B3640625
theorem B2427137 : Blo 1076618 2427137 := bstep (se 2 (by rfl) ⟨910176, by rfl⟩ : syracuseStep 2427137 = 1820353) B1820353
theorem B1214743 : Blo 1076618 1214743 := bstep (se 1 (by rfl) ⟨911057, by rfl⟩ : syracuseStep 1214743 = 1822115) B1822115
theorem B1214923 : Blo 1076618 1214923 := bstep (se 1 (by rfl) ⟨911192, by rfl⟩ : syracuseStep 1214923 = 1822385) B1822385
theorem B2427353 : Blo 1076618 2427353 := bstep (se 2 (by rfl) ⟨910257, by rfl⟩ : syracuseStep 2427353 = 1820515) B1820515
theorem B2427443 : Blo 1076618 2427443 := bstep (se 1 (by rfl) ⟨1820582, by rfl⟩ : syracuseStep 2427443 = 3641165) B3641165
theorem B1215031 : Blo 1076618 1215031 := bstep (se 1 (by rfl) ⟨911273, by rfl⟩ : syracuseStep 1215031 = 1822547) B1822547
theorem B2427479 : Blo 1076618 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B1215211 : Blo 1076618 1215211 := bstep (se 1 (by rfl) ⟨911408, by rfl⟩ : syracuseStep 1215211 = 1822817) B1822817
theorem B2427659 : Blo 1076618 2427659 := bstep (se 1 (by rfl) ⟨1820744, by rfl⟩ : syracuseStep 2427659 = 3641489) B3641489
theorem B1641227 : Blo 1076618 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B4098833 : Blo 1076618 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B2427713 : Blo 1076618 2427713 := bstep (se 2 (by rfl) ⟨910392, by rfl⟩ : syracuseStep 2427713 = 1820785) B1820785
theorem B3640139 : Blo 1076618 3640139 := bstep (se 1 (by rfl) ⟨2730104, by rfl⟩ : syracuseStep 3640139 = 5460209) B5460209
theorem B1215319 : Blo 1076618 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B1215499 : Blo 1076618 1215499 := bstep (se 1 (by rfl) ⟨911624, by rfl⟩ : syracuseStep 1215499 = 1823249) B1823249
theorem B2427929 : Blo 1076618 2427929 := bstep (se 2 (by rfl) ⟨910473, by rfl⟩ : syracuseStep 2427929 = 1820947) B1820947
theorem B1149995 : Blo 1076618 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B3640409 : Blo 1076618 3640409 := bstep (se 2 (by rfl) ⟨1365153, by rfl⟩ : syracuseStep 3640409 = 2730307) B2730307
theorem B2428019 : Blo 1076618 2428019 := bstep (se 1 (by rfl) ⟨1821014, by rfl⟩ : syracuseStep 2428019 = 3642029) B3642029
theorem B1215607 : Blo 1076618 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B2428055 : Blo 1076618 2428055 := bstep (se 1 (by rfl) ⟨1821041, by rfl⟩ : syracuseStep 2428055 = 3642083) B3642083
theorem B1150123 : Blo 1076618 1150123 := bstep (se 1 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 1150123 = 1725185) B1725185
theorem B9211097 : Blo 1076618 9211097 := bstep (se 2 (by rfl) ⟨3454161, by rfl⟩ : syracuseStep 9211097 = 6908323) B6908323
theorem B8293697 : Blo 1076618 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B2428235 : Blo 1076618 2428235 := bstep (se 1 (by rfl) ⟨1821176, by rfl⟩ : syracuseStep 2428235 = 3642353) B3642353
theorem B2428289 : Blo 1076618 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B4099531 : Blo 1076618 4099531 := bstep (se 1 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 4099531 = 6149297) B6149297
theorem B2428505 : Blo 1076618 2428505 := bstep (se 2 (by rfl) ⟨910689, by rfl⟩ : syracuseStep 2428505 = 1821379) B1821379
theorem B2428595 : Blo 1076618 2428595 := bstep (se 1 (by rfl) ⟨1821446, by rfl⟩ : syracuseStep 2428595 = 3642893) B3642893
theorem B2428631 : Blo 1076618 2428631 := bstep (se 1 (by rfl) ⟨1821473, by rfl⟩ : syracuseStep 2428631 = 3642947) B3642947
theorem B4099805 : Blo 1076618 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B3641111 : Blo 1076618 3641111 := bstep (se 1 (by rfl) ⟨2730833, by rfl⟩ : syracuseStep 3641111 = 5461667) B5461667
theorem B5246795 : Blo 1076618 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B3116875 : Blo 1076618 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B2428811 : Blo 1076618 2428811 := bstep (se 1 (by rfl) ⟨1821608, by rfl⟩ : syracuseStep 2428811 = 3643217) B3643217
theorem B2428865 : Blo 1076618 2428865 := bstep (se 2 (by rfl) ⟨910824, by rfl⟩ : syracuseStep 2428865 = 1821649) B1821649
theorem B2461697 : Blo 1076618 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B2429081 : Blo 1076618 2429081 := bstep (se 2 (by rfl) ⟨910905, by rfl⟩ : syracuseStep 2429081 = 1821811) B1821811
theorem B2429171 : Blo 1076618 2429171 := bstep (se 1 (by rfl) ⟨1821878, by rfl⟩ : syracuseStep 2429171 = 3643757) B3643757
theorem B2429207 : Blo 1076618 2429207 := bstep (se 1 (by rfl) ⟨1821905, by rfl⟩ : syracuseStep 2429207 = 3643811) B3643811
theorem B12292397 : Blo 1076618 12292397 := bstep (se 3 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 12292397 = 4609649) B4609649
theorem B3641651 : Blo 1076618 3641651 := bstep (se 1 (by rfl) ⟨2731238, by rfl⟩ : syracuseStep 3641651 = 5462477) B5462477
theorem B4100503 : Blo 1076618 4100503 := bstep (se 1 (by rfl) ⟨3075377, by rfl⟩ : syracuseStep 4100503 = 6150755) B6150755
theorem B2429387 : Blo 1076618 2429387 := bstep (se 1 (by rfl) ⟨1822040, by rfl⟩ : syracuseStep 2429387 = 3644081) B3644081
theorem B2429441 : Blo 1076618 2429441 := bstep (se 2 (by rfl) ⟨911040, by rfl⟩ : syracuseStep 2429441 = 1822081) B1822081
theorem B7377425 : Blo 1076618 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B3641921 : Blo 1076618 3641921 := bstep (se 2 (by rfl) ⟨1365720, by rfl⟩ : syracuseStep 3641921 = 2731441) B2731441
theorem B2429657 : Blo 1076618 2429657 := bstep (se 2 (by rfl) ⟨911121, by rfl⟩ : syracuseStep 2429657 = 1822243) B1822243
theorem B10490629 : Blo 1076618 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B9966341 : Blo 1076618 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2429747 : Blo 1076618 2429747 := bstep (se 1 (by rfl) ⟨1822310, by rfl⟩ : syracuseStep 2429747 = 3644621) B3644621
theorem B9212737 : Blo 1076618 9212737 := bstep (se 2 (by rfl) ⟨3454776, by rfl⟩ : syracuseStep 9212737 = 6909553) B6909553
theorem B2429783 : Blo 1076618 2429783 := bstep (se 1 (by rfl) ⟨1822337, by rfl⟩ : syracuseStep 2429783 = 3644675) B3644675
theorem B4920323 : Blo 1076618 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B2429963 : Blo 1076618 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B2430017 : Blo 1076618 2430017 := bstep (se 2 (by rfl) ⟨911256, by rfl⟩ : syracuseStep 2430017 = 1822513) B1822513
theorem B3642461 : Blo 1076618 3642461 := bstep (se 3 (by rfl) ⟨682961, by rfl⟩ : syracuseStep 3642461 = 1365923) B1365923
theorem B4101293 : Blo 1076618 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B2430233 : Blo 1076618 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B2430323 : Blo 1076618 2430323 := bstep (se 1 (by rfl) ⟨1822742, by rfl⟩ : syracuseStep 2430323 = 3645485) B3645485
theorem B2430359 : Blo 1076618 2430359 := bstep (se 1 (by rfl) ⟨1822769, by rfl⟩ : syracuseStep 2430359 = 3645539) B3645539
theorem B2594227 : Blo 1076618 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B2725427 : Blo 1076618 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B2430539 : Blo 1076618 2430539 := bstep (se 1 (by rfl) ⟨1822904, by rfl⟩ : syracuseStep 2430539 = 3645809) B3645809
theorem B2430593 : Blo 1076618 2430593 := bstep (se 2 (by rfl) ⟨911472, by rfl⟩ : syracuseStep 2430593 = 1822945) B1822945
theorem B4920983 : Blo 1076618 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B7378733 : Blo 1076618 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B2299699 : Blo 1076618 2299699 := bstep (se 1 (by rfl) ⟨1724774, by rfl⟩ : syracuseStep 2299699 = 3449549) B3449549
theorem B2725721 : Blo 1076618 2725721 := bstep (se 2 (by rfl) ⟨1022145, by rfl⟩ : syracuseStep 2725721 = 2044291) B2044291
theorem B2430809 : Blo 1076618 2430809 := bstep (se 2 (by rfl) ⟨911553, by rfl⟩ : syracuseStep 2430809 = 1823107) B1823107
theorem B2430899 : Blo 1076618 2430899 := bstep (se 1 (by rfl) ⟨1823174, by rfl⟩ : syracuseStep 2430899 = 3646349) B3646349
theorem B2430935 : Blo 1076618 2430935 := bstep (se 1 (by rfl) ⟨1823201, by rfl⟩ : syracuseStep 2430935 = 3646403) B3646403
theorem B4986845 : Blo 1076618 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B2463883 : Blo 1076618 2463883 := bstep (se 1 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 2463883 = 3695825) B3695825
theorem B2431115 : Blo 1076618 2431115 := bstep (se 1 (by rfl) ⟨1823336, by rfl⟩ : syracuseStep 2431115 = 3646673) B3646673
theorem B1153207 : Blo 1076618 1153207 := bstep (se 1 (by rfl) ⟨864905, by rfl⟩ : syracuseStep 1153207 = 1729811) B1729811
theorem B2431169 : Blo 1076618 2431169 := bstep (se 2 (by rfl) ⟨911688, by rfl⟩ : syracuseStep 2431169 = 1823377) B1823377
theorem B3643595 : Blo 1076618 3643595 := bstep (se 1 (by rfl) ⟨2732696, by rfl⟩ : syracuseStep 3643595 = 5465393) B5465393
theorem B2431385 : Blo 1076618 2431385 := bstep (se 2 (by rfl) ⟨911769, by rfl⟩ : syracuseStep 2431385 = 1823539) B1823539
theorem B2300375 : Blo 1076618 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B3643865 : Blo 1076618 3643865 := bstep (se 2 (by rfl) ⟨1366449, by rfl⟩ : syracuseStep 3643865 = 2732899) B2732899
theorem B2300417 : Blo 1076618 2300417 := bstep (se 2 (by rfl) ⟨862656, by rfl⟩ : syracuseStep 2300417 = 1725313) B1725313
theorem B4102721 : Blo 1076618 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B7772993 : Blo 1076618 7772993 := bstep (se 2 (by rfl) ⟨2914872, by rfl⟩ : syracuseStep 7772993 = 5829745) B5829745
theorem B6921035 : Blo 1076618 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1383307 : Blo 1076618 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B3939293 : Blo 1076618 3939293 := bstep (se 3 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 3939293 = 1477235) B1477235
theorem B3644567 : Blo 1076618 3644567 := bstep (se 1 (by rfl) ⟨2733425, by rfl⟩ : syracuseStep 3644567 = 5466851) B5466851
theorem B4365515 : Blo 1076618 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B2727371 : Blo 1076618 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B1941079 : Blo 1076618 1941079 := bstep (se 1 (by rfl) ⟨1455809, by rfl⟩ : syracuseStep 1941079 = 2911619) B2911619
theorem B1941121 : Blo 1076618 1941121 := bstep (se 2 (by rfl) ⟨727920, by rfl⟩ : syracuseStep 1941121 = 1455841) B1455841
theorem B3645107 : Blo 1076618 3645107 := bstep (se 1 (by rfl) ⟨2733830, by rfl⟩ : syracuseStep 3645107 = 5467661) B5467661
theorem B3645377 : Blo 1076618 3645377 := bstep (se 2 (by rfl) ⟨1367016, by rfl⟩ : syracuseStep 3645377 = 2734033) B2734033
theorem B5841227 : Blo 1076618 5841227 := bstep (se 1 (by rfl) ⟨4380920, by rfl⟩ : syracuseStep 5841227 = 8761841) B8761841
theorem B2728343 : Blo 1076618 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B6922675 : Blo 1076618 6922675 := bstep (se 1 (by rfl) ⟨5192006, by rfl⟩ : syracuseStep 6922675 = 10384013) B10384013
theorem B3645917 : Blo 1076618 3645917 := bstep (se 3 (by rfl) ⟨683609, by rfl⟩ : syracuseStep 3645917 = 1367219) B1367219
theorem B10363409 : Blo 1076618 10363409 := bstep (se 2 (by rfl) ⟨3886278, by rfl⟩ : syracuseStep 10363409 = 7772557) B7772557
theorem B3449395 : Blo 1076618 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B3449537 : Blo 1076618 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B2990785 : Blo 1076618 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B2335511 : Blo 1076618 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B2729011 : Blo 1076618 2729011 := bstep (se 1 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 2729011 = 4093517) B4093517
theorem B1614935 : Blo 1076618 1614935 := bstep (se 1 (by rfl) ⟨1211201, by rfl⟩ : syracuseStep 1614935 = 2422403) B2422403
theorem B1942679 : Blo 1076618 1942679 := bstep (se 1 (by rfl) ⟨1457009, by rfl⟩ : syracuseStep 1942679 = 2914019) B2914019
theorem B1615001 : Blo 1076618 1615001 := bstep (se 2 (by rfl) ⟨605625, by rfl⟩ : syracuseStep 1615001 = 1211251) B1211251
theorem B2729153 : Blo 1076618 2729153 := bstep (se 2 (by rfl) ⟨1023432, by rfl⟩ : syracuseStep 2729153 = 2046865) B2046865
theorem B1615115 : Blo 1076618 1615115 := bstep (se 1 (by rfl) ⟨1211336, by rfl⟩ : syracuseStep 1615115 = 2422673) B2422673
theorem B1615127 : Blo 1076618 1615127 := bstep (se 1 (by rfl) ⟨1211345, by rfl⟩ : syracuseStep 1615127 = 2422691) B2422691
theorem B11674925 : Blo 1076618 11674925 := bstep (se 3 (by rfl) ⟨2189048, by rfl⟩ : syracuseStep 11674925 = 4378097) B4378097
theorem B1615193 : Blo 1076618 1615193 := bstep (se 2 (by rfl) ⟨605697, by rfl⟩ : syracuseStep 1615193 = 1211395) B1211395
theorem B2303321 : Blo 1076618 2303321 := bstep (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) B1727491
theorem B78620053 : Blo 1076618 78620053 := bstep (se 6 (by rfl) ⟨1842657, by rfl⟩ : syracuseStep 78620053 = 3685315) B3685315
theorem B1615307 : Blo 1076618 1615307 := bstep (se 1 (by rfl) ⟨1211480, by rfl⟩ : syracuseStep 1615307 = 2422961) B2422961
theorem B1615319 : Blo 1076618 1615319 := bstep (se 1 (by rfl) ⟨1211489, by rfl⟩ : syracuseStep 1615319 = 2422979) B2422979
theorem B3941905 : Blo 1076618 3941905 := bstep (se 2 (by rfl) ⟨1478214, by rfl⟩ : syracuseStep 3941905 = 2956429) B2956429
theorem B1615385 : Blo 1076618 1615385 := bstep (se 2 (by rfl) ⟨605769, by rfl⟩ : syracuseStep 1615385 = 1211539) B1211539
theorem B15738443 : Blo 1076618 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B3647051 : Blo 1076618 3647051 := bstep (se 1 (by rfl) ⟨2735288, by rfl⟩ : syracuseStep 3647051 = 5470577) B5470577
theorem B1615499 : Blo 1076618 1615499 := bstep (se 1 (by rfl) ⟨1211624, by rfl⟩ : syracuseStep 1615499 = 2423249) B2423249
theorem B1615511 : Blo 1076618 1615511 := bstep (se 1 (by rfl) ⟨1211633, by rfl⟩ : syracuseStep 1615511 = 2423267) B2423267
theorem B17475223 : Blo 1076618 17475223 := bstep (se 1 (by rfl) ⟨13106417, by rfl⟩ : syracuseStep 17475223 = 26212835) B26212835
theorem B1615577 : Blo 1076618 1615577 := bstep (se 2 (by rfl) ⟨605841, by rfl⟩ : syracuseStep 1615577 = 1211683) B1211683
theorem B2303731 : Blo 1076618 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B1615691 : Blo 1076618 1615691 := bstep (se 1 (by rfl) ⟨1211768, by rfl⟩ : syracuseStep 1615691 = 2423537) B2423537
theorem B1615703 : Blo 1076618 1615703 := bstep (se 1 (by rfl) ⟨1211777, by rfl⟩ : syracuseStep 1615703 = 2423555) B2423555
theorem B9348965 : Blo 1076618 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B1615769 : Blo 1076618 1615769 := bstep (se 2 (by rfl) ⟨605913, by rfl⟩ : syracuseStep 1615769 = 1211827) B1211827
theorem B1615883 : Blo 1076618 1615883 := bstep (se 1 (by rfl) ⟨1211912, by rfl⟩ : syracuseStep 1615883 = 2423825) B2423825
theorem B1615895 : Blo 1076618 1615895 := bstep (se 1 (by rfl) ⟨1211921, by rfl⟩ : syracuseStep 1615895 = 2423843) B2423843
theorem B2304065 : Blo 1076618 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B1615961 : Blo 1076618 1615961 := bstep (se 2 (by rfl) ⟨605985, by rfl⟩ : syracuseStep 1615961 = 1211971) B1211971
theorem B4368563 : Blo 1076618 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B1616075 : Blo 1076618 1616075 := bstep (se 1 (by rfl) ⟨1212056, by rfl⟩ : syracuseStep 1616075 = 2424113) B2424113
theorem B1616087 : Blo 1076618 1616087 := bstep (se 1 (by rfl) ⟨1212065, by rfl⟩ : syracuseStep 1616087 = 2424131) B2424131
theorem B1616153 : Blo 1076618 1616153 := bstep (se 2 (by rfl) ⟨606057, by rfl⟩ : syracuseStep 1616153 = 1212115) B1212115
theorem B1616267 : Blo 1076618 1616267 := bstep (se 1 (by rfl) ⟨1212200, by rfl⟩ : syracuseStep 1616267 = 2424401) B2424401
theorem B1943947 : Blo 1076618 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B1616279 : Blo 1076618 1616279 := bstep (se 1 (by rfl) ⟨1212209, by rfl⟩ : syracuseStep 1616279 = 2424419) B2424419
theorem B2730419 : Blo 1076618 2730419 := bstep (se 1 (by rfl) ⟨2047814, by rfl⟩ : syracuseStep 2730419 = 4095629) B4095629
theorem B1616345 : Blo 1076618 1616345 := bstep (se 2 (by rfl) ⟨606129, by rfl⟩ : syracuseStep 1616345 = 1212259) B1212259
theorem B1616459 : Blo 1076618 1616459 := bstep (se 1 (by rfl) ⟨1212344, by rfl⟩ : syracuseStep 1616459 = 2424689) B2424689
theorem B1616471 : Blo 1076618 1616471 := bstep (se 1 (by rfl) ⟨1212353, by rfl⟩ : syracuseStep 1616471 = 2424707) B2424707
theorem B4991581 : Blo 1076618 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B11676311 : Blo 1076618 11676311 := bstep (se 1 (by rfl) ⟨8757233, by rfl⟩ : syracuseStep 11676311 = 17514467) B17514467
theorem B1616537 : Blo 1076618 1616537 := bstep (se 2 (by rfl) ⟨606201, by rfl⟩ : syracuseStep 1616537 = 1212403) B1212403
theorem B1616651 : Blo 1076618 1616651 := bstep (se 1 (by rfl) ⟨1212488, by rfl⟩ : syracuseStep 1616651 = 2424977) B2424977
theorem B1616663 : Blo 1076618 1616663 := bstep (se 1 (by rfl) ⟨1212497, by rfl⟩ : syracuseStep 1616663 = 2424995) B2424995
theorem B2304791 : Blo 1076618 2304791 := bstep (se 1 (by rfl) ⟨1728593, by rfl⟩ : syracuseStep 2304791 = 3457187) B3457187
theorem B12462893 : Blo 1076618 12462893 := bstep (se 3 (by rfl) ⟨2336792, by rfl⟩ : syracuseStep 12462893 = 4673585) B4673585
theorem B1616729 : Blo 1076618 1616729 := bstep (se 2 (by rfl) ⟨606273, by rfl⟩ : syracuseStep 1616729 = 1212547) B1212547
theorem B1616843 : Blo 1076618 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B2730955 : Blo 1076618 2730955 := bstep (se 1 (by rfl) ⟨2048216, by rfl⟩ : syracuseStep 2730955 = 4096433) B4096433
theorem B1616855 : Blo 1076618 1616855 := bstep (se 1 (by rfl) ⟨1212641, by rfl⟩ : syracuseStep 1616855 = 2425283) B2425283
theorem B1616921 : Blo 1076618 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B2731097 : Blo 1076618 2731097 := bstep (se 2 (by rfl) ⟨1024161, by rfl⟩ : syracuseStep 2731097 = 2048323) B2048323
theorem B3451997 : Blo 1076618 3451997 := bstep (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) B1294499
theorem B1617035 : Blo 1076618 1617035 := bstep (se 1 (by rfl) ⟨1212776, by rfl⟩ : syracuseStep 1617035 = 2425553) B2425553
theorem B1617047 : Blo 1076618 1617047 := bstep (se 1 (by rfl) ⟨1212785, by rfl⟩ : syracuseStep 1617047 = 2425571) B2425571
theorem B1617113 : Blo 1076618 1617113 := bstep (se 2 (by rfl) ⟨606417, by rfl⟩ : syracuseStep 1617113 = 1212835) B1212835
theorem B2338073 : Blo 1076618 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B4369729 : Blo 1076618 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B1617227 : Blo 1076618 1617227 := bstep (se 1 (by rfl) ⟨1212920, by rfl⟩ : syracuseStep 1617227 = 2425841) B2425841
theorem B1617239 : Blo 1076618 1617239 := bstep (se 1 (by rfl) ⟨1212929, by rfl⟩ : syracuseStep 1617239 = 2425859) B2425859
theorem B1617305 : Blo 1076618 1617305 := bstep (se 2 (by rfl) ⟨606489, by rfl⟩ : syracuseStep 1617305 = 1212979) B1212979
theorem B1944985 : Blo 1076618 1944985 := bstep (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) B1458739
theorem B11808179 : Blo 1076618 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B1617419 : Blo 1076618 1617419 := bstep (se 1 (by rfl) ⟨1213064, by rfl⟩ : syracuseStep 1617419 = 2426129) B2426129
theorem B1617431 : Blo 1076618 1617431 := bstep (se 1 (by rfl) ⟨1213073, by rfl⟩ : syracuseStep 1617431 = 2426147) B2426147
theorem B1617497 : Blo 1076618 1617497 := bstep (se 2 (by rfl) ⟨606561, by rfl⟩ : syracuseStep 1617497 = 1213123) B1213123
theorem B1748633 : Blo 1076618 1748633 := bstep (se 2 (by rfl) ⟨655737, by rfl⟩ : syracuseStep 1748633 = 1311475) B1311475
theorem B1617611 : Blo 1076618 1617611 := bstep (se 1 (by rfl) ⟨1213208, by rfl⟩ : syracuseStep 1617611 = 2426417) B2426417
theorem B1617623 : Blo 1076618 1617623 := bstep (se 1 (by rfl) ⟨1213217, by rfl⟩ : syracuseStep 1617623 = 2426435) B2426435
theorem B9219845 : Blo 1076618 9219845 := bstep (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) B1728721
theorem B1617689 : Blo 1076618 1617689 := bstep (se 2 (by rfl) ⟨606633, by rfl⟩ : syracuseStep 1617689 = 1213267) B1213267
theorem B1617803 : Blo 1076618 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B6139799 : Blo 1076618 6139799 := bstep (se 1 (by rfl) ⟨4604849, by rfl⟩ : syracuseStep 6139799 = 9209699) B9209699
theorem B1617815 : Blo 1076618 1617815 := bstep (se 1 (by rfl) ⟨1213361, by rfl⟩ : syracuseStep 1617815 = 2426723) B2426723
theorem B2731927 : Blo 1076618 2731927 := bstep (se 1 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 2731927 = 4097891) B4097891
theorem B1617881 : Blo 1076618 1617881 := bstep (se 2 (by rfl) ⟨606705, by rfl⟩ : syracuseStep 1617881 = 1213411) B1213411
theorem B4370507 : Blo 1076618 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B1617995 : Blo 1076618 1617995 := bstep (se 1 (by rfl) ⟨1213496, by rfl⟩ : syracuseStep 1617995 = 2426993) B2426993
theorem B1618007 : Blo 1076618 1618007 := bstep (se 1 (by rfl) ⟨1213505, by rfl⟩ : syracuseStep 1618007 = 2427011) B2427011
theorem B2044055 : Blo 1076618 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B1618073 : Blo 1076618 1618073 := bstep (se 2 (by rfl) ⟨606777, by rfl⟩ : syracuseStep 1618073 = 1213555) B1213555
theorem B4501763 : Blo 1076618 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B1618187 : Blo 1076618 1618187 := bstep (se 1 (by rfl) ⟨1213640, by rfl⟩ : syracuseStep 1618187 = 2427281) B2427281
theorem B4600081 : Blo 1076618 4600081 := bstep (se 2 (by rfl) ⟨1725030, by rfl⟩ : syracuseStep 4600081 = 3450061) B3450061
theorem B4370705 : Blo 1076618 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B1618199 : Blo 1076618 1618199 := bstep (se 1 (by rfl) ⟨1213649, by rfl⟩ : syracuseStep 1618199 = 2427299) B2427299
theorem B5189933 : Blo 1076618 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B2732363 : Blo 1076618 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B1618265 : Blo 1076618 1618265 := bstep (se 2 (by rfl) ⟨606849, by rfl⟩ : syracuseStep 1618265 = 1213699) B1213699
theorem B1618379 : Blo 1076618 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B1618391 : Blo 1076618 1618391 := bstep (se 1 (by rfl) ⟨1213793, by rfl⟩ : syracuseStep 1618391 = 2427587) B2427587
theorem B5190161 : Blo 1076618 5190161 := bstep (se 2 (by rfl) ⟨1946310, by rfl⟩ : syracuseStep 5190161 = 3892621) B3892621
theorem B1618457 : Blo 1076618 1618457 := bstep (se 2 (by rfl) ⟨606921, by rfl⟩ : syracuseStep 1618457 = 1213843) B1213843
theorem B1618571 : Blo 1076618 1618571 := bstep (se 1 (by rfl) ⟨1213928, by rfl⟩ : syracuseStep 1618571 = 2427857) B2427857
theorem B1618583 : Blo 1076618 1618583 := bstep (se 1 (by rfl) ⟨1213937, by rfl⟩ : syracuseStep 1618583 = 2427875) B2427875
theorem B8762033 : Blo 1076618 8762033 := bstep (se 2 (by rfl) ⟨3285762, by rfl⟩ : syracuseStep 8762033 = 6571525) B6571525
theorem B2044595 : Blo 1076618 2044595 := bstep (se 1 (by rfl) ⟨1533446, by rfl⟩ : syracuseStep 2044595 = 3066893) B3066893
theorem B2732737 : Blo 1076618 2732737 := bstep (se 2 (by rfl) ⟨1024776, by rfl⟩ : syracuseStep 2732737 = 2049553) B2049553
theorem B1946305 : Blo 1076618 1946305 := bstep (se 2 (by rfl) ⟨729864, by rfl⟩ : syracuseStep 1946305 = 1459729) B1459729
theorem B1618649 : Blo 1076618 1618649 := bstep (se 2 (by rfl) ⟨606993, by rfl⟩ : syracuseStep 1618649 = 1213987) B1213987
theorem B1946369 : Blo 1076618 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B7779077 : Blo 1076618 7779077 := bstep (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) B1458577
theorem B1618763 : Blo 1076618 1618763 := bstep (se 1 (by rfl) ⟨1214072, by rfl⟩ : syracuseStep 1618763 = 2428145) B2428145
theorem B1618775 : Blo 1076618 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B1618841 : Blo 1076618 1618841 := bstep (se 2 (by rfl) ⟨607065, by rfl⟩ : syracuseStep 1618841 = 1214131) B1214131
theorem B69874649 : Blo 1076618 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B1618955 : Blo 1076618 1618955 := bstep (se 1 (by rfl) ⟨1214216, by rfl⟩ : syracuseStep 1618955 = 2428433) B2428433
theorem B1618967 : Blo 1076618 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B56865827 : Blo 1076618 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B1094699 : Blo 1076618 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B1619033 : Blo 1076618 1619033 := bstep (se 2 (by rfl) ⟨607137, by rfl⟩ : syracuseStep 1619033 = 1214275) B1214275
theorem B2045081 : Blo 1076618 2045081 := bstep (se 2 (by rfl) ⟨766905, by rfl⟩ : syracuseStep 2045081 = 1533811) B1533811
theorem B2307251 : Blo 1076618 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B1619147 : Blo 1076618 1619147 := bstep (se 1 (by rfl) ⟨1214360, by rfl⟩ : syracuseStep 1619147 = 2428721) B2428721
theorem B1619159 : Blo 1076618 1619159 := bstep (se 1 (by rfl) ⟨1214369, by rfl⟩ : syracuseStep 1619159 = 2428739) B2428739
theorem B2733335 : Blo 1076618 2733335 := bstep (se 1 (by rfl) ⟨2050001, by rfl⟩ : syracuseStep 2733335 = 4100003) B4100003
theorem B1619225 : Blo 1076618 1619225 := bstep (se 2 (by rfl) ⟨607209, by rfl⟩ : syracuseStep 1619225 = 1214419) B1214419
theorem B2766145 : Blo 1076618 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B13841765 : Blo 1076618 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B1619339 : Blo 1076618 1619339 := bstep (se 1 (by rfl) ⟨1214504, by rfl⟩ : syracuseStep 1619339 = 2429009) B2429009
theorem B1619351 : Blo 1076618 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B1619417 : Blo 1076618 1619417 := bstep (se 2 (by rfl) ⟨607281, by rfl⟩ : syracuseStep 1619417 = 1214563) B1214563
theorem B1619531 : Blo 1076618 1619531 := bstep (se 1 (by rfl) ⟨1214648, by rfl⟩ : syracuseStep 1619531 = 2429297) B2429297
theorem B1619543 : Blo 1076618 1619543 := bstep (se 1 (by rfl) ⟨1214657, by rfl⟩ : syracuseStep 1619543 = 2429315) B2429315
theorem B5453405 : Blo 1076618 5453405 := bstep (se 3 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 5453405 = 2045027) B2045027
theorem B1619609 : Blo 1076618 1619609 := bstep (se 2 (by rfl) ⟨607353, by rfl⟩ : syracuseStep 1619609 = 1214707) B1214707
theorem B1619723 : Blo 1076618 1619723 := bstep (se 1 (by rfl) ⟨1214792, by rfl⟩ : syracuseStep 1619723 = 2429585) B2429585
theorem B1619735 : Blo 1076618 1619735 := bstep (se 1 (by rfl) ⟨1214801, by rfl⟩ : syracuseStep 1619735 = 2429603) B2429603
theorem B1619801 : Blo 1076618 1619801 := bstep (se 2 (by rfl) ⟨607425, by rfl⟩ : syracuseStep 1619801 = 1214851) B1214851
theorem B16824181 : Blo 1076618 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B1619915 : Blo 1076618 1619915 := bstep (se 1 (by rfl) ⟨1214936, by rfl⟩ : syracuseStep 1619915 = 2429873) B2429873
theorem B1619927 : Blo 1076618 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B1619993 : Blo 1076618 1619993 := bstep (se 2 (by rfl) ⟨607497, by rfl⟩ : syracuseStep 1619993 = 1214995) B1214995
theorem B2734145 : Blo 1076618 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B4667485 : Blo 1076618 4667485 := bstep (se 3 (by rfl) ⟨875153, by rfl⟩ : syracuseStep 4667485 = 1750307) B1750307
theorem B1620107 : Blo 1076618 1620107 := bstep (se 1 (by rfl) ⟨1215080, by rfl⟩ : syracuseStep 1620107 = 2430161) B2430161
theorem B1620119 : Blo 1076618 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B1620185 : Blo 1076618 1620185 := bstep (se 2 (by rfl) ⟨607569, by rfl⟩ : syracuseStep 1620185 = 1215139) B1215139
theorem B1816843 : Blo 1076618 1816843 := bstep (se 1 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 1816843 = 2725265) B2725265
theorem B1620299 : Blo 1076618 1620299 := bstep (se 1 (by rfl) ⟨1215224, by rfl⟩ : syracuseStep 1620299 = 2430449) B2430449
theorem B1620311 : Blo 1076618 1620311 := bstep (se 1 (by rfl) ⟨1215233, by rfl⟩ : syracuseStep 1620311 = 2430467) B2430467
theorem B2767193 : Blo 1076618 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B5912983 : Blo 1076618 5912983 := bstep (se 1 (by rfl) ⟨4434737, by rfl⟩ : syracuseStep 5912983 = 8869475) B8869475
theorem B1816985 : Blo 1076618 1816985 := bstep (se 2 (by rfl) ⟨681369, by rfl⟩ : syracuseStep 1816985 = 1362739) B1362739
theorem B1620377 : Blo 1076618 1620377 := bstep (se 2 (by rfl) ⟨607641, by rfl⟩ : syracuseStep 1620377 = 1215283) B1215283
theorem B10795481 : Blo 1076618 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B1620491 : Blo 1076618 1620491 := bstep (se 1 (by rfl) ⟨1215368, by rfl⟩ : syracuseStep 1620491 = 2430737) B2430737
theorem B1620503 : Blo 1076618 1620503 := bstep (se 1 (by rfl) ⟨1215377, by rfl⟩ : syracuseStep 1620503 = 2430755) B2430755
theorem B1817113 : Blo 1076618 1817113 := bstep (se 2 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 1817113 = 1362835) B1362835
theorem B2046539 : Blo 1076618 2046539 := bstep (se 1 (by rfl) ⟨1534904, by rfl⟩ : syracuseStep 2046539 = 3069809) B3069809
theorem B2734681 : Blo 1076618 2734681 := bstep (se 2 (by rfl) ⟨1025505, by rfl⟩ : syracuseStep 2734681 = 2051011) B2051011
theorem B1620569 : Blo 1076618 1620569 := bstep (se 2 (by rfl) ⟨607713, by rfl⟩ : syracuseStep 1620569 = 1215427) B1215427
theorem B1620683 : Blo 1076618 1620683 := bstep (se 1 (by rfl) ⟨1215512, by rfl⟩ : syracuseStep 1620683 = 2431025) B2431025
theorem B1620695 : Blo 1076618 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B2046721 : Blo 1076618 2046721 := bstep (se 2 (by rfl) ⟨767520, by rfl⟩ : syracuseStep 2046721 = 1535041) B1535041
theorem B1620761 : Blo 1076618 1620761 := bstep (se 2 (by rfl) ⟨607785, by rfl⟩ : syracuseStep 1620761 = 1215571) B1215571
theorem B4438849 : Blo 1076618 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B1620875 : Blo 1076618 1620875 := bstep (se 1 (by rfl) ⟨1215656, by rfl⟩ : syracuseStep 1620875 = 2431313) B2431313
theorem B1620887 : Blo 1076618 1620887 := bstep (se 1 (by rfl) ⟨1215665, by rfl⟩ : syracuseStep 1620887 = 2431331) B2431331
theorem B31112261 : Blo 1076618 31112261 := bstep (se 4 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 31112261 = 5833549) B5833549
theorem B1817687 : Blo 1076618 1817687 := bstep (se 1 (by rfl) ⟨1363265, by rfl⟩ : syracuseStep 1817687 = 2726531) B2726531
theorem B2047169 : Blo 1076618 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B1817815 : Blo 1076618 1817815 := bstep (se 1 (by rfl) ⟨1363361, by rfl⟩ : syracuseStep 1817815 = 2726723) B2726723
theorem B9223469 : Blo 1076618 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B4603225 : Blo 1076618 4603225 := bstep (se 2 (by rfl) ⟨1726209, by rfl⟩ : syracuseStep 4603225 = 3452419) B3452419
theorem B2047511 : Blo 1076618 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B3882647 : Blo 1076618 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B5455511 : Blo 1076618 5455511 := bstep (se 1 (by rfl) ⟨4091633, by rfl⟩ : syracuseStep 5455511 = 8183267) B8183267
theorem B1818443 : Blo 1076618 1818443 := bstep (se 1 (by rfl) ⟨1363832, by rfl⟩ : syracuseStep 1818443 = 2727665) B2727665
theorem B18693989 : Blo 1076618 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B4603841 : Blo 1076618 4603841 := bstep (se 2 (by rfl) ⟨1726440, by rfl⟩ : syracuseStep 4603841 = 3452881) B3452881
theorem B1818571 : Blo 1076618 1818571 := bstep (se 1 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 1818571 = 2727857) B2727857
theorem B18432035 : Blo 1076618 18432035 := bstep (se 1 (by rfl) ⟨13824026, by rfl⟩ : syracuseStep 18432035 = 27648053) B27648053
theorem B1458263 : Blo 1076618 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B1818713 : Blo 1076618 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B2048179 : Blo 1076618 2048179 := bstep (se 1 (by rfl) ⟨1536134, by rfl⟩ : syracuseStep 2048179 = 3072269) B3072269
theorem B1818841 : Blo 1076618 1818841 := bstep (se 2 (by rfl) ⟨682065, by rfl⟩ : syracuseStep 1818841 = 1364131) B1364131
theorem B16597349 : Blo 1076618 16597349 := bstep (se 4 (by rfl) ⟨1556001, by rfl⟩ : syracuseStep 16597349 = 3112003) B3112003
theorem B6570341 : Blo 1076618 6570341 := bstep (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) B1231939
theorem B1294807 : Blo 1076618 1294807 := bstep (se 1 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 1294807 = 1942211) B1942211
theorem B3883571 : Blo 1076618 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B6144605 : Blo 1076618 6144605 := bstep (se 3 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 6144605 = 2304227) B2304227
theorem B6898277 : Blo 1076618 6898277 := bstep (se 4 (by rfl) ⟨646713, by rfl⟩ : syracuseStep 6898277 = 1293427) B1293427
theorem B2048627 : Blo 1076618 2048627 := bstep (se 1 (by rfl) ⟨1536470, by rfl⟩ : syracuseStep 2048627 = 3072941) B3072941
theorem B2048665 : Blo 1076618 2048665 := bstep (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) B1536499
theorem B1819415 : Blo 1076618 1819415 := bstep (se 1 (by rfl) ⟨1364561, by rfl⟩ : syracuseStep 1819415 = 2729123) B2729123
theorem B13812545 : Blo 1076618 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B1819543 : Blo 1076618 1819543 := bstep (se 1 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 1819543 = 2729315) B2729315
theorem B8111027 : Blo 1076618 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B3687385 : Blo 1076618 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B1229899 : Blo 1076618 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B2049113 : Blo 1076618 2049113 := bstep (se 2 (by rfl) ⟨768417, by rfl⟩ : syracuseStep 2049113 = 1536835) B1536835
theorem B9848243 : Blo 1076618 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B1820171 : Blo 1076618 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B9225859 : Blo 1076618 9225859 := bstep (se 1 (by rfl) ⟨6919394, by rfl⟩ : syracuseStep 9225859 = 13838789) B13838789
theorem B1820299 : Blo 1076618 1820299 := bstep (se 1 (by rfl) ⟨1365224, by rfl⟩ : syracuseStep 1820299 = 2730449) B2730449
theorem B3884723 : Blo 1076618 3884723 := bstep (se 1 (by rfl) ⟨2913542, by rfl⟩ : syracuseStep 3884723 = 5827085) B5827085
theorem B1820441 : Blo 1076618 1820441 := bstep (se 2 (by rfl) ⟨682665, by rfl⟩ : syracuseStep 1820441 = 1365331) B1365331
theorem B1459993 : Blo 1076618 1459993 := bstep (se 2 (by rfl) ⟨547497, by rfl⟩ : syracuseStep 1459993 = 1094995) B1094995
theorem B2049857 : Blo 1076618 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B1820569 : Blo 1076618 1820569 := bstep (se 2 (by rfl) ⟨682713, by rfl⟩ : syracuseStep 1820569 = 1365427) B1365427
theorem B2050123 : Blo 1076618 2050123 := bstep (se 1 (by rfl) ⟨1537592, by rfl⟩ : syracuseStep 2050123 = 3075185) B3075185
theorem B4606301 : Blo 1076618 4606301 := bstep (se 3 (by rfl) ⟨863681, by rfl⟩ : syracuseStep 4606301 = 1727363) B1727363
theorem B1821143 : Blo 1076618 1821143 := bstep (se 1 (by rfl) ⟨1365857, by rfl⟩ : syracuseStep 1821143 = 2731715) B2731715
theorem B2050571 : Blo 1076618 2050571 := bstep (se 1 (by rfl) ⟨1537928, by rfl⟩ : syracuseStep 2050571 = 3075857) B3075857
theorem B9226817 : Blo 1076618 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B7490123 : Blo 1076618 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B1821271 : Blo 1076618 1821271 := bstep (se 1 (by rfl) ⟨1365953, by rfl⟩ : syracuseStep 1821271 = 2731907) B2731907
theorem B2050753 : Blo 1076618 2050753 := bstep (se 2 (by rfl) ⟨769032, by rfl⟩ : syracuseStep 2050753 = 1538065) B1538065
theorem B9849701 : Blo 1076618 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B1297291 : Blo 1076618 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B6147089 : Blo 1076618 6147089 := bstep (se 2 (by rfl) ⟨2305158, by rfl⟩ : syracuseStep 6147089 = 4610317) B4610317
theorem B2051095 : Blo 1076618 2051095 := bstep (se 1 (by rfl) ⟨1538321, by rfl⟩ : syracuseStep 2051095 = 3076643) B3076643
theorem B5459075 : Blo 1076618 5459075 := bstep (se 1 (by rfl) ⟨4094306, by rfl⟩ : syracuseStep 5459075 = 8188613) B8188613
theorem B1821899 : Blo 1076618 1821899 := bstep (se 1 (by rfl) ⟨1366424, by rfl⟩ : syracuseStep 1821899 = 2732849) B2732849
theorem B8178893 : Blo 1076618 8178893 := bstep (se 3 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 8178893 = 3067085) B3067085
theorem B1363159 : Blo 1076618 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B3460313 : Blo 1076618 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B2051315 : Blo 1076618 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B1822027 : Blo 1076618 1822027 := bstep (se 1 (by rfl) ⟨1366520, by rfl⟩ : syracuseStep 1822027 = 2733041) B2733041
theorem B3689945 : Blo 1076618 3689945 := bstep (se 2 (by rfl) ⟨1383729, by rfl⟩ : syracuseStep 3689945 = 2767459) B2767459
theorem B1822169 : Blo 1076618 1822169 := bstep (se 2 (by rfl) ⟨683313, by rfl⟩ : syracuseStep 1822169 = 1366627) B1366627
theorem B1822297 : Blo 1076618 1822297 := bstep (se 2 (by rfl) ⟨683361, by rfl⟩ : syracuseStep 1822297 = 1366723) B1366723
theorem B8179379 : Blo 1076618 8179379 := bstep (se 1 (by rfl) ⟨6134534, by rfl⟩ : syracuseStep 8179379 = 12269069) B12269069
theorem B8736473 : Blo 1076618 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B3067723 : Blo 1076618 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B1363979 : Blo 1076618 1363979 := bstep (se 1 (by rfl) ⟨1022984, by rfl⟩ : syracuseStep 1363979 = 2045969) B2045969
theorem B5525597 : Blo 1076618 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B1822871 : Blo 1076618 1822871 := bstep (se 1 (by rfl) ⟨1367153, by rfl⟩ : syracuseStep 1822871 = 2734307) B2734307
theorem B1822999 : Blo 1076618 1822999 := bstep (se 1 (by rfl) ⟨1367249, by rfl⟩ : syracuseStep 1822999 = 2734499) B2734499
theorem B3068225 : Blo 1076618 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B3330497 : Blo 1076618 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B3068567 : Blo 1076618 3068567 := bstep (se 1 (by rfl) ⟨2301425, by rfl⟩ : syracuseStep 3068567 = 4602851) B4602851
theorem B1364683 : Blo 1076618 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B14603125 : Blo 1076618 14603125 := bstep (se 5 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 14603125 = 1369043) B1369043
theorem B4608899 : Blo 1076618 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1364951 : Blo 1076618 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B2184215 : Blo 1076618 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B16634915 : Blo 1076618 16634915 := bstep (se 1 (by rfl) ⟨12476186, by rfl⟩ : syracuseStep 16634915 = 24952373) B24952373
theorem B8180837 : Blo 1076618 8180837 := bstep (se 4 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 8180837 = 1533907) B1533907
theorem B8181323 : Blo 1076618 8181323 := bstep (se 1 (by rfl) ⟨6135992, by rfl⟩ : syracuseStep 8181323 = 12271985) B12271985
theorem B1365655 : Blo 1076618 1365655 := bstep (se 1 (by rfl) ⟨1024241, by rfl⟩ : syracuseStep 1365655 = 2048483) B2048483
theorem B11655029 : Blo 1076618 11655029 := bstep (se 5 (by rfl) ⟨546329, by rfl⟩ : syracuseStep 11655029 = 1092659) B1092659
theorem B9197975 : Blo 1076618 9197975 := bstep (se 1 (by rfl) ⟨6898481, by rfl⟩ : syracuseStep 9197975 = 13796963) B13796963
theorem B7494275 : Blo 1076618 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B4741811 : Blo 1076618 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3070685 : Blo 1076618 3070685 := bstep (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) B1151507
theorem B5462801 : Blo 1076618 5462801 := bstep (se 2 (by rfl) ⟨2048550, by rfl⟩ : syracuseStep 5462801 = 4097101) B4097101
theorem B5462963 : Blo 1076618 5462963 := bstep (se 1 (by rfl) ⟨4097222, by rfl⟩ : syracuseStep 5462963 = 8194445) B8194445
theorem B14736401 : Blo 1076618 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B3071027 : Blo 1076618 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B4611275 : Blo 1076618 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B1367371 : Blo 1076618 1367371 := bstep (se 1 (by rfl) ⟨1025528, by rfl⟩ : syracuseStep 1367371 = 2051057) B2051057
theorem B2186585 : Blo 1076618 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B3890605 : Blo 1076618 3890605 := bstep (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) B1458977
theorem B4087853 : Blo 1076618 4087853 := bstep (se 3 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 4087853 = 1532945) B1532945
theorem B2187329 : Blo 1076618 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B4612247 : Blo 1076618 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B9199889 : Blo 1076618 9199889 := bstep (se 2 (by rfl) ⟨3449958, by rfl⟩ : syracuseStep 9199889 = 6899917) B6899917
theorem B6152921 : Blo 1076618 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B4088627 : Blo 1076618 4088627 := bstep (se 1 (by rfl) ⟨3066470, by rfl⟩ : syracuseStep 4088627 = 6132941) B6132941
theorem B5464907 : Blo 1076618 5464907 := bstep (se 1 (by rfl) ⟨4098680, by rfl⟩ : syracuseStep 5464907 = 8197361) B8197361
theorem B3073373 : Blo 1076618 3073373 := bstep (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) B1152515
theorem B3073601 : Blo 1076618 3073601 := bstep (se 2 (by rfl) ⟨1152600, by rfl⟩ : syracuseStep 3073601 = 2305201) B2305201
theorem B3073943 : Blo 1076618 3073943 := bstep (se 1 (by rfl) ⟨2305457, by rfl⟩ : syracuseStep 3073943 = 4610915) B4610915
theorem B3696691 : Blo 1076618 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B5826653 : Blo 1076618 5826653 := bstep (se 3 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 5826653 = 2184995) B2184995
theorem B4090115 : Blo 1076618 4090115 := bstep (se 1 (by rfl) ⟨3067586, by rfl⟩ : syracuseStep 4090115 = 6135173) B6135173
theorem B2189657 : Blo 1076618 2189657 := bstep (se 2 (by rfl) ⟨821121, by rfl⟩ : syracuseStep 2189657 = 1642243) B1642243
theorem B3893777 : Blo 1076618 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B4614707 : Blo 1076618 4614707 := bstep (se 1 (by rfl) ⟨3461030, by rfl⟩ : syracuseStep 4614707 = 6922061) B6922061
theorem B5466689 : Blo 1076618 5466689 := bstep (se 2 (by rfl) ⟨2050008, by rfl⟩ : syracuseStep 5466689 = 4100017) B4100017
theorem B18410165 : Blo 1076618 18410165 := bstep (se 5 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 18410165 = 1725953) B1725953
theorem B4090571 : Blo 1076618 4090571 := bstep (se 1 (by rfl) ⟨3067928, by rfl⟩ : syracuseStep 4090571 = 6135857) B6135857
theorem B8186669 : Blo 1076618 8186669 := bstep (se 3 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 8186669 = 3070001) B3070001
theorem B4090769 : Blo 1076618 4090769 := bstep (se 2 (by rfl) ⟨1534038, by rfl⟩ : syracuseStep 4090769 = 3068077) B3068077
theorem B27978713 : Blo 1076618 27978713 := bstep (se 2 (by rfl) ⟨10492017, by rfl⟩ : syracuseStep 27978713 = 20984035) B20984035
theorem B7761253 : Blo 1076618 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B1076619 : Blo 1076618 1076619 := bstep (se 1 (by rfl) ⟨807464, by rfl⟩ : syracuseStep 1076619 = 1614929) B1614929
theorem B1076631 : Blo 1076618 1076631 := bstep (se 1 (by rfl) ⟨807473, by rfl⟩ : syracuseStep 1076631 = 1614947) B1614947
theorem B1076651 : Blo 1076618 1076651 := bstep (se 1 (by rfl) ⟨807488, by rfl⟩ : syracuseStep 1076651 = 1614977) B1614977
theorem B1076663 : Blo 1076618 1076663 := bstep (se 1 (by rfl) ⟨807497, by rfl⟩ : syracuseStep 1076663 = 1614995) B1614995
theorem B1076683 : Blo 1076618 1076683 := bstep (se 1 (by rfl) ⟨807512, by rfl⟩ : syracuseStep 1076683 = 1615025) B1615025
theorem B1076695 : Blo 1076618 1076695 := bstep (se 1 (by rfl) ⟨807521, by rfl⟩ : syracuseStep 1076695 = 1615043) B1615043
theorem B6909401 : Blo 1076618 6909401 := bstep (se 2 (by rfl) ⟨2591025, by rfl⟩ : syracuseStep 6909401 = 5182051) B5182051
theorem B1076715 : Blo 1076618 1076715 := bstep (se 1 (by rfl) ⟨807536, by rfl⟩ : syracuseStep 1076715 = 1615073) B1615073
theorem B1076727 : Blo 1076618 1076727 := bstep (se 1 (by rfl) ⟨807545, by rfl⟩ : syracuseStep 1076727 = 1615091) B1615091
theorem B1076747 : Blo 1076618 1076747 := bstep (se 1 (by rfl) ⟨807560, by rfl⟩ : syracuseStep 1076747 = 1615121) B1615121
theorem B1076759 : Blo 1076618 1076759 := bstep (se 1 (by rfl) ⟨807569, by rfl⟩ : syracuseStep 1076759 = 1615139) B1615139
theorem B1076779 : Blo 1076618 1076779 := bstep (se 1 (by rfl) ⟨807584, by rfl⟩ : syracuseStep 1076779 = 1615169) B1615169
theorem B1076791 : Blo 1076618 1076791 := bstep (se 1 (by rfl) ⟨807593, by rfl⟩ : syracuseStep 1076791 = 1615187) B1615187
theorem B1076811 : Blo 1076618 1076811 := bstep (se 1 (by rfl) ⟨807608, by rfl⟩ : syracuseStep 1076811 = 1615217) B1615217
theorem B1076823 : Blo 1076618 1076823 := bstep (se 1 (by rfl) ⟨807617, by rfl⟩ : syracuseStep 1076823 = 1615235) B1615235
theorem B1076843 : Blo 1076618 1076843 := bstep (se 1 (by rfl) ⟨807632, by rfl⟩ : syracuseStep 1076843 = 1615265) B1615265
theorem B1076855 : Blo 1076618 1076855 := bstep (se 1 (by rfl) ⟨807641, by rfl⟩ : syracuseStep 1076855 = 1615283) B1615283
theorem B1076875 : Blo 1076618 1076875 := bstep (se 1 (by rfl) ⟨807656, by rfl⟩ : syracuseStep 1076875 = 1615313) B1615313
theorem B1076887 : Blo 1076618 1076887 := bstep (se 1 (by rfl) ⟨807665, by rfl⟩ : syracuseStep 1076887 = 1615331) B1615331
theorem B4091543 : Blo 1076618 4091543 := bstep (se 1 (by rfl) ⟨3068657, by rfl⟩ : syracuseStep 4091543 = 6137315) B6137315
theorem B1076907 : Blo 1076618 1076907 := bstep (se 1 (by rfl) ⟨807680, by rfl⟩ : syracuseStep 1076907 = 1615361) B1615361
theorem B1076919 : Blo 1076618 1076919 := bstep (se 1 (by rfl) ⟨807689, by rfl⟩ : syracuseStep 1076919 = 1615379) B1615379
theorem B1076939 : Blo 1076618 1076939 := bstep (se 1 (by rfl) ⟨807704, by rfl⟩ : syracuseStep 1076939 = 1615409) B1615409
theorem B1076951 : Blo 1076618 1076951 := bstep (se 1 (by rfl) ⟨807713, by rfl⟩ : syracuseStep 1076951 = 1615427) B1615427
theorem B1076971 : Blo 1076618 1076971 := bstep (se 1 (by rfl) ⟨807728, by rfl⟩ : syracuseStep 1076971 = 1615457) B1615457
theorem B1076983 : Blo 1076618 1076983 := bstep (se 1 (by rfl) ⟨807737, by rfl⟩ : syracuseStep 1076983 = 1615475) B1615475
theorem B10350341 : Blo 1076618 10350341 := bstep (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) B1940689
theorem B1077003 : Blo 1076618 1077003 := bstep (se 1 (by rfl) ⟨807752, by rfl⟩ : syracuseStep 1077003 = 1615505) B1615505
theorem B1077015 : Blo 1076618 1077015 := bstep (se 1 (by rfl) ⟨807761, by rfl⟩ : syracuseStep 1077015 = 1615523) B1615523
theorem B1077035 : Blo 1076618 1077035 := bstep (se 1 (by rfl) ⟨807776, by rfl⟩ : syracuseStep 1077035 = 1615553) B1615553
theorem B2912051 : Blo 1076618 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B1077047 : Blo 1076618 1077047 := bstep (se 1 (by rfl) ⟨807785, by rfl⟩ : syracuseStep 1077047 = 1615571) B1615571
theorem B1077067 : Blo 1076618 1077067 := bstep (se 1 (by rfl) ⟨807800, by rfl⟩ : syracuseStep 1077067 = 1615601) B1615601
theorem B1077079 : Blo 1076618 1077079 := bstep (se 1 (by rfl) ⟨807809, by rfl⟩ : syracuseStep 1077079 = 1615619) B1615619
theorem B3108701 : Blo 1076618 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B4091741 : Blo 1076618 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B1077099 : Blo 1076618 1077099 := bstep (se 1 (by rfl) ⟨807824, by rfl⟩ : syracuseStep 1077099 = 1615649) B1615649
theorem B1077111 : Blo 1076618 1077111 := bstep (se 1 (by rfl) ⟨807833, by rfl⟩ : syracuseStep 1077111 = 1615667) B1615667
theorem B1077131 : Blo 1076618 1077131 := bstep (se 1 (by rfl) ⟨807848, by rfl⟩ : syracuseStep 1077131 = 1615697) B1615697
theorem B1077143 : Blo 1076618 1077143 := bstep (se 1 (by rfl) ⟨807857, by rfl⟩ : syracuseStep 1077143 = 1615715) B1615715
theorem B1077163 : Blo 1076618 1077163 := bstep (se 1 (by rfl) ⟨807872, by rfl⟩ : syracuseStep 1077163 = 1615745) B1615745
theorem B1077175 : Blo 1076618 1077175 := bstep (se 1 (by rfl) ⟨807881, by rfl⟩ : syracuseStep 1077175 = 1615763) B1615763
theorem B1077195 : Blo 1076618 1077195 := bstep (se 1 (by rfl) ⟨807896, by rfl⟩ : syracuseStep 1077195 = 1615793) B1615793
theorem B1077207 : Blo 1076618 1077207 := bstep (se 1 (by rfl) ⟨807905, by rfl⟩ : syracuseStep 1077207 = 1615811) B1615811
theorem B1077227 : Blo 1076618 1077227 := bstep (se 1 (by rfl) ⟨807920, by rfl⟩ : syracuseStep 1077227 = 1615841) B1615841
theorem B1077239 : Blo 1076618 1077239 := bstep (se 1 (by rfl) ⟨807929, by rfl⟩ : syracuseStep 1077239 = 1615859) B1615859
theorem B1077259 : Blo 1076618 1077259 := bstep (se 1 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 1077259 = 1615889) B1615889
theorem B1077271 : Blo 1076618 1077271 := bstep (se 1 (by rfl) ⟨807953, by rfl⟩ : syracuseStep 1077271 = 1615907) B1615907
theorem B1077291 : Blo 1076618 1077291 := bstep (se 1 (by rfl) ⟨807968, by rfl⟩ : syracuseStep 1077291 = 1615937) B1615937
theorem B1077303 : Blo 1076618 1077303 := bstep (se 1 (by rfl) ⟨807977, by rfl⟩ : syracuseStep 1077303 = 1615955) B1615955
theorem B1077323 : Blo 1076618 1077323 := bstep (se 1 (by rfl) ⟨807992, by rfl⟩ : syracuseStep 1077323 = 1615985) B1615985
theorem B1077335 : Blo 1076618 1077335 := bstep (se 1 (by rfl) ⟨808001, by rfl⟩ : syracuseStep 1077335 = 1616003) B1616003
theorem B1077355 : Blo 1076618 1077355 := bstep (se 1 (by rfl) ⟨808016, by rfl⟩ : syracuseStep 1077355 = 1616033) B1616033
theorem B1077367 : Blo 1076618 1077367 := bstep (se 1 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 1077367 = 1616051) B1616051
theorem B1077387 : Blo 1076618 1077387 := bstep (se 1 (by rfl) ⟨808040, by rfl⟩ : syracuseStep 1077387 = 1616081) B1616081
theorem B1077399 : Blo 1076618 1077399 := bstep (se 1 (by rfl) ⟨808049, by rfl⟩ : syracuseStep 1077399 = 1616099) B1616099
theorem B1077419 : Blo 1076618 1077419 := bstep (se 1 (by rfl) ⟨808064, by rfl⟩ : syracuseStep 1077419 = 1616129) B1616129
theorem B1077431 : Blo 1076618 1077431 := bstep (se 1 (by rfl) ⟨808073, by rfl⟩ : syracuseStep 1077431 = 1616147) B1616147
theorem B3076289 : Blo 1076618 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B1077451 : Blo 1076618 1077451 := bstep (se 1 (by rfl) ⟨808088, by rfl⟩ : syracuseStep 1077451 = 1616177) B1616177
theorem B1077463 : Blo 1076618 1077463 := bstep (se 1 (by rfl) ⟨808097, by rfl⟩ : syracuseStep 1077463 = 1616195) B1616195
theorem B1077483 : Blo 1076618 1077483 := bstep (se 1 (by rfl) ⟨808112, by rfl⟩ : syracuseStep 1077483 = 1616225) B1616225
theorem B1077495 : Blo 1076618 1077495 := bstep (se 1 (by rfl) ⟨808121, by rfl⟩ : syracuseStep 1077495 = 1616243) B1616243
theorem B1077515 : Blo 1076618 1077515 := bstep (se 1 (by rfl) ⟨808136, by rfl⟩ : syracuseStep 1077515 = 1616273) B1616273
theorem B1077527 : Blo 1076618 1077527 := bstep (se 1 (by rfl) ⟨808145, by rfl⟩ : syracuseStep 1077527 = 1616291) B1616291
theorem B1077547 : Blo 1076618 1077547 := bstep (se 1 (by rfl) ⟨808160, by rfl⟩ : syracuseStep 1077547 = 1616321) B1616321
theorem B1077559 : Blo 1076618 1077559 := bstep (se 1 (by rfl) ⟨808169, by rfl⟩ : syracuseStep 1077559 = 1616339) B1616339
theorem B1077579 : Blo 1076618 1077579 := bstep (se 1 (by rfl) ⟨808184, by rfl⟩ : syracuseStep 1077579 = 1616369) B1616369
theorem B1077591 : Blo 1076618 1077591 := bstep (se 1 (by rfl) ⟨808193, by rfl⟩ : syracuseStep 1077591 = 1616387) B1616387
theorem B1077611 : Blo 1076618 1077611 := bstep (se 1 (by rfl) ⟨808208, by rfl⟩ : syracuseStep 1077611 = 1616417) B1616417
theorem B1077623 : Blo 1076618 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B1077643 : Blo 1076618 1077643 := bstep (se 1 (by rfl) ⟨808232, by rfl⟩ : syracuseStep 1077643 = 1616465) B1616465
theorem B1077655 : Blo 1076618 1077655 := bstep (se 1 (by rfl) ⟨808241, by rfl⟩ : syracuseStep 1077655 = 1616483) B1616483
theorem B1077675 : Blo 1076618 1077675 := bstep (se 1 (by rfl) ⟨808256, by rfl⟩ : syracuseStep 1077675 = 1616513) B1616513
theorem B1077687 : Blo 1076618 1077687 := bstep (se 1 (by rfl) ⟨808265, by rfl⟩ : syracuseStep 1077687 = 1616531) B1616531
theorem B1077707 : Blo 1076618 1077707 := bstep (se 1 (by rfl) ⟨808280, by rfl⟩ : syracuseStep 1077707 = 1616561) B1616561
theorem B1077719 : Blo 1076618 1077719 := bstep (se 1 (by rfl) ⟨808289, by rfl⟩ : syracuseStep 1077719 = 1616579) B1616579
theorem B5468633 : Blo 1076618 5468633 := bstep (se 2 (by rfl) ⟨2050737, by rfl⟩ : syracuseStep 5468633 = 4101475) B4101475
theorem B1077739 : Blo 1076618 1077739 := bstep (se 1 (by rfl) ⟨808304, by rfl⟩ : syracuseStep 1077739 = 1616609) B1616609
theorem B1077751 : Blo 1076618 1077751 := bstep (se 1 (by rfl) ⟨808313, by rfl⟩ : syracuseStep 1077751 = 1616627) B1616627
theorem B1077771 : Blo 1076618 1077771 := bstep (se 1 (by rfl) ⟨808328, by rfl⟩ : syracuseStep 1077771 = 1616657) B1616657
theorem B1077783 : Blo 1076618 1077783 := bstep (se 1 (by rfl) ⟨808337, by rfl⟩ : syracuseStep 1077783 = 1616675) B1616675
theorem B1077803 : Blo 1076618 1077803 := bstep (se 1 (by rfl) ⟨808352, by rfl⟩ : syracuseStep 1077803 = 1616705) B1616705
theorem B1077815 : Blo 1076618 1077815 := bstep (se 1 (by rfl) ⟨808361, by rfl⟩ : syracuseStep 1077815 = 1616723) B1616723
theorem B1077835 : Blo 1076618 1077835 := bstep (se 1 (by rfl) ⟨808376, by rfl⟩ : syracuseStep 1077835 = 1616753) B1616753
theorem B1077847 : Blo 1076618 1077847 := bstep (se 1 (by rfl) ⟨808385, by rfl⟩ : syracuseStep 1077847 = 1616771) B1616771
theorem B1077867 : Blo 1076618 1077867 := bstep (se 1 (by rfl) ⟨808400, by rfl⟩ : syracuseStep 1077867 = 1616801) B1616801
theorem B1077879 : Blo 1076618 1077879 := bstep (se 1 (by rfl) ⟨808409, by rfl⟩ : syracuseStep 1077879 = 1616819) B1616819
theorem B1077899 : Blo 1076618 1077899 := bstep (se 1 (by rfl) ⟨808424, by rfl⟩ : syracuseStep 1077899 = 1616849) B1616849
theorem B1077911 : Blo 1076618 1077911 := bstep (se 1 (by rfl) ⟨808433, by rfl⟩ : syracuseStep 1077911 = 1616867) B1616867
theorem B1077931 : Blo 1076618 1077931 := bstep (se 1 (by rfl) ⟨808448, by rfl⟩ : syracuseStep 1077931 = 1616897) B1616897
theorem B1077943 : Blo 1076618 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B1077963 : Blo 1076618 1077963 := bstep (se 1 (by rfl) ⟨808472, by rfl⟩ : syracuseStep 1077963 = 1616945) B1616945
theorem B1077975 : Blo 1076618 1077975 := bstep (se 1 (by rfl) ⟨808481, by rfl⟩ : syracuseStep 1077975 = 1616963) B1616963
theorem B1536727 : Blo 1076618 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B3076825 : Blo 1076618 3076825 := bstep (se 2 (by rfl) ⟨1153809, by rfl⟩ : syracuseStep 3076825 = 2307619) B2307619
theorem B1077995 : Blo 1076618 1077995 := bstep (se 1 (by rfl) ⟨808496, by rfl⟩ : syracuseStep 1077995 = 1616993) B1616993
theorem B1078007 : Blo 1076618 1078007 := bstep (se 1 (by rfl) ⟨808505, by rfl⟩ : syracuseStep 1078007 = 1617011) B1617011
theorem B1078027 : Blo 1076618 1078027 := bstep (se 1 (by rfl) ⟨808520, by rfl⟩ : syracuseStep 1078027 = 1617041) B1617041
theorem B1078039 : Blo 1076618 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B1078059 : Blo 1076618 1078059 := bstep (se 1 (by rfl) ⟨808544, by rfl⟩ : syracuseStep 1078059 = 1617089) B1617089
theorem B1078071 : Blo 1076618 1078071 := bstep (se 1 (by rfl) ⟨808553, by rfl⟩ : syracuseStep 1078071 = 1617107) B1617107
theorem B1078091 : Blo 1076618 1078091 := bstep (se 1 (by rfl) ⟨808568, by rfl⟩ : syracuseStep 1078091 = 1617137) B1617137
theorem B1078103 : Blo 1076618 1078103 := bstep (se 1 (by rfl) ⟨808577, by rfl⟩ : syracuseStep 1078103 = 1617155) B1617155
theorem B18445157 : Blo 1076618 18445157 := bstep (se 4 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 18445157 = 3458467) B3458467
theorem B1078123 : Blo 1076618 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1078135 : Blo 1076618 1078135 := bstep (se 1 (by rfl) ⟨808601, by rfl⟩ : syracuseStep 1078135 = 1617203) B1617203
theorem B1078155 : Blo 1076618 1078155 := bstep (se 1 (by rfl) ⟨808616, by rfl⟩ : syracuseStep 1078155 = 1617233) B1617233
theorem B2913175 : Blo 1076618 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B1078167 : Blo 1076618 1078167 := bstep (se 1 (by rfl) ⟨808625, by rfl⟩ : syracuseStep 1078167 = 1617251) B1617251
theorem B1078187 : Blo 1076618 1078187 := bstep (se 1 (by rfl) ⟨808640, by rfl⟩ : syracuseStep 1078187 = 1617281) B1617281
theorem B1078199 : Blo 1076618 1078199 := bstep (se 1 (by rfl) ⟨808649, by rfl⟩ : syracuseStep 1078199 = 1617299) B1617299
theorem B1078219 : Blo 1076618 1078219 := bstep (se 1 (by rfl) ⟨808664, by rfl⟩ : syracuseStep 1078219 = 1617329) B1617329
theorem B1078231 : Blo 1076618 1078231 := bstep (se 1 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 1078231 = 1617347) B1617347
theorem B1078251 : Blo 1076618 1078251 := bstep (se 1 (by rfl) ⟨808688, by rfl⟩ : syracuseStep 1078251 = 1617377) B1617377
theorem B1078263 : Blo 1076618 1078263 := bstep (se 1 (by rfl) ⟨808697, by rfl⟩ : syracuseStep 1078263 = 1617395) B1617395
theorem B1078283 : Blo 1076618 1078283 := bstep (se 1 (by rfl) ⟨808712, by rfl⟩ : syracuseStep 1078283 = 1617425) B1617425
theorem B3634199 : Blo 1076618 3634199 := bstep (se 1 (by rfl) ⟨2725649, by rfl⟩ : syracuseStep 3634199 = 5451299) B5451299
theorem B1078295 : Blo 1076618 1078295 := bstep (se 1 (by rfl) ⟨808721, by rfl⟩ : syracuseStep 1078295 = 1617443) B1617443
theorem B10515491 : Blo 1076618 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B1078315 : Blo 1076618 1078315 := bstep (se 1 (by rfl) ⟨808736, by rfl⟩ : syracuseStep 1078315 = 1617473) B1617473
theorem B1078327 : Blo 1076618 1078327 := bstep (se 1 (by rfl) ⟨808745, by rfl⟩ : syracuseStep 1078327 = 1617491) B1617491
theorem B6911041 : Blo 1076618 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B1078347 : Blo 1076618 1078347 := bstep (se 1 (by rfl) ⟨808760, by rfl⟩ : syracuseStep 1078347 = 1617521) B1617521
theorem B1078359 : Blo 1076618 1078359 := bstep (se 1 (by rfl) ⟨808769, by rfl⟩ : syracuseStep 1078359 = 1617539) B1617539
theorem B1078379 : Blo 1076618 1078379 := bstep (se 1 (by rfl) ⟨808784, by rfl⟩ : syracuseStep 1078379 = 1617569) B1617569
theorem B1078391 : Blo 1076618 1078391 := bstep (se 1 (by rfl) ⟨808793, by rfl⟩ : syracuseStep 1078391 = 1617587) B1617587
theorem B1078411 : Blo 1076618 1078411 := bstep (se 1 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 1078411 = 1617617) B1617617
theorem B1078423 : Blo 1076618 1078423 := bstep (se 1 (by rfl) ⟨808817, by rfl⟩ : syracuseStep 1078423 = 1617635) B1617635
theorem B1078443 : Blo 1076618 1078443 := bstep (se 1 (by rfl) ⟨808832, by rfl⟩ : syracuseStep 1078443 = 1617665) B1617665
theorem B1078455 : Blo 1076618 1078455 := bstep (se 1 (by rfl) ⟨808841, by rfl⟩ : syracuseStep 1078455 = 1617683) B1617683
theorem B1078475 : Blo 1076618 1078475 := bstep (se 1 (by rfl) ⟨808856, by rfl⟩ : syracuseStep 1078475 = 1617713) B1617713
theorem B1078487 : Blo 1076618 1078487 := bstep (se 1 (by rfl) ⟨808865, by rfl⟩ : syracuseStep 1078487 = 1617731) B1617731
theorem B1078507 : Blo 1076618 1078507 := bstep (se 1 (by rfl) ⟨808880, by rfl⟩ : syracuseStep 1078507 = 1617761) B1617761
theorem B1078519 : Blo 1076618 1078519 := bstep (se 1 (by rfl) ⟨808889, by rfl⟩ : syracuseStep 1078519 = 1617779) B1617779
theorem B1078539 : Blo 1076618 1078539 := bstep (se 1 (by rfl) ⟨808904, by rfl⟩ : syracuseStep 1078539 = 1617809) B1617809
theorem B1078551 : Blo 1076618 1078551 := bstep (se 1 (by rfl) ⟨808913, by rfl⟩ : syracuseStep 1078551 = 1617827) B1617827
theorem B1078571 : Blo 1076618 1078571 := bstep (se 1 (by rfl) ⟨808928, by rfl⟩ : syracuseStep 1078571 = 1617857) B1617857
theorem B1078583 : Blo 1076618 1078583 := bstep (se 1 (by rfl) ⟨808937, by rfl⟩ : syracuseStep 1078583 = 1617875) B1617875
theorem B1078603 : Blo 1076618 1078603 := bstep (se 1 (by rfl) ⟨808952, by rfl⟩ : syracuseStep 1078603 = 1617905) B1617905
theorem B1078615 : Blo 1076618 1078615 := bstep (se 1 (by rfl) ⟨808961, by rfl⟩ : syracuseStep 1078615 = 1617923) B1617923
theorem B1078635 : Blo 1076618 1078635 := bstep (se 1 (by rfl) ⟨808976, by rfl⟩ : syracuseStep 1078635 = 1617953) B1617953
theorem B1078647 : Blo 1076618 1078647 := bstep (se 1 (by rfl) ⟨808985, by rfl⟩ : syracuseStep 1078647 = 1617971) B1617971
theorem B1078667 : Blo 1076618 1078667 := bstep (se 1 (by rfl) ⟨809000, by rfl⟩ : syracuseStep 1078667 = 1618001) B1618001
theorem B1078679 : Blo 1076618 1078679 := bstep (se 1 (by rfl) ⟨809009, by rfl⟩ : syracuseStep 1078679 = 1618019) B1618019
theorem B1078699 : Blo 1076618 1078699 := bstep (se 1 (by rfl) ⟨809024, by rfl⟩ : syracuseStep 1078699 = 1618049) B1618049
theorem B1078711 : Blo 1076618 1078711 := bstep (se 1 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 1078711 = 1618067) B1618067
theorem B1078731 : Blo 1076618 1078731 := bstep (se 1 (by rfl) ⟨809048, by rfl⟩ : syracuseStep 1078731 = 1618097) B1618097
theorem B1078743 : Blo 1076618 1078743 := bstep (se 1 (by rfl) ⟨809057, by rfl⟩ : syracuseStep 1078743 = 1618115) B1618115
theorem B1078763 : Blo 1076618 1078763 := bstep (se 1 (by rfl) ⟨809072, by rfl⟩ : syracuseStep 1078763 = 1618145) B1618145
theorem B1078775 : Blo 1076618 1078775 := bstep (se 1 (by rfl) ⟨809081, by rfl⟩ : syracuseStep 1078775 = 1618163) B1618163
theorem B1078795 : Blo 1076618 1078795 := bstep (se 1 (by rfl) ⟨809096, by rfl⟩ : syracuseStep 1078795 = 1618193) B1618193
theorem B1078807 : Blo 1076618 1078807 := bstep (se 1 (by rfl) ⟨809105, by rfl⟩ : syracuseStep 1078807 = 1618211) B1618211
theorem B1078827 : Blo 1076618 1078827 := bstep (se 1 (by rfl) ⟨809120, by rfl⟩ : syracuseStep 1078827 = 1618241) B1618241
theorem B3634739 : Blo 1076618 3634739 := bstep (se 1 (by rfl) ⟨2726054, by rfl⟩ : syracuseStep 3634739 = 5452109) B5452109
theorem B1078839 : Blo 1076618 1078839 := bstep (se 1 (by rfl) ⟨809129, by rfl⟩ : syracuseStep 1078839 = 1618259) B1618259
theorem B1078859 : Blo 1076618 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B1078871 : Blo 1076618 1078871 := bstep (se 1 (by rfl) ⟨809153, by rfl⟩ : syracuseStep 1078871 = 1618307) B1618307
theorem B1078891 : Blo 1076618 1078891 := bstep (se 1 (by rfl) ⟨809168, by rfl⟩ : syracuseStep 1078891 = 1618337) B1618337
theorem B1078903 : Blo 1076618 1078903 := bstep (se 1 (by rfl) ⟨809177, by rfl⟩ : syracuseStep 1078903 = 1618355) B1618355
theorem B13825667 : Blo 1076618 13825667 := bstep (se 1 (by rfl) ⟨10369250, by rfl⟩ : syracuseStep 13825667 = 20738501) B20738501
theorem B1078923 : Blo 1076618 1078923 := bstep (se 1 (by rfl) ⟨809192, by rfl⟩ : syracuseStep 1078923 = 1618385) B1618385
theorem B1078935 : Blo 1076618 1078935 := bstep (se 1 (by rfl) ⟨809201, by rfl⟩ : syracuseStep 1078935 = 1618403) B1618403
theorem B1078955 : Blo 1076618 1078955 := bstep (se 1 (by rfl) ⟨809216, by rfl⟩ : syracuseStep 1078955 = 1618433) B1618433
theorem B1078967 : Blo 1076618 1078967 := bstep (se 1 (by rfl) ⟨809225, by rfl⟩ : syracuseStep 1078967 = 1618451) B1618451
theorem B2422475 : Blo 1076618 2422475 := bstep (se 1 (by rfl) ⟨1816856, by rfl⟩ : syracuseStep 2422475 = 3633713) B3633713
theorem B1078987 : Blo 1076618 1078987 := bstep (se 1 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 1078987 = 1618481) B1618481
theorem B1078999 : Blo 1076618 1078999 := bstep (se 1 (by rfl) ⟨809249, by rfl⟩ : syracuseStep 1078999 = 1618499) B1618499
theorem B1079019 : Blo 1076618 1079019 := bstep (se 1 (by rfl) ⟨809264, by rfl⟩ : syracuseStep 1079019 = 1618529) B1618529
theorem B1079031 : Blo 1076618 1079031 := bstep (se 1 (by rfl) ⟨809273, by rfl⟩ : syracuseStep 1079031 = 1618547) B1618547
theorem B2422529 : Blo 1076618 2422529 := bstep (se 2 (by rfl) ⟨908448, by rfl⟩ : syracuseStep 2422529 = 1816897) B1816897
theorem B4093699 : Blo 1076618 4093699 := bstep (se 1 (by rfl) ⟨3070274, by rfl⟩ : syracuseStep 4093699 = 6140549) B6140549
theorem B1079051 : Blo 1076618 1079051 := bstep (se 1 (by rfl) ⟨809288, by rfl⟩ : syracuseStep 1079051 = 1618577) B1618577
theorem B1079063 : Blo 1076618 1079063 := bstep (se 1 (by rfl) ⟨809297, by rfl⟩ : syracuseStep 1079063 = 1618595) B1618595
theorem B1079083 : Blo 1076618 1079083 := bstep (se 1 (by rfl) ⟨809312, by rfl⟩ : syracuseStep 1079083 = 1618625) B1618625
theorem B1079095 : Blo 1076618 1079095 := bstep (se 1 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 1079095 = 1618643) B1618643
theorem B3635009 : Blo 1076618 3635009 := bstep (se 2 (by rfl) ⟨1363128, by rfl⟩ : syracuseStep 3635009 = 2726257) B2726257
theorem B1079115 : Blo 1076618 1079115 := bstep (se 1 (by rfl) ⟨809336, by rfl⟩ : syracuseStep 1079115 = 1618673) B1618673
theorem B1079127 : Blo 1076618 1079127 := bstep (se 1 (by rfl) ⟨809345, by rfl⟩ : syracuseStep 1079127 = 1618691) B1618691
theorem B5830501 : Blo 1076618 5830501 := bstep (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) B1093219
theorem B1079147 : Blo 1076618 1079147 := bstep (se 1 (by rfl) ⟨809360, by rfl⟩ : syracuseStep 1079147 = 1618721) B1618721
theorem B1079159 : Blo 1076618 1079159 := bstep (se 1 (by rfl) ⟨809369, by rfl⟩ : syracuseStep 1079159 = 1618739) B1618739
theorem B1079179 : Blo 1076618 1079179 := bstep (se 1 (by rfl) ⟨809384, by rfl⟩ : syracuseStep 1079179 = 1618769) B1618769
theorem B1079191 : Blo 1076618 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B1079211 : Blo 1076618 1079211 := bstep (se 1 (by rfl) ⟨809408, by rfl⟩ : syracuseStep 1079211 = 1618817) B1618817
theorem B1079223 : Blo 1076618 1079223 := bstep (se 1 (by rfl) ⟨809417, by rfl⟩ : syracuseStep 1079223 = 1618835) B1618835
theorem B1079243 : Blo 1076618 1079243 := bstep (se 1 (by rfl) ⟨809432, by rfl⟩ : syracuseStep 1079243 = 1618865) B1618865
theorem B1079255 : Blo 1076618 1079255 := bstep (se 1 (by rfl) ⟨809441, by rfl⟩ : syracuseStep 1079255 = 1618883) B1618883
theorem B2422745 : Blo 1076618 2422745 := bstep (se 2 (by rfl) ⟨908529, by rfl⟩ : syracuseStep 2422745 = 1817059) B1817059
theorem B1079275 : Blo 1076618 1079275 := bstep (se 1 (by rfl) ⟨809456, by rfl⟩ : syracuseStep 1079275 = 1618913) B1618913
theorem B1079287 : Blo 1076618 1079287 := bstep (se 1 (by rfl) ⟨809465, by rfl⟩ : syracuseStep 1079287 = 1618931) B1618931
theorem B1079307 : Blo 1076618 1079307 := bstep (se 1 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 1079307 = 1618961) B1618961
theorem B1079319 : Blo 1076618 1079319 := bstep (se 1 (by rfl) ⟨809489, by rfl⟩ : syracuseStep 1079319 = 1618979) B1618979
theorem B1079339 : Blo 1076618 1079339 := bstep (se 1 (by rfl) ⟨809504, by rfl⟩ : syracuseStep 1079339 = 1619009) B1619009
theorem B5470253 : Blo 1076618 5470253 := bstep (se 3 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 5470253 = 2051345) B2051345
theorem B2422835 : Blo 1076618 2422835 := bstep (se 1 (by rfl) ⟨1817126, by rfl⟩ : syracuseStep 2422835 = 3634253) B3634253
theorem B4094003 : Blo 1076618 4094003 := bstep (se 1 (by rfl) ⟨3070502, by rfl⟩ : syracuseStep 4094003 = 6141005) B6141005
theorem B1079351 : Blo 1076618 1079351 := bstep (se 1 (by rfl) ⟨809513, by rfl⟩ : syracuseStep 1079351 = 1619027) B1619027
theorem B1079371 : Blo 1076618 1079371 := bstep (se 1 (by rfl) ⟨809528, by rfl⟩ : syracuseStep 1079371 = 1619057) B1619057
theorem B2422871 : Blo 1076618 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B1079383 : Blo 1076618 1079383 := bstep (se 1 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 1079383 = 1619075) B1619075
theorem B1079403 : Blo 1076618 1079403 := bstep (se 1 (by rfl) ⟨809552, by rfl⟩ : syracuseStep 1079403 = 1619105) B1619105
theorem B1079415 : Blo 1076618 1079415 := bstep (se 1 (by rfl) ⟨809561, by rfl⟩ : syracuseStep 1079415 = 1619123) B1619123
theorem B1079435 : Blo 1076618 1079435 := bstep (se 1 (by rfl) ⟨809576, by rfl⟩ : syracuseStep 1079435 = 1619153) B1619153
theorem B1079447 : Blo 1076618 1079447 := bstep (se 1 (by rfl) ⟨809585, by rfl⟩ : syracuseStep 1079447 = 1619171) B1619171
theorem B1079467 : Blo 1076618 1079467 := bstep (se 1 (by rfl) ⟨809600, by rfl⟩ : syracuseStep 1079467 = 1619201) B1619201
theorem B1079479 : Blo 1076618 1079479 := bstep (se 1 (by rfl) ⟨809609, by rfl⟩ : syracuseStep 1079479 = 1619219) B1619219
theorem B1079499 : Blo 1076618 1079499 := bstep (se 1 (by rfl) ⟨809624, by rfl⟩ : syracuseStep 1079499 = 1619249) B1619249
theorem B1079511 : Blo 1076618 1079511 := bstep (se 1 (by rfl) ⟨809633, by rfl⟩ : syracuseStep 1079511 = 1619267) B1619267
theorem B1079531 : Blo 1076618 1079531 := bstep (se 1 (by rfl) ⟨809648, by rfl⟩ : syracuseStep 1079531 = 1619297) B1619297
theorem B1079543 : Blo 1076618 1079543 := bstep (se 1 (by rfl) ⟨809657, by rfl⟩ : syracuseStep 1079543 = 1619315) B1619315
theorem B2423051 : Blo 1076618 2423051 := bstep (se 1 (by rfl) ⟨1817288, by rfl⟩ : syracuseStep 2423051 = 3634577) B3634577
theorem B1079563 : Blo 1076618 1079563 := bstep (se 1 (by rfl) ⟨809672, by rfl⟩ : syracuseStep 1079563 = 1619345) B1619345
theorem B1079575 : Blo 1076618 1079575 := bstep (se 1 (by rfl) ⟨809681, by rfl⟩ : syracuseStep 1079575 = 1619363) B1619363
theorem B1079595 : Blo 1076618 1079595 := bstep (se 1 (by rfl) ⟨809696, by rfl⟩ : syracuseStep 1079595 = 1619393) B1619393
theorem B1079607 : Blo 1076618 1079607 := bstep (se 1 (by rfl) ⟨809705, by rfl⟩ : syracuseStep 1079607 = 1619411) B1619411
theorem B2423105 : Blo 1076618 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B1079627 : Blo 1076618 1079627 := bstep (se 1 (by rfl) ⟨809720, by rfl⟩ : syracuseStep 1079627 = 1619441) B1619441
theorem B1079639 : Blo 1076618 1079639 := bstep (se 1 (by rfl) ⟨809729, by rfl⟩ : syracuseStep 1079639 = 1619459) B1619459
theorem B3635549 : Blo 1076618 3635549 := bstep (se 3 (by rfl) ⟨681665, by rfl⟩ : syracuseStep 3635549 = 1363331) B1363331
theorem B1079659 : Blo 1076618 1079659 := bstep (se 1 (by rfl) ⟨809744, by rfl⟩ : syracuseStep 1079659 = 1619489) B1619489
theorem B1079671 : Blo 1076618 1079671 := bstep (se 1 (by rfl) ⟨809753, by rfl⟩ : syracuseStep 1079671 = 1619507) B1619507
theorem B1079691 : Blo 1076618 1079691 := bstep (se 1 (by rfl) ⟨809768, by rfl⟩ : syracuseStep 1079691 = 1619537) B1619537
theorem B1079703 : Blo 1076618 1079703 := bstep (se 1 (by rfl) ⟨809777, by rfl⟩ : syracuseStep 1079703 = 1619555) B1619555
theorem B1079723 : Blo 1076618 1079723 := bstep (se 1 (by rfl) ⟨809792, by rfl⟩ : syracuseStep 1079723 = 1619585) B1619585
theorem B1079735 : Blo 1076618 1079735 := bstep (se 1 (by rfl) ⟨809801, by rfl⟩ : syracuseStep 1079735 = 1619603) B1619603
theorem B1079755 : Blo 1076618 1079755 := bstep (se 1 (by rfl) ⟨809816, by rfl⟩ : syracuseStep 1079755 = 1619633) B1619633
theorem B1079767 : Blo 1076618 1079767 := bstep (se 1 (by rfl) ⟨809825, by rfl⟩ : syracuseStep 1079767 = 1619651) B1619651
theorem B1079787 : Blo 1076618 1079787 := bstep (se 1 (by rfl) ⟨809840, by rfl⟩ : syracuseStep 1079787 = 1619681) B1619681
theorem B1079799 : Blo 1076618 1079799 := bstep (se 1 (by rfl) ⟨809849, by rfl⟩ : syracuseStep 1079799 = 1619699) B1619699
theorem B1079819 : Blo 1076618 1079819 := bstep (se 1 (by rfl) ⟨809864, by rfl⟩ : syracuseStep 1079819 = 1619729) B1619729
theorem B1079831 : Blo 1076618 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B2423321 : Blo 1076618 2423321 := bstep (se 2 (by rfl) ⟨908745, by rfl⟩ : syracuseStep 2423321 = 1817491) B1817491
theorem B1079851 : Blo 1076618 1079851 := bstep (se 1 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 1079851 = 1619777) B1619777
theorem B1079863 : Blo 1076618 1079863 := bstep (se 1 (by rfl) ⟨809897, by rfl⟩ : syracuseStep 1079863 = 1619795) B1619795
theorem B4323905 : Blo 1076618 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B1079883 : Blo 1076618 1079883 := bstep (se 1 (by rfl) ⟨809912, by rfl⟩ : syracuseStep 1079883 = 1619825) B1619825
theorem B1079895 : Blo 1076618 1079895 := bstep (se 1 (by rfl) ⟨809921, by rfl⟩ : syracuseStep 1079895 = 1619843) B1619843
theorem B8190557 : Blo 1076618 8190557 := bstep (se 3 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 8190557 = 3071459) B3071459
theorem B1079915 : Blo 1076618 1079915 := bstep (se 1 (by rfl) ⟨809936, by rfl⟩ : syracuseStep 1079915 = 1619873) B1619873
theorem B2423411 : Blo 1076618 2423411 := bstep (se 1 (by rfl) ⟨1817558, by rfl⟩ : syracuseStep 2423411 = 3635117) B3635117
theorem B1079927 : Blo 1076618 1079927 := bstep (se 1 (by rfl) ⟨809945, by rfl⟩ : syracuseStep 1079927 = 1619891) B1619891
theorem B1079947 : Blo 1076618 1079947 := bstep (se 1 (by rfl) ⟨809960, by rfl⟩ : syracuseStep 1079947 = 1619921) B1619921
theorem B2423447 : Blo 1076618 2423447 := bstep (se 1 (by rfl) ⟨1817585, by rfl⟩ : syracuseStep 2423447 = 3635171) B3635171
theorem B1079959 : Blo 1076618 1079959 := bstep (se 1 (by rfl) ⟨809969, by rfl⟩ : syracuseStep 1079959 = 1619939) B1619939
theorem B1079979 : Blo 1076618 1079979 := bstep (se 1 (by rfl) ⟨809984, by rfl⟩ : syracuseStep 1079979 = 1619969) B1619969
theorem B1079991 : Blo 1076618 1079991 := bstep (se 1 (by rfl) ⟨809993, by rfl⟩ : syracuseStep 1079991 = 1619987) B1619987
theorem B4094657 : Blo 1076618 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B1080011 : Blo 1076618 1080011 := bstep (se 1 (by rfl) ⟨810008, by rfl⟩ : syracuseStep 1080011 = 1620017) B1620017
theorem B1080023 : Blo 1076618 1080023 := bstep (se 1 (by rfl) ⟨810017, by rfl⟩ : syracuseStep 1080023 = 1620035) B1620035
theorem B4913885 : Blo 1076618 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B1080043 : Blo 1076618 1080043 := bstep (se 1 (by rfl) ⟨810032, by rfl⟩ : syracuseStep 1080043 = 1620065) B1620065
theorem B1080055 : Blo 1076618 1080055 := bstep (se 1 (by rfl) ⟨810041, by rfl⟩ : syracuseStep 1080055 = 1620083) B1620083
theorem B1080075 : Blo 1076618 1080075 := bstep (se 1 (by rfl) ⟨810056, by rfl⟩ : syracuseStep 1080075 = 1620113) B1620113
theorem B1080087 : Blo 1076618 1080087 := bstep (se 1 (by rfl) ⟨810065, by rfl⟩ : syracuseStep 1080087 = 1620131) B1620131
theorem B1080107 : Blo 1076618 1080107 := bstep (se 1 (by rfl) ⟨810080, by rfl⟩ : syracuseStep 1080107 = 1620161) B1620161
theorem B1080119 : Blo 1076618 1080119 := bstep (se 1 (by rfl) ⟨810089, by rfl⟩ : syracuseStep 1080119 = 1620179) B1620179
theorem B2423627 : Blo 1076618 2423627 := bstep (se 1 (by rfl) ⟨1817720, by rfl⟩ : syracuseStep 2423627 = 3635441) B3635441
theorem B1080139 : Blo 1076618 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1080151 : Blo 1076618 1080151 := bstep (se 1 (by rfl) ⟨810113, by rfl⟩ : syracuseStep 1080151 = 1620227) B1620227
theorem B1080171 : Blo 1076618 1080171 := bstep (se 1 (by rfl) ⟨810128, by rfl⟩ : syracuseStep 1080171 = 1620257) B1620257
theorem B1080183 : Blo 1076618 1080183 := bstep (se 1 (by rfl) ⟨810137, by rfl⟩ : syracuseStep 1080183 = 1620275) B1620275
theorem B2423681 : Blo 1076618 2423681 := bstep (se 2 (by rfl) ⟨908880, by rfl⟩ : syracuseStep 2423681 = 1817761) B1817761
theorem B1080203 : Blo 1076618 1080203 := bstep (se 1 (by rfl) ⟨810152, by rfl⟩ : syracuseStep 1080203 = 1620305) B1620305
theorem B1211287 : Blo 1076618 1211287 := bstep (se 1 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 1211287 = 1816931) B1816931
theorem B1080215 : Blo 1076618 1080215 := bstep (se 1 (by rfl) ⟨810161, by rfl⟩ : syracuseStep 1080215 = 1620323) B1620323
theorem B1080235 : Blo 1076618 1080235 := bstep (se 1 (by rfl) ⟨810176, by rfl⟩ : syracuseStep 1080235 = 1620353) B1620353
theorem B1080247 : Blo 1076618 1080247 := bstep (se 1 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 1080247 = 1620371) B1620371
theorem B1080267 : Blo 1076618 1080267 := bstep (se 1 (by rfl) ⟨810200, by rfl⟩ : syracuseStep 1080267 = 1620401) B1620401
theorem B1080279 : Blo 1076618 1080279 := bstep (se 1 (by rfl) ⟨810209, by rfl⟩ : syracuseStep 1080279 = 1620419) B1620419
theorem B1080299 : Blo 1076618 1080299 := bstep (se 1 (by rfl) ⟨810224, by rfl⟩ : syracuseStep 1080299 = 1620449) B1620449
theorem B1080311 : Blo 1076618 1080311 := bstep (se 1 (by rfl) ⟨810233, by rfl⟩ : syracuseStep 1080311 = 1620467) B1620467
theorem B4914179 : Blo 1076618 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B1080331 : Blo 1076618 1080331 := bstep (se 1 (by rfl) ⟨810248, by rfl⟩ : syracuseStep 1080331 = 1620497) B1620497
theorem B1080343 : Blo 1076618 1080343 := bstep (se 1 (by rfl) ⟨810257, by rfl⟩ : syracuseStep 1080343 = 1620515) B1620515
theorem B1080363 : Blo 1076618 1080363 := bstep (se 1 (by rfl) ⟨810272, by rfl⟩ : syracuseStep 1080363 = 1620545) B1620545
theorem B1080375 : Blo 1076618 1080375 := bstep (se 1 (by rfl) ⟨810281, by rfl⟩ : syracuseStep 1080375 = 1620563) B1620563
theorem B1211467 : Blo 1076618 1211467 := bstep (se 1 (by rfl) ⟨908600, by rfl⟩ : syracuseStep 1211467 = 1817201) B1817201
theorem B1080395 : Blo 1076618 1080395 := bstep (se 1 (by rfl) ⟨810296, by rfl⟩ : syracuseStep 1080395 = 1620593) B1620593
theorem B1080407 : Blo 1076618 1080407 := bstep (se 1 (by rfl) ⟨810305, by rfl⟩ : syracuseStep 1080407 = 1620611) B1620611
theorem B2423897 : Blo 1076618 2423897 := bstep (se 2 (by rfl) ⟨908961, by rfl⟩ : syracuseStep 2423897 = 1817923) B1817923
theorem B1080427 : Blo 1076618 1080427 := bstep (se 1 (by rfl) ⟨810320, by rfl⟩ : syracuseStep 1080427 = 1620641) B1620641
theorem B1080439 : Blo 1076618 1080439 := bstep (se 1 (by rfl) ⟨810329, by rfl⟩ : syracuseStep 1080439 = 1620659) B1620659
theorem B1080459 : Blo 1076618 1080459 := bstep (se 1 (by rfl) ⟨810344, by rfl⟩ : syracuseStep 1080459 = 1620689) B1620689
theorem B1080471 : Blo 1076618 1080471 := bstep (se 1 (by rfl) ⟨810353, by rfl⟩ : syracuseStep 1080471 = 1620707) B1620707
theorem B1080491 : Blo 1076618 1080491 := bstep (se 1 (by rfl) ⟨810368, by rfl⟩ : syracuseStep 1080491 = 1620737) B1620737
theorem B2423987 : Blo 1076618 2423987 := bstep (se 1 (by rfl) ⟨1817990, by rfl⟩ : syracuseStep 2423987 = 3635981) B3635981
theorem B1211575 : Blo 1076618 1211575 := bstep (se 1 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 1211575 = 1817363) B1817363
theorem B1080503 : Blo 1076618 1080503 := bstep (se 1 (by rfl) ⟨810377, by rfl⟩ : syracuseStep 1080503 = 1620755) B1620755
theorem B1080523 : Blo 1076618 1080523 := bstep (se 1 (by rfl) ⟨810392, by rfl⟩ : syracuseStep 1080523 = 1620785) B1620785
theorem B2424023 : Blo 1076618 2424023 := bstep (se 1 (by rfl) ⟨1818017, by rfl⟩ : syracuseStep 2424023 = 3636035) B3636035
theorem B1080535 : Blo 1076618 1080535 := bstep (se 1 (by rfl) ⟨810401, by rfl⟩ : syracuseStep 1080535 = 1620803) B1620803
theorem B1080555 : Blo 1076618 1080555 := bstep (se 1 (by rfl) ⟨810416, by rfl⟩ : syracuseStep 1080555 = 1620833) B1620833
theorem B1080567 : Blo 1076618 1080567 := bstep (se 1 (by rfl) ⟨810425, by rfl⟩ : syracuseStep 1080567 = 1620851) B1620851
theorem B1080587 : Blo 1076618 1080587 := bstep (se 1 (by rfl) ⟨810440, by rfl⟩ : syracuseStep 1080587 = 1620881) B1620881
theorem B1080599 : Blo 1076618 1080599 := bstep (se 1 (by rfl) ⟨810449, by rfl⟩ : syracuseStep 1080599 = 1620899) B1620899
theorem B1211755 : Blo 1076618 1211755 := bstep (se 1 (by rfl) ⟨908816, by rfl⟩ : syracuseStep 1211755 = 1817633) B1817633
theorem B15564149 : Blo 1076618 15564149 := bstep (se 5 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 15564149 = 1459139) B1459139
theorem B2424203 : Blo 1076618 2424203 := bstep (se 1 (by rfl) ⟨1818152, by rfl⟩ : syracuseStep 2424203 = 3636305) B3636305
theorem B2424257 : Blo 1076618 2424257 := bstep (se 2 (by rfl) ⟨909096, by rfl⟩ : syracuseStep 2424257 = 1818193) B1818193
theorem B3636683 : Blo 1076618 3636683 := bstep (se 1 (by rfl) ⟨2727512, by rfl⟩ : syracuseStep 3636683 = 5455025) B5455025
theorem B1211863 : Blo 1076618 1211863 := bstep (se 1 (by rfl) ⟨908897, by rfl⟩ : syracuseStep 1211863 = 1817795) B1817795
theorem B1998361 : Blo 1076618 1998361 := bstep (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) B1498771
theorem B6553133 : Blo 1076618 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B1212043 : Blo 1076618 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B2424473 : Blo 1076618 2424473 := bstep (se 2 (by rfl) ⟨909177, by rfl⟩ : syracuseStep 2424473 = 1818355) B1818355
theorem B3636953 : Blo 1076618 3636953 := bstep (se 2 (by rfl) ⟨1363857, by rfl⟩ : syracuseStep 3636953 = 2727715) B2727715
theorem B2424563 : Blo 1076618 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B1212151 : Blo 1076618 1212151 := bstep (se 1 (by rfl) ⟨909113, by rfl⟩ : syracuseStep 1212151 = 1818227) B1818227
theorem B2424599 : Blo 1076618 2424599 := bstep (se 1 (by rfl) ⟨1818449, by rfl⟩ : syracuseStep 2424599 = 3636899) B3636899
theorem B1212331 : Blo 1076618 1212331 := bstep (se 1 (by rfl) ⟨909248, by rfl⟩ : syracuseStep 1212331 = 1818497) B1818497
theorem B4095917 : Blo 1076618 4095917 := bstep (se 3 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 4095917 = 1535969) B1535969
theorem B2424779 : Blo 1076618 2424779 := bstep (se 1 (by rfl) ⟨1818584, by rfl⟩ : syracuseStep 2424779 = 3637169) B3637169
theorem B4095947 : Blo 1076618 4095947 := bstep (se 1 (by rfl) ⟨3071960, by rfl⟩ : syracuseStep 4095947 = 6143921) B6143921
theorem B12288023 : Blo 1076618 12288023 := bstep (se 1 (by rfl) ⟨9216017, by rfl⟩ : syracuseStep 12288023 = 18432035) B18432035
theorem B3637277 : Blo 1076618 3637277 := bstep (se 3 (by rfl) ⟨681989, by rfl⟩ : syracuseStep 3637277 = 1363979) B1363979
theorem B1212475 : Blo 1076618 1212475 := bstep (se 1 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 1212475 = 1818713) B1818713
theorem B23298293 : Blo 1076618 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2425103 : Blo 1076618 2425103 := bstep (se 1 (by rfl) ⟨1818827, by rfl⟩ : syracuseStep 2425103 = 3637655) B3637655
theorem B2425121 : Blo 1076618 2425121 := bstep (se 2 (by rfl) ⟨909420, by rfl⟩ : syracuseStep 2425121 = 1818841) B1818841
theorem B2589047 : Blo 1076618 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B4096403 : Blo 1076618 4096403 := bstep (se 1 (by rfl) ⟨3072302, by rfl⟩ : syracuseStep 4096403 = 6144605) B6144605
theorem B1212943 : Blo 1076618 1212943 := bstep (se 1 (by rfl) ⟨909707, by rfl⟩ : syracuseStep 1212943 = 1819415) B1819415
theorem B3277345 : Blo 1076618 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B9208363 : Blo 1076618 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B4915799 : Blo 1076618 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B2425463 : Blo 1076618 2425463 := bstep (se 1 (by rfl) ⟨1819097, by rfl⟩ : syracuseStep 2425463 = 3638195) B3638195
theorem B23331509 : Blo 1076618 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B2425643 : Blo 1076618 2425643 := bstep (se 1 (by rfl) ⟨1819232, by rfl⟩ : syracuseStep 2425643 = 3638465) B3638465
theorem B1213447 : Blo 1076618 1213447 := bstep (se 1 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 1213447 = 1820171) B1820171
theorem B2589815 : Blo 1076618 2589815 := bstep (se 1 (by rfl) ⟨1942361, by rfl⟩ : syracuseStep 2589815 = 3884723) B3884723
theorem B2426003 : Blo 1076618 2426003 := bstep (se 1 (by rfl) ⟨1819502, by rfl⟩ : syracuseStep 2426003 = 3639005) B3639005
theorem B8881325 : Blo 1076618 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B1213627 : Blo 1076618 1213627 := bstep (se 1 (by rfl) ⟨910220, by rfl⟩ : syracuseStep 1213627 = 1820441) B1820441
theorem B2426057 : Blo 1076618 2426057 := bstep (se 2 (by rfl) ⟨909771, by rfl⟩ : syracuseStep 2426057 = 1819543) B1819543
theorem B4916513 : Blo 1076618 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B3638681 : Blo 1076618 3638681 := bstep (se 2 (by rfl) ⟨1364505, by rfl⟩ : syracuseStep 3638681 = 2729011) B2729011
theorem B1639865 : Blo 1076618 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B1214095 : Blo 1076618 1214095 := bstep (se 1 (by rfl) ⟨910571, by rfl⟩ : syracuseStep 1214095 = 1821143) B1821143
theorem B104826737 : Blo 1076618 104826737 := bstep (se 2 (by rfl) ⟨39310026, by rfl⟩ : syracuseStep 104826737 = 78620053) B78620053
theorem B2426759 : Blo 1076618 2426759 := bstep (se 1 (by rfl) ⟨1820069, by rfl⟩ : syracuseStep 2426759 = 3640139) B3640139
theorem B4098059 : Blo 1076618 4098059 := bstep (se 1 (by rfl) ⟨3073544, by rfl⟩ : syracuseStep 4098059 = 6147089) B6147089
theorem B2426939 : Blo 1076618 2426939 := bstep (se 1 (by rfl) ⟨1820204, by rfl⟩ : syracuseStep 2426939 = 3640409) B3640409
theorem B6228029 : Blo 1076618 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B3639383 : Blo 1076618 3639383 := bstep (se 1 (by rfl) ⟨2729537, by rfl⟩ : syracuseStep 3639383 = 5459075) B5459075
theorem B1214599 : Blo 1076618 1214599 := bstep (se 1 (by rfl) ⟨910949, by rfl⟩ : syracuseStep 1214599 = 1821899) B1821899
theorem B2427065 : Blo 1076618 2427065 := bstep (se 2 (by rfl) ⟨910149, by rfl⟩ : syracuseStep 2427065 = 1820299) B1820299
theorem B23300297 : Blo 1076618 23300297 := bstep (se 2 (by rfl) ⟨8737611, by rfl⟩ : syracuseStep 23300297 = 17475223) B17475223
theorem B2459963 : Blo 1076618 2459963 := bstep (se 1 (by rfl) ⟨1844972, by rfl⟩ : syracuseStep 2459963 = 3689945) B3689945
theorem B1214779 : Blo 1076618 1214779 := bstep (se 1 (by rfl) ⟨911084, by rfl⟩ : syracuseStep 1214779 = 1822169) B1822169
theorem B21629405 : Blo 1076618 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B2427407 : Blo 1076618 2427407 := bstep (se 1 (by rfl) ⟨1820555, by rfl⟩ : syracuseStep 2427407 = 3641111) B3641111
theorem B2427425 : Blo 1076618 2427425 := bstep (se 2 (by rfl) ⟨910284, by rfl⟩ : syracuseStep 2427425 = 1820569) B1820569
theorem B3639869 : Blo 1076618 3639869 := bstep (se 3 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 3639869 = 1364951) B1364951
theorem B1641131 : Blo 1076618 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B1215247 : Blo 1076618 1215247 := bstep (se 1 (by rfl) ⟨911435, by rfl⟩ : syracuseStep 1215247 = 1822871) B1822871
theorem B2919197 : Blo 1076618 2919197 := bstep (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) B1094699
theorem B8194931 : Blo 1076618 8194931 := bstep (se 1 (by rfl) ⟨6146198, by rfl⟩ : syracuseStep 8194931 = 12292397) B12292397
theorem B2427767 : Blo 1076618 2427767 := bstep (se 1 (by rfl) ⟨1820825, by rfl⟩ : syracuseStep 2427767 = 3641651) B3641651
theorem B52562837 : Blo 1076618 52562837 := bstep (se 6 (by rfl) ⟨1231941, by rfl⟩ : syracuseStep 52562837 = 2463883) B2463883
theorem B4918283 : Blo 1076618 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B2427947 : Blo 1076618 2427947 := bstep (se 1 (by rfl) ⟨1820960, by rfl⟩ : syracuseStep 2427947 = 3641921) B3641921
theorem B2591929 : Blo 1076618 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B2428307 : Blo 1076618 2428307 := bstep (se 1 (by rfl) ⟨1821230, by rfl⟩ : syracuseStep 2428307 = 3642461) B3642461
theorem B2428361 : Blo 1076618 2428361 := bstep (se 2 (by rfl) ⟨910635, by rfl⟩ : syracuseStep 2428361 = 1821271) B1821271
theorem B6655441 : Blo 1076618 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B3280655 : Blo 1076618 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B7770019 : Blo 1076618 7770019 := bstep (se 1 (by rfl) ⟨5827514, by rfl⟩ : syracuseStep 7770019 = 11655029) B11655029
theorem B3641273 : Blo 1076618 3641273 := bstep (se 2 (by rfl) ⟨1365477, by rfl⟩ : syracuseStep 3641273 = 2730955) B2730955
theorem B2429063 : Blo 1076618 2429063 := bstep (se 1 (by rfl) ⟨1821797, by rfl⟩ : syracuseStep 2429063 = 3643595) B3643595
theorem B6131983 : Blo 1076618 6131983 := bstep (se 1 (by rfl) ⟨4598987, by rfl⟩ : syracuseStep 6131983 = 9197975) B9197975
theorem B2429243 : Blo 1076618 2429243 := bstep (se 1 (by rfl) ⟨1821932, by rfl⟩ : syracuseStep 2429243 = 3643865) B3643865
theorem B2429369 : Blo 1076618 2429369 := bstep (se 2 (by rfl) ⟨911013, by rfl⟩ : syracuseStep 2429369 = 1822027) B1822027
theorem B3641867 : Blo 1076618 3641867 := bstep (se 1 (by rfl) ⟨2731400, by rfl⟩ : syracuseStep 3641867 = 5462801) B5462801
theorem B2593313 : Blo 1076618 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B5181995 : Blo 1076618 5181995 := bstep (se 1 (by rfl) ⟨3886496, by rfl⟩ : syracuseStep 5181995 = 7772993) B7772993
theorem B3641975 : Blo 1076618 3641975 := bstep (se 1 (by rfl) ⟨2731481, by rfl⟩ : syracuseStep 3641975 = 5462963) B5462963
theorem B2626195 : Blo 1076618 2626195 := bstep (se 1 (by rfl) ⟨1969646, by rfl⟩ : syracuseStep 2626195 = 3939293) B3939293
theorem B7377637 : Blo 1076618 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B2429711 : Blo 1076618 2429711 := bstep (se 1 (by rfl) ⟨1822283, by rfl⟩ : syracuseStep 2429711 = 3644567) B3644567
theorem B2429729 : Blo 1076618 2429729 := bstep (se 2 (by rfl) ⟨911148, by rfl⟩ : syracuseStep 2429729 = 1822297) B1822297
theorem B2430071 : Blo 1076618 2430071 := bstep (se 1 (by rfl) ⟨1822553, by rfl⟩ : syracuseStep 2430071 = 3645107) B3645107
theorem B3642569 : Blo 1076618 3642569 := bstep (se 2 (by rfl) ⟨1365963, by rfl⟩ : syracuseStep 3642569 = 2731927) B2731927
theorem B2430251 : Blo 1076618 2430251 := bstep (se 1 (by rfl) ⟨1822688, by rfl⟩ : syracuseStep 2430251 = 3645377) B3645377
theorem B2725235 : Blo 1076618 2725235 := bstep (se 1 (by rfl) ⟨2043926, by rfl⟩ : syracuseStep 2725235 = 4087853) B4087853
theorem B6133259 : Blo 1076618 6133259 := bstep (se 1 (by rfl) ⟨4599944, by rfl⟩ : syracuseStep 6133259 = 9199889) B9199889
theorem B2430611 : Blo 1076618 2430611 := bstep (se 1 (by rfl) ⟨1822958, by rfl⟩ : syracuseStep 2430611 = 3645917) B3645917
theorem B6133441 : Blo 1076618 6133441 := bstep (se 2 (by rfl) ⟨2300040, by rfl⟩ : syracuseStep 6133441 = 4600081) B4600081
theorem B2430665 : Blo 1076618 2430665 := bstep (se 2 (by rfl) ⟨911499, by rfl⟩ : syracuseStep 2430665 = 1822999) B1822999
theorem B2299691 : Blo 1076618 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B4101947 : Blo 1076618 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B2725751 : Blo 1076618 2725751 := bstep (se 1 (by rfl) ⟨2044313, by rfl⟩ : syracuseStep 2725751 = 4088627) B4088627
theorem B3643271 : Blo 1076618 3643271 := bstep (se 1 (by rfl) ⟨2732453, by rfl⟩ : syracuseStep 3643271 = 5464907) B5464907
theorem B5839085 : Blo 1076618 5839085 := bstep (se 3 (by rfl) ⟨1094828, by rfl⟩ : syracuseStep 5839085 = 2189657) B2189657
theorem B3643649 : Blo 1076618 3643649 := bstep (se 2 (by rfl) ⟨1366368, by rfl⟩ : syracuseStep 3643649 = 2732737) B2732737
theorem B2595073 : Blo 1076618 2595073 := bstep (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) B1946305
theorem B4102433 : Blo 1076618 4102433 := bstep (se 2 (by rfl) ⟨1538412, by rfl⟩ : syracuseStep 4102433 = 3076825) B3076825
theorem B10492295 : Blo 1076618 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B2431367 : Blo 1076618 2431367 := bstep (se 1 (by rfl) ⟨1823525, by rfl⟩ : syracuseStep 2431367 = 3647051) B3647051
theorem B19470833 : Blo 1076618 19470833 := bstep (se 2 (by rfl) ⟨7301562, by rfl⟩ : syracuseStep 19470833 = 14603125) B14603125
theorem B6232643 : Blo 1076618 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B9214721 : Blo 1076618 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B2726743 : Blo 1076618 2726743 := bstep (se 1 (by rfl) ⟨2045057, by rfl⟩ : syracuseStep 2726743 = 4090115) B4090115
theorem B2595851 : Blo 1076618 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B3644459 : Blo 1076618 3644459 := bstep (se 1 (by rfl) ⟨2733344, by rfl⟩ : syracuseStep 3644459 = 5466689) B5466689
theorem B2727047 : Blo 1076618 2727047 := bstep (se 1 (by rfl) ⟨2045285, by rfl⟩ : syracuseStep 2727047 = 4090571) B4090571
theorem B2727179 : Blo 1076618 2727179 := bstep (se 1 (by rfl) ⟨2045384, by rfl⟩ : syracuseStep 2727179 = 4090769) B4090769
theorem B18652475 : Blo 1076618 18652475 := bstep (se 1 (by rfl) ⟨13989356, by rfl⟩ : syracuseStep 18652475 = 27978713) B27978713
theorem B7872119 : Blo 1076618 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B2727695 : Blo 1076618 2727695 := bstep (se 1 (by rfl) ⟨2045771, by rfl⟩ : syracuseStep 2727695 = 4091543) B4091543
theorem B7774001 : Blo 1076618 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B2727827 : Blo 1076618 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B10657925 : Blo 1076618 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B3645755 : Blo 1076618 3645755 := bstep (se 1 (by rfl) ⟨2734316, by rfl⟩ : syracuseStep 3645755 = 5468633) B5468633
theorem B5841355 : Blo 1076618 5841355 := bstep (se 1 (by rfl) ⟨4381016, by rfl⟩ : syracuseStep 5841355 = 8762033) B8762033
theorem B5186051 : Blo 1076618 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B12296771 : Blo 1076618 12296771 := bstep (se 1 (by rfl) ⟨9222578, by rfl⟩ : syracuseStep 12296771 = 18445157) B18445157
theorem B3646241 : Blo 1076618 3646241 := bstep (se 2 (by rfl) ⟨1367340, by rfl⟩ : syracuseStep 3646241 = 2734681) B2734681
theorem B2728961 : Blo 1076618 2728961 := bstep (se 2 (by rfl) ⟨1023360, by rfl⟩ : syracuseStep 2728961 = 2046721) B2046721
theorem B9217111 : Blo 1076618 9217111 := bstep (se 1 (by rfl) ⟨6912833, by rfl⟩ : syracuseStep 9217111 = 13825667) B13825667
theorem B1614983 : Blo 1076618 1614983 := bstep (se 1 (by rfl) ⟨1211237, by rfl⟩ : syracuseStep 1614983 = 2422475) B2422475
theorem B1615019 : Blo 1076618 1615019 := bstep (se 1 (by rfl) ⟨1211264, by rfl⟩ : syracuseStep 1615019 = 2422529) B2422529
theorem B1615049 : Blo 1076618 1615049 := bstep (se 2 (by rfl) ⟨605643, by rfl⟩ : syracuseStep 1615049 = 1211287) B1211287
theorem B1615163 : Blo 1076618 1615163 := bstep (se 1 (by rfl) ⟨1211372, by rfl⟩ : syracuseStep 1615163 = 2422745) B2422745
theorem B3646835 : Blo 1076618 3646835 := bstep (se 1 (by rfl) ⟨2735126, by rfl⟩ : syracuseStep 3646835 = 5470253) B5470253
theorem B1615223 : Blo 1076618 1615223 := bstep (se 1 (by rfl) ⟨1211417, by rfl⟩ : syracuseStep 1615223 = 2422835) B2422835
theorem B2729335 : Blo 1076618 2729335 := bstep (se 1 (by rfl) ⟨2047001, by rfl⟩ : syracuseStep 2729335 = 4094003) B4094003
theorem B1615247 : Blo 1076618 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B1615289 : Blo 1076618 1615289 := bstep (se 2 (by rfl) ⟨605733, by rfl⟩ : syracuseStep 1615289 = 1211467) B1211467
theorem B1615367 : Blo 1076618 1615367 := bstep (se 1 (by rfl) ⟨1211525, by rfl⟩ : syracuseStep 1615367 = 2423051) B2423051
theorem B1615403 : Blo 1076618 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B1844795 : Blo 1076618 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B1615433 : Blo 1076618 1615433 := bstep (se 2 (by rfl) ⟨605787, by rfl⟩ : syracuseStep 1615433 = 1211575) B1211575
theorem B1615547 : Blo 1076618 1615547 := bstep (se 1 (by rfl) ⟨1211660, by rfl⟩ : syracuseStep 1615547 = 2423321) B2423321
theorem B4663021 : Blo 1076618 4663021 := bstep (se 3 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 4663021 = 1748633) B1748633
theorem B1615607 : Blo 1076618 1615607 := bstep (se 1 (by rfl) ⟨1211705, by rfl⟩ : syracuseStep 1615607 = 2423411) B2423411
theorem B1615631 : Blo 1076618 1615631 := bstep (se 1 (by rfl) ⟨1211723, by rfl⟩ : syracuseStep 1615631 = 2423447) B2423447
theorem B6137633 : Blo 1076618 6137633 := bstep (se 2 (by rfl) ⟨2301612, by rfl⟩ : syracuseStep 6137633 = 4603225) B4603225
theorem B2729771 : Blo 1076618 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B1615673 : Blo 1076618 1615673 := bstep (se 2 (by rfl) ⟨605877, by rfl⟩ : syracuseStep 1615673 = 1211755) B1211755
theorem B1615751 : Blo 1076618 1615751 := bstep (se 1 (by rfl) ⟨1211813, by rfl⟩ : syracuseStep 1615751 = 2423627) B2423627
theorem B5187473 : Blo 1076618 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B1615787 : Blo 1076618 1615787 := bstep (se 1 (by rfl) ⟨1211840, by rfl⟩ : syracuseStep 1615787 = 2423681) B2423681
theorem B1615817 : Blo 1076618 1615817 := bstep (se 2 (by rfl) ⟨605931, by rfl⟩ : syracuseStep 1615817 = 1211863) B1211863
theorem B1615931 : Blo 1076618 1615931 := bstep (se 1 (by rfl) ⟨1211948, by rfl⟩ : syracuseStep 1615931 = 2423897) B2423897
theorem B1615991 : Blo 1076618 1615991 := bstep (se 1 (by rfl) ⟨1211993, by rfl⟩ : syracuseStep 1615991 = 2423987) B2423987
theorem B1616015 : Blo 1076618 1616015 := bstep (se 1 (by rfl) ⟨1212011, by rfl⟩ : syracuseStep 1616015 = 2424023) B2424023
theorem B1616057 : Blo 1076618 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B1616135 : Blo 1076618 1616135 := bstep (se 1 (by rfl) ⟨1212101, by rfl⟩ : syracuseStep 1616135 = 2424203) B2424203
theorem B1616171 : Blo 1076618 1616171 := bstep (se 1 (by rfl) ⟨1212128, by rfl⟩ : syracuseStep 1616171 = 2424257) B2424257
theorem B1616201 : Blo 1076618 1616201 := bstep (se 2 (by rfl) ⟨606075, by rfl⟩ : syracuseStep 1616201 = 1212151) B1212151
theorem B4368755 : Blo 1076618 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B1616315 : Blo 1076618 1616315 := bstep (se 1 (by rfl) ⟨1212236, by rfl⟩ : syracuseStep 1616315 = 2424473) B2424473
theorem B1616375 : Blo 1076618 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B1616399 : Blo 1076618 1616399 := bstep (se 1 (by rfl) ⟨1212299, by rfl⟩ : syracuseStep 1616399 = 2424599) B2424599
theorem B1616441 : Blo 1076618 1616441 := bstep (se 2 (by rfl) ⟨606165, by rfl⟩ : syracuseStep 1616441 = 1212331) B1212331
theorem B12462659 : Blo 1076618 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B2730611 : Blo 1076618 2730611 := bstep (se 1 (by rfl) ⟨2047958, by rfl⟩ : syracuseStep 2730611 = 4095917) B4095917
theorem B1616519 : Blo 1076618 1616519 := bstep (se 1 (by rfl) ⟨1212389, by rfl⟩ : syracuseStep 1616519 = 2424779) B2424779
theorem B2730631 : Blo 1076618 2730631 := bstep (se 1 (by rfl) ⟨2047973, by rfl⟩ : syracuseStep 2730631 = 4095947) B4095947
theorem B1616555 : Blo 1076618 1616555 := bstep (se 1 (by rfl) ⟨1212416, by rfl⟩ : syracuseStep 1616555 = 2424833) B2424833
theorem B1616585 : Blo 1076618 1616585 := bstep (se 2 (by rfl) ⟨606219, by rfl⟩ : syracuseStep 1616585 = 1212439) B1212439
theorem B1616699 : Blo 1076618 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B1616759 : Blo 1076618 1616759 := bstep (se 1 (by rfl) ⟨1212569, by rfl⟩ : syracuseStep 1616759 = 2425139) B2425139
theorem B1616783 : Blo 1076618 1616783 := bstep (se 1 (by rfl) ⟨1212587, by rfl⟩ : syracuseStep 1616783 = 2425175) B2425175
theorem B2730905 : Blo 1076618 2730905 := bstep (se 2 (by rfl) ⟨1024089, by rfl⟩ : syracuseStep 2730905 = 2048179) B2048179
theorem B1616825 : Blo 1076618 1616825 := bstep (se 2 (by rfl) ⟨606309, by rfl⟩ : syracuseStep 1616825 = 1212619) B1212619
theorem B1616903 : Blo 1076618 1616903 := bstep (se 1 (by rfl) ⟨1212677, by rfl⟩ : syracuseStep 1616903 = 2425355) B2425355
theorem B1092623 : Blo 1076618 1092623 := bstep (se 1 (by rfl) ⟨819467, by rfl⟩ : syracuseStep 1092623 = 1638935) B1638935
theorem B9219095 : Blo 1076618 9219095 := bstep (se 1 (by rfl) ⟨6914321, by rfl⟩ : syracuseStep 9219095 = 13828643) B13828643
theorem B1616939 : Blo 1076618 1616939 := bstep (se 1 (by rfl) ⟨1212704, by rfl⟩ : syracuseStep 1616939 = 2425409) B2425409
theorem B2731067 : Blo 1076618 2731067 := bstep (se 1 (by rfl) ⟨2048300, by rfl⟩ : syracuseStep 2731067 = 4096601) B4096601
theorem B5450813 : Blo 1076618 5450813 := bstep (se 3 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 5450813 = 2044055) B2044055
theorem B4598851 : Blo 1076618 4598851 := bstep (se 1 (by rfl) ⟨3449138, by rfl⟩ : syracuseStep 4598851 = 6898277) B6898277
theorem B1616969 : Blo 1076618 1616969 := bstep (se 2 (by rfl) ⟨606363, by rfl⟩ : syracuseStep 1616969 = 1212727) B1212727
theorem B1617083 : Blo 1076618 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B1617143 : Blo 1076618 1617143 := bstep (se 1 (by rfl) ⟨1212857, by rfl⟩ : syracuseStep 1617143 = 2425715) B2425715
theorem B1617167 : Blo 1076618 1617167 := bstep (se 1 (by rfl) ⟨1212875, by rfl⟩ : syracuseStep 1617167 = 2425751) B2425751
theorem B2731279 : Blo 1076618 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B1617209 : Blo 1076618 1617209 := bstep (se 2 (by rfl) ⟨606453, by rfl⟩ : syracuseStep 1617209 = 1212907) B1212907
theorem B1617287 : Blo 1076618 1617287 := bstep (se 1 (by rfl) ⟨1212965, by rfl⟩ : syracuseStep 1617287 = 2425931) B2425931
theorem B4599193 : Blo 1076618 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B1617323 : Blo 1076618 1617323 := bstep (se 1 (by rfl) ⟨1212992, by rfl⟩ : syracuseStep 1617323 = 2425985) B2425985
theorem B1617353 : Blo 1076618 1617353 := bstep (se 2 (by rfl) ⟨606507, by rfl⟩ : syracuseStep 1617353 = 1213015) B1213015
theorem B2731553 : Blo 1076618 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B1420859 : Blo 1076618 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B1617467 : Blo 1076618 1617467 := bstep (se 1 (by rfl) ⟨1213100, by rfl⟩ : syracuseStep 1617467 = 2426201) B2426201
theorem B1617527 : Blo 1076618 1617527 := bstep (se 1 (by rfl) ⟨1213145, by rfl⟩ : syracuseStep 1617527 = 2426291) B2426291
theorem B6565495 : Blo 1076618 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B1617551 : Blo 1076618 1617551 := bstep (se 1 (by rfl) ⟨1213163, by rfl⟩ : syracuseStep 1617551 = 2426327) B2426327
theorem B1617593 : Blo 1076618 1617593 := bstep (se 2 (by rfl) ⟨606597, by rfl⟩ : syracuseStep 1617593 = 1213195) B1213195
theorem B1617671 : Blo 1076618 1617671 := bstep (se 1 (by rfl) ⟨1213253, by rfl⟩ : syracuseStep 1617671 = 2426507) B2426507
theorem B1617707 : Blo 1076618 1617707 := bstep (se 1 (by rfl) ⟨1213280, by rfl⟩ : syracuseStep 1617707 = 2426561) B2426561
theorem B1617737 : Blo 1076618 1617737 := bstep (se 2 (by rfl) ⟨606651, by rfl⟩ : syracuseStep 1617737 = 1213303) B1213303
theorem B1617851 : Blo 1076618 1617851 := bstep (se 1 (by rfl) ⟨1213388, by rfl⟩ : syracuseStep 1617851 = 2426777) B2426777
theorem B1617911 : Blo 1076618 1617911 := bstep (se 1 (by rfl) ⟨1213433, by rfl⟩ : syracuseStep 1617911 = 2426867) B2426867
theorem B1617935 : Blo 1076618 1617935 := bstep (se 1 (by rfl) ⟨1213451, by rfl⟩ : syracuseStep 1617935 = 2426903) B2426903
theorem B13840429 : Blo 1076618 13840429 := bstep (se 3 (by rfl) ⟨2595080, by rfl⟩ : syracuseStep 13840429 = 5190161) B5190161
theorem B1617977 : Blo 1076618 1617977 := bstep (se 2 (by rfl) ⟨606741, by rfl⟩ : syracuseStep 1617977 = 1213483) B1213483
theorem B1618055 : Blo 1076618 1618055 := bstep (se 1 (by rfl) ⟨1213541, by rfl⟩ : syracuseStep 1618055 = 2427083) B2427083
theorem B1618091 : Blo 1076618 1618091 := bstep (se 1 (by rfl) ⟨1213568, by rfl⟩ : syracuseStep 1618091 = 2427137) B2427137
theorem B1618121 : Blo 1076618 1618121 := bstep (se 2 (by rfl) ⟨606795, by rfl⟩ : syracuseStep 1618121 = 1213591) B1213591
theorem B1618235 : Blo 1076618 1618235 := bstep (se 1 (by rfl) ⟨1213676, by rfl⟩ : syracuseStep 1618235 = 2427353) B2427353
theorem B1618295 : Blo 1076618 1618295 := bstep (se 1 (by rfl) ⟨1213721, by rfl⟩ : syracuseStep 1618295 = 2427443) B2427443
theorem B4993415 : Blo 1076618 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B1618319 : Blo 1076618 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B1618361 : Blo 1076618 1618361 := bstep (se 2 (by rfl) ⟨606885, by rfl⟩ : syracuseStep 1618361 = 1213771) B1213771
theorem B1618439 : Blo 1076618 1618439 := bstep (se 1 (by rfl) ⟨1213829, by rfl⟩ : syracuseStep 1618439 = 2427659) B2427659
theorem B2732555 : Blo 1076618 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B1618475 : Blo 1076618 1618475 := bstep (se 1 (by rfl) ⟨1213856, by rfl⟩ : syracuseStep 1618475 = 2427713) B2427713
theorem B6566467 : Blo 1076618 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B1618505 : Blo 1076618 1618505 := bstep (se 2 (by rfl) ⟨606939, by rfl⟩ : syracuseStep 1618505 = 1213879) B1213879
theorem B5190317 : Blo 1076618 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B1618619 : Blo 1076618 1618619 := bstep (se 1 (by rfl) ⟨1213964, by rfl⟩ : syracuseStep 1618619 = 2427929) B2427929
theorem B5255873 : Blo 1076618 5255873 := bstep (se 2 (by rfl) ⟨1970952, by rfl⟩ : syracuseStep 5255873 = 3941905) B3941905
theorem B1618679 : Blo 1076618 1618679 := bstep (se 1 (by rfl) ⟨1214009, by rfl⟩ : syracuseStep 1618679 = 2428019) B2428019
theorem B1618703 : Blo 1076618 1618703 := bstep (se 1 (by rfl) ⟨1214027, by rfl⟩ : syracuseStep 1618703 = 2428055) B2428055
theorem B31535909 : Blo 1076618 31535909 := bstep (se 4 (by rfl) ⟨2956491, by rfl⟩ : syracuseStep 31535909 = 5912983) B5912983
theorem B5452595 : Blo 1076618 5452595 := bstep (se 1 (by rfl) ⟨4089446, by rfl⟩ : syracuseStep 5452595 = 8178893) B8178893
theorem B1618745 : Blo 1076618 1618745 := bstep (se 2 (by rfl) ⟨607029, by rfl⟩ : syracuseStep 1618745 = 1214059) B1214059
theorem B6140731 : Blo 1076618 6140731 := bstep (se 1 (by rfl) ⟨4605548, by rfl⟩ : syracuseStep 6140731 = 9211097) B9211097
theorem B2306875 : Blo 1076618 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B12301145 : Blo 1076618 12301145 := bstep (se 2 (by rfl) ⟨4612929, by rfl⟩ : syracuseStep 12301145 = 9225859) B9225859
theorem B1618823 : Blo 1076618 1618823 := bstep (se 1 (by rfl) ⟨1214117, by rfl⟩ : syracuseStep 1618823 = 2428235) B2428235
theorem B1618859 : Blo 1076618 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B1618889 : Blo 1076618 1618889 := bstep (se 2 (by rfl) ⟨607083, by rfl⟩ : syracuseStep 1618889 = 1214167) B1214167
theorem B1946657 : Blo 1076618 1946657 := bstep (se 2 (by rfl) ⟨729996, by rfl⟩ : syracuseStep 1946657 = 1459993) B1459993
theorem B1619003 : Blo 1076618 1619003 := bstep (se 1 (by rfl) ⟨1214252, by rfl⟩ : syracuseStep 1619003 = 2428505) B2428505
theorem B5452919 : Blo 1076618 5452919 := bstep (se 1 (by rfl) ⟨4089689, by rfl⟩ : syracuseStep 5452919 = 8179379) B8179379
theorem B1619063 : Blo 1076618 1619063 := bstep (se 1 (by rfl) ⟨1214297, by rfl⟩ : syracuseStep 1619063 = 2428595) B2428595
theorem B1619087 : Blo 1076618 1619087 := bstep (se 1 (by rfl) ⟨1214315, by rfl⟩ : syracuseStep 1619087 = 2428631) B2428631
theorem B2733203 : Blo 1076618 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B1619129 : Blo 1076618 1619129 := bstep (se 2 (by rfl) ⟨607173, by rfl⟩ : syracuseStep 1619129 = 1214347) B1214347
theorem B1619207 : Blo 1076618 1619207 := bstep (se 1 (by rfl) ⟨1214405, by rfl⟩ : syracuseStep 1619207 = 2428811) B2428811
theorem B1619243 : Blo 1076618 1619243 := bstep (se 1 (by rfl) ⟨1214432, by rfl⟩ : syracuseStep 1619243 = 2428865) B2428865
theorem B1619273 : Blo 1076618 1619273 := bstep (se 2 (by rfl) ⟨607227, by rfl⟩ : syracuseStep 1619273 = 1214455) B1214455
theorem B13120861 : Blo 1076618 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B3683731 : Blo 1076618 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B4928921 : Blo 1076618 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B21018041 : Blo 1076618 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B2733497 : Blo 1076618 2733497 := bstep (se 2 (by rfl) ⟨1025061, by rfl⟩ : syracuseStep 2733497 = 2050123) B2050123
theorem B1619387 : Blo 1076618 1619387 := bstep (se 1 (by rfl) ⟨1214540, by rfl⟩ : syracuseStep 1619387 = 2429081) B2429081
theorem B1619447 : Blo 1076618 1619447 := bstep (se 1 (by rfl) ⟨1214585, by rfl⟩ : syracuseStep 1619447 = 2429171) B2429171
theorem B1619471 : Blo 1076618 1619471 := bstep (se 1 (by rfl) ⟨1214603, by rfl⟩ : syracuseStep 1619471 = 2429207) B2429207
theorem B2045483 : Blo 1076618 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B1619513 : Blo 1076618 1619513 := bstep (se 2 (by rfl) ⟨607317, by rfl⟩ : syracuseStep 1619513 = 1214635) B1214635
theorem B1619591 : Blo 1076618 1619591 := bstep (se 1 (by rfl) ⟨1214693, by rfl⟩ : syracuseStep 1619591 = 2429387) B2429387
theorem B1619627 : Blo 1076618 1619627 := bstep (se 1 (by rfl) ⟨1214720, by rfl⟩ : syracuseStep 1619627 = 2429441) B2429441
theorem B1619657 : Blo 1076618 1619657 := bstep (se 2 (by rfl) ⟨607371, by rfl⟩ : syracuseStep 1619657 = 1214743) B1214743
theorem B2045711 : Blo 1076618 2045711 := bstep (se 1 (by rfl) ⟨1534283, by rfl⟩ : syracuseStep 2045711 = 3068567) B3068567
theorem B1619771 : Blo 1076618 1619771 := bstep (se 1 (by rfl) ⟨1214828, by rfl⟩ : syracuseStep 1619771 = 2429657) B2429657
theorem B1619831 : Blo 1076618 1619831 := bstep (se 1 (by rfl) ⟨1214873, by rfl⟩ : syracuseStep 1619831 = 2429747) B2429747
theorem B1619855 : Blo 1076618 1619855 := bstep (se 1 (by rfl) ⟨1214891, by rfl⟩ : syracuseStep 1619855 = 2429783) B2429783
theorem B1619897 : Blo 1076618 1619897 := bstep (se 2 (by rfl) ⟨607461, by rfl⟩ : syracuseStep 1619897 = 1214923) B1214923
theorem B1619975 : Blo 1076618 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B11089943 : Blo 1076618 11089943 := bstep (se 1 (by rfl) ⟨8317457, by rfl⟩ : syracuseStep 11089943 = 16634915) B16634915
theorem B1620011 : Blo 1076618 1620011 := bstep (se 1 (by rfl) ⟨1215008, by rfl⟩ : syracuseStep 1620011 = 2430017) B2430017
theorem B5453891 : Blo 1076618 5453891 := bstep (se 1 (by rfl) ⟨4090418, by rfl⟩ : syracuseStep 5453891 = 8180837) B8180837
theorem B1620041 : Blo 1076618 1620041 := bstep (se 2 (by rfl) ⟨607515, by rfl⟩ : syracuseStep 1620041 = 1215031) B1215031
theorem B2734195 : Blo 1076618 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B1620155 : Blo 1076618 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B6142189 : Blo 1076618 6142189 := bstep (se 3 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 6142189 = 2303321) B2303321
theorem B1620215 : Blo 1076618 1620215 := bstep (se 1 (by rfl) ⟨1215161, by rfl⟩ : syracuseStep 1620215 = 2430323) B2430323
theorem B2734337 : Blo 1076618 2734337 := bstep (se 2 (by rfl) ⟨1025376, by rfl⟩ : syracuseStep 2734337 = 2050753) B2050753
theorem B1620239 : Blo 1076618 1620239 := bstep (se 1 (by rfl) ⟨1215179, by rfl⟩ : syracuseStep 1620239 = 2430359) B2430359
theorem B1620281 : Blo 1076618 1620281 := bstep (se 2 (by rfl) ⟨607605, by rfl⟩ : syracuseStep 1620281 = 1215211) B1215211
theorem B1816951 : Blo 1076618 1816951 := bstep (se 1 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 1816951 = 2725427) B2725427
theorem B5454215 : Blo 1076618 5454215 := bstep (se 1 (by rfl) ⟨4090661, by rfl⟩ : syracuseStep 5454215 = 8181323) B8181323
theorem B1620359 : Blo 1076618 1620359 := bstep (se 1 (by rfl) ⟨1215269, by rfl⟩ : syracuseStep 1620359 = 2430539) B2430539
theorem B1620395 : Blo 1076618 1620395 := bstep (se 1 (by rfl) ⟨1215296, by rfl⟩ : syracuseStep 1620395 = 2430593) B2430593
theorem B1620425 : Blo 1076618 1620425 := bstep (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) B1215319
theorem B1817147 : Blo 1076618 1817147 := bstep (se 1 (by rfl) ⟨1362860, by rfl⟩ : syracuseStep 1817147 = 2725721) B2725721
theorem B1620539 : Blo 1076618 1620539 := bstep (se 1 (by rfl) ⟨1215404, by rfl⟩ : syracuseStep 1620539 = 2430809) B2430809
theorem B1620599 : Blo 1076618 1620599 := bstep (se 1 (by rfl) ⟨1215449, by rfl⟩ : syracuseStep 1620599 = 2430899) B2430899
theorem B1620623 : Blo 1076618 1620623 := bstep (se 1 (by rfl) ⟨1215467, by rfl⟩ : syracuseStep 1620623 = 2430935) B2430935
theorem B3324563 : Blo 1076618 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B1620665 : Blo 1076618 1620665 := bstep (se 2 (by rfl) ⟨607749, by rfl⟩ : syracuseStep 1620665 = 1215499) B1215499
theorem B2734793 : Blo 1076618 2734793 := bstep (se 2 (by rfl) ⟨1025547, by rfl⟩ : syracuseStep 2734793 = 2051095) B2051095
theorem B1620743 : Blo 1076618 1620743 := bstep (se 1 (by rfl) ⟨1215557, by rfl⟩ : syracuseStep 1620743 = 2431115) B2431115
theorem B1620779 : Blo 1076618 1620779 := bstep (se 1 (by rfl) ⟨1215584, by rfl⟩ : syracuseStep 1620779 = 2431169) B2431169
theorem B1620809 : Blo 1076618 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B1620923 : Blo 1076618 1620923 := bstep (se 1 (by rfl) ⟨1215692, by rfl⟩ : syracuseStep 1620923 = 2431385) B2431385
theorem B1817545 : Blo 1076618 1817545 := bstep (se 2 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 1817545 = 1363159) B1363159
theorem B2735147 : Blo 1076618 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B7781437 : Blo 1076618 7781437 := bstep (se 3 (by rfl) ⟨1459019, by rfl⟩ : syracuseStep 7781437 = 2918039) B2918039
theorem B4996183 : Blo 1076618 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B3161207 : Blo 1076618 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2047123 : Blo 1076618 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B2047351 : Blo 1076618 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B19676621 : Blo 1076618 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B1457723 : Blo 1076618 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B1818247 : Blo 1076618 1818247 := bstep (se 1 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 1818247 = 2727371) B2727371
theorem B6144173 : Blo 1076618 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B1818895 : Blo 1076618 1818895 := bstep (se 1 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 1818895 = 2728343) B2728343
theorem B1295119 : Blo 1076618 1295119 := bstep (se 1 (by rfl) ⟨971339, by rfl⟩ : syracuseStep 1295119 = 1942679) B1942679
theorem B1819435 : Blo 1076618 1819435 := bstep (se 1 (by rfl) ⟨1364576, by rfl⟩ : syracuseStep 1819435 = 2729153) B2729153
theorem B7783283 : Blo 1076618 7783283 := bstep (se 1 (by rfl) ⟨5837462, by rfl⟩ : syracuseStep 7783283 = 11674925) B11674925
theorem B2048915 : Blo 1076618 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B1819577 : Blo 1076618 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B2048969 : Blo 1076618 2048969 := bstep (se 2 (by rfl) ⟨768363, by rfl⟩ : syracuseStep 2048969 = 1536727) B1536727
theorem B2049067 : Blo 1076618 2049067 := bstep (se 1 (by rfl) ⟨1536800, by rfl⟩ : syracuseStep 2049067 = 3073601) B3073601
theorem B3884233 : Blo 1076618 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B2049295 : Blo 1076618 2049295 := bstep (se 1 (by rfl) ⟨1536971, by rfl⟩ : syracuseStep 2049295 = 3073943) B3073943
theorem B3884435 : Blo 1076618 3884435 := bstep (se 1 (by rfl) ⟨2913326, by rfl⟩ : syracuseStep 3884435 = 5826653) B5826653
theorem B1820279 : Blo 1076618 1820279 := bstep (se 1 (by rfl) ⟨1365209, by rfl⟩ : syracuseStep 1820279 = 2730419) B2730419
theorem B3688193 : Blo 1076618 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B7784207 : Blo 1076618 7784207 := bstep (se 1 (by rfl) ⟨5838155, by rfl⟩ : syracuseStep 7784207 = 11676311) B11676311
theorem B12273443 : Blo 1076618 12273443 := bstep (se 1 (by rfl) ⟨9205082, by rfl⟩ : syracuseStep 12273443 = 18410165) B18410165
theorem B5457779 : Blo 1076618 5457779 := bstep (se 1 (by rfl) ⟨4093334, by rfl⟩ : syracuseStep 5457779 = 8186669) B8186669
theorem B8308595 : Blo 1076618 8308595 := bstep (se 1 (by rfl) ⟨6231446, by rfl⟩ : syracuseStep 8308595 = 12462893) B12462893
theorem B3458969 : Blo 1076618 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B4376605 : Blo 1076618 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B1820731 : Blo 1076618 1820731 := bstep (se 1 (by rfl) ⟨1365548, by rfl⟩ : syracuseStep 1820731 = 2731097) B2731097
theorem B1558715 : Blo 1076618 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B1820873 : Blo 1076618 1820873 := bstep (se 2 (by rfl) ⟨682827, by rfl⟩ : syracuseStep 1820873 = 1365655) B1365655
theorem B4606267 : Blo 1076618 4606267 := bstep (se 1 (by rfl) ⟨3454700, by rfl⟩ : syracuseStep 4606267 = 6909401) B6909401
theorem B5458265 : Blo 1076618 5458265 := bstep (se 2 (by rfl) ⟨2046849, by rfl⟩ : syracuseStep 5458265 = 4093699) B4093699
theorem B3066265 : Blo 1076618 3066265 := bstep (se 2 (by rfl) ⟨1149849, by rfl⟩ : syracuseStep 3066265 = 2299699) B2299699
theorem B22432241 : Blo 1076618 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B6900227 : Blo 1076618 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B6146563 : Blo 1076618 6146563 := bstep (se 1 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 6146563 = 9219845) B9219845
theorem B3066653 : Blo 1076618 3066653 := bstep (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) B1149995
theorem B2050859 : Blo 1076618 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B3001175 : Blo 1076618 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B3459955 : Blo 1076618 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B1821575 : Blo 1076618 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B1363063 : Blo 1076618 1363063 := bstep (se 1 (by rfl) ⟨1022297, by rfl⟩ : syracuseStep 1363063 = 2044595) B2044595
theorem B46583099 : Blo 1076618 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B1363387 : Blo 1076618 1363387 := bstep (se 1 (by rfl) ⟨1022540, by rfl⟩ : syracuseStep 1363387 = 2045081) B2045081
theorem B1822223 : Blo 1076618 1822223 := bstep (se 1 (by rfl) ⟨1366667, by rfl⟩ : syracuseStep 1822223 = 2733335) B2733335
theorem B9227843 : Blo 1076618 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B5918465 : Blo 1076618 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B1822763 : Blo 1076618 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B7196987 : Blo 1076618 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B1364359 : Blo 1076618 1364359 := bstep (se 1 (by rfl) ⟨1023269, by rfl⟩ : syracuseStep 1364359 = 2046539) B2046539
theorem B5460371 : Blo 1076618 5460371 := bstep (se 1 (by rfl) ⟨4095278, by rfl⟩ : syracuseStep 5460371 = 8190557) B8190557
theorem B1823161 : Blo 1076618 1823161 := bstep (se 2 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 1823161 = 1367371) B1367371
theorem B1364779 : Blo 1076618 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B6148979 : Blo 1076618 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B10376099 : Blo 1076618 10376099 := bstep (se 1 (by rfl) ⟨7782074, by rfl⟩ : syracuseStep 10376099 = 15564149) B15564149
theorem B1365007 : Blo 1076618 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B3069227 : Blo 1076618 3069227 := bstep (se 1 (by rfl) ⟨2301920, by rfl⟩ : syracuseStep 3069227 = 4603841) B4603841
theorem B52450739 : Blo 1076618 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B34952633 : Blo 1076618 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B3888701 : Blo 1076618 3888701 := bstep (se 3 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 3888701 = 1458263) B1458263
theorem B11064899 : Blo 1076618 11064899 := bstep (se 1 (by rfl) ⟨8298674, by rfl⟩ : syracuseStep 11064899 = 16597349) B16597349
theorem B4380227 : Blo 1076618 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B1365751 : Blo 1076618 1365751 := bstep (se 1 (by rfl) ⟨1024313, by rfl⟩ : syracuseStep 1365751 = 2048627) B2048627
theorem B9230233 : Blo 1076618 9230233 := bstep (se 2 (by rfl) ⟨3461337, by rfl⟩ : syracuseStep 9230233 = 6922675) B6922675
theorem B1726409 : Blo 1076618 1726409 := bstep (se 2 (by rfl) ⟨647403, by rfl⟩ : syracuseStep 1726409 = 1294807) B1294807
theorem B1366075 : Blo 1076618 1366075 := bstep (se 1 (by rfl) ⟨1024556, by rfl⟩ : syracuseStep 1366075 = 2049113) B2049113
theorem B3987713 : Blo 1076618 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B6150437 : Blo 1076618 6150437 := bstep (se 4 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 6150437 = 1153207) B1153207
theorem B1366571 : Blo 1076618 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B3070867 : Blo 1076618 3070867 := bstep (se 1 (by rfl) ⟨2303150, by rfl⟩ : syracuseStep 3070867 = 4606301) B4606301
theorem B1367047 : Blo 1076618 1367047 := bstep (se 1 (by rfl) ⟨1025285, by rfl⟩ : syracuseStep 1367047 = 2050571) B2050571
theorem B6151211 : Blo 1076618 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B5463449 : Blo 1076618 5463449 := bstep (se 2 (by rfl) ⟨2048793, by rfl⟩ : syracuseStep 5463449 = 4097587) B4097587
theorem B1367543 : Blo 1076618 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B5529131 : Blo 1076618 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B5824315 : Blo 1076618 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B3497863 : Blo 1076618 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B6152669 : Blo 1076618 6152669 := bstep (se 3 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 6152669 = 2307251) B2307251
theorem B6644227 : Blo 1076618 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B3072599 : Blo 1076618 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B6906941 : Blo 1076618 6906941 := bstep (se 3 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 6906941 = 2590103) B2590103
theorem B1729721 : Blo 1076618 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B1533497 : Blo 1076618 1533497 := bstep (se 2 (by rfl) ⟨575061, by rfl⟩ : syracuseStep 1533497 = 1150123) B1150123
theorem B1533583 : Blo 1076618 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B1533611 : Blo 1076618 1533611 := bstep (se 1 (by rfl) ⟨1150208, by rfl⟩ : syracuseStep 1533611 = 2300417) B2300417
theorem B5826305 : Blo 1076618 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B10348337 : Blo 1076618 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B4614023 : Blo 1076618 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B5466041 : Blo 1076618 5466041 := bstep (se 2 (by rfl) ⟨2049765, by rfl⟩ : syracuseStep 5466041 = 4099531) B4099531
theorem B9824267 : Blo 1076618 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B2910343 : Blo 1076618 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B3074183 : Blo 1076618 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B4090297 : Blo 1076618 4090297 := bstep (se 2 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 4090297 = 3067723) B3067723
theorem B4155833 : Blo 1076618 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B3074831 : Blo 1076618 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B3894151 : Blo 1076618 3894151 := bstep (se 1 (by rfl) ⟨2920613, by rfl⟩ : syracuseStep 3894151 = 5841227) B5841227
theorem B6908939 : Blo 1076618 6908939 := bstep (se 1 (by rfl) ⟨5181704, by rfl⟩ : syracuseStep 6908939 = 10363409) B10363409
theorem B5467337 : Blo 1076618 5467337 := bstep (se 2 (by rfl) ⟨2050251, by rfl⟩ : syracuseStep 5467337 = 4100503) B4100503
theorem B1076623 : Blo 1076618 1076623 := bstep (se 1 (by rfl) ⟨807467, by rfl⟩ : syracuseStep 1076623 = 1614935) B1614935
theorem B1076667 : Blo 1076618 1076667 := bstep (se 1 (by rfl) ⟨807500, by rfl⟩ : syracuseStep 1076667 = 1615001) B1615001
theorem B1076743 : Blo 1076618 1076743 := bstep (se 1 (by rfl) ⟨807557, by rfl⟩ : syracuseStep 1076743 = 1615115) B1615115
theorem B1076751 : Blo 1076618 1076751 := bstep (se 1 (by rfl) ⟨807563, by rfl⟩ : syracuseStep 1076751 = 1615127) B1615127
theorem B1076795 : Blo 1076618 1076795 := bstep (se 1 (by rfl) ⟨807596, by rfl⟩ : syracuseStep 1076795 = 1615193) B1615193
theorem B1076871 : Blo 1076618 1076871 := bstep (se 1 (by rfl) ⟨807653, by rfl⟩ : syracuseStep 1076871 = 1615307) B1615307
theorem B1076879 : Blo 1076618 1076879 := bstep (se 1 (by rfl) ⟨807659, by rfl⟩ : syracuseStep 1076879 = 1615319) B1615319
theorem B13987505 : Blo 1076618 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B1076923 : Blo 1076618 1076923 := bstep (se 1 (by rfl) ⟨807692, by rfl⟩ : syracuseStep 1076923 = 1615385) B1615385
theorem B12283649 : Blo 1076618 12283649 := bstep (se 2 (by rfl) ⟨4606368, by rfl⟩ : syracuseStep 12283649 = 9212737) B9212737
theorem B1076999 : Blo 1076618 1076999 := bstep (se 1 (by rfl) ⟨807749, by rfl⟩ : syracuseStep 1076999 = 1615499) B1615499
theorem B1077007 : Blo 1076618 1077007 := bstep (se 1 (by rfl) ⟨807755, by rfl⟩ : syracuseStep 1077007 = 1615511) B1615511
theorem B1077051 : Blo 1076618 1077051 := bstep (se 1 (by rfl) ⟨807788, by rfl⟩ : syracuseStep 1077051 = 1615577) B1615577
theorem B1077127 : Blo 1076618 1077127 := bstep (se 1 (by rfl) ⟨807845, by rfl⟩ : syracuseStep 1077127 = 1615691) B1615691
theorem B1077135 : Blo 1076618 1077135 := bstep (se 1 (by rfl) ⟨807851, by rfl⟩ : syracuseStep 1077135 = 1615703) B1615703
theorem B1077179 : Blo 1076618 1077179 := bstep (se 1 (by rfl) ⟨807884, by rfl⟩ : syracuseStep 1077179 = 1615769) B1615769
theorem B1077255 : Blo 1076618 1077255 := bstep (se 1 (by rfl) ⟨807941, by rfl⟩ : syracuseStep 1077255 = 1615883) B1615883
theorem B1077263 : Blo 1076618 1077263 := bstep (se 1 (by rfl) ⟨807947, by rfl⟩ : syracuseStep 1077263 = 1615895) B1615895
theorem B1077307 : Blo 1076618 1077307 := bstep (se 1 (by rfl) ⟨807980, by rfl⟩ : syracuseStep 1077307 = 1615961) B1615961
theorem B2912375 : Blo 1076618 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B1077383 : Blo 1076618 1077383 := bstep (se 1 (by rfl) ⟨808037, by rfl⟩ : syracuseStep 1077383 = 1616075) B1616075
theorem B1077391 : Blo 1076618 1077391 := bstep (se 1 (by rfl) ⟨808043, by rfl⟩ : syracuseStep 1077391 = 1616087) B1616087
theorem B1077435 : Blo 1076618 1077435 := bstep (se 1 (by rfl) ⟨808076, by rfl⟩ : syracuseStep 1077435 = 1616153) B1616153
theorem B1077511 : Blo 1076618 1077511 := bstep (se 1 (by rfl) ⟨808133, by rfl⟩ : syracuseStep 1077511 = 1616267) B1616267
theorem B1077519 : Blo 1076618 1077519 := bstep (se 1 (by rfl) ⟨808139, by rfl⟩ : syracuseStep 1077519 = 1616279) B1616279
theorem B1077563 : Blo 1076618 1077563 := bstep (se 1 (by rfl) ⟨808172, by rfl⟩ : syracuseStep 1077563 = 1616345) B1616345
theorem B3076471 : Blo 1076618 3076471 := bstep (se 1 (by rfl) ⟨2307353, by rfl⟩ : syracuseStep 3076471 = 4614707) B4614707
theorem B1077639 : Blo 1076618 1077639 := bstep (se 1 (by rfl) ⟨808229, by rfl⟩ : syracuseStep 1077639 = 1616459) B1616459
theorem B1077647 : Blo 1076618 1077647 := bstep (se 1 (by rfl) ⟨808235, by rfl⟩ : syracuseStep 1077647 = 1616471) B1616471
theorem B1077691 : Blo 1076618 1077691 := bstep (se 1 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 1077691 = 1616537) B1616537
theorem B1077767 : Blo 1076618 1077767 := bstep (se 1 (by rfl) ⟨808325, by rfl⟩ : syracuseStep 1077767 = 1616651) B1616651
theorem B1077775 : Blo 1076618 1077775 := bstep (se 1 (by rfl) ⟨808331, by rfl⟩ : syracuseStep 1077775 = 1616663) B1616663
theorem B1536527 : Blo 1076618 1536527 := bstep (se 1 (by rfl) ⟨1152395, by rfl⟩ : syracuseStep 1536527 = 2304791) B2304791
theorem B1077819 : Blo 1076618 1077819 := bstep (se 1 (by rfl) ⟨808364, by rfl⟩ : syracuseStep 1077819 = 1616729) B1616729
theorem B13103693 : Blo 1076618 13103693 := bstep (se 3 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 13103693 = 4913885) B4913885
theorem B1077895 : Blo 1076618 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B1077903 : Blo 1076618 1077903 := bstep (se 1 (by rfl) ⟨808427, by rfl⟩ : syracuseStep 1077903 = 1616855) B1616855
theorem B1077947 : Blo 1076618 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B1078023 : Blo 1076618 1078023 := bstep (se 1 (by rfl) ⟨808517, by rfl⟩ : syracuseStep 1078023 = 1617035) B1617035
theorem B1078031 : Blo 1076618 1078031 := bstep (se 1 (by rfl) ⟨808523, by rfl⟩ : syracuseStep 1078031 = 1617047) B1617047
theorem B1078075 : Blo 1076618 1078075 := bstep (se 1 (by rfl) ⟨808556, by rfl⟩ : syracuseStep 1078075 = 1617113) B1617113
theorem B1078151 : Blo 1076618 1078151 := bstep (se 1 (by rfl) ⟨808613, by rfl⟩ : syracuseStep 1078151 = 1617227) B1617227
theorem B1078159 : Blo 1076618 1078159 := bstep (se 1 (by rfl) ⟨808619, by rfl⟩ : syracuseStep 1078159 = 1617239) B1617239
theorem B1078203 : Blo 1076618 1078203 := bstep (se 1 (by rfl) ⟨808652, by rfl⟩ : syracuseStep 1078203 = 1617305) B1617305
theorem B1078279 : Blo 1076618 1078279 := bstep (se 1 (by rfl) ⟨808709, by rfl⟩ : syracuseStep 1078279 = 1617419) B1617419
theorem B1078287 : Blo 1076618 1078287 := bstep (se 1 (by rfl) ⟨808715, by rfl⟩ : syracuseStep 1078287 = 1617431) B1617431
theorem B1078331 : Blo 1076618 1078331 := bstep (se 1 (by rfl) ⟨808748, by rfl⟩ : syracuseStep 1078331 = 1617497) B1617497
theorem B1078407 : Blo 1076618 1078407 := bstep (se 1 (by rfl) ⟨808805, by rfl⟩ : syracuseStep 1078407 = 1617611) B1617611
theorem B1078415 : Blo 1076618 1078415 := bstep (se 1 (by rfl) ⟨808811, by rfl⟩ : syracuseStep 1078415 = 1617623) B1617623
theorem B1078459 : Blo 1076618 1078459 := bstep (se 1 (by rfl) ⟨808844, by rfl⟩ : syracuseStep 1078459 = 1617689) B1617689
theorem B1078535 : Blo 1076618 1078535 := bstep (se 1 (by rfl) ⟨808901, by rfl⟩ : syracuseStep 1078535 = 1617803) B1617803
theorem B4093199 : Blo 1076618 4093199 := bstep (se 1 (by rfl) ⟨3069899, by rfl⟩ : syracuseStep 4093199 = 6139799) B6139799
theorem B1078543 : Blo 1076618 1078543 := bstep (se 1 (by rfl) ⟨808907, by rfl⟩ : syracuseStep 1078543 = 1617815) B1617815
theorem B1078587 : Blo 1076618 1078587 := bstep (se 1 (by rfl) ⟨808940, by rfl⟩ : syracuseStep 1078587 = 1617881) B1617881
theorem B2913671 : Blo 1076618 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B1078663 : Blo 1076618 1078663 := bstep (se 1 (by rfl) ⟨808997, by rfl⟩ : syracuseStep 1078663 = 1617995) B1617995
theorem B1078671 : Blo 1076618 1078671 := bstep (se 1 (by rfl) ⟨809003, by rfl⟩ : syracuseStep 1078671 = 1618007) B1618007
theorem B1078715 : Blo 1076618 1078715 := bstep (se 1 (by rfl) ⟨809036, by rfl⟩ : syracuseStep 1078715 = 1618073) B1618073
theorem B6223313 : Blo 1076618 6223313 := bstep (se 2 (by rfl) ⟨2333742, by rfl⟩ : syracuseStep 6223313 = 4667485) B4667485
theorem B1078791 : Blo 1076618 1078791 := bstep (se 1 (by rfl) ⟨809093, by rfl⟩ : syracuseStep 1078791 = 1618187) B1618187
theorem B2913803 : Blo 1076618 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B1078799 : Blo 1076618 1078799 := bstep (se 1 (by rfl) ⟨809099, by rfl⟩ : syracuseStep 1078799 = 1618199) B1618199
theorem B1078843 : Blo 1076618 1078843 := bstep (se 1 (by rfl) ⟨809132, by rfl⟩ : syracuseStep 1078843 = 1618265) B1618265
theorem B9205325 : Blo 1076618 9205325 := bstep (se 3 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 9205325 = 3451997) B3451997
theorem B1078919 : Blo 1076618 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B1078927 : Blo 1076618 1078927 := bstep (se 1 (by rfl) ⟨809195, by rfl⟩ : syracuseStep 1078927 = 1618391) B1618391
theorem B2422457 : Blo 1076618 2422457 := bstep (se 2 (by rfl) ⟨908421, by rfl⟩ : syracuseStep 2422457 = 1816843) B1816843
theorem B1078971 : Blo 1076618 1078971 := bstep (se 1 (by rfl) ⟨809228, by rfl⟩ : syracuseStep 1078971 = 1618457) B1618457
theorem B1079047 : Blo 1076618 1079047 := bstep (se 1 (by rfl) ⟨809285, by rfl⟩ : syracuseStep 1079047 = 1618571) B1618571
theorem B1079055 : Blo 1076618 1079055 := bstep (se 1 (by rfl) ⟨809291, by rfl⟩ : syracuseStep 1079055 = 1618583) B1618583
theorem B1079099 : Blo 1076618 1079099 := bstep (se 1 (by rfl) ⟨809324, by rfl⟩ : syracuseStep 1079099 = 1618649) B1618649
theorem B1079175 : Blo 1076618 1079175 := bstep (se 1 (by rfl) ⟨809381, by rfl⟩ : syracuseStep 1079175 = 1618763) B1618763
theorem B1079183 : Blo 1076618 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1079227 : Blo 1076618 1079227 := bstep (se 1 (by rfl) ⟨809420, by rfl⟩ : syracuseStep 1079227 = 1618841) B1618841
theorem B1079303 : Blo 1076618 1079303 := bstep (se 1 (by rfl) ⟨809477, by rfl⟩ : syracuseStep 1079303 = 1618955) B1618955
theorem B2422799 : Blo 1076618 2422799 := bstep (se 1 (by rfl) ⟨1817099, by rfl⟩ : syracuseStep 2422799 = 3634199) B3634199
theorem B1079311 : Blo 1076618 1079311 := bstep (se 1 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 1079311 = 1618967) B1618967
theorem B7010327 : Blo 1076618 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B37910551 : Blo 1076618 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B2422817 : Blo 1076618 2422817 := bstep (se 2 (by rfl) ⟨908556, by rfl⟩ : syracuseStep 2422817 = 1817113) B1817113
theorem B1079355 : Blo 1076618 1079355 := bstep (se 1 (by rfl) ⟨809516, by rfl⟩ : syracuseStep 1079355 = 1619033) B1619033
theorem B1079431 : Blo 1076618 1079431 := bstep (se 1 (by rfl) ⟨809573, by rfl⟩ : syracuseStep 1079431 = 1619147) B1619147
theorem B1079439 : Blo 1076618 1079439 := bstep (se 1 (by rfl) ⟨809579, by rfl⟩ : syracuseStep 1079439 = 1619159) B1619159
theorem B1079483 : Blo 1076618 1079483 := bstep (se 1 (by rfl) ⟨809612, by rfl⟩ : syracuseStep 1079483 = 1619225) B1619225
theorem B1079559 : Blo 1076618 1079559 := bstep (se 1 (by rfl) ⟨809669, by rfl⟩ : syracuseStep 1079559 = 1619339) B1619339
theorem B1079567 : Blo 1076618 1079567 := bstep (se 1 (by rfl) ⟨809675, by rfl⟩ : syracuseStep 1079567 = 1619351) B1619351
theorem B1079611 : Blo 1076618 1079611 := bstep (se 1 (by rfl) ⟨809708, by rfl⟩ : syracuseStep 1079611 = 1619417) B1619417
theorem B2423159 : Blo 1076618 2423159 := bstep (se 1 (by rfl) ⟨1817369, by rfl⟩ : syracuseStep 2423159 = 3634739) B3634739
theorem B1079687 : Blo 1076618 1079687 := bstep (se 1 (by rfl) ⟨809765, by rfl⟩ : syracuseStep 1079687 = 1619531) B1619531
theorem B1079695 : Blo 1076618 1079695 := bstep (se 1 (by rfl) ⟨809771, by rfl⟩ : syracuseStep 1079695 = 1619543) B1619543
theorem B3635603 : Blo 1076618 3635603 := bstep (se 1 (by rfl) ⟨2726702, by rfl⟩ : syracuseStep 3635603 = 5453405) B5453405
theorem B1079739 : Blo 1076618 1079739 := bstep (se 1 (by rfl) ⟨809804, by rfl⟩ : syracuseStep 1079739 = 1619609) B1619609
theorem B1079815 : Blo 1076618 1079815 := bstep (se 1 (by rfl) ⟨809861, by rfl⟩ : syracuseStep 1079815 = 1619723) B1619723
theorem B1079823 : Blo 1076618 1079823 := bstep (se 1 (by rfl) ⟨809867, by rfl⟩ : syracuseStep 1079823 = 1619735) B1619735
theorem B2423339 : Blo 1076618 2423339 := bstep (se 1 (by rfl) ⟨1817504, by rfl⟩ : syracuseStep 2423339 = 3635009) B3635009
theorem B1079867 : Blo 1076618 1079867 := bstep (se 1 (by rfl) ⟨809900, by rfl⟩ : syracuseStep 1079867 = 1619801) B1619801
theorem B12286565 : Blo 1076618 12286565 := bstep (se 4 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 12286565 = 2303731) B2303731
theorem B1079943 : Blo 1076618 1079943 := bstep (se 1 (by rfl) ⟨809957, by rfl⟩ : syracuseStep 1079943 = 1619915) B1619915
theorem B1079951 : Blo 1076618 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B1079995 : Blo 1076618 1079995 := bstep (se 1 (by rfl) ⟨809996, by rfl⟩ : syracuseStep 1079995 = 1619993) B1619993
theorem B1080071 : Blo 1076618 1080071 := bstep (se 1 (by rfl) ⟨810053, by rfl⟩ : syracuseStep 1080071 = 1620107) B1620107
theorem B1080079 : Blo 1076618 1080079 := bstep (se 1 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 1080079 = 1620119) B1620119
theorem B1080123 : Blo 1076618 1080123 := bstep (se 1 (by rfl) ⟨810092, by rfl⟩ : syracuseStep 1080123 = 1620185) B1620185
theorem B1080199 : Blo 1076618 1080199 := bstep (se 1 (by rfl) ⟨810149, by rfl⟩ : syracuseStep 1080199 = 1620299) B1620299
theorem B1080207 : Blo 1076618 1080207 := bstep (se 1 (by rfl) ⟨810155, by rfl⟩ : syracuseStep 1080207 = 1620311) B1620311
theorem B2423699 : Blo 1076618 2423699 := bstep (se 1 (by rfl) ⟨1817774, by rfl⟩ : syracuseStep 2423699 = 3635549) B3635549
theorem B1211323 : Blo 1076618 1211323 := bstep (se 1 (by rfl) ⟨908492, by rfl⟩ : syracuseStep 1211323 = 1816985) B1816985
theorem B1080251 : Blo 1076618 1080251 := bstep (se 1 (by rfl) ⟨810188, by rfl⟩ : syracuseStep 1080251 = 1620377) B1620377
theorem B2423753 : Blo 1076618 2423753 := bstep (se 2 (by rfl) ⟨908907, by rfl⟩ : syracuseStep 2423753 = 1817815) B1817815
theorem B1080327 : Blo 1076618 1080327 := bstep (se 1 (by rfl) ⟨810245, by rfl⟩ : syracuseStep 1080327 = 1620491) B1620491
theorem B1080335 : Blo 1076618 1080335 := bstep (se 1 (by rfl) ⟨810251, by rfl⟩ : syracuseStep 1080335 = 1620503) B1620503
theorem B2882603 : Blo 1076618 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B1080379 : Blo 1076618 1080379 := bstep (se 1 (by rfl) ⟨810284, by rfl⟩ : syracuseStep 1080379 = 1620569) B1620569
theorem B1080455 : Blo 1076618 1080455 := bstep (se 1 (by rfl) ⟨810341, by rfl⟩ : syracuseStep 1080455 = 1620683) B1620683
theorem B1080463 : Blo 1076618 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B1080507 : Blo 1076618 1080507 := bstep (se 1 (by rfl) ⟨810380, by rfl⟩ : syracuseStep 1080507 = 1620761) B1620761
theorem B1080583 : Blo 1076618 1080583 := bstep (se 1 (by rfl) ⟨810437, by rfl⟩ : syracuseStep 1080583 = 1620875) B1620875
theorem B1080591 : Blo 1076618 1080591 := bstep (se 1 (by rfl) ⟨810443, by rfl⟩ : syracuseStep 1080591 = 1620887) B1620887
theorem B3276119 : Blo 1076618 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B20741507 : Blo 1076618 20741507 := bstep (se 1 (by rfl) ⟨15556130, by rfl⟩ : syracuseStep 20741507 = 31112261) B31112261
theorem B1211791 : Blo 1076618 1211791 := bstep (se 1 (by rfl) ⟨908843, by rfl⟩ : syracuseStep 1211791 = 1817687) B1817687
theorem B2588105 : Blo 1076618 2588105 := bstep (se 2 (by rfl) ⟨970539, by rfl⟩ : syracuseStep 2588105 = 1941079) B1941079
theorem B7765469 : Blo 1076618 7765469 := bstep (se 3 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 7765469 = 2912051) B2912051
theorem B2588161 : Blo 1076618 2588161 := bstep (se 2 (by rfl) ⟨970560, by rfl⟩ : syracuseStep 2588161 = 1941121) B1941121
theorem B8289869 : Blo 1076618 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B2424455 : Blo 1076618 2424455 := bstep (se 1 (by rfl) ⟨1818341, by rfl⟩ : syracuseStep 2424455 = 3636683) B3636683
theorem B2588431 : Blo 1076618 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B3637007 : Blo 1076618 3637007 := bstep (se 1 (by rfl) ⟨2727755, by rfl⟩ : syracuseStep 3637007 = 5455511) B5455511
theorem B2424635 : Blo 1076618 2424635 := bstep (se 1 (by rfl) ⟨1818476, by rfl⟩ : syracuseStep 2424635 = 3636953) B3636953
theorem B1212295 : Blo 1076618 1212295 := bstep (se 1 (by rfl) ⟨909221, by rfl⟩ : syracuseStep 1212295 = 1818443) B1818443
theorem B2424761 : Blo 1076618 2424761 := bstep (se 2 (by rfl) ⟨909285, by rfl⟩ : syracuseStep 2424761 = 1818571) B1818571
theorem B8192015 : Blo 1076618 8192015 := bstep (se 1 (by rfl) ⟨6144011, by rfl⟩ : syracuseStep 8192015 = 12288023) B12288023
theorem B2424851 : Blo 1076618 2424851 := bstep (se 1 (by rfl) ⟨1818638, by rfl⟩ : syracuseStep 2424851 = 3637277) B3637277
theorem B4096115 : Blo 1076618 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B15532195 : Blo 1076618 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B2425193 : Blo 1076618 2425193 := bstep (se 2 (by rfl) ⟨909447, by rfl⟩ : syracuseStep 2425193 = 1818895) B1818895
theorem B3277199 : Blo 1076618 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B1213051 : Blo 1076618 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B3277675 : Blo 1076618 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B2589623 : Blo 1076618 2589623 := bstep (se 1 (by rfl) ⟨1942217, by rfl⟩ : syracuseStep 2589623 = 3884435) B3884435
theorem B2425787 : Blo 1076618 2425787 := bstep (se 1 (by rfl) ⟨1819340, by rfl⟩ : syracuseStep 2425787 = 3638681) B3638681
theorem B2425913 : Blo 1076618 2425913 := bstep (se 2 (by rfl) ⟨909717, by rfl⟩ : syracuseStep 2425913 = 1819435) B1819435
theorem B1213519 : Blo 1076618 1213519 := bstep (se 1 (by rfl) ⟨910139, by rfl⟩ : syracuseStep 1213519 = 1820279) B1820279
theorem B3638519 : Blo 1076618 3638519 := bstep (se 1 (by rfl) ⟨2728889, by rfl⟩ : syracuseStep 3638519 = 5457779) B5457779
theorem B5539063 : Blo 1076618 5539063 := bstep (se 1 (by rfl) ⟨4154297, by rfl⟩ : syracuseStep 5539063 = 8308595) B8308595
theorem B4097405 : Blo 1076618 4097405 := bstep (se 3 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 4097405 = 1536527) B1536527
theorem B2426255 : Blo 1076618 2426255 := bstep (se 1 (by rfl) ⟨1819691, by rfl⟩ : syracuseStep 2426255 = 3639383) B3639383
theorem B12289481 : Blo 1076618 12289481 := bstep (se 2 (by rfl) ⟨4608555, by rfl⟩ : syracuseStep 12289481 = 9217111) B9217111
theorem B15533531 : Blo 1076618 15533531 := bstep (se 1 (by rfl) ⟨11650148, by rfl⟩ : syracuseStep 15533531 = 23300297) B23300297
theorem B1213915 : Blo 1076618 1213915 := bstep (se 1 (by rfl) ⟨910436, by rfl⟩ : syracuseStep 1213915 = 1820873) B1820873
theorem B1639975 : Blo 1076618 1639975 := bstep (se 1 (by rfl) ⟨1229981, by rfl⟩ : syracuseStep 1639975 = 2459963) B2459963
theorem B3638843 : Blo 1076618 3638843 := bstep (se 1 (by rfl) ⟨2729132, by rfl⟩ : syracuseStep 3638843 = 5458265) B5458265
theorem B5178977 : Blo 1076618 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B14419603 : Blo 1076618 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B2426579 : Blo 1076618 2426579 := bstep (se 1 (by rfl) ⟨1819934, by rfl⟩ : syracuseStep 2426579 = 3639869) B3639869
theorem B3639113 : Blo 1076618 3639113 := bstep (se 2 (by rfl) ⟨1364667, by rfl⟩ : syracuseStep 3639113 = 2729335) B2729335
theorem B2000783 : Blo 1076618 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B1214383 : Blo 1076618 1214383 := bstep (se 1 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 1214383 = 1821575) B1821575
theorem B3278855 : Blo 1076618 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B1214815 : Blo 1076618 1214815 := bstep (se 1 (by rfl) ⟨911111, by rfl⟩ : syracuseStep 1214815 = 1822223) B1822223
theorem B2427515 : Blo 1076618 2427515 := bstep (se 1 (by rfl) ⟨1820636, by rfl⟩ : syracuseStep 2427515 = 3641273) B3641273
theorem B1215175 : Blo 1076618 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B5835473 : Blo 1076618 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B2427641 : Blo 1076618 2427641 := bstep (se 2 (by rfl) ⟨910365, by rfl⟩ : syracuseStep 2427641 = 1820731) B1820731
theorem B3640247 : Blo 1076618 3640247 := bstep (se 1 (by rfl) ⟨2730185, by rfl⟩ : syracuseStep 3640247 = 5460371) B5460371
theorem B2427911 : Blo 1076618 2427911 := bstep (se 1 (by rfl) ⟨1820933, by rfl⟩ : syracuseStep 2427911 = 3641867) B3641867
theorem B2427983 : Blo 1076618 2427983 := bstep (se 1 (by rfl) ⟨1820987, by rfl⟩ : syracuseStep 2427983 = 3641975) B3641975
theorem B4099319 : Blo 1076618 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B6917399 : Blo 1076618 6917399 := bstep (se 1 (by rfl) ⟨5188049, by rfl⟩ : syracuseStep 6917399 = 10376099) B10376099
theorem B8195417 : Blo 1076618 8195417 := bstep (se 2 (by rfl) ⟨3073281, by rfl⟩ : syracuseStep 8195417 = 6146563) B6146563
theorem B2428379 : Blo 1076618 2428379 := bstep (se 1 (by rfl) ⟨1821284, by rfl⟩ : syracuseStep 2428379 = 3642569) B3642569
theorem B3640841 : Blo 1076618 3640841 := bstep (se 2 (by rfl) ⟨1365315, by rfl⟩ : syracuseStep 3640841 = 2730631) B2730631
theorem B34967159 : Blo 1076618 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B23301755 : Blo 1076618 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B7769789 : Blo 1076618 7769789 := bstep (se 3 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 7769789 = 2913671) B2913671
theorem B2592467 : Blo 1076618 2592467 := bstep (se 1 (by rfl) ⟨1944350, by rfl⟩ : syracuseStep 2592467 = 3888701) B3888701
theorem B7376599 : Blo 1076618 7376599 := bstep (se 1 (by rfl) ⟨5532449, by rfl⟩ : syracuseStep 7376599 = 11064899) B11064899
theorem B2920151 : Blo 1076618 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B2428847 : Blo 1076618 2428847 := bstep (se 1 (by rfl) ⟨1821635, by rfl⟩ : syracuseStep 2428847 = 3643271) B3643271
theorem B1150939 : Blo 1076618 1150939 := bstep (se 1 (by rfl) ⟨863204, by rfl⟩ : syracuseStep 1150939 = 1726409) B1726409
theorem B6131801 : Blo 1076618 6131801 := bstep (se 2 (by rfl) ⟨2299425, by rfl⟩ : syracuseStep 6131801 = 4598851) B4598851
theorem B4919453 : Blo 1076618 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B2658475 : Blo 1076618 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B2429099 : Blo 1076618 2429099 := bstep (se 1 (by rfl) ⟨1821824, by rfl⟩ : syracuseStep 2429099 = 3643649) B3643649
theorem B4100291 : Blo 1076618 4100291 := bstep (se 1 (by rfl) ⟨3075218, by rfl⟩ : syracuseStep 4100291 = 6150437) B6150437
theorem B12980555 : Blo 1076618 12980555 := bstep (se 1 (by rfl) ⟨9735416, by rfl⟩ : syracuseStep 12980555 = 19470833) B19470833
theorem B3641705 : Blo 1076618 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B6132257 : Blo 1076618 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B9835181 : Blo 1076618 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B2429639 : Blo 1076618 2429639 := bstep (se 1 (by rfl) ⟨1822229, by rfl⟩ : syracuseStep 2429639 = 3644459) B3644459
theorem B4100807 : Blo 1076618 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B6132509 : Blo 1076618 6132509 := bstep (se 3 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 6132509 = 2299691) B2299691
theorem B27595565 : Blo 1076618 27595565 := bstep (se 3 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 27595565 = 10348337) B10348337
theorem B8753993 : Blo 1076618 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B3642299 : Blo 1076618 3642299 := bstep (se 1 (by rfl) ⟨2731724, by rfl⟩ : syracuseStep 3642299 = 5463449) B5463449
theorem B5248079 : Blo 1076618 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B5182667 : Blo 1076618 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B10360025 : Blo 1076618 10360025 := bstep (se 2 (by rfl) ⟨3885009, by rfl⟩ : syracuseStep 10360025 = 7770019) B7770019
theorem B18453905 : Blo 1076618 18453905 := bstep (se 2 (by rfl) ⟨6920214, by rfl⟩ : syracuseStep 18453905 = 13840429) B13840429
theorem B2430503 : Blo 1076618 2430503 := bstep (se 1 (by rfl) ⟨1822877, by rfl⟩ : syracuseStep 2430503 = 3645755) B3645755
theorem B4101779 : Blo 1076618 4101779 := bstep (se 1 (by rfl) ⟨3076334, by rfl⟩ : syracuseStep 4101779 = 6152669) B6152669
theorem B8197847 : Blo 1076618 8197847 := bstep (se 1 (by rfl) ⟨6148385, by rfl⟩ : syracuseStep 8197847 = 12296771) B12296771
theorem B4101961 : Blo 1076618 4101961 := bstep (se 2 (by rfl) ⟨1538235, by rfl⟩ : syracuseStep 4101961 = 3076471) B3076471
theorem B2430827 : Blo 1076618 2430827 := bstep (se 1 (by rfl) ⟨1823120, by rfl⟩ : syracuseStep 2430827 = 3646241) B3646241
theorem B2430881 : Blo 1076618 2430881 := bstep (se 2 (by rfl) ⟨911580, by rfl⟩ : syracuseStep 2430881 = 1823161) B1823161
theorem B15570893 : Blo 1076618 15570893 := bstep (se 3 (by rfl) ⟨2919542, by rfl⟩ : syracuseStep 15570893 = 5839085) B5839085
theorem B8755289 : Blo 1076618 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B2431223 : Blo 1076618 2431223 := bstep (se 1 (by rfl) ⟨1823417, by rfl⟩ : syracuseStep 2431223 = 3646835) B3646835
theorem B9836849 : Blo 1076618 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B11082221 : Blo 1076618 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B3644027 : Blo 1076618 3644027 := bstep (se 1 (by rfl) ⟨2733020, by rfl⟩ : syracuseStep 3644027 = 5466041) B5466041
theorem B3644189 : Blo 1076618 3644189 := bstep (se 3 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 3644189 = 1366571) B1366571
theorem B3644891 : Blo 1076618 3644891 := bstep (se 1 (by rfl) ⟨2733668, by rfl⟩ : syracuseStep 3644891 = 5467337) B5467337
theorem B1941583 : Blo 1076618 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B3645593 : Blo 1076618 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B8200763 : Blo 1076618 8200763 := bstep (se 1 (by rfl) ⟨6150572, by rfl⟩ : syracuseStep 8200763 = 12301145) B12301145
theorem B2728799 : Blo 1076618 2728799 := bstep (se 1 (by rfl) ⟨2046599, by rfl⟩ : syracuseStep 2728799 = 4093199) B4093199
theorem B3285947 : Blo 1076618 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B1942535 : Blo 1076618 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B6136883 : Blo 1076618 6136883 := bstep (se 1 (by rfl) ⟨4602662, by rfl⟩ : syracuseStep 6136883 = 9205325) B9205325
theorem B1614971 : Blo 1076618 1614971 := bstep (se 1 (by rfl) ⟨1211228, by rfl⟩ : syracuseStep 1614971 = 2422457) B2422457
theorem B1615097 : Blo 1076618 1615097 := bstep (se 2 (by rfl) ⟨605661, by rfl⟩ : syracuseStep 1615097 = 1211323) B1211323
theorem B3646781 : Blo 1076618 3646781 := bstep (se 3 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 3646781 = 1367543) B1367543
theorem B1615199 : Blo 1076618 1615199 := bstep (se 1 (by rfl) ⟨1211399, by rfl⟩ : syracuseStep 1615199 = 2422799) B2422799
theorem B1615211 : Blo 1076618 1615211 := bstep (se 1 (by rfl) ⟨1211408, by rfl⟩ : syracuseStep 1615211 = 2422817) B2422817
theorem B6661577 : Blo 1076618 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B2729497 : Blo 1076618 2729497 := bstep (se 2 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 2729497 = 2047123) B2047123
theorem B1615439 : Blo 1076618 1615439 := bstep (se 1 (by rfl) ⟨1211579, by rfl⟩ : syracuseStep 1615439 = 2423159) B2423159
theorem B1615559 : Blo 1076618 1615559 := bstep (se 1 (by rfl) ⟨1211669, by rfl⟩ : syracuseStep 1615559 = 2423339) B2423339
theorem B2729801 : Blo 1076618 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B1615721 : Blo 1076618 1615721 := bstep (se 2 (by rfl) ⟨605895, by rfl⟩ : syracuseStep 1615721 = 1211791) B1211791
theorem B1615799 : Blo 1076618 1615799 := bstep (se 1 (by rfl) ⟨1211849, by rfl⟩ : syracuseStep 1615799 = 2423699) B2423699
theorem B1615835 : Blo 1076618 1615835 := bstep (se 1 (by rfl) ⟨1211876, by rfl⟩ : syracuseStep 1615835 = 2423753) B2423753
theorem B3450881 : Blo 1076618 3450881 := bstep (se 2 (by rfl) ⟨1294080, by rfl⟩ : syracuseStep 3450881 = 2588161) B2588161
theorem B2107471 : Blo 1076618 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B13117747 : Blo 1076618 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B3451241 : Blo 1076618 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B1616303 : Blo 1076618 1616303 := bstep (se 1 (by rfl) ⟨1212227, by rfl⟩ : syracuseStep 1616303 = 2424455) B2424455
theorem B4663817 : Blo 1076618 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B1616393 : Blo 1076618 1616393 := bstep (se 2 (by rfl) ⟨606147, by rfl⟩ : syracuseStep 1616393 = 1212295) B1212295
theorem B1616423 : Blo 1076618 1616423 := bstep (se 1 (by rfl) ⟨1212317, by rfl⟩ : syracuseStep 1616423 = 2424635) B2424635
theorem B1616507 : Blo 1076618 1616507 := bstep (se 1 (by rfl) ⟨1212380, by rfl⟩ : syracuseStep 1616507 = 2424761) B2424761
theorem B1616633 : Blo 1076618 1616633 := bstep (se 2 (by rfl) ⟨606237, by rfl⟩ : syracuseStep 1616633 = 1212475) B1212475
theorem B1616735 : Blo 1076618 1616735 := bstep (se 1 (by rfl) ⟨1212551, by rfl⟩ : syracuseStep 1616735 = 2425103) B2425103
theorem B1616747 : Blo 1076618 1616747 := bstep (se 1 (by rfl) ⟨1212560, by rfl⟩ : syracuseStep 1616747 = 2425121) B2425121
theorem B2730935 : Blo 1076618 2730935 := bstep (se 1 (by rfl) ⟨2048201, by rfl⟩ : syracuseStep 2730935 = 4096403) B4096403
theorem B1616975 : Blo 1076618 1616975 := bstep (se 1 (by rfl) ⟨1212731, by rfl⟩ : syracuseStep 1616975 = 2425463) B2425463
theorem B1617095 : Blo 1076618 1617095 := bstep (se 1 (by rfl) ⟨1212821, by rfl⟩ : syracuseStep 1617095 = 2425643) B2425643
theorem B5188855 : Blo 1076618 5188855 := bstep (se 1 (by rfl) ⟨3891641, by rfl⟩ : syracuseStep 5188855 = 7783283) B7783283
theorem B8858969 : Blo 1076618 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B1617257 : Blo 1076618 1617257 := bstep (se 2 (by rfl) ⟨606471, by rfl⟩ : syracuseStep 1617257 = 1212943) B1212943
theorem B4369793 : Blo 1076618 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B1617335 : Blo 1076618 1617335 := bstep (se 1 (by rfl) ⟨1213001, by rfl⟩ : syracuseStep 1617335 = 2426003) B2426003
theorem B1617371 : Blo 1076618 1617371 := bstep (se 1 (by rfl) ⟨1213028, by rfl⟩ : syracuseStep 1617371 = 2426057) B2426057
theorem B5189471 : Blo 1076618 5189471 := bstep (se 1 (by rfl) ⟨3892103, by rfl⟩ : syracuseStep 5189471 = 7784207) B7784207
theorem B1617839 : Blo 1076618 1617839 := bstep (se 1 (by rfl) ⟨1213379, by rfl⟩ : syracuseStep 1617839 = 2426759) B2426759
theorem B2305979 : Blo 1076618 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B2732039 : Blo 1076618 2732039 := bstep (se 1 (by rfl) ⟨2049029, by rfl⟩ : syracuseStep 2732039 = 4098059) B4098059
theorem B1617929 : Blo 1076618 1617929 := bstep (se 2 (by rfl) ⟨606723, by rfl⟩ : syracuseStep 1617929 = 1213447) B1213447
theorem B1617959 : Blo 1076618 1617959 := bstep (se 1 (by rfl) ⟨1213469, by rfl⟩ : syracuseStep 1617959 = 2426939) B2426939
theorem B2732089 : Blo 1076618 2732089 := bstep (se 2 (by rfl) ⟨1024533, by rfl⟩ : syracuseStep 2732089 = 2049067) B2049067
theorem B1618043 : Blo 1076618 1618043 := bstep (se 1 (by rfl) ⟨1213532, by rfl⟩ : syracuseStep 1618043 = 2427065) B2427065
theorem B1618169 : Blo 1076618 1618169 := bstep (se 2 (by rfl) ⟨606813, by rfl⟩ : syracuseStep 1618169 = 1213627) B1213627
theorem B14954827 : Blo 1076618 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B4600151 : Blo 1076618 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B1618271 : Blo 1076618 1618271 := bstep (se 1 (by rfl) ⟨1213703, by rfl⟩ : syracuseStep 1618271 = 2427407) B2427407
theorem B2732393 : Blo 1076618 2732393 := bstep (se 2 (by rfl) ⟨1024647, by rfl⟩ : syracuseStep 2732393 = 2049295) B2049295
theorem B1618283 : Blo 1076618 1618283 := bstep (se 1 (by rfl) ⟨1213712, by rfl⟩ : syracuseStep 1618283 = 2427425) B2427425
theorem B1094087 : Blo 1076618 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B2044435 : Blo 1076618 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B1618511 : Blo 1076618 1618511 := bstep (se 1 (by rfl) ⟨1213883, by rfl⟩ : syracuseStep 1618511 = 2427767) B2427767
theorem B35041891 : Blo 1076618 35041891 := bstep (se 1 (by rfl) ⟨26281418, by rfl⟩ : syracuseStep 35041891 = 52562837) B52562837
theorem B16626293 : Blo 1076618 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B1618631 : Blo 1076618 1618631 := bstep (se 1 (by rfl) ⟨1213973, by rfl⟩ : syracuseStep 1618631 = 2427947) B2427947
theorem B2044777 : Blo 1076618 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B1618793 : Blo 1076618 1618793 := bstep (se 2 (by rfl) ⟨607047, by rfl⟩ : syracuseStep 1618793 = 1214095) B1214095
theorem B1618871 : Blo 1076618 1618871 := bstep (se 1 (by rfl) ⟨1214153, by rfl⟩ : syracuseStep 1618871 = 2428307) B2428307
theorem B1618907 : Blo 1076618 1618907 := bstep (se 1 (by rfl) ⟨1214180, by rfl⟩ : syracuseStep 1618907 = 2428361) B2428361
theorem B1619375 : Blo 1076618 1619375 := bstep (se 1 (by rfl) ⟨1214531, by rfl⟩ : syracuseStep 1619375 = 2429063) B2429063
theorem B3880457 : Blo 1076618 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B1619465 : Blo 1076618 1619465 := bstep (se 2 (by rfl) ⟨607299, by rfl⟩ : syracuseStep 1619465 = 1214599) B1214599
theorem B4797991 : Blo 1076618 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B1619495 : Blo 1076618 1619495 := bstep (se 1 (by rfl) ⟨1214621, by rfl⟩ : syracuseStep 1619495 = 2429243) B2429243
theorem B1619579 : Blo 1076618 1619579 := bstep (se 1 (by rfl) ⟨1214684, by rfl⟩ : syracuseStep 1619579 = 2429369) B2429369
theorem B3454663 : Blo 1076618 3454663 := bstep (se 1 (by rfl) ⟨2590997, by rfl⟩ : syracuseStep 3454663 = 5181995) B5181995
theorem B6141689 : Blo 1076618 6141689 := bstep (se 2 (by rfl) ⟨2303133, by rfl⟩ : syracuseStep 6141689 = 4606267) B4606267
theorem B1619705 : Blo 1076618 1619705 := bstep (se 2 (by rfl) ⟨607389, by rfl⟩ : syracuseStep 1619705 = 1214779) B1214779
theorem B1619807 : Blo 1076618 1619807 := bstep (se 1 (by rfl) ⟨1214855, by rfl⟩ : syracuseStep 1619807 = 2429711) B2429711
theorem B1619819 : Blo 1076618 1619819 := bstep (se 1 (by rfl) ⟨1214864, by rfl⟩ : syracuseStep 1619819 = 2429729) B2429729
theorem B5453729 : Blo 1076618 5453729 := bstep (se 2 (by rfl) ⟨2045148, by rfl⟩ : syracuseStep 5453729 = 4090297) B4090297
theorem B1620047 : Blo 1076618 1620047 := bstep (se 1 (by rfl) ⟨1215035, by rfl⟩ : syracuseStep 1620047 = 2430071) B2430071
theorem B2046151 : Blo 1076618 2046151 := bstep (se 1 (by rfl) ⟨1534613, by rfl⟩ : syracuseStep 2046151 = 3069227) B3069227
theorem B1620167 : Blo 1076618 1620167 := bstep (se 1 (by rfl) ⟨1215125, by rfl⟩ : syracuseStep 1620167 = 2430251) B2430251
theorem B1816823 : Blo 1076618 1816823 := bstep (se 1 (by rfl) ⟨1362617, by rfl⟩ : syracuseStep 1816823 = 2725235) B2725235
theorem B1620329 : Blo 1076618 1620329 := bstep (se 2 (by rfl) ⟨607623, by rfl⟩ : syracuseStep 1620329 = 1215247) B1215247
theorem B1620407 : Blo 1076618 1620407 := bstep (se 1 (by rfl) ⟨1215305, by rfl⟩ : syracuseStep 1620407 = 2430611) B2430611
theorem B1620443 : Blo 1076618 1620443 := bstep (se 1 (by rfl) ⟨1215332, by rfl⟩ : syracuseStep 1620443 = 2430665) B2430665
theorem B4372973 : Blo 1076618 4372973 := bstep (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) B1639865
theorem B5192201 : Blo 1076618 5192201 := bstep (se 2 (by rfl) ⟨1947075, by rfl⟩ : syracuseStep 5192201 = 3894151) B3894151
theorem B2734631 : Blo 1076618 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B1817167 : Blo 1076618 1817167 := bstep (se 1 (by rfl) ⟨1362875, by rfl⟩ : syracuseStep 1817167 = 2725751) B2725751
theorem B1817417 : Blo 1076618 1817417 := bstep (se 2 (by rfl) ⟨681531, by rfl⟩ : syracuseStep 1817417 = 1363063) B1363063
theorem B2734955 : Blo 1076618 2734955 := bstep (se 1 (by rfl) ⟨2051216, by rfl⟩ : syracuseStep 2734955 = 4102433) B4102433
theorem B3455905 : Blo 1076618 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B1620911 : Blo 1076618 1620911 := bstep (se 1 (by rfl) ⟨1215683, by rfl⟩ : syracuseStep 1620911 = 2431367) B2431367
theorem B6143147 : Blo 1076618 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B1817849 : Blo 1076618 1817849 := bstep (se 2 (by rfl) ⟨681693, by rfl⟩ : syracuseStep 1817849 = 1363387) B1363387
theorem B1818031 : Blo 1076618 1818031 := bstep (se 1 (by rfl) ⟨1363523, by rfl⟩ : syracuseStep 1818031 = 2727047) B2727047
theorem B1818119 : Blo 1076618 1818119 := bstep (se 1 (by rfl) ⟨1363589, by rfl⟩ : syracuseStep 1818119 = 2727179) B2727179
theorem B12304061 : Blo 1076618 12304061 := bstep (se 3 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 12304061 = 4614023) B4614023
theorem B3686087 : Blo 1076618 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B1818463 : Blo 1076618 1818463 := bstep (se 1 (by rfl) ⟨1363847, by rfl⟩ : syracuseStep 1818463 = 2727695) B2727695
theorem B1818551 : Blo 1076618 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B3457367 : Blo 1076618 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B8175977 : Blo 1076618 8175977 := bstep (se 2 (by rfl) ⟨3065991, by rfl⟩ : syracuseStep 8175977 = 6131983) B6131983
theorem B2048399 : Blo 1076618 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B1819145 : Blo 1076618 1819145 := bstep (se 2 (by rfl) ⟨682179, by rfl⟩ : syracuseStep 1819145 = 1364359) B1364359
theorem B1819307 : Blo 1076618 1819307 := bstep (se 1 (by rfl) ⟨1364480, by rfl⟩ : syracuseStep 1819307 = 2728961) B2728961
theorem B4604627 : Blo 1076618 4604627 := bstep (se 1 (by rfl) ⟨3453470, by rfl⟩ : syracuseStep 4604627 = 6906941) B6906941
theorem B11650013 : Blo 1076618 11650013 := bstep (se 3 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 11650013 = 4368755) B4368755
theorem B1819705 : Blo 1076618 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B3884203 : Blo 1076618 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B1819847 : Blo 1076618 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B3458315 : Blo 1076618 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B1820009 : Blo 1076618 1820009 := bstep (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) B1365007
theorem B2049455 : Blo 1076618 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B8308439 : Blo 1076618 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B1820407 : Blo 1076618 1820407 := bstep (se 1 (by rfl) ⟨1365305, by rfl⟩ : syracuseStep 1820407 = 2730611) B2730611
theorem B2049887 : Blo 1076618 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B1820603 : Blo 1076618 1820603 := bstep (se 1 (by rfl) ⟨1365452, by rfl⟩ : syracuseStep 1820603 = 2730905) B2730905
theorem B4605959 : Blo 1076618 4605959 := bstep (se 1 (by rfl) ⟨3454469, by rfl⟩ : syracuseStep 4605959 = 6908939) B6908939
theorem B6146063 : Blo 1076618 6146063 := bstep (se 1 (by rfl) ⟨4609547, by rfl⟩ : syracuseStep 6146063 = 9219095) B9219095
theorem B1820711 : Blo 1076618 1820711 := bstep (se 1 (by rfl) ⟨1365533, by rfl⟩ : syracuseStep 1820711 = 2731067) B2731067
theorem B7784525 : Blo 1076618 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B8177921 : Blo 1076618 8177921 := bstep (se 2 (by rfl) ⟨3066720, by rfl⟩ : syracuseStep 8177921 = 6133441) B6133441
theorem B1821001 : Blo 1076618 1821001 := bstep (se 2 (by rfl) ⟨682875, by rfl⟩ : syracuseStep 1821001 = 1365751) B1365751
theorem B1821035 : Blo 1076618 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B9325003 : Blo 1076618 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B12306977 : Blo 1076618 12306977 := bstep (se 2 (by rfl) ⟨4615116, by rfl⟩ : syracuseStep 12306977 = 9230233) B9230233
theorem B50547401 : Blo 1076618 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B1821433 : Blo 1076618 1821433 := bstep (se 2 (by rfl) ⟨683037, by rfl⟩ : syracuseStep 1821433 = 1366075) B1366075
theorem B3328943 : Blo 1076618 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B3460097 : Blo 1076618 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B1821703 : Blo 1076618 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B8735795 : Blo 1076618 8735795 := bstep (se 1 (by rfl) ⟨6551846, by rfl⟩ : syracuseStep 8735795 = 13103693) B13103693
theorem B3460211 : Blo 1076618 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B21023939 : Blo 1076618 21023939 := bstep (se 1 (by rfl) ⟨15767954, by rfl⟩ : syracuseStep 21023939 = 31535909) B31535909
theorem B1297771 : Blo 1076618 1297771 := bstep (se 1 (by rfl) ⟨973328, by rfl⟩ : syracuseStep 1297771 = 1946657) B1946657
theorem B1822135 : Blo 1076618 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B14012027 : Blo 1076618 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B1822331 : Blo 1076618 1822331 := bstep (se 1 (by rfl) ⟨1366748, by rfl⟩ : syracuseStep 1822331 = 2733497) B2733497
theorem B4148875 : Blo 1076618 4148875 := bstep (se 1 (by rfl) ⟨3111656, by rfl⟩ : syracuseStep 4148875 = 6223313) B6223313
theorem B1363655 : Blo 1076618 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B1363807 : Blo 1076618 1363807 := bstep (se 1 (by rfl) ⟨1022855, by rfl⟩ : syracuseStep 1363807 = 2045711) B2045711
theorem B1822729 : Blo 1076618 1822729 := bstep (se 2 (by rfl) ⟨683523, by rfl⟩ : syracuseStep 1822729 = 1367047) B1367047
theorem B4673551 : Blo 1076618 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B7393295 : Blo 1076618 7393295 := bstep (se 1 (by rfl) ⟨5544971, by rfl⟩ : syracuseStep 7393295 = 11089943) B11089943
theorem B10375249 : Blo 1076618 10375249 := bstep (se 2 (by rfl) ⟨3890718, by rfl⟩ : syracuseStep 10375249 = 7781437) B7781437
theorem B3788957 : Blo 1076618 3788957 := bstep (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) B1420859
theorem B3887261 : Blo 1076618 3887261 := bstep (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) B1457723
theorem B1822891 : Blo 1076618 1822891 := bstep (se 1 (by rfl) ⟨1367168, by rfl⟩ : syracuseStep 1822891 = 2734337) B2734337
theorem B22106317 : Blo 1076618 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B2216375 : Blo 1076618 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B1823195 : Blo 1076618 1823195 := bstep (se 1 (by rfl) ⟨1367396, by rfl⟩ : syracuseStep 1823195 = 2734793) B2734793
theorem B15782573 : Blo 1076618 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B1921735 : Blo 1076618 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B1823431 : Blo 1076618 1823431 := bstep (se 1 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 1823431 = 2735147) B2735147
theorem B2184079 : Blo 1076618 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B1725403 : Blo 1076618 1725403 := bstep (se 1 (by rfl) ⟨1294052, by rfl⟩ : syracuseStep 1725403 = 2588105) B2588105
theorem B1726031 : Blo 1076618 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B15554339 : Blo 1076618 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B7788473 : Blo 1076618 7788473 := bstep (se 2 (by rfl) ⟨2920677, by rfl⟩ : syracuseStep 7788473 = 5841355) B5841355
theorem B1365979 : Blo 1076618 1365979 := bstep (se 1 (by rfl) ⟨1024484, by rfl⟩ : syracuseStep 1365979 = 2048969) B2048969
theorem B12277817 : Blo 1076618 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B1726543 : Blo 1076618 1726543 := bstep (se 1 (by rfl) ⟨1294907, by rfl⟩ : syracuseStep 1726543 = 2589815) B2589815
theorem B5920883 : Blo 1076618 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B1726825 : Blo 1076618 1726825 := bstep (se 2 (by rfl) ⟨647559, by rfl⟩ : syracuseStep 1726825 = 1295119) B1295119
theorem B8182295 : Blo 1076618 8182295 := bstep (se 1 (by rfl) ⟨6136721, by rfl⟩ : syracuseStep 8182295 = 12273443) B12273443
theorem B69884491 : Blo 1076618 69884491 := bstep (se 1 (by rfl) ⟨52413368, by rfl⟩ : syracuseStep 69884491 = 104826737) B104826737
theorem B5463287 : Blo 1076618 5463287 := bstep (se 1 (by rfl) ⟨4097465, by rfl⟩ : syracuseStep 5463287 = 8194931) B8194931
theorem B31055399 : Blo 1076618 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B6217361 : Blo 1076618 6217361 := bstep (se 2 (by rfl) ⟨2331510, by rfl⟩ : syracuseStep 6217361 = 4663021) B4663021
theorem B6151895 : Blo 1076618 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B5463773 : Blo 1076618 5463773 := bstep (se 3 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 5463773 = 2048915) B2048915
theorem B2187103 : Blo 1076618 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B1728875 : Blo 1076618 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B4612589 : Blo 1076618 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B4088353 : Blo 1076618 4088353 := bstep (se 2 (by rfl) ⟨1533132, by rfl⟩ : syracuseStep 4088353 = 3066265) B3066265
theorem B4088839 : Blo 1076618 4088839 := bstep (se 1 (by rfl) ⟨3066629, by rfl⟩ : syracuseStep 4088839 = 6133259) B6133259
theorem B4613273 : Blo 1076618 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B4089325 : Blo 1076618 4089325 := bstep (se 3 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 4089325 = 1533497) B1533497
theorem B4155095 : Blo 1076618 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B4089629 : Blo 1076618 4089629 := bstep (se 3 (by rfl) ⟨766805, by rfl⟩ : syracuseStep 4089629 = 1533611) B1533611
theorem B8873921 : Blo 1076618 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B1730567 : Blo 1076618 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B7105283 : Blo 1076618 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B16608077 : Blo 1076618 16608077 := bstep (se 3 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 16608077 = 6228029) B6228029
theorem B1076655 : Blo 1076618 1076655 := bstep (se 1 (by rfl) ⟨807491, by rfl⟩ : syracuseStep 1076655 = 1614983) B1614983
theorem B1076679 : Blo 1076618 1076679 := bstep (se 1 (by rfl) ⟨807509, by rfl⟩ : syracuseStep 1076679 = 1615019) B1615019
theorem B1076699 : Blo 1076618 1076699 := bstep (se 1 (by rfl) ⟨807524, by rfl⟩ : syracuseStep 1076699 = 1615049) B1615049
theorem B3501593 : Blo 1076618 3501593 := bstep (se 2 (by rfl) ⟨1313097, by rfl⟩ : syracuseStep 3501593 = 2626195) B2626195
theorem B1076775 : Blo 1076618 1076775 := bstep (se 1 (by rfl) ⟨807581, by rfl⟩ : syracuseStep 1076775 = 1615163) B1615163
theorem B1076815 : Blo 1076618 1076815 := bstep (se 1 (by rfl) ⟨807611, by rfl⟩ : syracuseStep 1076815 = 1615223) B1615223
theorem B1076831 : Blo 1076618 1076831 := bstep (se 1 (by rfl) ⟨807623, by rfl⟩ : syracuseStep 1076831 = 1615247) B1615247
theorem B1076859 : Blo 1076618 1076859 := bstep (se 1 (by rfl) ⟨807644, by rfl⟩ : syracuseStep 1076859 = 1615289) B1615289
theorem B1076911 : Blo 1076618 1076911 := bstep (se 1 (by rfl) ⟨807683, by rfl⟩ : syracuseStep 1076911 = 1615367) B1615367
theorem B27979453 : Blo 1076618 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B1076935 : Blo 1076618 1076935 := bstep (se 1 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 1076935 = 1615403) B1615403
theorem B1076955 : Blo 1076618 1076955 := bstep (se 1 (by rfl) ⟨807716, by rfl⟩ : syracuseStep 1076955 = 1615433) B1615433
theorem B8187641 : Blo 1076618 8187641 := bstep (se 2 (by rfl) ⟨3070365, by rfl⟩ : syracuseStep 8187641 = 6140731) B6140731
theorem B3075833 : Blo 1076618 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B1077031 : Blo 1076618 1077031 := bstep (se 1 (by rfl) ⟨807773, by rfl⟩ : syracuseStep 1077031 = 1615547) B1615547
theorem B1077071 : Blo 1076618 1077071 := bstep (se 1 (by rfl) ⟨807803, by rfl⟩ : syracuseStep 1077071 = 1615607) B1615607
theorem B1077087 : Blo 1076618 1077087 := bstep (se 1 (by rfl) ⟨807815, by rfl⟩ : syracuseStep 1077087 = 1615631) B1615631
theorem B4091755 : Blo 1076618 4091755 := bstep (se 1 (by rfl) ⟨3068816, by rfl⟩ : syracuseStep 4091755 = 6137633) B6137633
theorem B1077115 : Blo 1076618 1077115 := bstep (se 1 (by rfl) ⟨807836, by rfl⟩ : syracuseStep 1077115 = 1615673) B1615673
theorem B1077167 : Blo 1076618 1077167 := bstep (se 1 (by rfl) ⟨807875, by rfl⟩ : syracuseStep 1077167 = 1615751) B1615751
theorem B1077191 : Blo 1076618 1077191 := bstep (se 1 (by rfl) ⟨807893, by rfl⟩ : syracuseStep 1077191 = 1615787) B1615787
theorem B1077211 : Blo 1076618 1077211 := bstep (se 1 (by rfl) ⟨807908, by rfl⟩ : syracuseStep 1077211 = 1615817) B1615817
theorem B6549511 : Blo 1076618 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B1077287 : Blo 1076618 1077287 := bstep (se 1 (by rfl) ⟨807965, by rfl⟩ : syracuseStep 1077287 = 1615931) B1615931
theorem B1077327 : Blo 1076618 1077327 := bstep (se 1 (by rfl) ⟨807995, by rfl⟩ : syracuseStep 1077327 = 1615991) B1615991
theorem B1077343 : Blo 1076618 1077343 := bstep (se 1 (by rfl) ⟨808007, by rfl⟩ : syracuseStep 1077343 = 1616015) B1616015
theorem B1077371 : Blo 1076618 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B1077423 : Blo 1076618 1077423 := bstep (se 1 (by rfl) ⟨808067, by rfl⟩ : syracuseStep 1077423 = 1616135) B1616135
theorem B1077447 : Blo 1076618 1077447 := bstep (se 1 (by rfl) ⟨808085, by rfl⟩ : syracuseStep 1077447 = 1616171) B1616171
theorem B1077467 : Blo 1076618 1077467 := bstep (se 1 (by rfl) ⟨808100, by rfl⟩ : syracuseStep 1077467 = 1616201) B1616201
theorem B1077543 : Blo 1076618 1077543 := bstep (se 1 (by rfl) ⟨808157, by rfl⟩ : syracuseStep 1077543 = 1616315) B1616315
theorem B1077583 : Blo 1076618 1077583 := bstep (se 1 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 1077583 = 1616375) B1616375
theorem B1077599 : Blo 1076618 1077599 := bstep (se 1 (by rfl) ⟨808199, by rfl⟩ : syracuseStep 1077599 = 1616399) B1616399
theorem B1077627 : Blo 1076618 1077627 := bstep (se 1 (by rfl) ⟨808220, by rfl⟩ : syracuseStep 1077627 = 1616441) B1616441
theorem B1077679 : Blo 1076618 1077679 := bstep (se 1 (by rfl) ⟨808259, by rfl⟩ : syracuseStep 1077679 = 1616519) B1616519
theorem B1077703 : Blo 1076618 1077703 := bstep (se 1 (by rfl) ⟨808277, by rfl⟩ : syracuseStep 1077703 = 1616555) B1616555
theorem B17494481 : Blo 1076618 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B1077723 : Blo 1076618 1077723 := bstep (se 1 (by rfl) ⟨808292, by rfl⟩ : syracuseStep 1077723 = 1616585) B1616585
theorem B4911641 : Blo 1076618 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B1077799 : Blo 1076618 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B1077839 : Blo 1076618 1077839 := bstep (se 1 (by rfl) ⟨808379, by rfl⟩ : syracuseStep 1077839 = 1616759) B1616759
theorem B1077855 : Blo 1076618 1077855 := bstep (se 1 (by rfl) ⟨808391, by rfl⟩ : syracuseStep 1077855 = 1616783) B1616783
theorem B1077883 : Blo 1076618 1077883 := bstep (se 1 (by rfl) ⟨808412, by rfl⟩ : syracuseStep 1077883 = 1616825) B1616825
theorem B1077935 : Blo 1076618 1077935 := bstep (se 1 (by rfl) ⟨808451, by rfl⟩ : syracuseStep 1077935 = 1616903) B1616903
theorem B1077959 : Blo 1076618 1077959 := bstep (se 1 (by rfl) ⟨808469, by rfl⟩ : syracuseStep 1077959 = 1616939) B1616939
theorem B3633875 : Blo 1076618 3633875 := bstep (se 1 (by rfl) ⟨2725406, by rfl⟩ : syracuseStep 3633875 = 5450813) B5450813
theorem B1077979 : Blo 1076618 1077979 := bstep (se 1 (by rfl) ⟨808484, by rfl⟩ : syracuseStep 1077979 = 1616969) B1616969
theorem B5468957 : Blo 1076618 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B1078055 : Blo 1076618 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B1078095 : Blo 1076618 1078095 := bstep (se 1 (by rfl) ⟨808571, by rfl⟩ : syracuseStep 1078095 = 1617143) B1617143
theorem B1078111 : Blo 1076618 1078111 := bstep (se 1 (by rfl) ⟨808583, by rfl⟩ : syracuseStep 1078111 = 1617167) B1617167
theorem B1078139 : Blo 1076618 1078139 := bstep (se 1 (by rfl) ⟨808604, by rfl⟩ : syracuseStep 1078139 = 1617209) B1617209
theorem B1078191 : Blo 1076618 1078191 := bstep (se 1 (by rfl) ⟨808643, by rfl⟩ : syracuseStep 1078191 = 1617287) B1617287
theorem B1078215 : Blo 1076618 1078215 := bstep (se 1 (by rfl) ⟨808661, by rfl⟩ : syracuseStep 1078215 = 1617323) B1617323
theorem B1078235 : Blo 1076618 1078235 := bstep (se 1 (by rfl) ⟨808676, by rfl⟩ : syracuseStep 1078235 = 1617353) B1617353
theorem B1078311 : Blo 1076618 1078311 := bstep (se 1 (by rfl) ⟨808733, by rfl⟩ : syracuseStep 1078311 = 1617467) B1617467
theorem B1078351 : Blo 1076618 1078351 := bstep (se 1 (by rfl) ⟨808763, by rfl⟩ : syracuseStep 1078351 = 1617527) B1617527
theorem B1078367 : Blo 1076618 1078367 := bstep (se 1 (by rfl) ⟨808775, by rfl⟩ : syracuseStep 1078367 = 1617551) B1617551
theorem B1078395 : Blo 1076618 1078395 := bstep (se 1 (by rfl) ⟨808796, by rfl⟩ : syracuseStep 1078395 = 1617593) B1617593
theorem B8189099 : Blo 1076618 8189099 := bstep (se 1 (by rfl) ⟨6141824, by rfl⟩ : syracuseStep 8189099 = 12283649) B12283649
theorem B1078447 : Blo 1076618 1078447 := bstep (se 1 (by rfl) ⟨808835, by rfl⟩ : syracuseStep 1078447 = 1617671) B1617671
theorem B1078471 : Blo 1076618 1078471 := bstep (se 1 (by rfl) ⟨808853, by rfl⟩ : syracuseStep 1078471 = 1617707) B1617707
theorem B1078491 : Blo 1076618 1078491 := bstep (se 1 (by rfl) ⟨808868, by rfl⟩ : syracuseStep 1078491 = 1617737) B1617737
theorem B1078567 : Blo 1076618 1078567 := bstep (se 1 (by rfl) ⟨808925, by rfl⟩ : syracuseStep 1078567 = 1617851) B1617851
theorem B1078607 : Blo 1076618 1078607 := bstep (se 1 (by rfl) ⟨808955, by rfl⟩ : syracuseStep 1078607 = 1617911) B1617911
theorem B1078623 : Blo 1076618 1078623 := bstep (se 1 (by rfl) ⟨808967, by rfl⟩ : syracuseStep 1078623 = 1617935) B1617935
theorem B1078651 : Blo 1076618 1078651 := bstep (se 1 (by rfl) ⟨808988, by rfl⟩ : syracuseStep 1078651 = 1617977) B1617977
theorem B2913661 : Blo 1076618 2913661 := bstep (se 3 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 2913661 = 1092623) B1092623
theorem B1078703 : Blo 1076618 1078703 := bstep (se 1 (by rfl) ⟨809027, by rfl⟩ : syracuseStep 1078703 = 1618055) B1618055
theorem B1078727 : Blo 1076618 1078727 := bstep (se 1 (by rfl) ⟨809045, by rfl⟩ : syracuseStep 1078727 = 1618091) B1618091
theorem B1078747 : Blo 1076618 1078747 := bstep (se 1 (by rfl) ⟨809060, by rfl⟩ : syracuseStep 1078747 = 1618121) B1618121
theorem B1078823 : Blo 1076618 1078823 := bstep (se 1 (by rfl) ⟨809117, by rfl⟩ : syracuseStep 1078823 = 1618235) B1618235
theorem B1078863 : Blo 1076618 1078863 := bstep (se 1 (by rfl) ⟨809147, by rfl⟩ : syracuseStep 1078863 = 1618295) B1618295
theorem B1078879 : Blo 1076618 1078879 := bstep (se 1 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 1078879 = 1618319) B1618319
theorem B1078907 : Blo 1076618 1078907 := bstep (se 1 (by rfl) ⟨809180, by rfl⟩ : syracuseStep 1078907 = 1618361) B1618361
theorem B8189585 : Blo 1076618 8189585 := bstep (se 2 (by rfl) ⟨3071094, by rfl⟩ : syracuseStep 8189585 = 6142189) B6142189
theorem B1078959 : Blo 1076618 1078959 := bstep (se 1 (by rfl) ⟨809219, by rfl⟩ : syracuseStep 1078959 = 1618439) B1618439
theorem B1078983 : Blo 1076618 1078983 := bstep (se 1 (by rfl) ⟨809237, by rfl⟩ : syracuseStep 1078983 = 1618475) B1618475
theorem B1079003 : Blo 1076618 1079003 := bstep (se 1 (by rfl) ⟨809252, by rfl⟩ : syracuseStep 1079003 = 1618505) B1618505
theorem B1079079 : Blo 1076618 1079079 := bstep (se 1 (by rfl) ⟨809309, by rfl⟩ : syracuseStep 1079079 = 1618619) B1618619
theorem B3503915 : Blo 1076618 3503915 := bstep (se 1 (by rfl) ⟨2627936, by rfl⟩ : syracuseStep 3503915 = 5255873) B5255873
theorem B2422601 : Blo 1076618 2422601 := bstep (se 2 (by rfl) ⟨908475, by rfl⟩ : syracuseStep 2422601 = 1816951) B1816951
theorem B1079119 : Blo 1076618 1079119 := bstep (se 1 (by rfl) ⟨809339, by rfl⟩ : syracuseStep 1079119 = 1618679) B1618679
theorem B1079135 : Blo 1076618 1079135 := bstep (se 1 (by rfl) ⟨809351, by rfl⟩ : syracuseStep 1079135 = 1618703) B1618703
theorem B3635063 : Blo 1076618 3635063 := bstep (se 1 (by rfl) ⟨2726297, by rfl⟩ : syracuseStep 3635063 = 5452595) B5452595
theorem B1079163 : Blo 1076618 1079163 := bstep (se 1 (by rfl) ⟨809372, by rfl⟩ : syracuseStep 1079163 = 1618745) B1618745
theorem B1079215 : Blo 1076618 1079215 := bstep (se 1 (by rfl) ⟨809411, by rfl⟩ : syracuseStep 1079215 = 1618823) B1618823
theorem B1079239 : Blo 1076618 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B1079259 : Blo 1076618 1079259 := bstep (se 1 (by rfl) ⟨809444, by rfl⟩ : syracuseStep 1079259 = 1618889) B1618889
theorem B1079335 : Blo 1076618 1079335 := bstep (se 1 (by rfl) ⟨809501, by rfl⟩ : syracuseStep 1079335 = 1619003) B1619003
theorem B3635279 : Blo 1076618 3635279 := bstep (se 1 (by rfl) ⟨2726459, by rfl⟩ : syracuseStep 3635279 = 5452919) B5452919
theorem B1079375 : Blo 1076618 1079375 := bstep (se 1 (by rfl) ⟨809531, by rfl⟩ : syracuseStep 1079375 = 1619063) B1619063
theorem B1079391 : Blo 1076618 1079391 := bstep (se 1 (by rfl) ⟨809543, by rfl⟩ : syracuseStep 1079391 = 1619087) B1619087
theorem B1079419 : Blo 1076618 1079419 := bstep (se 1 (by rfl) ⟨809564, by rfl⟩ : syracuseStep 1079419 = 1619129) B1619129
theorem B49739933 : Blo 1076618 49739933 := bstep (se 3 (by rfl) ⟨9326237, by rfl⟩ : syracuseStep 49739933 = 18652475) B18652475
theorem B1079471 : Blo 1076618 1079471 := bstep (se 1 (by rfl) ⟨809603, by rfl⟩ : syracuseStep 1079471 = 1619207) B1619207
theorem B1079495 : Blo 1076618 1079495 := bstep (se 1 (by rfl) ⟨809621, by rfl⟩ : syracuseStep 1079495 = 1619243) B1619243
theorem B1079515 : Blo 1076618 1079515 := bstep (se 1 (by rfl) ⟨809636, by rfl⟩ : syracuseStep 1079515 = 1619273) B1619273
theorem B1079591 : Blo 1076618 1079591 := bstep (se 1 (by rfl) ⟨809693, by rfl⟩ : syracuseStep 1079591 = 1619387) B1619387
theorem B1079631 : Blo 1076618 1079631 := bstep (se 1 (by rfl) ⟨809723, by rfl⟩ : syracuseStep 1079631 = 1619447) B1619447
theorem B1079647 : Blo 1076618 1079647 := bstep (se 1 (by rfl) ⟨809735, by rfl⟩ : syracuseStep 1079647 = 1619471) B1619471
theorem B1079675 : Blo 1076618 1079675 := bstep (se 1 (by rfl) ⟨809756, by rfl⟩ : syracuseStep 1079675 = 1619513) B1619513
theorem B1079727 : Blo 1076618 1079727 := bstep (se 1 (by rfl) ⟨809795, by rfl⟩ : syracuseStep 1079727 = 1619591) B1619591
theorem B1079751 : Blo 1076618 1079751 := bstep (se 1 (by rfl) ⟨809813, by rfl⟩ : syracuseStep 1079751 = 1619627) B1619627
theorem B3635657 : Blo 1076618 3635657 := bstep (se 2 (by rfl) ⟨1363371, by rfl⟩ : syracuseStep 3635657 = 2726743) B2726743
theorem B1079771 : Blo 1076618 1079771 := bstep (se 1 (by rfl) ⟨809828, by rfl⟩ : syracuseStep 1079771 = 1619657) B1619657
theorem B4094489 : Blo 1076618 4094489 := bstep (se 2 (by rfl) ⟨1535433, by rfl⟩ : syracuseStep 4094489 = 3070867) B3070867
theorem B1079847 : Blo 1076618 1079847 := bstep (se 1 (by rfl) ⟨809885, by rfl⟩ : syracuseStep 1079847 = 1619771) B1619771
theorem B1079887 : Blo 1076618 1079887 := bstep (se 1 (by rfl) ⟨809915, by rfl⟩ : syracuseStep 1079887 = 1619831) B1619831
theorem B1079903 : Blo 1076618 1079903 := bstep (se 1 (by rfl) ⟨809927, by rfl⟩ : syracuseStep 1079903 = 1619855) B1619855
theorem B2423393 : Blo 1076618 2423393 := bstep (se 2 (by rfl) ⟨908772, by rfl⟩ : syracuseStep 2423393 = 1817545) B1817545
theorem B1079931 : Blo 1076618 1079931 := bstep (se 1 (by rfl) ⟨809948, by rfl⟩ : syracuseStep 1079931 = 1619897) B1619897
theorem B1079983 : Blo 1076618 1079983 := bstep (se 1 (by rfl) ⟨809987, by rfl⟩ : syracuseStep 1079983 = 1619975) B1619975
theorem B1080007 : Blo 1076618 1080007 := bstep (se 1 (by rfl) ⟨810005, by rfl⟩ : syracuseStep 1080007 = 1620011) B1620011
theorem B3635927 : Blo 1076618 3635927 := bstep (se 1 (by rfl) ⟨2726945, by rfl⟩ : syracuseStep 3635927 = 5453891) B5453891
theorem B1080027 : Blo 1076618 1080027 := bstep (se 1 (by rfl) ⟨810020, by rfl⟩ : syracuseStep 1080027 = 1620041) B1620041
theorem B1080103 : Blo 1076618 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B1080143 : Blo 1076618 1080143 := bstep (se 1 (by rfl) ⟨810107, by rfl⟩ : syracuseStep 1080143 = 1620215) B1620215
theorem B1080159 : Blo 1076618 1080159 := bstep (se 1 (by rfl) ⟨810119, by rfl⟩ : syracuseStep 1080159 = 1620239) B1620239
theorem B1080187 : Blo 1076618 1080187 := bstep (se 1 (by rfl) ⟨810140, by rfl⟩ : syracuseStep 1080187 = 1620281) B1620281
theorem B3636143 : Blo 1076618 3636143 := bstep (se 1 (by rfl) ⟨2727107, by rfl⟩ : syracuseStep 3636143 = 5454215) B5454215
theorem B1080239 : Blo 1076618 1080239 := bstep (se 1 (by rfl) ⟨810179, by rfl⟩ : syracuseStep 1080239 = 1620359) B1620359
theorem B2423735 : Blo 1076618 2423735 := bstep (se 1 (by rfl) ⟨1817801, by rfl⟩ : syracuseStep 2423735 = 3635603) B3635603
theorem B1080263 : Blo 1076618 1080263 := bstep (se 1 (by rfl) ⟨810197, by rfl⟩ : syracuseStep 1080263 = 1620395) B1620395
theorem B1080283 : Blo 1076618 1080283 := bstep (se 1 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 1080283 = 1620425) B1620425
theorem B1211431 : Blo 1076618 1211431 := bstep (se 1 (by rfl) ⟨908573, by rfl⟩ : syracuseStep 1211431 = 1817147) B1817147
theorem B1080359 : Blo 1076618 1080359 := bstep (se 1 (by rfl) ⟨810269, by rfl⟩ : syracuseStep 1080359 = 1620539) B1620539
theorem B8191043 : Blo 1076618 8191043 := bstep (se 1 (by rfl) ⟨6143282, by rfl⟩ : syracuseStep 8191043 = 12286565) B12286565
theorem B1080399 : Blo 1076618 1080399 := bstep (se 1 (by rfl) ⟨810299, by rfl⟩ : syracuseStep 1080399 = 1620599) B1620599
theorem B1080415 : Blo 1076618 1080415 := bstep (se 1 (by rfl) ⟨810311, by rfl⟩ : syracuseStep 1080415 = 1620623) B1620623
theorem B1080443 : Blo 1076618 1080443 := bstep (se 1 (by rfl) ⟨810332, by rfl⟩ : syracuseStep 1080443 = 1620665) B1620665
theorem B1080495 : Blo 1076618 1080495 := bstep (se 1 (by rfl) ⟨810371, by rfl⟩ : syracuseStep 1080495 = 1620743) B1620743
theorem B1080519 : Blo 1076618 1080519 := bstep (se 1 (by rfl) ⟨810389, by rfl⟩ : syracuseStep 1080519 = 1620779) B1620779
theorem B1080539 : Blo 1076618 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B1080615 : Blo 1076618 1080615 := bstep (se 1 (by rfl) ⟨810461, by rfl⟩ : syracuseStep 1080615 = 1620923) B1620923
theorem B2424329 : Blo 1076618 2424329 := bstep (se 2 (by rfl) ⟨909123, by rfl⟩ : syracuseStep 2424329 = 1818247) B1818247
theorem B13827671 : Blo 1076618 13827671 := bstep (se 1 (by rfl) ⟨10370753, by rfl⟩ : syracuseStep 13827671 = 20741507) B20741507
theorem B5176979 : Blo 1076618 5176979 := bstep (se 1 (by rfl) ⟨3882734, by rfl⟩ : syracuseStep 5176979 = 7765469) B7765469
theorem B7765753 : Blo 1076618 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B2424671 : Blo 1076618 2424671 := bstep (se 1 (by rfl) ⟨1818503, by rfl⟩ : syracuseStep 2424671 = 3637007) B3637007
theorem B2588777 : Blo 1076618 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B20709593 : Blo 1076618 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B1212763 : Blo 1076618 1212763 := bstep (se 1 (by rfl) ⟨909572, by rfl⟩ : syracuseStep 1212763 = 1819145) B1819145
theorem B1212871 : Blo 1076618 1212871 := bstep (se 1 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 1212871 = 1819307) B1819307
theorem B7766675 : Blo 1076618 7766675 := bstep (se 1 (by rfl) ⟨5825006, by rfl⟩ : syracuseStep 7766675 = 11650013) B11650013
theorem B1213231 : Blo 1076618 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B2425679 : Blo 1076618 2425679 := bstep (se 1 (by rfl) ⟨1819259, by rfl⟩ : syracuseStep 2425679 = 3638519) B3638519
theorem B1213339 : Blo 1076618 1213339 := bstep (se 1 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 1213339 = 1820009) B1820009
theorem B8192987 : Blo 1076618 8192987 := bstep (se 1 (by rfl) ⟨6144740, by rfl⟩ : syracuseStep 8192987 = 12289481) B12289481
theorem B10355687 : Blo 1076618 10355687 := bstep (se 1 (by rfl) ⟨7766765, by rfl⟩ : syracuseStep 10355687 = 15533531) B15533531
theorem B2425895 : Blo 1076618 2425895 := bstep (se 1 (by rfl) ⟨1819421, by rfl⟩ : syracuseStep 2425895 = 3638843) B3638843
theorem B5538959 : Blo 1076618 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B2917565 : Blo 1076618 2917565 := bstep (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) B1094087
theorem B2426075 : Blo 1076618 2426075 := bstep (se 1 (by rfl) ⟨1819556, by rfl⟩ : syracuseStep 2426075 = 3639113) B3639113
theorem B1213735 : Blo 1076618 1213735 := bstep (se 1 (by rfl) ⟨910301, by rfl⟩ : syracuseStep 1213735 = 1820603) B1820603
theorem B4097375 : Blo 1076618 4097375 := bstep (se 1 (by rfl) ⟨3073031, by rfl⟩ : syracuseStep 4097375 = 6146063) B6146063
theorem B1213807 : Blo 1076618 1213807 := bstep (se 1 (by rfl) ⟨910355, by rfl⟩ : syracuseStep 1213807 = 1820711) B1820711
theorem B2426273 : Blo 1076618 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B5178937 : Blo 1076618 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B1214023 : Blo 1076618 1214023 := bstep (se 1 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 1214023 = 1821035) B1821035
theorem B2426831 : Blo 1076618 2426831 := bstep (se 1 (by rfl) ⟨1820123, by rfl⟩ : syracuseStep 2426831 = 3640247) B3640247
theorem B3639329 : Blo 1076618 3639329 := bstep (se 2 (by rfl) ⟨1364748, by rfl⟩ : syracuseStep 3639329 = 2729497) B2729497
theorem B2427209 : Blo 1076618 2427209 := bstep (se 2 (by rfl) ⟨910203, by rfl⟩ : syracuseStep 2427209 = 1820407) B1820407
theorem B2427227 : Blo 1076618 2427227 := bstep (se 1 (by rfl) ⟨1820420, by rfl⟩ : syracuseStep 2427227 = 3640841) B3640841
theorem B15534503 : Blo 1076618 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B9341351 : Blo 1076618 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B1214887 : Blo 1076618 1214887 := bstep (se 1 (by rfl) ⟨911165, by rfl⟩ : syracuseStep 1214887 = 1822331) B1822331
theorem B5179859 : Blo 1076618 5179859 := bstep (se 1 (by rfl) ⟨3884894, by rfl⟩ : syracuseStep 5179859 = 7769789) B7769789
theorem B2525971 : Blo 1076618 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B3279635 : Blo 1076618 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B2591507 : Blo 1076618 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B2427803 : Blo 1076618 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B1215463 : Blo 1076618 1215463 := bstep (se 1 (by rfl) ⟨911597, by rfl⟩ : syracuseStep 1215463 = 1823195) B1823195
theorem B2428001 : Blo 1076618 2428001 := bstep (se 2 (by rfl) ⟨910500, by rfl⟩ : syracuseStep 2428001 = 1821001) B1821001
theorem B6556787 : Blo 1076618 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B5835995 : Blo 1076618 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B2428199 : Blo 1076618 2428199 := bstep (se 1 (by rfl) ⟨1821149, by rfl⟩ : syracuseStep 2428199 = 3642299) B3642299
theorem B2428577 : Blo 1076618 2428577 := bstep (se 2 (by rfl) ⟨910716, by rfl⟩ : syracuseStep 2428577 = 1821433) B1821433
theorem B1150687 : Blo 1076618 1150687 := bstep (se 1 (by rfl) ⟨863015, by rfl⟩ : syracuseStep 1150687 = 1726031) B1726031
theorem B2428937 : Blo 1076618 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B5836859 : Blo 1076618 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B6918473 : Blo 1076618 6918473 := bstep (se 2 (by rfl) ⟨2594427, by rfl⟩ : syracuseStep 6918473 = 5188855) B5188855
theorem B2429351 : Blo 1076618 2429351 := bstep (se 1 (by rfl) ⟨1822013, by rfl⟩ : syracuseStep 2429351 = 3644027) B3644027
theorem B2429459 : Blo 1076618 2429459 := bstep (se 1 (by rfl) ⟨1822094, by rfl⟩ : syracuseStep 2429459 = 3644189) B3644189
theorem B11080253 : Blo 1076618 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B2429513 : Blo 1076618 2429513 := bstep (se 2 (by rfl) ⟨911067, by rfl⟩ : syracuseStep 2429513 = 1822135) B1822135
theorem B3642191 : Blo 1076618 3642191 := bstep (se 1 (by rfl) ⟨2731643, by rfl⟩ : syracuseStep 3642191 = 5463287) B5463287
theorem B2429927 : Blo 1076618 2429927 := bstep (se 1 (by rfl) ⟨1822445, by rfl⟩ : syracuseStep 2429927 = 3644891) B3644891
theorem B4101263 : Blo 1076618 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B3642515 : Blo 1076618 3642515 := bstep (se 1 (by rfl) ⟨2731886, by rfl⟩ : syracuseStep 3642515 = 5463773) B5463773
theorem B23663789 : Blo 1076618 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B2430305 : Blo 1076618 2430305 := bstep (se 2 (by rfl) ⟨911364, by rfl⟩ : syracuseStep 2430305 = 1822729) B1822729
theorem B6231401 : Blo 1076618 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B3642785 : Blo 1076618 3642785 := bstep (se 2 (by rfl) ⟨1366044, by rfl⟩ : syracuseStep 3642785 = 2732089) B2732089
theorem B2430395 : Blo 1076618 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B13833665 : Blo 1076618 13833665 := bstep (se 2 (by rfl) ⟨5187624, by rfl⟩ : syracuseStep 13833665 = 10375249) B10375249
theorem B3544633 : Blo 1076618 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B2430521 : Blo 1076618 2430521 := bstep (se 2 (by rfl) ⟨911445, by rfl⟩ : syracuseStep 2430521 = 1822891) B1822891
theorem B2725913 : Blo 1076618 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B2431187 : Blo 1076618 2431187 := bstep (se 1 (by rfl) ⟨1823390, by rfl⟩ : syracuseStep 2431187 = 3646781) B3646781
theorem B2431241 : Blo 1076618 2431241 := bstep (se 2 (by rfl) ⟨911715, by rfl⟩ : syracuseStep 2431241 = 1823431) B1823431
theorem B2726369 : Blo 1076618 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B2726419 : Blo 1076618 2726419 := bstep (se 1 (by rfl) ⟨2044814, by rfl⟩ : syracuseStep 2726419 = 4089629) B4089629
theorem B2300537 : Blo 1076618 2300537 := bstep (se 2 (by rfl) ⟨862701, by rfl⟩ : syracuseStep 2300537 = 1725403) B1725403
theorem B1153711 : Blo 1076618 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B2300827 : Blo 1076618 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B6921445 : Blo 1076618 6921445 := bstep (se 4 (by rfl) ⟨648885, by rfl⟩ : syracuseStep 6921445 = 1297771) B1297771
theorem B15539525 : Blo 1076618 15539525 := bstep (se 4 (by rfl) ⟨1456830, by rfl⟩ : syracuseStep 15539525 = 2913661) B2913661
theorem B6397321 : Blo 1076618 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B5905979 : Blo 1076618 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B2334395 : Blo 1076618 2334395 := bstep (se 1 (by rfl) ⟨1750796, by rfl⟩ : syracuseStep 2334395 = 3501593) B3501593
theorem B2302057 : Blo 1076618 2302057 := bstep (se 2 (by rfl) ⟨863271, by rfl⟩ : syracuseStep 2302057 = 1726543) B1726543
theorem B2728201 : Blo 1076618 2728201 := bstep (se 2 (by rfl) ⟨1023075, by rfl⟩ : syracuseStep 2728201 = 2046151) B2046151
theorem B11084195 : Blo 1076618 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B2302433 : Blo 1076618 2302433 := bstep (se 2 (by rfl) ⟨863412, by rfl⟩ : syracuseStep 2302433 = 1726825) B1726825
theorem B3645971 : Blo 1076618 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B2335943 : Blo 1076618 2335943 := bstep (se 1 (by rfl) ⟨1751957, by rfl⟩ : syracuseStep 2335943 = 3503915) B3503915
theorem B1615067 : Blo 1076618 1615067 := bstep (se 1 (by rfl) ⟨1211300, by rfl⟩ : syracuseStep 1615067 = 2422601) B2422601
theorem B1615241 : Blo 1076618 1615241 := bstep (se 2 (by rfl) ⟨605715, by rfl⟩ : syracuseStep 1615241 = 1211431) B1211431
theorem B2729659 : Blo 1076618 2729659 := bstep (se 1 (by rfl) ⟨2047244, by rfl⟩ : syracuseStep 2729659 = 4094489) B4094489
theorem B1615595 : Blo 1076618 1615595 := bstep (se 1 (by rfl) ⟨1211696, by rfl⟩ : syracuseStep 1615595 = 2423393) B2423393
theorem B1615823 : Blo 1076618 1615823 := bstep (se 1 (by rfl) ⟨1211867, by rfl⟩ : syracuseStep 1615823 = 2423735) B2423735
theorem B8202221 : Blo 1076618 8202221 := bstep (se 3 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 8202221 = 3075833) B3075833
theorem B1616219 : Blo 1076618 1616219 := bstep (se 1 (by rfl) ⟨1212164, by rfl⟩ : syracuseStep 1616219 = 2424329) B2424329
theorem B9218447 : Blo 1076618 9218447 := bstep (se 1 (by rfl) ⟨6913835, by rfl⟩ : syracuseStep 9218447 = 13827671) B13827671
theorem B3451319 : Blo 1076618 3451319 := bstep (se 1 (by rfl) ⟨2588489, by rfl⟩ : syracuseStep 3451319 = 5176979) B5176979
theorem B8202707 : Blo 1076618 8202707 := bstep (se 1 (by rfl) ⟨6152030, by rfl⟩ : syracuseStep 8202707 = 12304061) B12304061
theorem B6138341 : Blo 1076618 6138341 := bstep (se 4 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 6138341 = 1150939) B1150939
theorem B1616447 : Blo 1076618 1616447 := bstep (se 1 (by rfl) ⟨1212335, by rfl⟩ : syracuseStep 1616447 = 2424671) B2424671
theorem B1616567 : Blo 1076618 1616567 := bstep (se 1 (by rfl) ⟨1212425, by rfl⟩ : syracuseStep 1616567 = 2424851) B2424851
theorem B2730743 : Blo 1076618 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B2304911 : Blo 1076618 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B5450651 : Blo 1076618 5450651 := bstep (se 1 (by rfl) ⟨4087988, by rfl⟩ : syracuseStep 5450651 = 8175977) B8175977
theorem B1616795 : Blo 1076618 1616795 := bstep (se 1 (by rfl) ⟨1212596, by rfl⟩ : syracuseStep 1616795 = 2425193) B2425193
theorem B1617191 : Blo 1076618 1617191 := bstep (se 1 (by rfl) ⟨1212893, by rfl⟩ : syracuseStep 1617191 = 2425787) B2425787
theorem B1617275 : Blo 1076618 1617275 := bstep (se 1 (by rfl) ⟨1212956, by rfl⟩ : syracuseStep 1617275 = 2425913) B2425913
theorem B5451137 : Blo 1076618 5451137 := bstep (se 2 (by rfl) ⟨2044176, by rfl⟩ : syracuseStep 5451137 = 4088353) B4088353
theorem B1617401 : Blo 1076618 1617401 := bstep (se 2 (by rfl) ⟨606525, by rfl⟩ : syracuseStep 1617401 = 1213051) B1213051
theorem B2305543 : Blo 1076618 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B2731603 : Blo 1076618 2731603 := bstep (se 1 (by rfl) ⟨2048702, by rfl⟩ : syracuseStep 2731603 = 4097405) B4097405
theorem B1617503 : Blo 1076618 1617503 := bstep (se 1 (by rfl) ⟨1213127, by rfl⟩ : syracuseStep 1617503 = 2426255) B2426255
theorem B3452651 : Blo 1076618 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B1617719 : Blo 1076618 1617719 := bstep (se 1 (by rfl) ⟨1213289, by rfl⟩ : syracuseStep 1617719 = 2426579) B2426579
theorem B5451785 : Blo 1076618 5451785 := bstep (se 2 (by rfl) ⟨2044419, by rfl⟩ : syracuseStep 5451785 = 4088839) B4088839
theorem B5189683 : Blo 1076618 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B1618025 : Blo 1076618 1618025 := bstep (se 2 (by rfl) ⟨606759, by rfl⟩ : syracuseStep 1618025 = 1213519) B1213519
theorem B5451947 : Blo 1076618 5451947 := bstep (se 1 (by rfl) ⟨4088960, by rfl⟩ : syracuseStep 5451947 = 8177921) B8177921
theorem B7385417 : Blo 1076618 7385417 := bstep (se 2 (by rfl) ⟨2769531, by rfl⟩ : syracuseStep 7385417 = 5539063) B5539063
theorem B8204651 : Blo 1076618 8204651 := bstep (se 1 (by rfl) ⟨6153488, by rfl⟩ : syracuseStep 8204651 = 12306977) B12306977
theorem B1618343 : Blo 1076618 1618343 := bstep (se 1 (by rfl) ⟨1213757, by rfl⟩ : syracuseStep 1618343 = 2427515) B2427515
theorem B42086861 : Blo 1076618 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B33698267 : Blo 1076618 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B1618427 : Blo 1076618 1618427 := bstep (se 1 (by rfl) ⟨1213820, by rfl⟩ : syracuseStep 1618427 = 2427641) B2427641
theorem B1618553 : Blo 1076618 1618553 := bstep (se 2 (by rfl) ⟨606957, by rfl⟩ : syracuseStep 1618553 = 1213915) B1213915
theorem B5452433 : Blo 1076618 5452433 := bstep (se 2 (by rfl) ⟨2044662, by rfl⟩ : syracuseStep 5452433 = 4089325) B4089325
theorem B2306731 : Blo 1076618 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B1618607 : Blo 1076618 1618607 := bstep (se 1 (by rfl) ⟨1213955, by rfl⟩ : syracuseStep 1618607 = 2427911) B2427911
theorem B1618655 : Blo 1076618 1618655 := bstep (se 1 (by rfl) ⟨1213991, by rfl⟩ : syracuseStep 1618655 = 2427983) B2427983
theorem B2306807 : Blo 1076618 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B2732879 : Blo 1076618 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B1618919 : Blo 1076618 1618919 := bstep (se 1 (by rfl) ⟨1214189, by rfl⟩ : syracuseStep 1618919 = 2428379) B2428379
theorem B23311439 : Blo 1076618 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B1946767 : Blo 1076618 1946767 := bstep (se 1 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 1946767 = 2920151) B2920151
theorem B8762525 : Blo 1076618 8762525 := bstep (se 3 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 8762525 = 3285947) B3285947
theorem B1619177 : Blo 1076618 1619177 := bstep (se 2 (by rfl) ⟨607191, by rfl⟩ : syracuseStep 1619177 = 1214383) B1214383
theorem B1619231 : Blo 1076618 1619231 := bstep (se 1 (by rfl) ⟨1214423, by rfl⟩ : syracuseStep 1619231 = 2428847) B2428847
theorem B4928863 : Blo 1076618 4928863 := bstep (se 1 (by rfl) ⟨3696647, by rfl⟩ : syracuseStep 4928863 = 7393295) B7393295
theorem B1619399 : Blo 1076618 1619399 := bstep (se 1 (by rfl) ⟨1214549, by rfl⟩ : syracuseStep 1619399 = 2429099) B2429099
theorem B2733527 : Blo 1076618 2733527 := bstep (se 1 (by rfl) ⟨2050145, by rfl⟩ : syracuseStep 2733527 = 4100291) B4100291
theorem B1619753 : Blo 1076618 1619753 := bstep (se 2 (by rfl) ⟨607407, by rfl⟩ : syracuseStep 1619753 = 1214815) B1214815
theorem B1619759 : Blo 1076618 1619759 := bstep (se 1 (by rfl) ⟨1214819, by rfl⟩ : syracuseStep 1619759 = 2429639) B2429639
theorem B2733871 : Blo 1076618 2733871 := bstep (se 1 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 2733871 = 4100807) B4100807
theorem B18397043 : Blo 1076618 18397043 := bstep (se 1 (by rfl) ⟨13797782, by rfl⟩ : syracuseStep 18397043 = 27595565) B27595565
theorem B12433337 : Blo 1076618 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B138459253 : Blo 1076618 138459253 := bstep (se 5 (by rfl) ⟨6490277, by rfl⟩ : syracuseStep 138459253 = 12980555) B12980555
theorem B3455111 : Blo 1076618 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B1620233 : Blo 1076618 1620233 := bstep (se 2 (by rfl) ⟨607587, by rfl⟩ : syracuseStep 1620233 = 1215175) B1215175
theorem B12302603 : Blo 1076618 12302603 := bstep (se 1 (by rfl) ⟨9226952, by rfl⟩ : syracuseStep 12302603 = 18453905) B18453905
theorem B1620335 : Blo 1076618 1620335 := bstep (se 1 (by rfl) ⟨1215251, by rfl⟩ : syracuseStep 1620335 = 2430503) B2430503
theorem B2734519 : Blo 1076618 2734519 := bstep (se 1 (by rfl) ⟨2050889, by rfl⟩ : syracuseStep 2734519 = 4101779) B4101779
theorem B10369559 : Blo 1076618 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B1620551 : Blo 1076618 1620551 := bstep (se 1 (by rfl) ⟨1215413, by rfl⟩ : syracuseStep 1620551 = 2430827) B2430827
theorem B1620587 : Blo 1076618 1620587 := bstep (se 1 (by rfl) ⟨1215440, by rfl⟩ : syracuseStep 1620587 = 2430881) B2430881
theorem B5192315 : Blo 1076618 5192315 := bstep (se 1 (by rfl) ⟨3894236, by rfl⟩ : syracuseStep 5192315 = 7788473) B7788473
theorem B3947255 : Blo 1076618 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B1620815 : Blo 1076618 1620815 := bstep (se 1 (by rfl) ⟨1215611, by rfl⟩ : syracuseStep 1620815 = 2431223) B2431223
theorem B7388147 : Blo 1076618 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B5454863 : Blo 1076618 5454863 := bstep (se 1 (by rfl) ⟨4091147, by rfl⟩ : syracuseStep 5454863 = 8182295) B8182295
theorem B17480933 : Blo 1076618 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B37305937 : Blo 1076618 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B4144907 : Blo 1076618 4144907 := bstep (se 1 (by rfl) ⟨3108680, by rfl⟩ : syracuseStep 4144907 = 6217361) B6217361
theorem B1818409 : Blo 1076618 1818409 := bstep (se 2 (by rfl) ⟨681903, by rfl⟩ : syracuseStep 1818409 = 1363807) B1363807
theorem B5455673 : Blo 1076618 5455673 := bstep (se 2 (by rfl) ⟨2045877, by rfl⟩ : syracuseStep 5455673 = 4091755) B4091755
theorem B8732681 : Blo 1076618 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B29475089 : Blo 1076618 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B19939769 : Blo 1076618 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B1819199 : Blo 1076618 1819199 := bstep (se 1 (by rfl) ⟨1364399, by rfl⟩ : syracuseStep 1819199 = 2728799) B2728799
theorem B1295023 : Blo 1076618 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B26231597 : Blo 1076618 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B4441051 : Blo 1076618 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B1819867 : Blo 1076618 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B4736855 : Blo 1076618 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B1820623 : Blo 1076618 1820623 := bstep (se 1 (by rfl) ⟨1365467, by rfl⟩ : syracuseStep 1820623 = 2730935) B2730935
theorem B4606217 : Blo 1076618 4606217 := bstep (se 2 (by rfl) ⟨1727331, by rfl⟩ : syracuseStep 4606217 = 3454663) B3454663
theorem B5458427 : Blo 1076618 5458427 := bstep (se 1 (by rfl) ⟨4093820, by rfl⟩ : syracuseStep 5458427 = 8187641) B8187641
theorem B3459647 : Blo 1076618 3459647 := bstep (se 1 (by rfl) ⟨2594735, by rfl⟩ : syracuseStep 3459647 = 5189471) B5189471
theorem B1821305 : Blo 1076618 1821305 := bstep (se 2 (by rfl) ⟨682989, by rfl⟩ : syracuseStep 1821305 = 1365979) B1365979
theorem B1821359 : Blo 1076618 1821359 := bstep (se 1 (by rfl) ⟨1366019, by rfl⟩ : syracuseStep 1821359 = 2732039) B2732039
theorem B3066767 : Blo 1076618 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B1821595 : Blo 1076618 1821595 := bstep (se 1 (by rfl) ⟨1366196, by rfl⟩ : syracuseStep 1821595 = 2732393) B2732393
theorem B93179321 : Blo 1076618 93179321 := bstep (se 2 (by rfl) ⟨34942245, by rfl⟩ : syracuseStep 93179321 = 69884491) B69884491
theorem B5459399 : Blo 1076618 5459399 := bstep (se 1 (by rfl) ⟨4094549, by rfl⟩ : syracuseStep 5459399 = 8189099) B8189099
theorem B11652781 : Blo 1076618 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B5459723 : Blo 1076618 5459723 := bstep (se 1 (by rfl) ⟨4094792, by rfl⟩ : syracuseStep 5459723 = 8189585) B8189585
theorem B39341861 : Blo 1076618 39341861 := bstep (se 4 (by rfl) ⟨3688299, by rfl⟩ : syracuseStep 39341861 = 7376599) B7376599
theorem B4607873 : Blo 1076618 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B3461467 : Blo 1076618 3461467 := bstep (se 1 (by rfl) ⟨2596100, by rfl⟩ : syracuseStep 3461467 = 5192201) B5192201
theorem B1823087 : Blo 1076618 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B35508725 : Blo 1076618 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B1823303 : Blo 1076618 1823303 := bstep (se 1 (by rfl) ⟨1367477, by rfl⟩ : syracuseStep 1823303 = 2734955) B2734955
theorem B5460695 : Blo 1076618 5460695 := bstep (se 1 (by rfl) ⟨4095521, by rfl⟩ : syracuseStep 5460695 = 8191043) B8191043
theorem B5461343 : Blo 1076618 5461343 := bstep (se 1 (by rfl) ⟨4096007, by rfl⟩ : syracuseStep 5461343 = 8192015) B8192015
theorem B1365599 : Blo 1076618 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B3069751 : Blo 1076618 3069751 := bstep (se 1 (by rfl) ⟨2302313, by rfl⟩ : syracuseStep 3069751 = 4604627) B4604627
theorem B1726415 : Blo 1076618 1726415 := bstep (se 1 (by rfl) ⟨1294811, by rfl⟩ : syracuseStep 1726415 = 2589623) B2589623
theorem B4610333 : Blo 1076618 4610333 := bstep (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) B1728875
theorem B1366303 : Blo 1076618 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B8739197 : Blo 1076618 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B2185903 : Blo 1076618 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B3070639 : Blo 1076618 3070639 := bstep (se 1 (by rfl) ⟨2302979, by rfl⟩ : syracuseStep 3070639 = 4605959) B4605959
theorem B3890315 : Blo 1076618 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B5823863 : Blo 1076618 5823863 := bstep (se 1 (by rfl) ⟨4367897, by rfl⟩ : syracuseStep 5823863 = 8735795) B8735795
theorem B2186633 : Blo 1076618 2186633 := bstep (se 2 (by rfl) ⟨819987, by rfl⟩ : syracuseStep 2186633 = 1639975) B1639975
theorem B14015959 : Blo 1076618 14015959 := bstep (se 1 (by rfl) ⟨10511969, by rfl⟩ : syracuseStep 14015959 = 21023939) B21023939
theorem B4611599 : Blo 1076618 4611599 := bstep (se 1 (by rfl) ⟨3458699, by rfl⟩ : syracuseStep 4611599 = 6917399) B6917399
theorem B5463611 : Blo 1076618 5463611 := bstep (se 1 (by rfl) ⟨4097708, by rfl⟩ : syracuseStep 5463611 = 8195417) B8195417
theorem B1728311 : Blo 1076618 1728311 := bstep (se 1 (by rfl) ⟨1296233, by rfl⟩ : syracuseStep 1728311 = 2592467) B2592467
theorem B4087867 : Blo 1076618 4087867 := bstep (se 1 (by rfl) ⟨3065900, by rfl⟩ : syracuseStep 4087867 = 6131801) B6131801
theorem B2809961 : Blo 1076618 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B4088171 : Blo 1076618 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B17490329 : Blo 1076618 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B4088339 : Blo 1076618 4088339 := bstep (se 1 (by rfl) ⟨3066254, by rfl⟩ : syracuseStep 4088339 = 6132509) B6132509
theorem B3498719 : Blo 1076618 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B6906683 : Blo 1076618 6906683 := bstep (se 1 (by rfl) ⟨5180012, by rfl⟩ : syracuseStep 6906683 = 10360025) B10360025
theorem B10249253 : Blo 1076618 10249253 := bstep (se 4 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 10249253 = 1921735) B1921735
theorem B5465231 : Blo 1076618 5465231 := bstep (se 1 (by rfl) ⟨4098923, by rfl⟩ : syracuseStep 5465231 = 8197847) B8197847
theorem B10380595 : Blo 1076618 10380595 := bstep (se 1 (by rfl) ⟨7785446, by rfl⟩ : syracuseStep 10380595 = 15570893) B15570893
theorem B8185211 : Blo 1076618 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B5531833 : Blo 1076618 5531833 := bstep (se 2 (by rfl) ⟨2074437, by rfl⟩ : syracuseStep 5531833 = 4148875) B4148875
theorem B5466365 : Blo 1076618 5466365 := bstep (se 3 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 5466365 = 2049887) B2049887
theorem B20703599 : Blo 1076618 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B5335421 : Blo 1076618 5335421 := bstep (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) B2000783
theorem B9202349 : Blo 1076618 9202349 := bstep (se 3 (by rfl) ⟨1725440, by rfl⟩ : syracuseStep 9202349 = 3450881) B3450881
theorem B3075059 : Blo 1076618 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B5467175 : Blo 1076618 5467175 := bstep (se 1 (by rfl) ⟨4100381, by rfl⟩ : syracuseStep 5467175 = 8200763) B8200763
theorem B4091255 : Blo 1076618 4091255 := bstep (se 1 (by rfl) ⟨3068441, by rfl⟩ : syracuseStep 4091255 = 6136883) B6136883
theorem B1076647 : Blo 1076618 1076647 := bstep (se 1 (by rfl) ⟨807485, by rfl⟩ : syracuseStep 1076647 = 1614971) B1614971
theorem B3075515 : Blo 1076618 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B46722521 : Blo 1076618 46722521 := bstep (se 2 (by rfl) ⟨17520945, by rfl⟩ : syracuseStep 46722521 = 35041891) B35041891
theorem B1076731 : Blo 1076618 1076731 := bstep (se 1 (by rfl) ⟨807548, by rfl⟩ : syracuseStep 1076731 = 1615097) B1615097
theorem B1076799 : Blo 1076618 1076799 := bstep (se 1 (by rfl) ⟨807599, by rfl⟩ : syracuseStep 1076799 = 1615199) B1615199
theorem B1076807 : Blo 1076618 1076807 := bstep (se 1 (by rfl) ⟨807605, by rfl⟩ : syracuseStep 1076807 = 1615211) B1615211
theorem B1076959 : Blo 1076618 1076959 := bstep (se 1 (by rfl) ⟨807719, by rfl⟩ : syracuseStep 1076959 = 1615439) B1615439
theorem B1077039 : Blo 1076618 1077039 := bstep (se 1 (by rfl) ⟨807779, by rfl⟩ : syracuseStep 1077039 = 1615559) B1615559
theorem B2912105 : Blo 1076618 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B1077147 : Blo 1076618 1077147 := bstep (se 1 (by rfl) ⟨807860, by rfl⟩ : syracuseStep 1077147 = 1615721) B1615721
theorem B1077199 : Blo 1076618 1077199 := bstep (se 1 (by rfl) ⟨807899, by rfl⟩ : syracuseStep 1077199 = 1615799) B1615799
theorem B1077223 : Blo 1076618 1077223 := bstep (se 1 (by rfl) ⟨807917, by rfl⟩ : syracuseStep 1077223 = 1615835) B1615835
theorem B1077535 : Blo 1076618 1077535 := bstep (se 1 (by rfl) ⟨808151, by rfl⟩ : syracuseStep 1077535 = 1616303) B1616303
theorem B3109211 : Blo 1076618 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B1077595 : Blo 1076618 1077595 := bstep (se 1 (by rfl) ⟨808196, by rfl⟩ : syracuseStep 1077595 = 1616393) B1616393
theorem B1077615 : Blo 1076618 1077615 := bstep (se 1 (by rfl) ⟨808211, by rfl⟩ : syracuseStep 1077615 = 1616423) B1616423
theorem B1077671 : Blo 1076618 1077671 := bstep (se 1 (by rfl) ⟨808253, by rfl⟩ : syracuseStep 1077671 = 1616507) B1616507
theorem B1077755 : Blo 1076618 1077755 := bstep (se 1 (by rfl) ⟨808316, by rfl⟩ : syracuseStep 1077755 = 1616633) B1616633
theorem B11072051 : Blo 1076618 11072051 := bstep (se 1 (by rfl) ⟨8304038, by rfl⟩ : syracuseStep 11072051 = 16608077) B16608077
theorem B1077823 : Blo 1076618 1077823 := bstep (se 1 (by rfl) ⟨808367, by rfl⟩ : syracuseStep 1077823 = 1616735) B1616735
theorem B1077831 : Blo 1076618 1077831 := bstep (se 1 (by rfl) ⟨808373, by rfl⟩ : syracuseStep 1077831 = 1616747) B1616747
theorem B1077983 : Blo 1076618 1077983 := bstep (se 1 (by rfl) ⟨808487, by rfl⟩ : syracuseStep 1077983 = 1616975) B1616975
theorem B1078063 : Blo 1076618 1078063 := bstep (se 1 (by rfl) ⟨808547, by rfl⟩ : syracuseStep 1078063 = 1617095) B1617095
theorem B1078171 : Blo 1076618 1078171 := bstep (se 1 (by rfl) ⟨808628, by rfl⟩ : syracuseStep 1078171 = 1617257) B1617257
theorem B1078223 : Blo 1076618 1078223 := bstep (se 1 (by rfl) ⟨808667, by rfl⟩ : syracuseStep 1078223 = 1617335) B1617335
theorem B94565333 : Blo 1076618 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B1078247 : Blo 1076618 1078247 := bstep (se 1 (by rfl) ⟨808685, by rfl⟩ : syracuseStep 1078247 = 1617371) B1617371
theorem B5469281 : Blo 1076618 5469281 := bstep (se 2 (by rfl) ⟨2050980, by rfl⟩ : syracuseStep 5469281 = 4101961) B4101961
theorem B1078559 : Blo 1076618 1078559 := bstep (se 1 (by rfl) ⟨808919, by rfl⟩ : syracuseStep 1078559 = 1617839) B1617839
theorem B1537319 : Blo 1076618 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B1078619 : Blo 1076618 1078619 := bstep (se 1 (by rfl) ⟨808964, by rfl⟩ : syracuseStep 1078619 = 1617929) B1617929
theorem B1078639 : Blo 1076618 1078639 := bstep (se 1 (by rfl) ⟨808979, by rfl⟩ : syracuseStep 1078639 = 1617959) B1617959
theorem B1078695 : Blo 1076618 1078695 := bstep (se 1 (by rfl) ⟨809021, by rfl⟩ : syracuseStep 1078695 = 1618043) B1618043
theorem B1078779 : Blo 1076618 1078779 := bstep (se 1 (by rfl) ⟨809084, by rfl⟩ : syracuseStep 1078779 = 1618169) B1618169
theorem B1078847 : Blo 1076618 1078847 := bstep (se 1 (by rfl) ⟨809135, by rfl⟩ : syracuseStep 1078847 = 1618271) B1618271
theorem B1078855 : Blo 1076618 1078855 := bstep (se 1 (by rfl) ⟨809141, by rfl⟩ : syracuseStep 1078855 = 1618283) B1618283
theorem B11662987 : Blo 1076618 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B3274427 : Blo 1076618 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B1079007 : Blo 1076618 1079007 := bstep (se 1 (by rfl) ⟨809255, by rfl⟩ : syracuseStep 1079007 = 1618511) B1618511
theorem B1079087 : Blo 1076618 1079087 := bstep (se 1 (by rfl) ⟨809315, by rfl⟩ : syracuseStep 1079087 = 1618631) B1618631
theorem B2422583 : Blo 1076618 2422583 := bstep (se 1 (by rfl) ⟨1816937, by rfl⟩ : syracuseStep 2422583 = 3633875) B3633875
theorem B1079195 : Blo 1076618 1079195 := bstep (se 1 (by rfl) ⟨809396, by rfl⟩ : syracuseStep 1079195 = 1618793) B1618793
theorem B1079247 : Blo 1076618 1079247 := bstep (se 1 (by rfl) ⟨809435, by rfl⟩ : syracuseStep 1079247 = 1618871) B1618871
theorem B1079271 : Blo 1076618 1079271 := bstep (se 1 (by rfl) ⟨809453, by rfl⟩ : syracuseStep 1079271 = 1618907) B1618907
theorem B76904549 : Blo 1076618 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B2422889 : Blo 1076618 2422889 := bstep (se 2 (by rfl) ⟨908583, by rfl⟩ : syracuseStep 2422889 = 1817167) B1817167
theorem B1079583 : Blo 1076618 1079583 := bstep (se 1 (by rfl) ⟨809687, by rfl⟩ : syracuseStep 1079583 = 1619375) B1619375
theorem B2586971 : Blo 1076618 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B1079643 : Blo 1076618 1079643 := bstep (se 1 (by rfl) ⟨809732, by rfl⟩ : syracuseStep 1079643 = 1619465) B1619465
theorem B1079663 : Blo 1076618 1079663 := bstep (se 1 (by rfl) ⟨809747, by rfl⟩ : syracuseStep 1079663 = 1619495) B1619495
theorem B1079719 : Blo 1076618 1079719 := bstep (se 1 (by rfl) ⟨809789, by rfl⟩ : syracuseStep 1079719 = 1619579) B1619579
theorem B4094459 : Blo 1076618 4094459 := bstep (se 1 (by rfl) ⟨3070844, by rfl⟩ : syracuseStep 4094459 = 6141689) B6141689
theorem B1079803 : Blo 1076618 1079803 := bstep (se 1 (by rfl) ⟨809852, by rfl⟩ : syracuseStep 1079803 = 1619705) B1619705
theorem B1079871 : Blo 1076618 1079871 := bstep (se 1 (by rfl) ⟨809903, by rfl⟩ : syracuseStep 1079871 = 1619807) B1619807
theorem B1079879 : Blo 1076618 1079879 := bstep (se 1 (by rfl) ⟨809909, by rfl⟩ : syracuseStep 1079879 = 1619819) B1619819
theorem B2423375 : Blo 1076618 2423375 := bstep (se 1 (by rfl) ⟨1817531, by rfl⟩ : syracuseStep 2423375 = 3635063) B3635063
theorem B3635819 : Blo 1076618 3635819 := bstep (se 1 (by rfl) ⟨2726864, by rfl⟩ : syracuseStep 3635819 = 5453729) B5453729
theorem B2423519 : Blo 1076618 2423519 := bstep (se 1 (by rfl) ⟨1817639, by rfl⟩ : syracuseStep 2423519 = 3635279) B3635279
theorem B1080031 : Blo 1076618 1080031 := bstep (se 1 (by rfl) ⟨810023, by rfl⟩ : syracuseStep 1080031 = 1620047) B1620047
theorem B33159955 : Blo 1076618 33159955 := bstep (se 1 (by rfl) ⟨24869966, by rfl⟩ : syracuseStep 33159955 = 49739933) B49739933
theorem B1080111 : Blo 1076618 1080111 := bstep (se 1 (by rfl) ⟨810083, by rfl⟩ : syracuseStep 1080111 = 1620167) B1620167
theorem B1211215 : Blo 1076618 1211215 := bstep (se 1 (by rfl) ⟨908411, by rfl⟩ : syracuseStep 1211215 = 1816823) B1816823
theorem B1080219 : Blo 1076618 1080219 := bstep (se 1 (by rfl) ⟨810164, by rfl⟩ : syracuseStep 1080219 = 1620329) B1620329
theorem B1080271 : Blo 1076618 1080271 := bstep (se 1 (by rfl) ⟨810203, by rfl⟩ : syracuseStep 1080271 = 1620407) B1620407
theorem B2423771 : Blo 1076618 2423771 := bstep (se 1 (by rfl) ⟨1817828, by rfl⟩ : syracuseStep 2423771 = 3635657) B3635657
theorem B1080295 : Blo 1076618 1080295 := bstep (se 1 (by rfl) ⟨810221, by rfl⟩ : syracuseStep 1080295 = 1620443) B1620443
theorem B2915315 : Blo 1076618 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B2423951 : Blo 1076618 2423951 := bstep (se 1 (by rfl) ⟨1817963, by rfl⟩ : syracuseStep 2423951 = 3635927) B3635927
theorem B3636413 : Blo 1076618 3636413 := bstep (se 3 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 3636413 = 1363655) B1363655
theorem B1211611 : Blo 1076618 1211611 := bstep (se 1 (by rfl) ⟨908708, by rfl⟩ : syracuseStep 1211611 = 1817417) B1817417
theorem B2424041 : Blo 1076618 2424041 := bstep (se 2 (by rfl) ⟨909015, by rfl⟩ : syracuseStep 2424041 = 1818031) B1818031
theorem B2424095 : Blo 1076618 2424095 := bstep (se 1 (by rfl) ⟨1818071, by rfl⟩ : syracuseStep 2424095 = 3636143) B3636143
theorem B1080607 : Blo 1076618 1080607 := bstep (se 1 (by rfl) ⟨810455, by rfl⟩ : syracuseStep 1080607 = 1620911) B1620911
theorem B4095431 : Blo 1076618 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B1211899 : Blo 1076618 1211899 := bstep (se 1 (by rfl) ⟨908924, by rfl⟩ : syracuseStep 1211899 = 1817849) B1817849
theorem B10354337 : Blo 1076618 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B1212079 : Blo 1076618 1212079 := bstep (se 1 (by rfl) ⟨909059, by rfl⟩ : syracuseStep 1212079 = 1818119) B1818119
theorem B2424617 : Blo 1076618 2424617 := bstep (se 2 (by rfl) ⟨909231, by rfl⟩ : syracuseStep 2424617 = 1818463) B1818463
theorem B2916137 : Blo 1076618 2916137 := bstep (se 2 (by rfl) ⟨1093551, by rfl⟩ : syracuseStep 2916137 = 2187103) B2187103
theorem B2457391 : Blo 1076618 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B1212367 : Blo 1076618 1212367 := bstep (se 1 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 1212367 = 1818551) B1818551
theorem B3637601 : Blo 1076618 3637601 := bstep (se 2 (by rfl) ⟨1364100, by rfl⟩ : syracuseStep 3637601 = 2728201) B2728201
theorem B1212799 : Blo 1076618 1212799 := bstep (se 1 (by rfl) ⟨909599, by rfl⟩ : syracuseStep 1212799 = 1819199) B1819199
theorem B5177783 : Blo 1076618 5177783 := bstep (se 1 (by rfl) ⟨3883337, by rfl⟩ : syracuseStep 5177783 = 7766675) B7766675
theorem B2426219 : Blo 1076618 2426219 := bstep (se 1 (by rfl) ⟨1819664, by rfl⟩ : syracuseStep 2426219 = 3639329) B3639329
theorem B215549525 : Blo 1076618 215549525 := bstep (se 8 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 215549525 = 2525971) B2525971
theorem B10356335 : Blo 1076618 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B6227567 : Blo 1076618 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B2426489 : Blo 1076618 2426489 := bstep (se 2 (by rfl) ⟨909933, by rfl⟩ : syracuseStep 2426489 = 1819867) B1819867
theorem B3638951 : Blo 1076618 3638951 := bstep (se 1 (by rfl) ⟨2729213, by rfl⟩ : syracuseStep 3638951 = 5458427) B5458427
theorem B1214203 : Blo 1076618 1214203 := bstep (se 1 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 1214203 = 1821305) B1821305
theorem B1214239 : Blo 1076618 1214239 := bstep (se 1 (by rfl) ⟨910679, by rfl⟩ : syracuseStep 1214239 = 1821359) B1821359
theorem B3639545 : Blo 1076618 3639545 := bstep (se 2 (by rfl) ⟨1364829, by rfl⟩ : syracuseStep 3639545 = 2729659) B2729659
theorem B3639599 : Blo 1076618 3639599 := bstep (se 1 (by rfl) ⟨2729699, by rfl⟩ : syracuseStep 3639599 = 5459399) B5459399
theorem B3639815 : Blo 1076618 3639815 := bstep (se 1 (by rfl) ⟨2729861, by rfl⟩ : syracuseStep 3639815 = 5459723) B5459723
theorem B2427497 : Blo 1076618 2427497 := bstep (se 2 (by rfl) ⟨910311, by rfl⟩ : syracuseStep 2427497 = 1820623) B1820623
theorem B1215391 : Blo 1076618 1215391 := bstep (se 1 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 1215391 = 1823087) B1823087
theorem B1215535 : Blo 1076618 1215535 := bstep (se 1 (by rfl) ⟨911651, by rfl⟩ : syracuseStep 1215535 = 1823303) B1823303
theorem B3640463 : Blo 1076618 3640463 := bstep (se 1 (by rfl) ⟨2730347, by rfl⟩ : syracuseStep 3640463 = 5460695) B5460695
theorem B2428127 : Blo 1076618 2428127 := bstep (se 1 (by rfl) ⟨1821095, by rfl⟩ : syracuseStep 2428127 = 3642191) B3642191
theorem B2428343 : Blo 1076618 2428343 := bstep (se 1 (by rfl) ⟨1821257, by rfl⟩ : syracuseStep 2428343 = 3642515) B3642515
theorem B4099517 : Blo 1076618 4099517 := bstep (se 3 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 4099517 = 1537319) B1537319
theorem B3640895 : Blo 1076618 3640895 := bstep (se 1 (by rfl) ⟨2730671, by rfl⟩ : syracuseStep 3640895 = 5461343) B5461343
theorem B2428523 : Blo 1076618 2428523 := bstep (se 1 (by rfl) ⟨1821392, by rfl⟩ : syracuseStep 2428523 = 3642785) B3642785
theorem B2428793 : Blo 1076618 2428793 := bstep (se 2 (by rfl) ⟨910797, by rfl⟩ : syracuseStep 2428793 = 1821595) B1821595
theorem B1150943 : Blo 1076618 1150943 := bstep (se 1 (by rfl) ⟨863207, by rfl⟩ : syracuseStep 1150943 = 1726415) B1726415
theorem B3641597 : Blo 1076618 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B2593543 : Blo 1076618 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B3642137 : Blo 1076618 3642137 := bstep (se 2 (by rfl) ⟨1365801, by rfl⟩ : syracuseStep 3642137 = 2731603) B2731603
theorem B10359683 : Blo 1076618 10359683 := bstep (se 1 (by rfl) ⟨7769762, by rfl⟩ : syracuseStep 10359683 = 15539525) B15539525
theorem B15537041 : Blo 1076618 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B3937319 : Blo 1076618 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B3642407 : Blo 1076618 3642407 := bstep (se 1 (by rfl) ⟨2731805, by rfl⟩ : syracuseStep 3642407 = 5463611) B5463611
theorem B6919577 : Blo 1076618 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B1873307 : Blo 1076618 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B2725447 : Blo 1076618 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B2725559 : Blo 1076618 2725559 := bstep (se 1 (by rfl) ⟨2044169, by rfl⟩ : syracuseStep 2725559 = 4088339) B4088339
theorem B2430647 : Blo 1076618 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B3643487 : Blo 1076618 3643487 := bstep (se 1 (by rfl) ⟨2732615, by rfl⟩ : syracuseStep 3643487 = 5465231) B5465231
theorem B3644243 : Blo 1076618 3644243 := bstep (se 1 (by rfl) ⟨2733182, by rfl⟩ : syracuseStep 3644243 = 5466365) B5466365
theorem B2595689 : Blo 1076618 2595689 := bstep (se 2 (by rfl) ⟨973383, by rfl⟩ : syracuseStep 2595689 = 1946767) B1946767
theorem B13802399 : Blo 1076618 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B2300879 : Blo 1076618 2300879 := bstep (se 1 (by rfl) ⟨1725659, by rfl⟩ : syracuseStep 2300879 = 3451319) B3451319
theorem B6134899 : Blo 1076618 6134899 := bstep (se 1 (by rfl) ⟨4601174, by rfl⟩ : syracuseStep 6134899 = 9202349) B9202349
theorem B3644783 : Blo 1076618 3644783 := bstep (se 1 (by rfl) ⟨2733587, by rfl⟩ : syracuseStep 3644783 = 5467175) B5467175
theorem B2727503 : Blo 1076618 2727503 := bstep (se 1 (by rfl) ⟨2045627, by rfl⟩ : syracuseStep 2727503 = 4091255) B4091255
theorem B3645161 : Blo 1076618 3645161 := bstep (se 2 (by rfl) ⟨1366935, by rfl⟩ : syracuseStep 3645161 = 2733871) B2733871
theorem B74751781 : Blo 1076618 74751781 := bstep (se 4 (by rfl) ⟨7007979, by rfl⟩ : syracuseStep 74751781 = 14015959) B14015959
theorem B2301767 : Blo 1076618 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B1941403 : Blo 1076618 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B4923611 : Blo 1076618 4923611 := bstep (se 1 (by rfl) ⟨3692708, by rfl⟩ : syracuseStep 4923611 = 7385417) B7385417
theorem B2072807 : Blo 1076618 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B28057907 : Blo 1076618 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B7381367 : Blo 1076618 7381367 := bstep (se 1 (by rfl) ⟨5536025, by rfl⟩ : syracuseStep 7381367 = 11072051) B11072051
theorem B3646025 : Blo 1076618 3646025 := bstep (se 2 (by rfl) ⟨1367259, by rfl⟩ : syracuseStep 3646025 = 2734519) B2734519
theorem B15540959 : Blo 1076618 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B3646187 : Blo 1076618 3646187 := bstep (se 1 (by rfl) ⟨2734640, by rfl⟩ : syracuseStep 3646187 = 5469281) B5469281
theorem B5841683 : Blo 1076618 5841683 := bstep (se 1 (by rfl) ⟨4381262, by rfl⟩ : syracuseStep 5841683 = 8762525) B8762525
theorem B44213273 : Blo 1076618 44213273 := bstep (se 2 (by rfl) ⟨16579977, by rfl⟩ : syracuseStep 44213273 = 33159955) B33159955
theorem B1614953 : Blo 1076618 1614953 := bstep (se 2 (by rfl) ⟨605607, by rfl⟩ : syracuseStep 1614953 = 1211215) B1211215
theorem B1615055 : Blo 1076618 1615055 := bstep (se 1 (by rfl) ⟨1211291, by rfl⟩ : syracuseStep 1615055 = 2422583) B2422583
theorem B12264695 : Blo 1076618 12264695 := bstep (se 1 (by rfl) ⟨9198521, by rfl⟩ : syracuseStep 12264695 = 18397043) B18397043
theorem B1615259 : Blo 1076618 1615259 := bstep (se 1 (by rfl) ⟨1211444, by rfl⟩ : syracuseStep 1615259 = 2422889) B2422889
theorem B2303407 : Blo 1076618 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B8201735 : Blo 1076618 8201735 := bstep (se 1 (by rfl) ⟨6151301, by rfl⟩ : syracuseStep 8201735 = 12302603) B12302603
theorem B1615481 : Blo 1076618 1615481 := bstep (se 2 (by rfl) ⟨605805, by rfl⟩ : syracuseStep 1615481 = 1211611) B1211611
theorem B2729639 : Blo 1076618 2729639 := bstep (se 1 (by rfl) ⟨2047229, by rfl⟩ : syracuseStep 2729639 = 4094459) B4094459
theorem B1615583 : Blo 1076618 1615583 := bstep (se 1 (by rfl) ⟨1211687, by rfl⟩ : syracuseStep 1615583 = 2423375) B2423375
theorem B1615679 : Blo 1076618 1615679 := bstep (se 1 (by rfl) ⟨1211759, by rfl⟩ : syracuseStep 1615679 = 2423519) B2423519
theorem B2631503 : Blo 1076618 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B8529761 : Blo 1076618 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B1615847 : Blo 1076618 1615847 := bstep (se 1 (by rfl) ⟨1211885, by rfl⟩ : syracuseStep 1615847 = 2423771) B2423771
theorem B1943543 : Blo 1076618 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B4925431 : Blo 1076618 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B1615865 : Blo 1076618 1615865 := bstep (se 2 (by rfl) ⟨605949, by rfl⟩ : syracuseStep 1615865 = 1211899) B1211899
theorem B1615967 : Blo 1076618 1615967 := bstep (se 1 (by rfl) ⟨1211975, by rfl⟩ : syracuseStep 1615967 = 2423951) B2423951
theorem B1616027 : Blo 1076618 1616027 := bstep (se 1 (by rfl) ⟨1212020, by rfl⟩ : syracuseStep 1616027 = 2424041) B2424041
theorem B1616063 : Blo 1076618 1616063 := bstep (se 1 (by rfl) ⟨1212047, by rfl⟩ : syracuseStep 1616063 = 2424095) B2424095
theorem B1616105 : Blo 1076618 1616105 := bstep (se 2 (by rfl) ⟨606039, by rfl⟩ : syracuseStep 1616105 = 1212079) B1212079
theorem B2730287 : Blo 1076618 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B2763271 : Blo 1076618 2763271 := bstep (se 1 (by rfl) ⟨2072453, by rfl⟩ : syracuseStep 2763271 = 4144907) B4144907
theorem B1616411 : Blo 1076618 1616411 := bstep (se 1 (by rfl) ⟨1212308, by rfl⟩ : syracuseStep 1616411 = 2424617) B2424617
theorem B1944091 : Blo 1076618 1944091 := bstep (se 1 (by rfl) ⟨1458068, by rfl⟩ : syracuseStep 1944091 = 2916137) B2916137
theorem B1616489 : Blo 1076618 1616489 := bstep (se 2 (by rfl) ⟨606183, by rfl⟩ : syracuseStep 1616489 = 1212367) B1212367
theorem B5450489 : Blo 1076618 5450489 := bstep (se 2 (by rfl) ⟨2043933, by rfl⟩ : syracuseStep 5450489 = 4087867) B4087867
theorem B13806395 : Blo 1076618 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B1617017 : Blo 1076618 1617017 := bstep (se 2 (by rfl) ⟨606381, by rfl⟩ : syracuseStep 1617017 = 1212763) B1212763
theorem B1617119 : Blo 1076618 1617119 := bstep (se 1 (by rfl) ⟨1212839, by rfl⟩ : syracuseStep 1617119 = 2425679) B2425679
theorem B1617161 : Blo 1076618 1617161 := bstep (se 2 (by rfl) ⟨606435, by rfl⟩ : syracuseStep 1617161 = 1212871) B1212871
theorem B1617263 : Blo 1076618 1617263 := bstep (se 1 (by rfl) ⟨1212947, by rfl⟩ : syracuseStep 1617263 = 2425895) B2425895
theorem B1945043 : Blo 1076618 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B1617383 : Blo 1076618 1617383 := bstep (se 1 (by rfl) ⟨1213037, by rfl⟩ : syracuseStep 1617383 = 2426075) B2426075
theorem B2731583 : Blo 1076618 2731583 := bstep (se 1 (by rfl) ⟨2048687, by rfl⟩ : syracuseStep 2731583 = 4097375) B4097375
theorem B1617515 : Blo 1076618 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B29503109 : Blo 1076618 29503109 := bstep (se 4 (by rfl) ⟨2765916, by rfl⟩ : syracuseStep 29503109 = 5531833) B5531833
theorem B1617641 : Blo 1076618 1617641 := bstep (se 2 (by rfl) ⟨606615, by rfl⟩ : syracuseStep 1617641 = 1213231) B1213231
theorem B1617785 : Blo 1076618 1617785 := bstep (se 2 (by rfl) ⟨606669, by rfl⟩ : syracuseStep 1617785 = 1213339) B1213339
theorem B3157903 : Blo 1076618 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B1617887 : Blo 1076618 1617887 := bstep (se 1 (by rfl) ⟨1213415, by rfl⟩ : syracuseStep 1617887 = 2426831) B2426831
theorem B1618139 : Blo 1076618 1618139 := bstep (se 1 (by rfl) ⟨1213604, by rfl⟩ : syracuseStep 1618139 = 2427209) B2427209
theorem B1618151 : Blo 1076618 1618151 := bstep (se 1 (by rfl) ⟨1213613, by rfl⟩ : syracuseStep 1618151 = 2427227) B2427227
theorem B3453239 : Blo 1076618 3453239 := bstep (se 1 (by rfl) ⟨2589929, by rfl⟩ : syracuseStep 3453239 = 5179859) B5179859
theorem B2306431 : Blo 1076618 2306431 := bstep (se 1 (by rfl) ⟨1729823, by rfl⟩ : syracuseStep 2306431 = 3459647) B3459647
theorem B1618313 : Blo 1076618 1618313 := bstep (se 2 (by rfl) ⟨606867, by rfl⟩ : syracuseStep 1618313 = 1213735) B1213735
theorem B13840793 : Blo 1076618 13840793 := bstep (se 2 (by rfl) ⟨5190297, by rfl⟩ : syracuseStep 13840793 = 10380595) B10380595
theorem B1618409 : Blo 1076618 1618409 := bstep (se 2 (by rfl) ⟨606903, by rfl⟩ : syracuseStep 1618409 = 1213807) B1213807
theorem B2044511 : Blo 1076618 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B1618535 : Blo 1076618 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B1618667 : Blo 1076618 1618667 := bstep (se 1 (by rfl) ⟨1214000, by rfl⟩ : syracuseStep 1618667 = 2428001) B2428001
theorem B4371191 : Blo 1076618 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B1618697 : Blo 1076618 1618697 := bstep (se 2 (by rfl) ⟨607011, by rfl⟩ : syracuseStep 1618697 = 1214023) B1214023
theorem B1618799 : Blo 1076618 1618799 := bstep (se 1 (by rfl) ⟨1214099, by rfl⟩ : syracuseStep 1618799 = 2428199) B2428199
theorem B1619051 : Blo 1076618 1619051 := bstep (se 1 (by rfl) ⟨1214288, by rfl⟩ : syracuseStep 1619051 = 2428577) B2428577
theorem B26227907 : Blo 1076618 26227907 := bstep (se 1 (by rfl) ⟨19670930, by rfl⟩ : syracuseStep 26227907 = 39341861) B39341861
theorem B1619291 : Blo 1076618 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B1619567 : Blo 1076618 1619567 := bstep (se 1 (by rfl) ⟨1214675, by rfl⟩ : syracuseStep 1619567 = 2429351) B2429351
theorem B23672483 : Blo 1076618 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B1619639 : Blo 1076618 1619639 := bstep (se 1 (by rfl) ⟨1214729, by rfl⟩ : syracuseStep 1619639 = 2429459) B2429459
theorem B1619675 : Blo 1076618 1619675 := bstep (se 1 (by rfl) ⟨1214756, by rfl⟩ : syracuseStep 1619675 = 2429513) B2429513
theorem B1619849 : Blo 1076618 1619849 := bstep (se 2 (by rfl) ⟨607443, by rfl⟩ : syracuseStep 1619849 = 1214887) B1214887
theorem B1619951 : Blo 1076618 1619951 := bstep (se 1 (by rfl) ⟨1214963, by rfl⟩ : syracuseStep 1619951 = 2429927) B2429927
theorem B2734175 : Blo 1076618 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B15775859 : Blo 1076618 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B1620203 : Blo 1076618 1620203 := bstep (se 1 (by rfl) ⟨1215152, by rfl⟩ : syracuseStep 1620203 = 2430305) B2430305
theorem B1620263 : Blo 1076618 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B9222443 : Blo 1076618 9222443 := bstep (se 1 (by rfl) ⟨6916832, by rfl⟩ : syracuseStep 9222443 = 13833665) B13833665
theorem B1620347 : Blo 1076618 1620347 := bstep (se 1 (by rfl) ⟨1215260, by rfl⟩ : syracuseStep 1620347 = 2430521) B2430521
theorem B1620617 : Blo 1076618 1620617 := bstep (se 2 (by rfl) ⟨607731, by rfl⟩ : syracuseStep 1620617 = 1215463) B1215463
theorem B1817275 : Blo 1076618 1817275 := bstep (se 1 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 1817275 = 2725913) B2725913
theorem B1620791 : Blo 1076618 1620791 := bstep (se 1 (by rfl) ⟨1215593, by rfl⟩ : syracuseStep 1620791 = 2431187) B2431187
theorem B1620827 : Blo 1076618 1620827 := bstep (se 1 (by rfl) ⟨1215620, by rfl⟩ : syracuseStep 1620827 = 2431241) B2431241
theorem B1817579 : Blo 1076618 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B3882575 : Blo 1076618 3882575 := bstep (se 1 (by rfl) ⟨2911931, by rfl⟩ : syracuseStep 3882575 = 5823863) B5823863
theorem B1556263 : Blo 1076618 1556263 := bstep (se 1 (by rfl) ⟨1167197, by rfl⟩ : syracuseStep 1556263 = 2334395) B2334395
theorem B7389463 : Blo 1076618 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B4604455 : Blo 1076618 4604455 := bstep (se 1 (by rfl) ⟨3453341, by rfl⟩ : syracuseStep 4604455 = 6906683) B6906683
theorem B6832835 : Blo 1076618 6832835 := bstep (se 1 (by rfl) ⟨5124626, by rfl⟩ : syracuseStep 6832835 = 10249253) B10249253
theorem B1557295 : Blo 1076618 1557295 := bstep (se 1 (by rfl) ⟨1167971, by rfl⟩ : syracuseStep 1557295 = 2335943) B2335943
theorem B5456807 : Blo 1076618 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B6145631 : Blo 1076618 6145631 := bstep (se 1 (by rfl) ⟨4609223, by rfl⟩ : syracuseStep 6145631 = 9218447) B9218447
theorem B6571817 : Blo 1076618 6571817 := bstep (se 2 (by rfl) ⟨2464431, by rfl⟩ : syracuseStep 6571817 = 4928863) B4928863
theorem B1820495 : Blo 1076618 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B2050039 : Blo 1076618 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B15550649 : Blo 1076618 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B2050343 : Blo 1076618 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B31148347 : Blo 1076618 31148347 := bstep (se 1 (by rfl) ⟨23361260, by rfl⟩ : syracuseStep 31148347 = 46722521) B46722521
theorem B22465511 : Blo 1076618 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B1821737 : Blo 1076618 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B1821919 : Blo 1076618 1821919 := bstep (se 1 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 1821919 = 2732879) B2732879
theorem B1822351 : Blo 1076618 1822351 := bstep (se 1 (by rfl) ⟨1366763, by rfl⟩ : syracuseStep 1822351 = 2733527) B2733527
theorem B2182951 : Blo 1076618 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B3067769 : Blo 1076618 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B51269699 : Blo 1076618 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B1724647 : Blo 1076618 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B9228593 : Blo 1076618 9228593 := bstep (se 2 (by rfl) ⟨3460722, by rfl⟩ : syracuseStep 9228593 = 6921445) B6921445
theorem B3461543 : Blo 1076618 3461543 := bstep (se 1 (by rfl) ⟨2596157, by rfl⟩ : syracuseStep 3461543 = 5192315) B5192315
theorem B4608829 : Blo 1076618 4608829 := bstep (se 3 (by rfl) ⟨864155, by rfl⟩ : syracuseStep 4608829 = 1728311) B1728311
theorem B11653955 : Blo 1076618 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B6902891 : Blo 1076618 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B5821787 : Blo 1076618 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B1725851 : Blo 1076618 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B3069409 : Blo 1076618 3069409 := bstep (se 2 (by rfl) ⟨1151028, by rfl⟩ : syracuseStep 3069409 = 2302057) B2302057
theorem B19650059 : Blo 1076618 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13293179 : Blo 1076618 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B17487731 : Blo 1076618 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B5461991 : Blo 1076618 5461991 := bstep (se 1 (by rfl) ⟨4096493, by rfl⟩ : syracuseStep 5461991 = 8192987) B8192987
theorem B6903791 : Blo 1076618 6903791 := bstep (se 1 (by rfl) ⟨5177843, by rfl⟩ : syracuseStep 6903791 = 10355687) B10355687
theorem B3692639 : Blo 1076618 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B1726697 : Blo 1076618 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B29547341 : Blo 1076618 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B3070811 : Blo 1076618 3070811 := bstep (se 1 (by rfl) ⟨2303108, by rfl⟩ : syracuseStep 3070811 = 4606217) B4606217
theorem B2186423 : Blo 1076618 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1727671 : Blo 1076618 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B9329917 : Blo 1076618 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B6905249 : Blo 1076618 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B3890663 : Blo 1076618 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B62119547 : Blo 1076618 62119547 := bstep (se 1 (by rfl) ⟨46589660, by rfl⟩ : syracuseStep 62119547 = 93179321) B93179321
theorem B252174221 : Blo 1076618 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B3071915 : Blo 1076618 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B3891239 : Blo 1076618 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B4612315 : Blo 1076618 4612315 := bstep (se 1 (by rfl) ⟨3459236, by rfl⟩ : syracuseStep 4612315 = 6918473) B6918473
theorem B4154267 : Blo 1076618 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B56911157 : Blo 1076618 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B3073555 : Blo 1076618 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B5826131 : Blo 1076618 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B1533691 : Blo 1076618 1533691 := bstep (se 1 (by rfl) ⟨1150268, by rfl⟩ : syracuseStep 1533691 = 2300537) B2300537
theorem B3074057 : Blo 1076618 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B1534249 : Blo 1076618 1534249 := bstep (se 2 (by rfl) ⟨575343, by rfl⟩ : syracuseStep 1534249 = 1150687) B1150687
theorem B3074399 : Blo 1076618 3074399 := bstep (se 1 (by rfl) ⟨2305799, by rfl⟩ : syracuseStep 3074399 = 4611599) B4611599
theorem B23685605 : Blo 1076618 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B11660219 : Blo 1076618 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B1534955 : Blo 1076618 1534955 := bstep (se 1 (by rfl) ⟨1151216, by rfl⟩ : syracuseStep 1534955 = 2302433) B2302433
theorem B4615289 : Blo 1076618 4615289 := bstep (se 2 (by rfl) ⟨1730733, by rfl⟩ : syracuseStep 4615289 = 3461467) B3461467
theorem B1076711 : Blo 1076618 1076711 := bstep (se 1 (by rfl) ⟨807533, by rfl⟩ : syracuseStep 1076711 = 1615067) B1615067
theorem B3075641 : Blo 1076618 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B1076827 : Blo 1076618 1076827 := bstep (se 1 (by rfl) ⟨807620, by rfl⟩ : syracuseStep 1076827 = 1615241) B1615241
theorem B1077063 : Blo 1076618 1077063 := bstep (se 1 (by rfl) ⟨807797, by rfl⟩ : syracuseStep 1077063 = 1615595) B1615595
theorem B1077215 : Blo 1076618 1077215 := bstep (se 1 (by rfl) ⟨807911, by rfl⟩ : syracuseStep 1077215 = 1615823) B1615823
theorem B5468147 : Blo 1076618 5468147 := bstep (se 1 (by rfl) ⟨4101110, by rfl⟩ : syracuseStep 5468147 = 8202221) B8202221
theorem B1077479 : Blo 1076618 1077479 := bstep (se 1 (by rfl) ⟨808109, by rfl⟩ : syracuseStep 1077479 = 1616219) B1616219
theorem B5468471 : Blo 1076618 5468471 := bstep (se 1 (by rfl) ⟨4101353, by rfl⟩ : syracuseStep 5468471 = 8202707) B8202707
theorem B4092227 : Blo 1076618 4092227 := bstep (se 1 (by rfl) ⟨3069170, by rfl⟩ : syracuseStep 4092227 = 6138341) B6138341
theorem B1077631 : Blo 1076618 1077631 := bstep (se 1 (by rfl) ⟨808223, by rfl⟩ : syracuseStep 1077631 = 1616447) B1616447
theorem B1077711 : Blo 1076618 1077711 := bstep (se 1 (by rfl) ⟨808283, by rfl⟩ : syracuseStep 1077711 = 1616567) B1616567
theorem B1536607 : Blo 1076618 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B3633767 : Blo 1076618 3633767 := bstep (se 1 (by rfl) ⟨2725325, by rfl⟩ : syracuseStep 3633767 = 5450651) B5450651
theorem B1077863 : Blo 1076618 1077863 := bstep (se 1 (by rfl) ⟨808397, by rfl⟩ : syracuseStep 1077863 = 1616795) B1616795
theorem B1078127 : Blo 1076618 1078127 := bstep (se 1 (by rfl) ⟨808595, by rfl⟩ : syracuseStep 1078127 = 1617191) B1617191
theorem B1078183 : Blo 1076618 1078183 := bstep (se 1 (by rfl) ⟨808637, by rfl⟩ : syracuseStep 1078183 = 1617275) B1617275
theorem B3634091 : Blo 1076618 3634091 := bstep (se 1 (by rfl) ⟨2725568, by rfl⟩ : syracuseStep 3634091 = 5451137) B5451137
theorem B1078267 : Blo 1076618 1078267 := bstep (se 1 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 1078267 = 1617401) B1617401
theorem B1078335 : Blo 1076618 1078335 := bstep (se 1 (by rfl) ⟨808751, by rfl⟩ : syracuseStep 1078335 = 1617503) B1617503
theorem B4093001 : Blo 1076618 4093001 := bstep (se 2 (by rfl) ⟨1534875, by rfl⟩ : syracuseStep 4093001 = 3069751) B3069751
theorem B1078479 : Blo 1076618 1078479 := bstep (se 1 (by rfl) ⟨808859, by rfl⟩ : syracuseStep 1078479 = 1617719) B1617719
theorem B3634523 : Blo 1076618 3634523 := bstep (se 1 (by rfl) ⟨2725892, by rfl⟩ : syracuseStep 3634523 = 5451785) B5451785
theorem B1078683 : Blo 1076618 1078683 := bstep (se 1 (by rfl) ⟨809012, by rfl⟩ : syracuseStep 1078683 = 1618025) B1618025
theorem B3634631 : Blo 1076618 3634631 := bstep (se 1 (by rfl) ⟨2725973, by rfl⟩ : syracuseStep 3634631 = 5451947) B5451947
theorem B184612337 : Blo 1076618 184612337 := bstep (se 2 (by rfl) ⟨69229626, by rfl⟩ : syracuseStep 184612337 = 138459253) B138459253
theorem B5469767 : Blo 1076618 5469767 := bstep (se 1 (by rfl) ⟨4102325, by rfl⟩ : syracuseStep 5469767 = 8204651) B8204651
theorem B1078895 : Blo 1076618 1078895 := bstep (se 1 (by rfl) ⟨809171, by rfl⟩ : syracuseStep 1078895 = 1618343) B1618343
theorem B18904709 : Blo 1076618 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B1078951 : Blo 1076618 1078951 := bstep (se 1 (by rfl) ⟨809213, by rfl⟩ : syracuseStep 1078951 = 1618427) B1618427
theorem B1079035 : Blo 1076618 1079035 := bstep (se 1 (by rfl) ⟨809276, by rfl⟩ : syracuseStep 1079035 = 1618553) B1618553
theorem B3634955 : Blo 1076618 3634955 := bstep (se 1 (by rfl) ⟨2726216, by rfl⟩ : syracuseStep 3634955 = 5452433) B5452433
theorem B1079071 : Blo 1076618 1079071 := bstep (se 1 (by rfl) ⟨809303, by rfl⟩ : syracuseStep 1079071 = 1618607) B1618607
theorem B1079103 : Blo 1076618 1079103 := bstep (se 1 (by rfl) ⟨809327, by rfl⟩ : syracuseStep 1079103 = 1618655) B1618655
theorem B1537871 : Blo 1076618 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1079279 : Blo 1076618 1079279 := bstep (se 1 (by rfl) ⟨809459, by rfl⟩ : syracuseStep 1079279 = 1618919) B1618919
theorem B3635225 : Blo 1076618 3635225 := bstep (se 2 (by rfl) ⟨1363209, by rfl⟩ : syracuseStep 3635225 = 2726419) B2726419
theorem B1079451 : Blo 1076618 1079451 := bstep (se 1 (by rfl) ⟨809588, by rfl⟩ : syracuseStep 1079451 = 1619177) B1619177
theorem B1079487 : Blo 1076618 1079487 := bstep (se 1 (by rfl) ⟨809615, by rfl⟩ : syracuseStep 1079487 = 1619231) B1619231
theorem B2914537 : Blo 1076618 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B4094185 : Blo 1076618 4094185 := bstep (se 2 (by rfl) ⟨1535319, by rfl⟩ : syracuseStep 4094185 = 3070639) B3070639
theorem B1538281 : Blo 1076618 1538281 := bstep (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) B1153711
theorem B1079599 : Blo 1076618 1079599 := bstep (se 1 (by rfl) ⟨809699, by rfl⟩ : syracuseStep 1079599 = 1619399) B1619399
theorem B5831021 : Blo 1076618 5831021 := bstep (se 3 (by rfl) ⟨1093316, by rfl⟩ : syracuseStep 5831021 = 2186633) B2186633
theorem B1079835 : Blo 1076618 1079835 := bstep (se 1 (by rfl) ⟨809876, by rfl⟩ : syracuseStep 1079835 = 1619753) B1619753
theorem B1079839 : Blo 1076618 1079839 := bstep (se 1 (by rfl) ⟨809879, by rfl⟩ : syracuseStep 1079839 = 1619759) B1619759
theorem B8288891 : Blo 1076618 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B1080155 : Blo 1076618 1080155 := bstep (se 1 (by rfl) ⟨810116, by rfl⟩ : syracuseStep 1080155 = 1620233) B1620233
theorem B1080223 : Blo 1076618 1080223 := bstep (se 1 (by rfl) ⟨810167, by rfl⟩ : syracuseStep 1080223 = 1620335) B1620335
theorem B6913039 : Blo 1076618 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B1080367 : Blo 1076618 1080367 := bstep (se 1 (by rfl) ⟨810275, by rfl⟩ : syracuseStep 1080367 = 1620551) B1620551
theorem B2423879 : Blo 1076618 2423879 := bstep (se 1 (by rfl) ⟨1817909, by rfl⟩ : syracuseStep 2423879 = 3635819) B3635819
theorem B1080391 : Blo 1076618 1080391 := bstep (se 1 (by rfl) ⟨810293, by rfl⟩ : syracuseStep 1080391 = 1620587) B1620587
theorem B1080543 : Blo 1076618 1080543 := bstep (se 1 (by rfl) ⟨810407, by rfl⟩ : syracuseStep 1080543 = 1620815) B1620815
theorem B3636575 : Blo 1076618 3636575 := bstep (se 1 (by rfl) ⟨2727431, by rfl⟩ : syracuseStep 3636575 = 5454863) B5454863
theorem B49741249 : Blo 1076618 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B2424275 : Blo 1076618 2424275 := bstep (se 1 (by rfl) ⟨1818206, by rfl⟩ : syracuseStep 2424275 = 3636413) B3636413
theorem B2424545 : Blo 1076618 2424545 := bstep (se 2 (by rfl) ⟨909204, by rfl⟩ : syracuseStep 2424545 = 1818409) B1818409
theorem B3276521 : Blo 1076618 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B3637115 : Blo 1076618 3637115 := bstep (se 1 (by rfl) ⟨2727836, by rfl⟩ : syracuseStep 3637115 = 5455673) B5455673
theorem B2425067 : Blo 1076618 2425067 := bstep (se 1 (by rfl) ⟨1818800, by rfl⟩ : syracuseStep 2425067 = 3637601) B3637601
theorem B4555223 : Blo 1076618 4555223 := bstep (se 1 (by rfl) ⟨3416417, by rfl⟩ : syracuseStep 4555223 = 6832835) B6832835
theorem B3637871 : Blo 1076618 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B9208637 : Blo 1076618 9208637 := bstep (se 3 (by rfl) ⟨1726619, by rfl⟩ : syracuseStep 9208637 = 3453239) B3453239
theorem B4097087 : Blo 1076618 4097087 := bstep (se 1 (by rfl) ⟨3072815, by rfl⟩ : syracuseStep 4097087 = 6145631) B6145631
theorem B2425967 : Blo 1076618 2425967 := bstep (se 1 (by rfl) ⟨1819475, by rfl⟩ : syracuseStep 2425967 = 3638951) B3638951
theorem B1213663 : Blo 1076618 1213663 := bstep (se 1 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 1213663 = 1820495) B1820495
theorem B2426363 : Blo 1076618 2426363 := bstep (se 1 (by rfl) ⟨1819772, by rfl⟩ : syracuseStep 2426363 = 3639545) B3639545
theorem B2426399 : Blo 1076618 2426399 := bstep (se 1 (by rfl) ⟨1819799, by rfl⟩ : syracuseStep 2426399 = 3639599) B3639599
theorem B2426543 : Blo 1076618 2426543 := bstep (se 1 (by rfl) ⟨1819907, by rfl⟩ : syracuseStep 2426543 = 3639815) B3639815
theorem B14977007 : Blo 1076618 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B4098073 : Blo 1076618 4098073 := bstep (se 2 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 4098073 = 3073555) B3073555
theorem B1214491 : Blo 1076618 1214491 := bstep (se 1 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 1214491 = 1821737) B1821737
theorem B2426975 : Blo 1076618 2426975 := bstep (se 1 (by rfl) ⟨1820231, by rfl⟩ : syracuseStep 2426975 = 3640463) B3640463
theorem B2427263 : Blo 1076618 2427263 := bstep (se 1 (by rfl) ⟨1820447, by rfl⟩ : syracuseStep 2427263 = 3640895) B3640895
theorem B11078045 : Blo 1076618 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B2427731 : Blo 1076618 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B2428091 : Blo 1076618 2428091 := bstep (se 1 (by rfl) ⟨1821068, by rfl⟩ : syracuseStep 2428091 = 3642137) B3642137
theorem B7769303 : Blo 1076618 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B10358027 : Blo 1076618 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B2624879 : Blo 1076618 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2428271 : Blo 1076618 2428271 := bstep (se 1 (by rfl) ⟨1821203, by rfl⟩ : syracuseStep 2428271 = 3642407) B3642407
theorem B1150567 : Blo 1076618 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B1248871 : Blo 1076618 1248871 := bstep (se 1 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 1248871 = 1873307) B1873307
theorem B3641327 : Blo 1076618 3641327 := bstep (se 1 (by rfl) ⟨2730995, by rfl⟩ : syracuseStep 3641327 = 5461991) B5461991
theorem B2461759 : Blo 1076618 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B2428991 : Blo 1076618 2428991 := bstep (se 1 (by rfl) ⟨1821743, by rfl⟩ : syracuseStep 2428991 = 3643487) B3643487
theorem B2429225 : Blo 1076618 2429225 := bstep (se 2 (by rfl) ⟨910959, by rfl⟩ : syracuseStep 2429225 = 1821919) B1821919
theorem B19698227 : Blo 1076618 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2429495 : Blo 1076618 2429495 := bstep (se 1 (by rfl) ⟨1822121, by rfl⟩ : syracuseStep 2429495 = 3644243) B3644243
theorem B2429801 : Blo 1076618 2429801 := bstep (se 2 (by rfl) ⟨911175, by rfl⟩ : syracuseStep 2429801 = 1822351) B1822351
theorem B4100989 : Blo 1076618 4100989 := bstep (se 3 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 4100989 = 1537871) B1537871
theorem B2429855 : Blo 1076618 2429855 := bstep (se 1 (by rfl) ⟨1822391, by rfl⟩ : syracuseStep 2429855 = 3644783) B3644783
theorem B2593775 : Blo 1076618 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B2430107 : Blo 1076618 2430107 := bstep (se 1 (by rfl) ⟨1822580, by rfl⟩ : syracuseStep 2430107 = 3645161) B3645161
theorem B2594159 : Blo 1076618 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B3282407 : Blo 1076618 3282407 := bstep (se 1 (by rfl) ⟨2461805, by rfl⟩ : syracuseStep 3282407 = 4923611) B4923611
theorem B1381871 : Blo 1076618 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B4920911 : Blo 1076618 4920911 := bstep (se 1 (by rfl) ⟨3690683, by rfl⟩ : syracuseStep 4920911 = 7381367) B7381367
theorem B2299529 : Blo 1076618 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B2430683 : Blo 1076618 2430683 := bstep (se 1 (by rfl) ⟨1823012, by rfl⟩ : syracuseStep 2430683 = 3646025) B3646025
theorem B10360639 : Blo 1076618 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B2430791 : Blo 1076618 2430791 := bstep (se 1 (by rfl) ⟨1823093, by rfl⟩ : syracuseStep 2430791 = 3646187) B3646187
theorem B7773479 : Blo 1076618 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B19668739 : Blo 1076618 19668739 := bstep (se 1 (by rfl) ⟨14751554, by rfl⟩ : syracuseStep 19668739 = 29503109) B29503109
theorem B3645431 : Blo 1076618 3645431 := bstep (se 1 (by rfl) ⟨2734073, by rfl⟩ : syracuseStep 3645431 = 5468147) B5468147
theorem B3645647 : Blo 1076618 3645647 := bstep (se 1 (by rfl) ⟨2734235, by rfl⟩ : syracuseStep 3645647 = 5468471) B5468471
theorem B2728151 : Blo 1076618 2728151 := bstep (se 1 (by rfl) ⟨2046113, by rfl⟩ : syracuseStep 2728151 = 4092227) B4092227
theorem B2728667 : Blo 1076618 2728667 := bstep (se 1 (by rfl) ⟨2046500, by rfl⟩ : syracuseStep 2728667 = 4093001) B4093001
theorem B3646511 : Blo 1076618 3646511 := bstep (se 1 (by rfl) ⟨2734883, by rfl⟩ : syracuseStep 3646511 = 5469767) B5469767
theorem B9217385 : Blo 1076618 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B2303561 : Blo 1076618 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B1615919 : Blo 1076618 1615919 := bstep (se 1 (by rfl) ⟨1211939, by rfl⟩ : syracuseStep 1615919 = 2423879) B2423879
theorem B1616183 : Blo 1076618 1616183 := bstep (se 1 (by rfl) ⟨1212137, by rfl⟩ : syracuseStep 1616183 = 2424275) B2424275
theorem B2075017 : Blo 1076618 2075017 := bstep (se 2 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 2075017 = 1556263) B1556263
theorem B1616363 : Blo 1076618 1616363 := bstep (se 1 (by rfl) ⟨1212272, by rfl⟩ : syracuseStep 1616363 = 2424545) B2424545
theorem B136719197 : Blo 1076618 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B1617065 : Blo 1076618 1617065 := bstep (se 2 (by rfl) ⟨606399, by rfl⟩ : syracuseStep 1617065 = 1212799) B1212799
theorem B6139273 : Blo 1076618 6139273 := bstep (se 2 (by rfl) ⟨2302227, by rfl⟩ : syracuseStep 6139273 = 4604455) B4604455
theorem B1617479 : Blo 1076618 1617479 := bstep (se 1 (by rfl) ⟨1213109, by rfl⟩ : syracuseStep 1617479 = 2426219) B2426219
theorem B143699683 : Blo 1076618 143699683 := bstep (se 1 (by rfl) ⟨107774762, by rfl⟩ : syracuseStep 143699683 = 215549525) B215549525
theorem B1617659 : Blo 1076618 1617659 := bstep (se 1 (by rfl) ⟨1213244, by rfl⟩ : syracuseStep 1617659 = 2426489) B2426489
theorem B13807421 : Blo 1076618 13807421 := bstep (se 3 (by rfl) ⟨2588891, by rfl⟩ : syracuseStep 13807421 = 5177783) B5177783
theorem B8204165 : Blo 1076618 8204165 := bstep (se 4 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 8204165 = 1538281) B1538281
theorem B10367099 : Blo 1076618 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B1618331 : Blo 1076618 1618331 := bstep (se 1 (by rfl) ⟨1213748, by rfl⟩ : syracuseStep 1618331 = 2427497) B2427497
theorem B1618751 : Blo 1076618 1618751 := bstep (se 1 (by rfl) ⟨1214063, by rfl⟩ : syracuseStep 1618751 = 2428127) B2428127
theorem B1618895 : Blo 1076618 1618895 := bstep (se 1 (by rfl) ⟨1214171, by rfl⟩ : syracuseStep 1618895 = 2428343) B2428343
theorem B2733011 : Blo 1076618 2733011 := bstep (se 1 (by rfl) ⟨2049758, by rfl⟩ : syracuseStep 2733011 = 4099517) B4099517
theorem B2044921 : Blo 1076618 2044921 := bstep (se 2 (by rfl) ⟨766845, by rfl⟩ : syracuseStep 2044921 = 1533691) B1533691
theorem B1618937 : Blo 1076618 1618937 := bstep (se 2 (by rfl) ⟨607101, by rfl⟩ : syracuseStep 1618937 = 1214203) B1214203
theorem B1618985 : Blo 1076618 1618985 := bstep (se 2 (by rfl) ⟨607119, by rfl⟩ : syracuseStep 1618985 = 1214239) B1214239
theorem B1619015 : Blo 1076618 1619015 := bstep (se 1 (by rfl) ⟨1214261, by rfl⟩ : syracuseStep 1619015 = 2428523) B2428523
theorem B2045179 : Blo 1076618 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B1619195 : Blo 1076618 1619195 := bstep (se 1 (by rfl) ⟨1214396, by rfl⟩ : syracuseStep 1619195 = 2428793) B2428793
theorem B6567241 : Blo 1076618 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B2733385 : Blo 1076618 2733385 := bstep (se 2 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 2733385 = 2050039) B2050039
theorem B10368485 : Blo 1076618 10368485 := bstep (se 4 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 10368485 = 1944091) B1944091
theorem B2307695 : Blo 1076618 2307695 := bstep (se 1 (by rfl) ⟨1730771, by rfl⟩ : syracuseStep 2307695 = 3461543) B3461543
theorem B2045665 : Blo 1076618 2045665 := bstep (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) B1534249
theorem B41531129 : Blo 1076618 41531129 := bstep (se 2 (by rfl) ⟨15574173, by rfl⟩ : syracuseStep 41531129 = 31148347) B31148347
theorem B3684361 : Blo 1076618 3684361 := bstep (se 2 (by rfl) ⟨1381635, by rfl⟩ : syracuseStep 3684361 = 2763271) B2763271
theorem B4601927 : Blo 1076618 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B3881191 : Blo 1076618 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B8862119 : Blo 1076618 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B1817039 : Blo 1076618 1817039 := bstep (se 1 (by rfl) ⟨1362779, by rfl⟩ : syracuseStep 1817039 = 2725559) B2725559
theorem B1620431 : Blo 1076618 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B1620521 : Blo 1076618 1620521 := bstep (se 2 (by rfl) ⟨607695, by rfl⟩ : syracuseStep 1620521 = 1215391) B1215391
theorem B4602527 : Blo 1076618 4602527 := bstep (se 1 (by rfl) ⟨3451895, by rfl⟩ : syracuseStep 4602527 = 6903791) B6903791
theorem B1620713 : Blo 1076618 1620713 := bstep (se 2 (by rfl) ⟨607767, by rfl⟩ : syracuseStep 1620713 = 1215535) B1215535
theorem B8305573 : Blo 1076618 8305573 := bstep (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) B1557295
theorem B50412557 : Blo 1076618 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B2047207 : Blo 1076618 2047207 := bstep (se 1 (by rfl) ⟨1535405, by rfl⟩ : syracuseStep 2047207 = 3070811) B3070811
theorem B1457615 : Blo 1076618 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B4603499 : Blo 1076618 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B1818335 : Blo 1076618 1818335 := bstep (se 1 (by rfl) ⟨1363751, by rfl⟩ : syracuseStep 1818335 = 2727503) B2727503
theorem B4210537 : Blo 1076618 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B168116147 : Blo 1076618 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B2047943 : Blo 1076618 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B4604525 : Blo 1076618 4604525 := bstep (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) B1726697
theorem B29475515 : Blo 1076618 29475515 := bstep (se 1 (by rfl) ⟨22106636, by rfl⟩ : syracuseStep 29475515 = 44213273) B44213273
theorem B2048809 : Blo 1076618 2048809 := bstep (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) B1536607
theorem B8176463 : Blo 1076618 8176463 := bstep (se 1 (by rfl) ⟨6132347, by rfl⟩ : syracuseStep 8176463 = 12264695) B12264695
theorem B3458057 : Blo 1076618 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B3884087 : Blo 1076618 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B6145105 : Blo 1076618 6145105 := bstep (se 2 (by rfl) ⟨2304414, by rfl⟩ : syracuseStep 6145105 = 4608829) B4608829
theorem B1819759 : Blo 1076618 1819759 := bstep (se 1 (by rfl) ⟨1364819, by rfl⟩ : syracuseStep 1819759 = 2729639) B2729639
theorem B1754335 : Blo 1076618 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B5686507 : Blo 1076618 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B1295695 : Blo 1076618 1295695 := bstep (se 1 (by rfl) ⟨971771, by rfl⟩ : syracuseStep 1295695 = 1943543) B1943543
theorem B2049371 : Blo 1076618 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B1820191 : Blo 1076618 1820191 := bstep (se 1 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 1820191 = 2730287) B2730287
theorem B2049599 : Blo 1076618 2049599 := bstep (se 1 (by rfl) ⟨1537199, by rfl⟩ : syracuseStep 2049599 = 3074399) B3074399
theorem B1296695 : Blo 1076618 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B2050427 : Blo 1076618 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B1821055 : Blo 1076618 1821055 := bstep (se 1 (by rfl) ⟨1365791, by rfl⟩ : syracuseStep 1821055 = 2731583) B2731583
theorem B9227195 : Blo 1076618 9227195 := bstep (se 1 (by rfl) ⟨6920396, by rfl⟩ : syracuseStep 9227195 = 13840793) B13840793
theorem B3886049 : Blo 1076618 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B5458913 : Blo 1076618 5458913 := bstep (se 2 (by rfl) ⟨2047092, by rfl⟩ : syracuseStep 5458913 = 4094185) B4094185
theorem B1363007 : Blo 1076618 1363007 := bstep (se 1 (by rfl) ⟨1022255, by rfl⟩ : syracuseStep 1363007 = 2044511) B2044511
theorem B17485271 : Blo 1076618 17485271 := bstep (se 1 (by rfl) ⟨13113953, by rfl⟩ : syracuseStep 17485271 = 26227907) B26227907
theorem B15781655 : Blo 1076618 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B1822783 : Blo 1076618 1822783 := bstep (se 1 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 1822783 = 2734175) B2734175
theorem B8179865 : Blo 1076618 8179865 := bstep (se 2 (by rfl) ⟨3067449, by rfl⟩ : syracuseStep 8179865 = 6134899) B6134899
theorem B6148295 : Blo 1076618 6148295 := bstep (se 1 (by rfl) ⟨4611221, by rfl⟩ : syracuseStep 6148295 = 9222443) B9222443
theorem B3887347 : Blo 1076618 3887347 := bstep (se 1 (by rfl) ⟨2915510, by rfl⟩ : syracuseStep 3887347 = 5831021) B5831021
theorem B12439889 : Blo 1076618 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B5525927 : Blo 1076618 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B99669041 : Blo 1076618 99669041 := bstep (se 2 (by rfl) ⟨37375890, by rfl⟩ : syracuseStep 99669041 = 74751781) B74751781
theorem B2184347 : Blo 1076618 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B3069181 : Blo 1076618 3069181 := bstep (se 3 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 3069181 = 1150943) B1150943
theorem B6149753 : Blo 1076618 6149753 := bstep (se 2 (by rfl) ⟨2306157, by rfl⟩ : syracuseStep 6149753 = 4612315) B4612315
theorem B9852617 : Blo 1076618 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B6904223 : Blo 1076618 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B4151711 : Blo 1076618 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B4381211 : Blo 1076618 4381211 := bstep (se 1 (by rfl) ⟨3285908, by rfl⟩ : syracuseStep 4381211 = 6571817) B6571817
theorem B1366895 : Blo 1076618 1366895 := bstep (se 1 (by rfl) ⟨1025171, by rfl⟩ : syracuseStep 1366895 = 2050343) B2050343
theorem B3071209 : Blo 1076618 3071209 := bstep (se 2 (by rfl) ⟨1151703, by rfl⟩ : syracuseStep 3071209 = 2303407) B2303407
theorem B6152395 : Blo 1076618 6152395 := bstep (se 1 (by rfl) ⟨4614296, by rfl⟩ : syracuseStep 6152395 = 9228593) B9228593
theorem B6906455 : Blo 1076618 6906455 := bstep (se 1 (by rfl) ⟨5179841, by rfl⟩ : syracuseStep 6906455 = 10359683) B10359683
theorem B4613051 : Blo 1076618 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B13100039 : Blo 1076618 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B11658487 : Blo 1076618 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B1730459 : Blo 1076618 1730459 := bstep (se 1 (by rfl) ⟨1297844, by rfl⟩ : syracuseStep 1730459 = 2595689) B2595689
theorem B9201599 : Blo 1076618 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B1533919 : Blo 1076618 1533919 := bstep (se 1 (by rfl) ⟨1150439, by rfl⟩ : syracuseStep 1533919 = 2300879) B2300879
theorem B2910601 : Blo 1076618 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B41413031 : Blo 1076618 41413031 := bstep (se 1 (by rfl) ⟨31059773, by rfl⟩ : syracuseStep 41413031 = 62119547) B62119547
theorem B1534511 : Blo 1076618 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B18705271 : Blo 1076618 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B3075241 : Blo 1076618 3075241 := bstep (se 2 (by rfl) ⟨1153215, by rfl⟩ : syracuseStep 3075241 = 2306431) B2306431
theorem B3894455 : Blo 1076618 3894455 := bstep (se 1 (by rfl) ⟨2920841, by rfl⟩ : syracuseStep 3894455 = 5841683) B5841683
theorem B1076635 : Blo 1076618 1076635 := bstep (se 1 (by rfl) ⟨807476, by rfl⟩ : syracuseStep 1076635 = 1614953) B1614953
theorem B1076703 : Blo 1076618 1076703 := bstep (se 1 (by rfl) ⟨807527, by rfl⟩ : syracuseStep 1076703 = 1615055) B1615055
theorem B37940771 : Blo 1076618 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B1076839 : Blo 1076618 1076839 := bstep (se 1 (by rfl) ⟨807629, by rfl⟩ : syracuseStep 1076839 = 1615259) B1615259
theorem B5467823 : Blo 1076618 5467823 := bstep (se 1 (by rfl) ⟨4100867, by rfl⟩ : syracuseStep 5467823 = 8201735) B8201735
theorem B1076987 : Blo 1076618 1076987 := bstep (se 1 (by rfl) ⟨807740, by rfl⟩ : syracuseStep 1076987 = 1615481) B1615481
theorem B1077055 : Blo 1076618 1077055 := bstep (se 1 (by rfl) ⟨807791, by rfl⟩ : syracuseStep 1077055 = 1615583) B1615583
theorem B1077119 : Blo 1076618 1077119 := bstep (se 1 (by rfl) ⟨807839, by rfl⟩ : syracuseStep 1077119 = 1615679) B1615679
theorem B1077231 : Blo 1076618 1077231 := bstep (se 1 (by rfl) ⟨807923, by rfl⟩ : syracuseStep 1077231 = 1615847) B1615847
theorem B1077243 : Blo 1076618 1077243 := bstep (se 1 (by rfl) ⟨807932, by rfl⟩ : syracuseStep 1077243 = 1615865) B1615865
theorem B1077311 : Blo 1076618 1077311 := bstep (se 1 (by rfl) ⟨807983, by rfl⟩ : syracuseStep 1077311 = 1615967) B1615967
theorem B1077351 : Blo 1076618 1077351 := bstep (se 1 (by rfl) ⟨808013, by rfl⟩ : syracuseStep 1077351 = 1616027) B1616027
theorem B1077375 : Blo 1076618 1077375 := bstep (se 1 (by rfl) ⟨808031, by rfl⟩ : syracuseStep 1077375 = 1616063) B1616063
theorem B1077403 : Blo 1076618 1077403 := bstep (se 1 (by rfl) ⟨808052, by rfl⟩ : syracuseStep 1077403 = 1616105) B1616105
theorem B15790403 : Blo 1076618 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B1077607 : Blo 1076618 1077607 := bstep (se 1 (by rfl) ⟨808205, by rfl⟩ : syracuseStep 1077607 = 1616411) B1616411
theorem B1077659 : Blo 1076618 1077659 := bstep (se 1 (by rfl) ⟨808244, by rfl⟩ : syracuseStep 1077659 = 1616489) B1616489
theorem B3633659 : Blo 1076618 3633659 := bstep (se 1 (by rfl) ⟨2725244, by rfl⟩ : syracuseStep 3633659 = 5450489) B5450489
theorem B9204263 : Blo 1076618 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B4092545 : Blo 1076618 4092545 := bstep (se 2 (by rfl) ⟨1534704, by rfl⟩ : syracuseStep 4092545 = 3069409) B3069409
theorem B1078011 : Blo 1076618 1078011 := bstep (se 1 (by rfl) ⟨808508, by rfl⟩ : syracuseStep 1078011 = 1617017) B1617017
theorem B3076859 : Blo 1076618 3076859 := bstep (se 1 (by rfl) ⟨2307644, by rfl⟩ : syracuseStep 3076859 = 4615289) B4615289
theorem B3633929 : Blo 1076618 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B1078079 : Blo 1076618 1078079 := bstep (se 1 (by rfl) ⟨808559, by rfl⟩ : syracuseStep 1078079 = 1617119) B1617119
theorem B1078107 : Blo 1076618 1078107 := bstep (se 1 (by rfl) ⟨808580, by rfl⟩ : syracuseStep 1078107 = 1617161) B1617161
theorem B1078175 : Blo 1076618 1078175 := bstep (se 1 (by rfl) ⟨808631, by rfl⟩ : syracuseStep 1078175 = 1617263) B1617263
theorem B1078255 : Blo 1076618 1078255 := bstep (se 1 (by rfl) ⟨808691, by rfl⟩ : syracuseStep 1078255 = 1617383) B1617383
theorem B1078343 : Blo 1076618 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B1078427 : Blo 1076618 1078427 := bstep (se 1 (by rfl) ⟨808820, by rfl⟩ : syracuseStep 1078427 = 1617641) B1617641
theorem B1078523 : Blo 1076618 1078523 := bstep (se 1 (by rfl) ⟨808892, by rfl⟩ : syracuseStep 1078523 = 1617785) B1617785
theorem B4093213 : Blo 1076618 4093213 := bstep (se 3 (by rfl) ⟨767477, by rfl⟩ : syracuseStep 4093213 = 1534955) B1534955
theorem B1078591 : Blo 1076618 1078591 := bstep (se 1 (by rfl) ⟨808943, by rfl⟩ : syracuseStep 1078591 = 1617887) B1617887
theorem B1078759 : Blo 1076618 1078759 := bstep (se 1 (by rfl) ⟨809069, by rfl⟩ : syracuseStep 1078759 = 1618139) B1618139
theorem B1078767 : Blo 1076618 1078767 := bstep (se 1 (by rfl) ⟨809075, by rfl⟩ : syracuseStep 1078767 = 1618151) B1618151
theorem B1078875 : Blo 1076618 1078875 := bstep (se 1 (by rfl) ⟨809156, by rfl⟩ : syracuseStep 1078875 = 1618313) B1618313
theorem B1078939 : Blo 1076618 1078939 := bstep (se 1 (by rfl) ⟨809204, by rfl⟩ : syracuseStep 1078939 = 1618409) B1618409
theorem B2422511 : Blo 1076618 2422511 := bstep (se 1 (by rfl) ⟨1816883, by rfl⟩ : syracuseStep 2422511 = 3633767) B3633767
theorem B1079023 : Blo 1076618 1079023 := bstep (se 1 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 1079023 = 1618535) B1618535
theorem B1079111 : Blo 1076618 1079111 := bstep (se 1 (by rfl) ⟨809333, by rfl⟩ : syracuseStep 1079111 = 1618667) B1618667
theorem B2914127 : Blo 1076618 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B1079131 : Blo 1076618 1079131 := bstep (se 1 (by rfl) ⟨809348, by rfl⟩ : syracuseStep 1079131 = 1618697) B1618697
theorem B1079199 : Blo 1076618 1079199 := bstep (se 1 (by rfl) ⟨809399, by rfl⟩ : syracuseStep 1079199 = 1618799) B1618799
theorem B2422727 : Blo 1076618 2422727 := bstep (se 1 (by rfl) ⟨1817045, by rfl⟩ : syracuseStep 2422727 = 3634091) B3634091
theorem B1079367 : Blo 1076618 1079367 := bstep (se 1 (by rfl) ⟨809525, by rfl⟩ : syracuseStep 1079367 = 1619051) B1619051
theorem B2423015 : Blo 1076618 2423015 := bstep (se 1 (by rfl) ⟨1817261, by rfl⟩ : syracuseStep 2423015 = 3634523) B3634523
theorem B1079527 : Blo 1076618 1079527 := bstep (se 1 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 1079527 = 1619291) B1619291
theorem B2423033 : Blo 1076618 2423033 := bstep (se 2 (by rfl) ⟨908637, by rfl⟩ : syracuseStep 2423033 = 1817275) B1817275
theorem B2423087 : Blo 1076618 2423087 := bstep (se 1 (by rfl) ⟨1817315, by rfl⟩ : syracuseStep 2423087 = 3634631) B3634631
theorem B123074891 : Blo 1076618 123074891 := bstep (se 1 (by rfl) ⟨92306168, by rfl⟩ : syracuseStep 123074891 = 184612337) B184612337
theorem B1079711 : Blo 1076618 1079711 := bstep (se 1 (by rfl) ⟨809783, by rfl⟩ : syracuseStep 1079711 = 1619567) B1619567
theorem B1079759 : Blo 1076618 1079759 := bstep (se 1 (by rfl) ⟨809819, by rfl⟩ : syracuseStep 1079759 = 1619639) B1619639
theorem B1079783 : Blo 1076618 1079783 := bstep (se 1 (by rfl) ⟨809837, by rfl⟩ : syracuseStep 1079783 = 1619675) B1619675
theorem B2423303 : Blo 1076618 2423303 := bstep (se 1 (by rfl) ⟨1817477, by rfl⟩ : syracuseStep 2423303 = 3634955) B3634955
theorem B1079899 : Blo 1076618 1079899 := bstep (se 1 (by rfl) ⟨809924, by rfl⟩ : syracuseStep 1079899 = 1619849) B1619849
theorem B1079967 : Blo 1076618 1079967 := bstep (se 1 (by rfl) ⟨809975, by rfl⟩ : syracuseStep 1079967 = 1619951) B1619951
theorem B2423483 : Blo 1076618 2423483 := bstep (se 1 (by rfl) ⟨1817612, by rfl⟩ : syracuseStep 2423483 = 3635225) B3635225
theorem B10517239 : Blo 1076618 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B1080135 : Blo 1076618 1080135 := bstep (se 1 (by rfl) ⟨810101, by rfl⟩ : syracuseStep 1080135 = 1620203) B1620203
theorem B1080175 : Blo 1076618 1080175 := bstep (se 1 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 1080175 = 1620263) B1620263
theorem B1080231 : Blo 1076618 1080231 := bstep (se 1 (by rfl) ⟨810173, by rfl⟩ : syracuseStep 1080231 = 1620347) B1620347
theorem B1080411 : Blo 1076618 1080411 := bstep (se 1 (by rfl) ⟨810308, by rfl⟩ : syracuseStep 1080411 = 1620617) B1620617
theorem B1080527 : Blo 1076618 1080527 := bstep (se 1 (by rfl) ⟨810395, by rfl⟩ : syracuseStep 1080527 = 1620791) B1620791
theorem B1080551 : Blo 1076618 1080551 := bstep (se 1 (by rfl) ⟨810413, by rfl⟩ : syracuseStep 1080551 = 1620827) B1620827
theorem B66321665 : Blo 1076618 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B1211719 : Blo 1076618 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B2424383 : Blo 1076618 2424383 := bstep (se 1 (by rfl) ⟨1818287, by rfl⟩ : syracuseStep 2424383 = 3636575) B3636575
theorem B2588383 : Blo 1076618 2588383 := bstep (se 1 (by rfl) ⟨1941287, by rfl⟩ : syracuseStep 2588383 = 3882575) B3882575
theorem B2588537 : Blo 1076618 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B2424743 : Blo 1076618 2424743 := bstep (se 1 (by rfl) ⟨1818557, by rfl⟩ : syracuseStep 2424743 = 3637115) B3637115
theorem B2425247 : Blo 1076618 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B2589391 : Blo 1076618 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B8193473 : Blo 1076618 8193473 := bstep (se 2 (by rfl) ⟨3072552, by rfl⟩ : syracuseStep 8193473 = 6145105) B6145105
theorem B2426345 : Blo 1076618 2426345 := bstep (se 2 (by rfl) ⟨909879, by rfl⟩ : syracuseStep 2426345 = 1819759) B1819759
theorem B2590699 : Blo 1076618 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B3639275 : Blo 1076618 3639275 := bstep (se 1 (by rfl) ⟨2729456, by rfl⟩ : syracuseStep 3639275 = 5458913) B5458913
theorem B2426921 : Blo 1076618 2426921 := bstep (se 2 (by rfl) ⟨910095, by rfl⟩ : syracuseStep 2426921 = 1820191) B1820191
theorem B5179535 : Blo 1076618 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B10521103 : Blo 1076618 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B2427551 : Blo 1076618 2427551 := bstep (se 1 (by rfl) ⟨1820663, by rfl⟩ : syracuseStep 2427551 = 3641327) B3641327
theorem B4098863 : Blo 1076618 4098863 := bstep (se 1 (by rfl) ⟨3074147, by rfl⟩ : syracuseStep 4098863 = 6148295) B6148295
theorem B8293259 : Blo 1076618 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B2428073 : Blo 1076618 2428073 := bstep (se 2 (by rfl) ⟨910527, by rfl⟩ : syracuseStep 2428073 = 1821055) B1821055
theorem B3280607 : Blo 1076618 3280607 := bstep (se 1 (by rfl) ⟨2460455, by rfl⟩ : syracuseStep 3280607 = 4920911) B4920911
theorem B4099835 : Blo 1076618 4099835 := bstep (se 1 (by rfl) ⟨3074876, by rfl⟩ : syracuseStep 4099835 = 6149753) B6149753
theorem B24940361 : Blo 1076618 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B4100321 : Blo 1076618 4100321 := bstep (se 2 (by rfl) ⟨1537620, by rfl⟩ : syracuseStep 4100321 = 3075241) B3075241
theorem B2920807 : Blo 1076618 2920807 := bstep (se 1 (by rfl) ⟨2190605, by rfl⟩ : syracuseStep 2920807 = 4381211) B4381211
theorem B5182319 : Blo 1076618 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B191599577 : Blo 1076618 191599577 := bstep (se 2 (by rfl) ⟨71849841, by rfl⟩ : syracuseStep 191599577 = 143699683) B143699683
theorem B2430287 : Blo 1076618 2430287 := bstep (se 1 (by rfl) ⟨1822715, by rfl⟩ : syracuseStep 2430287 = 3645431) B3645431
theorem B2430377 : Blo 1076618 2430377 := bstep (se 2 (by rfl) ⟨911391, by rfl⟩ : syracuseStep 2430377 = 1822783) B1822783
theorem B2430431 : Blo 1076618 2430431 := bstep (se 1 (by rfl) ⟨1822823, by rfl⟩ : syracuseStep 2430431 = 3645647) B3645647
theorem B5183129 : Blo 1076618 5183129 := bstep (se 2 (by rfl) ⟨1943673, by rfl⟩ : syracuseStep 5183129 = 3887347) B3887347
theorem B2431007 : Blo 1076618 2431007 := bstep (se 1 (by rfl) ⟨1823255, by rfl⟩ : syracuseStep 2431007 = 3646511) B3646511
theorem B1153639 : Blo 1076618 1153639 := bstep (se 1 (by rfl) ⟨865229, by rfl⟩ : syracuseStep 1153639 = 1730459) B1730459
theorem B6134399 : Blo 1076618 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B2726561 : Blo 1076618 2726561 := bstep (se 2 (by rfl) ⟨1022460, by rfl⟩ : syracuseStep 2726561 = 2044921) B2044921
theorem B2726905 : Blo 1076618 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B8756321 : Blo 1076618 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B3644513 : Blo 1076618 3644513 := bstep (se 2 (by rfl) ⟨1366692, by rfl⟩ : syracuseStep 3644513 = 2733385) B2733385
theorem B2596303 : Blo 1076618 2596303 := bstep (se 1 (by rfl) ⟨1947227, by rfl⟩ : syracuseStep 2596303 = 3894455) B3894455
theorem B3645053 : Blo 1076618 3645053 := bstep (se 3 (by rfl) ⟨683447, by rfl⟩ : syracuseStep 3645053 = 1366895) B1366895
theorem B2727553 : Blo 1076618 2727553 := bstep (se 2 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 2727553 = 2045665) B2045665
theorem B3645215 : Blo 1076618 3645215 := bstep (se 1 (by rfl) ⟨2733911, by rfl⟩ : syracuseStep 3645215 = 5467823) B5467823
theorem B10526935 : Blo 1076618 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B6136175 : Blo 1076618 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2728363 : Blo 1076618 2728363 := bstep (se 1 (by rfl) ⟨2046272, by rfl⟩ : syracuseStep 2728363 = 4092545) B4092545
theorem B6136357 : Blo 1076618 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B1615007 : Blo 1076618 1615007 := bstep (se 1 (by rfl) ⟨1211255, by rfl⟩ : syracuseStep 1615007 = 2422511) B2422511
theorem B1942751 : Blo 1076618 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B1615151 : Blo 1076618 1615151 := bstep (se 1 (by rfl) ⟨1211363, by rfl⟩ : syracuseStep 1615151 = 2422727) B2422727
theorem B1615343 : Blo 1076618 1615343 := bstep (se 1 (by rfl) ⟨1211507, by rfl⟩ : syracuseStep 1615343 = 2423015) B2423015
theorem B1615355 : Blo 1076618 1615355 := bstep (se 1 (by rfl) ⟨1211516, by rfl⟩ : syracuseStep 1615355 = 2423033) B2423033
theorem B1615391 : Blo 1076618 1615391 := bstep (se 1 (by rfl) ⟨1211543, by rfl⟩ : syracuseStep 1615391 = 2423087) B2423087
theorem B5908079 : Blo 1076618 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B2729609 : Blo 1076618 2729609 := bstep (se 2 (by rfl) ⟨1023603, by rfl⟩ : syracuseStep 2729609 = 2047207) B2047207
theorem B1615535 : Blo 1076618 1615535 := bstep (se 1 (by rfl) ⟨1211651, by rfl⟩ : syracuseStep 1615535 = 2423303) B2423303
theorem B1615625 : Blo 1076618 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B1615655 : Blo 1076618 1615655 := bstep (se 1 (by rfl) ⟨1211741, by rfl⟩ : syracuseStep 1615655 = 2423483) B2423483
theorem B44214443 : Blo 1076618 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B3451177 : Blo 1076618 3451177 := bstep (se 2 (by rfl) ⟨1294191, by rfl⟩ : syracuseStep 3451177 = 2588383) B2588383
theorem B26224985 : Blo 1076618 26224985 := bstep (se 2 (by rfl) ⟨9834369, by rfl⟩ : syracuseStep 26224985 = 19668739) B19668739
theorem B1616255 : Blo 1076618 1616255 := bstep (se 1 (by rfl) ⟨1212191, by rfl⟩ : syracuseStep 1616255 = 2424383) B2424383
theorem B5614049 : Blo 1076618 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B1616495 : Blo 1076618 1616495 := bstep (se 1 (by rfl) ⟨1212371, by rfl⟩ : syracuseStep 1616495 = 2424743) B2424743
theorem B112077431 : Blo 1076618 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B1616711 : Blo 1076618 1616711 := bstep (se 1 (by rfl) ⟨1212533, by rfl⟩ : syracuseStep 1616711 = 2425067) B2425067
theorem B8203193 : Blo 1076618 8203193 := bstep (se 2 (by rfl) ⟨3076197, by rfl⟩ : syracuseStep 8203193 = 6152395) B6152395
theorem B6139091 : Blo 1076618 6139091 := bstep (se 1 (by rfl) ⟨4604318, by rfl⟩ : syracuseStep 6139091 = 9208637) B9208637
theorem B5450975 : Blo 1076618 5450975 := bstep (se 1 (by rfl) ⟨4088231, by rfl⟩ : syracuseStep 5450975 = 8176463) B8176463
theorem B2731391 : Blo 1076618 2731391 := bstep (se 1 (by rfl) ⟨2048543, by rfl⟩ : syracuseStep 2731391 = 4097087) B4097087
theorem B1617311 : Blo 1076618 1617311 := bstep (se 1 (by rfl) ⟨1212983, by rfl⟩ : syracuseStep 1617311 = 2425967) B2425967
theorem B1617575 : Blo 1076618 1617575 := bstep (se 1 (by rfl) ⟨1213181, by rfl⟩ : syracuseStep 1617575 = 2426363) B2426363
theorem B1617599 : Blo 1076618 1617599 := bstep (se 1 (by rfl) ⟨1213199, by rfl⟩ : syracuseStep 1617599 = 2426399) B2426399
theorem B2731745 : Blo 1076618 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B1617695 : Blo 1076618 1617695 := bstep (se 1 (by rfl) ⟨1213271, by rfl⟩ : syracuseStep 1617695 = 2426543) B2426543
theorem B1617983 : Blo 1076618 1617983 := bstep (se 1 (by rfl) ⟨1213487, by rfl⟩ : syracuseStep 1617983 = 2426975) B2426975
theorem B1618175 : Blo 1076618 1618175 := bstep (se 1 (by rfl) ⟨1213631, by rfl⟩ : syracuseStep 1618175 = 2427263) B2427263
theorem B7385363 : Blo 1076618 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B1618217 : Blo 1076618 1618217 := bstep (se 2 (by rfl) ⟨606831, by rfl⟩ : syracuseStep 1618217 = 1213663) B1213663
theorem B2339113 : Blo 1076618 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B7582009 : Blo 1076618 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B15544649 : Blo 1076618 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B1618487 : Blo 1076618 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B1618727 : Blo 1076618 1618727 := bstep (se 1 (by rfl) ⟨1214045, by rfl⟩ : syracuseStep 1618727 = 2428091) B2428091
theorem B1749919 : Blo 1076618 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1618847 : Blo 1076618 1618847 := bstep (se 1 (by rfl) ⟨1214135, by rfl⟩ : syracuseStep 1618847 = 2428271) B2428271
theorem B2045225 : Blo 1076618 2045225 := bstep (se 2 (by rfl) ⟨766959, by rfl⟩ : syracuseStep 2045225 = 1533919) B1533919
theorem B9221485 : Blo 1076618 9221485 := bstep (se 3 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 9221485 = 3458057) B3458057
theorem B1619321 : Blo 1076618 1619321 := bstep (se 2 (by rfl) ⟨607245, by rfl⟩ : syracuseStep 1619321 = 1214491) B1214491
theorem B1619327 : Blo 1076618 1619327 := bstep (se 1 (by rfl) ⟨1214495, by rfl⟩ : syracuseStep 1619327 = 2428991) B2428991
theorem B5453243 : Blo 1076618 5453243 := bstep (se 1 (by rfl) ⟨4089932, by rfl⟩ : syracuseStep 5453243 = 8179865) B8179865
theorem B1619483 : Blo 1076618 1619483 := bstep (se 1 (by rfl) ⟨1214612, by rfl⟩ : syracuseStep 1619483 = 2429225) B2429225
theorem B3683951 : Blo 1076618 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B1619663 : Blo 1076618 1619663 := bstep (se 1 (by rfl) ⟨1214747, by rfl⟩ : syracuseStep 1619663 = 2429495) B2429495
theorem B3880801 : Blo 1076618 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B2766689 : Blo 1076618 2766689 := bstep (se 2 (by rfl) ⟨1037508, by rfl⟩ : syracuseStep 2766689 = 2075017) B2075017
theorem B1619867 : Blo 1076618 1619867 := bstep (se 1 (by rfl) ⟨1214900, by rfl⟩ : syracuseStep 1619867 = 2429801) B2429801
theorem B1619903 : Blo 1076618 1619903 := bstep (se 1 (by rfl) ⟨1214927, by rfl⟩ : syracuseStep 1619903 = 2429855) B2429855
theorem B1456231 : Blo 1076618 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B1620071 : Blo 1076618 1620071 := bstep (se 1 (by rfl) ⟨1215053, by rfl⟩ : syracuseStep 1620071 = 2430107) B2430107
theorem B6568411 : Blo 1076618 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B1620455 : Blo 1076618 1620455 := bstep (se 1 (by rfl) ⟨1215341, by rfl⟩ : syracuseStep 1620455 = 2430683) B2430683
theorem B1620527 : Blo 1076618 1620527 := bstep (se 1 (by rfl) ⟨1215395, by rfl⟩ : syracuseStep 1620527 = 2430791) B2430791
theorem B3684989 : Blo 1076618 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B4602815 : Blo 1076618 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B2767807 : Blo 1076618 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B1818767 : Blo 1076618 1818767 := bstep (se 1 (by rfl) ⟨1364075, by rfl⟩ : syracuseStep 1818767 = 2728151) B2728151
theorem B4604303 : Blo 1076618 4604303 := bstep (se 1 (by rfl) ⟨3453227, by rfl⟩ : syracuseStep 4604303 = 6906455) B6906455
theorem B1819111 : Blo 1076618 1819111 := bstep (se 1 (by rfl) ⟨1364333, by rfl⟩ : syracuseStep 1819111 = 2728667) B2728667
theorem B8733359 : Blo 1076618 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B3457853 : Blo 1076618 3457853 := bstep (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) B1296695
theorem B6144923 : Blo 1076618 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B27608687 : Blo 1076618 27608687 := bstep (se 1 (by rfl) ⟨20706515, by rfl⟩ : syracuseStep 27608687 = 41413031) B41413031
theorem B5457617 : Blo 1076618 5457617 := bstep (se 2 (by rfl) ⟨2046606, by rfl⟩ : syracuseStep 5457617 = 4093213) B4093213
theorem B91146131 : Blo 1076618 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B13814185 : Blo 1076618 13814185 := bstep (se 2 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 13814185 = 10360639) B10360639
theorem B2051239 : Blo 1076618 2051239 := bstep (se 1 (by rfl) ⟨1538429, by rfl⟩ : syracuseStep 2051239 = 3076859) B3076859
theorem B1822007 : Blo 1076618 1822007 := bstep (se 1 (by rfl) ⟨1366505, by rfl⟩ : syracuseStep 1822007 = 2733011) B2733011
theorem B3886973 : Blo 1076618 3886973 := bstep (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) B1457615
theorem B3067951 : Blo 1076618 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B101175389 : Blo 1076618 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B3068351 : Blo 1076618 3068351 := bstep (se 1 (by rfl) ⟨2301263, by rfl⟩ : syracuseStep 3068351 = 4602527) B4602527
theorem B33608371 : Blo 1076618 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B6902765 : Blo 1076618 6902765 := bstep (se 3 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 6902765 = 2588537) B2588537
theorem B3068999 : Blo 1076618 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B5461181 : Blo 1076618 5461181 := bstep (se 3 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 5461181 = 2047943) B2047943
theorem B3036815 : Blo 1076618 3036815 := bstep (se 1 (by rfl) ⟨2277611, by rfl⟩ : syracuseStep 3036815 = 4555223) B4555223
theorem B13129381 : Blo 1076618 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B3069683 : Blo 1076618 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B1366247 : Blo 1076618 1366247 := bstep (se 1 (by rfl) ⟨1024685, by rfl⟩ : syracuseStep 1366247 = 2049371) B2049371
theorem B1366399 : Blo 1076618 1366399 := bstep (se 1 (by rfl) ⟨1024799, by rfl⟩ : syracuseStep 1366399 = 2049599) B2049599
theorem B9984671 : Blo 1076618 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B1366951 : Blo 1076618 1366951 := bstep (se 1 (by rfl) ⟨1025213, by rfl⟩ : syracuseStep 1366951 = 2050427) B2050427
theorem B78601373 : Blo 1076618 78601373 := bstep (se 3 (by rfl) ⟨14737757, by rfl⟩ : syracuseStep 78601373 = 29475515) B29475515
theorem B6151463 : Blo 1076618 6151463 := bstep (se 1 (by rfl) ⟨4613597, by rfl⟩ : syracuseStep 6151463 = 9227195) B9227195
theorem B6905351 : Blo 1076618 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B11656847 : Blo 1076618 11656847 := bstep (se 1 (by rfl) ⟨8742635, by rfl⟩ : syracuseStep 11656847 = 17485271) B17485271
theorem B5464097 : Blo 1076618 5464097 := bstep (se 2 (by rfl) ⟨2049036, by rfl⟩ : syracuseStep 5464097 = 4098073) B4098073
theorem B13132151 : Blo 1076618 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B1729183 : Blo 1076618 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B66446027 : Blo 1076618 66446027 := bstep (se 1 (by rfl) ⟨49834520, by rfl⟩ : syracuseStep 66446027 = 99669041) B99669041
theorem B1729439 : Blo 1076618 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B2188271 : Blo 1076618 2188271 := bstep (se 1 (by rfl) ⟨1641203, by rfl⟩ : syracuseStep 2188271 = 3282407) B3282407
theorem B1533019 : Blo 1076618 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B6153853 : Blo 1076618 6153853 := bstep (se 3 (by rfl) ⟨1153847, by rfl⟩ : syracuseStep 6153853 = 2307695) B2307695
theorem B8185697 : Blo 1076618 8185697 := bstep (se 2 (by rfl) ⟨3069636, by rfl⟩ : syracuseStep 8185697 = 6139273) B6139273
theorem B1665161 : Blo 1076618 1665161 := bstep (se 2 (by rfl) ⟨624435, by rfl⟩ : syracuseStep 1665161 = 1248871) B1248871
theorem B3075367 : Blo 1076618 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B1535707 : Blo 1076618 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B5467985 : Blo 1076618 5467985 := bstep (se 2 (by rfl) ⟨2050494, by rfl⟩ : syracuseStep 5467985 = 4100989) B4100989
theorem B1077279 : Blo 1076618 1077279 := bstep (se 1 (by rfl) ⟨807959, by rfl⟩ : syracuseStep 1077279 = 1615919) B1615919
theorem B4092029 : Blo 1076618 4092029 := bstep (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) B1534511
theorem B1077455 : Blo 1076618 1077455 := bstep (se 1 (by rfl) ⟨808091, by rfl⟩ : syracuseStep 1077455 = 1616183) B1616183
theorem B1077575 : Blo 1076618 1077575 := bstep (se 1 (by rfl) ⟨808181, by rfl⟩ : syracuseStep 1077575 = 1616363) B1616363
theorem B4092241 : Blo 1076618 4092241 := bstep (se 2 (by rfl) ⟨1534590, by rfl⟩ : syracuseStep 4092241 = 3069181) B3069181
theorem B6910373 : Blo 1076618 6910373 := bstep (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) B1295695
theorem B1078043 : Blo 1076618 1078043 := bstep (se 1 (by rfl) ⟨808532, by rfl⟩ : syracuseStep 1078043 = 1617065) B1617065
theorem B1078319 : Blo 1076618 1078319 := bstep (se 1 (by rfl) ⟨808739, by rfl⟩ : syracuseStep 1078319 = 1617479) B1617479
theorem B1078439 : Blo 1076618 1078439 := bstep (se 1 (by rfl) ⟨808829, by rfl⟩ : syracuseStep 1078439 = 1617659) B1617659
theorem B9204947 : Blo 1076618 9204947 := bstep (se 1 (by rfl) ⟨6903710, by rfl⟩ : syracuseStep 9204947 = 13807421) B13807421
theorem B5469443 : Blo 1076618 5469443 := bstep (se 1 (by rfl) ⟨4102082, by rfl⟩ : syracuseStep 5469443 = 8204165) B8204165
theorem B4912481 : Blo 1076618 4912481 := bstep (se 2 (by rfl) ⟨1842180, by rfl⟩ : syracuseStep 4912481 = 3684361) B3684361
theorem B6911399 : Blo 1076618 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B3634685 : Blo 1076618 3634685 := bstep (se 3 (by rfl) ⟨681503, by rfl⟩ : syracuseStep 3634685 = 1363007) B1363007
theorem B1078887 : Blo 1076618 1078887 := bstep (se 1 (by rfl) ⟨809165, by rfl⟩ : syracuseStep 1078887 = 1618331) B1618331
theorem B5174921 : Blo 1076618 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B2422439 : Blo 1076618 2422439 := bstep (se 1 (by rfl) ⟨1816829, by rfl⟩ : syracuseStep 2422439 = 3633659) B3633659
theorem B2422619 : Blo 1076618 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B1079167 : Blo 1076618 1079167 := bstep (se 1 (by rfl) ⟨809375, by rfl⟩ : syracuseStep 1079167 = 1618751) B1618751
theorem B1079263 : Blo 1076618 1079263 := bstep (se 1 (by rfl) ⟨809447, by rfl⟩ : syracuseStep 1079263 = 1618895) B1618895
theorem B1079291 : Blo 1076618 1079291 := bstep (se 1 (by rfl) ⟨809468, by rfl⟩ : syracuseStep 1079291 = 1618937) B1618937
theorem B1079323 : Blo 1076618 1079323 := bstep (se 1 (by rfl) ⟨809492, by rfl⟩ : syracuseStep 1079323 = 1618985) B1618985
theorem B1079343 : Blo 1076618 1079343 := bstep (se 1 (by rfl) ⟨809507, by rfl⟩ : syracuseStep 1079343 = 1619015) B1619015
theorem B1079463 : Blo 1076618 1079463 := bstep (se 1 (by rfl) ⟨809597, by rfl⟩ : syracuseStep 1079463 = 1619195) B1619195
theorem B6912323 : Blo 1076618 6912323 := bstep (se 1 (by rfl) ⟨5184242, by rfl⟩ : syracuseStep 6912323 = 10368485) B10368485
theorem B14022985 : Blo 1076618 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B27687419 : Blo 1076618 27687419 := bstep (se 1 (by rfl) ⟨20765564, by rfl⟩ : syracuseStep 27687419 = 41531129) B41531129
theorem B11074097 : Blo 1076618 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B82049927 : Blo 1076618 82049927 := bstep (se 1 (by rfl) ⟨61537445, by rfl⟩ : syracuseStep 82049927 = 123074891) B123074891
theorem B1211359 : Blo 1076618 1211359 := bstep (se 1 (by rfl) ⟨908519, by rfl⟩ : syracuseStep 1211359 = 1817039) B1817039
theorem B1080287 : Blo 1076618 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B4094945 : Blo 1076618 4094945 := bstep (se 2 (by rfl) ⟨1535604, by rfl⟩ : syracuseStep 4094945 = 3071209) B3071209
theorem B1080347 : Blo 1076618 1080347 := bstep (se 1 (by rfl) ⟨810260, by rfl⟩ : syracuseStep 1080347 = 1620521) B1620521
theorem B1080475 : Blo 1076618 1080475 := bstep (se 1 (by rfl) ⟨810356, by rfl⟩ : syracuseStep 1080475 = 1620713) B1620713
theorem B1212223 : Blo 1076618 1212223 := bstep (se 1 (by rfl) ⟨909167, by rfl⟩ : syracuseStep 1212223 = 1818335) B1818335
theorem B1212511 : Blo 1076618 1212511 := bstep (se 1 (by rfl) ⟨909383, by rfl⟩ : syracuseStep 1212511 = 1818767) B1818767
theorem B3637817 : Blo 1076618 3637817 := bstep (se 2 (by rfl) ⟨1364181, by rfl⟩ : syracuseStep 3637817 = 2728363) B2728363
theorem B4096615 : Blo 1076618 4096615 := bstep (se 1 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 4096615 = 6144923) B6144923
theorem B2425481 : Blo 1076618 2425481 := bstep (se 2 (by rfl) ⟨909555, by rfl⟩ : syracuseStep 2425481 = 1819111) B1819111
theorem B41452397 : Blo 1076618 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B3638411 : Blo 1076618 3638411 := bstep (se 1 (by rfl) ⟨2728808, by rfl⟩ : syracuseStep 3638411 = 5457617) B5457617
theorem B2426183 : Blo 1076618 2426183 := bstep (se 1 (by rfl) ⟨1819637, by rfl⟩ : syracuseStep 2426183 = 3639275) B3639275
theorem B1214671 : Blo 1076618 1214671 := bstep (se 1 (by rfl) ⟨911003, by rfl⟩ : syracuseStep 1214671 = 1822007) B1822007
theorem B2591315 : Blo 1076618 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B18418913 : Blo 1076618 18418913 := bstep (se 2 (by rfl) ⟨6907092, by rfl⟩ : syracuseStep 18418913 = 13814185) B13814185
theorem B5180669 : Blo 1076618 5180669 := bstep (se 3 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 5180669 = 1942751) B1942751
theorem B127733051 : Blo 1076618 127733051 := bstep (se 1 (by rfl) ⟨95799788, by rfl⟩ : syracuseStep 127733051 = 191599577) B191599577
theorem B14028137 : Blo 1076618 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B3640787 : Blo 1076618 3640787 := bstep (se 1 (by rfl) ⟨2730590, by rfl⟩ : syracuseStep 3640787 = 5461181) B5461181
theorem B4100489 : Blo 1076618 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B6656447 : Blo 1076618 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B2429675 : Blo 1076618 2429675 := bstep (se 1 (by rfl) ⟨1822256, by rfl⟩ : syracuseStep 2429675 = 3644513) B3644513
theorem B52400915 : Blo 1076618 52400915 := bstep (se 1 (by rfl) ⟨39300686, by rfl⟩ : syracuseStep 52400915 = 78601373) B78601373
theorem B4100975 : Blo 1076618 4100975 := bstep (se 1 (by rfl) ⟨3075731, by rfl⟩ : syracuseStep 4100975 = 6151463) B6151463
theorem B2430035 : Blo 1076618 2430035 := bstep (se 1 (by rfl) ⟨1822526, by rfl⟩ : syracuseStep 2430035 = 3645053) B3645053
theorem B7771231 : Blo 1076618 7771231 := bstep (se 1 (by rfl) ⟨5828423, by rfl⟩ : syracuseStep 7771231 = 11656847) B11656847
theorem B2430143 : Blo 1076618 2430143 := bstep (se 1 (by rfl) ⟨1822607, by rfl⟩ : syracuseStep 2430143 = 3645215) B3645215
theorem B3642731 : Blo 1076618 3642731 := bstep (se 1 (by rfl) ⟨2732048, by rfl⟩ : syracuseStep 3642731 = 5464097) B5464097
theorem B8754767 : Blo 1076618 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B3118817 : Blo 1076618 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B3643325 : Blo 1076618 3643325 := bstep (se 3 (by rfl) ⟨683123, by rfl⟩ : syracuseStep 3643325 = 1366247) B1366247
theorem B1152959 : Blo 1076618 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B3938719 : Blo 1076618 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B2333225 : Blo 1076618 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B29530925 : Blo 1076618 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B3742699 : Blo 1076618 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B74718287 : Blo 1076618 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B12295313 : Blo 1076618 12295313 := bstep (se 2 (by rfl) ⟨4610742, by rfl⟩ : syracuseStep 12295313 = 9221485) B9221485
theorem B17505841 : Blo 1076618 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B218799805 : Blo 1076618 218799805 := bstep (se 3 (by rfl) ⟨41024963, by rfl⟩ : syracuseStep 218799805 = 82049927) B82049927
theorem B3645323 : Blo 1076618 3645323 := bstep (se 1 (by rfl) ⟨2733992, by rfl⟩ : syracuseStep 3645323 = 5467985) B5467985
theorem B2728019 : Blo 1076618 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B1941641 : Blo 1076618 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B4923575 : Blo 1076618 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B8757881 : Blo 1076618 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B6136631 : Blo 1076618 6136631 := bstep (se 1 (by rfl) ⟨4602473, by rfl⟩ : syracuseStep 6136631 = 9204947) B9204947
theorem B3646295 : Blo 1076618 3646295 := bstep (se 1 (by rfl) ⟨2734721, by rfl⟩ : syracuseStep 3646295 = 5469443) B5469443
theorem B3449947 : Blo 1076618 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B1614959 : Blo 1076618 1614959 := bstep (se 1 (by rfl) ⟨1211219, by rfl⟩ : syracuseStep 1614959 = 2422439) B2422439
theorem B1615079 : Blo 1076618 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B1844459 : Blo 1076618 1844459 := bstep (se 1 (by rfl) ⟨1383344, by rfl⟩ : syracuseStep 1844459 = 2766689) B2766689
theorem B1615145 : Blo 1076618 1615145 := bstep (se 2 (by rfl) ⟨605679, by rfl⟩ : syracuseStep 1615145 = 1211359) B1211359
theorem B18458279 : Blo 1076618 18458279 := bstep (se 1 (by rfl) ⟨13843709, by rfl⟩ : syracuseStep 18458279 = 27687419) B27687419
theorem B2729963 : Blo 1076618 2729963 := bstep (se 1 (by rfl) ⟨2047472, by rfl⟩ : syracuseStep 2729963 = 4094945) B4094945
theorem B1616297 : Blo 1076618 1616297 := bstep (se 2 (by rfl) ⟨606111, by rfl⟩ : syracuseStep 1616297 = 1212223) B1212223
theorem B1616831 : Blo 1076618 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B14035913 : Blo 1076618 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B2305235 : Blo 1076618 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B2305577 : Blo 1076618 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B1617563 : Blo 1076618 1617563 := bstep (se 1 (by rfl) ⟨1213172, by rfl⟩ : syracuseStep 1617563 = 2426345) B2426345
theorem B18427661 : Blo 1076618 18427661 := bstep (se 3 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 18427661 = 6910373) B6910373
theorem B60764087 : Blo 1076618 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B1617947 : Blo 1076618 1617947 := bstep (se 1 (by rfl) ⟨1213460, by rfl⟩ : syracuseStep 1617947 = 2426921) B2426921
theorem B3453023 : Blo 1076618 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B2044025 : Blo 1076618 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B1618367 : Blo 1076618 1618367 := bstep (se 1 (by rfl) ⟨1213775, by rfl⟩ : syracuseStep 1618367 = 2427551) B2427551
theorem B2732575 : Blo 1076618 2732575 := bstep (se 1 (by rfl) ⟨2049431, by rfl⟩ : syracuseStep 2732575 = 4098863) B4098863
theorem B1618715 : Blo 1076618 1618715 := bstep (se 1 (by rfl) ⟨1214036, by rfl⟩ : syracuseStep 1618715 = 2428073) B2428073
theorem B8205137 : Blo 1076618 8205137 := bstep (se 2 (by rfl) ⟨3076926, by rfl⟩ : syracuseStep 8205137 = 6153853) B6153853
theorem B2733223 : Blo 1076618 2733223 := bstep (se 1 (by rfl) ⟨2049917, by rfl⟩ : syracuseStep 2733223 = 4099835) B4099835
theorem B16626907 : Blo 1076618 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B3454265 : Blo 1076618 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B67450259 : Blo 1076618 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B2733547 : Blo 1076618 2733547 := bstep (se 1 (by rfl) ⟨2050160, by rfl⟩ : syracuseStep 2733547 = 4100321) B4100321
theorem B2045567 : Blo 1076618 2045567 := bstep (se 1 (by rfl) ⟨1534175, by rfl⟩ : syracuseStep 2045567 = 3068351) B3068351
theorem B4601569 : Blo 1076618 4601569 := bstep (se 2 (by rfl) ⟨1725588, by rfl⟩ : syracuseStep 4601569 = 3451177) B3451177
theorem B4601843 : Blo 1076618 4601843 := bstep (se 1 (by rfl) ⟨3451382, by rfl⟩ : syracuseStep 4601843 = 6902765) B6902765
theorem B2045999 : Blo 1076618 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B1620191 : Blo 1076618 1620191 := bstep (se 1 (by rfl) ⟨1215143, by rfl⟩ : syracuseStep 1620191 = 2430287) B2430287
theorem B1620251 : Blo 1076618 1620251 := bstep (se 1 (by rfl) ⟨1215188, by rfl⟩ : syracuseStep 1620251 = 2430377) B2430377
theorem B1620287 : Blo 1076618 1620287 := bstep (se 1 (by rfl) ⟨1215215, by rfl⟩ : syracuseStep 1620287 = 2430431) B2430431
theorem B13810085 : Blo 1076618 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B3455419 : Blo 1076618 3455419 := bstep (se 1 (by rfl) ⟨2591564, by rfl⟩ : syracuseStep 3455419 = 5183129) B5183129
theorem B2046455 : Blo 1076618 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B1620671 : Blo 1076618 1620671 := bstep (se 1 (by rfl) ⟨1215503, by rfl⟩ : syracuseStep 1620671 = 2431007) B2431007
theorem B2734985 : Blo 1076618 2734985 := bstep (se 2 (by rfl) ⟨1025619, by rfl⟩ : syracuseStep 2734985 = 2051239) B2051239
theorem B1817707 : Blo 1076618 1817707 := bstep (se 1 (by rfl) ⟨1363280, by rfl⟩ : syracuseStep 1817707 = 2726561) B2726561
theorem B2047609 : Blo 1076618 2047609 := bstep (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) B1535707
theorem B4603567 : Blo 1076618 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B10109345 : Blo 1076618 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B5456321 : Blo 1076618 5456321 := bstep (se 2 (by rfl) ⟨2046120, by rfl⟩ : syracuseStep 5456321 = 4092241) B4092241
theorem B1458847 : Blo 1076618 1458847 := bstep (se 1 (by rfl) ⟨1094135, by rfl⟩ : syracuseStep 1458847 = 2188271) B2188271
theorem B44811161 : Blo 1076618 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B1819739 : Blo 1076618 1819739 := bstep (se 1 (by rfl) ⟨1364804, by rfl⟩ : syracuseStep 1819739 = 2729609) B2729609
theorem B5457131 : Blo 1076618 5457131 := bstep (se 1 (by rfl) ⟨4092848, by rfl⟩ : syracuseStep 5457131 = 8185697) B8185697
theorem B29476295 : Blo 1076618 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B17483323 : Blo 1076618 17483323 := bstep (se 1 (by rfl) ⟨13112492, by rfl⟩ : syracuseStep 17483323 = 26224985) B26224985
theorem B1820927 : Blo 1076618 1820927 := bstep (se 1 (by rfl) ⟨1365695, by rfl⟩ : syracuseStep 1820927 = 2731391) B2731391
theorem B1821163 : Blo 1076618 1821163 := bstep (se 1 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 1821163 = 2731745) B2731745
theorem B23350189 : Blo 1076618 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B18697313 : Blo 1076618 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B1821865 : Blo 1076618 1821865 := bstep (se 2 (by rfl) ⟨683199, by rfl⟩ : syracuseStep 1821865 = 1366399) B1366399
theorem B1363483 : Blo 1076618 1363483 := bstep (se 1 (by rfl) ⟨1022612, by rfl⟩ : syracuseStep 1363483 = 2045225) B2045225
theorem B4607599 : Blo 1076618 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B1822601 : Blo 1076618 1822601 := bstep (se 2 (by rfl) ⟨683475, by rfl⟩ : syracuseStep 1822601 = 1366951) B1366951
theorem B3690409 : Blo 1076618 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B4608215 : Blo 1076618 4608215 := bstep (se 1 (by rfl) ⟨3456161, by rfl⟩ : syracuseStep 4608215 = 6912323) B6912323
theorem B3461737 : Blo 1076618 3461737 := bstep (se 2 (by rfl) ⟨1298151, by rfl⟩ : syracuseStep 3461737 = 2596303) B2596303
theorem B3068543 : Blo 1076618 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B3069535 : Blo 1076618 3069535 := bstep (se 1 (by rfl) ⟨2302151, by rfl⟩ : syracuseStep 3069535 = 4604303) B4604303
theorem B5822239 : Blo 1076618 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B8181809 : Blo 1076618 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B5462315 : Blo 1076618 5462315 := bstep (se 1 (by rfl) ⟨4096736, by rfl⟩ : syracuseStep 5462315 = 8193473) B8193473
theorem B18405791 : Blo 1076618 18405791 := bstep (se 1 (by rfl) ⟨13804343, by rfl⟩ : syracuseStep 18405791 = 27608687) B27608687
theorem B5528839 : Blo 1076618 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B13819517 : Blo 1076618 13819517 := bstep (se 3 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 13819517 = 5182319) B5182319
theorem B2187071 : Blo 1076618 2187071 := bstep (se 1 (by rfl) ⟨1640303, by rfl⟩ : syracuseStep 2187071 = 3280607) B3280607
theorem B2024543 : Blo 1076618 2024543 := bstep (se 1 (by rfl) ⟨1518407, by rfl⟩ : syracuseStep 2024543 = 3036815) B3036815
theorem B4089599 : Blo 1076618 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B4090601 : Blo 1076618 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B4090783 : Blo 1076618 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B44297351 : Blo 1076618 44297351 := bstep (se 1 (by rfl) ⟨33223013, by rfl⟩ : syracuseStep 44297351 = 66446027) B66446027
theorem B3894409 : Blo 1076618 3894409 := bstep (se 2 (by rfl) ⟨1460403, by rfl⟩ : syracuseStep 3894409 = 2920807) B2920807
theorem B1076671 : Blo 1076618 1076671 := bstep (se 1 (by rfl) ⟨807503, by rfl⟩ : syracuseStep 1076671 = 1615007) B1615007
theorem B1076767 : Blo 1076618 1076767 := bstep (se 1 (by rfl) ⟨807575, by rfl⟩ : syracuseStep 1076767 = 1615151) B1615151
theorem B1076895 : Blo 1076618 1076895 := bstep (se 1 (by rfl) ⟨807671, by rfl⟩ : syracuseStep 1076895 = 1615343) B1615343
theorem B1076903 : Blo 1076618 1076903 := bstep (se 1 (by rfl) ⟨807677, by rfl⟩ : syracuseStep 1076903 = 1615355) B1615355
theorem B1076927 : Blo 1076618 1076927 := bstep (se 1 (by rfl) ⟨807695, by rfl⟩ : syracuseStep 1076927 = 1615391) B1615391
theorem B1077023 : Blo 1076618 1077023 := bstep (se 1 (by rfl) ⟨807767, by rfl⟩ : syracuseStep 1077023 = 1615535) B1615535
theorem B1077083 : Blo 1076618 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B1077103 : Blo 1076618 1077103 := bstep (se 1 (by rfl) ⟨807827, by rfl⟩ : syracuseStep 1077103 = 1615655) B1615655
theorem B1110107 : Blo 1076618 1110107 := bstep (se 1 (by rfl) ⟨832580, by rfl⟩ : syracuseStep 1110107 = 1665161) B1665161
theorem B1077503 : Blo 1076618 1077503 := bstep (se 1 (by rfl) ⟨808127, by rfl⟩ : syracuseStep 1077503 = 1616255) B1616255
theorem B1077663 : Blo 1076618 1077663 := bstep (se 1 (by rfl) ⟨808247, by rfl⟩ : syracuseStep 1077663 = 1616495) B1616495
theorem B1077807 : Blo 1076618 1077807 := bstep (se 1 (by rfl) ⟨808355, by rfl⟩ : syracuseStep 1077807 = 1616711) B1616711
theorem B5468795 : Blo 1076618 5468795 := bstep (se 1 (by rfl) ⟨4101596, by rfl⟩ : syracuseStep 5468795 = 8203193) B8203193
theorem B4092727 : Blo 1076618 4092727 := bstep (se 1 (by rfl) ⟨3069545, by rfl⟩ : syracuseStep 4092727 = 6139091) B6139091
theorem B3633983 : Blo 1076618 3633983 := bstep (se 1 (by rfl) ⟨2725487, by rfl⟩ : syracuseStep 3633983 = 5450975) B5450975
theorem B1078207 : Blo 1076618 1078207 := bstep (se 1 (by rfl) ⟨808655, by rfl⟩ : syracuseStep 1078207 = 1617311) B1617311
theorem B1078383 : Blo 1076618 1078383 := bstep (se 1 (by rfl) ⟨808787, by rfl⟩ : syracuseStep 1078383 = 1617575) B1617575
theorem B1078399 : Blo 1076618 1078399 := bstep (se 1 (by rfl) ⟨808799, by rfl⟩ : syracuseStep 1078399 = 1617599) B1617599
theorem B5174401 : Blo 1076618 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B1078463 : Blo 1076618 1078463 := bstep (se 1 (by rfl) ⟨808847, by rfl⟩ : syracuseStep 1078463 = 1617695) B1617695
theorem B1078655 : Blo 1076618 1078655 := bstep (se 1 (by rfl) ⟨808991, by rfl⟩ : syracuseStep 1078655 = 1617983) B1617983
theorem B1078783 : Blo 1076618 1078783 := bstep (se 1 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 1078783 = 1618175) B1618175
theorem B1078811 : Blo 1076618 1078811 := bstep (se 1 (by rfl) ⟨809108, by rfl⟩ : syracuseStep 1078811 = 1618217) B1618217
theorem B1078991 : Blo 1076618 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B1079151 : Blo 1076618 1079151 := bstep (se 1 (by rfl) ⟨809363, by rfl⟩ : syracuseStep 1079151 = 1618727) B1618727
theorem B1079231 : Blo 1076618 1079231 := bstep (se 1 (by rfl) ⟨809423, by rfl⟩ : syracuseStep 1079231 = 1618847) B1618847
theorem B1538185 : Blo 1076618 1538185 := bstep (se 2 (by rfl) ⟨576819, by rfl⟩ : syracuseStep 1538185 = 1153639) B1153639
theorem B3274987 : Blo 1076618 3274987 := bstep (se 1 (by rfl) ⟨2456240, by rfl⟩ : syracuseStep 3274987 = 4912481) B4912481
theorem B1079547 : Blo 1076618 1079547 := bstep (se 1 (by rfl) ⟨809660, by rfl⟩ : syracuseStep 1079547 = 1619321) B1619321
theorem B1079551 : Blo 1076618 1079551 := bstep (se 1 (by rfl) ⟨809663, by rfl⟩ : syracuseStep 1079551 = 1619327) B1619327
theorem B3635495 : Blo 1076618 3635495 := bstep (se 1 (by rfl) ⟨2726621, by rfl⟩ : syracuseStep 3635495 = 5453243) B5453243
theorem B2423123 : Blo 1076618 2423123 := bstep (se 1 (by rfl) ⟨1817342, by rfl⟩ : syracuseStep 2423123 = 3634685) B3634685
theorem B1079655 : Blo 1076618 1079655 := bstep (se 1 (by rfl) ⟨809741, by rfl⟩ : syracuseStep 1079655 = 1619483) B1619483
theorem B2455967 : Blo 1076618 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B1079775 : Blo 1076618 1079775 := bstep (se 1 (by rfl) ⟨809831, by rfl⟩ : syracuseStep 1079775 = 1619663) B1619663
theorem B1079911 : Blo 1076618 1079911 := bstep (se 1 (by rfl) ⟨809933, by rfl⟩ : syracuseStep 1079911 = 1619867) B1619867
theorem B1079935 : Blo 1076618 1079935 := bstep (se 1 (by rfl) ⟨809951, by rfl⟩ : syracuseStep 1079935 = 1619903) B1619903
theorem B3635873 : Blo 1076618 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B1080047 : Blo 1076618 1080047 := bstep (se 1 (by rfl) ⟨810035, by rfl⟩ : syracuseStep 1080047 = 1620071) B1620071
theorem B1080303 : Blo 1076618 1080303 := bstep (se 1 (by rfl) ⟨810227, by rfl⟩ : syracuseStep 1080303 = 1620455) B1620455
theorem B1080351 : Blo 1076618 1080351 := bstep (se 1 (by rfl) ⟨810263, by rfl⟩ : syracuseStep 1080351 = 1620527) B1620527
theorem B2456659 : Blo 1076618 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B3636737 : Blo 1076618 3636737 := bstep (se 2 (by rfl) ⟨1363776, by rfl⟩ : syracuseStep 3636737 = 2727553) B2727553
theorem B3637547 : Blo 1076618 3637547 := bstep (se 1 (by rfl) ⟨2728160, by rfl⟩ : syracuseStep 3637547 = 5456321) B5456321
theorem B2425211 : Blo 1076618 2425211 := bstep (se 1 (by rfl) ⟨1818908, by rfl⟩ : syracuseStep 2425211 = 3637817) B3637817
theorem B1213159 : Blo 1076618 1213159 := bstep (se 1 (by rfl) ⟨909869, by rfl⟩ : syracuseStep 1213159 = 1819739) B1819739
theorem B2425607 : Blo 1076618 2425607 := bstep (se 1 (by rfl) ⟨1819205, by rfl⟩ : syracuseStep 2425607 = 3638411) B3638411
theorem B3638087 : Blo 1076618 3638087 := bstep (se 1 (by rfl) ⟨2728565, by rfl⟩ : syracuseStep 3638087 = 5457131) B5457131
theorem B1213951 : Blo 1076618 1213951 := bstep (se 1 (by rfl) ⟨910463, by rfl⟩ : syracuseStep 1213951 = 1820927) B1820927
theorem B2427191 : Blo 1076618 2427191 := bstep (se 1 (by rfl) ⟨1820393, by rfl⟩ : syracuseStep 2427191 = 3640787) B3640787
theorem B1215067 : Blo 1076618 1215067 := bstep (se 1 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 1215067 = 1822601) B1822601
theorem B34933943 : Blo 1076618 34933943 := bstep (se 1 (by rfl) ⟨26200457, by rfl⟩ : syracuseStep 34933943 = 52400915) B52400915
theorem B2428217 : Blo 1076618 2428217 := bstep (se 2 (by rfl) ⟨910581, by rfl⟩ : syracuseStep 2428217 = 1821163) B1821163
theorem B2428487 : Blo 1076618 2428487 := bstep (se 1 (by rfl) ⟨1821365, by rfl⟩ : syracuseStep 2428487 = 3642731) B3642731
theorem B5836511 : Blo 1076618 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B31133585 : Blo 1076618 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B2428883 : Blo 1076618 2428883 := bstep (se 1 (by rfl) ⟨1821662, by rfl⟩ : syracuseStep 2428883 = 3643325) B3643325
theorem B3641543 : Blo 1076618 3641543 := bstep (se 1 (by rfl) ⟨2731157, by rfl⟩ : syracuseStep 3641543 = 5462315) B5462315
theorem B2429153 : Blo 1076618 2429153 := bstep (se 2 (by rfl) ⟨910932, by rfl⟩ : syracuseStep 2429153 = 1821865) B1821865
theorem B49812191 : Blo 1076618 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B8196875 : Blo 1076618 8196875 := bstep (se 1 (by rfl) ⟨6147656, by rfl⟩ : syracuseStep 8196875 = 12295313) B12295313
theorem B9213011 : Blo 1076618 9213011 := bstep (se 1 (by rfl) ⟨6909758, by rfl⟩ : syracuseStep 9213011 = 13819517) B13819517
theorem B4920545 : Blo 1076618 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B2430215 : Blo 1076618 2430215 := bstep (se 1 (by rfl) ⟨1822661, by rfl⟩ : syracuseStep 2430215 = 3645323) B3645323
theorem B3282383 : Blo 1076618 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B5838587 : Blo 1076618 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B2430863 : Blo 1076618 2430863 := bstep (se 1 (by rfl) ⟨1823147, by rfl⟩ : syracuseStep 2430863 = 3646295) B3646295
theorem B3643433 : Blo 1076618 3643433 := bstep (se 2 (by rfl) ⟨1366287, by rfl⟩ : syracuseStep 3643433 = 2732575) B2732575
theorem B1349695 : Blo 1076618 1349695 := bstep (se 1 (by rfl) ⟨1012271, by rfl⟩ : syracuseStep 1349695 = 2024543) B2024543
theorem B2726399 : Blo 1076618 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B10361641 : Blo 1076618 10361641 := bstep (se 2 (by rfl) ⟨3885615, by rfl⟩ : syracuseStep 10361641 = 7771231) B7771231
theorem B3644297 : Blo 1076618 3644297 := bstep (se 2 (by rfl) ⟨1366611, by rfl⟩ : syracuseStep 3644297 = 2733223) B2733223
theorem B2727067 : Blo 1076618 2727067 := bstep (se 1 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 2727067 = 4090601) B4090601
theorem B3644729 : Blo 1076618 3644729 := bstep (se 2 (by rfl) ⟨1366773, by rfl⟩ : syracuseStep 3644729 = 2733547) B2733547
theorem B29531567 : Blo 1076618 29531567 := bstep (se 1 (by rfl) ⟨22148675, by rfl⟩ : syracuseStep 29531567 = 44297351) B44297351
theorem B6135425 : Blo 1076618 6135425 := bstep (se 2 (by rfl) ⟨2300784, by rfl⟩ : syracuseStep 6135425 = 4601569) B4601569
theorem B40509391 : Blo 1076618 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B2302015 : Blo 1076618 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B4366649 : Blo 1076618 4366649 := bstep (se 2 (by rfl) ⟨1637493, by rfl⟩ : syracuseStep 4366649 = 3274987) B3274987
theorem B3645863 : Blo 1076618 3645863 := bstep (se 1 (by rfl) ⟨2734397, by rfl⟩ : syracuseStep 3645863 = 5468795) B5468795
theorem B5251625 : Blo 1076618 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B2302843 : Blo 1076618 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B44966839 : Blo 1076618 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B4990265 : Blo 1076618 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B1615415 : Blo 1076618 1615415 := bstep (se 1 (by rfl) ⟨1211561, by rfl⟩ : syracuseStep 1615415 = 2423123) B2423123
theorem B12298229 : Blo 1076618 12298229 := bstep (se 5 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 12298229 = 1152959) B1152959
theorem B23341121 : Blo 1076618 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B2730145 : Blo 1076618 2730145 := bstep (se 2 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 2730145 = 2047609) B2047609
theorem B6138089 : Blo 1076618 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B1616681 : Blo 1076618 1616681 := bstep (se 2 (by rfl) ⟨606255, by rfl⟩ : syracuseStep 1616681 = 1212511) B1212511
theorem B2960285 : Blo 1076618 2960285 := bstep (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) B1110107
theorem B1616987 : Blo 1076618 1616987 := bstep (se 1 (by rfl) ⟨1212740, by rfl⟩ : syracuseStep 1616987 = 2425481) B2425481
theorem B27634931 : Blo 1076618 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B1945129 : Blo 1076618 1945129 := bstep (se 2 (by rfl) ⟨729423, by rfl⟩ : syracuseStep 1945129 = 1458847) B1458847
theorem B1617455 : Blo 1076618 1617455 := bstep (se 1 (by rfl) ⟨1213091, by rfl⟩ : syracuseStep 1617455 = 2426183) B2426183
theorem B4599929 : Blo 1076618 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B12464875 : Blo 1076618 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B23311097 : Blo 1076618 23311097 := bstep (se 2 (by rfl) ⟨8741661, by rfl⟩ : syracuseStep 23311097 = 17483323) B17483323
theorem B3453779 : Blo 1076618 3453779 := bstep (se 1 (by rfl) ⟨2590334, by rfl⟩ : syracuseStep 3453779 = 5180669) B5180669
theorem B9352091 : Blo 1076618 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B2733659 : Blo 1076618 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B1619561 : Blo 1076618 1619561 := bstep (se 2 (by rfl) ⟨607335, by rfl⟩ : syracuseStep 1619561 = 1214671) B1214671
theorem B4437631 : Blo 1076618 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B1619783 : Blo 1076618 1619783 := bstep (se 1 (by rfl) ⟨1214837, by rfl⟩ : syracuseStep 1619783 = 2429675) B2429675
theorem B2733983 : Blo 1076618 2733983 := bstep (se 1 (by rfl) ⟨2050487, by rfl⟩ : syracuseStep 2733983 = 4100975) B4100975
theorem B1620023 : Blo 1076618 1620023 := bstep (se 1 (by rfl) ⟨1215017, by rfl⟩ : syracuseStep 1620023 = 2430035) B2430035
theorem B1620095 : Blo 1076618 1620095 := bstep (se 1 (by rfl) ⟨1215071, by rfl⟩ : syracuseStep 1620095 = 2430143) B2430143
theorem B2079211 : Blo 1076618 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B5454377 : Blo 1076618 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B5454539 : Blo 1076618 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B12270527 : Blo 1076618 12270527 := bstep (se 1 (by rfl) ⟨9202895, by rfl⟩ : syracuseStep 12270527 = 18405791) B18405791
theorem B1817977 : Blo 1076618 1817977 := bstep (se 2 (by rfl) ⟨681741, by rfl⟩ : syracuseStep 1817977 = 1363483) B1363483
theorem B6143465 : Blo 1076618 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B1458047 : Blo 1076618 1458047 := bstep (se 1 (by rfl) ⟨1093535, by rfl⟩ : syracuseStep 1458047 = 2187071) B2187071
theorem B1818679 : Blo 1076618 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B1294427 : Blo 1076618 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B5455997 : Blo 1076618 5455997 := bstep (se 3 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 5455997 = 2045999) B2045999
theorem B1229639 : Blo 1076618 1229639 := bstep (se 1 (by rfl) ⟨922229, by rfl⟩ : syracuseStep 1229639 = 1844459) B1844459
theorem B5456969 : Blo 1076618 5456969 := bstep (se 2 (by rfl) ⟨2046363, by rfl⟩ : syracuseStep 5456969 = 4092727) B4092727
theorem B12305519 : Blo 1076618 12305519 := bstep (se 1 (by rfl) ⟨9229139, by rfl⟩ : syracuseStep 12305519 = 18458279) B18458279
theorem B1819975 : Blo 1076618 1819975 := bstep (se 1 (by rfl) ⟨1364981, by rfl⟩ : syracuseStep 1819975 = 2729963) B2729963
theorem B6899201 : Blo 1076618 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B22169209 : Blo 1076618 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B9357275 : Blo 1076618 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B1362683 : Blo 1076618 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B2050913 : Blo 1076618 2050913 := bstep (se 2 (by rfl) ⟨769092, by rfl⟩ : syracuseStep 2050913 = 1538185) B1538185
theorem B4607225 : Blo 1076618 4607225 := bstep (se 2 (by rfl) ⟨1727709, by rfl⟩ : syracuseStep 4607225 = 3455419) B3455419
theorem B1363711 : Blo 1076618 1363711 := bstep (se 1 (by rfl) ⟨1022783, by rfl⟩ : syracuseStep 1363711 = 2045567) B2045567
theorem B3067895 : Blo 1076618 3067895 := bstep (se 1 (by rfl) ⟨2300921, by rfl⟩ : syracuseStep 3067895 = 4601843) B4601843
theorem B1364303 : Blo 1076618 1364303 := bstep (se 1 (by rfl) ⟨1023227, by rfl⟩ : syracuseStep 1364303 = 2046455) B2046455
theorem B1823323 : Blo 1076618 1823323 := bstep (se 1 (by rfl) ⟨1367492, by rfl⟩ : syracuseStep 1823323 = 2734985) B2734985
theorem B29874107 : Blo 1076618 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B5462153 : Blo 1076618 5462153 := bstep (se 2 (by rfl) ⟨2048307, by rfl⟩ : syracuseStep 5462153 = 4096615) B4096615
theorem B19650863 : Blo 1076618 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B26958253 : Blo 1076618 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B8182781 : Blo 1076618 8182781 := bstep (se 3 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 8182781 = 3068543) B3068543
theorem B1727543 : Blo 1076618 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B12279275 : Blo 1076618 12279275 := bstep (se 1 (by rfl) ⟨9209456, by rfl⟩ : syracuseStep 12279275 = 18418913) B18418913
theorem B3072143 : Blo 1076618 3072143 := bstep (se 1 (by rfl) ⟨2304107, by rfl⟩ : syracuseStep 3072143 = 4608215) B4608215
theorem B19687283 : Blo 1076618 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B13102181 : Blo 1076618 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B4091087 : Blo 1076618 4091087 := bstep (se 1 (by rfl) ⟨3068315, by rfl⟩ : syracuseStep 4091087 = 6136631) B6136631
theorem B20770181 : Blo 1076618 20770181 := bstep (se 4 (by rfl) ⟨1947204, by rfl⟩ : syracuseStep 20770181 = 3894409) B3894409
theorem B1076639 : Blo 1076618 1076639 := bstep (se 1 (by rfl) ⟨807479, by rfl⟩ : syracuseStep 1076639 = 1614959) B1614959
theorem B4615649 : Blo 1076618 4615649 := bstep (se 2 (by rfl) ⟨1730868, by rfl⟩ : syracuseStep 4615649 = 3461737) B3461737
theorem B1076719 : Blo 1076618 1076719 := bstep (se 1 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 1076719 = 1615079) B1615079
theorem B1076763 : Blo 1076618 1076763 := bstep (se 1 (by rfl) ⟨807572, by rfl⟩ : syracuseStep 1076763 = 1615145) B1615145
theorem B6549245 : Blo 1076618 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B6221933 : Blo 1076618 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1077531 : Blo 1076618 1077531 := bstep (se 1 (by rfl) ⟨808148, by rfl⟩ : syracuseStep 1077531 = 1616297) B1616297
theorem B1077887 : Blo 1076618 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B4092713 : Blo 1076618 4092713 := bstep (se 2 (by rfl) ⟨1534767, by rfl⟩ : syracuseStep 4092713 = 3069535) B3069535
theorem B1536823 : Blo 1076618 1536823 := bstep (se 1 (by rfl) ⟨1152617, by rfl⟩ : syracuseStep 1536823 = 2305235) B2305235
theorem B1537051 : Blo 1076618 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B7762985 : Blo 1076618 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B1078375 : Blo 1076618 1078375 := bstep (se 1 (by rfl) ⟨808781, by rfl⟩ : syracuseStep 1078375 = 1617563) B1617563
theorem B12285107 : Blo 1076618 12285107 := bstep (se 1 (by rfl) ⟨9213830, by rfl⟩ : syracuseStep 12285107 = 18427661) B18427661
theorem B1078631 : Blo 1076618 1078631 := bstep (se 1 (by rfl) ⟨808973, by rfl⟩ : syracuseStep 1078631 = 1617947) B1617947
theorem B1078911 : Blo 1076618 1078911 := bstep (se 1 (by rfl) ⟨809183, by rfl⟩ : syracuseStep 1078911 = 1618367) B1618367
theorem B1079143 : Blo 1076618 1079143 := bstep (se 1 (by rfl) ⟨809357, by rfl⟩ : syracuseStep 1079143 = 1618715) B1618715
theorem B2422655 : Blo 1076618 2422655 := bstep (se 1 (by rfl) ⟨1816991, by rfl⟩ : syracuseStep 2422655 = 3633983) B3633983
theorem B5470091 : Blo 1076618 5470091 := bstep (se 1 (by rfl) ⟨4102568, by rfl⟩ : syracuseStep 5470091 = 8205137) B8205137
theorem B340621469 : Blo 1076618 340621469 := bstep (se 3 (by rfl) ⟨63866525, by rfl⟩ : syracuseStep 340621469 = 127733051) B127733051
theorem B2423609 : Blo 1076618 2423609 := bstep (se 2 (by rfl) ⟨908853, by rfl⟩ : syracuseStep 2423609 = 1817707) B1817707
theorem B1080127 : Blo 1076618 1080127 := bstep (se 1 (by rfl) ⟨810095, by rfl⟩ : syracuseStep 1080127 = 1620191) B1620191
theorem B1080167 : Blo 1076618 1080167 := bstep (se 1 (by rfl) ⟨810125, by rfl⟩ : syracuseStep 1080167 = 1620251) B1620251
theorem B2423663 : Blo 1076618 2423663 := bstep (se 1 (by rfl) ⟨1817747, by rfl⟩ : syracuseStep 2423663 = 3635495) B3635495
theorem B1080191 : Blo 1076618 1080191 := bstep (se 1 (by rfl) ⟨810143, by rfl⟩ : syracuseStep 1080191 = 1620287) B1620287
theorem B9206723 : Blo 1076618 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B7371785 : Blo 1076618 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B2423915 : Blo 1076618 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B1080447 : Blo 1076618 1080447 := bstep (se 1 (by rfl) ⟨810335, by rfl⟩ : syracuseStep 1080447 = 1620671) B1620671
theorem B291733073 : Blo 1076618 291733073 := bstep (se 2 (by rfl) ⟨109399902, by rfl⟩ : syracuseStep 291733073 = 218799805) B218799805
theorem B2424491 : Blo 1076618 2424491 := bstep (se 1 (by rfl) ⟨1818368, by rfl⟩ : syracuseStep 2424491 = 3636737) B3636737
theorem B2424905 : Blo 1076618 2424905 := bstep (se 2 (by rfl) ⟨909339, by rfl⟩ : syracuseStep 2424905 = 1818679) B1818679
theorem B3637331 : Blo 1076618 3637331 := bstep (se 1 (by rfl) ⟨2727998, by rfl⟩ : syracuseStep 3637331 = 5455997) B5455997
theorem B2425031 : Blo 1076618 2425031 := bstep (se 1 (by rfl) ⟨1818773, by rfl⟩ : syracuseStep 2425031 = 3637547) B3637547
theorem B2425391 : Blo 1076618 2425391 := bstep (se 1 (by rfl) ⟨1819043, by rfl⟩ : syracuseStep 2425391 = 3638087) B3638087
theorem B3637979 : Blo 1076618 3637979 := bstep (se 1 (by rfl) ⟨2728484, by rfl⟩ : syracuseStep 3637979 = 5456969) B5456969
theorem B3638141 : Blo 1076618 3638141 := bstep (se 3 (by rfl) ⟨682151, by rfl⟩ : syracuseStep 3638141 = 1364303) B1364303
theorem B2426633 : Blo 1076618 2426633 := bstep (se 2 (by rfl) ⟨909987, by rfl⟩ : syracuseStep 2426633 = 1819975) B1819975
theorem B29558945 : Blo 1076618 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B3279037 : Blo 1076618 3279037 := bstep (se 3 (by rfl) ⟨614819, by rfl⟩ : syracuseStep 3279037 = 1229639) B1229639
theorem B2427695 : Blo 1076618 2427695 := bstep (se 1 (by rfl) ⟨1820771, by rfl⟩ : syracuseStep 2427695 = 3641543) B3641543
theorem B3640193 : Blo 1076618 3640193 := bstep (se 2 (by rfl) ⟨1365072, by rfl⟩ : syracuseStep 3640193 = 2730145) B2730145
theorem B2428955 : Blo 1076618 2428955 := bstep (se 1 (by rfl) ⟨1821716, by rfl⟩ : syracuseStep 2428955 = 3643433) B3643433
theorem B3641435 : Blo 1076618 3641435 := bstep (se 1 (by rfl) ⟨2731076, by rfl⟩ : syracuseStep 3641435 = 5462153) B5462153
theorem B8196389 : Blo 1076618 8196389 := bstep (se 4 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 8196389 = 1536823) B1536823
theorem B2429531 : Blo 1076618 2429531 := bstep (se 1 (by rfl) ⟨1822148, by rfl⟩ : syracuseStep 2429531 = 3644297) B3644297
theorem B1151695 : Blo 1076618 1151695 := bstep (se 1 (by rfl) ⟨863771, by rfl⟩ : syracuseStep 1151695 = 1727543) B1727543
theorem B2593505 : Blo 1076618 2593505 := bstep (se 2 (by rfl) ⟨972564, by rfl⟩ : syracuseStep 2593505 = 1945129) B1945129
theorem B2429819 : Blo 1076618 2429819 := bstep (se 1 (by rfl) ⟨1822364, by rfl⟩ : syracuseStep 2429819 = 3644729) B3644729
theorem B79664285 : Blo 1076618 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B2430575 : Blo 1076618 2430575 := bstep (se 1 (by rfl) ⟨1822931, by rfl⟩ : syracuseStep 2430575 = 3645863) B3645863
theorem B2431097 : Blo 1076618 2431097 := bstep (se 2 (by rfl) ⟨911661, by rfl⟩ : syracuseStep 2431097 = 1823323) B1823323
theorem B16619833 : Blo 1076618 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B8198819 : Blo 1076618 8198819 := bstep (se 1 (by rfl) ⟨6149114, by rfl⟩ : syracuseStep 8198819 = 12298229) B12298229
theorem B2727391 : Blo 1076618 2727391 := bstep (se 1 (by rfl) ⟨2045543, by rfl⟩ : syracuseStep 2727391 = 4091087) B4091087
theorem B18423287 : Blo 1076618 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B4366163 : Blo 1076618 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B15540731 : Blo 1076618 15540731 := bstep (se 1 (by rfl) ⟨11655548, by rfl⟩ : syracuseStep 15540731 = 23311097) B23311097
theorem B2728475 : Blo 1076618 2728475 := bstep (se 1 (by rfl) ⟨2046356, by rfl⟩ : syracuseStep 2728475 = 4092713) B4092713
theorem B2302519 : Blo 1076618 2302519 := bstep (se 1 (by rfl) ⟨1726889, by rfl⟩ : syracuseStep 2302519 = 3453779) B3453779
theorem B6234727 : Blo 1076618 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B23667365 : Blo 1076618 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B1615103 : Blo 1076618 1615103 := bstep (se 1 (by rfl) ⟨1211327, by rfl⟩ : syracuseStep 1615103 = 2422655) B2422655
theorem B3646727 : Blo 1076618 3646727 := bstep (se 1 (by rfl) ⟨2735045, by rfl⟩ : syracuseStep 3646727 = 5470091) B5470091
theorem B1615739 : Blo 1076618 1615739 := bstep (se 1 (by rfl) ⟨1211804, by rfl⟩ : syracuseStep 1615739 = 2423609) B2423609
theorem B1615775 : Blo 1076618 1615775 := bstep (se 1 (by rfl) ⟨1211831, by rfl⟩ : syracuseStep 1615775 = 2423663) B2423663
theorem B6137815 : Blo 1076618 6137815 := bstep (se 1 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 6137815 = 9206723) B9206723
theorem B1615943 : Blo 1076618 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B194488715 : Blo 1076618 194488715 := bstep (se 1 (by rfl) ⟨145866536, by rfl⟩ : syracuseStep 194488715 = 291733073) B291733073
theorem B1616327 : Blo 1076618 1616327 := bstep (se 1 (by rfl) ⟨1212245, by rfl⟩ : syracuseStep 1616327 = 2424491) B2424491
theorem B54012521 : Blo 1076618 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B3451805 : Blo 1076618 3451805 := bstep (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) B1294427
theorem B1616807 : Blo 1076618 1616807 := bstep (se 1 (by rfl) ⟨1212605, by rfl⟩ : syracuseStep 1616807 = 2425211) B2425211
theorem B1617071 : Blo 1076618 1617071 := bstep (se 1 (by rfl) ⟨1212803, by rfl⟩ : syracuseStep 1617071 = 2425607) B2425607
theorem B8203679 : Blo 1076618 8203679 := bstep (se 1 (by rfl) ⟨6152759, by rfl⟩ : syracuseStep 8203679 = 12305519) B12305519
theorem B1617545 : Blo 1076618 1617545 := bstep (se 2 (by rfl) ⟨606579, by rfl⟩ : syracuseStep 1617545 = 1213159) B1213159
theorem B4599467 : Blo 1076618 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B6238183 : Blo 1076618 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B1618127 : Blo 1076618 1618127 := bstep (se 1 (by rfl) ⟨1213595, by rfl⟩ : syracuseStep 1618127 = 2427191) B2427191
theorem B1618601 : Blo 1076618 1618601 := bstep (se 2 (by rfl) ⟨606975, by rfl⟩ : syracuseStep 1618601 = 1213951) B1213951
theorem B1618811 : Blo 1076618 1618811 := bstep (se 1 (by rfl) ⟨1214108, by rfl⟩ : syracuseStep 1618811 = 2428217) B2428217
theorem B1618991 : Blo 1076618 1618991 := bstep (se 1 (by rfl) ⟨1214243, by rfl⟩ : syracuseStep 1618991 = 2428487) B2428487
theorem B20755723 : Blo 1076618 20755723 := bstep (se 1 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 20755723 = 31133585) B31133585
theorem B1619255 : Blo 1076618 1619255 := bstep (se 1 (by rfl) ⟨1214441, by rfl⟩ : syracuseStep 1619255 = 2428883) B2428883
theorem B2045263 : Blo 1076618 2045263 := bstep (se 1 (by rfl) ⟨1533947, by rfl⟩ : syracuseStep 2045263 = 3067895) B3067895
theorem B1619435 : Blo 1076618 1619435 := bstep (se 1 (by rfl) ⟨1214576, by rfl⟩ : syracuseStep 1619435 = 2429153) B2429153
theorem B33208127 : Blo 1076618 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B13121453 : Blo 1076618 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B6142007 : Blo 1076618 6142007 := bstep (se 1 (by rfl) ⟨4606505, by rfl⟩ : syracuseStep 6142007 = 9213011) B9213011
theorem B1620089 : Blo 1076618 1620089 := bstep (se 2 (by rfl) ⟨607533, by rfl⟩ : syracuseStep 1620089 = 1215067) B1215067
theorem B1620143 : Blo 1076618 1620143 := bstep (se 1 (by rfl) ⟨1215107, by rfl⟩ : syracuseStep 1620143 = 2430215) B2430215
theorem B1620575 : Blo 1076618 1620575 := bstep (se 1 (by rfl) ⟨1215431, by rfl⟩ : syracuseStep 1620575 = 2430863) B2430863
theorem B1817599 : Blo 1076618 1817599 := bstep (se 1 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 1817599 = 2726399) B2726399
theorem B5455187 : Blo 1076618 5455187 := bstep (se 1 (by rfl) ⟨4091390, by rfl⟩ : syracuseStep 5455187 = 8182781) B8182781
theorem B1818281 : Blo 1076618 1818281 := bstep (se 2 (by rfl) ⟨681855, by rfl⟩ : syracuseStep 1818281 = 1363711) B1363711
theorem B2048095 : Blo 1076618 2048095 := bstep (se 1 (by rfl) ⟨1536071, by rfl⟩ : syracuseStep 2048095 = 3072143) B3072143
theorem B3326843 : Blo 1076618 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B13124855 : Blo 1076618 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B2049401 : Blo 1076618 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B8734787 : Blo 1076618 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B13846787 : Blo 1076618 13846787 := bstep (se 1 (by rfl) ⟨10385090, by rfl⟩ : syracuseStep 13846787 = 20770181) B20770181
theorem B4147955 : Blo 1076618 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B3066619 : Blo 1076618 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B2772281 : Blo 1076618 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B13815521 : Blo 1076618 13815521 := bstep (se 2 (by rfl) ⟨5180820, by rfl⟩ : syracuseStep 13815521 = 10361641) B10361641
theorem B1822439 : Blo 1076618 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B1822655 : Blo 1076618 1822655 := bstep (se 1 (by rfl) ⟨1366991, by rfl⟩ : syracuseStep 1822655 = 2733983) B2733983
theorem B8180351 : Blo 1076618 8180351 := bstep (se 1 (by rfl) ⟨6135263, by rfl⟩ : syracuseStep 8180351 = 12270527) B12270527
theorem B3888125 : Blo 1076618 3888125 := bstep (se 3 (by rfl) ⟨729023, by rfl⟩ : syracuseStep 3888125 = 1458047) B1458047
theorem B3069353 : Blo 1076618 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B7198373 : Blo 1076618 7198373 := bstep (se 4 (by rfl) ⟨674847, by rfl⟩ : syracuseStep 7198373 = 1349695) B1349695
theorem B3070457 : Blo 1076618 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B59955785 : Blo 1076618 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B1367275 : Blo 1076618 1367275 := bstep (se 1 (by rfl) ⟨1025456, by rfl⟩ : syracuseStep 1367275 = 2050913) B2050913
theorem B23289295 : Blo 1076618 23289295 := bstep (se 1 (by rfl) ⟨17466971, by rfl⟩ : syracuseStep 23289295 = 34933943) B34933943
theorem B3071483 : Blo 1076618 3071483 := bstep (se 1 (by rfl) ⟨2303612, by rfl⟩ : syracuseStep 3071483 = 4607225) B4607225
theorem B3891007 : Blo 1076618 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B5464583 : Blo 1076618 5464583 := bstep (se 1 (by rfl) ⟨4098437, by rfl⟩ : syracuseStep 5464583 = 8196875) B8196875
theorem B2188255 : Blo 1076618 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B3892391 : Blo 1076618 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B13100575 : Blo 1076618 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B19687711 : Blo 1076618 19687711 := bstep (se 1 (by rfl) ⟨14765783, by rfl⟩ : syracuseStep 19687711 = 29531567) B29531567
theorem B8186183 : Blo 1076618 8186183 := bstep (se 1 (by rfl) ⟨6139637, by rfl⟩ : syracuseStep 8186183 = 12279275) B12279275
theorem B4090283 : Blo 1076618 4090283 := bstep (se 1 (by rfl) ⟨3067712, by rfl⟩ : syracuseStep 4090283 = 6135425) B6135425
theorem B2911099 : Blo 1076618 2911099 := bstep (se 1 (by rfl) ⟨2183324, by rfl⟩ : syracuseStep 2911099 = 4366649) B4366649
theorem B3501083 : Blo 1076618 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B1076943 : Blo 1076618 1076943 := bstep (se 1 (by rfl) ⟨807707, by rfl⟩ : syracuseStep 1076943 = 1615415) B1615415
theorem B15560747 : Blo 1076618 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B4092059 : Blo 1076618 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B1077787 : Blo 1076618 1077787 := bstep (se 1 (by rfl) ⟨808340, by rfl⟩ : syracuseStep 1077787 = 1616681) B1616681
theorem B3633821 : Blo 1076618 3633821 := bstep (se 3 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 3633821 = 1362683) B1362683
theorem B1077991 : Blo 1076618 1077991 := bstep (se 1 (by rfl) ⟨808493, by rfl⟩ : syracuseStep 1077991 = 1616987) B1616987
theorem B3077099 : Blo 1076618 3077099 := bstep (se 1 (by rfl) ⟨2307824, by rfl⟩ : syracuseStep 3077099 = 4615649) B4615649
theorem B1078303 : Blo 1076618 1078303 := bstep (se 1 (by rfl) ⟨808727, by rfl⟩ : syracuseStep 1078303 = 1617455) B1617455
theorem B7894093 : Blo 1076618 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B35944337 : Blo 1076618 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B5175323 : Blo 1076618 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B8190071 : Blo 1076618 8190071 := bstep (se 1 (by rfl) ⟨6142553, by rfl⟩ : syracuseStep 8190071 = 12285107) B12285107
theorem B1079707 : Blo 1076618 1079707 := bstep (se 1 (by rfl) ⟨809780, by rfl⟩ : syracuseStep 1079707 = 1619561) B1619561
theorem B1079855 : Blo 1076618 1079855 := bstep (se 1 (by rfl) ⟨809891, by rfl⟩ : syracuseStep 1079855 = 1619783) B1619783
theorem B1080015 : Blo 1076618 1080015 := bstep (se 1 (by rfl) ⟨810011, by rfl⟩ : syracuseStep 1080015 = 1620023) B1620023
theorem B1080063 : Blo 1076618 1080063 := bstep (se 1 (by rfl) ⟨810047, by rfl⟩ : syracuseStep 1080063 = 1620095) B1620095
theorem B227080979 : Blo 1076618 227080979 := bstep (se 1 (by rfl) ⟨170310734, by rfl⟩ : syracuseStep 227080979 = 340621469) B340621469
theorem B3636089 : Blo 1076618 3636089 := bstep (se 2 (by rfl) ⟨1363533, by rfl⟩ : syracuseStep 3636089 = 2727067) B2727067
theorem B3636251 : Blo 1076618 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B3636359 : Blo 1076618 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B2423969 : Blo 1076618 2423969 := bstep (se 2 (by rfl) ⟨908988, by rfl⟩ : syracuseStep 2423969 = 1817977) B1817977
theorem B4914523 : Blo 1076618 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B4095643 : Blo 1076618 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B2424887 : Blo 1076618 2424887 := bstep (se 1 (by rfl) ⟨1818665, by rfl⟩ : syracuseStep 2424887 = 3637331) B3637331
theorem B2425319 : Blo 1076618 2425319 := bstep (se 1 (by rfl) ⟨1818989, by rfl⟩ : syracuseStep 2425319 = 3637979) B3637979
theorem B2425427 : Blo 1076618 2425427 := bstep (se 1 (by rfl) ⟨1819070, by rfl⟩ : syracuseStep 2425427 = 3638141) B3638141
theorem B8749903 : Blo 1076618 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B2917673 : Blo 1076618 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B2426795 : Blo 1076618 2426795 := bstep (se 1 (by rfl) ⟨1820096, by rfl⟩ : syracuseStep 2426795 = 3640193) B3640193
theorem B6916013 : Blo 1076618 6916013 := bstep (se 3 (by rfl) ⟨1296752, by rfl⟩ : syracuseStep 6916013 = 2593505) B2593505
theorem B17467433 : Blo 1076618 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B9210347 : Blo 1076618 9210347 := bstep (se 1 (by rfl) ⟨6907760, by rfl⟩ : syracuseStep 9210347 = 13815521) B13815521
theorem B1214959 : Blo 1076618 1214959 := bstep (se 1 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 1214959 = 1822439) B1822439
theorem B1215103 : Blo 1076618 1215103 := bstep (se 1 (by rfl) ⟨911327, by rfl⟩ : syracuseStep 1215103 = 1822655) B1822655
theorem B2427623 : Blo 1076618 2427623 := bstep (se 1 (by rfl) ⟨1820717, by rfl⟩ : syracuseStep 2427623 = 3641435) B3641435
theorem B26250281 : Blo 1076618 26250281 := bstep (se 2 (by rfl) ⟨9843855, by rfl⟩ : syracuseStep 26250281 = 19687711) B19687711
theorem B2592083 : Blo 1076618 2592083 := bstep (se 1 (by rfl) ⟨1944062, by rfl⟩ : syracuseStep 2592083 = 3888125) B3888125
theorem B95851565 : Blo 1076618 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B10360487 : Blo 1076618 10360487 := bstep (se 1 (by rfl) ⟨7770365, by rfl⟩ : syracuseStep 10360487 = 15540731) B15540731
theorem B3643055 : Blo 1076618 3643055 := bstep (se 1 (by rfl) ⟨2732291, by rfl⟩ : syracuseStep 3643055 = 5464583) B5464583
theorem B2594927 : Blo 1076618 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B2431151 : Blo 1076618 2431151 := bstep (se 1 (by rfl) ⟨1823363, by rfl⟩ : syracuseStep 2431151 = 3646727) B3646727
theorem B10525457 : Blo 1076618 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B2726855 : Blo 1076618 2726855 := bstep (se 1 (by rfl) ⟨2045141, by rfl⟩ : syracuseStep 2726855 = 4090283) B4090283
theorem B2727017 : Blo 1076618 2727017 := bstep (se 2 (by rfl) ⟨1022631, by rfl⟩ : syracuseStep 2727017 = 2045263) B2045263
theorem B2301203 : Blo 1076618 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B2728039 : Blo 1076618 2728039 := bstep (se 1 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 2728039 = 4092059) B4092059
theorem B22159777 : Blo 1076618 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B3450215 : Blo 1076618 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B1615979 : Blo 1076618 1615979 := bstep (se 1 (by rfl) ⟨1211984, by rfl⟩ : syracuseStep 1615979 = 2423969) B2423969
theorem B5188009 : Blo 1076618 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B1616603 : Blo 1076618 1616603 := bstep (se 1 (by rfl) ⟨1212452, by rfl⟩ : syracuseStep 1616603 = 2424905) B2424905
theorem B2730793 : Blo 1076618 2730793 := bstep (se 2 (by rfl) ⟨1024047, by rfl⟩ : syracuseStep 2730793 = 2048095) B2048095
theorem B1616687 : Blo 1076618 1616687 := bstep (se 1 (by rfl) ⟨1212515, by rfl⟩ : syracuseStep 1616687 = 2425031) B2425031
theorem B1616927 : Blo 1076618 1616927 := bstep (se 1 (by rfl) ⟨1212695, by rfl⟩ : syracuseStep 1616927 = 2425391) B2425391
theorem B1617755 : Blo 1076618 1617755 := bstep (se 1 (by rfl) ⟨1213316, by rfl⟩ : syracuseStep 1617755 = 2426633) B2426633
theorem B2765303 : Blo 1076618 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B1618463 : Blo 1076618 1618463 := bstep (se 1 (by rfl) ⟨1213847, by rfl⟩ : syracuseStep 1618463 = 2427695) B2427695
theorem B1848187 : Blo 1076618 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B1619303 : Blo 1076618 1619303 := bstep (se 1 (by rfl) ⟨1214477, by rfl⟩ : syracuseStep 1619303 = 2428955) B2428955
theorem B4372049 : Blo 1076618 4372049 := bstep (se 2 (by rfl) ⟨1639518, by rfl⟩ : syracuseStep 4372049 = 3279037) B3279037
theorem B1619687 : Blo 1076618 1619687 := bstep (se 1 (by rfl) ⟨1214765, by rfl⟩ : syracuseStep 1619687 = 2429531) B2429531
theorem B5453567 : Blo 1076618 5453567 := bstep (se 1 (by rfl) ⟨4090175, by rfl⟩ : syracuseStep 5453567 = 8180351) B8180351
theorem B1619879 : Blo 1076618 1619879 := bstep (se 1 (by rfl) ⟨1214909, by rfl⟩ : syracuseStep 1619879 = 2429819) B2429819
theorem B2046235 : Blo 1076618 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B1620383 : Blo 1076618 1620383 := bstep (se 1 (by rfl) ⟨1215287, by rfl⟩ : syracuseStep 1620383 = 2430575) B2430575
theorem B3881465 : Blo 1076618 3881465 := bstep (se 2 (by rfl) ⟨1455549, by rfl⟩ : syracuseStep 3881465 = 2911099) B2911099
theorem B1620731 : Blo 1076618 1620731 := bstep (se 1 (by rfl) ⟨1215548, by rfl⟩ : syracuseStep 1620731 = 2431097) B2431097
theorem B2046971 : Blo 1076618 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B2047655 : Blo 1076618 2047655 := bstep (se 1 (by rfl) ⟨1535741, by rfl⟩ : syracuseStep 2047655 = 3071483) B3071483
theorem B1818983 : Blo 1076618 1818983 := bstep (se 1 (by rfl) ⟨1364237, by rfl⟩ : syracuseStep 1818983 = 2728475) B2728475
theorem B78823853 : Blo 1076618 78823853 := bstep (se 3 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 78823853 = 29558945) B29558945
theorem B15778243 : Blo 1076618 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B5457455 : Blo 1076618 5457455 := bstep (se 1 (by rfl) ⟨4093091, by rfl⟩ : syracuseStep 5457455 = 8186183) B8186183
theorem B27674297 : Blo 1076618 27674297 := bstep (se 2 (by rfl) ⟨10377861, by rfl⟩ : syracuseStep 27674297 = 20755723) B20755723
theorem B3066311 : Blo 1076618 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B10373831 : Blo 1076618 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B2051399 : Blo 1076618 2051399 := bstep (se 1 (by rfl) ⟨1538549, by rfl⟩ : syracuseStep 2051399 = 3077099) B3077099
theorem B22138751 : Blo 1076618 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B5460047 : Blo 1076618 5460047 := bstep (se 1 (by rfl) ⟨4095035, by rfl⟩ : syracuseStep 5460047 = 8190071) B8190071
theorem B1823033 : Blo 1076618 1823033 := bstep (se 2 (by rfl) ⟨683637, by rfl⟩ : syracuseStep 1823033 = 1367275) B1367275
theorem B31052393 : Blo 1076618 31052393 := bstep (se 2 (by rfl) ⟨11644647, by rfl⟩ : syracuseStep 31052393 = 23289295) B23289295
theorem B5460857 : Blo 1076618 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B3070025 : Blo 1076618 3070025 := bstep (se 2 (by rfl) ⟨1151259, by rfl⟩ : syracuseStep 3070025 = 2302519) B2302519
theorem B8312969 : Blo 1076618 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B5823191 : Blo 1076618 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B9231191 : Blo 1076618 9231191 := bstep (se 1 (by rfl) ⟨6923393, by rfl⟩ : syracuseStep 9231191 = 13846787) B13846787
theorem B8871581 : Blo 1076618 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B8183753 : Blo 1076618 8183753 := bstep (se 2 (by rfl) ⟨3068907, by rfl⟩ : syracuseStep 8183753 = 6137815) B6137815
theorem B5464259 : Blo 1076618 5464259 := bstep (se 1 (by rfl) ⟨4098194, by rfl⟩ : syracuseStep 5464259 = 8196389) B8196389
theorem B53109523 : Blo 1076618 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B5465069 : Blo 1076618 5465069 := bstep (se 3 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 5465069 = 2049401) B2049401
theorem B4088825 : Blo 1076618 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B39970523 : Blo 1076618 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B19195661 : Blo 1076618 19195661 := bstep (se 3 (by rfl) ⟨3599186, by rfl⟩ : syracuseStep 19195661 = 7198373) B7198373
theorem B5465879 : Blo 1076618 5465879 := bstep (se 1 (by rfl) ⟨4099409, by rfl⟩ : syracuseStep 5465879 = 8198819) B8198819
theorem B12282191 : Blo 1076618 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B2910775 : Blo 1076618 2910775 := bstep (se 1 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 2910775 = 4366163) B4366163
theorem B8317577 : Blo 1076618 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B1076735 : Blo 1076618 1076735 := bstep (se 1 (by rfl) ⟨807551, by rfl⟩ : syracuseStep 1076735 = 1615103) B1615103
theorem B1535593 : Blo 1076618 1535593 := bstep (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) B1151695
theorem B1077159 : Blo 1076618 1077159 := bstep (se 1 (by rfl) ⟨807869, by rfl⟩ : syracuseStep 1077159 = 1615739) B1615739
theorem B1077183 : Blo 1076618 1077183 := bstep (se 1 (by rfl) ⟨807887, by rfl⟩ : syracuseStep 1077183 = 1615775) B1615775
theorem B1077295 : Blo 1076618 1077295 := bstep (se 1 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 1077295 = 1615943) B1615943
theorem B129659143 : Blo 1076618 129659143 := bstep (se 1 (by rfl) ⟨97244357, by rfl⟩ : syracuseStep 129659143 = 194488715) B194488715
theorem B1077551 : Blo 1076618 1077551 := bstep (se 1 (by rfl) ⟨808163, by rfl⟩ : syracuseStep 1077551 = 1616327) B1616327
theorem B36008347 : Blo 1076618 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B1077871 : Blo 1076618 1077871 := bstep (se 1 (by rfl) ⟨808403, by rfl⟩ : syracuseStep 1077871 = 1616807) B1616807
theorem B1078047 : Blo 1076618 1078047 := bstep (se 1 (by rfl) ⟨808535, by rfl⟩ : syracuseStep 1078047 = 1617071) B1617071
theorem B5469119 : Blo 1076618 5469119 := bstep (se 1 (by rfl) ⟨4101839, by rfl⟩ : syracuseStep 5469119 = 8203679) B8203679
theorem B1078363 : Blo 1076618 1078363 := bstep (se 1 (by rfl) ⟨808772, by rfl⟩ : syracuseStep 1078363 = 1617545) B1617545
theorem B9336221 : Blo 1076618 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B1078751 : Blo 1076618 1078751 := bstep (se 1 (by rfl) ⟨809063, by rfl⟩ : syracuseStep 1078751 = 1618127) B1618127
theorem B2422547 : Blo 1076618 2422547 := bstep (se 1 (by rfl) ⟨1816910, by rfl⟩ : syracuseStep 2422547 = 3633821) B3633821
theorem B1079067 : Blo 1076618 1079067 := bstep (se 1 (by rfl) ⟨809300, by rfl⟩ : syracuseStep 1079067 = 1618601) B1618601
theorem B1079207 : Blo 1076618 1079207 := bstep (se 1 (by rfl) ⟨809405, by rfl⟩ : syracuseStep 1079207 = 1618811) B1618811
theorem B1079327 : Blo 1076618 1079327 := bstep (se 1 (by rfl) ⟨809495, by rfl⟩ : syracuseStep 1079327 = 1618991) B1618991
theorem B1079503 : Blo 1076618 1079503 := bstep (se 1 (by rfl) ⟨809627, by rfl⟩ : syracuseStep 1079503 = 1619255) B1619255
theorem B1079623 : Blo 1076618 1079623 := bstep (se 1 (by rfl) ⟨809717, by rfl⟩ : syracuseStep 1079623 = 1619435) B1619435
theorem B8747635 : Blo 1076618 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B2423465 : Blo 1076618 2423465 := bstep (se 2 (by rfl) ⟨908799, by rfl⟩ : syracuseStep 2423465 = 1817599) B1817599
theorem B4094671 : Blo 1076618 4094671 := bstep (se 1 (by rfl) ⟨3071003, by rfl⟩ : syracuseStep 4094671 = 6142007) B6142007
theorem B1080059 : Blo 1076618 1080059 := bstep (se 1 (by rfl) ⟨810044, by rfl⟩ : syracuseStep 1080059 = 1620089) B1620089
theorem B1080095 : Blo 1076618 1080095 := bstep (se 1 (by rfl) ⟨810071, by rfl⟩ : syracuseStep 1080095 = 1620143) B1620143
theorem B1080383 : Blo 1076618 1080383 := bstep (se 1 (by rfl) ⟨810287, by rfl⟩ : syracuseStep 1080383 = 1620575) B1620575
theorem B6552697 : Blo 1076618 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B151387319 : Blo 1076618 151387319 := bstep (se 1 (by rfl) ⟨113540489, by rfl⟩ : syracuseStep 151387319 = 227080979) B227080979
theorem B2424059 : Blo 1076618 2424059 := bstep (se 1 (by rfl) ⟨1818044, by rfl⟩ : syracuseStep 2424059 = 3636089) B3636089
theorem B3636521 : Blo 1076618 3636521 := bstep (se 2 (by rfl) ⟨1363695, by rfl⟩ : syracuseStep 3636521 = 2727391) B2727391
theorem B2424167 : Blo 1076618 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B2424239 : Blo 1076618 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B3636791 : Blo 1076618 3636791 := bstep (se 1 (by rfl) ⟨2727593, by rfl⟩ : syracuseStep 3636791 = 5455187) B5455187
theorem B1212187 : Blo 1076618 1212187 := bstep (se 1 (by rfl) ⟨909140, by rfl⟩ : syracuseStep 1212187 = 1818281) B1818281
theorem B3637385 : Blo 1076618 3637385 := bstep (se 2 (by rfl) ⟨1364019, by rfl⟩ : syracuseStep 3637385 = 2728039) B2728039
theorem B1212655 : Blo 1076618 1212655 := bstep (se 1 (by rfl) ⟨909491, by rfl⟩ : syracuseStep 1212655 = 1818983) B1818983
theorem B21037657 : Blo 1076618 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B3638303 : Blo 1076618 3638303 := bstep (se 1 (by rfl) ⟨2728727, by rfl⟩ : syracuseStep 3638303 = 5457455) B5457455
theorem B11666537 : Blo 1076618 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B18449531 : Blo 1076618 18449531 := bstep (se 1 (by rfl) ⟨13837148, by rfl⟩ : syracuseStep 18449531 = 27674297) B27674297
theorem B6915887 : Blo 1076618 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B17500187 : Blo 1076618 17500187 := bstep (se 1 (by rfl) ⟨13125140, by rfl⟩ : syracuseStep 17500187 = 26250281) B26250281
theorem B3640031 : Blo 1076618 3640031 := bstep (se 1 (by rfl) ⟨2730023, by rfl⟩ : syracuseStep 3640031 = 5460047) B5460047
theorem B1215355 : Blo 1076618 1215355 := bstep (se 1 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 1215355 = 1823033) B1823033
theorem B6917345 : Blo 1076618 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B3640571 : Blo 1076618 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B63901043 : Blo 1076618 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B3641057 : Blo 1076618 3641057 := bstep (se 2 (by rfl) ⟨1365396, by rfl⟩ : syracuseStep 3641057 = 2730793) B2730793
theorem B2428703 : Blo 1076618 2428703 := bstep (se 1 (by rfl) ⟨1821527, by rfl⟩ : syracuseStep 2428703 = 3643055) B3643055
theorem B5541979 : Blo 1076618 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B283250789 : Blo 1076618 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B7016971 : Blo 1076618 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B51188429 : Blo 1076618 51188429 := bstep (se 3 (by rfl) ⟨9597830, by rfl⟩ : syracuseStep 51188429 = 19195661) B19195661
theorem B3642839 : Blo 1076618 3642839 := bstep (se 1 (by rfl) ⟨2732129, by rfl⟩ : syracuseStep 3642839 = 5464259) B5464259
theorem B6919805 : Blo 1076618 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B48011129 : Blo 1076618 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B3643379 : Blo 1076618 3643379 := bstep (se 1 (by rfl) ⟨2732534, by rfl⟩ : syracuseStep 3643379 = 5465069) B5465069
theorem B2725883 : Blo 1076618 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B2464249 : Blo 1076618 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B3643919 : Blo 1076618 3643919 := bstep (se 1 (by rfl) ⟨2732939, by rfl⟩ : syracuseStep 3643919 = 5465879) B5465879
theorem B1843535 : Blo 1076618 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B2728313 : Blo 1076618 2728313 := bstep (se 2 (by rfl) ⟨1023117, by rfl⟩ : syracuseStep 2728313 = 2046235) B2046235
theorem B3646079 : Blo 1076618 3646079 := bstep (se 1 (by rfl) ⟨2734559, by rfl⟩ : syracuseStep 3646079 = 5469119) B5469119
theorem B1615031 : Blo 1076618 1615031 := bstep (se 1 (by rfl) ⟨1211273, by rfl⟩ : syracuseStep 1615031 = 2422547) B2422547
theorem B1615643 : Blo 1076618 1615643 := bstep (se 1 (by rfl) ⟨1211732, by rfl⟩ : syracuseStep 1615643 = 2423465) B2423465
theorem B1616039 : Blo 1076618 1616039 := bstep (se 1 (by rfl) ⟨1212029, by rfl⟩ : syracuseStep 1616039 = 2424059) B2424059
theorem B1616111 : Blo 1076618 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B1616159 : Blo 1076618 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B1616249 : Blo 1076618 1616249 := bstep (se 2 (by rfl) ⟨606093, by rfl⟩ : syracuseStep 1616249 = 1212187) B1212187
theorem B1616591 : Blo 1076618 1616591 := bstep (se 1 (by rfl) ⟨1212443, by rfl⟩ : syracuseStep 1616591 = 2424887) B2424887
theorem B1616879 : Blo 1076618 1616879 := bstep (se 1 (by rfl) ⟨1212659, by rfl⟩ : syracuseStep 1616879 = 2425319) B2425319
theorem B1616951 : Blo 1076618 1616951 := bstep (se 1 (by rfl) ⟨1212713, by rfl⟩ : syracuseStep 1616951 = 2425427) B2425427
theorem B1945115 : Blo 1076618 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B1617863 : Blo 1076618 1617863 := bstep (se 1 (by rfl) ⟨1213397, by rfl⟩ : syracuseStep 1617863 = 2426795) B2426795
theorem B11644955 : Blo 1076618 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B2044207 : Blo 1076618 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B6140231 : Blo 1076618 6140231 := bstep (se 1 (by rfl) ⟨4605173, by rfl⟩ : syracuseStep 6140231 = 9210347) B9210347
theorem B1618415 : Blo 1076618 1618415 := bstep (se 1 (by rfl) ⟨1213811, by rfl⟩ : syracuseStep 1618415 = 2427623) B2427623
theorem B14759167 : Blo 1076618 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B1619945 : Blo 1076618 1619945 := bstep (se 2 (by rfl) ⟨607479, by rfl⟩ : syracuseStep 1619945 = 1214959) B1214959
theorem B3881033 : Blo 1076618 3881033 := bstep (se 2 (by rfl) ⟨1455387, by rfl⟩ : syracuseStep 3881033 = 2910775) B2910775
theorem B1620137 : Blo 1076618 1620137 := bstep (se 2 (by rfl) ⟨607551, by rfl⟩ : syracuseStep 1620137 = 1215103) B1215103
theorem B2046683 : Blo 1076618 2046683 := bstep (se 1 (by rfl) ⟨1535012, by rfl⟩ : syracuseStep 2046683 = 3070025) B3070025
theorem B1620767 : Blo 1076618 1620767 := bstep (se 1 (by rfl) ⟨1215575, by rfl⟩ : syracuseStep 1620767 = 2431151) B2431151
theorem B3882127 : Blo 1076618 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B1817903 : Blo 1076618 1817903 := bstep (se 1 (by rfl) ⟨1363427, by rfl⟩ : syracuseStep 1817903 = 2726855) B2726855
theorem B1818011 : Blo 1076618 1818011 := bstep (se 1 (by rfl) ⟨1363508, by rfl⟩ : syracuseStep 1818011 = 2727017) B2727017
theorem B2047457 : Blo 1076618 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B5914387 : Blo 1076618 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B5455835 : Blo 1076618 5455835 := bstep (se 1 (by rfl) ⟨4091876, by rfl⟩ : syracuseStep 5455835 = 8183753) B8183753
theorem B5458589 : Blo 1076618 5458589 := bstep (se 3 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 5458589 = 2046971) B2046971
theorem B5459561 : Blo 1076618 5459561 := bstep (se 2 (by rfl) ⟨2047335, by rfl⟩ : syracuseStep 5459561 = 4094671) B4094671
theorem B8736929 : Blo 1076618 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B1365103 : Blo 1076618 1365103 := bstep (se 1 (by rfl) ⟨1023827, by rfl⟩ : syracuseStep 1365103 = 2047655) B2047655
theorem B52549235 : Blo 1076618 52549235 := bstep (se 1 (by rfl) ⟨39411926, by rfl⟩ : syracuseStep 52549235 = 78823853) B78823853
theorem B29546369 : Blo 1076618 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B4610675 : Blo 1076618 4610675 := bstep (se 1 (by rfl) ⟨3458006, by rfl⟩ : syracuseStep 4610675 = 6916013) B6916013
theorem B1367599 : Blo 1076618 1367599 := bstep (se 1 (by rfl) ⟨1025699, by rfl⟩ : syracuseStep 1367599 = 2051399) B2051399
theorem B1728055 : Blo 1076618 1728055 := bstep (se 1 (by rfl) ⟨1296041, by rfl⟩ : syracuseStep 1728055 = 2592083) B2592083
theorem B20701595 : Blo 1076618 20701595 := bstep (se 1 (by rfl) ⟨15526196, by rfl⟩ : syracuseStep 20701595 = 31052393) B31052393
theorem B9200573 : Blo 1076618 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B6906991 : Blo 1076618 6906991 := bstep (se 1 (by rfl) ⟨5180243, by rfl⟩ : syracuseStep 6906991 = 10360487) B10360487
theorem B6154127 : Blo 1076618 6154127 := bstep (se 1 (by rfl) ⟨4615595, by rfl⟩ : syracuseStep 6154127 = 9231191) B9231191
theorem B106588061 : Blo 1076618 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B1534135 : Blo 1076618 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B172878857 : Blo 1076618 172878857 := bstep (se 2 (by rfl) ⟨64829571, by rfl⟩ : syracuseStep 172878857 = 129659143) B129659143
theorem B1077319 : Blo 1076618 1077319 := bstep (se 1 (by rfl) ⟨807989, by rfl⟩ : syracuseStep 1077319 = 1615979) B1615979
theorem B8188127 : Blo 1076618 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B22180205 : Blo 1076618 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B1077735 : Blo 1076618 1077735 := bstep (se 1 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 1077735 = 1616603) B1616603
theorem B1077791 : Blo 1076618 1077791 := bstep (se 1 (by rfl) ⟨808343, by rfl⟩ : syracuseStep 1077791 = 1616687) B1616687
theorem B1077951 : Blo 1076618 1077951 := bstep (se 1 (by rfl) ⟨808463, by rfl⟩ : syracuseStep 1077951 = 1616927) B1616927
theorem B1078503 : Blo 1076618 1078503 := bstep (se 1 (by rfl) ⟨808877, by rfl⟩ : syracuseStep 1078503 = 1617755) B1617755
theorem B1078975 : Blo 1076618 1078975 := bstep (se 1 (by rfl) ⟨809231, by rfl⟩ : syracuseStep 1078975 = 1618463) B1618463
theorem B11663513 : Blo 1076618 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B1079535 : Blo 1076618 1079535 := bstep (se 1 (by rfl) ⟨809651, by rfl⟩ : syracuseStep 1079535 = 1619303) B1619303
theorem B6224147 : Blo 1076618 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B2914699 : Blo 1076618 2914699 := bstep (se 1 (by rfl) ⟨2186024, by rfl⟩ : syracuseStep 2914699 = 4372049) B4372049
theorem B1079791 : Blo 1076618 1079791 := bstep (se 1 (by rfl) ⟨809843, by rfl⟩ : syracuseStep 1079791 = 1619687) B1619687
theorem B3635711 : Blo 1076618 3635711 := bstep (se 1 (by rfl) ⟨2726783, by rfl⟩ : syracuseStep 3635711 = 5453567) B5453567
theorem B1079919 : Blo 1076618 1079919 := bstep (se 1 (by rfl) ⟨809939, by rfl⟩ : syracuseStep 1079919 = 1619879) B1619879
theorem B1080255 : Blo 1076618 1080255 := bstep (se 1 (by rfl) ⟨810191, by rfl⟩ : syracuseStep 1080255 = 1620383) B1620383
theorem B2587643 : Blo 1076618 2587643 := bstep (se 1 (by rfl) ⟨1940732, by rfl⟩ : syracuseStep 2587643 = 3881465) B3881465
theorem B1080487 : Blo 1076618 1080487 := bstep (se 1 (by rfl) ⟨810365, by rfl⟩ : syracuseStep 1080487 = 1620731) B1620731
theorem B100924879 : Blo 1076618 100924879 := bstep (se 1 (by rfl) ⟨75693659, by rfl⟩ : syracuseStep 100924879 = 151387319) B151387319
theorem B2424347 : Blo 1076618 2424347 := bstep (se 1 (by rfl) ⟨1818260, by rfl⟩ : syracuseStep 2424347 = 3636521) B3636521
theorem B2424527 : Blo 1076618 2424527 := bstep (se 1 (by rfl) ⟨1818395, by rfl⟩ : syracuseStep 2424527 = 3636791) B3636791
theorem B2424923 : Blo 1076618 2424923 := bstep (se 1 (by rfl) ⟨1818692, by rfl⟩ : syracuseStep 2424923 = 3637385) B3637385
theorem B2425535 : Blo 1076618 2425535 := bstep (se 1 (by rfl) ⟨1819151, by rfl⟩ : syracuseStep 2425535 = 3638303) B3638303
theorem B28050209 : Blo 1076618 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B11666791 : Blo 1076618 11666791 := bstep (se 1 (by rfl) ⟨8750093, by rfl⟩ : syracuseStep 11666791 = 17500187) B17500187
theorem B9209321 : Blo 1076618 9209321 := bstep (se 2 (by rfl) ⟨3453495, by rfl⟩ : syracuseStep 9209321 = 6906991) B6906991
theorem B3639059 : Blo 1076618 3639059 := bstep (se 1 (by rfl) ⟨2729294, by rfl⟩ : syracuseStep 3639059 = 5458589) B5458589
theorem B2426687 : Blo 1076618 2426687 := bstep (se 1 (by rfl) ⟨1820015, by rfl⟩ : syracuseStep 2426687 = 3640031) B3640031
theorem B2427047 : Blo 1076618 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B42600695 : Blo 1076618 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B3639707 : Blo 1076618 3639707 := bstep (se 1 (by rfl) ⟨2729780, by rfl⟩ : syracuseStep 3639707 = 5459561) B5459561
theorem B2427371 : Blo 1076618 2427371 := bstep (se 1 (by rfl) ⟨1820528, by rfl⟩ : syracuseStep 2427371 = 3641057) B3641057
theorem B2428559 : Blo 1076618 2428559 := bstep (se 1 (by rfl) ⟨1821419, by rfl⟩ : syracuseStep 2428559 = 3642839) B3642839
theorem B35032823 : Blo 1076618 35032823 := bstep (se 1 (by rfl) ⟨26274617, by rfl⟩ : syracuseStep 35032823 = 52549235) B52549235
theorem B19697579 : Blo 1076618 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B2428919 : Blo 1076618 2428919 := bstep (se 1 (by rfl) ⟨1821689, by rfl⟩ : syracuseStep 2428919 = 3643379) B3643379
theorem B2429279 : Blo 1076618 2429279 := bstep (se 1 (by rfl) ⟨1821959, by rfl⟩ : syracuseStep 2429279 = 3643919) B3643919
theorem B13801063 : Blo 1076618 13801063 := bstep (se 1 (by rfl) ⟨10350797, by rfl⟩ : syracuseStep 13801063 = 20701595) B20701595
theorem B2725609 : Blo 1076618 2725609 := bstep (se 2 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 2725609 = 2044207) B2044207
theorem B2430719 : Blo 1076618 2430719 := bstep (se 1 (by rfl) ⟨1823039, by rfl⟩ : syracuseStep 2430719 = 3646079) B3646079
theorem B6133715 : Blo 1076618 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B4102751 : Blo 1076618 4102751 := bstep (se 1 (by rfl) ⟨3077063, by rfl⟩ : syracuseStep 4102751 = 6154127) B6154127
theorem B115252571 : Blo 1076618 115252571 := bstep (se 1 (by rfl) ⟨86439428, by rfl⟩ : syracuseStep 115252571 = 172878857) B172878857
theorem B14786803 : Blo 1076618 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B3285665 : Blo 1076618 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B7775675 : Blo 1076618 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B2304073 : Blo 1076618 2304073 := bstep (se 2 (by rfl) ⟨864027, by rfl⟩ : syracuseStep 2304073 = 1728055) B1728055
theorem B1616231 : Blo 1076618 1616231 := bstep (se 1 (by rfl) ⟨1212173, by rfl⟩ : syracuseStep 1616231 = 2424347) B2424347
theorem B1616351 : Blo 1076618 1616351 := bstep (se 1 (by rfl) ⟨1212263, by rfl⟩ : syracuseStep 1616351 = 2424527) B2424527
theorem B1616873 : Blo 1076618 1616873 := bstep (se 2 (by rfl) ⟨606327, by rfl⟩ : syracuseStep 1616873 = 1212655) B1212655
theorem B7777691 : Blo 1076618 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B12299687 : Blo 1076618 12299687 := bstep (se 1 (by rfl) ⟨9224765, by rfl⟩ : syracuseStep 12299687 = 18449531) B18449531
theorem B1619135 : Blo 1076618 1619135 := bstep (se 1 (by rfl) ⟨1214351, by rfl⟩ : syracuseStep 1619135 = 2428703) B2428703
theorem B2045513 : Blo 1076618 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B34125619 : Blo 1076618 34125619 := bstep (se 1 (by rfl) ⟨25594214, by rfl⟩ : syracuseStep 34125619 = 51188429) B51188429
theorem B1620473 : Blo 1076618 1620473 := bstep (se 2 (by rfl) ⟨607677, by rfl⟩ : syracuseStep 1620473 = 1215355) B1215355
theorem B1817255 : Blo 1076618 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B7389305 : Blo 1076618 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B1229023 : Blo 1076618 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1818875 : Blo 1076618 1818875 := bstep (se 1 (by rfl) ⟨1364156, by rfl⟩ : syracuseStep 1818875 = 2728313) B2728313
theorem B9355961 : Blo 1076618 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B71058707 : Blo 1076618 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B1820137 : Blo 1076618 1820137 := bstep (se 2 (by rfl) ⟨682551, by rfl⟩ : syracuseStep 1820137 = 1365103) B1365103
theorem B19678889 : Blo 1076618 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B1296743 : Blo 1076618 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B5458751 : Blo 1076618 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B3886265 : Blo 1076618 3886265 := bstep (se 2 (by rfl) ⟨1457349, by rfl⟩ : syracuseStep 3886265 = 2914699) B2914699
theorem B5459885 : Blo 1076618 5459885 := bstep (se 3 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 5459885 = 2047457) B2047457
theorem B4149431 : Blo 1076618 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B1364455 : Blo 1076618 1364455 := bstep (se 1 (by rfl) ⟨1023341, by rfl⟩ : syracuseStep 1364455 = 2046683) B2046683
theorem B134566505 : Blo 1076618 134566505 := bstep (se 2 (by rfl) ⟨50462439, by rfl⟩ : syracuseStep 134566505 = 100924879) B100924879
theorem B1725095 : Blo 1076618 1725095 := bstep (se 1 (by rfl) ⟨1293821, by rfl⟩ : syracuseStep 1725095 = 2587643) B2587643
theorem B1823465 : Blo 1076618 1823465 := bstep (se 2 (by rfl) ⟨683799, by rfl⟩ : syracuseStep 1823465 = 1367599) B1367599
theorem B7885849 : Blo 1076618 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B4610591 : Blo 1076618 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B4611563 : Blo 1076618 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B188833859 : Blo 1076618 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B5824619 : Blo 1076618 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B4613203 : Blo 1076618 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B32007419 : Blo 1076618 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B3073783 : Blo 1076618 3073783 := bstep (se 1 (by rfl) ⟨2305337, by rfl⟩ : syracuseStep 3073783 = 4610675) B4610675
theorem B1076687 : Blo 1076618 1076687 := bstep (se 1 (by rfl) ⟨807515, by rfl⟩ : syracuseStep 1076687 = 1615031) B1615031
theorem B1077095 : Blo 1076618 1077095 := bstep (se 1 (by rfl) ⟨807821, by rfl⟩ : syracuseStep 1077095 = 1615643) B1615643
theorem B1077359 : Blo 1076618 1077359 := bstep (se 1 (by rfl) ⟨808019, by rfl⟩ : syracuseStep 1077359 = 1616039) B1616039
theorem B1077407 : Blo 1076618 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B1077439 : Blo 1076618 1077439 := bstep (se 1 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 1077439 = 1616159) B1616159
theorem B1077499 : Blo 1076618 1077499 := bstep (se 1 (by rfl) ⟨808124, by rfl⟩ : syracuseStep 1077499 = 1616249) B1616249
theorem B1077727 : Blo 1076618 1077727 := bstep (se 1 (by rfl) ⟨808295, by rfl⟩ : syracuseStep 1077727 = 1616591) B1616591
theorem B1077919 : Blo 1076618 1077919 := bstep (se 1 (by rfl) ⟨808439, by rfl⟩ : syracuseStep 1077919 = 1616879) B1616879
theorem B1077967 : Blo 1076618 1077967 := bstep (se 1 (by rfl) ⟨808475, by rfl⟩ : syracuseStep 1077967 = 1616951) B1616951
theorem B1078575 : Blo 1076618 1078575 := bstep (se 1 (by rfl) ⟨808931, by rfl⟩ : syracuseStep 1078575 = 1617863) B1617863
theorem B7763303 : Blo 1076618 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B4093487 : Blo 1076618 4093487 := bstep (se 1 (by rfl) ⟨3070115, by rfl⟩ : syracuseStep 4093487 = 6140231) B6140231
theorem B1078943 : Blo 1076618 1078943 := bstep (se 1 (by rfl) ⟨809207, by rfl⟩ : syracuseStep 1078943 = 1618415) B1618415
theorem B1079963 : Blo 1076618 1079963 := bstep (se 1 (by rfl) ⟨809972, by rfl⟩ : syracuseStep 1079963 = 1619945) B1619945
theorem B2587355 : Blo 1076618 2587355 := bstep (se 1 (by rfl) ⟨1940516, by rfl⟩ : syracuseStep 2587355 = 3881033) B3881033
theorem B1080091 : Blo 1076618 1080091 := bstep (se 1 (by rfl) ⟨810068, by rfl⟩ : syracuseStep 1080091 = 1620137) B1620137
theorem B5176169 : Blo 1076618 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B2423807 : Blo 1076618 2423807 := bstep (se 1 (by rfl) ⟨1817855, by rfl⟩ : syracuseStep 2423807 = 3635711) B3635711
theorem B1080511 : Blo 1076618 1080511 := bstep (se 1 (by rfl) ⟨810383, by rfl⟩ : syracuseStep 1080511 = 1620767) B1620767
theorem B1211935 : Blo 1076618 1211935 := bstep (se 1 (by rfl) ⟨908951, by rfl⟩ : syracuseStep 1211935 = 1817903) B1817903
theorem B1212007 : Blo 1076618 1212007 := bstep (se 1 (by rfl) ⟨909005, by rfl⟩ : syracuseStep 1212007 = 1818011) B1818011
theorem B3637223 : Blo 1076618 3637223 := bstep (se 1 (by rfl) ⟨2727917, by rfl⟩ : syracuseStep 3637223 = 5455835) B5455835
theorem B1212583 : Blo 1076618 1212583 := bstep (se 1 (by rfl) ⟨909437, by rfl⟩ : syracuseStep 1212583 = 1818875) B1818875
theorem B1638697 : Blo 1076618 1638697 := bstep (se 2 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 1638697 = 1229023) B1229023
theorem B2426039 : Blo 1076618 2426039 := bstep (se 1 (by rfl) ⟨1819529, by rfl⟩ : syracuseStep 2426039 = 3639059) B3639059
theorem B2426471 : Blo 1076618 2426471 := bstep (se 1 (by rfl) ⟨1819853, by rfl⟩ : syracuseStep 2426471 = 3639707) B3639707
theorem B3639167 : Blo 1076618 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B2426849 : Blo 1076618 2426849 := bstep (se 2 (by rfl) ⟨910068, by rfl⟩ : syracuseStep 2426849 = 1820137) B1820137
theorem B4098377 : Blo 1076618 4098377 := bstep (se 2 (by rfl) ⟨1536891, by rfl⟩ : syracuseStep 4098377 = 3073783) B3073783
theorem B3639923 : Blo 1076618 3639923 := bstep (se 1 (by rfl) ⟨2729942, by rfl⟩ : syracuseStep 3639923 = 5459885) B5459885
theorem B1215643 : Blo 1076618 1215643 := bstep (se 1 (by rfl) ⟨911732, by rfl⟩ : syracuseStep 1215643 = 1823465) B1823465
theorem B21338279 : Blo 1076618 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B5183783 : Blo 1076618 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B5185127 : Blo 1076618 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B8199791 : Blo 1076618 8199791 := bstep (se 1 (by rfl) ⟨6149843, by rfl⟩ : syracuseStep 8199791 = 12299687) B12299687
theorem B10363373 : Blo 1076618 10363373 := bstep (se 3 (by rfl) ⟨1943132, by rfl⟩ : syracuseStep 10363373 = 3886265) B3886265
theorem B307340189 : Blo 1076618 307340189 := bstep (se 3 (by rfl) ⟨57626285, by rfl⟩ : syracuseStep 307340189 = 115252571) B115252571
theorem B2728991 : Blo 1076618 2728991 := bstep (se 1 (by rfl) ⟨2046743, by rfl⟩ : syracuseStep 2728991 = 4093487) B4093487
theorem B3450779 : Blo 1076618 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B1615871 : Blo 1076618 1615871 := bstep (se 1 (by rfl) ⟨1211903, by rfl⟩ : syracuseStep 1615871 = 2423807) B2423807
theorem B1615913 : Blo 1076618 1615913 := bstep (se 2 (by rfl) ⟨605967, by rfl⟩ : syracuseStep 1615913 = 1211935) B1211935
theorem B1616009 : Blo 1076618 1616009 := bstep (se 2 (by rfl) ⟨606003, by rfl⟩ : syracuseStep 1616009 = 1212007) B1212007
theorem B1616615 : Blo 1076618 1616615 := bstep (se 1 (by rfl) ⟨1212461, by rfl⟩ : syracuseStep 1616615 = 2424923) B2424923
theorem B4926203 : Blo 1076618 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B6237307 : Blo 1076618 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B1617023 : Blo 1076618 1617023 := bstep (se 1 (by rfl) ⟨1212767, by rfl⟩ : syracuseStep 1617023 = 2425535) B2425535
theorem B6139547 : Blo 1076618 6139547 := bstep (se 1 (by rfl) ⟨4604660, by rfl⟩ : syracuseStep 6139547 = 9209321) B9209321
theorem B13119259 : Blo 1076618 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B1617791 : Blo 1076618 1617791 := bstep (se 1 (by rfl) ⟨1213343, by rfl⟩ : syracuseStep 1617791 = 2426687) B2426687
theorem B1618031 : Blo 1076618 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B1618247 : Blo 1076618 1618247 := bstep (se 1 (by rfl) ⟨1213685, by rfl⟩ : syracuseStep 1618247 = 2427371) B2427371
theorem B4600253 : Blo 1076618 4600253 := bstep (se 3 (by rfl) ⟨862547, by rfl⟩ : syracuseStep 4600253 = 1725095) B1725095
theorem B1619039 : Blo 1076618 1619039 := bstep (se 1 (by rfl) ⟨1214279, by rfl⟩ : syracuseStep 1619039 = 2428559) B2428559
theorem B1619279 : Blo 1076618 1619279 := bstep (se 1 (by rfl) ⟨1214459, by rfl⟩ : syracuseStep 1619279 = 2428919) B2428919
theorem B2766287 : Blo 1076618 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B1619519 : Blo 1076618 1619519 := bstep (se 1 (by rfl) ⟨1214639, by rfl⟩ : syracuseStep 1619519 = 2429279) B2429279
theorem B1620479 : Blo 1076618 1620479 := bstep (se 1 (by rfl) ⟨1215359, by rfl⟩ : syracuseStep 1620479 = 2430719) B2430719
theorem B5454701 : Blo 1076618 5454701 := bstep (se 3 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 5454701 = 2045513) B2045513
theorem B2735167 : Blo 1076618 2735167 := bstep (se 1 (by rfl) ⟨2051375, by rfl⟩ : syracuseStep 2735167 = 4102751) B4102751
theorem B3883079 : Blo 1076618 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B1819273 : Blo 1076618 1819273 := bstep (se 2 (by rfl) ⟨682227, by rfl⟩ : syracuseStep 1819273 = 1364455) B1364455
theorem B3457981 : Blo 1076618 3457981 := bstep (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) B1296743
theorem B18401417 : Blo 1076618 18401417 := bstep (se 2 (by rfl) ⟨6900531, by rfl⟩ : syracuseStep 18401417 = 13801063) B13801063
theorem B45500825 : Blo 1076618 45500825 := bstep (se 2 (by rfl) ⟨17062809, by rfl⟩ : syracuseStep 45500825 = 34125619) B34125619
theorem B1724903 : Blo 1076618 1724903 := bstep (se 1 (by rfl) ⟨1293677, by rfl⟩ : syracuseStep 1724903 = 2587355) B2587355
theorem B19715737 : Blo 1076618 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B18700139 : Blo 1076618 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B47372471 : Blo 1076618 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B6150937 : Blo 1076618 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B15555721 : Blo 1076618 15555721 := bstep (se 2 (by rfl) ⟨5833395, by rfl⟩ : syracuseStep 15555721 = 11666791) B11666791
theorem B23355215 : Blo 1076618 23355215 := bstep (se 1 (by rfl) ⟨17516411, by rfl⟩ : syracuseStep 23355215 = 35032823) B35032823
theorem B13131719 : Blo 1076618 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B3072097 : Blo 1076618 3072097 := bstep (se 2 (by rfl) ⟨1152036, by rfl⟩ : syracuseStep 3072097 = 2304073) B2304073
theorem B89711003 : Blo 1076618 89711003 := bstep (se 1 (by rfl) ⟨67283252, by rfl⟩ : syracuseStep 89711003 = 134566505) B134566505
theorem B20702141 : Blo 1076618 20702141 := bstep (se 3 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 20702141 = 7763303) B7763303
theorem B4089143 : Blo 1076618 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B3073727 : Blo 1076618 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B3074375 : Blo 1076618 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B125889239 : Blo 1076618 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B2190443 : Blo 1076618 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B113601853 : Blo 1076618 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B10514465 : Blo 1076618 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B1077487 : Blo 1076618 1077487 := bstep (se 1 (by rfl) ⟨808115, by rfl⟩ : syracuseStep 1077487 = 1616231) B1616231
theorem B1077567 : Blo 1076618 1077567 := bstep (se 1 (by rfl) ⟨808175, by rfl⟩ : syracuseStep 1077567 = 1616351) B1616351
theorem B1077915 : Blo 1076618 1077915 := bstep (se 1 (by rfl) ⟨808436, by rfl⟩ : syracuseStep 1077915 = 1616873) B1616873
theorem B3634145 : Blo 1076618 3634145 := bstep (se 2 (by rfl) ⟨1362804, by rfl⟩ : syracuseStep 3634145 = 2725609) B2725609
theorem B1079423 : Blo 1076618 1079423 := bstep (se 1 (by rfl) ⟨809567, by rfl⟩ : syracuseStep 1079423 = 1619135) B1619135
theorem B1080315 : Blo 1076618 1080315 := bstep (se 1 (by rfl) ⟨810236, by rfl⟩ : syracuseStep 1080315 = 1620473) B1620473
theorem B1211503 : Blo 1076618 1211503 := bstep (se 1 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 1211503 = 1817255) B1817255
theorem B2424815 : Blo 1076618 2424815 := bstep (se 1 (by rfl) ⟨1818611, by rfl⟩ : syracuseStep 2424815 = 3637223) B3637223
theorem B4096129 : Blo 1076618 4096129 := bstep (se 2 (by rfl) ⟨1536048, by rfl⟩ : syracuseStep 4096129 = 3072097) B3072097
theorem B10354877 : Blo 1076618 10354877 := bstep (se 3 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 10354877 = 3883079) B3883079
theorem B2425697 : Blo 1076618 2425697 := bstep (se 2 (by rfl) ⟨909636, by rfl⟩ : syracuseStep 2425697 = 1819273) B1819273
theorem B2426111 : Blo 1076618 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B2426615 : Blo 1076618 2426615 := bstep (se 1 (by rfl) ⟨1819961, by rfl⟩ : syracuseStep 2426615 = 3639923) B3639923
theorem B1149935 : Blo 1076618 1149935 := bstep (se 1 (by rfl) ⟨862451, by rfl⟩ : syracuseStep 1149935 = 1724903) B1724903
theorem B14225519 : Blo 1076618 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B15570143 : Blo 1076618 15570143 := bstep (se 1 (by rfl) ⟨11677607, by rfl⟩ : syracuseStep 15570143 = 23355215) B23355215
theorem B8754479 : Blo 1076618 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B59807335 : Blo 1076618 59807335 := bstep (se 1 (by rfl) ⟨44855501, by rfl⟩ : syracuseStep 59807335 = 89711003) B89711003
theorem B13801427 : Blo 1076618 13801427 := bstep (se 1 (by rfl) ⟨10351070, by rfl⟩ : syracuseStep 13801427 = 20702141) B20702141
theorem B33265637 : Blo 1076618 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B8198333 : Blo 1076618 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B2726095 : Blo 1076618 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B2300519 : Blo 1076618 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B3284135 : Blo 1076618 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B26287649 : Blo 1076618 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B5841181 : Blo 1076618 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B1844191 : Blo 1076618 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B8201249 : Blo 1076618 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B3646889 : Blo 1076618 3646889 := bstep (se 2 (by rfl) ⟨1367583, by rfl⟩ : syracuseStep 3646889 = 2735167) B2735167
theorem B1615337 : Blo 1076618 1615337 := bstep (se 2 (by rfl) ⟨605751, by rfl⟩ : syracuseStep 1615337 = 1211503) B1211503
theorem B1616543 : Blo 1076618 1616543 := bstep (se 1 (by rfl) ⟨1212407, by rfl⟩ : syracuseStep 1616543 = 2424815) B2424815
theorem B1616777 : Blo 1076618 1616777 := bstep (se 2 (by rfl) ⟨606291, by rfl⟩ : syracuseStep 1616777 = 1212583) B1212583
theorem B1617359 : Blo 1076618 1617359 := bstep (se 1 (by rfl) ⟨1213019, by rfl⟩ : syracuseStep 1617359 = 2426039) B2426039
theorem B1617647 : Blo 1076618 1617647 := bstep (se 1 (by rfl) ⟨1213235, by rfl⟩ : syracuseStep 1617647 = 2426471) B2426471
theorem B1617899 : Blo 1076618 1617899 := bstep (se 1 (by rfl) ⟨1213424, by rfl⟩ : syracuseStep 1617899 = 2426849) B2426849
theorem B12267611 : Blo 1076618 12267611 := bstep (se 1 (by rfl) ⟨9200708, by rfl⟩ : syracuseStep 12267611 = 18401417) B18401417
theorem B2732251 : Blo 1076618 2732251 := bstep (se 1 (by rfl) ⟨2049188, by rfl⟩ : syracuseStep 2732251 = 4098377) B4098377
theorem B12466759 : Blo 1076618 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B3455855 : Blo 1076618 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B1620857 : Blo 1076618 1620857 := bstep (se 2 (by rfl) ⟨607821, by rfl⟩ : syracuseStep 1620857 = 1215643) B1215643
theorem B151469137 : Blo 1076618 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B3456751 : Blo 1076618 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B1819327 : Blo 1076618 1819327 := bstep (se 1 (by rfl) ⟨1364495, by rfl⟩ : syracuseStep 1819327 = 2728991) B2728991
theorem B2049151 : Blo 1076618 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3066835 : Blo 1076618 3066835 := bstep (se 1 (by rfl) ⟨2300126, by rfl⟩ : syracuseStep 3066835 = 4600253) B4600253
theorem B2184929 : Blo 1076618 2184929 := bstep (se 2 (by rfl) ⟨819348, by rfl⟩ : syracuseStep 2184929 = 1638697) B1638697
theorem B4610641 : Blo 1076618 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B31581647 : Blo 1076618 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B17492345 : Blo 1076618 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B5466527 : Blo 1076618 5466527 := bstep (se 1 (by rfl) ⟨4099895, by rfl⟩ : syracuseStep 5466527 = 8199791) B8199791
theorem B6908915 : Blo 1076618 6908915 := bstep (se 1 (by rfl) ⟨5181686, by rfl⟩ : syracuseStep 6908915 = 10363373) B10363373
theorem B204893459 : Blo 1076618 204893459 := bstep (se 1 (by rfl) ⟨153670094, by rfl⟩ : syracuseStep 204893459 = 307340189) B307340189
theorem B121335533 : Blo 1076618 121335533 := bstep (se 3 (by rfl) ⟨22750412, by rfl⟩ : syracuseStep 121335533 = 45500825) B45500825
theorem B1077247 : Blo 1076618 1077247 := bstep (se 1 (by rfl) ⟨807935, by rfl⟩ : syracuseStep 1077247 = 1615871) B1615871
theorem B1077275 : Blo 1076618 1077275 := bstep (se 1 (by rfl) ⟨807956, by rfl⟩ : syracuseStep 1077275 = 1615913) B1615913
theorem B1077339 : Blo 1076618 1077339 := bstep (se 1 (by rfl) ⟨808004, by rfl⟩ : syracuseStep 1077339 = 1616009) B1616009
theorem B1077743 : Blo 1076618 1077743 := bstep (se 1 (by rfl) ⟨808307, by rfl⟩ : syracuseStep 1077743 = 1616615) B1616615
theorem B335704637 : Blo 1076618 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B1078015 : Blo 1076618 1078015 := bstep (se 1 (by rfl) ⟨808511, by rfl⟩ : syracuseStep 1078015 = 1617023) B1617023
theorem B4093031 : Blo 1076618 4093031 := bstep (se 1 (by rfl) ⟨3069773, by rfl⟩ : syracuseStep 4093031 = 6139547) B6139547
theorem B1078527 : Blo 1076618 1078527 := bstep (se 1 (by rfl) ⟨808895, by rfl⟩ : syracuseStep 1078527 = 1617791) B1617791
theorem B7009643 : Blo 1076618 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B1078687 : Blo 1076618 1078687 := bstep (se 1 (by rfl) ⟨809015, by rfl⟩ : syracuseStep 1078687 = 1618031) B1618031
theorem B1078831 : Blo 1076618 1078831 := bstep (se 1 (by rfl) ⟨809123, by rfl⟩ : syracuseStep 1078831 = 1618247) B1618247
theorem B2422763 : Blo 1076618 2422763 := bstep (se 1 (by rfl) ⟨1817072, by rfl⟩ : syracuseStep 2422763 = 3634145) B3634145
theorem B1079359 : Blo 1076618 1079359 := bstep (se 1 (by rfl) ⟨809519, by rfl⟩ : syracuseStep 1079359 = 1619039) B1619039
theorem B1079519 : Blo 1076618 1079519 := bstep (se 1 (by rfl) ⟨809639, by rfl⟩ : syracuseStep 1079519 = 1619279) B1619279
theorem B1079679 : Blo 1076618 1079679 := bstep (se 1 (by rfl) ⟨809759, by rfl⟩ : syracuseStep 1079679 = 1619519) B1619519
theorem B20740961 : Blo 1076618 20740961 := bstep (se 2 (by rfl) ⟨7777860, by rfl⟩ : syracuseStep 20740961 = 15555721) B15555721
theorem B1080319 : Blo 1076618 1080319 := bstep (se 1 (by rfl) ⟨810239, by rfl⟩ : syracuseStep 1080319 = 1620479) B1620479
theorem B3636467 : Blo 1076618 3636467 := bstep (se 1 (by rfl) ⟨2727350, by rfl⟩ : syracuseStep 3636467 = 5454701) B5454701
theorem B2425769 : Blo 1076618 2425769 := bstep (se 2 (by rfl) ⟨909663, by rfl⟩ : syracuseStep 2425769 = 1819327) B1819327
theorem B2458921 : Blo 1076618 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B5836319 : Blo 1076618 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B3643001 : Blo 1076618 3643001 := bstep (se 2 (by rfl) ⟨1366125, by rfl⟩ : syracuseStep 3643001 = 2732251) B2732251
theorem B2431259 : Blo 1076618 2431259 := bstep (se 1 (by rfl) ⟨1823444, by rfl⟩ : syracuseStep 2431259 = 3646889) B3646889
theorem B6134717 : Blo 1076618 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B3644351 : Blo 1076618 3644351 := bstep (se 1 (by rfl) ⟨2733263, by rfl⟩ : syracuseStep 3644351 = 5466527) B5466527
theorem B2728687 : Blo 1076618 2728687 := bstep (se 1 (by rfl) ⟨2046515, by rfl⟩ : syracuseStep 2728687 = 4093031) B4093031
theorem B16622345 : Blo 1076618 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B1615175 : Blo 1076618 1615175 := bstep (se 1 (by rfl) ⟨1211381, by rfl⟩ : syracuseStep 1615175 = 2422763) B2422763
theorem B201958849 : Blo 1076618 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B2303903 : Blo 1076618 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B1617131 : Blo 1076618 1617131 := bstep (se 1 (by rfl) ⟨1212848, by rfl⟩ : syracuseStep 1617131 = 2425697) B2425697
theorem B1617407 : Blo 1076618 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B1617743 : Blo 1076618 1617743 := bstep (se 1 (by rfl) ⟨1213307, by rfl⟩ : syracuseStep 1617743 = 2426615) B2426615
theorem B2732201 : Blo 1076618 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B9483679 : Blo 1076618 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B1456619 : Blo 1076618 1456619 := bstep (se 1 (by rfl) ⟨1092464, by rfl⟩ : syracuseStep 1456619 = 2184929) B2184929
theorem B21054431 : Blo 1076618 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B4605943 : Blo 1076618 4605943 := bstep (se 1 (by rfl) ⟨3454457, by rfl⟩ : syracuseStep 4605943 = 6908915) B6908915
theorem B79743113 : Blo 1076618 79743113 := bstep (se 2 (by rfl) ⟨29903667, by rfl⟩ : syracuseStep 79743113 = 59807335) B59807335
theorem B136595639 : Blo 1076618 136595639 := bstep (se 1 (by rfl) ⟨102446729, by rfl⟩ : syracuseStep 136595639 = 204893459) B204893459
theorem B80890355 : Blo 1076618 80890355 := bstep (se 1 (by rfl) ⟨60667766, by rfl⟩ : syracuseStep 80890355 = 121335533) B121335533
theorem B3066493 : Blo 1076618 3066493 := bstep (se 3 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 3066493 = 1149935) B1149935
theorem B8178407 : Blo 1076618 8178407 := bstep (se 1 (by rfl) ⟨6133805, by rfl⟩ : syracuseStep 8178407 = 12267611) B12267611
theorem B6147521 : Blo 1076618 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B4673095 : Blo 1076618 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B4609001 : Blo 1076618 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B6903251 : Blo 1076618 6903251 := bstep (se 1 (by rfl) ⟨5177438, by rfl⟩ : syracuseStep 6903251 = 10354877) B10354877
theorem B5461505 : Blo 1076618 5461505 := bstep (se 2 (by rfl) ⟨2048064, by rfl⟩ : syracuseStep 5461505 = 4096129) B4096129
theorem B7788241 : Blo 1076618 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B10380095 : Blo 1076618 10380095 := bstep (se 1 (by rfl) ⟨7785071, by rfl⟩ : syracuseStep 10380095 = 15570143) B15570143
theorem B4089113 : Blo 1076618 4089113 := bstep (se 2 (by rfl) ⟨1533417, by rfl⟩ : syracuseStep 4089113 = 3066835) B3066835
theorem B9200951 : Blo 1076618 9200951 := bstep (se 1 (by rfl) ⟨6900713, by rfl⟩ : syracuseStep 9200951 = 13801427) B13801427
theorem B22177091 : Blo 1076618 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B5465555 : Blo 1076618 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B2189423 : Blo 1076618 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B17525099 : Blo 1076618 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B5467499 : Blo 1076618 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B1076891 : Blo 1076618 1076891 := bstep (se 1 (by rfl) ⟨807668, by rfl⟩ : syracuseStep 1076891 = 1615337) B1615337
theorem B11661563 : Blo 1076618 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B1077695 : Blo 1076618 1077695 := bstep (se 1 (by rfl) ⟨808271, by rfl⟩ : syracuseStep 1077695 = 1616543) B1616543
theorem B1077851 : Blo 1076618 1077851 := bstep (se 1 (by rfl) ⟨808388, by rfl⟩ : syracuseStep 1077851 = 1616777) B1616777
theorem B1078239 : Blo 1076618 1078239 := bstep (se 1 (by rfl) ⟨808679, by rfl⟩ : syracuseStep 1078239 = 1617359) B1617359
theorem B1078431 : Blo 1076618 1078431 := bstep (se 1 (by rfl) ⟨808823, by rfl⟩ : syracuseStep 1078431 = 1617647) B1617647
theorem B1078599 : Blo 1076618 1078599 := bstep (se 1 (by rfl) ⟨808949, by rfl⟩ : syracuseStep 1078599 = 1617899) B1617899
theorem B3634793 : Blo 1076618 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B223803091 : Blo 1076618 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B13827307 : Blo 1076618 13827307 := bstep (se 1 (by rfl) ⟨10370480, by rfl⟩ : syracuseStep 13827307 = 20740961) B20740961
theorem B1080571 : Blo 1076618 1080571 := bstep (se 1 (by rfl) ⟨810428, by rfl⟩ : syracuseStep 1080571 = 1620857) B1620857
theorem B2424311 : Blo 1076618 2424311 := bstep (se 1 (by rfl) ⟨1818233, by rfl⟩ : syracuseStep 2424311 = 3636467) B3636467
theorem B3638249 : Blo 1076618 3638249 := bstep (se 2 (by rfl) ⟨1364343, by rfl⟩ : syracuseStep 3638249 = 2728687) B2728687
theorem B91063759 : Blo 1076618 91063759 := bstep (se 1 (by rfl) ⟨68297819, by rfl⟩ : syracuseStep 91063759 = 136595639) B136595639
theorem B3278561 : Blo 1076618 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B4098347 : Blo 1076618 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B3641003 : Blo 1076618 3641003 := bstep (se 1 (by rfl) ⟨2730752, by rfl⟩ : syracuseStep 3641003 = 5461505) B5461505
theorem B2428667 : Blo 1076618 2428667 := bstep (se 1 (by rfl) ⟨1821500, by rfl⟩ : syracuseStep 2428667 = 3643001) B3643001
theorem B2429567 : Blo 1076618 2429567 := bstep (se 1 (by rfl) ⟨1822175, by rfl⟩ : syracuseStep 2429567 = 3644351) B3644351
theorem B6920063 : Blo 1076618 6920063 := bstep (se 1 (by rfl) ⟨5190047, by rfl⟩ : syracuseStep 6920063 = 10380095) B10380095
theorem B2726075 : Blo 1076618 2726075 := bstep (se 1 (by rfl) ⟨2044556, by rfl⟩ : syracuseStep 2726075 = 4089113) B4089113
theorem B6133967 : Blo 1076618 6133967 := bstep (se 1 (by rfl) ⟨4600475, by rfl⟩ : syracuseStep 6133967 = 9200951) B9200951
theorem B3643703 : Blo 1076618 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B3644999 : Blo 1076618 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B7774375 : Blo 1076618 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B1193616485 : Blo 1076618 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B1616207 : Blo 1076618 1616207 := bstep (se 1 (by rfl) ⟨1212155, by rfl⟩ : syracuseStep 1616207 = 2424311) B2424311
theorem B1617179 : Blo 1076618 1617179 := bstep (se 1 (by rfl) ⟨1212884, by rfl⟩ : syracuseStep 1617179 = 2425769) B2425769
theorem B14036287 : Blo 1076618 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B53162075 : Blo 1076618 53162075 := bstep (se 1 (by rfl) ⟨39871556, by rfl⟩ : syracuseStep 53162075 = 79743113) B79743113
theorem B5452271 : Blo 1076618 5452271 := bstep (se 1 (by rfl) ⟨4089203, by rfl⟩ : syracuseStep 5452271 = 8178407) B8178407
theorem B6141257 : Blo 1076618 6141257 := bstep (se 2 (by rfl) ⟨2302971, by rfl⟩ : syracuseStep 6141257 = 4605943) B4605943
theorem B4602167 : Blo 1076618 4602167 := bstep (se 1 (by rfl) ⟨3451625, by rfl⟩ : syracuseStep 4602167 = 6903251) B6903251
theorem B1620839 : Blo 1076618 1620839 := bstep (se 1 (by rfl) ⟨1215629, by rfl⟩ : syracuseStep 1620839 = 2431259) B2431259
theorem B3884317 : Blo 1076618 3884317 := bstep (se 3 (by rfl) ⟨728309, by rfl⟩ : syracuseStep 3884317 = 1456619) B1456619
theorem B1459615 : Blo 1076618 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B11683399 : Blo 1076618 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B50579621 : Blo 1076618 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B1821467 : Blo 1076618 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B24923173 : Blo 1076618 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B18436409 : Blo 1076618 18436409 := bstep (se 2 (by rfl) ⟨6913653, by rfl⟩ : syracuseStep 18436409 = 13827307) B13827307
theorem B53926903 : Blo 1076618 53926903 := bstep (se 1 (by rfl) ⟨40445177, by rfl⟩ : syracuseStep 53926903 = 80890355) B80890355
theorem B269278465 : Blo 1076618 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B44326253 : Blo 1076618 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B3890879 : Blo 1076618 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B3072667 : Blo 1076618 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B4088657 : Blo 1076618 4088657 := bstep (se 2 (by rfl) ⟨1533246, by rfl⟩ : syracuseStep 4088657 = 3066493) B3066493
theorem B59138909 : Blo 1076618 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B4089811 : Blo 1076618 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B1076783 : Blo 1076618 1076783 := bstep (se 1 (by rfl) ⟨807587, by rfl⟩ : syracuseStep 1076783 = 1615175) B1615175
theorem B1535935 : Blo 1076618 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B1078087 : Blo 1076618 1078087 := bstep (se 1 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 1078087 = 1617131) B1617131
theorem B10384321 : Blo 1076618 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B1078271 : Blo 1076618 1078271 := bstep (se 1 (by rfl) ⟨808703, by rfl⟩ : syracuseStep 1078271 = 1617407) B1617407
theorem B1078495 : Blo 1076618 1078495 := bstep (se 1 (by rfl) ⟨808871, by rfl⟩ : syracuseStep 1078495 = 1617743) B1617743
theorem B2423195 : Blo 1076618 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B2425499 : Blo 1076618 2425499 := bstep (se 1 (by rfl) ⟨1819124, by rfl⟩ : syracuseStep 2425499 = 3638249) B3638249
theorem B4096889 : Blo 1076618 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B33719747 : Blo 1076618 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B1214311 : Blo 1076618 1214311 := bstep (se 1 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 1214311 = 1821467) B1821467
theorem B2427335 : Blo 1076618 2427335 := bstep (se 1 (by rfl) ⟨1820501, by rfl⟩ : syracuseStep 2427335 = 3641003) B3641003
theorem B12290939 : Blo 1076618 12290939 := bstep (se 1 (by rfl) ⟨9218204, by rfl⟩ : syracuseStep 12290939 = 18436409) B18436409
theorem B33230897 : Blo 1076618 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B2429135 : Blo 1076618 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B18715049 : Blo 1076618 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B2429999 : Blo 1076618 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B2593919 : Blo 1076618 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B287610149 : Blo 1076618 287610149 := bstep (se 4 (by rfl) ⟨26963451, by rfl⟩ : syracuseStep 287610149 = 53926903) B53926903
theorem B2725771 : Blo 1076618 2725771 := bstep (se 1 (by rfl) ⟨2044328, by rfl⟩ : syracuseStep 2725771 = 4088657) B4088657
theorem B39425939 : Blo 1076618 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B795744323 : Blo 1076618 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B20716357 : Blo 1076618 20716357 := bstep (se 4 (by rfl) ⟨1942158, by rfl⟩ : syracuseStep 20716357 = 3884317) B3884317
theorem B1615463 : Blo 1076618 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B10365833 : Blo 1076618 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B2732231 : Blo 1076618 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B1946153 : Blo 1076618 1946153 := bstep (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) B1459615
theorem B121418345 : Blo 1076618 121418345 := bstep (se 2 (by rfl) ⟨45531879, by rfl⟩ : syracuseStep 121418345 = 91063759) B91063759
theorem B15577865 : Blo 1076618 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B1619111 : Blo 1076618 1619111 := bstep (se 1 (by rfl) ⟨1214333, by rfl⟩ : syracuseStep 1619111 = 2428667) B2428667
theorem B5453081 : Blo 1076618 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B1619711 : Blo 1076618 1619711 := bstep (se 1 (by rfl) ⟨1214783, by rfl⟩ : syracuseStep 1619711 = 2429567) B2429567
theorem B1817383 : Blo 1076618 1817383 := bstep (se 1 (by rfl) ⟨1363037, by rfl⟩ : syracuseStep 1817383 = 2726075) B2726075
theorem B2047913 : Blo 1076618 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B13845761 : Blo 1076618 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B35441383 : Blo 1076618 35441383 := bstep (se 1 (by rfl) ⟨26581037, by rfl⟩ : syracuseStep 35441383 = 53162075) B53162075
theorem B3068111 : Blo 1076618 3068111 := bstep (se 1 (by rfl) ⟨2301083, by rfl⟩ : syracuseStep 3068111 = 4602167) B4602167
theorem B4613375 : Blo 1076618 4613375 := bstep (se 1 (by rfl) ⟨3460031, by rfl⟩ : syracuseStep 4613375 = 6920063) B6920063
theorem B4089311 : Blo 1076618 4089311 := bstep (se 1 (by rfl) ⟨3066983, by rfl⟩ : syracuseStep 4089311 = 6133967) B6133967
theorem B8742829 : Blo 1076618 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B29550835 : Blo 1076618 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B1077471 : Blo 1076618 1077471 := bstep (se 1 (by rfl) ⟨808103, by rfl⟩ : syracuseStep 1077471 = 1616207) B1616207
theorem B1078119 : Blo 1076618 1078119 := bstep (se 1 (by rfl) ⟨808589, by rfl⟩ : syracuseStep 1078119 = 1617179) B1617179
theorem B3634847 : Blo 1076618 3634847 := bstep (se 1 (by rfl) ⟨2726135, by rfl⟩ : syracuseStep 3634847 = 5452271) B5452271
theorem B4094171 : Blo 1076618 4094171 := bstep (se 1 (by rfl) ⟨3070628, by rfl⟩ : syracuseStep 4094171 = 6141257) B6141257
theorem B359037953 : Blo 1076618 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B1080559 : Blo 1076618 1080559 := bstep (se 1 (by rfl) ⟨810419, by rfl⟩ : syracuseStep 1080559 = 1620839) B1620839
theorem B8193959 : Blo 1076618 8193959 := bstep (se 1 (by rfl) ⟨6145469, by rfl⟩ : syracuseStep 8193959 = 12290939) B12290939
theorem B22153931 : Blo 1076618 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B47255177 : Blo 1076618 47255177 := bstep (se 2 (by rfl) ⟨17720691, by rfl⟩ : syracuseStep 47255177 = 35441383) B35441383
theorem B89919325 : Blo 1076618 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B26283959 : Blo 1076618 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B2726207 : Blo 1076618 2726207 := bstep (se 1 (by rfl) ⟨2044655, by rfl⟩ : syracuseStep 2726207 = 4089311) B4089311
theorem B80945563 : Blo 1076618 80945563 := bstep (se 1 (by rfl) ⟨60709172, by rfl⟩ : syracuseStep 80945563 = 121418345) B121418345
theorem B2729447 : Blo 1076618 2729447 := bstep (se 1 (by rfl) ⟨2047085, by rfl⟩ : syracuseStep 2729447 = 4094171) B4094171
theorem B1616999 : Blo 1076618 1616999 := bstep (se 1 (by rfl) ⟨1212749, by rfl⟩ : syracuseStep 1616999 = 2425499) B2425499
theorem B2731259 : Blo 1076618 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B5189741 : Blo 1076618 5189741 := bstep (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) B1946153
theorem B1618223 : Blo 1076618 1618223 := bstep (se 1 (by rfl) ⟨1213667, by rfl⟩ : syracuseStep 1618223 = 2427335) B2427335
theorem B1619081 : Blo 1076618 1619081 := bstep (se 2 (by rfl) ⟨607155, by rfl⟩ : syracuseStep 1619081 = 1214311) B1214311
theorem B2045407 : Blo 1076618 2045407 := bstep (se 1 (by rfl) ⟨1534055, by rfl⟩ : syracuseStep 2045407 = 3068111) B3068111
theorem B1619423 : Blo 1076618 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B39401113 : Blo 1076618 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B1619999 : Blo 1076618 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B530496215 : Blo 1076618 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B1821487 : Blo 1076618 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B239358635 : Blo 1076618 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B1365275 : Blo 1076618 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B9230507 : Blo 1076618 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B11657105 : Blo 1076618 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B12476699 : Blo 1076618 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B1729279 : Blo 1076618 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B766960397 : Blo 1076618 766960397 := bstep (se 3 (by rfl) ⟨143805074, by rfl⟩ : syracuseStep 766960397 = 287610149) B287610149
theorem B3075583 : Blo 1076618 3075583 := bstep (se 1 (by rfl) ⟨2306687, by rfl⟩ : syracuseStep 3075583 = 4613375) B4613375
theorem B1076975 : Blo 1076618 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B6910555 : Blo 1076618 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B3634361 : Blo 1076618 3634361 := bstep (se 2 (by rfl) ⟨1362885, by rfl⟩ : syracuseStep 3634361 = 2725771) B2725771
theorem B10385243 : Blo 1076618 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B1079407 : Blo 1076618 1079407 := bstep (se 1 (by rfl) ⟨809555, by rfl⟩ : syracuseStep 1079407 = 1619111) B1619111
theorem B3635387 : Blo 1076618 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B2423177 : Blo 1076618 2423177 := bstep (se 2 (by rfl) ⟨908691, by rfl⟩ : syracuseStep 2423177 = 1817383) B1817383
theorem B27621809 : Blo 1076618 27621809 := bstep (se 2 (by rfl) ⟨10358178, by rfl⟩ : syracuseStep 27621809 = 20716357) B20716357
theorem B2423231 : Blo 1076618 2423231 := bstep (se 1 (by rfl) ⟨1817423, by rfl⟩ : syracuseStep 2423231 = 3634847) B3634847
theorem B1079807 : Blo 1076618 1079807 := bstep (se 1 (by rfl) ⟨809855, by rfl⟩ : syracuseStep 1079807 = 1619711) B1619711
theorem B3640733 : Blo 1076618 3640733 := bstep (se 3 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 3640733 = 1365275) B1365275
theorem B2428649 : Blo 1076618 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B4100777 : Blo 1076618 4100777 := bstep (se 2 (by rfl) ⟨1537791, by rfl⟩ : syracuseStep 4100777 = 3075583) B3075583
theorem B7771403 : Blo 1076618 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B9214073 : Blo 1076618 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B2727209 : Blo 1076618 2727209 := bstep (se 2 (by rfl) ⟨1022703, by rfl⟩ : syracuseStep 2727209 = 2045407) B2045407
theorem B52534817 : Blo 1076618 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B6923495 : Blo 1076618 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B1615451 : Blo 1076618 1615451 := bstep (se 1 (by rfl) ⟨1211588, by rfl⟩ : syracuseStep 1615451 = 2423177) B2423177
theorem B1615487 : Blo 1076618 1615487 := bstep (se 1 (by rfl) ⟨1211615, by rfl⟩ : syracuseStep 1615487 = 2423231) B2423231
theorem B479569733 : Blo 1076618 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B31503451 : Blo 1076618 31503451 := bstep (se 1 (by rfl) ⟨23627588, by rfl⟩ : syracuseStep 31503451 = 47255177) B47255177
theorem B9222821 : Blo 1076618 9222821 := bstep (se 4 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 9222821 = 1729279) B1729279
theorem B1817471 : Blo 1076618 1817471 := bstep (se 1 (by rfl) ⟨1363103, by rfl⟩ : syracuseStep 1817471 = 2726207) B2726207
theorem B1819631 : Blo 1076618 1819631 := bstep (se 1 (by rfl) ⟨1364723, by rfl⟩ : syracuseStep 1819631 = 2729447) B2729447
theorem B1820839 : Blo 1076618 1820839 := bstep (se 1 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 1820839 = 2731259) B2731259
theorem B3459827 : Blo 1076618 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B107927417 : Blo 1076618 107927417 := bstep (se 2 (by rfl) ⟨40472781, by rfl⟩ : syracuseStep 107927417 = 80945563) B80945563
theorem B5462639 : Blo 1076618 5462639 := bstep (se 1 (by rfl) ⟨4096979, by rfl⟩ : syracuseStep 5462639 = 8193959) B8193959
theorem B14769287 : Blo 1076618 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B17522639 : Blo 1076618 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B159572423 : Blo 1076618 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B6153671 : Blo 1076618 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B8317799 : Blo 1076618 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B511306931 : Blo 1076618 511306931 := bstep (se 1 (by rfl) ⟨383480198, by rfl⟩ : syracuseStep 511306931 = 766960397) B766960397
theorem B1077999 : Blo 1076618 1077999 := bstep (se 1 (by rfl) ⟨808499, by rfl⟩ : syracuseStep 1077999 = 1616999) B1616999
theorem B1078815 : Blo 1076618 1078815 := bstep (se 1 (by rfl) ⟨809111, by rfl⟩ : syracuseStep 1078815 = 1618223) B1618223
theorem B1079387 : Blo 1076618 1079387 := bstep (se 1 (by rfl) ⟨809540, by rfl⟩ : syracuseStep 1079387 = 1619081) B1619081
theorem B2422907 : Blo 1076618 2422907 := bstep (se 1 (by rfl) ⟨1817180, by rfl⟩ : syracuseStep 2422907 = 3634361) B3634361
theorem B1079615 : Blo 1076618 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B1079999 : Blo 1076618 1079999 := bstep (se 1 (by rfl) ⟨809999, by rfl⟩ : syracuseStep 1079999 = 1619999) B1619999
theorem B2423591 : Blo 1076618 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B18414539 : Blo 1076618 18414539 := bstep (se 1 (by rfl) ⟨13810904, by rfl⟩ : syracuseStep 18414539 = 27621809) B27621809
theorem B353664143 : Blo 1076618 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B1213087 : Blo 1076618 1213087 := bstep (se 1 (by rfl) ⟨909815, by rfl⟩ : syracuseStep 1213087 = 1819631) B1819631
theorem B2427155 : Blo 1076618 2427155 := bstep (se 1 (by rfl) ⟨1820366, by rfl⟩ : syracuseStep 2427155 = 3640733) B3640733
theorem B2427785 : Blo 1076618 2427785 := bstep (se 2 (by rfl) ⟨910419, by rfl⟩ : syracuseStep 2427785 = 1820839) B1820839
theorem B5180935 : Blo 1076618 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B3641759 : Blo 1076618 3641759 := bstep (se 1 (by rfl) ⟨2731319, by rfl⟩ : syracuseStep 3641759 = 5462639) B5462639
theorem B287806445 : Blo 1076618 287806445 := bstep (se 3 (by rfl) ⟨53963708, by rfl⟩ : syracuseStep 287806445 = 107927417) B107927417
theorem B4102447 : Blo 1076618 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B5545199 : Blo 1076618 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B1615271 : Blo 1076618 1615271 := bstep (se 1 (by rfl) ⟨1211453, by rfl⟩ : syracuseStep 1615271 = 2422907) B2422907
theorem B1615727 : Blo 1076618 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B235776095 : Blo 1076618 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B2306551 : Blo 1076618 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B1619099 : Blo 1076618 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B2733851 : Blo 1076618 2733851 := bstep (se 1 (by rfl) ⟨2050388, by rfl⟩ : syracuseStep 2733851 = 4100777) B4100777
theorem B18462653 : Blo 1076618 18462653 := bstep (se 3 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 18462653 = 6923495) B6923495
theorem B6142715 : Blo 1076618 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B9846191 : Blo 1076618 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B1818139 : Blo 1076618 1818139 := bstep (se 1 (by rfl) ⟨1363604, by rfl⟩ : syracuseStep 1818139 = 2727209) B2727209
theorem B11681759 : Blo 1076618 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B106381615 : Blo 1076618 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B340871287 : Blo 1076618 340871287 := bstep (se 1 (by rfl) ⟨255653465, by rfl⟩ : syracuseStep 340871287 = 511306931) B511306931
theorem B6148547 : Blo 1076618 6148547 := bstep (se 1 (by rfl) ⟨4611410, by rfl⟩ : syracuseStep 6148547 = 9222821) B9222821
theorem B12276359 : Blo 1076618 12276359 := bstep (se 1 (by rfl) ⟨9207269, by rfl⟩ : syracuseStep 12276359 = 18414539) B18414539
theorem B35023211 : Blo 1076618 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B1076967 : Blo 1076618 1076967 := bstep (se 1 (by rfl) ⟨807725, by rfl⟩ : syracuseStep 1076967 = 1615451) B1615451
theorem B1076991 : Blo 1076618 1076991 := bstep (se 1 (by rfl) ⟨807743, by rfl⟩ : syracuseStep 1076991 = 1615487) B1615487
theorem B319713155 : Blo 1076618 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B42004601 : Blo 1076618 42004601 := bstep (se 2 (by rfl) ⟨15751725, by rfl⟩ : syracuseStep 42004601 = 31503451) B31503451
theorem B1211647 : Blo 1076618 1211647 := bstep (se 1 (by rfl) ⟨908735, by rfl⟩ : syracuseStep 1211647 = 1817471) B1817471
theorem B454495049 : Blo 1076618 454495049 := bstep (se 2 (by rfl) ⟨170435643, by rfl⟩ : syracuseStep 454495049 = 340871287) B340871287
theorem B2427839 : Blo 1076618 2427839 := bstep (se 1 (by rfl) ⟨1820879, by rfl⟩ : syracuseStep 2427839 = 3641759) B3641759
theorem B4099031 : Blo 1076618 4099031 := bstep (se 1 (by rfl) ⟨3074273, by rfl⟩ : syracuseStep 4099031 = 6148547) B6148547
theorem B14787197 : Blo 1076618 14787197 := bstep (se 3 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 14787197 = 5545199) B5545199
theorem B1615529 : Blo 1076618 1615529 := bstep (se 2 (by rfl) ⟨605823, by rfl⟩ : syracuseStep 1615529 = 1211647) B1211647
theorem B6564127 : Blo 1076618 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B1617449 : Blo 1076618 1617449 := bstep (se 2 (by rfl) ⟨606543, by rfl⟩ : syracuseStep 1617449 = 1213087) B1213087
theorem B1618103 : Blo 1076618 1618103 := bstep (se 1 (by rfl) ⟨1213577, by rfl⟩ : syracuseStep 1618103 = 2427155) B2427155
theorem B1618523 : Blo 1076618 1618523 := bstep (se 1 (by rfl) ⟨1213892, by rfl⟩ : syracuseStep 1618523 = 2427785) B2427785
theorem B191870963 : Blo 1076618 191870963 := bstep (se 1 (by rfl) ⟨143903222, by rfl⟩ : syracuseStep 191870963 = 287806445) B287806445
theorem B23348807 : Blo 1076618 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B213142103 : Blo 1076618 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B28003067 : Blo 1076618 28003067 := bstep (se 1 (by rfl) ⟨21002300, by rfl⟩ : syracuseStep 28003067 = 42004601) B42004601
theorem B1822567 : Blo 1076618 1822567 := bstep (se 1 (by rfl) ⟨1366925, by rfl⟩ : syracuseStep 1822567 = 2733851) B2733851
theorem B12308435 : Blo 1076618 12308435 := bstep (se 1 (by rfl) ⟨9231326, by rfl⟩ : syracuseStep 12308435 = 18462653) B18462653
theorem B7787839 : Blo 1076618 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B141842153 : Blo 1076618 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B8184239 : Blo 1076618 8184239 := bstep (se 1 (by rfl) ⟨6138179, by rfl⟩ : syracuseStep 8184239 = 12276359) B12276359
theorem B6907913 : Blo 1076618 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B3075401 : Blo 1076618 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B1076847 : Blo 1076618 1076847 := bstep (se 1 (by rfl) ⟨807635, by rfl⟩ : syracuseStep 1076847 = 1615271) B1615271
theorem B1077151 : Blo 1076618 1077151 := bstep (se 1 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 1077151 = 1615727) B1615727
theorem B157184063 : Blo 1076618 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B5469929 : Blo 1076618 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B1079399 : Blo 1076618 1079399 := bstep (se 1 (by rfl) ⟨809549, by rfl⟩ : syracuseStep 1079399 = 1619099) B1619099
theorem B4095143 : Blo 1076618 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2424185 : Blo 1076618 2424185 := bstep (se 2 (by rfl) ⟨909069, by rfl⟩ : syracuseStep 2424185 = 1818139) B1818139
theorem B15565871 : Blo 1076618 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B8752169 : Blo 1076618 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B2430089 : Blo 1076618 2430089 := bstep (se 2 (by rfl) ⟨911283, by rfl⟩ : syracuseStep 2430089 = 1822567) B1822567
theorem B3646619 : Blo 1076618 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B2730095 : Blo 1076618 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B1616123 : Blo 1076618 1616123 := bstep (se 1 (by rfl) ⟨1212092, by rfl⟩ : syracuseStep 1616123 = 2424185) B2424185
theorem B142094735 : Blo 1076618 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B1618559 : Blo 1076618 1618559 := bstep (se 1 (by rfl) ⟨1213919, by rfl⟩ : syracuseStep 1618559 = 2427839) B2427839
theorem B2732687 : Blo 1076618 2732687 := bstep (se 1 (by rfl) ⟨2049515, by rfl⟩ : syracuseStep 2732687 = 4099031) B4099031
theorem B8205623 : Blo 1076618 8205623 := bstep (se 1 (by rfl) ⟨6154217, by rfl⟩ : syracuseStep 8205623 = 12308435) B12308435
theorem B5456159 : Blo 1076618 5456159 := bstep (se 1 (by rfl) ⟨4092119, by rfl⟩ : syracuseStep 5456159 = 8184239) B8184239
theorem B4605275 : Blo 1076618 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B2050267 : Blo 1076618 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B127913975 : Blo 1076618 127913975 := bstep (se 1 (by rfl) ⟨95935481, by rfl⟩ : syracuseStep 127913975 = 191870963) B191870963
theorem B18668711 : Blo 1076618 18668711 := bstep (se 1 (by rfl) ⟨14001533, by rfl⟩ : syracuseStep 18668711 = 28003067) B28003067
theorem B302996699 : Blo 1076618 302996699 := bstep (se 1 (by rfl) ⟨227247524, by rfl⟩ : syracuseStep 302996699 = 454495049) B454495049
theorem B94561435 : Blo 1076618 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B9858131 : Blo 1076618 9858131 := bstep (se 1 (by rfl) ⟨7393598, by rfl⟩ : syracuseStep 9858131 = 14787197) B14787197
theorem B1077019 : Blo 1076618 1077019 := bstep (se 1 (by rfl) ⟨807764, by rfl⟩ : syracuseStep 1077019 = 1615529) B1615529
theorem B10383785 : Blo 1076618 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B1078299 : Blo 1076618 1078299 := bstep (se 1 (by rfl) ⟨808724, by rfl⟩ : syracuseStep 1078299 = 1617449) B1617449
theorem B104789375 : Blo 1076618 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B1078735 : Blo 1076618 1078735 := bstep (se 1 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 1078735 = 1618103) B1618103
theorem B1079015 : Blo 1076618 1079015 := bstep (se 1 (by rfl) ⟨809261, by rfl⟩ : syracuseStep 1079015 = 1618523) B1618523
theorem B3637439 : Blo 1076618 3637439 := bstep (se 1 (by rfl) ⟨2728079, by rfl⟩ : syracuseStep 3637439 = 5456159) B5456159
theorem B2431079 : Blo 1076618 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B23339117 : Blo 1076618 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B6922523 : Blo 1076618 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B85275983 : Blo 1076618 85275983 := bstep (se 1 (by rfl) ⟨63956987, by rfl⟩ : syracuseStep 85275983 = 127913975) B127913975
theorem B2733689 : Blo 1076618 2733689 := bstep (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) B2050267
theorem B1620059 : Blo 1076618 1620059 := bstep (se 1 (by rfl) ⟨1215044, by rfl⟩ : syracuseStep 1620059 = 2430089) B2430089
theorem B201997799 : Blo 1076618 201997799 := bstep (se 1 (by rfl) ⟨151498349, by rfl⟩ : syracuseStep 201997799 = 302996699) B302996699
theorem B1820063 : Blo 1076618 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B6572087 : Blo 1076618 6572087 := bstep (se 1 (by rfl) ⟨4929065, by rfl⟩ : syracuseStep 6572087 = 9858131) B9858131
theorem B1821791 : Blo 1076618 1821791 := bstep (se 1 (by rfl) ⟨1366343, by rfl⟩ : syracuseStep 1821791 = 2732687) B2732687
theorem B10377247 : Blo 1076618 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B12280733 : Blo 1076618 12280733 := bstep (se 3 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 12280733 = 4605275) B4605275
theorem B12445807 : Blo 1076618 12445807 := bstep (se 1 (by rfl) ⟨9334355, by rfl⟩ : syracuseStep 12445807 = 18668711) B18668711
theorem B504327653 : Blo 1076618 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B1077415 : Blo 1076618 1077415 := bstep (se 1 (by rfl) ⟨808061, by rfl⟩ : syracuseStep 1077415 = 1616123) B1616123
theorem B94729823 : Blo 1076618 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1079039 : Blo 1076618 1079039 := bstep (se 1 (by rfl) ⟨809279, by rfl⟩ : syracuseStep 1079039 = 1618559) B1618559
theorem B5470415 : Blo 1076618 5470415 := bstep (se 1 (by rfl) ⟨4102811, by rfl⟩ : syracuseStep 5470415 = 8205623) B8205623
theorem B69859583 : Blo 1076618 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B2424959 : Blo 1076618 2424959 := bstep (se 1 (by rfl) ⟨1818719, by rfl⟩ : syracuseStep 2424959 = 3637439) B3637439
theorem B1213375 : Blo 1076618 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B1214527 : Blo 1076618 1214527 := bstep (se 1 (by rfl) ⟨910895, by rfl⟩ : syracuseStep 1214527 = 1821791) B1821791
theorem B13836329 : Blo 1076618 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B63153215 : Blo 1076618 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B3646943 : Blo 1076618 3646943 := bstep (se 1 (by rfl) ⟨2735207, by rfl⟩ : syracuseStep 3646943 = 5470415) B5470415
theorem B46573055 : Blo 1076618 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B62237645 : Blo 1076618 62237645 := bstep (se 3 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 62237645 = 23339117) B23339117
theorem B16594409 : Blo 1076618 16594409 := bstep (se 2 (by rfl) ⟨6222903, by rfl⟩ : syracuseStep 16594409 = 12445807) B12445807
theorem B1620719 : Blo 1076618 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B336218435 : Blo 1076618 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B1822459 : Blo 1076618 1822459 := bstep (se 1 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 1822459 = 2733689) B2733689
theorem B134665199 : Blo 1076618 134665199 := bstep (se 1 (by rfl) ⟨100998899, by rfl⟩ : syracuseStep 134665199 = 201997799) B201997799
theorem B4381391 : Blo 1076618 4381391 := bstep (se 1 (by rfl) ⟨3286043, by rfl⟩ : syracuseStep 4381391 = 6572087) B6572087
theorem B4615015 : Blo 1076618 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B8187155 : Blo 1076618 8187155 := bstep (se 1 (by rfl) ⟨6140366, by rfl⟩ : syracuseStep 8187155 = 12280733) B12280733
theorem B56850655 : Blo 1076618 56850655 := bstep (se 1 (by rfl) ⟨42637991, by rfl⟩ : syracuseStep 56850655 = 85275983) B85275983
theorem B1080039 : Blo 1076618 1080039 := bstep (se 1 (by rfl) ⟨810029, by rfl⟩ : syracuseStep 1080039 = 1620059) B1620059
theorem B2920927 : Blo 1076618 2920927 := bstep (se 1 (by rfl) ⟨2190695, by rfl⟩ : syracuseStep 2920927 = 4381391) B4381391
theorem B2429945 : Blo 1076618 2429945 := bstep (se 2 (by rfl) ⟨911229, by rfl⟩ : syracuseStep 2429945 = 1822459) B1822459
theorem B2431295 : Blo 1076618 2431295 := bstep (se 1 (by rfl) ⟨1823471, by rfl⟩ : syracuseStep 2431295 = 3646943) B3646943
theorem B41491763 : Blo 1076618 41491763 := bstep (se 1 (by rfl) ⟨31118822, by rfl⟩ : syracuseStep 41491763 = 62237645) B62237645
theorem B75800873 : Blo 1076618 75800873 := bstep (se 2 (by rfl) ⟨28425327, by rfl⟩ : syracuseStep 75800873 = 56850655) B56850655
theorem B1616639 : Blo 1076618 1616639 := bstep (se 1 (by rfl) ⟨1212479, by rfl⟩ : syracuseStep 1616639 = 2424959) B2424959
theorem B1617833 : Blo 1076618 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B224145623 : Blo 1076618 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B1619369 : Blo 1076618 1619369 := bstep (se 2 (by rfl) ⟨607263, by rfl⟩ : syracuseStep 1619369 = 1214527) B1214527
theorem B9224219 : Blo 1076618 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B31048703 : Blo 1076618 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B5458103 : Blo 1076618 5458103 := bstep (se 1 (by rfl) ⟨4093577, by rfl⟩ : syracuseStep 5458103 = 8187155) B8187155
theorem B11062939 : Blo 1076618 11062939 := bstep (se 1 (by rfl) ⟨8297204, by rfl⟩ : syracuseStep 11062939 = 16594409) B16594409
theorem B89776799 : Blo 1076618 89776799 := bstep (se 1 (by rfl) ⟨67332599, by rfl⟩ : syracuseStep 89776799 = 134665199) B134665199
theorem B6153353 : Blo 1076618 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B42102143 : Blo 1076618 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B1080479 : Blo 1076618 1080479 := bstep (se 1 (by rfl) ⟨810359, by rfl⟩ : syracuseStep 1080479 = 1620719) B1620719
theorem B3638735 : Blo 1076618 3638735 := bstep (se 1 (by rfl) ⟨2729051, by rfl⟩ : syracuseStep 3638735 = 5458103) B5458103
theorem B27661175 : Blo 1076618 27661175 := bstep (se 1 (by rfl) ⟨20745881, by rfl⟩ : syracuseStep 27661175 = 41491763) B41491763
theorem B14750585 : Blo 1076618 14750585 := bstep (se 2 (by rfl) ⟨5531469, by rfl⟩ : syracuseStep 14750585 = 11062939) B11062939
theorem B50533915 : Blo 1076618 50533915 := bstep (se 1 (by rfl) ⟨37900436, by rfl⟩ : syracuseStep 50533915 = 75800873) B75800873
theorem B4102235 : Blo 1076618 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B149430415 : Blo 1076618 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B1619963 : Blo 1076618 1619963 := bstep (se 1 (by rfl) ⟨1214972, by rfl⟩ : syracuseStep 1619963 = 2429945) B2429945
theorem B1620863 : Blo 1076618 1620863 := bstep (se 1 (by rfl) ⟨1215647, by rfl⟩ : syracuseStep 1620863 = 2431295) B2431295
theorem B59851199 : Blo 1076618 59851199 := bstep (se 1 (by rfl) ⟨44888399, by rfl⟩ : syracuseStep 59851199 = 89776799) B89776799
theorem B28068095 : Blo 1076618 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B6149479 : Blo 1076618 6149479 := bstep (se 1 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 6149479 = 9224219) B9224219
theorem B20699135 : Blo 1076618 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B3894569 : Blo 1076618 3894569 := bstep (se 2 (by rfl) ⟨1460463, by rfl⟩ : syracuseStep 3894569 = 2920927) B2920927
theorem B1077759 : Blo 1076618 1077759 := bstep (se 1 (by rfl) ⟨808319, by rfl⟩ : syracuseStep 1077759 = 1616639) B1616639
theorem B1078555 : Blo 1076618 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B1079579 : Blo 1076618 1079579 := bstep (se 1 (by rfl) ⟨809684, by rfl⟩ : syracuseStep 1079579 = 1619369) B1619369
theorem B2425823 : Blo 1076618 2425823 := bstep (se 1 (by rfl) ⟨1819367, by rfl⟩ : syracuseStep 2425823 = 3638735) B3638735
theorem B18712063 : Blo 1076618 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B9833723 : Blo 1076618 9833723 := bstep (se 1 (by rfl) ⟨7375292, by rfl⟩ : syracuseStep 9833723 = 14750585) B14750585
theorem B13799423 : Blo 1076618 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B8199305 : Blo 1076618 8199305 := bstep (se 2 (by rfl) ⟨3074739, by rfl⟩ : syracuseStep 8199305 = 6149479) B6149479
theorem B67378553 : Blo 1076618 67378553 := bstep (se 2 (by rfl) ⟨25266957, by rfl⟩ : syracuseStep 67378553 = 50533915) B50533915
theorem B2596379 : Blo 1076618 2596379 := bstep (se 1 (by rfl) ⟨1947284, by rfl⟩ : syracuseStep 2596379 = 3894569) B3894569
theorem B199240553 : Blo 1076618 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B2734823 : Blo 1076618 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B39900799 : Blo 1076618 39900799 := bstep (se 1 (by rfl) ⟨29925599, by rfl⟩ : syracuseStep 39900799 = 59851199) B59851199
theorem B18440783 : Blo 1076618 18440783 := bstep (se 1 (by rfl) ⟨13830587, by rfl⟩ : syracuseStep 18440783 = 27661175) B27661175
theorem B1079975 : Blo 1076618 1079975 := bstep (se 1 (by rfl) ⟨809981, by rfl⟩ : syracuseStep 1079975 = 1619963) B1619963
theorem B1080575 : Blo 1076618 1080575 := bstep (se 1 (by rfl) ⟨810431, by rfl⟩ : syracuseStep 1080575 = 1620863) B1620863
theorem B6555815 : Blo 1076618 6555815 := bstep (se 1 (by rfl) ⟨4916861, by rfl⟩ : syracuseStep 6555815 = 9833723) B9833723
theorem B12293855 : Blo 1076618 12293855 := bstep (se 1 (by rfl) ⟨9220391, by rfl⟩ : syracuseStep 12293855 = 18440783) B18440783
theorem B6923677 : Blo 1076618 6923677 := bstep (se 3 (by rfl) ⟨1298189, by rfl⟩ : syracuseStep 6923677 = 2596379) B2596379
theorem B1617215 : Blo 1076618 1617215 := bstep (se 1 (by rfl) ⟨1212911, by rfl⟩ : syracuseStep 1617215 = 2425823) B2425823
theorem B24949417 : Blo 1076618 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B132827035 : Blo 1076618 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B53201065 : Blo 1076618 53201065 := bstep (se 2 (by rfl) ⟨19950399, by rfl⟩ : syracuseStep 53201065 = 39900799) B39900799
theorem B1823215 : Blo 1076618 1823215 := bstep (se 1 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 1823215 = 2734823) B2734823
theorem B9199615 : Blo 1076618 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B5466203 : Blo 1076618 5466203 := bstep (se 1 (by rfl) ⟨4099652, by rfl⟩ : syracuseStep 5466203 = 8199305) B8199305
theorem B44919035 : Blo 1076618 44919035 := bstep (se 1 (by rfl) ⟨33689276, by rfl⟩ : syracuseStep 44919035 = 67378553) B67378553
theorem B8195903 : Blo 1076618 8195903 := bstep (se 1 (by rfl) ⟨6146927, by rfl⟩ : syracuseStep 8195903 = 12293855) B12293855
theorem B2430953 : Blo 1076618 2430953 := bstep (se 2 (by rfl) ⟨911607, by rfl⟩ : syracuseStep 2430953 = 1823215) B1823215
theorem B33265889 : Blo 1076618 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B3644135 : Blo 1076618 3644135 := bstep (se 1 (by rfl) ⟨2733101, by rfl⟩ : syracuseStep 3644135 = 5466203) B5466203
theorem B12266153 : Blo 1076618 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B4370543 : Blo 1076618 4370543 := bstep (se 1 (by rfl) ⟨3277907, by rfl⟩ : syracuseStep 4370543 = 6555815) B6555815
theorem B9231569 : Blo 1076618 9231569 := bstep (se 2 (by rfl) ⟨3461838, by rfl⟩ : syracuseStep 9231569 = 6923677) B6923677
theorem B177102713 : Blo 1076618 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B70934753 : Blo 1076618 70934753 := bstep (se 2 (by rfl) ⟨26600532, by rfl⟩ : syracuseStep 70934753 = 53201065) B53201065
theorem B29946023 : Blo 1076618 29946023 := bstep (se 1 (by rfl) ⟨22459517, by rfl⟩ : syracuseStep 29946023 = 44919035) B44919035
theorem B1078143 : Blo 1076618 1078143 := bstep (se 1 (by rfl) ⟨808607, by rfl⟩ : syracuseStep 1078143 = 1617215) B1617215
theorem B2429423 : Blo 1076618 2429423 := bstep (se 1 (by rfl) ⟨1822067, by rfl⟩ : syracuseStep 2429423 = 3644135) B3644135
theorem B118068475 : Blo 1076618 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B47289835 : Blo 1076618 47289835 := bstep (se 1 (by rfl) ⟨35467376, by rfl⟩ : syracuseStep 47289835 = 70934753) B70934753
theorem B19964015 : Blo 1076618 19964015 := bstep (se 1 (by rfl) ⟨14973011, by rfl⟩ : syracuseStep 19964015 = 29946023) B29946023
theorem B1620635 : Blo 1076618 1620635 := bstep (se 1 (by rfl) ⟨1215476, by rfl⟩ : syracuseStep 1620635 = 2430953) B2430953
theorem B8177435 : Blo 1076618 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B5463935 : Blo 1076618 5463935 := bstep (se 1 (by rfl) ⟨4097951, by rfl⟩ : syracuseStep 5463935 = 8195903) B8195903
theorem B22177259 : Blo 1076618 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B6154379 : Blo 1076618 6154379 := bstep (se 1 (by rfl) ⟨4615784, by rfl⟩ : syracuseStep 6154379 = 9231569) B9231569
theorem B2913695 : Blo 1076618 2913695 := bstep (se 1 (by rfl) ⟨2185271, by rfl⟩ : syracuseStep 2913695 = 4370543) B4370543
theorem B3642623 : Blo 1076618 3642623 := bstep (se 1 (by rfl) ⟨2731967, by rfl⟩ : syracuseStep 3642623 = 5463935) B5463935
theorem B13309343 : Blo 1076618 13309343 := bstep (se 1 (by rfl) ⟨9982007, by rfl⟩ : syracuseStep 13309343 = 19964015) B19964015
theorem B14784839 : Blo 1076618 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B4102919 : Blo 1076618 4102919 := bstep (se 1 (by rfl) ⟨3077189, by rfl⟩ : syracuseStep 4102919 = 6154379) B6154379
theorem B157424633 : Blo 1076618 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B63053113 : Blo 1076618 63053113 := bstep (se 2 (by rfl) ⟨23644917, by rfl⟩ : syracuseStep 63053113 = 47289835) B47289835
theorem B1942463 : Blo 1076618 1942463 := bstep (se 1 (by rfl) ⟨1456847, by rfl⟩ : syracuseStep 1942463 = 2913695) B2913695
theorem B5451623 : Blo 1076618 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B1619615 : Blo 1076618 1619615 := bstep (se 1 (by rfl) ⟨1214711, by rfl⟩ : syracuseStep 1619615 = 2429423) B2429423
theorem B1080423 : Blo 1076618 1080423 := bstep (se 1 (by rfl) ⟨810317, by rfl⟩ : syracuseStep 1080423 = 1620635) B1620635
theorem B2428415 : Blo 1076618 2428415 := bstep (se 1 (by rfl) ⟨1821311, by rfl⟩ : syracuseStep 2428415 = 3642623) B3642623
theorem B2735279 : Blo 1076618 2735279 := bstep (se 1 (by rfl) ⟨2051459, by rfl⟩ : syracuseStep 2735279 = 4102919) B4102919
theorem B1294975 : Blo 1076618 1294975 := bstep (se 1 (by rfl) ⟨971231, by rfl⟩ : syracuseStep 1294975 = 1942463) B1942463
theorem B84070817 : Blo 1076618 84070817 := bstep (se 2 (by rfl) ⟨31526556, by rfl⟩ : syracuseStep 84070817 = 63053113) B63053113
theorem B8872895 : Blo 1076618 8872895 := bstep (se 1 (by rfl) ⟨6654671, by rfl⟩ : syracuseStep 8872895 = 13309343) B13309343
theorem B9856559 : Blo 1076618 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B104949755 : Blo 1076618 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B3634415 : Blo 1076618 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B1079743 : Blo 1076618 1079743 := bstep (se 1 (by rfl) ⟨809807, by rfl⟩ : syracuseStep 1079743 = 1619615) B1619615
theorem B69966503 : Blo 1076618 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B1618943 : Blo 1076618 1618943 := bstep (se 1 (by rfl) ⟨1214207, by rfl⟩ : syracuseStep 1618943 = 2428415) B2428415
theorem B56047211 : Blo 1076618 56047211 := bstep (se 1 (by rfl) ⟨42035408, by rfl⟩ : syracuseStep 56047211 = 84070817) B84070817
theorem B5915263 : Blo 1076618 5915263 := bstep (se 1 (by rfl) ⟨4436447, by rfl⟩ : syracuseStep 5915263 = 8872895) B8872895
theorem B6571039 : Blo 1076618 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B1823519 : Blo 1076618 1823519 := bstep (se 1 (by rfl) ⟨1367639, by rfl⟩ : syracuseStep 1823519 = 2735279) B2735279
theorem B1726633 : Blo 1076618 1726633 := bstep (se 2 (by rfl) ⟨647487, by rfl⟩ : syracuseStep 1726633 = 1294975) B1294975
theorem B2422943 : Blo 1076618 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B1215679 : Blo 1076618 1215679 := bstep (se 1 (by rfl) ⟨911759, by rfl⟩ : syracuseStep 1215679 = 1823519) B1823519
theorem B2302177 : Blo 1076618 2302177 := bstep (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) B1726633
theorem B37364807 : Blo 1076618 37364807 := bstep (se 1 (by rfl) ⟨28023605, by rfl⟩ : syracuseStep 37364807 = 56047211) B56047211
theorem B1615295 : Blo 1076618 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B8761385 : Blo 1076618 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B46644335 : Blo 1076618 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B7887017 : Blo 1076618 7887017 := bstep (se 2 (by rfl) ⟨2957631, by rfl⟩ : syracuseStep 7887017 = 5915263) B5915263
theorem B1079295 : Blo 1076618 1079295 := bstep (se 1 (by rfl) ⟨809471, by rfl⟩ : syracuseStep 1079295 = 1618943) B1618943
theorem B24909871 : Blo 1076618 24909871 := bstep (se 1 (by rfl) ⟨18682403, by rfl⟩ : syracuseStep 24909871 = 37364807) B37364807
theorem B5840923 : Blo 1076618 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B1620905 : Blo 1076618 1620905 := bstep (se 2 (by rfl) ⟨607839, by rfl⟩ : syracuseStep 1620905 = 1215679) B1215679
theorem B3069569 : Blo 1076618 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B21032045 : Blo 1076618 21032045 := bstep (se 3 (by rfl) ⟨3943508, by rfl⟩ : syracuseStep 21032045 = 7887017) B7887017
theorem B1076863 : Blo 1076618 1076863 := bstep (se 1 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 1076863 = 1615295) B1615295
theorem B31096223 : Blo 1076618 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B2046379 : Blo 1076618 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B33213161 : Blo 1076618 33213161 := bstep (se 2 (by rfl) ⟨12454935, by rfl⟩ : syracuseStep 33213161 = 24909871) B24909871
theorem B20730815 : Blo 1076618 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B7787897 : Blo 1076618 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B14021363 : Blo 1076618 14021363 := bstep (se 1 (by rfl) ⟨10516022, by rfl⟩ : syracuseStep 14021363 = 21032045) B21032045
theorem B1080603 : Blo 1076618 1080603 := bstep (se 1 (by rfl) ⟨810452, by rfl⟩ : syracuseStep 1080603 = 1620905) B1620905
theorem B37390301 : Blo 1076618 37390301 := bstep (se 3 (by rfl) ⟨7010681, by rfl⟩ : syracuseStep 37390301 = 14021363) B14021363
theorem B2728505 : Blo 1076618 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B5191931 : Blo 1076618 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B22142107 : Blo 1076618 22142107 := bstep (se 1 (by rfl) ⟨16606580, by rfl⟩ : syracuseStep 22142107 = 33213161) B33213161
theorem B13820543 : Blo 1076618 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B9213695 : Blo 1076618 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B1819003 : Blo 1076618 1819003 := bstep (se 1 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 1819003 = 2728505) B2728505
theorem B3461287 : Blo 1076618 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B24926867 : Blo 1076618 24926867 := bstep (se 1 (by rfl) ⟨18695150, by rfl⟩ : syracuseStep 24926867 = 37390301) B37390301
theorem B29522809 : Blo 1076618 29522809 := bstep (se 2 (by rfl) ⟨11071053, by rfl⟩ : syracuseStep 29522809 = 22142107) B22142107
theorem B2425337 : Blo 1076618 2425337 := bstep (se 2 (by rfl) ⟨909501, by rfl⟩ : syracuseStep 2425337 = 1819003) B1819003
theorem B16617911 : Blo 1076618 16617911 := bstep (se 1 (by rfl) ⟨12463433, by rfl⟩ : syracuseStep 16617911 = 24926867) B24926867
theorem B39363745 : Blo 1076618 39363745 := bstep (se 2 (by rfl) ⟨14761404, by rfl⟩ : syracuseStep 39363745 = 29522809) B29522809
theorem B6142463 : Blo 1076618 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B4615049 : Blo 1076618 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B1616891 : Blo 1076618 1616891 := bstep (se 1 (by rfl) ⟨1212668, by rfl⟩ : syracuseStep 1616891 = 2425337) B2425337
theorem B177257717 : Blo 1076618 177257717 := bstep (se 5 (by rfl) ⟨8308955, by rfl⟩ : syracuseStep 177257717 = 16617911) B16617911
theorem B52484993 : Blo 1076618 52484993 := bstep (se 2 (by rfl) ⟨19681872, by rfl⟩ : syracuseStep 52484993 = 39363745) B39363745
theorem B3076699 : Blo 1076618 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B4094975 : Blo 1076618 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B4102265 : Blo 1076618 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B2729983 : Blo 1076618 2729983 := bstep (se 1 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 2729983 = 4094975) B4094975
theorem B118171811 : Blo 1076618 118171811 := bstep (se 1 (by rfl) ⟨88628858, by rfl⟩ : syracuseStep 118171811 = 177257717) B177257717
theorem B34989995 : Blo 1076618 34989995 := bstep (se 1 (by rfl) ⟨26242496, by rfl⟩ : syracuseStep 34989995 = 52484993) B52484993
theorem B1077927 : Blo 1076618 1077927 := bstep (se 1 (by rfl) ⟨808445, by rfl⟩ : syracuseStep 1077927 = 1616891) B1616891
theorem B3639977 : Blo 1076618 3639977 := bstep (se 2 (by rfl) ⟨1364991, by rfl⟩ : syracuseStep 3639977 = 2729983) B2729983
theorem B78781207 : Blo 1076618 78781207 := bstep (se 1 (by rfl) ⟨59085905, by rfl⟩ : syracuseStep 78781207 = 118171811) B118171811
theorem B2734843 : Blo 1076618 2734843 := bstep (se 1 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 2734843 = 4102265) B4102265
theorem B23326663 : Blo 1076618 23326663 := bstep (se 1 (by rfl) ⟨17494997, by rfl⟩ : syracuseStep 23326663 = 34989995) B34989995
theorem B2426651 : Blo 1076618 2426651 := bstep (se 1 (by rfl) ⟨1819988, by rfl⟩ : syracuseStep 2426651 = 3639977) B3639977
theorem B31102217 : Blo 1076618 31102217 := bstep (se 2 (by rfl) ⟨11663331, by rfl⟩ : syracuseStep 31102217 = 23326663) B23326663
theorem B3646457 : Blo 1076618 3646457 := bstep (se 2 (by rfl) ⟨1367421, by rfl⟩ : syracuseStep 3646457 = 2734843) B2734843
theorem B105041609 : Blo 1076618 105041609 := bstep (se 2 (by rfl) ⟨39390603, by rfl⟩ : syracuseStep 105041609 = 78781207) B78781207
theorem B70027739 : Blo 1076618 70027739 := bstep (se 1 (by rfl) ⟨52520804, by rfl⟩ : syracuseStep 70027739 = 105041609) B105041609
theorem B2430971 : Blo 1076618 2430971 := bstep (se 1 (by rfl) ⟨1823228, by rfl⟩ : syracuseStep 2430971 = 3646457) B3646457
theorem B1617767 : Blo 1076618 1617767 := bstep (se 1 (by rfl) ⟨1213325, by rfl⟩ : syracuseStep 1617767 = 2426651) B2426651
theorem B20734811 : Blo 1076618 20734811 := bstep (se 1 (by rfl) ⟨15551108, by rfl⟩ : syracuseStep 20734811 = 31102217) B31102217
theorem B1620647 : Blo 1076618 1620647 := bstep (se 1 (by rfl) ⟨1215485, by rfl⟩ : syracuseStep 1620647 = 2430971) B2430971
theorem B46685159 : Blo 1076618 46685159 := bstep (se 1 (by rfl) ⟨35013869, by rfl⟩ : syracuseStep 46685159 = 70027739) B70027739
theorem B13823207 : Blo 1076618 13823207 := bstep (se 1 (by rfl) ⟨10367405, by rfl⟩ : syracuseStep 13823207 = 20734811) B20734811
theorem B1078511 : Blo 1076618 1078511 := bstep (se 1 (by rfl) ⟨808883, by rfl⟩ : syracuseStep 1078511 = 1617767) B1617767
theorem B9215471 : Blo 1076618 9215471 := bstep (se 1 (by rfl) ⟨6911603, by rfl⟩ : syracuseStep 9215471 = 13823207) B13823207
theorem B31123439 : Blo 1076618 31123439 := bstep (se 1 (by rfl) ⟨23342579, by rfl⟩ : syracuseStep 31123439 = 46685159) B46685159
theorem B1080431 : Blo 1076618 1080431 := bstep (se 1 (by rfl) ⟨810323, by rfl⟩ : syracuseStep 1080431 = 1620647) B1620647
theorem B20748959 : Blo 1076618 20748959 := bstep (se 1 (by rfl) ⟨15561719, by rfl⟩ : syracuseStep 20748959 = 31123439) B31123439
theorem B6143647 : Blo 1076618 6143647 := bstep (se 1 (by rfl) ⟨4607735, by rfl⟩ : syracuseStep 6143647 = 9215471) B9215471
theorem B13832639 : Blo 1076618 13832639 := bstep (se 1 (by rfl) ⟨10374479, by rfl⟩ : syracuseStep 13832639 = 20748959) B20748959
theorem B8191529 : Blo 1076618 8191529 := bstep (se 2 (by rfl) ⟨3071823, by rfl⟩ : syracuseStep 8191529 = 6143647) B6143647
theorem B9221759 : Blo 1076618 9221759 := bstep (se 1 (by rfl) ⟨6916319, by rfl⟩ : syracuseStep 9221759 = 13832639) B13832639
theorem B5461019 : Blo 1076618 5461019 := bstep (se 1 (by rfl) ⟨4095764, by rfl⟩ : syracuseStep 5461019 = 8191529) B8191529
theorem B3640679 : Blo 1076618 3640679 := bstep (se 1 (by rfl) ⟨2730509, by rfl⟩ : syracuseStep 3640679 = 5461019) B5461019
theorem B6147839 : Blo 1076618 6147839 := bstep (se 1 (by rfl) ⟨4610879, by rfl⟩ : syracuseStep 6147839 = 9221759) B9221759
theorem B2427119 : Blo 1076618 2427119 := bstep (se 1 (by rfl) ⟨1820339, by rfl⟩ : syracuseStep 2427119 = 3640679) B3640679
theorem B4098559 : Blo 1076618 4098559 := bstep (se 1 (by rfl) ⟨3073919, by rfl⟩ : syracuseStep 4098559 = 6147839) B6147839
theorem B1618079 : Blo 1076618 1618079 := bstep (se 1 (by rfl) ⟨1213559, by rfl⟩ : syracuseStep 1618079 = 2427119) B2427119
theorem B5464745 : Blo 1076618 5464745 := bstep (se 2 (by rfl) ⟨2049279, by rfl⟩ : syracuseStep 5464745 = 4098559) B4098559
theorem B3643163 : Blo 1076618 3643163 := bstep (se 1 (by rfl) ⟨2732372, by rfl⟩ : syracuseStep 3643163 = 5464745) B5464745
theorem B1078719 : Blo 1076618 1078719 := bstep (se 1 (by rfl) ⟨809039, by rfl⟩ : syracuseStep 1078719 = 1618079) B1618079
theorem B2428775 : Blo 1076618 2428775 := bstep (se 1 (by rfl) ⟨1821581, by rfl⟩ : syracuseStep 2428775 = 3643163) B3643163
theorem B1619183 : Blo 1076618 1619183 := bstep (se 1 (by rfl) ⟨1214387, by rfl⟩ : syracuseStep 1619183 = 2428775) B2428775
theorem B1079455 : Blo 1076618 1079455 := bstep (se 1 (by rfl) ⟨809591, by rfl⟩ : syracuseStep 1079455 = 1619183) B1619183

theorem C0 (j : ℕ) (h1 : 269154 ≤ j) (h2 : j ≤ 269853) : Blo 1076618 (4 * j + 3) := by
  interval_cases j
  · exact B1076619
  · exact B1076623
  · exact B1076627
  · exact B1076631
  · exact B1076635
  · exact B1076639
  · exact B1076643
  · exact B1076647
  · exact B1076651
  · exact B1076655
  · exact B1076659
  · exact B1076663
  · exact B1076667
  · exact B1076671
  · exact B1076675
  · exact B1076679
  · exact B1076683
  · exact B1076687
  · exact B1076691
  · exact B1076695
  · exact B1076699
  · exact B1076703
  · exact B1076707
  · exact B1076711
  · exact B1076715
  · exact B1076719
  · exact B1076723
  · exact B1076727
  · exact B1076731
  · exact B1076735
  · exact B1076739
  · exact B1076743
  · exact B1076747
  · exact B1076751
  · exact B1076755
  · exact B1076759
  · exact B1076763
  · exact B1076767
  · exact B1076771
  · exact B1076775
  · exact B1076779
  · exact B1076783
  · exact B1076787
  · exact B1076791
  · exact B1076795
  · exact B1076799
  · exact B1076803
  · exact B1076807
  · exact B1076811
  · exact B1076815
  · exact B1076819
  · exact B1076823
  · exact B1076827
  · exact B1076831
  · exact B1076835
  · exact B1076839
  · exact B1076843
  · exact B1076847
  · exact B1076851
  · exact B1076855
  · exact B1076859
  · exact B1076863
  · exact B1076867
  · exact B1076871
  · exact B1076875
  · exact B1076879
  · exact B1076883
  · exact B1076887
  · exact B1076891
  · exact B1076895
  · exact B1076899
  · exact B1076903
  · exact B1076907
  · exact B1076911
  · exact B1076915
  · exact B1076919
  · exact B1076923
  · exact B1076927
  · exact B1076931
  · exact B1076935
  · exact B1076939
  · exact B1076943
  · exact B1076947
  · exact B1076951
  · exact B1076955
  · exact B1076959
  · exact B1076963
  · exact B1076967
  · exact B1076971
  · exact B1076975
  · exact B1076979
  · exact B1076983
  · exact B1076987
  · exact B1076991
  · exact B1076995
  · exact B1076999
  · exact B1077003
  · exact B1077007
  · exact B1077011
  · exact B1077015
  · exact B1077019
  · exact B1077023
  · exact B1077027
  · exact B1077031
  · exact B1077035
  · exact B1077039
  · exact B1077043
  · exact B1077047
  · exact B1077051
  · exact B1077055
  · exact B1077059
  · exact B1077063
  · exact B1077067
  · exact B1077071
  · exact B1077075
  · exact B1077079
  · exact B1077083
  · exact B1077087
  · exact B1077091
  · exact B1077095
  · exact B1077099
  · exact B1077103
  · exact B1077107
  · exact B1077111
  · exact B1077115
  · exact B1077119
  · exact B1077123
  · exact B1077127
  · exact B1077131
  · exact B1077135
  · exact B1077139
  · exact B1077143
  · exact B1077147
  · exact B1077151
  · exact B1077155
  · exact B1077159
  · exact B1077163
  · exact B1077167
  · exact B1077171
  · exact B1077175
  · exact B1077179
  · exact B1077183
  · exact B1077187
  · exact B1077191
  · exact B1077195
  · exact B1077199
  · exact B1077203
  · exact B1077207
  · exact B1077211
  · exact B1077215
  · exact B1077219
  · exact B1077223
  · exact B1077227
  · exact B1077231
  · exact B1077235
  · exact B1077239
  · exact B1077243
  · exact B1077247
  · exact B1077251
  · exact B1077255
  · exact B1077259
  · exact B1077263
  · exact B1077267
  · exact B1077271
  · exact B1077275
  · exact B1077279
  · exact B1077283
  · exact B1077287
  · exact B1077291
  · exact B1077295
  · exact B1077299
  · exact B1077303
  · exact B1077307
  · exact B1077311
  · exact B1077315
  · exact B1077319
  · exact B1077323
  · exact B1077327
  · exact B1077331
  · exact B1077335
  · exact B1077339
  · exact B1077343
  · exact B1077347
  · exact B1077351
  · exact B1077355
  · exact B1077359
  · exact B1077363
  · exact B1077367
  · exact B1077371
  · exact B1077375
  · exact B1077379
  · exact B1077383
  · exact B1077387
  · exact B1077391
  · exact B1077395
  · exact B1077399
  · exact B1077403
  · exact B1077407
  · exact B1077411
  · exact B1077415
  · exact B1077419
  · exact B1077423
  · exact B1077427
  · exact B1077431
  · exact B1077435
  · exact B1077439
  · exact B1077443
  · exact B1077447
  · exact B1077451
  · exact B1077455
  · exact B1077459
  · exact B1077463
  · exact B1077467
  · exact B1077471
  · exact B1077475
  · exact B1077479
  · exact B1077483
  · exact B1077487
  · exact B1077491
  · exact B1077495
  · exact B1077499
  · exact B1077503
  · exact B1077507
  · exact B1077511
  · exact B1077515
  · exact B1077519
  · exact B1077523
  · exact B1077527
  · exact B1077531
  · exact B1077535
  · exact B1077539
  · exact B1077543
  · exact B1077547
  · exact B1077551
  · exact B1077555
  · exact B1077559
  · exact B1077563
  · exact B1077567
  · exact B1077571
  · exact B1077575
  · exact B1077579
  · exact B1077583
  · exact B1077587
  · exact B1077591
  · exact B1077595
  · exact B1077599
  · exact B1077603
  · exact B1077607
  · exact B1077611
  · exact B1077615
  · exact B1077619
  · exact B1077623
  · exact B1077627
  · exact B1077631
  · exact B1077635
  · exact B1077639
  · exact B1077643
  · exact B1077647
  · exact B1077651
  · exact B1077655
  · exact B1077659
  · exact B1077663
  · exact B1077667
  · exact B1077671
  · exact B1077675
  · exact B1077679
  · exact B1077683
  · exact B1077687
  · exact B1077691
  · exact B1077695
  · exact B1077699
  · exact B1077703
  · exact B1077707
  · exact B1077711
  · exact B1077715
  · exact B1077719
  · exact B1077723
  · exact B1077727
  · exact B1077731
  · exact B1077735
  · exact B1077739
  · exact B1077743
  · exact B1077747
  · exact B1077751
  · exact B1077755
  · exact B1077759
  · exact B1077763
  · exact B1077767
  · exact B1077771
  · exact B1077775
  · exact B1077779
  · exact B1077783
  · exact B1077787
  · exact B1077791
  · exact B1077795
  · exact B1077799
  · exact B1077803
  · exact B1077807
  · exact B1077811
  · exact B1077815
  · exact B1077819
  · exact B1077823
  · exact B1077827
  · exact B1077831
  · exact B1077835
  · exact B1077839
  · exact B1077843
  · exact B1077847
  · exact B1077851
  · exact B1077855
  · exact B1077859
  · exact B1077863
  · exact B1077867
  · exact B1077871
  · exact B1077875
  · exact B1077879
  · exact B1077883
  · exact B1077887
  · exact B1077891
  · exact B1077895
  · exact B1077899
  · exact B1077903
  · exact B1077907
  · exact B1077911
  · exact B1077915
  · exact B1077919
  · exact B1077923
  · exact B1077927
  · exact B1077931
  · exact B1077935
  · exact B1077939
  · exact B1077943
  · exact B1077947
  · exact B1077951
  · exact B1077955
  · exact B1077959
  · exact B1077963
  · exact B1077967
  · exact B1077971
  · exact B1077975
  · exact B1077979
  · exact B1077983
  · exact B1077987
  · exact B1077991
  · exact B1077995
  · exact B1077999
  · exact B1078003
  · exact B1078007
  · exact B1078011
  · exact B1078015
  · exact B1078019
  · exact B1078023
  · exact B1078027
  · exact B1078031
  · exact B1078035
  · exact B1078039
  · exact B1078043
  · exact B1078047
  · exact B1078051
  · exact B1078055
  · exact B1078059
  · exact B1078063
  · exact B1078067
  · exact B1078071
  · exact B1078075
  · exact B1078079
  · exact B1078083
  · exact B1078087
  · exact B1078091
  · exact B1078095
  · exact B1078099
  · exact B1078103
  · exact B1078107
  · exact B1078111
  · exact B1078115
  · exact B1078119
  · exact B1078123
  · exact B1078127
  · exact B1078131
  · exact B1078135
  · exact B1078139
  · exact B1078143
  · exact B1078147
  · exact B1078151
  · exact B1078155
  · exact B1078159
  · exact B1078163
  · exact B1078167
  · exact B1078171
  · exact B1078175
  · exact B1078179
  · exact B1078183
  · exact B1078187
  · exact B1078191
  · exact B1078195
  · exact B1078199
  · exact B1078203
  · exact B1078207
  · exact B1078211
  · exact B1078215
  · exact B1078219
  · exact B1078223
  · exact B1078227
  · exact B1078231
  · exact B1078235
  · exact B1078239
  · exact B1078243
  · exact B1078247
  · exact B1078251
  · exact B1078255
  · exact B1078259
  · exact B1078263
  · exact B1078267
  · exact B1078271
  · exact B1078275
  · exact B1078279
  · exact B1078283
  · exact B1078287
  · exact B1078291
  · exact B1078295
  · exact B1078299
  · exact B1078303
  · exact B1078307
  · exact B1078311
  · exact B1078315
  · exact B1078319
  · exact B1078323
  · exact B1078327
  · exact B1078331
  · exact B1078335
  · exact B1078339
  · exact B1078343
  · exact B1078347
  · exact B1078351
  · exact B1078355
  · exact B1078359
  · exact B1078363
  · exact B1078367
  · exact B1078371
  · exact B1078375
  · exact B1078379
  · exact B1078383
  · exact B1078387
  · exact B1078391
  · exact B1078395
  · exact B1078399
  · exact B1078403
  · exact B1078407
  · exact B1078411
  · exact B1078415
  · exact B1078419
  · exact B1078423
  · exact B1078427
  · exact B1078431
  · exact B1078435
  · exact B1078439
  · exact B1078443
  · exact B1078447
  · exact B1078451
  · exact B1078455
  · exact B1078459
  · exact B1078463
  · exact B1078467
  · exact B1078471
  · exact B1078475
  · exact B1078479
  · exact B1078483
  · exact B1078487
  · exact B1078491
  · exact B1078495
  · exact B1078499
  · exact B1078503
  · exact B1078507
  · exact B1078511
  · exact B1078515
  · exact B1078519
  · exact B1078523
  · exact B1078527
  · exact B1078531
  · exact B1078535
  · exact B1078539
  · exact B1078543
  · exact B1078547
  · exact B1078551
  · exact B1078555
  · exact B1078559
  · exact B1078563
  · exact B1078567
  · exact B1078571
  · exact B1078575
  · exact B1078579
  · exact B1078583
  · exact B1078587
  · exact B1078591
  · exact B1078595
  · exact B1078599
  · exact B1078603
  · exact B1078607
  · exact B1078611
  · exact B1078615
  · exact B1078619
  · exact B1078623
  · exact B1078627
  · exact B1078631
  · exact B1078635
  · exact B1078639
  · exact B1078643
  · exact B1078647
  · exact B1078651
  · exact B1078655
  · exact B1078659
  · exact B1078663
  · exact B1078667
  · exact B1078671
  · exact B1078675
  · exact B1078679
  · exact B1078683
  · exact B1078687
  · exact B1078691
  · exact B1078695
  · exact B1078699
  · exact B1078703
  · exact B1078707
  · exact B1078711
  · exact B1078715
  · exact B1078719
  · exact B1078723
  · exact B1078727
  · exact B1078731
  · exact B1078735
  · exact B1078739
  · exact B1078743
  · exact B1078747
  · exact B1078751
  · exact B1078755
  · exact B1078759
  · exact B1078763
  · exact B1078767
  · exact B1078771
  · exact B1078775
  · exact B1078779
  · exact B1078783
  · exact B1078787
  · exact B1078791
  · exact B1078795
  · exact B1078799
  · exact B1078803
  · exact B1078807
  · exact B1078811
  · exact B1078815
  · exact B1078819
  · exact B1078823
  · exact B1078827
  · exact B1078831
  · exact B1078835
  · exact B1078839
  · exact B1078843
  · exact B1078847
  · exact B1078851
  · exact B1078855
  · exact B1078859
  · exact B1078863
  · exact B1078867
  · exact B1078871
  · exact B1078875
  · exact B1078879
  · exact B1078883
  · exact B1078887
  · exact B1078891
  · exact B1078895
  · exact B1078899
  · exact B1078903
  · exact B1078907
  · exact B1078911
  · exact B1078915
  · exact B1078919
  · exact B1078923
  · exact B1078927
  · exact B1078931
  · exact B1078935
  · exact B1078939
  · exact B1078943
  · exact B1078947
  · exact B1078951
  · exact B1078955
  · exact B1078959
  · exact B1078963
  · exact B1078967
  · exact B1078971
  · exact B1078975
  · exact B1078979
  · exact B1078983
  · exact B1078987
  · exact B1078991
  · exact B1078995
  · exact B1078999
  · exact B1079003
  · exact B1079007
  · exact B1079011
  · exact B1079015
  · exact B1079019
  · exact B1079023
  · exact B1079027
  · exact B1079031
  · exact B1079035
  · exact B1079039
  · exact B1079043
  · exact B1079047
  · exact B1079051
  · exact B1079055
  · exact B1079059
  · exact B1079063
  · exact B1079067
  · exact B1079071
  · exact B1079075
  · exact B1079079
  · exact B1079083
  · exact B1079087
  · exact B1079091
  · exact B1079095
  · exact B1079099
  · exact B1079103
  · exact B1079107
  · exact B1079111
  · exact B1079115
  · exact B1079119
  · exact B1079123
  · exact B1079127
  · exact B1079131
  · exact B1079135
  · exact B1079139
  · exact B1079143
  · exact B1079147
  · exact B1079151
  · exact B1079155
  · exact B1079159
  · exact B1079163
  · exact B1079167
  · exact B1079171
  · exact B1079175
  · exact B1079179
  · exact B1079183
  · exact B1079187
  · exact B1079191
  · exact B1079195
  · exact B1079199
  · exact B1079203
  · exact B1079207
  · exact B1079211
  · exact B1079215
  · exact B1079219
  · exact B1079223
  · exact B1079227
  · exact B1079231
  · exact B1079235
  · exact B1079239
  · exact B1079243
  · exact B1079247
  · exact B1079251
  · exact B1079255
  · exact B1079259
  · exact B1079263
  · exact B1079267
  · exact B1079271
  · exact B1079275
  · exact B1079279
  · exact B1079283
  · exact B1079287
  · exact B1079291
  · exact B1079295
  · exact B1079299
  · exact B1079303
  · exact B1079307
  · exact B1079311
  · exact B1079315
  · exact B1079319
  · exact B1079323
  · exact B1079327
  · exact B1079331
  · exact B1079335
  · exact B1079339
  · exact B1079343
  · exact B1079347
  · exact B1079351
  · exact B1079355
  · exact B1079359
  · exact B1079363
  · exact B1079367
  · exact B1079371
  · exact B1079375
  · exact B1079379
  · exact B1079383
  · exact B1079387
  · exact B1079391
  · exact B1079395
  · exact B1079399
  · exact B1079403
  · exact B1079407
  · exact B1079411
  · exact B1079415

theorem C1 (j : ℕ) (h1 : 269854 ≤ j) (h2 : j ≤ 270153) : Blo 1076618 (4 * j + 3) := by
  interval_cases j
  · exact B1079419
  · exact B1079423
  · exact B1079427
  · exact B1079431
  · exact B1079435
  · exact B1079439
  · exact B1079443
  · exact B1079447
  · exact B1079451
  · exact B1079455
  · exact B1079459
  · exact B1079463
  · exact B1079467
  · exact B1079471
  · exact B1079475
  · exact B1079479
  · exact B1079483
  · exact B1079487
  · exact B1079491
  · exact B1079495
  · exact B1079499
  · exact B1079503
  · exact B1079507
  · exact B1079511
  · exact B1079515
  · exact B1079519
  · exact B1079523
  · exact B1079527
  · exact B1079531
  · exact B1079535
  · exact B1079539
  · exact B1079543
  · exact B1079547
  · exact B1079551
  · exact B1079555
  · exact B1079559
  · exact B1079563
  · exact B1079567
  · exact B1079571
  · exact B1079575
  · exact B1079579
  · exact B1079583
  · exact B1079587
  · exact B1079591
  · exact B1079595
  · exact B1079599
  · exact B1079603
  · exact B1079607
  · exact B1079611
  · exact B1079615
  · exact B1079619
  · exact B1079623
  · exact B1079627
  · exact B1079631
  · exact B1079635
  · exact B1079639
  · exact B1079643
  · exact B1079647
  · exact B1079651
  · exact B1079655
  · exact B1079659
  · exact B1079663
  · exact B1079667
  · exact B1079671
  · exact B1079675
  · exact B1079679
  · exact B1079683
  · exact B1079687
  · exact B1079691
  · exact B1079695
  · exact B1079699
  · exact B1079703
  · exact B1079707
  · exact B1079711
  · exact B1079715
  · exact B1079719
  · exact B1079723
  · exact B1079727
  · exact B1079731
  · exact B1079735
  · exact B1079739
  · exact B1079743
  · exact B1079747
  · exact B1079751
  · exact B1079755
  · exact B1079759
  · exact B1079763
  · exact B1079767
  · exact B1079771
  · exact B1079775
  · exact B1079779
  · exact B1079783
  · exact B1079787
  · exact B1079791
  · exact B1079795
  · exact B1079799
  · exact B1079803
  · exact B1079807
  · exact B1079811
  · exact B1079815
  · exact B1079819
  · exact B1079823
  · exact B1079827
  · exact B1079831
  · exact B1079835
  · exact B1079839
  · exact B1079843
  · exact B1079847
  · exact B1079851
  · exact B1079855
  · exact B1079859
  · exact B1079863
  · exact B1079867
  · exact B1079871
  · exact B1079875
  · exact B1079879
  · exact B1079883
  · exact B1079887
  · exact B1079891
  · exact B1079895
  · exact B1079899
  · exact B1079903
  · exact B1079907
  · exact B1079911
  · exact B1079915
  · exact B1079919
  · exact B1079923
  · exact B1079927
  · exact B1079931
  · exact B1079935
  · exact B1079939
  · exact B1079943
  · exact B1079947
  · exact B1079951
  · exact B1079955
  · exact B1079959
  · exact B1079963
  · exact B1079967
  · exact B1079971
  · exact B1079975
  · exact B1079979
  · exact B1079983
  · exact B1079987
  · exact B1079991
  · exact B1079995
  · exact B1079999
  · exact B1080003
  · exact B1080007
  · exact B1080011
  · exact B1080015
  · exact B1080019
  · exact B1080023
  · exact B1080027
  · exact B1080031
  · exact B1080035
  · exact B1080039
  · exact B1080043
  · exact B1080047
  · exact B1080051
  · exact B1080055
  · exact B1080059
  · exact B1080063
  · exact B1080067
  · exact B1080071
  · exact B1080075
  · exact B1080079
  · exact B1080083
  · exact B1080087
  · exact B1080091
  · exact B1080095
  · exact B1080099
  · exact B1080103
  · exact B1080107
  · exact B1080111
  · exact B1080115
  · exact B1080119
  · exact B1080123
  · exact B1080127
  · exact B1080131
  · exact B1080135
  · exact B1080139
  · exact B1080143
  · exact B1080147
  · exact B1080151
  · exact B1080155
  · exact B1080159
  · exact B1080163
  · exact B1080167
  · exact B1080171
  · exact B1080175
  · exact B1080179
  · exact B1080183
  · exact B1080187
  · exact B1080191
  · exact B1080195
  · exact B1080199
  · exact B1080203
  · exact B1080207
  · exact B1080211
  · exact B1080215
  · exact B1080219
  · exact B1080223
  · exact B1080227
  · exact B1080231
  · exact B1080235
  · exact B1080239
  · exact B1080243
  · exact B1080247
  · exact B1080251
  · exact B1080255
  · exact B1080259
  · exact B1080263
  · exact B1080267
  · exact B1080271
  · exact B1080275
  · exact B1080279
  · exact B1080283
  · exact B1080287
  · exact B1080291
  · exact B1080295
  · exact B1080299
  · exact B1080303
  · exact B1080307
  · exact B1080311
  · exact B1080315
  · exact B1080319
  · exact B1080323
  · exact B1080327
  · exact B1080331
  · exact B1080335
  · exact B1080339
  · exact B1080343
  · exact B1080347
  · exact B1080351
  · exact B1080355
  · exact B1080359
  · exact B1080363
  · exact B1080367
  · exact B1080371
  · exact B1080375
  · exact B1080379
  · exact B1080383
  · exact B1080387
  · exact B1080391
  · exact B1080395
  · exact B1080399
  · exact B1080403
  · exact B1080407
  · exact B1080411
  · exact B1080415
  · exact B1080419
  · exact B1080423
  · exact B1080427
  · exact B1080431
  · exact B1080435
  · exact B1080439
  · exact B1080443
  · exact B1080447
  · exact B1080451
  · exact B1080455
  · exact B1080459
  · exact B1080463
  · exact B1080467
  · exact B1080471
  · exact B1080475
  · exact B1080479
  · exact B1080483
  · exact B1080487
  · exact B1080491
  · exact B1080495
  · exact B1080499
  · exact B1080503
  · exact B1080507
  · exact B1080511
  · exact B1080515
  · exact B1080519
  · exact B1080523
  · exact B1080527
  · exact B1080531
  · exact B1080535
  · exact B1080539
  · exact B1080543
  · exact B1080547
  · exact B1080551
  · exact B1080555
  · exact B1080559
  · exact B1080563
  · exact B1080567
  · exact B1080571
  · exact B1080575
  · exact B1080579
  · exact B1080583
  · exact B1080587
  · exact B1080591
  · exact B1080595
  · exact B1080599
  · exact B1080603
  · exact B1080607
  · exact B1080611
  · exact B1080615

theorem solution (m : ℕ) (hlo : 1076618 ≤ m) (hhi : m ≤ 1080618) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 269154 ≤ j := by omega
    have hj2 : j ≤ 270153 := by omega
    have hb : Blo 1076618 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 269854 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
