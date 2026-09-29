-- Prove2me | solution 1 for syracuse_descends_range_1417528_1419528
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:23.861686+00:00
-- url     : https://prove2.me/submissions/2c77a195-0159-4cce-a1d6-95c343720e0e

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


theorem B2392085 : Blo 1417528 2392085 := bbase (se 6 (by rfl) ⟨56064, by rfl⟩ : syracuseStep 2392085 = 112129) (by norm_num)
theorem B12124181 : Blo 1417528 12124181 := bbase (se 6 (by rfl) ⟨284160, by rfl⟩ : syracuseStep 12124181 = 568321) (by norm_num)
theorem B1515557 : Blo 1417528 1515557 := bbase (se 4 (by rfl) ⟨142083, by rfl⟩ : syracuseStep 1515557 = 284167) (by norm_num)
theorem B1794089 : Blo 1417528 1794089 := bbase (se 2 (by rfl) ⟨672783, by rfl⟩ : syracuseStep 1794089 = 1345567) (by norm_num)
theorem B1794145 : Blo 1417528 1794145 := bbase (se 2 (by rfl) ⟨672804, by rfl⟩ : syracuseStep 1794145 = 1345609) (by norm_num)
theorem B2392213 : Blo 1417528 2392213 := bbase (se 6 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 2392213 = 112135) (by norm_num)
theorem B1704089 : Blo 1417528 1704089 := bbase (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) (by norm_num)
theorem B1794241 : Blo 1417528 1794241 := bbase (se 2 (by rfl) ⟨672840, by rfl⟩ : syracuseStep 1794241 = 1345681) (by norm_num)
theorem B2392301 : Blo 1417528 2392301 := bbase (se 3 (by rfl) ⟨448556, by rfl⟩ : syracuseStep 2392301 = 897113) (by norm_num)
theorem B7176437 : Blo 1417528 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B5382389 : Blo 1417528 5382389 := bbase (se 5 (by rfl) ⟨252299, by rfl⟩ : syracuseStep 5382389 = 504599) (by norm_num)
theorem B3031285 : Blo 1417528 3031285 := bbase (se 5 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 3031285 = 284183) (by norm_num)
theorem B4784453 : Blo 1417528 4784453 := bbase (se 4 (by rfl) ⟨448542, by rfl⟩ : syracuseStep 4784453 = 897085) (by norm_num)
theorem B3588421 : Blo 1417528 3588421 := bbase (se 4 (by rfl) ⟨336414, by rfl⟩ : syracuseStep 3588421 = 672829) (by norm_num)
theorem B2392429 : Blo 1417528 2392429 := bbase (se 3 (by rfl) ⟨448580, by rfl⟩ : syracuseStep 2392429 = 897161) (by norm_num)
theorem B1794413 : Blo 1417528 1794413 := bbase (se 3 (by rfl) ⟨336452, by rfl⟩ : syracuseStep 1794413 = 672905) (by norm_num)
theorem B6062485 : Blo 1417528 6062485 := bbase (se 6 (by rfl) ⟨142089, by rfl⟩ : syracuseStep 6062485 = 284179) (by norm_num)
theorem B1794469 : Blo 1417528 1794469 := bbase (se 4 (by rfl) ⟨168231, by rfl⟩ : syracuseStep 1794469 = 336463) (by norm_num)
theorem B6062501 : Blo 1417528 6062501 := bbase (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) (by norm_num)
theorem B3588533 : Blo 1417528 3588533 := bbase (se 5 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 3588533 = 336425) (by norm_num)
theorem B2425277 : Blo 1417528 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B2392517 : Blo 1417528 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B1704397 : Blo 1417528 1704397 := bbase (se 3 (by rfl) ⟨319574, by rfl⟩ : syracuseStep 1704397 = 639149) (by norm_num)
theorem B1794565 : Blo 1417528 1794565 := bbase (se 4 (by rfl) ⟨168240, by rfl⟩ : syracuseStep 1794565 = 336481) (by norm_num)
theorem B3408389 : Blo 1417528 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B5112341 : Blo 1417528 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B2392645 : Blo 1417528 2392645 := bbase (se 4 (by rfl) ⟨224310, by rfl⟩ : syracuseStep 2392645 = 448621) (by norm_num)
theorem B4039253 : Blo 1417528 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B3408485 : Blo 1417528 3408485 := bbase (se 4 (by rfl) ⟨319545, by rfl⟩ : syracuseStep 3408485 = 639091) (by norm_num)
theorem B3031661 : Blo 1417528 3031661 := bbase (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) (by norm_num)
theorem B3588725 : Blo 1417528 3588725 := bbase (se 5 (by rfl) ⟨168221, by rfl⟩ : syracuseStep 3588725 = 336443) (by norm_num)
theorem B2392733 : Blo 1417528 2392733 := bbase (se 3 (by rfl) ⟨448637, by rfl⟩ : syracuseStep 2392733 = 897275) (by norm_num)
theorem B1704613 : Blo 1417528 1704613 := bbase (se 4 (by rfl) ⟨159807, by rfl⟩ : syracuseStep 1704613 = 319615) (by norm_num)
theorem B1794737 : Blo 1417528 1794737 := bbase (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) (by norm_num)
theorem B2728637 : Blo 1417528 2728637 := bbase (se 3 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 2728637 = 1023239) (by norm_num)
theorem B6816469 : Blo 1417528 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B7283429 : Blo 1417528 7283429 := bbase (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) (by norm_num)
theorem B1794793 : Blo 1417528 1794793 := bbase (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) (by norm_num)
theorem B4784885 : Blo 1417528 4784885 := bbase (se 5 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 4784885 = 448583) (by norm_num)
theorem B1819409 : Blo 1417528 1819409 := bbase (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) (by norm_num)
theorem B20726549 : Blo 1417528 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B2392861 : Blo 1417528 2392861 := bbase (se 3 (by rfl) ⟨448661, by rfl⟩ : syracuseStep 2392861 = 897323) (by norm_num)
theorem B1794889 : Blo 1417528 1794889 := bbase (se 2 (by rfl) ⟨673083, by rfl⟩ : syracuseStep 1794889 = 1346167) (by norm_num)
theorem B2392949 : Blo 1417528 2392949 := bbase (se 5 (by rfl) ⟨112169, by rfl⟩ : syracuseStep 2392949 = 224339) (by norm_num)
theorem B2556805 : Blo 1417528 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B16147349 : Blo 1417528 16147349 := bbase (se 6 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 16147349 = 756907) (by norm_num)
theorem B3589069 : Blo 1417528 3589069 := bbase (se 3 (by rfl) ⟨672950, by rfl⟩ : syracuseStep 3589069 = 1345901) (by norm_num)
theorem B1704925 : Blo 1417528 1704925 := bbase (se 3 (by rfl) ⟨319673, by rfl⟩ : syracuseStep 1704925 = 639347) (by norm_num)
theorem B2393077 : Blo 1417528 2393077 := bbase (se 5 (by rfl) ⟨112175, by rfl⟩ : syracuseStep 2393077 = 224351) (by norm_num)
theorem B1795061 : Blo 1417528 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B4490245 : Blo 1417528 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B2876429 : Blo 1417528 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B3638317 : Blo 1417528 3638317 := bbase (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) (by norm_num)
theorem B1795117 : Blo 1417528 1795117 := bbase (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) (by norm_num)
theorem B10921013 : Blo 1417528 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B3589181 : Blo 1417528 3589181 := bbase (se 3 (by rfl) ⟨672971, by rfl⟩ : syracuseStep 3589181 = 1345943) (by norm_num)
theorem B2393165 : Blo 1417528 2393165 := bbase (se 3 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 2393165 = 897437) (by norm_num)
theorem B2557013 : Blo 1417528 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B7185509 : Blo 1417528 7185509 := bbase (se 4 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 7185509 = 1347283) (by norm_num)
theorem B2425981 : Blo 1417528 2425981 := bbase (se 3 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 2425981 = 909743) (by norm_num)
theorem B1795213 : Blo 1417528 1795213 := bbase (se 3 (by rfl) ⟨336602, by rfl⟩ : syracuseStep 1795213 = 673205) (by norm_num)
theorem B4785317 : Blo 1417528 4785317 := bbase (se 4 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 4785317 = 897247) (by norm_num)
theorem B3884213 : Blo 1417528 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2393293 : Blo 1417528 2393293 := bbase (se 3 (by rfl) ⟨448742, by rfl⟩ : syracuseStep 2393293 = 897485) (by norm_num)
theorem B9086165 : Blo 1417528 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B3589373 : Blo 1417528 3589373 := bbase (se 3 (by rfl) ⟨673007, by rfl⟩ : syracuseStep 3589373 = 1346015) (by norm_num)
theorem B5178629 : Blo 1417528 5178629 := bbase (se 4 (by rfl) ⟨485496, by rfl⟩ : syracuseStep 5178629 = 970993) (by norm_num)
theorem B2393381 : Blo 1417528 2393381 := bbase (se 4 (by rfl) ⟨224379, by rfl⟩ : syracuseStep 2393381 = 448759) (by norm_num)
theorem B1795385 : Blo 1417528 1795385 := bbase (se 2 (by rfl) ⟨673269, by rfl⟩ : syracuseStep 1795385 = 1346539) (by norm_num)
theorem B1795441 : Blo 1417528 1795441 := bbase (se 2 (by rfl) ⟨673290, by rfl⟩ : syracuseStep 1795441 = 1346581) (by norm_num)
theorem B2393509 : Blo 1417528 2393509 := bbase (se 4 (by rfl) ⟨224391, by rfl⟩ : syracuseStep 2393509 = 448783) (by norm_num)
theorem B1795537 : Blo 1417528 1795537 := bbase (se 2 (by rfl) ⟨673326, by rfl⟩ : syracuseStep 1795537 = 1346653) (by norm_num)
theorem B2393597 : Blo 1417528 2393597 := bbase (se 3 (by rfl) ⟨448799, by rfl⟩ : syracuseStep 2393597 = 897599) (by norm_num)
theorem B7177733 : Blo 1417528 7177733 := bbase (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) (by norm_num)
theorem B2336261 : Blo 1417528 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B3638861 : Blo 1417528 3638861 := bbase (se 3 (by rfl) ⟨682286, by rfl⟩ : syracuseStep 3638861 = 1364573) (by norm_num)
theorem B4785749 : Blo 1417528 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B3589717 : Blo 1417528 3589717 := bbase (se 8 (by rfl) ⟨21033, by rfl⟩ : syracuseStep 3589717 = 42067) (by norm_num)
theorem B3237461 : Blo 1417528 3237461 := bbase (se 8 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 3237461 = 37939) (by norm_num)
theorem B10774133 : Blo 1417528 10774133 := bbase (se 5 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 10774133 = 1010075) (by norm_num)
theorem B2393725 : Blo 1417528 2393725 := bbase (se 3 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 2393725 = 897647) (by norm_num)
theorem B1795709 : Blo 1417528 1795709 := bbase (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) (by norm_num)
theorem B1795765 : Blo 1417528 1795765 := bbase (se 5 (by rfl) ⟨84176, by rfl⟩ : syracuseStep 1795765 = 168353) (by norm_num)
theorem B3589829 : Blo 1417528 3589829 := bbase (se 4 (by rfl) ⟨336546, by rfl⟩ : syracuseStep 3589829 = 673093) (by norm_num)
theorem B2393813 : Blo 1417528 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B6473429 : Blo 1417528 6473429 := bbase (se 7 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 6473429 = 151721) (by norm_num)
theorem B4040437 : Blo 1417528 4040437 := bbase (se 5 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 4040437 = 378791) (by norm_num)
theorem B2426645 : Blo 1417528 2426645 := bbase (se 6 (by rfl) ⟨56874, by rfl⟩ : syracuseStep 2426645 = 113749) (by norm_num)
theorem B1795861 : Blo 1417528 1795861 := bbase (se 6 (by rfl) ⟨42090, by rfl⟩ : syracuseStep 1795861 = 84181) (by norm_num)
theorem B2393941 : Blo 1417528 2393941 := bbase (se 9 (by rfl) ⟨7013, by rfl⟩ : syracuseStep 2393941 = 14027) (by norm_num)
theorem B3590021 : Blo 1417528 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B4040597 : Blo 1417528 4040597 := bbase (se 6 (by rfl) ⟨94701, by rfl⟩ : syracuseStep 4040597 = 189403) (by norm_num)
theorem B1820569 : Blo 1417528 1820569 := bbase (se 2 (by rfl) ⟨682713, by rfl⟩ : syracuseStep 1820569 = 1365427) (by norm_num)
theorem B2394029 : Blo 1417528 2394029 := bbase (se 3 (by rfl) ⟨448880, by rfl⟩ : syracuseStep 2394029 = 897761) (by norm_num)
theorem B1796033 : Blo 1417528 1796033 := bbase (se 2 (by rfl) ⟨673512, by rfl⟩ : syracuseStep 1796033 = 1347025) (by norm_num)
theorem B1796089 : Blo 1417528 1796089 := bbase (se 2 (by rfl) ⟨673533, by rfl⟩ : syracuseStep 1796089 = 1347067) (by norm_num)
theorem B4786181 : Blo 1417528 4786181 := bbase (se 4 (by rfl) ⟨448704, by rfl⟩ : syracuseStep 4786181 = 897409) (by norm_num)
theorem B10766357 : Blo 1417528 10766357 := bbase (se 6 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 10766357 = 504673) (by norm_num)
theorem B2394157 : Blo 1417528 2394157 := bbase (se 3 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 2394157 = 897809) (by norm_num)
theorem B1796185 : Blo 1417528 1796185 := bbase (se 2 (by rfl) ⟨673569, by rfl⟩ : syracuseStep 1796185 = 1347139) (by norm_num)
theorem B2394245 : Blo 1417528 2394245 := bbase (se 4 (by rfl) ⟨224460, by rfl⟩ : syracuseStep 2394245 = 448921) (by norm_num)
theorem B4040837 : Blo 1417528 4040837 := bbase (se 4 (by rfl) ⟨378828, by rfl⟩ : syracuseStep 4040837 = 757657) (by norm_num)
theorem B1870025 : Blo 1417528 1870025 := bbase (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) (by norm_num)
theorem B39913685 : Blo 1417528 39913685 := bbase (se 7 (by rfl) ⟨467738, by rfl⟩ : syracuseStep 39913685 = 935477) (by norm_num)
theorem B3590365 : Blo 1417528 3590365 := bbase (se 3 (by rfl) ⟨673193, by rfl⟩ : syracuseStep 3590365 = 1346387) (by norm_num)
theorem B2271485 : Blo 1417528 2271485 := bbase (se 3 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 2271485 = 851807) (by norm_num)
theorem B2394373 : Blo 1417528 2394373 := bbase (se 4 (by rfl) ⟨224472, by rfl⟩ : syracuseStep 2394373 = 448945) (by norm_num)
theorem B1796357 : Blo 1417528 1796357 := bbase (se 4 (by rfl) ⟨168408, by rfl⟩ : syracuseStep 1796357 = 336817) (by norm_num)
theorem B5384501 : Blo 1417528 5384501 := bbase (se 5 (by rfl) ⟨252398, by rfl⟩ : syracuseStep 5384501 = 504797) (by norm_num)
theorem B1796413 : Blo 1417528 1796413 := bbase (se 3 (by rfl) ⟨336827, by rfl⟩ : syracuseStep 1796413 = 673655) (by norm_num)
theorem B4041029 : Blo 1417528 4041029 := bbase (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) (by norm_num)
theorem B3590477 : Blo 1417528 3590477 := bbase (se 3 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 3590477 = 1346429) (by norm_num)
theorem B3639629 : Blo 1417528 3639629 := bbase (se 3 (by rfl) ⟨682430, by rfl⟩ : syracuseStep 3639629 = 1364861) (by norm_num)
theorem B2156885 : Blo 1417528 2156885 := bbase (se 10 (by rfl) ⟨3159, by rfl⟩ : syracuseStep 2156885 = 6319) (by norm_num)
theorem B2427221 : Blo 1417528 2427221 := bbase (se 10 (by rfl) ⟨3555, by rfl⟩ : syracuseStep 2427221 = 7111) (by norm_num)
theorem B5114197 : Blo 1417528 5114197 := bbase (se 10 (by rfl) ⟨7491, by rfl⟩ : syracuseStep 5114197 = 14983) (by norm_num)
theorem B2394461 : Blo 1417528 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B1796509 : Blo 1417528 1796509 := bbase (se 3 (by rfl) ⟨336845, by rfl⟩ : syracuseStep 1796509 = 673691) (by norm_num)
theorem B4786613 : Blo 1417528 4786613 := bbase (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) (by norm_num)
theorem B2394589 : Blo 1417528 2394589 := bbase (se 3 (by rfl) ⟨448985, by rfl⟩ : syracuseStep 2394589 = 897971) (by norm_num)
theorem B3590669 : Blo 1417528 3590669 := bbase (se 3 (by rfl) ⟨673250, by rfl⟩ : syracuseStep 3590669 = 1346501) (by norm_num)
theorem B2460197 : Blo 1417528 2460197 := bbase (se 4 (by rfl) ⟨230643, by rfl⟩ : syracuseStep 2460197 = 461287) (by norm_num)
theorem B2394677 : Blo 1417528 2394677 := bbase (se 5 (by rfl) ⟨112250, by rfl⟩ : syracuseStep 2394677 = 224501) (by norm_num)
theorem B5384789 : Blo 1417528 5384789 := bbase (se 8 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 5384789 = 63103) (by norm_num)
theorem B1534573 : Blo 1417528 1534573 := bbase (se 3 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 1534573 = 575465) (by norm_num)
theorem B4311701 : Blo 1417528 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B3410581 : Blo 1417528 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B2394805 : Blo 1417528 2394805 := bbase (se 5 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 2394805 = 224513) (by norm_num)
theorem B6056693 : Blo 1417528 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B2271997 : Blo 1417528 2271997 := bbase (se 3 (by rfl) ⟨425999, by rfl⟩ : syracuseStep 2271997 = 851999) (by norm_num)
theorem B3189509 : Blo 1417528 3189509 := bbase (se 4 (by rfl) ⟨299016, by rfl⟩ : syracuseStep 3189509 = 598033) (by norm_num)
theorem B2394893 : Blo 1417528 2394893 := bbase (se 3 (by rfl) ⟨449042, by rfl⟩ : syracuseStep 2394893 = 898085) (by norm_num)
theorem B7179029 : Blo 1417528 7179029 := bbase (se 6 (by rfl) ⟨168258, by rfl⟩ : syracuseStep 7179029 = 336517) (by norm_num)
theorem B2304821 : Blo 1417528 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B3640133 : Blo 1417528 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B3189581 : Blo 1417528 3189581 := bbase (se 3 (by rfl) ⟨598046, by rfl⟩ : syracuseStep 3189581 = 1196093) (by norm_num)
theorem B4787045 : Blo 1417528 4787045 := bbase (se 4 (by rfl) ⟨448785, by rfl⟩ : syracuseStep 4787045 = 897571) (by norm_num)
theorem B3591013 : Blo 1417528 3591013 := bbase (se 4 (by rfl) ⟨336657, by rfl⟩ : syracuseStep 3591013 = 673315) (by norm_num)
theorem B10226549 : Blo 1417528 10226549 := bbase (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) (by norm_num)
theorem B2395021 : Blo 1417528 2395021 := bbase (se 3 (by rfl) ⟨449066, by rfl⟩ : syracuseStep 2395021 = 898133) (by norm_num)
theorem B3189653 : Blo 1417528 3189653 := bbase (se 6 (by rfl) ⟨74757, by rfl⟩ : syracuseStep 3189653 = 149515) (by norm_num)
theorem B3591125 : Blo 1417528 3591125 := bbase (se 7 (by rfl) ⟨42083, by rfl⟩ : syracuseStep 3591125 = 84167) (by norm_num)
theorem B3189725 : Blo 1417528 3189725 := bbase (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) (by norm_num)
theorem B2395109 : Blo 1417528 2395109 := bbase (se 4 (by rfl) ⟨224541, by rfl⟩ : syracuseStep 2395109 = 449083) (by norm_num)
theorem B11496437 : Blo 1417528 11496437 := bbase (se 5 (by rfl) ⟨538895, by rfl⟩ : syracuseStep 11496437 = 1077791) (by norm_num)
theorem B3189797 : Blo 1417528 3189797 := bbase (se 4 (by rfl) ⟨299043, by rfl⟩ : syracuseStep 3189797 = 598087) (by norm_num)
theorem B1944661 : Blo 1417528 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B2395237 : Blo 1417528 2395237 := bbase (se 4 (by rfl) ⟨224553, by rfl⟩ : syracuseStep 2395237 = 449107) (by norm_num)
theorem B3189869 : Blo 1417528 3189869 := bbase (se 3 (by rfl) ⟨598100, by rfl⟩ : syracuseStep 3189869 = 1196201) (by norm_num)
theorem B3591317 : Blo 1417528 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B3189941 : Blo 1417528 3189941 := bbase (se 5 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 3189941 = 299057) (by norm_num)
theorem B2395325 : Blo 1417528 2395325 := bbase (se 3 (by rfl) ⟨449123, by rfl⟩ : syracuseStep 2395325 = 898247) (by norm_num)
theorem B2018533 : Blo 1417528 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B5115109 : Blo 1417528 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B3190013 : Blo 1417528 3190013 := bbase (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) (by norm_num)
theorem B4787477 : Blo 1417528 4787477 := bbase (se 6 (by rfl) ⟨112206, by rfl⟩ : syracuseStep 4787477 = 224413) (by norm_num)
theorem B2624797 : Blo 1417528 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B2272541 : Blo 1417528 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B4042021 : Blo 1417528 4042021 := bbase (se 4 (by rfl) ⟨378939, by rfl⟩ : syracuseStep 4042021 = 757879) (by norm_num)
theorem B2395453 : Blo 1417528 2395453 := bbase (se 3 (by rfl) ⟨449147, by rfl⟩ : syracuseStep 2395453 = 898295) (by norm_num)
theorem B3190085 : Blo 1417528 3190085 := bbase (se 4 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 3190085 = 598141) (by norm_num)
theorem B3190157 : Blo 1417528 3190157 := bbase (se 3 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 3190157 = 1196309) (by norm_num)
theorem B3190229 : Blo 1417528 3190229 := bbase (se 7 (by rfl) ⟨37385, by rfl⟩ : syracuseStep 3190229 = 74771) (by norm_num)
theorem B3591661 : Blo 1417528 3591661 := bbase (se 3 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 3591661 = 1346873) (by norm_num)
theorem B3190301 : Blo 1417528 3190301 := bbase (se 3 (by rfl) ⟨598181, by rfl⟩ : syracuseStep 3190301 = 1196363) (by norm_num)
theorem B3591773 : Blo 1417528 3591773 := bbase (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) (by norm_num)
theorem B3190373 : Blo 1417528 3190373 := bbase (se 4 (by rfl) ⟨299097, by rfl⟩ : syracuseStep 3190373 = 598195) (by norm_num)
theorem B3190445 : Blo 1417528 3190445 := bbase (se 3 (by rfl) ⟨598208, by rfl⟩ : syracuseStep 3190445 = 1196417) (by norm_num)
theorem B13627061 : Blo 1417528 13627061 := bbase (se 5 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 13627061 = 1277537) (by norm_num)
theorem B4542149 : Blo 1417528 4542149 := bbase (se 4 (by rfl) ⟨425826, by rfl⟩ : syracuseStep 4542149 = 851653) (by norm_num)
theorem B4787909 : Blo 1417528 4787909 := bbase (se 4 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 4787909 = 897733) (by norm_num)
theorem B3190517 : Blo 1417528 3190517 := bbase (se 5 (by rfl) ⟨149555, by rfl⟩ : syracuseStep 3190517 = 299111) (by norm_num)
theorem B5385973 : Blo 1417528 5385973 := bbase (se 5 (by rfl) ⟨252467, by rfl⟩ : syracuseStep 5385973 = 504935) (by norm_num)
theorem B3591965 : Blo 1417528 3591965 := bbase (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) (by norm_num)
theorem B2019125 : Blo 1417528 2019125 := bbase (se 5 (by rfl) ⟨94646, by rfl⟩ : syracuseStep 2019125 = 189293) (by norm_num)
theorem B3190589 : Blo 1417528 3190589 := bbase (se 3 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 3190589 = 1196471) (by norm_num)
theorem B2273093 : Blo 1417528 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B2273125 : Blo 1417528 2273125 := bbase (se 4 (by rfl) ⟨213105, by rfl⟩ : syracuseStep 2273125 = 426211) (by norm_num)
theorem B3190661 : Blo 1417528 3190661 := bbase (se 4 (by rfl) ⟨299124, by rfl⟩ : syracuseStep 3190661 = 598249) (by norm_num)
theorem B2019205 : Blo 1417528 2019205 := bbase (se 4 (by rfl) ⟨189300, by rfl⟩ : syracuseStep 2019205 = 378601) (by norm_num)
theorem B2592661 : Blo 1417528 2592661 := bbase (se 6 (by rfl) ⟨60765, by rfl⟩ : syracuseStep 2592661 = 121531) (by norm_num)
theorem B3190733 : Blo 1417528 3190733 := bbase (se 3 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 3190733 = 1196525) (by norm_num)
theorem B2019325 : Blo 1417528 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B15331349 : Blo 1417528 15331349 := bbase (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) (by norm_num)
theorem B3190805 : Blo 1417528 3190805 := bbase (se 6 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 3190805 = 149569) (by norm_num)
theorem B7180325 : Blo 1417528 7180325 := bbase (se 4 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 7180325 = 1346311) (by norm_num)
theorem B5386277 : Blo 1417528 5386277 := bbase (se 4 (by rfl) ⟨504963, by rfl⟩ : syracuseStep 5386277 = 1009927) (by norm_num)
theorem B2691157 : Blo 1417528 2691157 := bbase (se 8 (by rfl) ⟨15768, by rfl⟩ : syracuseStep 2691157 = 31537) (by norm_num)
theorem B3190877 : Blo 1417528 3190877 := bbase (se 3 (by rfl) ⟨598289, by rfl⟩ : syracuseStep 3190877 = 1196579) (by norm_num)
theorem B2019421 : Blo 1417528 2019421 := bbase (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) (by norm_num)
theorem B4788341 : Blo 1417528 4788341 := bbase (se 5 (by rfl) ⟨224453, by rfl⟩ : syracuseStep 4788341 = 448907) (by norm_num)
theorem B3592309 : Blo 1417528 3592309 := bbase (se 5 (by rfl) ⟨168389, by rfl⟩ : syracuseStep 3592309 = 336779) (by norm_num)
theorem B1437833 : Blo 1417528 1437833 := bbase (se 2 (by rfl) ⟨539187, by rfl⟩ : syracuseStep 1437833 = 1078375) (by norm_num)
theorem B3190949 : Blo 1417528 3190949 := bbase (se 4 (by rfl) ⟨299151, by rfl⟩ : syracuseStep 3190949 = 598303) (by norm_num)
theorem B7671989 : Blo 1417528 7671989 := bbase (se 5 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 7671989 = 719249) (by norm_num)
theorem B2691301 : Blo 1417528 2691301 := bbase (se 4 (by rfl) ⟨252309, by rfl⟩ : syracuseStep 2691301 = 504619) (by norm_num)
theorem B3592421 : Blo 1417528 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B3191021 : Blo 1417528 3191021 := bbase (se 3 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 3191021 = 1196633) (by norm_num)
theorem B3191093 : Blo 1417528 3191093 := bbase (se 5 (by rfl) ⟨149582, by rfl⟩ : syracuseStep 3191093 = 299165) (by norm_num)
theorem B3191165 : Blo 1417528 3191165 := bbase (se 3 (by rfl) ⟨598343, by rfl⟩ : syracuseStep 3191165 = 1196687) (by norm_num)
theorem B2691461 : Blo 1417528 2691461 := bbase (se 4 (by rfl) ⟨252324, by rfl⟩ : syracuseStep 2691461 = 504649) (by norm_num)
theorem B3592613 : Blo 1417528 3592613 := bbase (se 4 (by rfl) ⟨336807, by rfl⟩ : syracuseStep 3592613 = 673615) (by norm_num)
theorem B3191237 : Blo 1417528 3191237 := bbase (se 4 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 3191237 = 598357) (by norm_num)
theorem B2126309 : Blo 1417528 2126309 := bbase (se 4 (by rfl) ⟨199341, by rfl⟩ : syracuseStep 2126309 = 398683) (by norm_num)
theorem B6058469 : Blo 1417528 6058469 := bbase (se 4 (by rfl) ⟨567981, by rfl⟩ : syracuseStep 6058469 = 1135963) (by norm_num)
theorem B2126333 : Blo 1417528 2126333 := bbase (se 3 (by rfl) ⟨398687, by rfl⟩ : syracuseStep 2126333 = 797375) (by norm_num)
theorem B3191309 : Blo 1417528 3191309 := bbase (se 3 (by rfl) ⟨598370, by rfl⟩ : syracuseStep 3191309 = 1196741) (by norm_num)
theorem B2126357 : Blo 1417528 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B2691605 : Blo 1417528 2691605 := bbase (se 6 (by rfl) ⟨63084, by rfl⟩ : syracuseStep 2691605 = 126169) (by norm_num)
theorem B4788773 : Blo 1417528 4788773 := bbase (se 4 (by rfl) ⟨448947, by rfl⟩ : syracuseStep 4788773 = 897895) (by norm_num)
theorem B2126381 : Blo 1417528 2126381 := bbase (se 3 (by rfl) ⟨398696, by rfl⟩ : syracuseStep 2126381 = 797393) (by norm_num)
theorem B2126405 : Blo 1417528 2126405 := bbase (se 4 (by rfl) ⟨199350, by rfl⟩ : syracuseStep 2126405 = 398701) (by norm_num)
theorem B2019917 : Blo 1417528 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B3191381 : Blo 1417528 3191381 := bbase (se 8 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 3191381 = 37399) (by norm_num)
theorem B2126429 : Blo 1417528 2126429 := bbase (se 3 (by rfl) ⟨398705, by rfl⟩ : syracuseStep 2126429 = 797411) (by norm_num)
theorem B2126453 : Blo 1417528 2126453 := bbase (se 5 (by rfl) ⟨99677, by rfl⟩ : syracuseStep 2126453 = 199355) (by norm_num)
theorem B6820469 : Blo 1417528 6820469 := bbase (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) (by norm_num)
theorem B2126477 : Blo 1417528 2126477 := bbase (se 3 (by rfl) ⟨398714, by rfl⟩ : syracuseStep 2126477 = 797429) (by norm_num)
theorem B3191453 : Blo 1417528 3191453 := bbase (se 3 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 3191453 = 1196795) (by norm_num)
theorem B2126501 : Blo 1417528 2126501 := bbase (se 4 (by rfl) ⟨199359, by rfl⟩ : syracuseStep 2126501 = 398719) (by norm_num)
theorem B2126525 : Blo 1417528 2126525 := bbase (se 3 (by rfl) ⟨398723, by rfl⟩ : syracuseStep 2126525 = 797447) (by norm_num)
theorem B2126549 : Blo 1417528 2126549 := bbase (se 7 (by rfl) ⟨24920, by rfl⟩ : syracuseStep 2126549 = 49841) (by norm_num)
theorem B6058709 : Blo 1417528 6058709 := bbase (se 7 (by rfl) ⟨71000, by rfl⟩ : syracuseStep 6058709 = 142001) (by norm_num)
theorem B3191525 : Blo 1417528 3191525 := bbase (se 4 (by rfl) ⟨299205, by rfl⟩ : syracuseStep 3191525 = 598411) (by norm_num)
theorem B2126573 : Blo 1417528 2126573 := bbase (se 3 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 2126573 = 797465) (by norm_num)
theorem B3592957 : Blo 1417528 3592957 := bbase (se 3 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 3592957 = 1347359) (by norm_num)
theorem B2126597 : Blo 1417528 2126597 := bbase (se 4 (by rfl) ⟨199368, by rfl⟩ : syracuseStep 2126597 = 398737) (by norm_num)
theorem B2126621 : Blo 1417528 2126621 := bbase (se 3 (by rfl) ⟨398741, by rfl⟩ : syracuseStep 2126621 = 797483) (by norm_num)
theorem B3191597 : Blo 1417528 3191597 := bbase (se 3 (by rfl) ⟨598424, by rfl⟩ : syracuseStep 3191597 = 1196849) (by norm_num)
theorem B2126645 : Blo 1417528 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B2691893 : Blo 1417528 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B6820661 : Blo 1417528 6820661 := bbase (se 5 (by rfl) ⟨319718, by rfl⟩ : syracuseStep 6820661 = 639437) (by norm_num)
theorem B2126669 : Blo 1417528 2126669 := bbase (se 3 (by rfl) ⟨398750, by rfl⟩ : syracuseStep 2126669 = 797501) (by norm_num)
theorem B2126693 : Blo 1417528 2126693 := bbase (se 4 (by rfl) ⟨199377, by rfl⟩ : syracuseStep 2126693 = 398755) (by norm_num)
theorem B3593069 : Blo 1417528 3593069 := bbase (se 3 (by rfl) ⟨673700, by rfl⟩ : syracuseStep 3593069 = 1347401) (by norm_num)
theorem B3191669 : Blo 1417528 3191669 := bbase (se 5 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 3191669 = 299219) (by norm_num)
theorem B2126717 : Blo 1417528 2126717 := bbase (se 3 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 2126717 = 797519) (by norm_num)
theorem B2126741 : Blo 1417528 2126741 := bbase (se 6 (by rfl) ⟨49845, by rfl⟩ : syracuseStep 2126741 = 99691) (by norm_num)
theorem B2126765 : Blo 1417528 2126765 := bbase (se 3 (by rfl) ⟨398768, by rfl⟩ : syracuseStep 2126765 = 797537) (by norm_num)
theorem B14554037 : Blo 1417528 14554037 := bbase (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) (by norm_num)
theorem B3191741 : Blo 1417528 3191741 := bbase (se 3 (by rfl) ⟨598451, by rfl⟩ : syracuseStep 3191741 = 1196903) (by norm_num)
theorem B2126789 : Blo 1417528 2126789 := bbase (se 4 (by rfl) ⟨199386, by rfl⟩ : syracuseStep 2126789 = 398773) (by norm_num)
theorem B2692045 : Blo 1417528 2692045 := bbase (se 3 (by rfl) ⟨504758, by rfl⟩ : syracuseStep 2692045 = 1009517) (by norm_num)
theorem B5747669 : Blo 1417528 5747669 := bbase (se 7 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 5747669 = 134711) (by norm_num)
theorem B4789205 : Blo 1417528 4789205 := bbase (se 7 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 4789205 = 112247) (by norm_num)
theorem B2126813 : Blo 1417528 2126813 := bbase (se 3 (by rfl) ⟨398777, by rfl⟩ : syracuseStep 2126813 = 797555) (by norm_num)
theorem B2126837 : Blo 1417528 2126837 := bbase (se 5 (by rfl) ⟨99695, by rfl⟩ : syracuseStep 2126837 = 199391) (by norm_num)
theorem B3191813 : Blo 1417528 3191813 := bbase (se 4 (by rfl) ⟨299232, by rfl⟩ : syracuseStep 3191813 = 598465) (by norm_num)
theorem B2126861 : Blo 1417528 2126861 := bbase (se 3 (by rfl) ⟨398786, by rfl⟩ : syracuseStep 2126861 = 797573) (by norm_num)
theorem B2126885 : Blo 1417528 2126885 := bbase (se 4 (by rfl) ⟨199395, by rfl⟩ : syracuseStep 2126885 = 398791) (by norm_num)
theorem B2126909 : Blo 1417528 2126909 := bbase (se 3 (by rfl) ⟨398795, by rfl⟩ : syracuseStep 2126909 = 797591) (by norm_num)
theorem B3191885 : Blo 1417528 3191885 := bbase (se 3 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 3191885 = 1196957) (by norm_num)
theorem B2126933 : Blo 1417528 2126933 := bbase (se 8 (by rfl) ⟨12462, by rfl⟩ : syracuseStep 2126933 = 24925) (by norm_num)
theorem B2126957 : Blo 1417528 2126957 := bbase (se 3 (by rfl) ⟨398804, by rfl⟩ : syracuseStep 2126957 = 797609) (by norm_num)
theorem B2020469 : Blo 1417528 2020469 := bbase (se 5 (by rfl) ⟨94709, by rfl⟩ : syracuseStep 2020469 = 189419) (by norm_num)
theorem B2126981 : Blo 1417528 2126981 := bbase (se 4 (by rfl) ⟨199404, by rfl⟩ : syracuseStep 2126981 = 398809) (by norm_num)
theorem B3191957 : Blo 1417528 3191957 := bbase (se 6 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 3191957 = 149623) (by norm_num)
theorem B2127005 : Blo 1417528 2127005 := bbase (se 3 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 2127005 = 797627) (by norm_num)
theorem B3028141 : Blo 1417528 3028141 := bbase (se 3 (by rfl) ⟨567776, by rfl⟩ : syracuseStep 3028141 = 1135553) (by norm_num)
theorem B2127029 : Blo 1417528 2127029 := bbase (se 5 (by rfl) ⟨99704, by rfl⟩ : syracuseStep 2127029 = 199409) (by norm_num)
theorem B2127053 : Blo 1417528 2127053 := bbase (se 3 (by rfl) ⟨398822, by rfl⟩ : syracuseStep 2127053 = 797645) (by norm_num)
theorem B3192029 : Blo 1417528 3192029 := bbase (se 3 (by rfl) ⟨598505, by rfl⟩ : syracuseStep 3192029 = 1197011) (by norm_num)
theorem B2127077 : Blo 1417528 2127077 := bbase (se 4 (by rfl) ⟨199413, by rfl⟩ : syracuseStep 2127077 = 398827) (by norm_num)
theorem B2127101 : Blo 1417528 2127101 := bbase (se 3 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 2127101 = 797663) (by norm_num)
theorem B2692349 : Blo 1417528 2692349 := bbase (se 3 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 2692349 = 1009631) (by norm_num)
theorem B2127125 : Blo 1417528 2127125 := bbase (se 6 (by rfl) ⟨49854, by rfl⟩ : syracuseStep 2127125 = 99709) (by norm_num)
theorem B3028261 : Blo 1417528 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B3192101 : Blo 1417528 3192101 := bbase (se 4 (by rfl) ⟨299259, by rfl⟩ : syracuseStep 3192101 = 598519) (by norm_num)
theorem B2127149 : Blo 1417528 2127149 := bbase (se 3 (by rfl) ⟨398840, by rfl⟩ : syracuseStep 2127149 = 797681) (by norm_num)
theorem B7181621 : Blo 1417528 7181621 := bbase (se 5 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 7181621 = 673277) (by norm_num)
theorem B2127173 : Blo 1417528 2127173 := bbase (se 4 (by rfl) ⟨199422, by rfl⟩ : syracuseStep 2127173 = 398845) (by norm_num)
theorem B2127197 : Blo 1417528 2127197 := bbase (se 3 (by rfl) ⟨398849, by rfl⟩ : syracuseStep 2127197 = 797699) (by norm_num)
theorem B3192173 : Blo 1417528 3192173 := bbase (se 3 (by rfl) ⟨598532, by rfl⟩ : syracuseStep 3192173 = 1197065) (by norm_num)
theorem B1594741 : Blo 1417528 1594741 := bbase (se 5 (by rfl) ⟨74753, by rfl⟩ : syracuseStep 1594741 = 149507) (by norm_num)
theorem B2127221 : Blo 1417528 2127221 := bbase (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) (by norm_num)
theorem B4789637 : Blo 1417528 4789637 := bbase (se 4 (by rfl) ⟨449028, by rfl⟩ : syracuseStep 4789637 = 898057) (by norm_num)
theorem B2127245 : Blo 1417528 2127245 := bbase (se 3 (by rfl) ⟨398858, by rfl⟩ : syracuseStep 2127245 = 797717) (by norm_num)
theorem B1594777 : Blo 1417528 1594777 := bbase (se 2 (by rfl) ⟨598041, by rfl⟩ : syracuseStep 1594777 = 1196083) (by norm_num)
theorem B2127269 : Blo 1417528 2127269 := bbase (se 4 (by rfl) ⟨199431, by rfl⟩ : syracuseStep 2127269 = 398863) (by norm_num)
theorem B3192245 : Blo 1417528 3192245 := bbase (se 5 (by rfl) ⟨149636, by rfl⟩ : syracuseStep 3192245 = 299273) (by norm_num)
theorem B1594813 : Blo 1417528 1594813 := bbase (se 3 (by rfl) ⟨299027, by rfl⟩ : syracuseStep 1594813 = 598055) (by norm_num)
theorem B2127293 : Blo 1417528 2127293 := bbase (se 3 (by rfl) ⟨398867, by rfl⟩ : syracuseStep 2127293 = 797735) (by norm_num)
theorem B10221013 : Blo 1417528 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B2127317 : Blo 1417528 2127317 := bbase (se 7 (by rfl) ⟨24929, by rfl⟩ : syracuseStep 2127317 = 49859) (by norm_num)
theorem B1594849 : Blo 1417528 1594849 := bbase (se 2 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 1594849 = 1196137) (by norm_num)
theorem B2127341 : Blo 1417528 2127341 := bbase (se 3 (by rfl) ⟨398876, by rfl⟩ : syracuseStep 2127341 = 797753) (by norm_num)
theorem B3192317 : Blo 1417528 3192317 := bbase (se 3 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 3192317 = 1197119) (by norm_num)
theorem B1594885 : Blo 1417528 1594885 := bbase (se 4 (by rfl) ⟨149520, by rfl⟩ : syracuseStep 1594885 = 299041) (by norm_num)
theorem B2127365 : Blo 1417528 2127365 := bbase (se 4 (by rfl) ⟨199440, by rfl⟩ : syracuseStep 2127365 = 398881) (by norm_num)
theorem B2127389 : Blo 1417528 2127389 := bbase (se 3 (by rfl) ⟨398885, by rfl⟩ : syracuseStep 2127389 = 797771) (by norm_num)
theorem B3028517 : Blo 1417528 3028517 := bbase (se 4 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 3028517 = 567847) (by norm_num)
theorem B1594921 : Blo 1417528 1594921 := bbase (se 2 (by rfl) ⟨598095, by rfl⟩ : syracuseStep 1594921 = 1196191) (by norm_num)
theorem B2127413 : Blo 1417528 2127413 := bbase (se 5 (by rfl) ⟨99722, by rfl⟩ : syracuseStep 2127413 = 199445) (by norm_num)
theorem B3192389 : Blo 1417528 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B1594957 : Blo 1417528 1594957 := bbase (se 3 (by rfl) ⟨299054, by rfl⟩ : syracuseStep 1594957 = 598109) (by norm_num)
theorem B2127437 : Blo 1417528 2127437 := bbase (se 3 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 2127437 = 797789) (by norm_num)
theorem B5535317 : Blo 1417528 5535317 := bbase (se 8 (by rfl) ⟨32433, by rfl⟩ : syracuseStep 5535317 = 64867) (by norm_num)
theorem B2127461 : Blo 1417528 2127461 := bbase (se 4 (by rfl) ⟨199449, by rfl⟩ : syracuseStep 2127461 = 398899) (by norm_num)
theorem B1594993 : Blo 1417528 1594993 := bbase (se 2 (by rfl) ⟨598122, by rfl⟩ : syracuseStep 1594993 = 1196245) (by norm_num)
theorem B8083061 : Blo 1417528 8083061 := bbase (se 5 (by rfl) ⟨378893, by rfl⟩ : syracuseStep 8083061 = 757787) (by norm_num)
theorem B12949109 : Blo 1417528 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B2127485 : Blo 1417528 2127485 := bbase (se 3 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 2127485 = 797807) (by norm_num)
theorem B3192461 : Blo 1417528 3192461 := bbase (se 3 (by rfl) ⟨598586, by rfl⟩ : syracuseStep 3192461 = 1197173) (by norm_num)
theorem B1595029 : Blo 1417528 1595029 := bbase (se 6 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 1595029 = 74767) (by norm_num)
theorem B2127509 : Blo 1417528 2127509 := bbase (se 6 (by rfl) ⟨49863, by rfl⟩ : syracuseStep 2127509 = 99727) (by norm_num)
theorem B2127533 : Blo 1417528 2127533 := bbase (se 3 (by rfl) ⟨398912, by rfl⟩ : syracuseStep 2127533 = 797825) (by norm_num)
theorem B6469301 : Blo 1417528 6469301 := bbase (se 5 (by rfl) ⟨303248, by rfl⟩ : syracuseStep 6469301 = 606497) (by norm_num)
theorem B1595065 : Blo 1417528 1595065 := bbase (se 2 (by rfl) ⟨598149, by rfl⟩ : syracuseStep 1595065 = 1196299) (by norm_num)
theorem B2127557 : Blo 1417528 2127557 := bbase (se 4 (by rfl) ⟨199458, by rfl⟩ : syracuseStep 2127557 = 398917) (by norm_num)
theorem B3192533 : Blo 1417528 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B1595101 : Blo 1417528 1595101 := bbase (se 3 (by rfl) ⟨299081, by rfl⟩ : syracuseStep 1595101 = 598163) (by norm_num)
theorem B2127581 : Blo 1417528 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B8074997 : Blo 1417528 8074997 := bbase (se 5 (by rfl) ⟨378515, by rfl⟩ : syracuseStep 8074997 = 757031) (by norm_num)
theorem B2127605 : Blo 1417528 2127605 := bbase (se 5 (by rfl) ⟨99731, by rfl⟩ : syracuseStep 2127605 = 199463) (by norm_num)
theorem B1595137 : Blo 1417528 1595137 := bbase (se 2 (by rfl) ⟨598176, by rfl⟩ : syracuseStep 1595137 = 1196353) (by norm_num)
theorem B2127629 : Blo 1417528 2127629 := bbase (se 3 (by rfl) ⟨398930, by rfl⟩ : syracuseStep 2127629 = 797861) (by norm_num)
theorem B3192605 : Blo 1417528 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B1595173 : Blo 1417528 1595173 := bbase (se 4 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 1595173 = 299095) (by norm_num)
theorem B2127653 : Blo 1417528 2127653 := bbase (se 4 (by rfl) ⟨199467, by rfl⟩ : syracuseStep 2127653 = 398935) (by norm_num)
theorem B4790069 : Blo 1417528 4790069 := bbase (se 5 (by rfl) ⟨224534, by rfl⟩ : syracuseStep 4790069 = 449069) (by norm_num)
theorem B2127677 : Blo 1417528 2127677 := bbase (se 3 (by rfl) ⟨398939, by rfl⟩ : syracuseStep 2127677 = 797879) (by norm_num)
theorem B1595209 : Blo 1417528 1595209 := bbase (se 2 (by rfl) ⟨598203, by rfl⟩ : syracuseStep 1595209 = 1196407) (by norm_num)
theorem B2127701 : Blo 1417528 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B3192677 : Blo 1417528 3192677 := bbase (se 4 (by rfl) ⟨299313, by rfl⟩ : syracuseStep 3192677 = 598627) (by norm_num)
theorem B1595245 : Blo 1417528 1595245 := bbase (se 3 (by rfl) ⟨299108, by rfl⟩ : syracuseStep 1595245 = 598217) (by norm_num)
theorem B2127725 : Blo 1417528 2127725 := bbase (se 3 (by rfl) ⟨398948, by rfl⟩ : syracuseStep 2127725 = 797897) (by norm_num)
theorem B2127749 : Blo 1417528 2127749 := bbase (se 4 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 2127749 = 398953) (by norm_num)
theorem B4855685 : Blo 1417528 4855685 := bbase (se 4 (by rfl) ⟨455220, by rfl⟩ : syracuseStep 4855685 = 910441) (by norm_num)
theorem B1595281 : Blo 1417528 1595281 := bbase (se 2 (by rfl) ⟨598230, by rfl⟩ : syracuseStep 1595281 = 1196461) (by norm_num)
theorem B2127773 : Blo 1417528 2127773 := bbase (se 3 (by rfl) ⟨398957, by rfl⟩ : syracuseStep 2127773 = 797915) (by norm_num)
theorem B3192749 : Blo 1417528 3192749 := bbase (se 3 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 3192749 = 1197281) (by norm_num)
theorem B1595317 : Blo 1417528 1595317 := bbase (se 5 (by rfl) ⟨74780, by rfl⟩ : syracuseStep 1595317 = 149561) (by norm_num)
theorem B2127797 : Blo 1417528 2127797 := bbase (se 5 (by rfl) ⟨99740, by rfl⟩ : syracuseStep 2127797 = 199481) (by norm_num)
theorem B2127821 : Blo 1417528 2127821 := bbase (se 3 (by rfl) ⟨398966, by rfl⟩ : syracuseStep 2127821 = 797933) (by norm_num)
theorem B1595353 : Blo 1417528 1595353 := bbase (se 2 (by rfl) ⟨598257, by rfl⟩ : syracuseStep 1595353 = 1196515) (by norm_num)
theorem B2127845 : Blo 1417528 2127845 := bbase (se 4 (by rfl) ⟨199485, by rfl⟩ : syracuseStep 2127845 = 398971) (by norm_num)
theorem B2693101 : Blo 1417528 2693101 := bbase (se 3 (by rfl) ⟨504956, by rfl⟩ : syracuseStep 2693101 = 1009913) (by norm_num)
theorem B3192821 : Blo 1417528 3192821 := bbase (se 5 (by rfl) ⟨149663, by rfl⟩ : syracuseStep 3192821 = 299327) (by norm_num)
theorem B1595389 : Blo 1417528 1595389 := bbase (se 3 (by rfl) ⟨299135, by rfl⟩ : syracuseStep 1595389 = 598271) (by norm_num)
theorem B2127869 : Blo 1417528 2127869 := bbase (se 3 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 2127869 = 797951) (by norm_num)
theorem B18176021 : Blo 1417528 18176021 := bbase (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) (by norm_num)
theorem B2127893 : Blo 1417528 2127893 := bbase (se 6 (by rfl) ⟨49872, by rfl⟩ : syracuseStep 2127893 = 99745) (by norm_num)
theorem B1595425 : Blo 1417528 1595425 := bbase (se 2 (by rfl) ⟨598284, by rfl⟩ : syracuseStep 1595425 = 1196569) (by norm_num)
theorem B2127917 : Blo 1417528 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B3192893 : Blo 1417528 3192893 := bbase (se 3 (by rfl) ⟨598667, by rfl⟩ : syracuseStep 3192893 = 1197335) (by norm_num)
theorem B1595461 : Blo 1417528 1595461 := bbase (se 4 (by rfl) ⟨149574, by rfl⟩ : syracuseStep 1595461 = 299149) (by norm_num)
theorem B2127941 : Blo 1417528 2127941 := bbase (se 4 (by rfl) ⟨199494, by rfl⟩ : syracuseStep 2127941 = 398989) (by norm_num)
theorem B2127965 : Blo 1417528 2127965 := bbase (se 3 (by rfl) ⟨398993, by rfl⟩ : syracuseStep 2127965 = 797987) (by norm_num)
theorem B5388389 : Blo 1417528 5388389 := bbase (se 4 (by rfl) ⟨505161, by rfl⟩ : syracuseStep 5388389 = 1010323) (by norm_num)
theorem B1595497 : Blo 1417528 1595497 := bbase (se 2 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 1595497 = 1196623) (by norm_num)
theorem B2127989 : Blo 1417528 2127989 := bbase (se 5 (by rfl) ⟨99749, by rfl⟩ : syracuseStep 2127989 = 199499) (by norm_num)
theorem B2693245 : Blo 1417528 2693245 := bbase (se 3 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 2693245 = 1009967) (by norm_num)
theorem B3192965 : Blo 1417528 3192965 := bbase (se 4 (by rfl) ⟨299340, by rfl⟩ : syracuseStep 3192965 = 598681) (by norm_num)
theorem B1595533 : Blo 1417528 1595533 := bbase (se 3 (by rfl) ⟨299162, by rfl⟩ : syracuseStep 1595533 = 598325) (by norm_num)
theorem B2128013 : Blo 1417528 2128013 := bbase (se 3 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 2128013 = 798005) (by norm_num)
theorem B2128037 : Blo 1417528 2128037 := bbase (se 4 (by rfl) ⟨199503, by rfl⟩ : syracuseStep 2128037 = 399007) (by norm_num)
theorem B1595569 : Blo 1417528 1595569 := bbase (se 2 (by rfl) ⟨598338, by rfl⟩ : syracuseStep 1595569 = 1196677) (by norm_num)
theorem B2128061 : Blo 1417528 2128061 := bbase (se 3 (by rfl) ⟨399011, by rfl⟩ : syracuseStep 2128061 = 798023) (by norm_num)
theorem B3193037 : Blo 1417528 3193037 := bbase (se 3 (by rfl) ⟨598694, by rfl⟩ : syracuseStep 3193037 = 1197389) (by norm_num)
theorem B1595605 : Blo 1417528 1595605 := bbase (se 7 (by rfl) ⟨18698, by rfl⟩ : syracuseStep 1595605 = 37397) (by norm_num)
theorem B2128085 : Blo 1417528 2128085 := bbase (se 7 (by rfl) ⟨24938, by rfl⟩ : syracuseStep 2128085 = 49877) (by norm_num)
theorem B4790501 : Blo 1417528 4790501 := bbase (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) (by norm_num)
theorem B2128109 : Blo 1417528 2128109 := bbase (se 3 (by rfl) ⟨399020, by rfl⟩ : syracuseStep 2128109 = 798041) (by norm_num)
theorem B1595641 : Blo 1417528 1595641 := bbase (se 2 (by rfl) ⟨598365, by rfl⟩ : syracuseStep 1595641 = 1196731) (by norm_num)
theorem B2128133 : Blo 1417528 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B3193109 : Blo 1417528 3193109 := bbase (se 6 (by rfl) ⟨74838, by rfl⟩ : syracuseStep 3193109 = 149677) (by norm_num)
theorem B1595677 : Blo 1417528 1595677 := bbase (se 3 (by rfl) ⟨299189, by rfl⟩ : syracuseStep 1595677 = 598379) (by norm_num)
theorem B2693405 : Blo 1417528 2693405 := bbase (se 3 (by rfl) ⟨505013, by rfl⟩ : syracuseStep 2693405 = 1010027) (by norm_num)
theorem B2128157 : Blo 1417528 2128157 := bbase (se 3 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 2128157 = 798059) (by norm_num)
theorem B2128181 : Blo 1417528 2128181 := bbase (se 5 (by rfl) ⟨99758, by rfl⟩ : syracuseStep 2128181 = 199517) (by norm_num)
theorem B1595713 : Blo 1417528 1595713 := bbase (se 2 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 1595713 = 1196785) (by norm_num)
theorem B5749061 : Blo 1417528 5749061 := bbase (se 4 (by rfl) ⟨538974, by rfl⟩ : syracuseStep 5749061 = 1077949) (by norm_num)
theorem B2128205 : Blo 1417528 2128205 := bbase (se 3 (by rfl) ⟨399038, by rfl⟩ : syracuseStep 2128205 = 798077) (by norm_num)
theorem B3193181 : Blo 1417528 3193181 := bbase (se 3 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 3193181 = 1197443) (by norm_num)
theorem B1595749 : Blo 1417528 1595749 := bbase (se 4 (by rfl) ⟨149601, by rfl⟩ : syracuseStep 1595749 = 299203) (by norm_num)
theorem B2128229 : Blo 1417528 2128229 := bbase (se 4 (by rfl) ⟨199521, by rfl⟩ : syracuseStep 2128229 = 399043) (by norm_num)
theorem B2128253 : Blo 1417528 2128253 := bbase (se 3 (by rfl) ⟨399047, by rfl⟩ : syracuseStep 2128253 = 798095) (by norm_num)
theorem B5388677 : Blo 1417528 5388677 := bbase (se 4 (by rfl) ⟨505188, by rfl⟩ : syracuseStep 5388677 = 1010377) (by norm_num)
theorem B1595785 : Blo 1417528 1595785 := bbase (se 2 (by rfl) ⟨598419, by rfl⟩ : syracuseStep 1595785 = 1196839) (by norm_num)
theorem B2128277 : Blo 1417528 2128277 := bbase (se 6 (by rfl) ⟨49881, by rfl⟩ : syracuseStep 2128277 = 99763) (by norm_num)
theorem B3029405 : Blo 1417528 3029405 := bbase (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) (by norm_num)
theorem B3193253 : Blo 1417528 3193253 := bbase (se 4 (by rfl) ⟨299367, by rfl⟩ : syracuseStep 3193253 = 598735) (by norm_num)
theorem B1595821 : Blo 1417528 1595821 := bbase (se 3 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 1595821 = 598433) (by norm_num)
theorem B2693549 : Blo 1417528 2693549 := bbase (se 3 (by rfl) ⟨505040, by rfl⟩ : syracuseStep 2693549 = 1010081) (by norm_num)
theorem B2128301 : Blo 1417528 2128301 := bbase (se 3 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 2128301 = 798113) (by norm_num)
theorem B2128325 : Blo 1417528 2128325 := bbase (se 4 (by rfl) ⟨199530, by rfl⟩ : syracuseStep 2128325 = 399061) (by norm_num)
theorem B2365901 : Blo 1417528 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B1595857 : Blo 1417528 1595857 := bbase (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) (by norm_num)
theorem B4544981 : Blo 1417528 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B2128349 : Blo 1417528 2128349 := bbase (se 3 (by rfl) ⟨399065, by rfl⟩ : syracuseStep 2128349 = 798131) (by norm_num)
theorem B3193325 : Blo 1417528 3193325 := bbase (se 3 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 3193325 = 1197497) (by norm_num)
theorem B1595893 : Blo 1417528 1595893 := bbase (se 5 (by rfl) ⟨74807, by rfl⟩ : syracuseStep 1595893 = 149615) (by norm_num)
theorem B2128373 : Blo 1417528 2128373 := bbase (se 5 (by rfl) ⟨99767, by rfl⟩ : syracuseStep 2128373 = 199535) (by norm_num)
theorem B3406333 : Blo 1417528 3406333 := bbase (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) (by norm_num)
theorem B1513981 : Blo 1417528 1513981 := bbase (se 3 (by rfl) ⟨283871, by rfl⟩ : syracuseStep 1513981 = 567743) (by norm_num)
theorem B1513985 : Blo 1417528 1513985 := bbase (se 2 (by rfl) ⟨567744, by rfl⟩ : syracuseStep 1513985 = 1135489) (by norm_num)
theorem B2128397 : Blo 1417528 2128397 := bbase (se 3 (by rfl) ⟨399074, by rfl⟩ : syracuseStep 2128397 = 798149) (by norm_num)
theorem B1595929 : Blo 1417528 1595929 := bbase (se 2 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 1595929 = 1196947) (by norm_num)
theorem B2128421 : Blo 1417528 2128421 := bbase (se 4 (by rfl) ⟨199539, by rfl⟩ : syracuseStep 2128421 = 399079) (by norm_num)
theorem B3193397 : Blo 1417528 3193397 := bbase (se 5 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 3193397 = 299381) (by norm_num)
theorem B1595965 : Blo 1417528 1595965 := bbase (se 3 (by rfl) ⟨299243, by rfl⟩ : syracuseStep 1595965 = 598487) (by norm_num)
theorem B2128445 : Blo 1417528 2128445 := bbase (se 3 (by rfl) ⟨399083, by rfl⟩ : syracuseStep 2128445 = 798167) (by norm_num)
theorem B7182917 : Blo 1417528 7182917 := bbase (se 4 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 7182917 = 1346797) (by norm_num)
theorem B15964757 : Blo 1417528 15964757 := bbase (se 8 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 15964757 = 187087) (by norm_num)
theorem B2128469 : Blo 1417528 2128469 := bbase (se 8 (by rfl) ⟨12471, by rfl⟩ : syracuseStep 2128469 = 24943) (by norm_num)
theorem B1596001 : Blo 1417528 1596001 := bbase (se 2 (by rfl) ⟨598500, by rfl⟩ : syracuseStep 1596001 = 1197001) (by norm_num)
theorem B2128493 : Blo 1417528 2128493 := bbase (se 3 (by rfl) ⟨399092, by rfl⟩ : syracuseStep 2128493 = 798185) (by norm_num)
theorem B3193469 : Blo 1417528 3193469 := bbase (se 3 (by rfl) ⟨598775, by rfl⟩ : syracuseStep 3193469 = 1197551) (by norm_num)
theorem B1596037 : Blo 1417528 1596037 := bbase (se 4 (by rfl) ⟨149628, by rfl⟩ : syracuseStep 1596037 = 299257) (by norm_num)
theorem B2128517 : Blo 1417528 2128517 := bbase (se 4 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 2128517 = 399097) (by norm_num)
theorem B2046605 : Blo 1417528 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B3029645 : Blo 1417528 3029645 := bbase (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) (by norm_num)
theorem B2128541 : Blo 1417528 2128541 := bbase (se 3 (by rfl) ⟨399101, by rfl⟩ : syracuseStep 2128541 = 798203) (by norm_num)
theorem B1596073 : Blo 1417528 1596073 := bbase (se 2 (by rfl) ⟨598527, by rfl⟩ : syracuseStep 1596073 = 1197055) (by norm_num)
theorem B2128565 : Blo 1417528 2128565 := bbase (se 5 (by rfl) ⟨99776, by rfl⟩ : syracuseStep 2128565 = 199553) (by norm_num)
theorem B3193541 : Blo 1417528 3193541 := bbase (se 4 (by rfl) ⟨299394, by rfl⟩ : syracuseStep 3193541 = 598789) (by norm_num)
theorem B1596109 : Blo 1417528 1596109 := bbase (se 3 (by rfl) ⟨299270, by rfl⟩ : syracuseStep 1596109 = 598541) (by norm_num)
theorem B2693837 : Blo 1417528 2693837 := bbase (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) (by norm_num)
theorem B2128589 : Blo 1417528 2128589 := bbase (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) (by norm_num)
theorem B2128613 : Blo 1417528 2128613 := bbase (se 4 (by rfl) ⟨199557, by rfl⟩ : syracuseStep 2128613 = 399115) (by norm_num)
theorem B1596145 : Blo 1417528 1596145 := bbase (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) (by norm_num)
theorem B2128637 : Blo 1417528 2128637 := bbase (se 3 (by rfl) ⟨399119, by rfl⟩ : syracuseStep 2128637 = 798239) (by norm_num)
theorem B3193613 : Blo 1417528 3193613 := bbase (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) (by norm_num)
theorem B1596181 : Blo 1417528 1596181 := bbase (se 6 (by rfl) ⟨37410, by rfl⟩ : syracuseStep 1596181 = 74821) (by norm_num)
theorem B2128661 : Blo 1417528 2128661 := bbase (se 6 (by rfl) ⟨49890, by rfl⟩ : syracuseStep 2128661 = 99781) (by norm_num)
theorem B8084245 : Blo 1417528 8084245 := bbase (se 6 (by rfl) ⟨189474, by rfl⟩ : syracuseStep 8084245 = 378949) (by norm_num)
theorem B2128685 : Blo 1417528 2128685 := bbase (se 3 (by rfl) ⟨399128, by rfl⟩ : syracuseStep 2128685 = 798257) (by norm_num)
theorem B1596217 : Blo 1417528 1596217 := bbase (se 2 (by rfl) ⟨598581, by rfl⟩ : syracuseStep 1596217 = 1197163) (by norm_num)
theorem B2128709 : Blo 1417528 2128709 := bbase (se 4 (by rfl) ⟨199566, by rfl⟩ : syracuseStep 2128709 = 399133) (by norm_num)
theorem B3193685 : Blo 1417528 3193685 := bbase (se 9 (by rfl) ⟨9356, by rfl⟩ : syracuseStep 3193685 = 18713) (by norm_num)
theorem B1596253 : Blo 1417528 1596253 := bbase (se 3 (by rfl) ⟨299297, by rfl⟩ : syracuseStep 1596253 = 598595) (by norm_num)
theorem B2128733 : Blo 1417528 2128733 := bbase (se 3 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 2128733 = 798275) (by norm_num)
theorem B2693989 : Blo 1417528 2693989 := bbase (se 4 (by rfl) ⟨252561, by rfl⟩ : syracuseStep 2693989 = 505123) (by norm_num)
theorem B2128757 : Blo 1417528 2128757 := bbase (se 5 (by rfl) ⟨99785, by rfl⟩ : syracuseStep 2128757 = 199571) (by norm_num)
theorem B1596289 : Blo 1417528 1596289 := bbase (se 2 (by rfl) ⟨598608, by rfl⟩ : syracuseStep 1596289 = 1197217) (by norm_num)
theorem B2128781 : Blo 1417528 2128781 := bbase (se 3 (by rfl) ⟨399146, by rfl⟩ : syracuseStep 2128781 = 798293) (by norm_num)
theorem B3193757 : Blo 1417528 3193757 := bbase (se 3 (by rfl) ⟨598829, by rfl⟩ : syracuseStep 3193757 = 1197659) (by norm_num)
theorem B1596325 : Blo 1417528 1596325 := bbase (se 4 (by rfl) ⟨149655, by rfl⟩ : syracuseStep 1596325 = 299311) (by norm_num)
theorem B2128805 : Blo 1417528 2128805 := bbase (se 4 (by rfl) ⟨199575, by rfl⟩ : syracuseStep 2128805 = 399151) (by norm_num)
theorem B2128829 : Blo 1417528 2128829 := bbase (se 3 (by rfl) ⟨399155, by rfl⟩ : syracuseStep 2128829 = 798311) (by norm_num)
theorem B6060997 : Blo 1417528 6060997 := bbase (se 4 (by rfl) ⟨568218, by rfl⟩ : syracuseStep 6060997 = 1136437) (by norm_num)
theorem B1596361 : Blo 1417528 1596361 := bbase (se 2 (by rfl) ⟨598635, by rfl⟩ : syracuseStep 1596361 = 1197271) (by norm_num)
theorem B2128853 : Blo 1417528 2128853 := bbase (se 7 (by rfl) ⟨24947, by rfl⟩ : syracuseStep 2128853 = 49895) (by norm_num)
theorem B3193829 : Blo 1417528 3193829 := bbase (se 4 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 3193829 = 598843) (by norm_num)
theorem B1596397 : Blo 1417528 1596397 := bbase (se 3 (by rfl) ⟨299324, by rfl⟩ : syracuseStep 1596397 = 598649) (by norm_num)
theorem B2128877 : Blo 1417528 2128877 := bbase (se 3 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 2128877 = 798329) (by norm_num)
theorem B2128901 : Blo 1417528 2128901 := bbase (se 4 (by rfl) ⟨199584, by rfl⟩ : syracuseStep 2128901 = 399169) (by norm_num)
theorem B1596433 : Blo 1417528 1596433 := bbase (se 2 (by rfl) ⟨598662, by rfl⟩ : syracuseStep 1596433 = 1197325) (by norm_num)
theorem B7478293 : Blo 1417528 7478293 := bbase (se 6 (by rfl) ⟨175272, by rfl⟩ : syracuseStep 7478293 = 350545) (by norm_num)
theorem B2128925 : Blo 1417528 2128925 := bbase (se 3 (by rfl) ⟨399173, by rfl⟩ : syracuseStep 2128925 = 798347) (by norm_num)
theorem B1727525 : Blo 1417528 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B3193901 : Blo 1417528 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B1514549 : Blo 1417528 1514549 := bbase (se 5 (by rfl) ⟨70994, by rfl⟩ : syracuseStep 1514549 = 141989) (by norm_num)
theorem B3456053 : Blo 1417528 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1596469 : Blo 1417528 1596469 := bbase (se 5 (by rfl) ⟨74834, by rfl⟩ : syracuseStep 1596469 = 149669) (by norm_num)
theorem B2128949 : Blo 1417528 2128949 := bbase (se 5 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 2128949 = 199589) (by norm_num)
theorem B2128973 : Blo 1417528 2128973 := bbase (se 3 (by rfl) ⟨399182, by rfl⟩ : syracuseStep 2128973 = 798365) (by norm_num)
theorem B1596505 : Blo 1417528 1596505 := bbase (se 2 (by rfl) ⟨598689, by rfl⟩ : syracuseStep 1596505 = 1197379) (by norm_num)
theorem B2128997 : Blo 1417528 2128997 := bbase (se 4 (by rfl) ⟨199593, by rfl⟩ : syracuseStep 2128997 = 399187) (by norm_num)
theorem B1596541 : Blo 1417528 1596541 := bbase (se 3 (by rfl) ⟨299351, by rfl⟩ : syracuseStep 1596541 = 598703) (by norm_num)
theorem B2129021 : Blo 1417528 2129021 := bbase (se 3 (by rfl) ⟨399191, by rfl⟩ : syracuseStep 2129021 = 798383) (by norm_num)
theorem B3030149 : Blo 1417528 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B3030157 : Blo 1417528 3030157 := bbase (se 3 (by rfl) ⟨568154, by rfl⟩ : syracuseStep 3030157 = 1136309) (by norm_num)
theorem B13810837 : Blo 1417528 13810837 := bbase (se 6 (by rfl) ⟨323691, by rfl⟩ : syracuseStep 13810837 = 647383) (by norm_num)
theorem B3406997 : Blo 1417528 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B2694293 : Blo 1417528 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2129045 : Blo 1417528 2129045 := bbase (se 6 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 2129045 = 99799) (by norm_num)
theorem B1596577 : Blo 1417528 1596577 := bbase (se 2 (by rfl) ⟨598716, by rfl⟩ : syracuseStep 1596577 = 1197433) (by norm_num)
theorem B2129069 : Blo 1417528 2129069 := bbase (se 3 (by rfl) ⟨399200, by rfl⟩ : syracuseStep 2129069 = 798401) (by norm_num)
theorem B1596613 : Blo 1417528 1596613 := bbase (se 4 (by rfl) ⟨149682, by rfl⟩ : syracuseStep 1596613 = 299365) (by norm_num)
theorem B2129093 : Blo 1417528 2129093 := bbase (se 4 (by rfl) ⟨199602, by rfl⟩ : syracuseStep 2129093 = 399205) (by norm_num)
theorem B5749973 : Blo 1417528 5749973 := bbase (se 7 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 5749973 = 134765) (by norm_num)
theorem B2129117 : Blo 1417528 2129117 := bbase (se 3 (by rfl) ⟨399209, by rfl⟩ : syracuseStep 2129117 = 798419) (by norm_num)
theorem B1596649 : Blo 1417528 1596649 := bbase (se 2 (by rfl) ⟨598743, by rfl⟩ : syracuseStep 1596649 = 1197487) (by norm_num)
theorem B1514737 : Blo 1417528 1514737 := bbase (se 2 (by rfl) ⟨568026, by rfl⟩ : syracuseStep 1514737 = 1136053) (by norm_num)
theorem B3833077 : Blo 1417528 3833077 := bbase (se 5 (by rfl) ⟨179675, by rfl⟩ : syracuseStep 3833077 = 359351) (by norm_num)
theorem B2129141 : Blo 1417528 2129141 := bbase (se 5 (by rfl) ⟨99803, by rfl⟩ : syracuseStep 2129141 = 199607) (by norm_num)
theorem B1596685 : Blo 1417528 1596685 := bbase (se 3 (by rfl) ⟨299378, by rfl⟩ : syracuseStep 1596685 = 598757) (by norm_num)
theorem B2129165 : Blo 1417528 2129165 := bbase (se 3 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 2129165 = 798437) (by norm_num)
theorem B2129189 : Blo 1417528 2129189 := bbase (se 4 (by rfl) ⟨199611, by rfl⟩ : syracuseStep 2129189 = 399223) (by norm_num)
theorem B1596721 : Blo 1417528 1596721 := bbase (se 2 (by rfl) ⟨598770, by rfl⟩ : syracuseStep 1596721 = 1197541) (by norm_num)
theorem B2129213 : Blo 1417528 2129213 := bbase (se 3 (by rfl) ⟨399227, by rfl⟩ : syracuseStep 2129213 = 798455) (by norm_num)
theorem B4545877 : Blo 1417528 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B1596757 : Blo 1417528 1596757 := bbase (se 11 (by rfl) ⟨1169, by rfl⟩ : syracuseStep 1596757 = 2339) (by norm_num)
theorem B2129237 : Blo 1417528 2129237 := bbase (se 11 (by rfl) ⟨1559, by rfl⟩ : syracuseStep 2129237 = 3119) (by norm_num)
theorem B2129261 : Blo 1417528 2129261 := bbase (se 3 (by rfl) ⟨399236, by rfl⟩ : syracuseStep 2129261 = 798473) (by norm_num)
theorem B1596793 : Blo 1417528 1596793 := bbase (se 2 (by rfl) ⟨598797, by rfl⟩ : syracuseStep 1596793 = 1197595) (by norm_num)
theorem B2129285 : Blo 1417528 2129285 := bbase (se 4 (by rfl) ⟨199620, by rfl⟩ : syracuseStep 2129285 = 399241) (by norm_num)
theorem B14548373 : Blo 1417528 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B1596829 : Blo 1417528 1596829 := bbase (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) (by norm_num)
theorem B1596865 : Blo 1417528 1596865 := bbase (se 2 (by rfl) ⟨598824, by rfl⟩ : syracuseStep 1596865 = 1197649) (by norm_num)
theorem B1596901 : Blo 1417528 1596901 := bbase (se 4 (by rfl) ⟨149709, by rfl⟩ : syracuseStep 1596901 = 299419) (by norm_num)
theorem B1596937 : Blo 1417528 1596937 := bbase (se 2 (by rfl) ⟨598851, by rfl⟩ : syracuseStep 1596937 = 1197703) (by norm_num)
theorem B3456605 : Blo 1417528 3456605 := bbase (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) (by norm_num)
theorem B5111429 : Blo 1417528 5111429 := bbase (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) (by norm_num)
theorem B7184213 : Blo 1417528 7184213 := bbase (se 9 (by rfl) ⟨21047, by rfl⟩ : syracuseStep 7184213 = 42095) (by norm_num)
theorem B1458109 : Blo 1417528 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1916885 : Blo 1417528 1916885 := bbase (se 7 (by rfl) ⟨22463, by rfl⟩ : syracuseStep 1916885 = 44927) (by norm_num)
theorem B20742101 : Blo 1417528 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B1703921 : Blo 1417528 1703921 := bbase (se 2 (by rfl) ⟨638970, by rfl⟩ : syracuseStep 1703921 = 1277941) (by norm_num)
theorem B4784237 : Blo 1417528 4784237 := bstep (se 3 (by rfl) ⟨897044, by rfl⟩ : syracuseStep 4784237 = 1794089) B1794089
theorem B3588209 : Blo 1417528 3588209 := bstep (se 2 (by rfl) ⟨1345578, by rfl⟩ : syracuseStep 3588209 = 2691157) B2691157
theorem B2392193 : Blo 1417528 2392193 := bstep (se 2 (by rfl) ⟨897072, by rfl⟩ : syracuseStep 2392193 = 1794145) B1794145
theorem B4038797 : Blo 1417528 4038797 := bstep (se 3 (by rfl) ⟨757274, by rfl⟩ : syracuseStep 4038797 = 1514549) B1514549
theorem B4784291 : Blo 1417528 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B3588259 : Blo 1417528 3588259 := bstep (se 1 (by rfl) ⟨2691194, by rfl⟩ : syracuseStep 3588259 = 5382389) B5382389
theorem B2392321 : Blo 1417528 2392321 := bstep (se 2 (by rfl) ⟨897120, by rfl⟩ : syracuseStep 2392321 = 1794241) B1794241
theorem B1794307 : Blo 1417528 1794307 := bstep (se 1 (by rfl) ⟨1345730, by rfl⟩ : syracuseStep 1794307 = 2691461) B2691461
theorem B2392355 : Blo 1417528 2392355 := bstep (se 1 (by rfl) ⟨1794266, by rfl⟩ : syracuseStep 2392355 = 3588533) B3588533
theorem B3588401 : Blo 1417528 3588401 := bstep (se 2 (by rfl) ⟨1345650, by rfl⟩ : syracuseStep 3588401 = 2691301) B2691301
theorem B1417539 : Blo 1417528 1417539 := bstep (se 1 (by rfl) ⟨1063154, by rfl⟩ : syracuseStep 1417539 = 2126309) B2126309
theorem B4038979 : Blo 1417528 4038979 := bstep (se 1 (by rfl) ⟨3029234, by rfl⟩ : syracuseStep 4038979 = 6058469) B6058469
theorem B1417555 : Blo 1417528 1417555 := bstep (se 1 (by rfl) ⟨1063166, by rfl⟩ : syracuseStep 1417555 = 2126333) B2126333
theorem B1417571 : Blo 1417528 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B1794403 : Blo 1417528 1794403 := bstep (se 1 (by rfl) ⟨1345802, by rfl⟩ : syracuseStep 1794403 = 2691605) B2691605
theorem B3408227 : Blo 1417528 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B3834221 : Blo 1417528 3834221 := bstep (se 3 (by rfl) ⟨718916, by rfl⟩ : syracuseStep 3834221 = 1437833) B1437833
theorem B1417587 : Blo 1417528 1417587 := bstep (se 1 (by rfl) ⟨1063190, by rfl⟩ : syracuseStep 1417587 = 2126381) B2126381
theorem B1417603 : Blo 1417528 1417603 := bstep (se 1 (by rfl) ⟨1063202, by rfl⟩ : syracuseStep 1417603 = 2126405) B2126405
theorem B1417619 : Blo 1417528 1417619 := bstep (se 1 (by rfl) ⟨1063214, by rfl⟩ : syracuseStep 1417619 = 2126429) B2126429
theorem B1417635 : Blo 1417528 1417635 := bstep (se 1 (by rfl) ⟨1063226, by rfl⟩ : syracuseStep 1417635 = 2126453) B2126453
theorem B2392483 : Blo 1417528 2392483 := bstep (se 1 (by rfl) ⟨1794362, by rfl⟩ : syracuseStep 2392483 = 3588725) B3588725
theorem B4546979 : Blo 1417528 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B4784561 : Blo 1417528 4784561 := bstep (se 2 (by rfl) ⟨1794210, by rfl⟩ : syracuseStep 4784561 = 3588421) B3588421
theorem B1417651 : Blo 1417528 1417651 := bstep (se 1 (by rfl) ⟨1063238, by rfl⟩ : syracuseStep 1417651 = 2126477) B2126477
theorem B1417667 : Blo 1417528 1417667 := bstep (se 1 (by rfl) ⟨1063250, by rfl⟩ : syracuseStep 1417667 = 2126501) B2126501
theorem B1417683 : Blo 1417528 1417683 := bstep (se 1 (by rfl) ⟨1063262, by rfl⟩ : syracuseStep 1417683 = 2126525) B2126525
theorem B1819091 : Blo 1417528 1819091 := bstep (se 1 (by rfl) ⟨1364318, by rfl⟩ : syracuseStep 1819091 = 2728637) B2728637
theorem B1417699 : Blo 1417528 1417699 := bstep (se 1 (by rfl) ⟨1063274, by rfl⟩ : syracuseStep 1417699 = 2126549) B2126549
theorem B4039139 : Blo 1417528 4039139 := bstep (se 1 (by rfl) ⟨3029354, by rfl⟩ : syracuseStep 4039139 = 6058709) B6058709
theorem B1417715 : Blo 1417528 1417715 := bstep (se 1 (by rfl) ⟨1063286, by rfl⟩ : syracuseStep 1417715 = 2126573) B2126573
theorem B1417731 : Blo 1417528 1417731 := bstep (se 1 (by rfl) ⟨1063298, by rfl⟩ : syracuseStep 1417731 = 2126597) B2126597
theorem B1417747 : Blo 1417528 1417747 := bstep (se 1 (by rfl) ⟨1063310, by rfl⟩ : syracuseStep 1417747 = 2126621) B2126621
theorem B1417763 : Blo 1417528 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B4547107 : Blo 1417528 4547107 := bstep (se 1 (by rfl) ⟨3410330, by rfl⟩ : syracuseStep 4547107 = 6820661) B6820661
theorem B2392625 : Blo 1417528 2392625 := bstep (se 2 (by rfl) ⟨897234, by rfl⟩ : syracuseStep 2392625 = 1794469) B1794469
theorem B1417779 : Blo 1417528 1417779 := bstep (se 1 (by rfl) ⟨1063334, by rfl⟩ : syracuseStep 1417779 = 2126669) B2126669
theorem B1417795 : Blo 1417528 1417795 := bstep (se 1 (by rfl) ⟨1063346, by rfl⟩ : syracuseStep 1417795 = 2126693) B2126693
theorem B1417811 : Blo 1417528 1417811 := bstep (se 1 (by rfl) ⟨1063358, by rfl⟩ : syracuseStep 1417811 = 2126717) B2126717
theorem B10764899 : Blo 1417528 10764899 := bstep (se 1 (by rfl) ⟨8073674, by rfl⟩ : syracuseStep 10764899 = 16147349) B16147349
theorem B1417827 : Blo 1417528 1417827 := bstep (se 1 (by rfl) ⟨1063370, by rfl⟩ : syracuseStep 1417827 = 2126741) B2126741
theorem B1417843 : Blo 1417528 1417843 := bstep (se 1 (by rfl) ⟨1063382, by rfl⟩ : syracuseStep 1417843 = 2126765) B2126765
theorem B1417859 : Blo 1417528 1417859 := bstep (se 1 (by rfl) ⟨1063394, by rfl⟩ : syracuseStep 1417859 = 2126789) B2126789
theorem B1417875 : Blo 1417528 1417875 := bstep (se 1 (by rfl) ⟨1063406, by rfl⟩ : syracuseStep 1417875 = 2126813) B2126813
theorem B1417891 : Blo 1417528 1417891 := bstep (se 1 (by rfl) ⟨1063418, by rfl⟩ : syracuseStep 1417891 = 2126837) B2126837
theorem B2392753 : Blo 1417528 2392753 := bstep (se 2 (by rfl) ⟨897282, by rfl⟩ : syracuseStep 2392753 = 1794565) B1794565
theorem B1417907 : Blo 1417528 1417907 := bstep (se 1 (by rfl) ⟨1063430, by rfl⟩ : syracuseStep 1417907 = 2126861) B2126861
theorem B1417923 : Blo 1417528 1417923 := bstep (se 1 (by rfl) ⟨1063442, by rfl⟩ : syracuseStep 1417923 = 2126885) B2126885
theorem B1417939 : Blo 1417528 1417939 := bstep (se 1 (by rfl) ⟨1063454, by rfl⟩ : syracuseStep 1417939 = 2126909) B2126909
theorem B2392787 : Blo 1417528 2392787 := bstep (se 1 (by rfl) ⟨1794590, by rfl⟩ : syracuseStep 2392787 = 3589181) B3589181
theorem B1417955 : Blo 1417528 1417955 := bstep (se 1 (by rfl) ⟨1063466, by rfl⟩ : syracuseStep 1417955 = 2126933) B2126933
theorem B1417971 : Blo 1417528 1417971 := bstep (se 1 (by rfl) ⟨1063478, by rfl⟩ : syracuseStep 1417971 = 2126957) B2126957
theorem B1417987 : Blo 1417528 1417987 := bstep (se 1 (by rfl) ⟨1063490, by rfl⟩ : syracuseStep 1417987 = 2126981) B2126981
theorem B1418003 : Blo 1417528 1418003 := bstep (se 1 (by rfl) ⟨1063502, by rfl⟩ : syracuseStep 1418003 = 2127005) B2127005
theorem B2589475 : Blo 1417528 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B1418019 : Blo 1417528 1418019 := bstep (se 1 (by rfl) ⟨1063514, by rfl⟩ : syracuseStep 1418019 = 2127029) B2127029
theorem B1418035 : Blo 1417528 1418035 := bstep (se 1 (by rfl) ⟨1063526, by rfl⟩ : syracuseStep 1418035 = 2127053) B2127053
theorem B1418051 : Blo 1417528 1418051 := bstep (se 1 (by rfl) ⟨1063538, by rfl⟩ : syracuseStep 1418051 = 2127077) B2127077
theorem B2392915 : Blo 1417528 2392915 := bstep (se 1 (by rfl) ⟨1794686, by rfl⟩ : syracuseStep 2392915 = 3589373) B3589373
theorem B1418067 : Blo 1417528 1418067 := bstep (se 1 (by rfl) ⟨1063550, by rfl⟩ : syracuseStep 1418067 = 2127101) B2127101
theorem B1794899 : Blo 1417528 1794899 := bstep (se 1 (by rfl) ⟨1346174, by rfl⟩ : syracuseStep 1794899 = 2692349) B2692349
theorem B1418083 : Blo 1417528 1418083 := bstep (se 1 (by rfl) ⟨1063562, by rfl⟩ : syracuseStep 1418083 = 2127125) B2127125
theorem B4547441 : Blo 1417528 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B1418099 : Blo 1417528 1418099 := bstep (se 1 (by rfl) ⟨1063574, by rfl⟩ : syracuseStep 1418099 = 2127149) B2127149
theorem B1418115 : Blo 1417528 1418115 := bstep (se 1 (by rfl) ⟨1063586, by rfl⟩ : syracuseStep 1418115 = 2127173) B2127173
theorem B1418131 : Blo 1417528 1418131 := bstep (se 1 (by rfl) ⟨1063598, by rfl⟩ : syracuseStep 1418131 = 2127197) B2127197
theorem B1418147 : Blo 1417528 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B1418163 : Blo 1417528 1418163 := bstep (se 1 (by rfl) ⟨1063622, by rfl⟩ : syracuseStep 1418163 = 2127245) B2127245
theorem B1418179 : Blo 1417528 1418179 := bstep (se 1 (by rfl) ⟨1063634, by rfl⟩ : syracuseStep 1418179 = 2127269) B2127269
theorem B4785101 : Blo 1417528 4785101 := bstep (se 3 (by rfl) ⟨897206, by rfl⟩ : syracuseStep 4785101 = 1794413) B1794413
theorem B1418195 : Blo 1417528 1418195 := bstep (se 1 (by rfl) ⟨1063646, by rfl⟩ : syracuseStep 1418195 = 2127293) B2127293
theorem B2393057 : Blo 1417528 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B1418211 : Blo 1417528 1418211 := bstep (se 1 (by rfl) ⟨1063658, by rfl⟩ : syracuseStep 1418211 = 2127317) B2127317
theorem B1418227 : Blo 1417528 1418227 := bstep (se 1 (by rfl) ⟨1063670, by rfl⟩ : syracuseStep 1418227 = 2127341) B2127341
theorem B4785155 : Blo 1417528 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B1418243 : Blo 1417528 1418243 := bstep (se 1 (by rfl) ⟨1063682, by rfl⟩ : syracuseStep 1418243 = 2127365) B2127365
theorem B1418259 : Blo 1417528 1418259 := bstep (se 1 (by rfl) ⟨1063694, by rfl⟩ : syracuseStep 1418259 = 2127389) B2127389
theorem B1418275 : Blo 1417528 1418275 := bstep (se 1 (by rfl) ⟨1063706, by rfl⟩ : syracuseStep 1418275 = 2127413) B2127413
theorem B2425907 : Blo 1417528 2425907 := bstep (se 1 (by rfl) ⟨1819430, by rfl⟩ : syracuseStep 2425907 = 3638861) B3638861
theorem B1418291 : Blo 1417528 1418291 := bstep (se 1 (by rfl) ⟨1063718, by rfl⟩ : syracuseStep 1418291 = 2127437) B2127437
theorem B1418307 : Blo 1417528 1418307 := bstep (se 1 (by rfl) ⟨1063730, by rfl⟩ : syracuseStep 1418307 = 2127461) B2127461
theorem B8078413 : Blo 1417528 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B1418323 : Blo 1417528 1418323 := bstep (se 1 (by rfl) ⟨1063742, by rfl⟩ : syracuseStep 1418323 = 2127485) B2127485
theorem B2393185 : Blo 1417528 2393185 := bstep (se 2 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 2393185 = 1794889) B1794889
theorem B1418339 : Blo 1417528 1418339 := bstep (se 1 (by rfl) ⟨1063754, by rfl⟩ : syracuseStep 1418339 = 2127509) B2127509
theorem B1418355 : Blo 1417528 1418355 := bstep (se 1 (by rfl) ⟨1063766, by rfl⟩ : syracuseStep 1418355 = 2127533) B2127533
theorem B2393219 : Blo 1417528 2393219 := bstep (se 1 (by rfl) ⟨1794914, by rfl⟩ : syracuseStep 2393219 = 3589829) B3589829
theorem B1418371 : Blo 1417528 1418371 := bstep (se 1 (by rfl) ⟨1063778, by rfl⟩ : syracuseStep 1418371 = 2127557) B2127557
theorem B1418387 : Blo 1417528 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B5383331 : Blo 1417528 5383331 := bstep (se 1 (by rfl) ⟨4037498, by rfl⟩ : syracuseStep 5383331 = 8074997) B8074997
theorem B1418403 : Blo 1417528 1418403 := bstep (se 1 (by rfl) ⟨1063802, by rfl⟩ : syracuseStep 1418403 = 2127605) B2127605
theorem B3409073 : Blo 1417528 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B1418419 : Blo 1417528 1418419 := bstep (se 1 (by rfl) ⟨1063814, by rfl⟩ : syracuseStep 1418419 = 2127629) B2127629
theorem B1418435 : Blo 1417528 1418435 := bstep (se 1 (by rfl) ⟨1063826, by rfl⟩ : syracuseStep 1418435 = 2127653) B2127653
theorem B1418451 : Blo 1417528 1418451 := bstep (se 1 (by rfl) ⟨1063838, by rfl⟩ : syracuseStep 1418451 = 2127677) B2127677
theorem B1418467 : Blo 1417528 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B1418483 : Blo 1417528 1418483 := bstep (se 1 (by rfl) ⟨1063862, by rfl⟩ : syracuseStep 1418483 = 2127725) B2127725
theorem B2393347 : Blo 1417528 2393347 := bstep (se 1 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 2393347 = 3590021) B3590021
theorem B1418499 : Blo 1417528 1418499 := bstep (se 1 (by rfl) ⟨1063874, by rfl⟩ : syracuseStep 1418499 = 2127749) B2127749
theorem B4785425 : Blo 1417528 4785425 := bstep (se 2 (by rfl) ⟨1794534, by rfl⟩ : syracuseStep 4785425 = 3589069) B3589069
theorem B3589393 : Blo 1417528 3589393 := bstep (se 2 (by rfl) ⟨1346022, by rfl⟩ : syracuseStep 3589393 = 2692045) B2692045
theorem B1418515 : Blo 1417528 1418515 := bstep (se 1 (by rfl) ⟨1063886, by rfl⟩ : syracuseStep 1418515 = 2127773) B2127773
theorem B1418531 : Blo 1417528 1418531 := bstep (se 1 (by rfl) ⟨1063898, by rfl⟩ : syracuseStep 1418531 = 2127797) B2127797
theorem B1418547 : Blo 1417528 1418547 := bstep (se 1 (by rfl) ⟨1063910, by rfl⟩ : syracuseStep 1418547 = 2127821) B2127821
theorem B1418563 : Blo 1417528 1418563 := bstep (se 1 (by rfl) ⟨1063922, by rfl⟩ : syracuseStep 1418563 = 2127845) B2127845
theorem B1418579 : Blo 1417528 1418579 := bstep (se 1 (by rfl) ⟨1063934, by rfl⟩ : syracuseStep 1418579 = 2127869) B2127869
theorem B7177571 : Blo 1417528 7177571 := bstep (se 1 (by rfl) ⟨5383178, by rfl⟩ : syracuseStep 7177571 = 10766357) B10766357
theorem B12117347 : Blo 1417528 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B1418595 : Blo 1417528 1418595 := bstep (se 1 (by rfl) ⟨1063946, by rfl⟩ : syracuseStep 1418595 = 2127893) B2127893
theorem B9971057 : Blo 1417528 9971057 := bstep (se 2 (by rfl) ⟨3739146, by rfl⟩ : syracuseStep 9971057 = 7478293) B7478293
theorem B1418611 : Blo 1417528 1418611 := bstep (se 1 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 1418611 = 2127917) B2127917
theorem B1418627 : Blo 1417528 1418627 := bstep (se 1 (by rfl) ⟨1063970, by rfl⟩ : syracuseStep 1418627 = 2127941) B2127941
theorem B4851089 : Blo 1417528 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B2393489 : Blo 1417528 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B1418643 : Blo 1417528 1418643 := bstep (se 1 (by rfl) ⟨1063982, by rfl⟩ : syracuseStep 1418643 = 2127965) B2127965
theorem B1418659 : Blo 1417528 1418659 := bstep (se 1 (by rfl) ⟨1063994, by rfl⟩ : syracuseStep 1418659 = 2127989) B2127989
theorem B1418675 : Blo 1417528 1418675 := bstep (se 1 (by rfl) ⟨1064006, by rfl⟩ : syracuseStep 1418675 = 2128013) B2128013
theorem B1418691 : Blo 1417528 1418691 := bstep (se 1 (by rfl) ⟨1064018, by rfl⟩ : syracuseStep 1418691 = 2128037) B2128037
theorem B1418707 : Blo 1417528 1418707 := bstep (se 1 (by rfl) ⟨1064030, by rfl⟩ : syracuseStep 1418707 = 2128061) B2128061
theorem B1418723 : Blo 1417528 1418723 := bstep (se 1 (by rfl) ⟨1064042, by rfl⟩ : syracuseStep 1418723 = 2128085) B2128085
theorem B26609123 : Blo 1417528 26609123 := bstep (se 1 (by rfl) ⟨19956842, by rfl⟩ : syracuseStep 26609123 = 39913685) B39913685
theorem B1418739 : Blo 1417528 1418739 := bstep (se 1 (by rfl) ⟨1064054, by rfl⟩ : syracuseStep 1418739 = 2128109) B2128109
theorem B1418755 : Blo 1417528 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B2393617 : Blo 1417528 2393617 := bstep (se 2 (by rfl) ⟨897606, by rfl⟩ : syracuseStep 2393617 = 1795213) B1795213
theorem B4040209 : Blo 1417528 4040209 := bstep (se 2 (by rfl) ⟨1515078, by rfl⟩ : syracuseStep 4040209 = 3030157) B3030157
theorem B1795603 : Blo 1417528 1795603 := bstep (se 1 (by rfl) ⟨1346702, by rfl⟩ : syracuseStep 1795603 = 2693405) B2693405
theorem B1418771 : Blo 1417528 1418771 := bstep (se 1 (by rfl) ⟨1064078, by rfl⟩ : syracuseStep 1418771 = 2128157) B2128157
theorem B3589667 : Blo 1417528 3589667 := bstep (se 1 (by rfl) ⟨2692250, by rfl⟩ : syracuseStep 3589667 = 5384501) B5384501
theorem B1418787 : Blo 1417528 1418787 := bstep (se 1 (by rfl) ⟨1064090, by rfl⟩ : syracuseStep 1418787 = 2128181) B2128181
theorem B2393651 : Blo 1417528 2393651 := bstep (se 1 (by rfl) ⟨1795238, by rfl⟩ : syracuseStep 2393651 = 3590477) B3590477
theorem B2426419 : Blo 1417528 2426419 := bstep (se 1 (by rfl) ⟨1819814, by rfl⟩ : syracuseStep 2426419 = 3639629) B3639629
theorem B1418803 : Blo 1417528 1418803 := bstep (se 1 (by rfl) ⟨1064102, by rfl⟩ : syracuseStep 1418803 = 2128205) B2128205
theorem B1418819 : Blo 1417528 1418819 := bstep (se 1 (by rfl) ⟨1064114, by rfl⟩ : syracuseStep 1418819 = 2128229) B2128229
theorem B9217613 : Blo 1417528 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B1418835 : Blo 1417528 1418835 := bstep (se 1 (by rfl) ⟨1064126, by rfl⟩ : syracuseStep 1418835 = 2128253) B2128253
theorem B1418851 : Blo 1417528 1418851 := bstep (se 1 (by rfl) ⟨1064138, by rfl⟩ : syracuseStep 1418851 = 2128277) B2128277
theorem B1795699 : Blo 1417528 1795699 := bstep (se 1 (by rfl) ⟨1346774, by rfl⟩ : syracuseStep 1795699 = 2693549) B2693549
theorem B1418867 : Blo 1417528 1418867 := bstep (se 1 (by rfl) ⟨1064150, by rfl⟩ : syracuseStep 1418867 = 2128301) B2128301
theorem B1418883 : Blo 1417528 1418883 := bstep (se 1 (by rfl) ⟨1064162, by rfl⟩ : syracuseStep 1418883 = 2128325) B2128325
theorem B1418899 : Blo 1417528 1418899 := bstep (se 1 (by rfl) ⟨1064174, by rfl⟩ : syracuseStep 1418899 = 2128349) B2128349
theorem B1418915 : Blo 1417528 1418915 := bstep (se 1 (by rfl) ⟨1064186, by rfl⟩ : syracuseStep 1418915 = 2128373) B2128373
theorem B2393779 : Blo 1417528 2393779 := bstep (se 1 (by rfl) ⟨1795334, by rfl⟩ : syracuseStep 2393779 = 3590669) B3590669
theorem B1418931 : Blo 1417528 1418931 := bstep (se 1 (by rfl) ⟨1064198, by rfl⟩ : syracuseStep 1418931 = 2128397) B2128397
theorem B1640131 : Blo 1417528 1640131 := bstep (se 1 (by rfl) ⟨1230098, by rfl⟩ : syracuseStep 1640131 = 2460197) B2460197
theorem B1418947 : Blo 1417528 1418947 := bstep (se 1 (by rfl) ⟨1064210, by rfl⟩ : syracuseStep 1418947 = 2128421) B2128421
theorem B5457613 : Blo 1417528 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B1418963 : Blo 1417528 1418963 := bstep (se 1 (by rfl) ⟨1064222, by rfl⟩ : syracuseStep 1418963 = 2128445) B2128445
theorem B10643171 : Blo 1417528 10643171 := bstep (se 1 (by rfl) ⟨7982378, by rfl⟩ : syracuseStep 10643171 = 15964757) B15964757
theorem B3589859 : Blo 1417528 3589859 := bstep (se 1 (by rfl) ⟨2692394, by rfl⟩ : syracuseStep 3589859 = 5384789) B5384789
theorem B1418979 : Blo 1417528 1418979 := bstep (se 1 (by rfl) ⟨1064234, by rfl⟩ : syracuseStep 1418979 = 2128469) B2128469
theorem B1418995 : Blo 1417528 1418995 := bstep (se 1 (by rfl) ⟨1064246, by rfl⟩ : syracuseStep 1418995 = 2128493) B2128493
theorem B1419011 : Blo 1417528 1419011 := bstep (se 1 (by rfl) ⟨1064258, by rfl⟩ : syracuseStep 1419011 = 2128517) B2128517
theorem B1419027 : Blo 1417528 1419027 := bstep (se 1 (by rfl) ⟨1064270, by rfl⟩ : syracuseStep 1419027 = 2128541) B2128541
theorem B1419043 : Blo 1417528 1419043 := bstep (se 1 (by rfl) ⟨1064282, by rfl⟩ : syracuseStep 1419043 = 2128565) B2128565
theorem B4785965 : Blo 1417528 4785965 := bstep (se 3 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 4785965 = 1794737) B1794737
theorem B1419059 : Blo 1417528 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B2393921 : Blo 1417528 2393921 := bstep (se 2 (by rfl) ⟨897720, by rfl⟩ : syracuseStep 2393921 = 1795441) B1795441
theorem B1419075 : Blo 1417528 1419075 := bstep (se 1 (by rfl) ⟨1064306, by rfl⟩ : syracuseStep 1419075 = 2128613) B2128613
theorem B1419091 : Blo 1417528 1419091 := bstep (se 1 (by rfl) ⟨1064318, by rfl⟩ : syracuseStep 1419091 = 2128637) B2128637
theorem B4786019 : Blo 1417528 4786019 := bstep (se 1 (by rfl) ⟨3589514, by rfl⟩ : syracuseStep 4786019 = 7179029) B7179029
theorem B1419107 : Blo 1417528 1419107 := bstep (se 1 (by rfl) ⟨1064330, by rfl⟩ : syracuseStep 1419107 = 2128661) B2128661
theorem B1419123 : Blo 1417528 1419123 := bstep (se 1 (by rfl) ⟨1064342, by rfl⟩ : syracuseStep 1419123 = 2128685) B2128685
theorem B2426755 : Blo 1417528 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B1419139 : Blo 1417528 1419139 := bstep (se 1 (by rfl) ⟨1064354, by rfl⟩ : syracuseStep 1419139 = 2128709) B2128709
theorem B1419155 : Blo 1417528 1419155 := bstep (se 1 (by rfl) ⟨1064366, by rfl⟩ : syracuseStep 1419155 = 2128733) B2128733
theorem B6817699 : Blo 1417528 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B1419171 : Blo 1417528 1419171 := bstep (se 1 (by rfl) ⟨1064378, by rfl⟩ : syracuseStep 1419171 = 2128757) B2128757
theorem B1419187 : Blo 1417528 1419187 := bstep (se 1 (by rfl) ⟨1064390, by rfl⟩ : syracuseStep 1419187 = 2128781) B2128781
theorem B2394049 : Blo 1417528 2394049 := bstep (se 2 (by rfl) ⟨897768, by rfl⟩ : syracuseStep 2394049 = 1795537) B1795537
theorem B1419203 : Blo 1417528 1419203 := bstep (se 1 (by rfl) ⟨1064402, by rfl⟩ : syracuseStep 1419203 = 2128805) B2128805
theorem B1419219 : Blo 1417528 1419219 := bstep (se 1 (by rfl) ⟨1064414, by rfl⟩ : syracuseStep 1419219 = 2128829) B2128829
theorem B2394083 : Blo 1417528 2394083 := bstep (se 1 (by rfl) ⟨1795562, by rfl⟩ : syracuseStep 2394083 = 3591125) B3591125
theorem B1419235 : Blo 1417528 1419235 := bstep (se 1 (by rfl) ⟨1064426, by rfl⟩ : syracuseStep 1419235 = 2128853) B2128853
theorem B1419251 : Blo 1417528 1419251 := bstep (se 1 (by rfl) ⟨1064438, by rfl⟩ : syracuseStep 1419251 = 2128877) B2128877
theorem B1419267 : Blo 1417528 1419267 := bstep (se 1 (by rfl) ⟨1064450, by rfl⟩ : syracuseStep 1419267 = 2128901) B2128901
theorem B1419283 : Blo 1417528 1419283 := bstep (se 1 (by rfl) ⟨1064462, by rfl⟩ : syracuseStep 1419283 = 2128925) B2128925
theorem B2304035 : Blo 1417528 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B1419299 : Blo 1417528 1419299 := bstep (se 1 (by rfl) ⟨1064474, by rfl⟩ : syracuseStep 1419299 = 2128949) B2128949
theorem B4851757 : Blo 1417528 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B1419315 : Blo 1417528 1419315 := bstep (se 1 (by rfl) ⟨1064486, by rfl⟩ : syracuseStep 1419315 = 2128973) B2128973
theorem B1419331 : Blo 1417528 1419331 := bstep (se 1 (by rfl) ⟨1064498, by rfl⟩ : syracuseStep 1419331 = 2128997) B2128997
theorem B1419347 : Blo 1417528 1419347 := bstep (se 1 (by rfl) ⟨1064510, by rfl⟩ : syracuseStep 1419347 = 2129021) B2129021
theorem B2271331 : Blo 1417528 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B2394211 : Blo 1417528 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1796195 : Blo 1417528 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1419363 : Blo 1417528 1419363 := bstep (se 1 (by rfl) ⟨1064522, by rfl⟩ : syracuseStep 1419363 = 2129045) B2129045
theorem B4786289 : Blo 1417528 4786289 := bstep (se 2 (by rfl) ⟨1794858, by rfl⟩ : syracuseStep 4786289 = 3589717) B3589717
theorem B1419379 : Blo 1417528 1419379 := bstep (se 1 (by rfl) ⟨1064534, by rfl⟩ : syracuseStep 1419379 = 2129069) B2129069
theorem B1419395 : Blo 1417528 1419395 := bstep (se 1 (by rfl) ⟨1064546, by rfl⟩ : syracuseStep 1419395 = 2129093) B2129093
theorem B7178381 : Blo 1417528 7178381 := bstep (se 3 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 7178381 = 2691893) B2691893
theorem B5384333 : Blo 1417528 5384333 := bstep (se 3 (by rfl) ⟨1009562, by rfl⟩ : syracuseStep 5384333 = 2019125) B2019125
theorem B6146189 : Blo 1417528 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B1419411 : Blo 1417528 1419411 := bstep (se 1 (by rfl) ⟨1064558, by rfl⟩ : syracuseStep 1419411 = 2129117) B2129117
theorem B1419427 : Blo 1417528 1419427 := bstep (se 1 (by rfl) ⟨1064570, by rfl⟩ : syracuseStep 1419427 = 2129141) B2129141
theorem B1419443 : Blo 1417528 1419443 := bstep (se 1 (by rfl) ⟨1064582, by rfl⟩ : syracuseStep 1419443 = 2129165) B2129165
theorem B1419459 : Blo 1417528 1419459 := bstep (se 1 (by rfl) ⟨1064594, by rfl⟩ : syracuseStep 1419459 = 2129189) B2129189
theorem B1419475 : Blo 1417528 1419475 := bstep (se 1 (by rfl) ⟨1064606, by rfl⟩ : syracuseStep 1419475 = 2129213) B2129213
theorem B1419491 : Blo 1417528 1419491 := bstep (se 1 (by rfl) ⟨1064618, by rfl⟩ : syracuseStep 1419491 = 2129237) B2129237
theorem B2394353 : Blo 1417528 2394353 := bstep (se 2 (by rfl) ⟨897882, by rfl⟩ : syracuseStep 2394353 = 1795765) B1795765
theorem B1419507 : Blo 1417528 1419507 := bstep (se 1 (by rfl) ⟨1064630, by rfl⟩ : syracuseStep 1419507 = 2129261) B2129261
theorem B1419523 : Blo 1417528 1419523 := bstep (se 1 (by rfl) ⟨1064642, by rfl⟩ : syracuseStep 1419523 = 2129285) B2129285
theorem B2394481 : Blo 1417528 2394481 := bstep (se 2 (by rfl) ⟨897930, by rfl⟩ : syracuseStep 2394481 = 1795861) B1795861
theorem B2394515 : Blo 1417528 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B2394643 : Blo 1417528 2394643 := bstep (se 1 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 2394643 = 3591965) B3591965
theorem B2427425 : Blo 1417528 2427425 := bstep (se 2 (by rfl) ⟨910284, by rfl⟩ : syracuseStep 2427425 = 1820569) B1820569
theorem B1944145 : Blo 1417528 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B4786829 : Blo 1417528 4786829 := bstep (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) B1795061
theorem B3590801 : Blo 1417528 3590801 := bstep (se 2 (by rfl) ⟨1346550, by rfl⟩ : syracuseStep 3590801 = 2693101) B2693101
theorem B2394785 : Blo 1417528 2394785 := bstep (se 2 (by rfl) ⟨898044, by rfl⟩ : syracuseStep 2394785 = 1796089) B1796089
theorem B4786883 : Blo 1417528 4786883 := bstep (se 1 (by rfl) ⟨3590162, by rfl⟩ : syracuseStep 4786883 = 7180325) B7180325
theorem B3590851 : Blo 1417528 3590851 := bstep (se 1 (by rfl) ⟨2693138, by rfl⟩ : syracuseStep 3590851 = 5386277) B5386277
theorem B7670477 : Blo 1417528 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B4606733 : Blo 1417528 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B4041485 : Blo 1417528 4041485 := bstep (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) B1515557
theorem B2394913 : Blo 1417528 2394913 := bstep (se 2 (by rfl) ⟨898092, by rfl⟩ : syracuseStep 2394913 = 1796185) B1796185
theorem B5114659 : Blo 1417528 5114659 := bstep (se 1 (by rfl) ⟨3835994, by rfl⟩ : syracuseStep 5114659 = 7671989) B7671989
theorem B2394947 : Blo 1417528 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B3590993 : Blo 1417528 3590993 := bstep (se 2 (by rfl) ⟨1346622, by rfl⟩ : syracuseStep 3590993 = 2693245) B2693245
theorem B3189617 : Blo 1417528 3189617 := bstep (se 2 (by rfl) ⟨1196106, by rfl⟩ : syracuseStep 3189617 = 2392213) B2392213
theorem B3189635 : Blo 1417528 3189635 := bstep (se 1 (by rfl) ⟨2392226, by rfl⟩ : syracuseStep 3189635 = 4784453) B4784453
theorem B6818701 : Blo 1417528 6818701 := bstep (se 3 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 6818701 = 2557013) B2557013
theorem B4041667 : Blo 1417528 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B2395075 : Blo 1417528 2395075 := bstep (se 1 (by rfl) ⟨1796306, by rfl⟩ : syracuseStep 2395075 = 3592613) B3592613
theorem B4787153 : Blo 1417528 4787153 := bstep (se 2 (by rfl) ⟨1795182, by rfl⟩ : syracuseStep 4787153 = 3590365) B3590365
theorem B1616851 : Blo 1417528 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B4041713 : Blo 1417528 4041713 := bstep (se 2 (by rfl) ⟨1515642, by rfl⟩ : syracuseStep 4041713 = 3031285) B3031285
theorem B2272259 : Blo 1417528 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B8080397 : Blo 1417528 8080397 := bstep (se 3 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 8080397 = 3030149) B3030149
theorem B2395217 : Blo 1417528 2395217 := bstep (se 2 (by rfl) ⟨898206, by rfl⟩ : syracuseStep 2395217 = 1796413) B1796413
theorem B3189905 : Blo 1417528 3189905 := bstep (se 2 (by rfl) ⟨1196214, by rfl⟩ : syracuseStep 3189905 = 2392429) B2392429
theorem B3189923 : Blo 1417528 3189923 := bstep (se 1 (by rfl) ⟨2392442, by rfl⟩ : syracuseStep 3189923 = 4784885) B4784885
theorem B2395345 : Blo 1417528 2395345 := bstep (se 2 (by rfl) ⟨898254, by rfl⟩ : syracuseStep 2395345 = 1796509) B1796509
theorem B2395379 : Blo 1417528 2395379 := bstep (se 1 (by rfl) ⟨1796534, by rfl⟩ : syracuseStep 2395379 = 3593069) B3593069
theorem B2272529 : Blo 1417528 2272529 := bstep (se 2 (by rfl) ⟨852198, by rfl⟩ : syracuseStep 2272529 = 1704397) B1704397
theorem B4541777 : Blo 1417528 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B3190193 : Blo 1417528 3190193 := bstep (se 2 (by rfl) ⟨1196322, by rfl⟩ : syracuseStep 3190193 = 2392645) B2392645
theorem B3190211 : Blo 1417528 3190211 := bstep (se 1 (by rfl) ⟨2392658, by rfl⟩ : syracuseStep 3190211 = 4785317) B4785317
theorem B6057443 : Blo 1417528 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B4787693 : Blo 1417528 4787693 := bstep (se 3 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 4787693 = 1795385) B1795385
theorem B3452419 : Blo 1417528 3452419 := bstep (se 1 (by rfl) ⟨2589314, by rfl⟩ : syracuseStep 3452419 = 5178629) B5178629
theorem B15330829 : Blo 1417528 15330829 := bstep (se 3 (by rfl) ⟨2874530, by rfl⟩ : syracuseStep 15330829 = 5749061) B5749061
theorem B10776077 : Blo 1417528 10776077 := bstep (se 3 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 10776077 = 4041029) B4041029
theorem B4787747 : Blo 1417528 4787747 := bstep (se 1 (by rfl) ⟨3590810, by rfl⟩ : syracuseStep 4787747 = 7181621) B7181621
theorem B2272817 : Blo 1417528 2272817 := bstep (se 2 (by rfl) ⟨852306, by rfl⟩ : syracuseStep 2272817 = 1704613) B1704613
theorem B9088625 : Blo 1417528 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B2019011 : Blo 1417528 2019011 := bstep (se 1 (by rfl) ⟨1514258, by rfl⟩ : syracuseStep 2019011 = 3028517) B3028517
theorem B3190481 : Blo 1417528 3190481 := bstep (se 2 (by rfl) ⟨1196430, by rfl⟩ : syracuseStep 3190481 = 2392861) B2392861
theorem B3190499 : Blo 1417528 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B3690211 : Blo 1417528 3690211 := bstep (se 1 (by rfl) ⟨2767658, by rfl⟩ : syracuseStep 3690211 = 5535317) B5535317
theorem B2158307 : Blo 1417528 2158307 := bstep (se 1 (by rfl) ⟨1618730, by rfl⟩ : syracuseStep 2158307 = 3237461) B3237461
theorem B4312867 : Blo 1417528 4312867 := bstep (se 1 (by rfl) ⟨3234650, by rfl⟩ : syracuseStep 4312867 = 6469301) B6469301
theorem B4788017 : Blo 1417528 4788017 := bstep (se 2 (by rfl) ⟨1795506, by rfl⟩ : syracuseStep 4788017 = 3591013) B3591013
theorem B3591985 : Blo 1417528 3591985 := bstep (se 2 (by rfl) ⟨1346994, by rfl⟩ : syracuseStep 3591985 = 2693989) B2693989
theorem B8081329 : Blo 1417528 8081329 := bstep (se 2 (by rfl) ⟨3030498, by rfl⟩ : syracuseStep 8081329 = 6060997) B6060997
theorem B2273233 : Blo 1417528 2273233 := bstep (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) B1704925
theorem B3190769 : Blo 1417528 3190769 := bstep (se 2 (by rfl) ⟨1196538, by rfl⟩ : syracuseStep 3190769 = 2393077) B2393077
theorem B3190787 : Blo 1417528 3190787 := bstep (se 1 (by rfl) ⟨2393090, by rfl⟩ : syracuseStep 3190787 = 4786181) B4786181
theorem B6230029 : Blo 1417528 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B54521909 : Blo 1417528 54521909 := bstep (se 5 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 54521909 = 5111429) B5111429
theorem B3592259 : Blo 1417528 3592259 := bstep (se 1 (by rfl) ⟨2694194, by rfl⟩ : syracuseStep 3592259 = 5388389) B5388389
theorem B2592881 : Blo 1417528 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B5386445 : Blo 1417528 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B1437923 : Blo 1417528 1437923 := bstep (se 1 (by rfl) ⟨1078442, by rfl⟩ : syracuseStep 1437923 = 2156885) B2156885
theorem B1618147 : Blo 1417528 1618147 := bstep (se 1 (by rfl) ⟨1213610, by rfl⟩ : syracuseStep 1618147 = 2427221) B2427221
theorem B3592451 : Blo 1417528 3592451 := bstep (se 1 (by rfl) ⟨2694338, by rfl⟩ : syracuseStep 3592451 = 5388677) B5388677
theorem B9089293 : Blo 1417528 9089293 := bstep (se 3 (by rfl) ⟨1704242, by rfl⟩ : syracuseStep 9089293 = 3408485) B3408485
theorem B3191057 : Blo 1417528 3191057 := bstep (se 2 (by rfl) ⟨1196646, by rfl⟩ : syracuseStep 3191057 = 2393293) B2393293
theorem B3191075 : Blo 1417528 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B2691377 : Blo 1417528 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B6820145 : Blo 1417528 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B1577267 : Blo 1417528 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B2019649 : Blo 1417528 2019649 := bstep (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) B1514737
theorem B4788557 : Blo 1417528 4788557 := bstep (se 3 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 4788557 = 1795709) B1795709
theorem B4788611 : Blo 1417528 4788611 := bstep (se 1 (by rfl) ⟨3591458, by rfl⟩ : syracuseStep 4788611 = 7182917) B7182917
theorem B2019763 : Blo 1417528 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B27275717 : Blo 1417528 27275717 := bstep (se 4 (by rfl) ⟨2557098, by rfl⟩ : syracuseStep 27275717 = 5114197) B5114197
theorem B2126321 : Blo 1417528 2126321 := bstep (se 2 (by rfl) ⟨797370, by rfl⟩ : syracuseStep 2126321 = 1594741) B1594741
theorem B2126339 : Blo 1417528 2126339 := bstep (se 1 (by rfl) ⟨1594754, by rfl⟩ : syracuseStep 2126339 = 3189509) B3189509
theorem B2126369 : Blo 1417528 2126369 := bstep (se 2 (by rfl) ⟨797388, by rfl⟩ : syracuseStep 2126369 = 1594777) B1594777
theorem B3191345 : Blo 1417528 3191345 := bstep (se 2 (by rfl) ⟨1196754, by rfl⟩ : syracuseStep 3191345 = 2393509) B2393509
theorem B2126387 : Blo 1417528 2126387 := bstep (se 1 (by rfl) ⟨1594790, by rfl⟩ : syracuseStep 2126387 = 3189581) B3189581
theorem B3191363 : Blo 1417528 3191363 := bstep (se 1 (by rfl) ⟨2393522, by rfl⟩ : syracuseStep 3191363 = 4787045) B4787045
theorem B2126417 : Blo 1417528 2126417 := bstep (se 2 (by rfl) ⟨797406, by rfl⟩ : syracuseStep 2126417 = 1594813) B1594813
theorem B2126435 : Blo 1417528 2126435 := bstep (se 1 (by rfl) ⟨1594826, by rfl⟩ : syracuseStep 2126435 = 3189653) B3189653
theorem B13628017 : Blo 1417528 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B2126465 : Blo 1417528 2126465 := bstep (se 2 (by rfl) ⟨797424, by rfl⟩ : syracuseStep 2126465 = 1594849) B1594849
theorem B4788881 : Blo 1417528 4788881 := bstep (se 2 (by rfl) ⟨1795830, by rfl⟩ : syracuseStep 4788881 = 3591661) B3591661
theorem B2126483 : Blo 1417528 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B7664291 : Blo 1417528 7664291 := bstep (se 1 (by rfl) ⟨5748218, by rfl⟩ : syracuseStep 7664291 = 11496437) B11496437
theorem B2126513 : Blo 1417528 2126513 := bstep (se 2 (by rfl) ⟨797442, by rfl⟩ : syracuseStep 2126513 = 1594885) B1594885
theorem B2126531 : Blo 1417528 2126531 := bstep (se 1 (by rfl) ⟨1594898, by rfl⟩ : syracuseStep 2126531 = 3189797) B3189797
theorem B2126561 : Blo 1417528 2126561 := bstep (se 2 (by rfl) ⟨797460, by rfl⟩ : syracuseStep 2126561 = 1594921) B1594921
theorem B2126579 : Blo 1417528 2126579 := bstep (se 1 (by rfl) ⟨1594934, by rfl⟩ : syracuseStep 2126579 = 3189869) B3189869
theorem B2126609 : Blo 1417528 2126609 := bstep (se 2 (by rfl) ⟨797478, by rfl⟩ : syracuseStep 2126609 = 1594957) B1594957
theorem B2126627 : Blo 1417528 2126627 := bstep (se 1 (by rfl) ⟨1594970, by rfl⟩ : syracuseStep 2126627 = 3189941) B3189941
theorem B2126657 : Blo 1417528 2126657 := bstep (se 2 (by rfl) ⟨797496, by rfl⟩ : syracuseStep 2126657 = 1594993) B1594993
theorem B3191633 : Blo 1417528 3191633 := bstep (se 2 (by rfl) ⟨1196862, by rfl⟩ : syracuseStep 3191633 = 2393725) B2393725
theorem B2126675 : Blo 1417528 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B3191651 : Blo 1417528 3191651 := bstep (se 1 (by rfl) ⟨2393738, by rfl⟩ : syracuseStep 3191651 = 4787477) B4787477
theorem B2126705 : Blo 1417528 2126705 := bstep (se 2 (by rfl) ⟨797514, by rfl⟩ : syracuseStep 2126705 = 1595029) B1595029
theorem B2126723 : Blo 1417528 2126723 := bstep (se 1 (by rfl) ⟨1595042, by rfl⟩ : syracuseStep 2126723 = 3190085) B3190085
theorem B2126753 : Blo 1417528 2126753 := bstep (se 2 (by rfl) ⟨797532, by rfl⟩ : syracuseStep 2126753 = 1595065) B1595065
theorem B2126771 : Blo 1417528 2126771 := bstep (se 1 (by rfl) ⟨1595078, by rfl⟩ : syracuseStep 2126771 = 3190157) B3190157
theorem B2126801 : Blo 1417528 2126801 := bstep (se 2 (by rfl) ⟨797550, by rfl⟩ : syracuseStep 2126801 = 1595101) B1595101
theorem B2126819 : Blo 1417528 2126819 := bstep (se 1 (by rfl) ⟨1595114, by rfl⟩ : syracuseStep 2126819 = 3190229) B3190229
theorem B7181297 : Blo 1417528 7181297 := bstep (se 2 (by rfl) ⟨2692986, by rfl⟩ : syracuseStep 7181297 = 5385973) B5385973
theorem B5387249 : Blo 1417528 5387249 := bstep (se 2 (by rfl) ⟨2020218, by rfl⟩ : syracuseStep 5387249 = 4040437) B4040437
theorem B2126849 : Blo 1417528 2126849 := bstep (se 2 (by rfl) ⟨797568, by rfl⟩ : syracuseStep 2126849 = 1595137) B1595137
theorem B12948493 : Blo 1417528 12948493 := bstep (se 3 (by rfl) ⟨2427842, by rfl⟩ : syracuseStep 12948493 = 4855685) B4855685
theorem B2126867 : Blo 1417528 2126867 := bstep (se 1 (by rfl) ⟨1595150, by rfl⟩ : syracuseStep 2126867 = 3190301) B3190301
theorem B2126897 : Blo 1417528 2126897 := bstep (se 2 (by rfl) ⟨797586, by rfl⟩ : syracuseStep 2126897 = 1595173) B1595173
theorem B2126915 : Blo 1417528 2126915 := bstep (se 1 (by rfl) ⟨1595186, by rfl⟩ : syracuseStep 2126915 = 3190373) B3190373
theorem B2126945 : Blo 1417528 2126945 := bstep (se 2 (by rfl) ⟨797604, by rfl⟩ : syracuseStep 2126945 = 1595209) B1595209
theorem B3191921 : Blo 1417528 3191921 := bstep (se 2 (by rfl) ⟨1196970, by rfl⟩ : syracuseStep 3191921 = 2393941) B2393941
theorem B2126963 : Blo 1417528 2126963 := bstep (se 1 (by rfl) ⟨1595222, by rfl⟩ : syracuseStep 2126963 = 3190445) B3190445
theorem B3028099 : Blo 1417528 3028099 := bstep (se 1 (by rfl) ⟨2271074, by rfl⟩ : syracuseStep 3028099 = 4542149) B4542149
theorem B3191939 : Blo 1417528 3191939 := bstep (se 1 (by rfl) ⟨2393954, by rfl⟩ : syracuseStep 3191939 = 4787909) B4787909
theorem B38810765 : Blo 1417528 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B2126993 : Blo 1417528 2126993 := bstep (se 2 (by rfl) ⟨797622, by rfl⟩ : syracuseStep 2126993 = 1595245) B1595245
theorem B2127011 : Blo 1417528 2127011 := bstep (se 1 (by rfl) ⟨1595258, by rfl⟩ : syracuseStep 2127011 = 3190517) B3190517
theorem B4789421 : Blo 1417528 4789421 := bstep (se 3 (by rfl) ⟨898016, by rfl⟩ : syracuseStep 4789421 = 1796033) B1796033
theorem B2692273 : Blo 1417528 2692273 := bstep (se 2 (by rfl) ⟨1009602, by rfl⟩ : syracuseStep 2692273 = 2019205) B2019205
theorem B2127041 : Blo 1417528 2127041 := bstep (se 2 (by rfl) ⟨797640, by rfl⟩ : syracuseStep 2127041 = 1595281) B1595281
theorem B2127059 : Blo 1417528 2127059 := bstep (se 1 (by rfl) ⟨1595294, by rfl⟩ : syracuseStep 2127059 = 3190589) B3190589
theorem B4789475 : Blo 1417528 4789475 := bstep (se 1 (by rfl) ⟨3592106, by rfl⟩ : syracuseStep 4789475 = 7184213) B7184213
theorem B2127089 : Blo 1417528 2127089 := bstep (se 2 (by rfl) ⟨797658, by rfl⟩ : syracuseStep 2127089 = 1595317) B1595317
theorem B2127107 : Blo 1417528 2127107 := bstep (se 1 (by rfl) ⟨1595330, by rfl⟩ : syracuseStep 2127107 = 3190661) B3190661
theorem B51754261 : Blo 1417528 51754261 := bstep (se 6 (by rfl) ⟨1212990, by rfl⟩ : syracuseStep 51754261 = 2425981) B2425981
theorem B2127137 : Blo 1417528 2127137 := bstep (se 2 (by rfl) ⟨797676, by rfl⟩ : syracuseStep 2127137 = 1595353) B1595353
theorem B4543789 : Blo 1417528 4543789 := bstep (se 3 (by rfl) ⟨851960, by rfl⟩ : syracuseStep 4543789 = 1703921) B1703921
theorem B2127155 : Blo 1417528 2127155 := bstep (se 1 (by rfl) ⟨1595366, by rfl⟩ : syracuseStep 2127155 = 3190733) B3190733
theorem B8074565 : Blo 1417528 8074565 := bstep (se 4 (by rfl) ⟨756990, by rfl⟩ : syracuseStep 8074565 = 1513981) B1513981
theorem B2127185 : Blo 1417528 2127185 := bstep (se 2 (by rfl) ⟨797694, by rfl⟩ : syracuseStep 2127185 = 1595389) B1595389
theorem B2692433 : Blo 1417528 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B1594723 : Blo 1417528 1594723 := bstep (se 1 (by rfl) ⟨1196042, by rfl⟩ : syracuseStep 1594723 = 2392085) B2392085
theorem B10220899 : Blo 1417528 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B2127203 : Blo 1417528 2127203 := bstep (se 1 (by rfl) ⟨1595402, by rfl⟩ : syracuseStep 2127203 = 3190805) B3190805
theorem B8082787 : Blo 1417528 8082787 := bstep (se 1 (by rfl) ⟨6062090, by rfl⟩ : syracuseStep 8082787 = 12124181) B12124181
theorem B2127233 : Blo 1417528 2127233 := bstep (se 2 (by rfl) ⟨797712, by rfl⟩ : syracuseStep 2127233 = 1595425) B1595425
theorem B3192209 : Blo 1417528 3192209 := bstep (se 2 (by rfl) ⟨1197078, by rfl⟩ : syracuseStep 3192209 = 2394157) B2394157
theorem B2127251 : Blo 1417528 2127251 := bstep (se 1 (by rfl) ⟨1595438, by rfl⟩ : syracuseStep 2127251 = 3190877) B3190877
theorem B3192227 : Blo 1417528 3192227 := bstep (se 1 (by rfl) ⟨2394170, by rfl⟩ : syracuseStep 3192227 = 4788341) B4788341
theorem B2127281 : Blo 1417528 2127281 := bstep (se 2 (by rfl) ⟨797730, by rfl⟩ : syracuseStep 2127281 = 1595461) B1595461
theorem B2127299 : Blo 1417528 2127299 := bstep (se 1 (by rfl) ⟨1595474, by rfl⟩ : syracuseStep 2127299 = 3190949) B3190949
theorem B2127329 : Blo 1417528 2127329 := bstep (se 2 (by rfl) ⟨797748, by rfl⟩ : syracuseStep 2127329 = 1595497) B1595497
theorem B4789745 : Blo 1417528 4789745 := bstep (se 2 (by rfl) ⟨1796154, by rfl⟩ : syracuseStep 4789745 = 3592309) B3592309
theorem B1594867 : Blo 1417528 1594867 := bstep (se 1 (by rfl) ⟨1196150, by rfl⟩ : syracuseStep 1594867 = 2392301) B2392301
theorem B2127347 : Blo 1417528 2127347 := bstep (se 1 (by rfl) ⟨1595510, by rfl⟩ : syracuseStep 2127347 = 3191021) B3191021
theorem B2127377 : Blo 1417528 2127377 := bstep (se 2 (by rfl) ⟨797766, by rfl⟩ : syracuseStep 2127377 = 1595533) B1595533
theorem B2127395 : Blo 1417528 2127395 := bstep (se 1 (by rfl) ⟨1595546, by rfl⟩ : syracuseStep 2127395 = 3191093) B3191093
theorem B2127425 : Blo 1417528 2127425 := bstep (se 2 (by rfl) ⟨797784, by rfl⟩ : syracuseStep 2127425 = 1595569) B1595569
theorem B2127443 : Blo 1417528 2127443 := bstep (se 1 (by rfl) ⟨1595582, by rfl⟩ : syracuseStep 2127443 = 3191165) B3191165
theorem B2127473 : Blo 1417528 2127473 := bstep (se 2 (by rfl) ⟨797802, by rfl⟩ : syracuseStep 2127473 = 1595605) B1595605
theorem B1595011 : Blo 1417528 1595011 := bstep (se 1 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 1595011 = 2392517) B2392517
theorem B2127491 : Blo 1417528 2127491 := bstep (se 1 (by rfl) ⟨1595618, by rfl⟩ : syracuseStep 2127491 = 3191237) B3191237
theorem B5387917 : Blo 1417528 5387917 := bstep (se 3 (by rfl) ⟨1010234, by rfl⟩ : syracuseStep 5387917 = 2020469) B2020469
theorem B2127521 : Blo 1417528 2127521 := bstep (se 2 (by rfl) ⟨797820, by rfl⟩ : syracuseStep 2127521 = 1595641) B1595641
theorem B3192497 : Blo 1417528 3192497 := bstep (se 2 (by rfl) ⟨1197186, by rfl⟩ : syracuseStep 3192497 = 2394373) B2394373
theorem B2127539 : Blo 1417528 2127539 := bstep (se 1 (by rfl) ⟨1595654, by rfl⟩ : syracuseStep 2127539 = 3191309) B3191309
theorem B3192515 : Blo 1417528 3192515 := bstep (se 1 (by rfl) ⟨2394386, by rfl⟩ : syracuseStep 3192515 = 4788773) B4788773
theorem B2127569 : Blo 1417528 2127569 := bstep (se 2 (by rfl) ⟨797838, by rfl⟩ : syracuseStep 2127569 = 1595677) B1595677
theorem B2127587 : Blo 1417528 2127587 := bstep (se 1 (by rfl) ⟨1595690, by rfl⟩ : syracuseStep 2127587 = 3191381) B3191381
theorem B2692835 : Blo 1417528 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B4544237 : Blo 1417528 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B2021107 : Blo 1417528 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B2127617 : Blo 1417528 2127617 := bstep (se 2 (by rfl) ⟨797856, by rfl⟩ : syracuseStep 2127617 = 1595713) B1595713
theorem B1595155 : Blo 1417528 1595155 := bstep (se 1 (by rfl) ⟨1196366, by rfl⟩ : syracuseStep 1595155 = 2392733) B2392733
theorem B2127635 : Blo 1417528 2127635 := bstep (se 1 (by rfl) ⟨1595726, by rfl⟩ : syracuseStep 2127635 = 3191453) B3191453
theorem B2127665 : Blo 1417528 2127665 := bstep (se 2 (by rfl) ⟨797874, by rfl⟩ : syracuseStep 2127665 = 1595749) B1595749
theorem B2127683 : Blo 1417528 2127683 := bstep (se 1 (by rfl) ⟨1595762, by rfl⟩ : syracuseStep 2127683 = 3191525) B3191525
theorem B10770245 : Blo 1417528 10770245 := bstep (se 4 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 10770245 = 2019421) B2019421
theorem B4855619 : Blo 1417528 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B2127713 : Blo 1417528 2127713 := bstep (se 2 (by rfl) ⟨797892, by rfl⟩ : syracuseStep 2127713 = 1595785) B1595785
theorem B13817699 : Blo 1417528 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B8083313 : Blo 1417528 8083313 := bstep (se 2 (by rfl) ⟨3031242, by rfl⟩ : syracuseStep 8083313 = 6062485) B6062485
theorem B2127731 : Blo 1417528 2127731 := bstep (se 1 (by rfl) ⟨1595798, by rfl⟩ : syracuseStep 2127731 = 3191597) B3191597
theorem B2127761 : Blo 1417528 2127761 := bstep (se 2 (by rfl) ⟨797910, by rfl⟩ : syracuseStep 2127761 = 1595821) B1595821
theorem B1595299 : Blo 1417528 1595299 := bstep (se 1 (by rfl) ⟨1196474, by rfl⟩ : syracuseStep 1595299 = 2392949) B2392949
theorem B2127779 : Blo 1417528 2127779 := bstep (se 1 (by rfl) ⟨1595834, by rfl⟩ : syracuseStep 2127779 = 3191669) B3191669
theorem B2127809 : Blo 1417528 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B3192785 : Blo 1417528 3192785 := bstep (se 2 (by rfl) ⟨1197294, by rfl⟩ : syracuseStep 3192785 = 2394589) B2394589
theorem B2127827 : Blo 1417528 2127827 := bstep (se 1 (by rfl) ⟨1595870, by rfl⟩ : syracuseStep 2127827 = 3191741) B3191741
theorem B3831779 : Blo 1417528 3831779 := bstep (se 1 (by rfl) ⟨2873834, by rfl⟩ : syracuseStep 3831779 = 5747669) B5747669
theorem B3192803 : Blo 1417528 3192803 := bstep (se 1 (by rfl) ⟨2394602, by rfl⟩ : syracuseStep 3192803 = 4789205) B4789205
theorem B2127857 : Blo 1417528 2127857 := bstep (se 2 (by rfl) ⟨797946, by rfl⟩ : syracuseStep 2127857 = 1595893) B1595893
theorem B2127875 : Blo 1417528 2127875 := bstep (se 1 (by rfl) ⟨1595906, by rfl⟩ : syracuseStep 2127875 = 3191813) B3191813
theorem B4790285 : Blo 1417528 4790285 := bstep (se 3 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 4790285 = 1796357) B1796357
theorem B2127905 : Blo 1417528 2127905 := bstep (se 2 (by rfl) ⟨797964, by rfl⟩ : syracuseStep 2127905 = 1595929) B1595929
theorem B7280675 : Blo 1417528 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B1595443 : Blo 1417528 1595443 := bstep (se 1 (by rfl) ⟨1196582, by rfl⟩ : syracuseStep 1595443 = 2393165) B2393165
theorem B2127923 : Blo 1417528 2127923 := bstep (se 1 (by rfl) ⟨1595942, by rfl⟩ : syracuseStep 2127923 = 3191885) B3191885
theorem B4790339 : Blo 1417528 4790339 := bstep (se 1 (by rfl) ⟨3592754, by rfl⟩ : syracuseStep 4790339 = 7185509) B7185509
theorem B6060109 : Blo 1417528 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B2127953 : Blo 1417528 2127953 := bstep (se 2 (by rfl) ⟨797982, by rfl⟩ : syracuseStep 2127953 = 1595965) B1595965
theorem B2127971 : Blo 1417528 2127971 := bstep (se 1 (by rfl) ⟨1595978, by rfl⟩ : syracuseStep 2127971 = 3191957) B3191957
theorem B2128001 : Blo 1417528 2128001 := bstep (se 2 (by rfl) ⟨798000, by rfl⟩ : syracuseStep 2128001 = 1596001) B1596001
theorem B2046097 : Blo 1417528 2046097 := bstep (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) B1534573
theorem B2128019 : Blo 1417528 2128019 := bstep (se 1 (by rfl) ⟨1596014, by rfl⟩ : syracuseStep 2128019 = 3192029) B3192029
theorem B2128049 : Blo 1417528 2128049 := bstep (se 2 (by rfl) ⟨798018, by rfl⟩ : syracuseStep 2128049 = 1596037) B1596037
theorem B1595587 : Blo 1417528 1595587 := bstep (se 1 (by rfl) ⟨1196690, by rfl⟩ : syracuseStep 1595587 = 2393381) B2393381
theorem B2128067 : Blo 1417528 2128067 := bstep (se 1 (by rfl) ⟨1596050, by rfl⟩ : syracuseStep 2128067 = 3192101) B3192101
theorem B2128097 : Blo 1417528 2128097 := bstep (se 2 (by rfl) ⟨798036, by rfl⟩ : syracuseStep 2128097 = 1596073) B1596073
theorem B3193073 : Blo 1417528 3193073 := bstep (se 2 (by rfl) ⟨1197402, by rfl⟩ : syracuseStep 3193073 = 2394805) B2394805
theorem B2128115 : Blo 1417528 2128115 := bstep (se 1 (by rfl) ⟨1596086, by rfl⟩ : syracuseStep 2128115 = 3192173) B3192173
theorem B3193091 : Blo 1417528 3193091 := bstep (se 1 (by rfl) ⟨2394818, by rfl⟩ : syracuseStep 3193091 = 4789637) B4789637
theorem B2128145 : Blo 1417528 2128145 := bstep (se 2 (by rfl) ⟨798054, by rfl⟩ : syracuseStep 2128145 = 1596109) B1596109
theorem B2128163 : Blo 1417528 2128163 := bstep (se 1 (by rfl) ⟨1596122, by rfl⟩ : syracuseStep 2128163 = 3192245) B3192245
theorem B2128193 : Blo 1417528 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B3029329 : Blo 1417528 3029329 := bstep (se 2 (by rfl) ⟨1135998, by rfl⟩ : syracuseStep 3029329 = 2271997) B2271997
theorem B4790609 : Blo 1417528 4790609 := bstep (se 2 (by rfl) ⟨1796478, by rfl⟩ : syracuseStep 4790609 = 3592957) B3592957
theorem B1595731 : Blo 1417528 1595731 := bstep (se 1 (by rfl) ⟨1196798, by rfl⟩ : syracuseStep 1595731 = 2393597) B2393597
theorem B2128211 : Blo 1417528 2128211 := bstep (se 1 (by rfl) ⟨1596158, by rfl⟩ : syracuseStep 2128211 = 3192317) B3192317
theorem B2128241 : Blo 1417528 2128241 := bstep (se 2 (by rfl) ⟨798090, by rfl⟩ : syracuseStep 2128241 = 1596181) B1596181
theorem B10778993 : Blo 1417528 10778993 := bstep (se 2 (by rfl) ⟨4042122, by rfl⟩ : syracuseStep 10778993 = 8084245) B8084245
theorem B2128259 : Blo 1417528 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B2128289 : Blo 1417528 2128289 := bstep (se 2 (by rfl) ⟨798108, by rfl⟩ : syracuseStep 2128289 = 1596217) B1596217
theorem B7182755 : Blo 1417528 7182755 := bstep (se 1 (by rfl) ⟨5387066, by rfl⟩ : syracuseStep 7182755 = 10774133) B10774133
theorem B5388707 : Blo 1417528 5388707 := bstep (se 1 (by rfl) ⟨4041530, by rfl⟩ : syracuseStep 5388707 = 8083061) B8083061
theorem B8632739 : Blo 1417528 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B2128307 : Blo 1417528 2128307 := bstep (se 1 (by rfl) ⟨1596230, by rfl⟩ : syracuseStep 2128307 = 3192461) B3192461
theorem B2128337 : Blo 1417528 2128337 := bstep (se 2 (by rfl) ⟨798126, by rfl⟩ : syracuseStep 2128337 = 1596253) B1596253
theorem B1595875 : Blo 1417528 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B2128355 : Blo 1417528 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B4315619 : Blo 1417528 4315619 := bstep (se 1 (by rfl) ⟨3236714, by rfl⟩ : syracuseStep 4315619 = 6473429) B6473429
theorem B2128385 : Blo 1417528 2128385 := bstep (se 2 (by rfl) ⟨798144, by rfl⟩ : syracuseStep 2128385 = 1596289) B1596289
theorem B3193361 : Blo 1417528 3193361 := bstep (se 2 (by rfl) ⟨1197510, by rfl⟩ : syracuseStep 3193361 = 2395021) B2395021
theorem B2128403 : Blo 1417528 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B3193379 : Blo 1417528 3193379 := bstep (se 1 (by rfl) ⟨2395034, by rfl⟩ : syracuseStep 3193379 = 4790069) B4790069
theorem B2128433 : Blo 1417528 2128433 := bstep (se 2 (by rfl) ⟨798162, by rfl⟩ : syracuseStep 2128433 = 1596325) B1596325
theorem B2128451 : Blo 1417528 2128451 := bstep (se 1 (by rfl) ⟨1596338, by rfl⟩ : syracuseStep 2128451 = 3192677) B3192677
theorem B2128481 : Blo 1417528 2128481 := bstep (se 2 (by rfl) ⟨798180, by rfl⟩ : syracuseStep 2128481 = 1596361) B1596361
theorem B2693731 : Blo 1417528 2693731 := bstep (se 1 (by rfl) ⟨2020298, by rfl⟩ : syracuseStep 2693731 = 4040597) B4040597
theorem B1596019 : Blo 1417528 1596019 := bstep (se 1 (by rfl) ⟨1197014, by rfl⟩ : syracuseStep 1596019 = 2394029) B2394029
theorem B2128499 : Blo 1417528 2128499 := bstep (se 1 (by rfl) ⟨1596374, by rfl⟩ : syracuseStep 2128499 = 3192749) B3192749
theorem B2128529 : Blo 1417528 2128529 := bstep (se 2 (by rfl) ⟨798198, by rfl⟩ : syracuseStep 2128529 = 1596397) B1596397
theorem B2128547 : Blo 1417528 2128547 := bstep (se 1 (by rfl) ⟨1596410, by rfl⟩ : syracuseStep 2128547 = 3192821) B3192821
theorem B4037293 : Blo 1417528 4037293 := bstep (se 3 (by rfl) ⟨756992, by rfl⟩ : syracuseStep 4037293 = 1513985) B1513985
theorem B5986993 : Blo 1417528 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B2128577 : Blo 1417528 2128577 := bstep (se 2 (by rfl) ⟨798216, by rfl⟩ : syracuseStep 2128577 = 1596433) B1596433
theorem B2128595 : Blo 1417528 2128595 := bstep (se 1 (by rfl) ⟨1596446, by rfl⟩ : syracuseStep 2128595 = 3192893) B3192893
theorem B2128625 : Blo 1417528 2128625 := bstep (se 2 (by rfl) ⟨798234, by rfl⟩ : syracuseStep 2128625 = 1596469) B1596469
theorem B1596163 : Blo 1417528 1596163 := bstep (se 1 (by rfl) ⟨1197122, by rfl⟩ : syracuseStep 1596163 = 2394245) B2394245
theorem B2693891 : Blo 1417528 2693891 := bstep (se 1 (by rfl) ⟨2020418, by rfl⟩ : syracuseStep 2693891 = 4040837) B4040837
theorem B2128643 : Blo 1417528 2128643 := bstep (se 1 (by rfl) ⟨1596482, by rfl⟩ : syracuseStep 2128643 = 3192965) B3192965
theorem B2128673 : Blo 1417528 2128673 := bstep (se 2 (by rfl) ⟨798252, by rfl⟩ : syracuseStep 2128673 = 1596505) B1596505
theorem B3193649 : Blo 1417528 3193649 := bstep (se 2 (by rfl) ⟨1197618, by rfl⟩ : syracuseStep 3193649 = 2395237) B2395237
theorem B2128691 : Blo 1417528 2128691 := bstep (se 1 (by rfl) ⟨1596518, by rfl⟩ : syracuseStep 2128691 = 3193037) B3193037
theorem B3193667 : Blo 1417528 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B13998917 : Blo 1417528 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B2128721 : Blo 1417528 2128721 := bstep (se 2 (by rfl) ⟨798270, by rfl⟩ : syracuseStep 2128721 = 1596541) B1596541
theorem B1514323 : Blo 1417528 1514323 := bstep (se 1 (by rfl) ⟨1135742, by rfl⟩ : syracuseStep 1514323 = 2271485) B2271485
theorem B2128739 : Blo 1417528 2128739 := bstep (se 1 (by rfl) ⟨1596554, by rfl⟩ : syracuseStep 2128739 = 3193109) B3193109
theorem B18414449 : Blo 1417528 18414449 := bstep (se 2 (by rfl) ⟨6905418, by rfl⟩ : syracuseStep 18414449 = 13810837) B13810837
theorem B2128769 : Blo 1417528 2128769 := bstep (se 2 (by rfl) ⟨798288, by rfl⟩ : syracuseStep 2128769 = 1596577) B1596577
theorem B4037521 : Blo 1417528 4037521 := bstep (se 2 (by rfl) ⟨1514070, by rfl⟩ : syracuseStep 4037521 = 3028141) B3028141
theorem B1596307 : Blo 1417528 1596307 := bstep (se 1 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 1596307 = 2394461) B2394461
theorem B2128787 : Blo 1417528 2128787 := bstep (se 1 (by rfl) ⟨1596590, by rfl⟩ : syracuseStep 2128787 = 3193181) B3193181
theorem B2128817 : Blo 1417528 2128817 := bstep (se 2 (by rfl) ⟨798306, by rfl⟩ : syracuseStep 2128817 = 1596613) B1596613
theorem B2128835 : Blo 1417528 2128835 := bstep (se 1 (by rfl) ⟨1596626, by rfl⟩ : syracuseStep 2128835 = 3193253) B3193253
theorem B2128865 : Blo 1417528 2128865 := bstep (se 2 (by rfl) ⟨798324, by rfl⟩ : syracuseStep 2128865 = 1596649) B1596649
theorem B3029987 : Blo 1417528 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B5110769 : Blo 1417528 5110769 := bstep (se 2 (by rfl) ⟨1916538, by rfl⟩ : syracuseStep 5110769 = 3833077) B3833077
theorem B2128883 : Blo 1417528 2128883 := bstep (se 1 (by rfl) ⟨1596662, by rfl⟩ : syracuseStep 2128883 = 3193325) B3193325
theorem B2128913 : Blo 1417528 2128913 := bstep (se 2 (by rfl) ⟨798342, by rfl⟩ : syracuseStep 2128913 = 1596685) B1596685
theorem B1596451 : Blo 1417528 1596451 := bstep (se 1 (by rfl) ⟨1197338, by rfl⟩ : syracuseStep 1596451 = 2394677) B2394677
theorem B2128931 : Blo 1417528 2128931 := bstep (se 1 (by rfl) ⟨1596698, by rfl⟩ : syracuseStep 2128931 = 3193397) B3193397
theorem B4037681 : Blo 1417528 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B5389361 : Blo 1417528 5389361 := bstep (se 2 (by rfl) ⟨2021010, by rfl⟩ : syracuseStep 5389361 = 4042021) B4042021
theorem B2128961 : Blo 1417528 2128961 := bstep (se 2 (by rfl) ⟨798360, by rfl⟩ : syracuseStep 2128961 = 1596721) B1596721
theorem B3193937 : Blo 1417528 3193937 := bstep (se 2 (by rfl) ⟨1197726, by rfl⟩ : syracuseStep 3193937 = 2395453) B2395453
theorem B2128979 : Blo 1417528 2128979 := bstep (se 1 (by rfl) ⟨1596734, by rfl⟩ : syracuseStep 2128979 = 3193469) B3193469
theorem B2874467 : Blo 1417528 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B6061169 : Blo 1417528 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B2129009 : Blo 1417528 2129009 := bstep (se 2 (by rfl) ⟨798378, by rfl⟩ : syracuseStep 2129009 = 1596757) B1596757
theorem B2129027 : Blo 1417528 2129027 := bstep (se 1 (by rfl) ⟨1596770, by rfl⟩ : syracuseStep 2129027 = 3193541) B3193541
theorem B2129057 : Blo 1417528 2129057 := bstep (se 2 (by rfl) ⟨798396, by rfl⟩ : syracuseStep 2129057 = 1596793) B1596793
theorem B4037795 : Blo 1417528 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B1596595 : Blo 1417528 1596595 := bstep (se 1 (by rfl) ⟨1197446, by rfl⟩ : syracuseStep 1596595 = 2394893) B2394893
theorem B2129075 : Blo 1417528 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B7183565 : Blo 1417528 7183565 := bstep (se 3 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 7183565 = 2693837) B2693837
theorem B2129105 : Blo 1417528 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B2129123 : Blo 1417528 2129123 := bstep (se 1 (by rfl) ⟨1596842, by rfl⟩ : syracuseStep 2129123 = 3193685) B3193685
theorem B2129153 : Blo 1417528 2129153 := bstep (se 2 (by rfl) ⟨798432, by rfl⟩ : syracuseStep 2129153 = 1596865) B1596865
theorem B2129171 : Blo 1417528 2129171 := bstep (se 1 (by rfl) ⟨1596878, by rfl⟩ : syracuseStep 2129171 = 3193757) B3193757
theorem B2129201 : Blo 1417528 2129201 := bstep (se 2 (by rfl) ⟨798450, by rfl⟩ : syracuseStep 2129201 = 1596901) B1596901
theorem B1596739 : Blo 1417528 1596739 := bstep (se 1 (by rfl) ⟨1197554, by rfl⟩ : syracuseStep 1596739 = 2395109) B2395109
theorem B2129219 : Blo 1417528 2129219 := bstep (se 1 (by rfl) ⟨1596914, by rfl⟩ : syracuseStep 2129219 = 3193829) B3193829
theorem B2129249 : Blo 1417528 2129249 := bstep (se 2 (by rfl) ⟨798468, by rfl⟩ : syracuseStep 2129249 = 1596937) B1596937
theorem B2129267 : Blo 1417528 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B6471053 : Blo 1417528 6471053 := bstep (se 3 (by rfl) ⟨1213322, by rfl⟩ : syracuseStep 6471053 = 2426645) B2426645
theorem B19946933 : Blo 1417528 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1596883 : Blo 1417528 1596883 := bstep (se 1 (by rfl) ⟨1197662, by rfl⟩ : syracuseStep 1596883 = 2395325) B2395325
theorem B3833315 : Blo 1417528 3833315 := bstep (se 1 (by rfl) ⟨2874986, by rfl⟩ : syracuseStep 3833315 = 5749973) B5749973
theorem B9698915 : Blo 1417528 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B9084707 : Blo 1417528 9084707 := bstep (se 1 (by rfl) ⟨6813530, by rfl⟩ : syracuseStep 9084707 = 13627061) B13627061
theorem B3030833 : Blo 1417528 3030833 := bstep (se 2 (by rfl) ⟨1136562, by rfl⟩ : syracuseStep 3030833 = 2273125) B2273125
theorem B3456881 : Blo 1417528 3456881 := bstep (se 2 (by rfl) ⟨1296330, by rfl⟩ : syracuseStep 3456881 = 2592661) B2592661
theorem B1515395 : Blo 1417528 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B5111693 : Blo 1417528 5111693 := bstep (se 3 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 5111693 = 1916885) B1916885
theorem B13828067 : Blo 1417528 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B8306705 : Blo 1417528 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B36347939 : Blo 1417528 36347939 := bstep (se 1 (by rfl) ⟨27260954, by rfl⟩ : syracuseStep 36347939 = 54521909) B54521909
theorem B2392139 : Blo 1417528 2392139 := bstep (se 1 (by rfl) ⟨1794104, by rfl⟩ : syracuseStep 2392139 = 3588209) B3588209
theorem B1728587 : Blo 1417528 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B2728129 : Blo 1417528 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B2392267 : Blo 1417528 2392267 := bstep (se 1 (by rfl) ⟨1794200, by rfl⟩ : syracuseStep 2392267 = 3588401) B3588401
theorem B1794251 : Blo 1417528 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B4546763 : Blo 1417528 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B4784345 : Blo 1417528 4784345 := bstep (se 2 (by rfl) ⟨1794129, by rfl⟩ : syracuseStep 4784345 = 3588259) B3588259
theorem B3031319 : Blo 1417528 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B1417547 : Blo 1417528 1417547 := bstep (se 1 (by rfl) ⟨1063160, by rfl⟩ : syracuseStep 1417547 = 2126321) B2126321
theorem B1417559 : Blo 1417528 1417559 := bstep (se 1 (by rfl) ⟨1063169, by rfl⟩ : syracuseStep 1417559 = 2126339) B2126339
theorem B2392409 : Blo 1417528 2392409 := bstep (se 2 (by rfl) ⟨897153, by rfl⟩ : syracuseStep 2392409 = 1794307) B1794307
theorem B1417579 : Blo 1417528 1417579 := bstep (se 1 (by rfl) ⟨1063184, by rfl⟩ : syracuseStep 1417579 = 2126369) B2126369
theorem B1417591 : Blo 1417528 1417591 := bstep (se 1 (by rfl) ⟨1063193, by rfl⟩ : syracuseStep 1417591 = 2126387) B2126387
theorem B1417611 : Blo 1417528 1417611 := bstep (se 1 (by rfl) ⟨1063208, by rfl⟩ : syracuseStep 1417611 = 2126417) B2126417
theorem B7176599 : Blo 1417528 7176599 := bstep (se 1 (by rfl) ⟨5382449, by rfl⟩ : syracuseStep 7176599 = 10764899) B10764899
theorem B1417623 : Blo 1417528 1417623 := bstep (se 1 (by rfl) ⟨1063217, by rfl⟩ : syracuseStep 1417623 = 2126435) B2126435
theorem B1417643 : Blo 1417528 1417643 := bstep (se 1 (by rfl) ⟨1063232, by rfl⟩ : syracuseStep 1417643 = 2126465) B2126465
theorem B1417655 : Blo 1417528 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B4039105 : Blo 1417528 4039105 := bstep (se 2 (by rfl) ⟨1514664, by rfl⟩ : syracuseStep 4039105 = 3029329) B3029329
theorem B1417675 : Blo 1417528 1417675 := bstep (se 1 (by rfl) ⟨1063256, by rfl⟩ : syracuseStep 1417675 = 2126513) B2126513
theorem B1417687 : Blo 1417528 1417687 := bstep (se 1 (by rfl) ⟨1063265, by rfl⟩ : syracuseStep 1417687 = 2126531) B2126531
theorem B2392537 : Blo 1417528 2392537 := bstep (se 2 (by rfl) ⟨897201, by rfl⟩ : syracuseStep 2392537 = 1794403) B1794403
theorem B1417707 : Blo 1417528 1417707 := bstep (se 1 (by rfl) ⟨1063280, by rfl⟩ : syracuseStep 1417707 = 2126561) B2126561
theorem B1417719 : Blo 1417528 1417719 := bstep (se 1 (by rfl) ⟨1063289, by rfl⟩ : syracuseStep 1417719 = 2126579) B2126579
theorem B1417739 : Blo 1417528 1417739 := bstep (se 1 (by rfl) ⟨1063304, by rfl⟩ : syracuseStep 1417739 = 2126609) B2126609
theorem B1417751 : Blo 1417528 1417751 := bstep (se 1 (by rfl) ⟨1063313, by rfl⟩ : syracuseStep 1417751 = 2126627) B2126627
theorem B1417771 : Blo 1417528 1417771 := bstep (se 1 (by rfl) ⟨1063328, by rfl⟩ : syracuseStep 1417771 = 2126657) B2126657
theorem B1417783 : Blo 1417528 1417783 := bstep (se 1 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 1417783 = 2126675) B2126675
theorem B1417803 : Blo 1417528 1417803 := bstep (se 1 (by rfl) ⟨1063352, by rfl⟩ : syracuseStep 1417803 = 2126705) B2126705
theorem B3031627 : Blo 1417528 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B1417815 : Blo 1417528 1417815 := bstep (se 1 (by rfl) ⟨1063361, by rfl⟩ : syracuseStep 1417815 = 2126723) B2126723
theorem B3834461 : Blo 1417528 3834461 := bstep (se 3 (by rfl) ⟨718961, by rfl⟩ : syracuseStep 3834461 = 1437923) B1437923
theorem B1417835 : Blo 1417528 1417835 := bstep (se 1 (by rfl) ⟨1063376, by rfl⟩ : syracuseStep 1417835 = 2126753) B2126753
theorem B1417847 : Blo 1417528 1417847 := bstep (se 1 (by rfl) ⟨1063385, by rfl⟩ : syracuseStep 1417847 = 2126771) B2126771
theorem B1417867 : Blo 1417528 1417867 := bstep (se 1 (by rfl) ⟨1063400, by rfl⟩ : syracuseStep 1417867 = 2126801) B2126801
theorem B1417879 : Blo 1417528 1417879 := bstep (se 1 (by rfl) ⟨1063409, by rfl⟩ : syracuseStep 1417879 = 2126819) B2126819
theorem B1417899 : Blo 1417528 1417899 := bstep (se 1 (by rfl) ⟨1063424, by rfl⟩ : syracuseStep 1417899 = 2126849) B2126849
theorem B1417911 : Blo 1417528 1417911 := bstep (se 1 (by rfl) ⟨1063433, by rfl⟩ : syracuseStep 1417911 = 2126867) B2126867
theorem B1417931 : Blo 1417528 1417931 := bstep (se 1 (by rfl) ⟨1063448, by rfl⟩ : syracuseStep 1417931 = 2126897) B2126897
theorem B1417943 : Blo 1417528 1417943 := bstep (se 1 (by rfl) ⟨1063457, by rfl⟩ : syracuseStep 1417943 = 2126915) B2126915
theorem B6062809 : Blo 1417528 6062809 := bstep (se 2 (by rfl) ⟨2273553, by rfl⟩ : syracuseStep 6062809 = 4547107) B4547107
theorem B1417963 : Blo 1417528 1417963 := bstep (se 1 (by rfl) ⟨1063472, by rfl⟩ : syracuseStep 1417963 = 2126945) B2126945
theorem B1417975 : Blo 1417528 1417975 := bstep (se 1 (by rfl) ⟨1063481, by rfl⟩ : syracuseStep 1417975 = 2126963) B2126963
theorem B1417995 : Blo 1417528 1417995 := bstep (se 1 (by rfl) ⟨1063496, by rfl⟩ : syracuseStep 1417995 = 2126993) B2126993
theorem B3588887 : Blo 1417528 3588887 := bstep (se 1 (by rfl) ⟨2691665, by rfl⟩ : syracuseStep 3588887 = 5383331) B5383331
theorem B1418007 : Blo 1417528 1418007 := bstep (se 1 (by rfl) ⟨1063505, by rfl⟩ : syracuseStep 1418007 = 2127011) B2127011
theorem B1418027 : Blo 1417528 1418027 := bstep (se 1 (by rfl) ⟨1063520, by rfl⟩ : syracuseStep 1418027 = 2127041) B2127041
theorem B1418039 : Blo 1417528 1418039 := bstep (se 1 (by rfl) ⟨1063529, by rfl⟩ : syracuseStep 1418039 = 2127059) B2127059
theorem B18170689 : Blo 1417528 18170689 := bstep (se 2 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 18170689 = 13628017) B13628017
theorem B1418059 : Blo 1417528 1418059 := bstep (se 1 (by rfl) ⟨1063544, by rfl⟩ : syracuseStep 1418059 = 2127089) B2127089
theorem B1418071 : Blo 1417528 1418071 := bstep (se 1 (by rfl) ⟨1063553, by rfl⟩ : syracuseStep 1418071 = 2127107) B2127107
theorem B1418091 : Blo 1417528 1418091 := bstep (se 1 (by rfl) ⟨1063568, by rfl⟩ : syracuseStep 1418091 = 2127137) B2127137
theorem B1418103 : Blo 1417528 1418103 := bstep (se 1 (by rfl) ⟨1063577, by rfl⟩ : syracuseStep 1418103 = 2127155) B2127155
theorem B5383043 : Blo 1417528 5383043 := bstep (se 1 (by rfl) ⟨4037282, by rfl⟩ : syracuseStep 5383043 = 8074565) B8074565
theorem B1418123 : Blo 1417528 1418123 := bstep (se 1 (by rfl) ⟨1063592, by rfl⟩ : syracuseStep 1418123 = 2127185) B2127185
theorem B1794955 : Blo 1417528 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B5383057 : Blo 1417528 5383057 := bstep (se 2 (by rfl) ⟨2018646, by rfl⟩ : syracuseStep 5383057 = 4037293) B4037293
theorem B4785047 : Blo 1417528 4785047 := bstep (se 1 (by rfl) ⟨3588785, by rfl⟩ : syracuseStep 4785047 = 7177571) B7177571
theorem B1418135 : Blo 1417528 1418135 := bstep (se 1 (by rfl) ⟨1063601, by rfl⟩ : syracuseStep 1418135 = 2127203) B2127203
theorem B8078231 : Blo 1417528 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B1418155 : Blo 1417528 1418155 := bstep (se 1 (by rfl) ⟨1063616, by rfl⟩ : syracuseStep 1418155 = 2127233) B2127233
theorem B1418167 : Blo 1417528 1418167 := bstep (se 1 (by rfl) ⟨1063625, by rfl⟩ : syracuseStep 1418167 = 2127251) B2127251
theorem B1418187 : Blo 1417528 1418187 := bstep (se 1 (by rfl) ⟨1063640, by rfl⟩ : syracuseStep 1418187 = 2127281) B2127281
theorem B1418199 : Blo 1417528 1418199 := bstep (se 1 (by rfl) ⟨1063649, by rfl⟩ : syracuseStep 1418199 = 2127299) B2127299
theorem B1418219 : Blo 1417528 1418219 := bstep (se 1 (by rfl) ⟨1063664, by rfl⟩ : syracuseStep 1418219 = 2127329) B2127329
theorem B1418231 : Blo 1417528 1418231 := bstep (se 1 (by rfl) ⟨1063673, by rfl⟩ : syracuseStep 1418231 = 2127347) B2127347
theorem B1418251 : Blo 1417528 1418251 := bstep (se 1 (by rfl) ⟨1063688, by rfl⟩ : syracuseStep 1418251 = 2127377) B2127377
theorem B2393111 : Blo 1417528 2393111 := bstep (se 1 (by rfl) ⟨1794833, by rfl⟩ : syracuseStep 2393111 = 3589667) B3589667
theorem B1418263 : Blo 1417528 1418263 := bstep (se 1 (by rfl) ⟨1063697, by rfl⟩ : syracuseStep 1418263 = 2127395) B2127395
theorem B1418283 : Blo 1417528 1418283 := bstep (se 1 (by rfl) ⟨1063712, by rfl⟩ : syracuseStep 1418283 = 2127425) B2127425
theorem B6145075 : Blo 1417528 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B1418295 : Blo 1417528 1418295 := bstep (se 1 (by rfl) ⟨1063721, by rfl⟩ : syracuseStep 1418295 = 2127443) B2127443
theorem B1418315 : Blo 1417528 1418315 := bstep (se 1 (by rfl) ⟨1063736, by rfl⟩ : syracuseStep 1418315 = 2127473) B2127473
theorem B1418327 : Blo 1417528 1418327 := bstep (se 1 (by rfl) ⟨1063745, by rfl⟩ : syracuseStep 1418327 = 2127491) B2127491
theorem B1418347 : Blo 1417528 1418347 := bstep (se 1 (by rfl) ⟨1063760, by rfl⟩ : syracuseStep 1418347 = 2127521) B2127521
theorem B1418359 : Blo 1417528 1418359 := bstep (se 1 (by rfl) ⟨1063769, by rfl⟩ : syracuseStep 1418359 = 2127539) B2127539
theorem B1418379 : Blo 1417528 1418379 := bstep (se 1 (by rfl) ⟨1063784, by rfl⟩ : syracuseStep 1418379 = 2127569) B2127569
theorem B2393239 : Blo 1417528 2393239 := bstep (se 1 (by rfl) ⟨1794929, by rfl⟩ : syracuseStep 2393239 = 3589859) B3589859
theorem B1418391 : Blo 1417528 1418391 := bstep (se 1 (by rfl) ⟨1063793, by rfl⟩ : syracuseStep 1418391 = 2127587) B2127587
theorem B1795223 : Blo 1417528 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B1418411 : Blo 1417528 1418411 := bstep (se 1 (by rfl) ⟨1063808, by rfl⟩ : syracuseStep 1418411 = 2127617) B2127617
theorem B1418423 : Blo 1417528 1418423 := bstep (se 1 (by rfl) ⟨1063817, by rfl⟩ : syracuseStep 1418423 = 2127635) B2127635
theorem B5383361 : Blo 1417528 5383361 := bstep (se 2 (by rfl) ⟨2018760, by rfl⟩ : syracuseStep 5383361 = 4037521) B4037521
theorem B1418443 : Blo 1417528 1418443 := bstep (se 1 (by rfl) ⟨1063832, by rfl⟩ : syracuseStep 1418443 = 2127665) B2127665
theorem B1418455 : Blo 1417528 1418455 := bstep (se 1 (by rfl) ⟨1063841, by rfl⟩ : syracuseStep 1418455 = 2127683) B2127683
theorem B3237079 : Blo 1417528 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B4850909 : Blo 1417528 4850909 := bstep (se 3 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 4850909 = 1819091) B1819091
theorem B1418475 : Blo 1417528 1418475 := bstep (se 1 (by rfl) ⟨1063856, by rfl⟩ : syracuseStep 1418475 = 2127713) B2127713
theorem B1418487 : Blo 1417528 1418487 := bstep (se 1 (by rfl) ⟨1063865, by rfl⟩ : syracuseStep 1418487 = 2127731) B2127731
theorem B1418507 : Blo 1417528 1418507 := bstep (se 1 (by rfl) ⟨1063880, by rfl⟩ : syracuseStep 1418507 = 2127761) B2127761
theorem B1418519 : Blo 1417528 1418519 := bstep (se 1 (by rfl) ⟨1063889, by rfl⟩ : syracuseStep 1418519 = 2127779) B2127779
theorem B2155801 : Blo 1417528 2155801 := bstep (se 2 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 2155801 = 1616851) B1616851
theorem B1418539 : Blo 1417528 1418539 := bstep (se 1 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 1418539 = 2127809) B2127809
theorem B1418551 : Blo 1417528 1418551 := bstep (se 1 (by rfl) ⟨1063913, by rfl⟩ : syracuseStep 1418551 = 2127827) B2127827
theorem B1418571 : Blo 1417528 1418571 := bstep (se 1 (by rfl) ⟨1063928, by rfl⟩ : syracuseStep 1418571 = 2127857) B2127857
theorem B1418583 : Blo 1417528 1418583 := bstep (se 1 (by rfl) ⟨1063937, by rfl⟩ : syracuseStep 1418583 = 2127875) B2127875
theorem B1418603 : Blo 1417528 1418603 := bstep (se 1 (by rfl) ⟨1063952, by rfl⟩ : syracuseStep 1418603 = 2127905) B2127905
theorem B1418615 : Blo 1417528 1418615 := bstep (se 1 (by rfl) ⟨1063961, by rfl⟩ : syracuseStep 1418615 = 2127923) B2127923
theorem B1418635 : Blo 1417528 1418635 := bstep (se 1 (by rfl) ⟨1063976, by rfl⟩ : syracuseStep 1418635 = 2127953) B2127953
theorem B1418647 : Blo 1417528 1418647 := bstep (se 1 (by rfl) ⟨1063985, by rfl⟩ : syracuseStep 1418647 = 2127971) B2127971
theorem B1418667 : Blo 1417528 1418667 := bstep (se 1 (by rfl) ⟨1064000, by rfl⟩ : syracuseStep 1418667 = 2128001) B2128001
theorem B4785587 : Blo 1417528 4785587 := bstep (se 1 (by rfl) ⟨3589190, by rfl⟩ : syracuseStep 4785587 = 7178381) B7178381
theorem B3589555 : Blo 1417528 3589555 := bstep (se 1 (by rfl) ⟨2692166, by rfl⟩ : syracuseStep 3589555 = 5384333) B5384333
theorem B4097459 : Blo 1417528 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B1418679 : Blo 1417528 1418679 := bstep (se 1 (by rfl) ⟨1064009, by rfl⟩ : syracuseStep 1418679 = 2128019) B2128019
theorem B1418699 : Blo 1417528 1418699 := bstep (se 1 (by rfl) ⟨1064024, by rfl⟩ : syracuseStep 1418699 = 2128049) B2128049
theorem B1418711 : Blo 1417528 1418711 := bstep (se 1 (by rfl) ⟨1064033, by rfl⟩ : syracuseStep 1418711 = 2128067) B2128067
theorem B1418731 : Blo 1417528 1418731 := bstep (se 1 (by rfl) ⟨1064048, by rfl⟩ : syracuseStep 1418731 = 2128097) B2128097
theorem B1418743 : Blo 1417528 1418743 := bstep (se 1 (by rfl) ⟨1064057, by rfl⟩ : syracuseStep 1418743 = 2128115) B2128115
theorem B1418763 : Blo 1417528 1418763 := bstep (se 1 (by rfl) ⟨1064072, by rfl⟩ : syracuseStep 1418763 = 2128145) B2128145
theorem B1418775 : Blo 1417528 1418775 := bstep (se 1 (by rfl) ⟨1064081, by rfl⟩ : syracuseStep 1418775 = 2128163) B2128163
theorem B1418795 : Blo 1417528 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B1418807 : Blo 1417528 1418807 := bstep (se 1 (by rfl) ⟨1064105, by rfl⟩ : syracuseStep 1418807 = 2128211) B2128211
theorem B3589697 : Blo 1417528 3589697 := bstep (se 2 (by rfl) ⟨1346136, by rfl⟩ : syracuseStep 3589697 = 2692273) B2692273
theorem B1418827 : Blo 1417528 1418827 := bstep (se 1 (by rfl) ⟨1064120, by rfl⟩ : syracuseStep 1418827 = 2128241) B2128241
theorem B7185995 : Blo 1417528 7185995 := bstep (se 1 (by rfl) ⟨5389496, by rfl⟩ : syracuseStep 7185995 = 10778993) B10778993
theorem B1418839 : Blo 1417528 1418839 := bstep (se 1 (by rfl) ⟨1064129, by rfl⟩ : syracuseStep 1418839 = 2128259) B2128259
theorem B1418859 : Blo 1417528 1418859 := bstep (se 1 (by rfl) ⟨1064144, by rfl⟩ : syracuseStep 1418859 = 2128289) B2128289
theorem B1418871 : Blo 1417528 1418871 := bstep (se 1 (by rfl) ⟨1064153, by rfl⟩ : syracuseStep 1418871 = 2128307) B2128307
theorem B1418891 : Blo 1417528 1418891 := bstep (se 1 (by rfl) ⟨1064168, by rfl⟩ : syracuseStep 1418891 = 2128337) B2128337
theorem B1418903 : Blo 1417528 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B2877079 : Blo 1417528 2877079 := bstep (se 1 (by rfl) ⟨2157809, by rfl⟩ : syracuseStep 2877079 = 4315619) B4315619
theorem B1418923 : Blo 1417528 1418923 := bstep (se 1 (by rfl) ⟨1064192, by rfl⟩ : syracuseStep 1418923 = 2128385) B2128385
theorem B1418935 : Blo 1417528 1418935 := bstep (se 1 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 1418935 = 2128403) B2128403
theorem B4785857 : Blo 1417528 4785857 := bstep (se 2 (by rfl) ⟨1794696, by rfl⟩ : syracuseStep 4785857 = 3589393) B3589393
theorem B1418955 : Blo 1417528 1418955 := bstep (se 1 (by rfl) ⟨1064216, by rfl⟩ : syracuseStep 1418955 = 2128433) B2128433
theorem B1418967 : Blo 1417528 1418967 := bstep (se 1 (by rfl) ⟨1064225, by rfl⟩ : syracuseStep 1418967 = 2128451) B2128451
theorem B1418987 : Blo 1417528 1418987 := bstep (se 1 (by rfl) ⟨1064240, by rfl⟩ : syracuseStep 1418987 = 2128481) B2128481
theorem B1418999 : Blo 1417528 1418999 := bstep (se 1 (by rfl) ⟨1064249, by rfl⟩ : syracuseStep 1418999 = 2128499) B2128499
theorem B2393867 : Blo 1417528 2393867 := bstep (se 1 (by rfl) ⟨1795400, by rfl⟩ : syracuseStep 2393867 = 3590801) B3590801
theorem B1419019 : Blo 1417528 1419019 := bstep (se 1 (by rfl) ⟨1064264, by rfl⟩ : syracuseStep 1419019 = 2128529) B2128529
theorem B1419031 : Blo 1417528 1419031 := bstep (se 1 (by rfl) ⟨1064273, by rfl⟩ : syracuseStep 1419031 = 2128547) B2128547
theorem B1419051 : Blo 1417528 1419051 := bstep (se 1 (by rfl) ⟨1064288, by rfl⟩ : syracuseStep 1419051 = 2128577) B2128577
theorem B5113651 : Blo 1417528 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B1419063 : Blo 1417528 1419063 := bstep (se 1 (by rfl) ⟨1064297, by rfl⟩ : syracuseStep 1419063 = 2128595) B2128595
theorem B1419083 : Blo 1417528 1419083 := bstep (se 1 (by rfl) ⟨1064312, by rfl⟩ : syracuseStep 1419083 = 2128625) B2128625
theorem B1795927 : Blo 1417528 1795927 := bstep (se 1 (by rfl) ⟨1346945, by rfl⟩ : syracuseStep 1795927 = 2693891) B2693891
theorem B1419095 : Blo 1417528 1419095 := bstep (se 1 (by rfl) ⟨1064321, by rfl⟩ : syracuseStep 1419095 = 2128643) B2128643
theorem B5384029 : Blo 1417528 5384029 := bstep (se 3 (by rfl) ⟨1009505, by rfl⟩ : syracuseStep 5384029 = 2019011) B2019011
theorem B1419115 : Blo 1417528 1419115 := bstep (se 1 (by rfl) ⟨1064336, by rfl⟩ : syracuseStep 1419115 = 2128673) B2128673
theorem B1419127 : Blo 1417528 1419127 := bstep (se 1 (by rfl) ⟨1064345, by rfl⟩ : syracuseStep 1419127 = 2128691) B2128691
theorem B2393995 : Blo 1417528 2393995 := bstep (se 1 (by rfl) ⟨1795496, by rfl⟩ : syracuseStep 2393995 = 3590993) B3590993
theorem B1419147 : Blo 1417528 1419147 := bstep (se 1 (by rfl) ⟨1064360, by rfl⟩ : syracuseStep 1419147 = 2128721) B2128721
theorem B1419159 : Blo 1417528 1419159 := bstep (se 1 (by rfl) ⟨1064369, by rfl⟩ : syracuseStep 1419159 = 2128739) B2128739
theorem B1419179 : Blo 1417528 1419179 := bstep (se 1 (by rfl) ⟨1064384, by rfl⟩ : syracuseStep 1419179 = 2128769) B2128769
theorem B1419191 : Blo 1417528 1419191 := bstep (se 1 (by rfl) ⟨1064393, by rfl⟩ : syracuseStep 1419191 = 2128787) B2128787
theorem B1419211 : Blo 1417528 1419211 := bstep (se 1 (by rfl) ⟨1064408, by rfl⟩ : syracuseStep 1419211 = 2128817) B2128817
theorem B1419223 : Blo 1417528 1419223 := bstep (se 1 (by rfl) ⟨1064417, by rfl⟩ : syracuseStep 1419223 = 2128835) B2128835
theorem B1419243 : Blo 1417528 1419243 := bstep (se 1 (by rfl) ⟨1064432, by rfl⟩ : syracuseStep 1419243 = 2128865) B2128865
theorem B1419255 : Blo 1417528 1419255 := bstep (se 1 (by rfl) ⟨1064441, by rfl⟩ : syracuseStep 1419255 = 2128883) B2128883
theorem B1419275 : Blo 1417528 1419275 := bstep (se 1 (by rfl) ⟨1064456, by rfl⟩ : syracuseStep 1419275 = 2128913) B2128913
theorem B20441105 : Blo 1417528 20441105 := bstep (se 2 (by rfl) ⟨7665414, by rfl⟩ : syracuseStep 20441105 = 15330829) B15330829
theorem B1419287 : Blo 1417528 1419287 := bstep (se 1 (by rfl) ⟨1064465, by rfl⟩ : syracuseStep 1419287 = 2128931) B2128931
theorem B2394137 : Blo 1417528 2394137 := bstep (se 2 (by rfl) ⟨897801, by rfl⟩ : syracuseStep 2394137 = 1795603) B1795603
theorem B1419307 : Blo 1417528 1419307 := bstep (se 1 (by rfl) ⟨1064480, by rfl⟩ : syracuseStep 1419307 = 2128961) B2128961
theorem B1419319 : Blo 1417528 1419319 := bstep (se 1 (by rfl) ⟨1064489, by rfl⟩ : syracuseStep 1419319 = 2128979) B2128979
theorem B4040779 : Blo 1417528 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B1419339 : Blo 1417528 1419339 := bstep (se 1 (by rfl) ⟨1064504, by rfl⟩ : syracuseStep 1419339 = 2129009) B2129009
theorem B1419351 : Blo 1417528 1419351 := bstep (se 1 (by rfl) ⟨1064513, by rfl⟩ : syracuseStep 1419351 = 2129027) B2129027
theorem B1419371 : Blo 1417528 1419371 := bstep (se 1 (by rfl) ⟨1064528, by rfl⟩ : syracuseStep 1419371 = 2129057) B2129057
theorem B1419383 : Blo 1417528 1419383 := bstep (se 1 (by rfl) ⟨1064537, by rfl⟩ : syracuseStep 1419383 = 2129075) B2129075
theorem B1419403 : Blo 1417528 1419403 := bstep (se 1 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 1419403 = 2129105) B2129105
theorem B1419415 : Blo 1417528 1419415 := bstep (se 1 (by rfl) ⟨1064561, by rfl⟩ : syracuseStep 1419415 = 2129123) B2129123
theorem B2394265 : Blo 1417528 2394265 := bstep (se 2 (by rfl) ⟨897849, by rfl⟩ : syracuseStep 2394265 = 1795699) B1795699
theorem B1419435 : Blo 1417528 1419435 := bstep (se 1 (by rfl) ⟨1064576, by rfl⟩ : syracuseStep 1419435 = 2129153) B2129153
theorem B1419447 : Blo 1417528 1419447 := bstep (se 1 (by rfl) ⟨1064585, by rfl⟩ : syracuseStep 1419447 = 2129171) B2129171
theorem B1419467 : Blo 1417528 1419467 := bstep (se 1 (by rfl) ⟨1064600, by rfl⟩ : syracuseStep 1419467 = 2129201) B2129201
theorem B1419479 : Blo 1417528 1419479 := bstep (se 1 (by rfl) ⟨1064609, by rfl⟩ : syracuseStep 1419479 = 2129219) B2129219
theorem B4786397 : Blo 1417528 4786397 := bstep (se 3 (by rfl) ⟨897449, by rfl⟩ : syracuseStep 4786397 = 1794899) B1794899
theorem B1419499 : Blo 1417528 1419499 := bstep (se 1 (by rfl) ⟨1064624, by rfl⟩ : syracuseStep 1419499 = 2129249) B2129249
theorem B1419511 : Blo 1417528 1419511 := bstep (se 1 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 1419511 = 2129267) B2129267
theorem B7276817 : Blo 1417528 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B13297955 : Blo 1417528 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B4041053 : Blo 1417528 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B6465943 : Blo 1417528 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B6056471 : Blo 1417528 6056471 := bstep (se 1 (by rfl) ⟨4542353, by rfl⟩ : syracuseStep 6056471 = 9084707) B9084707
theorem B10775105 : Blo 1417528 10775105 := bstep (se 2 (by rfl) ⟨4040664, by rfl⟩ : syracuseStep 10775105 = 8081329) B8081329
theorem B2304587 : Blo 1417528 2304587 := bstep (se 1 (by rfl) ⟨1728440, by rfl⟩ : syracuseStep 2304587 = 3456881) B3456881
theorem B9218711 : Blo 1417528 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B2394839 : Blo 1417528 2394839 := bstep (se 1 (by rfl) ⟨1796129, by rfl⟩ : syracuseStep 2394839 = 3592259) B3592259
theorem B3189491 : Blo 1417528 3189491 := bstep (se 1 (by rfl) ⟨2392118, by rfl⟩ : syracuseStep 3189491 = 4784237) B4784237
theorem B8080145 : Blo 1417528 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B3189527 : Blo 1417528 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B3590963 : Blo 1417528 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B2394967 : Blo 1417528 2394967 := bstep (se 1 (by rfl) ⟨1796225, by rfl⟩ : syracuseStep 2394967 = 3592451) B3592451
theorem B2272151 : Blo 1417528 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B3189707 : Blo 1417528 3189707 := bstep (se 1 (by rfl) ⟨2392280, by rfl⟩ : syracuseStep 3189707 = 4784561) B4784561
theorem B2157529 : Blo 1417528 2157529 := bstep (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) B1618147
theorem B3189761 : Blo 1417528 3189761 := bstep (se 2 (by rfl) ⟨1196160, by rfl⟩ : syracuseStep 3189761 = 2392321) B2392321
theorem B12119057 : Blo 1417528 12119057 := bstep (se 2 (by rfl) ⟨4544646, by rfl⟩ : syracuseStep 12119057 = 9089293) B9089293
theorem B5385305 : Blo 1417528 5385305 := bstep (se 2 (by rfl) ⟨2019489, by rfl⟩ : syracuseStep 5385305 = 4038979) B4038979
theorem B3189977 : Blo 1417528 3189977 := bstep (se 2 (by rfl) ⟨1196241, by rfl⟩ : syracuseStep 3189977 = 2392483) B2392483
theorem B3190067 : Blo 1417528 3190067 := bstep (se 1 (by rfl) ⟨2392550, by rfl⟩ : syracuseStep 3190067 = 4785101) B4785101
theorem B4787531 : Blo 1417528 4787531 := bstep (se 1 (by rfl) ⟨3590648, by rfl⟩ : syracuseStep 4787531 = 7181297) B7181297
theorem B3591499 : Blo 1417528 3591499 := bstep (se 1 (by rfl) ⟨2693624, by rfl⟩ : syracuseStep 3591499 = 5387249) B5387249
theorem B3190103 : Blo 1417528 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B25873843 : Blo 1417528 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B2272715 : Blo 1417528 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B3591641 : Blo 1417528 3591641 := bstep (se 2 (by rfl) ⟨1346865, by rfl⟩ : syracuseStep 3591641 = 2693731) B2693731
theorem B3190283 : Blo 1417528 3190283 := bstep (se 1 (by rfl) ⟨2392712, by rfl⟩ : syracuseStep 3190283 = 4785425) B4785425
theorem B7982657 : Blo 1417528 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B3190337 : Blo 1417528 3190337 := bstep (se 2 (by rfl) ⟨1196376, by rfl⟩ : syracuseStep 3190337 = 2392753) B2392753
theorem B4787801 : Blo 1417528 4787801 := bstep (se 2 (by rfl) ⟨1795425, by rfl⟩ : syracuseStep 4787801 = 3590851) B3590851
theorem B17739415 : Blo 1417528 17739415 := bstep (se 1 (by rfl) ⟨13304561, by rfl⟩ : syracuseStep 17739415 = 26609123) B26609123
theorem B3452633 : Blo 1417528 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B6819545 : Blo 1417528 6819545 := bstep (se 2 (by rfl) ⟨2557329, by rfl⟩ : syracuseStep 6819545 = 5114659) B5114659
theorem B3190553 : Blo 1417528 3190553 := bstep (se 2 (by rfl) ⟨1196457, by rfl⟩ : syracuseStep 3190553 = 2392915) B2392915
theorem B2019097 : Blo 1417528 2019097 := bstep (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) B1514323
theorem B40898357 : Blo 1417528 40898357 := bstep (se 5 (by rfl) ⟨1917110, by rfl⟩ : syracuseStep 40898357 = 3834221) B3834221
theorem B3190643 : Blo 1417528 3190643 := bstep (se 1 (by rfl) ⟨2392982, by rfl⟩ : syracuseStep 3190643 = 4785965) B4785965
theorem B7180163 : Blo 1417528 7180163 := bstep (se 1 (by rfl) ⟨5385122, by rfl⟩ : syracuseStep 7180163 = 10770245) B10770245
theorem B3190679 : Blo 1417528 3190679 := bstep (se 1 (by rfl) ⟨2393009, by rfl⟩ : syracuseStep 3190679 = 4786019) B4786019
theorem B9211799 : Blo 1417528 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B17264657 : Blo 1417528 17264657 := bstep (se 2 (by rfl) ⟨6474246, by rfl⟩ : syracuseStep 17264657 = 12948493) B12948493
theorem B4853783 : Blo 1417528 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B1536023 : Blo 1417528 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B3190859 : Blo 1417528 3190859 := bstep (se 1 (by rfl) ⟨2393144, by rfl⟩ : syracuseStep 3190859 = 4786289) B4786289
theorem B3190913 : Blo 1417528 3190913 := bstep (se 2 (by rfl) ⟨1196592, by rfl⟩ : syracuseStep 3190913 = 2393185) B2393185
theorem B4788503 : Blo 1417528 4788503 := bstep (se 1 (by rfl) ⟨3591377, by rfl⟩ : syracuseStep 4788503 = 7182755) B7182755
theorem B3592471 : Blo 1417528 3592471 := bstep (se 1 (by rfl) ⟨2694353, by rfl⟩ : syracuseStep 3592471 = 5388707) B5388707
theorem B5755159 : Blo 1417528 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B24236333 : Blo 1417528 24236333 := bstep (se 3 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 24236333 = 9088625) B9088625
theorem B3191129 : Blo 1417528 3191129 := bstep (se 2 (by rfl) ⟨1196673, by rfl⟩ : syracuseStep 3191129 = 2393347) B2393347
theorem B1618283 : Blo 1417528 1618283 := bstep (se 1 (by rfl) ⟨1213712, by rfl⟩ : syracuseStep 1618283 = 2427425) B2427425
theorem B69005681 : Blo 1417528 69005681 := bstep (se 2 (by rfl) ⟨25877130, by rfl⟩ : syracuseStep 69005681 = 51754261) B51754261
theorem B6058385 : Blo 1417528 6058385 := bstep (se 2 (by rfl) ⟨2271894, by rfl⟩ : syracuseStep 6058385 = 4543789) B4543789
theorem B3191219 : Blo 1417528 3191219 := bstep (se 1 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 3191219 = 4786829) B4786829
theorem B3191255 : Blo 1417528 3191255 := bstep (se 1 (by rfl) ⟨2393441, by rfl⟩ : syracuseStep 3191255 = 4786883) B4786883
theorem B2126297 : Blo 1417528 2126297 := bstep (se 2 (by rfl) ⟨797361, by rfl⟩ : syracuseStep 2126297 = 1594723) B1594723
theorem B13627865 : Blo 1417528 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B10777049 : Blo 1417528 10777049 := bstep (se 2 (by rfl) ⟨4041393, by rfl⟩ : syracuseStep 10777049 = 8082787) B8082787
theorem B2126411 : Blo 1417528 2126411 := bstep (se 1 (by rfl) ⟨1594808, by rfl⟩ : syracuseStep 2126411 = 3189617) B3189617
theorem B12276299 : Blo 1417528 12276299 := bstep (se 1 (by rfl) ⟨9207224, by rfl⟩ : syracuseStep 12276299 = 18414449) B18414449
theorem B2126423 : Blo 1417528 2126423 := bstep (se 1 (by rfl) ⟨1594817, by rfl⟩ : syracuseStep 2126423 = 3189635) B3189635
theorem B28381789 : Blo 1417528 28381789 := bstep (se 3 (by rfl) ⟨5321585, by rfl⟩ : syracuseStep 28381789 = 10643171) B10643171
theorem B3191435 : Blo 1417528 3191435 := bstep (se 1 (by rfl) ⟨2393576, by rfl⟩ : syracuseStep 3191435 = 4787153) B4787153
theorem B2019991 : Blo 1417528 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B2126489 : Blo 1417528 2126489 := bstep (se 2 (by rfl) ⟨797433, by rfl⟩ : syracuseStep 2126489 = 1594867) B1594867
theorem B5386931 : Blo 1417528 5386931 := bstep (se 1 (by rfl) ⟨4040198, by rfl⟩ : syracuseStep 5386931 = 8080397) B8080397
theorem B3191489 : Blo 1417528 3191489 := bstep (se 2 (by rfl) ⟨1196808, by rfl⟩ : syracuseStep 3191489 = 2393617) B2393617
theorem B5386945 : Blo 1417528 5386945 := bstep (se 2 (by rfl) ⟨2020104, by rfl⟩ : syracuseStep 5386945 = 4040209) B4040209
theorem B2691787 : Blo 1417528 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B3592907 : Blo 1417528 3592907 := bstep (se 1 (by rfl) ⟨2694680, by rfl⟩ : syracuseStep 3592907 = 5389361) B5389361
theorem B12284621 : Blo 1417528 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B2126603 : Blo 1417528 2126603 := bstep (se 1 (by rfl) ⟨1594952, by rfl⟩ : syracuseStep 2126603 = 3189905) B3189905
theorem B2126615 : Blo 1417528 2126615 := bstep (se 1 (by rfl) ⟨1594961, by rfl⟩ : syracuseStep 2126615 = 3189923) B3189923
theorem B2691863 : Blo 1417528 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B4789043 : Blo 1417528 4789043 := bstep (se 1 (by rfl) ⟨3591782, by rfl⟩ : syracuseStep 4789043 = 7183565) B7183565
theorem B2126681 : Blo 1417528 2126681 := bstep (se 2 (by rfl) ⟨797505, by rfl⟩ : syracuseStep 2126681 = 1595011) B1595011
theorem B36361061 : Blo 1417528 36361061 := bstep (se 4 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 36361061 = 6817699) B6817699
theorem B3027851 : Blo 1417528 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B3191705 : Blo 1417528 3191705 := bstep (se 2 (by rfl) ⟨1196889, by rfl⟩ : syracuseStep 3191705 = 2393779) B2393779
theorem B4314035 : Blo 1417528 4314035 := bstep (se 1 (by rfl) ⟨3235526, by rfl⟩ : syracuseStep 4314035 = 6471053) B6471053
theorem B2126795 : Blo 1417528 2126795 := bstep (se 1 (by rfl) ⟨1595096, by rfl⟩ : syracuseStep 2126795 = 3190193) B3190193
theorem B2126807 : Blo 1417528 2126807 := bstep (se 1 (by rfl) ⟨1595105, by rfl⟩ : syracuseStep 2126807 = 3190211) B3190211
theorem B4920281 : Blo 1417528 4920281 := bstep (se 2 (by rfl) ⟨1845105, by rfl⟩ : syracuseStep 4920281 = 3690211) B3690211
theorem B3191795 : Blo 1417528 3191795 := bstep (se 1 (by rfl) ⟨2393846, by rfl⟩ : syracuseStep 3191795 = 4787693) B4787693
theorem B3191831 : Blo 1417528 3191831 := bstep (se 1 (by rfl) ⟨2393873, by rfl⟩ : syracuseStep 3191831 = 4787747) B4787747
theorem B2126873 : Blo 1417528 2126873 := bstep (se 2 (by rfl) ⟨797577, by rfl⟩ : syracuseStep 2126873 = 1595155) B1595155
theorem B4789313 : Blo 1417528 4789313 := bstep (se 2 (by rfl) ⟨1795992, by rfl⟩ : syracuseStep 4789313 = 3591985) B3591985
theorem B2126987 : Blo 1417528 2126987 := bstep (se 1 (by rfl) ⟨1595240, by rfl⟩ : syracuseStep 2126987 = 3190481) B3190481
theorem B2126999 : Blo 1417528 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B1438871 : Blo 1417528 1438871 := bstep (se 1 (by rfl) ⟨1079153, by rfl⟩ : syracuseStep 1438871 = 2158307) B2158307
theorem B3192011 : Blo 1417528 3192011 := bstep (se 1 (by rfl) ⟨2394008, by rfl⟩ : syracuseStep 3192011 = 4788017) B4788017
theorem B2020555 : Blo 1417528 2020555 := bstep (se 1 (by rfl) ⟨1515416, by rfl⟩ : syracuseStep 2020555 = 3030833) B3030833
theorem B2127065 : Blo 1417528 2127065 := bstep (se 2 (by rfl) ⟨797649, by rfl⟩ : syracuseStep 2127065 = 1595299) B1595299
theorem B3192065 : Blo 1417528 3192065 := bstep (se 2 (by rfl) ⟨1197024, by rfl⟩ : syracuseStep 3192065 = 2394049) B2394049
theorem B2127179 : Blo 1417528 2127179 := bstep (se 1 (by rfl) ⟨1595384, by rfl⟩ : syracuseStep 2127179 = 3190769) B3190769
theorem B2127191 : Blo 1417528 2127191 := bstep (se 1 (by rfl) ⟨1595393, by rfl⟩ : syracuseStep 2127191 = 3190787) B3190787
theorem B6059357 : Blo 1417528 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B2127257 : Blo 1417528 2127257 := bstep (se 2 (by rfl) ⟨797721, by rfl⟩ : syracuseStep 2127257 = 1595443) B1595443
theorem B1594795 : Blo 1417528 1594795 := bstep (se 1 (by rfl) ⟨1196096, by rfl⟩ : syracuseStep 1594795 = 2392193) B2392193
theorem B2692531 : Blo 1417528 2692531 := bstep (se 1 (by rfl) ⟨2019398, by rfl⟩ : syracuseStep 2692531 = 4038797) B4038797
theorem B3028441 : Blo 1417528 3028441 := bstep (se 2 (by rfl) ⟨1135665, by rfl⟩ : syracuseStep 3028441 = 2271331) B2271331
theorem B3192281 : Blo 1417528 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B6469085 : Blo 1417528 6469085 := bstep (se 3 (by rfl) ⟨1212953, by rfl⟩ : syracuseStep 6469085 = 2425907) B2425907
theorem B2127371 : Blo 1417528 2127371 := bstep (se 1 (by rfl) ⟨1595528, by rfl⟩ : syracuseStep 2127371 = 3191057) B3191057
theorem B1594903 : Blo 1417528 1594903 := bstep (se 1 (by rfl) ⟨1196177, by rfl⟩ : syracuseStep 1594903 = 2392355) B2392355
theorem B2127383 : Blo 1417528 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B3192371 : Blo 1417528 3192371 := bstep (se 1 (by rfl) ⟨2394278, by rfl⟩ : syracuseStep 3192371 = 4788557) B4788557
theorem B25876037 : Blo 1417528 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B3192407 : Blo 1417528 3192407 := bstep (se 1 (by rfl) ⟨2394305, by rfl⟩ : syracuseStep 3192407 = 4788611) B4788611
theorem B2127449 : Blo 1417528 2127449 := bstep (se 2 (by rfl) ⟨797793, by rfl⟩ : syracuseStep 2127449 = 1595587) B1595587
theorem B4789853 : Blo 1417528 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B12940901 : Blo 1417528 12940901 := bstep (se 4 (by rfl) ⟨1213209, by rfl⟩ : syracuseStep 12940901 = 2426419) B2426419
theorem B18183811 : Blo 1417528 18183811 := bstep (se 1 (by rfl) ⟨13637858, by rfl⟩ : syracuseStep 18183811 = 27275717) B27275717
theorem B2692759 : Blo 1417528 2692759 := bstep (se 1 (by rfl) ⟨2019569, by rfl⟩ : syracuseStep 2692759 = 4039139) B4039139
theorem B1595083 : Blo 1417528 1595083 := bstep (se 1 (by rfl) ⟨1196312, by rfl⟩ : syracuseStep 1595083 = 2392625) B2392625
theorem B2127563 : Blo 1417528 2127563 := bstep (se 1 (by rfl) ⟨1595672, by rfl⟩ : syracuseStep 2127563 = 3191345) B3191345
theorem B2127575 : Blo 1417528 2127575 := bstep (se 1 (by rfl) ⟨1595681, by rfl⟩ : syracuseStep 2127575 = 3191363) B3191363
theorem B2692865 : Blo 1417528 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B10368773 : Blo 1417528 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B3192587 : Blo 1417528 3192587 := bstep (se 1 (by rfl) ⟨2394440, by rfl⟩ : syracuseStep 3192587 = 4788881) B4788881
theorem B5109527 : Blo 1417528 5109527 := bstep (se 1 (by rfl) ⟨3832145, by rfl⟩ : syracuseStep 5109527 = 7664291) B7664291
theorem B2127641 : Blo 1417528 2127641 := bstep (se 2 (by rfl) ⟨797865, by rfl⟩ : syracuseStep 2127641 = 1595731) B1595731
theorem B1595191 : Blo 1417528 1595191 := bstep (se 1 (by rfl) ⟨1196393, by rfl⟩ : syracuseStep 1595191 = 2392787) B2392787
theorem B3192641 : Blo 1417528 3192641 := bstep (se 2 (by rfl) ⟨1197240, by rfl⟩ : syracuseStep 3192641 = 2394481) B2394481
theorem B16824181 : Blo 1417528 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B2127755 : Blo 1417528 2127755 := bstep (se 1 (by rfl) ⟨1595816, by rfl⟩ : syracuseStep 2127755 = 3191633) B3191633
theorem B2127767 : Blo 1417528 2127767 := bstep (se 1 (by rfl) ⟨1595825, by rfl⟩ : syracuseStep 2127767 = 3191651) B3191651
theorem B2693017 : Blo 1417528 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B2127833 : Blo 1417528 2127833 := bstep (se 2 (by rfl) ⟨797937, by rfl⟩ : syracuseStep 2127833 = 1595875) B1595875
theorem B1595371 : Blo 1417528 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B3192857 : Blo 1417528 3192857 := bstep (se 2 (by rfl) ⟨1197321, by rfl⟩ : syracuseStep 3192857 = 2394643) B2394643
theorem B2127947 : Blo 1417528 2127947 := bstep (se 1 (by rfl) ⟨1595960, by rfl⟩ : syracuseStep 2127947 = 3191921) B3191921
theorem B1595479 : Blo 1417528 1595479 := bstep (se 1 (by rfl) ⟨1196609, by rfl⟩ : syracuseStep 1595479 = 2393219) B2393219
theorem B2127959 : Blo 1417528 2127959 := bstep (se 1 (by rfl) ⟨1595969, by rfl⟩ : syracuseStep 2127959 = 3191939) B3191939
theorem B3192947 : Blo 1417528 3192947 := bstep (se 1 (by rfl) ⟨2394710, by rfl⟩ : syracuseStep 3192947 = 4789421) B4789421
theorem B3192983 : Blo 1417528 3192983 := bstep (se 1 (by rfl) ⟨2394737, by rfl⟩ : syracuseStep 3192983 = 4789475) B4789475
theorem B2128025 : Blo 1417528 2128025 := bstep (se 2 (by rfl) ⟨798009, by rfl⟩ : syracuseStep 2128025 = 1596019) B1596019
theorem B3234059 : Blo 1417528 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B1595659 : Blo 1417528 1595659 := bstep (se 1 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 1595659 = 2393489) B2393489
theorem B2128139 : Blo 1417528 2128139 := bstep (se 1 (by rfl) ⟨1596104, by rfl⟩ : syracuseStep 2128139 = 3192209) B3192209
theorem B2128151 : Blo 1417528 2128151 := bstep (se 1 (by rfl) ⟨1596113, by rfl⟩ : syracuseStep 2128151 = 3192227) B3192227
theorem B26589485 : Blo 1417528 26589485 := bstep (se 3 (by rfl) ⟨4985528, by rfl⟩ : syracuseStep 26589485 = 9971057) B9971057
theorem B3193163 : Blo 1417528 3193163 := bstep (se 1 (by rfl) ⟨2394872, by rfl⟩ : syracuseStep 3193163 = 4789745) B4789745
theorem B2128217 : Blo 1417528 2128217 := bstep (se 2 (by rfl) ⟨798081, by rfl⟩ : syracuseStep 2128217 = 1596163) B1596163
theorem B8747365 : Blo 1417528 8747365 := bstep (se 4 (by rfl) ⟨820065, by rfl⟩ : syracuseStep 8747365 = 1640131) B1640131
theorem B1595767 : Blo 1417528 1595767 := bstep (se 1 (by rfl) ⟨1196825, by rfl⟩ : syracuseStep 1595767 = 2393651) B2393651
theorem B3193217 : Blo 1417528 3193217 := bstep (se 2 (by rfl) ⟨1197456, by rfl⟩ : syracuseStep 3193217 = 2394913) B2394913
theorem B2128331 : Blo 1417528 2128331 := bstep (se 1 (by rfl) ⟨1596248, by rfl⟩ : syracuseStep 2128331 = 3192497) B3192497
theorem B2128343 : Blo 1417528 2128343 := bstep (se 1 (by rfl) ⟨1596257, by rfl⟩ : syracuseStep 2128343 = 3192515) B3192515
theorem B3029491 : Blo 1417528 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B9091601 : Blo 1417528 9091601 := bstep (se 2 (by rfl) ⟨3409350, by rfl⟩ : syracuseStep 9091601 = 6818701) B6818701
theorem B2128409 : Blo 1417528 2128409 := bstep (se 2 (by rfl) ⟨798153, by rfl⟩ : syracuseStep 2128409 = 1596307) B1596307
theorem B1595947 : Blo 1417528 1595947 := bstep (se 1 (by rfl) ⟨1196960, by rfl⟩ : syracuseStep 1595947 = 2393921) B2393921
theorem B5388875 : Blo 1417528 5388875 := bstep (se 1 (by rfl) ⟨4041656, by rfl⟩ : syracuseStep 5388875 = 8083313) B8083313
theorem B5388889 : Blo 1417528 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B3193433 : Blo 1417528 3193433 := bstep (se 2 (by rfl) ⟨1197537, by rfl⟩ : syracuseStep 3193433 = 2395075) B2395075
theorem B16153181 : Blo 1417528 16153181 := bstep (se 3 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 16153181 = 6057443) B6057443
theorem B2128523 : Blo 1417528 2128523 := bstep (se 1 (by rfl) ⟨1596392, by rfl⟩ : syracuseStep 2128523 = 3192785) B3192785
theorem B2554519 : Blo 1417528 2554519 := bstep (se 1 (by rfl) ⟨1915889, by rfl⟩ : syracuseStep 2554519 = 3831779) B3831779
theorem B1596055 : Blo 1417528 1596055 := bstep (se 1 (by rfl) ⟨1197041, by rfl⟩ : syracuseStep 1596055 = 2394083) B2394083
theorem B2128535 : Blo 1417528 2128535 := bstep (se 1 (by rfl) ⟨1596401, by rfl⟩ : syracuseStep 2128535 = 3192803) B3192803
theorem B3193523 : Blo 1417528 3193523 := bstep (se 1 (by rfl) ⟨2395142, by rfl⟩ : syracuseStep 3193523 = 4790285) B4790285
theorem B3193559 : Blo 1417528 3193559 := bstep (se 1 (by rfl) ⟨2395169, by rfl⟩ : syracuseStep 3193559 = 4790339) B4790339
theorem B2128601 : Blo 1417528 2128601 := bstep (se 2 (by rfl) ⟨798225, by rfl⟩ : syracuseStep 2128601 = 1596451) B1596451
theorem B10771217 : Blo 1417528 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B6060845 : Blo 1417528 6060845 := bstep (se 3 (by rfl) ⟨1136408, by rfl⟩ : syracuseStep 6060845 = 2272817) B2272817
theorem B1596235 : Blo 1417528 1596235 := bstep (se 1 (by rfl) ⟨1197176, by rfl⟩ : syracuseStep 1596235 = 2394353) B2394353
theorem B2128715 : Blo 1417528 2128715 := bstep (se 1 (by rfl) ⟨1596536, by rfl⟩ : syracuseStep 2128715 = 3193073) B3193073
theorem B2128727 : Blo 1417528 2128727 := bstep (se 1 (by rfl) ⟨1596545, by rfl⟩ : syracuseStep 2128727 = 3193091) B3193091
theorem B4037465 : Blo 1417528 4037465 := bstep (se 2 (by rfl) ⟨1514049, by rfl⟩ : syracuseStep 4037465 = 3028099) B3028099
theorem B3193739 : Blo 1417528 3193739 := bstep (se 1 (by rfl) ⟨2395304, by rfl⟩ : syracuseStep 3193739 = 4790609) B4790609
theorem B2128793 : Blo 1417528 2128793 := bstep (se 2 (by rfl) ⟨798297, by rfl⟩ : syracuseStep 2128793 = 1596595) B1596595
theorem B1596343 : Blo 1417528 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B3193793 : Blo 1417528 3193793 := bstep (se 2 (by rfl) ⟨1197672, by rfl⟩ : syracuseStep 3193793 = 2395345) B2395345
theorem B2128907 : Blo 1417528 2128907 := bstep (se 1 (by rfl) ⟨1596680, by rfl⟩ : syracuseStep 2128907 = 3193361) B3193361
theorem B2128919 : Blo 1417528 2128919 := bstep (se 1 (by rfl) ⟨1596689, by rfl⟩ : syracuseStep 2128919 = 3193379) B3193379
theorem B2128985 : Blo 1417528 2128985 := bstep (se 2 (by rfl) ⟨798369, by rfl⟩ : syracuseStep 2128985 = 1596739) B1596739
theorem B1596523 : Blo 1417528 1596523 := bstep (se 1 (by rfl) ⟨1197392, by rfl⟩ : syracuseStep 1596523 = 2394785) B2394785
theorem B2694323 : Blo 1417528 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B2129099 : Blo 1417528 2129099 := bstep (se 1 (by rfl) ⟨1596824, by rfl⟩ : syracuseStep 2129099 = 3193649) B3193649
theorem B1596631 : Blo 1417528 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B2129111 : Blo 1417528 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B2129177 : Blo 1417528 2129177 := bstep (se 2 (by rfl) ⟨798441, by rfl⟩ : syracuseStep 2129177 = 1596883) B1596883
theorem B3407179 : Blo 1417528 3407179 := bstep (se 1 (by rfl) ⟨2555384, by rfl⟩ : syracuseStep 3407179 = 5110769) B5110769
theorem B2694475 : Blo 1417528 2694475 := bstep (se 1 (by rfl) ⟨2020856, by rfl⟩ : syracuseStep 2694475 = 4041713) B4041713
theorem B4603225 : Blo 1417528 4603225 := bstep (se 2 (by rfl) ⟨1726209, by rfl⟩ : syracuseStep 4603225 = 3452419) B3452419
theorem B1596811 : Blo 1417528 1596811 := bstep (se 1 (by rfl) ⟨1197608, by rfl⟩ : syracuseStep 1596811 = 2395217) B2395217
theorem B2129291 : Blo 1417528 2129291 := bstep (se 1 (by rfl) ⟨1596968, by rfl⟩ : syracuseStep 2129291 = 3193937) B3193937
theorem B1916311 : Blo 1417528 1916311 := bstep (se 1 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 1916311 = 2874467) B2874467
theorem B1596919 : Blo 1417528 1596919 := bstep (se 1 (by rfl) ⟨1197689, by rfl⟩ : syracuseStep 1596919 = 2395379) B2395379
theorem B1515019 : Blo 1417528 1515019 := bstep (se 1 (by rfl) ⟨1136264, by rfl⟩ : syracuseStep 1515019 = 2272529) B2272529
theorem B37330445 : Blo 1417528 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B7183889 : Blo 1417528 7183889 := bstep (se 2 (by rfl) ⟨2693958, by rfl⟩ : syracuseStep 7183889 = 5387917) B5387917
theorem B2555543 : Blo 1417528 2555543 := bstep (se 1 (by rfl) ⟨1916657, by rfl⟩ : syracuseStep 2555543 = 3833315) B3833315
theorem B2694809 : Blo 1417528 2694809 := bstep (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) B2021107
theorem B7184051 : Blo 1417528 7184051 := bstep (se 1 (by rfl) ⟨5388038, by rfl⟩ : syracuseStep 7184051 = 10776077) B10776077
theorem B5750489 : Blo 1417528 5750489 := bstep (se 2 (by rfl) ⟨2156433, by rfl⟩ : syracuseStep 5750489 = 4312867) B4312867
theorem B3235673 : Blo 1417528 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B3407795 : Blo 1417528 3407795 := bstep (se 1 (by rfl) ⟨2555846, by rfl⟩ : syracuseStep 3407795 = 5111693) B5111693
theorem B3030977 : Blo 1417528 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B11509771 : Blo 1417528 11509771 := bstep (se 1 (by rfl) ⟨8632328, by rfl⟩ : syracuseStep 11509771 = 17264657) B17264657
theorem B5537803 : Blo 1417528 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B3235855 : Blo 1417528 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B24231959 : Blo 1417528 24231959 := bstep (se 1 (by rfl) ⟨18173969, by rfl⟩ : syracuseStep 24231959 = 36347939) B36347939
theorem B4096061 : Blo 1417528 4096061 := bstep (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) B1536023
theorem B3031175 : Blo 1417528 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B3637505 : Blo 1417528 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B4038923 : Blo 1417528 4038923 := bstep (se 1 (by rfl) ⟨3029192, by rfl⟩ : syracuseStep 4038923 = 6058385) B6058385
theorem B4784399 : Blo 1417528 4784399 := bstep (se 1 (by rfl) ⟨3588299, by rfl⟩ : syracuseStep 4784399 = 7176599) B7176599
theorem B1417531 : Blo 1417528 1417531 := bstep (se 1 (by rfl) ⟨1063148, by rfl⟩ : syracuseStep 1417531 = 2126297) B2126297
theorem B9085243 : Blo 1417528 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B7184699 : Blo 1417528 7184699 := bstep (se 1 (by rfl) ⟨5388524, by rfl⟩ : syracuseStep 7184699 = 10777049) B10777049
theorem B141844853 : Blo 1417528 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B1417607 : Blo 1417528 1417607 := bstep (se 1 (by rfl) ⟨1063205, by rfl⟩ : syracuseStep 1417607 = 2126411) B2126411
theorem B8184199 : Blo 1417528 8184199 := bstep (se 1 (by rfl) ⟨6138149, by rfl⟩ : syracuseStep 8184199 = 12276299) B12276299
theorem B1417615 : Blo 1417528 1417615 := bstep (se 1 (by rfl) ⟨1063211, by rfl⟩ : syracuseStep 1417615 = 2126423) B2126423
theorem B2556307 : Blo 1417528 2556307 := bstep (se 1 (by rfl) ⟨1917230, by rfl⟩ : syracuseStep 2556307 = 3834461) B3834461
theorem B1417659 : Blo 1417528 1417659 := bstep (se 1 (by rfl) ⟨1063244, by rfl⟩ : syracuseStep 1417659 = 2126489) B2126489
theorem B7184861 : Blo 1417528 7184861 := bstep (se 3 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 7184861 = 2694323) B2694323
theorem B1417735 : Blo 1417528 1417735 := bstep (se 1 (by rfl) ⟨1063301, by rfl⟩ : syracuseStep 1417735 = 2126603) B2126603
theorem B1417743 : Blo 1417528 1417743 := bstep (se 1 (by rfl) ⟨1063307, by rfl⟩ : syracuseStep 1417743 = 2126615) B2126615
theorem B2392591 : Blo 1417528 2392591 := bstep (se 1 (by rfl) ⟨1794443, by rfl⟩ : syracuseStep 2392591 = 3588887) B3588887
theorem B1794575 : Blo 1417528 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B4784669 : Blo 1417528 4784669 := bstep (se 3 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 4784669 = 1794251) B1794251
theorem B1417787 : Blo 1417528 1417787 := bstep (se 1 (by rfl) ⟨1063340, by rfl⟩ : syracuseStep 1417787 = 2126681) B2126681
theorem B24240707 : Blo 1417528 24240707 := bstep (se 1 (by rfl) ⟨18180530, by rfl⟩ : syracuseStep 24240707 = 36361061) B36361061
theorem B3588695 : Blo 1417528 3588695 := bstep (se 1 (by rfl) ⟨2691521, by rfl⟩ : syracuseStep 3588695 = 5383043) B5383043
theorem B2876023 : Blo 1417528 2876023 := bstep (se 1 (by rfl) ⟨2157017, by rfl⟩ : syracuseStep 2876023 = 4314035) B4314035
theorem B1417863 : Blo 1417528 1417863 := bstep (se 1 (by rfl) ⟨1063397, by rfl⟩ : syracuseStep 1417863 = 2126795) B2126795
theorem B1417871 : Blo 1417528 1417871 := bstep (se 1 (by rfl) ⟨1063403, by rfl⟩ : syracuseStep 1417871 = 2126807) B2126807
theorem B4039321 : Blo 1417528 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B1417915 : Blo 1417528 1417915 := bstep (se 1 (by rfl) ⟨1063436, by rfl⟩ : syracuseStep 1417915 = 2126873) B2126873
theorem B1417991 : Blo 1417528 1417991 := bstep (se 1 (by rfl) ⟨1063493, by rfl⟩ : syracuseStep 1417991 = 2126987) B2126987
theorem B1417999 : Blo 1417528 1417999 := bstep (se 1 (by rfl) ⟨1063499, by rfl⟩ : syracuseStep 1417999 = 2126999) B2126999
theorem B7185185 : Blo 1417528 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B94610213 : Blo 1417528 94610213 := bstep (se 4 (by rfl) ⟨8869707, by rfl⟩ : syracuseStep 94610213 = 17739415) B17739415
theorem B3588907 : Blo 1417528 3588907 := bstep (se 1 (by rfl) ⟨2691680, by rfl⟩ : syracuseStep 3588907 = 5383361) B5383361
theorem B1418043 : Blo 1417528 1418043 := bstep (se 1 (by rfl) ⟨1063532, by rfl⟩ : syracuseStep 1418043 = 2127065) B2127065
theorem B1418119 : Blo 1417528 1418119 := bstep (se 1 (by rfl) ⟨1063589, by rfl⟩ : syracuseStep 1418119 = 2127179) B2127179
theorem B1418127 : Blo 1417528 1418127 := bstep (se 1 (by rfl) ⟨1063595, by rfl⟩ : syracuseStep 1418127 = 2127191) B2127191
theorem B4039571 : Blo 1417528 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B3589049 : Blo 1417528 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1418171 : Blo 1417528 1418171 := bstep (se 1 (by rfl) ⟨1063628, by rfl⟩ : syracuseStep 1418171 = 2127257) B2127257
theorem B1418247 : Blo 1417528 1418247 := bstep (se 1 (by rfl) ⟨1063685, by rfl⟩ : syracuseStep 1418247 = 2127371) B2127371
theorem B1418255 : Blo 1417528 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B2393131 : Blo 1417528 2393131 := bstep (se 1 (by rfl) ⟨1794848, by rfl⟩ : syracuseStep 2393131 = 3589697) B3589697
theorem B1418299 : Blo 1417528 1418299 := bstep (se 1 (by rfl) ⟨1063724, by rfl⟩ : syracuseStep 1418299 = 2127449) B2127449
theorem B8627267 : Blo 1417528 8627267 := bstep (se 1 (by rfl) ⟨6470450, by rfl⟩ : syracuseStep 8627267 = 12940901) B12940901
theorem B1418375 : Blo 1417528 1418375 := bstep (se 1 (by rfl) ⟨1063781, by rfl⟩ : syracuseStep 1418375 = 2127563) B2127563
theorem B1418383 : Blo 1417528 1418383 := bstep (se 1 (by rfl) ⟨1063787, by rfl⟩ : syracuseStep 1418383 = 2127575) B2127575
theorem B2393273 : Blo 1417528 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B1418427 : Blo 1417528 1418427 := bstep (se 1 (by rfl) ⟨1063820, by rfl⟩ : syracuseStep 1418427 = 2127641) B2127641
theorem B7177409 : Blo 1417528 7177409 := bstep (se 2 (by rfl) ⟨2691528, by rfl⟩ : syracuseStep 7177409 = 5383057) B5383057
theorem B1418503 : Blo 1417528 1418503 := bstep (se 1 (by rfl) ⟨1063877, by rfl⟩ : syracuseStep 1418503 = 2127755) B2127755
theorem B1418511 : Blo 1417528 1418511 := bstep (se 1 (by rfl) ⟨1063883, by rfl⟩ : syracuseStep 1418511 = 2127767) B2127767
theorem B2876705 : Blo 1417528 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B1418555 : Blo 1417528 1418555 := bstep (se 1 (by rfl) ⟨1063916, by rfl⟩ : syracuseStep 1418555 = 2127833) B2127833
theorem B1418631 : Blo 1417528 1418631 := bstep (se 1 (by rfl) ⟨1063973, by rfl⟩ : syracuseStep 1418631 = 2127947) B2127947
theorem B1418639 : Blo 1417528 1418639 := bstep (se 1 (by rfl) ⟨1063979, by rfl⟩ : syracuseStep 1418639 = 2127959) B2127959
theorem B1418683 : Blo 1417528 1418683 := bstep (se 1 (by rfl) ⟨1064012, by rfl⟩ : syracuseStep 1418683 = 2128025) B2128025
theorem B2156039 : Blo 1417528 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B1418759 : Blo 1417528 1418759 := bstep (se 1 (by rfl) ⟨1064069, by rfl⟩ : syracuseStep 1418759 = 2128139) B2128139
theorem B4851211 : Blo 1417528 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B1418767 : Blo 1417528 1418767 := bstep (se 1 (by rfl) ⟨1064075, by rfl⟩ : syracuseStep 1418767 = 2128151) B2128151
theorem B1418811 : Blo 1417528 1418811 := bstep (se 1 (by rfl) ⟨1064108, by rfl⟩ : syracuseStep 1418811 = 2128217) B2128217
theorem B1418887 : Blo 1417528 1418887 := bstep (se 1 (by rfl) ⟨1064165, by rfl⟩ : syracuseStep 1418887 = 2128331) B2128331
theorem B1418895 : Blo 1417528 1418895 := bstep (se 1 (by rfl) ⟨1064171, by rfl⟩ : syracuseStep 1418895 = 2128343) B2128343
theorem B1418939 : Blo 1417528 1418939 := bstep (se 1 (by rfl) ⟨1064204, by rfl⟩ : syracuseStep 1418939 = 2128409) B2128409
theorem B7186157 : Blo 1417528 7186157 := bstep (se 3 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 7186157 = 2694809) B2694809
theorem B1419015 : Blo 1417528 1419015 := bstep (se 1 (by rfl) ⟨1064261, by rfl⟩ : syracuseStep 1419015 = 2128523) B2128523
theorem B1419023 : Blo 1417528 1419023 := bstep (se 1 (by rfl) ⟨1064267, by rfl⟩ : syracuseStep 1419023 = 2128535) B2128535
theorem B6145807 : Blo 1417528 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B6137633 : Blo 1417528 6137633 := bstep (se 2 (by rfl) ⟨2301612, by rfl⟩ : syracuseStep 6137633 = 4603225) B4603225
theorem B1419067 : Blo 1417528 1419067 := bstep (se 1 (by rfl) ⟨1064300, by rfl⟩ : syracuseStep 1419067 = 2128601) B2128601
theorem B4040563 : Blo 1417528 4040563 := bstep (se 1 (by rfl) ⟨3030422, by rfl⟩ : syracuseStep 4040563 = 6060845) B6060845
theorem B2393975 : Blo 1417528 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B1419143 : Blo 1417528 1419143 := bstep (se 1 (by rfl) ⟨1064357, by rfl⟩ : syracuseStep 1419143 = 2128715) B2128715
theorem B1419151 : Blo 1417528 1419151 := bstep (se 1 (by rfl) ⟨1064363, by rfl⟩ : syracuseStep 1419151 = 2128727) B2128727
theorem B34498457 : Blo 1417528 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B4786073 : Blo 1417528 4786073 := bstep (se 2 (by rfl) ⟨1794777, by rfl⟩ : syracuseStep 4786073 = 3589555) B3589555
theorem B3590041 : Blo 1417528 3590041 := bstep (se 2 (by rfl) ⟨1346265, by rfl⟩ : syracuseStep 3590041 = 2692531) B2692531
theorem B1419195 : Blo 1417528 1419195 := bstep (se 1 (by rfl) ⟨1064396, by rfl⟩ : syracuseStep 1419195 = 2128793) B2128793
theorem B1419271 : Blo 1417528 1419271 := bstep (se 1 (by rfl) ⟨1064453, by rfl⟩ : syracuseStep 1419271 = 2128907) B2128907
theorem B8079371 : Blo 1417528 8079371 := bstep (se 1 (by rfl) ⟨6059528, by rfl⟩ : syracuseStep 8079371 = 12119057) B12119057
theorem B1419279 : Blo 1417528 1419279 := bstep (se 1 (by rfl) ⟨1064459, by rfl⟩ : syracuseStep 1419279 = 2128919) B2128919
theorem B3590203 : Blo 1417528 3590203 := bstep (se 1 (by rfl) ⟨2692652, by rfl⟩ : syracuseStep 3590203 = 5385305) B5385305
theorem B13625405 : Blo 1417528 13625405 := bstep (se 3 (by rfl) ⟨2554763, by rfl⟩ : syracuseStep 13625405 = 5109527) B5109527
theorem B1419323 : Blo 1417528 1419323 := bstep (se 1 (by rfl) ⟨1064492, by rfl⟩ : syracuseStep 1419323 = 2128985) B2128985
theorem B1419399 : Blo 1417528 1419399 := bstep (se 1 (by rfl) ⟨1064549, by rfl⟩ : syracuseStep 1419399 = 2129099) B2129099
theorem B1419407 : Blo 1417528 1419407 := bstep (se 1 (by rfl) ⟨1064555, by rfl⟩ : syracuseStep 1419407 = 2129111) B2129111
theorem B1419451 : Blo 1417528 1419451 := bstep (se 1 (by rfl) ⟨1064588, by rfl⟩ : syracuseStep 1419451 = 2129177) B2129177
theorem B3590345 : Blo 1417528 3590345 := bstep (se 2 (by rfl) ⟨1346379, by rfl⟩ : syracuseStep 3590345 = 2692759) B2692759
theorem B3836105 : Blo 1417528 3836105 := bstep (se 2 (by rfl) ⟨1438539, by rfl⟩ : syracuseStep 3836105 = 2877079) B2877079
theorem B1419527 : Blo 1417528 1419527 := bstep (se 1 (by rfl) ⟨1064645, by rfl⟩ : syracuseStep 1419527 = 2129291) B2129291
theorem B2394427 : Blo 1417528 2394427 := bstep (se 1 (by rfl) ⟨1795820, by rfl⟩ : syracuseStep 2394427 = 3591641) B3591641
theorem B6818201 : Blo 1417528 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B2394569 : Blo 1417528 2394569 := bstep (se 2 (by rfl) ⟨897963, by rfl⟩ : syracuseStep 2394569 = 1795927) B1795927
theorem B7178705 : Blo 1417528 7178705 := bstep (se 2 (by rfl) ⟨2692014, by rfl⟩ : syracuseStep 7178705 = 5384029) B5384029
theorem B22432241 : Blo 1417528 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B3590689 : Blo 1417528 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B27265571 : Blo 1417528 27265571 := bstep (se 1 (by rfl) ⟨20449178, by rfl⟩ : syracuseStep 27265571 = 40898357) B40898357
theorem B2157115 : Blo 1417528 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B4786775 : Blo 1417528 4786775 := bstep (se 1 (by rfl) ⟨3590081, by rfl⟩ : syracuseStep 4786775 = 7180163) B7180163
theorem B2271863 : Blo 1417528 2271863 := bstep (se 1 (by rfl) ⟨1703897, by rfl⟩ : syracuseStep 2271863 = 3407795) B3407795
theorem B3189563 : Blo 1417528 3189563 := bstep (se 1 (by rfl) ⟨2392172, by rfl⟩ : syracuseStep 3189563 = 4784345) B4784345
theorem B16157555 : Blo 1417528 16157555 := bstep (se 1 (by rfl) ⟨12118166, by rfl⟩ : syracuseStep 16157555 = 24236333) B24236333
theorem B3189689 : Blo 1417528 3189689 := bstep (se 2 (by rfl) ⟨1196133, by rfl⟩ : syracuseStep 3189689 = 2392267) B2392267
theorem B4787261 : Blo 1417528 4787261 := bstep (se 3 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 4787261 = 1795223) B1795223
theorem B3836989 : Blo 1417528 3836989 := bstep (se 3 (by rfl) ⟨719435, by rfl⟩ : syracuseStep 3836989 = 1438871) B1438871
theorem B3591287 : Blo 1417528 3591287 := bstep (se 1 (by rfl) ⟨2693465, by rfl⟩ : syracuseStep 3591287 = 5386931) B5386931
theorem B2395271 : Blo 1417528 2395271 := bstep (se 1 (by rfl) ⟨1796453, by rfl⟩ : syracuseStep 2395271 = 3592907) B3592907
theorem B8621257 : Blo 1417528 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B5385473 : Blo 1417528 5385473 := bstep (se 2 (by rfl) ⟨2019552, by rfl⟩ : syracuseStep 5385473 = 4039105) B4039105
theorem B2018567 : Blo 1417528 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B3190031 : Blo 1417528 3190031 := bstep (se 1 (by rfl) ⟨2392523, by rfl⟩ : syracuseStep 3190031 = 4785047) B4785047
theorem B5385487 : Blo 1417528 5385487 := bstep (se 1 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 5385487 = 8078231) B8078231
theorem B3190049 : Blo 1417528 3190049 := bstep (se 2 (by rfl) ⟨1196268, by rfl⟩ : syracuseStep 3190049 = 2392537) B2392537
theorem B3280187 : Blo 1417528 3280187 := bstep (se 1 (by rfl) ⟨2460140, by rfl⟩ : syracuseStep 3280187 = 4920281) B4920281
theorem B4042169 : Blo 1417528 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B37842385 : Blo 1417528 37842385 := bstep (se 2 (by rfl) ⟨14190894, by rfl⟩ : syracuseStep 37842385 = 28381789) B28381789
theorem B3190391 : Blo 1417528 3190391 := bstep (se 1 (by rfl) ⟨2392793, by rfl⟩ : syracuseStep 3190391 = 4785587) B4785587
theorem B2731639 : Blo 1417528 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B4312723 : Blo 1417528 4312723 := bstep (se 1 (by rfl) ⟨3234542, by rfl⟩ : syracuseStep 4312723 = 6469085) B6469085
theorem B24227585 : Blo 1417528 24227585 := bstep (se 2 (by rfl) ⟨9085344, by rfl⟩ : syracuseStep 24227585 = 18170689) B18170689
theorem B3190571 : Blo 1417528 3190571 := bstep (se 1 (by rfl) ⟨2392928, by rfl⟩ : syracuseStep 3190571 = 4785857) B4785857
theorem B13627403 : Blo 1417528 13627403 := bstep (se 1 (by rfl) ⟨10220552, by rfl⟩ : syracuseStep 13627403 = 20441105) B20441105
theorem B3190931 : Blo 1417528 3190931 := bstep (se 1 (by rfl) ⟨2393198, by rfl⟩ : syracuseStep 3190931 = 4786397) B4786397
theorem B3190985 : Blo 1417528 3190985 := bstep (se 2 (by rfl) ⟨1196619, by rfl⟩ : syracuseStep 3190985 = 2393239) B2393239
theorem B3592583 : Blo 1417528 3592583 := bstep (se 1 (by rfl) ⟨2694437, by rfl⟩ : syracuseStep 3592583 = 5388875) B5388875
theorem B1536391 : Blo 1417528 1536391 := bstep (se 1 (by rfl) ⟨1152293, by rfl⟩ : syracuseStep 1536391 = 2304587) B2304587
theorem B10768787 : Blo 1417528 10768787 := bstep (se 1 (by rfl) ⟨8076590, by rfl⟩ : syracuseStep 10768787 = 16153181) B16153181
theorem B4542905 : Blo 1417528 4542905 := bstep (se 2 (by rfl) ⟨1703589, by rfl⟩ : syracuseStep 4542905 = 3407179) B3407179
theorem B4788665 : Blo 1417528 4788665 := bstep (se 2 (by rfl) ⟨1795749, by rfl⟩ : syracuseStep 4788665 = 3591499) B3591499
theorem B3592633 : Blo 1417528 3592633 := bstep (se 2 (by rfl) ⟨1347237, by rfl⟩ : syracuseStep 3592633 = 2694475) B2694475
theorem B2126327 : Blo 1417528 2126327 := bstep (se 1 (by rfl) ⟨1594745, by rfl⟩ : syracuseStep 2126327 = 3189491) B3189491
theorem B7180811 : Blo 1417528 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B5386763 : Blo 1417528 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B2126351 : Blo 1417528 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B2126393 : Blo 1417528 2126393 := bstep (se 2 (by rfl) ⟨797397, by rfl⟩ : syracuseStep 2126393 = 1594795) B1594795
theorem B2691643 : Blo 1417528 2691643 := bstep (se 1 (by rfl) ⟨2018732, by rfl⟩ : syracuseStep 2691643 = 4037465) B4037465
theorem B2126471 : Blo 1417528 2126471 := bstep (se 1 (by rfl) ⟨1594853, by rfl⟩ : syracuseStep 2126471 = 3189707) B3189707
theorem B2126507 : Blo 1417528 2126507 := bstep (se 1 (by rfl) ⟨1594880, by rfl⟩ : syracuseStep 2126507 = 3189761) B3189761
theorem B7180973 : Blo 1417528 7180973 := bstep (se 3 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 7180973 = 2692865) B2692865
theorem B2020025 : Blo 1417528 2020025 := bstep (se 2 (by rfl) ⟨757509, by rfl⟩ : syracuseStep 2020025 = 1515019) B1515019
theorem B2126537 : Blo 1417528 2126537 := bstep (se 2 (by rfl) ⟨797451, by rfl⟩ : syracuseStep 2126537 = 1594903) B1594903
theorem B2126651 : Blo 1417528 2126651 := bstep (se 1 (by rfl) ⟨1594988, by rfl⟩ : syracuseStep 2126651 = 3189977) B3189977
theorem B24245081 : Blo 1417528 24245081 := bstep (se 2 (by rfl) ⟨9091905, by rfl⟩ : syracuseStep 24245081 = 18183811) B18183811
theorem B2126711 : Blo 1417528 2126711 := bstep (se 1 (by rfl) ⟨1595033, by rfl⟩ : syracuseStep 2126711 = 3190067) B3190067
theorem B3191687 : Blo 1417528 3191687 := bstep (se 1 (by rfl) ⟨2393765, by rfl⟩ : syracuseStep 3191687 = 4787531) B4787531
theorem B2126735 : Blo 1417528 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B2126777 : Blo 1417528 2126777 := bstep (se 2 (by rfl) ⟨797541, by rfl⟩ : syracuseStep 2126777 = 1595083) B1595083
theorem B2126855 : Blo 1417528 2126855 := bstep (se 1 (by rfl) ⟨1595141, by rfl⟩ : syracuseStep 2126855 = 3190283) B3190283
theorem B4789259 : Blo 1417528 4789259 := bstep (se 1 (by rfl) ⟨3591944, by rfl⟩ : syracuseStep 4789259 = 7183889) B7183889
theorem B2692129 : Blo 1417528 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B5321771 : Blo 1417528 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B2126891 : Blo 1417528 2126891 := bstep (se 1 (by rfl) ⟨1595168, by rfl⟩ : syracuseStep 2126891 = 3190337) B3190337
theorem B3191867 : Blo 1417528 3191867 := bstep (se 1 (by rfl) ⟨2393900, by rfl⟩ : syracuseStep 3191867 = 4787801) B4787801
theorem B6059069 : Blo 1417528 6059069 := bstep (se 3 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 6059069 = 2272151) B2272151
theorem B2126921 : Blo 1417528 2126921 := bstep (se 2 (by rfl) ⟨797595, by rfl⟩ : syracuseStep 2126921 = 1595191) B1595191
theorem B4789367 : Blo 1417528 4789367 := bstep (se 1 (by rfl) ⟨3592025, by rfl⟩ : syracuseStep 4789367 = 7184051) B7184051
theorem B8082605 : Blo 1417528 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B3191993 : Blo 1417528 3191993 := bstep (se 2 (by rfl) ⟨1196997, by rfl⟩ : syracuseStep 3191993 = 2393995) B2393995
theorem B2127035 : Blo 1417528 2127035 := bstep (se 1 (by rfl) ⟨1595276, by rfl⟩ : syracuseStep 2127035 = 3190553) B3190553
theorem B2127095 : Blo 1417528 2127095 := bstep (se 1 (by rfl) ⟨1595321, by rfl⟩ : syracuseStep 2127095 = 3190643) B3190643
theorem B2127119 : Blo 1417528 2127119 := bstep (se 1 (by rfl) ⟨1595339, by rfl⟩ : syracuseStep 2127119 = 3190679) B3190679
theorem B6141199 : Blo 1417528 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B2127161 : Blo 1417528 2127161 := bstep (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) B1595371
theorem B1594759 : Blo 1417528 1594759 := bstep (se 1 (by rfl) ⟨1196069, by rfl⟩ : syracuseStep 1594759 = 2392139) B2392139
theorem B2127239 : Blo 1417528 2127239 := bstep (se 1 (by rfl) ⟨1595429, by rfl⟩ : syracuseStep 2127239 = 3190859) B3190859
theorem B2127275 : Blo 1417528 2127275 := bstep (se 1 (by rfl) ⟨1595456, by rfl⟩ : syracuseStep 2127275 = 3190913) B3190913
theorem B5387705 : Blo 1417528 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B2127305 : Blo 1417528 2127305 := bstep (se 2 (by rfl) ⟨797739, by rfl⟩ : syracuseStep 2127305 = 1595479) B1595479
theorem B3192335 : Blo 1417528 3192335 := bstep (se 1 (by rfl) ⟨2394251, by rfl⟩ : syracuseStep 3192335 = 4788503) B4788503
theorem B2020879 : Blo 1417528 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B4609565 : Blo 1417528 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B3192353 : Blo 1417528 3192353 := bstep (se 2 (by rfl) ⟨1197132, by rfl⟩ : syracuseStep 3192353 = 2394265) B2394265
theorem B1594939 : Blo 1417528 1594939 := bstep (se 1 (by rfl) ⟨1196204, by rfl⟩ : syracuseStep 1594939 = 2392409) B2392409
theorem B2127419 : Blo 1417528 2127419 := bstep (se 1 (by rfl) ⟨1595564, by rfl⟩ : syracuseStep 2127419 = 3191129) B3191129
theorem B46003787 : Blo 1417528 46003787 := bstep (se 1 (by rfl) ⟨34502840, by rfl⟩ : syracuseStep 46003787 = 69005681) B69005681
theorem B32773733 : Blo 1417528 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B2127479 : Blo 1417528 2127479 := bstep (se 1 (by rfl) ⟨1595609, by rfl⟩ : syracuseStep 2127479 = 3191219) B3191219
theorem B2127503 : Blo 1417528 2127503 := bstep (se 1 (by rfl) ⟨1595627, by rfl⟩ : syracuseStep 2127503 = 3191255) B3191255
theorem B2127545 : Blo 1417528 2127545 := bstep (se 2 (by rfl) ⟨797829, by rfl⟩ : syracuseStep 2127545 = 1595659) B1595659
theorem B4789961 : Blo 1417528 4789961 := bstep (se 2 (by rfl) ⟨1796235, by rfl⟩ : syracuseStep 4789961 = 3592471) B3592471
theorem B7673545 : Blo 1417528 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B2127623 : Blo 1417528 2127623 := bstep (se 1 (by rfl) ⟨1595717, by rfl⟩ : syracuseStep 2127623 = 3191435) B3191435
theorem B2127659 : Blo 1417528 2127659 := bstep (se 1 (by rfl) ⟨1595744, by rfl⟩ : syracuseStep 2127659 = 3191489) B3191489
theorem B11663153 : Blo 1417528 11663153 := bstep (se 2 (by rfl) ⟨4373682, by rfl⟩ : syracuseStep 11663153 = 8747365) B8747365
theorem B8189747 : Blo 1417528 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B2127689 : Blo 1417528 2127689 := bstep (se 2 (by rfl) ⟨797883, by rfl⟩ : syracuseStep 2127689 = 1595767) B1595767
theorem B3192695 : Blo 1417528 3192695 := bstep (se 1 (by rfl) ⟨2394521, by rfl⟩ : syracuseStep 3192695 = 4789043) B4789043
theorem B2127803 : Blo 1417528 2127803 := bstep (se 1 (by rfl) ⟨1595852, by rfl⟩ : syracuseStep 2127803 = 3191705) B3191705
theorem B2127863 : Blo 1417528 2127863 := bstep (se 1 (by rfl) ⟨1595897, by rfl⟩ : syracuseStep 2127863 = 3191795) B3191795
theorem B1595407 : Blo 1417528 1595407 := bstep (se 1 (by rfl) ⟨1196555, by rfl⟩ : syracuseStep 1595407 = 2393111) B2393111
theorem B2127887 : Blo 1417528 2127887 := bstep (se 1 (by rfl) ⟨1595915, by rfl⟩ : syracuseStep 2127887 = 3191831) B3191831
theorem B3192875 : Blo 1417528 3192875 := bstep (se 1 (by rfl) ⟨2394656, by rfl⟩ : syracuseStep 3192875 = 4789313) B4789313
theorem B2127929 : Blo 1417528 2127929 := bstep (se 2 (by rfl) ⟨797973, by rfl⟩ : syracuseStep 2127929 = 1595947) B1595947
theorem B2128007 : Blo 1417528 2128007 := bstep (se 1 (by rfl) ⟨1596005, by rfl⟩ : syracuseStep 2128007 = 3192011) B3192011
theorem B3233939 : Blo 1417528 3233939 := bstep (se 1 (by rfl) ⟨2425454, by rfl⟩ : syracuseStep 3233939 = 4850909) B4850909
theorem B2128043 : Blo 1417528 2128043 := bstep (se 1 (by rfl) ⟨1596032, by rfl⟩ : syracuseStep 2128043 = 3192065) B3192065
theorem B3406025 : Blo 1417528 3406025 := bstep (se 2 (by rfl) ⟨1277259, by rfl⟩ : syracuseStep 3406025 = 2554519) B2554519
theorem B2693321 : Blo 1417528 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B2128073 : Blo 1417528 2128073 := bstep (se 2 (by rfl) ⟨798027, by rfl⟩ : syracuseStep 2128073 = 1596055) B1596055
theorem B7182593 : Blo 1417528 7182593 := bstep (se 2 (by rfl) ⟨2693472, by rfl⟩ : syracuseStep 7182593 = 5386945) B5386945
theorem B4315421 : Blo 1417528 4315421 := bstep (se 3 (by rfl) ⟨809141, by rfl⟩ : syracuseStep 4315421 = 1618283) B1618283
theorem B8083745 : Blo 1417528 8083745 := bstep (se 2 (by rfl) ⟨3031404, by rfl⟩ : syracuseStep 8083745 = 6062809) B6062809
theorem B2128187 : Blo 1417528 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B2128247 : Blo 1417528 2128247 := bstep (se 1 (by rfl) ⟨1596185, by rfl⟩ : syracuseStep 2128247 = 3192371) B3192371
theorem B17250691 : Blo 1417528 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B4790663 : Blo 1417528 4790663 := bstep (se 1 (by rfl) ⟨3592997, by rfl⟩ : syracuseStep 4790663 = 7185995) B7185995
theorem B2128271 : Blo 1417528 2128271 := bstep (se 1 (by rfl) ⟨1596203, by rfl⟩ : syracuseStep 2128271 = 3192407) B3192407
theorem B3193235 : Blo 1417528 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B2128313 : Blo 1417528 2128313 := bstep (se 2 (by rfl) ⟨798117, by rfl⟩ : syracuseStep 2128313 = 1596235) B1596235
theorem B3193289 : Blo 1417528 3193289 := bstep (se 2 (by rfl) ⟨1197483, by rfl⟩ : syracuseStep 3193289 = 2394967) B2394967
theorem B6912515 : Blo 1417528 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B1595911 : Blo 1417528 1595911 := bstep (se 1 (by rfl) ⟨1196933, by rfl⟩ : syracuseStep 1595911 = 2393867) B2393867
theorem B2128391 : Blo 1417528 2128391 := bstep (se 1 (by rfl) ⟨1596293, by rfl⟩ : syracuseStep 2128391 = 3192587) B3192587
theorem B2128427 : Blo 1417528 2128427 := bstep (se 1 (by rfl) ⟨1596320, by rfl⟩ : syracuseStep 2128427 = 3192641) B3192641
theorem B2128457 : Blo 1417528 2128457 := bstep (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) B1596343
theorem B1596091 : Blo 1417528 1596091 := bstep (se 1 (by rfl) ⟨1197068, by rfl⟩ : syracuseStep 1596091 = 2394137) B2394137
theorem B2128571 : Blo 1417528 2128571 := bstep (se 1 (by rfl) ⟨1596428, by rfl⟩ : syracuseStep 2128571 = 3192857) B3192857
theorem B2128631 : Blo 1417528 2128631 := bstep (se 1 (by rfl) ⟨1596473, by rfl⟩ : syracuseStep 2128631 = 3192947) B3192947
theorem B2128655 : Blo 1417528 2128655 := bstep (se 1 (by rfl) ⟨1596491, by rfl⟩ : syracuseStep 2128655 = 3192983) B3192983
theorem B2128697 : Blo 1417528 2128697 := bstep (se 2 (by rfl) ⟨798261, by rfl⟩ : syracuseStep 2128697 = 1596523) B1596523
theorem B17726323 : Blo 1417528 17726323 := bstep (se 1 (by rfl) ⟨13294742, by rfl⟩ : syracuseStep 17726323 = 26589485) B26589485
theorem B2128775 : Blo 1417528 2128775 := bstep (se 1 (by rfl) ⟨1596581, by rfl⟩ : syracuseStep 2128775 = 3193163) B3193163
theorem B2694035 : Blo 1417528 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B2128811 : Blo 1417528 2128811 := bstep (se 1 (by rfl) ⟨1596608, by rfl⟩ : syracuseStep 2128811 = 3193217) B3193217
theorem B2694073 : Blo 1417528 2694073 := bstep (se 2 (by rfl) ⟨1010277, by rfl⟩ : syracuseStep 2694073 = 2020555) B2020555
theorem B2128841 : Blo 1417528 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B4316105 : Blo 1417528 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B6061067 : Blo 1417528 6061067 := bstep (se 1 (by rfl) ⟨4545800, by rfl⟩ : syracuseStep 6061067 = 9091601) B9091601
theorem B4037647 : Blo 1417528 4037647 := bstep (se 1 (by rfl) ⟨3028235, by rfl⟩ : syracuseStep 4037647 = 6056471) B6056471
theorem B2874401 : Blo 1417528 2874401 := bstep (se 2 (by rfl) ⟨1077900, by rfl⟩ : syracuseStep 2874401 = 2155801) B2155801
theorem B7183403 : Blo 1417528 7183403 := bstep (se 1 (by rfl) ⟨5387552, by rfl⟩ : syracuseStep 7183403 = 10775105) B10775105
theorem B2128955 : Blo 1417528 2128955 := bstep (se 1 (by rfl) ⟨1596716, by rfl⟩ : syracuseStep 2128955 = 3193433) B3193433
theorem B2129015 : Blo 1417528 2129015 := bstep (se 1 (by rfl) ⟨1596761, by rfl⟩ : syracuseStep 2129015 = 3193523) B3193523
theorem B1596559 : Blo 1417528 1596559 := bstep (se 1 (by rfl) ⟨1197419, by rfl⟩ : syracuseStep 1596559 = 2394839) B2394839
theorem B2129039 : Blo 1417528 2129039 := bstep (se 1 (by rfl) ⟨1596779, by rfl⟩ : syracuseStep 2129039 = 3193559) B3193559
theorem B2129081 : Blo 1417528 2129081 := bstep (se 2 (by rfl) ⟨798405, by rfl⟩ : syracuseStep 2129081 = 1596811) B1596811
theorem B2555081 : Blo 1417528 2555081 := bstep (se 2 (by rfl) ⟨958155, by rfl⟩ : syracuseStep 2555081 = 1916311) B1916311
theorem B2129159 : Blo 1417528 2129159 := bstep (se 1 (by rfl) ⟨1596869, by rfl⟩ : syracuseStep 2129159 = 3193739) B3193739
theorem B4037921 : Blo 1417528 4037921 := bstep (se 2 (by rfl) ⟨1514220, by rfl⟩ : syracuseStep 4037921 = 3028441) B3028441
theorem B2129195 : Blo 1417528 2129195 := bstep (se 1 (by rfl) ⟨1596896, by rfl⟩ : syracuseStep 2129195 = 3193793) B3193793
theorem B2129225 : Blo 1417528 2129225 := bstep (se 2 (by rfl) ⟨798459, by rfl⟩ : syracuseStep 2129225 = 1596919) B1596919
theorem B1515143 : Blo 1417528 1515143 := bstep (se 1 (by rfl) ⟨1136357, by rfl⟩ : syracuseStep 1515143 = 2272715) B2272715
theorem B24886963 : Blo 1417528 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B1703695 : Blo 1417528 1703695 := bstep (se 1 (by rfl) ⟨1277771, by rfl⟩ : syracuseStep 1703695 = 2555543) B2555543
theorem B2301755 : Blo 1417528 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B3833659 : Blo 1417528 3833659 := bstep (se 1 (by rfl) ⟨2875244, by rfl⟩ : syracuseStep 3833659 = 5750489) B5750489
theorem B4546363 : Blo 1417528 4546363 := bstep (se 1 (by rfl) ⟨3409772, by rfl⟩ : syracuseStep 4546363 = 6819545) B6819545
theorem B9084935 : Blo 1417528 9084935 := bstep (se 1 (by rfl) ⟨6813701, by rfl⟩ : syracuseStep 9084935 = 13627403) B13627403
theorem B16154639 : Blo 1417528 16154639 := bstep (se 1 (by rfl) ⟨12115979, by rfl⟩ : syracuseStep 16154639 = 24231959) B24231959
theorem B20463941 : Blo 1417528 20463941 := bstep (se 4 (by rfl) ⟨1918494, by rfl⟩ : syracuseStep 20463941 = 3836989) B3836989
theorem B1417551 : Blo 1417528 1417551 := bstep (se 1 (by rfl) ⟨1063163, by rfl⟩ : syracuseStep 1417551 = 2126327) B2126327
theorem B1417567 : Blo 1417528 1417567 := bstep (se 1 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 1417567 = 2126351) B2126351
theorem B1417595 : Blo 1417528 1417595 := bstep (se 1 (by rfl) ⟨1063196, by rfl⟩ : syracuseStep 1417595 = 2126393) B2126393
theorem B2392463 : Blo 1417528 2392463 := bstep (se 1 (by rfl) ⟨1794347, by rfl⟩ : syracuseStep 2392463 = 3588695) B3588695
theorem B1417647 : Blo 1417528 1417647 := bstep (se 1 (by rfl) ⟨1063235, by rfl⟩ : syracuseStep 1417647 = 2126471) B2126471
theorem B1417671 : Blo 1417528 1417671 := bstep (se 1 (by rfl) ⟨1063253, by rfl⟩ : syracuseStep 1417671 = 2126507) B2126507
theorem B1417691 : Blo 1417528 1417691 := bstep (se 1 (by rfl) ⟨1063268, by rfl⟩ : syracuseStep 1417691 = 2126537) B2126537
theorem B10912265 : Blo 1417528 10912265 := bstep (se 2 (by rfl) ⟨4092099, by rfl⟩ : syracuseStep 10912265 = 8184199) B8184199
theorem B2048521 : Blo 1417528 2048521 := bstep (se 2 (by rfl) ⟨768195, by rfl⟩ : syracuseStep 2048521 = 1536391) B1536391
theorem B3408409 : Blo 1417528 3408409 := bstep (se 2 (by rfl) ⟨1278153, by rfl⟩ : syracuseStep 3408409 = 2556307) B2556307
theorem B1417767 : Blo 1417528 1417767 := bstep (se 1 (by rfl) ⟨1063325, by rfl⟩ : syracuseStep 1417767 = 2126651) B2126651
theorem B16163387 : Blo 1417528 16163387 := bstep (se 1 (by rfl) ⟨12122540, by rfl⟩ : syracuseStep 16163387 = 24245081) B24245081
theorem B1417807 : Blo 1417528 1417807 := bstep (se 1 (by rfl) ⟨1063355, by rfl⟩ : syracuseStep 1417807 = 2126711) B2126711
theorem B1417823 : Blo 1417528 1417823 := bstep (se 1 (by rfl) ⟨1063367, by rfl⟩ : syracuseStep 1417823 = 2126735) B2126735
theorem B1417851 : Blo 1417528 1417851 := bstep (se 1 (by rfl) ⟨1063388, by rfl⟩ : syracuseStep 1417851 = 2126777) B2126777
theorem B2392699 : Blo 1417528 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B9700013 : Blo 1417528 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B1417903 : Blo 1417528 1417903 := bstep (se 1 (by rfl) ⟨1063427, by rfl⟩ : syracuseStep 1417903 = 2126855) B2126855
theorem B5382845 : Blo 1417528 5382845 := bstep (se 3 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 5382845 = 2018567) B2018567
theorem B3547847 : Blo 1417528 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B1417927 : Blo 1417528 1417927 := bstep (se 1 (by rfl) ⟨1063445, by rfl⟩ : syracuseStep 1417927 = 2126891) B2126891
theorem B4039379 : Blo 1417528 4039379 := bstep (se 1 (by rfl) ⟨3029534, by rfl⟩ : syracuseStep 4039379 = 6059069) B6059069
theorem B1417947 : Blo 1417528 1417947 := bstep (se 1 (by rfl) ⟨1063460, by rfl⟩ : syracuseStep 1417947 = 2126921) B2126921
theorem B3588857 : Blo 1417528 3588857 := bstep (se 2 (by rfl) ⟨1345821, by rfl⟩ : syracuseStep 3588857 = 2691643) B2691643
theorem B2876153 : Blo 1417528 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1418023 : Blo 1417528 1418023 := bstep (se 1 (by rfl) ⟨1063517, by rfl⟩ : syracuseStep 1418023 = 2127035) B2127035
theorem B4784939 : Blo 1417528 4784939 := bstep (se 1 (by rfl) ⟨3588704, by rfl⟩ : syracuseStep 4784939 = 7177409) B7177409
theorem B3834697 : Blo 1417528 3834697 := bstep (se 2 (by rfl) ⟨1438011, by rfl⟩ : syracuseStep 3834697 = 2876023) B2876023
theorem B1418063 : Blo 1417528 1418063 := bstep (se 1 (by rfl) ⟨1063547, by rfl⟩ : syracuseStep 1418063 = 2127095) B2127095
theorem B1418079 : Blo 1417528 1418079 := bstep (se 1 (by rfl) ⟨1063559, by rfl⟩ : syracuseStep 1418079 = 2127119) B2127119
theorem B1917803 : Blo 1417528 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B1418107 : Blo 1417528 1418107 := bstep (se 1 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 1418107 = 2127161) B2127161
theorem B1418159 : Blo 1417528 1418159 := bstep (se 1 (by rfl) ⟨1063619, by rfl⟩ : syracuseStep 1418159 = 2127239) B2127239
theorem B1418183 : Blo 1417528 1418183 := bstep (se 1 (by rfl) ⟨1063637, by rfl⟩ : syracuseStep 1418183 = 2127275) B2127275
theorem B1418203 : Blo 1417528 1418203 := bstep (se 1 (by rfl) ⟨1063652, by rfl⟩ : syracuseStep 1418203 = 2127305) B2127305
theorem B3073043 : Blo 1417528 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B1418279 : Blo 1417528 1418279 := bstep (se 1 (by rfl) ⟨1063709, by rfl⟩ : syracuseStep 1418279 = 2127419) B2127419
theorem B4785209 : Blo 1417528 4785209 := bstep (se 2 (by rfl) ⟨1794453, by rfl⟩ : syracuseStep 4785209 = 3588907) B3588907
theorem B21849155 : Blo 1417528 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B1418319 : Blo 1417528 1418319 := bstep (se 1 (by rfl) ⟨1063739, by rfl⟩ : syracuseStep 1418319 = 2127479) B2127479
theorem B1418335 : Blo 1417528 1418335 := bstep (se 1 (by rfl) ⟨1063751, by rfl⟩ : syracuseStep 1418335 = 2127503) B2127503
theorem B1418363 : Blo 1417528 1418363 := bstep (se 1 (by rfl) ⟨1063772, by rfl⟩ : syracuseStep 1418363 = 2127545) B2127545
theorem B23635097 : Blo 1417528 23635097 := bstep (se 2 (by rfl) ⟨8863161, by rfl⟩ : syracuseStep 23635097 = 17726323) B17726323
theorem B1418415 : Blo 1417528 1418415 := bstep (se 1 (by rfl) ⟨1063811, by rfl⟩ : syracuseStep 1418415 = 2127623) B2127623
theorem B1418439 : Blo 1417528 1418439 := bstep (se 1 (by rfl) ⟨1063829, by rfl⟩ : syracuseStep 1418439 = 2127659) B2127659
theorem B7775435 : Blo 1417528 7775435 := bstep (se 1 (by rfl) ⟨5831576, by rfl⟩ : syracuseStep 7775435 = 11663153) B11663153
theorem B1418459 : Blo 1417528 1418459 := bstep (se 1 (by rfl) ⟨1063844, by rfl⟩ : syracuseStep 1418459 = 2127689) B2127689
theorem B1418535 : Blo 1417528 1418535 := bstep (se 1 (by rfl) ⟨1063901, by rfl⟩ : syracuseStep 1418535 = 2127803) B2127803
theorem B1418575 : Blo 1417528 1418575 := bstep (se 1 (by rfl) ⟨1063931, by rfl⟩ : syracuseStep 1418575 = 2127863) B2127863
theorem B1418591 : Blo 1417528 1418591 := bstep (se 1 (by rfl) ⟨1063943, by rfl⟩ : syracuseStep 1418591 = 2127887) B2127887
theorem B5383529 : Blo 1417528 5383529 := bstep (se 2 (by rfl) ⟨2018823, by rfl⟩ : syracuseStep 5383529 = 4037647) B4037647
theorem B1418619 : Blo 1417528 1418619 := bstep (se 1 (by rfl) ⟨1063964, by rfl⟩ : syracuseStep 1418619 = 2127929) B2127929
theorem B4785533 : Blo 1417528 4785533 := bstep (se 3 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 4785533 = 1794575) B1794575
theorem B3589505 : Blo 1417528 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B1418671 : Blo 1417528 1418671 := bstep (se 1 (by rfl) ⟨1064003, by rfl⟩ : syracuseStep 1418671 = 2128007) B2128007
theorem B1418695 : Blo 1417528 1418695 := bstep (se 1 (by rfl) ⟨1064021, by rfl⟩ : syracuseStep 1418695 = 2128043) B2128043
theorem B2270683 : Blo 1417528 2270683 := bstep (se 1 (by rfl) ⟨1703012, by rfl⟩ : syracuseStep 2270683 = 3406025) B3406025
theorem B2393563 : Blo 1417528 2393563 := bstep (se 1 (by rfl) ⟨1795172, by rfl⟩ : syracuseStep 2393563 = 3590345) B3590345
theorem B1795547 : Blo 1417528 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B1418715 : Blo 1417528 1418715 := bstep (se 1 (by rfl) ⟨1064036, by rfl⟩ : syracuseStep 1418715 = 2128073) B2128073
theorem B2557403 : Blo 1417528 2557403 := bstep (se 1 (by rfl) ⟨1918052, by rfl⟩ : syracuseStep 2557403 = 3836105) B3836105
theorem B1418791 : Blo 1417528 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B1418831 : Blo 1417528 1418831 := bstep (se 1 (by rfl) ⟨1064123, by rfl⟩ : syracuseStep 1418831 = 2128247) B2128247
theorem B1418847 : Blo 1417528 1418847 := bstep (se 1 (by rfl) ⟨1064135, by rfl⟩ : syracuseStep 1418847 = 2128271) B2128271
theorem B11495009 : Blo 1417528 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B1418875 : Blo 1417528 1418875 := bstep (se 1 (by rfl) ⟨1064156, by rfl⟩ : syracuseStep 1418875 = 2128313) B2128313
theorem B4785803 : Blo 1417528 4785803 := bstep (se 1 (by rfl) ⟨3589352, by rfl⟩ : syracuseStep 4785803 = 7178705) B7178705
theorem B1418927 : Blo 1417528 1418927 := bstep (se 1 (by rfl) ⟨1064195, by rfl⟩ : syracuseStep 1418927 = 2128391) B2128391
theorem B4040381 : Blo 1417528 4040381 := bstep (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) B1515143
theorem B1418951 : Blo 1417528 1418951 := bstep (se 1 (by rfl) ⟨1064213, by rfl⟩ : syracuseStep 1418951 = 2128427) B2128427
theorem B1418971 : Blo 1417528 1418971 := bstep (se 1 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 1418971 = 2128457) B2128457
theorem B1419047 : Blo 1417528 1419047 := bstep (se 1 (by rfl) ⟨1064285, by rfl⟩ : syracuseStep 1419047 = 2128571) B2128571
theorem B1419087 : Blo 1417528 1419087 := bstep (se 1 (by rfl) ⟨1064315, by rfl⟩ : syracuseStep 1419087 = 2128631) B2128631
theorem B1419103 : Blo 1417528 1419103 := bstep (se 1 (by rfl) ⟨1064327, by rfl⟩ : syracuseStep 1419103 = 2128655) B2128655
theorem B1419131 : Blo 1417528 1419131 := bstep (se 1 (by rfl) ⟨1064348, by rfl⟩ : syracuseStep 1419131 = 2128697) B2128697
theorem B1419183 : Blo 1417528 1419183 := bstep (se 1 (by rfl) ⟨1064387, by rfl⟩ : syracuseStep 1419183 = 2128775) B2128775
theorem B1796023 : Blo 1417528 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B50456513 : Blo 1417528 50456513 := bstep (se 2 (by rfl) ⟨18921192, by rfl⟩ : syracuseStep 50456513 = 37842385) B37842385
theorem B1419207 : Blo 1417528 1419207 := bstep (se 1 (by rfl) ⟨1064405, by rfl⟩ : syracuseStep 1419207 = 2128811) B2128811
theorem B1419227 : Blo 1417528 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B4040711 : Blo 1417528 4040711 := bstep (se 1 (by rfl) ⟨3030533, by rfl⟩ : syracuseStep 4040711 = 6061067) B6061067
theorem B1419303 : Blo 1417528 1419303 := bstep (se 1 (by rfl) ⟨1064477, by rfl⟩ : syracuseStep 1419303 = 2128955) B2128955
theorem B2394191 : Blo 1417528 2394191 := bstep (se 1 (by rfl) ⟨1795643, by rfl⟩ : syracuseStep 2394191 = 3591287) B3591287
theorem B1419343 : Blo 1417528 1419343 := bstep (se 1 (by rfl) ⟨1064507, by rfl⟩ : syracuseStep 1419343 = 2129015) B2129015
theorem B1419359 : Blo 1417528 1419359 := bstep (se 1 (by rfl) ⟨1064519, by rfl⟩ : syracuseStep 1419359 = 2129039) B2129039
theorem B1419387 : Blo 1417528 1419387 := bstep (se 1 (by rfl) ⟨1064540, by rfl⟩ : syracuseStep 1419387 = 2129081) B2129081
theorem B6138013 : Blo 1417528 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B3590315 : Blo 1417528 3590315 := bstep (se 1 (by rfl) ⟨2692736, by rfl⟩ : syracuseStep 3590315 = 5385473) B5385473
theorem B1419439 : Blo 1417528 1419439 := bstep (se 1 (by rfl) ⟨1064579, by rfl⟩ : syracuseStep 1419439 = 2129159) B2129159
theorem B1419463 : Blo 1417528 1419463 := bstep (se 1 (by rfl) ⟨1064597, by rfl⟩ : syracuseStep 1419463 = 2129195) B2129195
theorem B1419483 : Blo 1417528 1419483 := bstep (se 1 (by rfl) ⟨1064612, by rfl⟩ : syracuseStep 1419483 = 2129225) B2129225
theorem B2271593 : Blo 1417528 2271593 := bstep (se 2 (by rfl) ⟨851847, by rfl⟩ : syracuseStep 2271593 = 1703695) B1703695
theorem B8194409 : Blo 1417528 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B4786721 : Blo 1417528 4786721 := bstep (se 2 (by rfl) ⟨1795020, by rfl⟩ : syracuseStep 4786721 = 3590041) B3590041
theorem B15346361 : Blo 1417528 15346361 := bstep (se 2 (by rfl) ⟨5754885, by rfl⟩ : syracuseStep 15346361 = 11509771) B11509771
theorem B7383737 : Blo 1417528 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2730707 : Blo 1417528 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B4786937 : Blo 1417528 4786937 := bstep (se 2 (by rfl) ⟨1795101, by rfl⟩ : syracuseStep 4786937 = 3590203) B3590203
theorem B23006045 : Blo 1417528 23006045 := bstep (se 3 (by rfl) ⟨4313633, by rfl⟩ : syracuseStep 23006045 = 8627267) B8627267
theorem B3189599 : Blo 1417528 3189599 := bstep (se 1 (by rfl) ⟨2392199, by rfl⟩ : syracuseStep 3189599 = 4784399) B4784399
theorem B94563235 : Blo 1417528 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B2395055 : Blo 1417528 2395055 := bstep (se 1 (by rfl) ⟨1796291, by rfl⟩ : syracuseStep 2395055 = 3592583) B3592583
theorem B7179191 : Blo 1417528 7179191 := bstep (se 1 (by rfl) ⟨5384393, by rfl⟩ : syracuseStep 7179191 = 10768787) B10768787
theorem B4787207 : Blo 1417528 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B3591175 : Blo 1417528 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B3189779 : Blo 1417528 3189779 := bstep (se 1 (by rfl) ⟨2392334, by rfl⟩ : syracuseStep 3189779 = 4784669) B4784669
theorem B4787315 : Blo 1417528 4787315 := bstep (se 1 (by rfl) ⟨3590486, by rfl⟩ : syracuseStep 4787315 = 7180973) B7180973
theorem B63073475 : Blo 1417528 63073475 := bstep (se 1 (by rfl) ⟨47305106, by rfl⟩ : syracuseStep 63073475 = 94610213) B94610213
theorem B3190121 : Blo 1417528 3190121 := bstep (se 2 (by rfl) ⟨1196295, by rfl⟩ : syracuseStep 3190121 = 2392591) B2392591
theorem B4787585 : Blo 1417528 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B5385761 : Blo 1417528 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B3591803 : Blo 1417528 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B1437359 : Blo 1417528 1437359 := bstep (se 1 (by rfl) ⟨1078019, by rfl⟩ : syracuseStep 1437359 = 2156039) B2156039
theorem B5459831 : Blo 1417528 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B3592097 : Blo 1417528 3592097 := bstep (se 2 (by rfl) ⟨1347036, by rfl⟩ : syracuseStep 3592097 = 2694073) B2694073
theorem B22998971 : Blo 1417528 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B3190715 : Blo 1417528 3190715 := bstep (se 1 (by rfl) ⟨2393036, by rfl⟩ : syracuseStep 3190715 = 4786073) B4786073
theorem B5386247 : Blo 1417528 5386247 := bstep (se 1 (by rfl) ⟨4039685, by rfl⟩ : syracuseStep 5386247 = 8079371) B8079371
theorem B3190841 : Blo 1417528 3190841 := bstep (se 2 (by rfl) ⟨1196565, by rfl⟩ : syracuseStep 3190841 = 2393131) B2393131
theorem B4788395 : Blo 1417528 4788395 := bstep (se 1 (by rfl) ⟨3591296, by rfl⟩ : syracuseStep 4788395 = 7182593) B7182593
theorem B14954827 : Blo 1417528 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B4608343 : Blo 1417528 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B8188265 : Blo 1417528 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B7180649 : Blo 1417528 7180649 := bstep (se 2 (by rfl) ⟨2692743, by rfl⟩ : syracuseStep 7180649 = 5385487) B5385487
theorem B3191183 : Blo 1417528 3191183 := bstep (se 1 (by rfl) ⟨2393387, by rfl⟩ : syracuseStep 3191183 = 4786775) B4786775
theorem B5386733 : Blo 1417528 5386733 := bstep (se 3 (by rfl) ⟨1010012, by rfl⟩ : syracuseStep 5386733 = 2020025) B2020025
theorem B2126345 : Blo 1417528 2126345 := bstep (se 2 (by rfl) ⟨797379, by rfl⟩ : syracuseStep 2126345 = 1594759) B1594759
theorem B2126375 : Blo 1417528 2126375 := bstep (se 1 (by rfl) ⟨1594781, by rfl⟩ : syracuseStep 2126375 = 3189563) B3189563
theorem B2126459 : Blo 1417528 2126459 := bstep (se 1 (by rfl) ⟨1594844, by rfl⟩ : syracuseStep 2126459 = 3189689) B3189689
theorem B6468281 : Blo 1417528 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B4788935 : Blo 1417528 4788935 := bstep (se 1 (by rfl) ⟨3591701, by rfl⟩ : syracuseStep 4788935 = 7183403) B7183403
theorem B3191507 : Blo 1417528 3191507 := bstep (se 1 (by rfl) ⟨2393630, by rfl⟩ : syracuseStep 3191507 = 4787261) B4787261
theorem B2126585 : Blo 1417528 2126585 := bstep (se 2 (by rfl) ⟨797469, by rfl⟩ : syracuseStep 2126585 = 1594939) B1594939
theorem B3642185 : Blo 1417528 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B2126687 : Blo 1417528 2126687 := bstep (se 1 (by rfl) ⟨1595015, by rfl⟩ : syracuseStep 2126687 = 3190031) B3190031
theorem B2126699 : Blo 1417528 2126699 := bstep (se 1 (by rfl) ⟨1595024, by rfl⟩ : syracuseStep 2126699 = 3190049) B3190049
theorem B2691947 : Blo 1417528 2691947 := bstep (se 1 (by rfl) ⟨2018960, by rfl⟩ : syracuseStep 2691947 = 4037921) B4037921
theorem B33182617 : Blo 1417528 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B2126927 : Blo 1417528 2126927 := bstep (se 1 (by rfl) ⟨1595195, by rfl⟩ : syracuseStep 2126927 = 3190391) B3190391
theorem B5387417 : Blo 1417528 5387417 := bstep (se 2 (by rfl) ⟨2020281, by rfl⟩ : syracuseStep 5387417 = 4040563) B4040563
theorem B16151723 : Blo 1417528 16151723 := bstep (se 1 (by rfl) ⟨12113792, by rfl⟩ : syracuseStep 16151723 = 24227585) B24227585
theorem B2127047 : Blo 1417528 2127047 := bstep (se 1 (by rfl) ⟨1595285, by rfl⟩ : syracuseStep 2127047 = 3190571) B3190571
theorem B2127209 : Blo 1417528 2127209 := bstep (se 2 (by rfl) ⟨797703, by rfl⟩ : syracuseStep 2127209 = 1595407) B1595407
theorem B4314473 : Blo 1417528 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B10778021 : Blo 1417528 10778021 := bstep (se 4 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 10778021 = 2020879) B2020879
theorem B2020783 : Blo 1417528 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B2127287 : Blo 1417528 2127287 := bstep (se 1 (by rfl) ⟨1595465, by rfl⟩ : syracuseStep 2127287 = 3190931) B3190931
theorem B2127323 : Blo 1417528 2127323 := bstep (se 1 (by rfl) ⟨1595492, by rfl⟩ : syracuseStep 2127323 = 3190985) B3190985
theorem B2692615 : Blo 1417528 2692615 := bstep (se 1 (by rfl) ⟨2019461, by rfl⟩ : syracuseStep 2692615 = 4038923) B4038923
theorem B4789799 : Blo 1417528 4789799 := bstep (se 1 (by rfl) ⟨3592349, by rfl⟩ : syracuseStep 4789799 = 7184699) B7184699
theorem B3028603 : Blo 1417528 3028603 := bstep (se 1 (by rfl) ⟨2271452, by rfl⟩ : syracuseStep 3028603 = 4542905) B4542905
theorem B3192443 : Blo 1417528 3192443 := bstep (se 1 (by rfl) ⟨2394332, by rfl⟩ : syracuseStep 3192443 = 4788665) B4788665
theorem B4789907 : Blo 1417528 4789907 := bstep (se 1 (by rfl) ⟨3592430, by rfl⟩ : syracuseStep 4789907 = 7184861) B7184861
theorem B16160471 : Blo 1417528 16160471 := bstep (se 1 (by rfl) ⟨12120353, by rfl⟩ : syracuseStep 16160471 = 24240707) B24240707
theorem B8623837 : Blo 1417528 8623837 := bstep (se 3 (by rfl) ⟨1616969, by rfl⟩ : syracuseStep 8623837 = 3233939) B3233939
theorem B12113657 : Blo 1417528 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B3192569 : Blo 1417528 3192569 := bstep (se 2 (by rfl) ⟨1197213, by rfl⟩ : syracuseStep 3192569 = 2394427) B2394427
theorem B23000921 : Blo 1417528 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B4790123 : Blo 1417528 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B4790177 : Blo 1417528 4790177 := bstep (se 2 (by rfl) ⟨1796316, by rfl⟩ : syracuseStep 4790177 = 3592633) B3592633
theorem B2127791 : Blo 1417528 2127791 := bstep (se 1 (by rfl) ⟨1595843, by rfl⟩ : syracuseStep 2127791 = 3191687) B3191687
theorem B3192839 : Blo 1417528 3192839 := bstep (se 1 (by rfl) ⟨2394629, by rfl⟩ : syracuseStep 3192839 = 4789259) B4789259
theorem B2127881 : Blo 1417528 2127881 := bstep (se 2 (by rfl) ⟨797955, by rfl⟩ : syracuseStep 2127881 = 1595911) B1595911
theorem B2127911 : Blo 1417528 2127911 := bstep (se 1 (by rfl) ⟨1595933, by rfl⟩ : syracuseStep 2127911 = 3191867) B3191867
theorem B11507789 : Blo 1417528 11507789 := bstep (se 3 (by rfl) ⟨2157710, by rfl⟩ : syracuseStep 11507789 = 4315421) B4315421
theorem B3192911 : Blo 1417528 3192911 := bstep (se 1 (by rfl) ⟨2394683, by rfl⟩ : syracuseStep 3192911 = 4789367) B4789367
theorem B5388403 : Blo 1417528 5388403 := bstep (se 1 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 5388403 = 8082605) B8082605
theorem B1595515 : Blo 1417528 1595515 := bstep (se 1 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 1595515 = 2393273) B2393273
theorem B2127995 : Blo 1417528 2127995 := bstep (se 1 (by rfl) ⟨1595996, by rfl⟩ : syracuseStep 2127995 = 3191993) B3191993
theorem B8747165 : Blo 1417528 8747165 := bstep (se 3 (by rfl) ⟨1640093, by rfl⟩ : syracuseStep 8747165 = 3280187) B3280187
theorem B2128121 : Blo 1417528 2128121 := bstep (se 2 (by rfl) ⟨798045, by rfl⟩ : syracuseStep 2128121 = 1596091) B1596091
theorem B2128223 : Blo 1417528 2128223 := bstep (se 1 (by rfl) ⟨1596167, by rfl⟩ : syracuseStep 2128223 = 3192335) B3192335
theorem B2128235 : Blo 1417528 2128235 := bstep (se 1 (by rfl) ⟨1596176, by rfl⟩ : syracuseStep 2128235 = 3192353) B3192353
theorem B40925573 : Blo 1417528 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B30669191 : Blo 1417528 30669191 := bstep (se 1 (by rfl) ⟨23001893, by rfl⟩ : syracuseStep 30669191 = 46003787) B46003787
theorem B3193307 : Blo 1417528 3193307 := bstep (se 1 (by rfl) ⟨2394980, by rfl⟩ : syracuseStep 3193307 = 4789961) B4789961
theorem B4790771 : Blo 1417528 4790771 := bstep (se 1 (by rfl) ⟨3593078, by rfl⟩ : syracuseStep 4790771 = 7186157) B7186157
theorem B1595983 : Blo 1417528 1595983 := bstep (se 1 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 1595983 = 2393975) B2393975
theorem B2128463 : Blo 1417528 2128463 := bstep (se 1 (by rfl) ⟨1596347, by rfl⟩ : syracuseStep 2128463 = 3192695) B3192695
theorem B2128583 : Blo 1417528 2128583 := bstep (se 1 (by rfl) ⟨1596437, by rfl⟩ : syracuseStep 2128583 = 3192875) B3192875
theorem B9083603 : Blo 1417528 9083603 := bstep (se 1 (by rfl) ⟨6812702, by rfl⟩ : syracuseStep 9083603 = 13625405) B13625405
theorem B2128745 : Blo 1417528 2128745 := bstep (se 2 (by rfl) ⟨798279, by rfl⟩ : syracuseStep 2128745 = 1596559) B1596559
theorem B5389163 : Blo 1417528 5389163 := bstep (se 1 (by rfl) ⟨4041872, by rfl⟩ : syracuseStep 5389163 = 8083745) B8083745
theorem B3193775 : Blo 1417528 3193775 := bstep (se 1 (by rfl) ⟨2395331, by rfl⟩ : syracuseStep 3193775 = 4790663) B4790663
theorem B2128823 : Blo 1417528 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B4545467 : Blo 1417528 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B1596379 : Blo 1417528 1596379 := bstep (se 1 (by rfl) ⟨1197284, by rfl⟩ : syracuseStep 1596379 = 2394569) B2394569
theorem B2128859 : Blo 1417528 2128859 := bstep (se 1 (by rfl) ⟨1596644, by rfl⟩ : syracuseStep 2128859 = 3193289) B3193289
theorem B20446181 : Blo 1417528 20446181 := bstep (se 4 (by rfl) ⟨1916829, by rfl⟩ : syracuseStep 20446181 = 3833659) B3833659
theorem B18177047 : Blo 1417528 18177047 := bstep (se 1 (by rfl) ⟨13632785, by rfl⟩ : syracuseStep 18177047 = 27265571) B27265571
theorem B1514575 : Blo 1417528 1514575 := bstep (se 1 (by rfl) ⟨1135931, by rfl⟩ : syracuseStep 1514575 = 2271863) B2271863
theorem B10771703 : Blo 1417528 10771703 := bstep (se 1 (by rfl) ⟨8078777, by rfl⟩ : syracuseStep 10771703 = 16157555) B16157555
theorem B1916267 : Blo 1417528 1916267 := bstep (se 1 (by rfl) ⟨1437200, by rfl⟩ : syracuseStep 1916267 = 2874401) B2874401
theorem B16367021 : Blo 1417528 16367021 := bstep (se 3 (by rfl) ⟨3068816, by rfl⟩ : syracuseStep 16367021 = 6137633) B6137633
theorem B1596847 : Blo 1417528 1596847 := bstep (se 1 (by rfl) ⟨1197635, by rfl⟩ : syracuseStep 1596847 = 2395271) B2395271
theorem B1703387 : Blo 1417528 1703387 := bstep (se 1 (by rfl) ⟨1277540, by rfl⟩ : syracuseStep 1703387 = 2555081) B2555081
theorem B5750297 : Blo 1417528 5750297 := bstep (se 2 (by rfl) ⟨2156361, by rfl⟩ : syracuseStep 5750297 = 4312723) B4312723
theorem B2694779 : Blo 1417528 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B10772189 : Blo 1417528 10772189 := bstep (se 3 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 10772189 = 4039571) B4039571
theorem B6061817 : Blo 1417528 6061817 := bstep (se 2 (by rfl) ⟨2273181, by rfl⟩ : syracuseStep 6061817 = 4546363) B4546363
theorem B11509613 : Blo 1417528 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B7184537 : Blo 1417528 7184537 := bstep (se 2 (by rfl) ⟨2694201, by rfl⟩ : syracuseStep 7184537 = 5388403) B5388403
theorem B30687437 : Blo 1417528 30687437 := bstep (se 3 (by rfl) ⟨5753894, by rfl⟩ : syracuseStep 30687437 = 11507789) B11507789
theorem B8184017 : Blo 1417528 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1417563 : Blo 1417528 1417563 := bstep (se 1 (by rfl) ⟨1063172, by rfl⟩ : syracuseStep 1417563 = 2126345) B2126345
theorem B7274843 : Blo 1417528 7274843 := bstep (se 1 (by rfl) ⟨5456132, by rfl⟩ : syracuseStep 7274843 = 10912265) B10912265
theorem B1417583 : Blo 1417528 1417583 := bstep (se 1 (by rfl) ⟨1063187, by rfl⟩ : syracuseStep 1417583 = 2126375) B2126375
theorem B1417639 : Blo 1417528 1417639 := bstep (se 1 (by rfl) ⟨1063229, by rfl⟩ : syracuseStep 1417639 = 2126459) B2126459
theorem B19939769 : Blo 1417528 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B6144457 : Blo 1417528 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B3588563 : Blo 1417528 3588563 := bstep (se 1 (by rfl) ⟨2691422, by rfl⟩ : syracuseStep 3588563 = 5382845) B5382845
theorem B1417723 : Blo 1417528 1417723 := bstep (se 1 (by rfl) ⟨1063292, by rfl⟩ : syracuseStep 1417723 = 2126585) B2126585
theorem B2392571 : Blo 1417528 2392571 := bstep (se 1 (by rfl) ⟨1794428, by rfl⟩ : syracuseStep 2392571 = 3588857) B3588857
theorem B1417791 : Blo 1417528 1417791 := bstep (se 1 (by rfl) ⟨1063343, by rfl⟩ : syracuseStep 1417791 = 2126687) B2126687
theorem B1417799 : Blo 1417528 1417799 := bstep (se 1 (by rfl) ⟨1063349, by rfl⟩ : syracuseStep 1417799 = 2126699) B2126699
theorem B1794631 : Blo 1417528 1794631 := bstep (se 1 (by rfl) ⟨1345973, by rfl⟩ : syracuseStep 1794631 = 2691947) B2691947
theorem B2048695 : Blo 1417528 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B14566103 : Blo 1417528 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B1417951 : Blo 1417528 1417951 := bstep (se 1 (by rfl) ⟨1063463, by rfl⟩ : syracuseStep 1417951 = 2126927) B2126927
theorem B1418031 : Blo 1417528 1418031 := bstep (se 1 (by rfl) ⟨1063523, by rfl⟩ : syracuseStep 1418031 = 2127047) B2127047
theorem B3589019 : Blo 1417528 3589019 := bstep (se 1 (by rfl) ⟨2691764, by rfl⟩ : syracuseStep 3589019 = 5383529) B5383529
theorem B1418139 : Blo 1417528 1418139 := bstep (se 1 (by rfl) ⟨1063604, by rfl⟩ : syracuseStep 1418139 = 2127209) B2127209
theorem B2876315 : Blo 1417528 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B2393003 : Blo 1417528 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B7185347 : Blo 1417528 7185347 := bstep (se 1 (by rfl) ⟨5389010, by rfl⟩ : syracuseStep 7185347 = 10778021) B10778021
theorem B1418191 : Blo 1417528 1418191 := bstep (se 1 (by rfl) ⟨1063643, by rfl⟩ : syracuseStep 1418191 = 2127287) B2127287
theorem B1418215 : Blo 1417528 1418215 := bstep (se 1 (by rfl) ⟨1063661, by rfl⟩ : syracuseStep 1418215 = 2127323) B2127323
theorem B1704935 : Blo 1417528 1704935 := bstep (se 1 (by rfl) ⟨1278701, by rfl⟩ : syracuseStep 1704935 = 2557403) B2557403
theorem B5112929 : Blo 1417528 5112929 := bstep (se 2 (by rfl) ⟨1917348, by rfl⟩ : syracuseStep 5112929 = 3834697) B3834697
theorem B20440181 : Blo 1417528 20440181 := bstep (se 5 (by rfl) ⟨958133, by rfl⟩ : syracuseStep 20440181 = 1916267) B1916267
theorem B10773647 : Blo 1417528 10773647 := bstep (se 1 (by rfl) ⟨8080235, by rfl⟩ : syracuseStep 10773647 = 16160471) B16160471
theorem B126084313 : Blo 1417528 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B1418527 : Blo 1417528 1418527 := bstep (se 1 (by rfl) ⟨1063895, by rfl⟩ : syracuseStep 1418527 = 2127791) B2127791
theorem B33637675 : Blo 1417528 33637675 := bstep (se 1 (by rfl) ⟨25228256, by rfl⟩ : syracuseStep 33637675 = 50456513) B50456513
theorem B1418587 : Blo 1417528 1418587 := bstep (se 1 (by rfl) ⟨1063940, by rfl⟩ : syracuseStep 1418587 = 2127881) B2127881
theorem B1418607 : Blo 1417528 1418607 := bstep (se 1 (by rfl) ⟨1063955, by rfl⟩ : syracuseStep 1418607 = 2127911) B2127911
theorem B1418663 : Blo 1417528 1418663 := bstep (se 1 (by rfl) ⟨1063997, by rfl⟩ : syracuseStep 1418663 = 2127995) B2127995
theorem B2393543 : Blo 1417528 2393543 := bstep (se 1 (by rfl) ⟨1795157, by rfl⟩ : syracuseStep 2393543 = 3590315) B3590315
theorem B1418747 : Blo 1417528 1418747 := bstep (se 1 (by rfl) ⟨1064060, by rfl⟩ : syracuseStep 1418747 = 2128121) B2128121
theorem B1418815 : Blo 1417528 1418815 := bstep (se 1 (by rfl) ⟨1064111, by rfl⟩ : syracuseStep 1418815 = 2128223) B2128223
theorem B1418823 : Blo 1417528 1418823 := bstep (se 1 (by rfl) ⟨1064117, by rfl⟩ : syracuseStep 1418823 = 2128235) B2128235
theorem B1418975 : Blo 1417528 1418975 := bstep (se 1 (by rfl) ⟨1064231, by rfl⟩ : syracuseStep 1418975 = 2128463) B2128463
theorem B1419055 : Blo 1417528 1419055 := bstep (se 1 (by rfl) ⟨1064291, by rfl⟩ : syracuseStep 1419055 = 2128583) B2128583
theorem B6055735 : Blo 1417528 6055735 := bstep (se 1 (by rfl) ⟨4541801, by rfl⟩ : syracuseStep 6055735 = 9083603) B9083603
theorem B1820471 : Blo 1417528 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B15337363 : Blo 1417528 15337363 := bstep (se 1 (by rfl) ⟨11503022, by rfl⟩ : syracuseStep 15337363 = 23006045) B23006045
theorem B1419163 : Blo 1417528 1419163 := bstep (se 1 (by rfl) ⟨1064372, by rfl⟩ : syracuseStep 1419163 = 2128745) B2128745
theorem B4786127 : Blo 1417528 4786127 := bstep (se 1 (by rfl) ⟨3589595, by rfl⟩ : syracuseStep 4786127 = 7179191) B7179191
theorem B1419215 : Blo 1417528 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B1419239 : Blo 1417528 1419239 := bstep (se 1 (by rfl) ⟨1064429, by rfl⟩ : syracuseStep 1419239 = 2128859) B2128859
theorem B7669741 : Blo 1417528 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B16164845 : Blo 1417528 16164845 := bstep (se 3 (by rfl) ⟨3030908, by rfl⟩ : syracuseStep 16164845 = 6061817) B6061817
theorem B3590153 : Blo 1417528 3590153 := bstep (se 2 (by rfl) ⟨1346307, by rfl⟩ : syracuseStep 3590153 = 2692615) B2692615
theorem B12118031 : Blo 1417528 12118031 := bstep (se 1 (by rfl) ⟨9088523, by rfl⟩ : syracuseStep 12118031 = 18177047) B18177047
theorem B5114141 : Blo 1417528 5114141 := bstep (se 3 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 5114141 = 1917803) B1917803
theorem B3590507 : Blo 1417528 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B2394535 : Blo 1417528 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B1796519 : Blo 1417528 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B12110309 : Blo 1417528 12110309 := bstep (se 4 (by rfl) ⟨1135341, by rfl⟩ : syracuseStep 12110309 = 2270683) B2270683
theorem B2394697 : Blo 1417528 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B3639887 : Blo 1417528 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B2394731 : Blo 1417528 2394731 := bstep (se 1 (by rfl) ⟨1796048, by rfl⟩ : syracuseStep 2394731 = 3592097) B3592097
theorem B6056623 : Blo 1417528 6056623 := bstep (se 1 (by rfl) ⟨4542467, by rfl⟩ : syracuseStep 6056623 = 9084935) B9084935
theorem B3590831 : Blo 1417528 3590831 := bstep (se 1 (by rfl) ⟨2693123, by rfl⟩ : syracuseStep 3590831 = 5386247) B5386247
theorem B13642627 : Blo 1417528 13642627 := bstep (se 1 (by rfl) ⟨10231970, by rfl⟩ : syracuseStep 13642627 = 20463941) B20463941
theorem B5458843 : Blo 1417528 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B4787099 : Blo 1417528 4787099 := bstep (se 1 (by rfl) ⟨3590324, by rfl⟩ : syracuseStep 4787099 = 7180649) B7180649
theorem B3591155 : Blo 1417528 3591155 := bstep (se 1 (by rfl) ⟨2693366, by rfl⟩ : syracuseStep 3591155 = 5386733) B5386733
theorem B10775591 : Blo 1417528 10775591 := bstep (se 1 (by rfl) ⟨8081693, by rfl⟩ : syracuseStep 10775591 = 16163387) B16163387
theorem B6466675 : Blo 1417528 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B4312187 : Blo 1417528 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B3189959 : Blo 1417528 3189959 := bstep (se 1 (by rfl) ⟨2392469, by rfl⟩ : syracuseStep 3189959 = 4784939) B4784939
theorem B2428123 : Blo 1417528 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B2731361 : Blo 1417528 2731361 := bstep (se 2 (by rfl) ⟨1024260, by rfl⟩ : syracuseStep 2731361 = 2048521) B2048521
theorem B3190139 : Blo 1417528 3190139 := bstep (se 1 (by rfl) ⟨2392604, by rfl⟩ : syracuseStep 3190139 = 4785209) B4785209
theorem B15756731 : Blo 1417528 15756731 := bstep (se 1 (by rfl) ⟨11817548, by rfl⟩ : syracuseStep 15756731 = 23635097) B23635097
theorem B3591611 : Blo 1417528 3591611 := bstep (se 1 (by rfl) ⟨2693708, by rfl⟩ : syracuseStep 3591611 = 5387417) B5387417
theorem B10767815 : Blo 1417528 10767815 := bstep (se 1 (by rfl) ⟨8075861, by rfl⟩ : syracuseStep 10767815 = 16151723) B16151723
theorem B3190265 : Blo 1417528 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B3190355 : Blo 1417528 3190355 := bstep (se 1 (by rfl) ⟨2392766, by rfl⟩ : syracuseStep 3190355 = 4785533) B4785533
theorem B7663339 : Blo 1417528 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B3190535 : Blo 1417528 3190535 := bstep (se 1 (by rfl) ⟨2392901, by rfl⟩ : syracuseStep 3190535 = 4785803) B4785803
theorem B4542365 : Blo 1417528 4542365 := bstep (se 3 (by rfl) ⟨851693, by rfl⟩ : syracuseStep 4542365 = 1703387) B1703387
theorem B4788125 : Blo 1417528 4788125 := bstep (se 3 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 4788125 = 1795547) B1795547
theorem B4788233 : Blo 1417528 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B2019433 : Blo 1417528 2019433 := bstep (se 2 (by rfl) ⟨757287, by rfl⟩ : syracuseStep 2019433 = 1514575) B1514575
theorem B27283715 : Blo 1417528 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B3191147 : Blo 1417528 3191147 := bstep (se 1 (by rfl) ⟨2393360, by rfl⟩ : syracuseStep 3191147 = 4786721) B4786721
theorem B3191291 : Blo 1417528 3191291 := bstep (se 1 (by rfl) ⟨2393468, by rfl⟩ : syracuseStep 3191291 = 4786937) B4786937
theorem B2126399 : Blo 1417528 2126399 := bstep (se 1 (by rfl) ⟨1594799, by rfl⟩ : syracuseStep 2126399 = 3189599) B3189599
theorem B3592775 : Blo 1417528 3592775 := bstep (se 1 (by rfl) ⟨2694581, by rfl⟩ : syracuseStep 3592775 = 5389163) B5389163
theorem B3191417 : Blo 1417528 3191417 := bstep (se 2 (by rfl) ⟨1196781, by rfl⟩ : syracuseStep 3191417 = 2393563) B2393563
theorem B3191471 : Blo 1417528 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B2126519 : Blo 1417528 2126519 := bstep (se 1 (by rfl) ⟨1594889, by rfl⟩ : syracuseStep 2126519 = 3189779) B3189779
theorem B3191543 : Blo 1417528 3191543 := bstep (se 1 (by rfl) ⟨2393657, by rfl⟩ : syracuseStep 3191543 = 4787315) B4787315
theorem B7181135 : Blo 1417528 7181135 := bstep (se 1 (by rfl) ⟨5385851, by rfl⟩ : syracuseStep 7181135 = 10771703) B10771703
theorem B2126747 : Blo 1417528 2126747 := bstep (se 1 (by rfl) ⟨1595060, by rfl⟩ : syracuseStep 2126747 = 3190121) B3190121
theorem B3191723 : Blo 1417528 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B11498449 : Blo 1417528 11498449 := bstep (se 2 (by rfl) ⟨4311918, by rfl⟩ : syracuseStep 11498449 = 8623837) B8623837
theorem B7181459 : Blo 1417528 7181459 := bstep (se 1 (by rfl) ⟨5386094, by rfl⟩ : syracuseStep 7181459 = 10772189) B10772189
theorem B7673075 : Blo 1417528 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B15332647 : Blo 1417528 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2127143 : Blo 1417528 2127143 := bstep (se 1 (by rfl) ⟨1595357, by rfl⟩ : syracuseStep 2127143 = 3190715) B3190715
theorem B10769759 : Blo 1417528 10769759 := bstep (se 1 (by rfl) ⟨8077319, by rfl⟩ : syracuseStep 10769759 = 16154639) B16154639
theorem B2127227 : Blo 1417528 2127227 := bstep (se 1 (by rfl) ⟨1595420, by rfl⟩ : syracuseStep 2127227 = 3190841) B3190841
theorem B3192263 : Blo 1417528 3192263 := bstep (se 1 (by rfl) ⟨2394197, by rfl⟩ : syracuseStep 3192263 = 4788395) B4788395
theorem B2127353 : Blo 1417528 2127353 := bstep (se 2 (by rfl) ⟨797757, by rfl⟩ : syracuseStep 2127353 = 1595515) B1595515
theorem B1594975 : Blo 1417528 1594975 := bstep (se 1 (by rfl) ⟨1196231, by rfl⟩ : syracuseStep 1594975 = 2392463) B2392463
theorem B2127455 : Blo 1417528 2127455 := bstep (se 1 (by rfl) ⟨1595591, by rfl⟩ : syracuseStep 2127455 = 3191183) B3191183
theorem B3192623 : Blo 1417528 3192623 := bstep (se 1 (by rfl) ⟨2394467, by rfl⟩ : syracuseStep 3192623 = 4788935) B4788935
theorem B2127671 : Blo 1417528 2127671 := bstep (se 1 (by rfl) ⟨1595753, by rfl⟩ : syracuseStep 2127671 = 3191507) B3191507
theorem B2692919 : Blo 1417528 2692919 := bstep (se 1 (by rfl) ⟨2019689, by rfl⟩ : syracuseStep 2692919 = 4039379) B4039379
theorem B4544545 : Blo 1417528 4544545 := bstep (se 2 (by rfl) ⟨1704204, by rfl⟩ : syracuseStep 4544545 = 3408409) B3408409
theorem B2127977 : Blo 1417528 2127977 := bstep (se 2 (by rfl) ⟨797991, by rfl⟩ : syracuseStep 2127977 = 1595983) B1595983
theorem B5183623 : Blo 1417528 5183623 := bstep (se 1 (by rfl) ⟨3887717, by rfl⟩ : syracuseStep 5183623 = 7775435) B7775435
theorem B3193199 : Blo 1417528 3193199 := bstep (se 1 (by rfl) ⟨2394899, by rfl⟩ : syracuseStep 3193199 = 4789799) B4789799
theorem B2128295 : Blo 1417528 2128295 := bstep (se 1 (by rfl) ⟨1596221, by rfl⟩ : syracuseStep 2128295 = 3192443) B3192443
theorem B3193271 : Blo 1417528 3193271 := bstep (se 1 (by rfl) ⟨2394953, by rfl⟩ : syracuseStep 3193271 = 4789907) B4789907
theorem B2693587 : Blo 1417528 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B8075771 : Blo 1417528 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B2128379 : Blo 1417528 2128379 := bstep (se 1 (by rfl) ⟨1596284, by rfl⟩ : syracuseStep 2128379 = 3192569) B3192569
theorem B44243489 : Blo 1417528 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B15333947 : Blo 1417528 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B3193415 : Blo 1417528 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B3193451 : Blo 1417528 3193451 := bstep (se 1 (by rfl) ⟨2395088, by rfl⟩ : syracuseStep 3193451 = 4790177) B4790177
theorem B2128505 : Blo 1417528 2128505 := bstep (se 2 (by rfl) ⟨798189, by rfl⟩ : syracuseStep 2128505 = 1596379) B1596379
theorem B2693807 : Blo 1417528 2693807 := bstep (se 1 (by rfl) ⟨2020355, by rfl⟩ : syracuseStep 2693807 = 4040711) B4040711
theorem B2128559 : Blo 1417528 2128559 := bstep (se 1 (by rfl) ⟨1596419, by rfl⟩ : syracuseStep 2128559 = 3192839) B3192839
theorem B1596127 : Blo 1417528 1596127 := bstep (se 1 (by rfl) ⟨1197095, by rfl⟩ : syracuseStep 1596127 = 2394191) B2394191
theorem B2128607 : Blo 1417528 2128607 := bstep (se 1 (by rfl) ⟨1596455, by rfl⟩ : syracuseStep 2128607 = 3192911) B3192911
theorem B5831443 : Blo 1417528 5831443 := bstep (se 1 (by rfl) ⟨4373582, by rfl⟩ : syracuseStep 5831443 = 8747165) B8747165
theorem B1514395 : Blo 1417528 1514395 := bstep (se 1 (by rfl) ⟨1135796, by rfl⟩ : syracuseStep 1514395 = 2271593) B2271593
theorem B5462939 : Blo 1417528 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B20446127 : Blo 1417528 20446127 := bstep (se 1 (by rfl) ⟨15334595, by rfl⟩ : syracuseStep 20446127 = 30669191) B30669191
theorem B2128871 : Blo 1417528 2128871 := bstep (se 1 (by rfl) ⟨1596653, by rfl⟩ : syracuseStep 2128871 = 3193307) B3193307
theorem B3193847 : Blo 1417528 3193847 := bstep (se 1 (by rfl) ⟨2395385, by rfl⟩ : syracuseStep 3193847 = 4790771) B4790771
theorem B10230907 : Blo 1417528 10230907 := bstep (se 1 (by rfl) ⟨7673180, by rfl⟩ : syracuseStep 10230907 = 15346361) B15346361
theorem B4922491 : Blo 1417528 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B3832957 : Blo 1417528 3832957 := bstep (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) B1437359
theorem B9460925 : Blo 1417528 9460925 := bstep (se 3 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 9460925 = 3547847) B3547847
theorem B2694377 : Blo 1417528 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B2129129 : Blo 1417528 2129129 := bstep (se 2 (by rfl) ⟨798423, by rfl⟩ : syracuseStep 2129129 = 1596847) B1596847
theorem B1596703 : Blo 1417528 1596703 := bstep (se 1 (by rfl) ⟨1197527, by rfl⟩ : syracuseStep 1596703 = 2395055) B2395055
theorem B2129183 : Blo 1417528 2129183 := bstep (se 1 (by rfl) ⟨1596887, by rfl⟩ : syracuseStep 2129183 = 3193775) B3193775
theorem B3030311 : Blo 1417528 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B13630787 : Blo 1417528 13630787 := bstep (se 1 (by rfl) ⟨10223090, by rfl⟩ : syracuseStep 13630787 = 20446181) B20446181
theorem B42048983 : Blo 1417528 42048983 := bstep (se 1 (by rfl) ⟨31536737, by rfl⟩ : syracuseStep 42048983 = 63073475) B63073475
theorem B4038137 : Blo 1417528 4038137 := bstep (se 2 (by rfl) ⟨1514301, by rfl⟩ : syracuseStep 4038137 = 3028603) B3028603
theorem B10911347 : Blo 1417528 10911347 := bstep (se 1 (by rfl) ⟨8183510, by rfl⟩ : syracuseStep 10911347 = 16367021) B16367021
theorem B3833531 : Blo 1417528 3833531 := bstep (se 1 (by rfl) ⟨2875148, by rfl⟩ : syracuseStep 3833531 = 5750297) B5750297
theorem B5456011 : Blo 1417528 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B4849895 : Blo 1417528 4849895 := bstep (se 1 (by rfl) ⟨3637421, by rfl⟩ : syracuseStep 4849895 = 7274843) B7274843
theorem B2392375 : Blo 1417528 2392375 := bstep (se 1 (by rfl) ⟨1794281, by rfl⟩ : syracuseStep 2392375 = 3588563) B3588563
theorem B1417599 : Blo 1417528 1417599 := bstep (se 1 (by rfl) ⟨1063199, by rfl⟩ : syracuseStep 1417599 = 2126399) B2126399
theorem B1417679 : Blo 1417528 1417679 := bstep (se 1 (by rfl) ⟨1063259, by rfl⟩ : syracuseStep 1417679 = 2126519) B2126519
theorem B8192609 : Blo 1417528 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1417831 : Blo 1417528 1417831 := bstep (se 1 (by rfl) ⟨1063373, by rfl⟩ : syracuseStep 1417831 = 2126747) B2126747
theorem B2392679 : Blo 1417528 2392679 := bstep (se 1 (by rfl) ⟨1794509, by rfl⟩ : syracuseStep 2392679 = 3589019) B3589019
theorem B2392841 : Blo 1417528 2392841 := bstep (se 2 (by rfl) ⟨897315, by rfl⟩ : syracuseStep 2392841 = 1794631) B1794631
theorem B1418095 : Blo 1417528 1418095 := bstep (se 1 (by rfl) ⟨1063571, by rfl⟩ : syracuseStep 1418095 = 2127143) B2127143
theorem B1418151 : Blo 1417528 1418151 := bstep (se 1 (by rfl) ⟨1063613, by rfl⟩ : syracuseStep 1418151 = 2127227) B2127227
theorem B7283629 : Blo 1417528 7283629 := bstep (se 3 (by rfl) ⟨1365680, by rfl⟩ : syracuseStep 7283629 = 2731361) B2731361
theorem B1418235 : Blo 1417528 1418235 := bstep (se 1 (by rfl) ⟨1063676, by rfl⟩ : syracuseStep 1418235 = 2127353) B2127353
theorem B7775257 : Blo 1417528 7775257 := bstep (se 2 (by rfl) ⟨2915721, by rfl⟩ : syracuseStep 7775257 = 5831443) B5831443
theorem B1418303 : Blo 1417528 1418303 := bstep (se 1 (by rfl) ⟨1063727, by rfl⟩ : syracuseStep 1418303 = 2127455) B2127455
theorem B1418447 : Blo 1417528 1418447 := bstep (se 1 (by rfl) ⟨1063835, by rfl⟩ : syracuseStep 1418447 = 2127671) B2127671
theorem B1795279 : Blo 1417528 1795279 := bstep (se 1 (by rfl) ⟨1346459, by rfl⟩ : syracuseStep 1795279 = 2692919) B2692919
theorem B2393435 : Blo 1417528 2393435 := bstep (se 1 (by rfl) ⟨1795076, by rfl⟩ : syracuseStep 2393435 = 3590153) B3590153
theorem B8078687 : Blo 1417528 8078687 := bstep (se 1 (by rfl) ⟨6059015, by rfl⟩ : syracuseStep 8078687 = 12118031) B12118031
theorem B1418651 : Blo 1417528 1418651 := bstep (se 1 (by rfl) ⟨1063988, by rfl⟩ : syracuseStep 1418651 = 2127977) B2127977
theorem B13641209 : Blo 1417528 13641209 := bstep (se 2 (by rfl) ⟨5115453, by rfl⟩ : syracuseStep 13641209 = 10230907) B10230907
theorem B6563321 : Blo 1417528 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B3409427 : Blo 1417528 3409427 := bstep (se 1 (by rfl) ⟨2557070, by rfl⟩ : syracuseStep 3409427 = 5114141) B5114141
theorem B2393671 : Blo 1417528 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B1418863 : Blo 1417528 1418863 := bstep (se 1 (by rfl) ⟨1064147, by rfl⟩ : syracuseStep 1418863 = 2128295) B2128295
theorem B30680693 : Blo 1417528 30680693 := bstep (se 5 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 30680693 = 2876315) B2876315
theorem B3237497 : Blo 1417528 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B5383847 : Blo 1417528 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B1418919 : Blo 1417528 1418919 := bstep (se 1 (by rfl) ⟨1064189, by rfl⟩ : syracuseStep 1418919 = 2128379) B2128379
theorem B2426591 : Blo 1417528 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B1419003 : Blo 1417528 1419003 := bstep (se 1 (by rfl) ⟨1064252, by rfl⟩ : syracuseStep 1419003 = 2128505) B2128505
theorem B2393887 : Blo 1417528 2393887 := bstep (se 1 (by rfl) ⟨1795415, by rfl⟩ : syracuseStep 2393887 = 3590831) B3590831
theorem B1795871 : Blo 1417528 1795871 := bstep (se 1 (by rfl) ⟨1346903, by rfl⟩ : syracuseStep 1795871 = 2693807) B2693807
theorem B1419039 : Blo 1417528 1419039 := bstep (se 1 (by rfl) ⟨1064279, by rfl⟩ : syracuseStep 1419039 = 2128559) B2128559
theorem B1419071 : Blo 1417528 1419071 := bstep (se 1 (by rfl) ⟨1064303, by rfl⟩ : syracuseStep 1419071 = 2128607) B2128607
theorem B1419247 : Blo 1417528 1419247 := bstep (se 1 (by rfl) ⟨1064435, by rfl⟩ : syracuseStep 1419247 = 2128871) B2128871
theorem B2394103 : Blo 1417528 2394103 := bstep (se 1 (by rfl) ⟨1795577, by rfl⟩ : syracuseStep 2394103 = 3591155) B3591155
theorem B1796251 : Blo 1417528 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B1419419 : Blo 1417528 1419419 := bstep (se 1 (by rfl) ⟨1064564, by rfl⟩ : syracuseStep 1419419 = 2129129) B2129129
theorem B1419455 : Blo 1417528 1419455 := bstep (se 1 (by rfl) ⟨1064591, by rfl⟩ : syracuseStep 1419455 = 2129183) B2129183
theorem B9087191 : Blo 1417528 9087191 := bstep (se 1 (by rfl) ⟨6815393, by rfl⟩ : syracuseStep 9087191 = 13630787) B13630787
theorem B10504487 : Blo 1417528 10504487 := bstep (se 1 (by rfl) ⟨7878365, by rfl⟩ : syracuseStep 10504487 = 15756731) B15756731
theorem B2394407 : Blo 1417528 2394407 := bstep (se 1 (by rfl) ⟨1795805, by rfl⟩ : syracuseStep 2394407 = 3591611) B3591611
theorem B7178543 : Blo 1417528 7178543 := bstep (se 1 (by rfl) ⟨5383907, by rfl⟩ : syracuseStep 7178543 = 10767815) B10767815
theorem B10217785 : Blo 1417528 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B20449817 : Blo 1417528 20449817 := bstep (se 2 (by rfl) ⟨7668681, by rfl⟩ : syracuseStep 20449817 = 15337363) B15337363
theorem B10226321 : Blo 1417528 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B20458291 : Blo 1417528 20458291 := bstep (se 1 (by rfl) ⟨15343718, by rfl⟩ : syracuseStep 20458291 = 30687437) B30687437
theorem B18189143 : Blo 1417528 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B13634477 : Blo 1417528 13634477 := bstep (se 3 (by rfl) ⟨2556464, by rfl⟩ : syracuseStep 13634477 = 5112929) B5112929
theorem B2395183 : Blo 1417528 2395183 := bstep (se 1 (by rfl) ⟨1796387, by rfl⟩ : syracuseStep 2395183 = 3592775) B3592775
theorem B9710735 : Blo 1417528 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B4787423 : Blo 1417528 4787423 := bstep (se 1 (by rfl) ⟨3590567, by rfl⟩ : syracuseStep 4787423 = 7181135) B7181135
theorem B3591449 : Blo 1417528 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B13626787 : Blo 1417528 13626787 := bstep (se 1 (by rfl) ⟨10220090, by rfl⟩ : syracuseStep 13626787 = 20440181) B20440181
theorem B4787639 : Blo 1417528 4787639 := bstep (se 1 (by rfl) ⟨3590729, by rfl⟩ : syracuseStep 4787639 = 7181459) B7181459
theorem B8080829 : Blo 1417528 8080829 := bstep (se 3 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 8080829 = 3030311) B3030311
theorem B5115383 : Blo 1417528 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B7179839 : Blo 1417528 7179839 := bstep (se 1 (by rfl) ⟨5384879, by rfl⟩ : syracuseStep 7179839 = 10769759) B10769759
theorem B18190169 : Blo 1417528 18190169 := bstep (se 2 (by rfl) ⟨6821313, by rfl⟩ : syracuseStep 18190169 = 13642627) B13642627
theorem B7278457 : Blo 1417528 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B15331265 : Blo 1417528 15331265 := bstep (se 2 (by rfl) ⟨5749224, by rfl⟩ : syracuseStep 15331265 = 11498449) B11498449
theorem B3190751 : Blo 1417528 3190751 := bstep (se 1 (by rfl) ⟨2393063, by rfl⟩ : syracuseStep 3190751 = 4786127) B4786127
theorem B10776563 : Blo 1417528 10776563 := bstep (se 1 (by rfl) ⟨8082422, by rfl⟩ : syracuseStep 10776563 = 16164845) B16164845
theorem B8622233 : Blo 1417528 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B168112417 : Blo 1417528 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B8073539 : Blo 1417528 8073539 := bstep (se 1 (by rfl) ⟨6055154, by rfl⟩ : syracuseStep 8073539 = 12110309) B12110309
theorem B29495659 : Blo 1417528 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B20443529 : Blo 1417528 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B3191399 : Blo 1417528 3191399 := bstep (se 1 (by rfl) ⟨2393549, by rfl⟩ : syracuseStep 3191399 = 4787099) B4787099
theorem B3641959 : Blo 1417528 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B2126633 : Blo 1417528 2126633 := bstep (se 2 (by rfl) ⟨797487, by rfl⟩ : syracuseStep 2126633 = 1594975) B1594975
theorem B2126639 : Blo 1417528 2126639 := bstep (se 1 (by rfl) ⟨1594979, by rfl⟩ : syracuseStep 2126639 = 3189959) B3189959
theorem B4854589 : Blo 1417528 4854589 := bstep (se 3 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 4854589 = 1820471) B1820471
theorem B2126759 : Blo 1417528 2126759 := bstep (se 1 (by rfl) ⟨1595069, by rfl⟩ : syracuseStep 2126759 = 3190139) B3190139
theorem B2126843 : Blo 1417528 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B2692091 : Blo 1417528 2692091 := bstep (se 1 (by rfl) ⟨2019068, by rfl⟩ : syracuseStep 2692091 = 4038137) B4038137
theorem B2126903 : Blo 1417528 2126903 := bstep (se 1 (by rfl) ⟨1595177, by rfl⟩ : syracuseStep 2126903 = 3190355) B3190355
theorem B8074313 : Blo 1417528 8074313 := bstep (se 2 (by rfl) ⟨3027867, by rfl⟩ : syracuseStep 8074313 = 6055735) B6055735
theorem B12112973 : Blo 1417528 12112973 := bstep (se 3 (by rfl) ⟨2271182, by rfl⟩ : syracuseStep 12112973 = 4542365) B4542365
theorem B2127023 : Blo 1417528 2127023 := bstep (se 1 (by rfl) ⟨1595267, by rfl⟩ : syracuseStep 2127023 = 3190535) B3190535
theorem B3192083 : Blo 1417528 3192083 := bstep (se 1 (by rfl) ⟨2394062, by rfl⟩ : syracuseStep 3192083 = 4788125) B4788125
theorem B3192155 : Blo 1417528 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B6059393 : Blo 1417528 6059393 := bstep (se 2 (by rfl) ⟨2272272, by rfl⟩ : syracuseStep 6059393 = 4544545) B4544545
theorem B4789691 : Blo 1417528 4789691 := bstep (se 1 (by rfl) ⟨3592268, by rfl⟩ : syracuseStep 4789691 = 7184537) B7184537
theorem B2692577 : Blo 1417528 2692577 := bstep (se 2 (by rfl) ⟨1009716, by rfl⟩ : syracuseStep 2692577 = 2019433) B2019433
theorem B6911497 : Blo 1417528 6911497 := bstep (se 2 (by rfl) ⟨2591811, by rfl⟩ : syracuseStep 6911497 = 5183623) B5183623
theorem B2127431 : Blo 1417528 2127431 := bstep (se 1 (by rfl) ⟨1595573, by rfl⟩ : syracuseStep 2127431 = 3191147) B3191147
theorem B13293179 : Blo 1417528 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B1595047 : Blo 1417528 1595047 := bstep (se 1 (by rfl) ⟨1196285, by rfl⟩ : syracuseStep 1595047 = 2392571) B2392571
theorem B2127527 : Blo 1417528 2127527 := bstep (se 1 (by rfl) ⟨1595645, by rfl⟩ : syracuseStep 2127527 = 3191291) B3191291
theorem B2127611 : Blo 1417528 2127611 := bstep (se 1 (by rfl) ⟨1595708, by rfl⟩ : syracuseStep 2127611 = 3191417) B3191417
theorem B2127647 : Blo 1417528 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B2127695 : Blo 1417528 2127695 := bstep (se 1 (by rfl) ⟨1595771, by rfl⟩ : syracuseStep 2127695 = 3191543) B3191543
theorem B3192713 : Blo 1417528 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B1595335 : Blo 1417528 1595335 := bstep (se 1 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 1595335 = 2393003) B2393003
theorem B2127815 : Blo 1417528 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B4790231 : Blo 1417528 4790231 := bstep (se 1 (by rfl) ⟨3592673, by rfl⟩ : syracuseStep 4790231 = 7185347) B7185347
theorem B7182431 : Blo 1417528 7182431 := bstep (se 1 (by rfl) ⟨5386823, by rfl⟩ : syracuseStep 7182431 = 10773647) B10773647
theorem B3192929 : Blo 1417528 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B8075497 : Blo 1417528 8075497 := bstep (se 2 (by rfl) ⟨3028311, by rfl⟩ : syracuseStep 8075497 = 6056623) B6056623
theorem B10926373 : Blo 1417528 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B2128169 : Blo 1417528 2128169 := bstep (se 2 (by rfl) ⟨798063, by rfl⟩ : syracuseStep 2128169 = 1596127) B1596127
theorem B1595695 : Blo 1417528 1595695 := bstep (se 1 (by rfl) ⟨1196771, by rfl⟩ : syracuseStep 1595695 = 2393543) B2393543
theorem B2128175 : Blo 1417528 2128175 := bstep (se 1 (by rfl) ⟨1596131, by rfl⟩ : syracuseStep 2128175 = 3192263) B3192263
theorem B4790717 : Blo 1417528 4790717 := bstep (se 3 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 4790717 = 1796519) B1796519
theorem B2128415 : Blo 1417528 2128415 := bstep (se 1 (by rfl) ⟨1596311, by rfl⟩ : syracuseStep 2128415 = 3192623) B3192623
theorem B5110609 : Blo 1417528 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B2128799 : Blo 1417528 2128799 := bstep (se 1 (by rfl) ⟨1596599, by rfl⟩ : syracuseStep 2128799 = 3193199) B3193199
theorem B2128847 : Blo 1417528 2128847 := bstep (se 1 (by rfl) ⟨1596635, by rfl⟩ : syracuseStep 2128847 = 3193271) B3193271
theorem B10222631 : Blo 1417528 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B2128937 : Blo 1417528 2128937 := bstep (se 2 (by rfl) ⟨798351, by rfl⟩ : syracuseStep 2128937 = 1596703) B1596703
theorem B2128943 : Blo 1417528 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B44850233 : Blo 1417528 44850233 := bstep (se 2 (by rfl) ⟨16818837, by rfl⟩ : syracuseStep 44850233 = 33637675) B33637675
theorem B1596487 : Blo 1417528 1596487 := bstep (se 1 (by rfl) ⟨1197365, by rfl⟩ : syracuseStep 1596487 = 2394731) B2394731
theorem B2128967 : Blo 1417528 2128967 := bstep (se 1 (by rfl) ⟨1596725, by rfl⟩ : syracuseStep 2128967 = 3193451) B3193451
theorem B13630751 : Blo 1417528 13630751 := bstep (se 1 (by rfl) ⟨10223063, by rfl⟩ : syracuseStep 13630751 = 20446127) B20446127
theorem B2129231 : Blo 1417528 2129231 := bstep (se 1 (by rfl) ⟨1596923, by rfl⟩ : syracuseStep 2129231 = 3193847) B3193847
theorem B7183727 : Blo 1417528 7183727 := bstep (se 1 (by rfl) ⟨5387795, by rfl⟩ : syracuseStep 7183727 = 10775591) B10775591
theorem B2874791 : Blo 1417528 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B6307283 : Blo 1417528 6307283 := bstep (se 1 (by rfl) ⟨4730462, by rfl⟩ : syracuseStep 6307283 = 9460925) B9460925
theorem B8076773 : Blo 1417528 8076773 := bstep (se 4 (by rfl) ⟨757197, by rfl⟩ : syracuseStep 8076773 = 1514395) B1514395
theorem B28032655 : Blo 1417528 28032655 := bstep (se 1 (by rfl) ⟨21024491, by rfl⟩ : syracuseStep 28032655 = 42048983) B42048983
theorem B7274231 : Blo 1417528 7274231 := bstep (se 1 (by rfl) ⟨5455673, by rfl⟩ : syracuseStep 7274231 = 10911347) B10911347
theorem B2555687 : Blo 1417528 2555687 := bstep (se 1 (by rfl) ⟨1916765, by rfl⟩ : syracuseStep 2555687 = 3833531) B3833531
theorem B4546493 : Blo 1417528 4546493 := bstep (se 3 (by rfl) ⟨852467, by rfl⟩ : syracuseStep 4546493 = 1704935) B1704935
theorem B7274681 : Blo 1417528 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B5382359 : Blo 1417528 5382359 := bstep (se 1 (by rfl) ⟨4036769, by rfl⟩ : syracuseStep 5382359 = 8073539) B8073539
theorem B224149889 : Blo 1417528 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B13623713 : Blo 1417528 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B1417755 : Blo 1417528 1417755 := bstep (se 1 (by rfl) ⟨1063316, by rfl⟩ : syracuseStep 1417755 = 2126633) B2126633
theorem B1417759 : Blo 1417528 1417759 := bstep (se 1 (by rfl) ⟨1063319, by rfl⟩ : syracuseStep 1417759 = 2126639) B2126639
theorem B1417839 : Blo 1417528 1417839 := bstep (se 1 (by rfl) ⟨1063379, by rfl⟩ : syracuseStep 1417839 = 2126759) B2126759
theorem B1417895 : Blo 1417528 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B1794727 : Blo 1417528 1794727 := bstep (se 1 (by rfl) ⟨1346045, by rfl⟩ : syracuseStep 1794727 = 2692091) B2692091
theorem B1417935 : Blo 1417528 1417935 := bstep (se 1 (by rfl) ⟨1063451, by rfl⟩ : syracuseStep 1417935 = 2126903) B2126903
theorem B5382875 : Blo 1417528 5382875 := bstep (se 1 (by rfl) ⟨4037156, by rfl⟩ : syracuseStep 5382875 = 8074313) B8074313
theorem B1418015 : Blo 1417528 1418015 := bstep (se 1 (by rfl) ⟨1063511, by rfl⟩ : syracuseStep 1418015 = 2127023) B2127023
theorem B4039595 : Blo 1417528 4039595 := bstep (se 1 (by rfl) ⟨3029696, by rfl⟩ : syracuseStep 4039595 = 6059393) B6059393
theorem B1795051 : Blo 1417528 1795051 := bstep (se 1 (by rfl) ⟨1346288, by rfl⟩ : syracuseStep 1795051 = 2692577) B2692577
theorem B9094139 : Blo 1417528 9094139 := bstep (se 1 (by rfl) ⟨6820604, by rfl⟩ : syracuseStep 9094139 = 13641209) B13641209
theorem B4375547 : Blo 1417528 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1418287 : Blo 1417528 1418287 := bstep (se 1 (by rfl) ⟨1063715, by rfl⟩ : syracuseStep 1418287 = 2127431) B2127431
theorem B3589231 : Blo 1417528 3589231 := bstep (se 1 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 3589231 = 5383847) B5383847
theorem B1418351 : Blo 1417528 1418351 := bstep (se 1 (by rfl) ⟨1063763, by rfl⟩ : syracuseStep 1418351 = 2127527) B2127527
theorem B1418407 : Blo 1417528 1418407 := bstep (se 1 (by rfl) ⟨1063805, by rfl⟩ : syracuseStep 1418407 = 2127611) B2127611
theorem B1418431 : Blo 1417528 1418431 := bstep (se 1 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 1418431 = 2127647) B2127647
theorem B1418463 : Blo 1417528 1418463 := bstep (se 1 (by rfl) ⟨1063847, by rfl⟩ : syracuseStep 1418463 = 2127695) B2127695
theorem B103564565 : Blo 1417528 103564565 := bstep (se 6 (by rfl) ⟨2427294, by rfl⟩ : syracuseStep 103564565 = 4854589) B4854589
theorem B1418543 : Blo 1417528 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B103581173 : Blo 1417528 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B1418779 : Blo 1417528 1418779 := bstep (se 1 (by rfl) ⟨1064084, by rfl⟩ : syracuseStep 1418779 = 2128169) B2128169
theorem B4785695 : Blo 1417528 4785695 := bstep (se 1 (by rfl) ⟨3589271, by rfl⟩ : syracuseStep 4785695 = 7178543) B7178543
theorem B1418783 : Blo 1417528 1418783 := bstep (se 1 (by rfl) ⟨1064087, by rfl⟩ : syracuseStep 1418783 = 2128175) B2128175
theorem B2393705 : Blo 1417528 2393705 := bstep (se 2 (by rfl) ⟨897639, by rfl⟩ : syracuseStep 2393705 = 1795279) B1795279
theorem B13633211 : Blo 1417528 13633211 := bstep (se 1 (by rfl) ⟨10224908, by rfl⟩ : syracuseStep 13633211 = 20449817) B20449817
theorem B1418943 : Blo 1417528 1418943 := bstep (se 1 (by rfl) ⟨1064207, by rfl⟩ : syracuseStep 1418943 = 2128415) B2128415
theorem B6817547 : Blo 1417528 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B12126095 : Blo 1417528 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B1419199 : Blo 1417528 1419199 := bstep (se 1 (by rfl) ⟨1064399, by rfl⟩ : syracuseStep 1419199 = 2128799) B2128799
theorem B1419231 : Blo 1417528 1419231 := bstep (se 1 (by rfl) ⟨1064423, by rfl⟩ : syracuseStep 1419231 = 2128847) B2128847
theorem B1419291 : Blo 1417528 1419291 := bstep (se 1 (by rfl) ⟨1064468, by rfl⟩ : syracuseStep 1419291 = 2128937) B2128937
theorem B1419295 : Blo 1417528 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B1419311 : Blo 1417528 1419311 := bstep (se 1 (by rfl) ⟨1064483, by rfl⟩ : syracuseStep 1419311 = 2128967) B2128967
theorem B2394299 : Blo 1417528 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B9087167 : Blo 1417528 9087167 := bstep (se 1 (by rfl) ⟨6815375, by rfl⟩ : syracuseStep 9087167 = 13630751) B13630751
theorem B1419487 : Blo 1417528 1419487 := bstep (se 1 (by rfl) ⟨1064615, by rfl⟩ : syracuseStep 1419487 = 2129231) B2129231
theorem B4204855 : Blo 1417528 4204855 := bstep (se 1 (by rfl) ⟨3153641, by rfl⟩ : syracuseStep 4204855 = 6307283) B6307283
theorem B5384515 : Blo 1417528 5384515 := bstep (se 1 (by rfl) ⟨4038386, by rfl⟩ : syracuseStep 5384515 = 8076773) B8076773
theorem B3410255 : Blo 1417528 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B4786559 : Blo 1417528 4786559 := bstep (se 1 (by rfl) ⟨3589919, by rfl⟩ : syracuseStep 4786559 = 7179839) B7179839
theorem B12126779 : Blo 1417528 12126779 := bstep (se 1 (by rfl) ⟨9095084, by rfl⟩ : syracuseStep 12126779 = 18190169) B18190169
theorem B2395001 : Blo 1417528 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B10767329 : Blo 1417528 10767329 := bstep (se 2 (by rfl) ⟨4037748, by rfl⟩ : syracuseStep 10767329 = 8075497) B8075497
theorem B14568497 : Blo 1417528 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B3189833 : Blo 1417528 3189833 := bstep (se 2 (by rfl) ⟨1196187, by rfl⟩ : syracuseStep 3189833 = 2392375) B2392375
theorem B5385791 : Blo 1417528 5385791 := bstep (se 1 (by rfl) ⟨4039343, by rfl⟩ : syracuseStep 5385791 = 8078687) B8078687
theorem B2272951 : Blo 1417528 2272951 := bstep (se 1 (by rfl) ⟨1704713, by rfl⟩ : syracuseStep 2272951 = 3409427) B3409427
theorem B2158331 : Blo 1417528 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B1617727 : Blo 1417528 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B9711505 : Blo 1417528 9711505 := bstep (se 2 (by rfl) ⟨3641814, by rfl⟩ : syracuseStep 9711505 = 7283629) B7283629
theorem B10367009 : Blo 1417528 10367009 := bstep (se 2 (by rfl) ⟨3887628, by rfl⟩ : syracuseStep 10367009 = 7775257) B7775257
theorem B4788287 : Blo 1417528 4788287 := bstep (se 1 (by rfl) ⟨3591215, by rfl⟩ : syracuseStep 4788287 = 7182431) B7182431
theorem B6058127 : Blo 1417528 6058127 := bstep (se 1 (by rfl) ⟨4543595, by rfl⟩ : syracuseStep 6058127 = 9087191) B9087191
theorem B9089651 : Blo 1417528 9089651 := bstep (se 1 (by rfl) ⟨6817238, by rfl⟩ : syracuseStep 9089651 = 13634477) B13634477
theorem B4788989 : Blo 1417528 4788989 := bstep (se 3 (by rfl) ⟨897935, by rfl⟩ : syracuseStep 4788989 = 1795871) B1795871
theorem B3191561 : Blo 1417528 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B3191615 : Blo 1417528 3191615 := bstep (se 1 (by rfl) ⟨2393711, by rfl⟩ : syracuseStep 3191615 = 4787423) B4787423
theorem B37376873 : Blo 1417528 37376873 := bstep (se 2 (by rfl) ⟨14016327, by rfl⟩ : syracuseStep 37376873 = 28032655) B28032655
theorem B2126729 : Blo 1417528 2126729 := bstep (se 2 (by rfl) ⟨797523, by rfl⟩ : syracuseStep 2126729 = 1595047) B1595047
theorem B4789151 : Blo 1417528 4789151 := bstep (se 1 (by rfl) ⟨3591863, by rfl⟩ : syracuseStep 4789151 = 7183727) B7183727
theorem B3191759 : Blo 1417528 3191759 := bstep (se 1 (by rfl) ⟨2393819, by rfl⟩ : syracuseStep 3191759 = 4787639) B4787639
theorem B5387219 : Blo 1417528 5387219 := bstep (se 1 (by rfl) ⟨4040414, by rfl⟩ : syracuseStep 5387219 = 8080829) B8080829
theorem B3191849 : Blo 1417528 3191849 := bstep (se 2 (by rfl) ⟨1196943, by rfl⟩ : syracuseStep 3191849 = 2393887) B2393887
theorem B9704609 : Blo 1417528 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B2127113 : Blo 1417528 2127113 := bstep (se 2 (by rfl) ⟨797667, by rfl⟩ : syracuseStep 2127113 = 1595335) B1595335
theorem B10220843 : Blo 1417528 10220843 := bstep (se 1 (by rfl) ⟨7665632, by rfl⟩ : syracuseStep 10220843 = 15331265) B15331265
theorem B2127167 : Blo 1417528 2127167 := bstep (se 1 (by rfl) ⟨1595375, by rfl⟩ : syracuseStep 2127167 = 3190751) B3190751
theorem B3192137 : Blo 1417528 3192137 := bstep (se 2 (by rfl) ⟨1197051, by rfl⟩ : syracuseStep 3192137 = 2394103) B2394103
theorem B36861317 : Blo 1417528 36861317 := bstep (se 4 (by rfl) ⟨3455748, by rfl⟩ : syracuseStep 36861317 = 6911497) B6911497
theorem B5748155 : Blo 1417528 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B119600621 : Blo 1417528 119600621 := bstep (se 3 (by rfl) ⟨22425116, by rfl⟩ : syracuseStep 119600621 = 44850233) B44850233
theorem B13629019 : Blo 1417528 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B2127593 : Blo 1417528 2127593 := bstep (se 2 (by rfl) ⟨797847, by rfl⟩ : syracuseStep 2127593 = 1595695) B1595695
theorem B5461739 : Blo 1417528 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B1595119 : Blo 1417528 1595119 := bstep (se 1 (by rfl) ⟨1196339, by rfl⟩ : syracuseStep 1595119 = 2392679) B2392679
theorem B2127599 : Blo 1417528 2127599 := bstep (se 1 (by rfl) ⟨1595699, by rfl⟩ : syracuseStep 2127599 = 3191399) B3191399
theorem B39327545 : Blo 1417528 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B1595227 : Blo 1417528 1595227 := bstep (se 1 (by rfl) ⟨1196420, by rfl⟩ : syracuseStep 1595227 = 2392841) B2392841
theorem B12933053 : Blo 1417528 12933053 := bstep (se 3 (by rfl) ⟨2424947, by rfl⟩ : syracuseStep 12933053 = 4849895) B4849895
theorem B8075315 : Blo 1417528 8075315 := bstep (se 1 (by rfl) ⟨6056486, by rfl⟩ : syracuseStep 8075315 = 12112973) B12112973
theorem B4855945 : Blo 1417528 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B2128055 : Blo 1417528 2128055 := bstep (se 1 (by rfl) ⟨1596041, by rfl⟩ : syracuseStep 2128055 = 3192083) B3192083
theorem B1595623 : Blo 1417528 1595623 := bstep (se 1 (by rfl) ⟨1196717, by rfl⟩ : syracuseStep 1595623 = 2393435) B2393435
theorem B2128103 : Blo 1417528 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B3193127 : Blo 1417528 3193127 := bstep (se 1 (by rfl) ⟨2394845, by rfl⟩ : syracuseStep 3193127 = 4789691) B4789691
theorem B27277721 : Blo 1417528 27277721 := bstep (se 2 (by rfl) ⟨10229145, by rfl⟩ : syracuseStep 27277721 = 20458291) B20458291
theorem B20453795 : Blo 1417528 20453795 := bstep (se 1 (by rfl) ⟨15340346, by rfl⟩ : syracuseStep 20453795 = 30680693) B30680693
theorem B8862119 : Blo 1417528 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B7666109 : Blo 1417528 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B6814145 : Blo 1417528 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B2128475 : Blo 1417528 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B3193487 : Blo 1417528 3193487 := bstep (se 1 (by rfl) ⟨2395115, by rfl⟩ : syracuseStep 3193487 = 4790231) B4790231
theorem B3193577 : Blo 1417528 3193577 := bstep (se 2 (by rfl) ⟨1197591, by rfl⟩ : syracuseStep 3193577 = 2395183) B2395183
theorem B2128619 : Blo 1417528 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B2128649 : Blo 1417528 2128649 := bstep (se 2 (by rfl) ⟨798243, by rfl⟩ : syracuseStep 2128649 = 1596487) B1596487
theorem B7002991 : Blo 1417528 7002991 := bstep (se 1 (by rfl) ⟨5252243, by rfl⟩ : syracuseStep 7002991 = 10504487) B10504487
theorem B1596271 : Blo 1417528 1596271 := bstep (se 1 (by rfl) ⟨1197203, by rfl⟩ : syracuseStep 1596271 = 2394407) B2394407
theorem B3193811 : Blo 1417528 3193811 := bstep (se 1 (by rfl) ⟨2395358, by rfl⟩ : syracuseStep 3193811 = 4790717) B4790717
theorem B18169049 : Blo 1417528 18169049 := bstep (se 2 (by rfl) ⟨6813393, by rfl⟩ : syracuseStep 18169049 = 13626787) B13626787
theorem B6815087 : Blo 1417528 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B4849487 : Blo 1417528 4849487 := bstep (se 1 (by rfl) ⟨3637115, by rfl⟩ : syracuseStep 4849487 = 7274231) B7274231
theorem B1703791 : Blo 1417528 1703791 := bstep (se 1 (by rfl) ⟨1277843, by rfl⟩ : syracuseStep 1703791 = 2555687) B2555687
theorem B3030995 : Blo 1417528 3030995 := bstep (se 1 (by rfl) ⟨2273246, by rfl⟩ : syracuseStep 3030995 = 4546493) B4546493
theorem B7184375 : Blo 1417528 7184375 := bstep (se 1 (by rfl) ⟨5388281, by rfl⟩ : syracuseStep 7184375 = 10776563) B10776563
theorem B4038751 : Blo 1417528 4038751 := bstep (se 1 (by rfl) ⟨3029063, by rfl⟩ : syracuseStep 4038751 = 6058127) B6058127
theorem B4849787 : Blo 1417528 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B3588239 : Blo 1417528 3588239 := bstep (se 1 (by rfl) ⟨2691179, by rfl⟩ : syracuseStep 3588239 = 5382359) B5382359
theorem B3588583 : Blo 1417528 3588583 := bstep (se 1 (by rfl) ⟨2691437, by rfl⟩ : syracuseStep 3588583 = 5382875) B5382875
theorem B1417819 : Blo 1417528 1417819 := bstep (se 1 (by rfl) ⟨1063364, by rfl⟩ : syracuseStep 1417819 = 2126729) B2126729
theorem B6062759 : Blo 1417528 6062759 := bstep (se 1 (by rfl) ⟨4547069, by rfl⟩ : syracuseStep 6062759 = 9094139) B9094139
theorem B2917031 : Blo 1417528 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B1418075 : Blo 1417528 1418075 := bstep (se 1 (by rfl) ⟨1063556, by rfl⟩ : syracuseStep 1418075 = 2127113) B2127113
theorem B69043043 : Blo 1417528 69043043 := bstep (se 1 (by rfl) ⟨51782282, by rfl⟩ : syracuseStep 69043043 = 103564565) B103564565
theorem B1418111 : Blo 1417528 1418111 := bstep (se 1 (by rfl) ⟨1063583, by rfl⟩ : syracuseStep 1418111 = 2127167) B2127167
theorem B2392969 : Blo 1417528 2392969 := bstep (se 2 (by rfl) ⟨897363, by rfl⟩ : syracuseStep 2392969 = 1794727) B1794727
theorem B79733747 : Blo 1417528 79733747 := bstep (se 1 (by rfl) ⟨59800310, by rfl⟩ : syracuseStep 79733747 = 119600621) B119600621
theorem B1418395 : Blo 1417528 1418395 := bstep (se 1 (by rfl) ⟨1063796, by rfl⟩ : syracuseStep 1418395 = 2127593) B2127593
theorem B1418399 : Blo 1417528 1418399 := bstep (se 1 (by rfl) ⟨1063799, by rfl⟩ : syracuseStep 1418399 = 2127599) B2127599
theorem B18171053 : Blo 1417528 18171053 := bstep (se 3 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 18171053 = 6814145) B6814145
theorem B2393401 : Blo 1417528 2393401 := bstep (se 2 (by rfl) ⟨897525, by rfl⟩ : syracuseStep 2393401 = 1795051) B1795051
theorem B5383543 : Blo 1417528 5383543 := bstep (se 1 (by rfl) ⟨4037657, by rfl⟩ : syracuseStep 5383543 = 8075315) B8075315
theorem B1418703 : Blo 1417528 1418703 := bstep (se 1 (by rfl) ⟨1064027, by rfl⟩ : syracuseStep 1418703 = 2128055) B2128055
theorem B4785641 : Blo 1417528 4785641 := bstep (se 2 (by rfl) ⟨1794615, by rfl⟩ : syracuseStep 4785641 = 3589231) B3589231
theorem B1418735 : Blo 1417528 1418735 := bstep (se 1 (by rfl) ⟨1064051, by rfl⟩ : syracuseStep 1418735 = 2128103) B2128103
theorem B5908079 : Blo 1417528 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B1418983 : Blo 1417528 1418983 := bstep (se 1 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 1418983 = 2128475) B2128475
theorem B1419079 : Blo 1417528 1419079 := bstep (se 1 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 1419079 = 2128619) B2128619
theorem B1419099 : Blo 1417528 1419099 := bstep (se 1 (by rfl) ⟨1064324, by rfl⟩ : syracuseStep 1419099 = 2128649) B2128649
theorem B7178219 : Blo 1417528 7178219 := bstep (se 1 (by rfl) ⟨5383664, by rfl⟩ : syracuseStep 7178219 = 10767329) B10767329
theorem B18172025 : Blo 1417528 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B3590527 : Blo 1417528 3590527 := bstep (se 1 (by rfl) ⟨2692895, by rfl⟩ : syracuseStep 3590527 = 5385791) B5385791
theorem B2156969 : Blo 1417528 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B2271721 : Blo 1417528 2271721 := bstep (se 2 (by rfl) ⟨851895, by rfl⟩ : syracuseStep 2271721 = 1703791) B1703791
theorem B6474593 : Blo 1417528 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B7179353 : Blo 1417528 7179353 := bstep (se 2 (by rfl) ⟨2692257, by rfl⟩ : syracuseStep 7179353 = 5384515) B5384515
theorem B3591479 : Blo 1417528 3591479 := bstep (se 1 (by rfl) ⟨2693609, by rfl⟩ : syracuseStep 3591479 = 5387219) B5387219
theorem B69054115 : Blo 1417528 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B597733037 : Blo 1417528 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B3190463 : Blo 1417528 3190463 := bstep (se 1 (by rfl) ⟨2392847, by rfl⟩ : syracuseStep 3190463 = 4785695) B4785695
theorem B9088807 : Blo 1417528 9088807 := bstep (se 1 (by rfl) ⟨6816605, by rfl⟩ : syracuseStep 9088807 = 13633211) B13633211
theorem B3641159 : Blo 1417528 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B8622035 : Blo 1417528 8622035 := bstep (se 1 (by rfl) ⟨6466526, by rfl⟩ : syracuseStep 8622035 = 12933053) B12933053
theorem B6058111 : Blo 1417528 6058111 := bstep (se 1 (by rfl) ⟨4543583, by rfl⟩ : syracuseStep 6058111 = 9087167) B9087167
theorem B2273503 : Blo 1417528 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B3191039 : Blo 1417528 3191039 := bstep (se 1 (by rfl) ⟨2393279, by rfl⟩ : syracuseStep 3191039 = 4786559) B4786559
theorem B13635863 : Blo 1417528 13635863 := bstep (se 1 (by rfl) ⟨10226897, by rfl⟩ : syracuseStep 13635863 = 20453795) B20453795
theorem B22425893 : Blo 1417528 22425893 := bstep (se 4 (by rfl) ⟨2102427, by rfl⟩ : syracuseStep 22425893 = 4204855) B4204855
theorem B5755549 : Blo 1417528 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B9712331 : Blo 1417528 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B2126555 : Blo 1417528 2126555 := bstep (se 1 (by rfl) ⟨1594916, by rfl⟩ : syracuseStep 2126555 = 3189833) B3189833
theorem B12112699 : Blo 1417528 12112699 := bstep (se 1 (by rfl) ⟨9084524, by rfl⟩ : syracuseStep 12112699 = 18169049) B18169049
theorem B4543391 : Blo 1417528 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B2126825 : Blo 1417528 2126825 := bstep (se 2 (by rfl) ⟨797559, by rfl⟩ : syracuseStep 2126825 = 1595119) B1595119
theorem B2126969 : Blo 1417528 2126969 := bstep (se 2 (by rfl) ⟨797613, by rfl⟩ : syracuseStep 2126969 = 1595227) B1595227
theorem B12948673 : Blo 1417528 12948673 := bstep (se 2 (by rfl) ⟨4855752, by rfl⟩ : syracuseStep 12948673 = 9711505) B9711505
theorem B3232991 : Blo 1417528 3232991 := bstep (se 1 (by rfl) ⟨2424743, by rfl⟩ : syracuseStep 3232991 = 4849487) B4849487
theorem B2020663 : Blo 1417528 2020663 := bstep (se 1 (by rfl) ⟨1515497, by rfl⟩ : syracuseStep 2020663 = 3030995) B3030995
theorem B4789583 : Blo 1417528 4789583 := bstep (se 1 (by rfl) ⟨3592187, by rfl⟩ : syracuseStep 4789583 = 7184375) B7184375
theorem B6911339 : Blo 1417528 6911339 := bstep (se 1 (by rfl) ⟨5183504, by rfl⟩ : syracuseStep 6911339 = 10367009) B10367009
theorem B3192191 : Blo 1417528 3192191 := bstep (se 1 (by rfl) ⟨2394143, by rfl⟩ : syracuseStep 3192191 = 4788287) B4788287
theorem B9082475 : Blo 1417528 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B2127497 : Blo 1417528 2127497 := bstep (se 2 (by rfl) ⟨797811, by rfl⟩ : syracuseStep 2127497 = 1595623) B1595623
theorem B6059767 : Blo 1417528 6059767 := bstep (se 1 (by rfl) ⟨4544825, by rfl⟩ : syracuseStep 6059767 = 9089651) B9089651
theorem B3192659 : Blo 1417528 3192659 := bstep (se 1 (by rfl) ⟨2394494, by rfl⟩ : syracuseStep 3192659 = 4788989) B4788989
theorem B2127707 : Blo 1417528 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B2127743 : Blo 1417528 2127743 := bstep (se 1 (by rfl) ⟨1595807, by rfl⟩ : syracuseStep 2127743 = 3191615) B3191615
theorem B24917915 : Blo 1417528 24917915 := bstep (se 1 (by rfl) ⟨18688436, by rfl⟩ : syracuseStep 24917915 = 37376873) B37376873
theorem B3192767 : Blo 1417528 3192767 := bstep (se 1 (by rfl) ⟨2394575, by rfl⟩ : syracuseStep 3192767 = 4789151) B4789151
theorem B2693063 : Blo 1417528 2693063 := bstep (se 1 (by rfl) ⟨2019797, by rfl⟩ : syracuseStep 2693063 = 4039595) B4039595
theorem B2127839 : Blo 1417528 2127839 := bstep (se 1 (by rfl) ⟨1595879, by rfl⟩ : syracuseStep 2127839 = 3191759) B3191759
theorem B2127899 : Blo 1417528 2127899 := bstep (se 1 (by rfl) ⟨1595924, by rfl⟩ : syracuseStep 2127899 = 3191849) B3191849
theorem B6469739 : Blo 1417528 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B6813895 : Blo 1417528 6813895 := bstep (se 1 (by rfl) ⟨5110421, by rfl⟩ : syracuseStep 6813895 = 10220843) B10220843
theorem B2128091 : Blo 1417528 2128091 := bstep (se 1 (by rfl) ⟨1596068, by rfl⟩ : syracuseStep 2128091 = 3192137) B3192137
theorem B24574211 : Blo 1417528 24574211 := bstep (se 1 (by rfl) ⟨18430658, by rfl⟩ : syracuseStep 24574211 = 36861317) B36861317
theorem B12122405 : Blo 1417528 12122405 := bstep (se 4 (by rfl) ⟨1136475, by rfl⟩ : syracuseStep 12122405 = 2272951) B2272951
theorem B3832103 : Blo 1417528 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B1595803 : Blo 1417528 1595803 := bstep (se 1 (by rfl) ⟨1196852, by rfl⟩ : syracuseStep 1595803 = 2393705) B2393705
theorem B9337321 : Blo 1417528 9337321 := bstep (se 2 (by rfl) ⟨3501495, by rfl⟩ : syracuseStep 9337321 = 7002991) B7002991
theorem B2128361 : Blo 1417528 2128361 := bstep (se 2 (by rfl) ⟨798135, by rfl⟩ : syracuseStep 2128361 = 1596271) B1596271
theorem B4545031 : Blo 1417528 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B8084063 : Blo 1417528 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B1596199 : Blo 1417528 1596199 := bstep (se 1 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 1596199 = 2394299) B2394299
theorem B2128751 : Blo 1417528 2128751 := bstep (se 1 (by rfl) ⟨1596563, by rfl⟩ : syracuseStep 2128751 = 3193127) B3193127
theorem B18185147 : Blo 1417528 18185147 := bstep (se 1 (by rfl) ⟨13638860, by rfl⟩ : syracuseStep 18185147 = 27277721) B27277721
theorem B5110739 : Blo 1417528 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B8084519 : Blo 1417528 8084519 := bstep (se 1 (by rfl) ⟨6063389, by rfl⟩ : syracuseStep 8084519 = 12126779) B12126779
theorem B2128991 : Blo 1417528 2128991 := bstep (se 1 (by rfl) ⟨1596743, by rfl⟩ : syracuseStep 2128991 = 3193487) B3193487
theorem B2129051 : Blo 1417528 2129051 := bstep (se 1 (by rfl) ⟨1596788, by rfl⟩ : syracuseStep 2129051 = 3193577) B3193577
theorem B1596667 : Blo 1417528 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B2129207 : Blo 1417528 2129207 := bstep (se 1 (by rfl) ⟨1596905, by rfl⟩ : syracuseStep 2129207 = 3193811) B3193811
theorem B104873453 : Blo 1417528 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B2392159 : Blo 1417528 2392159 := bstep (se 1 (by rfl) ⟨1794119, by rfl⟩ : syracuseStep 2392159 = 3588239) B3588239
theorem B8077481 : Blo 1417528 8077481 := bstep (se 2 (by rfl) ⟨3029055, by rfl⟩ : syracuseStep 8077481 = 6058111) B6058111
theorem B14950595 : Blo 1417528 14950595 := bstep (se 1 (by rfl) ⟨11212946, by rfl⟩ : syracuseStep 14950595 = 22425893) B22425893
theorem B9085193 : Blo 1417528 9085193 := bstep (se 2 (by rfl) ⟨3406947, by rfl⟩ : syracuseStep 9085193 = 6813895) B6813895
theorem B3031337 : Blo 1417528 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B1417703 : Blo 1417528 1417703 := bstep (se 1 (by rfl) ⟨1063277, by rfl⟩ : syracuseStep 1417703 = 2126555) B2126555
theorem B4784777 : Blo 1417528 4784777 := bstep (se 2 (by rfl) ⟨1794291, by rfl⟩ : syracuseStep 4784777 = 3588583) B3588583
theorem B1417883 : Blo 1417528 1417883 := bstep (se 1 (by rfl) ⟨1063412, by rfl⟩ : syracuseStep 1417883 = 2126825) B2126825
theorem B1417979 : Blo 1417528 1417979 := bstep (se 1 (by rfl) ⟨1063484, by rfl⟩ : syracuseStep 1417979 = 2126969) B2126969
theorem B6054983 : Blo 1417528 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B1418331 : Blo 1417528 1418331 := bstep (se 1 (by rfl) ⟨1063748, by rfl⟩ : syracuseStep 1418331 = 2127497) B2127497
theorem B5751917 : Blo 1417528 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B1418471 : Blo 1417528 1418471 := bstep (se 1 (by rfl) ⟨1063853, by rfl⟩ : syracuseStep 1418471 = 2127707) B2127707
theorem B1418495 : Blo 1417528 1418495 := bstep (se 1 (by rfl) ⟨1063871, by rfl⟩ : syracuseStep 1418495 = 2127743) B2127743
theorem B1795375 : Blo 1417528 1795375 := bstep (se 1 (by rfl) ⟨1346531, by rfl⟩ : syracuseStep 1795375 = 2693063) B2693063
theorem B1418559 : Blo 1417528 1418559 := bstep (se 1 (by rfl) ⟨1063919, by rfl⟩ : syracuseStep 1418559 = 2127839) B2127839
theorem B4785479 : Blo 1417528 4785479 := bstep (se 1 (by rfl) ⟨3589109, by rfl⟩ : syracuseStep 4785479 = 7178219) B7178219
theorem B1418599 : Blo 1417528 1418599 := bstep (se 1 (by rfl) ⟨1063949, by rfl⟩ : syracuseStep 1418599 = 2127899) B2127899
theorem B1418727 : Blo 1417528 1418727 := bstep (se 1 (by rfl) ⟨1064045, by rfl⟩ : syracuseStep 1418727 = 2128091) B2128091
theorem B1418907 : Blo 1417528 1418907 := bstep (se 1 (by rfl) ⟨1064180, by rfl⟩ : syracuseStep 1418907 = 2128361) B2128361
theorem B7178057 : Blo 1417528 7178057 := bstep (se 2 (by rfl) ⟨2691771, by rfl⟩ : syracuseStep 7178057 = 5383543) B5383543
theorem B1419167 : Blo 1417528 1419167 := bstep (se 1 (by rfl) ⟨1064375, by rfl⟩ : syracuseStep 1419167 = 2128751) B2128751
theorem B4786235 : Blo 1417528 4786235 := bstep (se 1 (by rfl) ⟨3589676, by rfl⟩ : syracuseStep 4786235 = 7179353) B7179353
theorem B1419327 : Blo 1417528 1419327 := bstep (se 1 (by rfl) ⟨1064495, by rfl⟩ : syracuseStep 1419327 = 2128991) B2128991
theorem B1419367 : Blo 1417528 1419367 := bstep (se 1 (by rfl) ⟨1064525, by rfl⟩ : syracuseStep 1419367 = 2129051) B2129051
theorem B9709757 : Blo 1417528 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B2394319 : Blo 1417528 2394319 := bstep (se 1 (by rfl) ⟨1795739, by rfl⟩ : syracuseStep 2394319 = 3591479) B3591479
theorem B1419471 : Blo 1417528 1419471 := bstep (se 1 (by rfl) ⟨1064603, by rfl⟩ : syracuseStep 1419471 = 2129207) B2129207
theorem B92072153 : Blo 1417528 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B8079689 : Blo 1417528 8079689 := bstep (se 2 (by rfl) ⟨3029883, by rfl⟩ : syracuseStep 8079689 = 6059767) B6059767
theorem B12118409 : Blo 1417528 12118409 := bstep (se 2 (by rfl) ⟨4544403, by rfl⟩ : syracuseStep 12118409 = 9088807) B9088807
theorem B66447773 : Blo 1417528 66447773 := bstep (se 3 (by rfl) ⟨12458957, by rfl⟩ : syracuseStep 66447773 = 24917915) B24917915
theorem B5385001 : Blo 1417528 5385001 := bstep (se 2 (by rfl) ⟨2019375, by rfl⟩ : syracuseStep 5385001 = 4038751) B4038751
theorem B4041839 : Blo 1417528 4041839 := bstep (se 1 (by rfl) ⟨3031379, by rfl⟩ : syracuseStep 4041839 = 6062759) B6062759
theorem B6474887 : Blo 1417528 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B4787369 : Blo 1417528 4787369 := bstep (se 2 (by rfl) ⟨1795263, by rfl⟩ : syracuseStep 4787369 = 3590527) B3590527
theorem B8621309 : Blo 1417528 8621309 := bstep (se 3 (by rfl) ⟨1616495, by rfl⟩ : syracuseStep 8621309 = 3232991) B3232991
theorem B3190427 : Blo 1417528 3190427 := bstep (se 1 (by rfl) ⟨2392820, by rfl⟩ : syracuseStep 3190427 = 4785641) B4785641
theorem B16150265 : Blo 1417528 16150265 := bstep (se 2 (by rfl) ⟨6056349, by rfl⟩ : syracuseStep 16150265 = 12112699) B12112699
theorem B3190625 : Blo 1417528 3190625 := bstep (se 2 (by rfl) ⟨1196484, by rfl⟩ : syracuseStep 3190625 = 2392969) B2392969
theorem B4313159 : Blo 1417528 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B8081603 : Blo 1417528 8081603 := bstep (se 1 (by rfl) ⟨6061202, by rfl⟩ : syracuseStep 8081603 = 12122405) B12122405
theorem B17264897 : Blo 1417528 17264897 := bstep (se 2 (by rfl) ⟨6474336, by rfl⟩ : syracuseStep 17264897 = 12948673) B12948673
theorem B3191201 : Blo 1417528 3191201 := bstep (se 2 (by rfl) ⟨1196700, by rfl⟩ : syracuseStep 3191201 = 2393401) B2393401
theorem B7778749 : Blo 1417528 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B17265581 : Blo 1417528 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B69915635 : Blo 1417528 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B398488691 : Blo 1417528 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B2126975 : Blo 1417528 2126975 := bstep (se 1 (by rfl) ⟨1595231, by rfl⟩ : syracuseStep 2126975 = 3190463) B3190463
theorem B5748023 : Blo 1417528 5748023 := bstep (se 1 (by rfl) ⟨4311017, by rfl⟩ : syracuseStep 5748023 = 8622035) B8622035
theorem B3233191 : Blo 1417528 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B2127359 : Blo 1417528 2127359 := bstep (se 1 (by rfl) ⟨1595519, by rfl⟩ : syracuseStep 2127359 = 3191039) B3191039
theorem B9090575 : Blo 1417528 9090575 := bstep (se 1 (by rfl) ⟨6817931, by rfl⟩ : syracuseStep 9090575 = 13635863) B13635863
theorem B2127737 : Blo 1417528 2127737 := bstep (se 2 (by rfl) ⟨797901, by rfl⟩ : syracuseStep 2127737 = 1595803) B1595803
theorem B46028695 : Blo 1417528 46028695 := bstep (se 1 (by rfl) ⟨34521521, by rfl⟩ : syracuseStep 46028695 = 69043043) B69043043
theorem B3028927 : Blo 1417528 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B3028961 : Blo 1417528 3028961 := bstep (se 2 (by rfl) ⟨1135860, by rfl⟩ : syracuseStep 3028961 = 2271721) B2271721
theorem B53155831 : Blo 1417528 53155831 := bstep (se 1 (by rfl) ⟨39866873, by rfl⟩ : syracuseStep 53155831 = 79733747) B79733747
theorem B6060041 : Blo 1417528 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B12114035 : Blo 1417528 12114035 := bstep (se 1 (by rfl) ⟨9085526, by rfl⟩ : syracuseStep 12114035 = 18171053) B18171053
theorem B7674065 : Blo 1417528 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B3193055 : Blo 1417528 3193055 := bstep (se 1 (by rfl) ⟨2394791, by rfl⟩ : syracuseStep 3193055 = 4789583) B4789583
theorem B2128127 : Blo 1417528 2128127 := bstep (se 1 (by rfl) ⟨1596095, by rfl⟩ : syracuseStep 2128127 = 3192191) B3192191
theorem B18430237 : Blo 1417528 18430237 := bstep (se 3 (by rfl) ⟨3455669, by rfl⟩ : syracuseStep 18430237 = 6911339) B6911339
theorem B2128265 : Blo 1417528 2128265 := bstep (se 2 (by rfl) ⟨798099, by rfl⟩ : syracuseStep 2128265 = 1596199) B1596199
theorem B3938719 : Blo 1417528 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B2128439 : Blo 1417528 2128439 := bstep (se 1 (by rfl) ⟨1596329, by rfl⟩ : syracuseStep 2128439 = 3192659) B3192659
theorem B2128511 : Blo 1417528 2128511 := bstep (se 1 (by rfl) ⟨1596383, by rfl⟩ : syracuseStep 2128511 = 3192767) B3192767
theorem B12114683 : Blo 1417528 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B16382807 : Blo 1417528 16382807 := bstep (se 1 (by rfl) ⟨12287105, by rfl⟩ : syracuseStep 16382807 = 24574211) B24574211
theorem B2554735 : Blo 1417528 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B2128889 : Blo 1417528 2128889 := bstep (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) B1596667
theorem B5389375 : Blo 1417528 5389375 := bstep (se 1 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 5389375 = 8084063) B8084063
theorem B2694217 : Blo 1417528 2694217 := bstep (se 2 (by rfl) ⟨1010331, by rfl⟩ : syracuseStep 2694217 = 2020663) B2020663
theorem B12123431 : Blo 1417528 12123431 := bstep (se 1 (by rfl) ⟨9092573, by rfl⟩ : syracuseStep 12123431 = 18185147) B18185147
theorem B3407159 : Blo 1417528 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B5389679 : Blo 1417528 5389679 := bstep (se 1 (by rfl) ⟨4042259, by rfl⟩ : syracuseStep 5389679 = 8084519) B8084519
theorem B49799045 : Blo 1417528 49799045 := bstep (se 4 (by rfl) ⟨4668660, by rfl⟩ : syracuseStep 49799045 = 9337321) B9337321
theorem B2875439 : Blo 1417528 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B11509931 : Blo 1417528 11509931 := bstep (se 1 (by rfl) ⟨8632448, by rfl⟩ : syracuseStep 11509931 = 17264897) B17264897
theorem B5251625 : Blo 1417528 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B10371665 : Blo 1417528 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B11510387 : Blo 1417528 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B3834611 : Blo 1417528 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B1417983 : Blo 1417528 1417983 := bstep (se 1 (by rfl) ⟨1063487, by rfl⟩ : syracuseStep 1417983 = 2126975) B2126975
theorem B15328061 : Blo 1417528 15328061 := bstep (se 3 (by rfl) ⟨2874011, by rfl⟩ : syracuseStep 15328061 = 5748023) B5748023
theorem B1418239 : Blo 1417528 1418239 := bstep (se 1 (by rfl) ⟨1063679, by rfl⟩ : syracuseStep 1418239 = 2127359) B2127359
theorem B4785371 : Blo 1417528 4785371 := bstep (se 1 (by rfl) ⟨3589028, by rfl⟩ : syracuseStep 4785371 = 7178057) B7178057
theorem B1418491 : Blo 1417528 1418491 := bstep (se 1 (by rfl) ⟨1063868, by rfl⟩ : syracuseStep 1418491 = 2127737) B2127737
theorem B4040027 : Blo 1417528 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B7185833 : Blo 1417528 7185833 := bstep (se 2 (by rfl) ⟨2694687, by rfl⟩ : syracuseStep 7185833 = 5389375) B5389375
theorem B6473171 : Blo 1417528 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B1418751 : Blo 1417528 1418751 := bstep (se 1 (by rfl) ⟨1064063, by rfl⟩ : syracuseStep 1418751 = 2128127) B2128127
theorem B8078939 : Blo 1417528 8078939 := bstep (se 1 (by rfl) ⟨6059204, by rfl⟩ : syracuseStep 8078939 = 12118409) B12118409
theorem B1418843 : Blo 1417528 1418843 := bstep (se 1 (by rfl) ⟨1064132, by rfl⟩ : syracuseStep 1418843 = 2128265) B2128265
theorem B1418959 : Blo 1417528 1418959 := bstep (se 1 (by rfl) ⟨1064219, by rfl⟩ : syracuseStep 1418959 = 2128439) B2128439
theorem B2393833 : Blo 1417528 2393833 := bstep (se 2 (by rfl) ⟨897687, by rfl⟩ : syracuseStep 2393833 = 1795375) B1795375
theorem B1419007 : Blo 1417528 1419007 := bstep (se 1 (by rfl) ⟨1064255, by rfl⟩ : syracuseStep 1419007 = 2128511) B2128511
theorem B4310921 : Blo 1417528 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B10921871 : Blo 1417528 10921871 := bstep (se 1 (by rfl) ⟨8191403, by rfl⟩ : syracuseStep 10921871 = 16382807) B16382807
theorem B1419259 : Blo 1417528 1419259 := bstep (se 1 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 1419259 = 2128889) B2128889
theorem B2271439 : Blo 1417528 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B10766843 : Blo 1417528 10766843 := bstep (se 1 (by rfl) ⟨8075132, by rfl⟩ : syracuseStep 10766843 = 16150265) B16150265
theorem B5384987 : Blo 1417528 5384987 := bstep (se 1 (by rfl) ⟨4038740, by rfl⟩ : syracuseStep 5384987 = 8077481) B8077481
theorem B3189545 : Blo 1417528 3189545 := bstep (se 2 (by rfl) ⟨1196079, by rfl⟩ : syracuseStep 3189545 = 2392159) B2392159
theorem B6056795 : Blo 1417528 6056795 := bstep (se 1 (by rfl) ⟨4542596, by rfl⟩ : syracuseStep 6056795 = 9085193) B9085193
theorem B1062636509 : Blo 1417528 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B3189851 : Blo 1417528 3189851 := bstep (se 1 (by rfl) ⟨2392388, by rfl⟩ : syracuseStep 3189851 = 4784777) B4784777
theorem B3190319 : Blo 1417528 3190319 := bstep (se 1 (by rfl) ⟨2392739, by rfl⟩ : syracuseStep 3190319 = 4785479) B4785479
theorem B7180001 : Blo 1417528 7180001 := bstep (se 2 (by rfl) ⟨2692500, by rfl⟩ : syracuseStep 7180001 = 5385001) B5385001
theorem B3190823 : Blo 1417528 3190823 := bstep (se 1 (by rfl) ⟨2393117, by rfl⟩ : syracuseStep 3190823 = 4786235) B4786235
theorem B3592289 : Blo 1417528 3592289 := bstep (se 2 (by rfl) ⟨1347108, by rfl⟩ : syracuseStep 3592289 = 2694217) B2694217
theorem B5116043 : Blo 1417528 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B5386459 : Blo 1417528 5386459 := bstep (se 1 (by rfl) ⟨4039844, by rfl⟩ : syracuseStep 5386459 = 8079689) B8079689
theorem B44298515 : Blo 1417528 44298515 := bstep (se 1 (by rfl) ⟨33223886, by rfl⟩ : syracuseStep 44298515 = 66447773) B66447773
theorem B3191579 : Blo 1417528 3191579 := bstep (se 1 (by rfl) ⟨2393684, by rfl⟩ : syracuseStep 3191579 = 4787369) B4787369
theorem B5747539 : Blo 1417528 5747539 := bstep (se 1 (by rfl) ⟨4310654, by rfl⟩ : syracuseStep 5747539 = 8621309) B8621309
theorem B8082287 : Blo 1417528 8082287 := bstep (se 1 (by rfl) ⟨6061715, by rfl⟩ : syracuseStep 8082287 = 12123431) B12123431
theorem B3593119 : Blo 1417528 3593119 := bstep (se 1 (by rfl) ⟨2694839, by rfl⟩ : syracuseStep 3593119 = 5389679) B5389679
theorem B132797453 : Blo 1417528 132797453 := bstep (se 3 (by rfl) ⟨24899522, by rfl⟩ : syracuseStep 132797453 = 49799045) B49799045
theorem B2126951 : Blo 1417528 2126951 := bstep (se 1 (by rfl) ⟨1595213, by rfl⟩ : syracuseStep 2126951 = 3190427) B3190427
theorem B61371593 : Blo 1417528 61371593 := bstep (se 2 (by rfl) ⟨23014347, by rfl⟩ : syracuseStep 61371593 = 46028695) B46028695
theorem B2127083 : Blo 1417528 2127083 := bstep (se 1 (by rfl) ⟨1595312, by rfl⟩ : syracuseStep 2127083 = 3190625) B3190625
theorem B70874441 : Blo 1417528 70874441 := bstep (se 2 (by rfl) ⟨26577915, by rfl⟩ : syracuseStep 70874441 = 53155831) B53155831
theorem B9967063 : Blo 1417528 9967063 := bstep (se 1 (by rfl) ⟨7475297, by rfl⟩ : syracuseStep 9967063 = 14950595) B14950595
theorem B5387735 : Blo 1417528 5387735 := bstep (se 1 (by rfl) ⟨4040801, by rfl⟩ : syracuseStep 5387735 = 8081603) B8081603
theorem B2020891 : Blo 1417528 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B3192425 : Blo 1417528 3192425 := bstep (se 2 (by rfl) ⟨1197159, by rfl⟩ : syracuseStep 3192425 = 2394319) B2394319
theorem B2127467 : Blo 1417528 2127467 := bstep (se 1 (by rfl) ⟨1595600, by rfl⟩ : syracuseStep 2127467 = 3191201) B3191201
theorem B46610423 : Blo 1417528 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B4036655 : Blo 1417528 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B6060383 : Blo 1417528 6060383 := bstep (se 1 (by rfl) ⟨4545287, by rfl⟩ : syracuseStep 6060383 = 9090575) B9090575
theorem B3406313 : Blo 1417528 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B8076023 : Blo 1417528 8076023 := bstep (se 1 (by rfl) ⟨6057017, by rfl⟩ : syracuseStep 8076023 = 12114035) B12114035
theorem B61381435 : Blo 1417528 61381435 := bstep (se 1 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 61381435 = 92072153) B92072153
theorem B2128703 : Blo 1417528 2128703 := bstep (se 1 (by rfl) ⟨1596527, by rfl⟩ : syracuseStep 2128703 = 3193055) B3193055
theorem B98294597 : Blo 1417528 98294597 := bstep (se 4 (by rfl) ⟨9215118, by rfl⟩ : syracuseStep 98294597 = 18430237) B18430237
theorem B8076455 : Blo 1417528 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B2694559 : Blo 1417528 2694559 := bstep (se 1 (by rfl) ⟨2020919, by rfl⟩ : syracuseStep 2694559 = 4041839) B4041839
theorem B4316591 : Blo 1417528 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B4038569 : Blo 1417528 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B8077229 : Blo 1417528 8077229 := bstep (se 3 (by rfl) ⟨1514480, by rfl⟩ : syracuseStep 8077229 = 3028961) B3028961
theorem B10764413 : Blo 1417528 10764413 := bstep (se 3 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 10764413 = 4036655) B4036655
theorem B7667837 : Blo 1417528 7667837 := bstep (se 3 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 7667837 = 2875439) B2875439
theorem B29532343 : Blo 1417528 29532343 := bstep (se 1 (by rfl) ⟨22149257, by rfl⟩ : syracuseStep 29532343 = 44298515) B44298515
theorem B6914443 : Blo 1417528 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B2556407 : Blo 1417528 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B1417967 : Blo 1417528 1417967 := bstep (se 1 (by rfl) ⟨1063475, by rfl⟩ : syracuseStep 1417967 = 2126951) B2126951
theorem B1418055 : Blo 1417528 1418055 := bstep (se 1 (by rfl) ⟨1063541, by rfl⟩ : syracuseStep 1418055 = 2127083) B2127083
theorem B1418311 : Blo 1417528 1418311 := bstep (se 1 (by rfl) ⟨1063733, by rfl⟩ : syracuseStep 1418311 = 2127467) B2127467
theorem B11510909 : Blo 1417528 11510909 := bstep (se 3 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 11510909 = 4316591) B4316591
theorem B31073615 : Blo 1417528 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B4040255 : Blo 1417528 4040255 := bstep (se 1 (by rfl) ⟨3030191, by rfl⟩ : syracuseStep 4040255 = 6060383) B6060383
theorem B7177895 : Blo 1417528 7177895 := bstep (se 1 (by rfl) ⟨5383421, by rfl⟩ : syracuseStep 7177895 = 10766843) B10766843
theorem B5384015 : Blo 1417528 5384015 := bstep (se 1 (by rfl) ⟨4038011, by rfl⟩ : syracuseStep 5384015 = 8076023) B8076023
theorem B3589991 : Blo 1417528 3589991 := bstep (se 1 (by rfl) ⟨2692493, by rfl⟩ : syracuseStep 3589991 = 5384987) B5384987
theorem B1419135 : Blo 1417528 1419135 := bstep (se 1 (by rfl) ⟨1064351, by rfl⟩ : syracuseStep 1419135 = 2128703) B2128703
theorem B65529731 : Blo 1417528 65529731 := bstep (se 1 (by rfl) ⟨49147298, by rfl⟩ : syracuseStep 65529731 = 98294597) B98294597
theorem B13289417 : Blo 1417528 13289417 := bstep (se 2 (by rfl) ⟨4983531, by rfl⟩ : syracuseStep 13289417 = 9967063) B9967063
theorem B5384303 : Blo 1417528 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B11495789 : Blo 1417528 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B4786667 : Blo 1417528 4786667 := bstep (se 1 (by rfl) ⟨3590000, by rfl⟩ : syracuseStep 4786667 = 7180001) B7180001
theorem B2833697357 : Blo 1417528 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B5384819 : Blo 1417528 5384819 := bstep (se 1 (by rfl) ⟨4038614, by rfl⟩ : syracuseStep 5384819 = 8077229) B8077229
theorem B354126541 : Blo 1417528 354126541 := bstep (se 3 (by rfl) ⟨66398726, by rfl⟩ : syracuseStep 354126541 = 132797453) B132797453
theorem B2394859 : Blo 1417528 2394859 := bstep (se 1 (by rfl) ⟨1796144, by rfl⟩ : syracuseStep 2394859 = 3592289) B3592289
theorem B3410695 : Blo 1417528 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B3501083 : Blo 1417528 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B10218707 : Blo 1417528 10218707 := bstep (se 1 (by rfl) ⟨7664030, by rfl⟩ : syracuseStep 10218707 = 15328061) B15328061
theorem B40914395 : Blo 1417528 40914395 := bstep (se 1 (by rfl) ⟨30685796, by rfl⟩ : syracuseStep 40914395 = 61371593) B61371593
theorem B3190247 : Blo 1417528 3190247 := bstep (se 1 (by rfl) ⟨2392685, by rfl⟩ : syracuseStep 3190247 = 4785371) B4785371
theorem B3591823 : Blo 1417528 3591823 := bstep (se 1 (by rfl) ⟨2693867, by rfl⟩ : syracuseStep 3591823 = 5387735) B5387735
theorem B5385959 : Blo 1417528 5385959 := bstep (se 1 (by rfl) ⟨4039469, by rfl⟩ : syracuseStep 5385959 = 8078939) B8078939
theorem B81841913 : Blo 1417528 81841913 := bstep (se 2 (by rfl) ⟨30690717, by rfl⟩ : syracuseStep 81841913 = 61381435) B61381435
theorem B7663385 : Blo 1417528 7663385 := bstep (se 2 (by rfl) ⟨2873769, by rfl⟩ : syracuseStep 7663385 = 5747539) B5747539
theorem B2126363 : Blo 1417528 2126363 := bstep (se 1 (by rfl) ⟨1594772, by rfl⟩ : syracuseStep 2126363 = 3189545) B3189545
theorem B3592745 : Blo 1417528 3592745 := bstep (se 2 (by rfl) ⟨1347279, by rfl⟩ : syracuseStep 3592745 = 2694559) B2694559
theorem B2126567 : Blo 1417528 2126567 := bstep (se 1 (by rfl) ⟨1594925, by rfl⟩ : syracuseStep 2126567 = 3189851) B3189851
theorem B3191777 : Blo 1417528 3191777 := bstep (se 2 (by rfl) ⟨1196916, by rfl⟩ : syracuseStep 3191777 = 2393833) B2393833
theorem B2126879 : Blo 1417528 2126879 := bstep (se 1 (by rfl) ⟨1595159, by rfl⟩ : syracuseStep 2126879 = 3190319) B3190319
theorem B2692379 : Blo 1417528 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B2127215 : Blo 1417528 2127215 := bstep (se 1 (by rfl) ⟨1595411, by rfl⟩ : syracuseStep 2127215 = 3190823) B3190823
theorem B7673287 : Blo 1417528 7673287 := bstep (se 1 (by rfl) ⟨5754965, by rfl⟩ : syracuseStep 7673287 = 11509931) B11509931
theorem B3028585 : Blo 1417528 3028585 := bstep (se 2 (by rfl) ⟨1135719, by rfl⟩ : syracuseStep 3028585 = 2271439) B2271439
theorem B7181945 : Blo 1417528 7181945 := bstep (se 2 (by rfl) ⟨2693229, by rfl⟩ : syracuseStep 7181945 = 5386459) B5386459
theorem B7673591 : Blo 1417528 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B2127719 : Blo 1417528 2127719 := bstep (se 1 (by rfl) ⟨1595789, by rfl⟩ : syracuseStep 2127719 = 3191579) B3191579
theorem B5388191 : Blo 1417528 5388191 := bstep (se 1 (by rfl) ⟨4041143, by rfl⟩ : syracuseStep 5388191 = 8082287) B8082287
theorem B47249627 : Blo 1417528 47249627 := bstep (se 1 (by rfl) ⟨35437220, by rfl⟩ : syracuseStep 47249627 = 70874441) B70874441
theorem B2693351 : Blo 1417528 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B4790555 : Blo 1417528 4790555 := bstep (se 1 (by rfl) ⟨3592916, by rfl⟩ : syracuseStep 4790555 = 7185833) B7185833
theorem B4315447 : Blo 1417528 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B2128283 : Blo 1417528 2128283 := bstep (se 1 (by rfl) ⟨1596212, by rfl⟩ : syracuseStep 2128283 = 3192425) B3192425
theorem B4790825 : Blo 1417528 4790825 := bstep (se 2 (by rfl) ⟨1796559, by rfl⟩ : syracuseStep 4790825 = 3593119) B3593119
theorem B7281247 : Blo 1417528 7281247 := bstep (se 1 (by rfl) ⟨5460935, by rfl⟩ : syracuseStep 7281247 = 10921871) B10921871
theorem B9083501 : Blo 1417528 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B4037863 : Blo 1417528 4037863 := bstep (se 1 (by rfl) ⟨3028397, by rfl⟩ : syracuseStep 4037863 = 6056795) B6056795
theorem B2694521 : Blo 1417528 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B7176275 : Blo 1417528 7176275 := bstep (se 1 (by rfl) ⟨5382206, by rfl⟩ : syracuseStep 7176275 = 10764413) B10764413
theorem B5111891 : Blo 1417528 5111891 := bstep (se 1 (by rfl) ⟨3833918, by rfl⟩ : syracuseStep 5111891 = 7667837) B7667837
theorem B1417575 : Blo 1417528 1417575 := bstep (se 1 (by rfl) ⟨1063181, by rfl⟩ : syracuseStep 1417575 = 2126363) B2126363
theorem B1417711 : Blo 1417528 1417711 := bstep (se 1 (by rfl) ⟨1063283, by rfl⟩ : syracuseStep 1417711 = 2126567) B2126567
theorem B1417919 : Blo 1417528 1417919 := bstep (se 1 (by rfl) ⟨1063439, by rfl⟩ : syracuseStep 1417919 = 2126879) B2126879
theorem B9708329 : Blo 1417528 9708329 := bstep (se 2 (by rfl) ⟨3640623, by rfl⟩ : syracuseStep 9708329 = 7281247) B7281247
theorem B1418143 : Blo 1417528 1418143 := bstep (se 1 (by rfl) ⟨1063607, by rfl⟩ : syracuseStep 1418143 = 2127215) B2127215
theorem B4547593 : Blo 1417528 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B4785263 : Blo 1417528 4785263 := bstep (se 1 (by rfl) ⟨3588947, by rfl⟩ : syracuseStep 4785263 = 7177895) B7177895
theorem B3589343 : Blo 1417528 3589343 := bstep (se 1 (by rfl) ⟨2692007, by rfl⟩ : syracuseStep 3589343 = 5384015) B5384015
theorem B2393327 : Blo 1417528 2393327 := bstep (se 1 (by rfl) ⟨1794995, by rfl⟩ : syracuseStep 2393327 = 3589991) B3589991
theorem B1418479 : Blo 1417528 1418479 := bstep (se 1 (by rfl) ⟨1063859, by rfl⟩ : syracuseStep 1418479 = 2127719) B2127719
theorem B6817085 : Blo 1417528 6817085 := bstep (se 3 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 6817085 = 2556407) B2556407
theorem B3589535 : Blo 1417528 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1418855 : Blo 1417528 1418855 := bstep (se 1 (by rfl) ⟨1064141, by rfl⟩ : syracuseStep 1418855 = 2128283) B2128283
theorem B5383817 : Blo 1417528 5383817 := bstep (se 2 (by rfl) ⟨2018931, by rfl⟩ : syracuseStep 5383817 = 4037863) B4037863
theorem B6055667 : Blo 1417528 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B3589879 : Blo 1417528 3589879 := bstep (se 1 (by rfl) ⟨2692409, by rfl⟩ : syracuseStep 3589879 = 5384819) B5384819
theorem B1796347 : Blo 1417528 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B3590639 : Blo 1417528 3590639 := bstep (se 1 (by rfl) ⟨2692979, by rfl⟩ : syracuseStep 3590639 = 5385959) B5385959
theorem B54561275 : Blo 1417528 54561275 := bstep (se 1 (by rfl) ⟨40920956, by rfl⟩ : syracuseStep 54561275 = 81841913) B81841913
theorem B2395163 : Blo 1417528 2395163 := bstep (se 1 (by rfl) ⟨1796372, by rfl⟩ : syracuseStep 2395163 = 3592745) B3592745
theorem B5753929 : Blo 1417528 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B9219257 : Blo 1417528 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B7179677 : Blo 1417528 7179677 := bstep (se 3 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 7179677 = 2692379) B2692379
theorem B4787963 : Blo 1417528 4787963 := bstep (se 1 (by rfl) ⟨3590972, by rfl⟩ : syracuseStep 4787963 = 7181945) B7181945
theorem B5115727 : Blo 1417528 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B3592127 : Blo 1417528 3592127 := bstep (se 1 (by rfl) ⟨2694095, by rfl⟩ : syracuseStep 3592127 = 5388191) B5388191
theorem B8859611 : Blo 1417528 8859611 := bstep (se 1 (by rfl) ⟨6644708, by rfl⟩ : syracuseStep 8859611 = 13289417) B13289417
theorem B7663859 : Blo 1417528 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B3191111 : Blo 1417528 3191111 := bstep (se 1 (by rfl) ⟨2393333, by rfl⟩ : syracuseStep 3191111 = 4786667) B4786667
theorem B6812471 : Blo 1417528 6812471 := bstep (se 1 (by rfl) ⟨5109353, by rfl⟩ : syracuseStep 6812471 = 10218707) B10218707
theorem B4789097 : Blo 1417528 4789097 := bstep (se 2 (by rfl) ⟨1795911, by rfl⟩ : syracuseStep 4789097 = 3591823) B3591823
theorem B27276263 : Blo 1417528 27276263 := bstep (se 1 (by rfl) ⟨20457197, by rfl⟩ : syracuseStep 27276263 = 40914395) B40914395
theorem B2126831 : Blo 1417528 2126831 := bstep (se 1 (by rfl) ⟨1595123, by rfl⟩ : syracuseStep 2126831 = 3190247) B3190247
theorem B5108923 : Blo 1417528 5108923 := bstep (se 1 (by rfl) ⟨3831692, by rfl⟩ : syracuseStep 5108923 = 7663385) B7663385
theorem B9336221 : Blo 1417528 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B39376457 : Blo 1417528 39376457 := bstep (se 2 (by rfl) ⟨14766171, by rfl⟩ : syracuseStep 39376457 = 29532343) B29532343
theorem B125999005 : Blo 1417528 125999005 := bstep (se 3 (by rfl) ⟨23624813, by rfl⟩ : syracuseStep 125999005 = 47249627) B47249627
theorem B7182269 : Blo 1417528 7182269 := bstep (se 3 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 7182269 = 2693351) B2693351
theorem B2127851 : Blo 1417528 2127851 := bstep (se 1 (by rfl) ⟨1595888, by rfl⟩ : syracuseStep 2127851 = 3191777) B3191777
theorem B7673939 : Blo 1417528 7673939 := bstep (se 1 (by rfl) ⟨5755454, by rfl⟩ : syracuseStep 7673939 = 11510909) B11510909
theorem B20715743 : Blo 1417528 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B472168721 : Blo 1417528 472168721 := bstep (se 2 (by rfl) ⟨177063270, by rfl⟩ : syracuseStep 472168721 = 354126541) B354126541
theorem B3193145 : Blo 1417528 3193145 := bstep (se 2 (by rfl) ⟨1197429, by rfl⟩ : syracuseStep 3193145 = 2394859) B2394859
theorem B2693503 : Blo 1417528 2693503 := bstep (se 1 (by rfl) ⟨2020127, by rfl⟩ : syracuseStep 2693503 = 4040255) B4040255
theorem B43686487 : Blo 1417528 43686487 := bstep (se 1 (by rfl) ⟨32764865, by rfl⟩ : syracuseStep 43686487 = 65529731) B65529731
theorem B3193703 : Blo 1417528 3193703 := bstep (se 1 (by rfl) ⟨2395277, by rfl⟩ : syracuseStep 3193703 = 4790555) B4790555
theorem B3193883 : Blo 1417528 3193883 := bstep (se 1 (by rfl) ⟨2395412, by rfl⟩ : syracuseStep 3193883 = 4790825) B4790825
theorem B1889131571 : Blo 1417528 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B10231049 : Blo 1417528 10231049 := bstep (se 2 (by rfl) ⟨3836643, by rfl⟩ : syracuseStep 10231049 = 7673287) B7673287
theorem B4038113 : Blo 1417528 4038113 := bstep (se 2 (by rfl) ⟨1514292, by rfl⟩ : syracuseStep 4038113 = 3028585) B3028585
theorem B4784183 : Blo 1417528 4784183 := bstep (se 1 (by rfl) ⟨3588137, by rfl⟩ : syracuseStep 4784183 = 7176275) B7176275
theorem B3407927 : Blo 1417528 3407927 := bstep (se 1 (by rfl) ⟨2555945, by rfl⟩ : syracuseStep 3407927 = 5111891) B5111891
theorem B6472219 : Blo 1417528 6472219 := bstep (se 1 (by rfl) ⟨4854164, by rfl⟩ : syracuseStep 6472219 = 9708329) B9708329
theorem B1417887 : Blo 1417528 1417887 := bstep (se 1 (by rfl) ⟨1063415, by rfl⟩ : syracuseStep 1417887 = 2126831) B2126831
theorem B2392895 : Blo 1417528 2392895 := bstep (se 1 (by rfl) ⟨1794671, by rfl⟩ : syracuseStep 2392895 = 3589343) B3589343
theorem B2393023 : Blo 1417528 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B3589211 : Blo 1417528 3589211 := bstep (se 1 (by rfl) ⟨2691908, by rfl⟩ : syracuseStep 3589211 = 5383817) B5383817
theorem B1418567 : Blo 1417528 1418567 := bstep (se 1 (by rfl) ⟨1063925, by rfl⟩ : syracuseStep 1418567 = 2127851) B2127851
theorem B2393759 : Blo 1417528 2393759 := bstep (se 1 (by rfl) ⟨1795319, by rfl⟩ : syracuseStep 2393759 = 3590639) B3590639
theorem B36374183 : Blo 1417528 36374183 := bstep (se 1 (by rfl) ⟨27280637, by rfl⟩ : syracuseStep 36374183 = 54561275) B54561275
theorem B6146171 : Blo 1417528 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B4786451 : Blo 1417528 4786451 := bstep (se 1 (by rfl) ⟨3589838, by rfl⟩ : syracuseStep 4786451 = 7179677) B7179677
theorem B4786505 : Blo 1417528 4786505 := bstep (se 2 (by rfl) ⟨1794939, by rfl⟩ : syracuseStep 4786505 = 3589879) B3589879
theorem B2394751 : Blo 1417528 2394751 := bstep (se 1 (by rfl) ⟨1796063, by rfl⟩ : syracuseStep 2394751 = 3592127) B3592127
theorem B2395129 : Blo 1417528 2395129 := bstep (se 2 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 2395129 = 1796347) B1796347
theorem B3591337 : Blo 1417528 3591337 := bstep (se 2 (by rfl) ⟨1346751, by rfl⟩ : syracuseStep 3591337 = 2693503) B2693503
theorem B3190175 : Blo 1417528 3190175 := bstep (se 1 (by rfl) ⟨2392631, by rfl⟩ : syracuseStep 3190175 = 4785263) B4785263
theorem B58248649 : Blo 1417528 58248649 := bstep (se 2 (by rfl) ⟨21843243, by rfl⟩ : syracuseStep 58248649 = 43686487) B43686487
theorem B26250971 : Blo 1417528 26250971 := bstep (se 1 (by rfl) ⟨19688228, by rfl⟩ : syracuseStep 26250971 = 39376457) B39376457
theorem B10768301 : Blo 1417528 10768301 := bstep (se 3 (by rfl) ⟨2019056, by rfl⟩ : syracuseStep 10768301 = 4038113) B4038113
theorem B4788179 : Blo 1417528 4788179 := bstep (se 1 (by rfl) ⟨3591134, by rfl⟩ : syracuseStep 4788179 = 7182269) B7182269
theorem B5115959 : Blo 1417528 5115959 := bstep (se 1 (by rfl) ⟨3836969, by rfl⟩ : syracuseStep 5115959 = 7673939) B7673939
theorem B7671905 : Blo 1417528 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B6811897 : Blo 1417528 6811897 := bstep (se 2 (by rfl) ⟨2554461, by rfl⟩ : syracuseStep 6811897 = 5108923) B5108923
theorem B18166589 : Blo 1417528 18166589 := bstep (se 3 (by rfl) ⟨3406235, by rfl⟩ : syracuseStep 18166589 = 6812471) B6812471
theorem B6820699 : Blo 1417528 6820699 := bstep (se 1 (by rfl) ⟨5115524, by rfl⟩ : syracuseStep 6820699 = 10231049) B10231049
theorem B6820969 : Blo 1417528 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B3191975 : Blo 1417528 3191975 := bstep (se 1 (by rfl) ⟨2393981, by rfl⟩ : syracuseStep 3191975 = 4787963) B4787963
theorem B167998673 : Blo 1417528 167998673 := bstep (se 2 (by rfl) ⟨62999502, by rfl⟩ : syracuseStep 167998673 = 125999005) B125999005
theorem B24253829 : Blo 1417528 24253829 := bstep (se 4 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 24253829 = 4547593) B4547593
theorem B5109239 : Blo 1417528 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B2127407 : Blo 1417528 2127407 := bstep (se 1 (by rfl) ⟨1595555, by rfl⟩ : syracuseStep 2127407 = 3191111) B3191111
theorem B3192731 : Blo 1417528 3192731 := bstep (se 1 (by rfl) ⟨2394548, by rfl⟩ : syracuseStep 3192731 = 4789097) B4789097
theorem B18184175 : Blo 1417528 18184175 := bstep (se 1 (by rfl) ⟨13638131, by rfl⟩ : syracuseStep 18184175 = 27276263) B27276263
theorem B1259116589 : Blo 1417528 1259116589 := bstep (se 3 (by rfl) ⟨236084360, by rfl⟩ : syracuseStep 1259116589 = 472168721) B472168721
theorem B1595551 : Blo 1417528 1595551 := bstep (se 1 (by rfl) ⟨1196663, by rfl⟩ : syracuseStep 1595551 = 2393327) B2393327
theorem B4544723 : Blo 1417528 4544723 := bstep (se 1 (by rfl) ⟨3408542, by rfl⟩ : syracuseStep 4544723 = 6817085) B6817085
theorem B6224147 : Blo 1417528 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B4037111 : Blo 1417528 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B13810495 : Blo 1417528 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B2128763 : Blo 1417528 2128763 := bstep (se 1 (by rfl) ⟨1596572, by rfl⟩ : syracuseStep 2128763 = 3193145) B3193145
theorem B2129135 : Blo 1417528 2129135 := bstep (se 1 (by rfl) ⟨1596851, by rfl⟩ : syracuseStep 2129135 = 3193703) B3193703
theorem B1596775 : Blo 1417528 1596775 := bstep (se 1 (by rfl) ⟨1197581, by rfl⟩ : syracuseStep 1596775 = 2395163) B2395163
theorem B2129255 : Blo 1417528 2129255 := bstep (se 1 (by rfl) ⟨1596941, by rfl⟩ : syracuseStep 2129255 = 3193883) B3193883
theorem B1259421047 : Blo 1417528 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B5906407 : Blo 1417528 5906407 := bstep (se 1 (by rfl) ⟨4429805, by rfl⟩ : syracuseStep 5906407 = 8859611) B8859611
theorem B2392807 : Blo 1417528 2392807 := bstep (se 1 (by rfl) ⟨1794605, by rfl⟩ : syracuseStep 2392807 = 3589211) B3589211
theorem B1418271 : Blo 1417528 1418271 := bstep (se 1 (by rfl) ⟨1063703, by rfl⟩ : syracuseStep 1418271 = 2127407) B2127407
theorem B24249455 : Blo 1417528 24249455 := bstep (se 1 (by rfl) ⟨18187091, by rfl⟩ : syracuseStep 24249455 = 36374183) B36374183
theorem B9094265 : Blo 1417528 9094265 := bstep (se 2 (by rfl) ⟨3410349, by rfl⟩ : syracuseStep 9094265 = 6820699) B6820699
theorem B839411059 : Blo 1417528 839411059 := bstep (se 1 (by rfl) ⟨629558294, by rfl⟩ : syracuseStep 839411059 = 1259116589) B1259116589
theorem B4097447 : Blo 1417528 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B9094625 : Blo 1417528 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B70002589 : Blo 1417528 70002589 := bstep (se 3 (by rfl) ⟨13125485, by rfl⟩ : syracuseStep 70002589 = 26250971) B26250971
theorem B1419175 : Blo 1417528 1419175 := bstep (se 1 (by rfl) ⟨1064381, by rfl⟩ : syracuseStep 1419175 = 2128763) B2128763
theorem B1419423 : Blo 1417528 1419423 := bstep (se 1 (by rfl) ⟨1064567, by rfl⟩ : syracuseStep 1419423 = 2129135) B2129135
theorem B1419503 : Blo 1417528 1419503 := bstep (se 1 (by rfl) ⟨1064627, by rfl⟩ : syracuseStep 1419503 = 2129255) B2129255
theorem B7178867 : Blo 1417528 7178867 := bstep (se 1 (by rfl) ⟨5384150, by rfl⟩ : syracuseStep 7178867 = 10768301) B10768301
theorem B7875209 : Blo 1417528 7875209 := bstep (se 2 (by rfl) ⟨2953203, by rfl⟩ : syracuseStep 7875209 = 5906407) B5906407
theorem B3189455 : Blo 1417528 3189455 := bstep (se 1 (by rfl) ⟨2392091, by rfl⟩ : syracuseStep 3189455 = 4784183) B4784183
theorem B3410639 : Blo 1417528 3410639 := bstep (se 1 (by rfl) ⟨2557979, by rfl⟩ : syracuseStep 3410639 = 5115959) B5115959
theorem B5114603 : Blo 1417528 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B9087805 : Blo 1417528 9087805 := bstep (se 3 (by rfl) ⟨1703963, by rfl⟩ : syracuseStep 9087805 = 3407927) B3407927
theorem B12111059 : Blo 1417528 12111059 := bstep (se 1 (by rfl) ⟨9083294, by rfl⟩ : syracuseStep 12111059 = 18166589) B18166589
theorem B8629625 : Blo 1417528 8629625 := bstep (se 2 (by rfl) ⟨3236109, by rfl⟩ : syracuseStep 8629625 = 6472219) B6472219
theorem B3190697 : Blo 1417528 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B4149431 : Blo 1417528 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B3190967 : Blo 1417528 3190967 := bstep (se 1 (by rfl) ⟨2393225, by rfl⟩ : syracuseStep 3190967 = 4786451) B4786451
theorem B3191003 : Blo 1417528 3191003 := bstep (se 1 (by rfl) ⟨2393252, by rfl⟩ : syracuseStep 3191003 = 4786505) B4786505
theorem B4788449 : Blo 1417528 4788449 := bstep (se 2 (by rfl) ⟨1795668, by rfl⟩ : syracuseStep 4788449 = 3591337) B3591337
theorem B2691407 : Blo 1417528 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B77664865 : Blo 1417528 77664865 := bstep (se 2 (by rfl) ⟨29124324, by rfl⟩ : syracuseStep 77664865 = 58248649) B58248649
theorem B2126783 : Blo 1417528 2126783 := bstep (se 1 (by rfl) ⟨1595087, by rfl⟩ : syracuseStep 2126783 = 3190175) B3190175
theorem B3192119 : Blo 1417528 3192119 := bstep (se 1 (by rfl) ⟨2394089, by rfl⟩ : syracuseStep 3192119 = 4788179) B4788179
theorem B2127401 : Blo 1417528 2127401 := bstep (se 2 (by rfl) ⟨797775, by rfl⟩ : syracuseStep 2127401 = 1595551) B1595551
theorem B9082529 : Blo 1417528 9082529 := bstep (se 2 (by rfl) ⟨3405948, by rfl⟩ : syracuseStep 9082529 = 6811897) B6811897
theorem B1595263 : Blo 1417528 1595263 := bstep (se 1 (by rfl) ⟨1196447, by rfl⟩ : syracuseStep 1595263 = 2392895) B2392895
theorem B2127983 : Blo 1417528 2127983 := bstep (se 1 (by rfl) ⟨1595987, by rfl⟩ : syracuseStep 2127983 = 3191975) B3191975
theorem B111999115 : Blo 1417528 111999115 := bstep (se 1 (by rfl) ⟨83999336, by rfl⟩ : syracuseStep 111999115 = 167998673) B167998673
theorem B3193001 : Blo 1417528 3193001 := bstep (se 2 (by rfl) ⟨1197375, by rfl⟩ : syracuseStep 3193001 = 2394751) B2394751
theorem B16169219 : Blo 1417528 16169219 := bstep (se 1 (by rfl) ⟨12126914, by rfl⟩ : syracuseStep 16169219 = 24253829) B24253829
theorem B3406159 : Blo 1417528 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B18413993 : Blo 1417528 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B1595839 : Blo 1417528 1595839 := bstep (se 1 (by rfl) ⟨1196879, by rfl⟩ : syracuseStep 1595839 = 2393759) B2393759
theorem B2128487 : Blo 1417528 2128487 := bstep (se 1 (by rfl) ⟨1596365, by rfl⟩ : syracuseStep 2128487 = 3192731) B3192731
theorem B12122783 : Blo 1417528 12122783 := bstep (se 1 (by rfl) ⟨9092087, by rfl⟩ : syracuseStep 12122783 = 18184175) B18184175
theorem B3193505 : Blo 1417528 3193505 := bstep (se 2 (by rfl) ⟨1197564, by rfl⟩ : syracuseStep 3193505 = 2395129) B2395129
theorem B3029815 : Blo 1417528 3029815 := bstep (se 1 (by rfl) ⟨2272361, by rfl⟩ : syracuseStep 3029815 = 4544723) B4544723
theorem B2129033 : Blo 1417528 2129033 := bstep (se 2 (by rfl) ⟨798387, by rfl⟩ : syracuseStep 2129033 = 1596775) B1596775
theorem B839614031 : Blo 1417528 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B1417855 : Blo 1417528 1417855 := bstep (se 1 (by rfl) ⟨1063391, by rfl⟩ : syracuseStep 1417855 = 2126783) B2126783
theorem B597328613 : Blo 1417528 597328613 := bstep (se 4 (by rfl) ⟨55999557, by rfl⟩ : syracuseStep 597328613 = 111999115) B111999115
theorem B6062843 : Blo 1417528 6062843 := bstep (se 1 (by rfl) ⟨4547132, by rfl⟩ : syracuseStep 6062843 = 9094265) B9094265
theorem B7177085 : Blo 1417528 7177085 := bstep (se 3 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 7177085 = 2691407) B2691407
theorem B23012333 : Blo 1417528 23012333 := bstep (se 3 (by rfl) ⟨4314812, by rfl⟩ : syracuseStep 23012333 = 8629625) B8629625
theorem B6063083 : Blo 1417528 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B1418267 : Blo 1417528 1418267 := bstep (se 1 (by rfl) ⟨1063700, by rfl⟩ : syracuseStep 1418267 = 2127401) B2127401
theorem B12117073 : Blo 1417528 12117073 := bstep (se 2 (by rfl) ⟨4543902, by rfl⟩ : syracuseStep 12117073 = 9087805) B9087805
theorem B6055019 : Blo 1417528 6055019 := bstep (se 1 (by rfl) ⟨4541264, by rfl⟩ : syracuseStep 6055019 = 9082529) B9082529
theorem B49103981 : Blo 1417528 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B1418655 : Blo 1417528 1418655 := bstep (se 1 (by rfl) ⟨1063991, by rfl⟩ : syracuseStep 1418655 = 2127983) B2127983
theorem B1418991 : Blo 1417528 1418991 := bstep (se 1 (by rfl) ⟨1064243, by rfl⟩ : syracuseStep 1418991 = 2128487) B2128487
theorem B43706101 : Blo 1417528 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B4785911 : Blo 1417528 4785911 := bstep (se 1 (by rfl) ⟨3589433, by rfl⟩ : syracuseStep 4785911 = 7178867) B7178867
theorem B3409735 : Blo 1417528 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B1419355 : Blo 1417528 1419355 := bstep (se 1 (by rfl) ⟨1064516, by rfl⟩ : syracuseStep 1419355 = 2129033) B2129033
theorem B4541545 : Blo 1417528 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B16166303 : Blo 1417528 16166303 := bstep (se 1 (by rfl) ⟨12124727, by rfl⟩ : syracuseStep 16166303 = 24249455) B24249455
theorem B3190409 : Blo 1417528 3190409 := bstep (se 2 (by rfl) ⟨1196403, by rfl⟩ : syracuseStep 3190409 = 2392807) B2392807
theorem B16159013 : Blo 1417528 16159013 := bstep (se 4 (by rfl) ⟨1514907, by rfl⟩ : syracuseStep 16159013 = 3029815) B3029815
theorem B21000557 : Blo 1417528 21000557 := bstep (se 3 (by rfl) ⟨3937604, by rfl⟩ : syracuseStep 21000557 = 7875209) B7875209
theorem B8081855 : Blo 1417528 8081855 := bstep (se 1 (by rfl) ⟨6061391, by rfl⟩ : syracuseStep 8081855 = 12122783) B12122783
theorem B2126303 : Blo 1417528 2126303 := bstep (se 1 (by rfl) ⟨1594727, by rfl⟩ : syracuseStep 2126303 = 3189455) B3189455
theorem B2273759 : Blo 1417528 2273759 := bstep (se 1 (by rfl) ⟨1705319, by rfl⟩ : syracuseStep 2273759 = 3410639) B3410639
theorem B8074039 : Blo 1417528 8074039 := bstep (se 1 (by rfl) ⟨6055529, by rfl⟩ : syracuseStep 8074039 = 12111059) B12111059
theorem B2127017 : Blo 1417528 2127017 := bstep (se 2 (by rfl) ⟨797631, by rfl⟩ : syracuseStep 2127017 = 1595263) B1595263
theorem B93336785 : Blo 1417528 93336785 := bstep (se 2 (by rfl) ⟨35001294, by rfl⟩ : syracuseStep 93336785 = 70002589) B70002589
theorem B2127131 : Blo 1417528 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B2766287 : Blo 1417528 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B2127311 : Blo 1417528 2127311 := bstep (se 1 (by rfl) ⟨1595483, by rfl⟩ : syracuseStep 2127311 = 3190967) B3190967
theorem B2127335 : Blo 1417528 2127335 := bstep (se 1 (by rfl) ⟨1595501, by rfl⟩ : syracuseStep 2127335 = 3191003) B3191003
theorem B3192299 : Blo 1417528 3192299 := bstep (se 1 (by rfl) ⟨2394224, by rfl⟩ : syracuseStep 3192299 = 4788449) B4788449
theorem B2127785 : Blo 1417528 2127785 := bstep (se 2 (by rfl) ⟨797919, by rfl⟩ : syracuseStep 2127785 = 1595839) B1595839
theorem B103553153 : Blo 1417528 103553153 := bstep (se 2 (by rfl) ⟨38832432, by rfl⟩ : syracuseStep 103553153 = 77664865) B77664865
theorem B2128079 : Blo 1417528 2128079 := bstep (se 1 (by rfl) ⟨1596059, by rfl⟩ : syracuseStep 2128079 = 3192119) B3192119
theorem B2128667 : Blo 1417528 2128667 := bstep (se 1 (by rfl) ⟨1596500, by rfl⟩ : syracuseStep 2128667 = 3193001) B3193001
theorem B10779479 : Blo 1417528 10779479 := bstep (se 1 (by rfl) ⟨8084609, by rfl⟩ : syracuseStep 10779479 = 16169219) B16169219
theorem B2129003 : Blo 1417528 2129003 := bstep (se 1 (by rfl) ⟨1596752, by rfl⟩ : syracuseStep 2129003 = 3193505) B3193505
theorem B1119214745 : Blo 1417528 1119214745 := bstep (se 2 (by rfl) ⟨419705529, by rfl⟩ : syracuseStep 1119214745 = 839411059) B839411059
theorem B559742687 : Blo 1417528 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B10772675 : Blo 1417528 10772675 := bstep (se 1 (by rfl) ⟨8079506, by rfl⟩ : syracuseStep 10772675 = 16159013) B16159013
theorem B14000371 : Blo 1417528 14000371 := bstep (se 1 (by rfl) ⟨10500278, by rfl⟩ : syracuseStep 14000371 = 21000557) B21000557
theorem B1417535 : Blo 1417528 1417535 := bstep (se 1 (by rfl) ⟨1063151, by rfl⟩ : syracuseStep 1417535 = 2126303) B2126303
theorem B1515839 : Blo 1417528 1515839 := bstep (se 1 (by rfl) ⟨1136879, by rfl⟩ : syracuseStep 1515839 = 2273759) B2273759
theorem B4784723 : Blo 1417528 4784723 := bstep (se 1 (by rfl) ⟨3588542, by rfl⟩ : syracuseStep 4784723 = 7177085) B7177085
theorem B32735987 : Blo 1417528 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B1418011 : Blo 1417528 1418011 := bstep (se 1 (by rfl) ⟨1063508, by rfl⟩ : syracuseStep 1418011 = 2127017) B2127017
theorem B1418087 : Blo 1417528 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1844191 : Blo 1417528 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B1418207 : Blo 1417528 1418207 := bstep (se 1 (by rfl) ⟨1063655, by rfl⟩ : syracuseStep 1418207 = 2127311) B2127311
theorem B1418223 : Blo 1417528 1418223 := bstep (se 1 (by rfl) ⟨1063667, by rfl⟩ : syracuseStep 1418223 = 2127335) B2127335
theorem B10765385 : Blo 1417528 10765385 := bstep (se 2 (by rfl) ⟨4037019, by rfl⟩ : syracuseStep 10765385 = 8074039) B8074039
theorem B1418523 : Blo 1417528 1418523 := bstep (se 1 (by rfl) ⟨1063892, by rfl⟩ : syracuseStep 1418523 = 2127785) B2127785
theorem B69035435 : Blo 1417528 69035435 := bstep (se 1 (by rfl) ⟨51776576, by rfl⟩ : syracuseStep 69035435 = 103553153) B103553153
theorem B16156097 : Blo 1417528 16156097 := bstep (se 2 (by rfl) ⟨6058536, by rfl⟩ : syracuseStep 16156097 = 12117073) B12117073
theorem B1418719 : Blo 1417528 1418719 := bstep (se 1 (by rfl) ⟨1064039, by rfl⟩ : syracuseStep 1418719 = 2128079) B2128079
theorem B6055393 : Blo 1417528 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B1419111 : Blo 1417528 1419111 := bstep (se 1 (by rfl) ⟨1064333, by rfl⟩ : syracuseStep 1419111 = 2128667) B2128667
theorem B7186319 : Blo 1417528 7186319 := bstep (se 1 (by rfl) ⟨5389739, by rfl⟩ : syracuseStep 7186319 = 10779479) B10779479
theorem B1419335 : Blo 1417528 1419335 := bstep (se 1 (by rfl) ⟨1064501, by rfl⟩ : syracuseStep 1419335 = 2129003) B2129003
theorem B4041895 : Blo 1417528 4041895 := bstep (se 1 (by rfl) ⟨3031421, by rfl⟩ : syracuseStep 4041895 = 6062843) B6062843
theorem B4042055 : Blo 1417528 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B3190607 : Blo 1417528 3190607 := bstep (se 1 (by rfl) ⟨2392955, by rfl⟩ : syracuseStep 3190607 = 4785911) B4785911
theorem B10777535 : Blo 1417528 10777535 := bstep (se 1 (by rfl) ⟨8083151, by rfl⟩ : syracuseStep 10777535 = 16166303) B16166303
theorem B58274801 : Blo 1417528 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B2126939 : Blo 1417528 2126939 := bstep (se 1 (by rfl) ⟨1595204, by rfl⟩ : syracuseStep 2126939 = 3190409) B3190409
theorem B5387903 : Blo 1417528 5387903 := bstep (se 1 (by rfl) ⟨4040927, by rfl⟩ : syracuseStep 5387903 = 8081855) B8081855
theorem B398219075 : Blo 1417528 398219075 := bstep (se 1 (by rfl) ⟨298664306, by rfl⟩ : syracuseStep 398219075 = 597328613) B597328613
theorem B15341555 : Blo 1417528 15341555 := bstep (se 1 (by rfl) ⟨11506166, by rfl⟩ : syracuseStep 15341555 = 23012333) B23012333
theorem B4036679 : Blo 1417528 4036679 := bstep (se 1 (by rfl) ⟨3027509, by rfl⟩ : syracuseStep 4036679 = 6055019) B6055019
theorem B62224523 : Blo 1417528 62224523 := bstep (se 1 (by rfl) ⟨46668392, by rfl⟩ : syracuseStep 62224523 = 93336785) B93336785
theorem B2128199 : Blo 1417528 2128199 := bstep (se 1 (by rfl) ⟨1596149, by rfl⟩ : syracuseStep 2128199 = 3192299) B3192299
theorem B746143163 : Blo 1417528 746143163 := bstep (se 1 (by rfl) ⟨559607372, by rfl⟩ : syracuseStep 746143163 = 1119214745) B1119214745
theorem B4546313 : Blo 1417528 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B373161791 : Blo 1417528 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B21823991 : Blo 1417528 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B7185023 : Blo 1417528 7185023 := bstep (se 1 (by rfl) ⟨5388767, by rfl⟩ : syracuseStep 7185023 = 10777535) B10777535
theorem B7176923 : Blo 1417528 7176923 := bstep (se 1 (by rfl) ⟨5382692, by rfl⟩ : syracuseStep 7176923 = 10765385) B10765385
theorem B1417959 : Blo 1417528 1417959 := bstep (se 1 (by rfl) ⟨1063469, by rfl⟩ : syracuseStep 1417959 = 2126939) B2126939
theorem B46023623 : Blo 1417528 46023623 := bstep (se 1 (by rfl) ⟨34517717, by rfl⟩ : syracuseStep 46023623 = 69035435) B69035435
theorem B265479383 : Blo 1417528 265479383 := bstep (se 1 (by rfl) ⟨199109537, by rfl⟩ : syracuseStep 265479383 = 398219075) B398219075
theorem B2458921 : Blo 1417528 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B1418799 : Blo 1417528 1418799 := bstep (se 1 (by rfl) ⟨1064099, by rfl⟩ : syracuseStep 1418799 = 2128199) B2128199
theorem B497428775 : Blo 1417528 497428775 := bstep (se 1 (by rfl) ⟨373071581, by rfl⟩ : syracuseStep 497428775 = 746143163) B746143163
theorem B3189815 : Blo 1417528 3189815 := bstep (se 1 (by rfl) ⟨2392361, by rfl⟩ : syracuseStep 3189815 = 4784723) B4784723
theorem B38849867 : Blo 1417528 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B4042237 : Blo 1417528 4042237 := bstep (se 3 (by rfl) ⟨757919, by rfl⟩ : syracuseStep 4042237 = 1515839) B1515839
theorem B3591935 : Blo 1417528 3591935 := bstep (se 1 (by rfl) ⟨2693951, by rfl⟩ : syracuseStep 3591935 = 5387903) B5387903
theorem B10227703 : Blo 1417528 10227703 := bstep (se 1 (by rfl) ⟨7670777, by rfl⟩ : syracuseStep 10227703 = 15341555) B15341555
theorem B2691119 : Blo 1417528 2691119 := bstep (se 1 (by rfl) ⟨2018339, by rfl⟩ : syracuseStep 2691119 = 4036679) B4036679
theorem B8073857 : Blo 1417528 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B2127071 : Blo 1417528 2127071 := bstep (se 1 (by rfl) ⟨1595303, by rfl⟩ : syracuseStep 2127071 = 3190607) B3190607
theorem B7181783 : Blo 1417528 7181783 := bstep (se 1 (by rfl) ⟨5386337, by rfl⟩ : syracuseStep 7181783 = 10772675) B10772675
theorem B10770731 : Blo 1417528 10770731 := bstep (se 1 (by rfl) ⟨8078048, by rfl⟩ : syracuseStep 10770731 = 16156097) B16156097
theorem B4790879 : Blo 1417528 4790879 := bstep (se 1 (by rfl) ⟨3593159, by rfl⟩ : syracuseStep 4790879 = 7186319) B7186319
theorem B74668645 : Blo 1417528 74668645 := bstep (se 4 (by rfl) ⟨7000185, by rfl⟩ : syracuseStep 74668645 = 14000371) B14000371
theorem B41483015 : Blo 1417528 41483015 := bstep (se 1 (by rfl) ⟨31112261, by rfl⟩ : syracuseStep 41483015 = 62224523) B62224523
theorem B5389193 : Blo 1417528 5389193 := bstep (se 2 (by rfl) ⟨2020947, by rfl⟩ : syracuseStep 5389193 = 4041895) B4041895
theorem B2694703 : Blo 1417528 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B3030875 : Blo 1417528 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B248774527 : Blo 1417528 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B1794079 : Blo 1417528 1794079 := bstep (se 1 (by rfl) ⟨1345559, by rfl⟩ : syracuseStep 1794079 = 2691119) B2691119
theorem B14549327 : Blo 1417528 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B5382571 : Blo 1417528 5382571 := bstep (se 1 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 5382571 = 8073857) B8073857
theorem B4784615 : Blo 1417528 4784615 := bstep (se 1 (by rfl) ⟨3588461, by rfl⟩ : syracuseStep 4784615 = 7176923) B7176923
theorem B99558193 : Blo 1417528 99558193 := bstep (se 2 (by rfl) ⟨37334322, by rfl⟩ : syracuseStep 99558193 = 74668645) B74668645
theorem B1418047 : Blo 1417528 1418047 := bstep (se 1 (by rfl) ⟨1063535, by rfl⟩ : syracuseStep 1418047 = 2127071) B2127071
theorem B3278561 : Blo 1417528 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B2394623 : Blo 1417528 2394623 := bstep (se 1 (by rfl) ⟨1795967, by rfl⟩ : syracuseStep 2394623 = 3591935) B3591935
theorem B30682415 : Blo 1417528 30682415 := bstep (se 1 (by rfl) ⟨23011811, by rfl⟩ : syracuseStep 30682415 = 46023623) B46023623
theorem B4787855 : Blo 1417528 4787855 := bstep (se 1 (by rfl) ⟨3590891, by rfl⟩ : syracuseStep 4787855 = 7181783) B7181783
theorem B7180487 : Blo 1417528 7180487 := bstep (se 1 (by rfl) ⟨5385365, by rfl⟩ : syracuseStep 7180487 = 10770731) B10770731
theorem B3592795 : Blo 1417528 3592795 := bstep (se 1 (by rfl) ⟨2694596, by rfl⟩ : syracuseStep 3592795 = 5389193) B5389193
theorem B2126543 : Blo 1417528 2126543 := bstep (se 1 (by rfl) ⟨1594907, by rfl⟩ : syracuseStep 2126543 = 3189815) B3189815
theorem B3592937 : Blo 1417528 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B25899911 : Blo 1417528 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B331699369 : Blo 1417528 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B2020583 : Blo 1417528 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B13636937 : Blo 1417528 13636937 := bstep (se 2 (by rfl) ⟨5113851, by rfl⟩ : syracuseStep 13636937 = 10227703) B10227703
theorem B4790015 : Blo 1417528 4790015 := bstep (se 1 (by rfl) ⟨3592511, by rfl⟩ : syracuseStep 4790015 = 7185023) B7185023
theorem B176986255 : Blo 1417528 176986255 := bstep (se 1 (by rfl) ⟨132739691, by rfl⟩ : syracuseStep 176986255 = 265479383) B265479383
theorem B331619183 : Blo 1417528 331619183 := bstep (se 1 (by rfl) ⟨248714387, by rfl⟩ : syracuseStep 331619183 = 497428775) B497428775
theorem B3193919 : Blo 1417528 3193919 := bstep (se 1 (by rfl) ⟨2395439, by rfl⟩ : syracuseStep 3193919 = 4790879) B4790879
theorem B27655343 : Blo 1417528 27655343 := bstep (se 1 (by rfl) ⟨20741507, by rfl⟩ : syracuseStep 27655343 = 41483015) B41483015
theorem B5389649 : Blo 1417528 5389649 := bstep (se 2 (by rfl) ⟨2021118, by rfl⟩ : syracuseStep 5389649 = 4042237) B4042237
theorem B2392105 : Blo 1417528 2392105 := bstep (se 2 (by rfl) ⟨897039, by rfl⟩ : syracuseStep 2392105 = 1794079) B1794079
theorem B9699551 : Blo 1417528 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B1417695 : Blo 1417528 1417695 := bstep (se 1 (by rfl) ⟨1063271, by rfl⟩ : syracuseStep 1417695 = 2126543) B2126543
theorem B7176761 : Blo 1417528 7176761 := bstep (se 2 (by rfl) ⟨2691285, by rfl⟩ : syracuseStep 7176761 = 5382571) B5382571
theorem B132744257 : Blo 1417528 132744257 := bstep (se 2 (by rfl) ⟨49779096, by rfl⟩ : syracuseStep 132744257 = 99558193) B99558193
theorem B221079455 : Blo 1417528 221079455 := bstep (se 1 (by rfl) ⟨165809591, by rfl⟩ : syracuseStep 221079455 = 331619183) B331619183
theorem B8742829 : Blo 1417528 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B4786991 : Blo 1417528 4786991 := bstep (se 1 (by rfl) ⟨3590243, by rfl⟩ : syracuseStep 4786991 = 7180487) B7180487
theorem B235981673 : Blo 1417528 235981673 := bstep (se 2 (by rfl) ⟨88493127, by rfl⟩ : syracuseStep 235981673 = 176986255) B176986255
theorem B3189743 : Blo 1417528 3189743 := bstep (se 1 (by rfl) ⟨2392307, by rfl⟩ : syracuseStep 3189743 = 4784615) B4784615
theorem B2395291 : Blo 1417528 2395291 := bstep (se 1 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 2395291 = 3592937) B3592937
theorem B442265825 : Blo 1417528 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B18436895 : Blo 1417528 18436895 := bstep (se 1 (by rfl) ⟨13827671, by rfl⟩ : syracuseStep 18436895 = 27655343) B27655343
theorem B3593099 : Blo 1417528 3593099 := bstep (se 1 (by rfl) ⟨2694824, by rfl⟩ : syracuseStep 3593099 = 5389649) B5389649
theorem B3191903 : Blo 1417528 3191903 := bstep (se 1 (by rfl) ⟨2393927, by rfl⟩ : syracuseStep 3191903 = 4787855) B4787855
theorem B17266607 : Blo 1417528 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B5388221 : Blo 1417528 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B4790393 : Blo 1417528 4790393 := bstep (se 2 (by rfl) ⟨1796397, by rfl⟩ : syracuseStep 4790393 = 3592795) B3592795
theorem B9091291 : Blo 1417528 9091291 := bstep (se 1 (by rfl) ⟨6818468, by rfl⟩ : syracuseStep 9091291 = 13636937) B13636937
theorem B3193343 : Blo 1417528 3193343 := bstep (se 1 (by rfl) ⟨2395007, by rfl⟩ : syracuseStep 3193343 = 4790015) B4790015
theorem B1596415 : Blo 1417528 1596415 := bstep (se 1 (by rfl) ⟨1197311, by rfl⟩ : syracuseStep 1596415 = 2394623) B2394623
theorem B2129279 : Blo 1417528 2129279 := bstep (se 1 (by rfl) ⟨1596959, by rfl⟩ : syracuseStep 2129279 = 3193919) B3193919
theorem B20454943 : Blo 1417528 20454943 := bstep (se 1 (by rfl) ⟨15341207, by rfl⟩ : syracuseStep 20454943 = 30682415) B30682415
theorem B4784507 : Blo 1417528 4784507 := bstep (se 1 (by rfl) ⟨3588380, by rfl⟩ : syracuseStep 4784507 = 7176761) B7176761
theorem B11511071 : Blo 1417528 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B157321115 : Blo 1417528 157321115 := bstep (se 1 (by rfl) ⟨117990836, by rfl⟩ : syracuseStep 157321115 = 235981673) B235981673
theorem B27273257 : Blo 1417528 27273257 := bstep (se 2 (by rfl) ⟨10227471, by rfl⟩ : syracuseStep 27273257 = 20454943) B20454943
theorem B1419519 : Blo 1417528 1419519 := bstep (se 1 (by rfl) ⟨1064639, by rfl⟩ : syracuseStep 1419519 = 2129279) B2129279
theorem B3189473 : Blo 1417528 3189473 := bstep (se 2 (by rfl) ⟨1196052, by rfl⟩ : syracuseStep 3189473 = 2392105) B2392105
theorem B6466367 : Blo 1417528 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B12291263 : Blo 1417528 12291263 := bstep (se 1 (by rfl) ⟨9218447, by rfl⟩ : syracuseStep 12291263 = 18436895) B18436895
theorem B2395399 : Blo 1417528 2395399 := bstep (se 1 (by rfl) ⟨1796549, by rfl⟩ : syracuseStep 2395399 = 3593099) B3593099
theorem B147386303 : Blo 1417528 147386303 := bstep (se 1 (by rfl) ⟨110539727, by rfl⟩ : syracuseStep 147386303 = 221079455) B221079455
theorem B3592147 : Blo 1417528 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B3191327 : Blo 1417528 3191327 := bstep (se 1 (by rfl) ⟨2393495, by rfl⟩ : syracuseStep 3191327 = 4786991) B4786991
theorem B2126495 : Blo 1417528 2126495 := bstep (se 1 (by rfl) ⟨1594871, by rfl⟩ : syracuseStep 2126495 = 3189743) B3189743
theorem B294843883 : Blo 1417528 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B12121721 : Blo 1417528 12121721 := bstep (se 2 (by rfl) ⟨4545645, by rfl⟩ : syracuseStep 12121721 = 9091291) B9091291
theorem B88496171 : Blo 1417528 88496171 := bstep (se 1 (by rfl) ⟨66372128, by rfl⟩ : syracuseStep 88496171 = 132744257) B132744257
theorem B2127935 : Blo 1417528 2127935 := bstep (se 1 (by rfl) ⟨1595951, by rfl⟩ : syracuseStep 2127935 = 3191903) B3191903
theorem B2128553 : Blo 1417528 2128553 := bstep (se 2 (by rfl) ⟨798207, by rfl⟩ : syracuseStep 2128553 = 1596415) B1596415
theorem B3193595 : Blo 1417528 3193595 := bstep (se 1 (by rfl) ⟨2395196, by rfl⟩ : syracuseStep 3193595 = 4790393) B4790393
theorem B3193721 : Blo 1417528 3193721 := bstep (se 2 (by rfl) ⟨1197645, by rfl⟩ : syracuseStep 3193721 = 2395291) B2395291
theorem B2128895 : Blo 1417528 2128895 := bstep (se 1 (by rfl) ⟨1596671, by rfl⟩ : syracuseStep 2128895 = 3193343) B3193343
theorem B11657105 : Blo 1417528 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B1417663 : Blo 1417528 1417663 := bstep (se 1 (by rfl) ⟨1063247, by rfl⟩ : syracuseStep 1417663 = 2126495) B2126495
theorem B1418623 : Blo 1417528 1418623 := bstep (se 1 (by rfl) ⟨1063967, by rfl⟩ : syracuseStep 1418623 = 2127935) B2127935
theorem B1419035 : Blo 1417528 1419035 := bstep (se 1 (by rfl) ⟨1064276, by rfl⟩ : syracuseStep 1419035 = 2128553) B2128553
theorem B4310911 : Blo 1417528 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B1419263 : Blo 1417528 1419263 := bstep (se 1 (by rfl) ⟨1064447, by rfl⟩ : syracuseStep 1419263 = 2128895) B2128895
theorem B8194175 : Blo 1417528 8194175 := bstep (se 1 (by rfl) ⟨6145631, by rfl⟩ : syracuseStep 8194175 = 12291263) B12291263
theorem B98257535 : Blo 1417528 98257535 := bstep (se 1 (by rfl) ⟨73693151, by rfl⟩ : syracuseStep 98257535 = 147386303) B147386303
theorem B3189671 : Blo 1417528 3189671 := bstep (se 1 (by rfl) ⟨2392253, by rfl⟩ : syracuseStep 3189671 = 4784507) B4784507
theorem B8081147 : Blo 1417528 8081147 := bstep (se 1 (by rfl) ⟨6060860, by rfl⟩ : syracuseStep 8081147 = 12121721) B12121721
theorem B18182171 : Blo 1417528 18182171 := bstep (se 1 (by rfl) ⟨13636628, by rfl⟩ : syracuseStep 18182171 = 27273257) B27273257
theorem B2126315 : Blo 1417528 2126315 := bstep (se 1 (by rfl) ⟨1594736, by rfl⟩ : syracuseStep 2126315 = 3189473) B3189473
theorem B7771403 : Blo 1417528 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B4789529 : Blo 1417528 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B2127551 : Blo 1417528 2127551 := bstep (se 1 (by rfl) ⟨1595663, by rfl⟩ : syracuseStep 2127551 = 3191327) B3191327
theorem B7674047 : Blo 1417528 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B104880743 : Blo 1417528 104880743 := bstep (se 1 (by rfl) ⟨78660557, by rfl⟩ : syracuseStep 104880743 = 157321115) B157321115
theorem B58997447 : Blo 1417528 58997447 := bstep (se 1 (by rfl) ⟨44248085, by rfl⟩ : syracuseStep 58997447 = 88496171) B88496171
theorem B3193865 : Blo 1417528 3193865 := bstep (se 2 (by rfl) ⟨1197699, by rfl⟩ : syracuseStep 3193865 = 2395399) B2395399
theorem B2129063 : Blo 1417528 2129063 := bstep (se 1 (by rfl) ⟨1596797, by rfl⟩ : syracuseStep 2129063 = 3193595) B3193595
theorem B2129147 : Blo 1417528 2129147 := bstep (se 1 (by rfl) ⟨1596860, by rfl⟩ : syracuseStep 2129147 = 3193721) B3193721
theorem B393125177 : Blo 1417528 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B1417543 : Blo 1417528 1417543 := bstep (se 1 (by rfl) ⟨1063157, by rfl⟩ : syracuseStep 1417543 = 2126315) B2126315
theorem B1418367 : Blo 1417528 1418367 := bstep (se 1 (by rfl) ⟨1063775, by rfl⟩ : syracuseStep 1418367 = 2127551) B2127551
theorem B69920495 : Blo 1417528 69920495 := bstep (se 1 (by rfl) ⟨52440371, by rfl⟩ : syracuseStep 69920495 = 104880743) B104880743
theorem B65505023 : Blo 1417528 65505023 := bstep (se 1 (by rfl) ⟨49128767, by rfl⟩ : syracuseStep 65505023 = 98257535) B98257535
theorem B39331631 : Blo 1417528 39331631 := bstep (se 1 (by rfl) ⟨29498723, by rfl⟩ : syracuseStep 39331631 = 58997447) B58997447
theorem B1419375 : Blo 1417528 1419375 := bstep (se 1 (by rfl) ⟨1064531, by rfl⟩ : syracuseStep 1419375 = 2129063) B2129063
theorem B1419431 : Blo 1417528 1419431 := bstep (se 1 (by rfl) ⟨1064573, by rfl⟩ : syracuseStep 1419431 = 2129147) B2129147
theorem B5180935 : Blo 1417528 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B5116031 : Blo 1417528 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B2126447 : Blo 1417528 2126447 := bstep (se 1 (by rfl) ⟨1594835, by rfl⟩ : syracuseStep 2126447 = 3189671) B3189671
theorem B262083451 : Blo 1417528 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B5387431 : Blo 1417528 5387431 := bstep (se 1 (by rfl) ⟨4040573, by rfl⟩ : syracuseStep 5387431 = 8081147) B8081147
theorem B5747881 : Blo 1417528 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B12121447 : Blo 1417528 12121447 := bstep (se 1 (by rfl) ⟨9091085, by rfl⟩ : syracuseStep 12121447 = 18182171) B18182171
theorem B3193019 : Blo 1417528 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B5462783 : Blo 1417528 5462783 := bstep (se 1 (by rfl) ⟨4097087, by rfl⟩ : syracuseStep 5462783 = 8194175) B8194175
theorem B2129243 : Blo 1417528 2129243 := bstep (se 1 (by rfl) ⟨1596932, by rfl⟩ : syracuseStep 2129243 = 3193865) B3193865
theorem B1417631 : Blo 1417528 1417631 := bstep (se 1 (by rfl) ⟨1063223, by rfl⟩ : syracuseStep 1417631 = 2126447) B2126447
theorem B46613663 : Blo 1417528 46613663 := bstep (se 1 (by rfl) ⟨34960247, by rfl⟩ : syracuseStep 46613663 = 69920495) B69920495
theorem B6907913 : Blo 1417528 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B1419495 : Blo 1417528 1419495 := bstep (se 1 (by rfl) ⟨1064621, by rfl⟩ : syracuseStep 1419495 = 2129243) B2129243
theorem B3410687 : Blo 1417528 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B7663841 : Blo 1417528 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B3641855 : Blo 1417528 3641855 := bstep (se 1 (by rfl) ⟨2731391, by rfl⟩ : syracuseStep 3641855 = 5462783) B5462783
theorem B349444601 : Blo 1417528 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B43670015 : Blo 1417528 43670015 := bstep (se 1 (by rfl) ⟨32752511, by rfl⟩ : syracuseStep 43670015 = 65505023) B65505023
theorem B26221087 : Blo 1417528 26221087 := bstep (se 1 (by rfl) ⟨19665815, by rfl⟩ : syracuseStep 26221087 = 39331631) B39331631
theorem B2128679 : Blo 1417528 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B7183241 : Blo 1417528 7183241 := bstep (se 2 (by rfl) ⟨2693715, by rfl⟩ : syracuseStep 7183241 = 5387431) B5387431
theorem B16161929 : Blo 1417528 16161929 := bstep (se 2 (by rfl) ⟨6060723, by rfl⟩ : syracuseStep 16161929 = 12121447) B12121447
theorem B4605275 : Blo 1417528 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B1419119 : Blo 1417528 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B9095165 : Blo 1417528 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B10774619 : Blo 1417528 10774619 := bstep (se 1 (by rfl) ⟨8080964, by rfl⟩ : syracuseStep 10774619 = 16161929) B16161929
theorem B31075775 : Blo 1417528 31075775 := bstep (se 1 (by rfl) ⟨23306831, by rfl⟩ : syracuseStep 31075775 = 46613663) B46613663
theorem B9711613 : Blo 1417528 9711613 := bstep (se 3 (by rfl) ⟨1820927, by rfl⟩ : syracuseStep 9711613 = 3641855) B3641855
theorem B4788827 : Blo 1417528 4788827 := bstep (se 1 (by rfl) ⟨3591620, by rfl⟩ : syracuseStep 4788827 = 7183241) B7183241
theorem B5109227 : Blo 1417528 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B34961449 : Blo 1417528 34961449 := bstep (se 2 (by rfl) ⟨13110543, by rfl⟩ : syracuseStep 34961449 = 26221087) B26221087
theorem B232963067 : Blo 1417528 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B29113343 : Blo 1417528 29113343 := bstep (se 1 (by rfl) ⟨21835007, by rfl⟩ : syracuseStep 29113343 = 43670015) B43670015
theorem B12280733 : Blo 1417528 12280733 := bstep (se 3 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 12280733 = 4605275) B4605275
theorem B6063443 : Blo 1417528 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B19408895 : Blo 1417528 19408895 := bstep (se 1 (by rfl) ⟨14556671, by rfl⟩ : syracuseStep 19408895 = 29113343) B29113343
theorem B46615265 : Blo 1417528 46615265 := bstep (se 2 (by rfl) ⟨17480724, by rfl⟩ : syracuseStep 46615265 = 34961449) B34961449
theorem B155308711 : Blo 1417528 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B12948817 : Blo 1417528 12948817 := bstep (se 2 (by rfl) ⟨4855806, by rfl⟩ : syracuseStep 12948817 = 9711613) B9711613
theorem B3192551 : Blo 1417528 3192551 := bstep (se 1 (by rfl) ⟨2394413, by rfl⟩ : syracuseStep 3192551 = 4788827) B4788827
theorem B3406151 : Blo 1417528 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B7183079 : Blo 1417528 7183079 := bstep (se 1 (by rfl) ⟨5387309, by rfl⟩ : syracuseStep 7183079 = 10774619) B10774619
theorem B20717183 : Blo 1417528 20717183 := bstep (se 1 (by rfl) ⟨15537887, by rfl⟩ : syracuseStep 20717183 = 31075775) B31075775
theorem B207078281 : Blo 1417528 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B2270767 : Blo 1417528 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B8187155 : Blo 1417528 8187155 := bstep (se 1 (by rfl) ⟨6140366, by rfl⟩ : syracuseStep 8187155 = 12280733) B12280733
theorem B4042295 : Blo 1417528 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B12939263 : Blo 1417528 12939263 := bstep (se 1 (by rfl) ⟨9704447, by rfl⟩ : syracuseStep 12939263 = 19408895) B19408895
theorem B17265089 : Blo 1417528 17265089 := bstep (se 2 (by rfl) ⟨6474408, by rfl⟩ : syracuseStep 17265089 = 12948817) B12948817
theorem B31076843 : Blo 1417528 31076843 := bstep (se 1 (by rfl) ⟨23307632, by rfl⟩ : syracuseStep 31076843 = 46615265) B46615265
theorem B4788719 : Blo 1417528 4788719 := bstep (se 1 (by rfl) ⟨3591539, by rfl⟩ : syracuseStep 4788719 = 7183079) B7183079
theorem B2128367 : Blo 1417528 2128367 := bstep (se 1 (by rfl) ⟨1596275, by rfl⟩ : syracuseStep 2128367 = 3192551) B3192551
theorem B13811455 : Blo 1417528 13811455 := bstep (se 1 (by rfl) ⟨10358591, by rfl⟩ : syracuseStep 13811455 = 20717183) B20717183
theorem B11510059 : Blo 1417528 11510059 := bstep (se 1 (by rfl) ⟨8632544, by rfl⟩ : syracuseStep 11510059 = 17265089) B17265089
theorem B138052187 : Blo 1417528 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B82871581 : Blo 1417528 82871581 := bstep (se 3 (by rfl) ⟨15538421, by rfl⟩ : syracuseStep 82871581 = 31076843) B31076843
theorem B1418911 : Blo 1417528 1418911 := bstep (se 1 (by rfl) ⟨1064183, by rfl⟩ : syracuseStep 1418911 = 2128367) B2128367
theorem B5458103 : Blo 1417528 5458103 := bstep (se 1 (by rfl) ⟨4093577, by rfl⟩ : syracuseStep 5458103 = 8187155) B8187155
theorem B3027689 : Blo 1417528 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B3192479 : Blo 1417528 3192479 := bstep (se 1 (by rfl) ⟨2394359, by rfl⟩ : syracuseStep 3192479 = 4788719) B4788719
theorem B8626175 : Blo 1417528 8626175 := bstep (se 1 (by rfl) ⟨6469631, by rfl⟩ : syracuseStep 8626175 = 12939263) B12939263
theorem B18415273 : Blo 1417528 18415273 := bstep (se 2 (by rfl) ⟨6905727, by rfl⟩ : syracuseStep 18415273 = 13811455) B13811455
theorem B2694863 : Blo 1417528 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B3638735 : Blo 1417528 3638735 := bstep (se 1 (by rfl) ⟨2729051, by rfl⟩ : syracuseStep 3638735 = 5458103) B5458103
theorem B110495441 : Blo 1417528 110495441 := bstep (se 2 (by rfl) ⟨41435790, by rfl⟩ : syracuseStep 110495441 = 82871581) B82871581
theorem B24553697 : Blo 1417528 24553697 := bstep (se 2 (by rfl) ⟨9207636, by rfl⟩ : syracuseStep 24553697 = 18415273) B18415273
theorem B1796575 : Blo 1417528 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B15346745 : Blo 1417528 15346745 := bstep (se 2 (by rfl) ⟨5755029, by rfl⟩ : syracuseStep 15346745 = 11510059) B11510059
theorem B2018459 : Blo 1417528 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B92034791 : Blo 1417528 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B2128319 : Blo 1417528 2128319 := bstep (se 1 (by rfl) ⟨1596239, by rfl⟩ : syracuseStep 2128319 = 3192479) B3192479
theorem B5750783 : Blo 1417528 5750783 := bstep (se 1 (by rfl) ⟨4313087, by rfl⟩ : syracuseStep 5750783 = 8626175) B8626175
theorem B5382557 : Blo 1417528 5382557 := bstep (se 3 (by rfl) ⟨1009229, by rfl⟩ : syracuseStep 5382557 = 2018459) B2018459
theorem B2425823 : Blo 1417528 2425823 := bstep (se 1 (by rfl) ⟨1819367, by rfl⟩ : syracuseStep 2425823 = 3638735) B3638735
theorem B73663627 : Blo 1417528 73663627 := bstep (se 1 (by rfl) ⟨55247720, by rfl⟩ : syracuseStep 73663627 = 110495441) B110495441
theorem B1418879 : Blo 1417528 1418879 := bstep (se 1 (by rfl) ⟨1064159, by rfl⟩ : syracuseStep 1418879 = 2128319) B2128319
theorem B2395433 : Blo 1417528 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B3833855 : Blo 1417528 3833855 := bstep (se 1 (by rfl) ⟨2875391, by rfl⟩ : syracuseStep 3833855 = 5750783) B5750783
theorem B65476525 : Blo 1417528 65476525 := bstep (se 3 (by rfl) ⟨12276848, by rfl⟩ : syracuseStep 65476525 = 24553697) B24553697
theorem B61356527 : Blo 1417528 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B10231163 : Blo 1417528 10231163 := bstep (se 1 (by rfl) ⟨7673372, by rfl⟩ : syracuseStep 10231163 = 15346745) B15346745
theorem B3588371 : Blo 1417528 3588371 := bstep (se 1 (by rfl) ⟨2691278, by rfl⟩ : syracuseStep 3588371 = 5382557) B5382557
theorem B40904351 : Blo 1417528 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B98218169 : Blo 1417528 98218169 := bstep (se 2 (by rfl) ⟨36831813, by rfl⟩ : syracuseStep 98218169 = 73663627) B73663627
theorem B6820775 : Blo 1417528 6820775 := bstep (se 1 (by rfl) ⟨5115581, by rfl⟩ : syracuseStep 6820775 = 10231163) B10231163
theorem B25875445 : Blo 1417528 25875445 := bstep (se 5 (by rfl) ⟨1212911, by rfl⟩ : syracuseStep 25875445 = 2425823) B2425823
theorem B2555903 : Blo 1417528 2555903 := bstep (se 1 (by rfl) ⟨1916927, by rfl⟩ : syracuseStep 2555903 = 3833855) B3833855
theorem B1596955 : Blo 1417528 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B87302033 : Blo 1417528 87302033 := bstep (se 2 (by rfl) ⟨32738262, by rfl⟩ : syracuseStep 87302033 = 65476525) B65476525
theorem B65478779 : Blo 1417528 65478779 := bstep (se 1 (by rfl) ⟨49109084, by rfl⟩ : syracuseStep 65478779 = 98218169) B98218169
theorem B2392247 : Blo 1417528 2392247 := bstep (se 1 (by rfl) ⟨1794185, by rfl⟩ : syracuseStep 2392247 = 3588371) B3588371
theorem B4547183 : Blo 1417528 4547183 := bstep (se 1 (by rfl) ⟨3410387, by rfl⟩ : syracuseStep 4547183 = 6820775) B6820775
theorem B34500593 : Blo 1417528 34500593 := bstep (se 2 (by rfl) ⟨12937722, by rfl⟩ : syracuseStep 34500593 = 25875445) B25875445
theorem B58201355 : Blo 1417528 58201355 := bstep (se 1 (by rfl) ⟨43651016, by rfl⟩ : syracuseStep 58201355 = 87302033) B87302033
theorem B27269567 : Blo 1417528 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B2129273 : Blo 1417528 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B1703935 : Blo 1417528 1703935 := bstep (se 1 (by rfl) ⟨1277951, by rfl⟩ : syracuseStep 1703935 = 2555903) B2555903
theorem B18179711 : Blo 1417528 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B12125821 : Blo 1417528 12125821 := bstep (se 3 (by rfl) ⟨2273591, by rfl⟩ : syracuseStep 12125821 = 4547183) B4547183
theorem B1419515 : Blo 1417528 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B9087653 : Blo 1417528 9087653 := bstep (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) B1703935
theorem B23000395 : Blo 1417528 23000395 := bstep (se 1 (by rfl) ⟨17250296, by rfl⟩ : syracuseStep 23000395 = 34500593) B34500593
theorem B43652519 : Blo 1417528 43652519 := bstep (se 1 (by rfl) ⟨32739389, by rfl⟩ : syracuseStep 43652519 = 65478779) B65478779
theorem B1594831 : Blo 1417528 1594831 := bstep (se 1 (by rfl) ⟨1196123, by rfl⟩ : syracuseStep 1594831 = 2392247) B2392247
theorem B155203613 : Blo 1417528 155203613 := bstep (se 3 (by rfl) ⟨29100677, by rfl⟩ : syracuseStep 155203613 = 58201355) B58201355
theorem B29101679 : Blo 1417528 29101679 := bstep (se 1 (by rfl) ⟨21826259, by rfl⟩ : syracuseStep 29101679 = 43652519) B43652519
theorem B12119807 : Blo 1417528 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B103469075 : Blo 1417528 103469075 := bstep (se 1 (by rfl) ⟨77601806, by rfl⟩ : syracuseStep 103469075 = 155203613) B155203613
theorem B30667193 : Blo 1417528 30667193 := bstep (se 2 (by rfl) ⟨11500197, by rfl⟩ : syracuseStep 30667193 = 23000395) B23000395
theorem B6058435 : Blo 1417528 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B2126441 : Blo 1417528 2126441 := bstep (se 2 (by rfl) ⟨797415, by rfl⟩ : syracuseStep 2126441 = 1594831) B1594831
theorem B16167761 : Blo 1417528 16167761 := bstep (se 2 (by rfl) ⟨6062910, by rfl⟩ : syracuseStep 16167761 = 12125821) B12125821
theorem B1417627 : Blo 1417528 1417627 := bstep (se 1 (by rfl) ⟨1063220, by rfl⟩ : syracuseStep 1417627 = 2126441) B2126441
theorem B8077913 : Blo 1417528 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B19401119 : Blo 1417528 19401119 := bstep (se 1 (by rfl) ⟨14550839, by rfl⟩ : syracuseStep 19401119 = 29101679) B29101679
theorem B8079871 : Blo 1417528 8079871 := bstep (se 1 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 8079871 = 12119807) B12119807
theorem B68979383 : Blo 1417528 68979383 := bstep (se 1 (by rfl) ⟨51734537, by rfl⟩ : syracuseStep 68979383 = 103469075) B103469075
theorem B20444795 : Blo 1417528 20444795 := bstep (se 1 (by rfl) ⟨15333596, by rfl⟩ : syracuseStep 20444795 = 30667193) B30667193
theorem B10778507 : Blo 1417528 10778507 := bstep (se 1 (by rfl) ⟨8083880, by rfl⟩ : syracuseStep 10778507 = 16167761) B16167761
theorem B10773161 : Blo 1417528 10773161 := bstep (se 2 (by rfl) ⟨4039935, by rfl⟩ : syracuseStep 10773161 = 8079871) B8079871
theorem B7185671 : Blo 1417528 7185671 := bstep (se 1 (by rfl) ⟨5389253, by rfl⟩ : syracuseStep 7185671 = 10778507) B10778507
theorem B5385275 : Blo 1417528 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B45986255 : Blo 1417528 45986255 := bstep (se 1 (by rfl) ⟨34489691, by rfl⟩ : syracuseStep 45986255 = 68979383) B68979383
theorem B13629863 : Blo 1417528 13629863 := bstep (se 1 (by rfl) ⟨10222397, by rfl⟩ : syracuseStep 13629863 = 20444795) B20444795
theorem B12934079 : Blo 1417528 12934079 := bstep (se 1 (by rfl) ⟨9700559, by rfl⟩ : syracuseStep 12934079 = 19401119) B19401119
theorem B9086575 : Blo 1417528 9086575 := bstep (se 1 (by rfl) ⟨6814931, by rfl⟩ : syracuseStep 9086575 = 13629863) B13629863
theorem B3590183 : Blo 1417528 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B30657503 : Blo 1417528 30657503 := bstep (se 1 (by rfl) ⟨22993127, by rfl⟩ : syracuseStep 30657503 = 45986255) B45986255
theorem B8622719 : Blo 1417528 8622719 := bstep (se 1 (by rfl) ⟨6467039, by rfl⟩ : syracuseStep 8622719 = 12934079) B12934079
theorem B7182107 : Blo 1417528 7182107 := bstep (se 1 (by rfl) ⟨5386580, by rfl⟩ : syracuseStep 7182107 = 10773161) B10773161
theorem B4790447 : Blo 1417528 4790447 := bstep (se 1 (by rfl) ⟨3592835, by rfl⟩ : syracuseStep 4790447 = 7185671) B7185671
theorem B2393455 : Blo 1417528 2393455 := bstep (se 1 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 2393455 = 3590183) B3590183
theorem B4788071 : Blo 1417528 4788071 := bstep (se 1 (by rfl) ⟨3591053, by rfl⟩ : syracuseStep 4788071 = 7182107) B7182107
theorem B5748479 : Blo 1417528 5748479 := bstep (se 1 (by rfl) ⟨4311359, by rfl⟩ : syracuseStep 5748479 = 8622719) B8622719
theorem B3193631 : Blo 1417528 3193631 := bstep (se 1 (by rfl) ⟨2395223, by rfl⟩ : syracuseStep 3193631 = 4790447) B4790447
theorem B20438335 : Blo 1417528 20438335 := bstep (se 1 (by rfl) ⟨15328751, by rfl⟩ : syracuseStep 20438335 = 30657503) B30657503
theorem B12115433 : Blo 1417528 12115433 := bstep (se 2 (by rfl) ⟨4543287, by rfl⟩ : syracuseStep 12115433 = 9086575) B9086575
theorem B27251113 : Blo 1417528 27251113 := bstep (se 2 (by rfl) ⟨10219167, by rfl⟩ : syracuseStep 27251113 = 20438335) B20438335
theorem B3191273 : Blo 1417528 3191273 := bstep (se 2 (by rfl) ⟨1196727, by rfl⟩ : syracuseStep 3191273 = 2393455) B2393455
theorem B3192047 : Blo 1417528 3192047 := bstep (se 1 (by rfl) ⟨2394035, by rfl⟩ : syracuseStep 3192047 = 4788071) B4788071
theorem B3832319 : Blo 1417528 3832319 := bstep (se 1 (by rfl) ⟨2874239, by rfl⟩ : syracuseStep 3832319 = 5748479) B5748479
theorem B2129087 : Blo 1417528 2129087 := bstep (se 1 (by rfl) ⟨1596815, by rfl⟩ : syracuseStep 2129087 = 3193631) B3193631
theorem B8076955 : Blo 1417528 8076955 := bstep (se 1 (by rfl) ⟨6057716, by rfl⟩ : syracuseStep 8076955 = 12115433) B12115433
theorem B1419391 : Blo 1417528 1419391 := bstep (se 1 (by rfl) ⟨1064543, by rfl⟩ : syracuseStep 1419391 = 2129087) B2129087
theorem B36334817 : Blo 1417528 36334817 := bstep (se 2 (by rfl) ⟨13625556, by rfl⟩ : syracuseStep 36334817 = 27251113) B27251113
theorem B10219517 : Blo 1417528 10219517 := bstep (se 3 (by rfl) ⟨1916159, by rfl⟩ : syracuseStep 10219517 = 3832319) B3832319
theorem B10769273 : Blo 1417528 10769273 := bstep (se 2 (by rfl) ⟨4038477, by rfl⟩ : syracuseStep 10769273 = 8076955) B8076955
theorem B2127515 : Blo 1417528 2127515 := bstep (se 1 (by rfl) ⟨1595636, by rfl⟩ : syracuseStep 2127515 = 3191273) B3191273
theorem B2128031 : Blo 1417528 2128031 := bstep (se 1 (by rfl) ⟨1596023, by rfl⟩ : syracuseStep 2128031 = 3192047) B3192047
theorem B1418343 : Blo 1417528 1418343 := bstep (se 1 (by rfl) ⟨1063757, by rfl⟩ : syracuseStep 1418343 = 2127515) B2127515
theorem B1418687 : Blo 1417528 1418687 := bstep (se 1 (by rfl) ⟨1064015, by rfl⟩ : syracuseStep 1418687 = 2128031) B2128031
theorem B7179515 : Blo 1417528 7179515 := bstep (se 1 (by rfl) ⟨5384636, by rfl⟩ : syracuseStep 7179515 = 10769273) B10769273
theorem B6813011 : Blo 1417528 6813011 := bstep (se 1 (by rfl) ⟨5109758, by rfl⟩ : syracuseStep 6813011 = 10219517) B10219517
theorem B24223211 : Blo 1417528 24223211 := bstep (se 1 (by rfl) ⟨18167408, by rfl⟩ : syracuseStep 24223211 = 36334817) B36334817
theorem B4786343 : Blo 1417528 4786343 := bstep (se 1 (by rfl) ⟨3589757, by rfl⟩ : syracuseStep 4786343 = 7179515) B7179515
theorem B16148807 : Blo 1417528 16148807 := bstep (se 1 (by rfl) ⟨12111605, by rfl⟩ : syracuseStep 16148807 = 24223211) B24223211
theorem B4542007 : Blo 1417528 4542007 := bstep (se 1 (by rfl) ⟨3406505, by rfl⟩ : syracuseStep 4542007 = 6813011) B6813011
theorem B10765871 : Blo 1417528 10765871 := bstep (se 1 (by rfl) ⟨8074403, by rfl⟩ : syracuseStep 10765871 = 16148807) B16148807
theorem B6056009 : Blo 1417528 6056009 := bstep (se 2 (by rfl) ⟨2271003, by rfl⟩ : syracuseStep 6056009 = 4542007) B4542007
theorem B3190895 : Blo 1417528 3190895 := bstep (se 1 (by rfl) ⟨2393171, by rfl⟩ : syracuseStep 3190895 = 4786343) B4786343
theorem B7177247 : Blo 1417528 7177247 := bstep (se 1 (by rfl) ⟨5382935, by rfl⟩ : syracuseStep 7177247 = 10765871) B10765871
theorem B2127263 : Blo 1417528 2127263 := bstep (se 1 (by rfl) ⟨1595447, by rfl⟩ : syracuseStep 2127263 = 3190895) B3190895
theorem B4037339 : Blo 1417528 4037339 := bstep (se 1 (by rfl) ⟨3028004, by rfl⟩ : syracuseStep 4037339 = 6056009) B6056009
theorem B4784831 : Blo 1417528 4784831 := bstep (se 1 (by rfl) ⟨3588623, by rfl⟩ : syracuseStep 4784831 = 7177247) B7177247
theorem B1418175 : Blo 1417528 1418175 := bstep (se 1 (by rfl) ⟨1063631, by rfl⟩ : syracuseStep 1418175 = 2127263) B2127263
theorem B2691559 : Blo 1417528 2691559 := bstep (se 1 (by rfl) ⟨2018669, by rfl⟩ : syracuseStep 2691559 = 4037339) B4037339
theorem B3588745 : Blo 1417528 3588745 := bstep (se 2 (by rfl) ⟨1345779, by rfl⟩ : syracuseStep 3588745 = 2691559) B2691559
theorem B3189887 : Blo 1417528 3189887 := bstep (se 1 (by rfl) ⟨2392415, by rfl⟩ : syracuseStep 3189887 = 4784831) B4784831
theorem B4784993 : Blo 1417528 4784993 := bstep (se 2 (by rfl) ⟨1794372, by rfl⟩ : syracuseStep 4784993 = 3588745) B3588745
theorem B2126591 : Blo 1417528 2126591 := bstep (se 1 (by rfl) ⟨1594943, by rfl⟩ : syracuseStep 2126591 = 3189887) B3189887
theorem B1417727 : Blo 1417528 1417727 := bstep (se 1 (by rfl) ⟨1063295, by rfl⟩ : syracuseStep 1417727 = 2126591) B2126591
theorem B3189995 : Blo 1417528 3189995 := bstep (se 1 (by rfl) ⟨2392496, by rfl⟩ : syracuseStep 3189995 = 4784993) B4784993
theorem B2126663 : Blo 1417528 2126663 := bstep (se 1 (by rfl) ⟨1594997, by rfl⟩ : syracuseStep 2126663 = 3189995) B3189995
theorem B1417775 : Blo 1417528 1417775 := bstep (se 1 (by rfl) ⟨1063331, by rfl⟩ : syracuseStep 1417775 = 2126663) B2126663

theorem C0 (j : ℕ) (h1 : 354382 ≤ j) (h2 : j ≤ 354881) : Blo 1417528 (4 * j + 3) := by
  interval_cases j
  · exact B1417531
  · exact B1417535
  · exact B1417539
  · exact B1417543
  · exact B1417547
  · exact B1417551
  · exact B1417555
  · exact B1417559
  · exact B1417563
  · exact B1417567
  · exact B1417571
  · exact B1417575
  · exact B1417579
  · exact B1417583
  · exact B1417587
  · exact B1417591
  · exact B1417595
  · exact B1417599
  · exact B1417603
  · exact B1417607
  · exact B1417611
  · exact B1417615
  · exact B1417619
  · exact B1417623
  · exact B1417627
  · exact B1417631
  · exact B1417635
  · exact B1417639
  · exact B1417643
  · exact B1417647
  · exact B1417651
  · exact B1417655
  · exact B1417659
  · exact B1417663
  · exact B1417667
  · exact B1417671
  · exact B1417675
  · exact B1417679
  · exact B1417683
  · exact B1417687
  · exact B1417691
  · exact B1417695
  · exact B1417699
  · exact B1417703
  · exact B1417707
  · exact B1417711
  · exact B1417715
  · exact B1417719
  · exact B1417723
  · exact B1417727
  · exact B1417731
  · exact B1417735
  · exact B1417739
  · exact B1417743
  · exact B1417747
  · exact B1417751
  · exact B1417755
  · exact B1417759
  · exact B1417763
  · exact B1417767
  · exact B1417771
  · exact B1417775
  · exact B1417779
  · exact B1417783
  · exact B1417787
  · exact B1417791
  · exact B1417795
  · exact B1417799
  · exact B1417803
  · exact B1417807
  · exact B1417811
  · exact B1417815
  · exact B1417819
  · exact B1417823
  · exact B1417827
  · exact B1417831
  · exact B1417835
  · exact B1417839
  · exact B1417843
  · exact B1417847
  · exact B1417851
  · exact B1417855
  · exact B1417859
  · exact B1417863
  · exact B1417867
  · exact B1417871
  · exact B1417875
  · exact B1417879
  · exact B1417883
  · exact B1417887
  · exact B1417891
  · exact B1417895
  · exact B1417899
  · exact B1417903
  · exact B1417907
  · exact B1417911
  · exact B1417915
  · exact B1417919
  · exact B1417923
  · exact B1417927
  · exact B1417931
  · exact B1417935
  · exact B1417939
  · exact B1417943
  · exact B1417947
  · exact B1417951
  · exact B1417955
  · exact B1417959
  · exact B1417963
  · exact B1417967
  · exact B1417971
  · exact B1417975
  · exact B1417979
  · exact B1417983
  · exact B1417987
  · exact B1417991
  · exact B1417995
  · exact B1417999
  · exact B1418003
  · exact B1418007
  · exact B1418011
  · exact B1418015
  · exact B1418019
  · exact B1418023
  · exact B1418027
  · exact B1418031
  · exact B1418035
  · exact B1418039
  · exact B1418043
  · exact B1418047
  · exact B1418051
  · exact B1418055
  · exact B1418059
  · exact B1418063
  · exact B1418067
  · exact B1418071
  · exact B1418075
  · exact B1418079
  · exact B1418083
  · exact B1418087
  · exact B1418091
  · exact B1418095
  · exact B1418099
  · exact B1418103
  · exact B1418107
  · exact B1418111
  · exact B1418115
  · exact B1418119
  · exact B1418123
  · exact B1418127
  · exact B1418131
  · exact B1418135
  · exact B1418139
  · exact B1418143
  · exact B1418147
  · exact B1418151
  · exact B1418155
  · exact B1418159
  · exact B1418163
  · exact B1418167
  · exact B1418171
  · exact B1418175
  · exact B1418179
  · exact B1418183
  · exact B1418187
  · exact B1418191
  · exact B1418195
  · exact B1418199
  · exact B1418203
  · exact B1418207
  · exact B1418211
  · exact B1418215
  · exact B1418219
  · exact B1418223
  · exact B1418227
  · exact B1418231
  · exact B1418235
  · exact B1418239
  · exact B1418243
  · exact B1418247
  · exact B1418251
  · exact B1418255
  · exact B1418259
  · exact B1418263
  · exact B1418267
  · exact B1418271
  · exact B1418275
  · exact B1418279
  · exact B1418283
  · exact B1418287
  · exact B1418291
  · exact B1418295
  · exact B1418299
  · exact B1418303
  · exact B1418307
  · exact B1418311
  · exact B1418315
  · exact B1418319
  · exact B1418323
  · exact B1418327
  · exact B1418331
  · exact B1418335
  · exact B1418339
  · exact B1418343
  · exact B1418347
  · exact B1418351
  · exact B1418355
  · exact B1418359
  · exact B1418363
  · exact B1418367
  · exact B1418371
  · exact B1418375
  · exact B1418379
  · exact B1418383
  · exact B1418387
  · exact B1418391
  · exact B1418395
  · exact B1418399
  · exact B1418403
  · exact B1418407
  · exact B1418411
  · exact B1418415
  · exact B1418419
  · exact B1418423
  · exact B1418427
  · exact B1418431
  · exact B1418435
  · exact B1418439
  · exact B1418443
  · exact B1418447
  · exact B1418451
  · exact B1418455
  · exact B1418459
  · exact B1418463
  · exact B1418467
  · exact B1418471
  · exact B1418475
  · exact B1418479
  · exact B1418483
  · exact B1418487
  · exact B1418491
  · exact B1418495
  · exact B1418499
  · exact B1418503
  · exact B1418507
  · exact B1418511
  · exact B1418515
  · exact B1418519
  · exact B1418523
  · exact B1418527
  · exact B1418531
  · exact B1418535
  · exact B1418539
  · exact B1418543
  · exact B1418547
  · exact B1418551
  · exact B1418555
  · exact B1418559
  · exact B1418563
  · exact B1418567
  · exact B1418571
  · exact B1418575
  · exact B1418579
  · exact B1418583
  · exact B1418587
  · exact B1418591
  · exact B1418595
  · exact B1418599
  · exact B1418603
  · exact B1418607
  · exact B1418611
  · exact B1418615
  · exact B1418619
  · exact B1418623
  · exact B1418627
  · exact B1418631
  · exact B1418635
  · exact B1418639
  · exact B1418643
  · exact B1418647
  · exact B1418651
  · exact B1418655
  · exact B1418659
  · exact B1418663
  · exact B1418667
  · exact B1418671
  · exact B1418675
  · exact B1418679
  · exact B1418683
  · exact B1418687
  · exact B1418691
  · exact B1418695
  · exact B1418699
  · exact B1418703
  · exact B1418707
  · exact B1418711
  · exact B1418715
  · exact B1418719
  · exact B1418723
  · exact B1418727
  · exact B1418731
  · exact B1418735
  · exact B1418739
  · exact B1418743
  · exact B1418747
  · exact B1418751
  · exact B1418755
  · exact B1418759
  · exact B1418763
  · exact B1418767
  · exact B1418771
  · exact B1418775
  · exact B1418779
  · exact B1418783
  · exact B1418787
  · exact B1418791
  · exact B1418795
  · exact B1418799
  · exact B1418803
  · exact B1418807
  · exact B1418811
  · exact B1418815
  · exact B1418819
  · exact B1418823
  · exact B1418827
  · exact B1418831
  · exact B1418835
  · exact B1418839
  · exact B1418843
  · exact B1418847
  · exact B1418851
  · exact B1418855
  · exact B1418859
  · exact B1418863
  · exact B1418867
  · exact B1418871
  · exact B1418875
  · exact B1418879
  · exact B1418883
  · exact B1418887
  · exact B1418891
  · exact B1418895
  · exact B1418899
  · exact B1418903
  · exact B1418907
  · exact B1418911
  · exact B1418915
  · exact B1418919
  · exact B1418923
  · exact B1418927
  · exact B1418931
  · exact B1418935
  · exact B1418939
  · exact B1418943
  · exact B1418947
  · exact B1418951
  · exact B1418955
  · exact B1418959
  · exact B1418963
  · exact B1418967
  · exact B1418971
  · exact B1418975
  · exact B1418979
  · exact B1418983
  · exact B1418987
  · exact B1418991
  · exact B1418995
  · exact B1418999
  · exact B1419003
  · exact B1419007
  · exact B1419011
  · exact B1419015
  · exact B1419019
  · exact B1419023
  · exact B1419027
  · exact B1419031
  · exact B1419035
  · exact B1419039
  · exact B1419043
  · exact B1419047
  · exact B1419051
  · exact B1419055
  · exact B1419059
  · exact B1419063
  · exact B1419067
  · exact B1419071
  · exact B1419075
  · exact B1419079
  · exact B1419083
  · exact B1419087
  · exact B1419091
  · exact B1419095
  · exact B1419099
  · exact B1419103
  · exact B1419107
  · exact B1419111
  · exact B1419115
  · exact B1419119
  · exact B1419123
  · exact B1419127
  · exact B1419131
  · exact B1419135
  · exact B1419139
  · exact B1419143
  · exact B1419147
  · exact B1419151
  · exact B1419155
  · exact B1419159
  · exact B1419163
  · exact B1419167
  · exact B1419171
  · exact B1419175
  · exact B1419179
  · exact B1419183
  · exact B1419187
  · exact B1419191
  · exact B1419195
  · exact B1419199
  · exact B1419203
  · exact B1419207
  · exact B1419211
  · exact B1419215
  · exact B1419219
  · exact B1419223
  · exact B1419227
  · exact B1419231
  · exact B1419235
  · exact B1419239
  · exact B1419243
  · exact B1419247
  · exact B1419251
  · exact B1419255
  · exact B1419259
  · exact B1419263
  · exact B1419267
  · exact B1419271
  · exact B1419275
  · exact B1419279
  · exact B1419283
  · exact B1419287
  · exact B1419291
  · exact B1419295
  · exact B1419299
  · exact B1419303
  · exact B1419307
  · exact B1419311
  · exact B1419315
  · exact B1419319
  · exact B1419323
  · exact B1419327
  · exact B1419331
  · exact B1419335
  · exact B1419339
  · exact B1419343
  · exact B1419347
  · exact B1419351
  · exact B1419355
  · exact B1419359
  · exact B1419363
  · exact B1419367
  · exact B1419371
  · exact B1419375
  · exact B1419379
  · exact B1419383
  · exact B1419387
  · exact B1419391
  · exact B1419395
  · exact B1419399
  · exact B1419403
  · exact B1419407
  · exact B1419411
  · exact B1419415
  · exact B1419419
  · exact B1419423
  · exact B1419427
  · exact B1419431
  · exact B1419435
  · exact B1419439
  · exact B1419443
  · exact B1419447
  · exact B1419451
  · exact B1419455
  · exact B1419459
  · exact B1419463
  · exact B1419467
  · exact B1419471
  · exact B1419475
  · exact B1419479
  · exact B1419483
  · exact B1419487
  · exact B1419491
  · exact B1419495
  · exact B1419499
  · exact B1419503
  · exact B1419507
  · exact B1419511
  · exact B1419515
  · exact B1419519
  · exact B1419523
  · exact B1419527

theorem solution (m : ℕ) (hlo : 1417528 ≤ m) (hhi : m ≤ 1419528) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 354382 ≤ j := by omega
    have hj2 : j ≤ 354881 := by omega
    have hb : Blo 1417528 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
