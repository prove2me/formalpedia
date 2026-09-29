-- Prove2me | solution 1 for syracuse_descends_range_1344991_1346991
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:47.089111+00:00
-- url     : https://prove2.me/submissions/b750aa87-2150-4844-a684-48d421638824

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


theorem B1843205 : Blo 1344991 1843205 := bbase (se 4 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 1843205 = 345601) (by norm_num)
theorem B3407933 : Blo 1344991 3407933 := bbase (se 3 (by rfl) ⟨638987, by rfl⟩ : syracuseStep 3407933 = 1277975) (by norm_num)
theorem B2555965 : Blo 1344991 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B4849733 : Blo 1344991 4849733 := bbase (se 4 (by rfl) ⟨454662, by rfl⟩ : syracuseStep 4849733 = 909325) (by norm_num)
theorem B1704017 : Blo 1344991 1704017 := bbase (se 2 (by rfl) ⟨639006, by rfl⟩ : syracuseStep 1704017 = 1278013) (by norm_num)
theorem B1917037 : Blo 1344991 1917037 := bbase (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) (by norm_num)
theorem B5251189 : Blo 1344991 5251189 := bbase (se 5 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 5251189 = 492299) (by norm_num)
theorem B1704073 : Blo 1344991 1704073 := bbase (se 2 (by rfl) ⟨639027, by rfl⟩ : syracuseStep 1704073 = 1278055) (by norm_num)
theorem B4849861 : Blo 1344991 4849861 := bbase (se 4 (by rfl) ⟨454674, by rfl⟩ : syracuseStep 4849861 = 909349) (by norm_num)
theorem B1704169 : Blo 1344991 1704169 := bbase (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) (by norm_num)
theorem B3236125 : Blo 1344991 3236125 := bbase (se 3 (by rfl) ⟨606773, by rfl⟩ : syracuseStep 3236125 = 1213547) (by norm_num)
theorem B2302277 : Blo 1344991 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B2154853 : Blo 1344991 2154853 := bbase (se 4 (by rfl) ⟨202017, by rfl⟩ : syracuseStep 2154853 = 404035) (by norm_num)
theorem B2556269 : Blo 1344991 2556269 := bbase (se 3 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 2556269 = 958601) (by norm_num)
theorem B6816149 : Blo 1344991 6816149 := bbase (se 6 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 6816149 = 319507) (by norm_num)
theorem B3408277 : Blo 1344991 3408277 := bbase (se 6 (by rfl) ⟨79881, by rfl⟩ : syracuseStep 3408277 = 159763) (by norm_num)
theorem B1704341 : Blo 1344991 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B2589101 : Blo 1344991 2589101 := bbase (se 3 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 2589101 = 970913) (by norm_num)
theorem B2425277 : Blo 1344991 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B2875837 : Blo 1344991 2875837 := bbase (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) (by norm_num)
theorem B1917373 : Blo 1344991 1917373 := bbase (se 3 (by rfl) ⟨359507, by rfl⟩ : syracuseStep 1917373 = 719015) (by norm_num)
theorem B1704397 : Blo 1344991 1704397 := bbase (se 3 (by rfl) ⟨319574, by rfl⟩ : syracuseStep 1704397 = 639149) (by norm_num)
theorem B2425349 : Blo 1344991 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B3408389 : Blo 1344991 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B5112341 : Blo 1344991 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B2269741 : Blo 1344991 2269741 := bbase (se 3 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 2269741 = 851153) (by norm_num)
theorem B1704493 : Blo 1344991 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B2269829 : Blo 1344991 2269829 := bbase (se 4 (by rfl) ⟨212796, by rfl⟩ : syracuseStep 2269829 = 425593) (by norm_num)
theorem B6472325 : Blo 1344991 6472325 := bbase (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) (by norm_num)
theorem B1917589 : Blo 1344991 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B3408581 : Blo 1344991 3408581 := bbase (se 4 (by rfl) ⟨319554, by rfl⟩ : syracuseStep 3408581 = 639109) (by norm_num)
theorem B1704665 : Blo 1344991 1704665 := bbase (se 2 (by rfl) ⟨639249, by rfl⟩ : syracuseStep 1704665 = 1278499) (by norm_num)
theorem B2269957 : Blo 1344991 2269957 := bbase (se 4 (by rfl) ⟨212808, by rfl⟩ : syracuseStep 2269957 = 425617) (by norm_num)
theorem B1704721 : Blo 1344991 1704721 := bbase (se 2 (by rfl) ⟨639270, by rfl⟩ : syracuseStep 1704721 = 1278541) (by norm_num)
theorem B7668533 : Blo 1344991 7668533 := bbase (se 5 (by rfl) ⟨359462, by rfl⟩ : syracuseStep 7668533 = 718925) (by norm_num)
theorem B5112629 : Blo 1344991 5112629 := bbase (se 5 (by rfl) ⟨239654, by rfl⟩ : syracuseStep 5112629 = 479309) (by norm_num)
theorem B3834677 : Blo 1344991 3834677 := bbase (se 5 (by rfl) ⟨179750, by rfl⟩ : syracuseStep 3834677 = 359501) (by norm_num)
theorem B2270045 : Blo 1344991 2270045 := bbase (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) (by norm_num)
theorem B2155405 : Blo 1344991 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B11494325 : Blo 1344991 11494325 := bbase (se 5 (by rfl) ⟨538796, by rfl⟩ : syracuseStep 11494325 = 1077593) (by norm_num)
theorem B2270173 : Blo 1344991 2270173 := bbase (se 3 (by rfl) ⟨425657, by rfl⟩ : syracuseStep 2270173 = 851315) (by norm_num)
theorem B3638261 : Blo 1344991 3638261 := bbase (se 5 (by rfl) ⟨170543, by rfl⟩ : syracuseStep 3638261 = 341087) (by norm_num)
theorem B2425853 : Blo 1344991 2425853 := bbase (se 3 (by rfl) ⟨454847, by rfl⟩ : syracuseStep 2425853 = 909695) (by norm_num)
theorem B3408925 : Blo 1344991 3408925 := bbase (se 3 (by rfl) ⟨639173, by rfl⟩ : syracuseStep 3408925 = 1278347) (by norm_num)
theorem B2270261 : Blo 1344991 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B10921013 : Blo 1344991 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B2557021 : Blo 1344991 2557021 := bbase (se 3 (by rfl) ⟨479441, by rfl⟩ : syracuseStep 2557021 = 958883) (by norm_num)
theorem B4310117 : Blo 1344991 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B4539509 : Blo 1344991 4539509 := bbase (se 5 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 4539509 = 425579) (by norm_num)
theorem B2155661 : Blo 1344991 2155661 := bbase (se 3 (by rfl) ⟨404186, by rfl⟩ : syracuseStep 2155661 = 808373) (by norm_num)
theorem B3409037 : Blo 1344991 3409037 := bbase (se 3 (by rfl) ⟨639194, by rfl⟩ : syracuseStep 3409037 = 1278389) (by norm_num)
theorem B2270389 : Blo 1344991 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B2303213 : Blo 1344991 2303213 := bbase (se 3 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 2303213 = 863705) (by norm_num)
theorem B2557165 : Blo 1344991 2557165 := bbase (se 3 (by rfl) ⟨479468, by rfl⟩ : syracuseStep 2557165 = 958937) (by norm_num)
theorem B2073853 : Blo 1344991 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B2270477 : Blo 1344991 2270477 := bbase (se 3 (by rfl) ⟨425714, by rfl⟩ : syracuseStep 2270477 = 851429) (by norm_num)
theorem B2458925 : Blo 1344991 2458925 := bbase (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) (by norm_num)
theorem B2876725 : Blo 1344991 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B3409229 : Blo 1344991 3409229 := bbase (se 3 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 3409229 = 1278461) (by norm_num)
theorem B2270605 : Blo 1344991 2270605 := bbase (se 3 (by rfl) ⟨425738, by rfl⟩ : syracuseStep 2270605 = 851477) (by norm_num)
theorem B2270693 : Blo 1344991 2270693 := bbase (se 4 (by rfl) ⟨212877, by rfl⟩ : syracuseStep 2270693 = 425755) (by norm_num)
theorem B4539941 : Blo 1344991 4539941 := bbase (se 4 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 4539941 = 851239) (by norm_num)
theorem B2270821 : Blo 1344991 2270821 := bbase (se 4 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 2270821 = 425779) (by norm_num)
theorem B5457557 : Blo 1344991 5457557 := bbase (se 6 (by rfl) ⟨127911, by rfl⟩ : syracuseStep 5457557 = 255823) (by norm_num)
theorem B6817445 : Blo 1344991 6817445 := bbase (se 4 (by rfl) ⟨639135, by rfl⟩ : syracuseStep 6817445 = 1278271) (by norm_num)
theorem B3409573 : Blo 1344991 3409573 := bbase (se 4 (by rfl) ⟨319647, by rfl⟩ : syracuseStep 3409573 = 639295) (by norm_num)
theorem B2270909 : Blo 1344991 2270909 := bbase (se 3 (by rfl) ⟨425795, by rfl⟩ : syracuseStep 2270909 = 851591) (by norm_num)
theorem B2271037 : Blo 1344991 2271037 := bbase (se 3 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 2271037 = 851639) (by norm_num)
theorem B2156365 : Blo 1344991 2156365 := bbase (se 3 (by rfl) ⟨404318, by rfl⟩ : syracuseStep 2156365 = 808637) (by norm_num)
theorem B2074493 : Blo 1344991 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B2271125 : Blo 1344991 2271125 := bbase (se 6 (by rfl) ⟨53229, by rfl⟩ : syracuseStep 2271125 = 106459) (by norm_num)
theorem B4540373 : Blo 1344991 4540373 := bbase (se 7 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 4540373 = 106415) (by norm_num)
theorem B5113813 : Blo 1344991 5113813 := bbase (se 7 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 5113813 = 119855) (by norm_num)
theorem B3246101 : Blo 1344991 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B2271253 : Blo 1344991 2271253 := bbase (se 6 (by rfl) ⟨53232, by rfl⟩ : syracuseStep 2271253 = 106465) (by norm_num)
theorem B4605989 : Blo 1344991 4605989 := bbase (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) (by norm_num)
theorem B6809669 : Blo 1344991 6809669 := bbase (se 4 (by rfl) ⟨638406, by rfl⟩ : syracuseStep 6809669 = 1276813) (by norm_num)
theorem B2271341 : Blo 1344991 2271341 := bbase (se 3 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 2271341 = 851753) (by norm_num)
theorem B3451045 : Blo 1344991 3451045 := bbase (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) (by norm_num)
theorem B2730181 : Blo 1344991 2730181 := bbase (se 4 (by rfl) ⟨255954, by rfl⟩ : syracuseStep 2730181 = 511909) (by norm_num)
theorem B2017493 : Blo 1344991 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B2017517 : Blo 1344991 2017517 := bbase (se 3 (by rfl) ⟨378284, by rfl⟩ : syracuseStep 2017517 = 756569) (by norm_num)
theorem B2271469 : Blo 1344991 2271469 := bbase (se 3 (by rfl) ⟨425900, by rfl⟩ : syracuseStep 2271469 = 851801) (by norm_num)
theorem B2156789 : Blo 1344991 2156789 := bbase (se 5 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 2156789 = 202199) (by norm_num)
theorem B2017541 : Blo 1344991 2017541 := bbase (se 4 (by rfl) ⟨189144, by rfl⟩ : syracuseStep 2017541 = 378289) (by norm_num)
theorem B5114117 : Blo 1344991 5114117 := bbase (se 4 (by rfl) ⟨479448, by rfl⟩ : syracuseStep 5114117 = 958897) (by norm_num)
theorem B2017565 : Blo 1344991 2017565 := bbase (se 3 (by rfl) ⟨378293, by rfl⟩ : syracuseStep 2017565 = 756587) (by norm_num)
theorem B2017589 : Blo 1344991 2017589 := bbase (se 5 (by rfl) ⟨94574, by rfl⟩ : syracuseStep 2017589 = 189149) (by norm_num)
theorem B2271557 : Blo 1344991 2271557 := bbase (se 4 (by rfl) ⟨212958, by rfl⟩ : syracuseStep 2271557 = 425917) (by norm_num)
theorem B2017613 : Blo 1344991 2017613 := bbase (se 3 (by rfl) ⟨378302, by rfl⟩ : syracuseStep 2017613 = 756605) (by norm_num)
theorem B2017637 : Blo 1344991 2017637 := bbase (se 4 (by rfl) ⟨189153, by rfl⟩ : syracuseStep 2017637 = 378307) (by norm_num)
theorem B4311397 : Blo 1344991 4311397 := bbase (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) (by norm_num)
theorem B2017661 : Blo 1344991 2017661 := bbase (se 3 (by rfl) ⟨378311, by rfl⟩ : syracuseStep 2017661 = 756623) (by norm_num)
theorem B4540805 : Blo 1344991 4540805 := bbase (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) (by norm_num)
theorem B2017685 : Blo 1344991 2017685 := bbase (se 6 (by rfl) ⟨47289, by rfl⟩ : syracuseStep 2017685 = 94579) (by norm_num)
theorem B2017709 : Blo 1344991 2017709 := bbase (se 3 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 2017709 = 756641) (by norm_num)
theorem B2017733 : Blo 1344991 2017733 := bbase (se 4 (by rfl) ⟨189162, by rfl⟩ : syracuseStep 2017733 = 378325) (by norm_num)
theorem B2271685 : Blo 1344991 2271685 := bbase (se 4 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 2271685 = 425941) (by norm_num)
theorem B2017757 : Blo 1344991 2017757 := bbase (se 3 (by rfl) ⟨378329, by rfl⟩ : syracuseStep 2017757 = 756659) (by norm_num)
theorem B2017781 : Blo 1344991 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B2017805 : Blo 1344991 2017805 := bbase (se 3 (by rfl) ⟨378338, by rfl⟩ : syracuseStep 2017805 = 756677) (by norm_num)
theorem B2157077 : Blo 1344991 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B2271773 : Blo 1344991 2271773 := bbase (se 3 (by rfl) ⟨425957, by rfl⟩ : syracuseStep 2271773 = 851915) (by norm_num)
theorem B2017829 : Blo 1344991 2017829 := bbase (se 4 (by rfl) ⟨189171, by rfl⟩ : syracuseStep 2017829 = 378343) (by norm_num)
theorem B2017853 : Blo 1344991 2017853 := bbase (se 3 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 2017853 = 756695) (by norm_num)
theorem B2017877 : Blo 1344991 2017877 := bbase (se 8 (by rfl) ⟨11823, by rfl⟩ : syracuseStep 2017877 = 23647) (by norm_num)
theorem B2017901 : Blo 1344991 2017901 := bbase (se 3 (by rfl) ⟨378356, by rfl⟩ : syracuseStep 2017901 = 756713) (by norm_num)
theorem B1534573 : Blo 1344991 1534573 := bbase (se 3 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 1534573 = 575465) (by norm_num)
theorem B2017925 : Blo 1344991 2017925 := bbase (se 4 (by rfl) ⟨189180, by rfl⟩ : syracuseStep 2017925 = 378361) (by norm_num)
theorem B2017949 : Blo 1344991 2017949 := bbase (se 3 (by rfl) ⟨378365, by rfl⟩ : syracuseStep 2017949 = 756731) (by norm_num)
theorem B2271901 : Blo 1344991 2271901 := bbase (se 3 (by rfl) ⟨425981, by rfl⟩ : syracuseStep 2271901 = 851963) (by norm_num)
theorem B2017973 : Blo 1344991 2017973 := bbase (se 5 (by rfl) ⟨94592, by rfl⟩ : syracuseStep 2017973 = 189185) (by norm_num)
theorem B4606645 : Blo 1344991 4606645 := bbase (se 5 (by rfl) ⟨215936, by rfl⟩ : syracuseStep 4606645 = 431873) (by norm_num)
theorem B2017997 : Blo 1344991 2017997 := bbase (se 3 (by rfl) ⟨378374, by rfl⟩ : syracuseStep 2017997 = 756749) (by norm_num)
theorem B2018021 : Blo 1344991 2018021 := bbase (se 4 (by rfl) ⟨189189, by rfl⟩ : syracuseStep 2018021 = 378379) (by norm_num)
theorem B2271989 : Blo 1344991 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B2157301 : Blo 1344991 2157301 := bbase (se 5 (by rfl) ⟨101123, by rfl⟩ : syracuseStep 2157301 = 202247) (by norm_num)
theorem B2018045 : Blo 1344991 2018045 := bbase (se 3 (by rfl) ⟨378383, by rfl⟩ : syracuseStep 2018045 = 756767) (by norm_num)
theorem B2460413 : Blo 1344991 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B2018069 : Blo 1344991 2018069 := bbase (se 6 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 2018069 = 94597) (by norm_num)
theorem B4606757 : Blo 1344991 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B2018093 : Blo 1344991 2018093 := bbase (se 3 (by rfl) ⟨378392, by rfl⟩ : syracuseStep 2018093 = 756785) (by norm_num)
theorem B4541237 : Blo 1344991 4541237 := bbase (se 5 (by rfl) ⟨212870, by rfl⟩ : syracuseStep 4541237 = 425741) (by norm_num)
theorem B2018117 : Blo 1344991 2018117 := bbase (se 4 (by rfl) ⟨189198, by rfl⟩ : syracuseStep 2018117 = 378397) (by norm_num)
theorem B1477441 : Blo 1344991 1477441 := bbase (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) (by norm_num)
theorem B1616717 : Blo 1344991 1616717 := bbase (se 3 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 1616717 = 606269) (by norm_num)
theorem B2018141 : Blo 1344991 2018141 := bbase (se 3 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 2018141 = 756803) (by norm_num)
theorem B6466405 : Blo 1344991 6466405 := bbase (se 4 (by rfl) ⟨606225, by rfl⟩ : syracuseStep 6466405 = 1212451) (by norm_num)
theorem B2018165 : Blo 1344991 2018165 := bbase (se 5 (by rfl) ⟨94601, by rfl⟩ : syracuseStep 2018165 = 189203) (by norm_num)
theorem B2272117 : Blo 1344991 2272117 := bbase (se 5 (by rfl) ⟨106505, by rfl⟩ : syracuseStep 2272117 = 213011) (by norm_num)
theorem B2018189 : Blo 1344991 2018189 := bbase (se 3 (by rfl) ⟨378410, by rfl⟩ : syracuseStep 2018189 = 756821) (by norm_num)
theorem B2018213 : Blo 1344991 2018213 := bbase (se 4 (by rfl) ⟨189207, by rfl⟩ : syracuseStep 2018213 = 378415) (by norm_num)
theorem B6818741 : Blo 1344991 6818741 := bbase (se 5 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 6818741 = 639257) (by norm_num)
theorem B2018237 : Blo 1344991 2018237 := bbase (se 3 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 2018237 = 756839) (by norm_num)
theorem B2272205 : Blo 1344991 2272205 := bbase (se 3 (by rfl) ⟨426038, by rfl⟩ : syracuseStep 2272205 = 852077) (by norm_num)
theorem B2018261 : Blo 1344991 2018261 := bbase (se 7 (by rfl) ⟨23651, by rfl⟩ : syracuseStep 2018261 = 47303) (by norm_num)
theorem B2018285 : Blo 1344991 2018285 := bbase (se 3 (by rfl) ⟨378428, by rfl⟩ : syracuseStep 2018285 = 756857) (by norm_num)
theorem B2558965 : Blo 1344991 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B2018309 : Blo 1344991 2018309 := bbase (se 4 (by rfl) ⟨189216, by rfl⟩ : syracuseStep 2018309 = 378433) (by norm_num)
theorem B2018333 : Blo 1344991 2018333 := bbase (se 3 (by rfl) ⟨378437, by rfl⟩ : syracuseStep 2018333 = 756875) (by norm_num)
theorem B2018357 : Blo 1344991 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B2018381 : Blo 1344991 2018381 := bbase (se 3 (by rfl) ⟨378446, by rfl⟩ : syracuseStep 2018381 = 756893) (by norm_num)
theorem B2272333 : Blo 1344991 2272333 := bbase (se 3 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 2272333 = 852125) (by norm_num)
theorem B2018405 : Blo 1344991 2018405 := bbase (se 4 (by rfl) ⟨189225, by rfl⟩ : syracuseStep 2018405 = 378451) (by norm_num)
theorem B2018429 : Blo 1344991 2018429 := bbase (se 3 (by rfl) ⟨378455, by rfl⟩ : syracuseStep 2018429 = 756911) (by norm_num)
theorem B1617025 : Blo 1344991 1617025 := bbase (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) (by norm_num)
theorem B2018453 : Blo 1344991 2018453 := bbase (se 6 (by rfl) ⟨47307, by rfl⟩ : syracuseStep 2018453 = 94615) (by norm_num)
theorem B1436825 : Blo 1344991 1436825 := bbase (se 2 (by rfl) ⟨538809, by rfl⟩ : syracuseStep 1436825 = 1077619) (by norm_num)
theorem B2272421 : Blo 1344991 2272421 := bbase (se 4 (by rfl) ⟨213039, by rfl⟩ : syracuseStep 2272421 = 426079) (by norm_num)
theorem B2018477 : Blo 1344991 2018477 := bbase (se 3 (by rfl) ⟨378464, by rfl⟩ : syracuseStep 2018477 = 756929) (by norm_num)
theorem B3640501 : Blo 1344991 3640501 := bbase (se 5 (by rfl) ⟨170648, by rfl⟩ : syracuseStep 3640501 = 341297) (by norm_num)
theorem B2018501 : Blo 1344991 2018501 := bbase (se 4 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 2018501 = 378469) (by norm_num)
theorem B2018525 : Blo 1344991 2018525 := bbase (se 3 (by rfl) ⟨378473, by rfl⟩ : syracuseStep 2018525 = 756947) (by norm_num)
theorem B4541669 : Blo 1344991 4541669 := bbase (se 4 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 4541669 = 851563) (by norm_num)
theorem B2018549 : Blo 1344991 2018549 := bbase (se 5 (by rfl) ⟨94619, by rfl⟩ : syracuseStep 2018549 = 189239) (by norm_num)
theorem B2018573 : Blo 1344991 2018573 := bbase (se 3 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 2018573 = 756965) (by norm_num)
theorem B2624797 : Blo 1344991 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B2018597 : Blo 1344991 2018597 := bbase (se 4 (by rfl) ⟨189243, by rfl⟩ : syracuseStep 2018597 = 378487) (by norm_num)
theorem B2272549 : Blo 1344991 2272549 := bbase (se 4 (by rfl) ⟨213051, by rfl⟩ : syracuseStep 2272549 = 426103) (by norm_num)
theorem B1617193 : Blo 1344991 1617193 := bbase (se 2 (by rfl) ⟨606447, by rfl⟩ : syracuseStep 1617193 = 1212895) (by norm_num)
theorem B2018621 : Blo 1344991 2018621 := bbase (se 3 (by rfl) ⟨378491, by rfl⟩ : syracuseStep 2018621 = 756983) (by norm_num)
theorem B6810965 : Blo 1344991 6810965 := bbase (se 11 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 6810965 = 9977) (by norm_num)
theorem B2018645 : Blo 1344991 2018645 := bbase (se 11 (by rfl) ⟨1478, by rfl⟩ : syracuseStep 2018645 = 2957) (by norm_num)
theorem B3026285 : Blo 1344991 3026285 := bbase (se 3 (by rfl) ⟨567428, by rfl⟩ : syracuseStep 3026285 = 1134857) (by norm_num)
theorem B2018669 : Blo 1344991 2018669 := bbase (se 3 (by rfl) ⟨378500, by rfl⟩ : syracuseStep 2018669 = 757001) (by norm_num)
theorem B2272637 : Blo 1344991 2272637 := bbase (se 3 (by rfl) ⟨426119, by rfl⟩ : syracuseStep 2272637 = 852239) (by norm_num)
theorem B2018693 : Blo 1344991 2018693 := bbase (se 4 (by rfl) ⟨189252, by rfl⟩ : syracuseStep 2018693 = 378505) (by norm_num)
theorem B5746069 : Blo 1344991 5746069 := bbase (se 6 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 5746069 = 269347) (by norm_num)
theorem B2018717 : Blo 1344991 2018717 := bbase (se 3 (by rfl) ⟨378509, by rfl⟩ : syracuseStep 2018717 = 757019) (by norm_num)
theorem B3026357 : Blo 1344991 3026357 := bbase (se 5 (by rfl) ⟨141860, by rfl⟩ : syracuseStep 3026357 = 283721) (by norm_num)
theorem B2018741 : Blo 1344991 2018741 := bbase (se 5 (by rfl) ⟨94628, by rfl⟩ : syracuseStep 2018741 = 189257) (by norm_num)
theorem B3452357 : Blo 1344991 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2018765 : Blo 1344991 2018765 := bbase (se 3 (by rfl) ⟨378518, by rfl⟩ : syracuseStep 2018765 = 757037) (by norm_num)
theorem B2018789 : Blo 1344991 2018789 := bbase (se 4 (by rfl) ⟨189261, by rfl⟩ : syracuseStep 2018789 = 378523) (by norm_num)
theorem B1617389 : Blo 1344991 1617389 := bbase (se 3 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 1617389 = 606521) (by norm_num)
theorem B4369909 : Blo 1344991 4369909 := bbase (se 5 (by rfl) ⟨204839, by rfl⟩ : syracuseStep 4369909 = 409679) (by norm_num)
theorem B3026429 : Blo 1344991 3026429 := bbase (se 3 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 3026429 = 1134911) (by norm_num)
theorem B2018813 : Blo 1344991 2018813 := bbase (se 3 (by rfl) ⟨378527, by rfl⟩ : syracuseStep 2018813 = 757055) (by norm_num)
theorem B2272765 : Blo 1344991 2272765 := bbase (se 3 (by rfl) ⟨426143, by rfl⟩ : syracuseStep 2272765 = 852287) (by norm_num)
theorem B2018837 : Blo 1344991 2018837 := bbase (se 6 (by rfl) ⟨47316, by rfl⟩ : syracuseStep 2018837 = 94633) (by norm_num)
theorem B2018861 : Blo 1344991 2018861 := bbase (se 3 (by rfl) ⟨378536, by rfl⟩ : syracuseStep 2018861 = 757073) (by norm_num)
theorem B7663157 : Blo 1344991 7663157 := bbase (se 5 (by rfl) ⟨359210, by rfl⟩ : syracuseStep 7663157 = 718421) (by norm_num)
theorem B3026501 : Blo 1344991 3026501 := bbase (se 4 (by rfl) ⟨283734, by rfl⟩ : syracuseStep 3026501 = 567469) (by norm_num)
theorem B2018885 : Blo 1344991 2018885 := bbase (se 4 (by rfl) ⟨189270, by rfl⟩ : syracuseStep 2018885 = 378541) (by norm_num)
theorem B1363537 : Blo 1344991 1363537 := bbase (se 2 (by rfl) ⟨511326, by rfl⟩ : syracuseStep 1363537 = 1022653) (by norm_num)
theorem B1437269 : Blo 1344991 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B2272853 : Blo 1344991 2272853 := bbase (se 8 (by rfl) ⟨13317, by rfl⟩ : syracuseStep 2272853 = 26635) (by norm_num)
theorem B2018909 : Blo 1344991 2018909 := bbase (se 3 (by rfl) ⟨378545, by rfl⟩ : syracuseStep 2018909 = 757091) (by norm_num)
theorem B1535581 : Blo 1344991 1535581 := bbase (se 3 (by rfl) ⟨287921, by rfl⟩ : syracuseStep 1535581 = 575843) (by norm_num)
theorem B2018933 : Blo 1344991 2018933 := bbase (se 5 (by rfl) ⟨94637, by rfl⟩ : syracuseStep 2018933 = 189275) (by norm_num)
theorem B3026573 : Blo 1344991 3026573 := bbase (se 3 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 3026573 = 1134965) (by norm_num)
theorem B2018957 : Blo 1344991 2018957 := bbase (se 3 (by rfl) ⟨378554, by rfl⟩ : syracuseStep 2018957 = 757109) (by norm_num)
theorem B4542101 : Blo 1344991 4542101 := bbase (se 6 (by rfl) ⟨106455, by rfl⟩ : syracuseStep 4542101 = 212911) (by norm_num)
theorem B2018981 : Blo 1344991 2018981 := bbase (se 4 (by rfl) ⟨189279, by rfl⟩ : syracuseStep 2018981 = 378559) (by norm_num)
theorem B4312757 : Blo 1344991 4312757 := bbase (se 5 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 4312757 = 404321) (by norm_num)
theorem B2019005 : Blo 1344991 2019005 := bbase (se 3 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 2019005 = 757127) (by norm_num)
theorem B3026645 : Blo 1344991 3026645 := bbase (se 7 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 3026645 = 70937) (by norm_num)
theorem B2019029 : Blo 1344991 2019029 := bbase (se 7 (by rfl) ⟨23660, by rfl⟩ : syracuseStep 2019029 = 47321) (by norm_num)
theorem B2272981 : Blo 1344991 2272981 := bbase (se 7 (by rfl) ⟨26636, by rfl⟩ : syracuseStep 2272981 = 53273) (by norm_num)
theorem B2019053 : Blo 1344991 2019053 := bbase (se 3 (by rfl) ⟨378572, by rfl⟩ : syracuseStep 2019053 = 757145) (by norm_num)
theorem B2019077 : Blo 1344991 2019077 := bbase (se 4 (by rfl) ⟨189288, by rfl⟩ : syracuseStep 2019077 = 378577) (by norm_num)
theorem B3026717 : Blo 1344991 3026717 := bbase (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) (by norm_num)
theorem B2019101 : Blo 1344991 2019101 := bbase (se 3 (by rfl) ⟨378581, by rfl⟩ : syracuseStep 2019101 = 757163) (by norm_num)
theorem B2019125 : Blo 1344991 2019125 := bbase (se 5 (by rfl) ⟨94646, by rfl⟩ : syracuseStep 2019125 = 189293) (by norm_num)
theorem B4312885 : Blo 1344991 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B2019149 : Blo 1344991 2019149 := bbase (se 3 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 2019149 = 757181) (by norm_num)
theorem B1437517 : Blo 1344991 1437517 := bbase (se 3 (by rfl) ⟨269534, by rfl⟩ : syracuseStep 1437517 = 539069) (by norm_num)
theorem B11497301 : Blo 1344991 11497301 := bbase (se 9 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 11497301 = 67367) (by norm_num)
theorem B3026789 : Blo 1344991 3026789 := bbase (se 4 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 3026789 = 567523) (by norm_num)
theorem B2019173 : Blo 1344991 2019173 := bbase (se 4 (by rfl) ⟨189297, by rfl⟩ : syracuseStep 2019173 = 378595) (by norm_num)
theorem B2019197 : Blo 1344991 2019197 := bbase (se 3 (by rfl) ⟨378599, by rfl⟩ : syracuseStep 2019197 = 757199) (by norm_num)
theorem B2019221 : Blo 1344991 2019221 := bbase (se 6 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 2019221 = 94651) (by norm_num)
theorem B3026861 : Blo 1344991 3026861 := bbase (se 3 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 3026861 = 1135073) (by norm_num)
theorem B2019245 : Blo 1344991 2019245 := bbase (se 3 (by rfl) ⟨378608, by rfl⟩ : syracuseStep 2019245 = 757217) (by norm_num)
theorem B2019269 : Blo 1344991 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B2019293 : Blo 1344991 2019293 := bbase (se 3 (by rfl) ⟨378617, by rfl⟩ : syracuseStep 2019293 = 757235) (by norm_num)
theorem B3067885 : Blo 1344991 3067885 := bbase (se 3 (by rfl) ⟨575228, by rfl⟩ : syracuseStep 3067885 = 1150457) (by norm_num)
theorem B3026933 : Blo 1344991 3026933 := bbase (se 5 (by rfl) ⟨141887, by rfl⟩ : syracuseStep 3026933 = 283775) (by norm_num)
theorem B2019317 : Blo 1344991 2019317 := bbase (se 5 (by rfl) ⟨94655, by rfl⟩ : syracuseStep 2019317 = 189311) (by norm_num)
theorem B2019341 : Blo 1344991 2019341 := bbase (se 3 (by rfl) ⟨378626, by rfl⟩ : syracuseStep 2019341 = 757253) (by norm_num)
theorem B14544917 : Blo 1344991 14544917 := bbase (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) (by norm_num)
theorem B2019365 : Blo 1344991 2019365 := bbase (se 4 (by rfl) ⟨189315, by rfl⟩ : syracuseStep 2019365 = 378631) (by norm_num)
theorem B4313141 : Blo 1344991 4313141 := bbase (se 5 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 4313141 = 404357) (by norm_num)
theorem B3027005 : Blo 1344991 3027005 := bbase (se 3 (by rfl) ⟨567563, by rfl⟩ : syracuseStep 3027005 = 1135127) (by norm_num)
theorem B2019389 : Blo 1344991 2019389 := bbase (se 3 (by rfl) ⟨378635, by rfl⟩ : syracuseStep 2019389 = 757271) (by norm_num)
theorem B4542533 : Blo 1344991 4542533 := bbase (se 4 (by rfl) ⟨425862, by rfl⟩ : syracuseStep 4542533 = 851725) (by norm_num)
theorem B2019413 : Blo 1344991 2019413 := bbase (se 8 (by rfl) ⟨11832, by rfl⟩ : syracuseStep 2019413 = 23665) (by norm_num)
theorem B2019437 : Blo 1344991 2019437 := bbase (se 3 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 2019437 = 757289) (by norm_num)
theorem B3027077 : Blo 1344991 3027077 := bbase (se 4 (by rfl) ⟨283788, by rfl⟩ : syracuseStep 3027077 = 567577) (by norm_num)
theorem B2019461 : Blo 1344991 2019461 := bbase (se 4 (by rfl) ⟨189324, by rfl⟩ : syracuseStep 2019461 = 378649) (by norm_num)
theorem B2019485 : Blo 1344991 2019485 := bbase (se 3 (by rfl) ⟨378653, by rfl⟩ : syracuseStep 2019485 = 757307) (by norm_num)
theorem B1364137 : Blo 1344991 1364137 := bbase (se 2 (by rfl) ⟨511551, by rfl⟩ : syracuseStep 1364137 = 1023103) (by norm_num)
theorem B2019509 : Blo 1344991 2019509 := bbase (se 5 (by rfl) ⟨94664, by rfl⟩ : syracuseStep 2019509 = 189329) (by norm_num)
theorem B2527421 : Blo 1344991 2527421 := bbase (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) (by norm_num)
theorem B3027149 : Blo 1344991 3027149 := bbase (se 3 (by rfl) ⟨567590, by rfl⟩ : syracuseStep 3027149 = 1135181) (by norm_num)
theorem B2019533 : Blo 1344991 2019533 := bbase (se 3 (by rfl) ⟨378662, by rfl⟩ : syracuseStep 2019533 = 757325) (by norm_num)
theorem B2019557 : Blo 1344991 2019557 := bbase (se 4 (by rfl) ⟨189333, by rfl⟩ : syracuseStep 2019557 = 378667) (by norm_num)
theorem B2019581 : Blo 1344991 2019581 := bbase (se 3 (by rfl) ⟨378671, by rfl⟩ : syracuseStep 2019581 = 757343) (by norm_num)
theorem B1437949 : Blo 1344991 1437949 := bbase (se 3 (by rfl) ⟨269615, by rfl⟩ : syracuseStep 1437949 = 539231) (by norm_num)
theorem B3027221 : Blo 1344991 3027221 := bbase (se 6 (by rfl) ⟨70950, by rfl⟩ : syracuseStep 3027221 = 141901) (by norm_num)
theorem B2019605 : Blo 1344991 2019605 := bbase (se 6 (by rfl) ⟨47334, by rfl⟩ : syracuseStep 2019605 = 94669) (by norm_num)
theorem B2019629 : Blo 1344991 2019629 := bbase (se 3 (by rfl) ⟨378680, by rfl⟩ : syracuseStep 2019629 = 757361) (by norm_num)
theorem B2019653 : Blo 1344991 2019653 := bbase (se 4 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 2019653 = 378685) (by norm_num)
theorem B1438021 : Blo 1344991 1438021 := bbase (se 4 (by rfl) ⟨134814, by rfl⟩ : syracuseStep 1438021 = 269629) (by norm_num)
theorem B3027293 : Blo 1344991 3027293 := bbase (se 3 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 3027293 = 1135235) (by norm_num)
theorem B2019677 : Blo 1344991 2019677 := bbase (se 3 (by rfl) ⟨378689, by rfl⟩ : syracuseStep 2019677 = 757379) (by norm_num)
theorem B3887461 : Blo 1344991 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B2019701 : Blo 1344991 2019701 := bbase (se 5 (by rfl) ⟨94673, by rfl⟩ : syracuseStep 2019701 = 189347) (by norm_num)
theorem B2019725 : Blo 1344991 2019725 := bbase (se 3 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 2019725 = 757397) (by norm_num)
theorem B3027365 : Blo 1344991 3027365 := bbase (se 4 (by rfl) ⟨283815, by rfl⟩ : syracuseStep 3027365 = 567631) (by norm_num)
theorem B2019749 : Blo 1344991 2019749 := bbase (se 4 (by rfl) ⟨189351, by rfl⟩ : syracuseStep 2019749 = 378703) (by norm_num)
theorem B4919717 : Blo 1344991 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B2019773 : Blo 1344991 2019773 := bbase (se 3 (by rfl) ⟨378707, by rfl⟩ : syracuseStep 2019773 = 757415) (by norm_num)
theorem B2019797 : Blo 1344991 2019797 := bbase (se 7 (by rfl) ⟨23669, by rfl⟩ : syracuseStep 2019797 = 47339) (by norm_num)
theorem B3027437 : Blo 1344991 3027437 := bbase (se 3 (by rfl) ⟨567644, by rfl⟩ : syracuseStep 3027437 = 1135289) (by norm_num)
theorem B2019821 : Blo 1344991 2019821 := bbase (se 3 (by rfl) ⟨378716, by rfl⟩ : syracuseStep 2019821 = 757433) (by norm_num)
theorem B4542965 : Blo 1344991 4542965 := bbase (se 5 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 4542965 = 425903) (by norm_num)
theorem B3232261 : Blo 1344991 3232261 := bbase (se 4 (by rfl) ⟨303024, by rfl⟩ : syracuseStep 3232261 = 606049) (by norm_num)
theorem B2019845 : Blo 1344991 2019845 := bbase (se 4 (by rfl) ⟨189360, by rfl⟩ : syracuseStep 2019845 = 378721) (by norm_num)
theorem B2019869 : Blo 1344991 2019869 := bbase (se 3 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 2019869 = 757451) (by norm_num)
theorem B3027509 : Blo 1344991 3027509 := bbase (se 5 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 3027509 = 283829) (by norm_num)
theorem B2019893 : Blo 1344991 2019893 := bbase (se 5 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 2019893 = 189365) (by norm_num)
theorem B2019917 : Blo 1344991 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B6812261 : Blo 1344991 6812261 := bbase (se 4 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 6812261 = 1277299) (by norm_num)
theorem B2019941 : Blo 1344991 2019941 := bbase (se 4 (by rfl) ⟨189369, by rfl⟩ : syracuseStep 2019941 = 378739) (by norm_num)
theorem B9695861 : Blo 1344991 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B3027581 : Blo 1344991 3027581 := bbase (se 3 (by rfl) ⟨567671, by rfl⟩ : syracuseStep 3027581 = 1135343) (by norm_num)
theorem B2019965 : Blo 1344991 2019965 := bbase (se 3 (by rfl) ⟨378743, by rfl⟩ : syracuseStep 2019965 = 757487) (by norm_num)
theorem B2019989 : Blo 1344991 2019989 := bbase (se 6 (by rfl) ⟨47343, by rfl⟩ : syracuseStep 2019989 = 94687) (by norm_num)
theorem B2020013 : Blo 1344991 2020013 := bbase (se 3 (by rfl) ⟨378752, by rfl⟩ : syracuseStep 2020013 = 757505) (by norm_num)
theorem B8622773 : Blo 1344991 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B1438393 : Blo 1344991 1438393 := bbase (se 2 (by rfl) ⟨539397, by rfl⟩ : syracuseStep 1438393 = 1078795) (by norm_num)
theorem B3027653 : Blo 1344991 3027653 := bbase (se 4 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 3027653 = 567685) (by norm_num)
theorem B2020037 : Blo 1344991 2020037 := bbase (se 4 (by rfl) ⟨189378, by rfl⟩ : syracuseStep 2020037 = 378757) (by norm_num)
theorem B3830485 : Blo 1344991 3830485 := bbase (se 7 (by rfl) ⟨44888, by rfl⟩ : syracuseStep 3830485 = 89777) (by norm_num)
theorem B7664341 : Blo 1344991 7664341 := bbase (se 7 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 7664341 = 179633) (by norm_num)
theorem B2020061 : Blo 1344991 2020061 := bbase (se 3 (by rfl) ⟨378761, by rfl⟩ : syracuseStep 2020061 = 757523) (by norm_num)
theorem B5108453 : Blo 1344991 5108453 := bbase (se 4 (by rfl) ⟨478917, by rfl⟩ : syracuseStep 5108453 = 957835) (by norm_num)
theorem B3232493 : Blo 1344991 3232493 := bbase (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) (by norm_num)
theorem B2020085 : Blo 1344991 2020085 := bbase (se 5 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 2020085 = 189383) (by norm_num)
theorem B3027725 : Blo 1344991 3027725 := bbase (se 3 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 3027725 = 1135397) (by norm_num)
theorem B2020109 : Blo 1344991 2020109 := bbase (se 3 (by rfl) ⟨378770, by rfl⟩ : syracuseStep 2020109 = 757541) (by norm_num)
theorem B3232541 : Blo 1344991 3232541 := bbase (se 3 (by rfl) ⟨606101, by rfl⟩ : syracuseStep 3232541 = 1212203) (by norm_num)
theorem B2020133 : Blo 1344991 2020133 := bbase (se 4 (by rfl) ⟨189387, by rfl⟩ : syracuseStep 2020133 = 378775) (by norm_num)
theorem B2020157 : Blo 1344991 2020157 := bbase (se 3 (by rfl) ⟨378779, by rfl⟩ : syracuseStep 2020157 = 757559) (by norm_num)
theorem B3027797 : Blo 1344991 3027797 := bbase (se 9 (by rfl) ⟨8870, by rfl⟩ : syracuseStep 3027797 = 17741) (by norm_num)
theorem B2020181 : Blo 1344991 2020181 := bbase (se 9 (by rfl) ⟨5918, by rfl⟩ : syracuseStep 2020181 = 11837) (by norm_num)
theorem B5747557 : Blo 1344991 5747557 := bbase (se 4 (by rfl) ⟨538833, by rfl⟩ : syracuseStep 5747557 = 1077667) (by norm_num)
theorem B2020205 : Blo 1344991 2020205 := bbase (se 3 (by rfl) ⟨378788, by rfl⟩ : syracuseStep 2020205 = 757577) (by norm_num)
theorem B3830645 : Blo 1344991 3830645 := bbase (se 5 (by rfl) ⟨179561, by rfl⟩ : syracuseStep 3830645 = 359123) (by norm_num)
theorem B5747573 : Blo 1344991 5747573 := bbase (se 5 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 5747573 = 538835) (by norm_num)
theorem B2020229 : Blo 1344991 2020229 := bbase (se 4 (by rfl) ⟨189396, by rfl⟩ : syracuseStep 2020229 = 378793) (by norm_num)
theorem B3404693 : Blo 1344991 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B3027869 : Blo 1344991 3027869 := bbase (se 3 (by rfl) ⟨567725, by rfl⟩ : syracuseStep 3027869 = 1135451) (by norm_num)
theorem B2020253 : Blo 1344991 2020253 := bbase (se 3 (by rfl) ⟨378797, by rfl⟩ : syracuseStep 2020253 = 757595) (by norm_num)
theorem B4543397 : Blo 1344991 4543397 := bbase (se 4 (by rfl) ⟨425943, by rfl⟩ : syracuseStep 4543397 = 851887) (by norm_num)
theorem B2020277 : Blo 1344991 2020277 := bbase (se 5 (by rfl) ⟨94700, by rfl⟩ : syracuseStep 2020277 = 189401) (by norm_num)
theorem B2020301 : Blo 1344991 2020301 := bbase (se 3 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 2020301 = 757613) (by norm_num)
theorem B3027941 : Blo 1344991 3027941 := bbase (se 4 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 3027941 = 567739) (by norm_num)
theorem B2020325 : Blo 1344991 2020325 := bbase (se 4 (by rfl) ⟨189405, by rfl⟩ : syracuseStep 2020325 = 378811) (by norm_num)
theorem B9204725 : Blo 1344991 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B2020349 : Blo 1344991 2020349 := bbase (se 3 (by rfl) ⟨378815, by rfl⟩ : syracuseStep 2020349 = 757631) (by norm_num)
theorem B5108741 : Blo 1344991 5108741 := bbase (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) (by norm_num)
theorem B2020373 : Blo 1344991 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B3028013 : Blo 1344991 3028013 := bbase (se 3 (by rfl) ⟨567752, by rfl⟩ : syracuseStep 3028013 = 1135505) (by norm_num)
theorem B2020397 : Blo 1344991 2020397 := bbase (se 3 (by rfl) ⟨378824, by rfl⟩ : syracuseStep 2020397 = 757649) (by norm_num)
theorem B2020421 : Blo 1344991 2020421 := bbase (se 4 (by rfl) ⟨189414, by rfl⟩ : syracuseStep 2020421 = 378829) (by norm_num)
theorem B2020445 : Blo 1344991 2020445 := bbase (se 3 (by rfl) ⟨378833, by rfl⟩ : syracuseStep 2020445 = 757667) (by norm_num)
theorem B3830885 : Blo 1344991 3830885 := bbase (se 4 (by rfl) ⟨359145, by rfl⟩ : syracuseStep 3830885 = 718291) (by norm_num)
theorem B3028085 : Blo 1344991 3028085 := bbase (se 5 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 3028085 = 283883) (by norm_num)
theorem B2020469 : Blo 1344991 2020469 := bbase (se 5 (by rfl) ⟨94709, by rfl⟩ : syracuseStep 2020469 = 189419) (by norm_num)
theorem B3028157 : Blo 1344991 3028157 := bbase (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) (by norm_num)
theorem B3405037 : Blo 1344991 3405037 := bbase (se 3 (by rfl) ⟨638444, by rfl⟩ : syracuseStep 3405037 = 1276889) (by norm_num)
theorem B3028229 : Blo 1344991 3028229 := bbase (se 4 (by rfl) ⟨283896, by rfl⟩ : syracuseStep 3028229 = 567793) (by norm_num)
theorem B1365265 : Blo 1344991 1365265 := bbase (se 2 (by rfl) ⟨511974, by rfl⟩ : syracuseStep 1365265 = 1023949) (by norm_num)
theorem B3831077 : Blo 1344991 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B3028301 : Blo 1344991 3028301 := bbase (se 3 (by rfl) ⟨567806, by rfl⟩ : syracuseStep 3028301 = 1135613) (by norm_num)
theorem B4543829 : Blo 1344991 4543829 := bbase (se 20 (by rfl) ⟨6, by rfl⟩ : syracuseStep 4543829 = 13) (by norm_num)
theorem B3405149 : Blo 1344991 3405149 := bbase (se 3 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 3405149 = 1276931) (by norm_num)
theorem B2872685 : Blo 1344991 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B2872693 : Blo 1344991 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B2332045 : Blo 1344991 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B11654549 : Blo 1344991 11654549 := bbase (se 6 (by rfl) ⟨273153, by rfl⟩ : syracuseStep 11654549 = 546307) (by norm_num)
theorem B3028373 : Blo 1344991 3028373 := bbase (se 6 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 3028373 = 141955) (by norm_num)
theorem B3028445 : Blo 1344991 3028445 := bbase (se 3 (by rfl) ⟨567833, by rfl⟩ : syracuseStep 3028445 = 1135667) (by norm_num)
theorem B3405341 : Blo 1344991 3405341 := bbase (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) (by norm_num)
theorem B3028517 : Blo 1344991 3028517 := bbase (se 4 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 3028517 = 567847) (by norm_num)
theorem B2553437 : Blo 1344991 2553437 := bbase (se 3 (by rfl) ⟨478769, by rfl⟩ : syracuseStep 2553437 = 957539) (by norm_num)
theorem B6141541 : Blo 1344991 6141541 := bbase (se 4 (by rfl) ⟨575769, by rfl⟩ : syracuseStep 6141541 = 1151539) (by norm_num)
theorem B3028589 : Blo 1344991 3028589 := bbase (se 3 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 3028589 = 1135721) (by norm_num)
theorem B1513129 : Blo 1344991 1513129 := bbase (se 2 (by rfl) ⟨567423, by rfl⟩ : syracuseStep 1513129 = 1134847) (by norm_num)
theorem B3028661 : Blo 1344991 3028661 := bbase (se 5 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 3028661 = 283937) (by norm_num)
theorem B1513165 : Blo 1344991 1513165 := bbase (se 3 (by rfl) ⟨283718, by rfl⟩ : syracuseStep 1513165 = 567437) (by norm_num)
theorem B2553581 : Blo 1344991 2553581 := bbase (se 3 (by rfl) ⟨478796, by rfl⟩ : syracuseStep 2553581 = 957593) (by norm_num)
theorem B1750765 : Blo 1344991 1750765 := bbase (se 3 (by rfl) ⟨328268, by rfl⟩ : syracuseStep 1750765 = 656537) (by norm_num)
theorem B1513201 : Blo 1344991 1513201 := bbase (se 2 (by rfl) ⟨567450, by rfl⟩ : syracuseStep 1513201 = 1134901) (by norm_num)
theorem B3028733 : Blo 1344991 3028733 := bbase (se 3 (by rfl) ⟨567887, by rfl⟩ : syracuseStep 3028733 = 1135775) (by norm_num)
theorem B4544261 : Blo 1344991 4544261 := bbase (se 4 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 4544261 = 852049) (by norm_num)
theorem B1513237 : Blo 1344991 1513237 := bbase (se 6 (by rfl) ⟨35466, by rfl⟩ : syracuseStep 1513237 = 70933) (by norm_num)
theorem B1750825 : Blo 1344991 1750825 := bbase (se 2 (by rfl) ⟨656559, by rfl⟩ : syracuseStep 1750825 = 1313119) (by norm_num)
theorem B1513273 : Blo 1344991 1513273 := bbase (se 2 (by rfl) ⟨567477, by rfl⟩ : syracuseStep 1513273 = 1134955) (by norm_num)
theorem B3028805 : Blo 1344991 3028805 := bbase (se 4 (by rfl) ⟨283950, by rfl⟩ : syracuseStep 3028805 = 567901) (by norm_num)
theorem B1513309 : Blo 1344991 1513309 := bbase (se 3 (by rfl) ⟨283745, by rfl⟩ : syracuseStep 1513309 = 567491) (by norm_num)
theorem B3405685 : Blo 1344991 3405685 := bbase (se 5 (by rfl) ⟨159641, by rfl⟩ : syracuseStep 3405685 = 319283) (by norm_num)
theorem B6813557 : Blo 1344991 6813557 := bbase (se 5 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 6813557 = 638771) (by norm_num)
theorem B1513345 : Blo 1344991 1513345 := bbase (se 2 (by rfl) ⟨567504, by rfl⟩ : syracuseStep 1513345 = 1135009) (by norm_num)
theorem B3028877 : Blo 1344991 3028877 := bbase (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) (by norm_num)
theorem B12285845 : Blo 1344991 12285845 := bbase (se 6 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 12285845 = 575899) (by norm_num)
theorem B4151189 : Blo 1344991 4151189 := bbase (se 6 (by rfl) ⟨97293, by rfl⟩ : syracuseStep 4151189 = 194587) (by norm_num)
theorem B1513381 : Blo 1344991 1513381 := bbase (se 4 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 1513381 = 283759) (by norm_num)
theorem B6469541 : Blo 1344991 6469541 := bbase (se 4 (by rfl) ⟨606519, by rfl⟩ : syracuseStep 6469541 = 1213039) (by norm_num)
theorem B1513417 : Blo 1344991 1513417 := bbase (se 2 (by rfl) ⟨567531, by rfl⟩ : syracuseStep 1513417 = 1135063) (by norm_num)
theorem B3028949 : Blo 1344991 3028949 := bbase (se 7 (by rfl) ⟨35495, by rfl⟩ : syracuseStep 3028949 = 70991) (by norm_num)
theorem B3405797 : Blo 1344991 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B5183461 : Blo 1344991 5183461 := bbase (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) (by norm_num)
theorem B1513453 : Blo 1344991 1513453 := bbase (se 3 (by rfl) ⟨283772, by rfl⟩ : syracuseStep 1513453 = 567545) (by norm_num)
theorem B2553869 : Blo 1344991 2553869 := bbase (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) (by norm_num)
theorem B1513489 : Blo 1344991 1513489 := bbase (se 2 (by rfl) ⟨567558, by rfl⟩ : syracuseStep 1513489 = 1135117) (by norm_num)
theorem B3029021 : Blo 1344991 3029021 := bbase (se 3 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 3029021 = 1135883) (by norm_num)
theorem B1513525 : Blo 1344991 1513525 := bbase (se 5 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 1513525 = 141893) (by norm_num)
theorem B3323965 : Blo 1344991 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B1513561 : Blo 1344991 1513561 := bbase (se 2 (by rfl) ⟨567585, by rfl⟩ : syracuseStep 1513561 = 1135171) (by norm_num)
theorem B3029093 : Blo 1344991 3029093 := bbase (se 4 (by rfl) ⟨283977, by rfl⟩ : syracuseStep 3029093 = 567955) (by norm_num)
theorem B1513597 : Blo 1344991 1513597 := bbase (se 3 (by rfl) ⟨283799, by rfl⟩ : syracuseStep 1513597 = 567599) (by norm_num)
theorem B3233933 : Blo 1344991 3233933 := bbase (se 3 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 3233933 = 1212725) (by norm_num)
theorem B1513633 : Blo 1344991 1513633 := bbase (se 2 (by rfl) ⟨567612, by rfl⟩ : syracuseStep 1513633 = 1135225) (by norm_num)
theorem B2554021 : Blo 1344991 2554021 := bbase (se 4 (by rfl) ⟨239439, by rfl⟩ : syracuseStep 2554021 = 478879) (by norm_num)
theorem B3405989 : Blo 1344991 3405989 := bbase (se 4 (by rfl) ⟨319311, by rfl⟩ : syracuseStep 3405989 = 638623) (by norm_num)
theorem B5109925 : Blo 1344991 5109925 := bbase (se 4 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 5109925 = 958111) (by norm_num)
theorem B3029165 : Blo 1344991 3029165 := bbase (se 3 (by rfl) ⟨567968, by rfl⟩ : syracuseStep 3029165 = 1135937) (by norm_num)
theorem B9828533 : Blo 1344991 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B4544693 : Blo 1344991 4544693 := bbase (se 5 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 4544693 = 426065) (by norm_num)
theorem B1513669 : Blo 1344991 1513669 := bbase (se 4 (by rfl) ⟨141906, by rfl⟩ : syracuseStep 1513669 = 283813) (by norm_num)
theorem B9214165 : Blo 1344991 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B1513705 : Blo 1344991 1513705 := bbase (se 2 (by rfl) ⟨567639, by rfl⟩ : syracuseStep 1513705 = 1135279) (by norm_num)
theorem B3029237 : Blo 1344991 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B3832069 : Blo 1344991 3832069 := bbase (se 4 (by rfl) ⟨359256, by rfl⟩ : syracuseStep 3832069 = 718513) (by norm_num)
theorem B1513741 : Blo 1344991 1513741 := bbase (se 3 (by rfl) ⟨283826, by rfl⟩ : syracuseStep 1513741 = 567653) (by norm_num)
theorem B1513777 : Blo 1344991 1513777 := bbase (se 2 (by rfl) ⟨567666, by rfl⟩ : syracuseStep 1513777 = 1135333) (by norm_num)
theorem B3029309 : Blo 1344991 3029309 := bbase (se 3 (by rfl) ⟨567995, by rfl⟩ : syracuseStep 3029309 = 1135991) (by norm_num)
theorem B3234125 : Blo 1344991 3234125 := bbase (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) (by norm_num)
theorem B1513813 : Blo 1344991 1513813 := bbase (se 10 (by rfl) ⟨2217, by rfl⟩ : syracuseStep 1513813 = 4435) (by norm_num)
theorem B1513849 : Blo 1344991 1513849 := bbase (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) (by norm_num)
theorem B3029381 : Blo 1344991 3029381 := bbase (se 4 (by rfl) ⟨284004, by rfl⟩ : syracuseStep 3029381 = 568009) (by norm_num)
theorem B1513885 : Blo 1344991 1513885 := bbase (se 3 (by rfl) ⟨283853, by rfl⟩ : syracuseStep 1513885 = 567707) (by norm_num)
theorem B1513921 : Blo 1344991 1513921 := bbase (se 2 (by rfl) ⟨567720, by rfl⟩ : syracuseStep 1513921 = 1135441) (by norm_num)
theorem B3029453 : Blo 1344991 3029453 := bbase (se 3 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 3029453 = 1136045) (by norm_num)
theorem B2554325 : Blo 1344991 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B5110229 : Blo 1344991 5110229 := bbase (se 7 (by rfl) ⟨59885, by rfl⟩ : syracuseStep 5110229 = 119771) (by norm_num)
theorem B10222037 : Blo 1344991 10222037 := bbase (se 7 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 10222037 = 239579) (by norm_num)
theorem B2873821 : Blo 1344991 2873821 := bbase (se 3 (by rfl) ⟨538841, by rfl⟩ : syracuseStep 2873821 = 1077683) (by norm_num)
theorem B1513957 : Blo 1344991 1513957 := bbase (se 4 (by rfl) ⟨141933, by rfl⟩ : syracuseStep 1513957 = 283867) (by norm_num)
theorem B6224357 : Blo 1344991 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B1702397 : Blo 1344991 1702397 := bbase (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) (by norm_num)
theorem B3406333 : Blo 1344991 3406333 := bbase (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) (by norm_num)
theorem B1513993 : Blo 1344991 1513993 := bbase (se 2 (by rfl) ⟨567747, by rfl⟩ : syracuseStep 1513993 = 1135495) (by norm_num)
theorem B3029525 : Blo 1344991 3029525 := bbase (se 6 (by rfl) ⟨71004, by rfl⟩ : syracuseStep 3029525 = 142009) (by norm_num)
theorem B7281173 : Blo 1344991 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B1514029 : Blo 1344991 1514029 := bbase (se 3 (by rfl) ⟨283880, by rfl⟩ : syracuseStep 1514029 = 567761) (by norm_num)
theorem B1702453 : Blo 1344991 1702453 := bbase (se 5 (by rfl) ⟨79802, by rfl⟩ : syracuseStep 1702453 = 159605) (by norm_num)
theorem B1514065 : Blo 1344991 1514065 := bbase (se 2 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 1514065 = 1135549) (by norm_num)
theorem B9697877 : Blo 1344991 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B3029597 : Blo 1344991 3029597 := bbase (se 3 (by rfl) ⟨568049, by rfl⟩ : syracuseStep 3029597 = 1136099) (by norm_num)
theorem B1915493 : Blo 1344991 1915493 := bbase (se 4 (by rfl) ⟨179577, by rfl⟩ : syracuseStep 1915493 = 359155) (by norm_num)
theorem B4545125 : Blo 1344991 4545125 := bbase (se 4 (by rfl) ⟨426105, by rfl⟩ : syracuseStep 4545125 = 852211) (by norm_num)
theorem B3406445 : Blo 1344991 3406445 := bbase (se 3 (by rfl) ⟨638708, by rfl⟩ : syracuseStep 3406445 = 1277417) (by norm_num)
theorem B1514101 : Blo 1344991 1514101 := bbase (se 5 (by rfl) ⟨70973, by rfl⟩ : syracuseStep 1514101 = 141947) (by norm_num)
theorem B1702549 : Blo 1344991 1702549 := bbase (se 6 (by rfl) ⟨39903, by rfl⟩ : syracuseStep 1702549 = 79807) (by norm_num)
theorem B7666325 : Blo 1344991 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B1514137 : Blo 1344991 1514137 := bbase (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) (by norm_num)
theorem B3029669 : Blo 1344991 3029669 := bbase (se 4 (by rfl) ⟨284031, by rfl⟩ : syracuseStep 3029669 = 568063) (by norm_num)
theorem B1514173 : Blo 1344991 1514173 := bbase (se 3 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 1514173 = 567815) (by norm_num)
theorem B1514209 : Blo 1344991 1514209 := bbase (se 2 (by rfl) ⟨567828, by rfl⟩ : syracuseStep 1514209 = 1135657) (by norm_num)
theorem B3029741 : Blo 1344991 3029741 := bbase (se 3 (by rfl) ⟨568076, by rfl⟩ : syracuseStep 3029741 = 1136153) (by norm_num)
theorem B1514245 : Blo 1344991 1514245 := bbase (se 4 (by rfl) ⟨141960, by rfl⟩ : syracuseStep 1514245 = 283921) (by norm_num)
theorem B1514281 : Blo 1344991 1514281 := bbase (se 2 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 1514281 = 1135711) (by norm_num)
theorem B3406637 : Blo 1344991 3406637 := bbase (se 3 (by rfl) ⟨638744, by rfl⟩ : syracuseStep 3406637 = 1277489) (by norm_num)
theorem B3029813 : Blo 1344991 3029813 := bbase (se 5 (by rfl) ⟨142022, by rfl⟩ : syracuseStep 3029813 = 284045) (by norm_num)
theorem B1702721 : Blo 1344991 1702721 := bbase (se 2 (by rfl) ⟨638520, by rfl⟩ : syracuseStep 1702721 = 1277041) (by norm_num)
theorem B1514317 : Blo 1344991 1514317 := bbase (se 3 (by rfl) ⟨283934, by rfl⟩ : syracuseStep 1514317 = 567869) (by norm_num)
theorem B2874197 : Blo 1344991 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B1514353 : Blo 1344991 1514353 := bbase (se 2 (by rfl) ⟨567882, by rfl⟩ : syracuseStep 1514353 = 1135765) (by norm_num)
theorem B10214261 : Blo 1344991 10214261 := bbase (se 5 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 10214261 = 957587) (by norm_num)
theorem B1702777 : Blo 1344991 1702777 := bbase (se 2 (by rfl) ⟨638541, by rfl⟩ : syracuseStep 1702777 = 1277083) (by norm_num)
theorem B3029885 : Blo 1344991 3029885 := bbase (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) (by norm_num)
theorem B1514389 : Blo 1344991 1514389 := bbase (se 6 (by rfl) ⟨35493, by rfl⟩ : syracuseStep 1514389 = 70987) (by norm_num)
theorem B3455909 : Blo 1344991 3455909 := bbase (se 4 (by rfl) ⟨323991, by rfl⟩ : syracuseStep 3455909 = 647983) (by norm_num)
theorem B1514425 : Blo 1344991 1514425 := bbase (se 2 (by rfl) ⟨567909, by rfl⟩ : syracuseStep 1514425 = 1135819) (by norm_num)
theorem B2423749 : Blo 1344991 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B3029957 : Blo 1344991 3029957 := bbase (se 4 (by rfl) ⟨284058, by rfl⟩ : syracuseStep 3029957 = 568117) (by norm_num)
theorem B1702873 : Blo 1344991 1702873 := bbase (se 2 (by rfl) ⟨638577, by rfl⟩ : syracuseStep 1702873 = 1277155) (by norm_num)
theorem B1514461 : Blo 1344991 1514461 := bbase (se 3 (by rfl) ⟨283961, by rfl⟩ : syracuseStep 1514461 = 567923) (by norm_num)
theorem B2046973 : Blo 1344991 2046973 := bbase (se 3 (by rfl) ⟨383807, by rfl⟩ : syracuseStep 2046973 = 767615) (by norm_num)
theorem B1514497 : Blo 1344991 1514497 := bbase (se 2 (by rfl) ⟨567936, by rfl⟩ : syracuseStep 1514497 = 1135873) (by norm_num)
theorem B3030029 : Blo 1344991 3030029 := bbase (se 3 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 3030029 = 1136261) (by norm_num)
theorem B4545557 : Blo 1344991 4545557 := bbase (se 6 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 4545557 = 213073) (by norm_num)
theorem B1514533 : Blo 1344991 1514533 := bbase (se 4 (by rfl) ⟨141987, by rfl⟩ : syracuseStep 1514533 = 283975) (by norm_num)
theorem B5749829 : Blo 1344991 5749829 := bbase (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) (by norm_num)
theorem B1514569 : Blo 1344991 1514569 := bbase (se 2 (by rfl) ⟨567963, by rfl⟩ : syracuseStep 1514569 = 1135927) (by norm_num)
theorem B3030101 : Blo 1344991 3030101 := bbase (se 8 (by rfl) ⟨17754, by rfl⟩ : syracuseStep 3030101 = 35509) (by norm_num)
theorem B1514605 : Blo 1344991 1514605 := bbase (se 3 (by rfl) ⟨283988, by rfl⟩ : syracuseStep 1514605 = 567977) (by norm_num)
theorem B3939445 : Blo 1344991 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B1703045 : Blo 1344991 1703045 := bbase (se 4 (by rfl) ⟨159660, by rfl⟩ : syracuseStep 1703045 = 319321) (by norm_num)
theorem B3406981 : Blo 1344991 3406981 := bbase (se 4 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 3406981 = 638809) (by norm_num)
theorem B6814853 : Blo 1344991 6814853 := bbase (se 4 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 6814853 = 1277785) (by norm_num)
theorem B1514641 : Blo 1344991 1514641 := bbase (se 2 (by rfl) ⟨567990, by rfl⟩ : syracuseStep 1514641 = 1135981) (by norm_num)
theorem B3030173 : Blo 1344991 3030173 := bbase (se 3 (by rfl) ⟨568157, by rfl⟩ : syracuseStep 3030173 = 1136315) (by norm_num)
theorem B1514677 : Blo 1344991 1514677 := bbase (se 5 (by rfl) ⟨71000, by rfl⟩ : syracuseStep 1514677 = 142001) (by norm_num)
theorem B1703101 : Blo 1344991 1703101 := bbase (se 3 (by rfl) ⟨319331, by rfl⟩ : syracuseStep 1703101 = 638663) (by norm_num)
theorem B2555077 : Blo 1344991 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B2301133 : Blo 1344991 2301133 := bbase (se 3 (by rfl) ⟨431462, by rfl⟩ : syracuseStep 2301133 = 862925) (by norm_num)
theorem B1514713 : Blo 1344991 1514713 := bbase (se 2 (by rfl) ⟨568017, by rfl⟩ : syracuseStep 1514713 = 1136035) (by norm_num)
theorem B3030245 : Blo 1344991 3030245 := bbase (se 4 (by rfl) ⟨284085, by rfl⟩ : syracuseStep 3030245 = 568171) (by norm_num)
theorem B3407093 : Blo 1344991 3407093 := bbase (se 5 (by rfl) ⟨159707, by rfl⟩ : syracuseStep 3407093 = 319415) (by norm_num)
theorem B1514749 : Blo 1344991 1514749 := bbase (se 3 (by rfl) ⟨284015, by rfl⟩ : syracuseStep 1514749 = 568031) (by norm_num)
theorem B1703197 : Blo 1344991 1703197 := bbase (se 3 (by rfl) ⟨319349, by rfl⟩ : syracuseStep 1703197 = 638699) (by norm_num)
theorem B1514785 : Blo 1344991 1514785 := bbase (se 2 (by rfl) ⟨568044, by rfl⟩ : syracuseStep 1514785 = 1136089) (by norm_num)
theorem B3030317 : Blo 1344991 3030317 := bbase (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) (by norm_num)
theorem B1514821 : Blo 1344991 1514821 := bbase (se 4 (by rfl) ⟨142014, by rfl⟩ : syracuseStep 1514821 = 284029) (by norm_num)
theorem B1916245 : Blo 1344991 1916245 := bbase (se 11 (by rfl) ⟨1403, by rfl⟩ : syracuseStep 1916245 = 2807) (by norm_num)
theorem B2555221 : Blo 1344991 2555221 := bbase (se 11 (by rfl) ⟨1871, by rfl⟩ : syracuseStep 2555221 = 3743) (by norm_num)
theorem B3833173 : Blo 1344991 3833173 := bbase (se 11 (by rfl) ⟨2807, by rfl⟩ : syracuseStep 3833173 = 5615) (by norm_num)
theorem B1514857 : Blo 1344991 1514857 := bbase (se 2 (by rfl) ⟨568071, by rfl⟩ : syracuseStep 1514857 = 1136143) (by norm_num)
theorem B3030389 : Blo 1344991 3030389 := bbase (se 5 (by rfl) ⟨142049, by rfl⟩ : syracuseStep 3030389 = 284099) (by norm_num)
theorem B1514893 : Blo 1344991 1514893 := bbase (se 3 (by rfl) ⟨284042, by rfl⟩ : syracuseStep 1514893 = 568085) (by norm_num)
theorem B10911125 : Blo 1344991 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B1514929 : Blo 1344991 1514929 := bbase (se 2 (by rfl) ⟨568098, by rfl⟩ : syracuseStep 1514929 = 1136197) (by norm_num)
theorem B3407285 : Blo 1344991 3407285 := bbase (se 5 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 3407285 = 319433) (by norm_num)
theorem B3030461 : Blo 1344991 3030461 := bbase (se 3 (by rfl) ⟨568211, by rfl⟩ : syracuseStep 3030461 = 1136423) (by norm_num)
theorem B4545989 : Blo 1344991 4545989 := bbase (se 4 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 4545989 = 852373) (by norm_num)
theorem B1703369 : Blo 1344991 1703369 := bbase (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) (by norm_num)
theorem B1514965 : Blo 1344991 1514965 := bbase (se 7 (by rfl) ⟨17753, by rfl⟩ : syracuseStep 1514965 = 35507) (by norm_num)
theorem B2555381 : Blo 1344991 2555381 := bbase (se 5 (by rfl) ⟨119783, by rfl⟩ : syracuseStep 2555381 = 239567) (by norm_num)
theorem B1515001 : Blo 1344991 1515001 := bbase (se 2 (by rfl) ⟨568125, by rfl⟩ : syracuseStep 1515001 = 1136251) (by norm_num)
theorem B1703425 : Blo 1344991 1703425 := bbase (se 2 (by rfl) ⟨638784, by rfl⟩ : syracuseStep 1703425 = 1277569) (by norm_num)
theorem B3030533 : Blo 1344991 3030533 := bbase (se 4 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 3030533 = 568225) (by norm_num)
theorem B1842701 : Blo 1344991 1842701 := bbase (se 3 (by rfl) ⟨345506, by rfl⟩ : syracuseStep 1842701 = 691013) (by norm_num)
theorem B1515037 : Blo 1344991 1515037 := bbase (se 3 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 1515037 = 568139) (by norm_num)
theorem B1515073 : Blo 1344991 1515073 := bbase (se 2 (by rfl) ⟨568152, by rfl⟩ : syracuseStep 1515073 = 1136305) (by norm_num)
theorem B3030605 : Blo 1344991 3030605 := bbase (se 3 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 3030605 = 1136477) (by norm_num)
theorem B1703521 : Blo 1344991 1703521 := bbase (se 2 (by rfl) ⟨638820, by rfl⟩ : syracuseStep 1703521 = 1277641) (by norm_num)
theorem B1515109 : Blo 1344991 1515109 := bbase (se 4 (by rfl) ⟨142041, by rfl⟩ : syracuseStep 1515109 = 284083) (by norm_num)
theorem B2555525 : Blo 1344991 2555525 := bbase (se 4 (by rfl) ⟨239580, by rfl⟩ : syracuseStep 2555525 = 479161) (by norm_num)
theorem B1515145 : Blo 1344991 1515145 := bbase (se 2 (by rfl) ⟨568179, by rfl⟩ : syracuseStep 1515145 = 1136359) (by norm_num)
theorem B13115029 : Blo 1344991 13115029 := bbase (se 6 (by rfl) ⟨307383, by rfl⟩ : syracuseStep 13115029 = 614767) (by norm_num)
theorem B3030677 : Blo 1344991 3030677 := bbase (se 6 (by rfl) ⟨71031, by rfl⟩ : syracuseStep 3030677 = 142063) (by norm_num)
theorem B3071645 : Blo 1344991 3071645 := bbase (se 3 (by rfl) ⟨575933, by rfl⟩ : syracuseStep 3071645 = 1151867) (by norm_num)
theorem B1515181 : Blo 1344991 1515181 := bbase (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) (by norm_num)
theorem B1515217 : Blo 1344991 1515217 := bbase (se 2 (by rfl) ⟨568206, by rfl⟩ : syracuseStep 1515217 = 1136413) (by norm_num)
theorem B1515253 : Blo 1344991 1515253 := bbase (se 5 (by rfl) ⟨71027, by rfl⟩ : syracuseStep 1515253 = 142055) (by norm_num)
theorem B1703693 : Blo 1344991 1703693 := bbase (se 3 (by rfl) ⟨319442, by rfl⟩ : syracuseStep 1703693 = 638885) (by norm_num)
theorem B3407629 : Blo 1344991 3407629 := bbase (se 3 (by rfl) ⟨638930, by rfl⟩ : syracuseStep 3407629 = 1277861) (by norm_num)
theorem B6463253 : Blo 1344991 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1515289 : Blo 1344991 1515289 := bbase (se 2 (by rfl) ⟨568233, by rfl⟩ : syracuseStep 1515289 = 1136467) (by norm_num)
theorem B8625973 : Blo 1344991 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B1515325 : Blo 1344991 1515325 := bbase (se 3 (by rfl) ⟨284123, by rfl⟩ : syracuseStep 1515325 = 568247) (by norm_num)
theorem B1703749 : Blo 1344991 1703749 := bbase (se 4 (by rfl) ⟨159726, by rfl⟩ : syracuseStep 1703749 = 319453) (by norm_num)
theorem B1515361 : Blo 1344991 1515361 := bbase (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) (by norm_num)
theorem B3407741 : Blo 1344991 3407741 := bbase (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) (by norm_num)
theorem B1703845 : Blo 1344991 1703845 := bbase (se 4 (by rfl) ⟨159735, by rfl⟩ : syracuseStep 1703845 = 319471) (by norm_num)
theorem B2555813 : Blo 1344991 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B2875427 : Blo 1344991 2875427 := bstep (se 1 (by rfl) ⟨2156570, by rfl⟩ : syracuseStep 2875427 = 4313141) B4313141
theorem B19660853 : Blo 1344991 19660853 := bstep (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) B1843205
theorem B3407953 : Blo 1344991 3407953 := bstep (se 2 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 3407953 = 2555965) B2555965
theorem B4431953 : Blo 1344991 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B2556049 : Blo 1344991 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B1704179 : Blo 1344991 1704179 := bstep (se 1 (by rfl) ⟨1278134, by rfl⟩ : syracuseStep 1704179 = 2556269) B2556269
theorem B1917265 : Blo 1344991 1917265 := bstep (se 2 (by rfl) ⟨718974, by rfl⟩ : syracuseStep 1917265 = 1437949) B1437949
theorem B3408227 : Blo 1344991 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B6463907 : Blo 1344991 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B1917361 : Blo 1344991 1917361 := bstep (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) B1438021
theorem B2154995 : Blo 1344991 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B2155027 : Blo 1344991 2155027 := bstep (se 1 (by rfl) ⟨1616270, by rfl⟩ : syracuseStep 2155027 = 3232541) B3232541
theorem B5112355 : Blo 1344991 5112355 := bstep (se 1 (by rfl) ⟨3834266, by rfl⟩ : syracuseStep 5112355 = 7668533) B7668533
theorem B3408419 : Blo 1344991 3408419 := bstep (se 1 (by rfl) ⟨2556314, by rfl⟩ : syracuseStep 3408419 = 5112629) B5112629
theorem B2556451 : Blo 1344991 2556451 := bstep (se 1 (by rfl) ⟨1917338, by rfl⟩ : syracuseStep 2556451 = 3834677) B3834677
theorem B3834449 : Blo 1344991 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B2556497 : Blo 1344991 2556497 := bstep (se 2 (by rfl) ⟨958686, by rfl⟩ : syracuseStep 2556497 = 1917373) B1917373
theorem B2269795 : Blo 1344991 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B6136483 : Blo 1344991 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B2425507 : Blo 1344991 2425507 := bstep (se 1 (by rfl) ⟨1819130, by rfl⟩ : syracuseStep 2425507 = 3638261) B3638261
theorem B4309681 : Blo 1344991 4309681 := bstep (se 2 (by rfl) ⟨1616130, by rfl⟩ : syracuseStep 4309681 = 3232261) B3232261
theorem B2269937 : Blo 1344991 2269937 := bstep (se 2 (by rfl) ⟨851226, by rfl⟩ : syracuseStep 2269937 = 1702453) B1702453
theorem B10216205 : Blo 1344991 10216205 := bstep (se 3 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 10216205 = 3831077) B3831077
theorem B2270065 : Blo 1344991 2270065 := bstep (se 2 (by rfl) ⟨851274, by rfl⟩ : syracuseStep 2270065 = 1702549) B1702549
theorem B2556785 : Blo 1344991 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B1639283 : Blo 1344991 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B2270099 : Blo 1344991 2270099 := bstep (se 1 (by rfl) ⟨1702574, by rfl⟩ : syracuseStep 2270099 = 3405149) B3405149
theorem B1917857 : Blo 1344991 1917857 := bstep (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) B1438393
theorem B7660493 : Blo 1344991 7660493 := bstep (se 3 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 7660493 = 2872685) B2872685
theorem B2876401 : Blo 1344991 2876401 := bstep (se 2 (by rfl) ⟨1078650, by rfl⟩ : syracuseStep 2876401 = 2157301) B2157301
theorem B2270227 : Blo 1344991 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B3638371 : Blo 1344991 3638371 := bstep (se 1 (by rfl) ⟨2728778, by rfl⟩ : syracuseStep 3638371 = 5457557) B5457557
theorem B2270369 : Blo 1344991 2270369 := bstep (se 2 (by rfl) ⟨851388, by rfl⟩ : syracuseStep 2270369 = 1702777) B1702777
theorem B2270497 : Blo 1344991 2270497 := bstep (se 2 (by rfl) ⟨851436, by rfl⟩ : syracuseStep 2270497 = 1702873) B1702873
theorem B2270531 : Blo 1344991 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B4539725 : Blo 1344991 4539725 := bstep (se 3 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 4539725 = 1702397) B1702397
theorem B2729297 : Blo 1344991 2729297 := bstep (se 2 (by rfl) ⟨1023486, by rfl⟩ : syracuseStep 2729297 = 2046973) B2046973
theorem B2164067 : Blo 1344991 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B4539779 : Blo 1344991 4539779 := bstep (se 1 (by rfl) ⟨3404834, by rfl⟩ : syracuseStep 4539779 = 6809669) B6809669
theorem B5752205 : Blo 1344991 5752205 := bstep (se 3 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 5752205 = 2157077) B2157077
theorem B2155955 : Blo 1344991 2155955 := bstep (se 1 (by rfl) ⟨1616966, by rfl⟩ : syracuseStep 2155955 = 3233933) B3233933
theorem B2270659 : Blo 1344991 2270659 := bstep (se 1 (by rfl) ⟨1702994, by rfl⟩ : syracuseStep 2270659 = 3405989) B3405989
theorem B3409361 : Blo 1344991 3409361 := bstep (se 2 (by rfl) ⟨1278510, by rfl⟩ : syracuseStep 3409361 = 2557021) B2557021
theorem B1344995 : Blo 1344991 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B1345011 : Blo 1344991 1345011 := bstep (se 1 (by rfl) ⟨1008758, by rfl⟩ : syracuseStep 1345011 = 2017517) B2017517
theorem B2156033 : Blo 1344991 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B1345027 : Blo 1344991 1345027 := bstep (se 1 (by rfl) ⟨1008770, by rfl⟩ : syracuseStep 1345027 = 2017541) B2017541
theorem B3409411 : Blo 1344991 3409411 := bstep (se 1 (by rfl) ⟨2557058, by rfl⟩ : syracuseStep 3409411 = 5114117) B5114117
theorem B1345043 : Blo 1344991 1345043 := bstep (se 1 (by rfl) ⟨1008782, by rfl⟩ : syracuseStep 1345043 = 2017565) B2017565
theorem B1345059 : Blo 1344991 1345059 := bstep (se 1 (by rfl) ⟨1008794, by rfl⟩ : syracuseStep 1345059 = 2017589) B2017589
theorem B1345075 : Blo 1344991 1345075 := bstep (se 1 (by rfl) ⟨1008806, by rfl⟩ : syracuseStep 1345075 = 2017613) B2017613
theorem B1345091 : Blo 1344991 1345091 := bstep (se 1 (by rfl) ⟨1008818, by rfl⟩ : syracuseStep 1345091 = 2017637) B2017637
theorem B2270801 : Blo 1344991 2270801 := bstep (se 2 (by rfl) ⟨851550, by rfl⟩ : syracuseStep 2270801 = 1703101) B1703101
theorem B1345107 : Blo 1344991 1345107 := bstep (se 1 (by rfl) ⟨1008830, by rfl⟩ : syracuseStep 1345107 = 2017661) B2017661
theorem B1345123 : Blo 1344991 1345123 := bstep (se 1 (by rfl) ⟨1008842, by rfl⟩ : syracuseStep 1345123 = 2017685) B2017685
theorem B1345139 : Blo 1344991 1345139 := bstep (se 1 (by rfl) ⟨1008854, by rfl⟩ : syracuseStep 1345139 = 2017709) B2017709
theorem B1345155 : Blo 1344991 1345155 := bstep (se 1 (by rfl) ⟨1008866, by rfl⟩ : syracuseStep 1345155 = 2017733) B2017733
theorem B4540049 : Blo 1344991 4540049 := bstep (se 2 (by rfl) ⟨1702518, by rfl⟩ : syracuseStep 4540049 = 3405037) B3405037
theorem B3409553 : Blo 1344991 3409553 := bstep (se 2 (by rfl) ⟨1278582, by rfl⟩ : syracuseStep 3409553 = 2557165) B2557165
theorem B1345171 : Blo 1344991 1345171 := bstep (se 1 (by rfl) ⟨1008878, by rfl⟩ : syracuseStep 1345171 = 2017757) B2017757
theorem B1345187 : Blo 1344991 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1345203 : Blo 1344991 1345203 := bstep (se 1 (by rfl) ⟨1008902, by rfl⟩ : syracuseStep 1345203 = 2017805) B2017805
theorem B1345219 : Blo 1344991 1345219 := bstep (se 1 (by rfl) ⟨1008914, by rfl⟩ : syracuseStep 1345219 = 2017829) B2017829
theorem B2270929 : Blo 1344991 2270929 := bstep (se 2 (by rfl) ⟨851598, by rfl⟩ : syracuseStep 2270929 = 1703197) B1703197
theorem B1345235 : Blo 1344991 1345235 := bstep (se 1 (by rfl) ⟨1008926, by rfl⟩ : syracuseStep 1345235 = 2017853) B2017853
theorem B2156257 : Blo 1344991 2156257 := bstep (se 2 (by rfl) ⟨808596, by rfl⟩ : syracuseStep 2156257 = 1617193) B1617193
theorem B1345251 : Blo 1344991 1345251 := bstep (se 1 (by rfl) ⟨1008938, by rfl⟩ : syracuseStep 1345251 = 2017877) B2017877
theorem B6465251 : Blo 1344991 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B1345267 : Blo 1344991 1345267 := bstep (se 1 (by rfl) ⟨1008950, by rfl⟩ : syracuseStep 1345267 = 2017901) B2017901
theorem B2270963 : Blo 1344991 2270963 := bstep (se 1 (by rfl) ⟨1703222, by rfl⟩ : syracuseStep 2270963 = 3406445) B3406445
theorem B1345283 : Blo 1344991 1345283 := bstep (se 1 (by rfl) ⟨1008962, by rfl⟩ : syracuseStep 1345283 = 2017925) B2017925
theorem B1345299 : Blo 1344991 1345299 := bstep (se 1 (by rfl) ⟨1008974, by rfl⟩ : syracuseStep 1345299 = 2017949) B2017949
theorem B1345315 : Blo 1344991 1345315 := bstep (se 1 (by rfl) ⟨1008986, by rfl⟩ : syracuseStep 1345315 = 2017973) B2017973
theorem B1345331 : Blo 1344991 1345331 := bstep (se 1 (by rfl) ⟨1008998, by rfl⟩ : syracuseStep 1345331 = 2017997) B2017997
theorem B1345347 : Blo 1344991 1345347 := bstep (se 1 (by rfl) ⟨1009010, by rfl⟩ : syracuseStep 1345347 = 2018021) B2018021
theorem B1345363 : Blo 1344991 1345363 := bstep (se 1 (by rfl) ⟨1009022, by rfl⟩ : syracuseStep 1345363 = 2018045) B2018045
theorem B1345379 : Blo 1344991 1345379 := bstep (se 1 (by rfl) ⟨1009034, by rfl⟩ : syracuseStep 1345379 = 2018069) B2018069
theorem B7661425 : Blo 1344991 7661425 := bstep (se 2 (by rfl) ⟨2873034, by rfl⟩ : syracuseStep 7661425 = 5746069) B5746069
theorem B1345395 : Blo 1344991 1345395 := bstep (se 1 (by rfl) ⟨1009046, by rfl⟩ : syracuseStep 1345395 = 2018093) B2018093
theorem B2271091 : Blo 1344991 2271091 := bstep (se 1 (by rfl) ⟨1703318, by rfl⟩ : syracuseStep 2271091 = 3406637) B3406637
theorem B1345411 : Blo 1344991 1345411 := bstep (se 1 (by rfl) ⟨1009058, by rfl⟩ : syracuseStep 1345411 = 2018117) B2018117
theorem B1345427 : Blo 1344991 1345427 := bstep (se 1 (by rfl) ⟨1009070, by rfl⟩ : syracuseStep 1345427 = 2018141) B2018141
theorem B6809507 : Blo 1344991 6809507 := bstep (se 1 (by rfl) ⟨5107130, by rfl⟩ : syracuseStep 6809507 = 10214261) B10214261
theorem B1345443 : Blo 1344991 1345443 := bstep (se 1 (by rfl) ⟨1009082, by rfl⟩ : syracuseStep 1345443 = 2018165) B2018165
theorem B1345459 : Blo 1344991 1345459 := bstep (se 1 (by rfl) ⟨1009094, by rfl⟩ : syracuseStep 1345459 = 2018189) B2018189
theorem B1345475 : Blo 1344991 1345475 := bstep (se 1 (by rfl) ⟨1009106, by rfl⟩ : syracuseStep 1345475 = 2018213) B2018213
theorem B2303939 : Blo 1344991 2303939 := bstep (se 1 (by rfl) ⟨1727954, by rfl⟩ : syracuseStep 2303939 = 3455909) B3455909
theorem B1345491 : Blo 1344991 1345491 := bstep (se 1 (by rfl) ⟨1009118, by rfl⟩ : syracuseStep 1345491 = 2018237) B2018237
theorem B1345507 : Blo 1344991 1345507 := bstep (se 1 (by rfl) ⟨1009130, by rfl⟩ : syracuseStep 1345507 = 2018261) B2018261
theorem B5826545 : Blo 1344991 5826545 := bstep (se 2 (by rfl) ⟨2184954, by rfl⟩ : syracuseStep 5826545 = 4369909) B4369909
theorem B1345523 : Blo 1344991 1345523 := bstep (se 1 (by rfl) ⟨1009142, by rfl⟩ : syracuseStep 1345523 = 2018285) B2018285
theorem B2271233 : Blo 1344991 2271233 := bstep (se 2 (by rfl) ⟨851712, by rfl⟩ : syracuseStep 2271233 = 1703425) B1703425
theorem B1345539 : Blo 1344991 1345539 := bstep (se 1 (by rfl) ⟨1009154, by rfl⟩ : syracuseStep 1345539 = 2018309) B2018309
theorem B1345555 : Blo 1344991 1345555 := bstep (se 1 (by rfl) ⟨1009166, by rfl⟩ : syracuseStep 1345555 = 2018333) B2018333
theorem B1345571 : Blo 1344991 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B1345587 : Blo 1344991 1345587 := bstep (se 1 (by rfl) ⟨1009190, by rfl⟩ : syracuseStep 1345587 = 2018381) B2018381
theorem B1345603 : Blo 1344991 1345603 := bstep (se 1 (by rfl) ⟨1009202, by rfl⟩ : syracuseStep 1345603 = 2018405) B2018405
theorem B1345619 : Blo 1344991 1345619 := bstep (se 1 (by rfl) ⟨1009214, by rfl⟩ : syracuseStep 1345619 = 2018429) B2018429
theorem B1345635 : Blo 1344991 1345635 := bstep (se 1 (by rfl) ⟨1009226, by rfl⟩ : syracuseStep 1345635 = 2018453) B2018453
theorem B1345651 : Blo 1344991 1345651 := bstep (se 1 (by rfl) ⟨1009238, by rfl⟩ : syracuseStep 1345651 = 2018477) B2018477
theorem B2271361 : Blo 1344991 2271361 := bstep (se 2 (by rfl) ⟨851760, by rfl⟩ : syracuseStep 2271361 = 1703521) B1703521
theorem B1345667 : Blo 1344991 1345667 := bstep (se 1 (by rfl) ⟨1009250, by rfl⟩ : syracuseStep 1345667 = 2018501) B2018501
theorem B1345683 : Blo 1344991 1345683 := bstep (se 1 (by rfl) ⟨1009262, by rfl⟩ : syracuseStep 1345683 = 2018525) B2018525
theorem B1345699 : Blo 1344991 1345699 := bstep (se 1 (by rfl) ⟨1009274, by rfl⟩ : syracuseStep 1345699 = 2018549) B2018549
theorem B2271395 : Blo 1344991 2271395 := bstep (se 1 (by rfl) ⟨1703546, by rfl⟩ : syracuseStep 2271395 = 3407093) B3407093
theorem B4540589 : Blo 1344991 4540589 := bstep (se 3 (by rfl) ⟨851360, by rfl⟩ : syracuseStep 4540589 = 1702721) B1702721
theorem B1345715 : Blo 1344991 1345715 := bstep (se 1 (by rfl) ⟨1009286, by rfl⟩ : syracuseStep 1345715 = 2018573) B2018573
theorem B1345731 : Blo 1344991 1345731 := bstep (se 1 (by rfl) ⟨1009298, by rfl⟩ : syracuseStep 1345731 = 2018597) B2018597
theorem B4311245 : Blo 1344991 4311245 := bstep (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) B1616717
theorem B1345747 : Blo 1344991 1345747 := bstep (se 1 (by rfl) ⟨1009310, by rfl⟩ : syracuseStep 1345747 = 2018621) B2018621
theorem B2017505 : Blo 1344991 2017505 := bstep (se 2 (by rfl) ⟨756564, by rfl⟩ : syracuseStep 2017505 = 1513129) B1513129
theorem B4540643 : Blo 1344991 4540643 := bstep (se 1 (by rfl) ⟨3405482, by rfl⟩ : syracuseStep 4540643 = 6810965) B6810965
theorem B1345763 : Blo 1344991 1345763 := bstep (se 1 (by rfl) ⟨1009322, by rfl⟩ : syracuseStep 1345763 = 2018645) B2018645
theorem B2017523 : Blo 1344991 2017523 := bstep (se 1 (by rfl) ⟨1513142, by rfl⟩ : syracuseStep 2017523 = 3026285) B3026285
theorem B1345779 : Blo 1344991 1345779 := bstep (se 1 (by rfl) ⟨1009334, by rfl⟩ : syracuseStep 1345779 = 2018669) B2018669
theorem B1345795 : Blo 1344991 1345795 := bstep (se 1 (by rfl) ⟨1009346, by rfl⟩ : syracuseStep 1345795 = 2018693) B2018693
theorem B2017553 : Blo 1344991 2017553 := bstep (se 2 (by rfl) ⟨756582, by rfl⟩ : syracuseStep 2017553 = 1513165) B1513165
theorem B1345811 : Blo 1344991 1345811 := bstep (se 1 (by rfl) ⟨1009358, by rfl⟩ : syracuseStep 1345811 = 2018717) B2018717
theorem B2017571 : Blo 1344991 2017571 := bstep (se 1 (by rfl) ⟨1513178, by rfl⟩ : syracuseStep 2017571 = 3026357) B3026357
theorem B1345827 : Blo 1344991 1345827 := bstep (se 1 (by rfl) ⟨1009370, by rfl⟩ : syracuseStep 1345827 = 2018741) B2018741
theorem B2271523 : Blo 1344991 2271523 := bstep (se 1 (by rfl) ⟨1703642, by rfl⟩ : syracuseStep 2271523 = 3407285) B3407285
theorem B1345843 : Blo 1344991 1345843 := bstep (se 1 (by rfl) ⟨1009382, by rfl⟩ : syracuseStep 1345843 = 2018765) B2018765
theorem B2017601 : Blo 1344991 2017601 := bstep (se 2 (by rfl) ⟨756600, by rfl⟩ : syracuseStep 2017601 = 1513201) B1513201
theorem B1345859 : Blo 1344991 1345859 := bstep (se 1 (by rfl) ⟨1009394, by rfl⟩ : syracuseStep 1345859 = 2018789) B2018789
theorem B5531981 : Blo 1344991 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B2017619 : Blo 1344991 2017619 := bstep (se 1 (by rfl) ⟨1513214, by rfl⟩ : syracuseStep 2017619 = 3026429) B3026429
theorem B1345875 : Blo 1344991 1345875 := bstep (se 1 (by rfl) ⟨1009406, by rfl⟩ : syracuseStep 1345875 = 2018813) B2018813
theorem B1345891 : Blo 1344991 1345891 := bstep (se 1 (by rfl) ⟨1009418, by rfl⟩ : syracuseStep 1345891 = 2018837) B2018837
theorem B2017649 : Blo 1344991 2017649 := bstep (se 2 (by rfl) ⟨756618, by rfl⟩ : syracuseStep 2017649 = 1513237) B1513237
theorem B1345907 : Blo 1344991 1345907 := bstep (se 1 (by rfl) ⟨1009430, by rfl⟩ : syracuseStep 1345907 = 2018861) B2018861
theorem B2017667 : Blo 1344991 2017667 := bstep (se 1 (by rfl) ⟨1513250, by rfl⟩ : syracuseStep 2017667 = 3026501) B3026501
theorem B1345923 : Blo 1344991 1345923 := bstep (se 1 (by rfl) ⟨1009442, by rfl⟩ : syracuseStep 1345923 = 2018885) B2018885
theorem B1345939 : Blo 1344991 1345939 := bstep (se 1 (by rfl) ⟨1009454, by rfl⟩ : syracuseStep 1345939 = 2018909) B2018909
theorem B2017697 : Blo 1344991 2017697 := bstep (se 2 (by rfl) ⟨756636, by rfl⟩ : syracuseStep 2017697 = 1513273) B1513273
theorem B1345955 : Blo 1344991 1345955 := bstep (se 1 (by rfl) ⟨1009466, by rfl⟩ : syracuseStep 1345955 = 2018933) B2018933
theorem B2271665 : Blo 1344991 2271665 := bstep (se 2 (by rfl) ⟨851874, by rfl⟩ : syracuseStep 2271665 = 1703749) B1703749
theorem B2017715 : Blo 1344991 2017715 := bstep (se 1 (by rfl) ⟨1513286, by rfl⟩ : syracuseStep 2017715 = 3026573) B3026573
theorem B1345971 : Blo 1344991 1345971 := bstep (se 1 (by rfl) ⟨1009478, by rfl⟩ : syracuseStep 1345971 = 2018957) B2018957
theorem B1345987 : Blo 1344991 1345987 := bstep (se 1 (by rfl) ⟨1009490, by rfl⟩ : syracuseStep 1345987 = 2018981) B2018981
theorem B2017745 : Blo 1344991 2017745 := bstep (se 2 (by rfl) ⟨756654, by rfl⟩ : syracuseStep 2017745 = 1513309) B1513309
theorem B1346003 : Blo 1344991 1346003 := bstep (se 1 (by rfl) ⟨1009502, by rfl⟩ : syracuseStep 1346003 = 2019005) B2019005
theorem B2017763 : Blo 1344991 2017763 := bstep (se 1 (by rfl) ⟨1513322, by rfl⟩ : syracuseStep 2017763 = 3026645) B3026645
theorem B1346019 : Blo 1344991 1346019 := bstep (se 1 (by rfl) ⟨1009514, by rfl⟩ : syracuseStep 1346019 = 2019029) B2019029
theorem B4540913 : Blo 1344991 4540913 := bstep (se 2 (by rfl) ⟨1702842, by rfl⟩ : syracuseStep 4540913 = 3405685) B3405685
theorem B1346035 : Blo 1344991 1346035 := bstep (se 1 (by rfl) ⟨1009526, by rfl⟩ : syracuseStep 1346035 = 2019053) B2019053
theorem B2017793 : Blo 1344991 2017793 := bstep (se 2 (by rfl) ⟨756672, by rfl⟩ : syracuseStep 2017793 = 1513345) B1513345
theorem B1346051 : Blo 1344991 1346051 := bstep (se 1 (by rfl) ⟨1009538, by rfl⟩ : syracuseStep 1346051 = 2019077) B2019077
theorem B2017811 : Blo 1344991 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B1346067 : Blo 1344991 1346067 := bstep (se 1 (by rfl) ⟨1009550, by rfl⟩ : syracuseStep 1346067 = 2019101) B2019101
theorem B1346083 : Blo 1344991 1346083 := bstep (se 1 (by rfl) ⟨1009562, by rfl⟩ : syracuseStep 1346083 = 2019125) B2019125
theorem B2017841 : Blo 1344991 2017841 := bstep (se 2 (by rfl) ⟨756690, by rfl⟩ : syracuseStep 2017841 = 1513381) B1513381
theorem B2271793 : Blo 1344991 2271793 := bstep (se 2 (by rfl) ⟨851922, by rfl⟩ : syracuseStep 2271793 = 1703845) B1703845
theorem B1346099 : Blo 1344991 1346099 := bstep (se 1 (by rfl) ⟨1009574, by rfl⟩ : syracuseStep 1346099 = 2019149) B2019149
theorem B2017859 : Blo 1344991 2017859 := bstep (se 1 (by rfl) ⟨1513394, by rfl⟩ : syracuseStep 2017859 = 3026789) B3026789
theorem B1346115 : Blo 1344991 1346115 := bstep (se 1 (by rfl) ⟨1009586, by rfl⟩ : syracuseStep 1346115 = 2019173) B2019173
theorem B16362053 : Blo 1344991 16362053 := bstep (se 4 (by rfl) ⟨1533942, by rfl⟩ : syracuseStep 16362053 = 3067885) B3067885
theorem B1346131 : Blo 1344991 1346131 := bstep (se 1 (by rfl) ⟨1009598, by rfl⟩ : syracuseStep 1346131 = 2019197) B2019197
theorem B2271827 : Blo 1344991 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B2017889 : Blo 1344991 2017889 := bstep (se 2 (by rfl) ⟨756708, by rfl⟩ : syracuseStep 2017889 = 1513417) B1513417
theorem B1346147 : Blo 1344991 1346147 := bstep (se 1 (by rfl) ⟨1009610, by rfl⟩ : syracuseStep 1346147 = 2019221) B2019221
theorem B6818417 : Blo 1344991 6818417 := bstep (se 2 (by rfl) ⟨2556906, by rfl⟩ : syracuseStep 6818417 = 5113813) B5113813
theorem B2017907 : Blo 1344991 2017907 := bstep (se 1 (by rfl) ⟨1513430, by rfl⟩ : syracuseStep 2017907 = 3026861) B3026861
theorem B1346163 : Blo 1344991 1346163 := bstep (se 1 (by rfl) ⟨1009622, by rfl⟩ : syracuseStep 1346163 = 2019245) B2019245
theorem B1346179 : Blo 1344991 1346179 := bstep (se 1 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 1346179 = 2019269) B2019269
theorem B2017937 : Blo 1344991 2017937 := bstep (se 2 (by rfl) ⟨756726, by rfl⟩ : syracuseStep 2017937 = 1513453) B1513453
theorem B1346195 : Blo 1344991 1346195 := bstep (se 1 (by rfl) ⟨1009646, by rfl⟩ : syracuseStep 1346195 = 2019293) B2019293
theorem B2017955 : Blo 1344991 2017955 := bstep (se 1 (by rfl) ⟨1513466, by rfl⟩ : syracuseStep 2017955 = 3026933) B3026933
theorem B1346211 : Blo 1344991 1346211 := bstep (se 1 (by rfl) ⟨1009658, by rfl⟩ : syracuseStep 1346211 = 2019317) B2019317
theorem B1346227 : Blo 1344991 1346227 := bstep (se 1 (by rfl) ⟨1009670, by rfl⟩ : syracuseStep 1346227 = 2019341) B2019341
theorem B2017985 : Blo 1344991 2017985 := bstep (se 2 (by rfl) ⟨756744, by rfl⟩ : syracuseStep 2017985 = 1513489) B1513489
theorem B1346243 : Blo 1344991 1346243 := bstep (se 1 (by rfl) ⟨1009682, by rfl⟩ : syracuseStep 1346243 = 2019365) B2019365
theorem B6810317 : Blo 1344991 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B2018003 : Blo 1344991 2018003 := bstep (se 1 (by rfl) ⟨1513502, by rfl⟩ : syracuseStep 2018003 = 3027005) B3027005
theorem B1346259 : Blo 1344991 1346259 := bstep (se 1 (by rfl) ⟨1009694, by rfl⟩ : syracuseStep 1346259 = 2019389) B2019389
theorem B2271955 : Blo 1344991 2271955 := bstep (se 1 (by rfl) ⟨1703966, by rfl⟩ : syracuseStep 2271955 = 3407933) B3407933
theorem B1346275 : Blo 1344991 1346275 := bstep (se 1 (by rfl) ⟨1009706, by rfl⟩ : syracuseStep 1346275 = 2019413) B2019413
theorem B2018033 : Blo 1344991 2018033 := bstep (se 2 (by rfl) ⟨756762, by rfl⟩ : syracuseStep 2018033 = 1513525) B1513525
theorem B1346291 : Blo 1344991 1346291 := bstep (se 1 (by rfl) ⟨1009718, by rfl⟩ : syracuseStep 1346291 = 2019437) B2019437
theorem B2018051 : Blo 1344991 2018051 := bstep (se 1 (by rfl) ⟨1513538, by rfl⟩ : syracuseStep 2018051 = 3027077) B3027077
theorem B1346307 : Blo 1344991 1346307 := bstep (se 1 (by rfl) ⟨1009730, by rfl⟩ : syracuseStep 1346307 = 2019461) B2019461
theorem B12282637 : Blo 1344991 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B1346323 : Blo 1344991 1346323 := bstep (se 1 (by rfl) ⟨1009742, by rfl⟩ : syracuseStep 1346323 = 2019485) B2019485
theorem B2018081 : Blo 1344991 2018081 := bstep (se 2 (by rfl) ⟨756780, by rfl⟩ : syracuseStep 2018081 = 1513561) B1513561
theorem B1346339 : Blo 1344991 1346339 := bstep (se 1 (by rfl) ⟨1009754, by rfl⟩ : syracuseStep 1346339 = 2019509) B2019509
theorem B2018099 : Blo 1344991 2018099 := bstep (se 1 (by rfl) ⟨1513574, by rfl⟩ : syracuseStep 2018099 = 3027149) B3027149
theorem B1346355 : Blo 1344991 1346355 := bstep (se 1 (by rfl) ⟨1009766, by rfl⟩ : syracuseStep 1346355 = 2019533) B2019533
theorem B1346371 : Blo 1344991 1346371 := bstep (se 1 (by rfl) ⟨1009778, by rfl⟩ : syracuseStep 1346371 = 2019557) B2019557
theorem B2018129 : Blo 1344991 2018129 := bstep (se 2 (by rfl) ⟨756798, by rfl⟩ : syracuseStep 2018129 = 1513597) B1513597
theorem B1346387 : Blo 1344991 1346387 := bstep (se 1 (by rfl) ⟨1009790, by rfl⟩ : syracuseStep 1346387 = 2019581) B2019581
theorem B2272097 : Blo 1344991 2272097 := bstep (se 2 (by rfl) ⟨852036, by rfl⟩ : syracuseStep 2272097 = 1704073) B1704073
theorem B2018147 : Blo 1344991 2018147 := bstep (se 1 (by rfl) ⟨1513610, by rfl⟩ : syracuseStep 2018147 = 3027221) B3027221
theorem B1346403 : Blo 1344991 1346403 := bstep (se 1 (by rfl) ⟨1009802, by rfl⟩ : syracuseStep 1346403 = 2019605) B2019605
theorem B1346419 : Blo 1344991 1346419 := bstep (se 1 (by rfl) ⟨1009814, by rfl⟩ : syracuseStep 1346419 = 2019629) B2019629
theorem B2018177 : Blo 1344991 2018177 := bstep (se 2 (by rfl) ⟨756816, by rfl⟩ : syracuseStep 2018177 = 1513633) B1513633
theorem B1346435 : Blo 1344991 1346435 := bstep (se 1 (by rfl) ⟨1009826, by rfl⟩ : syracuseStep 1346435 = 2019653) B2019653
theorem B2018195 : Blo 1344991 2018195 := bstep (se 1 (by rfl) ⟨1513646, by rfl⟩ : syracuseStep 2018195 = 3027293) B3027293
theorem B1346451 : Blo 1344991 1346451 := bstep (se 1 (by rfl) ⟨1009838, by rfl⟩ : syracuseStep 1346451 = 2019677) B2019677
theorem B1346467 : Blo 1344991 1346467 := bstep (se 1 (by rfl) ⟨1009850, by rfl⟩ : syracuseStep 1346467 = 2019701) B2019701
theorem B2018225 : Blo 1344991 2018225 := bstep (se 2 (by rfl) ⟨756834, by rfl⟩ : syracuseStep 2018225 = 1513669) B1513669
theorem B6466481 : Blo 1344991 6466481 := bstep (se 2 (by rfl) ⟨2424930, by rfl⟩ : syracuseStep 6466481 = 4849861) B4849861
theorem B1346483 : Blo 1344991 1346483 := bstep (se 1 (by rfl) ⟨1009862, by rfl⟩ : syracuseStep 1346483 = 2019725) B2019725
theorem B3640241 : Blo 1344991 3640241 := bstep (se 2 (by rfl) ⟨1365090, by rfl⟩ : syracuseStep 3640241 = 2730181) B2730181
theorem B2018243 : Blo 1344991 2018243 := bstep (se 1 (by rfl) ⟨1513682, by rfl⟩ : syracuseStep 2018243 = 3027365) B3027365
theorem B1346499 : Blo 1344991 1346499 := bstep (se 1 (by rfl) ⟨1009874, by rfl⟩ : syracuseStep 1346499 = 2019749) B2019749
theorem B1616851 : Blo 1344991 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B1346515 : Blo 1344991 1346515 := bstep (se 1 (by rfl) ⟨1009886, by rfl⟩ : syracuseStep 1346515 = 2019773) B2019773
theorem B2018273 : Blo 1344991 2018273 := bstep (se 2 (by rfl) ⟨756852, by rfl⟩ : syracuseStep 2018273 = 1513705) B1513705
theorem B2272225 : Blo 1344991 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B1346531 : Blo 1344991 1346531 := bstep (se 1 (by rfl) ⟨1009898, by rfl⟩ : syracuseStep 1346531 = 2019797) B2019797
theorem B2018291 : Blo 1344991 2018291 := bstep (se 1 (by rfl) ⟨1513718, by rfl⟩ : syracuseStep 2018291 = 3027437) B3027437
theorem B1346547 : Blo 1344991 1346547 := bstep (se 1 (by rfl) ⟨1009910, by rfl⟩ : syracuseStep 1346547 = 2019821) B2019821
theorem B2272259 : Blo 1344991 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B1346563 : Blo 1344991 1346563 := bstep (se 1 (by rfl) ⟨1009922, by rfl⟩ : syracuseStep 1346563 = 2019845) B2019845
theorem B4541453 : Blo 1344991 4541453 := bstep (se 3 (by rfl) ⟨851522, by rfl⟩ : syracuseStep 4541453 = 1703045) B1703045
theorem B2018321 : Blo 1344991 2018321 := bstep (se 2 (by rfl) ⟨756870, by rfl⟩ : syracuseStep 2018321 = 1513741) B1513741
theorem B1346579 : Blo 1344991 1346579 := bstep (se 1 (by rfl) ⟨1009934, by rfl⟩ : syracuseStep 1346579 = 2019869) B2019869
theorem B2018339 : Blo 1344991 2018339 := bstep (se 1 (by rfl) ⟨1513754, by rfl⟩ : syracuseStep 2018339 = 3027509) B3027509
theorem B1346595 : Blo 1344991 1346595 := bstep (se 1 (by rfl) ⟨1009946, by rfl⟩ : syracuseStep 1346595 = 2019893) B2019893
theorem B1346611 : Blo 1344991 1346611 := bstep (se 1 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 1346611 = 2019917) B2019917
theorem B2018369 : Blo 1344991 2018369 := bstep (se 2 (by rfl) ⟨756888, by rfl⟩ : syracuseStep 2018369 = 1513777) B1513777
theorem B4541507 : Blo 1344991 4541507 := bstep (se 1 (by rfl) ⟨3406130, by rfl⟩ : syracuseStep 4541507 = 6812261) B6812261
theorem B1346627 : Blo 1344991 1346627 := bstep (se 1 (by rfl) ⟨1009970, by rfl⟩ : syracuseStep 1346627 = 2019941) B2019941
theorem B2018387 : Blo 1344991 2018387 := bstep (se 1 (by rfl) ⟨1513790, by rfl⟩ : syracuseStep 2018387 = 3027581) B3027581
theorem B1346643 : Blo 1344991 1346643 := bstep (se 1 (by rfl) ⟨1009982, by rfl⟩ : syracuseStep 1346643 = 2019965) B2019965
theorem B1346659 : Blo 1344991 1346659 := bstep (se 1 (by rfl) ⟨1009994, by rfl⟩ : syracuseStep 1346659 = 2019989) B2019989
theorem B2018417 : Blo 1344991 2018417 := bstep (se 2 (by rfl) ⟨756906, by rfl⟩ : syracuseStep 2018417 = 1513813) B1513813
theorem B1346675 : Blo 1344991 1346675 := bstep (se 1 (by rfl) ⟨1010006, by rfl⟩ : syracuseStep 1346675 = 2020013) B2020013
theorem B2018435 : Blo 1344991 2018435 := bstep (se 1 (by rfl) ⟨1513826, by rfl⟩ : syracuseStep 2018435 = 3027653) B3027653
theorem B2272387 : Blo 1344991 2272387 := bstep (se 1 (by rfl) ⟨1704290, by rfl⟩ : syracuseStep 2272387 = 3408581) B3408581
theorem B1346691 : Blo 1344991 1346691 := bstep (se 1 (by rfl) ⟨1010018, by rfl⟩ : syracuseStep 1346691 = 2020037) B2020037
theorem B1346707 : Blo 1344991 1346707 := bstep (se 1 (by rfl) ⟨1010030, by rfl⟩ : syracuseStep 1346707 = 2020061) B2020061
theorem B2018465 : Blo 1344991 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B1346723 : Blo 1344991 1346723 := bstep (se 1 (by rfl) ⟨1010042, by rfl⟩ : syracuseStep 1346723 = 2020085) B2020085
theorem B2018483 : Blo 1344991 2018483 := bstep (se 1 (by rfl) ⟨1513862, by rfl⟩ : syracuseStep 2018483 = 3027725) B3027725
theorem B1346739 : Blo 1344991 1346739 := bstep (se 1 (by rfl) ⟨1010054, by rfl⟩ : syracuseStep 1346739 = 2020109) B2020109
theorem B1346755 : Blo 1344991 1346755 := bstep (se 1 (by rfl) ⟨1010066, by rfl⟩ : syracuseStep 1346755 = 2020133) B2020133
theorem B2018513 : Blo 1344991 2018513 := bstep (se 2 (by rfl) ⟨756942, by rfl⟩ : syracuseStep 2018513 = 1513885) B1513885
theorem B1346771 : Blo 1344991 1346771 := bstep (se 1 (by rfl) ⟨1010078, by rfl⟩ : syracuseStep 1346771 = 2020157) B2020157
theorem B2018531 : Blo 1344991 2018531 := bstep (se 1 (by rfl) ⟨1513898, by rfl⟩ : syracuseStep 2018531 = 3027797) B3027797
theorem B1346787 : Blo 1344991 1346787 := bstep (se 1 (by rfl) ⟨1010090, by rfl⟩ : syracuseStep 1346787 = 2020181) B2020181
theorem B1346803 : Blo 1344991 1346803 := bstep (se 1 (by rfl) ⟨1010102, by rfl⟩ : syracuseStep 1346803 = 2020205) B2020205
theorem B2018561 : Blo 1344991 2018561 := bstep (se 2 (by rfl) ⟨756960, by rfl⟩ : syracuseStep 2018561 = 1513921) B1513921
theorem B1346819 : Blo 1344991 1346819 := bstep (se 1 (by rfl) ⟨1010114, by rfl⟩ : syracuseStep 1346819 = 2020229) B2020229
theorem B2272529 : Blo 1344991 2272529 := bstep (se 2 (by rfl) ⟨852198, by rfl⟩ : syracuseStep 2272529 = 1704397) B1704397
theorem B2018579 : Blo 1344991 2018579 := bstep (se 1 (by rfl) ⟨1513934, by rfl⟩ : syracuseStep 2018579 = 3027869) B3027869
theorem B1346835 : Blo 1344991 1346835 := bstep (se 1 (by rfl) ⟨1010126, by rfl⟩ : syracuseStep 1346835 = 2020253) B2020253
theorem B7662883 : Blo 1344991 7662883 := bstep (se 1 (by rfl) ⟨5747162, by rfl⟩ : syracuseStep 7662883 = 11494325) B11494325
theorem B1346851 : Blo 1344991 1346851 := bstep (se 1 (by rfl) ⟨1010138, by rfl⟩ : syracuseStep 1346851 = 2020277) B2020277
theorem B2018609 : Blo 1344991 2018609 := bstep (se 2 (by rfl) ⟨756978, by rfl⟩ : syracuseStep 2018609 = 1513957) B1513957
theorem B1346867 : Blo 1344991 1346867 := bstep (se 1 (by rfl) ⟨1010150, by rfl⟩ : syracuseStep 1346867 = 2020301) B2020301
theorem B2018627 : Blo 1344991 2018627 := bstep (se 1 (by rfl) ⟨1513970, by rfl⟩ : syracuseStep 2018627 = 3027941) B3027941
theorem B1346883 : Blo 1344991 1346883 := bstep (se 1 (by rfl) ⟨1010162, by rfl⟩ : syracuseStep 1346883 = 2020325) B2020325
theorem B4541777 : Blo 1344991 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B1346899 : Blo 1344991 1346899 := bstep (se 1 (by rfl) ⟨1010174, by rfl⟩ : syracuseStep 1346899 = 2020349) B2020349
theorem B2018657 : Blo 1344991 2018657 := bstep (se 2 (by rfl) ⟨756996, by rfl⟩ : syracuseStep 2018657 = 1513993) B1513993
theorem B1346915 : Blo 1344991 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B2018675 : Blo 1344991 2018675 := bstep (se 1 (by rfl) ⟨1514006, by rfl⟩ : syracuseStep 2018675 = 3028013) B3028013
theorem B1346931 : Blo 1344991 1346931 := bstep (se 1 (by rfl) ⟨1010198, by rfl⟩ : syracuseStep 1346931 = 2020397) B2020397
theorem B1346947 : Blo 1344991 1346947 := bstep (se 1 (by rfl) ⟨1010210, by rfl⟩ : syracuseStep 1346947 = 2020421) B2020421
theorem B3026321 : Blo 1344991 3026321 := bstep (se 2 (by rfl) ⟨1134870, by rfl⟩ : syracuseStep 3026321 = 2269741) B2269741
theorem B2018705 : Blo 1344991 2018705 := bstep (se 2 (by rfl) ⟨757014, by rfl⟩ : syracuseStep 2018705 = 1514029) B1514029
theorem B2272657 : Blo 1344991 2272657 := bstep (se 2 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 2272657 = 1704493) B1704493
theorem B1346963 : Blo 1344991 1346963 := bstep (se 1 (by rfl) ⟨1010222, by rfl⟩ : syracuseStep 1346963 = 2020445) B2020445
theorem B3026339 : Blo 1344991 3026339 := bstep (se 1 (by rfl) ⟨2269754, by rfl⟩ : syracuseStep 3026339 = 4539509) B4539509
theorem B2018723 : Blo 1344991 2018723 := bstep (se 1 (by rfl) ⟨1514042, by rfl⟩ : syracuseStep 2018723 = 3028085) B3028085
theorem B1346979 : Blo 1344991 1346979 := bstep (se 1 (by rfl) ⟨1010234, by rfl⟩ : syracuseStep 1346979 = 2020469) B2020469
theorem B1437107 : Blo 1344991 1437107 := bstep (se 1 (by rfl) ⟨1077830, by rfl⟩ : syracuseStep 1437107 = 2155661) B2155661
theorem B2272691 : Blo 1344991 2272691 := bstep (se 1 (by rfl) ⟨1704518, by rfl⟩ : syracuseStep 2272691 = 3409037) B3409037
theorem B2018753 : Blo 1344991 2018753 := bstep (se 2 (by rfl) ⟨757032, by rfl⟩ : syracuseStep 2018753 = 1514065) B1514065
theorem B2018771 : Blo 1344991 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B2018801 : Blo 1344991 2018801 := bstep (se 2 (by rfl) ⟨757050, by rfl⟩ : syracuseStep 2018801 = 1514101) B1514101
theorem B2018819 : Blo 1344991 2018819 := bstep (se 1 (by rfl) ⟨1514114, by rfl⟩ : syracuseStep 2018819 = 3028229) B3028229
theorem B6139405 : Blo 1344991 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B29101589 : Blo 1344991 29101589 := bstep (se 6 (by rfl) ⟨682068, by rfl⟩ : syracuseStep 29101589 = 1364137) B1364137
theorem B2018849 : Blo 1344991 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B2018867 : Blo 1344991 2018867 := bstep (se 1 (by rfl) ⟨1514150, by rfl⟩ : syracuseStep 2018867 = 3028301) B3028301
theorem B15330869 : Blo 1344991 15330869 := bstep (se 5 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 15330869 = 1437269) B1437269
theorem B2272819 : Blo 1344991 2272819 := bstep (se 1 (by rfl) ⟨1704614, by rfl⟩ : syracuseStep 2272819 = 3409229) B3409229
theorem B2018897 : Blo 1344991 2018897 := bstep (se 2 (by rfl) ⟨757086, by rfl⟩ : syracuseStep 2018897 = 1514173) B1514173
theorem B7769699 : Blo 1344991 7769699 := bstep (se 1 (by rfl) ⟨5827274, by rfl⟩ : syracuseStep 7769699 = 11654549) B11654549
theorem B2018915 : Blo 1344991 2018915 := bstep (se 1 (by rfl) ⟨1514186, by rfl⟩ : syracuseStep 2018915 = 3028373) B3028373
theorem B5107313 : Blo 1344991 5107313 := bstep (se 2 (by rfl) ⟨1915242, by rfl⟩ : syracuseStep 5107313 = 3830485) B3830485
theorem B10219121 : Blo 1344991 10219121 := bstep (se 2 (by rfl) ⟨3832170, by rfl⟩ : syracuseStep 10219121 = 7664341) B7664341
theorem B2018945 : Blo 1344991 2018945 := bstep (se 2 (by rfl) ⟨757104, by rfl⟩ : syracuseStep 2018945 = 1514209) B1514209
theorem B2018963 : Blo 1344991 2018963 := bstep (se 1 (by rfl) ⟨1514222, by rfl⟩ : syracuseStep 2018963 = 3028445) B3028445
theorem B3026609 : Blo 1344991 3026609 := bstep (se 2 (by rfl) ⟨1134978, by rfl⟩ : syracuseStep 3026609 = 2269957) B2269957
theorem B2018993 : Blo 1344991 2018993 := bstep (se 2 (by rfl) ⟨757122, by rfl⟩ : syracuseStep 2018993 = 1514245) B1514245
theorem B2272961 : Blo 1344991 2272961 := bstep (se 2 (by rfl) ⟨852360, by rfl⟩ : syracuseStep 2272961 = 1704721) B1704721
theorem B3026627 : Blo 1344991 3026627 := bstep (se 1 (by rfl) ⟨2269970, by rfl⟩ : syracuseStep 3026627 = 4539941) B4539941
theorem B2019011 : Blo 1344991 2019011 := bstep (se 1 (by rfl) ⟨1514258, by rfl⟩ : syracuseStep 2019011 = 3028517) B3028517
theorem B2019041 : Blo 1344991 2019041 := bstep (se 2 (by rfl) ⟨757140, by rfl⟩ : syracuseStep 2019041 = 1514281) B1514281
theorem B2019059 : Blo 1344991 2019059 := bstep (se 1 (by rfl) ⟨1514294, by rfl⟩ : syracuseStep 2019059 = 3028589) B3028589
theorem B1969921 : Blo 1344991 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B13119245 : Blo 1344991 13119245 := bstep (se 3 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 13119245 = 4919717) B4919717
theorem B2019089 : Blo 1344991 2019089 := bstep (se 2 (by rfl) ⟨757158, by rfl⟩ : syracuseStep 2019089 = 1514317) B1514317
theorem B2019107 : Blo 1344991 2019107 := bstep (se 1 (by rfl) ⟨1514330, by rfl⟩ : syracuseStep 2019107 = 3028661) B3028661
theorem B7663409 : Blo 1344991 7663409 := bstep (se 2 (by rfl) ⟨2873778, by rfl⟩ : syracuseStep 7663409 = 5747557) B5747557
theorem B8621873 : Blo 1344991 8621873 := bstep (se 2 (by rfl) ⟨3233202, by rfl⟩ : syracuseStep 8621873 = 6466405) B6466405
theorem B2019137 : Blo 1344991 2019137 := bstep (se 2 (by rfl) ⟨757176, by rfl⟩ : syracuseStep 2019137 = 1514353) B1514353
theorem B2019155 : Blo 1344991 2019155 := bstep (se 1 (by rfl) ⟨1514366, by rfl⟩ : syracuseStep 2019155 = 3028733) B3028733
theorem B4542317 : Blo 1344991 4542317 := bstep (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) B1703369
theorem B2019185 : Blo 1344991 2019185 := bstep (se 2 (by rfl) ⟨757194, by rfl⟩ : syracuseStep 2019185 = 1514389) B1514389
theorem B2019203 : Blo 1344991 2019203 := bstep (se 1 (by rfl) ⟨1514402, by rfl⟩ : syracuseStep 2019203 = 3028805) B3028805
theorem B2019233 : Blo 1344991 2019233 := bstep (se 2 (by rfl) ⟨757212, by rfl⟩ : syracuseStep 2019233 = 1514425) B1514425
theorem B4542371 : Blo 1344991 4542371 := bstep (se 1 (by rfl) ⟨3406778, by rfl⟩ : syracuseStep 4542371 = 6813557) B6813557
theorem B3231665 : Blo 1344991 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B2019251 : Blo 1344991 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B4313027 : Blo 1344991 4313027 := bstep (se 1 (by rfl) ⟨3234770, by rfl⟩ : syracuseStep 4313027 = 6469541) B6469541
theorem B3026897 : Blo 1344991 3026897 := bstep (se 2 (by rfl) ⟨1135086, by rfl⟩ : syracuseStep 3026897 = 2270173) B2270173
theorem B2019281 : Blo 1344991 2019281 := bstep (se 2 (by rfl) ⟨757230, by rfl⟩ : syracuseStep 2019281 = 1514461) B1514461
theorem B3026915 : Blo 1344991 3026915 := bstep (se 1 (by rfl) ⟨2270186, by rfl⟩ : syracuseStep 3026915 = 4540373) B4540373
theorem B2019299 : Blo 1344991 2019299 := bstep (se 1 (by rfl) ⟨1514474, by rfl⟩ : syracuseStep 2019299 = 3028949) B3028949
theorem B3411953 : Blo 1344991 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B2019329 : Blo 1344991 2019329 := bstep (se 2 (by rfl) ⟨757248, by rfl⟩ : syracuseStep 2019329 = 1514497) B1514497
theorem B6467597 : Blo 1344991 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B2019347 : Blo 1344991 2019347 := bstep (se 1 (by rfl) ⟨1514510, by rfl⟩ : syracuseStep 2019347 = 3029021) B3029021
theorem B2019377 : Blo 1344991 2019377 := bstep (se 2 (by rfl) ⟨757266, by rfl⟩ : syracuseStep 2019377 = 1514533) B1514533
theorem B2019395 : Blo 1344991 2019395 := bstep (se 1 (by rfl) ⟨1514546, by rfl⟩ : syracuseStep 2019395 = 3029093) B3029093
theorem B2019425 : Blo 1344991 2019425 := bstep (se 2 (by rfl) ⟨757284, by rfl⟩ : syracuseStep 2019425 = 1514569) B1514569
theorem B2019443 : Blo 1344991 2019443 := bstep (se 1 (by rfl) ⟨1514582, by rfl⟩ : syracuseStep 2019443 = 3029165) B3029165
theorem B2019473 : Blo 1344991 2019473 := bstep (se 2 (by rfl) ⟨757302, by rfl⟩ : syracuseStep 2019473 = 1514605) B1514605
theorem B2019491 : Blo 1344991 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1437859 : Blo 1344991 1437859 := bstep (se 1 (by rfl) ⟨1078394, by rfl⟩ : syracuseStep 1437859 = 2156789) B2156789
theorem B4542641 : Blo 1344991 4542641 := bstep (se 2 (by rfl) ⟨1703490, by rfl⟩ : syracuseStep 4542641 = 3406981) B3406981
theorem B2019521 : Blo 1344991 2019521 := bstep (se 2 (by rfl) ⟨757320, by rfl⟩ : syracuseStep 2019521 = 1514641) B1514641
theorem B2019539 : Blo 1344991 2019539 := bstep (se 1 (by rfl) ⟨1514654, by rfl⟩ : syracuseStep 2019539 = 3029309) B3029309
theorem B3027185 : Blo 1344991 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B2019569 : Blo 1344991 2019569 := bstep (se 2 (by rfl) ⟨757338, by rfl⟩ : syracuseStep 2019569 = 1514677) B1514677
theorem B4854001 : Blo 1344991 4854001 := bstep (se 2 (by rfl) ⟨1820250, by rfl⟩ : syracuseStep 4854001 = 3640501) B3640501
theorem B3027203 : Blo 1344991 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B2019587 : Blo 1344991 2019587 := bstep (se 1 (by rfl) ⟨1514690, by rfl⟩ : syracuseStep 2019587 = 3029381) B3029381
theorem B5107981 : Blo 1344991 5107981 := bstep (se 3 (by rfl) ⟨957746, by rfl⟩ : syracuseStep 5107981 = 1915493) B1915493
theorem B3068177 : Blo 1344991 3068177 := bstep (se 2 (by rfl) ⟨1150566, by rfl⟩ : syracuseStep 3068177 = 2301133) B2301133
theorem B2019617 : Blo 1344991 2019617 := bstep (se 2 (by rfl) ⟨757356, by rfl⟩ : syracuseStep 2019617 = 1514713) B1514713
theorem B2019635 : Blo 1344991 2019635 := bstep (se 1 (by rfl) ⟨1514726, by rfl⟩ : syracuseStep 2019635 = 3029453) B3029453
theorem B4149571 : Blo 1344991 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B2765137 : Blo 1344991 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B2019665 : Blo 1344991 2019665 := bstep (se 2 (by rfl) ⟨757374, by rfl⟩ : syracuseStep 2019665 = 1514749) B1514749
theorem B2019683 : Blo 1344991 2019683 := bstep (se 1 (by rfl) ⟨1514762, by rfl⟩ : syracuseStep 2019683 = 3029525) B3029525
theorem B4854115 : Blo 1344991 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B2019713 : Blo 1344991 2019713 := bstep (se 2 (by rfl) ⟨757392, by rfl⟩ : syracuseStep 2019713 = 1514785) B1514785
theorem B2019731 : Blo 1344991 2019731 := bstep (se 1 (by rfl) ⟨1514798, by rfl⟩ : syracuseStep 2019731 = 3029597) B3029597
theorem B2019761 : Blo 1344991 2019761 := bstep (se 2 (by rfl) ⟨757410, by rfl⟩ : syracuseStep 2019761 = 1514821) B1514821
theorem B2019779 : Blo 1344991 2019779 := bstep (se 1 (by rfl) ⟨1514834, by rfl⟩ : syracuseStep 2019779 = 3029669) B3029669
theorem B2019809 : Blo 1344991 2019809 := bstep (se 2 (by rfl) ⟨757428, by rfl⟩ : syracuseStep 2019809 = 1514857) B1514857
theorem B3830257 : Blo 1344991 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B2019827 : Blo 1344991 2019827 := bstep (se 1 (by rfl) ⟨1514870, by rfl⟩ : syracuseStep 2019827 = 3029741) B3029741
theorem B3109393 : Blo 1344991 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B3027473 : Blo 1344991 3027473 := bstep (se 2 (by rfl) ⟨1135302, by rfl⟩ : syracuseStep 3027473 = 2270605) B2270605
theorem B2019857 : Blo 1344991 2019857 := bstep (se 2 (by rfl) ⟨757446, by rfl⟩ : syracuseStep 2019857 = 1514893) B1514893
theorem B3027491 : Blo 1344991 3027491 := bstep (se 1 (by rfl) ⟨2270618, by rfl⟩ : syracuseStep 3027491 = 4541237) B4541237
theorem B2019875 : Blo 1344991 2019875 := bstep (se 1 (by rfl) ⟨1514906, by rfl⟩ : syracuseStep 2019875 = 3029813) B3029813
theorem B2019905 : Blo 1344991 2019905 := bstep (se 2 (by rfl) ⟨757464, by rfl⟩ : syracuseStep 2019905 = 1514929) B1514929
theorem B2019923 : Blo 1344991 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B2019953 : Blo 1344991 2019953 := bstep (se 2 (by rfl) ⟨757482, by rfl⟩ : syracuseStep 2019953 = 1514965) B1514965
theorem B2019971 : Blo 1344991 2019971 := bstep (se 1 (by rfl) ⟨1514978, by rfl⟩ : syracuseStep 2019971 = 3029957) B3029957
theorem B2020001 : Blo 1344991 2020001 := bstep (se 2 (by rfl) ⟨757500, by rfl⟩ : syracuseStep 2020001 = 1515001) B1515001
theorem B2020019 : Blo 1344991 2020019 := bstep (se 1 (by rfl) ⟨1515014, by rfl⟩ : syracuseStep 2020019 = 3030029) B3030029
theorem B4543181 : Blo 1344991 4543181 := bstep (se 3 (by rfl) ⟨851846, by rfl⟩ : syracuseStep 4543181 = 1703693) B1703693
theorem B2020049 : Blo 1344991 2020049 := bstep (se 2 (by rfl) ⟨757518, by rfl⟩ : syracuseStep 2020049 = 1515037) B1515037
theorem B2020067 : Blo 1344991 2020067 := bstep (se 1 (by rfl) ⟨1515050, by rfl⟩ : syracuseStep 2020067 = 3030101) B3030101
theorem B2020097 : Blo 1344991 2020097 := bstep (se 2 (by rfl) ⟨757536, by rfl⟩ : syracuseStep 2020097 = 1515073) B1515073
theorem B4543235 : Blo 1344991 4543235 := bstep (se 1 (by rfl) ⟨3407426, by rfl⟩ : syracuseStep 4543235 = 6814853) B6814853
theorem B2020115 : Blo 1344991 2020115 := bstep (se 1 (by rfl) ⟨1515086, by rfl⟩ : syracuseStep 2020115 = 3030173) B3030173
theorem B3027761 : Blo 1344991 3027761 := bstep (se 2 (by rfl) ⟨1135410, by rfl⟩ : syracuseStep 3027761 = 2270821) B2270821
theorem B8188721 : Blo 1344991 8188721 := bstep (se 2 (by rfl) ⟨3070770, by rfl⟩ : syracuseStep 8188721 = 6141541) B6141541
theorem B2020145 : Blo 1344991 2020145 := bstep (se 2 (by rfl) ⟨757554, by rfl⟩ : syracuseStep 2020145 = 1515109) B1515109
theorem B3027779 : Blo 1344991 3027779 := bstep (se 1 (by rfl) ⟨2270834, by rfl⟩ : syracuseStep 3027779 = 4541669) B4541669
theorem B2020163 : Blo 1344991 2020163 := bstep (se 1 (by rfl) ⟨1515122, by rfl⟩ : syracuseStep 2020163 = 3030245) B3030245
theorem B2020193 : Blo 1344991 2020193 := bstep (se 2 (by rfl) ⟨757572, by rfl⟩ : syracuseStep 2020193 = 1515145) B1515145
theorem B17486705 : Blo 1344991 17486705 := bstep (se 2 (by rfl) ⟨6557514, by rfl⟩ : syracuseStep 17486705 = 13115029) B13115029
theorem B2020211 : Blo 1344991 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B2020241 : Blo 1344991 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B2020259 : Blo 1344991 2020259 := bstep (se 1 (by rfl) ⟨1515194, by rfl⟩ : syracuseStep 2020259 = 3030389) B3030389
theorem B2020289 : Blo 1344991 2020289 := bstep (se 2 (by rfl) ⟨757608, by rfl⟩ : syracuseStep 2020289 = 1515217) B1515217
theorem B2020307 : Blo 1344991 2020307 := bstep (se 1 (by rfl) ⟨1515230, by rfl⟩ : syracuseStep 2020307 = 3030461) B3030461
theorem B2020337 : Blo 1344991 2020337 := bstep (se 2 (by rfl) ⟨757626, by rfl⟩ : syracuseStep 2020337 = 1515253) B1515253
theorem B2020355 : Blo 1344991 2020355 := bstep (se 1 (by rfl) ⟨1515266, by rfl⟩ : syracuseStep 2020355 = 3030533) B3030533
theorem B4543505 : Blo 1344991 4543505 := bstep (se 2 (by rfl) ⟨1703814, by rfl⟩ : syracuseStep 4543505 = 3407629) B3407629
theorem B2020385 : Blo 1344991 2020385 := bstep (se 2 (by rfl) ⟨757644, by rfl⟩ : syracuseStep 2020385 = 1515289) B1515289
theorem B5108771 : Blo 1344991 5108771 := bstep (se 1 (by rfl) ⟨3831578, by rfl⟩ : syracuseStep 5108771 = 7663157) B7663157
theorem B2020403 : Blo 1344991 2020403 := bstep (se 1 (by rfl) ⟨1515302, by rfl⟩ : syracuseStep 2020403 = 3030605) B3030605
theorem B3028049 : Blo 1344991 3028049 := bstep (se 2 (by rfl) ⟨1135518, by rfl⟩ : syracuseStep 3028049 = 2271037) B2271037
theorem B2020433 : Blo 1344991 2020433 := bstep (se 2 (by rfl) ⟨757662, by rfl⟩ : syracuseStep 2020433 = 1515325) B1515325
theorem B3028067 : Blo 1344991 3028067 := bstep (se 1 (by rfl) ⟨2271050, by rfl⟩ : syracuseStep 3028067 = 4542101) B4542101
theorem B2020451 : Blo 1344991 2020451 := bstep (se 1 (by rfl) ⟨1515338, by rfl⟩ : syracuseStep 2020451 = 3030677) B3030677
theorem B2020481 : Blo 1344991 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B7664867 : Blo 1344991 7664867 := bstep (se 1 (by rfl) ⟨5748650, by rfl⟩ : syracuseStep 7664867 = 11497301) B11497301
theorem B6911281 : Blo 1344991 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B6468941 : Blo 1344991 6468941 := bstep (se 3 (by rfl) ⟨1212926, by rfl⟩ : syracuseStep 6468941 = 2425853) B2425853
theorem B9696611 : Blo 1344991 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B3028337 : Blo 1344991 3028337 := bstep (se 2 (by rfl) ⟨1135626, by rfl⟩ : syracuseStep 3028337 = 2271253) B2271253
theorem B3028355 : Blo 1344991 3028355 := bstep (se 1 (by rfl) ⟨2271266, by rfl⟩ : syracuseStep 3028355 = 4542533) B4542533
theorem B7001585 : Blo 1344991 7001585 := bstep (se 2 (by rfl) ⟨2625594, by rfl⟩ : syracuseStep 7001585 = 5251189) B5251189
theorem B12932621 : Blo 1344991 12932621 := bstep (se 3 (by rfl) ⟨2424866, by rfl⟩ : syracuseStep 12932621 = 4849733) B4849733
theorem B4544045 : Blo 1344991 4544045 := bstep (se 3 (by rfl) ⟨852008, by rfl⟩ : syracuseStep 4544045 = 1704017) B1704017
theorem B4601393 : Blo 1344991 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B3405361 : Blo 1344991 3405361 := bstep (se 2 (by rfl) ⟨1277010, by rfl⟩ : syracuseStep 3405361 = 2554021) B2554021
theorem B6813233 : Blo 1344991 6813233 := bstep (se 2 (by rfl) ⟨2554962, by rfl⟩ : syracuseStep 6813233 = 5109925) B5109925
theorem B4544099 : Blo 1344991 4544099 := bstep (se 1 (by rfl) ⟨3408074, by rfl⟩ : syracuseStep 4544099 = 6816149) B6816149
theorem B12285553 : Blo 1344991 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B1726067 : Blo 1344991 1726067 := bstep (se 1 (by rfl) ⟨1294550, by rfl⟩ : syracuseStep 1726067 = 2589101) B2589101
theorem B3028625 : Blo 1344991 3028625 := bstep (se 2 (by rfl) ⟨1135734, by rfl⟩ : syracuseStep 3028625 = 2271469) B2271469
theorem B3028643 : Blo 1344991 3028643 := bstep (se 1 (by rfl) ⟨2271482, by rfl⟩ : syracuseStep 3028643 = 4542965) B4542965
theorem B5109425 : Blo 1344991 5109425 := bstep (se 2 (by rfl) ⟨1916034, by rfl⟩ : syracuseStep 5109425 = 3832069) B3832069
theorem B4314833 : Blo 1344991 4314833 := bstep (se 2 (by rfl) ⟨1618062, by rfl⟩ : syracuseStep 4314833 = 3236125) B3236125
theorem B3831533 : Blo 1344991 3831533 := bstep (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) B1436825
theorem B1513219 : Blo 1344991 1513219 := bstep (se 1 (by rfl) ⟨1134914, by rfl⟩ : syracuseStep 1513219 = 2269829) B2269829
theorem B4314883 : Blo 1344991 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B7272197 : Blo 1344991 7272197 := bstep (se 4 (by rfl) ⟨681768, by rfl⟩ : syracuseStep 7272197 = 1363537) B1363537
theorem B5748515 : Blo 1344991 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B5183281 : Blo 1344991 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B3405635 : Blo 1344991 3405635 := bstep (se 1 (by rfl) ⟨2554226, by rfl⟩ : syracuseStep 3405635 = 5108453) B5108453
theorem B6739789 : Blo 1344991 6739789 := bstep (se 3 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 6739789 = 2527421) B2527421
theorem B4544369 : Blo 1344991 4544369 := bstep (se 2 (by rfl) ⟨1704138, by rfl⟩ : syracuseStep 4544369 = 3408277) B3408277
theorem B1513363 : Blo 1344991 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B2553763 : Blo 1344991 2553763 := bstep (se 1 (by rfl) ⟨1915322, by rfl⟩ : syracuseStep 2553763 = 3830645) B3830645
theorem B3831715 : Blo 1344991 3831715 := bstep (se 1 (by rfl) ⟨2873786, by rfl⟩ : syracuseStep 3831715 = 5747573) B5747573
theorem B3028913 : Blo 1344991 3028913 := bstep (se 2 (by rfl) ⟨1135842, by rfl⟩ : syracuseStep 3028913 = 2271685) B2271685
theorem B3028931 : Blo 1344991 3028931 := bstep (se 1 (by rfl) ⟨2271698, by rfl⟩ : syracuseStep 3028931 = 4543397) B4543397
theorem B21010373 : Blo 1344991 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B6141901 : Blo 1344991 6141901 := bstep (se 3 (by rfl) ⟨1151606, by rfl⟩ : syracuseStep 6141901 = 2303213) B2303213
theorem B3831761 : Blo 1344991 3831761 := bstep (se 2 (by rfl) ⟨1436910, by rfl⟩ : syracuseStep 3831761 = 2873821) B2873821
theorem B3405827 : Blo 1344991 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B1513507 : Blo 1344991 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B7280675 : Blo 1344991 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B2553923 : Blo 1344991 2553923 := bstep (se 1 (by rfl) ⟨1915442, by rfl⟩ : syracuseStep 2553923 = 3830885) B3830885
theorem B2873411 : Blo 1344991 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B2046097 : Blo 1344991 2046097 := bstep (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) B1534573
theorem B1513651 : Blo 1344991 1513651 := bstep (se 1 (by rfl) ⟨1135238, by rfl⟩ : syracuseStep 1513651 = 2270477) B2270477
theorem B8624333 : Blo 1344991 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B3029201 : Blo 1344991 3029201 := bstep (se 2 (by rfl) ⟨1135950, by rfl⟩ : syracuseStep 3029201 = 2271901) B2271901
theorem B3029219 : Blo 1344991 3029219 := bstep (se 1 (by rfl) ⟨2271914, by rfl⟩ : syracuseStep 3029219 = 4543829) B4543829
theorem B6142193 : Blo 1344991 6142193 := bstep (se 2 (by rfl) ⟨2303322, by rfl⟩ : syracuseStep 6142193 = 4606645) B4606645
theorem B1513795 : Blo 1344991 1513795 := bstep (se 1 (by rfl) ⟨1135346, by rfl⟩ : syracuseStep 1513795 = 2270693) B2270693
theorem B4544909 : Blo 1344991 4544909 := bstep (se 3 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 4544909 = 1704341) B1704341
theorem B1702291 : Blo 1344991 1702291 := bstep (se 1 (by rfl) ⟨1276718, by rfl⟩ : syracuseStep 1702291 = 2553437) B2553437
theorem B4544963 : Blo 1344991 4544963 := bstep (se 1 (by rfl) ⟨3408722, by rfl⟩ : syracuseStep 4544963 = 6817445) B6817445
theorem B1513939 : Blo 1344991 1513939 := bstep (se 1 (by rfl) ⟨1135454, by rfl⟩ : syracuseStep 1513939 = 2270909) B2270909
theorem B3029489 : Blo 1344991 3029489 := bstep (se 2 (by rfl) ⟨1136058, by rfl⟩ : syracuseStep 3029489 = 2272117) B2272117
theorem B1702387 : Blo 1344991 1702387 := bstep (se 1 (by rfl) ⟨1276790, by rfl⟩ : syracuseStep 1702387 = 2553581) B2553581
theorem B3029507 : Blo 1344991 3029507 := bstep (se 1 (by rfl) ⟨2272130, by rfl⟩ : syracuseStep 3029507 = 4544261) B4544261
theorem B2873873 : Blo 1344991 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1514083 : Blo 1344991 1514083 := bstep (se 1 (by rfl) ⟨1135562, by rfl⟩ : syracuseStep 1514083 = 2271125) B2271125
theorem B8190563 : Blo 1344991 8190563 := bstep (se 1 (by rfl) ⟨6142922, by rfl⟩ : syracuseStep 8190563 = 12285845) B12285845
theorem B2767459 : Blo 1344991 2767459 := bstep (se 1 (by rfl) ⟨2075594, by rfl⟩ : syracuseStep 2767459 = 4151189) B4151189
theorem B4913869 : Blo 1344991 4913869 := bstep (se 3 (by rfl) ⟨921350, by rfl⟩ : syracuseStep 4913869 = 1842701) B1842701
theorem B4545233 : Blo 1344991 4545233 := bstep (se 2 (by rfl) ⟨1704462, by rfl⟩ : syracuseStep 4545233 = 3408925) B3408925
theorem B1514227 : Blo 1344991 1514227 := bstep (se 1 (by rfl) ⟨1135670, by rfl⟩ : syracuseStep 1514227 = 2271341) B2271341
theorem B7281413 : Blo 1344991 7281413 := bstep (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) B1365265
theorem B3029777 : Blo 1344991 3029777 := bstep (se 2 (by rfl) ⟨1136166, by rfl⟩ : syracuseStep 3029777 = 2272333) B2272333
theorem B6552355 : Blo 1344991 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B3029795 : Blo 1344991 3029795 := bstep (se 1 (by rfl) ⟨2272346, by rfl⟩ : syracuseStep 3029795 = 4544693) B4544693
theorem B13998917 : Blo 1344991 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B1514371 : Blo 1344991 1514371 := bstep (se 1 (by rfl) ⟨1135778, by rfl⟩ : syracuseStep 1514371 = 2271557) B2271557
theorem B3406769 : Blo 1344991 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B15342533 : Blo 1344991 15342533 := bstep (se 4 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 15342533 = 2876725) B2876725
theorem B1702883 : Blo 1344991 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B3406819 : Blo 1344991 3406819 := bstep (se 1 (by rfl) ⟨2555114, by rfl⟩ : syracuseStep 3406819 = 5110229) B5110229
theorem B6814691 : Blo 1344991 6814691 := bstep (se 1 (by rfl) ⟨5111018, by rfl⟩ : syracuseStep 6814691 = 10222037) B10222037
theorem B1514515 : Blo 1344991 1514515 := bstep (se 1 (by rfl) ⟨1135886, by rfl⟩ : syracuseStep 1514515 = 2271773) B2271773
theorem B3030065 : Blo 1344991 3030065 := bstep (se 2 (by rfl) ⟨1136274, by rfl⟩ : syracuseStep 3030065 = 2272549) B2272549
theorem B3030083 : Blo 1344991 3030083 := bstep (se 1 (by rfl) ⟨2272562, by rfl⟩ : syracuseStep 3030083 = 4545125) B4545125
theorem B7666757 : Blo 1344991 7666757 := bstep (se 4 (by rfl) ⟨718758, by rfl⟩ : syracuseStep 7666757 = 1437517) B1437517
theorem B11500613 : Blo 1344991 11500613 := bstep (se 4 (by rfl) ⟨1078182, by rfl⟩ : syracuseStep 11500613 = 2156365) B2156365
theorem B5110883 : Blo 1344991 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B2554993 : Blo 1344991 2554993 := bstep (se 2 (by rfl) ⟨958122, by rfl⟩ : syracuseStep 2554993 = 1916245) B1916245
theorem B3406961 : Blo 1344991 3406961 := bstep (se 2 (by rfl) ⟨1277610, by rfl⟩ : syracuseStep 3406961 = 2555221) B2555221
theorem B5110897 : Blo 1344991 5110897 := bstep (se 2 (by rfl) ⟨1916586, by rfl⟩ : syracuseStep 5110897 = 3833173) B3833173
theorem B1514659 : Blo 1344991 1514659 := bstep (se 1 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 1514659 = 2271989) B2271989
theorem B3071171 : Blo 1344991 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B11492549 : Blo 1344991 11492549 := bstep (se 4 (by rfl) ⟨1077426, by rfl⟩ : syracuseStep 11492549 = 2154853) B2154853
theorem B22994117 : Blo 1344991 22994117 := bstep (se 4 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 22994117 = 4311397) B4311397
theorem B1916131 : Blo 1344991 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B4545773 : Blo 1344991 4545773 := bstep (se 3 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 4545773 = 1704665) B1704665
theorem B4545827 : Blo 1344991 4545827 := bstep (se 1 (by rfl) ⟨3409370, by rfl⟩ : syracuseStep 4545827 = 6818741) B6818741
theorem B1514803 : Blo 1344991 1514803 := bstep (se 1 (by rfl) ⟨1136102, by rfl⟩ : syracuseStep 1514803 = 2272205) B2272205
theorem B6561101 : Blo 1344991 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B3030353 : Blo 1344991 3030353 := bstep (se 2 (by rfl) ⟨1136382, by rfl⟩ : syracuseStep 3030353 = 2272765) B2272765
theorem B3030371 : Blo 1344991 3030371 := bstep (se 1 (by rfl) ⟨2272778, by rfl⟩ : syracuseStep 3030371 = 4545557) B4545557
theorem B3833219 : Blo 1344991 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B1514947 : Blo 1344991 1514947 := bstep (se 1 (by rfl) ⟨1136210, by rfl⟩ : syracuseStep 1514947 = 2272421) B2272421
theorem B2047441 : Blo 1344991 2047441 := bstep (se 2 (by rfl) ⟨767790, by rfl⟩ : syracuseStep 2047441 = 1535581) B1535581
theorem B4546097 : Blo 1344991 4546097 := bstep (se 2 (by rfl) ⟨1704786, by rfl⟩ : syracuseStep 4546097 = 3409573) B3409573
theorem B1515091 : Blo 1344991 1515091 := bstep (se 1 (by rfl) ⟨1136318, by rfl⟩ : syracuseStep 1515091 = 2272637) B2272637
theorem B7274083 : Blo 1344991 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B3030641 : Blo 1344991 3030641 := bstep (se 2 (by rfl) ⟨1136490, by rfl⟩ : syracuseStep 3030641 = 2272981) B2272981
theorem B2301571 : Blo 1344991 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3030659 : Blo 1344991 3030659 := bstep (se 1 (by rfl) ⟨2272994, by rfl⟩ : syracuseStep 3030659 = 4545989) B4545989
theorem B2334353 : Blo 1344991 2334353 := bstep (se 2 (by rfl) ⟨875382, by rfl⟩ : syracuseStep 2334353 = 1750765) B1750765
theorem B1703587 : Blo 1344991 1703587 := bstep (se 1 (by rfl) ⟨1277690, by rfl⟩ : syracuseStep 1703587 = 2555381) B2555381
theorem B2334433 : Blo 1344991 2334433 := bstep (se 2 (by rfl) ⟨875412, by rfl⟩ : syracuseStep 2334433 = 1750825) B1750825
theorem B1515235 : Blo 1344991 1515235 := bstep (se 1 (by rfl) ⟨1136426, by rfl⟩ : syracuseStep 1515235 = 2272853) B2272853
theorem B5750513 : Blo 1344991 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B11501297 : Blo 1344991 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B1703683 : Blo 1344991 1703683 := bstep (se 1 (by rfl) ⟨1277762, by rfl⟩ : syracuseStep 1703683 = 2555525) B2555525
theorem B6815501 : Blo 1344991 6815501 := bstep (se 3 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 6815501 = 2555813) B2555813
theorem B2047763 : Blo 1344991 2047763 := bstep (se 1 (by rfl) ⟨1535822, by rfl⟩ : syracuseStep 2047763 = 3071645) B3071645
theorem B2875171 : Blo 1344991 2875171 := bstep (se 1 (by rfl) ⟨2156378, by rfl⟩ : syracuseStep 2875171 = 4312757) B4312757
theorem B17252149 : Blo 1344991 17252149 := bstep (se 5 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 17252149 = 1617389) B1617389
theorem B4308835 : Blo 1344991 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B1916951 : Blo 1344991 1916951 := bstep (se 1 (by rfl) ⟨1437713, by rfl⟩ : syracuseStep 1916951 = 2875427) B2875427
theorem B52428941 : Blo 1344991 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B2728129 : Blo 1344991 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B3408065 : Blo 1344991 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B1917145 : Blo 1344991 1917145 := bstep (se 2 (by rfl) ⟨718929, by rfl⟩ : syracuseStep 1917145 = 1437859) B1437859
theorem B4309271 : Blo 1344991 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B6472001 : Blo 1344991 6472001 := bstep (se 2 (by rfl) ⟨2427000, by rfl⟩ : syracuseStep 6472001 = 4854001) B4854001
theorem B2556299 : Blo 1344991 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B1704331 : Blo 1344991 1704331 := bstep (se 1 (by rfl) ⟨1278248, by rfl⟩ : syracuseStep 1704331 = 2556497) B2556497
theorem B3686849 : Blo 1344991 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B2556353 : Blo 1344991 2556353 := bstep (se 2 (by rfl) ⟨958632, by rfl⟩ : syracuseStep 2556353 = 1917265) B1917265
theorem B6472153 : Blo 1344991 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B2269721 : Blo 1344991 2269721 := bstep (se 2 (by rfl) ⟨851145, by rfl⟩ : syracuseStep 2269721 = 1702291) B1702291
theorem B2269849 : Blo 1344991 2269849 := bstep (se 2 (by rfl) ⟨851193, by rfl⟩ : syracuseStep 2269849 = 1702387) B1702387
theorem B6816473 : Blo 1344991 6816473 := bstep (se 2 (by rfl) ⟨2556177, by rfl⟩ : syracuseStep 6816473 = 5112355) B5112355
theorem B3408601 : Blo 1344991 3408601 := bstep (se 2 (by rfl) ⟨1278225, by rfl⟩ : syracuseStep 3408601 = 2556451) B2556451
theorem B59007797 : Blo 1344991 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B12936037 : Blo 1344991 12936037 := bstep (se 4 (by rfl) ⟨1212753, by rfl⟩ : syracuseStep 12936037 = 2425507) B2425507
theorem B1819531 : Blo 1344991 1819531 := bstep (se 1 (by rfl) ⟨1364648, by rfl⟩ : syracuseStep 1819531 = 2729297) B2729297
theorem B6464407 : Blo 1344991 6464407 := bstep (se 1 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 6464407 = 9696611) B9696611
theorem B1442711 : Blo 1344991 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B3834803 : Blo 1344991 3834803 := bstep (se 1 (by rfl) ⟨2876102, by rfl⟩ : syracuseStep 3834803 = 5752205) B5752205
theorem B16376849 : Blo 1344991 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B2876555 : Blo 1344991 2876555 := bstep (se 1 (by rfl) ⟨2157416, by rfl⟩ : syracuseStep 2876555 = 4314833) B4314833
theorem B4310167 : Blo 1344991 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B2270423 : Blo 1344991 2270423 := bstep (se 1 (by rfl) ⟨1702817, by rfl⟩ : syracuseStep 2270423 = 3405635) B3405635
theorem B4539671 : Blo 1344991 4539671 := bstep (se 1 (by rfl) ⟨3404753, by rfl⟩ : syracuseStep 4539671 = 6809507) B6809507
theorem B3835201 : Blo 1344991 3835201 := bstep (se 2 (by rfl) ⟨1438200, by rfl⟩ : syracuseStep 3835201 = 2876401) B2876401
theorem B3884363 : Blo 1344991 3884363 := bstep (se 1 (by rfl) ⟨2913272, by rfl⟩ : syracuseStep 3884363 = 5826545) B5826545
theorem B2270551 : Blo 1344991 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B4851161 : Blo 1344991 4851161 := bstep (se 2 (by rfl) ⟨1819185, by rfl⟩ : syracuseStep 4851161 = 3638371) B3638371
theorem B1345003 : Blo 1344991 1345003 := bstep (se 1 (by rfl) ⟨1008752, by rfl⟩ : syracuseStep 1345003 = 2017505) B2017505
theorem B1345015 : Blo 1344991 1345015 := bstep (se 1 (by rfl) ⟨1008761, by rfl⟩ : syracuseStep 1345015 = 2017523) B2017523
theorem B1345035 : Blo 1344991 1345035 := bstep (se 1 (by rfl) ⟨1008776, by rfl⟩ : syracuseStep 1345035 = 2017553) B2017553
theorem B1345047 : Blo 1344991 1345047 := bstep (se 1 (by rfl) ⟨1008785, by rfl⟩ : syracuseStep 1345047 = 2017571) B2017571
theorem B1345067 : Blo 1344991 1345067 := bstep (se 1 (by rfl) ⟨1008800, by rfl⟩ : syracuseStep 1345067 = 2017601) B2017601
theorem B1345079 : Blo 1344991 1345079 := bstep (se 1 (by rfl) ⟨1008809, by rfl⟩ : syracuseStep 1345079 = 2017619) B2017619
theorem B1345099 : Blo 1344991 1345099 := bstep (se 1 (by rfl) ⟨1008824, by rfl⟩ : syracuseStep 1345099 = 2017649) B2017649
theorem B1345111 : Blo 1344991 1345111 := bstep (se 1 (by rfl) ⟨1008833, by rfl⟩ : syracuseStep 1345111 = 2017667) B2017667
theorem B21841501 : Blo 1344991 21841501 := bstep (se 3 (by rfl) ⟨4095281, by rfl⟩ : syracuseStep 21841501 = 8190563) B8190563
theorem B1345131 : Blo 1344991 1345131 := bstep (se 1 (by rfl) ⟨1008848, by rfl⟩ : syracuseStep 1345131 = 2017697) B2017697
theorem B1345143 : Blo 1344991 1345143 := bstep (se 1 (by rfl) ⟨1008857, by rfl⟩ : syracuseStep 1345143 = 2017715) B2017715
theorem B1345163 : Blo 1344991 1345163 := bstep (se 1 (by rfl) ⟨1008872, by rfl⟩ : syracuseStep 1345163 = 2017745) B2017745
theorem B1345175 : Blo 1344991 1345175 := bstep (se 1 (by rfl) ⟨1008881, by rfl⟩ : syracuseStep 1345175 = 2017763) B2017763
theorem B1345195 : Blo 1344991 1345195 := bstep (se 1 (by rfl) ⟨1008896, by rfl⟩ : syracuseStep 1345195 = 2017793) B2017793
theorem B1345207 : Blo 1344991 1345207 := bstep (se 1 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 1345207 = 2017811) B2017811
theorem B1345227 : Blo 1344991 1345227 := bstep (se 1 (by rfl) ⟨1008920, by rfl⟩ : syracuseStep 1345227 = 2017841) B2017841
theorem B1345239 : Blo 1344991 1345239 := bstep (se 1 (by rfl) ⟨1008929, by rfl⟩ : syracuseStep 1345239 = 2017859) B2017859
theorem B10217177 : Blo 1344991 10217177 := bstep (se 2 (by rfl) ⟨3831441, by rfl⟩ : syracuseStep 10217177 = 7662883) B7662883
theorem B1345259 : Blo 1344991 1345259 := bstep (se 1 (by rfl) ⟨1008944, by rfl⟩ : syracuseStep 1345259 = 2017889) B2017889
theorem B1345271 : Blo 1344991 1345271 := bstep (se 1 (by rfl) ⟨1008953, by rfl⟩ : syracuseStep 1345271 = 2017907) B2017907
theorem B1345291 : Blo 1344991 1345291 := bstep (se 1 (by rfl) ⟨1008968, by rfl⟩ : syracuseStep 1345291 = 2017937) B2017937
theorem B1345303 : Blo 1344991 1345303 := bstep (se 1 (by rfl) ⟨1008977, by rfl⟩ : syracuseStep 1345303 = 2017955) B2017955
theorem B1345323 : Blo 1344991 1345323 := bstep (se 1 (by rfl) ⟨1008992, by rfl⟩ : syracuseStep 1345323 = 2017985) B2017985
theorem B4540211 : Blo 1344991 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B1345335 : Blo 1344991 1345335 := bstep (se 1 (by rfl) ⟨1009001, by rfl⟩ : syracuseStep 1345335 = 2018003) B2018003
theorem B1345355 : Blo 1344991 1345355 := bstep (se 1 (by rfl) ⟨1009016, by rfl⟩ : syracuseStep 1345355 = 2018033) B2018033
theorem B1345367 : Blo 1344991 1345367 := bstep (se 1 (by rfl) ⟨1009025, by rfl⟩ : syracuseStep 1345367 = 2018051) B2018051
theorem B1345387 : Blo 1344991 1345387 := bstep (se 1 (by rfl) ⟨1009040, by rfl⟩ : syracuseStep 1345387 = 2018081) B2018081
theorem B1345399 : Blo 1344991 1345399 := bstep (se 1 (by rfl) ⟨1009049, by rfl⟩ : syracuseStep 1345399 = 2018099) B2018099
theorem B1345419 : Blo 1344991 1345419 := bstep (se 1 (by rfl) ⟨1009064, by rfl⟩ : syracuseStep 1345419 = 2018129) B2018129
theorem B1345431 : Blo 1344991 1345431 := bstep (se 1 (by rfl) ⟨1009073, by rfl⟩ : syracuseStep 1345431 = 2018147) B2018147
theorem B1345451 : Blo 1344991 1345451 := bstep (se 1 (by rfl) ⟨1009088, by rfl⟩ : syracuseStep 1345451 = 2018177) B2018177
theorem B1345463 : Blo 1344991 1345463 := bstep (se 1 (by rfl) ⟨1009097, by rfl⟩ : syracuseStep 1345463 = 2018195) B2018195
theorem B2729921 : Blo 1344991 2729921 := bstep (se 2 (by rfl) ⟨1023720, by rfl⟩ : syracuseStep 2729921 = 2047441) B2047441
theorem B1345483 : Blo 1344991 1345483 := bstep (se 1 (by rfl) ⟨1009112, by rfl⟩ : syracuseStep 1345483 = 2018225) B2018225
theorem B4310987 : Blo 1344991 4310987 := bstep (se 1 (by rfl) ⟨3233240, by rfl⟩ : syracuseStep 4310987 = 6466481) B6466481
theorem B2271179 : Blo 1344991 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B1345495 : Blo 1344991 1345495 := bstep (se 1 (by rfl) ⟨1009121, by rfl⟩ : syracuseStep 1345495 = 2018243) B2018243
theorem B1345515 : Blo 1344991 1345515 := bstep (se 1 (by rfl) ⟨1009136, by rfl⟩ : syracuseStep 1345515 = 2018273) B2018273
theorem B1345527 : Blo 1344991 1345527 := bstep (se 1 (by rfl) ⟨1009145, by rfl⟩ : syracuseStep 1345527 = 2018291) B2018291
theorem B1345547 : Blo 1344991 1345547 := bstep (se 1 (by rfl) ⟨1009160, by rfl⟩ : syracuseStep 1345547 = 2018321) B2018321
theorem B8185873 : Blo 1344991 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B1345559 : Blo 1344991 1345559 := bstep (se 1 (by rfl) ⟨1009169, by rfl⟩ : syracuseStep 1345559 = 2018339) B2018339
theorem B1345579 : Blo 1344991 1345579 := bstep (se 1 (by rfl) ⟨1009184, by rfl⟩ : syracuseStep 1345579 = 2018369) B2018369
theorem B1345591 : Blo 1344991 1345591 := bstep (se 1 (by rfl) ⟨1009193, by rfl⟩ : syracuseStep 1345591 = 2018387) B2018387
theorem B4540481 : Blo 1344991 4540481 := bstep (se 2 (by rfl) ⟨1702680, by rfl⟩ : syracuseStep 4540481 = 3405361) B3405361
theorem B1345611 : Blo 1344991 1345611 := bstep (se 1 (by rfl) ⟨1009208, by rfl⟩ : syracuseStep 1345611 = 2018417) B2018417
theorem B2271307 : Blo 1344991 2271307 := bstep (se 1 (by rfl) ⟨1703480, by rfl⟩ : syracuseStep 2271307 = 3406961) B3406961
theorem B1345623 : Blo 1344991 1345623 := bstep (se 1 (by rfl) ⟨1009217, by rfl⟩ : syracuseStep 1345623 = 2018435) B2018435
theorem B1345643 : Blo 1344991 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B1345655 : Blo 1344991 1345655 := bstep (se 1 (by rfl) ⟨1009241, by rfl⟩ : syracuseStep 1345655 = 2018483) B2018483
theorem B7661699 : Blo 1344991 7661699 := bstep (se 1 (by rfl) ⟨5746274, by rfl⟩ : syracuseStep 7661699 = 11492549) B11492549
theorem B15329411 : Blo 1344991 15329411 := bstep (se 1 (by rfl) ⟨11497058, by rfl⟩ : syracuseStep 15329411 = 22994117) B22994117
theorem B1345675 : Blo 1344991 1345675 := bstep (se 1 (by rfl) ⟨1009256, by rfl⟩ : syracuseStep 1345675 = 2018513) B2018513
theorem B1345687 : Blo 1344991 1345687 := bstep (se 1 (by rfl) ⟨1009265, by rfl⟩ : syracuseStep 1345687 = 2018531) B2018531
theorem B1345707 : Blo 1344991 1345707 := bstep (se 1 (by rfl) ⟨1009280, by rfl⟩ : syracuseStep 1345707 = 2018561) B2018561
theorem B1345719 : Blo 1344991 1345719 := bstep (se 1 (by rfl) ⟨1009289, by rfl⟩ : syracuseStep 1345719 = 2018579) B2018579
theorem B1345739 : Blo 1344991 1345739 := bstep (se 1 (by rfl) ⟨1009304, by rfl⟩ : syracuseStep 1345739 = 2018609) B2018609
theorem B1345751 : Blo 1344991 1345751 := bstep (se 1 (by rfl) ⟨1009313, by rfl⟩ : syracuseStep 1345751 = 2018627) B2018627
theorem B2271449 : Blo 1344991 2271449 := bstep (se 2 (by rfl) ⟨851793, by rfl⟩ : syracuseStep 2271449 = 1703587) B1703587
theorem B1345771 : Blo 1344991 1345771 := bstep (se 1 (by rfl) ⟨1009328, by rfl⟩ : syracuseStep 1345771 = 2018657) B2018657
theorem B1345783 : Blo 1344991 1345783 := bstep (se 1 (by rfl) ⟨1009337, by rfl⟩ : syracuseStep 1345783 = 2018675) B2018675
theorem B10225925 : Blo 1344991 10225925 := bstep (se 4 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 10225925 = 1917361) B1917361
theorem B2017547 : Blo 1344991 2017547 := bstep (se 1 (by rfl) ⟨1513160, by rfl⟩ : syracuseStep 2017547 = 3026321) B3026321
theorem B1345803 : Blo 1344991 1345803 := bstep (se 1 (by rfl) ⟨1009352, by rfl⟩ : syracuseStep 1345803 = 2018705) B2018705
theorem B2017559 : Blo 1344991 2017559 := bstep (se 1 (by rfl) ⟨1513169, by rfl⟩ : syracuseStep 2017559 = 3026339) B3026339
theorem B1345815 : Blo 1344991 1345815 := bstep (se 1 (by rfl) ⟨1009361, by rfl⟩ : syracuseStep 1345815 = 2018723) B2018723
theorem B1345835 : Blo 1344991 1345835 := bstep (se 1 (by rfl) ⟨1009376, by rfl⟩ : syracuseStep 1345835 = 2018753) B2018753
theorem B46631213 : Blo 1344991 46631213 := bstep (se 3 (by rfl) ⟨8743352, by rfl⟩ : syracuseStep 46631213 = 17486705) B17486705
theorem B6818093 : Blo 1344991 6818093 := bstep (se 3 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 6818093 = 2556785) B2556785
theorem B1345847 : Blo 1344991 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B1345867 : Blo 1344991 1345867 := bstep (se 1 (by rfl) ⟨1009400, by rfl⟩ : syracuseStep 1345867 = 2018801) B2018801
theorem B1345879 : Blo 1344991 1345879 := bstep (se 1 (by rfl) ⟨1009409, by rfl⟩ : syracuseStep 1345879 = 2018819) B2018819
theorem B2017625 : Blo 1344991 2017625 := bstep (se 2 (by rfl) ⟨756609, by rfl⟩ : syracuseStep 2017625 = 1513219) B1513219
theorem B2271577 : Blo 1344991 2271577 := bstep (se 2 (by rfl) ⟨851841, by rfl⟩ : syracuseStep 2271577 = 1703683) B1703683
theorem B5753177 : Blo 1344991 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B19401059 : Blo 1344991 19401059 := bstep (se 1 (by rfl) ⟨14550794, by rfl⟩ : syracuseStep 19401059 = 29101589) B29101589
theorem B1345899 : Blo 1344991 1345899 := bstep (se 1 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 1345899 = 2018849) B2018849
theorem B1345911 : Blo 1344991 1345911 := bstep (se 1 (by rfl) ⟨1009433, by rfl⟩ : syracuseStep 1345911 = 2018867) B2018867
theorem B1345931 : Blo 1344991 1345931 := bstep (se 1 (by rfl) ⟨1009448, by rfl⟩ : syracuseStep 1345931 = 2018897) B2018897
theorem B5179799 : Blo 1344991 5179799 := bstep (se 1 (by rfl) ⟨3884849, by rfl⟩ : syracuseStep 5179799 = 7769699) B7769699
theorem B1345943 : Blo 1344991 1345943 := bstep (se 1 (by rfl) ⟨1009457, by rfl⟩ : syracuseStep 1345943 = 2018915) B2018915
theorem B1345963 : Blo 1344991 1345963 := bstep (se 1 (by rfl) ⟨1009472, by rfl⟩ : syracuseStep 1345963 = 2018945) B2018945
theorem B5114285 : Blo 1344991 5114285 := bstep (se 3 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 5114285 = 1917857) B1917857
theorem B1345975 : Blo 1344991 1345975 := bstep (se 1 (by rfl) ⟨1009481, by rfl⟩ : syracuseStep 1345975 = 2018963) B2018963
theorem B2017739 : Blo 1344991 2017739 := bstep (se 1 (by rfl) ⟨1513304, by rfl⟩ : syracuseStep 2017739 = 3026609) B3026609
theorem B1345995 : Blo 1344991 1345995 := bstep (se 1 (by rfl) ⟨1009496, by rfl⟩ : syracuseStep 1345995 = 2018993) B2018993
theorem B2017751 : Blo 1344991 2017751 := bstep (se 1 (by rfl) ⟨1513313, by rfl⟩ : syracuseStep 2017751 = 3026627) B3026627
theorem B1346007 : Blo 1344991 1346007 := bstep (se 1 (by rfl) ⟨1009505, by rfl⟩ : syracuseStep 1346007 = 2019011) B2019011
theorem B5745113 : Blo 1344991 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B1346027 : Blo 1344991 1346027 := bstep (se 1 (by rfl) ⟨1009520, by rfl⟩ : syracuseStep 1346027 = 2019041) B2019041
theorem B1346039 : Blo 1344991 1346039 := bstep (se 1 (by rfl) ⟨1009529, by rfl⟩ : syracuseStep 1346039 = 2019059) B2019059
theorem B1346059 : Blo 1344991 1346059 := bstep (se 1 (by rfl) ⟨1009544, by rfl⟩ : syracuseStep 1346059 = 2019089) B2019089
theorem B1346071 : Blo 1344991 1346071 := bstep (se 1 (by rfl) ⟨1009553, by rfl⟩ : syracuseStep 1346071 = 2019107) B2019107
theorem B2017817 : Blo 1344991 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B1346091 : Blo 1344991 1346091 := bstep (se 1 (by rfl) ⟨1009568, by rfl⟩ : syracuseStep 1346091 = 2019137) B2019137
theorem B1346103 : Blo 1344991 1346103 := bstep (se 1 (by rfl) ⟨1009577, by rfl⟩ : syracuseStep 1346103 = 2019155) B2019155
theorem B1346123 : Blo 1344991 1346123 := bstep (se 1 (by rfl) ⟨1009592, by rfl⟩ : syracuseStep 1346123 = 2019185) B2019185
theorem B1346135 : Blo 1344991 1346135 := bstep (se 1 (by rfl) ⟨1009601, by rfl⟩ : syracuseStep 1346135 = 2019203) B2019203
theorem B4541021 : Blo 1344991 4541021 := bstep (se 3 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 4541021 = 1702883) B1702883
theorem B1346155 : Blo 1344991 1346155 := bstep (se 1 (by rfl) ⟨1009616, by rfl⟩ : syracuseStep 1346155 = 2019233) B2019233
theorem B1346167 : Blo 1344991 1346167 := bstep (se 1 (by rfl) ⟨1009625, by rfl⟩ : syracuseStep 1346167 = 2019251) B2019251
theorem B2017931 : Blo 1344991 2017931 := bstep (se 1 (by rfl) ⟨1513448, by rfl⟩ : syracuseStep 2017931 = 3026897) B3026897
theorem B1346187 : Blo 1344991 1346187 := bstep (se 1 (by rfl) ⟨1009640, by rfl⟩ : syracuseStep 1346187 = 2019281) B2019281
theorem B2017943 : Blo 1344991 2017943 := bstep (se 1 (by rfl) ⟨1513457, by rfl⟩ : syracuseStep 2017943 = 3026915) B3026915
theorem B1346199 : Blo 1344991 1346199 := bstep (se 1 (by rfl) ⟨1009649, by rfl⟩ : syracuseStep 1346199 = 2019299) B2019299
theorem B1346219 : Blo 1344991 1346219 := bstep (se 1 (by rfl) ⟨1009664, by rfl⟩ : syracuseStep 1346219 = 2019329) B2019329
theorem B4311731 : Blo 1344991 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B1346231 : Blo 1344991 1346231 := bstep (se 1 (by rfl) ⟨1009673, by rfl⟩ : syracuseStep 1346231 = 2019347) B2019347
theorem B1346251 : Blo 1344991 1346251 := bstep (se 1 (by rfl) ⟨1009688, by rfl⟩ : syracuseStep 1346251 = 2019377) B2019377
theorem B1346263 : Blo 1344991 1346263 := bstep (se 1 (by rfl) ⟨1009697, by rfl⟩ : syracuseStep 1346263 = 2019395) B2019395
theorem B2018009 : Blo 1344991 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B1346283 : Blo 1344991 1346283 := bstep (se 1 (by rfl) ⟨1009712, by rfl⟩ : syracuseStep 1346283 = 2019425) B2019425
theorem B1346295 : Blo 1344991 1346295 := bstep (se 1 (by rfl) ⟨1009721, by rfl⟩ : syracuseStep 1346295 = 2019443) B2019443
theorem B16583429 : Blo 1344991 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B1346315 : Blo 1344991 1346315 := bstep (se 1 (by rfl) ⟨1009736, by rfl⟩ : syracuseStep 1346315 = 2019473) B2019473
theorem B1346327 : Blo 1344991 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1346347 : Blo 1344991 1346347 := bstep (se 1 (by rfl) ⟨1009760, by rfl⟩ : syracuseStep 1346347 = 2019521) B2019521
theorem B1346359 : Blo 1344991 1346359 := bstep (se 1 (by rfl) ⟨1009769, by rfl⟩ : syracuseStep 1346359 = 2019539) B2019539
theorem B2018123 : Blo 1344991 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B1346379 : Blo 1344991 1346379 := bstep (se 1 (by rfl) ⟨1009784, by rfl⟩ : syracuseStep 1346379 = 2019569) B2019569
theorem B2018135 : Blo 1344991 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B1346391 : Blo 1344991 1346391 := bstep (se 1 (by rfl) ⟨1009793, by rfl⟩ : syracuseStep 1346391 = 2019587) B2019587
theorem B1346411 : Blo 1344991 1346411 := bstep (se 1 (by rfl) ⟨1009808, by rfl⟩ : syracuseStep 1346411 = 2019617) B2019617
theorem B1346423 : Blo 1344991 1346423 := bstep (se 1 (by rfl) ⟨1009817, by rfl⟩ : syracuseStep 1346423 = 2019635) B2019635
theorem B1346443 : Blo 1344991 1346443 := bstep (se 1 (by rfl) ⟨1009832, by rfl⟩ : syracuseStep 1346443 = 2019665) B2019665
theorem B1346455 : Blo 1344991 1346455 := bstep (se 1 (by rfl) ⟨1009841, by rfl⟩ : syracuseStep 1346455 = 2019683) B2019683
theorem B2018201 : Blo 1344991 2018201 := bstep (se 2 (by rfl) ⟨756825, by rfl⟩ : syracuseStep 2018201 = 1513651) B1513651
theorem B2272151 : Blo 1344991 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B1346475 : Blo 1344991 1346475 := bstep (se 1 (by rfl) ⟨1009856, by rfl⟩ : syracuseStep 1346475 = 2019713) B2019713
theorem B1346487 : Blo 1344991 1346487 := bstep (se 1 (by rfl) ⟨1009865, by rfl⟩ : syracuseStep 1346487 = 2019731) B2019731
theorem B1346507 : Blo 1344991 1346507 := bstep (se 1 (by rfl) ⟨1009880, by rfl⟩ : syracuseStep 1346507 = 2019761) B2019761
theorem B1346519 : Blo 1344991 1346519 := bstep (se 1 (by rfl) ⟨1009889, by rfl⟩ : syracuseStep 1346519 = 2019779) B2019779
theorem B1346539 : Blo 1344991 1346539 := bstep (se 1 (by rfl) ⟨1009904, by rfl⟩ : syracuseStep 1346539 = 2019809) B2019809
theorem B1436663 : Blo 1344991 1436663 := bstep (se 1 (by rfl) ⟨1077497, by rfl⟩ : syracuseStep 1436663 = 2154995) B2154995
theorem B1346551 : Blo 1344991 1346551 := bstep (se 1 (by rfl) ⟨1009913, by rfl⟩ : syracuseStep 1346551 = 2019827) B2019827
theorem B2018315 : Blo 1344991 2018315 := bstep (se 1 (by rfl) ⟨1513736, by rfl⟩ : syracuseStep 2018315 = 3027473) B3027473
theorem B1346571 : Blo 1344991 1346571 := bstep (se 1 (by rfl) ⟨1009928, by rfl⟩ : syracuseStep 1346571 = 2019857) B2019857
theorem B6810641 : Blo 1344991 6810641 := bstep (se 2 (by rfl) ⟨2553990, by rfl⟩ : syracuseStep 6810641 = 5107981) B5107981
theorem B2018327 : Blo 1344991 2018327 := bstep (se 1 (by rfl) ⟨1513745, by rfl⟩ : syracuseStep 2018327 = 3027491) B3027491
theorem B2272279 : Blo 1344991 2272279 := bstep (se 1 (by rfl) ⟨1704209, by rfl⟩ : syracuseStep 2272279 = 3408419) B3408419
theorem B1346583 : Blo 1344991 1346583 := bstep (se 1 (by rfl) ⟨1009937, by rfl⟩ : syracuseStep 1346583 = 2019875) B2019875
theorem B1346603 : Blo 1344991 1346603 := bstep (se 1 (by rfl) ⟨1009952, by rfl⟩ : syracuseStep 1346603 = 2019905) B2019905
theorem B1346615 : Blo 1344991 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B1346635 : Blo 1344991 1346635 := bstep (se 1 (by rfl) ⟨1009976, by rfl⟩ : syracuseStep 1346635 = 2019953) B2019953
theorem B1346647 : Blo 1344991 1346647 := bstep (se 1 (by rfl) ⟨1009985, by rfl⟩ : syracuseStep 1346647 = 2019971) B2019971
theorem B2018393 : Blo 1344991 2018393 := bstep (se 2 (by rfl) ⟨756897, by rfl⟩ : syracuseStep 2018393 = 1513795) B1513795
theorem B5532761 : Blo 1344991 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B1346667 : Blo 1344991 1346667 := bstep (se 1 (by rfl) ⟨1010000, by rfl⟩ : syracuseStep 1346667 = 2020001) B2020001
theorem B1346679 : Blo 1344991 1346679 := bstep (se 1 (by rfl) ⟨1010009, by rfl⟩ : syracuseStep 1346679 = 2020019) B2020019
theorem B1346699 : Blo 1344991 1346699 := bstep (se 1 (by rfl) ⟨1010024, by rfl⟩ : syracuseStep 1346699 = 2020049) B2020049
theorem B1346711 : Blo 1344991 1346711 := bstep (se 1 (by rfl) ⟨1010033, by rfl⟩ : syracuseStep 1346711 = 2020067) B2020067
theorem B1346731 : Blo 1344991 1346731 := bstep (se 1 (by rfl) ⟨1010048, by rfl⟩ : syracuseStep 1346731 = 2020097) B2020097
theorem B6810803 : Blo 1344991 6810803 := bstep (se 1 (by rfl) ⟨5108102, by rfl⟩ : syracuseStep 6810803 = 10216205) B10216205
theorem B1346743 : Blo 1344991 1346743 := bstep (se 1 (by rfl) ⟨1010057, by rfl⟩ : syracuseStep 1346743 = 2020115) B2020115
theorem B2018507 : Blo 1344991 2018507 := bstep (se 1 (by rfl) ⟨1513880, by rfl⟩ : syracuseStep 2018507 = 3027761) B3027761
theorem B5459147 : Blo 1344991 5459147 := bstep (se 1 (by rfl) ⟨4094360, by rfl⟩ : syracuseStep 5459147 = 8188721) B8188721
theorem B1346763 : Blo 1344991 1346763 := bstep (se 1 (by rfl) ⟨1010072, by rfl⟩ : syracuseStep 1346763 = 2020145) B2020145
theorem B2018519 : Blo 1344991 2018519 := bstep (se 1 (by rfl) ⟨1513889, by rfl⟩ : syracuseStep 2018519 = 3027779) B3027779
theorem B1346775 : Blo 1344991 1346775 := bstep (se 1 (by rfl) ⟨1010081, by rfl⟩ : syracuseStep 1346775 = 2020163) B2020163
theorem B1346795 : Blo 1344991 1346795 := bstep (se 1 (by rfl) ⟨1010096, by rfl⟩ : syracuseStep 1346795 = 2020193) B2020193
theorem B1346807 : Blo 1344991 1346807 := bstep (se 1 (by rfl) ⟨1010105, by rfl⟩ : syracuseStep 1346807 = 2020211) B2020211
theorem B1346827 : Blo 1344991 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B1346839 : Blo 1344991 1346839 := bstep (se 1 (by rfl) ⟨1010129, by rfl⟩ : syracuseStep 1346839 = 2020259) B2020259
theorem B2018585 : Blo 1344991 2018585 := bstep (se 2 (by rfl) ⟨756969, by rfl⟩ : syracuseStep 2018585 = 1513939) B1513939
theorem B1346859 : Blo 1344991 1346859 := bstep (se 1 (by rfl) ⟨1010144, by rfl⟩ : syracuseStep 1346859 = 2020289) B2020289
theorem B5106995 : Blo 1344991 5106995 := bstep (se 1 (by rfl) ⟨3830246, by rfl⟩ : syracuseStep 5106995 = 7660493) B7660493
theorem B1346871 : Blo 1344991 1346871 := bstep (se 1 (by rfl) ⟨1010153, by rfl⟩ : syracuseStep 1346871 = 2020307) B2020307
theorem B5107009 : Blo 1344991 5107009 := bstep (se 2 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 5107009 = 3830257) B3830257
theorem B1346891 : Blo 1344991 1346891 := bstep (se 1 (by rfl) ⟨1010168, by rfl⟩ : syracuseStep 1346891 = 2020337) B2020337
theorem B1346903 : Blo 1344991 1346903 := bstep (se 1 (by rfl) ⟨1010177, by rfl⟩ : syracuseStep 1346903 = 2020355) B2020355
theorem B1346923 : Blo 1344991 1346923 := bstep (se 1 (by rfl) ⟨1010192, by rfl⟩ : syracuseStep 1346923 = 2020385) B2020385
theorem B1346935 : Blo 1344991 1346935 := bstep (se 1 (by rfl) ⟨1010201, by rfl⟩ : syracuseStep 1346935 = 2020403) B2020403
theorem B2018699 : Blo 1344991 2018699 := bstep (se 1 (by rfl) ⟨1514024, by rfl⟩ : syracuseStep 2018699 = 3028049) B3028049
theorem B1346955 : Blo 1344991 1346955 := bstep (se 1 (by rfl) ⟨1010216, by rfl⟩ : syracuseStep 1346955 = 2020433) B2020433
theorem B2018711 : Blo 1344991 2018711 := bstep (se 1 (by rfl) ⟨1514033, by rfl⟩ : syracuseStep 2018711 = 3028067) B3028067
theorem B1346967 : Blo 1344991 1346967 := bstep (se 1 (by rfl) ⟨1010225, by rfl⟩ : syracuseStep 1346967 = 2020451) B2020451
theorem B1346987 : Blo 1344991 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B3026393 : Blo 1344991 3026393 := bstep (se 2 (by rfl) ⟨1134897, by rfl⟩ : syracuseStep 3026393 = 2269795) B2269795
theorem B2018777 : Blo 1344991 2018777 := bstep (se 2 (by rfl) ⟨757041, by rfl⟩ : syracuseStep 2018777 = 1514083) B1514083
theorem B3689945 : Blo 1344991 3689945 := bstep (se 2 (by rfl) ⟨1383729, by rfl⟩ : syracuseStep 3689945 = 2767459) B2767459
theorem B3026483 : Blo 1344991 3026483 := bstep (se 1 (by rfl) ⟨2269862, by rfl⟩ : syracuseStep 3026483 = 4539725) B4539725
theorem B5746241 : Blo 1344991 5746241 := bstep (se 2 (by rfl) ⟨2154840, by rfl⟩ : syracuseStep 5746241 = 4309681) B4309681
theorem B2018891 : Blo 1344991 2018891 := bstep (se 1 (by rfl) ⟨1514168, by rfl⟩ : syracuseStep 2018891 = 3028337) B3028337
theorem B3026519 : Blo 1344991 3026519 := bstep (se 1 (by rfl) ⟨2269889, by rfl⟩ : syracuseStep 3026519 = 4539779) B4539779
theorem B2018903 : Blo 1344991 2018903 := bstep (se 1 (by rfl) ⟨1514177, by rfl⟩ : syracuseStep 2018903 = 3028355) B3028355
theorem B2272907 : Blo 1344991 2272907 := bstep (se 1 (by rfl) ⟨1704680, by rfl⟩ : syracuseStep 2272907 = 3409361) B3409361
theorem B2018969 : Blo 1344991 2018969 := bstep (se 2 (by rfl) ⟨757113, by rfl⟩ : syracuseStep 2018969 = 1514227) B1514227
theorem B1437355 : Blo 1344991 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B8621747 : Blo 1344991 8621747 := bstep (se 1 (by rfl) ⟨6466310, by rfl⟩ : syracuseStep 8621747 = 12932621) B12932621
theorem B3067595 : Blo 1344991 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B4542155 : Blo 1344991 4542155 := bstep (se 1 (by rfl) ⟨3406616, by rfl⟩ : syracuseStep 4542155 = 6813233) B6813233
theorem B8736473 : Blo 1344991 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B3026699 : Blo 1344991 3026699 := bstep (se 1 (by rfl) ⟨2270024, by rfl⟩ : syracuseStep 3026699 = 4540049) B4540049
theorem B2019083 : Blo 1344991 2019083 := bstep (se 1 (by rfl) ⟨1514312, by rfl⟩ : syracuseStep 2019083 = 3028625) B3028625
theorem B2273035 : Blo 1344991 2273035 := bstep (se 1 (by rfl) ⟨1704776, by rfl⟩ : syracuseStep 2273035 = 3409553) B3409553
theorem B2019095 : Blo 1344991 2019095 := bstep (se 1 (by rfl) ⟨1514321, by rfl⟩ : syracuseStep 2019095 = 3028643) B3028643
theorem B3026753 : Blo 1344991 3026753 := bstep (se 2 (by rfl) ⟨1135032, by rfl⟩ : syracuseStep 3026753 = 2270065) B2270065
theorem B2019161 : Blo 1344991 2019161 := bstep (se 2 (by rfl) ⟨757185, by rfl⟩ : syracuseStep 2019161 = 1514371) B1514371
theorem B2019275 : Blo 1344991 2019275 := bstep (se 1 (by rfl) ⟨1514456, by rfl⟩ : syracuseStep 2019275 = 3028913) B3028913
theorem B2019287 : Blo 1344991 2019287 := bstep (se 1 (by rfl) ⟨1514465, by rfl⟩ : syracuseStep 2019287 = 3028931) B3028931
theorem B1535959 : Blo 1344991 1535959 := bstep (se 1 (by rfl) ⟨1151969, by rfl⟩ : syracuseStep 1535959 = 2303939) B2303939
theorem B4542425 : Blo 1344991 4542425 := bstep (se 2 (by rfl) ⟨1703409, by rfl⟩ : syracuseStep 4542425 = 3406819) B3406819
theorem B4853783 : Blo 1344991 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3026969 : Blo 1344991 3026969 := bstep (se 2 (by rfl) ⟨1135113, by rfl⟩ : syracuseStep 3026969 = 2270227) B2270227
theorem B2019353 : Blo 1344991 2019353 := bstep (se 2 (by rfl) ⟨757257, by rfl⟩ : syracuseStep 2019353 = 1514515) B1514515
theorem B3027059 : Blo 1344991 3027059 := bstep (se 1 (by rfl) ⟨2270294, by rfl⟩ : syracuseStep 3027059 = 4540589) B4540589
theorem B2019467 : Blo 1344991 2019467 := bstep (se 1 (by rfl) ⟨1514600, by rfl⟩ : syracuseStep 2019467 = 3029201) B3029201
theorem B3027095 : Blo 1344991 3027095 := bstep (se 1 (by rfl) ⟨2270321, by rfl⟩ : syracuseStep 3027095 = 4540643) B4540643
theorem B2019479 : Blo 1344991 2019479 := bstep (se 1 (by rfl) ⟨1514609, by rfl⟩ : syracuseStep 2019479 = 3029219) B3029219
theorem B2019545 : Blo 1344991 2019545 := bstep (se 2 (by rfl) ⟨757329, by rfl⟩ : syracuseStep 2019545 = 1514659) B1514659
theorem B3027275 : Blo 1344991 3027275 := bstep (se 1 (by rfl) ⟨2270456, by rfl⟩ : syracuseStep 3027275 = 4540913) B4540913
theorem B2019659 : Blo 1344991 2019659 := bstep (se 1 (by rfl) ⟨1514744, by rfl⟩ : syracuseStep 2019659 = 3029489) B3029489
theorem B2019671 : Blo 1344991 2019671 := bstep (se 1 (by rfl) ⟨1514753, by rfl⟩ : syracuseStep 2019671 = 3029507) B3029507
theorem B3027329 : Blo 1344991 3027329 := bstep (se 2 (by rfl) ⟨1135248, by rfl⟩ : syracuseStep 3027329 = 2270497) B2270497
theorem B10908035 : Blo 1344991 10908035 := bstep (se 1 (by rfl) ⟨8181026, by rfl⟩ : syracuseStep 10908035 = 16362053) B16362053
theorem B2019737 : Blo 1344991 2019737 := bstep (se 2 (by rfl) ⟨757401, by rfl⟩ : syracuseStep 2019737 = 1514803) B1514803
theorem B4854275 : Blo 1344991 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B2019851 : Blo 1344991 2019851 := bstep (se 1 (by rfl) ⟨1514888, by rfl⟩ : syracuseStep 2019851 = 3029777) B3029777
theorem B2019863 : Blo 1344991 2019863 := bstep (se 1 (by rfl) ⟨1514897, by rfl⟩ : syracuseStep 2019863 = 3029795) B3029795
theorem B3027545 : Blo 1344991 3027545 := bstep (se 2 (by rfl) ⟨1135329, by rfl⟩ : syracuseStep 3027545 = 2270659) B2270659
theorem B2019929 : Blo 1344991 2019929 := bstep (se 2 (by rfl) ⟨757473, by rfl⟩ : syracuseStep 2019929 = 1514947) B1514947
theorem B10228355 : Blo 1344991 10228355 := bstep (se 1 (by rfl) ⟨7671266, by rfl⟩ : syracuseStep 10228355 = 15342533) B15342533
theorem B4543127 : Blo 1344991 4543127 := bstep (se 1 (by rfl) ⟨3407345, by rfl⟩ : syracuseStep 4543127 = 6814691) B6814691
theorem B3027635 : Blo 1344991 3027635 := bstep (se 1 (by rfl) ⟨2270726, by rfl⟩ : syracuseStep 3027635 = 4541453) B4541453
theorem B2020043 : Blo 1344991 2020043 := bstep (se 1 (by rfl) ⟨1515032, by rfl⟩ : syracuseStep 2020043 = 3030065) B3030065
theorem B3027671 : Blo 1344991 3027671 := bstep (se 1 (by rfl) ⟨2270753, by rfl⟩ : syracuseStep 3027671 = 4541507) B4541507
theorem B2020055 : Blo 1344991 2020055 := bstep (se 1 (by rfl) ⟨1515041, by rfl⟩ : syracuseStep 2020055 = 3030083) B3030083
theorem B2020121 : Blo 1344991 2020121 := bstep (se 2 (by rfl) ⟨757545, by rfl⟩ : syracuseStep 2020121 = 1515091) B1515091
theorem B16380737 : Blo 1344991 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B3068761 : Blo 1344991 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B3027851 : Blo 1344991 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B2020235 : Blo 1344991 2020235 := bstep (se 1 (by rfl) ⟨1515176, by rfl⟩ : syracuseStep 2020235 = 3030353) B3030353
theorem B2020247 : Blo 1344991 2020247 := bstep (se 1 (by rfl) ⟨1515185, by rfl⟩ : syracuseStep 2020247 = 3030371) B3030371
theorem B3027905 : Blo 1344991 3027905 := bstep (se 2 (by rfl) ⟨1135464, by rfl⟩ : syracuseStep 3027905 = 2270929) B2270929
theorem B2020313 : Blo 1344991 2020313 := bstep (se 2 (by rfl) ⟨757617, by rfl⟩ : syracuseStep 2020313 = 1515235) B1515235
theorem B4371421 : Blo 1344991 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B2626561 : Blo 1344991 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B10220579 : Blo 1344991 10220579 := bstep (se 1 (by rfl) ⟨7665434, by rfl⟩ : syracuseStep 10220579 = 15330869) B15330869
theorem B6911041 : Blo 1344991 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B3404875 : Blo 1344991 3404875 := bstep (se 1 (by rfl) ⟨2553656, by rfl⟩ : syracuseStep 3404875 = 5107313) B5107313
theorem B6812747 : Blo 1344991 6812747 := bstep (se 1 (by rfl) ⟨5109560, by rfl⟩ : syracuseStep 6812747 = 10219121) B10219121
theorem B2020427 : Blo 1344991 2020427 := bstep (se 1 (by rfl) ⟨1515320, by rfl⟩ : syracuseStep 2020427 = 3030641) B3030641
theorem B2020439 : Blo 1344991 2020439 := bstep (se 1 (by rfl) ⟨1515329, by rfl⟩ : syracuseStep 2020439 = 3030659) B3030659
theorem B8623205 : Blo 1344991 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B3028121 : Blo 1344991 3028121 := bstep (se 2 (by rfl) ⟨1135545, by rfl⟩ : syracuseStep 3028121 = 2271091) B2271091
theorem B4543667 : Blo 1344991 4543667 := bstep (se 1 (by rfl) ⟨3407750, by rfl⟩ : syracuseStep 4543667 = 6815501) B6815501
theorem B8746163 : Blo 1344991 8746163 := bstep (se 1 (by rfl) ⟨6559622, by rfl⟩ : syracuseStep 8746163 = 13119245) B13119245
theorem B1365175 : Blo 1344991 1365175 := bstep (se 1 (by rfl) ⟨1023881, by rfl⟩ : syracuseStep 1365175 = 2047763) B2047763
theorem B5108939 : Blo 1344991 5108939 := bstep (se 1 (by rfl) ⟨3831704, by rfl⟩ : syracuseStep 5108939 = 7663409) B7663409
theorem B5747915 : Blo 1344991 5747915 := bstep (se 1 (by rfl) ⟨4310936, by rfl⟩ : syracuseStep 5747915 = 8621873) B8621873
theorem B3405017 : Blo 1344991 3405017 := bstep (se 2 (by rfl) ⟨1276881, by rfl⟩ : syracuseStep 3405017 = 2553763) B2553763
theorem B5108953 : Blo 1344991 5108953 := bstep (se 2 (by rfl) ⟨1915857, by rfl⟩ : syracuseStep 5108953 = 3831715) B3831715
theorem B3028211 : Blo 1344991 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B8189201 : Blo 1344991 8189201 := bstep (se 2 (by rfl) ⟨3070950, by rfl⟩ : syracuseStep 8189201 = 6141901) B6141901
theorem B3028247 : Blo 1344991 3028247 := bstep (se 1 (by rfl) ⟨2271185, by rfl⟩ : syracuseStep 3028247 = 4542371) B4542371
theorem B2274635 : Blo 1344991 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B4543937 : Blo 1344991 4543937 := bstep (se 2 (by rfl) ⟨1703976, by rfl⟩ : syracuseStep 4543937 = 3407953) B3407953
theorem B3028427 : Blo 1344991 3028427 := bstep (se 1 (by rfl) ⟨2271320, by rfl⟩ : syracuseStep 3028427 = 4542641) B4542641
theorem B3028481 : Blo 1344991 3028481 := bstep (se 2 (by rfl) ⟨1135680, by rfl⟩ : syracuseStep 3028481 = 2271361) B2271361
theorem B11818541 : Blo 1344991 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B3028697 : Blo 1344991 3028697 := bstep (se 2 (by rfl) ⟨1135761, by rfl⟩ : syracuseStep 3028697 = 2271523) B2271523
theorem B3028787 : Blo 1344991 3028787 := bstep (se 1 (by rfl) ⟨2271590, by rfl⟩ : syracuseStep 3028787 = 4543181) B4543181
theorem B1513291 : Blo 1344991 1513291 := bstep (se 1 (by rfl) ⟨1134968, by rfl⟩ : syracuseStep 1513291 = 2269937) B2269937
theorem B3028823 : Blo 1344991 3028823 := bstep (se 1 (by rfl) ⟨2271617, by rfl⟩ : syracuseStep 3028823 = 4543235) B4543235
theorem B1513399 : Blo 1344991 1513399 := bstep (se 1 (by rfl) ⟨1135049, by rfl⟩ : syracuseStep 1513399 = 2270099) B2270099
theorem B4544477 : Blo 1344991 4544477 := bstep (se 3 (by rfl) ⟨852089, by rfl⟩ : syracuseStep 4544477 = 1704179) B1704179
theorem B3029003 : Blo 1344991 3029003 := bstep (se 1 (by rfl) ⟨2271752, by rfl⟩ : syracuseStep 3029003 = 4543505) B4543505
theorem B3405847 : Blo 1344991 3405847 := bstep (se 1 (by rfl) ⟨2554385, by rfl⟩ : syracuseStep 3405847 = 5108771) B5108771
theorem B2873369 : Blo 1344991 2873369 := bstep (se 2 (by rfl) ⟨1077513, by rfl⟩ : syracuseStep 2873369 = 2155027) B2155027
theorem B8181805 : Blo 1344991 8181805 := bstep (se 3 (by rfl) ⟨1534088, by rfl⟩ : syracuseStep 8181805 = 3068177) B3068177
theorem B3029057 : Blo 1344991 3029057 := bstep (se 2 (by rfl) ⟨1135896, by rfl⟩ : syracuseStep 3029057 = 2271793) B2271793
theorem B1513579 : Blo 1344991 1513579 := bstep (se 1 (by rfl) ⟨1135184, by rfl⟩ : syracuseStep 1513579 = 2270369) B2270369
theorem B5109911 : Blo 1344991 5109911 := bstep (se 1 (by rfl) ⟨3832433, by rfl⟩ : syracuseStep 5109911 = 7664867) B7664867
theorem B17250509 : Blo 1344991 17250509 := bstep (se 3 (by rfl) ⟨3234470, by rfl⟩ : syracuseStep 17250509 = 6468941) B6468941
theorem B1513687 : Blo 1344991 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B8181977 : Blo 1344991 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B6551825 : Blo 1344991 6551825 := bstep (se 2 (by rfl) ⟨2456934, by rfl⟩ : syracuseStep 6551825 = 4913869) B4913869
theorem B3029273 : Blo 1344991 3029273 := bstep (se 2 (by rfl) ⟨1135977, by rfl⟩ : syracuseStep 3029273 = 2271955) B2271955
theorem B4667723 : Blo 1344991 4667723 := bstep (se 1 (by rfl) ⟨3500792, by rfl⟩ : syracuseStep 4667723 = 7001585) B7001585
theorem B3029363 : Blo 1344991 3029363 := bstep (se 1 (by rfl) ⟨2272022, by rfl⟩ : syracuseStep 3029363 = 4544045) B4544045
theorem B1513867 : Blo 1344991 1513867 := bstep (se 1 (by rfl) ⟨1135400, by rfl⟩ : syracuseStep 1513867 = 2270801) B2270801
theorem B3029399 : Blo 1344991 3029399 := bstep (se 1 (by rfl) ⟨2272049, by rfl⟩ : syracuseStep 3029399 = 4544099) B4544099
theorem B3406283 : Blo 1344991 3406283 := bstep (se 1 (by rfl) ⟨2554712, by rfl⟩ : syracuseStep 3406283 = 5109425) B5109425
theorem B3832285 : Blo 1344991 3832285 := bstep (se 3 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 3832285 = 1437107) B1437107
theorem B5749213 : Blo 1344991 5749213 := bstep (se 3 (by rfl) ⟨1077977, by rfl⟩ : syracuseStep 5749213 = 2155955) B2155955
theorem B2554355 : Blo 1344991 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B1513975 : Blo 1344991 1513975 := bstep (se 1 (by rfl) ⟨1135481, by rfl⟩ : syracuseStep 1513975 = 2270963) B2270963
theorem B4848131 : Blo 1344991 4848131 := bstep (se 1 (by rfl) ⟨3636098, by rfl⟩ : syracuseStep 4848131 = 7272197) B7272197
theorem B3832343 : Blo 1344991 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B3029579 : Blo 1344991 3029579 := bstep (se 1 (by rfl) ⟨2272184, by rfl⟩ : syracuseStep 3029579 = 4544369) B4544369
theorem B3029633 : Blo 1344991 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B14006915 : Blo 1344991 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B2554507 : Blo 1344991 2554507 := bstep (se 1 (by rfl) ⟨1915880, by rfl⟩ : syracuseStep 2554507 = 3831761) B3831761
theorem B1514155 : Blo 1344991 1514155 := bstep (se 1 (by rfl) ⟨1135616, by rfl⟩ : syracuseStep 1514155 = 2271233) B2271233
theorem B1702615 : Blo 1344991 1702615 := bstep (se 1 (by rfl) ⟨1276961, by rfl⟩ : syracuseStep 1702615 = 2553923) B2553923
theorem B1915607 : Blo 1344991 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B1514263 : Blo 1344991 1514263 := bstep (se 1 (by rfl) ⟨1135697, by rfl⟩ : syracuseStep 1514263 = 2271395) B2271395
theorem B2874163 : Blo 1344991 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B5749555 : Blo 1344991 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B3406657 : Blo 1344991 3406657 := bstep (se 2 (by rfl) ⟨1277496, by rfl⟩ : syracuseStep 3406657 = 2554993) B2554993
theorem B6814529 : Blo 1344991 6814529 := bstep (se 2 (by rfl) ⟨2555448, by rfl⟩ : syracuseStep 6814529 = 5110897) B5110897
theorem B4094795 : Blo 1344991 4094795 := bstep (se 1 (by rfl) ⟨3071096, by rfl⟩ : syracuseStep 4094795 = 6142193) B6142193
theorem B3029849 : Blo 1344991 3029849 := bstep (se 2 (by rfl) ⟨1136193, by rfl⟩ : syracuseStep 3029849 = 2272387) B2272387
theorem B3029939 : Blo 1344991 3029939 := bstep (se 1 (by rfl) ⟨2272454, by rfl⟩ : syracuseStep 3029939 = 4544909) B4544909
theorem B1514443 : Blo 1344991 1514443 := bstep (se 1 (by rfl) ⟨1135832, by rfl⟩ : syracuseStep 1514443 = 2271665) B2271665
theorem B3029975 : Blo 1344991 3029975 := bstep (se 1 (by rfl) ⟨2272481, by rfl⟩ : syracuseStep 3029975 = 4544963) B4544963
theorem B2554841 : Blo 1344991 2554841 := bstep (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) B1916131
theorem B4602845 : Blo 1344991 4602845 := bstep (se 3 (by rfl) ⟨863033, by rfl⟩ : syracuseStep 4602845 = 1726067) B1726067
theorem B1915915 : Blo 1344991 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B6224941 : Blo 1344991 6224941 := bstep (se 3 (by rfl) ⟨1167176, by rfl⟩ : syracuseStep 6224941 = 2334353) B2334353
theorem B1514551 : Blo 1344991 1514551 := bstep (se 1 (by rfl) ⟨1135913, by rfl⟩ : syracuseStep 1514551 = 2271827) B2271827
theorem B9215041 : Blo 1344991 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B4545611 : Blo 1344991 4545611 := bstep (se 1 (by rfl) ⟨3409208, by rfl⟩ : syracuseStep 4545611 = 6818417) B6818417
theorem B3030155 : Blo 1344991 3030155 := bstep (se 1 (by rfl) ⟨2272616, by rfl⟩ : syracuseStep 3030155 = 4545233) B4545233
theorem B3030209 : Blo 1344991 3030209 := bstep (se 2 (by rfl) ⟨1136328, by rfl⟩ : syracuseStep 3030209 = 2272657) B2272657
theorem B1514731 : Blo 1344991 1514731 := bstep (se 1 (by rfl) ⟨1136048, by rfl⟩ : syracuseStep 1514731 = 2272097) B2272097
theorem B1514839 : Blo 1344991 1514839 := bstep (se 1 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 1514839 = 2272259) B2272259
theorem B4545881 : Blo 1344991 4545881 := bstep (se 2 (by rfl) ⟨1704705, by rfl⟩ : syracuseStep 4545881 = 3409411) B3409411
theorem B5111171 : Blo 1344991 5111171 := bstep (se 1 (by rfl) ⟨3833378, by rfl⟩ : syracuseStep 5111171 = 7666757) B7666757
theorem B7667075 : Blo 1344991 7667075 := bstep (se 1 (by rfl) ⟨5750306, by rfl⟩ : syracuseStep 7667075 = 11500613) B11500613
theorem B3407255 : Blo 1344991 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B3030425 : Blo 1344991 3030425 := bstep (se 2 (by rfl) ⟨1136409, by rfl⟩ : syracuseStep 3030425 = 2272819) B2272819
theorem B2047447 : Blo 1344991 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B9698777 : Blo 1344991 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B3030515 : Blo 1344991 3030515 := bstep (se 1 (by rfl) ⟨2272886, by rfl⟩ : syracuseStep 3030515 = 4545773) B4545773
theorem B1515019 : Blo 1344991 1515019 := bstep (se 1 (by rfl) ⟨1136264, by rfl⟩ : syracuseStep 1515019 = 2272529) B2272529
theorem B37330445 : Blo 1344991 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B3030551 : Blo 1344991 3030551 := bstep (se 1 (by rfl) ⟨2272913, by rfl⟩ : syracuseStep 3030551 = 4545827) B4545827
theorem B4374067 : Blo 1344991 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B2555479 : Blo 1344991 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B1515127 : Blo 1344991 1515127 := bstep (se 1 (by rfl) ⟨1136345, by rfl⟩ : syracuseStep 1515127 = 2272691) B2272691
theorem B2875009 : Blo 1344991 2875009 := bstep (se 2 (by rfl) ⟨1078128, by rfl⟩ : syracuseStep 2875009 = 2156257) B2156257
theorem B3112577 : Blo 1344991 3112577 := bstep (se 2 (by rfl) ⟨1167216, by rfl⟩ : syracuseStep 3112577 = 2334433) B2334433
theorem B3030731 : Blo 1344991 3030731 := bstep (se 1 (by rfl) ⟨2273048, by rfl⟩ : syracuseStep 3030731 = 4546097) B4546097
theorem B3833561 : Blo 1344991 3833561 := bstep (se 2 (by rfl) ⟨1437585, by rfl⟩ : syracuseStep 3833561 = 2875171) B2875171
theorem B23002865 : Blo 1344991 23002865 := bstep (se 2 (by rfl) ⟨8626074, by rfl⟩ : syracuseStep 23002865 = 17252149) B17252149
theorem B8986385 : Blo 1344991 8986385 := bstep (se 2 (by rfl) ⟨3369894, by rfl⟩ : syracuseStep 8986385 = 6739789) B6739789
theorem B1515307 : Blo 1344991 1515307 := bstep (se 1 (by rfl) ⟨1136480, by rfl⟩ : syracuseStep 1515307 = 2272961) B2272961
theorem B9707309 : Blo 1344991 9707309 := bstep (se 3 (by rfl) ⟨1820120, by rfl⟩ : syracuseStep 9707309 = 3640241) B3640241
theorem B10215233 : Blo 1344991 10215233 := bstep (se 2 (by rfl) ⟨3830712, by rfl⟩ : syracuseStep 10215233 = 7661425) B7661425
theorem B3833675 : Blo 1344991 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B7667531 : Blo 1344991 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B2154443 : Blo 1344991 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B2875351 : Blo 1344991 2875351 := bstep (se 1 (by rfl) ⟨2156513, by rfl⟩ : syracuseStep 2875351 = 4313027) B4313027
theorem B3235855 : Blo 1344991 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B5111869 : Blo 1344991 5111869 := bstep (se 3 (by rfl) ⟨958475, by rfl⟩ : syracuseStep 5111869 = 1916951) B1916951
theorem B3637505 : Blo 1344991 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B2556193 : Blo 1344991 2556193 := bstep (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) B1917145
theorem B2457899 : Blo 1344991 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B1704235 : Blo 1344991 1704235 := bstep (se 1 (by rfl) ⟨1278176, by rfl⟩ : syracuseStep 1704235 = 2556353) B2556353
theorem B3236183 : Blo 1344991 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B39338531 : Blo 1344991 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B10920491 : Blo 1344991 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B2556535 : Blo 1344991 2556535 := bstep (se 1 (by rfl) ⟨1917401, by rfl⟩ : syracuseStep 2556535 = 3834803) B3834803
theorem B1917703 : Blo 1344991 1917703 := bstep (se 1 (by rfl) ⟨1438277, by rfl⟩ : syracuseStep 1917703 = 2876555) B2876555
theorem B2270011 : Blo 1344991 2270011 := bstep (se 1 (by rfl) ⟨1702508, by rfl⟩ : syracuseStep 2270011 = 3405017) B3405017
theorem B1516423 : Blo 1344991 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B2589575 : Blo 1344991 2589575 := bstep (se 1 (by rfl) ⟨1942181, by rfl⟩ : syracuseStep 2589575 = 3884363) B3884363
theorem B2270153 : Blo 1344991 2270153 := bstep (se 2 (by rfl) ⟨851307, by rfl⟩ : syracuseStep 2270153 = 1702615) B1702615
theorem B6816797 : Blo 1344991 6816797 := bstep (se 3 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 6816797 = 2556299) B2556299
theorem B2426041 : Blo 1344991 2426041 := bstep (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) B1819531
theorem B8619209 : Blo 1344991 8619209 := bstep (se 2 (by rfl) ⟨3232203, by rfl⟩ : syracuseStep 8619209 = 6464407) B6464407
theorem B12928349 : Blo 1344991 12928349 := bstep (se 3 (by rfl) ⟨2424065, by rfl⟩ : syracuseStep 12928349 = 4848131) B4848131
theorem B8299921 : Blo 1344991 8299921 := bstep (se 2 (by rfl) ⟨3112470, by rfl⟩ : syracuseStep 8299921 = 6224941) B6224941
theorem B4539833 : Blo 1344991 4539833 := bstep (se 2 (by rfl) ⟨1702437, by rfl⟩ : syracuseStep 4539833 = 3404875) B3404875
theorem B6817283 : Blo 1344991 6817283 := bstep (se 1 (by rfl) ⟨5112962, by rfl⟩ : syracuseStep 6817283 = 10225925) B10225925
theorem B1345031 : Blo 1344991 1345031 := bstep (se 1 (by rfl) ⟨1008773, by rfl⟩ : syracuseStep 1345031 = 2017547) B2017547
theorem B1345039 : Blo 1344991 1345039 := bstep (se 1 (by rfl) ⟨1008779, by rfl⟩ : syracuseStep 1345039 = 2017559) B2017559
theorem B1345083 : Blo 1344991 1345083 := bstep (se 1 (by rfl) ⟨1008812, by rfl⟩ : syracuseStep 1345083 = 2017625) B2017625
theorem B3835451 : Blo 1344991 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B3409523 : Blo 1344991 3409523 := bstep (se 1 (by rfl) ⟨2557142, by rfl⟩ : syracuseStep 3409523 = 5114285) B5114285
theorem B1345159 : Blo 1344991 1345159 := bstep (se 1 (by rfl) ⟨1008869, by rfl⟩ : syracuseStep 1345159 = 2017739) B2017739
theorem B2270855 : Blo 1344991 2270855 := bstep (se 1 (by rfl) ⟨1703141, by rfl⟩ : syracuseStep 2270855 = 3406283) B3406283
theorem B1345167 : Blo 1344991 1345167 := bstep (se 1 (by rfl) ⟨1008875, by rfl⟩ : syracuseStep 1345167 = 2017751) B2017751
theorem B1345211 : Blo 1344991 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B6809345 : Blo 1344991 6809345 := bstep (se 2 (by rfl) ⟨2553504, by rfl⟩ : syracuseStep 6809345 = 5107009) B5107009
theorem B5113601 : Blo 1344991 5113601 := bstep (se 2 (by rfl) ⟨1917600, by rfl⟩ : syracuseStep 5113601 = 3835201) B3835201
theorem B1345287 : Blo 1344991 1345287 := bstep (se 1 (by rfl) ⟨1008965, by rfl⟩ : syracuseStep 1345287 = 2017931) B2017931
theorem B1345295 : Blo 1344991 1345295 := bstep (se 1 (by rfl) ⟨1008971, by rfl⟩ : syracuseStep 1345295 = 2017943) B2017943
theorem B1345339 : Blo 1344991 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B1345415 : Blo 1344991 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B2729863 : Blo 1344991 2729863 := bstep (se 1 (by rfl) ⟨2047397, by rfl⟩ : syracuseStep 2729863 = 4094795) B4094795
theorem B1345423 : Blo 1344991 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B1345467 : Blo 1344991 1345467 := bstep (se 1 (by rfl) ⟨1009100, by rfl⟩ : syracuseStep 1345467 = 2018201) B2018201
theorem B2729929 : Blo 1344991 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B1345543 : Blo 1344991 1345543 := bstep (se 1 (by rfl) ⟨1009157, by rfl⟩ : syracuseStep 1345543 = 2018315) B2018315
theorem B4540427 : Blo 1344991 4540427 := bstep (se 1 (by rfl) ⟨3405320, by rfl⟩ : syracuseStep 4540427 = 6810641) B6810641
theorem B1345551 : Blo 1344991 1345551 := bstep (se 1 (by rfl) ⟨1009163, by rfl⟩ : syracuseStep 1345551 = 2018327) B2018327
theorem B1345595 : Blo 1344991 1345595 := bstep (se 1 (by rfl) ⟨1009196, by rfl⟩ : syracuseStep 1345595 = 2018393) B2018393
theorem B3688507 : Blo 1344991 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B4540535 : Blo 1344991 4540535 := bstep (se 1 (by rfl) ⟨3405401, by rfl⟩ : syracuseStep 4540535 = 6810803) B6810803
theorem B1345671 : Blo 1344991 1345671 := bstep (se 1 (by rfl) ⟨1009253, by rfl⟩ : syracuseStep 1345671 = 2018507) B2018507
theorem B3639431 : Blo 1344991 3639431 := bstep (se 1 (by rfl) ⟨2729573, by rfl⟩ : syracuseStep 3639431 = 5459147) B5459147
theorem B1345679 : Blo 1344991 1345679 := bstep (se 1 (by rfl) ⟨1009259, by rfl⟩ : syracuseStep 1345679 = 2018519) B2018519
theorem B1345723 : Blo 1344991 1345723 := bstep (se 1 (by rfl) ⟨1009292, by rfl⟩ : syracuseStep 1345723 = 2018585) B2018585
theorem B1345799 : Blo 1344991 1345799 := bstep (se 1 (by rfl) ⟨1009349, by rfl⟩ : syracuseStep 1345799 = 2018699) B2018699
theorem B1345807 : Blo 1344991 1345807 := bstep (se 1 (by rfl) ⟨1009355, by rfl⟩ : syracuseStep 1345807 = 2018711) B2018711
theorem B2271503 : Blo 1344991 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B2017595 : Blo 1344991 2017595 := bstep (se 1 (by rfl) ⟨1513196, by rfl⟩ : syracuseStep 2017595 = 3026393) B3026393
theorem B6465851 : Blo 1344991 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B1345851 : Blo 1344991 1345851 := bstep (se 1 (by rfl) ⟨1009388, by rfl⟩ : syracuseStep 1345851 = 2018777) B2018777
theorem B2459963 : Blo 1344991 2459963 := bstep (se 1 (by rfl) ⟨1844972, by rfl⟩ : syracuseStep 2459963 = 3689945) B3689945
theorem B2017655 : Blo 1344991 2017655 := bstep (se 1 (by rfl) ⟨1513241, by rfl⟩ : syracuseStep 2017655 = 3026483) B3026483
theorem B1345927 : Blo 1344991 1345927 := bstep (se 1 (by rfl) ⟨1009445, by rfl⟩ : syracuseStep 1345927 = 2018891) B2018891
theorem B2017679 : Blo 1344991 2017679 := bstep (se 1 (by rfl) ⟨1513259, by rfl⟩ : syracuseStep 2017679 = 3026519) B3026519
theorem B1345935 : Blo 1344991 1345935 := bstep (se 1 (by rfl) ⟨1009451, by rfl⟩ : syracuseStep 1345935 = 2018903) B2018903
theorem B2075051 : Blo 1344991 2075051 := bstep (se 1 (by rfl) ⟨1556288, by rfl⟩ : syracuseStep 2075051 = 3112577) B3112577
theorem B2017721 : Blo 1344991 2017721 := bstep (se 2 (by rfl) ⟨756645, by rfl⟩ : syracuseStep 2017721 = 1513291) B1513291
theorem B1345979 : Blo 1344991 1345979 := bstep (se 1 (by rfl) ⟨1009484, by rfl⟩ : syracuseStep 1345979 = 2018969) B2018969
theorem B2017799 : Blo 1344991 2017799 := bstep (se 1 (by rfl) ⟨1513349, by rfl⟩ : syracuseStep 2017799 = 3026699) B3026699
theorem B1346055 : Blo 1344991 1346055 := bstep (se 1 (by rfl) ⟨1009541, by rfl⟩ : syracuseStep 1346055 = 2019083) B2019083
theorem B5990923 : Blo 1344991 5990923 := bstep (se 1 (by rfl) ⟨4493192, by rfl⟩ : syracuseStep 5990923 = 8986385) B8986385
theorem B1346063 : Blo 1344991 1346063 := bstep (se 1 (by rfl) ⟨1009547, by rfl⟩ : syracuseStep 1346063 = 2019095) B2019095
theorem B5745181 : Blo 1344991 5745181 := bstep (se 3 (by rfl) ⟨1077221, by rfl⟩ : syracuseStep 5745181 = 2154443) B2154443
theorem B11495965 : Blo 1344991 11495965 := bstep (se 3 (by rfl) ⟨2155493, by rfl⟩ : syracuseStep 11495965 = 4310987) B4310987
theorem B6810155 : Blo 1344991 6810155 := bstep (se 1 (by rfl) ⟨5107616, by rfl⟩ : syracuseStep 6810155 = 10215233) B10215233
theorem B2017835 : Blo 1344991 2017835 := bstep (se 1 (by rfl) ⟨1513376, by rfl⟩ : syracuseStep 2017835 = 3026753) B3026753
theorem B1346107 : Blo 1344991 1346107 := bstep (se 1 (by rfl) ⟨1009580, by rfl⟩ : syracuseStep 1346107 = 2019161) B2019161
theorem B2017865 : Blo 1344991 2017865 := bstep (se 2 (by rfl) ⟨756699, by rfl⟩ : syracuseStep 2017865 = 1513399) B1513399
theorem B1346183 : Blo 1344991 1346183 := bstep (se 1 (by rfl) ⟨1009637, by rfl⟩ : syracuseStep 1346183 = 2019275) B2019275
theorem B1346191 : Blo 1344991 1346191 := bstep (se 1 (by rfl) ⟨1009643, by rfl⟩ : syracuseStep 1346191 = 2019287) B2019287
theorem B2017979 : Blo 1344991 2017979 := bstep (se 1 (by rfl) ⟨1513484, by rfl⟩ : syracuseStep 2017979 = 3026969) B3026969
theorem B1346235 : Blo 1344991 1346235 := bstep (se 1 (by rfl) ⟨1009676, by rfl⟩ : syracuseStep 1346235 = 2019353) B2019353
theorem B10914497 : Blo 1344991 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B4541129 : Blo 1344991 4541129 := bstep (se 2 (by rfl) ⟨1702923, by rfl⟩ : syracuseStep 4541129 = 3405847) B3405847
theorem B2018039 : Blo 1344991 2018039 := bstep (se 1 (by rfl) ⟨1513529, by rfl⟩ : syracuseStep 2018039 = 3027059) B3027059
theorem B1346311 : Blo 1344991 1346311 := bstep (se 1 (by rfl) ⟨1009733, by rfl⟩ : syracuseStep 1346311 = 2019467) B2019467
theorem B2018063 : Blo 1344991 2018063 := bstep (se 1 (by rfl) ⟨1513547, by rfl⟩ : syracuseStep 2018063 = 3027095) B3027095
theorem B1346319 : Blo 1344991 1346319 := bstep (se 1 (by rfl) ⟨1009739, by rfl⟩ : syracuseStep 1346319 = 2019479) B2019479
theorem B2272043 : Blo 1344991 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B2018105 : Blo 1344991 2018105 := bstep (se 2 (by rfl) ⟨756789, by rfl⟩ : syracuseStep 2018105 = 1513579) B1513579
theorem B1346363 : Blo 1344991 1346363 := bstep (se 1 (by rfl) ⟨1009772, by rfl⟩ : syracuseStep 1346363 = 2019545) B2019545
theorem B2018183 : Blo 1344991 2018183 := bstep (se 1 (by rfl) ⟨1513637, by rfl⟩ : syracuseStep 2018183 = 3027275) B3027275
theorem B1346439 : Blo 1344991 1346439 := bstep (se 1 (by rfl) ⟨1009829, by rfl⟩ : syracuseStep 1346439 = 2019659) B2019659
theorem B1346447 : Blo 1344991 1346447 := bstep (se 1 (by rfl) ⟨1009835, by rfl⟩ : syracuseStep 1346447 = 2019671) B2019671
theorem B2018219 : Blo 1344991 2018219 := bstep (se 1 (by rfl) ⟨1513664, by rfl⟩ : syracuseStep 2018219 = 3027329) B3027329
theorem B1346491 : Blo 1344991 1346491 := bstep (se 1 (by rfl) ⟨1009868, by rfl⟩ : syracuseStep 1346491 = 2019737) B2019737
theorem B2018249 : Blo 1344991 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1346567 : Blo 1344991 1346567 := bstep (se 1 (by rfl) ⟨1009925, by rfl⟩ : syracuseStep 1346567 = 2019851) B2019851
theorem B1346575 : Blo 1344991 1346575 := bstep (se 1 (by rfl) ⟨1009931, by rfl⟩ : syracuseStep 1346575 = 2019863) B2019863
theorem B2018363 : Blo 1344991 2018363 := bstep (se 1 (by rfl) ⟨1513772, by rfl⟩ : syracuseStep 2018363 = 3027545) B3027545
theorem B1346619 : Blo 1344991 1346619 := bstep (se 1 (by rfl) ⟨1009964, by rfl⟩ : syracuseStep 1346619 = 2019929) B2019929
theorem B6818903 : Blo 1344991 6818903 := bstep (se 1 (by rfl) ⟨5114177, by rfl⟩ : syracuseStep 6818903 = 10228355) B10228355
theorem B2018423 : Blo 1344991 2018423 := bstep (se 1 (by rfl) ⟨1513817, by rfl⟩ : syracuseStep 2018423 = 3027635) B3027635
theorem B1346695 : Blo 1344991 1346695 := bstep (se 1 (by rfl) ⟨1010021, by rfl⟩ : syracuseStep 1346695 = 2020043) B2020043
theorem B2018447 : Blo 1344991 2018447 := bstep (se 1 (by rfl) ⟨1513835, by rfl⟩ : syracuseStep 2018447 = 3027671) B3027671
theorem B1346703 : Blo 1344991 1346703 := bstep (se 1 (by rfl) ⟨1010027, by rfl⟩ : syracuseStep 1346703 = 2020055) B2020055
theorem B2018489 : Blo 1344991 2018489 := bstep (se 2 (by rfl) ⟨756933, by rfl⟩ : syracuseStep 2018489 = 1513867) B1513867
theorem B2272441 : Blo 1344991 2272441 := bstep (se 2 (by rfl) ⟨852165, by rfl⟩ : syracuseStep 2272441 = 1704331) B1704331
theorem B1346747 : Blo 1344991 1346747 := bstep (se 1 (by rfl) ⟨1010060, by rfl⟩ : syracuseStep 1346747 = 2020121) B2020121
theorem B2018567 : Blo 1344991 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B1346823 : Blo 1344991 1346823 := bstep (se 1 (by rfl) ⟨1010117, by rfl⟩ : syracuseStep 1346823 = 2020235) B2020235
theorem B1346831 : Blo 1344991 1346831 := bstep (se 1 (by rfl) ⟨1010123, by rfl⟩ : syracuseStep 1346831 = 2020247) B2020247
theorem B8629537 : Blo 1344991 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B2018603 : Blo 1344991 2018603 := bstep (se 1 (by rfl) ⟨1513952, by rfl⟩ : syracuseStep 2018603 = 3027905) B3027905
theorem B1346875 : Blo 1344991 1346875 := bstep (se 1 (by rfl) ⟨1010156, by rfl⟩ : syracuseStep 1346875 = 2020313) B2020313
theorem B2018633 : Blo 1344991 2018633 := bstep (se 2 (by rfl) ⟨756987, by rfl⟩ : syracuseStep 2018633 = 1513975) B1513975
theorem B4541831 : Blo 1344991 4541831 := bstep (se 1 (by rfl) ⟨3406373, by rfl⟩ : syracuseStep 4541831 = 6812747) B6812747
theorem B1346951 : Blo 1344991 1346951 := bstep (se 1 (by rfl) ⟨1010213, by rfl⟩ : syracuseStep 1346951 = 2020427) B2020427
theorem B1346959 : Blo 1344991 1346959 := bstep (se 1 (by rfl) ⟨1010219, by rfl⟩ : syracuseStep 1346959 = 2020439) B2020439
theorem B2018747 : Blo 1344991 2018747 := bstep (se 1 (by rfl) ⟨1514060, by rfl⟩ : syracuseStep 2018747 = 3028121) B3028121
theorem B2018807 : Blo 1344991 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B3026447 : Blo 1344991 3026447 := bstep (se 1 (by rfl) ⟨2269835, by rfl⟩ : syracuseStep 3026447 = 4539671) B4539671
theorem B2018831 : Blo 1344991 2018831 := bstep (se 1 (by rfl) ⟨1514123, by rfl⟩ : syracuseStep 2018831 = 3028247) B3028247
theorem B3026465 : Blo 1344991 3026465 := bstep (se 2 (by rfl) ⟨1134924, by rfl⟩ : syracuseStep 3026465 = 2269849) B2269849
theorem B2018873 : Blo 1344991 2018873 := bstep (se 2 (by rfl) ⟨757077, by rfl⟩ : syracuseStep 2018873 = 1514155) B1514155
theorem B2018951 : Blo 1344991 2018951 := bstep (se 1 (by rfl) ⟨1514213, by rfl⟩ : syracuseStep 2018951 = 3028427) B3028427
theorem B2018987 : Blo 1344991 2018987 := bstep (se 1 (by rfl) ⟨1514240, by rfl⟩ : syracuseStep 2018987 = 3028481) B3028481
theorem B2019017 : Blo 1344991 2019017 := bstep (se 2 (by rfl) ⟨757131, by rfl⟩ : syracuseStep 2019017 = 1514263) B1514263
theorem B4542209 : Blo 1344991 4542209 := bstep (se 2 (by rfl) ⟨1703328, by rfl⟩ : syracuseStep 4542209 = 3406657) B3406657
theorem B4091681 : Blo 1344991 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B17248049 : Blo 1344991 17248049 := bstep (se 2 (by rfl) ⟨6468018, by rfl⟩ : syracuseStep 17248049 = 12936037) B12936037
theorem B6811451 : Blo 1344991 6811451 := bstep (se 1 (by rfl) ⟨5108588, by rfl⟩ : syracuseStep 6811451 = 10217177) B10217177
theorem B2019131 : Blo 1344991 2019131 := bstep (se 1 (by rfl) ⟨1514348, by rfl⟩ : syracuseStep 2019131 = 3028697) B3028697
theorem B3026807 : Blo 1344991 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B2019191 : Blo 1344991 2019191 := bstep (se 1 (by rfl) ⟨1514393, by rfl⟩ : syracuseStep 2019191 = 3028787) B3028787
theorem B2019215 : Blo 1344991 2019215 := bstep (se 1 (by rfl) ⟨1514411, by rfl⟩ : syracuseStep 2019215 = 3028823) B3028823
theorem B2019257 : Blo 1344991 2019257 := bstep (se 2 (by rfl) ⟨757221, by rfl⟩ : syracuseStep 2019257 = 1514443) B1514443
theorem B5828561 : Blo 1344991 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B6811613 : Blo 1344991 6811613 := bstep (se 3 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 6811613 = 2554355) B2554355
theorem B3502081 : Blo 1344991 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B2019335 : Blo 1344991 2019335 := bstep (se 1 (by rfl) ⟨1514501, by rfl⟩ : syracuseStep 2019335 = 3029003) B3029003
theorem B3026987 : Blo 1344991 3026987 := bstep (se 1 (by rfl) ⟨2270240, by rfl⟩ : syracuseStep 3026987 = 4540481) B4540481
theorem B2019371 : Blo 1344991 2019371 := bstep (se 1 (by rfl) ⟨1514528, by rfl⟩ : syracuseStep 2019371 = 3029057) B3029057
theorem B2019401 : Blo 1344991 2019401 := bstep (se 2 (by rfl) ⟨757275, by rfl⟩ : syracuseStep 2019401 = 1514551) B1514551
theorem B5107799 : Blo 1344991 5107799 := bstep (se 1 (by rfl) ⟨3830849, by rfl⟩ : syracuseStep 5107799 = 7661699) B7661699
theorem B10219607 : Blo 1344991 10219607 := bstep (se 1 (by rfl) ⟨7664705, by rfl⟩ : syracuseStep 10219607 = 15329411) B15329411
theorem B2019515 : Blo 1344991 2019515 := bstep (se 1 (by rfl) ⟨1514636, by rfl⟩ : syracuseStep 2019515 = 3029273) B3029273
theorem B5746889 : Blo 1344991 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B2019575 : Blo 1344991 2019575 := bstep (se 1 (by rfl) ⟨1514681, by rfl⟩ : syracuseStep 2019575 = 3029363) B3029363
theorem B3453199 : Blo 1344991 3453199 := bstep (se 1 (by rfl) ⟨2589899, by rfl⟩ : syracuseStep 3453199 = 5179799) B5179799
theorem B2019599 : Blo 1344991 2019599 := bstep (se 1 (by rfl) ⟨1514699, by rfl⟩ : syracuseStep 2019599 = 3029399) B3029399
theorem B6811937 : Blo 1344991 6811937 := bstep (se 2 (by rfl) ⟨2554476, by rfl⟩ : syracuseStep 6811937 = 5108953) B5108953
theorem B2019641 : Blo 1344991 2019641 := bstep (se 2 (by rfl) ⟨757365, by rfl⟩ : syracuseStep 2019641 = 1514731) B1514731
theorem B3830075 : Blo 1344991 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B2019719 : Blo 1344991 2019719 := bstep (se 1 (by rfl) ⟨1514789, by rfl⟩ : syracuseStep 2019719 = 3029579) B3029579
theorem B3027347 : Blo 1344991 3027347 := bstep (se 1 (by rfl) ⟨2270510, by rfl⟩ : syracuseStep 3027347 = 4541021) B4541021
theorem B2019755 : Blo 1344991 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B3027401 : Blo 1344991 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B2019785 : Blo 1344991 2019785 := bstep (se 2 (by rfl) ⟨757419, by rfl⟩ : syracuseStep 2019785 = 1514839) B1514839
theorem B11497949 : Blo 1344991 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B11055619 : Blo 1344991 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B4543019 : Blo 1344991 4543019 := bstep (se 1 (by rfl) ⟨3407264, by rfl⟩ : syracuseStep 4543019 = 6814529) B6814529
theorem B2019899 : Blo 1344991 2019899 := bstep (se 1 (by rfl) ⟨1514924, by rfl⟩ : syracuseStep 2019899 = 3029849) B3029849
theorem B5108285 : Blo 1344991 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B2019959 : Blo 1344991 2019959 := bstep (se 1 (by rfl) ⟨1514969, by rfl⟩ : syracuseStep 2019959 = 3029939) B3029939
theorem B2019983 : Blo 1344991 2019983 := bstep (se 1 (by rfl) ⟨1514987, by rfl⟩ : syracuseStep 2019983 = 3029975) B3029975
theorem B3068563 : Blo 1344991 3068563 := bstep (se 1 (by rfl) ⟨2301422, by rfl⟩ : syracuseStep 3068563 = 4602845) B4602845
theorem B2020025 : Blo 1344991 2020025 := bstep (se 2 (by rfl) ⟨757509, by rfl⟩ : syracuseStep 2020025 = 1515019) B1515019
theorem B2020103 : Blo 1344991 2020103 := bstep (se 1 (by rfl) ⟨1515077, by rfl⟩ : syracuseStep 2020103 = 3030155) B3030155
theorem B2020139 : Blo 1344991 2020139 := bstep (se 1 (by rfl) ⟨1515104, by rfl⟩ : syracuseStep 2020139 = 3030209) B3030209
theorem B2020169 : Blo 1344991 2020169 := bstep (se 2 (by rfl) ⟨757563, by rfl⟩ : syracuseStep 2020169 = 1515127) B1515127
theorem B3404663 : Blo 1344991 3404663 := bstep (se 1 (by rfl) ⟨2553497, by rfl⟩ : syracuseStep 3404663 = 5106995) B5106995
theorem B87274421 : Blo 1344991 87274421 := bstep (se 5 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 87274421 = 8181977) B8181977
theorem B2020283 : Blo 1344991 2020283 := bstep (se 1 (by rfl) ⟨1515212, by rfl⟩ : syracuseStep 2020283 = 3030425) B3030425
theorem B2020343 : Blo 1344991 2020343 := bstep (se 1 (by rfl) ⟨1515257, by rfl⟩ : syracuseStep 2020343 = 3030515) B3030515
theorem B2020367 : Blo 1344991 2020367 := bstep (se 1 (by rfl) ⟨1515275, by rfl⟩ : syracuseStep 2020367 = 3030551) B3030551
theorem B3830827 : Blo 1344991 3830827 := bstep (se 1 (by rfl) ⟨2873120, by rfl⟩ : syracuseStep 3830827 = 5746241) B5746241
theorem B2020409 : Blo 1344991 2020409 := bstep (se 2 (by rfl) ⟨757653, by rfl⟩ : syracuseStep 2020409 = 1515307) B1515307
theorem B3847229 : Blo 1344991 3847229 := bstep (se 3 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 3847229 = 1442711) B1442711
theorem B5747831 : Blo 1344991 5747831 := bstep (se 1 (by rfl) ⟨4310873, by rfl⟩ : syracuseStep 5747831 = 8621747) B8621747
theorem B2045063 : Blo 1344991 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B3028103 : Blo 1344991 3028103 := bstep (se 1 (by rfl) ⟨2271077, by rfl⟩ : syracuseStep 3028103 = 4542155) B4542155
theorem B2020487 : Blo 1344991 2020487 := bstep (se 1 (by rfl) ⟨1515365, by rfl⟩ : syracuseStep 2020487 = 3030731) B3030731
theorem B7279789 : Blo 1344991 7279789 := bstep (se 3 (by rfl) ⟨1364960, by rfl⟩ : syracuseStep 7279789 = 2729921) B2729921
theorem B6812909 : Blo 1344991 6812909 := bstep (se 3 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 6812909 = 2554841) B2554841
theorem B3028283 : Blo 1344991 3028283 := bstep (se 1 (by rfl) ⟨2271212, by rfl⟩ : syracuseStep 3028283 = 4542425) B4542425
theorem B3831101 : Blo 1344991 3831101 := bstep (se 3 (by rfl) ⟨718331, by rfl⟩ : syracuseStep 3831101 = 1436663) B1436663
theorem B10909073 : Blo 1344991 10909073 := bstep (se 2 (by rfl) ⟨4090902, by rfl⟩ : syracuseStep 10909073 = 8181805) B8181805
theorem B34952627 : Blo 1344991 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B3028409 : Blo 1344991 3028409 := bstep (se 2 (by rfl) ⟨1135653, by rfl⟩ : syracuseStep 3028409 = 2271307) B2271307
theorem B2872847 : Blo 1344991 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B4314667 : Blo 1344991 4314667 := bstep (se 1 (by rfl) ⟨3236000, by rfl⟩ : syracuseStep 4314667 = 6472001) B6472001
theorem B7272023 : Blo 1344991 7272023 := bstep (se 1 (by rfl) ⟨5454017, by rfl⟩ : syracuseStep 7272023 = 10908035) B10908035
theorem B1513147 : Blo 1344991 1513147 := bstep (se 1 (by rfl) ⟨1134860, by rfl⟩ : syracuseStep 1513147 = 2269721) B2269721
theorem B3028751 : Blo 1344991 3028751 := bstep (se 1 (by rfl) ⟨2271563, by rfl⟩ : syracuseStep 3028751 = 4543127) B4543127
theorem B3028769 : Blo 1344991 3028769 := bstep (se 2 (by rfl) ⟨1135788, by rfl⟩ : syracuseStep 3028769 = 2271577) B2271577
theorem B4544315 : Blo 1344991 4544315 := bstep (se 1 (by rfl) ⟨3408236, by rfl⟩ : syracuseStep 4544315 = 6816473) B6816473
theorem B5109713 : Blo 1344991 5109713 := bstep (se 2 (by rfl) ⟨1916142, by rfl⟩ : syracuseStep 5109713 = 3832285) B3832285
theorem B7665617 : Blo 1344991 7665617 := bstep (se 2 (by rfl) ⟨2874606, by rfl⟩ : syracuseStep 7665617 = 5749213) B5749213
theorem B10917899 : Blo 1344991 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B6813719 : Blo 1344991 6813719 := bstep (se 1 (by rfl) ⟨5110289, by rfl⟩ : syracuseStep 6813719 = 10220579) B10220579
theorem B17471533 : Blo 1344991 17471533 := bstep (se 3 (by rfl) ⟨3275912, by rfl⟩ : syracuseStep 17471533 = 6551825) B6551825
theorem B21837869 : Blo 1344991 21837869 := bstep (se 3 (by rfl) ⟨4094600, by rfl⟩ : syracuseStep 21837869 = 8189201) B8189201
theorem B5748803 : Blo 1344991 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B3029111 : Blo 1344991 3029111 := bstep (se 1 (by rfl) ⟨2271833, by rfl⟩ : syracuseStep 3029111 = 4543667) B4543667
theorem B5830775 : Blo 1344991 5830775 := bstep (se 1 (by rfl) ⟨4373081, by rfl⟩ : syracuseStep 5830775 = 8746163) B8746163
theorem B3405959 : Blo 1344991 3405959 := bstep (se 1 (by rfl) ⟨2554469, by rfl⟩ : syracuseStep 3405959 = 5108939) B5108939
theorem B3831943 : Blo 1344991 3831943 := bstep (se 1 (by rfl) ⟨2873957, by rfl⟩ : syracuseStep 3831943 = 5747915) B5747915
theorem B1513615 : Blo 1344991 1513615 := bstep (se 1 (by rfl) ⟨1135211, by rfl⟩ : syracuseStep 1513615 = 2270423) B2270423
theorem B3406009 : Blo 1344991 3406009 := bstep (se 2 (by rfl) ⟨1277253, by rfl⟩ : syracuseStep 3406009 = 2554507) B2554507
theorem B4544801 : Blo 1344991 4544801 := bstep (se 2 (by rfl) ⟨1704300, by rfl⟩ : syracuseStep 4544801 = 3408601) B3408601
theorem B7280933 : Blo 1344991 7280933 := bstep (se 4 (by rfl) ⟨682587, by rfl⟩ : syracuseStep 7280933 = 1365175) B1365175
theorem B3029291 : Blo 1344991 3029291 := bstep (se 1 (by rfl) ⟨2271968, by rfl⟩ : syracuseStep 3029291 = 4543937) B4543937
theorem B3234107 : Blo 1344991 3234107 := bstep (se 1 (by rfl) ⟨2425580, by rfl⟩ : syracuseStep 3234107 = 4851161) B4851161
theorem B7879027 : Blo 1344991 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B3832217 : Blo 1344991 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B7666073 : Blo 1344991 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B1514119 : Blo 1344991 1514119 := bstep (se 1 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 1514119 = 2271179) B2271179
theorem B3029651 : Blo 1344991 3029651 := bstep (se 1 (by rfl) ⟨2272238, by rfl⟩ : syracuseStep 3029651 = 4544477) B4544477
theorem B2554553 : Blo 1344991 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B1915579 : Blo 1344991 1915579 := bstep (se 1 (by rfl) ⟨1436684, by rfl⟩ : syracuseStep 1915579 = 2873369) B2873369
theorem B3029705 : Blo 1344991 3029705 := bstep (se 2 (by rfl) ⟨1136139, by rfl⟩ : syracuseStep 3029705 = 2272279) B2272279
theorem B9214721 : Blo 1344991 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B12286721 : Blo 1344991 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B3406607 : Blo 1344991 3406607 := bstep (se 1 (by rfl) ⟨2554955, by rfl⟩ : syracuseStep 3406607 = 5109911) B5109911
theorem B11500339 : Blo 1344991 11500339 := bstep (se 1 (by rfl) ⟨8625254, by rfl⟩ : syracuseStep 11500339 = 17250509) B17250509
theorem B1514299 : Blo 1344991 1514299 := bstep (se 1 (by rfl) ⟨1135724, by rfl⟩ : syracuseStep 1514299 = 2271449) B2271449
theorem B31087475 : Blo 1344991 31087475 := bstep (se 1 (by rfl) ⟨23315606, by rfl⟩ : syracuseStep 31087475 = 46631213) B46631213
theorem B4545395 : Blo 1344991 4545395 := bstep (se 1 (by rfl) ⟨3409046, by rfl⟩ : syracuseStep 4545395 = 6818093) B6818093
theorem B3111815 : Blo 1344991 3111815 := bstep (se 1 (by rfl) ⟨2333861, by rfl⟩ : syracuseStep 3111815 = 4667723) B4667723
theorem B12934039 : Blo 1344991 12934039 := bstep (se 1 (by rfl) ⟨9700529, by rfl⟩ : syracuseStep 12934039 = 19401059) B19401059
theorem B2554895 : Blo 1344991 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B9337943 : Blo 1344991 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B1514767 : Blo 1344991 1514767 := bstep (se 1 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 1514767 = 2272151) B2272151
theorem B3030407 : Blo 1344991 3030407 := bstep (se 1 (by rfl) ⟨2272805, by rfl⟩ : syracuseStep 3030407 = 4545611) B4545611
theorem B5832089 : Blo 1344991 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B3407305 : Blo 1344991 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B29122001 : Blo 1344991 29122001 := bstep (se 2 (by rfl) ⟨10920750, by rfl⟩ : syracuseStep 29122001 = 21841501) B21841501
theorem B3833345 : Blo 1344991 3833345 := bstep (se 2 (by rfl) ⟨1437504, by rfl⟩ : syracuseStep 3833345 = 2875009) B2875009
theorem B1916473 : Blo 1344991 1916473 := bstep (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) B1437355
theorem B3030587 : Blo 1344991 3030587 := bstep (se 1 (by rfl) ⟨2272940, by rfl⟩ : syracuseStep 3030587 = 4545881) B4545881
theorem B3407447 : Blo 1344991 3407447 := bstep (se 1 (by rfl) ⟨2555585, by rfl⟩ : syracuseStep 3407447 = 5111171) B5111171
theorem B5111383 : Blo 1344991 5111383 := bstep (se 1 (by rfl) ⟨3833537, by rfl⟩ : syracuseStep 5111383 = 7667075) B7667075
theorem B24886963 : Blo 1344991 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B3030713 : Blo 1344991 3030713 := bstep (se 2 (by rfl) ⟨1136517, by rfl⟩ : syracuseStep 3030713 = 2273035) B2273035
theorem B1515271 : Blo 1344991 1515271 := bstep (se 1 (by rfl) ⟨1136453, by rfl⟩ : syracuseStep 1515271 = 2272907) B2272907
theorem B8191781 : Blo 1344991 8191781 := bstep (se 4 (by rfl) ⟨767979, by rfl⟩ : syracuseStep 8191781 = 1535959) B1535959
theorem B5824315 : Blo 1344991 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B2555707 : Blo 1344991 2555707 := bstep (se 1 (by rfl) ⟨1916780, by rfl⟩ : syracuseStep 2555707 = 3833561) B3833561
theorem B15335243 : Blo 1344991 15335243 := bstep (se 1 (by rfl) ⟨11501432, by rfl⟩ : syracuseStep 15335243 = 23002865) B23002865
theorem B6471539 : Blo 1344991 6471539 := bstep (se 1 (by rfl) ⟨4853654, by rfl⟩ : syracuseStep 6471539 = 9707309) B9707309
theorem B2555783 : Blo 1344991 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B5111687 : Blo 1344991 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B3833801 : Blo 1344991 3833801 := bstep (se 2 (by rfl) ⟨1437675, by rfl⟩ : syracuseStep 3833801 = 2875351) B2875351
theorem B18677765 : Blo 1344991 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B6815825 : Blo 1344991 6815825 := bstep (se 2 (by rfl) ⟨2555934, by rfl⟩ : syracuseStep 6815825 = 5111869) B5111869
theorem B1638599 : Blo 1344991 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B3408257 : Blo 1344991 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B2269775 : Blo 1344991 2269775 := bstep (se 1 (by rfl) ⟨1702331, by rfl⟩ : syracuseStep 2269775 = 3404663) B3404663
theorem B9700013 : Blo 1344991 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B7987897 : Blo 1344991 7987897 := bstep (se 2 (by rfl) ⟨2995461, by rfl⟩ : syracuseStep 7987897 = 5990923) B5990923
theorem B7660241 : Blo 1344991 7660241 := bstep (se 2 (by rfl) ⟨2872590, by rfl⟩ : syracuseStep 7660241 = 5745181) B5745181
theorem B15327953 : Blo 1344991 15327953 := bstep (se 2 (by rfl) ⟨5747982, by rfl⟩ : syracuseStep 15327953 = 11495965) B11495965
theorem B2564819 : Blo 1344991 2564819 := bstep (se 1 (by rfl) ⟨1923614, by rfl⟩ : syracuseStep 2564819 = 3847229) B3847229
theorem B19415821 : Blo 1344991 19415821 := bstep (se 3 (by rfl) ⟨3640466, by rfl⟩ : syracuseStep 19415821 = 7280933) B7280933
theorem B3408713 : Blo 1344991 3408713 := bstep (se 2 (by rfl) ⟨1278267, by rfl⟩ : syracuseStep 3408713 = 2556535) B2556535
theorem B8618899 : Blo 1344991 8618899 := bstep (se 1 (by rfl) ⟨6464174, by rfl⟩ : syracuseStep 8618899 = 12928349) B12928349
theorem B2556937 : Blo 1344991 2556937 := bstep (se 2 (by rfl) ⟨958851, by rfl⟩ : syracuseStep 2556937 = 1917703) B1917703
theorem B4539563 : Blo 1344991 4539563 := bstep (se 1 (by rfl) ⟨3404672, by rfl⟩ : syracuseStep 4539563 = 6809345) B6809345
theorem B3409067 : Blo 1344991 3409067 := bstep (se 1 (by rfl) ⟨2556800, by rfl⟩ : syracuseStep 3409067 = 5113601) B5113601
theorem B17245385 : Blo 1344991 17245385 := bstep (se 2 (by rfl) ⟨6467019, by rfl⟩ : syracuseStep 17245385 = 12934039) B12934039
theorem B14558579 : Blo 1344991 14558579 := bstep (se 1 (by rfl) ⟨10918934, by rfl⟩ : syracuseStep 14558579 = 21837869) B21837869
theorem B7660925 : Blo 1344991 7660925 := bstep (se 3 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 7660925 = 2872847) B2872847
theorem B18417061 : Blo 1344991 18417061 := bstep (se 4 (by rfl) ⟨1726599, by rfl⟩ : syracuseStep 18417061 = 3453199) B3453199
theorem B2270639 : Blo 1344991 2270639 := bstep (se 1 (by rfl) ⟨1702979, by rfl⟩ : syracuseStep 2270639 = 3405959) B3405959
theorem B2426287 : Blo 1344991 2426287 := bstep (se 1 (by rfl) ⟨1819715, by rfl⟩ : syracuseStep 2426287 = 3639431) B3639431
theorem B1345063 : Blo 1344991 1345063 := bstep (se 1 (by rfl) ⟨1008797, by rfl⟩ : syracuseStep 1345063 = 2017595) B2017595
theorem B4310567 : Blo 1344991 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B2156071 : Blo 1344991 2156071 := bstep (se 1 (by rfl) ⟨1617053, by rfl⟩ : syracuseStep 2156071 = 3234107) B3234107
theorem B1639975 : Blo 1344991 1639975 := bstep (se 1 (by rfl) ⟨1229981, by rfl⟩ : syracuseStep 1639975 = 2459963) B2459963
theorem B19392061 : Blo 1344991 19392061 := bstep (se 3 (by rfl) ⟨3636011, by rfl⟩ : syracuseStep 19392061 = 7272023) B7272023
theorem B1345103 : Blo 1344991 1345103 := bstep (se 1 (by rfl) ⟨1008827, by rfl⟩ : syracuseStep 1345103 = 2017655) B2017655
theorem B1345119 : Blo 1344991 1345119 := bstep (se 1 (by rfl) ⟨1008839, by rfl⟩ : syracuseStep 1345119 = 2017679) B2017679
theorem B1345147 : Blo 1344991 1345147 := bstep (se 1 (by rfl) ⟨1008860, by rfl⟩ : syracuseStep 1345147 = 2017721) B2017721
theorem B1345199 : Blo 1344991 1345199 := bstep (se 1 (by rfl) ⟨1008899, by rfl⟩ : syracuseStep 1345199 = 2017799) B2017799
theorem B4540103 : Blo 1344991 4540103 := bstep (se 1 (by rfl) ⟨3405077, by rfl⟩ : syracuseStep 4540103 = 6810155) B6810155
theorem B1345223 : Blo 1344991 1345223 := bstep (se 1 (by rfl) ⟨1008917, by rfl⟩ : syracuseStep 1345223 = 2017835) B2017835
theorem B1345243 : Blo 1344991 1345243 := bstep (se 1 (by rfl) ⟨1008932, by rfl⟩ : syracuseStep 1345243 = 2017865) B2017865
theorem B1345319 : Blo 1344991 1345319 := bstep (se 1 (by rfl) ⟨1008989, by rfl⟩ : syracuseStep 1345319 = 2017979) B2017979
theorem B7276331 : Blo 1344991 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B1345359 : Blo 1344991 1345359 := bstep (se 1 (by rfl) ⟨1009019, by rfl⟩ : syracuseStep 1345359 = 2018039) B2018039
theorem B1345375 : Blo 1344991 1345375 := bstep (se 1 (by rfl) ⟨1009031, by rfl⟩ : syracuseStep 1345375 = 2018063) B2018063
theorem B2271071 : Blo 1344991 2271071 := bstep (se 1 (by rfl) ⟨1703303, by rfl⟩ : syracuseStep 2271071 = 3406607) B3406607
theorem B1345403 : Blo 1344991 1345403 := bstep (se 1 (by rfl) ⟨1009052, by rfl⟩ : syracuseStep 1345403 = 2018105) B2018105
theorem B1345455 : Blo 1344991 1345455 := bstep (se 1 (by rfl) ⟨1009091, by rfl⟩ : syracuseStep 1345455 = 2018183) B2018183
theorem B1345479 : Blo 1344991 1345479 := bstep (se 1 (by rfl) ⟨1009109, by rfl⟩ : syracuseStep 1345479 = 2018219) B2018219
theorem B1345499 : Blo 1344991 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B14559269 : Blo 1344991 14559269 := bstep (se 4 (by rfl) ⟨1364931, by rfl⟩ : syracuseStep 14559269 = 2729863) B2729863
theorem B1345575 : Blo 1344991 1345575 := bstep (se 1 (by rfl) ⟨1009181, by rfl⟩ : syracuseStep 1345575 = 2018363) B2018363
theorem B5752889 : Blo 1344991 5752889 := bstep (se 2 (by rfl) ⟨2157333, by rfl⟩ : syracuseStep 5752889 = 4314667) B4314667
theorem B1345615 : Blo 1344991 1345615 := bstep (se 1 (by rfl) ⟨1009211, by rfl⟩ : syracuseStep 1345615 = 2018423) B2018423
theorem B1345631 : Blo 1344991 1345631 := bstep (se 1 (by rfl) ⟨1009223, by rfl⟩ : syracuseStep 1345631 = 2018447) B2018447
theorem B1345659 : Blo 1344991 1345659 := bstep (se 1 (by rfl) ⟨1009244, by rfl⟩ : syracuseStep 1345659 = 2018489) B2018489
theorem B1345711 : Blo 1344991 1345711 := bstep (se 1 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 1345711 = 2018567) B2018567
theorem B1345735 : Blo 1344991 1345735 := bstep (se 1 (by rfl) ⟨1009301, by rfl⟩ : syracuseStep 1345735 = 2018603) B2018603
theorem B1345755 : Blo 1344991 1345755 := bstep (se 1 (by rfl) ⟨1009316, by rfl⟩ : syracuseStep 1345755 = 2018633) B2018633
theorem B2017529 : Blo 1344991 2017529 := bstep (se 2 (by rfl) ⟨756573, by rfl⟩ : syracuseStep 2017529 = 1513147) B1513147
theorem B1345831 : Blo 1344991 1345831 := bstep (se 1 (by rfl) ⟨1009373, by rfl⟩ : syracuseStep 1345831 = 2018747) B2018747
theorem B1345871 : Blo 1344991 1345871 := bstep (se 1 (by rfl) ⟨1009403, by rfl⟩ : syracuseStep 1345871 = 2018807) B2018807
theorem B2017631 : Blo 1344991 2017631 := bstep (se 1 (by rfl) ⟨1513223, by rfl⟩ : syracuseStep 2017631 = 3026447) B3026447
theorem B1345887 : Blo 1344991 1345887 := bstep (se 1 (by rfl) ⟨1009415, by rfl⟩ : syracuseStep 1345887 = 2018831) B2018831
theorem B2017643 : Blo 1344991 2017643 := bstep (se 1 (by rfl) ⟨1513232, by rfl⟩ : syracuseStep 2017643 = 3026465) B3026465
theorem B1345915 : Blo 1344991 1345915 := bstep (se 1 (by rfl) ⟨1009436, by rfl⟩ : syracuseStep 1345915 = 2018873) B2018873
theorem B2271631 : Blo 1344991 2271631 := bstep (se 1 (by rfl) ⟨1703723, by rfl⟩ : syracuseStep 2271631 = 3407447) B3407447
theorem B1345967 : Blo 1344991 1345967 := bstep (se 1 (by rfl) ⟨1009475, by rfl⟩ : syracuseStep 1345967 = 2018951) B2018951
theorem B1345991 : Blo 1344991 1345991 := bstep (se 1 (by rfl) ⟨1009493, by rfl⟩ : syracuseStep 1345991 = 2018987) B2018987
theorem B1346011 : Blo 1344991 1346011 := bstep (se 1 (by rfl) ⟨1009508, by rfl⟩ : syracuseStep 1346011 = 2019017) B2019017
theorem B4540967 : Blo 1344991 4540967 := bstep (se 1 (by rfl) ⟨3405725, by rfl⟩ : syracuseStep 4540967 = 6811451) B6811451
theorem B1346087 : Blo 1344991 1346087 := bstep (se 1 (by rfl) ⟨1009565, by rfl⟩ : syracuseStep 1346087 = 2019131) B2019131
theorem B2017871 : Blo 1344991 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B1346127 : Blo 1344991 1346127 := bstep (se 1 (by rfl) ⟨1009595, by rfl⟩ : syracuseStep 1346127 = 2019191) B2019191
theorem B1346143 : Blo 1344991 1346143 := bstep (se 1 (by rfl) ⟨1009607, by rfl⟩ : syracuseStep 1346143 = 2019215) B2019215
theorem B3639905 : Blo 1344991 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B1346171 : Blo 1344991 1346171 := bstep (se 1 (by rfl) ⟨1009628, by rfl⟩ : syracuseStep 1346171 = 2019257) B2019257
theorem B3885707 : Blo 1344991 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B4541075 : Blo 1344991 4541075 := bstep (se 1 (by rfl) ⟨3405806, by rfl⟩ : syracuseStep 4541075 = 6811613) B6811613
theorem B1346223 : Blo 1344991 1346223 := bstep (se 1 (by rfl) ⟨1009667, by rfl⟩ : syracuseStep 1346223 = 2019335) B2019335
theorem B2017991 : Blo 1344991 2017991 := bstep (se 1 (by rfl) ⟨1513493, by rfl⟩ : syracuseStep 2017991 = 3026987) B3026987
theorem B1346247 : Blo 1344991 1346247 := bstep (se 1 (by rfl) ⟨1009685, by rfl⟩ : syracuseStep 1346247 = 2019371) B2019371
theorem B1346267 : Blo 1344991 1346267 := bstep (se 1 (by rfl) ⟨1009700, by rfl⟩ : syracuseStep 1346267 = 2019401) B2019401
theorem B4918009 : Blo 1344991 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B1346343 : Blo 1344991 1346343 := bstep (se 1 (by rfl) ⟨1009757, by rfl⟩ : syracuseStep 1346343 = 2019515) B2019515
theorem B1346383 : Blo 1344991 1346383 := bstep (se 1 (by rfl) ⟨1009787, by rfl⟩ : syracuseStep 1346383 = 2019575) B2019575
theorem B1346399 : Blo 1344991 1346399 := bstep (se 1 (by rfl) ⟨1009799, by rfl⟩ : syracuseStep 1346399 = 2019599) B2019599
theorem B2018153 : Blo 1344991 2018153 := bstep (se 2 (by rfl) ⟨756807, by rfl⟩ : syracuseStep 2018153 = 1513615) B1513615
theorem B4541291 : Blo 1344991 4541291 := bstep (se 1 (by rfl) ⟨3405968, by rfl⟩ : syracuseStep 4541291 = 6811937) B6811937
theorem B1346427 : Blo 1344991 1346427 := bstep (se 1 (by rfl) ⟨1009820, by rfl⟩ : syracuseStep 1346427 = 2019641) B2019641
theorem B2157455 : Blo 1344991 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B4541345 : Blo 1344991 4541345 := bstep (se 2 (by rfl) ⟨1703004, by rfl⟩ : syracuseStep 4541345 = 3406009) B3406009
theorem B1346479 : Blo 1344991 1346479 := bstep (se 1 (by rfl) ⟨1009859, by rfl⟩ : syracuseStep 1346479 = 2019719) B2019719
theorem B2018231 : Blo 1344991 2018231 := bstep (se 1 (by rfl) ⟨1513673, by rfl⟩ : syracuseStep 2018231 = 3027347) B3027347
theorem B1346503 : Blo 1344991 1346503 := bstep (se 1 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 1346503 = 2019755) B2019755
theorem B2018267 : Blo 1344991 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B1346523 : Blo 1344991 1346523 := bstep (se 1 (by rfl) ⟨1009892, by rfl⟩ : syracuseStep 1346523 = 2019785) B2019785
theorem B26225687 : Blo 1344991 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B1346599 : Blo 1344991 1346599 := bstep (se 1 (by rfl) ⟨1009949, by rfl⟩ : syracuseStep 1346599 = 2019899) B2019899
theorem B2272313 : Blo 1344991 2272313 := bstep (se 2 (by rfl) ⟨852117, by rfl⟩ : syracuseStep 2272313 = 1704235) B1704235
theorem B1346639 : Blo 1344991 1346639 := bstep (se 1 (by rfl) ⟨1009979, by rfl⟩ : syracuseStep 1346639 = 2019959) B2019959
theorem B1346655 : Blo 1344991 1346655 := bstep (se 1 (by rfl) ⟨1009991, by rfl⟩ : syracuseStep 1346655 = 2019983) B2019983
theorem B1346683 : Blo 1344991 1346683 := bstep (se 1 (by rfl) ⟨1010012, by rfl⟩ : syracuseStep 1346683 = 2020025) B2020025
theorem B10505369 : Blo 1344991 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B1346735 : Blo 1344991 1346735 := bstep (se 1 (by rfl) ⟨1010051, by rfl⟩ : syracuseStep 1346735 = 2020103) B2020103
theorem B1346759 : Blo 1344991 1346759 := bstep (se 1 (by rfl) ⟨1010069, by rfl⟩ : syracuseStep 1346759 = 2020139) B2020139
theorem B1346779 : Blo 1344991 1346779 := bstep (se 1 (by rfl) ⟨1010084, by rfl⟩ : syracuseStep 1346779 = 2020169) B2020169
theorem B58182947 : Blo 1344991 58182947 := bstep (se 1 (by rfl) ⟨43637210, by rfl⟩ : syracuseStep 58182947 = 87274421) B87274421
theorem B1346855 : Blo 1344991 1346855 := bstep (se 1 (by rfl) ⟨1010141, by rfl⟩ : syracuseStep 1346855 = 2020283) B2020283
theorem B1346895 : Blo 1344991 1346895 := bstep (se 1 (by rfl) ⟨1010171, by rfl⟩ : syracuseStep 1346895 = 2020343) B2020343
theorem B14740825 : Blo 1344991 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B1346911 : Blo 1344991 1346911 := bstep (se 1 (by rfl) ⟨1010183, by rfl⟩ : syracuseStep 1346911 = 2020367) B2020367
theorem B1346939 : Blo 1344991 1346939 := bstep (se 1 (by rfl) ⟨1010204, by rfl⟩ : syracuseStep 1346939 = 2020409) B2020409
theorem B1363375 : Blo 1344991 1363375 := bstep (se 1 (by rfl) ⟨1022531, by rfl⟩ : syracuseStep 1363375 = 2045063) B2045063
theorem B2018735 : Blo 1344991 2018735 := bstep (se 1 (by rfl) ⟨1514051, by rfl⟩ : syracuseStep 2018735 = 3028103) B3028103
theorem B1346991 : Blo 1344991 1346991 := bstep (se 1 (by rfl) ⟨1010243, by rfl⟩ : syracuseStep 1346991 = 2020487) B2020487
theorem B5746139 : Blo 1344991 5746139 := bstep (se 1 (by rfl) ⟨4309604, by rfl⟩ : syracuseStep 5746139 = 8619209) B8619209
theorem B4541939 : Blo 1344991 4541939 := bstep (se 1 (by rfl) ⟨3406454, by rfl⟩ : syracuseStep 4541939 = 6812909) B6812909
theorem B2018825 : Blo 1344991 2018825 := bstep (se 2 (by rfl) ⟨757059, by rfl⟩ : syracuseStep 2018825 = 1514119) B1514119
theorem B4091417 : Blo 1344991 4091417 := bstep (se 2 (by rfl) ⟨1534281, by rfl⟩ : syracuseStep 4091417 = 3068563) B3068563
theorem B2018855 : Blo 1344991 2018855 := bstep (se 1 (by rfl) ⟨1514141, by rfl⟩ : syracuseStep 2018855 = 3028283) B3028283
theorem B23301751 : Blo 1344991 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B3026555 : Blo 1344991 3026555 := bstep (se 1 (by rfl) ⟨2269916, by rfl⟩ : syracuseStep 3026555 = 4539833) B4539833
theorem B2018939 : Blo 1344991 2018939 := bstep (se 1 (by rfl) ⟨1514204, by rfl⟩ : syracuseStep 2018939 = 3028409) B3028409
theorem B12938885 : Blo 1344991 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B2273015 : Blo 1344991 2273015 := bstep (se 1 (by rfl) ⟨1704761, by rfl⟩ : syracuseStep 2273015 = 3409523) B3409523
theorem B3026681 : Blo 1344991 3026681 := bstep (se 2 (by rfl) ⟨1135005, by rfl⟩ : syracuseStep 3026681 = 2270011) B2270011
theorem B2019065 : Blo 1344991 2019065 := bstep (se 2 (by rfl) ⟨757149, by rfl⟩ : syracuseStep 2019065 = 1514299) B1514299
theorem B2019167 : Blo 1344991 2019167 := bstep (se 1 (by rfl) ⟨1514375, by rfl⟩ : syracuseStep 2019167 = 3028751) B3028751
theorem B2019179 : Blo 1344991 2019179 := bstep (se 1 (by rfl) ⟨1514384, by rfl⟩ : syracuseStep 2019179 = 3028769) B3028769
theorem B3026951 : Blo 1344991 3026951 := bstep (se 1 (by rfl) ⟨2270213, by rfl⟩ : syracuseStep 3026951 = 4540427) B4540427
theorem B7278599 : Blo 1344991 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B4542479 : Blo 1344991 4542479 := bstep (se 1 (by rfl) ⟨3406859, by rfl⟩ : syracuseStep 4542479 = 6813719) B6813719
theorem B5107769 : Blo 1344991 5107769 := bstep (se 2 (by rfl) ⟨1915413, by rfl⟩ : syracuseStep 5107769 = 3830827) B3830827
theorem B3027023 : Blo 1344991 3027023 := bstep (se 1 (by rfl) ⟨2270267, by rfl⟩ : syracuseStep 3027023 = 4540535) B4540535
theorem B2019407 : Blo 1344991 2019407 := bstep (se 1 (by rfl) ⟨1514555, by rfl⟩ : syracuseStep 2019407 = 3029111) B3029111
theorem B3887183 : Blo 1344991 3887183 := bstep (se 1 (by rfl) ⟨2915387, by rfl⟩ : syracuseStep 3887183 = 5830775) B5830775
theorem B10227869 : Blo 1344991 10227869 := bstep (se 3 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 10227869 = 3835451) B3835451
theorem B2019527 : Blo 1344991 2019527 := bstep (se 1 (by rfl) ⟨1514645, by rfl⟩ : syracuseStep 2019527 = 3029291) B3029291
theorem B2019689 : Blo 1344991 2019689 := bstep (se 2 (by rfl) ⟨757383, by rfl⟩ : syracuseStep 2019689 = 1514767) B1514767
theorem B11506049 : Blo 1344991 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B2019767 : Blo 1344991 2019767 := bstep (se 1 (by rfl) ⟨1514825, by rfl⟩ : syracuseStep 2019767 = 3029651) B3029651
theorem B3027419 : Blo 1344991 3027419 := bstep (se 1 (by rfl) ⟨2270564, by rfl⟩ : syracuseStep 3027419 = 4541129) B4541129
theorem B2019803 : Blo 1344991 2019803 := bstep (se 1 (by rfl) ⟨1514852, by rfl⟩ : syracuseStep 2019803 = 3029705) B3029705
theorem B4543073 : Blo 1344991 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B33182617 : Blo 1344991 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B3027887 : Blo 1344991 3027887 := bstep (se 1 (by rfl) ⟨2270915, by rfl⟩ : syracuseStep 3027887 = 4541831) B4541831
theorem B2020271 : Blo 1344991 2020271 := bstep (se 1 (by rfl) ⟨1515203, by rfl⟩ : syracuseStep 2020271 = 3030407) B3030407
theorem B3888059 : Blo 1344991 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B2020361 : Blo 1344991 2020361 := bstep (se 2 (by rfl) ⟨757635, by rfl⟩ : syracuseStep 2020361 = 1515271) B1515271
theorem B2020391 : Blo 1344991 2020391 := bstep (se 1 (by rfl) ⟨1515293, by rfl⟩ : syracuseStep 2020391 = 3030587) B3030587
theorem B2020475 : Blo 1344991 2020475 := bstep (se 1 (by rfl) ⟨1515356, by rfl⟩ : syracuseStep 2020475 = 3030713) B3030713
theorem B3028139 : Blo 1344991 3028139 := bstep (se 1 (by rfl) ⟨2271104, by rfl⟩ : syracuseStep 3028139 = 4542209) B4542209
theorem B5461187 : Blo 1344991 5461187 := bstep (se 1 (by rfl) ⟨4095890, by rfl⟩ : syracuseStep 5461187 = 8191781) B8191781
theorem B11498699 : Blo 1344991 11498699 := bstep (se 1 (by rfl) ⟨8624024, by rfl⟩ : syracuseStep 11498699 = 17248049) B17248049
theorem B4314359 : Blo 1344991 4314359 := bstep (se 1 (by rfl) ⟨3235769, by rfl⟩ : syracuseStep 4314359 = 6471539) B6471539
theorem B4314473 : Blo 1344991 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B3405199 : Blo 1344991 3405199 := bstep (se 1 (by rfl) ⟨2553899, by rfl⟩ : syracuseStep 3405199 = 5107799) B5107799
theorem B6813071 : Blo 1344991 6813071 := bstep (se 1 (by rfl) ⟨5109803, by rfl⟩ : syracuseStep 6813071 = 10219607) B10219607
theorem B23295377 : Blo 1344991 23295377 := bstep (se 2 (by rfl) ⟨8735766, by rfl⟩ : syracuseStep 23295377 = 17471533) B17471533
theorem B5109257 : Blo 1344991 5109257 := bstep (se 2 (by rfl) ⟨1915971, by rfl⟩ : syracuseStep 5109257 = 3831943) B3831943
theorem B2553383 : Blo 1344991 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B7665299 : Blo 1344991 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B3028679 : Blo 1344991 3028679 := bstep (se 1 (by rfl) ⟨2271509, by rfl⟩ : syracuseStep 3028679 = 4543019) B4543019
theorem B7280327 : Blo 1344991 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B3405523 : Blo 1344991 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B15325037 : Blo 1344991 15325037 := bstep (se 3 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 15325037 = 5746889) B5746889
theorem B1513435 : Blo 1344991 1513435 := bstep (se 1 (by rfl) ⟨1135076, by rfl⟩ : syracuseStep 1513435 = 2270153) B2270153
theorem B4544531 : Blo 1344991 4544531 := bstep (se 1 (by rfl) ⟨3408398, by rfl⟩ : syracuseStep 4544531 = 6816797) B6816797
theorem B3831887 : Blo 1344991 3831887 := bstep (se 1 (by rfl) ⟨2873915, by rfl⟩ : syracuseStep 3831887 = 5747831) B5747831
theorem B2554067 : Blo 1344991 2554067 := bstep (se 1 (by rfl) ⟨1915550, by rfl⟩ : syracuseStep 2554067 = 3831101) B3831101
theorem B2554105 : Blo 1344991 2554105 := bstep (se 2 (by rfl) ⟨957789, by rfl⟩ : syracuseStep 2554105 = 1915579) B1915579
theorem B7272715 : Blo 1344991 7272715 := bstep (se 1 (by rfl) ⟨5454536, by rfl⟩ : syracuseStep 7272715 = 10909073) B10909073
theorem B4544855 : Blo 1344991 4544855 := bstep (se 1 (by rfl) ⟨3408641, by rfl⟩ : syracuseStep 4544855 = 6817283) B6817283
theorem B15333785 : Blo 1344991 15333785 := bstep (se 2 (by rfl) ⟨5750169, by rfl⟩ : syracuseStep 15333785 = 11500339) B11500339
theorem B1513903 : Blo 1344991 1513903 := bstep (se 1 (by rfl) ⟨1135427, by rfl⟩ : syracuseStep 1513903 = 2270855) B2270855
theorem B2021897 : Blo 1344991 2021897 := bstep (se 2 (by rfl) ⟨758211, by rfl⟩ : syracuseStep 2021897 = 1516423) B1516423
theorem B3029543 : Blo 1344991 3029543 := bstep (se 1 (by rfl) ⟨2272157, by rfl⟩ : syracuseStep 3029543 = 4544315) B4544315
theorem B3406475 : Blo 1344991 3406475 := bstep (se 1 (by rfl) ⟨2554856, by rfl⟩ : syracuseStep 3406475 = 5109713) B5109713
theorem B5110411 : Blo 1344991 5110411 := bstep (se 1 (by rfl) ⟨3832808, by rfl⟩ : syracuseStep 5110411 = 7665617) B7665617
theorem B3832535 : Blo 1344991 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B27622133 : Blo 1344991 27622133 := bstep (se 5 (by rfl) ⟨1294787, by rfl⟩ : syracuseStep 27622133 = 2589575) B2589575
theorem B1514335 : Blo 1344991 1514335 := bstep (se 1 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 1514335 = 2271503) B2271503
theorem B3029867 : Blo 1344991 3029867 := bstep (se 1 (by rfl) ⟨2272400, by rfl⟩ : syracuseStep 3029867 = 4544801) B4544801
theorem B9706385 : Blo 1344991 9706385 := bstep (se 2 (by rfl) ⟨3639894, by rfl⟩ : syracuseStep 9706385 = 7279789) B7279789
theorem B3029921 : Blo 1344991 3029921 := bstep (se 2 (by rfl) ⟨1136220, by rfl⟩ : syracuseStep 3029921 = 2272441) B2272441
theorem B2554811 : Blo 1344991 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B5110715 : Blo 1344991 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B1383367 : Blo 1344991 1383367 := bstep (se 1 (by rfl) ⟨1037525, by rfl⟩ : syracuseStep 1383367 = 2075051) B2075051
theorem B1703035 : Blo 1344991 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B6143147 : Blo 1344991 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B8191147 : Blo 1344991 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B11066561 : Blo 1344991 11066561 := bstep (se 2 (by rfl) ⟨4149960, by rfl⟩ : syracuseStep 11066561 = 8299921) B8299921
theorem B1514695 : Blo 1344991 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B20724983 : Blo 1344991 20724983 := bstep (se 1 (by rfl) ⟨15543737, by rfl⟩ : syracuseStep 20724983 = 31087475) B31087475
theorem B3030263 : Blo 1344991 3030263 := bstep (se 1 (by rfl) ⟨2272697, by rfl⟩ : syracuseStep 3030263 = 4545395) B4545395
theorem B1703263 : Blo 1344991 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B6225295 : Blo 1344991 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B4545935 : Blo 1344991 4545935 := bstep (se 1 (by rfl) ⟨3409451, by rfl⟩ : syracuseStep 4545935 = 6818903) B6818903
theorem B2555297 : Blo 1344991 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B6815177 : Blo 1344991 6815177 := bstep (se 2 (by rfl) ⟨2555691, by rfl⟩ : syracuseStep 6815177 = 5111383) B5111383
theorem B19414667 : Blo 1344991 19414667 := bstep (se 1 (by rfl) ⟨14561000, by rfl⟩ : syracuseStep 19414667 = 29122001) B29122001
theorem B2555563 : Blo 1344991 2555563 := bstep (se 1 (by rfl) ⟨1916672, by rfl⟩ : syracuseStep 2555563 = 3833345) B3833345
theorem B8298173 : Blo 1344991 8298173 := bstep (se 3 (by rfl) ⟨1555907, by rfl⟩ : syracuseStep 8298173 = 3111815) B3111815
theorem B7765753 : Blo 1344991 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B3407609 : Blo 1344991 3407609 := bstep (se 2 (by rfl) ⟨1277853, by rfl⟩ : syracuseStep 3407609 = 2555707) B2555707
theorem B2727787 : Blo 1344991 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B10223495 : Blo 1344991 10223495 := bstep (se 1 (by rfl) ⟨7667621, by rfl⟩ : syracuseStep 10223495 = 15335243) B15335243
theorem B1703855 : Blo 1344991 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B3407791 : Blo 1344991 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B2555867 : Blo 1344991 2555867 := bstep (se 1 (by rfl) ⟨1916900, by rfl⟩ : syracuseStep 2555867 = 3833801) B3833801
theorem B12451843 : Blo 1344991 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2876239 : Blo 1344991 2876239 := bstep (se 1 (by rfl) ⟨2157179, by rfl⟩ : syracuseStep 2876239 = 4314359) B4314359
theorem B2876315 : Blo 1344991 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B10650529 : Blo 1344991 10650529 := bstep (se 2 (by rfl) ⟨3993948, by rfl⟩ : syracuseStep 10650529 = 7987897) B7987897
theorem B25887761 : Blo 1344991 25887761 := bstep (se 2 (by rfl) ⟨9707910, by rfl⟩ : syracuseStep 25887761 = 19415821) B19415821
theorem B4850887 : Blo 1344991 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B10216691 : Blo 1344991 10216691 := bstep (se 1 (by rfl) ⟨7662518, by rfl⟩ : syracuseStep 10216691 = 15325037) B15325037
theorem B1844489 : Blo 1344991 1844489 := bstep (se 2 (by rfl) ⟨691683, by rfl⟩ : syracuseStep 1844489 = 1383367) B1383367
theorem B3409249 : Blo 1344991 3409249 := bstep (se 2 (by rfl) ⟨1278468, by rfl⟩ : syracuseStep 3409249 = 2556937) B2556937
theorem B3835259 : Blo 1344991 3835259 := bstep (se 1 (by rfl) ⟨2876444, by rfl⟩ : syracuseStep 3835259 = 5752889) B5752889
theorem B6809021 : Blo 1344991 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B2270713 : Blo 1344991 2270713 := bstep (se 2 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 2270713 = 1703035) B1703035
theorem B1345019 : Blo 1344991 1345019 := bstep (se 1 (by rfl) ⟨1008764, by rfl⟩ : syracuseStep 1345019 = 2017529) B2017529
theorem B10921529 : Blo 1344991 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B1345087 : Blo 1344991 1345087 := bstep (se 1 (by rfl) ⟨1008815, by rfl⟩ : syracuseStep 1345087 = 2017631) B2017631
theorem B1345095 : Blo 1344991 1345095 := bstep (se 1 (by rfl) ⟨1008821, by rfl⟩ : syracuseStep 1345095 = 2017643) B2017643
theorem B1345247 : Blo 1344991 1345247 := bstep (se 1 (by rfl) ⟨1008935, by rfl⟩ : syracuseStep 1345247 = 2017871) B2017871
theorem B2426603 : Blo 1344991 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B2270983 : Blo 1344991 2270983 := bstep (se 1 (by rfl) ⟨1703237, by rfl⟩ : syracuseStep 2270983 = 3406475) B3406475
theorem B2590471 : Blo 1344991 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B19654433 : Blo 1344991 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B2271017 : Blo 1344991 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B1345327 : Blo 1344991 1345327 := bstep (se 1 (by rfl) ⟨1008995, by rfl⟩ : syracuseStep 1345327 = 2017991) B2017991
theorem B22128461 : Blo 1344991 22128461 := bstep (se 3 (by rfl) ⟨4149086, by rfl⟩ : syracuseStep 22128461 = 8298173) B8298173
theorem B4540265 : Blo 1344991 4540265 := bstep (se 2 (by rfl) ⟨1702599, by rfl⟩ : syracuseStep 4540265 = 3405199) B3405199
theorem B8300393 : Blo 1344991 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B1345435 : Blo 1344991 1345435 := bstep (se 1 (by rfl) ⟨1009076, by rfl⟩ : syracuseStep 1345435 = 2018153) B2018153
theorem B1345487 : Blo 1344991 1345487 := bstep (se 1 (by rfl) ⟨1009115, by rfl⟩ : syracuseStep 1345487 = 2018231) B2018231
theorem B1345511 : Blo 1344991 1345511 := bstep (se 1 (by rfl) ⟨1009133, by rfl⟩ : syracuseStep 1345511 = 2018267) B2018267
theorem B17483791 : Blo 1344991 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B25856081 : Blo 1344991 25856081 := bstep (se 2 (by rfl) ⟨9696030, by rfl⟩ : syracuseStep 25856081 = 19392061) B19392061
theorem B4540697 : Blo 1344991 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B1345823 : Blo 1344991 1345823 := bstep (se 1 (by rfl) ⟨1009367, by rfl⟩ : syracuseStep 1345823 = 2018735) B2018735
theorem B1345883 : Blo 1344991 1345883 := bstep (se 1 (by rfl) ⟨1009412, by rfl⟩ : syracuseStep 1345883 = 2018825) B2018825
theorem B1345903 : Blo 1344991 1345903 := bstep (se 1 (by rfl) ⟨1009427, by rfl⟩ : syracuseStep 1345903 = 2018855) B2018855
theorem B5753213 : Blo 1344991 5753213 := bstep (se 3 (by rfl) ⟨1078727, by rfl⟩ : syracuseStep 5753213 = 2157455) B2157455
theorem B2017703 : Blo 1344991 2017703 := bstep (se 1 (by rfl) ⟨1513277, by rfl⟩ : syracuseStep 2017703 = 3026555) B3026555
theorem B1345959 : Blo 1344991 1345959 := bstep (se 1 (by rfl) ⟨1009469, by rfl⟩ : syracuseStep 1345959 = 2018939) B2018939
theorem B2017787 : Blo 1344991 2017787 := bstep (se 1 (by rfl) ⟨1513340, by rfl⟩ : syracuseStep 2017787 = 3026681) B3026681
theorem B1346043 : Blo 1344991 1346043 := bstep (se 1 (by rfl) ⟨1009532, by rfl⟩ : syracuseStep 1346043 = 2019065) B2019065
theorem B2271739 : Blo 1344991 2271739 := bstep (se 1 (by rfl) ⟨1703804, by rfl⟩ : syracuseStep 2271739 = 3407609) B3407609
theorem B1346111 : Blo 1344991 1346111 := bstep (se 1 (by rfl) ⟨1009583, by rfl⟩ : syracuseStep 1346111 = 2019167) B2019167
theorem B1346119 : Blo 1344991 1346119 := bstep (se 1 (by rfl) ⟨1009589, by rfl⟩ : syracuseStep 1346119 = 2019179) B2019179
theorem B2017913 : Blo 1344991 2017913 := bstep (se 2 (by rfl) ⟨756717, by rfl⟩ : syracuseStep 2017913 = 1513435) B1513435
theorem B2017967 : Blo 1344991 2017967 := bstep (se 1 (by rfl) ⟨1513475, by rfl⟩ : syracuseStep 2017967 = 3026951) B3026951
theorem B4852399 : Blo 1344991 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B2018015 : Blo 1344991 2018015 := bstep (se 1 (by rfl) ⟨1513511, by rfl⟩ : syracuseStep 2018015 = 3027023) B3027023
theorem B1346271 : Blo 1344991 1346271 := bstep (se 1 (by rfl) ⟨1009703, by rfl⟩ : syracuseStep 1346271 = 2019407) B2019407
theorem B2591455 : Blo 1344991 2591455 := bstep (se 1 (by rfl) ⟨1943591, by rfl⟩ : syracuseStep 2591455 = 3887183) B3887183
theorem B38824717 : Blo 1344991 38824717 := bstep (se 3 (by rfl) ⟨7279634, by rfl⟩ : syracuseStep 38824717 = 14559269) B14559269
theorem B6818579 : Blo 1344991 6818579 := bstep (se 1 (by rfl) ⟨5113934, by rfl⟩ : syracuseStep 6818579 = 10227869) B10227869
theorem B1346351 : Blo 1344991 1346351 := bstep (se 1 (by rfl) ⟨1009763, by rfl⟩ : syracuseStep 1346351 = 2019527) B2019527
theorem B1346459 : Blo 1344991 1346459 := bstep (se 1 (by rfl) ⟨1009844, by rfl⟩ : syracuseStep 1346459 = 2019689) B2019689
theorem B2272171 : Blo 1344991 2272171 := bstep (se 1 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 2272171 = 3408257) B3408257
theorem B7670699 : Blo 1344991 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B1346511 : Blo 1344991 1346511 := bstep (se 1 (by rfl) ⟨1009883, by rfl⟩ : syracuseStep 1346511 = 2019767) B2019767
theorem B2018279 : Blo 1344991 2018279 := bstep (se 1 (by rfl) ⟨1513709, by rfl⟩ : syracuseStep 2018279 = 3027419) B3027419
theorem B1346535 : Blo 1344991 1346535 := bstep (se 1 (by rfl) ⟨1009901, by rfl⟩ : syracuseStep 1346535 = 2019803) B2019803
theorem B6466675 : Blo 1344991 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B5106827 : Blo 1344991 5106827 := bstep (se 1 (by rfl) ⟨3830120, by rfl⟩ : syracuseStep 5106827 = 7660241) B7660241
theorem B10218635 : Blo 1344991 10218635 := bstep (se 1 (by rfl) ⟨7663976, by rfl⟩ : syracuseStep 10218635 = 15327953) B15327953
theorem B2272475 : Blo 1344991 2272475 := bstep (se 1 (by rfl) ⟨1704356, by rfl⟩ : syracuseStep 2272475 = 3408713) B3408713
theorem B2018537 : Blo 1344991 2018537 := bstep (se 2 (by rfl) ⟨756951, by rfl⟩ : syracuseStep 2018537 = 1513903) B1513903
theorem B2018591 : Blo 1344991 2018591 := bstep (se 1 (by rfl) ⟨1513943, by rfl⟩ : syracuseStep 2018591 = 3027887) B3027887
theorem B1346847 : Blo 1344991 1346847 := bstep (se 1 (by rfl) ⟨1010135, by rfl⟩ : syracuseStep 1346847 = 2020271) B2020271
theorem B1346907 : Blo 1344991 1346907 := bstep (se 1 (by rfl) ⟨1010180, by rfl⟩ : syracuseStep 1346907 = 2020361) B2020361
theorem B1346927 : Blo 1344991 1346927 := bstep (se 1 (by rfl) ⟨1010195, by rfl⟩ : syracuseStep 1346927 = 2020391) B2020391
theorem B1346983 : Blo 1344991 1346983 := bstep (se 1 (by rfl) ⟨1010237, by rfl⟩ : syracuseStep 1346983 = 2020475) B2020475
theorem B3026375 : Blo 1344991 3026375 := bstep (se 1 (by rfl) ⟨2269781, by rfl⟩ : syracuseStep 3026375 = 4539563) B4539563
theorem B2018759 : Blo 1344991 2018759 := bstep (se 1 (by rfl) ⟨1514069, by rfl⟩ : syracuseStep 2018759 = 3028139) B3028139
theorem B2272711 : Blo 1344991 2272711 := bstep (se 1 (by rfl) ⟨1704533, by rfl⟩ : syracuseStep 2272711 = 3409067) B3409067
theorem B11496923 : Blo 1344991 11496923 := bstep (se 1 (by rfl) ⟨8622692, by rfl⟩ : syracuseStep 11496923 = 17245385) B17245385
theorem B5107283 : Blo 1344991 5107283 := bstep (se 1 (by rfl) ⟨3830462, by rfl⟩ : syracuseStep 5107283 = 7660925) B7660925
theorem B4542047 : Blo 1344991 4542047 := bstep (se 1 (by rfl) ⟨3406535, by rfl⟩ : syracuseStep 4542047 = 6813071) B6813071
theorem B6557345 : Blo 1344991 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B2019113 : Blo 1344991 2019113 := bstep (se 2 (by rfl) ⟨757167, by rfl⟩ : syracuseStep 2019113 = 1514335) B1514335
theorem B3026735 : Blo 1344991 3026735 := bstep (se 1 (by rfl) ⟨2270051, by rfl⟩ : syracuseStep 3026735 = 4540103) B4540103
theorem B2019119 : Blo 1344991 2019119 := bstep (se 1 (by rfl) ⟨1514339, by rfl⟩ : syracuseStep 2019119 = 3028679) B3028679
theorem B2019593 : Blo 1344991 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B1347931 : Blo 1344991 1347931 := bstep (se 1 (by rfl) ⟨1010948, by rfl⟩ : syracuseStep 1347931 = 2021897) B2021897
theorem B3027311 : Blo 1344991 3027311 := bstep (se 1 (by rfl) ⟨2270483, by rfl⟩ : syracuseStep 3027311 = 4540967) B4540967
theorem B2019695 : Blo 1344991 2019695 := bstep (se 1 (by rfl) ⟨1514771, by rfl⟩ : syracuseStep 2019695 = 3029543) B3029543
theorem B3027383 : Blo 1344991 3027383 := bstep (se 1 (by rfl) ⟨2270537, by rfl⟩ : syracuseStep 3027383 = 4541075) B4541075
theorem B24556081 : Blo 1344991 24556081 := bstep (se 2 (by rfl) ⟨9208530, by rfl⟩ : syracuseStep 24556081 = 18417061) B18417061
theorem B10220093 : Blo 1344991 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B3027527 : Blo 1344991 3027527 := bstep (se 1 (by rfl) ⟨2270645, by rfl⟩ : syracuseStep 3027527 = 4541291) B4541291
theorem B2019911 : Blo 1344991 2019911 := bstep (se 1 (by rfl) ⟨1514933, by rfl⟩ : syracuseStep 2019911 = 3029867) B3029867
theorem B3027563 : Blo 1344991 3027563 := bstep (se 1 (by rfl) ⟨2270672, by rfl⟩ : syracuseStep 3027563 = 4541345) B4541345
theorem B2019947 : Blo 1344991 2019947 := bstep (se 1 (by rfl) ⟨1514960, by rfl⟩ : syracuseStep 2019947 = 3029921) B3029921
theorem B17478389 : Blo 1344991 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B7377707 : Blo 1344991 7377707 := bstep (se 1 (by rfl) ⟨5533280, by rfl⟩ : syracuseStep 7377707 = 11066561) B11066561
theorem B31069001 : Blo 1344991 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B13816655 : Blo 1344991 13816655 := bstep (se 1 (by rfl) ⟨10362491, by rfl⟩ : syracuseStep 13816655 = 20724983) B20724983
theorem B2020175 : Blo 1344991 2020175 := bstep (se 1 (by rfl) ⟨1515131, by rfl⟩ : syracuseStep 2020175 = 3030263) B3030263
theorem B58192789 : Blo 1344991 58192789 := bstep (se 6 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 58192789 = 2727787) B2727787
theorem B4543451 : Blo 1344991 4543451 := bstep (se 1 (by rfl) ⟨3407588, by rfl⟩ : syracuseStep 4543451 = 6815177) B6815177
theorem B3830759 : Blo 1344991 3830759 := bstep (se 1 (by rfl) ⟨2873069, by rfl⟩ : syracuseStep 3830759 = 5746139) B5746139
theorem B3027959 : Blo 1344991 3027959 := bstep (se 1 (by rfl) ⟨2270969, by rfl⟩ : syracuseStep 3027959 = 4541939) B4541939
theorem B4543613 : Blo 1344991 4543613 := bstep (se 3 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 4543613 = 1703855) B1703855
theorem B10368157 : Blo 1344991 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B4543721 : Blo 1344991 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B3028319 : Blo 1344991 3028319 := bstep (se 1 (by rfl) ⟨2271239, by rfl⟩ : syracuseStep 3028319 = 4542479) B4542479
theorem B3405179 : Blo 1344991 3405179 := bstep (se 1 (by rfl) ⟨2553884, by rfl⟩ : syracuseStep 3405179 = 5107769) B5107769
theorem B4543883 : Blo 1344991 4543883 := bstep (se 1 (by rfl) ⟨3407912, by rfl⟩ : syracuseStep 4543883 = 6815825) B6815825
theorem B3405473 : Blo 1344991 3405473 := bstep (se 2 (by rfl) ⟨1277052, by rfl⟩ : syracuseStep 3405473 = 2554105) B2554105
theorem B9696953 : Blo 1344991 9696953 := bstep (se 2 (by rfl) ⟨3636357, by rfl⟩ : syracuseStep 9696953 = 7272715) B7272715
theorem B1513183 : Blo 1344991 1513183 := bstep (se 1 (by rfl) ⟨1134887, by rfl⟩ : syracuseStep 1513183 = 2269775) B2269775
theorem B3028715 : Blo 1344991 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B1709879 : Blo 1344991 1709879 := bstep (se 1 (by rfl) ⟨1282409, by rfl⟩ : syracuseStep 1709879 = 2564819) B2564819
theorem B14563165 : Blo 1344991 14563165 := bstep (se 3 (by rfl) ⟨2730593, by rfl⟩ : syracuseStep 14563165 = 5461187) B5461187
theorem B3028841 : Blo 1344991 3028841 := bstep (se 2 (by rfl) ⟨1135815, by rfl⟩ : syracuseStep 3028841 = 2271631) B2271631
theorem B7665799 : Blo 1344991 7665799 := bstep (se 1 (by rfl) ⟨5749349, by rfl⟩ : syracuseStep 7665799 = 11498699) B11498699
theorem B6813881 : Blo 1344991 6813881 := bstep (se 2 (by rfl) ⟨2555205, by rfl⟩ : syracuseStep 6813881 = 5110411) B5110411
theorem B9705719 : Blo 1344991 9705719 := bstep (se 1 (by rfl) ⟨7279289, by rfl⟩ : syracuseStep 9705719 = 14558579) B14558579
theorem B15530251 : Blo 1344991 15530251 := bstep (se 1 (by rfl) ⟨11647688, by rfl⟩ : syracuseStep 15530251 = 23295377) B23295377
theorem B1513759 : Blo 1344991 1513759 := bstep (se 1 (by rfl) ⟨1135319, by rfl⟩ : syracuseStep 1513759 = 2270639) B2270639
theorem B3406171 : Blo 1344991 3406171 := bstep (se 1 (by rfl) ⟨2554628, by rfl⟩ : syracuseStep 3406171 = 5109257) B5109257
theorem B2873711 : Blo 1344991 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B5110199 : Blo 1344991 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B11491865 : Blo 1344991 11491865 := bstep (se 2 (by rfl) ⟨4309449, by rfl⟩ : syracuseStep 11491865 = 8618899) B8618899
theorem B44243489 : Blo 1344991 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B1514047 : Blo 1344991 1514047 := bstep (se 1 (by rfl) ⟨1135535, by rfl⟩ : syracuseStep 1514047 = 2271071) B2271071
theorem B3029687 : Blo 1344991 3029687 := bstep (se 1 (by rfl) ⟨2272265, by rfl⟩ : syracuseStep 3029687 = 4544531) B4544531
theorem B2554591 : Blo 1344991 2554591 := bstep (se 1 (by rfl) ⟨1915943, by rfl⟩ : syracuseStep 2554591 = 3831887) B3831887
theorem B1702711 : Blo 1344991 1702711 := bstep (se 1 (by rfl) ⟨1277033, by rfl⟩ : syracuseStep 1702711 = 2554067) B2554067
theorem B3029903 : Blo 1344991 3029903 := bstep (se 1 (by rfl) ⟨2272427, by rfl⟩ : syracuseStep 3029903 = 4544855) B4544855
theorem B10222523 : Blo 1344991 10222523 := bstep (se 1 (by rfl) ⟨7666892, by rfl⟩ : syracuseStep 10222523 = 15333785) B15333785
theorem B18414755 : Blo 1344991 18414755 := bstep (se 1 (by rfl) ⟨13811066, by rfl⟩ : syracuseStep 18414755 = 27622133) B27622133
theorem B19414205 : Blo 1344991 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B1817833 : Blo 1344991 1817833 := bstep (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) B1363375
theorem B3235049 : Blo 1344991 3235049 := bstep (se 2 (by rfl) ⟨1213143, by rfl⟩ : syracuseStep 3235049 = 2426287) B2426287
theorem B6470923 : Blo 1344991 6470923 := bstep (se 1 (by rfl) ⟨4853192, by rfl⟩ : syracuseStep 6470923 = 9706385) B9706385
theorem B1703207 : Blo 1344991 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B3407143 : Blo 1344991 3407143 := bstep (se 1 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 3407143 = 5110715) B5110715
theorem B1514875 : Blo 1344991 1514875 := bstep (se 1 (by rfl) ⟨1136156, by rfl⟩ : syracuseStep 1514875 = 2272313) B2272313
theorem B2874761 : Blo 1344991 2874761 := bstep (se 2 (by rfl) ⟨1078035, by rfl⟩ : syracuseStep 2874761 = 2156071) B2156071
theorem B2186633 : Blo 1344991 2186633 := bstep (se 2 (by rfl) ⟨819987, by rfl⟩ : syracuseStep 2186633 = 1639975) B1639975
theorem B7003579 : Blo 1344991 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B4095431 : Blo 1344991 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B38788631 : Blo 1344991 38788631 := bstep (se 1 (by rfl) ⟨29091473, by rfl⟩ : syracuseStep 38788631 = 58182947) B58182947
theorem B3407417 : Blo 1344991 3407417 := bstep (se 2 (by rfl) ⟨1277781, by rfl⟩ : syracuseStep 3407417 = 2555563) B2555563
theorem B3030623 : Blo 1344991 3030623 := bstep (se 1 (by rfl) ⟨2272967, by rfl⟩ : syracuseStep 3030623 = 4545935) B4545935
theorem B1703531 : Blo 1344991 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B10354337 : Blo 1344991 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B2727611 : Blo 1344991 2727611 := bstep (se 1 (by rfl) ⟨2045708, by rfl⟩ : syracuseStep 2727611 = 4091417) B4091417
theorem B8625923 : Blo 1344991 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B12943111 : Blo 1344991 12943111 := bstep (se 1 (by rfl) ⟨9707333, by rfl⟩ : syracuseStep 12943111 = 19414667) B19414667
theorem B1515343 : Blo 1344991 1515343 := bstep (se 1 (by rfl) ⟨1136507, by rfl⟩ : syracuseStep 1515343 = 2273015) B2273015
theorem B6815663 : Blo 1344991 6815663 := bstep (se 1 (by rfl) ⟨5111747, by rfl⟩ : syracuseStep 6815663 = 10223495) B10223495
theorem B1703911 : Blo 1344991 1703911 := bstep (se 1 (by rfl) ⟨1277933, by rfl⟩ : syracuseStep 1703911 = 2555867) B2555867
theorem B2270119 : Blo 1344991 2270119 := bstep (se 1 (by rfl) ⟨1702589, by rfl⟩ : syracuseStep 2270119 = 3405179) B3405179
theorem B2556839 : Blo 1344991 2556839 := bstep (se 1 (by rfl) ⟨1917629, by rfl⟩ : syracuseStep 2556839 = 3835259) B3835259
theorem B4539347 : Blo 1344991 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B51766289 : Blo 1344991 51766289 := bstep (se 2 (by rfl) ⟨19412358, by rfl⟩ : syracuseStep 51766289 = 38824717) B38824717
theorem B2270281 : Blo 1344991 2270281 := bstep (se 2 (by rfl) ⟨851355, by rfl⟩ : syracuseStep 2270281 = 1702711) B1702711
theorem B3834985 : Blo 1344991 3834985 := bstep (se 2 (by rfl) ⟨1438119, by rfl⟩ : syracuseStep 3834985 = 2876239) B2876239
theorem B2270315 : Blo 1344991 2270315 := bstep (se 1 (by rfl) ⟨1702736, by rfl⟩ : syracuseStep 2270315 = 3405473) B3405473
theorem B17237387 : Blo 1344991 17237387 := bstep (se 1 (by rfl) ⟨12928040, by rfl⟩ : syracuseStep 17237387 = 25856081) B25856081
theorem B3835475 : Blo 1344991 3835475 := bstep (se 1 (by rfl) ⟨2876606, by rfl⟩ : syracuseStep 3835475 = 5753213) B5753213
theorem B1345135 : Blo 1344991 1345135 := bstep (se 1 (by rfl) ⟨1008851, by rfl⟩ : syracuseStep 1345135 = 2017703) B2017703
theorem B1345191 : Blo 1344991 1345191 := bstep (se 1 (by rfl) ⟨1008893, by rfl⟩ : syracuseStep 1345191 = 2017787) B2017787
theorem B8627897 : Blo 1344991 8627897 := bstep (se 2 (by rfl) ⟨3235461, by rfl⟩ : syracuseStep 8627897 = 6470923) B6470923
theorem B7661243 : Blo 1344991 7661243 := bstep (se 1 (by rfl) ⟨5745932, by rfl⟩ : syracuseStep 7661243 = 11491865) B11491865
theorem B1345275 : Blo 1344991 1345275 := bstep (se 1 (by rfl) ⟨1008956, by rfl⟩ : syracuseStep 1345275 = 2017913) B2017913
theorem B1345311 : Blo 1344991 1345311 := bstep (se 1 (by rfl) ⟨1008983, by rfl⟩ : syracuseStep 1345311 = 2017967) B2017967
theorem B1345343 : Blo 1344991 1345343 := bstep (se 1 (by rfl) ⟨1009007, by rfl⟩ : syracuseStep 1345343 = 2018015) B2018015
theorem B5113799 : Blo 1344991 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B1345519 : Blo 1344991 1345519 := bstep (se 1 (by rfl) ⟨1009139, by rfl⟩ : syracuseStep 1345519 = 2018279) B2018279
theorem B1345691 : Blo 1344991 1345691 := bstep (se 1 (by rfl) ⟨1009268, by rfl⟩ : syracuseStep 1345691 = 2018537) B2018537
theorem B2156699 : Blo 1344991 2156699 := bstep (se 1 (by rfl) ⟨1617524, by rfl⟩ : syracuseStep 2156699 = 3235049) B3235049
theorem B1345727 : Blo 1344991 1345727 := bstep (se 1 (by rfl) ⟨1009295, by rfl⟩ : syracuseStep 1345727 = 2018591) B2018591
theorem B2017577 : Blo 1344991 2017577 := bstep (se 2 (by rfl) ⟨756591, by rfl⟩ : syracuseStep 2017577 = 1513183) B1513183
theorem B2017583 : Blo 1344991 2017583 := bstep (se 1 (by rfl) ⟨1513187, by rfl⟩ : syracuseStep 2017583 = 3026375) B3026375
theorem B1345839 : Blo 1344991 1345839 := bstep (se 1 (by rfl) ⟨1009379, by rfl⟩ : syracuseStep 1345839 = 2018759) B2018759
theorem B2730287 : Blo 1344991 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B2271611 : Blo 1344991 2271611 := bstep (se 1 (by rfl) ⟨1703708, by rfl⟩ : syracuseStep 2271611 = 3407417) B3407417
theorem B7670173 : Blo 1344991 7670173 := bstep (se 3 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 7670173 = 2876315) B2876315
theorem B19417553 : Blo 1344991 19417553 := bstep (se 2 (by rfl) ⟨7281582, by rfl⟩ : syracuseStep 19417553 = 14563165) B14563165
theorem B1346075 : Blo 1344991 1346075 := bstep (se 1 (by rfl) ⟨1009556, by rfl⟩ : syracuseStep 1346075 = 2019113) B2019113
theorem B2017823 : Blo 1344991 2017823 := bstep (se 1 (by rfl) ⟨1513367, by rfl⟩ : syracuseStep 2017823 = 3026735) B3026735
theorem B1346079 : Blo 1344991 1346079 := bstep (se 1 (by rfl) ⟨1009559, by rfl⟩ : syracuseStep 1346079 = 2019119) B2019119
theorem B2271881 : Blo 1344991 2271881 := bstep (se 2 (by rfl) ⟨851955, by rfl⟩ : syracuseStep 2271881 = 1703911) B1703911
theorem B1346395 : Blo 1344991 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B2018207 : Blo 1344991 2018207 := bstep (se 1 (by rfl) ⟨1513655, by rfl⟩ : syracuseStep 2018207 = 3027311) B3027311
theorem B1346463 : Blo 1344991 1346463 := bstep (se 1 (by rfl) ⟨1009847, by rfl⟩ : syracuseStep 1346463 = 2019695) B2019695
theorem B2018255 : Blo 1344991 2018255 := bstep (se 1 (by rfl) ⟨1513691, by rfl⟩ : syracuseStep 2018255 = 3027383) B3027383
theorem B2018345 : Blo 1344991 2018345 := bstep (se 2 (by rfl) ⟨756879, by rfl⟩ : syracuseStep 2018345 = 1513759) B1513759
theorem B2018351 : Blo 1344991 2018351 := bstep (se 1 (by rfl) ⟨1513763, by rfl⟩ : syracuseStep 2018351 = 3027527) B3027527
theorem B1346607 : Blo 1344991 1346607 := bstep (se 1 (by rfl) ⟨1009955, by rfl⟩ : syracuseStep 1346607 = 2019911) B2019911
theorem B2018375 : Blo 1344991 2018375 := bstep (se 1 (by rfl) ⟨1513781, by rfl⟩ : syracuseStep 2018375 = 3027563) B3027563
theorem B1346631 : Blo 1344991 1346631 := bstep (se 1 (by rfl) ⟨1009973, by rfl⟩ : syracuseStep 1346631 = 2019947) B2019947
theorem B4541561 : Blo 1344991 4541561 := bstep (se 2 (by rfl) ⟨1703085, by rfl⟩ : syracuseStep 4541561 = 3406171) B3406171
theorem B20712667 : Blo 1344991 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B9211103 : Blo 1344991 9211103 := bstep (se 1 (by rfl) ⟨6908327, by rfl⟩ : syracuseStep 9211103 = 13816655) B13816655
theorem B1346783 : Blo 1344991 1346783 := bstep (se 1 (by rfl) ⟨1010087, by rfl⟩ : syracuseStep 1346783 = 2020175) B2020175
theorem B18238709 : Blo 1344991 18238709 := bstep (se 5 (by rfl) ⟨854939, by rfl⟩ : syracuseStep 18238709 = 1709879) B1709879
theorem B2018639 : Blo 1344991 2018639 := bstep (se 1 (by rfl) ⟨1513979, by rfl⟩ : syracuseStep 2018639 = 3027959) B3027959
theorem B4918637 : Blo 1344991 4918637 := bstep (se 3 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 4918637 = 1844489) B1844489
theorem B2018729 : Blo 1344991 2018729 := bstep (se 2 (by rfl) ⟨757023, by rfl⟩ : syracuseStep 2018729 = 1514047) B1514047
theorem B4541885 : Blo 1344991 4541885 := bstep (se 3 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 4541885 = 1703207) B1703207
theorem B6811127 : Blo 1344991 6811127 := bstep (se 1 (by rfl) ⟨5108345, by rfl⟩ : syracuseStep 6811127 = 10216691) B10216691
theorem B2018879 : Blo 1344991 2018879 := bstep (se 1 (by rfl) ⟨1514159, by rfl⟩ : syracuseStep 2018879 = 3028319) B3028319
theorem B2019143 : Blo 1344991 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B13102955 : Blo 1344991 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B77590385 : Blo 1344991 77590385 := bstep (se 2 (by rfl) ⟨29096394, by rfl⟩ : syracuseStep 77590385 = 58192789) B58192789
theorem B14200705 : Blo 1344991 14200705 := bstep (se 2 (by rfl) ⟨5325264, by rfl⟩ : syracuseStep 14200705 = 10650529) B10650529
theorem B3026843 : Blo 1344991 3026843 := bstep (se 1 (by rfl) ⟨2270132, by rfl⟩ : syracuseStep 3026843 = 4540265) B4540265
theorem B2019227 : Blo 1344991 2019227 := bstep (se 1 (by rfl) ⟨1514420, by rfl⟩ : syracuseStep 2019227 = 3028841) B3028841
theorem B5533595 : Blo 1344991 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B4542587 : Blo 1344991 4542587 := bstep (se 1 (by rfl) ⟨3406940, by rfl⟩ : syracuseStep 4542587 = 6813881) B6813881
theorem B8622233 : Blo 1344991 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B3027131 : Blo 1344991 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B13824209 : Blo 1344991 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B6467849 : Blo 1344991 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B4542749 : Blo 1344991 4542749 := bstep (se 3 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 4542749 = 1703531) B1703531
theorem B29495659 : Blo 1344991 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B4542857 : Blo 1344991 4542857 := bstep (se 2 (by rfl) ⟨1703571, by rfl⟩ : syracuseStep 4542857 = 3407143) B3407143
theorem B2019791 : Blo 1344991 2019791 := bstep (se 1 (by rfl) ⟨1514843, by rfl⟩ : syracuseStep 2019791 = 3029687) B3029687
theorem B7188965 : Blo 1344991 7188965 := bstep (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) B1347931
theorem B25858541 : Blo 1344991 25858541 := bstep (se 3 (by rfl) ⟨4848476, by rfl⟩ : syracuseStep 25858541 = 9696953) B9696953
theorem B2019833 : Blo 1344991 2019833 := bstep (se 2 (by rfl) ⟨757437, by rfl⟩ : syracuseStep 2019833 = 1514875) B1514875
theorem B2019935 : Blo 1344991 2019935 := bstep (se 1 (by rfl) ⟨1514951, by rfl⟩ : syracuseStep 2019935 = 3029903) B3029903
theorem B46609037 : Blo 1344991 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B3027617 : Blo 1344991 3027617 := bstep (se 2 (by rfl) ⟨1135356, by rfl⟩ : syracuseStep 3027617 = 2270713) B2270713
theorem B3404551 : Blo 1344991 3404551 := bstep (se 1 (by rfl) ⟨2553413, by rfl⟩ : syracuseStep 3404551 = 5106827) B5106827
theorem B6812423 : Blo 1344991 6812423 := bstep (se 1 (by rfl) ⟨5109317, by rfl⟩ : syracuseStep 6812423 = 10218635) B10218635
theorem B12276503 : Blo 1344991 12276503 := bstep (se 1 (by rfl) ⟨9207377, by rfl⟩ : syracuseStep 12276503 = 18414755) B18414755
theorem B19673885 : Blo 1344991 19673885 := bstep (se 3 (by rfl) ⟨3688853, by rfl⟩ : syracuseStep 19673885 = 7377707) B7377707
theorem B7664615 : Blo 1344991 7664615 := bstep (se 1 (by rfl) ⟨5748461, by rfl⟩ : syracuseStep 7664615 = 11496923) B11496923
theorem B3027977 : Blo 1344991 3027977 := bstep (se 2 (by rfl) ⟨1135491, by rfl⟩ : syracuseStep 3027977 = 2270983) B2270983
theorem B3453961 : Blo 1344991 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B17257481 : Blo 1344991 17257481 := bstep (se 2 (by rfl) ⟨6471555, by rfl⟩ : syracuseStep 17257481 = 12943111) B12943111
theorem B25859087 : Blo 1344991 25859087 := bstep (se 1 (by rfl) ⟨19394315, by rfl⟩ : syracuseStep 25859087 = 38788631) B38788631
theorem B3404855 : Blo 1344991 3404855 := bstep (se 1 (by rfl) ⟨2553641, by rfl⟩ : syracuseStep 3404855 = 5107283) B5107283
theorem B3028031 : Blo 1344991 3028031 := bstep (se 1 (by rfl) ⟨2271023, by rfl⟩ : syracuseStep 3028031 = 4542047) B4542047
theorem B2020415 : Blo 1344991 2020415 := bstep (se 1 (by rfl) ⟨1515311, by rfl⟩ : syracuseStep 2020415 = 3030623) B3030623
theorem B2020457 : Blo 1344991 2020457 := bstep (se 2 (by rfl) ⟨757671, by rfl⟩ : syracuseStep 2020457 = 1515343) B1515343
theorem B6902891 : Blo 1344991 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B4371563 : Blo 1344991 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B4543775 : Blo 1344991 4543775 := bstep (se 1 (by rfl) ⟨3407831, by rfl⟩ : syracuseStep 4543775 = 6815663) B6815663
theorem B16602457 : Blo 1344991 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B23311721 : Blo 1344991 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B10221065 : Blo 1344991 10221065 := bstep (se 2 (by rfl) ⟨3832899, by rfl⟩ : syracuseStep 10221065 = 7665799) B7665799
theorem B20707001 : Blo 1344991 20707001 := bstep (se 2 (by rfl) ⟨7765125, by rfl⟩ : syracuseStep 20707001 = 15530251) B15530251
theorem B6813395 : Blo 1344991 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B3028967 : Blo 1344991 3028967 := bstep (se 1 (by rfl) ⟨2271725, by rfl⟩ : syracuseStep 3028967 = 4543451) B4543451
theorem B2553839 : Blo 1344991 2553839 := bstep (se 1 (by rfl) ⟨1915379, by rfl⟩ : syracuseStep 2553839 = 3830759) B3830759
theorem B3028985 : Blo 1344991 3028985 := bstep (se 2 (by rfl) ⟨1135869, by rfl⟩ : syracuseStep 3028985 = 2271739) B2271739
theorem B17258507 : Blo 1344991 17258507 := bstep (se 1 (by rfl) ⟨12943880, by rfl⟩ : syracuseStep 17258507 = 25887761) B25887761
theorem B32741441 : Blo 1344991 32741441 := bstep (se 2 (by rfl) ⟨12278040, by rfl⟩ : syracuseStep 32741441 = 24556081) B24556081
theorem B3029075 : Blo 1344991 3029075 := bstep (se 1 (by rfl) ⟨2271806, by rfl⟩ : syracuseStep 3029075 = 4543613) B4543613
theorem B3029147 : Blo 1344991 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B6469865 : Blo 1344991 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B3029255 : Blo 1344991 3029255 := bstep (se 1 (by rfl) ⟨2271941, by rfl⟩ : syracuseStep 3029255 = 4543883) B4543883
theorem B3406121 : Blo 1344991 3406121 := bstep (se 2 (by rfl) ⟨1277295, by rfl⟩ : syracuseStep 3406121 = 2554591) B2554591
theorem B3455273 : Blo 1344991 3455273 := bstep (se 2 (by rfl) ⟨1295727, by rfl⟩ : syracuseStep 3455273 = 2591455) B2591455
theorem B5831021 : Blo 1344991 5831021 := bstep (se 3 (by rfl) ⟨1093316, by rfl⟩ : syracuseStep 5831021 = 2186633) B2186633
theorem B7281019 : Blo 1344991 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B1514011 : Blo 1344991 1514011 := bstep (se 1 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 1514011 = 2271017) B2271017
theorem B14752307 : Blo 1344991 14752307 := bstep (se 1 (by rfl) ⟨11064230, by rfl⟩ : syracuseStep 14752307 = 22128461) B22128461
theorem B3029561 : Blo 1344991 3029561 := bstep (se 2 (by rfl) ⟨1136085, by rfl⟩ : syracuseStep 3029561 = 2272171) B2272171
theorem B6470479 : Blo 1344991 6470479 := bstep (se 1 (by rfl) ⟨4852859, by rfl⟩ : syracuseStep 6470479 = 9705719) B9705719
theorem B1915807 : Blo 1344991 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B3406799 : Blo 1344991 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B2423777 : Blo 1344991 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B4545665 : Blo 1344991 4545665 := bstep (se 2 (by rfl) ⟨1704624, by rfl⟩ : syracuseStep 4545665 = 3409249) B3409249
theorem B4545719 : Blo 1344991 4545719 := bstep (se 1 (by rfl) ⟨3409289, by rfl⟩ : syracuseStep 4545719 = 6818579) B6818579
theorem B9338105 : Blo 1344991 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B3030281 : Blo 1344991 3030281 := bstep (se 2 (by rfl) ⟨1136355, by rfl⟩ : syracuseStep 3030281 = 2272711) B2272711
theorem B6470941 : Blo 1344991 6470941 := bstep (se 3 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 6470941 = 2426603) B2426603
theorem B6815015 : Blo 1344991 6815015 := bstep (se 1 (by rfl) ⟨5111261, by rfl⟩ : syracuseStep 6815015 = 10222523) B10222523
theorem B12942803 : Blo 1344991 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B1514983 : Blo 1344991 1514983 := bstep (se 1 (by rfl) ⟨1136237, by rfl⟩ : syracuseStep 1514983 = 2272475) B2272475
theorem B1916507 : Blo 1344991 1916507 := bstep (se 1 (by rfl) ⟨1437380, by rfl⟩ : syracuseStep 1916507 = 2874761) B2874761
theorem B1818407 : Blo 1344991 1818407 := bstep (se 1 (by rfl) ⟨1363805, by rfl⟩ : syracuseStep 1818407 = 2727611) B2727611
theorem B5750615 : Blo 1344991 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B9216139 : Blo 1344991 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B4792643 : Blo 1344991 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B31072691 : Blo 1344991 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B9708025 : Blo 1344991 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B8184335 : Blo 1344991 8184335 := bstep (se 1 (by rfl) ⟨6138251, by rfl⟩ : syracuseStep 8184335 = 12276503) B12276503
theorem B1704559 : Blo 1344991 1704559 := bstep (se 1 (by rfl) ⟨1278419, by rfl⟩ : syracuseStep 1704559 = 2556839) B2556839
theorem B48636557 : Blo 1344991 48636557 := bstep (se 3 (by rfl) ⟨9119354, by rfl⟩ : syracuseStep 48636557 = 18238709) B18238709
theorem B2269903 : Blo 1344991 2269903 := bstep (se 1 (by rfl) ⟨1702427, by rfl⟩ : syracuseStep 2269903 = 3404855) B3404855
theorem B15541147 : Blo 1344991 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B4539401 : Blo 1344991 4539401 := bstep (se 2 (by rfl) ⟨1702275, by rfl⟩ : syracuseStep 4539401 = 3404551) B3404551
theorem B2556983 : Blo 1344991 2556983 := bstep (se 1 (by rfl) ⟨1917737, by rfl⟩ : syracuseStep 2556983 = 3835475) B3835475
theorem B8627305 : Blo 1344991 8627305 := bstep (se 2 (by rfl) ⟨3235239, by rfl⟩ : syracuseStep 8627305 = 6470479) B6470479
theorem B13804667 : Blo 1344991 13804667 := bstep (se 1 (by rfl) ⟨10353500, by rfl⟩ : syracuseStep 13804667 = 20707001) B20707001
theorem B5751931 : Blo 1344991 5751931 := bstep (se 1 (by rfl) ⟨4313948, by rfl⟩ : syracuseStep 5751931 = 8627897) B8627897
theorem B3409199 : Blo 1344991 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B4605281 : Blo 1344991 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B5113313 : Blo 1344991 5113313 := bstep (se 2 (by rfl) ⟨1917492, by rfl⟩ : syracuseStep 5113313 = 3834985) B3834985
theorem B1345051 : Blo 1344991 1345051 := bstep (se 1 (by rfl) ⟨1008788, by rfl⟩ : syracuseStep 1345051 = 2017577) B2017577
theorem B2270747 : Blo 1344991 2270747 := bstep (se 1 (by rfl) ⟨1703060, by rfl⟩ : syracuseStep 2270747 = 3406121) B3406121
theorem B2303515 : Blo 1344991 2303515 := bstep (se 1 (by rfl) ⟨1727636, by rfl⟩ : syracuseStep 2303515 = 3455273) B3455273
theorem B1345055 : Blo 1344991 1345055 := bstep (se 1 (by rfl) ⟨1008791, by rfl⟩ : syracuseStep 1345055 = 2017583) B2017583
theorem B27616889 : Blo 1344991 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B12945035 : Blo 1344991 12945035 := bstep (se 1 (by rfl) ⟨9708776, by rfl⟩ : syracuseStep 12945035 = 19417553) B19417553
theorem B1345215 : Blo 1344991 1345215 := bstep (se 1 (by rfl) ⟨1008911, by rfl⟩ : syracuseStep 1345215 = 2017823) B2017823
theorem B8627921 : Blo 1344991 8627921 := bstep (se 2 (by rfl) ⟨3235470, by rfl⟩ : syracuseStep 8627921 = 6470941) B6470941
theorem B22136609 : Blo 1344991 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B1345471 : Blo 1344991 1345471 := bstep (se 1 (by rfl) ⟨1009103, by rfl⟩ : syracuseStep 1345471 = 2018207) B2018207
theorem B1345503 : Blo 1344991 1345503 := bstep (se 1 (by rfl) ⟨1009127, by rfl⟩ : syracuseStep 1345503 = 2018255) B2018255
theorem B2271199 : Blo 1344991 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B1345563 : Blo 1344991 1345563 := bstep (se 1 (by rfl) ⟨1009172, by rfl⟩ : syracuseStep 1345563 = 2018345) B2018345
theorem B1345567 : Blo 1344991 1345567 := bstep (se 1 (by rfl) ⟨1009175, by rfl⟩ : syracuseStep 1345567 = 2018351) B2018351
theorem B1345583 : Blo 1344991 1345583 := bstep (se 1 (by rfl) ⟨1009187, by rfl⟩ : syracuseStep 1345583 = 2018375) B2018375
theorem B52463693 : Blo 1344991 52463693 := bstep (se 3 (by rfl) ⟨9836942, by rfl⟩ : syracuseStep 52463693 = 19673885) B19673885
theorem B1345759 : Blo 1344991 1345759 := bstep (se 1 (by rfl) ⟨1009319, by rfl⟩ : syracuseStep 1345759 = 2018639) B2018639
theorem B3279091 : Blo 1344991 3279091 := bstep (se 1 (by rfl) ⟨2459318, by rfl⟩ : syracuseStep 3279091 = 4918637) B4918637
theorem B1345819 : Blo 1344991 1345819 := bstep (se 1 (by rfl) ⟨1009364, by rfl⟩ : syracuseStep 1345819 = 2018729) B2018729
theorem B8628535 : Blo 1344991 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B4540751 : Blo 1344991 4540751 := bstep (se 1 (by rfl) ⟨3405563, by rfl⟩ : syracuseStep 4540751 = 6811127) B6811127
theorem B1345919 : Blo 1344991 1345919 := bstep (se 1 (by rfl) ⟨1009439, by rfl⟩ : syracuseStep 1345919 = 2018879) B2018879
theorem B18934273 : Blo 1344991 18934273 := bstep (se 2 (by rfl) ⟨7100352, by rfl⟩ : syracuseStep 18934273 = 14200705) B14200705
theorem B1346095 : Blo 1344991 1346095 := bstep (se 1 (by rfl) ⟨1009571, by rfl⟩ : syracuseStep 1346095 = 2019143) B2019143
theorem B8735303 : Blo 1344991 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B51726923 : Blo 1344991 51726923 := bstep (se 1 (by rfl) ⟨38795192, by rfl⟩ : syracuseStep 51726923 = 77590385) B77590385
theorem B2017895 : Blo 1344991 2017895 := bstep (se 1 (by rfl) ⟨1513421, by rfl⟩ : syracuseStep 2017895 = 3026843) B3026843
theorem B1346151 : Blo 1344991 1346151 := bstep (se 1 (by rfl) ⟨1009613, by rfl⟩ : syracuseStep 1346151 = 2019227) B2019227
theorem B3689063 : Blo 1344991 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B2018087 : Blo 1344991 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B4311899 : Blo 1344991 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B1346527 : Blo 1344991 1346527 := bstep (se 1 (by rfl) ⟨1009895, by rfl⟩ : syracuseStep 1346527 = 2019791) B2019791
theorem B17239027 : Blo 1344991 17239027 := bstep (se 1 (by rfl) ⟨12929270, by rfl⟩ : syracuseStep 17239027 = 25858541) B25858541
theorem B1346555 : Blo 1344991 1346555 := bstep (se 1 (by rfl) ⟨1009916, by rfl⟩ : syracuseStep 1346555 = 2019833) B2019833
theorem B1346623 : Blo 1344991 1346623 := bstep (se 1 (by rfl) ⟨1009967, by rfl⟩ : syracuseStep 1346623 = 2019935) B2019935
theorem B2018411 : Blo 1344991 2018411 := bstep (se 1 (by rfl) ⟨1513808, by rfl⟩ : syracuseStep 2018411 = 3027617) B3027617
theorem B4541615 : Blo 1344991 4541615 := bstep (se 1 (by rfl) ⟨3406211, by rfl⟩ : syracuseStep 4541615 = 6812423) B6812423
theorem B10226897 : Blo 1344991 10226897 := bstep (se 2 (by rfl) ⟨3835086, by rfl⟩ : syracuseStep 10226897 = 7670173) B7670173
theorem B3026231 : Blo 1344991 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B2018651 : Blo 1344991 2018651 := bstep (se 1 (by rfl) ⟨1513988, by rfl⟩ : syracuseStep 2018651 = 3027977) B3027977
theorem B11504987 : Blo 1344991 11504987 := bstep (se 1 (by rfl) ⟨8628740, by rfl⟩ : syracuseStep 11504987 = 17257481) B17257481
theorem B17239391 : Blo 1344991 17239391 := bstep (se 1 (by rfl) ⟨12929543, by rfl⟩ : syracuseStep 17239391 = 25859087) B25859087
theorem B2018681 : Blo 1344991 2018681 := bstep (se 2 (by rfl) ⟨757005, by rfl⟩ : syracuseStep 2018681 = 1514011) B1514011
theorem B2018687 : Blo 1344991 2018687 := bstep (se 1 (by rfl) ⟨1514015, by rfl⟩ : syracuseStep 2018687 = 3028031) B3028031
theorem B1346943 : Blo 1344991 1346943 := bstep (se 1 (by rfl) ⟨1010207, by rfl⟩ : syracuseStep 1346943 = 2020415) B2020415
theorem B1346971 : Blo 1344991 1346971 := bstep (se 1 (by rfl) ⟨1010228, by rfl⟩ : syracuseStep 1346971 = 2020457) B2020457
theorem B5107495 : Blo 1344991 5107495 := bstep (se 1 (by rfl) ⟨3830621, by rfl⟩ : syracuseStep 5107495 = 7661243) B7661243
theorem B4542263 : Blo 1344991 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B3026825 : Blo 1344991 3026825 := bstep (se 2 (by rfl) ⟨1135059, by rfl⟩ : syracuseStep 3026825 = 2270119) B2270119
theorem B2019311 : Blo 1344991 2019311 := bstep (se 1 (by rfl) ⟨1514483, by rfl⟩ : syracuseStep 2019311 = 3028967) B3028967
theorem B2019323 : Blo 1344991 2019323 := bstep (se 1 (by rfl) ⟨1514492, by rfl⟩ : syracuseStep 2019323 = 3028985) B3028985
theorem B11505671 : Blo 1344991 11505671 := bstep (se 1 (by rfl) ⟨8629253, by rfl⟩ : syracuseStep 11505671 = 17258507) B17258507
theorem B21827627 : Blo 1344991 21827627 := bstep (se 1 (by rfl) ⟨16370720, by rfl⟩ : syracuseStep 21827627 = 32741441) B32741441
theorem B2019383 : Blo 1344991 2019383 := bstep (se 1 (by rfl) ⟨1514537, by rfl⟩ : syracuseStep 2019383 = 3029075) B3029075
theorem B3027041 : Blo 1344991 3027041 := bstep (se 2 (by rfl) ⟨1135140, by rfl⟩ : syracuseStep 3027041 = 2270281) B2270281
theorem B2019431 : Blo 1344991 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B1437799 : Blo 1344991 1437799 := bstep (se 1 (by rfl) ⟨1078349, by rfl⟩ : syracuseStep 1437799 = 2156699) B2156699
theorem B4313243 : Blo 1344991 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B2019503 : Blo 1344991 2019503 := bstep (se 1 (by rfl) ⟨1514627, by rfl⟩ : syracuseStep 2019503 = 3029255) B3029255
theorem B3887347 : Blo 1344991 3887347 := bstep (se 1 (by rfl) ⟨2915510, by rfl⟩ : syracuseStep 3887347 = 5831021) B5831021
theorem B9834871 : Blo 1344991 9834871 := bstep (se 1 (by rfl) ⟨7376153, by rfl⟩ : syracuseStep 9834871 = 14752307) B14752307
theorem B2019707 : Blo 1344991 2019707 := bstep (se 1 (by rfl) ⟨1514780, by rfl⟩ : syracuseStep 2019707 = 3029561) B3029561
theorem B2019977 : Blo 1344991 2019977 := bstep (se 2 (by rfl) ⟨757491, by rfl⟩ : syracuseStep 2019977 = 1514983) B1514983
theorem B3027707 : Blo 1344991 3027707 := bstep (se 1 (by rfl) ⟨2270780, by rfl⟩ : syracuseStep 3027707 = 4541561) B4541561
theorem B6140735 : Blo 1344991 6140735 := bstep (se 1 (by rfl) ⟨4605551, by rfl⟩ : syracuseStep 6140735 = 9211103) B9211103
theorem B2020187 : Blo 1344991 2020187 := bstep (se 1 (by rfl) ⟨1515140, by rfl⟩ : syracuseStep 2020187 = 3030281) B3030281
theorem B4543343 : Blo 1344991 4543343 := bstep (se 1 (by rfl) ⟨3407507, by rfl⟩ : syracuseStep 4543343 = 6815015) B6815015
theorem B3027923 : Blo 1344991 3027923 := bstep (se 1 (by rfl) ⟨2270942, by rfl⟩ : syracuseStep 3027923 = 4541885) B4541885
theorem B3028391 : Blo 1344991 3028391 := bstep (se 1 (by rfl) ⟨2271293, by rfl⟩ : syracuseStep 3028391 = 4542587) B4542587
theorem B5748155 : Blo 1344991 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B3028499 : Blo 1344991 3028499 := bstep (se 1 (by rfl) ⟨2271374, by rfl⟩ : syracuseStep 3028499 = 4542749) B4542749
theorem B3028571 : Blo 1344991 3028571 := bstep (se 1 (by rfl) ⟨2271428, by rfl⟩ : syracuseStep 3028571 = 4542857) B4542857
theorem B39327545 : Blo 1344991 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B5109743 : Blo 1344991 5109743 := bstep (se 1 (by rfl) ⟨3832307, by rfl⟩ : syracuseStep 5109743 = 7664615) B7664615
theorem B34510859 : Blo 1344991 34510859 := bstep (se 1 (by rfl) ⟨25883144, by rfl⟩ : syracuseStep 34510859 = 51766289) B51766289
theorem B4601927 : Blo 1344991 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B1513543 : Blo 1344991 1513543 := bstep (se 1 (by rfl) ⟨1135157, by rfl⟩ : syracuseStep 1513543 = 2270315) B2270315
theorem B2914375 : Blo 1344991 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B7280765 : Blo 1344991 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B3029183 : Blo 1344991 3029183 := bstep (se 1 (by rfl) ⟨2271887, by rfl⟩ : syracuseStep 3029183 = 4543775) B4543775
theorem B11491591 : Blo 1344991 11491591 := bstep (se 1 (by rfl) ⟨8618693, by rfl⟩ : syracuseStep 11491591 = 17237387) B17237387
theorem B6814043 : Blo 1344991 6814043 := bstep (se 1 (by rfl) ⟨5110532, by rfl⟩ : syracuseStep 6814043 = 10221065) B10221065
theorem B2554409 : Blo 1344991 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B1702559 : Blo 1344991 1702559 := bstep (se 1 (by rfl) ⟨1276919, by rfl⟩ : syracuseStep 1702559 = 2553839) B2553839
theorem B5110685 : Blo 1344991 5110685 := bstep (se 3 (by rfl) ⟨958253, by rfl⟩ : syracuseStep 5110685 = 1916507) B1916507
theorem B1514407 : Blo 1344991 1514407 := bstep (se 1 (by rfl) ⟨1135805, by rfl⟩ : syracuseStep 1514407 = 2271611) B2271611
theorem B1514587 : Blo 1344991 1514587 := bstep (se 1 (by rfl) ⟨1135940, by rfl⟩ : syracuseStep 1514587 = 2271881) B2271881
theorem B3030443 : Blo 1344991 3030443 := bstep (se 1 (by rfl) ⟨2272832, by rfl⟩ : syracuseStep 3030443 = 4545665) B4545665
theorem B4849085 : Blo 1344991 4849085 := bstep (se 3 (by rfl) ⟨909203, by rfl⟩ : syracuseStep 4849085 = 1818407) B1818407
theorem B3030479 : Blo 1344991 3030479 := bstep (se 1 (by rfl) ⟨2272859, by rfl⟩ : syracuseStep 3030479 = 4545719) B4545719
theorem B6225403 : Blo 1344991 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B3833743 : Blo 1344991 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B6463405 : Blo 1344991 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B2875495 : Blo 1344991 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B1917065 : Blo 1344991 1917065 := bstep (se 2 (by rfl) ⟨718899, by rfl⟩ : syracuseStep 1917065 = 1437799) B1437799
theorem B12288185 : Blo 1344991 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B3195095 : Blo 1344991 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B32424371 : Blo 1344991 32424371 := bstep (se 1 (by rfl) ⟨24318278, by rfl⟩ : syracuseStep 32424371 = 48636557) B48636557
theorem B12944033 : Blo 1344991 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B1704655 : Blo 1344991 1704655 := bstep (se 1 (by rfl) ⟨1278491, by rfl⟩ : syracuseStep 1704655 = 2556983) B2556983
theorem B3408875 : Blo 1344991 3408875 := bstep (se 1 (by rfl) ⟨2556656, by rfl⟩ : syracuseStep 3408875 = 5113313) B5113313
theorem B5751947 : Blo 1344991 5751947 := bstep (se 1 (by rfl) ⟨4313960, by rfl⟩ : syracuseStep 5751947 = 8627921) B8627921
theorem B21824893 : Blo 1344991 21824893 := bstep (se 3 (by rfl) ⟨4092167, by rfl⟩ : syracuseStep 21824893 = 8184335) B8184335
theorem B11503073 : Blo 1344991 11503073 := bstep (se 2 (by rfl) ⟨4313652, by rfl⟩ : syracuseStep 11503073 = 8627305) B8627305
theorem B7669241 : Blo 1344991 7669241 := bstep (se 2 (by rfl) ⟨2875965, by rfl⟩ : syracuseStep 7669241 = 5751931) B5751931
theorem B1345263 : Blo 1344991 1345263 := bstep (se 1 (by rfl) ⟨1008947, by rfl⟩ : syracuseStep 1345263 = 2017895) B2017895
theorem B2459375 : Blo 1344991 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B4540157 : Blo 1344991 4540157 := bstep (se 3 (by rfl) ⟨851279, by rfl⟩ : syracuseStep 4540157 = 1702559) B1702559
theorem B1345391 : Blo 1344991 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B8300537 : Blo 1344991 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B1345607 : Blo 1344991 1345607 := bstep (se 1 (by rfl) ⟨1009205, by rfl⟩ : syracuseStep 1345607 = 2018411) B2018411
theorem B6817931 : Blo 1344991 6817931 := bstep (se 1 (by rfl) ⟨5113448, by rfl⟩ : syracuseStep 6817931 = 10226897) B10226897
theorem B2017487 : Blo 1344991 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B1345767 : Blo 1344991 1345767 := bstep (se 1 (by rfl) ⟨1009325, by rfl⟩ : syracuseStep 1345767 = 2018651) B2018651
theorem B7669991 : Blo 1344991 7669991 := bstep (se 1 (by rfl) ⟨5752493, by rfl⟩ : syracuseStep 7669991 = 11504987) B11504987
theorem B1345787 : Blo 1344991 1345787 := bstep (se 1 (by rfl) ⟨1009340, by rfl⟩ : syracuseStep 1345787 = 2018681) B2018681
theorem B1345791 : Blo 1344991 1345791 := bstep (se 1 (by rfl) ⟨1009343, by rfl⟩ : syracuseStep 1345791 = 2018687) B2018687
theorem B6809993 : Blo 1344991 6809993 := bstep (se 2 (by rfl) ⟨2553747, by rfl⟩ : syracuseStep 6809993 = 5107495) B5107495
theorem B2017883 : Blo 1344991 2017883 := bstep (se 1 (by rfl) ⟨1513412, by rfl⟩ : syracuseStep 2017883 = 3026825) B3026825
theorem B1346207 : Blo 1344991 1346207 := bstep (se 1 (by rfl) ⟨1009655, by rfl⟩ : syracuseStep 1346207 = 2019311) B2019311
theorem B1346215 : Blo 1344991 1346215 := bstep (se 1 (by rfl) ⟨1009661, by rfl⟩ : syracuseStep 1346215 = 2019323) B2019323
theorem B7670447 : Blo 1344991 7670447 := bstep (se 1 (by rfl) ⟨5752835, by rfl⟩ : syracuseStep 7670447 = 11505671) B11505671
theorem B14551751 : Blo 1344991 14551751 := bstep (se 1 (by rfl) ⟨10913813, by rfl⟩ : syracuseStep 14551751 = 21827627) B21827627
theorem B1346255 : Blo 1344991 1346255 := bstep (se 1 (by rfl) ⟨1009691, by rfl⟩ : syracuseStep 1346255 = 2019383) B2019383
theorem B2018027 : Blo 1344991 2018027 := bstep (se 1 (by rfl) ⟨1513520, by rfl⟩ : syracuseStep 2018027 = 3027041) B3027041
theorem B1346287 : Blo 1344991 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B2018057 : Blo 1344991 2018057 := bstep (se 2 (by rfl) ⟨756771, by rfl⟩ : syracuseStep 2018057 = 1513543) B1513543
theorem B3885833 : Blo 1344991 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B1346335 : Blo 1344991 1346335 := bstep (se 1 (by rfl) ⟨1009751, by rfl⟩ : syracuseStep 1346335 = 2019503) B2019503
theorem B1346471 : Blo 1344991 1346471 := bstep (se 1 (by rfl) ⟨1009853, by rfl⟩ : syracuseStep 1346471 = 2019707) B2019707
theorem B15322121 : Blo 1344991 15322121 := bstep (se 2 (by rfl) ⟨5745795, by rfl⟩ : syracuseStep 15322121 = 11491591) B11491591
theorem B11504713 : Blo 1344991 11504713 := bstep (se 2 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 11504713 = 8628535) B8628535
theorem B1346651 : Blo 1344991 1346651 := bstep (se 1 (by rfl) ⟨1009988, by rfl⟩ : syracuseStep 1346651 = 2019977) B2019977
theorem B2018471 : Blo 1344991 2018471 := bstep (se 1 (by rfl) ⟨1513853, by rfl⟩ : syracuseStep 2018471 = 3027707) B3027707
theorem B1346791 : Blo 1344991 1346791 := bstep (se 1 (by rfl) ⟨1010093, by rfl⟩ : syracuseStep 1346791 = 2020187) B2020187
theorem B2018615 : Blo 1344991 2018615 := bstep (se 1 (by rfl) ⟨1513961, by rfl⟩ : syracuseStep 2018615 = 3027923) B3027923
theorem B3026267 : Blo 1344991 3026267 := bstep (se 1 (by rfl) ⟨2269700, by rfl⟩ : syracuseStep 3026267 = 4539401) B4539401
theorem B9203111 : Blo 1344991 9203111 := bstep (se 1 (by rfl) ⟨6902333, by rfl⟩ : syracuseStep 9203111 = 13804667) B13804667
theorem B2272745 : Blo 1344991 2272745 := bstep (se 2 (by rfl) ⟨852279, by rfl⟩ : syracuseStep 2272745 = 1704559) B1704559
theorem B2272799 : Blo 1344991 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B3026537 : Blo 1344991 3026537 := bstep (se 2 (by rfl) ⟨1134951, by rfl⟩ : syracuseStep 3026537 = 2269903) B2269903
theorem B2018927 : Blo 1344991 2018927 := bstep (se 1 (by rfl) ⟨1514195, by rfl⟩ : syracuseStep 2018927 = 3028391) B3028391
theorem B2018999 : Blo 1344991 2018999 := bstep (se 1 (by rfl) ⟨1514249, by rfl⟩ : syracuseStep 2018999 = 3028499) B3028499
theorem B2019047 : Blo 1344991 2019047 := bstep (se 1 (by rfl) ⟨1514285, by rfl⟩ : syracuseStep 2019047 = 3028571) B3028571
theorem B18411259 : Blo 1344991 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B8630023 : Blo 1344991 8630023 := bstep (se 1 (by rfl) ⟨6472517, by rfl⟩ : syracuseStep 8630023 = 12945035) B12945035
theorem B20721529 : Blo 1344991 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B2019209 : Blo 1344991 2019209 := bstep (se 2 (by rfl) ⟨757203, by rfl⟩ : syracuseStep 2019209 = 1514407) B1514407
theorem B23007239 : Blo 1344991 23007239 := bstep (se 1 (by rfl) ⟨17255429, by rfl⟩ : syracuseStep 23007239 = 34510859) B34510859
theorem B3067951 : Blo 1344991 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B34975795 : Blo 1344991 34975795 := bstep (se 1 (by rfl) ⟨26231846, by rfl⟩ : syracuseStep 34975795 = 52463693) B52463693
theorem B4853843 : Blo 1344991 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B2019449 : Blo 1344991 2019449 := bstep (se 2 (by rfl) ⟨757293, by rfl⟩ : syracuseStep 2019449 = 1514587) B1514587
theorem B2019455 : Blo 1344991 2019455 := bstep (se 1 (by rfl) ⟨1514591, by rfl⟩ : syracuseStep 2019455 = 3029183) B3029183
theorem B23294141 : Blo 1344991 23294141 := bstep (se 3 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 23294141 = 8735303) B8735303
theorem B3027167 : Blo 1344991 3027167 := bstep (se 1 (by rfl) ⟨2270375, by rfl⟩ : syracuseStep 3027167 = 4540751) B4540751
theorem B4542695 : Blo 1344991 4542695 := bstep (se 1 (by rfl) ⟨3407021, by rfl⟩ : syracuseStep 4542695 = 6814043) B6814043
theorem B34484615 : Blo 1344991 34484615 := bstep (se 1 (by rfl) ⟨25863461, by rfl⟩ : syracuseStep 34484615 = 51726923) B51726923
theorem B3027743 : Blo 1344991 3027743 := bstep (se 1 (by rfl) ⟨2270807, by rfl⟩ : syracuseStep 3027743 = 4541615) B4541615
theorem B2020295 : Blo 1344991 2020295 := bstep (se 1 (by rfl) ⟨1515221, by rfl⟩ : syracuseStep 2020295 = 3030443) B3030443
theorem B3232723 : Blo 1344991 3232723 := bstep (se 1 (by rfl) ⟨2424542, by rfl⟩ : syracuseStep 3232723 = 4849085) B4849085
theorem B2020319 : Blo 1344991 2020319 := bstep (se 1 (by rfl) ⟨1515239, by rfl⟩ : syracuseStep 2020319 = 3030479) B3030479
theorem B3028175 : Blo 1344991 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B3028265 : Blo 1344991 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B4372121 : Blo 1344991 4372121 := bstep (se 2 (by rfl) ⟨1639545, by rfl⟩ : syracuseStep 4372121 = 3279091) B3279091
theorem B5183129 : Blo 1344991 5183129 := bstep (se 2 (by rfl) ⟨1943673, by rfl⟩ : syracuseStep 5183129 = 3887347) B3887347
theorem B13113161 : Blo 1344991 13113161 := bstep (se 2 (by rfl) ⟨4917435, by rfl⟩ : syracuseStep 13113161 = 9834871) B9834871
theorem B4093823 : Blo 1344991 4093823 := bstep (se 1 (by rfl) ⟨3070367, by rfl⟩ : syracuseStep 4093823 = 6140735) B6140735
theorem B3028895 : Blo 1344991 3028895 := bstep (se 1 (by rfl) ⟨2271671, by rfl⟩ : syracuseStep 3028895 = 4543343) B4543343
theorem B25245697 : Blo 1344991 25245697 := bstep (se 2 (by rfl) ⟨9467136, by rfl⟩ : syracuseStep 25245697 = 18934273) B18934273
theorem B3070187 : Blo 1344991 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B3832103 : Blo 1344991 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B1513831 : Blo 1344991 1513831 := bstep (se 1 (by rfl) ⟨1135373, by rfl⟩ : syracuseStep 1513831 = 2270747) B2270747
theorem B82860509 : Blo 1344991 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B22985369 : Blo 1344991 22985369 := bstep (se 2 (by rfl) ⟨8619513, by rfl⟩ : syracuseStep 22985369 = 17239027) B17239027
theorem B3406495 : Blo 1344991 3406495 := bstep (se 1 (by rfl) ⟨2554871, by rfl⟩ : syracuseStep 3406495 = 5109743) B5109743
theorem B1702939 : Blo 1344991 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B2874599 : Blo 1344991 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B3407123 : Blo 1344991 3407123 := bstep (se 1 (by rfl) ⟨2555342, by rfl⟩ : syracuseStep 3407123 = 5110685) B5110685
theorem B3071353 : Blo 1344991 3071353 := bstep (se 2 (by rfl) ⟨1151757, by rfl⟩ : syracuseStep 3071353 = 2303515) B2303515
theorem B59030957 : Blo 1344991 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B104873453 : Blo 1344991 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B11492927 : Blo 1344991 11492927 := bstep (se 1 (by rfl) ⟨8619695, by rfl⟩ : syracuseStep 11492927 = 17239391) B17239391
theorem B34471493 : Blo 1344991 34471493 := bstep (se 4 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 34471493 = 6463405) B6463405
theorem B5111657 : Blo 1344991 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B33660929 : Blo 1344991 33660929 := bstep (se 2 (by rfl) ⟨12622848, by rfl⟩ : syracuseStep 33660929 = 25245697) B25245697
theorem B3235895 : Blo 1344991 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B8192123 : Blo 1344991 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B3833993 : Blo 1344991 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B5112173 : Blo 1344991 5112173 := bstep (se 3 (by rfl) ⟨958532, by rfl⟩ : syracuseStep 5112173 = 1917065) B1917065
theorem B3834631 : Blo 1344991 3834631 := bstep (se 1 (by rfl) ⟨2875973, by rfl⟩ : syracuseStep 3834631 = 5751947) B5751947
theorem B7668715 : Blo 1344991 7668715 := bstep (se 1 (by rfl) ⟨5751536, by rfl⟩ : syracuseStep 7668715 = 11503073) B11503073
theorem B5112827 : Blo 1344991 5112827 := bstep (se 1 (by rfl) ⟨3834620, by rfl⟩ : syracuseStep 5112827 = 7669241) B7669241
theorem B1639583 : Blo 1344991 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B8742107 : Blo 1344991 8742107 := bstep (se 1 (by rfl) ⟨6556580, by rfl⟩ : syracuseStep 8742107 = 13113161) B13113161
theorem B2729215 : Blo 1344991 2729215 := bstep (se 1 (by rfl) ⟨2046911, by rfl⟩ : syracuseStep 2729215 = 4093823) B4093823
theorem B4310297 : Blo 1344991 4310297 := bstep (se 2 (by rfl) ⟨1616361, by rfl⟩ : syracuseStep 4310297 = 3232723) B3232723
theorem B2270585 : Blo 1344991 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B1344991 : Blo 1344991 1344991 := bstep (se 1 (by rfl) ⟨1008743, by rfl⟩ : syracuseStep 1344991 = 2017487) B2017487
theorem B5113327 : Blo 1344991 5113327 := bstep (se 1 (by rfl) ⟨3834995, by rfl⟩ : syracuseStep 5113327 = 7669991) B7669991
theorem B4539995 : Blo 1344991 4539995 := bstep (se 1 (by rfl) ⟨3404996, by rfl⟩ : syracuseStep 4539995 = 6809993) B6809993
theorem B55240339 : Blo 1344991 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B1345255 : Blo 1344991 1345255 := bstep (se 1 (by rfl) ⟨1008941, by rfl⟩ : syracuseStep 1345255 = 2017883) B2017883
theorem B5113631 : Blo 1344991 5113631 := bstep (se 1 (by rfl) ⟨3835223, by rfl⟩ : syracuseStep 5113631 = 7670447) B7670447
theorem B9701167 : Blo 1344991 9701167 := bstep (se 1 (by rfl) ⟨7275875, by rfl⟩ : syracuseStep 9701167 = 14551751) B14551751
theorem B1345351 : Blo 1344991 1345351 := bstep (se 1 (by rfl) ⟨1009013, by rfl⟩ : syracuseStep 1345351 = 2018027) B2018027
theorem B29099857 : Blo 1344991 29099857 := bstep (se 2 (by rfl) ⟨10912446, by rfl⟩ : syracuseStep 29099857 = 21824893) B21824893
theorem B1345371 : Blo 1344991 1345371 := bstep (se 1 (by rfl) ⟨1009028, by rfl⟩ : syracuseStep 1345371 = 2018057) B2018057
theorem B2590555 : Blo 1344991 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B1345647 : Blo 1344991 1345647 := bstep (se 1 (by rfl) ⟨1009235, by rfl⟩ : syracuseStep 1345647 = 2018471) B2018471
theorem B2271415 : Blo 1344991 2271415 := bstep (se 1 (by rfl) ⟨1703561, by rfl⟩ : syracuseStep 2271415 = 3407123) B3407123
theorem B1345743 : Blo 1344991 1345743 := bstep (se 1 (by rfl) ⟨1009307, by rfl⟩ : syracuseStep 1345743 = 2018615) B2018615
theorem B2017511 : Blo 1344991 2017511 := bstep (se 1 (by rfl) ⟨1513133, by rfl⟩ : syracuseStep 2017511 = 3026267) B3026267
theorem B34081013 : Blo 1344991 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B7661951 : Blo 1344991 7661951 := bstep (se 1 (by rfl) ⟨5746463, by rfl⟩ : syracuseStep 7661951 = 11492927) B11492927
theorem B22980995 : Blo 1344991 22980995 := bstep (se 1 (by rfl) ⟨17235746, by rfl⟩ : syracuseStep 22980995 = 34471493) B34471493
theorem B2017691 : Blo 1344991 2017691 := bstep (se 1 (by rfl) ⟨1513268, by rfl⟩ : syracuseStep 2017691 = 3026537) B3026537
theorem B1345951 : Blo 1344991 1345951 := bstep (se 1 (by rfl) ⟨1009463, by rfl⟩ : syracuseStep 1345951 = 2018927) B2018927
theorem B1345999 : Blo 1344991 1345999 := bstep (se 1 (by rfl) ⟨1009499, by rfl⟩ : syracuseStep 1345999 = 2018999) B2018999
theorem B1346031 : Blo 1344991 1346031 := bstep (se 1 (by rfl) ⟨1009523, by rfl⟩ : syracuseStep 1346031 = 2019047) B2019047
theorem B1346139 : Blo 1344991 1346139 := bstep (se 1 (by rfl) ⟨1009604, by rfl⟩ : syracuseStep 1346139 = 2019209) B2019209
theorem B15338159 : Blo 1344991 15338159 := bstep (se 1 (by rfl) ⟨11503619, by rfl⟩ : syracuseStep 15338159 = 23007239) B23007239
theorem B4090601 : Blo 1344991 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B1346299 : Blo 1344991 1346299 := bstep (se 1 (by rfl) ⟨1009724, by rfl⟩ : syracuseStep 1346299 = 2019449) B2019449
theorem B1346303 : Blo 1344991 1346303 := bstep (se 1 (by rfl) ⟨1009727, by rfl⟩ : syracuseStep 1346303 = 2019455) B2019455
theorem B2018111 : Blo 1344991 2018111 := bstep (se 1 (by rfl) ⟨1513583, by rfl⟩ : syracuseStep 2018111 = 3027167) B3027167
theorem B22989743 : Blo 1344991 22989743 := bstep (se 1 (by rfl) ⟨17242307, by rfl⟩ : syracuseStep 22989743 = 34484615) B34484615
theorem B2018441 : Blo 1344991 2018441 := bstep (se 2 (by rfl) ⟨756915, by rfl⟩ : syracuseStep 2018441 = 1513831) B1513831
theorem B2018495 : Blo 1344991 2018495 := bstep (se 1 (by rfl) ⟨1513871, by rfl⟩ : syracuseStep 2018495 = 3027743) B3027743
theorem B1346863 : Blo 1344991 1346863 := bstep (se 1 (by rfl) ⟨1010147, by rfl⟩ : syracuseStep 1346863 = 2020295) B2020295
theorem B1346879 : Blo 1344991 1346879 := bstep (se 1 (by rfl) ⟨1010159, by rfl⟩ : syracuseStep 1346879 = 2020319) B2020319
theorem B2272583 : Blo 1344991 2272583 := bstep (se 1 (by rfl) ⟨1704437, by rfl⟩ : syracuseStep 2272583 = 3408875) B3408875
theorem B2018783 : Blo 1344991 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B2018843 : Blo 1344991 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B4541993 : Blo 1344991 4541993 := bstep (se 2 (by rfl) ⟨1703247, by rfl⟩ : syracuseStep 4541993 = 3406495) B3406495
theorem B2272873 : Blo 1344991 2272873 := bstep (se 2 (by rfl) ⟨852327, by rfl⟩ : syracuseStep 2272873 = 1704655) B1704655
theorem B3026771 : Blo 1344991 3026771 := bstep (se 1 (by rfl) ⟨2270078, by rfl⟩ : syracuseStep 3026771 = 4540157) B4540157
theorem B2019263 : Blo 1344991 2019263 := bstep (se 1 (by rfl) ⟨1514447, by rfl⟩ : syracuseStep 2019263 = 3028895) B3028895
theorem B5533691 : Blo 1344991 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B15339617 : Blo 1344991 15339617 := bstep (se 2 (by rfl) ⟨5752356, by rfl⟩ : syracuseStep 15339617 = 11504713) B11504713
theorem B15323579 : Blo 1344991 15323579 := bstep (se 1 (by rfl) ⟨11492684, by rfl⟩ : syracuseStep 15323579 = 22985369) B22985369
theorem B69915635 : Blo 1344991 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B24548345 : Blo 1344991 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B11506697 : Blo 1344991 11506697 := bstep (se 2 (by rfl) ⟨4315011, by rfl⟩ : syracuseStep 11506697 = 8630023) B8630023
theorem B27628705 : Blo 1344991 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B46634393 : Blo 1344991 46634393 := bstep (se 2 (by rfl) ⟨17487897, by rfl⟩ : syracuseStep 46634393 = 34975795) B34975795
theorem B15529427 : Blo 1344991 15529427 := bstep (se 1 (by rfl) ⟨11647070, by rfl⟩ : syracuseStep 15529427 = 23294141) B23294141
theorem B3028463 : Blo 1344991 3028463 := bstep (se 1 (by rfl) ⟨2271347, by rfl⟩ : syracuseStep 3028463 = 4542695) B4542695
theorem B21616247 : Blo 1344991 21616247 := bstep (se 1 (by rfl) ⟨16212185, by rfl⟩ : syracuseStep 21616247 = 32424371) B32424371
theorem B2914747 : Blo 1344991 2914747 := bstep (se 1 (by rfl) ⟨2186060, by rfl⟩ : syracuseStep 2914747 = 4372121) B4372121
theorem B3455419 : Blo 1344991 3455419 := bstep (se 1 (by rfl) ⟨2591564, by rfl⟩ : syracuseStep 3455419 = 5183129) B5183129
theorem B4545287 : Blo 1344991 4545287 := bstep (se 1 (by rfl) ⟨3408965, by rfl⟩ : syracuseStep 4545287 = 6817931) B6817931
theorem B2046791 : Blo 1344991 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B2554735 : Blo 1344991 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B8629355 : Blo 1344991 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B4095137 : Blo 1344991 4095137 := bstep (se 2 (by rfl) ⟨1535676, by rfl⟩ : syracuseStep 4095137 = 3071353) B3071353
theorem B10214747 : Blo 1344991 10214747 := bstep (se 1 (by rfl) ⟨7661060, by rfl⟩ : syracuseStep 10214747 = 15322121) B15322121
theorem B1916399 : Blo 1344991 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B6135407 : Blo 1344991 6135407 := bstep (se 1 (by rfl) ⟨4601555, by rfl⟩ : syracuseStep 6135407 = 9203111) B9203111
theorem B39353971 : Blo 1344991 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B1515163 : Blo 1344991 1515163 := bstep (se 1 (by rfl) ⟨1136372, by rfl⟩ : syracuseStep 1515163 = 2272745) B2272745
theorem B1515199 : Blo 1344991 1515199 := bstep (se 1 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 1515199 = 2272799) B2272799
theorem B3407771 : Blo 1344991 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B3408115 : Blo 1344991 3408115 := bstep (se 1 (by rfl) ⟨2556086, by rfl⟩ : syracuseStep 3408115 = 5112173) B5112173
theorem B23011613 : Blo 1344991 23011613 := bstep (se 3 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 23011613 = 8629355) B8629355
theorem B10215719 : Blo 1344991 10215719 := bstep (se 1 (by rfl) ⟨7661789, by rfl⟩ : syracuseStep 10215719 = 15323579) B15323579
theorem B10223981 : Blo 1344991 10223981 := bstep (se 3 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 10223981 = 3833993) B3833993
theorem B10920365 : Blo 1344991 10920365 := bstep (se 3 (by rfl) ⟨2047568, by rfl⟩ : syracuseStep 10920365 = 4095137) B4095137
theorem B3408551 : Blo 1344991 3408551 := bstep (se 1 (by rfl) ⟨2556413, by rfl⟩ : syracuseStep 3408551 = 5112827) B5112827
theorem B31089595 : Blo 1344991 31089595 := bstep (se 1 (by rfl) ⟨23317196, by rfl⟩ : syracuseStep 31089595 = 46634393) B46634393
theorem B5112841 : Blo 1344991 5112841 := bstep (se 2 (by rfl) ⟨1917315, by rfl⟩ : syracuseStep 5112841 = 3834631) B3834631
theorem B3409087 : Blo 1344991 3409087 := bstep (se 1 (by rfl) ⟨2556815, by rfl⟩ : syracuseStep 3409087 = 5113631) B5113631
theorem B10224953 : Blo 1344991 10224953 := bstep (se 2 (by rfl) ⟨3834357, by rfl⟩ : syracuseStep 10224953 = 7668715) B7668715
theorem B1345007 : Blo 1344991 1345007 := bstep (se 1 (by rfl) ⟨1008755, by rfl⟩ : syracuseStep 1345007 = 2017511) B2017511
theorem B15320663 : Blo 1344991 15320663 := bstep (se 1 (by rfl) ⟨11490497, by rfl⟩ : syracuseStep 15320663 = 22980995) B22980995
theorem B1345127 : Blo 1344991 1345127 := bstep (se 1 (by rfl) ⟨1008845, by rfl⟩ : syracuseStep 1345127 = 2017691) B2017691
theorem B3638953 : Blo 1344991 3638953 := bstep (se 2 (by rfl) ⟨1364607, by rfl⟩ : syracuseStep 3638953 = 2729215) B2729215
theorem B10225439 : Blo 1344991 10225439 := bstep (se 1 (by rfl) ⟨7669079, by rfl⟩ : syracuseStep 10225439 = 15338159) B15338159
theorem B1345407 : Blo 1344991 1345407 := bstep (se 1 (by rfl) ⟨1009055, by rfl⟩ : syracuseStep 1345407 = 2018111) B2018111
theorem B6817769 : Blo 1344991 6817769 := bstep (se 2 (by rfl) ⟨2556663, by rfl⟩ : syracuseStep 6817769 = 5113327) B5113327
theorem B1345627 : Blo 1344991 1345627 := bstep (se 1 (by rfl) ⟨1009220, by rfl⟩ : syracuseStep 1345627 = 2018441) B2018441
theorem B1345663 : Blo 1344991 1345663 := bstep (se 1 (by rfl) ⟨1009247, by rfl⟩ : syracuseStep 1345663 = 2018495) B2018495
theorem B52471961 : Blo 1344991 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B6809831 : Blo 1344991 6809831 := bstep (se 1 (by rfl) ⟨5107373, by rfl⟩ : syracuseStep 6809831 = 10214747) B10214747
theorem B1345855 : Blo 1344991 1345855 := bstep (se 1 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 1345855 = 2018783) B2018783
theorem B1345895 : Blo 1344991 1345895 := bstep (se 1 (by rfl) ⟨1009421, by rfl⟩ : syracuseStep 1345895 = 2018843) B2018843
theorem B4090271 : Blo 1344991 4090271 := bstep (se 1 (by rfl) ⟨3067703, by rfl⟩ : syracuseStep 4090271 = 6135407) B6135407
theorem B38799809 : Blo 1344991 38799809 := bstep (se 2 (by rfl) ⟨14549928, by rfl⟩ : syracuseStep 38799809 = 29099857) B29099857
theorem B2017847 : Blo 1344991 2017847 := bstep (se 1 (by rfl) ⟨1513385, by rfl⟩ : syracuseStep 2017847 = 3026771) B3026771
theorem B2271847 : Blo 1344991 2271847 := bstep (se 1 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 2271847 = 3407771) B3407771
theorem B1346175 : Blo 1344991 1346175 := bstep (se 1 (by rfl) ⟨1009631, by rfl⟩ : syracuseStep 1346175 = 2019263) B2019263
theorem B14756509 : Blo 1344991 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B22440619 : Blo 1344991 22440619 := bstep (se 1 (by rfl) ⟨16830464, by rfl⟩ : syracuseStep 22440619 = 33660929) B33660929
theorem B2157263 : Blo 1344991 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B10226411 : Blo 1344991 10226411 := bstep (se 1 (by rfl) ⟨7669808, by rfl⟩ : syracuseStep 10226411 = 15339617) B15339617
theorem B4607225 : Blo 1344991 4607225 := bstep (se 2 (by rfl) ⟨1727709, by rfl⟩ : syracuseStep 4607225 = 3455419) B3455419
theorem B7671131 : Blo 1344991 7671131 := bstep (se 1 (by rfl) ⟨5753348, by rfl⟩ : syracuseStep 7671131 = 11506697) B11506697
theorem B5828071 : Blo 1344991 5828071 := bstep (se 1 (by rfl) ⟨4371053, by rfl⟩ : syracuseStep 5828071 = 8742107) B8742107
theorem B2018975 : Blo 1344991 2018975 := bstep (se 1 (by rfl) ⟨1514231, by rfl⟩ : syracuseStep 2018975 = 3028463) B3028463
theorem B3026663 : Blo 1344991 3026663 := bstep (se 1 (by rfl) ⟨2269997, by rfl⟩ : syracuseStep 3026663 = 4539995) B4539995
theorem B22720675 : Blo 1344991 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B5107967 : Blo 1344991 5107967 := bstep (se 1 (by rfl) ⟨3830975, by rfl⟩ : syracuseStep 5107967 = 7661951) B7661951
theorem B57643325 : Blo 1344991 57643325 := bstep (se 3 (by rfl) ⟨10808123, by rfl⟩ : syracuseStep 57643325 = 21616247) B21616247
theorem B1364527 : Blo 1344991 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B10908269 : Blo 1344991 10908269 := bstep (se 3 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 10908269 = 4090601) B4090601
theorem B2020217 : Blo 1344991 2020217 := bstep (se 2 (by rfl) ⟨757581, by rfl⟩ : syracuseStep 2020217 = 1515163) B1515163
theorem B2020265 : Blo 1344991 2020265 := bstep (se 2 (by rfl) ⟨757599, by rfl⟩ : syracuseStep 2020265 = 1515199) B1515199
theorem B15545317 : Blo 1344991 15545317 := bstep (se 4 (by rfl) ⟨1457373, by rfl⟩ : syracuseStep 15545317 = 2914747) B2914747
theorem B3027995 : Blo 1344991 3027995 := bstep (se 1 (by rfl) ⟨2270996, by rfl⟩ : syracuseStep 3027995 = 4541993) B4541993
theorem B3454073 : Blo 1344991 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B5461415 : Blo 1344991 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B3028553 : Blo 1344991 3028553 := bstep (se 2 (by rfl) ⟨1135707, by rfl⟩ : syracuseStep 3028553 = 2271415) B2271415
theorem B46610423 : Blo 1344991 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B16365563 : Blo 1344991 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B2873531 : Blo 1344991 2873531 := bstep (se 1 (by rfl) ⟨2155148, by rfl⟩ : syracuseStep 2873531 = 4310297) B4310297
theorem B1513723 : Blo 1344991 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B10352951 : Blo 1344991 10352951 := bstep (se 1 (by rfl) ⟨7764713, by rfl⟩ : syracuseStep 10352951 = 15529427) B15529427
theorem B3406313 : Blo 1344991 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B5110397 : Blo 1344991 5110397 := bstep (se 3 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 5110397 = 1916399) B1916399
theorem B36838273 : Blo 1344991 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B17488885 : Blo 1344991 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B3030191 : Blo 1344991 3030191 := bstep (se 1 (by rfl) ⟨2272643, by rfl⟩ : syracuseStep 3030191 = 4545287) B4545287
theorem B15326495 : Blo 1344991 15326495 := bstep (se 1 (by rfl) ⟨11494871, by rfl⟩ : syracuseStep 15326495 = 22989743) B22989743
theorem B3030497 : Blo 1344991 3030497 := bstep (se 2 (by rfl) ⟨1136436, by rfl⟩ : syracuseStep 3030497 = 2272873) B2272873
theorem B73653785 : Blo 1344991 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B1515055 : Blo 1344991 1515055 := bstep (se 1 (by rfl) ⟨1136291, by rfl⟩ : syracuseStep 1515055 = 2272583) B2272583
theorem B12934889 : Blo 1344991 12934889 := bstep (se 2 (by rfl) ⟨4850583, by rfl⟩ : syracuseStep 12934889 = 9701167) B9701167
theorem B38428883 : Blo 1344991 38428883 := bstep (se 1 (by rfl) ⟨28821662, by rfl⟩ : syracuseStep 38428883 = 57643325) B57643325
theorem B30294233 : Blo 1344991 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B6815987 : Blo 1344991 6815987 := bstep (se 1 (by rfl) ⟨5111990, by rfl⟩ : syracuseStep 6815987 = 10223981) B10223981
theorem B1819369 : Blo 1344991 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B2302715 : Blo 1344991 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B6816635 : Blo 1344991 6816635 := bstep (se 1 (by rfl) ⟨5112476, by rfl⟩ : syracuseStep 6816635 = 10224953) B10224953
theorem B6816959 : Blo 1344991 6816959 := bstep (se 1 (by rfl) ⟨5112719, by rfl⟩ : syracuseStep 6816959 = 10225439) B10225439
theorem B41452793 : Blo 1344991 41452793 := bstep (se 2 (by rfl) ⟨15544797, by rfl⟩ : syracuseStep 41452793 = 31089595) B31089595
theorem B20727089 : Blo 1344991 20727089 := bstep (se 2 (by rfl) ⟨7772658, by rfl⟩ : syracuseStep 20727089 = 15545317) B15545317
theorem B31073615 : Blo 1344991 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B6817121 : Blo 1344991 6817121 := bstep (se 2 (by rfl) ⟨2556420, by rfl⟩ : syracuseStep 6817121 = 5112841) B5112841
theorem B34981307 : Blo 1344991 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B4539887 : Blo 1344991 4539887 := bstep (se 1 (by rfl) ⟨3404915, by rfl⟩ : syracuseStep 4539887 = 6809831) B6809831
theorem B2270875 : Blo 1344991 2270875 := bstep (se 1 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 2270875 = 3406313) B3406313
theorem B1345231 : Blo 1344991 1345231 := bstep (se 1 (by rfl) ⟨1008923, by rfl⟩ : syracuseStep 1345231 = 2017847) B2017847
theorem B6817607 : Blo 1344991 6817607 := bstep (se 1 (by rfl) ⟨5113205, by rfl⟩ : syracuseStep 6817607 = 10226411) B10226411
theorem B10217663 : Blo 1344991 10217663 := bstep (se 1 (by rfl) ⟨7663247, by rfl⟩ : syracuseStep 10217663 = 15326495) B15326495
theorem B4851937 : Blo 1344991 4851937 := bstep (se 2 (by rfl) ⟨1819476, by rfl⟩ : syracuseStep 4851937 = 3638953) B3638953
theorem B5114087 : Blo 1344991 5114087 := bstep (se 1 (by rfl) ⟨3835565, by rfl⟩ : syracuseStep 5114087 = 7671131) B7671131
theorem B1345983 : Blo 1344991 1345983 := bstep (se 1 (by rfl) ⟨1009487, by rfl⟩ : syracuseStep 1345983 = 2018975) B2018975
theorem B2017775 : Blo 1344991 2017775 := bstep (se 1 (by rfl) ⟨1513331, by rfl⟩ : syracuseStep 2017775 = 3026663) B3026663
theorem B6810479 : Blo 1344991 6810479 := bstep (se 1 (by rfl) ⟨5107859, by rfl⟩ : syracuseStep 6810479 = 10215719) B10215719
theorem B2018297 : Blo 1344991 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B2272367 : Blo 1344991 2272367 := bstep (se 1 (by rfl) ⟨1704275, by rfl⟩ : syracuseStep 2272367 = 3408551) B3408551
theorem B1346811 : Blo 1344991 1346811 := bstep (se 1 (by rfl) ⟨1010108, by rfl⟩ : syracuseStep 1346811 = 2020217) B2020217
theorem B1346843 : Blo 1344991 1346843 := bstep (se 1 (by rfl) ⟨1010132, by rfl⟩ : syracuseStep 1346843 = 2020265) B2020265
theorem B2018663 : Blo 1344991 2018663 := bstep (se 1 (by rfl) ⟨1513997, by rfl⟩ : syracuseStep 2018663 = 3027995) B3027995
theorem B29920825 : Blo 1344991 29920825 := bstep (se 2 (by rfl) ⟨11220309, by rfl⟩ : syracuseStep 29920825 = 22440619) B22440619
theorem B3640943 : Blo 1344991 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B2019035 : Blo 1344991 2019035 := bstep (se 1 (by rfl) ⟨1514276, by rfl⟩ : syracuseStep 2019035 = 3028553) B3028553
theorem B10907389 : Blo 1344991 10907389 := bstep (se 3 (by rfl) ⟨2045135, by rfl⟩ : syracuseStep 10907389 = 4090271) B4090271
theorem B23318513 : Blo 1344991 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B6901967 : Blo 1344991 6901967 := bstep (se 1 (by rfl) ⟨5176475, by rfl⟩ : syracuseStep 6901967 = 10352951) B10352951
theorem B25866539 : Blo 1344991 25866539 := bstep (se 1 (by rfl) ⟨19399904, by rfl⟩ : syracuseStep 25866539 = 38799809) B38799809
theorem B1438175 : Blo 1344991 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B7770761 : Blo 1344991 7770761 := bstep (se 2 (by rfl) ⟨2914035, by rfl⟩ : syracuseStep 7770761 = 5828071) B5828071
theorem B2020073 : Blo 1344991 2020073 := bstep (se 2 (by rfl) ⟨757527, by rfl⟩ : syracuseStep 2020073 = 1515055) B1515055
theorem B2020127 : Blo 1344991 2020127 := bstep (se 1 (by rfl) ⟨1515095, by rfl⟩ : syracuseStep 2020127 = 3030191) B3030191
theorem B2020331 : Blo 1344991 2020331 := bstep (se 1 (by rfl) ⟨1515248, by rfl⟩ : syracuseStep 2020331 = 3030497) B3030497
theorem B8623259 : Blo 1344991 8623259 := bstep (se 1 (by rfl) ⟨6467444, by rfl⟩ : syracuseStep 8623259 = 12934889) B12934889
theorem B3405311 : Blo 1344991 3405311 := bstep (se 1 (by rfl) ⟨2553983, by rfl⟩ : syracuseStep 3405311 = 5107967) B5107967
theorem B15341075 : Blo 1344991 15341075 := bstep (se 1 (by rfl) ⟨11505806, by rfl⟩ : syracuseStep 15341075 = 23011613) B23011613
theorem B7280243 : Blo 1344991 7280243 := bstep (se 1 (by rfl) ⟨5460182, by rfl⟩ : syracuseStep 7280243 = 10920365) B10920365
theorem B4544153 : Blo 1344991 4544153 := bstep (se 2 (by rfl) ⟨1704057, by rfl⟩ : syracuseStep 4544153 = 3408115) B3408115
theorem B7272179 : Blo 1344991 7272179 := bstep (se 1 (by rfl) ⟨5454134, by rfl⟩ : syracuseStep 7272179 = 10908269) B10908269
theorem B3029129 : Blo 1344991 3029129 := bstep (se 2 (by rfl) ⟨1135923, by rfl⟩ : syracuseStep 3029129 = 2271847) B2271847
theorem B19675345 : Blo 1344991 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B10213775 : Blo 1344991 10213775 := bstep (se 1 (by rfl) ⟨7660331, by rfl⟩ : syracuseStep 10213775 = 15320663) B15320663
theorem B49117697 : Blo 1344991 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B4545179 : Blo 1344991 4545179 := bstep (se 1 (by rfl) ⟨3408884, by rfl⟩ : syracuseStep 4545179 = 6817769) B6817769
theorem B10910375 : Blo 1344991 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B1915687 : Blo 1344991 1915687 := bstep (se 1 (by rfl) ⟨1436765, by rfl⟩ : syracuseStep 1915687 = 2873531) B2873531
theorem B4545449 : Blo 1344991 4545449 := bstep (se 2 (by rfl) ⟨1704543, by rfl⟩ : syracuseStep 4545449 = 3409087) B3409087
theorem B3406931 : Blo 1344991 3406931 := bstep (se 1 (by rfl) ⟨2555198, by rfl⟩ : syracuseStep 3406931 = 5110397) B5110397
theorem B3071483 : Blo 1344991 3071483 := bstep (se 1 (by rfl) ⟨2303612, by rfl⟩ : syracuseStep 3071483 = 4607225) B4607225
theorem B49102523 : Blo 1344991 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B17244359 : Blo 1344991 17244359 := bstep (se 1 (by rfl) ⟨12933269, by rfl⟩ : syracuseStep 17244359 = 25866539) B25866539
theorem B2425825 : Blo 1344991 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B2270207 : Blo 1344991 2270207 := bstep (se 1 (by rfl) ⟨1702655, by rfl⟩ : syracuseStep 2270207 = 3405311) B3405311
theorem B3835133 : Blo 1344991 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B3409391 : Blo 1344991 3409391 := bstep (se 1 (by rfl) ⟨2557043, by rfl⟩ : syracuseStep 3409391 = 5114087) B5114087
theorem B6809183 : Blo 1344991 6809183 := bstep (se 1 (by rfl) ⟨5106887, by rfl⟩ : syracuseStep 6809183 = 10213775) B10213775
theorem B1345183 : Blo 1344991 1345183 := bstep (se 1 (by rfl) ⟨1008887, by rfl⟩ : syracuseStep 1345183 = 2017775) B2017775
theorem B32745131 : Blo 1344991 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B4540319 : Blo 1344991 4540319 := bstep (se 1 (by rfl) ⟨3405239, by rfl⟩ : syracuseStep 4540319 = 6810479) B6810479
theorem B1345531 : Blo 1344991 1345531 := bstep (se 1 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 1345531 = 2018297) B2018297
theorem B2271287 : Blo 1344991 2271287 := bstep (se 1 (by rfl) ⟨1703465, by rfl⟩ : syracuseStep 2271287 = 3406931) B3406931
theorem B1345775 : Blo 1344991 1345775 := bstep (se 1 (by rfl) ⟨1009331, by rfl⟩ : syracuseStep 1345775 = 2018663) B2018663
theorem B14543185 : Blo 1344991 14543185 := bstep (se 2 (by rfl) ⟨5453694, by rfl⟩ : syracuseStep 14543185 = 10907389) B10907389
theorem B2427295 : Blo 1344991 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B1346023 : Blo 1344991 1346023 := bstep (se 1 (by rfl) ⟨1009517, by rfl⟩ : syracuseStep 1346023 = 2019035) B2019035
theorem B25619255 : Blo 1344991 25619255 := bstep (se 1 (by rfl) ⟨19214441, by rfl⟩ : syracuseStep 25619255 = 38428883) B38428883
theorem B20196155 : Blo 1344991 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B26233793 : Blo 1344991 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B5180507 : Blo 1344991 5180507 := bstep (se 1 (by rfl) ⟨3885380, by rfl⟩ : syracuseStep 5180507 = 7770761) B7770761
theorem B1346715 : Blo 1344991 1346715 := bstep (se 1 (by rfl) ⟨1010036, by rfl⟩ : syracuseStep 1346715 = 2020073) B2020073
theorem B1346751 : Blo 1344991 1346751 := bstep (se 1 (by rfl) ⟨1010063, by rfl⟩ : syracuseStep 1346751 = 2020127) B2020127
theorem B1346887 : Blo 1344991 1346887 := bstep (se 1 (by rfl) ⟨1010165, by rfl⟩ : syracuseStep 1346887 = 2020331) B2020331
theorem B27635195 : Blo 1344991 27635195 := bstep (se 1 (by rfl) ⟨20726396, by rfl⟩ : syracuseStep 27635195 = 41452793) B41452793
theorem B3026591 : Blo 1344991 3026591 := bstep (se 1 (by rfl) ⟨2269943, by rfl⟩ : syracuseStep 3026591 = 4539887) B4539887
theorem B10227383 : Blo 1344991 10227383 := bstep (se 1 (by rfl) ⟨7670537, by rfl⟩ : syracuseStep 10227383 = 15341075) B15341075
theorem B4853495 : Blo 1344991 4853495 := bstep (se 1 (by rfl) ⟨3640121, by rfl⟩ : syracuseStep 4853495 = 7280243) B7280243
theorem B2019419 : Blo 1344991 2019419 := bstep (se 1 (by rfl) ⟨1514564, by rfl⟩ : syracuseStep 2019419 = 3029129) B3029129
theorem B6811775 : Blo 1344991 6811775 := bstep (se 1 (by rfl) ⟨5108831, by rfl⟩ : syracuseStep 6811775 = 10217663) B10217663
theorem B6140573 : Blo 1344991 6140573 := bstep (se 3 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 6140573 = 2302715) B2302715
theorem B3027833 : Blo 1344991 3027833 := bstep (se 2 (by rfl) ⟨1135437, by rfl⟩ : syracuseStep 3027833 = 2270875) B2270875
theorem B15545675 : Blo 1344991 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B4543991 : Blo 1344991 4543991 := bstep (se 1 (by rfl) ⟨3407993, by rfl⟩ : syracuseStep 4543991 = 6815987) B6815987
theorem B6469249 : Blo 1344991 6469249 := bstep (se 2 (by rfl) ⟨2425968, by rfl⟩ : syracuseStep 6469249 = 4851937) B4851937
theorem B18405245 : Blo 1344991 18405245 := bstep (se 3 (by rfl) ⟨3450983, by rfl⟩ : syracuseStep 18405245 = 6901967) B6901967
theorem B4544423 : Blo 1344991 4544423 := bstep (se 1 (by rfl) ⟨3408317, by rfl⟩ : syracuseStep 4544423 = 6816635) B6816635
theorem B5748839 : Blo 1344991 5748839 := bstep (se 1 (by rfl) ⟨4311629, by rfl⟩ : syracuseStep 5748839 = 8623259) B8623259
theorem B4544639 : Blo 1344991 4544639 := bstep (se 1 (by rfl) ⟨3408479, by rfl⟩ : syracuseStep 4544639 = 6816959) B6816959
theorem B13818059 : Blo 1344991 13818059 := bstep (se 1 (by rfl) ⟨10363544, by rfl⟩ : syracuseStep 13818059 = 20727089) B20727089
theorem B20715743 : Blo 1344991 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B4544747 : Blo 1344991 4544747 := bstep (se 1 (by rfl) ⟨3408560, by rfl⟩ : syracuseStep 4544747 = 6817121) B6817121
theorem B23320871 : Blo 1344991 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B2554249 : Blo 1344991 2554249 := bstep (se 2 (by rfl) ⟨957843, by rfl⟩ : syracuseStep 2554249 = 1915687) B1915687
theorem B3029435 : Blo 1344991 3029435 := bstep (se 1 (by rfl) ⟨2272076, by rfl⟩ : syracuseStep 3029435 = 4544153) B4544153
theorem B4848119 : Blo 1344991 4848119 := bstep (se 1 (by rfl) ⟨3636089, by rfl⟩ : syracuseStep 4848119 = 7272179) B7272179
theorem B4545071 : Blo 1344991 4545071 := bstep (se 1 (by rfl) ⟨3408803, by rfl⟩ : syracuseStep 4545071 = 6817607) B6817607
theorem B3030119 : Blo 1344991 3030119 := bstep (se 1 (by rfl) ⟨2272589, by rfl⟩ : syracuseStep 3030119 = 4545179) B4545179
theorem B7273583 : Blo 1344991 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B3030299 : Blo 1344991 3030299 := bstep (se 1 (by rfl) ⟨2272724, by rfl⟩ : syracuseStep 3030299 = 4545449) B4545449
theorem B1514911 : Blo 1344991 1514911 := bstep (se 1 (by rfl) ⟨1136183, by rfl⟩ : syracuseStep 1514911 = 2272367) B2272367
theorem B39894433 : Blo 1344991 39894433 := bstep (se 2 (by rfl) ⟨14960412, by rfl⟩ : syracuseStep 39894433 = 29920825) B29920825
theorem B2047655 : Blo 1344991 2047655 := bstep (se 1 (by rfl) ⟨1535741, by rfl⟩ : syracuseStep 2047655 = 3071483) B3071483
theorem B32735015 : Blo 1344991 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B19390913 : Blo 1344991 19390913 := bstep (se 2 (by rfl) ⟨7271592, by rfl⟩ : syracuseStep 19390913 = 14543185) B14543185
theorem B3236393 : Blo 1344991 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B2556755 : Blo 1344991 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B10363783 : Blo 1344991 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B4539455 : Blo 1344991 4539455 := bstep (se 1 (by rfl) ⟨3404591, by rfl⟩ : syracuseStep 4539455 = 6809183) B6809183
theorem B2017727 : Blo 1344991 2017727 := bstep (se 1 (by rfl) ⟨1513295, by rfl⟩ : syracuseStep 2017727 = 3026591) B3026591
theorem B6818255 : Blo 1344991 6818255 := bstep (se 1 (by rfl) ⟨5113691, by rfl⟩ : syracuseStep 6818255 = 10227383) B10227383
theorem B1346279 : Blo 1344991 1346279 := bstep (se 1 (by rfl) ⟨1009709, by rfl⟩ : syracuseStep 1346279 = 2019419) B2019419
theorem B4541183 : Blo 1344991 4541183 := bstep (se 1 (by rfl) ⟨3405887, by rfl⟩ : syracuseStep 4541183 = 6811775) B6811775
theorem B11496239 : Blo 1344991 11496239 := bstep (se 1 (by rfl) ⟨8622179, by rfl⟩ : syracuseStep 11496239 = 17244359) B17244359
theorem B2018555 : Blo 1344991 2018555 := bstep (se 1 (by rfl) ⟨1513916, by rfl⟩ : syracuseStep 2018555 = 3027833) B3027833
theorem B2272927 : Blo 1344991 2272927 := bstep (se 1 (by rfl) ⟨1704695, by rfl⟩ : syracuseStep 2272927 = 3409391) B3409391
theorem B3026879 : Blo 1344991 3026879 := bstep (se 1 (by rfl) ⟨2270159, by rfl⟩ : syracuseStep 3026879 = 4540319) B4540319
theorem B9212039 : Blo 1344991 9212039 := bstep (se 1 (by rfl) ⟨6909029, by rfl⟩ : syracuseStep 9212039 = 13818059) B13818059
theorem B2019623 : Blo 1344991 2019623 := bstep (se 1 (by rfl) ⟨1514717, by rfl⟩ : syracuseStep 2019623 = 3029435) B3029435
theorem B3232079 : Blo 1344991 3232079 := bstep (se 1 (by rfl) ⟨2424059, by rfl⟩ : syracuseStep 3232079 = 4848119) B4848119
theorem B13464103 : Blo 1344991 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B2019881 : Blo 1344991 2019881 := bstep (se 2 (by rfl) ⟨757455, by rfl⟩ : syracuseStep 2019881 = 1514911) B1514911
theorem B3453671 : Blo 1344991 3453671 := bstep (se 1 (by rfl) ⟨2590253, by rfl⟩ : syracuseStep 3453671 = 5180507) B5180507
theorem B2020079 : Blo 1344991 2020079 := bstep (se 1 (by rfl) ⟨1515059, by rfl⟩ : syracuseStep 2020079 = 3030119) B3030119
theorem B2020199 : Blo 1344991 2020199 := bstep (se 1 (by rfl) ⟨1515149, by rfl⟩ : syracuseStep 2020199 = 3030299) B3030299
theorem B1365103 : Blo 1344991 1365103 := bstep (se 1 (by rfl) ⟨1023827, by rfl⟩ : syracuseStep 1365103 = 2047655) B2047655
theorem B4093715 : Blo 1344991 4093715 := bstep (se 1 (by rfl) ⟨3070286, by rfl⟩ : syracuseStep 4093715 = 6140573) B6140573
theorem B3405665 : Blo 1344991 3405665 := bstep (se 2 (by rfl) ⟨1277124, by rfl⟩ : syracuseStep 3405665 = 2554249) B2554249
theorem B1513471 : Blo 1344991 1513471 := bstep (se 1 (by rfl) ⟨1135103, by rfl⟩ : syracuseStep 1513471 = 2270207) B2270207
theorem B3029327 : Blo 1344991 3029327 := bstep (se 1 (by rfl) ⟨2271995, by rfl⟩ : syracuseStep 3029327 = 4543991) B4543991
theorem B21830087 : Blo 1344991 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B12270163 : Blo 1344991 12270163 := bstep (se 1 (by rfl) ⟨9202622, by rfl⟩ : syracuseStep 12270163 = 18405245) B18405245
theorem B3029615 : Blo 1344991 3029615 := bstep (se 1 (by rfl) ⟨2272211, by rfl⟩ : syracuseStep 3029615 = 4544423) B4544423
theorem B3234433 : Blo 1344991 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B1514191 : Blo 1344991 1514191 := bstep (se 1 (by rfl) ⟨1135643, by rfl⟩ : syracuseStep 1514191 = 2271287) B2271287
theorem B3832559 : Blo 1344991 3832559 := bstep (se 1 (by rfl) ⟨2874419, by rfl⟩ : syracuseStep 3832559 = 5748839) B5748839
theorem B3029759 : Blo 1344991 3029759 := bstep (se 1 (by rfl) ⟨2272319, by rfl⟩ : syracuseStep 3029759 = 4544639) B4544639
theorem B13810495 : Blo 1344991 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B3029831 : Blo 1344991 3029831 := bstep (se 1 (by rfl) ⟨2272373, by rfl⟩ : syracuseStep 3029831 = 4544747) B4544747
theorem B15547247 : Blo 1344991 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B3030047 : Blo 1344991 3030047 := bstep (se 1 (by rfl) ⟨2272535, by rfl⟩ : syracuseStep 3030047 = 4545071) B4545071
theorem B17079503 : Blo 1344991 17079503 := bstep (se 1 (by rfl) ⟨12809627, by rfl⟩ : syracuseStep 17079503 = 25619255) B25619255
theorem B17489195 : Blo 1344991 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B4849055 : Blo 1344991 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B8625665 : Blo 1344991 8625665 := bstep (se 2 (by rfl) ⟨3234624, by rfl⟩ : syracuseStep 8625665 = 6469249) B6469249
theorem B212770309 : Blo 1344991 212770309 := bstep (se 4 (by rfl) ⟨19947216, by rfl⟩ : syracuseStep 212770309 = 39894433) B39894433
theorem B18423463 : Blo 1344991 18423463 := bstep (se 1 (by rfl) ⟨13817597, by rfl⟩ : syracuseStep 18423463 = 27635195) B27635195
theorem B3235663 : Blo 1344991 3235663 := bstep (se 1 (by rfl) ⟨2426747, by rfl⟩ : syracuseStep 3235663 = 4853495) B4853495
theorem B21823343 : Blo 1344991 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B2154719 : Blo 1344991 2154719 := bstep (se 1 (by rfl) ⟨1616039, by rfl⟩ : syracuseStep 2154719 = 3232079) B3232079
theorem B12927275 : Blo 1344991 12927275 := bstep (se 1 (by rfl) ⟨9695456, by rfl⟩ : syracuseStep 12927275 = 19390913) B19390913
theorem B2302447 : Blo 1344991 2302447 := bstep (se 1 (by rfl) ⟨1726835, by rfl⟩ : syracuseStep 2302447 = 3453671) B3453671
theorem B1704503 : Blo 1344991 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B16360217 : Blo 1344991 16360217 := bstep (se 2 (by rfl) ⟨6135081, by rfl⟩ : syracuseStep 16360217 = 12270163) B12270163
theorem B2729143 : Blo 1344991 2729143 := bstep (se 1 (by rfl) ⟨2046857, by rfl⟩ : syracuseStep 2729143 = 4093715) B4093715
theorem B2270443 : Blo 1344991 2270443 := bstep (se 1 (by rfl) ⟨1702832, by rfl⟩ : syracuseStep 2270443 = 3405665) B3405665
theorem B1820137 : Blo 1344991 1820137 := bstep (se 2 (by rfl) ⟨682551, by rfl⟩ : syracuseStep 1820137 = 1365103) B1365103
theorem B1345151 : Blo 1344991 1345151 := bstep (se 1 (by rfl) ⟨1008863, by rfl⟩ : syracuseStep 1345151 = 2017727) B2017727
theorem B10364831 : Blo 1344991 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B1345703 : Blo 1344991 1345703 := bstep (se 1 (by rfl) ⟨1009277, by rfl⟩ : syracuseStep 1345703 = 2018555) B2018555
theorem B11659463 : Blo 1344991 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B2017919 : Blo 1344991 2017919 := bstep (se 1 (by rfl) ⟨1513439, by rfl⟩ : syracuseStep 2017919 = 3026879) B3026879
theorem B2017961 : Blo 1344991 2017961 := bstep (se 2 (by rfl) ⟨756735, by rfl⟩ : syracuseStep 2017961 = 1513471) B1513471
theorem B1346415 : Blo 1344991 1346415 := bstep (se 1 (by rfl) ⟨1009811, by rfl⟩ : syracuseStep 1346415 = 2019623) B2019623
theorem B1346587 : Blo 1344991 1346587 := bstep (se 1 (by rfl) ⟨1009940, by rfl⟩ : syracuseStep 1346587 = 2019881) B2019881
theorem B1346719 : Blo 1344991 1346719 := bstep (se 1 (by rfl) ⟨1010039, by rfl⟩ : syracuseStep 1346719 = 2020079) B2020079
theorem B1346799 : Blo 1344991 1346799 := bstep (se 1 (by rfl) ⟨1010099, by rfl⟩ : syracuseStep 1346799 = 2020199) B2020199
theorem B3026303 : Blo 1344991 3026303 := bstep (se 1 (by rfl) ⟨2269727, by rfl⟩ : syracuseStep 3026303 = 4539455) B4539455
theorem B17952137 : Blo 1344991 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B4312577 : Blo 1344991 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B2018921 : Blo 1344991 2018921 := bstep (se 2 (by rfl) ⟨757095, by rfl⟩ : syracuseStep 2018921 = 1514191) B1514191
theorem B8630381 : Blo 1344991 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B2019551 : Blo 1344991 2019551 := bstep (se 1 (by rfl) ⟨1514663, by rfl⟩ : syracuseStep 2019551 = 3029327) B3029327
theorem B14553391 : Blo 1344991 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B2019743 : Blo 1344991 2019743 := bstep (se 1 (by rfl) ⟨1514807, by rfl⟩ : syracuseStep 2019743 = 3029615) B3029615
theorem B3027455 : Blo 1344991 3027455 := bstep (se 1 (by rfl) ⟨2270591, by rfl⟩ : syracuseStep 3027455 = 4541183) B4541183
theorem B2019839 : Blo 1344991 2019839 := bstep (se 1 (by rfl) ⟨1514879, by rfl⟩ : syracuseStep 2019839 = 3029759) B3029759
theorem B7664159 : Blo 1344991 7664159 := bstep (se 1 (by rfl) ⟨5748119, by rfl⟩ : syracuseStep 7664159 = 11496239) B11496239
theorem B2019887 : Blo 1344991 2019887 := bstep (se 1 (by rfl) ⟨1514915, by rfl⟩ : syracuseStep 2019887 = 3029831) B3029831
theorem B283693745 : Blo 1344991 283693745 := bstep (se 2 (by rfl) ⟨106385154, by rfl⟩ : syracuseStep 283693745 = 212770309) B212770309
theorem B2020031 : Blo 1344991 2020031 := bstep (se 1 (by rfl) ⟨1515023, by rfl⟩ : syracuseStep 2020031 = 3030047) B3030047
theorem B24564617 : Blo 1344991 24564617 := bstep (se 2 (by rfl) ⟨9211731, by rfl⟩ : syracuseStep 24564617 = 18423463) B18423463
theorem B3232703 : Blo 1344991 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B4314217 : Blo 1344991 4314217 := bstep (se 2 (by rfl) ⟨1617831, by rfl⟩ : syracuseStep 4314217 = 3235663) B3235663
theorem B6141359 : Blo 1344991 6141359 := bstep (se 1 (by rfl) ⟨4606019, by rfl⟩ : syracuseStep 6141359 = 9212039) B9212039
theorem B45545341 : Blo 1344991 45545341 := bstep (se 3 (by rfl) ⟨8539751, by rfl⟩ : syracuseStep 45545341 = 17079503) B17079503
theorem B18413993 : Blo 1344991 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B13818377 : Blo 1344991 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B4545503 : Blo 1344991 4545503 := bstep (se 1 (by rfl) ⟨3409127, by rfl⟩ : syracuseStep 4545503 = 6818255) B6818255
theorem B2555039 : Blo 1344991 2555039 := bstep (se 1 (by rfl) ⟨1916279, by rfl⟩ : syracuseStep 2555039 = 3832559) B3832559
theorem B3030569 : Blo 1344991 3030569 := bstep (se 2 (by rfl) ⟨1136463, by rfl⟩ : syracuseStep 3030569 = 2272927) B2272927
theorem B5750443 : Blo 1344991 5750443 := bstep (se 1 (by rfl) ⟨4312832, by rfl⟩ : syracuseStep 5750443 = 8625665) B8625665
theorem B14548895 : Blo 1344991 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B8618183 : Blo 1344991 8618183 := bstep (se 1 (by rfl) ⟨6463637, by rfl⟩ : syracuseStep 8618183 = 12927275) B12927275
theorem B189129163 : Blo 1344991 189129163 := bstep (se 1 (by rfl) ⟨141846872, by rfl⟩ : syracuseStep 189129163 = 283693745) B283693745
theorem B16376411 : Blo 1344991 16376411 := bstep (se 1 (by rfl) ⟨12282308, by rfl⟩ : syracuseStep 16376411 = 24564617) B24564617
theorem B2155135 : Blo 1344991 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B49103981 : Blo 1344991 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B36849005 : Blo 1344991 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B5752289 : Blo 1344991 5752289 := bstep (se 2 (by rfl) ⟨2157108, by rfl⟩ : syracuseStep 5752289 = 4314217) B4314217
theorem B3638857 : Blo 1344991 3638857 := bstep (se 2 (by rfl) ⟨1364571, by rfl⟩ : syracuseStep 3638857 = 2729143) B2729143
theorem B1345279 : Blo 1344991 1345279 := bstep (se 1 (by rfl) ⟨1008959, by rfl⟩ : syracuseStep 1345279 = 2017919) B2017919
theorem B1345307 : Blo 1344991 1345307 := bstep (se 1 (by rfl) ⟨1008980, by rfl⟩ : syracuseStep 1345307 = 2017961) B2017961
theorem B2426849 : Blo 1344991 2426849 := bstep (se 2 (by rfl) ⟨910068, by rfl⟩ : syracuseStep 2426849 = 1820137) B1820137
theorem B2017535 : Blo 1344991 2017535 := bstep (se 1 (by rfl) ⟨1513151, by rfl⟩ : syracuseStep 2017535 = 3026303) B3026303
theorem B1345947 : Blo 1344991 1345947 := bstep (se 1 (by rfl) ⟨1009460, by rfl⟩ : syracuseStep 1345947 = 2018921) B2018921
theorem B5753587 : Blo 1344991 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B1346367 : Blo 1344991 1346367 := bstep (se 1 (by rfl) ⟨1009775, by rfl⟩ : syracuseStep 1346367 = 2019551) B2019551
theorem B1346495 : Blo 1344991 1346495 := bstep (se 1 (by rfl) ⟨1009871, by rfl⟩ : syracuseStep 1346495 = 2019743) B2019743
theorem B2018303 : Blo 1344991 2018303 := bstep (se 1 (by rfl) ⟨1513727, by rfl⟩ : syracuseStep 2018303 = 3027455) B3027455
theorem B1346559 : Blo 1344991 1346559 := bstep (se 1 (by rfl) ⟨1009919, by rfl⟩ : syracuseStep 1346559 = 2019839) B2019839
theorem B1346591 : Blo 1344991 1346591 := bstep (se 1 (by rfl) ⟨1009943, by rfl⟩ : syracuseStep 1346591 = 2019887) B2019887
theorem B1346687 : Blo 1344991 1346687 := bstep (se 1 (by rfl) ⟨1010015, by rfl⟩ : syracuseStep 1346687 = 2020031) B2020031
theorem B10906811 : Blo 1344991 10906811 := bstep (se 1 (by rfl) ⟨8180108, by rfl⟩ : syracuseStep 10906811 = 16360217) B16360217
theorem B5745917 : Blo 1344991 5745917 := bstep (se 3 (by rfl) ⟨1077359, by rfl⟩ : syracuseStep 5745917 = 2154719) B2154719
theorem B6909887 : Blo 1344991 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B3027257 : Blo 1344991 3027257 := bstep (se 2 (by rfl) ⟨1135221, by rfl⟩ : syracuseStep 3027257 = 2270443) B2270443
theorem B2020379 : Blo 1344991 2020379 := bstep (se 1 (by rfl) ⟨1515284, by rfl⟩ : syracuseStep 2020379 = 3030569) B3030569
theorem B5109439 : Blo 1344991 5109439 := bstep (se 1 (by rfl) ⟨3832079, by rfl⟩ : syracuseStep 5109439 = 7664159) B7664159
theorem B19404521 : Blo 1344991 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B3069929 : Blo 1344991 3069929 := bstep (se 2 (by rfl) ⟨1151223, by rfl⟩ : syracuseStep 3069929 = 2302447) B2302447
theorem B4094239 : Blo 1344991 4094239 := bstep (se 1 (by rfl) ⟨3070679, by rfl⟩ : syracuseStep 4094239 = 6141359) B6141359
theorem B7772975 : Blo 1344991 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B4545341 : Blo 1344991 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B3030335 : Blo 1344991 3030335 := bstep (se 1 (by rfl) ⟨2272751, by rfl⟩ : syracuseStep 3030335 = 4545503) B4545503
theorem B1703359 : Blo 1344991 1703359 := bstep (se 1 (by rfl) ⟨1277519, by rfl⟩ : syracuseStep 1703359 = 2555039) B2555039
theorem B7667257 : Blo 1344991 7667257 := bstep (se 2 (by rfl) ⟨2875221, by rfl⟩ : syracuseStep 7667257 = 5750443) B5750443
theorem B11968091 : Blo 1344991 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B2875051 : Blo 1344991 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B60727121 : Blo 1344991 60727121 := bstep (se 2 (by rfl) ⟨22772670, by rfl⟩ : syracuseStep 60727121 = 45545341) B45545341
theorem B9699263 : Blo 1344991 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B32735987 : Blo 1344991 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B3834859 : Blo 1344991 3834859 := bstep (se 1 (by rfl) ⟨2876144, by rfl⟩ : syracuseStep 3834859 = 5752289) B5752289
theorem B12936347 : Blo 1344991 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B1345023 : Blo 1344991 1345023 := bstep (se 1 (by rfl) ⟨1008767, by rfl⟩ : syracuseStep 1345023 = 2017535) B2017535
theorem B2271145 : Blo 1344991 2271145 := bstep (se 2 (by rfl) ⟨851679, by rfl⟩ : syracuseStep 2271145 = 1703359) B1703359
theorem B1345535 : Blo 1344991 1345535 := bstep (se 1 (by rfl) ⟨1009151, by rfl⟩ : syracuseStep 1345535 = 2018303) B2018303
theorem B4851809 : Blo 1344991 4851809 := bstep (se 2 (by rfl) ⟨1819428, by rfl⟩ : syracuseStep 4851809 = 3638857) B3638857
theorem B18426365 : Blo 1344991 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B6466175 : Blo 1344991 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B5745455 : Blo 1344991 5745455 := bstep (se 1 (by rfl) ⟨4309091, by rfl⟩ : syracuseStep 5745455 = 8618183) B8618183
theorem B2018171 : Blo 1344991 2018171 := bstep (se 1 (by rfl) ⟨1513628, by rfl⟩ : syracuseStep 2018171 = 3027257) B3027257
theorem B5458985 : Blo 1344991 5458985 := bstep (se 2 (by rfl) ⟨2047119, by rfl⟩ : syracuseStep 5458985 = 4094239) B4094239
theorem B1346919 : Blo 1344991 1346919 := bstep (se 1 (by rfl) ⟨1010189, by rfl⟩ : syracuseStep 1346919 = 2020379) B2020379
theorem B7671449 : Blo 1344991 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B1617899 : Blo 1344991 1617899 := bstep (se 1 (by rfl) ⟨1213424, by rfl⟩ : syracuseStep 1617899 = 2426849) B2426849
theorem B5181983 : Blo 1344991 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B7271207 : Blo 1344991 7271207 := bstep (se 1 (by rfl) ⟨5453405, by rfl⟩ : syracuseStep 7271207 = 10906811) B10906811
theorem B3830611 : Blo 1344991 3830611 := bstep (se 1 (by rfl) ⟨2872958, by rfl⟩ : syracuseStep 3830611 = 5745917) B5745917
theorem B2020223 : Blo 1344991 2020223 := bstep (se 1 (by rfl) ⟨1515167, by rfl⟩ : syracuseStep 2020223 = 3030335) B3030335
theorem B6812585 : Blo 1344991 6812585 := bstep (se 2 (by rfl) ⟨2554719, by rfl⟩ : syracuseStep 6812585 = 5109439) B5109439
theorem B10917607 : Blo 1344991 10917607 := bstep (se 1 (by rfl) ⟨8188205, by rfl⟩ : syracuseStep 10917607 = 16376411) B16376411
theorem B252172217 : Blo 1344991 252172217 := bstep (se 2 (by rfl) ⟨94564581, by rfl⟩ : syracuseStep 252172217 = 189129163) B189129163
theorem B2873513 : Blo 1344991 2873513 := bstep (se 2 (by rfl) ⟨1077567, by rfl⟩ : syracuseStep 2873513 = 2155135) B2155135
theorem B24566003 : Blo 1344991 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B2046619 : Blo 1344991 2046619 := bstep (se 1 (by rfl) ⟨1534964, by rfl⟩ : syracuseStep 2046619 = 3069929) B3069929
theorem B3030227 : Blo 1344991 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B10223009 : Blo 1344991 10223009 := bstep (se 2 (by rfl) ⟨3833628, by rfl⟩ : syracuseStep 10223009 = 7667257) B7667257
theorem B3833401 : Blo 1344991 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B7978727 : Blo 1344991 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B40484747 : Blo 1344991 40484747 := bstep (se 1 (by rfl) ⟨30363560, by rfl⟩ : syracuseStep 40484747 = 60727121) B60727121
theorem B21823991 : Blo 1344991 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B2728825 : Blo 1344991 2728825 := bstep (se 2 (by rfl) ⟨1023309, by rfl⟩ : syracuseStep 2728825 = 2046619) B2046619
theorem B5113145 : Blo 1344991 5113145 := bstep (se 2 (by rfl) ⟨1917429, by rfl⟩ : syracuseStep 5113145 = 3834859) B3834859
theorem B16377335 : Blo 1344991 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B4310783 : Blo 1344991 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B1345447 : Blo 1344991 1345447 := bstep (se 1 (by rfl) ⟨1009085, by rfl⟩ : syracuseStep 1345447 = 2018171) B2018171
theorem B21276605 : Blo 1344991 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B3639323 : Blo 1344991 3639323 := bstep (se 1 (by rfl) ⟨2729492, by rfl⟩ : syracuseStep 3639323 = 5458985) B5458985
theorem B5114299 : Blo 1344991 5114299 := bstep (se 1 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 5114299 = 7671449) B7671449
theorem B7662701 : Blo 1344991 7662701 := bstep (se 3 (by rfl) ⟨1436756, by rfl⟩ : syracuseStep 7662701 = 2873513) B2873513
theorem B1346815 : Blo 1344991 1346815 := bstep (se 1 (by rfl) ⟨1010111, by rfl⟩ : syracuseStep 1346815 = 2020223) B2020223
theorem B4541723 : Blo 1344991 4541723 := bstep (se 1 (by rfl) ⟨3406292, by rfl⟩ : syracuseStep 4541723 = 6812585) B6812585
theorem B5107481 : Blo 1344991 5107481 := bstep (se 2 (by rfl) ⟨1915305, by rfl⟩ : syracuseStep 5107481 = 3830611) B3830611
theorem B12284243 : Blo 1344991 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B3830303 : Blo 1344991 3830303 := bstep (se 1 (by rfl) ⟨2872727, by rfl⟩ : syracuseStep 3830303 = 5745455) B5745455
theorem B2020151 : Blo 1344991 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B107959325 : Blo 1344991 107959325 := bstep (se 3 (by rfl) ⟨20242373, by rfl⟩ : syracuseStep 107959325 = 40484747) B40484747
theorem B3028193 : Blo 1344991 3028193 := bstep (se 2 (by rfl) ⟨1135572, by rfl⟩ : syracuseStep 3028193 = 2271145) B2271145
theorem B4314397 : Blo 1344991 4314397 := bstep (se 3 (by rfl) ⟨808949, by rfl⟩ : syracuseStep 4314397 = 1617899) B1617899
theorem B3454655 : Blo 1344991 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B4847471 : Blo 1344991 4847471 := bstep (se 1 (by rfl) ⟨3635603, by rfl⟩ : syracuseStep 4847471 = 7271207) B7271207
theorem B8624231 : Blo 1344991 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B168114811 : Blo 1344991 168114811 := bstep (se 1 (by rfl) ⟨126086108, by rfl⟩ : syracuseStep 168114811 = 252172217) B252172217
theorem B3234539 : Blo 1344991 3234539 := bstep (se 1 (by rfl) ⟨2425904, by rfl⟩ : syracuseStep 3234539 = 4851809) B4851809
theorem B5111201 : Blo 1344991 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B6815339 : Blo 1344991 6815339 := bstep (se 1 (by rfl) ⟨5111504, by rfl⟩ : syracuseStep 6815339 = 10223009) B10223009
theorem B14556809 : Blo 1344991 14556809 := bstep (se 2 (by rfl) ⟨5458803, by rfl⟩ : syracuseStep 14556809 = 10917607) B10917607
theorem B287891533 : Blo 1344991 287891533 := bstep (se 3 (by rfl) ⟨53979662, by rfl⟩ : syracuseStep 287891533 = 107959325) B107959325
theorem B14549327 : Blo 1344991 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B3408763 : Blo 1344991 3408763 := bstep (se 1 (by rfl) ⟨2556572, by rfl⟩ : syracuseStep 3408763 = 5113145) B5113145
theorem B2426215 : Blo 1344991 2426215 := bstep (se 1 (by rfl) ⟨1819661, by rfl⟩ : syracuseStep 2426215 = 3639323) B3639323
theorem B5752529 : Blo 1344991 5752529 := bstep (se 2 (by rfl) ⟨2157198, by rfl⟩ : syracuseStep 5752529 = 4314397) B4314397
theorem B36849653 : Blo 1344991 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B58214933 : Blo 1344991 58214933 := bstep (se 6 (by rfl) ⟨1364412, by rfl⟩ : syracuseStep 58214933 = 2728825) B2728825
theorem B1346767 : Blo 1344991 1346767 := bstep (se 1 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 1346767 = 2020151) B2020151
theorem B6819065 : Blo 1344991 6819065 := bstep (se 2 (by rfl) ⟨2557149, by rfl⟩ : syracuseStep 6819065 = 5114299) B5114299
theorem B2018795 : Blo 1344991 2018795 := bstep (se 1 (by rfl) ⟨1514096, by rfl⟩ : syracuseStep 2018795 = 3028193) B3028193
theorem B224153081 : Blo 1344991 224153081 := bstep (se 2 (by rfl) ⟨84057405, by rfl⟩ : syracuseStep 224153081 = 168114811) B168114811
theorem B3231647 : Blo 1344991 3231647 := bstep (se 1 (by rfl) ⟨2423735, by rfl⟩ : syracuseStep 3231647 = 4847471) B4847471
theorem B5108467 : Blo 1344991 5108467 := bstep (se 1 (by rfl) ⟨3831350, by rfl⟩ : syracuseStep 5108467 = 7662701) B7662701
theorem B3027815 : Blo 1344991 3027815 := bstep (se 1 (by rfl) ⟨2270861, by rfl⟩ : syracuseStep 3027815 = 4541723) B4541723
theorem B4543559 : Blo 1344991 4543559 := bstep (se 1 (by rfl) ⟨3407669, by rfl⟩ : syracuseStep 4543559 = 6815339) B6815339
theorem B9704539 : Blo 1344991 9704539 := bstep (se 1 (by rfl) ⟨7278404, by rfl⟩ : syracuseStep 9704539 = 14556809) B14556809
theorem B3404987 : Blo 1344991 3404987 := bstep (se 1 (by rfl) ⟨2553740, by rfl⟩ : syracuseStep 3404987 = 5107481) B5107481
theorem B8189495 : Blo 1344991 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B2553535 : Blo 1344991 2553535 := bstep (se 1 (by rfl) ⟨1915151, by rfl⟩ : syracuseStep 2553535 = 3830303) B3830303
theorem B10918223 : Blo 1344991 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B2873855 : Blo 1344991 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B5749487 : Blo 1344991 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B8625437 : Blo 1344991 8625437 := bstep (se 3 (by rfl) ⟨1617269, by rfl⟩ : syracuseStep 8625437 = 3234539) B3234539
theorem B3407467 : Blo 1344991 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B56737613 : Blo 1344991 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B9699551 : Blo 1344991 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B2269991 : Blo 1344991 2269991 := bstep (se 1 (by rfl) ⟨1702493, by rfl⟩ : syracuseStep 2269991 = 3404987) B3404987
theorem B3835019 : Blo 1344991 3835019 := bstep (se 1 (by rfl) ⟨2876264, by rfl⟩ : syracuseStep 3835019 = 5752529) B5752529
theorem B1345863 : Blo 1344991 1345863 := bstep (se 1 (by rfl) ⟨1009397, by rfl⟩ : syracuseStep 1345863 = 2018795) B2018795
theorem B37825075 : Blo 1344991 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B383855377 : Blo 1344991 383855377 := bstep (se 2 (by rfl) ⟨143945766, by rfl⟩ : syracuseStep 383855377 = 287891533) B287891533
theorem B2018543 : Blo 1344991 2018543 := bstep (se 1 (by rfl) ⟨1513907, by rfl⟩ : syracuseStep 2018543 = 3027815) B3027815
theorem B6811289 : Blo 1344991 6811289 := bstep (se 2 (by rfl) ⟨2554233, by rfl⟩ : syracuseStep 6811289 = 5108467) B5108467
theorem B5459663 : Blo 1344991 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B12939385 : Blo 1344991 12939385 := bstep (se 2 (by rfl) ⟨4852269, by rfl⟩ : syracuseStep 12939385 = 9704539) B9704539
theorem B7278815 : Blo 1344991 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B38809955 : Blo 1344991 38809955 := bstep (se 1 (by rfl) ⟨29107466, by rfl⟩ : syracuseStep 38809955 = 58214933) B58214933
theorem B4543289 : Blo 1344991 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B3404713 : Blo 1344991 3404713 := bstep (se 2 (by rfl) ⟨1276767, by rfl⟩ : syracuseStep 3404713 = 2553535) B2553535
theorem B149435387 : Blo 1344991 149435387 := bstep (se 1 (by rfl) ⟨112076540, by rfl⟩ : syracuseStep 149435387 = 224153081) B224153081
theorem B3029039 : Blo 1344991 3029039 := bstep (se 1 (by rfl) ⟨2271779, by rfl⟩ : syracuseStep 3029039 = 4543559) B4543559
theorem B4545017 : Blo 1344991 4545017 := bstep (se 2 (by rfl) ⟨1704381, by rfl⟩ : syracuseStep 4545017 = 3408763) B3408763
theorem B24566435 : Blo 1344991 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B1915903 : Blo 1344991 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B3234953 : Blo 1344991 3234953 := bstep (se 2 (by rfl) ⟨1213107, by rfl⟩ : syracuseStep 3234953 = 2426215) B2426215
theorem B3832991 : Blo 1344991 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B4546043 : Blo 1344991 4546043 := bstep (se 1 (by rfl) ⟨3409532, by rfl⟩ : syracuseStep 4546043 = 6819065) B6819065
theorem B5750291 : Blo 1344991 5750291 := bstep (se 1 (by rfl) ⟨4312718, by rfl⟩ : syracuseStep 5750291 = 8625437) B8625437
theorem B2154431 : Blo 1344991 2154431 := bstep (se 1 (by rfl) ⟨1615823, by rfl⟩ : syracuseStep 2154431 = 3231647) B3231647
theorem B17252513 : Blo 1344991 17252513 := bstep (se 2 (by rfl) ⟨6469692, by rfl⟩ : syracuseStep 17252513 = 12939385) B12939385
theorem B99623591 : Blo 1344991 99623591 := bstep (se 1 (by rfl) ⟨74717693, by rfl⟩ : syracuseStep 99623591 = 149435387) B149435387
theorem B2556679 : Blo 1344991 2556679 := bstep (se 1 (by rfl) ⟨1917509, by rfl⟩ : syracuseStep 2556679 = 3835019) B3835019
theorem B4539617 : Blo 1344991 4539617 := bstep (se 2 (by rfl) ⟨1702356, by rfl⟩ : syracuseStep 4539617 = 3404713) B3404713
theorem B16377623 : Blo 1344991 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B14559101 : Blo 1344991 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B2156635 : Blo 1344991 2156635 := bstep (se 1 (by rfl) ⟨1617476, by rfl⟩ : syracuseStep 2156635 = 3234953) B3234953
theorem B1345695 : Blo 1344991 1345695 := bstep (se 1 (by rfl) ⟨1009271, by rfl⟩ : syracuseStep 1345695 = 2018543) B2018543
theorem B4540859 : Blo 1344991 4540859 := bstep (se 1 (by rfl) ⟨3405644, by rfl⟩ : syracuseStep 4540859 = 6811289) B6811289
theorem B1436287 : Blo 1344991 1436287 := bstep (se 1 (by rfl) ⟨1077215, by rfl⟩ : syracuseStep 1436287 = 2154431) B2154431
theorem B10218149 : Blo 1344991 10218149 := bstep (se 4 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 10218149 = 1915903) B1915903
theorem B6466367 : Blo 1344991 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B4852543 : Blo 1344991 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B25873303 : Blo 1344991 25873303 := bstep (se 1 (by rfl) ⟨19404977, by rfl⟩ : syracuseStep 25873303 = 38809955) B38809955
theorem B511807169 : Blo 1344991 511807169 := bstep (se 2 (by rfl) ⟨191927688, by rfl⟩ : syracuseStep 511807169 = 383855377) B383855377
theorem B2019359 : Blo 1344991 2019359 := bstep (se 1 (by rfl) ⟨1514519, by rfl⟩ : syracuseStep 2019359 = 3029039) B3029039
theorem B201733733 : Blo 1344991 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B1513327 : Blo 1344991 1513327 := bstep (se 1 (by rfl) ⟨1134995, by rfl⟩ : syracuseStep 1513327 = 2269991) B2269991
theorem B3028859 : Blo 1344991 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B3030011 : Blo 1344991 3030011 := bstep (se 1 (by rfl) ⟨2272508, by rfl⟩ : syracuseStep 3030011 = 4545017) B4545017
theorem B2555327 : Blo 1344991 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B3030695 : Blo 1344991 3030695 := bstep (se 1 (by rfl) ⟨2273021, by rfl⟩ : syracuseStep 3030695 = 4546043) B4546043
theorem B3833527 : Blo 1344991 3833527 := bstep (se 1 (by rfl) ⟨2875145, by rfl⟩ : syracuseStep 3833527 = 5750291) B5750291
theorem B11501675 : Blo 1344991 11501675 := bstep (se 1 (by rfl) ⟨8626256, by rfl⟩ : syracuseStep 11501675 = 17252513) B17252513
theorem B2875513 : Blo 1344991 2875513 := bstep (se 2 (by rfl) ⟨1078317, by rfl⟩ : syracuseStep 2875513 = 2156635) B2156635
theorem B3408905 : Blo 1344991 3408905 := bstep (se 2 (by rfl) ⟨1278339, by rfl⟩ : syracuseStep 3408905 = 2556679) B2556679
theorem B134489155 : Blo 1344991 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B34497737 : Blo 1344991 34497737 := bstep (se 2 (by rfl) ⟨12936651, by rfl⟩ : syracuseStep 34497737 = 25873303) B25873303
theorem B4310911 : Blo 1344991 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B2017769 : Blo 1344991 2017769 := bstep (se 2 (by rfl) ⟨756663, by rfl⟩ : syracuseStep 2017769 = 1513327) B1513327
theorem B1346239 : Blo 1344991 1346239 := bstep (se 1 (by rfl) ⟨1009679, by rfl⟩ : syracuseStep 1346239 = 2019359) B2019359
theorem B66415727 : Blo 1344991 66415727 := bstep (se 1 (by rfl) ⟨49811795, by rfl⟩ : syracuseStep 66415727 = 99623591) B99623591
theorem B3026411 : Blo 1344991 3026411 := bstep (se 1 (by rfl) ⟨2269808, by rfl⟩ : syracuseStep 3026411 = 4539617) B4539617
theorem B2019239 : Blo 1344991 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B3027239 : Blo 1344991 3027239 := bstep (se 1 (by rfl) ⟨2270429, by rfl⟩ : syracuseStep 3027239 = 4540859) B4540859
theorem B6812099 : Blo 1344991 6812099 := bstep (se 1 (by rfl) ⟨5109074, by rfl⟩ : syracuseStep 6812099 = 10218149) B10218149
theorem B2020007 : Blo 1344991 2020007 := bstep (se 1 (by rfl) ⟨1515005, by rfl⟩ : syracuseStep 2020007 = 3030011) B3030011
theorem B2020463 : Blo 1344991 2020463 := bstep (se 1 (by rfl) ⟨1515347, by rfl⟩ : syracuseStep 2020463 = 3030695) B3030695
theorem B1915049 : Blo 1344991 1915049 := bstep (se 2 (by rfl) ⟨718143, by rfl⟩ : syracuseStep 1915049 = 1436287) B1436287
theorem B6470057 : Blo 1344991 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B6814205 : Blo 1344991 6814205 := bstep (se 3 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 6814205 = 2555327) B2555327
theorem B10918415 : Blo 1344991 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B9706067 : Blo 1344991 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B5111369 : Blo 1344991 5111369 := bstep (se 2 (by rfl) ⟨1916763, by rfl⟩ : syracuseStep 5111369 = 3833527) B3833527
theorem B341204779 : Blo 1344991 341204779 := bstep (se 1 (by rfl) ⟨255903584, by rfl⟩ : syracuseStep 341204779 = 511807169) B511807169
theorem B7667783 : Blo 1344991 7667783 := bstep (se 1 (by rfl) ⟨5750837, by rfl⟩ : syracuseStep 7667783 = 11501675) B11501675
theorem B3834017 : Blo 1344991 3834017 := bstep (se 2 (by rfl) ⟨1437756, by rfl⟩ : syracuseStep 3834017 = 2875513) B2875513
theorem B17253485 : Blo 1344991 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B29115773 : Blo 1344991 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B1345179 : Blo 1344991 1345179 := bstep (se 1 (by rfl) ⟨1008884, by rfl⟩ : syracuseStep 1345179 = 2017769) B2017769
theorem B2017607 : Blo 1344991 2017607 := bstep (se 1 (by rfl) ⟨1513205, by rfl⟩ : syracuseStep 2017607 = 3026411) B3026411
theorem B1346159 : Blo 1344991 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B2018159 : Blo 1344991 2018159 := bstep (se 1 (by rfl) ⟨1513619, by rfl⟩ : syracuseStep 2018159 = 3027239) B3027239
theorem B4541399 : Blo 1344991 4541399 := bstep (se 1 (by rfl) ⟨3406049, by rfl⟩ : syracuseStep 4541399 = 6812099) B6812099
theorem B5106797 : Blo 1344991 5106797 := bstep (se 3 (by rfl) ⟨957524, by rfl⟩ : syracuseStep 5106797 = 1915049) B1915049
theorem B1346671 : Blo 1344991 1346671 := bstep (se 1 (by rfl) ⟨1010003, by rfl⟩ : syracuseStep 1346671 = 2020007) B2020007
theorem B2272603 : Blo 1344991 2272603 := bstep (se 1 (by rfl) ⟨1704452, by rfl⟩ : syracuseStep 2272603 = 3408905) B3408905
theorem B1346975 : Blo 1344991 1346975 := bstep (se 1 (by rfl) ⟨1010231, by rfl⟩ : syracuseStep 1346975 = 2020463) B2020463
theorem B22998491 : Blo 1344991 22998491 := bstep (se 1 (by rfl) ⟨17248868, by rfl⟩ : syracuseStep 22998491 = 34497737) B34497737
theorem B179318873 : Blo 1344991 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B4542803 : Blo 1344991 4542803 := bstep (se 1 (by rfl) ⟨3407102, by rfl⟩ : syracuseStep 4542803 = 6814205) B6814205
theorem B454939705 : Blo 1344991 454939705 := bstep (se 2 (by rfl) ⟨170602389, by rfl⟩ : syracuseStep 454939705 = 341204779) B341204779
theorem B5747881 : Blo 1344991 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B6470711 : Blo 1344991 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B44277151 : Blo 1344991 44277151 := bstep (se 1 (by rfl) ⟨33207863, by rfl⟩ : syracuseStep 44277151 = 66415727) B66415727
theorem B3407579 : Blo 1344991 3407579 := bstep (se 1 (by rfl) ⟨2555684, by rfl⟩ : syracuseStep 3407579 = 5111369) B5111369
theorem B5111855 : Blo 1344991 5111855 := bstep (se 1 (by rfl) ⟨3833891, by rfl⟩ : syracuseStep 5111855 = 7667783) B7667783
theorem B119545915 : Blo 1344991 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B2556011 : Blo 1344991 2556011 := bstep (se 1 (by rfl) ⟨1917008, by rfl⟩ : syracuseStep 2556011 = 3834017) B3834017
theorem B11502323 : Blo 1344991 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B1345071 : Blo 1344991 1345071 := bstep (se 1 (by rfl) ⟨1008803, by rfl⟩ : syracuseStep 1345071 = 2017607) B2017607
theorem B1345439 : Blo 1344991 1345439 := bstep (se 1 (by rfl) ⟨1009079, by rfl⟩ : syracuseStep 1345439 = 2018159) B2018159
theorem B2271719 : Blo 1344991 2271719 := bstep (se 1 (by rfl) ⟨1703789, by rfl⟩ : syracuseStep 2271719 = 3407579) B3407579
theorem B19410515 : Blo 1344991 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B7663841 : Blo 1344991 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B59036201 : Blo 1344991 59036201 := bstep (se 2 (by rfl) ⟨22138575, by rfl⟩ : syracuseStep 59036201 = 44277151) B44277151
theorem B3027599 : Blo 1344991 3027599 := bstep (se 1 (by rfl) ⟨2270699, by rfl⟩ : syracuseStep 3027599 = 4541399) B4541399
theorem B4313807 : Blo 1344991 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B3404531 : Blo 1344991 3404531 := bstep (se 1 (by rfl) ⟨2553398, by rfl⟩ : syracuseStep 3404531 = 5106797) B5106797
theorem B15332327 : Blo 1344991 15332327 := bstep (se 1 (by rfl) ⟨11499245, by rfl⟩ : syracuseStep 15332327 = 22998491) B22998491
theorem B3028535 : Blo 1344991 3028535 := bstep (se 1 (by rfl) ⟨2271401, by rfl⟩ : syracuseStep 3028535 = 4542803) B4542803
theorem B2426345093 : Blo 1344991 2426345093 := bstep (se 4 (by rfl) ⟨227469852, by rfl⟩ : syracuseStep 2426345093 = 454939705) B454939705
theorem B3030137 : Blo 1344991 3030137 := bstep (se 2 (by rfl) ⟨1136301, by rfl⟩ : syracuseStep 3030137 = 2272603) B2272603
theorem B3407903 : Blo 1344991 3407903 := bstep (se 1 (by rfl) ⟨2555927, by rfl⟩ : syracuseStep 3407903 = 5111855) B5111855
theorem B1704007 : Blo 1344991 1704007 := bstep (se 1 (by rfl) ⟨1278005, by rfl⟩ : syracuseStep 1704007 = 2556011) B2556011
theorem B2875871 : Blo 1344991 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B2269687 : Blo 1344991 2269687 := bstep (se 1 (by rfl) ⟨1702265, by rfl⟩ : syracuseStep 2269687 = 3404531) B3404531
theorem B7668215 : Blo 1344991 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B159394553 : Blo 1344991 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B39357467 : Blo 1344991 39357467 := bstep (se 1 (by rfl) ⟨29518100, by rfl⟩ : syracuseStep 39357467 = 59036201) B59036201
theorem B2018399 : Blo 1344991 2018399 := bstep (se 1 (by rfl) ⟨1513799, by rfl⟩ : syracuseStep 2018399 = 3027599) B3027599
theorem B2019023 : Blo 1344991 2019023 := bstep (se 1 (by rfl) ⟨1514267, by rfl⟩ : syracuseStep 2019023 = 3028535) B3028535
theorem B1617563395 : Blo 1344991 1617563395 := bstep (se 1 (by rfl) ⟨1213172546, by rfl⟩ : syracuseStep 1617563395 = 2426345093) B2426345093
theorem B2020091 : Blo 1344991 2020091 := bstep (se 1 (by rfl) ⟨1515068, by rfl⟩ : syracuseStep 2020091 = 3030137) B3030137
theorem B12940343 : Blo 1344991 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B5109227 : Blo 1344991 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B10221551 : Blo 1344991 10221551 := bstep (se 1 (by rfl) ⟨7666163, by rfl⟩ : syracuseStep 10221551 = 15332327) B15332327
theorem B1514479 : Blo 1344991 1514479 := bstep (se 1 (by rfl) ⟨1135859, by rfl⟩ : syracuseStep 1514479 = 2271719) B2271719
theorem B5112143 : Blo 1344991 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B8626895 : Blo 1344991 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B7668989 : Blo 1344991 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B1345599 : Blo 1344991 1345599 := bstep (se 1 (by rfl) ⟨1009199, by rfl⟩ : syracuseStep 1345599 = 2018399) B2018399
theorem B2156751193 : Blo 1344991 2156751193 := bstep (se 2 (by rfl) ⟨808781697, by rfl⟩ : syracuseStep 2156751193 = 1617563395) B1617563395
theorem B1346015 : Blo 1344991 1346015 := bstep (se 1 (by rfl) ⟨1009511, by rfl⟩ : syracuseStep 1346015 = 2019023) B2019023
theorem B2271935 : Blo 1344991 2271935 := bstep (se 1 (by rfl) ⟨1703951, by rfl⟩ : syracuseStep 2271935 = 3407903) B3407903
theorem B2272009 : Blo 1344991 2272009 := bstep (se 2 (by rfl) ⟨852003, by rfl⟩ : syracuseStep 2272009 = 1704007) B1704007
theorem B1346727 : Blo 1344991 1346727 := bstep (se 1 (by rfl) ⟨1010045, by rfl⟩ : syracuseStep 1346727 = 2020091) B2020091
theorem B3026249 : Blo 1344991 3026249 := bstep (se 2 (by rfl) ⟨1134843, by rfl⟩ : syracuseStep 3026249 = 2269687) B2269687
theorem B2019305 : Blo 1344991 2019305 := bstep (se 2 (by rfl) ⟨757239, by rfl⟩ : syracuseStep 2019305 = 1514479) B1514479
theorem B106263035 : Blo 1344991 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B3406151 : Blo 1344991 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B6814367 : Blo 1344991 6814367 := bstep (se 1 (by rfl) ⟨5110775, by rfl⟩ : syracuseStep 6814367 = 10221551) B10221551
theorem B26238311 : Blo 1344991 26238311 := bstep (se 1 (by rfl) ⟨19678733, by rfl⟩ : syracuseStep 26238311 = 39357467) B39357467
theorem B3408095 : Blo 1344991 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B5751263 : Blo 1344991 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B5112659 : Blo 1344991 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B2270767 : Blo 1344991 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B2017499 : Blo 1344991 2017499 := bstep (se 1 (by rfl) ⟨1513124, by rfl⟩ : syracuseStep 2017499 = 3026249) B3026249
theorem B17492207 : Blo 1344991 17492207 := bstep (se 1 (by rfl) ⟨13119155, by rfl⟩ : syracuseStep 17492207 = 26238311) B26238311
theorem B1346203 : Blo 1344991 1346203 := bstep (se 1 (by rfl) ⟨1009652, by rfl⟩ : syracuseStep 1346203 = 2019305) B2019305
theorem B4542911 : Blo 1344991 4542911 := bstep (se 1 (by rfl) ⟨3407183, by rfl⟩ : syracuseStep 4542911 = 6814367) B6814367
theorem B70842023 : Blo 1344991 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B2875668257 : Blo 1344991 2875668257 := bstep (se 2 (by rfl) ⟨1078375596, by rfl⟩ : syracuseStep 2875668257 = 2156751193) B2156751193
theorem B3029345 : Blo 1344991 3029345 := bstep (se 2 (by rfl) ⟨1136004, by rfl⟩ : syracuseStep 3029345 = 2272009) B2272009
theorem B1514623 : Blo 1344991 1514623 := bstep (se 1 (by rfl) ⟨1135967, by rfl⟩ : syracuseStep 1514623 = 2271935) B2271935
theorem B3408439 : Blo 1344991 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B46645885 : Blo 1344991 46645885 := bstep (se 3 (by rfl) ⟨8746103, by rfl⟩ : syracuseStep 46645885 = 17492207) B17492207
theorem B47228015 : Blo 1344991 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B15336701 : Blo 1344991 15336701 := bstep (se 3 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 15336701 = 5751263) B5751263
theorem B1344999 : Blo 1344991 1344999 := bstep (se 1 (by rfl) ⟨1008749, by rfl⟩ : syracuseStep 1344999 = 2017499) B2017499
theorem B2272063 : Blo 1344991 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B1917112171 : Blo 1344991 1917112171 := bstep (se 1 (by rfl) ⟨1437834128, by rfl⟩ : syracuseStep 1917112171 = 2875668257) B2875668257
theorem B2019497 : Blo 1344991 2019497 := bstep (se 2 (by rfl) ⟨757311, by rfl⟩ : syracuseStep 2019497 = 1514623) B1514623
theorem B2019563 : Blo 1344991 2019563 := bstep (se 1 (by rfl) ⟨1514672, by rfl⟩ : syracuseStep 2019563 = 3029345) B3029345
theorem B3027689 : Blo 1344991 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B3028607 : Blo 1344991 3028607 := bstep (se 1 (by rfl) ⟨2271455, by rfl⟩ : syracuseStep 3028607 = 4542911) B4542911
theorem B10224467 : Blo 1344991 10224467 := bstep (se 1 (by rfl) ⟨7668350, by rfl⟩ : syracuseStep 10224467 = 15336701) B15336701
theorem B1346331 : Blo 1344991 1346331 := bstep (se 1 (by rfl) ⟨1009748, by rfl⟩ : syracuseStep 1346331 = 2019497) B2019497
theorem B1346375 : Blo 1344991 1346375 := bstep (se 1 (by rfl) ⟨1009781, by rfl⟩ : syracuseStep 1346375 = 2019563) B2019563
theorem B2018459 : Blo 1344991 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B248778053 : Blo 1344991 248778053 := bstep (se 4 (by rfl) ⟨23322942, by rfl⟩ : syracuseStep 248778053 = 46645885) B46645885
theorem B31485343 : Blo 1344991 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B2019071 : Blo 1344991 2019071 := bstep (se 1 (by rfl) ⟨1514303, by rfl⟩ : syracuseStep 2019071 = 3028607) B3028607
theorem B4544585 : Blo 1344991 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B3029417 : Blo 1344991 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B2556149561 : Blo 1344991 2556149561 := bstep (se 2 (by rfl) ⟨958556085, by rfl⟩ : syracuseStep 2556149561 = 1917112171) B1917112171
theorem B6816311 : Blo 1344991 6816311 := bstep (se 1 (by rfl) ⟨5112233, by rfl⟩ : syracuseStep 6816311 = 10224467) B10224467
theorem B1345639 : Blo 1344991 1345639 := bstep (se 1 (by rfl) ⟨1009229, by rfl⟩ : syracuseStep 1345639 = 2018459) B2018459
theorem B1346047 : Blo 1344991 1346047 := bstep (se 1 (by rfl) ⟨1009535, by rfl⟩ : syracuseStep 1346047 = 2019071) B2019071
theorem B2019611 : Blo 1344991 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B41980457 : Blo 1344991 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B165852035 : Blo 1344991 165852035 := bstep (se 1 (by rfl) ⟨124389026, by rfl⟩ : syracuseStep 165852035 = 248778053) B248778053
theorem B3029723 : Blo 1344991 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B1704099707 : Blo 1344991 1704099707 := bstep (se 1 (by rfl) ⟨1278074780, by rfl⟩ : syracuseStep 1704099707 = 2556149561) B2556149561
theorem B110568023 : Blo 1344991 110568023 := bstep (se 1 (by rfl) ⟨82926017, by rfl⟩ : syracuseStep 110568023 = 165852035) B165852035
theorem B1346407 : Blo 1344991 1346407 := bstep (se 1 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 1346407 = 2019611) B2019611
theorem B27986971 : Blo 1344991 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B2019815 : Blo 1344991 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B4544207 : Blo 1344991 4544207 := bstep (se 1 (by rfl) ⟨3408155, by rfl⟩ : syracuseStep 4544207 = 6816311) B6816311
theorem B1136066471 : Blo 1344991 1136066471 := bstep (se 1 (by rfl) ⟨852049853, by rfl⟩ : syracuseStep 1136066471 = 1704099707) B1704099707
theorem B73712015 : Blo 1344991 73712015 := bstep (se 1 (by rfl) ⟨55284011, by rfl⟩ : syracuseStep 73712015 = 110568023) B110568023
theorem B37315961 : Blo 1344991 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B757377647 : Blo 1344991 757377647 := bstep (se 1 (by rfl) ⟨568033235, by rfl⟩ : syracuseStep 757377647 = 1136066471) B1136066471
theorem B1346543 : Blo 1344991 1346543 := bstep (se 1 (by rfl) ⟨1009907, by rfl⟩ : syracuseStep 1346543 = 2019815) B2019815
theorem B3029471 : Blo 1344991 3029471 := bstep (se 1 (by rfl) ⟨2272103, by rfl⟩ : syracuseStep 3029471 = 4544207) B4544207
theorem B2019647 : Blo 1344991 2019647 := bstep (se 1 (by rfl) ⟨1514735, by rfl⟩ : syracuseStep 2019647 = 3029471) B3029471
theorem B504918431 : Blo 1344991 504918431 := bstep (se 1 (by rfl) ⟨378688823, by rfl⟩ : syracuseStep 504918431 = 757377647) B757377647
theorem B49141343 : Blo 1344991 49141343 := bstep (se 1 (by rfl) ⟨36856007, by rfl⟩ : syracuseStep 49141343 = 73712015) B73712015
theorem B24877307 : Blo 1344991 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B32760895 : Blo 1344991 32760895 := bstep (se 1 (by rfl) ⟨24570671, by rfl⟩ : syracuseStep 32760895 = 49141343) B49141343
theorem B1346431 : Blo 1344991 1346431 := bstep (se 1 (by rfl) ⟨1009823, by rfl⟩ : syracuseStep 1346431 = 2019647) B2019647
theorem B336612287 : Blo 1344991 336612287 := bstep (se 1 (by rfl) ⟨252459215, by rfl⟩ : syracuseStep 336612287 = 504918431) B504918431
theorem B16584871 : Blo 1344991 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B43681193 : Blo 1344991 43681193 := bstep (se 2 (by rfl) ⟨16380447, by rfl⟩ : syracuseStep 43681193 = 32760895) B32760895
theorem B22113161 : Blo 1344991 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B224408191 : Blo 1344991 224408191 := bstep (se 1 (by rfl) ⟨168306143, by rfl⟩ : syracuseStep 224408191 = 336612287) B336612287
theorem B14742107 : Blo 1344991 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B299210921 : Blo 1344991 299210921 := bstep (se 2 (by rfl) ⟨112204095, by rfl⟩ : syracuseStep 299210921 = 224408191) B224408191
theorem B29120795 : Blo 1344991 29120795 := bstep (se 1 (by rfl) ⟨21840596, by rfl⟩ : syracuseStep 29120795 = 43681193) B43681193
theorem B9828071 : Blo 1344991 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B199473947 : Blo 1344991 199473947 := bstep (se 1 (by rfl) ⟨149605460, by rfl⟩ : syracuseStep 199473947 = 299210921) B299210921
theorem B19413863 : Blo 1344991 19413863 := bstep (se 1 (by rfl) ⟨14560397, by rfl⟩ : syracuseStep 19413863 = 29120795) B29120795
theorem B132982631 : Blo 1344991 132982631 := bstep (se 1 (by rfl) ⟨99736973, by rfl⟩ : syracuseStep 132982631 = 199473947) B199473947
theorem B6552047 : Blo 1344991 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B12942575 : Blo 1344991 12942575 := bstep (se 1 (by rfl) ⟨9706931, by rfl⟩ : syracuseStep 12942575 = 19413863) B19413863
theorem B88655087 : Blo 1344991 88655087 := bstep (se 1 (by rfl) ⟨66491315, by rfl⟩ : syracuseStep 88655087 = 132982631) B132982631
theorem B8628383 : Blo 1344991 8628383 := bstep (se 1 (by rfl) ⟨6471287, by rfl⟩ : syracuseStep 8628383 = 12942575) B12942575
theorem B17472125 : Blo 1344991 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B5752255 : Blo 1344991 5752255 := bstep (se 1 (by rfl) ⟨4314191, by rfl⟩ : syracuseStep 5752255 = 8628383) B8628383
theorem B59103391 : Blo 1344991 59103391 := bstep (se 1 (by rfl) ⟨44327543, by rfl⟩ : syracuseStep 59103391 = 88655087) B88655087
theorem B11648083 : Blo 1344991 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B7669673 : Blo 1344991 7669673 := bstep (se 2 (by rfl) ⟨2876127, by rfl⟩ : syracuseStep 7669673 = 5752255) B5752255
theorem B78804521 : Blo 1344991 78804521 := bstep (se 2 (by rfl) ⟨29551695, by rfl⟩ : syracuseStep 78804521 = 59103391) B59103391
theorem B15530777 : Blo 1344991 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B52536347 : Blo 1344991 52536347 := bstep (se 1 (by rfl) ⟨39402260, by rfl⟩ : syracuseStep 52536347 = 78804521) B78804521
theorem B5113115 : Blo 1344991 5113115 := bstep (se 1 (by rfl) ⟨3834836, by rfl⟩ : syracuseStep 5113115 = 7669673) B7669673
theorem B10353851 : Blo 1344991 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B3408743 : Blo 1344991 3408743 := bstep (se 1 (by rfl) ⟨2556557, by rfl⟩ : syracuseStep 3408743 = 5113115) B5113115
theorem B35024231 : Blo 1344991 35024231 := bstep (se 1 (by rfl) ⟨26268173, by rfl⟩ : syracuseStep 35024231 = 52536347) B52536347
theorem B6902567 : Blo 1344991 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B23349487 : Blo 1344991 23349487 := bstep (se 1 (by rfl) ⟨17512115, by rfl⟩ : syracuseStep 23349487 = 35024231) B35024231
theorem B2272495 : Blo 1344991 2272495 := bstep (se 1 (by rfl) ⟨1704371, by rfl⟩ : syracuseStep 2272495 = 3408743) B3408743
theorem B4601711 : Blo 1344991 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B31132649 : Blo 1344991 31132649 := bstep (se 2 (by rfl) ⟨11674743, by rfl⟩ : syracuseStep 31132649 = 23349487) B23349487
theorem B3067807 : Blo 1344991 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B3029993 : Blo 1344991 3029993 := bstep (se 2 (by rfl) ⟨1136247, by rfl⟩ : syracuseStep 3029993 = 2272495) B2272495
theorem B4090409 : Blo 1344991 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B20755099 : Blo 1344991 20755099 := bstep (se 1 (by rfl) ⟨15566324, by rfl⟩ : syracuseStep 20755099 = 31132649) B31132649
theorem B2019995 : Blo 1344991 2019995 := bstep (se 1 (by rfl) ⟨1514996, by rfl⟩ : syracuseStep 2019995 = 3029993) B3029993
theorem B1346663 : Blo 1344991 1346663 := bstep (se 1 (by rfl) ⟨1009997, by rfl⟩ : syracuseStep 1346663 = 2019995) B2019995
theorem B110693861 : Blo 1344991 110693861 := bstep (se 4 (by rfl) ⟨10377549, by rfl⟩ : syracuseStep 110693861 = 20755099) B20755099
theorem B2726939 : Blo 1344991 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B73795907 : Blo 1344991 73795907 := bstep (se 1 (by rfl) ⟨55346930, by rfl⟩ : syracuseStep 73795907 = 110693861) B110693861
theorem B1817959 : Blo 1344991 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B196789085 : Blo 1344991 196789085 := bstep (se 3 (by rfl) ⟨36897953, by rfl⟩ : syracuseStep 196789085 = 73795907) B73795907
theorem B2423945 : Blo 1344991 2423945 := bstep (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) B1817959
theorem B1615963 : Blo 1344991 1615963 := bstep (se 1 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 1615963 = 2423945) B2423945
theorem B131192723 : Blo 1344991 131192723 := bstep (se 1 (by rfl) ⟨98394542, by rfl⟩ : syracuseStep 131192723 = 196789085) B196789085
theorem B2154617 : Blo 1344991 2154617 := bstep (se 2 (by rfl) ⟨807981, by rfl⟩ : syracuseStep 2154617 = 1615963) B1615963
theorem B349847261 : Blo 1344991 349847261 := bstep (se 3 (by rfl) ⟨65596361, by rfl⟩ : syracuseStep 349847261 = 131192723) B131192723
theorem B1436411 : Blo 1344991 1436411 := bstep (se 1 (by rfl) ⟨1077308, by rfl⟩ : syracuseStep 1436411 = 2154617) B2154617
theorem B233231507 : Blo 1344991 233231507 := bstep (se 1 (by rfl) ⟨174923630, by rfl⟩ : syracuseStep 233231507 = 349847261) B349847261
theorem B155487671 : Blo 1344991 155487671 := bstep (se 1 (by rfl) ⟨116615753, by rfl⟩ : syracuseStep 155487671 = 233231507) B233231507
theorem B3830429 : Blo 1344991 3830429 := bstep (se 3 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 3830429 = 1436411) B1436411
theorem B103658447 : Blo 1344991 103658447 := bstep (se 1 (by rfl) ⟨77743835, by rfl⟩ : syracuseStep 103658447 = 155487671) B155487671
theorem B2553619 : Blo 1344991 2553619 := bstep (se 1 (by rfl) ⟨1915214, by rfl⟩ : syracuseStep 2553619 = 3830429) B3830429
theorem B3404825 : Blo 1344991 3404825 := bstep (se 2 (by rfl) ⟨1276809, by rfl⟩ : syracuseStep 3404825 = 2553619) B2553619
theorem B69105631 : Blo 1344991 69105631 := bstep (se 1 (by rfl) ⟨51829223, by rfl⟩ : syracuseStep 69105631 = 103658447) B103658447
theorem B2269883 : Blo 1344991 2269883 := bstep (se 1 (by rfl) ⟨1702412, by rfl⟩ : syracuseStep 2269883 = 3404825) B3404825
theorem B92140841 : Blo 1344991 92140841 := bstep (se 2 (by rfl) ⟨34552815, by rfl⟩ : syracuseStep 92140841 = 69105631) B69105631
theorem B1513255 : Blo 1344991 1513255 := bstep (se 1 (by rfl) ⟨1134941, by rfl⟩ : syracuseStep 1513255 = 2269883) B2269883
theorem B245708909 : Blo 1344991 245708909 := bstep (se 3 (by rfl) ⟨46070420, by rfl⟩ : syracuseStep 245708909 = 92140841) B92140841
theorem B2017673 : Blo 1344991 2017673 := bstep (se 2 (by rfl) ⟨756627, by rfl⟩ : syracuseStep 2017673 = 1513255) B1513255
theorem B163805939 : Blo 1344991 163805939 := bstep (se 1 (by rfl) ⟨122854454, by rfl⟩ : syracuseStep 163805939 = 245708909) B245708909
theorem B1345115 : Blo 1344991 1345115 := bstep (se 1 (by rfl) ⟨1008836, by rfl⟩ : syracuseStep 1345115 = 2017673) B2017673
theorem B109203959 : Blo 1344991 109203959 := bstep (se 1 (by rfl) ⟨81902969, by rfl⟩ : syracuseStep 109203959 = 163805939) B163805939
theorem B72802639 : Blo 1344991 72802639 := bstep (se 1 (by rfl) ⟨54601979, by rfl⟩ : syracuseStep 72802639 = 109203959) B109203959
theorem B97070185 : Blo 1344991 97070185 := bstep (se 2 (by rfl) ⟨36401319, by rfl⟩ : syracuseStep 97070185 = 72802639) B72802639
theorem B129426913 : Blo 1344991 129426913 := bstep (se 2 (by rfl) ⟨48535092, by rfl⟩ : syracuseStep 129426913 = 97070185) B97070185
theorem B172569217 : Blo 1344991 172569217 := bstep (se 2 (by rfl) ⟨64713456, by rfl⟩ : syracuseStep 172569217 = 129426913) B129426913
theorem B230092289 : Blo 1344991 230092289 := bstep (se 2 (by rfl) ⟨86284608, by rfl⟩ : syracuseStep 230092289 = 172569217) B172569217
theorem B153394859 : Blo 1344991 153394859 := bstep (se 1 (by rfl) ⟨115046144, by rfl⟩ : syracuseStep 153394859 = 230092289) B230092289
theorem B102263239 : Blo 1344991 102263239 := bstep (se 1 (by rfl) ⟨76697429, by rfl⟩ : syracuseStep 102263239 = 153394859) B153394859
theorem B136350985 : Blo 1344991 136350985 := bstep (se 2 (by rfl) ⟨51131619, by rfl⟩ : syracuseStep 136350985 = 102263239) B102263239
theorem B181801313 : Blo 1344991 181801313 := bstep (se 2 (by rfl) ⟨68175492, by rfl⟩ : syracuseStep 181801313 = 136350985) B136350985
theorem B121200875 : Blo 1344991 121200875 := bstep (se 1 (by rfl) ⟨90900656, by rfl⟩ : syracuseStep 121200875 = 181801313) B181801313
theorem B80800583 : Blo 1344991 80800583 := bstep (se 1 (by rfl) ⟨60600437, by rfl⟩ : syracuseStep 80800583 = 121200875) B121200875
theorem B861872885 : Blo 1344991 861872885 := bstep (se 5 (by rfl) ⟨40400291, by rfl⟩ : syracuseStep 861872885 = 80800583) B80800583
theorem B574581923 : Blo 1344991 574581923 := bstep (se 1 (by rfl) ⟨430936442, by rfl⟩ : syracuseStep 574581923 = 861872885) B861872885
theorem B383054615 : Blo 1344991 383054615 := bstep (se 1 (by rfl) ⟨287290961, by rfl⟩ : syracuseStep 383054615 = 574581923) B574581923
theorem B255369743 : Blo 1344991 255369743 := bstep (se 1 (by rfl) ⟨191527307, by rfl⟩ : syracuseStep 255369743 = 383054615) B383054615
theorem B170246495 : Blo 1344991 170246495 := bstep (se 1 (by rfl) ⟨127684871, by rfl⟩ : syracuseStep 170246495 = 255369743) B255369743
theorem B453990653 : Blo 1344991 453990653 := bstep (se 3 (by rfl) ⟨85123247, by rfl⟩ : syracuseStep 453990653 = 170246495) B170246495
theorem B302660435 : Blo 1344991 302660435 := bstep (se 1 (by rfl) ⟨226995326, by rfl⟩ : syracuseStep 302660435 = 453990653) B453990653
theorem B807094493 : Blo 1344991 807094493 := bstep (se 3 (by rfl) ⟨151330217, by rfl⟩ : syracuseStep 807094493 = 302660435) B302660435
theorem B538062995 : Blo 1344991 538062995 := bstep (se 1 (by rfl) ⟨403547246, by rfl⟩ : syracuseStep 538062995 = 807094493) B807094493
theorem B358708663 : Blo 1344991 358708663 := bstep (se 1 (by rfl) ⟨269031497, by rfl⟩ : syracuseStep 358708663 = 538062995) B538062995
theorem B478278217 : Blo 1344991 478278217 := bstep (se 2 (by rfl) ⟨179354331, by rfl⟩ : syracuseStep 478278217 = 358708663) B358708663
theorem B637704289 : Blo 1344991 637704289 := bstep (se 2 (by rfl) ⟨239139108, by rfl⟩ : syracuseStep 637704289 = 478278217) B478278217
theorem B850272385 : Blo 1344991 850272385 := bstep (se 2 (by rfl) ⟨318852144, by rfl⟩ : syracuseStep 850272385 = 637704289) B637704289
theorem B1133696513 : Blo 1344991 1133696513 := bstep (se 2 (by rfl) ⟨425136192, by rfl⟩ : syracuseStep 1133696513 = 850272385) B850272385
theorem B755797675 : Blo 1344991 755797675 := bstep (se 1 (by rfl) ⟨566848256, by rfl⟩ : syracuseStep 755797675 = 1133696513) B1133696513
theorem B1007730233 : Blo 1344991 1007730233 := bstep (se 2 (by rfl) ⟨377898837, by rfl⟩ : syracuseStep 1007730233 = 755797675) B755797675
theorem B671820155 : Blo 1344991 671820155 := bstep (se 1 (by rfl) ⟨503865116, by rfl⟩ : syracuseStep 671820155 = 1007730233) B1007730233
theorem B447880103 : Blo 1344991 447880103 := bstep (se 1 (by rfl) ⟨335910077, by rfl⟩ : syracuseStep 447880103 = 671820155) B671820155
theorem B298586735 : Blo 1344991 298586735 := bstep (se 1 (by rfl) ⟨223940051, by rfl⟩ : syracuseStep 298586735 = 447880103) B447880103
theorem B199057823 : Blo 1344991 199057823 := bstep (se 1 (by rfl) ⟨149293367, by rfl⟩ : syracuseStep 199057823 = 298586735) B298586735
theorem B132705215 : Blo 1344991 132705215 := bstep (se 1 (by rfl) ⟨99528911, by rfl⟩ : syracuseStep 132705215 = 199057823) B199057823
theorem B88470143 : Blo 1344991 88470143 := bstep (se 1 (by rfl) ⟨66352607, by rfl⟩ : syracuseStep 88470143 = 132705215) B132705215
theorem B58980095 : Blo 1344991 58980095 := bstep (se 1 (by rfl) ⟨44235071, by rfl⟩ : syracuseStep 58980095 = 88470143) B88470143
theorem B39320063 : Blo 1344991 39320063 := bstep (se 1 (by rfl) ⟨29490047, by rfl⟩ : syracuseStep 39320063 = 58980095) B58980095
theorem B26213375 : Blo 1344991 26213375 := bstep (se 1 (by rfl) ⟨19660031, by rfl⟩ : syracuseStep 26213375 = 39320063) B39320063
theorem B17475583 : Blo 1344991 17475583 := bstep (se 1 (by rfl) ⟨13106687, by rfl⟩ : syracuseStep 17475583 = 26213375) B26213375
theorem B23300777 : Blo 1344991 23300777 := bstep (se 2 (by rfl) ⟨8737791, by rfl⟩ : syracuseStep 23300777 = 17475583) B17475583
theorem B15533851 : Blo 1344991 15533851 := bstep (se 1 (by rfl) ⟨11650388, by rfl⟩ : syracuseStep 15533851 = 23300777) B23300777
theorem B20711801 : Blo 1344991 20711801 := bstep (se 2 (by rfl) ⟨7766925, by rfl⟩ : syracuseStep 20711801 = 15533851) B15533851
theorem B13807867 : Blo 1344991 13807867 := bstep (se 1 (by rfl) ⟨10355900, by rfl⟩ : syracuseStep 13807867 = 20711801) B20711801
theorem B18410489 : Blo 1344991 18410489 := bstep (se 2 (by rfl) ⟨6903933, by rfl⟩ : syracuseStep 18410489 = 13807867) B13807867
theorem B12273659 : Blo 1344991 12273659 := bstep (se 1 (by rfl) ⟨9205244, by rfl⟩ : syracuseStep 12273659 = 18410489) B18410489
theorem B8182439 : Blo 1344991 8182439 := bstep (se 1 (by rfl) ⟨6136829, by rfl⟩ : syracuseStep 8182439 = 12273659) B12273659
theorem B5454959 : Blo 1344991 5454959 := bstep (se 1 (by rfl) ⟨4091219, by rfl⟩ : syracuseStep 5454959 = 8182439) B8182439
theorem B14546557 : Blo 1344991 14546557 := bstep (se 3 (by rfl) ⟨2727479, by rfl⟩ : syracuseStep 14546557 = 5454959) B5454959
theorem B19395409 : Blo 1344991 19395409 := bstep (se 2 (by rfl) ⟨7273278, by rfl⟩ : syracuseStep 19395409 = 14546557) B14546557
theorem B25860545 : Blo 1344991 25860545 := bstep (se 2 (by rfl) ⟨9697704, by rfl⟩ : syracuseStep 25860545 = 19395409) B19395409
theorem B17240363 : Blo 1344991 17240363 := bstep (se 1 (by rfl) ⟨12930272, by rfl⟩ : syracuseStep 17240363 = 25860545) B25860545
theorem B11493575 : Blo 1344991 11493575 := bstep (se 1 (by rfl) ⟨8620181, by rfl⟩ : syracuseStep 11493575 = 17240363) B17240363
theorem B7662383 : Blo 1344991 7662383 := bstep (se 1 (by rfl) ⟨5746787, by rfl⟩ : syracuseStep 7662383 = 11493575) B11493575
theorem B5108255 : Blo 1344991 5108255 := bstep (se 1 (by rfl) ⟨3831191, by rfl⟩ : syracuseStep 5108255 = 7662383) B7662383
theorem B3405503 : Blo 1344991 3405503 := bstep (se 1 (by rfl) ⟨2554127, by rfl⟩ : syracuseStep 3405503 = 5108255) B5108255
theorem B2270335 : Blo 1344991 2270335 := bstep (se 1 (by rfl) ⟨1702751, by rfl⟩ : syracuseStep 2270335 = 3405503) B3405503
theorem B3027113 : Blo 1344991 3027113 := bstep (se 2 (by rfl) ⟨1135167, by rfl⟩ : syracuseStep 3027113 = 2270335) B2270335
theorem B2018075 : Blo 1344991 2018075 := bstep (se 1 (by rfl) ⟨1513556, by rfl⟩ : syracuseStep 2018075 = 3027113) B3027113
theorem B1345383 : Blo 1344991 1345383 := bstep (se 1 (by rfl) ⟨1009037, by rfl⟩ : syracuseStep 1345383 = 2018075) B2018075

theorem C0 (j : ℕ) (h1 : 336247 ≤ j) (h2 : j ≤ 336747) : Blo 1344991 (4 * j + 3) := by
  interval_cases j
  · exact B1344991
  · exact B1344995
  · exact B1344999
  · exact B1345003
  · exact B1345007
  · exact B1345011
  · exact B1345015
  · exact B1345019
  · exact B1345023
  · exact B1345027
  · exact B1345031
  · exact B1345035
  · exact B1345039
  · exact B1345043
  · exact B1345047
  · exact B1345051
  · exact B1345055
  · exact B1345059
  · exact B1345063
  · exact B1345067
  · exact B1345071
  · exact B1345075
  · exact B1345079
  · exact B1345083
  · exact B1345087
  · exact B1345091
  · exact B1345095
  · exact B1345099
  · exact B1345103
  · exact B1345107
  · exact B1345111
  · exact B1345115
  · exact B1345119
  · exact B1345123
  · exact B1345127
  · exact B1345131
  · exact B1345135
  · exact B1345139
  · exact B1345143
  · exact B1345147
  · exact B1345151
  · exact B1345155
  · exact B1345159
  · exact B1345163
  · exact B1345167
  · exact B1345171
  · exact B1345175
  · exact B1345179
  · exact B1345183
  · exact B1345187
  · exact B1345191
  · exact B1345195
  · exact B1345199
  · exact B1345203
  · exact B1345207
  · exact B1345211
  · exact B1345215
  · exact B1345219
  · exact B1345223
  · exact B1345227
  · exact B1345231
  · exact B1345235
  · exact B1345239
  · exact B1345243
  · exact B1345247
  · exact B1345251
  · exact B1345255
  · exact B1345259
  · exact B1345263
  · exact B1345267
  · exact B1345271
  · exact B1345275
  · exact B1345279
  · exact B1345283
  · exact B1345287
  · exact B1345291
  · exact B1345295
  · exact B1345299
  · exact B1345303
  · exact B1345307
  · exact B1345311
  · exact B1345315
  · exact B1345319
  · exact B1345323
  · exact B1345327
  · exact B1345331
  · exact B1345335
  · exact B1345339
  · exact B1345343
  · exact B1345347
  · exact B1345351
  · exact B1345355
  · exact B1345359
  · exact B1345363
  · exact B1345367
  · exact B1345371
  · exact B1345375
  · exact B1345379
  · exact B1345383
  · exact B1345387
  · exact B1345391
  · exact B1345395
  · exact B1345399
  · exact B1345403
  · exact B1345407
  · exact B1345411
  · exact B1345415
  · exact B1345419
  · exact B1345423
  · exact B1345427
  · exact B1345431
  · exact B1345435
  · exact B1345439
  · exact B1345443
  · exact B1345447
  · exact B1345451
  · exact B1345455
  · exact B1345459
  · exact B1345463
  · exact B1345467
  · exact B1345471
  · exact B1345475
  · exact B1345479
  · exact B1345483
  · exact B1345487
  · exact B1345491
  · exact B1345495
  · exact B1345499
  · exact B1345503
  · exact B1345507
  · exact B1345511
  · exact B1345515
  · exact B1345519
  · exact B1345523
  · exact B1345527
  · exact B1345531
  · exact B1345535
  · exact B1345539
  · exact B1345543
  · exact B1345547
  · exact B1345551
  · exact B1345555
  · exact B1345559
  · exact B1345563
  · exact B1345567
  · exact B1345571
  · exact B1345575
  · exact B1345579
  · exact B1345583
  · exact B1345587
  · exact B1345591
  · exact B1345595
  · exact B1345599
  · exact B1345603
  · exact B1345607
  · exact B1345611
  · exact B1345615
  · exact B1345619
  · exact B1345623
  · exact B1345627
  · exact B1345631
  · exact B1345635
  · exact B1345639
  · exact B1345643
  · exact B1345647
  · exact B1345651
  · exact B1345655
  · exact B1345659
  · exact B1345663
  · exact B1345667
  · exact B1345671
  · exact B1345675
  · exact B1345679
  · exact B1345683
  · exact B1345687
  · exact B1345691
  · exact B1345695
  · exact B1345699
  · exact B1345703
  · exact B1345707
  · exact B1345711
  · exact B1345715
  · exact B1345719
  · exact B1345723
  · exact B1345727
  · exact B1345731
  · exact B1345735
  · exact B1345739
  · exact B1345743
  · exact B1345747
  · exact B1345751
  · exact B1345755
  · exact B1345759
  · exact B1345763
  · exact B1345767
  · exact B1345771
  · exact B1345775
  · exact B1345779
  · exact B1345783
  · exact B1345787
  · exact B1345791
  · exact B1345795
  · exact B1345799
  · exact B1345803
  · exact B1345807
  · exact B1345811
  · exact B1345815
  · exact B1345819
  · exact B1345823
  · exact B1345827
  · exact B1345831
  · exact B1345835
  · exact B1345839
  · exact B1345843
  · exact B1345847
  · exact B1345851
  · exact B1345855
  · exact B1345859
  · exact B1345863
  · exact B1345867
  · exact B1345871
  · exact B1345875
  · exact B1345879
  · exact B1345883
  · exact B1345887
  · exact B1345891
  · exact B1345895
  · exact B1345899
  · exact B1345903
  · exact B1345907
  · exact B1345911
  · exact B1345915
  · exact B1345919
  · exact B1345923
  · exact B1345927
  · exact B1345931
  · exact B1345935
  · exact B1345939
  · exact B1345943
  · exact B1345947
  · exact B1345951
  · exact B1345955
  · exact B1345959
  · exact B1345963
  · exact B1345967
  · exact B1345971
  · exact B1345975
  · exact B1345979
  · exact B1345983
  · exact B1345987
  · exact B1345991
  · exact B1345995
  · exact B1345999
  · exact B1346003
  · exact B1346007
  · exact B1346011
  · exact B1346015
  · exact B1346019
  · exact B1346023
  · exact B1346027
  · exact B1346031
  · exact B1346035
  · exact B1346039
  · exact B1346043
  · exact B1346047
  · exact B1346051
  · exact B1346055
  · exact B1346059
  · exact B1346063
  · exact B1346067
  · exact B1346071
  · exact B1346075
  · exact B1346079
  · exact B1346083
  · exact B1346087
  · exact B1346091
  · exact B1346095
  · exact B1346099
  · exact B1346103
  · exact B1346107
  · exact B1346111
  · exact B1346115
  · exact B1346119
  · exact B1346123
  · exact B1346127
  · exact B1346131
  · exact B1346135
  · exact B1346139
  · exact B1346143
  · exact B1346147
  · exact B1346151
  · exact B1346155
  · exact B1346159
  · exact B1346163
  · exact B1346167
  · exact B1346171
  · exact B1346175
  · exact B1346179
  · exact B1346183
  · exact B1346187
  · exact B1346191
  · exact B1346195
  · exact B1346199
  · exact B1346203
  · exact B1346207
  · exact B1346211
  · exact B1346215
  · exact B1346219
  · exact B1346223
  · exact B1346227
  · exact B1346231
  · exact B1346235
  · exact B1346239
  · exact B1346243
  · exact B1346247
  · exact B1346251
  · exact B1346255
  · exact B1346259
  · exact B1346263
  · exact B1346267
  · exact B1346271
  · exact B1346275
  · exact B1346279
  · exact B1346283
  · exact B1346287
  · exact B1346291
  · exact B1346295
  · exact B1346299
  · exact B1346303
  · exact B1346307
  · exact B1346311
  · exact B1346315
  · exact B1346319
  · exact B1346323
  · exact B1346327
  · exact B1346331
  · exact B1346335
  · exact B1346339
  · exact B1346343
  · exact B1346347
  · exact B1346351
  · exact B1346355
  · exact B1346359
  · exact B1346363
  · exact B1346367
  · exact B1346371
  · exact B1346375
  · exact B1346379
  · exact B1346383
  · exact B1346387
  · exact B1346391
  · exact B1346395
  · exact B1346399
  · exact B1346403
  · exact B1346407
  · exact B1346411
  · exact B1346415
  · exact B1346419
  · exact B1346423
  · exact B1346427
  · exact B1346431
  · exact B1346435
  · exact B1346439
  · exact B1346443
  · exact B1346447
  · exact B1346451
  · exact B1346455
  · exact B1346459
  · exact B1346463
  · exact B1346467
  · exact B1346471
  · exact B1346475
  · exact B1346479
  · exact B1346483
  · exact B1346487
  · exact B1346491
  · exact B1346495
  · exact B1346499
  · exact B1346503
  · exact B1346507
  · exact B1346511
  · exact B1346515
  · exact B1346519
  · exact B1346523
  · exact B1346527
  · exact B1346531
  · exact B1346535
  · exact B1346539
  · exact B1346543
  · exact B1346547
  · exact B1346551
  · exact B1346555
  · exact B1346559
  · exact B1346563
  · exact B1346567
  · exact B1346571
  · exact B1346575
  · exact B1346579
  · exact B1346583
  · exact B1346587
  · exact B1346591
  · exact B1346595
  · exact B1346599
  · exact B1346603
  · exact B1346607
  · exact B1346611
  · exact B1346615
  · exact B1346619
  · exact B1346623
  · exact B1346627
  · exact B1346631
  · exact B1346635
  · exact B1346639
  · exact B1346643
  · exact B1346647
  · exact B1346651
  · exact B1346655
  · exact B1346659
  · exact B1346663
  · exact B1346667
  · exact B1346671
  · exact B1346675
  · exact B1346679
  · exact B1346683
  · exact B1346687
  · exact B1346691
  · exact B1346695
  · exact B1346699
  · exact B1346703
  · exact B1346707
  · exact B1346711
  · exact B1346715
  · exact B1346719
  · exact B1346723
  · exact B1346727
  · exact B1346731
  · exact B1346735
  · exact B1346739
  · exact B1346743
  · exact B1346747
  · exact B1346751
  · exact B1346755
  · exact B1346759
  · exact B1346763
  · exact B1346767
  · exact B1346771
  · exact B1346775
  · exact B1346779
  · exact B1346783
  · exact B1346787
  · exact B1346791
  · exact B1346795
  · exact B1346799
  · exact B1346803
  · exact B1346807
  · exact B1346811
  · exact B1346815
  · exact B1346819
  · exact B1346823
  · exact B1346827
  · exact B1346831
  · exact B1346835
  · exact B1346839
  · exact B1346843
  · exact B1346847
  · exact B1346851
  · exact B1346855
  · exact B1346859
  · exact B1346863
  · exact B1346867
  · exact B1346871
  · exact B1346875
  · exact B1346879
  · exact B1346883
  · exact B1346887
  · exact B1346891
  · exact B1346895
  · exact B1346899
  · exact B1346903
  · exact B1346907
  · exact B1346911
  · exact B1346915
  · exact B1346919
  · exact B1346923
  · exact B1346927
  · exact B1346931
  · exact B1346935
  · exact B1346939
  · exact B1346943
  · exact B1346947
  · exact B1346951
  · exact B1346955
  · exact B1346959
  · exact B1346963
  · exact B1346967
  · exact B1346971
  · exact B1346975
  · exact B1346979
  · exact B1346983
  · exact B1346987
  · exact B1346991

theorem solution (m : ℕ) (hlo : 1344991 ≤ m) (hhi : m ≤ 1346991) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 336247 ≤ j := by omega
    have hj2 : j ≤ 336747 := by omega
    have hb : Blo 1344991 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
