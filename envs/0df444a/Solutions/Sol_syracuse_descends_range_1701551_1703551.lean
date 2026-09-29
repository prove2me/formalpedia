-- Prove2me | solution 1 for syracuse_descends_range_1701551_1703551
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:25:54.120645+00:00
-- url     : https://prove2.me/submissions/796ecb66-0659-4924-93f2-9ded2c20f697

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


theorem B4308997 : Blo 1701551 4308997 := bbase (se 4 (by rfl) ⟨403968, by rfl⟩ : syracuseStep 4308997 = 807937) (by norm_num)
theorem B2154529 : Blo 1701551 2154529 := bbase (se 2 (by rfl) ⟨807948, by rfl⟩ : syracuseStep 2154529 = 1615897) (by norm_num)
theorem B1818713 : Blo 1701551 1818713 := bbase (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) (by norm_num)
theorem B5455973 : Blo 1701551 5455973 := bbase (se 4 (by rfl) ⟨511497, by rfl⟩ : syracuseStep 5455973 = 1022995) (by norm_num)
theorem B4309109 : Blo 1701551 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B2424973 : Blo 1701551 2424973 := bbase (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) (by norm_num)
theorem B2154701 : Blo 1701551 2154701 := bbase (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) (by norm_num)
theorem B3637477 : Blo 1701551 3637477 := bbase (se 4 (by rfl) ⟨341013, by rfl⟩ : syracuseStep 3637477 = 682027) (by norm_num)
theorem B2154757 : Blo 1701551 2154757 := bbase (se 4 (by rfl) ⟨202008, by rfl⟩ : syracuseStep 2154757 = 404017) (by norm_num)
theorem B4309301 : Blo 1701551 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B2302285 : Blo 1701551 2302285 := bbase (se 3 (by rfl) ⟨431678, by rfl⟩ : syracuseStep 2302285 = 863357) (by norm_num)
theorem B2154853 : Blo 1701551 2154853 := bbase (se 4 (by rfl) ⟨202017, by rfl⟩ : syracuseStep 2154853 = 404035) (by norm_num)
theorem B1843561 : Blo 1701551 1843561 := bbase (se 2 (by rfl) ⟨691335, by rfl⟩ : syracuseStep 1843561 = 1382671) (by norm_num)
theorem B3277181 : Blo 1701551 3277181 := bbase (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) (by norm_num)
theorem B2728397 : Blo 1701551 2728397 := bbase (se 3 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 2728397 = 1023149) (by norm_num)
theorem B5743061 : Blo 1701551 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B2425349 : Blo 1701551 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B2155025 : Blo 1701551 2155025 := bbase (se 2 (by rfl) ⟨808134, by rfl⟩ : syracuseStep 2155025 = 1616269) (by norm_num)
theorem B1819157 : Blo 1701551 1819157 := bbase (se 6 (by rfl) ⟨42636, by rfl⟩ : syracuseStep 1819157 = 85273) (by norm_num)
theorem B2155081 : Blo 1701551 2155081 := bbase (se 2 (by rfl) ⟨808155, by rfl⟩ : syracuseStep 2155081 = 1616311) (by norm_num)
theorem B4309645 : Blo 1701551 4309645 := bbase (se 3 (by rfl) ⟨808058, by rfl⟩ : syracuseStep 4309645 = 1616117) (by norm_num)
theorem B2155177 : Blo 1701551 2155177 := bbase (se 2 (by rfl) ⟨808191, by rfl⟩ : syracuseStep 2155177 = 1616383) (by norm_num)
theorem B12935861 : Blo 1701551 12935861 := bbase (se 5 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 12935861 = 1212737) (by norm_num)
theorem B3637973 : Blo 1701551 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2589413 : Blo 1701551 2589413 := bbase (se 4 (by rfl) ⟨242757, by rfl⟩ : syracuseStep 2589413 = 485515) (by norm_num)
theorem B1942261 : Blo 1701551 1942261 := bbase (se 5 (by rfl) ⟨91043, by rfl⟩ : syracuseStep 1942261 = 182087) (by norm_num)
theorem B4309757 : Blo 1701551 4309757 := bbase (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) (by norm_num)
theorem B2073373 : Blo 1701551 2073373 := bbase (se 3 (by rfl) ⟨388757, by rfl⟩ : syracuseStep 2073373 = 777515) (by norm_num)
theorem B2155349 : Blo 1701551 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B7275365 : Blo 1701551 7275365 := bbase (se 4 (by rfl) ⟨682065, by rfl⟩ : syracuseStep 7275365 = 1364131) (by norm_num)
theorem B5743493 : Blo 1701551 5743493 := bbase (se 4 (by rfl) ⟨538452, by rfl⟩ : syracuseStep 5743493 = 1076905) (by norm_num)
theorem B8618885 : Blo 1701551 8618885 := bbase (se 4 (by rfl) ⟨808020, by rfl⟩ : syracuseStep 8618885 = 1616041) (by norm_num)
theorem B2073481 : Blo 1701551 2073481 := bbase (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) (by norm_num)
theorem B2155405 : Blo 1701551 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B3233837 : Blo 1701551 3233837 := bbase (se 3 (by rfl) ⟨606344, by rfl⟩ : syracuseStep 3233837 = 1212689) (by norm_num)
theorem B4309949 : Blo 1701551 4309949 := bbase (se 3 (by rfl) ⟨808115, by rfl⟩ : syracuseStep 4309949 = 1616231) (by norm_num)
theorem B2155501 : Blo 1701551 2155501 := bbase (se 3 (by rfl) ⟨404156, by rfl⟩ : syracuseStep 2155501 = 808313) (by norm_num)
theorem B12928085 : Blo 1701551 12928085 := bbase (se 8 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 12928085 = 151501) (by norm_num)
theorem B2155673 : Blo 1701551 2155673 := bbase (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) (by norm_num)
theorem B5457061 : Blo 1701551 5457061 := bbase (se 4 (by rfl) ⟨511599, by rfl⟩ : syracuseStep 5457061 = 1023199) (by norm_num)
theorem B3884213 : Blo 1701551 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2155729 : Blo 1701551 2155729 := bbase (se 2 (by rfl) ⟨808398, by rfl⟩ : syracuseStep 2155729 = 1616797) (by norm_num)
theorem B46613717 : Blo 1701551 46613717 := bbase (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) (by norm_num)
theorem B3990797 : Blo 1701551 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B4310293 : Blo 1701551 4310293 := bbase (se 6 (by rfl) ⟨101022, by rfl⟩ : syracuseStep 4310293 = 202045) (by norm_num)
theorem B2155825 : Blo 1701551 2155825 := bbase (se 2 (by rfl) ⟨808434, by rfl⟩ : syracuseStep 2155825 = 1616869) (by norm_num)
theorem B5743925 : Blo 1701551 5743925 := bbase (se 5 (by rfl) ⟨269246, by rfl⟩ : syracuseStep 5743925 = 538493) (by norm_num)
theorem B4851029 : Blo 1701551 4851029 := bbase (se 12 (by rfl) ⟨1776, by rfl⟩ : syracuseStep 4851029 = 3553) (by norm_num)
theorem B3687781 : Blo 1701551 3687781 := bbase (se 4 (by rfl) ⟨345729, by rfl⟩ : syracuseStep 3687781 = 691459) (by norm_num)
theorem B4089221 : Blo 1701551 4089221 := bbase (se 4 (by rfl) ⟨383364, by rfl⟩ : syracuseStep 4089221 = 766729) (by norm_num)
theorem B4310405 : Blo 1701551 4310405 := bbase (se 4 (by rfl) ⟨404100, by rfl⟩ : syracuseStep 4310405 = 808201) (by norm_num)
theorem B2155997 : Blo 1701551 2155997 := bbase (se 3 (by rfl) ⟨404249, by rfl⟩ : syracuseStep 2155997 = 808499) (by norm_num)
theorem B9692693 : Blo 1701551 9692693 := bbase (se 6 (by rfl) ⟨227172, by rfl⟩ : syracuseStep 9692693 = 454345) (by norm_num)
theorem B2156053 : Blo 1701551 2156053 := bbase (se 6 (by rfl) ⟨50532, by rfl⟩ : syracuseStep 2156053 = 101065) (by norm_num)
theorem B4089413 : Blo 1701551 4089413 := bbase (se 4 (by rfl) ⟨383382, by rfl⟩ : syracuseStep 4089413 = 766765) (by norm_num)
theorem B4310597 : Blo 1701551 4310597 := bbase (se 4 (by rfl) ⟨404118, by rfl⟩ : syracuseStep 4310597 = 808237) (by norm_num)
theorem B5744357 : Blo 1701551 5744357 := bbase (se 4 (by rfl) ⟨538533, by rfl⟩ : syracuseStep 5744357 = 1077067) (by norm_num)
theorem B33179413 : Blo 1701551 33179413 := bbase (se 6 (by rfl) ⟨777642, by rfl⟩ : syracuseStep 33179413 = 1555285) (by norm_num)
theorem B6465365 : Blo 1701551 6465365 := bbase (se 9 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 6465365 = 37883) (by norm_num)
theorem B10905461 : Blo 1701551 10905461 := bbase (se 5 (by rfl) ⟨511193, by rfl⟩ : syracuseStep 10905461 = 1022387) (by norm_num)
theorem B2074493 : Blo 1701551 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B4310941 : Blo 1701551 4310941 := bbase (se 3 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 4310941 = 1616603) (by norm_num)
theorem B4311053 : Blo 1701551 4311053 := bbase (se 3 (by rfl) ⟨808322, by rfl⟩ : syracuseStep 4311053 = 1616645) (by norm_num)
theorem B6465653 : Blo 1701551 6465653 := bbase (se 5 (by rfl) ⟨303077, by rfl⟩ : syracuseStep 6465653 = 606155) (by norm_num)
theorem B5744789 : Blo 1701551 5744789 := bbase (se 6 (by rfl) ⟨134643, by rfl⟩ : syracuseStep 5744789 = 269287) (by norm_num)
theorem B8620181 : Blo 1701551 8620181 := bbase (se 6 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 8620181 = 404071) (by norm_num)
theorem B4311245 : Blo 1701551 4311245 := bbase (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) (by norm_num)
theorem B16369877 : Blo 1701551 16369877 := bbase (se 7 (by rfl) ⟨191834, by rfl⟩ : syracuseStep 16369877 = 383669) (by norm_num)
theorem B3451189 : Blo 1701551 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B5900789 : Blo 1701551 5900789 := bbase (se 5 (by rfl) ⟨276599, by rfl⟩ : syracuseStep 5900789 = 553199) (by norm_num)
theorem B4311589 : Blo 1701551 4311589 := bbase (se 4 (by rfl) ⟨404211, by rfl⟩ : syracuseStep 4311589 = 808423) (by norm_num)
theorem B2951725 : Blo 1701551 2951725 := bbase (se 3 (by rfl) ⟨553448, by rfl⟩ : syracuseStep 2951725 = 1106897) (by norm_num)
theorem B5745221 : Blo 1701551 5745221 := bbase (se 4 (by rfl) ⟨538614, by rfl⟩ : syracuseStep 5745221 = 1077229) (by norm_num)
theorem B4311701 : Blo 1701551 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B3230381 : Blo 1701551 3230381 := bbase (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) (by norm_num)
theorem B9693877 : Blo 1701551 9693877 := bbase (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) (by norm_num)
theorem B3828509 : Blo 1701551 3828509 := bbase (se 3 (by rfl) ⟨717845, by rfl⟩ : syracuseStep 3828509 = 1435691) (by norm_num)
theorem B3230533 : Blo 1701551 3230533 := bbase (se 4 (by rfl) ⟨302862, by rfl⟩ : syracuseStep 3230533 = 605725) (by norm_num)
theorem B7875413 : Blo 1701551 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B4311893 : Blo 1701551 4311893 := bbase (se 9 (by rfl) ⟨12632, by rfl⟩ : syracuseStep 4311893 = 25265) (by norm_num)
theorem B3828581 : Blo 1701551 3828581 := bbase (se 4 (by rfl) ⟨358929, by rfl⟩ : syracuseStep 3828581 = 717859) (by norm_num)
theorem B5827493 : Blo 1701551 5827493 := bbase (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) (by norm_num)
theorem B3828653 : Blo 1701551 3828653 := bbase (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) (by norm_num)
theorem B2874413 : Blo 1701551 2874413 := bbase (se 3 (by rfl) ⟨538952, by rfl⟩ : syracuseStep 2874413 = 1077905) (by norm_num)
theorem B3828725 : Blo 1701551 3828725 := bbase (se 5 (by rfl) ⟨179471, by rfl⟩ : syracuseStep 3828725 = 358943) (by norm_num)
theorem B5745653 : Blo 1701551 5745653 := bbase (se 5 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 5745653 = 538655) (by norm_num)
theorem B3828797 : Blo 1701551 3828797 := bbase (se 3 (by rfl) ⟨717899, by rfl⟩ : syracuseStep 3828797 = 1435799) (by norm_num)
theorem B6900805 : Blo 1701551 6900805 := bbase (se 4 (by rfl) ⟨646950, by rfl⟩ : syracuseStep 6900805 = 1293901) (by norm_num)
theorem B4090981 : Blo 1701551 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B3230837 : Blo 1701551 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B9202805 : Blo 1701551 9202805 := bbase (se 5 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 9202805 = 862763) (by norm_num)
theorem B3828869 : Blo 1701551 3828869 := bbase (se 4 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 3828869 = 717913) (by norm_num)
theorem B3828941 : Blo 1701551 3828941 := bbase (se 3 (by rfl) ⟨717926, by rfl⟩ : syracuseStep 3828941 = 1435853) (by norm_num)
theorem B2911477 : Blo 1701551 2911477 := bbase (se 5 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 2911477 = 272951) (by norm_num)
theorem B3829013 : Blo 1701551 3829013 := bbase (se 6 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 3829013 = 179485) (by norm_num)
theorem B6466837 : Blo 1701551 6466837 := bbase (se 6 (by rfl) ⟨151566, by rfl⟩ : syracuseStep 6466837 = 303133) (by norm_num)
theorem B6548789 : Blo 1701551 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B3108149 : Blo 1701551 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B4369717 : Blo 1701551 4369717 := bbase (se 5 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 4369717 = 409661) (by norm_num)
theorem B3829085 : Blo 1701551 3829085 := bbase (se 3 (by rfl) ⟨717953, by rfl⟩ : syracuseStep 3829085 = 1435907) (by norm_num)
theorem B2100637 : Blo 1701551 2100637 := bbase (se 3 (by rfl) ⟨393869, by rfl⟩ : syracuseStep 2100637 = 787739) (by norm_num)
theorem B3829157 : Blo 1701551 3829157 := bbase (se 4 (by rfl) ⟨358983, by rfl⟩ : syracuseStep 3829157 = 717967) (by norm_num)
theorem B5746085 : Blo 1701551 5746085 := bbase (se 4 (by rfl) ⟨538695, by rfl⟩ : syracuseStep 5746085 = 1077391) (by norm_num)
theorem B8621477 : Blo 1701551 8621477 := bbase (se 4 (by rfl) ⟨808263, by rfl⟩ : syracuseStep 8621477 = 1616527) (by norm_num)
theorem B3452357 : Blo 1701551 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B3829229 : Blo 1701551 3829229 := bbase (se 3 (by rfl) ⟨717980, by rfl⟩ : syracuseStep 3829229 = 1435961) (by norm_num)
theorem B3829301 : Blo 1701551 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B6467141 : Blo 1701551 6467141 := bbase (se 4 (by rfl) ⟨606294, by rfl⟩ : syracuseStep 6467141 = 1212589) (by norm_num)
theorem B3829373 : Blo 1701551 3829373 := bbase (se 3 (by rfl) ⟨718007, by rfl⟩ : syracuseStep 3829373 = 1436015) (by norm_num)
theorem B3829445 : Blo 1701551 3829445 := bbase (se 4 (by rfl) ⟨359010, by rfl⟩ : syracuseStep 3829445 = 718021) (by norm_num)
theorem B4091597 : Blo 1701551 4091597 := bbase (se 3 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 4091597 = 1534349) (by norm_num)
theorem B3829517 : Blo 1701551 3829517 := bbase (se 3 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 3829517 = 1436069) (by norm_num)
theorem B3829589 : Blo 1701551 3829589 := bbase (se 9 (by rfl) ⟨11219, by rfl⟩ : syracuseStep 3829589 = 22439) (by norm_num)
theorem B5746517 : Blo 1701551 5746517 := bbase (se 9 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 5746517 = 33671) (by norm_num)
theorem B3231589 : Blo 1701551 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B3829661 : Blo 1701551 3829661 := bbase (se 3 (by rfl) ⟨718061, by rfl⟩ : syracuseStep 3829661 = 1436123) (by norm_num)
theorem B3829733 : Blo 1701551 3829733 := bbase (se 4 (by rfl) ⟨359037, by rfl⟩ : syracuseStep 3829733 = 718075) (by norm_num)
theorem B3231733 : Blo 1701551 3231733 := bbase (se 5 (by rfl) ⟨151487, by rfl⟩ : syracuseStep 3231733 = 302975) (by norm_num)
theorem B5451781 : Blo 1701551 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B14544917 : Blo 1701551 14544917 := bbase (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) (by norm_num)
theorem B3829805 : Blo 1701551 3829805 := bbase (se 3 (by rfl) ⟨718088, by rfl⟩ : syracuseStep 3829805 = 1436177) (by norm_num)
theorem B4845653 : Blo 1701551 4845653 := bbase (se 8 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 4845653 = 56785) (by norm_num)
theorem B2871389 : Blo 1701551 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B3829877 : Blo 1701551 3829877 := bbase (se 5 (by rfl) ⟨179525, by rfl⟩ : syracuseStep 3829877 = 359051) (by norm_num)
theorem B14536853 : Blo 1701551 14536853 := bbase (se 6 (by rfl) ⟨340707, by rfl⟩ : syracuseStep 14536853 = 681415) (by norm_num)
theorem B3231893 : Blo 1701551 3231893 := bbase (se 6 (by rfl) ⟨75747, by rfl⟩ : syracuseStep 3231893 = 151495) (by norm_num)
theorem B3829949 : Blo 1701551 3829949 := bbase (se 3 (by rfl) ⟨718115, by rfl⟩ : syracuseStep 3829949 = 1436231) (by norm_num)
theorem B2871517 : Blo 1701551 2871517 := bbase (se 3 (by rfl) ⟨538409, by rfl⟩ : syracuseStep 2871517 = 1076819) (by norm_num)
theorem B3830021 : Blo 1701551 3830021 := bbase (se 4 (by rfl) ⟨359064, by rfl⟩ : syracuseStep 3830021 = 718129) (by norm_num)
theorem B5746949 : Blo 1701551 5746949 := bbase (se 4 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 5746949 = 1077553) (by norm_num)
theorem B4845845 : Blo 1701551 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B6639893 : Blo 1701551 6639893 := bbase (se 6 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 6639893 = 311245) (by norm_num)
theorem B3232037 : Blo 1701551 3232037 := bbase (se 4 (by rfl) ⟨303003, by rfl⟩ : syracuseStep 3232037 = 606007) (by norm_num)
theorem B2871605 : Blo 1701551 2871605 := bbase (se 5 (by rfl) ⟨134606, by rfl⟩ : syracuseStep 2871605 = 269213) (by norm_num)
theorem B3068213 : Blo 1701551 3068213 := bbase (se 5 (by rfl) ⟨143822, by rfl⟩ : syracuseStep 3068213 = 287645) (by norm_num)
theorem B3830093 : Blo 1701551 3830093 := bbase (se 3 (by rfl) ⟨718142, by rfl⟩ : syracuseStep 3830093 = 1436285) (by norm_num)
theorem B34959701 : Blo 1701551 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B5452181 : Blo 1701551 5452181 := bbase (se 6 (by rfl) ⟨127785, by rfl⟩ : syracuseStep 5452181 = 255571) (by norm_num)
theorem B3830165 : Blo 1701551 3830165 := bbase (se 6 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 3830165 = 179539) (by norm_num)
theorem B2871733 : Blo 1701551 2871733 := bbase (se 5 (by rfl) ⟨134612, by rfl⟩ : syracuseStep 2871733 = 269225) (by norm_num)
theorem B4092373 : Blo 1701551 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B3830237 : Blo 1701551 3830237 := bbase (se 3 (by rfl) ⟨718169, by rfl⟩ : syracuseStep 3830237 = 1436339) (by norm_num)
theorem B5247461 : Blo 1701551 5247461 := bbase (se 4 (by rfl) ⟨491949, by rfl⟩ : syracuseStep 5247461 = 983899) (by norm_num)
theorem B2552333 : Blo 1701551 2552333 := bbase (se 3 (by rfl) ⟨478562, by rfl⟩ : syracuseStep 2552333 = 957125) (by norm_num)
theorem B2871821 : Blo 1701551 2871821 := bbase (se 3 (by rfl) ⟨538466, by rfl⟩ : syracuseStep 2871821 = 1076933) (by norm_num)
theorem B2552357 : Blo 1701551 2552357 := bbase (se 4 (by rfl) ⟨239283, by rfl⟩ : syracuseStep 2552357 = 478567) (by norm_num)
theorem B3830309 : Blo 1701551 3830309 := bbase (se 4 (by rfl) ⟨359091, by rfl⟩ : syracuseStep 3830309 = 718183) (by norm_num)
theorem B2552381 : Blo 1701551 2552381 := bbase (se 3 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 2552381 = 957143) (by norm_num)
theorem B3232325 : Blo 1701551 3232325 := bbase (se 4 (by rfl) ⟨303030, by rfl⟩ : syracuseStep 3232325 = 606061) (by norm_num)
theorem B2552405 : Blo 1701551 2552405 := bbase (se 8 (by rfl) ⟨14955, by rfl⟩ : syracuseStep 2552405 = 29911) (by norm_num)
theorem B2552429 : Blo 1701551 2552429 := bbase (se 3 (by rfl) ⟨478580, by rfl⟩ : syracuseStep 2552429 = 957161) (by norm_num)
theorem B3830381 : Blo 1701551 3830381 := bbase (se 3 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 3830381 = 1436393) (by norm_num)
theorem B9695861 : Blo 1701551 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B2552453 : Blo 1701551 2552453 := bbase (se 4 (by rfl) ⟨239292, by rfl⟩ : syracuseStep 2552453 = 478585) (by norm_num)
theorem B2871949 : Blo 1701551 2871949 := bbase (se 3 (by rfl) ⟨538490, by rfl⟩ : syracuseStep 2871949 = 1076981) (by norm_num)
theorem B2552477 : Blo 1701551 2552477 := bbase (se 3 (by rfl) ⟨478589, by rfl⟩ : syracuseStep 2552477 = 957179) (by norm_num)
theorem B8737445 : Blo 1701551 8737445 := bbase (se 4 (by rfl) ⟨819135, by rfl⟩ : syracuseStep 8737445 = 1638271) (by norm_num)
theorem B2552501 : Blo 1701551 2552501 := bbase (se 5 (by rfl) ⟨119648, by rfl⟩ : syracuseStep 2552501 = 239297) (by norm_num)
theorem B3830453 : Blo 1701551 3830453 := bbase (se 5 (by rfl) ⟨179552, by rfl⟩ : syracuseStep 3830453 = 359105) (by norm_num)
theorem B5747381 : Blo 1701551 5747381 := bbase (se 5 (by rfl) ⟨269408, by rfl⟩ : syracuseStep 5747381 = 538817) (by norm_num)
theorem B8622773 : Blo 1701551 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B2552525 : Blo 1701551 2552525 := bbase (se 3 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 2552525 = 957197) (by norm_num)
theorem B3232477 : Blo 1701551 3232477 := bbase (se 3 (by rfl) ⟨606089, by rfl⟩ : syracuseStep 3232477 = 1212179) (by norm_num)
theorem B2552549 : Blo 1701551 2552549 := bbase (se 4 (by rfl) ⟨239301, by rfl⟩ : syracuseStep 2552549 = 478603) (by norm_num)
theorem B2872037 : Blo 1701551 2872037 := bbase (se 4 (by rfl) ⟨269253, by rfl⟩ : syracuseStep 2872037 = 538507) (by norm_num)
theorem B2044649 : Blo 1701551 2044649 := bbase (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) (by norm_num)
theorem B2552573 : Blo 1701551 2552573 := bbase (se 3 (by rfl) ⟨478607, by rfl⟩ : syracuseStep 2552573 = 957215) (by norm_num)
theorem B3830525 : Blo 1701551 3830525 := bbase (se 3 (by rfl) ⟨718223, by rfl⟩ : syracuseStep 3830525 = 1436447) (by norm_num)
theorem B8295173 : Blo 1701551 8295173 := bbase (se 4 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 8295173 = 1555345) (by norm_num)
theorem B2552597 : Blo 1701551 2552597 := bbase (se 6 (by rfl) ⟨59826, by rfl⟩ : syracuseStep 2552597 = 119653) (by norm_num)
theorem B2044697 : Blo 1701551 2044697 := bbase (se 2 (by rfl) ⟨766761, by rfl⟩ : syracuseStep 2044697 = 1533523) (by norm_num)
theorem B2552621 : Blo 1701551 2552621 := bbase (se 3 (by rfl) ⟨478616, by rfl⟩ : syracuseStep 2552621 = 957233) (by norm_num)
theorem B2552645 : Blo 1701551 2552645 := bbase (se 4 (by rfl) ⟨239310, by rfl⟩ : syracuseStep 2552645 = 478621) (by norm_num)
theorem B3830597 : Blo 1701551 3830597 := bbase (se 4 (by rfl) ⟨359118, by rfl⟩ : syracuseStep 3830597 = 718237) (by norm_num)
theorem B2552669 : Blo 1701551 2552669 := bbase (se 3 (by rfl) ⟨478625, by rfl⟩ : syracuseStep 2552669 = 957251) (by norm_num)
theorem B2872165 : Blo 1701551 2872165 := bbase (se 4 (by rfl) ⟨269265, by rfl⟩ : syracuseStep 2872165 = 538531) (by norm_num)
theorem B2552693 : Blo 1701551 2552693 := bbase (se 5 (by rfl) ⟨119657, by rfl⟩ : syracuseStep 2552693 = 239315) (by norm_num)
theorem B2552717 : Blo 1701551 2552717 := bbase (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) (by norm_num)
theorem B3830669 : Blo 1701551 3830669 := bbase (se 3 (by rfl) ⟨718250, by rfl⟩ : syracuseStep 3830669 = 1436501) (by norm_num)
theorem B2552741 : Blo 1701551 2552741 := bbase (se 4 (by rfl) ⟨239319, by rfl⟩ : syracuseStep 2552741 = 478639) (by norm_num)
theorem B2552765 : Blo 1701551 2552765 := bbase (se 3 (by rfl) ⟨478643, by rfl⟩ : syracuseStep 2552765 = 957287) (by norm_num)
theorem B2872253 : Blo 1701551 2872253 := bbase (se 3 (by rfl) ⟨538547, by rfl⟩ : syracuseStep 2872253 = 1077095) (by norm_num)
theorem B7271365 : Blo 1701551 7271365 := bbase (se 4 (by rfl) ⟨681690, by rfl⟩ : syracuseStep 7271365 = 1363381) (by norm_num)
theorem B2552789 : Blo 1701551 2552789 := bbase (se 7 (by rfl) ⟨29915, by rfl⟩ : syracuseStep 2552789 = 59831) (by norm_num)
theorem B3830741 : Blo 1701551 3830741 := bbase (se 7 (by rfl) ⟨44891, by rfl⟩ : syracuseStep 3830741 = 89783) (by norm_num)
theorem B2552813 : Blo 1701551 2552813 := bbase (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) (by norm_num)
theorem B9204725 : Blo 1701551 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B2552837 : Blo 1701551 2552837 := bbase (se 4 (by rfl) ⟨239328, by rfl⟩ : syracuseStep 2552837 = 478657) (by norm_num)
theorem B2184197 : Blo 1701551 2184197 := bbase (se 4 (by rfl) ⟨204768, by rfl⟩ : syracuseStep 2184197 = 409537) (by norm_num)
theorem B3232781 : Blo 1701551 3232781 := bbase (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) (by norm_num)
theorem B2552861 : Blo 1701551 2552861 := bbase (se 3 (by rfl) ⟨478661, by rfl⟩ : syracuseStep 2552861 = 957323) (by norm_num)
theorem B3830813 : Blo 1701551 3830813 := bbase (se 3 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 3830813 = 1436555) (by norm_num)
theorem B1725473 : Blo 1701551 1725473 := bbase (se 2 (by rfl) ⟨647052, by rfl⟩ : syracuseStep 1725473 = 1294105) (by norm_num)
theorem B2552885 : Blo 1701551 2552885 := bbase (se 5 (by rfl) ⟨119666, by rfl⟩ : syracuseStep 2552885 = 239333) (by norm_num)
theorem B2872381 : Blo 1701551 2872381 := bbase (se 3 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 2872381 = 1077143) (by norm_num)
theorem B2552909 : Blo 1701551 2552909 := bbase (se 3 (by rfl) ⟨478670, by rfl⟩ : syracuseStep 2552909 = 957341) (by norm_num)
theorem B8614997 : Blo 1701551 8614997 := bbase (se 8 (by rfl) ⟨50478, by rfl⟩ : syracuseStep 8614997 = 100957) (by norm_num)
theorem B2552933 : Blo 1701551 2552933 := bbase (se 4 (by rfl) ⟨239337, by rfl⟩ : syracuseStep 2552933 = 478675) (by norm_num)
theorem B3830885 : Blo 1701551 3830885 := bbase (se 4 (by rfl) ⟨359145, by rfl⟩ : syracuseStep 3830885 = 718291) (by norm_num)
theorem B5747813 : Blo 1701551 5747813 := bbase (se 4 (by rfl) ⟨538857, by rfl⟩ : syracuseStep 5747813 = 1077715) (by norm_num)
theorem B2552957 : Blo 1701551 2552957 := bbase (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) (by norm_num)
theorem B2552981 : Blo 1701551 2552981 := bbase (se 6 (by rfl) ⟨59835, by rfl⟩ : syracuseStep 2552981 = 119671) (by norm_num)
theorem B2872469 : Blo 1701551 2872469 := bbase (se 6 (by rfl) ⟨67323, by rfl⟩ : syracuseStep 2872469 = 134647) (by norm_num)
theorem B4093085 : Blo 1701551 4093085 := bbase (se 3 (by rfl) ⟨767453, by rfl⟩ : syracuseStep 4093085 = 1534907) (by norm_num)
theorem B2553005 : Blo 1701551 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B3830957 : Blo 1701551 3830957 := bbase (se 3 (by rfl) ⟨718304, by rfl⟩ : syracuseStep 3830957 = 1436609) (by norm_num)
theorem B2553029 : Blo 1701551 2553029 := bbase (se 4 (by rfl) ⟨239346, by rfl⟩ : syracuseStep 2553029 = 478693) (by norm_num)
theorem B2553053 : Blo 1701551 2553053 := bbase (se 3 (by rfl) ⟨478697, by rfl⟩ : syracuseStep 2553053 = 957395) (by norm_num)
theorem B4846837 : Blo 1701551 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B2553077 : Blo 1701551 2553077 := bbase (se 5 (by rfl) ⟨119675, by rfl⟩ : syracuseStep 2553077 = 239351) (by norm_num)
theorem B3831029 : Blo 1701551 3831029 := bbase (se 5 (by rfl) ⟨179579, by rfl⟩ : syracuseStep 3831029 = 359159) (by norm_num)
theorem B3634445 : Blo 1701551 3634445 := bbase (se 3 (by rfl) ⟨681458, by rfl⟩ : syracuseStep 3634445 = 1362917) (by norm_num)
theorem B2553101 : Blo 1701551 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B2872597 : Blo 1701551 2872597 := bbase (se 6 (by rfl) ⟨67326, by rfl⟩ : syracuseStep 2872597 = 134653) (by norm_num)
theorem B2553125 : Blo 1701551 2553125 := bbase (se 4 (by rfl) ⟨239355, by rfl⟩ : syracuseStep 2553125 = 478711) (by norm_num)
theorem B1725733 : Blo 1701551 1725733 := bbase (se 4 (by rfl) ⟨161787, by rfl⟩ : syracuseStep 1725733 = 323575) (by norm_num)
theorem B2553149 : Blo 1701551 2553149 := bbase (se 3 (by rfl) ⟨478715, by rfl⟩ : syracuseStep 2553149 = 957431) (by norm_num)
theorem B2045245 : Blo 1701551 2045245 := bbase (se 3 (by rfl) ⟨383483, by rfl⟩ : syracuseStep 2045245 = 766967) (by norm_num)
theorem B3831101 : Blo 1701551 3831101 := bbase (se 3 (by rfl) ⟨718331, by rfl⟩ : syracuseStep 3831101 = 1436663) (by norm_num)
theorem B2553173 : Blo 1701551 2553173 := bbase (se 13 (by rfl) ⟨467, by rfl⟩ : syracuseStep 2553173 = 935) (by norm_num)
theorem B6550885 : Blo 1701551 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B2553197 : Blo 1701551 2553197 := bbase (se 3 (by rfl) ⟨478724, by rfl⟩ : syracuseStep 2553197 = 957449) (by norm_num)
theorem B2872685 : Blo 1701551 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B8295797 : Blo 1701551 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B2553221 : Blo 1701551 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B3831173 : Blo 1701551 3831173 := bbase (se 4 (by rfl) ⟨359172, by rfl⟩ : syracuseStep 3831173 = 718345) (by norm_num)
theorem B11654549 : Blo 1701551 11654549 := bbase (se 6 (by rfl) ⟨273153, by rfl⟩ : syracuseStep 11654549 = 546307) (by norm_num)
theorem B3634589 : Blo 1701551 3634589 := bbase (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) (by norm_num)
theorem B2553245 : Blo 1701551 2553245 := bbase (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) (by norm_num)
theorem B1914277 : Blo 1701551 1914277 := bbase (se 4 (by rfl) ⟨179463, by rfl⟩ : syracuseStep 1914277 = 358927) (by norm_num)
theorem B2553269 : Blo 1701551 2553269 := bbase (se 5 (by rfl) ⟨119684, by rfl⟩ : syracuseStep 2553269 = 239369) (by norm_num)
theorem B1914313 : Blo 1701551 1914313 := bbase (se 2 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 1914313 = 1435735) (by norm_num)
theorem B2553293 : Blo 1701551 2553293 := bbase (se 3 (by rfl) ⟨478742, by rfl⟩ : syracuseStep 2553293 = 957485) (by norm_num)
theorem B3831245 : Blo 1701551 3831245 := bbase (se 3 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 3831245 = 1436717) (by norm_num)
theorem B2553317 : Blo 1701551 2553317 := bbase (se 4 (by rfl) ⟨239373, by rfl⟩ : syracuseStep 2553317 = 478747) (by norm_num)
theorem B1914349 : Blo 1701551 1914349 := bbase (se 3 (by rfl) ⟨358940, by rfl⟩ : syracuseStep 1914349 = 717881) (by norm_num)
theorem B2872813 : Blo 1701551 2872813 := bbase (se 3 (by rfl) ⟨538652, by rfl⟩ : syracuseStep 2872813 = 1077305) (by norm_num)
theorem B3937781 : Blo 1701551 3937781 := bbase (se 5 (by rfl) ⟨184583, by rfl⟩ : syracuseStep 3937781 = 369167) (by norm_num)
theorem B2553341 : Blo 1701551 2553341 := bbase (se 3 (by rfl) ⟨478751, by rfl⟩ : syracuseStep 2553341 = 957503) (by norm_num)
theorem B1914385 : Blo 1701551 1914385 := bbase (se 2 (by rfl) ⟨717894, by rfl⟩ : syracuseStep 1914385 = 1435789) (by norm_num)
theorem B2553365 : Blo 1701551 2553365 := bbase (se 6 (by rfl) ⟨59844, by rfl⟩ : syracuseStep 2553365 = 119689) (by norm_num)
theorem B3831317 : Blo 1701551 3831317 := bbase (se 6 (by rfl) ⟨89796, by rfl⟩ : syracuseStep 3831317 = 179593) (by norm_num)
theorem B5748245 : Blo 1701551 5748245 := bbase (se 6 (by rfl) ⟨134724, by rfl⟩ : syracuseStep 5748245 = 269449) (by norm_num)
theorem B2553389 : Blo 1701551 2553389 := bbase (se 3 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 2553389 = 957521) (by norm_num)
theorem B1914421 : Blo 1701551 1914421 := bbase (se 5 (by rfl) ⟨89738, by rfl⟩ : syracuseStep 1914421 = 179477) (by norm_num)
theorem B2553413 : Blo 1701551 2553413 := bbase (se 4 (by rfl) ⟨239382, by rfl⟩ : syracuseStep 2553413 = 478765) (by norm_num)
theorem B2872901 : Blo 1701551 2872901 := bbase (se 4 (by rfl) ⟨269334, by rfl⟩ : syracuseStep 2872901 = 538669) (by norm_num)
theorem B1914457 : Blo 1701551 1914457 := bbase (se 2 (by rfl) ⟨717921, by rfl⟩ : syracuseStep 1914457 = 1435843) (by norm_num)
theorem B2553437 : Blo 1701551 2553437 := bbase (se 3 (by rfl) ⟨478769, by rfl⟩ : syracuseStep 2553437 = 957539) (by norm_num)
theorem B3831389 : Blo 1701551 3831389 := bbase (se 3 (by rfl) ⟨718385, by rfl⟩ : syracuseStep 3831389 = 1436771) (by norm_num)
theorem B2553461 : Blo 1701551 2553461 := bbase (se 5 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 2553461 = 239387) (by norm_num)
theorem B1914493 : Blo 1701551 1914493 := bbase (se 3 (by rfl) ⟨358967, by rfl⟩ : syracuseStep 1914493 = 717935) (by norm_num)
theorem B2553485 : Blo 1701551 2553485 := bbase (se 3 (by rfl) ⟨478778, by rfl⟩ : syracuseStep 2553485 = 957557) (by norm_num)
theorem B1914529 : Blo 1701551 1914529 := bbase (se 2 (by rfl) ⟨717948, by rfl⟩ : syracuseStep 1914529 = 1435897) (by norm_num)
theorem B2553509 : Blo 1701551 2553509 := bbase (se 4 (by rfl) ⟨239391, by rfl⟩ : syracuseStep 2553509 = 478783) (by norm_num)
theorem B3831461 : Blo 1701551 3831461 := bbase (se 4 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 3831461 = 718399) (by norm_num)
theorem B2553533 : Blo 1701551 2553533 := bbase (se 3 (by rfl) ⟨478787, by rfl⟩ : syracuseStep 2553533 = 957575) (by norm_num)
theorem B1914565 : Blo 1701551 1914565 := bbase (se 4 (by rfl) ⟨179490, by rfl⟩ : syracuseStep 1914565 = 358981) (by norm_num)
theorem B2873029 : Blo 1701551 2873029 := bbase (se 4 (by rfl) ⟨269346, by rfl⟩ : syracuseStep 2873029 = 538693) (by norm_num)
theorem B2553557 : Blo 1701551 2553557 := bbase (se 7 (by rfl) ⟨29924, by rfl⟩ : syracuseStep 2553557 = 59849) (by norm_num)
theorem B1914601 : Blo 1701551 1914601 := bbase (se 2 (by rfl) ⟨717975, by rfl⟩ : syracuseStep 1914601 = 1435951) (by norm_num)
theorem B2553581 : Blo 1701551 2553581 := bbase (se 3 (by rfl) ⟨478796, by rfl⟩ : syracuseStep 2553581 = 957593) (by norm_num)
theorem B3831533 : Blo 1701551 3831533 := bbase (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) (by norm_num)
theorem B3069677 : Blo 1701551 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B3233533 : Blo 1701551 3233533 := bbase (se 3 (by rfl) ⟨606287, by rfl⟩ : syracuseStep 3233533 = 1212575) (by norm_num)
theorem B3634949 : Blo 1701551 3634949 := bbase (se 4 (by rfl) ⟨340776, by rfl⟩ : syracuseStep 3634949 = 681553) (by norm_num)
theorem B2553605 : Blo 1701551 2553605 := bbase (se 4 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 2553605 = 478801) (by norm_num)
theorem B1914637 : Blo 1701551 1914637 := bbase (se 3 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 1914637 = 717989) (by norm_num)
theorem B2553629 : Blo 1701551 2553629 := bbase (se 3 (by rfl) ⟨478805, by rfl⟩ : syracuseStep 2553629 = 957611) (by norm_num)
theorem B2873117 : Blo 1701551 2873117 := bbase (se 3 (by rfl) ⟨538709, by rfl⟩ : syracuseStep 2873117 = 1077419) (by norm_num)
theorem B2045725 : Blo 1701551 2045725 := bbase (se 3 (by rfl) ⟨383573, by rfl⟩ : syracuseStep 2045725 = 767147) (by norm_num)
theorem B5601061 : Blo 1701551 5601061 := bbase (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) (by norm_num)
theorem B1914673 : Blo 1701551 1914673 := bbase (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) (by norm_num)
theorem B2553653 : Blo 1701551 2553653 := bbase (se 5 (by rfl) ⟨119702, by rfl⟩ : syracuseStep 2553653 = 239405) (by norm_num)
theorem B8181557 : Blo 1701551 8181557 := bbase (se 5 (by rfl) ⟨383510, by rfl⟩ : syracuseStep 8181557 = 767021) (by norm_num)
theorem B3831605 : Blo 1701551 3831605 := bbase (se 5 (by rfl) ⟨179606, by rfl⟩ : syracuseStep 3831605 = 359213) (by norm_num)
theorem B2553677 : Blo 1701551 2553677 := bbase (se 3 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 2553677 = 957629) (by norm_num)
theorem B1914709 : Blo 1701551 1914709 := bbase (se 9 (by rfl) ⟨5609, by rfl⟩ : syracuseStep 1914709 = 11219) (by norm_num)
theorem B2553701 : Blo 1701551 2553701 := bbase (se 4 (by rfl) ⟨239409, by rfl⟩ : syracuseStep 2553701 = 478819) (by norm_num)
theorem B1914745 : Blo 1701551 1914745 := bbase (se 2 (by rfl) ⟨718029, by rfl⟩ : syracuseStep 1914745 = 1436059) (by norm_num)
theorem B2553725 : Blo 1701551 2553725 := bbase (se 3 (by rfl) ⟨478823, by rfl⟩ : syracuseStep 2553725 = 957647) (by norm_num)
theorem B3831677 : Blo 1701551 3831677 := bbase (se 3 (by rfl) ⟨718439, by rfl⟩ : syracuseStep 3831677 = 1436879) (by norm_num)
theorem B3233677 : Blo 1701551 3233677 := bbase (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) (by norm_num)
theorem B2553749 : Blo 1701551 2553749 := bbase (se 6 (by rfl) ⟨59853, by rfl⟩ : syracuseStep 2553749 = 119707) (by norm_num)
theorem B1914781 : Blo 1701551 1914781 := bbase (se 3 (by rfl) ⟨359021, by rfl⟩ : syracuseStep 1914781 = 718043) (by norm_num)
theorem B2873245 : Blo 1701551 2873245 := bbase (se 3 (by rfl) ⟨538733, by rfl⟩ : syracuseStep 2873245 = 1077467) (by norm_num)
theorem B2553773 : Blo 1701551 2553773 := bbase (se 3 (by rfl) ⟨478832, by rfl⟩ : syracuseStep 2553773 = 957665) (by norm_num)
theorem B1914817 : Blo 1701551 1914817 := bbase (se 2 (by rfl) ⟨718056, by rfl⟩ : syracuseStep 1914817 = 1436113) (by norm_num)
theorem B2553797 : Blo 1701551 2553797 := bbase (se 4 (by rfl) ⟨239418, by rfl⟩ : syracuseStep 2553797 = 478837) (by norm_num)
theorem B3831749 : Blo 1701551 3831749 := bbase (se 4 (by rfl) ⟨359226, by rfl⟩ : syracuseStep 3831749 = 718453) (by norm_num)
theorem B5748677 : Blo 1701551 5748677 := bbase (se 4 (by rfl) ⟨538938, by rfl⟩ : syracuseStep 5748677 = 1077877) (by norm_num)
theorem B8624069 : Blo 1701551 8624069 := bbase (se 4 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 8624069 = 1617013) (by norm_num)
theorem B2553821 : Blo 1701551 2553821 := bbase (se 3 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 2553821 = 957683) (by norm_num)
theorem B1914853 : Blo 1701551 1914853 := bbase (se 4 (by rfl) ⟨179517, by rfl⟩ : syracuseStep 1914853 = 359035) (by norm_num)
theorem B2553845 : Blo 1701551 2553845 := bbase (se 5 (by rfl) ⟨119711, by rfl⟩ : syracuseStep 2553845 = 239423) (by norm_num)
theorem B8181749 : Blo 1701551 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B2873333 : Blo 1701551 2873333 := bbase (se 5 (by rfl) ⟨134687, by rfl⟩ : syracuseStep 2873333 = 269375) (by norm_num)
theorem B1914889 : Blo 1701551 1914889 := bbase (se 2 (by rfl) ⟨718083, by rfl⟩ : syracuseStep 1914889 = 1436167) (by norm_num)
theorem B3880973 : Blo 1701551 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B2553869 : Blo 1701551 2553869 := bbase (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) (by norm_num)
theorem B3831821 : Blo 1701551 3831821 := bbase (se 3 (by rfl) ⟨718466, by rfl⟩ : syracuseStep 3831821 = 1436933) (by norm_num)
theorem B6461477 : Blo 1701551 6461477 := bbase (se 4 (by rfl) ⟨605763, by rfl⟩ : syracuseStep 6461477 = 1211527) (by norm_num)
theorem B2553893 : Blo 1701551 2553893 := bbase (se 4 (by rfl) ⟨239427, by rfl⟩ : syracuseStep 2553893 = 478855) (by norm_num)
theorem B1914925 : Blo 1701551 1914925 := bbase (se 3 (by rfl) ⟨359048, by rfl⟩ : syracuseStep 1914925 = 718097) (by norm_num)
theorem B2553917 : Blo 1701551 2553917 := bbase (se 3 (by rfl) ⟨478859, by rfl⟩ : syracuseStep 2553917 = 957719) (by norm_num)
theorem B6993989 : Blo 1701551 6993989 := bbase (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) (by norm_num)
theorem B1914961 : Blo 1701551 1914961 := bbase (se 2 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 1914961 = 1436221) (by norm_num)
theorem B2553941 : Blo 1701551 2553941 := bbase (se 8 (by rfl) ⟨14964, by rfl⟩ : syracuseStep 2553941 = 29929) (by norm_num)
theorem B3831893 : Blo 1701551 3831893 := bbase (se 8 (by rfl) ⟨22452, by rfl⟩ : syracuseStep 3831893 = 44905) (by norm_num)
theorem B2422877 : Blo 1701551 2422877 := bbase (se 3 (by rfl) ⟨454289, by rfl⟩ : syracuseStep 2422877 = 908579) (by norm_num)
theorem B4307053 : Blo 1701551 4307053 := bbase (se 3 (by rfl) ⟨807572, by rfl⟩ : syracuseStep 4307053 = 1615145) (by norm_num)
theorem B2553965 : Blo 1701551 2553965 := bbase (se 3 (by rfl) ⟨478868, by rfl⟩ : syracuseStep 2553965 = 957737) (by norm_num)
theorem B1914997 : Blo 1701551 1914997 := bbase (se 5 (by rfl) ⟨89765, by rfl⟩ : syracuseStep 1914997 = 179531) (by norm_num)
theorem B2873461 : Blo 1701551 2873461 := bbase (se 5 (by rfl) ⟨134693, by rfl⟩ : syracuseStep 2873461 = 269387) (by norm_num)
theorem B2553989 : Blo 1701551 2553989 := bbase (se 4 (by rfl) ⟨239436, by rfl⟩ : syracuseStep 2553989 = 478873) (by norm_num)
theorem B1915033 : Blo 1701551 1915033 := bbase (se 2 (by rfl) ⟨718137, by rfl⟩ : syracuseStep 1915033 = 1436275) (by norm_num)
theorem B2726045 : Blo 1701551 2726045 := bbase (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) (by norm_num)
theorem B2554013 : Blo 1701551 2554013 := bbase (se 3 (by rfl) ⟨478877, by rfl⟩ : syracuseStep 2554013 = 957755) (by norm_num)
theorem B3831965 : Blo 1701551 3831965 := bbase (se 3 (by rfl) ⟨718493, by rfl⟩ : syracuseStep 3831965 = 1436987) (by norm_num)
theorem B1726633 : Blo 1701551 1726633 := bbase (se 2 (by rfl) ⟨647487, by rfl⟩ : syracuseStep 1726633 = 1294975) (by norm_num)
theorem B2554037 : Blo 1701551 2554037 := bbase (se 5 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 2554037 = 239441) (by norm_num)
theorem B1915069 : Blo 1701551 1915069 := bbase (se 3 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 1915069 = 718151) (by norm_num)
theorem B3233981 : Blo 1701551 3233981 := bbase (se 3 (by rfl) ⟨606371, by rfl⟩ : syracuseStep 3233981 = 1212743) (by norm_num)
theorem B2554061 : Blo 1701551 2554061 := bbase (se 3 (by rfl) ⟨478886, by rfl⟩ : syracuseStep 2554061 = 957773) (by norm_num)
theorem B2873549 : Blo 1701551 2873549 := bbase (se 3 (by rfl) ⟨538790, by rfl⟩ : syracuseStep 2873549 = 1077581) (by norm_num)
theorem B4307165 : Blo 1701551 4307165 := bbase (se 3 (by rfl) ⟨807593, by rfl⟩ : syracuseStep 4307165 = 1615187) (by norm_num)
theorem B1915105 : Blo 1701551 1915105 := bbase (se 2 (by rfl) ⟨718164, by rfl⟩ : syracuseStep 1915105 = 1436329) (by norm_num)
theorem B2554085 : Blo 1701551 2554085 := bbase (se 4 (by rfl) ⟨239445, by rfl⟩ : syracuseStep 2554085 = 478891) (by norm_num)
theorem B3832037 : Blo 1701551 3832037 := bbase (se 4 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 3832037 = 718507) (by norm_num)
theorem B2726141 : Blo 1701551 2726141 := bbase (se 3 (by rfl) ⟨511151, by rfl⟩ : syracuseStep 2726141 = 1022303) (by norm_num)
theorem B2554109 : Blo 1701551 2554109 := bbase (se 3 (by rfl) ⟨478895, by rfl⟩ : syracuseStep 2554109 = 957791) (by norm_num)
theorem B1915141 : Blo 1701551 1915141 := bbase (se 4 (by rfl) ⟨179544, by rfl⟩ : syracuseStep 1915141 = 359089) (by norm_num)
theorem B2554133 : Blo 1701551 2554133 := bbase (se 6 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 2554133 = 119725) (by norm_num)
theorem B2726173 : Blo 1701551 2726173 := bbase (se 3 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 2726173 = 1022315) (by norm_num)
theorem B1915177 : Blo 1701551 1915177 := bbase (se 2 (by rfl) ⟨718191, by rfl⟩ : syracuseStep 1915177 = 1436383) (by norm_num)
theorem B2554157 : Blo 1701551 2554157 := bbase (se 3 (by rfl) ⟨478904, by rfl⟩ : syracuseStep 2554157 = 957809) (by norm_num)
theorem B3832109 : Blo 1701551 3832109 := bbase (se 3 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 3832109 = 1437041) (by norm_num)
theorem B6461765 : Blo 1701551 6461765 := bbase (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) (by norm_num)
theorem B4847941 : Blo 1701551 4847941 := bbase (se 4 (by rfl) ⟨454494, by rfl⟩ : syracuseStep 4847941 = 908989) (by norm_num)
theorem B2554181 : Blo 1701551 2554181 := bbase (se 4 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 2554181 = 478909) (by norm_num)
theorem B1915213 : Blo 1701551 1915213 := bbase (se 3 (by rfl) ⟨359102, by rfl⟩ : syracuseStep 1915213 = 718205) (by norm_num)
theorem B2873677 : Blo 1701551 2873677 := bbase (se 3 (by rfl) ⟨538814, by rfl⟩ : syracuseStep 2873677 = 1077629) (by norm_num)
theorem B2554205 : Blo 1701551 2554205 := bbase (se 3 (by rfl) ⟨478913, by rfl⟩ : syracuseStep 2554205 = 957827) (by norm_num)
theorem B8616293 : Blo 1701551 8616293 := bbase (se 4 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 8616293 = 1615555) (by norm_num)
theorem B1915249 : Blo 1701551 1915249 := bbase (se 2 (by rfl) ⟨718218, by rfl⟩ : syracuseStep 1915249 = 1436437) (by norm_num)
theorem B8182133 : Blo 1701551 8182133 := bbase (se 5 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 8182133 = 767075) (by norm_num)
theorem B2554229 : Blo 1701551 2554229 := bbase (se 5 (by rfl) ⟨119729, by rfl⟩ : syracuseStep 2554229 = 239459) (by norm_num)
theorem B3832181 : Blo 1701551 3832181 := bbase (se 5 (by rfl) ⟨179633, by rfl⟩ : syracuseStep 3832181 = 359267) (by norm_num)
theorem B5749109 : Blo 1701551 5749109 := bbase (se 5 (by rfl) ⟨269489, by rfl⟩ : syracuseStep 5749109 = 538979) (by norm_num)
theorem B2554253 : Blo 1701551 2554253 := bbase (se 3 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 2554253 = 957845) (by norm_num)
theorem B1915285 : Blo 1701551 1915285 := bbase (se 6 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 1915285 = 89779) (by norm_num)
theorem B4307357 : Blo 1701551 4307357 := bbase (se 3 (by rfl) ⟨807629, by rfl⟩ : syracuseStep 4307357 = 1615259) (by norm_num)
theorem B2554277 : Blo 1701551 2554277 := bbase (se 4 (by rfl) ⟨239463, by rfl⟩ : syracuseStep 2554277 = 478927) (by norm_num)
theorem B2873765 : Blo 1701551 2873765 := bbase (se 4 (by rfl) ⟨269415, by rfl⟩ : syracuseStep 2873765 = 538831) (by norm_num)
theorem B1915321 : Blo 1701551 1915321 := bbase (se 2 (by rfl) ⟨718245, by rfl⟩ : syracuseStep 1915321 = 1436491) (by norm_num)
theorem B2554301 : Blo 1701551 2554301 := bbase (se 3 (by rfl) ⟨478931, by rfl⟩ : syracuseStep 2554301 = 957863) (by norm_num)
theorem B3832253 : Blo 1701551 3832253 := bbase (se 3 (by rfl) ⟨718547, by rfl⟩ : syracuseStep 3832253 = 1437095) (by norm_num)
theorem B2554325 : Blo 1701551 2554325 := bbase (se 7 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 2554325 = 59867) (by norm_num)
theorem B1915357 : Blo 1701551 1915357 := bbase (se 3 (by rfl) ⟨359129, by rfl⟩ : syracuseStep 1915357 = 718259) (by norm_num)
theorem B2554349 : Blo 1701551 2554349 := bbase (se 3 (by rfl) ⟨478940, by rfl⟩ : syracuseStep 2554349 = 957881) (by norm_num)
theorem B1915393 : Blo 1701551 1915393 := bbase (se 2 (by rfl) ⟨718272, by rfl⟩ : syracuseStep 1915393 = 1436545) (by norm_num)
theorem B2554373 : Blo 1701551 2554373 := bbase (se 4 (by rfl) ⟨239472, by rfl⟩ : syracuseStep 2554373 = 478945) (by norm_num)
theorem B3832325 : Blo 1701551 3832325 := bbase (se 4 (by rfl) ⟨359280, by rfl⟩ : syracuseStep 3832325 = 718561) (by norm_num)
theorem B2554397 : Blo 1701551 2554397 := bbase (se 3 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 2554397 = 957899) (by norm_num)
theorem B1915429 : Blo 1701551 1915429 := bbase (se 4 (by rfl) ⟨179571, by rfl⟩ : syracuseStep 1915429 = 359143) (by norm_num)
theorem B2873893 : Blo 1701551 2873893 := bbase (se 4 (by rfl) ⟨269427, by rfl⟩ : syracuseStep 2873893 = 538855) (by norm_num)
theorem B11647541 : Blo 1701551 11647541 := bbase (se 5 (by rfl) ⟨545978, by rfl⟩ : syracuseStep 11647541 = 1091957) (by norm_num)
theorem B2554421 : Blo 1701551 2554421 := bbase (se 5 (by rfl) ⟨119738, by rfl⟩ : syracuseStep 2554421 = 239477) (by norm_num)
theorem B2300485 : Blo 1701551 2300485 := bbase (se 4 (by rfl) ⟨215670, by rfl⟩ : syracuseStep 2300485 = 431341) (by norm_num)
theorem B1915465 : Blo 1701551 1915465 := bbase (se 2 (by rfl) ⟨718299, by rfl⟩ : syracuseStep 1915465 = 1436599) (by norm_num)
theorem B2554445 : Blo 1701551 2554445 := bbase (se 3 (by rfl) ⟨478958, by rfl⟩ : syracuseStep 2554445 = 957917) (by norm_num)
theorem B3832397 : Blo 1701551 3832397 := bbase (se 3 (by rfl) ⟨718574, by rfl⟩ : syracuseStep 3832397 = 1437149) (by norm_num)
theorem B2554469 : Blo 1701551 2554469 := bbase (se 4 (by rfl) ⟨239481, by rfl⟩ : syracuseStep 2554469 = 478963) (by norm_num)
theorem B1915501 : Blo 1701551 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B1817201 : Blo 1701551 1817201 := bbase (se 2 (by rfl) ⟨681450, by rfl⟩ : syracuseStep 1817201 = 1362901) (by norm_num)
theorem B8977013 : Blo 1701551 8977013 := bbase (se 5 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 8977013 = 841595) (by norm_num)
theorem B3635837 : Blo 1701551 3635837 := bbase (se 3 (by rfl) ⟨681719, by rfl⟩ : syracuseStep 3635837 = 1363439) (by norm_num)
theorem B2554493 : Blo 1701551 2554493 := bbase (se 3 (by rfl) ⟨478967, by rfl⟩ : syracuseStep 2554493 = 957935) (by norm_num)
theorem B2873981 : Blo 1701551 2873981 := bbase (se 3 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 2873981 = 1077743) (by norm_num)
theorem B1915537 : Blo 1701551 1915537 := bbase (se 2 (by rfl) ⟨718326, by rfl⟩ : syracuseStep 1915537 = 1436653) (by norm_num)
theorem B2554517 : Blo 1701551 2554517 := bbase (se 6 (by rfl) ⟨59871, by rfl⟩ : syracuseStep 2554517 = 119743) (by norm_num)
theorem B3832469 : Blo 1701551 3832469 := bbase (se 6 (by rfl) ⟨89823, by rfl⟩ : syracuseStep 3832469 = 179647) (by norm_num)
theorem B2554541 : Blo 1701551 2554541 := bbase (se 3 (by rfl) ⟨478976, by rfl⟩ : syracuseStep 2554541 = 957953) (by norm_num)
theorem B1915573 : Blo 1701551 1915573 := bbase (se 5 (by rfl) ⟨89792, by rfl⟩ : syracuseStep 1915573 = 179585) (by norm_num)
theorem B2554565 : Blo 1701551 2554565 := bbase (se 4 (by rfl) ⟨239490, by rfl⟩ : syracuseStep 2554565 = 478981) (by norm_num)
theorem B1915609 : Blo 1701551 1915609 := bbase (se 2 (by rfl) ⟨718353, by rfl⟩ : syracuseStep 1915609 = 1436707) (by norm_num)
theorem B2554589 : Blo 1701551 2554589 := bbase (se 3 (by rfl) ⟨478985, by rfl⟩ : syracuseStep 2554589 = 957971) (by norm_num)
theorem B3832541 : Blo 1701551 3832541 := bbase (se 3 (by rfl) ⟨718601, by rfl⟩ : syracuseStep 3832541 = 1437203) (by norm_num)
theorem B4307701 : Blo 1701551 4307701 := bbase (se 5 (by rfl) ⟨201923, by rfl⟩ : syracuseStep 4307701 = 403847) (by norm_num)
theorem B2554613 : Blo 1701551 2554613 := bbase (se 5 (by rfl) ⟨119747, by rfl⟩ : syracuseStep 2554613 = 239495) (by norm_num)
theorem B1915645 : Blo 1701551 1915645 := bbase (se 3 (by rfl) ⟨359183, by rfl⟩ : syracuseStep 1915645 = 718367) (by norm_num)
theorem B2874109 : Blo 1701551 2874109 := bbase (se 3 (by rfl) ⟨538895, by rfl⟩ : syracuseStep 2874109 = 1077791) (by norm_num)
theorem B2554637 : Blo 1701551 2554637 := bbase (se 3 (by rfl) ⟨478994, by rfl⟩ : syracuseStep 2554637 = 957989) (by norm_num)
theorem B9698069 : Blo 1701551 9698069 := bbase (se 6 (by rfl) ⟨227298, by rfl⟩ : syracuseStep 9698069 = 454597) (by norm_num)
theorem B1915681 : Blo 1701551 1915681 := bbase (se 2 (by rfl) ⟨718380, by rfl⟩ : syracuseStep 1915681 = 1436761) (by norm_num)
theorem B2554661 : Blo 1701551 2554661 := bbase (se 4 (by rfl) ⟨239499, by rfl⟩ : syracuseStep 2554661 = 478999) (by norm_num)
theorem B3832613 : Blo 1701551 3832613 := bbase (se 4 (by rfl) ⟨359307, by rfl⟩ : syracuseStep 3832613 = 718615) (by norm_num)
theorem B2554685 : Blo 1701551 2554685 := bbase (se 3 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 2554685 = 958007) (by norm_num)
theorem B1915717 : Blo 1701551 1915717 := bbase (se 4 (by rfl) ⟨179598, by rfl⟩ : syracuseStep 1915717 = 359197) (by norm_num)
theorem B2423629 : Blo 1701551 2423629 := bbase (se 3 (by rfl) ⟨454430, by rfl⟩ : syracuseStep 2423629 = 908861) (by norm_num)
theorem B2554709 : Blo 1701551 2554709 := bbase (se 9 (by rfl) ⟨7484, by rfl⟩ : syracuseStep 2554709 = 14969) (by norm_num)
theorem B2874197 : Blo 1701551 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B4307813 : Blo 1701551 4307813 := bbase (se 4 (by rfl) ⟨403857, by rfl⟩ : syracuseStep 4307813 = 807715) (by norm_num)
theorem B1915753 : Blo 1701551 1915753 := bbase (se 2 (by rfl) ⟨718407, by rfl⟩ : syracuseStep 1915753 = 1436815) (by norm_num)
theorem B2554733 : Blo 1701551 2554733 := bbase (se 3 (by rfl) ⟨479012, by rfl⟩ : syracuseStep 2554733 = 958025) (by norm_num)
theorem B3832685 : Blo 1701551 3832685 := bbase (se 3 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 3832685 = 1437257) (by norm_num)
theorem B3636085 : Blo 1701551 3636085 := bbase (se 5 (by rfl) ⟨170441, by rfl⟩ : syracuseStep 3636085 = 340883) (by norm_num)
theorem B3152773 : Blo 1701551 3152773 := bbase (se 4 (by rfl) ⟨295572, by rfl⟩ : syracuseStep 3152773 = 591145) (by norm_num)
theorem B2554757 : Blo 1701551 2554757 := bbase (se 4 (by rfl) ⟨239508, by rfl⟩ : syracuseStep 2554757 = 479017) (by norm_num)
theorem B1915789 : Blo 1701551 1915789 := bbase (se 3 (by rfl) ⟨359210, by rfl⟩ : syracuseStep 1915789 = 718421) (by norm_num)
theorem B2554781 : Blo 1701551 2554781 := bbase (se 3 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 2554781 = 958043) (by norm_num)
theorem B6552485 : Blo 1701551 6552485 := bbase (se 4 (by rfl) ⟨614295, by rfl⟩ : syracuseStep 6552485 = 1228591) (by norm_num)
theorem B2587565 : Blo 1701551 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B1915825 : Blo 1701551 1915825 := bbase (se 2 (by rfl) ⟨718434, by rfl⟩ : syracuseStep 1915825 = 1436869) (by norm_num)
theorem B2554805 : Blo 1701551 2554805 := bbase (se 5 (by rfl) ⟨119756, by rfl⟩ : syracuseStep 2554805 = 239513) (by norm_num)
theorem B3832757 : Blo 1701551 3832757 := bbase (se 5 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 3832757 = 359321) (by norm_num)
theorem B2554829 : Blo 1701551 2554829 := bbase (se 3 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 2554829 = 958061) (by norm_num)
theorem B6134741 : Blo 1701551 6134741 := bbase (se 7 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 6134741 = 143783) (by norm_num)
theorem B1915861 : Blo 1701551 1915861 := bbase (se 7 (by rfl) ⟨22451, by rfl⟩ : syracuseStep 1915861 = 44903) (by norm_num)
theorem B2874325 : Blo 1701551 2874325 := bbase (se 7 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 2874325 = 67367) (by norm_num)
theorem B2554853 : Blo 1701551 2554853 := bbase (se 4 (by rfl) ⟨239517, by rfl⟩ : syracuseStep 2554853 = 479035) (by norm_num)
theorem B1915897 : Blo 1701551 1915897 := bbase (se 2 (by rfl) ⟨718461, by rfl⟩ : syracuseStep 1915897 = 1436923) (by norm_num)
theorem B2554877 : Blo 1701551 2554877 := bbase (se 3 (by rfl) ⟨479039, by rfl⟩ : syracuseStep 2554877 = 958079) (by norm_num)
theorem B3832829 : Blo 1701551 3832829 := bbase (se 3 (by rfl) ⟨718655, by rfl⟩ : syracuseStep 3832829 = 1437311) (by norm_num)
theorem B2587661 : Blo 1701551 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B2554901 : Blo 1701551 2554901 := bbase (se 6 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 2554901 = 119761) (by norm_num)
theorem B1915933 : Blo 1701551 1915933 := bbase (se 3 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 1915933 = 718475) (by norm_num)
theorem B4308005 : Blo 1701551 4308005 := bbase (se 4 (by rfl) ⟨403875, by rfl⟩ : syracuseStep 4308005 = 807751) (by norm_num)
theorem B1817645 : Blo 1701551 1817645 := bbase (se 3 (by rfl) ⟨340808, by rfl⟩ : syracuseStep 1817645 = 681617) (by norm_num)
theorem B2554925 : Blo 1701551 2554925 := bbase (se 3 (by rfl) ⟨479048, by rfl⟩ : syracuseStep 2554925 = 958097) (by norm_num)
theorem B1915969 : Blo 1701551 1915969 := bbase (se 2 (by rfl) ⟨718488, by rfl⟩ : syracuseStep 1915969 = 1436977) (by norm_num)
theorem B2554949 : Blo 1701551 2554949 := bbase (se 4 (by rfl) ⟨239526, by rfl⟩ : syracuseStep 2554949 = 479053) (by norm_num)
theorem B3832901 : Blo 1701551 3832901 := bbase (se 4 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 3832901 = 718669) (by norm_num)
theorem B2153557 : Blo 1701551 2153557 := bbase (se 8 (by rfl) ⟨12618, by rfl⟩ : syracuseStep 2153557 = 25237) (by norm_num)
theorem B6134869 : Blo 1701551 6134869 := bbase (se 8 (by rfl) ⟨35946, by rfl⟩ : syracuseStep 6134869 = 71893) (by norm_num)
theorem B3882077 : Blo 1701551 3882077 := bbase (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) (by norm_num)
theorem B2554973 : Blo 1701551 2554973 := bbase (se 3 (by rfl) ⟨479057, by rfl⟩ : syracuseStep 2554973 = 958115) (by norm_num)
theorem B1916005 : Blo 1701551 1916005 := bbase (se 4 (by rfl) ⟨179625, by rfl⟩ : syracuseStep 1916005 = 359251) (by norm_num)
theorem B2554997 : Blo 1701551 2554997 := bbase (se 5 (by rfl) ⟨119765, by rfl⟩ : syracuseStep 2554997 = 239531) (by norm_num)
theorem B4603013 : Blo 1701551 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B1916041 : Blo 1701551 1916041 := bbase (se 2 (by rfl) ⟨718515, by rfl⟩ : syracuseStep 1916041 = 1437031) (by norm_num)
theorem B2555021 : Blo 1701551 2555021 := bbase (se 3 (by rfl) ⟨479066, by rfl⟩ : syracuseStep 2555021 = 958133) (by norm_num)
theorem B3832973 : Blo 1701551 3832973 := bbase (se 3 (by rfl) ⟨718682, by rfl⟩ : syracuseStep 3832973 = 1437365) (by norm_num)
theorem B2555045 : Blo 1701551 2555045 := bbase (se 4 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 2555045 = 479071) (by norm_num)
theorem B1916077 : Blo 1701551 1916077 := bbase (se 3 (by rfl) ⟨359264, by rfl⟩ : syracuseStep 1916077 = 718529) (by norm_num)
theorem B2874541 : Blo 1701551 2874541 := bbase (se 3 (by rfl) ⟨538976, by rfl⟩ : syracuseStep 2874541 = 1077953) (by norm_num)
theorem B2555069 : Blo 1701551 2555069 := bbase (se 3 (by rfl) ⟨479075, by rfl⟩ : syracuseStep 2555069 = 958151) (by norm_num)
theorem B1916113 : Blo 1701551 1916113 := bbase (se 2 (by rfl) ⟨718542, by rfl⟩ : syracuseStep 1916113 = 1437085) (by norm_num)
theorem B13991125 : Blo 1701551 13991125 := bbase (se 7 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 13991125 = 327917) (by norm_num)
theorem B2555093 : Blo 1701551 2555093 := bbase (se 7 (by rfl) ⟨29942, by rfl⟩ : syracuseStep 2555093 = 59885) (by norm_num)
theorem B2555117 : Blo 1701551 2555117 := bbase (se 3 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 2555117 = 958169) (by norm_num)
theorem B1916149 : Blo 1701551 1916149 := bbase (se 5 (by rfl) ⟨89819, by rfl⟩ : syracuseStep 1916149 = 179639) (by norm_num)
theorem B2153729 : Blo 1701551 2153729 := bbase (se 2 (by rfl) ⟨807648, by rfl⟩ : syracuseStep 2153729 = 1615297) (by norm_num)
theorem B2555141 : Blo 1701551 2555141 := bbase (se 4 (by rfl) ⟨239544, by rfl⟩ : syracuseStep 2555141 = 479089) (by norm_num)
theorem B2874629 : Blo 1701551 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B1916185 : Blo 1701551 1916185 := bbase (se 2 (by rfl) ⟨718569, by rfl⟩ : syracuseStep 1916185 = 1437139) (by norm_num)
theorem B2555165 : Blo 1701551 2555165 := bbase (se 3 (by rfl) ⟨479093, by rfl⟩ : syracuseStep 2555165 = 958187) (by norm_num)
theorem B1817893 : Blo 1701551 1817893 := bbase (se 4 (by rfl) ⟨170427, by rfl⟩ : syracuseStep 1817893 = 340855) (by norm_num)
theorem B2555189 : Blo 1701551 2555189 := bbase (se 5 (by rfl) ⟨119774, by rfl⟩ : syracuseStep 2555189 = 239549) (by norm_num)
theorem B2153785 : Blo 1701551 2153785 := bbase (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) (by norm_num)
theorem B1916221 : Blo 1701551 1916221 := bbase (se 3 (by rfl) ⟨359291, by rfl⟩ : syracuseStep 1916221 = 718583) (by norm_num)
theorem B2555213 : Blo 1701551 2555213 := bbase (se 3 (by rfl) ⟨479102, by rfl⟩ : syracuseStep 2555213 = 958205) (by norm_num)
theorem B1916257 : Blo 1701551 1916257 := bbase (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) (by norm_num)
theorem B2555237 : Blo 1701551 2555237 := bbase (se 4 (by rfl) ⟨239553, by rfl⟩ : syracuseStep 2555237 = 479107) (by norm_num)
theorem B3636589 : Blo 1701551 3636589 := bbase (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) (by norm_num)
theorem B4308349 : Blo 1701551 4308349 := bbase (se 3 (by rfl) ⟨807815, by rfl⟩ : syracuseStep 4308349 = 1615631) (by norm_num)
theorem B2555261 : Blo 1701551 2555261 := bbase (se 3 (by rfl) ⟨479111, by rfl⟩ : syracuseStep 2555261 = 958223) (by norm_num)
theorem B1916293 : Blo 1701551 1916293 := bbase (se 4 (by rfl) ⟨179652, by rfl⟩ : syracuseStep 1916293 = 359305) (by norm_num)
theorem B10911125 : Blo 1701551 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B2555285 : Blo 1701551 2555285 := bbase (se 6 (by rfl) ⟨59889, by rfl⟩ : syracuseStep 2555285 = 119779) (by norm_num)
theorem B2153881 : Blo 1701551 2153881 := bbase (se 2 (by rfl) ⟨807705, by rfl⟩ : syracuseStep 2153881 = 1615411) (by norm_num)
theorem B1916329 : Blo 1701551 1916329 := bbase (se 2 (by rfl) ⟨718623, by rfl⟩ : syracuseStep 1916329 = 1437247) (by norm_num)
theorem B2555309 : Blo 1701551 2555309 := bbase (se 3 (by rfl) ⟨479120, by rfl⟩ : syracuseStep 2555309 = 958241) (by norm_num)
theorem B1916365 : Blo 1701551 1916365 := bbase (se 3 (by rfl) ⟨359318, by rfl⟩ : syracuseStep 1916365 = 718637) (by norm_num)
theorem B6462949 : Blo 1701551 6462949 := bbase (se 4 (by rfl) ⟨605901, by rfl⟩ : syracuseStep 6462949 = 1211803) (by norm_num)
theorem B4308461 : Blo 1701551 4308461 := bbase (se 3 (by rfl) ⟨807836, by rfl⟩ : syracuseStep 4308461 = 1615673) (by norm_num)
theorem B1916401 : Blo 1701551 1916401 := bbase (se 2 (by rfl) ⟨718650, by rfl⟩ : syracuseStep 1916401 = 1437301) (by norm_num)
theorem B20708885 : Blo 1701551 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B1916437 : Blo 1701551 1916437 := bbase (se 6 (by rfl) ⟨44916, by rfl⟩ : syracuseStep 1916437 = 89833) (by norm_num)
theorem B3194405 : Blo 1701551 3194405 := bbase (se 4 (by rfl) ⟨299475, by rfl⟩ : syracuseStep 3194405 = 598951) (by norm_num)
theorem B1916473 : Blo 1701551 1916473 := bbase (se 2 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 1916473 = 1437355) (by norm_num)
theorem B2154053 : Blo 1701551 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B32710229 : Blo 1701551 32710229 := bbase (se 8 (by rfl) ⟨191661, by rfl⟩ : syracuseStep 32710229 = 383323) (by norm_num)
theorem B2424421 : Blo 1701551 2424421 := bbase (se 4 (by rfl) ⟨227289, by rfl⟩ : syracuseStep 2424421 = 454579) (by norm_num)
theorem B8617589 : Blo 1701551 8617589 := bbase (se 5 (by rfl) ⟨403949, by rfl⟩ : syracuseStep 8617589 = 807899) (by norm_num)
theorem B2154109 : Blo 1701551 2154109 := bbase (se 3 (by rfl) ⟨403895, by rfl⟩ : syracuseStep 2154109 = 807791) (by norm_num)
theorem B1941121 : Blo 1701551 1941121 := bbase (se 2 (by rfl) ⟨727920, by rfl⟩ : syracuseStep 1941121 = 1455841) (by norm_num)
theorem B4308653 : Blo 1701551 4308653 := bbase (se 3 (by rfl) ⟨807872, by rfl⟩ : syracuseStep 4308653 = 1615745) (by norm_num)
theorem B1941185 : Blo 1701551 1941185 := bbase (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) (by norm_num)
theorem B3546821 : Blo 1701551 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2154205 : Blo 1701551 2154205 := bbase (se 3 (by rfl) ⟨403913, by rfl⟩ : syracuseStep 2154205 = 807827) (by norm_num)
theorem B1818337 : Blo 1701551 1818337 := bbase (se 2 (by rfl) ⟨681876, by rfl⟩ : syracuseStep 1818337 = 1363753) (by norm_num)
theorem B2727685 : Blo 1701551 2727685 := bbase (se 4 (by rfl) ⟨255720, by rfl⟩ : syracuseStep 2727685 = 511441) (by norm_num)
theorem B6463253 : Blo 1701551 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1818397 : Blo 1701551 1818397 := bbase (se 3 (by rfl) ⟨340949, by rfl⟩ : syracuseStep 1818397 = 681899) (by norm_num)
theorem B4849445 : Blo 1701551 4849445 := bbase (se 4 (by rfl) ⟨454635, by rfl⟩ : syracuseStep 4849445 = 909271) (by norm_num)
theorem B7274357 : Blo 1701551 7274357 := bbase (se 5 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 7274357 = 681971) (by norm_num)
theorem B2154377 : Blo 1701551 2154377 := bbase (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) (by norm_num)
theorem B2301869 : Blo 1701551 2301869 := bbase (se 3 (by rfl) ⟨431600, by rfl⟩ : syracuseStep 2301869 = 863201) (by norm_num)
theorem B2424757 : Blo 1701551 2424757 := bbase (se 5 (by rfl) ⟨113660, by rfl⟩ : syracuseStep 2424757 = 227321) (by norm_num)
theorem B2154433 : Blo 1701551 2154433 := bbase (se 2 (by rfl) ⟨807912, by rfl⟩ : syracuseStep 2154433 = 1615825) (by norm_num)
theorem B23298101 : Blo 1701551 23298101 := bstep (se 5 (by rfl) ⟨1092098, by rfl⟩ : syracuseStep 23298101 = 2184197) B2184197
theorem B3637315 : Blo 1701551 3637315 := bstep (se 1 (by rfl) ⟨2727986, by rfl⟩ : syracuseStep 3637315 = 5455973) B5455973
theorem B9691235 : Blo 1701551 9691235 := bstep (se 1 (by rfl) ⟨7268426, by rfl⟩ : syracuseStep 9691235 = 14536853) B14536853
theorem B2154595 : Blo 1701551 2154595 := bstep (se 1 (by rfl) ⟨1615946, by rfl⟩ : syracuseStep 2154595 = 3231893) B3231893
theorem B5742737 : Blo 1701551 5742737 := bstep (se 2 (by rfl) ⟨2153526, by rfl⟩ : syracuseStep 5742737 = 4307053) B4307053
theorem B2154691 : Blo 1701551 2154691 := bstep (se 1 (by rfl) ⟨1616018, by rfl⟩ : syracuseStep 2154691 = 3232037) B3232037
theorem B2302177 : Blo 1701551 2302177 := bstep (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) B1726633
theorem B23306467 : Blo 1701551 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B4849901 : Blo 1701551 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B4849969 : Blo 1701551 4849969 := bstep (se 2 (by rfl) ⟨1818738, by rfl⟩ : syracuseStep 4849969 = 3637477) B3637477
theorem B1818931 : Blo 1701551 1818931 := bstep (se 1 (by rfl) ⟨1364198, by rfl⟩ : syracuseStep 1818931 = 2728397) B2728397
theorem B6463907 : Blo 1701551 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B6463921 : Blo 1701551 6463921 := bstep (se 2 (by rfl) ⟨2423970, by rfl⟩ : syracuseStep 6463921 = 4847941) B4847941
theorem B5824963 : Blo 1701551 5824963 := bstep (se 1 (by rfl) ⟨4368722, by rfl⟩ : syracuseStep 5824963 = 8737445) B8737445
theorem B2425315 : Blo 1701551 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B5530115 : Blo 1701551 5530115 := bstep (se 1 (by rfl) ⟨4147586, by rfl⟩ : syracuseStep 5530115 = 8295173) B8295173
theorem B4850243 : Blo 1701551 4850243 := bstep (se 1 (by rfl) ⟨3637682, by rfl⟩ : syracuseStep 4850243 = 7275365) B7275365
theorem B5456497 : Blo 1701551 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B6136483 : Blo 1701551 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B5743277 : Blo 1701551 5743277 := bstep (se 3 (by rfl) ⟨1076864, by rfl⟩ : syracuseStep 5743277 = 2153729) B2153729
theorem B2155187 : Blo 1701551 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B5743331 : Blo 1701551 5743331 := bstep (se 1 (by rfl) ⟨4307498, by rfl⟩ : syracuseStep 5743331 = 8614997) B8614997
theorem B8618723 : Blo 1701551 8618723 := bstep (se 1 (by rfl) ⟨6464042, by rfl⟩ : syracuseStep 8618723 = 12928085) B12928085
theorem B2728723 : Blo 1701551 2728723 := bstep (se 1 (by rfl) ⟨2046542, by rfl⟩ : syracuseStep 2728723 = 4093085) B4093085
theorem B2589475 : Blo 1701551 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B5530531 : Blo 1701551 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B4309969 : Blo 1701551 4309969 := bstep (se 2 (by rfl) ⟨1616238, by rfl⟩ : syracuseStep 4309969 = 3232477) B3232477
theorem B5743601 : Blo 1701551 5743601 := bstep (se 2 (by rfl) ⟨2153850, by rfl⟩ : syracuseStep 5743601 = 4307701) B4307701
theorem B9692237 : Blo 1701551 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B4310243 : Blo 1701551 4310243 := bstep (se 1 (by rfl) ⟨3232682, by rfl⟩ : syracuseStep 4310243 = 6465365) B6465365
theorem B13993229 : Blo 1701551 13993229 := bstep (se 3 (by rfl) ⟨2623730, by rfl⟩ : syracuseStep 13993229 = 5247461) B5247461
theorem B2155891 : Blo 1701551 2155891 := bstep (se 1 (by rfl) ⟨1616918, by rfl⟩ : syracuseStep 2155891 = 3233837) B3233837
theorem B4662659 : Blo 1701551 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B4851085 : Blo 1701551 4851085 := bstep (se 3 (by rfl) ⟨909578, by rfl⟩ : syracuseStep 4851085 = 1819157) B1819157
theorem B4310435 : Blo 1701551 4310435 := bstep (se 1 (by rfl) ⟨3232826, by rfl⟩ : syracuseStep 4310435 = 6465653) B6465653
theorem B2155987 : Blo 1701551 2155987 := bstep (se 1 (by rfl) ⟨1616990, by rfl⟩ : syracuseStep 2155987 = 3233981) B3233981
theorem B10913251 : Blo 1701551 10913251 := bstep (se 1 (by rfl) ⟨8184938, by rfl⟩ : syracuseStep 10913251 = 16369877) B16369877
theorem B5744141 : Blo 1701551 5744141 := bstep (se 3 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 5744141 = 2154053) B2154053
theorem B10905101 : Blo 1701551 10905101 := bstep (se 3 (by rfl) ⟨2044706, by rfl⟩ : syracuseStep 10905101 = 4089413) B4089413
theorem B8619533 : Blo 1701551 8619533 := bstep (se 3 (by rfl) ⟨1616162, by rfl⟩ : syracuseStep 8619533 = 3232325) B3232325
theorem B7276081 : Blo 1701551 7276081 := bstep (se 2 (by rfl) ⟨2728530, by rfl⟩ : syracuseStep 7276081 = 5457061) B5457061
theorem B5744195 : Blo 1701551 5744195 := bstep (se 1 (by rfl) ⟨4308146, by rfl⟩ : syracuseStep 5744195 = 8616293) B8616293
theorem B18654833 : Blo 1701551 18654833 := bstep (se 2 (by rfl) ⟨6995562, by rfl⟩ : syracuseStep 18654833 = 13991125) B13991125
theorem B3933859 : Blo 1701551 3933859 := bstep (se 1 (by rfl) ⟨2950394, by rfl⟩ : syracuseStep 3933859 = 5900789) B5900789
theorem B8734513 : Blo 1701551 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B4917041 : Blo 1701551 4917041 := bstep (se 2 (by rfl) ⟨1843890, by rfl⟩ : syracuseStep 4917041 = 3687781) B3687781
theorem B5744465 : Blo 1701551 5744465 := bstep (se 2 (by rfl) ⟨2154174, by rfl⟩ : syracuseStep 5744465 = 4308349) B4308349
theorem B6465379 : Blo 1701551 6465379 := bstep (se 1 (by rfl) ⟨4849034, by rfl⟩ : syracuseStep 6465379 = 9698069) B9698069
theorem B9832325 : Blo 1701551 9832325 := bstep (se 4 (by rfl) ⟨921780, by rfl⟩ : syracuseStep 9832325 = 1843561) B1843561
theorem B4368323 : Blo 1701551 4368323 := bstep (se 1 (by rfl) ⟨3276242, by rfl⟩ : syracuseStep 4368323 = 6552485) B6552485
theorem B3884995 : Blo 1701551 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B8185805 : Blo 1701551 8185805 := bstep (se 3 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 8185805 = 3069677) B3069677
theorem B4089827 : Blo 1701551 4089827 := bstep (se 1 (by rfl) ⟨3067370, by rfl⟩ : syracuseStep 4089827 = 6134741) B6134741
theorem B5531981 : Blo 1701551 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B4311377 : Blo 1701551 4311377 := bstep (se 2 (by rfl) ⟨1616766, by rfl⟩ : syracuseStep 4311377 = 3233533) B3233533
theorem B13805923 : Blo 1701551 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B5745005 : Blo 1701551 5745005 := bstep (se 3 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 5745005 = 2154377) B2154377
theorem B44239217 : Blo 1701551 44239217 := bstep (se 2 (by rfl) ⟨16589706, by rfl⟩ : syracuseStep 44239217 = 33179413) B33179413
theorem B4311427 : Blo 1701551 4311427 := bstep (se 1 (by rfl) ⟨3233570, by rfl⟩ : syracuseStep 4311427 = 6467141) B6467141
theorem B5745059 : Blo 1701551 5745059 := bstep (se 1 (by rfl) ⟨4308794, by rfl⟩ : syracuseStep 5745059 = 8617589) B8617589
theorem B6900173 : Blo 1701551 6900173 := bstep (se 3 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 6900173 = 2587565) B2587565
theorem B6138317 : Blo 1701551 6138317 := bstep (se 3 (by rfl) ⟨1150934, by rfl⟩ : syracuseStep 6138317 = 2301869) B2301869
theorem B4311569 : Blo 1701551 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B7269041 : Blo 1701551 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B5745329 : Blo 1701551 5745329 := bstep (se 2 (by rfl) ⟨2154498, by rfl⟩ : syracuseStep 5745329 = 4308997) B4308997
theorem B10349261 : Blo 1701551 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B3230435 : Blo 1701551 3230435 := bstep (se 1 (by rfl) ⟨2422826, by rfl⟩ : syracuseStep 3230435 = 4845653) B4845653
theorem B27601717 : Blo 1701551 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B4426595 : Blo 1701551 4426595 := bstep (se 1 (by rfl) ⟨3319946, by rfl⟩ : syracuseStep 4426595 = 6639893) B6639893
theorem B3828689 : Blo 1701551 3828689 := bstep (se 2 (by rfl) ⟨1435758, by rfl⟩ : syracuseStep 3828689 = 2871517) B2871517
theorem B3828707 : Blo 1701551 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B5745869 : Blo 1701551 5745869 := bstep (se 3 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 5745869 = 2154701) B2154701
theorem B3828977 : Blo 1701551 3828977 := bstep (se 2 (by rfl) ⟨1435866, by rfl⟩ : syracuseStep 3828977 = 2871733) B2871733
theorem B3828995 : Blo 1701551 3828995 := bstep (se 1 (by rfl) ⟨2871746, by rfl⟩ : syracuseStep 3828995 = 5743493) B5743493
theorem B5745923 : Blo 1701551 5745923 := bstep (se 1 (by rfl) ⟨4309442, by rfl⟩ : syracuseStep 5745923 = 8618885) B8618885
theorem B44231957 : Blo 1701551 44231957 := bstep (se 6 (by rfl) ⟨1036686, by rfl⟩ : syracuseStep 44231957 = 2073373) B2073373
theorem B7269709 : Blo 1701551 7269709 := bstep (se 3 (by rfl) ⟨1363070, by rfl⟩ : syracuseStep 7269709 = 2726141) B2726141
theorem B12922253 : Blo 1701551 12922253 := bstep (se 3 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 12922253 = 4845845) B4845845
theorem B3935633 : Blo 1701551 3935633 := bstep (se 2 (by rfl) ⟨1475862, by rfl⟩ : syracuseStep 3935633 = 2951725) B2951725
theorem B3067313 : Blo 1701551 3067313 := bstep (se 2 (by rfl) ⟨1150242, by rfl⟩ : syracuseStep 3067313 = 2300485) B2300485
theorem B31075811 : Blo 1701551 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B3829265 : Blo 1701551 3829265 := bstep (se 2 (by rfl) ⟨1435974, by rfl⟩ : syracuseStep 3829265 = 2871949) B2871949
theorem B5746193 : Blo 1701551 5746193 := bstep (se 2 (by rfl) ⟨2154822, by rfl⟩ : syracuseStep 5746193 = 4309645) B4309645
theorem B3829283 : Blo 1701551 3829283 := bstep (se 1 (by rfl) ⟨2871962, by rfl⟩ : syracuseStep 3829283 = 5743925) B5743925
theorem B7769699 : Blo 1701551 7769699 := bstep (se 1 (by rfl) ⟨5827274, by rfl⟩ : syracuseStep 7769699 = 11654549) B11654549
theorem B3231505 : Blo 1701551 3231505 := bstep (se 2 (by rfl) ⟨1211814, by rfl⟩ : syracuseStep 3231505 = 2423629) B2423629
theorem B3829553 : Blo 1701551 3829553 := bstep (se 2 (by rfl) ⟨1436082, by rfl⟩ : syracuseStep 3829553 = 2872165) B2872165
theorem B3829571 : Blo 1701551 3829571 := bstep (se 1 (by rfl) ⟨2872178, by rfl⟩ : syracuseStep 3829571 = 5744357) B5744357
theorem B7270307 : Blo 1701551 7270307 := bstep (se 1 (by rfl) ⟨5452730, by rfl⟩ : syracuseStep 7270307 = 10905461) B10905461
theorem B9695153 : Blo 1701551 9695153 := bstep (se 2 (by rfl) ⟨3635682, by rfl⟩ : syracuseStep 9695153 = 7271365) B7271365
theorem B6467597 : Blo 1701551 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B5746733 : Blo 1701551 5746733 := bstep (se 3 (by rfl) ⟨1077512, by rfl⟩ : syracuseStep 5746733 = 2155025) B2155025
theorem B3829841 : Blo 1701551 3829841 := bstep (se 2 (by rfl) ⟨1436190, by rfl⟩ : syracuseStep 3829841 = 2872381) B2872381
theorem B3829859 : Blo 1701551 3829859 := bstep (se 1 (by rfl) ⟨2872394, by rfl⟩ : syracuseStep 3829859 = 5744789) B5744789
theorem B5746787 : Blo 1701551 5746787 := bstep (se 1 (by rfl) ⟨4310090, by rfl⟩ : syracuseStep 5746787 = 8620181) B8620181
theorem B8623907 : Blo 1701551 8623907 := bstep (se 1 (by rfl) ⟨6467930, by rfl⟩ : syracuseStep 8623907 = 12935861) B12935861
theorem B2871409 : Blo 1701551 2871409 := bstep (se 2 (by rfl) ⟨1076778, by rfl⟩ : syracuseStep 2871409 = 2153557) B2153557
theorem B8179825 : Blo 1701551 8179825 := bstep (se 2 (by rfl) ⟨3067434, by rfl⟩ : syracuseStep 8179825 = 6134869) B6134869
theorem B2871443 : Blo 1701551 2871443 := bstep (se 1 (by rfl) ⟨2153582, by rfl⟩ : syracuseStep 2871443 = 4307165) B4307165
theorem B2871571 : Blo 1701551 2871571 := bstep (se 1 (by rfl) ⟨2153678, by rfl⟩ : syracuseStep 2871571 = 4307357) B4307357
theorem B4845869 : Blo 1701551 4845869 := bstep (se 3 (by rfl) ⟨908600, by rfl⟩ : syracuseStep 4845869 = 1817201) B1817201
theorem B3830129 : Blo 1701551 3830129 := bstep (se 2 (by rfl) ⟨1436298, by rfl⟩ : syracuseStep 3830129 = 2872597) B2872597
theorem B5747057 : Blo 1701551 5747057 := bstep (se 2 (by rfl) ⟨2155146, by rfl⟩ : syracuseStep 5747057 = 4310293) B4310293
theorem B8622449 : Blo 1701551 8622449 := bstep (se 2 (by rfl) ⟨3233418, by rfl⟩ : syracuseStep 8622449 = 6466837) B6466837
theorem B3830147 : Blo 1701551 3830147 := bstep (se 1 (by rfl) ⟨2872610, by rfl⟩ : syracuseStep 3830147 = 5745221) B5745221
theorem B2871713 : Blo 1701551 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B5984675 : Blo 1701551 5984675 := bstep (se 1 (by rfl) ⟨4488506, by rfl⟩ : syracuseStep 5984675 = 8977013) B8977013
theorem B8614349 : Blo 1701551 8614349 := bstep (se 3 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 8614349 = 3230381) B3230381
theorem B2552339 : Blo 1701551 2552339 := bstep (se 1 (by rfl) ⟨1914254, by rfl⟩ : syracuseStep 2552339 = 3828509) B3828509
theorem B2871841 : Blo 1701551 2871841 := bstep (se 2 (by rfl) ⟨1076940, by rfl⟩ : syracuseStep 2871841 = 2153881) B2153881
theorem B2552369 : Blo 1701551 2552369 := bstep (se 2 (by rfl) ⟨957138, by rfl⟩ : syracuseStep 2552369 = 1914277) B1914277
theorem B2552387 : Blo 1701551 2552387 := bstep (se 1 (by rfl) ⟨1914290, by rfl⟩ : syracuseStep 2552387 = 3828581) B3828581
theorem B2871875 : Blo 1701551 2871875 := bstep (se 1 (by rfl) ⟨2153906, by rfl⟩ : syracuseStep 2871875 = 4307813) B4307813
theorem B2552417 : Blo 1701551 2552417 := bstep (se 2 (by rfl) ⟨957156, by rfl⟩ : syracuseStep 2552417 = 1914313) B1914313
theorem B5452397 : Blo 1701551 5452397 := bstep (se 3 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 5452397 = 2044649) B2044649
theorem B2552435 : Blo 1701551 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B2552465 : Blo 1701551 2552465 := bstep (se 2 (by rfl) ⟨957174, by rfl⟩ : syracuseStep 2552465 = 1914349) B1914349
theorem B3830417 : Blo 1701551 3830417 := bstep (se 2 (by rfl) ⟨1436406, by rfl⟩ : syracuseStep 3830417 = 2872813) B2872813
theorem B2552483 : Blo 1701551 2552483 := bstep (se 1 (by rfl) ⟨1914362, by rfl⟩ : syracuseStep 2552483 = 3828725) B3828725
theorem B3830435 : Blo 1701551 3830435 := bstep (se 1 (by rfl) ⟨2872826, by rfl⟩ : syracuseStep 3830435 = 5745653) B5745653
theorem B2552513 : Blo 1701551 2552513 := bstep (se 2 (by rfl) ⟨957192, by rfl⟩ : syracuseStep 2552513 = 1914385) B1914385
theorem B2872003 : Blo 1701551 2872003 := bstep (se 1 (by rfl) ⟨2154002, by rfl⟩ : syracuseStep 2872003 = 4308005) B4308005
theorem B16814789 : Blo 1701551 16814789 := bstep (se 4 (by rfl) ⟨1576386, by rfl⟩ : syracuseStep 16814789 = 3152773) B3152773
theorem B2552531 : Blo 1701551 2552531 := bstep (se 1 (by rfl) ⟨1914398, by rfl⟩ : syracuseStep 2552531 = 3828797) B3828797
theorem B5452525 : Blo 1701551 5452525 := bstep (se 3 (by rfl) ⟨1022348, by rfl⟩ : syracuseStep 5452525 = 2044697) B2044697
theorem B2552561 : Blo 1701551 2552561 := bstep (se 2 (by rfl) ⟨957210, by rfl⟩ : syracuseStep 2552561 = 1914421) B1914421
theorem B2552579 : Blo 1701551 2552579 := bstep (se 1 (by rfl) ⟨1914434, by rfl⟩ : syracuseStep 2552579 = 3828869) B3828869
theorem B3068675 : Blo 1701551 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B2552609 : Blo 1701551 2552609 := bstep (se 2 (by rfl) ⟨957228, by rfl⟩ : syracuseStep 2552609 = 1914457) B1914457
theorem B3232561 : Blo 1701551 3232561 := bstep (se 2 (by rfl) ⟨1212210, by rfl⟩ : syracuseStep 3232561 = 2424421) B2424421
theorem B2552627 : Blo 1701551 2552627 := bstep (se 1 (by rfl) ⟨1914470, by rfl⟩ : syracuseStep 2552627 = 3828941) B3828941
theorem B2552657 : Blo 1701551 2552657 := bstep (se 2 (by rfl) ⟨957246, by rfl⟩ : syracuseStep 2552657 = 1914493) B1914493
theorem B2872145 : Blo 1701551 2872145 := bstep (se 2 (by rfl) ⟨1077054, by rfl⟩ : syracuseStep 2872145 = 2154109) B2154109
theorem B2552675 : Blo 1701551 2552675 := bstep (se 1 (by rfl) ⟨1914506, by rfl⟩ : syracuseStep 2552675 = 3829013) B3829013
theorem B2552705 : Blo 1701551 2552705 := bstep (se 2 (by rfl) ⟨957264, by rfl⟩ : syracuseStep 2552705 = 1914529) B1914529
theorem B5747597 : Blo 1701551 5747597 := bstep (se 3 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 5747597 = 2155349) B2155349
theorem B2552723 : Blo 1701551 2552723 := bstep (se 1 (by rfl) ⟨1914542, by rfl⟩ : syracuseStep 2552723 = 3829085) B3829085
theorem B2552753 : Blo 1701551 2552753 := bstep (se 2 (by rfl) ⟨957282, by rfl⟩ : syracuseStep 2552753 = 1914565) B1914565
theorem B3830705 : Blo 1701551 3830705 := bstep (se 2 (by rfl) ⟨1436514, by rfl⟩ : syracuseStep 3830705 = 2873029) B2873029
theorem B2552771 : Blo 1701551 2552771 := bstep (se 1 (by rfl) ⟨1914578, by rfl⟩ : syracuseStep 2552771 = 3829157) B3829157
theorem B3830723 : Blo 1701551 3830723 := bstep (se 1 (by rfl) ⟨2873042, by rfl⟩ : syracuseStep 3830723 = 5746085) B5746085
theorem B5747651 : Blo 1701551 5747651 := bstep (se 1 (by rfl) ⟨4310738, by rfl⟩ : syracuseStep 5747651 = 8621477) B8621477
theorem B2872273 : Blo 1701551 2872273 := bstep (se 2 (by rfl) ⟨1077102, by rfl⟩ : syracuseStep 2872273 = 2154205) B2154205
theorem B2552801 : Blo 1701551 2552801 := bstep (se 2 (by rfl) ⟨957300, by rfl⟩ : syracuseStep 2552801 = 1914601) B1914601
theorem B2552819 : Blo 1701551 2552819 := bstep (se 1 (by rfl) ⟨1914614, by rfl⟩ : syracuseStep 2552819 = 3829229) B3829229
theorem B2872307 : Blo 1701551 2872307 := bstep (se 1 (by rfl) ⟨2154230, by rfl⟩ : syracuseStep 2872307 = 4308461) B4308461
theorem B2552849 : Blo 1701551 2552849 := bstep (se 2 (by rfl) ⟨957318, by rfl⟩ : syracuseStep 2552849 = 1914637) B1914637
theorem B2552867 : Blo 1701551 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B7468081 : Blo 1701551 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B2552897 : Blo 1701551 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B2552915 : Blo 1701551 2552915 := bstep (se 1 (by rfl) ⟨1914686, by rfl⟩ : syracuseStep 2552915 = 3829373) B3829373
theorem B2552945 : Blo 1701551 2552945 := bstep (se 2 (by rfl) ⟨957354, by rfl⟩ : syracuseStep 2552945 = 1914709) B1914709
theorem B2872435 : Blo 1701551 2872435 := bstep (se 1 (by rfl) ⟨2154326, by rfl⟩ : syracuseStep 2872435 = 4308653) B4308653
theorem B2552963 : Blo 1701551 2552963 := bstep (se 1 (by rfl) ⟨1914722, by rfl⟩ : syracuseStep 2552963 = 3829445) B3829445
theorem B2364547 : Blo 1701551 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B2552993 : Blo 1701551 2552993 := bstep (se 2 (by rfl) ⟨957372, by rfl⟩ : syracuseStep 2552993 = 1914745) B1914745
theorem B2553011 : Blo 1701551 2553011 := bstep (se 1 (by rfl) ⟨1914758, by rfl⟩ : syracuseStep 2553011 = 3829517) B3829517
theorem B3232963 : Blo 1701551 3232963 := bstep (se 1 (by rfl) ⟨2424722, by rfl⟩ : syracuseStep 3232963 = 4849445) B4849445
theorem B2553041 : Blo 1701551 2553041 := bstep (se 2 (by rfl) ⟨957390, by rfl⟩ : syracuseStep 2553041 = 1914781) B1914781
theorem B3830993 : Blo 1701551 3830993 := bstep (se 2 (by rfl) ⟨1436622, by rfl⟩ : syracuseStep 3830993 = 2873245) B2873245
theorem B5747921 : Blo 1701551 5747921 := bstep (se 2 (by rfl) ⟨2155470, by rfl⟩ : syracuseStep 5747921 = 4310941) B4310941
theorem B2553059 : Blo 1701551 2553059 := bstep (se 1 (by rfl) ⟨1914794, by rfl⟩ : syracuseStep 2553059 = 3829589) B3829589
theorem B3831011 : Blo 1701551 3831011 := bstep (se 1 (by rfl) ⟨2873258, by rfl⟩ : syracuseStep 3831011 = 5746517) B5746517
theorem B3233009 : Blo 1701551 3233009 := bstep (se 2 (by rfl) ⟨1212378, by rfl⟩ : syracuseStep 3233009 = 2424757) B2424757
theorem B2553089 : Blo 1701551 2553089 := bstep (se 2 (by rfl) ⟨957408, by rfl⟩ : syracuseStep 2553089 = 1914817) B1914817
theorem B2872577 : Blo 1701551 2872577 := bstep (se 2 (by rfl) ⟨1077216, by rfl⟩ : syracuseStep 2872577 = 2154433) B2154433
theorem B2553107 : Blo 1701551 2553107 := bstep (se 1 (by rfl) ⟨1914830, by rfl⟩ : syracuseStep 2553107 = 3829661) B3829661
theorem B2553137 : Blo 1701551 2553137 := bstep (se 2 (by rfl) ⟨957426, by rfl⟩ : syracuseStep 2553137 = 1914853) B1914853
theorem B2553155 : Blo 1701551 2553155 := bstep (se 1 (by rfl) ⟨1914866, by rfl⟩ : syracuseStep 2553155 = 3829733) B3829733
theorem B2553185 : Blo 1701551 2553185 := bstep (se 2 (by rfl) ⟨957444, by rfl⟩ : syracuseStep 2553185 = 1914889) B1914889
theorem B9696611 : Blo 1701551 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B2553203 : Blo 1701551 2553203 := bstep (se 1 (by rfl) ⟨1914902, by rfl⟩ : syracuseStep 2553203 = 3829805) B3829805
theorem B2872705 : Blo 1701551 2872705 := bstep (se 2 (by rfl) ⟨1077264, by rfl⟩ : syracuseStep 2872705 = 2154529) B2154529
theorem B2553233 : Blo 1701551 2553233 := bstep (se 2 (by rfl) ⟨957462, by rfl⟩ : syracuseStep 2553233 = 1914925) B1914925
theorem B1914259 : Blo 1701551 1914259 := bstep (se 1 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 1914259 = 2871389) B2871389
theorem B2553251 : Blo 1701551 2553251 := bstep (se 1 (by rfl) ⟨1914938, by rfl⟩ : syracuseStep 2553251 = 3829877) B3829877
theorem B2872739 : Blo 1701551 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B4601261 : Blo 1701551 4601261 := bstep (se 3 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 4601261 = 1725473) B1725473
theorem B2553281 : Blo 1701551 2553281 := bstep (se 2 (by rfl) ⟨957480, by rfl⟩ : syracuseStep 2553281 = 1914961) B1914961
theorem B4847053 : Blo 1701551 4847053 := bstep (se 3 (by rfl) ⟨908822, by rfl⟩ : syracuseStep 4847053 = 1817645) B1817645
theorem B2553299 : Blo 1701551 2553299 := bstep (se 1 (by rfl) ⟨1914974, by rfl⟩ : syracuseStep 2553299 = 3829949) B3829949
theorem B2553329 : Blo 1701551 2553329 := bstep (se 2 (by rfl) ⟨957498, by rfl⟩ : syracuseStep 2553329 = 1914997) B1914997
theorem B3831281 : Blo 1701551 3831281 := bstep (se 2 (by rfl) ⟨1436730, by rfl⟩ : syracuseStep 3831281 = 2873461) B2873461
theorem B2553347 : Blo 1701551 2553347 := bstep (se 1 (by rfl) ⟨1915010, by rfl⟩ : syracuseStep 2553347 = 3830021) B3830021
theorem B3831299 : Blo 1701551 3831299 := bstep (se 1 (by rfl) ⟨2873474, by rfl⟩ : syracuseStep 3831299 = 5746949) B5746949
theorem B3233297 : Blo 1701551 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B44234261 : Blo 1701551 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B2553377 : Blo 1701551 2553377 := bstep (se 2 (by rfl) ⟨957516, by rfl⟩ : syracuseStep 2553377 = 1915033) B1915033
theorem B1914403 : Blo 1701551 1914403 := bstep (se 1 (by rfl) ⟨1435802, by rfl⟩ : syracuseStep 1914403 = 2871605) B2871605
theorem B2872867 : Blo 1701551 2872867 := bstep (se 1 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 2872867 = 4309301) B4309301
theorem B2553395 : Blo 1701551 2553395 := bstep (se 1 (by rfl) ⟨1915046, by rfl⟩ : syracuseStep 2553395 = 3830093) B3830093
theorem B6461005 : Blo 1701551 6461005 := bstep (se 3 (by rfl) ⟨1211438, by rfl⟩ : syracuseStep 6461005 = 2422877) B2422877
theorem B2553425 : Blo 1701551 2553425 := bstep (se 2 (by rfl) ⟨957534, by rfl⟩ : syracuseStep 2553425 = 1915069) B1915069
theorem B2184787 : Blo 1701551 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B3634787 : Blo 1701551 3634787 := bstep (se 1 (by rfl) ⟨2726090, by rfl⟩ : syracuseStep 3634787 = 5452181) B5452181
theorem B2553443 : Blo 1701551 2553443 := bstep (se 1 (by rfl) ⟨1915082, by rfl⟩ : syracuseStep 2553443 = 3830165) B3830165
theorem B2553473 : Blo 1701551 2553473 := bstep (se 2 (by rfl) ⟨957552, by rfl⟩ : syracuseStep 2553473 = 1915105) B1915105
theorem B2553491 : Blo 1701551 2553491 := bstep (se 1 (by rfl) ⟨1915118, by rfl⟩ : syracuseStep 2553491 = 3830237) B3830237
theorem B2553521 : Blo 1701551 2553521 := bstep (se 2 (by rfl) ⟨957570, by rfl⟩ : syracuseStep 2553521 = 1915141) B1915141
theorem B1701555 : Blo 1701551 1701555 := bstep (se 1 (by rfl) ⟨1276166, by rfl⟩ : syracuseStep 1701555 = 2552333) B2552333
theorem B1914547 : Blo 1701551 1914547 := bstep (se 1 (by rfl) ⟨1435910, by rfl⟩ : syracuseStep 1914547 = 2871821) B2871821
theorem B2873009 : Blo 1701551 2873009 := bstep (se 2 (by rfl) ⟨1077378, by rfl⟩ : syracuseStep 2873009 = 2154757) B2154757
theorem B2553539 : Blo 1701551 2553539 := bstep (se 1 (by rfl) ⟨1915154, by rfl⟩ : syracuseStep 2553539 = 3830309) B3830309
theorem B1701571 : Blo 1701551 1701571 := bstep (se 1 (by rfl) ⟨1276178, by rfl⟩ : syracuseStep 1701571 = 2552357) B2552357
theorem B36804293 : Blo 1701551 36804293 := bstep (se 4 (by rfl) ⟨3450402, by rfl⟩ : syracuseStep 36804293 = 6900805) B6900805
theorem B3634897 : Blo 1701551 3634897 := bstep (se 2 (by rfl) ⟨1363086, by rfl⟩ : syracuseStep 3634897 = 2726173) B2726173
theorem B1701587 : Blo 1701551 1701587 := bstep (se 1 (by rfl) ⟨1276190, by rfl⟩ : syracuseStep 1701587 = 2552381) B2552381
theorem B2553569 : Blo 1701551 2553569 := bstep (se 2 (by rfl) ⟨957588, by rfl⟩ : syracuseStep 2553569 = 1915177) B1915177
theorem B1701603 : Blo 1701551 1701603 := bstep (se 1 (by rfl) ⟨1276202, by rfl⟩ : syracuseStep 1701603 = 2552405) B2552405
theorem B5748461 : Blo 1701551 5748461 := bstep (se 3 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 5748461 = 2155673) B2155673
theorem B4601585 : Blo 1701551 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1701619 : Blo 1701551 1701619 := bstep (se 1 (by rfl) ⟨1276214, by rfl⟩ : syracuseStep 1701619 = 2552429) B2552429
theorem B2553587 : Blo 1701551 2553587 := bstep (se 1 (by rfl) ⟨1915190, by rfl⟩ : syracuseStep 2553587 = 3830381) B3830381
theorem B1701635 : Blo 1701551 1701635 := bstep (se 1 (by rfl) ⟨1276226, by rfl⟩ : syracuseStep 1701635 = 2552453) B2552453
theorem B2553617 : Blo 1701551 2553617 := bstep (se 2 (by rfl) ⟨957606, by rfl⟩ : syracuseStep 2553617 = 1915213) B1915213
theorem B3831569 : Blo 1701551 3831569 := bstep (se 2 (by rfl) ⟨1436838, by rfl⟩ : syracuseStep 3831569 = 2873677) B2873677
theorem B1701651 : Blo 1701551 1701651 := bstep (se 1 (by rfl) ⟨1276238, by rfl⟩ : syracuseStep 1701651 = 2552477) B2552477
theorem B3069713 : Blo 1701551 3069713 := bstep (se 2 (by rfl) ⟨1151142, by rfl⟩ : syracuseStep 3069713 = 2302285) B2302285
theorem B1701667 : Blo 1701551 1701667 := bstep (se 1 (by rfl) ⟨1276250, by rfl⟩ : syracuseStep 1701667 = 2552501) B2552501
theorem B2553635 : Blo 1701551 2553635 := bstep (se 1 (by rfl) ⟨1915226, by rfl⟩ : syracuseStep 2553635 = 3830453) B3830453
theorem B3831587 : Blo 1701551 3831587 := bstep (se 1 (by rfl) ⟨2873690, by rfl⟩ : syracuseStep 3831587 = 5747381) B5747381
theorem B5748515 : Blo 1701551 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B2873137 : Blo 1701551 2873137 := bstep (se 2 (by rfl) ⟨1077426, by rfl⟩ : syracuseStep 2873137 = 2154853) B2154853
theorem B1701683 : Blo 1701551 1701683 := bstep (se 1 (by rfl) ⟨1276262, by rfl⟩ : syracuseStep 1701683 = 2552525) B2552525
theorem B2553665 : Blo 1701551 2553665 := bstep (se 2 (by rfl) ⟨957624, by rfl⟩ : syracuseStep 2553665 = 1915249) B1915249
theorem B1701699 : Blo 1701551 1701699 := bstep (se 1 (by rfl) ⟨1276274, by rfl⟩ : syracuseStep 1701699 = 2552549) B2552549
theorem B1914691 : Blo 1701551 1914691 := bstep (se 1 (by rfl) ⟨1436018, by rfl⟩ : syracuseStep 1914691 = 2872037) B2872037
theorem B1701715 : Blo 1701551 1701715 := bstep (se 1 (by rfl) ⟨1276286, by rfl⟩ : syracuseStep 1701715 = 2552573) B2552573
theorem B2553683 : Blo 1701551 2553683 := bstep (se 1 (by rfl) ⟨1915262, by rfl⟩ : syracuseStep 2553683 = 3830525) B3830525
theorem B2873171 : Blo 1701551 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1701731 : Blo 1701551 1701731 := bstep (se 1 (by rfl) ⟨1276298, by rfl⟩ : syracuseStep 1701731 = 2552597) B2552597
theorem B2553713 : Blo 1701551 2553713 := bstep (se 2 (by rfl) ⟨957642, by rfl⟩ : syracuseStep 2553713 = 1915285) B1915285
theorem B1701747 : Blo 1701551 1701747 := bstep (se 1 (by rfl) ⟨1276310, by rfl⟩ : syracuseStep 1701747 = 2552621) B2552621
theorem B1701763 : Blo 1701551 1701763 := bstep (se 1 (by rfl) ⟨1276322, by rfl⟩ : syracuseStep 1701763 = 2552645) B2552645
theorem B2553731 : Blo 1701551 2553731 := bstep (se 1 (by rfl) ⟨1915298, by rfl⟩ : syracuseStep 2553731 = 3830597) B3830597
theorem B1701779 : Blo 1701551 1701779 := bstep (se 1 (by rfl) ⟨1276334, by rfl⟩ : syracuseStep 1701779 = 2552669) B2552669
theorem B2553761 : Blo 1701551 2553761 := bstep (se 2 (by rfl) ⟨957660, by rfl⟩ : syracuseStep 2553761 = 1915321) B1915321
theorem B1701795 : Blo 1701551 1701795 := bstep (se 1 (by rfl) ⟨1276346, by rfl⟩ : syracuseStep 1701795 = 2552693) B2552693
theorem B1701811 : Blo 1701551 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B2553779 : Blo 1701551 2553779 := bstep (se 1 (by rfl) ⟨1915334, by rfl⟩ : syracuseStep 2553779 = 3830669) B3830669
theorem B1701827 : Blo 1701551 1701827 := bstep (se 1 (by rfl) ⟨1276370, by rfl⟩ : syracuseStep 1701827 = 2552741) B2552741
theorem B2553809 : Blo 1701551 2553809 := bstep (se 2 (by rfl) ⟨957678, by rfl⟩ : syracuseStep 2553809 = 1915357) B1915357
theorem B1701843 : Blo 1701551 1701843 := bstep (se 1 (by rfl) ⟨1276382, by rfl⟩ : syracuseStep 1701843 = 2552765) B2552765
theorem B1914835 : Blo 1701551 1914835 := bstep (se 1 (by rfl) ⟨1436126, by rfl⟩ : syracuseStep 1914835 = 2872253) B2872253
theorem B2873299 : Blo 1701551 2873299 := bstep (se 1 (by rfl) ⟨2154974, by rfl⟩ : syracuseStep 2873299 = 4309949) B4309949
theorem B1701859 : Blo 1701551 1701859 := bstep (se 1 (by rfl) ⟨1276394, by rfl⟩ : syracuseStep 1701859 = 2552789) B2552789
theorem B2553827 : Blo 1701551 2553827 := bstep (se 1 (by rfl) ⟨1915370, by rfl⟩ : syracuseStep 2553827 = 3830741) B3830741
theorem B1701875 : Blo 1701551 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B2553857 : Blo 1701551 2553857 := bstep (se 2 (by rfl) ⟨957696, by rfl⟩ : syracuseStep 2553857 = 1915393) B1915393
theorem B1701891 : Blo 1701551 1701891 := bstep (se 1 (by rfl) ⟨1276418, by rfl⟩ : syracuseStep 1701891 = 2552837) B2552837
theorem B1701907 : Blo 1701551 1701907 := bstep (se 1 (by rfl) ⟨1276430, by rfl⟩ : syracuseStep 1701907 = 2552861) B2552861
theorem B2553875 : Blo 1701551 2553875 := bstep (se 1 (by rfl) ⟨1915406, by rfl⟩ : syracuseStep 2553875 = 3830813) B3830813
theorem B1701923 : Blo 1701551 1701923 := bstep (se 1 (by rfl) ⟨1276442, by rfl⟩ : syracuseStep 1701923 = 2552885) B2552885
theorem B2553905 : Blo 1701551 2553905 := bstep (se 2 (by rfl) ⟨957714, by rfl⟩ : syracuseStep 2553905 = 1915429) B1915429
theorem B3831857 : Blo 1701551 3831857 := bstep (se 2 (by rfl) ⟨1436946, by rfl⟩ : syracuseStep 3831857 = 2873893) B2873893
theorem B1701939 : Blo 1701551 1701939 := bstep (se 1 (by rfl) ⟨1276454, by rfl⟩ : syracuseStep 1701939 = 2552909) B2552909
theorem B5748785 : Blo 1701551 5748785 := bstep (se 2 (by rfl) ⟨2155794, by rfl⟩ : syracuseStep 5748785 = 4311589) B4311589
theorem B1701955 : Blo 1701551 1701955 := bstep (se 1 (by rfl) ⟨1276466, by rfl⟩ : syracuseStep 1701955 = 2552933) B2552933
theorem B2553923 : Blo 1701551 2553923 := bstep (se 1 (by rfl) ⟨1915442, by rfl⟩ : syracuseStep 2553923 = 3830885) B3830885
theorem B3831875 : Blo 1701551 3831875 := bstep (se 1 (by rfl) ⟨2873906, by rfl⟩ : syracuseStep 3831875 = 5747813) B5747813
theorem B1701971 : Blo 1701551 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B2553953 : Blo 1701551 2553953 := bstep (se 2 (by rfl) ⟨957732, by rfl⟩ : syracuseStep 2553953 = 1915465) B1915465
theorem B2873441 : Blo 1701551 2873441 := bstep (se 2 (by rfl) ⟨1077540, by rfl⟩ : syracuseStep 2873441 = 2155081) B2155081
theorem B1701987 : Blo 1701551 1701987 := bstep (se 1 (by rfl) ⟨1276490, by rfl⟩ : syracuseStep 1701987 = 2552981) B2552981
theorem B1914979 : Blo 1701551 1914979 := bstep (se 1 (by rfl) ⟨1436234, by rfl⟩ : syracuseStep 1914979 = 2872469) B2872469
theorem B1702003 : Blo 1701551 1702003 := bstep (se 1 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 1702003 = 2553005) B2553005
theorem B2553971 : Blo 1701551 2553971 := bstep (se 1 (by rfl) ⟨1915478, by rfl⟩ : syracuseStep 2553971 = 3830957) B3830957
theorem B1702019 : Blo 1701551 1702019 := bstep (se 1 (by rfl) ⟨1276514, by rfl⟩ : syracuseStep 1702019 = 2553029) B2553029
theorem B17463437 : Blo 1701551 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B8181901 : Blo 1701551 8181901 := bstep (se 3 (by rfl) ⟨1534106, by rfl⟩ : syracuseStep 8181901 = 3068213) B3068213
theorem B2554001 : Blo 1701551 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B1702035 : Blo 1701551 1702035 := bstep (se 1 (by rfl) ⟨1276526, by rfl⟩ : syracuseStep 1702035 = 2553053) B2553053
theorem B1702051 : Blo 1701551 1702051 := bstep (se 1 (by rfl) ⟨1276538, by rfl⟩ : syracuseStep 1702051 = 2553077) B2553077
theorem B2554019 : Blo 1701551 2554019 := bstep (se 1 (by rfl) ⟨1915514, by rfl⟩ : syracuseStep 2554019 = 3831029) B3831029
theorem B2422963 : Blo 1701551 2422963 := bstep (se 1 (by rfl) ⟨1817222, by rfl⟩ : syracuseStep 2422963 = 3634445) B3634445
theorem B1702067 : Blo 1701551 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B2660531 : Blo 1701551 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B2554049 : Blo 1701551 2554049 := bstep (se 2 (by rfl) ⟨957768, by rfl⟩ : syracuseStep 2554049 = 1915537) B1915537
theorem B1702083 : Blo 1701551 1702083 := bstep (se 1 (by rfl) ⟨1276562, by rfl⟩ : syracuseStep 1702083 = 2553125) B2553125
theorem B1702099 : Blo 1701551 1702099 := bstep (se 1 (by rfl) ⟨1276574, by rfl⟩ : syracuseStep 1702099 = 2553149) B2553149
theorem B2554067 : Blo 1701551 2554067 := bstep (se 1 (by rfl) ⟨1915550, by rfl⟩ : syracuseStep 2554067 = 3831101) B3831101
theorem B2873569 : Blo 1701551 2873569 := bstep (se 2 (by rfl) ⟨1077588, by rfl⟩ : syracuseStep 2873569 = 2155177) B2155177
theorem B1702115 : Blo 1701551 1702115 := bstep (se 1 (by rfl) ⟨1276586, by rfl⟩ : syracuseStep 1702115 = 2553173) B2553173
theorem B3234019 : Blo 1701551 3234019 := bstep (se 1 (by rfl) ⟨2425514, by rfl⟩ : syracuseStep 3234019 = 4851029) B4851029
theorem B12925169 : Blo 1701551 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B2554097 : Blo 1701551 2554097 := bstep (se 2 (by rfl) ⟨957786, by rfl⟩ : syracuseStep 2554097 = 1915573) B1915573
theorem B1702131 : Blo 1701551 1702131 := bstep (se 1 (by rfl) ⟨1276598, by rfl⟩ : syracuseStep 1702131 = 2553197) B2553197
theorem B1915123 : Blo 1701551 1915123 := bstep (se 1 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 1915123 = 2872685) B2872685
theorem B2726147 : Blo 1701551 2726147 := bstep (se 1 (by rfl) ⟨2044610, by rfl⟩ : syracuseStep 2726147 = 4089221) B4089221
theorem B1702147 : Blo 1701551 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B2554115 : Blo 1701551 2554115 := bstep (se 1 (by rfl) ⟨1915586, by rfl⟩ : syracuseStep 2554115 = 3831173) B3831173
theorem B2873603 : Blo 1701551 2873603 := bstep (se 1 (by rfl) ⟨2155202, by rfl⟩ : syracuseStep 2873603 = 4310405) B4310405
theorem B1702163 : Blo 1701551 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B2554145 : Blo 1701551 2554145 := bstep (se 2 (by rfl) ⟨957804, by rfl⟩ : syracuseStep 2554145 = 1915609) B1915609
theorem B1702179 : Blo 1701551 1702179 := bstep (se 1 (by rfl) ⟨1276634, by rfl⟩ : syracuseStep 1702179 = 2553269) B2553269
theorem B1702195 : Blo 1701551 1702195 := bstep (se 1 (by rfl) ⟨1276646, by rfl⟩ : syracuseStep 1702195 = 2553293) B2553293
theorem B2554163 : Blo 1701551 2554163 := bstep (se 1 (by rfl) ⟨1915622, by rfl⟩ : syracuseStep 2554163 = 3831245) B3831245
theorem B1702211 : Blo 1701551 1702211 := bstep (se 1 (by rfl) ⟨1276658, by rfl⟩ : syracuseStep 1702211 = 2553317) B2553317
theorem B2554193 : Blo 1701551 2554193 := bstep (se 2 (by rfl) ⟨957822, by rfl⟩ : syracuseStep 2554193 = 1915645) B1915645
theorem B3832145 : Blo 1701551 3832145 := bstep (se 2 (by rfl) ⟨1437054, by rfl⟩ : syracuseStep 3832145 = 2874109) B2874109
theorem B1702227 : Blo 1701551 1702227 := bstep (se 1 (by rfl) ⟨1276670, by rfl⟩ : syracuseStep 1702227 = 2553341) B2553341
theorem B6461795 : Blo 1701551 6461795 := bstep (se 1 (by rfl) ⟨4846346, by rfl⟩ : syracuseStep 6461795 = 9692693) B9692693
theorem B1702243 : Blo 1701551 1702243 := bstep (se 1 (by rfl) ⟨1276682, by rfl⟩ : syracuseStep 1702243 = 2553365) B2553365
theorem B2554211 : Blo 1701551 2554211 := bstep (se 1 (by rfl) ⟨1915658, by rfl⟩ : syracuseStep 2554211 = 3831317) B3831317
theorem B3832163 : Blo 1701551 3832163 := bstep (se 1 (by rfl) ⟨2874122, by rfl⟩ : syracuseStep 3832163 = 5748245) B5748245
theorem B1702259 : Blo 1701551 1702259 := bstep (se 1 (by rfl) ⟨1276694, by rfl⟩ : syracuseStep 1702259 = 2553389) B2553389
theorem B2554241 : Blo 1701551 2554241 := bstep (se 2 (by rfl) ⟨957840, by rfl⟩ : syracuseStep 2554241 = 1915681) B1915681
theorem B1702275 : Blo 1701551 1702275 := bstep (se 1 (by rfl) ⟨1276706, by rfl⟩ : syracuseStep 1702275 = 2553413) B2553413
theorem B1915267 : Blo 1701551 1915267 := bstep (se 1 (by rfl) ⟨1436450, by rfl⟩ : syracuseStep 1915267 = 2872901) B2872901
theorem B2873731 : Blo 1701551 2873731 := bstep (se 1 (by rfl) ⟨2155298, by rfl⟩ : syracuseStep 2873731 = 4310597) B4310597
theorem B1702291 : Blo 1701551 1702291 := bstep (se 1 (by rfl) ⟨1276718, by rfl⟩ : syracuseStep 1702291 = 2553437) B2553437
theorem B2554259 : Blo 1701551 2554259 := bstep (se 1 (by rfl) ⟨1915694, by rfl⟩ : syracuseStep 2554259 = 3831389) B3831389
theorem B1702307 : Blo 1701551 1702307 := bstep (se 1 (by rfl) ⟨1276730, by rfl⟩ : syracuseStep 1702307 = 2553461) B2553461
theorem B4307377 : Blo 1701551 4307377 := bstep (se 2 (by rfl) ⟨1615266, by rfl⟩ : syracuseStep 4307377 = 3230533) B3230533
theorem B1702323 : Blo 1701551 1702323 := bstep (se 1 (by rfl) ⟨1276742, by rfl⟩ : syracuseStep 1702323 = 2553485) B2553485
theorem B2554289 : Blo 1701551 2554289 := bstep (se 2 (by rfl) ⟨957858, by rfl⟩ : syracuseStep 2554289 = 1915717) B1915717
theorem B1702339 : Blo 1701551 1702339 := bstep (se 1 (by rfl) ⟨1276754, by rfl⟩ : syracuseStep 1702339 = 2553509) B2553509
theorem B2554307 : Blo 1701551 2554307 := bstep (se 1 (by rfl) ⟨1915730, by rfl⟩ : syracuseStep 2554307 = 3831461) B3831461
theorem B1702355 : Blo 1701551 1702355 := bstep (se 1 (by rfl) ⟨1276766, by rfl⟩ : syracuseStep 1702355 = 2553533) B2553533
theorem B2554337 : Blo 1701551 2554337 := bstep (se 2 (by rfl) ⟨957876, by rfl⟩ : syracuseStep 2554337 = 1915753) B1915753
theorem B1702371 : Blo 1701551 1702371 := bstep (se 1 (by rfl) ⟨1276778, by rfl⟩ : syracuseStep 1702371 = 2553557) B2553557
theorem B4848113 : Blo 1701551 4848113 := bstep (se 2 (by rfl) ⟨1818042, by rfl⟩ : syracuseStep 4848113 = 3636085) B3636085
theorem B1702387 : Blo 1701551 1702387 := bstep (se 1 (by rfl) ⟨1276790, by rfl⟩ : syracuseStep 1702387 = 2553581) B2553581
theorem B2554355 : Blo 1701551 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B2423299 : Blo 1701551 2423299 := bstep (se 1 (by rfl) ⟨1817474, by rfl⟩ : syracuseStep 2423299 = 3634949) B3634949
theorem B1702403 : Blo 1701551 1702403 := bstep (se 1 (by rfl) ⟨1276802, by rfl⟩ : syracuseStep 1702403 = 2553605) B2553605
theorem B2554385 : Blo 1701551 2554385 := bstep (se 2 (by rfl) ⟨957894, by rfl⟩ : syracuseStep 2554385 = 1915789) B1915789
theorem B2873873 : Blo 1701551 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1702419 : Blo 1701551 1702419 := bstep (se 1 (by rfl) ⟨1276814, by rfl⟩ : syracuseStep 1702419 = 2553629) B2553629
theorem B1915411 : Blo 1701551 1915411 := bstep (se 1 (by rfl) ⟨1436558, by rfl⟩ : syracuseStep 1915411 = 2873117) B2873117
theorem B1702435 : Blo 1701551 1702435 := bstep (se 1 (by rfl) ⟨1276826, by rfl⟩ : syracuseStep 1702435 = 2553653) B2553653
theorem B5454371 : Blo 1701551 5454371 := bstep (se 1 (by rfl) ⟨4090778, by rfl⟩ : syracuseStep 5454371 = 8181557) B8181557
theorem B2554403 : Blo 1701551 2554403 := bstep (se 1 (by rfl) ⟨1915802, by rfl⟩ : syracuseStep 2554403 = 3831605) B3831605
theorem B1702451 : Blo 1701551 1702451 := bstep (se 1 (by rfl) ⟨1276838, by rfl⟩ : syracuseStep 1702451 = 2553677) B2553677
theorem B2554433 : Blo 1701551 2554433 := bstep (se 2 (by rfl) ⟨957912, by rfl⟩ : syracuseStep 2554433 = 1915825) B1915825
theorem B1702467 : Blo 1701551 1702467 := bstep (se 1 (by rfl) ⟨1276850, by rfl⟩ : syracuseStep 1702467 = 2553701) B2553701
theorem B5749325 : Blo 1701551 5749325 := bstep (se 3 (by rfl) ⟨1077998, by rfl⟩ : syracuseStep 5749325 = 2155997) B2155997
theorem B1702483 : Blo 1701551 1702483 := bstep (se 1 (by rfl) ⟨1276862, by rfl⟩ : syracuseStep 1702483 = 2553725) B2553725
theorem B2554451 : Blo 1701551 2554451 := bstep (se 1 (by rfl) ⟨1915838, by rfl⟩ : syracuseStep 2554451 = 3831677) B3831677
theorem B1702499 : Blo 1701551 1702499 := bstep (se 1 (by rfl) ⟨1276874, by rfl⟩ : syracuseStep 1702499 = 2553749) B2553749
theorem B2554481 : Blo 1701551 2554481 := bstep (se 2 (by rfl) ⟨957930, by rfl⟩ : syracuseStep 2554481 = 1915861) B1915861
theorem B1702515 : Blo 1701551 1702515 := bstep (se 1 (by rfl) ⟨1276886, by rfl⟩ : syracuseStep 1702515 = 2553773) B2553773
theorem B3832433 : Blo 1701551 3832433 := bstep (se 2 (by rfl) ⟨1437162, by rfl⟩ : syracuseStep 3832433 = 2874325) B2874325
theorem B1702531 : Blo 1701551 1702531 := bstep (se 1 (by rfl) ⟨1276898, by rfl⟩ : syracuseStep 1702531 = 2553797) B2553797
theorem B2554499 : Blo 1701551 2554499 := bstep (se 1 (by rfl) ⟨1915874, by rfl⟩ : syracuseStep 2554499 = 3831749) B3831749
theorem B3832451 : Blo 1701551 3832451 := bstep (se 1 (by rfl) ⟨2874338, by rfl⟩ : syracuseStep 3832451 = 5748677) B5748677
theorem B5749379 : Blo 1701551 5749379 := bstep (se 1 (by rfl) ⟨4312034, by rfl⟩ : syracuseStep 5749379 = 8624069) B8624069
theorem B10500749 : Blo 1701551 10500749 := bstep (se 3 (by rfl) ⟨1968890, by rfl⟩ : syracuseStep 10500749 = 3937781) B3937781
theorem B2874001 : Blo 1701551 2874001 := bstep (se 2 (by rfl) ⟨1077750, by rfl⟩ : syracuseStep 2874001 = 2155501) B2155501
theorem B1702547 : Blo 1701551 1702547 := bstep (se 1 (by rfl) ⟨1276910, by rfl⟩ : syracuseStep 1702547 = 2553821) B2553821
theorem B2554529 : Blo 1701551 2554529 := bstep (se 2 (by rfl) ⟨957948, by rfl⟩ : syracuseStep 2554529 = 1915897) B1915897
theorem B1702563 : Blo 1701551 1702563 := bstep (se 1 (by rfl) ⟨1276922, by rfl⟩ : syracuseStep 1702563 = 2553845) B2553845
theorem B5454499 : Blo 1701551 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B1915555 : Blo 1701551 1915555 := bstep (se 1 (by rfl) ⟨1436666, by rfl⟩ : syracuseStep 1915555 = 2873333) B2873333
theorem B1702579 : Blo 1701551 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B2554547 : Blo 1701551 2554547 := bstep (se 1 (by rfl) ⟨1915910, by rfl⟩ : syracuseStep 2554547 = 3831821) B3831821
theorem B2874035 : Blo 1701551 2874035 := bstep (se 1 (by rfl) ⟨2155526, by rfl⟩ : syracuseStep 2874035 = 4311053) B4311053
theorem B4307651 : Blo 1701551 4307651 := bstep (se 1 (by rfl) ⟨3230738, by rfl⟩ : syracuseStep 4307651 = 6461477) B6461477
theorem B1702595 : Blo 1701551 1702595 := bstep (se 1 (by rfl) ⟨1276946, by rfl⟩ : syracuseStep 1702595 = 2553893) B2553893
theorem B2554577 : Blo 1701551 2554577 := bstep (se 2 (by rfl) ⟨957966, by rfl⟩ : syracuseStep 2554577 = 1915933) B1915933
theorem B1702611 : Blo 1701551 1702611 := bstep (se 1 (by rfl) ⟨1276958, by rfl⟩ : syracuseStep 1702611 = 2553917) B2553917
theorem B1702627 : Blo 1701551 1702627 := bstep (se 1 (by rfl) ⟨1276970, by rfl⟩ : syracuseStep 1702627 = 2553941) B2553941
theorem B2554595 : Blo 1701551 2554595 := bstep (se 1 (by rfl) ⟨1915946, by rfl⟩ : syracuseStep 2554595 = 3831893) B3831893
theorem B1702643 : Blo 1701551 1702643 := bstep (se 1 (by rfl) ⟨1276982, by rfl⟩ : syracuseStep 1702643 = 2553965) B2553965
theorem B2554625 : Blo 1701551 2554625 := bstep (se 2 (by rfl) ⟨957984, by rfl⟩ : syracuseStep 2554625 = 1915969) B1915969
theorem B1702659 : Blo 1701551 1702659 := bstep (se 1 (by rfl) ⟨1276994, by rfl⟩ : syracuseStep 1702659 = 2553989) B2553989
theorem B1817363 : Blo 1701551 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B1702675 : Blo 1701551 1702675 := bstep (se 1 (by rfl) ⟨1277006, by rfl⟩ : syracuseStep 1702675 = 2554013) B2554013
theorem B2554643 : Blo 1701551 2554643 := bstep (se 1 (by rfl) ⟨1915982, by rfl⟩ : syracuseStep 2554643 = 3831965) B3831965
theorem B1702691 : Blo 1701551 1702691 := bstep (se 1 (by rfl) ⟨1277018, by rfl⟩ : syracuseStep 1702691 = 2554037) B2554037
theorem B5454641 : Blo 1701551 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B2554673 : Blo 1701551 2554673 := bstep (se 2 (by rfl) ⟨958002, by rfl⟩ : syracuseStep 2554673 = 1916005) B1916005
theorem B1702707 : Blo 1701551 1702707 := bstep (se 1 (by rfl) ⟨1277030, by rfl⟩ : syracuseStep 1702707 = 2554061) B2554061
theorem B1915699 : Blo 1701551 1915699 := bstep (se 1 (by rfl) ⟨1436774, by rfl⟩ : syracuseStep 1915699 = 2873549) B2873549
theorem B2874163 : Blo 1701551 2874163 := bstep (se 1 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 2874163 = 4311245) B4311245
theorem B1702723 : Blo 1701551 1702723 := bstep (se 1 (by rfl) ⟨1277042, by rfl⟩ : syracuseStep 1702723 = 2554085) B2554085
theorem B2554691 : Blo 1701551 2554691 := bstep (se 1 (by rfl) ⟨1916018, by rfl⟩ : syracuseStep 2554691 = 3832037) B3832037
theorem B10910533 : Blo 1701551 10910533 := bstep (se 4 (by rfl) ⟨1022862, by rfl⟩ : syracuseStep 10910533 = 2045725) B2045725
theorem B1702739 : Blo 1701551 1702739 := bstep (se 1 (by rfl) ⟨1277054, by rfl⟩ : syracuseStep 1702739 = 2554109) B2554109
theorem B2554721 : Blo 1701551 2554721 := bstep (se 2 (by rfl) ⟨958020, by rfl⟩ : syracuseStep 2554721 = 1916041) B1916041
theorem B1702755 : Blo 1701551 1702755 := bstep (se 1 (by rfl) ⟨1277066, by rfl⟩ : syracuseStep 1702755 = 2554133) B2554133
theorem B1702771 : Blo 1701551 1702771 := bstep (se 1 (by rfl) ⟨1277078, by rfl⟩ : syracuseStep 1702771 = 2554157) B2554157
theorem B2554739 : Blo 1701551 2554739 := bstep (se 1 (by rfl) ⟨1916054, by rfl⟩ : syracuseStep 2554739 = 3832109) B3832109
theorem B4307843 : Blo 1701551 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B1702787 : Blo 1701551 1702787 := bstep (se 1 (by rfl) ⟨1277090, by rfl⟩ : syracuseStep 1702787 = 2554181) B2554181
theorem B2554769 : Blo 1701551 2554769 := bstep (se 2 (by rfl) ⟨958038, by rfl⟩ : syracuseStep 2554769 = 1916077) B1916077
theorem B1702803 : Blo 1701551 1702803 := bstep (se 1 (by rfl) ⟨1277102, by rfl⟩ : syracuseStep 1702803 = 2554205) B2554205
theorem B3832721 : Blo 1701551 3832721 := bstep (se 2 (by rfl) ⟨1437270, by rfl⟩ : syracuseStep 3832721 = 2874541) B2874541
theorem B5454755 : Blo 1701551 5454755 := bstep (se 1 (by rfl) ⟨4091066, by rfl⟩ : syracuseStep 5454755 = 8182133) B8182133
theorem B1702819 : Blo 1701551 1702819 := bstep (se 1 (by rfl) ⟨1277114, by rfl⟩ : syracuseStep 1702819 = 2554229) B2554229
theorem B2554787 : Blo 1701551 2554787 := bstep (se 1 (by rfl) ⟨1916090, by rfl⟩ : syracuseStep 2554787 = 3832181) B3832181
theorem B3832739 : Blo 1701551 3832739 := bstep (se 1 (by rfl) ⟨2874554, by rfl⟩ : syracuseStep 3832739 = 5749109) B5749109
theorem B1702835 : Blo 1701551 1702835 := bstep (se 1 (by rfl) ⟨1277126, by rfl⟩ : syracuseStep 1702835 = 2554253) B2554253
theorem B2554817 : Blo 1701551 2554817 := bstep (se 2 (by rfl) ⟨958056, by rfl⟩ : syracuseStep 2554817 = 1916113) B1916113
theorem B1702851 : Blo 1701551 1702851 := bstep (se 1 (by rfl) ⟨1277138, by rfl⟩ : syracuseStep 1702851 = 2554277) B2554277
theorem B1915843 : Blo 1701551 1915843 := bstep (se 1 (by rfl) ⟨1436882, by rfl⟩ : syracuseStep 1915843 = 2873765) B2873765
theorem B23305157 : Blo 1701551 23305157 := bstep (se 4 (by rfl) ⟨2184858, by rfl⟩ : syracuseStep 23305157 = 4369717) B4369717
theorem B2874305 : Blo 1701551 2874305 := bstep (se 2 (by rfl) ⟨1077864, by rfl⟩ : syracuseStep 2874305 = 2155729) B2155729
theorem B1702867 : Blo 1701551 1702867 := bstep (se 1 (by rfl) ⟨1277150, by rfl⟩ : syracuseStep 1702867 = 2554301) B2554301
theorem B2554835 : Blo 1701551 2554835 := bstep (se 1 (by rfl) ⟨1916126, by rfl⟩ : syracuseStep 2554835 = 3832253) B3832253
theorem B1702883 : Blo 1701551 1702883 := bstep (se 1 (by rfl) ⟨1277162, by rfl⟩ : syracuseStep 1702883 = 2554325) B2554325
theorem B6462449 : Blo 1701551 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B3881969 : Blo 1701551 3881969 := bstep (se 2 (by rfl) ⟨1455738, by rfl⟩ : syracuseStep 3881969 = 2911477) B2911477
theorem B1702899 : Blo 1701551 1702899 := bstep (se 1 (by rfl) ⟨1277174, by rfl⟩ : syracuseStep 1702899 = 2554349) B2554349
theorem B2554865 : Blo 1701551 2554865 := bstep (se 2 (by rfl) ⟨958074, by rfl⟩ : syracuseStep 2554865 = 1916149) B1916149
theorem B1702915 : Blo 1701551 1702915 := bstep (se 1 (by rfl) ⟨1277186, by rfl⟩ : syracuseStep 1702915 = 2554373) B2554373
theorem B2554883 : Blo 1701551 2554883 := bstep (se 1 (by rfl) ⟨1916162, by rfl⟩ : syracuseStep 2554883 = 3832325) B3832325
theorem B1702931 : Blo 1701551 1702931 := bstep (se 1 (by rfl) ⟨1277198, by rfl⟩ : syracuseStep 1702931 = 2554397) B2554397
theorem B2554913 : Blo 1701551 2554913 := bstep (se 2 (by rfl) ⟨958092, by rfl⟩ : syracuseStep 2554913 = 1916185) B1916185
theorem B7765027 : Blo 1701551 7765027 := bstep (se 1 (by rfl) ⟨5823770, by rfl⟩ : syracuseStep 7765027 = 11647541) B11647541
theorem B1702947 : Blo 1701551 1702947 := bstep (se 1 (by rfl) ⟨1277210, by rfl⟩ : syracuseStep 1702947 = 2554421) B2554421
theorem B2423857 : Blo 1701551 2423857 := bstep (se 2 (by rfl) ⟨908946, by rfl⟩ : syracuseStep 2423857 = 1817893) B1817893
theorem B2300977 : Blo 1701551 2300977 := bstep (se 2 (by rfl) ⟨862866, by rfl⟩ : syracuseStep 2300977 = 1725733) B1725733
theorem B1702963 : Blo 1701551 1702963 := bstep (se 1 (by rfl) ⟨1277222, by rfl⟩ : syracuseStep 1702963 = 2554445) B2554445
theorem B2554931 : Blo 1701551 2554931 := bstep (se 1 (by rfl) ⟨1916198, by rfl⟩ : syracuseStep 2554931 = 3832397) B3832397
theorem B2874433 : Blo 1701551 2874433 := bstep (se 2 (by rfl) ⟨1077912, by rfl⟩ : syracuseStep 2874433 = 2155825) B2155825
theorem B1702979 : Blo 1701551 1702979 := bstep (se 1 (by rfl) ⟨1277234, by rfl⟩ : syracuseStep 1702979 = 2554469) B2554469
theorem B2726993 : Blo 1701551 2726993 := bstep (se 2 (by rfl) ⟨1022622, by rfl⟩ : syracuseStep 2726993 = 2045245) B2045245
theorem B2554961 : Blo 1701551 2554961 := bstep (se 2 (by rfl) ⟨958110, by rfl⟩ : syracuseStep 2554961 = 1916221) B1916221
theorem B2423891 : Blo 1701551 2423891 := bstep (se 1 (by rfl) ⟨1817918, by rfl⟩ : syracuseStep 2423891 = 3635837) B3635837
theorem B1702995 : Blo 1701551 1702995 := bstep (se 1 (by rfl) ⟨1277246, by rfl⟩ : syracuseStep 1702995 = 2554493) B2554493
theorem B1915987 : Blo 1701551 1915987 := bstep (se 1 (by rfl) ⟨1436990, by rfl⟩ : syracuseStep 1915987 = 2873981) B2873981
theorem B1703011 : Blo 1701551 1703011 := bstep (se 1 (by rfl) ⟨1277258, by rfl⟩ : syracuseStep 1703011 = 2554517) B2554517
theorem B2554979 : Blo 1701551 2554979 := bstep (se 1 (by rfl) ⟨1916234, by rfl⟩ : syracuseStep 2554979 = 3832469) B3832469
theorem B2874467 : Blo 1701551 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B1703027 : Blo 1701551 1703027 := bstep (se 1 (by rfl) ⟨1277270, by rfl⟩ : syracuseStep 1703027 = 2554541) B2554541
theorem B2555009 : Blo 1701551 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1703043 : Blo 1701551 1703043 := bstep (se 1 (by rfl) ⟨1277282, by rfl⟩ : syracuseStep 1703043 = 2554565) B2554565
theorem B4848785 : Blo 1701551 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B1703059 : Blo 1701551 1703059 := bstep (se 1 (by rfl) ⟨1277294, by rfl⟩ : syracuseStep 1703059 = 2554589) B2554589
theorem B2555027 : Blo 1701551 2555027 := bstep (se 1 (by rfl) ⟨1916270, by rfl⟩ : syracuseStep 2555027 = 3832541) B3832541
theorem B1703075 : Blo 1701551 1703075 := bstep (se 1 (by rfl) ⟨1277306, by rfl⟩ : syracuseStep 1703075 = 2554613) B2554613
theorem B5176493 : Blo 1701551 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B1703091 : Blo 1701551 1703091 := bstep (se 1 (by rfl) ⟨1277318, by rfl⟩ : syracuseStep 1703091 = 2554637) B2554637
theorem B2555057 : Blo 1701551 2555057 := bstep (se 2 (by rfl) ⟨958146, by rfl⟩ : syracuseStep 2555057 = 1916293) B1916293
theorem B1703107 : Blo 1701551 1703107 := bstep (se 1 (by rfl) ⟨1277330, by rfl⟩ : syracuseStep 1703107 = 2554661) B2554661
theorem B2555075 : Blo 1701551 2555075 := bstep (se 1 (by rfl) ⟨1916306, by rfl⟩ : syracuseStep 2555075 = 3832613) B3832613
theorem B2800849 : Blo 1701551 2800849 := bstep (se 2 (by rfl) ⟨1050318, by rfl⟩ : syracuseStep 2800849 = 2100637) B2100637
theorem B1703123 : Blo 1701551 1703123 := bstep (se 1 (by rfl) ⟨1277342, by rfl⟩ : syracuseStep 1703123 = 2554685) B2554685
theorem B2555105 : Blo 1701551 2555105 := bstep (se 2 (by rfl) ⟨958164, by rfl⟩ : syracuseStep 2555105 = 1916329) B1916329
theorem B1703139 : Blo 1701551 1703139 := bstep (se 1 (by rfl) ⟨1277354, by rfl⟩ : syracuseStep 1703139 = 2554709) B2554709
theorem B1916131 : Blo 1701551 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B5250275 : Blo 1701551 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B2874595 : Blo 1701551 2874595 := bstep (se 1 (by rfl) ⟨2155946, by rfl⟩ : syracuseStep 2874595 = 4311893) B4311893
theorem B1703155 : Blo 1701551 1703155 := bstep (se 1 (by rfl) ⟨1277366, by rfl⟩ : syracuseStep 1703155 = 2554733) B2554733
theorem B2555123 : Blo 1701551 2555123 := bstep (se 1 (by rfl) ⟨1916342, by rfl⟩ : syracuseStep 2555123 = 3832685) B3832685
theorem B1703171 : Blo 1701551 1703171 := bstep (se 1 (by rfl) ⟨1277378, by rfl⟩ : syracuseStep 1703171 = 2554757) B2554757
theorem B6905101 : Blo 1701551 6905101 := bstep (se 3 (by rfl) ⟨1294706, by rfl⟩ : syracuseStep 6905101 = 2589413) B2589413
theorem B2555153 : Blo 1701551 2555153 := bstep (se 2 (by rfl) ⟨958182, by rfl⟩ : syracuseStep 2555153 = 1916365) B1916365
theorem B1703187 : Blo 1701551 1703187 := bstep (se 1 (by rfl) ⟨1277390, by rfl⟩ : syracuseStep 1703187 = 2554781) B2554781
theorem B1703203 : Blo 1701551 1703203 := bstep (se 1 (by rfl) ⟨1277402, by rfl⟩ : syracuseStep 1703203 = 2554805) B2554805
theorem B2555171 : Blo 1701551 2555171 := bstep (se 1 (by rfl) ⟨1916378, by rfl⟩ : syracuseStep 2555171 = 3832757) B3832757
theorem B8617265 : Blo 1701551 8617265 := bstep (se 2 (by rfl) ⟨3231474, by rfl⟩ : syracuseStep 8617265 = 6462949) B6462949
theorem B1703219 : Blo 1701551 1703219 := bstep (se 1 (by rfl) ⟨1277414, by rfl⟩ : syracuseStep 1703219 = 2554829) B2554829
theorem B2555201 : Blo 1701551 2555201 := bstep (se 2 (by rfl) ⟨958200, by rfl⟩ : syracuseStep 2555201 = 1916401) B1916401
theorem B1703235 : Blo 1701551 1703235 := bstep (se 1 (by rfl) ⟨1277426, by rfl⟩ : syracuseStep 1703235 = 2554853) B2554853
theorem B1703251 : Blo 1701551 1703251 := bstep (se 1 (by rfl) ⟨1277438, by rfl⟩ : syracuseStep 1703251 = 2554877) B2554877
theorem B2555219 : Blo 1701551 2555219 := bstep (se 1 (by rfl) ⟨1916414, by rfl⟩ : syracuseStep 2555219 = 3832829) B3832829
theorem B1703267 : Blo 1701551 1703267 := bstep (se 1 (by rfl) ⟨1277450, by rfl⟩ : syracuseStep 1703267 = 2554901) B2554901
theorem B2555249 : Blo 1701551 2555249 := bstep (se 2 (by rfl) ⟨958218, by rfl⟩ : syracuseStep 2555249 = 1916437) B1916437
theorem B2874737 : Blo 1701551 2874737 := bstep (se 2 (by rfl) ⟨1078026, by rfl⟩ : syracuseStep 2874737 = 2156053) B2156053
theorem B1703283 : Blo 1701551 1703283 := bstep (se 1 (by rfl) ⟨1277462, by rfl⟩ : syracuseStep 1703283 = 2554925) B2554925
theorem B1916275 : Blo 1701551 1916275 := bstep (se 1 (by rfl) ⟨1437206, by rfl⟩ : syracuseStep 1916275 = 2874413) B2874413
theorem B1703299 : Blo 1701551 1703299 := bstep (se 1 (by rfl) ⟨1277474, by rfl⟩ : syracuseStep 1703299 = 2554949) B2554949
theorem B2555267 : Blo 1701551 2555267 := bstep (se 1 (by rfl) ⟨1916450, by rfl⟩ : syracuseStep 2555267 = 3832901) B3832901
theorem B2588051 : Blo 1701551 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B1703315 : Blo 1701551 1703315 := bstep (se 1 (by rfl) ⟨1277486, by rfl⟩ : syracuseStep 1703315 = 2554973) B2554973
theorem B2555297 : Blo 1701551 2555297 := bstep (se 2 (by rfl) ⟨958236, by rfl⟩ : syracuseStep 2555297 = 1916473) B1916473
theorem B2153891 : Blo 1701551 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B6135203 : Blo 1701551 6135203 := bstep (se 1 (by rfl) ⟨4601402, by rfl⟩ : syracuseStep 6135203 = 9202805) B9202805
theorem B1703331 : Blo 1701551 1703331 := bstep (se 1 (by rfl) ⟨1277498, by rfl⟩ : syracuseStep 1703331 = 2554997) B2554997
theorem B1703347 : Blo 1701551 1703347 := bstep (se 1 (by rfl) ⟨1277510, by rfl⟩ : syracuseStep 1703347 = 2555021) B2555021
theorem B2555315 : Blo 1701551 2555315 := bstep (se 1 (by rfl) ⟨1916486, by rfl⟩ : syracuseStep 2555315 = 3832973) B3832973
theorem B1703363 : Blo 1701551 1703363 := bstep (se 1 (by rfl) ⟨1277522, by rfl⟩ : syracuseStep 1703363 = 2555045) B2555045
theorem B1703379 : Blo 1701551 1703379 := bstep (se 1 (by rfl) ⟨1277534, by rfl⟩ : syracuseStep 1703379 = 2555069) B2555069
theorem B1703395 : Blo 1701551 1703395 := bstep (se 1 (by rfl) ⟨1277546, by rfl⟩ : syracuseStep 1703395 = 2555093) B2555093
theorem B1703411 : Blo 1701551 1703411 := bstep (se 1 (by rfl) ⟨1277558, by rfl⟩ : syracuseStep 1703411 = 2555117) B2555117
theorem B2588161 : Blo 1701551 2588161 := bstep (se 2 (by rfl) ⟨970560, by rfl⟩ : syracuseStep 2588161 = 1941121) B1941121
theorem B1703427 : Blo 1701551 1703427 := bstep (se 1 (by rfl) ⟨1277570, by rfl⟩ : syracuseStep 1703427 = 2555141) B2555141
theorem B1916419 : Blo 1701551 1916419 := bstep (se 1 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 1916419 = 2874629) B2874629
theorem B1703443 : Blo 1701551 1703443 := bstep (se 1 (by rfl) ⟨1277582, by rfl⟩ : syracuseStep 1703443 = 2555165) B2555165
theorem B2072099 : Blo 1701551 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B1703459 : Blo 1701551 1703459 := bstep (se 1 (by rfl) ⟨1277594, by rfl⟩ : syracuseStep 1703459 = 2555189) B2555189
theorem B1703475 : Blo 1701551 1703475 := bstep (se 1 (by rfl) ⟨1277606, by rfl⟩ : syracuseStep 1703475 = 2555213) B2555213
theorem B1703491 : Blo 1701551 1703491 := bstep (se 1 (by rfl) ⟨1277618, by rfl⟩ : syracuseStep 1703491 = 2555237) B2555237
theorem B1703507 : Blo 1701551 1703507 := bstep (se 1 (by rfl) ⟨1277630, by rfl⟩ : syracuseStep 1703507 = 2555261) B2555261
theorem B7274083 : Blo 1701551 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B1703523 : Blo 1701551 1703523 := bstep (se 1 (by rfl) ⟨1277642, by rfl⟩ : syracuseStep 1703523 = 2555285) B2555285
theorem B1703539 : Blo 1701551 1703539 := bstep (se 1 (by rfl) ⟨1277654, by rfl⟩ : syracuseStep 1703539 = 2555309) B2555309
theorem B2424449 : Blo 1701551 2424449 := bstep (se 2 (by rfl) ⟨909168, by rfl⟩ : syracuseStep 2424449 = 1818337) B1818337
theorem B2301571 : Blo 1701551 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3636913 : Blo 1701551 3636913 := bstep (se 2 (by rfl) ⟨1363842, by rfl⟩ : syracuseStep 3636913 = 2727685) B2727685
theorem B2129603 : Blo 1701551 2129603 := bstep (se 1 (by rfl) ⟨1597202, by rfl⟩ : syracuseStep 2129603 = 3194405) B3194405
theorem B2424529 : Blo 1701551 2424529 := bstep (se 2 (by rfl) ⟨909198, by rfl⟩ : syracuseStep 2424529 = 1818397) B1818397
theorem B21806819 : Blo 1701551 21806819 := bstep (se 1 (by rfl) ⟨16355114, by rfl⟩ : syracuseStep 21806819 = 32710229) B32710229
theorem B41434901 : Blo 1701551 41434901 := bstep (se 6 (by rfl) ⟨971130, by rfl⟩ : syracuseStep 41434901 = 1942261) B1942261
theorem B4308785 : Blo 1701551 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B2727731 : Blo 1701551 2727731 := bstep (se 1 (by rfl) ⟨2045798, by rfl⟩ : syracuseStep 2727731 = 4091597) B4091597
theorem B4308835 : Blo 1701551 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B4849571 : Blo 1701551 4849571 := bstep (se 1 (by rfl) ⟨3637178, by rfl⟩ : syracuseStep 4849571 = 7274357) B7274357
theorem B4308977 : Blo 1701551 4308977 := bstep (se 2 (by rfl) ⟨1615866, by rfl⟩ : syracuseStep 4308977 = 3231733) B3231733
theorem B15532067 : Blo 1701551 15532067 := bstep (se 1 (by rfl) ⟨11649050, by rfl⟩ : syracuseStep 15532067 = 23298101) B23298101
theorem B4849753 : Blo 1701551 4849753 := bstep (se 2 (by rfl) ⟨1818657, by rfl⟩ : syracuseStep 4849753 = 3637315) B3637315
theorem B6463709 : Blo 1701551 6463709 := bstep (se 3 (by rfl) ⟨1211945, by rfl⟩ : syracuseStep 6463709 = 2423891) B2423891
theorem B39829765 : Blo 1701551 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B4309271 : Blo 1701551 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B3989783 : Blo 1701551 3989783 := bstep (se 1 (by rfl) ⟨2992337, by rfl⟩ : syracuseStep 3989783 = 5984675) B5984675
theorem B5742899 : Blo 1701551 5742899 := bstep (se 1 (by rfl) ⟨4307174, by rfl⟩ : syracuseStep 5742899 = 8614349) B8614349
theorem B3686743 : Blo 1701551 3686743 := bstep (se 1 (by rfl) ⟨2765057, by rfl⟩ : syracuseStep 3686743 = 5530115) B5530115
theorem B2425241 : Blo 1701551 2425241 := bstep (se 2 (by rfl) ⟨909465, by rfl⟩ : syracuseStep 2425241 = 1818931) B1818931
theorem B18407897 : Blo 1701551 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B7094749 : Blo 1701551 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B5743169 : Blo 1701551 5743169 := bstep (se 2 (by rfl) ⟨2153688, by rfl⟩ : syracuseStep 5743169 = 4307377) B4307377
theorem B8618561 : Blo 1701551 8618561 := bstep (se 2 (by rfl) ⟨3231960, by rfl⟩ : syracuseStep 8618561 = 6463921) B6463921
theorem B7766617 : Blo 1701551 7766617 := bstep (se 2 (by rfl) ⟨2912481, by rfl⟩ : syracuseStep 7766617 = 5824963) B5824963
theorem B59007797 : Blo 1701551 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B7275329 : Blo 1701551 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B2155339 : Blo 1701551 2155339 := bstep (se 1 (by rfl) ⟨1616504, by rfl⟩ : syracuseStep 2155339 = 3233009) B3233009
theorem B6464407 : Blo 1701551 6464407 := bstep (se 1 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 6464407 = 9696611) B9696611
theorem B3638297 : Blo 1701551 3638297 := bstep (se 2 (by rfl) ⟨1364361, by rfl⟩ : syracuseStep 3638297 = 2728723) B2728723
theorem B10495021 : Blo 1701551 10495021 := bstep (se 3 (by rfl) ⟨1967816, by rfl⟩ : syracuseStep 10495021 = 3935633) B3935633
theorem B4310081 : Blo 1701551 4310081 := bstep (se 2 (by rfl) ⟨1616280, by rfl⟩ : syracuseStep 4310081 = 3232561) B3232561
theorem B5743709 : Blo 1701551 5743709 := bstep (se 3 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 5743709 = 2153891) B2153891
theorem B24536195 : Blo 1701551 24536195 := bstep (se 1 (by rfl) ⟨18402146, by rfl⟩ : syracuseStep 24536195 = 36804293) B36804293
theorem B3278027 : Blo 1701551 3278027 := bstep (se 1 (by rfl) ⟨2458520, by rfl⟩ : syracuseStep 3278027 = 4917041) B4917041
theorem B7374041 : Blo 1701551 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B5457203 : Blo 1701551 5457203 := bstep (se 1 (by rfl) ⟨4092902, by rfl⟩ : syracuseStep 5457203 = 8185805) B8185805
theorem B11642291 : Blo 1701551 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B4310617 : Blo 1701551 4310617 := bstep (se 2 (by rfl) ⟨1616481, by rfl⟩ : syracuseStep 4310617 = 3232963) B3232963
theorem B6465197 : Blo 1701551 6465197 := bstep (se 3 (by rfl) ⟨1212224, by rfl⟩ : syracuseStep 6465197 = 2424449) B2424449
theorem B9692945 : Blo 1701551 9692945 := bstep (se 2 (by rfl) ⟨3634854, by rfl⟩ : syracuseStep 9692945 = 7269709) B7269709
theorem B19384109 : Blo 1701551 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B6899507 : Blo 1701551 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B2951063 : Blo 1701551 2951063 := bstep (se 1 (by rfl) ⟨2213297, by rfl⟩ : syracuseStep 2951063 = 4426595) B4426595
theorem B14551001 : Blo 1701551 14551001 := bstep (se 2 (by rfl) ⟨5456625, by rfl⟩ : syracuseStep 14551001 = 10913251) B10913251
theorem B3450881 : Blo 1701551 3450881 := bstep (se 2 (by rfl) ⟨1294080, by rfl⟩ : syracuseStep 3450881 = 2588161) B2588161
theorem B9701441 : Blo 1701551 9701441 := bstep (se 2 (by rfl) ⟨3638040, by rfl⟩ : syracuseStep 9701441 = 7276081) B7276081
theorem B3450995 : Blo 1701551 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B3500183 : Blo 1701551 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B5744843 : Blo 1701551 5744843 := bstep (se 1 (by rfl) ⟨4308632, by rfl⟩ : syracuseStep 5744843 = 8617265) B8617265
theorem B5245145 : Blo 1701551 5245145 := bstep (se 2 (by rfl) ⟨1966929, by rfl⟩ : syracuseStep 5245145 = 3933859) B3933859
theorem B4090135 : Blo 1701551 4090135 := bstep (se 1 (by rfl) ⟨3067601, by rfl⟩ : syracuseStep 4090135 = 6135203) B6135203
theorem B5179799 : Blo 1701551 5179799 := bstep (se 1 (by rfl) ⟨3884849, by rfl⟩ : syracuseStep 5179799 = 7769699) B7769699
theorem B5745113 : Blo 1701551 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B8620505 : Blo 1701551 8620505 := bstep (se 2 (by rfl) ⟨3232689, by rfl⟩ : syracuseStep 8620505 = 6465379) B6465379
theorem B5179993 : Blo 1701551 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B4311731 : Blo 1701551 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B3828491 : Blo 1701551 3828491 := bstep (se 1 (by rfl) ⟨2871368, by rfl⟩ : syracuseStep 3828491 = 5742737) B5742737
theorem B3828545 : Blo 1701551 3828545 := bstep (se 2 (by rfl) ⟨1435704, by rfl⟩ : syracuseStep 3828545 = 2871409) B2871409
theorem B10906433 : Blo 1701551 10906433 := bstep (se 2 (by rfl) ⟨4089912, by rfl⟩ : syracuseStep 10906433 = 8179825) B8179825
theorem B41413477 : Blo 1701551 41413477 := bstep (se 4 (by rfl) ⟨3882513, by rfl⟩ : syracuseStep 41413477 = 7765027) B7765027
theorem B3230579 : Blo 1701551 3230579 := bstep (se 1 (by rfl) ⟨2422934, by rfl⟩ : syracuseStep 3230579 = 4845869) B4845869
theorem B3230617 : Blo 1701551 3230617 := bstep (se 2 (by rfl) ⟨1211481, by rfl⟩ : syracuseStep 3230617 = 2422963) B2422963
theorem B31075289 : Blo 1701551 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B4312025 : Blo 1701551 4312025 := bstep (se 2 (by rfl) ⟨1617009, by rfl⟩ : syracuseStep 4312025 = 3234019) B3234019
theorem B3828761 : Blo 1701551 3828761 := bstep (se 2 (by rfl) ⟨1435785, by rfl⟩ : syracuseStep 3828761 = 2871571) B2871571
theorem B6466625 : Blo 1701551 6466625 := bstep (se 2 (by rfl) ⟨2424984, by rfl⟩ : syracuseStep 6466625 = 4849969) B4849969
theorem B3828851 : Blo 1701551 3828851 := bstep (se 1 (by rfl) ⟨2871638, by rfl⟩ : syracuseStep 3828851 = 5743277) B5743277
theorem B11209859 : Blo 1701551 11209859 := bstep (se 1 (by rfl) ⟨8407394, by rfl⟩ : syracuseStep 11209859 = 16814789) B16814789
theorem B3828887 : Blo 1701551 3828887 := bstep (se 1 (by rfl) ⟨2871665, by rfl⟩ : syracuseStep 3828887 = 5743331) B5743331
theorem B5745815 : Blo 1701551 5745815 := bstep (se 1 (by rfl) ⟨4309361, by rfl⟩ : syracuseStep 5745815 = 8618723) B8618723
theorem B3829067 : Blo 1701551 3829067 := bstep (se 1 (by rfl) ⟨2871800, by rfl⟩ : syracuseStep 3829067 = 5743601) B5743601
theorem B3231065 : Blo 1701551 3231065 := bstep (se 2 (by rfl) ⟨1211649, by rfl⟩ : syracuseStep 3231065 = 2423299) B2423299
theorem B7269725 : Blo 1701551 7269725 := bstep (se 3 (by rfl) ⟨1363073, by rfl⟩ : syracuseStep 7269725 = 2726147) B2726147
theorem B3829121 : Blo 1701551 3829121 := bstep (se 2 (by rfl) ⟨1435920, by rfl⟩ : syracuseStep 3829121 = 2871841) B2871841
theorem B3108439 : Blo 1701551 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B3829337 : Blo 1701551 3829337 := bstep (se 2 (by rfl) ⟨1436001, by rfl⟩ : syracuseStep 3829337 = 2872003) B2872003
theorem B3067507 : Blo 1701551 3067507 := bstep (se 1 (by rfl) ⟨2300630, by rfl⟩ : syracuseStep 3067507 = 4601261) B4601261
theorem B7270033 : Blo 1701551 7270033 := bstep (se 2 (by rfl) ⟨2726262, by rfl⟩ : syracuseStep 7270033 = 5452525) B5452525
theorem B3829427 : Blo 1701551 3829427 := bstep (se 1 (by rfl) ⟨2872070, by rfl⟩ : syracuseStep 3829427 = 5744141) B5744141
theorem B7270067 : Blo 1701551 7270067 := bstep (se 1 (by rfl) ⟨5452550, by rfl⟩ : syracuseStep 7270067 = 10905101) B10905101
theorem B5746355 : Blo 1701551 5746355 := bstep (se 1 (by rfl) ⟨4309766, by rfl⟩ : syracuseStep 5746355 = 8619533) B8619533
theorem B3829463 : Blo 1701551 3829463 := bstep (se 1 (by rfl) ⟨2872097, by rfl⟩ : syracuseStep 3829463 = 5744195) B5744195
theorem B3452633 : Blo 1701551 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B6901469 : Blo 1701551 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B36802289 : Blo 1701551 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B8179501 : Blo 1701551 8179501 := bstep (se 3 (by rfl) ⟨1533656, by rfl⟩ : syracuseStep 8179501 = 3067313) B3067313
theorem B3067723 : Blo 1701551 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B3829643 : Blo 1701551 3829643 := bstep (se 1 (by rfl) ⟨2872232, by rfl⟩ : syracuseStep 3829643 = 5744465) B5744465
theorem B3829697 : Blo 1701551 3829697 := bstep (se 2 (by rfl) ⟨1436136, by rfl⟩ : syracuseStep 3829697 = 2872273) B2872273
theorem B5746625 : Blo 1701551 5746625 := bstep (se 2 (by rfl) ⟨2154984, by rfl⟩ : syracuseStep 5746625 = 4309969) B4309969
theorem B2912215 : Blo 1701551 2912215 := bstep (se 1 (by rfl) ⟨2184161, by rfl⟩ : syracuseStep 2912215 = 4368323) B4368323
theorem B8622125 : Blo 1701551 8622125 := bstep (se 3 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 8622125 = 3233297) B3233297
theorem B3231809 : Blo 1701551 3231809 := bstep (se 2 (by rfl) ⟨1211928, by rfl⟩ : syracuseStep 3231809 = 2423857) B2423857
theorem B3067969 : Blo 1701551 3067969 := bstep (se 2 (by rfl) ⟨1150488, by rfl⟩ : syracuseStep 3067969 = 2300977) B2300977
theorem B5525597 : Blo 1701551 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B3829913 : Blo 1701551 3829913 := bstep (se 2 (by rfl) ⟨1436217, by rfl⟩ : syracuseStep 3829913 = 2872435) B2872435
theorem B3830003 : Blo 1701551 3830003 := bstep (se 1 (by rfl) ⟨2872502, by rfl⟩ : syracuseStep 3830003 = 5745005) B5745005
theorem B3830039 : Blo 1701551 3830039 := bstep (se 1 (by rfl) ⟨2872529, by rfl⟩ : syracuseStep 3830039 = 5745059) B5745059
theorem B49746221 : Blo 1701551 49746221 := bstep (se 3 (by rfl) ⟨9327416, by rfl⟩ : syracuseStep 49746221 = 18654833) B18654833
theorem B4600115 : Blo 1701551 4600115 := bstep (se 1 (by rfl) ⟨3450086, by rfl⟩ : syracuseStep 4600115 = 6900173) B6900173
theorem B4092211 : Blo 1701551 4092211 := bstep (se 1 (by rfl) ⟨3069158, by rfl⟩ : syracuseStep 4092211 = 6138317) B6138317
theorem B3232075 : Blo 1701551 3232075 := bstep (se 1 (by rfl) ⟨2424056, by rfl⟩ : syracuseStep 3232075 = 4848113) B4848113
theorem B7000499 : Blo 1701551 7000499 := bstep (se 1 (by rfl) ⟨5250374, by rfl⟩ : syracuseStep 7000499 = 10500749) B10500749
theorem B3830219 : Blo 1701551 3830219 := bstep (se 1 (by rfl) ⟨2872664, by rfl⟩ : syracuseStep 3830219 = 5745329) B5745329
theorem B2871767 : Blo 1701551 2871767 := bstep (se 1 (by rfl) ⟨2153825, by rfl⟩ : syracuseStep 2871767 = 4307651) B4307651
theorem B5747165 : Blo 1701551 5747165 := bstep (se 3 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 5747165 = 2155187) B2155187
theorem B3830273 : Blo 1701551 3830273 := bstep (se 2 (by rfl) ⟨1436352, by rfl⟩ : syracuseStep 3830273 = 2872705) B2872705
theorem B6468113 : Blo 1701551 6468113 := bstep (se 2 (by rfl) ⟨2425542, by rfl⟩ : syracuseStep 6468113 = 4851085) B4851085
theorem B2552345 : Blo 1701551 2552345 := bstep (se 2 (by rfl) ⟨957129, by rfl⟩ : syracuseStep 2552345 = 1914259) B1914259
theorem B2871895 : Blo 1701551 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B15536771 : Blo 1701551 15536771 := bstep (se 1 (by rfl) ⟨11652578, by rfl⟩ : syracuseStep 15536771 = 23305157) B23305157
theorem B2552459 : Blo 1701551 2552459 := bstep (se 1 (by rfl) ⟨1914344, by rfl⟩ : syracuseStep 2552459 = 3828689) B3828689
theorem B2552471 : Blo 1701551 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B2552537 : Blo 1701551 2552537 := bstep (se 2 (by rfl) ⟨957201, by rfl⟩ : syracuseStep 2552537 = 1914403) B1914403
theorem B3830489 : Blo 1701551 3830489 := bstep (se 2 (by rfl) ⟨1436433, by rfl⟩ : syracuseStep 3830489 = 2872867) B2872867
theorem B4846301 : Blo 1701551 4846301 := bstep (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) B1817363
theorem B3232523 : Blo 1701551 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B8614673 : Blo 1701551 8614673 := bstep (se 2 (by rfl) ⟨3230502, by rfl⟩ : syracuseStep 8614673 = 6461005) B6461005
theorem B2913049 : Blo 1701551 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B3830579 : Blo 1701551 3830579 := bstep (se 1 (by rfl) ⟨2872934, by rfl⟩ : syracuseStep 3830579 = 5745869) B5745869
theorem B2552651 : Blo 1701551 2552651 := bstep (se 1 (by rfl) ⟨1914488, by rfl⟩ : syracuseStep 2552651 = 3828977) B3828977
theorem B2552663 : Blo 1701551 2552663 := bstep (se 1 (by rfl) ⟨1914497, by rfl⟩ : syracuseStep 2552663 = 3828995) B3828995
theorem B3830615 : Blo 1701551 3830615 := bstep (se 1 (by rfl) ⟨2872961, by rfl⟩ : syracuseStep 3830615 = 5745923) B5745923
theorem B3068761 : Blo 1701551 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B29487971 : Blo 1701551 29487971 := bstep (se 1 (by rfl) ⟨22115978, by rfl⟩ : syracuseStep 29487971 = 44231957) B44231957
theorem B2552729 : Blo 1701551 2552729 := bstep (se 2 (by rfl) ⟨957273, by rfl⟩ : syracuseStep 2552729 = 1914547) B1914547
theorem B8614835 : Blo 1701551 8614835 := bstep (se 1 (by rfl) ⟨6461126, by rfl⟩ : syracuseStep 8614835 = 12922253) B12922253
theorem B4846529 : Blo 1701551 4846529 := bstep (se 2 (by rfl) ⟨1817448, by rfl⟩ : syracuseStep 4846529 = 3634897) B3634897
theorem B3232705 : Blo 1701551 3232705 := bstep (se 2 (by rfl) ⟨1212264, by rfl⟩ : syracuseStep 3232705 = 2424529) B2424529
theorem B2552843 : Blo 1701551 2552843 := bstep (se 1 (by rfl) ⟨1914632, by rfl⟩ : syracuseStep 2552843 = 3829265) B3829265
theorem B3830795 : Blo 1701551 3830795 := bstep (se 1 (by rfl) ⟨2873096, by rfl⟩ : syracuseStep 3830795 = 5746193) B5746193
theorem B26219533 : Blo 1701551 26219533 := bstep (se 3 (by rfl) ⟨4916162, by rfl⟩ : syracuseStep 26219533 = 9832325) B9832325
theorem B2552855 : Blo 1701551 2552855 := bstep (se 1 (by rfl) ⟨1914641, by rfl⟩ : syracuseStep 2552855 = 3829283) B3829283
theorem B11646017 : Blo 1701551 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B3830849 : Blo 1701551 3830849 := bstep (se 2 (by rfl) ⟨1436568, by rfl⟩ : syracuseStep 3830849 = 2873137) B2873137
theorem B2552921 : Blo 1701551 2552921 := bstep (se 2 (by rfl) ⟨957345, by rfl⟩ : syracuseStep 2552921 = 1914691) B1914691
theorem B14537879 : Blo 1701551 14537879 := bstep (se 1 (by rfl) ⟨10903409, by rfl⟩ : syracuseStep 14537879 = 21806819) B21806819
theorem B2553035 : Blo 1701551 2553035 := bstep (se 1 (by rfl) ⟨1914776, by rfl⟩ : syracuseStep 2553035 = 3829553) B3829553
theorem B2872523 : Blo 1701551 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B2553047 : Blo 1701551 2553047 := bstep (se 1 (by rfl) ⟨1914785, by rfl⟩ : syracuseStep 2553047 = 3829571) B3829571
theorem B4846871 : Blo 1701551 4846871 := bstep (se 1 (by rfl) ⟨3635153, by rfl⟩ : syracuseStep 4846871 = 7270307) B7270307
theorem B3233047 : Blo 1701551 3233047 := bstep (se 1 (by rfl) ⟨2424785, by rfl⟩ : syracuseStep 3233047 = 4849571) B4849571
theorem B2553113 : Blo 1701551 2553113 := bstep (se 2 (by rfl) ⟨957417, by rfl⟩ : syracuseStep 2553113 = 1914835) B1914835
theorem B3831065 : Blo 1701551 3831065 := bstep (se 2 (by rfl) ⟨1436649, by rfl⟩ : syracuseStep 3831065 = 2873299) B2873299
theorem B2872651 : Blo 1701551 2872651 := bstep (se 1 (by rfl) ⟨2154488, by rfl⟩ : syracuseStep 2872651 = 4308977) B4308977
theorem B3831155 : Blo 1701551 3831155 := bstep (se 1 (by rfl) ⟨2873366, by rfl⟩ : syracuseStep 3831155 = 5746733) B5746733
theorem B2553227 : Blo 1701551 2553227 := bstep (se 1 (by rfl) ⟨1914920, by rfl⟩ : syracuseStep 2553227 = 3829841) B3829841
theorem B6460823 : Blo 1701551 6460823 := bstep (se 1 (by rfl) ⟨4845617, by rfl⟩ : syracuseStep 6460823 = 9691235) B9691235
theorem B2553239 : Blo 1701551 2553239 := bstep (se 1 (by rfl) ⟨1914929, by rfl⟩ : syracuseStep 2553239 = 3829859) B3829859
theorem B3831191 : Blo 1701551 3831191 := bstep (se 1 (by rfl) ⟨2873393, by rfl⟩ : syracuseStep 3831191 = 5746787) B5746787
theorem B1914295 : Blo 1701551 1914295 := bstep (se 1 (by rfl) ⟨1435721, by rfl⟩ : syracuseStep 1914295 = 2871443) B2871443
theorem B2553305 : Blo 1701551 2553305 := bstep (se 2 (by rfl) ⟨957489, by rfl⟩ : syracuseStep 2553305 = 1914979) B1914979
theorem B2872793 : Blo 1701551 2872793 := bstep (se 2 (by rfl) ⟨1077297, by rfl⟩ : syracuseStep 2872793 = 2154595) B2154595
theorem B3233267 : Blo 1701551 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B10909201 : Blo 1701551 10909201 := bstep (se 2 (by rfl) ⟨4090950, by rfl⟩ : syracuseStep 10909201 = 8181901) B8181901
theorem B7271981 : Blo 1701551 7271981 := bstep (se 3 (by rfl) ⟨1363496, by rfl⟩ : syracuseStep 7271981 = 2726993) B2726993
theorem B2553419 : Blo 1701551 2553419 := bstep (se 1 (by rfl) ⟨1915064, by rfl⟩ : syracuseStep 2553419 = 3830129) B3830129
theorem B3831371 : Blo 1701551 3831371 := bstep (se 1 (by rfl) ⟨2873528, by rfl⟩ : syracuseStep 3831371 = 5747057) B5747057
theorem B5748299 : Blo 1701551 5748299 := bstep (se 1 (by rfl) ⟨4311224, by rfl⟩ : syracuseStep 5748299 = 8622449) B8622449
theorem B2553431 : Blo 1701551 2553431 := bstep (se 1 (by rfl) ⟨1915073, by rfl⟩ : syracuseStep 2553431 = 3830147) B3830147
theorem B2872921 : Blo 1701551 2872921 := bstep (se 2 (by rfl) ⟨1077345, by rfl⟩ : syracuseStep 2872921 = 2154691) B2154691
theorem B1914475 : Blo 1701551 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B3831425 : Blo 1701551 3831425 := bstep (se 2 (by rfl) ⟨1436784, by rfl⟩ : syracuseStep 3831425 = 2873569) B2873569
theorem B3069569 : Blo 1701551 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B2553497 : Blo 1701551 2553497 := bstep (se 2 (by rfl) ⟨957561, by rfl⟩ : syracuseStep 2553497 = 1915123) B1915123
theorem B1701559 : Blo 1701551 1701559 := bstep (se 1 (by rfl) ⟨1276169, by rfl⟩ : syracuseStep 1701559 = 2552339) B2552339
theorem B1701579 : Blo 1701551 1701579 := bstep (se 1 (by rfl) ⟨1276184, by rfl⟩ : syracuseStep 1701579 = 2552369) B2552369
theorem B1701591 : Blo 1701551 1701591 := bstep (se 1 (by rfl) ⟨1276193, by rfl⟩ : syracuseStep 1701591 = 2552387) B2552387
theorem B1914583 : Blo 1701551 1914583 := bstep (se 1 (by rfl) ⟨1435937, by rfl⟩ : syracuseStep 1914583 = 2871875) B2871875
theorem B3233495 : Blo 1701551 3233495 := bstep (se 1 (by rfl) ⟨2425121, by rfl⟩ : syracuseStep 3233495 = 4850243) B4850243
theorem B1701611 : Blo 1701551 1701611 := bstep (se 1 (by rfl) ⟨1276208, by rfl⟩ : syracuseStep 1701611 = 2552417) B2552417
theorem B3634931 : Blo 1701551 3634931 := bstep (se 1 (by rfl) ⟨2726198, by rfl⟩ : syracuseStep 3634931 = 5452397) B5452397
theorem B1701623 : Blo 1701551 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B1701643 : Blo 1701551 1701643 := bstep (se 1 (by rfl) ⟨1276232, by rfl⟩ : syracuseStep 1701643 = 2552465) B2552465
theorem B2553611 : Blo 1701551 2553611 := bstep (se 1 (by rfl) ⟨1915208, by rfl⟩ : syracuseStep 2553611 = 3830417) B3830417
theorem B1701655 : Blo 1701551 1701655 := bstep (se 1 (by rfl) ⟨1276241, by rfl⟩ : syracuseStep 1701655 = 2552483) B2552483
theorem B2553623 : Blo 1701551 2553623 := bstep (se 1 (by rfl) ⟨1915217, by rfl⟩ : syracuseStep 2553623 = 3830435) B3830435
theorem B1701675 : Blo 1701551 1701675 := bstep (se 1 (by rfl) ⟨1276256, by rfl⟩ : syracuseStep 1701675 = 2552513) B2552513
theorem B1701687 : Blo 1701551 1701687 := bstep (se 1 (by rfl) ⟨1276265, by rfl⟩ : syracuseStep 1701687 = 2552531) B2552531
theorem B1701707 : Blo 1701551 1701707 := bstep (se 1 (by rfl) ⟨1276280, by rfl⟩ : syracuseStep 1701707 = 2552561) B2552561
theorem B1701719 : Blo 1701551 1701719 := bstep (se 1 (by rfl) ⟨1276289, by rfl⟩ : syracuseStep 1701719 = 2552579) B2552579
theorem B2045783 : Blo 1701551 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B2553689 : Blo 1701551 2553689 := bstep (se 2 (by rfl) ⟨957633, by rfl⟩ : syracuseStep 2553689 = 1915267) B1915267
theorem B3831641 : Blo 1701551 3831641 := bstep (se 2 (by rfl) ⟨1436865, by rfl⟩ : syracuseStep 3831641 = 2873731) B2873731
theorem B5748569 : Blo 1701551 5748569 := bstep (se 2 (by rfl) ⟨2155713, by rfl⟩ : syracuseStep 5748569 = 4311427) B4311427
theorem B1701739 : Blo 1701551 1701739 := bstep (se 1 (by rfl) ⟨1276304, by rfl⟩ : syracuseStep 1701739 = 2552609) B2552609
theorem B1701751 : Blo 1701551 1701751 := bstep (se 1 (by rfl) ⟨1276313, by rfl⟩ : syracuseStep 1701751 = 2552627) B2552627
theorem B1701771 : Blo 1701551 1701771 := bstep (se 1 (by rfl) ⟨1276328, by rfl⟩ : syracuseStep 1701771 = 2552657) B2552657
theorem B1914763 : Blo 1701551 1914763 := bstep (se 1 (by rfl) ⟨1436072, by rfl⟩ : syracuseStep 1914763 = 2872145) B2872145
theorem B1701783 : Blo 1701551 1701783 := bstep (se 1 (by rfl) ⟨1276337, by rfl⟩ : syracuseStep 1701783 = 2552675) B2552675
theorem B1701803 : Blo 1701551 1701803 := bstep (se 1 (by rfl) ⟨1276352, by rfl⟩ : syracuseStep 1701803 = 2552705) B2552705
theorem B3831731 : Blo 1701551 3831731 := bstep (se 1 (by rfl) ⟨2873798, by rfl⟩ : syracuseStep 3831731 = 5747597) B5747597
theorem B1701815 : Blo 1701551 1701815 := bstep (se 1 (by rfl) ⟨1276361, by rfl⟩ : syracuseStep 1701815 = 2552723) B2552723
theorem B1701835 : Blo 1701551 1701835 := bstep (se 1 (by rfl) ⟨1276376, by rfl⟩ : syracuseStep 1701835 = 2552753) B2552753
theorem B2553803 : Blo 1701551 2553803 := bstep (se 1 (by rfl) ⟨1915352, by rfl⟩ : syracuseStep 2553803 = 3830705) B3830705
theorem B1701847 : Blo 1701551 1701847 := bstep (se 1 (by rfl) ⟨1276385, by rfl⟩ : syracuseStep 1701847 = 2552771) B2552771
theorem B2553815 : Blo 1701551 2553815 := bstep (se 1 (by rfl) ⟨1915361, by rfl⟩ : syracuseStep 2553815 = 3830723) B3830723
theorem B3831767 : Blo 1701551 3831767 := bstep (se 1 (by rfl) ⟨2873825, by rfl⟩ : syracuseStep 3831767 = 5747651) B5747651
theorem B3233753 : Blo 1701551 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B1701867 : Blo 1701551 1701867 := bstep (se 1 (by rfl) ⟨1276400, by rfl⟩ : syracuseStep 1701867 = 2552801) B2552801
theorem B1914871 : Blo 1701551 1914871 := bstep (se 1 (by rfl) ⟨1436153, by rfl⟩ : syracuseStep 1914871 = 2872307) B2872307
theorem B1701879 : Blo 1701551 1701879 := bstep (se 1 (by rfl) ⟨1276409, by rfl⟩ : syracuseStep 1701879 = 2552819) B2552819
theorem B1701899 : Blo 1701551 1701899 := bstep (se 1 (by rfl) ⟨1276424, by rfl⟩ : syracuseStep 1701899 = 2552849) B2552849
theorem B1701911 : Blo 1701551 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B2553881 : Blo 1701551 2553881 := bstep (se 2 (by rfl) ⟨957705, by rfl⟩ : syracuseStep 2553881 = 1915411) B1915411
theorem B1701931 : Blo 1701551 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B6461491 : Blo 1701551 6461491 := bstep (se 1 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 6461491 = 9692237) B9692237
theorem B1701943 : Blo 1701551 1701943 := bstep (se 1 (by rfl) ⟨1276457, by rfl⟩ : syracuseStep 1701943 = 2552915) B2552915
theorem B1701963 : Blo 1701551 1701963 := bstep (se 1 (by rfl) ⟨1276472, by rfl⟩ : syracuseStep 1701963 = 2552945) B2552945
theorem B1701975 : Blo 1701551 1701975 := bstep (se 1 (by rfl) ⟨1276481, by rfl⟩ : syracuseStep 1701975 = 2552963) B2552963
theorem B1701995 : Blo 1701551 1701995 := bstep (se 1 (by rfl) ⟨1276496, by rfl⟩ : syracuseStep 1701995 = 2552993) B2552993
theorem B1702007 : Blo 1701551 1702007 := bstep (se 1 (by rfl) ⟨1276505, by rfl⟩ : syracuseStep 1702007 = 2553011) B2553011
theorem B1702027 : Blo 1701551 1702027 := bstep (se 1 (by rfl) ⟨1276520, by rfl⟩ : syracuseStep 1702027 = 2553041) B2553041
theorem B2553995 : Blo 1701551 2553995 := bstep (se 1 (by rfl) ⟨1915496, by rfl⟩ : syracuseStep 2553995 = 3830993) B3830993
theorem B3831947 : Blo 1701551 3831947 := bstep (se 1 (by rfl) ⟨2873960, by rfl⟩ : syracuseStep 3831947 = 5747921) B5747921
theorem B1702039 : Blo 1701551 1702039 := bstep (se 1 (by rfl) ⟨1276529, by rfl⟩ : syracuseStep 1702039 = 2553059) B2553059
theorem B2554007 : Blo 1701551 2554007 := bstep (se 1 (by rfl) ⟨1915505, by rfl⟩ : syracuseStep 2554007 = 3831011) B3831011
theorem B2873495 : Blo 1701551 2873495 := bstep (se 1 (by rfl) ⟨2155121, by rfl⟩ : syracuseStep 2873495 = 4310243) B4310243
theorem B1702059 : Blo 1701551 1702059 := bstep (se 1 (by rfl) ⟨1276544, by rfl⟩ : syracuseStep 1702059 = 2553089) B2553089
theorem B1915051 : Blo 1701551 1915051 := bstep (se 1 (by rfl) ⟨1436288, by rfl⟩ : syracuseStep 1915051 = 2872577) B2872577
theorem B9328819 : Blo 1701551 9328819 := bstep (se 1 (by rfl) ⟨6996614, by rfl⟩ : syracuseStep 9328819 = 13993229) B13993229
theorem B1702071 : Blo 1701551 1702071 := bstep (se 1 (by rfl) ⟨1276553, by rfl⟩ : syracuseStep 1702071 = 2553107) B2553107
theorem B3832001 : Blo 1701551 3832001 := bstep (se 2 (by rfl) ⟨1437000, by rfl⟩ : syracuseStep 3832001 = 2874001) B2874001
theorem B1702091 : Blo 1701551 1702091 := bstep (se 1 (by rfl) ⟨1276568, by rfl⟩ : syracuseStep 1702091 = 2553137) B2553137
theorem B1702103 : Blo 1701551 1702103 := bstep (se 1 (by rfl) ⟨1276577, by rfl⟩ : syracuseStep 1702103 = 2553155) B2553155
theorem B7272665 : Blo 1701551 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B8181977 : Blo 1701551 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B2554073 : Blo 1701551 2554073 := bstep (se 2 (by rfl) ⟨957777, by rfl⟩ : syracuseStep 2554073 = 1915555) B1915555
theorem B1702123 : Blo 1701551 1702123 := bstep (se 1 (by rfl) ⟨1276592, by rfl⟩ : syracuseStep 1702123 = 2553185) B2553185
theorem B1702135 : Blo 1701551 1702135 := bstep (se 1 (by rfl) ⟨1276601, by rfl⟩ : syracuseStep 1702135 = 2553203) B2553203
theorem B1702155 : Blo 1701551 1702155 := bstep (se 1 (by rfl) ⟨1276616, by rfl⟩ : syracuseStep 1702155 = 2553233) B2553233
theorem B1702167 : Blo 1701551 1702167 := bstep (se 1 (by rfl) ⟨1276625, by rfl⟩ : syracuseStep 1702167 = 2553251) B2553251
theorem B1915159 : Blo 1701551 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B2873623 : Blo 1701551 2873623 := bstep (se 1 (by rfl) ⟨2155217, by rfl⟩ : syracuseStep 2873623 = 4310435) B4310435
theorem B1702187 : Blo 1701551 1702187 := bstep (se 1 (by rfl) ⟨1276640, by rfl⟩ : syracuseStep 1702187 = 2553281) B2553281
theorem B117971245 : Blo 1701551 117971245 := bstep (se 3 (by rfl) ⟨22119608, by rfl⟩ : syracuseStep 117971245 = 44239217) B44239217
theorem B1702199 : Blo 1701551 1702199 := bstep (se 1 (by rfl) ⟨1276649, by rfl⟩ : syracuseStep 1702199 = 2553299) B2553299
theorem B1702219 : Blo 1701551 1702219 := bstep (se 1 (by rfl) ⟨1276664, by rfl⟩ : syracuseStep 1702219 = 2553329) B2553329
theorem B2554187 : Blo 1701551 2554187 := bstep (se 1 (by rfl) ⟨1915640, by rfl⟩ : syracuseStep 2554187 = 3831281) B3831281
theorem B1702231 : Blo 1701551 1702231 := bstep (se 1 (by rfl) ⟨1276673, by rfl⟩ : syracuseStep 1702231 = 2553347) B2553347
theorem B2554199 : Blo 1701551 2554199 := bstep (se 1 (by rfl) ⟨1915649, by rfl⟩ : syracuseStep 2554199 = 3831299) B3831299
theorem B29489507 : Blo 1701551 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B1702251 : Blo 1701551 1702251 := bstep (se 1 (by rfl) ⟨1276688, by rfl⟩ : syracuseStep 1702251 = 2553377) B2553377
theorem B1702263 : Blo 1701551 1702263 := bstep (se 1 (by rfl) ⟨1276697, by rfl⟩ : syracuseStep 1702263 = 2553395) B2553395
theorem B1702283 : Blo 1701551 1702283 := bstep (se 1 (by rfl) ⟨1276712, by rfl⟩ : syracuseStep 1702283 = 2553425) B2553425
theorem B2423191 : Blo 1701551 2423191 := bstep (se 1 (by rfl) ⟨1817393, by rfl⟩ : syracuseStep 2423191 = 3634787) B3634787
theorem B1702295 : Blo 1701551 1702295 := bstep (se 1 (by rfl) ⟨1276721, by rfl⟩ : syracuseStep 1702295 = 2553443) B2553443
theorem B2554265 : Blo 1701551 2554265 := bstep (se 2 (by rfl) ⟨957849, by rfl⟩ : syracuseStep 2554265 = 1915699) B1915699
theorem B3832217 : Blo 1701551 3832217 := bstep (se 2 (by rfl) ⟨1437081, by rfl⟩ : syracuseStep 3832217 = 2874163) B2874163
theorem B1702315 : Blo 1701551 1702315 := bstep (se 1 (by rfl) ⟨1276736, by rfl⟩ : syracuseStep 1702315 = 2553473) B2553473
theorem B14547377 : Blo 1701551 14547377 := bstep (se 2 (by rfl) ⟨5455266, by rfl⟩ : syracuseStep 14547377 = 10910533) B10910533
theorem B1702327 : Blo 1701551 1702327 := bstep (se 1 (by rfl) ⟨1276745, by rfl⟩ : syracuseStep 1702327 = 2553491) B2553491
theorem B1702347 : Blo 1701551 1702347 := bstep (se 1 (by rfl) ⟨1276760, by rfl⟩ : syracuseStep 1702347 = 2553521) B2553521
theorem B1915339 : Blo 1701551 1915339 := bstep (se 1 (by rfl) ⟨1436504, by rfl⟩ : syracuseStep 1915339 = 2873009) B2873009
theorem B1702359 : Blo 1701551 1702359 := bstep (se 1 (by rfl) ⟨1276769, by rfl⟩ : syracuseStep 1702359 = 2553539) B2553539
theorem B1702379 : Blo 1701551 1702379 := bstep (se 1 (by rfl) ⟨1276784, by rfl⟩ : syracuseStep 1702379 = 2553569) B2553569
theorem B3832307 : Blo 1701551 3832307 := bstep (se 1 (by rfl) ⟨2874230, by rfl⟩ : syracuseStep 3832307 = 5748461) B5748461
theorem B1702391 : Blo 1701551 1702391 := bstep (se 1 (by rfl) ⟨1276793, by rfl⟩ : syracuseStep 1702391 = 2553587) B2553587
theorem B1702411 : Blo 1701551 1702411 := bstep (se 1 (by rfl) ⟨1276808, by rfl⟩ : syracuseStep 1702411 = 2553617) B2553617
theorem B2554379 : Blo 1701551 2554379 := bstep (se 1 (by rfl) ⟨1915784, by rfl⟩ : syracuseStep 2554379 = 3831569) B3831569
theorem B2046475 : Blo 1701551 2046475 := bstep (se 1 (by rfl) ⟨1534856, by rfl⟩ : syracuseStep 2046475 = 3069713) B3069713
theorem B1702423 : Blo 1701551 1702423 := bstep (se 1 (by rfl) ⟨1276817, by rfl⟩ : syracuseStep 1702423 = 2553635) B2553635
theorem B2554391 : Blo 1701551 2554391 := bstep (se 1 (by rfl) ⟨1915793, by rfl⟩ : syracuseStep 2554391 = 3831587) B3831587
theorem B3832343 : Blo 1701551 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B5749271 : Blo 1701551 5749271 := bstep (se 1 (by rfl) ⟨4311953, by rfl⟩ : syracuseStep 5749271 = 8623907) B8623907
theorem B1702443 : Blo 1701551 1702443 := bstep (se 1 (by rfl) ⟨1276832, by rfl⟩ : syracuseStep 1702443 = 2553665) B2553665
theorem B1702455 : Blo 1701551 1702455 := bstep (se 1 (by rfl) ⟨1276841, by rfl⟩ : syracuseStep 1702455 = 2553683) B2553683
theorem B1915447 : Blo 1701551 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B1702475 : Blo 1701551 1702475 := bstep (se 1 (by rfl) ⟨1276856, by rfl⟩ : syracuseStep 1702475 = 2553713) B2553713
theorem B1702487 : Blo 1701551 1702487 := bstep (se 1 (by rfl) ⟨1276865, by rfl⟩ : syracuseStep 1702487 = 2553731) B2553731
theorem B2554457 : Blo 1701551 2554457 := bstep (se 2 (by rfl) ⟨957921, by rfl⟩ : syracuseStep 2554457 = 1915843) B1915843
theorem B1702507 : Blo 1701551 1702507 := bstep (se 1 (by rfl) ⟨1276880, by rfl⟩ : syracuseStep 1702507 = 2553761) B2553761
theorem B1702519 : Blo 1701551 1702519 := bstep (se 1 (by rfl) ⟨1276889, by rfl⟩ : syracuseStep 1702519 = 2553779) B2553779
theorem B1702539 : Blo 1701551 1702539 := bstep (se 1 (by rfl) ⟨1276904, by rfl⟩ : syracuseStep 1702539 = 2553809) B2553809
theorem B2726551 : Blo 1701551 2726551 := bstep (se 1 (by rfl) ⟨2044913, by rfl⟩ : syracuseStep 2726551 = 4089827) B4089827
theorem B1702551 : Blo 1701551 1702551 := bstep (se 1 (by rfl) ⟨1276913, by rfl⟩ : syracuseStep 1702551 = 2553827) B2553827
theorem B1702571 : Blo 1701551 1702571 := bstep (se 1 (by rfl) ⟨1276928, by rfl⟩ : syracuseStep 1702571 = 2553857) B2553857
theorem B1702583 : Blo 1701551 1702583 := bstep (se 1 (by rfl) ⟨1276937, by rfl⟩ : syracuseStep 1702583 = 2553875) B2553875
theorem B1702603 : Blo 1701551 1702603 := bstep (se 1 (by rfl) ⟨1276952, by rfl⟩ : syracuseStep 1702603 = 2553905) B2553905
theorem B2554571 : Blo 1701551 2554571 := bstep (se 1 (by rfl) ⟨1915928, by rfl⟩ : syracuseStep 2554571 = 3831857) B3831857
theorem B3832523 : Blo 1701551 3832523 := bstep (se 1 (by rfl) ⟨2874392, by rfl⟩ : syracuseStep 3832523 = 5748785) B5748785
theorem B1702615 : Blo 1701551 1702615 := bstep (se 1 (by rfl) ⟨1276961, by rfl⟩ : syracuseStep 1702615 = 2553923) B2553923
theorem B2554583 : Blo 1701551 2554583 := bstep (se 1 (by rfl) ⟨1915937, by rfl⟩ : syracuseStep 2554583 = 3831875) B3831875
theorem B1702635 : Blo 1701551 1702635 := bstep (se 1 (by rfl) ⟨1276976, by rfl⟩ : syracuseStep 1702635 = 2553953) B2553953
theorem B1915627 : Blo 1701551 1915627 := bstep (se 1 (by rfl) ⟨1436720, by rfl⟩ : syracuseStep 1915627 = 2873441) B2873441
theorem B1702647 : Blo 1701551 1702647 := bstep (se 1 (by rfl) ⟨1276985, by rfl⟩ : syracuseStep 1702647 = 2553971) B2553971
theorem B3832577 : Blo 1701551 3832577 := bstep (se 2 (by rfl) ⟨1437216, by rfl⟩ : syracuseStep 3832577 = 2874433) B2874433
theorem B1702667 : Blo 1701551 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B1702679 : Blo 1701551 1702679 := bstep (se 1 (by rfl) ⟨1277009, by rfl⟩ : syracuseStep 1702679 = 2554019) B2554019
theorem B2554649 : Blo 1701551 2554649 := bstep (se 2 (by rfl) ⟨957993, by rfl⟩ : syracuseStep 2554649 = 1915987) B1915987
theorem B1702699 : Blo 1701551 1702699 := bstep (se 1 (by rfl) ⟨1277024, by rfl⟩ : syracuseStep 1702699 = 2554049) B2554049
theorem B1702711 : Blo 1701551 1702711 := bstep (se 1 (by rfl) ⟨1277033, by rfl⟩ : syracuseStep 1702711 = 2554067) B2554067
theorem B8616779 : Blo 1701551 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B1702731 : Blo 1701551 1702731 := bstep (se 1 (by rfl) ⟨1277048, by rfl⟩ : syracuseStep 1702731 = 2554097) B2554097
theorem B1702743 : Blo 1701551 1702743 := bstep (se 1 (by rfl) ⟨1277057, by rfl⟩ : syracuseStep 1702743 = 2554115) B2554115
theorem B1915735 : Blo 1701551 1915735 := bstep (se 1 (by rfl) ⟨1436801, by rfl⟩ : syracuseStep 1915735 = 2873603) B2873603
theorem B3152729 : Blo 1701551 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B1702763 : Blo 1701551 1702763 := bstep (se 1 (by rfl) ⟨1277072, by rfl⟩ : syracuseStep 1702763 = 2554145) B2554145
theorem B1702775 : Blo 1701551 1702775 := bstep (se 1 (by rfl) ⟨1277081, by rfl⟩ : syracuseStep 1702775 = 2554163) B2554163
theorem B1702795 : Blo 1701551 1702795 := bstep (se 1 (by rfl) ⟨1277096, by rfl⟩ : syracuseStep 1702795 = 2554193) B2554193
theorem B2554763 : Blo 1701551 2554763 := bstep (se 1 (by rfl) ⟨1916072, by rfl⟩ : syracuseStep 2554763 = 3832145) B3832145
theorem B2874251 : Blo 1701551 2874251 := bstep (se 1 (by rfl) ⟨2155688, by rfl⟩ : syracuseStep 2874251 = 4311377) B4311377
theorem B4307863 : Blo 1701551 4307863 := bstep (se 1 (by rfl) ⟨3230897, by rfl⟩ : syracuseStep 4307863 = 6461795) B6461795
theorem B1702807 : Blo 1701551 1702807 := bstep (se 1 (by rfl) ⟨1277105, by rfl⟩ : syracuseStep 1702807 = 2554211) B2554211
theorem B2554775 : Blo 1701551 2554775 := bstep (se 1 (by rfl) ⟨1916081, by rfl⟩ : syracuseStep 2554775 = 3832163) B3832163
theorem B1702827 : Blo 1701551 1702827 := bstep (se 1 (by rfl) ⟨1277120, by rfl⟩ : syracuseStep 1702827 = 2554241) B2554241
theorem B1702839 : Blo 1701551 1702839 := bstep (se 1 (by rfl) ⟨1277129, by rfl⟩ : syracuseStep 1702839 = 2554259) B2554259
theorem B3734465 : Blo 1701551 3734465 := bstep (se 2 (by rfl) ⟨1400424, by rfl⟩ : syracuseStep 3734465 = 2800849) B2800849
theorem B1702859 : Blo 1701551 1702859 := bstep (se 1 (by rfl) ⟨1277144, by rfl⟩ : syracuseStep 1702859 = 2554289) B2554289
theorem B1702871 : Blo 1701551 1702871 := bstep (se 1 (by rfl) ⟨1277153, by rfl⟩ : syracuseStep 1702871 = 2554307) B2554307
theorem B2554841 : Blo 1701551 2554841 := bstep (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) B1916131
theorem B3832793 : Blo 1701551 3832793 := bstep (se 2 (by rfl) ⟨1437297, by rfl⟩ : syracuseStep 3832793 = 2874595) B2874595
theorem B1702891 : Blo 1701551 1702891 := bstep (se 1 (by rfl) ⟨1277168, by rfl⟩ : syracuseStep 1702891 = 2554337) B2554337
theorem B1702903 : Blo 1701551 1702903 := bstep (se 1 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 1702903 = 2554355) B2554355
theorem B1702923 : Blo 1701551 1702923 := bstep (se 1 (by rfl) ⟨1277192, by rfl⟩ : syracuseStep 1702923 = 2554385) B2554385
theorem B1915915 : Blo 1701551 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B2874379 : Blo 1701551 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B9206801 : Blo 1701551 9206801 := bstep (se 2 (by rfl) ⟨3452550, by rfl⟩ : syracuseStep 9206801 = 6905101) B6905101
theorem B3636247 : Blo 1701551 3636247 := bstep (se 1 (by rfl) ⟨2727185, by rfl⟩ : syracuseStep 3636247 = 5454371) B5454371
theorem B1702935 : Blo 1701551 1702935 := bstep (se 1 (by rfl) ⟨1277201, by rfl⟩ : syracuseStep 1702935 = 2554403) B2554403
theorem B1702955 : Blo 1701551 1702955 := bstep (se 1 (by rfl) ⟨1277216, by rfl⟩ : syracuseStep 1702955 = 2554433) B2554433
theorem B1702967 : Blo 1701551 1702967 := bstep (se 1 (by rfl) ⟨1277225, by rfl⟩ : syracuseStep 1702967 = 2554451) B2554451
theorem B3832883 : Blo 1701551 3832883 := bstep (se 1 (by rfl) ⟨2874662, by rfl⟩ : syracuseStep 3832883 = 5749325) B5749325
theorem B1702987 : Blo 1701551 1702987 := bstep (se 1 (by rfl) ⟨1277240, by rfl⟩ : syracuseStep 1702987 = 2554481) B2554481
theorem B2554955 : Blo 1701551 2554955 := bstep (se 1 (by rfl) ⟨1916216, by rfl⟩ : syracuseStep 2554955 = 3832433) B3832433
theorem B1702999 : Blo 1701551 1702999 := bstep (se 1 (by rfl) ⟨1277249, by rfl⟩ : syracuseStep 1702999 = 2554499) B2554499
theorem B2554967 : Blo 1701551 2554967 := bstep (se 1 (by rfl) ⟨1916225, by rfl⟩ : syracuseStep 2554967 = 3832451) B3832451
theorem B3832919 : Blo 1701551 3832919 := bstep (se 1 (by rfl) ⟨2874689, by rfl⟩ : syracuseStep 3832919 = 5749379) B5749379
theorem B1703019 : Blo 1701551 1703019 := bstep (se 1 (by rfl) ⟨1277264, by rfl⟩ : syracuseStep 1703019 = 2554529) B2554529
theorem B1703031 : Blo 1701551 1703031 := bstep (se 1 (by rfl) ⟨1277273, by rfl⟩ : syracuseStep 1703031 = 2554547) B2554547
theorem B1916023 : Blo 1701551 1916023 := bstep (se 1 (by rfl) ⟨1437017, by rfl⟩ : syracuseStep 1916023 = 2874035) B2874035
theorem B1703051 : Blo 1701551 1703051 := bstep (se 1 (by rfl) ⟨1277288, by rfl⟩ : syracuseStep 1703051 = 2554577) B2554577
theorem B2153623 : Blo 1701551 2153623 := bstep (se 1 (by rfl) ⟨1615217, by rfl⟩ : syracuseStep 2153623 = 3230435) B3230435
theorem B1703063 : Blo 1701551 1703063 := bstep (se 1 (by rfl) ⟨1277297, by rfl⟩ : syracuseStep 1703063 = 2554595) B2554595
theorem B2555033 : Blo 1701551 2555033 := bstep (se 2 (by rfl) ⟨958137, by rfl⟩ : syracuseStep 2555033 = 1916275) B1916275
theorem B2874521 : Blo 1701551 2874521 := bstep (se 2 (by rfl) ⟨1077945, by rfl⟩ : syracuseStep 2874521 = 2155891) B2155891
theorem B1703083 : Blo 1701551 1703083 := bstep (se 1 (by rfl) ⟨1277312, by rfl⟩ : syracuseStep 1703083 = 2554625) B2554625
theorem B1703095 : Blo 1701551 1703095 := bstep (se 1 (by rfl) ⟨1277321, by rfl⟩ : syracuseStep 1703095 = 2554643) B2554643
theorem B3636427 : Blo 1701551 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B1703115 : Blo 1701551 1703115 := bstep (se 1 (by rfl) ⟨1277336, by rfl⟩ : syracuseStep 1703115 = 2554673) B2554673
theorem B1703127 : Blo 1701551 1703127 := bstep (se 1 (by rfl) ⟨1277345, by rfl⟩ : syracuseStep 1703127 = 2554691) B2554691
theorem B1703147 : Blo 1701551 1703147 := bstep (se 1 (by rfl) ⟨1277360, by rfl⟩ : syracuseStep 1703147 = 2554721) B2554721
theorem B1703159 : Blo 1701551 1703159 := bstep (se 1 (by rfl) ⟨1277369, by rfl⟩ : syracuseStep 1703159 = 2554739) B2554739
theorem B1703179 : Blo 1701551 1703179 := bstep (se 1 (by rfl) ⟨1277384, by rfl⟩ : syracuseStep 1703179 = 2554769) B2554769
theorem B2555147 : Blo 1701551 2555147 := bstep (se 1 (by rfl) ⟨1916360, by rfl⟩ : syracuseStep 2555147 = 3832721) B3832721
theorem B6462737 : Blo 1701551 6462737 := bstep (se 2 (by rfl) ⟨2423526, by rfl⟩ : syracuseStep 6462737 = 4847053) B4847053
theorem B3636503 : Blo 1701551 3636503 := bstep (se 1 (by rfl) ⟨2727377, by rfl⟩ : syracuseStep 3636503 = 5454755) B5454755
theorem B1703191 : Blo 1701551 1703191 := bstep (se 1 (by rfl) ⟨1277393, by rfl⟩ : syracuseStep 1703191 = 2554787) B2554787
theorem B2555159 : Blo 1701551 2555159 := bstep (se 1 (by rfl) ⟨1916369, by rfl⟩ : syracuseStep 2555159 = 3832739) B3832739
theorem B2874649 : Blo 1701551 2874649 := bstep (se 2 (by rfl) ⟨1077993, by rfl⟩ : syracuseStep 2874649 = 2155987) B2155987
theorem B1703211 : Blo 1701551 1703211 := bstep (se 1 (by rfl) ⟨1277408, by rfl⟩ : syracuseStep 1703211 = 2554817) B2554817
theorem B1916203 : Blo 1701551 1916203 := bstep (se 1 (by rfl) ⟨1437152, by rfl⟩ : syracuseStep 1916203 = 2874305) B2874305
theorem B1703223 : Blo 1701551 1703223 := bstep (se 1 (by rfl) ⟨1277417, by rfl⟩ : syracuseStep 1703223 = 2554835) B2554835
theorem B4308299 : Blo 1701551 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2587979 : Blo 1701551 2587979 := bstep (se 1 (by rfl) ⟨1940984, by rfl⟩ : syracuseStep 2587979 = 3881969) B3881969
theorem B1703243 : Blo 1701551 1703243 := bstep (se 1 (by rfl) ⟨1277432, by rfl⟩ : syracuseStep 1703243 = 2554865) B2554865
theorem B1703255 : Blo 1701551 1703255 := bstep (se 1 (by rfl) ⟨1277441, by rfl⟩ : syracuseStep 1703255 = 2554883) B2554883
theorem B2555225 : Blo 1701551 2555225 := bstep (se 2 (by rfl) ⟨958209, by rfl⟩ : syracuseStep 2555225 = 1916419) B1916419
theorem B1703275 : Blo 1701551 1703275 := bstep (se 1 (by rfl) ⟨1277456, by rfl⟩ : syracuseStep 1703275 = 2554913) B2554913
theorem B22715765 : Blo 1701551 22715765 := bstep (se 5 (by rfl) ⟨1064801, by rfl⟩ : syracuseStep 22715765 = 2129603) B2129603
theorem B1703287 : Blo 1701551 1703287 := bstep (se 1 (by rfl) ⟨1277465, by rfl⟩ : syracuseStep 1703287 = 2554931) B2554931
theorem B1703307 : Blo 1701551 1703307 := bstep (se 1 (by rfl) ⟨1277480, by rfl⟩ : syracuseStep 1703307 = 2554961) B2554961
theorem B1703319 : Blo 1701551 1703319 := bstep (se 1 (by rfl) ⟨1277489, by rfl⟩ : syracuseStep 1703319 = 2554979) B2554979
theorem B1916311 : Blo 1701551 1916311 := bstep (se 1 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 1916311 = 2874467) B2874467
theorem B1703339 : Blo 1701551 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B1703351 : Blo 1701551 1703351 := bstep (se 1 (by rfl) ⟨1277513, by rfl⟩ : syracuseStep 1703351 = 2555027) B2555027
theorem B1703371 : Blo 1701551 1703371 := bstep (se 1 (by rfl) ⟨1277528, by rfl⟩ : syracuseStep 1703371 = 2555057) B2555057
theorem B1703383 : Blo 1701551 1703383 := bstep (se 1 (by rfl) ⟨1277537, by rfl⟩ : syracuseStep 1703383 = 2555075) B2555075
theorem B9698777 : Blo 1701551 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B1703403 : Blo 1701551 1703403 := bstep (se 1 (by rfl) ⟨1277552, by rfl⟩ : syracuseStep 1703403 = 2555105) B2555105
theorem B1703415 : Blo 1701551 1703415 := bstep (se 1 (by rfl) ⟨1277561, by rfl⟩ : syracuseStep 1703415 = 2555123) B2555123
theorem B1703435 : Blo 1701551 1703435 := bstep (se 1 (by rfl) ⟨1277576, by rfl⟩ : syracuseStep 1703435 = 2555153) B2555153
theorem B1703447 : Blo 1701551 1703447 := bstep (se 1 (by rfl) ⟨1277585, by rfl⟩ : syracuseStep 1703447 = 2555171) B2555171
theorem B1703467 : Blo 1701551 1703467 := bstep (se 1 (by rfl) ⟨1277600, by rfl⟩ : syracuseStep 1703467 = 2555201) B2555201
theorem B1703479 : Blo 1701551 1703479 := bstep (se 1 (by rfl) ⟨1277609, by rfl⟩ : syracuseStep 1703479 = 2555219) B2555219
theorem B4849217 : Blo 1701551 4849217 := bstep (se 2 (by rfl) ⟨1818456, by rfl⟩ : syracuseStep 4849217 = 3636913) B3636913
theorem B1703499 : Blo 1701551 1703499 := bstep (se 1 (by rfl) ⟨1277624, by rfl⟩ : syracuseStep 1703499 = 2555249) B2555249
theorem B1916491 : Blo 1701551 1916491 := bstep (se 1 (by rfl) ⟨1437368, by rfl⟩ : syracuseStep 1916491 = 2874737) B2874737
theorem B1703511 : Blo 1701551 1703511 := bstep (se 1 (by rfl) ⟨1277633, by rfl⟩ : syracuseStep 1703511 = 2555267) B2555267
theorem B1703531 : Blo 1701551 1703531 := bstep (se 1 (by rfl) ⟨1277648, by rfl⟩ : syracuseStep 1703531 = 2555297) B2555297
theorem B1703543 : Blo 1701551 1703543 := bstep (se 1 (by rfl) ⟨1277657, by rfl⟩ : syracuseStep 1703543 = 2555315) B2555315
theorem B20717207 : Blo 1701551 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B4308673 : Blo 1701551 4308673 := bstep (se 2 (by rfl) ⟨1615752, by rfl⟩ : syracuseStep 4308673 = 3231505) B3231505
theorem B27623267 : Blo 1701551 27623267 := bstep (se 1 (by rfl) ⟨20717450, by rfl⟩ : syracuseStep 27623267 = 41434901) B41434901
theorem B1818487 : Blo 1701551 1818487 := bstep (se 1 (by rfl) ⟨1363865, by rfl⟩ : syracuseStep 1818487 = 2727731) B2727731
theorem B6463435 : Blo 1701551 6463435 := bstep (se 1 (by rfl) ⟨4847576, by rfl⟩ : syracuseStep 6463435 = 9695153) B9695153
theorem B10354711 : Blo 1701551 10354711 := bstep (se 1 (by rfl) ⟨7766033, by rfl⟩ : syracuseStep 10354711 = 15532067) B15532067
theorem B2154539 : Blo 1701551 2154539 := bstep (se 1 (by rfl) ⟨1615904, by rfl⟩ : syracuseStep 2154539 = 3231809) B3231809
theorem B4309139 : Blo 1701551 4309139 := bstep (se 1 (by rfl) ⟨3231854, by rfl⟩ : syracuseStep 4309139 = 6463709) B6463709
theorem B12271931 : Blo 1701551 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B157294993 : Blo 1701551 157294993 := bstep (se 2 (by rfl) ⟨58985622, by rfl⟩ : syracuseStep 157294993 = 117971245) B117971245
theorem B5456281 : Blo 1701551 5456281 := bstep (se 2 (by rfl) ⟨2046105, by rfl⟩ : syracuseStep 5456281 = 4092211) B4092211
theorem B4309433 : Blo 1701551 4309433 := bstep (se 2 (by rfl) ⟨1616037, by rfl⟩ : syracuseStep 4309433 = 3232075) B3232075
theorem B4915657 : Blo 1701551 4915657 := bstep (se 2 (by rfl) ⟨1843371, by rfl⟩ : syracuseStep 4915657 = 3686743) B3686743
theorem B2155015 : Blo 1701551 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B5743115 : Blo 1701551 5743115 := bstep (se 1 (by rfl) ⟨4307336, by rfl⟩ : syracuseStep 5743115 = 8614673) B8614673
theorem B8741405 : Blo 1701551 8741405 := bstep (se 3 (by rfl) ⟨1639013, by rfl⟩ : syracuseStep 8741405 = 3278027) B3278027
theorem B39338531 : Blo 1701551 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B4850219 : Blo 1701551 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B5743223 : Blo 1701551 5743223 := bstep (se 1 (by rfl) ⟨4307417, by rfl⟩ : syracuseStep 5743223 = 8614835) B8614835
theorem B9691919 : Blo 1701551 9691919 := bstep (se 1 (by rfl) ⟨7268939, by rfl⟩ : syracuseStep 9691919 = 14537879) B14537879
theorem B10355489 : Blo 1701551 10355489 := bstep (se 2 (by rfl) ⟨3883308, by rfl⟩ : syracuseStep 10355489 = 7766617) B7766617
theorem B14541605 : Blo 1701551 14541605 := bstep (se 4 (by rfl) ⟨1363275, by rfl⟩ : syracuseStep 14541605 = 2726551) B2726551
theorem B4916027 : Blo 1701551 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B3638135 : Blo 1701551 3638135 := bstep (se 1 (by rfl) ⟨2728601, by rfl⟩ : syracuseStep 3638135 = 5457203) B5457203
theorem B2155511 : Blo 1701551 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B4310131 : Blo 1701551 4310131 := bstep (se 1 (by rfl) ⟨3232598, by rfl⟩ : syracuseStep 4310131 = 6465197) B6465197
theorem B2155663 : Blo 1701551 2155663 := bstep (se 1 (by rfl) ⟨1616747, by rfl⟩ : syracuseStep 2155663 = 3233495) B3233495
theorem B5743817 : Blo 1701551 5743817 := bstep (se 2 (by rfl) ⟨2153931, by rfl⟩ : syracuseStep 5743817 = 4307863) B4307863
theorem B8619209 : Blo 1701551 8619209 := bstep (se 2 (by rfl) ⟨3232203, by rfl⟩ : syracuseStep 8619209 = 6464407) B6464407
theorem B4310273 : Blo 1701551 4310273 := bstep (se 2 (by rfl) ⟨1616352, by rfl⟩ : syracuseStep 4310273 = 3232705) B3232705
theorem B1967375 : Blo 1701551 1967375 := bstep (se 1 (by rfl) ⟨1475531, by rfl⟩ : syracuseStep 1967375 = 2951063) B2951063
theorem B9700667 : Blo 1701551 9700667 := bstep (se 1 (by rfl) ⟨7275500, by rfl⟩ : syracuseStep 9700667 = 14551001) B14551001
theorem B2155835 : Blo 1701551 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B13993361 : Blo 1701551 13993361 := bstep (se 2 (by rfl) ⟨5247510, by rfl⟩ : syracuseStep 13993361 = 10495021) B10495021
theorem B4310729 : Blo 1701551 4310729 := bstep (se 2 (by rfl) ⟨1616523, by rfl⟩ : syracuseStep 4310729 = 3233047) B3233047
theorem B16361189 : Blo 1701551 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B5744519 : Blo 1701551 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B6137867 : Blo 1701551 6137867 := bstep (se 1 (by rfl) ⟨4603400, by rfl⟩ : syracuseStep 6137867 = 9206801) B9206801
theorem B4311083 : Blo 1701551 4311083 := bstep (se 1 (by rfl) ⟨3233312, by rfl⟩ : syracuseStep 4311083 = 6466625) B6466625
theorem B7473239 : Blo 1701551 7473239 := bstep (se 1 (by rfl) ⟨5604929, by rfl⟩ : syracuseStep 7473239 = 11209859) B11209859
theorem B4090009 : Blo 1701551 4090009 := bstep (se 2 (by rfl) ⟨1533753, by rfl⟩ : syracuseStep 4090009 = 3067507) B3067507
theorem B9693377 : Blo 1701551 9693377 := bstep (se 2 (by rfl) ⟨3635016, by rfl⟩ : syracuseStep 9693377 = 7270033) B7270033
theorem B8407277 : Blo 1701551 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B5744897 : Blo 1701551 5744897 := bstep (se 2 (by rfl) ⟨2154336, by rfl⟩ : syracuseStep 5744897 = 4308673) B4308673
theorem B6465851 : Blo 1701551 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B10906001 : Blo 1701551 10906001 := bstep (se 2 (by rfl) ⟨4089750, by rfl⟩ : syracuseStep 10906001 = 8179501) B8179501
theorem B9202349 : Blo 1701551 9202349 := bstep (se 3 (by rfl) ⟨1725440, by rfl⟩ : syracuseStep 9202349 = 3450881) B3450881
theorem B10914533 : Blo 1701551 10914533 := bstep (se 4 (by rfl) ⟨1023237, by rfl⟩ : syracuseStep 10914533 = 2046475) B2046475
theorem B9702125 : Blo 1701551 9702125 := bstep (se 3 (by rfl) ⟨1819148, by rfl⟩ : syracuseStep 9702125 = 3638297) B3638297
theorem B4090625 : Blo 1701551 4090625 := bstep (se 2 (by rfl) ⟨1533984, by rfl⟩ : syracuseStep 4090625 = 3067969) B3067969
theorem B6466337 : Blo 1701551 6466337 := bstep (se 2 (by rfl) ⟨2424876, by rfl⟩ : syracuseStep 6466337 = 4849753) B4849753
theorem B33164147 : Blo 1701551 33164147 := bstep (se 1 (by rfl) ⟨24873110, by rfl⟩ : syracuseStep 33164147 = 49746221) B49746221
theorem B3828599 : Blo 1701551 3828599 := bstep (se 1 (by rfl) ⟨2871449, by rfl⟩ : syracuseStep 3828599 = 5742899) B5742899
theorem B3066743 : Blo 1701551 3066743 := bstep (se 1 (by rfl) ⟨2300057, by rfl⟩ : syracuseStep 3066743 = 4600115) B4600115
theorem B12438425 : Blo 1701551 12438425 := bstep (se 2 (by rfl) ⟨4664409, by rfl⟩ : syracuseStep 12438425 = 9328819) B9328819
theorem B4312075 : Blo 1701551 4312075 := bstep (se 1 (by rfl) ⟨3234056, by rfl⟩ : syracuseStep 4312075 = 6468113) B6468113
theorem B3828779 : Blo 1701551 3828779 := bstep (se 1 (by rfl) ⟨2871584, by rfl⟩ : syracuseStep 3828779 = 5743169) B5743169
theorem B5745707 : Blo 1701551 5745707 := bstep (se 1 (by rfl) ⟨4309280, by rfl⟩ : syracuseStep 5745707 = 8618561) B8618561
theorem B10357847 : Blo 1701551 10357847 := bstep (se 1 (by rfl) ⟨7768385, by rfl⟩ : syracuseStep 10357847 = 15536771) B15536771
theorem B27626629 : Blo 1701551 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B3230867 : Blo 1701551 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B3230921 : Blo 1701551 3230921 := bstep (se 2 (by rfl) ⟨1211595, by rfl⟩ : syracuseStep 3230921 = 2423191) B2423191
theorem B21818605 : Blo 1701551 21818605 := bstep (se 3 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 21818605 = 8181977) B8181977
theorem B3231019 : Blo 1701551 3231019 := bstep (se 1 (by rfl) ⟨2423264, by rfl⟩ : syracuseStep 3231019 = 4846529) B4846529
theorem B3829139 : Blo 1701551 3829139 := bstep (se 1 (by rfl) ⟨2871854, by rfl⟩ : syracuseStep 3829139 = 5743709) B5743709
theorem B3829193 : Blo 1701551 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B3231247 : Blo 1701551 3231247 := bstep (se 1 (by rfl) ⟨2423435, by rfl⟩ : syracuseStep 3231247 = 4846871) B4846871
theorem B7761527 : Blo 1701551 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B6467309 : Blo 1701551 6467309 := bstep (se 3 (by rfl) ⟨1212620, by rfl⟩ : syracuseStep 6467309 = 2425241) B2425241
theorem B4091681 : Blo 1701551 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B55217969 : Blo 1701551 55217969 := bstep (se 2 (by rfl) ⟨20706738, by rfl⟩ : syracuseStep 55217969 = 41413477) B41413477
theorem B12922739 : Blo 1701551 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B4599671 : Blo 1701551 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B34959377 : Blo 1701551 34959377 := bstep (se 2 (by rfl) ⟨13109766, by rfl⟩ : syracuseStep 34959377 = 26219533) B26219533
theorem B6467627 : Blo 1701551 6467627 := bstep (se 1 (by rfl) ⟨4850720, by rfl⟩ : syracuseStep 6467627 = 9701441) B9701441
theorem B15536261 : Blo 1701551 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B3829895 : Blo 1701551 3829895 := bstep (se 1 (by rfl) ⟨2872421, by rfl⟩ : syracuseStep 3829895 = 5744843) B5744843
theorem B2871497 : Blo 1701551 2871497 := bstep (se 2 (by rfl) ⟨1076811, by rfl⟩ : syracuseStep 2871497 = 2153623) B2153623
theorem B3453199 : Blo 1701551 3453199 := bstep (se 1 (by rfl) ⟨2589899, by rfl⟩ : syracuseStep 3453199 = 5179799) B5179799
theorem B3830075 : Blo 1701551 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B5747003 : Blo 1701551 5747003 := bstep (se 1 (by rfl) ⟨4310252, by rfl⟩ : syracuseStep 5747003 = 8620505) B8620505
theorem B3830201 : Blo 1701551 3830201 := bstep (se 2 (by rfl) ⟨1436325, by rfl⟩ : syracuseStep 3830201 = 2872651) B2872651
theorem B2552327 : Blo 1701551 2552327 := bstep (se 1 (by rfl) ⟨1914245, by rfl⟩ : syracuseStep 2552327 = 3828491) B3828491
theorem B2552363 : Blo 1701551 2552363 := bstep (se 1 (by rfl) ⟨1914272, by rfl⟩ : syracuseStep 2552363 = 3828545) B3828545
theorem B7270955 : Blo 1701551 7270955 := bstep (se 1 (by rfl) ⟨5453216, by rfl⟩ : syracuseStep 7270955 = 10906433) B10906433
theorem B2552393 : Blo 1701551 2552393 := bstep (se 2 (by rfl) ⟨957147, by rfl⟩ : syracuseStep 2552393 = 1914295) B1914295
theorem B2552507 : Blo 1701551 2552507 := bstep (se 1 (by rfl) ⟨1914380, by rfl⟩ : syracuseStep 2552507 = 3828761) B3828761
theorem B14545601 : Blo 1701551 14545601 := bstep (se 2 (by rfl) ⟨5454600, by rfl⟩ : syracuseStep 14545601 = 10909201) B10909201
theorem B2552567 : Blo 1701551 2552567 := bstep (se 1 (by rfl) ⟨1914425, by rfl⟩ : syracuseStep 2552567 = 3828851) B3828851
theorem B2552591 : Blo 1701551 2552591 := bstep (se 1 (by rfl) ⟨1914443, by rfl⟩ : syracuseStep 2552591 = 3828887) B3828887
theorem B3830543 : Blo 1701551 3830543 := bstep (se 1 (by rfl) ⟨2872907, by rfl⟩ : syracuseStep 3830543 = 5745815) B5745815
theorem B3830561 : Blo 1701551 3830561 := bstep (se 2 (by rfl) ⟨1436460, by rfl⟩ : syracuseStep 3830561 = 2872921) B2872921
theorem B5747489 : Blo 1701551 5747489 := bstep (se 2 (by rfl) ⟨2155308, by rfl⟩ : syracuseStep 5747489 = 4310617) B4310617
theorem B2552633 : Blo 1701551 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B2552711 : Blo 1701551 2552711 := bstep (se 1 (by rfl) ⟨1914533, by rfl⟩ : syracuseStep 2552711 = 3829067) B3829067
theorem B2872199 : Blo 1701551 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1725319 : Blo 1701551 1725319 := bstep (se 1 (by rfl) ⟨1293989, by rfl⟩ : syracuseStep 1725319 = 2587979) B2587979
theorem B4846483 : Blo 1701551 4846483 := bstep (se 1 (by rfl) ⟨3634862, by rfl⟩ : syracuseStep 4846483 = 7269725) B7269725
theorem B15143843 : Blo 1701551 15143843 := bstep (se 1 (by rfl) ⟨11357882, by rfl⟩ : syracuseStep 15143843 = 22715765) B22715765
theorem B2552747 : Blo 1701551 2552747 := bstep (se 1 (by rfl) ⟨1914560, by rfl⟩ : syracuseStep 2552747 = 3829121) B3829121
theorem B2552777 : Blo 1701551 2552777 := bstep (se 2 (by rfl) ⟨957291, by rfl⟩ : syracuseStep 2552777 = 1914583) B1914583
theorem B3232811 : Blo 1701551 3232811 := bstep (se 1 (by rfl) ⟨2424608, by rfl⟩ : syracuseStep 3232811 = 4849217) B4849217
theorem B2552891 : Blo 1701551 2552891 := bstep (se 1 (by rfl) ⟨1914668, by rfl⟩ : syracuseStep 2552891 = 3829337) B3829337
theorem B2552951 : Blo 1701551 2552951 := bstep (se 1 (by rfl) ⟨1914713, by rfl⟩ : syracuseStep 2552951 = 3829427) B3829427
theorem B4846711 : Blo 1701551 4846711 := bstep (se 1 (by rfl) ⟨3635033, by rfl⟩ : syracuseStep 4846711 = 7270067) B7270067
theorem B3830903 : Blo 1701551 3830903 := bstep (se 1 (by rfl) ⟨2873177, by rfl⟩ : syracuseStep 3830903 = 5746355) B5746355
theorem B2552975 : Blo 1701551 2552975 := bstep (se 1 (by rfl) ⟨1914731, by rfl⟩ : syracuseStep 2552975 = 3829463) B3829463
theorem B4600979 : Blo 1701551 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B9958573 : Blo 1701551 9958573 := bstep (se 3 (by rfl) ⟨1867232, by rfl⟩ : syracuseStep 9958573 = 3734465) B3734465
theorem B2553017 : Blo 1701551 2553017 := bstep (se 2 (by rfl) ⟨957381, by rfl⟩ : syracuseStep 2553017 = 1914763) B1914763
theorem B2553095 : Blo 1701551 2553095 := bstep (se 1 (by rfl) ⟨1914821, by rfl⟩ : syracuseStep 2553095 = 3829643) B3829643
theorem B2553131 : Blo 1701551 2553131 := bstep (se 1 (by rfl) ⟨1914848, by rfl⟩ : syracuseStep 2553131 = 3829697) B3829697
theorem B3831083 : Blo 1701551 3831083 := bstep (se 1 (by rfl) ⟨2873312, by rfl⟩ : syracuseStep 3831083 = 5746625) B5746625
theorem B2553161 : Blo 1701551 2553161 := bstep (se 2 (by rfl) ⟨957435, by rfl⟩ : syracuseStep 2553161 = 1914871) B1914871
theorem B5748083 : Blo 1701551 5748083 := bstep (se 1 (by rfl) ⟨4311062, by rfl⟩ : syracuseStep 5748083 = 8622125) B8622125
theorem B3683731 : Blo 1701551 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B8615321 : Blo 1701551 8615321 := bstep (se 2 (by rfl) ⟨3230745, by rfl⟩ : syracuseStep 8615321 = 6461491) B6461491
theorem B2553275 : Blo 1701551 2553275 := bstep (se 1 (by rfl) ⟨1914956, by rfl⟩ : syracuseStep 2553275 = 3829913) B3829913
theorem B2553335 : Blo 1701551 2553335 := bstep (se 1 (by rfl) ⟨1915001, by rfl⟩ : syracuseStep 2553335 = 3830003) B3830003
theorem B2553359 : Blo 1701551 2553359 := bstep (se 1 (by rfl) ⟨1915019, by rfl⟩ : syracuseStep 2553359 = 3830039) B3830039
theorem B2872847 : Blo 1701551 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B2553401 : Blo 1701551 2553401 := bstep (se 2 (by rfl) ⟨957525, by rfl⟩ : syracuseStep 2553401 = 1915051) B1915051
theorem B4666999 : Blo 1701551 4666999 := bstep (se 1 (by rfl) ⟨3500249, by rfl⟩ : syracuseStep 4666999 = 7000499) B7000499
theorem B2553479 : Blo 1701551 2553479 := bstep (se 1 (by rfl) ⟨1915109, by rfl⟩ : syracuseStep 2553479 = 3830219) B3830219
theorem B1914511 : Blo 1701551 1914511 := bstep (se 1 (by rfl) ⟨1435883, by rfl⟩ : syracuseStep 1914511 = 2871767) B2871767
theorem B3831443 : Blo 1701551 3831443 := bstep (se 1 (by rfl) ⟨2873582, by rfl⟩ : syracuseStep 3831443 = 5747165) B5747165
theorem B2553515 : Blo 1701551 2553515 := bstep (se 1 (by rfl) ⟨1915136, by rfl⟩ : syracuseStep 2553515 = 3830273) B3830273
theorem B53106353 : Blo 1701551 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B1701563 : Blo 1701551 1701563 := bstep (se 1 (by rfl) ⟨1276172, by rfl⟩ : syracuseStep 1701563 = 2552345) B2552345
theorem B5453513 : Blo 1701551 5453513 := bstep (se 2 (by rfl) ⟨2045067, by rfl⟩ : syracuseStep 5453513 = 4090135) B4090135
theorem B2553545 : Blo 1701551 2553545 := bstep (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) B1915159
theorem B3831497 : Blo 1701551 3831497 := bstep (se 2 (by rfl) ⟨1436811, by rfl⟩ : syracuseStep 3831497 = 2873623) B2873623
theorem B1701639 : Blo 1701551 1701639 := bstep (se 1 (by rfl) ⟨1276229, by rfl⟩ : syracuseStep 1701639 = 2552459) B2552459
theorem B1701647 : Blo 1701551 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B16578341 : Blo 1701551 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B1701691 : Blo 1701551 1701691 := bstep (se 1 (by rfl) ⟨1276268, by rfl⟩ : syracuseStep 1701691 = 2552537) B2552537
theorem B2553659 : Blo 1701551 2553659 := bstep (se 1 (by rfl) ⟨1915244, by rfl⟩ : syracuseStep 2553659 = 3830489) B3830489
theorem B2553719 : Blo 1701551 2553719 := bstep (se 1 (by rfl) ⟨1915289, by rfl⟩ : syracuseStep 2553719 = 3830579) B3830579
theorem B1701767 : Blo 1701551 1701767 := bstep (se 1 (by rfl) ⟨1276325, by rfl⟩ : syracuseStep 1701767 = 2552651) B2552651
theorem B1701775 : Blo 1701551 1701775 := bstep (se 1 (by rfl) ⟨1276331, by rfl⟩ : syracuseStep 1701775 = 2552663) B2552663
theorem B2553743 : Blo 1701551 2553743 := bstep (se 1 (by rfl) ⟨1915307, by rfl⟩ : syracuseStep 2553743 = 3830615) B3830615
theorem B19658647 : Blo 1701551 19658647 := bstep (se 1 (by rfl) ⟨14743985, by rfl⟩ : syracuseStep 19658647 = 29487971) B29487971
theorem B2553785 : Blo 1701551 2553785 := bstep (se 2 (by rfl) ⟨957669, by rfl⟩ : syracuseStep 2553785 = 1915339) B1915339
theorem B1701819 : Blo 1701551 1701819 := bstep (se 1 (by rfl) ⟨1276364, by rfl⟩ : syracuseStep 1701819 = 2552729) B2552729
theorem B9459665 : Blo 1701551 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B1701895 : Blo 1701551 1701895 := bstep (se 1 (by rfl) ⟨1276421, by rfl⟩ : syracuseStep 1701895 = 2552843) B2552843
theorem B2553863 : Blo 1701551 2553863 := bstep (se 1 (by rfl) ⟨1915397, by rfl⟩ : syracuseStep 2553863 = 3830795) B3830795
theorem B1701903 : Blo 1701551 1701903 := bstep (se 1 (by rfl) ⟨1276427, by rfl⟩ : syracuseStep 1701903 = 2552855) B2552855
theorem B7764011 : Blo 1701551 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B2553899 : Blo 1701551 2553899 := bstep (se 1 (by rfl) ⟨1915424, by rfl⟩ : syracuseStep 2553899 = 3830849) B3830849
theorem B2873387 : Blo 1701551 2873387 := bstep (se 1 (by rfl) ⟨2155040, by rfl⟩ : syracuseStep 2873387 = 4310081) B4310081
theorem B1701947 : Blo 1701551 1701947 := bstep (se 1 (by rfl) ⟨1276460, by rfl⟩ : syracuseStep 1701947 = 2552921) B2552921
theorem B10639421 : Blo 1701551 10639421 := bstep (se 3 (by rfl) ⟨1994891, by rfl⟩ : syracuseStep 10639421 = 3989783) B3989783
theorem B2553929 : Blo 1701551 2553929 := bstep (se 2 (by rfl) ⟨957723, by rfl⟩ : syracuseStep 2553929 = 1915447) B1915447
theorem B16357463 : Blo 1701551 16357463 := bstep (se 1 (by rfl) ⟨12268097, by rfl⟩ : syracuseStep 16357463 = 24536195) B24536195
theorem B1702023 : Blo 1701551 1702023 := bstep (se 1 (by rfl) ⟨1276517, by rfl⟩ : syracuseStep 1702023 = 2553035) B2553035
theorem B1915015 : Blo 1701551 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B1702031 : Blo 1701551 1702031 := bstep (se 1 (by rfl) ⟨1276523, by rfl⟩ : syracuseStep 1702031 = 2553047) B2553047
theorem B1702075 : Blo 1701551 1702075 := bstep (se 1 (by rfl) ⟨1276556, by rfl⟩ : syracuseStep 1702075 = 2553113) B2553113
theorem B2554043 : Blo 1701551 2554043 := bstep (se 1 (by rfl) ⟨1915532, by rfl⟩ : syracuseStep 2554043 = 3831065) B3831065
theorem B2554103 : Blo 1701551 2554103 := bstep (se 1 (by rfl) ⟨1915577, by rfl⟩ : syracuseStep 2554103 = 3831155) B3831155
theorem B1702151 : Blo 1701551 1702151 := bstep (se 1 (by rfl) ⟨1276613, by rfl⟩ : syracuseStep 1702151 = 2553227) B2553227
theorem B4307215 : Blo 1701551 4307215 := bstep (se 1 (by rfl) ⟨3230411, by rfl⟩ : syracuseStep 4307215 = 6460823) B6460823
theorem B1702159 : Blo 1701551 1702159 := bstep (se 1 (by rfl) ⟨1276619, by rfl⟩ : syracuseStep 1702159 = 2553239) B2553239
theorem B2554127 : Blo 1701551 2554127 := bstep (se 1 (by rfl) ⟨1915595, by rfl⟩ : syracuseStep 2554127 = 3831191) B3831191
theorem B2554169 : Blo 1701551 2554169 := bstep (se 2 (by rfl) ⟨957813, by rfl⟩ : syracuseStep 2554169 = 1915627) B1915627
theorem B1702203 : Blo 1701551 1702203 := bstep (se 1 (by rfl) ⟨1276652, by rfl⟩ : syracuseStep 1702203 = 2553305) B2553305
theorem B1915195 : Blo 1701551 1915195 := bstep (se 1 (by rfl) ⟨1436396, by rfl⟩ : syracuseStep 1915195 = 2872793) B2872793
theorem B4847987 : Blo 1701551 4847987 := bstep (se 1 (by rfl) ⟨3635990, by rfl⟩ : syracuseStep 4847987 = 7271981) B7271981
theorem B1702279 : Blo 1701551 1702279 := bstep (se 1 (by rfl) ⟨1276709, by rfl⟩ : syracuseStep 1702279 = 2553419) B2553419
theorem B2554247 : Blo 1701551 2554247 := bstep (se 1 (by rfl) ⟨1915685, by rfl⟩ : syracuseStep 2554247 = 3831371) B3831371
theorem B3832199 : Blo 1701551 3832199 := bstep (se 1 (by rfl) ⟨2874149, by rfl⟩ : syracuseStep 3832199 = 5748299) B5748299
theorem B1702287 : Blo 1701551 1702287 := bstep (se 1 (by rfl) ⟨1276715, by rfl⟩ : syracuseStep 1702287 = 2553431) B2553431
theorem B2554283 : Blo 1701551 2554283 := bstep (se 1 (by rfl) ⟨1915712, by rfl⟩ : syracuseStep 2554283 = 3831425) B3831425
theorem B2873785 : Blo 1701551 2873785 := bstep (se 2 (by rfl) ⟨1077669, by rfl⟩ : syracuseStep 2873785 = 2155339) B2155339
theorem B1702331 : Blo 1701551 1702331 := bstep (se 1 (by rfl) ⟨1276748, by rfl⟩ : syracuseStep 1702331 = 2553497) B2553497
theorem B2554313 : Blo 1701551 2554313 := bstep (se 2 (by rfl) ⟨957867, by rfl⟩ : syracuseStep 2554313 = 1915735) B1915735
theorem B2423287 : Blo 1701551 2423287 := bstep (se 1 (by rfl) ⟨1817465, by rfl⟩ : syracuseStep 2423287 = 3634931) B3634931
theorem B1702407 : Blo 1701551 1702407 := bstep (se 1 (by rfl) ⟨1276805, by rfl⟩ : syracuseStep 1702407 = 2553611) B2553611
theorem B6461963 : Blo 1701551 6461963 := bstep (se 1 (by rfl) ⟨4846472, by rfl⟩ : syracuseStep 6461963 = 9692945) B9692945
theorem B1702415 : Blo 1701551 1702415 := bstep (se 1 (by rfl) ⟨1276811, by rfl⟩ : syracuseStep 1702415 = 2553623) B2553623
theorem B4307489 : Blo 1701551 4307489 := bstep (se 2 (by rfl) ⟨1615308, by rfl⟩ : syracuseStep 4307489 = 3230617) B3230617
theorem B2046379 : Blo 1701551 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B1702459 : Blo 1701551 1702459 := bstep (se 1 (by rfl) ⟨1276844, by rfl⟩ : syracuseStep 1702459 = 2553689) B2553689
theorem B2554427 : Blo 1701551 2554427 := bstep (se 1 (by rfl) ⟨1915820, by rfl⟩ : syracuseStep 2554427 = 3831641) B3831641
theorem B3832379 : Blo 1701551 3832379 := bstep (se 1 (by rfl) ⟨2874284, by rfl⟩ : syracuseStep 3832379 = 5748569) B5748569
theorem B2554487 : Blo 1701551 2554487 := bstep (se 1 (by rfl) ⟨1915865, by rfl⟩ : syracuseStep 2554487 = 3831731) B3831731
theorem B1702535 : Blo 1701551 1702535 := bstep (se 1 (by rfl) ⟨1276901, by rfl⟩ : syracuseStep 1702535 = 2553803) B2553803
theorem B1702543 : Blo 1701551 1702543 := bstep (se 1 (by rfl) ⟨1276907, by rfl⟩ : syracuseStep 1702543 = 2553815) B2553815
theorem B2554511 : Blo 1701551 2554511 := bstep (se 1 (by rfl) ⟨1915883, by rfl⟩ : syracuseStep 2554511 = 3831767) B3831767
theorem B2554553 : Blo 1701551 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B3832505 : Blo 1701551 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B1702587 : Blo 1701551 1702587 := bstep (se 1 (by rfl) ⟨1276940, by rfl⟩ : syracuseStep 1702587 = 2553881) B2553881
theorem B4848329 : Blo 1701551 4848329 := bstep (se 2 (by rfl) ⟨1818123, by rfl⟩ : syracuseStep 4848329 = 3636247) B3636247
theorem B2300663 : Blo 1701551 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B1702663 : Blo 1701551 1702663 := bstep (se 1 (by rfl) ⟨1276997, by rfl⟩ : syracuseStep 1702663 = 2553995) B2553995
theorem B2554631 : Blo 1701551 2554631 := bstep (se 1 (by rfl) ⟨1915973, by rfl⟩ : syracuseStep 2554631 = 3831947) B3831947
theorem B1702671 : Blo 1701551 1702671 := bstep (se 1 (by rfl) ⟨1277003, by rfl⟩ : syracuseStep 1702671 = 2554007) B2554007
theorem B1915663 : Blo 1701551 1915663 := bstep (se 1 (by rfl) ⟨1436747, by rfl⟩ : syracuseStep 1915663 = 2873495) B2873495
theorem B2333455 : Blo 1701551 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B2554667 : Blo 1701551 2554667 := bstep (se 1 (by rfl) ⟨1916000, by rfl⟩ : syracuseStep 2554667 = 3832001) B3832001
theorem B3496763 : Blo 1701551 3496763 := bstep (se 1 (by rfl) ⟨2622572, by rfl⟩ : syracuseStep 3496763 = 5245145) B5245145
theorem B4848443 : Blo 1701551 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B1702715 : Blo 1701551 1702715 := bstep (se 1 (by rfl) ⟨1277036, by rfl⟩ : syracuseStep 1702715 = 2554073) B2554073
theorem B2554697 : Blo 1701551 2554697 := bstep (se 2 (by rfl) ⟨958011, by rfl⟩ : syracuseStep 2554697 = 1916023) B1916023
theorem B1702791 : Blo 1701551 1702791 := bstep (se 1 (by rfl) ⟨1277093, by rfl⟩ : syracuseStep 1702791 = 2554187) B2554187
theorem B1702799 : Blo 1701551 1702799 := bstep (se 1 (by rfl) ⟨1277099, by rfl⟩ : syracuseStep 1702799 = 2554199) B2554199
theorem B19659671 : Blo 1701551 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B4848569 : Blo 1701551 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B1702843 : Blo 1701551 1702843 := bstep (se 1 (by rfl) ⟨1277132, by rfl⟩ : syracuseStep 1702843 = 2554265) B2554265
theorem B2554811 : Blo 1701551 2554811 := bstep (se 1 (by rfl) ⟨1916108, by rfl⟩ : syracuseStep 2554811 = 3832217) B3832217
theorem B9698251 : Blo 1701551 9698251 := bstep (se 1 (by rfl) ⟨7273688, by rfl⟩ : syracuseStep 9698251 = 14547377) B14547377
theorem B2554871 : Blo 1701551 2554871 := bstep (se 1 (by rfl) ⟨1916153, by rfl⟩ : syracuseStep 2554871 = 3832307) B3832307
theorem B1702919 : Blo 1701551 1702919 := bstep (se 1 (by rfl) ⟨1277189, by rfl⟩ : syracuseStep 1702919 = 2554379) B2554379
theorem B1702927 : Blo 1701551 1702927 := bstep (se 1 (by rfl) ⟨1277195, by rfl⟩ : syracuseStep 1702927 = 2554391) B2554391
theorem B2554895 : Blo 1701551 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B3832847 : Blo 1701551 3832847 := bstep (se 1 (by rfl) ⟨2874635, by rfl⟩ : syracuseStep 3832847 = 5749271) B5749271
theorem B3832865 : Blo 1701551 3832865 := bstep (se 2 (by rfl) ⟨1437324, by rfl⟩ : syracuseStep 3832865 = 2874649) B2874649
theorem B2554937 : Blo 1701551 2554937 := bstep (se 2 (by rfl) ⟨958101, by rfl⟩ : syracuseStep 2554937 = 1916203) B1916203
theorem B1702971 : Blo 1701551 1702971 := bstep (se 1 (by rfl) ⟨1277228, by rfl⟩ : syracuseStep 1702971 = 2554457) B2554457
theorem B2874487 : Blo 1701551 2874487 := bstep (se 1 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 2874487 = 4311731) B4311731
theorem B1703047 : Blo 1701551 1703047 := bstep (se 1 (by rfl) ⟨1277285, by rfl⟩ : syracuseStep 1703047 = 2554571) B2554571
theorem B2555015 : Blo 1701551 2555015 := bstep (se 1 (by rfl) ⟨1916261, by rfl⟩ : syracuseStep 2555015 = 3832523) B3832523
theorem B1703055 : Blo 1701551 1703055 := bstep (se 1 (by rfl) ⟨1277291, by rfl⟩ : syracuseStep 1703055 = 2554583) B2554583
theorem B2555051 : Blo 1701551 2555051 := bstep (se 1 (by rfl) ⟨1916288, by rfl⟩ : syracuseStep 2555051 = 3832577) B3832577
theorem B1703099 : Blo 1701551 1703099 := bstep (se 1 (by rfl) ⟨1277324, by rfl⟩ : syracuseStep 1703099 = 2554649) B2554649
theorem B2555081 : Blo 1701551 2555081 := bstep (se 2 (by rfl) ⟨958155, by rfl⟩ : syracuseStep 2555081 = 1916311) B1916311
theorem B2153719 : Blo 1701551 2153719 := bstep (se 1 (by rfl) ⟨1615289, by rfl⟩ : syracuseStep 2153719 = 3230579) B3230579
theorem B1703175 : Blo 1701551 1703175 := bstep (se 1 (by rfl) ⟨1277381, by rfl⟩ : syracuseStep 1703175 = 2554763) B2554763
theorem B1916167 : Blo 1701551 1916167 := bstep (se 1 (by rfl) ⟨1437125, by rfl⟩ : syracuseStep 1916167 = 2874251) B2874251
theorem B1703183 : Blo 1701551 1703183 := bstep (se 1 (by rfl) ⟨1277387, by rfl⟩ : syracuseStep 1703183 = 2554775) B2554775
theorem B98139437 : Blo 1701551 98139437 := bstep (se 3 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 98139437 = 36802289) B36802289
theorem B20716859 : Blo 1701551 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B1703227 : Blo 1701551 1703227 := bstep (se 1 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 1703227 = 2554841) B2554841
theorem B2555195 : Blo 1701551 2555195 := bstep (se 1 (by rfl) ⟨1916396, by rfl⟩ : syracuseStep 2555195 = 3832793) B3832793
theorem B2874683 : Blo 1701551 2874683 := bstep (se 1 (by rfl) ⟨2156012, by rfl⟩ : syracuseStep 2874683 = 4312025) B4312025
theorem B2555255 : Blo 1701551 2555255 := bstep (se 1 (by rfl) ⟨1916441, by rfl⟩ : syracuseStep 2555255 = 3832883) B3832883
theorem B1703303 : Blo 1701551 1703303 := bstep (se 1 (by rfl) ⟨1277477, by rfl⟩ : syracuseStep 1703303 = 2554955) B2554955
theorem B1703311 : Blo 1701551 1703311 := bstep (se 1 (by rfl) ⟨1277483, by rfl⟩ : syracuseStep 1703311 = 2554967) B2554967
theorem B2555279 : Blo 1701551 2555279 := bstep (se 1 (by rfl) ⟨1916459, by rfl⟩ : syracuseStep 2555279 = 3832919) B3832919
theorem B2555321 : Blo 1701551 2555321 := bstep (se 2 (by rfl) ⟨958245, by rfl⟩ : syracuseStep 2555321 = 1916491) B1916491
theorem B1703355 : Blo 1701551 1703355 := bstep (se 1 (by rfl) ⟨1277516, by rfl⟩ : syracuseStep 1703355 = 2555033) B2555033
theorem B1916347 : Blo 1701551 1916347 := bstep (se 1 (by rfl) ⟨1437260, by rfl⟩ : syracuseStep 1916347 = 2874521) B2874521
theorem B1703431 : Blo 1701551 1703431 := bstep (se 1 (by rfl) ⟨1277573, by rfl⟩ : syracuseStep 1703431 = 2555147) B2555147
theorem B4308491 : Blo 1701551 4308491 := bstep (se 1 (by rfl) ⟨3231368, by rfl⟩ : syracuseStep 4308491 = 6462737) B6462737
theorem B2424335 : Blo 1701551 2424335 := bstep (se 1 (by rfl) ⟨1818251, by rfl⟩ : syracuseStep 2424335 = 3636503) B3636503
theorem B1703439 : Blo 1701551 1703439 := bstep (se 1 (by rfl) ⟨1277579, by rfl⟩ : syracuseStep 1703439 = 2555159) B2555159
theorem B2154043 : Blo 1701551 2154043 := bstep (se 1 (by rfl) ⟨1615532, by rfl⟩ : syracuseStep 2154043 = 3231065) B3231065
theorem B1703483 : Blo 1701551 1703483 := bstep (se 1 (by rfl) ⟨1277612, by rfl⟩ : syracuseStep 1703483 = 2555225) B2555225
theorem B5455421 : Blo 1701551 5455421 := bstep (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) B2045783
theorem B13811471 : Blo 1701551 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B2301755 : Blo 1701551 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B2424649 : Blo 1701551 2424649 := bstep (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) B1818487
theorem B18415511 : Blo 1701551 18415511 := bstep (se 1 (by rfl) ⟨13811633, by rfl⟩ : syracuseStep 18415511 = 27623267) B27623267
theorem B8617913 : Blo 1701551 8617913 := bstep (se 2 (by rfl) ⟨3231717, by rfl⟩ : syracuseStep 8617913 = 6463435) B6463435
theorem B3882953 : Blo 1701551 3882953 := bstep (se 2 (by rfl) ⟨1456107, by rfl⟩ : syracuseStep 3882953 = 2912215) B2912215
theorem B23306251 : Blo 1701551 23306251 := bstep (se 1 (by rfl) ⟨17479688, by rfl⟩ : syracuseStep 23306251 = 34959377) B34959377
theorem B16367645 : Blo 1701551 16367645 := bstep (se 3 (by rfl) ⟨3068933, by rfl⟩ : syracuseStep 16367645 = 6137867) B6137867
theorem B5742953 : Blo 1701551 5742953 := bstep (se 2 (by rfl) ⟨2153607, by rfl⟩ : syracuseStep 5742953 = 4307215) B4307215
theorem B7275041 : Blo 1701551 7275041 := bstep (se 2 (by rfl) ⟨2728140, by rfl⟩ : syracuseStep 7275041 = 5456281) B5456281
theorem B3277351 : Blo 1701551 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B2728505 : Blo 1701551 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B6554209 : Blo 1701551 6554209 := bstep (se 2 (by rfl) ⟨2457828, by rfl⟩ : syracuseStep 6554209 = 4915657) B4915657
theorem B5743547 : Blo 1701551 5743547 := bstep (se 1 (by rfl) ⟨4307660, by rfl⟩ : syracuseStep 5743547 = 8615321) B8615321
theorem B11052227 : Blo 1701551 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B49063157 : Blo 1701551 49063157 := bstep (se 5 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 49063157 = 4599671) B4599671
theorem B6464893 : Blo 1701551 6464893 := bstep (se 3 (by rfl) ⟨1212167, by rfl⟩ : syracuseStep 6464893 = 2424335) B2424335
theorem B10904975 : Blo 1701551 10904975 := bstep (se 1 (by rfl) ⟨8178731, by rfl⟩ : syracuseStep 10904975 = 16357463) B16357463
theorem B4982159 : Blo 1701551 4982159 := bstep (se 1 (by rfl) ⟨3736619, by rfl⟩ : syracuseStep 4982159 = 7473239) B7473239
theorem B12445093 : Blo 1701551 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B18417061 : Blo 1701551 18417061 := bstep (se 4 (by rfl) ⟨1726599, by rfl⟩ : syracuseStep 18417061 = 3453199) B3453199
theorem B5604851 : Blo 1701551 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B4310567 : Blo 1701551 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B29091473 : Blo 1701551 29091473 := bstep (se 2 (by rfl) ⟨10909302, by rfl⟩ : syracuseStep 29091473 = 21818605) B21818605
theorem B7276355 : Blo 1701551 7276355 := bstep (se 1 (by rfl) ⟨5457266, by rfl⟩ : syracuseStep 7276355 = 10914533) B10914533
theorem B4310891 : Blo 1701551 4310891 := bstep (se 1 (by rfl) ⟨3233168, by rfl⟩ : syracuseStep 4310891 = 6466337) B6466337
theorem B9201701 : Blo 1701551 9201701 := bstep (se 4 (by rfl) ⟨862659, by rfl⟩ : syracuseStep 9201701 = 1725319) B1725319
theorem B6138013 : Blo 1701551 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B9701693 : Blo 1701551 9701693 := bstep (se 3 (by rfl) ⟨1819067, by rfl⟩ : syracuseStep 9701693 = 3638135) B3638135
theorem B4311539 : Blo 1701551 4311539 := bstep (se 1 (by rfl) ⟨3233654, by rfl⟩ : syracuseStep 4311539 = 6467309) B6467309
theorem B5745275 : Blo 1701551 5745275 := bstep (se 1 (by rfl) ⟨4308956, by rfl⟩ : syracuseStep 5745275 = 8617913) B8617913
theorem B13806281 : Blo 1701551 13806281 := bstep (se 2 (by rfl) ⟨5177355, by rfl⟩ : syracuseStep 13806281 = 10354711) B10354711
theorem B4311751 : Blo 1701551 4311751 := bstep (se 1 (by rfl) ⟨3233813, by rfl⟩ : syracuseStep 4311751 = 6467627) B6467627
theorem B10357507 : Blo 1701551 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B5745437 : Blo 1701551 5745437 := bstep (se 3 (by rfl) ⟨1077269, by rfl⟩ : syracuseStep 5745437 = 2154539) B2154539
theorem B8620829 : Blo 1701551 8620829 := bstep (se 3 (by rfl) ⟨1616405, by rfl⟩ : syracuseStep 8620829 = 3232811) B3232811
theorem B3828743 : Blo 1701551 3828743 := bstep (se 1 (by rfl) ⟨2871557, by rfl⟩ : syracuseStep 3828743 = 5743115) B5743115
theorem B26225687 : Blo 1701551 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B3828815 : Blo 1701551 3828815 := bstep (se 1 (by rfl) ⟨2871611, by rfl⟩ : syracuseStep 3828815 = 5743223) B5743223
theorem B209726657 : Blo 1701551 209726657 := bstep (se 2 (by rfl) ⟨78647496, by rfl⟩ : syracuseStep 209726657 = 157294993) B157294993
theorem B9694403 : Blo 1701551 9694403 := bstep (se 1 (by rfl) ⟨7270802, by rfl⟩ : syracuseStep 9694403 = 14541605) B14541605
theorem B10095895 : Blo 1701551 10095895 := bstep (se 1 (by rfl) ⟨7571921, by rfl⟩ : syracuseStep 10095895 = 15143843) B15143843
theorem B5246333 : Blo 1701551 5246333 := bstep (se 3 (by rfl) ⟨983687, by rfl⟩ : syracuseStep 5246333 = 1967375) B1967375
theorem B3067319 : Blo 1701551 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B3829211 : Blo 1701551 3829211 := bstep (se 1 (by rfl) ⟨2871908, by rfl⟩ : syracuseStep 3829211 = 5743817) B5743817
theorem B5746139 : Blo 1701551 5746139 := bstep (se 1 (by rfl) ⟨4309604, by rfl⟩ : syracuseStep 5746139 = 8619209) B8619209
theorem B6467111 : Blo 1701551 6467111 := bstep (se 1 (by rfl) ⟨4850333, by rfl⟩ : syracuseStep 6467111 = 9700667) B9700667
theorem B10907459 : Blo 1701551 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B3829679 : Blo 1701551 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B12931001 : Blo 1701551 12931001 := bstep (se 2 (by rfl) ⟨4849125, by rfl⟩ : syracuseStep 12931001 = 9698251) B9698251
theorem B23310413 : Blo 1701551 23310413 := bstep (se 3 (by rfl) ⟨4370702, by rfl⟩ : syracuseStep 23310413 = 8741405) B8741405
theorem B5746841 : Blo 1701551 5746841 := bstep (se 2 (by rfl) ⟨2155065, by rfl⟩ : syracuseStep 5746841 = 4310131) B4310131
theorem B3829931 : Blo 1701551 3829931 := bstep (se 1 (by rfl) ⟨2872448, by rfl⟩ : syracuseStep 3829931 = 5744897) B5744897
theorem B36835505 : Blo 1701551 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B3231991 : Blo 1701551 3231991 := bstep (se 1 (by rfl) ⟨2423993, by rfl⟩ : syracuseStep 3231991 = 4847987) B4847987
theorem B7270667 : Blo 1701551 7270667 := bstep (se 1 (by rfl) ⟨5453000, by rfl⟩ : syracuseStep 7270667 = 10906001) B10906001
theorem B2871625 : Blo 1701551 2871625 := bstep (se 2 (by rfl) ⟨1076859, by rfl⟩ : syracuseStep 2871625 = 2153719) B2153719
theorem B2871659 : Blo 1701551 2871659 := bstep (se 1 (by rfl) ⟨2153744, by rfl⟩ : syracuseStep 2871659 = 4307489) B4307489
theorem B24539597 : Blo 1701551 24539597 := bstep (se 3 (by rfl) ⟨4601174, by rfl⟩ : syracuseStep 24539597 = 9202349) B9202349
theorem B3232219 : Blo 1701551 3232219 := bstep (se 1 (by rfl) ⟨2424164, by rfl⟩ : syracuseStep 3232219 = 4848329) B4848329
theorem B6468083 : Blo 1701551 6468083 := bstep (se 1 (by rfl) ⟨4851062, by rfl⟩ : syracuseStep 6468083 = 9702125) B9702125
theorem B4911641 : Blo 1701551 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B2331175 : Blo 1701551 2331175 := bstep (se 1 (by rfl) ⟨1748381, by rfl⟩ : syracuseStep 2331175 = 3496763) B3496763
theorem B3232295 : Blo 1701551 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B2552399 : Blo 1701551 2552399 := bstep (se 1 (by rfl) ⟨1914299, by rfl⟩ : syracuseStep 2552399 = 3828599) B3828599
theorem B2044495 : Blo 1701551 2044495 := bstep (se 1 (by rfl) ⟨1533371, by rfl⟩ : syracuseStep 2044495 = 3066743) B3066743
theorem B3232379 : Blo 1701551 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B2552519 : Blo 1701551 2552519 := bstep (se 1 (by rfl) ⟨1914389, by rfl⟩ : syracuseStep 2552519 = 3828779) B3828779
theorem B3830471 : Blo 1701551 3830471 := bstep (se 1 (by rfl) ⟨2872853, by rfl⟩ : syracuseStep 3830471 = 5745707) B5745707
theorem B2872057 : Blo 1701551 2872057 := bstep (se 2 (by rfl) ⟨1077021, by rfl⟩ : syracuseStep 2872057 = 2154043) B2154043
theorem B6222665 : Blo 1701551 6222665 := bstep (se 2 (by rfl) ⟨2333499, by rfl⟩ : syracuseStep 6222665 = 4666999) B4666999
theorem B2552681 : Blo 1701551 2552681 := bstep (se 2 (by rfl) ⟨957255, by rfl⟩ : syracuseStep 2552681 = 1914511) B1914511
theorem B65426291 : Blo 1701551 65426291 := bstep (se 1 (by rfl) ⟨49069718, by rfl⟩ : syracuseStep 65426291 = 98139437) B98139437
theorem B2552759 : Blo 1701551 2552759 := bstep (se 1 (by rfl) ⟨1914569, by rfl⟩ : syracuseStep 2552759 = 3829139) B3829139
theorem B2552795 : Blo 1701551 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B2872327 : Blo 1701551 2872327 := bstep (se 1 (by rfl) ⟨2154245, by rfl⟩ : syracuseStep 2872327 = 4308491) B4308491
theorem B5174351 : Blo 1701551 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B3232865 : Blo 1701551 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B26211529 : Blo 1701551 26211529 := bstep (se 2 (by rfl) ⟨9829323, by rfl⟩ : syracuseStep 26211529 = 19658647) B19658647
theorem B36811979 : Blo 1701551 36811979 := bstep (se 1 (by rfl) ⟨27608984, by rfl⟩ : syracuseStep 36811979 = 55217969) B55217969
theorem B8615159 : Blo 1701551 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B12277007 : Blo 1701551 12277007 := bstep (se 1 (by rfl) ⟨9207755, by rfl⟩ : syracuseStep 12277007 = 18415511) B18415511
theorem B12924197 : Blo 1701551 12924197 := bstep (se 4 (by rfl) ⟨1211643, by rfl⟩ : syracuseStep 12924197 = 2423287) B2423287
theorem B5748029 : Blo 1701551 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B2553263 : Blo 1701551 2553263 := bstep (se 1 (by rfl) ⟨1914947, by rfl⟩ : syracuseStep 2553263 = 3829895) B3829895
theorem B2872759 : Blo 1701551 2872759 := bstep (se 1 (by rfl) ⟨2154569, by rfl⟩ : syracuseStep 2872759 = 4309139) B4309139
theorem B1914331 : Blo 1701551 1914331 := bstep (se 1 (by rfl) ⟨1435748, by rfl⟩ : syracuseStep 1914331 = 2871497) B2871497
theorem B2553353 : Blo 1701551 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B5453345 : Blo 1701551 5453345 := bstep (se 2 (by rfl) ⟨2045004, by rfl⟩ : syracuseStep 5453345 = 4090009) B4090009
theorem B2553383 : Blo 1701551 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B8181287 : Blo 1701551 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B3831335 : Blo 1701551 3831335 := bstep (se 1 (by rfl) ⟨2873501, by rfl⟩ : syracuseStep 3831335 = 5747003) B5747003
theorem B2553467 : Blo 1701551 2553467 := bstep (se 1 (by rfl) ⟨1915100, by rfl⟩ : syracuseStep 2553467 = 3830201) B3830201
theorem B2872955 : Blo 1701551 2872955 := bstep (se 1 (by rfl) ⟨2154716, by rfl⟩ : syracuseStep 2872955 = 4309433) B4309433
theorem B1701551 : Blo 1701551 1701551 := bstep (se 1 (by rfl) ⟨1276163, by rfl⟩ : syracuseStep 1701551 = 2552327) B2552327
theorem B1701575 : Blo 1701551 1701575 := bstep (se 1 (by rfl) ⟨1276181, by rfl⟩ : syracuseStep 1701575 = 2552363) B2552363
theorem B4847303 : Blo 1701551 4847303 := bstep (se 1 (by rfl) ⟨3635477, by rfl⟩ : syracuseStep 4847303 = 7270955) B7270955
theorem B1701595 : Blo 1701551 1701595 := bstep (se 1 (by rfl) ⟨1276196, by rfl⟩ : syracuseStep 1701595 = 2552393) B2552393
theorem B8615645 : Blo 1701551 8615645 := bstep (se 3 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 8615645 = 3230867) B3230867
theorem B2553593 : Blo 1701551 2553593 := bstep (se 2 (by rfl) ⟨957597, by rfl⟩ : syracuseStep 2553593 = 1915195) B1915195
theorem B1701671 : Blo 1701551 1701671 := bstep (se 1 (by rfl) ⟨1276253, by rfl⟩ : syracuseStep 1701671 = 2552507) B2552507
theorem B9697067 : Blo 1701551 9697067 := bstep (se 1 (by rfl) ⟨7272800, by rfl⟩ : syracuseStep 9697067 = 14545601) B14545601
theorem B1701711 : Blo 1701551 1701711 := bstep (se 1 (by rfl) ⟨1276283, by rfl⟩ : syracuseStep 1701711 = 2552567) B2552567
theorem B1701727 : Blo 1701551 1701727 := bstep (se 1 (by rfl) ⟨1276295, by rfl⟩ : syracuseStep 1701727 = 2552591) B2552591
theorem B6461279 : Blo 1701551 6461279 := bstep (se 1 (by rfl) ⟨4845959, by rfl⟩ : syracuseStep 6461279 = 9691919) B9691919
theorem B2553695 : Blo 1701551 2553695 := bstep (se 1 (by rfl) ⟨1915271, by rfl⟩ : syracuseStep 2553695 = 3830543) B3830543
theorem B2553707 : Blo 1701551 2553707 := bstep (se 1 (by rfl) ⟨1915280, by rfl⟩ : syracuseStep 2553707 = 3830561) B3830561
theorem B6903659 : Blo 1701551 6903659 := bstep (se 1 (by rfl) ⟨5177744, by rfl⟩ : syracuseStep 6903659 = 10355489) B10355489
theorem B3831659 : Blo 1701551 3831659 := bstep (se 1 (by rfl) ⟨2873744, by rfl⟩ : syracuseStep 3831659 = 5747489) B5747489
theorem B1701755 : Blo 1701551 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B3831713 : Blo 1701551 3831713 := bstep (se 2 (by rfl) ⟨1436892, by rfl⟩ : syracuseStep 3831713 = 2873785) B2873785
theorem B1701807 : Blo 1701551 1701807 := bstep (se 1 (by rfl) ⟨1276355, by rfl⟩ : syracuseStep 1701807 = 2552711) B2552711
theorem B1914799 : Blo 1701551 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B1701831 : Blo 1701551 1701831 := bstep (se 1 (by rfl) ⟨1276373, by rfl⟩ : syracuseStep 1701831 = 2552747) B2552747
theorem B1701851 : Blo 1701551 1701851 := bstep (se 1 (by rfl) ⟨1276388, by rfl⟩ : syracuseStep 1701851 = 2552777) B2552777
theorem B2873353 : Blo 1701551 2873353 := bstep (se 2 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 2873353 = 2155015) B2155015
theorem B1701927 : Blo 1701551 1701927 := bstep (se 1 (by rfl) ⟨1276445, by rfl⟩ : syracuseStep 1701927 = 2552891) B2552891
theorem B1701967 : Blo 1701551 1701967 := bstep (se 1 (by rfl) ⟨1276475, by rfl⟩ : syracuseStep 1701967 = 2552951) B2552951
theorem B2553935 : Blo 1701551 2553935 := bstep (se 1 (by rfl) ⟨1915451, by rfl⟩ : syracuseStep 2553935 = 3830903) B3830903
theorem B1701983 : Blo 1701551 1701983 := bstep (se 1 (by rfl) ⟨1276487, by rfl⟩ : syracuseStep 1701983 = 2552975) B2552975
theorem B1702011 : Blo 1701551 1702011 := bstep (se 1 (by rfl) ⟨1276508, by rfl⟩ : syracuseStep 1702011 = 2553017) B2553017
theorem B5748893 : Blo 1701551 5748893 := bstep (se 3 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 5748893 = 2155835) B2155835
theorem B2873515 : Blo 1701551 2873515 := bstep (se 1 (by rfl) ⟨2155136, by rfl⟩ : syracuseStep 2873515 = 4310273) B4310273
theorem B1702063 : Blo 1701551 1702063 := bstep (se 1 (by rfl) ⟨1276547, by rfl⟩ : syracuseStep 1702063 = 2553095) B2553095
theorem B1702087 : Blo 1701551 1702087 := bstep (se 1 (by rfl) ⟨1276565, by rfl⟩ : syracuseStep 1702087 = 2553131) B2553131
theorem B2554055 : Blo 1701551 2554055 := bstep (se 1 (by rfl) ⟨1915541, by rfl⟩ : syracuseStep 2554055 = 3831083) B3831083
theorem B1702107 : Blo 1701551 1702107 := bstep (se 1 (by rfl) ⟨1276580, by rfl⟩ : syracuseStep 1702107 = 2553161) B2553161
theorem B3832055 : Blo 1701551 3832055 := bstep (se 1 (by rfl) ⟨2874041, by rfl⟩ : syracuseStep 3832055 = 5748083) B5748083
theorem B9328907 : Blo 1701551 9328907 := bstep (se 1 (by rfl) ⟨6996680, by rfl⟩ : syracuseStep 9328907 = 13993361) B13993361
theorem B1702183 : Blo 1701551 1702183 := bstep (se 1 (by rfl) ⟨1276637, by rfl⟩ : syracuseStep 1702183 = 2553275) B2553275
theorem B1702223 : Blo 1701551 1702223 := bstep (se 1 (by rfl) ⟨1276667, by rfl⟩ : syracuseStep 1702223 = 2553335) B2553335
theorem B1702239 : Blo 1701551 1702239 := bstep (se 1 (by rfl) ⟨1276679, by rfl⟩ : syracuseStep 1702239 = 2553359) B2553359
theorem B1915231 : Blo 1701551 1915231 := bstep (se 1 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 1915231 = 2872847) B2872847
theorem B2554217 : Blo 1701551 2554217 := bstep (se 2 (by rfl) ⟨957831, by rfl⟩ : syracuseStep 2554217 = 1915663) B1915663
theorem B1702267 : Blo 1701551 1702267 := bstep (se 1 (by rfl) ⟨1276700, by rfl⟩ : syracuseStep 1702267 = 2553401) B2553401
theorem B1702319 : Blo 1701551 1702319 := bstep (se 1 (by rfl) ⟨1276739, by rfl⟩ : syracuseStep 1702319 = 2553479) B2553479
theorem B2554295 : Blo 1701551 2554295 := bstep (se 1 (by rfl) ⟨1915721, by rfl⟩ : syracuseStep 2554295 = 3831443) B3831443
theorem B1702343 : Blo 1701551 1702343 := bstep (se 1 (by rfl) ⟨1276757, by rfl⟩ : syracuseStep 1702343 = 2553515) B2553515
theorem B35404235 : Blo 1701551 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B3635675 : Blo 1701551 3635675 := bstep (se 1 (by rfl) ⟨2726756, by rfl⟩ : syracuseStep 3635675 = 5453513) B5453513
theorem B1702363 : Blo 1701551 1702363 := bstep (se 1 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 1702363 = 2553545) B2553545
theorem B2554331 : Blo 1701551 2554331 := bstep (se 1 (by rfl) ⟨1915748, by rfl⟩ : syracuseStep 2554331 = 3831497) B3831497
theorem B2873819 : Blo 1701551 2873819 := bstep (se 1 (by rfl) ⟨2155364, by rfl⟩ : syracuseStep 2873819 = 4310729) B4310729
theorem B6461977 : Blo 1701551 6461977 := bstep (se 2 (by rfl) ⟨2423241, by rfl⟩ : syracuseStep 6461977 = 4846483) B4846483
theorem B1702439 : Blo 1701551 1702439 := bstep (se 1 (by rfl) ⟨1276829, by rfl⟩ : syracuseStep 1702439 = 2553659) B2553659
theorem B1702479 : Blo 1701551 1702479 := bstep (se 1 (by rfl) ⟨1276859, by rfl⟩ : syracuseStep 1702479 = 2553719) B2553719
theorem B1702495 : Blo 1701551 1702495 := bstep (se 1 (by rfl) ⟨1276871, by rfl⟩ : syracuseStep 1702495 = 2553743) B2553743
theorem B1702523 : Blo 1701551 1702523 := bstep (se 1 (by rfl) ⟨1276892, by rfl⟩ : syracuseStep 1702523 = 2553785) B2553785
theorem B6306443 : Blo 1701551 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B1702575 : Blo 1701551 1702575 := bstep (se 1 (by rfl) ⟨1276931, by rfl⟩ : syracuseStep 1702575 = 2553863) B2553863
theorem B5749433 : Blo 1701551 5749433 := bstep (se 2 (by rfl) ⟨2156037, by rfl⟩ : syracuseStep 5749433 = 4312075) B4312075
theorem B5176007 : Blo 1701551 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B1702599 : Blo 1701551 1702599 := bstep (se 1 (by rfl) ⟨1276949, by rfl⟩ : syracuseStep 1702599 = 2553899) B2553899
theorem B1915591 : Blo 1701551 1915591 := bstep (se 1 (by rfl) ⟨1436693, by rfl⟩ : syracuseStep 1915591 = 2873387) B2873387
theorem B2874055 : Blo 1701551 2874055 := bstep (se 1 (by rfl) ⟨2155541, by rfl⟩ : syracuseStep 2874055 = 4311083) B4311083
theorem B7092947 : Blo 1701551 7092947 := bstep (se 1 (by rfl) ⟨5319710, by rfl⟩ : syracuseStep 7092947 = 10639421) B10639421
theorem B1702619 : Blo 1701551 1702619 := bstep (se 1 (by rfl) ⟨1276964, by rfl⟩ : syracuseStep 1702619 = 2553929) B2553929
theorem B12933917 : Blo 1701551 12933917 := bstep (se 3 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 12933917 = 4850219) B4850219
theorem B1702695 : Blo 1701551 1702695 := bstep (se 1 (by rfl) ⟨1277021, by rfl⟩ : syracuseStep 1702695 = 2554043) B2554043
theorem B6462251 : Blo 1701551 6462251 := bstep (se 1 (by rfl) ⟨4846688, by rfl⟩ : syracuseStep 6462251 = 9693377) B9693377
theorem B6462281 : Blo 1701551 6462281 := bstep (se 2 (by rfl) ⟨2423355, by rfl⟩ : syracuseStep 6462281 = 4846711) B4846711
theorem B3832649 : Blo 1701551 3832649 := bstep (se 2 (by rfl) ⟨1437243, by rfl⟩ : syracuseStep 3832649 = 2874487) B2874487
theorem B1702735 : Blo 1701551 1702735 := bstep (se 1 (by rfl) ⟨1277051, by rfl⟩ : syracuseStep 1702735 = 2554103) B2554103
theorem B1702751 : Blo 1701551 1702751 := bstep (se 1 (by rfl) ⟨1277063, by rfl⟩ : syracuseStep 1702751 = 2554127) B2554127
theorem B2874217 : Blo 1701551 2874217 := bstep (se 2 (by rfl) ⟨1077831, by rfl⟩ : syracuseStep 2874217 = 2155663) B2155663
theorem B1702779 : Blo 1701551 1702779 := bstep (se 1 (by rfl) ⟨1277084, by rfl⟩ : syracuseStep 1702779 = 2554169) B2554169
theorem B13278097 : Blo 1701551 13278097 := bstep (se 2 (by rfl) ⟨4979286, by rfl⟩ : syracuseStep 13278097 = 9958573) B9958573
theorem B1702831 : Blo 1701551 1702831 := bstep (se 1 (by rfl) ⟨1277123, by rfl⟩ : syracuseStep 1702831 = 2554247) B2554247
theorem B2554799 : Blo 1701551 2554799 := bstep (se 1 (by rfl) ⟨1916099, by rfl⟩ : syracuseStep 2554799 = 3832199) B3832199
theorem B1702855 : Blo 1701551 1702855 := bstep (se 1 (by rfl) ⟨1277141, by rfl⟩ : syracuseStep 1702855 = 2554283) B2554283
theorem B1702875 : Blo 1701551 1702875 := bstep (se 1 (by rfl) ⟨1277156, by rfl⟩ : syracuseStep 1702875 = 2554313) B2554313
theorem B4307975 : Blo 1701551 4307975 := bstep (se 1 (by rfl) ⟨3230981, by rfl⟩ : syracuseStep 4307975 = 6461963) B6461963
theorem B2554889 : Blo 1701551 2554889 := bstep (se 2 (by rfl) ⟨958083, by rfl⟩ : syracuseStep 2554889 = 1916167) B1916167
theorem B1702951 : Blo 1701551 1702951 := bstep (se 1 (by rfl) ⟨1277213, by rfl⟩ : syracuseStep 1702951 = 2554427) B2554427
theorem B2554919 : Blo 1701551 2554919 := bstep (se 1 (by rfl) ⟨1916189, by rfl⟩ : syracuseStep 2554919 = 3832379) B3832379
theorem B4308025 : Blo 1701551 4308025 := bstep (se 2 (by rfl) ⟨1615509, by rfl⟩ : syracuseStep 4308025 = 3231019) B3231019
theorem B1702991 : Blo 1701551 1702991 := bstep (se 1 (by rfl) ⟨1277243, by rfl⟩ : syracuseStep 1702991 = 2554487) B2554487
theorem B1703007 : Blo 1701551 1703007 := bstep (se 1 (by rfl) ⟨1277255, by rfl⟩ : syracuseStep 1703007 = 2554511) B2554511
theorem B1703035 : Blo 1701551 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B2555003 : Blo 1701551 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B2727083 : Blo 1701551 2727083 := bstep (se 1 (by rfl) ⟨2045312, by rfl⟩ : syracuseStep 2727083 = 4090625) B4090625
theorem B1703087 : Blo 1701551 1703087 := bstep (se 1 (by rfl) ⟨1277315, by rfl⟩ : syracuseStep 1703087 = 2554631) B2554631
theorem B1703111 : Blo 1701551 1703111 := bstep (se 1 (by rfl) ⟨1277333, by rfl⟩ : syracuseStep 1703111 = 2554667) B2554667
theorem B1703131 : Blo 1701551 1703131 := bstep (se 1 (by rfl) ⟨1277348, by rfl⟩ : syracuseStep 1703131 = 2554697) B2554697
theorem B22109431 : Blo 1701551 22109431 := bstep (se 1 (by rfl) ⟨16582073, by rfl⟩ : syracuseStep 22109431 = 33164147) B33164147
theorem B2555129 : Blo 1701551 2555129 := bstep (se 2 (by rfl) ⟨958173, by rfl⟩ : syracuseStep 2555129 = 1916347) B1916347
theorem B13106447 : Blo 1701551 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B1703207 : Blo 1701551 1703207 := bstep (se 1 (by rfl) ⟨1277405, by rfl⟩ : syracuseStep 1703207 = 2554811) B2554811
theorem B6135101 : Blo 1701551 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B1703247 : Blo 1701551 1703247 := bstep (se 1 (by rfl) ⟨1277435, by rfl⟩ : syracuseStep 1703247 = 2554871) B2554871
theorem B1703263 : Blo 1701551 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2555231 : Blo 1701551 2555231 := bstep (se 1 (by rfl) ⟨1916423, by rfl⟩ : syracuseStep 2555231 = 3832847) B3832847
theorem B4308329 : Blo 1701551 4308329 := bstep (se 2 (by rfl) ⟨1615623, by rfl⟩ : syracuseStep 4308329 = 3231247) B3231247
theorem B2555243 : Blo 1701551 2555243 := bstep (se 1 (by rfl) ⟨1916432, by rfl⟩ : syracuseStep 2555243 = 3832865) B3832865
theorem B1703291 : Blo 1701551 1703291 := bstep (se 1 (by rfl) ⟨1277468, by rfl⟩ : syracuseStep 1703291 = 2554937) B2554937
theorem B6905231 : Blo 1701551 6905231 := bstep (se 1 (by rfl) ⟨5178923, by rfl⟩ : syracuseStep 6905231 = 10357847) B10357847
theorem B10911149 : Blo 1701551 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1703343 : Blo 1701551 1703343 := bstep (se 1 (by rfl) ⟨1277507, by rfl⟩ : syracuseStep 1703343 = 2555015) B2555015
theorem B1703367 : Blo 1701551 1703367 := bstep (se 1 (by rfl) ⟨1277525, by rfl⟩ : syracuseStep 1703367 = 2555051) B2555051
theorem B2153947 : Blo 1701551 2153947 := bstep (se 1 (by rfl) ⟨1615460, by rfl⟩ : syracuseStep 2153947 = 3230921) B3230921
theorem B1703387 : Blo 1701551 1703387 := bstep (se 1 (by rfl) ⟨1277540, by rfl⟩ : syracuseStep 1703387 = 2555081) B2555081
theorem B13811239 : Blo 1701551 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B1703463 : Blo 1701551 1703463 := bstep (se 1 (by rfl) ⟨1277597, by rfl⟩ : syracuseStep 1703463 = 2555195) B2555195
theorem B1916455 : Blo 1701551 1916455 := bstep (se 1 (by rfl) ⟨1437341, by rfl⟩ : syracuseStep 1916455 = 2874683) B2874683
theorem B1703503 : Blo 1701551 1703503 := bstep (se 1 (by rfl) ⟨1277627, by rfl⟩ : syracuseStep 1703503 = 2555255) B2555255
theorem B1703519 : Blo 1701551 1703519 := bstep (se 1 (by rfl) ⟨1277639, by rfl⟩ : syracuseStep 1703519 = 2555279) B2555279
theorem B1703547 : Blo 1701551 1703547 := bstep (se 1 (by rfl) ⟨1277660, by rfl⟩ : syracuseStep 1703547 = 2555321) B2555321
theorem B3636947 : Blo 1701551 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B33169133 : Blo 1701551 33169133 := bstep (se 3 (by rfl) ⟨6219212, by rfl⟩ : syracuseStep 33169133 = 12438425) B12438425
theorem B9207647 : Blo 1701551 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B2588635 : Blo 1701551 2588635 := bstep (se 1 (by rfl) ⟨1941476, by rfl⟩ : syracuseStep 2588635 = 3882953) B3882953
theorem B10911763 : Blo 1701551 10911763 := bstep (se 1 (by rfl) ⟨8183822, by rfl⟩ : syracuseStep 10911763 = 16367645) B16367645
theorem B15540275 : Blo 1701551 15540275 := bstep (se 1 (by rfl) ⟨11655206, by rfl⟩ : syracuseStep 15540275 = 23310413) B23310413
theorem B8184017 : Blo 1701551 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B16359731 : Blo 1701551 16359731 := bstep (se 1 (by rfl) ⟨12269798, by rfl⟩ : syracuseStep 16359731 = 24539597) B24539597
theorem B4309321 : Blo 1701551 4309321 := bstep (se 2 (by rfl) ⟨1615995, by rfl⟩ : syracuseStep 4309321 = 3231991) B3231991
theorem B4850027 : Blo 1701551 4850027 := bstep (se 1 (by rfl) ⟨3637520, by rfl⟩ : syracuseStep 4850027 = 7275041) B7275041
theorem B2154863 : Blo 1701551 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B2154919 : Blo 1701551 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B4309625 : Blo 1701551 4309625 := bstep (se 2 (by rfl) ⟨1616109, by rfl⟩ : syracuseStep 4309625 = 3232219) B3232219
theorem B3449567 : Blo 1701551 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B2155243 : Blo 1701551 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B5743439 : Blo 1701551 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B8184671 : Blo 1701551 8184671 := bstep (se 1 (by rfl) ⟨6138503, by rfl⟩ : syracuseStep 8184671 = 12277007) B12277007
theorem B3736567 : Blo 1701551 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B5743763 : Blo 1701551 5743763 := bstep (se 1 (by rfl) ⟨4307822, by rfl⟩ : syracuseStep 5743763 = 8615645) B8615645
theorem B6464711 : Blo 1701551 6464711 := bstep (se 1 (by rfl) ⟨4848533, by rfl⟩ : syracuseStep 6464711 = 9697067) B9697067
theorem B4850903 : Blo 1701551 4850903 := bstep (se 1 (by rfl) ⟨3638177, by rfl⟩ : syracuseStep 4850903 = 7276355) B7276355
theorem B5744033 : Blo 1701551 5744033 := bstep (se 2 (by rfl) ⟨2154012, by rfl⟩ : syracuseStep 5744033 = 4308025) B4308025
theorem B14542253 : Blo 1701551 14542253 := bstep (se 3 (by rfl) ⟨2726672, by rfl⟩ : syracuseStep 14542253 = 5453345) B5453345
theorem B7276013 : Blo 1701551 7276013 := bstep (se 3 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 7276013 = 2728505) B2728505
theorem B6219271 : Blo 1701551 6219271 := bstep (se 1 (by rfl) ⟨4664453, by rfl⟩ : syracuseStep 6219271 = 9328907) B9328907
theorem B34948705 : Blo 1701551 34948705 := bstep (se 2 (by rfl) ⟨13105764, by rfl⟩ : syracuseStep 34948705 = 26211529) B26211529
theorem B23602823 : Blo 1701551 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B4204295 : Blo 1701551 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B3450671 : Blo 1701551 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B4728631 : Blo 1701551 4728631 := bstep (se 1 (by rfl) ⟨3546473, by rfl⟩ : syracuseStep 4728631 = 7092947) B7092947
theorem B8619857 : Blo 1701551 8619857 := bstep (se 2 (by rfl) ⟨3232446, by rfl⟩ : syracuseStep 8619857 = 6464893) B6464893
theorem B88451021 : Blo 1701551 88451021 := bstep (se 3 (by rfl) ⟨16584566, by rfl⟩ : syracuseStep 88451021 = 33169133) B33169133
theorem B17483791 : Blo 1701551 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B4090067 : Blo 1701551 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B4311407 : Blo 1701551 4311407 := bstep (se 1 (by rfl) ⟨3233555, by rfl⟩ : syracuseStep 4311407 = 6467111) B6467111
theorem B6138431 : Blo 1701551 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B3451513 : Blo 1701551 3451513 := bstep (se 2 (by rfl) ⟨1294317, by rfl⟩ : syracuseStep 3451513 = 2588635) B2588635
theorem B8620667 : Blo 1701551 8620667 := bstep (se 1 (by rfl) ⟨6465500, by rfl⟩ : syracuseStep 8620667 = 12931001) B12931001
theorem B31075001 : Blo 1701551 31075001 := bstep (se 2 (by rfl) ⟨11653125, by rfl⟩ : syracuseStep 31075001 = 23306251) B23306251
theorem B3828635 : Blo 1701551 3828635 := bstep (se 1 (by rfl) ⟨2871476, by rfl⟩ : syracuseStep 3828635 = 5742953) B5742953
theorem B4312055 : Blo 1701551 4312055 := bstep (se 1 (by rfl) ⟨3234041, by rfl⟩ : syracuseStep 4312055 = 6468083) B6468083
theorem B3828833 : Blo 1701551 3828833 := bstep (se 2 (by rfl) ⟨1435812, by rfl⟩ : syracuseStep 3828833 = 2871625) B2871625
theorem B4148443 : Blo 1701551 4148443 := bstep (se 1 (by rfl) ⟨3111332, by rfl⟩ : syracuseStep 4148443 = 6222665) B6222665
theorem B43617527 : Blo 1701551 43617527 := bstep (se 1 (by rfl) ⟨32713145, by rfl⟩ : syracuseStep 43617527 = 65426291) B65426291
theorem B3829031 : Blo 1701551 3829031 := bstep (se 1 (by rfl) ⟨2871773, by rfl⟩ : syracuseStep 3829031 = 5743547) B5743547
theorem B3108233 : Blo 1701551 3108233 := bstep (se 2 (by rfl) ⟨1165587, by rfl⟩ : syracuseStep 3108233 = 2331175) B2331175
theorem B4369801 : Blo 1701551 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B7269983 : Blo 1701551 7269983 := bstep (se 1 (by rfl) ⟨5452487, by rfl⟩ : syracuseStep 7269983 = 10904975) B10904975
theorem B3829409 : Blo 1701551 3829409 := bstep (se 2 (by rfl) ⟨1436028, by rfl⟩ : syracuseStep 3829409 = 2872057) B2872057
theorem B19394315 : Blo 1701551 19394315 := bstep (se 1 (by rfl) ⟨14545736, by rfl⟩ : syracuseStep 19394315 = 29091473) B29091473
theorem B8179517 : Blo 1701551 8179517 := bstep (se 3 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 8179517 = 3067319) B3067319
theorem B3829769 : Blo 1701551 3829769 := bstep (se 2 (by rfl) ⟨1436163, by rfl⟩ : syracuseStep 3829769 = 2872327) B2872327
theorem B6467795 : Blo 1701551 6467795 := bstep (se 1 (by rfl) ⟨4850846, by rfl⟩ : syracuseStep 6467795 = 9701693) B9701693
theorem B29479241 : Blo 1701551 29479241 := bstep (se 2 (by rfl) ⟨11054715, by rfl⟩ : syracuseStep 29479241 = 22109431) B22109431
theorem B3830183 : Blo 1701551 3830183 := bstep (se 1 (by rfl) ⟨2872637, by rfl⟩ : syracuseStep 3830183 = 5745275) B5745275
theorem B9204187 : Blo 1701551 9204187 := bstep (se 1 (by rfl) ⟨6903140, by rfl⟩ : syracuseStep 9204187 = 13806281) B13806281
theorem B3830291 : Blo 1701551 3830291 := bstep (se 1 (by rfl) ⟨2872718, by rfl⟩ : syracuseStep 3830291 = 5745437) B5745437
theorem B5747219 : Blo 1701551 5747219 := bstep (se 1 (by rfl) ⟨4310414, by rfl⟩ : syracuseStep 5747219 = 8620829) B8620829
theorem B8622611 : Blo 1701551 8622611 := bstep (se 1 (by rfl) ⟨6466958, by rfl⟩ : syracuseStep 8622611 = 12933917) B12933917
theorem B16593457 : Blo 1701551 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B24556081 : Blo 1701551 24556081 := bstep (se 2 (by rfl) ⟨9208530, by rfl⟩ : syracuseStep 24556081 = 18417061) B18417061
theorem B3830345 : Blo 1701551 3830345 := bstep (se 2 (by rfl) ⟨1436379, by rfl⟩ : syracuseStep 3830345 = 2872759) B2872759
theorem B2552441 : Blo 1701551 2552441 := bstep (se 2 (by rfl) ⟨957165, by rfl⟩ : syracuseStep 2552441 = 1914331) B1914331
theorem B2871929 : Blo 1701551 2871929 := bstep (se 2 (by rfl) ⟨1076973, by rfl⟩ : syracuseStep 2871929 = 2153947) B2153947
theorem B2552495 : Blo 1701551 2552495 := bstep (se 1 (by rfl) ⟨1914371, by rfl⟩ : syracuseStep 2552495 = 3828743) B3828743
theorem B2871983 : Blo 1701551 2871983 := bstep (se 1 (by rfl) ⟨2153987, by rfl⟩ : syracuseStep 2871983 = 4307975) B4307975
theorem B2552543 : Blo 1701551 2552543 := bstep (se 1 (by rfl) ⟨1914407, by rfl⟩ : syracuseStep 2552543 = 3828815) B3828815
theorem B70816517 : Blo 1701551 70816517 := bstep (se 4 (by rfl) ⟨6639048, by rfl⟩ : syracuseStep 70816517 = 13278097) B13278097
theorem B139817771 : Blo 1701551 139817771 := bstep (se 1 (by rfl) ⟨104863328, by rfl⟩ : syracuseStep 139817771 = 209726657) B209726657
theorem B8737631 : Blo 1701551 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B2872219 : Blo 1701551 2872219 := bstep (se 1 (by rfl) ⟨2154164, by rfl⟩ : syracuseStep 2872219 = 4308329) B4308329
theorem B2552807 : Blo 1701551 2552807 := bstep (se 1 (by rfl) ⟨1914605, by rfl⟩ : syracuseStep 2552807 = 3829211) B3829211
theorem B3830759 : Blo 1701551 3830759 := bstep (se 1 (by rfl) ⟨2873069, by rfl⟩ : syracuseStep 3830759 = 5746139) B5746139
theorem B7271639 : Blo 1701551 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B2553065 : Blo 1701551 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B2553119 : Blo 1701551 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B3831137 : Blo 1701551 3831137 := bstep (se 2 (by rfl) ⟨1436676, by rfl⟩ : syracuseStep 3831137 = 2873353) B2873353
theorem B3831227 : Blo 1701551 3831227 := bstep (se 1 (by rfl) ⟨2873420, by rfl⟩ : syracuseStep 3831227 = 5746841) B5746841
theorem B2553287 : Blo 1701551 2553287 := bstep (se 1 (by rfl) ⟨1914965, by rfl⟩ : syracuseStep 2553287 = 3829931) B3829931
theorem B24557003 : Blo 1701551 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B4847111 : Blo 1701551 4847111 := bstep (se 1 (by rfl) ⟨3635333, by rfl⟩ : syracuseStep 4847111 = 7270667) B7270667
theorem B3831353 : Blo 1701551 3831353 := bstep (se 2 (by rfl) ⟨1436757, by rfl⟩ : syracuseStep 3831353 = 2873515) B2873515
theorem B1914439 : Blo 1701551 1914439 := bstep (se 1 (by rfl) ⟨1435829, by rfl⟩ : syracuseStep 1914439 = 2871659) B2871659
theorem B3274427 : Blo 1701551 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B1701599 : Blo 1701551 1701599 := bstep (se 1 (by rfl) ⟨1276199, by rfl⟩ : syracuseStep 1701599 = 2552399) B2552399
theorem B2553641 : Blo 1701551 2553641 := bstep (se 2 (by rfl) ⟨957615, by rfl⟩ : syracuseStep 2553641 = 1915231) B1915231
theorem B1701679 : Blo 1701551 1701679 := bstep (se 1 (by rfl) ⟨1276259, by rfl⟩ : syracuseStep 1701679 = 2552519) B2552519
theorem B2553647 : Blo 1701551 2553647 := bstep (se 1 (by rfl) ⟨1915235, by rfl⟩ : syracuseStep 2553647 = 3830471) B3830471
theorem B29472605 : Blo 1701551 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B1701787 : Blo 1701551 1701787 := bstep (se 1 (by rfl) ⟨1276340, by rfl⟩ : syracuseStep 1701787 = 2552681) B2552681
theorem B1701839 : Blo 1701551 1701839 := bstep (se 1 (by rfl) ⟨1276379, by rfl⟩ : syracuseStep 1701839 = 2552759) B2552759
theorem B1701863 : Blo 1701551 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B8615969 : Blo 1701551 8615969 := bstep (se 2 (by rfl) ⟨3230988, by rfl⟩ : syracuseStep 8615969 = 6461977) B6461977
theorem B2725993 : Blo 1701551 2725993 := bstep (se 2 (by rfl) ⟨1022247, by rfl⟩ : syracuseStep 2725993 = 2044495) B2044495
theorem B8738945 : Blo 1701551 8738945 := bstep (se 2 (by rfl) ⟨3277104, by rfl⟩ : syracuseStep 8738945 = 6554209) B6554209
theorem B24541319 : Blo 1701551 24541319 := bstep (se 1 (by rfl) ⟨18405989, by rfl⟩ : syracuseStep 24541319 = 36811979) B36811979
theorem B32708771 : Blo 1701551 32708771 := bstep (se 1 (by rfl) ⟨24531578, by rfl⟩ : syracuseStep 32708771 = 49063157) B49063157
theorem B8616131 : Blo 1701551 8616131 := bstep (se 1 (by rfl) ⟨6462098, by rfl⟩ : syracuseStep 8616131 = 12924197) B12924197
theorem B3832019 : Blo 1701551 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B2554121 : Blo 1701551 2554121 := bstep (se 2 (by rfl) ⟨957795, by rfl⟩ : syracuseStep 2554121 = 1915591) B1915591
theorem B3832073 : Blo 1701551 3832073 := bstep (se 2 (by rfl) ⟨1437027, by rfl⟩ : syracuseStep 3832073 = 2874055) B2874055
theorem B5749001 : Blo 1701551 5749001 := bstep (se 2 (by rfl) ⟨2155875, by rfl⟩ : syracuseStep 5749001 = 4311751) B4311751
theorem B1702175 : Blo 1701551 1702175 := bstep (se 1 (by rfl) ⟨1276631, by rfl⟩ : syracuseStep 1702175 = 2553263) B2553263
theorem B13810009 : Blo 1701551 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B1702235 : Blo 1701551 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B1702255 : Blo 1701551 1702255 := bstep (se 1 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 1702255 = 2553383) B2553383
theorem B5454191 : Blo 1701551 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B2554223 : Blo 1701551 2554223 := bstep (se 1 (by rfl) ⟨1915667, by rfl⟩ : syracuseStep 2554223 = 3831335) B3831335
theorem B2873711 : Blo 1701551 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B13285757 : Blo 1701551 13285757 := bstep (se 3 (by rfl) ⟨2491079, by rfl⟩ : syracuseStep 13285757 = 4982159) B4982159
theorem B1702311 : Blo 1701551 1702311 := bstep (se 1 (by rfl) ⟨1276733, by rfl⟩ : syracuseStep 1702311 = 2553467) B2553467
theorem B1915303 : Blo 1701551 1915303 := bstep (se 1 (by rfl) ⟨1436477, by rfl⟩ : syracuseStep 1915303 = 2872955) B2872955
theorem B3832289 : Blo 1701551 3832289 := bstep (se 2 (by rfl) ⟨1437108, by rfl⟩ : syracuseStep 3832289 = 2874217) B2874217
theorem B1702395 : Blo 1701551 1702395 := bstep (se 1 (by rfl) ⟨1276796, by rfl⟩ : syracuseStep 1702395 = 2553593) B2553593
theorem B4307519 : Blo 1701551 4307519 := bstep (se 1 (by rfl) ⟨3230639, by rfl⟩ : syracuseStep 4307519 = 6461279) B6461279
theorem B1702463 : Blo 1701551 1702463 := bstep (se 1 (by rfl) ⟨1276847, by rfl⟩ : syracuseStep 1702463 = 2553695) B2553695
theorem B1702471 : Blo 1701551 1702471 := bstep (se 1 (by rfl) ⟨1276853, by rfl⟩ : syracuseStep 1702471 = 2553707) B2553707
theorem B4602439 : Blo 1701551 4602439 := bstep (se 1 (by rfl) ⟨3451829, by rfl⟩ : syracuseStep 4602439 = 6903659) B6903659
theorem B2554439 : Blo 1701551 2554439 := bstep (se 1 (by rfl) ⟨1915829, by rfl⟩ : syracuseStep 2554439 = 3831659) B3831659
theorem B2873927 : Blo 1701551 2873927 := bstep (se 1 (by rfl) ⟨2155445, by rfl⟩ : syracuseStep 2873927 = 4310891) B4310891
theorem B2554475 : Blo 1701551 2554475 := bstep (se 1 (by rfl) ⟨1915856, by rfl⟩ : syracuseStep 2554475 = 3831713) B3831713
theorem B6134467 : Blo 1701551 6134467 := bstep (se 1 (by rfl) ⟨4600850, by rfl⟩ : syracuseStep 6134467 = 9201701) B9201701
theorem B1702623 : Blo 1701551 1702623 := bstep (se 1 (by rfl) ⟨1276967, by rfl⟩ : syracuseStep 1702623 = 2553935) B2553935
theorem B3832595 : Blo 1701551 3832595 := bstep (se 1 (by rfl) ⟨2874446, by rfl⟩ : syracuseStep 3832595 = 5748893) B5748893
theorem B53844773 : Blo 1701551 53844773 := bstep (se 4 (by rfl) ⟨5047947, by rfl⟩ : syracuseStep 53844773 = 10095895) B10095895
theorem B1702703 : Blo 1701551 1702703 := bstep (se 1 (by rfl) ⟨1277027, by rfl⟩ : syracuseStep 1702703 = 2554055) B2554055
theorem B2554703 : Blo 1701551 2554703 := bstep (se 1 (by rfl) ⟨1916027, by rfl⟩ : syracuseStep 2554703 = 3832055) B3832055
theorem B1702811 : Blo 1701551 1702811 := bstep (se 1 (by rfl) ⟨1277108, by rfl⟩ : syracuseStep 1702811 = 2554217) B2554217
theorem B1702863 : Blo 1701551 1702863 := bstep (se 1 (by rfl) ⟨1277147, by rfl⟩ : syracuseStep 1702863 = 2554295) B2554295
theorem B2423783 : Blo 1701551 2423783 := bstep (se 1 (by rfl) ⟨1817837, by rfl⟩ : syracuseStep 2423783 = 3635675) B3635675
theorem B1702887 : Blo 1701551 1702887 := bstep (se 1 (by rfl) ⟨1277165, by rfl⟩ : syracuseStep 1702887 = 2554331) B2554331
theorem B1915879 : Blo 1701551 1915879 := bstep (se 1 (by rfl) ⟨1436909, by rfl⟩ : syracuseStep 1915879 = 2873819) B2873819
theorem B2874359 : Blo 1701551 2874359 := bstep (se 1 (by rfl) ⟨2155769, by rfl⟩ : syracuseStep 2874359 = 4311539) B4311539
theorem B3832955 : Blo 1701551 3832955 := bstep (se 1 (by rfl) ⟨2874716, by rfl⟩ : syracuseStep 3832955 = 5749433) B5749433
theorem B12926141 : Blo 1701551 12926141 := bstep (se 3 (by rfl) ⟨2423651, by rfl⟩ : syracuseStep 12926141 = 4847303) B4847303
theorem B4308167 : Blo 1701551 4308167 := bstep (se 1 (by rfl) ⟨3231125, by rfl⟩ : syracuseStep 4308167 = 6462251) B6462251
theorem B4308187 : Blo 1701551 4308187 := bstep (se 1 (by rfl) ⟨3231140, by rfl⟩ : syracuseStep 4308187 = 6462281) B6462281
theorem B9698525 : Blo 1701551 9698525 := bstep (se 3 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 9698525 = 3636947) B3636947
theorem B2555099 : Blo 1701551 2555099 := bstep (se 1 (by rfl) ⟨1916324, by rfl⟩ : syracuseStep 2555099 = 3832649) B3832649
theorem B1703199 : Blo 1701551 1703199 := bstep (se 1 (by rfl) ⟨1277399, by rfl⟩ : syracuseStep 1703199 = 2554799) B2554799
theorem B1703259 : Blo 1701551 1703259 := bstep (se 1 (by rfl) ⟨1277444, by rfl⟩ : syracuseStep 1703259 = 2554889) B2554889
theorem B1703279 : Blo 1701551 1703279 := bstep (se 1 (by rfl) ⟨1277459, by rfl⟩ : syracuseStep 1703279 = 2554919) B2554919
theorem B18414985 : Blo 1701551 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B2555273 : Blo 1701551 2555273 := bstep (se 2 (by rfl) ⟨958227, by rfl⟩ : syracuseStep 2555273 = 1916455) B1916455
theorem B1703335 : Blo 1701551 1703335 := bstep (se 1 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 1703335 = 2555003) B2555003
theorem B1818055 : Blo 1701551 1818055 := bstep (se 1 (by rfl) ⟨1363541, by rfl⟩ : syracuseStep 1818055 = 2727083) B2727083
theorem B6462935 : Blo 1701551 6462935 := bstep (se 1 (by rfl) ⟨4847201, by rfl⟩ : syracuseStep 6462935 = 9694403) B9694403
theorem B1703419 : Blo 1701551 1703419 := bstep (se 1 (by rfl) ⟨1277564, by rfl⟩ : syracuseStep 1703419 = 2555129) B2555129
theorem B1703487 : Blo 1701551 1703487 := bstep (se 1 (by rfl) ⟨1277615, by rfl⟩ : syracuseStep 1703487 = 2555231) B2555231
theorem B1703495 : Blo 1701551 1703495 := bstep (se 1 (by rfl) ⟨1277621, by rfl⟩ : syracuseStep 1703495 = 2555243) B2555243
theorem B3497555 : Blo 1701551 3497555 := bstep (se 1 (by rfl) ⟨2623166, by rfl⟩ : syracuseStep 3497555 = 5246333) B5246333
theorem B4603487 : Blo 1701551 4603487 := bstep (se 1 (by rfl) ⟨3452615, by rfl⟩ : syracuseStep 4603487 = 6905231) B6905231
theorem B7274099 : Blo 1701551 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B14549017 : Blo 1701551 14549017 := bstep (se 2 (by rfl) ⟨5455881, by rfl⟩ : syracuseStep 14549017 = 10911763) B10911763
theorem B33169445 : Blo 1701551 33169445 := bstep (se 4 (by rfl) ⟨3109635, by rfl⟩ : syracuseStep 33169445 = 6219271) B6219271
theorem B5456011 : Blo 1701551 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B19652827 : Blo 1701551 19652827 := bstep (se 1 (by rfl) ⟨14739620, by rfl⟩ : syracuseStep 19652827 = 29479241) B29479241
theorem B47211011 : Blo 1701551 47211011 := bstep (se 1 (by rfl) ⟨35408258, by rfl⟩ : syracuseStep 47211011 = 70816517) B70816517
theorem B5825087 : Blo 1701551 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B5456447 : Blo 1701551 5456447 := bstep (se 1 (by rfl) ⟨4092335, by rfl⟩ : syracuseStep 5456447 = 8184671) B8184671
theorem B12272249 : Blo 1701551 12272249 := bstep (se 2 (by rfl) ⟨4602093, by rfl⟩ : syracuseStep 12272249 = 9204187) B9204187
theorem B4309807 : Blo 1701551 4309807 := bstep (se 1 (by rfl) ⟨3232355, by rfl⟩ : syracuseStep 4309807 = 6464711) B6464711
theorem B4850675 : Blo 1701551 4850675 := bstep (se 1 (by rfl) ⟨3638006, by rfl⟩ : syracuseStep 4850675 = 7276013) B7276013
theorem B2802863 : Blo 1701551 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B58967347 : Blo 1701551 58967347 := bstep (se 1 (by rfl) ⟨44225510, by rfl⟩ : syracuseStep 58967347 = 88451021) B88451021
theorem B5743979 : Blo 1701551 5743979 := bstep (se 1 (by rfl) ⟨4307984, by rfl⟩ : syracuseStep 5743979 = 8615969) B8615969
theorem B5825963 : Blo 1701551 5825963 := bstep (se 1 (by rfl) ⟨4369472, by rfl⟩ : syracuseStep 5825963 = 8738945) B8738945
theorem B16360879 : Blo 1701551 16360879 := bstep (se 1 (by rfl) ⟨12270659, by rfl⟩ : syracuseStep 16360879 = 24541319) B24541319
theorem B5744087 : Blo 1701551 5744087 := bstep (se 1 (by rfl) ⟨4308065, by rfl⟩ : syracuseStep 5744087 = 8616131) B8616131
theorem B22124609 : Blo 1701551 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B8857171 : Blo 1701551 8857171 := bstep (se 1 (by rfl) ⟨6642878, by rfl⟩ : syracuseStep 8857171 = 13285757) B13285757
theorem B5744249 : Blo 1701551 5744249 := bstep (se 2 (by rfl) ⟨2154093, by rfl⟩ : syracuseStep 5744249 = 4308187) B4308187
theorem B5531257 : Blo 1701551 5531257 := bstep (se 2 (by rfl) ⟨2074221, by rfl⟩ : syracuseStep 5531257 = 4148443) B4148443
theorem B5826401 : Blo 1701551 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B24553313 : Blo 1701551 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B46598273 : Blo 1701551 46598273 := bstep (se 2 (by rfl) ⟨17474352, by rfl⟩ : syracuseStep 46598273 = 34948705) B34948705
theorem B6465683 : Blo 1701551 6465683 := bstep (se 1 (by rfl) ⟨4849262, by rfl⟩ : syracuseStep 6465683 = 9698525) B9698525
theorem B12929543 : Blo 1701551 12929543 := bstep (se 1 (by rfl) ⟨9697157, by rfl⟩ : syracuseStep 12929543 = 19394315) B19394315
theorem B4311863 : Blo 1701551 4311863 := bstep (se 1 (by rfl) ⟨3233897, by rfl⟩ : syracuseStep 4311863 = 6467795) B6467795
theorem B10906487 : Blo 1701551 10906487 := bstep (se 1 (by rfl) ⟨8179865, by rfl⟩ : syracuseStep 10906487 = 16359731) B16359731
theorem B24546341 : Blo 1701551 24546341 := bstep (se 4 (by rfl) ⟨2301219, by rfl⟩ : syracuseStep 24546341 = 4602439) B4602439
theorem B574344245 : Blo 1701551 574344245 := bstep (se 5 (by rfl) ⟨26922386, by rfl⟩ : syracuseStep 574344245 = 53844773) B53844773
theorem B5745761 : Blo 1701551 5745761 := bstep (se 2 (by rfl) ⟨2154660, by rfl⟩ : syracuseStep 5745761 = 4309321) B4309321
theorem B93211847 : Blo 1701551 93211847 := bstep (se 1 (by rfl) ⟨69908885, by rfl⟩ : syracuseStep 93211847 = 139817771) B139817771
theorem B3828959 : Blo 1701551 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B3829175 : Blo 1701551 3829175 := bstep (se 1 (by rfl) ⟨2871881, by rfl⟩ : syracuseStep 3829175 = 5743763) B5743763
theorem B8179289 : Blo 1701551 8179289 := bstep (se 2 (by rfl) ⟨3067233, by rfl⟩ : syracuseStep 8179289 = 6134467) B6134467
theorem B3829355 : Blo 1701551 3829355 := bstep (se 1 (by rfl) ⟨2872016, by rfl⟩ : syracuseStep 3829355 = 5744033) B5744033
theorem B9694835 : Blo 1701551 9694835 := bstep (se 1 (by rfl) ⟨7271126, by rfl⟩ : syracuseStep 9694835 = 14542253) B14542253
theorem B5746301 : Blo 1701551 5746301 := bstep (se 3 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 5746301 = 2154863) B2154863
theorem B16371335 : Blo 1701551 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B3231407 : Blo 1701551 3231407 := bstep (se 1 (by rfl) ⟨2423555, by rfl⟩ : syracuseStep 3231407 = 4847111) B4847111
theorem B2182951 : Blo 1701551 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B3829625 : Blo 1701551 3829625 := bstep (se 2 (by rfl) ⟨1436109, by rfl⟩ : syracuseStep 3829625 = 2872219) B2872219
theorem B5746571 : Blo 1701551 5746571 := bstep (se 1 (by rfl) ⟨4309928, by rfl⟩ : syracuseStep 5746571 = 8619857) B8619857
theorem B19648403 : Blo 1701551 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B12275965 : Blo 1701551 12275965 := bstep (se 3 (by rfl) ⟨2301743, by rfl⟩ : syracuseStep 12275965 = 4603487) B4603487
theorem B2871679 : Blo 1701551 2871679 := bstep (se 1 (by rfl) ⟨2153759, by rfl⟩ : syracuseStep 2871679 = 4307519) B4307519
theorem B4092287 : Blo 1701551 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B5747111 : Blo 1701551 5747111 := bstep (se 1 (by rfl) ⟨4310333, by rfl⟩ : syracuseStep 5747111 = 8620667) B8620667
theorem B2552423 : Blo 1701551 2552423 := bstep (se 1 (by rfl) ⟨1914317, by rfl⟩ : syracuseStep 2552423 = 3828635) B3828635
theorem B2552555 : Blo 1701551 2552555 := bstep (se 1 (by rfl) ⟨1914416, by rfl⟩ : syracuseStep 2552555 = 3828833) B3828833
theorem B2552585 : Blo 1701551 2552585 := bstep (se 2 (by rfl) ⟨957219, by rfl⟩ : syracuseStep 2552585 = 1914439) B1914439
theorem B2872111 : Blo 1701551 2872111 := bstep (se 1 (by rfl) ⟨2154083, by rfl⟩ : syracuseStep 2872111 = 4308167) B4308167
theorem B29078351 : Blo 1701551 29078351 := bstep (se 1 (by rfl) ⟨21808763, by rfl⟩ : syracuseStep 29078351 = 43617527) B43617527
theorem B2552687 : Blo 1701551 2552687 := bstep (se 1 (by rfl) ⟨1914515, by rfl⟩ : syracuseStep 2552687 = 3829031) B3829031
theorem B9696293 : Blo 1701551 9696293 := bstep (se 4 (by rfl) ⟨909027, by rfl⟩ : syracuseStep 9696293 = 1818055) B1818055
theorem B2331703 : Blo 1701551 2331703 := bstep (se 1 (by rfl) ⟨1748777, by rfl⟩ : syracuseStep 2331703 = 3497555) B3497555
theorem B4846655 : Blo 1701551 4846655 := bstep (se 1 (by rfl) ⟨3634991, by rfl⟩ : syracuseStep 4846655 = 7269983) B7269983
theorem B6304841 : Blo 1701551 6304841 := bstep (se 2 (by rfl) ⟨2364315, by rfl⟩ : syracuseStep 6304841 = 4728631) B4728631
theorem B2552939 : Blo 1701551 2552939 := bstep (se 1 (by rfl) ⟨1914704, by rfl⟩ : syracuseStep 2552939 = 3829409) B3829409
theorem B5453011 : Blo 1701551 5453011 := bstep (se 1 (by rfl) ⟨4089758, by rfl⟩ : syracuseStep 5453011 = 8179517) B8179517
theorem B19928357 : Blo 1701551 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B2553179 : Blo 1701551 2553179 := bstep (se 1 (by rfl) ⟨1914884, by rfl⟩ : syracuseStep 2553179 = 3829769) B3829769
theorem B23311721 : Blo 1701551 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B41440733 : Blo 1701551 41440733 := bstep (se 3 (by rfl) ⟨7770137, by rfl⟩ : syracuseStep 41440733 = 15540275) B15540275
theorem B32741441 : Blo 1701551 32741441 := bstep (se 2 (by rfl) ⟨12278040, by rfl⟩ : syracuseStep 32741441 = 24556081) B24556081
theorem B3233351 : Blo 1701551 3233351 := bstep (se 1 (by rfl) ⟨2425013, by rfl⟩ : syracuseStep 3233351 = 4850027) B4850027
theorem B2553455 : Blo 1701551 2553455 := bstep (se 1 (by rfl) ⟨1915091, by rfl⟩ : syracuseStep 2553455 = 3830183) B3830183
theorem B2553527 : Blo 1701551 2553527 := bstep (se 1 (by rfl) ⟨1915145, by rfl⟩ : syracuseStep 2553527 = 3830291) B3830291
theorem B3831479 : Blo 1701551 3831479 := bstep (se 1 (by rfl) ⟨2873609, by rfl⟩ : syracuseStep 3831479 = 5747219) B5747219
theorem B5748407 : Blo 1701551 5748407 := bstep (se 1 (by rfl) ⟨4311305, by rfl⟩ : syracuseStep 5748407 = 8622611) B8622611
theorem B2553563 : Blo 1701551 2553563 := bstep (se 1 (by rfl) ⟨1915172, by rfl⟩ : syracuseStep 2553563 = 3830345) B3830345
theorem B1701627 : Blo 1701551 1701627 := bstep (se 1 (by rfl) ⟨1276220, by rfl⟩ : syracuseStep 1701627 = 2552441) B2552441
theorem B1914619 : Blo 1701551 1914619 := bstep (se 1 (by rfl) ⟨1435964, by rfl⟩ : syracuseStep 1914619 = 2871929) B2871929
theorem B2873083 : Blo 1701551 2873083 := bstep (se 1 (by rfl) ⟨2154812, by rfl⟩ : syracuseStep 2873083 = 4309625) B4309625
theorem B1701663 : Blo 1701551 1701663 := bstep (se 1 (by rfl) ⟨1276247, by rfl⟩ : syracuseStep 1701663 = 2552495) B2552495
theorem B1914655 : Blo 1701551 1914655 := bstep (se 1 (by rfl) ⟨1435991, by rfl⟩ : syracuseStep 1914655 = 2871983) B2871983
theorem B18413345 : Blo 1701551 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B1701695 : Blo 1701551 1701695 := bstep (se 1 (by rfl) ⟨1276271, by rfl⟩ : syracuseStep 1701695 = 2552543) B2552543
theorem B14538629 : Blo 1701551 14538629 := bstep (se 4 (by rfl) ⟨1362996, by rfl⟩ : syracuseStep 14538629 = 2725993) B2725993
theorem B2553737 : Blo 1701551 2553737 := bstep (se 2 (by rfl) ⟨957651, by rfl⟩ : syracuseStep 2553737 = 1915303) B1915303
theorem B2873225 : Blo 1701551 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B1701871 : Blo 1701551 1701871 := bstep (se 1 (by rfl) ⟨1276403, by rfl⟩ : syracuseStep 1701871 = 2552807) B2552807
theorem B2553839 : Blo 1701551 2553839 := bstep (se 1 (by rfl) ⟨1915379, by rfl⟩ : syracuseStep 2553839 = 3830759) B3830759
theorem B4847759 : Blo 1701551 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B3233935 : Blo 1701551 3233935 := bstep (se 1 (by rfl) ⟨2425451, by rfl⟩ : syracuseStep 3233935 = 4850903) B4850903
theorem B1702043 : Blo 1701551 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B4602017 : Blo 1701551 4602017 := bstep (se 2 (by rfl) ⟨1725756, by rfl⟩ : syracuseStep 4602017 = 3451513) B3451513
theorem B1702079 : Blo 1701551 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B2554091 : Blo 1701551 2554091 := bstep (se 1 (by rfl) ⟨1915568, by rfl⟩ : syracuseStep 2554091 = 3831137) B3831137
theorem B2554151 : Blo 1701551 2554151 := bstep (se 1 (by rfl) ⟨1915613, by rfl⟩ : syracuseStep 2554151 = 3831227) B3831227
theorem B1702191 : Blo 1701551 1702191 := bstep (se 1 (by rfl) ⟨1276643, by rfl⟩ : syracuseStep 1702191 = 2553287) B2553287
theorem B2873657 : Blo 1701551 2873657 := bstep (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) B2155243
theorem B2554235 : Blo 1701551 2554235 := bstep (se 1 (by rfl) ⟨1915676, by rfl⟩ : syracuseStep 2554235 = 3831353) B3831353
theorem B15735215 : Blo 1701551 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B1702427 : Blo 1701551 1702427 := bstep (se 1 (by rfl) ⟨1276820, by rfl⟩ : syracuseStep 1702427 = 2553641) B2553641
theorem B2300447 : Blo 1701551 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B1702431 : Blo 1701551 1702431 := bstep (se 1 (by rfl) ⟨1276823, by rfl⟩ : syracuseStep 1702431 = 2553647) B2553647
theorem B2554505 : Blo 1701551 2554505 := bstep (se 2 (by rfl) ⟨957939, by rfl⟩ : syracuseStep 2554505 = 1915879) B1915879
theorem B21805847 : Blo 1701551 21805847 := bstep (se 1 (by rfl) ⟨16354385, by rfl⟩ : syracuseStep 21805847 = 32708771) B32708771
theorem B2726711 : Blo 1701551 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B2554679 : Blo 1701551 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B1702747 : Blo 1701551 1702747 := bstep (se 1 (by rfl) ⟨1277060, by rfl⟩ : syracuseStep 1702747 = 2554121) B2554121
theorem B2554715 : Blo 1701551 2554715 := bstep (se 1 (by rfl) ⟨1916036, by rfl⟩ : syracuseStep 2554715 = 3832073) B3832073
theorem B3832667 : Blo 1701551 3832667 := bstep (se 1 (by rfl) ⟨2874500, by rfl⟩ : syracuseStep 3832667 = 5749001) B5749001
theorem B3636127 : Blo 1701551 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1702815 : Blo 1701551 1702815 := bstep (se 1 (by rfl) ⟨1277111, by rfl⟩ : syracuseStep 1702815 = 2554223) B2554223
theorem B1915807 : Blo 1701551 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B2874271 : Blo 1701551 2874271 := bstep (se 1 (by rfl) ⟨2155703, by rfl⟩ : syracuseStep 2874271 = 4311407) B4311407
theorem B2554859 : Blo 1701551 2554859 := bstep (se 1 (by rfl) ⟨1916144, by rfl⟩ : syracuseStep 2554859 = 3832289) B3832289
theorem B1702959 : Blo 1701551 1702959 := bstep (se 1 (by rfl) ⟨1277219, by rfl⟩ : syracuseStep 1702959 = 2554439) B2554439
theorem B1915951 : Blo 1701551 1915951 := bstep (se 1 (by rfl) ⟨1436963, by rfl⟩ : syracuseStep 1915951 = 2873927) B2873927
theorem B1702983 : Blo 1701551 1702983 := bstep (se 1 (by rfl) ⟨1277237, by rfl⟩ : syracuseStep 1702983 = 2554475) B2554475
theorem B20716667 : Blo 1701551 20716667 := bstep (se 1 (by rfl) ⟨15537500, by rfl⟩ : syracuseStep 20716667 = 31075001) B31075001
theorem B2555063 : Blo 1701551 2555063 := bstep (se 1 (by rfl) ⟨1916297, by rfl⟩ : syracuseStep 2555063 = 3832595) B3832595
theorem B1703135 : Blo 1701551 1703135 := bstep (se 1 (by rfl) ⟨1277351, by rfl⟩ : syracuseStep 1703135 = 2554703) B2554703
theorem B9198845 : Blo 1701551 9198845 := bstep (se 3 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 9198845 = 3449567) B3449567
theorem B1916239 : Blo 1701551 1916239 := bstep (se 1 (by rfl) ⟨1437179, by rfl⟩ : syracuseStep 1916239 = 2874359) B2874359
theorem B2874703 : Blo 1701551 2874703 := bstep (se 1 (by rfl) ⟨2156027, by rfl⟩ : syracuseStep 2874703 = 4312055) B4312055
theorem B2555303 : Blo 1701551 2555303 := bstep (se 1 (by rfl) ⟨1916477, by rfl⟩ : syracuseStep 2555303 = 3832955) B3832955
theorem B8617427 : Blo 1701551 8617427 := bstep (se 1 (by rfl) ⟨6463070, by rfl⟩ : syracuseStep 8617427 = 12926141) B12926141
theorem B1703399 : Blo 1701551 1703399 := bstep (se 1 (by rfl) ⟨1277549, by rfl⟩ : syracuseStep 1703399 = 2555099) B2555099
theorem B2072155 : Blo 1701551 2072155 := bstep (se 1 (by rfl) ⟨1554116, by rfl⟩ : syracuseStep 2072155 = 3108233) B3108233
theorem B1703515 : Blo 1701551 1703515 := bstep (se 1 (by rfl) ⟨1277636, by rfl⟩ : syracuseStep 1703515 = 2555273) B2555273
theorem B4308623 : Blo 1701551 4308623 := bstep (se 1 (by rfl) ⟨3231467, by rfl⟩ : syracuseStep 4308623 = 6462935) B6462935
theorem B4849399 : Blo 1701551 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B6463421 : Blo 1701551 6463421 := bstep (se 3 (by rfl) ⟨1211891, by rfl⟩ : syracuseStep 6463421 = 2423783) B2423783
theorem B19398689 : Blo 1701551 19398689 := bstep (se 2 (by rfl) ⟨7274508, by rfl⟩ : syracuseStep 19398689 = 14549017) B14549017
theorem B7274681 : Blo 1701551 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B16367953 : Blo 1701551 16367953 := bstep (se 2 (by rfl) ⟨6137982, by rfl⟩ : syracuseStep 16367953 = 12275965) B12275965
theorem B31474007 : Blo 1701551 31474007 := bstep (se 1 (by rfl) ⟨23605505, by rfl⟩ : syracuseStep 31474007 = 47211011) B47211011
theorem B3883391 : Blo 1701551 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B3637631 : Blo 1701551 3637631 := bstep (se 1 (by rfl) ⟨2728223, by rfl⟩ : syracuseStep 3637631 = 5456447) B5456447
theorem B6464195 : Blo 1701551 6464195 := bstep (se 1 (by rfl) ⟨4848146, by rfl⟩ : syracuseStep 6464195 = 9696293) B9696293
theorem B4203227 : Blo 1701551 4203227 := bstep (se 1 (by rfl) ⟨3152420, by rfl⟩ : syracuseStep 4203227 = 6304841) B6304841
theorem B15541147 : Blo 1701551 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B10912765 : Blo 1701551 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2155567 : Blo 1701551 2155567 := bstep (se 1 (by rfl) ⟨1616675, by rfl⟩ : syracuseStep 2155567 = 3233351) B3233351
theorem B29082725 : Blo 1701551 29082725 := bstep (se 4 (by rfl) ⟨2726505, by rfl⟩ : syracuseStep 29082725 = 5453011) B5453011
theorem B3884267 : Blo 1701551 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B16368875 : Blo 1701551 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B9692419 : Blo 1701551 9692419 := bstep (se 1 (by rfl) ⟨7269314, by rfl⟩ : syracuseStep 9692419 = 14538629) B14538629
theorem B31065515 : Blo 1701551 31065515 := bstep (se 1 (by rfl) ⟨23299136, by rfl⟩ : syracuseStep 31065515 = 46598273) B46598273
theorem B4310455 : Blo 1701551 4310455 := bstep (se 1 (by rfl) ⟨3232841, by rfl⟩ : syracuseStep 4310455 = 6465683) B6465683
theorem B8619695 : Blo 1701551 8619695 := bstep (se 1 (by rfl) ⟨6464771, by rfl⟩ : syracuseStep 8619695 = 12929543) B12929543
theorem B43656893 : Blo 1701551 43656893 := bstep (se 3 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 43656893 = 16371335) B16371335
theorem B382896163 : Blo 1701551 382896163 := bstep (se 1 (by rfl) ⟨287172122, by rfl⟩ : syracuseStep 382896163 = 574344245) B574344245
theorem B2762873 : Blo 1701551 2762873 := bstep (se 2 (by rfl) ⟨1036077, by rfl⟩ : syracuseStep 2762873 = 2072155) B2072155
theorem B7375009 : Blo 1701551 7375009 := bstep (se 2 (by rfl) ⟨2765628, by rfl⟩ : syracuseStep 7375009 = 5531257) B5531257
theorem B5744951 : Blo 1701551 5744951 := bstep (se 1 (by rfl) ⟨4308713, by rfl⟩ : syracuseStep 5744951 = 8617427) B8617427
theorem B6465865 : Blo 1701551 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B2910601 : Blo 1701551 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B22112963 : Blo 1701551 22112963 := bstep (se 1 (by rfl) ⟨16584722, by rfl⟩ : syracuseStep 22112963 = 33169445) B33169445
theorem B4311913 : Blo 1701551 4311913 := bstep (se 2 (by rfl) ⟨1616967, by rfl⟩ : syracuseStep 4311913 = 3233935) B3233935
theorem B7474301 : Blo 1701551 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B3828905 : Blo 1701551 3828905 := bstep (se 2 (by rfl) ⟨1435839, by rfl⟩ : syracuseStep 3828905 = 2871679) B2871679
theorem B19385567 : Blo 1701551 19385567 := bstep (se 1 (by rfl) ⟨14539175, by rfl⟩ : syracuseStep 19385567 = 29078351) B29078351
theorem B3231103 : Blo 1701551 3231103 := bstep (se 1 (by rfl) ⟨2423327, by rfl⟩ : syracuseStep 3231103 = 4846655) B4846655
theorem B3829319 : Blo 1701551 3829319 := bstep (se 1 (by rfl) ⟨2871989, by rfl⟩ : syracuseStep 3829319 = 5743979) B5743979
theorem B3829391 : Blo 1701551 3829391 := bstep (se 1 (by rfl) ⟨2872043, by rfl⟩ : syracuseStep 3829391 = 5744087) B5744087
theorem B27627155 : Blo 1701551 27627155 := bstep (se 1 (by rfl) ⟨20720366, by rfl⟩ : syracuseStep 27627155 = 41440733) B41440733
theorem B3829481 : Blo 1701551 3829481 := bstep (se 2 (by rfl) ⟨1436055, by rfl⟩ : syracuseStep 3829481 = 2872111) B2872111
theorem B5746409 : Blo 1701551 5746409 := bstep (se 2 (by rfl) ⟨2154903, by rfl⟩ : syracuseStep 5746409 = 4309807) B4309807
theorem B2874575 : Blo 1701551 2874575 := bstep (se 1 (by rfl) ⟨2155931, by rfl⟩ : syracuseStep 2874575 = 4311863) B4311863
theorem B3829499 : Blo 1701551 3829499 := bstep (se 1 (by rfl) ⟨2872124, by rfl⟩ : syracuseStep 3829499 = 5744249) B5744249
theorem B15535901 : Blo 1701551 15535901 := bstep (se 3 (by rfl) ⟨2912981, by rfl⟩ : syracuseStep 15535901 = 5825963) B5825963
theorem B12275563 : Blo 1701551 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B14749739 : Blo 1701551 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B21827627 : Blo 1701551 21827627 := bstep (se 1 (by rfl) ⟨16370720, by rfl⟩ : syracuseStep 21827627 = 32741441) B32741441
theorem B3108937 : Blo 1701551 3108937 := bstep (se 2 (by rfl) ⟨1165851, by rfl⟩ : syracuseStep 3108937 = 2331703) B2331703
theorem B3231839 : Blo 1701551 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B3068011 : Blo 1701551 3068011 := bstep (se 1 (by rfl) ⟨2301008, by rfl⟩ : syracuseStep 3068011 = 4602017) B4602017
theorem B10490143 : Blo 1701551 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B78623129 : Blo 1701551 78623129 := bstep (se 2 (by rfl) ⟨29483673, by rfl⟩ : syracuseStep 78623129 = 58967347) B58967347
theorem B14537231 : Blo 1701551 14537231 := bstep (se 1 (by rfl) ⟨10902923, by rfl⟩ : syracuseStep 14537231 = 21805847) B21805847
theorem B7270991 : Blo 1701551 7270991 := bstep (se 1 (by rfl) ⟨5453243, by rfl⟩ : syracuseStep 7270991 = 10906487) B10906487
theorem B16364227 : Blo 1701551 16364227 := bstep (se 1 (by rfl) ⟨12273170, by rfl⟩ : syracuseStep 16364227 = 24546341) B24546341
theorem B3830507 : Blo 1701551 3830507 := bstep (se 1 (by rfl) ⟨2872880, by rfl⟩ : syracuseStep 3830507 = 5745761) B5745761
theorem B11809561 : Blo 1701551 11809561 := bstep (se 2 (by rfl) ⟨4428585, by rfl⟩ : syracuseStep 11809561 = 8857171) B8857171
theorem B62141231 : Blo 1701551 62141231 := bstep (se 1 (by rfl) ⟨46605923, by rfl⟩ : syracuseStep 62141231 = 93211847) B93211847
theorem B2552639 : Blo 1701551 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B6132563 : Blo 1701551 6132563 := bstep (se 1 (by rfl) ⟨4599422, by rfl⟩ : syracuseStep 6132563 = 9198845) B9198845
theorem B2552783 : Blo 1701551 2552783 := bstep (se 1 (by rfl) ⟨1914587, by rfl⟩ : syracuseStep 2552783 = 3829175) B3829175
theorem B2552825 : Blo 1701551 2552825 := bstep (se 2 (by rfl) ⟨957309, by rfl⟩ : syracuseStep 2552825 = 1914619) B1914619
theorem B3830777 : Blo 1701551 3830777 := bstep (se 2 (by rfl) ⟨1436541, by rfl⟩ : syracuseStep 3830777 = 2873083) B2873083
theorem B2552873 : Blo 1701551 2552873 := bstep (se 2 (by rfl) ⟨957327, by rfl⟩ : syracuseStep 2552873 = 1914655) B1914655
theorem B5452859 : Blo 1701551 5452859 := bstep (se 1 (by rfl) ⟨4089644, by rfl⟩ : syracuseStep 5452859 = 8179289) B8179289
theorem B2552903 : Blo 1701551 2552903 := bstep (se 1 (by rfl) ⟨1914677, by rfl⟩ : syracuseStep 2552903 = 3829355) B3829355
theorem B3830867 : Blo 1701551 3830867 := bstep (se 1 (by rfl) ⟨2873150, by rfl⟩ : syracuseStep 3830867 = 5746301) B5746301
theorem B2872415 : Blo 1701551 2872415 := bstep (se 1 (by rfl) ⟨2154311, by rfl⟩ : syracuseStep 2872415 = 4308623) B4308623
theorem B2553083 : Blo 1701551 2553083 := bstep (se 1 (by rfl) ⟨1914812, by rfl⟩ : syracuseStep 2553083 = 3829625) B3829625
theorem B3831047 : Blo 1701551 3831047 := bstep (se 1 (by rfl) ⟨2873285, by rfl⟩ : syracuseStep 3831047 = 5746571) B5746571
theorem B3831407 : Blo 1701551 3831407 := bstep (se 1 (by rfl) ⟨2873555, by rfl⟩ : syracuseStep 3831407 = 5747111) B5747111
theorem B26203769 : Blo 1701551 26203769 := bstep (se 2 (by rfl) ⟨9826413, by rfl⟩ : syracuseStep 26203769 = 19652827) B19652827
theorem B1701615 : Blo 1701551 1701615 := bstep (se 1 (by rfl) ⟨1276211, by rfl⟩ : syracuseStep 1701615 = 2552423) B2552423
theorem B8181499 : Blo 1701551 8181499 := bstep (se 1 (by rfl) ⟨6136124, by rfl⟩ : syracuseStep 8181499 = 12272249) B12272249
theorem B1701703 : Blo 1701551 1701703 := bstep (se 1 (by rfl) ⟨1276277, by rfl⟩ : syracuseStep 1701703 = 2552555) B2552555
theorem B1701723 : Blo 1701551 1701723 := bstep (se 1 (by rfl) ⟨1276292, by rfl⟩ : syracuseStep 1701723 = 2552585) B2552585
theorem B1701791 : Blo 1701551 1701791 := bstep (se 1 (by rfl) ⟨1276343, by rfl⟩ : syracuseStep 1701791 = 2552687) B2552687
theorem B3233783 : Blo 1701551 3233783 := bstep (se 1 (by rfl) ⟨2425337, by rfl⟩ : syracuseStep 3233783 = 4850675) B4850675
theorem B1701959 : Blo 1701551 1701959 := bstep (se 1 (by rfl) ⟨1276469, by rfl⟩ : syracuseStep 1701959 = 2552939) B2552939
theorem B13285571 : Blo 1701551 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B1702119 : Blo 1701551 1702119 := bstep (se 1 (by rfl) ⟨1276589, by rfl⟩ : syracuseStep 1702119 = 2553179) B2553179
theorem B1702303 : Blo 1701551 1702303 := bstep (se 1 (by rfl) ⟨1276727, by rfl⟩ : syracuseStep 1702303 = 2553455) B2553455
theorem B1702351 : Blo 1701551 1702351 := bstep (se 1 (by rfl) ⟨1276763, by rfl⟩ : syracuseStep 1702351 = 2553527) B2553527
theorem B2554319 : Blo 1701551 2554319 := bstep (se 1 (by rfl) ⟨1915739, by rfl⟩ : syracuseStep 2554319 = 3831479) B3831479
theorem B3832271 : Blo 1701551 3832271 := bstep (se 1 (by rfl) ⟨2874203, by rfl⟩ : syracuseStep 3832271 = 5748407) B5748407
theorem B1702375 : Blo 1701551 1702375 := bstep (se 1 (by rfl) ⟨1276781, by rfl⟩ : syracuseStep 1702375 = 2553563) B2553563
theorem B4848169 : Blo 1701551 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554409 : Blo 1701551 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B3832361 : Blo 1701551 3832361 := bstep (se 2 (by rfl) ⟨1437135, by rfl⟩ : syracuseStep 3832361 = 2874271) B2874271
theorem B1702491 : Blo 1701551 1702491 := bstep (se 1 (by rfl) ⟨1276868, by rfl⟩ : syracuseStep 1702491 = 2553737) B2553737
theorem B1915483 : Blo 1701551 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B1702559 : Blo 1701551 1702559 := bstep (se 1 (by rfl) ⟨1276919, by rfl⟩ : syracuseStep 1702559 = 2553839) B2553839
theorem B2554601 : Blo 1701551 2554601 := bstep (se 2 (by rfl) ⟨957975, by rfl⟩ : syracuseStep 2554601 = 1915951) B1915951
theorem B6134525 : Blo 1701551 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B1702727 : Blo 1701551 1702727 := bstep (se 1 (by rfl) ⟨1277045, by rfl⟩ : syracuseStep 1702727 = 2554091) B2554091
theorem B1702767 : Blo 1701551 1702767 := bstep (se 1 (by rfl) ⟨1277075, by rfl⟩ : syracuseStep 1702767 = 2554151) B2554151
theorem B1915771 : Blo 1701551 1915771 := bstep (se 1 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 1915771 = 2873657) B2873657
theorem B1702823 : Blo 1701551 1702823 := bstep (se 1 (by rfl) ⟨1277117, by rfl⟩ : syracuseStep 1702823 = 2554235) B2554235
theorem B1703003 : Blo 1701551 1703003 := bstep (se 1 (by rfl) ⟨1277252, by rfl⟩ : syracuseStep 1703003 = 2554505) B2554505
theorem B2554985 : Blo 1701551 2554985 := bstep (se 2 (by rfl) ⟨958119, by rfl⟩ : syracuseStep 2554985 = 1916239) B1916239
theorem B3832937 : Blo 1701551 3832937 := bstep (se 2 (by rfl) ⟨1437351, by rfl⟩ : syracuseStep 3832937 = 2874703) B2874703
theorem B1817807 : Blo 1701551 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B1703119 : Blo 1701551 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1703143 : Blo 1701551 1703143 := bstep (se 1 (by rfl) ⟨1277357, by rfl⟩ : syracuseStep 1703143 = 2554715) B2554715
theorem B2555111 : Blo 1701551 2555111 := bstep (se 1 (by rfl) ⟨1916333, by rfl⟩ : syracuseStep 2555111 = 3832667) B3832667
theorem B21814505 : Blo 1701551 21814505 := bstep (se 2 (by rfl) ⟨8180439, by rfl⟩ : syracuseStep 21814505 = 16360879) B16360879
theorem B1703239 : Blo 1701551 1703239 := bstep (se 1 (by rfl) ⟨1277429, by rfl⟩ : syracuseStep 1703239 = 2554859) B2554859
theorem B13811111 : Blo 1701551 13811111 := bstep (se 1 (by rfl) ⟨10358333, by rfl⟩ : syracuseStep 13811111 = 20716667) B20716667
theorem B1703375 : Blo 1701551 1703375 := bstep (se 1 (by rfl) ⟨1277531, by rfl⟩ : syracuseStep 1703375 = 2555063) B2555063
theorem B1703535 : Blo 1701551 1703535 := bstep (se 1 (by rfl) ⟨1277651, by rfl⟩ : syracuseStep 1703535 = 2555303) B2555303
theorem B6463223 : Blo 1701551 6463223 := bstep (se 1 (by rfl) ⟨4847417, by rfl⟩ : syracuseStep 6463223 = 9694835) B9694835
theorem B2154271 : Blo 1701551 2154271 := bstep (se 1 (by rfl) ⟨1615703, by rfl⟩ : syracuseStep 2154271 = 3231407) B3231407
theorem B13098935 : Blo 1701551 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B4308947 : Blo 1701551 4308947 := bstep (se 1 (by rfl) ⟨3231710, by rfl⟩ : syracuseStep 4308947 = 6463421) B6463421
theorem B4145249 : Blo 1701551 4145249 := bstep (se 2 (by rfl) ⟨1554468, by rfl⟩ : syracuseStep 4145249 = 3108937) B3108937
theorem B4849787 : Blo 1701551 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B8618237 : Blo 1701551 8618237 := bstep (se 3 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 8618237 = 3231839) B3231839
theorem B2588927 : Blo 1701551 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B2425087 : Blo 1701551 2425087 := bstep (se 1 (by rfl) ⟨1818815, by rfl⟩ : syracuseStep 2425087 = 3637631) B3637631
theorem B9691487 : Blo 1701551 9691487 := bstep (se 1 (by rfl) ⟨7268615, by rfl⟩ : syracuseStep 9691487 = 14537231) B14537231
theorem B21823937 : Blo 1701551 21823937 := bstep (se 2 (by rfl) ⟨8183976, by rfl⟩ : syracuseStep 21823937 = 16367953) B16367953
theorem B4309463 : Blo 1701551 4309463 := bstep (se 1 (by rfl) ⟨3232097, by rfl⟩ : syracuseStep 4309463 = 6464195) B6464195
theorem B2802151 : Blo 1701551 2802151 := bstep (se 1 (by rfl) ⟨2101613, by rfl⟩ : syracuseStep 2802151 = 4203227) B4203227
theorem B41427487 : Blo 1701551 41427487 := bstep (se 1 (by rfl) ⟨31070615, by rfl⟩ : syracuseStep 41427487 = 62141231) B62141231
theorem B4088375 : Blo 1701551 4088375 := bstep (se 1 (by rfl) ⟨3066281, by rfl⟩ : syracuseStep 4088375 = 6132563) B6132563
theorem B6464225 : Blo 1701551 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B2589511 : Blo 1701551 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B10912583 : Blo 1701551 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B20710343 : Blo 1701551 20710343 := bstep (se 1 (by rfl) ⟨15532757, by rfl⟩ : syracuseStep 20710343 = 31065515) B31065515
theorem B15746081 : Blo 1701551 15746081 := bstep (se 2 (by rfl) ⟨5904780, by rfl⟩ : syracuseStep 15746081 = 11809561) B11809561
theorem B14550353 : Blo 1701551 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B4089683 : Blo 1701551 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B4982867 : Blo 1701551 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B14543003 : Blo 1701551 14543003 := bstep (se 1 (by rfl) ⟨10907252, by rfl⟩ : syracuseStep 14543003 = 21814505) B21814505
theorem B18418103 : Blo 1701551 18418103 := bstep (se 1 (by rfl) ⟨13813577, by rfl⟩ : syracuseStep 18418103 = 27627155) B27627155
theorem B10357267 : Blo 1701551 10357267 := bstep (se 1 (by rfl) ⟨7767950, by rfl⟩ : syracuseStep 10357267 = 15535901) B15535901
theorem B9833159 : Blo 1701551 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B14551751 : Blo 1701551 14551751 := bstep (se 1 (by rfl) ⟨10913813, by rfl⟩ : syracuseStep 14551751 = 21827627) B21827627
theorem B4090681 : Blo 1701551 4090681 := bstep (se 2 (by rfl) ⟨1534005, by rfl⟩ : syracuseStep 4090681 = 3068011) B3068011
theorem B2042112869 : Blo 1701551 2042112869 := bstep (se 4 (by rfl) ⟨191448081, by rfl⟩ : syracuseStep 2042112869 = 382896163) B382896163
theorem B9833345 : Blo 1701551 9833345 := bstep (se 2 (by rfl) ⟨3687504, by rfl⟩ : syracuseStep 9833345 = 7375009) B7375009
theorem B20982671 : Blo 1701551 20982671 := bstep (se 1 (by rfl) ⟨15737003, by rfl⟩ : syracuseStep 20982671 = 31474007) B31474007
theorem B52415419 : Blo 1701551 52415419 := bstep (se 1 (by rfl) ⟨39311564, by rfl⟩ : syracuseStep 52415419 = 78623129) B78623129
theorem B13986857 : Blo 1701551 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B8621153 : Blo 1701551 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B21818969 : Blo 1701551 21818969 := bstep (se 2 (by rfl) ⟨8182113, by rfl⟩ : syracuseStep 21818969 = 16364227) B16364227
theorem B17469179 : Blo 1701551 17469179 := bstep (se 1 (by rfl) ⟨13101884, by rfl⟩ : syracuseStep 17469179 = 26203769) B26203769
theorem B5746463 : Blo 1701551 5746463 := bstep (se 1 (by rfl) ⟨4309847, by rfl⟩ : syracuseStep 5746463 = 8619695) B8619695
theorem B20721529 : Blo 1701551 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B29470645 : Blo 1701551 29470645 := bstep (se 5 (by rfl) ⟨1381436, by rfl⟩ : syracuseStep 29470645 = 2762873) B2762873
theorem B3829967 : Blo 1701551 3829967 := bstep (se 1 (by rfl) ⟨2872475, by rfl⟩ : syracuseStep 3829967 = 5744951) B5744951
theorem B12923225 : Blo 1701551 12923225 := bstep (se 2 (by rfl) ⟨4846209, by rfl⟩ : syracuseStep 12923225 = 9692419) B9692419
theorem B14741975 : Blo 1701551 14741975 := bstep (se 1 (by rfl) ⟨11056481, by rfl⟩ : syracuseStep 14741975 = 22112963) B22112963
theorem B5747273 : Blo 1701551 5747273 := bstep (se 2 (by rfl) ⟨2155227, by rfl⟩ : syracuseStep 5747273 = 4310455) B4310455
theorem B2552603 : Blo 1701551 2552603 := bstep (se 1 (by rfl) ⟨1914452, by rfl⟩ : syracuseStep 2552603 = 3828905) B3828905
theorem B12923711 : Blo 1701551 12923711 := bstep (se 1 (by rfl) ⟨9692783, by rfl⟩ : syracuseStep 12923711 = 19385567) B19385567
theorem B10908665 : Blo 1701551 10908665 := bstep (se 2 (by rfl) ⟨4090749, by rfl⟩ : syracuseStep 10908665 = 8181499) B8181499
theorem B2872361 : Blo 1701551 2872361 := bstep (se 2 (by rfl) ⟨1077135, by rfl⟩ : syracuseStep 2872361 = 2154271) B2154271
theorem B2552879 : Blo 1701551 2552879 := bstep (se 1 (by rfl) ⟨1914659, by rfl⟩ : syracuseStep 2552879 = 3829319) B3829319
theorem B2552927 : Blo 1701551 2552927 := bstep (se 1 (by rfl) ⟨1914695, by rfl⟩ : syracuseStep 2552927 = 3829391) B3829391
theorem B2552987 : Blo 1701551 2552987 := bstep (se 1 (by rfl) ⟨1914740, by rfl⟩ : syracuseStep 2552987 = 3829481) B3829481
theorem B3830939 : Blo 1701551 3830939 := bstep (se 1 (by rfl) ⟨2873204, by rfl⟩ : syracuseStep 3830939 = 5746409) B5746409
theorem B2552999 : Blo 1701551 2552999 := bstep (se 1 (by rfl) ⟨1914749, by rfl⟩ : syracuseStep 2552999 = 3829499) B3829499
theorem B2872631 : Blo 1701551 2872631 := bstep (se 1 (by rfl) ⟨2154473, by rfl⟩ : syracuseStep 2872631 = 4308947) B4308947
theorem B8623421 : Blo 1701551 8623421 := bstep (se 3 (by rfl) ⟨1616891, by rfl⟩ : syracuseStep 8623421 = 3233783) B3233783
theorem B12932459 : Blo 1701551 12932459 := bstep (se 1 (by rfl) ⟨9699344, by rfl⟩ : syracuseStep 12932459 = 19398689) B19398689
theorem B4847327 : Blo 1701551 4847327 := bstep (se 1 (by rfl) ⟨3635495, by rfl⟩ : syracuseStep 4847327 = 7270991) B7270991
theorem B2553671 : Blo 1701551 2553671 := bstep (se 1 (by rfl) ⟨1915253, by rfl⟩ : syracuseStep 2553671 = 3830507) B3830507
theorem B3880801 : Blo 1701551 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B1701759 : Blo 1701551 1701759 := bstep (se 1 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 1701759 = 2552639) B2552639
theorem B1701855 : Blo 1701551 1701855 := bstep (se 1 (by rfl) ⟨1276391, by rfl⟩ : syracuseStep 1701855 = 2552783) B2552783
theorem B1701883 : Blo 1701551 1701883 := bstep (se 1 (by rfl) ⟨1276412, by rfl⟩ : syracuseStep 1701883 = 2552825) B2552825
theorem B2553851 : Blo 1701551 2553851 := bstep (se 1 (by rfl) ⟨1915388, by rfl⟩ : syracuseStep 2553851 = 3830777) B3830777
theorem B1701915 : Blo 1701551 1701915 := bstep (se 1 (by rfl) ⟨1276436, by rfl⟩ : syracuseStep 1701915 = 2552873) B2552873
theorem B3635239 : Blo 1701551 3635239 := bstep (se 1 (by rfl) ⟨2726429, by rfl⟩ : syracuseStep 3635239 = 5452859) B5452859
theorem B1701935 : Blo 1701551 1701935 := bstep (se 1 (by rfl) ⟨1276451, by rfl⟩ : syracuseStep 1701935 = 2552903) B2552903
theorem B2553911 : Blo 1701551 2553911 := bstep (se 1 (by rfl) ⟨1915433, by rfl⟩ : syracuseStep 2553911 = 3830867) B3830867
theorem B1914943 : Blo 1701551 1914943 := bstep (se 1 (by rfl) ⟨1436207, by rfl⟩ : syracuseStep 1914943 = 2872415) B2872415
theorem B19388483 : Blo 1701551 19388483 := bstep (se 1 (by rfl) ⟨14541362, by rfl⟩ : syracuseStep 19388483 = 29082725) B29082725
theorem B2553977 : Blo 1701551 2553977 := bstep (se 2 (by rfl) ⟨957741, by rfl⟩ : syracuseStep 2553977 = 1915483) B1915483
theorem B1702055 : Blo 1701551 1702055 := bstep (se 1 (by rfl) ⟨1276541, by rfl⟩ : syracuseStep 1702055 = 2553083) B2553083
theorem B2554031 : Blo 1701551 2554031 := bstep (se 1 (by rfl) ⟨1915523, by rfl⟩ : syracuseStep 2554031 = 3831047) B3831047
theorem B2554271 : Blo 1701551 2554271 := bstep (se 1 (by rfl) ⟨1915703, by rfl⟩ : syracuseStep 2554271 = 3831407) B3831407
theorem B29104595 : Blo 1701551 29104595 := bstep (se 1 (by rfl) ⟨21828446, by rfl⟩ : syracuseStep 29104595 = 43656893) B43656893
theorem B5749217 : Blo 1701551 5749217 := bstep (se 2 (by rfl) ⟨2155956, by rfl⟩ : syracuseStep 5749217 = 4311913) B4311913
theorem B2554361 : Blo 1701551 2554361 := bstep (se 2 (by rfl) ⟨957885, by rfl⟩ : syracuseStep 2554361 = 1915771) B1915771
theorem B2874089 : Blo 1701551 2874089 := bstep (se 2 (by rfl) ⟨1077783, by rfl⟩ : syracuseStep 2874089 = 2155567) B2155567
theorem B1702879 : Blo 1701551 1702879 := bstep (se 1 (by rfl) ⟨1277159, by rfl⟩ : syracuseStep 1702879 = 2554319) B2554319
theorem B2554847 : Blo 1701551 2554847 := bstep (se 1 (by rfl) ⟨1916135, by rfl⟩ : syracuseStep 2554847 = 3832271) B3832271
theorem B1702939 : Blo 1701551 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B2554907 : Blo 1701551 2554907 := bstep (se 1 (by rfl) ⟨1916180, by rfl⟩ : syracuseStep 2554907 = 3832361) B3832361
theorem B1703067 : Blo 1701551 1703067 := bstep (se 1 (by rfl) ⟨1277300, by rfl⟩ : syracuseStep 1703067 = 2554601) B2554601
theorem B4308137 : Blo 1701551 4308137 := bstep (se 2 (by rfl) ⟨1615551, by rfl⟩ : syracuseStep 4308137 = 3231103) B3231103
theorem B141712757 : Blo 1701551 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B1703323 : Blo 1701551 1703323 := bstep (se 1 (by rfl) ⟨1277492, by rfl⟩ : syracuseStep 1703323 = 2554985) B2554985
theorem B2555291 : Blo 1701551 2555291 := bstep (se 1 (by rfl) ⟨1916468, by rfl⟩ : syracuseStep 2555291 = 3832937) B3832937
theorem B1916383 : Blo 1701551 1916383 := bstep (se 1 (by rfl) ⟨1437287, by rfl⟩ : syracuseStep 1916383 = 2874575) B2874575
theorem B1703407 : Blo 1701551 1703407 := bstep (se 1 (by rfl) ⟨1277555, by rfl⟩ : syracuseStep 1703407 = 2555111) B2555111
theorem B19389941 : Blo 1701551 19389941 := bstep (se 5 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 19389941 = 1817807) B1817807
theorem B9207407 : Blo 1701551 9207407 := bstep (se 1 (by rfl) ⟨6905555, by rfl⟩ : syracuseStep 9207407 = 13811111) B13811111
theorem B16367417 : Blo 1701551 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B4308815 : Blo 1701551 4308815 := bstep (se 1 (by rfl) ⟨3231611, by rfl⟩ : syracuseStep 4308815 = 6463223) B6463223
theorem B8732623 : Blo 1701551 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B14549291 : Blo 1701551 14549291 := bstep (se 1 (by rfl) ⟨10911968, by rfl⟩ : syracuseStep 14549291 = 21823937) B21823937
theorem B4309483 : Blo 1701551 4309483 := bstep (se 1 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 4309483 = 6464225) B6464225
theorem B3736201 : Blo 1701551 3736201 := bstep (se 2 (by rfl) ⟨1401075, by rfl⟩ : syracuseStep 3736201 = 2802151) B2802151
theorem B9700235 : Blo 1701551 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B69887225 : Blo 1701551 69887225 := bstep (se 2 (by rfl) ⟨26207709, by rfl⟩ : syracuseStep 69887225 = 52415419) B52415419
theorem B21816965 : Blo 1701551 21816965 := bstep (se 4 (by rfl) ⟨2045340, by rfl⟩ : syracuseStep 21816965 = 4090681) B4090681
theorem B6555439 : Blo 1701551 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B9701167 : Blo 1701551 9701167 := bstep (se 1 (by rfl) ⟨7275875, by rfl⟩ : syracuseStep 9701167 = 14551751) B14551751
theorem B6555563 : Blo 1701551 6555563 := bstep (se 1 (by rfl) ⟨4916672, by rfl⟩ : syracuseStep 6555563 = 9833345) B9833345
theorem B9324571 : Blo 1701551 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B29100221 : Blo 1701551 29100221 := bstep (se 3 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 29100221 = 10912583) B10912583
theorem B6138271 : Blo 1701551 6138271 := bstep (se 1 (by rfl) ⟨4603703, by rfl⟩ : syracuseStep 6138271 = 9207407) B9207407
theorem B11643497 : Blo 1701551 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B2763499 : Blo 1701551 2763499 := bstep (se 1 (by rfl) ⟨2072624, by rfl⟩ : syracuseStep 2763499 = 4145249) B4145249
theorem B5745491 : Blo 1701551 5745491 := bstep (se 1 (by rfl) ⟨4309118, by rfl⟩ : syracuseStep 5745491 = 8618237) B8618237
theorem B8621639 : Blo 1701551 8621639 := bstep (se 1 (by rfl) ⟨6466229, by rfl⟩ : syracuseStep 8621639 = 12932459) B12932459
theorem B3452681 : Blo 1701551 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B3231551 : Blo 1701551 3231551 := bstep (se 1 (by rfl) ⟨2423663, by rfl⟩ : syracuseStep 3231551 = 4847327) B4847327
theorem B3321911 : Blo 1701551 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B9695335 : Blo 1701551 9695335 := bstep (se 1 (by rfl) ⟨7271501, by rfl⟩ : syracuseStep 9695335 = 14543003) B14543003
theorem B19403063 : Blo 1701551 19403063 := bstep (se 1 (by rfl) ⟨14552297, by rfl⟩ : syracuseStep 19403063 = 29104595) B29104595
theorem B1361408579 : Blo 1701551 1361408579 := bstep (se 1 (by rfl) ⟨1021056434, by rfl⟩ : syracuseStep 1361408579 = 2042112869) B2042112869
theorem B13988447 : Blo 1701551 13988447 := bstep (se 1 (by rfl) ⟨10491335, by rfl⟩ : syracuseStep 13988447 = 20982671) B20982671
theorem B5747435 : Blo 1701551 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B2872091 : Blo 1701551 2872091 := bstep (se 1 (by rfl) ⟨2154068, by rfl⟩ : syracuseStep 2872091 = 4308137) B4308137
theorem B94475171 : Blo 1701551 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B157176773 : Blo 1701551 157176773 := bstep (se 4 (by rfl) ⟨14735322, by rfl⟩ : syracuseStep 157176773 = 29470645) B29470645
theorem B14545979 : Blo 1701551 14545979 := bstep (se 1 (by rfl) ⟨10909484, by rfl⟩ : syracuseStep 14545979 = 21818969) B21818969
theorem B5174401 : Blo 1701551 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B27628705 : Blo 1701551 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B11646119 : Blo 1701551 11646119 := bstep (se 1 (by rfl) ⟨8734589, by rfl⟩ : syracuseStep 11646119 = 17469179) B17469179
theorem B55227581 : Blo 1701551 55227581 := bstep (se 3 (by rfl) ⟨10355171, by rfl⟩ : syracuseStep 55227581 = 20710343) B20710343
theorem B3830975 : Blo 1701551 3830975 := bstep (se 1 (by rfl) ⟨2873231, by rfl⟩ : syracuseStep 3830975 = 5746463) B5746463
theorem B2872543 : Blo 1701551 2872543 := bstep (se 1 (by rfl) ⟨2154407, by rfl⟩ : syracuseStep 2872543 = 4308815) B4308815
theorem B4846985 : Blo 1701551 4846985 := bstep (se 2 (by rfl) ⟨1817619, by rfl⟩ : syracuseStep 4846985 = 3635239) B3635239
theorem B3233191 : Blo 1701551 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B2553257 : Blo 1701551 2553257 := bstep (se 2 (by rfl) ⟨957471, by rfl⟩ : syracuseStep 2553257 = 1914943) B1914943
theorem B2553311 : Blo 1701551 2553311 := bstep (se 1 (by rfl) ⟨1914983, by rfl⟩ : syracuseStep 2553311 = 3829967) B3829967
theorem B8615483 : Blo 1701551 8615483 := bstep (se 1 (by rfl) ⟨6461612, by rfl⟩ : syracuseStep 8615483 = 12923225) B12923225
theorem B6460991 : Blo 1701551 6460991 := bstep (se 1 (by rfl) ⟨4845743, by rfl⟩ : syracuseStep 6460991 = 9691487) B9691487
theorem B9827983 : Blo 1701551 9827983 := bstep (se 1 (by rfl) ⟨7370987, by rfl⟩ : syracuseStep 9827983 = 14741975) B14741975
theorem B2872975 : Blo 1701551 2872975 := bstep (se 1 (by rfl) ⟨2154731, by rfl⟩ : syracuseStep 2872975 = 4309463) B4309463
theorem B3233449 : Blo 1701551 3233449 := bstep (se 2 (by rfl) ⟨1212543, by rfl⟩ : syracuseStep 3233449 = 2425087) B2425087
theorem B167958197 : Blo 1701551 167958197 := bstep (se 5 (by rfl) ⟨7873040, by rfl⟩ : syracuseStep 167958197 = 15746081) B15746081
theorem B2725583 : Blo 1701551 2725583 := bstep (se 1 (by rfl) ⟨2044187, by rfl⟩ : syracuseStep 2725583 = 4088375) B4088375
theorem B3831515 : Blo 1701551 3831515 := bstep (se 1 (by rfl) ⟨2873636, by rfl⟩ : syracuseStep 3831515 = 5747273) B5747273
theorem B1701735 : Blo 1701551 1701735 := bstep (se 1 (by rfl) ⟨1276301, by rfl⟩ : syracuseStep 1701735 = 2552603) B2552603
theorem B8615807 : Blo 1701551 8615807 := bstep (se 1 (by rfl) ⟨6461855, by rfl⟩ : syracuseStep 8615807 = 12923711) B12923711
theorem B7272443 : Blo 1701551 7272443 := bstep (se 1 (by rfl) ⟨5454332, by rfl⟩ : syracuseStep 7272443 = 10908665) B10908665
theorem B6903805 : Blo 1701551 6903805 := bstep (se 3 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 6903805 = 2588927) B2588927
theorem B13809689 : Blo 1701551 13809689 := bstep (se 2 (by rfl) ⟨5178633, by rfl⟩ : syracuseStep 13809689 = 10357267) B10357267
theorem B1914907 : Blo 1701551 1914907 := bstep (se 1 (by rfl) ⟨1436180, by rfl⟩ : syracuseStep 1914907 = 2872361) B2872361
theorem B1701919 : Blo 1701551 1701919 := bstep (se 1 (by rfl) ⟨1276439, by rfl⟩ : syracuseStep 1701919 = 2552879) B2552879
theorem B55236649 : Blo 1701551 55236649 := bstep (se 2 (by rfl) ⟨20713743, by rfl⟩ : syracuseStep 55236649 = 41427487) B41427487
theorem B1701951 : Blo 1701551 1701951 := bstep (se 1 (by rfl) ⟨1276463, by rfl⟩ : syracuseStep 1701951 = 2552927) B2552927
theorem B1701991 : Blo 1701551 1701991 := bstep (se 1 (by rfl) ⟨1276493, by rfl⟩ : syracuseStep 1701991 = 2552987) B2552987
theorem B2553959 : Blo 1701551 2553959 := bstep (se 1 (by rfl) ⟨1915469, by rfl⟩ : syracuseStep 2553959 = 3830939) B3830939
theorem B1701999 : Blo 1701551 1701999 := bstep (se 1 (by rfl) ⟨1276499, by rfl⟩ : syracuseStep 1701999 = 2552999) B2552999
theorem B1915087 : Blo 1701551 1915087 := bstep (se 1 (by rfl) ⟨1436315, by rfl⟩ : syracuseStep 1915087 = 2872631) B2872631
theorem B5748947 : Blo 1701551 5748947 := bstep (se 1 (by rfl) ⟨4311710, by rfl⟩ : syracuseStep 5748947 = 8623421) B8623421
theorem B1702447 : Blo 1701551 1702447 := bstep (se 1 (by rfl) ⟨1276835, by rfl⟩ : syracuseStep 1702447 = 2553671) B2553671
theorem B2726455 : Blo 1701551 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B1702567 : Blo 1701551 1702567 := bstep (se 1 (by rfl) ⟨1276925, by rfl⟩ : syracuseStep 1702567 = 2553851) B2553851
theorem B1702607 : Blo 1701551 1702607 := bstep (se 1 (by rfl) ⟨1276955, by rfl⟩ : syracuseStep 1702607 = 2553911) B2553911
theorem B12925655 : Blo 1701551 12925655 := bstep (se 1 (by rfl) ⟨9694241, by rfl⟩ : syracuseStep 12925655 = 19388483) B19388483
theorem B1702651 : Blo 1701551 1702651 := bstep (se 1 (by rfl) ⟨1276988, by rfl⟩ : syracuseStep 1702651 = 2553977) B2553977
theorem B1702687 : Blo 1701551 1702687 := bstep (se 1 (by rfl) ⟨1277015, by rfl⟩ : syracuseStep 1702687 = 2554031) B2554031
theorem B1702847 : Blo 1701551 1702847 := bstep (se 1 (by rfl) ⟨1277135, by rfl⟩ : syracuseStep 1702847 = 2554271) B2554271
theorem B12278735 : Blo 1701551 12278735 := bstep (se 1 (by rfl) ⟨9209051, by rfl⟩ : syracuseStep 12278735 = 18418103) B18418103
theorem B3832811 : Blo 1701551 3832811 := bstep (se 1 (by rfl) ⟨2874608, by rfl⟩ : syracuseStep 3832811 = 5749217) B5749217
theorem B1702907 : Blo 1701551 1702907 := bstep (se 1 (by rfl) ⟨1277180, by rfl⟩ : syracuseStep 1702907 = 2554361) B2554361
theorem B1916059 : Blo 1701551 1916059 := bstep (se 1 (by rfl) ⟨1437044, by rfl⟩ : syracuseStep 1916059 = 2874089) B2874089
theorem B2555177 : Blo 1701551 2555177 := bstep (se 2 (by rfl) ⟨958191, by rfl⟩ : syracuseStep 2555177 = 1916383) B1916383
theorem B1703231 : Blo 1701551 1703231 := bstep (se 1 (by rfl) ⟨1277423, by rfl⟩ : syracuseStep 1703231 = 2554847) B2554847
theorem B1703271 : Blo 1701551 1703271 := bstep (se 1 (by rfl) ⟨1277453, by rfl⟩ : syracuseStep 1703271 = 2554907) B2554907
theorem B1703527 : Blo 1701551 1703527 := bstep (se 1 (by rfl) ⟨1277645, by rfl⟩ : syracuseStep 1703527 = 2555291) B2555291
theorem B12926627 : Blo 1701551 12926627 := bstep (se 1 (by rfl) ⟨9694970, by rfl⟩ : syracuseStep 12926627 = 19389941) B19389941
theorem B10911611 : Blo 1701551 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B12927113 : Blo 1701551 12927113 := bstep (se 2 (by rfl) ⟨4847667, by rfl⟩ : syracuseStep 12927113 = 9695335) B9695335
theorem B9699527 : Blo 1701551 9699527 := bstep (se 1 (by rfl) ⟨7274645, by rfl⟩ : syracuseStep 9699527 = 14549291) B14549291
theorem B12935375 : Blo 1701551 12935375 := bstep (se 1 (by rfl) ⟨9701531, by rfl⟩ : syracuseStep 12935375 = 19403063) B19403063
theorem B31056317 : Blo 1701551 31056317 := bstep (se 3 (by rfl) ⟨5823059, by rfl⟩ : syracuseStep 31056317 = 11646119) B11646119
theorem B104784515 : Blo 1701551 104784515 := bstep (se 1 (by rfl) ⟨78588386, by rfl⟩ : syracuseStep 104784515 = 157176773) B157176773
theorem B4981601 : Blo 1701551 4981601 := bstep (se 2 (by rfl) ⟨1868100, by rfl⟩ : syracuseStep 4981601 = 3736201) B3736201
theorem B5743655 : Blo 1701551 5743655 := bstep (se 1 (by rfl) ⟨4307741, by rfl⟩ : syracuseStep 5743655 = 8615483) B8615483
theorem B5743871 : Blo 1701551 5743871 := bstep (se 1 (by rfl) ⟨4307903, by rfl⟩ : syracuseStep 5743871 = 8615807) B8615807
theorem B19400147 : Blo 1701551 19400147 := bstep (se 1 (by rfl) ⟨14550110, by rfl⟩ : syracuseStep 19400147 = 29100221) B29100221
theorem B6899201 : Blo 1701551 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B7268221 : Blo 1701551 7268221 := bstep (se 3 (by rfl) ⟨1362791, by rfl⟩ : syracuseStep 7268221 = 2725583) B2725583
theorem B4310921 : Blo 1701551 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B8185823 : Blo 1701551 8185823 := bstep (se 1 (by rfl) ⟨6139367, by rfl⟩ : syracuseStep 8185823 = 12278735) B12278735
theorem B32737445 : Blo 1701551 32737445 := bstep (se 4 (by rfl) ⟨3069135, by rfl⟩ : syracuseStep 32737445 = 6138271) B6138271
theorem B4311265 : Blo 1701551 4311265 := bstep (se 2 (by rfl) ⟨1616724, by rfl⟩ : syracuseStep 4311265 = 3233449) B3233449
theorem B73648865 : Blo 1701551 73648865 := bstep (se 2 (by rfl) ⟨27618324, by rfl⟩ : syracuseStep 73648865 = 55236649) B55236649
theorem B8858429 : Blo 1701551 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B9325631 : Blo 1701551 9325631 := bstep (se 1 (by rfl) ⟨6994223, by rfl⟩ : syracuseStep 9325631 = 13988447) B13988447
theorem B6466823 : Blo 1701551 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B5745977 : Blo 1701551 5745977 := bstep (se 2 (by rfl) ⟨2154741, by rfl⟩ : syracuseStep 5745977 = 4309483) B4309483
theorem B36818387 : Blo 1701551 36818387 := bstep (se 1 (by rfl) ⟨27613790, by rfl⟩ : syracuseStep 36818387 = 55227581) B55227581
theorem B46591483 : Blo 1701551 46591483 := bstep (se 1 (by rfl) ⟨34943612, by rfl⟩ : syracuseStep 46591483 = 69887225) B69887225
theorem B3231323 : Blo 1701551 3231323 := bstep (se 1 (by rfl) ⟨2423492, by rfl⟩ : syracuseStep 3231323 = 4846985) B4846985
theorem B14544643 : Blo 1701551 14544643 := bstep (se 1 (by rfl) ⟨10908482, by rfl⟩ : syracuseStep 14544643 = 21816965) B21816965
theorem B111972131 : Blo 1701551 111972131 := bstep (se 1 (by rfl) ⟨83979098, by rfl⟩ : syracuseStep 111972131 = 167958197) B167958197
theorem B4370375 : Blo 1701551 4370375 := bstep (se 1 (by rfl) ⟨3277781, by rfl⟩ : syracuseStep 4370375 = 6555563) B6555563
theorem B3830057 : Blo 1701551 3830057 := bstep (se 2 (by rfl) ⟨1436271, by rfl⟩ : syracuseStep 3830057 = 2872543) B2872543
theorem B7762331 : Blo 1701551 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B3830327 : Blo 1701551 3830327 := bstep (se 1 (by rfl) ⟨2872745, by rfl⟩ : syracuseStep 3830327 = 5745491) B5745491
theorem B13103977 : Blo 1701551 13103977 := bstep (se 2 (by rfl) ⟨4913991, by rfl⟩ : syracuseStep 13103977 = 9827983) B9827983
theorem B3830633 : Blo 1701551 3830633 := bstep (se 2 (by rfl) ⟨1436487, by rfl⟩ : syracuseStep 3830633 = 2872975) B2872975
theorem B5747759 : Blo 1701551 5747759 := bstep (se 1 (by rfl) ⟨4310819, by rfl⟩ : syracuseStep 5747759 = 8621639) B8621639
theorem B251933789 : Blo 1701551 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B9205073 : Blo 1701551 9205073 := bstep (se 2 (by rfl) ⟨3451902, by rfl⟩ : syracuseStep 9205073 = 6903805) B6903805
theorem B12432761 : Blo 1701551 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B2553209 : Blo 1701551 2553209 := bstep (se 2 (by rfl) ⟨957453, by rfl⟩ : syracuseStep 2553209 = 1914907) B1914907
theorem B2553449 : Blo 1701551 2553449 := bstep (se 2 (by rfl) ⟨957543, by rfl⟩ : syracuseStep 2553449 = 1915087) B1915087
theorem B907605719 : Blo 1701551 907605719 := bstep (se 1 (by rfl) ⟨680704289, by rfl⟩ : syracuseStep 907605719 = 1361408579) B1361408579
theorem B3831623 : Blo 1701551 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B1914727 : Blo 1701551 1914727 := bstep (se 1 (by rfl) ⟨1436045, by rfl⟩ : syracuseStep 1914727 = 2872091) B2872091
theorem B9697319 : Blo 1701551 9697319 := bstep (se 1 (by rfl) ⟨7272989, by rfl⟩ : syracuseStep 9697319 = 14545979) B14545979
theorem B3635273 : Blo 1701551 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B2553983 : Blo 1701551 2553983 := bstep (se 1 (by rfl) ⟨1915487, by rfl⟩ : syracuseStep 2553983 = 3830975) B3830975
theorem B1702171 : Blo 1701551 1702171 := bstep (se 1 (by rfl) ⟨1276628, by rfl⟩ : syracuseStep 1702171 = 2553257) B2553257
theorem B3684665 : Blo 1701551 3684665 := bstep (se 2 (by rfl) ⟨1381749, by rfl⟩ : syracuseStep 3684665 = 2763499) B2763499
theorem B1702207 : Blo 1701551 1702207 := bstep (se 1 (by rfl) ⟨1276655, by rfl⟩ : syracuseStep 1702207 = 2553311) B2553311
theorem B4307327 : Blo 1701551 4307327 := bstep (se 1 (by rfl) ⟨3230495, by rfl⟩ : syracuseStep 4307327 = 6460991) B6460991
theorem B2554343 : Blo 1701551 2554343 := bstep (se 1 (by rfl) ⟨1915757, by rfl⟩ : syracuseStep 2554343 = 3831515) B3831515
theorem B4848295 : Blo 1701551 4848295 := bstep (se 1 (by rfl) ⟨3636221, by rfl⟩ : syracuseStep 4848295 = 7272443) B7272443
theorem B9206459 : Blo 1701551 9206459 := bstep (se 1 (by rfl) ⟨6904844, by rfl⟩ : syracuseStep 9206459 = 13809689) B13809689
theorem B1702639 : Blo 1701551 1702639 := bstep (se 1 (by rfl) ⟨1276979, by rfl⟩ : syracuseStep 1702639 = 2553959) B2553959
theorem B3832631 : Blo 1701551 3832631 := bstep (se 1 (by rfl) ⟨2874473, by rfl⟩ : syracuseStep 3832631 = 5748947) B5748947
theorem B2554745 : Blo 1701551 2554745 := bstep (se 2 (by rfl) ⟨958029, by rfl⟩ : syracuseStep 2554745 = 1916059) B1916059
theorem B36838273 : Blo 1701551 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B8617103 : Blo 1701551 8617103 := bstep (se 1 (by rfl) ⟨6462827, by rfl⟩ : syracuseStep 8617103 = 12925655) B12925655
theorem B2555207 : Blo 1701551 2555207 := bstep (se 1 (by rfl) ⟨1916405, by rfl⟩ : syracuseStep 2555207 = 3832811) B3832811
theorem B1703451 : Blo 1701551 1703451 := bstep (se 1 (by rfl) ⟨1277588, by rfl⟩ : syracuseStep 1703451 = 2555177) B2555177
theorem B8740585 : Blo 1701551 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B12934889 : Blo 1701551 12934889 := bstep (se 2 (by rfl) ⟨4850583, by rfl⟩ : syracuseStep 12934889 = 9701167) B9701167
theorem B8617751 : Blo 1701551 8617751 := bstep (se 1 (by rfl) ⟨6463313, by rfl⟩ : syracuseStep 8617751 = 12926627) B12926627
theorem B2301787 : Blo 1701551 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B2154367 : Blo 1701551 2154367 := bstep (se 1 (by rfl) ⟨1615775, by rfl⟩ : syracuseStep 2154367 = 3231551) B3231551
theorem B7274407 : Blo 1701551 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B8618075 : Blo 1701551 8618075 := bstep (se 1 (by rfl) ⟨6463556, by rfl⟩ : syracuseStep 8618075 = 12927113) B12927113
theorem B6464393 : Blo 1701551 6464393 := bstep (se 2 (by rfl) ⟨2424147, by rfl⟩ : syracuseStep 6464393 = 4848295) B4848295
theorem B6136715 : Blo 1701551 6136715 := bstep (se 1 (by rfl) ⟨4602536, by rfl⟩ : syracuseStep 6136715 = 9205073) B9205073
theorem B605070479 : Blo 1701551 605070479 := bstep (se 1 (by rfl) ⟨453802859, by rfl⟩ : syracuseStep 605070479 = 907605719) B907605719
theorem B5457215 : Blo 1701551 5457215 := bstep (se 1 (by rfl) ⟨4092911, by rfl⟩ : syracuseStep 5457215 = 8185823) B8185823
theorem B6464879 : Blo 1701551 6464879 := bstep (se 1 (by rfl) ⟨4848659, by rfl⟩ : syracuseStep 6464879 = 9697319) B9697319
theorem B21824963 : Blo 1701551 21824963 := bstep (se 1 (by rfl) ⟨16368722, by rfl⟩ : syracuseStep 21824963 = 32737445) B32737445
theorem B6137639 : Blo 1701551 6137639 := bstep (se 1 (by rfl) ⟨4603229, by rfl⟩ : syracuseStep 6137639 = 9206459) B9206459
theorem B62121977 : Blo 1701551 62121977 := bstep (se 2 (by rfl) ⟨23295741, by rfl⟩ : syracuseStep 62121977 = 46591483) B46591483
theorem B5744735 : Blo 1701551 5744735 := bstep (se 1 (by rfl) ⟨4308551, by rfl⟩ : syracuseStep 5744735 = 8617103) B8617103
theorem B4311215 : Blo 1701551 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B24545591 : Blo 1701551 24545591 := bstep (se 1 (by rfl) ⟨18409193, by rfl⟩ : syracuseStep 24545591 = 36818387) B36818387
theorem B19392857 : Blo 1701551 19392857 := bstep (se 2 (by rfl) ⟨7272321, by rfl⟩ : syracuseStep 19392857 = 14544643) B14544643
theorem B5745167 : Blo 1701551 5745167 := bstep (se 1 (by rfl) ⟨4308875, by rfl⟩ : syracuseStep 5745167 = 8617751) B8617751
theorem B74648087 : Blo 1701551 74648087 := bstep (se 1 (by rfl) ⟨55986065, by rfl⟩ : syracuseStep 74648087 = 111972131) B111972131
theorem B6466351 : Blo 1701551 6466351 := bstep (se 1 (by rfl) ⟨4849763, by rfl⟩ : syracuseStep 6466351 = 9699527) B9699527
theorem B20704211 : Blo 1701551 20704211 := bstep (se 1 (by rfl) ⟨15528158, by rfl⟩ : syracuseStep 20704211 = 31056317) B31056317
theorem B69856343 : Blo 1701551 69856343 := bstep (se 1 (by rfl) ⟨52392257, by rfl⟩ : syracuseStep 69856343 = 104784515) B104784515
theorem B3831839 : Blo 1701551 3831839 := bstep (se 1 (by rfl) ⟨2873879, by rfl⟩ : syracuseStep 3831839 = 5747759) B5747759
theorem B3829103 : Blo 1701551 3829103 := bstep (se 1 (by rfl) ⟨2871827, by rfl⟩ : syracuseStep 3829103 = 5743655) B5743655
theorem B167955859 : Blo 1701551 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B3829247 : Blo 1701551 3829247 := bstep (se 1 (by rfl) ⟨2871935, by rfl⟩ : syracuseStep 3829247 = 5743871) B5743871
theorem B4599467 : Blo 1701551 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B2871551 : Blo 1701551 2871551 := bstep (se 1 (by rfl) ⟨2153663, by rfl⟩ : syracuseStep 2871551 = 4307327) B4307327
theorem B12276197 : Blo 1701551 12276197 := bstep (se 4 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 12276197 = 2301787) B2301787
theorem B49099243 : Blo 1701551 49099243 := bstep (se 1 (by rfl) ⟨36824432, by rfl⟩ : syracuseStep 49099243 = 73648865) B73648865
theorem B3830651 : Blo 1701551 3830651 := bstep (se 1 (by rfl) ⟨2872988, by rfl⟩ : syracuseStep 3830651 = 5745977) B5745977
theorem B13284269 : Blo 1701551 13284269 := bstep (se 3 (by rfl) ⟨2490800, by rfl⟩ : syracuseStep 13284269 = 4981601) B4981601
theorem B11654113 : Blo 1701551 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B2552969 : Blo 1701551 2552969 := bstep (se 2 (by rfl) ⟨957363, by rfl⟩ : syracuseStep 2552969 = 1914727) B1914727
theorem B8623259 : Blo 1701551 8623259 := bstep (se 1 (by rfl) ⟨6467444, by rfl⟩ : syracuseStep 8623259 = 12934889) B12934889
theorem B2872489 : Blo 1701551 2872489 := bstep (se 2 (by rfl) ⟨1077183, by rfl⟩ : syracuseStep 2872489 = 2154367) B2154367
theorem B2913583 : Blo 1701551 2913583 := bstep (se 1 (by rfl) ⟨2185187, by rfl⟩ : syracuseStep 2913583 = 4370375) B4370375
theorem B8623583 : Blo 1701551 8623583 := bstep (se 1 (by rfl) ⟨6467687, by rfl⟩ : syracuseStep 8623583 = 12935375) B12935375
theorem B2553371 : Blo 1701551 2553371 := bstep (se 1 (by rfl) ⟨1915028, by rfl⟩ : syracuseStep 2553371 = 3830057) B3830057
theorem B5174887 : Blo 1701551 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B5748353 : Blo 1701551 5748353 := bstep (se 2 (by rfl) ⟨2155632, by rfl⟩ : syracuseStep 5748353 = 4311265) B4311265
theorem B2553551 : Blo 1701551 2553551 := bstep (se 1 (by rfl) ⟨1915163, by rfl⟩ : syracuseStep 2553551 = 3830327) B3830327
theorem B2553755 : Blo 1701551 2553755 := bstep (se 1 (by rfl) ⟨1915316, by rfl⟩ : syracuseStep 2553755 = 3830633) B3830633
theorem B8288507 : Blo 1701551 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B1702139 : Blo 1701551 1702139 := bstep (se 1 (by rfl) ⟨1276604, by rfl⟩ : syracuseStep 1702139 = 2553209) B2553209
theorem B12933431 : Blo 1701551 12933431 := bstep (se 1 (by rfl) ⟨9700073, by rfl⟩ : syracuseStep 12933431 = 19400147) B19400147
theorem B1702299 : Blo 1701551 1702299 := bstep (se 1 (by rfl) ⟨1276724, by rfl⟩ : syracuseStep 1702299 = 2553449) B2553449
theorem B17471969 : Blo 1701551 17471969 := bstep (se 2 (by rfl) ⟨6551988, by rfl⟩ : syracuseStep 17471969 = 13103977) B13103977
theorem B49117697 : Blo 1701551 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B2554415 : Blo 1701551 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B2873947 : Blo 1701551 2873947 := bstep (se 1 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 2873947 = 4310921) B4310921
theorem B2423515 : Blo 1701551 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B1702655 : Blo 1701551 1702655 := bstep (se 1 (by rfl) ⟨1276991, by rfl⟩ : syracuseStep 1702655 = 2553983) B2553983
theorem B2456443 : Blo 1701551 2456443 := bstep (se 1 (by rfl) ⟨1842332, by rfl⟩ : syracuseStep 2456443 = 3684665) B3684665
theorem B1702895 : Blo 1701551 1702895 := bstep (se 1 (by rfl) ⟨1277171, by rfl⟩ : syracuseStep 1702895 = 2554343) B2554343
theorem B5905619 : Blo 1701551 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B2555087 : Blo 1701551 2555087 := bstep (se 1 (by rfl) ⟨1916315, by rfl⟩ : syracuseStep 2555087 = 3832631) B3832631
theorem B1703163 : Blo 1701551 1703163 := bstep (se 1 (by rfl) ⟨1277372, by rfl⟩ : syracuseStep 1703163 = 2554745) B2554745
theorem B6217087 : Blo 1701551 6217087 := bstep (se 1 (by rfl) ⟨4662815, by rfl⟩ : syracuseStep 6217087 = 9325631) B9325631
theorem B1703471 : Blo 1701551 1703471 := bstep (se 1 (by rfl) ⟨1277603, by rfl⟩ : syracuseStep 1703471 = 2555207) B2555207
theorem B2154215 : Blo 1701551 2154215 := bstep (se 1 (by rfl) ⟨1615661, by rfl⟩ : syracuseStep 2154215 = 3231323) B3231323
theorem B9690961 : Blo 1701551 9690961 := bstep (se 2 (by rfl) ⟨3634110, by rfl⟩ : syracuseStep 9690961 = 7268221) B7268221
theorem B9699209 : Blo 1701551 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B8184131 : Blo 1701551 8184131 := bstep (se 1 (by rfl) ⟨6138098, by rfl⟩ : syracuseStep 8184131 = 12276197) B12276197
theorem B4309595 : Blo 1701551 4309595 := bstep (se 1 (by rfl) ⟨3232196, by rfl⟩ : syracuseStep 4309595 = 6464393) B6464393
theorem B8856179 : Blo 1701551 8856179 := bstep (se 1 (by rfl) ⟨6642134, by rfl⟩ : syracuseStep 8856179 = 13284269) B13284269
theorem B3638143 : Blo 1701551 3638143 := bstep (se 1 (by rfl) ⟨2728607, by rfl⟩ : syracuseStep 3638143 = 5457215) B5457215
theorem B4309919 : Blo 1701551 4309919 := bstep (se 1 (by rfl) ⟨3232439, by rfl⟩ : syracuseStep 4309919 = 6464879) B6464879
theorem B14549975 : Blo 1701551 14549975 := bstep (se 1 (by rfl) ⟨10912481, by rfl⟩ : syracuseStep 14549975 = 21824963) B21824963
theorem B12928571 : Blo 1701551 12928571 := bstep (se 1 (by rfl) ⟨9696428, by rfl⟩ : syracuseStep 12928571 = 19392857) B19392857
theorem B32745131 : Blo 1701551 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B3884777 : Blo 1701551 3884777 := bstep (se 2 (by rfl) ⟨1456791, by rfl⟩ : syracuseStep 3884777 = 2913583) B2913583
theorem B5744573 : Blo 1701551 5744573 := bstep (se 3 (by rfl) ⟨1077107, by rfl⟩ : syracuseStep 5744573 = 2154215) B2154215
theorem B6899849 : Blo 1701551 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B12921281 : Blo 1701551 12921281 := bstep (se 2 (by rfl) ⟨4845480, by rfl⟩ : syracuseStep 12921281 = 9690961) B9690961
theorem B3066311 : Blo 1701551 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B6466139 : Blo 1701551 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B5745383 : Blo 1701551 5745383 := bstep (se 1 (by rfl) ⟨4309037, by rfl⟩ : syracuseStep 5745383 = 8618075) B8618075
theorem B4091143 : Blo 1701551 4091143 := bstep (se 1 (by rfl) ⟨3068357, by rfl⟩ : syracuseStep 4091143 = 6136715) B6136715
theorem B65465657 : Blo 1701551 65465657 := bstep (se 2 (by rfl) ⟨24549621, by rfl⟩ : syracuseStep 65465657 = 49099243) B49099243
theorem B3231353 : Blo 1701551 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B8621801 : Blo 1701551 8621801 := bstep (se 2 (by rfl) ⟨3233175, by rfl⟩ : syracuseStep 8621801 = 6466351) B6466351
theorem B4091759 : Blo 1701551 4091759 := bstep (se 1 (by rfl) ⟨3068819, by rfl⟩ : syracuseStep 4091759 = 6137639) B6137639
theorem B41414651 : Blo 1701551 41414651 := bstep (se 1 (by rfl) ⟨31060988, by rfl⟩ : syracuseStep 41414651 = 62121977) B62121977
theorem B3829823 : Blo 1701551 3829823 := bstep (se 1 (by rfl) ⟨2872367, by rfl⟩ : syracuseStep 3829823 = 5744735) B5744735
theorem B5525671 : Blo 1701551 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B16363727 : Blo 1701551 16363727 := bstep (se 1 (by rfl) ⟨12272795, by rfl⟩ : syracuseStep 16363727 = 24545591) B24545591
theorem B8622287 : Blo 1701551 8622287 := bstep (se 1 (by rfl) ⟨6466715, by rfl⟩ : syracuseStep 8622287 = 12933431) B12933431
theorem B3829985 : Blo 1701551 3829985 := bstep (se 2 (by rfl) ⟨1436244, by rfl⟩ : syracuseStep 3829985 = 2872489) B2872489
theorem B3830111 : Blo 1701551 3830111 := bstep (se 1 (by rfl) ⟨2872583, by rfl⟩ : syracuseStep 3830111 = 5745167) B5745167
theorem B223941145 : Blo 1701551 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B3937079 : Blo 1701551 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B2552735 : Blo 1701551 2552735 := bstep (se 1 (by rfl) ⟨1914551, by rfl⟩ : syracuseStep 2552735 = 3829103) B3829103
theorem B2552831 : Blo 1701551 2552831 := bstep (se 1 (by rfl) ⟨1914623, by rfl⟩ : syracuseStep 2552831 = 3829247) B3829247
theorem B3832235 : Blo 1701551 3832235 := bstep (se 1 (by rfl) ⟨2874176, by rfl⟩ : syracuseStep 3832235 = 5748353) B5748353
theorem B1914367 : Blo 1701551 1914367 := bstep (se 1 (by rfl) ⟨1435775, by rfl⟩ : syracuseStep 1914367 = 2871551) B2871551
theorem B2553767 : Blo 1701551 2553767 := bstep (se 1 (by rfl) ⟨1915325, by rfl⟩ : syracuseStep 2553767 = 3830651) B3830651
theorem B1701979 : Blo 1701551 1701979 := bstep (se 1 (by rfl) ⟨1276484, by rfl⟩ : syracuseStep 1701979 = 2552969) B2552969
theorem B403380319 : Blo 1701551 403380319 := bstep (se 1 (by rfl) ⟨302535239, by rfl⟩ : syracuseStep 403380319 = 605070479) B605070479
theorem B5748839 : Blo 1701551 5748839 := bstep (se 1 (by rfl) ⟨4311629, by rfl⟩ : syracuseStep 5748839 = 8623259) B8623259
theorem B3831929 : Blo 1701551 3831929 := bstep (se 2 (by rfl) ⟨1436973, by rfl⟩ : syracuseStep 3831929 = 2873947) B2873947
theorem B5749055 : Blo 1701551 5749055 := bstep (se 1 (by rfl) ⟨4311791, by rfl⟩ : syracuseStep 5749055 = 8623583) B8623583
theorem B1702247 : Blo 1701551 1702247 := bstep (se 1 (by rfl) ⟨1276685, by rfl⟩ : syracuseStep 1702247 = 2553371) B2553371
theorem B1702367 : Blo 1701551 1702367 := bstep (se 1 (by rfl) ⟨1276775, by rfl⟩ : syracuseStep 1702367 = 2553551) B2553551
theorem B3275257 : Blo 1701551 3275257 := bstep (se 2 (by rfl) ⟨1228221, by rfl⟩ : syracuseStep 3275257 = 2456443) B2456443
theorem B1702503 : Blo 1701551 1702503 := bstep (se 1 (by rfl) ⟨1276877, by rfl⟩ : syracuseStep 1702503 = 2553755) B2553755
theorem B15538817 : Blo 1701551 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B2554559 : Blo 1701551 2554559 := bstep (se 1 (by rfl) ⟨1915919, by rfl⟩ : syracuseStep 2554559 = 3831839) B3831839
theorem B2874143 : Blo 1701551 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B11647979 : Blo 1701551 11647979 := bstep (se 1 (by rfl) ⟨8735984, by rfl⟩ : syracuseStep 11647979 = 17471969) B17471969
theorem B49765391 : Blo 1701551 49765391 := bstep (se 1 (by rfl) ⟨37324043, by rfl⟩ : syracuseStep 49765391 = 74648087) B74648087
theorem B1702943 : Blo 1701551 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B8289449 : Blo 1701551 8289449 := bstep (se 2 (by rfl) ⟨3108543, by rfl⟩ : syracuseStep 8289449 = 6217087) B6217087
theorem B13802807 : Blo 1701551 13802807 := bstep (se 1 (by rfl) ⟨10352105, by rfl⟩ : syracuseStep 13802807 = 20704211) B20704211
theorem B46570895 : Blo 1701551 46570895 := bstep (se 1 (by rfl) ⟨34928171, by rfl⟩ : syracuseStep 46570895 = 69856343) B69856343
theorem B1703391 : Blo 1701551 1703391 := bstep (se 1 (by rfl) ⟨1277543, by rfl⟩ : syracuseStep 1703391 = 2555087) B2555087
theorem B5456087 : Blo 1701551 5456087 := bstep (se 1 (by rfl) ⟨4092065, by rfl⟩ : syracuseStep 5456087 = 8184131) B8184131
theorem B9699983 : Blo 1701551 9699983 := bstep (se 1 (by rfl) ⟨7274987, by rfl⟩ : syracuseStep 9699983 = 14549975) B14549975
theorem B4367009 : Blo 1701551 4367009 := bstep (se 2 (by rfl) ⟨1637628, by rfl⟩ : syracuseStep 4367009 = 3275257) B3275257
theorem B8619047 : Blo 1701551 8619047 := bstep (se 1 (by rfl) ⟨6464285, by rfl⟩ : syracuseStep 8619047 = 12928571) B12928571
theorem B2589851 : Blo 1701551 2589851 := bstep (se 1 (by rfl) ⟨1942388, by rfl⟩ : syracuseStep 2589851 = 3884777) B3884777
theorem B4850857 : Blo 1701551 4850857 := bstep (se 2 (by rfl) ⟨1819071, by rfl⟩ : syracuseStep 4850857 = 3638143) B3638143
theorem B4310759 : Blo 1701551 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B9201871 : Blo 1701551 9201871 := bstep (se 1 (by rfl) ⟨6901403, by rfl⟩ : syracuseStep 9201871 = 13802807) B13802807
theorem B27609767 : Blo 1701551 27609767 := bstep (se 1 (by rfl) ⟨20707325, by rfl⟩ : syracuseStep 27609767 = 41414651) B41414651
theorem B537840425 : Blo 1701551 537840425 := bstep (se 2 (by rfl) ⟨201690159, by rfl⟩ : syracuseStep 537840425 = 403380319) B403380319
theorem B7367561 : Blo 1701551 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B2624719 : Blo 1701551 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B3829715 : Blo 1701551 3829715 := bstep (se 1 (by rfl) ⟨2872286, by rfl⟩ : syracuseStep 3829715 = 5744573) B5744573
theorem B4599899 : Blo 1701551 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B8614187 : Blo 1701551 8614187 := bstep (se 1 (by rfl) ⟨6460640, by rfl⟩ : syracuseStep 8614187 = 12921281) B12921281
theorem B2044207 : Blo 1701551 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B10359211 : Blo 1701551 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B3830255 : Blo 1701551 3830255 := bstep (se 1 (by rfl) ⟨2872691, by rfl⟩ : syracuseStep 3830255 = 5745383) B5745383
theorem B2552489 : Blo 1701551 2552489 := bstep (se 2 (by rfl) ⟨957183, by rfl⟩ : syracuseStep 2552489 = 1914367) B1914367
theorem B5526299 : Blo 1701551 5526299 := bstep (se 1 (by rfl) ⟨4144724, by rfl⟩ : syracuseStep 5526299 = 8289449) B8289449
theorem B43643771 : Blo 1701551 43643771 := bstep (se 1 (by rfl) ⟨32732828, by rfl⟩ : syracuseStep 43643771 = 65465657) B65465657
theorem B5747867 : Blo 1701551 5747867 := bstep (se 1 (by rfl) ⟨4310900, by rfl⟩ : syracuseStep 5747867 = 8621801) B8621801
theorem B2553215 : Blo 1701551 2553215 := bstep (se 1 (by rfl) ⟨1914911, by rfl⟩ : syracuseStep 2553215 = 3829823) B3829823
theorem B10909151 : Blo 1701551 10909151 := bstep (se 1 (by rfl) ⟨8181863, by rfl⟩ : syracuseStep 10909151 = 16363727) B16363727
theorem B5748191 : Blo 1701551 5748191 := bstep (se 1 (by rfl) ⟨4311143, by rfl⟩ : syracuseStep 5748191 = 8622287) B8622287
theorem B2553323 : Blo 1701551 2553323 := bstep (se 1 (by rfl) ⟨1914992, by rfl⟩ : syracuseStep 2553323 = 3829985) B3829985
theorem B2553407 : Blo 1701551 2553407 := bstep (se 1 (by rfl) ⟨1915055, by rfl⟩ : syracuseStep 2553407 = 3830111) B3830111
theorem B2873063 : Blo 1701551 2873063 := bstep (se 1 (by rfl) ⟨2154797, by rfl⟩ : syracuseStep 2873063 = 4309595) B4309595
theorem B5904119 : Blo 1701551 5904119 := bstep (se 1 (by rfl) ⟨4428089, by rfl⟩ : syracuseStep 5904119 = 8856179) B8856179
theorem B1701823 : Blo 1701551 1701823 := bstep (se 1 (by rfl) ⟨1276367, by rfl⟩ : syracuseStep 1701823 = 2552735) B2552735
theorem B2873279 : Blo 1701551 2873279 := bstep (se 1 (by rfl) ⟨2154959, by rfl⟩ : syracuseStep 2873279 = 4309919) B4309919
theorem B1701887 : Blo 1701551 1701887 := bstep (se 1 (by rfl) ⟨1276415, by rfl⟩ : syracuseStep 1701887 = 2552831) B2552831
theorem B298588193 : Blo 1701551 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B21830087 : Blo 1701551 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B1702511 : Blo 1701551 1702511 := bstep (se 1 (by rfl) ⟨1276883, by rfl⟩ : syracuseStep 1702511 = 2553767) B2553767
theorem B3832559 : Blo 1701551 3832559 := bstep (se 1 (by rfl) ⟨2874419, by rfl⟩ : syracuseStep 3832559 = 5748839) B5748839
theorem B2554619 : Blo 1701551 2554619 := bstep (se 1 (by rfl) ⟨1915964, by rfl⟩ : syracuseStep 2554619 = 3831929) B3831929
theorem B3832703 : Blo 1701551 3832703 := bstep (se 1 (by rfl) ⟨2874527, by rfl⟩ : syracuseStep 3832703 = 5749055) B5749055
theorem B2554823 : Blo 1701551 2554823 := bstep (se 1 (by rfl) ⟨1916117, by rfl⟩ : syracuseStep 2554823 = 3832235) B3832235
theorem B8616941 : Blo 1701551 8616941 := bstep (se 3 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 8616941 = 3231353) B3231353
theorem B5454857 : Blo 1701551 5454857 := bstep (se 2 (by rfl) ⟨2045571, by rfl⟩ : syracuseStep 5454857 = 4091143) B4091143
theorem B1703039 : Blo 1701551 1703039 := bstep (se 1 (by rfl) ⟨1277279, by rfl⟩ : syracuseStep 1703039 = 2554559) B2554559
theorem B1916095 : Blo 1701551 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B7765319 : Blo 1701551 7765319 := bstep (se 1 (by rfl) ⟨5823989, by rfl⟩ : syracuseStep 7765319 = 11647979) B11647979
theorem B33176927 : Blo 1701551 33176927 := bstep (se 1 (by rfl) ⟨24882695, by rfl⟩ : syracuseStep 33176927 = 49765391) B49765391
theorem B31047263 : Blo 1701551 31047263 := bstep (se 1 (by rfl) ⟨23285447, by rfl⟩ : syracuseStep 31047263 = 46570895) B46570895
theorem B2727839 : Blo 1701551 2727839 := bstep (se 1 (by rfl) ⟨2045879, by rfl⟩ : syracuseStep 2727839 = 4091759) B4091759
theorem B3637391 : Blo 1701551 3637391 := bstep (se 1 (by rfl) ⟨2728043, by rfl⟩ : syracuseStep 3637391 = 5456087) B5456087
theorem B5742791 : Blo 1701551 5742791 := bstep (se 1 (by rfl) ⟨4307093, by rfl⟩ : syracuseStep 5742791 = 8614187) B8614187
theorem B6906269 : Blo 1701551 6906269 := bstep (se 3 (by rfl) ⟨1294925, by rfl⟩ : syracuseStep 6906269 = 2589851) B2589851
theorem B13812281 : Blo 1701551 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B199058795 : Blo 1701551 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B3499625 : Blo 1701551 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B5744627 : Blo 1701551 5744627 := bstep (se 1 (by rfl) ⟨4308470, by rfl⟩ : syracuseStep 5744627 = 8616941) B8616941
theorem B3066599 : Blo 1701551 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B6466655 : Blo 1701551 6466655 := bstep (se 1 (by rfl) ⟨4849991, by rfl⟩ : syracuseStep 6466655 = 9699983) B9699983
theorem B2911339 : Blo 1701551 2911339 := bstep (se 1 (by rfl) ⟨2183504, by rfl⟩ : syracuseStep 2911339 = 4367009) B4367009
theorem B5746031 : Blo 1701551 5746031 := bstep (se 1 (by rfl) ⟨4309523, by rfl⟩ : syracuseStep 5746031 = 8619047) B8619047
theorem B3936079 : Blo 1701551 3936079 := bstep (se 1 (by rfl) ⟨2952059, by rfl⟩ : syracuseStep 3936079 = 5904119) B5904119
theorem B6467809 : Blo 1701551 6467809 := bstep (se 2 (by rfl) ⟨2425428, by rfl⟩ : syracuseStep 6467809 = 4850857) B4850857
theorem B14553391 : Blo 1701551 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B358560283 : Blo 1701551 358560283 := bstep (se 1 (by rfl) ⟨268920212, by rfl⟩ : syracuseStep 358560283 = 537840425) B537840425
theorem B4911707 : Blo 1701551 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B20698175 : Blo 1701551 20698175 := bstep (se 1 (by rfl) ⟨15523631, by rfl⟩ : syracuseStep 20698175 = 31047263) B31047263
theorem B2553143 : Blo 1701551 2553143 := bstep (se 1 (by rfl) ⟨1914857, by rfl⟩ : syracuseStep 2553143 = 3829715) B3829715
theorem B12269161 : Blo 1701551 12269161 := bstep (se 2 (by rfl) ⟨4600935, by rfl⟩ : syracuseStep 12269161 = 9201871) B9201871
theorem B2553503 : Blo 1701551 2553503 := bstep (se 1 (by rfl) ⟨1915127, by rfl⟩ : syracuseStep 2553503 = 3830255) B3830255
theorem B1701659 : Blo 1701551 1701659 := bstep (se 1 (by rfl) ⟨1276244, by rfl⟩ : syracuseStep 1701659 = 2552489) B2552489
theorem B3684199 : Blo 1701551 3684199 := bstep (se 1 (by rfl) ⟨2763149, by rfl⟩ : syracuseStep 3684199 = 5526299) B5526299
theorem B29095847 : Blo 1701551 29095847 := bstep (se 1 (by rfl) ⟨21821885, by rfl⟩ : syracuseStep 29095847 = 43643771) B43643771
theorem B3831911 : Blo 1701551 3831911 := bstep (se 1 (by rfl) ⟨2873933, by rfl⟩ : syracuseStep 3831911 = 5747867) B5747867
theorem B1702143 : Blo 1701551 1702143 := bstep (se 1 (by rfl) ⟨1276607, by rfl⟩ : syracuseStep 1702143 = 2553215) B2553215
theorem B7272767 : Blo 1701551 7272767 := bstep (se 1 (by rfl) ⟨5454575, by rfl⟩ : syracuseStep 7272767 = 10909151) B10909151
theorem B3832127 : Blo 1701551 3832127 := bstep (se 1 (by rfl) ⟨2874095, by rfl⟩ : syracuseStep 3832127 = 5748191) B5748191
theorem B1702215 : Blo 1701551 1702215 := bstep (se 1 (by rfl) ⟨1276661, by rfl⟩ : syracuseStep 1702215 = 2553323) B2553323
theorem B1702271 : Blo 1701551 1702271 := bstep (se 1 (by rfl) ⟨1276703, by rfl⟩ : syracuseStep 1702271 = 2553407) B2553407
theorem B1915375 : Blo 1701551 1915375 := bstep (se 1 (by rfl) ⟨1436531, by rfl⟩ : syracuseStep 1915375 = 2873063) B2873063
theorem B2873839 : Blo 1701551 2873839 := bstep (se 1 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 2873839 = 4310759) B4310759
theorem B1915519 : Blo 1701551 1915519 := bstep (se 1 (by rfl) ⟨1436639, by rfl⟩ : syracuseStep 1915519 = 2873279) B2873279
theorem B10902437 : Blo 1701551 10902437 := bstep (se 4 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 10902437 = 2044207) B2044207
theorem B2554793 : Blo 1701551 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B18406511 : Blo 1701551 18406511 := bstep (se 1 (by rfl) ⟨13804883, by rfl⟩ : syracuseStep 18406511 = 27609767) B27609767
theorem B2555039 : Blo 1701551 2555039 := bstep (se 1 (by rfl) ⟨1916279, by rfl⟩ : syracuseStep 2555039 = 3832559) B3832559
theorem B1703079 : Blo 1701551 1703079 := bstep (se 1 (by rfl) ⟨1277309, by rfl⟩ : syracuseStep 1703079 = 2554619) B2554619
theorem B2555135 : Blo 1701551 2555135 := bstep (se 1 (by rfl) ⟨1916351, by rfl⟩ : syracuseStep 2555135 = 3832703) B3832703
theorem B1703215 : Blo 1701551 1703215 := bstep (se 1 (by rfl) ⟨1277411, by rfl⟩ : syracuseStep 1703215 = 2554823) B2554823
theorem B3636571 : Blo 1701551 3636571 := bstep (se 1 (by rfl) ⟨2727428, by rfl⟩ : syracuseStep 3636571 = 5454857) B5454857
theorem B5176879 : Blo 1701551 5176879 := bstep (se 1 (by rfl) ⟨3882659, by rfl⟩ : syracuseStep 5176879 = 7765319) B7765319
theorem B22117951 : Blo 1701551 22117951 := bstep (se 1 (by rfl) ⟨16588463, by rfl⟩ : syracuseStep 22117951 = 33176927) B33176927
theorem B1818559 : Blo 1701551 1818559 := bstep (se 1 (by rfl) ⟨1363919, by rfl⟩ : syracuseStep 1818559 = 2727839) B2727839
theorem B9208187 : Blo 1701551 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B9699709 : Blo 1701551 9699709 := bstep (se 3 (by rfl) ⟨1818695, by rfl⟩ : syracuseStep 9699709 = 3637391) B3637391
theorem B18416717 : Blo 1701551 18416717 := bstep (se 3 (by rfl) ⟨3453134, by rfl⟩ : syracuseStep 18416717 = 6906269) B6906269
theorem B9332333 : Blo 1701551 9332333 := bstep (se 3 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 9332333 = 3499625) B3499625
theorem B8177597 : Blo 1701551 8177597 := bstep (se 3 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 8177597 = 3066599) B3066599
theorem B7268291 : Blo 1701551 7268291 := bstep (se 1 (by rfl) ⟨5451218, by rfl⟩ : syracuseStep 7268291 = 10902437) B10902437
theorem B4311103 : Blo 1701551 4311103 := bstep (se 1 (by rfl) ⟨3233327, by rfl⟩ : syracuseStep 4311103 = 6466655) B6466655
theorem B3828527 : Blo 1701551 3828527 := bstep (se 1 (by rfl) ⟨2871395, by rfl⟩ : syracuseStep 3828527 = 5742791) B5742791
theorem B27610021 : Blo 1701551 27610021 := bstep (se 4 (by rfl) ⟨2588439, by rfl⟩ : syracuseStep 27610021 = 5176879) B5176879
theorem B478080377 : Blo 1701551 478080377 := bstep (se 2 (by rfl) ⟨179280141, by rfl⟩ : syracuseStep 478080377 = 358560283) B358560283
theorem B13798783 : Blo 1701551 13798783 := bstep (se 1 (by rfl) ⟨10349087, by rfl⟩ : syracuseStep 13798783 = 20698175) B20698175
theorem B132705863 : Blo 1701551 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B3829751 : Blo 1701551 3829751 := bstep (se 1 (by rfl) ⟨2872313, by rfl⟩ : syracuseStep 3829751 = 5744627) B5744627
theorem B20992421 : Blo 1701551 20992421 := bstep (se 4 (by rfl) ⟨1968039, by rfl⟩ : syracuseStep 20992421 = 3936079) B3936079
theorem B19404521 : Blo 1701551 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B3830687 : Blo 1701551 3830687 := bstep (se 1 (by rfl) ⟨2873015, by rfl⟩ : syracuseStep 3830687 = 5746031) B5746031
theorem B4912265 : Blo 1701551 4912265 := bstep (se 2 (by rfl) ⟨1842099, by rfl⟩ : syracuseStep 4912265 = 3684199) B3684199
theorem B8623745 : Blo 1701551 8623745 := bstep (se 2 (by rfl) ⟨3233904, by rfl⟩ : syracuseStep 8623745 = 6467809) B6467809
theorem B117962405 : Blo 1701551 117962405 := bstep (se 4 (by rfl) ⟨11058975, by rfl⟩ : syracuseStep 117962405 = 22117951) B22117951
theorem B3274471 : Blo 1701551 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B2553833 : Blo 1701551 2553833 := bstep (se 2 (by rfl) ⟨957687, by rfl⟩ : syracuseStep 2553833 = 1915375) B1915375
theorem B3831785 : Blo 1701551 3831785 := bstep (se 2 (by rfl) ⟨1436919, by rfl⟩ : syracuseStep 3831785 = 2873839) B2873839
theorem B2554025 : Blo 1701551 2554025 := bstep (se 2 (by rfl) ⟨957759, by rfl⟩ : syracuseStep 2554025 = 1915519) B1915519
theorem B1702095 : Blo 1701551 1702095 := bstep (se 1 (by rfl) ⟨1276571, by rfl⟩ : syracuseStep 1702095 = 2553143) B2553143
theorem B1702335 : Blo 1701551 1702335 := bstep (se 1 (by rfl) ⟨1276751, by rfl⟩ : syracuseStep 1702335 = 2553503) B2553503
theorem B19397231 : Blo 1701551 19397231 := bstep (se 1 (by rfl) ⟨14547923, by rfl⟩ : syracuseStep 19397231 = 29095847) B29095847
theorem B2554607 : Blo 1701551 2554607 := bstep (se 1 (by rfl) ⟨1915955, by rfl⟩ : syracuseStep 2554607 = 3831911) B3831911
theorem B3881785 : Blo 1701551 3881785 := bstep (se 2 (by rfl) ⟨1455669, by rfl⟩ : syracuseStep 3881785 = 2911339) B2911339
theorem B4848511 : Blo 1701551 4848511 := bstep (se 1 (by rfl) ⟨3636383, by rfl⟩ : syracuseStep 4848511 = 7272767) B7272767
theorem B2554751 : Blo 1701551 2554751 := bstep (se 1 (by rfl) ⟨1916063, by rfl⟩ : syracuseStep 2554751 = 3832127) B3832127
theorem B4848761 : Blo 1701551 4848761 := bstep (se 2 (by rfl) ⟨1818285, by rfl⟩ : syracuseStep 4848761 = 3636571) B3636571
theorem B1703195 : Blo 1701551 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B12271007 : Blo 1701551 12271007 := bstep (se 1 (by rfl) ⟨9203255, by rfl⟩ : syracuseStep 12271007 = 18406511) B18406511
theorem B1703359 : Blo 1701551 1703359 := bstep (se 1 (by rfl) ⟨1277519, by rfl⟩ : syracuseStep 1703359 = 2555039) B2555039
theorem B16358881 : Blo 1701551 16358881 := bstep (se 2 (by rfl) ⟨6134580, by rfl⟩ : syracuseStep 16358881 = 12269161) B12269161
theorem B1703423 : Blo 1701551 1703423 := bstep (se 1 (by rfl) ⟨1277567, by rfl⟩ : syracuseStep 1703423 = 2555135) B2555135
theorem B2424745 : Blo 1701551 2424745 := bstep (se 2 (by rfl) ⟨909279, by rfl⟩ : syracuseStep 2424745 = 1818559) B1818559
theorem B12936347 : Blo 1701551 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B6464681 : Blo 1701551 6464681 := bstep (se 2 (by rfl) ⟨2424255, by rfl⟩ : syracuseStep 6464681 = 4848511) B4848511
theorem B318720251 : Blo 1701551 318720251 := bstep (se 1 (by rfl) ⟨239040188, by rfl⟩ : syracuseStep 318720251 = 478080377) B478080377
theorem B6138791 : Blo 1701551 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B13994947 : Blo 1701551 13994947 := bstep (se 1 (by rfl) ⟨10496210, by rfl⟩ : syracuseStep 13994947 = 20992421) B20992421
theorem B12930029 : Blo 1701551 12930029 := bstep (se 3 (by rfl) ⟨2424380, by rfl⟩ : syracuseStep 12930029 = 4848761) B4848761
theorem B6221555 : Blo 1701551 6221555 := bstep (se 1 (by rfl) ⟨4666166, by rfl⟩ : syracuseStep 6221555 = 9332333) B9332333
theorem B5451731 : Blo 1701551 5451731 := bstep (se 1 (by rfl) ⟨4088798, by rfl⟩ : syracuseStep 5451731 = 8177597) B8177597
theorem B4845527 : Blo 1701551 4845527 := bstep (se 1 (by rfl) ⟨3634145, by rfl⟩ : syracuseStep 4845527 = 7268291) B7268291
theorem B12931487 : Blo 1701551 12931487 := bstep (se 1 (by rfl) ⟨9698615, by rfl⟩ : syracuseStep 12931487 = 19397231) B19397231
theorem B2552351 : Blo 1701551 2552351 := bstep (se 1 (by rfl) ⟨1914263, by rfl⟩ : syracuseStep 2552351 = 3828527) B3828527
theorem B21811841 : Blo 1701551 21811841 := bstep (se 2 (by rfl) ⟨8179440, by rfl⟩ : syracuseStep 21811841 = 16358881) B16358881
theorem B12931973 : Blo 1701551 12931973 := bstep (se 4 (by rfl) ⟨1212372, by rfl⟩ : syracuseStep 12931973 = 2424745) B2424745
theorem B8180671 : Blo 1701551 8180671 := bstep (se 1 (by rfl) ⟨6135503, by rfl⟩ : syracuseStep 8180671 = 12271007) B12271007
theorem B88470575 : Blo 1701551 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B2553167 : Blo 1701551 2553167 := bstep (se 1 (by rfl) ⟨1914875, by rfl⟩ : syracuseStep 2553167 = 3829751) B3829751
theorem B5748137 : Blo 1701551 5748137 := bstep (se 2 (by rfl) ⟨2155551, by rfl⟩ : syracuseStep 5748137 = 4311103) B4311103
theorem B12932945 : Blo 1701551 12932945 := bstep (se 2 (by rfl) ⟨4849854, by rfl⟩ : syracuseStep 12932945 = 9699709) B9699709
theorem B2553791 : Blo 1701551 2553791 := bstep (se 1 (by rfl) ⟨1915343, by rfl⟩ : syracuseStep 2553791 = 3830687) B3830687
theorem B12277811 : Blo 1701551 12277811 := bstep (se 1 (by rfl) ⟨9208358, by rfl⟩ : syracuseStep 12277811 = 18416717) B18416717
theorem B3274843 : Blo 1701551 3274843 := bstep (se 1 (by rfl) ⟨2456132, by rfl⟩ : syracuseStep 3274843 = 4912265) B4912265
theorem B5175713 : Blo 1701551 5175713 := bstep (se 2 (by rfl) ⟨1940892, by rfl⟩ : syracuseStep 5175713 = 3881785) B3881785
theorem B78641603 : Blo 1701551 78641603 := bstep (se 1 (by rfl) ⟨58981202, by rfl⟩ : syracuseStep 78641603 = 117962405) B117962405
theorem B17463845 : Blo 1701551 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B36813361 : Blo 1701551 36813361 := bstep (se 2 (by rfl) ⟨13805010, by rfl⟩ : syracuseStep 36813361 = 27610021) B27610021
theorem B1702555 : Blo 1701551 1702555 := bstep (se 1 (by rfl) ⟨1276916, by rfl⟩ : syracuseStep 1702555 = 2553833) B2553833
theorem B2554523 : Blo 1701551 2554523 := bstep (se 1 (by rfl) ⟨1915892, by rfl⟩ : syracuseStep 2554523 = 3831785) B3831785
theorem B1702683 : Blo 1701551 1702683 := bstep (se 1 (by rfl) ⟨1277012, by rfl⟩ : syracuseStep 1702683 = 2554025) B2554025
theorem B1703071 : Blo 1701551 1703071 := bstep (se 1 (by rfl) ⟨1277303, by rfl⟩ : syracuseStep 1703071 = 2554607) B2554607
theorem B18398377 : Blo 1701551 18398377 := bstep (se 2 (by rfl) ⟨6899391, by rfl⟩ : syracuseStep 18398377 = 13798783) B13798783
theorem B1703167 : Blo 1701551 1703167 := bstep (se 1 (by rfl) ⟨1277375, by rfl⟩ : syracuseStep 1703167 = 2554751) B2554751
theorem B5749163 : Blo 1701551 5749163 := bstep (se 1 (by rfl) ⟨4311872, by rfl⟩ : syracuseStep 5749163 = 8623745) B8623745
theorem B4366457 : Blo 1701551 4366457 := bstep (se 2 (by rfl) ⟨1637421, by rfl⟩ : syracuseStep 4366457 = 3274843) B3274843
theorem B14541227 : Blo 1701551 14541227 := bstep (se 1 (by rfl) ⟨10905920, by rfl⟩ : syracuseStep 14541227 = 21811841) B21811841
theorem B4309787 : Blo 1701551 4309787 := bstep (se 1 (by rfl) ⟨3232340, by rfl⟩ : syracuseStep 4309787 = 6464681) B6464681
theorem B8185207 : Blo 1701551 8185207 := bstep (se 1 (by rfl) ⟨6138905, by rfl⟩ : syracuseStep 8185207 = 12277811) B12277811
theorem B3450475 : Blo 1701551 3450475 := bstep (se 1 (by rfl) ⟨2587856, by rfl⟩ : syracuseStep 3450475 = 5175713) B5175713
theorem B11642563 : Blo 1701551 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B8620019 : Blo 1701551 8620019 := bstep (se 1 (by rfl) ⟨6465014, by rfl⟩ : syracuseStep 8620019 = 12930029) B12930029
theorem B4147703 : Blo 1701551 4147703 := bstep (se 1 (by rfl) ⟨3110777, by rfl⟩ : syracuseStep 4147703 = 6221555) B6221555
theorem B3230351 : Blo 1701551 3230351 := bstep (se 1 (by rfl) ⟨2422763, by rfl⟩ : syracuseStep 3230351 = 4845527) B4845527
theorem B8620991 : Blo 1701551 8620991 := bstep (se 1 (by rfl) ⟨6465743, by rfl⟩ : syracuseStep 8620991 = 12931487) B12931487
theorem B8621315 : Blo 1701551 8621315 := bstep (se 1 (by rfl) ⟨6465986, by rfl⟩ : syracuseStep 8621315 = 12931973) B12931973
theorem B8621963 : Blo 1701551 8621963 := bstep (se 1 (by rfl) ⟨6466472, by rfl⟩ : syracuseStep 8621963 = 12932945) B12932945
theorem B10907561 : Blo 1701551 10907561 := bstep (se 2 (by rfl) ⟨4090335, by rfl⟩ : syracuseStep 10907561 = 8180671) B8180671
theorem B212480167 : Blo 1701551 212480167 := bstep (se 1 (by rfl) ⟨159360125, by rfl⟩ : syracuseStep 212480167 = 318720251) B318720251
theorem B24531169 : Blo 1701551 24531169 := bstep (se 2 (by rfl) ⟨9199188, by rfl⟩ : syracuseStep 24531169 = 18398377) B18398377
theorem B4092527 : Blo 1701551 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B3634487 : Blo 1701551 3634487 := bstep (se 1 (by rfl) ⟨2725865, by rfl⟩ : syracuseStep 3634487 = 5451731) B5451731
theorem B1701567 : Blo 1701551 1701567 := bstep (se 1 (by rfl) ⟨1276175, by rfl⟩ : syracuseStep 1701567 = 2552351) B2552351
theorem B58980383 : Blo 1701551 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B49084481 : Blo 1701551 49084481 := bstep (se 2 (by rfl) ⟨18406680, by rfl⟩ : syracuseStep 49084481 = 36813361) B36813361
theorem B8624231 : Blo 1701551 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B1702111 : Blo 1701551 1702111 := bstep (se 1 (by rfl) ⟨1276583, by rfl⟩ : syracuseStep 1702111 = 2553167) B2553167
theorem B3832091 : Blo 1701551 3832091 := bstep (se 1 (by rfl) ⟨2874068, by rfl⟩ : syracuseStep 3832091 = 5748137) B5748137
theorem B18659929 : Blo 1701551 18659929 := bstep (se 2 (by rfl) ⟨6997473, by rfl⟩ : syracuseStep 18659929 = 13994947) B13994947
theorem B1702527 : Blo 1701551 1702527 := bstep (se 1 (by rfl) ⟨1276895, by rfl⟩ : syracuseStep 1702527 = 2553791) B2553791
theorem B3832775 : Blo 1701551 3832775 := bstep (se 1 (by rfl) ⟨2874581, by rfl⟩ : syracuseStep 3832775 = 5749163) B5749163
theorem B52427735 : Blo 1701551 52427735 := bstep (se 1 (by rfl) ⟨39320801, by rfl⟩ : syracuseStep 52427735 = 78641603) B78641603
theorem B1703015 : Blo 1701551 1703015 := bstep (se 1 (by rfl) ⟨1277261, by rfl⟩ : syracuseStep 1703015 = 2554523) B2554523
theorem B2728351 : Blo 1701551 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B24879905 : Blo 1701551 24879905 := bstep (se 2 (by rfl) ⟨9329964, by rfl⟩ : syracuseStep 24879905 = 18659929) B18659929
theorem B10913609 : Blo 1701551 10913609 := bstep (se 2 (by rfl) ⟨4092603, by rfl⟩ : syracuseStep 10913609 = 8185207) B8185207
theorem B2910971 : Blo 1701551 2910971 := bstep (se 1 (by rfl) ⟨2183228, by rfl⟩ : syracuseStep 2910971 = 4366457) B4366457
theorem B283306889 : Blo 1701551 283306889 := bstep (se 2 (by rfl) ⟨106240083, by rfl⟩ : syracuseStep 283306889 = 212480167) B212480167
theorem B9694151 : Blo 1701551 9694151 := bstep (se 1 (by rfl) ⟨7270613, by rfl⟩ : syracuseStep 9694151 = 14541227) B14541227
theorem B5746679 : Blo 1701551 5746679 := bstep (se 1 (by rfl) ⟨4310009, by rfl⟩ : syracuseStep 5746679 = 8620019) B8620019
theorem B32722987 : Blo 1701551 32722987 := bstep (se 1 (by rfl) ⟨24542240, by rfl⟩ : syracuseStep 32722987 = 49084481) B49084481
theorem B2765135 : Blo 1701551 2765135 := bstep (se 1 (by rfl) ⟨2073851, by rfl⟩ : syracuseStep 2765135 = 4147703) B4147703
theorem B5747327 : Blo 1701551 5747327 := bstep (se 1 (by rfl) ⟨4310495, by rfl⟩ : syracuseStep 5747327 = 8620991) B8620991
theorem B34951823 : Blo 1701551 34951823 := bstep (se 1 (by rfl) ⟨26213867, by rfl⟩ : syracuseStep 34951823 = 52427735) B52427735
theorem B4600633 : Blo 1701551 4600633 := bstep (se 2 (by rfl) ⟨1725237, by rfl⟩ : syracuseStep 4600633 = 3450475) B3450475
theorem B5747543 : Blo 1701551 5747543 := bstep (se 1 (by rfl) ⟨4310657, by rfl⟩ : syracuseStep 5747543 = 8621315) B8621315
theorem B5747975 : Blo 1701551 5747975 := bstep (se 1 (by rfl) ⟨4310981, by rfl⟩ : syracuseStep 5747975 = 8621963) B8621963
theorem B7271707 : Blo 1701551 7271707 := bstep (se 1 (by rfl) ⟨5453780, by rfl⟩ : syracuseStep 7271707 = 10907561) B10907561
theorem B32708225 : Blo 1701551 32708225 := bstep (se 2 (by rfl) ⟨12265584, by rfl⟩ : syracuseStep 32708225 = 24531169) B24531169
theorem B2873191 : Blo 1701551 2873191 := bstep (se 1 (by rfl) ⟨2154893, by rfl⟩ : syracuseStep 2873191 = 4309787) B4309787
theorem B2422991 : Blo 1701551 2422991 := bstep (se 1 (by rfl) ⟨1817243, by rfl⟩ : syracuseStep 2422991 = 3634487) B3634487
theorem B39320255 : Blo 1701551 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B5749487 : Blo 1701551 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B2554727 : Blo 1701551 2554727 := bstep (se 1 (by rfl) ⟨1916045, by rfl⟩ : syracuseStep 2554727 = 3832091) B3832091
theorem B2153567 : Blo 1701551 2153567 := bstep (se 1 (by rfl) ⟨1615175, by rfl⟩ : syracuseStep 2153567 = 3230351) B3230351
theorem B2555183 : Blo 1701551 2555183 := bstep (se 1 (by rfl) ⟨1916387, by rfl⟩ : syracuseStep 2555183 = 3832775) B3832775
theorem B15523417 : Blo 1701551 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B43630649 : Blo 1701551 43630649 := bstep (se 2 (by rfl) ⟨16361493, by rfl⟩ : syracuseStep 43630649 = 32722987) B32722987
theorem B5742845 : Blo 1701551 5742845 := bstep (se 3 (by rfl) ⟨1076783, by rfl⟩ : syracuseStep 5742845 = 2153567) B2153567
theorem B3637801 : Blo 1701551 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B7373693 : Blo 1701551 7373693 := bstep (se 3 (by rfl) ⟨1382567, by rfl⟩ : syracuseStep 7373693 = 2765135) B2765135
theorem B7275739 : Blo 1701551 7275739 := bstep (se 1 (by rfl) ⟨5456804, by rfl⟩ : syracuseStep 7275739 = 10913609) B10913609
theorem B23301215 : Blo 1701551 23301215 := bstep (se 1 (by rfl) ⟨17475911, by rfl⟩ : syracuseStep 23301215 = 34951823) B34951823
theorem B9695609 : Blo 1701551 9695609 := bstep (se 2 (by rfl) ⟨3635853, by rfl⟩ : syracuseStep 9695609 = 7271707) B7271707
theorem B188871259 : Blo 1701551 188871259 := bstep (se 1 (by rfl) ⟨141653444, by rfl⟩ : syracuseStep 188871259 = 283306889) B283306889
theorem B20697889 : Blo 1701551 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B3830921 : Blo 1701551 3830921 := bstep (se 2 (by rfl) ⟨1436595, by rfl⟩ : syracuseStep 3830921 = 2873191) B2873191
theorem B3831119 : Blo 1701551 3831119 := bstep (se 1 (by rfl) ⟨2873339, by rfl⟩ : syracuseStep 3831119 = 5746679) B5746679
theorem B3831551 : Blo 1701551 3831551 := bstep (se 1 (by rfl) ⟨2873663, by rfl⟩ : syracuseStep 3831551 = 5747327) B5747327
theorem B16586603 : Blo 1701551 16586603 := bstep (se 1 (by rfl) ⟨12439952, by rfl⟩ : syracuseStep 16586603 = 24879905) B24879905
theorem B6461309 : Blo 1701551 6461309 := bstep (se 3 (by rfl) ⟨1211495, by rfl⟩ : syracuseStep 6461309 = 2422991) B2422991
theorem B3831695 : Blo 1701551 3831695 := bstep (se 1 (by rfl) ⟨2873771, by rfl⟩ : syracuseStep 3831695 = 5747543) B5747543
theorem B3831983 : Blo 1701551 3831983 := bstep (se 1 (by rfl) ⟨2873987, by rfl⟩ : syracuseStep 3831983 = 5747975) B5747975
theorem B6134177 : Blo 1701551 6134177 := bstep (se 2 (by rfl) ⟨2300316, by rfl⟩ : syracuseStep 6134177 = 4600633) B4600633
theorem B21805483 : Blo 1701551 21805483 := bstep (se 1 (by rfl) ⟨16354112, by rfl⟩ : syracuseStep 21805483 = 32708225) B32708225
theorem B26213503 : Blo 1701551 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B3832991 : Blo 1701551 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B1940647 : Blo 1701551 1940647 := bstep (se 1 (by rfl) ⟨1455485, by rfl⟩ : syracuseStep 1940647 = 2910971) B2910971
theorem B1703151 : Blo 1701551 1703151 := bstep (se 1 (by rfl) ⟨1277363, by rfl⟩ : syracuseStep 1703151 = 2554727) B2554727
theorem B6462767 : Blo 1701551 6462767 := bstep (se 1 (by rfl) ⟨4847075, by rfl⟩ : syracuseStep 6462767 = 9694151) B9694151
theorem B1703455 : Blo 1701551 1703455 := bstep (se 1 (by rfl) ⟨1277591, by rfl⟩ : syracuseStep 1703455 = 2555183) B2555183
theorem B6463739 : Blo 1701551 6463739 := bstep (se 1 (by rfl) ⟨4847804, by rfl⟩ : syracuseStep 6463739 = 9695609) B9695609
theorem B29073977 : Blo 1701551 29073977 := bstep (se 2 (by rfl) ⟨10902741, by rfl⟩ : syracuseStep 29073977 = 21805483) B21805483
theorem B4089451 : Blo 1701551 4089451 := bstep (se 1 (by rfl) ⟨3067088, by rfl⟩ : syracuseStep 4089451 = 6134177) B6134177
theorem B9700985 : Blo 1701551 9700985 := bstep (se 2 (by rfl) ⟨3637869, by rfl⟩ : syracuseStep 9700985 = 7275739) B7275739
theorem B15534143 : Blo 1701551 15534143 := bstep (se 1 (by rfl) ⟨11650607, by rfl⟩ : syracuseStep 15534143 = 23301215) B23301215
theorem B19663181 : Blo 1701551 19663181 := bstep (se 3 (by rfl) ⟨3686846, by rfl⟩ : syracuseStep 19663181 = 7373693) B7373693
theorem B3828563 : Blo 1701551 3828563 := bstep (se 1 (by rfl) ⟨2871422, by rfl⟩ : syracuseStep 3828563 = 5742845) B5742845
theorem B19401605 : Blo 1701551 19401605 := bstep (se 4 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 19401605 = 3637801) B3637801
theorem B34951337 : Blo 1701551 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B29087099 : Blo 1701551 29087099 := bstep (se 1 (by rfl) ⟨21815324, by rfl⟩ : syracuseStep 29087099 = 43630649) B43630649
theorem B2553947 : Blo 1701551 2553947 := bstep (se 1 (by rfl) ⟨1915460, by rfl⟩ : syracuseStep 2553947 = 3830921) B3830921
theorem B251828345 : Blo 1701551 251828345 := bstep (se 2 (by rfl) ⟨94435629, by rfl⟩ : syracuseStep 251828345 = 188871259) B188871259
theorem B2554079 : Blo 1701551 2554079 := bstep (se 1 (by rfl) ⟨1915559, by rfl⟩ : syracuseStep 2554079 = 3831119) B3831119
theorem B27597185 : Blo 1701551 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B2554367 : Blo 1701551 2554367 := bstep (se 1 (by rfl) ⟨1915775, by rfl⟩ : syracuseStep 2554367 = 3831551) B3831551
theorem B11057735 : Blo 1701551 11057735 := bstep (se 1 (by rfl) ⟨8293301, by rfl⟩ : syracuseStep 11057735 = 16586603) B16586603
theorem B4307539 : Blo 1701551 4307539 := bstep (se 1 (by rfl) ⟨3230654, by rfl⟩ : syracuseStep 4307539 = 6461309) B6461309
theorem B2554463 : Blo 1701551 2554463 := bstep (se 1 (by rfl) ⟨1915847, by rfl⟩ : syracuseStep 2554463 = 3831695) B3831695
theorem B2554655 : Blo 1701551 2554655 := bstep (se 1 (by rfl) ⟨1915991, by rfl⟩ : syracuseStep 2554655 = 3831983) B3831983
theorem B2587529 : Blo 1701551 2587529 := bstep (se 2 (by rfl) ⟨970323, by rfl⟩ : syracuseStep 2587529 = 1940647) B1940647
theorem B2555327 : Blo 1701551 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B4308511 : Blo 1701551 4308511 := bstep (se 1 (by rfl) ⟨3231383, by rfl⟩ : syracuseStep 4308511 = 6462767) B6462767
theorem B4309159 : Blo 1701551 4309159 := bstep (se 1 (by rfl) ⟨3231869, by rfl⟩ : syracuseStep 4309159 = 6463739) B6463739
theorem B19382651 : Blo 1701551 19382651 := bstep (se 1 (by rfl) ⟨14536988, by rfl⟩ : syracuseStep 19382651 = 29073977) B29073977
theorem B5743385 : Blo 1701551 5743385 := bstep (se 2 (by rfl) ⟨2153769, by rfl⟩ : syracuseStep 5743385 = 4307539) B4307539
theorem B19391399 : Blo 1701551 19391399 := bstep (se 1 (by rfl) ⟨14543549, by rfl⟩ : syracuseStep 19391399 = 29087099) B29087099
theorem B10356095 : Blo 1701551 10356095 := bstep (se 1 (by rfl) ⟨7767071, by rfl⟩ : syracuseStep 10356095 = 15534143) B15534143
theorem B13108787 : Blo 1701551 13108787 := bstep (se 1 (by rfl) ⟨9831590, by rfl⟩ : syracuseStep 13108787 = 19663181) B19663181
theorem B5744681 : Blo 1701551 5744681 := bstep (se 2 (by rfl) ⟨2154255, by rfl⟩ : syracuseStep 5744681 = 4308511) B4308511
theorem B23300891 : Blo 1701551 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B6467323 : Blo 1701551 6467323 := bstep (se 1 (by rfl) ⟨4850492, by rfl⟩ : syracuseStep 6467323 = 9700985) B9700985
theorem B2552375 : Blo 1701551 2552375 := bstep (se 1 (by rfl) ⟨1914281, by rfl⟩ : syracuseStep 2552375 = 3828563) B3828563
theorem B1725019 : Blo 1701551 1725019 := bstep (se 1 (by rfl) ⟨1293764, by rfl⟩ : syracuseStep 1725019 = 2587529) B2587529
theorem B5452601 : Blo 1701551 5452601 := bstep (se 2 (by rfl) ⟨2044725, by rfl⟩ : syracuseStep 5452601 = 4089451) B4089451
theorem B1702631 : Blo 1701551 1702631 := bstep (se 1 (by rfl) ⟨1276973, by rfl⟩ : syracuseStep 1702631 = 2553947) B2553947
theorem B167885563 : Blo 1701551 167885563 := bstep (se 1 (by rfl) ⟨125914172, by rfl⟩ : syracuseStep 167885563 = 251828345) B251828345
theorem B1702719 : Blo 1701551 1702719 := bstep (se 1 (by rfl) ⟨1277039, by rfl⟩ : syracuseStep 1702719 = 2554079) B2554079
theorem B18398123 : Blo 1701551 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B1702911 : Blo 1701551 1702911 := bstep (se 1 (by rfl) ⟨1277183, by rfl⟩ : syracuseStep 1702911 = 2554367) B2554367
theorem B7371823 : Blo 1701551 7371823 := bstep (se 1 (by rfl) ⟨5528867, by rfl⟩ : syracuseStep 7371823 = 11057735) B11057735
theorem B1702975 : Blo 1701551 1702975 := bstep (se 1 (by rfl) ⟨1277231, by rfl⟩ : syracuseStep 1702975 = 2554463) B2554463
theorem B1703103 : Blo 1701551 1703103 := bstep (se 1 (by rfl) ⟨1277327, by rfl⟩ : syracuseStep 1703103 = 2554655) B2554655
theorem B12934403 : Blo 1701551 12934403 := bstep (se 1 (by rfl) ⟨9700802, by rfl⟩ : syracuseStep 12934403 = 19401605) B19401605
theorem B1703551 : Blo 1701551 1703551 := bstep (se 1 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 1703551 = 2555327) B2555327
theorem B9200101 : Blo 1701551 9200101 := bstep (se 4 (by rfl) ⟨862509, by rfl⟩ : syracuseStep 9200101 = 1725019) B1725019
theorem B12927599 : Blo 1701551 12927599 := bstep (se 1 (by rfl) ⟨9695699, by rfl⟩ : syracuseStep 12927599 = 19391399) B19391399
theorem B223847417 : Blo 1701551 223847417 := bstep (se 2 (by rfl) ⟨83942781, by rfl⟩ : syracuseStep 223847417 = 167885563) B167885563
theorem B15533927 : Blo 1701551 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B12265415 : Blo 1701551 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B5745545 : Blo 1701551 5745545 := bstep (se 2 (by rfl) ⟨2154579, by rfl⟩ : syracuseStep 5745545 = 4309159) B4309159
theorem B12921767 : Blo 1701551 12921767 := bstep (se 1 (by rfl) ⟨9691325, by rfl⟩ : syracuseStep 12921767 = 19382651) B19382651
theorem B3828923 : Blo 1701551 3828923 := bstep (se 1 (by rfl) ⟨2871692, by rfl⟩ : syracuseStep 3828923 = 5743385) B5743385
theorem B3829787 : Blo 1701551 3829787 := bstep (se 1 (by rfl) ⟨2872340, by rfl⟩ : syracuseStep 3829787 = 5744681) B5744681
theorem B8622935 : Blo 1701551 8622935 := bstep (se 1 (by rfl) ⟨6467201, by rfl⟩ : syracuseStep 8622935 = 12934403) B12934403
theorem B8623097 : Blo 1701551 8623097 := bstep (se 2 (by rfl) ⟨3233661, by rfl⟩ : syracuseStep 8623097 = 6467323) B6467323
theorem B1701583 : Blo 1701551 1701583 := bstep (se 1 (by rfl) ⟨1276187, by rfl⟩ : syracuseStep 1701583 = 2552375) B2552375
theorem B6904063 : Blo 1701551 6904063 := bstep (se 1 (by rfl) ⟨5178047, by rfl⟩ : syracuseStep 6904063 = 10356095) B10356095
theorem B8739191 : Blo 1701551 8739191 := bstep (se 1 (by rfl) ⟨6554393, by rfl⟩ : syracuseStep 8739191 = 13108787) B13108787
theorem B9829097 : Blo 1701551 9829097 := bstep (se 2 (by rfl) ⟨3685911, by rfl⟩ : syracuseStep 9829097 = 7371823) B7371823
theorem B14540269 : Blo 1701551 14540269 := bstep (se 3 (by rfl) ⟨2726300, by rfl⟩ : syracuseStep 14540269 = 5452601) B5452601
theorem B8618399 : Blo 1701551 8618399 := bstep (se 1 (by rfl) ⟨6463799, by rfl⟩ : syracuseStep 8618399 = 12927599) B12927599
theorem B10355951 : Blo 1701551 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B8176943 : Blo 1701551 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B5826127 : Blo 1701551 5826127 := bstep (se 1 (by rfl) ⟨4369595, by rfl⟩ : syracuseStep 5826127 = 8739191) B8739191
theorem B12266801 : Blo 1701551 12266801 := bstep (se 2 (by rfl) ⟨4600050, by rfl⟩ : syracuseStep 12266801 = 9200101) B9200101
theorem B3830363 : Blo 1701551 3830363 := bstep (se 1 (by rfl) ⟨2872772, by rfl⟩ : syracuseStep 3830363 = 5745545) B5745545
theorem B8614511 : Blo 1701551 8614511 := bstep (se 1 (by rfl) ⟨6460883, by rfl⟩ : syracuseStep 8614511 = 12921767) B12921767
theorem B19387025 : Blo 1701551 19387025 := bstep (se 2 (by rfl) ⟨7270134, by rfl⟩ : syracuseStep 19387025 = 14540269) B14540269
theorem B2552615 : Blo 1701551 2552615 := bstep (se 1 (by rfl) ⟨1914461, by rfl⟩ : syracuseStep 2552615 = 3828923) B3828923
theorem B2553191 : Blo 1701551 2553191 := bstep (se 1 (by rfl) ⟨1914893, by rfl⟩ : syracuseStep 2553191 = 3829787) B3829787
theorem B9205417 : Blo 1701551 9205417 := bstep (se 2 (by rfl) ⟨3452031, by rfl⟩ : syracuseStep 9205417 = 6904063) B6904063
theorem B5748623 : Blo 1701551 5748623 := bstep (se 1 (by rfl) ⟨4311467, by rfl⟩ : syracuseStep 5748623 = 8622935) B8622935
theorem B149231611 : Blo 1701551 149231611 := bstep (se 1 (by rfl) ⟨111923708, by rfl⟩ : syracuseStep 149231611 = 223847417) B223847417
theorem B5748731 : Blo 1701551 5748731 := bstep (se 1 (by rfl) ⟨4311548, by rfl⟩ : syracuseStep 5748731 = 8623097) B8623097
theorem B6552731 : Blo 1701551 6552731 := bstep (se 1 (by rfl) ⟨4914548, by rfl⟩ : syracuseStep 6552731 = 9829097) B9829097
theorem B5743007 : Blo 1701551 5743007 := bstep (se 1 (by rfl) ⟨4307255, by rfl⟩ : syracuseStep 5743007 = 8614511) B8614511
theorem B4368487 : Blo 1701551 4368487 := bstep (se 1 (by rfl) ⟨3276365, by rfl⟩ : syracuseStep 4368487 = 6552731) B6552731
theorem B7768169 : Blo 1701551 7768169 := bstep (se 2 (by rfl) ⟨2913063, by rfl⟩ : syracuseStep 7768169 = 5826127) B5826127
theorem B8177867 : Blo 1701551 8177867 := bstep (se 1 (by rfl) ⟨6133400, by rfl⟩ : syracuseStep 8177867 = 12266801) B12266801
theorem B12273889 : Blo 1701551 12273889 := bstep (se 2 (by rfl) ⟨4602708, by rfl⟩ : syracuseStep 12273889 = 9205417) B9205417
theorem B5745599 : Blo 1701551 5745599 := bstep (se 1 (by rfl) ⟨4309199, by rfl⟩ : syracuseStep 5745599 = 8618399) B8618399
theorem B5451295 : Blo 1701551 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B2553575 : Blo 1701551 2553575 := bstep (se 1 (by rfl) ⟨1915181, by rfl⟩ : syracuseStep 2553575 = 3830363) B3830363
theorem B12924683 : Blo 1701551 12924683 := bstep (se 1 (by rfl) ⟨9693512, by rfl⟩ : syracuseStep 12924683 = 19387025) B19387025
theorem B1701743 : Blo 1701551 1701743 := bstep (se 1 (by rfl) ⟨1276307, by rfl⟩ : syracuseStep 1701743 = 2552615) B2552615
theorem B6903967 : Blo 1701551 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B1702127 : Blo 1701551 1702127 := bstep (se 1 (by rfl) ⟨1276595, by rfl⟩ : syracuseStep 1702127 = 2553191) B2553191
theorem B3832415 : Blo 1701551 3832415 := bstep (se 1 (by rfl) ⟨2874311, by rfl⟩ : syracuseStep 3832415 = 5748623) B5748623
theorem B3832487 : Blo 1701551 3832487 := bstep (se 1 (by rfl) ⟨2874365, by rfl⟩ : syracuseStep 3832487 = 5748731) B5748731
theorem B795901925 : Blo 1701551 795901925 := bstep (se 4 (by rfl) ⟨74615805, by rfl⟩ : syracuseStep 795901925 = 149231611) B149231611
theorem B5824649 : Blo 1701551 5824649 := bstep (se 2 (by rfl) ⟨2184243, by rfl⟩ : syracuseStep 5824649 = 4368487) B4368487
theorem B5178779 : Blo 1701551 5178779 := bstep (se 1 (by rfl) ⟨3884084, by rfl⟩ : syracuseStep 5178779 = 7768169) B7768169
theorem B7268393 : Blo 1701551 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B3828671 : Blo 1701551 3828671 := bstep (se 1 (by rfl) ⟨2871503, by rfl⟩ : syracuseStep 3828671 = 5743007) B5743007
theorem B5451911 : Blo 1701551 5451911 := bstep (se 1 (by rfl) ⟨4088933, by rfl⟩ : syracuseStep 5451911 = 8177867) B8177867
theorem B3830399 : Blo 1701551 3830399 := bstep (se 1 (by rfl) ⟨2872799, by rfl⟩ : syracuseStep 3830399 = 5745599) B5745599
theorem B530601283 : Blo 1701551 530601283 := bstep (se 1 (by rfl) ⟨397950962, by rfl⟩ : syracuseStep 530601283 = 795901925) B795901925
theorem B9205289 : Blo 1701551 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B16365185 : Blo 1701551 16365185 := bstep (se 2 (by rfl) ⟨6136944, by rfl⟩ : syracuseStep 16365185 = 12273889) B12273889
theorem B1702383 : Blo 1701551 1702383 := bstep (se 1 (by rfl) ⟨1276787, by rfl⟩ : syracuseStep 1702383 = 2553575) B2553575
theorem B8616455 : Blo 1701551 8616455 := bstep (se 1 (by rfl) ⟨6462341, by rfl⟩ : syracuseStep 8616455 = 12924683) B12924683
theorem B2554943 : Blo 1701551 2554943 := bstep (se 1 (by rfl) ⟨1916207, by rfl⟩ : syracuseStep 2554943 = 3832415) B3832415
theorem B2554991 : Blo 1701551 2554991 := bstep (se 1 (by rfl) ⟨1916243, by rfl⟩ : syracuseStep 2554991 = 3832487) B3832487
theorem B3883099 : Blo 1701551 3883099 := bstep (se 1 (by rfl) ⟨2912324, by rfl⟩ : syracuseStep 3883099 = 5824649) B5824649
theorem B6136859 : Blo 1701551 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B5744303 : Blo 1701551 5744303 := bstep (se 1 (by rfl) ⟨4308227, by rfl⟩ : syracuseStep 5744303 = 8616455) B8616455
theorem B3452519 : Blo 1701551 3452519 := bstep (se 1 (by rfl) ⟨2589389, by rfl⟩ : syracuseStep 3452519 = 5178779) B5178779
theorem B4845595 : Blo 1701551 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B2552447 : Blo 1701551 2552447 := bstep (se 1 (by rfl) ⟨1914335, by rfl⟩ : syracuseStep 2552447 = 3828671) B3828671
theorem B3634607 : Blo 1701551 3634607 := bstep (se 1 (by rfl) ⟨2725955, by rfl⟩ : syracuseStep 3634607 = 5451911) B5451911
theorem B2553599 : Blo 1701551 2553599 := bstep (se 1 (by rfl) ⟨1915199, by rfl⟩ : syracuseStep 2553599 = 3830399) B3830399
theorem B10910123 : Blo 1701551 10910123 := bstep (se 1 (by rfl) ⟨8182592, by rfl⟩ : syracuseStep 10910123 = 16365185) B16365185
theorem B707468377 : Blo 1701551 707468377 := bstep (se 2 (by rfl) ⟨265300641, by rfl⟩ : syracuseStep 707468377 = 530601283) B530601283
theorem B1703295 : Blo 1701551 1703295 := bstep (se 1 (by rfl) ⟨1277471, by rfl⟩ : syracuseStep 1703295 = 2554943) B2554943
theorem B1703327 : Blo 1701551 1703327 := bstep (se 1 (by rfl) ⟨1277495, by rfl⟩ : syracuseStep 1703327 = 2554991) B2554991
theorem B5177465 : Blo 1701551 5177465 := bstep (se 2 (by rfl) ⟨1941549, by rfl⟩ : syracuseStep 5177465 = 3883099) B3883099
theorem B4091239 : Blo 1701551 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B3829535 : Blo 1701551 3829535 := bstep (se 1 (by rfl) ⟨2872151, by rfl⟩ : syracuseStep 3829535 = 5744303) B5744303
theorem B6460793 : Blo 1701551 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B1701631 : Blo 1701551 1701631 := bstep (se 1 (by rfl) ⟨1276223, by rfl⟩ : syracuseStep 1701631 = 2552447) B2552447
theorem B2423071 : Blo 1701551 2423071 := bstep (se 1 (by rfl) ⟨1817303, by rfl⟩ : syracuseStep 2423071 = 3634607) B3634607
theorem B1702399 : Blo 1701551 1702399 := bstep (se 1 (by rfl) ⟨1276799, by rfl⟩ : syracuseStep 1702399 = 2553599) B2553599
theorem B943291169 : Blo 1701551 943291169 := bstep (se 2 (by rfl) ⟨353734188, by rfl⟩ : syracuseStep 943291169 = 707468377) B707468377
theorem B7273415 : Blo 1701551 7273415 := bstep (se 1 (by rfl) ⟨5455061, by rfl⟩ : syracuseStep 7273415 = 10910123) B10910123
theorem B2301679 : Blo 1701551 2301679 := bstep (se 1 (by rfl) ⟨1726259, by rfl⟩ : syracuseStep 2301679 = 3452519) B3452519
theorem B628860779 : Blo 1701551 628860779 := bstep (se 1 (by rfl) ⟨471645584, by rfl⟩ : syracuseStep 628860779 = 943291169) B943291169
theorem B3451643 : Blo 1701551 3451643 := bstep (se 1 (by rfl) ⟨2588732, by rfl⟩ : syracuseStep 3451643 = 5177465) B5177465
theorem B3230761 : Blo 1701551 3230761 := bstep (se 2 (by rfl) ⟨1211535, by rfl⟩ : syracuseStep 3230761 = 2423071) B2423071
theorem B12275621 : Blo 1701551 12275621 := bstep (se 4 (by rfl) ⟨1150839, by rfl⟩ : syracuseStep 12275621 = 2301679) B2301679
theorem B21819941 : Blo 1701551 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B19395773 : Blo 1701551 19395773 := bstep (se 3 (by rfl) ⟨3636707, by rfl⟩ : syracuseStep 19395773 = 7273415) B7273415
theorem B2553023 : Blo 1701551 2553023 := bstep (se 1 (by rfl) ⟨1914767, by rfl⟩ : syracuseStep 2553023 = 3829535) B3829535
theorem B4307195 : Blo 1701551 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B14546627 : Blo 1701551 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B12930515 : Blo 1701551 12930515 := bstep (se 1 (by rfl) ⟨9697886, by rfl⟩ : syracuseStep 12930515 = 19395773) B19395773
theorem B2871463 : Blo 1701551 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B1702015 : Blo 1701551 1702015 := bstep (se 1 (by rfl) ⟨1276511, by rfl⟩ : syracuseStep 1702015 = 2553023) B2553023
theorem B419240519 : Blo 1701551 419240519 := bstep (se 1 (by rfl) ⟨314430389, by rfl⟩ : syracuseStep 419240519 = 628860779) B628860779
theorem B4307681 : Blo 1701551 4307681 := bstep (se 2 (by rfl) ⟨1615380, by rfl⟩ : syracuseStep 4307681 = 3230761) B3230761
theorem B2301095 : Blo 1701551 2301095 := bstep (se 1 (by rfl) ⟨1725821, by rfl⟩ : syracuseStep 2301095 = 3451643) B3451643
theorem B8183747 : Blo 1701551 8183747 := bstep (se 1 (by rfl) ⟨6137810, by rfl⟩ : syracuseStep 8183747 = 12275621) B12275621
theorem B6136253 : Blo 1701551 6136253 := bstep (se 3 (by rfl) ⟨1150547, by rfl⟩ : syracuseStep 6136253 = 2301095) B2301095
theorem B8620343 : Blo 1701551 8620343 := bstep (se 1 (by rfl) ⟨6465257, by rfl⟩ : syracuseStep 8620343 = 12930515) B12930515
theorem B3828617 : Blo 1701551 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B2871787 : Blo 1701551 2871787 := bstep (se 1 (by rfl) ⟨2153840, by rfl⟩ : syracuseStep 2871787 = 4307681) B4307681
theorem B9697751 : Blo 1701551 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B279493679 : Blo 1701551 279493679 := bstep (se 1 (by rfl) ⟨209620259, by rfl⟩ : syracuseStep 279493679 = 419240519) B419240519
theorem B5455831 : Blo 1701551 5455831 := bstep (se 1 (by rfl) ⟨4091873, by rfl⟩ : syracuseStep 5455831 = 8183747) B8183747
theorem B6465167 : Blo 1701551 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B186329119 : Blo 1701551 186329119 := bstep (se 1 (by rfl) ⟨139746839, by rfl⟩ : syracuseStep 186329119 = 279493679) B279493679
theorem B4090835 : Blo 1701551 4090835 := bstep (se 1 (by rfl) ⟨3068126, by rfl⟩ : syracuseStep 4090835 = 6136253) B6136253
theorem B3829049 : Blo 1701551 3829049 := bstep (se 2 (by rfl) ⟨1435893, by rfl⟩ : syracuseStep 3829049 = 2871787) B2871787
theorem B5746895 : Blo 1701551 5746895 := bstep (se 1 (by rfl) ⟨4310171, by rfl⟩ : syracuseStep 5746895 = 8620343) B8620343
theorem B2552411 : Blo 1701551 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B7274441 : Blo 1701551 7274441 := bstep (se 2 (by rfl) ⟨2727915, by rfl⟩ : syracuseStep 7274441 = 5455831) B5455831
theorem B248438825 : Blo 1701551 248438825 := bstep (se 2 (by rfl) ⟨93164559, by rfl⟩ : syracuseStep 248438825 = 186329119) B186329119
theorem B4310111 : Blo 1701551 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B2552699 : Blo 1701551 2552699 := bstep (se 1 (by rfl) ⟨1914524, by rfl⟩ : syracuseStep 2552699 = 3829049) B3829049
theorem B10908893 : Blo 1701551 10908893 := bstep (se 3 (by rfl) ⟨2045417, by rfl⟩ : syracuseStep 10908893 = 4090835) B4090835
theorem B3831263 : Blo 1701551 3831263 := bstep (se 1 (by rfl) ⟨2873447, by rfl⟩ : syracuseStep 3831263 = 5746895) B5746895
theorem B1701607 : Blo 1701551 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B4849627 : Blo 1701551 4849627 := bstep (se 1 (by rfl) ⟨3637220, by rfl⟩ : syracuseStep 4849627 = 7274441) B7274441
theorem B165625883 : Blo 1701551 165625883 := bstep (se 1 (by rfl) ⟨124219412, by rfl⟩ : syracuseStep 165625883 = 248438825) B248438825
theorem B6466169 : Blo 1701551 6466169 := bstep (se 2 (by rfl) ⟨2424813, by rfl⟩ : syracuseStep 6466169 = 4849627) B4849627
theorem B1701799 : Blo 1701551 1701799 := bstep (se 1 (by rfl) ⟨1276349, by rfl⟩ : syracuseStep 1701799 = 2552699) B2552699
theorem B2873407 : Blo 1701551 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B7272595 : Blo 1701551 7272595 := bstep (se 1 (by rfl) ⟨5454446, by rfl⟩ : syracuseStep 7272595 = 10908893) B10908893
theorem B2554175 : Blo 1701551 2554175 := bstep (se 1 (by rfl) ⟨1915631, by rfl⟩ : syracuseStep 2554175 = 3831263) B3831263
theorem B4310779 : Blo 1701551 4310779 := bstep (se 1 (by rfl) ⟨3233084, by rfl⟩ : syracuseStep 4310779 = 6466169) B6466169
theorem B110417255 : Blo 1701551 110417255 := bstep (se 1 (by rfl) ⟨82812941, by rfl⟩ : syracuseStep 110417255 = 165625883) B165625883
theorem B3831209 : Blo 1701551 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B9696793 : Blo 1701551 9696793 := bstep (se 2 (by rfl) ⟨3636297, by rfl⟩ : syracuseStep 9696793 = 7272595) B7272595
theorem B1702783 : Blo 1701551 1702783 := bstep (se 1 (by rfl) ⟨1277087, by rfl⟩ : syracuseStep 1702783 = 2554175) B2554175
theorem B12929057 : Blo 1701551 12929057 := bstep (se 2 (by rfl) ⟨4848396, by rfl⟩ : syracuseStep 12929057 = 9696793) B9696793
theorem B5747705 : Blo 1701551 5747705 := bstep (se 2 (by rfl) ⟨2155389, by rfl⟩ : syracuseStep 5747705 = 4310779) B4310779
theorem B73611503 : Blo 1701551 73611503 := bstep (se 1 (by rfl) ⟨55208627, by rfl⟩ : syracuseStep 73611503 = 110417255) B110417255
theorem B2554139 : Blo 1701551 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B8619371 : Blo 1701551 8619371 := bstep (se 1 (by rfl) ⟨6464528, by rfl⟩ : syracuseStep 8619371 = 12929057) B12929057
theorem B49074335 : Blo 1701551 49074335 := bstep (se 1 (by rfl) ⟨36805751, by rfl⟩ : syracuseStep 49074335 = 73611503) B73611503
theorem B3831803 : Blo 1701551 3831803 := bstep (se 1 (by rfl) ⟨2873852, by rfl⟩ : syracuseStep 3831803 = 5747705) B5747705
theorem B1702759 : Blo 1701551 1702759 := bstep (se 1 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 1702759 = 2554139) B2554139
theorem B5746247 : Blo 1701551 5746247 := bstep (se 1 (by rfl) ⟨4309685, by rfl⟩ : syracuseStep 5746247 = 8619371) B8619371
theorem B32716223 : Blo 1701551 32716223 := bstep (se 1 (by rfl) ⟨24537167, by rfl⟩ : syracuseStep 32716223 = 49074335) B49074335
theorem B2554535 : Blo 1701551 2554535 := bstep (se 1 (by rfl) ⟨1915901, by rfl⟩ : syracuseStep 2554535 = 3831803) B3831803
theorem B21810815 : Blo 1701551 21810815 := bstep (se 1 (by rfl) ⟨16358111, by rfl⟩ : syracuseStep 21810815 = 32716223) B32716223
theorem B3830831 : Blo 1701551 3830831 := bstep (se 1 (by rfl) ⟨2873123, by rfl⟩ : syracuseStep 3830831 = 5746247) B5746247
theorem B1703023 : Blo 1701551 1703023 := bstep (se 1 (by rfl) ⟨1277267, by rfl⟩ : syracuseStep 1703023 = 2554535) B2554535
theorem B2553887 : Blo 1701551 2553887 := bstep (se 1 (by rfl) ⟨1915415, by rfl⟩ : syracuseStep 2553887 = 3830831) B3830831
theorem B14540543 : Blo 1701551 14540543 := bstep (se 1 (by rfl) ⟨10905407, by rfl⟩ : syracuseStep 14540543 = 21810815) B21810815
theorem B9693695 : Blo 1701551 9693695 := bstep (se 1 (by rfl) ⟨7270271, by rfl⟩ : syracuseStep 9693695 = 14540543) B14540543
theorem B1702591 : Blo 1701551 1702591 := bstep (se 1 (by rfl) ⟨1276943, by rfl⟩ : syracuseStep 1702591 = 2553887) B2553887
theorem B6462463 : Blo 1701551 6462463 := bstep (se 1 (by rfl) ⟨4846847, by rfl⟩ : syracuseStep 6462463 = 9693695) B9693695
theorem B8616617 : Blo 1701551 8616617 := bstep (se 2 (by rfl) ⟨3231231, by rfl⟩ : syracuseStep 8616617 = 6462463) B6462463
theorem B5744411 : Blo 1701551 5744411 := bstep (se 1 (by rfl) ⟨4308308, by rfl⟩ : syracuseStep 5744411 = 8616617) B8616617
theorem B3829607 : Blo 1701551 3829607 := bstep (se 1 (by rfl) ⟨2872205, by rfl⟩ : syracuseStep 3829607 = 5744411) B5744411
theorem B2553071 : Blo 1701551 2553071 := bstep (se 1 (by rfl) ⟨1914803, by rfl⟩ : syracuseStep 2553071 = 3829607) B3829607
theorem B1702047 : Blo 1701551 1702047 := bstep (se 1 (by rfl) ⟨1276535, by rfl⟩ : syracuseStep 1702047 = 2553071) B2553071

theorem C0 (j : ℕ) (h1 : 425387 ≤ j) (h2 : j ≤ 425887) : Blo 1701551 (4 * j + 3) := by
  interval_cases j
  · exact B1701551
  · exact B1701555
  · exact B1701559
  · exact B1701563
  · exact B1701567
  · exact B1701571
  · exact B1701575
  · exact B1701579
  · exact B1701583
  · exact B1701587
  · exact B1701591
  · exact B1701595
  · exact B1701599
  · exact B1701603
  · exact B1701607
  · exact B1701611
  · exact B1701615
  · exact B1701619
  · exact B1701623
  · exact B1701627
  · exact B1701631
  · exact B1701635
  · exact B1701639
  · exact B1701643
  · exact B1701647
  · exact B1701651
  · exact B1701655
  · exact B1701659
  · exact B1701663
  · exact B1701667
  · exact B1701671
  · exact B1701675
  · exact B1701679
  · exact B1701683
  · exact B1701687
  · exact B1701691
  · exact B1701695
  · exact B1701699
  · exact B1701703
  · exact B1701707
  · exact B1701711
  · exact B1701715
  · exact B1701719
  · exact B1701723
  · exact B1701727
  · exact B1701731
  · exact B1701735
  · exact B1701739
  · exact B1701743
  · exact B1701747
  · exact B1701751
  · exact B1701755
  · exact B1701759
  · exact B1701763
  · exact B1701767
  · exact B1701771
  · exact B1701775
  · exact B1701779
  · exact B1701783
  · exact B1701787
  · exact B1701791
  · exact B1701795
  · exact B1701799
  · exact B1701803
  · exact B1701807
  · exact B1701811
  · exact B1701815
  · exact B1701819
  · exact B1701823
  · exact B1701827
  · exact B1701831
  · exact B1701835
  · exact B1701839
  · exact B1701843
  · exact B1701847
  · exact B1701851
  · exact B1701855
  · exact B1701859
  · exact B1701863
  · exact B1701867
  · exact B1701871
  · exact B1701875
  · exact B1701879
  · exact B1701883
  · exact B1701887
  · exact B1701891
  · exact B1701895
  · exact B1701899
  · exact B1701903
  · exact B1701907
  · exact B1701911
  · exact B1701915
  · exact B1701919
  · exact B1701923
  · exact B1701927
  · exact B1701931
  · exact B1701935
  · exact B1701939
  · exact B1701943
  · exact B1701947
  · exact B1701951
  · exact B1701955
  · exact B1701959
  · exact B1701963
  · exact B1701967
  · exact B1701971
  · exact B1701975
  · exact B1701979
  · exact B1701983
  · exact B1701987
  · exact B1701991
  · exact B1701995
  · exact B1701999
  · exact B1702003
  · exact B1702007
  · exact B1702011
  · exact B1702015
  · exact B1702019
  · exact B1702023
  · exact B1702027
  · exact B1702031
  · exact B1702035
  · exact B1702039
  · exact B1702043
  · exact B1702047
  · exact B1702051
  · exact B1702055
  · exact B1702059
  · exact B1702063
  · exact B1702067
  · exact B1702071
  · exact B1702075
  · exact B1702079
  · exact B1702083
  · exact B1702087
  · exact B1702091
  · exact B1702095
  · exact B1702099
  · exact B1702103
  · exact B1702107
  · exact B1702111
  · exact B1702115
  · exact B1702119
  · exact B1702123
  · exact B1702127
  · exact B1702131
  · exact B1702135
  · exact B1702139
  · exact B1702143
  · exact B1702147
  · exact B1702151
  · exact B1702155
  · exact B1702159
  · exact B1702163
  · exact B1702167
  · exact B1702171
  · exact B1702175
  · exact B1702179
  · exact B1702183
  · exact B1702187
  · exact B1702191
  · exact B1702195
  · exact B1702199
  · exact B1702203
  · exact B1702207
  · exact B1702211
  · exact B1702215
  · exact B1702219
  · exact B1702223
  · exact B1702227
  · exact B1702231
  · exact B1702235
  · exact B1702239
  · exact B1702243
  · exact B1702247
  · exact B1702251
  · exact B1702255
  · exact B1702259
  · exact B1702263
  · exact B1702267
  · exact B1702271
  · exact B1702275
  · exact B1702279
  · exact B1702283
  · exact B1702287
  · exact B1702291
  · exact B1702295
  · exact B1702299
  · exact B1702303
  · exact B1702307
  · exact B1702311
  · exact B1702315
  · exact B1702319
  · exact B1702323
  · exact B1702327
  · exact B1702331
  · exact B1702335
  · exact B1702339
  · exact B1702343
  · exact B1702347
  · exact B1702351
  · exact B1702355
  · exact B1702359
  · exact B1702363
  · exact B1702367
  · exact B1702371
  · exact B1702375
  · exact B1702379
  · exact B1702383
  · exact B1702387
  · exact B1702391
  · exact B1702395
  · exact B1702399
  · exact B1702403
  · exact B1702407
  · exact B1702411
  · exact B1702415
  · exact B1702419
  · exact B1702423
  · exact B1702427
  · exact B1702431
  · exact B1702435
  · exact B1702439
  · exact B1702443
  · exact B1702447
  · exact B1702451
  · exact B1702455
  · exact B1702459
  · exact B1702463
  · exact B1702467
  · exact B1702471
  · exact B1702475
  · exact B1702479
  · exact B1702483
  · exact B1702487
  · exact B1702491
  · exact B1702495
  · exact B1702499
  · exact B1702503
  · exact B1702507
  · exact B1702511
  · exact B1702515
  · exact B1702519
  · exact B1702523
  · exact B1702527
  · exact B1702531
  · exact B1702535
  · exact B1702539
  · exact B1702543
  · exact B1702547
  · exact B1702551
  · exact B1702555
  · exact B1702559
  · exact B1702563
  · exact B1702567
  · exact B1702571
  · exact B1702575
  · exact B1702579
  · exact B1702583
  · exact B1702587
  · exact B1702591
  · exact B1702595
  · exact B1702599
  · exact B1702603
  · exact B1702607
  · exact B1702611
  · exact B1702615
  · exact B1702619
  · exact B1702623
  · exact B1702627
  · exact B1702631
  · exact B1702635
  · exact B1702639
  · exact B1702643
  · exact B1702647
  · exact B1702651
  · exact B1702655
  · exact B1702659
  · exact B1702663
  · exact B1702667
  · exact B1702671
  · exact B1702675
  · exact B1702679
  · exact B1702683
  · exact B1702687
  · exact B1702691
  · exact B1702695
  · exact B1702699
  · exact B1702703
  · exact B1702707
  · exact B1702711
  · exact B1702715
  · exact B1702719
  · exact B1702723
  · exact B1702727
  · exact B1702731
  · exact B1702735
  · exact B1702739
  · exact B1702743
  · exact B1702747
  · exact B1702751
  · exact B1702755
  · exact B1702759
  · exact B1702763
  · exact B1702767
  · exact B1702771
  · exact B1702775
  · exact B1702779
  · exact B1702783
  · exact B1702787
  · exact B1702791
  · exact B1702795
  · exact B1702799
  · exact B1702803
  · exact B1702807
  · exact B1702811
  · exact B1702815
  · exact B1702819
  · exact B1702823
  · exact B1702827
  · exact B1702831
  · exact B1702835
  · exact B1702839
  · exact B1702843
  · exact B1702847
  · exact B1702851
  · exact B1702855
  · exact B1702859
  · exact B1702863
  · exact B1702867
  · exact B1702871
  · exact B1702875
  · exact B1702879
  · exact B1702883
  · exact B1702887
  · exact B1702891
  · exact B1702895
  · exact B1702899
  · exact B1702903
  · exact B1702907
  · exact B1702911
  · exact B1702915
  · exact B1702919
  · exact B1702923
  · exact B1702927
  · exact B1702931
  · exact B1702935
  · exact B1702939
  · exact B1702943
  · exact B1702947
  · exact B1702951
  · exact B1702955
  · exact B1702959
  · exact B1702963
  · exact B1702967
  · exact B1702971
  · exact B1702975
  · exact B1702979
  · exact B1702983
  · exact B1702987
  · exact B1702991
  · exact B1702995
  · exact B1702999
  · exact B1703003
  · exact B1703007
  · exact B1703011
  · exact B1703015
  · exact B1703019
  · exact B1703023
  · exact B1703027
  · exact B1703031
  · exact B1703035
  · exact B1703039
  · exact B1703043
  · exact B1703047
  · exact B1703051
  · exact B1703055
  · exact B1703059
  · exact B1703063
  · exact B1703067
  · exact B1703071
  · exact B1703075
  · exact B1703079
  · exact B1703083
  · exact B1703087
  · exact B1703091
  · exact B1703095
  · exact B1703099
  · exact B1703103
  · exact B1703107
  · exact B1703111
  · exact B1703115
  · exact B1703119
  · exact B1703123
  · exact B1703127
  · exact B1703131
  · exact B1703135
  · exact B1703139
  · exact B1703143
  · exact B1703147
  · exact B1703151
  · exact B1703155
  · exact B1703159
  · exact B1703163
  · exact B1703167
  · exact B1703171
  · exact B1703175
  · exact B1703179
  · exact B1703183
  · exact B1703187
  · exact B1703191
  · exact B1703195
  · exact B1703199
  · exact B1703203
  · exact B1703207
  · exact B1703211
  · exact B1703215
  · exact B1703219
  · exact B1703223
  · exact B1703227
  · exact B1703231
  · exact B1703235
  · exact B1703239
  · exact B1703243
  · exact B1703247
  · exact B1703251
  · exact B1703255
  · exact B1703259
  · exact B1703263
  · exact B1703267
  · exact B1703271
  · exact B1703275
  · exact B1703279
  · exact B1703283
  · exact B1703287
  · exact B1703291
  · exact B1703295
  · exact B1703299
  · exact B1703303
  · exact B1703307
  · exact B1703311
  · exact B1703315
  · exact B1703319
  · exact B1703323
  · exact B1703327
  · exact B1703331
  · exact B1703335
  · exact B1703339
  · exact B1703343
  · exact B1703347
  · exact B1703351
  · exact B1703355
  · exact B1703359
  · exact B1703363
  · exact B1703367
  · exact B1703371
  · exact B1703375
  · exact B1703379
  · exact B1703383
  · exact B1703387
  · exact B1703391
  · exact B1703395
  · exact B1703399
  · exact B1703403
  · exact B1703407
  · exact B1703411
  · exact B1703415
  · exact B1703419
  · exact B1703423
  · exact B1703427
  · exact B1703431
  · exact B1703435
  · exact B1703439
  · exact B1703443
  · exact B1703447
  · exact B1703451
  · exact B1703455
  · exact B1703459
  · exact B1703463
  · exact B1703467
  · exact B1703471
  · exact B1703475
  · exact B1703479
  · exact B1703483
  · exact B1703487
  · exact B1703491
  · exact B1703495
  · exact B1703499
  · exact B1703503
  · exact B1703507
  · exact B1703511
  · exact B1703515
  · exact B1703519
  · exact B1703523
  · exact B1703527
  · exact B1703531
  · exact B1703535
  · exact B1703539
  · exact B1703543
  · exact B1703547
  · exact B1703551

theorem solution (m : ℕ) (hlo : 1701551 ≤ m) (hhi : m ≤ 1703551) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 425387 ≤ j := by omega
    have hj2 : j ≤ 425887 := by omega
    have hb : Blo 1701551 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
