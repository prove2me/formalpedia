-- Prove2me | solution 1 for syracuse_descends_range_1788095_1790095
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:46:34.067077+00:00
-- url     : https://prove2.me/submissions/572655de-2894-4bf8-869f-0c531bedb3d0

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


theorem B5734405 : Blo 1788095 5734405 := bbase (se 4 (by rfl) ⟨537600, by rfl⟩ : syracuseStep 5734405 = 1075201) (by norm_num)
theorem B4300813 : Blo 1788095 4300813 := bbase (se 3 (by rfl) ⟨806402, by rfl⟩ : syracuseStep 4300813 = 1612805) (by norm_num)
theorem B5734469 : Blo 1788095 5734469 := bbase (se 4 (by rfl) ⟨537606, by rfl⟩ : syracuseStep 5734469 = 1075213) (by norm_num)
theorem B4530269 : Blo 1788095 4530269 := bbase (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) (by norm_num)
theorem B2547821 : Blo 1788095 2547821 := bbase (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) (by norm_num)
theorem B6037685 : Blo 1788095 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B2449693 : Blo 1788095 2449693 := bbase (se 3 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 2449693 = 918635) (by norm_num)
theorem B7643429 : Blo 1788095 7643429 := bbase (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) (by norm_num)
theorem B2040121 : Blo 1788095 2040121 := bbase (se 2 (by rfl) ⟨765045, by rfl⟩ : syracuseStep 2040121 = 1530091) (by norm_num)
theorem B2417045 : Blo 1788095 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B17432981 : Blo 1788095 17432981 := bbase (se 6 (by rfl) ⟨408585, by rfl⟩ : syracuseStep 17432981 = 817171) (by norm_num)
theorem B4358549 : Blo 1788095 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B2040241 : Blo 1788095 2040241 := bbase (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) (by norm_num)
theorem B4530613 : Blo 1788095 4530613 := bbase (se 5 (by rfl) ⟨212372, by rfl⟩ : syracuseStep 4530613 = 424745) (by norm_num)
theorem B9060821 : Blo 1788095 9060821 := bbase (se 7 (by rfl) ⟨106181, by rfl⟩ : syracuseStep 9060821 = 212363) (by norm_num)
theorem B8159717 : Blo 1788095 8159717 := bbase (se 4 (by rfl) ⟨764973, by rfl⟩ : syracuseStep 8159717 = 1529947) (by norm_num)
theorem B5095973 : Blo 1788095 5095973 := bbase (se 4 (by rfl) ⟨477747, by rfl⟩ : syracuseStep 5095973 = 955495) (by norm_num)
theorem B4530725 : Blo 1788095 4530725 := bbase (se 4 (by rfl) ⟨424755, by rfl⟩ : syracuseStep 4530725 = 849511) (by norm_num)
theorem B6038117 : Blo 1788095 6038117 := bbase (se 4 (by rfl) ⟨566073, by rfl⟩ : syracuseStep 6038117 = 1132147) (by norm_num)
theorem B2417261 : Blo 1788095 2417261 := bbase (se 3 (by rfl) ⟨453236, by rfl⟩ : syracuseStep 2417261 = 906473) (by norm_num)
theorem B2450045 : Blo 1788095 2450045 := bbase (se 3 (by rfl) ⟨459383, by rfl⟩ : syracuseStep 2450045 = 918767) (by norm_num)
theorem B4530917 : Blo 1788095 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B7742213 : Blo 1788095 7742213 := bbase (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) (by norm_num)
theorem B2417413 : Blo 1788095 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B6791957 : Blo 1788095 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B17204021 : Blo 1788095 17204021 := bbase (se 5 (by rfl) ⟨806438, by rfl⟩ : syracuseStep 17204021 = 1612877) (by norm_num)
theorem B9053045 : Blo 1788095 9053045 := bbase (se 5 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 9053045 = 848723) (by norm_num)
theorem B1909661 : Blo 1788095 1909661 := bbase (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) (by norm_num)
theorem B4023269 : Blo 1788095 4023269 := bbase (se 4 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 4023269 = 754363) (by norm_num)
theorem B6038549 : Blo 1788095 6038549 := bbase (se 6 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 6038549 = 283057) (by norm_num)
theorem B4023341 : Blo 1788095 4023341 := bbase (se 3 (by rfl) ⟨754376, by rfl⟩ : syracuseStep 4023341 = 1508753) (by norm_num)
theorem B6792245 : Blo 1788095 6792245 := bbase (se 5 (by rfl) ⟨318386, by rfl⟩ : syracuseStep 6792245 = 636773) (by norm_num)
theorem B10183765 : Blo 1788095 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B4023413 : Blo 1788095 4023413 := bbase (se 5 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 4023413 = 377195) (by norm_num)
theorem B1909909 : Blo 1788095 1909909 := bbase (se 6 (by rfl) ⟨44763, by rfl⟩ : syracuseStep 1909909 = 89527) (by norm_num)
theorem B2040997 : Blo 1788095 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B4023485 : Blo 1788095 4023485 := bbase (se 3 (by rfl) ⟨754403, by rfl⟩ : syracuseStep 4023485 = 1508807) (by norm_num)
theorem B5096645 : Blo 1788095 5096645 := bbase (se 4 (by rfl) ⟨477810, by rfl⟩ : syracuseStep 5096645 = 955621) (by norm_num)
theorem B4359413 : Blo 1788095 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B4023557 : Blo 1788095 4023557 := bbase (se 4 (by rfl) ⟨377208, by rfl⟩ : syracuseStep 4023557 = 754417) (by norm_num)
theorem B4023629 : Blo 1788095 4023629 := bbase (se 3 (by rfl) ⟨754430, by rfl⟩ : syracuseStep 4023629 = 1508861) (by norm_num)
theorem B4023701 : Blo 1788095 4023701 := bbase (se 6 (by rfl) ⟨94305, by rfl⟩ : syracuseStep 4023701 = 188611) (by norm_num)
theorem B6038981 : Blo 1788095 6038981 := bbase (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) (by norm_num)
theorem B4023773 : Blo 1788095 4023773 := bbase (se 3 (by rfl) ⟨754457, by rfl⟩ : syracuseStep 4023773 = 1508915) (by norm_num)
theorem B3818981 : Blo 1788095 3818981 := bbase (se 4 (by rfl) ⟨358029, by rfl⟩ : syracuseStep 3818981 = 716059) (by norm_num)
theorem B4023845 : Blo 1788095 4023845 := bbase (se 4 (by rfl) ⟨377235, by rfl⟩ : syracuseStep 4023845 = 754471) (by norm_num)
theorem B3442213 : Blo 1788095 3442213 := bbase (se 4 (by rfl) ⟨322707, by rfl⟩ : syracuseStep 3442213 = 645415) (by norm_num)
theorem B8595013 : Blo 1788095 8595013 := bbase (se 4 (by rfl) ⟨805782, by rfl⟩ : syracuseStep 8595013 = 1611565) (by norm_num)
theorem B1910341 : Blo 1788095 1910341 := bbase (se 4 (by rfl) ⟨179094, by rfl⟩ : syracuseStep 1910341 = 358189) (by norm_num)
theorem B4023917 : Blo 1788095 4023917 := bbase (se 3 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 4023917 = 1508969) (by norm_num)
theorem B5097077 : Blo 1788095 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B2295425 : Blo 1788095 2295425 := bbase (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) (by norm_num)
theorem B1910413 : Blo 1788095 1910413 := bbase (se 3 (by rfl) ⟨358202, by rfl⟩ : syracuseStep 1910413 = 716405) (by norm_num)
theorem B4023989 : Blo 1788095 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B9062117 : Blo 1788095 9062117 := bbase (se 4 (by rfl) ⟨849573, by rfl⟩ : syracuseStep 9062117 = 1699147) (by norm_num)
theorem B4024061 : Blo 1788095 4024061 := bbase (se 3 (by rfl) ⟨754511, by rfl⟩ : syracuseStep 4024061 = 1509023) (by norm_num)
theorem B2295577 : Blo 1788095 2295577 := bbase (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) (by norm_num)
theorem B4024133 : Blo 1788095 4024133 := bbase (se 4 (by rfl) ⟨377262, by rfl⟩ : syracuseStep 4024133 = 754525) (by norm_num)
theorem B5810005 : Blo 1788095 5810005 := bbase (se 9 (by rfl) ⟨17021, by rfl⟩ : syracuseStep 5810005 = 34043) (by norm_num)
theorem B4835173 : Blo 1788095 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B6039413 : Blo 1788095 6039413 := bbase (se 5 (by rfl) ⟨283097, by rfl⟩ : syracuseStep 6039413 = 566195) (by norm_num)
theorem B4024205 : Blo 1788095 4024205 := bbase (se 3 (by rfl) ⟨754538, by rfl⟩ : syracuseStep 4024205 = 1509077) (by norm_num)
theorem B2295697 : Blo 1788095 2295697 := bbase (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) (by norm_num)
theorem B2721701 : Blo 1788095 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B4024277 : Blo 1788095 4024277 := bbase (se 7 (by rfl) ⟨47159, by rfl⟩ : syracuseStep 4024277 = 94319) (by norm_num)
theorem B1910785 : Blo 1788095 1910785 := bbase (se 2 (by rfl) ⟨716544, by rfl⟩ : syracuseStep 1910785 = 1433089) (by norm_num)
theorem B7645205 : Blo 1788095 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B2263069 : Blo 1788095 2263069 := bbase (se 3 (by rfl) ⟨424325, by rfl⟩ : syracuseStep 2263069 = 848651) (by norm_num)
theorem B4024349 : Blo 1788095 4024349 := bbase (se 3 (by rfl) ⟨754565, by rfl⟩ : syracuseStep 4024349 = 1509131) (by norm_num)
theorem B1812557 : Blo 1788095 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B4024421 : Blo 1788095 4024421 := bbase (se 4 (by rfl) ⟨377289, by rfl⟩ : syracuseStep 4024421 = 754579) (by norm_num)
theorem B9054341 : Blo 1788095 9054341 := bbase (se 4 (by rfl) ⟨848844, by rfl⟩ : syracuseStep 9054341 = 1697689) (by norm_num)
theorem B5728421 : Blo 1788095 5728421 := bbase (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) (by norm_num)
theorem B4024493 : Blo 1788095 4024493 := bbase (se 3 (by rfl) ⟨754592, by rfl⟩ : syracuseStep 4024493 = 1509185) (by norm_num)
theorem B2263241 : Blo 1788095 2263241 := bbase (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) (by norm_num)
theorem B6793429 : Blo 1788095 6793429 := bbase (se 7 (by rfl) ⟨79610, by rfl⟩ : syracuseStep 6793429 = 159221) (by norm_num)
theorem B4024565 : Blo 1788095 4024565 := bbase (se 5 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 4024565 = 377303) (by norm_num)
theorem B2263297 : Blo 1788095 2263297 := bbase (se 2 (by rfl) ⟨848736, by rfl⟩ : syracuseStep 2263297 = 1697473) (by norm_num)
theorem B6039845 : Blo 1788095 6039845 := bbase (se 4 (by rfl) ⟨566235, by rfl⟩ : syracuseStep 6039845 = 1132471) (by norm_num)
theorem B4024637 : Blo 1788095 4024637 := bbase (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) (by norm_num)
theorem B2263393 : Blo 1788095 2263393 := bbase (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) (by norm_num)
theorem B2148725 : Blo 1788095 2148725 := bbase (se 5 (by rfl) ⟨100721, by rfl⟩ : syracuseStep 2148725 = 201443) (by norm_num)
theorem B1911161 : Blo 1788095 1911161 := bbase (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) (by norm_num)
theorem B4024709 : Blo 1788095 4024709 := bbase (se 4 (by rfl) ⟨377316, by rfl⟩ : syracuseStep 4024709 = 754633) (by norm_num)
theorem B2148773 : Blo 1788095 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B1911233 : Blo 1788095 1911233 := bbase (se 2 (by rfl) ⟨716712, by rfl⟩ : syracuseStep 1911233 = 1433425) (by norm_num)
theorem B6121925 : Blo 1788095 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B4024781 : Blo 1788095 4024781 := bbase (se 3 (by rfl) ⟨754646, by rfl⟩ : syracuseStep 4024781 = 1509293) (by norm_num)
theorem B1837549 : Blo 1788095 1837549 := bbase (se 3 (by rfl) ⟨344540, by rfl⟩ : syracuseStep 1837549 = 689081) (by norm_num)
theorem B3443197 : Blo 1788095 3443197 := bbase (se 3 (by rfl) ⟨645599, by rfl⟩ : syracuseStep 3443197 = 1291199) (by norm_num)
theorem B2148869 : Blo 1788095 2148869 := bbase (se 4 (by rfl) ⟨201456, by rfl⟩ : syracuseStep 2148869 = 402913) (by norm_num)
theorem B6793733 : Blo 1788095 6793733 := bbase (se 4 (by rfl) ⟨636912, by rfl⟩ : syracuseStep 6793733 = 1273825) (by norm_num)
theorem B2263565 : Blo 1788095 2263565 := bbase (se 3 (by rfl) ⟨424418, by rfl⟩ : syracuseStep 2263565 = 848837) (by norm_num)
theorem B4024853 : Blo 1788095 4024853 := bbase (se 6 (by rfl) ⟨94332, by rfl⟩ : syracuseStep 4024853 = 188665) (by norm_num)
theorem B2263621 : Blo 1788095 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B4024925 : Blo 1788095 4024925 := bbase (se 3 (by rfl) ⟨754673, by rfl⟩ : syracuseStep 4024925 = 1509347) (by norm_num)
theorem B2583149 : Blo 1788095 2583149 := bbase (se 3 (by rfl) ⟨484340, by rfl⟩ : syracuseStep 2583149 = 968681) (by norm_num)
theorem B1911421 : Blo 1788095 1911421 := bbase (se 3 (by rfl) ⟨358391, by rfl⟩ : syracuseStep 1911421 = 716783) (by norm_num)
theorem B1813141 : Blo 1788095 1813141 := bbase (se 6 (by rfl) ⟨42495, by rfl⟩ : syracuseStep 1813141 = 84991) (by norm_num)
theorem B2263717 : Blo 1788095 2263717 := bbase (se 4 (by rfl) ⟨212223, by rfl⟩ : syracuseStep 2263717 = 424447) (by norm_num)
theorem B4024997 : Blo 1788095 4024997 := bbase (se 4 (by rfl) ⟨377343, by rfl⟩ : syracuseStep 4024997 = 754687) (by norm_num)
theorem B2149033 : Blo 1788095 2149033 := bbase (se 2 (by rfl) ⟨805887, by rfl⟩ : syracuseStep 2149033 = 1611775) (by norm_num)
theorem B39217877 : Blo 1788095 39217877 := bbase (se 7 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 39217877 = 919169) (by norm_num)
theorem B6040277 : Blo 1788095 6040277 := bbase (se 7 (by rfl) ⟨70784, by rfl⟩ : syracuseStep 6040277 = 141569) (by norm_num)
theorem B4025069 : Blo 1788095 4025069 := bbase (se 3 (by rfl) ⟨754700, by rfl⟩ : syracuseStep 4025069 = 1509401) (by norm_num)
theorem B3222317 : Blo 1788095 3222317 := bbase (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) (by norm_num)
theorem B4025141 : Blo 1788095 4025141 := bbase (se 5 (by rfl) ⟨188678, by rfl⟩ : syracuseStep 4025141 = 377357) (by norm_num)
theorem B3017533 : Blo 1788095 3017533 := bbase (se 3 (by rfl) ⟨565787, by rfl⟩ : syracuseStep 3017533 = 1131575) (by norm_num)
theorem B2263889 : Blo 1788095 2263889 := bbase (se 2 (by rfl) ⟨848958, by rfl⟩ : syracuseStep 2263889 = 1697917) (by norm_num)
theorem B4025213 : Blo 1788095 4025213 := bbase (se 3 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 4025213 = 1509455) (by norm_num)
theorem B2149249 : Blo 1788095 2149249 := bbase (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) (by norm_num)
theorem B2263945 : Blo 1788095 2263945 := bbase (se 2 (by rfl) ⟨848979, by rfl⟩ : syracuseStep 2263945 = 1697959) (by norm_num)
theorem B3017621 : Blo 1788095 3017621 := bbase (se 6 (by rfl) ⟨70725, by rfl⟩ : syracuseStep 3017621 = 141451) (by norm_num)
theorem B4025285 : Blo 1788095 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B2264041 : Blo 1788095 2264041 := bbase (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) (by norm_num)
theorem B7646197 : Blo 1788095 7646197 := bbase (se 5 (by rfl) ⟨358415, by rfl⟩ : syracuseStep 7646197 = 716831) (by norm_num)
theorem B4025357 : Blo 1788095 4025357 := bbase (se 3 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 4025357 = 1509509) (by norm_num)
theorem B3017749 : Blo 1788095 3017749 := bbase (se 6 (by rfl) ⟨70728, by rfl⟩ : syracuseStep 3017749 = 141457) (by norm_num)
theorem B10185749 : Blo 1788095 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B2149417 : Blo 1788095 2149417 := bbase (se 2 (by rfl) ⟨806031, by rfl⟩ : syracuseStep 2149417 = 1612063) (by norm_num)
theorem B15486005 : Blo 1788095 15486005 := bbase (se 5 (by rfl) ⟨725906, by rfl⟩ : syracuseStep 15486005 = 1451813) (by norm_num)
theorem B3222605 : Blo 1788095 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B3820621 : Blo 1788095 3820621 := bbase (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) (by norm_num)
theorem B4025429 : Blo 1788095 4025429 := bbase (se 8 (by rfl) ⟨23586, by rfl⟩ : syracuseStep 4025429 = 47173) (by norm_num)
theorem B3017837 : Blo 1788095 3017837 := bbase (se 3 (by rfl) ⟨565844, by rfl⟩ : syracuseStep 3017837 = 1131689) (by norm_num)
theorem B6040709 : Blo 1788095 6040709 := bbase (se 4 (by rfl) ⟨566316, by rfl⟩ : syracuseStep 6040709 = 1132633) (by norm_num)
theorem B2264213 : Blo 1788095 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B19614869 : Blo 1788095 19614869 := bbase (se 6 (by rfl) ⟨459723, by rfl⟩ : syracuseStep 19614869 = 919447) (by norm_num)
theorem B4025501 : Blo 1788095 4025501 := bbase (se 3 (by rfl) ⟨754781, by rfl⟩ : syracuseStep 4025501 = 1509563) (by norm_num)
theorem B2264269 : Blo 1788095 2264269 := bbase (se 3 (by rfl) ⟨424550, by rfl⟩ : syracuseStep 2264269 = 849101) (by norm_num)
theorem B4025573 : Blo 1788095 4025573 := bbase (se 4 (by rfl) ⟨377397, by rfl⟩ : syracuseStep 4025573 = 754795) (by norm_num)
theorem B3017965 : Blo 1788095 3017965 := bbase (se 3 (by rfl) ⟨565868, by rfl⟩ : syracuseStep 3017965 = 1131737) (by norm_num)
theorem B1813757 : Blo 1788095 1813757 := bbase (se 3 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 1813757 = 680159) (by norm_num)
theorem B2682149 : Blo 1788095 2682149 := bbase (se 4 (by rfl) ⟨251451, by rfl⟩ : syracuseStep 2682149 = 502903) (by norm_num)
theorem B2264365 : Blo 1788095 2264365 := bbase (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) (by norm_num)
theorem B4025645 : Blo 1788095 4025645 := bbase (se 3 (by rfl) ⟨754808, by rfl⟩ : syracuseStep 4025645 = 1509617) (by norm_num)
theorem B2682173 : Blo 1788095 2682173 := bbase (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) (by norm_num)
theorem B3394885 : Blo 1788095 3394885 := bbase (se 4 (by rfl) ⟨318270, by rfl⟩ : syracuseStep 3394885 = 636541) (by norm_num)
theorem B3018053 : Blo 1788095 3018053 := bbase (se 4 (by rfl) ⟨282942, by rfl⟩ : syracuseStep 3018053 = 565885) (by norm_num)
theorem B2682197 : Blo 1788095 2682197 := bbase (se 11 (by rfl) ⟨1964, by rfl⟩ : syracuseStep 2682197 = 3929) (by norm_num)
theorem B2682221 : Blo 1788095 2682221 := bbase (se 3 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 2682221 = 1005833) (by norm_num)
theorem B4025717 : Blo 1788095 4025717 := bbase (se 5 (by rfl) ⟨188705, by rfl⟩ : syracuseStep 4025717 = 377411) (by norm_num)
theorem B2682245 : Blo 1788095 2682245 := bbase (se 4 (by rfl) ⟨251460, by rfl⟩ : syracuseStep 2682245 = 502921) (by norm_num)
theorem B9055637 : Blo 1788095 9055637 := bbase (se 6 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 9055637 = 424483) (by norm_num)
theorem B2682269 : Blo 1788095 2682269 := bbase (se 3 (by rfl) ⟨502925, by rfl⟩ : syracuseStep 2682269 = 1005851) (by norm_num)
theorem B2682293 : Blo 1788095 2682293 := bbase (se 5 (by rfl) ⟨125732, by rfl⟩ : syracuseStep 2682293 = 251465) (by norm_num)
theorem B4025789 : Blo 1788095 4025789 := bbase (se 3 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 4025789 = 1509671) (by norm_num)
theorem B3018181 : Blo 1788095 3018181 := bbase (se 4 (by rfl) ⟨282954, by rfl⟩ : syracuseStep 3018181 = 565909) (by norm_num)
theorem B2682317 : Blo 1788095 2682317 := bbase (se 3 (by rfl) ⟨502934, by rfl⟩ : syracuseStep 2682317 = 1005869) (by norm_num)
theorem B3395029 : Blo 1788095 3395029 := bbase (se 7 (by rfl) ⟨39785, by rfl⟩ : syracuseStep 3395029 = 79571) (by norm_num)
theorem B16141781 : Blo 1788095 16141781 := bbase (se 7 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 16141781 = 378323) (by norm_num)
theorem B2264537 : Blo 1788095 2264537 := bbase (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) (by norm_num)
theorem B2682341 : Blo 1788095 2682341 := bbase (se 4 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 2682341 = 502939) (by norm_num)
theorem B2682365 : Blo 1788095 2682365 := bbase (se 3 (by rfl) ⟨502943, by rfl⟩ : syracuseStep 2682365 = 1005887) (by norm_num)
theorem B4025861 : Blo 1788095 4025861 := bbase (se 4 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 4025861 = 754849) (by norm_num)
theorem B2264593 : Blo 1788095 2264593 := bbase (se 2 (by rfl) ⟨849222, by rfl⟩ : syracuseStep 2264593 = 1698445) (by norm_num)
theorem B2682389 : Blo 1788095 2682389 := bbase (se 6 (by rfl) ⟨62868, by rfl⟩ : syracuseStep 2682389 = 125737) (by norm_num)
theorem B3018269 : Blo 1788095 3018269 := bbase (se 3 (by rfl) ⟨565925, by rfl⟩ : syracuseStep 3018269 = 1131851) (by norm_num)
theorem B2682413 : Blo 1788095 2682413 := bbase (se 3 (by rfl) ⟨502952, by rfl⟩ : syracuseStep 2682413 = 1005905) (by norm_num)
theorem B6041141 : Blo 1788095 6041141 := bbase (se 5 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 6041141 = 566357) (by norm_num)
theorem B2149945 : Blo 1788095 2149945 := bbase (se 2 (by rfl) ⟨806229, by rfl⟩ : syracuseStep 2149945 = 1612459) (by norm_num)
theorem B2682437 : Blo 1788095 2682437 := bbase (se 4 (by rfl) ⟨251478, by rfl⟩ : syracuseStep 2682437 = 502957) (by norm_num)
theorem B4025933 : Blo 1788095 4025933 := bbase (se 3 (by rfl) ⟨754862, by rfl⟩ : syracuseStep 4025933 = 1509725) (by norm_num)
theorem B2682461 : Blo 1788095 2682461 := bbase (se 3 (by rfl) ⟨502961, by rfl⟩ : syracuseStep 2682461 = 1005923) (by norm_num)
theorem B2264689 : Blo 1788095 2264689 := bbase (se 2 (by rfl) ⟨849258, by rfl⟩ : syracuseStep 2264689 = 1698517) (by norm_num)
theorem B2682485 : Blo 1788095 2682485 := bbase (se 5 (by rfl) ⟨125741, by rfl⟩ : syracuseStep 2682485 = 251483) (by norm_num)
theorem B3395189 : Blo 1788095 3395189 := bbase (se 5 (by rfl) ⟨159149, by rfl⟩ : syracuseStep 3395189 = 318299) (by norm_num)
theorem B2682509 : Blo 1788095 2682509 := bbase (se 3 (by rfl) ⟨502970, by rfl⟩ : syracuseStep 2682509 = 1005941) (by norm_num)
theorem B4026005 : Blo 1788095 4026005 := bbase (se 6 (by rfl) ⟨94359, by rfl⟩ : syracuseStep 4026005 = 188719) (by norm_num)
theorem B3018397 : Blo 1788095 3018397 := bbase (se 3 (by rfl) ⟨565949, by rfl⟩ : syracuseStep 3018397 = 1131899) (by norm_num)
theorem B2682533 : Blo 1788095 2682533 := bbase (se 4 (by rfl) ⟨251487, by rfl⟩ : syracuseStep 2682533 = 502975) (by norm_num)
theorem B2682557 : Blo 1788095 2682557 := bbase (se 3 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 2682557 = 1005959) (by norm_num)
theorem B1937101 : Blo 1788095 1937101 := bbase (se 3 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 1937101 = 726413) (by norm_num)
theorem B12889813 : Blo 1788095 12889813 := bbase (se 7 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 12889813 = 302105) (by norm_num)
theorem B2682581 : Blo 1788095 2682581 := bbase (se 7 (by rfl) ⟨31436, by rfl⟩ : syracuseStep 2682581 = 62873) (by norm_num)
theorem B4026077 : Blo 1788095 4026077 := bbase (se 3 (by rfl) ⟨754889, by rfl⟩ : syracuseStep 4026077 = 1509779) (by norm_num)
theorem B2682605 : Blo 1788095 2682605 := bbase (se 3 (by rfl) ⟨502988, by rfl⟩ : syracuseStep 2682605 = 1005977) (by norm_num)
theorem B3018485 : Blo 1788095 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B2682629 : Blo 1788095 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B3395333 : Blo 1788095 3395333 := bbase (se 4 (by rfl) ⟨318312, by rfl⟩ : syracuseStep 3395333 = 636625) (by norm_num)
theorem B1814285 : Blo 1788095 1814285 := bbase (se 3 (by rfl) ⟨340178, by rfl⟩ : syracuseStep 1814285 = 680357) (by norm_num)
theorem B2682653 : Blo 1788095 2682653 := bbase (se 3 (by rfl) ⟨502997, by rfl⟩ : syracuseStep 2682653 = 1005995) (by norm_num)
theorem B2264861 : Blo 1788095 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B4026149 : Blo 1788095 4026149 := bbase (se 4 (by rfl) ⟨377451, by rfl⟩ : syracuseStep 4026149 = 754903) (by norm_num)
theorem B2682677 : Blo 1788095 2682677 := bbase (se 5 (by rfl) ⟨125750, by rfl⟩ : syracuseStep 2682677 = 251501) (by norm_num)
theorem B2682701 : Blo 1788095 2682701 := bbase (se 3 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 2682701 = 1006013) (by norm_num)
theorem B2264917 : Blo 1788095 2264917 := bbase (se 9 (by rfl) ⟨6635, by rfl⟩ : syracuseStep 2264917 = 13271) (by norm_num)
theorem B2682725 : Blo 1788095 2682725 := bbase (se 4 (by rfl) ⟨251505, by rfl⟩ : syracuseStep 2682725 = 503011) (by norm_num)
theorem B4026221 : Blo 1788095 4026221 := bbase (se 3 (by rfl) ⟨754916, by rfl⟩ : syracuseStep 4026221 = 1509833) (by norm_num)
theorem B3018613 : Blo 1788095 3018613 := bbase (se 5 (by rfl) ⟨141497, by rfl⟩ : syracuseStep 3018613 = 282995) (by norm_num)
theorem B2682749 : Blo 1788095 2682749 := bbase (se 3 (by rfl) ⟨503015, by rfl⟩ : syracuseStep 2682749 = 1006031) (by norm_num)
theorem B2682773 : Blo 1788095 2682773 := bbase (se 6 (by rfl) ⟨62877, by rfl⟩ : syracuseStep 2682773 = 125755) (by norm_num)
theorem B2682797 : Blo 1788095 2682797 := bbase (se 3 (by rfl) ⟨503024, by rfl⟩ : syracuseStep 2682797 = 1006049) (by norm_num)
theorem B4026293 : Blo 1788095 4026293 := bbase (se 5 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 4026293 = 377465) (by norm_num)
theorem B2265013 : Blo 1788095 2265013 := bbase (se 5 (by rfl) ⟨106172, by rfl⟩ : syracuseStep 2265013 = 212345) (by norm_num)
theorem B2682821 : Blo 1788095 2682821 := bbase (se 4 (by rfl) ⟨251514, by rfl⟩ : syracuseStep 2682821 = 503029) (by norm_num)
theorem B3821509 : Blo 1788095 3821509 := bbase (se 4 (by rfl) ⟨358266, by rfl⟩ : syracuseStep 3821509 = 716533) (by norm_num)
theorem B3018701 : Blo 1788095 3018701 := bbase (se 3 (by rfl) ⟨566006, by rfl⟩ : syracuseStep 3018701 = 1132013) (by norm_num)
theorem B2682845 : Blo 1788095 2682845 := bbase (se 3 (by rfl) ⟨503033, by rfl⟩ : syracuseStep 2682845 = 1006067) (by norm_num)
theorem B6041573 : Blo 1788095 6041573 := bbase (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) (by norm_num)
theorem B2682869 : Blo 1788095 2682869 := bbase (se 5 (by rfl) ⟨125759, by rfl⟩ : syracuseStep 2682869 = 251519) (by norm_num)
theorem B4026365 : Blo 1788095 4026365 := bbase (se 3 (by rfl) ⟨754943, by rfl⟩ : syracuseStep 4026365 = 1509887) (by norm_num)
theorem B2682893 : Blo 1788095 2682893 := bbase (se 3 (by rfl) ⟨503042, by rfl⟩ : syracuseStep 2682893 = 1006085) (by norm_num)
theorem B2682917 : Blo 1788095 2682917 := bbase (se 4 (by rfl) ⟨251523, by rfl⟩ : syracuseStep 2682917 = 503047) (by norm_num)
theorem B3395621 : Blo 1788095 3395621 := bbase (se 4 (by rfl) ⟨318339, by rfl⟩ : syracuseStep 3395621 = 636679) (by norm_num)
theorem B2682941 : Blo 1788095 2682941 := bbase (se 3 (by rfl) ⟨503051, by rfl⟩ : syracuseStep 2682941 = 1006103) (by norm_num)
theorem B4026437 : Blo 1788095 4026437 := bbase (se 4 (by rfl) ⟨377478, by rfl⟩ : syracuseStep 4026437 = 754957) (by norm_num)
theorem B3018829 : Blo 1788095 3018829 := bbase (se 3 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 3018829 = 1132061) (by norm_num)
theorem B2682965 : Blo 1788095 2682965 := bbase (se 8 (by rfl) ⟨15720, by rfl⟩ : syracuseStep 2682965 = 31441) (by norm_num)
theorem B2265185 : Blo 1788095 2265185 := bbase (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) (by norm_num)
theorem B4526189 : Blo 1788095 4526189 := bbase (se 3 (by rfl) ⟨848660, by rfl⟩ : syracuseStep 4526189 = 1697321) (by norm_num)
theorem B2682989 : Blo 1788095 2682989 := bbase (se 3 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 2682989 = 1006121) (by norm_num)
theorem B2683013 : Blo 1788095 2683013 := bbase (se 4 (by rfl) ⟨251532, by rfl⟩ : syracuseStep 2683013 = 503065) (by norm_num)
theorem B4026509 : Blo 1788095 4026509 := bbase (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) (by norm_num)
theorem B2265241 : Blo 1788095 2265241 := bbase (se 2 (by rfl) ⟨849465, by rfl⟩ : syracuseStep 2265241 = 1698931) (by norm_num)
theorem B2683037 : Blo 1788095 2683037 := bbase (se 3 (by rfl) ⟨503069, by rfl⟩ : syracuseStep 2683037 = 1006139) (by norm_num)
theorem B3018917 : Blo 1788095 3018917 := bbase (se 4 (by rfl) ⟨283023, by rfl⟩ : syracuseStep 3018917 = 566047) (by norm_num)
theorem B2683061 : Blo 1788095 2683061 := bbase (se 5 (by rfl) ⟨125768, by rfl⟩ : syracuseStep 2683061 = 251537) (by norm_num)
theorem B3395773 : Blo 1788095 3395773 := bbase (se 3 (by rfl) ⟨636707, by rfl⟩ : syracuseStep 3395773 = 1273415) (by norm_num)
theorem B2683085 : Blo 1788095 2683085 := bbase (se 3 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 2683085 = 1006157) (by norm_num)
theorem B4026581 : Blo 1788095 4026581 := bbase (se 7 (by rfl) ⟨47186, by rfl⟩ : syracuseStep 4026581 = 94373) (by norm_num)
theorem B2683109 : Blo 1788095 2683109 := bbase (se 4 (by rfl) ⟨251541, by rfl⟩ : syracuseStep 2683109 = 503083) (by norm_num)
theorem B2265337 : Blo 1788095 2265337 := bbase (se 2 (by rfl) ⟨849501, by rfl⟩ : syracuseStep 2265337 = 1699003) (by norm_num)
theorem B2683133 : Blo 1788095 2683133 := bbase (se 3 (by rfl) ⟨503087, by rfl⟩ : syracuseStep 2683133 = 1006175) (by norm_num)
theorem B8597765 : Blo 1788095 8597765 := bbase (se 4 (by rfl) ⟨806040, by rfl⟩ : syracuseStep 8597765 = 1612081) (by norm_num)
theorem B2683157 : Blo 1788095 2683157 := bbase (se 6 (by rfl) ⟨62886, by rfl⟩ : syracuseStep 2683157 = 125773) (by norm_num)
theorem B4296989 : Blo 1788095 4296989 := bbase (se 3 (by rfl) ⟨805685, by rfl⟩ : syracuseStep 4296989 = 1611371) (by norm_num)
theorem B4026653 : Blo 1788095 4026653 := bbase (se 3 (by rfl) ⟨754997, by rfl⟩ : syracuseStep 4026653 = 1509995) (by norm_num)
theorem B3019045 : Blo 1788095 3019045 := bbase (se 4 (by rfl) ⟨283035, by rfl⟩ : syracuseStep 3019045 = 566071) (by norm_num)
theorem B4526381 : Blo 1788095 4526381 := bbase (se 3 (by rfl) ⟨848696, by rfl⟩ : syracuseStep 4526381 = 1697393) (by norm_num)
theorem B2683181 : Blo 1788095 2683181 := bbase (se 3 (by rfl) ⟨503096, by rfl⟩ : syracuseStep 2683181 = 1006193) (by norm_num)
theorem B13070645 : Blo 1788095 13070645 := bbase (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) (by norm_num)
theorem B2683205 : Blo 1788095 2683205 := bbase (se 4 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 2683205 = 503101) (by norm_num)
theorem B2683229 : Blo 1788095 2683229 := bbase (se 3 (by rfl) ⟨503105, by rfl⟩ : syracuseStep 2683229 = 1006211) (by norm_num)
theorem B7639397 : Blo 1788095 7639397 := bbase (se 4 (by rfl) ⟨716193, by rfl⟩ : syracuseStep 7639397 = 1432387) (by norm_num)
theorem B3223909 : Blo 1788095 3223909 := bbase (se 4 (by rfl) ⟨302241, by rfl⟩ : syracuseStep 3223909 = 604483) (by norm_num)
theorem B4026725 : Blo 1788095 4026725 := bbase (se 4 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 4026725 = 755011) (by norm_num)
theorem B3625325 : Blo 1788095 3625325 := bbase (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) (by norm_num)
theorem B2683253 : Blo 1788095 2683253 := bbase (se 5 (by rfl) ⟨125777, by rfl⟩ : syracuseStep 2683253 = 251555) (by norm_num)
theorem B3019133 : Blo 1788095 3019133 := bbase (se 3 (by rfl) ⟨566087, by rfl⟩ : syracuseStep 3019133 = 1132175) (by norm_num)
theorem B2683277 : Blo 1788095 2683277 := bbase (se 3 (by rfl) ⟨503114, by rfl⟩ : syracuseStep 2683277 = 1006229) (by norm_num)
theorem B2683301 : Blo 1788095 2683301 := bbase (se 4 (by rfl) ⟨251559, by rfl⟩ : syracuseStep 2683301 = 503119) (by norm_num)
theorem B2265509 : Blo 1788095 2265509 := bbase (se 4 (by rfl) ⟨212391, by rfl⟩ : syracuseStep 2265509 = 424783) (by norm_num)
theorem B4026797 : Blo 1788095 4026797 := bbase (se 3 (by rfl) ⟨755024, by rfl⟩ : syracuseStep 4026797 = 1510049) (by norm_num)
theorem B3822005 : Blo 1788095 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B2683325 : Blo 1788095 2683325 := bbase (se 3 (by rfl) ⟨503123, by rfl⟩ : syracuseStep 2683325 = 1006247) (by norm_num)
theorem B2683349 : Blo 1788095 2683349 := bbase (se 7 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 2683349 = 62891) (by norm_num)
theorem B2265565 : Blo 1788095 2265565 := bbase (se 3 (by rfl) ⟨424793, by rfl⟩ : syracuseStep 2265565 = 849587) (by norm_num)
theorem B2011621 : Blo 1788095 2011621 := bbase (se 4 (by rfl) ⟨188589, by rfl⟩ : syracuseStep 2011621 = 377179) (by norm_num)
theorem B3396077 : Blo 1788095 3396077 := bbase (se 3 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 3396077 = 1273529) (by norm_num)
theorem B2683373 : Blo 1788095 2683373 := bbase (se 3 (by rfl) ⟨503132, by rfl⟩ : syracuseStep 2683373 = 1006265) (by norm_num)
theorem B3224053 : Blo 1788095 3224053 := bbase (se 5 (by rfl) ⟨151127, by rfl⟩ : syracuseStep 3224053 = 302255) (by norm_num)
theorem B4026869 : Blo 1788095 4026869 := bbase (se 5 (by rfl) ⟨188759, by rfl⟩ : syracuseStep 4026869 = 377519) (by norm_num)
theorem B3019261 : Blo 1788095 3019261 := bbase (se 3 (by rfl) ⟨566111, by rfl⟩ : syracuseStep 3019261 = 1132223) (by norm_num)
theorem B2683397 : Blo 1788095 2683397 := bbase (se 4 (by rfl) ⟨251568, by rfl⟩ : syracuseStep 2683397 = 503137) (by norm_num)
theorem B2011657 : Blo 1788095 2011657 := bbase (se 2 (by rfl) ⟨754371, by rfl⟩ : syracuseStep 2011657 = 1508743) (by norm_num)
theorem B2683421 : Blo 1788095 2683421 := bbase (se 3 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 2683421 = 1006283) (by norm_num)
theorem B2011693 : Blo 1788095 2011693 := bbase (se 3 (by rfl) ⟨377192, by rfl⟩ : syracuseStep 2011693 = 754385) (by norm_num)
theorem B2683445 : Blo 1788095 2683445 := bbase (se 5 (by rfl) ⟨125786, by rfl⟩ : syracuseStep 2683445 = 251573) (by norm_num)
theorem B4026941 : Blo 1788095 4026941 := bbase (se 3 (by rfl) ⟨755051, by rfl⟩ : syracuseStep 4026941 = 1510103) (by norm_num)
theorem B6795845 : Blo 1788095 6795845 := bbase (se 4 (by rfl) ⟨637110, by rfl⟩ : syracuseStep 6795845 = 1274221) (by norm_num)
theorem B2683469 : Blo 1788095 2683469 := bbase (se 3 (by rfl) ⟨503150, by rfl⟩ : syracuseStep 2683469 = 1006301) (by norm_num)
theorem B2011729 : Blo 1788095 2011729 := bbase (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) (by norm_num)
theorem B3019349 : Blo 1788095 3019349 := bbase (se 8 (by rfl) ⟨17691, by rfl⟩ : syracuseStep 3019349 = 35383) (by norm_num)
theorem B2683493 : Blo 1788095 2683493 := bbase (se 4 (by rfl) ⟨251577, by rfl⟩ : syracuseStep 2683493 = 503155) (by norm_num)
theorem B2011765 : Blo 1788095 2011765 := bbase (se 5 (by rfl) ⟨94301, by rfl⟩ : syracuseStep 2011765 = 188603) (by norm_num)
theorem B13070965 : Blo 1788095 13070965 := bbase (se 5 (by rfl) ⟨612701, by rfl⟩ : syracuseStep 13070965 = 1225403) (by norm_num)
theorem B2683517 : Blo 1788095 2683517 := bbase (se 3 (by rfl) ⟨503159, by rfl⟩ : syracuseStep 2683517 = 1006319) (by norm_num)
theorem B4526725 : Blo 1788095 4526725 := bbase (se 4 (by rfl) ⟨424380, by rfl⟩ : syracuseStep 4526725 = 848761) (by norm_num)
theorem B4027013 : Blo 1788095 4027013 := bbase (se 4 (by rfl) ⟨377532, by rfl⟩ : syracuseStep 4027013 = 755065) (by norm_num)
theorem B2683541 : Blo 1788095 2683541 := bbase (se 6 (by rfl) ⟨62895, by rfl⟩ : syracuseStep 2683541 = 125791) (by norm_num)
theorem B2011801 : Blo 1788095 2011801 := bbase (se 2 (by rfl) ⟨754425, by rfl⟩ : syracuseStep 2011801 = 1508851) (by norm_num)
theorem B9056933 : Blo 1788095 9056933 := bbase (se 4 (by rfl) ⟨849087, by rfl⟩ : syracuseStep 9056933 = 1698175) (by norm_num)
theorem B2683565 : Blo 1788095 2683565 := bbase (se 3 (by rfl) ⟨503168, by rfl⟩ : syracuseStep 2683565 = 1006337) (by norm_num)
theorem B4838069 : Blo 1788095 4838069 := bbase (se 5 (by rfl) ⟨226784, by rfl⟩ : syracuseStep 4838069 = 453569) (by norm_num)
theorem B2011837 : Blo 1788095 2011837 := bbase (se 3 (by rfl) ⟨377219, by rfl⟩ : syracuseStep 2011837 = 754439) (by norm_num)
theorem B2683589 : Blo 1788095 2683589 := bbase (se 4 (by rfl) ⟨251586, by rfl⟩ : syracuseStep 2683589 = 503173) (by norm_num)
theorem B4297421 : Blo 1788095 4297421 := bbase (se 3 (by rfl) ⟨805766, by rfl⟩ : syracuseStep 4297421 = 1611533) (by norm_num)
theorem B4027085 : Blo 1788095 4027085 := bbase (se 3 (by rfl) ⟨755078, by rfl⟩ : syracuseStep 4027085 = 1510157) (by norm_num)
theorem B3019477 : Blo 1788095 3019477 := bbase (se 7 (by rfl) ⟨35384, by rfl⟩ : syracuseStep 3019477 = 70769) (by norm_num)
theorem B2683613 : Blo 1788095 2683613 := bbase (se 3 (by rfl) ⟨503177, by rfl⟩ : syracuseStep 2683613 = 1006355) (by norm_num)
theorem B2011873 : Blo 1788095 2011873 := bbase (se 2 (by rfl) ⟨754452, by rfl⟩ : syracuseStep 2011873 = 1508905) (by norm_num)
theorem B4526837 : Blo 1788095 4526837 := bbase (se 5 (by rfl) ⟨212195, by rfl⟩ : syracuseStep 4526837 = 424391) (by norm_num)
theorem B2683637 : Blo 1788095 2683637 := bbase (se 5 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 2683637 = 251591) (by norm_num)
theorem B2011909 : Blo 1788095 2011909 := bbase (se 4 (by rfl) ⟨188616, by rfl⟩ : syracuseStep 2011909 = 377233) (by norm_num)
theorem B2683661 : Blo 1788095 2683661 := bbase (se 3 (by rfl) ⟨503186, by rfl⟩ : syracuseStep 2683661 = 1006373) (by norm_num)
theorem B4027157 : Blo 1788095 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B2683685 : Blo 1788095 2683685 := bbase (se 4 (by rfl) ⟨251595, by rfl⟩ : syracuseStep 2683685 = 503191) (by norm_num)
theorem B2011945 : Blo 1788095 2011945 := bbase (se 2 (by rfl) ⟨754479, by rfl⟩ : syracuseStep 2011945 = 1508959) (by norm_num)
theorem B3019565 : Blo 1788095 3019565 := bbase (se 3 (by rfl) ⟨566168, by rfl⟩ : syracuseStep 3019565 = 1132337) (by norm_num)
theorem B2683709 : Blo 1788095 2683709 := bbase (se 3 (by rfl) ⟨503195, by rfl⟩ : syracuseStep 2683709 = 1006391) (by norm_num)
theorem B2011981 : Blo 1788095 2011981 := bbase (se 3 (by rfl) ⟨377246, by rfl⟩ : syracuseStep 2011981 = 754493) (by norm_num)
theorem B1962829 : Blo 1788095 1962829 := bbase (se 3 (by rfl) ⟨368030, by rfl⟩ : syracuseStep 1962829 = 736061) (by norm_num)
theorem B2683733 : Blo 1788095 2683733 := bbase (se 9 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 2683733 = 15725) (by norm_num)
theorem B4027229 : Blo 1788095 4027229 := bbase (se 3 (by rfl) ⟨755105, by rfl⟩ : syracuseStep 4027229 = 1510211) (by norm_num)
theorem B6796133 : Blo 1788095 6796133 := bbase (se 4 (by rfl) ⟨637137, by rfl⟩ : syracuseStep 6796133 = 1274275) (by norm_num)
theorem B2683757 : Blo 1788095 2683757 := bbase (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) (by norm_num)
theorem B2012017 : Blo 1788095 2012017 := bbase (se 2 (by rfl) ⟨754506, by rfl⟩ : syracuseStep 2012017 = 1509013) (by norm_num)
theorem B2683781 : Blo 1788095 2683781 := bbase (se 4 (by rfl) ⟨251604, by rfl⟩ : syracuseStep 2683781 = 503209) (by norm_num)
theorem B2012053 : Blo 1788095 2012053 := bbase (se 6 (by rfl) ⟨47157, by rfl⟩ : syracuseStep 2012053 = 94315) (by norm_num)
theorem B2683805 : Blo 1788095 2683805 := bbase (se 3 (by rfl) ⟨503213, by rfl⟩ : syracuseStep 2683805 = 1006427) (by norm_num)
theorem B4027301 : Blo 1788095 4027301 := bbase (se 4 (by rfl) ⟨377559, by rfl⟩ : syracuseStep 4027301 = 755119) (by norm_num)
theorem B3019693 : Blo 1788095 3019693 := bbase (se 3 (by rfl) ⟨566192, by rfl⟩ : syracuseStep 3019693 = 1132385) (by norm_num)
theorem B4527029 : Blo 1788095 4527029 := bbase (se 5 (by rfl) ⟨212204, by rfl⟩ : syracuseStep 4527029 = 424409) (by norm_num)
theorem B2683829 : Blo 1788095 2683829 := bbase (se 5 (by rfl) ⟨125804, by rfl⟩ : syracuseStep 2683829 = 251609) (by norm_num)
theorem B2012089 : Blo 1788095 2012089 := bbase (se 2 (by rfl) ⟨754533, by rfl⟩ : syracuseStep 2012089 = 1509067) (by norm_num)
theorem B2683853 : Blo 1788095 2683853 := bbase (se 3 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 2683853 = 1006445) (by norm_num)
theorem B2012125 : Blo 1788095 2012125 := bbase (se 3 (by rfl) ⟨377273, by rfl⟩ : syracuseStep 2012125 = 754547) (by norm_num)
theorem B2683877 : Blo 1788095 2683877 := bbase (se 4 (by rfl) ⟨251613, by rfl⟩ : syracuseStep 2683877 = 503227) (by norm_num)
theorem B4027373 : Blo 1788095 4027373 := bbase (se 3 (by rfl) ⟨755132, by rfl⟩ : syracuseStep 4027373 = 1510265) (by norm_num)
theorem B1963001 : Blo 1788095 1963001 := bbase (se 2 (by rfl) ⟨736125, by rfl⟩ : syracuseStep 1963001 = 1472251) (by norm_num)
theorem B2683901 : Blo 1788095 2683901 := bbase (se 3 (by rfl) ⟨503231, by rfl⟩ : syracuseStep 2683901 = 1006463) (by norm_num)
theorem B2012161 : Blo 1788095 2012161 := bbase (se 2 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 2012161 = 1509121) (by norm_num)
theorem B3019781 : Blo 1788095 3019781 := bbase (se 4 (by rfl) ⟨283104, by rfl⟩ : syracuseStep 3019781 = 566209) (by norm_num)
theorem B11457557 : Blo 1788095 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B2683925 : Blo 1788095 2683925 := bbase (se 6 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 2683925 = 125809) (by norm_num)
theorem B2012197 : Blo 1788095 2012197 := bbase (se 4 (by rfl) ⟨188643, by rfl⟩ : syracuseStep 2012197 = 377287) (by norm_num)
theorem B2683949 : Blo 1788095 2683949 := bbase (se 3 (by rfl) ⟨503240, by rfl⟩ : syracuseStep 2683949 = 1006481) (by norm_num)
theorem B3224629 : Blo 1788095 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B4027445 : Blo 1788095 4027445 := bbase (se 5 (by rfl) ⟨188786, by rfl⟩ : syracuseStep 4027445 = 377573) (by norm_num)
theorem B2683973 : Blo 1788095 2683973 := bbase (se 4 (by rfl) ⟨251622, by rfl⟩ : syracuseStep 2683973 = 503245) (by norm_num)
theorem B2012233 : Blo 1788095 2012233 := bbase (se 2 (by rfl) ⟨754587, by rfl⟩ : syracuseStep 2012233 = 1509175) (by norm_num)
theorem B2683997 : Blo 1788095 2683997 := bbase (se 3 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 2683997 = 1006499) (by norm_num)
theorem B2012269 : Blo 1788095 2012269 := bbase (se 3 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 2012269 = 754601) (by norm_num)
theorem B2684021 : Blo 1788095 2684021 := bbase (se 5 (by rfl) ⟨125813, by rfl⟩ : syracuseStep 2684021 = 251627) (by norm_num)
theorem B4027517 : Blo 1788095 4027517 := bbase (se 3 (by rfl) ⟨755159, by rfl⟩ : syracuseStep 4027517 = 1510319) (by norm_num)
theorem B3019909 : Blo 1788095 3019909 := bbase (se 4 (by rfl) ⟨283116, by rfl⟩ : syracuseStep 3019909 = 566233) (by norm_num)
theorem B2684045 : Blo 1788095 2684045 := bbase (se 3 (by rfl) ⟨503258, by rfl⟩ : syracuseStep 2684045 = 1006517) (by norm_num)
theorem B2012305 : Blo 1788095 2012305 := bbase (se 2 (by rfl) ⟨754614, by rfl⟩ : syracuseStep 2012305 = 1509229) (by norm_num)
theorem B2684069 : Blo 1788095 2684069 := bbase (se 4 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 2684069 = 503263) (by norm_num)
theorem B2012341 : Blo 1788095 2012341 := bbase (se 5 (by rfl) ⟨94328, by rfl⟩ : syracuseStep 2012341 = 188657) (by norm_num)
theorem B10187957 : Blo 1788095 10187957 := bbase (se 5 (by rfl) ⟨477560, by rfl⟩ : syracuseStep 10187957 = 955121) (by norm_num)
theorem B4592821 : Blo 1788095 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B2684093 : Blo 1788095 2684093 := bbase (se 3 (by rfl) ⟨503267, by rfl⟩ : syracuseStep 2684093 = 1006535) (by norm_num)
theorem B4027589 : Blo 1788095 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B2684117 : Blo 1788095 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B2012377 : Blo 1788095 2012377 := bbase (se 2 (by rfl) ⟨754641, by rfl⟩ : syracuseStep 2012377 = 1509283) (by norm_num)
theorem B3396829 : Blo 1788095 3396829 := bbase (se 3 (by rfl) ⟨636905, by rfl⟩ : syracuseStep 3396829 = 1273811) (by norm_num)
theorem B3019997 : Blo 1788095 3019997 := bbase (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) (by norm_num)
theorem B2684141 : Blo 1788095 2684141 := bbase (se 3 (by rfl) ⟨503276, by rfl⟩ : syracuseStep 2684141 = 1006553) (by norm_num)
theorem B5731573 : Blo 1788095 5731573 := bbase (se 5 (by rfl) ⟨268667, by rfl⟩ : syracuseStep 5731573 = 537335) (by norm_num)
theorem B2012413 : Blo 1788095 2012413 := bbase (se 3 (by rfl) ⟨377327, by rfl⟩ : syracuseStep 2012413 = 754655) (by norm_num)
theorem B2684165 : Blo 1788095 2684165 := bbase (se 4 (by rfl) ⟨251640, by rfl⟩ : syracuseStep 2684165 = 503281) (by norm_num)
theorem B4527373 : Blo 1788095 4527373 := bbase (se 3 (by rfl) ⟨848882, by rfl⟩ : syracuseStep 4527373 = 1697765) (by norm_num)
theorem B4027661 : Blo 1788095 4027661 := bbase (se 3 (by rfl) ⟨755186, by rfl⟩ : syracuseStep 4027661 = 1510373) (by norm_num)
theorem B3822869 : Blo 1788095 3822869 := bbase (se 6 (by rfl) ⟨89598, by rfl⟩ : syracuseStep 3822869 = 179197) (by norm_num)
theorem B2684189 : Blo 1788095 2684189 := bbase (se 3 (by rfl) ⟨503285, by rfl⟩ : syracuseStep 2684189 = 1006571) (by norm_num)
theorem B2012449 : Blo 1788095 2012449 := bbase (se 2 (by rfl) ⟨754668, by rfl⟩ : syracuseStep 2012449 = 1509337) (by norm_num)
theorem B2684213 : Blo 1788095 2684213 := bbase (se 5 (by rfl) ⟨125822, by rfl⟩ : syracuseStep 2684213 = 251645) (by norm_num)
theorem B2012485 : Blo 1788095 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B2684237 : Blo 1788095 2684237 := bbase (se 3 (by rfl) ⟨503294, by rfl⟩ : syracuseStep 2684237 = 1006589) (by norm_num)
theorem B3020125 : Blo 1788095 3020125 := bbase (se 3 (by rfl) ⟨566273, by rfl⟩ : syracuseStep 3020125 = 1132547) (by norm_num)
theorem B2684261 : Blo 1788095 2684261 := bbase (se 4 (by rfl) ⟨251649, by rfl⟩ : syracuseStep 2684261 = 503299) (by norm_num)
theorem B2012521 : Blo 1788095 2012521 := bbase (se 2 (by rfl) ⟨754695, by rfl⟩ : syracuseStep 2012521 = 1509391) (by norm_num)
theorem B3396973 : Blo 1788095 3396973 := bbase (se 3 (by rfl) ⟨636932, by rfl⟩ : syracuseStep 3396973 = 1273865) (by norm_num)
theorem B4527485 : Blo 1788095 4527485 := bbase (se 3 (by rfl) ⟨848903, by rfl⟩ : syracuseStep 4527485 = 1697807) (by norm_num)
theorem B2684285 : Blo 1788095 2684285 := bbase (se 3 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 2684285 = 1006607) (by norm_num)
theorem B2012557 : Blo 1788095 2012557 := bbase (se 3 (by rfl) ⟨377354, by rfl⟩ : syracuseStep 2012557 = 754709) (by norm_num)
theorem B2684309 : Blo 1788095 2684309 := bbase (se 6 (by rfl) ⟨62913, by rfl⟩ : syracuseStep 2684309 = 125827) (by norm_num)
theorem B3823013 : Blo 1788095 3823013 := bbase (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) (by norm_num)
theorem B2684333 : Blo 1788095 2684333 := bbase (se 3 (by rfl) ⟨503312, by rfl⟩ : syracuseStep 2684333 = 1006625) (by norm_num)
theorem B2012593 : Blo 1788095 2012593 := bbase (se 2 (by rfl) ⟨754722, by rfl⟩ : syracuseStep 2012593 = 1509445) (by norm_num)
theorem B3020213 : Blo 1788095 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B2684357 : Blo 1788095 2684357 := bbase (se 4 (by rfl) ⟨251658, by rfl⟩ : syracuseStep 2684357 = 503317) (by norm_num)
theorem B2012629 : Blo 1788095 2012629 := bbase (se 7 (by rfl) ⟨23585, by rfl⟩ : syracuseStep 2012629 = 47171) (by norm_num)
theorem B2684381 : Blo 1788095 2684381 := bbase (se 3 (by rfl) ⟨503321, by rfl⟩ : syracuseStep 2684381 = 1006643) (by norm_num)
theorem B2864621 : Blo 1788095 2864621 := bbase (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) (by norm_num)
theorem B2684405 : Blo 1788095 2684405 := bbase (se 5 (by rfl) ⟨125831, by rfl⟩ : syracuseStep 2684405 = 251663) (by norm_num)
theorem B2012665 : Blo 1788095 2012665 := bbase (se 2 (by rfl) ⟨754749, by rfl⟩ : syracuseStep 2012665 = 1509499) (by norm_num)
theorem B3397133 : Blo 1788095 3397133 := bbase (se 3 (by rfl) ⟨636962, by rfl⟩ : syracuseStep 3397133 = 1273925) (by norm_num)
theorem B2684429 : Blo 1788095 2684429 := bbase (se 3 (by rfl) ⟨503330, by rfl⟩ : syracuseStep 2684429 = 1006661) (by norm_num)
theorem B5092885 : Blo 1788095 5092885 := bbase (se 6 (by rfl) ⟨119364, by rfl⟩ : syracuseStep 5092885 = 238729) (by norm_num)
theorem B2012701 : Blo 1788095 2012701 := bbase (se 3 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 2012701 = 754763) (by norm_num)
theorem B2684453 : Blo 1788095 2684453 := bbase (se 4 (by rfl) ⟨251667, by rfl⟩ : syracuseStep 2684453 = 503335) (by norm_num)
theorem B3020341 : Blo 1788095 3020341 := bbase (se 5 (by rfl) ⟨141578, by rfl⟩ : syracuseStep 3020341 = 283157) (by norm_num)
theorem B4527677 : Blo 1788095 4527677 := bbase (se 3 (by rfl) ⟨848939, by rfl⟩ : syracuseStep 4527677 = 1697879) (by norm_num)
theorem B2684477 : Blo 1788095 2684477 := bbase (se 3 (by rfl) ⟨503339, by rfl⟩ : syracuseStep 2684477 = 1006679) (by norm_num)
theorem B2012737 : Blo 1788095 2012737 := bbase (se 2 (by rfl) ⟨754776, by rfl⟩ : syracuseStep 2012737 = 1509553) (by norm_num)
theorem B2684501 : Blo 1788095 2684501 := bbase (se 8 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 2684501 = 31459) (by norm_num)
theorem B2012773 : Blo 1788095 2012773 := bbase (se 4 (by rfl) ⟨188697, by rfl⟩ : syracuseStep 2012773 = 377395) (by norm_num)
theorem B2684525 : Blo 1788095 2684525 := bbase (se 3 (by rfl) ⟨503348, by rfl⟩ : syracuseStep 2684525 = 1006697) (by norm_num)
theorem B3061373 : Blo 1788095 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B2684549 : Blo 1788095 2684549 := bbase (se 4 (by rfl) ⟨251676, by rfl⟩ : syracuseStep 2684549 = 503353) (by norm_num)
theorem B2012809 : Blo 1788095 2012809 := bbase (se 2 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 2012809 = 1509607) (by norm_num)
theorem B3020429 : Blo 1788095 3020429 := bbase (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) (by norm_num)
theorem B6035093 : Blo 1788095 6035093 := bbase (se 6 (by rfl) ⟨141447, by rfl⟩ : syracuseStep 6035093 = 282895) (by norm_num)
theorem B3397277 : Blo 1788095 3397277 := bbase (se 3 (by rfl) ⟨636989, by rfl⟩ : syracuseStep 3397277 = 1273979) (by norm_num)
theorem B2684573 : Blo 1788095 2684573 := bbase (se 3 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 2684573 = 1006715) (by norm_num)
theorem B2012845 : Blo 1788095 2012845 := bbase (se 3 (by rfl) ⟨377408, by rfl⟩ : syracuseStep 2012845 = 754817) (by norm_num)
theorem B2684597 : Blo 1788095 2684597 := bbase (se 5 (by rfl) ⟨125840, by rfl⟩ : syracuseStep 2684597 = 251681) (by norm_num)
theorem B2864845 : Blo 1788095 2864845 := bbase (se 3 (by rfl) ⟨537158, by rfl⟩ : syracuseStep 2864845 = 1074317) (by norm_num)
theorem B2684621 : Blo 1788095 2684621 := bbase (se 3 (by rfl) ⟨503366, by rfl⟩ : syracuseStep 2684621 = 1006733) (by norm_num)
theorem B2012881 : Blo 1788095 2012881 := bbase (se 2 (by rfl) ⟨754830, by rfl⟩ : syracuseStep 2012881 = 1509661) (by norm_num)
theorem B2684645 : Blo 1788095 2684645 := bbase (se 4 (by rfl) ⟨251685, by rfl⟩ : syracuseStep 2684645 = 503371) (by norm_num)
theorem B2012917 : Blo 1788095 2012917 := bbase (se 5 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 2012917 = 188711) (by norm_num)
theorem B2684669 : Blo 1788095 2684669 := bbase (se 3 (by rfl) ⟨503375, by rfl⟩ : syracuseStep 2684669 = 1006751) (by norm_num)
theorem B3020557 : Blo 1788095 3020557 := bbase (se 3 (by rfl) ⟨566354, by rfl⟩ : syracuseStep 3020557 = 1132709) (by norm_num)
theorem B2684693 : Blo 1788095 2684693 := bbase (se 6 (by rfl) ⟨62922, by rfl⟩ : syracuseStep 2684693 = 125845) (by norm_num)
theorem B2012953 : Blo 1788095 2012953 := bbase (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) (by norm_num)
theorem B2684717 : Blo 1788095 2684717 := bbase (se 3 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 2684717 = 1006769) (by norm_num)
theorem B2012989 : Blo 1788095 2012989 := bbase (se 3 (by rfl) ⟨377435, by rfl⟩ : syracuseStep 2012989 = 754871) (by norm_num)
theorem B2684741 : Blo 1788095 2684741 := bbase (se 4 (by rfl) ⟨251694, by rfl⟩ : syracuseStep 2684741 = 503389) (by norm_num)
theorem B2684765 : Blo 1788095 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B3225437 : Blo 1788095 3225437 := bbase (se 3 (by rfl) ⟨604769, by rfl⟩ : syracuseStep 3225437 = 1209539) (by norm_num)
theorem B2013025 : Blo 1788095 2013025 := bbase (se 2 (by rfl) ⟨754884, by rfl⟩ : syracuseStep 2013025 = 1509769) (by norm_num)
theorem B3020645 : Blo 1788095 3020645 := bbase (se 4 (by rfl) ⟨283185, by rfl⟩ : syracuseStep 3020645 = 566371) (by norm_num)
theorem B2684789 : Blo 1788095 2684789 := bbase (se 5 (by rfl) ⟨125849, by rfl⟩ : syracuseStep 2684789 = 251699) (by norm_num)
theorem B2013061 : Blo 1788095 2013061 := bbase (se 4 (by rfl) ⟨188724, by rfl⟩ : syracuseStep 2013061 = 377449) (by norm_num)
theorem B2684813 : Blo 1788095 2684813 := bbase (se 3 (by rfl) ⟨503402, by rfl⟩ : syracuseStep 2684813 = 1006805) (by norm_num)
theorem B4528021 : Blo 1788095 4528021 := bbase (se 6 (by rfl) ⟨106125, by rfl⟩ : syracuseStep 4528021 = 212251) (by norm_num)
theorem B2684837 : Blo 1788095 2684837 := bbase (se 4 (by rfl) ⟨251703, by rfl⟩ : syracuseStep 2684837 = 503407) (by norm_num)
theorem B2013097 : Blo 1788095 2013097 := bbase (se 2 (by rfl) ⟨754911, by rfl⟩ : syracuseStep 2013097 = 1509823) (by norm_num)
theorem B9058229 : Blo 1788095 9058229 := bbase (se 5 (by rfl) ⟨424604, by rfl⟩ : syracuseStep 9058229 = 849209) (by norm_num)
theorem B3397565 : Blo 1788095 3397565 := bbase (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) (by norm_num)
theorem B2684861 : Blo 1788095 2684861 := bbase (se 3 (by rfl) ⟨503411, by rfl⟩ : syracuseStep 2684861 = 1006823) (by norm_num)
theorem B2013133 : Blo 1788095 2013133 := bbase (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) (by norm_num)
theorem B2684885 : Blo 1788095 2684885 := bbase (se 7 (by rfl) ⟨31463, by rfl⟩ : syracuseStep 2684885 = 62927) (by norm_num)
theorem B3020773 : Blo 1788095 3020773 := bbase (se 4 (by rfl) ⟨283197, by rfl⟩ : syracuseStep 3020773 = 566395) (by norm_num)
theorem B2684909 : Blo 1788095 2684909 := bbase (se 3 (by rfl) ⟨503420, by rfl⟩ : syracuseStep 2684909 = 1006841) (by norm_num)
theorem B2013169 : Blo 1788095 2013169 := bbase (se 2 (by rfl) ⟨754938, by rfl⟩ : syracuseStep 2013169 = 1509877) (by norm_num)
theorem B4249597 : Blo 1788095 4249597 := bbase (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) (by norm_num)
theorem B4528133 : Blo 1788095 4528133 := bbase (se 4 (by rfl) ⟨424512, by rfl⟩ : syracuseStep 4528133 = 849025) (by norm_num)
theorem B2684933 : Blo 1788095 2684933 := bbase (se 4 (by rfl) ⟨251712, by rfl⟩ : syracuseStep 2684933 = 503425) (by norm_num)
theorem B2013205 : Blo 1788095 2013205 := bbase (se 6 (by rfl) ⟨47184, by rfl⟩ : syracuseStep 2013205 = 94369) (by norm_num)
theorem B2684957 : Blo 1788095 2684957 := bbase (se 3 (by rfl) ⟨503429, by rfl⟩ : syracuseStep 2684957 = 1006859) (by norm_num)
theorem B7256101 : Blo 1788095 7256101 := bbase (se 4 (by rfl) ⟨680259, by rfl⟩ : syracuseStep 7256101 = 1360519) (by norm_num)
theorem B2684981 : Blo 1788095 2684981 := bbase (se 5 (by rfl) ⟨125858, by rfl⟩ : syracuseStep 2684981 = 251717) (by norm_num)
theorem B2013241 : Blo 1788095 2013241 := bbase (se 2 (by rfl) ⟨754965, by rfl⟩ : syracuseStep 2013241 = 1509931) (by norm_num)
theorem B6035525 : Blo 1788095 6035525 := bbase (se 4 (by rfl) ⟨565830, by rfl⟩ : syracuseStep 6035525 = 1131661) (by norm_num)
theorem B2685005 : Blo 1788095 2685005 := bbase (se 3 (by rfl) ⟨503438, by rfl⟩ : syracuseStep 2685005 = 1006877) (by norm_num)
theorem B3397717 : Blo 1788095 3397717 := bbase (se 8 (by rfl) ⟨19908, by rfl⟩ : syracuseStep 3397717 = 39817) (by norm_num)
theorem B2013277 : Blo 1788095 2013277 := bbase (se 3 (by rfl) ⟨377489, by rfl⟩ : syracuseStep 2013277 = 754979) (by norm_num)
theorem B2685029 : Blo 1788095 2685029 := bbase (se 4 (by rfl) ⟨251721, by rfl⟩ : syracuseStep 2685029 = 503443) (by norm_num)
theorem B2685053 : Blo 1788095 2685053 := bbase (se 3 (by rfl) ⟨503447, by rfl⟩ : syracuseStep 2685053 = 1006895) (by norm_num)
theorem B2013313 : Blo 1788095 2013313 := bbase (se 2 (by rfl) ⟨754992, by rfl⟩ : syracuseStep 2013313 = 1509985) (by norm_num)
theorem B19347605 : Blo 1788095 19347605 := bbase (se 6 (by rfl) ⟨453459, by rfl⟩ : syracuseStep 19347605 = 906919) (by norm_num)
theorem B15497365 : Blo 1788095 15497365 := bbase (se 6 (by rfl) ⟨363219, by rfl⟩ : syracuseStep 15497365 = 726439) (by norm_num)
theorem B2685077 : Blo 1788095 2685077 := bbase (se 6 (by rfl) ⟨62931, by rfl⟩ : syracuseStep 2685077 = 125863) (by norm_num)
theorem B2013349 : Blo 1788095 2013349 := bbase (se 4 (by rfl) ⟨188751, by rfl⟩ : syracuseStep 2013349 = 377503) (by norm_num)
theorem B2685101 : Blo 1788095 2685101 := bbase (se 3 (by rfl) ⟨503456, by rfl⟩ : syracuseStep 2685101 = 1006913) (by norm_num)
theorem B15292597 : Blo 1788095 15292597 := bbase (se 5 (by rfl) ⟨716840, by rfl⟩ : syracuseStep 15292597 = 1433681) (by norm_num)
theorem B4528325 : Blo 1788095 4528325 := bbase (se 4 (by rfl) ⟨424530, by rfl⟩ : syracuseStep 4528325 = 849061) (by norm_num)
theorem B7256261 : Blo 1788095 7256261 := bbase (se 4 (by rfl) ⟨680274, by rfl⟩ : syracuseStep 7256261 = 1360549) (by norm_num)
theorem B2685125 : Blo 1788095 2685125 := bbase (se 4 (by rfl) ⟨251730, by rfl⟩ : syracuseStep 2685125 = 503461) (by norm_num)
theorem B2013385 : Blo 1788095 2013385 := bbase (se 2 (by rfl) ⟨755019, by rfl⟩ : syracuseStep 2013385 = 1510039) (by norm_num)
theorem B2013421 : Blo 1788095 2013421 := bbase (se 3 (by rfl) ⟨377516, by rfl⟩ : syracuseStep 2013421 = 755033) (by norm_num)
theorem B2013457 : Blo 1788095 2013457 := bbase (se 2 (by rfl) ⟨755046, by rfl⟩ : syracuseStep 2013457 = 1510093) (by norm_num)
theorem B2013493 : Blo 1788095 2013493 := bbase (se 5 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 2013493 = 188765) (by norm_num)
theorem B2013529 : Blo 1788095 2013529 := bbase (se 2 (by rfl) ⟨755073, by rfl⟩ : syracuseStep 2013529 = 1510147) (by norm_num)
theorem B3103085 : Blo 1788095 3103085 := bbase (se 3 (by rfl) ⟨581828, by rfl⟩ : syracuseStep 3103085 = 1163657) (by norm_num)
theorem B2013565 : Blo 1788095 2013565 := bbase (se 3 (by rfl) ⟨377543, by rfl⟩ : syracuseStep 2013565 = 755087) (by norm_num)
theorem B3398021 : Blo 1788095 3398021 := bbase (se 4 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 3398021 = 637129) (by norm_num)
theorem B15276437 : Blo 1788095 15276437 := bbase (se 6 (by rfl) ⟨358041, by rfl⟩ : syracuseStep 15276437 = 716083) (by norm_num)
theorem B2013601 : Blo 1788095 2013601 := bbase (se 2 (by rfl) ⟨755100, by rfl⟩ : syracuseStep 2013601 = 1510201) (by norm_num)
theorem B6789541 : Blo 1788095 6789541 := bbase (se 4 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 6789541 = 1273039) (by norm_num)
theorem B2546101 : Blo 1788095 2546101 := bbase (se 5 (by rfl) ⟨119348, by rfl⟩ : syracuseStep 2546101 = 238697) (by norm_num)
theorem B2013637 : Blo 1788095 2013637 := bbase (se 4 (by rfl) ⟨188778, by rfl⟩ : syracuseStep 2013637 = 377557) (by norm_num)
theorem B4135373 : Blo 1788095 4135373 := bbase (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) (by norm_num)
theorem B2013673 : Blo 1788095 2013673 := bbase (se 2 (by rfl) ⟨755127, by rfl⟩ : syracuseStep 2013673 = 1510255) (by norm_num)
theorem B6035957 : Blo 1788095 6035957 := bbase (se 5 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 6035957 = 565871) (by norm_num)
theorem B2013709 : Blo 1788095 2013709 := bbase (se 3 (by rfl) ⟨377570, by rfl⟩ : syracuseStep 2013709 = 755141) (by norm_num)
theorem B4528669 : Blo 1788095 4528669 := bbase (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) (by norm_num)
theorem B4192813 : Blo 1788095 4192813 := bbase (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) (by norm_num)
theorem B2013745 : Blo 1788095 2013745 := bbase (se 2 (by rfl) ⟨755154, by rfl⟩ : syracuseStep 2013745 = 1510309) (by norm_num)
theorem B13589045 : Blo 1788095 13589045 := bbase (se 5 (by rfl) ⟨636986, by rfl⟩ : syracuseStep 13589045 = 1273973) (by norm_num)
theorem B2013781 : Blo 1788095 2013781 := bbase (se 8 (by rfl) ⟨11799, by rfl⟩ : syracuseStep 2013781 = 23599) (by norm_num)
theorem B8600165 : Blo 1788095 8600165 := bbase (se 4 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 8600165 = 1612531) (by norm_num)
theorem B2013817 : Blo 1788095 2013817 := bbase (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) (by norm_num)
theorem B4528781 : Blo 1788095 4528781 := bbase (se 3 (by rfl) ⟨849146, by rfl⟩ : syracuseStep 4528781 = 1698293) (by norm_num)
theorem B6118037 : Blo 1788095 6118037 := bbase (se 6 (by rfl) ⟨143391, by rfl⟩ : syracuseStep 6118037 = 286783) (by norm_num)
theorem B2013853 : Blo 1788095 2013853 := bbase (se 3 (by rfl) ⟨377597, by rfl⟩ : syracuseStep 2013853 = 755195) (by norm_num)
theorem B6789845 : Blo 1788095 6789845 := bbase (se 7 (by rfl) ⟨79568, by rfl⟩ : syracuseStep 6789845 = 159137) (by norm_num)
theorem B4528973 : Blo 1788095 4528973 := bbase (se 3 (by rfl) ⟨849182, by rfl⟩ : syracuseStep 4528973 = 1698365) (by norm_num)
theorem B9804629 : Blo 1788095 9804629 := bbase (se 9 (by rfl) ⟨28724, by rfl⟩ : syracuseStep 9804629 = 57449) (by norm_num)
theorem B6445973 : Blo 1788095 6445973 := bbase (se 6 (by rfl) ⟨151077, by rfl⟩ : syracuseStep 6445973 = 302155) (by norm_num)
theorem B6036389 : Blo 1788095 6036389 := bbase (se 4 (by rfl) ⟨565911, by rfl⟩ : syracuseStep 6036389 = 1131823) (by norm_num)
theorem B13581269 : Blo 1788095 13581269 := bbase (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) (by norm_num)
theorem B5094389 : Blo 1788095 5094389 := bbase (se 5 (by rfl) ⟨238799, by rfl⟩ : syracuseStep 5094389 = 477599) (by norm_num)
theorem B2866261 : Blo 1788095 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B3267749 : Blo 1788095 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B4529317 : Blo 1788095 4529317 := bbase (se 4 (by rfl) ⟨424623, by rfl⟩ : syracuseStep 4529317 = 849247) (by norm_num)
theorem B4357309 : Blo 1788095 4357309 := bbase (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) (by norm_num)
theorem B9059525 : Blo 1788095 9059525 := bbase (se 4 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 9059525 = 1698661) (by norm_num)
theorem B2546893 : Blo 1788095 2546893 := bbase (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) (by norm_num)
theorem B4529429 : Blo 1788095 4529429 := bbase (se 6 (by rfl) ⟨106158, by rfl⟩ : syracuseStep 4529429 = 212317) (by norm_num)
theorem B6446405 : Blo 1788095 6446405 := bbase (se 4 (by rfl) ⟨604350, by rfl⟩ : syracuseStep 6446405 = 1208701) (by norm_num)
theorem B1989965 : Blo 1788095 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B6036821 : Blo 1788095 6036821 := bbase (se 11 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 6036821 = 8843) (by norm_num)
theorem B2866517 : Blo 1788095 2866517 := bbase (se 11 (by rfl) ⟨2099, by rfl⟩ : syracuseStep 2866517 = 4199) (by norm_num)
theorem B4529621 : Blo 1788095 4529621 := bbase (se 7 (by rfl) ⟨53081, by rfl⟩ : syracuseStep 4529621 = 106163) (by norm_num)
theorem B2866709 : Blo 1788095 2866709 := bbase (se 6 (by rfl) ⟨67188, by rfl⟩ : syracuseStep 2866709 = 134377) (by norm_num)
theorem B2547229 : Blo 1788095 2547229 := bbase (se 3 (by rfl) ⟨477605, by rfl⟩ : syracuseStep 2547229 = 955211) (by norm_num)
theorem B22920853 : Blo 1788095 22920853 := bbase (se 6 (by rfl) ⟨537207, by rfl⟩ : syracuseStep 22920853 = 1074415) (by norm_num)
theorem B2719469 : Blo 1788095 2719469 := bbase (se 3 (by rfl) ⟨509900, by rfl⟩ : syracuseStep 2719469 = 1019801) (by norm_num)
theorem B2547445 : Blo 1788095 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B6037253 : Blo 1788095 6037253 := bbase (se 4 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 6037253 = 1131985) (by norm_num)
theorem B4529965 : Blo 1788095 4529965 := bbase (se 3 (by rfl) ⟨849368, by rfl⟩ : syracuseStep 4529965 = 1698737) (by norm_num)
theorem B4079413 : Blo 1788095 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B4079485 : Blo 1788095 4079485 := bbase (se 3 (by rfl) ⟨764903, by rfl⟩ : syracuseStep 4079485 = 1529807) (by norm_num)
theorem B4530077 : Blo 1788095 4530077 := bbase (se 3 (by rfl) ⟨849389, by rfl⟩ : syracuseStep 4530077 = 1698779) (by norm_num)
theorem B6119381 : Blo 1788095 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B2547713 : Blo 1788095 2547713 := bstep (se 2 (by rfl) ⟨955392, by rfl⟩ : syracuseStep 2547713 = 1910785) B1910785
theorem B5734417 : Blo 1788095 5734417 := bstep (se 2 (by rfl) ⟨2150406, by rfl⟩ : syracuseStep 5734417 = 4300813) B4300813
theorem B9674801 : Blo 1788095 9674801 := bstep (se 2 (by rfl) ⟨3628050, by rfl⟩ : syracuseStep 9674801 = 7256101) B7256101
theorem B4530289 : Blo 1788095 4530289 := bstep (se 2 (by rfl) ⟨1698858, by rfl⟩ : syracuseStep 4530289 = 3397717) B3397717
theorem B41296013 : Blo 1788095 41296013 := bstep (se 3 (by rfl) ⟨7743002, by rfl⟩ : syracuseStep 41296013 = 15486005) B15486005
theorem B5095619 : Blo 1788095 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B4833485 : Blo 1788095 4833485 := bstep (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) B1812557
theorem B8593613 : Blo 1788095 8593613 := bstep (se 3 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 8593613 = 3222605) B3222605
theorem B20390129 : Blo 1788095 20390129 := bstep (se 2 (by rfl) ⟨7646298, by rfl⟩ : syracuseStep 20390129 = 15292597) B15292597
theorem B2416883 : Blo 1788095 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B5439811 : Blo 1788095 5439811 := bstep (se 1 (by rfl) ⟨4079858, by rfl⟩ : syracuseStep 5439811 = 8159717) B8159717
theorem B4530563 : Blo 1788095 4530563 := bstep (se 1 (by rfl) ⟨3397922, by rfl⟩ : syracuseStep 4530563 = 6795845) B6795845
theorem B6037901 : Blo 1788095 6037901 := bstep (se 3 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 6037901 = 2264213) B2264213
theorem B2720161 : Blo 1788095 2720161 := bstep (se 2 (by rfl) ⟨1020060, by rfl⟩ : syracuseStep 2720161 = 2040121) B2040121
theorem B6037955 : Blo 1788095 6037955 := bstep (se 1 (by rfl) ⟨4528466, by rfl⟩ : syracuseStep 6037955 = 9056933) B9056933
theorem B5161475 : Blo 1788095 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B19350029 : Blo 1788095 19350029 := bstep (se 3 (by rfl) ⟨3628130, by rfl⟩ : syracuseStep 19350029 = 7256261) B7256261
theorem B11469347 : Blo 1788095 11469347 := bstep (se 1 (by rfl) ⟨8602010, by rfl⟩ : syracuseStep 11469347 = 17204021) B17204021
theorem B9052721 : Blo 1788095 9052721 := bstep (se 2 (by rfl) ⟨3394770, by rfl⟩ : syracuseStep 9052721 = 6789541) B6789541
theorem B2720321 : Blo 1788095 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B4530755 : Blo 1788095 4530755 := bstep (se 1 (by rfl) ⟨3398066, by rfl⟩ : syracuseStep 4530755 = 6796133) B6796133
theorem B6038225 : Blo 1788095 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B6791971 : Blo 1788095 6791971 := bstep (se 1 (by rfl) ⟨5093978, by rfl⟩ : syracuseStep 6791971 = 10187957) B10187957
theorem B2548579 : Blo 1788095 2548579 := bstep (se 1 (by rfl) ⟨1911434, by rfl⟩ : syracuseStep 2548579 = 3822869) B3822869
theorem B2417521 : Blo 1788095 2417521 := bstep (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) B1813141
theorem B2548675 : Blo 1788095 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B5096429 : Blo 1788095 5096429 := bstep (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) B1911161
theorem B1909747 : Blo 1788095 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B4023377 : Blo 1788095 4023377 := bstep (se 2 (by rfl) ⟨1508766, by rfl⟩ : syracuseStep 4023377 = 3017533) B3017533
theorem B4023395 : Blo 1788095 4023395 := bstep (se 1 (by rfl) ⟨3017546, by rfl⟩ : syracuseStep 4023395 = 6035093) B6035093
theorem B10192013 : Blo 1788095 10192013 := bstep (se 3 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 10192013 = 3822005) B3822005
theorem B5096621 : Blo 1788095 5096621 := bstep (se 3 (by rfl) ⟨955616, by rfl⟩ : syracuseStep 5096621 = 1911233) B1911233
theorem B6038765 : Blo 1788095 6038765 := bstep (se 3 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 6038765 = 2264537) B2264537
theorem B6038819 : Blo 1788095 6038819 := bstep (se 1 (by rfl) ⟨4529114, by rfl⟩ : syracuseStep 6038819 = 9058229) B9058229
theorem B4023665 : Blo 1788095 4023665 := bstep (se 2 (by rfl) ⟨1508874, by rfl⟩ : syracuseStep 4023665 = 3017749) B3017749
theorem B4023683 : Blo 1788095 4023683 := bstep (se 1 (by rfl) ⟨3017762, by rfl⟩ : syracuseStep 4023683 = 6035525) B6035525
theorem B7644557 : Blo 1788095 7644557 := bstep (se 3 (by rfl) ⟨1433354, by rfl⟩ : syracuseStep 7644557 = 2866709) B2866709
theorem B3818947 : Blo 1788095 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B6039089 : Blo 1788095 6039089 := bstep (se 2 (by rfl) ⟨2264658, by rfl⟩ : syracuseStep 6039089 = 4529317) B4529317
theorem B2721329 : Blo 1788095 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B25781813 : Blo 1788095 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B5809745 : Blo 1788095 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B10184291 : Blo 1788095 10184291 := bstep (se 1 (by rfl) ⟨7638218, by rfl⟩ : syracuseStep 10184291 = 15276437) B15276437
theorem B4081283 : Blo 1788095 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B4023953 : Blo 1788095 4023953 := bstep (se 2 (by rfl) ⟨1508982, by rfl⟩ : syracuseStep 4023953 = 3017965) B3017965
theorem B4023971 : Blo 1788095 4023971 := bstep (se 1 (by rfl) ⟨3017978, by rfl⟩ : syracuseStep 4023971 = 6035957) B6035957
theorem B6121133 : Blo 1788095 6121133 := bstep (se 3 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 6121133 = 2295425) B2295425
theorem B2148211 : Blo 1788095 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B4024241 : Blo 1788095 4024241 := bstep (se 2 (by rfl) ⟨1509090, by rfl⟩ : syracuseStep 4024241 = 3018181) B3018181
theorem B4024259 : Blo 1788095 4024259 := bstep (se 1 (by rfl) ⟨3018194, by rfl⟩ : syracuseStep 4024259 = 6036389) B6036389
theorem B9054179 : Blo 1788095 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B4589617 : Blo 1788095 4589617 := bstep (se 2 (by rfl) ⟨1721106, by rfl⟩ : syracuseStep 4589617 = 3442213) B3442213
theorem B6039629 : Blo 1788095 6039629 := bstep (se 3 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 6039629 = 2264861) B2264861
theorem B13076579 : Blo 1788095 13076579 := bstep (se 1 (by rfl) ⟨9807434, by rfl⟩ : syracuseStep 13076579 = 19614869) B19614869
theorem B6039683 : Blo 1788095 6039683 := bstep (se 1 (by rfl) ⟨4529762, by rfl⟩ : syracuseStep 6039683 = 9059525) B9059525
theorem B1788099 : Blo 1788095 1788099 := bstep (se 1 (by rfl) ⟨1341074, by rfl⟩ : syracuseStep 1788099 = 2682149) B2682149
theorem B4024529 : Blo 1788095 4024529 := bstep (se 2 (by rfl) ⟨1509198, by rfl⟩ : syracuseStep 4024529 = 3018397) B3018397
theorem B1788115 : Blo 1788095 1788115 := bstep (se 1 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 1788115 = 2682173) B2682173
theorem B1788131 : Blo 1788095 1788131 := bstep (se 1 (by rfl) ⟨1341098, by rfl⟩ : syracuseStep 1788131 = 2682197) B2682197
theorem B4024547 : Blo 1788095 4024547 := bstep (se 1 (by rfl) ⟨3018410, by rfl⟩ : syracuseStep 4024547 = 6036821) B6036821
theorem B1911011 : Blo 1788095 1911011 := bstep (se 1 (by rfl) ⟨1433258, by rfl⟩ : syracuseStep 1911011 = 2866517) B2866517
theorem B1788147 : Blo 1788095 1788147 := bstep (se 1 (by rfl) ⟨1341110, by rfl⟩ : syracuseStep 1788147 = 2682221) B2682221
theorem B1788163 : Blo 1788095 1788163 := bstep (se 1 (by rfl) ⟨1341122, by rfl⟩ : syracuseStep 1788163 = 2682245) B2682245
theorem B3819793 : Blo 1788095 3819793 := bstep (se 2 (by rfl) ⟨1432422, by rfl⟩ : syracuseStep 3819793 = 2864845) B2864845
theorem B2582801 : Blo 1788095 2582801 := bstep (se 2 (by rfl) ⟨968550, by rfl⟩ : syracuseStep 2582801 = 1937101) B1937101
theorem B1788179 : Blo 1788095 1788179 := bstep (se 1 (by rfl) ⟨1341134, by rfl⟩ : syracuseStep 1788179 = 2682269) B2682269
theorem B1788195 : Blo 1788095 1788195 := bstep (se 1 (by rfl) ⟨1341146, by rfl⟩ : syracuseStep 1788195 = 2682293) B2682293
theorem B1788211 : Blo 1788095 1788211 := bstep (se 1 (by rfl) ⟨1341158, by rfl⟩ : syracuseStep 1788211 = 2682317) B2682317
theorem B1788227 : Blo 1788095 1788227 := bstep (se 1 (by rfl) ⟨1341170, by rfl⟩ : syracuseStep 1788227 = 2682341) B2682341
theorem B1788243 : Blo 1788095 1788243 := bstep (se 1 (by rfl) ⟨1341182, by rfl⟩ : syracuseStep 1788243 = 2682365) B2682365
theorem B1788259 : Blo 1788095 1788259 := bstep (se 1 (by rfl) ⟨1341194, by rfl⟩ : syracuseStep 1788259 = 2682389) B2682389
theorem B1788275 : Blo 1788095 1788275 := bstep (se 1 (by rfl) ⟨1341206, by rfl⟩ : syracuseStep 1788275 = 2682413) B2682413
theorem B1788291 : Blo 1788095 1788291 := bstep (se 1 (by rfl) ⟨1341218, by rfl⟩ : syracuseStep 1788291 = 2682437) B2682437
theorem B6039953 : Blo 1788095 6039953 := bstep (se 2 (by rfl) ⟨2264982, by rfl⟩ : syracuseStep 6039953 = 4529965) B4529965
theorem B1788307 : Blo 1788095 1788307 := bstep (se 1 (by rfl) ⟨1341230, by rfl⟩ : syracuseStep 1788307 = 2682461) B2682461
theorem B1788323 : Blo 1788095 1788323 := bstep (se 1 (by rfl) ⟨1341242, by rfl⟩ : syracuseStep 1788323 = 2682485) B2682485
theorem B2263459 : Blo 1788095 2263459 := bstep (se 1 (by rfl) ⟨1697594, by rfl⟩ : syracuseStep 2263459 = 3395189) B3395189
theorem B1788339 : Blo 1788095 1788339 := bstep (se 1 (by rfl) ⟨1341254, by rfl⟩ : syracuseStep 1788339 = 2682509) B2682509
theorem B1788355 : Blo 1788095 1788355 := bstep (se 1 (by rfl) ⟨1341266, by rfl⟩ : syracuseStep 1788355 = 2682533) B2682533
theorem B1788371 : Blo 1788095 1788371 := bstep (se 1 (by rfl) ⟨1341278, by rfl⟩ : syracuseStep 1788371 = 2682557) B2682557
theorem B1788387 : Blo 1788095 1788387 := bstep (se 1 (by rfl) ⟨1341290, by rfl⟩ : syracuseStep 1788387 = 2682581) B2682581
theorem B4024817 : Blo 1788095 4024817 := bstep (se 2 (by rfl) ⟨1509306, by rfl⟩ : syracuseStep 4024817 = 3018613) B3018613
theorem B1788403 : Blo 1788095 1788403 := bstep (se 1 (by rfl) ⟨1341302, by rfl⟩ : syracuseStep 1788403 = 2682605) B2682605
theorem B1812979 : Blo 1788095 1812979 := bstep (se 1 (by rfl) ⟨1359734, by rfl⟩ : syracuseStep 1812979 = 2719469) B2719469
theorem B1788419 : Blo 1788095 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B2263555 : Blo 1788095 2263555 := bstep (se 1 (by rfl) ⟨1697666, by rfl⟩ : syracuseStep 2263555 = 3395333) B3395333
theorem B4024835 : Blo 1788095 4024835 := bstep (se 1 (by rfl) ⟨3018626, by rfl⟩ : syracuseStep 4024835 = 6037253) B6037253
theorem B1788435 : Blo 1788095 1788435 := bstep (se 1 (by rfl) ⟨1341326, by rfl⟩ : syracuseStep 1788435 = 2682653) B2682653
theorem B1788451 : Blo 1788095 1788451 := bstep (se 1 (by rfl) ⟨1341338, by rfl⟩ : syracuseStep 1788451 = 2682677) B2682677
theorem B1788467 : Blo 1788095 1788467 := bstep (se 1 (by rfl) ⟨1341350, by rfl⟩ : syracuseStep 1788467 = 2682701) B2682701
theorem B1788483 : Blo 1788095 1788483 := bstep (se 1 (by rfl) ⟨1341362, by rfl⟩ : syracuseStep 1788483 = 2682725) B2682725
theorem B9800261 : Blo 1788095 9800261 := bstep (se 4 (by rfl) ⟨918774, by rfl⟩ : syracuseStep 9800261 = 1837549) B1837549
theorem B1788499 : Blo 1788095 1788499 := bstep (se 1 (by rfl) ⟨1341374, by rfl⟩ : syracuseStep 1788499 = 2682749) B2682749
theorem B1788515 : Blo 1788095 1788515 := bstep (se 1 (by rfl) ⟨1341386, by rfl⟩ : syracuseStep 1788515 = 2682773) B2682773
theorem B1788531 : Blo 1788095 1788531 := bstep (se 1 (by rfl) ⟨1341398, by rfl⟩ : syracuseStep 1788531 = 2682797) B2682797
theorem B1788547 : Blo 1788095 1788547 := bstep (se 1 (by rfl) ⟨1341410, by rfl⟩ : syracuseStep 1788547 = 2682821) B2682821
theorem B1788563 : Blo 1788095 1788563 := bstep (se 1 (by rfl) ⟨1341422, by rfl⟩ : syracuseStep 1788563 = 2682845) B2682845
theorem B1788579 : Blo 1788095 1788579 := bstep (se 1 (by rfl) ⟨1341434, by rfl⟩ : syracuseStep 1788579 = 2682869) B2682869
theorem B7645873 : Blo 1788095 7645873 := bstep (se 2 (by rfl) ⟨2867202, by rfl⟩ : syracuseStep 7645873 = 5734405) B5734405
theorem B1788595 : Blo 1788095 1788595 := bstep (se 1 (by rfl) ⟨1341446, by rfl⟩ : syracuseStep 1788595 = 2682893) B2682893
theorem B1788611 : Blo 1788095 1788611 := bstep (se 1 (by rfl) ⟨1341458, by rfl⟩ : syracuseStep 1788611 = 2682917) B2682917
theorem B3017425 : Blo 1788095 3017425 := bstep (se 2 (by rfl) ⟨1131534, by rfl⟩ : syracuseStep 3017425 = 2263069) B2263069
theorem B1788627 : Blo 1788095 1788627 := bstep (se 1 (by rfl) ⟨1341470, by rfl⟩ : syracuseStep 1788627 = 2682941) B2682941
theorem B1788643 : Blo 1788095 1788643 := bstep (se 1 (by rfl) ⟨1341482, by rfl⟩ : syracuseStep 1788643 = 2682965) B2682965
theorem B3017459 : Blo 1788095 3017459 := bstep (se 1 (by rfl) ⟨2263094, by rfl⟩ : syracuseStep 3017459 = 4526189) B4526189
theorem B1788659 : Blo 1788095 1788659 := bstep (se 1 (by rfl) ⟨1341494, by rfl⟩ : syracuseStep 1788659 = 2682989) B2682989
theorem B1788675 : Blo 1788095 1788675 := bstep (se 1 (by rfl) ⟨1341506, by rfl⟩ : syracuseStep 1788675 = 2683013) B2683013
theorem B9054989 : Blo 1788095 9054989 := bstep (se 3 (by rfl) ⟨1697810, by rfl⟩ : syracuseStep 9054989 = 3395621) B3395621
theorem B4025105 : Blo 1788095 4025105 := bstep (se 2 (by rfl) ⟨1509414, by rfl⟩ : syracuseStep 4025105 = 3018829) B3018829
theorem B1788691 : Blo 1788095 1788691 := bstep (se 1 (by rfl) ⟨1341518, by rfl⟩ : syracuseStep 1788691 = 2683037) B2683037
theorem B1788707 : Blo 1788095 1788707 := bstep (se 1 (by rfl) ⟨1341530, by rfl⟩ : syracuseStep 1788707 = 2683061) B2683061
theorem B4025123 : Blo 1788095 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B1788723 : Blo 1788095 1788723 := bstep (se 1 (by rfl) ⟨1341542, by rfl⟩ : syracuseStep 1788723 = 2683085) B2683085
theorem B1788739 : Blo 1788095 1788739 := bstep (se 1 (by rfl) ⟨1341554, by rfl⟩ : syracuseStep 1788739 = 2683109) B2683109
theorem B1788755 : Blo 1788095 1788755 := bstep (se 1 (by rfl) ⟨1341566, by rfl⟩ : syracuseStep 1788755 = 2683133) B2683133
theorem B1788771 : Blo 1788095 1788771 := bstep (se 1 (by rfl) ⟨1341578, by rfl⟩ : syracuseStep 1788771 = 2683157) B2683157
theorem B20663153 : Blo 1788095 20663153 := bstep (se 2 (by rfl) ⟨7748682, by rfl⟩ : syracuseStep 20663153 = 15497365) B15497365
theorem B3017587 : Blo 1788095 3017587 := bstep (se 1 (by rfl) ⟨2263190, by rfl⟩ : syracuseStep 3017587 = 4526381) B4526381
theorem B1788787 : Blo 1788095 1788787 := bstep (se 1 (by rfl) ⟨1341590, by rfl⟩ : syracuseStep 1788787 = 2683181) B2683181
theorem B1788803 : Blo 1788095 1788803 := bstep (se 1 (by rfl) ⟨1341602, by rfl⟩ : syracuseStep 1788803 = 2683205) B2683205
theorem B1788819 : Blo 1788095 1788819 := bstep (se 1 (by rfl) ⟨1341614, by rfl⟩ : syracuseStep 1788819 = 2683229) B2683229
theorem B1788835 : Blo 1788095 1788835 := bstep (se 1 (by rfl) ⟨1341626, by rfl⟩ : syracuseStep 1788835 = 2683253) B2683253
theorem B6040493 : Blo 1788095 6040493 := bstep (se 3 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 6040493 = 2265185) B2265185
theorem B1788851 : Blo 1788095 1788851 := bstep (se 1 (by rfl) ⟨1341638, by rfl⟩ : syracuseStep 1788851 = 2683277) B2683277
theorem B1788867 : Blo 1788095 1788867 := bstep (se 1 (by rfl) ⟨1341650, by rfl⟩ : syracuseStep 1788867 = 2683301) B2683301
theorem B17198021 : Blo 1788095 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B6794189 : Blo 1788095 6794189 := bstep (se 3 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 6794189 = 2547821) B2547821
theorem B1788883 : Blo 1788095 1788883 := bstep (se 1 (by rfl) ⟨1341662, by rfl⟩ : syracuseStep 1788883 = 2683325) B2683325
theorem B1788899 : Blo 1788095 1788899 := bstep (se 1 (by rfl) ⟨1341674, by rfl⟩ : syracuseStep 1788899 = 2683349) B2683349
theorem B6040547 : Blo 1788095 6040547 := bstep (se 1 (by rfl) ⟨4530410, by rfl⟩ : syracuseStep 6040547 = 9060821) B9060821
theorem B2264051 : Blo 1788095 2264051 := bstep (se 1 (by rfl) ⟨1698038, by rfl⟩ : syracuseStep 2264051 = 3396077) B3396077
theorem B1788915 : Blo 1788095 1788915 := bstep (se 1 (by rfl) ⟨1341686, by rfl⟩ : syracuseStep 1788915 = 2683373) B2683373
theorem B3017729 : Blo 1788095 3017729 := bstep (se 2 (by rfl) ⟨1131648, by rfl⟩ : syracuseStep 3017729 = 2263297) B2263297
theorem B1788931 : Blo 1788095 1788931 := bstep (se 1 (by rfl) ⟨1341698, by rfl⟩ : syracuseStep 1788931 = 2683397) B2683397
theorem B1788947 : Blo 1788095 1788947 := bstep (se 1 (by rfl) ⟨1341710, by rfl⟩ : syracuseStep 1788947 = 2683421) B2683421
theorem B1788963 : Blo 1788095 1788963 := bstep (se 1 (by rfl) ⟨1341722, by rfl⟩ : syracuseStep 1788963 = 2683445) B2683445
theorem B4025393 : Blo 1788095 4025393 := bstep (se 2 (by rfl) ⟨1509522, by rfl⟩ : syracuseStep 4025393 = 3019045) B3019045
theorem B1788979 : Blo 1788095 1788979 := bstep (se 1 (by rfl) ⟨1341734, by rfl⟩ : syracuseStep 1788979 = 2683469) B2683469
theorem B1788995 : Blo 1788095 1788995 := bstep (se 1 (by rfl) ⟨1341746, by rfl⟩ : syracuseStep 1788995 = 2683493) B2683493
theorem B4025411 : Blo 1788095 4025411 := bstep (se 1 (by rfl) ⟨3019058, by rfl⟩ : syracuseStep 4025411 = 6038117) B6038117
theorem B1789011 : Blo 1788095 1789011 := bstep (se 1 (by rfl) ⟨1341758, by rfl⟩ : syracuseStep 1789011 = 2683517) B2683517
theorem B1789027 : Blo 1788095 1789027 := bstep (se 1 (by rfl) ⟨1341770, by rfl⟩ : syracuseStep 1789027 = 2683541) B2683541
theorem B1789043 : Blo 1788095 1789043 := bstep (se 1 (by rfl) ⟨1341782, by rfl⟩ : syracuseStep 1789043 = 2683565) B2683565
theorem B3017857 : Blo 1788095 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B1789059 : Blo 1788095 1789059 := bstep (se 1 (by rfl) ⟨1341794, by rfl⟩ : syracuseStep 1789059 = 2683589) B2683589
theorem B1789075 : Blo 1788095 1789075 := bstep (se 1 (by rfl) ⟨1341806, by rfl⟩ : syracuseStep 1789075 = 2683613) B2683613
theorem B3017891 : Blo 1788095 3017891 := bstep (se 1 (by rfl) ⟨2263418, by rfl⟩ : syracuseStep 3017891 = 4526837) B4526837
theorem B1789091 : Blo 1788095 1789091 := bstep (se 1 (by rfl) ⟨1341818, by rfl⟩ : syracuseStep 1789091 = 2683637) B2683637
theorem B1789107 : Blo 1788095 1789107 := bstep (se 1 (by rfl) ⟨1341830, by rfl⟩ : syracuseStep 1789107 = 2683661) B2683661
theorem B1789123 : Blo 1788095 1789123 := bstep (se 1 (by rfl) ⟨1341842, by rfl⟩ : syracuseStep 1789123 = 2683685) B2683685
theorem B1789139 : Blo 1788095 1789139 := bstep (se 1 (by rfl) ⟨1341854, by rfl⟩ : syracuseStep 1789139 = 2683709) B2683709
theorem B1789155 : Blo 1788095 1789155 := bstep (se 1 (by rfl) ⟨1341866, by rfl⟩ : syracuseStep 1789155 = 2683733) B2683733
theorem B3394801 : Blo 1788095 3394801 := bstep (se 2 (by rfl) ⟨1273050, by rfl⟩ : syracuseStep 3394801 = 2546101) B2546101
theorem B6040817 : Blo 1788095 6040817 := bstep (se 2 (by rfl) ⟨2265306, by rfl⟩ : syracuseStep 6040817 = 4530613) B4530613
theorem B1789171 : Blo 1788095 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B1789187 : Blo 1788095 1789187 := bstep (se 1 (by rfl) ⟨1341890, by rfl⟩ : syracuseStep 1789187 = 2683781) B2683781
theorem B1789203 : Blo 1788095 1789203 := bstep (se 1 (by rfl) ⟨1341902, by rfl⟩ : syracuseStep 1789203 = 2683805) B2683805
theorem B3018019 : Blo 1788095 3018019 := bstep (se 1 (by rfl) ⟨2263514, by rfl⟩ : syracuseStep 3018019 = 4527029) B4527029
theorem B1789219 : Blo 1788095 1789219 := bstep (se 1 (by rfl) ⟨1341914, by rfl⟩ : syracuseStep 1789219 = 2683829) B2683829
theorem B2682161 : Blo 1788095 2682161 := bstep (se 2 (by rfl) ⟨1005810, by rfl⟩ : syracuseStep 2682161 = 2011621) B2011621
theorem B1789235 : Blo 1788095 1789235 := bstep (se 1 (by rfl) ⟨1341926, by rfl⟩ : syracuseStep 1789235 = 2683853) B2683853
theorem B2682179 : Blo 1788095 2682179 := bstep (se 1 (by rfl) ⟨2011634, by rfl⟩ : syracuseStep 2682179 = 4023269) B4023269
theorem B1789251 : Blo 1788095 1789251 := bstep (se 1 (by rfl) ⟨1341938, by rfl⟩ : syracuseStep 1789251 = 2683877) B2683877
theorem B10194245 : Blo 1788095 10194245 := bstep (se 4 (by rfl) ⟨955710, by rfl⟩ : syracuseStep 10194245 = 1911421) B1911421
theorem B4836685 : Blo 1788095 4836685 := bstep (se 3 (by rfl) ⟨906878, by rfl⟩ : syracuseStep 4836685 = 1813757) B1813757
theorem B4025681 : Blo 1788095 4025681 := bstep (se 2 (by rfl) ⟨1509630, by rfl⟩ : syracuseStep 4025681 = 3019261) B3019261
theorem B4590929 : Blo 1788095 4590929 := bstep (se 2 (by rfl) ⟨1721598, by rfl⟩ : syracuseStep 4590929 = 3443197) B3443197
theorem B1789267 : Blo 1788095 1789267 := bstep (se 1 (by rfl) ⟨1341950, by rfl⟩ : syracuseStep 1789267 = 2683901) B2683901
theorem B2682209 : Blo 1788095 2682209 := bstep (se 2 (by rfl) ⟨1005828, by rfl⟩ : syracuseStep 2682209 = 2011657) B2011657
theorem B7638371 : Blo 1788095 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B4025699 : Blo 1788095 4025699 := bstep (se 1 (by rfl) ⟨3019274, by rfl⟩ : syracuseStep 4025699 = 6038549) B6038549
theorem B1789283 : Blo 1788095 1789283 := bstep (se 1 (by rfl) ⟨1341962, by rfl⟩ : syracuseStep 1789283 = 2683925) B2683925
theorem B2682227 : Blo 1788095 2682227 := bstep (se 1 (by rfl) ⟨2011670, by rfl⟩ : syracuseStep 2682227 = 4023341) B4023341
theorem B1789299 : Blo 1788095 1789299 := bstep (se 1 (by rfl) ⟨1341974, by rfl⟩ : syracuseStep 1789299 = 2683949) B2683949
theorem B1789315 : Blo 1788095 1789315 := bstep (se 1 (by rfl) ⟨1341986, by rfl⟩ : syracuseStep 1789315 = 2683973) B2683973
theorem B2682257 : Blo 1788095 2682257 := bstep (se 2 (by rfl) ⟨1005846, by rfl⟩ : syracuseStep 2682257 = 2011693) B2011693
theorem B5590417 : Blo 1788095 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B1789331 : Blo 1788095 1789331 := bstep (se 1 (by rfl) ⟨1341998, by rfl⟩ : syracuseStep 1789331 = 2683997) B2683997
theorem B2682275 : Blo 1788095 2682275 := bstep (se 1 (by rfl) ⟨2011706, by rfl⟩ : syracuseStep 2682275 = 4023413) B4023413
theorem B1789347 : Blo 1788095 1789347 := bstep (se 1 (by rfl) ⟨1342010, by rfl⟩ : syracuseStep 1789347 = 2684021) B2684021
theorem B3018161 : Blo 1788095 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B1789363 : Blo 1788095 1789363 := bstep (se 1 (by rfl) ⟨1342022, by rfl⟩ : syracuseStep 1789363 = 2684045) B2684045
theorem B2682305 : Blo 1788095 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B1789379 : Blo 1788095 1789379 := bstep (se 1 (by rfl) ⟨1342034, by rfl⟩ : syracuseStep 1789379 = 2684069) B2684069
theorem B10186181 : Blo 1788095 10186181 := bstep (se 4 (by rfl) ⟨954954, by rfl⟩ : syracuseStep 10186181 = 1909909) B1909909
theorem B2682323 : Blo 1788095 2682323 := bstep (se 1 (by rfl) ⟨2011742, by rfl⟩ : syracuseStep 2682323 = 4023485) B4023485
theorem B1789395 : Blo 1788095 1789395 := bstep (se 1 (by rfl) ⟨1342046, by rfl⟩ : syracuseStep 1789395 = 2684093) B2684093
theorem B1789411 : Blo 1788095 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B2682353 : Blo 1788095 2682353 := bstep (se 2 (by rfl) ⟨1005882, by rfl⟩ : syracuseStep 2682353 = 2011765) B2011765
theorem B17427953 : Blo 1788095 17427953 := bstep (se 2 (by rfl) ⟨6535482, by rfl⟩ : syracuseStep 17427953 = 13070965) B13070965
theorem B1789427 : Blo 1788095 1789427 := bstep (se 1 (by rfl) ⟨1342070, by rfl⟩ : syracuseStep 1789427 = 2684141) B2684141
theorem B2682371 : Blo 1788095 2682371 := bstep (se 1 (by rfl) ⟨2011778, by rfl⟩ : syracuseStep 2682371 = 4023557) B4023557
theorem B1789443 : Blo 1788095 1789443 := bstep (se 1 (by rfl) ⟨1342082, by rfl⟩ : syracuseStep 1789443 = 2684165) B2684165
theorem B17190413 : Blo 1788095 17190413 := bstep (se 3 (by rfl) ⟨3223202, by rfl⟩ : syracuseStep 17190413 = 6446405) B6446405
theorem B1789459 : Blo 1788095 1789459 := bstep (se 1 (by rfl) ⟨1342094, by rfl⟩ : syracuseStep 1789459 = 2684189) B2684189
theorem B2682401 : Blo 1788095 2682401 := bstep (se 2 (by rfl) ⟨1005900, by rfl⟩ : syracuseStep 2682401 = 2011801) B2011801
theorem B1789475 : Blo 1788095 1789475 := bstep (se 1 (by rfl) ⟨1342106, by rfl⟩ : syracuseStep 1789475 = 2684213) B2684213
theorem B3018289 : Blo 1788095 3018289 := bstep (se 2 (by rfl) ⟨1131858, by rfl⟩ : syracuseStep 3018289 = 2263717) B2263717
theorem B2682419 : Blo 1788095 2682419 := bstep (se 1 (by rfl) ⟨2011814, by rfl⟩ : syracuseStep 2682419 = 4023629) B4023629
theorem B1789491 : Blo 1788095 1789491 := bstep (se 1 (by rfl) ⟨1342118, by rfl⟩ : syracuseStep 1789491 = 2684237) B2684237
theorem B1789507 : Blo 1788095 1789507 := bstep (se 1 (by rfl) ⟨1342130, by rfl⟩ : syracuseStep 1789507 = 2684261) B2684261
theorem B2682449 : Blo 1788095 2682449 := bstep (se 2 (by rfl) ⟨1005918, by rfl⟩ : syracuseStep 2682449 = 2011837) B2011837
theorem B3018323 : Blo 1788095 3018323 := bstep (se 1 (by rfl) ⟨2263742, by rfl⟩ : syracuseStep 3018323 = 4527485) B4527485
theorem B1789523 : Blo 1788095 1789523 := bstep (se 1 (by rfl) ⟨1342142, by rfl⟩ : syracuseStep 1789523 = 2684285) B2684285
theorem B2682467 : Blo 1788095 2682467 := bstep (se 1 (by rfl) ⟨2011850, by rfl⟩ : syracuseStep 2682467 = 4023701) B4023701
theorem B1789539 : Blo 1788095 1789539 := bstep (se 1 (by rfl) ⟨1342154, by rfl⟩ : syracuseStep 1789539 = 2684309) B2684309
theorem B4025969 : Blo 1788095 4025969 := bstep (se 2 (by rfl) ⟨1509738, by rfl⟩ : syracuseStep 4025969 = 3019477) B3019477
theorem B1789555 : Blo 1788095 1789555 := bstep (se 1 (by rfl) ⟨1342166, by rfl⟩ : syracuseStep 1789555 = 2684333) B2684333
theorem B2682497 : Blo 1788095 2682497 := bstep (se 2 (by rfl) ⟨1005936, by rfl⟩ : syracuseStep 2682497 = 2011873) B2011873
theorem B4025987 : Blo 1788095 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B1789571 : Blo 1788095 1789571 := bstep (se 1 (by rfl) ⟨1342178, by rfl⟩ : syracuseStep 1789571 = 2684357) B2684357
theorem B5729933 : Blo 1788095 5729933 := bstep (se 3 (by rfl) ⟨1074362, by rfl⟩ : syracuseStep 5729933 = 2148725) B2148725
theorem B2682515 : Blo 1788095 2682515 := bstep (se 1 (by rfl) ⟨2011886, by rfl⟩ : syracuseStep 2682515 = 4023773) B4023773
theorem B1789587 : Blo 1788095 1789587 := bstep (se 1 (by rfl) ⟨1342190, by rfl⟩ : syracuseStep 1789587 = 2684381) B2684381
theorem B1789603 : Blo 1788095 1789603 := bstep (se 1 (by rfl) ⟨1342202, by rfl⟩ : syracuseStep 1789603 = 2684405) B2684405
theorem B2682545 : Blo 1788095 2682545 := bstep (se 2 (by rfl) ⟨1005954, by rfl⟩ : syracuseStep 2682545 = 2011909) B2011909
theorem B3223217 : Blo 1788095 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B2264755 : Blo 1788095 2264755 := bstep (se 1 (by rfl) ⟨1698566, by rfl⟩ : syracuseStep 2264755 = 3397133) B3397133
theorem B1789619 : Blo 1788095 1789619 := bstep (se 1 (by rfl) ⟨1342214, by rfl⟩ : syracuseStep 1789619 = 2684429) B2684429
theorem B2682563 : Blo 1788095 2682563 := bstep (se 1 (by rfl) ⟨2011922, by rfl⟩ : syracuseStep 2682563 = 4023845) B4023845
theorem B1789635 : Blo 1788095 1789635 := bstep (se 1 (by rfl) ⟨1342226, by rfl⟩ : syracuseStep 1789635 = 2684453) B2684453
theorem B3018451 : Blo 1788095 3018451 := bstep (se 1 (by rfl) ⟨2263838, by rfl⟩ : syracuseStep 3018451 = 4527677) B4527677
theorem B1789651 : Blo 1788095 1789651 := bstep (se 1 (by rfl) ⟨1342238, by rfl⟩ : syracuseStep 1789651 = 2684477) B2684477
theorem B2682593 : Blo 1788095 2682593 := bstep (se 2 (by rfl) ⟨1005972, by rfl⟩ : syracuseStep 2682593 = 2011945) B2011945
theorem B1789667 : Blo 1788095 1789667 := bstep (se 1 (by rfl) ⟨1342250, by rfl⟩ : syracuseStep 1789667 = 2684501) B2684501
theorem B2682611 : Blo 1788095 2682611 := bstep (se 1 (by rfl) ⟨2011958, by rfl⟩ : syracuseStep 2682611 = 4023917) B4023917
theorem B1789683 : Blo 1788095 1789683 := bstep (se 1 (by rfl) ⟨1342262, by rfl⟩ : syracuseStep 1789683 = 2684525) B2684525
theorem B1789699 : Blo 1788095 1789699 := bstep (se 1 (by rfl) ⟨1342274, by rfl⟩ : syracuseStep 1789699 = 2684549) B2684549
theorem B5730061 : Blo 1788095 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B6041357 : Blo 1788095 6041357 := bstep (se 3 (by rfl) ⟨1132754, by rfl⟩ : syracuseStep 6041357 = 2265509) B2265509
theorem B2682641 : Blo 1788095 2682641 := bstep (se 2 (by rfl) ⟨1005990, by rfl⟩ : syracuseStep 2682641 = 2011981) B2011981
theorem B2617105 : Blo 1788095 2617105 := bstep (se 2 (by rfl) ⟨981414, by rfl⟩ : syracuseStep 2617105 = 1962829) B1962829
theorem B2264851 : Blo 1788095 2264851 := bstep (se 1 (by rfl) ⟨1698638, by rfl⟩ : syracuseStep 2264851 = 3397277) B3397277
theorem B1789715 : Blo 1788095 1789715 := bstep (se 1 (by rfl) ⟨1342286, by rfl⟩ : syracuseStep 1789715 = 2684573) B2684573
theorem B2682659 : Blo 1788095 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B1789731 : Blo 1788095 1789731 := bstep (se 1 (by rfl) ⟨1342298, by rfl⟩ : syracuseStep 1789731 = 2684597) B2684597
theorem B1789747 : Blo 1788095 1789747 := bstep (se 1 (by rfl) ⟨1342310, by rfl⟩ : syracuseStep 1789747 = 2684621) B2684621
theorem B2682689 : Blo 1788095 2682689 := bstep (se 2 (by rfl) ⟨1006008, by rfl⟩ : syracuseStep 2682689 = 2012017) B2012017
theorem B1789763 : Blo 1788095 1789763 := bstep (se 1 (by rfl) ⟨1342322, by rfl⟩ : syracuseStep 1789763 = 2684645) B2684645
theorem B6041411 : Blo 1788095 6041411 := bstep (se 1 (by rfl) ⟨4531058, by rfl⟩ : syracuseStep 6041411 = 9062117) B9062117
theorem B2682707 : Blo 1788095 2682707 := bstep (se 1 (by rfl) ⟨2012030, by rfl⟩ : syracuseStep 2682707 = 4024061) B4024061
theorem B1789779 : Blo 1788095 1789779 := bstep (se 1 (by rfl) ⟨1342334, by rfl⟩ : syracuseStep 1789779 = 2684669) B2684669
theorem B3018593 : Blo 1788095 3018593 := bstep (se 2 (by rfl) ⟨1131972, by rfl⟩ : syracuseStep 3018593 = 2263945) B2263945
theorem B1789795 : Blo 1788095 1789795 := bstep (se 1 (by rfl) ⟨1342346, by rfl⟩ : syracuseStep 1789795 = 2684693) B2684693
theorem B2682737 : Blo 1788095 2682737 := bstep (se 2 (by rfl) ⟨1006026, by rfl⟩ : syracuseStep 2682737 = 2012053) B2012053
theorem B1789811 : Blo 1788095 1789811 := bstep (se 1 (by rfl) ⟨1342358, by rfl⟩ : syracuseStep 1789811 = 2684717) B2684717
theorem B2682755 : Blo 1788095 2682755 := bstep (se 1 (by rfl) ⟨2012066, by rfl⟩ : syracuseStep 2682755 = 4024133) B4024133
theorem B1789827 : Blo 1788095 1789827 := bstep (se 1 (by rfl) ⟨1342370, by rfl⟩ : syracuseStep 1789827 = 2684741) B2684741
theorem B4026257 : Blo 1788095 4026257 := bstep (se 2 (by rfl) ⟨1509846, by rfl⟩ : syracuseStep 4026257 = 3019693) B3019693
theorem B1789843 : Blo 1788095 1789843 := bstep (se 1 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 1789843 = 2684765) B2684765
theorem B2150291 : Blo 1788095 2150291 := bstep (se 1 (by rfl) ⟨1612718, by rfl⟩ : syracuseStep 2150291 = 3225437) B3225437
theorem B2682785 : Blo 1788095 2682785 := bstep (se 2 (by rfl) ⟨1006044, by rfl⟩ : syracuseStep 2682785 = 2012089) B2012089
theorem B4026275 : Blo 1788095 4026275 := bstep (se 1 (by rfl) ⟨3019706, by rfl⟩ : syracuseStep 4026275 = 6039413) B6039413
theorem B1789859 : Blo 1788095 1789859 := bstep (se 1 (by rfl) ⟨1342394, by rfl⟩ : syracuseStep 1789859 = 2684789) B2684789
theorem B2682803 : Blo 1788095 2682803 := bstep (se 1 (by rfl) ⟨2012102, by rfl⟩ : syracuseStep 2682803 = 4024205) B4024205
theorem B1789875 : Blo 1788095 1789875 := bstep (se 1 (by rfl) ⟨1342406, by rfl⟩ : syracuseStep 1789875 = 2684813) B2684813
theorem B1789891 : Blo 1788095 1789891 := bstep (se 1 (by rfl) ⟨1342418, by rfl⟩ : syracuseStep 1789891 = 2684837) B2684837
theorem B2682833 : Blo 1788095 2682833 := bstep (se 2 (by rfl) ⟨1006062, by rfl⟩ : syracuseStep 2682833 = 2012125) B2012125
theorem B1789907 : Blo 1788095 1789907 := bstep (se 1 (by rfl) ⟨1342430, by rfl⟩ : syracuseStep 1789907 = 2684861) B2684861
theorem B3018721 : Blo 1788095 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B2682851 : Blo 1788095 2682851 := bstep (se 1 (by rfl) ⟨2012138, by rfl⟩ : syracuseStep 2682851 = 4024277) B4024277
theorem B1789923 : Blo 1788095 1789923 := bstep (se 1 (by rfl) ⟨1342442, by rfl⟩ : syracuseStep 1789923 = 2684885) B2684885
theorem B10194929 : Blo 1788095 10194929 := bstep (se 2 (by rfl) ⟨3823098, by rfl⟩ : syracuseStep 10194929 = 7646197) B7646197
theorem B1789939 : Blo 1788095 1789939 := bstep (se 1 (by rfl) ⟨1342454, by rfl⟩ : syracuseStep 1789939 = 2684909) B2684909
theorem B2682881 : Blo 1788095 2682881 := bstep (se 2 (by rfl) ⟨1006080, by rfl⟩ : syracuseStep 2682881 = 2012161) B2012161
theorem B3018755 : Blo 1788095 3018755 := bstep (se 1 (by rfl) ⟨2264066, by rfl⟩ : syracuseStep 3018755 = 4528133) B4528133
theorem B1789955 : Blo 1788095 1789955 := bstep (se 1 (by rfl) ⟨1342466, by rfl⟩ : syracuseStep 1789955 = 2684933) B2684933
theorem B5730317 : Blo 1788095 5730317 := bstep (se 3 (by rfl) ⟨1074434, by rfl⟩ : syracuseStep 5730317 = 2148869) B2148869
theorem B2682899 : Blo 1788095 2682899 := bstep (se 1 (by rfl) ⟨2012174, by rfl⟩ : syracuseStep 2682899 = 4024349) B4024349
theorem B1789971 : Blo 1788095 1789971 := bstep (se 1 (by rfl) ⟨1342478, by rfl⟩ : syracuseStep 1789971 = 2684957) B2684957
theorem B1789987 : Blo 1788095 1789987 := bstep (se 1 (by rfl) ⟨1342490, by rfl⟩ : syracuseStep 1789987 = 2684981) B2684981
theorem B2682929 : Blo 1788095 2682929 := bstep (se 2 (by rfl) ⟨1006098, by rfl⟩ : syracuseStep 2682929 = 2012197) B2012197
theorem B1790003 : Blo 1788095 1790003 := bstep (se 1 (by rfl) ⟨1342502, by rfl⟩ : syracuseStep 1790003 = 2685005) B2685005
theorem B2682947 : Blo 1788095 2682947 := bstep (se 1 (by rfl) ⟨2012210, by rfl⟩ : syracuseStep 2682947 = 4024421) B4024421
theorem B1790019 : Blo 1788095 1790019 := bstep (se 1 (by rfl) ⟨1342514, by rfl⟩ : syracuseStep 1790019 = 2685029) B2685029
theorem B1790035 : Blo 1788095 1790035 := bstep (se 1 (by rfl) ⟨1342526, by rfl⟩ : syracuseStep 1790035 = 2685053) B2685053
theorem B2682977 : Blo 1788095 2682977 := bstep (se 2 (by rfl) ⟨1006116, by rfl⟩ : syracuseStep 2682977 = 2012233) B2012233
theorem B12898403 : Blo 1788095 12898403 := bstep (se 1 (by rfl) ⟨9673802, by rfl⟩ : syracuseStep 12898403 = 19347605) B19347605
theorem B1790051 : Blo 1788095 1790051 := bstep (se 1 (by rfl) ⟨1342538, by rfl⟩ : syracuseStep 1790051 = 2685077) B2685077
theorem B13578353 : Blo 1788095 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B3821681 : Blo 1788095 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B2682995 : Blo 1788095 2682995 := bstep (se 1 (by rfl) ⟨2012246, by rfl⟩ : syracuseStep 2682995 = 4024493) B4024493
theorem B1790067 : Blo 1788095 1790067 := bstep (se 1 (by rfl) ⟨1342550, by rfl⟩ : syracuseStep 1790067 = 2685101) B2685101
theorem B3018883 : Blo 1788095 3018883 := bstep (se 1 (by rfl) ⟨2264162, by rfl⟩ : syracuseStep 3018883 = 4528325) B4528325
theorem B1790083 : Blo 1788095 1790083 := bstep (se 1 (by rfl) ⟨1342562, by rfl⟩ : syracuseStep 1790083 = 2685125) B2685125
theorem B12243077 : Blo 1788095 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B2683025 : Blo 1788095 2683025 := bstep (se 2 (by rfl) ⟨1006134, by rfl⟩ : syracuseStep 2683025 = 2012269) B2012269
theorem B2683043 : Blo 1788095 2683043 := bstep (se 1 (by rfl) ⟨2012282, by rfl⟩ : syracuseStep 2683043 = 4024565) B4024565
theorem B4026545 : Blo 1788095 4026545 := bstep (se 2 (by rfl) ⟨1509954, by rfl⟩ : syracuseStep 4026545 = 3019909) B3019909
theorem B2683073 : Blo 1788095 2683073 := bstep (se 2 (by rfl) ⟨1006152, by rfl⟩ : syracuseStep 2683073 = 2012305) B2012305
theorem B4026563 : Blo 1788095 4026563 := bstep (se 1 (by rfl) ⟨3019922, by rfl⟩ : syracuseStep 4026563 = 6039845) B6039845
theorem B2683091 : Blo 1788095 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B2683121 : Blo 1788095 2683121 := bstep (se 2 (by rfl) ⟨1006170, by rfl⟩ : syracuseStep 2683121 = 2012341) B2012341
theorem B6123761 : Blo 1788095 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B2068723 : Blo 1788095 2068723 := bstep (se 1 (by rfl) ⟨1551542, by rfl⟩ : syracuseStep 2068723 = 3103085) B3103085
theorem B2683139 : Blo 1788095 2683139 := bstep (se 1 (by rfl) ⟨2012354, by rfl⟩ : syracuseStep 2683139 = 4024709) B4024709
theorem B2265347 : Blo 1788095 2265347 := bstep (se 1 (by rfl) ⟨1699010, by rfl⟩ : syracuseStep 2265347 = 3398021) B3398021
theorem B3395857 : Blo 1788095 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B3019025 : Blo 1788095 3019025 := bstep (se 2 (by rfl) ⟨1132134, by rfl⟩ : syracuseStep 3019025 = 2264269) B2264269
theorem B2683169 : Blo 1788095 2683169 := bstep (se 2 (by rfl) ⟨1006188, by rfl⟩ : syracuseStep 2683169 = 2012377) B2012377
theorem B2683187 : Blo 1788095 2683187 := bstep (se 1 (by rfl) ⟨2012390, by rfl⟩ : syracuseStep 2683187 = 4024781) B4024781
theorem B2756915 : Blo 1788095 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B20369717 : Blo 1788095 20369717 := bstep (se 5 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 20369717 = 1909661) B1909661
theorem B6533453 : Blo 1788095 6533453 := bstep (se 3 (by rfl) ⟨1225022, by rfl⟩ : syracuseStep 6533453 = 2450045) B2450045
theorem B8163661 : Blo 1788095 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B2683217 : Blo 1788095 2683217 := bstep (se 2 (by rfl) ⟨1006206, by rfl⟩ : syracuseStep 2683217 = 2012413) B2012413
theorem B2683235 : Blo 1788095 2683235 := bstep (se 1 (by rfl) ⟨2012426, by rfl⟩ : syracuseStep 2683235 = 4024853) B4024853
theorem B2683265 : Blo 1788095 2683265 := bstep (se 2 (by rfl) ⟨1006224, by rfl⟩ : syracuseStep 2683265 = 2012449) B2012449
theorem B3019153 : Blo 1788095 3019153 := bstep (se 2 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 3019153 = 2264365) B2264365
theorem B2683283 : Blo 1788095 2683283 := bstep (se 1 (by rfl) ⟨2012462, by rfl⟩ : syracuseStep 2683283 = 4024925) B4024925
theorem B4526513 : Blo 1788095 4526513 := bstep (se 2 (by rfl) ⟨1697442, by rfl⟩ : syracuseStep 4526513 = 3394885) B3394885
theorem B2683313 : Blo 1788095 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B3019187 : Blo 1788095 3019187 := bstep (se 1 (by rfl) ⟨2264390, by rfl⟩ : syracuseStep 3019187 = 4528781) B4528781
theorem B2683331 : Blo 1788095 2683331 := bstep (se 1 (by rfl) ⟨2012498, by rfl⟩ : syracuseStep 2683331 = 4024997) B4024997
theorem B4026833 : Blo 1788095 4026833 := bstep (se 2 (by rfl) ⟨1510062, by rfl⟩ : syracuseStep 4026833 = 3020125) B3020125
theorem B2683361 : Blo 1788095 2683361 := bstep (se 2 (by rfl) ⟨1006260, by rfl⟩ : syracuseStep 2683361 = 2012521) B2012521
theorem B4526563 : Blo 1788095 4526563 := bstep (se 1 (by rfl) ⟨3394922, by rfl⟩ : syracuseStep 4526563 = 6789845) B6789845
theorem B26145251 : Blo 1788095 26145251 := bstep (se 1 (by rfl) ⟨19608938, by rfl⟩ : syracuseStep 26145251 = 39217877) B39217877
theorem B4026851 : Blo 1788095 4026851 := bstep (se 1 (by rfl) ⟨3020138, by rfl⟩ : syracuseStep 4026851 = 6040277) B6040277
theorem B2683379 : Blo 1788095 2683379 := bstep (se 1 (by rfl) ⟨2012534, by rfl⟩ : syracuseStep 2683379 = 4025069) B4025069
theorem B2683409 : Blo 1788095 2683409 := bstep (se 2 (by rfl) ⟨1006278, by rfl⟩ : syracuseStep 2683409 = 2012557) B2012557
theorem B2683427 : Blo 1788095 2683427 := bstep (se 1 (by rfl) ⟨2012570, by rfl⟩ : syracuseStep 2683427 = 4025141) B4025141
theorem B3019315 : Blo 1788095 3019315 := bstep (se 1 (by rfl) ⟨2264486, by rfl⟩ : syracuseStep 3019315 = 4528973) B4528973
theorem B2683457 : Blo 1788095 2683457 := bstep (se 2 (by rfl) ⟨1006296, by rfl⟩ : syracuseStep 2683457 = 2012593) B2012593
theorem B2683475 : Blo 1788095 2683475 := bstep (se 1 (by rfl) ⟨2012606, by rfl⟩ : syracuseStep 2683475 = 4025213) B4025213
theorem B2011747 : Blo 1788095 2011747 := bstep (se 1 (by rfl) ⟨1508810, by rfl⟩ : syracuseStep 2011747 = 3017621) B3017621
theorem B4297315 : Blo 1788095 4297315 := bstep (se 1 (by rfl) ⟨3222986, by rfl⟩ : syracuseStep 4297315 = 6445973) B6445973
theorem B4526705 : Blo 1788095 4526705 := bstep (se 2 (by rfl) ⟨1697514, by rfl⟩ : syracuseStep 4526705 = 3395029) B3395029
theorem B2683505 : Blo 1788095 2683505 := bstep (se 2 (by rfl) ⟨1006314, by rfl⟩ : syracuseStep 2683505 = 2012629) B2012629
theorem B2683523 : Blo 1788095 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B2683553 : Blo 1788095 2683553 := bstep (se 2 (by rfl) ⟨1006332, by rfl⟩ : syracuseStep 2683553 = 2012665) B2012665
theorem B3396259 : Blo 1788095 3396259 := bstep (se 1 (by rfl) ⟨2547194, by rfl⟩ : syracuseStep 3396259 = 5094389) B5094389
theorem B2683571 : Blo 1788095 2683571 := bstep (se 1 (by rfl) ⟨2012678, by rfl⟩ : syracuseStep 2683571 = 4025357) B4025357
theorem B3019457 : Blo 1788095 3019457 := bstep (se 2 (by rfl) ⟨1132296, by rfl⟩ : syracuseStep 3019457 = 2264593) B2264593
theorem B4838093 : Blo 1788095 4838093 := bstep (se 3 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 4838093 = 1814285) B1814285
theorem B3396305 : Blo 1788095 3396305 := bstep (se 2 (by rfl) ⟨1273614, by rfl⟩ : syracuseStep 3396305 = 2547229) B2547229
theorem B2683601 : Blo 1788095 2683601 := bstep (se 2 (by rfl) ⟨1006350, by rfl⟩ : syracuseStep 2683601 = 2012701) B2012701
theorem B2683619 : Blo 1788095 2683619 := bstep (se 1 (by rfl) ⟨2012714, by rfl⟩ : syracuseStep 2683619 = 4025429) B4025429
theorem B4027121 : Blo 1788095 4027121 := bstep (se 2 (by rfl) ⟨1510170, by rfl⟩ : syracuseStep 4027121 = 3020341) B3020341
theorem B2011891 : Blo 1788095 2011891 := bstep (se 1 (by rfl) ⟨1508918, by rfl⟩ : syracuseStep 2011891 = 3017837) B3017837
theorem B2683649 : Blo 1788095 2683649 := bstep (se 2 (by rfl) ⟨1006368, by rfl⟩ : syracuseStep 2683649 = 2012737) B2012737
theorem B4027139 : Blo 1788095 4027139 := bstep (se 1 (by rfl) ⟨3020354, by rfl⟩ : syracuseStep 4027139 = 6040709) B6040709
theorem B2683667 : Blo 1788095 2683667 := bstep (se 1 (by rfl) ⟨2012750, by rfl⟩ : syracuseStep 2683667 = 4025501) B4025501
theorem B2683697 : Blo 1788095 2683697 := bstep (se 2 (by rfl) ⟨1006386, by rfl⟩ : syracuseStep 2683697 = 2012773) B2012773
theorem B3019585 : Blo 1788095 3019585 := bstep (se 2 (by rfl) ⟨1132344, by rfl⟩ : syracuseStep 3019585 = 2264689) B2264689
theorem B2683715 : Blo 1788095 2683715 := bstep (se 1 (by rfl) ⟨2012786, by rfl⟩ : syracuseStep 2683715 = 4025573) B4025573
theorem B2683745 : Blo 1788095 2683745 := bstep (se 2 (by rfl) ⟨1006404, by rfl⟩ : syracuseStep 2683745 = 2012809) B2012809
theorem B3019619 : Blo 1788095 3019619 := bstep (se 1 (by rfl) ⟨2264714, by rfl⟩ : syracuseStep 3019619 = 4529429) B4529429
theorem B30561137 : Blo 1788095 30561137 := bstep (se 2 (by rfl) ⟨11460426, by rfl⟩ : syracuseStep 30561137 = 22920853) B22920853
theorem B2683763 : Blo 1788095 2683763 := bstep (se 1 (by rfl) ⟨2012822, by rfl⟩ : syracuseStep 2683763 = 4025645) B4025645
theorem B2012035 : Blo 1788095 2012035 := bstep (se 1 (by rfl) ⟨1509026, by rfl⟩ : syracuseStep 2012035 = 3018053) B3018053
theorem B2683793 : Blo 1788095 2683793 := bstep (se 2 (by rfl) ⟨1006422, by rfl⟩ : syracuseStep 2683793 = 2012845) B2012845
theorem B2683811 : Blo 1788095 2683811 := bstep (se 1 (by rfl) ⟨2012858, by rfl⟩ : syracuseStep 2683811 = 4025717) B4025717
theorem B2683841 : Blo 1788095 2683841 := bstep (se 2 (by rfl) ⟨1006440, by rfl⟩ : syracuseStep 2683841 = 2012881) B2012881
theorem B2683859 : Blo 1788095 2683859 := bstep (se 1 (by rfl) ⟨2012894, by rfl⟩ : syracuseStep 2683859 = 4025789) B4025789
theorem B3019747 : Blo 1788095 3019747 := bstep (se 1 (by rfl) ⟨2264810, by rfl⟩ : syracuseStep 3019747 = 4529621) B4529621
theorem B10761187 : Blo 1788095 10761187 := bstep (se 1 (by rfl) ⟨8070890, by rfl⟩ : syracuseStep 10761187 = 16141781) B16141781
theorem B3396593 : Blo 1788095 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2683889 : Blo 1788095 2683889 := bstep (se 2 (by rfl) ⟨1006458, by rfl⟩ : syracuseStep 2683889 = 2012917) B2012917
theorem B2683907 : Blo 1788095 2683907 := bstep (se 1 (by rfl) ⟨2012930, by rfl⟩ : syracuseStep 2683907 = 4025861) B4025861
theorem B4027409 : Blo 1788095 4027409 := bstep (se 2 (by rfl) ⟨1510278, by rfl⟩ : syracuseStep 4027409 = 3020557) B3020557
theorem B2012179 : Blo 1788095 2012179 := bstep (se 1 (by rfl) ⟨1509134, by rfl⟩ : syracuseStep 2012179 = 3018269) B3018269
theorem B2683937 : Blo 1788095 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B4027427 : Blo 1788095 4027427 := bstep (se 1 (by rfl) ⟨3020570, by rfl⟩ : syracuseStep 4027427 = 6041141) B6041141
theorem B2683955 : Blo 1788095 2683955 := bstep (se 1 (by rfl) ⟨2012966, by rfl⟩ : syracuseStep 2683955 = 4025933) B4025933
theorem B2683985 : Blo 1788095 2683985 := bstep (se 2 (by rfl) ⟨1006494, by rfl⟩ : syracuseStep 2683985 = 2012989) B2012989
theorem B2684003 : Blo 1788095 2684003 := bstep (se 1 (by rfl) ⟨2013002, by rfl⟩ : syracuseStep 2684003 = 4026005) B4026005
theorem B7746673 : Blo 1788095 7746673 := bstep (se 2 (by rfl) ⟨2905002, by rfl⟩ : syracuseStep 7746673 = 5810005) B5810005
theorem B3019889 : Blo 1788095 3019889 := bstep (se 2 (by rfl) ⟨1132458, by rfl⟩ : syracuseStep 3019889 = 2264917) B2264917
theorem B2684033 : Blo 1788095 2684033 := bstep (se 2 (by rfl) ⟨1006512, by rfl⟩ : syracuseStep 2684033 = 2013025) B2013025
theorem B2684051 : Blo 1788095 2684051 := bstep (se 1 (by rfl) ⟨2013038, by rfl⟩ : syracuseStep 2684051 = 4026077) B4026077
theorem B2012323 : Blo 1788095 2012323 := bstep (se 1 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 2012323 = 3018485) B3018485
theorem B2684081 : Blo 1788095 2684081 := bstep (se 2 (by rfl) ⟨1006530, by rfl⟩ : syracuseStep 2684081 = 2013061) B2013061
theorem B3060929 : Blo 1788095 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B2684099 : Blo 1788095 2684099 := bstep (se 1 (by rfl) ⟨2013074, by rfl⟩ : syracuseStep 2684099 = 4026149) B4026149
theorem B2684129 : Blo 1788095 2684129 := bstep (se 2 (by rfl) ⟨1006548, by rfl⟩ : syracuseStep 2684129 = 2013097) B2013097
theorem B3020017 : Blo 1788095 3020017 := bstep (se 2 (by rfl) ⟨1132506, by rfl⟩ : syracuseStep 3020017 = 2265013) B2265013
theorem B2684147 : Blo 1788095 2684147 := bstep (se 1 (by rfl) ⟨2013110, by rfl⟩ : syracuseStep 2684147 = 4026221) B4026221
theorem B2684177 : Blo 1788095 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B3020051 : Blo 1788095 3020051 := bstep (se 1 (by rfl) ⟨2265038, by rfl⟩ : syracuseStep 3020051 = 4530077) B4530077
theorem B2684195 : Blo 1788095 2684195 := bstep (se 1 (by rfl) ⟨2013146, by rfl⟩ : syracuseStep 2684195 = 4026293) B4026293
theorem B4027697 : Blo 1788095 4027697 := bstep (se 2 (by rfl) ⟨1510386, by rfl⟩ : syracuseStep 4027697 = 3020773) B3020773
theorem B2012467 : Blo 1788095 2012467 := bstep (se 1 (by rfl) ⟨1509350, by rfl⟩ : syracuseStep 2012467 = 3018701) B3018701
theorem B2684225 : Blo 1788095 2684225 := bstep (se 2 (by rfl) ⟨1006584, by rfl⟩ : syracuseStep 2684225 = 2013169) B2013169
theorem B4027715 : Blo 1788095 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B5666129 : Blo 1788095 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B2684243 : Blo 1788095 2684243 := bstep (se 1 (by rfl) ⟨2013182, by rfl⟩ : syracuseStep 2684243 = 4026365) B4026365
theorem B2684273 : Blo 1788095 2684273 := bstep (se 2 (by rfl) ⟨1006602, by rfl⟩ : syracuseStep 2684273 = 2013205) B2013205
theorem B2684291 : Blo 1788095 2684291 := bstep (se 1 (by rfl) ⟨2013218, by rfl⟩ : syracuseStep 2684291 = 4026437) B4026437
theorem B3822979 : Blo 1788095 3822979 := bstep (se 1 (by rfl) ⟨2867234, by rfl⟩ : syracuseStep 3822979 = 5734469) B5734469
theorem B20387213 : Blo 1788095 20387213 := bstep (se 3 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 20387213 = 7645205) B7645205
theorem B3020179 : Blo 1788095 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B2684321 : Blo 1788095 2684321 := bstep (se 2 (by rfl) ⟨1006620, by rfl⟩ : syracuseStep 2684321 = 2013241) B2013241
theorem B2684339 : Blo 1788095 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B2012611 : Blo 1788095 2012611 := bstep (se 1 (by rfl) ⟨1509458, by rfl⟩ : syracuseStep 2012611 = 3018917) B3018917
theorem B2684369 : Blo 1788095 2684369 := bstep (se 2 (by rfl) ⟨1006638, by rfl⟩ : syracuseStep 2684369 = 2013277) B2013277
theorem B2684387 : Blo 1788095 2684387 := bstep (se 1 (by rfl) ⟨2013290, by rfl⟩ : syracuseStep 2684387 = 4026581) B4026581
theorem B2684417 : Blo 1788095 2684417 := bstep (se 2 (by rfl) ⟨1006656, by rfl⟩ : syracuseStep 2684417 = 2013313) B2013313
theorem B5731843 : Blo 1788095 5731843 := bstep (se 1 (by rfl) ⟨4298882, by rfl⟩ : syracuseStep 5731843 = 8597765) B8597765
theorem B2864659 : Blo 1788095 2864659 := bstep (se 1 (by rfl) ⟨2148494, by rfl⟩ : syracuseStep 2864659 = 4296989) B4296989
theorem B2684435 : Blo 1788095 2684435 := bstep (se 1 (by rfl) ⟨2013326, by rfl⟩ : syracuseStep 2684435 = 4026653) B4026653
theorem B8713763 : Blo 1788095 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B3020321 : Blo 1788095 3020321 := bstep (se 2 (by rfl) ⟨1132620, by rfl⟩ : syracuseStep 3020321 = 2265241) B2265241
theorem B2684465 : Blo 1788095 2684465 := bstep (se 2 (by rfl) ⟨1006674, by rfl⟩ : syracuseStep 2684465 = 2013349) B2013349
theorem B5092931 : Blo 1788095 5092931 := bstep (se 1 (by rfl) ⟨3819698, by rfl⟩ : syracuseStep 5092931 = 7639397) B7639397
theorem B2684483 : Blo 1788095 2684483 := bstep (se 1 (by rfl) ⟨2013362, by rfl⟩ : syracuseStep 2684483 = 4026725) B4026725
theorem B4527697 : Blo 1788095 4527697 := bstep (se 2 (by rfl) ⟨1697886, by rfl⟩ : syracuseStep 4527697 = 3395773) B3395773
theorem B2012755 : Blo 1788095 2012755 := bstep (se 1 (by rfl) ⟨1509566, by rfl⟩ : syracuseStep 2012755 = 3019133) B3019133
theorem B2684513 : Blo 1788095 2684513 := bstep (se 2 (by rfl) ⟨1006692, by rfl⟩ : syracuseStep 2684513 = 2013385) B2013385
theorem B11621987 : Blo 1788095 11621987 := bstep (se 1 (by rfl) ⟨8716490, by rfl⟩ : syracuseStep 11621987 = 17432981) B17432981
theorem B9057905 : Blo 1788095 9057905 := bstep (se 2 (by rfl) ⟨3396714, by rfl⟩ : syracuseStep 9057905 = 6793429) B6793429
theorem B2684531 : Blo 1788095 2684531 := bstep (se 1 (by rfl) ⟨2013398, by rfl⟩ : syracuseStep 2684531 = 4026797) B4026797
theorem B11466373 : Blo 1788095 11466373 := bstep (se 4 (by rfl) ⟨1074972, by rfl⟩ : syracuseStep 11466373 = 2149945) B2149945
theorem B2684561 : Blo 1788095 2684561 := bstep (se 2 (by rfl) ⟨1006710, by rfl⟩ : syracuseStep 2684561 = 2013421) B2013421
theorem B3020449 : Blo 1788095 3020449 := bstep (se 2 (by rfl) ⟨1132668, by rfl⟩ : syracuseStep 3020449 = 2265337) B2265337
theorem B2684579 : Blo 1788095 2684579 := bstep (se 1 (by rfl) ⟨2013434, by rfl⟩ : syracuseStep 2684579 = 4026869) B4026869
theorem B3397315 : Blo 1788095 3397315 := bstep (se 1 (by rfl) ⟨2547986, by rfl⟩ : syracuseStep 3397315 = 5095973) B5095973
theorem B2684609 : Blo 1788095 2684609 := bstep (se 2 (by rfl) ⟨1006728, by rfl⟩ : syracuseStep 2684609 = 2013457) B2013457
theorem B3020483 : Blo 1788095 3020483 := bstep (se 1 (by rfl) ⟨2265362, by rfl⟩ : syracuseStep 3020483 = 4530725) B4530725
theorem B3266257 : Blo 1788095 3266257 := bstep (se 2 (by rfl) ⟨1224846, by rfl⟩ : syracuseStep 3266257 = 2449693) B2449693
theorem B2684627 : Blo 1788095 2684627 := bstep (se 1 (by rfl) ⟨2013470, by rfl⟩ : syracuseStep 2684627 = 4026941) B4026941
theorem B2012899 : Blo 1788095 2012899 := bstep (se 1 (by rfl) ⟨1509674, by rfl⟩ : syracuseStep 2012899 = 3019349) B3019349
theorem B2684657 : Blo 1788095 2684657 := bstep (se 2 (by rfl) ⟨1006746, by rfl⟩ : syracuseStep 2684657 = 2013493) B2013493
theorem B2684675 : Blo 1788095 2684675 := bstep (se 1 (by rfl) ⟨2013506, by rfl⟩ : syracuseStep 2684675 = 4027013) B4027013
theorem B2684705 : Blo 1788095 2684705 := bstep (se 2 (by rfl) ⟨1006764, by rfl⟩ : syracuseStep 2684705 = 2013529) B2013529
theorem B4298545 : Blo 1788095 4298545 := bstep (se 2 (by rfl) ⟨1611954, by rfl⟩ : syracuseStep 4298545 = 3223909) B3223909
theorem B2684723 : Blo 1788095 2684723 := bstep (se 1 (by rfl) ⟨2013542, by rfl⟩ : syracuseStep 2684723 = 4027085) B4027085
theorem B3020611 : Blo 1788095 3020611 := bstep (se 1 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 3020611 = 4530917) B4530917
theorem B2684753 : Blo 1788095 2684753 := bstep (se 2 (by rfl) ⟨1006782, by rfl⟩ : syracuseStep 2684753 = 2013565) B2013565
theorem B4527971 : Blo 1788095 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B2684771 : Blo 1788095 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B6035309 : Blo 1788095 6035309 := bstep (se 3 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 6035309 = 2263241) B2263241
theorem B2013043 : Blo 1788095 2013043 := bstep (se 1 (by rfl) ⟨1509782, by rfl⟩ : syracuseStep 2013043 = 3019565) B3019565
theorem B2684801 : Blo 1788095 2684801 := bstep (se 2 (by rfl) ⟨1006800, by rfl⟩ : syracuseStep 2684801 = 2013601) B2013601
theorem B2684819 : Blo 1788095 2684819 := bstep (se 1 (by rfl) ⟨2013614, by rfl⟩ : syracuseStep 2684819 = 4027229) B4027229
theorem B6035363 : Blo 1788095 6035363 := bstep (se 1 (by rfl) ⟨4526522, by rfl⟩ : syracuseStep 6035363 = 9053045) B9053045
theorem B2684849 : Blo 1788095 2684849 := bstep (se 2 (by rfl) ⟨1006818, by rfl⟩ : syracuseStep 2684849 = 2013637) B2013637
theorem B2684867 : Blo 1788095 2684867 := bstep (se 1 (by rfl) ⟨2013650, by rfl⟩ : syracuseStep 2684867 = 4027301) B4027301
theorem B3020753 : Blo 1788095 3020753 := bstep (se 2 (by rfl) ⟨1132782, by rfl⟩ : syracuseStep 3020753 = 2265565) B2265565
theorem B2684897 : Blo 1788095 2684897 := bstep (se 2 (by rfl) ⟨1006836, by rfl⟩ : syracuseStep 2684897 = 2013673) B2013673
theorem B4298737 : Blo 1788095 4298737 := bstep (se 2 (by rfl) ⟨1612026, by rfl⟩ : syracuseStep 4298737 = 3224053) B3224053
theorem B2684915 : Blo 1788095 2684915 := bstep (se 1 (by rfl) ⟨2013686, by rfl⟩ : syracuseStep 2684915 = 4027373) B4027373
theorem B2013187 : Blo 1788095 2013187 := bstep (se 1 (by rfl) ⟨1509890, by rfl⟩ : syracuseStep 2013187 = 3019781) B3019781
theorem B2684945 : Blo 1788095 2684945 := bstep (se 2 (by rfl) ⟨1006854, by rfl⟩ : syracuseStep 2684945 = 2013709) B2013709
theorem B4528163 : Blo 1788095 4528163 := bstep (se 1 (by rfl) ⟨3396122, by rfl⟩ : syracuseStep 4528163 = 6792245) B6792245
theorem B2684963 : Blo 1788095 2684963 := bstep (se 1 (by rfl) ⟨2013722, by rfl⟩ : syracuseStep 2684963 = 4027445) B4027445
theorem B2684993 : Blo 1788095 2684993 := bstep (se 2 (by rfl) ⟨1006872, by rfl⟩ : syracuseStep 2684993 = 2013745) B2013745
theorem B2685011 : Blo 1788095 2685011 := bstep (se 1 (by rfl) ⟨2013758, by rfl⟩ : syracuseStep 2685011 = 4027517) B4027517
theorem B2685041 : Blo 1788095 2685041 := bstep (se 2 (by rfl) ⟨1006890, by rfl⟩ : syracuseStep 2685041 = 2013781) B2013781
theorem B3397763 : Blo 1788095 3397763 := bstep (se 1 (by rfl) ⟨2548322, by rfl⟩ : syracuseStep 3397763 = 5096645) B5096645
theorem B2685059 : Blo 1788095 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B2013331 : Blo 1788095 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B2685089 : Blo 1788095 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B2906275 : Blo 1788095 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B6035633 : Blo 1788095 6035633 := bstep (se 2 (by rfl) ⟨2263362, by rfl⟩ : syracuseStep 6035633 = 4526725) B4526725
theorem B2685107 : Blo 1788095 2685107 := bstep (se 1 (by rfl) ⟨2013830, by rfl⟩ : syracuseStep 2685107 = 4027661) B4027661
theorem B5306573 : Blo 1788095 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B2685137 : Blo 1788095 2685137 := bstep (se 2 (by rfl) ⟨1006926, by rfl⟩ : syracuseStep 2685137 = 2013853) B2013853
theorem B2865377 : Blo 1788095 2865377 := bstep (se 2 (by rfl) ⟨1074516, by rfl⟩ : syracuseStep 2865377 = 2149033) B2149033
theorem B2013475 : Blo 1788095 2013475 := bstep (se 1 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 2013475 = 3020213) B3020213
theorem B2545987 : Blo 1788095 2545987 := bstep (se 1 (by rfl) ⟨1909490, by rfl⟩ : syracuseStep 2545987 = 3818981) B3818981
theorem B11622797 : Blo 1788095 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B3398051 : Blo 1788095 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2013619 : Blo 1788095 2013619 := bstep (se 1 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 2013619 = 3020429) B3020429
theorem B2865665 : Blo 1788095 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B2013763 : Blo 1788095 2013763 := bstep (se 1 (by rfl) ⟨1510322, by rfl⟩ : syracuseStep 2013763 = 3020645) B3020645
theorem B6036173 : Blo 1788095 6036173 := bstep (se 3 (by rfl) ⟨1131782, by rfl⟩ : syracuseStep 6036173 = 2263565) B2263565
theorem B2865889 : Blo 1788095 2865889 := bstep (se 2 (by rfl) ⟨1074708, by rfl⟩ : syracuseStep 2865889 = 2149417) B2149417
theorem B6036227 : Blo 1788095 6036227 := bstep (se 1 (by rfl) ⟨4527170, by rfl⟩ : syracuseStep 6036227 = 9054341) B9054341
theorem B5094161 : Blo 1788095 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B21756869 : Blo 1788095 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B6446029 : Blo 1788095 6446029 := bstep (se 3 (by rfl) ⟨1208630, by rfl⟩ : syracuseStep 6446029 = 2417261) B2417261
theorem B6888397 : Blo 1788095 6888397 := bstep (se 3 (by rfl) ⟨1291574, by rfl⟩ : syracuseStep 6888397 = 2583149) B2583149
theorem B4529105 : Blo 1788095 4529105 := bstep (se 2 (by rfl) ⟨1698414, by rfl⟩ : syracuseStep 4529105 = 3396829) B3396829
theorem B7642097 : Blo 1788095 7642097 := bstep (se 2 (by rfl) ⟨2865786, by rfl⟩ : syracuseStep 7642097 = 5731573) B5731573
theorem B4529155 : Blo 1788095 4529155 := bstep (se 1 (by rfl) ⟨3396866, by rfl⟩ : syracuseStep 4529155 = 6793733) B6793733
theorem B6036497 : Blo 1788095 6036497 := bstep (se 2 (by rfl) ⟨2263686, by rfl⟩ : syracuseStep 6036497 = 4527373) B4527373
theorem B9059363 : Blo 1788095 9059363 := bstep (se 1 (by rfl) ⟨6794522, by rfl⟩ : syracuseStep 9059363 = 13589045) B13589045
theorem B5733443 : Blo 1788095 5733443 := bstep (se 1 (by rfl) ⟨4300082, by rfl⟩ : syracuseStep 5733443 = 8600165) B8600165
theorem B4078691 : Blo 1788095 4078691 := bstep (se 1 (by rfl) ⟨3059018, by rfl⟩ : syracuseStep 4078691 = 6118037) B6118037
theorem B12901517 : Blo 1788095 12901517 := bstep (se 3 (by rfl) ⟨2419034, by rfl⟩ : syracuseStep 12901517 = 4838069) B4838069
theorem B4529297 : Blo 1788095 4529297 := bstep (se 2 (by rfl) ⟨1698486, by rfl⟩ : syracuseStep 4529297 = 3396973) B3396973
theorem B11459789 : Blo 1788095 11459789 := bstep (se 3 (by rfl) ⟨2148710, by rfl⟩ : syracuseStep 11459789 = 4297421) B4297421
theorem B6536419 : Blo 1788095 6536419 := bstep (se 1 (by rfl) ⟨4902314, by rfl⟩ : syracuseStep 6536419 = 9804629) B9804629
theorem B6790499 : Blo 1788095 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B6790513 : Blo 1788095 6790513 := bstep (se 2 (by rfl) ⟨2546442, by rfl⟩ : syracuseStep 6790513 = 5092885) B5092885
theorem B11460017 : Blo 1788095 11460017 := bstep (se 2 (by rfl) ⟨4297506, by rfl⟩ : syracuseStep 11460017 = 8595013) B8595013
theorem B2547121 : Blo 1788095 2547121 := bstep (se 2 (by rfl) ⟨955170, by rfl⟩ : syracuseStep 2547121 = 1910341) B1910341
theorem B2178499 : Blo 1788095 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B2547217 : Blo 1788095 2547217 := bstep (se 2 (by rfl) ⟨955206, by rfl⟩ : syracuseStep 2547217 = 1910413) B1910413
theorem B6037037 : Blo 1788095 6037037 := bstep (se 3 (by rfl) ⟨1131944, by rfl⟩ : syracuseStep 6037037 = 2263889) B2263889
theorem B6037091 : Blo 1788095 6037091 := bstep (se 1 (by rfl) ⟨4527818, by rfl⟩ : syracuseStep 6037091 = 9055637) B9055637
theorem B17186417 : Blo 1788095 17186417 := bstep (se 2 (by rfl) ⟨6444906, by rfl⟩ : syracuseStep 17186417 = 12889813) B12889813
theorem B20381381 : Blo 1788095 20381381 := bstep (se 4 (by rfl) ⟨1910754, by rfl⟩ : syracuseStep 20381381 = 3821509) B3821509
theorem B7257869 : Blo 1788095 7257869 := bstep (se 3 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 7257869 = 2721701) B2721701
theorem B6446897 : Blo 1788095 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B9060173 : Blo 1788095 9060173 := bstep (se 3 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 9060173 = 3397565) B3397565
theorem B5439313 : Blo 1788095 5439313 := bstep (se 2 (by rfl) ⟨2039742, by rfl⟩ : syracuseStep 5439313 = 4079485) B4079485
theorem B6037361 : Blo 1788095 6037361 := bstep (se 2 (by rfl) ⟨2264010, by rfl⟩ : syracuseStep 6037361 = 4528021) B4528021
theorem B4079587 : Blo 1788095 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B5234669 : Blo 1788095 5234669 := bstep (se 3 (by rfl) ⟨981500, by rfl⟩ : syracuseStep 5234669 = 1963001) B1963001
theorem B6119489 : Blo 1788095 6119489 := bstep (se 2 (by rfl) ⟨2294808, by rfl⟩ : syracuseStep 6119489 = 4589617) B4589617
theorem B9052235 : Blo 1788095 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B2547787 : Blo 1788095 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B27549877 : Blo 1788095 27549877 := bstep (se 5 (by rfl) ⟨1291400, by rfl⟩ : syracuseStep 27549877 = 2582801) B2582801
theorem B3875033 : Blo 1788095 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B3440983 : Blo 1788095 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B13590989 : Blo 1788095 13590989 := bstep (se 3 (by rfl) ⟨2548310, by rfl⟩ : syracuseStep 13590989 = 5096621) B5096621
theorem B20374091 : Blo 1788095 20374091 := bstep (se 1 (by rfl) ⟨15280568, by rfl⟩ : syracuseStep 20374091 = 30561137) B30561137
theorem B5096029 : Blo 1788095 5096029 := bstep (se 3 (by rfl) ⟨955505, by rfl⟩ : syracuseStep 5096029 = 1911011) B1911011
theorem B2417305 : Blo 1788095 2417305 := bstep (se 2 (by rfl) ⟨906489, by rfl⟩ : syracuseStep 2417305 = 1812979) B1812979
theorem B3777419 : Blo 1788095 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B5096371 : Blo 1788095 5096371 := bstep (se 1 (by rfl) ⟨3822278, by rfl⟩ : syracuseStep 5096371 = 7644557) B7644557
theorem B13591475 : Blo 1788095 13591475 := bstep (se 1 (by rfl) ⟨10193606, by rfl⟩ : syracuseStep 13591475 = 20387213) B20387213
theorem B4023233 : Blo 1788095 4023233 := bstep (se 2 (by rfl) ⟨1508712, by rfl⟩ : syracuseStep 4023233 = 3017425) B3017425
theorem B5809175 : Blo 1788095 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B17187875 : Blo 1788095 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B6038603 : Blo 1788095 6038603 := bstep (se 1 (by rfl) ⟨4528952, by rfl⟩ : syracuseStep 6038603 = 9057905) B9057905
theorem B2720855 : Blo 1788095 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B9061469 : Blo 1788095 9061469 := bstep (se 3 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 9061469 = 3398051) B3398051
theorem B4080755 : Blo 1788095 4080755 := bstep (se 1 (by rfl) ⟨3060566, by rfl⟩ : syracuseStep 4080755 = 6121133) B6121133
theorem B4023449 : Blo 1788095 4023449 := bstep (se 2 (by rfl) ⟨1508793, by rfl⟩ : syracuseStep 4023449 = 3017587) B3017587
theorem B4023539 : Blo 1788095 4023539 := bstep (se 1 (by rfl) ⟨3017654, by rfl⟩ : syracuseStep 4023539 = 6035309) B6035309
theorem B8594705 : Blo 1788095 8594705 := bstep (se 2 (by rfl) ⟨3223014, by rfl⟩ : syracuseStep 8594705 = 6446029) B6446029
theorem B9184529 : Blo 1788095 9184529 := bstep (se 2 (by rfl) ⟨3444198, by rfl⟩ : syracuseStep 9184529 = 6888397) B6888397
theorem B4023575 : Blo 1788095 4023575 := bstep (se 1 (by rfl) ⟨3017681, by rfl⟩ : syracuseStep 4023575 = 6035363) B6035363
theorem B6038873 : Blo 1788095 6038873 := bstep (se 2 (by rfl) ⟨2264577, by rfl⟩ : syracuseStep 6038873 = 4529155) B4529155
theorem B8717719 : Blo 1788095 8717719 := bstep (se 1 (by rfl) ⟨6538289, by rfl⟩ : syracuseStep 8717719 = 13076579) B13076579
theorem B4023755 : Blo 1788095 4023755 := bstep (se 1 (by rfl) ⟨3017816, by rfl⟩ : syracuseStep 4023755 = 6035633) B6035633
theorem B1910251 : Blo 1788095 1910251 := bstep (se 1 (by rfl) ⟨1432688, by rfl⟩ : syracuseStep 1910251 = 2865377) B2865377
theorem B4023809 : Blo 1788095 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B15492653 : Blo 1788095 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B4024025 : Blo 1788095 4024025 := bstep (se 2 (by rfl) ⟨1509009, by rfl⟩ : syracuseStep 4024025 = 3018019) B3018019
theorem B6448913 : Blo 1788095 6448913 := bstep (se 2 (by rfl) ⟨2418342, by rfl⟩ : syracuseStep 6448913 = 4836685) B4836685
theorem B4024115 : Blo 1788095 4024115 := bstep (se 1 (by rfl) ⟨3018086, by rfl⟩ : syracuseStep 4024115 = 6036173) B6036173
theorem B9054017 : Blo 1788095 9054017 := bstep (se 2 (by rfl) ⟨3395256, by rfl⟩ : syracuseStep 9054017 = 6790513) B6790513
theorem B4024151 : Blo 1788095 4024151 := bstep (se 1 (by rfl) ⟨3018113, by rfl⟩ : syracuseStep 4024151 = 6036227) B6036227
theorem B5097305 : Blo 1788095 5097305 := bstep (se 2 (by rfl) ⟨1911489, by rfl⟩ : syracuseStep 5097305 = 3822979) B3822979
theorem B4024331 : Blo 1788095 4024331 := bstep (se 1 (by rfl) ⟨3018248, by rfl⟩ : syracuseStep 4024331 = 6036497) B6036497
theorem B6039575 : Blo 1788095 6039575 := bstep (se 1 (by rfl) ⟨4529681, by rfl⟩ : syracuseStep 6039575 = 9059363) B9059363
theorem B3819545 : Blo 1788095 3819545 := bstep (se 2 (by rfl) ⟨1432329, by rfl⟩ : syracuseStep 3819545 = 2864659) B2864659
theorem B4024385 : Blo 1788095 4024385 := bstep (se 2 (by rfl) ⟨1509144, by rfl⟩ : syracuseStep 4024385 = 3018289) B3018289
theorem B15288497 : Blo 1788095 15288497 := bstep (se 2 (by rfl) ⟨5733186, by rfl⟩ : syracuseStep 15288497 = 11466373) B11466373
theorem B1788107 : Blo 1788095 1788107 := bstep (se 1 (by rfl) ⟨1341080, by rfl⟩ : syracuseStep 1788107 = 2682161) B2682161
theorem B1788119 : Blo 1788095 1788119 := bstep (se 1 (by rfl) ⟨1341089, by rfl⟩ : syracuseStep 1788119 = 2682179) B2682179
theorem B1788139 : Blo 1788095 1788139 := bstep (se 1 (by rfl) ⟨1341104, by rfl⟩ : syracuseStep 1788139 = 2682209) B2682209
theorem B1788151 : Blo 1788095 1788151 := bstep (se 1 (by rfl) ⟨1341113, by rfl⟩ : syracuseStep 1788151 = 2682227) B2682227
theorem B1788171 : Blo 1788095 1788171 := bstep (se 1 (by rfl) ⟨1341128, by rfl⟩ : syracuseStep 1788171 = 2682257) B2682257
theorem B1788183 : Blo 1788095 1788183 := bstep (se 1 (by rfl) ⟨1341137, by rfl⟩ : syracuseStep 1788183 = 2682275) B2682275
theorem B4024601 : Blo 1788095 4024601 := bstep (se 2 (by rfl) ⟨1509225, by rfl⟩ : syracuseStep 4024601 = 3018451) B3018451
theorem B1788203 : Blo 1788095 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B1788215 : Blo 1788095 1788215 := bstep (se 1 (by rfl) ⟨1341161, by rfl⟩ : syracuseStep 1788215 = 2682323) B2682323
theorem B1788235 : Blo 1788095 1788235 := bstep (se 1 (by rfl) ⟨1341176, by rfl⟩ : syracuseStep 1788235 = 2682353) B2682353
theorem B11618635 : Blo 1788095 11618635 := bstep (se 1 (by rfl) ⟨8713976, by rfl⟩ : syracuseStep 11618635 = 17427953) B17427953
theorem B1788247 : Blo 1788095 1788247 := bstep (se 1 (by rfl) ⟨1341185, by rfl⟩ : syracuseStep 1788247 = 2682371) B2682371
theorem B13592933 : Blo 1788095 13592933 := bstep (se 4 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 13592933 = 2548675) B2548675
theorem B1788267 : Blo 1788095 1788267 := bstep (se 1 (by rfl) ⟨1341200, by rfl⟩ : syracuseStep 1788267 = 2682401) B2682401
theorem B4024691 : Blo 1788095 4024691 := bstep (se 1 (by rfl) ⟨3018518, by rfl⟩ : syracuseStep 4024691 = 6037037) B6037037
theorem B1788279 : Blo 1788095 1788279 := bstep (se 1 (by rfl) ⟨1341209, by rfl⟩ : syracuseStep 1788279 = 2682419) B2682419
theorem B1788299 : Blo 1788095 1788299 := bstep (se 1 (by rfl) ⟨1341224, by rfl⟩ : syracuseStep 1788299 = 2682449) B2682449
theorem B1788311 : Blo 1788095 1788311 := bstep (se 1 (by rfl) ⟨1341233, by rfl⟩ : syracuseStep 1788311 = 2682467) B2682467
theorem B4024727 : Blo 1788095 4024727 := bstep (se 1 (by rfl) ⟨3018545, by rfl⟩ : syracuseStep 4024727 = 6037091) B6037091
theorem B1788331 : Blo 1788095 1788331 := bstep (se 1 (by rfl) ⟨1341248, by rfl⟩ : syracuseStep 1788331 = 2682497) B2682497
theorem B3819955 : Blo 1788095 3819955 := bstep (se 1 (by rfl) ⟨2864966, by rfl⟩ : syracuseStep 3819955 = 5729933) B5729933
theorem B1788343 : Blo 1788095 1788343 := bstep (se 1 (by rfl) ⟨1341257, by rfl⟩ : syracuseStep 1788343 = 2682515) B2682515
theorem B7252417 : Blo 1788095 7252417 := bstep (se 2 (by rfl) ⟨2719656, by rfl⟩ : syracuseStep 7252417 = 5439313) B5439313
theorem B1788363 : Blo 1788095 1788363 := bstep (se 1 (by rfl) ⟨1341272, by rfl⟩ : syracuseStep 1788363 = 2682545) B2682545
theorem B2148811 : Blo 1788095 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B1788375 : Blo 1788095 1788375 := bstep (se 1 (by rfl) ⟨1341281, by rfl⟩ : syracuseStep 1788375 = 2682563) B2682563
theorem B1788395 : Blo 1788095 1788395 := bstep (se 1 (by rfl) ⟨1341296, by rfl⟩ : syracuseStep 1788395 = 2682593) B2682593
theorem B1788407 : Blo 1788095 1788407 := bstep (se 1 (by rfl) ⟨1341305, by rfl⟩ : syracuseStep 1788407 = 2682611) B2682611
theorem B1788427 : Blo 1788095 1788427 := bstep (se 1 (by rfl) ⟨1341320, by rfl⟩ : syracuseStep 1788427 = 2682641) B2682641
theorem B45861389 : Blo 1788095 45861389 := bstep (se 3 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 45861389 = 17198021) B17198021
theorem B1788439 : Blo 1788095 1788439 := bstep (se 1 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 1788439 = 2682659) B2682659
theorem B1788459 : Blo 1788095 1788459 := bstep (se 1 (by rfl) ⟨1341344, by rfl⟩ : syracuseStep 1788459 = 2682689) B2682689
theorem B6040115 : Blo 1788095 6040115 := bstep (se 1 (by rfl) ⟨4530086, by rfl⟩ : syracuseStep 6040115 = 9060173) B9060173
theorem B1788471 : Blo 1788095 1788471 := bstep (se 1 (by rfl) ⟨1341353, by rfl⟩ : syracuseStep 1788471 = 2682707) B2682707
theorem B1788491 : Blo 1788095 1788491 := bstep (se 1 (by rfl) ⟨1341368, by rfl⟩ : syracuseStep 1788491 = 2682737) B2682737
theorem B4024907 : Blo 1788095 4024907 := bstep (se 1 (by rfl) ⟨3018680, by rfl⟩ : syracuseStep 4024907 = 6037361) B6037361
theorem B1788503 : Blo 1788095 1788503 := bstep (se 1 (by rfl) ⟨1341377, by rfl⟩ : syracuseStep 1788503 = 2682755) B2682755
theorem B1788523 : Blo 1788095 1788523 := bstep (se 1 (by rfl) ⟨1341392, by rfl⟩ : syracuseStep 1788523 = 2682785) B2682785
theorem B1788535 : Blo 1788095 1788535 := bstep (se 1 (by rfl) ⟨1341401, by rfl⟩ : syracuseStep 1788535 = 2682803) B2682803
theorem B4024961 : Blo 1788095 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B1788555 : Blo 1788095 1788555 := bstep (se 1 (by rfl) ⟨1341416, by rfl⟩ : syracuseStep 1788555 = 2682833) B2682833
theorem B1788567 : Blo 1788095 1788567 := bstep (se 1 (by rfl) ⟨1341425, by rfl⟩ : syracuseStep 1788567 = 2682851) B2682851
theorem B1788587 : Blo 1788095 1788587 := bstep (se 1 (by rfl) ⟨1341440, by rfl⟩ : syracuseStep 1788587 = 2682881) B2682881
theorem B6793901 : Blo 1788095 6793901 := bstep (se 3 (by rfl) ⟨1273856, by rfl⟩ : syracuseStep 6793901 = 2547713) B2547713
theorem B3820211 : Blo 1788095 3820211 := bstep (se 1 (by rfl) ⟨2865158, by rfl⟩ : syracuseStep 3820211 = 5730317) B5730317
theorem B1788599 : Blo 1788095 1788599 := bstep (se 1 (by rfl) ⟨1341449, by rfl⟩ : syracuseStep 1788599 = 2682899) B2682899
theorem B7645889 : Blo 1788095 7645889 := bstep (se 2 (by rfl) ⟨2867208, by rfl⟩ : syracuseStep 7645889 = 5734417) B5734417
theorem B1788619 : Blo 1788095 1788619 := bstep (se 1 (by rfl) ⟨1341464, by rfl⟩ : syracuseStep 1788619 = 2682929) B2682929
theorem B6449867 : Blo 1788095 6449867 := bstep (se 1 (by rfl) ⟨4837400, by rfl⟩ : syracuseStep 6449867 = 9674801) B9674801
theorem B1788631 : Blo 1788095 1788631 := bstep (se 1 (by rfl) ⟨1341473, by rfl⟩ : syracuseStep 1788631 = 2682947) B2682947
theorem B1788651 : Blo 1788095 1788651 := bstep (se 1 (by rfl) ⟨1341488, by rfl⟩ : syracuseStep 1788651 = 2682977) B2682977
theorem B1788663 : Blo 1788095 1788663 := bstep (se 1 (by rfl) ⟨1341497, by rfl⟩ : syracuseStep 1788663 = 2682995) B2682995
theorem B8162051 : Blo 1788095 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B13585157 : Blo 1788095 13585157 := bstep (se 4 (by rfl) ⟨1273608, by rfl⟩ : syracuseStep 13585157 = 2547217) B2547217
theorem B1788683 : Blo 1788095 1788683 := bstep (se 1 (by rfl) ⟨1341512, by rfl⟩ : syracuseStep 1788683 = 2683025) B2683025
theorem B1788695 : Blo 1788095 1788695 := bstep (se 1 (by rfl) ⟨1341521, by rfl⟩ : syracuseStep 1788695 = 2683043) B2683043
theorem B1788715 : Blo 1788095 1788715 := bstep (se 1 (by rfl) ⟨1341536, by rfl⟩ : syracuseStep 1788715 = 2683073) B2683073
theorem B3222323 : Blo 1788095 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B5729075 : Blo 1788095 5729075 := bstep (se 1 (by rfl) ⟨4296806, by rfl⟩ : syracuseStep 5729075 = 8593613) B8593613
theorem B1788727 : Blo 1788095 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B6040385 : Blo 1788095 6040385 := bstep (se 2 (by rfl) ⟨2265144, by rfl⟩ : syracuseStep 6040385 = 4530289) B4530289
theorem B1788747 : Blo 1788095 1788747 := bstep (se 1 (by rfl) ⟨1341560, by rfl⟩ : syracuseStep 1788747 = 2683121) B2683121
theorem B4082507 : Blo 1788095 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B13593419 : Blo 1788095 13593419 := bstep (se 1 (by rfl) ⟨10195064, by rfl⟩ : syracuseStep 13593419 = 20390129) B20390129
theorem B1788759 : Blo 1788095 1788759 := bstep (se 1 (by rfl) ⟨1341569, by rfl⟩ : syracuseStep 1788759 = 2683139) B2683139
theorem B4025177 : Blo 1788095 4025177 := bstep (se 2 (by rfl) ⟨1509441, by rfl⟩ : syracuseStep 4025177 = 3018883) B3018883
theorem B15289181 : Blo 1788095 15289181 := bstep (se 3 (by rfl) ⟨2866721, by rfl⟩ : syracuseStep 15289181 = 5733443) B5733443
theorem B1788779 : Blo 1788095 1788779 := bstep (se 1 (by rfl) ⟨1341584, by rfl⟩ : syracuseStep 1788779 = 2683169) B2683169
theorem B1788791 : Blo 1788095 1788791 := bstep (se 1 (by rfl) ⟨1341593, by rfl⟩ : syracuseStep 1788791 = 2683187) B2683187
theorem B1788811 : Blo 1788095 1788811 := bstep (se 1 (by rfl) ⟨1341608, by rfl⟩ : syracuseStep 1788811 = 2683217) B2683217
theorem B1788823 : Blo 1788095 1788823 := bstep (se 1 (by rfl) ⟨1341617, by rfl⟩ : syracuseStep 1788823 = 2683235) B2683235
theorem B1788843 : Blo 1788095 1788843 := bstep (se 1 (by rfl) ⟨1341632, by rfl⟩ : syracuseStep 1788843 = 2683265) B2683265
theorem B4025267 : Blo 1788095 4025267 := bstep (se 1 (by rfl) ⟨3018950, by rfl⟩ : syracuseStep 4025267 = 6037901) B6037901
theorem B1788855 : Blo 1788095 1788855 := bstep (se 1 (by rfl) ⟨1341641, by rfl⟩ : syracuseStep 1788855 = 2683283) B2683283
theorem B3017675 : Blo 1788095 3017675 := bstep (se 1 (by rfl) ⟨2263256, by rfl⟩ : syracuseStep 3017675 = 4526513) B4526513
theorem B1788875 : Blo 1788095 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B1788887 : Blo 1788095 1788887 := bstep (se 1 (by rfl) ⟨1341665, by rfl⟩ : syracuseStep 1788887 = 2683331) B2683331
theorem B4025303 : Blo 1788095 4025303 := bstep (se 1 (by rfl) ⟨3018977, by rfl⟩ : syracuseStep 4025303 = 6037955) B6037955
theorem B1788907 : Blo 1788095 1788907 := bstep (se 1 (by rfl) ⟨1341680, by rfl⟩ : syracuseStep 1788907 = 2683361) B2683361
theorem B1788919 : Blo 1788095 1788919 := bstep (se 1 (by rfl) ⟨1341689, by rfl⟩ : syracuseStep 1788919 = 2683379) B2683379
theorem B1788939 : Blo 1788095 1788939 := bstep (se 1 (by rfl) ⟨1341704, by rfl⟩ : syracuseStep 1788939 = 2683409) B2683409
theorem B1788951 : Blo 1788095 1788951 := bstep (se 1 (by rfl) ⟨1341713, by rfl⟩ : syracuseStep 1788951 = 2683427) B2683427
theorem B7646231 : Blo 1788095 7646231 := bstep (se 1 (by rfl) ⟨5734673, by rfl⟩ : syracuseStep 7646231 = 11469347) B11469347
theorem B1788971 : Blo 1788095 1788971 := bstep (se 1 (by rfl) ⟨1341728, by rfl⟩ : syracuseStep 1788971 = 2683457) B2683457
theorem B1813547 : Blo 1788095 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B1788983 : Blo 1788095 1788983 := bstep (se 1 (by rfl) ⟨1341737, by rfl⟩ : syracuseStep 1788983 = 2683475) B2683475
theorem B3017803 : Blo 1788095 3017803 := bstep (se 1 (by rfl) ⟨2263352, by rfl⟩ : syracuseStep 3017803 = 4526705) B4526705
theorem B1789003 : Blo 1788095 1789003 := bstep (se 1 (by rfl) ⟨1341752, by rfl⟩ : syracuseStep 1789003 = 2683505) B2683505
theorem B1789015 : Blo 1788095 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B3394649 : Blo 1788095 3394649 := bstep (se 2 (by rfl) ⟨1272993, by rfl⟩ : syracuseStep 3394649 = 2545987) B2545987
theorem B7253081 : Blo 1788095 7253081 := bstep (se 2 (by rfl) ⟨2719905, by rfl⟩ : syracuseStep 7253081 = 5439811) B5439811
theorem B1789035 : Blo 1788095 1789035 := bstep (se 1 (by rfl) ⟨1341776, by rfl⟩ : syracuseStep 1789035 = 2683553) B2683553
theorem B1789047 : Blo 1788095 1789047 := bstep (se 1 (by rfl) ⟨1341785, by rfl⟩ : syracuseStep 1789047 = 2683571) B2683571
theorem B2264203 : Blo 1788095 2264203 := bstep (se 1 (by rfl) ⟨1698152, by rfl⟩ : syracuseStep 2264203 = 3396305) B3396305
theorem B1789067 : Blo 1788095 1789067 := bstep (se 1 (by rfl) ⟨1341800, by rfl⟩ : syracuseStep 1789067 = 2683601) B2683601
theorem B4025483 : Blo 1788095 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B1789079 : Blo 1788095 1789079 := bstep (se 1 (by rfl) ⟨1341809, by rfl⟩ : syracuseStep 1789079 = 2683619) B2683619
theorem B1790059 : Blo 1788095 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B1789099 : Blo 1788095 1789099 := bstep (se 1 (by rfl) ⟨1341824, by rfl⟩ : syracuseStep 1789099 = 2683649) B2683649
theorem B8162477 : Blo 1788095 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B1789111 : Blo 1788095 1789111 := bstep (se 1 (by rfl) ⟨1341833, by rfl⟩ : syracuseStep 1789111 = 2683667) B2683667
theorem B4025537 : Blo 1788095 4025537 := bstep (se 2 (by rfl) ⟨1509576, by rfl⟩ : syracuseStep 4025537 = 3019153) B3019153
theorem B1789131 : Blo 1788095 1789131 := bstep (se 1 (by rfl) ⟨1341848, by rfl⟩ : syracuseStep 1789131 = 2683697) B2683697
theorem B14150861 : Blo 1788095 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1789143 : Blo 1788095 1789143 := bstep (se 1 (by rfl) ⟨1341857, by rfl⟩ : syracuseStep 1789143 = 2683715) B2683715
theorem B3017945 : Blo 1788095 3017945 := bstep (se 2 (by rfl) ⟨1131729, by rfl⟩ : syracuseStep 3017945 = 2263459) B2263459
theorem B1789163 : Blo 1788095 1789163 := bstep (se 1 (by rfl) ⟨1341872, by rfl⟩ : syracuseStep 1789163 = 2683745) B2683745
theorem B1789175 : Blo 1788095 1789175 := bstep (se 1 (by rfl) ⟨1341881, by rfl⟩ : syracuseStep 1789175 = 2683763) B2683763
theorem B1789195 : Blo 1788095 1789195 := bstep (se 1 (by rfl) ⟨1341896, by rfl⟩ : syracuseStep 1789195 = 2683793) B2683793
theorem B1789207 : Blo 1788095 1789207 := bstep (se 1 (by rfl) ⟨1341905, by rfl⟩ : syracuseStep 1789207 = 2683811) B2683811
theorem B1789227 : Blo 1788095 1789227 := bstep (se 1 (by rfl) ⟨1341920, by rfl⟩ : syracuseStep 1789227 = 2683841) B2683841
theorem B1789239 : Blo 1788095 1789239 := bstep (se 1 (by rfl) ⟨1341929, by rfl⟩ : syracuseStep 1789239 = 2683859) B2683859
theorem B1789259 : Blo 1788095 1789259 := bstep (se 1 (by rfl) ⟨1341944, by rfl⟩ : syracuseStep 1789259 = 2683889) B2683889
theorem B1789271 : Blo 1788095 1789271 := bstep (se 1 (by rfl) ⟨1341953, by rfl⟩ : syracuseStep 1789271 = 2683907) B2683907
theorem B3018073 : Blo 1788095 3018073 := bstep (se 2 (by rfl) ⟨1131777, by rfl⟩ : syracuseStep 3018073 = 2263555) B2263555
theorem B6040925 : Blo 1788095 6040925 := bstep (se 3 (by rfl) ⟨1132673, by rfl⟩ : syracuseStep 6040925 = 2265347) B2265347
theorem B1789291 : Blo 1788095 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B1789303 : Blo 1788095 1789303 := bstep (se 1 (by rfl) ⟨1341977, by rfl⟩ : syracuseStep 1789303 = 2683955) B2683955
theorem B2682251 : Blo 1788095 2682251 := bstep (se 1 (by rfl) ⟨2011688, by rfl⟩ : syracuseStep 2682251 = 4023377) B4023377
theorem B1789323 : Blo 1788095 1789323 := bstep (se 1 (by rfl) ⟨1341992, by rfl⟩ : syracuseStep 1789323 = 2683985) B2683985
theorem B2682263 : Blo 1788095 2682263 := bstep (se 1 (by rfl) ⟨2011697, by rfl⟩ : syracuseStep 2682263 = 4023395) B4023395
theorem B1789335 : Blo 1788095 1789335 := bstep (se 1 (by rfl) ⟨1342001, by rfl⟩ : syracuseStep 1789335 = 2684003) B2684003
theorem B4025753 : Blo 1788095 4025753 := bstep (se 2 (by rfl) ⟨1509657, by rfl⟩ : syracuseStep 4025753 = 3019315) B3019315
theorem B1789355 : Blo 1788095 1789355 := bstep (se 1 (by rfl) ⟨1342016, by rfl⟩ : syracuseStep 1789355 = 2684033) B2684033
theorem B6794675 : Blo 1788095 6794675 := bstep (se 1 (by rfl) ⟨5096006, by rfl⟩ : syracuseStep 6794675 = 10192013) B10192013
theorem B1789367 : Blo 1788095 1789367 := bstep (se 1 (by rfl) ⟨1342025, by rfl⟩ : syracuseStep 1789367 = 2684051) B2684051
theorem B1789387 : Blo 1788095 1789387 := bstep (se 1 (by rfl) ⟨1342040, by rfl⟩ : syracuseStep 1789387 = 2684081) B2684081
theorem B1789399 : Blo 1788095 1789399 := bstep (se 1 (by rfl) ⟨1342049, by rfl⟩ : syracuseStep 1789399 = 2684099) B2684099
theorem B2682329 : Blo 1788095 2682329 := bstep (se 2 (by rfl) ⟨1005873, by rfl⟩ : syracuseStep 2682329 = 2011747) B2011747
theorem B5729753 : Blo 1788095 5729753 := bstep (se 2 (by rfl) ⟨2148657, by rfl⟩ : syracuseStep 5729753 = 4297315) B4297315
theorem B1789419 : Blo 1788095 1789419 := bstep (se 1 (by rfl) ⟨1342064, by rfl⟩ : syracuseStep 1789419 = 2684129) B2684129
theorem B4025843 : Blo 1788095 4025843 := bstep (se 1 (by rfl) ⟨3019382, by rfl⟩ : syracuseStep 4025843 = 6038765) B6038765
theorem B1789431 : Blo 1788095 1789431 := bstep (se 1 (by rfl) ⟨1342073, by rfl⟩ : syracuseStep 1789431 = 2684147) B2684147
theorem B1789451 : Blo 1788095 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B4025879 : Blo 1788095 4025879 := bstep (se 1 (by rfl) ⟨3019409, by rfl⟩ : syracuseStep 4025879 = 6038819) B6038819
theorem B1789463 : Blo 1788095 1789463 := bstep (se 1 (by rfl) ⟨1342097, by rfl⟩ : syracuseStep 1789463 = 2684195) B2684195
theorem B1789483 : Blo 1788095 1789483 := bstep (se 1 (by rfl) ⟨1342112, by rfl⟩ : syracuseStep 1789483 = 2684225) B2684225
theorem B12242477 : Blo 1788095 12242477 := bstep (se 3 (by rfl) ⟨2295464, by rfl⟩ : syracuseStep 12242477 = 4590929) B4590929
theorem B1789495 : Blo 1788095 1789495 := bstep (se 1 (by rfl) ⟨1342121, by rfl⟩ : syracuseStep 1789495 = 2684243) B2684243
theorem B10194497 : Blo 1788095 10194497 := bstep (se 2 (by rfl) ⟨3822936, by rfl⟩ : syracuseStep 10194497 = 7645873) B7645873
theorem B2682443 : Blo 1788095 2682443 := bstep (se 1 (by rfl) ⟨2011832, by rfl⟩ : syracuseStep 2682443 = 4023665) B4023665
theorem B1789515 : Blo 1788095 1789515 := bstep (se 1 (by rfl) ⟨1342136, by rfl⟩ : syracuseStep 1789515 = 2684273) B2684273
theorem B2682455 : Blo 1788095 2682455 := bstep (se 1 (by rfl) ⟨2011841, by rfl⟩ : syracuseStep 2682455 = 4023683) B4023683
theorem B1789527 : Blo 1788095 1789527 := bstep (se 1 (by rfl) ⟨1342145, by rfl⟩ : syracuseStep 1789527 = 2684291) B2684291
theorem B1789547 : Blo 1788095 1789547 := bstep (se 1 (by rfl) ⟨1342160, by rfl⟩ : syracuseStep 1789547 = 2684321) B2684321
theorem B1789559 : Blo 1788095 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B3821185 : Blo 1788095 3821185 := bstep (se 2 (by rfl) ⟨1432944, by rfl⟩ : syracuseStep 3821185 = 2865889) B2865889
theorem B1789579 : Blo 1788095 1789579 := bstep (se 1 (by rfl) ⟨1342184, by rfl⟩ : syracuseStep 1789579 = 2684369) B2684369
theorem B1789591 : Blo 1788095 1789591 := bstep (se 1 (by rfl) ⟨1342193, by rfl⟩ : syracuseStep 1789591 = 2684387) B2684387
theorem B2682521 : Blo 1788095 2682521 := bstep (se 2 (by rfl) ⟨1005945, by rfl⟩ : syracuseStep 2682521 = 2011891) B2011891
theorem B1789611 : Blo 1788095 1789611 := bstep (se 1 (by rfl) ⟨1342208, by rfl⟩ : syracuseStep 1789611 = 2684417) B2684417
theorem B1789623 : Blo 1788095 1789623 := bstep (se 1 (by rfl) ⟨1342217, by rfl⟩ : syracuseStep 1789623 = 2684435) B2684435
theorem B4026059 : Blo 1788095 4026059 := bstep (se 1 (by rfl) ⟨3019544, by rfl⟩ : syracuseStep 4026059 = 6039089) B6039089
theorem B1789643 : Blo 1788095 1789643 := bstep (se 1 (by rfl) ⟨1342232, by rfl⟩ : syracuseStep 1789643 = 2684465) B2684465
theorem B1814219 : Blo 1788095 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B3395287 : Blo 1788095 3395287 := bstep (se 1 (by rfl) ⟨2546465, by rfl⟩ : syracuseStep 3395287 = 5092931) B5092931
theorem B1789655 : Blo 1788095 1789655 := bstep (se 1 (by rfl) ⟨1342241, by rfl⟩ : syracuseStep 1789655 = 2684483) B2684483
theorem B9055961 : Blo 1788095 9055961 := bstep (se 2 (by rfl) ⟨3395985, by rfl⟩ : syracuseStep 9055961 = 6791971) B6791971
theorem B1789675 : Blo 1788095 1789675 := bstep (se 1 (by rfl) ⟨1342256, by rfl⟩ : syracuseStep 1789675 = 2684513) B2684513
theorem B1789687 : Blo 1788095 1789687 := bstep (se 1 (by rfl) ⟨1342265, by rfl⟩ : syracuseStep 1789687 = 2684531) B2684531
theorem B4026113 : Blo 1788095 4026113 := bstep (se 2 (by rfl) ⟨1509792, by rfl⟩ : syracuseStep 4026113 = 3019585) B3019585
theorem B2682635 : Blo 1788095 2682635 := bstep (se 1 (by rfl) ⟨2011976, by rfl⟩ : syracuseStep 2682635 = 4023953) B4023953
theorem B1789707 : Blo 1788095 1789707 := bstep (se 1 (by rfl) ⟨1342280, by rfl⟩ : syracuseStep 1789707 = 2684561) B2684561
theorem B2682647 : Blo 1788095 2682647 := bstep (se 1 (by rfl) ⟨2011985, by rfl⟩ : syracuseStep 2682647 = 4023971) B4023971
theorem B1789719 : Blo 1788095 1789719 := bstep (se 1 (by rfl) ⟨1342289, by rfl⟩ : syracuseStep 1789719 = 2684579) B2684579
theorem B1789739 : Blo 1788095 1789739 := bstep (se 1 (by rfl) ⟨1342304, by rfl⟩ : syracuseStep 1789739 = 2684609) B2684609
theorem B1789751 : Blo 1788095 1789751 := bstep (se 1 (by rfl) ⟨1342313, by rfl⟩ : syracuseStep 1789751 = 2684627) B2684627
theorem B3223361 : Blo 1788095 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B1789771 : Blo 1788095 1789771 := bstep (se 1 (by rfl) ⟨1342328, by rfl⟩ : syracuseStep 1789771 = 2684657) B2684657
theorem B1789783 : Blo 1788095 1789783 := bstep (se 1 (by rfl) ⟨1342337, by rfl⟩ : syracuseStep 1789783 = 2684675) B2684675
theorem B2682713 : Blo 1788095 2682713 := bstep (se 2 (by rfl) ⟨1006017, by rfl⟩ : syracuseStep 2682713 = 2012035) B2012035
theorem B34860901 : Blo 1788095 34860901 := bstep (se 4 (by rfl) ⟨3268209, by rfl⟩ : syracuseStep 34860901 = 6536419) B6536419
theorem B1789803 : Blo 1788095 1789803 := bstep (se 1 (by rfl) ⟨1342352, by rfl⟩ : syracuseStep 1789803 = 2684705) B2684705
theorem B1789815 : Blo 1788095 1789815 := bstep (se 1 (by rfl) ⟨1342361, by rfl⟩ : syracuseStep 1789815 = 2684723) B2684723
theorem B1789835 : Blo 1788095 1789835 := bstep (se 1 (by rfl) ⟨1342376, by rfl⟩ : syracuseStep 1789835 = 2684753) B2684753
theorem B3018647 : Blo 1788095 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B1789847 : Blo 1788095 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B1789867 : Blo 1788095 1789867 := bstep (se 1 (by rfl) ⟨1342400, by rfl⟩ : syracuseStep 1789867 = 2684801) B2684801
theorem B1789879 : Blo 1788095 1789879 := bstep (se 1 (by rfl) ⟨1342409, by rfl⟩ : syracuseStep 1789879 = 2684819) B2684819
theorem B2682827 : Blo 1788095 2682827 := bstep (se 1 (by rfl) ⟨2012120, by rfl⟩ : syracuseStep 2682827 = 4024241) B4024241
theorem B1789899 : Blo 1788095 1789899 := bstep (se 1 (by rfl) ⟨1342424, by rfl⟩ : syracuseStep 1789899 = 2684849) B2684849
theorem B2682839 : Blo 1788095 2682839 := bstep (se 1 (by rfl) ⟨2012129, by rfl⟩ : syracuseStep 2682839 = 4024259) B4024259
theorem B4026329 : Blo 1788095 4026329 := bstep (se 2 (by rfl) ⟨1509873, by rfl⟩ : syracuseStep 4026329 = 3019747) B3019747
theorem B14348249 : Blo 1788095 14348249 := bstep (se 2 (by rfl) ⟨5380593, by rfl⟩ : syracuseStep 14348249 = 10761187) B10761187
theorem B1789911 : Blo 1788095 1789911 := bstep (se 1 (by rfl) ⟨1342433, by rfl⟩ : syracuseStep 1789911 = 2684867) B2684867
theorem B1789931 : Blo 1788095 1789931 := bstep (se 1 (by rfl) ⟨1342448, by rfl⟩ : syracuseStep 1789931 = 2684897) B2684897
theorem B1789943 : Blo 1788095 1789943 := bstep (se 1 (by rfl) ⟨1342457, by rfl⟩ : syracuseStep 1789943 = 2684915) B2684915
theorem B1789963 : Blo 1788095 1789963 := bstep (se 1 (by rfl) ⟨1342472, by rfl⟩ : syracuseStep 1789963 = 2684945) B2684945
theorem B3018775 : Blo 1788095 3018775 := bstep (se 1 (by rfl) ⟨2264081, by rfl⟩ : syracuseStep 3018775 = 4528163) B4528163
theorem B1789975 : Blo 1788095 1789975 := bstep (se 1 (by rfl) ⟨1342481, by rfl⟩ : syracuseStep 1789975 = 2684963) B2684963
theorem B2682905 : Blo 1788095 2682905 := bstep (se 2 (by rfl) ⟨1006089, by rfl⟩ : syracuseStep 2682905 = 2012179) B2012179
theorem B1789995 : Blo 1788095 1789995 := bstep (se 1 (by rfl) ⟨1342496, by rfl⟩ : syracuseStep 1789995 = 2684993) B2684993
theorem B4026419 : Blo 1788095 4026419 := bstep (se 1 (by rfl) ⟨3019814, by rfl⟩ : syracuseStep 4026419 = 6039629) B6039629
theorem B1790007 : Blo 1788095 1790007 := bstep (se 1 (by rfl) ⟨1342505, by rfl⟩ : syracuseStep 1790007 = 2685011) B2685011
theorem B1790027 : Blo 1788095 1790027 := bstep (se 1 (by rfl) ⟨1342520, by rfl⟩ : syracuseStep 1790027 = 2685041) B2685041
theorem B4026455 : Blo 1788095 4026455 := bstep (se 1 (by rfl) ⟨3019841, by rfl⟩ : syracuseStep 4026455 = 6039683) B6039683
theorem B2265175 : Blo 1788095 2265175 := bstep (se 1 (by rfl) ⟨1698881, by rfl⟩ : syracuseStep 2265175 = 3397763) B3397763
theorem B1790039 : Blo 1788095 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1790071 : Blo 1788095 1790071 := bstep (se 1 (by rfl) ⟨1342553, by rfl⟩ : syracuseStep 1790071 = 2685107) B2685107
theorem B2683019 : Blo 1788095 2683019 := bstep (se 1 (by rfl) ⟨2012264, by rfl⟩ : syracuseStep 2683019 = 4024529) B4024529
theorem B1790091 : Blo 1788095 1790091 := bstep (se 1 (by rfl) ⟨1342568, by rfl⟩ : syracuseStep 1790091 = 2685137) B2685137
theorem B2683031 : Blo 1788095 2683031 := bstep (se 1 (by rfl) ⟨2012273, by rfl⟩ : syracuseStep 2683031 = 4024547) B4024547
theorem B2683097 : Blo 1788095 2683097 := bstep (se 2 (by rfl) ⟨1006161, by rfl⟩ : syracuseStep 2683097 = 2012323) B2012323
theorem B4026635 : Blo 1788095 4026635 := bstep (se 1 (by rfl) ⟨3019976, by rfl⟩ : syracuseStep 4026635 = 6039953) B6039953
theorem B4526401 : Blo 1788095 4526401 := bstep (se 2 (by rfl) ⟨1697400, by rfl⟩ : syracuseStep 4526401 = 3394801) B3394801
theorem B4026689 : Blo 1788095 4026689 := bstep (se 2 (by rfl) ⟨1510008, by rfl⟩ : syracuseStep 4026689 = 3020017) B3020017
theorem B2683211 : Blo 1788095 2683211 := bstep (se 1 (by rfl) ⟨2012408, by rfl⟩ : syracuseStep 2683211 = 4024817) B4024817
theorem B2683223 : Blo 1788095 2683223 := bstep (se 1 (by rfl) ⟨2012417, by rfl⟩ : syracuseStep 2683223 = 4024835) B4024835
theorem B6533507 : Blo 1788095 6533507 := bstep (se 1 (by rfl) ⟨4900130, by rfl⟩ : syracuseStep 6533507 = 9800261) B9800261
theorem B2683289 : Blo 1788095 2683289 := bstep (se 2 (by rfl) ⟨1006233, by rfl⟩ : syracuseStep 2683289 = 2012467) B2012467
theorem B2011639 : Blo 1788095 2011639 := bstep (se 1 (by rfl) ⟨1508729, by rfl⟩ : syracuseStep 2011639 = 3017459) B3017459
theorem B3396107 : Blo 1788095 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2683403 : Blo 1788095 2683403 := bstep (se 1 (by rfl) ⟨2012552, by rfl⟩ : syracuseStep 2683403 = 4025105) B4025105
theorem B2683415 : Blo 1788095 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B4026905 : Blo 1788095 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B3396161 : Blo 1788095 3396161 := bstep (se 2 (by rfl) ⟨1273560, by rfl⟩ : syracuseStep 3396161 = 2547121) B2547121
theorem B13775435 : Blo 1788095 13775435 := bstep (se 1 (by rfl) ⟨10331576, by rfl⟩ : syracuseStep 13775435 = 20663153) B20663153
theorem B5091929 : Blo 1788095 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B2904665 : Blo 1788095 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B2683481 : Blo 1788095 2683481 := bstep (se 2 (by rfl) ⟨1006305, by rfl⟩ : syracuseStep 2683481 = 2012611) B2012611
theorem B11457125 : Blo 1788095 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B4026995 : Blo 1788095 4026995 := bstep (se 1 (by rfl) ⟨3020246, by rfl⟩ : syracuseStep 4026995 = 6040493) B6040493
theorem B14504579 : Blo 1788095 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B3019403 : Blo 1788095 3019403 := bstep (se 1 (by rfl) ⟨2264552, by rfl⟩ : syracuseStep 3019403 = 4529105) B4529105
theorem B4027031 : Blo 1788095 4027031 := bstep (se 1 (by rfl) ⟨3020273, by rfl⟩ : syracuseStep 4027031 = 6040547) B6040547
theorem B2011819 : Blo 1788095 2011819 := bstep (se 1 (by rfl) ⟨1508864, by rfl⟩ : syracuseStep 2011819 = 3017729) B3017729
theorem B2683595 : Blo 1788095 2683595 := bstep (se 1 (by rfl) ⟨2012696, by rfl⟩ : syracuseStep 2683595 = 4025393) B4025393
theorem B2683607 : Blo 1788095 2683607 := bstep (se 1 (by rfl) ⟨2012705, by rfl⟩ : syracuseStep 2683607 = 4025411) B4025411
theorem B3019531 : Blo 1788095 3019531 := bstep (se 1 (by rfl) ⟨2264648, by rfl⟩ : syracuseStep 3019531 = 4529297) B4529297
theorem B2011927 : Blo 1788095 2011927 := bstep (se 1 (by rfl) ⟨1508945, by rfl⟩ : syracuseStep 2011927 = 3017891) B3017891
theorem B2683673 : Blo 1788095 2683673 := bstep (se 2 (by rfl) ⟨1006377, by rfl⟩ : syracuseStep 2683673 = 2012755) B2012755
theorem B7639859 : Blo 1788095 7639859 := bstep (se 1 (by rfl) ⟨5729894, by rfl⟩ : syracuseStep 7639859 = 11459789) B11459789
theorem B4027211 : Blo 1788095 4027211 := bstep (se 1 (by rfl) ⟨3020408, by rfl⟩ : syracuseStep 4027211 = 6040817) B6040817
theorem B4027265 : Blo 1788095 4027265 := bstep (se 2 (by rfl) ⟨1510224, by rfl⟩ : syracuseStep 4027265 = 3020449) B3020449
theorem B6796163 : Blo 1788095 6796163 := bstep (se 1 (by rfl) ⟨5097122, by rfl⟩ : syracuseStep 6796163 = 10194245) B10194245
theorem B2683787 : Blo 1788095 2683787 := bstep (se 1 (by rfl) ⟨2012840, by rfl⟩ : syracuseStep 2683787 = 4025681) B4025681
theorem B5092247 : Blo 1788095 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B4526999 : Blo 1788095 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B2683799 : Blo 1788095 2683799 := bstep (se 1 (by rfl) ⟨2012849, by rfl⟩ : syracuseStep 2683799 = 4025699) B4025699
theorem B3019673 : Blo 1788095 3019673 := bstep (se 2 (by rfl) ⟨1132377, by rfl⟩ : syracuseStep 3019673 = 2264755) B2264755
theorem B4355009 : Blo 1788095 4355009 := bstep (se 2 (by rfl) ⟨1633128, by rfl⟩ : syracuseStep 4355009 = 3266257) B3266257
theorem B2012107 : Blo 1788095 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B7640011 : Blo 1788095 7640011 := bstep (se 1 (by rfl) ⟨5730008, by rfl⟩ : syracuseStep 7640011 = 11460017) B11460017
theorem B2683865 : Blo 1788095 2683865 := bstep (se 2 (by rfl) ⟨1006449, by rfl⟩ : syracuseStep 2683865 = 2012899) B2012899
theorem B7640081 : Blo 1788095 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B3019801 : Blo 1788095 3019801 := bstep (se 2 (by rfl) ⟨1132425, by rfl⟩ : syracuseStep 3019801 = 2264851) B2264851
theorem B2012215 : Blo 1788095 2012215 := bstep (se 1 (by rfl) ⟨1509161, by rfl⟩ : syracuseStep 2012215 = 3018323) B3018323
theorem B5731393 : Blo 1788095 5731393 := bstep (se 2 (by rfl) ⟨2149272, by rfl⟩ : syracuseStep 5731393 = 4298545) B4298545
theorem B11457611 : Blo 1788095 11457611 := bstep (se 1 (by rfl) ⟨8593208, by rfl⟩ : syracuseStep 11457611 = 17186417) B17186417
theorem B2683979 : Blo 1788095 2683979 := bstep (se 1 (by rfl) ⟨2012984, by rfl⟩ : syracuseStep 2683979 = 4025969) B4025969
theorem B2683991 : Blo 1788095 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B4027481 : Blo 1788095 4027481 := bstep (se 2 (by rfl) ⟨1510305, by rfl⟩ : syracuseStep 4027481 = 3020611) B3020611
theorem B13587587 : Blo 1788095 13587587 := bstep (se 1 (by rfl) ⟨10190690, by rfl⟩ : syracuseStep 13587587 = 20381381) B20381381
theorem B2684057 : Blo 1788095 2684057 := bstep (se 2 (by rfl) ⟨1006521, by rfl⟩ : syracuseStep 2684057 = 2013043) B2013043
theorem B4027571 : Blo 1788095 4027571 := bstep (se 1 (by rfl) ⟨3020678, by rfl⟩ : syracuseStep 4027571 = 6041357) B6041357
theorem B4838579 : Blo 1788095 4838579 := bstep (se 1 (by rfl) ⟨3628934, by rfl⟩ : syracuseStep 4838579 = 7257869) B7257869
theorem B4297931 : Blo 1788095 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B4027607 : Blo 1788095 4027607 := bstep (se 1 (by rfl) ⟨3020705, by rfl⟩ : syracuseStep 4027607 = 6041411) B6041411
theorem B2012395 : Blo 1788095 2012395 := bstep (se 1 (by rfl) ⟨1509296, by rfl⟩ : syracuseStep 2012395 = 3018593) B3018593
theorem B2684171 : Blo 1788095 2684171 := bstep (se 1 (by rfl) ⟨2013128, by rfl⟩ : syracuseStep 2684171 = 4026257) B4026257
theorem B2684183 : Blo 1788095 2684183 := bstep (se 1 (by rfl) ⟨2013137, by rfl⟩ : syracuseStep 2684183 = 4026275) B4026275
theorem B9057581 : Blo 1788095 9057581 := bstep (se 3 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 9057581 = 3396593) B3396593
theorem B5731649 : Blo 1788095 5731649 := bstep (se 2 (by rfl) ⟨2149368, by rfl⟩ : syracuseStep 5731649 = 4298737) B4298737
theorem B6796619 : Blo 1788095 6796619 := bstep (se 1 (by rfl) ⟨5097464, by rfl⟩ : syracuseStep 6796619 = 10194929) B10194929
theorem B2012503 : Blo 1788095 2012503 := bstep (se 1 (by rfl) ⟨1509377, by rfl⟩ : syracuseStep 2012503 = 3018755) B3018755
theorem B2684249 : Blo 1788095 2684249 := bstep (se 2 (by rfl) ⟨1006593, by rfl⟩ : syracuseStep 2684249 = 2013187) B2013187
theorem B8598935 : Blo 1788095 8598935 := bstep (se 1 (by rfl) ⟨6449201, by rfl⟩ : syracuseStep 8598935 = 12898403) B12898403
theorem B27530675 : Blo 1788095 27530675 := bstep (se 1 (by rfl) ⟨20648006, by rfl⟩ : syracuseStep 27530675 = 41296013) B41296013
theorem B2684363 : Blo 1788095 2684363 := bstep (se 1 (by rfl) ⟨2013272, by rfl⟩ : syracuseStep 2684363 = 4026545) B4026545
theorem B3397079 : Blo 1788095 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B2684375 : Blo 1788095 2684375 := bstep (se 1 (by rfl) ⟨2013281, by rfl⟩ : syracuseStep 2684375 = 4026563) B4026563
theorem B2012683 : Blo 1788095 2012683 := bstep (se 1 (by rfl) ⟨1509512, by rfl⟩ : syracuseStep 2012683 = 3019025) B3019025
theorem B2684441 : Blo 1788095 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B13579811 : Blo 1788095 13579811 := bstep (se 1 (by rfl) ⟨10184858, by rfl⟩ : syracuseStep 13579811 = 20369717) B20369717
theorem B4355635 : Blo 1788095 4355635 := bstep (se 1 (by rfl) ⟨3266726, by rfl⟩ : syracuseStep 4355635 = 6533453) B6533453
theorem B3020375 : Blo 1788095 3020375 := bstep (se 1 (by rfl) ⟨2265281, by rfl⟩ : syracuseStep 3020375 = 4530563) B4530563
theorem B2012791 : Blo 1788095 2012791 := bstep (se 1 (by rfl) ⟨1509593, by rfl⟩ : syracuseStep 2012791 = 3019187) B3019187
theorem B2684555 : Blo 1788095 2684555 := bstep (se 1 (by rfl) ⟨2013416, by rfl⟩ : syracuseStep 2684555 = 4026833) B4026833
theorem B17430167 : Blo 1788095 17430167 := bstep (se 1 (by rfl) ⟨13072625, by rfl⟩ : syracuseStep 17430167 = 26145251) B26145251
theorem B2684567 : Blo 1788095 2684567 := bstep (se 1 (by rfl) ⟨2013425, by rfl⟩ : syracuseStep 2684567 = 4026851) B4026851
theorem B2758297 : Blo 1788095 2758297 := bstep (se 2 (by rfl) ⟨1034361, by rfl⟩ : syracuseStep 2758297 = 2068723) B2068723
theorem B12900019 : Blo 1788095 12900019 := bstep (se 1 (by rfl) ⟨9675014, by rfl⟩ : syracuseStep 12900019 = 19350029) B19350029
theorem B5093057 : Blo 1788095 5093057 := bstep (se 2 (by rfl) ⟨1909896, by rfl⟩ : syracuseStep 5093057 = 3819793) B3819793
theorem B4527809 : Blo 1788095 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B6035147 : Blo 1788095 6035147 := bstep (se 1 (by rfl) ⟨4526360, by rfl⟩ : syracuseStep 6035147 = 9052721) B9052721
theorem B3020503 : Blo 1788095 3020503 := bstep (se 1 (by rfl) ⟨2265377, by rfl⟩ : syracuseStep 3020503 = 4530755) B4530755
theorem B2684633 : Blo 1788095 2684633 := bstep (se 2 (by rfl) ⟨1006737, by rfl⟩ : syracuseStep 2684633 = 2013475) B2013475
theorem B10884881 : Blo 1788095 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2012971 : Blo 1788095 2012971 := bstep (se 1 (by rfl) ⟨1509728, by rfl⟩ : syracuseStep 2012971 = 3019457) B3019457
theorem B3225395 : Blo 1788095 3225395 := bstep (se 1 (by rfl) ⟨2419046, by rfl⟩ : syracuseStep 3225395 = 4838093) B4838093
theorem B2684747 : Blo 1788095 2684747 := bstep (se 1 (by rfl) ⟨2013560, by rfl⟩ : syracuseStep 2684747 = 4027121) B4027121
theorem B2684759 : Blo 1788095 2684759 := bstep (se 1 (by rfl) ⟨2013569, by rfl⟩ : syracuseStep 2684759 = 4027139) B4027139
theorem B29407093 : Blo 1788095 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2013079 : Blo 1788095 2013079 := bstep (se 1 (by rfl) ⟨1509809, by rfl⟩ : syracuseStep 2013079 = 3019619) B3019619
theorem B2684825 : Blo 1788095 2684825 := bstep (se 2 (by rfl) ⟨1006809, by rfl⟩ : syracuseStep 2684825 = 2013619) B2013619
theorem B6035417 : Blo 1788095 6035417 := bstep (se 2 (by rfl) ⟨2263281, by rfl⟩ : syracuseStep 6035417 = 4526563) B4526563
theorem B6445021 : Blo 1788095 6445021 := bstep (se 3 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 6445021 = 2416883) B2416883
theorem B3397619 : Blo 1788095 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2684939 : Blo 1788095 2684939 := bstep (se 1 (by rfl) ⟨2013704, by rfl⟩ : syracuseStep 2684939 = 4027409) B4027409
theorem B2684951 : Blo 1788095 2684951 := bstep (se 1 (by rfl) ⟨2013713, by rfl⟩ : syracuseStep 2684951 = 4027427) B4027427
theorem B2013259 : Blo 1788095 2013259 := bstep (se 1 (by rfl) ⟨1509944, by rfl⟩ : syracuseStep 2013259 = 3019889) B3019889
theorem B2685017 : Blo 1788095 2685017 := bstep (se 2 (by rfl) ⟨1006881, by rfl⟩ : syracuseStep 2685017 = 2013763) B2013763
theorem B2013367 : Blo 1788095 2013367 := bstep (se 1 (by rfl) ⟨1510025, by rfl⟩ : syracuseStep 2013367 = 3020051) B3020051
theorem B2685131 : Blo 1788095 2685131 := bstep (se 1 (by rfl) ⟨2013848, by rfl⟩ : syracuseStep 2685131 = 4027697) B4027697
theorem B2685143 : Blo 1788095 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B4528345 : Blo 1788095 4528345 := bstep (se 2 (by rfl) ⟨1698129, by rfl⟩ : syracuseStep 4528345 = 3396259) B3396259
theorem B2013547 : Blo 1788095 2013547 := bstep (se 1 (by rfl) ⟨1510160, by rfl⟩ : syracuseStep 2013547 = 3020321) B3020321
theorem B6789527 : Blo 1788095 6789527 := bstep (se 1 (by rfl) ⟨5092145, by rfl⟩ : syracuseStep 6789527 = 10184291) B10184291
theorem B7747991 : Blo 1788095 7747991 := bstep (se 1 (by rfl) ⟨5810993, by rfl⟩ : syracuseStep 7747991 = 11621987) B11621987
theorem B2013655 : Blo 1788095 2013655 := bstep (se 1 (by rfl) ⟨1510241, by rfl⟩ : syracuseStep 2013655 = 3020483) B3020483
theorem B3398105 : Blo 1788095 3398105 := bstep (se 2 (by rfl) ⟨1274289, by rfl⟩ : syracuseStep 3398105 = 2548579) B2548579
theorem B2013835 : Blo 1788095 2013835 := bstep (se 1 (by rfl) ⟨1510376, by rfl⟩ : syracuseStep 2013835 = 3020753) B3020753
theorem B6036119 : Blo 1788095 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B2546329 : Blo 1788095 2546329 := bstep (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) B1909747
theorem B7641773 : Blo 1788095 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B10328897 : Blo 1788095 10328897 := bstep (se 2 (by rfl) ⟨3873336, by rfl⟩ : syracuseStep 10328897 = 7746673) B7746673
theorem B7748531 : Blo 1788095 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B6036659 : Blo 1788095 6036659 := bstep (se 1 (by rfl) ⟨4527494, by rfl⟩ : syracuseStep 6036659 = 9054989) B9054989
theorem B7453889 : Blo 1788095 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B4529459 : Blo 1788095 4529459 := bstep (se 1 (by rfl) ⟨3397094, by rfl⟩ : syracuseStep 4529459 = 6794189) B6794189
theorem B5094731 : Blo 1788095 5094731 := bstep (se 1 (by rfl) ⟨3821048, by rfl⟩ : syracuseStep 5094731 = 7642097) B7642097
theorem B7642457 : Blo 1788095 7642457 := bstep (se 2 (by rfl) ⟨2865921, by rfl⟩ : syracuseStep 7642457 = 5731843) B5731843
theorem B2719127 : Blo 1788095 2719127 := bstep (se 1 (by rfl) ⟨2039345, by rfl⟩ : syracuseStep 2719127 = 4078691) B4078691
theorem B8601011 : Blo 1788095 8601011 := bstep (se 1 (by rfl) ⟨6450758, by rfl⟩ : syracuseStep 8601011 = 12901517) B12901517
theorem B6036929 : Blo 1788095 6036929 := bstep (se 2 (by rfl) ⟨2263848, by rfl⟩ : syracuseStep 6036929 = 4527697) B4527697
theorem B14507525 : Blo 1788095 14507525 := bstep (se 4 (by rfl) ⟨1360080, by rfl⟩ : syracuseStep 14507525 = 2720161) B2720161
theorem B4529753 : Blo 1788095 4529753 := bstep (se 2 (by rfl) ⟨1698657, by rfl⟩ : syracuseStep 4529753 = 3397315) B3397315
theorem B6790787 : Blo 1788095 6790787 := bstep (se 1 (by rfl) ⟨5093090, by rfl⟩ : syracuseStep 6790787 = 10186181) B10186181
theorem B11460275 : Blo 1788095 11460275 := bstep (se 1 (by rfl) ⟨8595206, by rfl⟩ : syracuseStep 11460275 = 17190413) B17190413
theorem B3489473 : Blo 1788095 3489473 := bstep (se 2 (by rfl) ⟨1308552, by rfl⟩ : syracuseStep 3489473 = 2617105) B2617105
theorem B5734109 : Blo 1788095 5734109 := bstep (se 3 (by rfl) ⟨1075145, by rfl⟩ : syracuseStep 5734109 = 2150291) B2150291
theorem B5439449 : Blo 1788095 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B6037469 : Blo 1788095 6037469 := bstep (se 3 (by rfl) ⟨1132025, by rfl⟩ : syracuseStep 6037469 = 2264051) B2264051
theorem B3489779 : Blo 1788095 3489779 := bstep (se 1 (by rfl) ⟨2617334, by rfl⟩ : syracuseStep 3489779 = 5234669) B5234669
theorem B4079659 : Blo 1788095 4079659 := bstep (se 1 (by rfl) ⟨3059744, by rfl⟩ : syracuseStep 4079659 = 6119489) B6119489
theorem B9052397 : Blo 1788095 9052397 := bstep (se 3 (by rfl) ⟨1697324, by rfl⟩ : syracuseStep 9052397 = 3394649) B3394649
theorem B36733169 : Blo 1788095 36733169 := bstep (se 2 (by rfl) ⟨13774938, by rfl⟩ : syracuseStep 36733169 = 27549877) B27549877
theorem B6037793 : Blo 1788095 6037793 := bstep (se 2 (by rfl) ⟨2264172, by rfl⟩ : syracuseStep 6037793 = 4528345) B4528345
theorem B9060659 : Blo 1788095 9060659 := bstep (se 1 (by rfl) ⟨6795494, by rfl⟩ : syracuseStep 9060659 = 13590989) B13590989
theorem B13582727 : Blo 1788095 13582727 := bstep (se 1 (by rfl) ⟨10187045, by rfl⟩ : syracuseStep 13582727 = 20374091) B20374091
theorem B9183623 : Blo 1788095 9183623 := bstep (se 1 (by rfl) ⟨6887717, by rfl⟩ : syracuseStep 9183623 = 13775435) B13775435
theorem B15491513 : Blo 1788095 15491513 := bstep (se 2 (by rfl) ⟨5809317, by rfl⟩ : syracuseStep 15491513 = 11618635) B11618635
theorem B4587977 : Blo 1788095 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B77406677 : Blo 1788095 77406677 := bstep (se 7 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 77406677 = 1814219) B1814219
theorem B4530775 : Blo 1788095 4530775 := bstep (se 1 (by rfl) ⟨3398081, by rfl⟩ : syracuseStep 4530775 = 6796163) B6796163
theorem B9060983 : Blo 1788095 9060983 := bstep (se 1 (by rfl) ⟨6795737, by rfl⟩ : syracuseStep 9060983 = 13591475) B13591475
theorem B2720503 : Blo 1788095 2720503 := bstep (se 1 (by rfl) ⟨2040377, by rfl⟩ : syracuseStep 2720503 = 4080755) B4080755
theorem B6038387 : Blo 1788095 6038387 := bstep (se 1 (by rfl) ⟨4528790, by rfl⟩ : syracuseStep 6038387 = 9057581) B9057581
theorem B4531079 : Blo 1788095 4531079 := bstep (se 1 (by rfl) ⟨3398309, by rfl⟩ : syracuseStep 4531079 = 6796619) B6796619
theorem B30983093 : Blo 1788095 30983093 := bstep (se 5 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 30983093 = 2904665) B2904665
theorem B9053207 : Blo 1788095 9053207 := bstep (se 1 (by rfl) ⟨6789905, by rfl⟩ : syracuseStep 9053207 = 13579811) B13579811
theorem B7251005 : Blo 1788095 7251005 := bstep (se 3 (by rfl) ⟨1359563, by rfl⟩ : syracuseStep 7251005 = 2719127) B2719127
theorem B4023431 : Blo 1788095 4023431 := bstep (se 1 (by rfl) ⟨3017573, by rfl⟩ : syracuseStep 4023431 = 6035147) B6035147
theorem B4023611 : Blo 1788095 4023611 := bstep (se 1 (by rfl) ⟨3017708, by rfl⟩ : syracuseStep 4023611 = 6035417) B6035417
theorem B4023737 : Blo 1788095 4023737 := bstep (se 2 (by rfl) ⟨1508901, by rfl⟩ : syracuseStep 4023737 = 3017803) B3017803
theorem B10192331 : Blo 1788095 10192331 := bstep (se 1 (by rfl) ⟨7644248, by rfl⟩ : syracuseStep 10192331 = 15288497) B15288497
theorem B9061955 : Blo 1788095 9061955 := bstep (se 1 (by rfl) ⟨6796466, by rfl⟩ : syracuseStep 9061955 = 13592933) B13592933
theorem B30574259 : Blo 1788095 30574259 := bstep (se 1 (by rfl) ⟨22930694, by rfl⟩ : syracuseStep 30574259 = 45861389) B45861389
theorem B4024079 : Blo 1788095 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B4024097 : Blo 1788095 4024097 := bstep (se 2 (by rfl) ⟨1509036, by rfl⟩ : syracuseStep 4024097 = 3018073) B3018073
theorem B5097259 : Blo 1788095 5097259 := bstep (se 1 (by rfl) ⟨3822944, by rfl⟩ : syracuseStep 5097259 = 7645889) B7645889
theorem B2148215 : Blo 1788095 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B3819383 : Blo 1788095 3819383 := bstep (se 1 (by rfl) ⟨2864537, by rfl⟩ : syracuseStep 3819383 = 5729075) B5729075
theorem B2721671 : Blo 1788095 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B9062279 : Blo 1788095 9062279 := bstep (se 1 (by rfl) ⟨6796709, by rfl⟩ : syracuseStep 9062279 = 13593419) B13593419
theorem B10192787 : Blo 1788095 10192787 := bstep (se 1 (by rfl) ⟨7644590, by rfl⟩ : syracuseStep 10192787 = 15289181) B15289181
theorem B5097487 : Blo 1788095 5097487 := bstep (se 1 (by rfl) ⟨3823115, by rfl⟩ : syracuseStep 5097487 = 7646231) B7646231
theorem B4835387 : Blo 1788095 4835387 := bstep (se 1 (by rfl) ⟨3626540, by rfl⟩ : syracuseStep 4835387 = 7253081) B7253081
theorem B5441651 : Blo 1788095 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B4024439 : Blo 1788095 4024439 := bstep (se 1 (by rfl) ⟨3018329, by rfl⟩ : syracuseStep 4024439 = 6036659) B6036659
theorem B8595629 : Blo 1788095 8595629 := bstep (se 3 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 8595629 = 3223361) B3223361
theorem B27543725 : Blo 1788095 27543725 := bstep (se 3 (by rfl) ⟨5164448, by rfl⟩ : syracuseStep 27543725 = 10328897) B10328897
theorem B1788167 : Blo 1788095 1788167 := bstep (se 1 (by rfl) ⟨1341125, by rfl⟩ : syracuseStep 1788167 = 2682251) B2682251
theorem B1788175 : Blo 1788095 1788175 := bstep (se 1 (by rfl) ⟨1341131, by rfl⟩ : syracuseStep 1788175 = 2682263) B2682263
theorem B4024619 : Blo 1788095 4024619 := bstep (se 1 (by rfl) ⟨3018464, by rfl⟩ : syracuseStep 4024619 = 6036929) B6036929
theorem B1788219 : Blo 1788095 1788219 := bstep (se 1 (by rfl) ⟨1341164, by rfl⟩ : syracuseStep 1788219 = 2682329) B2682329
theorem B3819835 : Blo 1788095 3819835 := bstep (se 1 (by rfl) ⟨2864876, by rfl⟩ : syracuseStep 3819835 = 5729753) B5729753
theorem B8161651 : Blo 1788095 8161651 := bstep (se 1 (by rfl) ⟨6121238, by rfl⟩ : syracuseStep 8161651 = 12242477) B12242477
theorem B1788295 : Blo 1788095 1788295 := bstep (se 1 (by rfl) ⟨1341221, by rfl⟩ : syracuseStep 1788295 = 2682443) B2682443
theorem B1788303 : Blo 1788095 1788303 := bstep (se 1 (by rfl) ⟨1341227, by rfl⟩ : syracuseStep 1788303 = 2682455) B2682455
theorem B1788347 : Blo 1788095 1788347 := bstep (se 1 (by rfl) ⟨1341260, by rfl⟩ : syracuseStep 1788347 = 2682521) B2682521
theorem B1788423 : Blo 1788095 1788423 := bstep (se 1 (by rfl) ⟨1341317, by rfl⟩ : syracuseStep 1788423 = 2682635) B2682635
theorem B1788431 : Blo 1788095 1788431 := bstep (se 1 (by rfl) ⟨1341323, by rfl⟩ : syracuseStep 1788431 = 2682647) B2682647
theorem B1788475 : Blo 1788095 1788475 := bstep (se 1 (by rfl) ⟨1341356, by rfl⟩ : syracuseStep 1788475 = 2682713) B2682713
theorem B1788551 : Blo 1788095 1788551 := bstep (se 1 (by rfl) ⟨1341413, by rfl⟩ : syracuseStep 1788551 = 2682827) B2682827
theorem B1788559 : Blo 1788095 1788559 := bstep (se 1 (by rfl) ⟨1341419, by rfl⟩ : syracuseStep 1788559 = 2682839) B2682839
theorem B4024979 : Blo 1788095 4024979 := bstep (se 1 (by rfl) ⟨3018734, by rfl⟩ : syracuseStep 4024979 = 6037469) B6037469
theorem B1788603 : Blo 1788095 1788603 := bstep (se 1 (by rfl) ⟨1341452, by rfl⟩ : syracuseStep 1788603 = 2682905) B2682905
theorem B4025033 : Blo 1788095 4025033 := bstep (se 2 (by rfl) ⟨1509387, by rfl⟩ : syracuseStep 4025033 = 3018775) B3018775
theorem B1788679 : Blo 1788095 1788679 := bstep (se 1 (by rfl) ⟨1341509, by rfl⟩ : syracuseStep 1788679 = 2683019) B2683019
theorem B1788687 : Blo 1788095 1788687 := bstep (se 1 (by rfl) ⟨1341515, by rfl⟩ : syracuseStep 1788687 = 2683031) B2683031
theorem B4836125 : Blo 1788095 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B1788731 : Blo 1788095 1788731 := bstep (se 1 (by rfl) ⟨1341548, by rfl⟩ : syracuseStep 1788731 = 2683097) B2683097
theorem B1788807 : Blo 1788095 1788807 := bstep (se 1 (by rfl) ⟨1341605, by rfl⟩ : syracuseStep 1788807 = 2683211) B2683211
theorem B1788815 : Blo 1788095 1788815 := bstep (se 1 (by rfl) ⟨1341611, by rfl⟩ : syracuseStep 1788815 = 2683223) B2683223
theorem B1788859 : Blo 1788095 1788859 := bstep (se 1 (by rfl) ⟨1341644, by rfl⟩ : syracuseStep 1788859 = 2683289) B2683289
theorem B1788935 : Blo 1788095 1788935 := bstep (se 1 (by rfl) ⟨1341701, by rfl⟩ : syracuseStep 1788935 = 2683403) B2683403
theorem B1788943 : Blo 1788095 1788943 := bstep (se 1 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 1788943 = 2683415) B2683415
theorem B2264107 : Blo 1788095 2264107 := bstep (se 1 (by rfl) ⟨1698080, by rfl⟩ : syracuseStep 2264107 = 3396161) B3396161
theorem B3394619 : Blo 1788095 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B1788987 : Blo 1788095 1788987 := bstep (se 1 (by rfl) ⟨1341740, by rfl⟩ : syracuseStep 1788987 = 2683481) B2683481
theorem B7638083 : Blo 1788095 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B9669719 : Blo 1788095 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B1789063 : Blo 1788095 1789063 := bstep (se 1 (by rfl) ⟨1341797, by rfl⟩ : syracuseStep 1789063 = 2683595) B2683595
theorem B1789071 : Blo 1788095 1789071 := bstep (se 1 (by rfl) ⟨1341803, by rfl⟩ : syracuseStep 1789071 = 2683607) B2683607
theorem B1789115 : Blo 1788095 1789115 := bstep (se 1 (by rfl) ⟨1341836, by rfl⟩ : syracuseStep 1789115 = 2683673) B2683673
theorem B10333421 : Blo 1788095 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B9669889 : Blo 1788095 9669889 := bstep (se 2 (by rfl) ⟨3626208, by rfl⟩ : syracuseStep 9669889 = 7252417) B7252417
theorem B1789191 : Blo 1788095 1789191 := bstep (se 1 (by rfl) ⟨1341893, by rfl⟩ : syracuseStep 1789191 = 2683787) B2683787
theorem B3017999 : Blo 1788095 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B1789199 : Blo 1788095 1789199 := bstep (se 1 (by rfl) ⟨1341899, by rfl⟩ : syracuseStep 1789199 = 2683799) B2683799
theorem B2682155 : Blo 1788095 2682155 := bstep (se 1 (by rfl) ⟨2011616, by rfl⟩ : syracuseStep 2682155 = 4023233) B4023233
theorem B1789243 : Blo 1788095 1789243 := bstep (se 1 (by rfl) ⟨1341932, by rfl⟩ : syracuseStep 1789243 = 2683865) B2683865
theorem B2682185 : Blo 1788095 2682185 := bstep (se 2 (by rfl) ⟨1005819, by rfl⟩ : syracuseStep 2682185 = 2011639) B2011639
theorem B7638407 : Blo 1788095 7638407 := bstep (se 1 (by rfl) ⟨5728805, by rfl⟩ : syracuseStep 7638407 = 11457611) B11457611
theorem B4025735 : Blo 1788095 4025735 := bstep (se 1 (by rfl) ⟨3019301, by rfl⟩ : syracuseStep 4025735 = 6038603) B6038603
theorem B1789319 : Blo 1788095 1789319 := bstep (se 1 (by rfl) ⟨1341989, by rfl⟩ : syracuseStep 1789319 = 2683979) B2683979
theorem B1789327 : Blo 1788095 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B1813903 : Blo 1788095 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B6040979 : Blo 1788095 6040979 := bstep (se 1 (by rfl) ⟨4530734, by rfl⟩ : syracuseStep 6040979 = 9061469) B9061469
theorem B2682299 : Blo 1788095 2682299 := bstep (se 1 (by rfl) ⟨2011724, by rfl⟩ : syracuseStep 2682299 = 4023449) B4023449
theorem B1789371 : Blo 1788095 1789371 := bstep (se 1 (by rfl) ⟨1342028, by rfl⟩ : syracuseStep 1789371 = 2684057) B2684057
theorem B6794705 : Blo 1788095 6794705 := bstep (se 2 (by rfl) ⟨2548014, by rfl⟩ : syracuseStep 6794705 = 5096029) B5096029
theorem B2682359 : Blo 1788095 2682359 := bstep (se 1 (by rfl) ⟨2011769, by rfl⟩ : syracuseStep 2682359 = 4023539) B4023539
theorem B1789447 : Blo 1788095 1789447 := bstep (se 1 (by rfl) ⟨1342085, by rfl⟩ : syracuseStep 1789447 = 2684171) B2684171
theorem B2682383 : Blo 1788095 2682383 := bstep (se 1 (by rfl) ⟨2011787, by rfl⟩ : syracuseStep 2682383 = 4023575) B4023575
theorem B1789455 : Blo 1788095 1789455 := bstep (se 1 (by rfl) ⟨1342091, by rfl⟩ : syracuseStep 1789455 = 2684183) B2684183
theorem B3395105 : Blo 1788095 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B3223073 : Blo 1788095 3223073 := bstep (se 2 (by rfl) ⟨1208652, by rfl⟩ : syracuseStep 3223073 = 2417305) B2417305
theorem B3821099 : Blo 1788095 3821099 := bstep (se 1 (by rfl) ⟨2865824, by rfl⟩ : syracuseStep 3821099 = 5731649) B5731649
theorem B2682425 : Blo 1788095 2682425 := bstep (se 2 (by rfl) ⟨1005909, by rfl⟩ : syracuseStep 2682425 = 2011819) B2011819
theorem B4025915 : Blo 1788095 4025915 := bstep (se 1 (by rfl) ⟨3019436, by rfl⟩ : syracuseStep 4025915 = 6038873) B6038873
theorem B1789499 : Blo 1788095 1789499 := bstep (se 1 (by rfl) ⟨1342124, by rfl⟩ : syracuseStep 1789499 = 2684249) B2684249
theorem B18353783 : Blo 1788095 18353783 := bstep (se 1 (by rfl) ⟨13765337, by rfl⟩ : syracuseStep 18353783 = 27530675) B27530675
theorem B2682503 : Blo 1788095 2682503 := bstep (se 1 (by rfl) ⟨2011877, by rfl⟩ : syracuseStep 2682503 = 4023755) B4023755
theorem B1789575 : Blo 1788095 1789575 := bstep (se 1 (by rfl) ⟨1342181, by rfl⟩ : syracuseStep 1789575 = 2684363) B2684363
theorem B1789583 : Blo 1788095 1789583 := bstep (se 1 (by rfl) ⟨1342187, by rfl⟩ : syracuseStep 1789583 = 2684375) B2684375
theorem B2682539 : Blo 1788095 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B4026041 : Blo 1788095 4026041 := bstep (se 2 (by rfl) ⟨1509765, by rfl⟩ : syracuseStep 4026041 = 3019531) B3019531
theorem B1789627 : Blo 1788095 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B2682569 : Blo 1788095 2682569 := bstep (se 2 (by rfl) ⟨1005963, by rfl⟩ : syracuseStep 2682569 = 2011927) B2011927
theorem B1789703 : Blo 1788095 1789703 := bstep (se 1 (by rfl) ⟨1342277, by rfl⟩ : syracuseStep 1789703 = 2684555) B2684555
theorem B1789711 : Blo 1788095 1789711 := bstep (se 1 (by rfl) ⟨1342283, by rfl⟩ : syracuseStep 1789711 = 2684567) B2684567
theorem B3395371 : Blo 1788095 3395371 := bstep (se 1 (by rfl) ⟨2546528, by rfl⟩ : syracuseStep 3395371 = 5093057) B5093057
theorem B3018539 : Blo 1788095 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B2682683 : Blo 1788095 2682683 := bstep (se 1 (by rfl) ⟨2012012, by rfl⟩ : syracuseStep 2682683 = 4024025) B4024025
theorem B1789755 : Blo 1788095 1789755 := bstep (se 1 (by rfl) ⟨1342316, by rfl⟩ : syracuseStep 1789755 = 2684633) B2684633
theorem B2682743 : Blo 1788095 2682743 := bstep (se 1 (by rfl) ⟨2012057, by rfl⟩ : syracuseStep 2682743 = 4024115) B4024115
theorem B2150263 : Blo 1788095 2150263 := bstep (se 1 (by rfl) ⟨1612697, by rfl⟩ : syracuseStep 2150263 = 3225395) B3225395
theorem B1789831 : Blo 1788095 1789831 := bstep (se 1 (by rfl) ⟨1342373, by rfl⟩ : syracuseStep 1789831 = 2684747) B2684747
theorem B2682767 : Blo 1788095 2682767 := bstep (se 1 (by rfl) ⟨2012075, by rfl⟩ : syracuseStep 2682767 = 4024151) B4024151
theorem B1789839 : Blo 1788095 1789839 := bstep (se 1 (by rfl) ⟨1342379, by rfl⟩ : syracuseStep 1789839 = 2684759) B2684759
theorem B6795161 : Blo 1788095 6795161 := bstep (se 2 (by rfl) ⟨2548185, by rfl⟩ : syracuseStep 6795161 = 5096371) B5096371
theorem B2682809 : Blo 1788095 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B10186681 : Blo 1788095 10186681 := bstep (se 2 (by rfl) ⟨3820005, by rfl⟩ : syracuseStep 10186681 = 7640011) B7640011
theorem B1789883 : Blo 1788095 1789883 := bstep (se 1 (by rfl) ⟨1342412, by rfl⟩ : syracuseStep 1789883 = 2684825) B2684825
theorem B2265079 : Blo 1788095 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B2682887 : Blo 1788095 2682887 := bstep (se 1 (by rfl) ⟨2012165, by rfl⟩ : syracuseStep 2682887 = 4024331) B4024331
theorem B1789959 : Blo 1788095 1789959 := bstep (se 1 (by rfl) ⟨1342469, by rfl⟩ : syracuseStep 1789959 = 2684939) B2684939
theorem B38686733 : Blo 1788095 38686733 := bstep (se 3 (by rfl) ⟨7253762, by rfl⟩ : syracuseStep 38686733 = 14507525) B14507525
theorem B4026383 : Blo 1788095 4026383 := bstep (se 1 (by rfl) ⟨3019787, by rfl⟩ : syracuseStep 4026383 = 6039575) B6039575
theorem B1789967 : Blo 1788095 1789967 := bstep (se 1 (by rfl) ⟨1342475, by rfl⟩ : syracuseStep 1789967 = 2684951) B2684951
theorem B9056285 : Blo 1788095 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B4026401 : Blo 1788095 4026401 := bstep (se 2 (by rfl) ⟨1509900, by rfl⟩ : syracuseStep 4026401 = 3019801) B3019801
theorem B2682923 : Blo 1788095 2682923 := bstep (se 1 (by rfl) ⟨2012192, by rfl⟩ : syracuseStep 2682923 = 4024385) B4024385
theorem B1790011 : Blo 1788095 1790011 := bstep (se 1 (by rfl) ⟨1342508, by rfl⟩ : syracuseStep 1790011 = 2685017) B2685017
theorem B2682953 : Blo 1788095 2682953 := bstep (se 2 (by rfl) ⟨1006107, by rfl⟩ : syracuseStep 2682953 = 2012215) B2012215
theorem B1790087 : Blo 1788095 1790087 := bstep (se 1 (by rfl) ⟨1342565, by rfl⟩ : syracuseStep 1790087 = 2685131) B2685131
theorem B1790095 : Blo 1788095 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B3018937 : Blo 1788095 3018937 := bstep (se 2 (by rfl) ⟨1132101, by rfl⟩ : syracuseStep 3018937 = 2264203) B2264203
theorem B2683067 : Blo 1788095 2683067 := bstep (se 1 (by rfl) ⟨2012300, by rfl⟩ : syracuseStep 2683067 = 4024601) B4024601
theorem B2683127 : Blo 1788095 2683127 := bstep (se 1 (by rfl) ⟨2012345, by rfl⟩ : syracuseStep 2683127 = 4024691) B4024691
theorem B4526351 : Blo 1788095 4526351 := bstep (se 1 (by rfl) ⟨3394763, by rfl⟩ : syracuseStep 4526351 = 6789527) B6789527
theorem B2683151 : Blo 1788095 2683151 := bstep (se 1 (by rfl) ⟨2012363, by rfl⟩ : syracuseStep 2683151 = 4024727) B4024727
theorem B5165327 : Blo 1788095 5165327 := bstep (se 1 (by rfl) ⟨3873995, by rfl⟩ : syracuseStep 5165327 = 7747991) B7747991
theorem B2683193 : Blo 1788095 2683193 := bstep (se 2 (by rfl) ⟨1006197, by rfl⟩ : syracuseStep 2683193 = 2012395) B2012395
theorem B2265403 : Blo 1788095 2265403 := bstep (se 1 (by rfl) ⟨1699052, by rfl⟩ : syracuseStep 2265403 = 3398105) B3398105
theorem B4026743 : Blo 1788095 4026743 := bstep (se 1 (by rfl) ⟨3020057, by rfl⟩ : syracuseStep 4026743 = 6040115) B6040115
theorem B2683271 : Blo 1788095 2683271 := bstep (se 1 (by rfl) ⟨2012453, by rfl⟩ : syracuseStep 2683271 = 4024907) B4024907
theorem B2683307 : Blo 1788095 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B2683337 : Blo 1788095 2683337 := bstep (se 2 (by rfl) ⟨1006251, by rfl⟩ : syracuseStep 2683337 = 2012503) B2012503
theorem B9056771 : Blo 1788095 9056771 := bstep (se 1 (by rfl) ⟨6792578, by rfl⟩ : syracuseStep 9056771 = 13585157) B13585157
theorem B4026923 : Blo 1788095 4026923 := bstep (se 1 (by rfl) ⟨3020192, by rfl⟩ : syracuseStep 4026923 = 6040385) B6040385
theorem B2683451 : Blo 1788095 2683451 := bstep (se 1 (by rfl) ⟨2012588, by rfl⟩ : syracuseStep 2683451 = 4025177) B4025177
theorem B15290957 : Blo 1788095 15290957 := bstep (se 3 (by rfl) ⟨2867054, by rfl⟩ : syracuseStep 15290957 = 5734109) B5734109
theorem B2683511 : Blo 1788095 2683511 := bstep (se 1 (by rfl) ⟨2012633, by rfl⟩ : syracuseStep 2683511 = 4025267) B4025267
theorem B5165687 : Blo 1788095 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B2011783 : Blo 1788095 2011783 := bstep (se 1 (by rfl) ⟨1508837, by rfl⟩ : syracuseStep 2011783 = 3017675) B3017675
theorem B2683535 : Blo 1788095 2683535 := bstep (se 1 (by rfl) ⟨2012651, by rfl⟩ : syracuseStep 2683535 = 4025303) B4025303
theorem B46453429 : Blo 1788095 46453429 := bstep (se 5 (by rfl) ⟨2177504, by rfl⟩ : syracuseStep 46453429 = 4355009) B4355009
theorem B2683577 : Blo 1788095 2683577 := bstep (se 2 (by rfl) ⟨1006341, by rfl⟩ : syracuseStep 2683577 = 2012683) B2012683
theorem B2683655 : Blo 1788095 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B2683691 : Blo 1788095 2683691 := bstep (se 1 (by rfl) ⟨2012768, by rfl⟩ : syracuseStep 2683691 = 4025537) B4025537
theorem B4969259 : Blo 1788095 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B9433907 : Blo 1788095 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B2011963 : Blo 1788095 2011963 := bstep (se 1 (by rfl) ⟨1508972, by rfl⟩ : syracuseStep 2011963 = 3017945) B3017945
theorem B2683721 : Blo 1788095 2683721 := bstep (se 2 (by rfl) ⟨1006395, by rfl⟩ : syracuseStep 2683721 = 2012791) B2012791
theorem B3019639 : Blo 1788095 3019639 := bstep (se 1 (by rfl) ⟨2264729, by rfl⟩ : syracuseStep 3019639 = 4529459) B4529459
theorem B3396487 : Blo 1788095 3396487 := bstep (se 1 (by rfl) ⟨2547365, by rfl⟩ : syracuseStep 3396487 = 5094731) B5094731
theorem B4027283 : Blo 1788095 4027283 := bstep (se 1 (by rfl) ⟨3020462, by rfl⟩ : syracuseStep 4027283 = 6040925) B6040925
theorem B17200025 : Blo 1788095 17200025 := bstep (se 2 (by rfl) ⟨6450009, by rfl⟩ : syracuseStep 17200025 = 12900019) B12900019
theorem B2683835 : Blo 1788095 2683835 := bstep (se 1 (by rfl) ⟨2012876, by rfl⟩ : syracuseStep 2683835 = 4025753) B4025753
theorem B4527049 : Blo 1788095 4527049 := bstep (se 2 (by rfl) ⟨1697643, by rfl⟩ : syracuseStep 4527049 = 3395287) B3395287
theorem B4027337 : Blo 1788095 4027337 := bstep (se 2 (by rfl) ⟨1510251, by rfl⟩ : syracuseStep 4027337 = 3020503) B3020503
theorem B2683895 : Blo 1788095 2683895 := bstep (se 1 (by rfl) ⟨2012921, by rfl⟩ : syracuseStep 2683895 = 4025843) B4025843
theorem B2683919 : Blo 1788095 2683919 := bstep (se 1 (by rfl) ⟨2012939, by rfl⟩ : syracuseStep 2683919 = 4025879) B4025879
theorem B10073117 : Blo 1788095 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B6796331 : Blo 1788095 6796331 := bstep (se 1 (by rfl) ⟨5097248, by rfl⟩ : syracuseStep 6796331 = 10194497) B10194497
theorem B2683961 : Blo 1788095 2683961 := bstep (se 2 (by rfl) ⟨1006485, by rfl⟩ : syracuseStep 2683961 = 2012971) B2012971
theorem B3019835 : Blo 1788095 3019835 := bstep (se 1 (by rfl) ⟨2264876, by rfl⟩ : syracuseStep 3019835 = 4529753) B4529753
theorem B13579325 : Blo 1788095 13579325 := bstep (se 3 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 13579325 = 5092247) B5092247
theorem B4527191 : Blo 1788095 4527191 := bstep (se 1 (by rfl) ⟨3395393, by rfl⟩ : syracuseStep 4527191 = 6790787) B6790787
theorem B7640183 : Blo 1788095 7640183 := bstep (se 1 (by rfl) ⟨5730137, by rfl⟩ : syracuseStep 7640183 = 11460275) B11460275
theorem B2684039 : Blo 1788095 2684039 := bstep (se 1 (by rfl) ⟨2013029, by rfl⟩ : syracuseStep 2684039 = 4026059) B4026059
theorem B2684075 : Blo 1788095 2684075 := bstep (se 1 (by rfl) ⟨2013056, by rfl⟩ : syracuseStep 2684075 = 4026113) B4026113
theorem B2684105 : Blo 1788095 2684105 := bstep (se 2 (by rfl) ⟨1006539, by rfl⟩ : syracuseStep 2684105 = 2013079) B2013079
theorem B2012431 : Blo 1788095 2012431 := bstep (se 1 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 2012431 = 3018647) B3018647
theorem B3626299 : Blo 1788095 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B2684219 : Blo 1788095 2684219 := bstep (se 1 (by rfl) ⟨2013164, by rfl⟩ : syracuseStep 2684219 = 4026329) B4026329
theorem B9565499 : Blo 1788095 9565499 := bstep (se 1 (by rfl) ⟨7174124, by rfl⟩ : syracuseStep 9565499 = 14348249) B14348249
theorem B2684279 : Blo 1788095 2684279 := bstep (se 1 (by rfl) ⟨2013209, by rfl⟩ : syracuseStep 2684279 = 4026419) B4026419
theorem B6034823 : Blo 1788095 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B2684303 : Blo 1788095 2684303 := bstep (se 1 (by rfl) ⟨2013227, by rfl⟩ : syracuseStep 2684303 = 4026455) B4026455
theorem B3397049 : Blo 1788095 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B2684345 : Blo 1788095 2684345 := bstep (se 2 (by rfl) ⟨1006629, by rfl⟩ : syracuseStep 2684345 = 2013259) B2013259
theorem B3020233 : Blo 1788095 3020233 := bstep (se 2 (by rfl) ⟨1132587, by rfl⟩ : syracuseStep 3020233 = 2265175) B2265175
theorem B2684423 : Blo 1788095 2684423 := bstep (se 1 (by rfl) ⟨2013317, by rfl⟩ : syracuseStep 2684423 = 4026635) B4026635
theorem B2684459 : Blo 1788095 2684459 := bstep (se 1 (by rfl) ⟨2013344, by rfl⟩ : syracuseStep 2684459 = 4026689) B4026689
theorem B2684489 : Blo 1788095 2684489 := bstep (se 2 (by rfl) ⟨1006683, by rfl⟩ : syracuseStep 2684489 = 2013367) B2013367
theorem B2684603 : Blo 1788095 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B2684663 : Blo 1788095 2684663 := bstep (se 1 (by rfl) ⟨2013497, by rfl⟩ : syracuseStep 2684663 = 4026995) B4026995
theorem B6035201 : Blo 1788095 6035201 := bstep (se 2 (by rfl) ⟨2263200, by rfl⟩ : syracuseStep 6035201 = 4526401) B4526401
theorem B2012935 : Blo 1788095 2012935 := bstep (se 1 (by rfl) ⟨1509701, by rfl⟩ : syracuseStep 2012935 = 3019403) B3019403
theorem B2684687 : Blo 1788095 2684687 := bstep (se 1 (by rfl) ⟨2013515, by rfl⟩ : syracuseStep 2684687 = 4027031) B4027031
theorem B2684729 : Blo 1788095 2684729 := bstep (se 2 (by rfl) ⟨1006773, by rfl⟩ : syracuseStep 2684729 = 2013547) B2013547
theorem B5093239 : Blo 1788095 5093239 := bstep (se 1 (by rfl) ⟨3819929, by rfl⟩ : syracuseStep 5093239 = 7639859) B7639859
theorem B2684807 : Blo 1788095 2684807 := bstep (se 1 (by rfl) ⟨2013605, by rfl⟩ : syracuseStep 2684807 = 4027211) B4027211
theorem B5093273 : Blo 1788095 5093273 := bstep (se 2 (by rfl) ⟨1909977, by rfl⟩ : syracuseStep 5093273 = 3819955) B3819955
theorem B2684843 : Blo 1788095 2684843 := bstep (se 1 (by rfl) ⟨2013632, by rfl⟩ : syracuseStep 2684843 = 4027265) B4027265
theorem B2013115 : Blo 1788095 2013115 := bstep (se 1 (by rfl) ⟨1509836, by rfl⟩ : syracuseStep 2013115 = 3019673) B3019673
theorem B2684873 : Blo 1788095 2684873 := bstep (se 2 (by rfl) ⟨1006827, by rfl⟩ : syracuseStep 2684873 = 2013655) B2013655
theorem B5093387 : Blo 1788095 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B3872783 : Blo 1788095 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B11458583 : Blo 1788095 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B22919213 : Blo 1788095 22919213 := bstep (se 3 (by rfl) ⟨4297352, by rfl⟩ : syracuseStep 22919213 = 8594705) B8594705
theorem B24492077 : Blo 1788095 24492077 := bstep (se 3 (by rfl) ⟨4592264, by rfl⟩ : syracuseStep 24492077 = 9184529) B9184529
theorem B2684987 : Blo 1788095 2684987 := bstep (se 1 (by rfl) ⟨2013740, by rfl⟩ : syracuseStep 2684987 = 4027481) B4027481
theorem B9058391 : Blo 1788095 9058391 := bstep (se 1 (by rfl) ⟨6793793, by rfl⟩ : syracuseStep 9058391 = 13587587) B13587587
theorem B2685047 : Blo 1788095 2685047 := bstep (se 1 (by rfl) ⟨2013785, by rfl⟩ : syracuseStep 2685047 = 4027571) B4027571
theorem B3225719 : Blo 1788095 3225719 := bstep (se 1 (by rfl) ⟨2419289, by rfl⟩ : syracuseStep 3225719 = 4838579) B4838579
theorem B2865287 : Blo 1788095 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B2685071 : Blo 1788095 2685071 := bstep (se 1 (by rfl) ⟨2013803, by rfl⟩ : syracuseStep 2685071 = 4027607) B4027607
theorem B2685113 : Blo 1788095 2685113 := bstep (se 2 (by rfl) ⟨1006917, by rfl⟩ : syracuseStep 2685113 = 2013835) B2013835
theorem B5732623 : Blo 1788095 5732623 := bstep (se 1 (by rfl) ⟨4299467, by rfl⟩ : syracuseStep 5732623 = 8598935) B8598935
theorem B17422685 : Blo 1788095 17422685 := bstep (se 3 (by rfl) ⟨3266753, by rfl⟩ : syracuseStep 17422685 = 6533507) B6533507
theorem B10328435 : Blo 1788095 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B2013583 : Blo 1788095 2013583 := bstep (se 1 (by rfl) ⟨1510187, by rfl⟩ : syracuseStep 2013583 = 3020375) B3020375
theorem B4299275 : Blo 1788095 4299275 := bstep (se 1 (by rfl) ⟨3224456, by rfl⟩ : syracuseStep 4299275 = 6448913) B6448913
theorem B7256587 : Blo 1788095 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B6036011 : Blo 1788095 6036011 := bstep (se 1 (by rfl) ⟨4527008, by rfl⟩ : syracuseStep 6036011 = 9054017) B9054017
theorem B3398203 : Blo 1788095 3398203 := bstep (se 1 (by rfl) ⟨2548652, by rfl⟩ : syracuseStep 3398203 = 5097305) B5097305
theorem B9058877 : Blo 1788095 9058877 := bstep (se 3 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 9058877 = 3397079) B3397079
theorem B2546363 : Blo 1788095 2546363 := bstep (se 1 (by rfl) ⟨1909772, by rfl⟩ : syracuseStep 2546363 = 3819545) B3819545
theorem B7641857 : Blo 1788095 7641857 := bstep (se 2 (by rfl) ⟨2865696, by rfl⟩ : syracuseStep 7641857 = 5731393) B5731393
theorem B46480445 : Blo 1788095 46480445 := bstep (se 3 (by rfl) ⟨8715083, by rfl⟩ : syracuseStep 46480445 = 17430167) B17430167
theorem B5094515 : Blo 1788095 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B4529267 : Blo 1788095 4529267 := bstep (se 1 (by rfl) ⟨3396950, by rfl⟩ : syracuseStep 4529267 = 6793901) B6793901
theorem B2546807 : Blo 1788095 2546807 := bstep (se 1 (by rfl) ⟨1910105, by rfl⟩ : syracuseStep 2546807 = 3820211) B3820211
theorem B4299911 : Blo 1788095 4299911 := bstep (se 1 (by rfl) ⟨3224933, by rfl⟩ : syracuseStep 4299911 = 6449867) B6449867
theorem B11623625 : Blo 1788095 11623625 := bstep (se 2 (by rfl) ⟨4358859, by rfl⟩ : syracuseStep 11623625 = 8717719) B8717719
theorem B2547001 : Blo 1788095 2547001 := bstep (se 2 (by rfl) ⟨955125, by rfl⟩ : syracuseStep 2547001 = 1910251) B1910251
theorem B21765469 : Blo 1788095 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B5807513 : Blo 1788095 5807513 := bstep (se 2 (by rfl) ⟨2177817, by rfl⟩ : syracuseStep 5807513 = 4355635) B4355635
theorem B5094913 : Blo 1788095 5094913 := bstep (se 2 (by rfl) ⟨1910592, by rfl⟩ : syracuseStep 5094913 = 3821185) B3821185
theorem B3677729 : Blo 1788095 3677729 := bstep (se 2 (by rfl) ⟨1379148, by rfl⟩ : syracuseStep 3677729 = 2758297) B2758297
theorem B5094971 : Blo 1788095 5094971 := bstep (se 1 (by rfl) ⟨3821228, by rfl⟩ : syracuseStep 5094971 = 7642457) B7642457
theorem B4529783 : Blo 1788095 4529783 := bstep (se 1 (by rfl) ⟨3397337, by rfl⟩ : syracuseStep 4529783 = 6794675) B6794675
theorem B5734007 : Blo 1788095 5734007 := bstep (se 1 (by rfl) ⟨4300505, by rfl⟩ : syracuseStep 5734007 = 8601011) B8601011
theorem B11460325 : Blo 1788095 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B627351317 : Blo 1788095 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B2326315 : Blo 1788095 2326315 := bstep (se 1 (by rfl) ⟨1744736, by rfl⟩ : syracuseStep 2326315 = 3489473) B3489473
theorem B46481201 : Blo 1788095 46481201 := bstep (se 2 (by rfl) ⟨17430450, by rfl⟩ : syracuseStep 46481201 = 34860901) B34860901
theorem B6037307 : Blo 1788095 6037307 := bstep (se 1 (by rfl) ⟨4527980, by rfl⟩ : syracuseStep 6037307 = 9055961) B9055961
theorem B8593361 : Blo 1788095 8593361 := bstep (se 2 (by rfl) ⟨3222510, by rfl⟩ : syracuseStep 8593361 = 6445021) B6445021
theorem B2326519 : Blo 1788095 2326519 := bstep (se 1 (by rfl) ⟨1744889, by rfl⟩ : syracuseStep 2326519 = 3489779) B3489779
theorem B6037523 : Blo 1788095 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B5439545 : Blo 1788095 5439545 := bstep (se 2 (by rfl) ⟨2039829, by rfl⟩ : syracuseStep 5439545 = 4079659) B4079659
theorem B26861645 : Blo 1788095 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B12894365 : Blo 1788095 12894365 := bstep (se 3 (by rfl) ⟨2417693, by rfl⟩ : syracuseStep 12894365 = 4835387) B4835387
theorem B6791485 : Blo 1788095 6791485 := bstep (se 3 (by rfl) ⟨1273403, by rfl⟩ : syracuseStep 6791485 = 2546807) B2546807
theorem B6037847 : Blo 1788095 6037847 := bstep (se 1 (by rfl) ⟨4528385, by rfl⟩ : syracuseStep 6037847 = 9056771) B9056771
theorem B7643497 : Blo 1788095 7643497 := bstep (se 2 (by rfl) ⟨2866311, by rfl⟩ : syracuseStep 7643497 = 5732623) B5732623
theorem B9675449 : Blo 1788095 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B4530887 : Blo 1788095 4530887 := bstep (se 1 (by rfl) ⟨3398165, by rfl⟩ : syracuseStep 4530887 = 6796331) B6796331
theorem B9052883 : Blo 1788095 9052883 := bstep (se 1 (by rfl) ⟨6789662, by rfl⟩ : syracuseStep 9052883 = 13579325) B13579325
theorem B4834003 : Blo 1788095 4834003 := bstep (se 1 (by rfl) ⟨3625502, by rfl⟩ : syracuseStep 4834003 = 7251005) B7251005
theorem B4530937 : Blo 1788095 4530937 := bstep (se 2 (by rfl) ⟨1699101, by rfl⟩ : syracuseStep 4530937 = 3398203) B3398203
theorem B4023215 : Blo 1788095 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B20382839 : Blo 1788095 20382839 := bstep (se 1 (by rfl) ⟨15287129, by rfl⟩ : syracuseStep 20382839 = 30574259) B30574259
theorem B4023467 : Blo 1788095 4023467 := bstep (se 1 (by rfl) ⟨3017600, by rfl⟩ : syracuseStep 4023467 = 6035201) B6035201
theorem B15279475 : Blo 1788095 15279475 := bstep (se 1 (by rfl) ⟨11459606, by rfl⟩ : syracuseStep 15279475 = 22919213) B22919213
theorem B16328051 : Blo 1788095 16328051 := bstep (se 1 (by rfl) ⟨12246038, by rfl⟩ : syracuseStep 16328051 = 24492077) B24492077
theorem B6038927 : Blo 1788095 6038927 := bstep (se 1 (by rfl) ⟨4529195, by rfl⟩ : syracuseStep 6038927 = 9058391) B9058391
theorem B1910191 : Blo 1788095 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B4024007 : Blo 1788095 4024007 := bstep (se 1 (by rfl) ⟨3018005, by rfl⟩ : syracuseStep 4024007 = 6036011) B6036011
theorem B6039251 : Blo 1788095 6039251 := bstep (se 1 (by rfl) ⟨4529438, by rfl⟩ : syracuseStep 6039251 = 9058877) B9058877
theorem B4835065 : Blo 1788095 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B6793217 : Blo 1788095 6793217 := bstep (se 2 (by rfl) ⟨2547456, by rfl⟩ : syracuseStep 6793217 = 5094913) B5094913
theorem B2263079 : Blo 1788095 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B1788103 : Blo 1788095 1788103 := bstep (se 1 (by rfl) ⟨1341077, by rfl⟩ : syracuseStep 1788103 = 2682155) B2682155
theorem B1788123 : Blo 1788095 1788123 := bstep (se 1 (by rfl) ⟨1341092, by rfl⟩ : syracuseStep 1788123 = 2682185) B2682185
theorem B1788199 : Blo 1788095 1788199 := bstep (se 1 (by rfl) ⟨1341149, by rfl⟩ : syracuseStep 1788199 = 2682299) B2682299
theorem B15280433 : Blo 1788095 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B5728573 : Blo 1788095 5728573 := bstep (se 3 (by rfl) ⟨1074107, by rfl⟩ : syracuseStep 5728573 = 2148215) B2148215
theorem B1788239 : Blo 1788095 1788239 := bstep (se 1 (by rfl) ⟨1341179, by rfl⟩ : syracuseStep 1788239 = 2682359) B2682359
theorem B1788255 : Blo 1788095 1788255 := bstep (se 1 (by rfl) ⟨1341191, by rfl⟩ : syracuseStep 1788255 = 2682383) B2682383
theorem B2263403 : Blo 1788095 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B2148715 : Blo 1788095 2148715 := bstep (se 1 (by rfl) ⟨1611536, by rfl⟩ : syracuseStep 2148715 = 3223073) B3223073
theorem B1788283 : Blo 1788095 1788283 := bstep (se 1 (by rfl) ⟨1341212, by rfl⟩ : syracuseStep 1788283 = 2682425) B2682425
theorem B1788335 : Blo 1788095 1788335 := bstep (se 1 (by rfl) ⟨1341251, by rfl⟩ : syracuseStep 1788335 = 2682503) B2682503
theorem B1788359 : Blo 1788095 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B1788379 : Blo 1788095 1788379 := bstep (se 1 (by rfl) ⟨1341284, by rfl⟩ : syracuseStep 1788379 = 2682569) B2682569
theorem B1788455 : Blo 1788095 1788455 := bstep (se 1 (by rfl) ⟨1341341, by rfl⟩ : syracuseStep 1788455 = 2682683) B2682683
theorem B4024871 : Blo 1788095 4024871 := bstep (se 1 (by rfl) ⟨3018653, by rfl⟩ : syracuseStep 4024871 = 6037307) B6037307
theorem B1788495 : Blo 1788095 1788495 := bstep (se 1 (by rfl) ⟨1341371, by rfl⟩ : syracuseStep 1788495 = 2682743) B2682743
theorem B1788511 : Blo 1788095 1788511 := bstep (se 1 (by rfl) ⟨1341383, by rfl⟩ : syracuseStep 1788511 = 2682767) B2682767
theorem B1788539 : Blo 1788095 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B5728907 : Blo 1788095 5728907 := bstep (se 1 (by rfl) ⟨4296680, by rfl⟩ : syracuseStep 5728907 = 8593361) B8593361
theorem B1788591 : Blo 1788095 1788591 := bstep (se 1 (by rfl) ⟨1341443, by rfl⟩ : syracuseStep 1788591 = 2682887) B2682887
theorem B25791155 : Blo 1788095 25791155 := bstep (se 1 (by rfl) ⟨19343366, by rfl⟩ : syracuseStep 25791155 = 38686733) B38686733
theorem B1788615 : Blo 1788095 1788615 := bstep (se 1 (by rfl) ⟨1341461, by rfl⟩ : syracuseStep 1788615 = 2682923) B2682923
theorem B1788635 : Blo 1788095 1788635 := bstep (se 1 (by rfl) ⟨1341476, by rfl⟩ : syracuseStep 1788635 = 2682953) B2682953
theorem B1788711 : Blo 1788095 1788711 := bstep (se 1 (by rfl) ⟨1341533, by rfl⟩ : syracuseStep 1788711 = 2683067) B2683067
theorem B24488779 : Blo 1788095 24488779 := bstep (se 1 (by rfl) ⟨18366584, by rfl⟩ : syracuseStep 24488779 = 36733169) B36733169
theorem B1788751 : Blo 1788095 1788751 := bstep (se 1 (by rfl) ⟨1341563, by rfl⟩ : syracuseStep 1788751 = 2683127) B2683127
theorem B3017567 : Blo 1788095 3017567 := bstep (se 1 (by rfl) ⟨2263175, by rfl⟩ : syracuseStep 3017567 = 4526351) B4526351
theorem B1788767 : Blo 1788095 1788767 := bstep (se 1 (by rfl) ⟨1341575, by rfl⟩ : syracuseStep 1788767 = 2683151) B2683151
theorem B4025195 : Blo 1788095 4025195 := bstep (se 1 (by rfl) ⟨3018896, by rfl⟩ : syracuseStep 4025195 = 6037793) B6037793
theorem B6040439 : Blo 1788095 6040439 := bstep (se 1 (by rfl) ⟨4530329, by rfl⟩ : syracuseStep 6040439 = 9060659) B9060659
theorem B1788795 : Blo 1788095 1788795 := bstep (se 1 (by rfl) ⟨1341596, by rfl⟩ : syracuseStep 1788795 = 2683193) B2683193
theorem B4025249 : Blo 1788095 4025249 := bstep (se 2 (by rfl) ⟨1509468, by rfl⟩ : syracuseStep 4025249 = 3018937) B3018937
theorem B9055151 : Blo 1788095 9055151 := bstep (se 1 (by rfl) ⟨6791363, by rfl⟩ : syracuseStep 9055151 = 13582727) B13582727
theorem B1788847 : Blo 1788095 1788847 := bstep (se 1 (by rfl) ⟨1341635, by rfl⟩ : syracuseStep 1788847 = 2683271) B2683271
theorem B1788871 : Blo 1788095 1788871 := bstep (se 1 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 1788871 = 2683307) B2683307
theorem B3058651 : Blo 1788095 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B1788891 : Blo 1788095 1788891 := bstep (se 1 (by rfl) ⟨1341668, by rfl⟩ : syracuseStep 1788891 = 2683337) B2683337
theorem B51604451 : Blo 1788095 51604451 := bstep (se 1 (by rfl) ⟨38703338, by rfl⟩ : syracuseStep 51604451 = 77406677) B77406677
theorem B1788967 : Blo 1788095 1788967 := bstep (se 1 (by rfl) ⟨1341725, by rfl⟩ : syracuseStep 1788967 = 2683451) B2683451
theorem B10193971 : Blo 1788095 10193971 := bstep (se 1 (by rfl) ⟨7645478, by rfl⟩ : syracuseStep 10193971 = 15290957) B15290957
theorem B1789007 : Blo 1788095 1789007 := bstep (se 1 (by rfl) ⟨1341755, by rfl⟩ : syracuseStep 1789007 = 2683511) B2683511
theorem B3443791 : Blo 1788095 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B6040655 : Blo 1788095 6040655 := bstep (se 1 (by rfl) ⟨4530491, by rfl⟩ : syracuseStep 6040655 = 9060983) B9060983
theorem B1789023 : Blo 1788095 1789023 := bstep (se 1 (by rfl) ⟨1341767, by rfl⟩ : syracuseStep 1789023 = 2683535) B2683535
theorem B1789051 : Blo 1788095 1789051 := bstep (se 1 (by rfl) ⟨1341788, by rfl⟩ : syracuseStep 1789051 = 2683577) B2683577
theorem B10882201 : Blo 1788095 10882201 := bstep (se 2 (by rfl) ⟨4080825, by rfl⟩ : syracuseStep 10882201 = 8161651) B8161651
theorem B1789103 : Blo 1788095 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B1789127 : Blo 1788095 1789127 := bstep (se 1 (by rfl) ⟨1341845, by rfl⟩ : syracuseStep 1789127 = 2683691) B2683691
theorem B3312839 : Blo 1788095 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B1789147 : Blo 1788095 1789147 := bstep (se 1 (by rfl) ⟨1341860, by rfl⟩ : syracuseStep 1789147 = 2683721) B2683721
theorem B4025591 : Blo 1788095 4025591 := bstep (se 1 (by rfl) ⟨3019193, by rfl⟩ : syracuseStep 4025591 = 6038387) B6038387
theorem B20655395 : Blo 1788095 20655395 := bstep (se 1 (by rfl) ⟨15491546, by rfl⟩ : syracuseStep 20655395 = 30983093) B30983093
theorem B1789223 : Blo 1788095 1789223 := bstep (se 1 (by rfl) ⟨1341917, by rfl⟩ : syracuseStep 1789223 = 2683835) B2683835
theorem B1789263 : Blo 1788095 1789263 := bstep (se 1 (by rfl) ⟨1341947, by rfl⟩ : syracuseStep 1789263 = 2683895) B2683895
theorem B1789279 : Blo 1788095 1789279 := bstep (se 1 (by rfl) ⟨1341959, by rfl⟩ : syracuseStep 1789279 = 2683919) B2683919
theorem B1789307 : Blo 1788095 1789307 := bstep (se 1 (by rfl) ⟨1341980, by rfl⟩ : syracuseStep 1789307 = 2683961) B2683961
theorem B13774205 : Blo 1788095 13774205 := bstep (se 3 (by rfl) ⟨2582663, by rfl⟩ : syracuseStep 13774205 = 5165327) B5165327
theorem B3018127 : Blo 1788095 3018127 := bstep (se 1 (by rfl) ⟨2263595, by rfl⟩ : syracuseStep 3018127 = 4527191) B4527191
theorem B2682287 : Blo 1788095 2682287 := bstep (se 1 (by rfl) ⟨2011715, by rfl⟩ : syracuseStep 2682287 = 4023431) B4023431
theorem B1789359 : Blo 1788095 1789359 := bstep (se 1 (by rfl) ⟨1342019, by rfl⟩ : syracuseStep 1789359 = 2684039) B2684039
theorem B1789383 : Blo 1788095 1789383 := bstep (se 1 (by rfl) ⟨1342037, by rfl⟩ : syracuseStep 1789383 = 2684075) B2684075
theorem B6041033 : Blo 1788095 6041033 := bstep (se 2 (by rfl) ⟨2265387, by rfl⟩ : syracuseStep 6041033 = 4530775) B4530775
theorem B1789403 : Blo 1788095 1789403 := bstep (se 1 (by rfl) ⟨1342052, by rfl⟩ : syracuseStep 1789403 = 2684105) B2684105
theorem B2682377 : Blo 1788095 2682377 := bstep (se 2 (by rfl) ⟨1005891, by rfl⟩ : syracuseStep 2682377 = 2011783) B2011783
theorem B2682407 : Blo 1788095 2682407 := bstep (se 1 (by rfl) ⟨2011805, by rfl⟩ : syracuseStep 2682407 = 4023611) B4023611
theorem B1789479 : Blo 1788095 1789479 := bstep (se 1 (by rfl) ⟨1342109, by rfl⟩ : syracuseStep 1789479 = 2684219) B2684219
theorem B1789519 : Blo 1788095 1789519 := bstep (se 1 (by rfl) ⟨1342139, by rfl⟩ : syracuseStep 1789519 = 2684279) B2684279
theorem B1789535 : Blo 1788095 1789535 := bstep (se 1 (by rfl) ⟨1342151, by rfl⟩ : syracuseStep 1789535 = 2684303) B2684303
theorem B2682491 : Blo 1788095 2682491 := bstep (se 1 (by rfl) ⟨2011868, by rfl⟩ : syracuseStep 2682491 = 4023737) B4023737
theorem B2264699 : Blo 1788095 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B1789563 : Blo 1788095 1789563 := bstep (se 1 (by rfl) ⟨1342172, by rfl⟩ : syracuseStep 1789563 = 2684345) B2684345
theorem B6794887 : Blo 1788095 6794887 := bstep (se 1 (by rfl) ⟨5096165, by rfl⟩ : syracuseStep 6794887 = 10192331) B10192331
theorem B1789615 : Blo 1788095 1789615 := bstep (se 1 (by rfl) ⟨1342211, by rfl⟩ : syracuseStep 1789615 = 2684423) B2684423
theorem B24489661 : Blo 1788095 24489661 := bstep (se 3 (by rfl) ⟨4591811, by rfl⟩ : syracuseStep 24489661 = 9183623) B9183623
theorem B1789639 : Blo 1788095 1789639 := bstep (se 1 (by rfl) ⟨1342229, by rfl⟩ : syracuseStep 1789639 = 2684459) B2684459
theorem B6041303 : Blo 1788095 6041303 := bstep (se 1 (by rfl) ⟨4530977, by rfl⟩ : syracuseStep 6041303 = 9061955) B9061955
theorem B1789659 : Blo 1788095 1789659 := bstep (se 1 (by rfl) ⟨1342244, by rfl⟩ : syracuseStep 1789659 = 2684489) B2684489
theorem B2682617 : Blo 1788095 2682617 := bstep (se 2 (by rfl) ⟨1005981, by rfl⟩ : syracuseStep 2682617 = 2011963) B2011963
theorem B1789735 : Blo 1788095 1789735 := bstep (se 1 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 1789735 = 2684603) B2684603
theorem B4026185 : Blo 1788095 4026185 := bstep (se 2 (by rfl) ⟨1509819, by rfl⟩ : syracuseStep 4026185 = 3019639) B3019639
theorem B1789775 : Blo 1788095 1789775 := bstep (se 1 (by rfl) ⟨1342331, by rfl⟩ : syracuseStep 1789775 = 2684663) B2684663
theorem B2682719 : Blo 1788095 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B1789791 : Blo 1788095 1789791 := bstep (se 1 (by rfl) ⟨1342343, by rfl⟩ : syracuseStep 1789791 = 2684687) B2684687
theorem B2682731 : Blo 1788095 2682731 := bstep (se 1 (by rfl) ⟨2012048, by rfl⟩ : syracuseStep 2682731 = 4024097) B4024097
theorem B1789819 : Blo 1788095 1789819 := bstep (se 1 (by rfl) ⟨1342364, by rfl⟩ : syracuseStep 1789819 = 2684729) B2684729
theorem B1789871 : Blo 1788095 1789871 := bstep (se 1 (by rfl) ⟨1342403, by rfl⟩ : syracuseStep 1789871 = 2684807) B2684807
theorem B1814447 : Blo 1788095 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B6041519 : Blo 1788095 6041519 := bstep (se 1 (by rfl) ⟨4531139, by rfl⟩ : syracuseStep 6041519 = 9062279) B9062279
theorem B6795191 : Blo 1788095 6795191 := bstep (se 1 (by rfl) ⟨5096393, by rfl⟩ : syracuseStep 6795191 = 10192787) B10192787
theorem B3395515 : Blo 1788095 3395515 := bstep (se 1 (by rfl) ⟨2546636, by rfl⟩ : syracuseStep 3395515 = 5093273) B5093273
theorem B1789895 : Blo 1788095 1789895 := bstep (se 1 (by rfl) ⟨1342421, by rfl⟩ : syracuseStep 1789895 = 2684843) B2684843
theorem B1789915 : Blo 1788095 1789915 := bstep (se 1 (by rfl) ⟨1342436, by rfl⟩ : syracuseStep 1789915 = 2684873) B2684873
theorem B3395591 : Blo 1788095 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B7639055 : Blo 1788095 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B11464733 : Blo 1788095 11464733 := bstep (se 3 (by rfl) ⟨2149637, by rfl⟩ : syracuseStep 11464733 = 4299275) B4299275
theorem B1789991 : Blo 1788095 1789991 := bstep (se 1 (by rfl) ⟨1342493, by rfl⟩ : syracuseStep 1789991 = 2684987) B2684987
theorem B3018809 : Blo 1788095 3018809 := bstep (se 2 (by rfl) ⟨1132053, by rfl⟩ : syracuseStep 3018809 = 2264107) B2264107
theorem B2682959 : Blo 1788095 2682959 := bstep (se 1 (by rfl) ⟨2012219, by rfl⟩ : syracuseStep 2682959 = 4024439) B4024439
theorem B1790031 : Blo 1788095 1790031 := bstep (se 1 (by rfl) ⟨1342523, by rfl⟩ : syracuseStep 1790031 = 2685047) B2685047
theorem B2150479 : Blo 1788095 2150479 := bstep (se 1 (by rfl) ⟨1612859, by rfl⟩ : syracuseStep 2150479 = 3225719) B3225719
theorem B1790047 : Blo 1788095 1790047 := bstep (se 1 (by rfl) ⟨1342535, by rfl⟩ : syracuseStep 1790047 = 2685071) B2685071
theorem B5730419 : Blo 1788095 5730419 := bstep (se 1 (by rfl) ⟨4297814, by rfl⟩ : syracuseStep 5730419 = 8595629) B8595629
theorem B18362483 : Blo 1788095 18362483 := bstep (se 1 (by rfl) ⟨13771862, by rfl⟩ : syracuseStep 18362483 = 27543725) B27543725
theorem B1790075 : Blo 1788095 1790075 := bstep (se 1 (by rfl) ⟨1342556, by rfl⟩ : syracuseStep 1790075 = 2685113) B2685113
theorem B2683079 : Blo 1788095 2683079 := bstep (se 1 (by rfl) ⟨2012309, by rfl⟩ : syracuseStep 2683079 = 4024619) B4024619
theorem B6885623 : Blo 1788095 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B2683241 : Blo 1788095 2683241 := bstep (se 2 (by rfl) ⟨1006215, by rfl⟩ : syracuseStep 2683241 = 2012431) B2012431
theorem B3396001 : Blo 1788095 3396001 := bstep (se 2 (by rfl) ⟨1273500, by rfl⟩ : syracuseStep 3396001 = 2547001) B2547001
theorem B2683319 : Blo 1788095 2683319 := bstep (se 1 (by rfl) ⟨2012489, by rfl⟩ : syracuseStep 2683319 = 4024979) B4024979
theorem B29020625 : Blo 1788095 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B2683355 : Blo 1788095 2683355 := bstep (se 1 (by rfl) ⟨2012516, by rfl⟩ : syracuseStep 2683355 = 4025033) B4025033
theorem B3224083 : Blo 1788095 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B4026977 : Blo 1788095 4026977 := bstep (se 2 (by rfl) ⟨1510116, by rfl⟩ : syracuseStep 4026977 = 3020233) B3020233
theorem B30986963 : Blo 1788095 30986963 := bstep (se 1 (by rfl) ⟨23240222, by rfl⟩ : syracuseStep 30986963 = 46480445) B46480445
theorem B5092055 : Blo 1788095 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B3396343 : Blo 1788095 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B3019511 : Blo 1788095 3019511 := bstep (se 1 (by rfl) ⟨2264633, by rfl⟩ : syracuseStep 3019511 = 4529267) B4529267
theorem B2011999 : Blo 1788095 2011999 := bstep (se 1 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 2011999 = 3017999) B3017999
theorem B5092271 : Blo 1788095 5092271 := bstep (se 1 (by rfl) ⟨3819203, by rfl⟩ : syracuseStep 5092271 = 7638407) B7638407
theorem B2683823 : Blo 1788095 2683823 := bstep (se 1 (by rfl) ⟨2012867, by rfl⟩ : syracuseStep 2683823 = 4025735) B4025735
theorem B4027319 : Blo 1788095 4027319 := bstep (se 1 (by rfl) ⟨3020489, by rfl⟩ : syracuseStep 4027319 = 6040979) B6040979
theorem B3871675 : Blo 1788095 3871675 := bstep (se 1 (by rfl) ⟨2903756, by rfl⟩ : syracuseStep 3871675 = 5807513) B5807513
theorem B2683913 : Blo 1788095 2683913 := bstep (se 2 (by rfl) ⟨1006467, by rfl⟩ : syracuseStep 2683913 = 2012935) B2012935
theorem B3396647 : Blo 1788095 3396647 := bstep (se 1 (by rfl) ⟨2547485, by rfl⟩ : syracuseStep 3396647 = 5094971) B5094971
theorem B2683943 : Blo 1788095 2683943 := bstep (se 1 (by rfl) ⟨2012957, by rfl⟩ : syracuseStep 2683943 = 4025915) B4025915
theorem B4527161 : Blo 1788095 4527161 := bstep (se 2 (by rfl) ⟨1697685, by rfl⟩ : syracuseStep 4527161 = 3395371) B3395371
theorem B3101753 : Blo 1788095 3101753 := bstep (se 2 (by rfl) ⟨1163157, by rfl⟩ : syracuseStep 3101753 = 2326315) B2326315
theorem B6796345 : Blo 1788095 6796345 := bstep (se 2 (by rfl) ⟨2548629, by rfl⟩ : syracuseStep 6796345 = 5097259) B5097259
theorem B12235855 : Blo 1788095 12235855 := bstep (se 1 (by rfl) ⟨9176891, by rfl⟩ : syracuseStep 12235855 = 18353783) B18353783
theorem B3019855 : Blo 1788095 3019855 := bstep (se 1 (by rfl) ⟨2264891, by rfl⟩ : syracuseStep 3019855 = 4529783) B4529783
theorem B3822671 : Blo 1788095 3822671 := bstep (se 1 (by rfl) ⟨2867003, by rfl⟩ : syracuseStep 3822671 = 5734007) B5734007
theorem B2684027 : Blo 1788095 2684027 := bstep (se 1 (by rfl) ⟨2013020, by rfl⟩ : syracuseStep 2684027 = 4026041) B4026041
theorem B2012359 : Blo 1788095 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B30987467 : Blo 1788095 30987467 := bstep (se 1 (by rfl) ⟨23240600, by rfl⟩ : syracuseStep 30987467 = 46481201) B46481201
theorem B2684153 : Blo 1788095 2684153 := bstep (se 2 (by rfl) ⟨1006557, by rfl⟩ : syracuseStep 2684153 = 2013115) B2013115
theorem B3102025 : Blo 1788095 3102025 := bstep (se 2 (by rfl) ⟨1163259, by rfl⟩ : syracuseStep 3102025 = 2326519) B2326519
theorem B3020105 : Blo 1788095 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B2684255 : Blo 1788095 2684255 := bstep (se 1 (by rfl) ⟨2013191, by rfl⟩ : syracuseStep 2684255 = 4026383) B4026383
theorem B6796649 : Blo 1788095 6796649 := bstep (se 2 (by rfl) ⟨2548743, by rfl⟩ : syracuseStep 6796649 = 5097487) B5097487
theorem B2684267 : Blo 1788095 2684267 := bstep (se 1 (by rfl) ⟨2013200, by rfl⟩ : syracuseStep 2684267 = 4026401) B4026401
theorem B10327421 : Blo 1788095 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B6034931 : Blo 1788095 6034931 := bstep (se 1 (by rfl) ⟨4526198, by rfl⟩ : syracuseStep 6034931 = 9052397) B9052397
theorem B2684495 : Blo 1788095 2684495 := bstep (se 1 (by rfl) ⟨2013371, by rfl⟩ : syracuseStep 2684495 = 4026743) B4026743
theorem B10327675 : Blo 1788095 10327675 := bstep (se 1 (by rfl) ⟨7745756, by rfl⟩ : syracuseStep 10327675 = 15491513) B15491513
theorem B39229109 : Blo 1788095 39229109 := bstep (se 5 (by rfl) ⟨1838864, by rfl⟩ : syracuseStep 39229109 = 3677729) B3677729
theorem B2684615 : Blo 1788095 2684615 := bstep (se 1 (by rfl) ⟨2013461, by rfl⟩ : syracuseStep 2684615 = 4026923) B4026923
theorem B5093113 : Blo 1788095 5093113 := bstep (se 2 (by rfl) ⟨1909917, by rfl⟩ : syracuseStep 5093113 = 3819835) B3819835
theorem B3020537 : Blo 1788095 3020537 := bstep (se 2 (by rfl) ⟨1132701, by rfl⟩ : syracuseStep 3020537 = 2265403) B2265403
theorem B2684777 : Blo 1788095 2684777 := bstep (se 2 (by rfl) ⟨1006791, by rfl⟩ : syracuseStep 2684777 = 2013583) B2013583
theorem B6289271 : Blo 1788095 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B3020719 : Blo 1788095 3020719 := bstep (se 1 (by rfl) ⟨2265539, by rfl⟩ : syracuseStep 3020719 = 4531079) B4531079
theorem B2684855 : Blo 1788095 2684855 := bstep (se 1 (by rfl) ⟨2013641, by rfl⟩ : syracuseStep 2684855 = 4027283) B4027283
theorem B11466683 : Blo 1788095 11466683 := bstep (se 1 (by rfl) ⟨8600012, by rfl⟩ : syracuseStep 11466683 = 17200025) B17200025
theorem B2684891 : Blo 1788095 2684891 := bstep (se 1 (by rfl) ⟨2013668, by rfl⟩ : syracuseStep 2684891 = 4027337) B4027337
theorem B6035471 : Blo 1788095 6035471 := bstep (se 1 (by rfl) ⟨4526603, by rfl⟩ : syracuseStep 6035471 = 9053207) B9053207
theorem B2013223 : Blo 1788095 2013223 := bstep (se 1 (by rfl) ⟨1509917, by rfl⟩ : syracuseStep 2013223 = 3019835) B3019835
theorem B5093455 : Blo 1788095 5093455 := bstep (se 1 (by rfl) ⟨3820091, by rfl⟩ : syracuseStep 5093455 = 7640183) B7640183
theorem B25507997 : Blo 1788095 25507997 := bstep (se 3 (by rfl) ⟨4782749, by rfl⟩ : syracuseStep 25507997 = 9565499) B9565499
theorem B61937905 : Blo 1788095 61937905 := bstep (se 2 (by rfl) ⟨23226714, by rfl⟩ : syracuseStep 61937905 = 46453429) B46453429
theorem B3627337 : Blo 1788095 3627337 := bstep (se 2 (by rfl) ⟨1360251, by rfl⟩ : syracuseStep 3627337 = 2720503) B2720503
theorem B4528649 : Blo 1788095 4528649 := bstep (se 2 (by rfl) ⟨1698243, by rfl⟩ : syracuseStep 4528649 = 3396487) B3396487
theorem B2546255 : Blo 1788095 2546255 := bstep (se 1 (by rfl) ⟨1909691, by rfl⟩ : syracuseStep 2546255 = 3819383) B3819383
theorem B6036065 : Blo 1788095 6036065 := bstep (se 2 (by rfl) ⟨2263524, by rfl⟩ : syracuseStep 6036065 = 4527049) B4527049
theorem B3627767 : Blo 1788095 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B10189597 : Blo 1788095 10189597 := bstep (se 3 (by rfl) ⟨1910549, by rfl⟩ : syracuseStep 10189597 = 3821099) B3821099
theorem B11615123 : Blo 1788095 11615123 := bstep (se 1 (by rfl) ⟨8711342, by rfl⟩ : syracuseStep 11615123 = 17422685) B17422685
theorem B12893185 : Blo 1788095 12893185 := bstep (se 2 (by rfl) ⟨4834944, by rfl⟩ : syracuseStep 12893185 = 9669889) B9669889
theorem B6790301 : Blo 1788095 6790301 := bstep (se 3 (by rfl) ⟨1273181, by rfl⟩ : syracuseStep 6790301 = 2546363) B2546363
theorem B5094571 : Blo 1788095 5094571 := bstep (se 1 (by rfl) ⟨3820928, by rfl⟩ : syracuseStep 5094571 = 7641857) B7641857
theorem B6446479 : Blo 1788095 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B9674149 : Blo 1788095 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B2866607 : Blo 1788095 2866607 := bstep (se 1 (by rfl) ⟨2149955, by rfl⟩ : syracuseStep 2866607 = 4299911) B4299911
theorem B7749083 : Blo 1788095 7749083 := bstep (se 1 (by rfl) ⟨5811812, by rfl⟩ : syracuseStep 7749083 = 11623625) B11623625
theorem B6888947 : Blo 1788095 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B4529803 : Blo 1788095 4529803 := bstep (se 1 (by rfl) ⟨3397352, by rfl⟩ : syracuseStep 4529803 = 6794705) B6794705
theorem B6790985 : Blo 1788095 6790985 := bstep (se 2 (by rfl) ⟨2546619, by rfl⟩ : syracuseStep 6790985 = 5093239) B5093239
theorem B2867017 : Blo 1788095 2867017 := bstep (se 2 (by rfl) ⟨1075131, by rfl⟩ : syracuseStep 2867017 = 2150263) B2150263
theorem B418234211 : Blo 1788095 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B13582241 : Blo 1788095 13582241 := bstep (se 2 (by rfl) ⟨5093340, by rfl⟩ : syracuseStep 13582241 = 10186681) B10186681
theorem B4530107 : Blo 1788095 4530107 := bstep (se 1 (by rfl) ⟨3397580, by rfl⟩ : syracuseStep 4530107 = 6795161) B6795161
theorem B7643155 : Blo 1788095 7643155 := bstep (se 1 (by rfl) ⟨5732366, by rfl⟩ : syracuseStep 7643155 = 11464733) B11464733
theorem B6791273 : Blo 1788095 6791273 := bstep (se 2 (by rfl) ⟨2546727, by rfl⟩ : syracuseStep 6791273 = 5093455) B5093455
theorem B71631053 : Blo 1788095 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B82583873 : Blo 1788095 82583873 := bstep (se 2 (by rfl) ⟨30968952, by rfl⟩ : syracuseStep 82583873 = 61937905) B61937905
theorem B11469221 : Blo 1788095 11469221 := bstep (se 4 (by rfl) ⟨1075239, by rfl⟩ : syracuseStep 11469221 = 2150479) B2150479
theorem B10191329 : Blo 1788095 10191329 := bstep (se 2 (by rfl) ⟨3821748, by rfl⟩ : syracuseStep 10191329 = 7643497) B7643497
theorem B4531099 : Blo 1788095 4531099 := bstep (se 1 (by rfl) ⟨3398324, by rfl⟩ : syracuseStep 4531099 = 6796649) B6796649
theorem B4023287 : Blo 1788095 4023287 := bstep (se 1 (by rfl) ⟨3017465, by rfl⟩ : syracuseStep 4023287 = 6034931) B6034931
theorem B5162233 : Blo 1788095 5162233 := bstep (se 2 (by rfl) ⟨1935837, by rfl⟩ : syracuseStep 5162233 = 3871675) B3871675
theorem B7644455 : Blo 1788095 7644455 := bstep (se 1 (by rfl) ⟨5733341, by rfl⟩ : syracuseStep 7644455 = 11466683) B11466683
theorem B4023647 : Blo 1788095 4023647 := bstep (se 1 (by rfl) ⟨3017735, by rfl⟩ : syracuseStep 4023647 = 6035471) B6035471
theorem B13591961 : Blo 1788095 13591961 := bstep (se 2 (by rfl) ⟨5096985, by rfl⟩ : syracuseStep 13591961 = 10193971) B10193971
theorem B9061793 : Blo 1788095 9061793 := bstep (se 2 (by rfl) ⟨3398172, by rfl⟩ : syracuseStep 9061793 = 6796345) B6796345
theorem B14509601 : Blo 1788095 14509601 := bstep (se 2 (by rfl) ⟨5441100, by rfl⟩ : syracuseStep 14509601 = 10882201) B10882201
theorem B6792761 : Blo 1788095 6792761 := bstep (se 2 (by rfl) ⟨2547285, by rfl⟩ : syracuseStep 6792761 = 5094571) B5094571
theorem B6039197 : Blo 1788095 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B4024043 : Blo 1788095 4024043 := bstep (se 1 (by rfl) ⟨3018032, by rfl⟩ : syracuseStep 4024043 = 6036065) B6036065
theorem B2418511 : Blo 1788095 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B4024169 : Blo 1788095 4024169 := bstep (se 2 (by rfl) ⟨1509063, by rfl⟩ : syracuseStep 4024169 = 3018127) B3018127
theorem B8595305 : Blo 1788095 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B7743415 : Blo 1788095 7743415 := bstep (se 1 (by rfl) ⟨5807561, by rfl⟩ : syracuseStep 7743415 = 11615123) B11615123
theorem B6039737 : Blo 1788095 6039737 := bstep (se 2 (by rfl) ⟨2264901, by rfl⟩ : syracuseStep 6039737 = 4529803) B4529803
theorem B1788191 : Blo 1788095 1788191 := bstep (se 1 (by rfl) ⟨1341143, by rfl⟩ : syracuseStep 1788191 = 2682287) B2682287
theorem B1911071 : Blo 1788095 1911071 := bstep (se 1 (by rfl) ⟨1433303, by rfl⟩ : syracuseStep 1911071 = 2866607) B2866607
theorem B1788251 : Blo 1788095 1788251 := bstep (se 1 (by rfl) ⟨1341188, by rfl⟩ : syracuseStep 1788251 = 2682377) B2682377
theorem B1788271 : Blo 1788095 1788271 := bstep (se 1 (by rfl) ⟨1341203, by rfl⟩ : syracuseStep 1788271 = 2682407) B2682407
theorem B1788327 : Blo 1788095 1788327 := bstep (se 1 (by rfl) ⟨1341245, by rfl⟩ : syracuseStep 1788327 = 2682491) B2682491
theorem B1788411 : Blo 1788095 1788411 := bstep (se 1 (by rfl) ⟨1341308, by rfl⟩ : syracuseStep 1788411 = 2682617) B2682617
theorem B1788479 : Blo 1788095 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B1788487 : Blo 1788095 1788487 := bstep (se 1 (by rfl) ⟨1341365, by rfl⟩ : syracuseStep 1788487 = 2682731) B2682731
theorem B9054827 : Blo 1788095 9054827 := bstep (se 1 (by rfl) ⟨6791120, by rfl⟩ : syracuseStep 9054827 = 13582241) B13582241
theorem B2263727 : Blo 1788095 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B4025015 : Blo 1788095 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B1788639 : Blo 1788095 1788639 := bstep (se 1 (by rfl) ⟨1341479, by rfl⟩ : syracuseStep 1788639 = 2682959) B2682959
theorem B3820279 : Blo 1788095 3820279 := bstep (se 1 (by rfl) ⟨2865209, by rfl⟩ : syracuseStep 3820279 = 5730419) B5730419
theorem B12241655 : Blo 1788095 12241655 := bstep (se 1 (by rfl) ⟨9181241, by rfl⟩ : syracuseStep 12241655 = 18362483) B18362483
theorem B8596243 : Blo 1788095 8596243 := bstep (se 1 (by rfl) ⟨6447182, by rfl⟩ : syracuseStep 8596243 = 12894365) B12894365
theorem B1788719 : Blo 1788095 1788719 := bstep (se 1 (by rfl) ⟨1341539, by rfl⟩ : syracuseStep 1788719 = 2683079) B2683079
theorem B4590415 : Blo 1788095 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B10193789 : Blo 1788095 10193789 := bstep (se 3 (by rfl) ⟨1911335, by rfl⟩ : syracuseStep 10193789 = 3822671) B3822671
theorem B4025231 : Blo 1788095 4025231 := bstep (se 1 (by rfl) ⟨3018923, by rfl⟩ : syracuseStep 4025231 = 6037847) B6037847
theorem B1788827 : Blo 1788095 1788827 := bstep (se 1 (by rfl) ⟨1341620, by rfl⟩ : syracuseStep 1788827 = 2683241) B2683241
theorem B1788879 : Blo 1788095 1788879 := bstep (se 1 (by rfl) ⟨1341659, by rfl⟩ : syracuseStep 1788879 = 2683319) B2683319
theorem B1788903 : Blo 1788095 1788903 := bstep (se 1 (by rfl) ⟨1341677, by rfl⟩ : syracuseStep 1788903 = 2683355) B2683355
theorem B9055313 : Blo 1788095 9055313 := bstep (se 2 (by rfl) ⟨3395742, by rfl⟩ : syracuseStep 9055313 = 6791485) B6791485
theorem B4836449 : Blo 1788095 4836449 := bstep (se 2 (by rfl) ⟨1813668, by rfl⟩ : syracuseStep 4836449 = 3627337) B3627337
theorem B6450299 : Blo 1788095 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B3394703 : Blo 1788095 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2682143 : Blo 1788095 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B3394847 : Blo 1788095 3394847 := bstep (se 1 (by rfl) ⟨2546135, by rfl⟩ : syracuseStep 3394847 = 5092271) B5092271
theorem B1789215 : Blo 1788095 1789215 := bstep (se 1 (by rfl) ⟨1341911, by rfl⟩ : syracuseStep 1789215 = 2683823) B2683823
theorem B1789275 : Blo 1788095 1789275 := bstep (se 1 (by rfl) ⟨1341956, by rfl⟩ : syracuseStep 1789275 = 2683913) B2683913
theorem B2264431 : Blo 1788095 2264431 := bstep (se 1 (by rfl) ⟨1698323, by rfl⟩ : syracuseStep 2264431 = 3396647) B3396647
theorem B1789295 : Blo 1788095 1789295 := bstep (se 1 (by rfl) ⟨1341971, by rfl⟩ : syracuseStep 1789295 = 2683943) B2683943
theorem B3018107 : Blo 1788095 3018107 := bstep (se 1 (by rfl) ⟨2263580, by rfl⟩ : syracuseStep 3018107 = 4527161) B4527161
theorem B1789351 : Blo 1788095 1789351 := bstep (se 1 (by rfl) ⟨1342013, by rfl⟩ : syracuseStep 1789351 = 2684027) B2684027
theorem B2682311 : Blo 1788095 2682311 := bstep (se 1 (by rfl) ⟨2011733, by rfl⟩ : syracuseStep 2682311 = 4023467) B4023467
theorem B1789435 : Blo 1788095 1789435 := bstep (se 1 (by rfl) ⟨1342076, by rfl⟩ : syracuseStep 1789435 = 2684153) B2684153
theorem B1789503 : Blo 1788095 1789503 := bstep (se 1 (by rfl) ⟨1342127, by rfl⟩ : syracuseStep 1789503 = 2684255) B2684255
theorem B1789511 : Blo 1788095 1789511 := bstep (se 1 (by rfl) ⟨1342133, by rfl⟩ : syracuseStep 1789511 = 2684267) B2684267
theorem B6884947 : Blo 1788095 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B4025951 : Blo 1788095 4025951 := bstep (se 1 (by rfl) ⟨3019463, by rfl⟩ : syracuseStep 4025951 = 6038927) B6038927
theorem B6041249 : Blo 1788095 6041249 := bstep (se 2 (by rfl) ⟨2265468, by rfl⟩ : syracuseStep 6041249 = 4530937) B4530937
theorem B13586129 : Blo 1788095 13586129 := bstep (se 2 (by rfl) ⟨5094798, by rfl⟩ : syracuseStep 13586129 = 10189597) B10189597
theorem B1789663 : Blo 1788095 1789663 := bstep (se 1 (by rfl) ⟨1342247, by rfl⟩ : syracuseStep 1789663 = 2684495) B2684495
theorem B26152739 : Blo 1788095 26152739 := bstep (se 1 (by rfl) ⟨19614554, by rfl⟩ : syracuseStep 26152739 = 39229109) B39229109
theorem B2682665 : Blo 1788095 2682665 := bstep (se 2 (by rfl) ⟨1005999, by rfl⟩ : syracuseStep 2682665 = 2011999) B2011999
theorem B2682671 : Blo 1788095 2682671 := bstep (se 1 (by rfl) ⟨2012003, by rfl⟩ : syracuseStep 2682671 = 4024007) B4024007
theorem B1789743 : Blo 1788095 1789743 := bstep (se 1 (by rfl) ⟨1342307, by rfl⟩ : syracuseStep 1789743 = 2684615) B2684615
theorem B4026167 : Blo 1788095 4026167 := bstep (se 1 (by rfl) ⟨3019625, by rfl⟩ : syracuseStep 4026167 = 6039251) B6039251
theorem B1789851 : Blo 1788095 1789851 := bstep (se 1 (by rfl) ⟨1342388, by rfl⟩ : syracuseStep 1789851 = 2684777) B2684777
theorem B1789903 : Blo 1788095 1789903 := bstep (se 1 (by rfl) ⟨1342427, by rfl⟩ : syracuseStep 1789903 = 2684855) B2684855
theorem B18370525 : Blo 1788095 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B1789927 : Blo 1788095 1789927 := bstep (se 1 (by rfl) ⟨1342445, by rfl⟩ : syracuseStep 1789927 = 2684891) B2684891
theorem B17190913 : Blo 1788095 17190913 := bstep (se 2 (by rfl) ⟨6446592, by rfl⟩ : syracuseStep 17190913 = 12893185) B12893185
theorem B16314473 : Blo 1788095 16314473 := bstep (se 2 (by rfl) ⟨6117927, by rfl⟩ : syracuseStep 16314473 = 12235855) B12235855
theorem B4026473 : Blo 1788095 4026473 := bstep (se 2 (by rfl) ⟨1509927, by rfl⟩ : syracuseStep 4026473 = 3019855) B3019855
theorem B4591721 : Blo 1788095 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B10186955 : Blo 1788095 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B2683145 : Blo 1788095 2683145 := bstep (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) B2012359
theorem B30552389 : Blo 1788095 30552389 := bstep (se 4 (by rfl) ⟨2864286, by rfl⟩ : syracuseStep 30552389 = 5728573) B5728573
theorem B3019099 : Blo 1788095 3019099 := bstep (se 1 (by rfl) ⟨2264324, by rfl⟩ : syracuseStep 3019099 = 4528649) B4528649
theorem B2683247 : Blo 1788095 2683247 := bstep (se 1 (by rfl) ⟨2012435, by rfl⟩ : syracuseStep 2683247 = 4024871) B4024871
theorem B12898865 : Blo 1788095 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B2011711 : Blo 1788095 2011711 := bstep (se 1 (by rfl) ⟨1508783, by rfl⟩ : syracuseStep 2011711 = 3017567) B3017567
theorem B2683463 : Blo 1788095 2683463 := bstep (se 1 (by rfl) ⟨2012597, by rfl⟩ : syracuseStep 2683463 = 4025195) B4025195
theorem B4026959 : Blo 1788095 4026959 := bstep (se 1 (by rfl) ⟨3020219, by rfl⟩ : syracuseStep 4026959 = 6040439) B6040439
theorem B2683499 : Blo 1788095 2683499 := bstep (se 1 (by rfl) ⟨2012624, by rfl⟩ : syracuseStep 2683499 = 4025249) B4025249
theorem B34402967 : Blo 1788095 34402967 := bstep (se 1 (by rfl) ⟨25802225, by rfl⟩ : syracuseStep 34402967 = 51604451) B51604451
theorem B4027103 : Blo 1788095 4027103 := bstep (se 1 (by rfl) ⟨3020327, by rfl⟩ : syracuseStep 4027103 = 6040655) B6040655
theorem B4526867 : Blo 1788095 4526867 := bstep (se 1 (by rfl) ⟨3395150, by rfl⟩ : syracuseStep 4526867 = 6790301) B6790301
theorem B2208559 : Blo 1788095 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B2683727 : Blo 1788095 2683727 := bstep (se 1 (by rfl) ⟨2012795, by rfl⟩ : syracuseStep 2683727 = 4025591) B4025591
theorem B4027355 : Blo 1788095 4027355 := bstep (se 1 (by rfl) ⟨3020516, by rfl⟩ : syracuseStep 4027355 = 6041033) B6041033
theorem B5166055 : Blo 1788095 5166055 := bstep (se 1 (by rfl) ⟨3874541, by rfl⟩ : syracuseStep 5166055 = 7749083) B7749083
theorem B3822689 : Blo 1788095 3822689 := bstep (se 2 (by rfl) ⟨1433508, by rfl⟩ : syracuseStep 3822689 = 2867017) B2867017
theorem B4838525 : Blo 1788095 4838525 := bstep (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) B1814447
theorem B4027535 : Blo 1788095 4027535 := bstep (se 1 (by rfl) ⟨3020651, by rfl⟩ : syracuseStep 4027535 = 6041303) B6041303
theorem B4527323 : Blo 1788095 4527323 := bstep (se 1 (by rfl) ⟨3395492, by rfl⟩ : syracuseStep 4527323 = 6790985) B6790985
theorem B2684123 : Blo 1788095 2684123 := bstep (se 1 (by rfl) ⟨2013092, by rfl⟩ : syracuseStep 2684123 = 4026185) B4026185
theorem B4027625 : Blo 1788095 4027625 := bstep (se 2 (by rfl) ⟨1510359, by rfl⟩ : syracuseStep 4027625 = 3020719) B3020719
theorem B4527353 : Blo 1788095 4527353 := bstep (se 2 (by rfl) ⟨1697757, by rfl⟩ : syracuseStep 4527353 = 3395515) B3395515
theorem B4027679 : Blo 1788095 4027679 := bstep (se 1 (by rfl) ⟨3020759, by rfl⟩ : syracuseStep 4027679 = 6041519) B6041519
theorem B3020071 : Blo 1788095 3020071 := bstep (se 1 (by rfl) ⟨2265053, by rfl⟩ : syracuseStep 3020071 = 4530107) B4530107
theorem B5092703 : Blo 1788095 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B3626363 : Blo 1788095 3626363 := bstep (se 1 (by rfl) ⟨2719772, by rfl⟩ : syracuseStep 3626363 = 5439545) B5439545
theorem B2012539 : Blo 1788095 2012539 := bstep (se 1 (by rfl) ⟨1509404, by rfl⟩ : syracuseStep 2012539 = 3018809) B3018809
theorem B2684297 : Blo 1788095 2684297 := bstep (se 2 (by rfl) ⟨1006611, by rfl⟩ : syracuseStep 2684297 = 2013223) B2013223
theorem B6034877 : Blo 1788095 6034877 := bstep (se 3 (by rfl) ⟨1131539, by rfl⟩ : syracuseStep 6034877 = 2263079) B2263079
theorem B8271341 : Blo 1788095 8271341 := bstep (se 3 (by rfl) ⟨1550876, by rfl⟩ : syracuseStep 8271341 = 3101753) B3101753
theorem B19347083 : Blo 1788095 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B2684651 : Blo 1788095 2684651 := bstep (se 1 (by rfl) ⟨2013488, by rfl⟩ : syracuseStep 2684651 = 4026977) B4026977
theorem B3020591 : Blo 1788095 3020591 := bstep (se 1 (by rfl) ⟨2265443, by rfl⟩ : syracuseStep 3020591 = 4530887) B4530887
theorem B6035255 : Blo 1788095 6035255 := bstep (se 1 (by rfl) ⟨4526441, by rfl⟩ : syracuseStep 6035255 = 9052883) B9052883
theorem B20657975 : Blo 1788095 20657975 := bstep (se 1 (by rfl) ⟨15493481, by rfl⟩ : syracuseStep 20657975 = 30986963) B30986963
theorem B2864953 : Blo 1788095 2864953 := bstep (se 2 (by rfl) ⟨1074357, by rfl⟩ : syracuseStep 2864953 = 2148715) B2148715
theorem B2013007 : Blo 1788095 2013007 := bstep (se 1 (by rfl) ⟨1509755, by rfl⟩ : syracuseStep 2013007 = 3019511) B3019511
theorem B4528001 : Blo 1788095 4528001 := bstep (se 2 (by rfl) ⟨1698000, by rfl⟩ : syracuseStep 4528001 = 3396001) B3396001
theorem B2684879 : Blo 1788095 2684879 := bstep (se 1 (by rfl) ⟨2013659, by rfl⟩ : syracuseStep 2684879 = 4027319) B4027319
theorem B4298777 : Blo 1788095 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B13588559 : Blo 1788095 13588559 := bstep (se 1 (by rfl) ⟨10191419, by rfl⟩ : syracuseStep 13588559 = 20382839) B20382839
theorem B20658311 : Blo 1788095 20658311 := bstep (se 1 (by rfl) ⟨15493733, by rfl⟩ : syracuseStep 20658311 = 30987467) B30987467
theorem B2013403 : Blo 1788095 2013403 := bstep (se 1 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 2013403 = 3020105) B3020105
theorem B10885367 : Blo 1788095 10885367 := bstep (se 1 (by rfl) ⟨8164025, by rfl⟩ : syracuseStep 10885367 = 16328051) B16328051
theorem B6445337 : Blo 1788095 6445337 := bstep (se 2 (by rfl) ⟨2417001, by rfl⟩ : syracuseStep 6445337 = 4834003) B4834003
theorem B6035741 : Blo 1788095 6035741 := bstep (se 3 (by rfl) ⟨1131701, by rfl⟩ : syracuseStep 6035741 = 2263403) B2263403
theorem B4528457 : Blo 1788095 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B32651705 : Blo 1788095 32651705 := bstep (se 2 (by rfl) ⟨12244389, by rfl⟩ : syracuseStep 32651705 = 24488779) B24488779
theorem B2013691 : Blo 1788095 2013691 := bstep (se 1 (by rfl) ⟨1510268, by rfl⟩ : syracuseStep 2013691 = 3020537) B3020537
theorem B4192847 : Blo 1788095 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B4078201 : Blo 1788095 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B4528811 : Blo 1788095 4528811 := bstep (se 1 (by rfl) ⟨3396608, by rfl⟩ : syracuseStep 4528811 = 6793217) B6793217
theorem B17005331 : Blo 1788095 17005331 := bstep (se 1 (by rfl) ⟨12753998, by rfl⟩ : syracuseStep 17005331 = 25507997) B25507997
theorem B6790013 : Blo 1788095 6790013 := bstep (se 3 (by rfl) ⟨1273127, by rfl⟩ : syracuseStep 6790013 = 2546255) B2546255
theorem B15277085 : Blo 1788095 15277085 := bstep (se 3 (by rfl) ⟨2864453, by rfl⟩ : syracuseStep 15277085 = 5728907) B5728907
theorem B4136033 : Blo 1788095 4136033 := bstep (se 2 (by rfl) ⟨1551012, by rfl⟩ : syracuseStep 4136033 = 3102025) B3102025
theorem B17194103 : Blo 1788095 17194103 := bstep (se 1 (by rfl) ⟨12895577, by rfl⟩ : syracuseStep 17194103 = 25791155) B25791155
theorem B20372633 : Blo 1788095 20372633 := bstep (se 2 (by rfl) ⟨7639737, by rfl⟩ : syracuseStep 20372633 = 15279475) B15279475
theorem B2546921 : Blo 1788095 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B6036767 : Blo 1788095 6036767 := bstep (se 1 (by rfl) ⟨4527575, by rfl⟩ : syracuseStep 6036767 = 9055151) B9055151
theorem B13770233 : Blo 1788095 13770233 := bstep (se 2 (by rfl) ⟨5163837, by rfl⟩ : syracuseStep 13770233 = 10327675) B10327675
theorem B9059849 : Blo 1788095 9059849 := bstep (se 2 (by rfl) ⟨3397443, by rfl⟩ : syracuseStep 9059849 = 6794887) B6794887
theorem B13770263 : Blo 1788095 13770263 := bstep (se 1 (by rfl) ⟨10327697, by rfl⟩ : syracuseStep 13770263 = 20655395) B20655395
theorem B32652881 : Blo 1788095 32652881 := bstep (se 2 (by rfl) ⟨12244830, by rfl⟩ : syracuseStep 32652881 = 24489661) B24489661
theorem B9182803 : Blo 1788095 9182803 := bstep (se 1 (by rfl) ⟨6887102, by rfl⟩ : syracuseStep 9182803 = 13774205) B13774205
theorem B6790817 : Blo 1788095 6790817 := bstep (se 2 (by rfl) ⟨2546556, by rfl⟩ : syracuseStep 6790817 = 5093113) B5093113
theorem B6446753 : Blo 1788095 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B278822807 : Blo 1788095 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B4530127 : Blo 1788095 4530127 := bstep (se 1 (by rfl) ⟨3397595, by rfl⟩ : syracuseStep 4530127 = 6795191) B6795191
theorem B22921217 : Blo 1788095 22921217 := bstep (se 2 (by rfl) ⟨8595456, by rfl⟩ : syracuseStep 22921217 = 17190913) B17190913
theorem B10190873 : Blo 1788095 10190873 := bstep (se 2 (by rfl) ⟨3821577, by rfl⟩ : syracuseStep 10190873 = 7643155) B7643155
theorem B6791303 : Blo 1788095 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B6791789 : Blo 1788095 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B2548459 : Blo 1788095 2548459 := bstep (se 1 (by rfl) ⟨1911344, by rfl⟩ : syracuseStep 2548459 = 3822689) B3822689
theorem B17187565 : Blo 1788095 17187565 := bstep (se 3 (by rfl) ⟨3222668, by rfl⟩ : syracuseStep 17187565 = 6445337) B6445337
theorem B5096189 : Blo 1788095 5096189 := bstep (se 3 (by rfl) ⟨955535, by rfl⟩ : syracuseStep 5096189 = 1911071) B1911071
theorem B5096303 : Blo 1788095 5096303 := bstep (se 1 (by rfl) ⟨3822227, by rfl⟩ : syracuseStep 5096303 = 7644455) B7644455
theorem B2417575 : Blo 1788095 2417575 := bstep (se 1 (by rfl) ⟨1813181, by rfl⟩ : syracuseStep 2417575 = 3626363) B3626363
theorem B9061307 : Blo 1788095 9061307 := bstep (se 1 (by rfl) ⟨6795980, by rfl⟩ : syracuseStep 9061307 = 13591961) B13591961
theorem B4023251 : Blo 1788095 4023251 := bstep (se 1 (by rfl) ⟨3017438, by rfl⟩ : syracuseStep 4023251 = 6034877) B6034877
theorem B5514227 : Blo 1788095 5514227 := bstep (se 1 (by rfl) ⟨4135670, by rfl⟩ : syracuseStep 5514227 = 8271341) B8271341
theorem B11461657 : Blo 1788095 11461657 := bstep (se 2 (by rfl) ⟨4298121, by rfl⟩ : syracuseStep 11461657 = 8596243) B8596243
theorem B4023503 : Blo 1788095 4023503 := bstep (se 1 (by rfl) ⟨3017627, by rfl⟩ : syracuseStep 4023503 = 6035255) B6035255
theorem B13772207 : Blo 1788095 13772207 := bstep (se 1 (by rfl) ⟨10329155, by rfl⟩ : syracuseStep 13772207 = 20658311) B20658311
theorem B4023827 : Blo 1788095 4023827 := bstep (se 1 (by rfl) ⟨3017870, by rfl⟩ : syracuseStep 4023827 = 6035741) B6035741
theorem B15279749 : Blo 1788095 15279749 := bstep (se 4 (by rfl) ⟨1432476, by rfl⟩ : syracuseStep 15279749 = 2864953) B2864953
theorem B6882977 : Blo 1788095 6882977 := bstep (se 2 (by rfl) ⟨2581116, by rfl⟩ : syracuseStep 6882977 = 5162233) B5162233
theorem B2795231 : Blo 1788095 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B8161103 : Blo 1788095 8161103 := bstep (se 1 (by rfl) ⟨6120827, by rfl⟩ : syracuseStep 8161103 = 12241655) B12241655
theorem B10184723 : Blo 1788095 10184723 := bstep (se 1 (by rfl) ⟨7638542, by rfl⟩ : syracuseStep 10184723 = 15277085) B15277085
theorem B11462735 : Blo 1788095 11462735 := bstep (se 1 (by rfl) ⟨8597051, by rfl⟩ : syracuseStep 11462735 = 17194103) B17194103
theorem B2263135 : Blo 1788095 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B1788095 : Blo 1788095 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B2263231 : Blo 1788095 2263231 := bstep (se 1 (by rfl) ⟨1697423, by rfl⟩ : syracuseStep 2263231 = 3394847) B3394847
theorem B4024511 : Blo 1788095 4024511 := bstep (se 1 (by rfl) ⟨3018383, by rfl⟩ : syracuseStep 4024511 = 6036767) B6036767
theorem B1788207 : Blo 1788095 1788207 := bstep (se 1 (by rfl) ⟨1341155, by rfl⟩ : syracuseStep 1788207 = 2682311) B2682311
theorem B6039899 : Blo 1788095 6039899 := bstep (se 1 (by rfl) ⟨4529924, by rfl⟩ : syracuseStep 6039899 = 9059849) B9059849
theorem B21768587 : Blo 1788095 21768587 := bstep (se 1 (by rfl) ⟨16326440, by rfl⟩ : syracuseStep 21768587 = 32652881) B32652881
theorem B17435159 : Blo 1788095 17435159 := bstep (se 1 (by rfl) ⟨13076369, by rfl⟩ : syracuseStep 17435159 = 26152739) B26152739
theorem B1788443 : Blo 1788095 1788443 := bstep (se 1 (by rfl) ⟨1341332, by rfl⟩ : syracuseStep 1788443 = 2682665) B2682665
theorem B1788447 : Blo 1788095 1788447 := bstep (se 1 (by rfl) ⟨1341335, by rfl⟩ : syracuseStep 1788447 = 2682671) B2682671
theorem B10324553 : Blo 1788095 10324553 := bstep (se 2 (by rfl) ⟨3871707, by rfl⟩ : syracuseStep 10324553 = 7743415) B7743415
theorem B6040169 : Blo 1788095 6040169 := bstep (se 2 (by rfl) ⟨2265063, by rfl⟩ : syracuseStep 6040169 = 4530127) B4530127
theorem B47754035 : Blo 1788095 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1788763 : Blo 1788095 1788763 := bstep (se 1 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 1788763 = 2683145) B2683145
theorem B20368259 : Blo 1788095 20368259 := bstep (se 1 (by rfl) ⟨15276194, by rfl⟩ : syracuseStep 20368259 = 30552389) B30552389
theorem B1788831 : Blo 1788095 1788831 := bstep (se 1 (by rfl) ⟨1341623, by rfl⟩ : syracuseStep 1788831 = 2683247) B2683247
theorem B11029421 : Blo 1788095 11029421 := bstep (se 3 (by rfl) ⟨2068016, by rfl⟩ : syracuseStep 11029421 = 4136033) B4136033
theorem B7646147 : Blo 1788095 7646147 := bstep (se 1 (by rfl) ⟨5734610, by rfl⟩ : syracuseStep 7646147 = 11469221) B11469221
theorem B6794219 : Blo 1788095 6794219 := bstep (se 1 (by rfl) ⟨5095664, by rfl⟩ : syracuseStep 6794219 = 10191329) B10191329
theorem B1788975 : Blo 1788095 1788975 := bstep (se 1 (by rfl) ⟨1341731, by rfl⟩ : syracuseStep 1788975 = 2683463) B2683463
theorem B1788999 : Blo 1788095 1788999 := bstep (se 1 (by rfl) ⟨1341749, by rfl⟩ : syracuseStep 1788999 = 2683499) B2683499
theorem B4025465 : Blo 1788095 4025465 := bstep (se 2 (by rfl) ⟨1509549, by rfl⟩ : syracuseStep 4025465 = 3019099) B3019099
theorem B3017911 : Blo 1788095 3017911 := bstep (se 1 (by rfl) ⟨2263433, by rfl⟩ : syracuseStep 3017911 = 4526867) B4526867
theorem B1789151 : Blo 1788095 1789151 := bstep (se 1 (by rfl) ⟨1341863, by rfl⟩ : syracuseStep 1789151 = 2683727) B2683727
theorem B2682191 : Blo 1788095 2682191 := bstep (se 1 (by rfl) ⟨2011643, by rfl⟩ : syracuseStep 2682191 = 4023287) B4023287
theorem B2682281 : Blo 1788095 2682281 := bstep (se 2 (by rfl) ⟨1005855, by rfl⟩ : syracuseStep 2682281 = 2011711) B2011711
theorem B3018215 : Blo 1788095 3018215 := bstep (se 1 (by rfl) ⟨2263661, by rfl⟩ : syracuseStep 3018215 = 4527323) B4527323
theorem B1789415 : Blo 1788095 1789415 := bstep (se 1 (by rfl) ⟨1342061, by rfl⟩ : syracuseStep 1789415 = 2684123) B2684123
theorem B3018235 : Blo 1788095 3018235 := bstep (se 1 (by rfl) ⟨2263676, by rfl⟩ : syracuseStep 3018235 = 4527353) B4527353
theorem B2682431 : Blo 1788095 2682431 := bstep (se 1 (by rfl) ⟨2011823, by rfl⟩ : syracuseStep 2682431 = 4023647) B4023647
theorem B3395135 : Blo 1788095 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B1789531 : Blo 1788095 1789531 := bstep (se 1 (by rfl) ⟨1342148, by rfl⟩ : syracuseStep 1789531 = 2684297) B2684297
theorem B6041195 : Blo 1788095 6041195 := bstep (se 1 (by rfl) ⟨4530896, by rfl⟩ : syracuseStep 6041195 = 9061793) B9061793
theorem B2944745 : Blo 1788095 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B12898055 : Blo 1788095 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B4026131 : Blo 1788095 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B2682695 : Blo 1788095 2682695 := bstep (se 1 (by rfl) ⟨2012021, by rfl⟩ : syracuseStep 2682695 = 4024043) B4024043
theorem B1789767 : Blo 1788095 1789767 := bstep (se 1 (by rfl) ⟨1342325, by rfl⟩ : syracuseStep 1789767 = 2684651) B2684651
theorem B6041465 : Blo 1788095 6041465 := bstep (se 2 (by rfl) ⟨2265549, by rfl⟩ : syracuseStep 6041465 = 4531099) B4531099
theorem B2682779 : Blo 1788095 2682779 := bstep (se 1 (by rfl) ⟨2012084, by rfl⟩ : syracuseStep 2682779 = 4024169) B4024169
theorem B5730203 : Blo 1788095 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B3018667 : Blo 1788095 3018667 := bstep (se 1 (by rfl) ⟨2264000, by rfl⟩ : syracuseStep 3018667 = 4528001) B4528001
theorem B1789919 : Blo 1788095 1789919 := bstep (se 1 (by rfl) ⟨1342439, by rfl⟩ : syracuseStep 1789919 = 2684879) B2684879
theorem B36720701 : Blo 1788095 36720701 := bstep (se 3 (by rfl) ⟨6885131, by rfl⟩ : syracuseStep 36720701 = 13770263) B13770263
theorem B4026491 : Blo 1788095 4026491 := bstep (se 1 (by rfl) ⟨3019868, by rfl⟩ : syracuseStep 4026491 = 6039737) B6039737
theorem B3018971 : Blo 1788095 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B4026761 : Blo 1788095 4026761 := bstep (se 2 (by rfl) ⟨1510035, by rfl⟩ : syracuseStep 4026761 = 3020071) B3020071
theorem B24482213 : Blo 1788095 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B3019207 : Blo 1788095 3019207 := bstep (se 1 (by rfl) ⟨2264405, by rfl⟩ : syracuseStep 3019207 = 4528811) B4528811
theorem B2683343 : Blo 1788095 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B3019241 : Blo 1788095 3019241 := bstep (se 2 (by rfl) ⟨1132215, by rfl⟩ : syracuseStep 3019241 = 2264431) B2264431
theorem B2683385 : Blo 1788095 2683385 := bstep (se 2 (by rfl) ⟨1006269, by rfl⟩ : syracuseStep 2683385 = 2012539) B2012539
theorem B4526675 : Blo 1788095 4526675 := bstep (se 1 (by rfl) ⟨3395006, by rfl⟩ : syracuseStep 4526675 = 6790013) B6790013
theorem B6795859 : Blo 1788095 6795859 := bstep (se 1 (by rfl) ⟨5096894, by rfl⟩ : syracuseStep 6795859 = 10193789) B10193789
theorem B2683487 : Blo 1788095 2683487 := bstep (se 1 (by rfl) ⟨2012615, by rfl⟩ : syracuseStep 2683487 = 4025231) B4025231
theorem B3224299 : Blo 1788095 3224299 := bstep (se 1 (by rfl) ⟨2418224, by rfl⟩ : syracuseStep 3224299 = 4836449) B4836449
theorem B9179929 : Blo 1788095 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B12243737 : Blo 1788095 12243737 := bstep (se 2 (by rfl) ⟨4591401, by rfl⟩ : syracuseStep 12243737 = 9182803) B9182803
theorem B55087933 : Blo 1788095 55087933 := bstep (se 3 (by rfl) ⟨10328987, by rfl⟩ : syracuseStep 55087933 = 20657975) B20657975
theorem B2012071 : Blo 1788095 2012071 := bstep (se 1 (by rfl) ⟨1509053, by rfl⟩ : syracuseStep 2012071 = 3018107) B3018107
theorem B9180155 : Blo 1788095 9180155 := bstep (se 1 (by rfl) ⟨6885116, by rfl⟩ : syracuseStep 9180155 = 13770233) B13770233
theorem B2683967 : Blo 1788095 2683967 := bstep (se 1 (by rfl) ⟨2012975, by rfl⟩ : syracuseStep 2683967 = 4025951) B4025951
theorem B2684009 : Blo 1788095 2684009 := bstep (se 2 (by rfl) ⟨1006503, by rfl⟩ : syracuseStep 2684009 = 2013007) B2013007
theorem B3224681 : Blo 1788095 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B4527211 : Blo 1788095 4527211 := bstep (se 1 (by rfl) ⟨3395408, by rfl⟩ : syracuseStep 4527211 = 6790817) B6790817
theorem B4297835 : Blo 1788095 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B4027499 : Blo 1788095 4027499 := bstep (se 1 (by rfl) ⟨3020624, by rfl⟩ : syracuseStep 4027499 = 6041249) B6041249
theorem B9057419 : Blo 1788095 9057419 := bstep (se 1 (by rfl) ⟨6793064, by rfl⟩ : syracuseStep 9057419 = 13586129) B13586129
theorem B2684111 : Blo 1788095 2684111 := bstep (se 1 (by rfl) ⟨2013083, by rfl⟩ : syracuseStep 2684111 = 4026167) B4026167
theorem B185881871 : Blo 1788095 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B10876315 : Blo 1788095 10876315 := bstep (se 1 (by rfl) ⟨8157236, by rfl⟩ : syracuseStep 10876315 = 16314473) B16314473
theorem B4527515 : Blo 1788095 4527515 := bstep (se 1 (by rfl) ⟨3395636, by rfl⟩ : syracuseStep 4527515 = 6791273) B6791273
theorem B2684315 : Blo 1788095 2684315 := bstep (se 1 (by rfl) ⟨2013236, by rfl⟩ : syracuseStep 2684315 = 4026473) B4026473
theorem B3061147 : Blo 1788095 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B55055915 : Blo 1788095 55055915 := bstep (se 1 (by rfl) ⟨41291936, by rfl⟩ : syracuseStep 55055915 = 82583873) B82583873
theorem B2684537 : Blo 1788095 2684537 := bstep (se 2 (by rfl) ⟨1006701, by rfl⟩ : syracuseStep 2684537 = 2013403) B2013403
theorem B8599243 : Blo 1788095 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B2684639 : Blo 1788095 2684639 := bstep (se 1 (by rfl) ⟨2013479, by rfl⟩ : syracuseStep 2684639 = 4026959) B4026959
theorem B22935311 : Blo 1788095 22935311 := bstep (se 1 (by rfl) ⟨17201483, by rfl⟩ : syracuseStep 22935311 = 34402967) B34402967
theorem B2684735 : Blo 1788095 2684735 := bstep (se 1 (by rfl) ⟨2013551, by rfl⟩ : syracuseStep 2684735 = 4027103) B4027103
theorem B2684903 : Blo 1788095 2684903 := bstep (se 1 (by rfl) ⟨2013677, by rfl⟩ : syracuseStep 2684903 = 4027355) B4027355
theorem B2684921 : Blo 1788095 2684921 := bstep (se 2 (by rfl) ⟨1006845, by rfl⟩ : syracuseStep 2684921 = 2013691) B2013691
theorem B3225683 : Blo 1788095 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B2685023 : Blo 1788095 2685023 := bstep (se 1 (by rfl) ⟨2013767, by rfl⟩ : syracuseStep 2685023 = 4027535) B4027535
theorem B2685083 : Blo 1788095 2685083 := bstep (se 1 (by rfl) ⟨2013812, by rfl⟩ : syracuseStep 2685083 = 4027625) B4027625
theorem B5437601 : Blo 1788095 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B2685119 : Blo 1788095 2685119 := bstep (se 1 (by rfl) ⟨2013839, by rfl⟩ : syracuseStep 2685119 = 4027679) B4027679
theorem B5093705 : Blo 1788095 5093705 := bstep (se 2 (by rfl) ⟨1910139, by rfl⟩ : syracuseStep 5093705 = 3820279) B3820279
theorem B9673067 : Blo 1788095 9673067 := bstep (se 1 (by rfl) ⟨7254800, by rfl⟩ : syracuseStep 9673067 = 14509601) B14509601
theorem B4528507 : Blo 1788095 4528507 := bstep (se 1 (by rfl) ⟨3396380, by rfl⟩ : syracuseStep 4528507 = 6792761) B6792761
theorem B87071213 : Blo 1788095 87071213 := bstep (se 3 (by rfl) ⟨16325852, by rfl⟩ : syracuseStep 87071213 = 32651705) B32651705
theorem B2013727 : Blo 1788095 2013727 := bstep (se 1 (by rfl) ⟨1510295, by rfl⟩ : syracuseStep 2013727 = 3020591) B3020591
theorem B6888073 : Blo 1788095 6888073 := bstep (se 2 (by rfl) ⟨2583027, by rfl⟩ : syracuseStep 6888073 = 5166055) B5166055
theorem B2865851 : Blo 1788095 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B9059039 : Blo 1788095 9059039 := bstep (se 1 (by rfl) ⟨6794279, by rfl⟩ : syracuseStep 9059039 = 13588559) B13588559
theorem B7256911 : Blo 1788095 7256911 := bstep (se 1 (by rfl) ⟨5442683, by rfl⟩ : syracuseStep 7256911 = 10885367) B10885367
theorem B6036551 : Blo 1788095 6036551 := bstep (se 1 (by rfl) ⟨4527413, by rfl⟩ : syracuseStep 6036551 = 9054827) B9054827
theorem B6036605 : Blo 1788095 6036605 := bstep (se 3 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 6036605 = 2263727) B2263727
theorem B11336887 : Blo 1788095 11336887 := bstep (se 1 (by rfl) ⟨8502665, by rfl⟩ : syracuseStep 11336887 = 17005331) B17005331
theorem B6036875 : Blo 1788095 6036875 := bstep (se 1 (by rfl) ⟨4527656, by rfl⟩ : syracuseStep 6036875 = 9055313) B9055313
theorem B4300199 : Blo 1788095 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B13581755 : Blo 1788095 13581755 := bstep (se 1 (by rfl) ⟨10186316, by rfl⟩ : syracuseStep 13581755 = 20372633) B20372633
theorem B24494033 : Blo 1788095 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B8601821 : Blo 1788095 8601821 := bstep (se 3 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 8601821 = 3225683) B3225683
theorem B6038009 : Blo 1788095 6038009 := bstep (se 2 (by rfl) ⟨2264253, by rfl⟩ : syracuseStep 6038009 = 4528507) B4528507
theorem B6038279 : Blo 1788095 6038279 := bstep (se 1 (by rfl) ⟨4528709, by rfl⟩ : syracuseStep 6038279 = 9057419) B9057419
theorem B9061145 : Blo 1788095 9061145 := bstep (se 2 (by rfl) ⟨3397929, by rfl⟩ : syracuseStep 9061145 = 6795859) B6795859
theorem B123921247 : Blo 1788095 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B9184097 : Blo 1788095 9184097 := bstep (se 2 (by rfl) ⟨3444036, by rfl⟩ : syracuseStep 9184097 = 6888073) B6888073
theorem B13583213 : Blo 1788095 13583213 := bstep (se 3 (by rfl) ⟨2546852, by rfl⟩ : syracuseStep 13583213 = 5093705) B5093705
theorem B12239905 : Blo 1788095 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B73450577 : Blo 1788095 73450577 := bstep (se 2 (by rfl) ⟨27543966, by rfl⟩ : syracuseStep 73450577 = 55087933) B55087933
theorem B9675881 : Blo 1788095 9675881 := bstep (se 2 (by rfl) ⟨3628455, by rfl⟩ : syracuseStep 9675881 = 7256911) B7256911
theorem B4588651 : Blo 1788095 4588651 := bstep (se 1 (by rfl) ⟨3441488, by rfl⟩ : syracuseStep 4588651 = 6882977) B6882977
theorem B5440735 : Blo 1788095 5440735 := bstep (se 1 (by rfl) ⟨4080551, by rfl⟩ : syracuseStep 5440735 = 8161103) B8161103
theorem B9053693 : Blo 1788095 9053693 := bstep (se 3 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 9053693 = 3395135) B3395135
theorem B4023881 : Blo 1788095 4023881 := bstep (se 2 (by rfl) ⟨1508955, by rfl⟩ : syracuseStep 4023881 = 3017911) B3017911
theorem B1910567 : Blo 1788095 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B6039359 : Blo 1788095 6039359 := bstep (se 1 (by rfl) ⟨4529519, by rfl⟩ : syracuseStep 6039359 = 9059039) B9059039
theorem B14501753 : Blo 1788095 14501753 := bstep (se 2 (by rfl) ⟨5438157, by rfl⟩ : syracuseStep 14501753 = 10876315) B10876315
theorem B31836023 : Blo 1788095 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B4081529 : Blo 1788095 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B5097431 : Blo 1788095 5097431 := bstep (se 1 (by rfl) ⟨3823073, by rfl⟩ : syracuseStep 5097431 = 7646147) B7646147
theorem B4024313 : Blo 1788095 4024313 := bstep (se 2 (by rfl) ⟨1509117, by rfl⟩ : syracuseStep 4024313 = 3018235) B3018235
theorem B4024367 : Blo 1788095 4024367 := bstep (se 1 (by rfl) ⟨3018275, by rfl⟩ : syracuseStep 4024367 = 6036551) B6036551
theorem B4024403 : Blo 1788095 4024403 := bstep (se 1 (by rfl) ⟨3018302, by rfl⟩ : syracuseStep 4024403 = 6036605) B6036605
theorem B1788127 : Blo 1788095 1788127 := bstep (se 1 (by rfl) ⟨1341095, by rfl⟩ : syracuseStep 1788127 = 2682191) B2682191
theorem B4024583 : Blo 1788095 4024583 := bstep (se 1 (by rfl) ⟨3018437, by rfl⟩ : syracuseStep 4024583 = 6036875) B6036875
theorem B1788187 : Blo 1788095 1788187 := bstep (se 1 (by rfl) ⟨1341140, by rfl⟩ : syracuseStep 1788187 = 2682281) B2682281
theorem B9054503 : Blo 1788095 9054503 := bstep (se 1 (by rfl) ⟨6790877, by rfl⟩ : syracuseStep 9054503 = 13581755) B13581755
theorem B1788287 : Blo 1788095 1788287 := bstep (se 1 (by rfl) ⟨1341215, by rfl⟩ : syracuseStep 1788287 = 2682431) B2682431
theorem B65317421 : Blo 1788095 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B1788463 : Blo 1788095 1788463 := bstep (se 1 (by rfl) ⟨1341347, by rfl⟩ : syracuseStep 1788463 = 2682695) B2682695
theorem B4024889 : Blo 1788095 4024889 := bstep (se 2 (by rfl) ⟨1509333, by rfl⟩ : syracuseStep 4024889 = 3018667) B3018667
theorem B1788519 : Blo 1788095 1788519 := bstep (se 1 (by rfl) ⟨1341389, by rfl⟩ : syracuseStep 1788519 = 2682779) B2682779
theorem B3820135 : Blo 1788095 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B24480413 : Blo 1788095 24480413 := bstep (se 3 (by rfl) ⟨4590077, by rfl⟩ : syracuseStep 24480413 = 9180155) B9180155
theorem B15280811 : Blo 1788095 15280811 := bstep (se 1 (by rfl) ⟨11460608, by rfl⟩ : syracuseStep 15280811 = 22921217) B22921217
theorem B6793915 : Blo 1788095 6793915 := bstep (se 1 (by rfl) ⟨5095436, by rfl⟩ : syracuseStep 6793915 = 10190873) B10190873
theorem B24480467 : Blo 1788095 24480467 := bstep (se 1 (by rfl) ⟨18360350, by rfl⟩ : syracuseStep 24480467 = 36720701) B36720701
theorem B3017513 : Blo 1788095 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B3017641 : Blo 1788095 3017641 := bstep (se 2 (by rfl) ⟨1131615, by rfl⟩ : syracuseStep 3017641 = 2263231) B2263231
theorem B16321475 : Blo 1788095 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B1788895 : Blo 1788095 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B1788923 : Blo 1788095 1788923 := bstep (se 1 (by rfl) ⟨1341692, by rfl⟩ : syracuseStep 1788923 = 2683385) B2683385
theorem B3017783 : Blo 1788095 3017783 := bstep (se 1 (by rfl) ⟨2263337, by rfl⟩ : syracuseStep 3017783 = 4526675) B4526675
theorem B1788991 : Blo 1788095 1788991 := bstep (se 1 (by rfl) ⟨1341743, by rfl⟩ : syracuseStep 1788991 = 2683487) B2683487
theorem B4025609 : Blo 1788095 4025609 := bstep (se 2 (by rfl) ⟨1509603, by rfl⟩ : syracuseStep 4025609 = 3019207) B3019207
theorem B6040871 : Blo 1788095 6040871 := bstep (se 1 (by rfl) ⟨4530653, by rfl⟩ : syracuseStep 6040871 = 9061307) B9061307
theorem B2682167 : Blo 1788095 2682167 := bstep (se 1 (by rfl) ⟨2011625, by rfl⟩ : syracuseStep 2682167 = 4023251) B4023251
theorem B1789311 : Blo 1788095 1789311 := bstep (se 1 (by rfl) ⟨1341983, by rfl⟩ : syracuseStep 1789311 = 2683967) B2683967
theorem B1789339 : Blo 1788095 1789339 := bstep (se 1 (by rfl) ⟨1342004, by rfl⟩ : syracuseStep 1789339 = 2684009) B2684009
theorem B2149787 : Blo 1788095 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B110128565 : Blo 1788095 110128565 := bstep (se 5 (by rfl) ⟨5162276, by rfl⟩ : syracuseStep 110128565 = 10324553) B10324553
theorem B2682335 : Blo 1788095 2682335 := bstep (se 1 (by rfl) ⟨2011751, by rfl⟩ : syracuseStep 2682335 = 4023503) B4023503
theorem B1789407 : Blo 1788095 1789407 := bstep (se 1 (by rfl) ⟨1342055, by rfl⟩ : syracuseStep 1789407 = 2684111) B2684111
theorem B3018343 : Blo 1788095 3018343 := bstep (se 1 (by rfl) ⟨2263757, by rfl⟩ : syracuseStep 3018343 = 4527515) B4527515
theorem B1789543 : Blo 1788095 1789543 := bstep (se 1 (by rfl) ⟨1342157, by rfl⟩ : syracuseStep 1789543 = 2684315) B2684315
theorem B22916753 : Blo 1788095 22916753 := bstep (se 2 (by rfl) ⟨8593782, by rfl⟩ : syracuseStep 22916753 = 17187565) B17187565
theorem B2682551 : Blo 1788095 2682551 := bstep (se 1 (by rfl) ⟨2011913, by rfl⟩ : syracuseStep 2682551 = 4023827) B4023827
theorem B36703943 : Blo 1788095 36703943 := bstep (se 1 (by rfl) ⟨27527957, by rfl⟩ : syracuseStep 36703943 = 55055915) B55055915
theorem B1789691 : Blo 1788095 1789691 := bstep (se 1 (by rfl) ⟨1342268, by rfl⟩ : syracuseStep 1789691 = 2684537) B2684537
theorem B10186499 : Blo 1788095 10186499 := bstep (se 1 (by rfl) ⟨7639874, by rfl⟩ : syracuseStep 10186499 = 15279749) B15279749
theorem B1789759 : Blo 1788095 1789759 := bstep (se 1 (by rfl) ⟨1342319, by rfl⟩ : syracuseStep 1789759 = 2684639) B2684639
theorem B15290207 : Blo 1788095 15290207 := bstep (se 1 (by rfl) ⟨11467655, by rfl⟩ : syracuseStep 15290207 = 22935311) B22935311
theorem B1789823 : Blo 1788095 1789823 := bstep (se 1 (by rfl) ⟨1342367, by rfl⟩ : syracuseStep 1789823 = 2684735) B2684735
theorem B2682761 : Blo 1788095 2682761 := bstep (se 2 (by rfl) ⟨1006035, by rfl⟩ : syracuseStep 2682761 = 2012071) B2012071
theorem B3223433 : Blo 1788095 3223433 := bstep (se 2 (by rfl) ⟨1208787, by rfl⟩ : syracuseStep 3223433 = 2417575) B2417575
theorem B1789935 : Blo 1788095 1789935 := bstep (se 1 (by rfl) ⟨1342451, by rfl⟩ : syracuseStep 1789935 = 2684903) B2684903
theorem B1789947 : Blo 1788095 1789947 := bstep (se 1 (by rfl) ⟨1342460, by rfl⟩ : syracuseStep 1789947 = 2684921) B2684921
theorem B15282209 : Blo 1788095 15282209 := bstep (se 2 (by rfl) ⟨5730828, by rfl⟩ : syracuseStep 15282209 = 11461657) B11461657
theorem B1790015 : Blo 1788095 1790015 := bstep (se 1 (by rfl) ⟨1342511, by rfl⟩ : syracuseStep 1790015 = 2685023) B2685023
theorem B1790055 : Blo 1788095 1790055 := bstep (se 1 (by rfl) ⟨1342541, by rfl⟩ : syracuseStep 1790055 = 2685083) B2685083
theorem B3625067 : Blo 1788095 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B2683007 : Blo 1788095 2683007 := bstep (se 1 (by rfl) ⟨2012255, by rfl⟩ : syracuseStep 2683007 = 4024511) B4024511
theorem B1790079 : Blo 1788095 1790079 := bstep (se 1 (by rfl) ⟨1342559, by rfl⟩ : syracuseStep 1790079 = 2685119) B2685119
theorem B4026599 : Blo 1788095 4026599 := bstep (se 1 (by rfl) ⟨3019949, by rfl⟩ : syracuseStep 4026599 = 6039899) B6039899
theorem B14512391 : Blo 1788095 14512391 := bstep (se 1 (by rfl) ⟨10884293, by rfl⟩ : syracuseStep 14512391 = 21768587) B21768587
theorem B4026779 : Blo 1788095 4026779 := bstep (se 1 (by rfl) ⟨3020084, by rfl⟩ : syracuseStep 4026779 = 6040169) B6040169
theorem B13578839 : Blo 1788095 13578839 := bstep (se 1 (by rfl) ⟨10184129, by rfl⟩ : syracuseStep 13578839 = 20368259) B20368259
theorem B7352947 : Blo 1788095 7352947 := bstep (se 1 (by rfl) ⟨5514710, by rfl⟩ : syracuseStep 7352947 = 11029421) B11029421
theorem B34394813 : Blo 1788095 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B32649965 : Blo 1788095 32649965 := bstep (se 3 (by rfl) ⟨6121868, by rfl⟩ : syracuseStep 32649965 = 12243737) B12243737
theorem B2683643 : Blo 1788095 2683643 := bstep (se 1 (by rfl) ⟨2012732, by rfl⟩ : syracuseStep 2683643 = 4025465) B4025465
theorem B11465657 : Blo 1788095 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B2012143 : Blo 1788095 2012143 := bstep (se 1 (by rfl) ⟨1509107, by rfl⟩ : syracuseStep 2012143 = 3018215) B3018215
theorem B4027463 : Blo 1788095 4027463 := bstep (se 1 (by rfl) ⟨3020597, by rfl⟩ : syracuseStep 4027463 = 6041195) B6041195
theorem B1963163 : Blo 1788095 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B2684087 : Blo 1788095 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B4027643 : Blo 1788095 4027643 := bstep (se 1 (by rfl) ⟨3020732, by rfl⟩ : syracuseStep 4027643 = 6041465) B6041465
theorem B2684327 : Blo 1788095 2684327 := bstep (se 1 (by rfl) ⟨2013245, by rfl⟩ : syracuseStep 2684327 = 4026491) B4026491
theorem B4527535 : Blo 1788095 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B2012647 : Blo 1788095 2012647 := bstep (se 1 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 2012647 = 3018971) B3018971
theorem B2684507 : Blo 1788095 2684507 := bstep (se 1 (by rfl) ⟨2013380, by rfl⟩ : syracuseStep 2684507 = 4026761) B4026761
theorem B2012827 : Blo 1788095 2012827 := bstep (se 1 (by rfl) ⟨1509620, by rfl⟩ : syracuseStep 2012827 = 3019241) B3019241
theorem B4527859 : Blo 1788095 4527859 := bstep (se 1 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 4527859 = 6791789) B6791789
theorem B3397459 : Blo 1788095 3397459 := bstep (se 1 (by rfl) ⟨2548094, by rfl⟩ : syracuseStep 3397459 = 5096189) B5096189
theorem B3397535 : Blo 1788095 3397535 := bstep (se 1 (by rfl) ⟨2548151, by rfl⟩ : syracuseStep 3397535 = 5096303) B5096303
theorem B3676151 : Blo 1788095 3676151 := bstep (se 1 (by rfl) ⟨2757113, by rfl⟩ : syracuseStep 3676151 = 5514227) B5514227
theorem B2684969 : Blo 1788095 2684969 := bstep (se 2 (by rfl) ⟨1006863, by rfl⟩ : syracuseStep 2684969 = 2013727) B2013727
theorem B2865223 : Blo 1788095 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B2684999 : Blo 1788095 2684999 := bstep (se 1 (by rfl) ⟨2013749, by rfl⟩ : syracuseStep 2684999 = 4027499) B4027499
theorem B25794845 : Blo 1788095 25794845 := bstep (se 3 (by rfl) ⟨4836533, by rfl⟩ : syracuseStep 25794845 = 9673067) B9673067
theorem B9181471 : Blo 1788095 9181471 := bstep (se 1 (by rfl) ⟨6886103, by rfl⟩ : syracuseStep 9181471 = 13772207) B13772207
theorem B60463397 : Blo 1788095 60463397 := bstep (se 4 (by rfl) ⟨5668443, by rfl⟩ : syracuseStep 60463397 = 11336887) B11336887
theorem B4299065 : Blo 1788095 4299065 := bstep (se 2 (by rfl) ⟨1612149, by rfl⟩ : syracuseStep 4299065 = 3224299) B3224299
theorem B3397945 : Blo 1788095 3397945 := bstep (se 2 (by rfl) ⟨1274229, by rfl⟩ : syracuseStep 3397945 = 2548459) B2548459
theorem B6789815 : Blo 1788095 6789815 := bstep (se 1 (by rfl) ⟨5092361, by rfl⟩ : syracuseStep 6789815 = 10184723) B10184723
theorem B7641823 : Blo 1788095 7641823 := bstep (se 1 (by rfl) ⟨5731367, by rfl⟩ : syracuseStep 7641823 = 11462735) B11462735
theorem B6036281 : Blo 1788095 6036281 := bstep (se 2 (by rfl) ⟨2263605, by rfl⟩ : syracuseStep 6036281 = 4527211) B4527211
theorem B58047475 : Blo 1788095 58047475 := bstep (se 1 (by rfl) ⟨43535606, by rfl⟩ : syracuseStep 58047475 = 87071213) B87071213
theorem B11623439 : Blo 1788095 11623439 := bstep (se 1 (by rfl) ⟨8717579, by rfl⟩ : syracuseStep 11623439 = 17435159) B17435159
theorem B7453949 : Blo 1788095 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B4529479 : Blo 1788095 4529479 := bstep (se 1 (by rfl) ⟨3397109, by rfl⟩ : syracuseStep 4529479 = 6794219) B6794219
theorem B2866799 : Blo 1788095 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B2416711 : Blo 1788095 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B5734547 : Blo 1788095 5734547 := bstep (se 1 (by rfl) ⟨4300910, by rfl⟩ : syracuseStep 5734547 = 8601821) B8601821
theorem B9674927 : Blo 1788095 9674927 := bstep (se 1 (by rfl) ⟨7256195, by rfl⟩ : syracuseStep 9674927 = 14512391) B14512391
theorem B9052559 : Blo 1788095 9052559 := bstep (se 1 (by rfl) ⟨6789419, by rfl⟩ : syracuseStep 9052559 = 13578839) B13578839
theorem B5235101 : Blo 1788095 5235101 := bstep (se 3 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 5235101 = 1963163) B1963163
theorem B4530593 : Blo 1788095 4530593 := bstep (se 2 (by rfl) ⟨1698972, by rfl⟩ : syracuseStep 4530593 = 3397945) B3397945
theorem B22929875 : Blo 1788095 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B21766643 : Blo 1788095 21766643 := bstep (se 1 (by rfl) ⟨16324982, by rfl⟩ : syracuseStep 21766643 = 32649965) B32649965
theorem B7643771 : Blo 1788095 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B29017253 : Blo 1788095 29017253 := bstep (se 4 (by rfl) ⟨2720367, by rfl⟩ : syracuseStep 29017253 = 5440735) B5440735
theorem B4023521 : Blo 1788095 4023521 := bstep (se 2 (by rfl) ⟨1508820, by rfl⟩ : syracuseStep 4023521 = 3017641) B3017641
theorem B9667835 : Blo 1788095 9667835 := bstep (se 1 (by rfl) ⟨7250876, by rfl⟩ : syracuseStep 9667835 = 14501753) B14501753
theorem B16319873 : Blo 1788095 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B17196563 : Blo 1788095 17196563 := bstep (se 1 (by rfl) ⟨12897422, by rfl⟩ : syracuseStep 17196563 = 25794845) B25794845
theorem B6039305 : Blo 1788095 6039305 := bstep (se 2 (by rfl) ⟨2264739, by rfl⟩ : syracuseStep 6039305 = 4529479) B4529479
theorem B16320275 : Blo 1788095 16320275 := bstep (se 1 (by rfl) ⟨12240206, by rfl⟩ : syracuseStep 16320275 = 24480413) B24480413
theorem B16320311 : Blo 1788095 16320311 := bstep (se 1 (by rfl) ⟨12240233, by rfl⟩ : syracuseStep 16320311 = 24480467) B24480467
theorem B4024187 : Blo 1788095 4024187 := bstep (se 1 (by rfl) ⟨3018140, by rfl⟩ : syracuseStep 4024187 = 6036281) B6036281
theorem B10880983 : Blo 1788095 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B4024457 : Blo 1788095 4024457 := bstep (se 2 (by rfl) ⟨1509171, by rfl⟩ : syracuseStep 4024457 = 3018343) B3018343
theorem B1788111 : Blo 1788095 1788111 := bstep (se 1 (by rfl) ⟨1341083, by rfl⟩ : syracuseStep 1788111 = 2682167) B2682167
theorem B73419043 : Blo 1788095 73419043 := bstep (se 1 (by rfl) ⟨55064282, by rfl⟩ : syracuseStep 73419043 = 110128565) B110128565
theorem B1788223 : Blo 1788095 1788223 := bstep (se 1 (by rfl) ⟨1341167, by rfl⟩ : syracuseStep 1788223 = 2682335) B2682335
theorem B8595821 : Blo 1788095 8595821 := bstep (se 3 (by rfl) ⟨1611716, by rfl⟩ : syracuseStep 8595821 = 3223433) B3223433
theorem B1911199 : Blo 1788095 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B1788367 : Blo 1788095 1788367 := bstep (se 1 (by rfl) ⟨1341275, by rfl⟩ : syracuseStep 1788367 = 2682551) B2682551
theorem B10193471 : Blo 1788095 10193471 := bstep (se 1 (by rfl) ⟨7645103, by rfl⟩ : syracuseStep 10193471 = 15290207) B15290207
theorem B1788507 : Blo 1788095 1788507 := bstep (se 1 (by rfl) ⟨1341380, by rfl⟩ : syracuseStep 1788507 = 2682761) B2682761
theorem B1788671 : Blo 1788095 1788671 := bstep (se 1 (by rfl) ⟨1341503, by rfl⟩ : syracuseStep 1788671 = 2683007) B2683007
theorem B3820297 : Blo 1788095 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B4025339 : Blo 1788095 4025339 := bstep (se 1 (by rfl) ⟨3019004, by rfl⟩ : syracuseStep 4025339 = 6038009) B6038009
theorem B12241961 : Blo 1788095 12241961 := bstep (se 2 (by rfl) ⟨4590735, by rfl⟩ : syracuseStep 12241961 = 9181471) B9181471
theorem B1789095 : Blo 1788095 1789095 := bstep (se 1 (by rfl) ⟨1341821, by rfl⟩ : syracuseStep 1789095 = 2683643) B2683643
theorem B4025519 : Blo 1788095 4025519 := bstep (se 1 (by rfl) ⟨3019139, by rfl⟩ : syracuseStep 4025519 = 6038279) B6038279
theorem B6040763 : Blo 1788095 6040763 := bstep (se 1 (by rfl) ⟨4530572, by rfl⟩ : syracuseStep 6040763 = 9061145) B9061145
theorem B6122731 : Blo 1788095 6122731 := bstep (se 1 (by rfl) ⟨4592048, by rfl⟩ : syracuseStep 6122731 = 9184097) B9184097
theorem B9055475 : Blo 1788095 9055475 := bstep (se 1 (by rfl) ⟨6791606, by rfl⟩ : syracuseStep 9055475 = 13583213) B13583213
theorem B48967051 : Blo 1788095 48967051 := bstep (se 1 (by rfl) ⟨36725288, by rfl⟩ : syracuseStep 48967051 = 73450577) B73450577
theorem B6450587 : Blo 1788095 6450587 := bstep (se 1 (by rfl) ⟨4837940, by rfl⟩ : syracuseStep 6450587 = 9675881) B9675881
theorem B1789391 : Blo 1788095 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B1789551 : Blo 1788095 1789551 := bstep (se 1 (by rfl) ⟨1342163, by rfl⟩ : syracuseStep 1789551 = 2684327) B2684327
theorem B2682587 : Blo 1788095 2682587 := bstep (se 1 (by rfl) ⟨2011940, by rfl⟩ : syracuseStep 2682587 = 4023881) B4023881
theorem B1789671 : Blo 1788095 1789671 := bstep (se 1 (by rfl) ⟨1342253, by rfl⟩ : syracuseStep 1789671 = 2684507) B2684507
theorem B165228329 : Blo 1788095 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B4026239 : Blo 1788095 4026239 := bstep (se 1 (by rfl) ⟨3019679, by rfl⟩ : syracuseStep 4026239 = 6039359) B6039359
theorem B2265023 : Blo 1788095 2265023 := bstep (se 1 (by rfl) ⟨1698767, by rfl⟩ : syracuseStep 2265023 = 3397535) B3397535
theorem B2682857 : Blo 1788095 2682857 := bstep (se 2 (by rfl) ⟨1006071, by rfl⟩ : syracuseStep 2682857 = 2012143) B2012143
theorem B2682875 : Blo 1788095 2682875 := bstep (se 1 (by rfl) ⟨2012156, by rfl⟩ : syracuseStep 2682875 = 4024313) B4024313
theorem B1789979 : Blo 1788095 1789979 := bstep (se 1 (by rfl) ⟨1342484, by rfl⟩ : syracuseStep 1789979 = 2684969) B2684969
theorem B2682911 : Blo 1788095 2682911 := bstep (se 1 (by rfl) ⟨2012183, by rfl⟩ : syracuseStep 2682911 = 4024367) B4024367
theorem B1789999 : Blo 1788095 1789999 := bstep (se 1 (by rfl) ⟨1342499, by rfl⟩ : syracuseStep 1789999 = 2684999) B2684999
theorem B2682935 : Blo 1788095 2682935 := bstep (se 1 (by rfl) ⟨2012201, by rfl⟩ : syracuseStep 2682935 = 4024403) B4024403
theorem B2683055 : Blo 1788095 2683055 := bstep (se 1 (by rfl) ⟨2012291, by rfl⟩ : syracuseStep 2683055 = 4024583) B4024583
theorem B40308931 : Blo 1788095 40308931 := bstep (se 1 (by rfl) ⟨30231698, by rfl⟩ : syracuseStep 40308931 = 60463397) B60463397
theorem B43544947 : Blo 1788095 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B2683259 : Blo 1788095 2683259 := bstep (se 1 (by rfl) ⟨2012444, by rfl⟩ : syracuseStep 2683259 = 4024889) B4024889
theorem B10187207 : Blo 1788095 10187207 := bstep (se 1 (by rfl) ⟨7640405, by rfl⟩ : syracuseStep 10187207 = 15280811) B15280811
theorem B4526543 : Blo 1788095 4526543 := bstep (se 1 (by rfl) ⟨3394907, by rfl⟩ : syracuseStep 4526543 = 6789815) B6789815
theorem B2011675 : Blo 1788095 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B2683529 : Blo 1788095 2683529 := bstep (se 2 (by rfl) ⟨1006323, by rfl⟩ : syracuseStep 2683529 = 2012647) B2012647
theorem B2011855 : Blo 1788095 2011855 := bstep (se 1 (by rfl) ⟨1508891, by rfl⟩ : syracuseStep 2011855 = 3017783) B3017783
theorem B2683739 : Blo 1788095 2683739 := bstep (se 1 (by rfl) ⟨2012804, by rfl⟩ : syracuseStep 2683739 = 4025609) B4025609
theorem B4027247 : Blo 1788095 4027247 := bstep (se 1 (by rfl) ⟨3020435, by rfl⟩ : syracuseStep 4027247 = 6040871) B6040871
theorem B2683769 : Blo 1788095 2683769 := bstep (se 2 (by rfl) ⟨1006413, by rfl⟩ : syracuseStep 2683769 = 2012827) B2012827
theorem B10884077 : Blo 1788095 10884077 := bstep (se 3 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 10884077 = 4081529) B4081529
theorem B79508789 : Blo 1788095 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B9803069 : Blo 1788095 9803069 := bstep (se 3 (by rfl) ⟨1838075, by rfl⟩ : syracuseStep 9803069 = 3676151) B3676151
theorem B10188139 : Blo 1788095 10188139 := bstep (se 1 (by rfl) ⟨7641104, by rfl⟩ : syracuseStep 10188139 = 15282209) B15282209
theorem B2684399 : Blo 1788095 2684399 := bstep (se 1 (by rfl) ⟨2013299, by rfl⟩ : syracuseStep 2684399 = 4026599) B4026599
theorem B2684519 : Blo 1788095 2684519 := bstep (se 1 (by rfl) ⟨2013389, by rfl⟩ : syracuseStep 2684519 = 4026779) B4026779
theorem B2684975 : Blo 1788095 2684975 := bstep (se 1 (by rfl) ⟨2013731, by rfl⟩ : syracuseStep 2684975 = 4027463) B4027463
theorem B5093513 : Blo 1788095 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B9803929 : Blo 1788095 9803929 := bstep (se 2 (by rfl) ⟨3676473, by rfl⟩ : syracuseStep 9803929 = 7352947) B7352947
theorem B2685095 : Blo 1788095 2685095 := bstep (se 1 (by rfl) ⟨2013821, by rfl⟩ : syracuseStep 2685095 = 4027643) B4027643
theorem B9058553 : Blo 1788095 9058553 := bstep (se 2 (by rfl) ⟨3396957, by rfl⟩ : syracuseStep 9058553 = 6793915) B6793915
theorem B10189097 : Blo 1788095 10189097 := bstep (se 2 (by rfl) ⟨3820911, by rfl⟩ : syracuseStep 10189097 = 7641823) B7641823
theorem B6035795 : Blo 1788095 6035795 := bstep (se 1 (by rfl) ⟨4526846, by rfl⟩ : syracuseStep 6035795 = 9053693) B9053693
theorem B5732765 : Blo 1788095 5732765 := bstep (se 3 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 5732765 = 2149787) B2149787
theorem B21224015 : Blo 1788095 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B3398287 : Blo 1788095 3398287 := bstep (se 1 (by rfl) ⟨2548715, by rfl⟩ : syracuseStep 3398287 = 5097431) B5097431
theorem B77396633 : Blo 1788095 77396633 := bstep (se 2 (by rfl) ⟨29023737, by rfl⟩ : syracuseStep 77396633 = 58047475) B58047475
theorem B6118201 : Blo 1788095 6118201 := bstep (se 2 (by rfl) ⟨2294325, by rfl⟩ : syracuseStep 6118201 = 4588651) B4588651
theorem B6036335 : Blo 1788095 6036335 := bstep (se 1 (by rfl) ⟨4527251, by rfl⟩ : syracuseStep 6036335 = 9054503) B9054503
theorem B2866043 : Blo 1788095 2866043 := bstep (se 1 (by rfl) ⟨2149532, by rfl⟩ : syracuseStep 2866043 = 4299065) B4299065
theorem B6036713 : Blo 1788095 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B7748959 : Blo 1788095 7748959 := bstep (se 1 (by rfl) ⟨5811719, by rfl⟩ : syracuseStep 7748959 = 11623439) B11623439
theorem B5094845 : Blo 1788095 5094845 := bstep (se 3 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 5094845 = 1910567) B1910567
theorem B6037145 : Blo 1788095 6037145 := bstep (se 2 (by rfl) ⟨2263929, by rfl⟩ : syracuseStep 6037145 = 4527859) B4527859
theorem B15277835 : Blo 1788095 15277835 := bstep (se 1 (by rfl) ⟨11458376, by rfl⟩ : syracuseStep 15277835 = 22916753) B22916753
theorem B4529945 : Blo 1788095 4529945 := bstep (se 2 (by rfl) ⟨1698729, by rfl⟩ : syracuseStep 4529945 = 3397459) B3397459
theorem B24469295 : Blo 1788095 24469295 := bstep (se 1 (by rfl) ⟨18351971, by rfl⟩ : syracuseStep 24469295 = 36703943) B36703943
theorem B6790999 : Blo 1788095 6790999 := bstep (se 1 (by rfl) ⟨5093249, by rfl⟩ : syracuseStep 6790999 = 10186499) B10186499
theorem B3490067 : Blo 1788095 3490067 := bstep (se 1 (by rfl) ⟨2617550, by rfl⟩ : syracuseStep 3490067 = 5235101) B5235101
theorem B6791471 : Blo 1788095 6791471 := bstep (se 1 (by rfl) ⟨5093603, by rfl⟩ : syracuseStep 6791471 = 10187207) B10187207
theorem B15286583 : Blo 1788095 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B5095847 : Blo 1788095 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B2548265 : Blo 1788095 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B4531049 : Blo 1788095 4531049 := bstep (se 2 (by rfl) ⟨1699143, by rfl⟩ : syracuseStep 4531049 = 3398287) B3398287
theorem B10879915 : Blo 1788095 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B22922189 : Blo 1788095 22922189 := bstep (se 3 (by rfl) ⟨4297910, by rfl⟩ : syracuseStep 22922189 = 8595821) B8595821
theorem B10880183 : Blo 1788095 10880183 := bstep (se 1 (by rfl) ⟨8160137, by rfl⟩ : syracuseStep 10880183 = 16320275) B16320275
theorem B10880207 : Blo 1788095 10880207 := bstep (se 1 (by rfl) ⟨8160155, by rfl⟩ : syracuseStep 10880207 = 16320311) B16320311
theorem B6039035 : Blo 1788095 6039035 := bstep (se 1 (by rfl) ⟨4529276, by rfl⟩ : syracuseStep 6039035 = 9058553) B9058553
theorem B6792731 : Blo 1788095 6792731 := bstep (se 1 (by rfl) ⟨5094548, by rfl⟩ : syracuseStep 6792731 = 10189097) B10189097
theorem B4023863 : Blo 1788095 4023863 := bstep (se 1 (by rfl) ⟨3017897, by rfl⟩ : syracuseStep 4023863 = 6035795) B6035795
theorem B14149343 : Blo 1788095 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B10331945 : Blo 1788095 10331945 := bstep (se 2 (by rfl) ⟨3874479, by rfl⟩ : syracuseStep 10331945 = 7748959) B7748959
theorem B13584185 : Blo 1788095 13584185 := bstep (se 2 (by rfl) ⟨5094069, by rfl⟩ : syracuseStep 13584185 = 10188139) B10188139
theorem B4024223 : Blo 1788095 4024223 := bstep (se 1 (by rfl) ⟨3018167, by rfl⟩ : syracuseStep 4024223 = 6036335) B6036335
theorem B8161307 : Blo 1788095 8161307 := bstep (se 1 (by rfl) ⟨6120980, by rfl⟩ : syracuseStep 8161307 = 12241961) B12241961
theorem B65251453 : Blo 1788095 65251453 := bstep (se 3 (by rfl) ⟨12234647, by rfl⟩ : syracuseStep 65251453 = 24469295) B24469295
theorem B4024475 : Blo 1788095 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B4024763 : Blo 1788095 4024763 := bstep (se 1 (by rfl) ⟨3018572, by rfl⟩ : syracuseStep 4024763 = 6037145) B6037145
theorem B9054665 : Blo 1788095 9054665 := bstep (se 2 (by rfl) ⟨3395499, by rfl⟩ : syracuseStep 9054665 = 6790999) B6790999
theorem B1788391 : Blo 1788095 1788391 := bstep (se 1 (by rfl) ⟨1341293, by rfl⟩ : syracuseStep 1788391 = 2682587) B2682587
theorem B6040061 : Blo 1788095 6040061 := bstep (se 3 (by rfl) ⟨1132511, by rfl⟩ : syracuseStep 6040061 = 2265023) B2265023
theorem B10185223 : Blo 1788095 10185223 := bstep (se 1 (by rfl) ⟨7638917, by rfl⟩ : syracuseStep 10185223 = 15277835) B15277835
theorem B110152219 : Blo 1788095 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1788571 : Blo 1788095 1788571 := bstep (se 1 (by rfl) ⟨1341428, by rfl⟩ : syracuseStep 1788571 = 2682857) B2682857
theorem B1788583 : Blo 1788095 1788583 := bstep (se 1 (by rfl) ⟨1341437, by rfl⟩ : syracuseStep 1788583 = 2682875) B2682875
theorem B1788607 : Blo 1788095 1788607 := bstep (se 1 (by rfl) ⟨1341455, by rfl⟩ : syracuseStep 1788607 = 2682911) B2682911
theorem B1788623 : Blo 1788095 1788623 := bstep (se 1 (by rfl) ⟨1341467, by rfl⟩ : syracuseStep 1788623 = 2682935) B2682935
theorem B3222281 : Blo 1788095 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B1788703 : Blo 1788095 1788703 := bstep (se 1 (by rfl) ⟨1341527, by rfl⟩ : syracuseStep 1788703 = 2683055) B2683055
theorem B6449951 : Blo 1788095 6449951 := bstep (se 1 (by rfl) ⟨4837463, by rfl⟩ : syracuseStep 6449951 = 9674927) B9674927
theorem B1788839 : Blo 1788095 1788839 := bstep (se 1 (by rfl) ⟨1341629, by rfl⟩ : syracuseStep 1788839 = 2683259) B2683259
theorem B3017695 : Blo 1788095 3017695 := bstep (se 1 (by rfl) ⟨2263271, by rfl⟩ : syracuseStep 3017695 = 4526543) B4526543
theorem B14511095 : Blo 1788095 14511095 := bstep (se 1 (by rfl) ⟨10883321, by rfl⟩ : syracuseStep 14511095 = 21766643) B21766643
theorem B1789019 : Blo 1788095 1789019 := bstep (se 1 (by rfl) ⟨1341764, by rfl⟩ : syracuseStep 1789019 = 2683529) B2683529
theorem B58059929 : Blo 1788095 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B1789159 : Blo 1788095 1789159 := bstep (se 1 (by rfl) ⟨1341869, by rfl⟩ : syracuseStep 1789159 = 2683739) B2683739
theorem B1789179 : Blo 1788095 1789179 := bstep (se 1 (by rfl) ⟨1341884, by rfl⟩ : syracuseStep 1789179 = 2683769) B2683769
theorem B2682233 : Blo 1788095 2682233 := bstep (se 2 (by rfl) ⟨1005837, by rfl⟩ : syracuseStep 2682233 = 2011675) B2011675
theorem B19344835 : Blo 1788095 19344835 := bstep (se 1 (by rfl) ⟨14508626, by rfl⟩ : syracuseStep 19344835 = 29017253) B29017253
theorem B2682347 : Blo 1788095 2682347 := bstep (se 1 (by rfl) ⟨2011760, by rfl⟩ : syracuseStep 2682347 = 4023521) B4023521
theorem B53005859 : Blo 1788095 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B2682473 : Blo 1788095 2682473 := bstep (se 2 (by rfl) ⟨1005927, by rfl⟩ : syracuseStep 2682473 = 2011855) B2011855
theorem B1789599 : Blo 1788095 1789599 := bstep (se 1 (by rfl) ⟨1342199, by rfl⟩ : syracuseStep 1789599 = 2684399) B2684399
theorem B11464375 : Blo 1788095 11464375 := bstep (se 1 (by rfl) ⟨8598281, by rfl⟩ : syracuseStep 11464375 = 17196563) B17196563
theorem B1789679 : Blo 1788095 1789679 := bstep (se 1 (by rfl) ⟨1342259, by rfl⟩ : syracuseStep 1789679 = 2684519) B2684519
theorem B4026203 : Blo 1788095 4026203 := bstep (se 1 (by rfl) ⟨3019652, by rfl⟩ : syracuseStep 4026203 = 6039305) B6039305
theorem B2682791 : Blo 1788095 2682791 := bstep (se 1 (by rfl) ⟨2012093, by rfl⟩ : syracuseStep 2682791 = 4024187) B4024187
theorem B1789983 : Blo 1788095 1789983 := bstep (se 1 (by rfl) ⟨1342487, by rfl⟩ : syracuseStep 1789983 = 2684975) B2684975
theorem B2682971 : Blo 1788095 2682971 := bstep (se 1 (by rfl) ⟨2012228, by rfl⟩ : syracuseStep 2682971 = 4024457) B4024457
theorem B3395675 : Blo 1788095 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B1790063 : Blo 1788095 1790063 := bstep (se 1 (by rfl) ⟨1342547, by rfl⟩ : syracuseStep 1790063 = 2685095) B2685095
theorem B3821843 : Blo 1788095 3821843 := bstep (se 1 (by rfl) ⟨2866382, by rfl⟩ : syracuseStep 3821843 = 5732765) B5732765
theorem B8163641 : Blo 1788095 8163641 := bstep (se 2 (by rfl) ⟨3061365, by rfl⟩ : syracuseStep 8163641 = 6122731) B6122731
theorem B6795647 : Blo 1788095 6795647 := bstep (se 1 (by rfl) ⟨5096735, by rfl⟩ : syracuseStep 6795647 = 10193471) B10193471
theorem B51597755 : Blo 1788095 51597755 := bstep (se 1 (by rfl) ⟨38698316, by rfl⟩ : syracuseStep 51597755 = 77396633) B77396633
theorem B2683559 : Blo 1788095 2683559 := bstep (se 1 (by rfl) ⟨2012669, by rfl⟩ : syracuseStep 2683559 = 4025339) B4025339
theorem B2683679 : Blo 1788095 2683679 := bstep (se 1 (by rfl) ⟨2012759, by rfl⟩ : syracuseStep 2683679 = 4025519) B4025519
theorem B4027175 : Blo 1788095 4027175 := bstep (se 1 (by rfl) ⟨3020381, by rfl⟩ : syracuseStep 4027175 = 6040763) B6040763
theorem B3396563 : Blo 1788095 3396563 := bstep (se 1 (by rfl) ⟨2547422, by rfl⟩ : syracuseStep 3396563 = 5094845) B5094845
theorem B3019963 : Blo 1788095 3019963 := bstep (se 1 (by rfl) ⟨2264972, by rfl⟩ : syracuseStep 3019963 = 4529945) B4529945
theorem B2684159 : Blo 1788095 2684159 := bstep (se 1 (by rfl) ⟨2013119, by rfl⟩ : syracuseStep 2684159 = 4026239) B4026239
theorem B3823031 : Blo 1788095 3823031 := bstep (se 1 (by rfl) ⟨2867273, by rfl⟩ : syracuseStep 3823031 = 5734547) B5734547
theorem B13071905 : Blo 1788095 13071905 := bstep (se 2 (by rfl) ⟨4901964, by rfl⟩ : syracuseStep 13071905 = 9803929) B9803929
theorem B53745241 : Blo 1788095 53745241 := bstep (se 2 (by rfl) ⟨20154465, by rfl⟩ : syracuseStep 53745241 = 40308931) B40308931
theorem B6035039 : Blo 1788095 6035039 := bstep (se 1 (by rfl) ⟨4526279, by rfl⟩ : syracuseStep 6035039 = 9052559) B9052559
theorem B3020395 : Blo 1788095 3020395 := bstep (se 1 (by rfl) ⟨2265296, by rfl⟩ : syracuseStep 3020395 = 4530593) B4530593
theorem B97892057 : Blo 1788095 97892057 := bstep (se 2 (by rfl) ⟨36709521, by rfl⟩ : syracuseStep 97892057 = 73419043) B73419043
theorem B2684831 : Blo 1788095 2684831 := bstep (se 1 (by rfl) ⟨2013623, by rfl⟩ : syracuseStep 2684831 = 4027247) B4027247
theorem B7256051 : Blo 1788095 7256051 := bstep (se 1 (by rfl) ⟨5442038, by rfl⟩ : syracuseStep 7256051 = 10884077) B10884077
theorem B6445223 : Blo 1788095 6445223 := bstep (se 1 (by rfl) ⟨4833917, by rfl⟩ : syracuseStep 6445223 = 9667835) B9667835
theorem B6535379 : Blo 1788095 6535379 := bstep (se 1 (by rfl) ⟨4901534, by rfl⟩ : syracuseStep 6535379 = 9803069) B9803069
theorem B5093729 : Blo 1788095 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B8157601 : Blo 1788095 8157601 := bstep (se 2 (by rfl) ⟨3059100, by rfl⟩ : syracuseStep 8157601 = 6118201) B6118201
theorem B65289401 : Blo 1788095 65289401 := bstep (se 2 (by rfl) ⟨24483525, by rfl⟩ : syracuseStep 65289401 = 48967051) B48967051
theorem B6036983 : Blo 1788095 6036983 := bstep (se 1 (by rfl) ⟨4527737, by rfl⟩ : syracuseStep 6036983 = 9055475) B9055475
theorem B4300391 : Blo 1788095 4300391 := bstep (se 1 (by rfl) ⟨3225293, by rfl⟩ : syracuseStep 4300391 = 6450587) B6450587
theorem B7642781 : Blo 1788095 7642781 := bstep (se 3 (by rfl) ⟨1433021, by rfl⟩ : syracuseStep 7642781 = 2866043) B2866043
theorem B58031909 : Blo 1788095 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B2326711 : Blo 1788095 2326711 := bstep (se 1 (by rfl) ⟨1745033, by rfl⟩ : syracuseStep 2326711 = 3490067) B3490067
theorem B10191055 : Blo 1788095 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B4530431 : Blo 1788095 4530431 := bstep (se 1 (by rfl) ⟨3397823, by rfl⟩ : syracuseStep 4530431 = 6795647) B6795647
theorem B34398503 : Blo 1788095 34398503 := bstep (se 1 (by rfl) ⟨25798877, by rfl⟩ : syracuseStep 34398503 = 51597755) B51597755
theorem B10191581 : Blo 1788095 10191581 := bstep (se 3 (by rfl) ⟨1910921, by rfl⟩ : syracuseStep 10191581 = 3821843) B3821843
theorem B2548687 : Blo 1788095 2548687 := bstep (se 1 (by rfl) ⟨1911515, by rfl⟩ : syracuseStep 2548687 = 3823031) B3823031
theorem B4023359 : Blo 1788095 4023359 := bstep (se 1 (by rfl) ⟨3017519, by rfl⟩ : syracuseStep 4023359 = 6035039) B6035039
theorem B4023593 : Blo 1788095 4023593 := bstep (se 2 (by rfl) ⟨1508847, by rfl⟩ : syracuseStep 4023593 = 3017695) B3017695
theorem B5440871 : Blo 1788095 5440871 := bstep (se 1 (by rfl) ⟨4080653, by rfl⟩ : syracuseStep 5440871 = 8161307) B8161307
theorem B2148187 : Blo 1788095 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B43526267 : Blo 1788095 43526267 := bstep (se 1 (by rfl) ⟨32644700, by rfl⟩ : syracuseStep 43526267 = 65289401) B65289401
theorem B1788155 : Blo 1788095 1788155 := bstep (se 1 (by rfl) ⟨1341116, by rfl⟩ : syracuseStep 1788155 = 2682233) B2682233
theorem B1788231 : Blo 1788095 1788231 := bstep (se 1 (by rfl) ⟨1341173, by rfl⟩ : syracuseStep 1788231 = 2682347) B2682347
theorem B4024655 : Blo 1788095 4024655 := bstep (se 1 (by rfl) ⟨3018491, by rfl⟩ : syracuseStep 4024655 = 6036983) B6036983
theorem B1788315 : Blo 1788095 1788315 := bstep (se 1 (by rfl) ⟨1341236, by rfl⟩ : syracuseStep 1788315 = 2682473) B2682473
theorem B1788527 : Blo 1788095 1788527 := bstep (se 1 (by rfl) ⟨1341395, by rfl⟩ : syracuseStep 1788527 = 2682791) B2682791
theorem B1788647 : Blo 1788095 1788647 := bstep (se 1 (by rfl) ⟨1341485, by rfl⟩ : syracuseStep 1788647 = 2682971) B2682971
theorem B2263783 : Blo 1788095 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B87001937 : Blo 1788095 87001937 := bstep (se 2 (by rfl) ⟨32625726, by rfl⟩ : syracuseStep 87001937 = 65251453) B65251453
theorem B5442427 : Blo 1788095 5442427 := bstep (se 1 (by rfl) ⟨4081820, by rfl⟩ : syracuseStep 5442427 = 8163641) B8163641
theorem B1789039 : Blo 1788095 1789039 := bstep (se 1 (by rfl) ⟨1341779, by rfl⟩ : syracuseStep 1789039 = 2683559) B2683559
theorem B1789119 : Blo 1788095 1789119 := bstep (se 1 (by rfl) ⟨1341839, by rfl⟩ : syracuseStep 1789119 = 2683679) B2683679
theorem B15281459 : Blo 1788095 15281459 := bstep (se 1 (by rfl) ⟨11461094, by rfl⟩ : syracuseStep 15281459 = 22922189) B22922189
theorem B2264375 : Blo 1788095 2264375 := bstep (se 1 (by rfl) ⟨1698281, by rfl⟩ : syracuseStep 2264375 = 3396563) B3396563
theorem B146869625 : Blo 1788095 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B7253471 : Blo 1788095 7253471 := bstep (se 1 (by rfl) ⟨5440103, by rfl⟩ : syracuseStep 7253471 = 10880207) B10880207
theorem B1789439 : Blo 1788095 1789439 := bstep (se 1 (by rfl) ⟨1342079, by rfl⟩ : syracuseStep 1789439 = 2684159) B2684159
theorem B4026023 : Blo 1788095 4026023 := bstep (se 1 (by rfl) ⟨3019517, by rfl⟩ : syracuseStep 4026023 = 6039035) B6039035
theorem B2682575 : Blo 1788095 2682575 := bstep (se 1 (by rfl) ⟨2011931, by rfl⟩ : syracuseStep 2682575 = 4023863) B4023863
theorem B65261371 : Blo 1788095 65261371 := bstep (se 1 (by rfl) ⟨48946028, by rfl⟩ : syracuseStep 65261371 = 97892057) B97892057
theorem B9432895 : Blo 1788095 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B9056123 : Blo 1788095 9056123 := bstep (se 1 (by rfl) ⟨6792092, by rfl⟩ : syracuseStep 9056123 = 13584185) B13584185
theorem B2682815 : Blo 1788095 2682815 := bstep (se 1 (by rfl) ⟨2012111, by rfl⟩ : syracuseStep 2682815 = 4024223) B4024223
theorem B1789887 : Blo 1788095 1789887 := bstep (se 1 (by rfl) ⟨1342415, by rfl⟩ : syracuseStep 1789887 = 2684831) B2684831
theorem B4837367 : Blo 1788095 4837367 := bstep (se 1 (by rfl) ⟨3628025, by rfl⟩ : syracuseStep 4837367 = 7256051) B7256051
theorem B2682983 : Blo 1788095 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B4296815 : Blo 1788095 4296815 := bstep (se 1 (by rfl) ⟨3222611, by rfl⟩ : syracuseStep 4296815 = 6445223) B6445223
theorem B6795373 : Blo 1788095 6795373 := bstep (se 3 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 6795373 = 2548265) B2548265
theorem B3395819 : Blo 1788095 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B4026617 : Blo 1788095 4026617 := bstep (se 2 (by rfl) ⟨1509981, by rfl⟩ : syracuseStep 4026617 = 3019963) B3019963
theorem B2683175 : Blo 1788095 2683175 := bstep (se 1 (by rfl) ⟨2012381, by rfl⟩ : syracuseStep 2683175 = 4024763) B4024763
theorem B4026707 : Blo 1788095 4026707 := bstep (se 1 (by rfl) ⟨3020030, by rfl⟩ : syracuseStep 4026707 = 6040061) B6040061
theorem B25793113 : Blo 1788095 25793113 := bstep (se 2 (by rfl) ⟨9672417, by rfl⟩ : syracuseStep 25793113 = 19344835) B19344835
theorem B71660321 : Blo 1788095 71660321 := bstep (se 2 (by rfl) ⟨26872620, by rfl⟩ : syracuseStep 71660321 = 53745241) B53745241
theorem B4027193 : Blo 1788095 4027193 := bstep (se 2 (by rfl) ⟨1510197, by rfl⟩ : syracuseStep 4027193 = 3020395) B3020395
theorem B35337239 : Blo 1788095 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B38687939 : Blo 1788095 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B2684135 : Blo 1788095 2684135 := bstep (se 1 (by rfl) ⟨2013101, by rfl⟩ : syracuseStep 2684135 = 4026203) B4026203
theorem B4527647 : Blo 1788095 4527647 := bstep (se 1 (by rfl) ⟨3395735, by rfl⟩ : syracuseStep 4527647 = 6791471) B6791471
theorem B3397231 : Blo 1788095 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B154826477 : Blo 1788095 154826477 := bstep (se 3 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 154826477 = 58059929) B58059929
theorem B29013821 : Blo 1788095 29013821 := bstep (se 3 (by rfl) ⟨5440091, by rfl⟩ : syracuseStep 29013821 = 10880183) B10880183
theorem B2684783 : Blo 1788095 2684783 := bstep (se 1 (by rfl) ⟨2013587, by rfl⟩ : syracuseStep 2684783 = 4027175) B4027175
theorem B10876801 : Blo 1788095 10876801 := bstep (se 2 (by rfl) ⟨4078800, by rfl⟩ : syracuseStep 10876801 = 8157601) B8157601
theorem B3020699 : Blo 1788095 3020699 := bstep (se 1 (by rfl) ⟨2265524, by rfl⟩ : syracuseStep 3020699 = 4531049) B4531049
theorem B13580297 : Blo 1788095 13580297 := bstep (se 2 (by rfl) ⟨5092611, by rfl⟩ : syracuseStep 13580297 = 10185223) B10185223
theorem B4528487 : Blo 1788095 4528487 := bstep (se 1 (by rfl) ⟨3396365, by rfl⟩ : syracuseStep 4528487 = 6792731) B6792731
theorem B8714603 : Blo 1788095 8714603 := bstep (se 1 (by rfl) ⟨6535952, by rfl⟩ : syracuseStep 8714603 = 13071905) B13071905
theorem B6887963 : Blo 1788095 6887963 := bstep (se 1 (by rfl) ⟨5165972, by rfl⟩ : syracuseStep 6887963 = 10331945) B10331945
theorem B14506553 : Blo 1788095 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B4356919 : Blo 1788095 4356919 := bstep (se 1 (by rfl) ⟨3267689, by rfl⟩ : syracuseStep 4356919 = 6535379) B6535379
theorem B6036443 : Blo 1788095 6036443 := bstep (se 1 (by rfl) ⟨4527332, by rfl⟩ : syracuseStep 6036443 = 9054665) B9054665
theorem B4299967 : Blo 1788095 4299967 := bstep (se 1 (by rfl) ⟨3224975, by rfl⟩ : syracuseStep 4299967 = 6449951) B6449951
theorem B9674063 : Blo 1788095 9674063 := bstep (se 1 (by rfl) ⟨7255547, by rfl⟩ : syracuseStep 9674063 = 14511095) B14511095
theorem B15285833 : Blo 1788095 15285833 := bstep (se 2 (by rfl) ⟨5732187, by rfl⟩ : syracuseStep 15285833 = 11464375) B11464375
theorem B2866927 : Blo 1788095 2866927 := bstep (se 1 (by rfl) ⟨2150195, by rfl⟩ : syracuseStep 2866927 = 4300391) B4300391
theorem B5095187 : Blo 1788095 5095187 := bstep (se 1 (by rfl) ⟨3821390, by rfl⟩ : syracuseStep 5095187 = 7642781) B7642781
theorem B9060497 : Blo 1788095 9060497 := bstep (se 2 (by rfl) ⟨3397686, by rfl⟩ : syracuseStep 9060497 = 6795373) B6795373
theorem B34390817 : Blo 1788095 34390817 := bstep (se 2 (by rfl) ⟨12896556, by rfl⟩ : syracuseStep 34390817 = 25793113) B25793113
theorem B6038333 : Blo 1788095 6038333 := bstep (se 3 (by rfl) ⟨1132187, by rfl⟩ : syracuseStep 6038333 = 2264375) B2264375
theorem B5809225 : Blo 1788095 5809225 := bstep (se 2 (by rfl) ⟨2178459, by rfl⟩ : syracuseStep 5809225 = 4356919) B4356919
theorem B19342547 : Blo 1788095 19342547 := bstep (se 1 (by rfl) ⟨14506910, by rfl⟩ : syracuseStep 19342547 = 29013821) B29013821
theorem B9053531 : Blo 1788095 9053531 := bstep (se 1 (by rfl) ⟨6790148, by rfl⟩ : syracuseStep 9053531 = 13580297) B13580297
theorem B29017511 : Blo 1788095 29017511 := bstep (se 1 (by rfl) ⟨21763133, by rfl⟩ : syracuseStep 29017511 = 43526267) B43526267
theorem B5809735 : Blo 1788095 5809735 := bstep (se 1 (by rfl) ⟨4357301, by rfl⟩ : syracuseStep 5809735 = 8714603) B8714603
theorem B58001291 : Blo 1788095 58001291 := bstep (se 1 (by rfl) ⟨43500968, by rfl⟩ : syracuseStep 58001291 = 87001937) B87001937
theorem B4024295 : Blo 1788095 4024295 := bstep (se 1 (by rfl) ⟨3018221, by rfl⟩ : syracuseStep 4024295 = 6036443) B6036443
theorem B6449375 : Blo 1788095 6449375 := bstep (se 1 (by rfl) ⟨4837031, by rfl⟩ : syracuseStep 6449375 = 9674063) B9674063
theorem B97913083 : Blo 1788095 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B4835647 : Blo 1788095 4835647 := bstep (se 1 (by rfl) ⟨3626735, by rfl⟩ : syracuseStep 4835647 = 7253471) B7253471
theorem B12577193 : Blo 1788095 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B1788383 : Blo 1788095 1788383 := bstep (se 1 (by rfl) ⟨1341287, by rfl⟩ : syracuseStep 1788383 = 2682575) B2682575
theorem B14502401 : Blo 1788095 14502401 := bstep (se 2 (by rfl) ⟨5438400, by rfl⟩ : syracuseStep 14502401 = 10876801) B10876801
theorem B1788543 : Blo 1788095 1788543 := bstep (se 1 (by rfl) ⟨1341407, by rfl⟩ : syracuseStep 1788543 = 2682815) B2682815
theorem B1788655 : Blo 1788095 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B2263879 : Blo 1788095 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B1788783 : Blo 1788095 1788783 := bstep (se 1 (by rfl) ⟨1341587, by rfl⟩ : syracuseStep 1788783 = 2683175) B2683175
theorem B22932335 : Blo 1788095 22932335 := bstep (se 1 (by rfl) ⟨17199251, by rfl⟩ : syracuseStep 22932335 = 34398503) B34398503
theorem B6794387 : Blo 1788095 6794387 := bstep (se 1 (by rfl) ⟨5095790, by rfl⟩ : syracuseStep 6794387 = 10191581) B10191581
theorem B2682239 : Blo 1788095 2682239 := bstep (se 1 (by rfl) ⟨2011679, by rfl⟩ : syracuseStep 2682239 = 4023359) B4023359
theorem B25791959 : Blo 1788095 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B1789423 : Blo 1788095 1789423 := bstep (se 1 (by rfl) ⟨1342067, by rfl⟩ : syracuseStep 1789423 = 2684135) B2684135
theorem B2682395 : Blo 1788095 2682395 := bstep (se 1 (by rfl) ⟨2011796, by rfl⟩ : syracuseStep 2682395 = 4023593) B4023593
theorem B3018377 : Blo 1788095 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B3018431 : Blo 1788095 3018431 := bstep (se 1 (by rfl) ⟨2263823, by rfl⟩ : syracuseStep 3018431 = 4527647) B4527647
theorem B1789855 : Blo 1788095 1789855 := bstep (se 1 (by rfl) ⟨1342391, by rfl⟩ : syracuseStep 1789855 = 2684783) B2684783
theorem B2683103 : Blo 1788095 2683103 := bstep (se 1 (by rfl) ⟨2012327, by rfl⟩ : syracuseStep 2683103 = 4024655) B4024655
theorem B3018991 : Blo 1788095 3018991 := bstep (se 1 (by rfl) ⟨2264243, by rfl⟩ : syracuseStep 3018991 = 4528487) B4528487
theorem B4591975 : Blo 1788095 4591975 := bstep (se 1 (by rfl) ⟨3443981, by rfl⟩ : syracuseStep 4591975 = 6887963) B6887963
theorem B9671035 : Blo 1788095 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B10187639 : Blo 1788095 10187639 := bstep (se 1 (by rfl) ⟨7640729, by rfl⟩ : syracuseStep 10187639 = 15281459) B15281459
theorem B3822569 : Blo 1788095 3822569 := bstep (se 2 (by rfl) ⟨1433463, by rfl⟩ : syracuseStep 3822569 = 2866927) B2866927
theorem B2684015 : Blo 1788095 2684015 := bstep (se 1 (by rfl) ⟨2013011, by rfl⟩ : syracuseStep 2684015 = 4026023) B4026023
theorem B2864249 : Blo 1788095 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B3396791 : Blo 1788095 3396791 := bstep (se 1 (by rfl) ⟨2547593, by rfl⟩ : syracuseStep 3396791 = 5095187) B5095187
theorem B12899645 : Blo 1788095 12899645 := bstep (se 3 (by rfl) ⟨2418683, by rfl⟩ : syracuseStep 12899645 = 4837367) B4837367
theorem B2864543 : Blo 1788095 2864543 := bstep (se 1 (by rfl) ⟨2148407, by rfl⟩ : syracuseStep 2864543 = 4296815) B4296815
theorem B2684411 : Blo 1788095 2684411 := bstep (se 1 (by rfl) ⟨2013308, by rfl⟩ : syracuseStep 2684411 = 4026617) B4026617
theorem B3020287 : Blo 1788095 3020287 := bstep (se 1 (by rfl) ⟨2265215, by rfl⟩ : syracuseStep 3020287 = 4530431) B4530431
theorem B2684471 : Blo 1788095 2684471 := bstep (se 1 (by rfl) ⟨2013353, by rfl⟩ : syracuseStep 2684471 = 4026707) B4026707
theorem B3102281 : Blo 1788095 3102281 := bstep (se 2 (by rfl) ⟨1163355, by rfl⟩ : syracuseStep 3102281 = 2326711) B2326711
theorem B13588073 : Blo 1788095 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B47773547 : Blo 1788095 47773547 := bstep (se 1 (by rfl) ⟨35830160, by rfl⟩ : syracuseStep 47773547 = 71660321) B71660321
theorem B2684795 : Blo 1788095 2684795 := bstep (se 1 (by rfl) ⟨2013596, by rfl⟩ : syracuseStep 2684795 = 4027193) B4027193
theorem B23558159 : Blo 1788095 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B3627247 : Blo 1788095 3627247 := bstep (se 1 (by rfl) ⟨2720435, by rfl⟩ : syracuseStep 3627247 = 5440871) B5440871
theorem B103217651 : Blo 1788095 103217651 := bstep (se 1 (by rfl) ⟨77413238, by rfl⟩ : syracuseStep 103217651 = 154826477) B154826477
theorem B7256569 : Blo 1788095 7256569 := bstep (se 2 (by rfl) ⟨2721213, by rfl⟩ : syracuseStep 7256569 = 5442427) B5442427
theorem B2013799 : Blo 1788095 2013799 := bstep (se 1 (by rfl) ⟨1510349, by rfl⟩ : syracuseStep 2013799 = 3020699) B3020699
theorem B3398249 : Blo 1788095 3398249 := bstep (se 2 (by rfl) ⟨1274343, by rfl⟩ : syracuseStep 3398249 = 2548687) B2548687
theorem B5733289 : Blo 1788095 5733289 := bstep (se 2 (by rfl) ⟨2149983, by rfl⟩ : syracuseStep 5733289 = 4299967) B4299967
theorem B4529641 : Blo 1788095 4529641 := bstep (se 2 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 4529641 = 3397231) B3397231
theorem B10190555 : Blo 1788095 10190555 := bstep (se 1 (by rfl) ⟨7642916, by rfl⟩ : syracuseStep 10190555 = 15285833) B15285833
theorem B87015161 : Blo 1788095 87015161 := bstep (se 2 (by rfl) ⟨32630685, by rfl⟩ : syracuseStep 87015161 = 65261371) B65261371
theorem B6037415 : Blo 1788095 6037415 := bstep (se 1 (by rfl) ⟨4528061, by rfl⟩ : syracuseStep 6037415 = 9056123) B9056123
theorem B6447529 : Blo 1788095 6447529 := bstep (se 2 (by rfl) ⟨2417823, by rfl⟩ : syracuseStep 6447529 = 4835647) B4835647
theorem B12894713 : Blo 1788095 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B6791759 : Blo 1788095 6791759 := bstep (se 1 (by rfl) ⟨5093819, by rfl⟩ : syracuseStep 6791759 = 10187639) B10187639
theorem B2548379 : Blo 1788095 2548379 := bstep (se 1 (by rfl) ⟨1911284, by rfl⟩ : syracuseStep 2548379 = 3822569) B3822569
theorem B9675425 : Blo 1788095 9675425 := bstep (se 2 (by rfl) ⟨3628284, by rfl⟩ : syracuseStep 9675425 = 7256569) B7256569
theorem B1909499 : Blo 1788095 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B12895031 : Blo 1788095 12895031 := bstep (se 1 (by rfl) ⟨9671273, by rfl⟩ : syracuseStep 12895031 = 19342547) B19342547
theorem B7644385 : Blo 1788095 7644385 := bstep (se 2 (by rfl) ⟨2866644, by rfl⟩ : syracuseStep 7644385 = 5733289) B5733289
theorem B38667527 : Blo 1788095 38667527 := bstep (se 1 (by rfl) ⟨29000645, by rfl⟩ : syracuseStep 38667527 = 58001291) B58001291
theorem B9668267 : Blo 1788095 9668267 := bstep (se 1 (by rfl) ⟨7251200, by rfl⟩ : syracuseStep 9668267 = 14502401) B14502401
theorem B15288223 : Blo 1788095 15288223 := bstep (se 1 (by rfl) ⟨11466167, by rfl⟩ : syracuseStep 15288223 = 22932335) B22932335
theorem B6039521 : Blo 1788095 6039521 := bstep (se 2 (by rfl) ⟨2264820, by rfl⟩ : syracuseStep 6039521 = 4529641) B4529641
theorem B1788159 : Blo 1788095 1788159 := bstep (se 1 (by rfl) ⟨1341119, by rfl⟩ : syracuseStep 1788159 = 2682239) B2682239
theorem B1788263 : Blo 1788095 1788263 := bstep (se 1 (by rfl) ⟨1341197, by rfl⟩ : syracuseStep 1788263 = 2682395) B2682395
theorem B6793703 : Blo 1788095 6793703 := bstep (se 1 (by rfl) ⟨5095277, by rfl⟩ : syracuseStep 6793703 = 10190555) B10190555
theorem B58010107 : Blo 1788095 58010107 := bstep (se 1 (by rfl) ⟨43507580, by rfl⟩ : syracuseStep 58010107 = 87015161) B87015161
theorem B4024943 : Blo 1788095 4024943 := bstep (se 1 (by rfl) ⟨3018707, by rfl⟩ : syracuseStep 4024943 = 6037415) B6037415
theorem B6040331 : Blo 1788095 6040331 := bstep (se 1 (by rfl) ⟨4530248, by rfl⟩ : syracuseStep 6040331 = 9060497) B9060497
theorem B1788735 : Blo 1788095 1788735 := bstep (se 1 (by rfl) ⟨1341551, by rfl⟩ : syracuseStep 1788735 = 2683103) B2683103
theorem B4025321 : Blo 1788095 4025321 := bstep (se 2 (by rfl) ⟨1509495, by rfl⟩ : syracuseStep 4025321 = 3018991) B3018991
theorem B4836329 : Blo 1788095 4836329 := bstep (se 2 (by rfl) ⟨1813623, by rfl⟩ : syracuseStep 4836329 = 3627247) B3627247
theorem B130550777 : Blo 1788095 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B6122633 : Blo 1788095 6122633 := bstep (se 2 (by rfl) ⟨2295987, by rfl⟩ : syracuseStep 6122633 = 4591975) B4591975
theorem B4025555 : Blo 1788095 4025555 := bstep (se 1 (by rfl) ⟨3019166, by rfl⟩ : syracuseStep 4025555 = 6038333) B6038333
theorem B1789343 : Blo 1788095 1789343 := bstep (se 1 (by rfl) ⟨1342007, by rfl⟩ : syracuseStep 1789343 = 2684015) B2684015
theorem B2264527 : Blo 1788095 2264527 := bstep (se 1 (by rfl) ⟨1698395, by rfl⟩ : syracuseStep 2264527 = 3396791) B3396791
theorem B19345007 : Blo 1788095 19345007 := bstep (se 1 (by rfl) ⟨14508755, by rfl⟩ : syracuseStep 19345007 = 29017511) B29017511
theorem B1789607 : Blo 1788095 1789607 := bstep (se 1 (by rfl) ⟨1342205, by rfl⟩ : syracuseStep 1789607 = 2684411) B2684411
theorem B1789647 : Blo 1788095 1789647 := bstep (se 1 (by rfl) ⟨1342235, by rfl⟩ : syracuseStep 1789647 = 2684471) B2684471
theorem B2068187 : Blo 1788095 2068187 := bstep (se 1 (by rfl) ⟨1551140, by rfl⟩ : syracuseStep 2068187 = 3102281) B3102281
theorem B7638781 : Blo 1788095 7638781 := bstep (se 3 (by rfl) ⟨1432271, by rfl⟩ : syracuseStep 7638781 = 2864543) B2864543
theorem B3018505 : Blo 1788095 3018505 := bstep (se 2 (by rfl) ⟨1131939, by rfl⟩ : syracuseStep 3018505 = 2263879) B2263879
theorem B1789863 : Blo 1788095 1789863 := bstep (se 1 (by rfl) ⟨1342397, by rfl⟩ : syracuseStep 1789863 = 2684795) B2684795
theorem B2682863 : Blo 1788095 2682863 := bstep (se 1 (by rfl) ⟨2012147, by rfl⟩ : syracuseStep 2682863 = 4024295) B4024295
theorem B7745633 : Blo 1788095 7745633 := bstep (se 2 (by rfl) ⟨2904612, by rfl⟩ : syracuseStep 7745633 = 5809225) B5809225
theorem B8384795 : Blo 1788095 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B2265499 : Blo 1788095 2265499 := bstep (se 1 (by rfl) ⟨1699124, by rfl⟩ : syracuseStep 2265499 = 3398249) B3398249
theorem B4027049 : Blo 1788095 4027049 := bstep (se 2 (by rfl) ⟨1510143, by rfl⟩ : syracuseStep 4027049 = 3020287) B3020287
theorem B7746313 : Blo 1788095 7746313 := bstep (se 2 (by rfl) ⟨2904867, by rfl⟩ : syracuseStep 7746313 = 5809735) B5809735
theorem B2012251 : Blo 1788095 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B2012287 : Blo 1788095 2012287 := bstep (se 1 (by rfl) ⟨1509215, by rfl⟩ : syracuseStep 2012287 = 3018431) B3018431
theorem B62821757 : Blo 1788095 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B22927211 : Blo 1788095 22927211 := bstep (se 1 (by rfl) ⟨17195408, by rfl⟩ : syracuseStep 22927211 = 34390817) B34390817
theorem B2685065 : Blo 1788095 2685065 := bstep (se 2 (by rfl) ⟨1006899, by rfl⟩ : syracuseStep 2685065 = 2013799) B2013799
theorem B8599763 : Blo 1788095 8599763 := bstep (se 1 (by rfl) ⟨6449822, by rfl⟩ : syracuseStep 8599763 = 12899645) B12899645
theorem B6035687 : Blo 1788095 6035687 := bstep (se 1 (by rfl) ⟨4526765, by rfl⟩ : syracuseStep 6035687 = 9053531) B9053531
theorem B9058715 : Blo 1788095 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B31849031 : Blo 1788095 31849031 := bstep (se 1 (by rfl) ⟨23886773, by rfl⟩ : syracuseStep 31849031 = 47773547) B47773547
theorem B4299583 : Blo 1788095 4299583 := bstep (se 1 (by rfl) ⟨3224687, by rfl⟩ : syracuseStep 4299583 = 6449375) B6449375
theorem B68811767 : Blo 1788095 68811767 := bstep (se 1 (by rfl) ⟨51608825, by rfl⟩ : syracuseStep 68811767 = 103217651) B103217651
theorem B4529591 : Blo 1788095 4529591 := bstep (se 1 (by rfl) ⟨3397193, by rfl⟩ : syracuseStep 4529591 = 6794387) B6794387
theorem B17194639 : Blo 1788095 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B16327021 : Blo 1788095 16327021 := bstep (se 3 (by rfl) ⟨3061316, by rfl⟩ : syracuseStep 16327021 = 6122633) B6122633
theorem B4023791 : Blo 1788095 4023791 := bstep (se 1 (by rfl) ⟨3017843, by rfl⟩ : syracuseStep 4023791 = 6035687) B6035687
theorem B6039143 : Blo 1788095 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B10192513 : Blo 1788095 10192513 := bstep (se 2 (by rfl) ⟨3822192, by rfl⟩ : syracuseStep 10192513 = 7644385) B7644385
theorem B5515165 : Blo 1788095 5515165 := bstep (se 3 (by rfl) ⟨1034093, by rfl⟩ : syracuseStep 5515165 = 2068187) B2068187
theorem B87033851 : Blo 1788095 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B10185041 : Blo 1788095 10185041 := bstep (se 2 (by rfl) ⟨3819390, by rfl⟩ : syracuseStep 10185041 = 7638781) B7638781
theorem B4024673 : Blo 1788095 4024673 := bstep (se 2 (by rfl) ⟨1509252, by rfl⟩ : syracuseStep 4024673 = 3018505) B3018505
theorem B12896671 : Blo 1788095 12896671 := bstep (se 1 (by rfl) ⟨9672503, by rfl⟩ : syracuseStep 12896671 = 19345007) B19345007
theorem B20384297 : Blo 1788095 20384297 := bstep (se 2 (by rfl) ⟨7644111, by rfl⟩ : syracuseStep 20384297 = 15288223) B15288223
theorem B1788575 : Blo 1788095 1788575 := bstep (se 1 (by rfl) ⟨1341431, by rfl⟩ : syracuseStep 1788575 = 2682863) B2682863
theorem B5163755 : Blo 1788095 5163755 := bstep (se 1 (by rfl) ⟨3872816, by rfl⟩ : syracuseStep 5163755 = 7745633) B7745633
theorem B5589863 : Blo 1788095 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B8596475 : Blo 1788095 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B6450283 : Blo 1788095 6450283 := bstep (se 1 (by rfl) ⟨4837712, by rfl⟩ : syracuseStep 6450283 = 9675425) B9675425
theorem B8596687 : Blo 1788095 8596687 := bstep (se 1 (by rfl) ⟨6447515, by rfl⟩ : syracuseStep 8596687 = 12895031) B12895031
theorem B8596705 : Blo 1788095 8596705 := bstep (se 2 (by rfl) ⟨3223764, by rfl⟩ : syracuseStep 8596705 = 6447529) B6447529
theorem B41881171 : Blo 1788095 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B4026347 : Blo 1788095 4026347 := bstep (se 1 (by rfl) ⟨3019760, by rfl⟩ : syracuseStep 4026347 = 6039521) B6039521
theorem B1790043 : Blo 1788095 1790043 := bstep (se 1 (by rfl) ⟨1342532, by rfl⟩ : syracuseStep 1790043 = 2685065) B2685065
theorem B2683001 : Blo 1788095 2683001 := bstep (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) B2012251
theorem B2683049 : Blo 1788095 2683049 := bstep (se 2 (by rfl) ⟨1006143, by rfl⟩ : syracuseStep 2683049 = 2012287) B2012287
theorem B6795677 : Blo 1788095 6795677 := bstep (se 3 (by rfl) ⟨1274189, by rfl⟩ : syracuseStep 6795677 = 2548379) B2548379
theorem B2683295 : Blo 1788095 2683295 := bstep (se 1 (by rfl) ⟨2012471, by rfl⟩ : syracuseStep 2683295 = 4024943) B4024943
theorem B4026887 : Blo 1788095 4026887 := bstep (se 1 (by rfl) ⟨3020165, by rfl⟩ : syracuseStep 4026887 = 6040331) B6040331
theorem B3019369 : Blo 1788095 3019369 := bstep (se 2 (by rfl) ⟨1132263, by rfl⟩ : syracuseStep 3019369 = 2264527) B2264527
theorem B2683547 : Blo 1788095 2683547 := bstep (se 1 (by rfl) ⟨2012660, by rfl⟩ : syracuseStep 2683547 = 4025321) B4025321
theorem B3224219 : Blo 1788095 3224219 := bstep (se 1 (by rfl) ⟨2418164, by rfl⟩ : syracuseStep 3224219 = 4836329) B4836329
theorem B5091997 : Blo 1788095 5091997 := bstep (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) B1909499
theorem B2683703 : Blo 1788095 2683703 := bstep (se 1 (by rfl) ⟨2012777, by rfl⟩ : syracuseStep 2683703 = 4025555) B4025555
theorem B22926185 : Blo 1788095 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B3019727 : Blo 1788095 3019727 := bstep (se 1 (by rfl) ⟨2264795, by rfl⟩ : syracuseStep 3019727 = 4529591) B4529591
theorem B4527839 : Blo 1788095 4527839 := bstep (se 1 (by rfl) ⟨3395879, by rfl⟩ : syracuseStep 4527839 = 6791759) B6791759
theorem B2684699 : Blo 1788095 2684699 := bstep (se 1 (by rfl) ⟨2013524, by rfl⟩ : syracuseStep 2684699 = 4027049) B4027049
theorem B3020665 : Blo 1788095 3020665 := bstep (se 2 (by rfl) ⟨1132749, by rfl⟩ : syracuseStep 3020665 = 2265499) B2265499
theorem B77346809 : Blo 1788095 77346809 := bstep (se 2 (by rfl) ⟨29005053, by rfl⟩ : syracuseStep 77346809 = 58010107) B58010107
theorem B25778351 : Blo 1788095 25778351 := bstep (se 1 (by rfl) ⟨19333763, by rfl⟩ : syracuseStep 25778351 = 38667527) B38667527
theorem B10328417 : Blo 1788095 10328417 := bstep (se 2 (by rfl) ⟨3873156, by rfl⟩ : syracuseStep 10328417 = 7746313) B7746313
theorem B5732777 : Blo 1788095 5732777 := bstep (se 2 (by rfl) ⟨2149791, by rfl⟩ : syracuseStep 5732777 = 4299583) B4299583
theorem B6445511 : Blo 1788095 6445511 := bstep (se 1 (by rfl) ⟨4834133, by rfl⟩ : syracuseStep 6445511 = 9668267) B9668267
theorem B15284807 : Blo 1788095 15284807 := bstep (se 1 (by rfl) ⟨11463605, by rfl⟩ : syracuseStep 15284807 = 22927211) B22927211
theorem B5733175 : Blo 1788095 5733175 := bstep (se 1 (by rfl) ⟨4299881, by rfl⟩ : syracuseStep 5733175 = 8599763) B8599763
theorem B4529135 : Blo 1788095 4529135 := bstep (se 1 (by rfl) ⟨3396851, by rfl⟩ : syracuseStep 4529135 = 6793703) B6793703
theorem B21232687 : Blo 1788095 21232687 := bstep (se 1 (by rfl) ⟨15924515, by rfl⟩ : syracuseStep 21232687 = 31849031) B31849031
theorem B45874511 : Blo 1788095 45874511 := bstep (se 1 (by rfl) ⟨34405883, by rfl⟩ : syracuseStep 45874511 = 68811767) B68811767
theorem B4530451 : Blo 1788095 4530451 := bstep (se 1 (by rfl) ⟨3397838, by rfl⟩ : syracuseStep 4530451 = 6795677) B6795677
theorem B17195561 : Blo 1788095 17195561 := bstep (se 2 (by rfl) ⟨6448335, by rfl⟩ : syracuseStep 17195561 = 12896671) B12896671
theorem B7644233 : Blo 1788095 7644233 := bstep (se 2 (by rfl) ⟨2866587, by rfl⟩ : syracuseStep 7644233 = 5733175) B5733175
theorem B11462249 : Blo 1788095 11462249 := bstep (se 2 (by rfl) ⟨4298343, by rfl⟩ : syracuseStep 11462249 = 8596687) B8596687
theorem B11462273 : Blo 1788095 11462273 := bstep (se 2 (by rfl) ⟨4298352, by rfl⟩ : syracuseStep 11462273 = 8596705) B8596705
theorem B30583007 : Blo 1788095 30583007 := bstep (se 1 (by rfl) ⟨22937255, by rfl⟩ : syracuseStep 30583007 = 45874511) B45874511
theorem B1788667 : Blo 1788095 1788667 := bstep (se 1 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 1788667 = 2683001) B2683001
theorem B1788699 : Blo 1788095 1788699 := bstep (se 1 (by rfl) ⟨1341524, by rfl⟩ : syracuseStep 1788699 = 2683049) B2683049
theorem B1788863 : Blo 1788095 1788863 := bstep (se 1 (by rfl) ⟨1341647, by rfl⟩ : syracuseStep 1788863 = 2683295) B2683295
theorem B1789031 : Blo 1788095 1789031 := bstep (se 1 (by rfl) ⟨1341773, by rfl⟩ : syracuseStep 1789031 = 2683547) B2683547
theorem B21769361 : Blo 1788095 21769361 := bstep (se 2 (by rfl) ⟨8163510, by rfl⟩ : syracuseStep 21769361 = 16327021) B16327021
theorem B1789135 : Blo 1788095 1789135 := bstep (se 1 (by rfl) ⟨1341851, by rfl⟩ : syracuseStep 1789135 = 2683703) B2683703
theorem B34401509 : Blo 1788095 34401509 := bstep (se 4 (by rfl) ⟨3225141, by rfl⟩ : syracuseStep 34401509 = 6450283) B6450283
theorem B4025825 : Blo 1788095 4025825 := bstep (se 2 (by rfl) ⟨1509684, by rfl⟩ : syracuseStep 4025825 = 3019369) B3019369
theorem B2682527 : Blo 1788095 2682527 := bstep (se 1 (by rfl) ⟨2011895, by rfl⟩ : syracuseStep 2682527 = 4023791) B4023791
theorem B4026095 : Blo 1788095 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B3018559 : Blo 1788095 3018559 := bstep (se 1 (by rfl) ⟨2263919, by rfl⟩ : syracuseStep 3018559 = 4527839) B4527839
theorem B1789799 : Blo 1788095 1789799 := bstep (se 1 (by rfl) ⟨1342349, by rfl⟩ : syracuseStep 1789799 = 2684699) B2684699
theorem B51564539 : Blo 1788095 51564539 := bstep (se 1 (by rfl) ⟨38673404, by rfl⟩ : syracuseStep 51564539 = 77346809) B77346809
theorem B2683115 : Blo 1788095 2683115 := bstep (se 1 (by rfl) ⟨2012336, by rfl⟩ : syracuseStep 2683115 = 4024673) B4024673
theorem B6885611 : Blo 1788095 6885611 := bstep (se 1 (by rfl) ⟨5164208, by rfl⟩ : syracuseStep 6885611 = 10328417) B10328417
theorem B3821851 : Blo 1788095 3821851 := bstep (se 1 (by rfl) ⟨2866388, by rfl⟩ : syracuseStep 3821851 = 5732777) B5732777
theorem B4297007 : Blo 1788095 4297007 := bstep (se 1 (by rfl) ⟨3222755, by rfl⟩ : syracuseStep 4297007 = 6445511) B6445511
theorem B8597917 : Blo 1788095 8597917 := bstep (se 3 (by rfl) ⟨1612109, by rfl⟩ : syracuseStep 8597917 = 3224219) B3224219
theorem B3019423 : Blo 1788095 3019423 := bstep (se 1 (by rfl) ⟨2264567, by rfl⟩ : syracuseStep 3019423 = 4529135) B4529135
theorem B5730983 : Blo 1788095 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B55841561 : Blo 1788095 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B4027553 : Blo 1788095 4027553 := bstep (se 2 (by rfl) ⟨1510332, by rfl⟩ : syracuseStep 4027553 = 3020665) B3020665
theorem B7353553 : Blo 1788095 7353553 := bstep (se 2 (by rfl) ⟨2757582, by rfl⟩ : syracuseStep 7353553 = 5515165) B5515165
theorem B2684231 : Blo 1788095 2684231 := bstep (se 1 (by rfl) ⟨2013173, by rfl⟩ : syracuseStep 2684231 = 4026347) B4026347
theorem B2684591 : Blo 1788095 2684591 := bstep (se 1 (by rfl) ⟨2013443, by rfl⟩ : syracuseStep 2684591 = 4026887) B4026887
theorem B15284123 : Blo 1788095 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B2013151 : Blo 1788095 2013151 := bstep (se 1 (by rfl) ⟨1509863, by rfl⟩ : syracuseStep 2013151 = 3019727) B3019727
theorem B6789329 : Blo 1788095 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B58022567 : Blo 1788095 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B28310249 : Blo 1788095 28310249 := bstep (se 2 (by rfl) ⟨10616343, by rfl⟩ : syracuseStep 28310249 = 21232687) B21232687
theorem B17185567 : Blo 1788095 17185567 := bstep (se 1 (by rfl) ⟨12889175, by rfl⟩ : syracuseStep 17185567 = 25778351) B25778351
theorem B6790027 : Blo 1788095 6790027 := bstep (se 1 (by rfl) ⟨5092520, by rfl⟩ : syracuseStep 6790027 = 10185041) B10185041
theorem B13589531 : Blo 1788095 13589531 := bstep (se 1 (by rfl) ⟨10192148, by rfl⟩ : syracuseStep 13589531 = 20384297) B20384297
theorem B10189871 : Blo 1788095 10189871 := bstep (se 1 (by rfl) ⟨7642403, by rfl⟩ : syracuseStep 10189871 = 15284807) B15284807
theorem B3726575 : Blo 1788095 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B13770013 : Blo 1788095 13770013 := bstep (se 3 (by rfl) ⟨2581877, by rfl⟩ : syracuseStep 13770013 = 5163755) B5163755
theorem B13590017 : Blo 1788095 13590017 := bstep (se 2 (by rfl) ⟨5096256, by rfl⟩ : syracuseStep 13590017 = 10192513) B10192513
theorem B5095801 : Blo 1788095 5095801 := bstep (se 2 (by rfl) ⟨1910925, by rfl⟩ : syracuseStep 5095801 = 3821851) B3821851
theorem B5096155 : Blo 1788095 5096155 := bstep (se 1 (by rfl) ⟨3822116, by rfl⟩ : syracuseStep 5096155 = 7644233) B7644233
theorem B22914089 : Blo 1788095 22914089 := bstep (se 2 (by rfl) ⟨8592783, by rfl⟩ : syracuseStep 22914089 = 17185567) B17185567
theorem B9053369 : Blo 1788095 9053369 := bstep (se 2 (by rfl) ⟨3395013, by rfl⟩ : syracuseStep 9053369 = 6790027) B6790027
theorem B18360017 : Blo 1788095 18360017 := bstep (se 2 (by rfl) ⟨6885006, by rfl⟩ : syracuseStep 18360017 = 13770013) B13770013
theorem B6793247 : Blo 1788095 6793247 := bstep (se 1 (by rfl) ⟨5094935, by rfl⟩ : syracuseStep 6793247 = 10189871) B10189871
theorem B2484383 : Blo 1788095 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B4024745 : Blo 1788095 4024745 := bstep (se 2 (by rfl) ⟨1509279, by rfl⟩ : syracuseStep 4024745 = 3018559) B3018559
theorem B1788351 : Blo 1788095 1788351 := bstep (se 1 (by rfl) ⟨1341263, by rfl⟩ : syracuseStep 1788351 = 2682527) B2682527
theorem B34376359 : Blo 1788095 34376359 := bstep (se 1 (by rfl) ⟨25782269, by rfl⟩ : syracuseStep 34376359 = 51564539) B51564539
theorem B1788743 : Blo 1788095 1788743 := bstep (se 1 (by rfl) ⟨1341557, by rfl⟩ : syracuseStep 1788743 = 2683115) B2683115
theorem B4590407 : Blo 1788095 4590407 := bstep (se 1 (by rfl) ⟨3442805, by rfl⟩ : syracuseStep 4590407 = 6885611) B6885611
theorem B6040601 : Blo 1788095 6040601 := bstep (se 2 (by rfl) ⟨2265225, by rfl⟩ : syracuseStep 6040601 = 4530451) B4530451
theorem B11463707 : Blo 1788095 11463707 := bstep (se 1 (by rfl) ⟨8597780, by rfl⟩ : syracuseStep 11463707 = 17195561) B17195561
theorem B3820655 : Blo 1788095 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B37227707 : Blo 1788095 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B11463889 : Blo 1788095 11463889 := bstep (se 2 (by rfl) ⟨4298958, by rfl⟩ : syracuseStep 11463889 = 8597917) B8597917
theorem B4025897 : Blo 1788095 4025897 := bstep (se 2 (by rfl) ⟨1509711, by rfl⟩ : syracuseStep 4025897 = 3019423) B3019423
theorem B1789487 : Blo 1788095 1789487 := bstep (se 1 (by rfl) ⟨1342115, by rfl⟩ : syracuseStep 1789487 = 2684231) B2684231
theorem B1789727 : Blo 1788095 1789727 := bstep (se 1 (by rfl) ⟨1342295, by rfl⟩ : syracuseStep 1789727 = 2684591) B2684591
theorem B4526219 : Blo 1788095 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B14512907 : Blo 1788095 14512907 := bstep (se 1 (by rfl) ⟨10884680, by rfl⟩ : syracuseStep 14512907 = 21769361) B21769361
theorem B22934339 : Blo 1788095 22934339 := bstep (se 1 (by rfl) ⟨17200754, by rfl⟩ : syracuseStep 22934339 = 34401509) B34401509
theorem B2683883 : Blo 1788095 2683883 := bstep (se 1 (by rfl) ⟨2012912, by rfl⟩ : syracuseStep 2683883 = 4025825) B4025825
theorem B2684063 : Blo 1788095 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B2684201 : Blo 1788095 2684201 := bstep (se 2 (by rfl) ⟨1006575, by rfl⟩ : syracuseStep 2684201 = 2013151) B2013151
theorem B2685035 : Blo 1788095 2685035 := bstep (se 1 (by rfl) ⟨2013776, by rfl⟩ : syracuseStep 2685035 = 4027553) B4027553
theorem B11458685 : Blo 1788095 11458685 := bstep (se 3 (by rfl) ⟨2148503, by rfl⟩ : syracuseStep 11458685 = 4297007) B4297007
theorem B7641499 : Blo 1788095 7641499 := bstep (se 1 (by rfl) ⟨5731124, by rfl⟩ : syracuseStep 7641499 = 11462249) B11462249
theorem B7641515 : Blo 1788095 7641515 := bstep (se 1 (by rfl) ⟨5731136, by rfl⟩ : syracuseStep 7641515 = 11462273) B11462273
theorem B10189415 : Blo 1788095 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B20388671 : Blo 1788095 20388671 := bstep (se 1 (by rfl) ⟨15291503, by rfl⟩ : syracuseStep 20388671 = 30583007) B30583007
theorem B9804737 : Blo 1788095 9804737 := bstep (se 2 (by rfl) ⟨3676776, by rfl⟩ : syracuseStep 9804737 = 7353553) B7353553
theorem B38681711 : Blo 1788095 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B18873499 : Blo 1788095 18873499 := bstep (se 1 (by rfl) ⟨14155124, by rfl⟩ : syracuseStep 18873499 = 28310249) B28310249
theorem B9059687 : Blo 1788095 9059687 := bstep (se 1 (by rfl) ⟨6794765, by rfl⟩ : syracuseStep 9059687 = 13589531) B13589531
theorem B9060011 : Blo 1788095 9060011 := bstep (se 1 (by rfl) ⟨6795008, by rfl⟩ : syracuseStep 9060011 = 13590017) B13590017
theorem B9675271 : Blo 1788095 9675271 := bstep (se 1 (by rfl) ⟨7256453, by rfl⟩ : syracuseStep 9675271 = 14512907) B14512907
theorem B45835145 : Blo 1788095 45835145 := bstep (se 2 (by rfl) ⟨17188179, by rfl⟩ : syracuseStep 45835145 = 34376359) B34376359
theorem B12240011 : Blo 1788095 12240011 := bstep (se 1 (by rfl) ⟨9180008, by rfl⟩ : syracuseStep 12240011 = 18360017) B18360017
theorem B6792943 : Blo 1788095 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B13592447 : Blo 1788095 13592447 := bstep (se 1 (by rfl) ⟨10194335, by rfl⟩ : syracuseStep 13592447 = 20388671) B20388671
theorem B6039791 : Blo 1788095 6039791 := bstep (se 1 (by rfl) ⟨4529843, by rfl⟩ : syracuseStep 6039791 = 9059687) B9059687
theorem B6040007 : Blo 1788095 6040007 := bstep (se 1 (by rfl) ⟨4530005, by rfl⟩ : syracuseStep 6040007 = 9060011) B9060011
theorem B3017479 : Blo 1788095 3017479 := bstep (se 1 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 3017479 = 4526219) B4526219
theorem B6794401 : Blo 1788095 6794401 := bstep (se 2 (by rfl) ⟨2547900, by rfl⟩ : syracuseStep 6794401 = 5095801) B5095801
theorem B15289559 : Blo 1788095 15289559 := bstep (se 1 (by rfl) ⟨11467169, by rfl⟩ : syracuseStep 15289559 = 22934339) B22934339
theorem B1789255 : Blo 1788095 1789255 := bstep (se 1 (by rfl) ⟨1341941, by rfl⟩ : syracuseStep 1789255 = 2683883) B2683883
theorem B1789375 : Blo 1788095 1789375 := bstep (se 1 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 1789375 = 2684063) B2684063
theorem B1789467 : Blo 1788095 1789467 := bstep (se 1 (by rfl) ⟨1342100, by rfl⟩ : syracuseStep 1789467 = 2684201) B2684201
theorem B6794873 : Blo 1788095 6794873 := bstep (se 2 (by rfl) ⟨2548077, by rfl⟩ : syracuseStep 6794873 = 5096155) B5096155
theorem B1790023 : Blo 1788095 1790023 := bstep (se 1 (by rfl) ⟨1342517, by rfl⟩ : syracuseStep 1790023 = 2685035) B2685035
theorem B7639123 : Blo 1788095 7639123 := bstep (se 1 (by rfl) ⟨5729342, by rfl⟩ : syracuseStep 7639123 = 11458685) B11458685
theorem B2683163 : Blo 1788095 2683163 := bstep (se 1 (by rfl) ⟨2012372, by rfl⟩ : syracuseStep 2683163 = 4024745) B4024745
theorem B3060271 : Blo 1788095 3060271 := bstep (se 1 (by rfl) ⟨2295203, by rfl⟩ : syracuseStep 3060271 = 4590407) B4590407
theorem B4027067 : Blo 1788095 4027067 := bstep (se 1 (by rfl) ⟨3020300, by rfl⟩ : syracuseStep 4027067 = 6040601) B6040601
theorem B24818471 : Blo 1788095 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B2683931 : Blo 1788095 2683931 := bstep (se 1 (by rfl) ⟨2012948, by rfl⟩ : syracuseStep 2683931 = 4025897) B4025897
theorem B26145965 : Blo 1788095 26145965 := bstep (se 3 (by rfl) ⟨4902368, by rfl⟩ : syracuseStep 26145965 = 9804737) B9804737
theorem B30569885 : Blo 1788095 30569885 := bstep (se 3 (by rfl) ⟨5731853, by rfl⟩ : syracuseStep 30569885 = 11463707) B11463707
theorem B10188413 : Blo 1788095 10188413 := bstep (se 3 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 10188413 = 3820655) B3820655
theorem B10188665 : Blo 1788095 10188665 := bstep (se 2 (by rfl) ⟨3820749, by rfl⟩ : syracuseStep 10188665 = 7641499) B7641499
theorem B15276059 : Blo 1788095 15276059 := bstep (se 1 (by rfl) ⟨11457044, by rfl⟩ : syracuseStep 15276059 = 22914089) B22914089
theorem B6035579 : Blo 1788095 6035579 := bstep (se 1 (by rfl) ⟨4526684, by rfl⟩ : syracuseStep 6035579 = 9053369) B9053369
theorem B4528831 : Blo 1788095 4528831 := bstep (se 1 (by rfl) ⟨3396623, by rfl⟩ : syracuseStep 4528831 = 6793247) B6793247
theorem B25164665 : Blo 1788095 25164665 := bstep (se 2 (by rfl) ⟨9436749, by rfl⟩ : syracuseStep 25164665 = 18873499) B18873499
theorem B15285185 : Blo 1788095 15285185 := bstep (se 2 (by rfl) ⟨5731944, by rfl⟩ : syracuseStep 15285185 = 11463889) B11463889
theorem B5094343 : Blo 1788095 5094343 := bstep (se 1 (by rfl) ⟨3820757, by rfl⟩ : syracuseStep 5094343 = 7641515) B7641515
theorem B26500085 : Blo 1788095 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B25787807 : Blo 1788095 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B51601445 : Blo 1788095 51601445 := bstep (se 4 (by rfl) ⟨4837635, by rfl⟩ : syracuseStep 51601445 = 9675271) B9675271
theorem B30556763 : Blo 1788095 30556763 := bstep (se 1 (by rfl) ⟨22917572, by rfl⟩ : syracuseStep 30556763 = 45835145) B45835145
theorem B6038441 : Blo 1788095 6038441 := bstep (se 2 (by rfl) ⟨2264415, by rfl⟩ : syracuseStep 6038441 = 4528831) B4528831
theorem B4023305 : Blo 1788095 4023305 := bstep (se 2 (by rfl) ⟨1508739, by rfl⟩ : syracuseStep 4023305 = 3017479) B3017479
theorem B6792275 : Blo 1788095 6792275 := bstep (se 1 (by rfl) ⟨5094206, by rfl⟩ : syracuseStep 6792275 = 10188413) B10188413
theorem B6792443 : Blo 1788095 6792443 := bstep (se 1 (by rfl) ⟨5094332, by rfl⟩ : syracuseStep 6792443 = 10188665) B10188665
theorem B9061631 : Blo 1788095 9061631 := bstep (se 1 (by rfl) ⟨6796223, by rfl⟩ : syracuseStep 9061631 = 13592447) B13592447
theorem B6792457 : Blo 1788095 6792457 := bstep (se 2 (by rfl) ⟨2547171, by rfl⟩ : syracuseStep 6792457 = 5094343) B5094343
theorem B10184039 : Blo 1788095 10184039 := bstep (se 1 (by rfl) ⟨7638029, by rfl⟩ : syracuseStep 10184039 = 15276059) B15276059
theorem B4023719 : Blo 1788095 4023719 := bstep (se 1 (by rfl) ⟨3017789, by rfl⟩ : syracuseStep 4023719 = 6035579) B6035579
theorem B10193039 : Blo 1788095 10193039 := bstep (se 1 (by rfl) ⟨7644779, by rfl⟩ : syracuseStep 10193039 = 15289559) B15289559
theorem B10185497 : Blo 1788095 10185497 := bstep (se 2 (by rfl) ⟨3819561, by rfl⟩ : syracuseStep 10185497 = 7639123) B7639123
theorem B1788775 : Blo 1788095 1788775 := bstep (se 1 (by rfl) ⟨1341581, by rfl⟩ : syracuseStep 1788775 = 2683163) B2683163
theorem B16321445 : Blo 1788095 16321445 := bstep (se 4 (by rfl) ⟨1530135, by rfl⟩ : syracuseStep 16321445 = 3060271) B3060271
theorem B32640029 : Blo 1788095 32640029 := bstep (se 3 (by rfl) ⟨6120005, by rfl⟩ : syracuseStep 32640029 = 12240011) B12240011
theorem B1789287 : Blo 1788095 1789287 := bstep (se 1 (by rfl) ⟨1341965, by rfl⟩ : syracuseStep 1789287 = 2683931) B2683931
theorem B4026527 : Blo 1788095 4026527 := bstep (se 1 (by rfl) ⟨3019895, by rfl⟩ : syracuseStep 4026527 = 6039791) B6039791
theorem B4026671 : Blo 1788095 4026671 := bstep (se 1 (by rfl) ⟨3020003, by rfl⟩ : syracuseStep 4026671 = 6040007) B6040007
theorem B17666723 : Blo 1788095 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B17191871 : Blo 1788095 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B9057257 : Blo 1788095 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B2684711 : Blo 1788095 2684711 := bstep (se 1 (by rfl) ⟨2013533, by rfl⟩ : syracuseStep 2684711 = 4027067) B4027067
theorem B16545647 : Blo 1788095 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B17430643 : Blo 1788095 17430643 := bstep (se 1 (by rfl) ⟨13072982, by rfl⟩ : syracuseStep 17430643 = 26145965) B26145965
theorem B20379923 : Blo 1788095 20379923 := bstep (se 1 (by rfl) ⟨15284942, by rfl⟩ : syracuseStep 20379923 = 30569885) B30569885
theorem B9059201 : Blo 1788095 9059201 := bstep (se 2 (by rfl) ⟨3397200, by rfl⟩ : syracuseStep 9059201 = 6794401) B6794401
theorem B16776443 : Blo 1788095 16776443 := bstep (se 1 (by rfl) ⟨12582332, by rfl⟩ : syracuseStep 16776443 = 25164665) B25164665
theorem B10190123 : Blo 1788095 10190123 := bstep (se 1 (by rfl) ⟨7642592, by rfl⟩ : syracuseStep 10190123 = 15285185) B15285185
theorem B4529915 : Blo 1788095 4529915 := bstep (se 1 (by rfl) ⟨3397436, by rfl⟩ : syracuseStep 4529915 = 6794873) B6794873
theorem B23240857 : Blo 1788095 23240857 := bstep (se 2 (by rfl) ⟨8715321, by rfl⟩ : syracuseStep 23240857 = 17430643) B17430643
theorem B11461247 : Blo 1788095 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B6038171 : Blo 1788095 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B44737181 : Blo 1788095 44737181 := bstep (se 3 (by rfl) ⟨8388221, by rfl⟩ : syracuseStep 44737181 = 16776443) B16776443
theorem B6039467 : Blo 1788095 6039467 := bstep (se 1 (by rfl) ⟨4529600, by rfl⟩ : syracuseStep 6039467 = 9059201) B9059201
theorem B10880963 : Blo 1788095 10880963 := bstep (se 1 (by rfl) ⟨8160722, by rfl⟩ : syracuseStep 10880963 = 16321445) B16321445
theorem B21760019 : Blo 1788095 21760019 := bstep (se 1 (by rfl) ⟨16320014, by rfl⟩ : syracuseStep 21760019 = 32640029) B32640029
theorem B6793415 : Blo 1788095 6793415 := bstep (se 1 (by rfl) ⟨5095061, by rfl⟩ : syracuseStep 6793415 = 10190123) B10190123
theorem B34400963 : Blo 1788095 34400963 := bstep (se 1 (by rfl) ⟨25800722, by rfl⟩ : syracuseStep 34400963 = 51601445) B51601445
theorem B4025627 : Blo 1788095 4025627 := bstep (se 1 (by rfl) ⟨3019220, by rfl⟩ : syracuseStep 4025627 = 6038441) B6038441
theorem B2682203 : Blo 1788095 2682203 := bstep (se 1 (by rfl) ⟨2011652, by rfl⟩ : syracuseStep 2682203 = 4023305) B4023305
theorem B6041087 : Blo 1788095 6041087 := bstep (se 1 (by rfl) ⟨4530815, by rfl⟩ : syracuseStep 6041087 = 9061631) B9061631
theorem B2682479 : Blo 1788095 2682479 := bstep (se 1 (by rfl) ⟨2011859, by rfl⟩ : syracuseStep 2682479 = 4023719) B4023719
theorem B1789807 : Blo 1788095 1789807 := bstep (se 1 (by rfl) ⟨1342355, by rfl⟩ : syracuseStep 1789807 = 2684711) B2684711
theorem B11030431 : Blo 1788095 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B6795359 : Blo 1788095 6795359 := bstep (se 1 (by rfl) ⟨5096519, by rfl⟩ : syracuseStep 6795359 = 10193039) B10193039
theorem B13586615 : Blo 1788095 13586615 := bstep (se 1 (by rfl) ⟨10189961, by rfl⟩ : syracuseStep 13586615 = 20379923) B20379923
theorem B9056609 : Blo 1788095 9056609 := bstep (se 2 (by rfl) ⟨3396228, by rfl⟩ : syracuseStep 9056609 = 6792457) B6792457
theorem B3019943 : Blo 1788095 3019943 := bstep (se 1 (by rfl) ⟨2264957, by rfl⟩ : syracuseStep 3019943 = 4529915) B4529915
theorem B2684351 : Blo 1788095 2684351 := bstep (se 1 (by rfl) ⟨2013263, by rfl⟩ : syracuseStep 2684351 = 4026527) B4026527
theorem B2684447 : Blo 1788095 2684447 := bstep (se 1 (by rfl) ⟨2013335, by rfl⟩ : syracuseStep 2684447 = 4026671) B4026671
theorem B20371175 : Blo 1788095 20371175 := bstep (se 1 (by rfl) ⟨15278381, by rfl⟩ : syracuseStep 20371175 = 30556763) B30556763
theorem B11777815 : Blo 1788095 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B4528183 : Blo 1788095 4528183 := bstep (se 1 (by rfl) ⟨3396137, by rfl⟩ : syracuseStep 4528183 = 6792275) B6792275
theorem B4528295 : Blo 1788095 4528295 := bstep (se 1 (by rfl) ⟨3396221, by rfl⟩ : syracuseStep 4528295 = 6792443) B6792443
theorem B6789359 : Blo 1788095 6789359 := bstep (se 1 (by rfl) ⟨5092019, by rfl⟩ : syracuseStep 6789359 = 10184039) B10184039
theorem B6790331 : Blo 1788095 6790331 := bstep (se 1 (by rfl) ⟨5092748, by rfl⟩ : syracuseStep 6790331 = 10185497) B10185497
theorem B4530239 : Blo 1788095 4530239 := bstep (se 1 (by rfl) ⟨3397679, by rfl⟩ : syracuseStep 4530239 = 6795359) B6795359
theorem B6037577 : Blo 1788095 6037577 := bstep (se 2 (by rfl) ⟨2264091, by rfl⟩ : syracuseStep 6037577 = 4528183) B4528183
theorem B6037739 : Blo 1788095 6037739 := bstep (se 1 (by rfl) ⟨4528304, by rfl⟩ : syracuseStep 6037739 = 9056609) B9056609
theorem B1788135 : Blo 1788095 1788135 := bstep (se 1 (by rfl) ⟨1341101, by rfl⟩ : syracuseStep 1788135 = 2682203) B2682203
theorem B1788319 : Blo 1788095 1788319 := bstep (se 1 (by rfl) ⟨1341239, by rfl⟩ : syracuseStep 1788319 = 2682479) B2682479
theorem B14707241 : Blo 1788095 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B4025447 : Blo 1788095 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B1789567 : Blo 1788095 1789567 := bstep (se 1 (by rfl) ⟨1342175, by rfl⟩ : syracuseStep 1789567 = 2684351) B2684351
theorem B1789631 : Blo 1788095 1789631 := bstep (se 1 (by rfl) ⟨1342223, by rfl⟩ : syracuseStep 1789631 = 2684447) B2684447
theorem B4026311 : Blo 1788095 4026311 := bstep (se 1 (by rfl) ⟨3019733, by rfl⟩ : syracuseStep 4026311 = 6039467) B6039467
theorem B7253975 : Blo 1788095 7253975 := bstep (se 1 (by rfl) ⟨5440481, by rfl⟩ : syracuseStep 7253975 = 10880963) B10880963
theorem B3018863 : Blo 1788095 3018863 := bstep (se 1 (by rfl) ⟨2264147, by rfl⟩ : syracuseStep 3018863 = 4528295) B4528295
theorem B4526239 : Blo 1788095 4526239 := bstep (se 1 (by rfl) ⟨3394679, by rfl⟩ : syracuseStep 4526239 = 6789359) B6789359
theorem B22933975 : Blo 1788095 22933975 := bstep (se 1 (by rfl) ⟨17200481, by rfl⟩ : syracuseStep 22933975 = 34400963) B34400963
theorem B4526887 : Blo 1788095 4526887 := bstep (se 1 (by rfl) ⟨3395165, by rfl⟩ : syracuseStep 4526887 = 6790331) B6790331
theorem B2683751 : Blo 1788095 2683751 := bstep (se 1 (by rfl) ⟨2012813, by rfl⟩ : syracuseStep 2683751 = 4025627) B4025627
theorem B4027391 : Blo 1788095 4027391 := bstep (se 1 (by rfl) ⟨3020543, by rfl⟩ : syracuseStep 4027391 = 6041087) B6041087
theorem B9057743 : Blo 1788095 9057743 := bstep (se 1 (by rfl) ⟨6793307, by rfl⟩ : syracuseStep 9057743 = 13586615) B13586615
theorem B30987809 : Blo 1788095 30987809 := bstep (se 2 (by rfl) ⟨11620428, by rfl⟩ : syracuseStep 30987809 = 23240857) B23240857
theorem B7640831 : Blo 1788095 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B29824787 : Blo 1788095 29824787 := bstep (se 1 (by rfl) ⟨22368590, by rfl⟩ : syracuseStep 29824787 = 44737181) B44737181
theorem B2013295 : Blo 1788095 2013295 := bstep (se 1 (by rfl) ⟨1509971, by rfl⟩ : syracuseStep 2013295 = 3019943) B3019943
theorem B13580783 : Blo 1788095 13580783 := bstep (se 1 (by rfl) ⟨10185587, by rfl⟩ : syracuseStep 13580783 = 20371175) B20371175
theorem B14506679 : Blo 1788095 14506679 := bstep (se 1 (by rfl) ⟨10880009, by rfl⟩ : syracuseStep 14506679 = 21760019) B21760019
theorem B4528943 : Blo 1788095 4528943 := bstep (se 1 (by rfl) ⟨3396707, by rfl⟩ : syracuseStep 4528943 = 6793415) B6793415
theorem B15703753 : Blo 1788095 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B6038495 : Blo 1788095 6038495 := bstep (se 1 (by rfl) ⟨4528871, by rfl⟩ : syracuseStep 6038495 = 9057743) B9057743
theorem B19883191 : Blo 1788095 19883191 := bstep (se 1 (by rfl) ⟨14912393, by rfl⟩ : syracuseStep 19883191 = 29824787) B29824787
theorem B9053855 : Blo 1788095 9053855 := bstep (se 1 (by rfl) ⟨6790391, by rfl⟩ : syracuseStep 9053855 = 13580783) B13580783
theorem B20375549 : Blo 1788095 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B19343933 : Blo 1788095 19343933 := bstep (se 3 (by rfl) ⟨3626987, by rfl⟩ : syracuseStep 19343933 = 7253975) B7253975
theorem B4025051 : Blo 1788095 4025051 := bstep (se 1 (by rfl) ⟨3018788, by rfl⟩ : syracuseStep 4025051 = 6037577) B6037577
theorem B4025159 : Blo 1788095 4025159 := bstep (se 1 (by rfl) ⟨3018869, by rfl⟩ : syracuseStep 4025159 = 6037739) B6037739
theorem B1789167 : Blo 1788095 1789167 := bstep (se 1 (by rfl) ⟨1341875, by rfl⟩ : syracuseStep 1789167 = 2683751) B2683751
theorem B9671119 : Blo 1788095 9671119 := bstep (se 1 (by rfl) ⟨7253339, by rfl⟩ : syracuseStep 9671119 = 14506679) B14506679
theorem B3019295 : Blo 1788095 3019295 := bstep (se 1 (by rfl) ⟨2264471, by rfl⟩ : syracuseStep 3019295 = 4528943) B4528943
theorem B2683631 : Blo 1788095 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B2684207 : Blo 1788095 2684207 := bstep (se 1 (by rfl) ⟨2013155, by rfl⟩ : syracuseStep 2684207 = 4026311) B4026311
theorem B3020159 : Blo 1788095 3020159 := bstep (se 1 (by rfl) ⟨2265119, by rfl⟩ : syracuseStep 3020159 = 4530239) B4530239
theorem B2012575 : Blo 1788095 2012575 := bstep (se 1 (by rfl) ⟨1509431, by rfl⟩ : syracuseStep 2012575 = 3018863) B3018863
theorem B2684393 : Blo 1788095 2684393 := bstep (se 2 (by rfl) ⟨1006647, by rfl⟩ : syracuseStep 2684393 = 2013295) B2013295
theorem B6034985 : Blo 1788095 6034985 := bstep (se 2 (by rfl) ⟨2263119, by rfl⟩ : syracuseStep 6034985 = 4526239) B4526239
theorem B30578633 : Blo 1788095 30578633 := bstep (se 2 (by rfl) ⟨11466987, by rfl⟩ : syracuseStep 30578633 = 22933975) B22933975
theorem B2684927 : Blo 1788095 2684927 := bstep (se 1 (by rfl) ⟨2013695, by rfl⟩ : syracuseStep 2684927 = 4027391) B4027391
theorem B20658539 : Blo 1788095 20658539 := bstep (se 1 (by rfl) ⟨15493904, by rfl⟩ : syracuseStep 20658539 = 30987809) B30987809
theorem B6035849 : Blo 1788095 6035849 := bstep (se 2 (by rfl) ⟨2263443, by rfl⟩ : syracuseStep 6035849 = 4526887) B4526887
theorem B9804827 : Blo 1788095 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B20938337 : Blo 1788095 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B4023323 : Blo 1788095 4023323 := bstep (se 1 (by rfl) ⟨3017492, by rfl⟩ : syracuseStep 4023323 = 6034985) B6034985
theorem B13583699 : Blo 1788095 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B13772359 : Blo 1788095 13772359 := bstep (se 1 (by rfl) ⟨10329269, by rfl⟩ : syracuseStep 13772359 = 20658539) B20658539
theorem B26510921 : Blo 1788095 26510921 := bstep (se 2 (by rfl) ⟨9941595, by rfl⟩ : syracuseStep 26510921 = 19883191) B19883191
theorem B4023899 : Blo 1788095 4023899 := bstep (se 1 (by rfl) ⟨3017924, by rfl⟩ : syracuseStep 4023899 = 6035849) B6035849
theorem B12895955 : Blo 1788095 12895955 := bstep (se 1 (by rfl) ⟨9671966, by rfl⟩ : syracuseStep 12895955 = 19343933) B19343933
theorem B51579301 : Blo 1788095 51579301 := bstep (se 4 (by rfl) ⟨4835559, by rfl⟩ : syracuseStep 51579301 = 9671119) B9671119
theorem B1789087 : Blo 1788095 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B4025663 : Blo 1788095 4025663 := bstep (se 1 (by rfl) ⟨3019247, by rfl⟩ : syracuseStep 4025663 = 6038495) B6038495
theorem B1789471 : Blo 1788095 1789471 := bstep (se 1 (by rfl) ⟨1342103, by rfl⟩ : syracuseStep 1789471 = 2684207) B2684207
theorem B1789595 : Blo 1788095 1789595 := bstep (se 1 (by rfl) ⟨1342196, by rfl⟩ : syracuseStep 1789595 = 2684393) B2684393
theorem B20385755 : Blo 1788095 20385755 := bstep (se 1 (by rfl) ⟨15289316, by rfl⟩ : syracuseStep 20385755 = 30578633) B30578633
theorem B1789951 : Blo 1788095 1789951 := bstep (se 1 (by rfl) ⟨1342463, by rfl⟩ : syracuseStep 1789951 = 2684927) B2684927
theorem B2683367 : Blo 1788095 2683367 := bstep (se 1 (by rfl) ⟨2012525, by rfl⟩ : syracuseStep 2683367 = 4025051) B4025051
theorem B2683433 : Blo 1788095 2683433 := bstep (se 2 (by rfl) ⟨1006287, by rfl⟩ : syracuseStep 2683433 = 2012575) B2012575
theorem B2683439 : Blo 1788095 2683439 := bstep (se 1 (by rfl) ⟨2012579, by rfl⟩ : syracuseStep 2683439 = 4025159) B4025159
theorem B2012863 : Blo 1788095 2012863 := bstep (se 1 (by rfl) ⟨1509647, by rfl⟩ : syracuseStep 2012863 = 3019295) B3019295
theorem B2013439 : Blo 1788095 2013439 := bstep (se 1 (by rfl) ⟨1510079, by rfl⟩ : syracuseStep 2013439 = 3020159) B3020159
theorem B6035903 : Blo 1788095 6035903 := bstep (se 1 (by rfl) ⟨4526927, by rfl⟩ : syracuseStep 6035903 = 9053855) B9053855
theorem B6536551 : Blo 1788095 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B13958891 : Blo 1788095 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B68772401 : Blo 1788095 68772401 := bstep (se 2 (by rfl) ⟨25789650, by rfl⟩ : syracuseStep 68772401 = 51579301) B51579301
theorem B4023935 : Blo 1788095 4023935 := bstep (se 1 (by rfl) ⟨3017951, by rfl⟩ : syracuseStep 4023935 = 6035903) B6035903
theorem B1788911 : Blo 1788095 1788911 := bstep (se 1 (by rfl) ⟨1341683, by rfl⟩ : syracuseStep 1788911 = 2683367) B2683367
theorem B1788955 : Blo 1788095 1788955 := bstep (se 1 (by rfl) ⟨1341716, by rfl⟩ : syracuseStep 1788955 = 2683433) B2683433
theorem B1788959 : Blo 1788095 1788959 := bstep (se 1 (by rfl) ⟨1341719, by rfl⟩ : syracuseStep 1788959 = 2683439) B2683439
theorem B73452581 : Blo 1788095 73452581 := bstep (se 4 (by rfl) ⟨6886179, by rfl⟩ : syracuseStep 73452581 = 13772359) B13772359
theorem B2682215 : Blo 1788095 2682215 := bstep (se 1 (by rfl) ⟨2011661, by rfl⟩ : syracuseStep 2682215 = 4023323) B4023323
theorem B9055799 : Blo 1788095 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B17673947 : Blo 1788095 17673947 := bstep (se 1 (by rfl) ⟨13255460, by rfl⟩ : syracuseStep 17673947 = 26510921) B26510921
theorem B2682599 : Blo 1788095 2682599 := bstep (se 1 (by rfl) ⟨2011949, by rfl⟩ : syracuseStep 2682599 = 4023899) B4023899
theorem B8597303 : Blo 1788095 8597303 := bstep (se 1 (by rfl) ⟨6447977, by rfl⟩ : syracuseStep 8597303 = 12895955) B12895955
theorem B2683775 : Blo 1788095 2683775 := bstep (se 1 (by rfl) ⟨2012831, by rfl⟩ : syracuseStep 2683775 = 4025663) B4025663
theorem B2683817 : Blo 1788095 2683817 := bstep (se 2 (by rfl) ⟨1006431, by rfl⟩ : syracuseStep 2683817 = 2012863) B2012863
theorem B2684585 : Blo 1788095 2684585 := bstep (se 2 (by rfl) ⟨1006719, by rfl⟩ : syracuseStep 2684585 = 2013439) B2013439
theorem B8715401 : Blo 1788095 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B9305927 : Blo 1788095 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B13590503 : Blo 1788095 13590503 := bstep (se 1 (by rfl) ⟨10192877, by rfl⟩ : syracuseStep 13590503 = 20385755) B20385755
theorem B5810267 : Blo 1788095 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B1788143 : Blo 1788095 1788143 := bstep (se 1 (by rfl) ⟨1341107, by rfl⟩ : syracuseStep 1788143 = 2682215) B2682215
theorem B11782631 : Blo 1788095 11782631 := bstep (se 1 (by rfl) ⟨8836973, by rfl⟩ : syracuseStep 11782631 = 17673947) B17673947
theorem B1788399 : Blo 1788095 1788399 := bstep (se 1 (by rfl) ⟨1341299, by rfl⟩ : syracuseStep 1788399 = 2682599) B2682599
theorem B6203951 : Blo 1788095 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B1789183 : Blo 1788095 1789183 := bstep (se 1 (by rfl) ⟨1341887, by rfl⟩ : syracuseStep 1789183 = 2683775) B2683775
theorem B1789211 : Blo 1788095 1789211 := bstep (se 1 (by rfl) ⟨1341908, by rfl⟩ : syracuseStep 1789211 = 2683817) B2683817
theorem B2682623 : Blo 1788095 2682623 := bstep (se 1 (by rfl) ⟨2011967, by rfl⟩ : syracuseStep 2682623 = 4023935) B4023935
theorem B1789723 : Blo 1788095 1789723 := bstep (se 1 (by rfl) ⟨1342292, by rfl⟩ : syracuseStep 1789723 = 2684585) B2684585
theorem B48968387 : Blo 1788095 48968387 := bstep (se 1 (by rfl) ⟨36726290, by rfl⟩ : syracuseStep 48968387 = 73452581) B73452581
theorem B5731535 : Blo 1788095 5731535 := bstep (se 1 (by rfl) ⟨4298651, by rfl⟩ : syracuseStep 5731535 = 8597303) B8597303
theorem B45848267 : Blo 1788095 45848267 := bstep (se 1 (by rfl) ⟨34386200, by rfl⟩ : syracuseStep 45848267 = 68772401) B68772401
theorem B6037199 : Blo 1788095 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B9060335 : Blo 1788095 9060335 := bstep (se 1 (by rfl) ⟨6795251, by rfl⟩ : syracuseStep 9060335 = 13590503) B13590503
theorem B32645591 : Blo 1788095 32645591 := bstep (se 1 (by rfl) ⟨24484193, by rfl⟩ : syracuseStep 32645591 = 48968387) B48968387
theorem B30565511 : Blo 1788095 30565511 := bstep (se 1 (by rfl) ⟨22924133, by rfl⟩ : syracuseStep 30565511 = 45848267) B45848267
theorem B4024799 : Blo 1788095 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B1788415 : Blo 1788095 1788415 := bstep (se 1 (by rfl) ⟨1341311, by rfl⟩ : syracuseStep 1788415 = 2682623) B2682623
theorem B6040223 : Blo 1788095 6040223 := bstep (se 1 (by rfl) ⟨4530167, by rfl⟩ : syracuseStep 6040223 = 9060335) B9060335
theorem B3821023 : Blo 1788095 3821023 := bstep (se 1 (by rfl) ⟨2865767, by rfl⟩ : syracuseStep 3821023 = 5731535) B5731535
theorem B3873511 : Blo 1788095 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B7855087 : Blo 1788095 7855087 := bstep (se 1 (by rfl) ⟨5891315, by rfl⟩ : syracuseStep 7855087 = 11782631) B11782631
theorem B4135967 : Blo 1788095 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B20377007 : Blo 1788095 20377007 := bstep (se 1 (by rfl) ⟨15282755, by rfl⟩ : syracuseStep 20377007 = 30565511) B30565511
theorem B5164681 : Blo 1788095 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B10473449 : Blo 1788095 10473449 := bstep (se 2 (by rfl) ⟨3927543, by rfl⟩ : syracuseStep 10473449 = 7855087) B7855087
theorem B2683199 : Blo 1788095 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B4026815 : Blo 1788095 4026815 := bstep (se 1 (by rfl) ⟨3020111, by rfl⟩ : syracuseStep 4026815 = 6040223) B6040223
theorem B2757311 : Blo 1788095 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B21763727 : Blo 1788095 21763727 := bstep (se 1 (by rfl) ⟨16322795, by rfl⟩ : syracuseStep 21763727 = 32645591) B32645591
theorem B5094697 : Blo 1788095 5094697 := bstep (se 2 (by rfl) ⟨1910511, by rfl⟩ : syracuseStep 5094697 = 3821023) B3821023
theorem B14509151 : Blo 1788095 14509151 := bstep (se 1 (by rfl) ⟨10881863, by rfl⟩ : syracuseStep 14509151 = 21763727) B21763727
theorem B6792929 : Blo 1788095 6792929 := bstep (se 2 (by rfl) ⟨2547348, by rfl⟩ : syracuseStep 6792929 = 5094697) B5094697
theorem B13584671 : Blo 1788095 13584671 := bstep (se 1 (by rfl) ⟨10188503, by rfl⟩ : syracuseStep 13584671 = 20377007) B20377007
theorem B27929197 : Blo 1788095 27929197 := bstep (se 3 (by rfl) ⟨5236724, by rfl⟩ : syracuseStep 27929197 = 10473449) B10473449
theorem B1788799 : Blo 1788095 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B1838207 : Blo 1788095 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B6886241 : Blo 1788095 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B2684543 : Blo 1788095 2684543 := bstep (se 1 (by rfl) ⟨2013407, by rfl⟩ : syracuseStep 2684543 = 4026815) B4026815
theorem B4901885 : Blo 1788095 4901885 := bstep (se 3 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 4901885 = 1838207) B1838207
theorem B4590827 : Blo 1788095 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B1789695 : Blo 1788095 1789695 := bstep (se 1 (by rfl) ⟨1342271, by rfl⟩ : syracuseStep 1789695 = 2684543) B2684543
theorem B9056447 : Blo 1788095 9056447 := bstep (se 1 (by rfl) ⟨6792335, by rfl⟩ : syracuseStep 9056447 = 13584671) B13584671
theorem B9672767 : Blo 1788095 9672767 := bstep (se 1 (by rfl) ⟨7254575, by rfl⟩ : syracuseStep 9672767 = 14509151) B14509151
theorem B37238929 : Blo 1788095 37238929 := bstep (se 2 (by rfl) ⟨13964598, by rfl⟩ : syracuseStep 37238929 = 27929197) B27929197
theorem B4528619 : Blo 1788095 4528619 := bstep (se 1 (by rfl) ⟨3396464, by rfl⟩ : syracuseStep 4528619 = 6792929) B6792929
theorem B6037631 : Blo 1788095 6037631 := bstep (se 1 (by rfl) ⟨4528223, by rfl⟩ : syracuseStep 6037631 = 9056447) B9056447
theorem B198607621 : Blo 1788095 198607621 := bstep (se 4 (by rfl) ⟨18619464, by rfl⟩ : syracuseStep 198607621 = 37238929) B37238929
theorem B6448511 : Blo 1788095 6448511 := bstep (se 1 (by rfl) ⟨4836383, by rfl⟩ : syracuseStep 6448511 = 9672767) B9672767
theorem B3019079 : Blo 1788095 3019079 := bstep (se 1 (by rfl) ⟨2264309, by rfl⟩ : syracuseStep 3019079 = 4528619) B4528619
theorem B3060551 : Blo 1788095 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B3267923 : Blo 1788095 3267923 := bstep (se 1 (by rfl) ⟨2450942, by rfl⟩ : syracuseStep 3267923 = 4901885) B4901885
theorem B8161469 : Blo 1788095 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B4025087 : Blo 1788095 4025087 := bstep (se 1 (by rfl) ⟨3018815, by rfl⟩ : syracuseStep 4025087 = 6037631) B6037631
theorem B264810161 : Blo 1788095 264810161 := bstep (se 2 (by rfl) ⟨99303810, by rfl⟩ : syracuseStep 264810161 = 198607621) B198607621
theorem B2012719 : Blo 1788095 2012719 := bstep (se 1 (by rfl) ⟨1509539, by rfl⟩ : syracuseStep 2012719 = 3019079) B3019079
theorem B8714461 : Blo 1788095 8714461 := bstep (se 3 (by rfl) ⟨1633961, by rfl⟩ : syracuseStep 8714461 = 3267923) B3267923
theorem B4299007 : Blo 1788095 4299007 := bstep (se 1 (by rfl) ⟨3224255, by rfl⟩ : syracuseStep 4299007 = 6448511) B6448511
theorem B5440979 : Blo 1788095 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B706160429 : Blo 1788095 706160429 := bstep (se 3 (by rfl) ⟨132405080, by rfl⟩ : syracuseStep 706160429 = 264810161) B264810161
theorem B11619281 : Blo 1788095 11619281 := bstep (se 2 (by rfl) ⟨4357230, by rfl⟩ : syracuseStep 11619281 = 8714461) B8714461
theorem B2683391 : Blo 1788095 2683391 := bstep (se 1 (by rfl) ⟨2012543, by rfl⟩ : syracuseStep 2683391 = 4025087) B4025087
theorem B2683625 : Blo 1788095 2683625 := bstep (se 2 (by rfl) ⟨1006359, by rfl⟩ : syracuseStep 2683625 = 2012719) B2012719
theorem B5732009 : Blo 1788095 5732009 := bstep (se 2 (by rfl) ⟨2149503, by rfl⟩ : syracuseStep 5732009 = 4299007) B4299007
theorem B14509277 : Blo 1788095 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B1788927 : Blo 1788095 1788927 := bstep (se 1 (by rfl) ⟨1341695, by rfl⟩ : syracuseStep 1788927 = 2683391) B2683391
theorem B1789083 : Blo 1788095 1789083 := bstep (se 1 (by rfl) ⟨1341812, by rfl⟩ : syracuseStep 1789083 = 2683625) B2683625
theorem B3821339 : Blo 1788095 3821339 := bstep (se 1 (by rfl) ⟨2866004, by rfl⟩ : syracuseStep 3821339 = 5732009) B5732009
theorem B470773619 : Blo 1788095 470773619 := bstep (se 1 (by rfl) ⟨353080214, by rfl⟩ : syracuseStep 470773619 = 706160429) B706160429
theorem B7746187 : Blo 1788095 7746187 := bstep (se 1 (by rfl) ⟨5809640, by rfl⟩ : syracuseStep 7746187 = 11619281) B11619281
theorem B313849079 : Blo 1788095 313849079 := bstep (se 1 (by rfl) ⟨235386809, by rfl⟩ : syracuseStep 313849079 = 470773619) B470773619
theorem B9672851 : Blo 1788095 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B10328249 : Blo 1788095 10328249 := bstep (se 2 (by rfl) ⟨3873093, by rfl⟩ : syracuseStep 10328249 = 7746187) B7746187
theorem B2547559 : Blo 1788095 2547559 := bstep (se 1 (by rfl) ⟨1910669, by rfl⟩ : syracuseStep 2547559 = 3821339) B3821339
theorem B27541997 : Blo 1788095 27541997 := bstep (se 3 (by rfl) ⟨5164124, by rfl⟩ : syracuseStep 27541997 = 10328249) B10328249
theorem B209232719 : Blo 1788095 209232719 := bstep (se 1 (by rfl) ⟨156924539, by rfl⟩ : syracuseStep 209232719 = 313849079) B313849079
theorem B6448567 : Blo 1788095 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B3396745 : Blo 1788095 3396745 := bstep (se 2 (by rfl) ⟨1273779, by rfl⟩ : syracuseStep 3396745 = 2547559) B2547559
theorem B18361331 : Blo 1788095 18361331 := bstep (se 1 (by rfl) ⟨13770998, by rfl⟩ : syracuseStep 18361331 = 27541997) B27541997
theorem B139488479 : Blo 1788095 139488479 := bstep (se 1 (by rfl) ⟨104616359, by rfl⟩ : syracuseStep 139488479 = 209232719) B209232719
theorem B8598089 : Blo 1788095 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B4528993 : Blo 1788095 4528993 := bstep (se 2 (by rfl) ⟨1698372, by rfl⟩ : syracuseStep 4528993 = 3396745) B3396745
theorem B6038657 : Blo 1788095 6038657 := bstep (se 2 (by rfl) ⟨2264496, by rfl⟩ : syracuseStep 6038657 = 4528993) B4528993
theorem B12240887 : Blo 1788095 12240887 := bstep (se 1 (by rfl) ⟨9180665, by rfl⟩ : syracuseStep 12240887 = 18361331) B18361331
theorem B92992319 : Blo 1788095 92992319 := bstep (se 1 (by rfl) ⟨69744239, by rfl⟩ : syracuseStep 92992319 = 139488479) B139488479
theorem B5732059 : Blo 1788095 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B4025771 : Blo 1788095 4025771 := bstep (se 1 (by rfl) ⟨3019328, by rfl⟩ : syracuseStep 4025771 = 6038657) B6038657
theorem B32642365 : Blo 1788095 32642365 := bstep (se 3 (by rfl) ⟨6120443, by rfl⟩ : syracuseStep 32642365 = 12240887) B12240887
theorem B61994879 : Blo 1788095 61994879 := bstep (se 1 (by rfl) ⟨46496159, by rfl⟩ : syracuseStep 61994879 = 92992319) B92992319
theorem B7642745 : Blo 1788095 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B41329919 : Blo 1788095 41329919 := bstep (se 1 (by rfl) ⟨30997439, by rfl⟩ : syracuseStep 41329919 = 61994879) B61994879
theorem B2683847 : Blo 1788095 2683847 := bstep (se 1 (by rfl) ⟨2012885, by rfl⟩ : syracuseStep 2683847 = 4025771) B4025771
theorem B43523153 : Blo 1788095 43523153 := bstep (se 2 (by rfl) ⟨16321182, by rfl⟩ : syracuseStep 43523153 = 32642365) B32642365
theorem B5095163 : Blo 1788095 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B1789231 : Blo 1788095 1789231 := bstep (se 1 (by rfl) ⟨1341923, by rfl⟩ : syracuseStep 1789231 = 2683847) B2683847
theorem B27553279 : Blo 1788095 27553279 := bstep (se 1 (by rfl) ⟨20664959, by rfl⟩ : syracuseStep 27553279 = 41329919) B41329919
theorem B13587101 : Blo 1788095 13587101 := bstep (se 3 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 13587101 = 5095163) B5095163
theorem B29015435 : Blo 1788095 29015435 := bstep (se 1 (by rfl) ⟨21761576, by rfl⟩ : syracuseStep 29015435 = 43523153) B43523153
theorem B19343623 : Blo 1788095 19343623 := bstep (se 1 (by rfl) ⟨14507717, by rfl⟩ : syracuseStep 19343623 = 29015435) B29015435
theorem B36737705 : Blo 1788095 36737705 := bstep (se 2 (by rfl) ⟨13776639, by rfl⟩ : syracuseStep 36737705 = 27553279) B27553279
theorem B9058067 : Blo 1788095 9058067 := bstep (se 1 (by rfl) ⟨6793550, by rfl⟩ : syracuseStep 9058067 = 13587101) B13587101
theorem B6038711 : Blo 1788095 6038711 := bstep (se 1 (by rfl) ⟨4529033, by rfl⟩ : syracuseStep 6038711 = 9058067) B9058067
theorem B25791497 : Blo 1788095 25791497 := bstep (se 2 (by rfl) ⟨9671811, by rfl⟩ : syracuseStep 25791497 = 19343623) B19343623
theorem B24491803 : Blo 1788095 24491803 := bstep (se 1 (by rfl) ⟨18368852, by rfl⟩ : syracuseStep 24491803 = 36737705) B36737705
theorem B32655737 : Blo 1788095 32655737 := bstep (se 2 (by rfl) ⟨12245901, by rfl⟩ : syracuseStep 32655737 = 24491803) B24491803
theorem B4025807 : Blo 1788095 4025807 := bstep (se 1 (by rfl) ⟨3019355, by rfl⟩ : syracuseStep 4025807 = 6038711) B6038711
theorem B17194331 : Blo 1788095 17194331 := bstep (se 1 (by rfl) ⟨12895748, by rfl⟩ : syracuseStep 17194331 = 25791497) B25791497
theorem B11462887 : Blo 1788095 11462887 := bstep (se 1 (by rfl) ⟨8597165, by rfl⟩ : syracuseStep 11462887 = 17194331) B17194331
theorem B21770491 : Blo 1788095 21770491 := bstep (se 1 (by rfl) ⟨16327868, by rfl⟩ : syracuseStep 21770491 = 32655737) B32655737
theorem B2683871 : Blo 1788095 2683871 := bstep (se 1 (by rfl) ⟨2012903, by rfl⟩ : syracuseStep 2683871 = 4025807) B4025807
theorem B29027321 : Blo 1788095 29027321 := bstep (se 2 (by rfl) ⟨10885245, by rfl⟩ : syracuseStep 29027321 = 21770491) B21770491
theorem B1789247 : Blo 1788095 1789247 := bstep (se 1 (by rfl) ⟨1341935, by rfl⟩ : syracuseStep 1789247 = 2683871) B2683871
theorem B15283849 : Blo 1788095 15283849 := bstep (se 2 (by rfl) ⟨5731443, by rfl⟩ : syracuseStep 15283849 = 11462887) B11462887
theorem B19351547 : Blo 1788095 19351547 := bstep (se 1 (by rfl) ⟨14513660, by rfl⟩ : syracuseStep 19351547 = 29027321) B29027321
theorem B20378465 : Blo 1788095 20378465 := bstep (se 2 (by rfl) ⟨7641924, by rfl⟩ : syracuseStep 20378465 = 15283849) B15283849
theorem B13585643 : Blo 1788095 13585643 := bstep (se 1 (by rfl) ⟨10189232, by rfl⟩ : syracuseStep 13585643 = 20378465) B20378465
theorem B12901031 : Blo 1788095 12901031 := bstep (se 1 (by rfl) ⟨9675773, by rfl⟩ : syracuseStep 12901031 = 19351547) B19351547
theorem B9057095 : Blo 1788095 9057095 := bstep (se 1 (by rfl) ⟨6792821, by rfl⟩ : syracuseStep 9057095 = 13585643) B13585643
theorem B8600687 : Blo 1788095 8600687 := bstep (se 1 (by rfl) ⟨6450515, by rfl⟩ : syracuseStep 8600687 = 12901031) B12901031
theorem B6038063 : Blo 1788095 6038063 := bstep (se 1 (by rfl) ⟨4528547, by rfl⟩ : syracuseStep 6038063 = 9057095) B9057095
theorem B5733791 : Blo 1788095 5733791 := bstep (se 1 (by rfl) ⟨4300343, by rfl⟩ : syracuseStep 5733791 = 8600687) B8600687
theorem B4025375 : Blo 1788095 4025375 := bstep (se 1 (by rfl) ⟨3019031, by rfl⟩ : syracuseStep 4025375 = 6038063) B6038063
theorem B3822527 : Blo 1788095 3822527 := bstep (se 1 (by rfl) ⟨2866895, by rfl⟩ : syracuseStep 3822527 = 5733791) B5733791
theorem B2548351 : Blo 1788095 2548351 := bstep (se 1 (by rfl) ⟨1911263, by rfl⟩ : syracuseStep 2548351 = 3822527) B3822527
theorem B2683583 : Blo 1788095 2683583 := bstep (se 1 (by rfl) ⟨2012687, by rfl⟩ : syracuseStep 2683583 = 4025375) B4025375
theorem B1789055 : Blo 1788095 1789055 := bstep (se 1 (by rfl) ⟨1341791, by rfl⟩ : syracuseStep 1789055 = 2683583) B2683583
theorem B3397801 : Blo 1788095 3397801 := bstep (se 2 (by rfl) ⟨1274175, by rfl⟩ : syracuseStep 3397801 = 2548351) B2548351
theorem B4530401 : Blo 1788095 4530401 := bstep (se 2 (by rfl) ⟨1698900, by rfl⟩ : syracuseStep 4530401 = 3397801) B3397801
theorem B3020267 : Blo 1788095 3020267 := bstep (se 1 (by rfl) ⟨2265200, by rfl⟩ : syracuseStep 3020267 = 4530401) B4530401
theorem B2013511 : Blo 1788095 2013511 := bstep (se 1 (by rfl) ⟨1510133, by rfl⟩ : syracuseStep 2013511 = 3020267) B3020267
theorem B2684681 : Blo 1788095 2684681 := bstep (se 2 (by rfl) ⟨1006755, by rfl⟩ : syracuseStep 2684681 = 2013511) B2013511
theorem B1789787 : Blo 1788095 1789787 := bstep (se 1 (by rfl) ⟨1342340, by rfl⟩ : syracuseStep 1789787 = 2684681) B2684681

theorem C0 (j : ℕ) (h1 : 447023 ≤ j) (h2 : j ≤ 447523) : Blo 1788095 (4 * j + 3) := by
  interval_cases j
  · exact B1788095
  · exact B1788099
  · exact B1788103
  · exact B1788107
  · exact B1788111
  · exact B1788115
  · exact B1788119
  · exact B1788123
  · exact B1788127
  · exact B1788131
  · exact B1788135
  · exact B1788139
  · exact B1788143
  · exact B1788147
  · exact B1788151
  · exact B1788155
  · exact B1788159
  · exact B1788163
  · exact B1788167
  · exact B1788171
  · exact B1788175
  · exact B1788179
  · exact B1788183
  · exact B1788187
  · exact B1788191
  · exact B1788195
  · exact B1788199
  · exact B1788203
  · exact B1788207
  · exact B1788211
  · exact B1788215
  · exact B1788219
  · exact B1788223
  · exact B1788227
  · exact B1788231
  · exact B1788235
  · exact B1788239
  · exact B1788243
  · exact B1788247
  · exact B1788251
  · exact B1788255
  · exact B1788259
  · exact B1788263
  · exact B1788267
  · exact B1788271
  · exact B1788275
  · exact B1788279
  · exact B1788283
  · exact B1788287
  · exact B1788291
  · exact B1788295
  · exact B1788299
  · exact B1788303
  · exact B1788307
  · exact B1788311
  · exact B1788315
  · exact B1788319
  · exact B1788323
  · exact B1788327
  · exact B1788331
  · exact B1788335
  · exact B1788339
  · exact B1788343
  · exact B1788347
  · exact B1788351
  · exact B1788355
  · exact B1788359
  · exact B1788363
  · exact B1788367
  · exact B1788371
  · exact B1788375
  · exact B1788379
  · exact B1788383
  · exact B1788387
  · exact B1788391
  · exact B1788395
  · exact B1788399
  · exact B1788403
  · exact B1788407
  · exact B1788411
  · exact B1788415
  · exact B1788419
  · exact B1788423
  · exact B1788427
  · exact B1788431
  · exact B1788435
  · exact B1788439
  · exact B1788443
  · exact B1788447
  · exact B1788451
  · exact B1788455
  · exact B1788459
  · exact B1788463
  · exact B1788467
  · exact B1788471
  · exact B1788475
  · exact B1788479
  · exact B1788483
  · exact B1788487
  · exact B1788491
  · exact B1788495
  · exact B1788499
  · exact B1788503
  · exact B1788507
  · exact B1788511
  · exact B1788515
  · exact B1788519
  · exact B1788523
  · exact B1788527
  · exact B1788531
  · exact B1788535
  · exact B1788539
  · exact B1788543
  · exact B1788547
  · exact B1788551
  · exact B1788555
  · exact B1788559
  · exact B1788563
  · exact B1788567
  · exact B1788571
  · exact B1788575
  · exact B1788579
  · exact B1788583
  · exact B1788587
  · exact B1788591
  · exact B1788595
  · exact B1788599
  · exact B1788603
  · exact B1788607
  · exact B1788611
  · exact B1788615
  · exact B1788619
  · exact B1788623
  · exact B1788627
  · exact B1788631
  · exact B1788635
  · exact B1788639
  · exact B1788643
  · exact B1788647
  · exact B1788651
  · exact B1788655
  · exact B1788659
  · exact B1788663
  · exact B1788667
  · exact B1788671
  · exact B1788675
  · exact B1788679
  · exact B1788683
  · exact B1788687
  · exact B1788691
  · exact B1788695
  · exact B1788699
  · exact B1788703
  · exact B1788707
  · exact B1788711
  · exact B1788715
  · exact B1788719
  · exact B1788723
  · exact B1788727
  · exact B1788731
  · exact B1788735
  · exact B1788739
  · exact B1788743
  · exact B1788747
  · exact B1788751
  · exact B1788755
  · exact B1788759
  · exact B1788763
  · exact B1788767
  · exact B1788771
  · exact B1788775
  · exact B1788779
  · exact B1788783
  · exact B1788787
  · exact B1788791
  · exact B1788795
  · exact B1788799
  · exact B1788803
  · exact B1788807
  · exact B1788811
  · exact B1788815
  · exact B1788819
  · exact B1788823
  · exact B1788827
  · exact B1788831
  · exact B1788835
  · exact B1788839
  · exact B1788843
  · exact B1788847
  · exact B1788851
  · exact B1788855
  · exact B1788859
  · exact B1788863
  · exact B1788867
  · exact B1788871
  · exact B1788875
  · exact B1788879
  · exact B1788883
  · exact B1788887
  · exact B1788891
  · exact B1788895
  · exact B1788899
  · exact B1788903
  · exact B1788907
  · exact B1788911
  · exact B1788915
  · exact B1788919
  · exact B1788923
  · exact B1788927
  · exact B1788931
  · exact B1788935
  · exact B1788939
  · exact B1788943
  · exact B1788947
  · exact B1788951
  · exact B1788955
  · exact B1788959
  · exact B1788963
  · exact B1788967
  · exact B1788971
  · exact B1788975
  · exact B1788979
  · exact B1788983
  · exact B1788987
  · exact B1788991
  · exact B1788995
  · exact B1788999
  · exact B1789003
  · exact B1789007
  · exact B1789011
  · exact B1789015
  · exact B1789019
  · exact B1789023
  · exact B1789027
  · exact B1789031
  · exact B1789035
  · exact B1789039
  · exact B1789043
  · exact B1789047
  · exact B1789051
  · exact B1789055
  · exact B1789059
  · exact B1789063
  · exact B1789067
  · exact B1789071
  · exact B1789075
  · exact B1789079
  · exact B1789083
  · exact B1789087
  · exact B1789091
  · exact B1789095
  · exact B1789099
  · exact B1789103
  · exact B1789107
  · exact B1789111
  · exact B1789115
  · exact B1789119
  · exact B1789123
  · exact B1789127
  · exact B1789131
  · exact B1789135
  · exact B1789139
  · exact B1789143
  · exact B1789147
  · exact B1789151
  · exact B1789155
  · exact B1789159
  · exact B1789163
  · exact B1789167
  · exact B1789171
  · exact B1789175
  · exact B1789179
  · exact B1789183
  · exact B1789187
  · exact B1789191
  · exact B1789195
  · exact B1789199
  · exact B1789203
  · exact B1789207
  · exact B1789211
  · exact B1789215
  · exact B1789219
  · exact B1789223
  · exact B1789227
  · exact B1789231
  · exact B1789235
  · exact B1789239
  · exact B1789243
  · exact B1789247
  · exact B1789251
  · exact B1789255
  · exact B1789259
  · exact B1789263
  · exact B1789267
  · exact B1789271
  · exact B1789275
  · exact B1789279
  · exact B1789283
  · exact B1789287
  · exact B1789291
  · exact B1789295
  · exact B1789299
  · exact B1789303
  · exact B1789307
  · exact B1789311
  · exact B1789315
  · exact B1789319
  · exact B1789323
  · exact B1789327
  · exact B1789331
  · exact B1789335
  · exact B1789339
  · exact B1789343
  · exact B1789347
  · exact B1789351
  · exact B1789355
  · exact B1789359
  · exact B1789363
  · exact B1789367
  · exact B1789371
  · exact B1789375
  · exact B1789379
  · exact B1789383
  · exact B1789387
  · exact B1789391
  · exact B1789395
  · exact B1789399
  · exact B1789403
  · exact B1789407
  · exact B1789411
  · exact B1789415
  · exact B1789419
  · exact B1789423
  · exact B1789427
  · exact B1789431
  · exact B1789435
  · exact B1789439
  · exact B1789443
  · exact B1789447
  · exact B1789451
  · exact B1789455
  · exact B1789459
  · exact B1789463
  · exact B1789467
  · exact B1789471
  · exact B1789475
  · exact B1789479
  · exact B1789483
  · exact B1789487
  · exact B1789491
  · exact B1789495
  · exact B1789499
  · exact B1789503
  · exact B1789507
  · exact B1789511
  · exact B1789515
  · exact B1789519
  · exact B1789523
  · exact B1789527
  · exact B1789531
  · exact B1789535
  · exact B1789539
  · exact B1789543
  · exact B1789547
  · exact B1789551
  · exact B1789555
  · exact B1789559
  · exact B1789563
  · exact B1789567
  · exact B1789571
  · exact B1789575
  · exact B1789579
  · exact B1789583
  · exact B1789587
  · exact B1789591
  · exact B1789595
  · exact B1789599
  · exact B1789603
  · exact B1789607
  · exact B1789611
  · exact B1789615
  · exact B1789619
  · exact B1789623
  · exact B1789627
  · exact B1789631
  · exact B1789635
  · exact B1789639
  · exact B1789643
  · exact B1789647
  · exact B1789651
  · exact B1789655
  · exact B1789659
  · exact B1789663
  · exact B1789667
  · exact B1789671
  · exact B1789675
  · exact B1789679
  · exact B1789683
  · exact B1789687
  · exact B1789691
  · exact B1789695
  · exact B1789699
  · exact B1789703
  · exact B1789707
  · exact B1789711
  · exact B1789715
  · exact B1789719
  · exact B1789723
  · exact B1789727
  · exact B1789731
  · exact B1789735
  · exact B1789739
  · exact B1789743
  · exact B1789747
  · exact B1789751
  · exact B1789755
  · exact B1789759
  · exact B1789763
  · exact B1789767
  · exact B1789771
  · exact B1789775
  · exact B1789779
  · exact B1789783
  · exact B1789787
  · exact B1789791
  · exact B1789795
  · exact B1789799
  · exact B1789803
  · exact B1789807
  · exact B1789811
  · exact B1789815
  · exact B1789819
  · exact B1789823
  · exact B1789827
  · exact B1789831
  · exact B1789835
  · exact B1789839
  · exact B1789843
  · exact B1789847
  · exact B1789851
  · exact B1789855
  · exact B1789859
  · exact B1789863
  · exact B1789867
  · exact B1789871
  · exact B1789875
  · exact B1789879
  · exact B1789883
  · exact B1789887
  · exact B1789891
  · exact B1789895
  · exact B1789899
  · exact B1789903
  · exact B1789907
  · exact B1789911
  · exact B1789915
  · exact B1789919
  · exact B1789923
  · exact B1789927
  · exact B1789931
  · exact B1789935
  · exact B1789939
  · exact B1789943
  · exact B1789947
  · exact B1789951
  · exact B1789955
  · exact B1789959
  · exact B1789963
  · exact B1789967
  · exact B1789971
  · exact B1789975
  · exact B1789979
  · exact B1789983
  · exact B1789987
  · exact B1789991
  · exact B1789995
  · exact B1789999
  · exact B1790003
  · exact B1790007
  · exact B1790011
  · exact B1790015
  · exact B1790019
  · exact B1790023
  · exact B1790027
  · exact B1790031
  · exact B1790035
  · exact B1790039
  · exact B1790043
  · exact B1790047
  · exact B1790051
  · exact B1790055
  · exact B1790059
  · exact B1790063
  · exact B1790067
  · exact B1790071
  · exact B1790075
  · exact B1790079
  · exact B1790083
  · exact B1790087
  · exact B1790091
  · exact B1790095

theorem solution (m : ℕ) (hlo : 1788095 ≤ m) (hhi : m ≤ 1790095) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 447023 ≤ j := by omega
    have hj2 : j ≤ 447523 := by omega
    have hb : Blo 1788095 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
