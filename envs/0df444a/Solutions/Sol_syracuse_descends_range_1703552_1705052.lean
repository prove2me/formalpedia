-- Prove2me | solution 1 for syracuse_descends_range_1703552_1705052
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:26:17.150984+00:00
-- url     : https://prove2.me/submissions/2b3466a5-98be-41ec-ac73-2e12b076bce2

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


theorem B2555909 : Blo 1703552 2555909 := bbase (se 4 (by rfl) ⟨239616, by rfl⟩ : syracuseStep 2555909 = 479233) (by norm_num)
theorem B2875405 : Blo 1703552 2875405 := bbase (se 3 (by rfl) ⟨539138, by rfl⟩ : syracuseStep 2875405 = 1078277) (by norm_num)
theorem B1916941 : Blo 1703552 1916941 := bbase (se 3 (by rfl) ⟨359426, by rfl⟩ : syracuseStep 1916941 = 718853) (by norm_num)
theorem B2187281 : Blo 1703552 2187281 := bbase (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) (by norm_num)
theorem B2555933 : Blo 1703552 2555933 := bbase (se 3 (by rfl) ⟨479237, by rfl⟩ : syracuseStep 2555933 = 958475) (by norm_num)
theorem B1916977 : Blo 1703552 1916977 := bbase (se 2 (by rfl) ⟨718866, by rfl⟩ : syracuseStep 1916977 = 1437733) (by norm_num)
theorem B5750837 : Blo 1703552 5750837 := bbase (se 5 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 5750837 = 539141) (by norm_num)
theorem B3833909 : Blo 1703552 3833909 := bbase (se 5 (by rfl) ⟨179714, by rfl⟩ : syracuseStep 3833909 = 359429) (by norm_num)
theorem B2555957 : Blo 1703552 2555957 := bbase (se 5 (by rfl) ⟨119810, by rfl⟩ : syracuseStep 2555957 = 239621) (by norm_num)
theorem B2555981 : Blo 1703552 2555981 := bbase (se 3 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 2555981 = 958493) (by norm_num)
theorem B1917013 : Blo 1703552 1917013 := bbase (se 8 (by rfl) ⟨11232, by rfl⟩ : syracuseStep 1917013 = 22465) (by norm_num)
theorem B3235925 : Blo 1703552 3235925 := bbase (se 8 (by rfl) ⟨18960, by rfl⟩ : syracuseStep 3235925 = 37921) (by norm_num)
theorem B2875493 : Blo 1703552 2875493 := bbase (se 4 (by rfl) ⟨269577, by rfl⟩ : syracuseStep 2875493 = 539155) (by norm_num)
theorem B2556005 : Blo 1703552 2556005 := bbase (se 4 (by rfl) ⟨239625, by rfl⟩ : syracuseStep 2556005 = 479251) (by norm_num)
theorem B3833981 : Blo 1703552 3833981 := bbase (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) (by norm_num)
theorem B2556029 : Blo 1703552 2556029 := bbase (se 3 (by rfl) ⟨479255, by rfl⟩ : syracuseStep 2556029 = 958511) (by norm_num)
theorem B1917049 : Blo 1703552 1917049 := bbase (se 2 (by rfl) ⟨718893, by rfl⟩ : syracuseStep 1917049 = 1437787) (by norm_num)
theorem B4096133 : Blo 1703552 4096133 := bbase (se 4 (by rfl) ⟨384012, by rfl⟩ : syracuseStep 4096133 = 768025) (by norm_num)
theorem B2556053 : Blo 1703552 2556053 := bbase (se 6 (by rfl) ⟨59907, by rfl⟩ : syracuseStep 2556053 = 119815) (by norm_num)
theorem B1917085 : Blo 1703552 1917085 := bbase (se 3 (by rfl) ⟨359453, by rfl⟩ : syracuseStep 1917085 = 718907) (by norm_num)
theorem B2556077 : Blo 1703552 2556077 := bbase (se 3 (by rfl) ⟨479264, by rfl⟩ : syracuseStep 2556077 = 958529) (by norm_num)
theorem B2916533 : Blo 1703552 2916533 := bbase (se 5 (by rfl) ⟨136712, by rfl⟩ : syracuseStep 2916533 = 273425) (by norm_num)
theorem B1917121 : Blo 1703552 1917121 := bbase (se 2 (by rfl) ⟨718920, by rfl⟩ : syracuseStep 1917121 = 1437841) (by norm_num)
theorem B3834053 : Blo 1703552 3834053 := bbase (se 4 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 3834053 = 718885) (by norm_num)
theorem B2556101 : Blo 1703552 2556101 := bbase (se 4 (by rfl) ⟨239634, by rfl⟩ : syracuseStep 2556101 = 479269) (by norm_num)
theorem B2556125 : Blo 1703552 2556125 := bbase (se 3 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 2556125 = 958547) (by norm_num)
theorem B2875621 : Blo 1703552 2875621 := bbase (se 4 (by rfl) ⟨269589, by rfl⟩ : syracuseStep 2875621 = 539179) (by norm_num)
theorem B1917157 : Blo 1703552 1917157 := bbase (se 4 (by rfl) ⟨179733, by rfl⟩ : syracuseStep 1917157 = 359467) (by norm_num)
theorem B2556149 : Blo 1703552 2556149 := bbase (se 5 (by rfl) ⟨119819, by rfl⟩ : syracuseStep 2556149 = 239639) (by norm_num)
theorem B1917193 : Blo 1703552 1917193 := bbase (se 2 (by rfl) ⟨718947, by rfl⟩ : syracuseStep 1917193 = 1437895) (by norm_num)
theorem B3834125 : Blo 1703552 3834125 := bbase (se 3 (by rfl) ⟨718898, by rfl⟩ : syracuseStep 3834125 = 1437797) (by norm_num)
theorem B2556173 : Blo 1703552 2556173 := bbase (se 3 (by rfl) ⟨479282, by rfl⟩ : syracuseStep 2556173 = 958565) (by norm_num)
theorem B12943637 : Blo 1703552 12943637 := bbase (se 6 (by rfl) ⟨303366, by rfl⟩ : syracuseStep 12943637 = 606733) (by norm_num)
theorem B2556197 : Blo 1703552 2556197 := bbase (se 4 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 2556197 = 479287) (by norm_num)
theorem B1917229 : Blo 1703552 1917229 := bbase (se 3 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 1917229 = 718961) (by norm_num)
theorem B2875709 : Blo 1703552 2875709 := bbase (se 3 (by rfl) ⟨539195, by rfl⟩ : syracuseStep 2875709 = 1078391) (by norm_num)
theorem B2556221 : Blo 1703552 2556221 := bbase (se 3 (by rfl) ⟨479291, by rfl⟩ : syracuseStep 2556221 = 958583) (by norm_num)
theorem B1917265 : Blo 1703552 1917265 := bbase (se 2 (by rfl) ⟨718974, by rfl⟩ : syracuseStep 1917265 = 1437949) (by norm_num)
theorem B3834197 : Blo 1703552 3834197 := bbase (se 10 (by rfl) ⟨5616, by rfl⟩ : syracuseStep 3834197 = 11233) (by norm_num)
theorem B2556245 : Blo 1703552 2556245 := bbase (se 10 (by rfl) ⟨3744, by rfl⟩ : syracuseStep 2556245 = 7489) (by norm_num)
theorem B2556269 : Blo 1703552 2556269 := bbase (se 3 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 2556269 = 958601) (by norm_num)
theorem B1917301 : Blo 1703552 1917301 := bbase (se 5 (by rfl) ⟨89873, by rfl⟩ : syracuseStep 1917301 = 179747) (by norm_num)
theorem B3236213 : Blo 1703552 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2556293 : Blo 1703552 2556293 := bbase (se 4 (by rfl) ⟨239652, by rfl⟩ : syracuseStep 2556293 = 479305) (by norm_num)
theorem B1917337 : Blo 1703552 1917337 := bbase (se 2 (by rfl) ⟨719001, by rfl⟩ : syracuseStep 1917337 = 1438003) (by norm_num)
theorem B3834269 : Blo 1703552 3834269 := bbase (se 3 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 3834269 = 1437851) (by norm_num)
theorem B2556317 : Blo 1703552 2556317 := bbase (se 3 (by rfl) ⟨479309, by rfl⟩ : syracuseStep 2556317 = 958619) (by norm_num)
theorem B2556341 : Blo 1703552 2556341 := bbase (se 5 (by rfl) ⟨119828, by rfl⟩ : syracuseStep 2556341 = 239657) (by norm_num)
theorem B9707957 : Blo 1703552 9707957 := bbase (se 5 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 9707957 = 910121) (by norm_num)
theorem B2875837 : Blo 1703552 2875837 := bbase (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) (by norm_num)
theorem B1917373 : Blo 1703552 1917373 := bbase (se 3 (by rfl) ⟨359507, by rfl⟩ : syracuseStep 1917373 = 719015) (by norm_num)
theorem B2556365 : Blo 1703552 2556365 := bbase (se 3 (by rfl) ⟨479318, by rfl⟩ : syracuseStep 2556365 = 958637) (by norm_num)
theorem B1917409 : Blo 1703552 1917409 := bbase (se 2 (by rfl) ⟨719028, by rfl⟩ : syracuseStep 1917409 = 1438057) (by norm_num)
theorem B8626661 : Blo 1703552 8626661 := bbase (se 4 (by rfl) ⟨808749, by rfl⟩ : syracuseStep 8626661 = 1617499) (by norm_num)
theorem B5751269 : Blo 1703552 5751269 := bbase (se 4 (by rfl) ⟨539181, by rfl⟩ : syracuseStep 5751269 = 1078363) (by norm_num)
theorem B3834341 : Blo 1703552 3834341 := bbase (se 4 (by rfl) ⟨359469, by rfl⟩ : syracuseStep 3834341 = 718939) (by norm_num)
theorem B2556389 : Blo 1703552 2556389 := bbase (se 4 (by rfl) ⟨239661, by rfl⟩ : syracuseStep 2556389 = 479323) (by norm_num)
theorem B2556413 : Blo 1703552 2556413 := bbase (se 3 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 2556413 = 958655) (by norm_num)
theorem B1917445 : Blo 1703552 1917445 := bbase (se 4 (by rfl) ⟨179760, by rfl⟩ : syracuseStep 1917445 = 359521) (by norm_num)
theorem B3236365 : Blo 1703552 3236365 := bbase (se 3 (by rfl) ⟨606818, by rfl⟩ : syracuseStep 3236365 = 1213637) (by norm_num)
theorem B2875925 : Blo 1703552 2875925 := bbase (se 6 (by rfl) ⟨67404, by rfl⟩ : syracuseStep 2875925 = 134809) (by norm_num)
theorem B2556437 : Blo 1703552 2556437 := bbase (se 6 (by rfl) ⟨59916, by rfl⟩ : syracuseStep 2556437 = 119833) (by norm_num)
theorem B1917481 : Blo 1703552 1917481 := bbase (se 2 (by rfl) ⟨719055, by rfl⟩ : syracuseStep 1917481 = 1438111) (by norm_num)
theorem B3834413 : Blo 1703552 3834413 := bbase (se 3 (by rfl) ⟨718952, by rfl⟩ : syracuseStep 3834413 = 1437905) (by norm_num)
theorem B2556461 : Blo 1703552 2556461 := bbase (se 3 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 2556461 = 958673) (by norm_num)
theorem B15753781 : Blo 1703552 15753781 := bbase (se 5 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 15753781 = 1476917) (by norm_num)
theorem B2556485 : Blo 1703552 2556485 := bbase (se 4 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 2556485 = 479341) (by norm_num)
theorem B1917517 : Blo 1703552 1917517 := bbase (se 3 (by rfl) ⟨359534, by rfl⟩ : syracuseStep 1917517 = 719069) (by norm_num)
theorem B1819217 : Blo 1703552 1819217 := bbase (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) (by norm_num)
theorem B2556509 : Blo 1703552 2556509 := bbase (se 3 (by rfl) ⟨479345, by rfl⟩ : syracuseStep 2556509 = 958691) (by norm_num)
theorem B1917553 : Blo 1703552 1917553 := bbase (se 2 (by rfl) ⟨719082, by rfl⟩ : syracuseStep 1917553 = 1438165) (by norm_num)
theorem B3834485 : Blo 1703552 3834485 := bbase (se 5 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 3834485 = 359483) (by norm_num)
theorem B2556533 : Blo 1703552 2556533 := bbase (se 5 (by rfl) ⟨119837, by rfl⟩ : syracuseStep 2556533 = 239675) (by norm_num)
theorem B2556557 : Blo 1703552 2556557 := bbase (se 3 (by rfl) ⟨479354, by rfl⟩ : syracuseStep 2556557 = 958709) (by norm_num)
theorem B2876053 : Blo 1703552 2876053 := bbase (se 6 (by rfl) ⟨67407, by rfl⟩ : syracuseStep 2876053 = 134815) (by norm_num)
theorem B1917589 : Blo 1703552 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B2556581 : Blo 1703552 2556581 := bbase (se 4 (by rfl) ⟨239679, by rfl⟩ : syracuseStep 2556581 = 479359) (by norm_num)
theorem B1917625 : Blo 1703552 1917625 := bbase (se 2 (by rfl) ⟨719109, by rfl⟩ : syracuseStep 1917625 = 1438219) (by norm_num)
theorem B3834557 : Blo 1703552 3834557 := bbase (se 3 (by rfl) ⟨718979, by rfl⟩ : syracuseStep 3834557 = 1437959) (by norm_num)
theorem B2556605 : Blo 1703552 2556605 := bbase (se 3 (by rfl) ⟨479363, by rfl⟩ : syracuseStep 2556605 = 958727) (by norm_num)
theorem B1819345 : Blo 1703552 1819345 := bbase (se 2 (by rfl) ⟨682254, by rfl⟩ : syracuseStep 1819345 = 1364509) (by norm_num)
theorem B2556629 : Blo 1703552 2556629 := bbase (se 7 (by rfl) ⟨29960, by rfl⟩ : syracuseStep 2556629 = 59921) (by norm_num)
theorem B1917661 : Blo 1703552 1917661 := bbase (se 3 (by rfl) ⟨359561, by rfl⟩ : syracuseStep 1917661 = 719123) (by norm_num)
theorem B2876141 : Blo 1703552 2876141 := bbase (se 3 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 2876141 = 1078553) (by norm_num)
theorem B2556653 : Blo 1703552 2556653 := bbase (se 3 (by rfl) ⟨479372, by rfl⟩ : syracuseStep 2556653 = 958745) (by norm_num)
theorem B1917697 : Blo 1703552 1917697 := bbase (se 2 (by rfl) ⟨719136, by rfl⟩ : syracuseStep 1917697 = 1438273) (by norm_num)
theorem B3834629 : Blo 1703552 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B2556677 : Blo 1703552 2556677 := bbase (se 4 (by rfl) ⟨239688, by rfl⟩ : syracuseStep 2556677 = 479377) (by norm_num)
theorem B20726549 : Blo 1703552 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B2556701 : Blo 1703552 2556701 := bbase (se 3 (by rfl) ⟨479381, by rfl⟩ : syracuseStep 2556701 = 958763) (by norm_num)
theorem B1917733 : Blo 1703552 1917733 := bbase (se 4 (by rfl) ⟨179787, by rfl⟩ : syracuseStep 1917733 = 359575) (by norm_num)
theorem B2556725 : Blo 1703552 2556725 := bbase (se 5 (by rfl) ⟨119846, by rfl⟩ : syracuseStep 2556725 = 239693) (by norm_num)
theorem B3236669 : Blo 1703552 3236669 := bbase (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) (by norm_num)
theorem B1917769 : Blo 1703552 1917769 := bbase (se 2 (by rfl) ⟨719163, by rfl⟩ : syracuseStep 1917769 = 1438327) (by norm_num)
theorem B3834701 : Blo 1703552 3834701 := bbase (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) (by norm_num)
theorem B2556749 : Blo 1703552 2556749 := bbase (se 3 (by rfl) ⟨479390, by rfl⟩ : syracuseStep 2556749 = 958781) (by norm_num)
theorem B2556773 : Blo 1703552 2556773 := bbase (se 4 (by rfl) ⟨239697, by rfl⟩ : syracuseStep 2556773 = 479395) (by norm_num)
theorem B2876269 : Blo 1703552 2876269 := bbase (se 3 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 2876269 = 1078601) (by norm_num)
theorem B1917805 : Blo 1703552 1917805 := bbase (se 3 (by rfl) ⟨359588, by rfl⟩ : syracuseStep 1917805 = 719177) (by norm_num)
theorem B2556797 : Blo 1703552 2556797 := bbase (se 3 (by rfl) ⟨479399, by rfl⟩ : syracuseStep 2556797 = 958799) (by norm_num)
theorem B1917841 : Blo 1703552 1917841 := bbase (se 2 (by rfl) ⟨719190, by rfl⟩ : syracuseStep 1917841 = 1438381) (by norm_num)
theorem B5751701 : Blo 1703552 5751701 := bbase (se 6 (by rfl) ⟨134805, by rfl⟩ : syracuseStep 5751701 = 269611) (by norm_num)
theorem B3834773 : Blo 1703552 3834773 := bbase (se 6 (by rfl) ⟨89877, by rfl⟩ : syracuseStep 3834773 = 179755) (by norm_num)
theorem B2556821 : Blo 1703552 2556821 := bbase (se 6 (by rfl) ⟨59925, by rfl⟩ : syracuseStep 2556821 = 119851) (by norm_num)
theorem B2556845 : Blo 1703552 2556845 := bbase (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) (by norm_num)
theorem B1917877 : Blo 1703552 1917877 := bbase (se 5 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 1917877 = 179801) (by norm_num)
theorem B2876357 : Blo 1703552 2876357 := bbase (se 4 (by rfl) ⟨269658, by rfl⟩ : syracuseStep 2876357 = 539317) (by norm_num)
theorem B2556869 : Blo 1703552 2556869 := bbase (se 4 (by rfl) ⟨239706, by rfl⟩ : syracuseStep 2556869 = 479413) (by norm_num)
theorem B1917913 : Blo 1703552 1917913 := bbase (se 2 (by rfl) ⟨719217, by rfl⟩ : syracuseStep 1917913 = 1438435) (by norm_num)
theorem B3834845 : Blo 1703552 3834845 := bbase (se 3 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 3834845 = 1438067) (by norm_num)
theorem B2556893 : Blo 1703552 2556893 := bbase (se 3 (by rfl) ⟨479417, by rfl⟩ : syracuseStep 2556893 = 958835) (by norm_num)
theorem B3646453 : Blo 1703552 3646453 := bbase (se 5 (by rfl) ⟨170927, by rfl⟩ : syracuseStep 3646453 = 341855) (by norm_num)
theorem B2556917 : Blo 1703552 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B1917949 : Blo 1703552 1917949 := bbase (se 3 (by rfl) ⟨359615, by rfl⟩ : syracuseStep 1917949 = 719231) (by norm_num)
theorem B2556941 : Blo 1703552 2556941 := bbase (se 3 (by rfl) ⟨479426, by rfl⟩ : syracuseStep 2556941 = 958853) (by norm_num)
theorem B1917985 : Blo 1703552 1917985 := bbase (se 2 (by rfl) ⟨719244, by rfl⟩ : syracuseStep 1917985 = 1438489) (by norm_num)
theorem B3834917 : Blo 1703552 3834917 := bbase (se 4 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 3834917 = 719047) (by norm_num)
theorem B2556965 : Blo 1703552 2556965 := bbase (se 4 (by rfl) ⟨239715, by rfl⟩ : syracuseStep 2556965 = 479431) (by norm_num)
theorem B2556989 : Blo 1703552 2556989 := bbase (se 3 (by rfl) ⟨479435, by rfl⟩ : syracuseStep 2556989 = 958871) (by norm_num)
theorem B2876485 : Blo 1703552 2876485 := bbase (se 4 (by rfl) ⟨269670, by rfl⟩ : syracuseStep 2876485 = 539341) (by norm_num)
theorem B1918021 : Blo 1703552 1918021 := bbase (se 4 (by rfl) ⟨179814, by rfl⟩ : syracuseStep 1918021 = 359629) (by norm_num)
theorem B2557013 : Blo 1703552 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B1918057 : Blo 1703552 1918057 := bbase (se 2 (by rfl) ⟨719271, by rfl⟩ : syracuseStep 1918057 = 1438543) (by norm_num)
theorem B2729069 : Blo 1703552 2729069 := bbase (se 3 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 2729069 = 1023401) (by norm_num)
theorem B3834989 : Blo 1703552 3834989 := bbase (se 3 (by rfl) ⟨719060, by rfl⟩ : syracuseStep 3834989 = 1438121) (by norm_num)
theorem B2557037 : Blo 1703552 2557037 := bbase (se 3 (by rfl) ⟨479444, by rfl⟩ : syracuseStep 2557037 = 958889) (by norm_num)
theorem B2557061 : Blo 1703552 2557061 := bbase (se 4 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 2557061 = 479449) (by norm_num)
theorem B1819789 : Blo 1703552 1819789 := bbase (se 3 (by rfl) ⟨341210, by rfl⟩ : syracuseStep 1819789 = 682421) (by norm_num)
theorem B1918093 : Blo 1703552 1918093 := bbase (se 3 (by rfl) ⟨359642, by rfl⟩ : syracuseStep 1918093 = 719285) (by norm_num)
theorem B2843797 : Blo 1703552 2843797 := bbase (se 6 (by rfl) ⟨66651, by rfl⟩ : syracuseStep 2843797 = 133303) (by norm_num)
theorem B2876573 : Blo 1703552 2876573 := bbase (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) (by norm_num)
theorem B2557085 : Blo 1703552 2557085 := bbase (se 3 (by rfl) ⟨479453, by rfl⟩ : syracuseStep 2557085 = 958907) (by norm_num)
theorem B1918129 : Blo 1703552 1918129 := bbase (se 2 (by rfl) ⟨719298, by rfl⟩ : syracuseStep 1918129 = 1438597) (by norm_num)
theorem B3835061 : Blo 1703552 3835061 := bbase (se 5 (by rfl) ⟨179768, by rfl⟩ : syracuseStep 3835061 = 359537) (by norm_num)
theorem B2557109 : Blo 1703552 2557109 := bbase (se 5 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 2557109 = 239729) (by norm_num)
theorem B2557133 : Blo 1703552 2557133 := bbase (se 3 (by rfl) ⟨479462, by rfl⟩ : syracuseStep 2557133 = 958925) (by norm_num)
theorem B1918165 : Blo 1703552 1918165 := bbase (se 7 (by rfl) ⟨22478, by rfl⟩ : syracuseStep 1918165 = 44957) (by norm_num)
theorem B2557157 : Blo 1703552 2557157 := bbase (se 4 (by rfl) ⟨239733, by rfl⟩ : syracuseStep 2557157 = 479467) (by norm_num)
theorem B3835133 : Blo 1703552 3835133 := bbase (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) (by norm_num)
theorem B2557181 : Blo 1703552 2557181 := bbase (se 3 (by rfl) ⟨479471, by rfl⟩ : syracuseStep 2557181 = 958943) (by norm_num)
theorem B1819909 : Blo 1703552 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B1844489 : Blo 1703552 1844489 := bbase (se 2 (by rfl) ⟨691683, by rfl⟩ : syracuseStep 1844489 = 1383367) (by norm_num)
theorem B6227221 : Blo 1703552 6227221 := bbase (se 6 (by rfl) ⟨145950, by rfl⟩ : syracuseStep 6227221 = 291901) (by norm_num)
theorem B2557205 : Blo 1703552 2557205 := bbase (se 6 (by rfl) ⟨59934, by rfl⟩ : syracuseStep 2557205 = 119869) (by norm_num)
theorem B2876701 : Blo 1703552 2876701 := bbase (se 3 (by rfl) ⟨539381, by rfl⟩ : syracuseStep 2876701 = 1078763) (by norm_num)
theorem B2557229 : Blo 1703552 2557229 := bbase (se 3 (by rfl) ⟨479480, by rfl⟩ : syracuseStep 2557229 = 958961) (by norm_num)
theorem B5752133 : Blo 1703552 5752133 := bbase (se 4 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 5752133 = 1078525) (by norm_num)
theorem B3835205 : Blo 1703552 3835205 := bbase (se 4 (by rfl) ⟨359550, by rfl⟩ : syracuseStep 3835205 = 719101) (by norm_num)
theorem B2557253 : Blo 1703552 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B2557277 : Blo 1703552 2557277 := bbase (se 3 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 2557277 = 958979) (by norm_num)
theorem B2876789 : Blo 1703552 2876789 := bbase (se 5 (by rfl) ⟨134849, by rfl⟩ : syracuseStep 2876789 = 269699) (by norm_num)
theorem B2557301 : Blo 1703552 2557301 := bbase (se 5 (by rfl) ⟨119873, by rfl⟩ : syracuseStep 2557301 = 239747) (by norm_num)
theorem B3835277 : Blo 1703552 3835277 := bbase (se 3 (by rfl) ⟨719114, by rfl⟩ : syracuseStep 3835277 = 1438229) (by norm_num)
theorem B2557325 : Blo 1703552 2557325 := bbase (se 3 (by rfl) ⟨479498, by rfl⟩ : syracuseStep 2557325 = 958997) (by norm_num)
theorem B2557349 : Blo 1703552 2557349 := bbase (se 4 (by rfl) ⟨239751, by rfl⟩ : syracuseStep 2557349 = 479503) (by norm_num)
theorem B6473141 : Blo 1703552 6473141 := bbase (se 5 (by rfl) ⟨303428, by rfl⟩ : syracuseStep 6473141 = 606857) (by norm_num)
theorem B2557373 : Blo 1703552 2557373 := bbase (se 3 (by rfl) ⟨479507, by rfl⟩ : syracuseStep 2557373 = 959015) (by norm_num)
theorem B3835349 : Blo 1703552 3835349 := bbase (se 7 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 3835349 = 89891) (by norm_num)
theorem B2557397 : Blo 1703552 2557397 := bbase (se 7 (by rfl) ⟨29969, by rfl⟩ : syracuseStep 2557397 = 59939) (by norm_num)
theorem B2557421 : Blo 1703552 2557421 := bbase (se 3 (by rfl) ⟨479516, by rfl⟩ : syracuseStep 2557421 = 959033) (by norm_num)
theorem B2876917 : Blo 1703552 2876917 := bbase (se 5 (by rfl) ⟨134855, by rfl⟩ : syracuseStep 2876917 = 269711) (by norm_num)
theorem B1820161 : Blo 1703552 1820161 := bbase (se 2 (by rfl) ⟨682560, by rfl⟩ : syracuseStep 1820161 = 1365121) (by norm_num)
theorem B1820165 : Blo 1703552 1820165 := bbase (se 4 (by rfl) ⟨170640, by rfl⟩ : syracuseStep 1820165 = 341281) (by norm_num)
theorem B2557445 : Blo 1703552 2557445 := bbase (se 4 (by rfl) ⟨239760, by rfl⟩ : syracuseStep 2557445 = 479521) (by norm_num)
theorem B3835421 : Blo 1703552 3835421 := bbase (se 3 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 3835421 = 1438283) (by norm_num)
theorem B2557469 : Blo 1703552 2557469 := bbase (se 3 (by rfl) ⟨479525, by rfl⟩ : syracuseStep 2557469 = 959051) (by norm_num)
theorem B2557493 : Blo 1703552 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B3638861 : Blo 1703552 3638861 := bbase (se 3 (by rfl) ⟨682286, by rfl⟩ : syracuseStep 3638861 = 1364573) (by norm_num)
theorem B2877005 : Blo 1703552 2877005 := bbase (se 3 (by rfl) ⟨539438, by rfl⟩ : syracuseStep 2877005 = 1078877) (by norm_num)
theorem B2557517 : Blo 1703552 2557517 := bbase (se 3 (by rfl) ⟨479534, by rfl⟩ : syracuseStep 2557517 = 959069) (by norm_num)
theorem B1943137 : Blo 1703552 1943137 := bbase (se 2 (by rfl) ⟨728676, by rfl⟩ : syracuseStep 1943137 = 1457353) (by norm_num)
theorem B3835493 : Blo 1703552 3835493 := bbase (se 4 (by rfl) ⟨359577, by rfl⟩ : syracuseStep 3835493 = 719155) (by norm_num)
theorem B2557541 : Blo 1703552 2557541 := bbase (se 4 (by rfl) ⟨239769, by rfl⟩ : syracuseStep 2557541 = 479539) (by norm_num)
theorem B2729581 : Blo 1703552 2729581 := bbase (se 3 (by rfl) ⟨511796, by rfl⟩ : syracuseStep 2729581 = 1023593) (by norm_num)
theorem B2156149 : Blo 1703552 2156149 := bbase (se 5 (by rfl) ⟨101069, by rfl⟩ : syracuseStep 2156149 = 202139) (by norm_num)
theorem B2557565 : Blo 1703552 2557565 := bbase (se 3 (by rfl) ⟨479543, by rfl⟩ : syracuseStep 2557565 = 959087) (by norm_num)
theorem B1943201 : Blo 1703552 1943201 := bbase (se 2 (by rfl) ⟨728700, by rfl⟩ : syracuseStep 1943201 = 1457401) (by norm_num)
theorem B3835565 : Blo 1703552 3835565 := bbase (se 3 (by rfl) ⟨719168, by rfl⟩ : syracuseStep 3835565 = 1438337) (by norm_num)
theorem B3638981 : Blo 1703552 3638981 := bbase (se 4 (by rfl) ⟨341154, by rfl⟩ : syracuseStep 3638981 = 682309) (by norm_num)
theorem B2877133 : Blo 1703552 2877133 := bbase (se 3 (by rfl) ⟨539462, by rfl⟩ : syracuseStep 2877133 = 1078925) (by norm_num)
theorem B6473429 : Blo 1703552 6473429 := bbase (se 7 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 6473429 = 151721) (by norm_num)
theorem B8627957 : Blo 1703552 8627957 := bbase (se 5 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 8627957 = 808871) (by norm_num)
theorem B5752565 : Blo 1703552 5752565 := bbase (se 5 (by rfl) ⟨269651, by rfl⟩ : syracuseStep 5752565 = 539303) (by norm_num)
theorem B3835637 : Blo 1703552 3835637 := bbase (se 5 (by rfl) ⟨179795, by rfl⟩ : syracuseStep 3835637 = 359591) (by norm_num)
theorem B2156321 : Blo 1703552 2156321 := bbase (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) (by norm_num)
theorem B2877221 : Blo 1703552 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B3835709 : Blo 1703552 3835709 := bbase (se 3 (by rfl) ⟨719195, by rfl⟩ : syracuseStep 3835709 = 1438391) (by norm_num)
theorem B4605781 : Blo 1703552 4605781 := bbase (se 9 (by rfl) ⟨13493, by rfl⟩ : syracuseStep 4605781 = 26987) (by norm_num)
theorem B2156377 : Blo 1703552 2156377 := bbase (se 2 (by rfl) ⟨808641, by rfl⟩ : syracuseStep 2156377 = 1617283) (by norm_num)
theorem B3835781 : Blo 1703552 3835781 := bbase (se 4 (by rfl) ⟨359604, by rfl⟩ : syracuseStep 3835781 = 719209) (by norm_num)
theorem B2426773 : Blo 1703552 2426773 := bbase (se 6 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 2426773 = 113755) (by norm_num)
theorem B2156473 : Blo 1703552 2156473 := bbase (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) (by norm_num)
theorem B3835853 : Blo 1703552 3835853 := bbase (se 3 (by rfl) ⟨719222, by rfl⟩ : syracuseStep 3835853 = 1438445) (by norm_num)
theorem B4851701 : Blo 1703552 4851701 := bbase (se 5 (by rfl) ⟨227423, by rfl⟩ : syracuseStep 4851701 = 454847) (by norm_num)
theorem B3835925 : Blo 1703552 3835925 := bbase (se 6 (by rfl) ⟨89904, by rfl⟩ : syracuseStep 3835925 = 179809) (by norm_num)
theorem B2730037 : Blo 1703552 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B1820729 : Blo 1703552 1820729 := bbase (se 2 (by rfl) ⟨682773, by rfl⟩ : syracuseStep 1820729 = 1365547) (by norm_num)
theorem B4671557 : Blo 1703552 4671557 := bbase (se 4 (by rfl) ⟨437958, by rfl⟩ : syracuseStep 4671557 = 875917) (by norm_num)
theorem B3835997 : Blo 1703552 3835997 := bbase (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) (by norm_num)
theorem B2156645 : Blo 1703552 2156645 := bbase (se 4 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 2156645 = 404371) (by norm_num)
theorem B2156701 : Blo 1703552 2156701 := bbase (se 3 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 2156701 = 808763) (by norm_num)
theorem B5752997 : Blo 1703552 5752997 := bbase (se 4 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 5752997 = 1078687) (by norm_num)
theorem B3836069 : Blo 1703552 3836069 := bbase (se 4 (by rfl) ⟨359631, by rfl⟩ : syracuseStep 3836069 = 719263) (by norm_num)
theorem B3836141 : Blo 1703552 3836141 := bbase (se 3 (by rfl) ⟨719276, by rfl⟩ : syracuseStep 3836141 = 1438553) (by norm_num)
theorem B2156797 : Blo 1703552 2156797 := bbase (se 3 (by rfl) ⟨404399, by rfl⟩ : syracuseStep 2156797 = 808799) (by norm_num)
theorem B5458229 : Blo 1703552 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B3836213 : Blo 1703552 3836213 := bbase (se 5 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 3836213 = 359645) (by norm_num)
theorem B3639613 : Blo 1703552 3639613 := bbase (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) (by norm_num)
theorem B149473621 : Blo 1703552 149473621 := bbase (se 10 (by rfl) ⟨218955, by rfl⟩ : syracuseStep 149473621 = 437911) (by norm_num)
theorem B3836285 : Blo 1703552 3836285 := bbase (se 3 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 3836285 = 1438607) (by norm_num)
theorem B2591117 : Blo 1703552 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B3279253 : Blo 1703552 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B4852133 : Blo 1703552 4852133 := bbase (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) (by norm_num)
theorem B2156969 : Blo 1703552 2156969 := bbase (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) (by norm_num)
theorem B3836357 : Blo 1703552 3836357 := bbase (se 4 (by rfl) ⟨359658, by rfl⟩ : syracuseStep 3836357 = 719317) (by norm_num)
theorem B2157025 : Blo 1703552 2157025 := bbase (se 2 (by rfl) ⟨808884, by rfl⟩ : syracuseStep 2157025 = 1617769) (by norm_num)
theorem B2427365 : Blo 1703552 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B2427445 : Blo 1703552 2427445 := bbase (se 5 (by rfl) ⟨113786, by rfl⟩ : syracuseStep 2427445 = 227573) (by norm_num)
theorem B3689021 : Blo 1703552 3689021 := bbase (se 3 (by rfl) ⟨691691, by rfl⟩ : syracuseStep 3689021 = 1383383) (by norm_num)
theorem B2157121 : Blo 1703552 2157121 := bbase (se 2 (by rfl) ⟨808920, by rfl⟩ : syracuseStep 2157121 = 1617841) (by norm_num)
theorem B8186437 : Blo 1703552 8186437 := bbase (se 4 (by rfl) ⟨767478, by rfl⟩ : syracuseStep 8186437 = 1534957) (by norm_num)
theorem B7277141 : Blo 1703552 7277141 := bbase (se 8 (by rfl) ⟨42639, by rfl⟩ : syracuseStep 7277141 = 85279) (by norm_num)
theorem B5753429 : Blo 1703552 5753429 := bbase (se 8 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 5753429 = 67423) (by norm_num)
theorem B2075269 : Blo 1703552 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B2427565 : Blo 1703552 2427565 := bbase (se 3 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 2427565 = 910337) (by norm_num)
theorem B2730709 : Blo 1703552 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B2157293 : Blo 1703552 2157293 := bbase (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) (by norm_num)
theorem B2427661 : Blo 1703552 2427661 := bbase (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) (by norm_num)
theorem B4049693 : Blo 1703552 4049693 := bbase (se 3 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 4049693 = 1518635) (by norm_num)
theorem B2157349 : Blo 1703552 2157349 := bbase (se 4 (by rfl) ⟨202251, by rfl⟩ : syracuseStep 2157349 = 404503) (by norm_num)
theorem B5909365 : Blo 1703552 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B2157445 : Blo 1703552 2157445 := bbase (se 4 (by rfl) ⟨202260, by rfl⟩ : syracuseStep 2157445 = 404521) (by norm_num)
theorem B7007141 : Blo 1703552 7007141 := bbase (se 4 (by rfl) ⟨656919, by rfl⟩ : syracuseStep 7007141 = 1313839) (by norm_num)
theorem B8629253 : Blo 1703552 8629253 := bbase (se 4 (by rfl) ⟨808992, by rfl⟩ : syracuseStep 8629253 = 1617985) (by norm_num)
theorem B5753861 : Blo 1703552 5753861 := bbase (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) (by norm_num)
theorem B2157617 : Blo 1703552 2157617 := bbase (se 2 (by rfl) ⟨809106, by rfl⟩ : syracuseStep 2157617 = 1618213) (by norm_num)
theorem B3886157 : Blo 1703552 3886157 := bbase (se 3 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 3886157 = 1457309) (by norm_num)
theorem B2157673 : Blo 1703552 2157673 := bbase (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) (by norm_num)
theorem B2731133 : Blo 1703552 2731133 := bbase (se 3 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 2731133 = 1024175) (by norm_num)
theorem B4852885 : Blo 1703552 4852885 := bbase (se 6 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 4852885 = 227479) (by norm_num)
theorem B4312237 : Blo 1703552 4312237 := bbase (se 3 (by rfl) ⟨808544, by rfl⟩ : syracuseStep 4312237 = 1617089) (by norm_num)
theorem B3640501 : Blo 1703552 3640501 := bbase (se 5 (by rfl) ⟨170648, by rfl⟩ : syracuseStep 3640501 = 341297) (by norm_num)
theorem B2157769 : Blo 1703552 2157769 := bbase (se 2 (by rfl) ⟨809163, by rfl⟩ : syracuseStep 2157769 = 1618327) (by norm_num)
theorem B29117717 : Blo 1703552 29117717 := bbase (se 6 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 29117717 = 1364893) (by norm_num)
theorem B4312349 : Blo 1703552 4312349 := bbase (se 3 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 4312349 = 1617131) (by norm_num)
theorem B3640621 : Blo 1703552 3640621 := bbase (se 3 (by rfl) ⟨682616, by rfl⟩ : syracuseStep 3640621 = 1365233) (by norm_num)
theorem B2157941 : Blo 1703552 2157941 := bbase (se 5 (by rfl) ⟨101153, by rfl⟩ : syracuseStep 2157941 = 202307) (by norm_num)
theorem B5754293 : Blo 1703552 5754293 := bbase (se 5 (by rfl) ⟨269732, by rfl⟩ : syracuseStep 5754293 = 539465) (by norm_num)
theorem B4312541 : Blo 1703552 4312541 := bbase (se 3 (by rfl) ⟨808601, by rfl⟩ : syracuseStep 4312541 = 1617203) (by norm_num)
theorem B2215397 : Blo 1703552 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B3640877 : Blo 1703552 3640877 := bbase (se 3 (by rfl) ⟨682664, by rfl⟩ : syracuseStep 3640877 = 1365329) (by norm_num)
theorem B3550837 : Blo 1703552 3550837 := bbase (se 5 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 3550837 = 332891) (by norm_num)
theorem B1969921 : Blo 1703552 1969921 := bbase (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) (by norm_num)
theorem B4312885 : Blo 1703552 4312885 := bbase (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) (by norm_num)
theorem B4312997 : Blo 1703552 4312997 := bbase (se 4 (by rfl) ⟨404343, by rfl⟩ : syracuseStep 4312997 = 808687) (by norm_num)
theorem B3280861 : Blo 1703552 3280861 := bbase (se 3 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 3280861 = 1230323) (by norm_num)
theorem B2994245 : Blo 1703552 2994245 := bbase (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) (by norm_num)
theorem B4313189 : Blo 1703552 4313189 := bbase (se 4 (by rfl) ⟨404361, by rfl⟩ : syracuseStep 4313189 = 808723) (by norm_num)
theorem B5460085 : Blo 1703552 5460085 := bbase (se 5 (by rfl) ⟨255941, by rfl⟩ : syracuseStep 5460085 = 511883) (by norm_num)
theorem B6140117 : Blo 1703552 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B4608245 : Blo 1703552 4608245 := bbase (se 5 (by rfl) ⟨216011, by rfl⟩ : syracuseStep 4608245 = 432023) (by norm_num)
theorem B8630549 : Blo 1703552 8630549 := bbase (se 6 (by rfl) ⟨202278, by rfl⟩ : syracuseStep 8630549 = 404557) (by norm_num)
theorem B2806093 : Blo 1703552 2806093 := bbase (se 3 (by rfl) ⟨526142, by rfl⟩ : syracuseStep 2806093 = 1052285) (by norm_num)
theorem B5829029 : Blo 1703552 5829029 := bbase (se 4 (by rfl) ⟨546471, by rfl⟩ : syracuseStep 5829029 = 1092943) (by norm_num)
theorem B4313533 : Blo 1703552 4313533 := bbase (se 3 (by rfl) ⟨808787, by rfl⟩ : syracuseStep 4313533 = 1617575) (by norm_num)
theorem B4313645 : Blo 1703552 4313645 := bbase (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) (by norm_num)
theorem B4313837 : Blo 1703552 4313837 := bbase (se 3 (by rfl) ⟨808844, by rfl⟩ : syracuseStep 4313837 = 1617689) (by norm_num)
theorem B3887909 : Blo 1703552 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B6558517 : Blo 1703552 6558517 := bbase (se 5 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 6558517 = 614861) (by norm_num)
theorem B4314181 : Blo 1703552 4314181 := bbase (se 4 (by rfl) ⟨404454, by rfl⟩ : syracuseStep 4314181 = 808909) (by norm_num)
theorem B4314293 : Blo 1703552 4314293 := bbase (se 5 (by rfl) ⟨202232, by rfl⟩ : syracuseStep 4314293 = 404465) (by norm_num)
theorem B15365429 : Blo 1703552 15365429 := bbase (se 5 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 15365429 = 1440509) (by norm_num)
theorem B4314485 : Blo 1703552 4314485 := bbase (se 5 (by rfl) ⟨202241, by rfl⟩ : syracuseStep 4314485 = 404483) (by norm_num)
theorem B2921869 : Blo 1703552 2921869 := bbase (se 3 (by rfl) ⟨547850, by rfl⟩ : syracuseStep 2921869 = 1095701) (by norm_num)
theorem B4920725 : Blo 1703552 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B5461445 : Blo 1703552 5461445 := bbase (se 4 (by rfl) ⟨512010, by rfl⟩ : syracuseStep 5461445 = 1024021) (by norm_num)
theorem B6469253 : Blo 1703552 6469253 := bbase (se 4 (by rfl) ⟨606492, by rfl⟩ : syracuseStep 6469253 = 1212985) (by norm_num)
theorem B4314829 : Blo 1703552 4314829 := bbase (se 3 (by rfl) ⟨809030, by rfl⟩ : syracuseStep 4314829 = 1618061) (by norm_num)
theorem B4093757 : Blo 1703552 4093757 := bbase (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) (by norm_num)
theorem B4314941 : Blo 1703552 4314941 := bbase (se 3 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 4314941 = 1618103) (by norm_num)
theorem B6469541 : Blo 1703552 6469541 := bbase (se 4 (by rfl) ⟨606519, by rfl⟩ : syracuseStep 6469541 = 1213039) (by norm_num)
theorem B4315133 : Blo 1703552 4315133 := bbase (se 3 (by rfl) ⟨809087, by rfl⟩ : syracuseStep 4315133 = 1618175) (by norm_num)
theorem B19413269 : Blo 1703552 19413269 := bbase (se 6 (by rfl) ⟨454998, by rfl⟩ : syracuseStep 19413269 = 909997) (by norm_num)
theorem B4315477 : Blo 1703552 4315477 := bbase (se 10 (by rfl) ⟨6321, by rfl⟩ : syracuseStep 4315477 = 12643) (by norm_num)
theorem B3455405 : Blo 1703552 3455405 := bbase (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) (by norm_num)
theorem B4315589 : Blo 1703552 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B3234269 : Blo 1703552 3234269 := bbase (se 3 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 3234269 = 1212851) (by norm_num)
theorem B2767421 : Blo 1703552 2767421 := bbase (se 3 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 2767421 = 1037783) (by norm_num)
theorem B3234421 : Blo 1703552 3234421 := bbase (se 5 (by rfl) ⟨151613, by rfl⟩ : syracuseStep 3234421 = 303227) (by norm_num)
theorem B4315781 : Blo 1703552 4315781 := bbase (se 4 (by rfl) ⟨404604, by rfl⟩ : syracuseStep 4315781 = 809209) (by norm_num)
theorem B2046605 : Blo 1703552 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B2046721 : Blo 1703552 2046721 := bbase (se 2 (by rfl) ⟨767520, by rfl⟩ : syracuseStep 2046721 = 1535041) (by norm_num)
theorem B7281413 : Blo 1703552 7281413 := bbase (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) (by norm_num)
theorem B1727249 : Blo 1703552 1727249 := bbase (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) (by norm_num)
theorem B5749541 : Blo 1703552 5749541 := bbase (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) (by norm_num)
theorem B8190821 : Blo 1703552 8190821 := bbase (se 4 (by rfl) ⟨767889, by rfl⟩ : syracuseStep 8190821 = 1535779) (by norm_num)
theorem B3234725 : Blo 1703552 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B2046917 : Blo 1703552 2046917 := bbase (se 4 (by rfl) ⟨191898, by rfl⟩ : syracuseStep 2046917 = 383797) (by norm_num)
theorem B17488885 : Blo 1703552 17488885 := bbase (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) (by norm_num)
theorem B3070981 : Blo 1703552 3070981 := bbase (se 4 (by rfl) ⟨287904, by rfl⟩ : syracuseStep 3070981 = 575809) (by norm_num)
theorem B7478293 : Blo 1703552 7478293 := bbase (se 6 (by rfl) ⟨175272, by rfl⟩ : syracuseStep 7478293 = 350545) (by norm_num)
theorem B2915389 : Blo 1703552 2915389 := bbase (se 3 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 2915389 = 1093271) (by norm_num)
theorem B6470725 : Blo 1703552 6470725 := bbase (se 4 (by rfl) ⟨606630, by rfl⟩ : syracuseStep 6470725 = 1213261) (by norm_num)
theorem B3071125 : Blo 1703552 3071125 := bbase (se 6 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 3071125 = 143959) (by norm_num)
theorem B2186389 : Blo 1703552 2186389 := bbase (se 6 (by rfl) ⟨51243, by rfl⟩ : syracuseStep 2186389 = 102487) (by norm_num)
theorem B3833045 : Blo 1703552 3833045 := bbase (se 7 (by rfl) ⟨44918, by rfl⟩ : syracuseStep 3833045 = 89837) (by norm_num)
theorem B5749973 : Blo 1703552 5749973 := bbase (se 7 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 5749973 = 134765) (by norm_num)
theorem B8625365 : Blo 1703552 8625365 := bbase (se 7 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 8625365 = 202157) (by norm_num)
theorem B3833117 : Blo 1703552 3833117 := bbase (se 3 (by rfl) ⟨718709, by rfl⟩ : syracuseStep 3833117 = 1437419) (by norm_num)
theorem B3833189 : Blo 1703552 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B6471029 : Blo 1703552 6471029 := bbase (se 5 (by rfl) ⟨303329, by rfl⟩ : syracuseStep 6471029 = 606659) (by norm_num)
theorem B1727861 : Blo 1703552 1727861 := bbase (se 5 (by rfl) ⟨80993, by rfl⟩ : syracuseStep 1727861 = 161987) (by norm_num)
theorem B2874757 : Blo 1703552 2874757 := bbase (se 4 (by rfl) ⟨269508, by rfl⟩ : syracuseStep 2874757 = 539017) (by norm_num)
theorem B3833261 : Blo 1703552 3833261 := bbase (se 3 (by rfl) ⟨718736, by rfl⟩ : syracuseStep 3833261 = 1437473) (by norm_num)
theorem B2555333 : Blo 1703552 2555333 := bbase (se 4 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 2555333 = 479125) (by norm_num)
theorem B3071429 : Blo 1703552 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B2555357 : Blo 1703552 2555357 := bbase (se 3 (by rfl) ⟨479129, by rfl⟩ : syracuseStep 2555357 = 958259) (by norm_num)
theorem B2874845 : Blo 1703552 2874845 := bbase (se 3 (by rfl) ⟨539033, by rfl⟩ : syracuseStep 2874845 = 1078067) (by norm_num)
theorem B2047465 : Blo 1703552 2047465 := bbase (se 2 (by rfl) ⟨767799, by rfl⟩ : syracuseStep 2047465 = 1535599) (by norm_num)
theorem B2555381 : Blo 1703552 2555381 := bbase (se 5 (by rfl) ⟨119783, by rfl⟩ : syracuseStep 2555381 = 239567) (by norm_num)
theorem B3833333 : Blo 1703552 3833333 := bbase (se 5 (by rfl) ⟨179687, by rfl⟩ : syracuseStep 3833333 = 359375) (by norm_num)
theorem B2555405 : Blo 1703552 2555405 := bbase (se 3 (by rfl) ⟨479138, by rfl⟩ : syracuseStep 2555405 = 958277) (by norm_num)
theorem B4095517 : Blo 1703552 4095517 := bbase (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) (by norm_num)
theorem B2555429 : Blo 1703552 2555429 := bbase (se 4 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 2555429 = 479143) (by norm_num)
theorem B3112501 : Blo 1703552 3112501 := bbase (se 5 (by rfl) ⟨145898, by rfl⟩ : syracuseStep 3112501 = 291797) (by norm_num)
theorem B2555453 : Blo 1703552 2555453 := bbase (se 3 (by rfl) ⟨479147, by rfl⟩ : syracuseStep 2555453 = 958295) (by norm_num)
theorem B3833405 : Blo 1703552 3833405 := bbase (se 3 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 3833405 = 1437527) (by norm_num)
theorem B2555477 : Blo 1703552 2555477 := bbase (se 8 (by rfl) ⟨14973, by rfl⟩ : syracuseStep 2555477 = 29947) (by norm_num)
theorem B1916509 : Blo 1703552 1916509 := bbase (se 3 (by rfl) ⟨359345, by rfl⟩ : syracuseStep 1916509 = 718691) (by norm_num)
theorem B2874973 : Blo 1703552 2874973 := bbase (se 3 (by rfl) ⟨539057, by rfl⟩ : syracuseStep 2874973 = 1078115) (by norm_num)
theorem B2555501 : Blo 1703552 2555501 := bbase (se 3 (by rfl) ⟨479156, by rfl⟩ : syracuseStep 2555501 = 958313) (by norm_num)
theorem B2047609 : Blo 1703552 2047609 := bbase (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) (by norm_num)
theorem B1916545 : Blo 1703552 1916545 := bbase (se 2 (by rfl) ⟨718704, by rfl⟩ : syracuseStep 1916545 = 1437409) (by norm_num)
theorem B2555525 : Blo 1703552 2555525 := bbase (se 4 (by rfl) ⟨239580, by rfl⟩ : syracuseStep 2555525 = 479161) (by norm_num)
theorem B3833477 : Blo 1703552 3833477 := bbase (se 4 (by rfl) ⟨359388, by rfl⟩ : syracuseStep 3833477 = 718777) (by norm_num)
theorem B5750405 : Blo 1703552 5750405 := bbase (se 4 (by rfl) ⟨539100, by rfl⟩ : syracuseStep 5750405 = 1078201) (by norm_num)
theorem B3235477 : Blo 1703552 3235477 := bbase (se 6 (by rfl) ⟨75831, by rfl⟩ : syracuseStep 3235477 = 151663) (by norm_num)
theorem B16383637 : Blo 1703552 16383637 := bbase (se 6 (by rfl) ⟨383991, by rfl⟩ : syracuseStep 16383637 = 767983) (by norm_num)
theorem B2555549 : Blo 1703552 2555549 := bbase (se 3 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 2555549 = 958331) (by norm_num)
theorem B1916581 : Blo 1703552 1916581 := bbase (se 4 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 1916581 = 359359) (by norm_num)
theorem B2555573 : Blo 1703552 2555573 := bbase (se 5 (by rfl) ⟨119792, by rfl⟩ : syracuseStep 2555573 = 239585) (by norm_num)
theorem B2875061 : Blo 1703552 2875061 := bbase (se 5 (by rfl) ⟨134768, by rfl⟩ : syracuseStep 2875061 = 269537) (by norm_num)
theorem B9215669 : Blo 1703552 9215669 := bbase (se 5 (by rfl) ⟨431984, by rfl⟩ : syracuseStep 9215669 = 863969) (by norm_num)
theorem B1916617 : Blo 1703552 1916617 := bbase (se 2 (by rfl) ⟨718731, by rfl⟩ : syracuseStep 1916617 = 1437463) (by norm_num)
theorem B2555597 : Blo 1703552 2555597 := bbase (se 3 (by rfl) ⟨479174, by rfl⟩ : syracuseStep 2555597 = 958349) (by norm_num)
theorem B3833549 : Blo 1703552 3833549 := bbase (se 3 (by rfl) ⟨718790, by rfl⟩ : syracuseStep 3833549 = 1437581) (by norm_num)
theorem B2555621 : Blo 1703552 2555621 := bbase (se 4 (by rfl) ⟨239589, by rfl⟩ : syracuseStep 2555621 = 479179) (by norm_num)
theorem B1916653 : Blo 1703552 1916653 := bbase (se 3 (by rfl) ⟨359372, by rfl⟩ : syracuseStep 1916653 = 718745) (by norm_num)
theorem B2555645 : Blo 1703552 2555645 := bbase (se 3 (by rfl) ⟨479183, by rfl⟩ : syracuseStep 2555645 = 958367) (by norm_num)
theorem B1916689 : Blo 1703552 1916689 := bbase (se 2 (by rfl) ⟨718758, by rfl⟩ : syracuseStep 1916689 = 1437517) (by norm_num)
theorem B2555669 : Blo 1703552 2555669 := bbase (se 6 (by rfl) ⟨59898, by rfl⟩ : syracuseStep 2555669 = 119797) (by norm_num)
theorem B3833621 : Blo 1703552 3833621 := bbase (se 6 (by rfl) ⟨89850, by rfl⟩ : syracuseStep 3833621 = 179701) (by norm_num)
theorem B3235621 : Blo 1703552 3235621 := bbase (se 4 (by rfl) ⟨303339, by rfl⟩ : syracuseStep 3235621 = 606679) (by norm_num)
theorem B2555693 : Blo 1703552 2555693 := bbase (se 3 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 2555693 = 958385) (by norm_num)
theorem B4374317 : Blo 1703552 4374317 := bbase (se 3 (by rfl) ⟨820184, by rfl⟩ : syracuseStep 4374317 = 1640369) (by norm_num)
theorem B1916725 : Blo 1703552 1916725 := bbase (se 5 (by rfl) ⟨89846, by rfl⟩ : syracuseStep 1916725 = 179693) (by norm_num)
theorem B2875189 : Blo 1703552 2875189 := bbase (se 5 (by rfl) ⟨134774, by rfl⟩ : syracuseStep 2875189 = 269549) (by norm_num)
theorem B2555717 : Blo 1703552 2555717 := bbase (se 4 (by rfl) ⟨239598, by rfl⟩ : syracuseStep 2555717 = 479197) (by norm_num)
theorem B1916761 : Blo 1703552 1916761 := bbase (se 2 (by rfl) ⟨718785, by rfl⟩ : syracuseStep 1916761 = 1437571) (by norm_num)
theorem B2555741 : Blo 1703552 2555741 := bbase (se 3 (by rfl) ⟨479201, by rfl⟩ : syracuseStep 2555741 = 958403) (by norm_num)
theorem B3833693 : Blo 1703552 3833693 := bbase (se 3 (by rfl) ⟨718817, by rfl⟩ : syracuseStep 3833693 = 1437635) (by norm_num)
theorem B2555765 : Blo 1703552 2555765 := bbase (se 5 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 2555765 = 239603) (by norm_num)
theorem B1916797 : Blo 1703552 1916797 := bbase (se 3 (by rfl) ⟨359399, by rfl⟩ : syracuseStep 1916797 = 718799) (by norm_num)
theorem B2555789 : Blo 1703552 2555789 := bbase (se 3 (by rfl) ⟨479210, by rfl⟩ : syracuseStep 2555789 = 958421) (by norm_num)
theorem B2875277 : Blo 1703552 2875277 := bbase (se 3 (by rfl) ⟨539114, by rfl⟩ : syracuseStep 2875277 = 1078229) (by norm_num)
theorem B1916833 : Blo 1703552 1916833 := bbase (se 2 (by rfl) ⟨718812, by rfl⟩ : syracuseStep 1916833 = 1437625) (by norm_num)
theorem B2555813 : Blo 1703552 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B3833765 : Blo 1703552 3833765 := bbase (se 4 (by rfl) ⟨359415, by rfl⟩ : syracuseStep 3833765 = 718831) (by norm_num)
theorem B2555837 : Blo 1703552 2555837 := bbase (se 3 (by rfl) ⟨479219, by rfl⟩ : syracuseStep 2555837 = 958439) (by norm_num)
theorem B1916869 : Blo 1703552 1916869 := bbase (se 4 (by rfl) ⟨179706, by rfl⟩ : syracuseStep 1916869 = 359413) (by norm_num)
theorem B3235781 : Blo 1703552 3235781 := bbase (se 4 (by rfl) ⟨303354, by rfl⟩ : syracuseStep 3235781 = 606709) (by norm_num)
theorem B2555861 : Blo 1703552 2555861 := bbase (se 7 (by rfl) ⟨29951, by rfl⟩ : syracuseStep 2555861 = 59903) (by norm_num)
theorem B1916905 : Blo 1703552 1916905 := bbase (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) (by norm_num)
theorem B2555885 : Blo 1703552 2555885 := bbase (se 3 (by rfl) ⟨479228, by rfl⟩ : syracuseStep 2555885 = 958457) (by norm_num)
theorem B3833837 : Blo 1703552 3833837 := bbase (se 3 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 3833837 = 1437689) (by norm_num)
theorem B1703939 : Blo 1703552 1703939 := bstep (se 1 (by rfl) ⟨1277954, by rfl⟩ : syracuseStep 1703939 = 2555909) B2555909
theorem B9707525 : Blo 1703552 9707525 := bstep (se 4 (by rfl) ⟨910080, by rfl⟩ : syracuseStep 9707525 = 1820161) B1820161
theorem B3833873 : Blo 1703552 3833873 := bstep (se 2 (by rfl) ⟨1437702, by rfl⟩ : syracuseStep 3833873 = 2875405) B2875405
theorem B2555921 : Blo 1703552 2555921 := bstep (se 2 (by rfl) ⟨958470, by rfl⟩ : syracuseStep 2555921 = 1916941) B1916941
theorem B1703955 : Blo 1703552 1703955 := bstep (se 1 (by rfl) ⟨1277966, by rfl⟩ : syracuseStep 1703955 = 2555933) B2555933
theorem B3833891 : Blo 1703552 3833891 := bstep (se 1 (by rfl) ⟨2875418, by rfl⟩ : syracuseStep 3833891 = 5750837) B5750837
theorem B2555939 : Blo 1703552 2555939 := bstep (se 1 (by rfl) ⟨1916954, by rfl⟩ : syracuseStep 2555939 = 3833909) B3833909
theorem B1703971 : Blo 1703552 1703971 := bstep (se 1 (by rfl) ⟨1277978, by rfl⟩ : syracuseStep 1703971 = 2555957) B2555957
theorem B5832749 : Blo 1703552 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B1703987 : Blo 1703552 1703987 := bstep (se 1 (by rfl) ⟨1277990, by rfl⟩ : syracuseStep 1703987 = 2555981) B2555981
theorem B2555969 : Blo 1703552 2555969 := bstep (se 2 (by rfl) ⟨958488, by rfl⟩ : syracuseStep 2555969 = 1916977) B1916977
theorem B2875459 : Blo 1703552 2875459 := bstep (se 1 (by rfl) ⟨2156594, by rfl⟩ : syracuseStep 2875459 = 4313189) B4313189
theorem B1916995 : Blo 1703552 1916995 := bstep (se 1 (by rfl) ⟨1437746, by rfl⟩ : syracuseStep 1916995 = 2875493) B2875493
theorem B1704003 : Blo 1703552 1704003 := bstep (se 1 (by rfl) ⟨1278002, by rfl⟩ : syracuseStep 1704003 = 2556005) B2556005
theorem B2555987 : Blo 1703552 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B1704019 : Blo 1703552 1704019 := bstep (se 1 (by rfl) ⟨1278014, by rfl⟩ : syracuseStep 1704019 = 2556029) B2556029
theorem B1704035 : Blo 1703552 1704035 := bstep (se 1 (by rfl) ⟨1278026, by rfl⟩ : syracuseStep 1704035 = 2556053) B2556053
theorem B2556017 : Blo 1703552 2556017 := bstep (se 2 (by rfl) ⟨958506, by rfl⟩ : syracuseStep 2556017 = 1917013) B1917013
theorem B1704051 : Blo 1703552 1704051 := bstep (se 1 (by rfl) ⟨1278038, by rfl⟩ : syracuseStep 1704051 = 2556077) B2556077
theorem B2556035 : Blo 1703552 2556035 := bstep (se 1 (by rfl) ⟨1917026, by rfl⟩ : syracuseStep 2556035 = 3834053) B3834053
theorem B1704067 : Blo 1703552 1704067 := bstep (se 1 (by rfl) ⟨1278050, by rfl⟩ : syracuseStep 1704067 = 2556101) B2556101
theorem B1704083 : Blo 1703552 1704083 := bstep (se 1 (by rfl) ⟨1278062, by rfl⟩ : syracuseStep 1704083 = 2556125) B2556125
theorem B2556065 : Blo 1703552 2556065 := bstep (se 2 (by rfl) ⟨958524, by rfl⟩ : syracuseStep 2556065 = 1917049) B1917049
theorem B1704099 : Blo 1703552 1704099 := bstep (se 1 (by rfl) ⟨1278074, by rfl⟩ : syracuseStep 1704099 = 2556149) B2556149
theorem B3072163 : Blo 1703552 3072163 := bstep (se 1 (by rfl) ⟨2304122, by rfl⟩ : syracuseStep 3072163 = 4608245) B4608245
theorem B2556083 : Blo 1703552 2556083 := bstep (se 1 (by rfl) ⟨1917062, by rfl⟩ : syracuseStep 2556083 = 3834125) B3834125
theorem B1704115 : Blo 1703552 1704115 := bstep (se 1 (by rfl) ⟨1278086, by rfl⟩ : syracuseStep 1704115 = 2556173) B2556173
theorem B1704131 : Blo 1703552 1704131 := bstep (se 1 (by rfl) ⟨1278098, by rfl⟩ : syracuseStep 1704131 = 2556197) B2556197
theorem B10363085 : Blo 1703552 10363085 := bstep (se 3 (by rfl) ⟨1943078, by rfl⟩ : syracuseStep 10363085 = 3886157) B3886157
theorem B2875601 : Blo 1703552 2875601 := bstep (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) B2156701
theorem B2556113 : Blo 1703552 2556113 := bstep (se 2 (by rfl) ⟨958542, by rfl⟩ : syracuseStep 2556113 = 1917085) B1917085
theorem B1917139 : Blo 1703552 1917139 := bstep (se 1 (by rfl) ⟨1437854, by rfl⟩ : syracuseStep 1917139 = 2875709) B2875709
theorem B1704147 : Blo 1703552 1704147 := bstep (se 1 (by rfl) ⟨1278110, by rfl⟩ : syracuseStep 1704147 = 2556221) B2556221
theorem B2556131 : Blo 1703552 2556131 := bstep (se 1 (by rfl) ⟨1917098, by rfl⟩ : syracuseStep 2556131 = 3834197) B3834197
theorem B1704163 : Blo 1703552 1704163 := bstep (se 1 (by rfl) ⟨1278122, by rfl⟩ : syracuseStep 1704163 = 2556245) B2556245
theorem B1704179 : Blo 1703552 1704179 := bstep (se 1 (by rfl) ⟨1278134, by rfl⟩ : syracuseStep 1704179 = 2556269) B2556269
theorem B2556161 : Blo 1703552 2556161 := bstep (se 2 (by rfl) ⟨958560, by rfl⟩ : syracuseStep 2556161 = 1917121) B1917121
theorem B1704195 : Blo 1703552 1704195 := bstep (se 1 (by rfl) ⟨1278146, by rfl⟩ : syracuseStep 1704195 = 2556293) B2556293
theorem B5751053 : Blo 1703552 5751053 := bstep (se 3 (by rfl) ⟨1078322, by rfl⟩ : syracuseStep 5751053 = 2156645) B2156645
theorem B2556179 : Blo 1703552 2556179 := bstep (se 1 (by rfl) ⟨1917134, by rfl⟩ : syracuseStep 2556179 = 3834269) B3834269
theorem B1704211 : Blo 1703552 1704211 := bstep (se 1 (by rfl) ⟨1278158, by rfl⟩ : syracuseStep 1704211 = 2556317) B2556317
theorem B1704227 : Blo 1703552 1704227 := bstep (se 1 (by rfl) ⟨1278170, by rfl⟩ : syracuseStep 1704227 = 2556341) B2556341
theorem B6471971 : Blo 1703552 6471971 := bstep (se 1 (by rfl) ⟨4853978, by rfl⟩ : syracuseStep 6471971 = 9707957) B9707957
theorem B3834161 : Blo 1703552 3834161 := bstep (se 2 (by rfl) ⟨1437810, by rfl⟩ : syracuseStep 3834161 = 2875621) B2875621
theorem B2556209 : Blo 1703552 2556209 := bstep (se 2 (by rfl) ⟨958578, by rfl⟩ : syracuseStep 2556209 = 1917157) B1917157
theorem B1704243 : Blo 1703552 1704243 := bstep (se 1 (by rfl) ⟨1278182, by rfl⟩ : syracuseStep 1704243 = 2556365) B2556365
theorem B5751107 : Blo 1703552 5751107 := bstep (se 1 (by rfl) ⟨4313330, by rfl⟩ : syracuseStep 5751107 = 8626661) B8626661
theorem B3834179 : Blo 1703552 3834179 := bstep (se 1 (by rfl) ⟨2875634, by rfl⟩ : syracuseStep 3834179 = 5751269) B5751269
theorem B2556227 : Blo 1703552 2556227 := bstep (se 1 (by rfl) ⟨1917170, by rfl⟩ : syracuseStep 2556227 = 3834341) B3834341
theorem B1704259 : Blo 1703552 1704259 := bstep (se 1 (by rfl) ⟨1278194, by rfl⟩ : syracuseStep 1704259 = 2556389) B2556389
theorem B2875729 : Blo 1703552 2875729 := bstep (se 2 (by rfl) ⟨1078398, by rfl⟩ : syracuseStep 2875729 = 2156797) B2156797
theorem B1704275 : Blo 1703552 1704275 := bstep (se 1 (by rfl) ⟨1278206, by rfl⟩ : syracuseStep 1704275 = 2556413) B2556413
theorem B2556257 : Blo 1703552 2556257 := bstep (se 2 (by rfl) ⟨958596, by rfl⟩ : syracuseStep 2556257 = 1917193) B1917193
theorem B1917283 : Blo 1703552 1917283 := bstep (se 1 (by rfl) ⟨1437962, by rfl⟩ : syracuseStep 1917283 = 2875925) B2875925
theorem B1704291 : Blo 1703552 1704291 := bstep (se 1 (by rfl) ⟨1278218, by rfl⟩ : syracuseStep 1704291 = 2556437) B2556437
theorem B2875763 : Blo 1703552 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B2556275 : Blo 1703552 2556275 := bstep (se 1 (by rfl) ⟨1917206, by rfl⟩ : syracuseStep 2556275 = 3834413) B3834413
theorem B1704307 : Blo 1703552 1704307 := bstep (se 1 (by rfl) ⟨1278230, by rfl⟩ : syracuseStep 1704307 = 2556461) B2556461
theorem B1704323 : Blo 1703552 1704323 := bstep (se 1 (by rfl) ⟨1278242, by rfl⟩ : syracuseStep 1704323 = 2556485) B2556485
theorem B2556305 : Blo 1703552 2556305 := bstep (se 2 (by rfl) ⟨958614, by rfl⟩ : syracuseStep 2556305 = 1917229) B1917229
theorem B1704339 : Blo 1703552 1704339 := bstep (se 1 (by rfl) ⟨1278254, by rfl⟩ : syracuseStep 1704339 = 2556509) B2556509
theorem B2556323 : Blo 1703552 2556323 := bstep (se 1 (by rfl) ⟨1917242, by rfl⟩ : syracuseStep 2556323 = 3834485) B3834485
theorem B1704355 : Blo 1703552 1704355 := bstep (se 1 (by rfl) ⟨1278266, by rfl⟩ : syracuseStep 1704355 = 2556533) B2556533
theorem B1704371 : Blo 1703552 1704371 := bstep (se 1 (by rfl) ⟨1278278, by rfl⟩ : syracuseStep 1704371 = 2556557) B2556557
theorem B2556353 : Blo 1703552 2556353 := bstep (se 2 (by rfl) ⟨958632, by rfl⟩ : syracuseStep 2556353 = 1917265) B1917265
theorem B1704387 : Blo 1703552 1704387 := bstep (se 1 (by rfl) ⟨1278290, by rfl⟩ : syracuseStep 1704387 = 2556581) B2556581
theorem B2556371 : Blo 1703552 2556371 := bstep (se 1 (by rfl) ⟨1917278, by rfl⟩ : syracuseStep 2556371 = 3834557) B3834557
theorem B1704403 : Blo 1703552 1704403 := bstep (se 1 (by rfl) ⟨1278302, by rfl⟩ : syracuseStep 1704403 = 2556605) B2556605
theorem B1704419 : Blo 1703552 1704419 := bstep (se 1 (by rfl) ⟨1278314, by rfl⟩ : syracuseStep 1704419 = 2556629) B2556629
theorem B2556401 : Blo 1703552 2556401 := bstep (se 2 (by rfl) ⟨958650, by rfl⟩ : syracuseStep 2556401 = 1917301) B1917301
theorem B2875891 : Blo 1703552 2875891 := bstep (se 1 (by rfl) ⟨2156918, by rfl⟩ : syracuseStep 2875891 = 4313837) B4313837
theorem B1917427 : Blo 1703552 1917427 := bstep (se 1 (by rfl) ⟨1438070, by rfl⟩ : syracuseStep 1917427 = 2876141) B2876141
theorem B1704435 : Blo 1703552 1704435 := bstep (se 1 (by rfl) ⟨1278326, by rfl⟩ : syracuseStep 1704435 = 2556653) B2556653
theorem B2556419 : Blo 1703552 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B1704451 : Blo 1703552 1704451 := bstep (se 1 (by rfl) ⟨1278338, by rfl⟩ : syracuseStep 1704451 = 2556677) B2556677
theorem B1704467 : Blo 1703552 1704467 := bstep (se 1 (by rfl) ⟨1278350, by rfl⟩ : syracuseStep 1704467 = 2556701) B2556701
theorem B2556449 : Blo 1703552 2556449 := bstep (se 2 (by rfl) ⟨958668, by rfl⟩ : syracuseStep 2556449 = 1917337) B1917337
theorem B1704483 : Blo 1703552 1704483 := bstep (se 1 (by rfl) ⟨1278362, by rfl⟩ : syracuseStep 1704483 = 2556725) B2556725
theorem B2556467 : Blo 1703552 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B1704499 : Blo 1703552 1704499 := bstep (se 1 (by rfl) ⟨1278374, by rfl⟩ : syracuseStep 1704499 = 2556749) B2556749
theorem B1704515 : Blo 1703552 1704515 := bstep (se 1 (by rfl) ⟨1278386, by rfl⟩ : syracuseStep 1704515 = 2556773) B2556773
theorem B14557765 : Blo 1703552 14557765 := bstep (se 4 (by rfl) ⟨1364790, by rfl⟩ : syracuseStep 14557765 = 2729581) B2729581
theorem B5751377 : Blo 1703552 5751377 := bstep (se 2 (by rfl) ⟨2156766, by rfl⟩ : syracuseStep 5751377 = 4313533) B4313533
theorem B3834449 : Blo 1703552 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B2556497 : Blo 1703552 2556497 := bstep (se 2 (by rfl) ⟨958686, by rfl⟩ : syracuseStep 2556497 = 1917373) B1917373
theorem B1704531 : Blo 1703552 1704531 := bstep (se 1 (by rfl) ⟨1278398, by rfl⟩ : syracuseStep 1704531 = 2556797) B2556797
theorem B3834467 : Blo 1703552 3834467 := bstep (se 1 (by rfl) ⟨2875850, by rfl⟩ : syracuseStep 3834467 = 5751701) B5751701
theorem B2556515 : Blo 1703552 2556515 := bstep (se 1 (by rfl) ⟨1917386, by rfl⟩ : syracuseStep 2556515 = 3834773) B3834773
theorem B1704547 : Blo 1703552 1704547 := bstep (se 1 (by rfl) ⟨1278410, by rfl⟩ : syracuseStep 1704547 = 2556821) B2556821
theorem B1704563 : Blo 1703552 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B2876033 : Blo 1703552 2876033 := bstep (se 2 (by rfl) ⟨1078512, by rfl⟩ : syracuseStep 2876033 = 2157025) B2157025
theorem B2556545 : Blo 1703552 2556545 := bstep (se 2 (by rfl) ⟨958704, by rfl⟩ : syracuseStep 2556545 = 1917409) B1917409
theorem B1917571 : Blo 1703552 1917571 := bstep (se 1 (by rfl) ⟨1438178, by rfl⟩ : syracuseStep 1917571 = 2876357) B2876357
theorem B1704579 : Blo 1703552 1704579 := bstep (se 1 (by rfl) ⟨1278434, by rfl⟩ : syracuseStep 1704579 = 2556869) B2556869
theorem B10920581 : Blo 1703552 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B2556563 : Blo 1703552 2556563 := bstep (se 1 (by rfl) ⟨1917422, by rfl⟩ : syracuseStep 2556563 = 3834845) B3834845
theorem B1704595 : Blo 1703552 1704595 := bstep (se 1 (by rfl) ⟨1278446, by rfl⟩ : syracuseStep 1704595 = 2556893) B2556893
theorem B1704611 : Blo 1703552 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B2556593 : Blo 1703552 2556593 := bstep (se 2 (by rfl) ⟨958722, by rfl⟩ : syracuseStep 2556593 = 1917445) B1917445
theorem B1704627 : Blo 1703552 1704627 := bstep (se 1 (by rfl) ⟨1278470, by rfl⟩ : syracuseStep 1704627 = 2556941) B2556941
theorem B2556611 : Blo 1703552 2556611 := bstep (se 1 (by rfl) ⟨1917458, by rfl⟩ : syracuseStep 2556611 = 3834917) B3834917
theorem B1704643 : Blo 1703552 1704643 := bstep (se 1 (by rfl) ⟨1278482, by rfl⟩ : syracuseStep 1704643 = 2556965) B2556965
theorem B1704659 : Blo 1703552 1704659 := bstep (se 1 (by rfl) ⟨1278494, by rfl⟩ : syracuseStep 1704659 = 2556989) B2556989
theorem B2556641 : Blo 1703552 2556641 := bstep (se 2 (by rfl) ⟨958740, by rfl⟩ : syracuseStep 2556641 = 1917481) B1917481
theorem B1704675 : Blo 1703552 1704675 := bstep (se 1 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 1704675 = 2557013) B2557013
theorem B3236593 : Blo 1703552 3236593 := bstep (se 2 (by rfl) ⟨1213722, by rfl⟩ : syracuseStep 3236593 = 2427445) B2427445
theorem B1819379 : Blo 1703552 1819379 := bstep (se 1 (by rfl) ⟨1364534, by rfl⟩ : syracuseStep 1819379 = 2729069) B2729069
theorem B2556659 : Blo 1703552 2556659 := bstep (se 1 (by rfl) ⟨1917494, by rfl⟩ : syracuseStep 2556659 = 3834989) B3834989
theorem B1704691 : Blo 1703552 1704691 := bstep (se 1 (by rfl) ⟨1278518, by rfl⟩ : syracuseStep 1704691 = 2557037) B2557037
theorem B2876161 : Blo 1703552 2876161 := bstep (se 2 (by rfl) ⟨1078560, by rfl⟩ : syracuseStep 2876161 = 2157121) B2157121
theorem B1704707 : Blo 1703552 1704707 := bstep (se 1 (by rfl) ⟨1278530, by rfl⟩ : syracuseStep 1704707 = 2557061) B2557061
theorem B2556689 : Blo 1703552 2556689 := bstep (se 2 (by rfl) ⟨958758, by rfl⟩ : syracuseStep 2556689 = 1917517) B1917517
theorem B1917715 : Blo 1703552 1917715 := bstep (se 1 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 1917715 = 2876573) B2876573
theorem B1704723 : Blo 1703552 1704723 := bstep (se 1 (by rfl) ⟨1278542, by rfl⟩ : syracuseStep 1704723 = 2557085) B2557085
theorem B2876195 : Blo 1703552 2876195 := bstep (se 1 (by rfl) ⟨2157146, by rfl⟩ : syracuseStep 2876195 = 4314293) B4314293
theorem B2556707 : Blo 1703552 2556707 := bstep (se 1 (by rfl) ⟨1917530, by rfl⟩ : syracuseStep 2556707 = 3835061) B3835061
theorem B1704739 : Blo 1703552 1704739 := bstep (se 1 (by rfl) ⟨1278554, by rfl⟩ : syracuseStep 1704739 = 2557109) B2557109
theorem B1704755 : Blo 1703552 1704755 := bstep (se 1 (by rfl) ⟨1278566, by rfl⟩ : syracuseStep 1704755 = 2557133) B2557133
theorem B2556737 : Blo 1703552 2556737 := bstep (se 2 (by rfl) ⟨958776, by rfl⟩ : syracuseStep 2556737 = 1917553) B1917553
theorem B1704771 : Blo 1703552 1704771 := bstep (se 1 (by rfl) ⟨1278578, by rfl⟩ : syracuseStep 1704771 = 2557157) B2557157
theorem B2556755 : Blo 1703552 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B1704787 : Blo 1703552 1704787 := bstep (se 1 (by rfl) ⟨1278590, by rfl⟩ : syracuseStep 1704787 = 2557181) B2557181
theorem B1704803 : Blo 1703552 1704803 := bstep (se 1 (by rfl) ⟨1278602, by rfl⟩ : syracuseStep 1704803 = 2557205) B2557205
theorem B3834737 : Blo 1703552 3834737 := bstep (se 2 (by rfl) ⟨1438026, by rfl⟩ : syracuseStep 3834737 = 2876053) B2876053
theorem B2556785 : Blo 1703552 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B1704819 : Blo 1703552 1704819 := bstep (se 1 (by rfl) ⟨1278614, by rfl⟩ : syracuseStep 1704819 = 2557229) B2557229
theorem B3834755 : Blo 1703552 3834755 := bstep (se 1 (by rfl) ⟨2876066, by rfl⟩ : syracuseStep 3834755 = 5752133) B5752133
theorem B2556803 : Blo 1703552 2556803 := bstep (se 1 (by rfl) ⟨1917602, by rfl⟩ : syracuseStep 2556803 = 3835205) B3835205
theorem B1704835 : Blo 1703552 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B1704851 : Blo 1703552 1704851 := bstep (se 1 (by rfl) ⟨1278638, by rfl⟩ : syracuseStep 1704851 = 2557277) B2557277
theorem B3236753 : Blo 1703552 3236753 := bstep (se 2 (by rfl) ⟨1213782, by rfl⟩ : syracuseStep 3236753 = 2427565) B2427565
theorem B2556833 : Blo 1703552 2556833 := bstep (se 2 (by rfl) ⟨958812, by rfl⟩ : syracuseStep 2556833 = 1917625) B1917625
theorem B2876323 : Blo 1703552 2876323 := bstep (se 1 (by rfl) ⟨2157242, by rfl⟩ : syracuseStep 2876323 = 4314485) B4314485
theorem B1917859 : Blo 1703552 1917859 := bstep (se 1 (by rfl) ⟨1438394, by rfl⟩ : syracuseStep 1917859 = 2876789) B2876789
theorem B1704867 : Blo 1703552 1704867 := bstep (se 1 (by rfl) ⟨1278650, by rfl⟩ : syracuseStep 1704867 = 2557301) B2557301
theorem B2556851 : Blo 1703552 2556851 := bstep (se 1 (by rfl) ⟨1917638, by rfl⟩ : syracuseStep 2556851 = 3835277) B3835277
theorem B1704883 : Blo 1703552 1704883 := bstep (se 1 (by rfl) ⟨1278662, by rfl⟩ : syracuseStep 1704883 = 2557325) B2557325
theorem B2425793 : Blo 1703552 2425793 := bstep (se 2 (by rfl) ⟨909672, by rfl⟩ : syracuseStep 2425793 = 1819345) B1819345
theorem B1704899 : Blo 1703552 1704899 := bstep (se 1 (by rfl) ⟨1278674, by rfl⟩ : syracuseStep 1704899 = 2557349) B2557349
theorem B2556881 : Blo 1703552 2556881 := bstep (se 2 (by rfl) ⟨958830, by rfl⟩ : syracuseStep 2556881 = 1917661) B1917661
theorem B1704915 : Blo 1703552 1704915 := bstep (se 1 (by rfl) ⟨1278686, by rfl⟩ : syracuseStep 1704915 = 2557373) B2557373
theorem B2556899 : Blo 1703552 2556899 := bstep (se 1 (by rfl) ⟨1917674, by rfl⟩ : syracuseStep 2556899 = 3835349) B3835349
theorem B1704931 : Blo 1703552 1704931 := bstep (se 1 (by rfl) ⟨1278698, by rfl⟩ : syracuseStep 1704931 = 2557397) B2557397
theorem B1704947 : Blo 1703552 1704947 := bstep (se 1 (by rfl) ⟨1278710, by rfl⟩ : syracuseStep 1704947 = 2557421) B2557421
theorem B2728961 : Blo 1703552 2728961 := bstep (se 2 (by rfl) ⟨1023360, by rfl⟩ : syracuseStep 2728961 = 2046721) B2046721
theorem B2556929 : Blo 1703552 2556929 := bstep (se 2 (by rfl) ⟨958848, by rfl⟩ : syracuseStep 2556929 = 1917697) B1917697
theorem B1704963 : Blo 1703552 1704963 := bstep (se 1 (by rfl) ⟨1278722, by rfl⟩ : syracuseStep 1704963 = 2557445) B2557445
theorem B2556947 : Blo 1703552 2556947 := bstep (se 1 (by rfl) ⟨1917710, by rfl⟩ : syracuseStep 2556947 = 3835421) B3835421
theorem B1704979 : Blo 1703552 1704979 := bstep (se 1 (by rfl) ⟨1278734, by rfl⟩ : syracuseStep 1704979 = 2557469) B2557469
theorem B1704995 : Blo 1703552 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B2876465 : Blo 1703552 2876465 := bstep (se 2 (by rfl) ⟨1078674, by rfl⟩ : syracuseStep 2876465 = 2157349) B2157349
theorem B2556977 : Blo 1703552 2556977 := bstep (se 2 (by rfl) ⟨958866, by rfl⟩ : syracuseStep 2556977 = 1917733) B1917733
theorem B2425907 : Blo 1703552 2425907 := bstep (se 1 (by rfl) ⟨1819430, by rfl⟩ : syracuseStep 2425907 = 3638861) B3638861
theorem B1918003 : Blo 1703552 1918003 := bstep (se 1 (by rfl) ⟨1438502, by rfl⟩ : syracuseStep 1918003 = 2877005) B2877005
theorem B1705011 : Blo 1703552 1705011 := bstep (se 1 (by rfl) ⟨1278758, by rfl⟩ : syracuseStep 1705011 = 2557517) B2557517
theorem B2556995 : Blo 1703552 2556995 := bstep (se 1 (by rfl) ⟨1917746, by rfl⟩ : syracuseStep 2556995 = 3835493) B3835493
theorem B1705027 : Blo 1703552 1705027 := bstep (se 1 (by rfl) ⟨1278770, by rfl⟩ : syracuseStep 1705027 = 2557541) B2557541
theorem B1705043 : Blo 1703552 1705043 := bstep (se 1 (by rfl) ⟨1278782, by rfl⟩ : syracuseStep 1705043 = 2557565) B2557565
theorem B2557025 : Blo 1703552 2557025 := bstep (se 2 (by rfl) ⟨958884, by rfl⟩ : syracuseStep 2557025 = 1917769) B1917769
theorem B5751917 : Blo 1703552 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B2557043 : Blo 1703552 2557043 := bstep (se 1 (by rfl) ⟨1917782, by rfl⟩ : syracuseStep 2557043 = 3835565) B3835565
theorem B2425987 : Blo 1703552 2425987 := bstep (se 1 (by rfl) ⟨1819490, by rfl⟩ : syracuseStep 2425987 = 3638981) B3638981
theorem B3835025 : Blo 1703552 3835025 := bstep (se 2 (by rfl) ⟨1438134, by rfl⟩ : syracuseStep 3835025 = 2876269) B2876269
theorem B2557073 : Blo 1703552 2557073 := bstep (se 2 (by rfl) ⟨958902, by rfl⟩ : syracuseStep 2557073 = 1917805) B1917805
theorem B5751971 : Blo 1703552 5751971 := bstep (se 1 (by rfl) ⟨4313978, by rfl⟩ : syracuseStep 5751971 = 8627957) B8627957
theorem B3835043 : Blo 1703552 3835043 := bstep (se 1 (by rfl) ⟨2876282, by rfl⟩ : syracuseStep 3835043 = 5752565) B5752565
theorem B2557091 : Blo 1703552 2557091 := bstep (se 1 (by rfl) ⟨1917818, by rfl⟩ : syracuseStep 2557091 = 3835637) B3835637
theorem B2876593 : Blo 1703552 2876593 := bstep (se 2 (by rfl) ⟨1078722, by rfl⟩ : syracuseStep 2876593 = 2157445) B2157445
theorem B2557121 : Blo 1703552 2557121 := bstep (se 2 (by rfl) ⟨958920, by rfl⟩ : syracuseStep 2557121 = 1917841) B1917841
theorem B1918147 : Blo 1703552 1918147 := bstep (se 1 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 1918147 = 2877221) B2877221
theorem B2729171 : Blo 1703552 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B2876627 : Blo 1703552 2876627 := bstep (se 1 (by rfl) ⟨2157470, by rfl⟩ : syracuseStep 2876627 = 4314941) B4314941
theorem B2557139 : Blo 1703552 2557139 := bstep (se 1 (by rfl) ⟨1917854, by rfl⟩ : syracuseStep 2557139 = 3835709) B3835709
theorem B2557169 : Blo 1703552 2557169 := bstep (se 2 (by rfl) ⟨958938, by rfl⟩ : syracuseStep 2557169 = 1917877) B1917877
theorem B2557187 : Blo 1703552 2557187 := bstep (se 1 (by rfl) ⟨1917890, by rfl⟩ : syracuseStep 2557187 = 3835781) B3835781
theorem B5907725 : Blo 1703552 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B6472973 : Blo 1703552 6472973 := bstep (se 3 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 6472973 = 2427365) B2427365
theorem B2557217 : Blo 1703552 2557217 := bstep (se 2 (by rfl) ⟨958956, by rfl⟩ : syracuseStep 2557217 = 1917913) B1917913
theorem B2557235 : Blo 1703552 2557235 := bstep (se 1 (by rfl) ⟨1917926, by rfl⟩ : syracuseStep 2557235 = 3835853) B3835853
theorem B2557265 : Blo 1703552 2557265 := bstep (se 2 (by rfl) ⟨958974, by rfl⟩ : syracuseStep 2557265 = 1917949) B1917949
theorem B2876755 : Blo 1703552 2876755 := bstep (se 1 (by rfl) ⟨2157566, by rfl⟩ : syracuseStep 2876755 = 4315133) B4315133
theorem B2557283 : Blo 1703552 2557283 := bstep (se 1 (by rfl) ⟨1917962, by rfl⟩ : syracuseStep 2557283 = 3835925) B3835925
theorem B9971057 : Blo 1703552 9971057 := bstep (se 2 (by rfl) ⟨3739146, by rfl⟩ : syracuseStep 9971057 = 7478293) B7478293
theorem B2557313 : Blo 1703552 2557313 := bstep (se 2 (by rfl) ⟨958992, by rfl⟩ : syracuseStep 2557313 = 1917985) B1917985
theorem B3114371 : Blo 1703552 3114371 := bstep (se 1 (by rfl) ⟨2335778, by rfl⟩ : syracuseStep 3114371 = 4671557) B4671557
theorem B2557331 : Blo 1703552 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B8627633 : Blo 1703552 8627633 := bstep (se 2 (by rfl) ⟨3235362, by rfl⟩ : syracuseStep 8627633 = 6470725) B6470725
theorem B5752241 : Blo 1703552 5752241 := bstep (se 2 (by rfl) ⟨2157090, by rfl⟩ : syracuseStep 5752241 = 4314181) B4314181
theorem B3835313 : Blo 1703552 3835313 := bstep (se 2 (by rfl) ⟨1438242, by rfl⟩ : syracuseStep 3835313 = 2876485) B2876485
theorem B2557361 : Blo 1703552 2557361 := bstep (se 2 (by rfl) ⟨959010, by rfl⟩ : syracuseStep 2557361 = 1918021) B1918021
theorem B3835331 : Blo 1703552 3835331 := bstep (se 1 (by rfl) ⟨2876498, by rfl⟩ : syracuseStep 3835331 = 5752997) B5752997
theorem B2557379 : Blo 1703552 2557379 := bstep (se 1 (by rfl) ⟨1918034, by rfl⟩ : syracuseStep 2557379 = 3836069) B3836069
theorem B2876897 : Blo 1703552 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B2557409 : Blo 1703552 2557409 := bstep (se 2 (by rfl) ⟨959028, by rfl⟩ : syracuseStep 2557409 = 1918057) B1918057
theorem B2557427 : Blo 1703552 2557427 := bstep (se 1 (by rfl) ⟨1918070, by rfl⟩ : syracuseStep 2557427 = 3836141) B3836141
theorem B2557457 : Blo 1703552 2557457 := bstep (se 2 (by rfl) ⟨959046, by rfl⟩ : syracuseStep 2557457 = 1918093) B1918093
theorem B3638819 : Blo 1703552 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B2557475 : Blo 1703552 2557475 := bstep (se 1 (by rfl) ⟨1918106, by rfl⟩ : syracuseStep 2557475 = 3836213) B3836213
theorem B4851245 : Blo 1703552 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B2557505 : Blo 1703552 2557505 := bstep (se 2 (by rfl) ⟨959064, by rfl⟩ : syracuseStep 2557505 = 1918129) B1918129
theorem B2557523 : Blo 1703552 2557523 := bstep (se 1 (by rfl) ⟨1918142, by rfl⟩ : syracuseStep 2557523 = 3836285) B3836285
theorem B2877025 : Blo 1703552 2877025 := bstep (se 2 (by rfl) ⟨1078884, by rfl⟩ : syracuseStep 2877025 = 2157769) B2157769
theorem B2557553 : Blo 1703552 2557553 := bstep (se 2 (by rfl) ⟨959082, by rfl⟩ : syracuseStep 2557553 = 1918165) B1918165
theorem B2303603 : Blo 1703552 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B2877059 : Blo 1703552 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B2557571 : Blo 1703552 2557571 := bstep (se 1 (by rfl) ⟨1918178, by rfl⟩ : syracuseStep 2557571 = 3836357) B3836357
theorem B2426545 : Blo 1703552 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B5457613 : Blo 1703552 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B3835601 : Blo 1703552 3835601 := bstep (se 2 (by rfl) ⟨1438350, by rfl⟩ : syracuseStep 3835601 = 2876701) B2876701
theorem B1844947 : Blo 1703552 1844947 := bstep (se 1 (by rfl) ⟨1383710, by rfl⟩ : syracuseStep 1844947 = 2767421) B2767421
theorem B4851427 : Blo 1703552 4851427 := bstep (se 1 (by rfl) ⟨3638570, by rfl⟩ : syracuseStep 4851427 = 7277141) B7277141
theorem B3835619 : Blo 1703552 3835619 := bstep (se 1 (by rfl) ⟨2876714, by rfl⟩ : syracuseStep 3835619 = 5753429) B5753429
theorem B2877187 : Blo 1703552 2877187 := bstep (se 1 (by rfl) ⟨2157890, by rfl⟩ : syracuseStep 2877187 = 4315781) B4315781
theorem B2156483 : Blo 1703552 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B4671427 : Blo 1703552 4671427 := bstep (se 1 (by rfl) ⟨3503570, by rfl⟩ : syracuseStep 4671427 = 7007141) B7007141
theorem B5752781 : Blo 1703552 5752781 := bstep (se 3 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 5752781 = 2157293) B2157293
theorem B2729953 : Blo 1703552 2729953 := bstep (se 2 (by rfl) ⟨1023732, by rfl⟩ : syracuseStep 2729953 = 2047465) B2047465
theorem B3835889 : Blo 1703552 3835889 := bstep (se 2 (by rfl) ⟨1438458, by rfl⟩ : syracuseStep 3835889 = 2876917) B2876917
theorem B5752835 : Blo 1703552 5752835 := bstep (se 1 (by rfl) ⟨4314626, by rfl⟩ : syracuseStep 5752835 = 8629253) B8629253
theorem B3835907 : Blo 1703552 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B4605997 : Blo 1703552 4605997 := bstep (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) B1727249
theorem B1820755 : Blo 1703552 1820755 := bstep (se 1 (by rfl) ⟨1365566, by rfl⟩ : syracuseStep 1820755 = 2731133) B2731133
theorem B2590849 : Blo 1703552 2590849 := bstep (se 2 (by rfl) ⟨971568, by rfl⟩ : syracuseStep 2590849 = 1943137) B1943137
theorem B655591637 : Blo 1703552 655591637 := bstep (se 7 (by rfl) ⟨7682714, by rfl⟩ : syracuseStep 655591637 = 15365429) B15365429
theorem B5753105 : Blo 1703552 5753105 := bstep (se 2 (by rfl) ⟨2157414, by rfl⟩ : syracuseStep 5753105 = 4314829) B4314829
theorem B3836177 : Blo 1703552 3836177 := bstep (se 2 (by rfl) ⟨1438566, by rfl⟩ : syracuseStep 3836177 = 2877133) B2877133
theorem B3836195 : Blo 1703552 3836195 := bstep (se 1 (by rfl) ⟨2877146, by rfl⟩ : syracuseStep 3836195 = 5754293) B5754293
theorem B2427251 : Blo 1703552 2427251 := bstep (se 1 (by rfl) ⟨1820438, by rfl⟩ : syracuseStep 2427251 = 3640877) B3640877
theorem B5458445 : Blo 1703552 5458445 := bstep (se 3 (by rfl) ⟨1023458, by rfl⟩ : syracuseStep 5458445 = 2046917) B2046917
theorem B2157187 : Blo 1703552 2157187 := bstep (se 1 (by rfl) ⟨1617890, by rfl⟩ : syracuseStep 2157187 = 3235781) B3235781
theorem B2157283 : Blo 1703552 2157283 := bstep (se 1 (by rfl) ⟨1617962, by rfl⟩ : syracuseStep 2157283 = 3235925) B3235925
theorem B3640049 : Blo 1703552 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B2730755 : Blo 1703552 2730755 := bstep (se 1 (by rfl) ⟨2048066, by rfl⟩ : syracuseStep 2730755 = 4096133) B4096133
theorem B5753645 : Blo 1703552 5753645 := bstep (se 3 (by rfl) ⟨1078808, by rfl⟩ : syracuseStep 5753645 = 2157617) B2157617
theorem B8629091 : Blo 1703552 8629091 := bstep (se 1 (by rfl) ⟨6471818, by rfl⟩ : syracuseStep 8629091 = 12943637) B12943637
theorem B5753699 : Blo 1703552 5753699 := bstep (se 1 (by rfl) ⟨4315274, by rfl⟩ : syracuseStep 5753699 = 8630549) B8630549
theorem B3886019 : Blo 1703552 3886019 := bstep (se 1 (by rfl) ⟨2914514, by rfl⟩ : syracuseStep 3886019 = 5829029) B5829029
theorem B84020165 : Blo 1703552 84020165 := bstep (se 4 (by rfl) ⟨7876890, by rfl⟩ : syracuseStep 84020165 = 15753781) B15753781
theorem B4852817 : Blo 1703552 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B199298161 : Blo 1703552 199298161 := bstep (se 2 (by rfl) ⟨74736810, by rfl⟩ : syracuseStep 199298161 = 149473621) B149473621
theorem B5753969 : Blo 1703552 5753969 := bstep (se 2 (by rfl) ⟨2157738, by rfl⟩ : syracuseStep 5753969 = 4315477) B4315477
theorem B7777421 : Blo 1703552 7777421 := bstep (se 3 (by rfl) ⟨1458266, by rfl⟩ : syracuseStep 7777421 = 2916533) B2916533
theorem B2591939 : Blo 1703552 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B2157779 : Blo 1703552 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B4918637 : Blo 1703552 4918637 := bstep (se 3 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 4918637 = 1844489) B1844489
theorem B10915249 : Blo 1703552 10915249 := bstep (se 2 (by rfl) ⟨4093218, by rfl⟩ : syracuseStep 10915249 = 8186437) B8186437
theorem B16379333 : Blo 1703552 16379333 := bstep (se 4 (by rfl) ⟨1535562, by rfl⟩ : syracuseStep 16379333 = 3071125) B3071125
theorem B4312561 : Blo 1703552 4312561 := bstep (se 2 (by rfl) ⟨1617210, by rfl⟩ : syracuseStep 4312561 = 3234421) B3234421
theorem B3280483 : Blo 1703552 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B3640945 : Blo 1703552 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B3640963 : Blo 1703552 3640963 := bstep (se 1 (by rfl) ⟨2730722, by rfl⟩ : syracuseStep 3640963 = 5461445) B5461445
theorem B8629901 : Blo 1703552 8629901 := bstep (se 3 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 8629901 = 3236213) B3236213
theorem B5754509 : Blo 1703552 5754509 := bstep (se 3 (by rfl) ⟨1078970, by rfl⟩ : syracuseStep 5754509 = 2157941) B2157941
theorem B8744689 : Blo 1703552 8744689 := bstep (se 2 (by rfl) ⟨3279258, by rfl⟩ : syracuseStep 8744689 = 6558517) B6558517
theorem B4312835 : Blo 1703552 4312835 := bstep (se 1 (by rfl) ⟨3234626, by rfl⟩ : syracuseStep 4312835 = 6469253) B6469253
theorem B4313027 : Blo 1703552 4313027 := bstep (se 1 (by rfl) ⟨3234770, by rfl⟩ : syracuseStep 4313027 = 6469541) B6469541
theorem B4861937 : Blo 1703552 4861937 := bstep (se 2 (by rfl) ⟨1823226, by rfl⟩ : syracuseStep 4861937 = 3646453) B3646453
theorem B23318513 : Blo 1703552 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B4853773 : Blo 1703552 4853773 := bstep (se 3 (by rfl) ⟨910082, by rfl⟩ : syracuseStep 4853773 = 1820165) B1820165
theorem B12947525 : Blo 1703552 12947525 := bstep (se 4 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 12947525 = 2427661) B2427661
theorem B3887185 : Blo 1703552 3887185 := bstep (se 2 (by rfl) ⟨1457694, by rfl⟩ : syracuseStep 3887185 = 2915389) B2915389
theorem B4854001 : Blo 1703552 4854001 := bstep (se 2 (by rfl) ⟨1820250, by rfl⟩ : syracuseStep 4854001 = 3640501) B3640501
theorem B8302961 : Blo 1703552 8302961 := bstep (se 2 (by rfl) ⟨3113610, by rfl⟩ : syracuseStep 8302961 = 6227221) B6227221
theorem B4854161 : Blo 1703552 4854161 := bstep (se 2 (by rfl) ⟨1820310, by rfl⟩ : syracuseStep 4854161 = 3640621) B3640621
theorem B5181869 : Blo 1703552 5181869 := bstep (se 3 (by rfl) ⟨971600, by rfl⟩ : syracuseStep 5181869 = 1943201) B1943201
theorem B4854275 : Blo 1703552 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B3895825 : Blo 1703552 3895825 := bstep (se 2 (by rfl) ⟨1460934, by rfl⟩ : syracuseStep 3895825 = 2921869) B2921869
theorem B2699795 : Blo 1703552 2699795 := bstep (se 1 (by rfl) ⟨2024846, by rfl⟩ : syracuseStep 2699795 = 4049693) B4049693
theorem B5460547 : Blo 1703552 5460547 := bstep (se 1 (by rfl) ⟨4095410, by rfl⟩ : syracuseStep 5460547 = 8190821) B8190821
theorem B5460689 : Blo 1703552 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B4150001 : Blo 1703552 4150001 := bstep (se 2 (by rfl) ⟨1556250, by rfl⟩ : syracuseStep 4150001 = 3112501) B3112501
theorem B19411811 : Blo 1703552 19411811 := bstep (se 1 (by rfl) ⟨14558858, by rfl⟩ : syracuseStep 19411811 = 29117717) B29117717
theorem B4313969 : Blo 1703552 4313969 := bstep (se 2 (by rfl) ⟨1617738, by rfl⟩ : syracuseStep 4313969 = 3235477) B3235477
theorem B21844849 : Blo 1703552 21844849 := bstep (se 2 (by rfl) ⟨8191818, by rfl⟩ : syracuseStep 21844849 = 16383637) B16383637
theorem B4314019 : Blo 1703552 4314019 := bstep (se 1 (by rfl) ⟨3235514, by rfl⟩ : syracuseStep 4314019 = 6471029) B6471029
theorem B2626561 : Blo 1703552 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B4314161 : Blo 1703552 4314161 := bstep (se 2 (by rfl) ⟨1617810, by rfl⟩ : syracuseStep 4314161 = 3235621) B3235621
theorem B6141041 : Blo 1703552 6141041 := bstep (se 2 (by rfl) ⟨2302890, by rfl⟩ : syracuseStep 6141041 = 4605781) B4605781
theorem B1996163 : Blo 1703552 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B4093411 : Blo 1703552 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B4855277 : Blo 1703552 4855277 := bstep (se 3 (by rfl) ⟨910364, by rfl⟩ : syracuseStep 4855277 = 1820729) B1820729
theorem B7280113 : Blo 1703552 7280113 := bstep (se 2 (by rfl) ⟨2730042, by rfl⟩ : syracuseStep 7280113 = 5460085) B5460085
theorem B3741457 : Blo 1703552 3741457 := bstep (se 2 (by rfl) ⟨1403046, by rfl⟩ : syracuseStep 3741457 = 2806093) B2806093
theorem B13817699 : Blo 1703552 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B4372337 : Blo 1703552 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B4315153 : Blo 1703552 4315153 := bstep (se 2 (by rfl) ⟨1618182, by rfl⟩ : syracuseStep 4315153 = 3236365) B3236365
theorem B9705541 : Blo 1703552 9705541 := bstep (se 4 (by rfl) ⟨909894, by rfl⟩ : syracuseStep 9705541 = 1819789) B1819789
theorem B2767025 : Blo 1703552 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B4315427 : Blo 1703552 4315427 := bstep (se 1 (by rfl) ⟨3236570, by rfl⟩ : syracuseStep 4315427 = 6473141) B6473141
theorem B4315619 : Blo 1703552 4315619 := bstep (se 1 (by rfl) ⟨3236714, by rfl⟩ : syracuseStep 4315619 = 6473429) B6473429
theorem B7879153 : Blo 1703552 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B18430517 : Blo 1703552 18430517 := bstep (se 5 (by rfl) ⟨863930, by rfl⟩ : syracuseStep 18430517 = 1727861) B1727861
theorem B8624717 : Blo 1703552 8624717 := bstep (se 3 (by rfl) ⟨1617134, by rfl⟩ : syracuseStep 8624717 = 3234269) B3234269
theorem B3234467 : Blo 1703552 3234467 := bstep (se 1 (by rfl) ⟨2425850, by rfl⟩ : syracuseStep 3234467 = 4851701) B4851701
theorem B4094641 : Blo 1703552 4094641 := bstep (se 2 (by rfl) ⟨1535490, by rfl⟩ : syracuseStep 4094641 = 3070981) B3070981
theorem B9837389 : Blo 1703552 9837389 := bstep (se 3 (by rfl) ⟨1844510, by rfl⟩ : syracuseStep 9837389 = 3689021) B3689021
theorem B12942179 : Blo 1703552 12942179 := bstep (se 1 (by rfl) ⟨9706634, by rfl⟩ : syracuseStep 12942179 = 19413269) B19413269
theorem B6470513 : Blo 1703552 6470513 := bstep (se 2 (by rfl) ⟨2426442, by rfl⟩ : syracuseStep 6470513 = 4852885) B4852885
theorem B2915185 : Blo 1703552 2915185 := bstep (se 2 (by rfl) ⟨1093194, by rfl⟩ : syracuseStep 2915185 = 2186389) B2186389
theorem B3791729 : Blo 1703552 3791729 := bstep (se 2 (by rfl) ⟨1421898, by rfl⟩ : syracuseStep 3791729 = 2843797) B2843797
theorem B5749649 : Blo 1703552 5749649 := bstep (se 2 (by rfl) ⟨2156118, by rfl⟩ : syracuseStep 5749649 = 4312237) B4312237
theorem B1727411 : Blo 1703552 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B3234755 : Blo 1703552 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B3833009 : Blo 1703552 3833009 := bstep (se 2 (by rfl) ⟨1437378, by rfl⟩ : syracuseStep 3833009 = 2874757) B2874757
theorem B3833027 : Blo 1703552 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B5750189 : Blo 1703552 5750189 := bstep (se 3 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 5750189 = 2156321) B2156321
theorem B2555345 : Blo 1703552 2555345 := bstep (se 2 (by rfl) ⟨958254, by rfl⟩ : syracuseStep 2555345 = 1916509) B1916509
theorem B3833297 : Blo 1703552 3833297 := bstep (se 2 (by rfl) ⟨1437486, by rfl⟩ : syracuseStep 3833297 = 2874973) B2874973
theorem B2555363 : Blo 1703552 2555363 := bstep (se 1 (by rfl) ⟨1916522, by rfl⟩ : syracuseStep 2555363 = 3833045) B3833045
theorem B3833315 : Blo 1703552 3833315 := bstep (se 1 (by rfl) ⟨2874986, by rfl⟩ : syracuseStep 3833315 = 5749973) B5749973
theorem B5750243 : Blo 1703552 5750243 := bstep (se 1 (by rfl) ⟨4312682, by rfl⟩ : syracuseStep 5750243 = 8625365) B8625365
theorem B2874865 : Blo 1703552 2874865 := bstep (se 2 (by rfl) ⟨1078074, by rfl⟩ : syracuseStep 2874865 = 2156149) B2156149
theorem B4734449 : Blo 1703552 4734449 := bstep (se 2 (by rfl) ⟨1775418, by rfl⟩ : syracuseStep 4734449 = 3550837) B3550837
theorem B2555393 : Blo 1703552 2555393 := bstep (se 2 (by rfl) ⟨958272, by rfl⟩ : syracuseStep 2555393 = 1916545) B1916545
theorem B2555411 : Blo 1703552 2555411 := bstep (se 1 (by rfl) ⟨1916558, by rfl⟩ : syracuseStep 2555411 = 3833117) B3833117
theorem B2874899 : Blo 1703552 2874899 := bstep (se 1 (by rfl) ⟨2156174, by rfl⟩ : syracuseStep 2874899 = 4312349) B4312349
theorem B2555441 : Blo 1703552 2555441 := bstep (se 2 (by rfl) ⟨958290, by rfl⟩ : syracuseStep 2555441 = 1916581) B1916581
theorem B2555459 : Blo 1703552 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B2555489 : Blo 1703552 2555489 := bstep (se 2 (by rfl) ⟨958308, by rfl⟩ : syracuseStep 2555489 = 1916617) B1916617
theorem B2555507 : Blo 1703552 2555507 := bstep (se 1 (by rfl) ⟨1916630, by rfl⟩ : syracuseStep 2555507 = 3833261) B3833261
theorem B1703555 : Blo 1703552 1703555 := bstep (se 1 (by rfl) ⟨1277666, by rfl⟩ : syracuseStep 1703555 = 2555333) B2555333
theorem B2047619 : Blo 1703552 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B2555537 : Blo 1703552 2555537 := bstep (se 2 (by rfl) ⟨958326, by rfl⟩ : syracuseStep 2555537 = 1916653) B1916653
theorem B1703571 : Blo 1703552 1703571 := bstep (se 1 (by rfl) ⟨1277678, by rfl⟩ : syracuseStep 1703571 = 2555357) B2555357
theorem B1916563 : Blo 1703552 1916563 := bstep (se 1 (by rfl) ⟨1437422, by rfl⟩ : syracuseStep 1916563 = 2874845) B2874845
theorem B2875027 : Blo 1703552 2875027 := bstep (se 1 (by rfl) ⟨2156270, by rfl⟩ : syracuseStep 2875027 = 4312541) B4312541
theorem B1703587 : Blo 1703552 1703587 := bstep (se 1 (by rfl) ⟨1277690, by rfl⟩ : syracuseStep 1703587 = 2555381) B2555381
theorem B2555555 : Blo 1703552 2555555 := bstep (se 1 (by rfl) ⟨1916666, by rfl⟩ : syracuseStep 2555555 = 3833333) B3833333
theorem B1703603 : Blo 1703552 1703603 := bstep (se 1 (by rfl) ⟨1277702, by rfl⟩ : syracuseStep 1703603 = 2555405) B2555405
theorem B2555585 : Blo 1703552 2555585 := bstep (se 2 (by rfl) ⟨958344, by rfl⟩ : syracuseStep 2555585 = 1916689) B1916689
theorem B1703619 : Blo 1703552 1703619 := bstep (se 1 (by rfl) ⟨1277714, by rfl⟩ : syracuseStep 1703619 = 2555429) B2555429
theorem B1703635 : Blo 1703552 1703635 := bstep (se 1 (by rfl) ⟨1277726, by rfl⟩ : syracuseStep 1703635 = 2555453) B2555453
theorem B2555603 : Blo 1703552 2555603 := bstep (se 1 (by rfl) ⟨1916702, by rfl⟩ : syracuseStep 2555603 = 3833405) B3833405
theorem B1703651 : Blo 1703552 1703651 := bstep (se 1 (by rfl) ⟨1277738, by rfl⟩ : syracuseStep 1703651 = 2555477) B2555477
theorem B2555633 : Blo 1703552 2555633 := bstep (se 2 (by rfl) ⟨958362, by rfl⟩ : syracuseStep 2555633 = 1916725) B1916725
theorem B3833585 : Blo 1703552 3833585 := bstep (se 2 (by rfl) ⟨1437594, by rfl⟩ : syracuseStep 3833585 = 2875189) B2875189
theorem B1703667 : Blo 1703552 1703667 := bstep (se 1 (by rfl) ⟨1277750, by rfl⟩ : syracuseStep 1703667 = 2555501) B2555501
theorem B5750513 : Blo 1703552 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B1703683 : Blo 1703552 1703683 := bstep (se 1 (by rfl) ⟨1277762, by rfl⟩ : syracuseStep 1703683 = 2555525) B2555525
theorem B2555651 : Blo 1703552 2555651 := bstep (se 1 (by rfl) ⟨1916738, by rfl⟩ : syracuseStep 2555651 = 3833477) B3833477
theorem B3833603 : Blo 1703552 3833603 := bstep (se 1 (by rfl) ⟨2875202, by rfl⟩ : syracuseStep 3833603 = 5750405) B5750405
theorem B1703699 : Blo 1703552 1703699 := bstep (se 1 (by rfl) ⟨1277774, by rfl⟩ : syracuseStep 1703699 = 2555549) B2555549
theorem B2555681 : Blo 1703552 2555681 := bstep (se 2 (by rfl) ⟨958380, by rfl⟩ : syracuseStep 2555681 = 1916761) B1916761
theorem B2875169 : Blo 1703552 2875169 := bstep (se 2 (by rfl) ⟨1078188, by rfl⟩ : syracuseStep 2875169 = 2156377) B2156377
theorem B1703715 : Blo 1703552 1703715 := bstep (se 1 (by rfl) ⟨1277786, by rfl⟩ : syracuseStep 1703715 = 2555573) B2555573
theorem B1916707 : Blo 1703552 1916707 := bstep (se 1 (by rfl) ⟨1437530, by rfl⟩ : syracuseStep 1916707 = 2875061) B2875061
theorem B6143779 : Blo 1703552 6143779 := bstep (se 1 (by rfl) ⟨4607834, by rfl⟩ : syracuseStep 6143779 = 9215669) B9215669
theorem B1703731 : Blo 1703552 1703731 := bstep (se 1 (by rfl) ⟨1277798, by rfl⟩ : syracuseStep 1703731 = 2555597) B2555597
theorem B2555699 : Blo 1703552 2555699 := bstep (se 1 (by rfl) ⟨1916774, by rfl⟩ : syracuseStep 2555699 = 3833549) B3833549
theorem B1703747 : Blo 1703552 1703747 := bstep (se 1 (by rfl) ⟨1277810, by rfl⟩ : syracuseStep 1703747 = 2555621) B2555621
theorem B2555729 : Blo 1703552 2555729 := bstep (se 2 (by rfl) ⟨958398, by rfl⟩ : syracuseStep 2555729 = 1916797) B1916797
theorem B1703763 : Blo 1703552 1703763 := bstep (se 1 (by rfl) ⟨1277822, by rfl⟩ : syracuseStep 1703763 = 2555645) B2555645
theorem B1703779 : Blo 1703552 1703779 := bstep (se 1 (by rfl) ⟨1277834, by rfl⟩ : syracuseStep 1703779 = 2555669) B2555669
theorem B2555747 : Blo 1703552 2555747 := bstep (se 1 (by rfl) ⟨1916810, by rfl⟩ : syracuseStep 2555747 = 3833621) B3833621
theorem B3235697 : Blo 1703552 3235697 := bstep (se 2 (by rfl) ⟨1213386, by rfl⟩ : syracuseStep 3235697 = 2426773) B2426773
theorem B1703795 : Blo 1703552 1703795 := bstep (se 1 (by rfl) ⟨1277846, by rfl⟩ : syracuseStep 1703795 = 2555693) B2555693
theorem B2916211 : Blo 1703552 2916211 := bstep (se 1 (by rfl) ⟨2187158, by rfl⟩ : syracuseStep 2916211 = 4374317) B4374317
theorem B2555777 : Blo 1703552 2555777 := bstep (se 2 (by rfl) ⟨958416, by rfl⟩ : syracuseStep 2555777 = 1916833) B1916833
theorem B1703811 : Blo 1703552 1703811 := bstep (se 1 (by rfl) ⟨1277858, by rfl⟩ : syracuseStep 1703811 = 2555717) B2555717
theorem B1703827 : Blo 1703552 1703827 := bstep (se 1 (by rfl) ⟨1277870, by rfl⟩ : syracuseStep 1703827 = 2555741) B2555741
theorem B2555795 : Blo 1703552 2555795 := bstep (se 1 (by rfl) ⟨1916846, by rfl⟩ : syracuseStep 2555795 = 3833693) B3833693
theorem B2875297 : Blo 1703552 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B1703843 : Blo 1703552 1703843 := bstep (se 1 (by rfl) ⟨1277882, by rfl⟩ : syracuseStep 1703843 = 2555765) B2555765
theorem B2555825 : Blo 1703552 2555825 := bstep (se 2 (by rfl) ⟨958434, by rfl⟩ : syracuseStep 2555825 = 1916869) B1916869
theorem B1703859 : Blo 1703552 1703859 := bstep (se 1 (by rfl) ⟨1277894, by rfl⟩ : syracuseStep 1703859 = 2555789) B2555789
theorem B1916851 : Blo 1703552 1916851 := bstep (se 1 (by rfl) ⟨1437638, by rfl⟩ : syracuseStep 1916851 = 2875277) B2875277
theorem B1703875 : Blo 1703552 1703875 := bstep (se 1 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 1703875 = 2555813) B2555813
theorem B2555843 : Blo 1703552 2555843 := bstep (se 1 (by rfl) ⟨1916882, by rfl⟩ : syracuseStep 2555843 = 3833765) B3833765
theorem B2875331 : Blo 1703552 2875331 := bstep (se 1 (by rfl) ⟨2156498, by rfl⟩ : syracuseStep 2875331 = 4312997) B4312997
theorem B4374481 : Blo 1703552 4374481 := bstep (se 2 (by rfl) ⟨1640430, by rfl⟩ : syracuseStep 4374481 = 3280861) B3280861
theorem B1703891 : Blo 1703552 1703891 := bstep (se 1 (by rfl) ⟨1277918, by rfl⟩ : syracuseStep 1703891 = 2555837) B2555837
theorem B2555873 : Blo 1703552 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B1703907 : Blo 1703552 1703907 := bstep (se 1 (by rfl) ⟨1277930, by rfl⟩ : syracuseStep 1703907 = 2555861) B2555861
theorem B1703923 : Blo 1703552 1703923 := bstep (se 1 (by rfl) ⟨1277942, by rfl⟩ : syracuseStep 1703923 = 2555885) B2555885
theorem B2555891 : Blo 1703552 2555891 := bstep (se 1 (by rfl) ⟨1916918, by rfl⟩ : syracuseStep 2555891 = 3833837) B3833837
theorem B6471683 : Blo 1703552 6471683 := bstep (se 1 (by rfl) ⟨4853762, by rfl⟩ : syracuseStep 6471683 = 9707525) B9707525
theorem B2555915 : Blo 1703552 2555915 := bstep (se 1 (by rfl) ⟨1916936, by rfl⟩ : syracuseStep 2555915 = 3833873) B3833873
theorem B1703947 : Blo 1703552 1703947 := bstep (se 1 (by rfl) ⟨1277960, by rfl⟩ : syracuseStep 1703947 = 2555921) B2555921
theorem B6471697 : Blo 1703552 6471697 := bstep (se 2 (by rfl) ⟨2426886, by rfl⟩ : syracuseStep 6471697 = 4853773) B4853773
theorem B2555927 : Blo 1703552 2555927 := bstep (se 1 (by rfl) ⟨1916945, by rfl⟩ : syracuseStep 2555927 = 3833891) B3833891
theorem B1703959 : Blo 1703552 1703959 := bstep (se 1 (by rfl) ⟨1277969, by rfl⟩ : syracuseStep 1703959 = 2555939) B2555939
theorem B1703979 : Blo 1703552 1703979 := bstep (se 1 (by rfl) ⟨1277984, by rfl⟩ : syracuseStep 1703979 = 2555969) B2555969
theorem B1703991 : Blo 1703552 1703991 := bstep (se 1 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 1703991 = 2555987) B2555987
theorem B1704011 : Blo 1703552 1704011 := bstep (se 1 (by rfl) ⟨1278008, by rfl⟩ : syracuseStep 1704011 = 2556017) B2556017
theorem B1704023 : Blo 1703552 1704023 := bstep (se 1 (by rfl) ⟨1278017, by rfl⟩ : syracuseStep 1704023 = 2556035) B2556035
theorem B3833945 : Blo 1703552 3833945 := bstep (se 2 (by rfl) ⟨1437729, by rfl⟩ : syracuseStep 3833945 = 2875459) B2875459
theorem B2555993 : Blo 1703552 2555993 := bstep (se 2 (by rfl) ⟨958497, by rfl⟩ : syracuseStep 2555993 = 1916995) B1916995
theorem B1704043 : Blo 1703552 1704043 := bstep (se 1 (by rfl) ⟨1278032, by rfl⟩ : syracuseStep 1704043 = 2556065) B2556065
theorem B1704055 : Blo 1703552 1704055 := bstep (se 1 (by rfl) ⟨1278041, by rfl⟩ : syracuseStep 1704055 = 2556083) B2556083
theorem B1917067 : Blo 1703552 1917067 := bstep (se 1 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 1917067 = 2875601) B2875601
theorem B1704075 : Blo 1703552 1704075 := bstep (se 1 (by rfl) ⟨1278056, by rfl⟩ : syracuseStep 1704075 = 2556113) B2556113
theorem B1704087 : Blo 1703552 1704087 := bstep (se 1 (by rfl) ⟨1278065, by rfl⟩ : syracuseStep 1704087 = 2556131) B2556131
theorem B1704107 : Blo 1703552 1704107 := bstep (se 1 (by rfl) ⟨1278080, by rfl⟩ : syracuseStep 1704107 = 2556161) B2556161
theorem B3834035 : Blo 1703552 3834035 := bstep (se 1 (by rfl) ⟨2875526, by rfl⟩ : syracuseStep 3834035 = 5751053) B5751053
theorem B1704119 : Blo 1703552 1704119 := bstep (se 1 (by rfl) ⟨1278089, by rfl⟩ : syracuseStep 1704119 = 2556179) B2556179
theorem B2556107 : Blo 1703552 2556107 := bstep (se 1 (by rfl) ⟨1917080, by rfl⟩ : syracuseStep 2556107 = 3834161) B3834161
theorem B1704139 : Blo 1703552 1704139 := bstep (se 1 (by rfl) ⟨1278104, by rfl⟩ : syracuseStep 1704139 = 2556209) B2556209
theorem B3834071 : Blo 1703552 3834071 := bstep (se 1 (by rfl) ⟨2875553, by rfl⟩ : syracuseStep 3834071 = 5751107) B5751107
theorem B2556119 : Blo 1703552 2556119 := bstep (se 1 (by rfl) ⟨1917089, by rfl⟩ : syracuseStep 2556119 = 3834179) B3834179
theorem B1704151 : Blo 1703552 1704151 := bstep (se 1 (by rfl) ⟨1278113, by rfl⟩ : syracuseStep 1704151 = 2556227) B2556227
theorem B4096217 : Blo 1703552 4096217 := bstep (se 2 (by rfl) ⟨1536081, by rfl⟩ : syracuseStep 4096217 = 3072163) B3072163
theorem B1704171 : Blo 1703552 1704171 := bstep (se 1 (by rfl) ⟨1278128, by rfl⟩ : syracuseStep 1704171 = 2556257) B2556257
theorem B1917175 : Blo 1703552 1917175 := bstep (se 1 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 1917175 = 2875763) B2875763
theorem B1704183 : Blo 1703552 1704183 := bstep (se 1 (by rfl) ⟨1278137, by rfl⟩ : syracuseStep 1704183 = 2556275) B2556275
theorem B1704203 : Blo 1703552 1704203 := bstep (se 1 (by rfl) ⟨1278152, by rfl⟩ : syracuseStep 1704203 = 2556305) B2556305
theorem B3236107 : Blo 1703552 3236107 := bstep (se 1 (by rfl) ⟨2427080, by rfl⟩ : syracuseStep 3236107 = 4854161) B4854161
theorem B1704215 : Blo 1703552 1704215 := bstep (se 1 (by rfl) ⟨1278161, by rfl⟩ : syracuseStep 1704215 = 2556323) B2556323
theorem B2556185 : Blo 1703552 2556185 := bstep (se 2 (by rfl) ⟨958569, by rfl⟩ : syracuseStep 2556185 = 1917139) B1917139
theorem B1704235 : Blo 1703552 1704235 := bstep (se 1 (by rfl) ⟨1278176, by rfl⟩ : syracuseStep 1704235 = 2556353) B2556353
theorem B1704247 : Blo 1703552 1704247 := bstep (se 1 (by rfl) ⟨1278185, by rfl⟩ : syracuseStep 1704247 = 2556371) B2556371
theorem B6472001 : Blo 1703552 6472001 := bstep (se 2 (by rfl) ⟨2427000, by rfl⟩ : syracuseStep 6472001 = 4854001) B4854001
theorem B1704267 : Blo 1703552 1704267 := bstep (se 1 (by rfl) ⟨1278200, by rfl⟩ : syracuseStep 1704267 = 2556401) B2556401
theorem B1704279 : Blo 1703552 1704279 := bstep (se 1 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 1704279 = 2556419) B2556419
theorem B3236183 : Blo 1703552 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B1704299 : Blo 1703552 1704299 := bstep (se 1 (by rfl) ⟨1278224, by rfl⟩ : syracuseStep 1704299 = 2556449) B2556449
theorem B1704311 : Blo 1703552 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B3834251 : Blo 1703552 3834251 := bstep (se 1 (by rfl) ⟨2875688, by rfl⟩ : syracuseStep 3834251 = 5751377) B5751377
theorem B2556299 : Blo 1703552 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B1704331 : Blo 1703552 1704331 := bstep (se 1 (by rfl) ⟨1278248, by rfl⟩ : syracuseStep 1704331 = 2556497) B2556497
theorem B2556311 : Blo 1703552 2556311 := bstep (se 1 (by rfl) ⟨1917233, by rfl⟩ : syracuseStep 2556311 = 3834467) B3834467
theorem B1704343 : Blo 1703552 1704343 := bstep (se 1 (by rfl) ⟨1278257, by rfl⟩ : syracuseStep 1704343 = 2556515) B2556515
theorem B1917355 : Blo 1703552 1917355 := bstep (se 1 (by rfl) ⟨1438016, by rfl⟩ : syracuseStep 1917355 = 2876033) B2876033
theorem B1704363 : Blo 1703552 1704363 := bstep (se 1 (by rfl) ⟨1278272, by rfl⟩ : syracuseStep 1704363 = 2556545) B2556545
theorem B1704375 : Blo 1703552 1704375 := bstep (se 1 (by rfl) ⟨1278281, by rfl⟩ : syracuseStep 1704375 = 2556563) B2556563
theorem B3834305 : Blo 1703552 3834305 := bstep (se 2 (by rfl) ⟨1437864, by rfl⟩ : syracuseStep 3834305 = 2875729) B2875729
theorem B1704395 : Blo 1703552 1704395 := bstep (se 1 (by rfl) ⟨1278296, by rfl⟩ : syracuseStep 1704395 = 2556593) B2556593
theorem B1704407 : Blo 1703552 1704407 := bstep (se 1 (by rfl) ⟨1278305, by rfl⟩ : syracuseStep 1704407 = 2556611) B2556611
theorem B2556377 : Blo 1703552 2556377 := bstep (se 2 (by rfl) ⟨958641, by rfl⟩ : syracuseStep 2556377 = 1917283) B1917283
theorem B1704427 : Blo 1703552 1704427 := bstep (se 1 (by rfl) ⟨1278320, by rfl⟩ : syracuseStep 1704427 = 2556641) B2556641
theorem B1704439 : Blo 1703552 1704439 := bstep (se 1 (by rfl) ⟨1278329, by rfl⟩ : syracuseStep 1704439 = 2556659) B2556659
theorem B1704459 : Blo 1703552 1704459 := bstep (se 1 (by rfl) ⟨1278344, by rfl⟩ : syracuseStep 1704459 = 2556689) B2556689
theorem B1917463 : Blo 1703552 1917463 := bstep (se 1 (by rfl) ⟨1438097, by rfl⟩ : syracuseStep 1917463 = 2876195) B2876195
theorem B1704471 : Blo 1703552 1704471 := bstep (se 1 (by rfl) ⟨1278353, by rfl⟩ : syracuseStep 1704471 = 2556707) B2556707
theorem B1704491 : Blo 1703552 1704491 := bstep (se 1 (by rfl) ⟨1278368, by rfl⟩ : syracuseStep 1704491 = 2556737) B2556737
theorem B1704503 : Blo 1703552 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B2875979 : Blo 1703552 2875979 := bstep (se 1 (by rfl) ⟨2156984, by rfl⟩ : syracuseStep 2875979 = 4313969) B4313969
theorem B2556491 : Blo 1703552 2556491 := bstep (se 1 (by rfl) ⟨1917368, by rfl⟩ : syracuseStep 2556491 = 3834737) B3834737
theorem B1704523 : Blo 1703552 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B2556503 : Blo 1703552 2556503 := bstep (se 1 (by rfl) ⟨1917377, by rfl⟩ : syracuseStep 2556503 = 3834755) B3834755
theorem B1704535 : Blo 1703552 1704535 := bstep (se 1 (by rfl) ⟨1278401, by rfl⟩ : syracuseStep 1704535 = 2556803) B2556803
theorem B1704555 : Blo 1703552 1704555 := bstep (se 1 (by rfl) ⟨1278416, by rfl⟩ : syracuseStep 1704555 = 2556833) B2556833
theorem B1704567 : Blo 1703552 1704567 := bstep (se 1 (by rfl) ⟨1278425, by rfl⟩ : syracuseStep 1704567 = 2556851) B2556851
theorem B1704587 : Blo 1703552 1704587 := bstep (se 1 (by rfl) ⟨1278440, by rfl⟩ : syracuseStep 1704587 = 2556881) B2556881
theorem B1704599 : Blo 1703552 1704599 := bstep (se 1 (by rfl) ⟨1278449, by rfl⟩ : syracuseStep 1704599 = 2556899) B2556899
theorem B3834521 : Blo 1703552 3834521 := bstep (se 2 (by rfl) ⟨1437945, by rfl⟩ : syracuseStep 3834521 = 2875891) B2875891
theorem B2556569 : Blo 1703552 2556569 := bstep (se 2 (by rfl) ⟨958713, by rfl⟩ : syracuseStep 2556569 = 1917427) B1917427
theorem B1819307 : Blo 1703552 1819307 := bstep (se 1 (by rfl) ⟨1364480, by rfl⟩ : syracuseStep 1819307 = 2728961) B2728961
theorem B1704619 : Blo 1703552 1704619 := bstep (se 1 (by rfl) ⟨1278464, by rfl⟩ : syracuseStep 1704619 = 2556929) B2556929
theorem B1704631 : Blo 1703552 1704631 := bstep (se 1 (by rfl) ⟨1278473, by rfl⟩ : syracuseStep 1704631 = 2556947) B2556947
theorem B5194433 : Blo 1703552 5194433 := bstep (se 2 (by rfl) ⟨1947912, by rfl⟩ : syracuseStep 5194433 = 3895825) B3895825
theorem B2876107 : Blo 1703552 2876107 := bstep (se 1 (by rfl) ⟨2157080, by rfl⟩ : syracuseStep 2876107 = 4314161) B4314161
theorem B1917643 : Blo 1703552 1917643 := bstep (se 1 (by rfl) ⟨1438232, by rfl⟩ : syracuseStep 1917643 = 2876465) B2876465
theorem B1704651 : Blo 1703552 1704651 := bstep (se 1 (by rfl) ⟨1278488, by rfl⟩ : syracuseStep 1704651 = 2556977) B2556977
theorem B1704663 : Blo 1703552 1704663 := bstep (se 1 (by rfl) ⟨1278497, by rfl⟩ : syracuseStep 1704663 = 2556995) B2556995
theorem B1704683 : Blo 1703552 1704683 := bstep (se 1 (by rfl) ⟨1278512, by rfl⟩ : syracuseStep 1704683 = 2557025) B2557025
theorem B3834611 : Blo 1703552 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B1704695 : Blo 1703552 1704695 := bstep (se 1 (by rfl) ⟨1278521, by rfl⟩ : syracuseStep 1704695 = 2557043) B2557043
theorem B2556683 : Blo 1703552 2556683 := bstep (se 1 (by rfl) ⟨1917512, by rfl⟩ : syracuseStep 2556683 = 3835025) B3835025
theorem B1704715 : Blo 1703552 1704715 := bstep (se 1 (by rfl) ⟨1278536, by rfl⟩ : syracuseStep 1704715 = 2557073) B2557073
theorem B3834647 : Blo 1703552 3834647 := bstep (se 1 (by rfl) ⟨2875985, by rfl⟩ : syracuseStep 3834647 = 5751971) B5751971
theorem B2556695 : Blo 1703552 2556695 := bstep (se 1 (by rfl) ⟨1917521, by rfl⟩ : syracuseStep 2556695 = 3835043) B3835043
theorem B1704727 : Blo 1703552 1704727 := bstep (se 1 (by rfl) ⟨1278545, by rfl⟩ : syracuseStep 1704727 = 2557091) B2557091
theorem B1704747 : Blo 1703552 1704747 := bstep (se 1 (by rfl) ⟨1278560, by rfl⟩ : syracuseStep 1704747 = 2557121) B2557121
theorem B1917751 : Blo 1703552 1917751 := bstep (se 1 (by rfl) ⟨1438313, by rfl⟩ : syracuseStep 1917751 = 2876627) B2876627
theorem B1704759 : Blo 1703552 1704759 := bstep (se 1 (by rfl) ⟨1278569, by rfl⟩ : syracuseStep 1704759 = 2557139) B2557139
theorem B1704779 : Blo 1703552 1704779 := bstep (se 1 (by rfl) ⟨1278584, by rfl⟩ : syracuseStep 1704779 = 2557169) B2557169
theorem B1704791 : Blo 1703552 1704791 := bstep (se 1 (by rfl) ⟨1278593, by rfl⟩ : syracuseStep 1704791 = 2557187) B2557187
theorem B2876249 : Blo 1703552 2876249 := bstep (se 2 (by rfl) ⟨1078593, by rfl⟩ : syracuseStep 2876249 = 2157187) B2157187
theorem B2556761 : Blo 1703552 2556761 := bstep (se 2 (by rfl) ⟨958785, by rfl⟩ : syracuseStep 2556761 = 1917571) B1917571
theorem B1704811 : Blo 1703552 1704811 := bstep (se 1 (by rfl) ⟨1278608, by rfl⟩ : syracuseStep 1704811 = 2557217) B2557217
theorem B1704823 : Blo 1703552 1704823 := bstep (se 1 (by rfl) ⟨1278617, by rfl⟩ : syracuseStep 1704823 = 2557235) B2557235
theorem B1704843 : Blo 1703552 1704843 := bstep (se 1 (by rfl) ⟨1278632, by rfl⟩ : syracuseStep 1704843 = 2557265) B2557265
theorem B1704855 : Blo 1703552 1704855 := bstep (se 1 (by rfl) ⟨1278641, by rfl⟩ : syracuseStep 1704855 = 2557283) B2557283
theorem B1704875 : Blo 1703552 1704875 := bstep (se 1 (by rfl) ⟨1278656, by rfl⟩ : syracuseStep 1704875 = 2557313) B2557313
theorem B1704887 : Blo 1703552 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B5751755 : Blo 1703552 5751755 := bstep (se 1 (by rfl) ⟨4313816, by rfl⟩ : syracuseStep 5751755 = 8627633) B8627633
theorem B3834827 : Blo 1703552 3834827 := bstep (se 1 (by rfl) ⟨2876120, by rfl⟩ : syracuseStep 3834827 = 5752241) B5752241
theorem B2556875 : Blo 1703552 2556875 := bstep (se 1 (by rfl) ⟨1917656, by rfl⟩ : syracuseStep 2556875 = 3835313) B3835313
theorem B1704907 : Blo 1703552 1704907 := bstep (se 1 (by rfl) ⟨1278680, by rfl⟩ : syracuseStep 1704907 = 2557361) B2557361
theorem B2556887 : Blo 1703552 2556887 := bstep (se 1 (by rfl) ⟨1917665, by rfl⟩ : syracuseStep 2556887 = 3835331) B3835331
theorem B1704919 : Blo 1703552 1704919 := bstep (se 1 (by rfl) ⟨1278689, by rfl⟩ : syracuseStep 1704919 = 2557379) B2557379
theorem B2876377 : Blo 1703552 2876377 := bstep (se 2 (by rfl) ⟨1078641, by rfl⟩ : syracuseStep 2876377 = 2157283) B2157283
theorem B6472669 : Blo 1703552 6472669 := bstep (se 3 (by rfl) ⟨1213625, by rfl⟩ : syracuseStep 6472669 = 2427251) B2427251
theorem B1917931 : Blo 1703552 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B1704939 : Blo 1703552 1704939 := bstep (se 1 (by rfl) ⟨1278704, by rfl⟩ : syracuseStep 1704939 = 2557409) B2557409
theorem B3236851 : Blo 1703552 3236851 := bstep (se 1 (by rfl) ⟨2427638, by rfl⟩ : syracuseStep 3236851 = 4855277) B4855277
theorem B1704951 : Blo 1703552 1704951 := bstep (se 1 (by rfl) ⟨1278713, by rfl⟩ : syracuseStep 1704951 = 2557427) B2557427
theorem B3834881 : Blo 1703552 3834881 := bstep (se 2 (by rfl) ⟨1438080, by rfl⟩ : syracuseStep 3834881 = 2876161) B2876161
theorem B1704971 : Blo 1703552 1704971 := bstep (se 1 (by rfl) ⟨1278728, by rfl⟩ : syracuseStep 1704971 = 2557457) B2557457
theorem B2425879 : Blo 1703552 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B1704983 : Blo 1703552 1704983 := bstep (se 1 (by rfl) ⟨1278737, by rfl⟩ : syracuseStep 1704983 = 2557475) B2557475
theorem B2556953 : Blo 1703552 2556953 := bstep (se 2 (by rfl) ⟨958857, by rfl⟩ : syracuseStep 2556953 = 1917715) B1917715
theorem B1705003 : Blo 1703552 1705003 := bstep (se 1 (by rfl) ⟨1278752, by rfl⟩ : syracuseStep 1705003 = 2557505) B2557505
theorem B1705015 : Blo 1703552 1705015 := bstep (se 1 (by rfl) ⟨1278761, by rfl⟩ : syracuseStep 1705015 = 2557523) B2557523
theorem B1705035 : Blo 1703552 1705035 := bstep (se 1 (by rfl) ⟨1278776, by rfl⟩ : syracuseStep 1705035 = 2557553) B2557553
theorem B1918039 : Blo 1703552 1918039 := bstep (se 1 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 1918039 = 2877059) B2877059
theorem B1705047 : Blo 1703552 1705047 := bstep (se 1 (by rfl) ⟨1278785, by rfl⟩ : syracuseStep 1705047 = 2557571) B2557571
theorem B9839717 : Blo 1703552 9839717 := bstep (se 4 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 9839717 = 1844947) B1844947
theorem B2557067 : Blo 1703552 2557067 := bstep (se 1 (by rfl) ⟨1917800, by rfl⟩ : syracuseStep 2557067 = 3835601) B3835601
theorem B2557079 : Blo 1703552 2557079 := bstep (se 1 (by rfl) ⟨1917809, by rfl⟩ : syracuseStep 2557079 = 3835619) B3835619
theorem B5752025 : Blo 1703552 5752025 := bstep (se 2 (by rfl) ⟨2157009, by rfl⟩ : syracuseStep 5752025 = 4314019) B4314019
theorem B3835097 : Blo 1703552 3835097 := bstep (se 2 (by rfl) ⟨1438161, by rfl⟩ : syracuseStep 3835097 = 2876323) B2876323
theorem B2557145 : Blo 1703552 2557145 := bstep (se 2 (by rfl) ⟨958929, by rfl⟩ : syracuseStep 2557145 = 1917859) B1917859
theorem B3835187 : Blo 1703552 3835187 := bstep (se 1 (by rfl) ⟨2876390, by rfl⟩ : syracuseStep 3835187 = 5752781) B5752781
theorem B2557259 : Blo 1703552 2557259 := bstep (se 1 (by rfl) ⟨1917944, by rfl⟩ : syracuseStep 2557259 = 3835889) B3835889
theorem B3835223 : Blo 1703552 3835223 := bstep (se 1 (by rfl) ⟨2876417, by rfl⟩ : syracuseStep 3835223 = 5752835) B5752835
theorem B2557271 : Blo 1703552 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B2557337 : Blo 1703552 2557337 := bstep (se 2 (by rfl) ⟨959001, by rfl⟩ : syracuseStep 2557337 = 1918003) B1918003
theorem B437061091 : Blo 1703552 437061091 := bstep (se 1 (by rfl) ⟨327795818, by rfl⟩ : syracuseStep 437061091 = 655591637) B655591637
theorem B3835403 : Blo 1703552 3835403 := bstep (se 1 (by rfl) ⟨2876552, by rfl⟩ : syracuseStep 3835403 = 5753105) B5753105
theorem B2557451 : Blo 1703552 2557451 := bstep (se 1 (by rfl) ⟨1918088, by rfl⟩ : syracuseStep 2557451 = 3836177) B3836177
theorem B2876951 : Blo 1703552 2876951 := bstep (se 1 (by rfl) ⟨2157713, by rfl⟩ : syracuseStep 2876951 = 4315427) B4315427
theorem B2557463 : Blo 1703552 2557463 := bstep (se 1 (by rfl) ⟨1918097, by rfl⟩ : syracuseStep 2557463 = 3836195) B3836195
theorem B3835457 : Blo 1703552 3835457 := bstep (se 2 (by rfl) ⟨1438296, by rfl⟩ : syracuseStep 3835457 = 2876593) B2876593
theorem B2557529 : Blo 1703552 2557529 := bstep (se 2 (by rfl) ⟨959073, by rfl⟩ : syracuseStep 2557529 = 1918147) B1918147
theorem B2877079 : Blo 1703552 2877079 := bstep (se 1 (by rfl) ⟨2157809, by rfl⟩ : syracuseStep 2877079 = 4315619) B4315619
theorem B3638963 : Blo 1703552 3638963 := bstep (se 1 (by rfl) ⟨2729222, by rfl⟩ : syracuseStep 3638963 = 5458445) B5458445
theorem B2156311 : Blo 1703552 2156311 := bstep (se 1 (by rfl) ⟨1617233, by rfl⟩ : syracuseStep 2156311 = 3234467) B3234467
theorem B3835673 : Blo 1703552 3835673 := bstep (se 2 (by rfl) ⟨1438377, by rfl⟩ : syracuseStep 3835673 = 2876755) B2876755
theorem B2426699 : Blo 1703552 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B1820503 : Blo 1703552 1820503 := bstep (se 1 (by rfl) ⟨1365377, by rfl⟩ : syracuseStep 1820503 = 2730755) B2730755
theorem B3835763 : Blo 1703552 3835763 := bstep (se 1 (by rfl) ⟨2876822, by rfl⟩ : syracuseStep 3835763 = 5753645) B5753645
theorem B18425717 : Blo 1703552 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B8628119 : Blo 1703552 8628119 := bstep (se 1 (by rfl) ⟨6471089, by rfl⟩ : syracuseStep 8628119 = 12942179) B12942179
theorem B5752727 : Blo 1703552 5752727 := bstep (se 1 (by rfl) ⟨4314545, by rfl⟩ : syracuseStep 5752727 = 8629091) B8629091
theorem B3835799 : Blo 1703552 3835799 := bstep (se 1 (by rfl) ⟨2876849, by rfl⟩ : syracuseStep 3835799 = 5753699) B5753699
theorem B2590679 : Blo 1703552 2590679 := bstep (se 1 (by rfl) ⟨1943009, by rfl⟩ : syracuseStep 2590679 = 3886019) B3886019
theorem B5457881 : Blo 1703552 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B4851677 : Blo 1703552 4851677 := bstep (se 3 (by rfl) ⟨909689, by rfl⟩ : syracuseStep 4851677 = 1819379) B1819379
theorem B3835979 : Blo 1703552 3835979 := bstep (se 1 (by rfl) ⟨2876984, by rfl⟩ : syracuseStep 3835979 = 5753969) B5753969
theorem B3836033 : Blo 1703552 3836033 := bstep (se 2 (by rfl) ⟨1438512, by rfl⟩ : syracuseStep 3836033 = 2877025) B2877025
theorem B3279091 : Blo 1703552 3279091 := bstep (se 1 (by rfl) ⟨2459318, by rfl⟩ : syracuseStep 3279091 = 4918637) B4918637
theorem B7276817 : Blo 1703552 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B11659565 : Blo 1703552 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B10111277 : Blo 1703552 10111277 := bstep (se 3 (by rfl) ⟨1895864, by rfl⟩ : syracuseStep 10111277 = 3791729) B3791729
theorem B11659585 : Blo 1703552 11659585 := bstep (se 2 (by rfl) ⟨4372344, by rfl⟩ : syracuseStep 11659585 = 8744689) B8744689
theorem B3156299 : Blo 1703552 3156299 := bstep (se 1 (by rfl) ⟨2367224, by rfl⟩ : syracuseStep 3156299 = 4734449) B4734449
theorem B3836249 : Blo 1703552 3836249 := bstep (se 2 (by rfl) ⟨1438593, by rfl⟩ : syracuseStep 3836249 = 2877187) B2877187
theorem B5753267 : Blo 1703552 5753267 := bstep (se 1 (by rfl) ⟨4314950, by rfl⟩ : syracuseStep 5753267 = 8629901) B8629901
theorem B3836339 : Blo 1703552 3836339 := bstep (se 1 (by rfl) ⟨2877254, by rfl⟩ : syracuseStep 3836339 = 5754509) B5754509
theorem B14559749 : Blo 1703552 14559749 := bstep (se 4 (by rfl) ⟨1364976, by rfl⟩ : syracuseStep 14559749 = 2729953) B2729953
theorem B2157131 : Blo 1703552 2157131 := bstep (se 1 (by rfl) ⟨1617848, by rfl⟩ : syracuseStep 2157131 = 3235697) B3235697
theorem B6228569 : Blo 1703552 6228569 := bstep (se 2 (by rfl) ⟨2335713, by rfl⟩ : syracuseStep 6228569 = 4671427) B4671427
theorem B5753537 : Blo 1703552 5753537 := bstep (se 2 (by rfl) ⟨2157576, by rfl⟩ : syracuseStep 5753537 = 4315153) B4315153
theorem B2427673 : Blo 1703552 2427673 := bstep (se 2 (by rfl) ⟨910377, by rfl⟩ : syracuseStep 2427673 = 1820755) B1820755
theorem B6908723 : Blo 1703552 6908723 := bstep (se 1 (by rfl) ⟨5181542, by rfl⟩ : syracuseStep 6908723 = 10363085) B10363085
theorem B3640459 : Blo 1703552 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B7277789 : Blo 1703552 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B5754077 : Blo 1703552 5754077 := bstep (se 3 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 5754077 = 2157779) B2157779
theorem B2157835 : Blo 1703552 2157835 := bstep (se 1 (by rfl) ⟨1618376, by rfl⟩ : syracuseStep 2157835 = 3236753) B3236753
theorem B10505537 : Blo 1703552 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B19410353 : Blo 1703552 19410353 := bstep (se 2 (by rfl) ⟨7278882, by rfl⟩ : syracuseStep 19410353 = 14557765) B14557765
theorem B2076247 : Blo 1703552 2076247 := bstep (se 1 (by rfl) ⟨1557185, by rfl⟩ : syracuseStep 2076247 = 3114371) B3114371
theorem B3886913 : Blo 1703552 3886913 := bstep (se 2 (by rfl) ⟨1457592, by rfl⟩ : syracuseStep 3886913 = 2915185) B2915185
theorem B29126465 : Blo 1703552 29126465 := bstep (se 2 (by rfl) ⟨10922424, by rfl⟩ : syracuseStep 29126465 = 21844849) B21844849
theorem B24571765 : Blo 1703552 24571765 := bstep (se 5 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 24571765 = 2303603) B2303603
theorem B9211799 : Blo 1703552 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B3502081 : Blo 1703552 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B5460317 : Blo 1703552 5460317 := bstep (se 3 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 5460317 = 2047619) B2047619
theorem B6558259 : Blo 1703552 6558259 := bstep (se 1 (by rfl) ⟨4918694, by rfl⟩ : syracuseStep 6558259 = 9837389) B9837389
theorem B14553665 : Blo 1703552 14553665 := bstep (se 2 (by rfl) ⟨5457624, by rfl⟩ : syracuseStep 14553665 = 10915249) B10915249
theorem B4313675 : Blo 1703552 4313675 := bstep (se 1 (by rfl) ⟨3235256, by rfl⟩ : syracuseStep 4313675 = 6470513) B6470513
theorem B56013443 : Blo 1703552 56013443 := bstep (se 1 (by rfl) ⟨42010082, by rfl⟩ : syracuseStep 56013443 = 84020165) B84020165
theorem B4854593 : Blo 1703552 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B4854617 : Blo 1703552 4854617 := bstep (se 2 (by rfl) ⟨1820481, by rfl⟩ : syracuseStep 4854617 = 3640963) B3640963
theorem B6468569 : Blo 1703552 6468569 := bstep (se 2 (by rfl) ⟨2425713, by rfl⟩ : syracuseStep 6468569 = 4851427) B4851427
theorem B3888281 : Blo 1703552 3888281 := bstep (se 2 (by rfl) ⟨1458105, by rfl⟩ : syracuseStep 3888281 = 2916211) B2916211
theorem B6468781 : Blo 1703552 6468781 := bstep (se 3 (by rfl) ⟨1212896, by rfl⟩ : syracuseStep 6468781 = 2425793) B2425793
theorem B3241291 : Blo 1703552 3241291 := bstep (se 1 (by rfl) ⟨2430968, by rfl⟩ : syracuseStep 3241291 = 4861937) B4861937
theorem B15545675 : Blo 1703552 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B3888499 : Blo 1703552 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B8631683 : Blo 1703552 8631683 := bstep (se 1 (by rfl) ⟨6473762, by rfl⟩ : syracuseStep 8631683 = 12947525) B12947525
theorem B6141329 : Blo 1703552 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B12940721 : Blo 1703552 12940721 := bstep (se 2 (by rfl) ⟨4852770, by rfl⟩ : syracuseStep 12940721 = 9705541) B9705541
theorem B5182913 : Blo 1703552 5182913 := bstep (se 2 (by rfl) ⟨1943592, by rfl⟩ : syracuseStep 5182913 = 3887185) B3887185
theorem B85169621 : Blo 1703552 85169621 := bstep (se 7 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 85169621 = 1996163) B1996163
theorem B6469085 : Blo 1703552 6469085 := bstep (se 3 (by rfl) ⟨1212953, by rfl⟩ : syracuseStep 6469085 = 2425907) B2425907
theorem B4314647 : Blo 1703552 4314647 := bstep (se 1 (by rfl) ⟨3235985, by rfl⟩ : syracuseStep 4314647 = 6471971) B6471971
theorem B5535307 : Blo 1703552 5535307 := bstep (se 1 (by rfl) ⟨4151480, by rfl⟩ : syracuseStep 5535307 = 8302961) B8302961
theorem B3454579 : Blo 1703552 3454579 := bstep (se 1 (by rfl) ⟨2590934, by rfl⟩ : syracuseStep 3454579 = 5181869) B5181869
theorem B1799863 : Blo 1703552 1799863 := bstep (se 1 (by rfl) ⟨1349897, by rfl⟩ : syracuseStep 1799863 = 2699795) B2699795
theorem B7280387 : Blo 1703552 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B7378733 : Blo 1703552 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B6911837 : Blo 1703552 6911837 := bstep (se 3 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 6911837 = 2591939) B2591939
theorem B17495909 : Blo 1703552 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B12941207 : Blo 1703552 12941207 := bstep (se 1 (by rfl) ⟨9705905, by rfl⟩ : syracuseStep 12941207 = 19411811) B19411811
theorem B13817861 : Blo 1703552 13817861 := bstep (se 4 (by rfl) ⟨1295424, by rfl⟩ : syracuseStep 13817861 = 2590849) B2590849
theorem B4094027 : Blo 1703552 4094027 := bstep (se 1 (by rfl) ⟨3070520, by rfl⟩ : syracuseStep 4094027 = 6141041) B6141041
theorem B7280729 : Blo 1703552 7280729 := bstep (se 2 (by rfl) ⟨2730273, by rfl⟩ : syracuseStep 7280729 = 5460547) B5460547
theorem B3938483 : Blo 1703552 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B4315315 : Blo 1703552 4315315 := bstep (se 1 (by rfl) ⟨3236486, by rfl⟩ : syracuseStep 4315315 = 6472973) B6472973
theorem B21838085 : Blo 1703552 21838085 := bstep (se 4 (by rfl) ⟨2047320, by rfl⟩ : syracuseStep 21838085 = 4094641) B4094641
theorem B26589485 : Blo 1703552 26589485 := bstep (se 3 (by rfl) ⟨4985528, by rfl⟩ : syracuseStep 26589485 = 9971057) B9971057
theorem B4315457 : Blo 1703552 4315457 := bstep (se 2 (by rfl) ⟨1618296, by rfl⟩ : syracuseStep 4315457 = 3236593) B3236593
theorem B3234163 : Blo 1703552 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B265730881 : Blo 1703552 265730881 := bstep (se 2 (by rfl) ⟨99649080, by rfl⟩ : syracuseStep 265730881 = 199298161) B199298161
theorem B3234649 : Blo 1703552 3234649 := bstep (se 2 (by rfl) ⟨1212993, by rfl⟩ : syracuseStep 3234649 = 2425987) B2425987
theorem B12287011 : Blo 1703552 12287011 := bstep (se 1 (by rfl) ⟨9215258, by rfl⟩ : syracuseStep 12287011 = 18430517) B18430517
theorem B5749811 : Blo 1703552 5749811 := bstep (se 1 (by rfl) ⟨4312358, by rfl⟩ : syracuseStep 5749811 = 8624717) B8624717
theorem B3833099 : Blo 1703552 3833099 := bstep (se 1 (by rfl) ⟨2874824, by rfl⟩ : syracuseStep 3833099 = 5749649) B5749649
theorem B11066669 : Blo 1703552 11066669 := bstep (se 3 (by rfl) ⟨2075000, by rfl⟩ : syracuseStep 11066669 = 4150001) B4150001
theorem B3833153 : Blo 1703552 3833153 := bstep (se 2 (by rfl) ⟨1437432, by rfl⟩ : syracuseStep 3833153 = 2874865) B2874865
theorem B5750081 : Blo 1703552 5750081 := bstep (se 2 (by rfl) ⟨2156280, by rfl⟩ : syracuseStep 5750081 = 4312561) B4312561
theorem B9706817 : Blo 1703552 9706817 := bstep (se 2 (by rfl) ⟨3640056, by rfl⟩ : syracuseStep 9706817 = 7280113) B7280113
theorem B3235211 : Blo 1703552 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B5184947 : Blo 1703552 5184947 := bstep (se 1 (by rfl) ⟨3888710, by rfl⟩ : syracuseStep 5184947 = 7777421) B7777421
theorem B2555339 : Blo 1703552 2555339 := bstep (se 1 (by rfl) ⟨1916504, by rfl⟩ : syracuseStep 2555339 = 3833009) B3833009
theorem B2555351 : Blo 1703552 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B2555417 : Blo 1703552 2555417 := bstep (se 2 (by rfl) ⟨958281, by rfl⟩ : syracuseStep 2555417 = 1916563) B1916563
theorem B3833369 : Blo 1703552 3833369 := bstep (se 2 (by rfl) ⟨1437513, by rfl⟩ : syracuseStep 3833369 = 2875027) B2875027
theorem B3235393 : Blo 1703552 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B3833459 : Blo 1703552 3833459 := bstep (se 1 (by rfl) ⟨2875094, by rfl⟩ : syracuseStep 3833459 = 5750189) B5750189
theorem B10919555 : Blo 1703552 10919555 := bstep (se 1 (by rfl) ⟨8189666, by rfl⟩ : syracuseStep 10919555 = 16379333) B16379333
theorem B1703563 : Blo 1703552 1703563 := bstep (se 1 (by rfl) ⟨1277672, by rfl⟩ : syracuseStep 1703563 = 2555345) B2555345
theorem B2555531 : Blo 1703552 2555531 := bstep (se 1 (by rfl) ⟨1916648, by rfl⟩ : syracuseStep 2555531 = 3833297) B3833297
theorem B1703575 : Blo 1703552 1703575 := bstep (se 1 (by rfl) ⟨1277681, by rfl⟩ : syracuseStep 1703575 = 2555363) B2555363
theorem B2555543 : Blo 1703552 2555543 := bstep (se 1 (by rfl) ⟨1916657, by rfl⟩ : syracuseStep 2555543 = 3833315) B3833315
theorem B3833495 : Blo 1703552 3833495 := bstep (se 1 (by rfl) ⟨2875121, by rfl⟩ : syracuseStep 3833495 = 5750243) B5750243
theorem B1703595 : Blo 1703552 1703595 := bstep (se 1 (by rfl) ⟨1277696, by rfl⟩ : syracuseStep 1703595 = 2555393) B2555393
theorem B1703607 : Blo 1703552 1703607 := bstep (se 1 (by rfl) ⟨1277705, by rfl⟩ : syracuseStep 1703607 = 2555411) B2555411
theorem B1916599 : Blo 1703552 1916599 := bstep (se 1 (by rfl) ⟨1437449, by rfl⟩ : syracuseStep 1916599 = 2874899) B2874899
theorem B4988609 : Blo 1703552 4988609 := bstep (se 2 (by rfl) ⟨1870728, by rfl⟩ : syracuseStep 4988609 = 3741457) B3741457
theorem B1703627 : Blo 1703552 1703627 := bstep (se 1 (by rfl) ⟨1277720, by rfl⟩ : syracuseStep 1703627 = 2555441) B2555441
theorem B1703639 : Blo 1703552 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B2555609 : Blo 1703552 2555609 := bstep (se 2 (by rfl) ⟨958353, by rfl⟩ : syracuseStep 2555609 = 1916707) B1916707
theorem B8191705 : Blo 1703552 8191705 := bstep (se 2 (by rfl) ⟨3071889, by rfl⟩ : syracuseStep 8191705 = 6143779) B6143779
theorem B1703659 : Blo 1703552 1703659 := bstep (se 1 (by rfl) ⟨1277744, by rfl⟩ : syracuseStep 1703659 = 2555489) B2555489
theorem B1703671 : Blo 1703552 1703671 := bstep (se 1 (by rfl) ⟨1277753, by rfl⟩ : syracuseStep 1703671 = 2555507) B2555507
theorem B1703691 : Blo 1703552 1703691 := bstep (se 1 (by rfl) ⟨1277768, by rfl⟩ : syracuseStep 1703691 = 2555537) B2555537
theorem B1703703 : Blo 1703552 1703703 := bstep (se 1 (by rfl) ⟨1277777, by rfl⟩ : syracuseStep 1703703 = 2555555) B2555555
theorem B1703723 : Blo 1703552 1703723 := bstep (se 1 (by rfl) ⟨1277792, by rfl⟩ : syracuseStep 1703723 = 2555585) B2555585
theorem B1703735 : Blo 1703552 1703735 := bstep (se 1 (by rfl) ⟨1277801, by rfl⟩ : syracuseStep 1703735 = 2555603) B2555603
theorem B1703755 : Blo 1703552 1703755 := bstep (se 1 (by rfl) ⟨1277816, by rfl⟩ : syracuseStep 1703755 = 2555633) B2555633
theorem B2555723 : Blo 1703552 2555723 := bstep (se 1 (by rfl) ⟨1916792, by rfl⟩ : syracuseStep 2555723 = 3833585) B3833585
theorem B3833675 : Blo 1703552 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B1703767 : Blo 1703552 1703767 := bstep (se 1 (by rfl) ⟨1277825, by rfl⟩ : syracuseStep 1703767 = 2555651) B2555651
theorem B2555735 : Blo 1703552 2555735 := bstep (se 1 (by rfl) ⟨1916801, by rfl⟩ : syracuseStep 2555735 = 3833603) B3833603
theorem B2875223 : Blo 1703552 2875223 := bstep (se 1 (by rfl) ⟨2156417, by rfl⟩ : syracuseStep 2875223 = 4312835) B4312835
theorem B5750621 : Blo 1703552 5750621 := bstep (se 3 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 5750621 = 2156483) B2156483
theorem B8626013 : Blo 1703552 8626013 := bstep (se 3 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 8626013 = 3234755) B3234755
theorem B1703787 : Blo 1703552 1703787 := bstep (se 1 (by rfl) ⟨1277840, by rfl⟩ : syracuseStep 1703787 = 2555681) B2555681
theorem B1916779 : Blo 1703552 1916779 := bstep (se 1 (by rfl) ⟨1437584, by rfl⟩ : syracuseStep 1916779 = 2875169) B2875169
theorem B1703799 : Blo 1703552 1703799 := bstep (se 1 (by rfl) ⟨1277849, by rfl⟩ : syracuseStep 1703799 = 2555699) B2555699
theorem B3833729 : Blo 1703552 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B1703819 : Blo 1703552 1703819 := bstep (se 1 (by rfl) ⟨1277864, by rfl⟩ : syracuseStep 1703819 = 2555729) B2555729
theorem B1703831 : Blo 1703552 1703831 := bstep (se 1 (by rfl) ⟨1277873, by rfl⟩ : syracuseStep 1703831 = 2555747) B2555747
theorem B2555801 : Blo 1703552 2555801 := bstep (se 2 (by rfl) ⟨958425, by rfl⟩ : syracuseStep 2555801 = 1916851) B1916851
theorem B1703851 : Blo 1703552 1703851 := bstep (se 1 (by rfl) ⟨1277888, by rfl⟩ : syracuseStep 1703851 = 2555777) B2555777
theorem B1703863 : Blo 1703552 1703863 := bstep (se 1 (by rfl) ⟨1277897, by rfl⟩ : syracuseStep 1703863 = 2555795) B2555795
theorem B5832641 : Blo 1703552 5832641 := bstep (se 2 (by rfl) ⟨2187240, by rfl⟩ : syracuseStep 5832641 = 4374481) B4374481
theorem B1703883 : Blo 1703552 1703883 := bstep (se 1 (by rfl) ⟨1277912, by rfl⟩ : syracuseStep 1703883 = 2555825) B2555825
theorem B2875351 : Blo 1703552 2875351 := bstep (se 1 (by rfl) ⟨2156513, by rfl⟩ : syracuseStep 2875351 = 4313027) B4313027
theorem B1703895 : Blo 1703552 1703895 := bstep (se 1 (by rfl) ⟨1277921, by rfl⟩ : syracuseStep 1703895 = 2555843) B2555843
theorem B1916887 : Blo 1703552 1916887 := bstep (se 1 (by rfl) ⟨1437665, by rfl⟩ : syracuseStep 1916887 = 2875331) B2875331
theorem B1703915 : Blo 1703552 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B1703927 : Blo 1703552 1703927 := bstep (se 1 (by rfl) ⟨1277945, by rfl⟩ : syracuseStep 1703927 = 2555891) B2555891
theorem B18677765 : Blo 1703552 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1703943 : Blo 1703552 1703943 := bstep (se 1 (by rfl) ⟨1277957, by rfl⟩ : syracuseStep 1703943 = 2555915) B2555915
theorem B1703951 : Blo 1703552 1703951 := bstep (se 1 (by rfl) ⟨1277963, by rfl⟩ : syracuseStep 1703951 = 2555927) B2555927
theorem B2555963 : Blo 1703552 2555963 := bstep (se 1 (by rfl) ⟨1916972, by rfl⟩ : syracuseStep 2555963 = 3833945) B3833945
theorem B1703995 : Blo 1703552 1703995 := bstep (se 1 (by rfl) ⟨1277996, by rfl⟩ : syracuseStep 1703995 = 2555993) B2555993
theorem B2556023 : Blo 1703552 2556023 := bstep (se 1 (by rfl) ⟨1917017, by rfl⟩ : syracuseStep 2556023 = 3834035) B3834035
theorem B1704071 : Blo 1703552 1704071 := bstep (se 1 (by rfl) ⟨1278053, by rfl⟩ : syracuseStep 1704071 = 2556107) B2556107
theorem B2556047 : Blo 1703552 2556047 := bstep (se 1 (by rfl) ⟨1917035, by rfl⟩ : syracuseStep 2556047 = 3834071) B3834071
theorem B1704079 : Blo 1703552 1704079 := bstep (se 1 (by rfl) ⟨1278059, by rfl⟩ : syracuseStep 1704079 = 2556119) B2556119
theorem B2556089 : Blo 1703552 2556089 := bstep (se 2 (by rfl) ⟨958533, by rfl⟩ : syracuseStep 2556089 = 1917067) B1917067
theorem B1704123 : Blo 1703552 1704123 := bstep (se 1 (by rfl) ⟨1278092, by rfl⟩ : syracuseStep 1704123 = 2556185) B2556185
theorem B2556167 : Blo 1703552 2556167 := bstep (se 1 (by rfl) ⟨1917125, by rfl⟩ : syracuseStep 2556167 = 3834251) B3834251
theorem B1704199 : Blo 1703552 1704199 := bstep (se 1 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 1704199 = 2556299) B2556299
theorem B1704207 : Blo 1703552 1704207 := bstep (se 1 (by rfl) ⟨1278155, by rfl⟩ : syracuseStep 1704207 = 2556311) B2556311
theorem B2556203 : Blo 1703552 2556203 := bstep (se 1 (by rfl) ⟨1917152, by rfl⟩ : syracuseStep 2556203 = 3834305) B3834305
theorem B1704251 : Blo 1703552 1704251 := bstep (se 1 (by rfl) ⟨1278188, by rfl⟩ : syracuseStep 1704251 = 2556377) B2556377
theorem B2556233 : Blo 1703552 2556233 := bstep (se 2 (by rfl) ⟨958587, by rfl⟩ : syracuseStep 2556233 = 1917175) B1917175
theorem B2875783 : Blo 1703552 2875783 := bstep (se 1 (by rfl) ⟨2156837, by rfl⟩ : syracuseStep 2875783 = 4313675) B4313675
theorem B1917319 : Blo 1703552 1917319 := bstep (se 1 (by rfl) ⟨1437989, by rfl⟩ : syracuseStep 1917319 = 2875979) B2875979
theorem B1704327 : Blo 1703552 1704327 := bstep (se 1 (by rfl) ⟨1278245, by rfl⟩ : syracuseStep 1704327 = 2556491) B2556491
theorem B1704335 : Blo 1703552 1704335 := bstep (se 1 (by rfl) ⟨1278251, by rfl⟩ : syracuseStep 1704335 = 2556503) B2556503
theorem B2556347 : Blo 1703552 2556347 := bstep (se 1 (by rfl) ⟨1917260, by rfl⟩ : syracuseStep 2556347 = 3834521) B3834521
theorem B1704379 : Blo 1703552 1704379 := bstep (se 1 (by rfl) ⟨1278284, by rfl⟩ : syracuseStep 1704379 = 2556569) B2556569
theorem B10502621 : Blo 1703552 10502621 := bstep (se 3 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 10502621 = 3938483) B3938483
theorem B2556407 : Blo 1703552 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B1704455 : Blo 1703552 1704455 := bstep (se 1 (by rfl) ⟨1278341, by rfl⟩ : syracuseStep 1704455 = 2556683) B2556683
theorem B2556431 : Blo 1703552 2556431 := bstep (se 1 (by rfl) ⟨1917323, by rfl⟩ : syracuseStep 2556431 = 3834647) B3834647
theorem B1704463 : Blo 1703552 1704463 := bstep (se 1 (by rfl) ⟨1278347, by rfl⟩ : syracuseStep 1704463 = 2556695) B2556695
theorem B2556473 : Blo 1703552 2556473 := bstep (se 2 (by rfl) ⟨958677, by rfl⟩ : syracuseStep 2556473 = 1917355) B1917355
theorem B1917499 : Blo 1703552 1917499 := bstep (se 1 (by rfl) ⟨1438124, by rfl⟩ : syracuseStep 1917499 = 2876249) B2876249
theorem B1704507 : Blo 1703552 1704507 := bstep (se 1 (by rfl) ⟨1278380, by rfl⟩ : syracuseStep 1704507 = 2556761) B2556761
theorem B3236411 : Blo 1703552 3236411 := bstep (se 1 (by rfl) ⟨2427308, by rfl⟩ : syracuseStep 3236411 = 4854617) B4854617
theorem B19407437 : Blo 1703552 19407437 := bstep (se 3 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 19407437 = 7277789) B7277789
theorem B3834503 : Blo 1703552 3834503 := bstep (se 1 (by rfl) ⟨2875877, by rfl⟩ : syracuseStep 3834503 = 5751755) B5751755
theorem B2556551 : Blo 1703552 2556551 := bstep (se 1 (by rfl) ⟨1917413, by rfl⟩ : syracuseStep 2556551 = 3834827) B3834827
theorem B1704583 : Blo 1703552 1704583 := bstep (se 1 (by rfl) ⟨1278437, by rfl⟩ : syracuseStep 1704583 = 2556875) B2556875
theorem B1704591 : Blo 1703552 1704591 := bstep (se 1 (by rfl) ⟨1278443, by rfl⟩ : syracuseStep 1704591 = 2556887) B2556887
theorem B2556587 : Blo 1703552 2556587 := bstep (se 1 (by rfl) ⟨1917440, by rfl⟩ : syracuseStep 2556587 = 3834881) B3834881
theorem B1704635 : Blo 1703552 1704635 := bstep (se 1 (by rfl) ⟨1278476, by rfl⟩ : syracuseStep 1704635 = 2556953) B2556953
theorem B2556617 : Blo 1703552 2556617 := bstep (se 2 (by rfl) ⟨958731, by rfl⟩ : syracuseStep 2556617 = 1917463) B1917463
theorem B1704711 : Blo 1703552 1704711 := bstep (se 1 (by rfl) ⟨1278533, by rfl⟩ : syracuseStep 1704711 = 2557067) B2557067
theorem B1704719 : Blo 1703552 1704719 := bstep (se 1 (by rfl) ⟨1278539, by rfl⟩ : syracuseStep 1704719 = 2557079) B2557079
theorem B3834683 : Blo 1703552 3834683 := bstep (se 1 (by rfl) ⟨2876012, by rfl⟩ : syracuseStep 3834683 = 5752025) B5752025
theorem B2556731 : Blo 1703552 2556731 := bstep (se 1 (by rfl) ⟨1917548, by rfl⟩ : syracuseStep 2556731 = 3835097) B3835097
theorem B1704763 : Blo 1703552 1704763 := bstep (se 1 (by rfl) ⟨1278572, by rfl⟩ : syracuseStep 1704763 = 2557145) B2557145
theorem B2556791 : Blo 1703552 2556791 := bstep (se 1 (by rfl) ⟨1917593, by rfl⟩ : syracuseStep 2556791 = 3835187) B3835187
theorem B10363783 : Blo 1703552 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B1704839 : Blo 1703552 1704839 := bstep (se 1 (by rfl) ⟨1278629, by rfl⟩ : syracuseStep 1704839 = 2557259) B2557259
theorem B2556815 : Blo 1703552 2556815 := bstep (se 1 (by rfl) ⟨1917611, by rfl⟩ : syracuseStep 2556815 = 3835223) B3835223
theorem B1704847 : Blo 1703552 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B3834809 : Blo 1703552 3834809 := bstep (se 2 (by rfl) ⟨1438053, by rfl⟩ : syracuseStep 3834809 = 2876107) B2876107
theorem B2556857 : Blo 1703552 2556857 := bstep (se 2 (by rfl) ⟨958821, by rfl⟩ : syracuseStep 2556857 = 1917643) B1917643
theorem B1704891 : Blo 1703552 1704891 := bstep (se 1 (by rfl) ⟨1278668, by rfl⟩ : syracuseStep 1704891 = 2557337) B2557337
theorem B8627147 : Blo 1703552 8627147 := bstep (se 1 (by rfl) ⟨6470360, by rfl⟩ : syracuseStep 8627147 = 12940721) B12940721
theorem B56779747 : Blo 1703552 56779747 := bstep (se 1 (by rfl) ⟨42584810, by rfl⟩ : syracuseStep 56779747 = 85169621) B85169621
theorem B2556935 : Blo 1703552 2556935 := bstep (se 1 (by rfl) ⟨1917701, by rfl⟩ : syracuseStep 2556935 = 3835403) B3835403
theorem B1704967 : Blo 1703552 1704967 := bstep (se 1 (by rfl) ⟨1278725, by rfl⟩ : syracuseStep 1704967 = 2557451) B2557451
theorem B2876431 : Blo 1703552 2876431 := bstep (se 1 (by rfl) ⟨2157323, by rfl⟩ : syracuseStep 2876431 = 4314647) B4314647
theorem B1917967 : Blo 1703552 1917967 := bstep (se 1 (by rfl) ⟨1438475, by rfl⟩ : syracuseStep 1917967 = 2876951) B2876951
theorem B1704975 : Blo 1703552 1704975 := bstep (se 1 (by rfl) ⟨1278731, by rfl⟩ : syracuseStep 1704975 = 2557463) B2557463
theorem B3236897 : Blo 1703552 3236897 := bstep (se 2 (by rfl) ⟨1213836, by rfl⟩ : syracuseStep 3236897 = 2427673) B2427673
theorem B2556971 : Blo 1703552 2556971 := bstep (se 1 (by rfl) ⟨1917728, by rfl⟩ : syracuseStep 2556971 = 3835457) B3835457
theorem B1705019 : Blo 1703552 1705019 := bstep (se 1 (by rfl) ⟨1278764, by rfl⟩ : syracuseStep 1705019 = 2557529) B2557529
theorem B2557001 : Blo 1703552 2557001 := bstep (se 2 (by rfl) ⟨958875, by rfl⟩ : syracuseStep 2557001 = 1917751) B1917751
theorem B38397077 : Blo 1703552 38397077 := bstep (se 6 (by rfl) ⟨899931, by rfl⟩ : syracuseStep 38397077 = 1799863) B1799863
theorem B13821101 : Blo 1703552 13821101 := bstep (se 3 (by rfl) ⟨2591456, by rfl⟩ : syracuseStep 13821101 = 5182913) B5182913
theorem B2557115 : Blo 1703552 2557115 := bstep (se 1 (by rfl) ⟨1917836, by rfl⟩ : syracuseStep 2557115 = 3835673) B3835673
theorem B2557175 : Blo 1703552 2557175 := bstep (se 1 (by rfl) ⟨1917881, by rfl⟩ : syracuseStep 2557175 = 3835763) B3835763
theorem B8627471 : Blo 1703552 8627471 := bstep (se 1 (by rfl) ⟨6470603, by rfl⟩ : syracuseStep 8627471 = 12941207) B12941207
theorem B5752079 : Blo 1703552 5752079 := bstep (se 1 (by rfl) ⟨4314059, by rfl⟩ : syracuseStep 5752079 = 8628119) B8628119
theorem B3835151 : Blo 1703552 3835151 := bstep (se 1 (by rfl) ⟨2876363, by rfl⟩ : syracuseStep 3835151 = 5752727) B5752727
theorem B2557199 : Blo 1703552 2557199 := bstep (se 1 (by rfl) ⟨1917899, by rfl⟩ : syracuseStep 2557199 = 3835799) B3835799
theorem B3835169 : Blo 1703552 3835169 := bstep (se 2 (by rfl) ⟨1438188, by rfl⟩ : syracuseStep 3835169 = 2876377) B2876377
theorem B2557241 : Blo 1703552 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B2729351 : Blo 1703552 2729351 := bstep (se 1 (by rfl) ⟨2047013, by rfl⟩ : syracuseStep 2729351 = 4094027) B4094027
theorem B2557319 : Blo 1703552 2557319 := bstep (se 1 (by rfl) ⟨1917989, by rfl⟩ : syracuseStep 2557319 = 3835979) B3835979
theorem B2557355 : Blo 1703552 2557355 := bstep (se 1 (by rfl) ⟨1918016, by rfl⟩ : syracuseStep 2557355 = 3836033) B3836033
theorem B2557385 : Blo 1703552 2557385 := bstep (se 2 (by rfl) ⟨959019, by rfl⟩ : syracuseStep 2557385 = 1918039) B1918039
theorem B14558723 : Blo 1703552 14558723 := bstep (se 1 (by rfl) ⟨10919042, by rfl⟩ : syracuseStep 14558723 = 21838085) B21838085
theorem B4851211 : Blo 1703552 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B5752349 : Blo 1703552 5752349 := bstep (se 3 (by rfl) ⟨1078565, by rfl⟩ : syracuseStep 5752349 = 2157131) B2157131
theorem B2876971 : Blo 1703552 2876971 := bstep (se 1 (by rfl) ⟨2157728, by rfl⟩ : syracuseStep 2876971 = 4315457) B4315457
theorem B2557499 : Blo 1703552 2557499 := bstep (se 1 (by rfl) ⟨1918124, by rfl⟩ : syracuseStep 2557499 = 3836249) B3836249
theorem B3835511 : Blo 1703552 3835511 := bstep (se 1 (by rfl) ⟨2876633, by rfl⟩ : syracuseStep 3835511 = 5753267) B5753267
theorem B2557559 : Blo 1703552 2557559 := bstep (se 1 (by rfl) ⟨1918169, by rfl⟩ : syracuseStep 2557559 = 3836339) B3836339
theorem B2877113 : Blo 1703552 2877113 := bstep (se 2 (by rfl) ⟨1078917, by rfl⟩ : syracuseStep 2877113 = 2157835) B2157835
theorem B4851485 : Blo 1703552 4851485 := bstep (se 3 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 4851485 = 1819307) B1819307
theorem B3835691 : Blo 1703552 3835691 := bstep (se 1 (by rfl) ⟨2876768, by rfl⟩ : syracuseStep 3835691 = 5753537) B5753537
theorem B4605815 : Blo 1703552 4605815 := bstep (se 1 (by rfl) ⟨3454361, by rfl⟩ : syracuseStep 4605815 = 6908723) B6908723
theorem B582748121 : Blo 1703552 582748121 := bstep (se 2 (by rfl) ⟨218530545, by rfl⟩ : syracuseStep 582748121 = 437061091) B437061091
theorem B3836051 : Blo 1703552 3836051 := bstep (se 1 (by rfl) ⟨2877038, by rfl⟩ : syracuseStep 3836051 = 5754077) B5754077
theorem B4606105 : Blo 1703552 4606105 := bstep (se 2 (by rfl) ⟨1727289, by rfl⟩ : syracuseStep 4606105 = 3454579) B3454579
theorem B12945581 : Blo 1703552 12945581 := bstep (se 3 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 12945581 = 4854593) B4854593
theorem B3836105 : Blo 1703552 3836105 := bstep (se 2 (by rfl) ⟨1438539, by rfl⟩ : syracuseStep 3836105 = 2877079) B2877079
theorem B2156807 : Blo 1703552 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B10922273 : Blo 1703552 10922273 := bstep (se 2 (by rfl) ⟨4095852, by rfl⟩ : syracuseStep 10922273 = 8191705) B8191705
theorem B2427337 : Blo 1703552 2427337 := bstep (se 2 (by rfl) ⟨910251, by rfl⟩ : syracuseStep 2427337 = 1820503) B1820503
theorem B32762353 : Blo 1703552 32762353 := bstep (se 2 (by rfl) ⟨12285882, by rfl⟩ : syracuseStep 32762353 = 24571765) B24571765
theorem B2591275 : Blo 1703552 2591275 := bstep (se 1 (by rfl) ⟨1943456, by rfl⟩ : syracuseStep 2591275 = 3886913) B3886913
theorem B19417643 : Blo 1703552 19417643 := bstep (se 1 (by rfl) ⟨14563232, by rfl⟩ : syracuseStep 19417643 = 29126465) B29126465
theorem B12937805 : Blo 1703552 12937805 := bstep (se 3 (by rfl) ⟨2425838, by rfl⟩ : syracuseStep 12937805 = 4851677) B4851677
theorem B8628929 : Blo 1703552 8628929 := bstep (se 2 (by rfl) ⟨3235848, by rfl⟩ : syracuseStep 8628929 = 6471697) B6471697
theorem B2157455 : Blo 1703552 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B3640211 : Blo 1703552 3640211 := bstep (se 1 (by rfl) ⟨2730158, by rfl⟩ : syracuseStep 3640211 = 5460317) B5460317
theorem B5753753 : Blo 1703552 5753753 := bstep (se 2 (by rfl) ⟨2157657, by rfl⟩ : syracuseStep 5753753 = 4315315) B4315315
theorem B9702443 : Blo 1703552 9702443 := bstep (se 1 (by rfl) ⟨7276832, by rfl⟩ : syracuseStep 9702443 = 14553665) B14553665
theorem B37342295 : Blo 1703552 37342295 := bstep (se 1 (by rfl) ⟨28006721, by rfl⟩ : syracuseStep 37342295 = 56013443) B56013443
theorem B4312217 : Blo 1703552 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B10923245 : Blo 1703552 10923245 := bstep (se 3 (by rfl) ⟨2048108, by rfl⟩ : syracuseStep 10923245 = 4096217) B4096217
theorem B4312379 : Blo 1703552 4312379 := bstep (se 1 (by rfl) ⟨3234284, by rfl⟩ : syracuseStep 4312379 = 6468569) B6468569
theorem B8744345 : Blo 1703552 8744345 := bstep (se 2 (by rfl) ⟨3279129, by rfl⟩ : syracuseStep 8744345 = 6558259) B6558259
theorem B26963405 : Blo 1703552 26963405 := bstep (se 3 (by rfl) ⟨5055638, by rfl⟩ : syracuseStep 26963405 = 10111277) B10111277
theorem B5754455 : Blo 1703552 5754455 := bstep (se 1 (by rfl) ⟨4315841, by rfl⟩ : syracuseStep 5754455 = 8631683) B8631683
theorem B4312723 : Blo 1703552 4312723 := bstep (se 1 (by rfl) ⟨3234542, by rfl⟩ : syracuseStep 4312723 = 6469085) B6469085
theorem B354307841 : Blo 1703552 354307841 := bstep (se 2 (by rfl) ⟨132865440, by rfl⟩ : syracuseStep 354307841 = 265730881) B265730881
theorem B4312865 : Blo 1703552 4312865 := bstep (se 2 (by rfl) ⟨1617324, by rfl⟩ : syracuseStep 4312865 = 3234649) B3234649
theorem B4853591 : Blo 1703552 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B4607891 : Blo 1703552 4607891 := bstep (se 1 (by rfl) ⟨3455918, by rfl⟩ : syracuseStep 4607891 = 6911837) B6911837
theorem B12283811 : Blo 1703552 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B8630225 : Blo 1703552 8630225 := bstep (se 2 (by rfl) ⟨3236334, by rfl⟩ : syracuseStep 8630225 = 6472669) B6472669
theorem B9211907 : Blo 1703552 9211907 := bstep (se 1 (by rfl) ⟨6908930, by rfl⟩ : syracuseStep 9211907 = 13817861) B13817861
theorem B4853819 : Blo 1703552 4853819 := bstep (se 1 (by rfl) ⟨3640364, by rfl⟩ : syracuseStep 4853819 = 7280729) B7280729
theorem B4853945 : Blo 1703552 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B4321721 : Blo 1703552 4321721 := bstep (se 2 (by rfl) ⟨1620645, by rfl⟩ : syracuseStep 4321721 = 3241291) B3241291
theorem B9703901 : Blo 1703552 9703901 := bstep (se 3 (by rfl) ⟨1819481, by rfl⟩ : syracuseStep 9703901 = 3638963) B3638963
theorem B53211829 : Blo 1703552 53211829 := bstep (se 5 (by rfl) ⟨2494304, by rfl⟩ : syracuseStep 53211829 = 4988609) B4988609
theorem B4313857 : Blo 1703552 4313857 := bstep (se 2 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 4313857 = 3235393) B3235393
theorem B7377779 : Blo 1703552 7377779 := bstep (se 1 (by rfl) ⟨5533334, by rfl⟩ : syracuseStep 7377779 = 11066669) B11066669
theorem B12940235 : Blo 1703552 12940235 := bstep (se 1 (by rfl) ⟨9705176, by rfl⟩ : syracuseStep 12940235 = 19410353) B19410353
theorem B7279703 : Blo 1703552 7279703 := bstep (se 1 (by rfl) ⟨5459777, by rfl⟩ : syracuseStep 7279703 = 10919555) B10919555
theorem B14554349 : Blo 1703552 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B6141199 : Blo 1703552 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B3888427 : Blo 1703552 3888427 := bstep (se 1 (by rfl) ⟨2916320, by rfl⟩ : syracuseStep 3888427 = 5832641) B5832641
theorem B4314455 : Blo 1703552 4314455 := bstep (se 1 (by rfl) ⟨3235841, by rfl⟩ : syracuseStep 4314455 = 6471683) B6471683
theorem B4314667 : Blo 1703552 4314667 := bstep (se 1 (by rfl) ⟨3236000, by rfl⟩ : syracuseStep 4314667 = 6472001) B6472001
theorem B4372121 : Blo 1703552 4372121 := bstep (se 2 (by rfl) ⟨1639545, by rfl⟩ : syracuseStep 4372121 = 3279091) B3279091
theorem B4314809 : Blo 1703552 4314809 := bstep (se 2 (by rfl) ⟨1618053, by rfl⟩ : syracuseStep 4314809 = 3236107) B3236107
theorem B10368749 : Blo 1703552 10368749 := bstep (se 3 (by rfl) ⟨1944140, by rfl⟩ : syracuseStep 10368749 = 3888281) B3888281
theorem B15546113 : Blo 1703552 15546113 := bstep (se 2 (by rfl) ⟨5829792, by rfl⟩ : syracuseStep 15546113 = 11659585) B11659585
theorem B3462955 : Blo 1703552 3462955 := bstep (se 1 (by rfl) ⟨2597216, by rfl⟩ : syracuseStep 3462955 = 5194433) B5194433
theorem B6559811 : Blo 1703552 6559811 := bstep (se 1 (by rfl) ⟨4919858, by rfl⟩ : syracuseStep 6559811 = 9839717) B9839717
theorem B4094219 : Blo 1703552 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B11663939 : Blo 1703552 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B1727119 : Blo 1703552 1727119 := bstep (se 1 (by rfl) ⟨1295339, by rfl⟩ : syracuseStep 1727119 = 2590679) B2590679
theorem B4315801 : Blo 1703552 4315801 := bstep (se 2 (by rfl) ⟨1618425, by rfl⟩ : syracuseStep 4315801 = 3236851) B3236851
theorem B3234505 : Blo 1703552 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B16382681 : Blo 1703552 16382681 := bstep (se 2 (by rfl) ⟨6143505, by rfl⟩ : syracuseStep 16382681 = 12287011) B12287011
theorem B17726323 : Blo 1703552 17726323 := bstep (se 1 (by rfl) ⟨13294742, by rfl⟩ : syracuseStep 17726323 = 26589485) B26589485
theorem B7773043 : Blo 1703552 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B2104199 : Blo 1703552 2104199 := bstep (se 1 (by rfl) ⟨1578149, by rfl⟩ : syracuseStep 2104199 = 3156299) B3156299
theorem B8625041 : Blo 1703552 8625041 := bstep (se 2 (by rfl) ⟨3234390, by rfl⟩ : syracuseStep 8625041 = 6468781) B6468781
theorem B9706499 : Blo 1703552 9706499 := bstep (se 1 (by rfl) ⟨7279874, by rfl⟩ : syracuseStep 9706499 = 14559749) B14559749
theorem B4152379 : Blo 1703552 4152379 := bstep (se 1 (by rfl) ⟨3114284, by rfl⟩ : syracuseStep 4152379 = 6228569) B6228569
theorem B5184665 : Blo 1703552 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B3833207 : Blo 1703552 3833207 := bstep (se 1 (by rfl) ⟨2874905, by rfl⟩ : syracuseStep 3833207 = 5749811) B5749811
theorem B7380409 : Blo 1703552 7380409 := bstep (se 2 (by rfl) ⟨2767653, by rfl⟩ : syracuseStep 7380409 = 5535307) B5535307
theorem B2768329 : Blo 1703552 2768329 := bstep (se 2 (by rfl) ⟨1038123, by rfl⟩ : syracuseStep 2768329 = 2076247) B2076247
theorem B19676621 : Blo 1703552 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B2555399 : Blo 1703552 2555399 := bstep (se 1 (by rfl) ⟨1916549, by rfl⟩ : syracuseStep 2555399 = 3833099) B3833099
theorem B6471197 : Blo 1703552 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B2555435 : Blo 1703552 2555435 := bstep (se 1 (by rfl) ⟨1916576, by rfl⟩ : syracuseStep 2555435 = 3833153) B3833153
theorem B3833387 : Blo 1703552 3833387 := bstep (se 1 (by rfl) ⟨2875040, by rfl⟩ : syracuseStep 3833387 = 5750081) B5750081
theorem B7003691 : Blo 1703552 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B6471211 : Blo 1703552 6471211 := bstep (se 1 (by rfl) ⟨4853408, by rfl⟩ : syracuseStep 6471211 = 9706817) B9706817
theorem B2555465 : Blo 1703552 2555465 := bstep (se 2 (by rfl) ⟨958299, by rfl⟩ : syracuseStep 2555465 = 1916599) B1916599
theorem B3456631 : Blo 1703552 3456631 := bstep (se 1 (by rfl) ⟨2592473, by rfl⟩ : syracuseStep 3456631 = 5184947) B5184947
theorem B1703559 : Blo 1703552 1703559 := bstep (se 1 (by rfl) ⟨1277669, by rfl⟩ : syracuseStep 1703559 = 2555339) B2555339
theorem B1703567 : Blo 1703552 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B1703611 : Blo 1703552 1703611 := bstep (se 1 (by rfl) ⟨1277708, by rfl⟩ : syracuseStep 1703611 = 2555417) B2555417
theorem B2555579 : Blo 1703552 2555579 := bstep (se 1 (by rfl) ⟨1916684, by rfl⟩ : syracuseStep 2555579 = 3833369) B3833369
theorem B2875081 : Blo 1703552 2875081 := bstep (se 2 (by rfl) ⟨1078155, by rfl⟩ : syracuseStep 2875081 = 2156311) B2156311
theorem B2555639 : Blo 1703552 2555639 := bstep (se 1 (by rfl) ⟨1916729, by rfl⟩ : syracuseStep 2555639 = 3833459) B3833459
theorem B1703687 : Blo 1703552 1703687 := bstep (se 1 (by rfl) ⟨1277765, by rfl⟩ : syracuseStep 1703687 = 2555531) B2555531
theorem B1703695 : Blo 1703552 1703695 := bstep (se 1 (by rfl) ⟨1277771, by rfl⟩ : syracuseStep 1703695 = 2555543) B2555543
theorem B2555663 : Blo 1703552 2555663 := bstep (se 1 (by rfl) ⟨1916747, by rfl⟩ : syracuseStep 2555663 = 3833495) B3833495
theorem B2555705 : Blo 1703552 2555705 := bstep (se 2 (by rfl) ⟨958389, by rfl⟩ : syracuseStep 2555705 = 1916779) B1916779
theorem B1703739 : Blo 1703552 1703739 := bstep (se 1 (by rfl) ⟨1277804, by rfl⟩ : syracuseStep 1703739 = 2555609) B2555609
theorem B1703815 : Blo 1703552 1703815 := bstep (se 1 (by rfl) ⟨1277861, by rfl⟩ : syracuseStep 1703815 = 2555723) B2555723
theorem B2555783 : Blo 1703552 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B1703823 : Blo 1703552 1703823 := bstep (se 1 (by rfl) ⟨1277867, by rfl⟩ : syracuseStep 1703823 = 2555735) B2555735
theorem B1916815 : Blo 1703552 1916815 := bstep (se 1 (by rfl) ⟨1437611, by rfl⟩ : syracuseStep 1916815 = 2875223) B2875223
theorem B3833747 : Blo 1703552 3833747 := bstep (se 1 (by rfl) ⟨2875310, by rfl⟩ : syracuseStep 3833747 = 5750621) B5750621
theorem B5750675 : Blo 1703552 5750675 := bstep (se 1 (by rfl) ⟨4313006, by rfl⟩ : syracuseStep 5750675 = 8626013) B8626013
theorem B2555819 : Blo 1703552 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B1703867 : Blo 1703552 1703867 := bstep (se 1 (by rfl) ⟨1277900, by rfl⟩ : syracuseStep 1703867 = 2555801) B2555801
theorem B2555849 : Blo 1703552 2555849 := bstep (se 2 (by rfl) ⟨958443, by rfl⟩ : syracuseStep 2555849 = 1916887) B1916887
theorem B3833801 : Blo 1703552 3833801 := bstep (se 2 (by rfl) ⟨1437675, by rfl⟩ : syracuseStep 3833801 = 2875351) B2875351
theorem B12451843 : Blo 1703552 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B1703975 : Blo 1703552 1703975 := bstep (se 1 (by rfl) ⟨1277981, by rfl⟩ : syracuseStep 1703975 = 2555963) B2555963
theorem B3235879 : Blo 1703552 3235879 := bstep (se 1 (by rfl) ⟨2426909, by rfl⟩ : syracuseStep 3235879 = 4853819) B4853819
theorem B1704015 : Blo 1703552 1704015 := bstep (se 1 (by rfl) ⟨1278011, by rfl⟩ : syracuseStep 1704015 = 2556023) B2556023
theorem B1704031 : Blo 1703552 1704031 := bstep (se 1 (by rfl) ⟨1278023, by rfl⟩ : syracuseStep 1704031 = 2556047) B2556047
theorem B1704059 : Blo 1703552 1704059 := bstep (se 1 (by rfl) ⟨1278044, by rfl⟩ : syracuseStep 1704059 = 2556089) B2556089
theorem B3235963 : Blo 1703552 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B1704111 : Blo 1703552 1704111 := bstep (se 1 (by rfl) ⟨1278083, by rfl⟩ : syracuseStep 1704111 = 2556167) B2556167
theorem B1704135 : Blo 1703552 1704135 := bstep (se 1 (by rfl) ⟨1278101, by rfl⟩ : syracuseStep 1704135 = 2556203) B2556203
theorem B1704155 : Blo 1703552 1704155 := bstep (se 1 (by rfl) ⟨1278116, by rfl⟩ : syracuseStep 1704155 = 2556233) B2556233
theorem B1704231 : Blo 1703552 1704231 := bstep (se 1 (by rfl) ⟨1278173, by rfl⟩ : syracuseStep 1704231 = 2556347) B2556347
theorem B1704271 : Blo 1703552 1704271 := bstep (se 1 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 1704271 = 2556407) B2556407
theorem B1704287 : Blo 1703552 1704287 := bstep (se 1 (by rfl) ⟨1278215, by rfl⟩ : syracuseStep 1704287 = 2556431) B2556431
theorem B1704315 : Blo 1703552 1704315 := bstep (se 1 (by rfl) ⟨1278236, by rfl⟩ : syracuseStep 1704315 = 2556473) B2556473
theorem B2556335 : Blo 1703552 2556335 := bstep (se 1 (by rfl) ⟨1917251, by rfl⟩ : syracuseStep 2556335 = 3834503) B3834503
theorem B1704367 : Blo 1703552 1704367 := bstep (se 1 (by rfl) ⟨1278275, by rfl⟩ : syracuseStep 1704367 = 2556551) B2556551
theorem B1704391 : Blo 1703552 1704391 := bstep (se 1 (by rfl) ⟨1278293, by rfl⟩ : syracuseStep 1704391 = 2556587) B2556587
theorem B1704411 : Blo 1703552 1704411 := bstep (se 1 (by rfl) ⟨1278308, by rfl⟩ : syracuseStep 1704411 = 2556617) B2556617
theorem B3834377 : Blo 1703552 3834377 := bstep (se 2 (by rfl) ⟨1437891, by rfl⟩ : syracuseStep 3834377 = 2875783) B2875783
theorem B2556425 : Blo 1703552 2556425 := bstep (se 2 (by rfl) ⟨958659, by rfl⟩ : syracuseStep 2556425 = 1917319) B1917319
theorem B2556455 : Blo 1703552 2556455 := bstep (se 1 (by rfl) ⟨1917341, by rfl⟩ : syracuseStep 2556455 = 3834683) B3834683
theorem B1704487 : Blo 1703552 1704487 := bstep (se 1 (by rfl) ⟨1278365, by rfl⟩ : syracuseStep 1704487 = 2556731) B2556731
theorem B1704527 : Blo 1703552 1704527 := bstep (se 1 (by rfl) ⟨1278395, by rfl⟩ : syracuseStep 1704527 = 2556791) B2556791
theorem B1704543 : Blo 1703552 1704543 := bstep (se 1 (by rfl) ⟨1278407, by rfl⟩ : syracuseStep 1704543 = 2556815) B2556815
theorem B3236449 : Blo 1703552 3236449 := bstep (se 2 (by rfl) ⟨1213668, by rfl⟩ : syracuseStep 3236449 = 2427337) B2427337
theorem B2556539 : Blo 1703552 2556539 := bstep (se 1 (by rfl) ⟨1917404, by rfl⟩ : syracuseStep 2556539 = 3834809) B3834809
theorem B1704571 : Blo 1703552 1704571 := bstep (se 1 (by rfl) ⟨1278428, by rfl⟩ : syracuseStep 1704571 = 2556857) B2556857
theorem B8626823 : Blo 1703552 8626823 := bstep (se 1 (by rfl) ⟨6470117, by rfl⟩ : syracuseStep 8626823 = 12940235) B12940235
theorem B5751431 : Blo 1703552 5751431 := bstep (se 1 (by rfl) ⟨4313573, by rfl⟩ : syracuseStep 5751431 = 8627147) B8627147
theorem B1704623 : Blo 1703552 1704623 := bstep (se 1 (by rfl) ⟨1278467, by rfl⟩ : syracuseStep 1704623 = 2556935) B2556935
theorem B5751485 : Blo 1703552 5751485 := bstep (se 3 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 5751485 = 2156807) B2156807
theorem B1704647 : Blo 1703552 1704647 := bstep (se 1 (by rfl) ⟨1278485, by rfl⟩ : syracuseStep 1704647 = 2556971) B2556971
theorem B1704667 : Blo 1703552 1704667 := bstep (se 1 (by rfl) ⟨1278500, by rfl⟩ : syracuseStep 1704667 = 2557001) B2557001
theorem B2556665 : Blo 1703552 2556665 := bstep (se 2 (by rfl) ⟨958749, by rfl⟩ : syracuseStep 2556665 = 1917499) B1917499
theorem B1704743 : Blo 1703552 1704743 := bstep (se 1 (by rfl) ⟨1278557, by rfl⟩ : syracuseStep 1704743 = 2557115) B2557115
theorem B1704783 : Blo 1703552 1704783 := bstep (se 1 (by rfl) ⟨1278587, by rfl⟩ : syracuseStep 1704783 = 2557175) B2557175
theorem B5751647 : Blo 1703552 5751647 := bstep (se 1 (by rfl) ⟨4313735, by rfl⟩ : syracuseStep 5751647 = 8627471) B8627471
theorem B3834719 : Blo 1703552 3834719 := bstep (se 1 (by rfl) ⟨2876039, by rfl⟩ : syracuseStep 3834719 = 5752079) B5752079
theorem B2556767 : Blo 1703552 2556767 := bstep (se 1 (by rfl) ⟨1917575, by rfl⟩ : syracuseStep 2556767 = 3835151) B3835151
theorem B1704799 : Blo 1703552 1704799 := bstep (se 1 (by rfl) ⟨1278599, by rfl⟩ : syracuseStep 1704799 = 2557199) B2557199
theorem B2302825 : Blo 1703552 2302825 := bstep (se 2 (by rfl) ⟨863559, by rfl⟩ : syracuseStep 2302825 = 1727119) B1727119
theorem B2556779 : Blo 1703552 2556779 := bstep (se 1 (by rfl) ⟨1917584, by rfl⟩ : syracuseStep 2556779 = 3835169) B3835169
theorem B1704827 : Blo 1703552 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B2876303 : Blo 1703552 2876303 := bstep (se 1 (by rfl) ⟨2157227, by rfl⟩ : syracuseStep 2876303 = 4314455) B4314455
theorem B73876373 : Blo 1703552 73876373 := bstep (se 6 (by rfl) ⟨1731477, by rfl⟩ : syracuseStep 73876373 = 3462955) B3462955
theorem B1819567 : Blo 1703552 1819567 := bstep (se 1 (by rfl) ⟨1364675, by rfl⟩ : syracuseStep 1819567 = 2729351) B2729351
theorem B1704879 : Blo 1703552 1704879 := bstep (se 1 (by rfl) ⟨1278659, by rfl⟩ : syracuseStep 1704879 = 2557319) B2557319
theorem B1704903 : Blo 1703552 1704903 := bstep (se 1 (by rfl) ⟨1278677, by rfl⟩ : syracuseStep 1704903 = 2557355) B2557355
theorem B1704923 : Blo 1703552 1704923 := bstep (se 1 (by rfl) ⟨1278692, by rfl⟩ : syracuseStep 1704923 = 2557385) B2557385
theorem B5751809 : Blo 1703552 5751809 := bstep (se 2 (by rfl) ⟨2156928, by rfl⟩ : syracuseStep 5751809 = 4313857) B4313857
theorem B3834899 : Blo 1703552 3834899 := bstep (se 1 (by rfl) ⟨2876174, by rfl⟩ : syracuseStep 3834899 = 5752349) B5752349
theorem B1704999 : Blo 1703552 1704999 := bstep (se 1 (by rfl) ⟨1278749, by rfl⟩ : syracuseStep 1704999 = 2557499) B2557499
theorem B2557007 : Blo 1703552 2557007 := bstep (se 1 (by rfl) ⟨1917755, by rfl⟩ : syracuseStep 2557007 = 3835511) B3835511
theorem B1705039 : Blo 1703552 1705039 := bstep (se 1 (by rfl) ⟨1278779, by rfl⟩ : syracuseStep 1705039 = 2557559) B2557559
theorem B2876539 : Blo 1703552 2876539 := bstep (se 1 (by rfl) ⟨2157404, by rfl⟩ : syracuseStep 2876539 = 4314809) B4314809
theorem B1918075 : Blo 1703552 1918075 := bstep (se 1 (by rfl) ⟨1438556, by rfl⟩ : syracuseStep 1918075 = 2877113) B2877113
theorem B23635097 : Blo 1703552 23635097 := bstep (se 2 (by rfl) ⟨8863161, by rfl⟩ : syracuseStep 23635097 = 17726323) B17726323
theorem B10364057 : Blo 1703552 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B10364075 : Blo 1703552 10364075 := bstep (se 1 (by rfl) ⟨7773056, by rfl⟩ : syracuseStep 10364075 = 15546113) B15546113
theorem B2557127 : Blo 1703552 2557127 := bstep (se 1 (by rfl) ⟨1917845, by rfl⟩ : syracuseStep 2557127 = 3835691) B3835691
theorem B388498747 : Blo 1703552 388498747 := bstep (se 1 (by rfl) ⟨291374060, by rfl⟩ : syracuseStep 388498747 = 582748121) B582748121
theorem B3835241 : Blo 1703552 3835241 := bstep (se 2 (by rfl) ⟨1438215, by rfl⟩ : syracuseStep 3835241 = 2876431) B2876431
theorem B2557289 : Blo 1703552 2557289 := bstep (se 2 (by rfl) ⟨958983, by rfl⟩ : syracuseStep 2557289 = 1917967) B1917967
theorem B2557367 : Blo 1703552 2557367 := bstep (se 1 (by rfl) ⟨1918025, by rfl⟩ : syracuseStep 2557367 = 3836051) B3836051
theorem B2557403 : Blo 1703552 2557403 := bstep (se 1 (by rfl) ⟨1918052, by rfl⟩ : syracuseStep 2557403 = 3836105) B3836105
theorem B2729479 : Blo 1703552 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B12945095 : Blo 1703552 12945095 := bstep (se 1 (by rfl) ⟨9708821, by rfl⟩ : syracuseStep 12945095 = 19417643) B19417643
theorem B7775959 : Blo 1703552 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B5752619 : Blo 1703552 5752619 := bstep (se 1 (by rfl) ⟨4314464, by rfl⟩ : syracuseStep 5752619 = 8628929) B8628929
theorem B10921787 : Blo 1703552 10921787 := bstep (se 1 (by rfl) ⟨8191340, by rfl⟩ : syracuseStep 10921787 = 16382681) B16382681
theorem B9840545 : Blo 1703552 9840545 := bstep (se 2 (by rfl) ⟨3690204, by rfl⟩ : syracuseStep 9840545 = 7380409) B7380409
theorem B2426807 : Blo 1703552 2426807 := bstep (se 1 (by rfl) ⟨1820105, by rfl⟩ : syracuseStep 2426807 = 3640211) B3640211
theorem B3835835 : Blo 1703552 3835835 := bstep (se 1 (by rfl) ⟨2876876, by rfl⟩ : syracuseStep 3835835 = 5753753) B5753753
theorem B8628281 : Blo 1703552 8628281 := bstep (se 2 (by rfl) ⟨3235605, by rfl⟩ : syracuseStep 8628281 = 6471211) B6471211
theorem B5752889 : Blo 1703552 5752889 := bstep (se 2 (by rfl) ⟨2157333, by rfl⟩ : syracuseStep 5752889 = 4314667) B4314667
theorem B3835961 : Blo 1703552 3835961 := bstep (se 2 (by rfl) ⟨1438485, by rfl⟩ : syracuseStep 3835961 = 2876971) B2876971
theorem B13117747 : Blo 1703552 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B17975603 : Blo 1703552 17975603 := bstep (se 1 (by rfl) ⟨13481702, by rfl⟩ : syracuseStep 17975603 = 26963405) B26963405
theorem B5753213 : Blo 1703552 5753213 := bstep (se 3 (by rfl) ⟨1078727, by rfl⟩ : syracuseStep 5753213 = 2157455) B2157455
theorem B3836303 : Blo 1703552 3836303 := bstep (se 1 (by rfl) ⟨2877227, by rfl⟩ : syracuseStep 3836303 = 5754455) B5754455
theorem B5753483 : Blo 1703552 5753483 := bstep (se 1 (by rfl) ⟨4315112, by rfl⟩ : syracuseStep 5753483 = 8630225) B8630225
theorem B2157607 : Blo 1703552 2157607 := bstep (se 1 (by rfl) ⟨1618205, by rfl⟩ : syracuseStep 2157607 = 3236411) B3236411
theorem B12938291 : Blo 1703552 12938291 := bstep (se 1 (by rfl) ⟨9703718, by rfl⟩ : syracuseStep 12938291 = 19407437) B19407437
theorem B4918519 : Blo 1703552 4918519 := bstep (se 1 (by rfl) ⟨3688889, by rfl⟩ : syracuseStep 4918519 = 7377779) B7377779
theorem B43683137 : Blo 1703552 43683137 := bstep (se 2 (by rfl) ⟨16381176, by rfl⟩ : syracuseStep 43683137 = 32762353) B32762353
theorem B2157931 : Blo 1703552 2157931 := bstep (se 1 (by rfl) ⟨1618448, by rfl⟩ : syracuseStep 2157931 = 3236897) B3236897
theorem B4853135 : Blo 1703552 4853135 := bstep (se 1 (by rfl) ⟨3639851, by rfl⟩ : syracuseStep 4853135 = 7279703) B7279703
theorem B9702899 : Blo 1703552 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B5754401 : Blo 1703552 5754401 := bstep (se 2 (by rfl) ⟨2157900, by rfl⟩ : syracuseStep 5754401 = 4315801) B4315801
theorem B4312673 : Blo 1703552 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B8630387 : Blo 1703552 8630387 := bstep (se 1 (by rfl) ⟨6472790, by rfl⟩ : syracuseStep 8630387 = 12945581) B12945581
theorem B8188265 : Blo 1703552 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B3691105 : Blo 1703552 3691105 := bstep (se 2 (by rfl) ⟨1384164, by rfl⟩ : syracuseStep 3691105 = 2768329) B2768329
theorem B6468281 : Blo 1703552 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B6468295 : Blo 1703552 6468295 := bstep (se 1 (by rfl) ⟨4851221, by rfl⟩ : syracuseStep 6468295 = 9702443) B9702443
theorem B4608841 : Blo 1703552 4608841 := bstep (se 2 (by rfl) ⟨1728315, by rfl⟩ : syracuseStep 4608841 = 3456631) B3456631
theorem B5829563 : Blo 1703552 5829563 := bstep (se 1 (by rfl) ⟨4372172, by rfl⟩ : syracuseStep 5829563 = 8744345) B8744345
theorem B4314131 : Blo 1703552 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B236205227 : Blo 1703552 236205227 := bstep (se 1 (by rfl) ⟨177153920, by rfl⟩ : syracuseStep 236205227 = 354307841) B354307841
theorem B8189207 : Blo 1703552 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B6141271 : Blo 1703552 6141271 := bstep (se 1 (by rfl) ⟨4605953, by rfl⟩ : syracuseStep 6141271 = 9211907) B9211907
theorem B6141473 : Blo 1703552 6141473 := bstep (se 2 (by rfl) ⟨2303052, by rfl⟩ : syracuseStep 6141473 = 4606105) B4606105
theorem B6469267 : Blo 1703552 6469267 := bstep (se 1 (by rfl) ⟨4851950, by rfl⟩ : syracuseStep 6469267 = 9703901) B9703901
theorem B7001747 : Blo 1703552 7001747 := bstep (se 1 (by rfl) ⟨5251310, by rfl⟩ : syracuseStep 7001747 = 10502621) B10502621
theorem B3455033 : Blo 1703552 3455033 := bstep (se 2 (by rfl) ⟨1295637, by rfl⟩ : syracuseStep 3455033 = 2591275) B2591275
theorem B25598051 : Blo 1703552 25598051 := bstep (se 1 (by rfl) ⟨19198538, by rfl⟩ : syracuseStep 25598051 = 38397077) B38397077
theorem B9214067 : Blo 1703552 9214067 := bstep (se 1 (by rfl) ⟨6910550, by rfl⟩ : syracuseStep 9214067 = 13821101) B13821101
theorem B70949105 : Blo 1703552 70949105 := bstep (se 2 (by rfl) ⟨26605914, by rfl⟩ : syracuseStep 70949105 = 53211829) B53211829
theorem B9705815 : Blo 1703552 9705815 := bstep (se 1 (by rfl) ⟨7279361, by rfl⟩ : syracuseStep 9705815 = 14558723) B14558723
theorem B2914747 : Blo 1703552 2914747 := bstep (se 1 (by rfl) ⟨2186060, by rfl⟩ : syracuseStep 2914747 = 4372121) B4372121
theorem B11524589 : Blo 1703552 11524589 := bstep (se 3 (by rfl) ⟨2160860, by rfl⟩ : syracuseStep 11524589 = 4321721) B4321721
theorem B6912499 : Blo 1703552 6912499 := bstep (se 1 (by rfl) ⟨5184374, by rfl⟩ : syracuseStep 6912499 = 10368749) B10368749
theorem B13818377 : Blo 1703552 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B3234323 : Blo 1703552 3234323 := bstep (se 1 (by rfl) ⟨2425742, by rfl⟩ : syracuseStep 3234323 = 4851485) B4851485
theorem B3070543 : Blo 1703552 3070543 := bstep (se 1 (by rfl) ⟨2302907, by rfl⟩ : syracuseStep 3070543 = 4605815) B4605815
theorem B4373207 : Blo 1703552 4373207 := bstep (se 1 (by rfl) ⟨3279905, by rfl⟩ : syracuseStep 4373207 = 6559811) B6559811
theorem B22444789 : Blo 1703552 22444789 := bstep (se 5 (by rfl) ⟨1052099, by rfl⟩ : syracuseStep 22444789 = 2104199) B2104199
theorem B5536505 : Blo 1703552 5536505 := bstep (se 2 (by rfl) ⟨2076189, by rfl⟩ : syracuseStep 5536505 = 4152379) B4152379
theorem B7281515 : Blo 1703552 7281515 := bstep (se 1 (by rfl) ⟨5461136, by rfl⟩ : syracuseStep 7281515 = 10922273) B10922273
theorem B8625203 : Blo 1703552 8625203 := bstep (se 1 (by rfl) ⟨6468902, by rfl⟩ : syracuseStep 8625203 = 12937805) B12937805
theorem B5184569 : Blo 1703552 5184569 := bstep (se 2 (by rfl) ⟨1944213, by rfl⟩ : syracuseStep 5184569 = 3888427) B3888427
theorem B5750027 : Blo 1703552 5750027 := bstep (se 1 (by rfl) ⟨4312520, by rfl⟩ : syracuseStep 5750027 = 8625041) B8625041
theorem B6470999 : Blo 1703552 6470999 := bstep (se 1 (by rfl) ⟨4853249, by rfl⟩ : syracuseStep 6470999 = 9706499) B9706499
theorem B24894863 : Blo 1703552 24894863 := bstep (se 1 (by rfl) ⟨18671147, by rfl⟩ : syracuseStep 24894863 = 37342295) B37342295
theorem B2874811 : Blo 1703552 2874811 := bstep (se 1 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 2874811 = 4312217) B4312217
theorem B3456443 : Blo 1703552 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B7282163 : Blo 1703552 7282163 := bstep (se 1 (by rfl) ⟨5461622, by rfl⟩ : syracuseStep 7282163 = 10923245) B10923245
theorem B5750297 : Blo 1703552 5750297 := bstep (se 2 (by rfl) ⟨2156361, by rfl⟩ : syracuseStep 5750297 = 4312723) B4312723
theorem B2874919 : Blo 1703552 2874919 := bstep (se 1 (by rfl) ⟨2156189, by rfl⟩ : syracuseStep 2874919 = 4312379) B4312379
theorem B2555471 : Blo 1703552 2555471 := bstep (se 1 (by rfl) ⟨1916603, by rfl⟩ : syracuseStep 2555471 = 3833207) B3833207
theorem B3833441 : Blo 1703552 3833441 := bstep (se 2 (by rfl) ⟨1437540, by rfl⟩ : syracuseStep 3833441 = 2875081) B2875081
theorem B1703599 : Blo 1703552 1703599 := bstep (se 1 (by rfl) ⟨1277699, by rfl⟩ : syracuseStep 1703599 = 2555399) B2555399
theorem B1703623 : Blo 1703552 1703623 := bstep (se 1 (by rfl) ⟨1277717, by rfl⟩ : syracuseStep 1703623 = 2555435) B2555435
theorem B2555591 : Blo 1703552 2555591 := bstep (se 1 (by rfl) ⟨1916693, by rfl⟩ : syracuseStep 2555591 = 3833387) B3833387
theorem B4669127 : Blo 1703552 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B1703643 : Blo 1703552 1703643 := bstep (se 1 (by rfl) ⟨1277732, by rfl⟩ : syracuseStep 1703643 = 2555465) B2555465
theorem B1703719 : Blo 1703552 1703719 := bstep (se 1 (by rfl) ⟨1277789, by rfl⟩ : syracuseStep 1703719 = 2555579) B2555579
theorem B1703759 : Blo 1703552 1703759 := bstep (se 1 (by rfl) ⟨1277819, by rfl⟩ : syracuseStep 1703759 = 2555639) B2555639
theorem B1703775 : Blo 1703552 1703775 := bstep (se 1 (by rfl) ⟨1277831, by rfl⟩ : syracuseStep 1703775 = 2555663) B2555663
theorem B302825317 : Blo 1703552 302825317 := bstep (se 4 (by rfl) ⟨28389873, by rfl⟩ : syracuseStep 302825317 = 56779747) B56779747
theorem B2555753 : Blo 1703552 2555753 := bstep (se 2 (by rfl) ⟨958407, by rfl⟩ : syracuseStep 2555753 = 1916815) B1916815
theorem B2875243 : Blo 1703552 2875243 := bstep (se 1 (by rfl) ⟨2156432, by rfl⟩ : syracuseStep 2875243 = 4312865) B4312865
theorem B1703803 : Blo 1703552 1703803 := bstep (se 1 (by rfl) ⟨1277852, by rfl⟩ : syracuseStep 1703803 = 2555705) B2555705
theorem B3235727 : Blo 1703552 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B1703855 : Blo 1703552 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B2555831 : Blo 1703552 2555831 := bstep (se 1 (by rfl) ⟨1916873, by rfl⟩ : syracuseStep 2555831 = 3833747) B3833747
theorem B3833783 : Blo 1703552 3833783 := bstep (se 1 (by rfl) ⟨2875337, by rfl⟩ : syracuseStep 3833783 = 5750675) B5750675
theorem B3071927 : Blo 1703552 3071927 := bstep (se 1 (by rfl) ⟨2303945, by rfl⟩ : syracuseStep 3071927 = 4607891) B4607891
theorem B1703879 : Blo 1703552 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B1703899 : Blo 1703552 1703899 := bstep (se 1 (by rfl) ⟨1277924, by rfl⟩ : syracuseStep 1703899 = 2555849) B2555849
theorem B2555867 : Blo 1703552 2555867 := bstep (se 1 (by rfl) ⟨1916900, by rfl⟩ : syracuseStep 2555867 = 3833801) B3833801
theorem B1704223 : Blo 1703552 1704223 := bstep (se 1 (by rfl) ⟨1278167, by rfl⟩ : syracuseStep 1704223 = 2556335) B2556335
theorem B2556251 : Blo 1703552 2556251 := bstep (se 1 (by rfl) ⟨1917188, by rfl⟩ : syracuseStep 2556251 = 3834377) B3834377
theorem B1704283 : Blo 1703552 1704283 := bstep (se 1 (by rfl) ⟨1278212, by rfl⟩ : syracuseStep 1704283 = 2556425) B2556425
theorem B1704303 : Blo 1703552 1704303 := bstep (se 1 (by rfl) ⟨1278227, by rfl⟩ : syracuseStep 1704303 = 2556455) B2556455
theorem B17490329 : Blo 1703552 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B1704359 : Blo 1703552 1704359 := bstep (se 1 (by rfl) ⟨1278269, by rfl⟩ : syracuseStep 1704359 = 2556539) B2556539
theorem B5751215 : Blo 1703552 5751215 := bstep (se 1 (by rfl) ⟨4313411, by rfl⟩ : syracuseStep 5751215 = 8626823) B8626823
theorem B3834287 : Blo 1703552 3834287 := bstep (se 1 (by rfl) ⟨2875715, by rfl⟩ : syracuseStep 3834287 = 5751431) B5751431
theorem B3834323 : Blo 1703552 3834323 := bstep (se 1 (by rfl) ⟨2875742, by rfl⟩ : syracuseStep 3834323 = 5751485) B5751485
theorem B1704443 : Blo 1703552 1704443 := bstep (se 1 (by rfl) ⟨1278332, by rfl⟩ : syracuseStep 1704443 = 2556665) B2556665
theorem B3834431 : Blo 1703552 3834431 := bstep (se 1 (by rfl) ⟨2875823, by rfl⟩ : syracuseStep 3834431 = 5751647) B5751647
theorem B2556479 : Blo 1703552 2556479 := bstep (se 1 (by rfl) ⟨1917359, by rfl⟩ : syracuseStep 2556479 = 3834719) B3834719
theorem B1704511 : Blo 1703552 1704511 := bstep (se 1 (by rfl) ⟨1278383, by rfl⟩ : syracuseStep 1704511 = 2556767) B2556767
theorem B1704519 : Blo 1703552 1704519 := bstep (se 1 (by rfl) ⟨1278389, by rfl⟩ : syracuseStep 1704519 = 2556779) B2556779
theorem B1917535 : Blo 1703552 1917535 := bstep (se 1 (by rfl) ⟨1438151, by rfl⟩ : syracuseStep 1917535 = 2876303) B2876303
theorem B49250915 : Blo 1703552 49250915 := bstep (se 1 (by rfl) ⟨36938186, by rfl⟩ : syracuseStep 49250915 = 73876373) B73876373
theorem B9216665 : Blo 1703552 9216665 := bstep (se 2 (by rfl) ⟨3456249, by rfl⟩ : syracuseStep 9216665 = 6912499) B6912499
theorem B3834539 : Blo 1703552 3834539 := bstep (se 1 (by rfl) ⟨2875904, by rfl⟩ : syracuseStep 3834539 = 5751809) B5751809
theorem B2876087 : Blo 1703552 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B2556599 : Blo 1703552 2556599 := bstep (se 1 (by rfl) ⟨1917449, by rfl⟩ : syracuseStep 2556599 = 3834899) B3834899
theorem B1704671 : Blo 1703552 1704671 := bstep (se 1 (by rfl) ⟨1278503, by rfl⟩ : syracuseStep 1704671 = 2557007) B2557007
theorem B1704751 : Blo 1703552 1704751 := bstep (se 1 (by rfl) ⟨1278563, by rfl⟩ : syracuseStep 1704751 = 2557127) B2557127
theorem B2556827 : Blo 1703552 2556827 := bstep (se 1 (by rfl) ⟨1917620, by rfl⟩ : syracuseStep 2556827 = 3835241) B3835241
theorem B1704859 : Blo 1703552 1704859 := bstep (se 1 (by rfl) ⟨1278644, by rfl⟩ : syracuseStep 1704859 = 2557289) B2557289
theorem B1704911 : Blo 1703552 1704911 := bstep (se 1 (by rfl) ⟨1278683, by rfl⟩ : syracuseStep 1704911 = 2557367) B2557367
theorem B1704935 : Blo 1703552 1704935 := bstep (se 1 (by rfl) ⟨1278701, by rfl⟩ : syracuseStep 1704935 = 2557403) B2557403
theorem B29926385 : Blo 1703552 29926385 := bstep (se 2 (by rfl) ⟨11222394, by rfl⟩ : syracuseStep 29926385 = 22444789) B22444789
theorem B6145121 : Blo 1703552 6145121 := bstep (se 2 (by rfl) ⟨2304420, by rfl⟩ : syracuseStep 6145121 = 4608841) B4608841
theorem B3835079 : Blo 1703552 3835079 := bstep (se 1 (by rfl) ⟨2876309, by rfl⟩ : syracuseStep 3835079 = 5752619) B5752619
theorem B2557223 : Blo 1703552 2557223 := bstep (se 1 (by rfl) ⟨1917917, by rfl⟩ : syracuseStep 2557223 = 3835835) B3835835
theorem B36849005 : Blo 1703552 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B5752187 : Blo 1703552 5752187 := bstep (se 1 (by rfl) ⟨4314140, by rfl⟩ : syracuseStep 5752187 = 8628281) B8628281
theorem B3835259 : Blo 1703552 3835259 := bstep (se 1 (by rfl) ⟨2876444, by rfl⟩ : syracuseStep 3835259 = 5752889) B5752889
theorem B2557307 : Blo 1703552 2557307 := bstep (se 1 (by rfl) ⟨1917980, by rfl⟩ : syracuseStep 2557307 = 3835961) B3835961
theorem B2876809 : Blo 1703552 2876809 := bstep (se 2 (by rfl) ⟨1078803, by rfl⟩ : syracuseStep 2876809 = 2157607) B2157607
theorem B17065367 : Blo 1703552 17065367 := bstep (se 1 (by rfl) ⟨12799025, by rfl⟩ : syracuseStep 17065367 = 25598051) B25598051
theorem B3835385 : Blo 1703552 3835385 := bstep (se 2 (by rfl) ⟨1438269, by rfl⟩ : syracuseStep 3835385 = 2876539) B2876539
theorem B2557433 : Blo 1703552 2557433 := bstep (se 2 (by rfl) ⟨959037, by rfl⟩ : syracuseStep 2557433 = 1918075) B1918075
theorem B3835475 : Blo 1703552 3835475 := bstep (se 1 (by rfl) ⟨2876606, by rfl⟩ : syracuseStep 3835475 = 5753213) B5753213
theorem B2557535 : Blo 1703552 2557535 := bstep (se 1 (by rfl) ⟨1918151, by rfl⟩ : syracuseStep 2557535 = 3836303) B3836303
theorem B2156215 : Blo 1703552 2156215 := bstep (se 1 (by rfl) ⟨1617161, by rfl⟩ : syracuseStep 2156215 = 3234323) B3234323
theorem B517998329 : Blo 1703552 517998329 := bstep (se 2 (by rfl) ⟨194249373, by rfl⟩ : syracuseStep 517998329 = 388498747) B388498747
theorem B3835655 : Blo 1703552 3835655 := bstep (se 1 (by rfl) ⟨2876741, by rfl⟩ : syracuseStep 3835655 = 5753483) B5753483
theorem B2877241 : Blo 1703552 2877241 := bstep (se 2 (by rfl) ⟨1078965, by rfl⟩ : syracuseStep 2877241 = 2157931) B2157931
theorem B3639305 : Blo 1703552 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B78743573 : Blo 1703552 78743573 := bstep (se 6 (by rfl) ⟨1845552, by rfl⟩ : syracuseStep 78743573 = 3691105) B3691105
theorem B2304295 : Blo 1703552 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B3836267 : Blo 1703552 3836267 := bstep (se 1 (by rfl) ⟨2877200, by rfl⟩ : syracuseStep 3836267 = 5754401) B5754401
theorem B8628605 : Blo 1703552 8628605 := bstep (se 3 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 8628605 = 3235727) B3235727
theorem B5753591 : Blo 1703552 5753591 := bstep (se 1 (by rfl) ⟨4315193, by rfl⟩ : syracuseStep 5753591 = 8630387) B8630387
theorem B5458843 : Blo 1703552 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B4312187 : Blo 1703552 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B3886375 : Blo 1703552 3886375 := bstep (se 1 (by rfl) ⟨2914781, by rfl⟩ : syracuseStep 3886375 = 5829563) B5829563
theorem B15756731 : Blo 1703552 15756731 := bstep (se 1 (by rfl) ⟨11817548, by rfl⟩ : syracuseStep 15756731 = 23635097) B23635097
theorem B6909371 : Blo 1703552 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B6909383 : Blo 1703552 6909383 := bstep (se 1 (by rfl) ⟨5182037, by rfl⟩ : syracuseStep 6909383 = 10364075) B10364075
theorem B157470151 : Blo 1703552 157470151 := bstep (se 1 (by rfl) ⟨118102613, by rfl⟩ : syracuseStep 157470151 = 236205227) B236205227
theorem B5459471 : Blo 1703552 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B8630063 : Blo 1703552 8630063 := bstep (se 1 (by rfl) ⟨6472547, by rfl⟩ : syracuseStep 8630063 = 12945095) B12945095
theorem B19419101 : Blo 1703552 19419101 := bstep (se 3 (by rfl) ⟨3641081, by rfl⟩ : syracuseStep 19419101 = 7282163) B7282163
theorem B6558025 : Blo 1703552 6558025 := bstep (se 2 (by rfl) ⟨2459259, by rfl⟩ : syracuseStep 6558025 = 4918519) B4918519
theorem B8188361 : Blo 1703552 8188361 := bstep (se 2 (by rfl) ⟨3070635, by rfl⟩ : syracuseStep 8188361 = 6141271) B6141271
theorem B3691003 : Blo 1703552 3691003 := bstep (se 1 (by rfl) ⟨2768252, by rfl⟩ : syracuseStep 3691003 = 5536505) B5536505
theorem B4854343 : Blo 1703552 4854343 := bstep (se 1 (by rfl) ⟨3640757, by rfl⟩ : syracuseStep 4854343 = 7281515) B7281515
theorem B4313999 : Blo 1703552 4313999 := bstep (se 1 (by rfl) ⟨3235499, by rfl⟩ : syracuseStep 4313999 = 6470999) B6470999
theorem B9704357 : Blo 1703552 9704357 := bstep (se 4 (by rfl) ⟨909783, by rfl⟩ : syracuseStep 9704357 = 1819567) B1819567
theorem B10367945 : Blo 1703552 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B15545317 : Blo 1703552 15545317 := bstep (se 4 (by rfl) ⟨1457373, by rfl⟩ : syracuseStep 15545317 = 2914747) B2914747
theorem B6468599 : Blo 1703552 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B16602457 : Blo 1703552 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B4314505 : Blo 1703552 4314505 := bstep (se 2 (by rfl) ⟨1617939, by rfl⟩ : syracuseStep 4314505 = 3235879) B3235879
theorem B9213421 : Blo 1703552 9213421 := bstep (se 3 (by rfl) ⟨1727516, by rfl⟩ : syracuseStep 9213421 = 3455033) B3455033
theorem B4314617 : Blo 1703552 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B4094057 : Blo 1703552 4094057 := bstep (se 2 (by rfl) ⟨1535271, by rfl⟩ : syracuseStep 4094057 = 3070543) B3070543
theorem B4315265 : Blo 1703552 4315265 := bstep (se 2 (by rfl) ⟨1618224, by rfl⟩ : syracuseStep 4315265 = 3236449) B3236449
theorem B8624393 : Blo 1703552 8624393 := bstep (se 2 (by rfl) ⟨3234147, by rfl⟩ : syracuseStep 8624393 = 6468295) B6468295
theorem B4094315 : Blo 1703552 4094315 := bstep (se 1 (by rfl) ⟨3070736, by rfl⟩ : syracuseStep 4094315 = 6141473) B6141473
theorem B12941693 : Blo 1703552 12941693 := bstep (se 3 (by rfl) ⟨2426567, by rfl⟩ : syracuseStep 12941693 = 4853135) B4853135
theorem B4667831 : Blo 1703552 4667831 := bstep (se 1 (by rfl) ⟨3500873, by rfl⟩ : syracuseStep 4667831 = 7001747) B7001747
theorem B3070433 : Blo 1703552 3070433 := bstep (se 2 (by rfl) ⟨1151412, by rfl⟩ : syracuseStep 3070433 = 2302825) B2302825
theorem B7281191 : Blo 1703552 7281191 := bstep (se 1 (by rfl) ⟨5460893, by rfl⟩ : syracuseStep 7281191 = 10921787) B10921787
theorem B6560363 : Blo 1703552 6560363 := bstep (se 1 (by rfl) ⟨4920272, by rfl⟩ : syracuseStep 6560363 = 9840545) B9840545
theorem B6142711 : Blo 1703552 6142711 := bstep (se 1 (by rfl) ⟨4607033, by rfl⟩ : syracuseStep 6142711 = 9214067) B9214067
theorem B47299403 : Blo 1703552 47299403 := bstep (se 1 (by rfl) ⟨35474552, by rfl⟩ : syracuseStep 47299403 = 70949105) B70949105
theorem B11983735 : Blo 1703552 11983735 := bstep (se 1 (by rfl) ⟨8987801, by rfl⟩ : syracuseStep 11983735 = 17975603) B17975603
theorem B6470543 : Blo 1703552 6470543 := bstep (se 1 (by rfl) ⟨4852907, by rfl⟩ : syracuseStep 6470543 = 9705815) B9705815
theorem B7683059 : Blo 1703552 7683059 := bstep (se 1 (by rfl) ⟨5762294, by rfl⟩ : syracuseStep 7683059 = 11524589) B11524589
theorem B2915471 : Blo 1703552 2915471 := bstep (se 1 (by rfl) ⟨2186603, by rfl⟩ : syracuseStep 2915471 = 4373207) B4373207
theorem B3833081 : Blo 1703552 3833081 := bstep (se 2 (by rfl) ⟨1437405, by rfl⟩ : syracuseStep 3833081 = 2874811) B2874811
theorem B5750135 : Blo 1703552 5750135 := bstep (se 1 (by rfl) ⟨4312601, by rfl⟩ : syracuseStep 5750135 = 8625203) B8625203
theorem B8625527 : Blo 1703552 8625527 := bstep (se 1 (by rfl) ⟨6469145, by rfl⟩ : syracuseStep 8625527 = 12938291) B12938291
theorem B3456379 : Blo 1703552 3456379 := bstep (se 1 (by rfl) ⟨2592284, by rfl⟩ : syracuseStep 3456379 = 5184569) B5184569
theorem B3833225 : Blo 1703552 3833225 := bstep (se 2 (by rfl) ⟨1437459, by rfl⟩ : syracuseStep 3833225 = 2874919) B2874919
theorem B3833351 : Blo 1703552 3833351 := bstep (se 1 (by rfl) ⟨2875013, by rfl⟩ : syracuseStep 3833351 = 5750027) B5750027
theorem B8625689 : Blo 1703552 8625689 := bstep (se 2 (by rfl) ⟨3234633, by rfl⟩ : syracuseStep 8625689 = 6469267) B6469267
theorem B29122091 : Blo 1703552 29122091 := bstep (se 1 (by rfl) ⟨21841568, by rfl⟩ : syracuseStep 29122091 = 43683137) B43683137
theorem B16596575 : Blo 1703552 16596575 := bstep (se 1 (by rfl) ⟨12447431, by rfl⟩ : syracuseStep 16596575 = 24894863) B24894863
theorem B3833531 : Blo 1703552 3833531 := bstep (se 1 (by rfl) ⟨2875148, by rfl⟩ : syracuseStep 3833531 = 5750297) B5750297
theorem B1703647 : Blo 1703552 1703647 := bstep (se 1 (by rfl) ⟨1277735, by rfl⟩ : syracuseStep 1703647 = 2555471) B2555471
theorem B2555627 : Blo 1703552 2555627 := bstep (se 1 (by rfl) ⟨1916720, by rfl⟩ : syracuseStep 2555627 = 3833441) B3833441
theorem B2875115 : Blo 1703552 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B1703727 : Blo 1703552 1703727 := bstep (se 1 (by rfl) ⟨1277795, by rfl⟩ : syracuseStep 1703727 = 2555591) B2555591
theorem B3112751 : Blo 1703552 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B403767089 : Blo 1703552 403767089 := bstep (se 2 (by rfl) ⟨151412658, by rfl⟩ : syracuseStep 403767089 = 302825317) B302825317
theorem B3833657 : Blo 1703552 3833657 := bstep (se 2 (by rfl) ⟨1437621, by rfl⟩ : syracuseStep 3833657 = 2875243) B2875243
theorem B6471485 : Blo 1703552 6471485 := bstep (se 3 (by rfl) ⟨1213403, by rfl⟩ : syracuseStep 6471485 = 2426807) B2426807
theorem B1703835 : Blo 1703552 1703835 := bstep (se 1 (by rfl) ⟨1277876, by rfl⟩ : syracuseStep 1703835 = 2555753) B2555753
theorem B1703887 : Blo 1703552 1703887 := bstep (se 1 (by rfl) ⟨1277915, by rfl⟩ : syracuseStep 1703887 = 2555831) B2555831
theorem B2555855 : Blo 1703552 2555855 := bstep (se 1 (by rfl) ⟨1916891, by rfl⟩ : syracuseStep 2555855 = 3833783) B3833783
theorem B2047951 : Blo 1703552 2047951 := bstep (se 1 (by rfl) ⟨1535963, by rfl⟩ : syracuseStep 2047951 = 3071927) B3071927
theorem B1703911 : Blo 1703552 1703911 := bstep (se 1 (by rfl) ⟨1277933, by rfl⟩ : syracuseStep 1703911 = 2555867) B2555867
theorem B1704167 : Blo 1703552 1704167 := bstep (se 1 (by rfl) ⟨1278125, by rfl⟩ : syracuseStep 1704167 = 2556251) B2556251
theorem B3834143 : Blo 1703552 3834143 := bstep (se 1 (by rfl) ⟨2875607, by rfl⟩ : syracuseStep 3834143 = 5751215) B5751215
theorem B2556191 : Blo 1703552 2556191 := bstep (se 1 (by rfl) ⟨1917143, by rfl⟩ : syracuseStep 2556191 = 3834287) B3834287
theorem B2556215 : Blo 1703552 2556215 := bstep (se 1 (by rfl) ⟨1917161, by rfl⟩ : syracuseStep 2556215 = 3834323) B3834323
theorem B7774589 : Blo 1703552 7774589 := bstep (se 3 (by rfl) ⟨1457735, by rfl⟩ : syracuseStep 7774589 = 2915471) B2915471
theorem B2556287 : Blo 1703552 2556287 := bstep (se 1 (by rfl) ⟨1917215, by rfl⟩ : syracuseStep 2556287 = 3834431) B3834431
theorem B1704319 : Blo 1703552 1704319 := bstep (se 1 (by rfl) ⟨1278239, by rfl⟩ : syracuseStep 1704319 = 2556479) B2556479
theorem B32833943 : Blo 1703552 32833943 := bstep (se 1 (by rfl) ⟨24625457, by rfl⟩ : syracuseStep 32833943 = 49250915) B49250915
theorem B6144443 : Blo 1703552 6144443 := bstep (se 1 (by rfl) ⟨4608332, by rfl⟩ : syracuseStep 6144443 = 9216665) B9216665
theorem B2556359 : Blo 1703552 2556359 := bstep (se 1 (by rfl) ⟨1917269, by rfl⟩ : syracuseStep 2556359 = 3834539) B3834539
theorem B1917391 : Blo 1703552 1917391 := bstep (se 1 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 1917391 = 2876087) B2876087
theorem B1704399 : Blo 1703552 1704399 := bstep (se 1 (by rfl) ⟨1278299, by rfl⟩ : syracuseStep 1704399 = 2556599) B2556599
theorem B2875999 : Blo 1703552 2875999 := bstep (se 1 (by rfl) ⟨2156999, by rfl⟩ : syracuseStep 2875999 = 4313999) B4313999
theorem B1704551 : Blo 1703552 1704551 := bstep (se 1 (by rfl) ⟨1278413, by rfl⟩ : syracuseStep 1704551 = 2556827) B2556827
theorem B4096747 : Blo 1703552 4096747 := bstep (se 1 (by rfl) ⟨3072560, by rfl⟩ : syracuseStep 4096747 = 6145121) B6145121
theorem B6472457 : Blo 1703552 6472457 := bstep (se 2 (by rfl) ⟨2427171, by rfl⟩ : syracuseStep 6472457 = 4854343) B4854343
theorem B2556713 : Blo 1703552 2556713 := bstep (se 2 (by rfl) ⟨958767, by rfl⟩ : syracuseStep 2556713 = 1917535) B1917535
theorem B2556719 : Blo 1703552 2556719 := bstep (se 1 (by rfl) ⟨1917539, by rfl⟩ : syracuseStep 2556719 = 3835079) B3835079
theorem B1704815 : Blo 1703552 1704815 := bstep (se 1 (by rfl) ⟨1278611, by rfl⟩ : syracuseStep 1704815 = 2557223) B2557223
theorem B3834791 : Blo 1703552 3834791 := bstep (se 1 (by rfl) ⟨2876093, by rfl⟩ : syracuseStep 3834791 = 5752187) B5752187
theorem B2556839 : Blo 1703552 2556839 := bstep (se 1 (by rfl) ⟨1917629, by rfl⟩ : syracuseStep 2556839 = 3835259) B3835259
theorem B1704871 : Blo 1703552 1704871 := bstep (se 1 (by rfl) ⟨1278653, by rfl⟩ : syracuseStep 1704871 = 2557307) B2557307
theorem B2876411 : Blo 1703552 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B2556923 : Blo 1703552 2556923 := bstep (se 1 (by rfl) ⟨1917692, by rfl⟩ : syracuseStep 2556923 = 3835385) B3835385
theorem B1704955 : Blo 1703552 1704955 := bstep (se 1 (by rfl) ⟨1278716, by rfl⟩ : syracuseStep 1704955 = 2557433) B2557433
theorem B2556983 : Blo 1703552 2556983 := bstep (se 1 (by rfl) ⟨1917737, by rfl⟩ : syracuseStep 2556983 = 3835475) B3835475
theorem B1705023 : Blo 1703552 1705023 := bstep (se 1 (by rfl) ⟨1278767, by rfl⟩ : syracuseStep 1705023 = 2557535) B2557535
theorem B2557103 : Blo 1703552 2557103 := bstep (se 1 (by rfl) ⟨1917827, by rfl⟩ : syracuseStep 2557103 = 3835655) B3835655
theorem B20727089 : Blo 1703552 20727089 := bstep (se 2 (by rfl) ⟨7772658, by rfl⟩ : syracuseStep 20727089 = 15545317) B15545317
theorem B2426203 : Blo 1703552 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B52495715 : Blo 1703552 52495715 := bstep (se 1 (by rfl) ⟨39371786, by rfl⟩ : syracuseStep 52495715 = 78743573) B78743573
theorem B2729371 : Blo 1703552 2729371 := bstep (se 1 (by rfl) ⟨2047028, by rfl⟩ : syracuseStep 2729371 = 4094057) B4094057
theorem B2876843 : Blo 1703552 2876843 := bstep (se 1 (by rfl) ⟨2157632, by rfl⟩ : syracuseStep 2876843 = 4315265) B4315265
theorem B12289573 : Blo 1703552 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B2729543 : Blo 1703552 2729543 := bstep (se 1 (by rfl) ⟨2047157, by rfl⟩ : syracuseStep 2729543 = 4094315) B4094315
theorem B2557511 : Blo 1703552 2557511 := bstep (se 1 (by rfl) ⟨1918133, by rfl⟩ : syracuseStep 2557511 = 3836267) B3836267
theorem B8627795 : Blo 1703552 8627795 := bstep (se 1 (by rfl) ⟨6470846, by rfl⟩ : syracuseStep 8627795 = 12941693) B12941693
theorem B5752403 : Blo 1703552 5752403 := bstep (se 1 (by rfl) ⟨4314302, by rfl⟩ : syracuseStep 5752403 = 8628605) B8628605
theorem B22136609 : Blo 1703552 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B3835727 : Blo 1703552 3835727 := bstep (se 1 (by rfl) ⟨2876795, by rfl⟩ : syracuseStep 3835727 = 5753591) B5753591
theorem B5752673 : Blo 1703552 5752673 := bstep (se 2 (by rfl) ⟨2157252, by rfl⟩ : syracuseStep 5752673 = 4314505) B4314505
theorem B3835745 : Blo 1703552 3835745 := bstep (se 2 (by rfl) ⟨1438404, by rfl⟩ : syracuseStep 3835745 = 2876809) B2876809
theorem B10504487 : Blo 1703552 10504487 := bstep (se 1 (by rfl) ⟨7878365, by rfl⟩ : syracuseStep 10504487 = 15756731) B15756731
theorem B4606247 : Blo 1703552 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B4606255 : Blo 1703552 4606255 := bstep (se 1 (by rfl) ⟨3454691, by rfl⟩ : syracuseStep 4606255 = 6909383) B6909383
theorem B3639647 : Blo 1703552 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B3836321 : Blo 1703552 3836321 := bstep (se 2 (by rfl) ⟨1438620, by rfl⟩ : syracuseStep 3836321 = 2877241) B2877241
theorem B2075167 : Blo 1703552 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B5753375 : Blo 1703552 5753375 := bstep (se 1 (by rfl) ⟨4315031, by rfl⟩ : syracuseStep 5753375 = 8630063) B8630063
theorem B2730601 : Blo 1703552 2730601 := bstep (se 2 (by rfl) ⟨1023975, by rfl⟩ : syracuseStep 2730601 = 2047951) B2047951
theorem B12946067 : Blo 1703552 12946067 := bstep (se 1 (by rfl) ⟨9709550, by rfl⟩ : syracuseStep 12946067 = 19419101) B19419101
theorem B11660219 : Blo 1703552 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B5458907 : Blo 1703552 5458907 := bstep (se 1 (by rfl) ⟨4094180, by rfl⟩ : syracuseStep 5458907 = 8188361) B8188361
theorem B8744033 : Blo 1703552 8744033 := bstep (se 2 (by rfl) ⟨3279012, by rfl⟩ : syracuseStep 8744033 = 6558025) B6558025
theorem B19950923 : Blo 1703552 19950923 := bstep (se 1 (by rfl) ⟨14963192, by rfl⟩ : syracuseStep 19950923 = 29926385) B29926385
theorem B4312399 : Blo 1703552 4312399 := bstep (se 1 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 4312399 = 6468599) B6468599
theorem B15978313 : Blo 1703552 15978313 := bstep (se 2 (by rfl) ⟨5991867, by rfl⟩ : syracuseStep 15978313 = 11983735) B11983735
theorem B7278457 : Blo 1703552 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B8187821 : Blo 1703552 8187821 := bstep (se 3 (by rfl) ⟨1535216, by rfl⟩ : syracuseStep 8187821 = 3070433) B3070433
theorem B17494301 : Blo 1703552 17494301 := bstep (se 3 (by rfl) ⟨3280181, by rfl⟩ : syracuseStep 17494301 = 6560363) B6560363
theorem B4854127 : Blo 1703552 4854127 := bstep (se 1 (by rfl) ⟨3640595, by rfl⟩ : syracuseStep 4854127 = 7281191) B7281191
theorem B5181833 : Blo 1703552 5181833 := bstep (se 2 (by rfl) ⟨1943187, by rfl⟩ : syracuseStep 5181833 = 3886375) B3886375
theorem B4608505 : Blo 1703552 4608505 := bstep (se 2 (by rfl) ⟨1728189, by rfl⟩ : syracuseStep 4608505 = 3456379) B3456379
theorem B4313695 : Blo 1703552 4313695 := bstep (se 1 (by rfl) ⟨3235271, by rfl⟩ : syracuseStep 4313695 = 6470543) B6470543
theorem B12284561 : Blo 1703552 12284561 := bstep (se 2 (by rfl) ⟨4606710, by rfl⟩ : syracuseStep 12284561 = 9213421) B9213421
theorem B11064383 : Blo 1703552 11064383 := bstep (se 1 (by rfl) ⟨8298287, by rfl⟩ : syracuseStep 11064383 = 16596575) B16596575
theorem B269178059 : Blo 1703552 269178059 := bstep (se 1 (by rfl) ⟨201883544, by rfl⟩ : syracuseStep 269178059 = 403767089) B403767089
theorem B4314323 : Blo 1703552 4314323 := bstep (se 1 (by rfl) ⟨3235742, by rfl⟩ : syracuseStep 4314323 = 6471485) B6471485
theorem B6469571 : Blo 1703552 6469571 := bstep (se 1 (by rfl) ⟨4852178, by rfl⟩ : syracuseStep 6469571 = 9704357) B9704357
theorem B6911963 : Blo 1703552 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B4921337 : Blo 1703552 4921337 := bstep (se 2 (by rfl) ⟨1845501, by rfl⟩ : syracuseStep 4921337 = 3691003) B3691003
theorem B24566003 : Blo 1703552 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B11376911 : Blo 1703552 11376911 := bstep (se 1 (by rfl) ⟨8532683, by rfl⟩ : syracuseStep 11376911 = 17065367) B17065367
theorem B8190281 : Blo 1703552 8190281 := bstep (se 2 (by rfl) ⟨3071355, by rfl⟩ : syracuseStep 8190281 = 6142711) B6142711
theorem B345332219 : Blo 1703552 345332219 := bstep (se 1 (by rfl) ⟨258999164, by rfl⟩ : syracuseStep 345332219 = 517998329) B517998329
theorem B5749595 : Blo 1703552 5749595 := bstep (se 1 (by rfl) ⟨4312196, by rfl⟩ : syracuseStep 5749595 = 8624393) B8624393
theorem B3111887 : Blo 1703552 3111887 := bstep (se 1 (by rfl) ⟨2333915, by rfl⟩ : syracuseStep 3111887 = 4667831) B4667831
theorem B209960201 : Blo 1703552 209960201 := bstep (se 2 (by rfl) ⟨78735075, by rfl⟩ : syracuseStep 209960201 = 157470151) B157470151
theorem B2874791 : Blo 1703552 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B2555387 : Blo 1703552 2555387 := bstep (se 1 (by rfl) ⟨1916540, by rfl⟩ : syracuseStep 2555387 = 3833081) B3833081
theorem B126131741 : Blo 1703552 126131741 := bstep (se 3 (by rfl) ⟨23649701, by rfl⟩ : syracuseStep 126131741 = 47299403) B47299403
theorem B2874953 : Blo 1703552 2874953 := bstep (se 2 (by rfl) ⟨1078107, by rfl⟩ : syracuseStep 2874953 = 2156215) B2156215
theorem B3833423 : Blo 1703552 3833423 := bstep (se 1 (by rfl) ⟨2875067, by rfl⟩ : syracuseStep 3833423 = 5750135) B5750135
theorem B5750351 : Blo 1703552 5750351 := bstep (se 1 (by rfl) ⟨4312763, by rfl⟩ : syracuseStep 5750351 = 8625527) B8625527
theorem B2555483 : Blo 1703552 2555483 := bstep (se 1 (by rfl) ⟨1916612, by rfl⟩ : syracuseStep 2555483 = 3833225) B3833225
theorem B2555567 : Blo 1703552 2555567 := bstep (se 1 (by rfl) ⟨1916675, by rfl⟩ : syracuseStep 2555567 = 3833351) B3833351
theorem B5750459 : Blo 1703552 5750459 := bstep (se 1 (by rfl) ⟨4312844, by rfl⟩ : syracuseStep 5750459 = 8625689) B8625689
theorem B19414727 : Blo 1703552 19414727 := bstep (se 1 (by rfl) ⟨14561045, by rfl⟩ : syracuseStep 19414727 = 29122091) B29122091
theorem B2555687 : Blo 1703552 2555687 := bstep (se 1 (by rfl) ⟨1916765, by rfl⟩ : syracuseStep 2555687 = 3833531) B3833531
theorem B1703751 : Blo 1703552 1703751 := bstep (se 1 (by rfl) ⟨1277813, by rfl⟩ : syracuseStep 1703751 = 2555627) B2555627
theorem B1916743 : Blo 1703552 1916743 := bstep (se 1 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 1916743 = 2875115) B2875115
theorem B2555771 : Blo 1703552 2555771 := bstep (se 1 (by rfl) ⟨1916828, by rfl⟩ : syracuseStep 2555771 = 3833657) B3833657
theorem B20488157 : Blo 1703552 20488157 := bstep (se 3 (by rfl) ⟨3841529, by rfl⟩ : syracuseStep 20488157 = 7683059) B7683059
theorem B1703903 : Blo 1703552 1703903 := bstep (se 1 (by rfl) ⟨1277927, by rfl⟩ : syracuseStep 1703903 = 2555855) B2555855
theorem B2556095 : Blo 1703552 2556095 := bstep (se 1 (by rfl) ⟨1917071, by rfl⟩ : syracuseStep 2556095 = 3834143) B3834143
theorem B1704127 : Blo 1703552 1704127 := bstep (se 1 (by rfl) ⟨1278095, by rfl⟩ : syracuseStep 1704127 = 2556191) B2556191
theorem B65544389 : Blo 1703552 65544389 := bstep (se 4 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 65544389 = 12289573) B12289573
theorem B1704143 : Blo 1703552 1704143 := bstep (se 1 (by rfl) ⟨1278107, by rfl⟩ : syracuseStep 1704143 = 2556215) B2556215
theorem B1704191 : Blo 1703552 1704191 := bstep (se 1 (by rfl) ⟨1278143, by rfl⟩ : syracuseStep 1704191 = 2556287) B2556287
theorem B21889295 : Blo 1703552 21889295 := bstep (se 1 (by rfl) ⟨16416971, by rfl⟩ : syracuseStep 21889295 = 32833943) B32833943
theorem B4096295 : Blo 1703552 4096295 := bstep (se 1 (by rfl) ⟨3072221, by rfl⟩ : syracuseStep 4096295 = 6144443) B6144443
theorem B1704239 : Blo 1703552 1704239 := bstep (se 1 (by rfl) ⟨1278179, by rfl⟩ : syracuseStep 1704239 = 2556359) B2556359
theorem B6472169 : Blo 1703552 6472169 := bstep (se 2 (by rfl) ⟨2427063, by rfl⟩ : syracuseStep 6472169 = 4854127) B4854127
theorem B1704475 : Blo 1703552 1704475 := bstep (se 1 (by rfl) ⟨1278356, by rfl⟩ : syracuseStep 1704475 = 2556713) B2556713
theorem B1704479 : Blo 1703552 1704479 := bstep (se 1 (by rfl) ⟨1278359, by rfl⟩ : syracuseStep 1704479 = 2556719) B2556719
theorem B2556521 : Blo 1703552 2556521 := bstep (se 2 (by rfl) ⟨958695, by rfl⟩ : syracuseStep 2556521 = 1917391) B1917391
theorem B2556527 : Blo 1703552 2556527 := bstep (se 1 (by rfl) ⟨1917395, by rfl⟩ : syracuseStep 2556527 = 3834791) B3834791
theorem B1704559 : Blo 1703552 1704559 := bstep (se 1 (by rfl) ⟨1278419, by rfl⟩ : syracuseStep 1704559 = 2556839) B2556839
theorem B6144673 : Blo 1703552 6144673 := bstep (se 2 (by rfl) ⟨2304252, by rfl⟩ : syracuseStep 6144673 = 4608505) B4608505
theorem B1917607 : Blo 1703552 1917607 := bstep (se 1 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 1917607 = 2876411) B2876411
theorem B1704615 : Blo 1703552 1704615 := bstep (se 1 (by rfl) ⟨1278461, by rfl⟩ : syracuseStep 1704615 = 2556923) B2556923
theorem B1704655 : Blo 1703552 1704655 := bstep (se 1 (by rfl) ⟨1278491, by rfl⟩ : syracuseStep 1704655 = 2556983) B2556983
theorem B1704735 : Blo 1703552 1704735 := bstep (se 1 (by rfl) ⟨1278551, by rfl⟩ : syracuseStep 1704735 = 2557103) B2557103
theorem B5751593 : Blo 1703552 5751593 := bstep (se 2 (by rfl) ⟨2156847, by rfl⟩ : syracuseStep 5751593 = 4313695) B4313695
theorem B3834665 : Blo 1703552 3834665 := bstep (se 2 (by rfl) ⟨1437999, by rfl⟩ : syracuseStep 3834665 = 2875999) B2875999
theorem B2876215 : Blo 1703552 2876215 := bstep (se 1 (by rfl) ⟨2157161, by rfl⟩ : syracuseStep 2876215 = 4314323) B4314323
theorem B21840749 : Blo 1703552 21840749 := bstep (se 3 (by rfl) ⟨4095140, by rfl⟩ : syracuseStep 21840749 = 8190281) B8190281
theorem B1917895 : Blo 1703552 1917895 := bstep (se 1 (by rfl) ⟨1438421, by rfl⟩ : syracuseStep 1917895 = 2876843) B2876843
theorem B1705007 : Blo 1703552 1705007 := bstep (se 1 (by rfl) ⟨1278755, by rfl⟩ : syracuseStep 1705007 = 2557511) B2557511
theorem B5751863 : Blo 1703552 5751863 := bstep (se 1 (by rfl) ⟨4313897, by rfl⟩ : syracuseStep 5751863 = 8627795) B8627795
theorem B3834935 : Blo 1703552 3834935 := bstep (se 1 (by rfl) ⟨2876201, by rfl⟩ : syracuseStep 3834935 = 5752403) B5752403
theorem B2557151 : Blo 1703552 2557151 := bstep (se 1 (by rfl) ⟨1917863, by rfl⟩ : syracuseStep 2557151 = 3835727) B3835727
theorem B3835115 : Blo 1703552 3835115 := bstep (se 1 (by rfl) ⟨2876336, by rfl⟩ : syracuseStep 3835115 = 5752673) B5752673
theorem B2557163 : Blo 1703552 2557163 := bstep (se 1 (by rfl) ⟨1917872, by rfl⟩ : syracuseStep 2557163 = 3835745) B3835745
theorem B16377335 : Blo 1703552 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B2426431 : Blo 1703552 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B2557547 : Blo 1703552 2557547 := bstep (se 1 (by rfl) ⟨1918160, by rfl⟩ : syracuseStep 2557547 = 3836321) B3836321
theorem B3835583 : Blo 1703552 3835583 := bstep (se 1 (by rfl) ⟨2876687, by rfl⟩ : syracuseStep 3835583 = 5753375) B5753375
theorem B3639161 : Blo 1703552 3639161 := bstep (se 2 (by rfl) ⟨1364685, by rfl⟩ : syracuseStep 3639161 = 2729371) B2729371
theorem B2074591 : Blo 1703552 2074591 := bstep (se 1 (by rfl) ⟨1555943, by rfl⟩ : syracuseStep 2074591 = 3111887) B3111887
theorem B3639271 : Blo 1703552 3639271 := bstep (se 1 (by rfl) ⟨2729453, by rfl⟩ : syracuseStep 3639271 = 5458907) B5458907
theorem B5458547 : Blo 1703552 5458547 := bstep (se 1 (by rfl) ⟨4093910, by rfl⟩ : syracuseStep 5458547 = 8187821) B8187821
theorem B13658771 : Blo 1703552 13658771 := bstep (se 1 (by rfl) ⟨10244078, by rfl⟩ : syracuseStep 13658771 = 20488157) B20488157
theorem B7376255 : Blo 1703552 7376255 := bstep (se 1 (by rfl) ⟨5532191, by rfl⟩ : syracuseStep 7376255 = 11064383) B11064383
theorem B3640801 : Blo 1703552 3640801 := bstep (se 2 (by rfl) ⟨1365300, by rfl⟩ : syracuseStep 3640801 = 2730601) B2730601
theorem B139988573 : Blo 1703552 139988573 := bstep (se 3 (by rfl) ⟨26247857, by rfl⟩ : syracuseStep 139988573 = 52495715) B52495715
theorem B4313047 : Blo 1703552 4313047 := bstep (se 1 (by rfl) ⟨3234785, by rfl⟩ : syracuseStep 4313047 = 6469571) B6469571
theorem B4607975 : Blo 1703552 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B7278781 : Blo 1703552 7278781 := bstep (se 3 (by rfl) ⟨1364771, by rfl⟩ : syracuseStep 7278781 = 2729543) B2729543
theorem B8630711 : Blo 1703552 8630711 := bstep (se 1 (by rfl) ⟨6473033, by rfl⟩ : syracuseStep 8630711 = 12946067) B12946067
theorem B12939749 : Blo 1703552 12939749 := bstep (se 4 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 12939749 = 2426203) B2426203
theorem B5829355 : Blo 1703552 5829355 := bstep (se 1 (by rfl) ⟨4372016, by rfl⟩ : syracuseStep 5829355 = 8744033) B8744033
theorem B139973467 : Blo 1703552 139973467 := bstep (se 1 (by rfl) ⟨104980100, by rfl⟩ : syracuseStep 139973467 = 209960201) B209960201
theorem B13300615 : Blo 1703552 13300615 := bstep (se 1 (by rfl) ⟨9975461, by rfl⟩ : syracuseStep 13300615 = 19950923) B19950923
theorem B84087827 : Blo 1703552 84087827 := bstep (se 1 (by rfl) ⟨63065870, by rfl⟩ : syracuseStep 84087827 = 126131741) B126131741
theorem B21304417 : Blo 1703552 21304417 := bstep (se 2 (by rfl) ⟨7989156, by rfl⟩ : syracuseStep 21304417 = 15978313) B15978313
theorem B9704609 : Blo 1703552 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B11662867 : Blo 1703552 11662867 := bstep (se 1 (by rfl) ⟨8747150, by rfl⟩ : syracuseStep 11662867 = 17494301) B17494301
theorem B3454555 : Blo 1703552 3454555 := bstep (se 1 (by rfl) ⟨2590916, by rfl⟩ : syracuseStep 3454555 = 5181833) B5181833
theorem B6141673 : Blo 1703552 6141673 := bstep (se 2 (by rfl) ⟨2303127, by rfl⟩ : syracuseStep 6141673 = 4606255) B4606255
theorem B8189707 : Blo 1703552 8189707 := bstep (se 1 (by rfl) ⟨6142280, by rfl⟩ : syracuseStep 8189707 = 12284561) B12284561
theorem B4314971 : Blo 1703552 4314971 := bstep (se 1 (by rfl) ⟨3236228, by rfl⟩ : syracuseStep 4314971 = 6472457) B6472457
theorem B2766889 : Blo 1703552 2766889 := bstep (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) B2075167
theorem B179452039 : Blo 1703552 179452039 := bstep (se 1 (by rfl) ⟨134589029, by rfl⟩ : syracuseStep 179452039 = 269178059) B269178059
theorem B13818059 : Blo 1703552 13818059 := bstep (se 1 (by rfl) ⟨10363544, by rfl⟩ : syracuseStep 13818059 = 20727089) B20727089
theorem B5462329 : Blo 1703552 5462329 := bstep (se 2 (by rfl) ⟨2048373, by rfl⟩ : syracuseStep 5462329 = 4096747) B4096747
theorem B20732237 : Blo 1703552 20732237 := bstep (se 3 (by rfl) ⟨3887294, by rfl⟩ : syracuseStep 20732237 = 7774589) B7774589
theorem B920885917 : Blo 1703552 920885917 := bstep (se 3 (by rfl) ⟨172666109, by rfl⟩ : syracuseStep 920885917 = 345332219) B345332219
theorem B7584607 : Blo 1703552 7584607 := bstep (se 1 (by rfl) ⟨5688455, by rfl⟩ : syracuseStep 7584607 = 11376911) B11376911
theorem B7002991 : Blo 1703552 7002991 := bstep (se 1 (by rfl) ⟨5252243, by rfl⟩ : syracuseStep 7002991 = 10504487) B10504487
theorem B3070831 : Blo 1703552 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B5749865 : Blo 1703552 5749865 := bstep (se 2 (by rfl) ⟨2156199, by rfl⟩ : syracuseStep 5749865 = 4312399) B4312399
theorem B3833063 : Blo 1703552 3833063 := bstep (se 1 (by rfl) ⟨2874797, by rfl⟩ : syracuseStep 3833063 = 5749595) B5749595
theorem B7773479 : Blo 1703552 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B59030957 : Blo 1703552 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B1916527 : Blo 1703552 1916527 := bstep (se 1 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 1916527 = 2874791) B2874791
theorem B1703591 : Blo 1703552 1703591 := bstep (se 1 (by rfl) ⟨1277693, by rfl⟩ : syracuseStep 1703591 = 2555387) B2555387
theorem B1916635 : Blo 1703552 1916635 := bstep (se 1 (by rfl) ⟨1437476, by rfl⟩ : syracuseStep 1916635 = 2874953) B2874953
theorem B2555615 : Blo 1703552 2555615 := bstep (se 1 (by rfl) ⟨1916711, by rfl⟩ : syracuseStep 2555615 = 3833423) B3833423
theorem B3833567 : Blo 1703552 3833567 := bstep (se 1 (by rfl) ⟨2875175, by rfl⟩ : syracuseStep 3833567 = 5750351) B5750351
theorem B1703655 : Blo 1703552 1703655 := bstep (se 1 (by rfl) ⟨1277741, by rfl⟩ : syracuseStep 1703655 = 2555483) B2555483
theorem B2555657 : Blo 1703552 2555657 := bstep (se 2 (by rfl) ⟨958371, by rfl⟩ : syracuseStep 2555657 = 1916743) B1916743
theorem B1703711 : Blo 1703552 1703711 := bstep (se 1 (by rfl) ⟨1277783, by rfl⟩ : syracuseStep 1703711 = 2555567) B2555567
theorem B3833639 : Blo 1703552 3833639 := bstep (se 1 (by rfl) ⟨2875229, by rfl⟩ : syracuseStep 3833639 = 5750459) B5750459
theorem B12943151 : Blo 1703552 12943151 := bstep (se 1 (by rfl) ⟨9707363, by rfl⟩ : syracuseStep 12943151 = 19414727) B19414727
theorem B1703791 : Blo 1703552 1703791 := bstep (se 1 (by rfl) ⟨1277843, by rfl⟩ : syracuseStep 1703791 = 2555687) B2555687
theorem B1703847 : Blo 1703552 1703847 := bstep (se 1 (by rfl) ⟨1277885, by rfl⟩ : syracuseStep 1703847 = 2555771) B2555771
theorem B13123565 : Blo 1703552 13123565 := bstep (se 3 (by rfl) ⟨2460668, by rfl⟩ : syracuseStep 13123565 = 4921337) B4921337
theorem B1704063 : Blo 1703552 1704063 := bstep (se 1 (by rfl) ⟨1278047, by rfl⟩ : syracuseStep 1704063 = 2556095) B2556095
theorem B43696259 : Blo 1703552 43696259 := bstep (se 1 (by rfl) ⟨32772194, by rfl⟩ : syracuseStep 43696259 = 65544389) B65544389
theorem B8626499 : Blo 1703552 8626499 := bstep (se 1 (by rfl) ⟨6469874, by rfl⟩ : syracuseStep 8626499 = 12939749) B12939749
theorem B1704347 : Blo 1703552 1704347 := bstep (se 1 (by rfl) ⟨1278260, by rfl⟩ : syracuseStep 1704347 = 2556521) B2556521
theorem B1704351 : Blo 1703552 1704351 := bstep (se 1 (by rfl) ⟨1278263, by rfl⟩ : syracuseStep 1704351 = 2556527) B2556527
theorem B7283105 : Blo 1703552 7283105 := bstep (se 2 (by rfl) ⟨2731164, by rfl⟩ : syracuseStep 7283105 = 5462329) B5462329
theorem B3834395 : Blo 1703552 3834395 := bstep (se 1 (by rfl) ⟨2875796, by rfl⟩ : syracuseStep 3834395 = 5751593) B5751593
theorem B2556443 : Blo 1703552 2556443 := bstep (se 1 (by rfl) ⟨1917332, by rfl⟩ : syracuseStep 2556443 = 3834665) B3834665
theorem B56058551 : Blo 1703552 56058551 := bstep (se 1 (by rfl) ⟨42043913, by rfl⟩ : syracuseStep 56058551 = 84087827) B84087827
theorem B3834575 : Blo 1703552 3834575 := bstep (se 1 (by rfl) ⟨2875931, by rfl⟩ : syracuseStep 3834575 = 5751863) B5751863
theorem B2556623 : Blo 1703552 2556623 := bstep (se 1 (by rfl) ⟨1917467, by rfl⟩ : syracuseStep 2556623 = 3834935) B3834935
theorem B1704767 : Blo 1703552 1704767 := bstep (se 1 (by rfl) ⟨1278575, by rfl⟩ : syracuseStep 1704767 = 2557151) B2557151
theorem B2556743 : Blo 1703552 2556743 := bstep (se 1 (by rfl) ⟨1917557, by rfl⟩ : syracuseStep 2556743 = 3835115) B3835115
theorem B1704775 : Blo 1703552 1704775 := bstep (se 1 (by rfl) ⟨1278581, by rfl⟩ : syracuseStep 1704775 = 2557163) B2557163
theorem B8192897 : Blo 1703552 8192897 := bstep (se 2 (by rfl) ⟨3072336, by rfl⟩ : syracuseStep 8192897 = 6144673) B6144673
theorem B2556809 : Blo 1703552 2556809 := bstep (se 2 (by rfl) ⟨958803, by rfl⟩ : syracuseStep 2556809 = 1917607) B1917607
theorem B1705031 : Blo 1703552 1705031 := bstep (se 1 (by rfl) ⟨1278773, by rfl⟩ : syracuseStep 1705031 = 2557547) B2557547
theorem B3834953 : Blo 1703552 3834953 := bstep (se 2 (by rfl) ⟨1438107, by rfl⟩ : syracuseStep 3834953 = 2876215) B2876215
theorem B186631289 : Blo 1703552 186631289 := bstep (se 2 (by rfl) ⟨69986733, by rfl⟩ : syracuseStep 186631289 = 139973467) B139973467
theorem B2557055 : Blo 1703552 2557055 := bstep (se 1 (by rfl) ⟨1917791, by rfl⟩ : syracuseStep 2557055 = 3835583) B3835583
theorem B2876647 : Blo 1703552 2876647 := bstep (se 1 (by rfl) ⟨2157485, by rfl⟩ : syracuseStep 2876647 = 4314971) B4314971
theorem B2426107 : Blo 1703552 2426107 := bstep (se 1 (by rfl) ⟨1819580, by rfl⟩ : syracuseStep 2426107 = 3639161) B3639161
theorem B2557193 : Blo 1703552 2557193 := bstep (se 2 (by rfl) ⟨958947, by rfl⟩ : syracuseStep 2557193 = 1917895) B1917895
theorem B13821491 : Blo 1703552 13821491 := bstep (se 1 (by rfl) ⟨10366118, by rfl⟩ : syracuseStep 13821491 = 20732237) B20732237
theorem B15550489 : Blo 1703552 15550489 := bstep (se 2 (by rfl) ⟨5831433, by rfl⟩ : syracuseStep 15550489 = 11662867) B11662867
theorem B4606073 : Blo 1703552 4606073 := bstep (se 2 (by rfl) ⟨1727277, by rfl⟩ : syracuseStep 4606073 = 3454555) B3454555
theorem B4917503 : Blo 1703552 4917503 := bstep (se 1 (by rfl) ⟨3688127, by rfl⟩ : syracuseStep 4917503 = 7376255) B7376255
theorem B93325715 : Blo 1703552 93325715 := bstep (se 1 (by rfl) ⟨69994286, by rfl⟩ : syracuseStep 93325715 = 139988573) B139988573
theorem B8628767 : Blo 1703552 8628767 := bstep (se 1 (by rfl) ⟨6471575, by rfl⟩ : syracuseStep 8628767 = 12943151) B12943151
theorem B4852361 : Blo 1703552 4852361 := bstep (se 2 (by rfl) ⟨1819635, by rfl⟩ : syracuseStep 4852361 = 3639271) B3639271
theorem B3689185 : Blo 1703552 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B14592863 : Blo 1703552 14592863 := bstep (se 1 (by rfl) ⟨10944647, by rfl⟩ : syracuseStep 14592863 = 21889295) B21889295
theorem B2730863 : Blo 1703552 2730863 := bstep (se 1 (by rfl) ⟨2048147, by rfl⟩ : syracuseStep 2730863 = 4096295) B4096295
theorem B5753807 : Blo 1703552 5753807 := bstep (se 1 (by rfl) ⟨4315355, by rfl⟩ : syracuseStep 5753807 = 8630711) B8630711
theorem B14560499 : Blo 1703552 14560499 := bstep (se 1 (by rfl) ⟨10920374, by rfl⟩ : syracuseStep 14560499 = 21840749) B21840749
theorem B10112809 : Blo 1703552 10112809 := bstep (se 2 (by rfl) ⟨3792303, by rfl⟩ : syracuseStep 10112809 = 7584607) B7584607
theorem B32755589 : Blo 1703552 32755589 := bstep (se 4 (by rfl) ⟨3070836, by rfl⟩ : syracuseStep 32755589 = 6141673) B6141673
theorem B28405889 : Blo 1703552 28405889 := bstep (se 2 (by rfl) ⟨10652208, by rfl⟩ : syracuseStep 28405889 = 21304417) B21304417
theorem B9212039 : Blo 1703552 9212039 := bstep (se 1 (by rfl) ⟨6909029, by rfl⟩ : syracuseStep 9212039 = 13818059) B13818059
theorem B9105847 : Blo 1703552 9105847 := bstep (se 1 (by rfl) ⟨6829385, by rfl⟩ : syracuseStep 9105847 = 13658771) B13658771
theorem B4854401 : Blo 1703552 4854401 := bstep (se 2 (by rfl) ⟨1820400, by rfl⟩ : syracuseStep 4854401 = 3640801) B3640801
theorem B5182319 : Blo 1703552 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B11064485 : Blo 1703552 11064485 := bstep (se 4 (by rfl) ⟨1037295, by rfl⟩ : syracuseStep 11064485 = 2074591) B2074591
theorem B239269385 : Blo 1703552 239269385 := bstep (se 2 (by rfl) ⟨89726019, by rfl⟩ : syracuseStep 239269385 = 179452039) B179452039
theorem B9705041 : Blo 1703552 9705041 := bstep (se 2 (by rfl) ⟨3639390, by rfl⟩ : syracuseStep 9705041 = 7278781) B7278781
theorem B4314779 : Blo 1703552 4314779 := bstep (se 1 (by rfl) ⟨3236084, by rfl⟩ : syracuseStep 4314779 = 6472169) B6472169
theorem B6469739 : Blo 1703552 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B1227847889 : Blo 1703552 1227847889 := bstep (se 2 (by rfl) ⟨460442958, by rfl⟩ : syracuseStep 1227847889 = 920885917) B920885917
theorem B7772473 : Blo 1703552 7772473 := bstep (se 2 (by rfl) ⟨2914677, by rfl⟩ : syracuseStep 7772473 = 5829355) B5829355
theorem B10918223 : Blo 1703552 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B9337321 : Blo 1703552 9337321 := bstep (se 2 (by rfl) ⟨3501495, by rfl⟩ : syracuseStep 9337321 = 7002991) B7002991
theorem B4094441 : Blo 1703552 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B17734153 : Blo 1703552 17734153 := bstep (se 2 (by rfl) ⟨6650307, by rfl⟩ : syracuseStep 17734153 = 13300615) B13300615
theorem B14556125 : Blo 1703552 14556125 := bstep (se 3 (by rfl) ⟨2729273, by rfl⟩ : syracuseStep 14556125 = 5458547) B5458547
theorem B3833243 : Blo 1703552 3833243 := bstep (se 1 (by rfl) ⟨2874932, by rfl⟩ : syracuseStep 3833243 = 5749865) B5749865
theorem B3235241 : Blo 1703552 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B2555369 : Blo 1703552 2555369 := bstep (se 2 (by rfl) ⟨958263, by rfl⟩ : syracuseStep 2555369 = 1916527) B1916527
theorem B2555375 : Blo 1703552 2555375 := bstep (se 1 (by rfl) ⟨1916531, by rfl⟩ : syracuseStep 2555375 = 3833063) B3833063
theorem B39353971 : Blo 1703552 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B2555513 : Blo 1703552 2555513 := bstep (se 2 (by rfl) ⟨958317, by rfl⟩ : syracuseStep 2555513 = 1916635) B1916635
theorem B10919609 : Blo 1703552 10919609 := bstep (se 2 (by rfl) ⟨4094853, by rfl⟩ : syracuseStep 10919609 = 8189707) B8189707
theorem B1703743 : Blo 1703552 1703743 := bstep (se 1 (by rfl) ⟨1277807, by rfl⟩ : syracuseStep 1703743 = 2555615) B2555615
theorem B2555711 : Blo 1703552 2555711 := bstep (se 1 (by rfl) ⟨1916783, by rfl⟩ : syracuseStep 2555711 = 3833567) B3833567
theorem B1703771 : Blo 1703552 1703771 := bstep (se 1 (by rfl) ⟨1277828, by rfl⟩ : syracuseStep 1703771 = 2555657) B2555657
theorem B2555759 : Blo 1703552 2555759 := bstep (se 1 (by rfl) ⟨1916819, by rfl⟩ : syracuseStep 2555759 = 3833639) B3833639
theorem B12287933 : Blo 1703552 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B5750729 : Blo 1703552 5750729 := bstep (se 2 (by rfl) ⟨2156523, by rfl⟩ : syracuseStep 5750729 = 4313047) B4313047
theorem B8749043 : Blo 1703552 8749043 := bstep (se 1 (by rfl) ⟨6561782, by rfl⟩ : syracuseStep 8749043 = 13123565) B13123565
theorem B20733985 : Blo 1703552 20733985 := bstep (se 2 (by rfl) ⟨7775244, by rfl⟩ : syracuseStep 20733985 = 15550489) B15550489
theorem B29130839 : Blo 1703552 29130839 := bstep (se 1 (by rfl) ⟨21848129, by rfl⟩ : syracuseStep 29130839 = 43696259) B43696259
theorem B5750999 : Blo 1703552 5750999 := bstep (se 1 (by rfl) ⟨4313249, by rfl⟩ : syracuseStep 5750999 = 8626499) B8626499
theorem B2556263 : Blo 1703552 2556263 := bstep (se 1 (by rfl) ⟨1917197, by rfl⟩ : syracuseStep 2556263 = 3834395) B3834395
theorem B1704295 : Blo 1703552 1704295 := bstep (se 1 (by rfl) ⟨1278221, by rfl⟩ : syracuseStep 1704295 = 2556443) B2556443
theorem B10363297 : Blo 1703552 10363297 := bstep (se 2 (by rfl) ⟨3886236, by rfl⟩ : syracuseStep 10363297 = 7772473) B7772473
theorem B3236267 : Blo 1703552 3236267 := bstep (se 1 (by rfl) ⟨2427200, by rfl⟩ : syracuseStep 3236267 = 4854401) B4854401
theorem B37372367 : Blo 1703552 37372367 := bstep (se 1 (by rfl) ⟨28029275, by rfl⟩ : syracuseStep 37372367 = 56058551) B56058551
theorem B2556383 : Blo 1703552 2556383 := bstep (se 1 (by rfl) ⟨1917287, by rfl⟩ : syracuseStep 2556383 = 3834575) B3834575
theorem B1704415 : Blo 1703552 1704415 := bstep (se 1 (by rfl) ⟨1278311, by rfl⟩ : syracuseStep 1704415 = 2556623) B2556623
theorem B1704495 : Blo 1703552 1704495 := bstep (se 1 (by rfl) ⟨1278371, by rfl⟩ : syracuseStep 1704495 = 2556743) B2556743
theorem B1704539 : Blo 1703552 1704539 := bstep (se 1 (by rfl) ⟨1278404, by rfl⟩ : syracuseStep 1704539 = 2556809) B2556809
theorem B2556635 : Blo 1703552 2556635 := bstep (se 1 (by rfl) ⟨1917476, by rfl⟩ : syracuseStep 2556635 = 3834953) B3834953
theorem B124420859 : Blo 1703552 124420859 := bstep (se 1 (by rfl) ⟨93315644, by rfl⟩ : syracuseStep 124420859 = 186631289) B186631289
theorem B1704703 : Blo 1703552 1704703 := bstep (se 1 (by rfl) ⟨1278527, by rfl⟩ : syracuseStep 1704703 = 2557055) B2557055
theorem B1704795 : Blo 1703552 1704795 := bstep (se 1 (by rfl) ⟨1278596, by rfl⟩ : syracuseStep 1704795 = 2557193) B2557193
theorem B2876519 : Blo 1703552 2876519 := bstep (se 1 (by rfl) ⟨2157389, by rfl⟩ : syracuseStep 2876519 = 4314779) B4314779
theorem B8627309 : Blo 1703552 8627309 := bstep (se 3 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 8627309 = 3235241) B3235241
theorem B3278335 : Blo 1703552 3278335 := bstep (se 1 (by rfl) ⟨2458751, by rfl⟩ : syracuseStep 3278335 = 4917503) B4917503
theorem B3835529 : Blo 1703552 3835529 := bstep (se 2 (by rfl) ⟨1438323, by rfl⟩ : syracuseStep 3835529 = 2876647) B2876647
theorem B2729627 : Blo 1703552 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B5752511 : Blo 1703552 5752511 := bstep (se 1 (by rfl) ⟨4314383, by rfl⟩ : syracuseStep 5752511 = 8628767) B8628767
theorem B1820575 : Blo 1703552 1820575 := bstep (se 1 (by rfl) ⟨1365431, by rfl⟩ : syracuseStep 1820575 = 2730863) B2730863
theorem B5832695 : Blo 1703552 5832695 := bstep (se 1 (by rfl) ⟨4374521, by rfl⟩ : syracuseStep 5832695 = 8749043) B8749043
theorem B3835871 : Blo 1703552 3835871 := bstep (se 1 (by rfl) ⟨2876903, by rfl⟩ : syracuseStep 3835871 = 5753807) B5753807
theorem B52471961 : Blo 1703552 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B38914301 : Blo 1703552 38914301 := bstep (se 3 (by rfl) ⟨7296431, by rfl⟩ : syracuseStep 38914301 = 14592863) B14592863
theorem B48564517 : Blo 1703552 48564517 := bstep (se 4 (by rfl) ⟨4552923, by rfl⟩ : syracuseStep 48564517 = 9105847) B9105847
theorem B23645537 : Blo 1703552 23645537 := bstep (se 2 (by rfl) ⟨8867076, by rfl⟩ : syracuseStep 23645537 = 17734153) B17734153
theorem B4918913 : Blo 1703552 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B4313159 : Blo 1703552 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B818565259 : Blo 1703552 818565259 := bstep (se 1 (by rfl) ⟨613923944, by rfl⟩ : syracuseStep 818565259 = 1227847889) B1227847889
theorem B7278815 : Blo 1703552 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B9704083 : Blo 1703552 9704083 := bstep (se 1 (by rfl) ⟨7278062, by rfl⟩ : syracuseStep 9704083 = 14556125) B14556125
theorem B7279739 : Blo 1703552 7279739 := bstep (se 1 (by rfl) ⟨5459804, by rfl⟩ : syracuseStep 7279739 = 10919609) B10919609
theorem B21837059 : Blo 1703552 21837059 := bstep (se 1 (by rfl) ⟨16377794, by rfl⟩ : syracuseStep 21837059 = 32755589) B32755589
theorem B18937259 : Blo 1703552 18937259 := bstep (se 1 (by rfl) ⟨14202944, by rfl⟩ : syracuseStep 18937259 = 28405889) B28405889
theorem B6141359 : Blo 1703552 6141359 := bstep (se 1 (by rfl) ⟨4606019, by rfl⟩ : syracuseStep 6141359 = 9212039) B9212039
theorem B4855403 : Blo 1703552 4855403 := bstep (se 1 (by rfl) ⟨3641552, by rfl⟩ : syracuseStep 4855403 = 7283105) B7283105
theorem B29505293 : Blo 1703552 29505293 := bstep (se 3 (by rfl) ⟨5532242, by rfl⟩ : syracuseStep 29505293 = 11064485) B11064485
theorem B5461931 : Blo 1703552 5461931 := bstep (se 1 (by rfl) ⟨4096448, by rfl⟩ : syracuseStep 5461931 = 8192897) B8192897
theorem B159512923 : Blo 1703552 159512923 := bstep (se 1 (by rfl) ⟨119634692, by rfl⟩ : syracuseStep 159512923 = 239269385) B239269385
theorem B9214327 : Blo 1703552 9214327 := bstep (se 1 (by rfl) ⟨6910745, by rfl⟩ : syracuseStep 9214327 = 13821491) B13821491
theorem B6470027 : Blo 1703552 6470027 := bstep (se 1 (by rfl) ⟨4852520, by rfl⟩ : syracuseStep 6470027 = 9705041) B9705041
theorem B3070715 : Blo 1703552 3070715 := bstep (se 1 (by rfl) ⟨2303036, by rfl⟩ : syracuseStep 3070715 = 4606073) B4606073
theorem B62217143 : Blo 1703552 62217143 := bstep (se 1 (by rfl) ⟨46662857, by rfl⟩ : syracuseStep 62217143 = 93325715) B93325715
theorem B3234809 : Blo 1703552 3234809 := bstep (se 2 (by rfl) ⟨1213053, by rfl⟩ : syracuseStep 3234809 = 2426107) B2426107
theorem B3234907 : Blo 1703552 3234907 := bstep (se 1 (by rfl) ⟨2426180, by rfl⟩ : syracuseStep 3234907 = 4852361) B4852361
theorem B9706999 : Blo 1703552 9706999 := bstep (se 1 (by rfl) ⟨7280249, by rfl⟩ : syracuseStep 9706999 = 14560499) B14560499
theorem B2555495 : Blo 1703552 2555495 := bstep (se 1 (by rfl) ⟨1916621, by rfl⟩ : syracuseStep 2555495 = 3833243) B3833243
theorem B13819517 : Blo 1703552 13819517 := bstep (se 3 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 13819517 = 5182319) B5182319
theorem B1703579 : Blo 1703552 1703579 := bstep (se 1 (by rfl) ⟨1277684, by rfl⟩ : syracuseStep 1703579 = 2555369) B2555369
theorem B1703583 : Blo 1703552 1703583 := bstep (se 1 (by rfl) ⟨1277687, by rfl⟩ : syracuseStep 1703583 = 2555375) B2555375
theorem B13483745 : Blo 1703552 13483745 := bstep (se 2 (by rfl) ⟨5056404, by rfl⟩ : syracuseStep 13483745 = 10112809) B10112809
theorem B1703675 : Blo 1703552 1703675 := bstep (se 1 (by rfl) ⟨1277756, by rfl⟩ : syracuseStep 1703675 = 2555513) B2555513
theorem B1703807 : Blo 1703552 1703807 := bstep (se 1 (by rfl) ⟨1277855, by rfl⟩ : syracuseStep 1703807 = 2555711) B2555711
theorem B49799045 : Blo 1703552 49799045 := bstep (se 4 (by rfl) ⟨4668660, by rfl⟩ : syracuseStep 49799045 = 9337321) B9337321
theorem B1703839 : Blo 1703552 1703839 := bstep (se 1 (by rfl) ⟨1277879, by rfl⟩ : syracuseStep 1703839 = 2555759) B2555759
theorem B8191955 : Blo 1703552 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B3833819 : Blo 1703552 3833819 := bstep (se 1 (by rfl) ⟨2875364, by rfl⟩ : syracuseStep 3833819 = 5750729) B5750729
theorem B2875439 : Blo 1703552 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B3833999 : Blo 1703552 3833999 := bstep (se 1 (by rfl) ⟨2875499, by rfl⟩ : syracuseStep 3833999 = 5750999) B5750999
theorem B1091420345 : Blo 1703552 1091420345 := bstep (se 2 (by rfl) ⟨409282629, by rfl⟩ : syracuseStep 1091420345 = 818565259) B818565259
theorem B1704175 : Blo 1703552 1704175 := bstep (se 1 (by rfl) ⟨1278131, by rfl⟩ : syracuseStep 1704175 = 2556263) B2556263
theorem B1704255 : Blo 1703552 1704255 := bstep (se 1 (by rfl) ⟨1278191, by rfl⟩ : syracuseStep 1704255 = 2556383) B2556383
theorem B1704423 : Blo 1703552 1704423 := bstep (se 1 (by rfl) ⟨1278317, by rfl⟩ : syracuseStep 1704423 = 2556635) B2556635
theorem B1917679 : Blo 1703552 1917679 := bstep (se 1 (by rfl) ⟨1438259, by rfl⟩ : syracuseStep 1917679 = 2876519) B2876519
theorem B5751539 : Blo 1703552 5751539 := bstep (se 1 (by rfl) ⟨4313654, by rfl⟩ : syracuseStep 5751539 = 8627309) B8627309
theorem B14558039 : Blo 1703552 14558039 := bstep (se 1 (by rfl) ⟨10918529, by rfl⟩ : syracuseStep 14558039 = 21837059) B21837059
theorem B12624839 : Blo 1703552 12624839 := bstep (se 1 (by rfl) ⟨9468629, by rfl⟩ : syracuseStep 12624839 = 18937259) B18937259
theorem B3236935 : Blo 1703552 3236935 := bstep (se 1 (by rfl) ⟨2427701, by rfl⟩ : syracuseStep 3236935 = 4855403) B4855403
theorem B2557019 : Blo 1703552 2557019 := bstep (se 1 (by rfl) ⟨1917764, by rfl⟩ : syracuseStep 2557019 = 3835529) B3835529
theorem B1819751 : Blo 1703552 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B3835007 : Blo 1703552 3835007 := bstep (se 1 (by rfl) ⟨2876255, by rfl⟩ : syracuseStep 3835007 = 5752511) B5752511
theorem B19670195 : Blo 1703552 19670195 := bstep (se 1 (by rfl) ⟨14752646, by rfl⟩ : syracuseStep 19670195 = 29505293) B29505293
theorem B2557247 : Blo 1703552 2557247 := bstep (se 1 (by rfl) ⟨1917935, by rfl⟩ : syracuseStep 2557247 = 3835871) B3835871
theorem B34981307 : Blo 1703552 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B41478095 : Blo 1703552 41478095 := bstep (se 1 (by rfl) ⟨31108571, by rfl⟩ : syracuseStep 41478095 = 62217143) B62217143
theorem B2156539 : Blo 1703552 2156539 := bstep (se 1 (by rfl) ⟨1617404, by rfl⟩ : syracuseStep 2156539 = 3234809) B3234809
theorem B9709733 : Blo 1703552 9709733 := bstep (se 4 (by rfl) ⟨910287, by rfl⟩ : syracuseStep 9709733 = 1820575) B1820575
theorem B15763691 : Blo 1703552 15763691 := bstep (se 1 (by rfl) ⟨11822768, by rfl⟩ : syracuseStep 15763691 = 23645537) B23645537
theorem B3279275 : Blo 1703552 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B8989163 : Blo 1703552 8989163 := bstep (se 1 (by rfl) ⟨6741872, by rfl⟩ : syracuseStep 8989163 = 13483745) B13483745
theorem B4852543 : Blo 1703552 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B2157511 : Blo 1703552 2157511 := bstep (se 1 (by rfl) ⟨1618133, by rfl⟩ : syracuseStep 2157511 = 3236267) B3236267
theorem B64752689 : Blo 1703552 64752689 := bstep (se 2 (by rfl) ⟨24282258, by rfl⟩ : syracuseStep 64752689 = 48564517) B48564517
theorem B212683897 : Blo 1703552 212683897 := bstep (se 2 (by rfl) ⟨79756461, by rfl⟩ : syracuseStep 212683897 = 159512923) B159512923
theorem B82947239 : Blo 1703552 82947239 := bstep (se 1 (by rfl) ⟨62210429, by rfl⟩ : syracuseStep 82947239 = 124420859) B124420859
theorem B103771469 : Blo 1703552 103771469 := bstep (se 3 (by rfl) ⟨19457150, by rfl⟩ : syracuseStep 103771469 = 38914301) B38914301
theorem B4853159 : Blo 1703552 4853159 := bstep (se 1 (by rfl) ⟨3639869, by rfl⟩ : syracuseStep 4853159 = 7279739) B7279739
theorem B12938777 : Blo 1703552 12938777 := bstep (se 2 (by rfl) ⟨4852041, by rfl⟩ : syracuseStep 12938777 = 9704083) B9704083
theorem B99659645 : Blo 1703552 99659645 := bstep (se 3 (by rfl) ⟨18686183, by rfl⟩ : syracuseStep 99659645 = 37372367) B37372367
theorem B3641287 : Blo 1703552 3641287 := bstep (se 1 (by rfl) ⟨2730965, by rfl⟩ : syracuseStep 3641287 = 5461931) B5461931
theorem B4313209 : Blo 1703552 4313209 := bstep (se 2 (by rfl) ⟨1617453, by rfl⟩ : syracuseStep 4313209 = 3234907) B3234907
theorem B4313351 : Blo 1703552 4313351 := bstep (se 1 (by rfl) ⟨3235013, by rfl⟩ : syracuseStep 4313351 = 6470027) B6470027
theorem B8188573 : Blo 1703552 8188573 := bstep (se 3 (by rfl) ⟨1535357, by rfl⟩ : syracuseStep 8188573 = 3070715) B3070715
theorem B4371113 : Blo 1703552 4371113 := bstep (se 2 (by rfl) ⟨1639167, by rfl⟩ : syracuseStep 4371113 = 3278335) B3278335
theorem B132797453 : Blo 1703552 132797453 := bstep (se 3 (by rfl) ⟨24899522, by rfl⟩ : syracuseStep 132797453 = 49799045) B49799045
theorem B9213011 : Blo 1703552 9213011 := bstep (se 1 (by rfl) ⟨6909758, by rfl⟩ : syracuseStep 9213011 = 13819517) B13819517
theorem B21845213 : Blo 1703552 21845213 := bstep (se 3 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 21845213 = 8191955) B8191955
theorem B15553853 : Blo 1703552 15553853 := bstep (se 3 (by rfl) ⟨2916347, by rfl⟩ : syracuseStep 15553853 = 5832695) B5832695
theorem B27645313 : Blo 1703552 27645313 := bstep (se 2 (by rfl) ⟨10366992, by rfl⟩ : syracuseStep 27645313 = 20733985) B20733985
theorem B19420559 : Blo 1703552 19420559 := bstep (se 1 (by rfl) ⟨14565419, by rfl⟩ : syracuseStep 19420559 = 29130839) B29130839
theorem B12285769 : Blo 1703552 12285769 := bstep (se 2 (by rfl) ⟨4607163, by rfl⟩ : syracuseStep 12285769 = 9214327) B9214327
theorem B13817729 : Blo 1703552 13817729 := bstep (se 2 (by rfl) ⟨5181648, by rfl⟩ : syracuseStep 13817729 = 10363297) B10363297
theorem B4094239 : Blo 1703552 4094239 := bstep (se 1 (by rfl) ⟨3070679, by rfl⟩ : syracuseStep 4094239 = 6141359) B6141359
theorem B12942665 : Blo 1703552 12942665 := bstep (se 2 (by rfl) ⟨4853499, by rfl⟩ : syracuseStep 12942665 = 9706999) B9706999
theorem B1703663 : Blo 1703552 1703663 := bstep (se 1 (by rfl) ⟨1277747, by rfl⟩ : syracuseStep 1703663 = 2555495) B2555495
theorem B2555879 : Blo 1703552 2555879 := bstep (se 1 (by rfl) ⟨1916909, by rfl⟩ : syracuseStep 2555879 = 3833819) B3833819
theorem B1916959 : Blo 1703552 1916959 := bstep (se 1 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 1916959 = 2875439) B2875439
theorem B2555999 : Blo 1703552 2555999 := bstep (se 1 (by rfl) ⟨1916999, by rfl⟩ : syracuseStep 2555999 = 3833999) B3833999
theorem B727613563 : Blo 1703552 727613563 := bstep (se 1 (by rfl) ⟨545710172, by rfl⟩ : syracuseStep 727613563 = 1091420345) B1091420345
theorem B5750945 : Blo 1703552 5750945 := bstep (se 2 (by rfl) ⟨2156604, by rfl⟩ : syracuseStep 5750945 = 4313209) B4313209
theorem B2875567 : Blo 1703552 2875567 := bstep (se 1 (by rfl) ⟨2156675, by rfl⟩ : syracuseStep 2875567 = 4313351) B4313351
theorem B3834359 : Blo 1703552 3834359 := bstep (se 1 (by rfl) ⟨2875769, by rfl⟩ : syracuseStep 3834359 = 5751539) B5751539
theorem B1704679 : Blo 1703552 1704679 := bstep (se 1 (by rfl) ⟨1278509, by rfl⟩ : syracuseStep 1704679 = 2557019) B2557019
theorem B2556671 : Blo 1703552 2556671 := bstep (se 1 (by rfl) ⟨1917503, by rfl⟩ : syracuseStep 2556671 = 3835007) B3835007
theorem B1704831 : Blo 1703552 1704831 := bstep (se 1 (by rfl) ⟨1278623, by rfl⟩ : syracuseStep 1704831 = 2557247) B2557247
theorem B2556905 : Blo 1703552 2556905 := bstep (se 2 (by rfl) ⟨958839, by rfl⟩ : syracuseStep 2556905 = 1917679) B1917679
theorem B2876681 : Blo 1703552 2876681 := bstep (se 2 (by rfl) ⟨1078755, by rfl⟩ : syracuseStep 2876681 = 2157511) B2157511
theorem B6473155 : Blo 1703552 6473155 := bstep (se 1 (by rfl) ⟨4854866, by rfl⟩ : syracuseStep 6473155 = 9709733) B9709733
theorem B55298159 : Blo 1703552 55298159 := bstep (se 1 (by rfl) ⟨41473619, by rfl⟩ : syracuseStep 55298159 = 82947239) B82947239
theorem B8628443 : Blo 1703552 8628443 := bstep (se 1 (by rfl) ⟨6471332, by rfl⟩ : syracuseStep 8628443 = 12942665) B12942665
theorem B66439763 : Blo 1703552 66439763 := bstep (se 1 (by rfl) ⟨49829822, by rfl⟩ : syracuseStep 66439763 = 99659645) B99659645
theorem B354126541 : Blo 1703552 354126541 := bstep (se 3 (by rfl) ⟨66398726, by rfl⟩ : syracuseStep 354126541 = 132797453) B132797453
theorem B4852669 : Blo 1703552 4852669 := bstep (se 3 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 4852669 = 1819751) B1819751
theorem B5458985 : Blo 1703552 5458985 := bstep (se 2 (by rfl) ⟨2047119, by rfl⟩ : syracuseStep 5458985 = 4094239) B4094239
theorem B42036509 : Blo 1703552 42036509 := bstep (se 3 (by rfl) ⟨7881845, by rfl⟩ : syracuseStep 42036509 = 15763691) B15763691
theorem B8416559 : Blo 1703552 8416559 := bstep (se 1 (by rfl) ⟨6312419, by rfl⟩ : syracuseStep 8416559 = 12624839) B12624839
theorem B12947039 : Blo 1703552 12947039 := bstep (se 1 (by rfl) ⟨9710279, by rfl⟩ : syracuseStep 12947039 = 19420559) B19420559
theorem B9211819 : Blo 1703552 9211819 := bstep (se 1 (by rfl) ⟨6908864, by rfl⟩ : syracuseStep 9211819 = 13817729) B13817729
theorem B27652063 : Blo 1703552 27652063 := bstep (se 1 (by rfl) ⟨20739047, by rfl⟩ : syracuseStep 27652063 = 41478095) B41478095
theorem B283578529 : Blo 1703552 283578529 := bstep (se 2 (by rfl) ⟨106341948, by rfl⟩ : syracuseStep 283578529 = 212683897) B212683897
theorem B5992775 : Blo 1703552 5992775 := bstep (se 1 (by rfl) ⟨4494581, by rfl⟩ : syracuseStep 5992775 = 8989163) B8989163
theorem B36860417 : Blo 1703552 36860417 := bstep (se 2 (by rfl) ⟨13822656, by rfl⟩ : syracuseStep 36860417 = 27645313) B27645313
theorem B43168459 : Blo 1703552 43168459 := bstep (se 1 (by rfl) ⟨32376344, by rfl⟩ : syracuseStep 43168459 = 64752689) B64752689
theorem B16381025 : Blo 1703552 16381025 := bstep (se 2 (by rfl) ⟨6142884, by rfl⟩ : syracuseStep 16381025 = 12285769) B12285769
theorem B4855049 : Blo 1703552 4855049 := bstep (se 2 (by rfl) ⟨1820643, by rfl⟩ : syracuseStep 4855049 = 3641287) B3641287
theorem B2914075 : Blo 1703552 2914075 := bstep (se 1 (by rfl) ⟨2185556, by rfl⟩ : syracuseStep 2914075 = 4371113) B4371113
theorem B9705359 : Blo 1703552 9705359 := bstep (se 1 (by rfl) ⟨7279019, by rfl⟩ : syracuseStep 9705359 = 14558039) B14558039
theorem B6142007 : Blo 1703552 6142007 := bstep (se 1 (by rfl) ⟨4606505, by rfl⟩ : syracuseStep 6142007 = 9213011) B9213011
theorem B13113463 : Blo 1703552 13113463 := bstep (se 1 (by rfl) ⟨9835097, by rfl⟩ : syracuseStep 13113463 = 19670195) B19670195
theorem B14563475 : Blo 1703552 14563475 := bstep (se 1 (by rfl) ⟨10922606, by rfl⟩ : syracuseStep 14563475 = 21845213) B21845213
theorem B10918097 : Blo 1703552 10918097 := bstep (se 2 (by rfl) ⟨4094286, by rfl⟩ : syracuseStep 10918097 = 8188573) B8188573
theorem B10369235 : Blo 1703552 10369235 := bstep (se 1 (by rfl) ⟨7776926, by rfl⟩ : syracuseStep 10369235 = 15553853) B15553853
theorem B23320871 : Blo 1703552 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B6470057 : Blo 1703552 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B4315913 : Blo 1703552 4315913 := bstep (se 2 (by rfl) ⟨1618467, by rfl⟩ : syracuseStep 4315913 = 3236935) B3236935
theorem B2186183 : Blo 1703552 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B69180979 : Blo 1703552 69180979 := bstep (se 1 (by rfl) ⟨51885734, by rfl⟩ : syracuseStep 69180979 = 103771469) B103771469
theorem B3235439 : Blo 1703552 3235439 := bstep (se 1 (by rfl) ⟨2426579, by rfl⟩ : syracuseStep 3235439 = 4853159) B4853159
theorem B8625851 : Blo 1703552 8625851 := bstep (se 1 (by rfl) ⟨6469388, by rfl⟩ : syracuseStep 8625851 = 12938777) B12938777
theorem B1703919 : Blo 1703552 1703919 := bstep (se 1 (by rfl) ⟨1277939, by rfl⟩ : syracuseStep 1703919 = 2555879) B2555879
theorem B2875385 : Blo 1703552 2875385 := bstep (se 2 (by rfl) ⟨1078269, by rfl⟩ : syracuseStep 2875385 = 2156539) B2156539
theorem B2555945 : Blo 1703552 2555945 := bstep (se 2 (by rfl) ⟨958479, by rfl⟩ : syracuseStep 2555945 = 1916959) B1916959
theorem B1703999 : Blo 1703552 1703999 := bstep (se 1 (by rfl) ⟨1277999, by rfl⟩ : syracuseStep 1703999 = 2555999) B2555999
theorem B3833963 : Blo 1703552 3833963 := bstep (se 1 (by rfl) ⟨2875472, by rfl⟩ : syracuseStep 3833963 = 5750945) B5750945
theorem B3834089 : Blo 1703552 3834089 := bstep (se 2 (by rfl) ⟨1437783, by rfl⟩ : syracuseStep 3834089 = 2875567) B2875567
theorem B2556239 : Blo 1703552 2556239 := bstep (se 1 (by rfl) ⟨1917179, by rfl⟩ : syracuseStep 2556239 = 3834359) B3834359
theorem B1704447 : Blo 1703552 1704447 := bstep (se 1 (by rfl) ⟨1278335, by rfl⟩ : syracuseStep 1704447 = 2556671) B2556671
theorem B1704603 : Blo 1703552 1704603 := bstep (se 1 (by rfl) ⟨1278452, by rfl⟩ : syracuseStep 1704603 = 2556905) B2556905
theorem B10920683 : Blo 1703552 10920683 := bstep (se 1 (by rfl) ⟨8190512, by rfl⟩ : syracuseStep 10920683 = 16381025) B16381025
theorem B1917787 : Blo 1703552 1917787 := bstep (se 1 (by rfl) ⟨1438340, by rfl⟩ : syracuseStep 1917787 = 2876681) B2876681
theorem B3236699 : Blo 1703552 3236699 := bstep (se 1 (by rfl) ⟨2427524, by rfl⟩ : syracuseStep 3236699 = 4855049) B4855049
theorem B57557945 : Blo 1703552 57557945 := bstep (se 2 (by rfl) ⟨21584229, by rfl⟩ : syracuseStep 57557945 = 43168459) B43168459
theorem B36865439 : Blo 1703552 36865439 := bstep (se 1 (by rfl) ⟨27649079, by rfl⟩ : syracuseStep 36865439 = 55298159) B55298159
theorem B9708983 : Blo 1703552 9708983 := bstep (se 1 (by rfl) ⟨7281737, by rfl⟩ : syracuseStep 9708983 = 14563475) B14563475
theorem B15541733 : Blo 1703552 15541733 := bstep (se 4 (by rfl) ⟨1457037, by rfl⟩ : syracuseStep 15541733 = 2914075) B2914075
theorem B5752295 : Blo 1703552 5752295 := bstep (se 1 (by rfl) ⟨4314221, by rfl⟩ : syracuseStep 5752295 = 8628443) B8628443
theorem B2877275 : Blo 1703552 2877275 := bstep (se 1 (by rfl) ⟨2157956, by rfl⟩ : syracuseStep 2877275 = 4315913) B4315913
theorem B3639323 : Blo 1703552 3639323 := bstep (se 1 (by rfl) ⟨2729492, by rfl⟩ : syracuseStep 3639323 = 5458985) B5458985
theorem B2156959 : Blo 1703552 2156959 := bstep (se 1 (by rfl) ⟨1617719, by rfl⟩ : syracuseStep 2156959 = 3235439) B3235439
theorem B12282425 : Blo 1703552 12282425 := bstep (se 2 (by rfl) ⟨4605909, by rfl⟩ : syracuseStep 12282425 = 9211819) B9211819
theorem B16378685 : Blo 1703552 16378685 := bstep (se 3 (by rfl) ⟨3071003, by rfl⟩ : syracuseStep 16378685 = 6142007) B6142007
theorem B17484617 : Blo 1703552 17484617 := bstep (se 2 (by rfl) ⟨6556731, by rfl⟩ : syracuseStep 17484617 = 13113463) B13113463
theorem B378104705 : Blo 1703552 378104705 := bstep (se 2 (by rfl) ⟨141789264, by rfl⟩ : syracuseStep 378104705 = 283578529) B283578529
theorem B7278731 : Blo 1703552 7278731 := bstep (se 1 (by rfl) ⟨5459048, by rfl⟩ : syracuseStep 7278731 = 10918097) B10918097
theorem B4313371 : Blo 1703552 4313371 := bstep (se 1 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 4313371 = 6470057) B6470057
theorem B8630873 : Blo 1703552 8630873 := bstep (se 2 (by rfl) ⟨3236577, by rfl⟩ : syracuseStep 8630873 = 6473155) B6473155
theorem B8631359 : Blo 1703552 8631359 := bstep (se 1 (by rfl) ⟨6473519, by rfl⟩ : syracuseStep 8631359 = 12947039) B12947039
theorem B5829821 : Blo 1703552 5829821 := bstep (se 3 (by rfl) ⟨1093091, by rfl⟩ : syracuseStep 5829821 = 2186183) B2186183
theorem B36869417 : Blo 1703552 36869417 := bstep (se 2 (by rfl) ⟨13826031, by rfl⟩ : syracuseStep 36869417 = 27652063) B27652063
theorem B970151417 : Blo 1703552 970151417 := bstep (se 2 (by rfl) ⟨363806781, by rfl⟩ : syracuseStep 970151417 = 727613563) B727613563
theorem B3995183 : Blo 1703552 3995183 := bstep (se 1 (by rfl) ⟨2996387, by rfl⟩ : syracuseStep 3995183 = 5992775) B5992775
theorem B24573611 : Blo 1703552 24573611 := bstep (se 1 (by rfl) ⟨18430208, by rfl⟩ : syracuseStep 24573611 = 36860417) B36860417
theorem B472168721 : Blo 1703552 472168721 := bstep (se 2 (by rfl) ⟨177063270, by rfl⟩ : syracuseStep 472168721 = 354126541) B354126541
theorem B6470225 : Blo 1703552 6470225 := bstep (se 2 (by rfl) ⟨2426334, by rfl⟩ : syracuseStep 6470225 = 4852669) B4852669
theorem B6470239 : Blo 1703552 6470239 := bstep (se 1 (by rfl) ⟨4852679, by rfl⟩ : syracuseStep 6470239 = 9705359) B9705359
theorem B6912823 : Blo 1703552 6912823 := bstep (se 1 (by rfl) ⟨5184617, by rfl⟩ : syracuseStep 6912823 = 10369235) B10369235
theorem B15547247 : Blo 1703552 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B44293175 : Blo 1703552 44293175 := bstep (se 1 (by rfl) ⟨33219881, by rfl⟩ : syracuseStep 44293175 = 66439763) B66439763
theorem B92241305 : Blo 1703552 92241305 := bstep (se 2 (by rfl) ⟨34590489, by rfl⟩ : syracuseStep 92241305 = 69180979) B69180979
theorem B28024339 : Blo 1703552 28024339 := bstep (se 1 (by rfl) ⟨21018254, by rfl⟩ : syracuseStep 28024339 = 42036509) B42036509
theorem B5611039 : Blo 1703552 5611039 := bstep (se 1 (by rfl) ⟨4208279, by rfl⟩ : syracuseStep 5611039 = 8416559) B8416559
theorem B5750567 : Blo 1703552 5750567 := bstep (se 1 (by rfl) ⟨4312925, by rfl⟩ : syracuseStep 5750567 = 8625851) B8625851
theorem B1916923 : Blo 1703552 1916923 := bstep (se 1 (by rfl) ⟨1437692, by rfl⟩ : syracuseStep 1916923 = 2875385) B2875385
theorem B1703963 : Blo 1703552 1703963 := bstep (se 1 (by rfl) ⟨1277972, by rfl⟩ : syracuseStep 1703963 = 2555945) B2555945
theorem B2555975 : Blo 1703552 2555975 := bstep (se 1 (by rfl) ⟨1916981, by rfl⟩ : syracuseStep 2555975 = 3833963) B3833963
theorem B2556059 : Blo 1703552 2556059 := bstep (se 1 (by rfl) ⟨1917044, by rfl⟩ : syracuseStep 2556059 = 3834089) B3834089
theorem B29925541 : Blo 1703552 29925541 := bstep (se 4 (by rfl) ⟨2805519, by rfl⟩ : syracuseStep 29925541 = 5611039) B5611039
theorem B1704159 : Blo 1703552 1704159 := bstep (se 1 (by rfl) ⟨1278119, by rfl⟩ : syracuseStep 1704159 = 2556239) B2556239
theorem B5751161 : Blo 1703552 5751161 := bstep (se 2 (by rfl) ⟨2156685, by rfl⟩ : syracuseStep 5751161 = 4313371) B4313371
theorem B2875945 : Blo 1703552 2875945 := bstep (se 2 (by rfl) ⟨1078479, by rfl⟩ : syracuseStep 2875945 = 2156959) B2156959
theorem B38371963 : Blo 1703552 38371963 := bstep (se 1 (by rfl) ⟨28778972, by rfl⟩ : syracuseStep 38371963 = 57557945) B57557945
theorem B8626985 : Blo 1703552 8626985 := bstep (se 2 (by rfl) ⟨3235119, by rfl⟩ : syracuseStep 8626985 = 6470239) B6470239
theorem B24576959 : Blo 1703552 24576959 := bstep (se 1 (by rfl) ⟨18432719, by rfl⟩ : syracuseStep 24576959 = 36865439) B36865439
theorem B6472655 : Blo 1703552 6472655 := bstep (se 1 (by rfl) ⟨4854491, by rfl⟩ : syracuseStep 6472655 = 9708983) B9708983
theorem B3834863 : Blo 1703552 3834863 := bstep (se 1 (by rfl) ⟨2876147, by rfl⟩ : syracuseStep 3834863 = 5752295) B5752295
theorem B646767611 : Blo 1703552 646767611 := bstep (se 1 (by rfl) ⟨485075708, by rfl⟩ : syracuseStep 646767611 = 970151417) B970151417
theorem B2663455 : Blo 1703552 2663455 := bstep (se 1 (by rfl) ⟨1997591, by rfl⟩ : syracuseStep 2663455 = 3995183) B3995183
theorem B9217097 : Blo 1703552 9217097 := bstep (se 2 (by rfl) ⟨3456411, by rfl⟩ : syracuseStep 9217097 = 6912823) B6912823
theorem B2557049 : Blo 1703552 2557049 := bstep (se 2 (by rfl) ⟨958893, by rfl⟩ : syracuseStep 2557049 = 1917787) B1917787
theorem B1918183 : Blo 1703552 1918183 := bstep (se 1 (by rfl) ⟨1438637, by rfl⟩ : syracuseStep 1918183 = 2877275) B2877275
theorem B41444621 : Blo 1703552 41444621 := bstep (se 3 (by rfl) ⟨7770866, by rfl⟩ : syracuseStep 41444621 = 15541733) B15541733
theorem B2426215 : Blo 1703552 2426215 := bstep (se 1 (by rfl) ⟨1819661, by rfl⟩ : syracuseStep 2426215 = 3639323) B3639323
theorem B10364831 : Blo 1703552 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B252069803 : Blo 1703552 252069803 := bstep (se 1 (by rfl) ⟨189052352, by rfl⟩ : syracuseStep 252069803 = 378104705) B378104705
theorem B37365785 : Blo 1703552 37365785 := bstep (se 2 (by rfl) ⟨14012169, by rfl⟩ : syracuseStep 37365785 = 28024339) B28024339
theorem B4852487 : Blo 1703552 4852487 := bstep (se 1 (by rfl) ⟨3639365, by rfl⟩ : syracuseStep 4852487 = 7278731) B7278731
theorem B5753915 : Blo 1703552 5753915 := bstep (se 1 (by rfl) ⟨4315436, by rfl⟩ : syracuseStep 5753915 = 8630873) B8630873
theorem B5754239 : Blo 1703552 5754239 := bstep (se 1 (by rfl) ⟨4315679, by rfl⟩ : syracuseStep 5754239 = 8631359) B8631359
theorem B3886547 : Blo 1703552 3886547 := bstep (se 1 (by rfl) ⟨2914910, by rfl⟩ : syracuseStep 3886547 = 5829821) B5829821
theorem B24579611 : Blo 1703552 24579611 := bstep (se 1 (by rfl) ⟨18434708, by rfl⟩ : syracuseStep 24579611 = 36869417) B36869417
theorem B8188283 : Blo 1703552 8188283 := bstep (se 1 (by rfl) ⟨6141212, by rfl⟩ : syracuseStep 8188283 = 12282425) B12282425
theorem B4313483 : Blo 1703552 4313483 := bstep (se 1 (by rfl) ⟨3235112, by rfl⟩ : syracuseStep 4313483 = 6470225) B6470225
theorem B29528783 : Blo 1703552 29528783 := bstep (se 1 (by rfl) ⟨22146587, by rfl⟩ : syracuseStep 29528783 = 44293175) B44293175
theorem B46625645 : Blo 1703552 46625645 := bstep (se 3 (by rfl) ⟨8742308, by rfl⟩ : syracuseStep 46625645 = 17484617) B17484617
theorem B8631197 : Blo 1703552 8631197 := bstep (se 3 (by rfl) ⟨1618349, by rfl⟩ : syracuseStep 8631197 = 3236699) B3236699
theorem B61494203 : Blo 1703552 61494203 := bstep (se 1 (by rfl) ⟨46120652, by rfl⟩ : syracuseStep 61494203 = 92241305) B92241305
theorem B7280455 : Blo 1703552 7280455 := bstep (se 1 (by rfl) ⟨5460341, by rfl⟩ : syracuseStep 7280455 = 10920683) B10920683
theorem B2555897 : Blo 1703552 2555897 := bstep (se 2 (by rfl) ⟨958461, by rfl⟩ : syracuseStep 2555897 = 1916923) B1916923
theorem B1259116589 : Blo 1703552 1259116589 := bstep (se 3 (by rfl) ⟨236084360, by rfl⟩ : syracuseStep 1259116589 = 472168721) B472168721
theorem B16382407 : Blo 1703552 16382407 := bstep (se 1 (by rfl) ⟨12286805, by rfl⟩ : syracuseStep 16382407 = 24573611) B24573611
theorem B10919123 : Blo 1703552 10919123 := bstep (se 1 (by rfl) ⟨8189342, by rfl⟩ : syracuseStep 10919123 = 16378685) B16378685
theorem B3833711 : Blo 1703552 3833711 := bstep (se 1 (by rfl) ⟨2875283, by rfl⟩ : syracuseStep 3833711 = 5750567) B5750567
theorem B1703983 : Blo 1703552 1703983 := bstep (se 1 (by rfl) ⟨1277987, by rfl⟩ : syracuseStep 1703983 = 2555975) B2555975
theorem B1704039 : Blo 1703552 1704039 := bstep (se 1 (by rfl) ⟨1278029, by rfl⟩ : syracuseStep 1704039 = 2556059) B2556059
theorem B3834107 : Blo 1703552 3834107 := bstep (se 1 (by rfl) ⟨2875580, by rfl⟩ : syracuseStep 3834107 = 5751161) B5751161
theorem B2875655 : Blo 1703552 2875655 := bstep (se 1 (by rfl) ⟨2156741, by rfl⟩ : syracuseStep 2875655 = 4313483) B4313483
theorem B19685855 : Blo 1703552 19685855 := bstep (se 1 (by rfl) ⟨14764391, by rfl⟩ : syracuseStep 19685855 = 29528783) B29528783
theorem B5751323 : Blo 1703552 5751323 := bstep (se 1 (by rfl) ⟨4313492, by rfl⟩ : syracuseStep 5751323 = 8626985) B8626985
theorem B16384639 : Blo 1703552 16384639 := bstep (se 1 (by rfl) ⟨12288479, by rfl⟩ : syracuseStep 16384639 = 24576959) B24576959
theorem B2556575 : Blo 1703552 2556575 := bstep (se 1 (by rfl) ⟨1917431, by rfl⟩ : syracuseStep 2556575 = 3834863) B3834863
theorem B431178407 : Blo 1703552 431178407 := bstep (se 1 (by rfl) ⟨323383805, by rfl⟩ : syracuseStep 431178407 = 646767611) B646767611
theorem B6144731 : Blo 1703552 6144731 := bstep (se 1 (by rfl) ⟨4608548, by rfl⟩ : syracuseStep 6144731 = 9217097) B9217097
theorem B3834593 : Blo 1703552 3834593 := bstep (se 2 (by rfl) ⟨1437972, by rfl⟩ : syracuseStep 3834593 = 2875945) B2875945
theorem B1704699 : Blo 1703552 1704699 := bstep (se 1 (by rfl) ⟨1278524, by rfl⟩ : syracuseStep 1704699 = 2557049) B2557049
theorem B10364125 : Blo 1703552 10364125 := bstep (se 3 (by rfl) ⟨1943273, by rfl⟩ : syracuseStep 10364125 = 3886547) B3886547
theorem B839411059 : Blo 1703552 839411059 := bstep (se 1 (by rfl) ⟨629558294, by rfl⟩ : syracuseStep 839411059 = 1259116589) B1259116589
theorem B2557577 : Blo 1703552 2557577 := bstep (se 2 (by rfl) ⟨959091, by rfl⟩ : syracuseStep 2557577 = 1918183) B1918183
theorem B3835943 : Blo 1703552 3835943 := bstep (se 1 (by rfl) ⟨2876957, by rfl⟩ : syracuseStep 3835943 = 5753915) B5753915
theorem B3836159 : Blo 1703552 3836159 := bstep (se 1 (by rfl) ⟨2877119, by rfl⟩ : syracuseStep 3836159 = 5754239) B5754239
theorem B16386407 : Blo 1703552 16386407 := bstep (se 1 (by rfl) ⟨12289805, by rfl⟩ : syracuseStep 16386407 = 24579611) B24579611
theorem B5458855 : Blo 1703552 5458855 := bstep (se 1 (by rfl) ⟨4094141, by rfl⟩ : syracuseStep 5458855 = 8188283) B8188283
theorem B31083763 : Blo 1703552 31083763 := bstep (se 1 (by rfl) ⟨23312822, by rfl⟩ : syracuseStep 31083763 = 46625645) B46625645
theorem B21843209 : Blo 1703552 21843209 := bstep (se 2 (by rfl) ⟨8191203, by rfl⟩ : syracuseStep 21843209 = 16382407) B16382407
theorem B5754131 : Blo 1703552 5754131 := bstep (se 1 (by rfl) ⟨4315598, by rfl⟩ : syracuseStep 5754131 = 8631197) B8631197
theorem B40996135 : Blo 1703552 40996135 := bstep (se 1 (by rfl) ⟨30747101, by rfl⟩ : syracuseStep 40996135 = 61494203) B61494203
theorem B51162617 : Blo 1703552 51162617 := bstep (se 2 (by rfl) ⟨19185981, by rfl⟩ : syracuseStep 51162617 = 38371963) B38371963
theorem B6909887 : Blo 1703552 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B168046535 : Blo 1703552 168046535 := bstep (se 1 (by rfl) ⟨126034901, by rfl⟩ : syracuseStep 168046535 = 252069803) B252069803
theorem B1703931 : Blo 1703552 1703931 := bstep (se 1 (by rfl) ⟨1277948, by rfl⟩ : syracuseStep 1703931 = 2555897) B2555897
theorem B3551273 : Blo 1703552 3551273 := bstep (se 2 (by rfl) ⟨1331727, by rfl⟩ : syracuseStep 3551273 = 2663455) B2663455
theorem B7279415 : Blo 1703552 7279415 := bstep (se 1 (by rfl) ⟨5459561, by rfl⟩ : syracuseStep 7279415 = 10919123) B10919123
theorem B4315103 : Blo 1703552 4315103 := bstep (se 1 (by rfl) ⟨3236327, by rfl⟩ : syracuseStep 4315103 = 6472655) B6472655
theorem B27629747 : Blo 1703552 27629747 := bstep (se 1 (by rfl) ⟨20722310, by rfl⟩ : syracuseStep 27629747 = 41444621) B41444621
theorem B159602885 : Blo 1703552 159602885 := bstep (se 4 (by rfl) ⟨14962770, by rfl⟩ : syracuseStep 159602885 = 29925541) B29925541
theorem B24910523 : Blo 1703552 24910523 := bstep (se 1 (by rfl) ⟨18682892, by rfl⟩ : syracuseStep 24910523 = 37365785) B37365785
theorem B3234953 : Blo 1703552 3234953 := bstep (se 2 (by rfl) ⟨1213107, by rfl⟩ : syracuseStep 3234953 = 2426215) B2426215
theorem B3234991 : Blo 1703552 3234991 := bstep (se 1 (by rfl) ⟨2426243, by rfl⟩ : syracuseStep 3234991 = 4852487) B4852487
theorem B9707273 : Blo 1703552 9707273 := bstep (se 2 (by rfl) ⟨3640227, by rfl⟩ : syracuseStep 9707273 = 7280455) B7280455
theorem B2555807 : Blo 1703552 2555807 := bstep (se 1 (by rfl) ⟨1916855, by rfl⟩ : syracuseStep 2555807 = 3833711) B3833711
theorem B2367515 : Blo 1703552 2367515 := bstep (se 1 (by rfl) ⟨1775636, by rfl⟩ : syracuseStep 2367515 = 3551273) B3551273
theorem B2556071 : Blo 1703552 2556071 := bstep (se 1 (by rfl) ⟨1917053, by rfl⟩ : syracuseStep 2556071 = 3834107) B3834107
theorem B1917103 : Blo 1703552 1917103 := bstep (se 1 (by rfl) ⟨1437827, by rfl⟩ : syracuseStep 1917103 = 2875655) B2875655
theorem B13123903 : Blo 1703552 13123903 := bstep (se 1 (by rfl) ⟨9842927, by rfl⟩ : syracuseStep 13123903 = 19685855) B19685855
theorem B3834215 : Blo 1703552 3834215 := bstep (se 1 (by rfl) ⟨2875661, by rfl⟩ : syracuseStep 3834215 = 5751323) B5751323
theorem B1704383 : Blo 1703552 1704383 := bstep (se 1 (by rfl) ⟨1278287, by rfl⟩ : syracuseStep 1704383 = 2556575) B2556575
theorem B2556395 : Blo 1703552 2556395 := bstep (se 1 (by rfl) ⟨1917296, by rfl⟩ : syracuseStep 2556395 = 3834593) B3834593
theorem B4096487 : Blo 1703552 4096487 := bstep (se 1 (by rfl) ⟨3072365, by rfl⟩ : syracuseStep 4096487 = 6144731) B6144731
theorem B1705051 : Blo 1703552 1705051 := bstep (se 1 (by rfl) ⟨1278788, by rfl⟩ : syracuseStep 1705051 = 2557577) B2557577
theorem B2876735 : Blo 1703552 2876735 := bstep (se 1 (by rfl) ⟨2157551, by rfl⟩ : syracuseStep 2876735 = 4315103) B4315103
theorem B2557295 : Blo 1703552 2557295 := bstep (se 1 (by rfl) ⟨1917971, by rfl⟩ : syracuseStep 2557295 = 3835943) B3835943
theorem B2557439 : Blo 1703552 2557439 := bstep (se 1 (by rfl) ⟨1918079, by rfl⟩ : syracuseStep 2557439 = 3836159) B3836159
theorem B41445017 : Blo 1703552 41445017 := bstep (se 2 (by rfl) ⟨15541881, by rfl⟩ : syracuseStep 41445017 = 31083763) B31083763
theorem B16607015 : Blo 1703552 16607015 := bstep (se 1 (by rfl) ⟨12455261, by rfl⟩ : syracuseStep 16607015 = 24910523) B24910523
theorem B2156635 : Blo 1703552 2156635 := bstep (se 1 (by rfl) ⟨1617476, by rfl⟩ : syracuseStep 2156635 = 3234953) B3234953
theorem B3836087 : Blo 1703552 3836087 := bstep (se 1 (by rfl) ⟨2877065, by rfl⟩ : syracuseStep 3836087 = 5754131) B5754131
theorem B18426365 : Blo 1703552 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B287452271 : Blo 1703552 287452271 := bstep (se 1 (by rfl) ⟨215589203, by rfl⟩ : syracuseStep 287452271 = 431178407) B431178407
theorem B4852943 : Blo 1703552 4852943 := bstep (se 1 (by rfl) ⟨3639707, by rfl⟩ : syracuseStep 4852943 = 7279415) B7279415
theorem B7278473 : Blo 1703552 7278473 := bstep (se 2 (by rfl) ⟨2729427, by rfl⟩ : syracuseStep 7278473 = 5458855) B5458855
theorem B18419831 : Blo 1703552 18419831 := bstep (se 1 (by rfl) ⟨13814873, by rfl⟩ : syracuseStep 18419831 = 27629747) B27629747
theorem B106401923 : Blo 1703552 106401923 := bstep (se 1 (by rfl) ⟨79801442, by rfl⟩ : syracuseStep 106401923 = 159602885) B159602885
theorem B4313321 : Blo 1703552 4313321 := bstep (se 2 (by rfl) ⟨1617495, by rfl⟩ : syracuseStep 4313321 = 3234991) B3234991
theorem B10924271 : Blo 1703552 10924271 := bstep (se 1 (by rfl) ⟨8193203, by rfl⟩ : syracuseStep 10924271 = 16386407) B16386407
theorem B54661513 : Blo 1703552 54661513 := bstep (se 2 (by rfl) ⟨20498067, by rfl⟩ : syracuseStep 54661513 = 40996135) B40996135
theorem B14562139 : Blo 1703552 14562139 := bstep (se 1 (by rfl) ⟨10921604, by rfl⟩ : syracuseStep 14562139 = 21843209) B21843209
theorem B34108411 : Blo 1703552 34108411 := bstep (se 1 (by rfl) ⟨25581308, by rfl⟩ : syracuseStep 34108411 = 51162617) B51162617
theorem B112031023 : Blo 1703552 112031023 := bstep (se 1 (by rfl) ⟨84023267, by rfl⟩ : syracuseStep 112031023 = 168046535) B168046535
theorem B21846185 : Blo 1703552 21846185 := bstep (se 2 (by rfl) ⟨8192319, by rfl⟩ : syracuseStep 21846185 = 16384639) B16384639
theorem B13818833 : Blo 1703552 13818833 := bstep (se 2 (by rfl) ⟨5182062, by rfl⟩ : syracuseStep 13818833 = 10364125) B10364125
theorem B1119214745 : Blo 1703552 1119214745 := bstep (se 2 (by rfl) ⟨419705529, by rfl⟩ : syracuseStep 1119214745 = 839411059) B839411059
theorem B6471515 : Blo 1703552 6471515 := bstep (se 1 (by rfl) ⟨4853636, by rfl⟩ : syracuseStep 6471515 = 9707273) B9707273
theorem B1703871 : Blo 1703552 1703871 := bstep (se 1 (by rfl) ⟨1277903, by rfl⟩ : syracuseStep 1703871 = 2555807) B2555807
theorem B12279887 : Blo 1703552 12279887 := bstep (se 1 (by rfl) ⟨9209915, by rfl⟩ : syracuseStep 12279887 = 18419831) B18419831
theorem B70934615 : Blo 1703552 70934615 := bstep (se 1 (by rfl) ⟨53200961, by rfl⟩ : syracuseStep 70934615 = 106401923) B106401923
theorem B17498537 : Blo 1703552 17498537 := bstep (se 2 (by rfl) ⟨6561951, by rfl⟩ : syracuseStep 17498537 = 13123903) B13123903
theorem B1704047 : Blo 1703552 1704047 := bstep (se 1 (by rfl) ⟨1278035, by rfl⟩ : syracuseStep 1704047 = 2556071) B2556071
theorem B2875513 : Blo 1703552 2875513 := bstep (se 2 (by rfl) ⟨1078317, by rfl⟩ : syracuseStep 2875513 = 2156635) B2156635
theorem B2875547 : Blo 1703552 2875547 := bstep (se 1 (by rfl) ⟨2156660, by rfl⟩ : syracuseStep 2875547 = 4313321) B4313321
theorem B7282847 : Blo 1703552 7282847 := bstep (se 1 (by rfl) ⟨5462135, by rfl⟩ : syracuseStep 7282847 = 10924271) B10924271
theorem B2556137 : Blo 1703552 2556137 := bstep (se 2 (by rfl) ⟨958551, by rfl⟩ : syracuseStep 2556137 = 1917103) B1917103
theorem B2556143 : Blo 1703552 2556143 := bstep (se 1 (by rfl) ⟨1917107, by rfl⟩ : syracuseStep 2556143 = 3834215) B3834215
theorem B1704263 : Blo 1703552 1704263 := bstep (se 1 (by rfl) ⟨1278197, by rfl⟩ : syracuseStep 1704263 = 2556395) B2556395
theorem B1917823 : Blo 1703552 1917823 := bstep (se 1 (by rfl) ⟨1438367, by rfl⟩ : syracuseStep 1917823 = 2876735) B2876735
theorem B1704863 : Blo 1703552 1704863 := bstep (se 1 (by rfl) ⟨1278647, by rfl⟩ : syracuseStep 1704863 = 2557295) B2557295
theorem B1704959 : Blo 1703552 1704959 := bstep (se 1 (by rfl) ⟨1278719, by rfl⟩ : syracuseStep 1704959 = 2557439) B2557439
theorem B19416185 : Blo 1703552 19416185 := bstep (se 2 (by rfl) ⟨7281069, by rfl⟩ : syracuseStep 19416185 = 14562139) B14562139
theorem B2557391 : Blo 1703552 2557391 := bstep (se 1 (by rfl) ⟨1918043, by rfl⟩ : syracuseStep 2557391 = 3836087) B3836087
theorem B149374697 : Blo 1703552 149374697 := bstep (se 2 (by rfl) ⟨56015511, by rfl⟩ : syracuseStep 149374697 = 112031023) B112031023
theorem B4852315 : Blo 1703552 4852315 := bstep (se 1 (by rfl) ⟨3639236, by rfl⟩ : syracuseStep 4852315 = 7278473) B7278473
theorem B2730991 : Blo 1703552 2730991 := bstep (se 1 (by rfl) ⟨2048243, by rfl⟩ : syracuseStep 2730991 = 4096487) B4096487
theorem B11071343 : Blo 1703552 11071343 := bstep (se 1 (by rfl) ⟨8303507, by rfl⟩ : syracuseStep 11071343 = 16607015) B16607015
theorem B45477881 : Blo 1703552 45477881 := bstep (se 2 (by rfl) ⟨17054205, by rfl⟩ : syracuseStep 45477881 = 34108411) B34108411
theorem B12284243 : Blo 1703552 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B9212555 : Blo 1703552 9212555 := bstep (se 1 (by rfl) ⟨6909416, by rfl⟩ : syracuseStep 9212555 = 13818833) B13818833
theorem B4314343 : Blo 1703552 4314343 := bstep (se 1 (by rfl) ⟨3235757, by rfl⟩ : syracuseStep 4314343 = 6471515) B6471515
theorem B6313373 : Blo 1703552 6313373 := bstep (se 3 (by rfl) ⟨1183757, by rfl⟩ : syracuseStep 6313373 = 2367515) B2367515
theorem B766539389 : Blo 1703552 766539389 := bstep (se 3 (by rfl) ⟨143726135, by rfl⟩ : syracuseStep 766539389 = 287452271) B287452271
theorem B72882017 : Blo 1703552 72882017 := bstep (se 2 (by rfl) ⟨27330756, by rfl⟩ : syracuseStep 72882017 = 54661513) B54661513
theorem B27630011 : Blo 1703552 27630011 := bstep (se 1 (by rfl) ⟨20722508, by rfl⟩ : syracuseStep 27630011 = 41445017) B41445017
theorem B14564123 : Blo 1703552 14564123 := bstep (se 1 (by rfl) ⟨10923092, by rfl⟩ : syracuseStep 14564123 = 21846185) B21846185
theorem B746143163 : Blo 1703552 746143163 := bstep (se 1 (by rfl) ⟨559607372, by rfl⟩ : syracuseStep 746143163 = 1119214745) B1119214745
theorem B3235295 : Blo 1703552 3235295 := bstep (se 1 (by rfl) ⟨2426471, by rfl⟩ : syracuseStep 3235295 = 4852943) B4852943
theorem B1917031 : Blo 1703552 1917031 := bstep (se 1 (by rfl) ⟨1437773, by rfl⟩ : syracuseStep 1917031 = 2875547) B2875547
theorem B1704091 : Blo 1703552 1704091 := bstep (se 1 (by rfl) ⟨1278068, by rfl⟩ : syracuseStep 1704091 = 2556137) B2556137
theorem B1704095 : Blo 1703552 1704095 := bstep (se 1 (by rfl) ⟨1278071, by rfl⟩ : syracuseStep 1704095 = 2556143) B2556143
theorem B3834017 : Blo 1703552 3834017 := bstep (se 2 (by rfl) ⟨1437756, by rfl⟩ : syracuseStep 3834017 = 2875513) B2875513
theorem B11665691 : Blo 1703552 11665691 := bstep (se 1 (by rfl) ⟨8749268, by rfl⟩ : syracuseStep 11665691 = 17498537) B17498537
theorem B12944123 : Blo 1703552 12944123 := bstep (se 1 (by rfl) ⟨9708092, by rfl⟩ : syracuseStep 12944123 = 19416185) B19416185
theorem B1704927 : Blo 1703552 1704927 := bstep (se 1 (by rfl) ⟨1278695, by rfl⟩ : syracuseStep 1704927 = 2557391) B2557391
theorem B511026259 : Blo 1703552 511026259 := bstep (se 1 (by rfl) ⟨383269694, by rfl⟩ : syracuseStep 511026259 = 766539389) B766539389
theorem B2557097 : Blo 1703552 2557097 := bstep (se 2 (by rfl) ⟨958911, by rfl⟩ : syracuseStep 2557097 = 1917823) B1917823
theorem B48588011 : Blo 1703552 48588011 := bstep (se 1 (by rfl) ⟨36441008, by rfl⟩ : syracuseStep 48588011 = 72882017) B72882017
theorem B5752457 : Blo 1703552 5752457 := bstep (se 2 (by rfl) ⟨2157171, by rfl⟩ : syracuseStep 5752457 = 4314343) B4314343
theorem B9709415 : Blo 1703552 9709415 := bstep (se 1 (by rfl) ⟨7282061, by rfl⟩ : syracuseStep 9709415 = 14564123) B14564123
theorem B497428775 : Blo 1703552 497428775 := bstep (se 1 (by rfl) ⟨373071581, by rfl⟩ : syracuseStep 497428775 = 746143163) B746143163
theorem B2156863 : Blo 1703552 2156863 := bstep (se 1 (by rfl) ⟨1617647, by rfl⟩ : syracuseStep 2156863 = 3235295) B3235295
theorem B8186591 : Blo 1703552 8186591 := bstep (se 1 (by rfl) ⟨6139943, by rfl⟩ : syracuseStep 8186591 = 12279887) B12279887
theorem B3641321 : Blo 1703552 3641321 := bstep (se 2 (by rfl) ⟨1365495, by rfl⟩ : syracuseStep 3641321 = 2730991) B2730991
theorem B18420007 : Blo 1703552 18420007 := bstep (se 1 (by rfl) ⟨13815005, by rfl⟩ : syracuseStep 18420007 = 27630011) B27630011
theorem B398332525 : Blo 1703552 398332525 := bstep (se 3 (by rfl) ⟨74687348, by rfl⟩ : syracuseStep 398332525 = 149374697) B149374697
theorem B30318587 : Blo 1703552 30318587 := bstep (se 1 (by rfl) ⟨22738940, by rfl⟩ : syracuseStep 30318587 = 45477881) B45477881
theorem B47289743 : Blo 1703552 47289743 := bstep (se 1 (by rfl) ⟨35467307, by rfl⟩ : syracuseStep 47289743 = 70934615) B70934615
theorem B4855231 : Blo 1703552 4855231 := bstep (se 1 (by rfl) ⟨3641423, by rfl⟩ : syracuseStep 4855231 = 7282847) B7282847
theorem B8189495 : Blo 1703552 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B6469753 : Blo 1703552 6469753 := bstep (se 2 (by rfl) ⟨2426157, by rfl⟩ : syracuseStep 6469753 = 4852315) B4852315
theorem B4208915 : Blo 1703552 4208915 := bstep (se 1 (by rfl) ⟨3156686, by rfl⟩ : syracuseStep 4208915 = 6313373) B6313373
theorem B24566813 : Blo 1703552 24566813 := bstep (se 3 (by rfl) ⟨4606277, by rfl⟩ : syracuseStep 24566813 = 9212555) B9212555
theorem B7380895 : Blo 1703552 7380895 := bstep (se 1 (by rfl) ⟨5535671, by rfl⟩ : syracuseStep 7380895 = 11071343) B11071343
theorem B2556011 : Blo 1703552 2556011 := bstep (se 1 (by rfl) ⟨1917008, by rfl⟩ : syracuseStep 2556011 = 3834017) B3834017
theorem B2556041 : Blo 1703552 2556041 := bstep (se 2 (by rfl) ⟨958515, by rfl⟩ : syracuseStep 2556041 = 1917031) B1917031
theorem B8626337 : Blo 1703552 8626337 := bstep (se 2 (by rfl) ⟨3234876, by rfl⟩ : syracuseStep 8626337 = 6469753) B6469753
theorem B24560009 : Blo 1703552 24560009 := bstep (se 2 (by rfl) ⟨9210003, by rfl⟩ : syracuseStep 24560009 = 18420007) B18420007
theorem B2875817 : Blo 1703552 2875817 := bstep (se 2 (by rfl) ⟨1078431, by rfl⟩ : syracuseStep 2875817 = 2156863) B2156863
theorem B1704731 : Blo 1703552 1704731 := bstep (se 1 (by rfl) ⟨1278548, by rfl⟩ : syracuseStep 1704731 = 2557097) B2557097
theorem B32392007 : Blo 1703552 32392007 := bstep (se 1 (by rfl) ⟨24294005, by rfl⟩ : syracuseStep 32392007 = 48588011) B48588011
theorem B3834971 : Blo 1703552 3834971 := bstep (se 1 (by rfl) ⟨2876228, by rfl⟩ : syracuseStep 3834971 = 5752457) B5752457
theorem B6472943 : Blo 1703552 6472943 := bstep (se 1 (by rfl) ⟨4854707, by rfl⟩ : syracuseStep 6472943 = 9709415) B9709415
theorem B5457727 : Blo 1703552 5457727 := bstep (se 1 (by rfl) ⟨4093295, by rfl⟩ : syracuseStep 5457727 = 8186591) B8186591
theorem B6473641 : Blo 1703552 6473641 := bstep (se 2 (by rfl) ⟨2427615, by rfl⟩ : syracuseStep 6473641 = 4855231) B4855231
theorem B16377875 : Blo 1703552 16377875 := bstep (se 1 (by rfl) ⟨12283406, by rfl⟩ : syracuseStep 16377875 = 24566813) B24566813
theorem B9841193 : Blo 1703552 9841193 := bstep (se 2 (by rfl) ⟨3690447, by rfl⟩ : syracuseStep 9841193 = 7380895) B7380895
theorem B9710189 : Blo 1703552 9710189 := bstep (se 3 (by rfl) ⟨1820660, by rfl⟩ : syracuseStep 9710189 = 3641321) B3641321
theorem B20212391 : Blo 1703552 20212391 := bstep (se 1 (by rfl) ⟨15159293, by rfl⟩ : syracuseStep 20212391 = 30318587) B30318587
theorem B7777127 : Blo 1703552 7777127 := bstep (se 1 (by rfl) ⟨5832845, by rfl⟩ : syracuseStep 7777127 = 11665691) B11665691
theorem B8629415 : Blo 1703552 8629415 := bstep (se 1 (by rfl) ⟨6472061, by rfl⟩ : syracuseStep 8629415 = 12944123) B12944123
theorem B31526495 : Blo 1703552 31526495 := bstep (se 1 (by rfl) ⟨23644871, by rfl⟩ : syracuseStep 31526495 = 47289743) B47289743
theorem B5459663 : Blo 1703552 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B2805943 : Blo 1703552 2805943 := bstep (se 1 (by rfl) ⟨2104457, by rfl⟩ : syracuseStep 2805943 = 4208915) B4208915
theorem B531110033 : Blo 1703552 531110033 := bstep (se 2 (by rfl) ⟨199166262, by rfl⟩ : syracuseStep 531110033 = 398332525) B398332525
theorem B681368345 : Blo 1703552 681368345 := bstep (se 2 (by rfl) ⟨255513129, by rfl⟩ : syracuseStep 681368345 = 511026259) B511026259
theorem B331619183 : Blo 1703552 331619183 := bstep (se 1 (by rfl) ⟨248714387, by rfl⟩ : syracuseStep 331619183 = 497428775) B497428775
theorem B1704007 : Blo 1703552 1704007 := bstep (se 1 (by rfl) ⟨1278005, by rfl⟩ : syracuseStep 1704007 = 2556011) B2556011
theorem B1704027 : Blo 1703552 1704027 := bstep (se 1 (by rfl) ⟨1278020, by rfl⟩ : syracuseStep 1704027 = 2556041) B2556041
theorem B5750891 : Blo 1703552 5750891 := bstep (se 1 (by rfl) ⟨4313168, by rfl⟩ : syracuseStep 5750891 = 8626337) B8626337
theorem B1917211 : Blo 1703552 1917211 := bstep (se 1 (by rfl) ⟨1437908, by rfl⟩ : syracuseStep 1917211 = 2875817) B2875817
theorem B21594671 : Blo 1703552 21594671 := bstep (se 1 (by rfl) ⟨16196003, by rfl⟩ : syracuseStep 21594671 = 32392007) B32392007
theorem B2556647 : Blo 1703552 2556647 := bstep (se 1 (by rfl) ⟨1917485, by rfl⟩ : syracuseStep 2556647 = 3834971) B3834971
theorem B6473459 : Blo 1703552 6473459 := bstep (se 1 (by rfl) ⟨4855094, by rfl⟩ : syracuseStep 6473459 = 9710189) B9710189
theorem B14559101 : Blo 1703552 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B221079455 : Blo 1703552 221079455 := bstep (se 1 (by rfl) ⟨165809591, by rfl⟩ : syracuseStep 221079455 = 331619183) B331619183
theorem B5752943 : Blo 1703552 5752943 := bstep (se 1 (by rfl) ⟨4314707, by rfl⟩ : syracuseStep 5752943 = 8629415) B8629415
theorem B7276969 : Blo 1703552 7276969 := bstep (se 2 (by rfl) ⟨2728863, by rfl⟩ : syracuseStep 7276969 = 5457727) B5457727
theorem B21017663 : Blo 1703552 21017663 := bstep (se 1 (by rfl) ⟨15763247, by rfl⟩ : syracuseStep 21017663 = 31526495) B31526495
theorem B8631521 : Blo 1703552 8631521 := bstep (se 2 (by rfl) ⟨3236820, by rfl⟩ : syracuseStep 8631521 = 6473641) B6473641
theorem B3741257 : Blo 1703552 3741257 := bstep (se 2 (by rfl) ⟨1402971, by rfl⟩ : syracuseStep 3741257 = 2805943) B2805943
theorem B16373339 : Blo 1703552 16373339 := bstep (se 1 (by rfl) ⟨12280004, by rfl⟩ : syracuseStep 16373339 = 24560009) B24560009
theorem B4315295 : Blo 1703552 4315295 := bstep (se 1 (by rfl) ⟨3236471, by rfl⟩ : syracuseStep 4315295 = 6472943) B6472943
theorem B10918583 : Blo 1703552 10918583 := bstep (se 1 (by rfl) ⟨8188937, by rfl⟩ : syracuseStep 10918583 = 16377875) B16377875
theorem B354073355 : Blo 1703552 354073355 := bstep (se 1 (by rfl) ⟨265555016, by rfl⟩ : syracuseStep 354073355 = 531110033) B531110033
theorem B6560795 : Blo 1703552 6560795 := bstep (se 1 (by rfl) ⟨4920596, by rfl⟩ : syracuseStep 6560795 = 9841193) B9841193
theorem B13474927 : Blo 1703552 13474927 := bstep (se 1 (by rfl) ⟨10106195, by rfl⟩ : syracuseStep 13474927 = 20212391) B20212391
theorem B454245563 : Blo 1703552 454245563 := bstep (se 1 (by rfl) ⟨340684172, by rfl⟩ : syracuseStep 454245563 = 681368345) B681368345
theorem B5184751 : Blo 1703552 5184751 := bstep (se 1 (by rfl) ⟨3888563, by rfl⟩ : syracuseStep 5184751 = 7777127) B7777127
theorem B3833927 : Blo 1703552 3833927 := bstep (se 1 (by rfl) ⟨2875445, by rfl⟩ : syracuseStep 3833927 = 5750891) B5750891
theorem B2556281 : Blo 1703552 2556281 := bstep (se 2 (by rfl) ⟨958605, by rfl⟩ : syracuseStep 2556281 = 1917211) B1917211
theorem B1704431 : Blo 1703552 1704431 := bstep (se 1 (by rfl) ⟨1278323, by rfl⟩ : syracuseStep 1704431 = 2556647) B2556647
theorem B3835295 : Blo 1703552 3835295 := bstep (se 1 (by rfl) ⟨2876471, by rfl⟩ : syracuseStep 3835295 = 5752943) B5752943
theorem B2876863 : Blo 1703552 2876863 := bstep (se 1 (by rfl) ⟨2157647, by rfl⟩ : syracuseStep 2876863 = 4315295) B4315295
theorem B14396447 : Blo 1703552 14396447 := bstep (se 1 (by rfl) ⟨10797335, by rfl⟩ : syracuseStep 14396447 = 21594671) B21594671
theorem B9702625 : Blo 1703552 9702625 := bstep (se 2 (by rfl) ⟨3638484, by rfl⟩ : syracuseStep 9702625 = 7276969) B7276969
theorem B14011775 : Blo 1703552 14011775 := bstep (se 1 (by rfl) ⟨10508831, by rfl⟩ : syracuseStep 14011775 = 21017663) B21017663
theorem B5754347 : Blo 1703552 5754347 := bstep (se 1 (by rfl) ⟨4315760, by rfl⟩ : syracuseStep 5754347 = 8631521) B8631521
theorem B2494171 : Blo 1703552 2494171 := bstep (se 1 (by rfl) ⟨1870628, by rfl⟩ : syracuseStep 2494171 = 3741257) B3741257
theorem B10915559 : Blo 1703552 10915559 := bstep (se 1 (by rfl) ⟨8186669, by rfl⟩ : syracuseStep 10915559 = 16373339) B16373339
theorem B147386303 : Blo 1703552 147386303 := bstep (se 1 (by rfl) ⟨110539727, by rfl⟩ : syracuseStep 147386303 = 221079455) B221079455
theorem B7279055 : Blo 1703552 7279055 := bstep (se 1 (by rfl) ⟨5459291, by rfl⟩ : syracuseStep 7279055 = 10918583) B10918583
theorem B236048903 : Blo 1703552 236048903 := bstep (se 1 (by rfl) ⟨177036677, by rfl⟩ : syracuseStep 236048903 = 354073355) B354073355
theorem B302830375 : Blo 1703552 302830375 := bstep (se 1 (by rfl) ⟨227122781, by rfl⟩ : syracuseStep 302830375 = 454245563) B454245563
theorem B17495453 : Blo 1703552 17495453 := bstep (se 3 (by rfl) ⟨3280397, by rfl⟩ : syracuseStep 17495453 = 6560795) B6560795
theorem B71866277 : Blo 1703552 71866277 := bstep (se 4 (by rfl) ⟨6737463, by rfl⟩ : syracuseStep 71866277 = 13474927) B13474927
theorem B4315639 : Blo 1703552 4315639 := bstep (se 1 (by rfl) ⟨3236729, by rfl⟩ : syracuseStep 4315639 = 6473459) B6473459
theorem B9706067 : Blo 1703552 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B6913001 : Blo 1703552 6913001 := bstep (se 2 (by rfl) ⟨2592375, by rfl⟩ : syracuseStep 6913001 = 5184751) B5184751
theorem B2555951 : Blo 1703552 2555951 := bstep (se 1 (by rfl) ⟨1916963, by rfl⟩ : syracuseStep 2555951 = 3833927) B3833927
theorem B1704187 : Blo 1703552 1704187 := bstep (se 1 (by rfl) ⟨1278140, by rfl⟩ : syracuseStep 1704187 = 2556281) B2556281
theorem B2556863 : Blo 1703552 2556863 := bstep (se 1 (by rfl) ⟨1917647, by rfl⟩ : syracuseStep 2556863 = 3835295) B3835295
theorem B46654541 : Blo 1703552 46654541 := bstep (se 3 (by rfl) ⟨8747726, by rfl⟩ : syracuseStep 46654541 = 17495453) B17495453
theorem B12936833 : Blo 1703552 12936833 := bstep (se 2 (by rfl) ⟨4851312, by rfl⟩ : syracuseStep 12936833 = 9702625) B9702625
theorem B3835817 : Blo 1703552 3835817 := bstep (se 2 (by rfl) ⟨1438431, by rfl⟩ : syracuseStep 3835817 = 2876863) B2876863
theorem B9341183 : Blo 1703552 9341183 := bstep (se 1 (by rfl) ⟨7005887, by rfl⟩ : syracuseStep 9341183 = 14011775) B14011775
theorem B3836231 : Blo 1703552 3836231 := bstep (se 1 (by rfl) ⟨2877173, by rfl⟩ : syracuseStep 3836231 = 5754347) B5754347
theorem B7277039 : Blo 1703552 7277039 := bstep (se 1 (by rfl) ⟨5457779, by rfl⟩ : syracuseStep 7277039 = 10915559) B10915559
theorem B98257535 : Blo 1703552 98257535 := bstep (se 1 (by rfl) ⟨73693151, by rfl⟩ : syracuseStep 98257535 = 147386303) B147386303
theorem B4852703 : Blo 1703552 4852703 := bstep (se 1 (by rfl) ⟨3639527, by rfl⟩ : syracuseStep 4852703 = 7279055) B7279055
theorem B5754185 : Blo 1703552 5754185 := bstep (se 2 (by rfl) ⟨2157819, by rfl⟩ : syracuseStep 5754185 = 4315639) B4315639
theorem B47910851 : Blo 1703552 47910851 := bstep (se 1 (by rfl) ⟨35933138, by rfl⟩ : syracuseStep 47910851 = 71866277) B71866277
theorem B4608667 : Blo 1703552 4608667 := bstep (se 1 (by rfl) ⟨3456500, by rfl⟩ : syracuseStep 4608667 = 6913001) B6913001
theorem B9597631 : Blo 1703552 9597631 := bstep (se 1 (by rfl) ⟨7198223, by rfl⟩ : syracuseStep 9597631 = 14396447) B14396447
theorem B157365935 : Blo 1703552 157365935 := bstep (se 1 (by rfl) ⟨118024451, by rfl⟩ : syracuseStep 157365935 = 236048903) B236048903
theorem B403773833 : Blo 1703552 403773833 := bstep (se 2 (by rfl) ⟨151415187, by rfl⟩ : syracuseStep 403773833 = 302830375) B302830375
theorem B13302245 : Blo 1703552 13302245 := bstep (se 4 (by rfl) ⟨1247085, by rfl⟩ : syracuseStep 13302245 = 2494171) B2494171
theorem B6470711 : Blo 1703552 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B1703967 : Blo 1703552 1703967 := bstep (se 1 (by rfl) ⟨1277975, by rfl⟩ : syracuseStep 1703967 = 2555951) B2555951
theorem B1704575 : Blo 1703552 1704575 := bstep (se 1 (by rfl) ⟨1278431, by rfl⟩ : syracuseStep 1704575 = 2556863) B2556863
theorem B35472653 : Blo 1703552 35472653 := bstep (se 3 (by rfl) ⟨6651122, by rfl⟩ : syracuseStep 35472653 = 13302245) B13302245
theorem B12796841 : Blo 1703552 12796841 := bstep (se 2 (by rfl) ⟨4798815, by rfl⟩ : syracuseStep 12796841 = 9597631) B9597631
theorem B2557211 : Blo 1703552 2557211 := bstep (se 1 (by rfl) ⟨1917908, by rfl⟩ : syracuseStep 2557211 = 3835817) B3835817
theorem B6227455 : Blo 1703552 6227455 := bstep (se 1 (by rfl) ⟨4670591, by rfl⟩ : syracuseStep 6227455 = 9341183) B9341183
theorem B2557487 : Blo 1703552 2557487 := bstep (se 1 (by rfl) ⟨1918115, by rfl⟩ : syracuseStep 2557487 = 3836231) B3836231
theorem B4851359 : Blo 1703552 4851359 := bstep (se 1 (by rfl) ⟨3638519, by rfl⟩ : syracuseStep 4851359 = 7277039) B7277039
theorem B65505023 : Blo 1703552 65505023 := bstep (se 1 (by rfl) ⟨49128767, by rfl⟩ : syracuseStep 65505023 = 98257535) B98257535
theorem B3836123 : Blo 1703552 3836123 := bstep (se 1 (by rfl) ⟨2877092, by rfl⟩ : syracuseStep 3836123 = 5754185) B5754185
theorem B24579557 : Blo 1703552 24579557 := bstep (se 4 (by rfl) ⟨2304333, by rfl⟩ : syracuseStep 24579557 = 4608667) B4608667
theorem B104910623 : Blo 1703552 104910623 := bstep (se 1 (by rfl) ⟨78682967, by rfl⟩ : syracuseStep 104910623 = 157365935) B157365935
theorem B4313807 : Blo 1703552 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B31103027 : Blo 1703552 31103027 := bstep (se 1 (by rfl) ⟨23327270, by rfl⟩ : syracuseStep 31103027 = 46654541) B46654541
theorem B1076730221 : Blo 1703552 1076730221 := bstep (se 3 (by rfl) ⟨201886916, by rfl⟩ : syracuseStep 1076730221 = 403773833) B403773833
theorem B8624555 : Blo 1703552 8624555 := bstep (se 1 (by rfl) ⟨6468416, by rfl⟩ : syracuseStep 8624555 = 12936833) B12936833
theorem B3235135 : Blo 1703552 3235135 := bstep (se 1 (by rfl) ⟨2426351, by rfl⟩ : syracuseStep 3235135 = 4852703) B4852703
theorem B31940567 : Blo 1703552 31940567 := bstep (se 1 (by rfl) ⟨23955425, by rfl⟩ : syracuseStep 31940567 = 47910851) B47910851
theorem B2875871 : Blo 1703552 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B1704807 : Blo 1703552 1704807 := bstep (se 1 (by rfl) ⟨1278605, by rfl⟩ : syracuseStep 1704807 = 2557211) B2557211
theorem B1704991 : Blo 1703552 1704991 := bstep (se 1 (by rfl) ⟨1278743, by rfl⟩ : syracuseStep 1704991 = 2557487) B2557487
theorem B20735351 : Blo 1703552 20735351 := bstep (se 1 (by rfl) ⟨15551513, by rfl⟩ : syracuseStep 20735351 = 31103027) B31103027
theorem B2557415 : Blo 1703552 2557415 := bstep (se 1 (by rfl) ⟨1918061, by rfl⟩ : syracuseStep 2557415 = 3836123) B3836123
theorem B16386371 : Blo 1703552 16386371 := bstep (se 1 (by rfl) ⟨12289778, by rfl⟩ : syracuseStep 16386371 = 24579557) B24579557
theorem B21293711 : Blo 1703552 21293711 := bstep (se 1 (by rfl) ⟨15970283, by rfl⟩ : syracuseStep 21293711 = 31940567) B31940567
theorem B717820147 : Blo 1703552 717820147 := bstep (se 1 (by rfl) ⟨538365110, by rfl⟩ : syracuseStep 717820147 = 1076730221) B1076730221
theorem B4313513 : Blo 1703552 4313513 := bstep (se 2 (by rfl) ⟨1617567, by rfl⟩ : syracuseStep 4313513 = 3235135) B3235135
theorem B8303273 : Blo 1703552 8303273 := bstep (se 2 (by rfl) ⟨3113727, by rfl⟩ : syracuseStep 8303273 = 6227455) B6227455
theorem B34124909 : Blo 1703552 34124909 := bstep (se 3 (by rfl) ⟨6398420, by rfl⟩ : syracuseStep 34124909 = 12796841) B12796841
theorem B69940415 : Blo 1703552 69940415 := bstep (se 1 (by rfl) ⟨52455311, by rfl⟩ : syracuseStep 69940415 = 104910623) B104910623
theorem B23648435 : Blo 1703552 23648435 := bstep (se 1 (by rfl) ⟨17736326, by rfl⟩ : syracuseStep 23648435 = 35472653) B35472653
theorem B3234239 : Blo 1703552 3234239 := bstep (se 1 (by rfl) ⟨2425679, by rfl⟩ : syracuseStep 3234239 = 4851359) B4851359
theorem B43670015 : Blo 1703552 43670015 := bstep (se 1 (by rfl) ⟨32752511, by rfl⟩ : syracuseStep 43670015 = 65505023) B65505023
theorem B5749703 : Blo 1703552 5749703 := bstep (se 1 (by rfl) ⟨4312277, by rfl⟩ : syracuseStep 5749703 = 8624555) B8624555
theorem B2875675 : Blo 1703552 2875675 := bstep (se 1 (by rfl) ⟨2156756, by rfl⟩ : syracuseStep 2875675 = 4313513) B4313513
theorem B1917247 : Blo 1703552 1917247 := bstep (se 1 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 1917247 = 2875871) B2875871
theorem B1704943 : Blo 1703552 1704943 := bstep (se 1 (by rfl) ⟨1278707, by rfl⟩ : syracuseStep 1704943 = 2557415) B2557415
theorem B2156159 : Blo 1703552 2156159 := bstep (se 1 (by rfl) ⟨1617119, by rfl⟩ : syracuseStep 2156159 = 3234239) B3234239
theorem B90999757 : Blo 1703552 90999757 := bstep (se 3 (by rfl) ⟨17062454, by rfl⟩ : syracuseStep 90999757 = 34124909) B34124909
theorem B13823567 : Blo 1703552 13823567 := bstep (se 1 (by rfl) ⟨10367675, by rfl⟩ : syracuseStep 13823567 = 20735351) B20735351
theorem B15765623 : Blo 1703552 15765623 := bstep (se 1 (by rfl) ⟨11824217, by rfl⟩ : syracuseStep 15765623 = 23648435) B23648435
theorem B10924247 : Blo 1703552 10924247 := bstep (se 1 (by rfl) ⟨8193185, by rfl⟩ : syracuseStep 10924247 = 16386371) B16386371
theorem B957093529 : Blo 1703552 957093529 := bstep (se 2 (by rfl) ⟨358910073, by rfl⟩ : syracuseStep 957093529 = 717820147) B717820147
theorem B5535515 : Blo 1703552 5535515 := bstep (se 1 (by rfl) ⟨4151636, by rfl⟩ : syracuseStep 5535515 = 8303273) B8303273
theorem B46626943 : Blo 1703552 46626943 := bstep (se 1 (by rfl) ⟨34970207, by rfl⟩ : syracuseStep 46626943 = 69940415) B69940415
theorem B29113343 : Blo 1703552 29113343 := bstep (se 1 (by rfl) ⟨21835007, by rfl⟩ : syracuseStep 29113343 = 43670015) B43670015
theorem B14195807 : Blo 1703552 14195807 := bstep (se 1 (by rfl) ⟨10646855, by rfl⟩ : syracuseStep 14195807 = 21293711) B21293711
theorem B3833135 : Blo 1703552 3833135 := bstep (se 1 (by rfl) ⟨2874851, by rfl⟩ : syracuseStep 3833135 = 5749703) B5749703
theorem B10510415 : Blo 1703552 10510415 := bstep (se 1 (by rfl) ⟨7882811, by rfl⟩ : syracuseStep 10510415 = 15765623) B15765623
theorem B7282831 : Blo 1703552 7282831 := bstep (se 1 (by rfl) ⟨5462123, by rfl⟩ : syracuseStep 7282831 = 10924247) B10924247
theorem B62169257 : Blo 1703552 62169257 := bstep (se 2 (by rfl) ⟨23313471, by rfl⟩ : syracuseStep 62169257 = 46626943) B46626943
theorem B3834233 : Blo 1703552 3834233 := bstep (se 2 (by rfl) ⟨1437837, by rfl⟩ : syracuseStep 3834233 = 2875675) B2875675
theorem B2556329 : Blo 1703552 2556329 := bstep (se 2 (by rfl) ⟨958623, by rfl⟩ : syracuseStep 2556329 = 1917247) B1917247
theorem B121333009 : Blo 1703552 121333009 := bstep (se 2 (by rfl) ⟨45499878, by rfl⟩ : syracuseStep 121333009 = 90999757) B90999757
theorem B19408895 : Blo 1703552 19408895 := bstep (se 1 (by rfl) ⟨14556671, by rfl⟩ : syracuseStep 19408895 = 29113343) B29113343
theorem B9463871 : Blo 1703552 9463871 := bstep (se 1 (by rfl) ⟨7097903, by rfl⟩ : syracuseStep 9463871 = 14195807) B14195807
theorem B3690343 : Blo 1703552 3690343 := bstep (se 1 (by rfl) ⟨2767757, by rfl⟩ : syracuseStep 3690343 = 5535515) B5535515
theorem B5749757 : Blo 1703552 5749757 := bstep (se 3 (by rfl) ⟨1078079, by rfl⟩ : syracuseStep 5749757 = 2156159) B2156159
theorem B2555423 : Blo 1703552 2555423 := bstep (se 1 (by rfl) ⟨1916567, by rfl⟩ : syracuseStep 2555423 = 3833135) B3833135
theorem B1276124705 : Blo 1703552 1276124705 := bstep (se 2 (by rfl) ⟨478546764, by rfl⟩ : syracuseStep 1276124705 = 957093529) B957093529
theorem B9215711 : Blo 1703552 9215711 := bstep (se 1 (by rfl) ⟨6911783, by rfl⟩ : syracuseStep 9215711 = 13823567) B13823567
theorem B2556155 : Blo 1703552 2556155 := bstep (se 1 (by rfl) ⟨1917116, by rfl⟩ : syracuseStep 2556155 = 3834233) B3834233
theorem B1704219 : Blo 1703552 1704219 := bstep (se 1 (by rfl) ⟨1278164, by rfl⟩ : syracuseStep 1704219 = 2556329) B2556329
theorem B161777345 : Blo 1703552 161777345 := bstep (se 2 (by rfl) ⟨60666504, by rfl⟩ : syracuseStep 161777345 = 121333009) B121333009
theorem B850749803 : Blo 1703552 850749803 := bstep (se 1 (by rfl) ⟨638062352, by rfl⟩ : syracuseStep 850749803 = 1276124705) B1276124705
theorem B7006943 : Blo 1703552 7006943 := bstep (se 1 (by rfl) ⟨5255207, by rfl⟩ : syracuseStep 7006943 = 10510415) B10510415
theorem B41446171 : Blo 1703552 41446171 := bstep (se 1 (by rfl) ⟨31084628, by rfl⟩ : syracuseStep 41446171 = 62169257) B62169257
theorem B9710441 : Blo 1703552 9710441 := bstep (se 2 (by rfl) ⟨3641415, by rfl⟩ : syracuseStep 9710441 = 7282831) B7282831
theorem B12939263 : Blo 1703552 12939263 := bstep (se 1 (by rfl) ⟨9704447, by rfl⟩ : syracuseStep 12939263 = 19408895) B19408895
theorem B19681829 : Blo 1703552 19681829 := bstep (se 4 (by rfl) ⟨1845171, by rfl⟩ : syracuseStep 19681829 = 3690343) B3690343
theorem B25236989 : Blo 1703552 25236989 := bstep (se 3 (by rfl) ⟨4731935, by rfl⟩ : syracuseStep 25236989 = 9463871) B9463871
theorem B3833171 : Blo 1703552 3833171 := bstep (se 1 (by rfl) ⟨2874878, by rfl⟩ : syracuseStep 3833171 = 5749757) B5749757
theorem B1703615 : Blo 1703552 1703615 := bstep (se 1 (by rfl) ⟨1277711, by rfl⟩ : syracuseStep 1703615 = 2555423) B2555423
theorem B6143807 : Blo 1703552 6143807 := bstep (se 1 (by rfl) ⟨4607855, by rfl⟩ : syracuseStep 6143807 = 9215711) B9215711
theorem B1704103 : Blo 1703552 1704103 := bstep (se 1 (by rfl) ⟨1278077, by rfl⟩ : syracuseStep 1704103 = 2556155) B2556155
theorem B567166535 : Blo 1703552 567166535 := bstep (se 1 (by rfl) ⟨425374901, by rfl⟩ : syracuseStep 567166535 = 850749803) B850749803
theorem B6473627 : Blo 1703552 6473627 := bstep (se 1 (by rfl) ⟨4855220, by rfl⟩ : syracuseStep 6473627 = 9710441) B9710441
theorem B1076778197 : Blo 1703552 1076778197 := bstep (se 7 (by rfl) ⟨12618494, by rfl⟩ : syracuseStep 1076778197 = 25236989) B25236989
theorem B13121219 : Blo 1703552 13121219 := bstep (se 1 (by rfl) ⟨9840914, by rfl⟩ : syracuseStep 13121219 = 19681829) B19681829
theorem B55261561 : Blo 1703552 55261561 := bstep (se 2 (by rfl) ⟨20723085, by rfl⟩ : syracuseStep 55261561 = 41446171) B41446171
theorem B431406253 : Blo 1703552 431406253 := bstep (se 3 (by rfl) ⟨80888672, by rfl⟩ : syracuseStep 431406253 = 161777345) B161777345
theorem B8626175 : Blo 1703552 8626175 := bstep (se 1 (by rfl) ⟨6469631, by rfl⟩ : syracuseStep 8626175 = 12939263) B12939263
theorem B18685181 : Blo 1703552 18685181 := bstep (se 3 (by rfl) ⟨3503471, by rfl⟩ : syracuseStep 18685181 = 7006943) B7006943
theorem B16383485 : Blo 1703552 16383485 := bstep (se 3 (by rfl) ⟨3071903, by rfl⟩ : syracuseStep 16383485 = 6143807) B6143807
theorem B2555447 : Blo 1703552 2555447 := bstep (se 1 (by rfl) ⟨1916585, by rfl⟩ : syracuseStep 2555447 = 3833171) B3833171
theorem B378111023 : Blo 1703552 378111023 := bstep (se 1 (by rfl) ⟨283583267, by rfl⟩ : syracuseStep 378111023 = 567166535) B567166535
theorem B10922323 : Blo 1703552 10922323 := bstep (se 1 (by rfl) ⟨8191742, by rfl⟩ : syracuseStep 10922323 = 16383485) B16383485
theorem B73682081 : Blo 1703552 73682081 := bstep (se 2 (by rfl) ⟨27630780, by rfl⟩ : syracuseStep 73682081 = 55261561) B55261561
theorem B717852131 : Blo 1703552 717852131 := bstep (se 1 (by rfl) ⟨538389098, by rfl⟩ : syracuseStep 717852131 = 1076778197) B1076778197
theorem B12456787 : Blo 1703552 12456787 := bstep (se 1 (by rfl) ⟨9342590, by rfl⟩ : syracuseStep 12456787 = 18685181) B18685181
theorem B8747479 : Blo 1703552 8747479 := bstep (se 1 (by rfl) ⟨6560609, by rfl⟩ : syracuseStep 8747479 = 13121219) B13121219
theorem B4315751 : Blo 1703552 4315751 := bstep (se 1 (by rfl) ⟨3236813, by rfl⟩ : syracuseStep 4315751 = 6473627) B6473627
theorem B575208337 : Blo 1703552 575208337 := bstep (se 2 (by rfl) ⟨215703126, by rfl⟩ : syracuseStep 575208337 = 431406253) B431406253
theorem B5750783 : Blo 1703552 5750783 := bstep (se 1 (by rfl) ⟨4313087, by rfl⟩ : syracuseStep 5750783 = 8626175) B8626175
theorem B1703631 : Blo 1703552 1703631 := bstep (se 1 (by rfl) ⟨1277723, by rfl⟩ : syracuseStep 1703631 = 2555447) B2555447
theorem B766944449 : Blo 1703552 766944449 := bstep (se 2 (by rfl) ⟨287604168, by rfl⟩ : syracuseStep 766944449 = 575208337) B575208337
theorem B2877167 : Blo 1703552 2877167 := bstep (se 1 (by rfl) ⟨2157875, by rfl⟩ : syracuseStep 2877167 = 4315751) B4315751
theorem B49121387 : Blo 1703552 49121387 := bstep (se 1 (by rfl) ⟨36841040, by rfl⟩ : syracuseStep 49121387 = 73682081) B73682081
theorem B16609049 : Blo 1703552 16609049 := bstep (se 2 (by rfl) ⟨6228393, by rfl⟩ : syracuseStep 16609049 = 12456787) B12456787
theorem B3833855 : Blo 1703552 3833855 := bstep (se 1 (by rfl) ⟨2875391, by rfl⟩ : syracuseStep 3833855 = 5750783) B5750783
theorem B14563097 : Blo 1703552 14563097 := bstep (se 2 (by rfl) ⟨5461161, by rfl⟩ : syracuseStep 14563097 = 10922323) B10922323
theorem B252074015 : Blo 1703552 252074015 := bstep (se 1 (by rfl) ⟨189055511, by rfl⟩ : syracuseStep 252074015 = 378111023) B378111023
theorem B478568087 : Blo 1703552 478568087 := bstep (se 1 (by rfl) ⟨358926065, by rfl⟩ : syracuseStep 478568087 = 717852131) B717852131
theorem B46653221 : Blo 1703552 46653221 := bstep (se 4 (by rfl) ⟨4373739, by rfl⟩ : syracuseStep 46653221 = 8747479) B8747479
theorem B511296299 : Blo 1703552 511296299 := bstep (se 1 (by rfl) ⟨383472224, by rfl⟩ : syracuseStep 511296299 = 766944449) B766944449
theorem B1918111 : Blo 1703552 1918111 := bstep (se 1 (by rfl) ⟨1438583, by rfl⟩ : syracuseStep 1918111 = 2877167) B2877167
theorem B9708731 : Blo 1703552 9708731 := bstep (se 1 (by rfl) ⟨7281548, by rfl⟩ : syracuseStep 9708731 = 14563097) B14563097
theorem B32747591 : Blo 1703552 32747591 := bstep (se 1 (by rfl) ⟨24560693, by rfl⟩ : syracuseStep 32747591 = 49121387) B49121387
theorem B11072699 : Blo 1703552 11072699 := bstep (se 1 (by rfl) ⟨8304524, by rfl⟩ : syracuseStep 11072699 = 16609049) B16609049
theorem B31102147 : Blo 1703552 31102147 := bstep (se 1 (by rfl) ⟨23326610, by rfl⟩ : syracuseStep 31102147 = 46653221) B46653221
theorem B168049343 : Blo 1703552 168049343 := bstep (se 1 (by rfl) ⟨126037007, by rfl⟩ : syracuseStep 168049343 = 252074015) B252074015
theorem B319045391 : Blo 1703552 319045391 := bstep (se 1 (by rfl) ⟨239284043, by rfl⟩ : syracuseStep 319045391 = 478568087) B478568087
theorem B2555903 : Blo 1703552 2555903 := bstep (se 1 (by rfl) ⟨1916927, by rfl⟩ : syracuseStep 2555903 = 3833855) B3833855
theorem B21831727 : Blo 1703552 21831727 := bstep (se 1 (by rfl) ⟨16373795, by rfl⟩ : syracuseStep 21831727 = 32747591) B32747591
theorem B6472487 : Blo 1703552 6472487 := bstep (se 1 (by rfl) ⟨4854365, by rfl⟩ : syracuseStep 6472487 = 9708731) B9708731
theorem B2557481 : Blo 1703552 2557481 := bstep (se 2 (by rfl) ⟨959055, by rfl⟩ : syracuseStep 2557481 = 1918111) B1918111
theorem B41469529 : Blo 1703552 41469529 := bstep (se 2 (by rfl) ⟨15551073, by rfl⟩ : syracuseStep 41469529 = 31102147) B31102147
theorem B340864199 : Blo 1703552 340864199 := bstep (se 1 (by rfl) ⟨255648149, by rfl⟩ : syracuseStep 340864199 = 511296299) B511296299
theorem B1703935 : Blo 1703552 1703935 := bstep (se 1 (by rfl) ⟨1277951, by rfl⟩ : syracuseStep 1703935 = 2555903) B2555903
theorem B7381799 : Blo 1703552 7381799 := bstep (se 1 (by rfl) ⟨5536349, by rfl⟩ : syracuseStep 7381799 = 11072699) B11072699
theorem B112032895 : Blo 1703552 112032895 := bstep (se 1 (by rfl) ⟨84024671, by rfl⟩ : syracuseStep 112032895 = 168049343) B168049343
theorem B212696927 : Blo 1703552 212696927 := bstep (se 1 (by rfl) ⟨159522695, by rfl⟩ : syracuseStep 212696927 = 319045391) B319045391
theorem B1704987 : Blo 1703552 1704987 := bstep (se 1 (by rfl) ⟨1278740, by rfl⟩ : syracuseStep 1704987 = 2557481) B2557481
theorem B141797951 : Blo 1703552 141797951 := bstep (se 1 (by rfl) ⟨106348463, by rfl⟩ : syracuseStep 141797951 = 212696927) B212696927
theorem B29108969 : Blo 1703552 29108969 := bstep (se 2 (by rfl) ⟨10915863, by rfl⟩ : syracuseStep 29108969 = 21831727) B21831727
theorem B149377193 : Blo 1703552 149377193 := bstep (se 2 (by rfl) ⟨56016447, by rfl⟩ : syracuseStep 149377193 = 112032895) B112032895
theorem B55292705 : Blo 1703552 55292705 := bstep (se 2 (by rfl) ⟨20734764, by rfl⟩ : syracuseStep 55292705 = 41469529) B41469529
theorem B227242799 : Blo 1703552 227242799 := bstep (se 1 (by rfl) ⟨170432099, by rfl⟩ : syracuseStep 227242799 = 340864199) B340864199
theorem B4314991 : Blo 1703552 4314991 := bstep (se 1 (by rfl) ⟨3236243, by rfl⟩ : syracuseStep 4314991 = 6472487) B6472487
theorem B4921199 : Blo 1703552 4921199 := bstep (se 1 (by rfl) ⟨3690899, by rfl⟩ : syracuseStep 4921199 = 7381799) B7381799
theorem B151495199 : Blo 1703552 151495199 := bstep (se 1 (by rfl) ⟨113621399, by rfl⟩ : syracuseStep 151495199 = 227242799) B227242799
theorem B5753321 : Blo 1703552 5753321 := bstep (se 2 (by rfl) ⟨2157495, by rfl⟩ : syracuseStep 5753321 = 4314991) B4314991
theorem B99584795 : Blo 1703552 99584795 := bstep (se 1 (by rfl) ⟨74688596, by rfl⟩ : syracuseStep 99584795 = 149377193) B149377193
theorem B3280799 : Blo 1703552 3280799 := bstep (se 1 (by rfl) ⟨2460599, by rfl⟩ : syracuseStep 3280799 = 4921199) B4921199
theorem B94531967 : Blo 1703552 94531967 := bstep (se 1 (by rfl) ⟨70898975, by rfl⟩ : syracuseStep 94531967 = 141797951) B141797951
theorem B36861803 : Blo 1703552 36861803 := bstep (se 1 (by rfl) ⟨27646352, by rfl⟩ : syracuseStep 36861803 = 55292705) B55292705
theorem B19405979 : Blo 1703552 19405979 := bstep (se 1 (by rfl) ⟨14554484, by rfl⟩ : syracuseStep 19405979 = 29108969) B29108969
theorem B63021311 : Blo 1703552 63021311 := bstep (se 1 (by rfl) ⟨47265983, by rfl⟩ : syracuseStep 63021311 = 94531967) B94531967
theorem B3835547 : Blo 1703552 3835547 := bstep (se 1 (by rfl) ⟨2876660, by rfl⟩ : syracuseStep 3835547 = 5753321) B5753321
theorem B66389863 : Blo 1703552 66389863 := bstep (se 1 (by rfl) ⟨49792397, by rfl⟩ : syracuseStep 66389863 = 99584795) B99584795
theorem B12937319 : Blo 1703552 12937319 := bstep (se 1 (by rfl) ⟨9702989, by rfl⟩ : syracuseStep 12937319 = 19405979) B19405979
theorem B100996799 : Blo 1703552 100996799 := bstep (se 1 (by rfl) ⟨75747599, by rfl⟩ : syracuseStep 100996799 = 151495199) B151495199
theorem B24574535 : Blo 1703552 24574535 := bstep (se 1 (by rfl) ⟨18430901, by rfl⟩ : syracuseStep 24574535 = 36861803) B36861803
theorem B2187199 : Blo 1703552 2187199 := bstep (se 1 (by rfl) ⟨1640399, by rfl⟩ : syracuseStep 2187199 = 3280799) B3280799
theorem B2557031 : Blo 1703552 2557031 := bstep (se 1 (by rfl) ⟨1917773, by rfl⟩ : syracuseStep 2557031 = 3835547) B3835547
theorem B269324797 : Blo 1703552 269324797 := bstep (se 3 (by rfl) ⟨50498399, by rfl⟩ : syracuseStep 269324797 = 100996799) B100996799
theorem B88519817 : Blo 1703552 88519817 := bstep (se 2 (by rfl) ⟨33194931, by rfl⟩ : syracuseStep 88519817 = 66389863) B66389863
theorem B42014207 : Blo 1703552 42014207 := bstep (se 1 (by rfl) ⟨31510655, by rfl⟩ : syracuseStep 42014207 = 63021311) B63021311
theorem B8624879 : Blo 1703552 8624879 := bstep (se 1 (by rfl) ⟨6468659, by rfl⟩ : syracuseStep 8624879 = 12937319) B12937319
theorem B16383023 : Blo 1703552 16383023 := bstep (se 1 (by rfl) ⟨12287267, by rfl⟩ : syracuseStep 16383023 = 24574535) B24574535
theorem B2916265 : Blo 1703552 2916265 := bstep (se 2 (by rfl) ⟨1093599, by rfl⟩ : syracuseStep 2916265 = 2187199) B2187199
theorem B1704687 : Blo 1703552 1704687 := bstep (se 1 (by rfl) ⟨1278515, by rfl⟩ : syracuseStep 1704687 = 2557031) B2557031
theorem B28009471 : Blo 1703552 28009471 := bstep (se 1 (by rfl) ⟨21007103, by rfl⟩ : syracuseStep 28009471 = 42014207) B42014207
theorem B10922015 : Blo 1703552 10922015 := bstep (se 1 (by rfl) ⟨8191511, by rfl⟩ : syracuseStep 10922015 = 16383023) B16383023
theorem B359099729 : Blo 1703552 359099729 := bstep (se 2 (by rfl) ⟨134662398, by rfl⟩ : syracuseStep 359099729 = 269324797) B269324797
theorem B3888353 : Blo 1703552 3888353 := bstep (se 2 (by rfl) ⟨1458132, by rfl⟩ : syracuseStep 3888353 = 2916265) B2916265
theorem B59013211 : Blo 1703552 59013211 := bstep (se 1 (by rfl) ⟨44259908, by rfl⟩ : syracuseStep 59013211 = 88519817) B88519817
theorem B5749919 : Blo 1703552 5749919 := bstep (se 1 (by rfl) ⟨4312439, by rfl⟩ : syracuseStep 5749919 = 8624879) B8624879
theorem B78684281 : Blo 1703552 78684281 := bstep (se 2 (by rfl) ⟨29506605, by rfl⟩ : syracuseStep 78684281 = 59013211) B59013211
theorem B2592235 : Blo 1703552 2592235 := bstep (se 1 (by rfl) ⟨1944176, by rfl⟩ : syracuseStep 2592235 = 3888353) B3888353
theorem B239399819 : Blo 1703552 239399819 := bstep (se 1 (by rfl) ⟨179549864, by rfl⟩ : syracuseStep 239399819 = 359099729) B359099729
theorem B37345961 : Blo 1703552 37345961 := bstep (se 2 (by rfl) ⟨14004735, by rfl⟩ : syracuseStep 37345961 = 28009471) B28009471
theorem B7281343 : Blo 1703552 7281343 := bstep (se 1 (by rfl) ⟨5461007, by rfl⟩ : syracuseStep 7281343 = 10922015) B10922015
theorem B3833279 : Blo 1703552 3833279 := bstep (se 1 (by rfl) ⟨2874959, by rfl⟩ : syracuseStep 3833279 = 5749919) B5749919
theorem B9708457 : Blo 1703552 9708457 := bstep (se 2 (by rfl) ⟨3640671, by rfl⟩ : syracuseStep 9708457 = 7281343) B7281343
theorem B24897307 : Blo 1703552 24897307 := bstep (se 1 (by rfl) ⟨18672980, by rfl⟩ : syracuseStep 24897307 = 37345961) B37345961
theorem B52456187 : Blo 1703552 52456187 := bstep (se 1 (by rfl) ⟨39342140, by rfl⟩ : syracuseStep 52456187 = 78684281) B78684281
theorem B159599879 : Blo 1703552 159599879 := bstep (se 1 (by rfl) ⟨119699909, by rfl⟩ : syracuseStep 159599879 = 239399819) B239399819
theorem B3456313 : Blo 1703552 3456313 := bstep (se 2 (by rfl) ⟨1296117, by rfl⟩ : syracuseStep 3456313 = 2592235) B2592235
theorem B2555519 : Blo 1703552 2555519 := bstep (se 1 (by rfl) ⟨1916639, by rfl⟩ : syracuseStep 2555519 = 3833279) B3833279
theorem B12944609 : Blo 1703552 12944609 := bstep (se 2 (by rfl) ⟨4854228, by rfl⟩ : syracuseStep 12944609 = 9708457) B9708457
theorem B18433669 : Blo 1703552 18433669 := bstep (se 4 (by rfl) ⟨1728156, by rfl⟩ : syracuseStep 18433669 = 3456313) B3456313
theorem B106399919 : Blo 1703552 106399919 := bstep (se 1 (by rfl) ⟨79799939, by rfl⟩ : syracuseStep 106399919 = 159599879) B159599879
theorem B33196409 : Blo 1703552 33196409 := bstep (se 2 (by rfl) ⟨12448653, by rfl⟩ : syracuseStep 33196409 = 24897307) B24897307
theorem B34970791 : Blo 1703552 34970791 := bstep (se 1 (by rfl) ⟨26228093, by rfl⟩ : syracuseStep 34970791 = 52456187) B52456187
theorem B1703679 : Blo 1703552 1703679 := bstep (se 1 (by rfl) ⟨1277759, by rfl⟩ : syracuseStep 1703679 = 2555519) B2555519
theorem B24578225 : Blo 1703552 24578225 := bstep (se 2 (by rfl) ⟨9216834, by rfl⟩ : syracuseStep 24578225 = 18433669) B18433669
theorem B8629739 : Blo 1703552 8629739 := bstep (se 1 (by rfl) ⟨6472304, by rfl⟩ : syracuseStep 8629739 = 12944609) B12944609
theorem B22130939 : Blo 1703552 22130939 := bstep (se 1 (by rfl) ⟨16598204, by rfl⟩ : syracuseStep 22130939 = 33196409) B33196409
theorem B70933279 : Blo 1703552 70933279 := bstep (se 1 (by rfl) ⟨53199959, by rfl⟩ : syracuseStep 70933279 = 106399919) B106399919
theorem B46627721 : Blo 1703552 46627721 := bstep (se 2 (by rfl) ⟨17485395, by rfl⟩ : syracuseStep 46627721 = 34970791) B34970791
theorem B59015837 : Blo 1703552 59015837 := bstep (se 3 (by rfl) ⟨11065469, by rfl⟩ : syracuseStep 59015837 = 22130939) B22130939
theorem B94577705 : Blo 1703552 94577705 := bstep (se 2 (by rfl) ⟨35466639, by rfl⟩ : syracuseStep 94577705 = 70933279) B70933279
theorem B16385483 : Blo 1703552 16385483 := bstep (se 1 (by rfl) ⟨12289112, by rfl⟩ : syracuseStep 16385483 = 24578225) B24578225
theorem B5753159 : Blo 1703552 5753159 := bstep (se 1 (by rfl) ⟨4314869, by rfl⟩ : syracuseStep 5753159 = 8629739) B8629739
theorem B31085147 : Blo 1703552 31085147 := bstep (se 1 (by rfl) ⟨23313860, by rfl⟩ : syracuseStep 31085147 = 46627721) B46627721
theorem B3835439 : Blo 1703552 3835439 := bstep (se 1 (by rfl) ⟨2876579, by rfl⟩ : syracuseStep 3835439 = 5753159) B5753159
theorem B10923655 : Blo 1703552 10923655 := bstep (se 1 (by rfl) ⟨8192741, by rfl⟩ : syracuseStep 10923655 = 16385483) B16385483
theorem B39343891 : Blo 1703552 39343891 := bstep (se 1 (by rfl) ⟨29507918, by rfl⟩ : syracuseStep 39343891 = 59015837) B59015837
theorem B63051803 : Blo 1703552 63051803 := bstep (se 1 (by rfl) ⟨47288852, by rfl⟩ : syracuseStep 63051803 = 94577705) B94577705
theorem B82893725 : Blo 1703552 82893725 := bstep (se 3 (by rfl) ⟨15542573, by rfl⟩ : syracuseStep 82893725 = 31085147) B31085147
theorem B2556959 : Blo 1703552 2556959 := bstep (se 1 (by rfl) ⟨1917719, by rfl⟩ : syracuseStep 2556959 = 3835439) B3835439
theorem B42034535 : Blo 1703552 42034535 := bstep (se 1 (by rfl) ⟨31525901, by rfl⟩ : syracuseStep 42034535 = 63051803) B63051803
theorem B52458521 : Blo 1703552 52458521 := bstep (se 2 (by rfl) ⟨19671945, by rfl⟩ : syracuseStep 52458521 = 39343891) B39343891
theorem B55262483 : Blo 1703552 55262483 := bstep (se 1 (by rfl) ⟨41446862, by rfl⟩ : syracuseStep 55262483 = 82893725) B82893725
theorem B14564873 : Blo 1703552 14564873 := bstep (se 2 (by rfl) ⟨5461827, by rfl⟩ : syracuseStep 14564873 = 10923655) B10923655
theorem B1704639 : Blo 1703552 1704639 := bstep (se 1 (by rfl) ⟨1278479, by rfl⟩ : syracuseStep 1704639 = 2556959) B2556959
theorem B36841655 : Blo 1703552 36841655 := bstep (se 1 (by rfl) ⟨27631241, by rfl⟩ : syracuseStep 36841655 = 55262483) B55262483
theorem B9709915 : Blo 1703552 9709915 := bstep (se 1 (by rfl) ⟨7282436, by rfl⟩ : syracuseStep 9709915 = 14564873) B14564873
theorem B139889389 : Blo 1703552 139889389 := bstep (se 3 (by rfl) ⟨26229260, by rfl⟩ : syracuseStep 139889389 = 52458521) B52458521
theorem B28023023 : Blo 1703552 28023023 := bstep (se 1 (by rfl) ⟨21017267, by rfl⟩ : syracuseStep 28023023 = 42034535) B42034535
theorem B24561103 : Blo 1703552 24561103 := bstep (se 1 (by rfl) ⟨18420827, by rfl⟩ : syracuseStep 24561103 = 36841655) B36841655
theorem B12946553 : Blo 1703552 12946553 := bstep (se 2 (by rfl) ⟨4854957, by rfl⟩ : syracuseStep 12946553 = 9709915) B9709915
theorem B186519185 : Blo 1703552 186519185 := bstep (se 2 (by rfl) ⟨69944694, by rfl⟩ : syracuseStep 186519185 = 139889389) B139889389
theorem B18682015 : Blo 1703552 18682015 := bstep (se 1 (by rfl) ⟨14011511, by rfl⟩ : syracuseStep 18682015 = 28023023) B28023023
theorem B32748137 : Blo 1703552 32748137 := bstep (se 2 (by rfl) ⟨12280551, by rfl⟩ : syracuseStep 32748137 = 24561103) B24561103
theorem B8631035 : Blo 1703552 8631035 := bstep (se 1 (by rfl) ⟨6473276, by rfl⟩ : syracuseStep 8631035 = 12946553) B12946553
theorem B24909353 : Blo 1703552 24909353 := bstep (se 2 (by rfl) ⟨9341007, by rfl⟩ : syracuseStep 24909353 = 18682015) B18682015
theorem B124346123 : Blo 1703552 124346123 := bstep (se 1 (by rfl) ⟨93259592, by rfl⟩ : syracuseStep 124346123 = 186519185) B186519185
theorem B21832091 : Blo 1703552 21832091 := bstep (se 1 (by rfl) ⟨16374068, by rfl⟩ : syracuseStep 21832091 = 32748137) B32748137
theorem B16606235 : Blo 1703552 16606235 := bstep (se 1 (by rfl) ⟨12454676, by rfl⟩ : syracuseStep 16606235 = 24909353) B24909353
theorem B82897415 : Blo 1703552 82897415 := bstep (se 1 (by rfl) ⟨62173061, by rfl⟩ : syracuseStep 82897415 = 124346123) B124346123
theorem B5754023 : Blo 1703552 5754023 := bstep (se 1 (by rfl) ⟨4315517, by rfl⟩ : syracuseStep 5754023 = 8631035) B8631035
theorem B55264943 : Blo 1703552 55264943 := bstep (se 1 (by rfl) ⟨41448707, by rfl⟩ : syracuseStep 55264943 = 82897415) B82897415
theorem B3836015 : Blo 1703552 3836015 := bstep (se 1 (by rfl) ⟨2877011, by rfl⟩ : syracuseStep 3836015 = 5754023) B5754023
theorem B44283293 : Blo 1703552 44283293 := bstep (se 3 (by rfl) ⟨8303117, by rfl⟩ : syracuseStep 44283293 = 16606235) B16606235
theorem B14554727 : Blo 1703552 14554727 := bstep (se 1 (by rfl) ⟨10916045, by rfl⟩ : syracuseStep 14554727 = 21832091) B21832091
theorem B2557343 : Blo 1703552 2557343 := bstep (se 1 (by rfl) ⟨1918007, by rfl⟩ : syracuseStep 2557343 = 3836015) B3836015
theorem B9703151 : Blo 1703552 9703151 := bstep (se 1 (by rfl) ⟨7277363, by rfl⟩ : syracuseStep 9703151 = 14554727) B14554727
theorem B36843295 : Blo 1703552 36843295 := bstep (se 1 (by rfl) ⟨27632471, by rfl⟩ : syracuseStep 36843295 = 55264943) B55264943
theorem B29522195 : Blo 1703552 29522195 := bstep (se 1 (by rfl) ⟨22141646, by rfl⟩ : syracuseStep 29522195 = 44283293) B44283293
theorem B1704895 : Blo 1703552 1704895 := bstep (se 1 (by rfl) ⟨1278671, by rfl⟩ : syracuseStep 1704895 = 2557343) B2557343
theorem B19681463 : Blo 1703552 19681463 := bstep (se 1 (by rfl) ⟨14761097, by rfl⟩ : syracuseStep 19681463 = 29522195) B29522195
theorem B49124393 : Blo 1703552 49124393 := bstep (se 2 (by rfl) ⟨18421647, by rfl⟩ : syracuseStep 49124393 = 36843295) B36843295
theorem B6468767 : Blo 1703552 6468767 := bstep (se 1 (by rfl) ⟨4851575, by rfl⟩ : syracuseStep 6468767 = 9703151) B9703151
theorem B4312511 : Blo 1703552 4312511 := bstep (se 1 (by rfl) ⟨3234383, by rfl⟩ : syracuseStep 4312511 = 6468767) B6468767
theorem B13120975 : Blo 1703552 13120975 := bstep (se 1 (by rfl) ⟨9840731, by rfl⟩ : syracuseStep 13120975 = 19681463) B19681463
theorem B32749595 : Blo 1703552 32749595 := bstep (se 1 (by rfl) ⟨24562196, by rfl⟩ : syracuseStep 32749595 = 49124393) B49124393
theorem B21833063 : Blo 1703552 21833063 := bstep (se 1 (by rfl) ⟨16374797, by rfl⟩ : syracuseStep 21833063 = 32749595) B32749595
theorem B17494633 : Blo 1703552 17494633 := bstep (se 2 (by rfl) ⟨6560487, by rfl⟩ : syracuseStep 17494633 = 13120975) B13120975
theorem B2875007 : Blo 1703552 2875007 := bstep (se 1 (by rfl) ⟨2156255, by rfl⟩ : syracuseStep 2875007 = 4312511) B4312511
theorem B23326177 : Blo 1703552 23326177 := bstep (se 2 (by rfl) ⟨8747316, by rfl⟩ : syracuseStep 23326177 = 17494633) B17494633
theorem B14555375 : Blo 1703552 14555375 := bstep (se 1 (by rfl) ⟨10916531, by rfl⟩ : syracuseStep 14555375 = 21833063) B21833063
theorem B1916671 : Blo 1703552 1916671 := bstep (se 1 (by rfl) ⟨1437503, by rfl⟩ : syracuseStep 1916671 = 2875007) B2875007
theorem B9703583 : Blo 1703552 9703583 := bstep (se 1 (by rfl) ⟨7277687, by rfl⟩ : syracuseStep 9703583 = 14555375) B14555375
theorem B31101569 : Blo 1703552 31101569 := bstep (se 2 (by rfl) ⟨11663088, by rfl⟩ : syracuseStep 31101569 = 23326177) B23326177
theorem B2555561 : Blo 1703552 2555561 := bstep (se 2 (by rfl) ⟨958335, by rfl⟩ : syracuseStep 2555561 = 1916671) B1916671
theorem B20734379 : Blo 1703552 20734379 := bstep (se 1 (by rfl) ⟨15550784, by rfl⟩ : syracuseStep 20734379 = 31101569) B31101569
theorem B6469055 : Blo 1703552 6469055 := bstep (se 1 (by rfl) ⟨4851791, by rfl⟩ : syracuseStep 6469055 = 9703583) B9703583
theorem B1703707 : Blo 1703552 1703707 := bstep (se 1 (by rfl) ⟨1277780, by rfl⟩ : syracuseStep 1703707 = 2555561) B2555561
theorem B13822919 : Blo 1703552 13822919 := bstep (se 1 (by rfl) ⟨10367189, by rfl⟩ : syracuseStep 13822919 = 20734379) B20734379
theorem B4312703 : Blo 1703552 4312703 := bstep (se 1 (by rfl) ⟨3234527, by rfl⟩ : syracuseStep 4312703 = 6469055) B6469055
theorem B9215279 : Blo 1703552 9215279 := bstep (se 1 (by rfl) ⟨6911459, by rfl⟩ : syracuseStep 9215279 = 13822919) B13822919
theorem B2875135 : Blo 1703552 2875135 := bstep (se 1 (by rfl) ⟨2156351, by rfl⟩ : syracuseStep 2875135 = 4312703) B4312703
theorem B6143519 : Blo 1703552 6143519 := bstep (se 1 (by rfl) ⟨4607639, by rfl⟩ : syracuseStep 6143519 = 9215279) B9215279
theorem B3833513 : Blo 1703552 3833513 := bstep (se 2 (by rfl) ⟨1437567, by rfl⟩ : syracuseStep 3833513 = 2875135) B2875135
theorem B4095679 : Blo 1703552 4095679 := bstep (se 1 (by rfl) ⟨3071759, by rfl⟩ : syracuseStep 4095679 = 6143519) B6143519
theorem B2555675 : Blo 1703552 2555675 := bstep (se 1 (by rfl) ⟨1916756, by rfl⟩ : syracuseStep 2555675 = 3833513) B3833513
theorem B5460905 : Blo 1703552 5460905 := bstep (se 2 (by rfl) ⟨2047839, by rfl⟩ : syracuseStep 5460905 = 4095679) B4095679
theorem B1703783 : Blo 1703552 1703783 := bstep (se 1 (by rfl) ⟨1277837, by rfl⟩ : syracuseStep 1703783 = 2555675) B2555675
theorem B14562413 : Blo 1703552 14562413 := bstep (se 3 (by rfl) ⟨2730452, by rfl⟩ : syracuseStep 14562413 = 5460905) B5460905
theorem B9708275 : Blo 1703552 9708275 := bstep (se 1 (by rfl) ⟨7281206, by rfl⟩ : syracuseStep 9708275 = 14562413) B14562413
theorem B6472183 : Blo 1703552 6472183 := bstep (se 1 (by rfl) ⟨4854137, by rfl⟩ : syracuseStep 6472183 = 9708275) B9708275
theorem B8629577 : Blo 1703552 8629577 := bstep (se 2 (by rfl) ⟨3236091, by rfl⟩ : syracuseStep 8629577 = 6472183) B6472183
theorem B5753051 : Blo 1703552 5753051 := bstep (se 1 (by rfl) ⟨4314788, by rfl⟩ : syracuseStep 5753051 = 8629577) B8629577
theorem B3835367 : Blo 1703552 3835367 := bstep (se 1 (by rfl) ⟨2876525, by rfl⟩ : syracuseStep 3835367 = 5753051) B5753051
theorem B2556911 : Blo 1703552 2556911 := bstep (se 1 (by rfl) ⟨1917683, by rfl⟩ : syracuseStep 2556911 = 3835367) B3835367
theorem B1704607 : Blo 1703552 1704607 := bstep (se 1 (by rfl) ⟨1278455, by rfl⟩ : syracuseStep 1704607 = 2556911) B2556911

theorem C0 (j : ℕ) (h1 : 425888 ≤ j) (h2 : j ≤ 426262) : Blo 1703552 (4 * j + 3) := by
  interval_cases j
  · exact B1703555
  · exact B1703559
  · exact B1703563
  · exact B1703567
  · exact B1703571
  · exact B1703575
  · exact B1703579
  · exact B1703583
  · exact B1703587
  · exact B1703591
  · exact B1703595
  · exact B1703599
  · exact B1703603
  · exact B1703607
  · exact B1703611
  · exact B1703615
  · exact B1703619
  · exact B1703623
  · exact B1703627
  · exact B1703631
  · exact B1703635
  · exact B1703639
  · exact B1703643
  · exact B1703647
  · exact B1703651
  · exact B1703655
  · exact B1703659
  · exact B1703663
  · exact B1703667
  · exact B1703671
  · exact B1703675
  · exact B1703679
  · exact B1703683
  · exact B1703687
  · exact B1703691
  · exact B1703695
  · exact B1703699
  · exact B1703703
  · exact B1703707
  · exact B1703711
  · exact B1703715
  · exact B1703719
  · exact B1703723
  · exact B1703727
  · exact B1703731
  · exact B1703735
  · exact B1703739
  · exact B1703743
  · exact B1703747
  · exact B1703751
  · exact B1703755
  · exact B1703759
  · exact B1703763
  · exact B1703767
  · exact B1703771
  · exact B1703775
  · exact B1703779
  · exact B1703783
  · exact B1703787
  · exact B1703791
  · exact B1703795
  · exact B1703799
  · exact B1703803
  · exact B1703807
  · exact B1703811
  · exact B1703815
  · exact B1703819
  · exact B1703823
  · exact B1703827
  · exact B1703831
  · exact B1703835
  · exact B1703839
  · exact B1703843
  · exact B1703847
  · exact B1703851
  · exact B1703855
  · exact B1703859
  · exact B1703863
  · exact B1703867
  · exact B1703871
  · exact B1703875
  · exact B1703879
  · exact B1703883
  · exact B1703887
  · exact B1703891
  · exact B1703895
  · exact B1703899
  · exact B1703903
  · exact B1703907
  · exact B1703911
  · exact B1703915
  · exact B1703919
  · exact B1703923
  · exact B1703927
  · exact B1703931
  · exact B1703935
  · exact B1703939
  · exact B1703943
  · exact B1703947
  · exact B1703951
  · exact B1703955
  · exact B1703959
  · exact B1703963
  · exact B1703967
  · exact B1703971
  · exact B1703975
  · exact B1703979
  · exact B1703983
  · exact B1703987
  · exact B1703991
  · exact B1703995
  · exact B1703999
  · exact B1704003
  · exact B1704007
  · exact B1704011
  · exact B1704015
  · exact B1704019
  · exact B1704023
  · exact B1704027
  · exact B1704031
  · exact B1704035
  · exact B1704039
  · exact B1704043
  · exact B1704047
  · exact B1704051
  · exact B1704055
  · exact B1704059
  · exact B1704063
  · exact B1704067
  · exact B1704071
  · exact B1704075
  · exact B1704079
  · exact B1704083
  · exact B1704087
  · exact B1704091
  · exact B1704095
  · exact B1704099
  · exact B1704103
  · exact B1704107
  · exact B1704111
  · exact B1704115
  · exact B1704119
  · exact B1704123
  · exact B1704127
  · exact B1704131
  · exact B1704135
  · exact B1704139
  · exact B1704143
  · exact B1704147
  · exact B1704151
  · exact B1704155
  · exact B1704159
  · exact B1704163
  · exact B1704167
  · exact B1704171
  · exact B1704175
  · exact B1704179
  · exact B1704183
  · exact B1704187
  · exact B1704191
  · exact B1704195
  · exact B1704199
  · exact B1704203
  · exact B1704207
  · exact B1704211
  · exact B1704215
  · exact B1704219
  · exact B1704223
  · exact B1704227
  · exact B1704231
  · exact B1704235
  · exact B1704239
  · exact B1704243
  · exact B1704247
  · exact B1704251
  · exact B1704255
  · exact B1704259
  · exact B1704263
  · exact B1704267
  · exact B1704271
  · exact B1704275
  · exact B1704279
  · exact B1704283
  · exact B1704287
  · exact B1704291
  · exact B1704295
  · exact B1704299
  · exact B1704303
  · exact B1704307
  · exact B1704311
  · exact B1704315
  · exact B1704319
  · exact B1704323
  · exact B1704327
  · exact B1704331
  · exact B1704335
  · exact B1704339
  · exact B1704343
  · exact B1704347
  · exact B1704351
  · exact B1704355
  · exact B1704359
  · exact B1704363
  · exact B1704367
  · exact B1704371
  · exact B1704375
  · exact B1704379
  · exact B1704383
  · exact B1704387
  · exact B1704391
  · exact B1704395
  · exact B1704399
  · exact B1704403
  · exact B1704407
  · exact B1704411
  · exact B1704415
  · exact B1704419
  · exact B1704423
  · exact B1704427
  · exact B1704431
  · exact B1704435
  · exact B1704439
  · exact B1704443
  · exact B1704447
  · exact B1704451
  · exact B1704455
  · exact B1704459
  · exact B1704463
  · exact B1704467
  · exact B1704471
  · exact B1704475
  · exact B1704479
  · exact B1704483
  · exact B1704487
  · exact B1704491
  · exact B1704495
  · exact B1704499
  · exact B1704503
  · exact B1704507
  · exact B1704511
  · exact B1704515
  · exact B1704519
  · exact B1704523
  · exact B1704527
  · exact B1704531
  · exact B1704535
  · exact B1704539
  · exact B1704543
  · exact B1704547
  · exact B1704551
  · exact B1704555
  · exact B1704559
  · exact B1704563
  · exact B1704567
  · exact B1704571
  · exact B1704575
  · exact B1704579
  · exact B1704583
  · exact B1704587
  · exact B1704591
  · exact B1704595
  · exact B1704599
  · exact B1704603
  · exact B1704607
  · exact B1704611
  · exact B1704615
  · exact B1704619
  · exact B1704623
  · exact B1704627
  · exact B1704631
  · exact B1704635
  · exact B1704639
  · exact B1704643
  · exact B1704647
  · exact B1704651
  · exact B1704655
  · exact B1704659
  · exact B1704663
  · exact B1704667
  · exact B1704671
  · exact B1704675
  · exact B1704679
  · exact B1704683
  · exact B1704687
  · exact B1704691
  · exact B1704695
  · exact B1704699
  · exact B1704703
  · exact B1704707
  · exact B1704711
  · exact B1704715
  · exact B1704719
  · exact B1704723
  · exact B1704727
  · exact B1704731
  · exact B1704735
  · exact B1704739
  · exact B1704743
  · exact B1704747
  · exact B1704751
  · exact B1704755
  · exact B1704759
  · exact B1704763
  · exact B1704767
  · exact B1704771
  · exact B1704775
  · exact B1704779
  · exact B1704783
  · exact B1704787
  · exact B1704791
  · exact B1704795
  · exact B1704799
  · exact B1704803
  · exact B1704807
  · exact B1704811
  · exact B1704815
  · exact B1704819
  · exact B1704823
  · exact B1704827
  · exact B1704831
  · exact B1704835
  · exact B1704839
  · exact B1704843
  · exact B1704847
  · exact B1704851
  · exact B1704855
  · exact B1704859
  · exact B1704863
  · exact B1704867
  · exact B1704871
  · exact B1704875
  · exact B1704879
  · exact B1704883
  · exact B1704887
  · exact B1704891
  · exact B1704895
  · exact B1704899
  · exact B1704903
  · exact B1704907
  · exact B1704911
  · exact B1704915
  · exact B1704919
  · exact B1704923
  · exact B1704927
  · exact B1704931
  · exact B1704935
  · exact B1704939
  · exact B1704943
  · exact B1704947
  · exact B1704951
  · exact B1704955
  · exact B1704959
  · exact B1704963
  · exact B1704967
  · exact B1704971
  · exact B1704975
  · exact B1704979
  · exact B1704983
  · exact B1704987
  · exact B1704991
  · exact B1704995
  · exact B1704999
  · exact B1705003
  · exact B1705007
  · exact B1705011
  · exact B1705015
  · exact B1705019
  · exact B1705023
  · exact B1705027
  · exact B1705031
  · exact B1705035
  · exact B1705039
  · exact B1705043
  · exact B1705047
  · exact B1705051

theorem solution (m : ℕ) (hlo : 1703552 ≤ m) (hhi : m ≤ 1705052) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 425888 ≤ j := by omega
    have hj2 : j ≤ 426262 := by omega
    have hb : Blo 1703552 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
