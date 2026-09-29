-- Prove2me | solution 1 for syracuse_descends_range_1068616_1072616
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:30.364417+00:00
-- url     : https://prove2.me/submissions/28e076af-aa9b-4973-8cb7-87d9823b0805

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


theorem B1605653 : Blo 1068616 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B1605677 : Blo 1068616 1605677 := bbase (se 3 (by rfl) ⟨301064, by rfl⟩ : syracuseStep 1605677 = 602129) (by norm_num)
theorem B1605701 : Blo 1068616 1605701 := bbase (se 4 (by rfl) ⟨150534, by rfl⟩ : syracuseStep 1605701 = 301069) (by norm_num)
theorem B1605725 : Blo 1068616 1605725 := bbase (se 3 (by rfl) ⟨301073, by rfl⟩ : syracuseStep 1605725 = 602147) (by norm_num)
theorem B1605749 : Blo 1068616 1605749 := bbase (se 5 (by rfl) ⟨75269, by rfl⟩ : syracuseStep 1605749 = 150539) (by norm_num)
theorem B1605773 : Blo 1068616 1605773 := bbase (se 3 (by rfl) ⟨301082, by rfl⟩ : syracuseStep 1605773 = 602165) (by norm_num)
theorem B1605797 : Blo 1068616 1605797 := bbase (se 4 (by rfl) ⟨150543, by rfl⟩ : syracuseStep 1605797 = 301087) (by norm_num)
theorem B1605821 : Blo 1068616 1605821 := bbase (se 3 (by rfl) ⟨301091, by rfl⟩ : syracuseStep 1605821 = 602183) (by norm_num)
theorem B1605845 : Blo 1068616 1605845 := bbase (se 7 (by rfl) ⟨18818, by rfl⟩ : syracuseStep 1605845 = 37637) (by norm_num)
theorem B1605869 : Blo 1068616 1605869 := bbase (se 3 (by rfl) ⟨301100, by rfl⟩ : syracuseStep 1605869 = 602201) (by norm_num)
theorem B1736957 : Blo 1068616 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1605893 : Blo 1068616 1605893 := bbase (se 4 (by rfl) ⟨150552, by rfl⟩ : syracuseStep 1605893 = 301105) (by norm_num)
theorem B1605917 : Blo 1068616 1605917 := bbase (se 3 (by rfl) ⟨301109, by rfl⟩ : syracuseStep 1605917 = 602219) (by norm_num)
theorem B1605941 : Blo 1068616 1605941 := bbase (se 5 (by rfl) ⟨75278, by rfl⟩ : syracuseStep 1605941 = 150557) (by norm_num)
theorem B1605965 : Blo 1068616 1605965 := bbase (se 3 (by rfl) ⟨301118, by rfl⟩ : syracuseStep 1605965 = 602237) (by norm_num)
theorem B1605989 : Blo 1068616 1605989 := bbase (se 4 (by rfl) ⟨150561, by rfl⟩ : syracuseStep 1605989 = 301123) (by norm_num)
theorem B1606013 : Blo 1068616 1606013 := bbase (se 3 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 1606013 = 602255) (by norm_num)
theorem B3047813 : Blo 1068616 3047813 := bbase (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) (by norm_num)
theorem B1606037 : Blo 1068616 1606037 := bbase (se 6 (by rfl) ⟨37641, by rfl⟩ : syracuseStep 1606037 = 75283) (by norm_num)
theorem B1606061 : Blo 1068616 1606061 := bbase (se 3 (by rfl) ⟨301136, by rfl⟩ : syracuseStep 1606061 = 602273) (by norm_num)
theorem B1606085 : Blo 1068616 1606085 := bbase (se 4 (by rfl) ⟨150570, by rfl⟩ : syracuseStep 1606085 = 301141) (by norm_num)
theorem B1606109 : Blo 1068616 1606109 := bbase (se 3 (by rfl) ⟨301145, by rfl⟩ : syracuseStep 1606109 = 602291) (by norm_num)
theorem B1606133 : Blo 1068616 1606133 := bbase (se 5 (by rfl) ⟨75287, by rfl⟩ : syracuseStep 1606133 = 150575) (by norm_num)
theorem B2032141 : Blo 1068616 2032141 := bbase (se 3 (by rfl) ⟨381026, by rfl⟩ : syracuseStep 2032141 = 762053) (by norm_num)
theorem B1606157 : Blo 1068616 1606157 := bbase (se 3 (by rfl) ⟨301154, by rfl⟩ : syracuseStep 1606157 = 602309) (by norm_num)
theorem B1606181 : Blo 1068616 1606181 := bbase (se 4 (by rfl) ⟨150579, by rfl⟩ : syracuseStep 1606181 = 301159) (by norm_num)
theorem B1606205 : Blo 1068616 1606205 := bbase (se 3 (by rfl) ⟨301163, by rfl⟩ : syracuseStep 1606205 = 602327) (by norm_num)
theorem B1606229 : Blo 1068616 1606229 := bbase (se 8 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 1606229 = 18823) (by norm_num)
theorem B1114729 : Blo 1068616 1114729 := bbase (se 2 (by rfl) ⟨418023, by rfl⟩ : syracuseStep 1114729 = 836047) (by norm_num)
theorem B1606253 : Blo 1068616 1606253 := bbase (se 3 (by rfl) ⟨301172, by rfl⟩ : syracuseStep 1606253 = 602345) (by norm_num)
theorem B1606277 : Blo 1068616 1606277 := bbase (se 4 (by rfl) ⟨150588, by rfl⟩ : syracuseStep 1606277 = 301177) (by norm_num)
theorem B2032285 : Blo 1068616 2032285 := bbase (se 3 (by rfl) ⟨381053, by rfl⟩ : syracuseStep 2032285 = 762107) (by norm_num)
theorem B1606301 : Blo 1068616 1606301 := bbase (se 3 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 1606301 = 602363) (by norm_num)
theorem B1606325 : Blo 1068616 1606325 := bbase (se 5 (by rfl) ⟨75296, by rfl⟩ : syracuseStep 1606325 = 150593) (by norm_num)
theorem B1606349 : Blo 1068616 1606349 := bbase (se 3 (by rfl) ⟨301190, by rfl⟩ : syracuseStep 1606349 = 602381) (by norm_num)
theorem B1606373 : Blo 1068616 1606373 := bbase (se 4 (by rfl) ⟨150597, by rfl⟩ : syracuseStep 1606373 = 301195) (by norm_num)
theorem B1606397 : Blo 1068616 1606397 := bbase (se 3 (by rfl) ⟨301199, by rfl⟩ : syracuseStep 1606397 = 602399) (by norm_num)
theorem B2196229 : Blo 1068616 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B1606421 : Blo 1068616 1606421 := bbase (se 6 (by rfl) ⟨37650, by rfl⟩ : syracuseStep 1606421 = 75301) (by norm_num)
theorem B1606445 : Blo 1068616 1606445 := bbase (se 3 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 1606445 = 602417) (by norm_num)
theorem B4064053 : Blo 1068616 4064053 := bbase (se 5 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 4064053 = 381005) (by norm_num)
theorem B2032445 : Blo 1068616 2032445 := bbase (se 3 (by rfl) ⟨381083, by rfl⟩ : syracuseStep 2032445 = 762167) (by norm_num)
theorem B1606469 : Blo 1068616 1606469 := bbase (se 4 (by rfl) ⟨150606, by rfl⟩ : syracuseStep 1606469 = 301213) (by norm_num)
theorem B1606493 : Blo 1068616 1606493 := bbase (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) (by norm_num)
theorem B1606517 : Blo 1068616 1606517 := bbase (se 5 (by rfl) ⟨75305, by rfl⟩ : syracuseStep 1606517 = 150611) (by norm_num)
theorem B1606541 : Blo 1068616 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B1606565 : Blo 1068616 1606565 := bbase (se 4 (by rfl) ⟨150615, by rfl⟩ : syracuseStep 1606565 = 301231) (by norm_num)
theorem B1606589 : Blo 1068616 1606589 := bbase (se 3 (by rfl) ⟨301235, by rfl⟩ : syracuseStep 1606589 = 602471) (by norm_num)
theorem B2032589 : Blo 1068616 2032589 := bbase (se 3 (by rfl) ⟨381110, by rfl⟩ : syracuseStep 2032589 = 762221) (by norm_num)
theorem B1606613 : Blo 1068616 1606613 := bbase (se 7 (by rfl) ⟨18827, by rfl⟩ : syracuseStep 1606613 = 37655) (by norm_num)
theorem B1606637 : Blo 1068616 1606637 := bbase (se 3 (by rfl) ⟨301244, by rfl⟩ : syracuseStep 1606637 = 602489) (by norm_num)
theorem B1606661 : Blo 1068616 1606661 := bbase (se 4 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 1606661 = 301249) (by norm_num)
theorem B1606685 : Blo 1068616 1606685 := bbase (se 3 (by rfl) ⟨301253, by rfl⟩ : syracuseStep 1606685 = 602507) (by norm_num)
theorem B1606709 : Blo 1068616 1606709 := bbase (se 5 (by rfl) ⟨75314, by rfl⟩ : syracuseStep 1606709 = 150629) (by norm_num)
theorem B1606733 : Blo 1068616 1606733 := bbase (se 3 (by rfl) ⟨301262, by rfl⟩ : syracuseStep 1606733 = 602525) (by norm_num)
theorem B4064357 : Blo 1068616 4064357 := bbase (se 4 (by rfl) ⟨381033, by rfl⟩ : syracuseStep 4064357 = 762067) (by norm_num)
theorem B1606757 : Blo 1068616 1606757 := bbase (se 4 (by rfl) ⟨150633, by rfl⟩ : syracuseStep 1606757 = 301267) (by norm_num)
theorem B1606781 : Blo 1068616 1606781 := bbase (se 3 (by rfl) ⟨301271, by rfl⟩ : syracuseStep 1606781 = 602543) (by norm_num)
theorem B1803397 : Blo 1068616 1803397 := bbase (se 4 (by rfl) ⟨169068, by rfl⟩ : syracuseStep 1803397 = 338137) (by norm_num)
theorem B1606805 : Blo 1068616 1606805 := bbase (se 6 (by rfl) ⟨37659, by rfl⟩ : syracuseStep 1606805 = 75319) (by norm_num)
theorem B1606829 : Blo 1068616 1606829 := bbase (se 3 (by rfl) ⟨301280, by rfl⟩ : syracuseStep 1606829 = 602561) (by norm_num)
theorem B1606853 : Blo 1068616 1606853 := bbase (se 4 (by rfl) ⟨150642, by rfl⟩ : syracuseStep 1606853 = 301285) (by norm_num)
theorem B1803485 : Blo 1068616 1803485 := bbase (se 3 (by rfl) ⟨338153, by rfl⟩ : syracuseStep 1803485 = 676307) (by norm_num)
theorem B1606877 : Blo 1068616 1606877 := bbase (se 3 (by rfl) ⟨301289, by rfl⟩ : syracuseStep 1606877 = 602579) (by norm_num)
theorem B2032877 : Blo 1068616 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B1606901 : Blo 1068616 1606901 := bbase (se 5 (by rfl) ⟨75323, by rfl⟩ : syracuseStep 1606901 = 150647) (by norm_num)
theorem B1606925 : Blo 1068616 1606925 := bbase (se 3 (by rfl) ⟨301298, by rfl⟩ : syracuseStep 1606925 = 602597) (by norm_num)
theorem B1606949 : Blo 1068616 1606949 := bbase (se 4 (by rfl) ⟨150651, by rfl⟩ : syracuseStep 1606949 = 301303) (by norm_num)
theorem B1606973 : Blo 1068616 1606973 := bbase (se 3 (by rfl) ⟨301307, by rfl⟩ : syracuseStep 1606973 = 602615) (by norm_num)
theorem B1606997 : Blo 1068616 1606997 := bbase (se 12 (by rfl) ⟨588, by rfl⟩ : syracuseStep 1606997 = 1177) (by norm_num)
theorem B1803613 : Blo 1068616 1803613 := bbase (se 3 (by rfl) ⟨338177, by rfl⟩ : syracuseStep 1803613 = 676355) (by norm_num)
theorem B1607021 : Blo 1068616 1607021 := bbase (se 3 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 1607021 = 602633) (by norm_num)
theorem B2033029 : Blo 1068616 2033029 := bbase (se 4 (by rfl) ⟨190596, by rfl⟩ : syracuseStep 2033029 = 381193) (by norm_num)
theorem B1607045 : Blo 1068616 1607045 := bbase (se 4 (by rfl) ⟨150660, by rfl⟩ : syracuseStep 1607045 = 301321) (by norm_num)
theorem B1607069 : Blo 1068616 1607069 := bbase (se 3 (by rfl) ⟨301325, by rfl⟩ : syracuseStep 1607069 = 602651) (by norm_num)
theorem B1803701 : Blo 1068616 1803701 := bbase (se 5 (by rfl) ⟨84548, by rfl⟩ : syracuseStep 1803701 = 169097) (by norm_num)
theorem B1607093 : Blo 1068616 1607093 := bbase (se 5 (by rfl) ⟨75332, by rfl⟩ : syracuseStep 1607093 = 150665) (by norm_num)
theorem B1607117 : Blo 1068616 1607117 := bbase (se 3 (by rfl) ⟨301334, by rfl⟩ : syracuseStep 1607117 = 602669) (by norm_num)
theorem B1607141 : Blo 1068616 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B1607165 : Blo 1068616 1607165 := bbase (se 3 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 1607165 = 602687) (by norm_num)
theorem B1607189 : Blo 1068616 1607189 := bbase (se 6 (by rfl) ⟨37668, by rfl⟩ : syracuseStep 1607189 = 75337) (by norm_num)
theorem B3048997 : Blo 1068616 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B1607213 : Blo 1068616 1607213 := bbase (se 3 (by rfl) ⟨301352, by rfl⟩ : syracuseStep 1607213 = 602705) (by norm_num)
theorem B1803829 : Blo 1068616 1803829 := bbase (se 5 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 1803829 = 169109) (by norm_num)
theorem B1607237 : Blo 1068616 1607237 := bbase (se 4 (by rfl) ⟨150678, by rfl⟩ : syracuseStep 1607237 = 301357) (by norm_num)
theorem B1607261 : Blo 1068616 1607261 := bbase (se 3 (by rfl) ⟨301361, by rfl⟩ : syracuseStep 1607261 = 602723) (by norm_num)
theorem B1607285 : Blo 1068616 1607285 := bbase (se 5 (by rfl) ⟨75341, by rfl⟩ : syracuseStep 1607285 = 150683) (by norm_num)
theorem B1803917 : Blo 1068616 1803917 := bbase (se 3 (by rfl) ⟨338234, by rfl⟩ : syracuseStep 1803917 = 676469) (by norm_num)
theorem B1607309 : Blo 1068616 1607309 := bbase (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) (by norm_num)
theorem B1607333 : Blo 1068616 1607333 := bbase (se 4 (by rfl) ⟨150687, by rfl⟩ : syracuseStep 1607333 = 301375) (by norm_num)
theorem B2033333 : Blo 1068616 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B1607357 : Blo 1068616 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B3049157 : Blo 1068616 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B1607381 : Blo 1068616 1607381 := bbase (se 7 (by rfl) ⟨18836, by rfl⟩ : syracuseStep 1607381 = 37673) (by norm_num)
theorem B1607405 : Blo 1068616 1607405 := bbase (se 3 (by rfl) ⟨301388, by rfl⟩ : syracuseStep 1607405 = 602777) (by norm_num)
theorem B1607429 : Blo 1068616 1607429 := bbase (se 4 (by rfl) ⟨150696, by rfl⟩ : syracuseStep 1607429 = 301393) (by norm_num)
theorem B1804045 : Blo 1068616 1804045 := bbase (se 3 (by rfl) ⟨338258, by rfl⟩ : syracuseStep 1804045 = 676517) (by norm_num)
theorem B1607453 : Blo 1068616 1607453 := bbase (se 3 (by rfl) ⟨301397, by rfl⟩ : syracuseStep 1607453 = 602795) (by norm_num)
theorem B1607477 : Blo 1068616 1607477 := bbase (se 5 (by rfl) ⟨75350, by rfl⟩ : syracuseStep 1607477 = 150701) (by norm_num)
theorem B1607501 : Blo 1068616 1607501 := bbase (se 3 (by rfl) ⟨301406, by rfl⟩ : syracuseStep 1607501 = 602813) (by norm_num)
theorem B1804133 : Blo 1068616 1804133 := bbase (se 4 (by rfl) ⟨169137, by rfl⟩ : syracuseStep 1804133 = 338275) (by norm_num)
theorem B1607525 : Blo 1068616 1607525 := bbase (se 4 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 1607525 = 301411) (by norm_num)
theorem B1607549 : Blo 1068616 1607549 := bbase (se 3 (by rfl) ⟨301415, by rfl⟩ : syracuseStep 1607549 = 602831) (by norm_num)
theorem B1607573 : Blo 1068616 1607573 := bbase (se 6 (by rfl) ⟨37677, by rfl⟩ : syracuseStep 1607573 = 75355) (by norm_num)
theorem B1607597 : Blo 1068616 1607597 := bbase (se 3 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 1607597 = 602849) (by norm_num)
theorem B3049397 : Blo 1068616 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B1607621 : Blo 1068616 1607621 := bbase (se 4 (by rfl) ⟨150714, by rfl⟩ : syracuseStep 1607621 = 301429) (by norm_num)
theorem B1607645 : Blo 1068616 1607645 := bbase (se 3 (by rfl) ⟨301433, by rfl⟩ : syracuseStep 1607645 = 602867) (by norm_num)
theorem B1804261 : Blo 1068616 1804261 := bbase (se 4 (by rfl) ⟨169149, by rfl⟩ : syracuseStep 1804261 = 338299) (by norm_num)
theorem B1607669 : Blo 1068616 1607669 := bbase (se 5 (by rfl) ⟨75359, by rfl⟩ : syracuseStep 1607669 = 150719) (by norm_num)
theorem B1607693 : Blo 1068616 1607693 := bbase (se 3 (by rfl) ⟨301442, by rfl⟩ : syracuseStep 1607693 = 602885) (by norm_num)
theorem B1607717 : Blo 1068616 1607717 := bbase (se 4 (by rfl) ⟨150723, by rfl⟩ : syracuseStep 1607717 = 301447) (by norm_num)
theorem B1804349 : Blo 1068616 1804349 := bbase (se 3 (by rfl) ⟨338315, by rfl⟩ : syracuseStep 1804349 = 676631) (by norm_num)
theorem B1607741 : Blo 1068616 1607741 := bbase (se 3 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 1607741 = 602903) (by norm_num)
theorem B1607765 : Blo 1068616 1607765 := bbase (se 8 (by rfl) ⟨9420, by rfl⟩ : syracuseStep 1607765 = 18841) (by norm_num)
theorem B1607789 : Blo 1068616 1607789 := bbase (se 3 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 1607789 = 602921) (by norm_num)
theorem B3049589 : Blo 1068616 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B1607813 : Blo 1068616 1607813 := bbase (se 4 (by rfl) ⟨150732, by rfl⟩ : syracuseStep 1607813 = 301465) (by norm_num)
theorem B1607837 : Blo 1068616 1607837 := bbase (se 3 (by rfl) ⟨301469, by rfl⟩ : syracuseStep 1607837 = 602939) (by norm_num)
theorem B1607861 : Blo 1068616 1607861 := bbase (se 5 (by rfl) ⟨75368, by rfl⟩ : syracuseStep 1607861 = 150737) (by norm_num)
theorem B1804477 : Blo 1068616 1804477 := bbase (se 3 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 1804477 = 676679) (by norm_num)
theorem B1607885 : Blo 1068616 1607885 := bbase (se 3 (by rfl) ⟨301478, by rfl⟩ : syracuseStep 1607885 = 602957) (by norm_num)
theorem B4950245 : Blo 1068616 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B1607909 : Blo 1068616 1607909 := bbase (se 4 (by rfl) ⟨150741, by rfl⟩ : syracuseStep 1607909 = 301483) (by norm_num)
theorem B1607933 : Blo 1068616 1607933 := bbase (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) (by norm_num)
theorem B1804565 : Blo 1068616 1804565 := bbase (se 6 (by rfl) ⟨42294, by rfl⟩ : syracuseStep 1804565 = 84589) (by norm_num)
theorem B1607957 : Blo 1068616 1607957 := bbase (se 6 (by rfl) ⟨37686, by rfl⟩ : syracuseStep 1607957 = 75373) (by norm_num)
theorem B3606821 : Blo 1068616 3606821 := bbase (se 4 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 3606821 = 676279) (by norm_num)
theorem B1607981 : Blo 1068616 1607981 := bbase (se 3 (by rfl) ⟨301496, by rfl⟩ : syracuseStep 1607981 = 602993) (by norm_num)
theorem B1608005 : Blo 1068616 1608005 := bbase (se 4 (by rfl) ⟨150750, by rfl⟩ : syracuseStep 1608005 = 301501) (by norm_num)
theorem B1608029 : Blo 1068616 1608029 := bbase (se 3 (by rfl) ⟨301505, by rfl⟩ : syracuseStep 1608029 = 603011) (by norm_num)
theorem B1608053 : Blo 1068616 1608053 := bbase (se 5 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 1608053 = 150755) (by norm_num)
theorem B1608077 : Blo 1068616 1608077 := bbase (se 3 (by rfl) ⟨301514, by rfl⟩ : syracuseStep 1608077 = 603029) (by norm_num)
theorem B1804693 : Blo 1068616 1804693 := bbase (se 6 (by rfl) ⟨42297, by rfl⟩ : syracuseStep 1804693 = 84595) (by norm_num)
theorem B2034085 : Blo 1068616 2034085 := bbase (se 4 (by rfl) ⟨190695, by rfl⟩ : syracuseStep 2034085 = 381391) (by norm_num)
theorem B1608101 : Blo 1068616 1608101 := bbase (se 4 (by rfl) ⟨150759, by rfl⟩ : syracuseStep 1608101 = 301519) (by norm_num)
theorem B1608125 : Blo 1068616 1608125 := bbase (se 3 (by rfl) ⟨301523, by rfl⟩ : syracuseStep 1608125 = 603047) (by norm_num)
theorem B1608149 : Blo 1068616 1608149 := bbase (se 7 (by rfl) ⟨18845, by rfl⟩ : syracuseStep 1608149 = 37691) (by norm_num)
theorem B1804781 : Blo 1068616 1804781 := bbase (se 3 (by rfl) ⟨338396, by rfl⟩ : syracuseStep 1804781 = 676793) (by norm_num)
theorem B1608173 : Blo 1068616 1608173 := bbase (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) (by norm_num)
theorem B1608197 : Blo 1068616 1608197 := bbase (se 4 (by rfl) ⟨150768, by rfl⟩ : syracuseStep 1608197 = 301537) (by norm_num)
theorem B1739293 : Blo 1068616 1739293 := bbase (se 3 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 1739293 = 652235) (by norm_num)
theorem B1608221 : Blo 1068616 1608221 := bbase (se 3 (by rfl) ⟨301541, by rfl⟩ : syracuseStep 1608221 = 603083) (by norm_num)
theorem B2034229 : Blo 1068616 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1608245 : Blo 1068616 1608245 := bbase (se 5 (by rfl) ⟨75386, by rfl⟩ : syracuseStep 1608245 = 150773) (by norm_num)
theorem B1608269 : Blo 1068616 1608269 := bbase (se 3 (by rfl) ⟨301550, by rfl⟩ : syracuseStep 1608269 = 603101) (by norm_num)
theorem B1608293 : Blo 1068616 1608293 := bbase (se 4 (by rfl) ⟨150777, by rfl⟩ : syracuseStep 1608293 = 301555) (by norm_num)
theorem B1804909 : Blo 1068616 1804909 := bbase (se 3 (by rfl) ⟨338420, by rfl⟩ : syracuseStep 1804909 = 676841) (by norm_num)
theorem B1608317 : Blo 1068616 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B1608341 : Blo 1068616 1608341 := bbase (se 6 (by rfl) ⟨37695, by rfl⟩ : syracuseStep 1608341 = 75391) (by norm_num)
theorem B1608365 : Blo 1068616 1608365 := bbase (se 3 (by rfl) ⟨301568, by rfl⟩ : syracuseStep 1608365 = 603137) (by norm_num)
theorem B1804997 : Blo 1068616 1804997 := bbase (se 4 (by rfl) ⟨169218, by rfl⟩ : syracuseStep 1804997 = 338437) (by norm_num)
theorem B1608389 : Blo 1068616 1608389 := bbase (se 4 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 1608389 = 301573) (by norm_num)
theorem B3607253 : Blo 1068616 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B2034389 : Blo 1068616 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B1608413 : Blo 1068616 1608413 := bbase (se 3 (by rfl) ⟨301577, by rfl⟩ : syracuseStep 1608413 = 603155) (by norm_num)
theorem B1608437 : Blo 1068616 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B1608461 : Blo 1068616 1608461 := bbase (se 3 (by rfl) ⟨301586, by rfl⟩ : syracuseStep 1608461 = 603173) (by norm_num)
theorem B1608485 : Blo 1068616 1608485 := bbase (se 4 (by rfl) ⟨150795, by rfl⟩ : syracuseStep 1608485 = 301591) (by norm_num)
theorem B1608509 : Blo 1068616 1608509 := bbase (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) (by norm_num)
theorem B1805125 : Blo 1068616 1805125 := bbase (se 4 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 1805125 = 338461) (by norm_num)
theorem B1608533 : Blo 1068616 1608533 := bbase (se 9 (by rfl) ⟨4712, by rfl⟩ : syracuseStep 1608533 = 9425) (by norm_num)
theorem B2034533 : Blo 1068616 2034533 := bbase (se 4 (by rfl) ⟨190737, by rfl⟩ : syracuseStep 2034533 = 381475) (by norm_num)
theorem B1608557 : Blo 1068616 1608557 := bbase (se 3 (by rfl) ⟨301604, by rfl⟩ : syracuseStep 1608557 = 603209) (by norm_num)
theorem B1608581 : Blo 1068616 1608581 := bbase (se 4 (by rfl) ⟨150804, by rfl⟩ : syracuseStep 1608581 = 301609) (by norm_num)
theorem B1805213 : Blo 1068616 1805213 := bbase (se 3 (by rfl) ⟨338477, by rfl⟩ : syracuseStep 1805213 = 676955) (by norm_num)
theorem B1608605 : Blo 1068616 1608605 := bbase (se 3 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 1608605 = 603227) (by norm_num)
theorem B3476405 : Blo 1068616 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B1608629 : Blo 1068616 1608629 := bbase (se 5 (by rfl) ⟨75404, by rfl⟩ : syracuseStep 1608629 = 150809) (by norm_num)
theorem B1608653 : Blo 1068616 1608653 := bbase (se 3 (by rfl) ⟨301622, by rfl⟩ : syracuseStep 1608653 = 603245) (by norm_num)
theorem B1608677 : Blo 1068616 1608677 := bbase (se 4 (by rfl) ⟨150813, by rfl⟩ : syracuseStep 1608677 = 301627) (by norm_num)
theorem B1608701 : Blo 1068616 1608701 := bbase (se 3 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 1608701 = 603263) (by norm_num)
theorem B1608725 : Blo 1068616 1608725 := bbase (se 6 (by rfl) ⟨37704, by rfl⟩ : syracuseStep 1608725 = 75409) (by norm_num)
theorem B1805341 : Blo 1068616 1805341 := bbase (se 3 (by rfl) ⟨338501, by rfl⟩ : syracuseStep 1805341 = 677003) (by norm_num)
theorem B1608749 : Blo 1068616 1608749 := bbase (se 3 (by rfl) ⟨301640, by rfl⟩ : syracuseStep 1608749 = 603281) (by norm_num)
theorem B1608773 : Blo 1068616 1608773 := bbase (se 4 (by rfl) ⟨150822, by rfl⟩ : syracuseStep 1608773 = 301645) (by norm_num)
theorem B3050581 : Blo 1068616 3050581 := bbase (se 8 (by rfl) ⟨17874, by rfl⟩ : syracuseStep 3050581 = 35749) (by norm_num)
theorem B1608797 : Blo 1068616 1608797 := bbase (se 3 (by rfl) ⟨301649, by rfl⟩ : syracuseStep 1608797 = 603299) (by norm_num)
theorem B1444981 : Blo 1068616 1444981 := bbase (se 5 (by rfl) ⟨67733, by rfl⟩ : syracuseStep 1444981 = 135467) (by norm_num)
theorem B1805429 : Blo 1068616 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B6261877 : Blo 1068616 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B1608821 : Blo 1068616 1608821 := bbase (se 5 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 1608821 = 150827) (by norm_num)
theorem B3607685 : Blo 1068616 3607685 := bbase (se 4 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 3607685 = 676441) (by norm_num)
theorem B2034821 : Blo 1068616 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B1608845 : Blo 1068616 1608845 := bbase (se 3 (by rfl) ⟨301658, by rfl⟩ : syracuseStep 1608845 = 603317) (by norm_num)
theorem B4066469 : Blo 1068616 4066469 := bbase (se 4 (by rfl) ⟨381231, by rfl⟩ : syracuseStep 4066469 = 762463) (by norm_num)
theorem B1608869 : Blo 1068616 1608869 := bbase (se 4 (by rfl) ⟨150831, by rfl⟩ : syracuseStep 1608869 = 301663) (by norm_num)
theorem B1608893 : Blo 1068616 1608893 := bbase (se 3 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 1608893 = 603335) (by norm_num)
theorem B5409989 : Blo 1068616 5409989 := bbase (se 4 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 5409989 = 1014373) (by norm_num)
theorem B4885717 : Blo 1068616 4885717 := bbase (se 7 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 4885717 = 114509) (by norm_num)
theorem B1608917 : Blo 1068616 1608917 := bbase (se 7 (by rfl) ⟨18854, by rfl⟩ : syracuseStep 1608917 = 37709) (by norm_num)
theorem B1805557 : Blo 1068616 1805557 := bbase (se 5 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 1805557 = 169271) (by norm_num)
theorem B2034973 : Blo 1068616 2034973 := bbase (se 3 (by rfl) ⟨381557, by rfl⟩ : syracuseStep 2034973 = 763115) (by norm_num)
theorem B1805645 : Blo 1068616 1805645 := bbase (se 3 (by rfl) ⟨338558, by rfl⟩ : syracuseStep 1805645 = 677117) (by norm_num)
theorem B4066757 : Blo 1068616 4066757 := bbase (se 4 (by rfl) ⟨381258, by rfl⟩ : syracuseStep 4066757 = 762517) (by norm_num)
theorem B1805773 : Blo 1068616 1805773 := bbase (se 3 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 1805773 = 677165) (by norm_num)
theorem B1805861 : Blo 1068616 1805861 := bbase (se 4 (by rfl) ⟨169299, by rfl⟩ : syracuseStep 1805861 = 338599) (by norm_num)
theorem B3608117 : Blo 1068616 3608117 := bbase (se 5 (by rfl) ⟨169130, by rfl⟩ : syracuseStep 3608117 = 338261) (by norm_num)
theorem B2035277 : Blo 1068616 2035277 := bbase (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) (by norm_num)
theorem B1805989 : Blo 1068616 1805989 := bbase (se 4 (by rfl) ⟨169311, by rfl⟩ : syracuseStep 1805989 = 338623) (by norm_num)
theorem B1412813 : Blo 1068616 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B9899765 : Blo 1068616 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B8130293 : Blo 1068616 8130293 := bbase (se 5 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 8130293 = 762215) (by norm_num)
theorem B1806077 : Blo 1068616 1806077 := bbase (se 3 (by rfl) ⟨338639, by rfl⟩ : syracuseStep 1806077 = 677279) (by norm_num)
theorem B1806205 : Blo 1068616 1806205 := bbase (se 3 (by rfl) ⟨338663, by rfl⟩ : syracuseStep 1806205 = 677327) (by norm_num)
theorem B1806293 : Blo 1068616 1806293 := bbase (se 7 (by rfl) ⟨21167, by rfl⟩ : syracuseStep 1806293 = 42335) (by norm_num)
theorem B3608549 : Blo 1068616 3608549 := bbase (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) (by norm_num)
theorem B1806421 : Blo 1068616 1806421 := bbase (se 8 (by rfl) ⟨10584, by rfl⟩ : syracuseStep 1806421 = 21169) (by norm_num)
theorem B3051685 : Blo 1068616 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B1806509 : Blo 1068616 1806509 := bbase (se 3 (by rfl) ⟨338720, by rfl⟩ : syracuseStep 1806509 = 677441) (by norm_num)
theorem B1085653 : Blo 1068616 1085653 := bbase (se 7 (by rfl) ⟨12722, by rfl⟩ : syracuseStep 1085653 = 25445) (by norm_num)
theorem B1806637 : Blo 1068616 1806637 := bbase (se 3 (by rfl) ⟨338744, by rfl⟩ : syracuseStep 1806637 = 677489) (by norm_num)
theorem B2036029 : Blo 1068616 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B19501397 : Blo 1068616 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B1806725 : Blo 1068616 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B3608981 : Blo 1068616 3608981 := bbase (se 6 (by rfl) ⟨84585, by rfl⟩ : syracuseStep 3608981 = 169171) (by norm_num)
theorem B2036173 : Blo 1068616 2036173 := bbase (se 3 (by rfl) ⟨381782, by rfl⟩ : syracuseStep 2036173 = 763565) (by norm_num)
theorem B5411285 : Blo 1068616 5411285 := bbase (se 7 (by rfl) ⟨63413, by rfl⟩ : syracuseStep 5411285 = 126827) (by norm_num)
theorem B1085929 : Blo 1068616 1085929 := bbase (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) (by norm_num)
theorem B2200069 : Blo 1068616 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B1806853 : Blo 1068616 1806853 := bbase (se 4 (by rfl) ⟨169392, by rfl⟩ : syracuseStep 1806853 = 338785) (by norm_num)
theorem B1806941 : Blo 1068616 1806941 := bbase (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) (by norm_num)
theorem B4067941 : Blo 1068616 4067941 := bbase (se 4 (by rfl) ⟨381369, by rfl⟩ : syracuseStep 4067941 = 762739) (by norm_num)
theorem B7705205 : Blo 1068616 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B1807069 : Blo 1068616 1807069 := bbase (se 3 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 1807069 = 677651) (by norm_num)
theorem B1807157 : Blo 1068616 1807157 := bbase (se 5 (by rfl) ⟨84710, by rfl⟩ : syracuseStep 1807157 = 169421) (by norm_num)
theorem B3609413 : Blo 1068616 3609413 := bbase (se 4 (by rfl) ⟨338382, by rfl⟩ : syracuseStep 3609413 = 676765) (by norm_num)
theorem B4068245 : Blo 1068616 4068245 := bbase (se 6 (by rfl) ⟨95349, by rfl⟩ : syracuseStep 4068245 = 190699) (by norm_num)
theorem B1807285 : Blo 1068616 1807285 := bbase (se 5 (by rfl) ⟨84716, by rfl⟩ : syracuseStep 1807285 = 169433) (by norm_num)
theorem B1807373 : Blo 1068616 1807373 := bbase (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) (by norm_num)
theorem B1807501 : Blo 1068616 1807501 := bbase (se 3 (by rfl) ⟨338906, by rfl⟩ : syracuseStep 1807501 = 677813) (by norm_num)
theorem B6100181 : Blo 1068616 6100181 := bbase (se 7 (by rfl) ⟨71486, by rfl⟩ : syracuseStep 6100181 = 142973) (by norm_num)
theorem B1807589 : Blo 1068616 1807589 := bbase (se 4 (by rfl) ⟨169461, by rfl⟩ : syracuseStep 1807589 = 338923) (by norm_num)
theorem B3609845 : Blo 1068616 3609845 := bbase (se 5 (by rfl) ⟨169211, by rfl⟩ : syracuseStep 3609845 = 338423) (by norm_num)
theorem B1807717 : Blo 1068616 1807717 := bbase (se 4 (by rfl) ⟨169473, by rfl⟩ : syracuseStep 1807717 = 338947) (by norm_num)
theorem B1807805 : Blo 1068616 1807805 := bbase (se 3 (by rfl) ⟨338963, by rfl⟩ : syracuseStep 1807805 = 677927) (by norm_num)
theorem B1807933 : Blo 1068616 1807933 := bbase (se 3 (by rfl) ⟨338987, by rfl⟩ : syracuseStep 1807933 = 677975) (by norm_num)
theorem B3053189 : Blo 1068616 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B1808021 : Blo 1068616 1808021 := bbase (se 6 (by rfl) ⟨42375, by rfl⟩ : syracuseStep 1808021 = 84751) (by norm_num)
theorem B3610277 : Blo 1068616 3610277 := bbase (se 4 (by rfl) ⟨338463, by rfl⟩ : syracuseStep 3610277 = 676927) (by norm_num)
theorem B3249845 : Blo 1068616 3249845 := bbase (se 5 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 3249845 = 304673) (by norm_num)
theorem B9148085 : Blo 1068616 9148085 := bbase (se 5 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 9148085 = 857633) (by norm_num)
theorem B5412581 : Blo 1068616 5412581 := bbase (se 4 (by rfl) ⟨507429, by rfl⟩ : syracuseStep 5412581 = 1014859) (by norm_num)
theorem B2168581 : Blo 1068616 2168581 := bbase (se 4 (by rfl) ⟨203304, by rfl⟩ : syracuseStep 2168581 = 406609) (by norm_num)
theorem B1808149 : Blo 1068616 1808149 := bbase (se 6 (by rfl) ⟨42378, by rfl⟩ : syracuseStep 1808149 = 84757) (by norm_num)
theorem B1283893 : Blo 1068616 1283893 := bbase (se 5 (by rfl) ⟨60182, by rfl⟩ : syracuseStep 1283893 = 120365) (by norm_num)
theorem B6854453 : Blo 1068616 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B1808237 : Blo 1068616 1808237 := bbase (se 3 (by rfl) ⟨339044, by rfl⟩ : syracuseStep 1808237 = 678089) (by norm_num)
theorem B1808365 : Blo 1068616 1808365 := bbase (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) (by norm_num)
theorem B1808453 : Blo 1068616 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B3610709 : Blo 1068616 3610709 := bbase (se 8 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 3610709 = 42313) (by norm_num)
theorem B1808581 : Blo 1068616 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B1808669 : Blo 1068616 1808669 := bbase (se 3 (by rfl) ⟨339125, by rfl⟩ : syracuseStep 1808669 = 678251) (by norm_num)
theorem B6101365 : Blo 1068616 6101365 := bbase (se 5 (by rfl) ⟨286001, by rfl⟩ : syracuseStep 6101365 = 572003) (by norm_num)
theorem B1808797 : Blo 1068616 1808797 := bbase (se 3 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 1808797 = 678299) (by norm_num)
theorem B1448381 : Blo 1068616 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B1808885 : Blo 1068616 1808885 := bbase (se 5 (by rfl) ⟨84791, by rfl⟩ : syracuseStep 1808885 = 169583) (by norm_num)
theorem B3611141 : Blo 1068616 3611141 := bbase (se 4 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 3611141 = 677089) (by norm_num)
theorem B21142037 : Blo 1068616 21142037 := bbase (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) (by norm_num)
theorem B1809013 : Blo 1068616 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B1809101 : Blo 1068616 1809101 := bbase (se 3 (by rfl) ⟨339206, by rfl⟩ : syracuseStep 1809101 = 678413) (by norm_num)
theorem B1809229 : Blo 1068616 1809229 := bbase (se 3 (by rfl) ⟨339230, by rfl⟩ : syracuseStep 1809229 = 678461) (by norm_num)
theorem B13736789 : Blo 1068616 13736789 := bbase (se 9 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 13736789 = 80489) (by norm_num)
theorem B1284989 : Blo 1068616 1284989 := bbase (se 3 (by rfl) ⟨240935, by rfl⟩ : syracuseStep 1284989 = 481871) (by norm_num)
theorem B1809317 : Blo 1068616 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B3611573 : Blo 1068616 3611573 := bbase (se 5 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 3611573 = 338585) (by norm_num)
theorem B4070357 : Blo 1068616 4070357 := bbase (se 7 (by rfl) ⟨47699, by rfl⟩ : syracuseStep 4070357 = 95399) (by norm_num)
theorem B5413877 : Blo 1068616 5413877 := bbase (se 5 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 5413877 = 507551) (by norm_num)
theorem B1448965 : Blo 1068616 1448965 := bbase (se 4 (by rfl) ⟨135840, by rfl⟩ : syracuseStep 1448965 = 271681) (by norm_num)
theorem B1809445 : Blo 1068616 1809445 := bbase (se 4 (by rfl) ⟨169635, by rfl⟩ : syracuseStep 1809445 = 339271) (by norm_num)
theorem B1219645 : Blo 1068616 1219645 := bbase (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) (by norm_num)
theorem B1219681 : Blo 1068616 1219681 := bbase (se 2 (by rfl) ⟨457380, by rfl⟩ : syracuseStep 1219681 = 914761) (by norm_num)
theorem B1809533 : Blo 1068616 1809533 := bbase (se 3 (by rfl) ⟨339287, by rfl⟩ : syracuseStep 1809533 = 678575) (by norm_num)
theorem B4070645 : Blo 1068616 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B1809661 : Blo 1068616 1809661 := bbase (se 3 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 1809661 = 678623) (by norm_num)
theorem B1809749 : Blo 1068616 1809749 := bbase (se 11 (by rfl) ⟨1325, by rfl⟩ : syracuseStep 1809749 = 2651) (by norm_num)
theorem B3612005 : Blo 1068616 3612005 := bbase (se 4 (by rfl) ⟨338625, by rfl⟩ : syracuseStep 3612005 = 677251) (by norm_num)
theorem B2891173 : Blo 1068616 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B1809877 : Blo 1068616 1809877 := bbase (se 7 (by rfl) ⟨21209, by rfl⟩ : syracuseStep 1809877 = 42419) (by norm_num)
theorem B1809965 : Blo 1068616 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B1285681 : Blo 1068616 1285681 := bbase (se 2 (by rfl) ⟨482130, by rfl⟩ : syracuseStep 1285681 = 964261) (by norm_num)
theorem B4628053 : Blo 1068616 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B1285777 : Blo 1068616 1285777 := bbase (se 2 (by rfl) ⟨482166, by rfl⟩ : syracuseStep 1285777 = 964333) (by norm_num)
theorem B1711781 : Blo 1068616 1711781 := bbase (se 4 (by rfl) ⟨160479, by rfl⟩ : syracuseStep 1711781 = 320959) (by norm_num)
theorem B1220297 : Blo 1068616 1220297 := bbase (se 2 (by rfl) ⟨457611, by rfl⟩ : syracuseStep 1220297 = 915223) (by norm_num)
theorem B3612437 : Blo 1068616 3612437 := bbase (se 6 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 3612437 = 169333) (by norm_num)
theorem B5152565 : Blo 1068616 5152565 := bbase (se 5 (by rfl) ⟨241526, by rfl⟩ : syracuseStep 5152565 = 483053) (by norm_num)
theorem B1711973 : Blo 1068616 1711973 := bbase (se 4 (by rfl) ⟨160497, by rfl⟩ : syracuseStep 1711973 = 320995) (by norm_num)
theorem B13705109 : Blo 1068616 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B1220557 : Blo 1068616 1220557 := bbase (se 3 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 1220557 = 457709) (by norm_num)
theorem B1286161 : Blo 1068616 1286161 := bbase (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) (by norm_num)
theorem B5152949 : Blo 1068616 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B3612869 : Blo 1068616 3612869 := bbase (se 4 (by rfl) ⟨338706, by rfl⟩ : syracuseStep 3612869 = 677413) (by norm_num)
theorem B5415173 : Blo 1068616 5415173 := bbase (se 4 (by rfl) ⟨507672, by rfl⟩ : syracuseStep 5415173 = 1015345) (by norm_num)
theorem B6103349 : Blo 1068616 6103349 := bbase (se 5 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 6103349 = 572189) (by norm_num)
theorem B2892133 : Blo 1068616 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B4071829 : Blo 1068616 4071829 := bbase (se 6 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 4071829 = 190867) (by norm_num)
theorem B3613301 : Blo 1068616 3613301 := bbase (se 5 (by rfl) ⟨169373, by rfl⟩ : syracuseStep 3613301 = 338747) (by norm_num)
theorem B4072133 : Blo 1068616 4072133 := bbase (se 4 (by rfl) ⟨381762, by rfl⟩ : syracuseStep 4072133 = 763525) (by norm_num)
theorem B4334309 : Blo 1068616 4334309 := bbase (se 4 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 4334309 = 812683) (by norm_num)
theorem B1712909 : Blo 1068616 1712909 := bbase (se 3 (by rfl) ⟨321170, by rfl⟩ : syracuseStep 1712909 = 642341) (by norm_num)
theorem B1352477 : Blo 1068616 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B1352533 : Blo 1068616 1352533 := bbase (se 9 (by rfl) ⟨3962, by rfl⟩ : syracuseStep 1352533 = 7925) (by norm_num)
theorem B1352629 : Blo 1068616 1352629 := bbase (se 5 (by rfl) ⟨63404, by rfl⟩ : syracuseStep 1352629 = 126809) (by norm_num)
theorem B3613733 : Blo 1068616 3613733 := bbase (se 4 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 3613733 = 677575) (by norm_num)
theorem B1287209 : Blo 1068616 1287209 := bbase (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) (by norm_num)
theorem B1352801 : Blo 1068616 1352801 := bbase (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) (by norm_num)
theorem B1713293 : Blo 1068616 1713293 := bbase (se 3 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 1713293 = 642485) (by norm_num)
theorem B1352857 : Blo 1068616 1352857 := bbase (se 2 (by rfl) ⟨507321, by rfl⟩ : syracuseStep 1352857 = 1014643) (by norm_num)
theorem B2172101 : Blo 1068616 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1352953 : Blo 1068616 1352953 := bbase (se 2 (by rfl) ⟨507357, by rfl⟩ : syracuseStep 1352953 = 1014715) (by norm_num)
theorem B1713421 : Blo 1068616 1713421 := bbase (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) (by norm_num)
theorem B1287517 : Blo 1068616 1287517 := bbase (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) (by norm_num)
theorem B1287545 : Blo 1068616 1287545 := bbase (se 2 (by rfl) ⟨482829, by rfl⟩ : syracuseStep 1287545 = 965659) (by norm_num)
theorem B1353125 : Blo 1068616 1353125 := bbase (se 4 (by rfl) ⟨126855, by rfl⟩ : syracuseStep 1353125 = 253711) (by norm_num)
theorem B3614165 : Blo 1068616 3614165 := bbase (se 7 (by rfl) ⟨42353, by rfl⟩ : syracuseStep 3614165 = 84707) (by norm_num)
theorem B1353181 : Blo 1068616 1353181 := bbase (se 3 (by rfl) ⟨253721, by rfl⟩ : syracuseStep 1353181 = 507443) (by norm_num)
theorem B5416469 : Blo 1068616 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B1353277 : Blo 1068616 1353277 := bbase (se 3 (by rfl) ⟨253739, by rfl⟩ : syracuseStep 1353277 = 507479) (by norm_num)
theorem B1353449 : Blo 1068616 1353449 := bbase (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) (by norm_num)
theorem B2172701 : Blo 1068616 2172701 := bbase (se 3 (by rfl) ⟨407381, by rfl⟩ : syracuseStep 2172701 = 814763) (by norm_num)
theorem B1353505 : Blo 1068616 1353505 := bbase (se 2 (by rfl) ⟨507564, by rfl⟩ : syracuseStep 1353505 = 1015129) (by norm_num)
theorem B1288045 : Blo 1068616 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B1353601 : Blo 1068616 1353601 := bbase (se 2 (by rfl) ⟨507600, by rfl⟩ : syracuseStep 1353601 = 1015201) (by norm_num)
theorem B3614597 : Blo 1068616 3614597 := bbase (se 4 (by rfl) ⟨338868, by rfl⟩ : syracuseStep 3614597 = 677737) (by norm_num)
theorem B1353773 : Blo 1068616 1353773 := bbase (se 3 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 1353773 = 507665) (by norm_num)
theorem B3254357 : Blo 1068616 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B1353829 : Blo 1068616 1353829 := bbase (se 4 (by rfl) ⟨126921, by rfl⟩ : syracuseStep 1353829 = 253843) (by norm_num)
theorem B1353925 : Blo 1068616 1353925 := bbase (se 4 (by rfl) ⟨126930, by rfl⟩ : syracuseStep 1353925 = 253861) (by norm_num)
theorem B1714421 : Blo 1068616 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B3615029 : Blo 1068616 3615029 := bbase (se 5 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 3615029 = 338909) (by norm_num)
theorem B1354097 : Blo 1068616 1354097 := bbase (se 2 (by rfl) ⟨507786, by rfl⟩ : syracuseStep 1354097 = 1015573) (by norm_num)
theorem B1714549 : Blo 1068616 1714549 := bbase (se 5 (by rfl) ⟨80369, by rfl⟩ : syracuseStep 1714549 = 160739) (by norm_num)
theorem B1354153 : Blo 1068616 1354153 := bbase (se 2 (by rfl) ⟨507807, by rfl⟩ : syracuseStep 1354153 = 1015615) (by norm_num)
theorem B6105557 : Blo 1068616 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B1354249 : Blo 1068616 1354249 := bbase (se 2 (by rfl) ⟨507843, by rfl⟩ : syracuseStep 1354249 = 1015687) (by norm_num)
theorem B12364373 : Blo 1068616 12364373 := bbase (se 8 (by rfl) ⟨72447, by rfl⟩ : syracuseStep 12364373 = 144895) (by norm_num)
theorem B5778037 : Blo 1068616 5778037 := bbase (se 5 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 5778037 = 541691) (by norm_num)
theorem B1354421 : Blo 1068616 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B3615461 : Blo 1068616 3615461 := bbase (se 4 (by rfl) ⟨338949, by rfl⟩ : syracuseStep 3615461 = 677899) (by norm_num)
theorem B1354477 : Blo 1068616 1354477 := bbase (se 3 (by rfl) ⟨253964, by rfl⟩ : syracuseStep 1354477 = 507929) (by norm_num)
theorem B1714933 : Blo 1068616 1714933 := bbase (se 5 (by rfl) ⟨80387, by rfl⟩ : syracuseStep 1714933 = 160775) (by norm_num)
theorem B5417765 : Blo 1068616 5417765 := bbase (se 4 (by rfl) ⟨507915, by rfl⟩ : syracuseStep 5417765 = 1015831) (by norm_num)
theorem B1354573 : Blo 1068616 1354573 := bbase (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) (by norm_num)
theorem B4565909 : Blo 1068616 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B2173853 : Blo 1068616 2173853 := bbase (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) (by norm_num)
theorem B1715189 : Blo 1068616 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B1354745 : Blo 1068616 1354745 := bbase (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) (by norm_num)
theorem B1354801 : Blo 1068616 1354801 := bbase (se 2 (by rfl) ⟨508050, by rfl⟩ : syracuseStep 1354801 = 1016101) (by norm_num)
theorem B1354897 : Blo 1068616 1354897 := bbase (se 2 (by rfl) ⟨508086, by rfl⟩ : syracuseStep 1354897 = 1016173) (by norm_num)
theorem B3615893 : Blo 1068616 3615893 := bbase (se 6 (by rfl) ⟨84747, by rfl⟩ : syracuseStep 3615893 = 169495) (by norm_num)
theorem B1355069 : Blo 1068616 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B8138069 : Blo 1068616 8138069 := bbase (se 11 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 8138069 = 11921) (by norm_num)
theorem B1355125 : Blo 1068616 1355125 := bbase (se 5 (by rfl) ⟨63521, by rfl⟩ : syracuseStep 1355125 = 127043) (by norm_num)
theorem B1355221 : Blo 1068616 1355221 := bbase (se 7 (by rfl) ⟨15881, by rfl⟩ : syracuseStep 1355221 = 31763) (by norm_num)
theorem B2928197 : Blo 1068616 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B3616325 : Blo 1068616 3616325 := bbase (se 4 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 3616325 = 678061) (by norm_num)
theorem B1355393 : Blo 1068616 1355393 := bbase (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) (by norm_num)
theorem B1355449 : Blo 1068616 1355449 := bbase (se 2 (by rfl) ⟨508293, by rfl⟩ : syracuseStep 1355449 = 1016587) (by norm_num)
theorem B3092213 : Blo 1068616 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1355545 : Blo 1068616 1355545 := bbase (se 2 (by rfl) ⟨508329, by rfl⟩ : syracuseStep 1355545 = 1016659) (by norm_num)
theorem B1716061 : Blo 1068616 1716061 := bbase (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) (by norm_num)
theorem B4566901 : Blo 1068616 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B1716157 : Blo 1068616 1716157 := bbase (se 3 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 1716157 = 643559) (by norm_num)
theorem B1355717 : Blo 1068616 1355717 := bbase (se 4 (by rfl) ⟨127098, by rfl⟩ : syracuseStep 1355717 = 254197) (by norm_num)
theorem B3616757 : Blo 1068616 3616757 := bbase (se 5 (by rfl) ⟨169535, by rfl⟩ : syracuseStep 3616757 = 339071) (by norm_num)
theorem B1355773 : Blo 1068616 1355773 := bbase (se 3 (by rfl) ⟨254207, by rfl⟩ : syracuseStep 1355773 = 508415) (by norm_num)
theorem B5419061 : Blo 1068616 5419061 := bbase (se 5 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 5419061 = 508037) (by norm_num)
theorem B2404421 : Blo 1068616 2404421 := bbase (se 4 (by rfl) ⟨225414, by rfl⟩ : syracuseStep 2404421 = 450829) (by norm_num)
theorem B1355869 : Blo 1068616 1355869 := bbase (se 3 (by rfl) ⟨254225, by rfl⟩ : syracuseStep 1355869 = 508451) (by norm_num)
theorem B1716317 : Blo 1068616 1716317 := bbase (se 3 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 1716317 = 643619) (by norm_num)
theorem B1650797 : Blo 1068616 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B2404493 : Blo 1068616 2404493 := bbase (se 3 (by rfl) ⟨450842, by rfl⟩ : syracuseStep 2404493 = 901685) (by norm_num)
theorem B4337813 : Blo 1068616 4337813 := bbase (se 6 (by rfl) ⟨101667, by rfl⟩ : syracuseStep 4337813 = 203335) (by norm_num)
theorem B2404565 : Blo 1068616 2404565 := bbase (se 7 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 2404565 = 56357) (by norm_num)
theorem B6598901 : Blo 1068616 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1356041 : Blo 1068616 1356041 := bbase (se 2 (by rfl) ⟨508515, by rfl⟩ : syracuseStep 1356041 = 1017031) (by norm_num)
theorem B2404637 : Blo 1068616 2404637 := bbase (se 3 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 2404637 = 901739) (by norm_num)
theorem B1356097 : Blo 1068616 1356097 := bbase (se 2 (by rfl) ⟨508536, by rfl⟩ : syracuseStep 1356097 = 1017073) (by norm_num)
theorem B2404709 : Blo 1068616 2404709 := bbase (se 4 (by rfl) ⟨225441, by rfl⟩ : syracuseStep 2404709 = 450883) (by norm_num)
theorem B1356193 : Blo 1068616 1356193 := bbase (se 2 (by rfl) ⟨508572, by rfl⟩ : syracuseStep 1356193 = 1017145) (by norm_num)
theorem B3617189 : Blo 1068616 3617189 := bbase (se 4 (by rfl) ⟨339111, by rfl⟩ : syracuseStep 3617189 = 678223) (by norm_num)
theorem B2404781 : Blo 1068616 2404781 := bbase (se 3 (by rfl) ⟨450896, by rfl⟩ : syracuseStep 2404781 = 901793) (by norm_num)
theorem B2404853 : Blo 1068616 2404853 := bbase (se 5 (by rfl) ⟨112727, by rfl⟩ : syracuseStep 2404853 = 225455) (by norm_num)
theorem B2568709 : Blo 1068616 2568709 := bbase (se 4 (by rfl) ⟨240816, by rfl⟩ : syracuseStep 2568709 = 481633) (by norm_num)
theorem B2404925 : Blo 1068616 2404925 := bbase (se 3 (by rfl) ⟨450923, by rfl⟩ : syracuseStep 2404925 = 901847) (by norm_num)
theorem B1356365 : Blo 1068616 1356365 := bbase (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) (by norm_num)
theorem B2404997 : Blo 1068616 2404997 := bbase (se 4 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 2404997 = 450937) (by norm_num)
theorem B1356421 : Blo 1068616 1356421 := bbase (se 4 (by rfl) ⟨127164, by rfl⟩ : syracuseStep 1356421 = 254329) (by norm_num)
theorem B2405069 : Blo 1068616 2405069 := bbase (se 3 (by rfl) ⟨450950, by rfl⟩ : syracuseStep 2405069 = 901901) (by norm_num)
theorem B1356517 : Blo 1068616 1356517 := bbase (se 4 (by rfl) ⟨127173, by rfl⟩ : syracuseStep 1356517 = 254347) (by norm_num)
theorem B2405141 : Blo 1068616 2405141 := bbase (se 6 (by rfl) ⟨56370, by rfl⟩ : syracuseStep 2405141 = 112741) (by norm_num)
theorem B3617621 : Blo 1068616 3617621 := bbase (se 9 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 3617621 = 21197) (by norm_num)
theorem B2405213 : Blo 1068616 2405213 := bbase (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) (by norm_num)
theorem B1356689 : Blo 1068616 1356689 := bbase (se 2 (by rfl) ⟨508758, by rfl⟩ : syracuseStep 1356689 = 1017517) (by norm_num)
theorem B2405285 : Blo 1068616 2405285 := bbase (se 4 (by rfl) ⟨225495, by rfl⟩ : syracuseStep 2405285 = 450991) (by norm_num)
theorem B2569133 : Blo 1068616 2569133 := bbase (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) (by norm_num)
theorem B1356745 : Blo 1068616 1356745 := bbase (se 2 (by rfl) ⟨508779, by rfl⟩ : syracuseStep 1356745 = 1017559) (by norm_num)
theorem B2405357 : Blo 1068616 2405357 := bbase (se 3 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 2405357 = 902009) (by norm_num)
theorem B1356841 : Blo 1068616 1356841 := bbase (se 2 (by rfl) ⟨508815, by rfl⟩ : syracuseStep 1356841 = 1017631) (by norm_num)
theorem B2405429 : Blo 1068616 2405429 := bbase (se 5 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 2405429 = 225509) (by norm_num)
theorem B2405501 : Blo 1068616 2405501 := bbase (se 3 (by rfl) ⟨451031, by rfl⟩ : syracuseStep 2405501 = 902063) (by norm_num)
theorem B2929829 : Blo 1068616 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B2405573 : Blo 1068616 2405573 := bbase (se 4 (by rfl) ⟨225522, by rfl⟩ : syracuseStep 2405573 = 451045) (by norm_num)
theorem B1717445 : Blo 1068616 1717445 := bbase (se 4 (by rfl) ⟨161010, by rfl⟩ : syracuseStep 1717445 = 322021) (by norm_num)
theorem B2569421 : Blo 1068616 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B1357013 : Blo 1068616 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B4338917 : Blo 1068616 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B3618053 : Blo 1068616 3618053 := bbase (se 4 (by rfl) ⟨339192, by rfl⟩ : syracuseStep 3618053 = 678385) (by norm_num)
theorem B2405645 : Blo 1068616 2405645 := bbase (se 3 (by rfl) ⟨451058, by rfl⟩ : syracuseStep 2405645 = 902117) (by norm_num)
theorem B1357069 : Blo 1068616 1357069 := bbase (se 3 (by rfl) ⟨254450, by rfl⟩ : syracuseStep 1357069 = 508901) (by norm_num)
theorem B5420357 : Blo 1068616 5420357 := bbase (se 4 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 5420357 = 1016317) (by norm_num)
theorem B2405717 : Blo 1068616 2405717 := bbase (se 13 (by rfl) ⟨440, by rfl⟩ : syracuseStep 2405717 = 881) (by norm_num)
theorem B1357165 : Blo 1068616 1357165 := bbase (se 3 (by rfl) ⟨254468, by rfl⟩ : syracuseStep 1357165 = 508937) (by norm_num)
theorem B2405789 : Blo 1068616 2405789 := bbase (se 3 (by rfl) ⟨451085, by rfl⟩ : syracuseStep 2405789 = 902171) (by norm_num)
theorem B2405861 : Blo 1068616 2405861 := bbase (se 4 (by rfl) ⟨225549, by rfl⟩ : syracuseStep 2405861 = 451099) (by norm_num)
theorem B1357337 : Blo 1068616 1357337 := bbase (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) (by norm_num)
theorem B2405933 : Blo 1068616 2405933 := bbase (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) (by norm_num)
theorem B9156149 : Blo 1068616 9156149 := bbase (se 5 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 9156149 = 858389) (by norm_num)
theorem B1357393 : Blo 1068616 1357393 := bbase (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) (by norm_num)
theorem B2406005 : Blo 1068616 2406005 := bbase (se 5 (by rfl) ⟨112781, by rfl⟩ : syracuseStep 2406005 = 225563) (by norm_num)
theorem B1357489 : Blo 1068616 1357489 := bbase (se 2 (by rfl) ⟨509058, by rfl⟩ : syracuseStep 1357489 = 1018117) (by norm_num)
theorem B3618485 : Blo 1068616 3618485 := bbase (se 5 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 3618485 = 339233) (by norm_num)
theorem B2406077 : Blo 1068616 2406077 := bbase (se 3 (by rfl) ⟨451139, by rfl⟩ : syracuseStep 2406077 = 902279) (by norm_num)
theorem B1717957 : Blo 1068616 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B2406149 : Blo 1068616 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B2897669 : Blo 1068616 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B2406221 : Blo 1068616 2406221 := bbase (se 3 (by rfl) ⟨451166, by rfl⟩ : syracuseStep 2406221 = 902333) (by norm_num)
theorem B2406293 : Blo 1068616 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B2406365 : Blo 1068616 2406365 := bbase (se 3 (by rfl) ⟨451193, by rfl⟩ : syracuseStep 2406365 = 902387) (by norm_num)
theorem B2406437 : Blo 1068616 2406437 := bbase (se 4 (by rfl) ⟨225603, by rfl⟩ : syracuseStep 2406437 = 451207) (by norm_num)
theorem B8697941 : Blo 1068616 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B3618917 : Blo 1068616 3618917 := bbase (se 4 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 3618917 = 678547) (by norm_num)
theorem B2406509 : Blo 1068616 2406509 := bbase (se 3 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 2406509 = 902441) (by norm_num)
theorem B2406581 : Blo 1068616 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B3258613 : Blo 1068616 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B2406653 : Blo 1068616 2406653 := bbase (se 3 (by rfl) ⟨451247, by rfl⟩ : syracuseStep 2406653 = 902495) (by norm_num)
theorem B2406725 : Blo 1068616 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B2406797 : Blo 1068616 2406797 := bbase (se 3 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 2406797 = 902549) (by norm_num)
theorem B2406869 : Blo 1068616 2406869 := bbase (se 7 (by rfl) ⟨28205, by rfl⟩ : syracuseStep 2406869 = 56411) (by norm_num)
theorem B3389957 : Blo 1068616 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B3619349 : Blo 1068616 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B2406941 : Blo 1068616 2406941 := bbase (se 3 (by rfl) ⟨451301, by rfl⟩ : syracuseStep 2406941 = 902603) (by norm_num)
theorem B5421653 : Blo 1068616 5421653 := bbase (se 8 (by rfl) ⟨31767, by rfl⟩ : syracuseStep 5421653 = 63535) (by norm_num)
theorem B2407013 : Blo 1068616 2407013 := bbase (se 4 (by rfl) ⟨225657, by rfl⟩ : syracuseStep 2407013 = 451315) (by norm_num)
theorem B2407085 : Blo 1068616 2407085 := bbase (se 3 (by rfl) ⟨451328, by rfl⟩ : syracuseStep 2407085 = 902657) (by norm_num)
theorem B2407157 : Blo 1068616 2407157 := bbase (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) (by norm_num)
theorem B2407229 : Blo 1068616 2407229 := bbase (se 3 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 2407229 = 902711) (by norm_num)
theorem B2407301 : Blo 1068616 2407301 := bbase (se 4 (by rfl) ⟨225684, by rfl⟩ : syracuseStep 2407301 = 451369) (by norm_num)
theorem B3619781 : Blo 1068616 3619781 := bbase (se 4 (by rfl) ⟨339354, by rfl⟩ : syracuseStep 3619781 = 678709) (by norm_num)
theorem B2407373 : Blo 1068616 2407373 := bbase (se 3 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 2407373 = 902765) (by norm_num)
theorem B2407445 : Blo 1068616 2407445 := bbase (se 6 (by rfl) ⟨56424, by rfl⟩ : syracuseStep 2407445 = 112849) (by norm_num)
theorem B2473037 : Blo 1068616 2473037 := bbase (se 3 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 2473037 = 927389) (by norm_num)
theorem B15416405 : Blo 1068616 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B2407517 : Blo 1068616 2407517 := bbase (se 3 (by rfl) ⟨451409, by rfl⟩ : syracuseStep 2407517 = 902819) (by norm_num)
theorem B1391737 : Blo 1068616 1391737 := bbase (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) (by norm_num)
theorem B1522813 : Blo 1068616 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B2407589 : Blo 1068616 2407589 := bbase (se 4 (by rfl) ⟨225711, by rfl⟩ : syracuseStep 2407589 = 451423) (by norm_num)
theorem B2407661 : Blo 1068616 2407661 := bbase (se 3 (by rfl) ⟨451436, by rfl⟩ : syracuseStep 2407661 = 902873) (by norm_num)
theorem B2407733 : Blo 1068616 2407733 := bbase (se 5 (by rfl) ⟨112862, by rfl⟩ : syracuseStep 2407733 = 225725) (by norm_num)
theorem B2407805 : Blo 1068616 2407805 := bbase (se 3 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 2407805 = 902927) (by norm_num)
theorem B2407877 : Blo 1068616 2407877 := bbase (se 4 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 2407877 = 451477) (by norm_num)
theorem B2407949 : Blo 1068616 2407949 := bbase (se 3 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 2407949 = 902981) (by norm_num)
theorem B2408021 : Blo 1068616 2408021 := bbase (se 8 (by rfl) ⟨14109, by rfl⟩ : syracuseStep 2408021 = 28219) (by norm_num)
theorem B2408093 : Blo 1068616 2408093 := bbase (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) (by norm_num)
theorem B1523405 : Blo 1068616 1523405 := bbase (se 3 (by rfl) ⟨285638, by rfl⟩ : syracuseStep 1523405 = 571277) (by norm_num)
theorem B2408165 : Blo 1068616 2408165 := bbase (se 4 (by rfl) ⟨225765, by rfl⟩ : syracuseStep 2408165 = 451531) (by norm_num)
theorem B6176533 : Blo 1068616 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B1523485 : Blo 1068616 1523485 := bbase (se 3 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 1523485 = 571307) (by norm_num)
theorem B2408237 : Blo 1068616 2408237 := bbase (se 3 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 2408237 = 903089) (by norm_num)
theorem B5422949 : Blo 1068616 5422949 := bbase (se 4 (by rfl) ⟨508401, by rfl⟩ : syracuseStep 5422949 = 1016803) (by norm_num)
theorem B2408309 : Blo 1068616 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B1523605 : Blo 1068616 1523605 := bbase (se 6 (by rfl) ⟨35709, by rfl⟩ : syracuseStep 1523605 = 71419) (by norm_num)
theorem B2408381 : Blo 1068616 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B1523701 : Blo 1068616 1523701 := bbase (se 5 (by rfl) ⟨71423, by rfl⟩ : syracuseStep 1523701 = 142847) (by norm_num)
theorem B2408453 : Blo 1068616 2408453 := bbase (se 4 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 2408453 = 451585) (by norm_num)
theorem B5783573 : Blo 1068616 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B10305589 : Blo 1068616 10305589 := bbase (se 5 (by rfl) ⟨483074, by rfl⟩ : syracuseStep 10305589 = 966149) (by norm_num)
theorem B2408525 : Blo 1068616 2408525 := bbase (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) (by norm_num)
theorem B6701173 : Blo 1068616 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B2408597 : Blo 1068616 2408597 := bbase (se 6 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 2408597 = 112903) (by norm_num)
theorem B2408669 : Blo 1068616 2408669 := bbase (se 3 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 2408669 = 903251) (by norm_num)
theorem B2572573 : Blo 1068616 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B2408741 : Blo 1068616 2408741 := bbase (se 4 (by rfl) ⟨225819, by rfl⟩ : syracuseStep 2408741 = 451639) (by norm_num)
theorem B2408813 : Blo 1068616 2408813 := bbase (se 3 (by rfl) ⟨451652, by rfl⟩ : syracuseStep 2408813 = 903305) (by norm_num)
theorem B2638253 : Blo 1068616 2638253 := bbase (se 3 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 2638253 = 989345) (by norm_num)
theorem B2408885 : Blo 1068616 2408885 := bbase (se 5 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 2408885 = 225833) (by norm_num)
theorem B1524197 : Blo 1068616 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B2408957 : Blo 1068616 2408957 := bbase (se 3 (by rfl) ⟨451679, by rfl⟩ : syracuseStep 2408957 = 903359) (by norm_num)
theorem B2409029 : Blo 1068616 2409029 := bbase (se 4 (by rfl) ⟨225846, by rfl⟩ : syracuseStep 2409029 = 451693) (by norm_num)
theorem B2409101 : Blo 1068616 2409101 := bbase (se 3 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 2409101 = 903413) (by norm_num)
theorem B3424933 : Blo 1068616 3424933 := bbase (se 4 (by rfl) ⟨321087, by rfl⟩ : syracuseStep 3424933 = 642175) (by norm_num)
theorem B2507429 : Blo 1068616 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B2409173 : Blo 1068616 2409173 := bbase (se 7 (by rfl) ⟨28232, by rfl⟩ : syracuseStep 2409173 = 56465) (by norm_num)
theorem B3424997 : Blo 1068616 3424997 := bbase (se 4 (by rfl) ⟨321093, by rfl⟩ : syracuseStep 3424997 = 642187) (by norm_num)
theorem B4342517 : Blo 1068616 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B4571909 : Blo 1068616 4571909 := bbase (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) (by norm_num)
theorem B2441989 : Blo 1068616 2441989 := bbase (se 4 (by rfl) ⟨228936, by rfl⟩ : syracuseStep 2441989 = 457873) (by norm_num)
theorem B2409245 : Blo 1068616 2409245 := bbase (se 3 (by rfl) ⟨451733, by rfl⟩ : syracuseStep 2409245 = 903467) (by norm_num)
theorem B2409317 : Blo 1068616 2409317 := bbase (se 4 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 2409317 = 451747) (by norm_num)
theorem B2409389 : Blo 1068616 2409389 := bbase (se 3 (by rfl) ⟨451760, by rfl⟩ : syracuseStep 2409389 = 903521) (by norm_num)
theorem B2573245 : Blo 1068616 2573245 := bbase (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) (by norm_num)
theorem B2409461 : Blo 1068616 2409461 := bbase (se 5 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 2409461 = 225887) (by norm_num)
theorem B1524749 : Blo 1068616 1524749 := bbase (se 3 (by rfl) ⟨285890, by rfl⟩ : syracuseStep 1524749 = 571781) (by norm_num)
theorem B4572197 : Blo 1068616 4572197 := bbase (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) (by norm_num)
theorem B2409533 : Blo 1068616 2409533 := bbase (se 3 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 2409533 = 903575) (by norm_num)
theorem B5424245 : Blo 1068616 5424245 := bbase (se 5 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 5424245 = 508523) (by norm_num)
theorem B2409605 : Blo 1068616 2409605 := bbase (se 4 (by rfl) ⟨225900, by rfl⟩ : syracuseStep 2409605 = 451801) (by norm_num)
theorem B2573477 : Blo 1068616 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B2409677 : Blo 1068616 2409677 := bbase (se 3 (by rfl) ⟨451814, by rfl⟩ : syracuseStep 2409677 = 903629) (by norm_num)
theorem B2409749 : Blo 1068616 2409749 := bbase (se 6 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 2409749 = 112957) (by norm_num)
theorem B2573621 : Blo 1068616 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B2409821 : Blo 1068616 2409821 := bbase (se 3 (by rfl) ⟨451841, by rfl⟩ : syracuseStep 2409821 = 903683) (by norm_num)
theorem B2573669 : Blo 1068616 2573669 := bbase (se 4 (by rfl) ⟨241281, by rfl⟩ : syracuseStep 2573669 = 482563) (by norm_num)
theorem B2409893 : Blo 1068616 2409893 := bbase (se 4 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 2409893 = 451855) (by norm_num)
theorem B2409965 : Blo 1068616 2409965 := bbase (se 3 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 2409965 = 903737) (by norm_num)
theorem B2410037 : Blo 1068616 2410037 := bbase (se 5 (by rfl) ⟨112970, by rfl⟩ : syracuseStep 2410037 = 225941) (by norm_num)
theorem B2410109 : Blo 1068616 2410109 := bbase (se 3 (by rfl) ⟨451895, by rfl⟩ : syracuseStep 2410109 = 903791) (by norm_num)
theorem B2573957 : Blo 1068616 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B2410181 : Blo 1068616 2410181 := bbase (se 4 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 2410181 = 451909) (by norm_num)
theorem B1525501 : Blo 1068616 1525501 := bbase (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) (by norm_num)
theorem B2443013 : Blo 1068616 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B2410253 : Blo 1068616 2410253 := bbase (se 3 (by rfl) ⟨451922, by rfl⟩ : syracuseStep 2410253 = 903845) (by norm_num)
theorem B4572949 : Blo 1068616 4572949 := bbase (se 6 (by rfl) ⟨107178, by rfl⟩ : syracuseStep 4572949 = 214357) (by norm_num)
theorem B2705197 : Blo 1068616 2705197 := bbase (se 3 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 2705197 = 1014449) (by norm_num)
theorem B2410325 : Blo 1068616 2410325 := bbase (se 9 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 2410325 = 14123) (by norm_num)
theorem B2705309 : Blo 1068616 2705309 := bbase (se 3 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 2705309 = 1014491) (by norm_num)
theorem B2410397 : Blo 1068616 2410397 := bbase (se 3 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 2410397 = 903899) (by norm_num)
theorem B2410469 : Blo 1068616 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B2410541 : Blo 1068616 2410541 := bbase (se 3 (by rfl) ⟨451976, by rfl⟩ : syracuseStep 2410541 = 903953) (by norm_num)
theorem B2705501 : Blo 1068616 2705501 := bbase (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) (by norm_num)
theorem B2410613 : Blo 1068616 2410613 := bbase (se 5 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 2410613 = 225995) (by norm_num)
theorem B2410685 : Blo 1068616 2410685 := bbase (se 3 (by rfl) ⟨452003, by rfl⟩ : syracuseStep 2410685 = 904007) (by norm_num)
theorem B2410757 : Blo 1068616 2410757 := bbase (se 4 (by rfl) ⟨226008, by rfl⟩ : syracuseStep 2410757 = 452017) (by norm_num)
theorem B2410829 : Blo 1068616 2410829 := bbase (se 3 (by rfl) ⟨452030, by rfl⟩ : syracuseStep 2410829 = 904061) (by norm_num)
theorem B6867317 : Blo 1068616 6867317 := bbase (se 5 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 6867317 = 643811) (by norm_num)
theorem B5425541 : Blo 1068616 5425541 := bbase (se 4 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 5425541 = 1017289) (by norm_num)
theorem B2410901 : Blo 1068616 2410901 := bbase (se 6 (by rfl) ⟨56505, by rfl⟩ : syracuseStep 2410901 = 113011) (by norm_num)
theorem B2705845 : Blo 1068616 2705845 := bbase (se 5 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 2705845 = 253673) (by norm_num)
theorem B2410973 : Blo 1068616 2410973 := bbase (se 3 (by rfl) ⟨452057, by rfl⟩ : syracuseStep 2410973 = 904115) (by norm_num)
theorem B4573685 : Blo 1068616 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B1526293 : Blo 1068616 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B2705957 : Blo 1068616 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B2411045 : Blo 1068616 2411045 := bbase (se 4 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 2411045 = 452071) (by norm_num)
theorem B3525205 : Blo 1068616 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B2411117 : Blo 1068616 2411117 := bbase (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) (by norm_num)
theorem B2411189 : Blo 1068616 2411189 := bbase (se 5 (by rfl) ⟨113024, by rfl⟩ : syracuseStep 2411189 = 226049) (by norm_num)
theorem B2706149 : Blo 1068616 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B2411261 : Blo 1068616 2411261 := bbase (se 3 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 2411261 = 904223) (by norm_num)
theorem B10275605 : Blo 1068616 10275605 := bbase (se 6 (by rfl) ⟨240834, by rfl⟩ : syracuseStep 10275605 = 481669) (by norm_num)
theorem B2411333 : Blo 1068616 2411333 := bbase (se 4 (by rfl) ⟨226062, by rfl⟩ : syracuseStep 2411333 = 452125) (by norm_num)
theorem B1526629 : Blo 1068616 1526629 := bbase (se 4 (by rfl) ⟨143121, by rfl⟩ : syracuseStep 1526629 = 286243) (by norm_num)
theorem B2411405 : Blo 1068616 2411405 := bbase (se 3 (by rfl) ⟨452138, by rfl⟩ : syracuseStep 2411405 = 904277) (by norm_num)
theorem B2411477 : Blo 1068616 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B2411549 : Blo 1068616 2411549 := bbase (se 3 (by rfl) ⟨452165, by rfl⟩ : syracuseStep 2411549 = 904331) (by norm_num)
theorem B2706493 : Blo 1068616 2706493 := bbase (se 3 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 2706493 = 1014935) (by norm_num)
theorem B1526845 : Blo 1068616 1526845 := bbase (se 3 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 1526845 = 572567) (by norm_num)
theorem B2411621 : Blo 1068616 2411621 := bbase (se 4 (by rfl) ⟨226089, by rfl⟩ : syracuseStep 2411621 = 452179) (by norm_num)
theorem B2706605 : Blo 1068616 2706605 := bbase (se 3 (by rfl) ⟨507488, by rfl⟩ : syracuseStep 2706605 = 1014977) (by norm_num)
theorem B2411693 : Blo 1068616 2411693 := bbase (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) (by norm_num)
theorem B2411765 : Blo 1068616 2411765 := bbase (se 5 (by rfl) ⟨113051, by rfl⟩ : syracuseStep 2411765 = 226103) (by norm_num)
theorem B9784597 : Blo 1068616 9784597 := bbase (se 6 (by rfl) ⟨229326, by rfl⟩ : syracuseStep 9784597 = 458653) (by norm_num)
theorem B2411837 : Blo 1068616 2411837 := bbase (se 3 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 2411837 = 904439) (by norm_num)
theorem B2706797 : Blo 1068616 2706797 := bbase (se 3 (by rfl) ⟨507524, by rfl⟩ : syracuseStep 2706797 = 1015049) (by norm_num)
theorem B3526021 : Blo 1068616 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B2411909 : Blo 1068616 2411909 := bbase (se 4 (by rfl) ⟨226116, by rfl⟩ : syracuseStep 2411909 = 452233) (by norm_num)
theorem B1527221 : Blo 1068616 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B2411981 : Blo 1068616 2411981 := bbase (se 3 (by rfl) ⟨452246, by rfl⟩ : syracuseStep 2411981 = 904493) (by norm_num)
theorem B3853813 : Blo 1068616 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B2412053 : Blo 1068616 2412053 := bbase (se 6 (by rfl) ⟨56532, by rfl⟩ : syracuseStep 2412053 = 113065) (by norm_num)
theorem B2412125 : Blo 1068616 2412125 := bbase (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) (by norm_num)
theorem B3853973 : Blo 1068616 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B5426837 : Blo 1068616 5426837 := bbase (se 6 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 5426837 = 254383) (by norm_num)
theorem B2412197 : Blo 1068616 2412197 := bbase (se 4 (by rfl) ⟨226143, by rfl⟩ : syracuseStep 2412197 = 452287) (by norm_num)
theorem B3428021 : Blo 1068616 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B2707141 : Blo 1068616 2707141 := bbase (se 4 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 2707141 = 507589) (by norm_num)
theorem B4181701 : Blo 1068616 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B5590757 : Blo 1068616 5590757 := bbase (se 4 (by rfl) ⟨524133, by rfl⟩ : syracuseStep 5590757 = 1048267) (by norm_num)
theorem B2412269 : Blo 1068616 2412269 := bbase (se 3 (by rfl) ⟨452300, by rfl⟩ : syracuseStep 2412269 = 904601) (by norm_num)
theorem B2707253 : Blo 1068616 2707253 := bbase (se 5 (by rfl) ⟨126902, by rfl⟩ : syracuseStep 2707253 = 253805) (by norm_num)
theorem B2412341 : Blo 1068616 2412341 := bbase (se 5 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 2412341 = 226157) (by norm_num)
theorem B2477933 : Blo 1068616 2477933 := bbase (se 3 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 2477933 = 929225) (by norm_num)
theorem B2412413 : Blo 1068616 2412413 := bbase (se 3 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 2412413 = 904655) (by norm_num)
theorem B2412485 : Blo 1068616 2412485 := bbase (se 4 (by rfl) ⟨226170, by rfl⟩ : syracuseStep 2412485 = 452341) (by norm_num)
theorem B2707445 : Blo 1068616 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B2084861 : Blo 1068616 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B2576389 : Blo 1068616 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B2412557 : Blo 1068616 2412557 := bbase (se 3 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 2412557 = 904709) (by norm_num)
theorem B2412629 : Blo 1068616 2412629 := bbase (se 8 (by rfl) ⟨14136, by rfl⟩ : syracuseStep 2412629 = 28273) (by norm_num)
theorem B4345973 : Blo 1068616 4345973 := bbase (se 5 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 4345973 = 407435) (by norm_num)
theorem B2412701 : Blo 1068616 2412701 := bbase (se 3 (by rfl) ⟨452381, by rfl⟩ : syracuseStep 2412701 = 904763) (by norm_num)
theorem B2412773 : Blo 1068616 2412773 := bbase (se 4 (by rfl) ⟨226197, by rfl⟩ : syracuseStep 2412773 = 452395) (by norm_num)
theorem B2412845 : Blo 1068616 2412845 := bbase (se 3 (by rfl) ⟨452408, by rfl⟩ : syracuseStep 2412845 = 904817) (by norm_num)
theorem B2707789 : Blo 1068616 2707789 := bbase (se 3 (by rfl) ⟨507710, by rfl⟩ : syracuseStep 2707789 = 1015421) (by norm_num)
theorem B21123413 : Blo 1068616 21123413 := bbase (se 10 (by rfl) ⟨30942, by rfl⟩ : syracuseStep 21123413 = 61885) (by norm_num)
theorem B2412917 : Blo 1068616 2412917 := bbase (se 5 (by rfl) ⟨113105, by rfl⟩ : syracuseStep 2412917 = 226211) (by norm_num)
theorem B2707901 : Blo 1068616 2707901 := bbase (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) (by norm_num)
theorem B2412989 : Blo 1068616 2412989 := bbase (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) (by norm_num)
theorem B2413061 : Blo 1068616 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B2413133 : Blo 1068616 2413133 := bbase (se 3 (by rfl) ⟨452462, by rfl⟩ : syracuseStep 2413133 = 904925) (by norm_num)
theorem B2577005 : Blo 1068616 2577005 := bbase (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) (by norm_num)
theorem B2708093 : Blo 1068616 2708093 := bbase (se 3 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 2708093 = 1015535) (by norm_num)
theorem B2413205 : Blo 1068616 2413205 := bbase (se 6 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 2413205 = 113119) (by norm_num)
theorem B9261749 : Blo 1068616 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B2413277 : Blo 1068616 2413277 := bbase (se 3 (by rfl) ⟨452489, by rfl⟩ : syracuseStep 2413277 = 904979) (by norm_num)
theorem B2413349 : Blo 1068616 2413349 := bbase (se 4 (by rfl) ⟨226251, by rfl⟩ : syracuseStep 2413349 = 452503) (by norm_num)
theorem B2282357 : Blo 1068616 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B5428133 : Blo 1068616 5428133 := bbase (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) (by norm_num)
theorem B1627069 : Blo 1068616 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B2708437 : Blo 1068616 2708437 := bbase (se 7 (by rfl) ⟨31739, by rfl⟩ : syracuseStep 2708437 = 63479) (by norm_num)
theorem B2708549 : Blo 1068616 2708549 := bbase (se 4 (by rfl) ⟨253926, by rfl⟩ : syracuseStep 2708549 = 507853) (by norm_num)
theorem B5788853 : Blo 1068616 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B2708741 : Blo 1068616 2708741 := bbase (se 4 (by rfl) ⟨253944, by rfl⟩ : syracuseStep 2708741 = 507889) (by norm_num)
theorem B32986453 : Blo 1068616 32986453 := bbase (se 17 (by rfl) ⟨377, by rfl⟩ : syracuseStep 32986453 = 755) (by norm_num)
theorem B4347445 : Blo 1068616 4347445 := bbase (se 5 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 4347445 = 407573) (by norm_num)
theorem B2709085 : Blo 1068616 2709085 := bbase (se 3 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 2709085 = 1015907) (by norm_num)
theorem B4347541 : Blo 1068616 4347541 := bbase (se 6 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 4347541 = 203791) (by norm_num)
theorem B2709197 : Blo 1068616 2709197 := bbase (se 3 (by rfl) ⟨507974, by rfl⟩ : syracuseStep 2709197 = 1015949) (by norm_num)
theorem B2283221 : Blo 1068616 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B4576981 : Blo 1068616 4576981 := bbase (se 7 (by rfl) ⟨53636, by rfl⟩ : syracuseStep 4576981 = 107273) (by norm_num)
theorem B2283365 : Blo 1068616 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B2742149 : Blo 1068616 2742149 := bbase (se 4 (by rfl) ⟨257076, by rfl⟩ : syracuseStep 2742149 = 514153) (by norm_num)
theorem B2709389 : Blo 1068616 2709389 := bbase (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) (by norm_num)
theorem B3659701 : Blo 1068616 3659701 := bbase (se 5 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 3659701 = 343097) (by norm_num)
theorem B7722965 : Blo 1068616 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B2316269 : Blo 1068616 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B1202197 : Blo 1068616 1202197 := bbase (se 6 (by rfl) ⟨28176, by rfl⟩ : syracuseStep 1202197 = 56353) (by norm_num)
theorem B1202233 : Blo 1068616 1202233 := bbase (se 2 (by rfl) ⟨450837, by rfl⟩ : syracuseStep 1202233 = 901675) (by norm_num)
theorem B1202269 : Blo 1068616 1202269 := bbase (se 3 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 1202269 = 450851) (by norm_num)
theorem B1202305 : Blo 1068616 1202305 := bbase (se 2 (by rfl) ⟨450864, by rfl⟩ : syracuseStep 1202305 = 901729) (by norm_num)
theorem B17356949 : Blo 1068616 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B1955989 : Blo 1068616 1955989 := bbase (se 6 (by rfl) ⟨45843, by rfl⟩ : syracuseStep 1955989 = 91687) (by norm_num)
theorem B6871189 : Blo 1068616 6871189 := bbase (se 6 (by rfl) ⟨161043, by rfl⟩ : syracuseStep 6871189 = 322087) (by norm_num)
theorem B1202341 : Blo 1068616 1202341 := bbase (se 4 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 1202341 = 225439) (by norm_num)
theorem B5429429 : Blo 1068616 5429429 := bbase (se 5 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 5429429 = 509009) (by norm_num)
theorem B1202377 : Blo 1068616 1202377 := bbase (se 2 (by rfl) ⟨450891, by rfl⟩ : syracuseStep 1202377 = 901783) (by norm_num)
theorem B2709733 : Blo 1068616 2709733 := bbase (se 4 (by rfl) ⟨254037, by rfl⟩ : syracuseStep 2709733 = 508075) (by norm_num)
theorem B1202413 : Blo 1068616 1202413 := bbase (se 3 (by rfl) ⟨225452, by rfl⟩ : syracuseStep 1202413 = 450905) (by norm_num)
theorem B1202449 : Blo 1068616 1202449 := bbase (se 2 (by rfl) ⟨450918, by rfl⟩ : syracuseStep 1202449 = 901837) (by norm_num)
theorem B3299621 : Blo 1068616 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B1202485 : Blo 1068616 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B2709845 : Blo 1068616 2709845 := bbase (se 10 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 2709845 = 7939) (by norm_num)
theorem B1202521 : Blo 1068616 1202521 := bbase (se 2 (by rfl) ⟨450945, by rfl⟩ : syracuseStep 1202521 = 901891) (by norm_num)
theorem B2677093 : Blo 1068616 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1202557 : Blo 1068616 1202557 := bbase (se 3 (by rfl) ⟨225479, by rfl⟩ : syracuseStep 1202557 = 450959) (by norm_num)
theorem B1202593 : Blo 1068616 1202593 := bbase (se 2 (by rfl) ⟨450972, by rfl⟩ : syracuseStep 1202593 = 901945) (by norm_num)
theorem B1202629 : Blo 1068616 1202629 := bbase (se 4 (by rfl) ⟨112746, by rfl⟩ : syracuseStep 1202629 = 225493) (by norm_num)
theorem B1202665 : Blo 1068616 1202665 := bbase (se 2 (by rfl) ⟨450999, by rfl⟩ : syracuseStep 1202665 = 901999) (by norm_num)
theorem B1202701 : Blo 1068616 1202701 := bbase (se 3 (by rfl) ⟨225506, by rfl⟩ : syracuseStep 1202701 = 451013) (by norm_num)
theorem B2710037 : Blo 1068616 2710037 := bbase (se 6 (by rfl) ⟨63516, by rfl⟩ : syracuseStep 2710037 = 127033) (by norm_num)
theorem B1628717 : Blo 1068616 1628717 := bbase (se 3 (by rfl) ⟨305384, by rfl⟩ : syracuseStep 1628717 = 610769) (by norm_num)
theorem B1202737 : Blo 1068616 1202737 := bbase (se 2 (by rfl) ⟨451026, by rfl⟩ : syracuseStep 1202737 = 902053) (by norm_num)
theorem B2284109 : Blo 1068616 2284109 := bbase (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) (by norm_num)
theorem B1202773 : Blo 1068616 1202773 := bbase (se 8 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 1202773 = 14095) (by norm_num)
theorem B1202809 : Blo 1068616 1202809 := bbase (se 2 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 1202809 = 902107) (by norm_num)
theorem B1202845 : Blo 1068616 1202845 := bbase (se 3 (by rfl) ⟨225533, by rfl⟩ : syracuseStep 1202845 = 451067) (by norm_num)
theorem B1202881 : Blo 1068616 1202881 := bbase (se 2 (by rfl) ⟨451080, by rfl⟩ : syracuseStep 1202881 = 902161) (by norm_num)
theorem B1202917 : Blo 1068616 1202917 := bbase (se 4 (by rfl) ⟨112773, by rfl⟩ : syracuseStep 1202917 = 225547) (by norm_num)
theorem B8674037 : Blo 1068616 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B1202953 : Blo 1068616 1202953 := bbase (se 2 (by rfl) ⟨451107, by rfl⟩ : syracuseStep 1202953 = 902215) (by norm_num)
theorem B1202989 : Blo 1068616 1202989 := bbase (se 3 (by rfl) ⟨225560, by rfl⟩ : syracuseStep 1202989 = 451121) (by norm_num)
theorem B1203025 : Blo 1068616 1203025 := bbase (se 2 (by rfl) ⟨451134, by rfl⟩ : syracuseStep 1203025 = 902269) (by norm_num)
theorem B2710381 : Blo 1068616 2710381 := bbase (se 3 (by rfl) ⟨508196, by rfl⟩ : syracuseStep 2710381 = 1016393) (by norm_num)
theorem B1203061 : Blo 1068616 1203061 := bbase (se 5 (by rfl) ⟨56393, by rfl⟩ : syracuseStep 1203061 = 112787) (by norm_num)
theorem B1203097 : Blo 1068616 1203097 := bbase (se 2 (by rfl) ⟨451161, by rfl⟩ : syracuseStep 1203097 = 902323) (by norm_num)
theorem B1203133 : Blo 1068616 1203133 := bbase (se 3 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 1203133 = 451175) (by norm_num)
theorem B2710493 : Blo 1068616 2710493 := bbase (se 3 (by rfl) ⟨508217, by rfl⟩ : syracuseStep 2710493 = 1016435) (by norm_num)
theorem B1203169 : Blo 1068616 1203169 := bbase (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) (by norm_num)
theorem B1203205 : Blo 1068616 1203205 := bbase (se 4 (by rfl) ⟨112800, by rfl⟩ : syracuseStep 1203205 = 225601) (by norm_num)
theorem B1203241 : Blo 1068616 1203241 := bbase (se 2 (by rfl) ⟨451215, by rfl⟩ : syracuseStep 1203241 = 902431) (by norm_num)
theorem B1203277 : Blo 1068616 1203277 := bbase (se 3 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 1203277 = 451229) (by norm_num)
theorem B1203313 : Blo 1068616 1203313 := bbase (se 2 (by rfl) ⟨451242, by rfl⟩ : syracuseStep 1203313 = 902485) (by norm_num)
theorem B1203349 : Blo 1068616 1203349 := bbase (se 6 (by rfl) ⟨28203, by rfl⟩ : syracuseStep 1203349 = 56407) (by norm_num)
theorem B2710685 : Blo 1068616 2710685 := bbase (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) (by norm_num)
theorem B1301665 : Blo 1068616 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B1203385 : Blo 1068616 1203385 := bbase (se 2 (by rfl) ⟨451269, by rfl⟩ : syracuseStep 1203385 = 902539) (by norm_num)
theorem B1203421 : Blo 1068616 1203421 := bbase (se 3 (by rfl) ⟨225641, by rfl⟩ : syracuseStep 1203421 = 451283) (by norm_num)
theorem B4119781 : Blo 1068616 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B1203457 : Blo 1068616 1203457 := bbase (se 2 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 1203457 = 902593) (by norm_num)
theorem B1203493 : Blo 1068616 1203493 := bbase (se 4 (by rfl) ⟨112827, by rfl⟩ : syracuseStep 1203493 = 225655) (by norm_num)
theorem B2284861 : Blo 1068616 2284861 := bbase (se 3 (by rfl) ⟨428411, by rfl⟩ : syracuseStep 2284861 = 856823) (by norm_num)
theorem B1203529 : Blo 1068616 1203529 := bbase (se 2 (by rfl) ⟨451323, by rfl⟩ : syracuseStep 1203529 = 902647) (by norm_num)
theorem B1203565 : Blo 1068616 1203565 := bbase (se 3 (by rfl) ⟨225668, by rfl⟩ : syracuseStep 1203565 = 451337) (by norm_num)
theorem B3431813 : Blo 1068616 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B1203601 : Blo 1068616 1203601 := bbase (se 2 (by rfl) ⟨451350, by rfl⟩ : syracuseStep 1203601 = 902701) (by norm_num)
theorem B1203637 : Blo 1068616 1203637 := bbase (se 5 (by rfl) ⟨56420, by rfl⟩ : syracuseStep 1203637 = 112841) (by norm_num)
theorem B2285005 : Blo 1068616 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B1203673 : Blo 1068616 1203673 := bbase (se 2 (by rfl) ⟨451377, by rfl⟩ : syracuseStep 1203673 = 902755) (by norm_num)
theorem B2711029 : Blo 1068616 2711029 := bbase (se 5 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 2711029 = 254159) (by norm_num)
theorem B1203709 : Blo 1068616 1203709 := bbase (se 3 (by rfl) ⟨225695, by rfl⟩ : syracuseStep 1203709 = 451391) (by norm_num)
theorem B1203745 : Blo 1068616 1203745 := bbase (se 2 (by rfl) ⟨451404, by rfl⟩ : syracuseStep 1203745 = 902809) (by norm_num)
theorem B1203781 : Blo 1068616 1203781 := bbase (se 4 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 1203781 = 225709) (by norm_num)
theorem B5135957 : Blo 1068616 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B2711141 : Blo 1068616 2711141 := bbase (se 4 (by rfl) ⟨254169, by rfl⟩ : syracuseStep 2711141 = 508339) (by norm_num)
theorem B1203817 : Blo 1068616 1203817 := bbase (se 2 (by rfl) ⟨451431, by rfl⟩ : syracuseStep 1203817 = 902863) (by norm_num)
theorem B1072769 : Blo 1068616 1072769 := bbase (se 2 (by rfl) ⟨402288, by rfl⟩ : syracuseStep 1072769 = 804577) (by norm_num)
theorem B1203853 : Blo 1068616 1203853 := bbase (se 3 (by rfl) ⟨225722, by rfl⟩ : syracuseStep 1203853 = 451445) (by norm_num)
theorem B1203889 : Blo 1068616 1203889 := bbase (se 2 (by rfl) ⟨451458, by rfl⟩ : syracuseStep 1203889 = 902917) (by norm_num)
theorem B1203925 : Blo 1068616 1203925 := bbase (se 7 (by rfl) ⟨14108, by rfl⟩ : syracuseStep 1203925 = 28217) (by norm_num)
theorem B2318053 : Blo 1068616 2318053 := bbase (se 4 (by rfl) ⟨217317, by rfl⟩ : syracuseStep 2318053 = 434635) (by norm_num)
theorem B1203961 : Blo 1068616 1203961 := bbase (se 2 (by rfl) ⟨451485, by rfl⟩ : syracuseStep 1203961 = 902971) (by norm_num)
theorem B1203997 : Blo 1068616 1203997 := bbase (se 3 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 1203997 = 451499) (by norm_num)
theorem B2711333 : Blo 1068616 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B1204033 : Blo 1068616 1204033 := bbase (se 2 (by rfl) ⟨451512, by rfl⟩ : syracuseStep 1204033 = 903025) (by norm_num)
theorem B2285381 : Blo 1068616 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B1630037 : Blo 1068616 1630037 := bbase (se 9 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 1630037 = 9551) (by norm_num)
theorem B1204069 : Blo 1068616 1204069 := bbase (se 4 (by rfl) ⟨112881, by rfl⟩ : syracuseStep 1204069 = 225763) (by norm_num)
theorem B1204105 : Blo 1068616 1204105 := bbase (se 2 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 1204105 = 903079) (by norm_num)
theorem B1204141 : Blo 1068616 1204141 := bbase (se 3 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 1204141 = 451553) (by norm_num)
theorem B9134005 : Blo 1068616 9134005 := bbase (se 5 (by rfl) ⟨428156, by rfl⟩ : syracuseStep 9134005 = 856313) (by norm_num)
theorem B1630133 : Blo 1068616 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B1204177 : Blo 1068616 1204177 := bbase (se 2 (by rfl) ⟨451566, by rfl⟩ : syracuseStep 1204177 = 903133) (by norm_num)
theorem B1204213 : Blo 1068616 1204213 := bbase (se 5 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 1204213 = 112895) (by norm_num)
theorem B1204249 : Blo 1068616 1204249 := bbase (se 2 (by rfl) ⟨451593, by rfl⟩ : syracuseStep 1204249 = 903187) (by norm_num)
theorem B1204285 : Blo 1068616 1204285 := bbase (se 3 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 1204285 = 451607) (by norm_num)
theorem B12181589 : Blo 1068616 12181589 := bbase (se 8 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 12181589 = 142753) (by norm_num)
theorem B1204321 : Blo 1068616 1204321 := bbase (se 2 (by rfl) ⟨451620, by rfl⟩ : syracuseStep 1204321 = 903241) (by norm_num)
theorem B1302653 : Blo 1068616 1302653 := bbase (se 3 (by rfl) ⟨244247, by rfl⟩ : syracuseStep 1302653 = 488495) (by norm_num)
theorem B2711677 : Blo 1068616 2711677 := bbase (se 3 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 2711677 = 1016879) (by norm_num)
theorem B1204357 : Blo 1068616 1204357 := bbase (se 4 (by rfl) ⟨112908, by rfl⟩ : syracuseStep 1204357 = 225817) (by norm_num)
theorem B1204393 : Blo 1068616 1204393 := bbase (se 2 (by rfl) ⟨451647, by rfl⟩ : syracuseStep 1204393 = 903295) (by norm_num)
theorem B2285749 : Blo 1068616 2285749 := bbase (se 5 (by rfl) ⟨107144, by rfl⟩ : syracuseStep 2285749 = 214289) (by norm_num)
theorem B1204429 : Blo 1068616 1204429 := bbase (se 3 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 1204429 = 451661) (by norm_num)
theorem B2711789 : Blo 1068616 2711789 := bbase (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) (by norm_num)
theorem B1204465 : Blo 1068616 1204465 := bbase (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) (by norm_num)
theorem B1204501 : Blo 1068616 1204501 := bbase (se 6 (by rfl) ⟨28230, by rfl⟩ : syracuseStep 1204501 = 56461) (by norm_num)
theorem B3432725 : Blo 1068616 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B1204537 : Blo 1068616 1204537 := bbase (se 2 (by rfl) ⟨451701, by rfl⟩ : syracuseStep 1204537 = 903403) (by norm_num)
theorem B1204573 : Blo 1068616 1204573 := bbase (se 3 (by rfl) ⟨225857, by rfl⟩ : syracuseStep 1204573 = 451715) (by norm_num)
theorem B1204609 : Blo 1068616 1204609 := bbase (se 2 (by rfl) ⟨451728, by rfl⟩ : syracuseStep 1204609 = 903457) (by norm_num)
theorem B1630597 : Blo 1068616 1630597 := bbase (se 4 (by rfl) ⟨152868, by rfl⟩ : syracuseStep 1630597 = 305737) (by norm_num)
theorem B1630621 : Blo 1068616 1630621 := bbase (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) (by norm_num)
theorem B1204645 : Blo 1068616 1204645 := bbase (se 4 (by rfl) ⟨112935, by rfl⟩ : syracuseStep 1204645 = 225871) (by norm_num)
theorem B2711981 : Blo 1068616 2711981 := bbase (se 3 (by rfl) ⟨508496, by rfl⟩ : syracuseStep 2711981 = 1016993) (by norm_num)
theorem B1204681 : Blo 1068616 1204681 := bbase (se 2 (by rfl) ⟨451755, by rfl⟩ : syracuseStep 1204681 = 903511) (by norm_num)
theorem B1204717 : Blo 1068616 1204717 := bbase (se 3 (by rfl) ⟨225884, by rfl⟩ : syracuseStep 1204717 = 451769) (by norm_num)
theorem B1204753 : Blo 1068616 1204753 := bbase (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) (by norm_num)
theorem B2318885 : Blo 1068616 2318885 := bbase (se 4 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 2318885 = 434791) (by norm_num)
theorem B1204789 : Blo 1068616 1204789 := bbase (se 5 (by rfl) ⟨56474, by rfl⟩ : syracuseStep 1204789 = 112949) (by norm_num)
theorem B1204825 : Blo 1068616 1204825 := bbase (se 2 (by rfl) ⟨451809, by rfl⟩ : syracuseStep 1204825 = 903619) (by norm_num)
theorem B1204861 : Blo 1068616 1204861 := bbase (se 3 (by rfl) ⟨225911, by rfl⟩ : syracuseStep 1204861 = 451823) (by norm_num)
theorem B4579973 : Blo 1068616 4579973 := bbase (se 4 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 4579973 = 858745) (by norm_num)
theorem B1204897 : Blo 1068616 1204897 := bbase (se 2 (by rfl) ⟨451836, by rfl⟩ : syracuseStep 1204897 = 903673) (by norm_num)
theorem B1204933 : Blo 1068616 1204933 := bbase (se 4 (by rfl) ⟨112962, by rfl⟩ : syracuseStep 1204933 = 225925) (by norm_num)
theorem B1204969 : Blo 1068616 1204969 := bbase (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) (by norm_num)
theorem B2712325 : Blo 1068616 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B1205005 : Blo 1068616 1205005 := bbase (se 3 (by rfl) ⟨225938, by rfl⟩ : syracuseStep 1205005 = 451877) (by norm_num)
theorem B1205041 : Blo 1068616 1205041 := bbase (se 2 (by rfl) ⟨451890, by rfl⟩ : syracuseStep 1205041 = 903781) (by norm_num)
theorem B1205077 : Blo 1068616 1205077 := bbase (se 9 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 1205077 = 7061) (by norm_num)
theorem B2712437 : Blo 1068616 2712437 := bbase (se 5 (by rfl) ⟨127145, by rfl⟩ : syracuseStep 2712437 = 254291) (by norm_num)
theorem B1205113 : Blo 1068616 1205113 := bbase (se 2 (by rfl) ⟨451917, by rfl⟩ : syracuseStep 1205113 = 903835) (by norm_num)
theorem B1205149 : Blo 1068616 1205149 := bbase (se 3 (by rfl) ⟨225965, by rfl⟩ : syracuseStep 1205149 = 451931) (by norm_num)
theorem B1205185 : Blo 1068616 1205185 := bbase (se 2 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 1205185 = 903889) (by norm_num)
theorem B1205221 : Blo 1068616 1205221 := bbase (se 4 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 1205221 = 225979) (by norm_num)
theorem B1205257 : Blo 1068616 1205257 := bbase (se 2 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 1205257 = 903943) (by norm_num)
theorem B1205293 : Blo 1068616 1205293 := bbase (se 3 (by rfl) ⟨225992, by rfl⟩ : syracuseStep 1205293 = 451985) (by norm_num)
theorem B2712629 : Blo 1068616 2712629 := bbase (se 5 (by rfl) ⟨127154, by rfl⟩ : syracuseStep 2712629 = 254309) (by norm_num)
theorem B1205329 : Blo 1068616 1205329 := bbase (se 2 (by rfl) ⟨451998, by rfl⟩ : syracuseStep 1205329 = 903997) (by norm_num)
theorem B1205365 : Blo 1068616 1205365 := bbase (se 5 (by rfl) ⟨56501, by rfl⟩ : syracuseStep 1205365 = 113003) (by norm_num)
theorem B1205401 : Blo 1068616 1205401 := bbase (se 2 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 1205401 = 904051) (by norm_num)
theorem B1926317 : Blo 1068616 1926317 := bbase (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) (by norm_num)
theorem B1205437 : Blo 1068616 1205437 := bbase (se 3 (by rfl) ⟨226019, by rfl⟩ : syracuseStep 1205437 = 452039) (by norm_num)
theorem B1205473 : Blo 1068616 1205473 := bbase (se 2 (by rfl) ⟨452052, by rfl⟩ : syracuseStep 1205473 = 904105) (by norm_num)
theorem B1205509 : Blo 1068616 1205509 := bbase (se 4 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 1205509 = 226033) (by norm_num)
theorem B1205545 : Blo 1068616 1205545 := bbase (se 2 (by rfl) ⟨452079, by rfl⟩ : syracuseStep 1205545 = 904159) (by norm_num)
theorem B1205581 : Blo 1068616 1205581 := bbase (se 3 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 1205581 = 452093) (by norm_num)
theorem B13034837 : Blo 1068616 13034837 := bbase (se 12 (by rfl) ⟨4773, by rfl⟩ : syracuseStep 13034837 = 9547) (by norm_num)
theorem B1205617 : Blo 1068616 1205617 := bbase (se 2 (by rfl) ⟨452106, by rfl⟩ : syracuseStep 1205617 = 904213) (by norm_num)
theorem B2712973 : Blo 1068616 2712973 := bbase (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) (by norm_num)
theorem B1205653 : Blo 1068616 1205653 := bbase (se 6 (by rfl) ⟨28257, by rfl⟩ : syracuseStep 1205653 = 56515) (by norm_num)
theorem B1205689 : Blo 1068616 1205689 := bbase (se 2 (by rfl) ⟨452133, by rfl⟩ : syracuseStep 1205689 = 904267) (by norm_num)
theorem B1926605 : Blo 1068616 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B1205725 : Blo 1068616 1205725 := bbase (se 3 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 1205725 = 452147) (by norm_num)
theorem B2713085 : Blo 1068616 2713085 := bbase (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) (by norm_num)
theorem B1205761 : Blo 1068616 1205761 := bbase (se 2 (by rfl) ⟨452160, by rfl⟩ : syracuseStep 1205761 = 904321) (by norm_num)
theorem B1205797 : Blo 1068616 1205797 := bbase (se 4 (by rfl) ⟨113043, by rfl⟩ : syracuseStep 1205797 = 226087) (by norm_num)
theorem B1205833 : Blo 1068616 1205833 := bbase (se 2 (by rfl) ⟨452187, by rfl⟩ : syracuseStep 1205833 = 904375) (by norm_num)
theorem B3434069 : Blo 1068616 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B1205869 : Blo 1068616 1205869 := bbase (se 3 (by rfl) ⟨226100, by rfl⟩ : syracuseStep 1205869 = 452201) (by norm_num)
theorem B4580981 : Blo 1068616 4580981 := bbase (se 5 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 4580981 = 429467) (by norm_num)
theorem B1205905 : Blo 1068616 1205905 := bbase (se 2 (by rfl) ⟨452214, by rfl⟩ : syracuseStep 1205905 = 904429) (by norm_num)
theorem B2287253 : Blo 1068616 2287253 := bbase (se 6 (by rfl) ⟨53607, by rfl⟩ : syracuseStep 2287253 = 107215) (by norm_num)
theorem B1926821 : Blo 1068616 1926821 := bbase (se 4 (by rfl) ⟨180639, by rfl⟩ : syracuseStep 1926821 = 361279) (by norm_num)
theorem B1205941 : Blo 1068616 1205941 := bbase (se 5 (by rfl) ⟨56528, by rfl⟩ : syracuseStep 1205941 = 113057) (by norm_num)
theorem B2713277 : Blo 1068616 2713277 := bbase (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) (by norm_num)
theorem B1205977 : Blo 1068616 1205977 := bbase (se 2 (by rfl) ⟨452241, by rfl⟩ : syracuseStep 1205977 = 904483) (by norm_num)
theorem B1206013 : Blo 1068616 1206013 := bbase (se 3 (by rfl) ⟨226127, by rfl⟩ : syracuseStep 1206013 = 452255) (by norm_num)
theorem B1206049 : Blo 1068616 1206049 := bbase (se 2 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 1206049 = 904537) (by norm_num)
theorem B1828645 : Blo 1068616 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B2287397 : Blo 1068616 2287397 := bbase (se 4 (by rfl) ⟨214443, by rfl⟩ : syracuseStep 2287397 = 428887) (by norm_num)
theorem B1206085 : Blo 1068616 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B1206121 : Blo 1068616 1206121 := bbase (se 2 (by rfl) ⟨452295, by rfl⟩ : syracuseStep 1206121 = 904591) (by norm_num)
theorem B9135989 : Blo 1068616 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B1206157 : Blo 1068616 1206157 := bbase (se 3 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 1206157 = 452309) (by norm_num)
theorem B1206193 : Blo 1068616 1206193 := bbase (se 2 (by rfl) ⟨452322, by rfl⟩ : syracuseStep 1206193 = 904645) (by norm_num)
theorem B1206229 : Blo 1068616 1206229 := bbase (se 7 (by rfl) ⟨14135, by rfl⟩ : syracuseStep 1206229 = 28271) (by norm_num)
theorem B1206265 : Blo 1068616 1206265 := bbase (se 2 (by rfl) ⟨452349, by rfl⟩ : syracuseStep 1206265 = 904699) (by norm_num)
theorem B2713621 : Blo 1068616 2713621 := bbase (se 6 (by rfl) ⟨63600, by rfl⟩ : syracuseStep 2713621 = 127201) (by norm_num)
theorem B1206301 : Blo 1068616 1206301 := bbase (se 3 (by rfl) ⟨226181, by rfl⟩ : syracuseStep 1206301 = 452363) (by norm_num)
theorem B1206337 : Blo 1068616 1206337 := bbase (se 2 (by rfl) ⟨452376, by rfl⟩ : syracuseStep 1206337 = 904753) (by norm_num)
theorem B1206373 : Blo 1068616 1206373 := bbase (se 4 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 1206373 = 226195) (by norm_num)
theorem B2713733 : Blo 1068616 2713733 := bbase (se 4 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 2713733 = 508825) (by norm_num)
theorem B1206409 : Blo 1068616 1206409 := bbase (se 2 (by rfl) ⟨452403, by rfl⟩ : syracuseStep 1206409 = 904807) (by norm_num)
theorem B2287757 : Blo 1068616 2287757 := bbase (se 3 (by rfl) ⟨428954, by rfl⟩ : syracuseStep 2287757 = 857909) (by norm_num)
theorem B1206445 : Blo 1068616 1206445 := bbase (se 3 (by rfl) ⟨226208, by rfl⟩ : syracuseStep 1206445 = 452417) (by norm_num)
theorem B1206481 : Blo 1068616 1206481 := bbase (se 2 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 1206481 = 904861) (by norm_num)
theorem B1206517 : Blo 1068616 1206517 := bbase (se 5 (by rfl) ⟨56555, by rfl⟩ : syracuseStep 1206517 = 113111) (by norm_num)
theorem B1206553 : Blo 1068616 1206553 := bbase (se 2 (by rfl) ⟨452457, by rfl⟩ : syracuseStep 1206553 = 904915) (by norm_num)
theorem B1206589 : Blo 1068616 1206589 := bbase (se 3 (by rfl) ⟨226235, by rfl⟩ : syracuseStep 1206589 = 452471) (by norm_num)
theorem B2713925 : Blo 1068616 2713925 := bbase (se 4 (by rfl) ⟨254430, by rfl⟩ : syracuseStep 2713925 = 508861) (by norm_num)
theorem B1206625 : Blo 1068616 1206625 := bbase (se 2 (by rfl) ⟨452484, by rfl⟩ : syracuseStep 1206625 = 904969) (by norm_num)
theorem B1206661 : Blo 1068616 1206661 := bbase (se 4 (by rfl) ⟨113124, by rfl⟩ : syracuseStep 1206661 = 226249) (by norm_num)
theorem B1927685 : Blo 1068616 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B1141337 : Blo 1068616 1141337 := bbase (se 2 (by rfl) ⟨428001, by rfl⟩ : syracuseStep 1141337 = 856003) (by norm_num)
theorem B2714269 : Blo 1068616 2714269 := bbase (se 3 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 2714269 = 1017851) (by norm_num)
theorem B1141409 : Blo 1068616 1141409 := bbase (se 2 (by rfl) ⟨428028, by rfl⟩ : syracuseStep 1141409 = 856057) (by norm_num)
theorem B5794517 : Blo 1068616 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B1927909 : Blo 1068616 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B2714381 : Blo 1068616 2714381 := bbase (se 3 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 2714381 = 1017893) (by norm_num)
theorem B5794645 : Blo 1068616 5794645 := bbase (se 9 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 5794645 = 33953) (by norm_num)
theorem B1141597 : Blo 1068616 1141597 := bbase (se 3 (by rfl) ⟨214049, by rfl⟩ : syracuseStep 1141597 = 428099) (by norm_num)
theorem B2714573 : Blo 1068616 2714573 := bbase (se 3 (by rfl) ⟨508982, by rfl⟩ : syracuseStep 2714573 = 1017965) (by norm_num)
theorem B3435493 : Blo 1068616 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B2288645 : Blo 1068616 2288645 := bbase (se 4 (by rfl) ⟨214560, by rfl⟩ : syracuseStep 2288645 = 429121) (by norm_num)
theorem B1141781 : Blo 1068616 1141781 := bbase (se 6 (by rfl) ⟨26760, by rfl⟩ : syracuseStep 1141781 = 53521) (by norm_num)
theorem B2288893 : Blo 1068616 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B3665173 : Blo 1068616 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B2714917 : Blo 1068616 2714917 := bbase (se 4 (by rfl) ⟨254523, by rfl⟩ : syracuseStep 2714917 = 509047) (by norm_num)
theorem B2715029 : Blo 1068616 2715029 := bbase (se 6 (by rfl) ⟨63633, by rfl⟩ : syracuseStep 2715029 = 127267) (by norm_num)
theorem B1371701 : Blo 1068616 1371701 := bbase (se 5 (by rfl) ⟨64298, by rfl⟩ : syracuseStep 1371701 = 128597) (by norm_num)
theorem B4058693 : Blo 1068616 4058693 := bbase (se 4 (by rfl) ⟨380502, by rfl⟩ : syracuseStep 4058693 = 761005) (by norm_num)
theorem B12381781 : Blo 1068616 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B3862117 : Blo 1068616 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B1371773 : Blo 1068616 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B2289397 : Blo 1068616 2289397 := bbase (se 5 (by rfl) ⟨107315, by rfl⟩ : syracuseStep 2289397 = 214631) (by norm_num)
theorem B1142533 : Blo 1068616 1142533 := bbase (se 4 (by rfl) ⟨107112, by rfl⟩ : syracuseStep 1142533 = 214225) (by norm_num)
theorem B3043109 : Blo 1068616 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B1142605 : Blo 1068616 1142605 := bbase (se 3 (by rfl) ⟨214238, by rfl⟩ : syracuseStep 1142605 = 428477) (by norm_num)
theorem B4058981 : Blo 1068616 4058981 := bbase (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) (by norm_num)
theorem B1142785 : Blo 1068616 1142785 := bbase (se 2 (by rfl) ⟨428544, by rfl⟩ : syracuseStep 1142785 = 857089) (by norm_num)
theorem B8122517 : Blo 1068616 8122517 := bbase (se 6 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 8122517 = 380743) (by norm_num)
theorem B1143229 : Blo 1068616 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B3043781 : Blo 1068616 3043781 := bbase (se 4 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 3043781 = 570709) (by norm_num)
theorem B1143353 : Blo 1068616 1143353 := bbase (se 2 (by rfl) ⟨428757, by rfl⟩ : syracuseStep 1143353 = 857515) (by norm_num)
theorem B2290285 : Blo 1068616 2290285 := bbase (se 3 (by rfl) ⟨429428, by rfl⟩ : syracuseStep 2290285 = 858857) (by norm_num)
theorem B5501621 : Blo 1068616 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B1143605 : Blo 1068616 1143605 := bbase (se 5 (by rfl) ⟨53606, by rfl⟩ : syracuseStep 1143605 = 107213) (by norm_num)
theorem B3044213 : Blo 1068616 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B2749373 : Blo 1068616 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B4060165 : Blo 1068616 4060165 := bbase (se 4 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 4060165 = 761281) (by norm_num)
theorem B10417205 : Blo 1068616 10417205 := bbase (se 5 (by rfl) ⟨488306, by rfl⟩ : syracuseStep 10417205 = 976613) (by norm_num)
theorem B2290781 : Blo 1068616 2290781 := bbase (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) (by norm_num)
theorem B1144049 : Blo 1068616 1144049 := bbase (se 2 (by rfl) ⟨429018, by rfl⟩ : syracuseStep 1144049 = 858037) (by norm_num)
theorem B4060469 : Blo 1068616 4060469 := bbase (se 5 (by rfl) ⟨190334, by rfl⟩ : syracuseStep 4060469 = 380669) (by norm_num)
theorem B6092117 : Blo 1068616 6092117 := bbase (se 13 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 6092117 = 2231) (by norm_num)
theorem B1930597 : Blo 1068616 1930597 := bbase (se 4 (by rfl) ⟨180993, by rfl⟩ : syracuseStep 1930597 = 361987) (by norm_num)
theorem B1602941 : Blo 1068616 1602941 := bbase (se 3 (by rfl) ⟨300551, by rfl⟩ : syracuseStep 1602941 = 601103) (by norm_num)
theorem B1602965 : Blo 1068616 1602965 := bbase (se 6 (by rfl) ⟨37569, by rfl⟩ : syracuseStep 1602965 = 75139) (by norm_num)
theorem B1602989 : Blo 1068616 1602989 := bbase (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) (by norm_num)
theorem B2028989 : Blo 1068616 2028989 := bbase (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) (by norm_num)
theorem B1603013 : Blo 1068616 1603013 := bbase (se 4 (by rfl) ⟨150282, by rfl⟩ : syracuseStep 1603013 = 300565) (by norm_num)
theorem B1603037 : Blo 1068616 1603037 := bbase (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) (by norm_num)
theorem B1144297 : Blo 1068616 1144297 := bbase (se 2 (by rfl) ⟨429111, by rfl⟩ : syracuseStep 1144297 = 858223) (by norm_num)
theorem B1603061 : Blo 1068616 1603061 := bbase (se 5 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 1603061 = 150287) (by norm_num)
theorem B1603085 : Blo 1068616 1603085 := bbase (se 3 (by rfl) ⟨300578, by rfl⟩ : syracuseStep 1603085 = 601157) (by norm_num)
theorem B1603109 : Blo 1068616 1603109 := bbase (se 4 (by rfl) ⟨150291, by rfl⟩ : syracuseStep 1603109 = 300583) (by norm_num)
theorem B1603133 : Blo 1068616 1603133 := bbase (se 3 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 1603133 = 601175) (by norm_num)
theorem B1603157 : Blo 1068616 1603157 := bbase (se 8 (by rfl) ⟨9393, by rfl⟩ : syracuseStep 1603157 = 18787) (by norm_num)
theorem B2029141 : Blo 1068616 2029141 := bbase (se 8 (by rfl) ⟨11889, by rfl⟩ : syracuseStep 2029141 = 23779) (by norm_num)
theorem B3044965 : Blo 1068616 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B1603181 : Blo 1068616 1603181 := bbase (se 3 (by rfl) ⟨300596, by rfl⟩ : syracuseStep 1603181 = 601193) (by norm_num)
theorem B1603205 : Blo 1068616 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B1603229 : Blo 1068616 1603229 := bbase (se 3 (by rfl) ⟨300605, by rfl⟩ : syracuseStep 1603229 = 601211) (by norm_num)
theorem B1603253 : Blo 1068616 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B1603277 : Blo 1068616 1603277 := bbase (se 3 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 1603277 = 601229) (by norm_num)
theorem B1373917 : Blo 1068616 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B1603301 : Blo 1068616 1603301 := bbase (se 4 (by rfl) ⟨150309, by rfl⟩ : syracuseStep 1603301 = 300619) (by norm_num)
theorem B3471077 : Blo 1068616 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B1603325 : Blo 1068616 1603325 := bbase (se 3 (by rfl) ⟨300623, by rfl⟩ : syracuseStep 1603325 = 601247) (by norm_num)
theorem B1603349 : Blo 1068616 1603349 := bbase (se 6 (by rfl) ⟨37578, by rfl⟩ : syracuseStep 1603349 = 75157) (by norm_num)
theorem B1603373 : Blo 1068616 1603373 := bbase (se 3 (by rfl) ⟨300632, by rfl⟩ : syracuseStep 1603373 = 601265) (by norm_num)
theorem B1603397 : Blo 1068616 1603397 := bbase (se 4 (by rfl) ⟨150318, by rfl⟩ : syracuseStep 1603397 = 300637) (by norm_num)
theorem B1603421 : Blo 1068616 1603421 := bbase (se 3 (by rfl) ⟨300641, by rfl⟩ : syracuseStep 1603421 = 601283) (by norm_num)
theorem B1603445 : Blo 1068616 1603445 := bbase (se 5 (by rfl) ⟨75161, by rfl⟩ : syracuseStep 1603445 = 150323) (by norm_num)
theorem B2029445 : Blo 1068616 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1603469 : Blo 1068616 1603469 := bbase (se 3 (by rfl) ⟨300650, by rfl⟩ : syracuseStep 1603469 = 601301) (by norm_num)
theorem B1603493 : Blo 1068616 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B1144741 : Blo 1068616 1144741 := bbase (se 4 (by rfl) ⟨107319, by rfl⟩ : syracuseStep 1144741 = 214639) (by norm_num)
theorem B1603517 : Blo 1068616 1603517 := bbase (se 3 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 1603517 = 601319) (by norm_num)
theorem B1603541 : Blo 1068616 1603541 := bbase (se 7 (by rfl) ⟨18791, by rfl⟩ : syracuseStep 1603541 = 37583) (by norm_num)
theorem B1144801 : Blo 1068616 1144801 := bbase (se 2 (by rfl) ⟨429300, by rfl⟩ : syracuseStep 1144801 = 858601) (by norm_num)
theorem B1603565 : Blo 1068616 1603565 := bbase (se 3 (by rfl) ⟨300668, by rfl⟩ : syracuseStep 1603565 = 601337) (by norm_num)
theorem B1603589 : Blo 1068616 1603589 := bbase (se 4 (by rfl) ⟨150336, by rfl⟩ : syracuseStep 1603589 = 300673) (by norm_num)
theorem B1603613 : Blo 1068616 1603613 := bbase (se 3 (by rfl) ⟨300677, by rfl⟩ : syracuseStep 1603613 = 601355) (by norm_num)
theorem B1603637 : Blo 1068616 1603637 := bbase (se 5 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 1603637 = 150341) (by norm_num)
theorem B1603661 : Blo 1068616 1603661 := bbase (se 3 (by rfl) ⟨300686, by rfl⟩ : syracuseStep 1603661 = 601373) (by norm_num)
theorem B1603685 : Blo 1068616 1603685 := bbase (se 4 (by rfl) ⟨150345, by rfl⟩ : syracuseStep 1603685 = 300691) (by norm_num)
theorem B5142629 : Blo 1068616 5142629 := bbase (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) (by norm_num)
theorem B1603709 : Blo 1068616 1603709 := bbase (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) (by norm_num)
theorem B2062477 : Blo 1068616 2062477 := bbase (se 3 (by rfl) ⟨386714, by rfl⟩ : syracuseStep 2062477 = 773429) (by norm_num)
theorem B1603733 : Blo 1068616 1603733 := bbase (se 6 (by rfl) ⟨37587, by rfl⟩ : syracuseStep 1603733 = 75175) (by norm_num)
theorem B1603757 : Blo 1068616 1603757 := bbase (se 3 (by rfl) ⟨300704, by rfl⟩ : syracuseStep 1603757 = 601409) (by norm_num)
theorem B1603781 : Blo 1068616 1603781 := bbase (se 4 (by rfl) ⟨150354, by rfl⟩ : syracuseStep 1603781 = 300709) (by norm_num)
theorem B1603805 : Blo 1068616 1603805 := bbase (se 3 (by rfl) ⟨300713, by rfl⟩ : syracuseStep 1603805 = 601427) (by norm_num)
theorem B1603829 : Blo 1068616 1603829 := bbase (se 5 (by rfl) ⟨75179, by rfl⟩ : syracuseStep 1603829 = 150359) (by norm_num)
theorem B1603853 : Blo 1068616 1603853 := bbase (se 3 (by rfl) ⟨300722, by rfl⟩ : syracuseStep 1603853 = 601445) (by norm_num)
theorem B1145117 : Blo 1068616 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B1603877 : Blo 1068616 1603877 := bbase (se 4 (by rfl) ⟨150363, by rfl⟩ : syracuseStep 1603877 = 300727) (by norm_num)
theorem B1603901 : Blo 1068616 1603901 := bbase (se 3 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 1603901 = 601463) (by norm_num)
theorem B1833293 : Blo 1068616 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B1603925 : Blo 1068616 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1603949 : Blo 1068616 1603949 := bbase (se 3 (by rfl) ⟨300740, by rfl⟩ : syracuseStep 1603949 = 601481) (by norm_num)
theorem B1603973 : Blo 1068616 1603973 := bbase (se 4 (by rfl) ⟨150372, by rfl⟩ : syracuseStep 1603973 = 300745) (by norm_num)
theorem B1603997 : Blo 1068616 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B1604021 : Blo 1068616 1604021 := bbase (se 5 (by rfl) ⟨75188, by rfl⟩ : syracuseStep 1604021 = 150377) (by norm_num)
theorem B1604045 : Blo 1068616 1604045 := bbase (se 3 (by rfl) ⟨300758, by rfl⟩ : syracuseStep 1604045 = 601517) (by norm_num)
theorem B1604069 : Blo 1068616 1604069 := bbase (se 4 (by rfl) ⟨150381, by rfl⟩ : syracuseStep 1604069 = 300763) (by norm_num)
theorem B1604093 : Blo 1068616 1604093 := bbase (se 3 (by rfl) ⟨300767, by rfl⟩ : syracuseStep 1604093 = 601535) (by norm_num)
theorem B1604117 : Blo 1068616 1604117 := bbase (se 6 (by rfl) ⟨37596, by rfl⟩ : syracuseStep 1604117 = 75193) (by norm_num)
theorem B1604141 : Blo 1068616 1604141 := bbase (se 3 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 1604141 = 601553) (by norm_num)
theorem B1604165 : Blo 1068616 1604165 := bbase (se 4 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 1604165 = 300781) (by norm_num)
theorem B1604189 : Blo 1068616 1604189 := bbase (se 3 (by rfl) ⟨300785, by rfl⟩ : syracuseStep 1604189 = 601571) (by norm_num)
theorem B2030197 : Blo 1068616 2030197 := bbase (se 5 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 2030197 = 190331) (by norm_num)
theorem B1604213 : Blo 1068616 1604213 := bbase (se 5 (by rfl) ⟨75197, by rfl⟩ : syracuseStep 1604213 = 150395) (by norm_num)
theorem B1604237 : Blo 1068616 1604237 := bbase (se 3 (by rfl) ⟨300794, by rfl⟩ : syracuseStep 1604237 = 601589) (by norm_num)
theorem B1604261 : Blo 1068616 1604261 := bbase (se 4 (by rfl) ⟨150399, by rfl⟩ : syracuseStep 1604261 = 300799) (by norm_num)
theorem B1604285 : Blo 1068616 1604285 := bbase (se 3 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 1604285 = 601607) (by norm_num)
theorem B1604309 : Blo 1068616 1604309 := bbase (se 7 (by rfl) ⟨18800, by rfl⟩ : syracuseStep 1604309 = 37601) (by norm_num)
theorem B1932005 : Blo 1068616 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B1604333 : Blo 1068616 1604333 := bbase (se 3 (by rfl) ⟨300812, by rfl⟩ : syracuseStep 1604333 = 601625) (by norm_num)
theorem B2030341 : Blo 1068616 2030341 := bbase (se 4 (by rfl) ⟨190344, by rfl⟩ : syracuseStep 2030341 = 380689) (by norm_num)
theorem B1604357 : Blo 1068616 1604357 := bbase (se 4 (by rfl) ⟨150408, by rfl⟩ : syracuseStep 1604357 = 300817) (by norm_num)
theorem B5143301 : Blo 1068616 5143301 := bbase (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) (by norm_num)
theorem B1604381 : Blo 1068616 1604381 := bbase (se 3 (by rfl) ⟨300821, by rfl⟩ : syracuseStep 1604381 = 601643) (by norm_num)
theorem B1932061 : Blo 1068616 1932061 := bbase (se 3 (by rfl) ⟨362261, by rfl⟩ : syracuseStep 1932061 = 724523) (by norm_num)
theorem B1604405 : Blo 1068616 1604405 := bbase (se 5 (by rfl) ⟨75206, by rfl⟩ : syracuseStep 1604405 = 150413) (by norm_num)
theorem B1604429 : Blo 1068616 1604429 := bbase (se 3 (by rfl) ⟨300830, by rfl⟩ : syracuseStep 1604429 = 601661) (by norm_num)
theorem B1604453 : Blo 1068616 1604453 := bbase (se 4 (by rfl) ⟨150417, by rfl⟩ : syracuseStep 1604453 = 300835) (by norm_num)
theorem B1604477 : Blo 1068616 1604477 := bbase (se 3 (by rfl) ⟨300839, by rfl⟩ : syracuseStep 1604477 = 601679) (by norm_num)
theorem B1604501 : Blo 1068616 1604501 := bbase (se 6 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 1604501 = 75211) (by norm_num)
theorem B1375133 : Blo 1068616 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B2030501 : Blo 1068616 2030501 := bbase (se 4 (by rfl) ⟨190359, by rfl⟩ : syracuseStep 2030501 = 380719) (by norm_num)
theorem B1604525 : Blo 1068616 1604525 := bbase (se 3 (by rfl) ⟨300848, by rfl⟩ : syracuseStep 1604525 = 601697) (by norm_num)
theorem B1604549 : Blo 1068616 1604549 := bbase (se 4 (by rfl) ⟨150426, by rfl⟩ : syracuseStep 1604549 = 300853) (by norm_num)
theorem B1604573 : Blo 1068616 1604573 := bbase (se 3 (by rfl) ⟨300857, by rfl⟩ : syracuseStep 1604573 = 601715) (by norm_num)
theorem B1604597 : Blo 1068616 1604597 := bbase (se 5 (by rfl) ⟨75215, by rfl⟩ : syracuseStep 1604597 = 150431) (by norm_num)
theorem B1604621 : Blo 1068616 1604621 := bbase (se 3 (by rfl) ⟨300866, by rfl⟩ : syracuseStep 1604621 = 601733) (by norm_num)
theorem B1604645 : Blo 1068616 1604645 := bbase (se 4 (by rfl) ⟨150435, by rfl⟩ : syracuseStep 1604645 = 300871) (by norm_num)
theorem B2030645 : Blo 1068616 2030645 := bbase (se 5 (by rfl) ⟨95186, by rfl⟩ : syracuseStep 2030645 = 190373) (by norm_num)
theorem B1604669 : Blo 1068616 1604669 := bbase (se 3 (by rfl) ⟨300875, by rfl⟩ : syracuseStep 1604669 = 601751) (by norm_num)
theorem B1604693 : Blo 1068616 1604693 := bbase (se 8 (by rfl) ⟨9402, by rfl⟩ : syracuseStep 1604693 = 18805) (by norm_num)
theorem B1604717 : Blo 1068616 1604717 := bbase (se 3 (by rfl) ⟨300884, by rfl⟩ : syracuseStep 1604717 = 601769) (by norm_num)
theorem B11140213 : Blo 1068616 11140213 := bbase (se 5 (by rfl) ⟨522197, by rfl⟩ : syracuseStep 11140213 = 1044395) (by norm_num)
theorem B1604741 : Blo 1068616 1604741 := bbase (se 4 (by rfl) ⟨150444, by rfl⟩ : syracuseStep 1604741 = 300889) (by norm_num)
theorem B1604765 : Blo 1068616 1604765 := bbase (se 3 (by rfl) ⟨300893, by rfl⟩ : syracuseStep 1604765 = 601787) (by norm_num)
theorem B1604789 : Blo 1068616 1604789 := bbase (se 5 (by rfl) ⟨75224, by rfl⟩ : syracuseStep 1604789 = 150449) (by norm_num)
theorem B1604813 : Blo 1068616 1604813 := bbase (se 3 (by rfl) ⟨300902, by rfl⟩ : syracuseStep 1604813 = 601805) (by norm_num)
theorem B1604837 : Blo 1068616 1604837 := bbase (se 4 (by rfl) ⟨150453, by rfl⟩ : syracuseStep 1604837 = 300907) (by norm_num)
theorem B1604861 : Blo 1068616 1604861 := bbase (se 3 (by rfl) ⟨300911, by rfl⟩ : syracuseStep 1604861 = 601823) (by norm_num)
theorem B1604885 : Blo 1068616 1604885 := bbase (se 6 (by rfl) ⟨37614, by rfl⟩ : syracuseStep 1604885 = 75229) (by norm_num)
theorem B5209381 : Blo 1068616 5209381 := bbase (se 4 (by rfl) ⟨488379, by rfl⟩ : syracuseStep 5209381 = 976759) (by norm_num)
theorem B1604909 : Blo 1068616 1604909 := bbase (se 3 (by rfl) ⟨300920, by rfl⟩ : syracuseStep 1604909 = 601841) (by norm_num)
theorem B1604933 : Blo 1068616 1604933 := bbase (se 4 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 1604933 = 300925) (by norm_num)
theorem B2030933 : Blo 1068616 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B1604957 : Blo 1068616 1604957 := bbase (se 3 (by rfl) ⟨300929, by rfl⟩ : syracuseStep 1604957 = 601859) (by norm_num)
theorem B1736045 : Blo 1068616 1736045 := bbase (se 3 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 1736045 = 651017) (by norm_num)
theorem B4062581 : Blo 1068616 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B1604981 : Blo 1068616 1604981 := bbase (se 5 (by rfl) ⟨75233, by rfl⟩ : syracuseStep 1604981 = 150467) (by norm_num)
theorem B1605005 : Blo 1068616 1605005 := bbase (se 3 (by rfl) ⟨300938, by rfl⟩ : syracuseStep 1605005 = 601877) (by norm_num)
theorem B1605029 : Blo 1068616 1605029 := bbase (se 4 (by rfl) ⟨150471, by rfl⟩ : syracuseStep 1605029 = 300943) (by norm_num)
theorem B4881829 : Blo 1068616 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B1605053 : Blo 1068616 1605053 := bbase (se 3 (by rfl) ⟨300947, by rfl⟩ : syracuseStep 1605053 = 601895) (by norm_num)
theorem B1605077 : Blo 1068616 1605077 := bbase (se 7 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 1605077 = 37619) (by norm_num)
theorem B2031085 : Blo 1068616 2031085 := bbase (se 3 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 2031085 = 761657) (by norm_num)
theorem B1605101 : Blo 1068616 1605101 := bbase (se 3 (by rfl) ⟨300956, by rfl⟩ : syracuseStep 1605101 = 601913) (by norm_num)
theorem B1605125 : Blo 1068616 1605125 := bbase (se 4 (by rfl) ⟨150480, by rfl⟩ : syracuseStep 1605125 = 300961) (by norm_num)
theorem B1834517 : Blo 1068616 1834517 := bbase (se 6 (by rfl) ⟨42996, by rfl⟩ : syracuseStep 1834517 = 85993) (by norm_num)
theorem B1605149 : Blo 1068616 1605149 := bbase (se 3 (by rfl) ⟨300965, by rfl⟩ : syracuseStep 1605149 = 601931) (by norm_num)
theorem B1605173 : Blo 1068616 1605173 := bbase (se 5 (by rfl) ⟨75242, by rfl⟩ : syracuseStep 1605173 = 150485) (by norm_num)
theorem B1605197 : Blo 1068616 1605197 := bbase (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) (by norm_num)
theorem B1605221 : Blo 1068616 1605221 := bbase (se 4 (by rfl) ⟨150489, by rfl⟩ : syracuseStep 1605221 = 300979) (by norm_num)
theorem B1605245 : Blo 1068616 1605245 := bbase (se 3 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 1605245 = 601967) (by norm_num)
theorem B4062869 : Blo 1068616 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B1605269 : Blo 1068616 1605269 := bbase (se 6 (by rfl) ⟨37623, by rfl⟩ : syracuseStep 1605269 = 75247) (by norm_num)
theorem B1605293 : Blo 1068616 1605293 := bbase (se 3 (by rfl) ⟨300992, by rfl⟩ : syracuseStep 1605293 = 601985) (by norm_num)
theorem B1605317 : Blo 1068616 1605317 := bbase (se 4 (by rfl) ⟨150498, by rfl⟩ : syracuseStep 1605317 = 300997) (by norm_num)
theorem B1605341 : Blo 1068616 1605341 := bbase (se 3 (by rfl) ⟨301001, by rfl⟩ : syracuseStep 1605341 = 602003) (by norm_num)
theorem B1605365 : Blo 1068616 1605365 := bbase (se 5 (by rfl) ⟨75251, by rfl⟩ : syracuseStep 1605365 = 150503) (by norm_num)
theorem B1605389 : Blo 1068616 1605389 := bbase (se 3 (by rfl) ⟨301010, by rfl⟩ : syracuseStep 1605389 = 602021) (by norm_num)
theorem B2031389 : Blo 1068616 2031389 := bbase (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) (by norm_num)
theorem B1605413 : Blo 1068616 1605413 := bbase (se 4 (by rfl) ⟨150507, by rfl⟩ : syracuseStep 1605413 = 301015) (by norm_num)
theorem B1605437 : Blo 1068616 1605437 := bbase (se 3 (by rfl) ⟨301019, by rfl⟩ : syracuseStep 1605437 = 602039) (by norm_num)
theorem B1605461 : Blo 1068616 1605461 := bbase (se 9 (by rfl) ⟨4703, by rfl⟩ : syracuseStep 1605461 = 9407) (by norm_num)
theorem B1605485 : Blo 1068616 1605485 := bbase (se 3 (by rfl) ⟨301028, by rfl⟩ : syracuseStep 1605485 = 602057) (by norm_num)
theorem B1605509 : Blo 1068616 1605509 := bbase (se 4 (by rfl) ⟨150516, by rfl⟩ : syracuseStep 1605509 = 301033) (by norm_num)
theorem B1605533 : Blo 1068616 1605533 := bbase (se 3 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 1605533 = 602075) (by norm_num)
theorem B1605557 : Blo 1068616 1605557 := bbase (se 5 (by rfl) ⟨75260, by rfl⟩ : syracuseStep 1605557 = 150521) (by norm_num)
theorem B1605581 : Blo 1068616 1605581 := bbase (se 3 (by rfl) ⟨301046, by rfl⟩ : syracuseStep 1605581 = 602093) (by norm_num)
theorem B1605605 : Blo 1068616 1605605 := bbase (se 4 (by rfl) ⟨150525, by rfl⟩ : syracuseStep 1605605 = 301051) (by norm_num)
theorem B1605629 : Blo 1068616 1605629 := bbase (se 3 (by rfl) ⟨301055, by rfl⟩ : syracuseStep 1605629 = 602111) (by norm_num)
theorem B1605635 : Blo 1068616 1605635 := bstep (se 1 (by rfl) ⟨1204226, by rfl⟩ : syracuseStep 1605635 = 2408453) B2408453
theorem B1605665 : Blo 1068616 1605665 := bstep (se 2 (by rfl) ⟨602124, by rfl⟩ : syracuseStep 1605665 = 1204249) B1204249
theorem B1605683 : Blo 1068616 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B1605713 : Blo 1068616 1605713 := bstep (se 2 (by rfl) ⟨602142, by rfl⟩ : syracuseStep 1605713 = 1204285) B1204285
theorem B1605731 : Blo 1068616 1605731 := bstep (se 1 (by rfl) ⟨1204298, by rfl⟩ : syracuseStep 1605731 = 2408597) B2408597
theorem B1605761 : Blo 1068616 1605761 := bstep (se 2 (by rfl) ⟨602160, by rfl⟩ : syracuseStep 1605761 = 1204321) B1204321
theorem B1605779 : Blo 1068616 1605779 := bstep (se 1 (by rfl) ⟨1204334, by rfl⟩ : syracuseStep 1605779 = 2408669) B2408669
theorem B1605809 : Blo 1068616 1605809 := bstep (se 2 (by rfl) ⟨602178, by rfl⟩ : syracuseStep 1605809 = 1204357) B1204357
theorem B1605827 : Blo 1068616 1605827 := bstep (se 1 (by rfl) ⟨1204370, by rfl⟩ : syracuseStep 1605827 = 2408741) B2408741
theorem B1605857 : Blo 1068616 1605857 := bstep (se 2 (by rfl) ⟨602196, by rfl⟩ : syracuseStep 1605857 = 1204393) B1204393
theorem B3047665 : Blo 1068616 3047665 := bstep (se 2 (by rfl) ⟨1142874, by rfl⟩ : syracuseStep 3047665 = 2285749) B2285749
theorem B1605875 : Blo 1068616 1605875 := bstep (se 1 (by rfl) ⟨1204406, by rfl⟩ : syracuseStep 1605875 = 2408813) B2408813
theorem B2031875 : Blo 1068616 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B1605905 : Blo 1068616 1605905 := bstep (se 2 (by rfl) ⟨602214, by rfl⟩ : syracuseStep 1605905 = 1204429) B1204429
theorem B1605923 : Blo 1068616 1605923 := bstep (se 1 (by rfl) ⟨1204442, by rfl⟩ : syracuseStep 1605923 = 2408885) B2408885
theorem B1605953 : Blo 1068616 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B3473741 : Blo 1068616 3473741 := bstep (se 3 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 3473741 = 1302653) B1302653
theorem B1605971 : Blo 1068616 1605971 := bstep (se 1 (by rfl) ⟨1204478, by rfl⟩ : syracuseStep 1605971 = 2408957) B2408957
theorem B1606001 : Blo 1068616 1606001 := bstep (se 2 (by rfl) ⟨602250, by rfl⟩ : syracuseStep 1606001 = 1204501) B1204501
theorem B1606019 : Blo 1068616 1606019 := bstep (se 1 (by rfl) ⟨1204514, by rfl⟩ : syracuseStep 1606019 = 2409029) B2409029
theorem B1606049 : Blo 1068616 1606049 := bstep (se 2 (by rfl) ⟨602268, by rfl⟩ : syracuseStep 1606049 = 1204537) B1204537
theorem B1606067 : Blo 1068616 1606067 := bstep (se 1 (by rfl) ⟨1204550, by rfl⟩ : syracuseStep 1606067 = 2409101) B2409101
theorem B1606097 : Blo 1068616 1606097 := bstep (se 2 (by rfl) ⟨602286, by rfl⟩ : syracuseStep 1606097 = 1204573) B1204573
theorem B1606115 : Blo 1068616 1606115 := bstep (se 1 (by rfl) ⟨1204586, by rfl⟩ : syracuseStep 1606115 = 2409173) B2409173
theorem B1606145 : Blo 1068616 1606145 := bstep (se 2 (by rfl) ⟨602304, by rfl⟩ : syracuseStep 1606145 = 1204609) B1204609
theorem B3047939 : Blo 1068616 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B1606163 : Blo 1068616 1606163 := bstep (se 1 (by rfl) ⟨1204622, by rfl⟩ : syracuseStep 1606163 = 2409245) B2409245
theorem B1606193 : Blo 1068616 1606193 := bstep (se 2 (by rfl) ⟨602322, by rfl⟩ : syracuseStep 1606193 = 1204645) B1204645
theorem B1606211 : Blo 1068616 1606211 := bstep (se 1 (by rfl) ⟨1204658, by rfl⟩ : syracuseStep 1606211 = 2409317) B2409317
theorem B1606241 : Blo 1068616 1606241 := bstep (se 2 (by rfl) ⟨602340, by rfl⟩ : syracuseStep 1606241 = 1204681) B1204681
theorem B1606259 : Blo 1068616 1606259 := bstep (se 1 (by rfl) ⟨1204694, by rfl⟩ : syracuseStep 1606259 = 2409389) B2409389
theorem B1606289 : Blo 1068616 1606289 := bstep (se 2 (by rfl) ⟨602358, by rfl⟩ : syracuseStep 1606289 = 1204717) B1204717
theorem B1606307 : Blo 1068616 1606307 := bstep (se 1 (by rfl) ⟨1204730, by rfl⟩ : syracuseStep 1606307 = 2409461) B2409461
theorem B1606337 : Blo 1068616 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B3048131 : Blo 1068616 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B1606355 : Blo 1068616 1606355 := bstep (se 1 (by rfl) ⟨1204766, by rfl⟩ : syracuseStep 1606355 = 2409533) B2409533
theorem B1606385 : Blo 1068616 1606385 := bstep (se 2 (by rfl) ⟨602394, by rfl⟩ : syracuseStep 1606385 = 1204789) B1204789
theorem B1606403 : Blo 1068616 1606403 := bstep (se 1 (by rfl) ⟨1204802, by rfl⟩ : syracuseStep 1606403 = 2409605) B2409605
theorem B1606433 : Blo 1068616 1606433 := bstep (se 2 (by rfl) ⟨602412, by rfl⟩ : syracuseStep 1606433 = 1204825) B1204825
theorem B1606451 : Blo 1068616 1606451 := bstep (se 1 (by rfl) ⟨1204838, by rfl⟩ : syracuseStep 1606451 = 2409677) B2409677
theorem B1606481 : Blo 1068616 1606481 := bstep (se 2 (by rfl) ⟨602430, by rfl⟩ : syracuseStep 1606481 = 1204861) B1204861
theorem B1606499 : Blo 1068616 1606499 := bstep (se 1 (by rfl) ⟨1204874, by rfl⟩ : syracuseStep 1606499 = 2409749) B2409749
theorem B1606529 : Blo 1068616 1606529 := bstep (se 2 (by rfl) ⟨602448, by rfl⟩ : syracuseStep 1606529 = 1204897) B1204897
theorem B1606547 : Blo 1068616 1606547 := bstep (se 1 (by rfl) ⟨1204910, by rfl⟩ : syracuseStep 1606547 = 2409821) B2409821
theorem B1606577 : Blo 1068616 1606577 := bstep (se 2 (by rfl) ⟨602466, by rfl⟩ : syracuseStep 1606577 = 1204933) B1204933
theorem B1606595 : Blo 1068616 1606595 := bstep (se 1 (by rfl) ⟨1204946, by rfl⟩ : syracuseStep 1606595 = 2409893) B2409893
theorem B1606625 : Blo 1068616 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B1606643 : Blo 1068616 1606643 := bstep (se 1 (by rfl) ⟨1204982, by rfl⟩ : syracuseStep 1606643 = 2409965) B2409965
theorem B1606673 : Blo 1068616 1606673 := bstep (se 2 (by rfl) ⟨602502, by rfl⟩ : syracuseStep 1606673 = 1205005) B1205005
theorem B1606691 : Blo 1068616 1606691 := bstep (se 1 (by rfl) ⟨1205018, by rfl⟩ : syracuseStep 1606691 = 2410037) B2410037
theorem B1606721 : Blo 1068616 1606721 := bstep (se 2 (by rfl) ⟨602520, by rfl⟩ : syracuseStep 1606721 = 1205041) B1205041
theorem B1606739 : Blo 1068616 1606739 := bstep (se 1 (by rfl) ⟨1205054, by rfl⟩ : syracuseStep 1606739 = 2410109) B2410109
theorem B1803377 : Blo 1068616 1803377 := bstep (se 2 (by rfl) ⟨676266, by rfl⟩ : syracuseStep 1803377 = 1352533) B1352533
theorem B1606769 : Blo 1068616 1606769 := bstep (se 2 (by rfl) ⟨602538, by rfl⟩ : syracuseStep 1606769 = 1205077) B1205077
theorem B2032771 : Blo 1068616 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B1606787 : Blo 1068616 1606787 := bstep (se 1 (by rfl) ⟨1205090, by rfl⟩ : syracuseStep 1606787 = 2410181) B2410181
theorem B1606817 : Blo 1068616 1606817 := bstep (se 2 (by rfl) ⟨602556, by rfl⟩ : syracuseStep 1606817 = 1205113) B1205113
theorem B1606835 : Blo 1068616 1606835 := bstep (se 1 (by rfl) ⟨1205126, by rfl⟩ : syracuseStep 1606835 = 2410253) B2410253
theorem B1606865 : Blo 1068616 1606865 := bstep (se 2 (by rfl) ⟨602574, by rfl⟩ : syracuseStep 1606865 = 1205149) B1205149
theorem B1606883 : Blo 1068616 1606883 := bstep (se 1 (by rfl) ⟨1205162, by rfl⟩ : syracuseStep 1606883 = 2410325) B2410325
theorem B1803505 : Blo 1068616 1803505 := bstep (se 2 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 1803505 = 1352629) B1352629
theorem B1606913 : Blo 1068616 1606913 := bstep (se 2 (by rfl) ⟨602592, by rfl⟩ : syracuseStep 1606913 = 1205185) B1205185
theorem B4064525 : Blo 1068616 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B1803539 : Blo 1068616 1803539 := bstep (se 1 (by rfl) ⟨1352654, by rfl⟩ : syracuseStep 1803539 = 2705309) B2705309
theorem B1606931 : Blo 1068616 1606931 := bstep (se 1 (by rfl) ⟨1205198, by rfl⟩ : syracuseStep 1606931 = 2410397) B2410397
theorem B2032931 : Blo 1068616 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B1606961 : Blo 1068616 1606961 := bstep (se 2 (by rfl) ⟨602610, by rfl⟩ : syracuseStep 1606961 = 1205221) B1205221
theorem B1606979 : Blo 1068616 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B1607009 : Blo 1068616 1607009 := bstep (se 2 (by rfl) ⟨602628, by rfl⟩ : syracuseStep 1607009 = 1205257) B1205257
theorem B1607027 : Blo 1068616 1607027 := bstep (se 1 (by rfl) ⟨1205270, by rfl⟩ : syracuseStep 1607027 = 2410541) B2410541
theorem B1607057 : Blo 1068616 1607057 := bstep (se 2 (by rfl) ⟨602646, by rfl⟩ : syracuseStep 1607057 = 1205293) B1205293
theorem B1803667 : Blo 1068616 1803667 := bstep (se 1 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 1803667 = 2705501) B2705501
theorem B1607075 : Blo 1068616 1607075 := bstep (se 1 (by rfl) ⟨1205306, by rfl⟩ : syracuseStep 1607075 = 2410613) B2410613
theorem B1607105 : Blo 1068616 1607105 := bstep (se 2 (by rfl) ⟨602664, by rfl⟩ : syracuseStep 1607105 = 1205329) B1205329
theorem B1607123 : Blo 1068616 1607123 := bstep (se 1 (by rfl) ⟨1205342, by rfl⟩ : syracuseStep 1607123 = 2410685) B2410685
theorem B3048941 : Blo 1068616 3048941 := bstep (se 3 (by rfl) ⟨571676, by rfl⟩ : syracuseStep 3048941 = 1143353) B1143353
theorem B1607153 : Blo 1068616 1607153 := bstep (se 2 (by rfl) ⟨602682, by rfl⟩ : syracuseStep 1607153 = 1205365) B1205365
theorem B1607171 : Blo 1068616 1607171 := bstep (se 1 (by rfl) ⟨1205378, by rfl⟩ : syracuseStep 1607171 = 2410757) B2410757
theorem B1803809 : Blo 1068616 1803809 := bstep (se 2 (by rfl) ⟨676428, by rfl⟩ : syracuseStep 1803809 = 1352857) B1352857
theorem B1607201 : Blo 1068616 1607201 := bstep (se 2 (by rfl) ⟨602700, by rfl⟩ : syracuseStep 1607201 = 1205401) B1205401
theorem B1607219 : Blo 1068616 1607219 := bstep (se 1 (by rfl) ⟨1205414, by rfl⟩ : syracuseStep 1607219 = 2410829) B2410829
theorem B1607249 : Blo 1068616 1607249 := bstep (se 2 (by rfl) ⟨602718, by rfl⟩ : syracuseStep 1607249 = 1205437) B1205437
theorem B1607267 : Blo 1068616 1607267 := bstep (se 1 (by rfl) ⟨1205450, by rfl⟩ : syracuseStep 1607267 = 2410901) B2410901
theorem B1607297 : Blo 1068616 1607297 := bstep (se 2 (by rfl) ⟨602736, by rfl⟩ : syracuseStep 1607297 = 1205473) B1205473
theorem B1607315 : Blo 1068616 1607315 := bstep (se 1 (by rfl) ⟨1205486, by rfl⟩ : syracuseStep 1607315 = 2410973) B2410973
theorem B1803937 : Blo 1068616 1803937 := bstep (se 2 (by rfl) ⟨676476, by rfl⟩ : syracuseStep 1803937 = 1352953) B1352953
theorem B3049123 : Blo 1068616 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B1607345 : Blo 1068616 1607345 := bstep (se 2 (by rfl) ⟨602754, by rfl⟩ : syracuseStep 1607345 = 1205509) B1205509
theorem B1803971 : Blo 1068616 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B1607363 : Blo 1068616 1607363 := bstep (se 1 (by rfl) ⟨1205522, by rfl⟩ : syracuseStep 1607363 = 2411045) B2411045
theorem B1607393 : Blo 1068616 1607393 := bstep (se 2 (by rfl) ⟨602772, by rfl⟩ : syracuseStep 1607393 = 1205545) B1205545
theorem B1607411 : Blo 1068616 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B6686477 : Blo 1068616 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B1607441 : Blo 1068616 1607441 := bstep (se 2 (by rfl) ⟨602790, by rfl⟩ : syracuseStep 1607441 = 1205581) B1205581
theorem B1607459 : Blo 1068616 1607459 := bstep (se 1 (by rfl) ⟨1205594, by rfl⟩ : syracuseStep 1607459 = 2411189) B2411189
theorem B1607489 : Blo 1068616 1607489 := bstep (se 2 (by rfl) ⟨602808, by rfl⟩ : syracuseStep 1607489 = 1205617) B1205617
theorem B1804099 : Blo 1068616 1804099 := bstep (se 1 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 1804099 = 2706149) B2706149
theorem B1607507 : Blo 1068616 1607507 := bstep (se 1 (by rfl) ⟨1205630, by rfl⟩ : syracuseStep 1607507 = 2411261) B2411261
theorem B6850403 : Blo 1068616 6850403 := bstep (se 1 (by rfl) ⟨5137802, by rfl⟩ : syracuseStep 6850403 = 10275605) B10275605
theorem B1607537 : Blo 1068616 1607537 := bstep (se 2 (by rfl) ⟨602826, by rfl⟩ : syracuseStep 1607537 = 1205653) B1205653
theorem B1607555 : Blo 1068616 1607555 := bstep (se 1 (by rfl) ⟨1205666, by rfl⟩ : syracuseStep 1607555 = 2411333) B2411333
theorem B1607585 : Blo 1068616 1607585 := bstep (se 2 (by rfl) ⟨602844, by rfl⟩ : syracuseStep 1607585 = 1205689) B1205689
theorem B1607603 : Blo 1068616 1607603 := bstep (se 1 (by rfl) ⟨1205702, by rfl⟩ : syracuseStep 1607603 = 2411405) B2411405
theorem B1804241 : Blo 1068616 1804241 := bstep (se 2 (by rfl) ⟨676590, by rfl⟩ : syracuseStep 1804241 = 1353181) B1353181
theorem B1607633 : Blo 1068616 1607633 := bstep (se 2 (by rfl) ⟨602862, by rfl⟩ : syracuseStep 1607633 = 1205725) B1205725
theorem B1607651 : Blo 1068616 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B1607681 : Blo 1068616 1607681 := bstep (se 2 (by rfl) ⟨602880, by rfl⟩ : syracuseStep 1607681 = 1205761) B1205761
theorem B1607699 : Blo 1068616 1607699 := bstep (se 1 (by rfl) ⟨1205774, by rfl⟩ : syracuseStep 1607699 = 2411549) B2411549
theorem B4065329 : Blo 1068616 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B1607729 : Blo 1068616 1607729 := bstep (se 2 (by rfl) ⟨602898, by rfl⟩ : syracuseStep 1607729 = 1205797) B1205797
theorem B23169077 : Blo 1068616 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B1607747 : Blo 1068616 1607747 := bstep (se 1 (by rfl) ⟨1205810, by rfl⟩ : syracuseStep 1607747 = 2411621) B2411621
theorem B3606605 : Blo 1068616 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B1804369 : Blo 1068616 1804369 := bstep (se 2 (by rfl) ⟨676638, by rfl⟩ : syracuseStep 1804369 = 1353277) B1353277
theorem B1607777 : Blo 1068616 1607777 := bstep (se 2 (by rfl) ⟨602916, by rfl⟩ : syracuseStep 1607777 = 1205833) B1205833
theorem B1804403 : Blo 1068616 1804403 := bstep (se 1 (by rfl) ⟨1353302, by rfl⟩ : syracuseStep 1804403 = 2706605) B2706605
theorem B1607795 : Blo 1068616 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B3606659 : Blo 1068616 3606659 := bstep (se 1 (by rfl) ⟨2704994, by rfl⟩ : syracuseStep 3606659 = 5409989) B5409989
theorem B3049613 : Blo 1068616 3049613 := bstep (se 3 (by rfl) ⟨571802, by rfl⟩ : syracuseStep 3049613 = 1143605) B1143605
theorem B1607825 : Blo 1068616 1607825 := bstep (se 2 (by rfl) ⟨602934, by rfl⟩ : syracuseStep 1607825 = 1205869) B1205869
theorem B1607843 : Blo 1068616 1607843 := bstep (se 1 (by rfl) ⟨1205882, by rfl⟩ : syracuseStep 1607843 = 2411765) B2411765
theorem B1607873 : Blo 1068616 1607873 := bstep (se 2 (by rfl) ⟨602952, by rfl⟩ : syracuseStep 1607873 = 1205905) B1205905
theorem B1607891 : Blo 1068616 1607891 := bstep (se 1 (by rfl) ⟨1205918, by rfl⟩ : syracuseStep 1607891 = 2411837) B2411837
theorem B1607921 : Blo 1068616 1607921 := bstep (se 2 (by rfl) ⟨602970, by rfl⟩ : syracuseStep 1607921 = 1205941) B1205941
theorem B1804531 : Blo 1068616 1804531 := bstep (se 1 (by rfl) ⟨1353398, by rfl⟩ : syracuseStep 1804531 = 2706797) B2706797
theorem B1607939 : Blo 1068616 1607939 := bstep (se 1 (by rfl) ⟨1205954, by rfl⟩ : syracuseStep 1607939 = 2411909) B2411909
theorem B1607969 : Blo 1068616 1607969 := bstep (se 2 (by rfl) ⟨602988, by rfl⟩ : syracuseStep 1607969 = 1205977) B1205977
theorem B1607987 : Blo 1068616 1607987 := bstep (se 1 (by rfl) ⟨1205990, by rfl⟩ : syracuseStep 1607987 = 2411981) B2411981
theorem B2034001 : Blo 1068616 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B1608017 : Blo 1068616 1608017 := bstep (se 2 (by rfl) ⟨603006, by rfl⟩ : syracuseStep 1608017 = 1206013) B1206013
theorem B1608035 : Blo 1068616 1608035 := bstep (se 1 (by rfl) ⟨1206026, by rfl⟩ : syracuseStep 1608035 = 2412053) B2412053
theorem B6097265 : Blo 1068616 6097265 := bstep (se 2 (by rfl) ⟨2286474, by rfl⟩ : syracuseStep 6097265 = 4572949) B4572949
theorem B1804673 : Blo 1068616 1804673 := bstep (se 2 (by rfl) ⟨676752, by rfl⟩ : syracuseStep 1804673 = 1353505) B1353505
theorem B1608065 : Blo 1068616 1608065 := bstep (se 2 (by rfl) ⟨603024, by rfl⟩ : syracuseStep 1608065 = 1206049) B1206049
theorem B3606929 : Blo 1068616 3606929 := bstep (se 2 (by rfl) ⟨1352598, by rfl⟩ : syracuseStep 3606929 = 2705197) B2705197
theorem B1608083 : Blo 1068616 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B1608113 : Blo 1068616 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B1608131 : Blo 1068616 1608131 := bstep (se 1 (by rfl) ⟨1206098, by rfl⟩ : syracuseStep 1608131 = 2412197) B2412197
theorem B1608161 : Blo 1068616 1608161 := bstep (se 2 (by rfl) ⟨603060, by rfl⟩ : syracuseStep 1608161 = 1206121) B1206121
theorem B1608179 : Blo 1068616 1608179 := bstep (se 1 (by rfl) ⟨1206134, by rfl⟩ : syracuseStep 1608179 = 2412269) B2412269
theorem B1804801 : Blo 1068616 1804801 := bstep (se 2 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 1804801 = 1353601) B1353601
theorem B1608209 : Blo 1068616 1608209 := bstep (se 2 (by rfl) ⟨603078, by rfl⟩ : syracuseStep 1608209 = 1206157) B1206157
theorem B1804835 : Blo 1068616 1804835 := bstep (se 1 (by rfl) ⟨1353626, by rfl⟩ : syracuseStep 1804835 = 2707253) B2707253
theorem B1608227 : Blo 1068616 1608227 := bstep (se 1 (by rfl) ⟨1206170, by rfl⟩ : syracuseStep 1608227 = 2412341) B2412341
theorem B1608257 : Blo 1068616 1608257 := bstep (se 2 (by rfl) ⟨603096, by rfl⟩ : syracuseStep 1608257 = 1206193) B1206193
theorem B1608275 : Blo 1068616 1608275 := bstep (se 1 (by rfl) ⟨1206206, by rfl⟩ : syracuseStep 1608275 = 2412413) B2412413
theorem B1608305 : Blo 1068616 1608305 := bstep (se 2 (by rfl) ⟨603114, by rfl⟩ : syracuseStep 1608305 = 1206229) B1206229
theorem B1608323 : Blo 1068616 1608323 := bstep (se 1 (by rfl) ⟨1206242, by rfl⟩ : syracuseStep 1608323 = 2412485) B2412485
theorem B1608353 : Blo 1068616 1608353 := bstep (se 2 (by rfl) ⟨603132, by rfl⟩ : syracuseStep 1608353 = 1206265) B1206265
theorem B1804963 : Blo 1068616 1804963 := bstep (se 1 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 1804963 = 2707445) B2707445
theorem B1608371 : Blo 1068616 1608371 := bstep (se 1 (by rfl) ⟨1206278, by rfl⟩ : syracuseStep 1608371 = 2412557) B2412557
theorem B4065997 : Blo 1068616 4065997 := bstep (se 3 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 4065997 = 1524749) B1524749
theorem B1608401 : Blo 1068616 1608401 := bstep (se 2 (by rfl) ⟨603150, by rfl⟩ : syracuseStep 1608401 = 1206301) B1206301
theorem B1608419 : Blo 1068616 1608419 := bstep (se 1 (by rfl) ⟨1206314, by rfl⟩ : syracuseStep 1608419 = 2412629) B2412629
theorem B1608449 : Blo 1068616 1608449 := bstep (se 2 (by rfl) ⟨603168, by rfl⟩ : syracuseStep 1608449 = 1206337) B1206337
theorem B1608467 : Blo 1068616 1608467 := bstep (se 1 (by rfl) ⟨1206350, by rfl⟩ : syracuseStep 1608467 = 2412701) B2412701
theorem B1805105 : Blo 1068616 1805105 := bstep (se 2 (by rfl) ⟨676914, by rfl⟩ : syracuseStep 1805105 = 1353829) B1353829
theorem B1608497 : Blo 1068616 1608497 := bstep (se 2 (by rfl) ⟨603186, by rfl⟩ : syracuseStep 1608497 = 1206373) B1206373
theorem B1608515 : Blo 1068616 1608515 := bstep (se 1 (by rfl) ⟨1206386, by rfl⟩ : syracuseStep 1608515 = 2412773) B2412773
theorem B9276229 : Blo 1068616 9276229 := bstep (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) B1739293
theorem B1608545 : Blo 1068616 1608545 := bstep (se 2 (by rfl) ⟨603204, by rfl⟩ : syracuseStep 1608545 = 1206409) B1206409
theorem B1608563 : Blo 1068616 1608563 := bstep (se 1 (by rfl) ⟨1206422, by rfl⟩ : syracuseStep 1608563 = 2412845) B2412845
theorem B1608593 : Blo 1068616 1608593 := bstep (se 2 (by rfl) ⟨603222, by rfl⟩ : syracuseStep 1608593 = 1206445) B1206445
theorem B1608611 : Blo 1068616 1608611 := bstep (se 1 (by rfl) ⟨1206458, by rfl⟩ : syracuseStep 1608611 = 2412917) B2412917
theorem B3607469 : Blo 1068616 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B1805233 : Blo 1068616 1805233 := bstep (se 2 (by rfl) ⟨676962, by rfl⟩ : syracuseStep 1805233 = 1353925) B1353925
theorem B1608641 : Blo 1068616 1608641 := bstep (se 2 (by rfl) ⟨603240, by rfl⟩ : syracuseStep 1608641 = 1206481) B1206481
theorem B1805267 : Blo 1068616 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B1608659 : Blo 1068616 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B3607523 : Blo 1068616 3607523 := bstep (se 1 (by rfl) ⟨2705642, by rfl⟩ : syracuseStep 3607523 = 5411285) B5411285
theorem B1608689 : Blo 1068616 1608689 := bstep (se 2 (by rfl) ⟨603258, by rfl⟩ : syracuseStep 1608689 = 1206517) B1206517
theorem B1608707 : Blo 1068616 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B1608737 : Blo 1068616 1608737 := bstep (se 2 (by rfl) ⟨603276, by rfl⟩ : syracuseStep 1608737 = 1206553) B1206553
theorem B1608755 : Blo 1068616 1608755 := bstep (se 1 (by rfl) ⟨1206566, by rfl⟩ : syracuseStep 1608755 = 2413133) B2413133
theorem B1608785 : Blo 1068616 1608785 := bstep (se 2 (by rfl) ⟨603294, by rfl⟩ : syracuseStep 1608785 = 1206589) B1206589
theorem B1805395 : Blo 1068616 1805395 := bstep (se 1 (by rfl) ⟨1354046, by rfl⟩ : syracuseStep 1805395 = 2708093) B2708093
theorem B1608803 : Blo 1068616 1608803 := bstep (se 1 (by rfl) ⟨1206602, by rfl⟩ : syracuseStep 1608803 = 2413205) B2413205
theorem B1608833 : Blo 1068616 1608833 := bstep (se 2 (by rfl) ⟨603312, by rfl⟩ : syracuseStep 1608833 = 1206625) B1206625
theorem B1608851 : Blo 1068616 1608851 := bstep (se 1 (by rfl) ⟨1206638, by rfl⟩ : syracuseStep 1608851 = 2413277) B2413277
theorem B1608881 : Blo 1068616 1608881 := bstep (se 2 (by rfl) ⟨603330, by rfl⟩ : syracuseStep 1608881 = 1206661) B1206661
theorem B1608899 : Blo 1068616 1608899 := bstep (se 1 (by rfl) ⟨1206674, by rfl⟩ : syracuseStep 1608899 = 2413349) B2413349
theorem B6851789 : Blo 1068616 6851789 := bstep (se 3 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 6851789 = 2569421) B2569421
theorem B1805537 : Blo 1068616 1805537 := bstep (se 2 (by rfl) ⟨677076, by rfl⟩ : syracuseStep 1805537 = 1354153) B1354153
theorem B3607793 : Blo 1068616 3607793 := bstep (se 2 (by rfl) ⟨1352922, by rfl⟩ : syracuseStep 3607793 = 2705845) B2705845
theorem B3050797 : Blo 1068616 3050797 := bstep (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) B1144049
theorem B1805665 : Blo 1068616 1805665 := bstep (se 2 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 1805665 = 1354249) B1354249
theorem B2035057 : Blo 1068616 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B1805699 : Blo 1068616 1805699 := bstep (se 1 (by rfl) ⟨1354274, by rfl⟩ : syracuseStep 1805699 = 2708549) B2708549
theorem B4066787 : Blo 1068616 4066787 := bstep (se 1 (by rfl) ⟨3050090, by rfl⟩ : syracuseStep 4066787 = 6100181) B6100181
theorem B1805827 : Blo 1068616 1805827 := bstep (se 1 (by rfl) ⟨1354370, by rfl⟩ : syracuseStep 1805827 = 2708741) B2708741
theorem B1805969 : Blo 1068616 1805969 := bstep (se 2 (by rfl) ⟨677238, by rfl⟩ : syracuseStep 1805969 = 1354477) B1354477
theorem B2035459 : Blo 1068616 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B3608333 : Blo 1068616 3608333 := bstep (se 3 (by rfl) ⟨676562, by rfl⟩ : syracuseStep 3608333 = 1353125) B1353125
theorem B1806097 : Blo 1068616 1806097 := bstep (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) B1354573
theorem B2166563 : Blo 1068616 2166563 := bstep (se 1 (by rfl) ⟨1624922, by rfl⟩ : syracuseStep 2166563 = 3249845) B3249845
theorem B6098723 : Blo 1068616 6098723 := bstep (se 1 (by rfl) ⟨4574042, by rfl⟩ : syracuseStep 6098723 = 9148085) B9148085
theorem B2035505 : Blo 1068616 2035505 := bstep (se 2 (by rfl) ⟨763314, by rfl⟩ : syracuseStep 2035505 = 1526629) B1526629
theorem B1806131 : Blo 1068616 1806131 := bstep (se 1 (by rfl) ⟨1354598, by rfl⟩ : syracuseStep 1806131 = 2709197) B2709197
theorem B3608387 : Blo 1068616 3608387 := bstep (se 1 (by rfl) ⟨2706290, by rfl⟩ : syracuseStep 3608387 = 5412581) B5412581
theorem B5410637 : Blo 1068616 5410637 := bstep (se 3 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 5410637 = 2028989) B2028989
theorem B1806259 : Blo 1068616 1806259 := bstep (se 1 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 1806259 = 2709389) B2709389
theorem B13733813 : Blo 1068616 13733813 := bstep (se 5 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 13733813 = 1287545) B1287545
theorem B5148643 : Blo 1068616 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B1544179 : Blo 1068616 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B1806401 : Blo 1068616 1806401 := bstep (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) B1354801
theorem B3608657 : Blo 1068616 3608657 := bstep (se 2 (by rfl) ⟨1353246, by rfl⟩ : syracuseStep 3608657 = 2706493) B2706493
theorem B2035793 : Blo 1068616 2035793 := bstep (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) B1526845
theorem B11571299 : Blo 1068616 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B4067441 : Blo 1068616 4067441 := bstep (se 2 (by rfl) ⟨1525290, by rfl⟩ : syracuseStep 4067441 = 3050581) B3050581
theorem B1806529 : Blo 1068616 1806529 := bstep (se 2 (by rfl) ⟨677448, by rfl⟩ : syracuseStep 1806529 = 1354897) B1354897
theorem B1806563 : Blo 1068616 1806563 := bstep (se 1 (by rfl) ⟨1354922, by rfl⟩ : syracuseStep 1806563 = 2709845) B2709845
theorem B3051857 : Blo 1068616 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B14094691 : Blo 1068616 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B1806691 : Blo 1068616 1806691 := bstep (se 1 (by rfl) ⟨1355018, by rfl⟩ : syracuseStep 1806691 = 2710037) B2710037
theorem B4886897 : Blo 1068616 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B13046129 : Blo 1068616 13046129 := bstep (se 2 (by rfl) ⟨4892298, by rfl⟩ : syracuseStep 13046129 = 9784597) B9784597
theorem B1806833 : Blo 1068616 1806833 := bstep (se 2 (by rfl) ⟨677562, by rfl⟩ : syracuseStep 1806833 = 1355125) B1355125
theorem B3609197 : Blo 1068616 3609197 := bstep (se 3 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 3609197 = 1353449) B1353449
theorem B1806961 : Blo 1068616 1806961 := bstep (se 2 (by rfl) ⟨677610, by rfl⟩ : syracuseStep 1806961 = 1355221) B1355221
theorem B1806995 : Blo 1068616 1806995 := bstep (se 1 (by rfl) ⟨1355246, by rfl⟩ : syracuseStep 1806995 = 2710493) B2710493
theorem B3609251 : Blo 1068616 3609251 := bstep (se 1 (by rfl) ⟨2706938, by rfl⟩ : syracuseStep 3609251 = 5413877) B5413877
theorem B6099725 : Blo 1068616 6099725 := bstep (se 3 (by rfl) ⟨1143698, by rfl⟩ : syracuseStep 6099725 = 2287397) B2287397
theorem B1807123 : Blo 1068616 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B5149489 : Blo 1068616 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B1807265 : Blo 1068616 1807265 := bstep (se 2 (by rfl) ⟨677724, by rfl⟩ : syracuseStep 1807265 = 1355449) B1355449
theorem B3609521 : Blo 1068616 3609521 := bstep (se 2 (by rfl) ⟨1353570, by rfl⟩ : syracuseStep 3609521 = 2707141) B2707141
theorem B5575601 : Blo 1068616 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B3052529 : Blo 1068616 3052529 := bstep (se 2 (by rfl) ⟨1144698, by rfl⟩ : syracuseStep 3052529 = 2289397) B2289397
theorem B1807393 : Blo 1068616 1807393 := bstep (se 2 (by rfl) ⟨677772, by rfl⟩ : syracuseStep 1807393 = 1355545) B1355545
theorem B1807427 : Blo 1068616 1807427 := bstep (se 1 (by rfl) ⟨1355570, by rfl⟩ : syracuseStep 1807427 = 2711141) B2711141
theorem B1807555 : Blo 1068616 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B1086691 : Blo 1068616 1086691 := bstep (se 1 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 1086691 = 1630037) B1630037
theorem B1807697 : Blo 1068616 1807697 := bstep (se 2 (by rfl) ⟨677886, by rfl⟩ : syracuseStep 1807697 = 1355773) B1355773
theorem B3610061 : Blo 1068616 3610061 := bstep (se 3 (by rfl) ⟨676886, by rfl⟩ : syracuseStep 3610061 = 1353773) B1353773
theorem B1807825 : Blo 1068616 1807825 := bstep (se 2 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 1807825 = 1355869) B1355869
theorem B1807859 : Blo 1068616 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B3610115 : Blo 1068616 3610115 := bstep (se 1 (by rfl) ⟨2707586, by rfl⟩ : syracuseStep 3610115 = 5415173) B5415173
theorem B4068899 : Blo 1068616 4068899 := bstep (se 1 (by rfl) ⟨3051674, by rfl⟩ : syracuseStep 4068899 = 6103349) B6103349
theorem B4068913 : Blo 1068616 4068913 := bstep (se 2 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 4068913 = 3051685) B3051685
theorem B1807987 : Blo 1068616 1807987 := bstep (se 1 (by rfl) ⟨1355990, by rfl⟩ : syracuseStep 1807987 = 2711981) B2711981
theorem B8132237 : Blo 1068616 8132237 := bstep (se 3 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 8132237 = 3049589) B3049589
theorem B1545923 : Blo 1068616 1545923 := bstep (se 1 (by rfl) ⟨1159442, by rfl⟩ : syracuseStep 1545923 = 2318885) B2318885
theorem B1808129 : Blo 1068616 1808129 := bstep (se 2 (by rfl) ⟨678048, by rfl⟩ : syracuseStep 1808129 = 1356097) B1356097
theorem B3053315 : Blo 1068616 3053315 := bstep (se 1 (by rfl) ⟨2289986, by rfl⟩ : syracuseStep 3053315 = 4579973) B4579973
theorem B3610385 : Blo 1068616 3610385 := bstep (se 2 (by rfl) ⟨1353894, by rfl⟩ : syracuseStep 3610385 = 2707789) B2707789
theorem B17372981 : Blo 1068616 17372981 := bstep (se 5 (by rfl) ⟨814358, by rfl⟩ : syracuseStep 17372981 = 1628717) B1628717
theorem B2889539 : Blo 1068616 2889539 := bstep (se 1 (by rfl) ⟨2167154, by rfl⟩ : syracuseStep 2889539 = 4334309) B4334309
theorem B1808257 : Blo 1068616 1808257 := bstep (se 2 (by rfl) ⟨678096, by rfl⟩ : syracuseStep 1808257 = 1356193) B1356193
theorem B1808291 : Blo 1068616 1808291 := bstep (se 1 (by rfl) ⟨1356218, by rfl⟩ : syracuseStep 1808291 = 2712437) B2712437
theorem B1808419 : Blo 1068616 1808419 := bstep (se 1 (by rfl) ⟨1356314, by rfl⟩ : syracuseStep 1808419 = 2712629) B2712629
theorem B3053645 : Blo 1068616 3053645 := bstep (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) B1145117
theorem B1284211 : Blo 1068616 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B3053713 : Blo 1068616 3053713 := bstep (se 2 (by rfl) ⟨1145142, by rfl⟩ : syracuseStep 3053713 = 2290285) B2290285
theorem B1808561 : Blo 1068616 1808561 := bstep (se 2 (by rfl) ⟨678210, by rfl⟩ : syracuseStep 1808561 = 1356421) B1356421
theorem B4888781 : Blo 1068616 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B8689891 : Blo 1068616 8689891 := bstep (se 1 (by rfl) ⟨6517418, by rfl⟩ : syracuseStep 8689891 = 13034837) B13034837
theorem B3610925 : Blo 1068616 3610925 := bstep (se 3 (by rfl) ⟨677048, by rfl⟩ : syracuseStep 3610925 = 1354097) B1354097
theorem B1808689 : Blo 1068616 1808689 := bstep (se 2 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 1808689 = 1356517) B1356517
theorem B1808723 : Blo 1068616 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B3610979 : Blo 1068616 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B3053987 : Blo 1068616 3053987 := bstep (se 1 (by rfl) ⟨2290490, by rfl⟩ : syracuseStep 3053987 = 4580981) B4580981
theorem B1284547 : Blo 1068616 1284547 := bstep (se 1 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 1284547 = 1926821) B1926821
theorem B1808851 : Blo 1068616 1808851 := bstep (se 1 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 1808851 = 2713277) B2713277
theorem B2169425 : Blo 1068616 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B1808993 : Blo 1068616 1808993 := bstep (se 2 (by rfl) ⟨678372, by rfl⟩ : syracuseStep 1808993 = 1356745) B1356745
theorem B3611249 : Blo 1068616 3611249 := bstep (se 2 (by rfl) ⟨1354218, by rfl⟩ : syracuseStep 3611249 = 2708437) B2708437
theorem B5413553 : Blo 1068616 5413553 := bstep (se 2 (by rfl) ⟨2030082, by rfl⟩ : syracuseStep 5413553 = 4060165) B4060165
theorem B1809121 : Blo 1068616 1809121 := bstep (se 2 (by rfl) ⟨678420, by rfl⟩ : syracuseStep 1809121 = 1356841) B1356841
theorem B2169571 : Blo 1068616 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B1809155 : Blo 1068616 1809155 := bstep (se 1 (by rfl) ⟨1356866, by rfl⟩ : syracuseStep 1809155 = 2713733) B2713733
theorem B1809283 : Blo 1068616 1809283 := bstep (se 1 (by rfl) ⟨1356962, by rfl⟩ : syracuseStep 1809283 = 2713925) B2713925
theorem B32971661 : Blo 1068616 32971661 := bstep (se 3 (by rfl) ⟨6182186, by rfl⟩ : syracuseStep 32971661 = 12364373) B12364373
theorem B4070371 : Blo 1068616 4070371 := bstep (se 1 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 4070371 = 6105557) B6105557
theorem B1809425 : Blo 1068616 1809425 := bstep (se 2 (by rfl) ⟨678534, by rfl⟩ : syracuseStep 1809425 = 1357069) B1357069
theorem B43981937 : Blo 1068616 43981937 := bstep (se 2 (by rfl) ⟨16493226, by rfl⟩ : syracuseStep 43981937 = 32986453) B32986453
theorem B3611789 : Blo 1068616 3611789 := bstep (se 3 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 3611789 = 1354421) B1354421
theorem B1809553 : Blo 1068616 1809553 := bstep (se 2 (by rfl) ⟨678582, by rfl⟩ : syracuseStep 1809553 = 1357165) B1357165
theorem B1809587 : Blo 1068616 1809587 := bstep (se 1 (by rfl) ⟨1357190, by rfl⟩ : syracuseStep 1809587 = 2714381) B2714381
theorem B3611843 : Blo 1068616 3611843 := bstep (se 1 (by rfl) ⟨2708882, by rfl⟩ : syracuseStep 3611843 = 5417765) B5417765
theorem B10296517 : Blo 1068616 10296517 := bstep (se 4 (by rfl) ⟨965298, by rfl⟩ : syracuseStep 10296517 = 1930597) B1930597
theorem B1449235 : Blo 1068616 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B1809715 : Blo 1068616 1809715 := bstep (se 1 (by rfl) ⟨1357286, by rfl⟩ : syracuseStep 1809715 = 2714573) B2714573
theorem B13016501 : Blo 1068616 13016501 := bstep (se 5 (by rfl) ⟨610148, by rfl⟩ : syracuseStep 13016501 = 1220297) B1220297
theorem B1809857 : Blo 1068616 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B3612113 : Blo 1068616 3612113 := bstep (se 2 (by rfl) ⟨1354542, by rfl⟩ : syracuseStep 3612113 = 2709085) B2709085
theorem B1809985 : Blo 1068616 1809985 := bstep (se 2 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 1809985 = 1357489) B1357489
theorem B1810019 : Blo 1068616 1810019 := bstep (se 1 (by rfl) ⟨1357514, by rfl⟩ : syracuseStep 1810019 = 2715029) B2715029
theorem B6102641 : Blo 1068616 6102641 := bstep (se 2 (by rfl) ⟨2288490, by rfl⟩ : syracuseStep 6102641 = 4576981) B4576981
theorem B2891441 : Blo 1068616 2891441 := bstep (se 2 (by rfl) ⟨1084290, by rfl⟩ : syracuseStep 2891441 = 2168581) B2168581
theorem B3612653 : Blo 1068616 3612653 := bstep (se 3 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 3612653 = 1354745) B1354745
theorem B3612707 : Blo 1068616 3612707 := bstep (se 1 (by rfl) ⟨2709530, by rfl⟩ : syracuseStep 3612707 = 5419061) B5419061
theorem B5415011 : Blo 1068616 5415011 := bstep (se 1 (by rfl) ⟨4061258, by rfl⟩ : syracuseStep 5415011 = 8122517) B8122517
theorem B2891875 : Blo 1068616 2891875 := bstep (se 1 (by rfl) ⟨2168906, by rfl⟩ : syracuseStep 2891875 = 4337813) B4337813
theorem B4399267 : Blo 1068616 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B3612977 : Blo 1068616 3612977 := bstep (se 2 (by rfl) ⟨1354866, by rfl⟩ : syracuseStep 3612977 = 2709733) B2709733
theorem B8135153 : Blo 1068616 8135153 := bstep (se 2 (by rfl) ⟨3050682, by rfl⟩ : syracuseStep 8135153 = 6101365) B6101365
theorem B1712755 : Blo 1068616 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B2892611 : Blo 1068616 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B3613517 : Blo 1068616 3613517 := bstep (se 3 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 3613517 = 1355069) B1355069
theorem B3613571 : Blo 1068616 3613571 := bstep (se 1 (by rfl) ⟨2710178, by rfl⟩ : syracuseStep 3613571 = 5420357) B5420357
theorem B5415821 : Blo 1068616 5415821 := bstep (se 3 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 5415821 = 2030933) B2030933
theorem B9151501 : Blo 1068616 9151501 := bstep (se 3 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 9151501 = 3431813) B3431813
theorem B6104099 : Blo 1068616 6104099 := bstep (se 1 (by rfl) ⟨4578074, by rfl⟩ : syracuseStep 6104099 = 9156149) B9156149
theorem B4072589 : Blo 1068616 4072589 := bstep (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) B1527221
theorem B3613841 : Blo 1068616 3613841 := bstep (se 2 (by rfl) ⟨1355190, by rfl⟩ : syracuseStep 3613841 = 2710381) B2710381
theorem B1352963 : Blo 1068616 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B14853617 : Blo 1068616 14853617 := bstep (se 2 (by rfl) ⟨5570106, by rfl⟩ : syracuseStep 14853617 = 11140213) B11140213
theorem B2860717 : Blo 1068616 2860717 := bstep (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) B1072769
theorem B3614381 : Blo 1068616 3614381 := bstep (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) B1355393
theorem B3614435 : Blo 1068616 3614435 := bstep (se 1 (by rfl) ⟨2710826, by rfl⟩ : syracuseStep 3614435 = 5421653) B5421653
theorem B1288003 : Blo 1068616 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B1353667 : Blo 1068616 1353667 := bstep (se 1 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 1353667 = 2030501) B2030501
theorem B3614705 : Blo 1068616 3614705 := bstep (se 2 (by rfl) ⟨1355514, by rfl⟩ : syracuseStep 3614705 = 2711029) B2711029
theorem B1353763 : Blo 1068616 1353763 := bstep (se 1 (by rfl) ⟨1015322, by rfl⟩ : syracuseStep 1353763 = 2030645) B2030645
theorem B1648691 : Blo 1068616 1648691 := bstep (se 1 (by rfl) ⟨1236518, by rfl⟩ : syracuseStep 1648691 = 2473037) B2473037
theorem B1714241 : Blo 1068616 1714241 := bstep (se 2 (by rfl) ⟨642840, by rfl⟩ : syracuseStep 1714241 = 1285681) B1285681
theorem B6170737 : Blo 1068616 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B1714369 : Blo 1068616 1714369 := bstep (se 2 (by rfl) ⟨642888, by rfl⟩ : syracuseStep 1714369 = 1285777) B1285777
theorem B1157363 : Blo 1068616 1157363 := bstep (se 1 (by rfl) ⟨868022, by rfl⟩ : syracuseStep 1157363 = 1736045) B1736045
theorem B4565261 : Blo 1068616 4565261 := bstep (se 3 (by rfl) ⟨855986, by rfl⟩ : syracuseStep 4565261 = 1711973) B1711973
theorem B3090737 : Blo 1068616 3090737 := bstep (se 2 (by rfl) ⟨1159026, by rfl⟩ : syracuseStep 3090737 = 2318053) B2318053
theorem B9152837 : Blo 1068616 9152837 := bstep (se 4 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 9152837 = 1716157) B1716157
theorem B1223011 : Blo 1068616 1223011 := bstep (se 1 (by rfl) ⟨917258, by rfl⟩ : syracuseStep 1223011 = 1834517) B1834517
theorem B8235377 : Blo 1068616 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B3615245 : Blo 1068616 3615245 := bstep (se 3 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 3615245 = 1355717) B1355717
theorem B1354259 : Blo 1068616 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B3615299 : Blo 1068616 3615299 := bstep (se 1 (by rfl) ⟨2711474, by rfl⟩ : syracuseStep 3615299 = 5422949) B5422949
theorem B13740785 : Blo 1068616 13740785 := bstep (se 2 (by rfl) ⟨5152794, by rfl⟩ : syracuseStep 13740785 = 10305589) B10305589
theorem B3615569 : Blo 1068616 3615569 := bstep (se 2 (by rfl) ⟨1355838, by rfl⟩ : syracuseStep 3615569 = 2711677) B2711677
theorem B1157971 : Blo 1068616 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B27438101 : Blo 1068616 27438101 := bstep (se 6 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 27438101 = 1286161) B1286161
theorem B2895011 : Blo 1068616 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B2174129 : Blo 1068616 2174129 := bstep (se 2 (by rfl) ⟨815298, by rfl⟩ : syracuseStep 2174129 = 1630597) B1630597
theorem B2174161 : Blo 1068616 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B1354963 : Blo 1068616 1354963 := bstep (se 1 (by rfl) ⟨1016222, by rfl⟩ : syracuseStep 1354963 = 2032445) B2032445
theorem B1355059 : Blo 1068616 1355059 := bstep (se 1 (by rfl) ⟨1016294, by rfl⟩ : syracuseStep 1355059 = 2032589) B2032589
theorem B3616109 : Blo 1068616 3616109 := bstep (se 3 (by rfl) ⟨678020, by rfl⟩ : syracuseStep 3616109 = 1356041) B1356041
theorem B3616163 : Blo 1068616 3616163 := bstep (se 1 (by rfl) ⟨2712122, by rfl⟩ : syracuseStep 3616163 = 5424245) B5424245
theorem B1715651 : Blo 1068616 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1715747 : Blo 1068616 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B4566577 : Blo 1068616 4566577 := bstep (se 2 (by rfl) ⟨1712466, by rfl⟩ : syracuseStep 4566577 = 3424933) B3424933
theorem B1715779 : Blo 1068616 1715779 := bstep (se 1 (by rfl) ⟨1286834, by rfl⟩ : syracuseStep 1715779 = 2573669) B2573669
theorem B2928305 : Blo 1068616 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B3255985 : Blo 1068616 3255985 := bstep (se 2 (by rfl) ⟨1220994, by rfl⟩ : syracuseStep 3255985 = 2441989) B2441989
theorem B3616433 : Blo 1068616 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B5418737 : Blo 1068616 5418737 := bstep (se 2 (by rfl) ⟨2032026, by rfl⟩ : syracuseStep 5418737 = 4064053) B4064053
theorem B1355555 : Blo 1068616 1355555 := bstep (se 1 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 1355555 = 2033333) B2033333
theorem B17379269 : Blo 1068616 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B2404529 : Blo 1068616 2404529 := bstep (se 2 (by rfl) ⟨901698, by rfl⟩ : syracuseStep 2404529 = 1803397) B1803397
theorem B2404547 : Blo 1068616 2404547 := bstep (se 1 (by rfl) ⟨1803410, by rfl⟩ : syracuseStep 2404547 = 3606821) B3606821
theorem B3616973 : Blo 1068616 3616973 := bstep (se 3 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 3616973 = 1356365) B1356365
theorem B3617027 : Blo 1068616 3617027 := bstep (se 1 (by rfl) ⟨2712770, by rfl⟩ : syracuseStep 3617027 = 5425541) B5425541
theorem B2404817 : Blo 1068616 2404817 := bstep (se 2 (by rfl) ⟨901806, by rfl⟩ : syracuseStep 2404817 = 1803613) B1803613
theorem B1716689 : Blo 1068616 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B2404835 : Blo 1068616 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B1356259 : Blo 1068616 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B3617297 : Blo 1068616 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B1356355 : Blo 1068616 1356355 := bstep (se 1 (by rfl) ⟨1017266, by rfl⟩ : syracuseStep 1356355 = 2034533) B2034533
theorem B2405105 : Blo 1068616 2405105 := bstep (se 2 (by rfl) ⟨901914, by rfl⟩ : syracuseStep 2405105 = 1803829) B1803829
theorem B2405123 : Blo 1068616 2405123 := bstep (se 1 (by rfl) ⟨1803842, by rfl⟩ : syracuseStep 2405123 = 3607685) B3607685
theorem B2405393 : Blo 1068616 2405393 := bstep (se 2 (by rfl) ⟨902022, by rfl⟩ : syracuseStep 2405393 = 1804045) B1804045
theorem B2405411 : Blo 1068616 2405411 := bstep (se 1 (by rfl) ⟨1804058, by rfl⟩ : syracuseStep 2405411 = 3608117) B3608117
theorem B3617837 : Blo 1068616 3617837 := bstep (se 3 (by rfl) ⟨678344, by rfl⟩ : syracuseStep 3617837 = 1356689) B1356689
theorem B1356851 : Blo 1068616 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B2569315 : Blo 1068616 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B3617891 : Blo 1068616 3617891 := bstep (se 1 (by rfl) ⟨2713418, by rfl⟩ : syracuseStep 3617891 = 5426837) B5426837
theorem B6599843 : Blo 1068616 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B5420195 : Blo 1068616 5420195 := bstep (se 1 (by rfl) ⟨4065146, by rfl⟩ : syracuseStep 5420195 = 8130293) B8130293
theorem B1651955 : Blo 1068616 1651955 := bstep (se 1 (by rfl) ⟨1238966, by rfl⟩ : syracuseStep 1651955 = 2477933) B2477933
theorem B2405681 : Blo 1068616 2405681 := bstep (se 2 (by rfl) ⟨902130, by rfl⟩ : syracuseStep 2405681 = 1804261) B1804261
theorem B2405699 : Blo 1068616 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B1389907 : Blo 1068616 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B3618161 : Blo 1068616 3618161 := bstep (se 2 (by rfl) ⟨1356810, by rfl⟩ : syracuseStep 3618161 = 2713621) B2713621
theorem B2897315 : Blo 1068616 2897315 := bstep (se 1 (by rfl) ⟨2172986, by rfl⟩ : syracuseStep 2897315 = 4345973) B4345973
theorem B2405969 : Blo 1068616 2405969 := bstep (se 2 (by rfl) ⟨902238, by rfl⟩ : syracuseStep 2405969 = 1804477) B1804477
theorem B2405987 : Blo 1068616 2405987 := bstep (se 1 (by rfl) ⟨1804490, by rfl⟩ : syracuseStep 2405987 = 3608981) B3608981
theorem B1718003 : Blo 1068616 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B7812877 : Blo 1068616 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B2406257 : Blo 1068616 2406257 := bstep (se 2 (by rfl) ⟨902346, by rfl⟩ : syracuseStep 2406257 = 1804693) B1804693
theorem B2406275 : Blo 1068616 2406275 := bstep (se 1 (by rfl) ⟨1804706, by rfl⟩ : syracuseStep 2406275 = 3609413) B3609413
theorem B5945221 : Blo 1068616 5945221 := bstep (se 4 (by rfl) ⟨557364, by rfl⟩ : syracuseStep 5945221 = 1114729) B1114729
theorem B3618701 : Blo 1068616 3618701 := bstep (se 3 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 3618701 = 1357013) B1357013
theorem B3618755 : Blo 1068616 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B30816197 : Blo 1068616 30816197 := bstep (se 4 (by rfl) ⟨2889018, by rfl⟩ : syracuseStep 30816197 = 5778037) B5778037
theorem B5421005 : Blo 1068616 5421005 := bstep (se 3 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 5421005 = 2032877) B2032877
theorem B4700273 : Blo 1068616 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B2406545 : Blo 1068616 2406545 := bstep (se 2 (by rfl) ⟨902454, by rfl⟩ : syracuseStep 2406545 = 1804909) B1804909
theorem B2406563 : Blo 1068616 2406563 := bstep (se 1 (by rfl) ⟨1804922, by rfl⟩ : syracuseStep 2406563 = 3609845) B3609845
theorem B3619025 : Blo 1068616 3619025 := bstep (se 2 (by rfl) ⟨1357134, by rfl⟩ : syracuseStep 3619025 = 2714269) B2714269
theorem B2570545 : Blo 1068616 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B2406833 : Blo 1068616 2406833 := bstep (se 2 (by rfl) ⟨902562, by rfl⟩ : syracuseStep 2406833 = 1805125) B1805125
theorem B2406851 : Blo 1068616 2406851 := bstep (se 1 (by rfl) ⟨1805138, by rfl⟩ : syracuseStep 2406851 = 3610277) B3610277
theorem B1522147 : Blo 1068616 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B4569635 : Blo 1068616 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B1522243 : Blo 1068616 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B2407121 : Blo 1068616 2407121 := bstep (se 2 (by rfl) ⟨902670, by rfl⟩ : syracuseStep 2407121 = 1805341) B1805341
theorem B2407139 : Blo 1068616 2407139 := bstep (se 1 (by rfl) ⟨1805354, by rfl⟩ : syracuseStep 2407139 = 3610709) B3610709
theorem B3619565 : Blo 1068616 3619565 := bstep (se 3 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 3619565 = 1357337) B1357337
theorem B3619619 : Blo 1068616 3619619 := bstep (se 1 (by rfl) ⟨2714714, by rfl⟩ : syracuseStep 3619619 = 5429429) B5429429
theorem B2407409 : Blo 1068616 2407409 := bstep (se 2 (by rfl) ⟨902778, by rfl⟩ : syracuseStep 2407409 = 1805557) B1805557
theorem B2407427 : Blo 1068616 2407427 := bstep (se 1 (by rfl) ⟨1805570, by rfl⟩ : syracuseStep 2407427 = 3611141) B3611141
theorem B6863885 : Blo 1068616 6863885 := bstep (se 3 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 6863885 = 2573957) B2573957
theorem B3619889 : Blo 1068616 3619889 := bstep (se 2 (by rfl) ⟨1357458, by rfl⟩ : syracuseStep 3619889 = 2714917) B2714917
theorem B1522739 : Blo 1068616 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B5782691 : Blo 1068616 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B9157859 : Blo 1068616 9157859 := bstep (se 1 (by rfl) ⟨6868394, by rfl⟩ : syracuseStep 9157859 = 13736789) B13736789
theorem B2407697 : Blo 1068616 2407697 := bstep (se 2 (by rfl) ⟨902886, by rfl⟩ : syracuseStep 2407697 = 1805773) B1805773
theorem B2407715 : Blo 1068616 2407715 := bstep (se 1 (by rfl) ⟨1805786, by rfl⟩ : syracuseStep 2407715 = 3611573) B3611573
theorem B2407985 : Blo 1068616 2407985 := bstep (se 2 (by rfl) ⟨902994, by rfl⟩ : syracuseStep 2407985 = 1805989) B1805989
theorem B2408003 : Blo 1068616 2408003 := bstep (se 1 (by rfl) ⟨1806002, by rfl⟩ : syracuseStep 2408003 = 3612005) B3612005
theorem B1523377 : Blo 1068616 1523377 := bstep (se 2 (by rfl) ⟨571266, by rfl⟩ : syracuseStep 1523377 = 1142533) B1142533
theorem B3423971 : Blo 1068616 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B2408273 : Blo 1068616 2408273 := bstep (se 2 (by rfl) ⟨903102, by rfl⟩ : syracuseStep 2408273 = 1806205) B1806205
theorem B2408291 : Blo 1068616 2408291 := bstep (se 1 (by rfl) ⟨1806218, by rfl⟩ : syracuseStep 2408291 = 3612437) B3612437
theorem B1523713 : Blo 1068616 1523713 := bstep (se 2 (by rfl) ⟨571392, by rfl⟩ : syracuseStep 1523713 = 1142785) B1142785
theorem B2408561 : Blo 1068616 2408561 := bstep (se 2 (by rfl) ⟨903210, by rfl⟩ : syracuseStep 2408561 = 1806421) B1806421
theorem B2408579 : Blo 1068616 2408579 := bstep (se 1 (by rfl) ⟨1806434, by rfl⟩ : syracuseStep 2408579 = 3612869) B3612869
theorem B2408849 : Blo 1068616 2408849 := bstep (se 2 (by rfl) ⟨903318, by rfl⟩ : syracuseStep 2408849 = 1806637) B1806637
theorem B2408867 : Blo 1068616 2408867 := bstep (se 1 (by rfl) ⟨1806650, by rfl⟩ : syracuseStep 2408867 = 3613301) B3613301
theorem B1524305 : Blo 1068616 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B3424945 : Blo 1068616 3424945 := bstep (se 2 (by rfl) ⟨1284354, by rfl⟩ : syracuseStep 3424945 = 2568709) B2568709
theorem B2933425 : Blo 1068616 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B2409137 : Blo 1068616 2409137 := bstep (se 2 (by rfl) ⟨903426, by rfl⟩ : syracuseStep 2409137 = 1806853) B1806853
theorem B2409155 : Blo 1068616 2409155 := bstep (se 1 (by rfl) ⟨1806866, by rfl⟩ : syracuseStep 2409155 = 3613733) B3613733
theorem B8798989 : Blo 1068616 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B5423921 : Blo 1068616 5423921 := bstep (se 2 (by rfl) ⟨2033970, by rfl⟩ : syracuseStep 5423921 = 4067941) B4067941
theorem B2409425 : Blo 1068616 2409425 := bstep (se 2 (by rfl) ⟨903534, by rfl⟩ : syracuseStep 2409425 = 1807069) B1807069
theorem B2409443 : Blo 1068616 2409443 := bstep (se 1 (by rfl) ⟨1807082, by rfl⟩ : syracuseStep 2409443 = 3614165) B3614165
theorem B1524835 : Blo 1068616 1524835 := bstep (se 1 (by rfl) ⟨1143626, by rfl⟩ : syracuseStep 1524835 = 2287253) B2287253
theorem B2409713 : Blo 1068616 2409713 := bstep (se 2 (by rfl) ⟨903642, by rfl⟩ : syracuseStep 2409713 = 1807285) B1807285
theorem B2409731 : Blo 1068616 2409731 := bstep (se 1 (by rfl) ⟨1807298, by rfl⟩ : syracuseStep 2409731 = 3614597) B3614597
theorem B1525171 : Blo 1068616 1525171 := bstep (se 1 (by rfl) ⟨1143878, by rfl⟩ : syracuseStep 1525171 = 2287757) B2287757
theorem B2410001 : Blo 1068616 2410001 := bstep (se 2 (by rfl) ⟨903750, by rfl⟩ : syracuseStep 2410001 = 1807501) B1807501
theorem B2410019 : Blo 1068616 2410019 := bstep (se 1 (by rfl) ⟨1807514, by rfl⟩ : syracuseStep 2410019 = 3615029) B3615029
theorem B2410289 : Blo 1068616 2410289 := bstep (se 2 (by rfl) ⟨903858, by rfl⟩ : syracuseStep 2410289 = 1807717) B1807717
theorem B2410307 : Blo 1068616 2410307 := bstep (se 1 (by rfl) ⟨1807730, by rfl⟩ : syracuseStep 2410307 = 3615461) B3615461
theorem B15452045 : Blo 1068616 15452045 := bstep (se 3 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 15452045 = 5794517) B5794517
theorem B1525729 : Blo 1068616 1525729 := bstep (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) B1144297
theorem B1525763 : Blo 1068616 1525763 := bstep (se 1 (by rfl) ⟨1144322, by rfl⟩ : syracuseStep 1525763 = 2288645) B2288645
theorem B2410577 : Blo 1068616 2410577 := bstep (se 2 (by rfl) ⟨903966, by rfl⟩ : syracuseStep 2410577 = 1807933) B1807933
theorem B2410595 : Blo 1068616 2410595 := bstep (se 1 (by rfl) ⟨1807946, by rfl⟩ : syracuseStep 2410595 = 3615893) B3615893
theorem B2705521 : Blo 1068616 2705521 := bstep (se 2 (by rfl) ⟨1014570, by rfl⟩ : syracuseStep 2705521 = 2029141) B2029141
theorem B69552341 : Blo 1068616 69552341 := bstep (se 7 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 69552341 = 1630133) B1630133
theorem B5425379 : Blo 1068616 5425379 := bstep (se 1 (by rfl) ⟨4069034, by rfl⟩ : syracuseStep 5425379 = 8138069) B8138069
theorem B3426637 : Blo 1068616 3426637 := bstep (se 3 (by rfl) ⟨642494, by rfl⟩ : syracuseStep 3426637 = 1284989) B1284989
theorem B2410865 : Blo 1068616 2410865 := bstep (se 2 (by rfl) ⟨904074, by rfl⟩ : syracuseStep 2410865 = 1808149) B1808149
theorem B1952131 : Blo 1068616 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B2705795 : Blo 1068616 2705795 := bstep (se 1 (by rfl) ⟨2029346, by rfl⟩ : syracuseStep 2705795 = 4058693) B4058693
theorem B2410883 : Blo 1068616 2410883 := bstep (se 1 (by rfl) ⟨1808162, by rfl⟩ : syracuseStep 2410883 = 3616325) B3616325
theorem B12175757 : Blo 1068616 12175757 := bstep (se 3 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 12175757 = 4565909) B4565909
theorem B1526321 : Blo 1068616 1526321 := bstep (se 2 (by rfl) ⟨572370, by rfl⟩ : syracuseStep 1526321 = 1144741) B1144741
theorem B2705987 : Blo 1068616 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B1526401 : Blo 1068616 1526401 := bstep (se 2 (by rfl) ⟨572400, by rfl⟩ : syracuseStep 1526401 = 1144801) B1144801
theorem B4573837 : Blo 1068616 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B2411153 : Blo 1068616 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B2411171 : Blo 1068616 2411171 := bstep (se 1 (by rfl) ⟨1808378, by rfl⟩ : syracuseStep 2411171 = 3616757) B3616757
theorem B1100531 : Blo 1068616 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B2607985 : Blo 1068616 2607985 := bstep (se 2 (by rfl) ⟨977994, by rfl⟩ : syracuseStep 2607985 = 1955989) B1955989
theorem B9161585 : Blo 1068616 9161585 := bstep (se 2 (by rfl) ⟨3435594, by rfl⟩ : syracuseStep 9161585 = 6871189) B6871189
theorem B2411441 : Blo 1068616 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B2411459 : Blo 1068616 2411459 := bstep (se 1 (by rfl) ⟨1808594, by rfl⟩ : syracuseStep 2411459 = 3617189) B3617189
theorem B5426189 : Blo 1068616 5426189 := bstep (se 3 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 5426189 = 2034821) B2034821
theorem B2411729 : Blo 1068616 2411729 := bstep (se 2 (by rfl) ⟨904398, by rfl⟩ : syracuseStep 2411729 = 1808797) B1808797
theorem B2411747 : Blo 1068616 2411747 := bstep (se 1 (by rfl) ⟨1808810, by rfl⟩ : syracuseStep 2411747 = 3617621) B3617621
theorem B1527187 : Blo 1068616 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B2706929 : Blo 1068616 2706929 := bstep (se 2 (by rfl) ⟨1015098, by rfl⟩ : syracuseStep 2706929 = 2030197) B2030197
theorem B2412017 : Blo 1068616 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B2412035 : Blo 1068616 2412035 := bstep (se 1 (by rfl) ⟨1809026, by rfl⟩ : syracuseStep 2412035 = 3618053) B3618053
theorem B2706979 : Blo 1068616 2706979 := bstep (se 1 (by rfl) ⟨2030234, by rfl⟩ : syracuseStep 2706979 = 4060469) B4060469
theorem B1068627 : Blo 1068616 1068627 := bstep (se 1 (by rfl) ⟨801470, by rfl⟩ : syracuseStep 1068627 = 1602941) B1602941
theorem B1068643 : Blo 1068616 1068643 := bstep (se 1 (by rfl) ⟨801482, by rfl⟩ : syracuseStep 1068643 = 1602965) B1602965
theorem B1068659 : Blo 1068616 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B1068675 : Blo 1068616 1068675 := bstep (se 1 (by rfl) ⟨801506, by rfl⟩ : syracuseStep 1068675 = 1603013) B1603013
theorem B1068691 : Blo 1068616 1068691 := bstep (se 1 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 1068691 = 1603037) B1603037
theorem B1068707 : Blo 1068616 1068707 := bstep (se 1 (by rfl) ⟨801530, by rfl⟩ : syracuseStep 1068707 = 1603061) B1603061
theorem B2707121 : Blo 1068616 2707121 := bstep (se 2 (by rfl) ⟨1015170, by rfl⟩ : syracuseStep 2707121 = 2030341) B2030341
theorem B1068723 : Blo 1068616 1068723 := bstep (se 1 (by rfl) ⟨801542, by rfl⟩ : syracuseStep 1068723 = 1603085) B1603085
theorem B1068739 : Blo 1068616 1068739 := bstep (se 1 (by rfl) ⟨801554, by rfl⟩ : syracuseStep 1068739 = 1603109) B1603109
theorem B2576081 : Blo 1068616 2576081 := bstep (se 2 (by rfl) ⟨966030, by rfl⟩ : syracuseStep 2576081 = 1932061) B1932061
theorem B1068755 : Blo 1068616 1068755 := bstep (se 1 (by rfl) ⟨801566, by rfl⟩ : syracuseStep 1068755 = 1603133) B1603133
theorem B1068771 : Blo 1068616 1068771 := bstep (se 1 (by rfl) ⟨801578, by rfl⟩ : syracuseStep 1068771 = 1603157) B1603157
theorem B1068787 : Blo 1068616 1068787 := bstep (se 1 (by rfl) ⟨801590, by rfl⟩ : syracuseStep 1068787 = 1603181) B1603181
theorem B1068803 : Blo 1068616 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B2412305 : Blo 1068616 2412305 := bstep (se 2 (by rfl) ⟨904614, by rfl⟩ : syracuseStep 2412305 = 1809229) B1809229
theorem B1068819 : Blo 1068616 1068819 := bstep (se 1 (by rfl) ⟨801614, by rfl⟩ : syracuseStep 1068819 = 1603229) B1603229
theorem B1068835 : Blo 1068616 1068835 := bstep (se 1 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 1068835 = 1603253) B1603253
theorem B2412323 : Blo 1068616 2412323 := bstep (se 1 (by rfl) ⟨1809242, by rfl⟩ : syracuseStep 2412323 = 3618485) B3618485
theorem B1068851 : Blo 1068616 1068851 := bstep (se 1 (by rfl) ⟨801638, by rfl⟩ : syracuseStep 1068851 = 1603277) B1603277
theorem B1068867 : Blo 1068616 1068867 := bstep (se 1 (by rfl) ⟨801650, by rfl⟩ : syracuseStep 1068867 = 1603301) B1603301
theorem B2314051 : Blo 1068616 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B1068883 : Blo 1068616 1068883 := bstep (se 1 (by rfl) ⟨801662, by rfl⟩ : syracuseStep 1068883 = 1603325) B1603325
theorem B1068899 : Blo 1068616 1068899 := bstep (se 1 (by rfl) ⟨801674, by rfl⟩ : syracuseStep 1068899 = 1603349) B1603349
theorem B1068915 : Blo 1068616 1068915 := bstep (se 1 (by rfl) ⟨801686, by rfl⟩ : syracuseStep 1068915 = 1603373) B1603373
theorem B1068931 : Blo 1068616 1068931 := bstep (se 1 (by rfl) ⟨801698, by rfl⟩ : syracuseStep 1068931 = 1603397) B1603397
theorem B1068947 : Blo 1068616 1068947 := bstep (se 1 (by rfl) ⟨801710, by rfl⟩ : syracuseStep 1068947 = 1603421) B1603421
theorem B1068963 : Blo 1068616 1068963 := bstep (se 1 (by rfl) ⟨801722, by rfl⟩ : syracuseStep 1068963 = 1603445) B1603445
theorem B1068979 : Blo 1068616 1068979 := bstep (se 1 (by rfl) ⟨801734, by rfl⟩ : syracuseStep 1068979 = 1603469) B1603469
theorem B1068995 : Blo 1068616 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B1069011 : Blo 1068616 1069011 := bstep (se 1 (by rfl) ⟨801758, by rfl⟩ : syracuseStep 1069011 = 1603517) B1603517
theorem B1069027 : Blo 1068616 1069027 := bstep (se 1 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 1069027 = 1603541) B1603541
theorem B1069043 : Blo 1068616 1069043 := bstep (se 1 (by rfl) ⟨801782, by rfl⟩ : syracuseStep 1069043 = 1603565) B1603565
theorem B1069059 : Blo 1068616 1069059 := bstep (se 1 (by rfl) ⟨801794, by rfl⟩ : syracuseStep 1069059 = 1603589) B1603589
theorem B1069075 : Blo 1068616 1069075 := bstep (se 1 (by rfl) ⟨801806, by rfl⟩ : syracuseStep 1069075 = 1603613) B1603613
theorem B1069091 : Blo 1068616 1069091 := bstep (se 1 (by rfl) ⟨801818, by rfl⟩ : syracuseStep 1069091 = 1603637) B1603637
theorem B2412593 : Blo 1068616 2412593 := bstep (se 2 (by rfl) ⟨904722, by rfl⟩ : syracuseStep 2412593 = 1809445) B1809445
theorem B1069107 : Blo 1068616 1069107 := bstep (se 1 (by rfl) ⟨801830, by rfl⟩ : syracuseStep 1069107 = 1603661) B1603661
theorem B1069123 : Blo 1068616 1069123 := bstep (se 1 (by rfl) ⟨801842, by rfl⟩ : syracuseStep 1069123 = 1603685) B1603685
theorem B3428419 : Blo 1068616 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B2412611 : Blo 1068616 2412611 := bstep (se 1 (by rfl) ⟨1809458, by rfl⟩ : syracuseStep 2412611 = 3618917) B3618917
theorem B1626193 : Blo 1068616 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1069139 : Blo 1068616 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1069155 : Blo 1068616 1069155 := bstep (se 1 (by rfl) ⟨801866, by rfl⟩ : syracuseStep 1069155 = 1603733) B1603733
theorem B1069171 : Blo 1068616 1069171 := bstep (se 1 (by rfl) ⟨801878, by rfl⟩ : syracuseStep 1069171 = 1603757) B1603757
theorem B1626241 : Blo 1068616 1626241 := bstep (se 2 (by rfl) ⟨609840, by rfl⟩ : syracuseStep 1626241 = 1219681) B1219681
theorem B1069187 : Blo 1068616 1069187 := bstep (se 1 (by rfl) ⟨801890, by rfl⟩ : syracuseStep 1069187 = 1603781) B1603781
theorem B3657869 : Blo 1068616 3657869 := bstep (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) B1371701
theorem B1069203 : Blo 1068616 1069203 := bstep (se 1 (by rfl) ⟨801902, by rfl⟩ : syracuseStep 1069203 = 1603805) B1603805
theorem B1855649 : Blo 1068616 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B1069219 : Blo 1068616 1069219 := bstep (se 1 (by rfl) ⟨801914, by rfl⟩ : syracuseStep 1069219 = 1603829) B1603829
theorem B1069235 : Blo 1068616 1069235 := bstep (se 1 (by rfl) ⟨801926, by rfl⟩ : syracuseStep 1069235 = 1603853) B1603853
theorem B1069251 : Blo 1068616 1069251 := bstep (se 1 (by rfl) ⟨801938, by rfl⟩ : syracuseStep 1069251 = 1603877) B1603877
theorem B9752773 : Blo 1068616 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B1069267 : Blo 1068616 1069267 := bstep (se 1 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 1069267 = 1603901) B1603901
theorem B1069283 : Blo 1068616 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B1069299 : Blo 1068616 1069299 := bstep (se 1 (by rfl) ⟨801974, by rfl⟩ : syracuseStep 1069299 = 1603949) B1603949
theorem B1069315 : Blo 1068616 1069315 := bstep (se 1 (by rfl) ⟨801986, by rfl⟩ : syracuseStep 1069315 = 1603973) B1603973
theorem B1069331 : Blo 1068616 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B1069347 : Blo 1068616 1069347 := bstep (se 1 (by rfl) ⟨802010, by rfl⟩ : syracuseStep 1069347 = 1604021) B1604021
theorem B5493041 : Blo 1068616 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B1069363 : Blo 1068616 1069363 := bstep (se 1 (by rfl) ⟨802022, by rfl⟩ : syracuseStep 1069363 = 1604045) B1604045
theorem B1069379 : Blo 1068616 1069379 := bstep (se 1 (by rfl) ⟨802034, by rfl⟩ : syracuseStep 1069379 = 1604069) B1604069
theorem B3658061 : Blo 1068616 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B2412881 : Blo 1068616 2412881 := bstep (se 2 (by rfl) ⟨904830, by rfl⟩ : syracuseStep 2412881 = 1809661) B1809661
theorem B1069395 : Blo 1068616 1069395 := bstep (se 1 (by rfl) ⟨802046, by rfl⟩ : syracuseStep 1069395 = 1604093) B1604093
theorem B1069411 : Blo 1068616 1069411 := bstep (se 1 (by rfl) ⟨802058, by rfl⟩ : syracuseStep 1069411 = 1604117) B1604117
theorem B2412899 : Blo 1068616 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B1069427 : Blo 1068616 1069427 := bstep (se 1 (by rfl) ⟨802070, by rfl⟩ : syracuseStep 1069427 = 1604141) B1604141
theorem B1069443 : Blo 1068616 1069443 := bstep (se 1 (by rfl) ⟨802082, by rfl⟩ : syracuseStep 1069443 = 1604165) B1604165
theorem B1069459 : Blo 1068616 1069459 := bstep (se 1 (by rfl) ⟨802094, by rfl⟩ : syracuseStep 1069459 = 1604189) B1604189
theorem B1069475 : Blo 1068616 1069475 := bstep (se 1 (by rfl) ⟨802106, by rfl⟩ : syracuseStep 1069475 = 1604213) B1604213
theorem B1069491 : Blo 1068616 1069491 := bstep (se 1 (by rfl) ⟨802118, by rfl⟩ : syracuseStep 1069491 = 1604237) B1604237
theorem B1069507 : Blo 1068616 1069507 := bstep (se 1 (by rfl) ⟨802130, by rfl⟩ : syracuseStep 1069507 = 1604261) B1604261
theorem B1069523 : Blo 1068616 1069523 := bstep (se 1 (by rfl) ⟨802142, by rfl⟩ : syracuseStep 1069523 = 1604285) B1604285
theorem B1069539 : Blo 1068616 1069539 := bstep (se 1 (by rfl) ⟨802154, by rfl⟩ : syracuseStep 1069539 = 1604309) B1604309
theorem B1069555 : Blo 1068616 1069555 := bstep (se 1 (by rfl) ⟨802166, by rfl⟩ : syracuseStep 1069555 = 1604333) B1604333
theorem B1069571 : Blo 1068616 1069571 := bstep (se 1 (by rfl) ⟨802178, by rfl⟩ : syracuseStep 1069571 = 1604357) B1604357
theorem B3428867 : Blo 1068616 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B1069587 : Blo 1068616 1069587 := bstep (se 1 (by rfl) ⟨802190, by rfl⟩ : syracuseStep 1069587 = 1604381) B1604381
theorem B1069603 : Blo 1068616 1069603 := bstep (se 1 (by rfl) ⟨802202, by rfl⟩ : syracuseStep 1069603 = 1604405) B1604405
theorem B3854897 : Blo 1068616 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B6509105 : Blo 1068616 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B1069619 : Blo 1068616 1069619 := bstep (se 1 (by rfl) ⟨802214, by rfl⟩ : syracuseStep 1069619 = 1604429) B1604429
theorem B1069635 : Blo 1068616 1069635 := bstep (se 1 (by rfl) ⟨802226, by rfl⟩ : syracuseStep 1069635 = 1604453) B1604453
theorem B6869573 : Blo 1068616 6869573 := bstep (se 4 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 6869573 = 1288045) B1288045
theorem B1069651 : Blo 1068616 1069651 := bstep (se 1 (by rfl) ⟨802238, by rfl⟩ : syracuseStep 1069651 = 1604477) B1604477
theorem B1069667 : Blo 1068616 1069667 := bstep (se 1 (by rfl) ⟨802250, by rfl⟩ : syracuseStep 1069667 = 1604501) B1604501
theorem B2413169 : Blo 1068616 2413169 := bstep (se 2 (by rfl) ⟨904938, by rfl⟩ : syracuseStep 2413169 = 1809877) B1809877
theorem B1069683 : Blo 1068616 1069683 := bstep (se 1 (by rfl) ⟨802262, by rfl⟩ : syracuseStep 1069683 = 1604525) B1604525
theorem B1069699 : Blo 1068616 1069699 := bstep (se 1 (by rfl) ⟨802274, by rfl⟩ : syracuseStep 1069699 = 1604549) B1604549
theorem B2413187 : Blo 1068616 2413187 := bstep (se 1 (by rfl) ⟨1809890, by rfl⟩ : syracuseStep 2413187 = 3619781) B3619781
theorem B8245901 : Blo 1068616 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B2708113 : Blo 1068616 2708113 := bstep (se 2 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 2708113 = 2031085) B2031085
theorem B1069715 : Blo 1068616 1069715 := bstep (se 1 (by rfl) ⟨802286, by rfl⟩ : syracuseStep 1069715 = 1604573) B1604573
theorem B1069731 : Blo 1068616 1069731 := bstep (se 1 (by rfl) ⟨802298, by rfl⟩ : syracuseStep 1069731 = 1604597) B1604597
theorem B1069747 : Blo 1068616 1069747 := bstep (se 1 (by rfl) ⟨802310, by rfl⟩ : syracuseStep 1069747 = 1604621) B1604621
theorem B1069763 : Blo 1068616 1069763 := bstep (se 1 (by rfl) ⟨802322, by rfl⟩ : syracuseStep 1069763 = 1604645) B1604645
theorem B1069779 : Blo 1068616 1069779 := bstep (se 1 (by rfl) ⟨802334, by rfl⟩ : syracuseStep 1069779 = 1604669) B1604669
theorem B10277603 : Blo 1068616 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B1069795 : Blo 1068616 1069795 := bstep (se 1 (by rfl) ⟨802346, by rfl⟩ : syracuseStep 1069795 = 1604693) B1604693
theorem B1069811 : Blo 1068616 1069811 := bstep (se 1 (by rfl) ⟨802358, by rfl⟩ : syracuseStep 1069811 = 1604717) B1604717
theorem B1069827 : Blo 1068616 1069827 := bstep (se 1 (by rfl) ⟨802370, by rfl⟩ : syracuseStep 1069827 = 1604741) B1604741
theorem B1069843 : Blo 1068616 1069843 := bstep (se 1 (by rfl) ⟨802382, by rfl⟩ : syracuseStep 1069843 = 1604765) B1604765
theorem B1069859 : Blo 1068616 1069859 := bstep (se 1 (by rfl) ⟨802394, by rfl⟩ : syracuseStep 1069859 = 1604789) B1604789
theorem B1069875 : Blo 1068616 1069875 := bstep (se 1 (by rfl) ⟨802406, by rfl⟩ : syracuseStep 1069875 = 1604813) B1604813
theorem B1069891 : Blo 1068616 1069891 := bstep (se 1 (by rfl) ⟨802418, by rfl⟩ : syracuseStep 1069891 = 1604837) B1604837
theorem B1069907 : Blo 1068616 1069907 := bstep (se 1 (by rfl) ⟨802430, by rfl⟩ : syracuseStep 1069907 = 1604861) B1604861
theorem B1069923 : Blo 1068616 1069923 := bstep (se 1 (by rfl) ⟨802442, by rfl⟩ : syracuseStep 1069923 = 1604885) B1604885
theorem B1069939 : Blo 1068616 1069939 := bstep (se 1 (by rfl) ⟨802454, by rfl⟩ : syracuseStep 1069939 = 1604909) B1604909
theorem B1069955 : Blo 1068616 1069955 := bstep (se 1 (by rfl) ⟨802466, by rfl⟩ : syracuseStep 1069955 = 1604933) B1604933
theorem B1069971 : Blo 1068616 1069971 := bstep (se 1 (by rfl) ⟨802478, by rfl⟩ : syracuseStep 1069971 = 1604957) B1604957
theorem B2708387 : Blo 1068616 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B1069987 : Blo 1068616 1069987 := bstep (se 1 (by rfl) ⟨802490, by rfl⟩ : syracuseStep 1069987 = 1604981) B1604981
theorem B1070003 : Blo 1068616 1070003 := bstep (se 1 (by rfl) ⟨802502, by rfl⟩ : syracuseStep 1070003 = 1605005) B1605005
theorem B1070019 : Blo 1068616 1070019 := bstep (se 1 (by rfl) ⟨802514, by rfl⟩ : syracuseStep 1070019 = 1605029) B1605029
theorem B1070035 : Blo 1068616 1070035 := bstep (se 1 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 1070035 = 1605053) B1605053
theorem B1070051 : Blo 1068616 1070051 := bstep (se 1 (by rfl) ⟨802538, by rfl⟩ : syracuseStep 1070051 = 1605077) B1605077
theorem B1070067 : Blo 1068616 1070067 := bstep (se 1 (by rfl) ⟨802550, by rfl⟩ : syracuseStep 1070067 = 1605101) B1605101
theorem B1070083 : Blo 1068616 1070083 := bstep (se 1 (by rfl) ⟨802562, by rfl⟩ : syracuseStep 1070083 = 1605125) B1605125
theorem B1070099 : Blo 1068616 1070099 := bstep (se 1 (by rfl) ⟨802574, by rfl⟩ : syracuseStep 1070099 = 1605149) B1605149
theorem B1070115 : Blo 1068616 1070115 := bstep (se 1 (by rfl) ⟨802586, by rfl⟩ : syracuseStep 1070115 = 1605173) B1605173
theorem B1070131 : Blo 1068616 1070131 := bstep (se 1 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 1070131 = 1605197) B1605197
theorem B1070147 : Blo 1068616 1070147 := bstep (se 1 (by rfl) ⟨802610, by rfl⟩ : syracuseStep 1070147 = 1605221) B1605221
theorem B1070163 : Blo 1068616 1070163 := bstep (se 1 (by rfl) ⟨802622, by rfl⟩ : syracuseStep 1070163 = 1605245) B1605245
theorem B2708579 : Blo 1068616 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B1070179 : Blo 1068616 1070179 := bstep (se 1 (by rfl) ⟨802634, by rfl⟩ : syracuseStep 1070179 = 1605269) B1605269
theorem B1070195 : Blo 1068616 1070195 := bstep (se 1 (by rfl) ⟨802646, by rfl⟩ : syracuseStep 1070195 = 1605293) B1605293
theorem B1070211 : Blo 1068616 1070211 := bstep (se 1 (by rfl) ⟨802658, by rfl⟩ : syracuseStep 1070211 = 1605317) B1605317
theorem B1070227 : Blo 1068616 1070227 := bstep (se 1 (by rfl) ⟨802670, by rfl⟩ : syracuseStep 1070227 = 1605341) B1605341
theorem B1070243 : Blo 1068616 1070243 := bstep (se 1 (by rfl) ⟨802682, by rfl⟩ : syracuseStep 1070243 = 1605365) B1605365
theorem B1070259 : Blo 1068616 1070259 := bstep (se 1 (by rfl) ⟨802694, by rfl⟩ : syracuseStep 1070259 = 1605389) B1605389
theorem B1070275 : Blo 1068616 1070275 := bstep (se 1 (by rfl) ⟨802706, by rfl⟩ : syracuseStep 1070275 = 1605413) B1605413
theorem B1070291 : Blo 1068616 1070291 := bstep (se 1 (by rfl) ⟨802718, by rfl⟩ : syracuseStep 1070291 = 1605437) B1605437
theorem B1070307 : Blo 1068616 1070307 := bstep (se 1 (by rfl) ⟨802730, by rfl⟩ : syracuseStep 1070307 = 1605461) B1605461
theorem B12178673 : Blo 1068616 12178673 := bstep (se 2 (by rfl) ⟨4567002, by rfl⟩ : syracuseStep 12178673 = 9134005) B9134005
theorem B1070323 : Blo 1068616 1070323 := bstep (se 1 (by rfl) ⟨802742, by rfl⟩ : syracuseStep 1070323 = 1605485) B1605485
theorem B1070339 : Blo 1068616 1070339 := bstep (se 1 (by rfl) ⟨802754, by rfl⟩ : syracuseStep 1070339 = 1605509) B1605509
theorem B1627409 : Blo 1068616 1627409 := bstep (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) B1220557
theorem B1070355 : Blo 1068616 1070355 := bstep (se 1 (by rfl) ⟨802766, by rfl⟩ : syracuseStep 1070355 = 1605533) B1605533
theorem B1070371 : Blo 1068616 1070371 := bstep (se 1 (by rfl) ⟨802778, by rfl⟩ : syracuseStep 1070371 = 1605557) B1605557
theorem B1070387 : Blo 1068616 1070387 := bstep (se 1 (by rfl) ⟨802790, by rfl⟩ : syracuseStep 1070387 = 1605581) B1605581
theorem B1070403 : Blo 1068616 1070403 := bstep (se 1 (by rfl) ⟨802802, by rfl⟩ : syracuseStep 1070403 = 1605605) B1605605
theorem B1070419 : Blo 1068616 1070419 := bstep (se 1 (by rfl) ⟨802814, by rfl⟩ : syracuseStep 1070419 = 1605629) B1605629
theorem B1070435 : Blo 1068616 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B1070451 : Blo 1068616 1070451 := bstep (se 1 (by rfl) ⟨802838, by rfl⟩ : syracuseStep 1070451 = 1605677) B1605677
theorem B1070467 : Blo 1068616 1070467 := bstep (se 1 (by rfl) ⟨802850, by rfl⟩ : syracuseStep 1070467 = 1605701) B1605701
theorem B15422861 : Blo 1068616 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B1070483 : Blo 1068616 1070483 := bstep (se 1 (by rfl) ⟨802862, by rfl⟩ : syracuseStep 1070483 = 1605725) B1605725
theorem B1070499 : Blo 1068616 1070499 := bstep (se 1 (by rfl) ⟨802874, by rfl⟩ : syracuseStep 1070499 = 1605749) B1605749
theorem B1070515 : Blo 1068616 1070515 := bstep (se 1 (by rfl) ⟨802886, by rfl⟩ : syracuseStep 1070515 = 1605773) B1605773
theorem B1070531 : Blo 1068616 1070531 := bstep (se 1 (by rfl) ⟨802898, by rfl⟩ : syracuseStep 1070531 = 1605797) B1605797
theorem B1070547 : Blo 1068616 1070547 := bstep (se 1 (by rfl) ⟨802910, by rfl⟩ : syracuseStep 1070547 = 1605821) B1605821
theorem B1070563 : Blo 1068616 1070563 := bstep (se 1 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 1070563 = 1605845) B1605845
theorem B1070579 : Blo 1068616 1070579 := bstep (se 1 (by rfl) ⟨802934, by rfl⟩ : syracuseStep 1070579 = 1605869) B1605869
theorem B1070595 : Blo 1068616 1070595 := bstep (se 1 (by rfl) ⟨802946, by rfl⟩ : syracuseStep 1070595 = 1605893) B1605893
theorem B1070611 : Blo 1068616 1070611 := bstep (se 1 (by rfl) ⟨802958, by rfl⟩ : syracuseStep 1070611 = 1605917) B1605917
theorem B1070627 : Blo 1068616 1070627 := bstep (se 1 (by rfl) ⟨802970, by rfl⟩ : syracuseStep 1070627 = 1605941) B1605941
theorem B1070643 : Blo 1068616 1070643 := bstep (se 1 (by rfl) ⟨802982, by rfl⟩ : syracuseStep 1070643 = 1605965) B1605965
theorem B1070659 : Blo 1068616 1070659 := bstep (se 1 (by rfl) ⟨802994, by rfl⟩ : syracuseStep 1070659 = 1605989) B1605989
theorem B1070675 : Blo 1068616 1070675 := bstep (se 1 (by rfl) ⟨803006, by rfl⟩ : syracuseStep 1070675 = 1606013) B1606013
theorem B1070691 : Blo 1068616 1070691 := bstep (se 1 (by rfl) ⟨803018, by rfl⟩ : syracuseStep 1070691 = 1606037) B1606037
theorem B1758835 : Blo 1068616 1758835 := bstep (se 1 (by rfl) ⟨1319126, by rfl⟩ : syracuseStep 1758835 = 2638253) B2638253
theorem B1070707 : Blo 1068616 1070707 := bstep (se 1 (by rfl) ⟨803030, by rfl⟩ : syracuseStep 1070707 = 1606061) B1606061
theorem B1070723 : Blo 1068616 1070723 := bstep (se 1 (by rfl) ⟨803042, by rfl⟩ : syracuseStep 1070723 = 1606085) B1606085
theorem B1070739 : Blo 1068616 1070739 := bstep (se 1 (by rfl) ⟨803054, by rfl⟩ : syracuseStep 1070739 = 1606109) B1606109
theorem B1070755 : Blo 1068616 1070755 := bstep (se 1 (by rfl) ⟨803066, by rfl⟩ : syracuseStep 1070755 = 1606133) B1606133
theorem B1070771 : Blo 1068616 1070771 := bstep (se 1 (by rfl) ⟨803078, by rfl⟩ : syracuseStep 1070771 = 1606157) B1606157
theorem B1070787 : Blo 1068616 1070787 := bstep (se 1 (by rfl) ⟨803090, by rfl⟩ : syracuseStep 1070787 = 1606181) B1606181
theorem B3430097 : Blo 1068616 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B1070803 : Blo 1068616 1070803 := bstep (se 1 (by rfl) ⟨803102, by rfl⟩ : syracuseStep 1070803 = 1606205) B1606205
theorem B1070819 : Blo 1068616 1070819 := bstep (se 1 (by rfl) ⟨803114, by rfl⟩ : syracuseStep 1070819 = 1606229) B1606229
theorem B1070835 : Blo 1068616 1070835 := bstep (se 1 (by rfl) ⟨803126, by rfl⟩ : syracuseStep 1070835 = 1606253) B1606253
theorem B1070851 : Blo 1068616 1070851 := bstep (se 1 (by rfl) ⟨803138, by rfl⟩ : syracuseStep 1070851 = 1606277) B1606277
theorem B1070867 : Blo 1068616 1070867 := bstep (se 1 (by rfl) ⟨803150, by rfl⟩ : syracuseStep 1070867 = 1606301) B1606301
theorem B1070883 : Blo 1068616 1070883 := bstep (se 1 (by rfl) ⟨803162, by rfl⟩ : syracuseStep 1070883 = 1606325) B1606325
theorem B3856177 : Blo 1068616 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B1070899 : Blo 1068616 1070899 := bstep (se 1 (by rfl) ⟨803174, by rfl⟩ : syracuseStep 1070899 = 1606349) B1606349
theorem B2283331 : Blo 1068616 2283331 := bstep (se 1 (by rfl) ⟨1712498, by rfl⟩ : syracuseStep 2283331 = 3424997) B3424997
theorem B1070915 : Blo 1068616 1070915 := bstep (se 1 (by rfl) ⟨803186, by rfl⟩ : syracuseStep 1070915 = 1606373) B1606373
theorem B1070931 : Blo 1068616 1070931 := bstep (se 1 (by rfl) ⟨803198, by rfl⟩ : syracuseStep 1070931 = 1606397) B1606397
theorem B1070947 : Blo 1068616 1070947 := bstep (se 1 (by rfl) ⟨803210, by rfl⟩ : syracuseStep 1070947 = 1606421) B1606421
theorem B5429105 : Blo 1068616 5429105 := bstep (se 2 (by rfl) ⟨2035914, by rfl⟩ : syracuseStep 5429105 = 4071829) B4071829
theorem B1070963 : Blo 1068616 1070963 := bstep (se 1 (by rfl) ⟨803222, by rfl⟩ : syracuseStep 1070963 = 1606445) B1606445
theorem B1070979 : Blo 1068616 1070979 := bstep (se 1 (by rfl) ⟨803234, by rfl⟩ : syracuseStep 1070979 = 1606469) B1606469
theorem B1070995 : Blo 1068616 1070995 := bstep (se 1 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 1070995 = 1606493) B1606493
theorem B1071011 : Blo 1068616 1071011 := bstep (se 1 (by rfl) ⟨803258, by rfl⟩ : syracuseStep 1071011 = 1606517) B1606517
theorem B1071027 : Blo 1068616 1071027 := bstep (se 1 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 1071027 = 1606541) B1606541
theorem B1071043 : Blo 1068616 1071043 := bstep (se 1 (by rfl) ⟨803282, by rfl⟩ : syracuseStep 1071043 = 1606565) B1606565
theorem B35739589 : Blo 1068616 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B1071059 : Blo 1068616 1071059 := bstep (se 1 (by rfl) ⟨803294, by rfl⟩ : syracuseStep 1071059 = 1606589) B1606589
theorem B1071075 : Blo 1068616 1071075 := bstep (se 1 (by rfl) ⟨803306, by rfl⟩ : syracuseStep 1071075 = 1606613) B1606613
theorem B1071091 : Blo 1068616 1071091 := bstep (se 1 (by rfl) ⟨803318, by rfl⟩ : syracuseStep 1071091 = 1606637) B1606637
theorem B1071107 : Blo 1068616 1071107 := bstep (se 1 (by rfl) ⟨803330, by rfl⟩ : syracuseStep 1071107 = 1606661) B1606661
theorem B2709521 : Blo 1068616 2709521 := bstep (se 2 (by rfl) ⟨1016070, by rfl⟩ : syracuseStep 2709521 = 2032141) B2032141
theorem B1071123 : Blo 1068616 1071123 := bstep (se 1 (by rfl) ⟨803342, by rfl⟩ : syracuseStep 1071123 = 1606685) B1606685
theorem B1071139 : Blo 1068616 1071139 := bstep (se 1 (by rfl) ⟨803354, by rfl⟩ : syracuseStep 1071139 = 1606709) B1606709
theorem B1071155 : Blo 1068616 1071155 := bstep (se 1 (by rfl) ⟨803366, by rfl⟩ : syracuseStep 1071155 = 1606733) B1606733
theorem B2709571 : Blo 1068616 2709571 := bstep (se 1 (by rfl) ⟨2032178, by rfl⟩ : syracuseStep 2709571 = 4064357) B4064357
theorem B1071171 : Blo 1068616 1071171 := bstep (se 1 (by rfl) ⟨803378, by rfl⟩ : syracuseStep 1071171 = 1606757) B1606757
theorem B1071187 : Blo 1068616 1071187 := bstep (se 1 (by rfl) ⟨803390, by rfl⟩ : syracuseStep 1071187 = 1606781) B1606781
theorem B1071203 : Blo 1068616 1071203 := bstep (se 1 (by rfl) ⟨803402, by rfl⟩ : syracuseStep 1071203 = 1606805) B1606805
theorem B1071219 : Blo 1068616 1071219 := bstep (se 1 (by rfl) ⟨803414, by rfl⟩ : syracuseStep 1071219 = 1606829) B1606829
theorem B1071235 : Blo 1068616 1071235 := bstep (se 1 (by rfl) ⟨803426, by rfl⟩ : syracuseStep 1071235 = 1606853) B1606853
theorem B1202323 : Blo 1068616 1202323 := bstep (se 1 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 1202323 = 1803485) B1803485
theorem B1071251 : Blo 1068616 1071251 := bstep (se 1 (by rfl) ⟨803438, by rfl⟩ : syracuseStep 1071251 = 1606877) B1606877
theorem B1071267 : Blo 1068616 1071267 := bstep (se 1 (by rfl) ⟨803450, by rfl⟩ : syracuseStep 1071267 = 1606901) B1606901
theorem B1071283 : Blo 1068616 1071283 := bstep (se 1 (by rfl) ⟨803462, by rfl⟩ : syracuseStep 1071283 = 1606925) B1606925
theorem B1071299 : Blo 1068616 1071299 := bstep (se 1 (by rfl) ⟨803474, by rfl⟩ : syracuseStep 1071299 = 1606949) B1606949
theorem B2709713 : Blo 1068616 2709713 := bstep (se 2 (by rfl) ⟨1016142, by rfl⟩ : syracuseStep 2709713 = 2032285) B2032285
theorem B1071315 : Blo 1068616 1071315 := bstep (se 1 (by rfl) ⟨803486, by rfl⟩ : syracuseStep 1071315 = 1606973) B1606973
theorem B1071331 : Blo 1068616 1071331 := bstep (se 1 (by rfl) ⟨803498, by rfl⟩ : syracuseStep 1071331 = 1606997) B1606997
theorem B1071347 : Blo 1068616 1071347 := bstep (se 1 (by rfl) ⟨803510, by rfl⟩ : syracuseStep 1071347 = 1607021) B1607021
theorem B1071363 : Blo 1068616 1071363 := bstep (se 1 (by rfl) ⟨803522, by rfl⟩ : syracuseStep 1071363 = 1607045) B1607045
theorem B1071379 : Blo 1068616 1071379 := bstep (se 1 (by rfl) ⟨803534, by rfl⟩ : syracuseStep 1071379 = 1607069) B1607069
theorem B1202467 : Blo 1068616 1202467 := bstep (se 1 (by rfl) ⟨901850, by rfl⟩ : syracuseStep 1202467 = 1803701) B1803701
theorem B1071395 : Blo 1068616 1071395 := bstep (se 1 (by rfl) ⟨803546, by rfl⟩ : syracuseStep 1071395 = 1607093) B1607093
theorem B1071411 : Blo 1068616 1071411 := bstep (se 1 (by rfl) ⟨803558, by rfl⟩ : syracuseStep 1071411 = 1607117) B1607117
theorem B1071427 : Blo 1068616 1071427 := bstep (se 1 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 1071427 = 1607141) B1607141
theorem B1071443 : Blo 1068616 1071443 := bstep (se 1 (by rfl) ⟨803582, by rfl⟩ : syracuseStep 1071443 = 1607165) B1607165
theorem B1071459 : Blo 1068616 1071459 := bstep (se 1 (by rfl) ⟨803594, by rfl⟩ : syracuseStep 1071459 = 1607189) B1607189
theorem B1071475 : Blo 1068616 1071475 := bstep (se 1 (by rfl) ⟨803606, by rfl⟩ : syracuseStep 1071475 = 1607213) B1607213
theorem B1071491 : Blo 1068616 1071491 := bstep (se 1 (by rfl) ⟨803618, by rfl⟩ : syracuseStep 1071491 = 1607237) B1607237
theorem B1071507 : Blo 1068616 1071507 := bstep (se 1 (by rfl) ⟨803630, by rfl⟩ : syracuseStep 1071507 = 1607261) B1607261
theorem B1071523 : Blo 1068616 1071523 := bstep (se 1 (by rfl) ⟨803642, by rfl⟩ : syracuseStep 1071523 = 1607285) B1607285
theorem B1202611 : Blo 1068616 1202611 := bstep (se 1 (by rfl) ⟨901958, by rfl⟩ : syracuseStep 1202611 = 1803917) B1803917
theorem B1071539 : Blo 1068616 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B1071555 : Blo 1068616 1071555 := bstep (se 1 (by rfl) ⟨803666, by rfl⟩ : syracuseStep 1071555 = 1607333) B1607333
theorem B5790149 : Blo 1068616 5790149 := bstep (se 4 (by rfl) ⟨542826, by rfl⟩ : syracuseStep 5790149 = 1085653) B1085653
theorem B1071571 : Blo 1068616 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B1071587 : Blo 1068616 1071587 := bstep (se 1 (by rfl) ⟨803690, by rfl⟩ : syracuseStep 1071587 = 1607381) B1607381
theorem B1071603 : Blo 1068616 1071603 := bstep (se 1 (by rfl) ⟨803702, by rfl⟩ : syracuseStep 1071603 = 1607405) B1607405
theorem B1628675 : Blo 1068616 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B1071619 : Blo 1068616 1071619 := bstep (se 1 (by rfl) ⟨803714, by rfl⟩ : syracuseStep 1071619 = 1607429) B1607429
theorem B1071635 : Blo 1068616 1071635 := bstep (se 1 (by rfl) ⟨803726, by rfl⟩ : syracuseStep 1071635 = 1607453) B1607453
theorem B1071651 : Blo 1068616 1071651 := bstep (se 1 (by rfl) ⟨803738, by rfl⟩ : syracuseStep 1071651 = 1607477) B1607477
theorem B1071667 : Blo 1068616 1071667 := bstep (se 1 (by rfl) ⟨803750, by rfl⟩ : syracuseStep 1071667 = 1607501) B1607501
theorem B1202755 : Blo 1068616 1202755 := bstep (se 1 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 1202755 = 1804133) B1804133
theorem B1071683 : Blo 1068616 1071683 := bstep (se 1 (by rfl) ⟨803762, by rfl⟩ : syracuseStep 1071683 = 1607525) B1607525
theorem B3430993 : Blo 1068616 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B1071699 : Blo 1068616 1071699 := bstep (se 1 (by rfl) ⟨803774, by rfl⟩ : syracuseStep 1071699 = 1607549) B1607549
theorem B1071715 : Blo 1068616 1071715 := bstep (se 1 (by rfl) ⟨803786, by rfl⟩ : syracuseStep 1071715 = 1607573) B1607573
theorem B1071731 : Blo 1068616 1071731 := bstep (se 1 (by rfl) ⟨803798, by rfl⟩ : syracuseStep 1071731 = 1607597) B1607597
theorem B1071747 : Blo 1068616 1071747 := bstep (se 1 (by rfl) ⟨803810, by rfl⟩ : syracuseStep 1071747 = 1607621) B1607621
theorem B1071763 : Blo 1068616 1071763 := bstep (se 1 (by rfl) ⟨803822, by rfl⟩ : syracuseStep 1071763 = 1607645) B1607645
theorem B1071779 : Blo 1068616 1071779 := bstep (se 1 (by rfl) ⟨803834, by rfl⟩ : syracuseStep 1071779 = 1607669) B1607669
theorem B1071795 : Blo 1068616 1071795 := bstep (se 1 (by rfl) ⟨803846, by rfl⟩ : syracuseStep 1071795 = 1607693) B1607693
theorem B1071811 : Blo 1068616 1071811 := bstep (se 1 (by rfl) ⟨803858, by rfl⟩ : syracuseStep 1071811 = 1607717) B1607717
theorem B1202899 : Blo 1068616 1202899 := bstep (se 1 (by rfl) ⟨902174, by rfl⟩ : syracuseStep 1202899 = 1804349) B1804349
theorem B1071827 : Blo 1068616 1071827 := bstep (se 1 (by rfl) ⟨803870, by rfl⟩ : syracuseStep 1071827 = 1607741) B1607741
theorem B1071843 : Blo 1068616 1071843 := bstep (se 1 (by rfl) ⟨803882, by rfl⟩ : syracuseStep 1071843 = 1607765) B1607765
theorem B1071859 : Blo 1068616 1071859 := bstep (se 1 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 1071859 = 1607789) B1607789
theorem B1071875 : Blo 1068616 1071875 := bstep (se 1 (by rfl) ⟨803906, by rfl⟩ : syracuseStep 1071875 = 1607813) B1607813
theorem B1071891 : Blo 1068616 1071891 := bstep (se 1 (by rfl) ⟨803918, by rfl⟩ : syracuseStep 1071891 = 1607837) B1607837
theorem B1071907 : Blo 1068616 1071907 := bstep (se 1 (by rfl) ⟨803930, by rfl⟩ : syracuseStep 1071907 = 1607861) B1607861
theorem B1071923 : Blo 1068616 1071923 := bstep (se 1 (by rfl) ⟨803942, by rfl⟩ : syracuseStep 1071923 = 1607885) B1607885
theorem B1071939 : Blo 1068616 1071939 := bstep (se 1 (by rfl) ⟨803954, by rfl⟩ : syracuseStep 1071939 = 1607909) B1607909
theorem B1071955 : Blo 1068616 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B1203043 : Blo 1068616 1203043 := bstep (se 1 (by rfl) ⟨902282, by rfl⟩ : syracuseStep 1203043 = 1804565) B1804565
theorem B1071971 : Blo 1068616 1071971 := bstep (se 1 (by rfl) ⟨803978, by rfl⟩ : syracuseStep 1071971 = 1607957) B1607957
theorem B1071987 : Blo 1068616 1071987 := bstep (se 1 (by rfl) ⟨803990, by rfl⟩ : syracuseStep 1071987 = 1607981) B1607981
theorem B1072003 : Blo 1068616 1072003 := bstep (se 1 (by rfl) ⟨804002, by rfl⟩ : syracuseStep 1072003 = 1608005) B1608005
theorem B1072019 : Blo 1068616 1072019 := bstep (se 1 (by rfl) ⟨804014, by rfl⟩ : syracuseStep 1072019 = 1608029) B1608029
theorem B4578211 : Blo 1068616 4578211 := bstep (se 1 (by rfl) ⟨3433658, by rfl⟩ : syracuseStep 4578211 = 6867317) B6867317
theorem B1072035 : Blo 1068616 1072035 := bstep (se 1 (by rfl) ⟨804026, by rfl⟩ : syracuseStep 1072035 = 1608053) B1608053
theorem B1072051 : Blo 1068616 1072051 := bstep (se 1 (by rfl) ⟨804038, by rfl⟩ : syracuseStep 1072051 = 1608077) B1608077
theorem B1072067 : Blo 1068616 1072067 := bstep (se 1 (by rfl) ⟨804050, by rfl⟩ : syracuseStep 1072067 = 1608101) B1608101
theorem B1072083 : Blo 1068616 1072083 := bstep (se 1 (by rfl) ⟨804062, by rfl⟩ : syracuseStep 1072083 = 1608125) B1608125
theorem B1072099 : Blo 1068616 1072099 := bstep (se 1 (by rfl) ⟨804074, by rfl⟩ : syracuseStep 1072099 = 1608149) B1608149
theorem B1203187 : Blo 1068616 1203187 := bstep (se 1 (by rfl) ⟨902390, by rfl⟩ : syracuseStep 1203187 = 1804781) B1804781
theorem B1072115 : Blo 1068616 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B1072131 : Blo 1068616 1072131 := bstep (se 1 (by rfl) ⟨804098, by rfl⟩ : syracuseStep 1072131 = 1608197) B1608197
theorem B2284561 : Blo 1068616 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B1072147 : Blo 1068616 1072147 := bstep (se 1 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 1072147 = 1608221) B1608221
theorem B1072163 : Blo 1068616 1072163 := bstep (se 1 (by rfl) ⟨804122, by rfl⟩ : syracuseStep 1072163 = 1608245) B1608245
theorem B1072179 : Blo 1068616 1072179 := bstep (se 1 (by rfl) ⟨804134, by rfl⟩ : syracuseStep 1072179 = 1608269) B1608269
theorem B1072195 : Blo 1068616 1072195 := bstep (se 1 (by rfl) ⟨804146, by rfl⟩ : syracuseStep 1072195 = 1608293) B1608293
theorem B1072211 : Blo 1068616 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1072227 : Blo 1068616 1072227 := bstep (se 1 (by rfl) ⟨804170, by rfl⟩ : syracuseStep 1072227 = 1608341) B1608341
theorem B1072243 : Blo 1068616 1072243 := bstep (se 1 (by rfl) ⟨804182, by rfl⟩ : syracuseStep 1072243 = 1608365) B1608365
theorem B1203331 : Blo 1068616 1203331 := bstep (se 1 (by rfl) ⟨902498, by rfl⟩ : syracuseStep 1203331 = 1804997) B1804997
theorem B1072259 : Blo 1068616 1072259 := bstep (se 1 (by rfl) ⟨804194, by rfl⟩ : syracuseStep 1072259 = 1608389) B1608389
theorem B24697997 : Blo 1068616 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B14670989 : Blo 1068616 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B1072275 : Blo 1068616 1072275 := bstep (se 1 (by rfl) ⟨804206, by rfl⟩ : syracuseStep 1072275 = 1608413) B1608413
theorem B1072291 : Blo 1068616 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B2710705 : Blo 1068616 2710705 := bstep (se 2 (by rfl) ⟨1016514, by rfl⟩ : syracuseStep 2710705 = 2033029) B2033029
theorem B1072307 : Blo 1068616 1072307 := bstep (se 1 (by rfl) ⟨804230, by rfl⟩ : syracuseStep 1072307 = 1608461) B1608461
theorem B1072323 : Blo 1068616 1072323 := bstep (se 1 (by rfl) ⟨804242, by rfl⟩ : syracuseStep 1072323 = 1608485) B1608485
theorem B14277829 : Blo 1068616 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1072339 : Blo 1068616 1072339 := bstep (se 1 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 1072339 = 1608509) B1608509
theorem B1072355 : Blo 1068616 1072355 := bstep (se 1 (by rfl) ⟨804266, by rfl⟩ : syracuseStep 1072355 = 1608533) B1608533
theorem B1072371 : Blo 1068616 1072371 := bstep (se 1 (by rfl) ⟨804278, by rfl⟩ : syracuseStep 1072371 = 1608557) B1608557
theorem B1072387 : Blo 1068616 1072387 := bstep (se 1 (by rfl) ⟨804290, by rfl⟩ : syracuseStep 1072387 = 1608581) B1608581
theorem B1203475 : Blo 1068616 1203475 := bstep (se 1 (by rfl) ⟨902606, by rfl⟩ : syracuseStep 1203475 = 1805213) B1805213
theorem B1072403 : Blo 1068616 1072403 := bstep (se 1 (by rfl) ⟨804302, by rfl⟩ : syracuseStep 1072403 = 1608605) B1608605
theorem B1072419 : Blo 1068616 1072419 := bstep (se 1 (by rfl) ⟨804314, by rfl⟩ : syracuseStep 1072419 = 1608629) B1608629
theorem B1072435 : Blo 1068616 1072435 := bstep (se 1 (by rfl) ⟨804326, by rfl⟩ : syracuseStep 1072435 = 1608653) B1608653
theorem B1072451 : Blo 1068616 1072451 := bstep (se 1 (by rfl) ⟨804338, by rfl⟩ : syracuseStep 1072451 = 1608677) B1608677
theorem B1072467 : Blo 1068616 1072467 := bstep (se 1 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 1072467 = 1608701) B1608701
theorem B1072483 : Blo 1068616 1072483 := bstep (se 1 (by rfl) ⟨804362, by rfl⟩ : syracuseStep 1072483 = 1608725) B1608725
theorem B1072499 : Blo 1068616 1072499 := bstep (se 1 (by rfl) ⟨804374, by rfl⟩ : syracuseStep 1072499 = 1608749) B1608749
theorem B1072515 : Blo 1068616 1072515 := bstep (se 1 (by rfl) ⟨804386, by rfl⟩ : syracuseStep 1072515 = 1608773) B1608773
theorem B1072531 : Blo 1068616 1072531 := bstep (se 1 (by rfl) ⟨804398, by rfl⟩ : syracuseStep 1072531 = 1608797) B1608797
theorem B1203619 : Blo 1068616 1203619 := bstep (se 1 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 1203619 = 1805429) B1805429
theorem B1072547 : Blo 1068616 1072547 := bstep (se 1 (by rfl) ⟨804410, by rfl⟩ : syracuseStep 1072547 = 1608821) B1608821
theorem B1072563 : Blo 1068616 1072563 := bstep (se 1 (by rfl) ⟨804422, by rfl⟩ : syracuseStep 1072563 = 1608845) B1608845
theorem B2710979 : Blo 1068616 2710979 := bstep (se 1 (by rfl) ⟨2033234, by rfl⟩ : syracuseStep 2710979 = 4066469) B4066469
theorem B1072579 : Blo 1068616 1072579 := bstep (se 1 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 1072579 = 1608869) B1608869
theorem B1072595 : Blo 1068616 1072595 := bstep (se 1 (by rfl) ⟨804446, by rfl⟩ : syracuseStep 1072595 = 1608893) B1608893
theorem B1072611 : Blo 1068616 1072611 := bstep (se 1 (by rfl) ⟨804458, by rfl⟩ : syracuseStep 1072611 = 1608917) B1608917
theorem B1203763 : Blo 1068616 1203763 := bstep (se 1 (by rfl) ⟨902822, by rfl⟩ : syracuseStep 1203763 = 1805645) B1805645
theorem B2711171 : Blo 1068616 2711171 := bstep (se 1 (by rfl) ⟨2033378, by rfl⟩ : syracuseStep 2711171 = 4066757) B4066757
theorem B6086285 : Blo 1068616 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B1203907 : Blo 1068616 1203907 := bstep (se 1 (by rfl) ⟨902930, by rfl⟩ : syracuseStep 1203907 = 1805861) B1805861
theorem B2285347 : Blo 1068616 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B3727171 : Blo 1068616 3727171 := bstep (se 1 (by rfl) ⟨2795378, by rfl⟩ : syracuseStep 3727171 = 5590757) B5590757
theorem B1204051 : Blo 1068616 1204051 := bstep (se 1 (by rfl) ⟨903038, by rfl⟩ : syracuseStep 1204051 = 1806077) B1806077
theorem B5791621 : Blo 1068616 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B1204195 : Blo 1068616 1204195 := bstep (se 1 (by rfl) ⟨903146, by rfl⟩ : syracuseStep 1204195 = 1806293) B1806293
theorem B3432557 : Blo 1068616 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B1204339 : Blo 1068616 1204339 := bstep (se 1 (by rfl) ⟨903254, by rfl⟩ : syracuseStep 1204339 = 1806509) B1806509
theorem B27779213 : Blo 1068616 27779213 := bstep (se 3 (by rfl) ⟨5208602, by rfl⟩ : syracuseStep 27779213 = 10417205) B10417205
theorem B13000931 : Blo 1068616 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B14082275 : Blo 1068616 14082275 := bstep (se 1 (by rfl) ⟨10561706, by rfl⟩ : syracuseStep 14082275 = 21123413) B21123413
theorem B1204483 : Blo 1068616 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B1204627 : Blo 1068616 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B5136803 : Blo 1068616 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B2286065 : Blo 1068616 2286065 := bstep (se 2 (by rfl) ⟨857274, by rfl⟩ : syracuseStep 2286065 = 1714549) B1714549
theorem B1204771 : Blo 1068616 1204771 := bstep (se 1 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 1204771 = 1807157) B1807157
theorem B2712113 : Blo 1068616 2712113 := bstep (se 2 (by rfl) ⟨1017042, by rfl⟩ : syracuseStep 2712113 = 2034085) B2034085
theorem B2712163 : Blo 1068616 2712163 := bstep (se 1 (by rfl) ⟨2034122, by rfl⟩ : syracuseStep 2712163 = 4068245) B4068245
theorem B1204915 : Blo 1068616 1204915 := bstep (se 1 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 1204915 = 1807373) B1807373
theorem B2712305 : Blo 1068616 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B3859235 : Blo 1068616 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B1205059 : Blo 1068616 1205059 := bstep (se 1 (by rfl) ⟨903794, by rfl⟩ : syracuseStep 1205059 = 1807589) B1807589
theorem B1205203 : Blo 1068616 1205203 := bstep (se 1 (by rfl) ⟨903902, by rfl⟩ : syracuseStep 1205203 = 1807805) B1807805
theorem B2286577 : Blo 1068616 2286577 := bstep (se 2 (by rfl) ⟨857466, by rfl⟩ : syracuseStep 2286577 = 1714933) B1714933
theorem B1205347 : Blo 1068616 1205347 := bstep (se 1 (by rfl) ⟨904010, by rfl⟩ : syracuseStep 1205347 = 1808021) B1808021
theorem B7726193 : Blo 1068616 7726193 := bstep (se 2 (by rfl) ⟨2897322, by rfl⟩ : syracuseStep 7726193 = 5794645) B5794645
theorem B5137613 : Blo 1068616 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B1205491 : Blo 1068616 1205491 := bstep (se 1 (by rfl) ⟨904118, by rfl⟩ : syracuseStep 1205491 = 1808237) B1808237
theorem B1828099 : Blo 1068616 1828099 := bstep (se 1 (by rfl) ⟨1371074, by rfl⟩ : syracuseStep 1828099 = 2742149) B2742149
theorem B4580657 : Blo 1068616 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1205635 : Blo 1068616 1205635 := bstep (se 1 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 1205635 = 1808453) B1808453
theorem B1926641 : Blo 1068616 1926641 := bstep (se 2 (by rfl) ⟨722490, by rfl⟩ : syracuseStep 1926641 = 1444981) B1444981
theorem B8349169 : Blo 1068616 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B1205779 : Blo 1068616 1205779 := bstep (se 1 (by rfl) ⟨904334, by rfl⟩ : syracuseStep 1205779 = 1808669) B1808669
theorem B6514289 : Blo 1068616 6514289 := bstep (se 2 (by rfl) ⟨2442858, by rfl⟩ : syracuseStep 6514289 = 4885717) B4885717
theorem B1205923 : Blo 1068616 1205923 := bstep (se 1 (by rfl) ⟨904442, by rfl⟩ : syracuseStep 1205923 = 1808885) B1808885
theorem B2713297 : Blo 1068616 2713297 := bstep (se 2 (by rfl) ⟨1017486, by rfl⟩ : syracuseStep 2713297 = 2034973) B2034973
theorem B1206067 : Blo 1068616 1206067 := bstep (se 1 (by rfl) ⟨904550, by rfl⟩ : syracuseStep 1206067 = 1809101) B1809101
theorem B6088517 : Blo 1068616 6088517 := bstep (se 4 (by rfl) ⟨570798, by rfl⟩ : syracuseStep 6088517 = 1141597) B1141597
theorem B1206211 : Blo 1068616 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B2713571 : Blo 1068616 2713571 := bstep (se 1 (by rfl) ⟨2035178, by rfl⟩ : syracuseStep 2713571 = 4070357) B4070357
theorem B5138417 : Blo 1068616 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B5793869 : Blo 1068616 5793869 := bstep (se 3 (by rfl) ⟨1086350, by rfl⟩ : syracuseStep 5793869 = 2172701) B2172701
theorem B1206355 : Blo 1068616 1206355 := bstep (se 1 (by rfl) ⟨904766, by rfl⟩ : syracuseStep 1206355 = 1809533) B1809533
theorem B16509041 : Blo 1068616 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B2713763 : Blo 1068616 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B1206499 : Blo 1068616 1206499 := bstep (se 1 (by rfl) ⟨904874, by rfl⟩ : syracuseStep 1206499 = 1809749) B1809749
theorem B1206643 : Blo 1068616 1206643 := bstep (se 1 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 1206643 = 1809965) B1809965
theorem B1141187 : Blo 1068616 1141187 := bstep (se 1 (by rfl) ⟨855890, by rfl⟩ : syracuseStep 1141187 = 1711781) B1711781
theorem B2288081 : Blo 1068616 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B6089201 : Blo 1068616 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B3435043 : Blo 1068616 3435043 := bstep (se 1 (by rfl) ⟨2576282, by rfl⟩ : syracuseStep 3435043 = 5152565) B5152565
theorem B9136739 : Blo 1068616 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B3435185 : Blo 1068616 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B8121059 : Blo 1068616 8121059 := bstep (se 1 (by rfl) ⟨6090794, by rfl⟩ : syracuseStep 8121059 = 12181589) B12181589
theorem B3435299 : Blo 1068616 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B2288483 : Blo 1068616 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B2714705 : Blo 1068616 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B2714755 : Blo 1068616 2714755 := bstep (se 1 (by rfl) ⟨2036066, by rfl⟩ : syracuseStep 2714755 = 4072133) B4072133
theorem B1141939 : Blo 1068616 1141939 := bstep (se 1 (by rfl) ⟨856454, by rfl⟩ : syracuseStep 1141939 = 1712909) B1712909
theorem B13200653 : Blo 1068616 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B2714897 : Blo 1068616 2714897 := bstep (se 2 (by rfl) ⟨1018086, by rfl⟩ : syracuseStep 2714897 = 2036173) B2036173
theorem B1142195 : Blo 1068616 1142195 := bstep (se 1 (by rfl) ⟨856646, by rfl⟩ : syracuseStep 1142195 = 1713293) B1713293
theorem B2289379 : Blo 1068616 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B3862349 : Blo 1068616 3862349 := bstep (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) B1448381
theorem B6090659 : Blo 1068616 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B5140493 : Blo 1068616 5140493 := bstep (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) B1927685
theorem B1142947 : Blo 1068616 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B3043565 : Blo 1068616 3043565 := bstep (se 3 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 3043565 = 1141337) B1141337
theorem B3043757 : Blo 1068616 3043757 := bstep (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) B1141409
theorem B18805445 : Blo 1068616 18805445 := bstep (se 4 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 18805445 = 3526021) B3526021
theorem B5796593 : Blo 1068616 5796593 := bstep (se 2 (by rfl) ⟨2173722, by rfl⟩ : syracuseStep 5796593 = 4347445) B4347445
theorem B4059953 : Blo 1068616 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B5796721 : Blo 1068616 5796721 := bstep (se 2 (by rfl) ⟨2173770, by rfl⟩ : syracuseStep 5796721 = 4347541) B4347541
theorem B2290609 : Blo 1068616 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B1831889 : Blo 1068616 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B3667021 : Blo 1068616 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B9270413 : Blo 1068616 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B2028739 : Blo 1068616 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B4879601 : Blo 1068616 4879601 := bstep (se 2 (by rfl) ⟨1829850, by rfl⟩ : syracuseStep 4879601 = 3659701) B3659701
theorem B1602929 : Blo 1068616 1602929 := bstep (se 2 (by rfl) ⟨601098, by rfl⟩ : syracuseStep 1602929 = 1202197) B1202197
theorem B1602947 : Blo 1068616 1602947 := bstep (se 1 (by rfl) ⟨1202210, by rfl⟩ : syracuseStep 1602947 = 2404421) B2404421
theorem B3044749 : Blo 1068616 3044749 := bstep (se 3 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 3044749 = 1141781) B1141781
theorem B1144211 : Blo 1068616 1144211 := bstep (se 1 (by rfl) ⟨858158, by rfl⟩ : syracuseStep 1144211 = 1716317) B1716317
theorem B1602977 : Blo 1068616 1602977 := bstep (se 2 (by rfl) ⟨601116, by rfl⟩ : syracuseStep 1602977 = 1202233) B1202233
theorem B1602995 : Blo 1068616 1602995 := bstep (se 1 (by rfl) ⟨1202246, by rfl⟩ : syracuseStep 1602995 = 2404493) B2404493
theorem B1603025 : Blo 1068616 1603025 := bstep (se 2 (by rfl) ⟨601134, by rfl⟩ : syracuseStep 1603025 = 1202269) B1202269
theorem B1603043 : Blo 1068616 1603043 := bstep (se 1 (by rfl) ⟨1202282, by rfl⟩ : syracuseStep 1603043 = 2404565) B2404565
theorem B1603073 : Blo 1068616 1603073 := bstep (se 2 (by rfl) ⟨601152, by rfl⟩ : syracuseStep 1603073 = 1202305) B1202305
theorem B2749969 : Blo 1068616 2749969 := bstep (se 2 (by rfl) ⟨1031238, by rfl⟩ : syracuseStep 2749969 = 2062477) B2062477
theorem B1603091 : Blo 1068616 1603091 := bstep (se 1 (by rfl) ⟨1202318, by rfl⟩ : syracuseStep 1603091 = 2404637) B2404637
theorem B1603121 : Blo 1068616 1603121 := bstep (se 2 (by rfl) ⟨601170, by rfl⟩ : syracuseStep 1603121 = 1202341) B1202341
theorem B1603139 : Blo 1068616 1603139 := bstep (se 1 (by rfl) ⟨1202354, by rfl⟩ : syracuseStep 1603139 = 2404709) B2404709
theorem B1603169 : Blo 1068616 1603169 := bstep (se 2 (by rfl) ⟨601188, by rfl⟩ : syracuseStep 1603169 = 1202377) B1202377
theorem B1603187 : Blo 1068616 1603187 := bstep (se 1 (by rfl) ⟨1202390, by rfl⟩ : syracuseStep 1603187 = 2404781) B2404781
theorem B2029187 : Blo 1068616 2029187 := bstep (se 1 (by rfl) ⟨1521890, by rfl⟩ : syracuseStep 2029187 = 3043781) B3043781
theorem B1603217 : Blo 1068616 1603217 := bstep (se 2 (by rfl) ⟨601206, by rfl⟩ : syracuseStep 1603217 = 1202413) B1202413
theorem B1603235 : Blo 1068616 1603235 := bstep (se 1 (by rfl) ⟨1202426, by rfl⟩ : syracuseStep 1603235 = 2404853) B2404853
theorem B1603265 : Blo 1068616 1603265 := bstep (se 2 (by rfl) ⟨601224, by rfl⟩ : syracuseStep 1603265 = 1202449) B1202449
theorem B1603283 : Blo 1068616 1603283 := bstep (se 1 (by rfl) ⟨1202462, by rfl⟩ : syracuseStep 1603283 = 2404925) B2404925
theorem B1603313 : Blo 1068616 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B1603331 : Blo 1068616 1603331 := bstep (se 1 (by rfl) ⟨1202498, by rfl⟩ : syracuseStep 1603331 = 2404997) B2404997
theorem B1603361 : Blo 1068616 1603361 := bstep (se 2 (by rfl) ⟨601260, by rfl⟩ : syracuseStep 1603361 = 1202521) B1202521
theorem B1603379 : Blo 1068616 1603379 := bstep (se 1 (by rfl) ⟨1202534, by rfl⟩ : syracuseStep 1603379 = 2405069) B2405069
theorem B1603409 : Blo 1068616 1603409 := bstep (se 2 (by rfl) ⟨601278, by rfl⟩ : syracuseStep 1603409 = 1202557) B1202557
theorem B1603427 : Blo 1068616 1603427 := bstep (se 1 (by rfl) ⟨1202570, by rfl⟩ : syracuseStep 1603427 = 2405141) B2405141
theorem B1603457 : Blo 1068616 1603457 := bstep (se 2 (by rfl) ⟨601296, by rfl⟩ : syracuseStep 1603457 = 1202593) B1202593
theorem B1603475 : Blo 1068616 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B2029475 : Blo 1068616 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B1603505 : Blo 1068616 1603505 := bstep (se 2 (by rfl) ⟨601314, by rfl⟩ : syracuseStep 1603505 = 1202629) B1202629
theorem B1603523 : Blo 1068616 1603523 := bstep (se 1 (by rfl) ⟨1202642, by rfl⟩ : syracuseStep 1603523 = 2405285) B2405285
theorem B1832915 : Blo 1068616 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B1603553 : Blo 1068616 1603553 := bstep (se 2 (by rfl) ⟨601332, by rfl⟩ : syracuseStep 1603553 = 1202665) B1202665
theorem B1603571 : Blo 1068616 1603571 := bstep (se 1 (by rfl) ⟨1202678, by rfl⟩ : syracuseStep 1603571 = 2405357) B2405357
theorem B1603601 : Blo 1068616 1603601 := bstep (se 2 (by rfl) ⟨601350, by rfl⟩ : syracuseStep 1603601 = 1202701) B1202701
theorem B1603619 : Blo 1068616 1603619 := bstep (se 1 (by rfl) ⟨1202714, by rfl⟩ : syracuseStep 1603619 = 2405429) B2405429
theorem B1603649 : Blo 1068616 1603649 := bstep (se 2 (by rfl) ⟨601368, by rfl⟩ : syracuseStep 1603649 = 1202737) B1202737
theorem B1603667 : Blo 1068616 1603667 := bstep (se 1 (by rfl) ⟨1202750, by rfl⟩ : syracuseStep 1603667 = 2405501) B2405501
theorem B1603697 : Blo 1068616 1603697 := bstep (se 2 (by rfl) ⟨601386, by rfl⟩ : syracuseStep 1603697 = 1202773) B1202773
theorem B1603715 : Blo 1068616 1603715 := bstep (se 1 (by rfl) ⟨1202786, by rfl⟩ : syracuseStep 1603715 = 2405573) B2405573
theorem B1144963 : Blo 1068616 1144963 := bstep (se 1 (by rfl) ⟨858722, by rfl⟩ : syracuseStep 1144963 = 1717445) B1717445
theorem B1603745 : Blo 1068616 1603745 := bstep (se 2 (by rfl) ⟨601404, by rfl⟩ : syracuseStep 1603745 = 1202809) B1202809
theorem B1603763 : Blo 1068616 1603763 := bstep (se 1 (by rfl) ⟨1202822, by rfl⟩ : syracuseStep 1603763 = 2405645) B2405645
theorem B1603793 : Blo 1068616 1603793 := bstep (se 2 (by rfl) ⟨601422, by rfl⟩ : syracuseStep 1603793 = 1202845) B1202845
theorem B1603811 : Blo 1068616 1603811 := bstep (se 1 (by rfl) ⟨1202858, by rfl⟩ : syracuseStep 1603811 = 2405717) B2405717
theorem B4061411 : Blo 1068616 4061411 := bstep (se 1 (by rfl) ⟨3046058, by rfl⟩ : syracuseStep 4061411 = 6092117) B6092117
theorem B1603841 : Blo 1068616 1603841 := bstep (se 2 (by rfl) ⟨601440, by rfl⟩ : syracuseStep 1603841 = 1202881) B1202881
theorem B1603859 : Blo 1068616 1603859 := bstep (se 1 (by rfl) ⟨1202894, by rfl⟩ : syracuseStep 1603859 = 2405789) B2405789
theorem B1603889 : Blo 1068616 1603889 := bstep (se 2 (by rfl) ⟨601458, by rfl⟩ : syracuseStep 1603889 = 1202917) B1202917
theorem B1603907 : Blo 1068616 1603907 := bstep (se 1 (by rfl) ⟨1202930, by rfl⟩ : syracuseStep 1603907 = 2405861) B2405861
theorem B1603937 : Blo 1068616 1603937 := bstep (se 2 (by rfl) ⟨601476, by rfl⟩ : syracuseStep 1603937 = 1202953) B1202953
theorem B1603955 : Blo 1068616 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B1603985 : Blo 1068616 1603985 := bstep (se 2 (by rfl) ⟨601494, by rfl⟩ : syracuseStep 1603985 = 1202989) B1202989
theorem B1604003 : Blo 1068616 1604003 := bstep (se 1 (by rfl) ⟨1203002, by rfl⟩ : syracuseStep 1604003 = 2406005) B2406005
theorem B1604033 : Blo 1068616 1604033 := bstep (se 2 (by rfl) ⟨601512, by rfl⟩ : syracuseStep 1604033 = 1203025) B1203025
theorem B1604051 : Blo 1068616 1604051 := bstep (se 1 (by rfl) ⟨1203038, by rfl⟩ : syracuseStep 1604051 = 2406077) B2406077
theorem B1604081 : Blo 1068616 1604081 := bstep (se 2 (by rfl) ⟨601530, by rfl⟩ : syracuseStep 1604081 = 1203061) B1203061
theorem B1604099 : Blo 1068616 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B1931779 : Blo 1068616 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1604129 : Blo 1068616 1604129 := bstep (se 2 (by rfl) ⟨601548, by rfl⟩ : syracuseStep 1604129 = 1203097) B1203097
theorem B1604147 : Blo 1068616 1604147 := bstep (se 1 (by rfl) ⟨1203110, by rfl⟩ : syracuseStep 1604147 = 2406221) B2406221
theorem B1604177 : Blo 1068616 1604177 := bstep (se 2 (by rfl) ⟨601566, by rfl⟩ : syracuseStep 1604177 = 1203133) B1203133
theorem B1604195 : Blo 1068616 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B1604225 : Blo 1068616 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B1604243 : Blo 1068616 1604243 := bstep (se 1 (by rfl) ⟨1203182, by rfl⟩ : syracuseStep 1604243 = 2406365) B2406365
theorem B1604273 : Blo 1068616 1604273 := bstep (se 2 (by rfl) ⟨601602, by rfl⟩ : syracuseStep 1604273 = 1203205) B1203205
theorem B1931953 : Blo 1068616 1931953 := bstep (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) B1448965
theorem B1604291 : Blo 1068616 1604291 := bstep (se 1 (by rfl) ⟨1203218, by rfl⟩ : syracuseStep 1604291 = 2406437) B2406437
theorem B1604321 : Blo 1068616 1604321 := bstep (se 2 (by rfl) ⟨601620, by rfl⟩ : syracuseStep 1604321 = 1203241) B1203241
theorem B5798627 : Blo 1068616 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1604339 : Blo 1068616 1604339 := bstep (se 1 (by rfl) ⟨1203254, by rfl⟩ : syracuseStep 1604339 = 2406509) B2406509
theorem B1604369 : Blo 1068616 1604369 := bstep (se 2 (by rfl) ⟨601638, by rfl⟩ : syracuseStep 1604369 = 1203277) B1203277
theorem B1604387 : Blo 1068616 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B1604417 : Blo 1068616 1604417 := bstep (se 2 (by rfl) ⟨601656, by rfl⟩ : syracuseStep 1604417 = 1203313) B1203313
theorem B2030417 : Blo 1068616 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B1604435 : Blo 1068616 1604435 := bstep (se 1 (by rfl) ⟨1203326, by rfl⟩ : syracuseStep 1604435 = 2406653) B2406653
theorem B1604465 : Blo 1068616 1604465 := bstep (se 2 (by rfl) ⟨601674, by rfl⟩ : syracuseStep 1604465 = 1203349) B1203349
theorem B1735553 : Blo 1068616 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1604483 : Blo 1068616 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B1604513 : Blo 1068616 1604513 := bstep (se 2 (by rfl) ⟨601692, by rfl⟩ : syracuseStep 1604513 = 1203385) B1203385
theorem B1604531 : Blo 1068616 1604531 := bstep (se 1 (by rfl) ⟨1203398, by rfl⟩ : syracuseStep 1604531 = 2406797) B2406797
theorem B6847429 : Blo 1068616 6847429 := bstep (se 4 (by rfl) ⟨641946, by rfl⟩ : syracuseStep 6847429 = 1283893) B1283893
theorem B1604561 : Blo 1068616 1604561 := bstep (se 2 (by rfl) ⟨601710, by rfl⟩ : syracuseStep 1604561 = 1203421) B1203421
theorem B1604579 : Blo 1068616 1604579 := bstep (se 1 (by rfl) ⟨1203434, by rfl⟩ : syracuseStep 1604579 = 2406869) B2406869
theorem B1604609 : Blo 1068616 1604609 := bstep (se 2 (by rfl) ⟨601728, by rfl⟩ : syracuseStep 1604609 = 1203457) B1203457
theorem B2259971 : Blo 1068616 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B1604627 : Blo 1068616 1604627 := bstep (se 1 (by rfl) ⟨1203470, by rfl⟩ : syracuseStep 1604627 = 2406941) B2406941
theorem B6945841 : Blo 1068616 6945841 := bstep (se 2 (by rfl) ⟨2604690, by rfl⟩ : syracuseStep 6945841 = 5209381) B5209381
theorem B1604657 : Blo 1068616 1604657 := bstep (se 2 (by rfl) ⟨601746, by rfl⟩ : syracuseStep 1604657 = 1203493) B1203493
theorem B1604675 : Blo 1068616 1604675 := bstep (se 1 (by rfl) ⟨1203506, by rfl⟩ : syracuseStep 1604675 = 2407013) B2407013
theorem B6093893 : Blo 1068616 6093893 := bstep (se 4 (by rfl) ⟨571302, by rfl⟩ : syracuseStep 6093893 = 1142605) B1142605
theorem B3046481 : Blo 1068616 3046481 := bstep (se 2 (by rfl) ⟨1142430, by rfl⟩ : syracuseStep 3046481 = 2284861) B2284861
theorem B1604705 : Blo 1068616 1604705 := bstep (se 2 (by rfl) ⟨601764, by rfl⟩ : syracuseStep 1604705 = 1203529) B1203529
theorem B1604723 : Blo 1068616 1604723 := bstep (se 1 (by rfl) ⟨1203542, by rfl⟩ : syracuseStep 1604723 = 2407085) B2407085
theorem B1604753 : Blo 1068616 1604753 := bstep (se 2 (by rfl) ⟨601782, by rfl⟩ : syracuseStep 1604753 = 1203565) B1203565
theorem B1604771 : Blo 1068616 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B1604801 : Blo 1068616 1604801 := bstep (se 2 (by rfl) ⟨601800, by rfl⟩ : syracuseStep 1604801 = 1203601) B1203601
theorem B4062413 : Blo 1068616 4062413 := bstep (se 3 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 4062413 = 1523405) B1523405
theorem B3767501 : Blo 1068616 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B1604819 : Blo 1068616 1604819 := bstep (se 1 (by rfl) ⟨1203614, by rfl⟩ : syracuseStep 1604819 = 2407229) B2407229
theorem B1604849 : Blo 1068616 1604849 := bstep (se 2 (by rfl) ⟨601818, by rfl⟩ : syracuseStep 1604849 = 1203637) B1203637
theorem B1604867 : Blo 1068616 1604867 := bstep (se 1 (by rfl) ⟨1203650, by rfl⟩ : syracuseStep 1604867 = 2407301) B2407301
theorem B3046673 : Blo 1068616 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1604897 : Blo 1068616 1604897 := bstep (se 2 (by rfl) ⟨601836, by rfl⟩ : syracuseStep 1604897 = 1203673) B1203673
theorem B1604915 : Blo 1068616 1604915 := bstep (se 1 (by rfl) ⟨1203686, by rfl⟩ : syracuseStep 1604915 = 2407373) B2407373
theorem B1604945 : Blo 1068616 1604945 := bstep (se 2 (by rfl) ⟨601854, by rfl⟩ : syracuseStep 1604945 = 1203709) B1203709
theorem B1604963 : Blo 1068616 1604963 := bstep (se 1 (by rfl) ⟨1203722, by rfl⟩ : syracuseStep 1604963 = 2407445) B2407445
theorem B1604993 : Blo 1068616 1604993 := bstep (se 2 (by rfl) ⟨601872, by rfl⟩ : syracuseStep 1604993 = 1203745) B1203745
theorem B1605011 : Blo 1068616 1605011 := bstep (se 1 (by rfl) ⟨1203758, by rfl⟩ : syracuseStep 1605011 = 2407517) B2407517
theorem B1605041 : Blo 1068616 1605041 := bstep (se 2 (by rfl) ⟨601890, by rfl⟩ : syracuseStep 1605041 = 1203781) B1203781
theorem B1605059 : Blo 1068616 1605059 := bstep (se 1 (by rfl) ⟨1203794, by rfl⟩ : syracuseStep 1605059 = 2407589) B2407589
theorem B1605089 : Blo 1068616 1605089 := bstep (se 2 (by rfl) ⟨601908, by rfl⟩ : syracuseStep 1605089 = 1203817) B1203817
theorem B1605107 : Blo 1068616 1605107 := bstep (se 1 (by rfl) ⟨1203830, by rfl⟩ : syracuseStep 1605107 = 2407661) B2407661
theorem B6094349 : Blo 1068616 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B1605137 : Blo 1068616 1605137 := bstep (se 2 (by rfl) ⟨601926, by rfl⟩ : syracuseStep 1605137 = 1203853) B1203853
theorem B1605155 : Blo 1068616 1605155 := bstep (se 1 (by rfl) ⟨1203866, by rfl⟩ : syracuseStep 1605155 = 2407733) B2407733
theorem B1605185 : Blo 1068616 1605185 := bstep (se 2 (by rfl) ⟨601944, by rfl⟩ : syracuseStep 1605185 = 1203889) B1203889
theorem B1605203 : Blo 1068616 1605203 := bstep (se 1 (by rfl) ⟨1203902, by rfl⟩ : syracuseStep 1605203 = 2407805) B2407805
theorem B1605233 : Blo 1068616 1605233 := bstep (se 2 (by rfl) ⟨601962, by rfl⟩ : syracuseStep 1605233 = 1203925) B1203925
theorem B1605251 : Blo 1068616 1605251 := bstep (se 1 (by rfl) ⟨1203938, by rfl⟩ : syracuseStep 1605251 = 2407877) B2407877
theorem B1605281 : Blo 1068616 1605281 := bstep (se 2 (by rfl) ⟨601980, by rfl⟩ : syracuseStep 1605281 = 1203961) B1203961
theorem B1605299 : Blo 1068616 1605299 := bstep (se 1 (by rfl) ⟨1203974, by rfl⟩ : syracuseStep 1605299 = 2407949) B2407949
theorem B2031313 : Blo 1068616 2031313 := bstep (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) B1523485
theorem B1605329 : Blo 1068616 1605329 := bstep (se 2 (by rfl) ⟨601998, by rfl⟩ : syracuseStep 1605329 = 1203997) B1203997
theorem B1605347 : Blo 1068616 1605347 := bstep (se 1 (by rfl) ⟨1204010, by rfl⟩ : syracuseStep 1605347 = 2408021) B2408021
theorem B1605377 : Blo 1068616 1605377 := bstep (se 2 (by rfl) ⟨602016, by rfl⟩ : syracuseStep 1605377 = 1204033) B1204033
theorem B1605395 : Blo 1068616 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B1605425 : Blo 1068616 1605425 := bstep (se 2 (by rfl) ⟨602034, by rfl⟩ : syracuseStep 1605425 = 1204069) B1204069
theorem B1605443 : Blo 1068616 1605443 := bstep (se 1 (by rfl) ⟨1204082, by rfl⟩ : syracuseStep 1605443 = 2408165) B2408165
theorem B1605473 : Blo 1068616 1605473 := bstep (se 2 (by rfl) ⟨602052, by rfl⟩ : syracuseStep 1605473 = 1204105) B1204105
theorem B2031473 : Blo 1068616 2031473 := bstep (se 2 (by rfl) ⟨761802, by rfl⟩ : syracuseStep 2031473 = 1523605) B1523605
theorem B1605491 : Blo 1068616 1605491 := bstep (se 1 (by rfl) ⟨1204118, by rfl⟩ : syracuseStep 1605491 = 2408237) B2408237
theorem B1605521 : Blo 1068616 1605521 := bstep (se 2 (by rfl) ⟨602070, by rfl⟩ : syracuseStep 1605521 = 1204141) B1204141
theorem B1605539 : Blo 1068616 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B1605569 : Blo 1068616 1605569 := bstep (se 2 (by rfl) ⟨602088, by rfl⟩ : syracuseStep 1605569 = 1204177) B1204177
theorem B8126405 : Blo 1068616 8126405 := bstep (se 4 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 8126405 = 1523701) B1523701
theorem B1605587 : Blo 1068616 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B1605617 : Blo 1068616 1605617 := bstep (se 2 (by rfl) ⟨602106, by rfl⟩ : syracuseStep 1605617 = 1204213) B1204213
theorem B2031617 : Blo 1068616 2031617 := bstep (se 2 (by rfl) ⟨761856, by rfl⟩ : syracuseStep 2031617 = 1523713) B1523713
theorem B1605707 : Blo 1068616 1605707 := bstep (se 1 (by rfl) ⟨1204280, by rfl⟩ : syracuseStep 1605707 = 2408561) B2408561
theorem B1605719 : Blo 1068616 1605719 := bstep (se 1 (by rfl) ⟨1204289, by rfl⟩ : syracuseStep 1605719 = 2408579) B2408579
theorem B1605785 : Blo 1068616 1605785 := bstep (se 2 (by rfl) ⟨602169, by rfl⟩ : syracuseStep 1605785 = 1204339) B1204339
theorem B5865689 : Blo 1068616 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B1605899 : Blo 1068616 1605899 := bstep (se 1 (by rfl) ⟨1204424, by rfl⟩ : syracuseStep 1605899 = 2408849) B2408849
theorem B1605911 : Blo 1068616 1605911 := bstep (se 1 (by rfl) ⟨1204433, by rfl⟩ : syracuseStep 1605911 = 2408867) B2408867
theorem B4063553 : Blo 1068616 4063553 := bstep (se 2 (by rfl) ⟨1523832, by rfl⟩ : syracuseStep 4063553 = 3047665) B3047665
theorem B2031959 : Blo 1068616 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B1605977 : Blo 1068616 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B4948397 : Blo 1068616 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B1606091 : Blo 1068616 1606091 := bstep (se 1 (by rfl) ⟨1204568, by rfl⟩ : syracuseStep 1606091 = 2409137) B2409137
theorem B1606103 : Blo 1068616 1606103 := bstep (se 1 (by rfl) ⟨1204577, by rfl⟩ : syracuseStep 1606103 = 2409155) B2409155
theorem B1606169 : Blo 1068616 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B1606283 : Blo 1068616 1606283 := bstep (se 1 (by rfl) ⟨1204712, by rfl⟩ : syracuseStep 1606283 = 2409425) B2409425
theorem B1606295 : Blo 1068616 1606295 := bstep (se 1 (by rfl) ⟨1204721, by rfl⟩ : syracuseStep 1606295 = 2409443) B2409443
theorem B1606361 : Blo 1068616 1606361 := bstep (se 2 (by rfl) ⟨602385, by rfl⟩ : syracuseStep 1606361 = 1204771) B1204771
theorem B1606475 : Blo 1068616 1606475 := bstep (se 1 (by rfl) ⟨1204856, by rfl⟩ : syracuseStep 1606475 = 2409713) B2409713
theorem B1606487 : Blo 1068616 1606487 := bstep (se 1 (by rfl) ⟨1204865, by rfl⟩ : syracuseStep 1606487 = 2409731) B2409731
theorem B1606553 : Blo 1068616 1606553 := bstep (se 2 (by rfl) ⟨602457, by rfl⟩ : syracuseStep 1606553 = 1204915) B1204915
theorem B2032627 : Blo 1068616 2032627 := bstep (se 1 (by rfl) ⟨1524470, by rfl⟩ : syracuseStep 2032627 = 3048941) B3048941
theorem B1606667 : Blo 1068616 1606667 := bstep (se 1 (by rfl) ⟨1205000, by rfl⟩ : syracuseStep 1606667 = 2410001) B2410001
theorem B11731985 : Blo 1068616 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B1606679 : Blo 1068616 1606679 := bstep (se 1 (by rfl) ⟨1205009, by rfl⟩ : syracuseStep 1606679 = 2410019) B2410019
theorem B1606745 : Blo 1068616 1606745 := bstep (se 2 (by rfl) ⟨602529, by rfl⟩ : syracuseStep 1606745 = 1205059) B1205059
theorem B4457651 : Blo 1068616 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B50136245 : Blo 1068616 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B1606859 : Blo 1068616 1606859 := bstep (se 1 (by rfl) ⟨1205144, by rfl⟩ : syracuseStep 1606859 = 2410289) B2410289
theorem B1606871 : Blo 1068616 1606871 := bstep (se 1 (by rfl) ⟨1205153, by rfl⟩ : syracuseStep 1606871 = 2410307) B2410307
theorem B1606937 : Blo 1068616 1606937 := bstep (se 2 (by rfl) ⟨602601, by rfl⟩ : syracuseStep 1606937 = 1205203) B1205203
theorem B3048769 : Blo 1068616 3048769 := bstep (se 2 (by rfl) ⟨1143288, by rfl⟩ : syracuseStep 3048769 = 2286577) B2286577
theorem B1607051 : Blo 1068616 1607051 := bstep (se 1 (by rfl) ⟨1205288, by rfl⟩ : syracuseStep 1607051 = 2410577) B2410577
theorem B1607063 : Blo 1068616 1607063 := bstep (se 1 (by rfl) ⟨1205297, by rfl⟩ : syracuseStep 1607063 = 2410595) B2410595
theorem B2033075 : Blo 1068616 2033075 := bstep (se 1 (by rfl) ⟨1524806, by rfl⟩ : syracuseStep 2033075 = 3049613) B3049613
theorem B2033113 : Blo 1068616 2033113 := bstep (se 2 (by rfl) ⟨762417, by rfl⟩ : syracuseStep 2033113 = 1524835) B1524835
theorem B1607129 : Blo 1068616 1607129 := bstep (se 2 (by rfl) ⟨602673, by rfl⟩ : syracuseStep 1607129 = 1205347) B1205347
theorem B46368227 : Blo 1068616 46368227 := bstep (se 1 (by rfl) ⟨34776170, by rfl⟩ : syracuseStep 46368227 = 69552341) B69552341
theorem B4064813 : Blo 1068616 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B4064843 : Blo 1068616 4064843 := bstep (se 1 (by rfl) ⟨3048632, by rfl⟩ : syracuseStep 4064843 = 6097265) B6097265
theorem B1607243 : Blo 1068616 1607243 := bstep (se 1 (by rfl) ⟨1205432, by rfl⟩ : syracuseStep 1607243 = 2410865) B2410865
theorem B1803863 : Blo 1068616 1803863 := bstep (se 1 (by rfl) ⟨1352897, by rfl⟩ : syracuseStep 1803863 = 2705795) B2705795
theorem B1607255 : Blo 1068616 1607255 := bstep (se 1 (by rfl) ⟨1205441, by rfl⟩ : syracuseStep 1607255 = 2410883) B2410883
theorem B1607321 : Blo 1068616 1607321 := bstep (se 2 (by rfl) ⟨602745, by rfl⟩ : syracuseStep 1607321 = 1205491) B1205491
theorem B1803991 : Blo 1068616 1803991 := bstep (se 1 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 1803991 = 2705987) B2705987
theorem B1607435 : Blo 1068616 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B1607447 : Blo 1068616 1607447 := bstep (se 1 (by rfl) ⟨1205585, by rfl⟩ : syracuseStep 1607447 = 2411171) B2411171
theorem B1607513 : Blo 1068616 1607513 := bstep (se 2 (by rfl) ⟨602817, by rfl⟩ : syracuseStep 1607513 = 1205635) B1205635
theorem B8128349 : Blo 1068616 8128349 := bstep (se 3 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 8128349 = 3048131) B3048131
theorem B75171685 : Blo 1068616 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B2033561 : Blo 1068616 2033561 := bstep (se 2 (by rfl) ⟨762585, by rfl⟩ : syracuseStep 2033561 = 1525171) B1525171
theorem B1607627 : Blo 1068616 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B1607639 : Blo 1068616 1607639 := bstep (se 1 (by rfl) ⟨1205729, by rfl⟩ : syracuseStep 1607639 = 2411459) B2411459
theorem B1607705 : Blo 1068616 1607705 := bstep (se 2 (by rfl) ⟨602889, by rfl⟩ : syracuseStep 1607705 = 1205779) B1205779
theorem B1607819 : Blo 1068616 1607819 := bstep (se 1 (by rfl) ⟨1205864, by rfl⟩ : syracuseStep 1607819 = 2411729) B2411729
theorem B1607831 : Blo 1068616 1607831 := bstep (se 1 (by rfl) ⟨1205873, by rfl⟩ : syracuseStep 1607831 = 2411747) B2411747
theorem B4065497 : Blo 1068616 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B1607897 : Blo 1068616 1607897 := bstep (se 2 (by rfl) ⟨602961, by rfl⟩ : syracuseStep 1607897 = 1205923) B1205923
theorem B1804619 : Blo 1068616 1804619 := bstep (se 1 (by rfl) ⟨1353464, by rfl⟩ : syracuseStep 1804619 = 2706929) B2706929
theorem B1608011 : Blo 1068616 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B1608023 : Blo 1068616 1608023 := bstep (se 1 (by rfl) ⟨1206017, by rfl⟩ : syracuseStep 1608023 = 2412035) B2412035
theorem B1608089 : Blo 1068616 1608089 := bstep (se 2 (by rfl) ⟨603033, by rfl⟩ : syracuseStep 1608089 = 1206067) B1206067
theorem B1804747 : Blo 1068616 1804747 := bstep (se 1 (by rfl) ⟨1353560, by rfl⟩ : syracuseStep 1804747 = 2707121) B2707121
theorem B1608203 : Blo 1068616 1608203 := bstep (se 1 (by rfl) ⟨1206152, by rfl⟩ : syracuseStep 1608203 = 2412305) B2412305
theorem B1444375 : Blo 1068616 1444375 := bstep (se 1 (by rfl) ⟨1083281, by rfl⟩ : syracuseStep 1444375 = 2166563) B2166563
theorem B4065815 : Blo 1068616 4065815 := bstep (se 1 (by rfl) ⟨3049361, by rfl⟩ : syracuseStep 4065815 = 6098723) B6098723
theorem B1608215 : Blo 1068616 1608215 := bstep (se 1 (by rfl) ⟨1206161, by rfl⟩ : syracuseStep 1608215 = 2412323) B2412323
theorem B4885037 : Blo 1068616 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B3607091 : Blo 1068616 3607091 := bstep (se 1 (by rfl) ⟨2705318, by rfl⟩ : syracuseStep 3607091 = 5410637) B5410637
theorem B1804889 : Blo 1068616 1804889 := bstep (se 2 (by rfl) ⟨676833, by rfl⟩ : syracuseStep 1804889 = 1353667) B1353667
theorem B1608281 : Blo 1068616 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B2034305 : Blo 1068616 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B1608395 : Blo 1068616 1608395 := bstep (se 1 (by rfl) ⟨1206296, by rfl⟩ : syracuseStep 1608395 = 2412593) B2412593
theorem B1608407 : Blo 1068616 1608407 := bstep (se 1 (by rfl) ⟨1206305, by rfl⟩ : syracuseStep 1608407 = 2412611) B2412611
theorem B1805017 : Blo 1068616 1805017 := bstep (se 2 (by rfl) ⟨676881, by rfl⟩ : syracuseStep 1805017 = 1353763) B1353763
theorem B1608473 : Blo 1068616 1608473 := bstep (se 2 (by rfl) ⟨603177, by rfl⟩ : syracuseStep 1608473 = 1206355) B1206355
theorem B3607361 : Blo 1068616 3607361 := bstep (se 2 (by rfl) ⟨1352760, by rfl⟩ : syracuseStep 3607361 = 2705521) B2705521
theorem B8227649 : Blo 1068616 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B2034571 : Blo 1068616 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B1608587 : Blo 1068616 1608587 := bstep (se 1 (by rfl) ⟨1206440, by rfl⟩ : syracuseStep 1608587 = 2412881) B2412881
theorem B1608599 : Blo 1068616 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B1608665 : Blo 1068616 1608665 := bstep (se 2 (by rfl) ⟨603249, by rfl⟩ : syracuseStep 1608665 = 1206499) B1206499
theorem B1608779 : Blo 1068616 1608779 := bstep (se 1 (by rfl) ⟨1206584, by rfl⟩ : syracuseStep 1608779 = 2413169) B2413169
theorem B1608791 : Blo 1068616 1608791 := bstep (se 1 (by rfl) ⟨1206593, by rfl⟩ : syracuseStep 1608791 = 2413187) B2413187
theorem B6851735 : Blo 1068616 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1608857 : Blo 1068616 1608857 := bstep (se 2 (by rfl) ⟨603321, by rfl⟩ : syracuseStep 1608857 = 1206643) B1206643
theorem B4066483 : Blo 1068616 4066483 := bstep (se 1 (by rfl) ⟨3049862, by rfl⟩ : syracuseStep 4066483 = 6099725) B6099725
theorem B1805591 : Blo 1068616 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B2035019 : Blo 1068616 2035019 := bstep (se 1 (by rfl) ⟨1526264, by rfl⟩ : syracuseStep 2035019 = 3052529) B3052529
theorem B3607901 : Blo 1068616 3607901 := bstep (se 3 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 3607901 = 1352963) B1352963
theorem B1805719 : Blo 1068616 1805719 := bstep (se 1 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 1805719 = 2708579) B2708579
theorem B2035201 : Blo 1068616 2035201 := bstep (se 2 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 2035201 = 1526401) B1526401
theorem B6098449 : Blo 1068616 6098449 := bstep (se 2 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 6098449 = 4573837) B4573837
theorem B1543961 : Blo 1068616 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B3477313 : Blo 1068616 3477313 := bstep (se 2 (by rfl) ⟨1303992, by rfl⟩ : syracuseStep 3477313 = 2607985) B2607985
theorem B2035543 : Blo 1068616 2035543 := bstep (se 1 (by rfl) ⟨1526657, by rfl⟩ : syracuseStep 2035543 = 3053315) B3053315
theorem B1806347 : Blo 1068616 1806347 := bstep (se 1 (by rfl) ⟨1354760, by rfl⟩ : syracuseStep 1806347 = 2709521) B2709521
theorem B2035763 : Blo 1068616 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B1806475 : Blo 1068616 1806475 := bstep (se 1 (by rfl) ⟨1354856, by rfl⟩ : syracuseStep 1806475 = 2709713) B2709713
theorem B2035991 : Blo 1068616 2035991 := bstep (se 1 (by rfl) ⟨1526993, by rfl⟩ : syracuseStep 2035991 = 3053987) B3053987
theorem B1806617 : Blo 1068616 1806617 := bstep (se 2 (by rfl) ⟨677481, by rfl⟩ : syracuseStep 1806617 = 1354963) B1354963
theorem B1085783 : Blo 1068616 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B1446283 : Blo 1068616 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B4067729 : Blo 1068616 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B1806745 : Blo 1068616 1806745 := bstep (se 2 (by rfl) ⟨677529, by rfl⟩ : syracuseStep 1806745 = 1355059) B1355059
theorem B3609035 : Blo 1068616 3609035 := bstep (se 1 (by rfl) ⟨2706776, by rfl⟩ : syracuseStep 3609035 = 5413553) B5413553
theorem B2036249 : Blo 1068616 2036249 := bstep (se 2 (by rfl) ⟨763593, by rfl⟩ : syracuseStep 2036249 = 1527187) B1527187
theorem B3609305 : Blo 1068616 3609305 := bstep (se 2 (by rfl) ⟨1353489, by rfl⟩ : syracuseStep 3609305 = 2706979) B2706979
theorem B1807319 : Blo 1068616 1807319 := bstep (se 1 (by rfl) ⟨1355489, by rfl⟩ : syracuseStep 1807319 = 2710979) B2710979
theorem B3052505 : Blo 1068616 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B4068427 : Blo 1068616 4068427 := bstep (se 1 (by rfl) ⟨3051320, by rfl⟩ : syracuseStep 4068427 = 6102641) B6102641
theorem B1807447 : Blo 1068616 1807447 := bstep (se 1 (by rfl) ⟨1355585, by rfl⟩ : syracuseStep 1807447 = 2711171) B2711171
theorem B5411933 : Blo 1068616 5411933 := bstep (se 3 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 5411933 = 2029475) B2029475
theorem B4887773 : Blo 1068616 4887773 := bstep (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) B1832915
theorem B13702445 : Blo 1068616 13702445 := bstep (se 3 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 13702445 = 5138417) B5138417
theorem B4068701 : Blo 1068616 4068701 := bstep (se 3 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 4068701 = 1525763) B1525763
theorem B3610007 : Blo 1068616 3610007 := bstep (se 1 (by rfl) ⟨2707505, by rfl⟩ : syracuseStep 3610007 = 5415011) B5415011
theorem B18519475 : Blo 1068616 18519475 := bstep (se 1 (by rfl) ⟨13889606, by rfl⟩ : syracuseStep 18519475 = 27779213) B27779213
theorem B2168257 : Blo 1068616 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B2168321 : Blo 1068616 2168321 := bstep (se 2 (by rfl) ⟨813120, by rfl⟩ : syracuseStep 2168321 = 1626241) B1626241
theorem B1808075 : Blo 1068616 1808075 := bstep (se 1 (by rfl) ⟨1356056, by rfl⟩ : syracuseStep 1808075 = 2712113) B2712113
theorem B1808203 : Blo 1068616 1808203 := bstep (se 1 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 1808203 = 2712305) B2712305
theorem B3610547 : Blo 1068616 3610547 := bstep (se 1 (by rfl) ⟨2707910, by rfl⟩ : syracuseStep 3610547 = 5415821) B5415821
theorem B1808345 : Blo 1068616 1808345 := bstep (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) B1356259
theorem B4069399 : Blo 1068616 4069399 := bstep (se 1 (by rfl) ⟨3052049, by rfl⟩ : syracuseStep 4069399 = 6104099) B6104099
theorem B5150795 : Blo 1068616 5150795 := bstep (se 1 (by rfl) ⟨3863096, by rfl⟩ : syracuseStep 5150795 = 7726193) B7726193
theorem B1808473 : Blo 1068616 1808473 := bstep (se 2 (by rfl) ⟨678177, by rfl⟩ : syracuseStep 1808473 = 1356355) B1356355
theorem B3610817 : Blo 1068616 3610817 := bstep (se 2 (by rfl) ⟨1354056, by rfl⟩ : syracuseStep 3610817 = 2708113) B2708113
theorem B3053771 : Blo 1068616 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B1284427 : Blo 1068616 1284427 := bstep (se 1 (by rfl) ⟨963320, by rfl⟩ : syracuseStep 1284427 = 1926641) B1926641
theorem B9902411 : Blo 1068616 9902411 := bstep (se 1 (by rfl) ⟨7426808, by rfl⟩ : syracuseStep 9902411 = 14853617) B14853617
theorem B1809047 : Blo 1068616 1809047 := bstep (se 1 (by rfl) ⟨1356785, by rfl⟩ : syracuseStep 1809047 = 2713571) B2713571
theorem B3611357 : Blo 1068616 3611357 := bstep (se 3 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 3611357 = 1354259) B1354259
theorem B1809175 : Blo 1068616 1809175 := bstep (se 1 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 1809175 = 2713763) B2713763
theorem B4070189 : Blo 1068616 4070189 := bstep (se 3 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 4070189 = 1526321) B1526321
theorem B6101891 : Blo 1068616 6101891 := bstep (se 1 (by rfl) ⟨4576418, by rfl⟩ : syracuseStep 6101891 = 9152837) B9152837
theorem B1448921 : Blo 1068616 1448921 := bstep (se 2 (by rfl) ⟨543345, by rfl⟩ : syracuseStep 1448921 = 1086691) B1086691
theorem B5414039 : Blo 1068616 5414039 := bstep (se 1 (by rfl) ⟨4060529, by rfl⟩ : syracuseStep 5414039 = 8121059) B8121059
theorem B18292067 : Blo 1068616 18292067 := bstep (se 1 (by rfl) ⟨13719050, by rfl⟩ : syracuseStep 18292067 = 27438101) B27438101
theorem B1809803 : Blo 1068616 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B1449419 : Blo 1068616 1449419 := bstep (se 1 (by rfl) ⟨1087064, by rfl⟩ : syracuseStep 1449419 = 2174129) B2174129
theorem B1809931 : Blo 1068616 1809931 := bstep (se 1 (by rfl) ⟨1357448, by rfl⟩ : syracuseStep 1809931 = 2714897) B2714897
theorem B4628141 : Blo 1068616 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B3612491 : Blo 1068616 3612491 := bstep (se 1 (by rfl) ⟨2709368, by rfl⟩ : syracuseStep 3612491 = 5418737) B5418737
theorem B47652785 : Blo 1068616 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B3612761 : Blo 1068616 3612761 := bstep (se 2 (by rfl) ⟨1354785, by rfl⟩ : syracuseStep 3612761 = 2709571) B2709571
theorem B1712281 : Blo 1068616 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B4071617 : Blo 1068616 4071617 := bstep (se 2 (by rfl) ⟨1526856, by rfl⟩ : syracuseStep 4071617 = 3053713) B3053713
theorem B1712729 : Blo 1068616 1712729 := bstep (se 2 (by rfl) ⟨642273, by rfl⟩ : syracuseStep 1712729 = 1284547) B1284547
theorem B4399895 : Blo 1068616 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B3613463 : Blo 1068616 3613463 := bstep (se 1 (by rfl) ⟨2710097, by rfl⟩ : syracuseStep 3613463 = 5420195) B5420195
theorem B3253067 : Blo 1068616 3253067 := bstep (se 1 (by rfl) ⟨2439800, by rfl⟩ : syracuseStep 3253067 = 4879601) B4879601
theorem B2892761 : Blo 1068616 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B1352791 : Blo 1068616 1352791 := bstep (se 1 (by rfl) ⟨1014593, by rfl⟩ : syracuseStep 1352791 = 2029187) B2029187
theorem B6104281 : Blo 1068616 6104281 := bstep (se 2 (by rfl) ⟨2289105, by rfl⟩ : syracuseStep 6104281 = 4578211) B4578211
theorem B3614003 : Blo 1068616 3614003 := bstep (se 1 (by rfl) ⟨2710502, by rfl⟩ : syracuseStep 3614003 = 5421005) B5421005
theorem B3614273 : Blo 1068616 3614273 := bstep (se 2 (by rfl) ⟨1355352, by rfl⟩ : syracuseStep 3614273 = 2710705) B2710705
theorem B7808813 : Blo 1068616 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B1353611 : Blo 1068616 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B3614813 : Blo 1068616 3614813 := bstep (se 3 (by rfl) ⟨677777, by rfl⟩ : syracuseStep 3614813 = 1355555) B1355555
theorem B6105239 : Blo 1068616 6105239 := bstep (se 1 (by rfl) ⟨4578929, by rfl⟩ : syracuseStep 6105239 = 9157859) B9157859
theorem B1354315 : Blo 1068616 1354315 := bstep (se 1 (by rfl) ⟨1015736, by rfl⟩ : syracuseStep 1354315 = 2031473) B2031473
theorem B5417603 : Blo 1068616 5417603 := bstep (se 1 (by rfl) ⟨4063202, by rfl⟩ : syracuseStep 5417603 = 8126405) B8126405
theorem B1354583 : Blo 1068616 1354583 := bstep (se 1 (by rfl) ⟨1015937, by rfl⟩ : syracuseStep 1354583 = 2031875) B2031875
theorem B9153485 : Blo 1068616 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B3615947 : Blo 1068616 3615947 := bstep (se 1 (by rfl) ⟨2711960, by rfl⟩ : syracuseStep 3615947 = 5423921) B5423921
theorem B3616217 : Blo 1068616 3616217 := bstep (se 2 (by rfl) ⟨1356081, by rfl⟩ : syracuseStep 3616217 = 2712163) B2712163
theorem B1355287 : Blo 1068616 1355287 := bstep (se 1 (by rfl) ⟨1016465, by rfl⟩ : syracuseStep 1355287 = 2032931) B2032931
theorem B4566593 : Blo 1068616 4566593 := bstep (se 2 (by rfl) ⟨1712472, by rfl⟩ : syracuseStep 4566593 = 3424945) B3424945
theorem B4566935 : Blo 1068616 4566935 := bstep (se 1 (by rfl) ⟨3425201, by rfl⟩ : syracuseStep 4566935 = 6850403) B6850403
theorem B10301363 : Blo 1068616 10301363 := bstep (se 1 (by rfl) ⟨7726022, by rfl⟩ : syracuseStep 10301363 = 15452045) B15452045
theorem B12202001 : Blo 1068616 12202001 := bstep (se 2 (by rfl) ⟨4575750, by rfl⟩ : syracuseStep 12202001 = 9151501) B9151501
theorem B15446051 : Blo 1068616 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B2404403 : Blo 1068616 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B2404439 : Blo 1068616 2404439 := bstep (se 1 (by rfl) ⟨1803329, by rfl⟩ : syracuseStep 2404439 = 3606659) B3606659
theorem B3616919 : Blo 1068616 3616919 := bstep (se 1 (by rfl) ⟨2712689, by rfl⟩ : syracuseStep 3616919 = 5425379) B5425379
theorem B13709573 : Blo 1068616 13709573 := bstep (se 4 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 13709573 = 2570545) B2570545
theorem B2404619 : Blo 1068616 2404619 := bstep (se 1 (by rfl) ⟨1803464, by rfl⟩ : syracuseStep 2404619 = 3606929) B3606929
theorem B2404673 : Blo 1068616 2404673 := bstep (se 2 (by rfl) ⟨901752, by rfl⟩ : syracuseStep 2404673 = 1803505) B1803505
theorem B2437465 : Blo 1068616 2437465 := bstep (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) B1828099
theorem B2404889 : Blo 1068616 2404889 := bstep (se 2 (by rfl) ⟨901833, by rfl⟩ : syracuseStep 2404889 = 1803667) B1803667
theorem B6107723 : Blo 1068616 6107723 := bstep (se 1 (by rfl) ⟨4580792, by rfl⟩ : syracuseStep 6107723 = 9161585) B9161585
theorem B2404979 : Blo 1068616 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B2405015 : Blo 1068616 2405015 := bstep (se 1 (by rfl) ⟨1803761, by rfl⟩ : syracuseStep 2405015 = 3607523) B3607523
theorem B3617459 : Blo 1068616 3617459 := bstep (se 1 (by rfl) ⟨2713094, by rfl⟩ : syracuseStep 3617459 = 5426189) B5426189
theorem B4567859 : Blo 1068616 4567859 := bstep (se 1 (by rfl) ⟨3425894, by rfl⟩ : syracuseStep 4567859 = 6851789) B6851789
theorem B2405195 : Blo 1068616 2405195 := bstep (se 1 (by rfl) ⟨1803896, by rfl⟩ : syracuseStep 2405195 = 3607793) B3607793
theorem B2405249 : Blo 1068616 2405249 := bstep (se 2 (by rfl) ⟨901968, by rfl⟩ : syracuseStep 2405249 = 1803937) B1803937
theorem B3814289 : Blo 1068616 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B3617729 : Blo 1068616 3617729 := bstep (se 2 (by rfl) ⟨1356648, by rfl⟩ : syracuseStep 3617729 = 2713297) B2713297
theorem B2405465 : Blo 1068616 2405465 := bstep (se 2 (by rfl) ⟨902049, by rfl⟩ : syracuseStep 2405465 = 1804099) B1804099
theorem B1717337 : Blo 1068616 1717337 := bstep (se 2 (by rfl) ⟨644001, by rfl⟩ : syracuseStep 1717337 = 1288003) B1288003
theorem B2405555 : Blo 1068616 2405555 := bstep (se 1 (by rfl) ⟨1804166, by rfl⟩ : syracuseStep 2405555 = 3608333) B3608333
theorem B1357003 : Blo 1068616 1357003 := bstep (se 1 (by rfl) ⟨1017752, by rfl⟩ : syracuseStep 1357003 = 2035505) B2035505
theorem B2405591 : Blo 1068616 2405591 := bstep (se 1 (by rfl) ⟨1804193, by rfl⟩ : syracuseStep 2405591 = 3608387) B3608387
theorem B9155875 : Blo 1068616 9155875 := bstep (se 1 (by rfl) ⟨6866906, by rfl⟩ : syracuseStep 9155875 = 13733813) B13733813
theorem B10302821 : Blo 1068616 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B2405771 : Blo 1068616 2405771 := bstep (se 1 (by rfl) ⟨1804328, by rfl⟩ : syracuseStep 2405771 = 3608657) B3608657
theorem B7714199 : Blo 1068616 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B2438579 : Blo 1068616 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B2405825 : Blo 1068616 2405825 := bstep (se 2 (by rfl) ⟨902184, by rfl⟩ : syracuseStep 2405825 = 1804369) B1804369
theorem B3618269 : Blo 1068616 3618269 := bstep (se 3 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 3618269 = 1356851) B1356851
theorem B2438707 : Blo 1068616 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B8697419 : Blo 1068616 8697419 := bstep (se 1 (by rfl) ⟨6523064, by rfl⟩ : syracuseStep 8697419 = 13046129) B13046129
theorem B2406041 : Blo 1068616 2406041 := bstep (se 2 (by rfl) ⟨902265, by rfl⟩ : syracuseStep 2406041 = 1804531) B1804531
theorem B2569931 : Blo 1068616 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B4339403 : Blo 1068616 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B2406131 : Blo 1068616 2406131 := bstep (se 1 (by rfl) ⟨1804598, by rfl⟩ : syracuseStep 2406131 = 3609197) B3609197
theorem B4568849 : Blo 1068616 4568849 := bstep (se 2 (by rfl) ⟨1713318, by rfl⟩ : syracuseStep 4568849 = 3426637) B3426637
theorem B2406167 : Blo 1068616 2406167 := bstep (se 1 (by rfl) ⟨1804625, by rfl⟩ : syracuseStep 2406167 = 3609251) B3609251
theorem B2406347 : Blo 1068616 2406347 := bstep (se 1 (by rfl) ⟨1804760, by rfl⟩ : syracuseStep 2406347 = 3609521) B3609521
theorem B4405213 : Blo 1068616 4405213 := bstep (se 3 (by rfl) ⟨825977, by rfl⟩ : syracuseStep 4405213 = 1651955) B1651955
theorem B2406401 : Blo 1068616 2406401 := bstep (se 2 (by rfl) ⟨902400, by rfl⟩ : syracuseStep 2406401 = 1804801) B1804801
theorem B4339757 : Blo 1068616 4339757 := bstep (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) B1627409
theorem B2406617 : Blo 1068616 2406617 := bstep (se 2 (by rfl) ⟨902481, by rfl⟩ : syracuseStep 2406617 = 1804963) B1804963
theorem B15644933 : Blo 1068616 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B5421329 : Blo 1068616 5421329 := bstep (se 2 (by rfl) ⟨2032998, by rfl⟩ : syracuseStep 5421329 = 4065997) B4065997
theorem B2406707 : Blo 1068616 2406707 := bstep (se 1 (by rfl) ⟨1805030, by rfl⟩ : syracuseStep 2406707 = 3610061) B3610061
theorem B2406743 : Blo 1068616 2406743 := bstep (se 1 (by rfl) ⟨1805057, by rfl⟩ : syracuseStep 2406743 = 3610115) B3610115
theorem B12368305 : Blo 1068616 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B5421491 : Blo 1068616 5421491 := bstep (se 1 (by rfl) ⟨4066118, by rfl⟩ : syracuseStep 5421491 = 8132237) B8132237
theorem B2406923 : Blo 1068616 2406923 := bstep (se 1 (by rfl) ⟨1805192, by rfl⟩ : syracuseStep 2406923 = 3610385) B3610385
theorem B11581987 : Blo 1068616 11581987 := bstep (se 1 (by rfl) ⟨8686490, by rfl⟩ : syracuseStep 11581987 = 17372981) B17372981
theorem B2406977 : Blo 1068616 2406977 := bstep (se 2 (by rfl) ⟨902616, by rfl⟩ : syracuseStep 2406977 = 1805233) B1805233
theorem B3619403 : Blo 1068616 3619403 := bstep (se 1 (by rfl) ⟨2714552, by rfl⟩ : syracuseStep 3619403 = 5429105) B5429105
theorem B2407193 : Blo 1068616 2407193 := bstep (se 2 (by rfl) ⟨902697, by rfl⟩ : syracuseStep 2407193 = 1805395) B1805395
theorem B3259187 : Blo 1068616 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B3619673 : Blo 1068616 3619673 := bstep (se 2 (by rfl) ⟨1357377, by rfl⟩ : syracuseStep 3619673 = 2714755) B2714755
theorem B2407283 : Blo 1068616 2407283 := bstep (se 1 (by rfl) ⟨1805462, by rfl⟩ : syracuseStep 2407283 = 3610925) B3610925
theorem B12204917 : Blo 1068616 12204917 := bstep (se 5 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 12204917 = 1144211) B1144211
theorem B2407319 : Blo 1068616 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B1522585 : Blo 1068616 1522585 := bstep (se 2 (by rfl) ⟨570969, by rfl⟩ : syracuseStep 1522585 = 1141939) B1141939
theorem B2898881 : Blo 1068616 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B2407499 : Blo 1068616 2407499 := bstep (se 1 (by rfl) ⟨1805624, by rfl⟩ : syracuseStep 2407499 = 3611249) B3611249
theorem B2407553 : Blo 1068616 2407553 := bstep (se 2 (by rfl) ⟨902832, by rfl⟩ : syracuseStep 2407553 = 1805665) B1805665
theorem B2407769 : Blo 1068616 2407769 := bstep (se 2 (by rfl) ⟨902913, by rfl⟩ : syracuseStep 2407769 = 1805827) B1805827
theorem B16465331 : Blo 1068616 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B2407859 : Blo 1068616 2407859 := bstep (se 1 (by rfl) ⟨1805894, by rfl⟩ : syracuseStep 2407859 = 3611789) B3611789
theorem B9780659 : Blo 1068616 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B2407895 : Blo 1068616 2407895 := bstep (se 1 (by rfl) ⟨1805921, by rfl⟩ : syracuseStep 2407895 = 3611843) B3611843
theorem B4341313 : Blo 1068616 4341313 := bstep (se 2 (by rfl) ⟨1627992, by rfl⟩ : syracuseStep 4341313 = 3255985) B3255985
theorem B2408075 : Blo 1068616 2408075 := bstep (se 1 (by rfl) ⟨1806056, by rfl⟩ : syracuseStep 2408075 = 3612113) B3612113
theorem B2408129 : Blo 1068616 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B2408345 : Blo 1068616 2408345 := bstep (se 2 (by rfl) ⟨903129, by rfl⟩ : syracuseStep 2408345 = 1806259) B1806259
theorem B6864857 : Blo 1068616 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B2408435 : Blo 1068616 2408435 := bstep (se 1 (by rfl) ⟨1806326, by rfl⟩ : syracuseStep 2408435 = 3612653) B3612653
theorem B2408471 : Blo 1068616 2408471 := bstep (se 1 (by rfl) ⟨1806353, by rfl⟩ : syracuseStep 2408471 = 3612707) B3612707
theorem B4571225 : Blo 1068616 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B8667287 : Blo 1068616 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B9388183 : Blo 1068616 9388183 := bstep (se 1 (by rfl) ⟨7041137, by rfl⟩ : syracuseStep 9388183 = 14082275) B14082275
theorem B4571309 : Blo 1068616 4571309 := bstep (se 3 (by rfl) ⟨857120, by rfl⟩ : syracuseStep 4571309 = 1714241) B1714241
theorem B2408651 : Blo 1068616 2408651 := bstep (se 1 (by rfl) ⟨1806488, by rfl⟩ : syracuseStep 2408651 = 3612977) B3612977
theorem B1523929 : Blo 1068616 1523929 := bstep (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) B1142947
theorem B2408705 : Blo 1068616 2408705 := bstep (se 2 (by rfl) ⟨903264, by rfl⟩ : syracuseStep 2408705 = 1806529) B1806529
theorem B37044485 : Blo 1068616 37044485 := bstep (se 4 (by rfl) ⟨3472920, by rfl⟩ : syracuseStep 37044485 = 6945841) B6945841
theorem B3424535 : Blo 1068616 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B1524043 : Blo 1068616 1524043 := bstep (se 1 (by rfl) ⟨1143032, by rfl⟩ : syracuseStep 1524043 = 2286065) B2286065
theorem B5423435 : Blo 1068616 5423435 := bstep (se 1 (by rfl) ⟨4067576, by rfl⟩ : syracuseStep 5423435 = 8135153) B8135153
theorem B2408921 : Blo 1068616 2408921 := bstep (se 2 (by rfl) ⟨903345, by rfl⟩ : syracuseStep 2408921 = 1806691) B1806691
theorem B2572823 : Blo 1068616 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B2409011 : Blo 1068616 2409011 := bstep (se 1 (by rfl) ⟨1806758, by rfl⟩ : syracuseStep 2409011 = 3613517) B3613517
theorem B2409047 : Blo 1068616 2409047 := bstep (se 1 (by rfl) ⟨1806785, by rfl⟩ : syracuseStep 2409047 = 3613571) B3613571
theorem B2409227 : Blo 1068616 2409227 := bstep (se 1 (by rfl) ⟨1806920, by rfl⟩ : syracuseStep 2409227 = 3613841) B3613841
theorem B3425075 : Blo 1068616 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B2409281 : Blo 1068616 2409281 := bstep (se 2 (by rfl) ⟨903480, by rfl⟩ : syracuseStep 2409281 = 1806961) B1806961
theorem B2409497 : Blo 1068616 2409497 := bstep (se 2 (by rfl) ⟨903561, by rfl⟩ : syracuseStep 2409497 = 1807123) B1807123
theorem B6865985 : Blo 1068616 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B4342859 : Blo 1068616 4342859 := bstep (se 1 (by rfl) ⟨3257144, by rfl⟩ : syracuseStep 4342859 = 6514289) B6514289
theorem B2409587 : Blo 1068616 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B2409623 : Blo 1068616 2409623 := bstep (se 1 (by rfl) ⟨1807217, by rfl⟩ : syracuseStep 2409623 = 3614435) B3614435
theorem B2409803 : Blo 1068616 2409803 := bstep (se 1 (by rfl) ⟨1807352, by rfl⟩ : syracuseStep 2409803 = 3614705) B3614705
theorem B1099127 : Blo 1068616 1099127 := bstep (se 1 (by rfl) ⟨824345, by rfl⟩ : syracuseStep 1099127 = 1648691) B1648691
theorem B2409857 : Blo 1068616 2409857 := bstep (se 2 (by rfl) ⟨903696, by rfl⟩ : syracuseStep 2409857 = 1807393) B1807393
theorem B3425753 : Blo 1068616 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B5490251 : Blo 1068616 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B2704985 : Blo 1068616 2704985 := bstep (se 2 (by rfl) ⟨1014369, by rfl⟩ : syracuseStep 2704985 = 2028739) B2028739
theorem B2410073 : Blo 1068616 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B1525387 : Blo 1068616 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B2410163 : Blo 1068616 2410163 := bstep (se 1 (by rfl) ⟨1807622, by rfl⟩ : syracuseStep 2410163 = 3615245) B3615245
theorem B2410199 : Blo 1068616 2410199 := bstep (se 1 (by rfl) ⟨1807649, by rfl⟩ : syracuseStep 2410199 = 3615299) B3615299
theorem B1853209 : Blo 1068616 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B9160523 : Blo 1068616 9160523 := bstep (se 1 (by rfl) ⟨6870392, by rfl⟩ : syracuseStep 9160523 = 13740785) B13740785
theorem B2410379 : Blo 1068616 2410379 := bstep (se 1 (by rfl) ⟨1807784, by rfl⟩ : syracuseStep 2410379 = 3615569) B3615569
theorem B1525655 : Blo 1068616 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B2410433 : Blo 1068616 2410433 := bstep (se 2 (by rfl) ⟨903912, by rfl⟩ : syracuseStep 2410433 = 1807825) B1807825
theorem B2934749 : Blo 1068616 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B5425217 : Blo 1068616 5425217 := bstep (se 2 (by rfl) ⟨2034456, by rfl⟩ : syracuseStep 5425217 = 4068913) B4068913
theorem B2345113 : Blo 1068616 2345113 := bstep (se 2 (by rfl) ⟨879417, by rfl⟩ : syracuseStep 2345113 = 1758835) B1758835
theorem B2410649 : Blo 1068616 2410649 := bstep (se 2 (by rfl) ⟨903993, by rfl⟩ : syracuseStep 2410649 = 1807987) B1807987
theorem B8800435 : Blo 1068616 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B2410739 : Blo 1068616 2410739 := bstep (se 1 (by rfl) ⟨1808054, by rfl⟩ : syracuseStep 2410739 = 3616109) B3616109
theorem B2410775 : Blo 1068616 2410775 := bstep (se 1 (by rfl) ⟨1808081, by rfl⟩ : syracuseStep 2410775 = 3616163) B3616163
theorem B2410955 : Blo 1068616 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B2411009 : Blo 1068616 2411009 := bstep (se 2 (by rfl) ⟨904128, by rfl⟩ : syracuseStep 2411009 = 1808257) B1808257
theorem B2574899 : Blo 1068616 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B11586179 : Blo 1068616 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B3426995 : Blo 1068616 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B2411225 : Blo 1068616 2411225 := bstep (se 2 (by rfl) ⟨904209, by rfl⟩ : syracuseStep 2411225 = 1808419) B1808419
theorem B14666501 : Blo 1068616 14666501 := bstep (se 4 (by rfl) ⟨1374984, by rfl⟩ : syracuseStep 14666501 = 2749969) B2749969
theorem B2411315 : Blo 1068616 2411315 := bstep (se 1 (by rfl) ⟨1808486, by rfl⟩ : syracuseStep 2411315 = 3616973) B3616973
theorem B2411351 : Blo 1068616 2411351 := bstep (se 1 (by rfl) ⟨1808513, by rfl⟩ : syracuseStep 2411351 = 3617027) B3617027
theorem B1526617 : Blo 1068616 1526617 := bstep (se 2 (by rfl) ⟨572481, by rfl⟩ : syracuseStep 1526617 = 1144963) B1144963
theorem B11586521 : Blo 1068616 11586521 := bstep (se 2 (by rfl) ⟨4344945, by rfl⟩ : syracuseStep 11586521 = 8689891) B8689891
theorem B2411531 : Blo 1068616 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B2411585 : Blo 1068616 2411585 := bstep (se 2 (by rfl) ⟨904344, by rfl⟩ : syracuseStep 2411585 = 1808689) B1808689
theorem B12536963 : Blo 1068616 12536963 := bstep (se 1 (by rfl) ⟨9402722, by rfl⟩ : syracuseStep 12536963 = 18805445) B18805445
theorem B2706635 : Blo 1068616 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B2411801 : Blo 1068616 2411801 := bstep (se 2 (by rfl) ⟨904425, by rfl⟩ : syracuseStep 2411801 = 1808851) B1808851
theorem B2411891 : Blo 1068616 2411891 := bstep (se 1 (by rfl) ⟨1808918, by rfl⟩ : syracuseStep 2411891 = 3617837) B3617837
theorem B2411927 : Blo 1068616 2411927 := bstep (se 1 (by rfl) ⟨1808945, by rfl⟩ : syracuseStep 2411927 = 3617891) B3617891
theorem B6180275 : Blo 1068616 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B4574657 : Blo 1068616 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B2575937 : Blo 1068616 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B1068619 : Blo 1068616 1068619 := bstep (se 1 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 1068619 = 1602929) B1602929
theorem B2412107 : Blo 1068616 2412107 := bstep (se 1 (by rfl) ⟨1809080, by rfl⟩ : syracuseStep 2412107 = 3618161) B3618161
theorem B1068631 : Blo 1068616 1068631 := bstep (se 1 (by rfl) ⟨801473, by rfl⟩ : syracuseStep 1068631 = 1602947) B1602947
theorem B1068651 : Blo 1068616 1068651 := bstep (se 1 (by rfl) ⟨801488, by rfl⟩ : syracuseStep 1068651 = 1602977) B1602977
theorem B1068663 : Blo 1068616 1068663 := bstep (se 1 (by rfl) ⟨801497, by rfl⟩ : syracuseStep 1068663 = 1602995) B1602995
theorem B2412161 : Blo 1068616 2412161 := bstep (se 2 (by rfl) ⟨904560, by rfl⟩ : syracuseStep 2412161 = 1809121) B1809121
theorem B1068683 : Blo 1068616 1068683 := bstep (se 1 (by rfl) ⟨801512, by rfl⟩ : syracuseStep 1068683 = 1603025) B1603025
theorem B1068695 : Blo 1068616 1068695 := bstep (se 1 (by rfl) ⟨801521, by rfl⟩ : syracuseStep 1068695 = 1603043) B1603043
theorem B1068715 : Blo 1068616 1068715 := bstep (se 1 (by rfl) ⟨801536, by rfl⟩ : syracuseStep 1068715 = 1603073) B1603073
theorem B1068727 : Blo 1068616 1068727 := bstep (se 1 (by rfl) ⟨801545, by rfl⟩ : syracuseStep 1068727 = 1603091) B1603091
theorem B1068747 : Blo 1068616 1068747 := bstep (se 1 (by rfl) ⟨801560, by rfl⟩ : syracuseStep 1068747 = 1603121) B1603121
theorem B1068759 : Blo 1068616 1068759 := bstep (se 1 (by rfl) ⟨801569, by rfl⟩ : syracuseStep 1068759 = 1603139) B1603139
theorem B1068779 : Blo 1068616 1068779 := bstep (se 1 (by rfl) ⟨801584, by rfl⟩ : syracuseStep 1068779 = 1603169) B1603169
theorem B1068791 : Blo 1068616 1068791 := bstep (se 1 (by rfl) ⟨801593, by rfl⟩ : syracuseStep 1068791 = 1603187) B1603187
theorem B1068811 : Blo 1068616 1068811 := bstep (se 1 (by rfl) ⟨801608, by rfl⟩ : syracuseStep 1068811 = 1603217) B1603217
theorem B1068823 : Blo 1068616 1068823 := bstep (se 1 (by rfl) ⟨801617, by rfl⟩ : syracuseStep 1068823 = 1603235) B1603235
theorem B1068843 : Blo 1068616 1068843 := bstep (se 1 (by rfl) ⟨801632, by rfl⟩ : syracuseStep 1068843 = 1603265) B1603265
theorem B1068855 : Blo 1068616 1068855 := bstep (se 1 (by rfl) ⟨801641, by rfl⟩ : syracuseStep 1068855 = 1603283) B1603283
theorem B1068875 : Blo 1068616 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B1068887 : Blo 1068616 1068887 := bstep (se 1 (by rfl) ⟨801665, by rfl⟩ : syracuseStep 1068887 = 1603331) B1603331
theorem B2412377 : Blo 1068616 2412377 := bstep (se 2 (by rfl) ⟨904641, by rfl⟩ : syracuseStep 2412377 = 1809283) B1809283
theorem B1068907 : Blo 1068616 1068907 := bstep (se 1 (by rfl) ⟨801680, by rfl⟩ : syracuseStep 1068907 = 1603361) B1603361
theorem B1068919 : Blo 1068616 1068919 := bstep (se 1 (by rfl) ⟨801689, by rfl⟩ : syracuseStep 1068919 = 1603379) B1603379
theorem B1068939 : Blo 1068616 1068939 := bstep (se 1 (by rfl) ⟨801704, by rfl⟩ : syracuseStep 1068939 = 1603409) B1603409
theorem B1068951 : Blo 1068616 1068951 := bstep (se 1 (by rfl) ⟨801713, by rfl⟩ : syracuseStep 1068951 = 1603427) B1603427
theorem B1068971 : Blo 1068616 1068971 := bstep (se 1 (by rfl) ⟨801728, by rfl⟩ : syracuseStep 1068971 = 1603457) B1603457
theorem B9129905 : Blo 1068616 9129905 := bstep (se 2 (by rfl) ⟨3423714, by rfl⟩ : syracuseStep 9129905 = 6847429) B6847429
theorem B2412467 : Blo 1068616 2412467 := bstep (se 1 (by rfl) ⟨1809350, by rfl⟩ : syracuseStep 2412467 = 3618701) B3618701
theorem B1068983 : Blo 1068616 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B1069003 : Blo 1068616 1069003 := bstep (se 1 (by rfl) ⟨801752, by rfl⟩ : syracuseStep 1069003 = 1603505) B1603505
theorem B1069015 : Blo 1068616 1069015 := bstep (se 1 (by rfl) ⟨801761, by rfl⟩ : syracuseStep 1069015 = 1603523) B1603523
theorem B5427161 : Blo 1068616 5427161 := bstep (se 2 (by rfl) ⟨2035185, by rfl⟩ : syracuseStep 5427161 = 4070371) B4070371
theorem B2412503 : Blo 1068616 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B1069035 : Blo 1068616 1069035 := bstep (se 1 (by rfl) ⟨801776, by rfl⟩ : syracuseStep 1069035 = 1603553) B1603553
theorem B1069047 : Blo 1068616 1069047 := bstep (se 1 (by rfl) ⟨801785, by rfl⟩ : syracuseStep 1069047 = 1603571) B1603571
theorem B1069067 : Blo 1068616 1069067 := bstep (se 1 (by rfl) ⟨801800, by rfl⟩ : syracuseStep 1069067 = 1603601) B1603601
theorem B1069079 : Blo 1068616 1069079 := bstep (se 1 (by rfl) ⟨801809, by rfl⟩ : syracuseStep 1069079 = 1603619) B1603619
theorem B1069099 : Blo 1068616 1069099 := bstep (se 1 (by rfl) ⟨801824, by rfl⟩ : syracuseStep 1069099 = 1603649) B1603649
theorem B1069111 : Blo 1068616 1069111 := bstep (se 1 (by rfl) ⟨801833, by rfl⟩ : syracuseStep 1069111 = 1603667) B1603667
theorem B1069131 : Blo 1068616 1069131 := bstep (se 1 (by rfl) ⟨801848, by rfl⟩ : syracuseStep 1069131 = 1603697) B1603697
theorem B1069143 : Blo 1068616 1069143 := bstep (se 1 (by rfl) ⟨801857, by rfl⟩ : syracuseStep 1069143 = 1603715) B1603715
theorem B4575325 : Blo 1068616 4575325 := bstep (se 3 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 4575325 = 1715747) B1715747
theorem B1069163 : Blo 1068616 1069163 := bstep (se 1 (by rfl) ⟨801872, by rfl⟩ : syracuseStep 1069163 = 1603745) B1603745
theorem B1069175 : Blo 1068616 1069175 := bstep (se 1 (by rfl) ⟨801881, by rfl⟩ : syracuseStep 1069175 = 1603763) B1603763
theorem B1069195 : Blo 1068616 1069195 := bstep (se 1 (by rfl) ⟨801896, by rfl⟩ : syracuseStep 1069195 = 1603793) B1603793
theorem B2412683 : Blo 1068616 2412683 := bstep (se 1 (by rfl) ⟨1809512, by rfl⟩ : syracuseStep 2412683 = 3619025) B3619025
theorem B1069207 : Blo 1068616 1069207 := bstep (se 1 (by rfl) ⟨801905, by rfl⟩ : syracuseStep 1069207 = 1603811) B1603811
theorem B2707607 : Blo 1068616 2707607 := bstep (se 1 (by rfl) ⟨2030705, by rfl⟩ : syracuseStep 2707607 = 4061411) B4061411
theorem B1069227 : Blo 1068616 1069227 := bstep (se 1 (by rfl) ⟨801920, by rfl⟩ : syracuseStep 1069227 = 1603841) B1603841
theorem B1069239 : Blo 1068616 1069239 := bstep (se 1 (by rfl) ⟨801929, by rfl⟩ : syracuseStep 1069239 = 1603859) B1603859
theorem B2412737 : Blo 1068616 2412737 := bstep (se 2 (by rfl) ⟨904776, by rfl⟩ : syracuseStep 2412737 = 1809553) B1809553
theorem B1069259 : Blo 1068616 1069259 := bstep (se 1 (by rfl) ⟨801944, by rfl⟩ : syracuseStep 1069259 = 1603889) B1603889
theorem B1069271 : Blo 1068616 1069271 := bstep (se 1 (by rfl) ⟨801953, by rfl⟩ : syracuseStep 1069271 = 1603907) B1603907
theorem B1069291 : Blo 1068616 1069291 := bstep (se 1 (by rfl) ⟨801968, by rfl⟩ : syracuseStep 1069291 = 1603937) B1603937
theorem B1069303 : Blo 1068616 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B1069323 : Blo 1068616 1069323 := bstep (se 1 (by rfl) ⟨801992, by rfl⟩ : syracuseStep 1069323 = 1603985) B1603985
theorem B1069335 : Blo 1068616 1069335 := bstep (se 1 (by rfl) ⟨802001, by rfl⟩ : syracuseStep 1069335 = 1604003) B1604003
theorem B1069355 : Blo 1068616 1069355 := bstep (se 1 (by rfl) ⟨802016, by rfl⟩ : syracuseStep 1069355 = 1604033) B1604033
theorem B1069367 : Blo 1068616 1069367 := bstep (se 1 (by rfl) ⟨802025, by rfl⟩ : syracuseStep 1069367 = 1604051) B1604051
theorem B1069387 : Blo 1068616 1069387 := bstep (se 1 (by rfl) ⟨802040, by rfl⟩ : syracuseStep 1069387 = 1604081) B1604081
theorem B1069399 : Blo 1068616 1069399 := bstep (se 1 (by rfl) ⟨802049, by rfl⟩ : syracuseStep 1069399 = 1604099) B1604099
theorem B12341605 : Blo 1068616 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B1069419 : Blo 1068616 1069419 := bstep (se 1 (by rfl) ⟨802064, by rfl⟩ : syracuseStep 1069419 = 1604129) B1604129
theorem B1069431 : Blo 1068616 1069431 := bstep (se 1 (by rfl) ⟨802073, by rfl⟩ : syracuseStep 1069431 = 1604147) B1604147
theorem B1069451 : Blo 1068616 1069451 := bstep (se 1 (by rfl) ⟨802088, by rfl⟩ : syracuseStep 1069451 = 1604177) B1604177
theorem B1069463 : Blo 1068616 1069463 := bstep (se 1 (by rfl) ⟨802097, by rfl⟩ : syracuseStep 1069463 = 1604195) B1604195
theorem B2412953 : Blo 1068616 2412953 := bstep (se 2 (by rfl) ⟨904857, by rfl⟩ : syracuseStep 2412953 = 1809715) B1809715
theorem B1069483 : Blo 1068616 1069483 := bstep (se 1 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 1069483 = 1604225) B1604225
theorem B1069495 : Blo 1068616 1069495 := bstep (se 1 (by rfl) ⟨802121, by rfl⟩ : syracuseStep 1069495 = 1604243) B1604243
theorem B1069515 : Blo 1068616 1069515 := bstep (se 1 (by rfl) ⟨802136, by rfl⟩ : syracuseStep 1069515 = 1604273) B1604273
theorem B1069527 : Blo 1068616 1069527 := bstep (se 1 (by rfl) ⟨802145, by rfl⟩ : syracuseStep 1069527 = 1604291) B1604291
theorem B1069547 : Blo 1068616 1069547 := bstep (se 1 (by rfl) ⟨802160, by rfl⟩ : syracuseStep 1069547 = 1604321) B1604321
theorem B2413043 : Blo 1068616 2413043 := bstep (se 1 (by rfl) ⟨1809782, by rfl⟩ : syracuseStep 2413043 = 3619565) B3619565
theorem B1069559 : Blo 1068616 1069559 := bstep (se 1 (by rfl) ⟨802169, by rfl⟩ : syracuseStep 1069559 = 1604339) B1604339
theorem B1069579 : Blo 1068616 1069579 := bstep (se 1 (by rfl) ⟨802184, by rfl⟩ : syracuseStep 1069579 = 1604369) B1604369
theorem B1069591 : Blo 1068616 1069591 := bstep (se 1 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 1069591 = 1604387) B1604387
theorem B2413079 : Blo 1068616 2413079 := bstep (se 1 (by rfl) ⟨1809809, by rfl⟩ : syracuseStep 2413079 = 3619619) B3619619
theorem B1069611 : Blo 1068616 1069611 := bstep (se 1 (by rfl) ⟨802208, by rfl⟩ : syracuseStep 1069611 = 1604417) B1604417
theorem B6869549 : Blo 1068616 6869549 := bstep (se 3 (by rfl) ⟨1288040, by rfl⟩ : syracuseStep 6869549 = 2576081) B2576081
theorem B1069623 : Blo 1068616 1069623 := bstep (se 1 (by rfl) ⟨802217, by rfl⟩ : syracuseStep 1069623 = 1604435) B1604435
theorem B1069643 : Blo 1068616 1069643 := bstep (se 1 (by rfl) ⟨802232, by rfl⟩ : syracuseStep 1069643 = 1604465) B1604465
theorem B1069655 : Blo 1068616 1069655 := bstep (se 1 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 1069655 = 1604483) B1604483
theorem B9130589 : Blo 1068616 9130589 := bstep (se 3 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 9130589 = 3423971) B3423971
theorem B1069675 : Blo 1068616 1069675 := bstep (se 1 (by rfl) ⟨802256, by rfl⟩ : syracuseStep 1069675 = 1604513) B1604513
theorem B1069687 : Blo 1068616 1069687 := bstep (se 1 (by rfl) ⟨802265, by rfl⟩ : syracuseStep 1069687 = 1604531) B1604531
theorem B1069707 : Blo 1068616 1069707 := bstep (se 1 (by rfl) ⟨802280, by rfl⟩ : syracuseStep 1069707 = 1604561) B1604561
theorem B1069719 : Blo 1068616 1069719 := bstep (se 1 (by rfl) ⟨802289, by rfl⟩ : syracuseStep 1069719 = 1604579) B1604579
theorem B1069739 : Blo 1068616 1069739 := bstep (se 1 (by rfl) ⟨802304, by rfl⟩ : syracuseStep 1069739 = 1604609) B1604609
theorem B4575923 : Blo 1068616 4575923 := bstep (se 1 (by rfl) ⟨3431942, by rfl⟩ : syracuseStep 4575923 = 6863885) B6863885
theorem B1069751 : Blo 1068616 1069751 := bstep (se 1 (by rfl) ⟨802313, by rfl⟩ : syracuseStep 1069751 = 1604627) B1604627
theorem B31707845 : Blo 1068616 31707845 := bstep (se 4 (by rfl) ⟨2972610, by rfl⟩ : syracuseStep 31707845 = 5945221) B5945221
theorem B1069771 : Blo 1068616 1069771 := bstep (se 1 (by rfl) ⟨802328, by rfl⟩ : syracuseStep 1069771 = 1604657) B1604657
theorem B2413259 : Blo 1068616 2413259 := bstep (se 1 (by rfl) ⟨1809944, by rfl⟩ : syracuseStep 2413259 = 3619889) B3619889
theorem B1069783 : Blo 1068616 1069783 := bstep (se 1 (by rfl) ⟨802337, by rfl⟩ : syracuseStep 1069783 = 1604675) B1604675
theorem B1069803 : Blo 1068616 1069803 := bstep (se 1 (by rfl) ⟨802352, by rfl⟩ : syracuseStep 1069803 = 1604705) B1604705
theorem B1069815 : Blo 1068616 1069815 := bstep (se 1 (by rfl) ⟨802361, by rfl⟩ : syracuseStep 1069815 = 1604723) B1604723
theorem B2413313 : Blo 1068616 2413313 := bstep (se 2 (by rfl) ⟨904992, by rfl⟩ : syracuseStep 2413313 = 1809985) B1809985
theorem B1069835 : Blo 1068616 1069835 := bstep (se 1 (by rfl) ⟨802376, by rfl⟩ : syracuseStep 1069835 = 1604753) B1604753
theorem B3855127 : Blo 1068616 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B1069847 : Blo 1068616 1069847 := bstep (se 1 (by rfl) ⟨802385, by rfl⟩ : syracuseStep 1069847 = 1604771) B1604771
theorem B1069867 : Blo 1068616 1069867 := bstep (se 1 (by rfl) ⟨802400, by rfl⟩ : syracuseStep 1069867 = 1604801) B1604801
theorem B2511667 : Blo 1068616 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B2708275 : Blo 1068616 2708275 := bstep (se 1 (by rfl) ⟨2031206, by rfl⟩ : syracuseStep 2708275 = 4062413) B4062413
theorem B1069879 : Blo 1068616 1069879 := bstep (se 1 (by rfl) ⟨802409, by rfl⟩ : syracuseStep 1069879 = 1604819) B1604819
theorem B1069899 : Blo 1068616 1069899 := bstep (se 1 (by rfl) ⟨802424, by rfl⟩ : syracuseStep 1069899 = 1604849) B1604849
theorem B1069911 : Blo 1068616 1069911 := bstep (se 1 (by rfl) ⟨802433, by rfl⟩ : syracuseStep 1069911 = 1604867) B1604867
theorem B1069931 : Blo 1068616 1069931 := bstep (se 1 (by rfl) ⟨802448, by rfl⟩ : syracuseStep 1069931 = 1604897) B1604897
theorem B1069943 : Blo 1068616 1069943 := bstep (se 1 (by rfl) ⟨802457, by rfl⟩ : syracuseStep 1069943 = 1604915) B1604915
theorem B1069963 : Blo 1068616 1069963 := bstep (se 1 (by rfl) ⟨802472, by rfl⟩ : syracuseStep 1069963 = 1604945) B1604945
theorem B1069975 : Blo 1068616 1069975 := bstep (se 1 (by rfl) ⟨802481, by rfl⟩ : syracuseStep 1069975 = 1604963) B1604963
theorem B1069995 : Blo 1068616 1069995 := bstep (se 1 (by rfl) ⟨802496, by rfl⟩ : syracuseStep 1069995 = 1604993) B1604993
theorem B1070007 : Blo 1068616 1070007 := bstep (se 1 (by rfl) ⟨802505, by rfl⟩ : syracuseStep 1070007 = 1605011) B1605011
theorem B2708417 : Blo 1068616 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B1070027 : Blo 1068616 1070027 := bstep (se 1 (by rfl) ⟨802520, by rfl⟩ : syracuseStep 1070027 = 1605041) B1605041
theorem B1070039 : Blo 1068616 1070039 := bstep (se 1 (by rfl) ⟨802529, by rfl⟩ : syracuseStep 1070039 = 1605059) B1605059
theorem B1070059 : Blo 1068616 1070059 := bstep (se 1 (by rfl) ⟨802544, by rfl⟩ : syracuseStep 1070059 = 1605089) B1605089
theorem B1070071 : Blo 1068616 1070071 := bstep (se 1 (by rfl) ⟨802553, by rfl⟩ : syracuseStep 1070071 = 1605107) B1605107
theorem B1070091 : Blo 1068616 1070091 := bstep (se 1 (by rfl) ⟨802568, by rfl⟩ : syracuseStep 1070091 = 1605137) B1605137
theorem B1070103 : Blo 1068616 1070103 := bstep (se 1 (by rfl) ⟨802577, by rfl⟩ : syracuseStep 1070103 = 1605155) B1605155
theorem B1070123 : Blo 1068616 1070123 := bstep (se 1 (by rfl) ⟨802592, by rfl⟩ : syracuseStep 1070123 = 1605185) B1605185
theorem B1070135 : Blo 1068616 1070135 := bstep (se 1 (by rfl) ⟨802601, by rfl⟩ : syracuseStep 1070135 = 1605203) B1605203
theorem B1070155 : Blo 1068616 1070155 := bstep (se 1 (by rfl) ⟨802616, by rfl⟩ : syracuseStep 1070155 = 1605233) B1605233
theorem B1070167 : Blo 1068616 1070167 := bstep (se 1 (by rfl) ⟨802625, by rfl⟩ : syracuseStep 1070167 = 1605251) B1605251
theorem B4969561 : Blo 1068616 4969561 := bstep (se 2 (by rfl) ⟨1863585, by rfl⟩ : syracuseStep 4969561 = 3727171) B3727171
theorem B1070187 : Blo 1068616 1070187 := bstep (se 1 (by rfl) ⟨802640, by rfl⟩ : syracuseStep 1070187 = 1605281) B1605281
theorem B1070199 : Blo 1068616 1070199 := bstep (se 1 (by rfl) ⟨802649, by rfl⟩ : syracuseStep 1070199 = 1605299) B1605299
theorem B1070219 : Blo 1068616 1070219 := bstep (se 1 (by rfl) ⟨802664, by rfl⟩ : syracuseStep 1070219 = 1605329) B1605329
theorem B1070231 : Blo 1068616 1070231 := bstep (se 1 (by rfl) ⟨802673, by rfl⟩ : syracuseStep 1070231 = 1605347) B1605347
theorem B1070251 : Blo 1068616 1070251 := bstep (se 1 (by rfl) ⟨802688, by rfl⟩ : syracuseStep 1070251 = 1605377) B1605377
theorem B7722161 : Blo 1068616 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1070263 : Blo 1068616 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B1070283 : Blo 1068616 1070283 := bstep (se 1 (by rfl) ⟨802712, by rfl⟩ : syracuseStep 1070283 = 1605425) B1605425
theorem B1070295 : Blo 1068616 1070295 := bstep (se 1 (by rfl) ⟨802721, by rfl⟩ : syracuseStep 1070295 = 1605443) B1605443
theorem B1070315 : Blo 1068616 1070315 := bstep (se 1 (by rfl) ⟨802736, by rfl⟩ : syracuseStep 1070315 = 1605473) B1605473
theorem B1070327 : Blo 1068616 1070327 := bstep (se 1 (by rfl) ⟨802745, by rfl⟩ : syracuseStep 1070327 = 1605491) B1605491
theorem B1070347 : Blo 1068616 1070347 := bstep (se 1 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 1070347 = 1605521) B1605521
theorem B1070359 : Blo 1068616 1070359 := bstep (se 1 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 1070359 = 1605539) B1605539
theorem B1070379 : Blo 1068616 1070379 := bstep (se 1 (by rfl) ⟨802784, by rfl⟩ : syracuseStep 1070379 = 1605569) B1605569
theorem B1070391 : Blo 1068616 1070391 := bstep (se 1 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 1070391 = 1605587) B1605587
theorem B1070411 : Blo 1068616 1070411 := bstep (se 1 (by rfl) ⟨802808, by rfl⟩ : syracuseStep 1070411 = 1605617) B1605617
theorem B1070423 : Blo 1068616 1070423 := bstep (se 1 (by rfl) ⟨802817, by rfl⟩ : syracuseStep 1070423 = 1605635) B1605635
theorem B1070443 : Blo 1068616 1070443 := bstep (se 1 (by rfl) ⟨802832, by rfl⟩ : syracuseStep 1070443 = 1605665) B1605665
theorem B1070455 : Blo 1068616 1070455 := bstep (se 1 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 1070455 = 1605683) B1605683
theorem B1070475 : Blo 1068616 1070475 := bstep (se 1 (by rfl) ⟨802856, by rfl⟩ : syracuseStep 1070475 = 1605713) B1605713
theorem B1070487 : Blo 1068616 1070487 := bstep (se 1 (by rfl) ⟨802865, by rfl⟩ : syracuseStep 1070487 = 1605731) B1605731
theorem B1070507 : Blo 1068616 1070507 := bstep (se 1 (by rfl) ⟨802880, by rfl⟩ : syracuseStep 1070507 = 1605761) B1605761
theorem B1070519 : Blo 1068616 1070519 := bstep (se 1 (by rfl) ⟨802889, by rfl⟩ : syracuseStep 1070519 = 1605779) B1605779
theorem B1070539 : Blo 1068616 1070539 := bstep (se 1 (by rfl) ⟨802904, by rfl⟩ : syracuseStep 1070539 = 1605809) B1605809
theorem B1070551 : Blo 1068616 1070551 := bstep (se 1 (by rfl) ⟨802913, by rfl⟩ : syracuseStep 1070551 = 1605827) B1605827
theorem B3855833 : Blo 1068616 3855833 := bstep (se 2 (by rfl) ⟨1445937, by rfl⟩ : syracuseStep 3855833 = 2891875) B2891875
theorem B1070571 : Blo 1068616 1070571 := bstep (se 1 (by rfl) ⟨802928, by rfl⟩ : syracuseStep 1070571 = 1605857) B1605857
theorem B1070583 : Blo 1068616 1070583 := bstep (se 1 (by rfl) ⟨802937, by rfl⟩ : syracuseStep 1070583 = 1605875) B1605875
theorem B1070603 : Blo 1068616 1070603 := bstep (se 1 (by rfl) ⟨802952, by rfl⟩ : syracuseStep 1070603 = 1605905) B1605905
theorem B1070615 : Blo 1068616 1070615 := bstep (se 1 (by rfl) ⟨802961, by rfl⟩ : syracuseStep 1070615 = 1605923) B1605923
theorem B1070635 : Blo 1068616 1070635 := bstep (se 1 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 1070635 = 1605953) B1605953
theorem B5428781 : Blo 1068616 5428781 := bstep (se 3 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 5428781 = 2035793) B2035793
theorem B2315827 : Blo 1068616 2315827 := bstep (se 1 (by rfl) ⟨1736870, by rfl⟩ : syracuseStep 2315827 = 3473741) B3473741
theorem B1070647 : Blo 1068616 1070647 := bstep (se 1 (by rfl) ⟨802985, by rfl⟩ : syracuseStep 1070647 = 1605971) B1605971
theorem B1070667 : Blo 1068616 1070667 := bstep (se 1 (by rfl) ⟨803000, by rfl⟩ : syracuseStep 1070667 = 1606001) B1606001
theorem B166581845 : Blo 1068616 166581845 := bstep (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) B1952131
theorem B1070679 : Blo 1068616 1070679 := bstep (se 1 (by rfl) ⟨803009, by rfl⟩ : syracuseStep 1070679 = 1606019) B1606019
theorem B1070699 : Blo 1068616 1070699 := bstep (se 1 (by rfl) ⟨803024, by rfl⟩ : syracuseStep 1070699 = 1606049) B1606049
theorem B1070711 : Blo 1068616 1070711 := bstep (se 1 (by rfl) ⟨803033, by rfl⟩ : syracuseStep 1070711 = 1606067) B1606067
theorem B1070731 : Blo 1068616 1070731 := bstep (se 1 (by rfl) ⟨803048, by rfl⟩ : syracuseStep 1070731 = 1606097) B1606097
theorem B1070743 : Blo 1068616 1070743 := bstep (se 1 (by rfl) ⟨803057, by rfl⟩ : syracuseStep 1070743 = 1606115) B1606115
theorem B1070763 : Blo 1068616 1070763 := bstep (se 1 (by rfl) ⟨803072, by rfl⟩ : syracuseStep 1070763 = 1606145) B1606145
theorem B1070775 : Blo 1068616 1070775 := bstep (se 1 (by rfl) ⟨803081, by rfl⟩ : syracuseStep 1070775 = 1606163) B1606163
theorem B1070795 : Blo 1068616 1070795 := bstep (se 1 (by rfl) ⟨803096, by rfl⟩ : syracuseStep 1070795 = 1606193) B1606193
theorem B1070807 : Blo 1068616 1070807 := bstep (se 1 (by rfl) ⟨803105, by rfl⟩ : syracuseStep 1070807 = 1606211) B1606211
theorem B1070827 : Blo 1068616 1070827 := bstep (se 1 (by rfl) ⟨803120, by rfl⟩ : syracuseStep 1070827 = 1606241) B1606241
theorem B1070839 : Blo 1068616 1070839 := bstep (se 1 (by rfl) ⟨803129, by rfl⟩ : syracuseStep 1070839 = 1606259) B1606259
theorem B1070859 : Blo 1068616 1070859 := bstep (se 1 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 1070859 = 1606289) B1606289
theorem B1070871 : Blo 1068616 1070871 := bstep (se 1 (by rfl) ⟨803153, by rfl⟩ : syracuseStep 1070871 = 1606307) B1606307
theorem B1070891 : Blo 1068616 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B1070903 : Blo 1068616 1070903 := bstep (se 1 (by rfl) ⟨803177, by rfl⟩ : syracuseStep 1070903 = 1606355) B1606355
theorem B1070923 : Blo 1068616 1070923 := bstep (se 1 (by rfl) ⟨803192, by rfl⟩ : syracuseStep 1070923 = 1606385) B1606385
theorem B1070935 : Blo 1068616 1070935 := bstep (se 1 (by rfl) ⟨803201, by rfl⟩ : syracuseStep 1070935 = 1606403) B1606403
theorem B1070955 : Blo 1068616 1070955 := bstep (se 1 (by rfl) ⟨803216, by rfl⟩ : syracuseStep 1070955 = 1606433) B1606433
theorem B1070967 : Blo 1068616 1070967 := bstep (se 1 (by rfl) ⟨803225, by rfl⟩ : syracuseStep 1070967 = 1606451) B1606451
theorem B1070987 : Blo 1068616 1070987 := bstep (se 1 (by rfl) ⟨803240, by rfl⟩ : syracuseStep 1070987 = 1606481) B1606481
theorem B1070999 : Blo 1068616 1070999 := bstep (se 1 (by rfl) ⟨803249, by rfl⟩ : syracuseStep 1070999 = 1606499) B1606499
theorem B1071019 : Blo 1068616 1071019 := bstep (se 1 (by rfl) ⟨803264, by rfl⟩ : syracuseStep 1071019 = 1606529) B1606529
theorem B1071031 : Blo 1068616 1071031 := bstep (se 1 (by rfl) ⟨803273, by rfl⟩ : syracuseStep 1071031 = 1606547) B1606547
theorem B1071051 : Blo 1068616 1071051 := bstep (se 1 (by rfl) ⟨803288, by rfl⟩ : syracuseStep 1071051 = 1606577) B1606577
theorem B1071063 : Blo 1068616 1071063 := bstep (se 1 (by rfl) ⟨803297, by rfl⟩ : syracuseStep 1071063 = 1606595) B1606595
theorem B1071083 : Blo 1068616 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B1071095 : Blo 1068616 1071095 := bstep (se 1 (by rfl) ⟨803321, by rfl⟩ : syracuseStep 1071095 = 1606643) B1606643
theorem B1071115 : Blo 1068616 1071115 := bstep (se 1 (by rfl) ⟨803336, by rfl⟩ : syracuseStep 1071115 = 1606673) B1606673
theorem B1071127 : Blo 1068616 1071127 := bstep (se 1 (by rfl) ⟨803345, by rfl⟩ : syracuseStep 1071127 = 1606691) B1606691
theorem B1071147 : Blo 1068616 1071147 := bstep (se 1 (by rfl) ⟨803360, by rfl⟩ : syracuseStep 1071147 = 1606721) B1606721
theorem B1071159 : Blo 1068616 1071159 := bstep (se 1 (by rfl) ⟨803369, by rfl⟩ : syracuseStep 1071159 = 1606739) B1606739
theorem B1202251 : Blo 1068616 1202251 := bstep (se 1 (by rfl) ⟨901688, by rfl⟩ : syracuseStep 1202251 = 1803377) B1803377
theorem B1071179 : Blo 1068616 1071179 := bstep (se 1 (by rfl) ⟨803384, by rfl⟩ : syracuseStep 1071179 = 1606769) B1606769
theorem B1071191 : Blo 1068616 1071191 := bstep (se 1 (by rfl) ⟨803393, by rfl⟩ : syracuseStep 1071191 = 1606787) B1606787
theorem B1071211 : Blo 1068616 1071211 := bstep (se 1 (by rfl) ⟨803408, by rfl⟩ : syracuseStep 1071211 = 1606817) B1606817
theorem B1071223 : Blo 1068616 1071223 := bstep (se 1 (by rfl) ⟨803417, by rfl⟩ : syracuseStep 1071223 = 1606835) B1606835
theorem B1071243 : Blo 1068616 1071243 := bstep (se 1 (by rfl) ⟨803432, by rfl⟩ : syracuseStep 1071243 = 1606865) B1606865
theorem B1071255 : Blo 1068616 1071255 := bstep (se 1 (by rfl) ⟨803441, by rfl⟩ : syracuseStep 1071255 = 1606883) B1606883
theorem B2283673 : Blo 1068616 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B1071275 : Blo 1068616 1071275 := bstep (se 1 (by rfl) ⟨803456, by rfl⟩ : syracuseStep 1071275 = 1606913) B1606913
theorem B2709683 : Blo 1068616 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B1202359 : Blo 1068616 1202359 := bstep (se 1 (by rfl) ⟨901769, by rfl⟩ : syracuseStep 1202359 = 1803539) B1803539
theorem B1071287 : Blo 1068616 1071287 := bstep (se 1 (by rfl) ⟨803465, by rfl⟩ : syracuseStep 1071287 = 1606931) B1606931
theorem B1071307 : Blo 1068616 1071307 := bstep (se 1 (by rfl) ⟨803480, by rfl⟩ : syracuseStep 1071307 = 1606961) B1606961
theorem B1071319 : Blo 1068616 1071319 := bstep (se 1 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 1071319 = 1606979) B1606979
theorem B1071339 : Blo 1068616 1071339 := bstep (se 1 (by rfl) ⟨803504, by rfl⟩ : syracuseStep 1071339 = 1607009) B1607009
theorem B1071351 : Blo 1068616 1071351 := bstep (se 1 (by rfl) ⟨803513, by rfl⟩ : syracuseStep 1071351 = 1607027) B1607027
theorem B1071371 : Blo 1068616 1071371 := bstep (se 1 (by rfl) ⟨803528, by rfl⟩ : syracuseStep 1071371 = 1607057) B1607057
theorem B1071383 : Blo 1068616 1071383 := bstep (se 1 (by rfl) ⟨803537, by rfl⟩ : syracuseStep 1071383 = 1607075) B1607075
theorem B1071403 : Blo 1068616 1071403 := bstep (se 1 (by rfl) ⟨803552, by rfl⟩ : syracuseStep 1071403 = 1607105) B1607105
theorem B13031725 : Blo 1068616 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B1071415 : Blo 1068616 1071415 := bstep (se 1 (by rfl) ⟨803561, by rfl⟩ : syracuseStep 1071415 = 1607123) B1607123
theorem B1071435 : Blo 1068616 1071435 := bstep (se 1 (by rfl) ⟨803576, by rfl⟩ : syracuseStep 1071435 = 1607153) B1607153
theorem B1071447 : Blo 1068616 1071447 := bstep (se 1 (by rfl) ⟨803585, by rfl⟩ : syracuseStep 1071447 = 1607171) B1607171
theorem B1202539 : Blo 1068616 1202539 := bstep (se 1 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 1202539 = 1803809) B1803809
theorem B1071467 : Blo 1068616 1071467 := bstep (se 1 (by rfl) ⟨803600, by rfl⟩ : syracuseStep 1071467 = 1607201) B1607201
theorem B1071479 : Blo 1068616 1071479 := bstep (se 1 (by rfl) ⟨803609, by rfl⟩ : syracuseStep 1071479 = 1607219) B1607219
theorem B1071499 : Blo 1068616 1071499 := bstep (se 1 (by rfl) ⟨803624, by rfl⟩ : syracuseStep 1071499 = 1607249) B1607249
theorem B1071511 : Blo 1068616 1071511 := bstep (se 1 (by rfl) ⟨803633, by rfl⟩ : syracuseStep 1071511 = 1607267) B1607267
theorem B1071531 : Blo 1068616 1071531 := bstep (se 1 (by rfl) ⟨803648, by rfl⟩ : syracuseStep 1071531 = 1607297) B1607297
theorem B1071543 : Blo 1068616 1071543 := bstep (se 1 (by rfl) ⟨803657, by rfl⟩ : syracuseStep 1071543 = 1607315) B1607315
theorem B1071563 : Blo 1068616 1071563 := bstep (se 1 (by rfl) ⟨803672, by rfl⟩ : syracuseStep 1071563 = 1607345) B1607345
theorem B8116685 : Blo 1068616 8116685 := bstep (se 3 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 8116685 = 3043757) B3043757
theorem B1202647 : Blo 1068616 1202647 := bstep (se 1 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 1202647 = 1803971) B1803971
theorem B1071575 : Blo 1068616 1071575 := bstep (se 1 (by rfl) ⟨803681, by rfl⟩ : syracuseStep 1071575 = 1607363) B1607363
theorem B1071595 : Blo 1068616 1071595 := bstep (se 1 (by rfl) ⟨803696, by rfl⟩ : syracuseStep 1071595 = 1607393) B1607393
theorem B1071607 : Blo 1068616 1071607 := bstep (se 1 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 1071607 = 1607411) B1607411
theorem B1071627 : Blo 1068616 1071627 := bstep (se 1 (by rfl) ⟨803720, by rfl⟩ : syracuseStep 1071627 = 1607441) B1607441
theorem B1071639 : Blo 1068616 1071639 := bstep (se 1 (by rfl) ⟨803729, by rfl⟩ : syracuseStep 1071639 = 1607459) B1607459
theorem B1071659 : Blo 1068616 1071659 := bstep (se 1 (by rfl) ⟨803744, by rfl⟩ : syracuseStep 1071659 = 1607489) B1607489
theorem B1071671 : Blo 1068616 1071671 := bstep (se 1 (by rfl) ⟨803753, by rfl⟩ : syracuseStep 1071671 = 1607507) B1607507
theorem B1071691 : Blo 1068616 1071691 := bstep (se 1 (by rfl) ⟨803768, by rfl⟩ : syracuseStep 1071691 = 1607537) B1607537
theorem B1071703 : Blo 1068616 1071703 := bstep (se 1 (by rfl) ⟨803777, by rfl⟩ : syracuseStep 1071703 = 1607555) B1607555
theorem B1071723 : Blo 1068616 1071723 := bstep (se 1 (by rfl) ⟨803792, by rfl⟩ : syracuseStep 1071723 = 1607585) B1607585
theorem B1071735 : Blo 1068616 1071735 := bstep (se 1 (by rfl) ⟨803801, by rfl⟩ : syracuseStep 1071735 = 1607603) B1607603
theorem B1202827 : Blo 1068616 1202827 := bstep (se 1 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 1202827 = 1804241) B1804241
theorem B1071755 : Blo 1068616 1071755 := bstep (se 1 (by rfl) ⟨803816, by rfl⟩ : syracuseStep 1071755 = 1607633) B1607633
theorem B1071767 : Blo 1068616 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B1071787 : Blo 1068616 1071787 := bstep (se 1 (by rfl) ⟨803840, by rfl⟩ : syracuseStep 1071787 = 1607681) B1607681
theorem B1071799 : Blo 1068616 1071799 := bstep (se 1 (by rfl) ⟨803849, by rfl⟩ : syracuseStep 1071799 = 1607699) B1607699
theorem B2710219 : Blo 1068616 2710219 := bstep (se 1 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 2710219 = 4065329) B4065329
theorem B1071819 : Blo 1068616 1071819 := bstep (se 1 (by rfl) ⟨803864, by rfl⟩ : syracuseStep 1071819 = 1607729) B1607729
theorem B1071831 : Blo 1068616 1071831 := bstep (se 1 (by rfl) ⟨803873, by rfl⟩ : syracuseStep 1071831 = 1607747) B1607747
theorem B1071851 : Blo 1068616 1071851 := bstep (se 1 (by rfl) ⟨803888, by rfl⟩ : syracuseStep 1071851 = 1607777) B1607777
theorem B1202935 : Blo 1068616 1202935 := bstep (se 1 (by rfl) ⟨902201, by rfl⟩ : syracuseStep 1202935 = 1804403) B1804403
theorem B1071863 : Blo 1068616 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B1071883 : Blo 1068616 1071883 := bstep (se 1 (by rfl) ⟨803912, by rfl⟩ : syracuseStep 1071883 = 1607825) B1607825
theorem B1071895 : Blo 1068616 1071895 := bstep (se 1 (by rfl) ⟨803921, by rfl⟩ : syracuseStep 1071895 = 1607843) B1607843
theorem B1071915 : Blo 1068616 1071915 := bstep (se 1 (by rfl) ⟨803936, by rfl⟩ : syracuseStep 1071915 = 1607873) B1607873
theorem B1071927 : Blo 1068616 1071927 := bstep (se 1 (by rfl) ⟨803945, by rfl⟩ : syracuseStep 1071927 = 1607891) B1607891
theorem B1071947 : Blo 1068616 1071947 := bstep (se 1 (by rfl) ⟨803960, by rfl⟩ : syracuseStep 1071947 = 1607921) B1607921
theorem B1071959 : Blo 1068616 1071959 := bstep (se 1 (by rfl) ⟨803969, by rfl⟩ : syracuseStep 1071959 = 1607939) B1607939
theorem B2710361 : Blo 1068616 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B1071979 : Blo 1068616 1071979 := bstep (se 1 (by rfl) ⟨803984, by rfl⟩ : syracuseStep 1071979 = 1607969) B1607969
theorem B1071991 : Blo 1068616 1071991 := bstep (se 1 (by rfl) ⟨803993, by rfl⟩ : syracuseStep 1071991 = 1607987) B1607987
theorem B1072011 : Blo 1068616 1072011 := bstep (se 1 (by rfl) ⟨804008, by rfl⟩ : syracuseStep 1072011 = 1608017) B1608017
theorem B1072023 : Blo 1068616 1072023 := bstep (se 1 (by rfl) ⟨804017, by rfl⟩ : syracuseStep 1072023 = 1608035) B1608035
theorem B1203115 : Blo 1068616 1203115 := bstep (se 1 (by rfl) ⟨902336, by rfl⟩ : syracuseStep 1203115 = 1804673) B1804673
theorem B1072043 : Blo 1068616 1072043 := bstep (se 1 (by rfl) ⟨804032, by rfl⟩ : syracuseStep 1072043 = 1608065) B1608065
theorem B8117171 : Blo 1068616 8117171 := bstep (se 1 (by rfl) ⟨6087878, by rfl⟩ : syracuseStep 8117171 = 12175757) B12175757
theorem B1072055 : Blo 1068616 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1072075 : Blo 1068616 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B1072087 : Blo 1068616 1072087 := bstep (se 1 (by rfl) ⟨804065, by rfl⟩ : syracuseStep 1072087 = 1608131) B1608131
theorem B1072107 : Blo 1068616 1072107 := bstep (se 1 (by rfl) ⟨804080, by rfl⟩ : syracuseStep 1072107 = 1608161) B1608161
theorem B1072119 : Blo 1068616 1072119 := bstep (se 1 (by rfl) ⟨804089, by rfl⟩ : syracuseStep 1072119 = 1608179) B1608179
theorem B1072139 : Blo 1068616 1072139 := bstep (se 1 (by rfl) ⟨804104, by rfl⟩ : syracuseStep 1072139 = 1608209) B1608209
theorem B1203223 : Blo 1068616 1203223 := bstep (se 1 (by rfl) ⟨902417, by rfl⟩ : syracuseStep 1203223 = 1804835) B1804835
theorem B1072151 : Blo 1068616 1072151 := bstep (se 1 (by rfl) ⟨804113, by rfl⟩ : syracuseStep 1072151 = 1608227) B1608227
theorem B1072171 : Blo 1068616 1072171 := bstep (se 1 (by rfl) ⟨804128, by rfl⟩ : syracuseStep 1072171 = 1608257) B1608257
theorem B1072183 : Blo 1068616 1072183 := bstep (se 1 (by rfl) ⟨804137, by rfl⟩ : syracuseStep 1072183 = 1608275) B1608275
theorem B1072203 : Blo 1068616 1072203 := bstep (se 1 (by rfl) ⟨804152, by rfl⟩ : syracuseStep 1072203 = 1608305) B1608305
theorem B1072215 : Blo 1068616 1072215 := bstep (se 1 (by rfl) ⟨804161, by rfl⟩ : syracuseStep 1072215 = 1608323) B1608323
theorem B1072235 : Blo 1068616 1072235 := bstep (se 1 (by rfl) ⟨804176, by rfl⟩ : syracuseStep 1072235 = 1608353) B1608353
theorem B1072247 : Blo 1068616 1072247 := bstep (se 1 (by rfl) ⟨804185, by rfl⟩ : syracuseStep 1072247 = 1608371) B1608371
theorem B1072267 : Blo 1068616 1072267 := bstep (se 1 (by rfl) ⟨804200, by rfl⟩ : syracuseStep 1072267 = 1608401) B1608401
theorem B1072279 : Blo 1068616 1072279 := bstep (se 1 (by rfl) ⟨804209, by rfl⟩ : syracuseStep 1072279 = 1608419) B1608419
theorem B1072299 : Blo 1068616 1072299 := bstep (se 1 (by rfl) ⟨804224, by rfl⟩ : syracuseStep 1072299 = 1608449) B1608449
theorem B1072311 : Blo 1068616 1072311 := bstep (se 1 (by rfl) ⟨804233, by rfl⟩ : syracuseStep 1072311 = 1608467) B1608467
theorem B1203403 : Blo 1068616 1203403 := bstep (se 1 (by rfl) ⟨902552, by rfl⟩ : syracuseStep 1203403 = 1805105) B1805105
theorem B1072331 : Blo 1068616 1072331 := bstep (se 1 (by rfl) ⟨804248, by rfl⟩ : syracuseStep 1072331 = 1608497) B1608497
theorem B1072343 : Blo 1068616 1072343 := bstep (se 1 (by rfl) ⟨804257, by rfl⟩ : syracuseStep 1072343 = 1608515) B1608515
theorem B1072363 : Blo 1068616 1072363 := bstep (se 1 (by rfl) ⟨804272, by rfl⟩ : syracuseStep 1072363 = 1608545) B1608545
theorem B1072375 : Blo 1068616 1072375 := bstep (se 1 (by rfl) ⟨804281, by rfl⟩ : syracuseStep 1072375 = 1608563) B1608563
theorem B1072395 : Blo 1068616 1072395 := bstep (se 1 (by rfl) ⟨804296, by rfl⟩ : syracuseStep 1072395 = 1608593) B1608593
theorem B1072407 : Blo 1068616 1072407 := bstep (se 1 (by rfl) ⟨804305, by rfl⟩ : syracuseStep 1072407 = 1608611) B1608611
theorem B1072427 : Blo 1068616 1072427 := bstep (se 1 (by rfl) ⟨804320, by rfl⟩ : syracuseStep 1072427 = 1608641) B1608641
theorem B1203511 : Blo 1068616 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B1072439 : Blo 1068616 1072439 := bstep (se 1 (by rfl) ⟨804329, by rfl⟩ : syracuseStep 1072439 = 1608659) B1608659
theorem B11132225 : Blo 1068616 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B1072459 : Blo 1068616 1072459 := bstep (se 1 (by rfl) ⟨804344, by rfl⟩ : syracuseStep 1072459 = 1608689) B1608689
theorem B1072471 : Blo 1068616 1072471 := bstep (se 1 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 1072471 = 1608707) B1608707
theorem B1072491 : Blo 1068616 1072491 := bstep (se 1 (by rfl) ⟨804368, by rfl⟩ : syracuseStep 1072491 = 1608737) B1608737
theorem B1072503 : Blo 1068616 1072503 := bstep (se 1 (by rfl) ⟨804377, by rfl⟩ : syracuseStep 1072503 = 1608755) B1608755
theorem B1072523 : Blo 1068616 1072523 := bstep (se 1 (by rfl) ⟨804392, by rfl⟩ : syracuseStep 1072523 = 1608785) B1608785
theorem B1072535 : Blo 1068616 1072535 := bstep (se 1 (by rfl) ⟨804401, by rfl⟩ : syracuseStep 1072535 = 1608803) B1608803
theorem B1072555 : Blo 1068616 1072555 := bstep (se 1 (by rfl) ⟨804416, by rfl⟩ : syracuseStep 1072555 = 1608833) B1608833
theorem B1072567 : Blo 1068616 1072567 := bstep (se 1 (by rfl) ⟨804425, by rfl⟩ : syracuseStep 1072567 = 1608851) B1608851
theorem B1072587 : Blo 1068616 1072587 := bstep (se 1 (by rfl) ⟨804440, by rfl⟩ : syracuseStep 1072587 = 1608881) B1608881
theorem B1072599 : Blo 1068616 1072599 := bstep (se 1 (by rfl) ⟨804449, by rfl⟩ : syracuseStep 1072599 = 1608899) B1608899
theorem B1203691 : Blo 1068616 1203691 := bstep (se 1 (by rfl) ⟨902768, by rfl⟩ : syracuseStep 1203691 = 1805537) B1805537
theorem B1203799 : Blo 1068616 1203799 := bstep (se 1 (by rfl) ⟨902849, by rfl⟩ : syracuseStep 1203799 = 1805699) B1805699
theorem B2711191 : Blo 1068616 2711191 := bstep (se 1 (by rfl) ⟨2033393, by rfl⟩ : syracuseStep 2711191 = 4066787) B4066787
theorem B1203979 : Blo 1068616 1203979 := bstep (se 1 (by rfl) ⟨902984, by rfl⟩ : syracuseStep 1203979 = 1805969) B1805969
theorem B14868269 : Blo 1068616 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B12345205 : Blo 1068616 12345205 := bstep (se 5 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 12345205 = 1157363) B1157363
theorem B1204087 : Blo 1068616 1204087 := bstep (se 1 (by rfl) ⟨903065, by rfl⟩ : syracuseStep 1204087 = 1806131) B1806131
theorem B1204267 : Blo 1068616 1204267 := bstep (se 1 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 1204267 = 1806401) B1806401
theorem B2711627 : Blo 1068616 2711627 := bstep (se 1 (by rfl) ⟨2033720, by rfl⟩ : syracuseStep 2711627 = 4067441) B4067441
theorem B1204375 : Blo 1068616 1204375 := bstep (se 1 (by rfl) ⟨903281, by rfl⟩ : syracuseStep 1204375 = 1806563) B1806563
theorem B3662027 : Blo 1068616 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B2285825 : Blo 1068616 2285825 := bstep (se 2 (by rfl) ⟨857184, by rfl⟩ : syracuseStep 2285825 = 1714369) B1714369
theorem B1204555 : Blo 1068616 1204555 := bstep (se 1 (by rfl) ⟨903416, by rfl⟩ : syracuseStep 1204555 = 1806833) B1806833
theorem B2285911 : Blo 1068616 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B8118629 : Blo 1068616 8118629 := bstep (se 4 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 8118629 = 1522243) B1522243
theorem B4579715 : Blo 1068616 4579715 := bstep (se 1 (by rfl) ⟨3434786, by rfl⟩ : syracuseStep 4579715 = 6869573) B6869573
theorem B5497267 : Blo 1068616 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B1204663 : Blo 1068616 1204663 := bstep (se 1 (by rfl) ⟨903497, by rfl⟩ : syracuseStep 1204663 = 1806995) B1806995
theorem B2712001 : Blo 1068616 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B1630681 : Blo 1068616 1630681 := bstep (se 2 (by rfl) ⟨611505, by rfl⟩ : syracuseStep 1630681 = 1223011) B1223011
theorem B1204843 : Blo 1068616 1204843 := bstep (se 1 (by rfl) ⟨903632, by rfl⟩ : syracuseStep 1204843 = 1807265) B1807265
theorem B1204951 : Blo 1068616 1204951 := bstep (se 1 (by rfl) ⟨903713, by rfl⟩ : syracuseStep 1204951 = 1807427) B1807427
theorem B4580057 : Blo 1068616 4580057 := bstep (se 2 (by rfl) ⟨1717521, by rfl⟩ : syracuseStep 4580057 = 3435043) B3435043
theorem B8119115 : Blo 1068616 8119115 := bstep (se 1 (by rfl) ⟨6089336, by rfl⟩ : syracuseStep 8119115 = 12178673) B12178673
theorem B1205131 : Blo 1068616 1205131 := bstep (se 1 (by rfl) ⟨903848, by rfl⟩ : syracuseStep 1205131 = 1807697) B1807697
theorem B10281907 : Blo 1068616 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B1205239 : Blo 1068616 1205239 := bstep (se 1 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 1205239 = 1807859) B1807859
theorem B2712599 : Blo 1068616 2712599 := bstep (se 1 (by rfl) ⟨2034449, by rfl⟩ : syracuseStep 2712599 = 4068899) B4068899
theorem B2286731 : Blo 1068616 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B1205419 : Blo 1068616 1205419 := bstep (se 1 (by rfl) ⟨904064, by rfl⟩ : syracuseStep 1205419 = 1808129) B1808129
theorem B1926359 : Blo 1068616 1926359 := bstep (se 1 (by rfl) ⟨1444769, by rfl⟩ : syracuseStep 1926359 = 2889539) B2889539
theorem B1205527 : Blo 1068616 1205527 := bstep (se 1 (by rfl) ⟨904145, by rfl⟩ : syracuseStep 1205527 = 1808291) B1808291
theorem B1205707 : Blo 1068616 1205707 := bstep (se 1 (by rfl) ⟨904280, by rfl⟩ : syracuseStep 1205707 = 1808561) B1808561
theorem B1205815 : Blo 1068616 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B3860099 : Blo 1068616 3860099 := bstep (se 1 (by rfl) ⟨2895074, by rfl⟩ : syracuseStep 3860099 = 5790149) B5790149
theorem B1205995 : Blo 1068616 1205995 := bstep (se 1 (by rfl) ⟨904496, by rfl⟩ : syracuseStep 1205995 = 1808993) B1808993
theorem B2713409 : Blo 1068616 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B1206103 : Blo 1068616 1206103 := bstep (se 1 (by rfl) ⟨904577, by rfl⟩ : syracuseStep 1206103 = 1809155) B1809155
theorem B4122461 : Blo 1068616 4122461 := bstep (se 3 (by rfl) ⟨772961, by rfl⟩ : syracuseStep 4122461 = 1545923) B1545923
theorem B21981107 : Blo 1068616 21981107 := bstep (se 1 (by rfl) ⟨16485830, by rfl⟩ : syracuseStep 21981107 = 32971661) B32971661
theorem B1206283 : Blo 1068616 1206283 := bstep (se 1 (by rfl) ⟨904712, by rfl⟩ : syracuseStep 1206283 = 1809425) B1809425
theorem B6088769 : Blo 1068616 6088769 := bstep (se 2 (by rfl) ⟨2283288, by rfl⟩ : syracuseStep 6088769 = 4566577) B4566577
theorem B29321291 : Blo 1068616 29321291 := bstep (se 1 (by rfl) ⟨21990968, by rfl⟩ : syracuseStep 29321291 = 43981937) B43981937
theorem B2287705 : Blo 1068616 2287705 := bstep (se 2 (by rfl) ⟨857889, by rfl⟩ : syracuseStep 2287705 = 1715779) B1715779
theorem B1206391 : Blo 1068616 1206391 := bstep (se 1 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 1206391 = 1809587) B1809587
theorem B12216581 : Blo 1068616 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B8677667 : Blo 1068616 8677667 := bstep (se 1 (by rfl) ⟨6508250, by rfl⟩ : syracuseStep 8677667 = 13016501) B13016501
theorem B1206571 : Blo 1068616 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B2713945 : Blo 1068616 2713945 := bstep (se 2 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 2713945 = 2035459) B2035459
theorem B1206679 : Blo 1068616 1206679 := bstep (se 1 (by rfl) ⟨905009, by rfl⟩ : syracuseStep 1206679 = 1810019) B1810019
theorem B4057523 : Blo 1068616 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B1927627 : Blo 1068616 1927627 := bstep (se 1 (by rfl) ⟨1445720, by rfl⟩ : syracuseStep 1927627 = 2891441) B2891441
theorem B2058905 : Blo 1068616 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B13003697 : Blo 1068616 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B19557445 : Blo 1068616 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B1928407 : Blo 1068616 1928407 := bstep (se 1 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 1928407 = 2892611) B2892611
theorem B2715059 : Blo 1068616 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B7728961 : Blo 1068616 7728961 := bstep (se 2 (by rfl) ⟨2898360, by rfl⟩ : syracuseStep 7728961 = 5796721) B5796721
theorem B3043165 : Blo 1068616 3043165 := bstep (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) B1141187
theorem B4059011 : Blo 1068616 4059011 := bstep (se 1 (by rfl) ⟨3044258, by rfl⟩ : syracuseStep 4059011 = 6088517) B6088517
theorem B3862579 : Blo 1068616 3862579 := bstep (se 1 (by rfl) ⟨2896934, by rfl⟩ : syracuseStep 3862579 = 5793869) B5793869
theorem B11006027 : Blo 1068616 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B7729253 : Blo 1068616 7729253 := bstep (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) B1449235
theorem B3043507 : Blo 1068616 3043507 := bstep (se 1 (by rfl) ⟨2282630, by rfl⟩ : syracuseStep 3043507 = 4565261) B4565261
theorem B2060491 : Blo 1068616 2060491 := bstep (se 1 (by rfl) ⟨1545368, by rfl⟩ : syracuseStep 2060491 = 3090737) B3090737
theorem B4059467 : Blo 1068616 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B6091159 : Blo 1068616 6091159 := bstep (se 1 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 6091159 = 9136739) B9136739
theorem B2290123 : Blo 1068616 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B4059665 : Blo 1068616 4059665 := bstep (se 2 (by rfl) ⟨1522374, by rfl⟩ : syracuseStep 4059665 = 3044749) B3044749
theorem B2290199 : Blo 1068616 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B1930007 : Blo 1068616 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B1143767 : Blo 1068616 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B10417169 : Blo 1068616 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B5141569 : Blo 1068616 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B3044441 : Blo 1068616 3044441 := bstep (se 2 (by rfl) ⟨1141665, by rfl⟩ : syracuseStep 3044441 = 2283331) B2283331
theorem B4060439 : Blo 1068616 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B1603019 : Blo 1068616 1603019 := bstep (se 1 (by rfl) ⟨1202264, by rfl⟩ : syracuseStep 1603019 = 2404529) B2404529
theorem B1603031 : Blo 1068616 1603031 := bstep (se 1 (by rfl) ⟨1202273, by rfl⟩ : syracuseStep 1603031 = 2404547) B2404547
theorem B4060637 : Blo 1068616 4060637 := bstep (se 3 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 4060637 = 1522739) B1522739
theorem B2029043 : Blo 1068616 2029043 := bstep (se 1 (by rfl) ⟨1521782, by rfl⟩ : syracuseStep 2029043 = 3043565) B3043565
theorem B1603097 : Blo 1068616 1603097 := bstep (se 2 (by rfl) ⟨601161, by rfl⟩ : syracuseStep 1603097 = 1202323) B1202323
theorem B1603211 : Blo 1068616 1603211 := bstep (se 1 (by rfl) ⟨1202408, by rfl⟩ : syracuseStep 1603211 = 2404817) B2404817
theorem B1144459 : Blo 1068616 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B1603223 : Blo 1068616 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B1603289 : Blo 1068616 1603289 := bstep (se 2 (by rfl) ⟨601233, by rfl⟩ : syracuseStep 1603289 = 1202467) B1202467
theorem B1603403 : Blo 1068616 1603403 := bstep (se 1 (by rfl) ⟨1202552, by rfl⟩ : syracuseStep 1603403 = 2405105) B2405105
theorem B3864395 : Blo 1068616 3864395 := bstep (se 1 (by rfl) ⟨2898296, by rfl⟩ : syracuseStep 3864395 = 5796593) B5796593
theorem B1603415 : Blo 1068616 1603415 := bstep (se 1 (by rfl) ⟨1202561, by rfl⟩ : syracuseStep 1603415 = 2405123) B2405123
theorem B1603481 : Blo 1068616 1603481 := bstep (se 2 (by rfl) ⟨601305, by rfl⟩ : syracuseStep 1603481 = 1202611) B1202611
theorem B2029529 : Blo 1068616 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B1603595 : Blo 1068616 1603595 := bstep (se 1 (by rfl) ⟨1202696, by rfl⟩ : syracuseStep 1603595 = 2405393) B2405393
theorem B1603607 : Blo 1068616 1603607 := bstep (se 1 (by rfl) ⟨1202705, by rfl⟩ : syracuseStep 1603607 = 2405411) B2405411
theorem B8124461 : Blo 1068616 8124461 := bstep (se 3 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 8124461 = 3046673) B3046673
theorem B1603673 : Blo 1068616 1603673 := bstep (se 2 (by rfl) ⟨601377, by rfl⟩ : syracuseStep 1603673 = 1202755) B1202755
theorem B1603787 : Blo 1068616 1603787 := bstep (se 1 (by rfl) ⟨1202840, by rfl⟩ : syracuseStep 1603787 = 2405681) B2405681
theorem B1603799 : Blo 1068616 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B1931543 : Blo 1068616 1931543 := bstep (se 1 (by rfl) ⟨1448657, by rfl⟩ : syracuseStep 1931543 = 2897315) B2897315
theorem B1603865 : Blo 1068616 1603865 := bstep (se 2 (by rfl) ⟨601449, by rfl⟩ : syracuseStep 1603865 = 1202899) B1202899
theorem B1603979 : Blo 1068616 1603979 := bstep (se 1 (by rfl) ⟨1202984, by rfl⟩ : syracuseStep 1603979 = 2405969) B2405969
theorem B1603991 : Blo 1068616 1603991 := bstep (se 1 (by rfl) ⟨1202993, by rfl⟩ : syracuseStep 1603991 = 2405987) B2405987
theorem B1604057 : Blo 1068616 1604057 := bstep (se 2 (by rfl) ⟨601521, by rfl⟩ : syracuseStep 1604057 = 1203043) B1203043
theorem B3045853 : Blo 1068616 3045853 := bstep (se 3 (by rfl) ⟨571097, by rfl⟩ : syracuseStep 3045853 = 1142195) B1142195
theorem B1145335 : Blo 1068616 1145335 := bstep (se 1 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 1145335 = 1718003) B1718003
theorem B1604171 : Blo 1068616 1604171 := bstep (se 1 (by rfl) ⟨1203128, by rfl⟩ : syracuseStep 1604171 = 2406257) B2406257
theorem B1604183 : Blo 1068616 1604183 := bstep (se 1 (by rfl) ⟨1203137, by rfl⟩ : syracuseStep 1604183 = 2406275) B2406275
theorem B20544131 : Blo 1068616 20544131 := bstep (se 1 (by rfl) ⟨15408098, by rfl⟩ : syracuseStep 20544131 = 30816197) B30816197
theorem B1604249 : Blo 1068616 1604249 := bstep (se 2 (by rfl) ⟨601593, by rfl⟩ : syracuseStep 1604249 = 1203187) B1203187
theorem B3046081 : Blo 1068616 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B1604363 : Blo 1068616 1604363 := bstep (se 1 (by rfl) ⟨1203272, by rfl⟩ : syracuseStep 1604363 = 2406545) B2406545
theorem B1604375 : Blo 1068616 1604375 := bstep (se 1 (by rfl) ⟨1203281, by rfl⟩ : syracuseStep 1604375 = 2406563) B2406563
theorem B1604441 : Blo 1068616 1604441 := bstep (se 2 (by rfl) ⟨601665, by rfl⟩ : syracuseStep 1604441 = 1203331) B1203331
theorem B19037105 : Blo 1068616 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B13728689 : Blo 1068616 13728689 := bstep (se 2 (by rfl) ⟨5148258, by rfl⟩ : syracuseStep 13728689 = 10296517) B10296517
theorem B1604555 : Blo 1068616 1604555 := bstep (se 1 (by rfl) ⟨1203416, by rfl⟩ : syracuseStep 1604555 = 2406833) B2406833
theorem B1604567 : Blo 1068616 1604567 := bstep (se 1 (by rfl) ⟨1203425, by rfl⟩ : syracuseStep 1604567 = 2406851) B2406851
theorem B3046423 : Blo 1068616 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B1604633 : Blo 1068616 1604633 := bstep (se 2 (by rfl) ⟨601737, by rfl⟩ : syracuseStep 1604633 = 1203475) B1203475
theorem B1604747 : Blo 1068616 1604747 := bstep (se 1 (by rfl) ⟨1203560, by rfl⟩ : syracuseStep 1604747 = 2407121) B2407121
theorem B1604759 : Blo 1068616 1604759 := bstep (se 1 (by rfl) ⟨1203569, by rfl⟩ : syracuseStep 1604759 = 2407139) B2407139
theorem B3865751 : Blo 1068616 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B1604825 : Blo 1068616 1604825 := bstep (se 2 (by rfl) ⟨601809, by rfl⟩ : syracuseStep 1604825 = 1203619) B1203619
theorem B1604939 : Blo 1068616 1604939 := bstep (se 1 (by rfl) ⟨1203704, by rfl⟩ : syracuseStep 1604939 = 2407409) B2407409
theorem B1604951 : Blo 1068616 1604951 := bstep (se 1 (by rfl) ⟨1203713, by rfl⟩ : syracuseStep 1604951 = 2407427) B2407427
theorem B1506647 : Blo 1068616 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B4062595 : Blo 1068616 4062595 := bstep (se 1 (by rfl) ⟨3046946, by rfl⟩ : syracuseStep 4062595 = 6093893) B6093893
theorem B2030987 : Blo 1068616 2030987 := bstep (se 1 (by rfl) ⟨1523240, by rfl⟩ : syracuseStep 2030987 = 3046481) B3046481
theorem B1605017 : Blo 1068616 1605017 := bstep (se 2 (by rfl) ⟨601881, by rfl⟩ : syracuseStep 1605017 = 1203763) B1203763
theorem B1605131 : Blo 1068616 1605131 := bstep (se 1 (by rfl) ⟨1203848, by rfl⟩ : syracuseStep 1605131 = 2407697) B2407697
theorem B1605143 : Blo 1068616 1605143 := bstep (se 1 (by rfl) ⟨1203857, by rfl⟩ : syracuseStep 1605143 = 2407715) B2407715
theorem B2031169 : Blo 1068616 2031169 := bstep (se 2 (by rfl) ⟨761688, by rfl⟩ : syracuseStep 2031169 = 1523377) B1523377
theorem B1605209 : Blo 1068616 1605209 := bstep (se 2 (by rfl) ⟨601953, by rfl⟩ : syracuseStep 1605209 = 1203907) B1203907
theorem B4062899 : Blo 1068616 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B1605323 : Blo 1068616 1605323 := bstep (se 1 (by rfl) ⟨1203992, by rfl⟩ : syracuseStep 1605323 = 2407985) B2407985
theorem B1605335 : Blo 1068616 1605335 := bstep (se 1 (by rfl) ⟨1204001, by rfl⟩ : syracuseStep 1605335 = 2408003) B2408003
theorem B3047129 : Blo 1068616 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B1605401 : Blo 1068616 1605401 := bstep (se 2 (by rfl) ⟨602025, by rfl⟩ : syracuseStep 1605401 = 1204051) B1204051
theorem B1605515 : Blo 1068616 1605515 := bstep (se 1 (by rfl) ⟨1204136, by rfl⟩ : syracuseStep 1605515 = 2408273) B2408273
theorem B1605527 : Blo 1068616 1605527 := bstep (se 1 (by rfl) ⟨1204145, by rfl⟩ : syracuseStep 1605527 = 2408291) B2408291
theorem B1605593 : Blo 1068616 1605593 := bstep (se 2 (by rfl) ⟨602097, by rfl⟩ : syracuseStep 1605593 = 1204195) B1204195
theorem B1605647 : Blo 1068616 1605647 := bstep (se 1 (by rfl) ⟨1204235, by rfl⟩ : syracuseStep 1605647 = 2408471) B2408471
theorem B1605689 : Blo 1068616 1605689 := bstep (se 2 (by rfl) ⟨602133, by rfl⟩ : syracuseStep 1605689 = 1204267) B1204267
theorem B3047483 : Blo 1068616 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B3047539 : Blo 1068616 3047539 := bstep (se 1 (by rfl) ⟨2285654, by rfl⟩ : syracuseStep 3047539 = 4571309) B4571309
theorem B1605767 : Blo 1068616 1605767 := bstep (se 1 (by rfl) ⟨1204325, by rfl⟩ : syracuseStep 1605767 = 2408651) B2408651
theorem B1605803 : Blo 1068616 1605803 := bstep (se 1 (by rfl) ⟨1204352, by rfl⟩ : syracuseStep 1605803 = 2408705) B2408705
theorem B12517577 : Blo 1068616 12517577 := bstep (se 2 (by rfl) ⟨4694091, by rfl⟩ : syracuseStep 12517577 = 9388183) B9388183
theorem B1605833 : Blo 1068616 1605833 := bstep (se 2 (by rfl) ⟨602187, by rfl⟩ : syracuseStep 1605833 = 1204375) B1204375
theorem B2031905 : Blo 1068616 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B1605947 : Blo 1068616 1605947 := bstep (se 1 (by rfl) ⟨1204460, by rfl⟩ : syracuseStep 1605947 = 2408921) B2408921
theorem B1606007 : Blo 1068616 1606007 := bstep (se 1 (by rfl) ⟨1204505, by rfl⟩ : syracuseStep 1606007 = 2409011) B2409011
theorem B1606031 : Blo 1068616 1606031 := bstep (se 1 (by rfl) ⟨1204523, by rfl⟩ : syracuseStep 1606031 = 2409047) B2409047
theorem B2032057 : Blo 1068616 2032057 := bstep (se 2 (by rfl) ⟨762021, by rfl⟩ : syracuseStep 2032057 = 1524043) B1524043
theorem B1606073 : Blo 1068616 1606073 := bstep (se 2 (by rfl) ⟨602277, by rfl⟩ : syracuseStep 1606073 = 1204555) B1204555
theorem B3047881 : Blo 1068616 3047881 := bstep (se 2 (by rfl) ⟨1142955, by rfl⟩ : syracuseStep 3047881 = 2285911) B2285911
theorem B1606151 : Blo 1068616 1606151 := bstep (se 1 (by rfl) ⟨1204613, by rfl⟩ : syracuseStep 1606151 = 2409227) B2409227
theorem B1606187 : Blo 1068616 1606187 := bstep (se 1 (by rfl) ⟨1204640, by rfl⟩ : syracuseStep 1606187 = 2409281) B2409281
theorem B1606217 : Blo 1068616 1606217 := bstep (se 2 (by rfl) ⟨602331, by rfl⟩ : syracuseStep 1606217 = 1204663) B1204663
theorem B6095533 : Blo 1068616 6095533 := bstep (se 3 (by rfl) ⟨1142912, by rfl⟩ : syracuseStep 6095533 = 2285825) B2285825
theorem B1606331 : Blo 1068616 1606331 := bstep (se 1 (by rfl) ⟨1204748, by rfl⟩ : syracuseStep 1606331 = 2409497) B2409497
theorem B1606391 : Blo 1068616 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B1606415 : Blo 1068616 1606415 := bstep (se 1 (by rfl) ⟨1204811, by rfl⟩ : syracuseStep 1606415 = 2409623) B2409623
theorem B33424163 : Blo 1068616 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B1606457 : Blo 1068616 1606457 := bstep (se 2 (by rfl) ⟨602421, by rfl⟩ : syracuseStep 1606457 = 1204843) B1204843
theorem B1606535 : Blo 1068616 1606535 := bstep (se 1 (by rfl) ⟨1204901, by rfl⟩ : syracuseStep 1606535 = 2409803) B2409803
theorem B1606571 : Blo 1068616 1606571 := bstep (se 1 (by rfl) ⟨1204928, by rfl⟩ : syracuseStep 1606571 = 2409857) B2409857
theorem B1606601 : Blo 1068616 1606601 := bstep (se 2 (by rfl) ⟨602475, by rfl⟩ : syracuseStep 1606601 = 1204951) B1204951
theorem B1803323 : Blo 1068616 1803323 := bstep (se 1 (by rfl) ⟨1352492, by rfl⟩ : syracuseStep 1803323 = 2704985) B2704985
theorem B1606715 : Blo 1068616 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B1606775 : Blo 1068616 1606775 := bstep (se 1 (by rfl) ⟨1205081, by rfl⟩ : syracuseStep 1606775 = 2410163) B2410163
theorem B1606799 : Blo 1068616 1606799 := bstep (se 1 (by rfl) ⟨1205099, by rfl⟩ : syracuseStep 1606799 = 2410199) B2410199
theorem B1606841 : Blo 1068616 1606841 := bstep (se 2 (by rfl) ⟨602565, by rfl⟩ : syracuseStep 1606841 = 1205131) B1205131
theorem B1606919 : Blo 1068616 1606919 := bstep (se 1 (by rfl) ⟨1205189, by rfl⟩ : syracuseStep 1606919 = 2410379) B2410379
theorem B1606955 : Blo 1068616 1606955 := bstep (se 1 (by rfl) ⟨1205216, by rfl⟩ : syracuseStep 1606955 = 2410433) B2410433
theorem B1606985 : Blo 1068616 1606985 := bstep (se 2 (by rfl) ⟨602619, by rfl⟩ : syracuseStep 1606985 = 1205239) B1205239
theorem B1607099 : Blo 1068616 1607099 := bstep (se 1 (by rfl) ⟨1205324, by rfl⟩ : syracuseStep 1607099 = 2410649) B2410649
theorem B1803721 : Blo 1068616 1803721 := bstep (se 2 (by rfl) ⟨676395, by rfl⟩ : syracuseStep 1803721 = 1352791) B1352791
theorem B1607159 : Blo 1068616 1607159 := bstep (se 1 (by rfl) ⟨1205369, by rfl⟩ : syracuseStep 1607159 = 2410739) B2410739
theorem B1607183 : Blo 1068616 1607183 := bstep (se 1 (by rfl) ⟨1205387, by rfl⟩ : syracuseStep 1607183 = 2410775) B2410775
theorem B1607225 : Blo 1068616 1607225 := bstep (se 2 (by rfl) ⟨602709, by rfl⟩ : syracuseStep 1607225 = 1205419) B1205419
theorem B1607303 : Blo 1068616 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B1607339 : Blo 1068616 1607339 := bstep (se 1 (by rfl) ⟨1205504, by rfl⟩ : syracuseStep 1607339 = 2411009) B2411009
theorem B1607369 : Blo 1068616 1607369 := bstep (se 2 (by rfl) ⟨602763, by rfl⟩ : syracuseStep 1607369 = 1205527) B1205527
theorem B6850277 : Blo 1068616 6850277 := bstep (se 4 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 6850277 = 1284427) B1284427
theorem B4065025 : Blo 1068616 4065025 := bstep (se 2 (by rfl) ⟨1524384, by rfl⟩ : syracuseStep 4065025 = 3048769) B3048769
theorem B1607483 : Blo 1068616 1607483 := bstep (se 1 (by rfl) ⟨1205612, by rfl⟩ : syracuseStep 1607483 = 2411225) B2411225
theorem B1607543 : Blo 1068616 1607543 := bstep (se 1 (by rfl) ⟨1205657, by rfl⟩ : syracuseStep 1607543 = 2411315) B2411315
theorem B1607567 : Blo 1068616 1607567 := bstep (se 1 (by rfl) ⟨1205675, by rfl⟩ : syracuseStep 1607567 = 2411351) B2411351
theorem B1607609 : Blo 1068616 1607609 := bstep (se 2 (by rfl) ⟨602853, by rfl⟩ : syracuseStep 1607609 = 1205707) B1205707
theorem B1607687 : Blo 1068616 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B1607723 : Blo 1068616 1607723 := bstep (se 1 (by rfl) ⟨1205792, by rfl⟩ : syracuseStep 1607723 = 2411585) B2411585
theorem B5146685 : Blo 1068616 5146685 := bstep (se 3 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 5146685 = 1930007) B1930007
theorem B1607753 : Blo 1068616 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B8357975 : Blo 1068616 8357975 := bstep (se 1 (by rfl) ⟨6268481, by rfl⟩ : syracuseStep 8357975 = 12536963) B12536963
theorem B1804423 : Blo 1068616 1804423 := bstep (se 1 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 1804423 = 2706635) B2706635
theorem B2033849 : Blo 1068616 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B1607867 : Blo 1068616 1607867 := bstep (se 1 (by rfl) ⟨1205900, by rfl⟩ : syracuseStep 1607867 = 2411801) B2411801
theorem B1607927 : Blo 1068616 1607927 := bstep (se 1 (by rfl) ⟨1205945, by rfl⟩ : syracuseStep 1607927 = 2411891) B2411891
theorem B1607951 : Blo 1068616 1607951 := bstep (se 1 (by rfl) ⟨1205963, by rfl⟩ : syracuseStep 1607951 = 2411927) B2411927
theorem B1607993 : Blo 1068616 1607993 := bstep (se 2 (by rfl) ⟨602997, by rfl⟩ : syracuseStep 1607993 = 1205995) B1205995
theorem B1608071 : Blo 1068616 1608071 := bstep (se 1 (by rfl) ⟨1206053, by rfl⟩ : syracuseStep 1608071 = 2412107) B2412107
theorem B1608107 : Blo 1068616 1608107 := bstep (se 1 (by rfl) ⟨1206080, by rfl⟩ : syracuseStep 1608107 = 2412161) B2412161
theorem B1608137 : Blo 1068616 1608137 := bstep (se 2 (by rfl) ⟨603051, by rfl⟩ : syracuseStep 1608137 = 1206103) B1206103
theorem B1608251 : Blo 1068616 1608251 := bstep (se 1 (by rfl) ⟨1206188, by rfl⟩ : syracuseStep 1608251 = 2412377) B2412377
theorem B3050045 : Blo 1068616 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B1608311 : Blo 1068616 1608311 := bstep (se 1 (by rfl) ⟨1206233, by rfl⟩ : syracuseStep 1608311 = 2412467) B2412467
theorem B1608335 : Blo 1068616 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B1608377 : Blo 1068616 1608377 := bstep (se 2 (by rfl) ⟨603141, by rfl⟩ : syracuseStep 1608377 = 1206283) B1206283
theorem B1608455 : Blo 1068616 1608455 := bstep (se 1 (by rfl) ⟨1206341, by rfl⟩ : syracuseStep 1608455 = 2412683) B2412683
theorem B1805071 : Blo 1068616 1805071 := bstep (se 1 (by rfl) ⟨1353803, by rfl⟩ : syracuseStep 1805071 = 2707607) B2707607
theorem B3050273 : Blo 1068616 3050273 := bstep (se 2 (by rfl) ⟨1143852, by rfl⟩ : syracuseStep 3050273 = 2287705) B2287705
theorem B7703333 : Blo 1068616 7703333 := bstep (se 4 (by rfl) ⟨722187, by rfl⟩ : syracuseStep 7703333 = 1444375) B1444375
theorem B1608491 : Blo 1068616 1608491 := bstep (se 1 (by rfl) ⟨1206368, by rfl⟩ : syracuseStep 1608491 = 2412737) B2412737
theorem B1608521 : Blo 1068616 1608521 := bstep (se 2 (by rfl) ⟨603195, by rfl⟩ : syracuseStep 1608521 = 1206391) B1206391
theorem B11733913 : Blo 1068616 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B1608635 : Blo 1068616 1608635 := bstep (se 1 (by rfl) ⟨1206476, by rfl⟩ : syracuseStep 1608635 = 2412953) B2412953
theorem B1608695 : Blo 1068616 1608695 := bstep (se 1 (by rfl) ⟨1206521, by rfl⟩ : syracuseStep 1608695 = 2413043) B2413043
theorem B1608719 : Blo 1068616 1608719 := bstep (se 1 (by rfl) ⟨1206539, by rfl⟩ : syracuseStep 1608719 = 2413079) B2413079
theorem B6097949 : Blo 1068616 6097949 := bstep (se 3 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 6097949 = 2286731) B2286731
theorem B1608761 : Blo 1068616 1608761 := bstep (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) B1206571
theorem B3050615 : Blo 1068616 3050615 := bstep (se 1 (by rfl) ⟨2287961, by rfl⟩ : syracuseStep 3050615 = 4575923) B4575923
theorem B21138563 : Blo 1068616 21138563 := bstep (se 1 (by rfl) ⟨15853922, by rfl⟩ : syracuseStep 21138563 = 31707845) B31707845
theorem B1608839 : Blo 1068616 1608839 := bstep (se 1 (by rfl) ⟨1206629, by rfl⟩ : syracuseStep 1608839 = 2413259) B2413259
theorem B1608875 : Blo 1068616 1608875 := bstep (se 1 (by rfl) ⟨1206656, by rfl⟩ : syracuseStep 1608875 = 2413313) B2413313
theorem B1608905 : Blo 1068616 1608905 := bstep (se 2 (by rfl) ⟨603339, by rfl⟩ : syracuseStep 1608905 = 1206679) B1206679
theorem B1805611 : Blo 1068616 1805611 := bstep (se 1 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 1805611 = 2708417) B2708417
theorem B3607955 : Blo 1068616 3607955 := bstep (se 1 (by rfl) ⟨2705966, by rfl⟩ : syracuseStep 3607955 = 5411933) B5411933
theorem B1805753 : Blo 1068616 1805753 := bstep (se 2 (by rfl) ⟨677157, by rfl⟩ : syracuseStep 1805753 = 1354315) B1354315
theorem B5148107 : Blo 1068616 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B111054563 : Blo 1068616 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B1806455 : Blo 1068616 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B2035847 : Blo 1068616 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B5411123 : Blo 1068616 5411123 := bstep (se 1 (by rfl) ⟨4058342, by rfl⟩ : syracuseStep 5411123 = 8116685) B8116685
theorem B1806907 : Blo 1068616 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B4067927 : Blo 1068616 4067927 := bstep (se 1 (by rfl) ⟨3050945, by rfl⟩ : syracuseStep 4067927 = 6101891) B6101891
theorem B5411447 : Blo 1068616 5411447 := bstep (se 1 (by rfl) ⟨4058585, by rfl⟩ : syracuseStep 5411447 = 8117171) B8117171
theorem B8131265 : Blo 1068616 8131265 := bstep (se 2 (by rfl) ⟨3049224, by rfl⟩ : syracuseStep 8131265 = 6098449) B6098449
theorem B1807049 : Blo 1068616 1807049 := bstep (se 2 (by rfl) ⟨677643, by rfl⟩ : syracuseStep 1807049 = 1355287) B1355287
theorem B3609359 : Blo 1068616 3609359 := bstep (se 1 (by rfl) ⟨2707019, by rfl⟩ : syracuseStep 3609359 = 5414039) B5414039
theorem B12194711 : Blo 1068616 12194711 := bstep (se 1 (by rfl) ⟨9146033, by rfl⟩ : syracuseStep 12194711 = 18292067) B18292067
theorem B3609629 : Blo 1068616 3609629 := bstep (se 3 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 3609629 = 1353611) B1353611
theorem B4068413 : Blo 1068616 4068413 := bstep (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) B1525655
theorem B3085427 : Blo 1068616 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1807751 : Blo 1068616 1807751 := bstep (se 1 (by rfl) ⟨1355813, by rfl⟩ : syracuseStep 1807751 = 2711627) B2711627
theorem B5150105 : Blo 1068616 5150105 := bstep (se 2 (by rfl) ⟨1931289, by rfl⟩ : syracuseStep 5150105 = 3862579) B3862579
theorem B6100433 : Blo 1068616 6100433 := bstep (se 2 (by rfl) ⟨2287662, by rfl⟩ : syracuseStep 6100433 = 4575325) B4575325
theorem B13735453 : Blo 1068616 13735453 := bstep (se 3 (by rfl) ⟨2575397, by rfl⟩ : syracuseStep 13735453 = 5150795) B5150795
theorem B5412419 : Blo 1068616 5412419 := bstep (se 1 (by rfl) ⟨4059314, by rfl⟩ : syracuseStep 5412419 = 8118629) B8118629
theorem B3053143 : Blo 1068616 3053143 := bstep (se 1 (by rfl) ⟨2289857, by rfl⟩ : syracuseStep 3053143 = 4579715) B4579715
theorem B3249953 : Blo 1068616 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B16455473 : Blo 1068616 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B3053371 : Blo 1068616 3053371 := bstep (se 1 (by rfl) ⟨2290028, by rfl⟩ : syracuseStep 3053371 = 4580057) B4580057
theorem B5412743 : Blo 1068616 5412743 := bstep (se 1 (by rfl) ⟨4059557, by rfl⟩ : syracuseStep 5412743 = 8119115) B8119115
theorem B2168711 : Blo 1068616 2168711 := bstep (se 1 (by rfl) ⟨1626533, by rfl⟩ : syracuseStep 2168711 = 3253067) B3253067
theorem B3053497 : Blo 1068616 3053497 := bstep (se 2 (by rfl) ⟨1145061, by rfl⟩ : syracuseStep 3053497 = 2290123) B2290123
theorem B1808399 : Blo 1068616 1808399 := bstep (se 1 (by rfl) ⟨1356299, by rfl⟩ : syracuseStep 1808399 = 2712599) B2712599
theorem B1284239 : Blo 1068616 1284239 := bstep (se 1 (by rfl) ⟨963179, by rfl⟩ : syracuseStep 1284239 = 1926359) B1926359
theorem B3611033 : Blo 1068616 3611033 := bstep (se 2 (by rfl) ⟨1354137, by rfl⟩ : syracuseStep 3611033 = 2708275) B2708275
theorem B1808939 : Blo 1068616 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B14654071 : Blo 1068616 14654071 := bstep (se 1 (by rfl) ⟨10990553, by rfl⟩ : syracuseStep 14654071 = 21981107) B21981107
theorem B6855425 : Blo 1068616 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B4070159 : Blo 1068616 4070159 := bstep (se 1 (by rfl) ⟨3052619, by rfl⟩ : syracuseStep 4070159 = 6105239) B6105239
theorem B6626081 : Blo 1068616 6626081 := bstep (se 2 (by rfl) ⟨2484780, by rfl⟩ : syracuseStep 6626081 = 4969561) B4969561
theorem B1809337 : Blo 1068616 1809337 := bstep (se 2 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 1809337 = 1357003) B1357003
theorem B3611735 : Blo 1068616 3611735 := bstep (se 1 (by rfl) ⟨2708801, by rfl⟩ : syracuseStep 3611735 = 5417603) B5417603
theorem B2891009 : Blo 1068616 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B6102323 : Blo 1068616 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B3251609 : Blo 1068616 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B3087769 : Blo 1068616 3087769 := bstep (se 2 (by rfl) ⟨1157913, by rfl⟩ : syracuseStep 3087769 = 2315827) B2315827
theorem B3612221 : Blo 1068616 3612221 := bstep (se 3 (by rfl) ⟨677291, by rfl⟩ : syracuseStep 3612221 = 1354583) B1354583
theorem B1810039 : Blo 1068616 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B34676525 : Blo 1068616 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B5873617 : Blo 1068616 5873617 := bstep (se 2 (by rfl) ⟨2202606, by rfl⟩ : syracuseStep 5873617 = 4405213) B4405213
theorem B8134667 : Blo 1068616 8134667 := bstep (se 1 (by rfl) ⟨6101000, by rfl⟩ : syracuseStep 8134667 = 12202001) B12202001
theorem B10297367 : Blo 1068616 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B5152835 : Blo 1068616 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B4071815 : Blo 1068616 4071815 := bstep (se 1 (by rfl) ⟨3053861, by rfl⟩ : syracuseStep 4071815 = 6107723) B6107723
theorem B17375633 : Blo 1068616 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B16491073 : Blo 1068616 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B15442649 : Blo 1068616 15442649 := bstep (se 2 (by rfl) ⟨5790993, by rfl⟩ : syracuseStep 15442649 = 11581987) B11581987
theorem B6103781 : Blo 1068616 6103781 := bstep (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) B1144459
theorem B3613625 : Blo 1068616 3613625 := bstep (se 2 (by rfl) ⟨1355109, by rfl⟩ : syracuseStep 3613625 = 2710219) B2710219
theorem B1352695 : Blo 1068616 1352695 := bstep (se 1 (by rfl) ⟨1014521, by rfl⟩ : syracuseStep 1352695 = 2029043) B2029043
theorem B1713287 : Blo 1068616 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B2892935 : Blo 1068616 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B12199085 : Blo 1068616 12199085 := bstep (se 3 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 12199085 = 4574657) B4574657
theorem B1353019 : Blo 1068616 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B5416307 : Blo 1068616 5416307 := bstep (se 1 (by rfl) ⟨4062230, by rfl⟩ : syracuseStep 5416307 = 8124461) B8124461
theorem B2893171 : Blo 1068616 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B10429955 : Blo 1068616 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B3614219 : Blo 1068616 3614219 := bstep (se 1 (by rfl) ⟨2710664, by rfl⟩ : syracuseStep 3614219 = 5421329) B5421329
theorem B1287695 : Blo 1068616 1287695 := bstep (se 1 (by rfl) ⟨965771, by rfl⟩ : syracuseStep 1287695 = 1931543) B1931543
theorem B3614327 : Blo 1068616 3614327 := bstep (se 1 (by rfl) ⟨2710745, by rfl⟩ : syracuseStep 3614327 = 5421491) B5421491
theorem B5416793 : Blo 1068616 5416793 := bstep (se 2 (by rfl) ⟨2031297, by rfl⟩ : syracuseStep 5416793 = 4062595) B4062595
theorem B2172791 : Blo 1068616 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B8136611 : Blo 1068616 8136611 := bstep (se 1 (by rfl) ⟨6102458, by rfl⟩ : syracuseStep 8136611 = 12204917) B12204917
theorem B12691403 : Blo 1068616 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B9152459 : Blo 1068616 9152459 := bstep (se 1 (by rfl) ⟨6864344, by rfl⟩ : syracuseStep 9152459 = 13728689) B13728689
theorem B3614921 : Blo 1068616 3614921 := bstep (se 2 (by rfl) ⟨1355595, by rfl⟩ : syracuseStep 3614921 = 2711191) B2711191
theorem B1353991 : Blo 1068616 1353991 := bstep (se 1 (by rfl) ⟨1015493, by rfl⟩ : syracuseStep 1353991 = 2030987) B2030987
theorem B16460273 : Blo 1068616 16460273 := bstep (se 2 (by rfl) ⟨6172602, by rfl⟩ : syracuseStep 16460273 = 12345205) B12345205
theorem B1354411 : Blo 1068616 1354411 := bstep (se 1 (by rfl) ⟨1015808, by rfl⟩ : syracuseStep 1354411 = 2031617) B2031617
theorem B5778191 : Blo 1068616 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B3910459 : Blo 1068616 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B3615623 : Blo 1068616 3615623 := bstep (se 1 (by rfl) ⟨2711717, by rfl⟩ : syracuseStep 3615623 = 5423435) B5423435
theorem B1354639 : Blo 1068616 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B3616001 : Blo 1068616 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B2895239 : Blo 1068616 2895239 := bstep (se 1 (by rfl) ⟨2171429, by rfl⟩ : syracuseStep 2895239 = 4342859) B4342859
theorem B2895421 : Blo 1068616 2895421 := bstep (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) B1085783
theorem B1355383 : Blo 1068616 1355383 := bstep (se 1 (by rfl) ⟨1016537, by rfl⟩ : syracuseStep 1355383 = 2033075) B2033075
theorem B30912151 : Blo 1068616 30912151 := bstep (se 1 (by rfl) ⟨23184113, by rfl⟩ : syracuseStep 30912151 = 46368227) B46368227
theorem B6107015 : Blo 1068616 6107015 := bstep (se 1 (by rfl) ⟨4580261, by rfl⟩ : syracuseStep 6107015 = 9160523) B9160523
theorem B5418899 : Blo 1068616 5418899 := bstep (se 1 (by rfl) ⟨4064174, by rfl⟩ : syracuseStep 5418899 = 8128349) B8128349
theorem B13709209 : Blo 1068616 13709209 := bstep (se 2 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 13709209 = 10281907) B10281907
theorem B1355707 : Blo 1068616 1355707 := bstep (se 1 (by rfl) ⟨1016780, by rfl⟩ : syracuseStep 1355707 = 2033561) B2033561
theorem B3616811 : Blo 1068616 3616811 := bstep (se 1 (by rfl) ⟨2712608, by rfl⟩ : syracuseStep 3616811 = 5425217) B5425217
theorem B6860861 : Blo 1068616 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B6107197 : Blo 1068616 6107197 := bstep (se 3 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 6107197 = 2290199) B2290199
theorem B8139041 : Blo 1068616 8139041 := bstep (se 2 (by rfl) ⟨3052140, by rfl⟩ : syracuseStep 8139041 = 6104281) B6104281
theorem B3256691 : Blo 1068616 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B2404727 : Blo 1068616 2404727 := bstep (se 1 (by rfl) ⟨1803545, by rfl⟩ : syracuseStep 2404727 = 3607091) B3607091
theorem B1716599 : Blo 1068616 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B1356203 : Blo 1068616 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B9777667 : Blo 1068616 9777667 := bstep (se 1 (by rfl) ⟨7333250, by rfl⟩ : syracuseStep 9777667 = 14666501) B14666501
theorem B2404907 : Blo 1068616 2404907 := bstep (se 1 (by rfl) ⟨1803680, by rfl⟩ : syracuseStep 2404907 = 3607361) B3607361
theorem B5485099 : Blo 1068616 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B4567823 : Blo 1068616 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B1356679 : Blo 1068616 1356679 := bstep (se 1 (by rfl) ⟨1017509, by rfl⟩ : syracuseStep 1356679 = 2035019) B2035019
theorem B2405267 : Blo 1068616 2405267 := bstep (se 1 (by rfl) ⟨1803950, by rfl⟩ : syracuseStep 2405267 = 3607901) B3607901
theorem B2405321 : Blo 1068616 2405321 := bstep (se 2 (by rfl) ⟨901995, by rfl⟩ : syracuseStep 2405321 = 1803991) B1803991
theorem B1717291 : Blo 1068616 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B8696965 : Blo 1068616 8696965 := bstep (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) B1630681
theorem B8140013 : Blo 1068616 8140013 := bstep (se 3 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 8140013 = 3052505) B3052505
theorem B3618107 : Blo 1068616 3618107 := bstep (se 1 (by rfl) ⟨2713580, by rfl⟩ : syracuseStep 3618107 = 5427161) B5427161
theorem B1357175 : Blo 1068616 1357175 := bstep (se 1 (by rfl) ⟨1017881, by rfl⟩ : syracuseStep 1357175 = 2035763) B2035763
theorem B1357327 : Blo 1068616 1357327 := bstep (se 1 (by rfl) ⟨1017995, by rfl⟩ : syracuseStep 1357327 = 2035991) B2035991
theorem B3126817 : Blo 1068616 3126817 := bstep (se 2 (by rfl) ⟨1172556, by rfl⟩ : syracuseStep 3126817 = 2345113) B2345113
theorem B2406023 : Blo 1068616 2406023 := bstep (se 1 (by rfl) ⟨1804517, by rfl⟩ : syracuseStep 2406023 = 3609035) B3609035
theorem B1357499 : Blo 1068616 1357499 := bstep (se 1 (by rfl) ⟨1018124, by rfl⟩ : syracuseStep 1357499 = 2036249) B2036249
theorem B3618593 : Blo 1068616 3618593 := bstep (se 2 (by rfl) ⟨1356972, by rfl⟩ : syracuseStep 3618593 = 2713945) B2713945
theorem B2406203 : Blo 1068616 2406203 := bstep (se 1 (by rfl) ⟨1804652, by rfl⟩ : syracuseStep 2406203 = 3609305) B3609305
theorem B2406329 : Blo 1068616 2406329 := bstep (se 2 (by rfl) ⟨902373, by rfl⟩ : syracuseStep 2406329 = 1804747) B1804747
theorem B3258515 : Blo 1068616 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B2406671 : Blo 1068616 2406671 := bstep (se 1 (by rfl) ⟨1805003, by rfl⟩ : syracuseStep 2406671 = 3610007) B3610007
theorem B2406689 : Blo 1068616 2406689 := bstep (se 2 (by rfl) ⟨902508, by rfl⟩ : syracuseStep 2406689 = 1805017) B1805017
theorem B2570555 : Blo 1068616 2570555 := bstep (se 1 (by rfl) ⟨1927916, by rfl⟩ : syracuseStep 2570555 = 3855833) B3855833
theorem B2931005 : Blo 1068616 2931005 := bstep (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) B1099127
theorem B3619187 : Blo 1068616 3619187 := bstep (se 1 (by rfl) ⟨2714390, by rfl⟩ : syracuseStep 3619187 = 5428781) B5428781
theorem B2407031 : Blo 1068616 2407031 := bstep (se 1 (by rfl) ⟨1805273, by rfl⟩ : syracuseStep 2407031 = 3610547) B3610547
theorem B5782189 : Blo 1068616 5782189 := bstep (se 3 (by rfl) ⟨1084160, by rfl⟩ : syracuseStep 5782189 = 2168321) B2168321
theorem B2407211 : Blo 1068616 2407211 := bstep (se 1 (by rfl) ⟨1805408, by rfl⟩ : syracuseStep 2407211 = 3610817) B3610817
theorem B6601607 : Blo 1068616 6601607 := bstep (se 1 (by rfl) ⟨4951205, by rfl⟩ : syracuseStep 6601607 = 9902411) B9902411
theorem B5421977 : Blo 1068616 5421977 := bstep (se 2 (by rfl) ⟨2033241, by rfl⟩ : syracuseStep 5421977 = 4066483) B4066483
theorem B2571209 : Blo 1068616 2571209 := bstep (se 2 (by rfl) ⟨964203, by rfl⟩ : syracuseStep 2571209 = 1928407) B1928407
theorem B8141957 : Blo 1068616 8141957 := bstep (se 4 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 8141957 = 1526617) B1526617
theorem B2407571 : Blo 1068616 2407571 := bstep (se 1 (by rfl) ⟨1805678, by rfl⟩ : syracuseStep 2407571 = 3611357) B3611357
theorem B2407625 : Blo 1068616 2407625 := bstep (se 2 (by rfl) ⟨902859, by rfl⟩ : syracuseStep 2407625 = 1805719) B1805719
theorem B10305053 : Blo 1068616 10305053 := bstep (se 3 (by rfl) ⟨1932197, by rfl⟩ : syracuseStep 10305053 = 3864395) B3864395
theorem B7421483 : Blo 1068616 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B10993229 : Blo 1068616 10993229 := bstep (se 3 (by rfl) ⟨2061230, by rfl⟩ : syracuseStep 10993229 = 4122461) B4122461
theorem B10305281 : Blo 1068616 10305281 := bstep (se 2 (by rfl) ⟨3864480, by rfl⟩ : syracuseStep 10305281 = 7728961) B7728961
theorem B9912179 : Blo 1068616 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B2408327 : Blo 1068616 2408327 := bstep (se 1 (by rfl) ⟨1806245, by rfl⟩ : syracuseStep 2408327 = 3612491) B3612491
theorem B31768523 : Blo 1068616 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B2408507 : Blo 1068616 2408507 := bstep (se 1 (by rfl) ⟨1806380, by rfl⟩ : syracuseStep 2408507 = 3612761) B3612761
theorem B2441351 : Blo 1068616 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B2408633 : Blo 1068616 2408633 := bstep (se 2 (by rfl) ⟨903237, by rfl⟩ : syracuseStep 2408633 = 1806475) B1806475
theorem B2933263 : Blo 1068616 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B2408975 : Blo 1068616 2408975 := bstep (se 1 (by rfl) ⟨1806731, by rfl⟩ : syracuseStep 2408975 = 3613463) B3613463
theorem B2408993 : Blo 1068616 2408993 := bstep (se 2 (by rfl) ⟨903372, by rfl⟩ : syracuseStep 2408993 = 1806745) B1806745
theorem B2409335 : Blo 1068616 2409335 := bstep (se 1 (by rfl) ⟨1807001, by rfl⟩ : syracuseStep 2409335 = 3614003) B3614003
theorem B2409515 : Blo 1068616 2409515 := bstep (se 1 (by rfl) ⟨1807136, by rfl⟩ : syracuseStep 2409515 = 3614273) B3614273
theorem B2573399 : Blo 1068616 2573399 := bstep (se 1 (by rfl) ⟨1930049, by rfl⟩ : syracuseStep 2573399 = 3860099) B3860099
theorem B19547527 : Blo 1068616 19547527 := bstep (se 1 (by rfl) ⟨14660645, by rfl⟩ : syracuseStep 19547527 = 29321291) B29321291
theorem B2409875 : Blo 1068616 2409875 := bstep (se 1 (by rfl) ⟨1807406, by rfl⟩ : syracuseStep 2409875 = 3614813) B3614813
theorem B5424569 : Blo 1068616 5424569 := bstep (se 2 (by rfl) ⟨2034213, by rfl⟩ : syracuseStep 5424569 = 4068427) B4068427
theorem B2409929 : Blo 1068616 2409929 := bstep (se 2 (by rfl) ⟨903723, by rfl⟩ : syracuseStep 2409929 = 1807447) B1807447
theorem B8144387 : Blo 1068616 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B5785111 : Blo 1068616 5785111 := bstep (se 1 (by rfl) ⟨4338833, by rfl⟩ : syracuseStep 5785111 = 8677667) B8677667
theorem B2705015 : Blo 1068616 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B12207833 : Blo 1068616 12207833 := bstep (se 2 (by rfl) ⟨4577937, by rfl⟩ : syracuseStep 12207833 = 9155875) B9155875
theorem B5490413 : Blo 1068616 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B24692633 : Blo 1068616 24692633 := bstep (se 2 (by rfl) ⟨9259737, by rfl⟩ : syracuseStep 24692633 = 18519475) B18519475
theorem B2410631 : Blo 1068616 2410631 := bstep (se 1 (by rfl) ⟨1807973, by rfl⟩ : syracuseStep 2410631 = 3615947) B3615947
theorem B2410811 : Blo 1068616 2410811 := bstep (se 1 (by rfl) ⟨1808108, by rfl⟩ : syracuseStep 2410811 = 3616217) B3616217
theorem B2410937 : Blo 1068616 2410937 := bstep (se 2 (by rfl) ⟨904101, by rfl⟩ : syracuseStep 2410937 = 1808203) B1808203
theorem B2706007 : Blo 1068616 2706007 := bstep (se 1 (by rfl) ⟨2029505, by rfl⟩ : syracuseStep 2706007 = 4059011) B4059011
theorem B6867575 : Blo 1068616 6867575 := bstep (se 1 (by rfl) ⟨5150681, by rfl⟩ : syracuseStep 6867575 = 10301363) B10301363
theorem B5425865 : Blo 1068616 5425865 := bstep (se 2 (by rfl) ⟨2034699, by rfl⟩ : syracuseStep 5425865 = 4069399) B4069399
theorem B2411279 : Blo 1068616 2411279 := bstep (se 1 (by rfl) ⟨1808459, by rfl⟩ : syracuseStep 2411279 = 3616919) B3616919
theorem B2411297 : Blo 1068616 2411297 := bstep (se 2 (by rfl) ⟨904236, by rfl⟩ : syracuseStep 2411297 = 1808473) B1808473
theorem B2706311 : Blo 1068616 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B2706443 : Blo 1068616 2706443 := bstep (se 1 (by rfl) ⟨2029832, by rfl⟩ : syracuseStep 2706443 = 4059665) B4059665
theorem B2411639 : Blo 1068616 2411639 := bstep (se 1 (by rfl) ⟨1808729, by rfl⟩ : syracuseStep 2411639 = 3617459) B3617459
theorem B2542859 : Blo 1068616 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B2411819 : Blo 1068616 2411819 := bstep (se 1 (by rfl) ⟨1808864, by rfl⟩ : syracuseStep 2411819 = 3617729) B3617729
theorem B1527113 : Blo 1068616 1527113 := bstep (se 2 (by rfl) ⟨572667, by rfl⟩ : syracuseStep 1527113 = 1145335) B1145335
theorem B2706959 : Blo 1068616 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B4017725 : Blo 1068616 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B6868547 : Blo 1068616 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B1625719 : Blo 1068616 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B1068679 : Blo 1068616 1068679 := bstep (se 1 (by rfl) ⟨801509, by rfl⟩ : syracuseStep 1068679 = 1603019) B1603019
theorem B1068687 : Blo 1068616 1068687 := bstep (se 1 (by rfl) ⟨801515, by rfl⟩ : syracuseStep 1068687 = 1603031) B1603031
theorem B2707091 : Blo 1068616 2707091 := bstep (se 1 (by rfl) ⟨2030318, by rfl⟩ : syracuseStep 2707091 = 4060637) B4060637
theorem B2412179 : Blo 1068616 2412179 := bstep (se 1 (by rfl) ⟨1809134, by rfl⟩ : syracuseStep 2412179 = 3618269) B3618269
theorem B1068731 : Blo 1068616 1068731 := bstep (se 1 (by rfl) ⟨801548, by rfl⟩ : syracuseStep 1068731 = 1603097) B1603097
theorem B2412233 : Blo 1068616 2412233 := bstep (se 2 (by rfl) ⟨904587, by rfl⟩ : syracuseStep 2412233 = 1809175) B1809175
theorem B1068807 : Blo 1068616 1068807 := bstep (se 1 (by rfl) ⟨801605, by rfl⟩ : syracuseStep 1068807 = 1603211) B1603211
theorem B1068815 : Blo 1068616 1068815 := bstep (se 1 (by rfl) ⟨801611, by rfl⟩ : syracuseStep 1068815 = 1603223) B1603223
theorem B1068859 : Blo 1068616 1068859 := bstep (se 1 (by rfl) ⟨801644, by rfl⟩ : syracuseStep 1068859 = 1603289) B1603289
theorem B1068935 : Blo 1068616 1068935 := bstep (se 1 (by rfl) ⟨801701, by rfl⟩ : syracuseStep 1068935 = 1603403) B1603403
theorem B1068943 : Blo 1068616 1068943 := bstep (se 1 (by rfl) ⟨801707, by rfl⟩ : syracuseStep 1068943 = 1603415) B1603415
theorem B1068987 : Blo 1068616 1068987 := bstep (se 1 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 1068987 = 1603481) B1603481
theorem B1069063 : Blo 1068616 1069063 := bstep (se 1 (by rfl) ⟨801797, by rfl⟩ : syracuseStep 1069063 = 1603595) B1603595
theorem B1069071 : Blo 1068616 1069071 := bstep (se 1 (by rfl) ⟨801803, by rfl⟩ : syracuseStep 1069071 = 1603607) B1603607
theorem B1069115 : Blo 1068616 1069115 := bstep (se 1 (by rfl) ⟨801836, by rfl⟩ : syracuseStep 1069115 = 1603673) B1603673
theorem B9883781 : Blo 1068616 9883781 := bstep (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) B1853209
theorem B1069191 : Blo 1068616 1069191 := bstep (se 1 (by rfl) ⟨801893, by rfl⟩ : syracuseStep 1069191 = 1603787) B1603787
theorem B1069199 : Blo 1068616 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B1069243 : Blo 1068616 1069243 := bstep (se 1 (by rfl) ⟨801932, by rfl⟩ : syracuseStep 1069243 = 1603865) B1603865
theorem B1069319 : Blo 1068616 1069319 := bstep (se 1 (by rfl) ⟨801989, by rfl⟩ : syracuseStep 1069319 = 1603979) B1603979
theorem B1069327 : Blo 1068616 1069327 := bstep (se 1 (by rfl) ⟨801995, by rfl⟩ : syracuseStep 1069327 = 1603991) B1603991
theorem B1069371 : Blo 1068616 1069371 := bstep (se 1 (by rfl) ⟨802028, by rfl⟩ : syracuseStep 1069371 = 1604057) B1604057
theorem B1069447 : Blo 1068616 1069447 := bstep (se 1 (by rfl) ⟨802085, by rfl⟩ : syracuseStep 1069447 = 1604171) B1604171
theorem B2412935 : Blo 1068616 2412935 := bstep (se 1 (by rfl) ⟨1809701, by rfl⟩ : syracuseStep 2412935 = 3619403) B3619403
theorem B1069455 : Blo 1068616 1069455 := bstep (se 1 (by rfl) ⟨802091, by rfl⟩ : syracuseStep 1069455 = 1604183) B1604183
theorem B1069499 : Blo 1068616 1069499 := bstep (se 1 (by rfl) ⟨802124, by rfl⟩ : syracuseStep 1069499 = 1604249) B1604249
theorem B1069575 : Blo 1068616 1069575 := bstep (se 1 (by rfl) ⟨802181, by rfl⟩ : syracuseStep 1069575 = 1604363) B1604363
theorem B1069583 : Blo 1068616 1069583 := bstep (se 1 (by rfl) ⟨802187, by rfl⟩ : syracuseStep 1069583 = 1604375) B1604375
theorem B1069627 : Blo 1068616 1069627 := bstep (se 1 (by rfl) ⟨802220, by rfl⟩ : syracuseStep 1069627 = 1604441) B1604441
theorem B2413115 : Blo 1068616 2413115 := bstep (se 1 (by rfl) ⟨1809836, by rfl⟩ : syracuseStep 2413115 = 3619673) B3619673
theorem B1069703 : Blo 1068616 1069703 := bstep (se 1 (by rfl) ⟨802277, by rfl⟩ : syracuseStep 1069703 = 1604555) B1604555
theorem B1069711 : Blo 1068616 1069711 := bstep (se 1 (by rfl) ⟨802283, by rfl⟩ : syracuseStep 1069711 = 1604567) B1604567
theorem B2413241 : Blo 1068616 2413241 := bstep (se 2 (by rfl) ⟨904965, by rfl⟩ : syracuseStep 2413241 = 1809931) B1809931
theorem B1069755 : Blo 1068616 1069755 := bstep (se 1 (by rfl) ⟨802316, by rfl⟩ : syracuseStep 1069755 = 1604633) B1604633
theorem B4117229 : Blo 1068616 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B2708225 : Blo 1068616 2708225 := bstep (se 2 (by rfl) ⟨1015584, by rfl⟩ : syracuseStep 2708225 = 2031169) B2031169
theorem B5788417 : Blo 1068616 5788417 := bstep (se 2 (by rfl) ⟨2170656, by rfl⟩ : syracuseStep 5788417 = 4341313) B4341313
theorem B1069831 : Blo 1068616 1069831 := bstep (se 1 (by rfl) ⟨802373, by rfl⟩ : syracuseStep 1069831 = 1604747) B1604747
theorem B1069839 : Blo 1068616 1069839 := bstep (se 1 (by rfl) ⟨802379, by rfl⟩ : syracuseStep 1069839 = 1604759) B1604759
theorem B2577167 : Blo 1068616 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B1069883 : Blo 1068616 1069883 := bstep (se 1 (by rfl) ⟨802412, by rfl⟩ : syracuseStep 1069883 = 1604825) B1604825
theorem B1069959 : Blo 1068616 1069959 := bstep (se 1 (by rfl) ⟨802469, by rfl⟩ : syracuseStep 1069959 = 1604939) B1604939
theorem B1069967 : Blo 1068616 1069967 := bstep (se 1 (by rfl) ⟨802475, by rfl⟩ : syracuseStep 1069967 = 1604951) B1604951
theorem B1070011 : Blo 1068616 1070011 := bstep (se 1 (by rfl) ⟨802508, by rfl⟩ : syracuseStep 1070011 = 1605017) B1605017
theorem B1070087 : Blo 1068616 1070087 := bstep (se 1 (by rfl) ⟨802565, by rfl⟩ : syracuseStep 1070087 = 1605131) B1605131
theorem B1070095 : Blo 1068616 1070095 := bstep (se 1 (by rfl) ⟨802571, by rfl⟩ : syracuseStep 1070095 = 1605143) B1605143
theorem B1070139 : Blo 1068616 1070139 := bstep (se 1 (by rfl) ⟨802604, by rfl⟩ : syracuseStep 1070139 = 1605209) B1605209
theorem B2708599 : Blo 1068616 2708599 := bstep (se 1 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 2708599 = 4062899) B4062899
theorem B1070215 : Blo 1068616 1070215 := bstep (se 1 (by rfl) ⟨802661, by rfl⟩ : syracuseStep 1070215 = 1605323) B1605323
theorem B1070223 : Blo 1068616 1070223 := bstep (se 1 (by rfl) ⟨802667, by rfl⟩ : syracuseStep 1070223 = 1605335) B1605335
theorem B1070267 : Blo 1068616 1070267 := bstep (se 1 (by rfl) ⟨802700, by rfl⟩ : syracuseStep 1070267 = 1605401) B1605401
theorem B1070343 : Blo 1068616 1070343 := bstep (se 1 (by rfl) ⟨802757, by rfl⟩ : syracuseStep 1070343 = 1605515) B1605515
theorem B1070351 : Blo 1068616 1070351 := bstep (se 1 (by rfl) ⟨802763, by rfl⟩ : syracuseStep 1070351 = 1605527) B1605527
theorem B1070395 : Blo 1068616 1070395 := bstep (se 1 (by rfl) ⟨802796, by rfl⟩ : syracuseStep 1070395 = 1605593) B1605593
theorem B4576571 : Blo 1068616 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B1070471 : Blo 1068616 1070471 := bstep (se 1 (by rfl) ⟨802853, by rfl⟩ : syracuseStep 1070471 = 1605707) B1605707
theorem B1070479 : Blo 1068616 1070479 := bstep (se 1 (by rfl) ⟨802859, by rfl⟩ : syracuseStep 1070479 = 1605719) B1605719
theorem B1070523 : Blo 1068616 1070523 := bstep (se 1 (by rfl) ⟨802892, by rfl⟩ : syracuseStep 1070523 = 1605785) B1605785
theorem B24696323 : Blo 1068616 24696323 := bstep (se 1 (by rfl) ⟨18522242, by rfl⟩ : syracuseStep 24696323 = 37044485) B37044485
theorem B1070599 : Blo 1068616 1070599 := bstep (se 1 (by rfl) ⟨802949, by rfl⟩ : syracuseStep 1070599 = 1605899) B1605899
theorem B2283023 : Blo 1068616 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B1070607 : Blo 1068616 1070607 := bstep (se 1 (by rfl) ⟨802955, by rfl⟩ : syracuseStep 1070607 = 1605911) B1605911
theorem B2283041 : Blo 1068616 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B2709035 : Blo 1068616 2709035 := bstep (se 1 (by rfl) ⟨2031776, by rfl⟩ : syracuseStep 2709035 = 4063553) B4063553
theorem B1070651 : Blo 1068616 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B3298931 : Blo 1068616 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B1070727 : Blo 1068616 1070727 := bstep (se 1 (by rfl) ⟨803045, by rfl⟩ : syracuseStep 1070727 = 1606091) B1606091
theorem B1070735 : Blo 1068616 1070735 := bstep (se 1 (by rfl) ⟨803051, by rfl⟩ : syracuseStep 1070735 = 1606103) B1606103
theorem B1070779 : Blo 1068616 1070779 := bstep (se 1 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 1070779 = 1606169) B1606169
theorem B1070855 : Blo 1068616 1070855 := bstep (se 1 (by rfl) ⟨803141, by rfl⟩ : syracuseStep 1070855 = 1606283) B1606283
theorem B1070863 : Blo 1068616 1070863 := bstep (se 1 (by rfl) ⟨803147, by rfl⟩ : syracuseStep 1070863 = 1606295) B1606295
theorem B1070907 : Blo 1068616 1070907 := bstep (se 1 (by rfl) ⟨803180, by rfl⟩ : syracuseStep 1070907 = 1606361) B1606361
theorem B2283383 : Blo 1068616 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B1070983 : Blo 1068616 1070983 := bstep (se 1 (by rfl) ⟨803237, by rfl⟩ : syracuseStep 1070983 = 1606475) B1606475
theorem B1070991 : Blo 1068616 1070991 := bstep (se 1 (by rfl) ⟨803243, by rfl⟩ : syracuseStep 1070991 = 1606487) B1606487
theorem B7329689 : Blo 1068616 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1071035 : Blo 1068616 1071035 := bstep (se 1 (by rfl) ⟨803276, by rfl⟩ : syracuseStep 1071035 = 1606553) B1606553
theorem B1071111 : Blo 1068616 1071111 := bstep (se 1 (by rfl) ⟨803333, by rfl⟩ : syracuseStep 1071111 = 1606667) B1606667
theorem B7821323 : Blo 1068616 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B1071119 : Blo 1068616 1071119 := bstep (se 1 (by rfl) ⟨803339, by rfl⟩ : syracuseStep 1071119 = 1606679) B1606679
theorem B4577323 : Blo 1068616 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B1071163 : Blo 1068616 1071163 := bstep (se 1 (by rfl) ⟨803372, by rfl⟩ : syracuseStep 1071163 = 1606745) B1606745
theorem B1071239 : Blo 1068616 1071239 := bstep (se 1 (by rfl) ⟨803429, by rfl⟩ : syracuseStep 1071239 = 1606859) B1606859
theorem B1071247 : Blo 1068616 1071247 := bstep (se 1 (by rfl) ⟨803435, by rfl⟩ : syracuseStep 1071247 = 1606871) B1606871
theorem B1071291 : Blo 1068616 1071291 := bstep (se 1 (by rfl) ⟨803468, by rfl⟩ : syracuseStep 1071291 = 1606937) B1606937
theorem B1071367 : Blo 1068616 1071367 := bstep (se 1 (by rfl) ⟨803525, by rfl⟩ : syracuseStep 1071367 = 1607051) B1607051
theorem B1071375 : Blo 1068616 1071375 := bstep (se 1 (by rfl) ⟨803531, by rfl⟩ : syracuseStep 1071375 = 1607063) B1607063
theorem B1071419 : Blo 1068616 1071419 := bstep (se 1 (by rfl) ⟨803564, by rfl⟩ : syracuseStep 1071419 = 1607129) B1607129
theorem B2709875 : Blo 1068616 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B3660167 : Blo 1068616 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B2709895 : Blo 1068616 2709895 := bstep (se 1 (by rfl) ⟨2032421, by rfl⟩ : syracuseStep 2709895 = 4064843) B4064843
theorem B1071495 : Blo 1068616 1071495 := bstep (se 1 (by rfl) ⟨803621, by rfl⟩ : syracuseStep 1071495 = 1607243) B1607243
theorem B1202575 : Blo 1068616 1202575 := bstep (se 1 (by rfl) ⟨901931, by rfl⟩ : syracuseStep 1202575 = 1803863) B1803863
theorem B1071503 : Blo 1068616 1071503 := bstep (se 1 (by rfl) ⟨803627, by rfl⟩ : syracuseStep 1071503 = 1607255) B1607255
theorem B1071547 : Blo 1068616 1071547 := bstep (se 1 (by rfl) ⟨803660, by rfl⟩ : syracuseStep 1071547 = 1607321) B1607321
theorem B1071623 : Blo 1068616 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B1071631 : Blo 1068616 1071631 := bstep (se 1 (by rfl) ⟨803723, by rfl⟩ : syracuseStep 1071631 = 1607447) B1607447
theorem B1071675 : Blo 1068616 1071675 := bstep (se 1 (by rfl) ⟨803756, by rfl⟩ : syracuseStep 1071675 = 1607513) B1607513
theorem B1071751 : Blo 1068616 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1071759 : Blo 1068616 1071759 := bstep (se 1 (by rfl) ⟨803819, by rfl⟩ : syracuseStep 1071759 = 1607639) B1607639
theorem B2710169 : Blo 1068616 2710169 := bstep (se 2 (by rfl) ⟨1016313, by rfl⟩ : syracuseStep 2710169 = 2032627) B2032627
theorem B1071803 : Blo 1068616 1071803 := bstep (se 1 (by rfl) ⟨803852, by rfl⟩ : syracuseStep 1071803 = 1607705) B1607705
theorem B1071879 : Blo 1068616 1071879 := bstep (se 1 (by rfl) ⟨803909, by rfl⟩ : syracuseStep 1071879 = 1607819) B1607819
theorem B1071887 : Blo 1068616 1071887 := bstep (se 1 (by rfl) ⟨803915, by rfl⟩ : syracuseStep 1071887 = 1607831) B1607831
theorem B2710331 : Blo 1068616 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B1071931 : Blo 1068616 1071931 := bstep (se 1 (by rfl) ⟨803948, by rfl⟩ : syracuseStep 1071931 = 1607897) B1607897
theorem B1203079 : Blo 1068616 1203079 := bstep (se 1 (by rfl) ⟨902309, by rfl⟩ : syracuseStep 1203079 = 1804619) B1804619
theorem B1072007 : Blo 1068616 1072007 := bstep (se 1 (by rfl) ⟨804005, by rfl⟩ : syracuseStep 1072007 = 1608011) B1608011
theorem B1072015 : Blo 1068616 1072015 := bstep (se 1 (by rfl) ⟨804011, by rfl⟩ : syracuseStep 1072015 = 1608023) B1608023
theorem B1072059 : Blo 1068616 1072059 := bstep (se 1 (by rfl) ⟨804044, by rfl⟩ : syracuseStep 1072059 = 1608089) B1608089
theorem B1072135 : Blo 1068616 1072135 := bstep (se 1 (by rfl) ⟨804101, by rfl⟩ : syracuseStep 1072135 = 1608203) B1608203
theorem B2710543 : Blo 1068616 2710543 := bstep (se 1 (by rfl) ⟨2032907, by rfl⟩ : syracuseStep 2710543 = 4065815) B4065815
theorem B1072143 : Blo 1068616 1072143 := bstep (se 1 (by rfl) ⟨804107, by rfl⟩ : syracuseStep 1072143 = 1608215) B1608215
theorem B1203259 : Blo 1068616 1203259 := bstep (se 1 (by rfl) ⟨902444, by rfl⟩ : syracuseStep 1203259 = 1804889) B1804889
theorem B1072187 : Blo 1068616 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B7724119 : Blo 1068616 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B1072263 : Blo 1068616 1072263 := bstep (se 1 (by rfl) ⟨804197, by rfl⟩ : syracuseStep 1072263 = 1608395) B1608395
theorem B1072271 : Blo 1068616 1072271 := bstep (se 1 (by rfl) ⟨804203, by rfl⟩ : syracuseStep 1072271 = 1608407) B1608407
theorem B1072315 : Blo 1068616 1072315 := bstep (se 1 (by rfl) ⟨804236, by rfl⟩ : syracuseStep 1072315 = 1608473) B1608473
theorem B1072391 : Blo 1068616 1072391 := bstep (se 1 (by rfl) ⟨804293, by rfl⟩ : syracuseStep 1072391 = 1608587) B1608587
theorem B1072399 : Blo 1068616 1072399 := bstep (se 1 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 1072399 = 1608599) B1608599
theorem B2710817 : Blo 1068616 2710817 := bstep (se 2 (by rfl) ⟨1016556, by rfl⟩ : syracuseStep 2710817 = 2033113) B2033113
theorem B1072443 : Blo 1068616 1072443 := bstep (se 1 (by rfl) ⟨804332, by rfl⟩ : syracuseStep 1072443 = 1608665) B1608665
theorem B1072519 : Blo 1068616 1072519 := bstep (se 1 (by rfl) ⟨804389, by rfl⟩ : syracuseStep 1072519 = 1608779) B1608779
theorem B1072527 : Blo 1068616 1072527 := bstep (se 1 (by rfl) ⟨804395, by rfl⟩ : syracuseStep 1072527 = 1608791) B1608791
theorem B1072571 : Blo 1068616 1072571 := bstep (se 1 (by rfl) ⟨804428, by rfl⟩ : syracuseStep 1072571 = 1608857) B1608857
theorem B1203727 : Blo 1068616 1203727 := bstep (se 1 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 1203727 = 1805591) B1805591
theorem B4120183 : Blo 1068616 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B10280677 : Blo 1068616 10280677 := bstep (se 4 (by rfl) ⟨963813, by rfl⟩ : syracuseStep 10280677 = 1927627) B1927627
theorem B100228913 : Blo 1068616 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B6086603 : Blo 1068616 6086603 := bstep (se 1 (by rfl) ⟨4564952, by rfl⟩ : syracuseStep 6086603 = 9129905) B9129905
theorem B1204231 : Blo 1068616 1204231 := bstep (se 1 (by rfl) ⟨903173, by rfl⟩ : syracuseStep 1204231 = 1806347) B1806347
theorem B1204411 : Blo 1068616 1204411 := bstep (se 1 (by rfl) ⟨903308, by rfl⟩ : syracuseStep 1204411 = 1806617) B1806617
theorem B2711819 : Blo 1068616 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B4579699 : Blo 1068616 4579699 := bstep (se 1 (by rfl) ⟨3434774, by rfl⟩ : syracuseStep 4579699 = 6869549) B6869549
theorem B6087059 : Blo 1068616 6087059 := bstep (se 1 (by rfl) ⟨4565294, by rfl⟩ : syracuseStep 6087059 = 9130589) B9130589
theorem B11887069 : Blo 1068616 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B1204879 : Blo 1068616 1204879 := bstep (se 1 (by rfl) ⟨903659, by rfl⟩ : syracuseStep 1204879 = 1807319) B1807319
theorem B9134963 : Blo 1068616 9134963 := bstep (se 1 (by rfl) ⟨6851222, by rfl⟩ : syracuseStep 9134963 = 13702445) B13702445
theorem B2712467 : Blo 1068616 2712467 := bstep (se 1 (by rfl) ⟨2034350, by rfl⟩ : syracuseStep 2712467 = 4068701) B4068701
theorem B1205383 : Blo 1068616 1205383 := bstep (se 1 (by rfl) ⟨904037, by rfl⟩ : syracuseStep 1205383 = 1808075) B1808075
theorem B2712761 : Blo 1068616 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B9135341 : Blo 1068616 9135341 := bstep (se 3 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 9135341 = 3425753) B3425753
theorem B1205563 : Blo 1068616 1205563 := bstep (se 1 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 1205563 = 1808345) B1808345
theorem B26076593 : Blo 1068616 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B13395557 : Blo 1068616 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B1206031 : Blo 1068616 1206031 := bstep (se 1 (by rfl) ⟨904523, by rfl⟩ : syracuseStep 1206031 = 1809047) B1809047
theorem B2713459 : Blo 1068616 2713459 := bstep (se 1 (by rfl) ⟨2035094, by rfl⟩ : syracuseStep 2713459 = 4070189) B4070189
theorem B2713601 : Blo 1068616 2713601 := bstep (se 2 (by rfl) ⟨1017600, by rfl⟩ : syracuseStep 2713601 = 2035201) B2035201
theorem B1206535 : Blo 1068616 1206535 := bstep (se 1 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 1206535 = 1809803) B1809803
theorem B2714057 : Blo 1068616 2714057 := bstep (se 2 (by rfl) ⟨1017771, by rfl⟩ : syracuseStep 2714057 = 2035543) B2035543
theorem B4057553 : Blo 1068616 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B7825997 : Blo 1068616 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B2714411 : Blo 1068616 2714411 := bstep (se 1 (by rfl) ⟨2035808, by rfl⟩ : syracuseStep 2714411 = 4071617) B4071617
theorem B4058009 : Blo 1068616 4058009 := bstep (se 2 (by rfl) ⟨1521753, by rfl⟩ : syracuseStep 4058009 = 3043507) B3043507
theorem B2747321 : Blo 1068616 2747321 := bstep (se 2 (by rfl) ⟨1030245, by rfl⟩ : syracuseStep 2747321 = 2060491) B2060491
theorem B1141819 : Blo 1068616 1141819 := bstep (se 1 (by rfl) ⟨856364, by rfl⟩ : syracuseStep 1141819 = 1712729) B1712729
theorem B1928377 : Blo 1068616 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B8121545 : Blo 1068616 8121545 := bstep (se 2 (by rfl) ⟨3045579, by rfl⟩ : syracuseStep 8121545 = 6091159) B6091159
theorem B1928507 : Blo 1068616 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B5140169 : Blo 1068616 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B5205875 : Blo 1068616 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B4059179 : Blo 1068616 4059179 := bstep (se 1 (by rfl) ⟨3044384, by rfl⟩ : syracuseStep 4059179 = 6088769) B6088769
theorem B9138653 : Blo 1068616 9138653 := bstep (se 3 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 9138653 = 3426995) B3426995
theorem B3044395 : Blo 1068616 3044395 := bstep (se 1 (by rfl) ⟨2283296, by rfl⟩ : syracuseStep 3044395 = 4566593) B4566593
theorem B30897389 : Blo 1068616 30897389 := bstep (se 3 (by rfl) ⟨5793260, by rfl⟩ : syracuseStep 30897389 = 11586521) B11586521
theorem B3863789 : Blo 1068616 3863789 := bstep (se 3 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 3863789 = 1448921) B1448921
theorem B3044623 : Blo 1068616 3044623 := bstep (se 1 (by rfl) ⟨2283467, by rfl⟩ : syracuseStep 3044623 = 4566935) B4566935
theorem B1602935 : Blo 1068616 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B7337351 : Blo 1068616 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B1602959 : Blo 1068616 1602959 := bstep (se 1 (by rfl) ⟨1202219, by rfl⟩ : syracuseStep 1602959 = 2404439) B2404439
theorem B1603001 : Blo 1068616 1603001 := bstep (se 2 (by rfl) ⟨601125, by rfl⟩ : syracuseStep 1603001 = 1202251) B1202251
theorem B9139715 : Blo 1068616 9139715 := bstep (se 1 (by rfl) ⟨6854786, by rfl⟩ : syracuseStep 9139715 = 13709573) B13709573
theorem B1603079 : Blo 1068616 1603079 := bstep (se 1 (by rfl) ⟨1202309, by rfl⟩ : syracuseStep 1603079 = 2404619) B2404619
theorem B3044897 : Blo 1068616 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B1603115 : Blo 1068616 1603115 := bstep (se 1 (by rfl) ⟨1202336, by rfl⟩ : syracuseStep 1603115 = 2404673) B2404673
theorem B1603145 : Blo 1068616 1603145 := bstep (se 2 (by rfl) ⟨601179, by rfl⟩ : syracuseStep 1603145 = 1202359) B1202359
theorem B1603259 : Blo 1068616 1603259 := bstep (se 1 (by rfl) ⟨1202444, by rfl⟩ : syracuseStep 1603259 = 2404889) B2404889
theorem B1603319 : Blo 1068616 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1603343 : Blo 1068616 1603343 := bstep (se 1 (by rfl) ⟨1202507, by rfl⟩ : syracuseStep 1603343 = 2405015) B2405015
theorem B1603385 : Blo 1068616 1603385 := bstep (se 2 (by rfl) ⟨601269, by rfl⟩ : syracuseStep 1603385 = 1202539) B1202539
theorem B3045239 : Blo 1068616 3045239 := bstep (se 1 (by rfl) ⟨2283929, by rfl⟩ : syracuseStep 3045239 = 4567859) B4567859
theorem B1603463 : Blo 1068616 1603463 := bstep (se 1 (by rfl) ⟨1202597, by rfl⟩ : syracuseStep 1603463 = 2405195) B2405195
theorem B1603499 : Blo 1068616 1603499 := bstep (se 1 (by rfl) ⟨1202624, by rfl⟩ : syracuseStep 1603499 = 2405249) B2405249
theorem B1603529 : Blo 1068616 1603529 := bstep (se 2 (by rfl) ⟨601323, by rfl⟩ : syracuseStep 1603529 = 1202647) B1202647
theorem B4061137 : Blo 1068616 4061137 := bstep (se 2 (by rfl) ⟨1522926, by rfl⟩ : syracuseStep 4061137 = 3045853) B3045853
theorem B6944779 : Blo 1068616 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B1603643 : Blo 1068616 1603643 := bstep (se 1 (by rfl) ⟨1202732, by rfl⟩ : syracuseStep 1603643 = 2405465) B2405465
theorem B2029627 : Blo 1068616 2029627 := bstep (se 1 (by rfl) ⟨1522220, by rfl⟩ : syracuseStep 2029627 = 3044441) B3044441
theorem B1144891 : Blo 1068616 1144891 := bstep (se 1 (by rfl) ⟨858668, by rfl⟩ : syracuseStep 1144891 = 1717337) B1717337
theorem B1603703 : Blo 1068616 1603703 := bstep (se 1 (by rfl) ⟨1202777, by rfl⟩ : syracuseStep 1603703 = 2405555) B2405555
theorem B1603727 : Blo 1068616 1603727 := bstep (se 1 (by rfl) ⟨1202795, by rfl⟩ : syracuseStep 1603727 = 2405591) B2405591
theorem B1603769 : Blo 1068616 1603769 := bstep (se 2 (by rfl) ⟨601413, by rfl⟩ : syracuseStep 1603769 = 1202827) B1202827
theorem B4061441 : Blo 1068616 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B1603847 : Blo 1068616 1603847 := bstep (se 1 (by rfl) ⟨1202885, by rfl⟩ : syracuseStep 1603847 = 2405771) B2405771
theorem B5142799 : Blo 1068616 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B1603883 : Blo 1068616 1603883 := bstep (se 1 (by rfl) ⟨1202912, by rfl⟩ : syracuseStep 1603883 = 2405825) B2405825
theorem B1603913 : Blo 1068616 1603913 := bstep (se 2 (by rfl) ⟨601467, by rfl⟩ : syracuseStep 1603913 = 1202935) B1202935
theorem B5798279 : Blo 1068616 5798279 := bstep (se 1 (by rfl) ⟨4348709, by rfl⟩ : syracuseStep 5798279 = 8697419) B8697419
theorem B1604027 : Blo 1068616 1604027 := bstep (se 1 (by rfl) ⟨1203020, by rfl⟩ : syracuseStep 1604027 = 2406041) B2406041
theorem B1604087 : Blo 1068616 1604087 := bstep (se 1 (by rfl) ⟨1203065, by rfl⟩ : syracuseStep 1604087 = 2406131) B2406131
theorem B3045899 : Blo 1068616 3045899 := bstep (se 1 (by rfl) ⟨2284424, by rfl⟩ : syracuseStep 3045899 = 4568849) B4568849
theorem B1604111 : Blo 1068616 1604111 := bstep (se 1 (by rfl) ⟨1203083, by rfl⟩ : syracuseStep 1604111 = 2406167) B2406167
theorem B3865117 : Blo 1068616 3865117 := bstep (se 3 (by rfl) ⟨724709, by rfl⟩ : syracuseStep 3865117 = 1449419) B1449419
theorem B2030113 : Blo 1068616 2030113 := bstep (se 2 (by rfl) ⟨761292, by rfl⟩ : syracuseStep 2030113 = 1522585) B1522585
theorem B1604153 : Blo 1068616 1604153 := bstep (se 2 (by rfl) ⟨601557, by rfl⟩ : syracuseStep 1604153 = 1203115) B1203115
theorem B1604231 : Blo 1068616 1604231 := bstep (se 1 (by rfl) ⟨1203173, by rfl⟩ : syracuseStep 1604231 = 2406347) B2406347
theorem B1604267 : Blo 1068616 1604267 := bstep (se 1 (by rfl) ⟨1203200, by rfl⟩ : syracuseStep 1604267 = 2406401) B2406401
theorem B1604297 : Blo 1068616 1604297 := bstep (se 2 (by rfl) ⟨601611, by rfl⟩ : syracuseStep 1604297 = 1203223) B1203223
theorem B4061897 : Blo 1068616 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B1604411 : Blo 1068616 1604411 := bstep (se 1 (by rfl) ⟨1203308, by rfl⟩ : syracuseStep 1604411 = 2406617) B2406617
theorem B1604471 : Blo 1068616 1604471 := bstep (se 1 (by rfl) ⟨1203353, by rfl⟩ : syracuseStep 1604471 = 2406707) B2406707
theorem B1604495 : Blo 1068616 1604495 := bstep (se 1 (by rfl) ⟨1203371, by rfl⟩ : syracuseStep 1604495 = 2406743) B2406743
theorem B1604537 : Blo 1068616 1604537 := bstep (se 2 (by rfl) ⟨601701, by rfl⟩ : syracuseStep 1604537 = 1203403) B1203403
theorem B18545669 : Blo 1068616 18545669 := bstep (se 4 (by rfl) ⟨1738656, by rfl⟩ : syracuseStep 18545669 = 3477313) B3477313
theorem B1604615 : Blo 1068616 1604615 := bstep (se 1 (by rfl) ⟨1203461, by rfl⟩ : syracuseStep 1604615 = 2406923) B2406923
theorem B1604651 : Blo 1068616 1604651 := bstep (se 1 (by rfl) ⟨1203488, by rfl⟩ : syracuseStep 1604651 = 2406977) B2406977
theorem B1604681 : Blo 1068616 1604681 := bstep (se 2 (by rfl) ⟨601755, by rfl⟩ : syracuseStep 1604681 = 1203511) B1203511
theorem B13696087 : Blo 1068616 13696087 := bstep (se 1 (by rfl) ⟨10272065, by rfl⟩ : syracuseStep 13696087 = 20544131) B20544131
theorem B1604795 : Blo 1068616 1604795 := bstep (se 1 (by rfl) ⟨1203596, by rfl⟩ : syracuseStep 1604795 = 2407193) B2407193
theorem B1604855 : Blo 1068616 1604855 := bstep (se 1 (by rfl) ⟨1203641, by rfl⟩ : syracuseStep 1604855 = 2407283) B2407283
theorem B1604879 : Blo 1068616 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B1932587 : Blo 1068616 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B1604921 : Blo 1068616 1604921 := bstep (se 2 (by rfl) ⟨601845, by rfl⟩ : syracuseStep 1604921 = 1203691) B1203691
theorem B1604999 : Blo 1068616 1604999 := bstep (se 1 (by rfl) ⟨1203749, by rfl⟩ : syracuseStep 1604999 = 2407499) B2407499
theorem B1605035 : Blo 1068616 1605035 := bstep (se 1 (by rfl) ⟨1203776, by rfl⟩ : syracuseStep 1605035 = 2407553) B2407553
theorem B1605065 : Blo 1068616 1605065 := bstep (se 2 (by rfl) ⟨601899, by rfl⟩ : syracuseStep 1605065 = 1203799) B1203799
theorem B1605179 : Blo 1068616 1605179 := bstep (se 1 (by rfl) ⟨1203884, by rfl⟩ : syracuseStep 1605179 = 2407769) B2407769
theorem B10976887 : Blo 1068616 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B1605239 : Blo 1068616 1605239 := bstep (se 1 (by rfl) ⟨1203929, by rfl⟩ : syracuseStep 1605239 = 2407859) B2407859
theorem B6520439 : Blo 1068616 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B1605263 : Blo 1068616 1605263 := bstep (se 1 (by rfl) ⟨1203947, by rfl⟩ : syracuseStep 1605263 = 2407895) B2407895
theorem B1605305 : Blo 1068616 1605305 := bstep (se 2 (by rfl) ⟨601989, by rfl⟩ : syracuseStep 1605305 = 1203979) B1203979
theorem B1605383 : Blo 1068616 1605383 := bstep (se 1 (by rfl) ⟨1204037, by rfl⟩ : syracuseStep 1605383 = 2408075) B2408075
theorem B1605419 : Blo 1068616 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B2031419 : Blo 1068616 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B1605449 : Blo 1068616 1605449 := bstep (se 2 (by rfl) ⟨602043, by rfl⟩ : syracuseStep 1605449 = 1204087) B1204087
theorem B1605563 : Blo 1068616 1605563 := bstep (se 1 (by rfl) ⟨1204172, by rfl⟩ : syracuseStep 1605563 = 2408345) B2408345
theorem B1605623 : Blo 1068616 1605623 := bstep (se 1 (by rfl) ⟨1204217, by rfl⟩ : syracuseStep 1605623 = 2408435) B2408435
theorem B1605641 : Blo 1068616 1605641 := bstep (se 2 (by rfl) ⟨602115, by rfl⟩ : syracuseStep 1605641 = 1204231) B1204231
theorem B2031655 : Blo 1068616 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B1605671 : Blo 1068616 1605671 := bstep (se 1 (by rfl) ⟨1204253, by rfl⟩ : syracuseStep 1605671 = 2408507) B2408507
theorem B1605755 : Blo 1068616 1605755 := bstep (se 1 (by rfl) ⟨1204316, by rfl⟩ : syracuseStep 1605755 = 2408633) B2408633
theorem B4063385 : Blo 1068616 4063385 := bstep (se 2 (by rfl) ⟨1523769, by rfl⟩ : syracuseStep 4063385 = 3047539) B3047539
theorem B1605881 : Blo 1068616 1605881 := bstep (se 2 (by rfl) ⟨602205, by rfl⟩ : syracuseStep 1605881 = 1204411) B1204411
theorem B1605983 : Blo 1068616 1605983 := bstep (se 1 (by rfl) ⟨1204487, by rfl⟩ : syracuseStep 1605983 = 2408975) B2408975
theorem B1605995 : Blo 1068616 1605995 := bstep (se 1 (by rfl) ⟨1204496, by rfl⟩ : syracuseStep 1605995 = 2408993) B2408993
theorem B22282775 : Blo 1068616 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B1606223 : Blo 1068616 1606223 := bstep (se 1 (by rfl) ⟨1204667, by rfl⟩ : syracuseStep 1606223 = 2409335) B2409335
theorem B4063841 : Blo 1068616 4063841 := bstep (se 2 (by rfl) ⟨1523940, by rfl⟩ : syracuseStep 4063841 = 3047881) B3047881
theorem B1606343 : Blo 1068616 1606343 := bstep (se 1 (by rfl) ⟨1204757, by rfl⟩ : syracuseStep 1606343 = 2409515) B2409515
theorem B21988097 : Blo 1068616 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B1606505 : Blo 1068616 1606505 := bstep (se 2 (by rfl) ⟨602439, by rfl⟩ : syracuseStep 1606505 = 1204879) B1204879
theorem B8127377 : Blo 1068616 8127377 := bstep (se 2 (by rfl) ⟨3047766, by rfl⟩ : syracuseStep 8127377 = 6095533) B6095533
theorem B1606583 : Blo 1068616 1606583 := bstep (se 1 (by rfl) ⟨1204937, by rfl⟩ : syracuseStep 1606583 = 2409875) B2409875
theorem B1606619 : Blo 1068616 1606619 := bstep (se 1 (by rfl) ⟨1204964, by rfl⟩ : syracuseStep 1606619 = 2409929) B2409929
theorem B8684509 : Blo 1068616 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B1803343 : Blo 1068616 1803343 := bstep (se 1 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 1803343 = 2705015) B2705015
theorem B1803593 : Blo 1068616 1803593 := bstep (se 2 (by rfl) ⟨676347, by rfl⟩ : syracuseStep 1803593 = 1352695) B1352695
theorem B5571983 : Blo 1068616 5571983 := bstep (se 1 (by rfl) ⟨4178987, by rfl⟩ : syracuseStep 5571983 = 8357975) B8357975
theorem B1607087 : Blo 1068616 1607087 := bstep (se 1 (by rfl) ⟨1205315, by rfl⟩ : syracuseStep 1607087 = 2410631) B2410631
theorem B1607177 : Blo 1068616 1607177 := bstep (se 2 (by rfl) ⟨602691, by rfl⟩ : syracuseStep 1607177 = 1205383) B1205383
theorem B1607207 : Blo 1068616 1607207 := bstep (se 1 (by rfl) ⟨1205405, by rfl⟩ : syracuseStep 1607207 = 2410811) B2410811
theorem B1607291 : Blo 1068616 1607291 := bstep (se 1 (by rfl) ⟨1205468, by rfl⟩ : syracuseStep 1607291 = 2410937) B2410937
theorem B2033363 : Blo 1068616 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B1804025 : Blo 1068616 1804025 := bstep (se 2 (by rfl) ⟨676509, by rfl⟩ : syracuseStep 1804025 = 1353019) B1353019
theorem B1607417 : Blo 1068616 1607417 := bstep (se 2 (by rfl) ⟨602781, by rfl⟩ : syracuseStep 1607417 = 1205563) B1205563
theorem B1607519 : Blo 1068616 1607519 := bstep (se 1 (by rfl) ⟨1205639, by rfl⟩ : syracuseStep 1607519 = 2411279) B2411279
theorem B2033515 : Blo 1068616 2033515 := bstep (se 1 (by rfl) ⟨1525136, by rfl⟩ : syracuseStep 2033515 = 3050273) B3050273
theorem B1607531 : Blo 1068616 1607531 := bstep (se 1 (by rfl) ⟨1205648, by rfl⟩ : syracuseStep 1607531 = 2411297) B2411297
theorem B1804207 : Blo 1068616 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B1804295 : Blo 1068616 1804295 := bstep (se 1 (by rfl) ⟨1353221, by rfl⟩ : syracuseStep 1804295 = 2706443) B2706443
theorem B4065299 : Blo 1068616 4065299 := bstep (se 1 (by rfl) ⟨3048974, by rfl⟩ : syracuseStep 4065299 = 6097949) B6097949
theorem B2033743 : Blo 1068616 2033743 := bstep (se 1 (by rfl) ⟨1525307, by rfl⟩ : syracuseStep 2033743 = 3050615) B3050615
theorem B1607759 : Blo 1068616 1607759 := bstep (se 1 (by rfl) ⟨1205819, by rfl⟩ : syracuseStep 1607759 = 2411639) B2411639
theorem B14092375 : Blo 1068616 14092375 := bstep (se 1 (by rfl) ⟨10569281, by rfl⟩ : syracuseStep 14092375 = 21138563) B21138563
theorem B1607879 : Blo 1068616 1607879 := bstep (se 1 (by rfl) ⟨1205909, by rfl⟩ : syracuseStep 1607879 = 2411819) B2411819
theorem B1804639 : Blo 1068616 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B1608041 : Blo 1068616 1608041 := bstep (se 2 (by rfl) ⟨603015, by rfl⟩ : syracuseStep 1608041 = 1206031) B1206031
theorem B1804727 : Blo 1068616 1804727 := bstep (se 1 (by rfl) ⟨1353545, by rfl⟩ : syracuseStep 1804727 = 2707091) B2707091
theorem B1608119 : Blo 1068616 1608119 := bstep (se 1 (by rfl) ⟨1206089, by rfl⟩ : syracuseStep 1608119 = 2412179) B2412179
theorem B1608155 : Blo 1068616 1608155 := bstep (se 1 (by rfl) ⟨1206116, by rfl⟩ : syracuseStep 1608155 = 2412233) B2412233
theorem B6589187 : Blo 1068616 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B3607415 : Blo 1068616 3607415 := bstep (se 1 (by rfl) ⟨2705561, by rfl⟩ : syracuseStep 3607415 = 5411123) B5411123
theorem B1608623 : Blo 1068616 1608623 := bstep (se 1 (by rfl) ⟨1206467, by rfl⟩ : syracuseStep 1608623 = 2412935) B2412935
theorem B1805321 : Blo 1068616 1805321 := bstep (se 2 (by rfl) ⟨676995, by rfl⟩ : syracuseStep 1805321 = 1353991) B1353991
theorem B1608713 : Blo 1068616 1608713 := bstep (se 2 (by rfl) ⟨603267, by rfl⟩ : syracuseStep 1608713 = 1206535) B1206535
theorem B1608743 : Blo 1068616 1608743 := bstep (se 1 (by rfl) ⟨1206557, by rfl⟩ : syracuseStep 1608743 = 2413115) B2413115
theorem B3607631 : Blo 1068616 3607631 := bstep (se 1 (by rfl) ⟨2705723, by rfl⟩ : syracuseStep 3607631 = 5411447) B5411447
theorem B1608827 : Blo 1068616 1608827 := bstep (se 1 (by rfl) ⟨1206620, by rfl⟩ : syracuseStep 1608827 = 2413241) B2413241
theorem B1805483 : Blo 1068616 1805483 := bstep (se 1 (by rfl) ⟨1354112, by rfl⟩ : syracuseStep 1805483 = 2708225) B2708225
theorem B8129807 : Blo 1068616 8129807 := bstep (se 1 (by rfl) ⟨6097355, by rfl⟩ : syracuseStep 8129807 = 12194711) B12194711
theorem B3608009 : Blo 1068616 3608009 := bstep (se 2 (by rfl) ⟨1353003, by rfl⟩ : syracuseStep 3608009 = 2706007) B2706007
theorem B3051047 : Blo 1068616 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B1805881 : Blo 1068616 1805881 := bstep (se 2 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 1805881 = 1354411) B1354411
theorem B4066955 : Blo 1068616 4066955 := bstep (se 1 (by rfl) ⟨3050216, by rfl⟩ : syracuseStep 4066955 = 6100433) B6100433
theorem B19566269 : Blo 1068616 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B1806023 : Blo 1068616 1806023 := bstep (se 1 (by rfl) ⟨1354517, by rfl⟩ : syracuseStep 1806023 = 2709035) B2709035
theorem B3608279 : Blo 1068616 3608279 := bstep (se 1 (by rfl) ⟨2706209, by rfl⟩ : syracuseStep 3608279 = 5412419) B5412419
theorem B2199287 : Blo 1068616 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B5213945 : Blo 1068616 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B1806185 : Blo 1068616 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B2166635 : Blo 1068616 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B3608495 : Blo 1068616 3608495 := bstep (se 1 (by rfl) ⟨2706371, by rfl⟩ : syracuseStep 3608495 = 5412743) B5412743
theorem B1445807 : Blo 1068616 1445807 := bstep (se 1 (by rfl) ⟨1084355, by rfl⟩ : syracuseStep 1445807 = 2168711) B2168711
theorem B4886459 : Blo 1068616 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B5214215 : Blo 1068616 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B1806583 : Blo 1068616 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B1806779 : Blo 1068616 1806779 := bstep (se 1 (by rfl) ⟨1355084, by rfl⟩ : syracuseStep 1806779 = 2710169) B2710169
theorem B1806887 : Blo 1068616 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B2167625 : Blo 1068616 2167625 := bstep (se 2 (by rfl) ⟨812859, by rfl⟩ : syracuseStep 2167625 = 1625719) B1625719
theorem B1807177 : Blo 1068616 1807177 := bstep (se 2 (by rfl) ⟨677691, by rfl⟩ : syracuseStep 1807177 = 1355383) B1355383
theorem B1807211 : Blo 1068616 1807211 := bstep (se 1 (by rfl) ⟨1355408, by rfl⟩ : syracuseStep 1807211 = 2710817) B2710817
theorem B4068215 : Blo 1068616 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B2167739 : Blo 1068616 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B66819275 : Blo 1068616 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B1807609 : Blo 1068616 1807609 := bstep (se 2 (by rfl) ⟨677853, by rfl⟩ : syracuseStep 1807609 = 1355707) B1355707
theorem B1807879 : Blo 1068616 1807879 := bstep (se 1 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 1807879 = 2711819) B2711819
theorem B8689373 : Blo 1068616 8689373 := bstep (se 3 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 8689373 = 3258515) B3258515
theorem B10295099 : Blo 1068616 10295099 := bstep (se 1 (by rfl) ⟨7721324, by rfl⟩ : syracuseStep 10295099 = 15442649) B15442649
theorem B4069187 : Blo 1068616 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B1808311 : Blo 1068616 1808311 := bstep (se 1 (by rfl) ⟨1356233, by rfl⟩ : syracuseStep 1808311 = 2712467) B2712467
theorem B7313465 : Blo 1068616 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B8132723 : Blo 1068616 8132723 := bstep (se 1 (by rfl) ⟨6099542, by rfl⟩ : syracuseStep 8132723 = 12199085) B12199085
theorem B1808507 : Blo 1068616 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B3610871 : Blo 1068616 3610871 := bstep (se 1 (by rfl) ⟨2708153, by rfl⟩ : syracuseStep 3610871 = 5416307) B5416307
theorem B6953303 : Blo 1068616 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B1808905 : Blo 1068616 1808905 := bstep (se 2 (by rfl) ⟨678339, by rfl⟩ : syracuseStep 1808905 = 1356679) B1356679
theorem B3611195 : Blo 1068616 3611195 := bstep (se 1 (by rfl) ⟨2708396, by rfl⟩ : syracuseStep 3611195 = 5416793) B5416793
theorem B1448527 : Blo 1068616 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B8460935 : Blo 1068616 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B6101639 : Blo 1068616 6101639 := bstep (se 1 (by rfl) ⟨4576229, by rfl⟩ : syracuseStep 6101639 = 9152459) B9152459
theorem B1809067 : Blo 1068616 1809067 := bstep (se 1 (by rfl) ⟨1356800, by rfl⟩ : syracuseStep 1809067 = 2713601) B2713601
theorem B3611465 : Blo 1068616 3611465 := bstep (se 2 (by rfl) ⟨1354299, by rfl⟩ : syracuseStep 3611465 = 2708599) B2708599
theorem B1809371 : Blo 1068616 1809371 := bstep (se 1 (by rfl) ⟨1357028, by rfl⟩ : syracuseStep 1809371 = 2714057) B2714057
theorem B5217331 : Blo 1068616 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B1809607 : Blo 1068616 1809607 := bstep (se 1 (by rfl) ⟨1357205, by rfl⟩ : syracuseStep 1809607 = 2714411) B2714411
theorem B1809769 : Blo 1068616 1809769 := bstep (se 2 (by rfl) ⟨678663, by rfl⟩ : syracuseStep 1809769 = 1357327) B1357327
theorem B4169089 : Blo 1068616 4169089 := bstep (se 2 (by rfl) ⟨1563408, by rfl⟩ : syracuseStep 4169089 = 3126817) B3126817
theorem B17669549 : Blo 1068616 17669549 := bstep (se 3 (by rfl) ⟨3313040, by rfl⟩ : syracuseStep 17669549 = 6626081) B6626081
theorem B4070857 : Blo 1068616 4070857 := bstep (se 2 (by rfl) ⟨1526571, by rfl⟩ : syracuseStep 4070857 = 3053143) B3053143
theorem B5414363 : Blo 1068616 5414363 := bstep (se 1 (by rfl) ⟨4060772, by rfl⟩ : syracuseStep 5414363 = 8121545) B8121545
theorem B4071161 : Blo 1068616 4071161 := bstep (se 2 (by rfl) ⟨1526685, by rfl⟩ : syracuseStep 4071161 = 3053371) B3053371
theorem B4071329 : Blo 1068616 4071329 := bstep (se 2 (by rfl) ⟨1526748, by rfl⟩ : syracuseStep 4071329 = 3053497) B3053497
theorem B4071343 : Blo 1068616 4071343 := bstep (se 1 (by rfl) ⟨3053507, by rfl⟩ : syracuseStep 4071343 = 6107015) B6107015
theorem B3612599 : Blo 1068616 3612599 := bstep (se 1 (by rfl) ⟨2709449, by rfl⟩ : syracuseStep 3612599 = 5418899) B5418899
theorem B5414849 : Blo 1068616 5414849 := bstep (se 2 (by rfl) ⟨2030568, by rfl⟩ : syracuseStep 5414849 = 4061137) B4061137
theorem B6103097 : Blo 1068616 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B6857065 : Blo 1068616 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B3613193 : Blo 1068616 3613193 := bstep (se 2 (by rfl) ⟨1354947, by rfl⟩ : syracuseStep 3613193 = 2709895) B2709895
theorem B7709357 : Blo 1068616 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B5153489 : Blo 1068616 5153489 := bstep (se 2 (by rfl) ⟨1932558, by rfl⟩ : syracuseStep 5153489 = 3865117) B3865117
theorem B19538761 : Blo 1068616 19538761 := bstep (se 2 (by rfl) ⟨7327035, by rfl⟩ : syracuseStep 19538761 = 14654071) B14654071
theorem B4072301 : Blo 1068616 4072301 := bstep (se 3 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 4072301 = 1527113) B1527113
theorem B7709585 : Blo 1068616 7709585 := bstep (se 2 (by rfl) ⟨2891094, by rfl⟩ : syracuseStep 7709585 = 5782189) B5782189
theorem B3614057 : Blo 1068616 3614057 := bstep (se 2 (by rfl) ⟨1355271, by rfl⟩ : syracuseStep 3614057 = 2710543) B2710543
theorem B18261449 : Blo 1068616 18261449 := bstep (se 2 (by rfl) ⟨6848043, by rfl⟩ : syracuseStep 18261449 = 13696087) B13696087
theorem B10298825 : Blo 1068616 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B1713703 : Blo 1068616 1713703 := bstep (se 1 (by rfl) ⟨1285277, by rfl⟩ : syracuseStep 1713703 = 2570555) B2570555
theorem B4401071 : Blo 1068616 4401071 := bstep (se 1 (by rfl) ⟨3300803, by rfl⟩ : syracuseStep 4401071 = 6601607) B6601607
theorem B3614651 : Blo 1068616 3614651 := bstep (se 1 (by rfl) ⟨2710988, by rfl⟩ : syracuseStep 3614651 = 5421977) B5421977
theorem B1714139 : Blo 1068616 1714139 := bstep (se 1 (by rfl) ⟨1285604, by rfl⟩ : syracuseStep 1714139 = 2571209) B2571209
theorem B12363779 : Blo 1068616 12363779 := bstep (se 1 (by rfl) ⟨9272834, by rfl⟩ : syracuseStep 12363779 = 18545669) B18545669
theorem B5417117 : Blo 1068616 5417117 := bstep (se 3 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 5417117 = 2031419) B2031419
theorem B1288391 : Blo 1068616 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B13707569 : Blo 1068616 13707569 := bstep (se 2 (by rfl) ⟨5140338, by rfl⟩ : syracuseStep 13707569 = 10280677) B10280677
theorem B21179015 : Blo 1068616 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B6106265 : Blo 1068616 6106265 := bstep (se 2 (by rfl) ⟨2289849, by rfl⟩ : syracuseStep 6106265 = 4579699) B4579699
theorem B3911017 : Blo 1068616 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B1715599 : Blo 1068616 1715599 := bstep (se 1 (by rfl) ⟨1286699, by rfl⟩ : syracuseStep 1715599 = 2573399) B2573399
theorem B5418413 : Blo 1068616 5418413 := bstep (se 3 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 5418413 = 2031905) B2031905
theorem B3616379 : Blo 1068616 3616379 := bstep (se 1 (by rfl) ⟨2712284, by rfl⟩ : syracuseStep 3616379 = 5424569) B5424569
theorem B3616541 : Blo 1068616 3616541 := bstep (se 3 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 3616541 = 1356203) B1356203
theorem B8138555 : Blo 1068616 8138555 := bstep (se 1 (by rfl) ⟨6103916, by rfl⟩ : syracuseStep 8138555 = 12207833) B12207833
theorem B4566851 : Blo 1068616 4566851 := bstep (se 1 (by rfl) ⟨3425138, by rfl⟩ : syracuseStep 4566851 = 6850277) B6850277
theorem B16461755 : Blo 1068616 16461755 := bstep (se 1 (by rfl) ⟨12346316, by rfl⟩ : syracuseStep 16461755 = 24692633) B24692633
theorem B3617243 : Blo 1068616 3617243 := bstep (se 1 (by rfl) ⟨2712932, by rfl⟩ : syracuseStep 3617243 = 5425865) B5425865
theorem B26063369 : Blo 1068616 26063369 := bstep (se 2 (by rfl) ⟨9773763, by rfl⟩ : syracuseStep 26063369 = 19547527) B19547527
theorem B2404961 : Blo 1068616 2404961 := bstep (se 2 (by rfl) ⟨901860, by rfl⟩ : syracuseStep 2404961 = 1803721) B1803721
theorem B7713481 : Blo 1068616 7713481 := bstep (se 2 (by rfl) ⟨2892555, by rfl⟩ : syracuseStep 7713481 = 5785111) B5785111
theorem B2405303 : Blo 1068616 2405303 := bstep (se 1 (by rfl) ⟨1803977, by rfl⟩ : syracuseStep 2405303 = 3607955) B3607955
theorem B5420033 : Blo 1068616 5420033 := bstep (se 2 (by rfl) ⟨2032512, by rfl⟩ : syracuseStep 5420033 = 4065025) B4065025
theorem B74036375 : Blo 1068616 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B3617945 : Blo 1068616 3617945 := bstep (se 2 (by rfl) ⟨1356729, by rfl⟩ : syracuseStep 3617945 = 2713459) B2713459
theorem B1357231 : Blo 1068616 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B2405897 : Blo 1068616 2405897 := bstep (se 2 (by rfl) ⟨902211, by rfl⟩ : syracuseStep 2405897 = 1804423) B1804423
theorem B5420843 : Blo 1068616 5420843 := bstep (se 1 (by rfl) ⟨4065632, by rfl⟩ : syracuseStep 5420843 = 8131265) B8131265
theorem B2406239 : Blo 1068616 2406239 := bstep (se 1 (by rfl) ⟨1804679, by rfl⟩ : syracuseStep 2406239 = 3609359) B3609359
theorem B1718111 : Blo 1068616 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B2406419 : Blo 1068616 2406419 := bstep (se 1 (by rfl) ⟨1804814, by rfl⟩ : syracuseStep 2406419 = 3609629) B3609629
theorem B3619133 : Blo 1068616 3619133 := bstep (se 3 (by rfl) ⟨678587, by rfl⟩ : syracuseStep 3619133 = 1357175) B1357175
theorem B16464215 : Blo 1068616 16464215 := bstep (se 1 (by rfl) ⟨12348161, by rfl⟩ : syracuseStep 16464215 = 24696323) B24696323
theorem B2406761 : Blo 1068616 2406761 := bstep (se 2 (by rfl) ⟨902535, by rfl⟩ : syracuseStep 2406761 = 1805071) B1805071
theorem B1522027 : Blo 1068616 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1522255 : Blo 1068616 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B2407355 : Blo 1068616 2407355 := bstep (se 1 (by rfl) ⟨1805516, by rfl⟩ : syracuseStep 2407355 = 3611033) B3611033
theorem B2407481 : Blo 1068616 2407481 := bstep (se 2 (by rfl) ⟨902805, by rfl⟩ : syracuseStep 2407481 = 1805611) B1805611
theorem B3619997 : Blo 1068616 3619997 := bstep (se 3 (by rfl) ⟨678749, by rfl⟩ : syracuseStep 3619997 = 1357499) B1357499
theorem B4570283 : Blo 1068616 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B2407823 : Blo 1068616 2407823 := bstep (se 1 (by rfl) ⟨1805867, by rfl⟩ : syracuseStep 2407823 = 3611735) B3611735
theorem B2408147 : Blo 1068616 2408147 := bstep (se 1 (by rfl) ⟨1806110, by rfl⟩ : syracuseStep 2408147 = 3612221) B3612221
theorem B5423111 : Blo 1068616 5423111 := bstep (se 1 (by rfl) ⟨4067333, by rfl⟩ : syracuseStep 5423111 = 8134667) B8134667
theorem B6864911 : Blo 1068616 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B8142929 : Blo 1068616 8142929 := bstep (se 2 (by rfl) ⟨3053598, by rfl⟩ : syracuseStep 8142929 = 6107197) B6107197
theorem B11583755 : Blo 1068616 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B3424637 : Blo 1068616 3424637 := bstep (se 3 (by rfl) ⟨642119, by rfl⟩ : syracuseStep 3424637 = 1284239) B1284239
theorem B5423597 : Blo 1068616 5423597 := bstep (se 3 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 5423597 = 2033849) B2033849
theorem B2409083 : Blo 1068616 2409083 := bstep (se 1 (by rfl) ⟨1806812, by rfl⟩ : syracuseStep 2409083 = 3613625) B3613625
theorem B2409209 : Blo 1068616 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B17384395 : Blo 1068616 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B7717889 : Blo 1068616 7717889 := bstep (se 2 (by rfl) ⟨2894208, by rfl⟩ : syracuseStep 7717889 = 5788417) B5788417
theorem B2409479 : Blo 1068616 2409479 := bstep (se 1 (by rfl) ⟨1807109, by rfl⟩ : syracuseStep 2409479 = 3614219) B3614219
theorem B8930371 : Blo 1068616 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B2409551 : Blo 1068616 2409551 := bstep (se 1 (by rfl) ⟨1807163, by rfl⟩ : syracuseStep 2409551 = 3614327) B3614327
theorem B5424407 : Blo 1068616 5424407 := bstep (se 1 (by rfl) ⟨4068305, by rfl⟩ : syracuseStep 5424407 = 8136611) B8136611
theorem B2409947 : Blo 1068616 2409947 := bstep (se 1 (by rfl) ⟨1807460, by rfl⟩ : syracuseStep 2409947 = 3614921) B3614921
theorem B2705035 : Blo 1068616 2705035 := bstep (se 1 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 2705035 = 4057553) B4057553
theorem B3852127 : Blo 1068616 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B2410415 : Blo 1068616 2410415 := bstep (se 1 (by rfl) ⟨1807811, by rfl⟩ : syracuseStep 2410415 = 3615623) B3615623
theorem B2705339 : Blo 1068616 2705339 := bstep (se 1 (by rfl) ⟨2029004, by rfl⟩ : syracuseStep 2705339 = 4058009) B4058009
theorem B2410667 : Blo 1068616 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B3426779 : Blo 1068616 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B9259705 : Blo 1068616 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B2706119 : Blo 1068616 2706119 := bstep (se 1 (by rfl) ⟨2029589, by rfl⟩ : syracuseStep 2706119 = 4059179) B4059179
theorem B2411207 : Blo 1068616 2411207 := bstep (se 1 (by rfl) ⟨1808405, by rfl⟩ : syracuseStep 2411207 = 3616811) B3616811
theorem B4573907 : Blo 1068616 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B2706169 : Blo 1068616 2706169 := bstep (se 2 (by rfl) ⟨1014813, by rfl⟩ : syracuseStep 2706169 = 2029627) B2029627
theorem B1526521 : Blo 1068616 1526521 := bstep (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) B1144891
theorem B5426027 : Blo 1068616 5426027 := bstep (se 1 (by rfl) ⟨4069520, by rfl⟩ : syracuseStep 5426027 = 8139041) B8139041
theorem B2706817 : Blo 1068616 2706817 := bstep (se 2 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 2706817 = 2030113) B2030113
theorem B20598259 : Blo 1068616 20598259 := bstep (se 1 (by rfl) ⟨15448694, by rfl⟩ : syracuseStep 20598259 = 30897389) B30897389
theorem B5426675 : Blo 1068616 5426675 := bstep (se 1 (by rfl) ⟨4070006, by rfl⟩ : syracuseStep 5426675 = 8140013) B8140013
theorem B2575859 : Blo 1068616 2575859 := bstep (se 1 (by rfl) ⟨1931894, by rfl⟩ : syracuseStep 2575859 = 3863789) B3863789
theorem B2412071 : Blo 1068616 2412071 := bstep (se 1 (by rfl) ⟨1809053, by rfl⟩ : syracuseStep 2412071 = 3618107) B3618107
theorem B1068623 : Blo 1068616 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1068639 : Blo 1068616 1068639 := bstep (se 1 (by rfl) ⟨801479, by rfl⟩ : syracuseStep 1068639 = 1602959) B1602959
theorem B1068667 : Blo 1068616 1068667 := bstep (se 1 (by rfl) ⟨801500, by rfl⟩ : syracuseStep 1068667 = 1603001) B1603001
theorem B1068719 : Blo 1068616 1068719 := bstep (se 1 (by rfl) ⟨801539, by rfl⟩ : syracuseStep 1068719 = 1603079) B1603079
theorem B1068743 : Blo 1068616 1068743 := bstep (se 1 (by rfl) ⟨801557, by rfl⟩ : syracuseStep 1068743 = 1603115) B1603115
theorem B1068763 : Blo 1068616 1068763 := bstep (se 1 (by rfl) ⟨801572, by rfl⟩ : syracuseStep 1068763 = 1603145) B1603145
theorem B1068839 : Blo 1068616 1068839 := bstep (se 1 (by rfl) ⟨801629, by rfl⟩ : syracuseStep 1068839 = 1603259) B1603259
theorem B1068879 : Blo 1068616 1068879 := bstep (se 1 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 1068879 = 1603319) B1603319
theorem B1068895 : Blo 1068616 1068895 := bstep (se 1 (by rfl) ⟨801671, by rfl⟩ : syracuseStep 1068895 = 1603343) B1603343
theorem B2412395 : Blo 1068616 2412395 := bstep (se 1 (by rfl) ⟨1809296, by rfl⟩ : syracuseStep 2412395 = 3618593) B3618593
theorem B55529333 : Blo 1068616 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B1068923 : Blo 1068616 1068923 := bstep (se 1 (by rfl) ⟨801692, by rfl⟩ : syracuseStep 1068923 = 1603385) B1603385
theorem B2412449 : Blo 1068616 2412449 := bstep (se 2 (by rfl) ⟨904668, by rfl⟩ : syracuseStep 2412449 = 1809337) B1809337
theorem B1068975 : Blo 1068616 1068975 := bstep (se 1 (by rfl) ⟨801731, by rfl⟩ : syracuseStep 1068975 = 1603463) B1603463
theorem B1068999 : Blo 1068616 1068999 := bstep (se 1 (by rfl) ⟨801749, by rfl⟩ : syracuseStep 1068999 = 1603499) B1603499
theorem B1069019 : Blo 1068616 1069019 := bstep (se 1 (by rfl) ⟨801764, by rfl⟩ : syracuseStep 1069019 = 1603529) B1603529
theorem B1069095 : Blo 1068616 1069095 := bstep (se 1 (by rfl) ⟨801821, by rfl⟩ : syracuseStep 1069095 = 1603643) B1603643
theorem B1069135 : Blo 1068616 1069135 := bstep (se 1 (by rfl) ⟨801851, by rfl⟩ : syracuseStep 1069135 = 1603703) B1603703
theorem B1069151 : Blo 1068616 1069151 := bstep (se 1 (by rfl) ⟨801863, by rfl⟩ : syracuseStep 1069151 = 1603727) B1603727
theorem B1069179 : Blo 1068616 1069179 := bstep (se 1 (by rfl) ⟨801884, by rfl⟩ : syracuseStep 1069179 = 1603769) B1603769
theorem B2707627 : Blo 1068616 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B1069231 : Blo 1068616 1069231 := bstep (se 1 (by rfl) ⟨801923, by rfl⟩ : syracuseStep 1069231 = 1603847) B1603847
theorem B1069255 : Blo 1068616 1069255 := bstep (se 1 (by rfl) ⟨801941, by rfl⟩ : syracuseStep 1069255 = 1603883) B1603883
theorem B1954003 : Blo 1068616 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B1069275 : Blo 1068616 1069275 := bstep (se 1 (by rfl) ⟨801956, by rfl⟩ : syracuseStep 1069275 = 1603913) B1603913
theorem B2412791 : Blo 1068616 2412791 := bstep (se 1 (by rfl) ⟨1809593, by rfl⟩ : syracuseStep 2412791 = 3619187) B3619187
theorem B1069351 : Blo 1068616 1069351 := bstep (se 1 (by rfl) ⟨802013, by rfl⟩ : syracuseStep 1069351 = 1604027) B1604027
theorem B1069391 : Blo 1068616 1069391 := bstep (se 1 (by rfl) ⟨802043, by rfl⟩ : syracuseStep 1069391 = 1604087) B1604087
theorem B1069407 : Blo 1068616 1069407 := bstep (se 1 (by rfl) ⟨802055, by rfl⟩ : syracuseStep 1069407 = 1604111) B1604111
theorem B1069435 : Blo 1068616 1069435 := bstep (se 1 (by rfl) ⟨802076, by rfl⟩ : syracuseStep 1069435 = 1604153) B1604153
theorem B1069487 : Blo 1068616 1069487 := bstep (se 1 (by rfl) ⟨802115, by rfl⟩ : syracuseStep 1069487 = 1604231) B1604231
theorem B1069511 : Blo 1068616 1069511 := bstep (se 1 (by rfl) ⟨802133, by rfl⟩ : syracuseStep 1069511 = 1604267) B1604267
theorem B1069531 : Blo 1068616 1069531 := bstep (se 1 (by rfl) ⟨802148, by rfl⟩ : syracuseStep 1069531 = 1604297) B1604297
theorem B2707931 : Blo 1068616 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B4117025 : Blo 1068616 4117025 := bstep (se 2 (by rfl) ⟨1543884, by rfl⟩ : syracuseStep 4117025 = 3087769) B3087769
theorem B1069607 : Blo 1068616 1069607 := bstep (se 1 (by rfl) ⟨802205, by rfl⟩ : syracuseStep 1069607 = 1604411) B1604411
theorem B1069647 : Blo 1068616 1069647 := bstep (se 1 (by rfl) ⟨802235, by rfl⟩ : syracuseStep 1069647 = 1604471) B1604471
theorem B1069663 : Blo 1068616 1069663 := bstep (se 1 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 1069663 = 1604495) B1604495
theorem B1069691 : Blo 1068616 1069691 := bstep (se 1 (by rfl) ⟨802268, by rfl⟩ : syracuseStep 1069691 = 1604537) B1604537
theorem B1069743 : Blo 1068616 1069743 := bstep (se 1 (by rfl) ⟨802307, by rfl⟩ : syracuseStep 1069743 = 1604615) B1604615
theorem B1069767 : Blo 1068616 1069767 := bstep (se 1 (by rfl) ⟨802325, by rfl⟩ : syracuseStep 1069767 = 1604651) B1604651
theorem B1069787 : Blo 1068616 1069787 := bstep (se 1 (by rfl) ⟨802340, by rfl⟩ : syracuseStep 1069787 = 1604681) B1604681
theorem B5427971 : Blo 1068616 5427971 := bstep (se 1 (by rfl) ⟨4070978, by rfl⟩ : syracuseStep 5427971 = 8141957) B8141957
theorem B1069863 : Blo 1068616 1069863 := bstep (se 1 (by rfl) ⟨802397, by rfl⟩ : syracuseStep 1069863 = 1604795) B1604795
theorem B14635849 : Blo 1068616 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B5493577 : Blo 1068616 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B2413385 : Blo 1068616 2413385 := bstep (se 2 (by rfl) ⟨905019, by rfl⟩ : syracuseStep 2413385 = 1810039) B1810039
theorem B1069903 : Blo 1068616 1069903 := bstep (se 1 (by rfl) ⟨802427, by rfl⟩ : syracuseStep 1069903 = 1604855) B1604855
theorem B1069919 : Blo 1068616 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B1069947 : Blo 1068616 1069947 := bstep (se 1 (by rfl) ⟨802460, by rfl⟩ : syracuseStep 1069947 = 1604921) B1604921
theorem B1069999 : Blo 1068616 1069999 := bstep (se 1 (by rfl) ⟨802499, by rfl⟩ : syracuseStep 1069999 = 1604999) B1604999
theorem B1070023 : Blo 1068616 1070023 := bstep (se 1 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 1070023 = 1605035) B1605035
theorem B1070043 : Blo 1068616 1070043 := bstep (se 1 (by rfl) ⟨802532, by rfl⟩ : syracuseStep 1070043 = 1605065) B1605065
theorem B26432477 : Blo 1068616 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B6870035 : Blo 1068616 6870035 := bstep (se 1 (by rfl) ⟨5152526, by rfl⟩ : syracuseStep 6870035 = 10305053) B10305053
theorem B1070119 : Blo 1068616 1070119 := bstep (se 1 (by rfl) ⟨802589, by rfl⟩ : syracuseStep 1070119 = 1605179) B1605179
theorem B7328819 : Blo 1068616 7328819 := bstep (se 1 (by rfl) ⟨5496614, by rfl⟩ : syracuseStep 7328819 = 10993229) B10993229
theorem B1070159 : Blo 1068616 1070159 := bstep (se 1 (by rfl) ⟨802619, by rfl⟩ : syracuseStep 1070159 = 1605239) B1605239
theorem B4346959 : Blo 1068616 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B1070175 : Blo 1068616 1070175 := bstep (se 1 (by rfl) ⟨802631, by rfl⟩ : syracuseStep 1070175 = 1605263) B1605263
theorem B1070203 : Blo 1068616 1070203 := bstep (se 1 (by rfl) ⟨802652, by rfl⟩ : syracuseStep 1070203 = 1605305) B1605305
theorem B6870187 : Blo 1068616 6870187 := bstep (se 1 (by rfl) ⟨5152640, by rfl⟩ : syracuseStep 6870187 = 10305281) B10305281
theorem B1070255 : Blo 1068616 1070255 := bstep (se 1 (by rfl) ⟨802691, by rfl⟩ : syracuseStep 1070255 = 1605383) B1605383
theorem B1070279 : Blo 1068616 1070279 := bstep (se 1 (by rfl) ⟨802709, by rfl⟩ : syracuseStep 1070279 = 1605419) B1605419
theorem B1070299 : Blo 1068616 1070299 := bstep (se 1 (by rfl) ⟨802724, by rfl⟩ : syracuseStep 1070299 = 1605449) B1605449
theorem B1070375 : Blo 1068616 1070375 := bstep (se 1 (by rfl) ⟨802781, by rfl⟩ : syracuseStep 1070375 = 1605563) B1605563
theorem B1070415 : Blo 1068616 1070415 := bstep (se 1 (by rfl) ⟨802811, by rfl⟩ : syracuseStep 1070415 = 1605623) B1605623
theorem B1070431 : Blo 1068616 1070431 := bstep (se 1 (by rfl) ⟨802823, by rfl⟩ : syracuseStep 1070431 = 1605647) B1605647
theorem B1070459 : Blo 1068616 1070459 := bstep (se 1 (by rfl) ⟨802844, by rfl⟩ : syracuseStep 1070459 = 1605689) B1605689
theorem B1070511 : Blo 1068616 1070511 := bstep (se 1 (by rfl) ⟨802883, by rfl⟩ : syracuseStep 1070511 = 1605767) B1605767
theorem B1070535 : Blo 1068616 1070535 := bstep (se 1 (by rfl) ⟨802901, by rfl⟩ : syracuseStep 1070535 = 1605803) B1605803
theorem B8345051 : Blo 1068616 8345051 := bstep (se 1 (by rfl) ⟨6258788, by rfl⟩ : syracuseStep 8345051 = 12517577) B12517577
theorem B1070555 : Blo 1068616 1070555 := bstep (se 1 (by rfl) ⟨802916, by rfl⟩ : syracuseStep 1070555 = 1605833) B1605833
theorem B1070631 : Blo 1068616 1070631 := bstep (se 1 (by rfl) ⟨802973, by rfl⟩ : syracuseStep 1070631 = 1605947) B1605947
theorem B1070671 : Blo 1068616 1070671 := bstep (se 1 (by rfl) ⟨803003, by rfl⟩ : syracuseStep 1070671 = 1606007) B1606007
theorem B1070687 : Blo 1068616 1070687 := bstep (se 1 (by rfl) ⟨803015, by rfl⟩ : syracuseStep 1070687 = 1606031) B1606031
theorem B1070715 : Blo 1068616 1070715 := bstep (se 1 (by rfl) ⟨803036, by rfl⟩ : syracuseStep 1070715 = 1606073) B1606073
theorem B1070767 : Blo 1068616 1070767 := bstep (se 1 (by rfl) ⟨803075, by rfl⟩ : syracuseStep 1070767 = 1606151) B1606151
theorem B6510269 : Blo 1068616 6510269 := bstep (se 3 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 6510269 = 2441351) B2441351
theorem B1070791 : Blo 1068616 1070791 := bstep (se 1 (by rfl) ⟨803093, by rfl⟩ : syracuseStep 1070791 = 1606187) B1606187
theorem B1070811 : Blo 1068616 1070811 := bstep (se 1 (by rfl) ⟨803108, by rfl⟩ : syracuseStep 1070811 = 1606217) B1606217
theorem B1070887 : Blo 1068616 1070887 := bstep (se 1 (by rfl) ⟨803165, by rfl⟩ : syracuseStep 1070887 = 1606331) B1606331
theorem B1070927 : Blo 1068616 1070927 := bstep (se 1 (by rfl) ⟨803195, by rfl⟩ : syracuseStep 1070927 = 1606391) B1606391
theorem B1070943 : Blo 1068616 1070943 := bstep (se 1 (by rfl) ⟨803207, by rfl⟩ : syracuseStep 1070943 = 1606415) B1606415
theorem B1070971 : Blo 1068616 1070971 := bstep (se 1 (by rfl) ⟨803228, by rfl⟩ : syracuseStep 1070971 = 1606457) B1606457
theorem B2709409 : Blo 1068616 2709409 := bstep (se 2 (by rfl) ⟨1016028, by rfl⟩ : syracuseStep 2709409 = 2032057) B2032057
theorem B1071023 : Blo 1068616 1071023 := bstep (se 1 (by rfl) ⟨803267, by rfl⟩ : syracuseStep 1071023 = 1606535) B1606535
theorem B1071047 : Blo 1068616 1071047 := bstep (se 1 (by rfl) ⟨803285, by rfl⟩ : syracuseStep 1071047 = 1606571) B1606571
theorem B15849425 : Blo 1068616 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B1071067 : Blo 1068616 1071067 := bstep (se 1 (by rfl) ⟨803300, by rfl⟩ : syracuseStep 1071067 = 1606601) B1606601
theorem B1202215 : Blo 1068616 1202215 := bstep (se 1 (by rfl) ⟨901661, by rfl⟩ : syracuseStep 1202215 = 1803323) B1803323
theorem B1071143 : Blo 1068616 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B1071183 : Blo 1068616 1071183 := bstep (se 1 (by rfl) ⟨803387, by rfl⟩ : syracuseStep 1071183 = 1606775) B1606775
theorem B1071199 : Blo 1068616 1071199 := bstep (se 1 (by rfl) ⟨803399, by rfl⟩ : syracuseStep 1071199 = 1606799) B1606799
theorem B1071227 : Blo 1068616 1071227 := bstep (se 1 (by rfl) ⟨803420, by rfl⟩ : syracuseStep 1071227 = 1606841) B1606841
theorem B1071279 : Blo 1068616 1071279 := bstep (se 1 (by rfl) ⟨803459, by rfl⟩ : syracuseStep 1071279 = 1606919) B1606919
theorem B1071303 : Blo 1068616 1071303 := bstep (se 1 (by rfl) ⟨803477, by rfl⟩ : syracuseStep 1071303 = 1606955) B1606955
theorem B1071323 : Blo 1068616 1071323 := bstep (se 1 (by rfl) ⟨803492, by rfl⟩ : syracuseStep 1071323 = 1606985) B1606985
theorem B1071399 : Blo 1068616 1071399 := bstep (se 1 (by rfl) ⟨803549, by rfl⟩ : syracuseStep 1071399 = 1607099) B1607099
theorem B4577597 : Blo 1068616 4577597 := bstep (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) B1716599
theorem B1071439 : Blo 1068616 1071439 := bstep (se 1 (by rfl) ⟨803579, by rfl⟩ : syracuseStep 1071439 = 1607159) B1607159
theorem B5429591 : Blo 1068616 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B1071455 : Blo 1068616 1071455 := bstep (se 1 (by rfl) ⟨803591, by rfl⟩ : syracuseStep 1071455 = 1607183) B1607183
theorem B1071483 : Blo 1068616 1071483 := bstep (se 1 (by rfl) ⟨803612, by rfl⟩ : syracuseStep 1071483 = 1607225) B1607225
theorem B1071535 : Blo 1068616 1071535 := bstep (se 1 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 1071535 = 1607303) B1607303
theorem B1071559 : Blo 1068616 1071559 := bstep (se 1 (by rfl) ⟨803669, by rfl⟩ : syracuseStep 1071559 = 1607339) B1607339
theorem B1071579 : Blo 1068616 1071579 := bstep (se 1 (by rfl) ⟨803684, by rfl⟩ : syracuseStep 1071579 = 1607369) B1607369
theorem B3660275 : Blo 1068616 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B1071655 : Blo 1068616 1071655 := bstep (se 1 (by rfl) ⟨803741, by rfl⟩ : syracuseStep 1071655 = 1607483) B1607483
theorem B1071695 : Blo 1068616 1071695 := bstep (se 1 (by rfl) ⟨803771, by rfl⟩ : syracuseStep 1071695 = 1607543) B1607543
theorem B1071711 : Blo 1068616 1071711 := bstep (se 1 (by rfl) ⟨803783, by rfl⟩ : syracuseStep 1071711 = 1607567) B1607567
theorem B1071739 : Blo 1068616 1071739 := bstep (se 1 (by rfl) ⟨803804, by rfl⟩ : syracuseStep 1071739 = 1607609) B1607609
theorem B1071791 : Blo 1068616 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B1071815 : Blo 1068616 1071815 := bstep (se 1 (by rfl) ⟨803861, by rfl⟩ : syracuseStep 1071815 = 1607723) B1607723
theorem B3431123 : Blo 1068616 3431123 := bstep (se 1 (by rfl) ⟨2573342, by rfl⟩ : syracuseStep 3431123 = 5146685) B5146685
theorem B1071835 : Blo 1068616 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B1071911 : Blo 1068616 1071911 := bstep (se 1 (by rfl) ⟨803933, by rfl⟩ : syracuseStep 1071911 = 1607867) B1607867
theorem B1071951 : Blo 1068616 1071951 := bstep (se 1 (by rfl) ⟨803963, by rfl⟩ : syracuseStep 1071951 = 1607927) B1607927
theorem B1071967 : Blo 1068616 1071967 := bstep (se 1 (by rfl) ⟨803975, by rfl⟩ : syracuseStep 1071967 = 1607951) B1607951
theorem B1071995 : Blo 1068616 1071995 := bstep (se 1 (by rfl) ⟨803996, by rfl⟩ : syracuseStep 1071995 = 1607993) B1607993
theorem B1072047 : Blo 1068616 1072047 := bstep (se 1 (by rfl) ⟨804035, by rfl⟩ : syracuseStep 1072047 = 1608071) B1608071
theorem B1072071 : Blo 1068616 1072071 := bstep (se 1 (by rfl) ⟨804053, by rfl⟩ : syracuseStep 1072071 = 1608107) B1608107
theorem B1072091 : Blo 1068616 1072091 := bstep (se 1 (by rfl) ⟨804068, by rfl⟩ : syracuseStep 1072091 = 1608137) B1608137
theorem B1072167 : Blo 1068616 1072167 := bstep (se 1 (by rfl) ⟨804125, by rfl⟩ : syracuseStep 1072167 = 1608251) B1608251
theorem B4578383 : Blo 1068616 4578383 := bstep (se 1 (by rfl) ⟨3433787, by rfl⟩ : syracuseStep 4578383 = 6867575) B6867575
theorem B1072207 : Blo 1068616 1072207 := bstep (se 1 (by rfl) ⟨804155, by rfl⟩ : syracuseStep 1072207 = 1608311) B1608311
theorem B1072223 : Blo 1068616 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B1072251 : Blo 1068616 1072251 := bstep (se 1 (by rfl) ⟨804188, by rfl⟩ : syracuseStep 1072251 = 1608377) B1608377
theorem B3857561 : Blo 1068616 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B1072303 : Blo 1068616 1072303 := bstep (se 1 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 1072303 = 1608455) B1608455
theorem B5135555 : Blo 1068616 5135555 := bstep (se 1 (by rfl) ⟨3851666, by rfl⟩ : syracuseStep 5135555 = 7703333) B7703333
theorem B1072327 : Blo 1068616 1072327 := bstep (se 1 (by rfl) ⟨804245, by rfl⟩ : syracuseStep 1072327 = 1608491) B1608491
theorem B1072347 : Blo 1068616 1072347 := bstep (se 1 (by rfl) ⟨804260, by rfl⟩ : syracuseStep 1072347 = 1608521) B1608521
theorem B1072423 : Blo 1068616 1072423 := bstep (se 1 (by rfl) ⟨804317, by rfl⟩ : syracuseStep 1072423 = 1608635) B1608635
theorem B1072463 : Blo 1068616 1072463 := bstep (se 1 (by rfl) ⟨804347, by rfl⟩ : syracuseStep 1072463 = 1608695) B1608695
theorem B1072479 : Blo 1068616 1072479 := bstep (se 1 (by rfl) ⟨804359, by rfl⟩ : syracuseStep 1072479 = 1608719) B1608719
theorem B1072507 : Blo 1068616 1072507 := bstep (se 1 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 1072507 = 1608761) B1608761
theorem B1072559 : Blo 1068616 1072559 := bstep (se 1 (by rfl) ⟨804419, by rfl⟩ : syracuseStep 1072559 = 1608839) B1608839
theorem B1072583 : Blo 1068616 1072583 := bstep (se 1 (by rfl) ⟨804437, by rfl⟩ : syracuseStep 1072583 = 1608875) B1608875
theorem B1072603 : Blo 1068616 1072603 := bstep (se 1 (by rfl) ⟨804452, by rfl⟩ : syracuseStep 1072603 = 1608905) B1608905
theorem B1695239 : Blo 1068616 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B1203835 : Blo 1068616 1203835 := bstep (se 1 (by rfl) ⟨902876, by rfl⟩ : syracuseStep 1203835 = 1805753) B1805753
theorem B3432071 : Blo 1068616 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B2678483 : Blo 1068616 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B4579031 : Blo 1068616 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B1204303 : Blo 1068616 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B2711951 : Blo 1068616 2711951 := bstep (se 1 (by rfl) ⟨2033963, by rfl⟩ : syracuseStep 2711951 = 4067927) B4067927
theorem B1204699 : Blo 1068616 1204699 := bstep (se 1 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 1204699 = 1807049) B1807049
theorem B2744819 : Blo 1068616 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2712275 : Blo 1068616 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B2056951 : Blo 1068616 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B1205167 : Blo 1068616 1205167 := bstep (se 1 (by rfl) ⟨903875, by rfl⟩ : syracuseStep 1205167 = 1807751) B1807751
theorem B3433403 : Blo 1068616 3433403 := bstep (se 1 (by rfl) ⟨2575052, by rfl⟩ : syracuseStep 3433403 = 5150105) B5150105
theorem B10970315 : Blo 1068616 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B1205599 : Blo 1068616 1205599 := bstep (se 1 (by rfl) ⟨904199, by rfl⟩ : syracuseStep 1205599 = 1808399) B1808399
theorem B6088061 : Blo 1068616 6088061 := bstep (se 3 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 6088061 = 2283023) B2283023
theorem B3433853 : Blo 1068616 3433853 := bstep (se 3 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 3433853 = 1287695) B1287695
theorem B1205959 : Blo 1068616 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B2713439 : Blo 1068616 2713439 := bstep (se 1 (by rfl) ⟨2035079, by rfl⟩ : syracuseStep 2713439 = 4070159) B4070159
theorem B3860561 : Blo 1068616 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B62580869 : Blo 1068616 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B41216201 : Blo 1068616 41216201 := bstep (se 2 (by rfl) ⟨15456075, by rfl⟩ : syracuseStep 41216201 = 30912151) B30912151
theorem B18278945 : Blo 1068616 18278945 := bstep (se 2 (by rfl) ⟨6854604, by rfl⟩ : syracuseStep 18278945 = 13709209) B13709209
theorem B4057735 : Blo 1068616 4057735 := bstep (se 1 (by rfl) ⟨3043301, by rfl⟩ : syracuseStep 4057735 = 6086603) B6086603
theorem B3435223 : Blo 1068616 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B2714543 : Blo 1068616 2714543 := bstep (se 1 (by rfl) ⟨2035907, by rfl⟩ : syracuseStep 2714543 = 4071815) B4071815
theorem B4058039 : Blo 1068616 4058039 := bstep (se 1 (by rfl) ⟨3043529, by rfl⟩ : syracuseStep 4058039 = 6087059) B6087059
theorem B6089701 : Blo 1068616 6089701 := bstep (se 4 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 6089701 = 1141819) B1141819
theorem B6089975 : Blo 1068616 6089975 := bstep (se 1 (by rfl) ⟨4567481, by rfl⟩ : syracuseStep 6089975 = 9134963) B9134963
theorem B13036889 : Blo 1068616 13036889 := bstep (se 2 (by rfl) ⟨4888833, by rfl⟩ : syracuseStep 13036889 = 9777667) B9777667
theorem B1142191 : Blo 1068616 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B1928623 : Blo 1068616 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B6090227 : Blo 1068616 6090227 := bstep (se 1 (by rfl) ⟨4567670, by rfl⟩ : syracuseStep 6090227 = 9135341) B9135341
theorem B10284677 : Blo 1068616 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B9760445 : Blo 1068616 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B4059193 : Blo 1068616 4059193 := bstep (se 2 (by rfl) ⟨1522197, by rfl⟩ : syracuseStep 4059193 = 3044395) B3044395
theorem B2289721 : Blo 1068616 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B11595953 : Blo 1068616 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B10973515 : Blo 1068616 10973515 := bstep (se 1 (by rfl) ⟨8230136, by rfl⟩ : syracuseStep 10973515 = 16460273) B16460273
theorem B4059497 : Blo 1068616 4059497 := bstep (se 2 (by rfl) ⟨1522311, by rfl⟩ : syracuseStep 4059497 = 3044623) B3044623
theorem B1831547 : Blo 1068616 1831547 := bstep (se 1 (by rfl) ⟨1373660, by rfl⟩ : syracuseStep 1831547 = 2747321) B2747321
theorem B18313937 : Blo 1068616 18313937 := bstep (se 2 (by rfl) ⟨6867726, by rfl⟩ : syracuseStep 18313937 = 13735453) B13735453
theorem B1930159 : Blo 1068616 1930159 := bstep (se 1 (by rfl) ⟨1447619, by rfl⟩ : syracuseStep 1930159 = 2895239) B2895239
theorem B1603151 : Blo 1068616 1603151 := bstep (se 1 (by rfl) ⟨1202363, by rfl⟩ : syracuseStep 1603151 = 2404727) B2404727
theorem B6092435 : Blo 1068616 6092435 := bstep (se 1 (by rfl) ⟨4569326, by rfl⟩ : syracuseStep 6092435 = 9138653) B9138653
theorem B1603271 : Blo 1068616 1603271 := bstep (se 1 (by rfl) ⟨1202453, by rfl⟩ : syracuseStep 1603271 = 2404907) B2404907
theorem B3045215 : Blo 1068616 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1603433 : Blo 1068616 1603433 := bstep (se 2 (by rfl) ⟨601287, by rfl⟩ : syracuseStep 1603433 = 1202575) B1202575
theorem B1603511 : Blo 1068616 1603511 := bstep (se 1 (by rfl) ⟨1202633, by rfl⟩ : syracuseStep 1603511 = 2405267) B2405267
theorem B1603547 : Blo 1068616 1603547 := bstep (se 1 (by rfl) ⟨1202660, by rfl⟩ : syracuseStep 1603547 = 2405321) B2405321
theorem B5142685 : Blo 1068616 5142685 := bstep (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) B1928507
theorem B6093143 : Blo 1068616 6093143 := bstep (se 1 (by rfl) ⟨4569857, by rfl⟩ : syracuseStep 6093143 = 9139715) B9139715
theorem B2029931 : Blo 1068616 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B1604015 : Blo 1068616 1604015 := bstep (se 1 (by rfl) ⟨1203011, by rfl⟩ : syracuseStep 1604015 = 2406023) B2406023
theorem B1604105 : Blo 1068616 1604105 := bstep (se 2 (by rfl) ⟨601539, by rfl⟩ : syracuseStep 1604105 = 1203079) B1203079
theorem B1604135 : Blo 1068616 1604135 := bstep (se 1 (by rfl) ⟨1203101, by rfl⟩ : syracuseStep 1604135 = 2406203) B2406203
theorem B2030159 : Blo 1068616 2030159 := bstep (se 1 (by rfl) ⟨1522619, by rfl⟩ : syracuseStep 2030159 = 3045239) B3045239
theorem B1604219 : Blo 1068616 1604219 := bstep (se 1 (by rfl) ⟨1203164, by rfl⟩ : syracuseStep 1604219 = 2406329) B2406329
theorem B1604345 : Blo 1068616 1604345 := bstep (se 2 (by rfl) ⟨601629, by rfl⟩ : syracuseStep 1604345 = 1203259) B1203259
theorem B1604447 : Blo 1068616 1604447 := bstep (se 1 (by rfl) ⟨1203335, by rfl⟩ : syracuseStep 1604447 = 2406671) B2406671
theorem B1604459 : Blo 1068616 1604459 := bstep (se 1 (by rfl) ⟨1203344, by rfl⟩ : syracuseStep 1604459 = 2406689) B2406689
theorem B3865519 : Blo 1068616 3865519 := bstep (se 1 (by rfl) ⟨2899139, by rfl⟩ : syracuseStep 3865519 = 5798279) B5798279
theorem B2030599 : Blo 1068616 2030599 := bstep (se 1 (by rfl) ⟨1522949, by rfl⟩ : syracuseStep 2030599 = 3045899) B3045899
theorem B1604687 : Blo 1068616 1604687 := bstep (se 1 (by rfl) ⟨1203515, by rfl⟩ : syracuseStep 1604687 = 2407031) B2407031
theorem B1604807 : Blo 1068616 1604807 := bstep (se 1 (by rfl) ⟨1203605, by rfl⟩ : syracuseStep 1604807 = 2407211) B2407211
theorem B1604969 : Blo 1068616 1604969 := bstep (se 2 (by rfl) ⟨601863, by rfl⟩ : syracuseStep 1604969 = 1203727) B1203727
theorem B1605047 : Blo 1068616 1605047 := bstep (se 1 (by rfl) ⟨1203785, by rfl⟩ : syracuseStep 1605047 = 2407571) B2407571
theorem B92470733 : Blo 1068616 92470733 := bstep (se 3 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 92470733 = 34676525) B34676525
theorem B1605083 : Blo 1068616 1605083 := bstep (se 1 (by rfl) ⟨1203812, by rfl⟩ : syracuseStep 1605083 = 2407625) B2407625
theorem B4947655 : Blo 1068616 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B31325957 : Blo 1068616 31325957 := bstep (se 4 (by rfl) ⟨2936808, by rfl⟩ : syracuseStep 31325957 = 5873617) B5873617
theorem B1605551 : Blo 1068616 1605551 := bstep (se 1 (by rfl) ⟨1204163, by rfl⟩ : syracuseStep 1605551 = 2408327) B2408327
theorem B1605737 : Blo 1068616 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B1606055 : Blo 1068616 1606055 := bstep (se 1 (by rfl) ⟨1204541, by rfl⟩ : syracuseStep 1606055 = 2409083) B2409083
theorem B9142753 : Blo 1068616 9142753 := bstep (se 2 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 9142753 = 6857065) B6857065
theorem B1606139 : Blo 1068616 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B1606265 : Blo 1068616 1606265 := bstep (se 2 (by rfl) ⟨602349, by rfl⟩ : syracuseStep 1606265 = 1204699) B1204699
theorem B1606319 : Blo 1068616 1606319 := bstep (se 1 (by rfl) ⟨1204739, by rfl⟩ : syracuseStep 1606319 = 2409479) B2409479
theorem B1606367 : Blo 1068616 1606367 := bstep (se 1 (by rfl) ⟨1204775, by rfl⟩ : syracuseStep 1606367 = 2409551) B2409551
theorem B1606631 : Blo 1068616 1606631 := bstep (se 1 (by rfl) ⟨1204973, by rfl⟩ : syracuseStep 1606631 = 2409947) B2409947
theorem B26051681 : Blo 1068616 26051681 := bstep (se 2 (by rfl) ⟨9769380, by rfl⟩ : syracuseStep 26051681 = 19538761) B19538761
theorem B1606889 : Blo 1068616 1606889 := bstep (se 2 (by rfl) ⟨602583, by rfl⟩ : syracuseStep 1606889 = 1205167) B1205167
theorem B1606943 : Blo 1068616 1606943 := bstep (se 1 (by rfl) ⟨1205207, by rfl⟩ : syracuseStep 1606943 = 2410415) B2410415
theorem B1803559 : Blo 1068616 1803559 := bstep (se 1 (by rfl) ⟨1352669, by rfl⟩ : syracuseStep 1803559 = 2705339) B2705339
theorem B10978733 : Blo 1068616 10978733 := bstep (se 3 (by rfl) ⟨2058512, by rfl⟩ : syracuseStep 10978733 = 4117025) B4117025
theorem B1607111 : Blo 1068616 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B1607465 : Blo 1068616 1607465 := bstep (se 2 (by rfl) ⟨602799, by rfl⟩ : syracuseStep 1607465 = 1205599) B1205599
theorem B1804079 : Blo 1068616 1804079 := bstep (se 1 (by rfl) ⟨1353059, by rfl⟩ : syracuseStep 1804079 = 2706119) B2706119
theorem B1607471 : Blo 1068616 1607471 := bstep (se 1 (by rfl) ⟨1205603, by rfl⟩ : syracuseStep 1607471 = 2411207) B2411207
theorem B3049271 : Blo 1068616 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B4392791 : Blo 1068616 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B3606713 : Blo 1068616 3606713 := bstep (se 2 (by rfl) ⟨1352517, by rfl⟩ : syracuseStep 3606713 = 2705035) B2705035
theorem B1607945 : Blo 1068616 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B1608047 : Blo 1068616 1608047 := bstep (se 1 (by rfl) ⟨1206035, by rfl⟩ : syracuseStep 1608047 = 2412071) B2412071
theorem B13044179 : Blo 1068616 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B3475963 : Blo 1068616 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B1608263 : Blo 1068616 1608263 := bstep (se 1 (by rfl) ⟨1206197, by rfl⟩ : syracuseStep 1608263 = 2412395) B2412395
theorem B1608299 : Blo 1068616 1608299 := bstep (se 1 (by rfl) ⟨1206224, by rfl⟩ : syracuseStep 1608299 = 2412449) B2412449
theorem B20581037 : Blo 1068616 20581037 := bstep (se 3 (by rfl) ⟨3858944, by rfl⟩ : syracuseStep 20581037 = 7717889) B7717889
theorem B3476143 : Blo 1068616 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B1608527 : Blo 1068616 1608527 := bstep (se 1 (by rfl) ⟨1206395, by rfl⟩ : syracuseStep 1608527 = 2412791) B2412791
theorem B1805287 : Blo 1068616 1805287 := bstep (se 1 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 1805287 = 2707931) B2707931
theorem B1445083 : Blo 1068616 1445083 := bstep (se 1 (by rfl) ⟨1083812, by rfl⟩ : syracuseStep 1445083 = 2167625) B2167625
theorem B1608923 : Blo 1068616 1608923 := bstep (se 1 (by rfl) ⟨1206692, by rfl⟩ : syracuseStep 1608923 = 2413385) B2413385
theorem B1445159 : Blo 1068616 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B4885879 : Blo 1068616 4885879 := bstep (se 1 (by rfl) ⟨3664409, by rfl⟩ : syracuseStep 4885879 = 7328819) B7328819
theorem B5410313 : Blo 1068616 5410313 := bstep (se 2 (by rfl) ⟨2028867, by rfl⟩ : syracuseStep 5410313 = 4057735) B4057735
theorem B3608225 : Blo 1068616 3608225 := bstep (se 2 (by rfl) ⟨1353084, by rfl⟩ : syracuseStep 3608225 = 2706169) B2706169
theorem B2035361 : Blo 1068616 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B3051731 : Blo 1068616 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B5640623 : Blo 1068616 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B4067759 : Blo 1068616 4067759 := bstep (se 1 (by rfl) ⟨3050819, by rfl⟩ : syracuseStep 4067759 = 6101639) B6101639
theorem B5214689 : Blo 1068616 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B3609089 : Blo 1068616 3609089 := bstep (se 2 (by rfl) ⟨1353408, by rfl⟩ : syracuseStep 3609089 = 2706817) B2706817
theorem B27464345 : Blo 1068616 27464345 := bstep (se 2 (by rfl) ⟨10299129, by rfl⟩ : syracuseStep 27464345 = 20598259) B20598259
theorem B3052255 : Blo 1068616 3052255 := bstep (se 1 (by rfl) ⟨2289191, by rfl⟩ : syracuseStep 3052255 = 4578383) B4578383
theorem B3609575 : Blo 1068616 3609575 := bstep (se 1 (by rfl) ⟨2707181, by rfl⟩ : syracuseStep 3609575 = 5414363) B5414363
theorem B3609899 : Blo 1068616 3609899 := bstep (se 1 (by rfl) ⟨2707424, by rfl⟩ : syracuseStep 3609899 = 5414849) B5414849
theorem B4068731 : Blo 1068616 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B5412257 : Blo 1068616 5412257 := bstep (se 2 (by rfl) ⟨2029596, by rfl⟩ : syracuseStep 5412257 = 4059193) B4059193
theorem B3052961 : Blo 1068616 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B3610169 : Blo 1068616 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B1807967 : Blo 1068616 1807967 := bstep (se 1 (by rfl) ⟨1355975, by rfl⟩ : syracuseStep 1807967 = 2711951) B2711951
theorem B1808183 : Blo 1068616 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B7313543 : Blo 1068616 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B1808959 : Blo 1068616 1808959 := bstep (se 1 (by rfl) ⟨1356719, by rfl⟩ : syracuseStep 1808959 = 2713439) B2713439
theorem B41720579 : Blo 1068616 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B3611411 : Blo 1068616 3611411 := bstep (se 1 (by rfl) ⟨2708558, by rfl⟩ : syracuseStep 3611411 = 5417117) B5417117
theorem B1809641 : Blo 1068616 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B1809695 : Blo 1068616 1809695 := bstep (se 1 (by rfl) ⟨1357271, by rfl⟩ : syracuseStep 1809695 = 2714543) B2714543
theorem B9149861 : Blo 1068616 9149861 := bstep (se 4 (by rfl) ⟨857799, by rfl⟩ : syracuseStep 9149861 = 1715599) B1715599
theorem B4070843 : Blo 1068616 4070843 := bstep (se 1 (by rfl) ⟨3053132, by rfl⟩ : syracuseStep 4070843 = 6106265) B6106265
theorem B8691259 : Blo 1068616 8691259 := bstep (se 1 (by rfl) ⟨6518444, by rfl⟩ : syracuseStep 8691259 = 13036889) B13036889
theorem B3612275 : Blo 1068616 3612275 := bstep (se 1 (by rfl) ⟨2709206, by rfl⟩ : syracuseStep 3612275 = 5418413) B5418413
theorem B6856451 : Blo 1068616 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B3612545 : Blo 1068616 3612545 := bstep (se 2 (by rfl) ⟨1354704, by rfl⟩ : syracuseStep 3612545 = 2709409) B2709409
theorem B6856913 : Blo 1068616 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B17375579 : Blo 1068616 17375579 := bstep (se 1 (by rfl) ⟨13031684, by rfl⟩ : syracuseStep 17375579 = 26063369) B26063369
theorem B1221031 : Blo 1068616 1221031 := bstep (se 1 (by rfl) ⟨915773, by rfl⟩ : syracuseStep 1221031 = 1831547) B1831547
theorem B3613355 : Blo 1068616 3613355 := bstep (se 1 (by rfl) ⟨2710016, by rfl⟩ : syracuseStep 3613355 = 5420033) B5420033
theorem B49357583 : Blo 1068616 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B3613895 : Blo 1068616 3613895 := bstep (se 1 (by rfl) ⟨2710421, by rfl⟩ : syracuseStep 3613895 = 5420843) B5420843
theorem B5154025 : Blo 1068616 5154025 := bstep (se 2 (by rfl) ⟨1932759, by rfl⟩ : syracuseStep 5154025 = 3865519) B3865519
theorem B6956441 : Blo 1068616 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B8136125 : Blo 1068616 8136125 := bstep (se 3 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 8136125 = 3051047) B3051047
theorem B1353287 : Blo 1068616 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B1353439 : Blo 1068616 1353439 := bstep (se 1 (by rfl) ⟨1015079, by rfl⟩ : syracuseStep 1353439 = 2030159) B2030159
theorem B6596873 : Blo 1068616 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B5777693 : Blo 1068616 5777693 := bstep (se 3 (by rfl) ⟨1083317, by rfl⟩ : syracuseStep 5777693 = 2166635) B2166635
theorem B61647155 : Blo 1068616 61647155 := bstep (se 1 (by rfl) ⟨46235366, by rfl⟩ : syracuseStep 61647155 = 92470733) B92470733
theorem B20883971 : Blo 1068616 20883971 := bstep (se 1 (by rfl) ⟨15662978, by rfl⟩ : syracuseStep 20883971 = 31325957) B31325957
theorem B3615407 : Blo 1068616 3615407 := bstep (se 1 (by rfl) ⟨2711555, by rfl⟩ : syracuseStep 3615407 = 5423111) B5423111
theorem B3615731 : Blo 1068616 3615731 := bstep (se 1 (by rfl) ⟨2711798, by rfl⟩ : syracuseStep 3615731 = 5423597) B5423597
theorem B14855183 : Blo 1068616 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B14658731 : Blo 1068616 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B5418251 : Blo 1068616 5418251 := bstep (se 1 (by rfl) ⟨4063688, by rfl⟩ : syracuseStep 5418251 = 8127377) B8127377
theorem B3616271 : Blo 1068616 3616271 := bstep (se 1 (by rfl) ⟨2712203, by rfl⟩ : syracuseStep 3616271 = 5424407) B5424407
theorem B3714655 : Blo 1068616 3714655 := bstep (se 1 (by rfl) ⟨2785991, by rfl⟩ : syracuseStep 3714655 = 5571983) B5571983
theorem B23179193 : Blo 1068616 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B11579345 : Blo 1068616 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B11907161 : Blo 1068616 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B2404457 : Blo 1068616 2404457 := bstep (se 2 (by rfl) ⟨901671, by rfl⟩ : syracuseStep 2404457 = 1803343) B1803343
theorem B3617351 : Blo 1068616 3617351 := bstep (se 1 (by rfl) ⟨2713013, by rfl⟩ : syracuseStep 3617351 = 5426027) B5426027
theorem B2404943 : Blo 1068616 2404943 := bstep (se 1 (by rfl) ⟨1803707, by rfl⟩ : syracuseStep 2404943 = 3607415) B3607415
theorem B2405087 : Blo 1068616 2405087 := bstep (se 1 (by rfl) ⟨1803815, by rfl⟩ : syracuseStep 2405087 = 3607631) B3607631
theorem B5419871 : Blo 1068616 5419871 := bstep (se 1 (by rfl) ⟨4064903, by rfl⟩ : syracuseStep 5419871 = 8129807) B8129807
theorem B2405339 : Blo 1068616 2405339 := bstep (se 1 (by rfl) ⟨1804004, by rfl⟩ : syracuseStep 2405339 = 3608009) B3608009
theorem B3617783 : Blo 1068616 3617783 := bstep (se 1 (by rfl) ⟨2713337, by rfl⟩ : syracuseStep 3617783 = 5426675) B5426675
theorem B20558893 : Blo 1068616 20558893 := bstep (se 3 (by rfl) ⟨3854792, by rfl⟩ : syracuseStep 20558893 = 7709585) B7709585
theorem B2405519 : Blo 1068616 2405519 := bstep (se 1 (by rfl) ⟨1804139, by rfl⟩ : syracuseStep 2405519 = 3608279) B3608279
theorem B2405609 : Blo 1068616 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B2405663 : Blo 1068616 2405663 := bstep (se 1 (by rfl) ⟨1804247, by rfl⟩ : syracuseStep 2405663 = 3608495) B3608495
theorem B3257639 : Blo 1068616 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B18789833 : Blo 1068616 18789833 := bstep (se 2 (by rfl) ⟨7046187, by rfl⟩ : syracuseStep 18789833 = 14092375) B14092375
theorem B2406185 : Blo 1068616 2406185 := bstep (se 2 (by rfl) ⟨902319, by rfl⟩ : syracuseStep 2406185 = 1804639) B1804639
theorem B3618647 : Blo 1068616 3618647 := bstep (se 1 (by rfl) ⟨2713985, by rfl⟩ : syracuseStep 3618647 = 5427971) B5427971
theorem B44546183 : Blo 1068616 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B4340179 : Blo 1068616 4340179 := bstep (se 1 (by rfl) ⟨3255134, by rfl⟩ : syracuseStep 4340179 = 6510269) B6510269
theorem B6863399 : Blo 1068616 6863399 := bstep (se 1 (by rfl) ⟨5147549, by rfl⟩ : syracuseStep 6863399 = 10295099) B10295099
theorem B10566283 : Blo 1068616 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B5421815 : Blo 1068616 5421815 := bstep (se 1 (by rfl) ⟨4066361, by rfl⟩ : syracuseStep 5421815 = 8132723) B8132723
theorem B2407247 : Blo 1068616 2407247 := bstep (se 1 (by rfl) ⟨1805435, by rfl⟩ : syracuseStep 2407247 = 3610871) B3610871
theorem B4635535 : Blo 1068616 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B3619727 : Blo 1068616 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B2407463 : Blo 1068616 2407463 := bstep (se 1 (by rfl) ⟨1805597, by rfl⟩ : syracuseStep 2407463 = 3611195) B3611195
theorem B2407643 : Blo 1068616 2407643 := bstep (se 1 (by rfl) ⟨1805732, by rfl⟩ : syracuseStep 2407643 = 3611465) B3611465
theorem B5422301 : Blo 1068616 5422301 := bstep (se 3 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 5422301 = 2033363) B2033363
theorem B2571497 : Blo 1068616 2571497 := bstep (se 2 (by rfl) ⟨964311, by rfl⟩ : syracuseStep 2571497 = 1928623) B1928623
theorem B2407841 : Blo 1068616 2407841 := bstep (se 2 (by rfl) ⟨902940, by rfl⟩ : syracuseStep 2407841 = 1805881) B1805881
theorem B2571707 : Blo 1068616 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B3423703 : Blo 1068616 3423703 := bstep (se 1 (by rfl) ⟨2567777, by rfl⟩ : syracuseStep 3423703 = 5135555) B5135555
theorem B1130159 : Blo 1068616 1130159 := bstep (se 1 (by rfl) ⟨847619, by rfl⟩ : syracuseStep 1130159 = 1695239) B1695239
theorem B1785655 : Blo 1068616 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B2408399 : Blo 1068616 2408399 := bstep (se 1 (by rfl) ⟨1806299, by rfl⟩ : syracuseStep 2408399 = 3612599) B3612599
theorem B2605337 : Blo 1068616 2605337 := bstep (se 2 (by rfl) ⟨977001, by rfl⟩ : syracuseStep 2605337 = 1954003) B1954003
theorem B2408777 : Blo 1068616 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B2408795 : Blo 1068616 2408795 := bstep (se 1 (by rfl) ⟨1806596, by rfl⟩ : syracuseStep 2408795 = 3613193) B3613193
theorem B14631353 : Blo 1068616 14631353 := bstep (se 2 (by rfl) ⟨5486757, by rfl⟩ : syracuseStep 14631353 = 10973515) B10973515
theorem B2409371 : Blo 1068616 2409371 := bstep (se 1 (by rfl) ⟨1807028, by rfl⟩ : syracuseStep 2409371 = 3614057) B3614057
theorem B12174299 : Blo 1068616 12174299 := bstep (se 1 (by rfl) ⟨9130724, by rfl⟩ : syracuseStep 12174299 = 18261449) B18261449
theorem B6865883 : Blo 1068616 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B19514465 : Blo 1068616 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B7324769 : Blo 1068616 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B2409569 : Blo 1068616 2409569 := bstep (se 2 (by rfl) ⟨903588, by rfl⟩ : syracuseStep 2409569 = 1807177) B1807177
theorem B2573545 : Blo 1068616 2573545 := bstep (se 2 (by rfl) ⟨965079, by rfl⟩ : syracuseStep 2573545 = 1930159) B1930159
theorem B2934047 : Blo 1068616 2934047 := bstep (se 1 (by rfl) ⟨2200535, by rfl⟩ : syracuseStep 2934047 = 4401071) B4401071
theorem B2409767 : Blo 1068616 2409767 := bstep (se 1 (by rfl) ⟨1807325, by rfl⟩ : syracuseStep 2409767 = 3614651) B3614651
theorem B8242519 : Blo 1068616 8242519 := bstep (se 1 (by rfl) ⟨6181889, by rfl⟩ : syracuseStep 8242519 = 12363779) B12363779
theorem B2573707 : Blo 1068616 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B27477467 : Blo 1068616 27477467 := bstep (se 1 (by rfl) ⟨20608100, by rfl⟩ : syracuseStep 27477467 = 41216201) B41216201
theorem B9160249 : Blo 1068616 9160249 := bstep (se 2 (by rfl) ⟨3435093, by rfl⟩ : syracuseStep 9160249 = 6870187) B6870187
theorem B2410145 : Blo 1068616 2410145 := bstep (se 2 (by rfl) ⟨903804, by rfl⟩ : syracuseStep 2410145 = 1807609) B1807609
theorem B2705359 : Blo 1068616 2705359 := bstep (se 1 (by rfl) ⟨2029019, by rfl⟩ : syracuseStep 2705359 = 4058039) B4058039
theorem B22235141 : Blo 1068616 22235141 := bstep (se 4 (by rfl) ⟨2084544, by rfl⟩ : syracuseStep 22235141 = 4169089) B4169089
theorem B2410505 : Blo 1068616 2410505 := bstep (se 2 (by rfl) ⟨903939, by rfl⟩ : syracuseStep 2410505 = 1807879) B1807879
theorem B2410919 : Blo 1068616 2410919 := bstep (se 1 (by rfl) ⟨1808189, by rfl⟩ : syracuseStep 2410919 = 3616379) B3616379
theorem B6506963 : Blo 1068616 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B2411027 : Blo 1068616 2411027 := bstep (se 1 (by rfl) ⟨1808270, by rfl⟩ : syracuseStep 2411027 = 3616541) B3616541
theorem B5425703 : Blo 1068616 5425703 := bstep (se 1 (by rfl) ⟨4069277, by rfl⟩ : syracuseStep 5425703 = 8138555) B8138555
theorem B2411081 : Blo 1068616 2411081 := bstep (se 2 (by rfl) ⟨904155, by rfl⟩ : syracuseStep 2411081 = 1808311) B1808311
theorem B2706331 : Blo 1068616 2706331 := bstep (se 1 (by rfl) ⟨2029748, by rfl⟩ : syracuseStep 2706331 = 4059497) B4059497
theorem B2411495 : Blo 1068616 2411495 := bstep (se 1 (by rfl) ⟨1808621, by rfl⟩ : syracuseStep 2411495 = 3617243) B3617243
theorem B12209291 : Blo 1068616 12209291 := bstep (se 1 (by rfl) ⟨9156968, by rfl⟩ : syracuseStep 12209291 = 18313937) B18313937
theorem B2411873 : Blo 1068616 2411873 := bstep (se 2 (by rfl) ⟨904452, by rfl⟩ : syracuseStep 2411873 = 1808905) B1808905
theorem B2411963 : Blo 1068616 2411963 := bstep (se 1 (by rfl) ⟨1808972, by rfl⟩ : syracuseStep 2411963 = 3617945) B3617945
theorem B2412089 : Blo 1068616 2412089 := bstep (se 2 (by rfl) ⟨904533, by rfl⟩ : syracuseStep 2412089 = 1809067) B1809067
theorem B1068767 : Blo 1068616 1068767 := bstep (se 1 (by rfl) ⟨801575, by rfl⟩ : syracuseStep 1068767 = 1603151) B1603151
theorem B1068847 : Blo 1068616 1068847 := bstep (se 1 (by rfl) ⟨801635, by rfl⟩ : syracuseStep 1068847 = 1603271) B1603271
theorem B1068955 : Blo 1068616 1068955 := bstep (se 1 (by rfl) ⟨801716, by rfl⟩ : syracuseStep 1068955 = 1603433) B1603433
theorem B1069007 : Blo 1068616 1069007 := bstep (se 1 (by rfl) ⟨801755, by rfl⟩ : syracuseStep 1069007 = 1603511) B1603511
theorem B6868957 : Blo 1068616 6868957 := bstep (se 3 (by rfl) ⟨1287929, by rfl⟩ : syracuseStep 6868957 = 2575859) B2575859
theorem B1069031 : Blo 1068616 1069031 := bstep (se 1 (by rfl) ⟨801773, by rfl⟩ : syracuseStep 1069031 = 1603547) B1603547
theorem B2707465 : Blo 1068616 2707465 := bstep (se 2 (by rfl) ⟨1015299, by rfl⟩ : syracuseStep 2707465 = 2030599) B2030599
theorem B2412755 : Blo 1068616 2412755 := bstep (se 1 (by rfl) ⟨1809566, by rfl⟩ : syracuseStep 2412755 = 3619133) B3619133
theorem B2412809 : Blo 1068616 2412809 := bstep (se 2 (by rfl) ⟨904803, by rfl⟩ : syracuseStep 2412809 = 1809607) B1809607
theorem B1069343 : Blo 1068616 1069343 := bstep (se 1 (by rfl) ⟨802007, by rfl⟩ : syracuseStep 1069343 = 1604015) B1604015
theorem B1069403 : Blo 1068616 1069403 := bstep (se 1 (by rfl) ⟨802052, by rfl⟩ : syracuseStep 1069403 = 1604105) B1604105
theorem B1069423 : Blo 1068616 1069423 := bstep (se 1 (by rfl) ⟨802067, by rfl⟩ : syracuseStep 1069423 = 1604135) B1604135
theorem B1069479 : Blo 1068616 1069479 := bstep (se 1 (by rfl) ⟨802109, by rfl⟩ : syracuseStep 1069479 = 1604219) B1604219
theorem B2413025 : Blo 1068616 2413025 := bstep (se 2 (by rfl) ⟨904884, by rfl⟩ : syracuseStep 2413025 = 1809769) B1809769
theorem B1069563 : Blo 1068616 1069563 := bstep (se 1 (by rfl) ⟨802172, by rfl⟩ : syracuseStep 1069563 = 1604345) B1604345
theorem B12210749 : Blo 1068616 12210749 := bstep (se 3 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 12210749 = 4579031) B4579031
theorem B1069631 : Blo 1068616 1069631 := bstep (se 1 (by rfl) ⟨802223, by rfl⟩ : syracuseStep 1069631 = 1604447) B1604447
theorem B1069639 : Blo 1068616 1069639 := bstep (se 1 (by rfl) ⟨802229, by rfl⟩ : syracuseStep 1069639 = 1604459) B1604459
theorem B5427809 : Blo 1068616 5427809 := bstep (se 2 (by rfl) ⟨2035428, by rfl⟩ : syracuseStep 5427809 = 4070857) B4070857
theorem B1069791 : Blo 1068616 1069791 := bstep (se 1 (by rfl) ⟨802343, by rfl⟩ : syracuseStep 1069791 = 1604687) B1604687
theorem B2413331 : Blo 1068616 2413331 := bstep (se 1 (by rfl) ⟨1809998, by rfl⟩ : syracuseStep 2413331 = 3619997) B3619997
theorem B1069871 : Blo 1068616 1069871 := bstep (se 1 (by rfl) ⟨802403, by rfl⟩ : syracuseStep 1069871 = 1604807) B1604807
theorem B1069979 : Blo 1068616 1069979 := bstep (se 1 (by rfl) ⟨802484, by rfl⟩ : syracuseStep 1069979 = 1604969) B1604969
theorem B1070031 : Blo 1068616 1070031 := bstep (se 1 (by rfl) ⟨802523, by rfl⟩ : syracuseStep 1070031 = 1605047) B1605047
theorem B1070055 : Blo 1068616 1070055 := bstep (se 1 (by rfl) ⟨802541, by rfl⟩ : syracuseStep 1070055 = 1605083) B1605083
theorem B3855485 : Blo 1068616 3855485 := bstep (se 3 (by rfl) ⟨722903, by rfl⟩ : syracuseStep 3855485 = 1445807) B1445807
theorem B5428457 : Blo 1068616 5428457 := bstep (se 2 (by rfl) ⟨2035671, by rfl⟩ : syracuseStep 5428457 = 4071343) B4071343
theorem B1070367 : Blo 1068616 1070367 := bstep (se 1 (by rfl) ⟨802775, by rfl⟩ : syracuseStep 1070367 = 1605551) B1605551
theorem B1070427 : Blo 1068616 1070427 := bstep (se 1 (by rfl) ⟨802820, by rfl⟩ : syracuseStep 1070427 = 1605641) B1605641
theorem B4576607 : Blo 1068616 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B1070447 : Blo 1068616 1070447 := bstep (se 1 (by rfl) ⟨802835, by rfl⟩ : syracuseStep 1070447 = 1605671) B1605671
theorem B2708873 : Blo 1068616 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B5428619 : Blo 1068616 5428619 := bstep (se 1 (by rfl) ⟨4071464, by rfl⟩ : syracuseStep 5428619 = 8142929) B8142929
theorem B1070503 : Blo 1068616 1070503 := bstep (se 1 (by rfl) ⟨802877, by rfl⟩ : syracuseStep 1070503 = 1605755) B1605755
theorem B2708923 : Blo 1068616 2708923 := bstep (se 1 (by rfl) ⟨2031692, by rfl⟩ : syracuseStep 2708923 = 4063385) B4063385
theorem B1070587 : Blo 1068616 1070587 := bstep (se 1 (by rfl) ⟨802940, by rfl⟩ : syracuseStep 1070587 = 1605881) B1605881
theorem B7722503 : Blo 1068616 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1070655 : Blo 1068616 1070655 := bstep (se 1 (by rfl) ⟨802991, by rfl⟩ : syracuseStep 1070655 = 1605983) B1605983
theorem B1070663 : Blo 1068616 1070663 := bstep (se 1 (by rfl) ⟨802997, by rfl⟩ : syracuseStep 1070663 = 1605995) B1605995
theorem B1070815 : Blo 1068616 1070815 := bstep (se 1 (by rfl) ⟨803111, by rfl⟩ : syracuseStep 1070815 = 1606223) B1606223
theorem B2709227 : Blo 1068616 2709227 := bstep (se 1 (by rfl) ⟨2031920, by rfl⟩ : syracuseStep 2709227 = 4063841) B4063841
theorem B1070895 : Blo 1068616 1070895 := bstep (se 1 (by rfl) ⟨803171, by rfl⟩ : syracuseStep 1070895 = 1606343) B1606343
theorem B1071003 : Blo 1068616 1071003 := bstep (se 1 (by rfl) ⟨803252, by rfl⟩ : syracuseStep 1071003 = 1606505) B1606505
theorem B1071055 : Blo 1068616 1071055 := bstep (se 1 (by rfl) ⟨803291, by rfl⟩ : syracuseStep 1071055 = 1606583) B1606583
theorem B1071079 : Blo 1068616 1071079 := bstep (se 1 (by rfl) ⟨803309, by rfl⟩ : syracuseStep 1071079 = 1606619) B1606619
theorem B1202395 : Blo 1068616 1202395 := bstep (se 1 (by rfl) ⟨901796, by rfl⟩ : syracuseStep 1202395 = 1803593) B1803593
theorem B1071391 : Blo 1068616 1071391 := bstep (se 1 (by rfl) ⟨803543, by rfl⟩ : syracuseStep 1071391 = 1607087) B1607087
theorem B2742601 : Blo 1068616 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B9132365 : Blo 1068616 9132365 := bstep (se 3 (by rfl) ⟨1712318, by rfl⟩ : syracuseStep 9132365 = 3424637) B3424637
theorem B1071451 : Blo 1068616 1071451 := bstep (se 1 (by rfl) ⟨803588, by rfl⟩ : syracuseStep 1071451 = 1607177) B1607177
theorem B1071471 : Blo 1068616 1071471 := bstep (se 1 (by rfl) ⟨803603, by rfl⟩ : syracuseStep 1071471 = 1607207) B1607207
theorem B1071527 : Blo 1068616 1071527 := bstep (se 1 (by rfl) ⟨803645, by rfl⟩ : syracuseStep 1071527 = 1607291) B1607291
theorem B1202683 : Blo 1068616 1202683 := bstep (se 1 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 1202683 = 1804025) B1804025
theorem B1071611 : Blo 1068616 1071611 := bstep (se 1 (by rfl) ⟨803708, by rfl⟩ : syracuseStep 1071611 = 1607417) B1607417
theorem B1071679 : Blo 1068616 1071679 := bstep (se 1 (by rfl) ⟨803759, by rfl⟩ : syracuseStep 1071679 = 1607519) B1607519
theorem B1071687 : Blo 1068616 1071687 := bstep (se 1 (by rfl) ⟨803765, by rfl⟩ : syracuseStep 1071687 = 1607531) B1607531
theorem B1202863 : Blo 1068616 1202863 := bstep (se 1 (by rfl) ⟨902147, by rfl⟩ : syracuseStep 1202863 = 1804295) B1804295
theorem B2710199 : Blo 1068616 2710199 := bstep (se 1 (by rfl) ⟨2032649, by rfl⟩ : syracuseStep 2710199 = 4065299) B4065299
theorem B1071839 : Blo 1068616 1071839 := bstep (se 1 (by rfl) ⟨803879, by rfl⟩ : syracuseStep 1071839 = 1607759) B1607759
theorem B1071919 : Blo 1068616 1071919 := bstep (se 1 (by rfl) ⟨803939, by rfl⟩ : syracuseStep 1071919 = 1607879) B1607879
theorem B1072027 : Blo 1068616 1072027 := bstep (se 1 (by rfl) ⟨804020, by rfl⟩ : syracuseStep 1072027 = 1608041) B1608041
theorem B1203151 : Blo 1068616 1203151 := bstep (se 1 (by rfl) ⟨902363, by rfl⟩ : syracuseStep 1203151 = 1804727) B1804727
theorem B1072079 : Blo 1068616 1072079 := bstep (se 1 (by rfl) ⟨804059, by rfl⟩ : syracuseStep 1072079 = 1608119) B1608119
theorem B2284519 : Blo 1068616 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B1072103 : Blo 1068616 1072103 := bstep (se 1 (by rfl) ⟨804077, by rfl⟩ : syracuseStep 1072103 = 1608155) B1608155
theorem B1072415 : Blo 1068616 1072415 := bstep (se 1 (by rfl) ⟨804311, by rfl⟩ : syracuseStep 1072415 = 1608623) B1608623
theorem B1203547 : Blo 1068616 1203547 := bstep (se 1 (by rfl) ⟨902660, by rfl⟩ : syracuseStep 1203547 = 1805321) B1805321
theorem B1072475 : Blo 1068616 1072475 := bstep (se 1 (by rfl) ⟨804356, by rfl⟩ : syracuseStep 1072475 = 1608713) B1608713
theorem B1072495 : Blo 1068616 1072495 := bstep (se 1 (by rfl) ⟨804371, by rfl⟩ : syracuseStep 1072495 = 1608743) B1608743
theorem B2284937 : Blo 1068616 2284937 := bstep (se 2 (by rfl) ⟨856851, by rfl⟩ : syracuseStep 2284937 = 1713703) B1713703
theorem B1072551 : Blo 1068616 1072551 := bstep (se 1 (by rfl) ⟨804413, by rfl⟩ : syracuseStep 1072551 = 1608827) B1608827
theorem B1203655 : Blo 1068616 1203655 := bstep (se 1 (by rfl) ⟨902741, by rfl⟩ : syracuseStep 1203655 = 1805483) B1805483
theorem B2711303 : Blo 1068616 2711303 := bstep (se 1 (by rfl) ⟨2033477, by rfl⟩ : syracuseStep 2711303 = 4066955) B4066955
theorem B1204015 : Blo 1068616 1204015 := bstep (se 1 (by rfl) ⟨903011, by rfl⟩ : syracuseStep 1204015 = 1806023) B1806023
theorem B2711353 : Blo 1068616 2711353 := bstep (se 2 (by rfl) ⟨1016757, by rfl⟩ : syracuseStep 2711353 = 2033515) B2033515
theorem B1466191 : Blo 1068616 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B1204123 : Blo 1068616 1204123 := bstep (se 1 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 1204123 = 1806185) B1806185
theorem B37019555 : Blo 1068616 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B2711657 : Blo 1068616 2711657 := bstep (se 2 (by rfl) ⟨1016871, by rfl⟩ : syracuseStep 2711657 = 2033743) B2033743
theorem B1204519 : Blo 1068616 1204519 := bstep (se 1 (by rfl) ⟨903389, by rfl⟩ : syracuseStep 1204519 = 1806779) B1806779
theorem B1204591 : Blo 1068616 1204591 := bstep (se 1 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 1204591 = 1806887) B1806887
theorem B1204807 : Blo 1068616 1204807 := bstep (se 1 (by rfl) ⟨903605, by rfl⟩ : syracuseStep 1204807 = 1807211) B1807211
theorem B2712143 : Blo 1068616 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B17621651 : Blo 1068616 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B4580023 : Blo 1068616 4580023 := bstep (se 1 (by rfl) ⟨3435017, by rfl⟩ : syracuseStep 4580023 = 6870035) B6870035
theorem B12346273 : Blo 1068616 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B4580297 : Blo 1068616 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B5563367 : Blo 1068616 5563367 := bstep (se 1 (by rfl) ⟨4172525, by rfl⟩ : syracuseStep 5563367 = 8345051) B8345051
theorem B5792915 : Blo 1068616 5792915 := bstep (se 1 (by rfl) ⟨4344686, by rfl⟩ : syracuseStep 5792915 = 8689373) B8689373
theorem B2712791 : Blo 1068616 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B8119601 : Blo 1068616 8119601 := bstep (se 2 (by rfl) ⟨3044850, by rfl⟩ : syracuseStep 8119601 = 6089701) B6089701
theorem B4875643 : Blo 1068616 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B1205671 : Blo 1068616 1205671 := bstep (se 1 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 1205671 = 1808507) B1808507
theorem B2287415 : Blo 1068616 2287415 := bstep (se 1 (by rfl) ⟨1715561, by rfl⟩ : syracuseStep 2287415 = 3431123) B3431123
theorem B1206247 : Blo 1068616 1206247 := bstep (se 1 (by rfl) ⟨904685, by rfl⟩ : syracuseStep 1206247 = 1809371) B1809371
theorem B8120573 : Blo 1068616 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B4581629 : Blo 1068616 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B2288047 : Blo 1068616 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B2714107 : Blo 1068616 2714107 := bstep (se 1 (by rfl) ⟨2035580, by rfl⟩ : syracuseStep 2714107 = 4071161) B4071161
theorem B2714219 : Blo 1068616 2714219 := bstep (se 1 (by rfl) ⟨2035664, by rfl⟩ : syracuseStep 2714219 = 4071329) B4071329
theorem B1829879 : Blo 1068616 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B5139571 : Blo 1068616 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B3435659 : Blo 1068616 3435659 := bstep (se 1 (by rfl) ⟨2576744, by rfl⟩ : syracuseStep 3435659 = 5153489) B5153489
theorem B3435709 : Blo 1068616 3435709 := bstep (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) B1288391
theorem B2714867 : Blo 1068616 2714867 := bstep (se 1 (by rfl) ⟨2036150, by rfl⟩ : syracuseStep 2714867 = 4072301) B4072301
theorem B2288935 : Blo 1068616 2288935 := bstep (se 1 (by rfl) ⟨1716701, by rfl⟩ : syracuseStep 2288935 = 3433403) B3433403
theorem B4058707 : Blo 1068616 4058707 := bstep (se 1 (by rfl) ⟨3044030, by rfl⟩ : syracuseStep 4058707 = 6088061) B6088061
theorem B2289235 : Blo 1068616 2289235 := bstep (se 1 (by rfl) ⟨1716926, by rfl⟩ : syracuseStep 2289235 = 3433853) B3433853
theorem B10284641 : Blo 1068616 10284641 := bstep (se 2 (by rfl) ⟨3856740, by rfl⟩ : syracuseStep 10284641 = 7713481) B7713481
theorem B9760733 : Blo 1068616 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B1142759 : Blo 1068616 1142759 := bstep (se 1 (by rfl) ⟨857069, by rfl⟩ : syracuseStep 1142759 = 1714139) B1714139
theorem B5795945 : Blo 1068616 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B9138379 : Blo 1068616 9138379 := bstep (se 1 (by rfl) ⟨6853784, by rfl⟩ : syracuseStep 9138379 = 13707569) B13707569
theorem B12185963 : Blo 1068616 12185963 := bstep (se 1 (by rfl) ⟨9139472, by rfl⟩ : syracuseStep 12185963 = 18278945) B18278945
theorem B14119343 : Blo 1068616 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B4059983 : Blo 1068616 4059983 := bstep (se 1 (by rfl) ⟨3044987, by rfl⟩ : syracuseStep 4059983 = 6089975) B6089975
theorem B6091685 : Blo 1068616 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B4060151 : Blo 1068616 4060151 := bstep (se 1 (by rfl) ⟨3045113, by rfl⟩ : syracuseStep 4060151 = 6090227) B6090227
theorem B3044567 : Blo 1068616 3044567 := bstep (se 1 (by rfl) ⟨2283425, by rfl⟩ : syracuseStep 3044567 = 4566851) B4566851
theorem B10974503 : Blo 1068616 10974503 := bstep (se 1 (by rfl) ⟨8230877, by rfl⟩ : syracuseStep 10974503 = 16461755) B16461755
theorem B1602953 : Blo 1068616 1602953 := bstep (se 2 (by rfl) ⟨601107, by rfl⟩ : syracuseStep 1602953 = 1202215) B1202215
theorem B7730635 : Blo 1068616 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B1603307 : Blo 1068616 1603307 := bstep (se 1 (by rfl) ⟨1202480, by rfl⟩ : syracuseStep 1603307 = 2404961) B2404961
theorem B12187421 : Blo 1068616 12187421 := bstep (se 3 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 12187421 = 4570283) B4570283
theorem B2029369 : Blo 1068616 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B1603535 : Blo 1068616 1603535 := bstep (se 1 (by rfl) ⟨1202651, by rfl⟩ : syracuseStep 1603535 = 2405303) B2405303
theorem B2029673 : Blo 1068616 2029673 := bstep (se 2 (by rfl) ⟨761127, by rfl⟩ : syracuseStep 2029673 = 1522255) B1522255
theorem B1931369 : Blo 1068616 1931369 := bstep (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) B1448527
theorem B1603931 : Blo 1068616 1603931 := bstep (se 1 (by rfl) ⟨1202948, by rfl⟩ : syracuseStep 1603931 = 2405897) B2405897
theorem B4061623 : Blo 1068616 4061623 := bstep (se 1 (by rfl) ⟨3046217, by rfl⟩ : syracuseStep 4061623 = 6092435) B6092435
theorem B47118797 : Blo 1068616 47118797 := bstep (se 3 (by rfl) ⟨8834774, by rfl⟩ : syracuseStep 47118797 = 17669549) B17669549
theorem B1604159 : Blo 1068616 1604159 := bstep (se 1 (by rfl) ⟨1203119, by rfl⟩ : syracuseStep 1604159 = 2406239) B2406239
theorem B1604279 : Blo 1068616 1604279 := bstep (se 1 (by rfl) ⟨1203209, by rfl⟩ : syracuseStep 1604279 = 2406419) B2406419
theorem B10976143 : Blo 1068616 10976143 := bstep (se 1 (by rfl) ⟨8232107, by rfl⟩ : syracuseStep 10976143 = 16464215) B16464215
theorem B4062095 : Blo 1068616 4062095 := bstep (se 1 (by rfl) ⟨3046571, by rfl⟩ : syracuseStep 4062095 = 6093143) B6093143
theorem B1604507 : Blo 1068616 1604507 := bstep (se 1 (by rfl) ⟨1203380, by rfl⟩ : syracuseStep 1604507 = 2406761) B2406761
theorem B20544677 : Blo 1068616 20544677 := bstep (se 4 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 20544677 = 3852127) B3852127
theorem B1604903 : Blo 1068616 1604903 := bstep (se 1 (by rfl) ⟨1203677, by rfl⟩ : syracuseStep 1604903 = 2407355) B2407355
theorem B1604987 : Blo 1068616 1604987 := bstep (se 1 (by rfl) ⟨1203740, by rfl⟩ : syracuseStep 1604987 = 2407481) B2407481
theorem B1605113 : Blo 1068616 1605113 := bstep (se 2 (by rfl) ⟨601917, by rfl⟩ : syracuseStep 1605113 = 1203835) B1203835
theorem B1605215 : Blo 1068616 1605215 := bstep (se 1 (by rfl) ⟨1203911, by rfl⟩ : syracuseStep 1605215 = 2407823) B2407823
theorem B1605431 : Blo 1068616 1605431 := bstep (se 1 (by rfl) ⟨1204073, by rfl⟩ : syracuseStep 1605431 = 2408147) B2408147
theorem B1736891 : Blo 1068616 1736891 := bstep (se 1 (by rfl) ⟨1302668, by rfl⟩ : syracuseStep 1736891 = 2605337) B2605337
theorem B1605851 : Blo 1068616 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B1605863 : Blo 1068616 1605863 := bstep (se 1 (by rfl) ⟨1204397, by rfl⟩ : syracuseStep 1605863 = 2408795) B2408795
theorem B1606025 : Blo 1068616 1606025 := bstep (se 2 (by rfl) ⟨602259, by rfl⟩ : syracuseStep 1606025 = 1204519) B1204519
theorem B1606121 : Blo 1068616 1606121 := bstep (se 2 (by rfl) ⟨602295, by rfl⟩ : syracuseStep 1606121 = 1204591) B1204591
theorem B1606247 : Blo 1068616 1606247 := bstep (se 1 (by rfl) ⟨1204685, by rfl⟩ : syracuseStep 1606247 = 2409371) B2409371
theorem B12190337 : Blo 1068616 12190337 := bstep (se 2 (by rfl) ⟨4571376, by rfl⟩ : syracuseStep 12190337 = 9142753) B9142753
theorem B13009643 : Blo 1068616 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B4883179 : Blo 1068616 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B17367787 : Blo 1068616 17367787 := bstep (se 1 (by rfl) ⟨13025840, by rfl⟩ : syracuseStep 17367787 = 26051681) B26051681
theorem B1606379 : Blo 1068616 1606379 := bstep (se 1 (by rfl) ⟨1204784, by rfl⟩ : syracuseStep 1606379 = 2409569) B2409569
theorem B1606409 : Blo 1068616 1606409 := bstep (se 2 (by rfl) ⟨602403, by rfl⟩ : syracuseStep 1606409 = 1204807) B1204807
theorem B1606511 : Blo 1068616 1606511 := bstep (se 1 (by rfl) ⟨1204883, by rfl⟩ : syracuseStep 1606511 = 2409767) B2409767
theorem B18318311 : Blo 1068616 18318311 := bstep (se 1 (by rfl) ⟨13738733, by rfl⟩ : syracuseStep 18318311 = 27477467) B27477467
theorem B1606763 : Blo 1068616 1606763 := bstep (se 1 (by rfl) ⟨1205072, by rfl⟩ : syracuseStep 1606763 = 2410145) B2410145
theorem B2032847 : Blo 1068616 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B1607003 : Blo 1068616 1607003 := bstep (se 1 (by rfl) ⟨1205252, by rfl⟩ : syracuseStep 1607003 = 2410505) B2410505
theorem B1607279 : Blo 1068616 1607279 := bstep (se 1 (by rfl) ⟨1205459, by rfl⟩ : syracuseStep 1607279 = 2410919) B2410919
theorem B1607351 : Blo 1068616 1607351 := bstep (se 1 (by rfl) ⟨1205513, by rfl⟩ : syracuseStep 1607351 = 2411027) B2411027
theorem B1607387 : Blo 1068616 1607387 := bstep (se 1 (by rfl) ⟨1205540, by rfl⟩ : syracuseStep 1607387 = 2411081) B2411081
theorem B1607561 : Blo 1068616 1607561 := bstep (se 2 (by rfl) ⟨602835, by rfl⟩ : syracuseStep 1607561 = 1205671) B1205671
theorem B1607663 : Blo 1068616 1607663 := bstep (se 1 (by rfl) ⟨1205747, by rfl⟩ : syracuseStep 1607663 = 2411495) B2411495
theorem B1607915 : Blo 1068616 1607915 := bstep (se 1 (by rfl) ⟨1205936, by rfl⟩ : syracuseStep 1607915 = 2411873) B2411873
theorem B1607975 : Blo 1068616 1607975 := bstep (se 1 (by rfl) ⟨1205981, by rfl⟩ : syracuseStep 1607975 = 2411963) B2411963
theorem B1804585 : Blo 1068616 1804585 := bstep (se 2 (by rfl) ⟨676719, by rfl⟩ : syracuseStep 1804585 = 1353439) B1353439
theorem B3606875 : Blo 1068616 3606875 := bstep (se 1 (by rfl) ⟨2705156, by rfl⟩ : syracuseStep 3606875 = 5410313) B5410313
theorem B1608059 : Blo 1068616 1608059 := bstep (se 1 (by rfl) ⟨1206044, by rfl⟩ : syracuseStep 1608059 = 2412089) B2412089
theorem B3607145 : Blo 1068616 3607145 := bstep (se 2 (by rfl) ⟨1352679, by rfl⟩ : syracuseStep 3607145 = 2705359) B2705359
theorem B1608329 : Blo 1068616 1608329 := bstep (se 2 (by rfl) ⟨603123, by rfl⟩ : syracuseStep 1608329 = 1206247) B1206247
theorem B2034487 : Blo 1068616 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B1608503 : Blo 1068616 1608503 := bstep (se 1 (by rfl) ⟨1206377, by rfl⟩ : syracuseStep 1608503 = 2412755) B2412755
theorem B1608539 : Blo 1068616 1608539 := bstep (se 1 (by rfl) ⟨1206404, by rfl⟩ : syracuseStep 1608539 = 2412809) B2412809
theorem B3476459 : Blo 1068616 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B1608683 : Blo 1068616 1608683 := bstep (se 1 (by rfl) ⟨1206512, by rfl⟩ : syracuseStep 1608683 = 2413025) B2413025
theorem B1608887 : Blo 1068616 1608887 := bstep (se 1 (by rfl) ⟨1206665, by rfl⟩ : syracuseStep 1608887 = 2413331) B2413331
theorem B3050729 : Blo 1068616 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B3051071 : Blo 1068616 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B1805915 : Blo 1068616 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B3608171 : Blo 1068616 3608171 := bstep (se 1 (by rfl) ⟨2706128, by rfl⟩ : syracuseStep 3608171 = 5412257) B5412257
theorem B2035307 : Blo 1068616 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B5148335 : Blo 1068616 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B1806151 : Blo 1068616 1806151 := bstep (se 1 (by rfl) ⟨1354613, by rfl⟩ : syracuseStep 1806151 = 2709227) B2709227
theorem B50106221 : Blo 1068616 50106221 := bstep (se 3 (by rfl) ⟨9394916, by rfl⟩ : syracuseStep 50106221 = 18789833) B18789833
theorem B3608441 : Blo 1068616 3608441 := bstep (se 2 (by rfl) ⟨1353165, by rfl⟩ : syracuseStep 3608441 = 2706331) B2706331
theorem B6852761 : Blo 1068616 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B3608765 : Blo 1068616 3608765 := bstep (se 3 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 3608765 = 1353287) B1353287
theorem B3051913 : Blo 1068616 3051913 := bstep (se 2 (by rfl) ⟨1144467, by rfl⟩ : syracuseStep 3051913 = 2288935) B2288935
theorem B1806799 : Blo 1068616 1806799 := bstep (se 1 (by rfl) ⟨1355099, by rfl⟩ : syracuseStep 1806799 = 2710199) B2710199
theorem B5411609 : Blo 1068616 5411609 := bstep (se 2 (by rfl) ⟨2029353, by rfl⟩ : syracuseStep 5411609 = 4058707) B4058707
theorem B3052313 : Blo 1068616 3052313 := bstep (se 2 (by rfl) ⟨1144617, by rfl⟩ : syracuseStep 3052313 = 2289235) B2289235
theorem B4952873 : Blo 1068616 4952873 := bstep (se 2 (by rfl) ⟨1857327, by rfl⟩ : syracuseStep 4952873 = 3714655) B3714655
theorem B6099907 : Blo 1068616 6099907 := bstep (se 1 (by rfl) ⟨4574930, by rfl⟩ : syracuseStep 6099907 = 9149861) B9149861
theorem B1807535 : Blo 1068616 1807535 := bstep (se 1 (by rfl) ⟨1355651, by rfl⟩ : syracuseStep 1807535 = 2711303) B2711303
theorem B24679703 : Blo 1068616 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B3609953 : Blo 1068616 3609953 := bstep (se 2 (by rfl) ⟨1353732, by rfl⟩ : syracuseStep 3609953 = 2707465) B2707465
theorem B1807771 : Blo 1068616 1807771 := bstep (se 1 (by rfl) ⟨1355828, by rfl⟩ : syracuseStep 1807771 = 2711657) B2711657
theorem B5150317 : Blo 1068616 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B1808095 : Blo 1068616 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B32905055 : Blo 1068616 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B3053531 : Blo 1068616 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B3708911 : Blo 1068616 3708911 := bstep (se 1 (by rfl) ⟨2781683, by rfl⟩ : syracuseStep 3708911 = 5563367) B5563367
theorem B1808527 : Blo 1068616 1808527 := bstep (se 1 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 1808527 = 2712791) B2712791
theorem B5413067 : Blo 1068616 5413067 := bstep (se 1 (by rfl) ⟨4059800, by rfl⟩ : syracuseStep 5413067 = 8119601) B8119601
theorem B4069673 : Blo 1068616 4069673 := bstep (se 2 (by rfl) ⟨1526127, by rfl⟩ : syracuseStep 4069673 = 3052255) B3052255
theorem B7707109 : Blo 1068616 7707109 := bstep (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) B1445083
theorem B5413715 : Blo 1068616 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B3054419 : Blo 1068616 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B4397915 : Blo 1068616 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B41098103 : Blo 1068616 41098103 := bstep (se 1 (by rfl) ⟨30823577, by rfl⟩ : syracuseStep 41098103 = 61647155) B61647155
theorem B1809479 : Blo 1068616 1809479 := bstep (se 1 (by rfl) ⟨1357109, by rfl⟩ : syracuseStep 1809479 = 2714219) B2714219
theorem B3611897 : Blo 1068616 3611897 := bstep (se 2 (by rfl) ⟨1354461, by rfl⟩ : syracuseStep 3611897 = 2708923) B2708923
theorem B1219919 : Blo 1068616 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B9903455 : Blo 1068616 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B9772487 : Blo 1068616 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B1809911 : Blo 1068616 1809911 := bstep (se 1 (by rfl) ⟨1357433, by rfl⟩ : syracuseStep 1809911 = 2714867) B2714867
theorem B3612167 : Blo 1068616 3612167 := bstep (se 1 (by rfl) ⟨2709125, by rfl⟩ : syracuseStep 3612167 = 5418251) B5418251
theorem B6856427 : Blo 1068616 6856427 := bstep (se 1 (by rfl) ⟨5142320, by rfl⟩ : syracuseStep 6856427 = 10284641) B10284641
theorem B7938107 : Blo 1068616 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B9412895 : Blo 1068616 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B3613247 : Blo 1068616 3613247 := bstep (se 1 (by rfl) ⟨2709935, by rfl⟩ : syracuseStep 3613247 = 5419871) B5419871
theorem B5415497 : Blo 1068616 5415497 := bstep (se 2 (by rfl) ⟨2030811, by rfl⟩ : syracuseStep 5415497 = 4061623) B4061623
theorem B7316335 : Blo 1068616 7316335 := bstep (se 1 (by rfl) ⟨5487251, by rfl⟩ : syracuseStep 7316335 = 10974503) B10974503
theorem B6857885 : Blo 1068616 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B1353115 : Blo 1068616 1353115 := bstep (se 1 (by rfl) ⟨1014836, by rfl⟩ : syracuseStep 1353115 = 2029673) B2029673
theorem B29697455 : Blo 1068616 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B3614543 : Blo 1068616 3614543 := bstep (se 1 (by rfl) ⟨2710907, by rfl⟩ : syracuseStep 3614543 = 5421815) B5421815
theorem B4564937 : Blo 1068616 4564937 := bstep (se 2 (by rfl) ⟨1711851, by rfl⟩ : syracuseStep 4564937 = 3423703) B3423703
theorem B3614867 : Blo 1068616 3614867 := bstep (se 1 (by rfl) ⟨2711150, by rfl⟩ : syracuseStep 3614867 = 5422301) B5422301
theorem B1714331 : Blo 1068616 1714331 := bstep (se 1 (by rfl) ⟨1285748, by rfl⟩ : syracuseStep 1714331 = 2571497) B2571497
theorem B3615137 : Blo 1068616 3615137 := bstep (se 2 (by rfl) ⟨1355676, by rfl⟩ : syracuseStep 3615137 = 2711353) B2711353
theorem B6106697 : Blo 1068616 6106697 := bstep (se 2 (by rfl) ⟨2290011, by rfl⟩ : syracuseStep 6106697 = 4580023) B4580023
theorem B7319155 : Blo 1068616 7319155 := bstep (se 1 (by rfl) ⟨5489366, by rfl⟩ : syracuseStep 7319155 = 10978733) B10978733
theorem B2928527 : Blo 1068616 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B14823427 : Blo 1068616 14823427 := bstep (se 1 (by rfl) ⟨11117570, by rfl⟩ : syracuseStep 14823427 = 22235141) B22235141
theorem B2404475 : Blo 1068616 2404475 := bstep (se 1 (by rfl) ⟨1803356, by rfl⟩ : syracuseStep 2404475 = 3606713) B3606713
theorem B4337975 : Blo 1068616 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B3617135 : Blo 1068616 3617135 := bstep (se 1 (by rfl) ⟨2712851, by rfl⟩ : syracuseStep 3617135 = 5425703) B5425703
theorem B2404745 : Blo 1068616 2404745 := bstep (se 2 (by rfl) ⟨901779, by rfl⟩ : syracuseStep 2404745 = 1803559) B1803559
theorem B10990025 : Blo 1068616 10990025 := bstep (se 2 (by rfl) ⟨4121259, by rfl⟩ : syracuseStep 10990025 = 8242519) B8242519
theorem B8139527 : Blo 1068616 8139527 := bstep (se 1 (by rfl) ⟨6104645, by rfl⟩ : syracuseStep 8139527 = 12209291) B12209291
theorem B2405483 : Blo 1068616 2405483 := bstep (se 1 (by rfl) ⟨1804112, by rfl⟩ : syracuseStep 2405483 = 3608225) B3608225
theorem B1356907 : Blo 1068616 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B2406059 : Blo 1068616 2406059 := bstep (se 1 (by rfl) ⟨1804544, by rfl⟩ : syracuseStep 2406059 = 3609089) B3609089
theorem B8140499 : Blo 1068616 8140499 := bstep (se 1 (by rfl) ⟨6105374, by rfl⟩ : syracuseStep 8140499 = 12210749) B12210749
theorem B15447773 : Blo 1068616 15447773 := bstep (se 3 (by rfl) ⟨2896457, by rfl⟩ : syracuseStep 15447773 = 5792915) B5792915
theorem B3618539 : Blo 1068616 3618539 := bstep (se 1 (by rfl) ⟨2713904, by rfl⟩ : syracuseStep 3618539 = 5427809) B5427809
theorem B34748149 : Blo 1068616 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B2406383 : Blo 1068616 2406383 := bstep (se 1 (by rfl) ⟨1804787, by rfl⟩ : syracuseStep 2406383 = 3609575) B3609575
theorem B3618809 : Blo 1068616 3618809 := bstep (se 2 (by rfl) ⟨1357053, by rfl⟩ : syracuseStep 3618809 = 2714107) B2714107
theorem B3618971 : Blo 1068616 3618971 := bstep (se 1 (by rfl) ⟨2714228, by rfl⟩ : syracuseStep 3618971 = 5428457) B5428457
theorem B2406599 : Blo 1068616 2406599 := bstep (se 1 (by rfl) ⟨1804949, by rfl⟩ : syracuseStep 2406599 = 3609899) B3609899
theorem B4634857 : Blo 1068616 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B3619079 : Blo 1068616 3619079 := bstep (se 1 (by rfl) ⟨2714309, by rfl⟩ : syracuseStep 3619079 = 5428619) B5428619
theorem B2406779 : Blo 1068616 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B2407049 : Blo 1068616 2407049 := bstep (se 2 (by rfl) ⟨902643, by rfl⟩ : syracuseStep 2407049 = 1805287) B1805287
theorem B2407607 : Blo 1068616 2407607 := bstep (se 1 (by rfl) ⟨1805705, by rfl⟩ : syracuseStep 2407607 = 3611411) B3611411
theorem B65846789 : Blo 1068616 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B1523291 : Blo 1068616 1523291 := bstep (se 1 (by rfl) ⟨1142468, by rfl⟩ : syracuseStep 1523291 = 2284937) B2284937
theorem B2408183 : Blo 1068616 2408183 := bstep (se 1 (by rfl) ⟨1806137, by rfl⟩ : syracuseStep 2408183 = 3612275) B3612275
theorem B4570967 : Blo 1068616 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B2408363 : Blo 1068616 2408363 := bstep (se 1 (by rfl) ⟨1806272, by rfl⟩ : syracuseStep 2408363 = 3612545) B3612545
theorem B9158609 : Blo 1068616 9158609 := bstep (se 2 (by rfl) ⟨3434478, by rfl⟩ : syracuseStep 9158609 = 6868957) B6868957
theorem B4571275 : Blo 1068616 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B11583719 : Blo 1068616 11583719 := bstep (se 1 (by rfl) ⟨8687789, by rfl⟩ : syracuseStep 11583719 = 17375579) B17375579
theorem B11747767 : Blo 1068616 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B2408903 : Blo 1068616 2408903 := bstep (se 1 (by rfl) ⟨1806677, by rfl⟩ : syracuseStep 2408903 = 3613355) B3613355
theorem B2409263 : Blo 1068616 2409263 := bstep (se 1 (by rfl) ⟨1806947, by rfl⟩ : syracuseStep 2409263 = 3613895) B3613895
theorem B4637627 : Blo 1068616 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B5424083 : Blo 1068616 5424083 := bstep (se 1 (by rfl) ⟨4068062, by rfl⟩ : syracuseStep 5424083 = 8136125) B8136125
theorem B1524943 : Blo 1068616 1524943 := bstep (se 1 (by rfl) ⟨1143707, by rfl⟩ : syracuseStep 1524943 = 2287415) B2287415
theorem B34784477 : Blo 1068616 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B27411857 : Blo 1068616 27411857 := bstep (se 2 (by rfl) ⟨10279446, by rfl⟩ : syracuseStep 27411857 = 20558893) B20558893
theorem B3851795 : Blo 1068616 3851795 := bstep (se 1 (by rfl) ⟨2888846, by rfl⟩ : syracuseStep 3851795 = 5777693) B5777693
theorem B2410271 : Blo 1068616 2410271 := bstep (se 1 (by rfl) ⟨1807703, by rfl⟩ : syracuseStep 2410271 = 3615407) B3615407
theorem B10307513 : Blo 1068616 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B26003429 : Blo 1068616 26003429 := bstep (se 4 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 26003429 = 4875643) B4875643
theorem B2410487 : Blo 1068616 2410487 := bstep (se 1 (by rfl) ⟨1807865, by rfl⟩ : syracuseStep 2410487 = 3615731) B3615731
theorem B2410847 : Blo 1068616 2410847 := bstep (se 1 (by rfl) ⟨1808135, by rfl⟩ : syracuseStep 2410847 = 3616271) B3616271
theorem B2705825 : Blo 1068616 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B15452795 : Blo 1068616 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B7719563 : Blo 1068616 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B6507155 : Blo 1068616 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B2411567 : Blo 1068616 2411567 := bstep (se 1 (by rfl) ⟨1808675, by rfl⟩ : syracuseStep 2411567 = 3617351) B3617351
theorem B3656801 : Blo 1068616 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B2706655 : Blo 1068616 2706655 := bstep (se 1 (by rfl) ⟨2029991, by rfl⟩ : syracuseStep 2706655 = 4059983) B4059983
theorem B5786905 : Blo 1068616 5786905 := bstep (se 2 (by rfl) ⟨2170089, by rfl⟩ : syracuseStep 5786905 = 4340179) B4340179
theorem B2706767 : Blo 1068616 2706767 := bstep (se 1 (by rfl) ⟨2030075, by rfl⟩ : syracuseStep 2706767 = 4060151) B4060151
theorem B2411855 : Blo 1068616 2411855 := bstep (se 1 (by rfl) ⟨1808891, by rfl⟩ : syracuseStep 2411855 = 3617783) B3617783
theorem B2411945 : Blo 1068616 2411945 := bstep (se 2 (by rfl) ⟨904479, by rfl⟩ : syracuseStep 2411945 = 1808959) B1808959
theorem B3853757 : Blo 1068616 3853757 := bstep (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) B1445159
theorem B1068635 : Blo 1068616 1068635 := bstep (se 1 (by rfl) ⟨801476, by rfl⟩ : syracuseStep 1068635 = 1602953) B1602953
theorem B1068871 : Blo 1068616 1068871 := bstep (se 1 (by rfl) ⟨801653, by rfl⟩ : syracuseStep 1068871 = 1603307) B1603307
theorem B14634857 : Blo 1068616 14634857 := bstep (se 2 (by rfl) ⟨5488071, by rfl⟩ : syracuseStep 14634857 = 10976143) B10976143
theorem B6180713 : Blo 1068616 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B2412431 : Blo 1068616 2412431 := bstep (se 1 (by rfl) ⟨1809323, by rfl⟩ : syracuseStep 2412431 = 3618647) B3618647
theorem B1069023 : Blo 1068616 1069023 := bstep (se 1 (by rfl) ⟨801767, by rfl⟩ : syracuseStep 1069023 = 1603535) B1603535
theorem B1069287 : Blo 1068616 1069287 := bstep (se 1 (by rfl) ⟨801965, by rfl⟩ : syracuseStep 1069287 = 1603931) B1603931
theorem B9523493 : Blo 1068616 9523493 := bstep (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) B1785655
theorem B31412531 : Blo 1068616 31412531 := bstep (se 1 (by rfl) ⟨23559398, by rfl⟩ : syracuseStep 31412531 = 47118797) B47118797
theorem B4575599 : Blo 1068616 4575599 := bstep (se 1 (by rfl) ⟨3431699, by rfl⟩ : syracuseStep 4575599 = 6863399) B6863399
theorem B1069439 : Blo 1068616 1069439 := bstep (se 1 (by rfl) ⟨802079, by rfl⟩ : syracuseStep 1069439 = 1604159) B1604159
theorem B7819685 : Blo 1068616 7819685 := bstep (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) B1466191
theorem B1069519 : Blo 1068616 1069519 := bstep (se 1 (by rfl) ⟨802139, by rfl⟩ : syracuseStep 1069519 = 1604279) B1604279
theorem B2708063 : Blo 1068616 2708063 := bstep (se 1 (by rfl) ⟨2031047, by rfl⟩ : syracuseStep 2708063 = 4062095) B4062095
theorem B2413151 : Blo 1068616 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B1069671 : Blo 1068616 1069671 := bstep (se 1 (by rfl) ⟨802253, by rfl⟩ : syracuseStep 1069671 = 1604507) B1604507
theorem B11588345 : Blo 1068616 11588345 := bstep (se 2 (by rfl) ⟨4345629, by rfl⟩ : syracuseStep 11588345 = 8691259) B8691259
theorem B1069935 : Blo 1068616 1069935 := bstep (se 1 (by rfl) ⟨802451, by rfl⟩ : syracuseStep 1069935 = 1604903) B1604903
theorem B1069991 : Blo 1068616 1069991 := bstep (se 1 (by rfl) ⟨802493, by rfl⟩ : syracuseStep 1069991 = 1604987) B1604987
theorem B1070075 : Blo 1068616 1070075 := bstep (se 1 (by rfl) ⟨802556, by rfl⟩ : syracuseStep 1070075 = 1605113) B1605113
theorem B1070143 : Blo 1068616 1070143 := bstep (se 1 (by rfl) ⟨802607, by rfl⟩ : syracuseStep 1070143 = 1605215) B1605215
theorem B1070287 : Blo 1068616 1070287 := bstep (se 1 (by rfl) ⟨802715, by rfl⟩ : syracuseStep 1070287 = 1605431) B1605431
theorem B1070491 : Blo 1068616 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B1070703 : Blo 1068616 1070703 := bstep (se 1 (by rfl) ⟨803027, by rfl⟩ : syracuseStep 1070703 = 1606055) B1606055
theorem B9754235 : Blo 1068616 9754235 := bstep (se 1 (by rfl) ⟨7315676, by rfl⟩ : syracuseStep 9754235 = 14631353) B14631353
theorem B1070759 : Blo 1068616 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B1070843 : Blo 1068616 1070843 := bstep (se 1 (by rfl) ⟨803132, by rfl⟩ : syracuseStep 1070843 = 1606265) B1606265
theorem B1070879 : Blo 1068616 1070879 := bstep (se 1 (by rfl) ⟨803159, by rfl⟩ : syracuseStep 1070879 = 1606319) B1606319
theorem B1070911 : Blo 1068616 1070911 := bstep (se 1 (by rfl) ⟨803183, by rfl⟩ : syracuseStep 1070911 = 1606367) B1606367
theorem B8116199 : Blo 1068616 8116199 := bstep (se 1 (by rfl) ⟨6087149, by rfl⟩ : syracuseStep 8116199 = 12174299) B12174299
theorem B4577255 : Blo 1068616 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B1071087 : Blo 1068616 1071087 := bstep (se 1 (by rfl) ⟨803315, by rfl⟩ : syracuseStep 1071087 = 1606631) B1606631
theorem B1071259 : Blo 1068616 1071259 := bstep (se 1 (by rfl) ⟨803444, by rfl⟩ : syracuseStep 1071259 = 1606889) B1606889
theorem B1956031 : Blo 1068616 1956031 := bstep (se 1 (by rfl) ⟨1467023, by rfl⟩ : syracuseStep 1956031 = 2934047) B2934047
theorem B1071295 : Blo 1068616 1071295 := bstep (se 1 (by rfl) ⟨803471, by rfl⟩ : syracuseStep 1071295 = 1606943) B1606943
theorem B1071407 : Blo 1068616 1071407 := bstep (se 1 (by rfl) ⟨803555, by rfl⟩ : syracuseStep 1071407 = 1607111) B1607111
theorem B1071643 : Blo 1068616 1071643 := bstep (se 1 (by rfl) ⟨803732, by rfl⟩ : syracuseStep 1071643 = 1607465) B1607465
theorem B1202719 : Blo 1068616 1202719 := bstep (se 1 (by rfl) ⟨902039, by rfl⟩ : syracuseStep 1202719 = 1804079) B1804079
theorem B1071647 : Blo 1068616 1071647 := bstep (se 1 (by rfl) ⟨803735, by rfl⟩ : syracuseStep 1071647 = 1607471) B1607471
theorem B1071963 : Blo 1068616 1071963 := bstep (se 1 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 1071963 = 1607945) B1607945
theorem B1072031 : Blo 1068616 1072031 := bstep (se 1 (by rfl) ⟨804023, by rfl⟩ : syracuseStep 1072031 = 1608047) B1608047
theorem B3431393 : Blo 1068616 3431393 := bstep (se 2 (by rfl) ⟨1286772, by rfl⟩ : syracuseStep 3431393 = 2573545) B2573545
theorem B6872033 : Blo 1068616 6872033 := bstep (se 2 (by rfl) ⟨2577012, by rfl⟩ : syracuseStep 6872033 = 5154025) B5154025
theorem B1072175 : Blo 1068616 1072175 := bstep (se 1 (by rfl) ⟨804131, by rfl⟩ : syracuseStep 1072175 = 1608263) B1608263
theorem B1072199 : Blo 1068616 1072199 := bstep (se 1 (by rfl) ⟨804149, by rfl⟩ : syracuseStep 1072199 = 1608299) B1608299
theorem B13720691 : Blo 1068616 13720691 := bstep (se 1 (by rfl) ⟨10290518, by rfl⟩ : syracuseStep 13720691 = 20581037) B20581037
theorem B3431609 : Blo 1068616 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B1072351 : Blo 1068616 1072351 := bstep (se 1 (by rfl) ⟨804263, by rfl⟩ : syracuseStep 1072351 = 1608527) B1608527
theorem B12213665 : Blo 1068616 12213665 := bstep (se 2 (by rfl) ⟨4580124, by rfl⟩ : syracuseStep 12213665 = 9160249) B9160249
theorem B1072615 : Blo 1068616 1072615 := bstep (se 1 (by rfl) ⟨804461, by rfl⟩ : syracuseStep 1072615 = 1608923) B1608923
theorem B6512165 : Blo 1068616 6512165 := bstep (se 4 (by rfl) ⟨610515, by rfl⟩ : syracuseStep 6512165 = 1221031) B1221031
theorem B18538469 : Blo 1068616 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B3760415 : Blo 1068616 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B2711839 : Blo 1068616 2711839 := bstep (se 1 (by rfl) ⟨2033879, by rfl⟩ : syracuseStep 2711839 = 4067759) B4067759
theorem B10281293 : Blo 1068616 10281293 := bstep (se 3 (by rfl) ⟨1927742, by rfl⟩ : syracuseStep 10281293 = 3855485) B3855485
theorem B18309563 : Blo 1068616 18309563 := bstep (se 1 (by rfl) ⟨13732172, by rfl⟩ : syracuseStep 18309563 = 27464345) B27464345
theorem B2712487 : Blo 1068616 2712487 := bstep (se 1 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 2712487 = 4068731) B4068731
theorem B1205311 : Blo 1068616 1205311 := bstep (se 1 (by rfl) ⟨903983, by rfl⟩ : syracuseStep 1205311 = 1807967) B1807967
theorem B1205455 : Blo 1068616 1205455 := bstep (se 1 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 1205455 = 1808183) B1808183
theorem B4875695 : Blo 1068616 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B6088243 : Blo 1068616 6088243 := bstep (se 1 (by rfl) ⟨4566182, by rfl⟩ : syracuseStep 6088243 = 9132365) B9132365
theorem B4580945 : Blo 1068616 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B6514505 : Blo 1068616 6514505 := bstep (se 2 (by rfl) ⟨2442939, by rfl⟩ : syracuseStep 6514505 = 4885879) B4885879
theorem B27813719 : Blo 1068616 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1206427 : Blo 1068616 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B1206463 : Blo 1068616 1206463 := bstep (se 1 (by rfl) ⟨904847, by rfl⟩ : syracuseStep 1206463 = 1809695) B1809695
theorem B2713895 : Blo 1068616 2713895 := bstep (se 1 (by rfl) ⟨2035421, by rfl⟩ : syracuseStep 2713895 = 4070843) B4070843
theorem B12184505 : Blo 1068616 12184505 := bstep (se 2 (by rfl) ⟨4569189, by rfl⟩ : syracuseStep 12184505 = 9138379) B9138379
theorem B13922647 : Blo 1068616 13922647 := bstep (se 1 (by rfl) ⟨10441985, by rfl⟩ : syracuseStep 13922647 = 20883971) B20883971
theorem B2290439 : Blo 1068616 2290439 := bstep (se 1 (by rfl) ⟨1717829, by rfl⟩ : syracuseStep 2290439 = 3435659) B3435659
theorem B1602971 : Blo 1068616 1602971 := bstep (se 1 (by rfl) ⟨1202228, by rfl⟩ : syracuseStep 1602971 = 2404457) B2404457
theorem B3863963 : Blo 1068616 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B8123975 : Blo 1068616 8123975 := bstep (se 1 (by rfl) ⟨6092981, by rfl⟩ : syracuseStep 8123975 = 12185963) B12185963
theorem B1603193 : Blo 1068616 1603193 := bstep (se 2 (by rfl) ⟨601197, by rfl⟩ : syracuseStep 1603193 = 1202395) B1202395
theorem B1603295 : Blo 1068616 1603295 := bstep (se 1 (by rfl) ⟨1202471, by rfl⟩ : syracuseStep 1603295 = 2404943) B2404943
theorem B1603391 : Blo 1068616 1603391 := bstep (se 1 (by rfl) ⟨1202543, by rfl⟩ : syracuseStep 1603391 = 2405087) B2405087
theorem B4061123 : Blo 1068616 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B1603559 : Blo 1068616 1603559 := bstep (se 1 (by rfl) ⟨1202669, by rfl⟩ : syracuseStep 1603559 = 2405339) B2405339
theorem B1603577 : Blo 1068616 1603577 := bstep (se 2 (by rfl) ⟨601341, by rfl⟩ : syracuseStep 1603577 = 1202683) B1202683
theorem B1603679 : Blo 1068616 1603679 := bstep (se 1 (by rfl) ⟨1202759, by rfl⟩ : syracuseStep 1603679 = 2405519) B2405519
theorem B2029711 : Blo 1068616 2029711 := bstep (se 1 (by rfl) ⟨1522283, by rfl⟩ : syracuseStep 2029711 = 3044567) B3044567
theorem B1603739 : Blo 1068616 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B14088377 : Blo 1068616 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B1603775 : Blo 1068616 1603775 := bstep (se 1 (by rfl) ⟨1202831, by rfl⟩ : syracuseStep 1603775 = 2405663) B2405663
theorem B1603817 : Blo 1068616 1603817 := bstep (se 2 (by rfl) ⟨601431, by rfl⟩ : syracuseStep 1603817 = 1202863) B1202863
theorem B8124947 : Blo 1068616 8124947 := bstep (se 1 (by rfl) ⟨6093710, by rfl⟩ : syracuseStep 8124947 = 12187421) B12187421
theorem B1604123 : Blo 1068616 1604123 := bstep (se 1 (by rfl) ⟨1203092, by rfl⟩ : syracuseStep 1604123 = 2406185) B2406185
theorem B1604201 : Blo 1068616 1604201 := bstep (se 2 (by rfl) ⟨601575, by rfl⟩ : syracuseStep 1604201 = 1203151) B1203151
theorem B3046025 : Blo 1068616 3046025 := bstep (se 2 (by rfl) ⟨1142259, by rfl⟩ : syracuseStep 3046025 = 2284519) B2284519
theorem B1604729 : Blo 1068616 1604729 := bstep (se 2 (by rfl) ⟨601773, by rfl⟩ : syracuseStep 1604729 = 1203547) B1203547
theorem B3013757 : Blo 1068616 3013757 := bstep (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) B1130159
theorem B1604831 : Blo 1068616 1604831 := bstep (se 1 (by rfl) ⟨1203623, by rfl⟩ : syracuseStep 1604831 = 2407247) B2407247
theorem B1604873 : Blo 1068616 1604873 := bstep (se 2 (by rfl) ⟨601827, by rfl⟩ : syracuseStep 1604873 = 1203655) B1203655
theorem B1604975 : Blo 1068616 1604975 := bstep (se 1 (by rfl) ⟨1203731, by rfl⟩ : syracuseStep 1604975 = 2407463) B2407463
theorem B13696451 : Blo 1068616 13696451 := bstep (se 1 (by rfl) ⟨10272338, by rfl⟩ : syracuseStep 13696451 = 20544677) B20544677
theorem B1605095 : Blo 1068616 1605095 := bstep (se 1 (by rfl) ⟨1203821, by rfl⟩ : syracuseStep 1605095 = 2407643) B2407643
theorem B1605227 : Blo 1068616 1605227 := bstep (se 1 (by rfl) ⟨1203920, by rfl⟩ : syracuseStep 1605227 = 2407841) B2407841
theorem B1605353 : Blo 1068616 1605353 := bstep (se 2 (by rfl) ⟨602007, by rfl⟩ : syracuseStep 1605353 = 1204015) B1204015
theorem B1605497 : Blo 1068616 1605497 := bstep (se 2 (by rfl) ⟨602061, by rfl⟩ : syracuseStep 1605497 = 1204123) B1204123
theorem B3047357 : Blo 1068616 3047357 := bstep (se 3 (by rfl) ⟨571379, by rfl⟩ : syracuseStep 3047357 = 1142759) B1142759
theorem B1605599 : Blo 1068616 1605599 := bstep (se 1 (by rfl) ⟨1204199, by rfl⟩ : syracuseStep 1605599 = 2408399) B2408399
theorem B6095033 : Blo 1068616 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B1605935 : Blo 1068616 1605935 := bstep (se 1 (by rfl) ⟨1204451, by rfl⟩ : syracuseStep 1605935 = 2408903) B2408903
theorem B8126891 : Blo 1068616 8126891 := bstep (se 1 (by rfl) ⟨6095168, by rfl⟩ : syracuseStep 8126891 = 12190337) B12190337
theorem B1606175 : Blo 1068616 1606175 := bstep (se 1 (by rfl) ⟨1204631, by rfl⟩ : syracuseStep 1606175 = 2409263) B2409263
theorem B15663689 : Blo 1068616 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B25101053 : Blo 1068616 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B11567933 : Blo 1068616 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B1606847 : Blo 1068616 1606847 := bstep (se 1 (by rfl) ⟨1205135, by rfl⟩ : syracuseStep 1606847 = 2410271) B2410271
theorem B17335619 : Blo 1068616 17335619 := bstep (se 1 (by rfl) ⟨13001714, by rfl⟩ : syracuseStep 17335619 = 26003429) B26003429
theorem B1606991 : Blo 1068616 1606991 := bstep (se 1 (by rfl) ⟨1205243, by rfl⟩ : syracuseStep 1606991 = 2410487) B2410487
theorem B1607081 : Blo 1068616 1607081 := bstep (se 2 (by rfl) ⟨602655, by rfl⟩ : syracuseStep 1607081 = 1205311) B1205311
theorem B1607231 : Blo 1068616 1607231 := bstep (se 1 (by rfl) ⟨1205423, by rfl⟩ : syracuseStep 1607231 = 2410847) B2410847
theorem B2033257 : Blo 1068616 2033257 := bstep (se 2 (by rfl) ⟨762471, by rfl⟩ : syracuseStep 2033257 = 1524943) B1524943
theorem B1607273 : Blo 1068616 1607273 := bstep (se 2 (by rfl) ⟨602727, by rfl⟩ : syracuseStep 1607273 = 1205455) B1205455
theorem B1803883 : Blo 1068616 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B1804153 : Blo 1068616 1804153 := bstep (se 2 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 1804153 = 1353115) B1353115
theorem B1607711 : Blo 1068616 1607711 := bstep (se 1 (by rfl) ⟨1205783, by rfl⟩ : syracuseStep 1607711 = 2411567) B2411567
theorem B2033819 : Blo 1068616 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B1804511 : Blo 1068616 1804511 := bstep (se 1 (by rfl) ⟨1353383, by rfl⟩ : syracuseStep 1804511 = 2706767) B2706767
theorem B1607903 : Blo 1068616 1607903 := bstep (se 1 (by rfl) ⟨1205927, by rfl⟩ : syracuseStep 1607903 = 2411855) B2411855
theorem B1607963 : Blo 1068616 1607963 := bstep (se 1 (by rfl) ⟨1205972, by rfl⟩ : syracuseStep 1607963 = 2411945) B2411945
theorem B2034047 : Blo 1068616 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B1608287 : Blo 1068616 1608287 := bstep (se 1 (by rfl) ⟨1206215, by rfl⟩ : syracuseStep 1608287 = 2412431) B2412431
theorem B20941687 : Blo 1068616 20941687 := bstep (se 1 (by rfl) ⟨15706265, by rfl⟩ : syracuseStep 20941687 = 31412531) B31412531
theorem B1608569 : Blo 1068616 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B3050399 : Blo 1068616 3050399 := bstep (se 1 (by rfl) ⟨2287799, by rfl⟩ : syracuseStep 3050399 = 4575599) B4575599
theorem B1608617 : Blo 1068616 1608617 := bstep (se 2 (by rfl) ⟨603231, by rfl⟩ : syracuseStep 1608617 = 1206463) B1206463
theorem B5213123 : Blo 1068616 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B1805375 : Blo 1068616 1805375 := bstep (se 1 (by rfl) ⟨1354031, by rfl⟩ : syracuseStep 1805375 = 2708063) B2708063
theorem B1608767 : Blo 1068616 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B18287693 : Blo 1068616 18287693 := bstep (se 3 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 18287693 = 6857885) B6857885
theorem B3607739 : Blo 1068616 3607739 := bstep (se 1 (by rfl) ⟨2705804, by rfl⟩ : syracuseStep 3607739 = 5411609) B5411609
theorem B2034875 : Blo 1068616 2034875 := bstep (se 1 (by rfl) ⟨1526156, by rfl⟩ : syracuseStep 2034875 = 3052313) B3052313
theorem B16453135 : Blo 1068616 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B2035687 : Blo 1068616 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B5410799 : Blo 1068616 5410799 := bstep (se 1 (by rfl) ⟨4058099, by rfl⟩ : syracuseStep 5410799 = 8116199) B8116199
theorem B3051503 : Blo 1068616 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B3608711 : Blo 1068616 3608711 := bstep (se 1 (by rfl) ⟨2706533, by rfl⟩ : syracuseStep 3608711 = 5413067) B5413067
theorem B3608873 : Blo 1068616 3608873 := bstep (se 2 (by rfl) ⟨1353327, by rfl⟩ : syracuseStep 3608873 = 2706655) B2706655
theorem B3609143 : Blo 1068616 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B2036279 : Blo 1068616 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B27398735 : Blo 1068616 27398735 := bstep (se 1 (by rfl) ⟨20549051, by rfl⟩ : syracuseStep 27398735 = 41098103) B41098103
theorem B9147127 : Blo 1068616 9147127 := bstep (se 1 (by rfl) ⟨6860345, by rfl⟩ : syracuseStep 9147127 = 13720691) B13720691
theorem B12358979 : Blo 1068616 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B19764569 : Blo 1068616 19764569 := bstep (se 2 (by rfl) ⟨7411713, by rfl⟩ : syracuseStep 19764569 = 14823427) B14823427
theorem B6854195 : Blo 1068616 6854195 := bstep (se 1 (by rfl) ⟨5140646, by rfl⟩ : syracuseStep 6854195 = 10281293) B10281293
theorem B3610331 : Blo 1068616 3610331 := bstep (se 1 (by rfl) ⟨2707748, by rfl⟩ : syracuseStep 3610331 = 5415497) B5415497
theorem B4069217 : Blo 1068616 4069217 := bstep (se 2 (by rfl) ⟨1525956, by rfl⟩ : syracuseStep 4069217 = 3051913) B3051913
theorem B3250463 : Blo 1068616 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B3053963 : Blo 1068616 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B8133209 : Blo 1068616 8133209 := bstep (se 2 (by rfl) ⟨3049953, by rfl⟩ : syracuseStep 8133209 = 6099907) B6099907
theorem B1809209 : Blo 1068616 1809209 := bstep (se 2 (by rfl) ⟨678453, by rfl⟩ : syracuseStep 1809209 = 1356907) B1356907
theorem B1809263 : Blo 1068616 1809263 := bstep (se 1 (by rfl) ⟨1356947, by rfl⟩ : syracuseStep 1809263 = 2713895) B2713895
theorem B20585501 : Blo 1068616 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B297016469 : Blo 1068616 297016469 := bstep (se 6 (by rfl) ⟨6961323, by rfl⟩ : syracuseStep 297016469 = 13922647) B13922647
theorem B4071131 : Blo 1068616 4071131 := bstep (se 1 (by rfl) ⟨3053348, by rfl⟩ : syracuseStep 4071131 = 6106697) B6106697
theorem B3253117 : Blo 1068616 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B5415983 : Blo 1068616 5415983 := bstep (se 1 (by rfl) ⟨4061987, by rfl⟩ : syracuseStep 5415983 = 8123975) B8123975
theorem B10298515 : Blo 1068616 10298515 := bstep (se 1 (by rfl) ⟨7723886, by rfl⟩ : syracuseStep 10298515 = 15447773) B15447773
theorem B5416631 : Blo 1068616 5416631 := bstep (se 1 (by rfl) ⟨4062473, by rfl⟩ : syracuseStep 5416631 = 8124947) B8124947
theorem B2009171 : Blo 1068616 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B6105739 : Blo 1068616 6105739 := bstep (se 1 (by rfl) ⟨4579304, by rfl⟩ : syracuseStep 6105739 = 9158609) B9158609
theorem B1157927 : Blo 1068616 1157927 := bstep (se 1 (by rfl) ⟨868445, by rfl⟩ : syracuseStep 1157927 = 1736891) B1736891
theorem B3615785 : Blo 1068616 3615785 := bstep (se 2 (by rfl) ⟨1355919, by rfl⟩ : syracuseStep 3615785 = 2711839) B2711839
theorem B3091751 : Blo 1068616 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B3616055 : Blo 1068616 3616055 := bstep (se 1 (by rfl) ⟨2712041, by rfl⟩ : syracuseStep 3616055 = 5424083) B5424083
theorem B1355231 : Blo 1068616 1355231 := bstep (se 1 (by rfl) ⟨1016423, by rfl⟩ : syracuseStep 1355231 = 2032847) B2032847
theorem B10432165 : Blo 1068616 10432165 := bstep (se 4 (by rfl) ⟨978015, by rfl⟩ : syracuseStep 10432165 = 1956031) B1956031
theorem B2567863 : Blo 1068616 2567863 := bstep (se 1 (by rfl) ⟨1925897, by rfl⟩ : syracuseStep 2567863 = 3851795) B3851795
theorem B3616649 : Blo 1068616 3616649 := bstep (se 2 (by rfl) ⟨1356243, by rfl⟩ : syracuseStep 3616649 = 2712487) B2712487
theorem B2404583 : Blo 1068616 2404583 := bstep (se 1 (by rfl) ⟨1803437, by rfl⟩ : syracuseStep 2404583 = 3606875) B3606875
theorem B2404763 : Blo 1068616 2404763 := bstep (se 1 (by rfl) ⟨1803572, by rfl⟩ : syracuseStep 2404763 = 3607145) B3607145
theorem B10301863 : Blo 1068616 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B4338103 : Blo 1068616 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B2437867 : Blo 1068616 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B2569171 : Blo 1068616 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B2405447 : Blo 1068616 2405447 := bstep (se 1 (by rfl) ⟨1804085, by rfl⟩ : syracuseStep 2405447 = 3608171) B3608171
theorem B33404147 : Blo 1068616 33404147 := bstep (se 1 (by rfl) ⟨25053110, by rfl⟩ : syracuseStep 33404147 = 50106221) B50106221
theorem B2405627 : Blo 1068616 2405627 := bstep (se 1 (by rfl) ⟨1804220, by rfl⟩ : syracuseStep 2405627 = 3608441) B3608441
theorem B4568507 : Blo 1068616 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2405843 : Blo 1068616 2405843 := bstep (se 1 (by rfl) ⟨1804382, by rfl⟩ : syracuseStep 2405843 = 3608765) B3608765
theorem B2406113 : Blo 1068616 2406113 := bstep (se 2 (by rfl) ⟨902292, by rfl⟩ : syracuseStep 2406113 = 1804585) B1804585
theorem B2406635 : Blo 1068616 2406635 := bstep (se 1 (by rfl) ⟨1804976, by rfl⟩ : syracuseStep 2406635 = 3609953) B3609953
theorem B6502823 : Blo 1068616 6502823 := bstep (se 1 (by rfl) ⟨4877117, by rfl⟩ : syracuseStep 6502823 = 9754235) B9754235
theorem B21936703 : Blo 1068616 21936703 := bstep (se 1 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 21936703 = 32905055) B32905055
theorem B2472607 : Blo 1068616 2472607 := bstep (se 1 (by rfl) ⟨1854455, by rfl⟩ : syracuseStep 2472607 = 3708911) B3708911
theorem B7715873 : Blo 1068616 7715873 := bstep (se 2 (by rfl) ⟨2893452, by rfl⟩ : syracuseStep 7715873 = 5786905) B5786905
theorem B2407931 : Blo 1068616 2407931 := bstep (se 1 (by rfl) ⟨1805948, by rfl⟩ : syracuseStep 2407931 = 3611897) B3611897
theorem B6602303 : Blo 1068616 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B8142443 : Blo 1068616 8142443 := bstep (se 1 (by rfl) ⟨6106832, by rfl⟩ : syracuseStep 8142443 = 12213665) B12213665
theorem B2408111 : Blo 1068616 2408111 := bstep (se 1 (by rfl) ⟨1806083, by rfl⟩ : syracuseStep 2408111 = 3612167) B3612167
theorem B4341443 : Blo 1068616 4341443 := bstep (se 1 (by rfl) ⟨3256082, by rfl⟩ : syracuseStep 4341443 = 6512165) B6512165
theorem B2408201 : Blo 1068616 2408201 := bstep (se 2 (by rfl) ⟨903075, by rfl⟩ : syracuseStep 2408201 = 1806151) B1806151
theorem B4570951 : Blo 1068616 4570951 := bstep (se 1 (by rfl) ⟨3428213, by rfl⟩ : syracuseStep 4570951 = 6856427) B6856427
theorem B5292071 : Blo 1068616 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B2506943 : Blo 1068616 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B12206375 : Blo 1068616 12206375 := bstep (se 1 (by rfl) ⟨9154781, by rfl⟩ : syracuseStep 12206375 = 18309563) B18309563
theorem B2408831 : Blo 1068616 2408831 := bstep (se 1 (by rfl) ⟨1806623, by rfl⟩ : syracuseStep 2408831 = 3613247) B3613247
theorem B4571549 : Blo 1068616 4571549 := bstep (se 3 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 4571549 = 1714331) B1714331
theorem B37569005 : Blo 1068616 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B2409065 : Blo 1068616 2409065 := bstep (se 2 (by rfl) ⟨903399, by rfl⟩ : syracuseStep 2409065 = 1806799) B1806799
theorem B4343003 : Blo 1068616 4343003 := bstep (se 1 (by rfl) ⟨3257252, by rfl⟩ : syracuseStep 4343003 = 6514505) B6514505
theorem B2409695 : Blo 1068616 2409695 := bstep (se 1 (by rfl) ⟨1807271, by rfl⟩ : syracuseStep 2409695 = 3614543) B3614543
theorem B2409911 : Blo 1068616 2409911 := bstep (se 1 (by rfl) ⟨1807433, by rfl⟩ : syracuseStep 2409911 = 3614867) B3614867
theorem B2410091 : Blo 1068616 2410091 := bstep (se 1 (by rfl) ⟨1807568, by rfl⟩ : syracuseStep 2410091 = 3615137) B3615137
theorem B2410361 : Blo 1068616 2410361 := bstep (se 2 (by rfl) ⟨903885, by rfl⟩ : syracuseStep 2410361 = 1807771) B1807771
theorem B6867089 : Blo 1068616 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B2410793 : Blo 1068616 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B1952351 : Blo 1068616 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B2706281 : Blo 1068616 2706281 := bstep (se 2 (by rfl) ⟨1014855, by rfl⟩ : syracuseStep 2706281 = 2029711) B2029711
theorem B2411369 : Blo 1068616 2411369 := bstep (se 2 (by rfl) ⟨904263, by rfl⟩ : syracuseStep 2411369 = 1808527) B1808527
theorem B2411423 : Blo 1068616 2411423 := bstep (se 1 (by rfl) ⟨1808567, by rfl⟩ : syracuseStep 2411423 = 3617135) B3617135
theorem B7326683 : Blo 1068616 7326683 := bstep (se 1 (by rfl) ⟨5495012, by rfl⟩ : syracuseStep 7326683 = 10990025) B10990025
theorem B6179809 : Blo 1068616 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B5426351 : Blo 1068616 5426351 := bstep (se 1 (by rfl) ⟨4069763, by rfl⟩ : syracuseStep 5426351 = 8139527) B8139527
theorem B1526959 : Blo 1068616 1526959 := bstep (se 1 (by rfl) ⟨1145219, by rfl⟩ : syracuseStep 1526959 = 2290439) B2290439
theorem B10276145 : Blo 1068616 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B1068647 : Blo 1068616 1068647 := bstep (se 1 (by rfl) ⟨801485, by rfl⟩ : syracuseStep 1068647 = 1602971) B1602971
theorem B2575975 : Blo 1068616 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B1068795 : Blo 1068616 1068795 := bstep (se 1 (by rfl) ⟨801596, by rfl⟩ : syracuseStep 1068795 = 1603193) B1603193
theorem B5426999 : Blo 1068616 5426999 := bstep (se 1 (by rfl) ⟨4070249, by rfl⟩ : syracuseStep 5426999 = 8140499) B8140499
theorem B1068863 : Blo 1068616 1068863 := bstep (se 1 (by rfl) ⟨801647, by rfl⟩ : syracuseStep 1068863 = 1603295) B1603295
theorem B2412359 : Blo 1068616 2412359 := bstep (se 1 (by rfl) ⟨1809269, by rfl⟩ : syracuseStep 2412359 = 3618539) B3618539
theorem B1068927 : Blo 1068616 1068927 := bstep (se 1 (by rfl) ⟨801695, by rfl⟩ : syracuseStep 1068927 = 1603391) B1603391
theorem B2707415 : Blo 1068616 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B1069039 : Blo 1068616 1069039 := bstep (se 1 (by rfl) ⟨801779, by rfl⟩ : syracuseStep 1069039 = 1603559) B1603559
theorem B1069051 : Blo 1068616 1069051 := bstep (se 1 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 1069051 = 1603577) B1603577
theorem B2412539 : Blo 1068616 2412539 := bstep (se 1 (by rfl) ⟨1809404, by rfl⟩ : syracuseStep 2412539 = 3618809) B3618809
theorem B1069119 : Blo 1068616 1069119 := bstep (se 1 (by rfl) ⟨801839, by rfl⟩ : syracuseStep 1069119 = 1603679) B1603679
theorem B1069159 : Blo 1068616 1069159 := bstep (se 1 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 1069159 = 1603739) B1603739
theorem B2412647 : Blo 1068616 2412647 := bstep (se 1 (by rfl) ⟨1809485, by rfl⟩ : syracuseStep 2412647 = 3618971) B3618971
theorem B1069183 : Blo 1068616 1069183 := bstep (se 1 (by rfl) ⟨801887, by rfl⟩ : syracuseStep 1069183 = 1603775) B1603775
theorem B1069211 : Blo 1068616 1069211 := bstep (se 1 (by rfl) ⟨801908, by rfl⟩ : syracuseStep 1069211 = 1603817) B1603817
theorem B2412719 : Blo 1068616 2412719 := bstep (se 1 (by rfl) ⟨1809539, by rfl⟩ : syracuseStep 2412719 = 3619079) B3619079
theorem B5427485 : Blo 1068616 5427485 := bstep (se 3 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 5427485 = 2035307) B2035307
theorem B1069415 : Blo 1068616 1069415 := bstep (se 1 (by rfl) ⟨802061, by rfl⟩ : syracuseStep 1069415 = 1604123) B1604123
theorem B1069467 : Blo 1068616 1069467 := bstep (se 1 (by rfl) ⟨802100, by rfl⟩ : syracuseStep 1069467 = 1604201) B1604201
theorem B1069819 : Blo 1068616 1069819 := bstep (se 1 (by rfl) ⟨802364, by rfl⟩ : syracuseStep 1069819 = 1604729) B1604729
theorem B1069887 : Blo 1068616 1069887 := bstep (se 1 (by rfl) ⟨802415, by rfl⟩ : syracuseStep 1069887 = 1604831) B1604831
theorem B1069915 : Blo 1068616 1069915 := bstep (se 1 (by rfl) ⟨802436, by rfl⟩ : syracuseStep 1069915 = 1604873) B1604873
theorem B1069983 : Blo 1068616 1069983 := bstep (se 1 (by rfl) ⟨802487, by rfl⟩ : syracuseStep 1069983 = 1604975) B1604975
theorem B9130967 : Blo 1068616 9130967 := bstep (se 1 (by rfl) ⟨6848225, by rfl⟩ : syracuseStep 9130967 = 13696451) B13696451
theorem B1070063 : Blo 1068616 1070063 := bstep (se 1 (by rfl) ⟨802547, by rfl⟩ : syracuseStep 1070063 = 1605095) B1605095
theorem B43897859 : Blo 1068616 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B1070151 : Blo 1068616 1070151 := bstep (se 1 (by rfl) ⟨802613, by rfl⟩ : syracuseStep 1070151 = 1605227) B1605227
theorem B1070235 : Blo 1068616 1070235 := bstep (se 1 (by rfl) ⟨802676, by rfl⟩ : syracuseStep 1070235 = 1605353) B1605353
theorem B1070331 : Blo 1068616 1070331 := bstep (se 1 (by rfl) ⟨802748, by rfl⟩ : syracuseStep 1070331 = 1605497) B1605497
theorem B1070399 : Blo 1068616 1070399 := bstep (se 1 (by rfl) ⟨802799, by rfl⟩ : syracuseStep 1070399 = 1605599) B1605599
theorem B1070567 : Blo 1068616 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B1070575 : Blo 1068616 1070575 := bstep (se 1 (by rfl) ⟨802931, by rfl⟩ : syracuseStep 1070575 = 1605863) B1605863
theorem B7722479 : Blo 1068616 7722479 := bstep (se 1 (by rfl) ⟨5791859, by rfl⟩ : syracuseStep 7722479 = 11583719) B11583719
theorem B1070683 : Blo 1068616 1070683 := bstep (se 1 (by rfl) ⟨803012, by rfl⟩ : syracuseStep 1070683 = 1606025) B1606025
theorem B1070747 : Blo 1068616 1070747 := bstep (se 1 (by rfl) ⟨803060, by rfl⟩ : syracuseStep 1070747 = 1606121) B1606121
theorem B1070831 : Blo 1068616 1070831 := bstep (se 1 (by rfl) ⟨803123, by rfl⟩ : syracuseStep 1070831 = 1606247) B1606247
theorem B8673095 : Blo 1068616 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B1070919 : Blo 1068616 1070919 := bstep (se 1 (by rfl) ⟨803189, by rfl⟩ : syracuseStep 1070919 = 1606379) B1606379
theorem B1070939 : Blo 1068616 1070939 := bstep (se 1 (by rfl) ⟨803204, by rfl⟩ : syracuseStep 1070939 = 1606409) B1606409
theorem B1071007 : Blo 1068616 1071007 := bstep (se 1 (by rfl) ⟨803255, by rfl⟩ : syracuseStep 1071007 = 1606511) B1606511
theorem B12212207 : Blo 1068616 12212207 := bstep (se 1 (by rfl) ⟨9159155, by rfl⟩ : syracuseStep 12212207 = 18318311) B18318311
theorem B1071175 : Blo 1068616 1071175 := bstep (se 1 (by rfl) ⟨803381, by rfl⟩ : syracuseStep 1071175 = 1606763) B1606763
theorem B23189651 : Blo 1068616 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B1071335 : Blo 1068616 1071335 := bstep (se 1 (by rfl) ⟨803501, by rfl⟩ : syracuseStep 1071335 = 1607003) B1607003
theorem B18274571 : Blo 1068616 18274571 := bstep (se 1 (by rfl) ⟨13705928, by rfl⟩ : syracuseStep 18274571 = 27411857) B27411857
theorem B6510905 : Blo 1068616 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B23157049 : Blo 1068616 23157049 := bstep (se 2 (by rfl) ⟨8683893, by rfl⟩ : syracuseStep 23157049 = 17367787) B17367787
theorem B1071519 : Blo 1068616 1071519 := bstep (se 1 (by rfl) ⟨803639, by rfl⟩ : syracuseStep 1071519 = 1607279) B1607279
theorem B1071567 : Blo 1068616 1071567 := bstep (se 1 (by rfl) ⟨803675, by rfl⟩ : syracuseStep 1071567 = 1607351) B1607351
theorem B1071591 : Blo 1068616 1071591 := bstep (se 1 (by rfl) ⟨803693, by rfl⟩ : syracuseStep 1071591 = 1607387) B1607387
theorem B9755113 : Blo 1068616 9755113 := bstep (se 2 (by rfl) ⟨3658167, by rfl⟩ : syracuseStep 9755113 = 7316335) B7316335
theorem B1071707 : Blo 1068616 1071707 := bstep (se 1 (by rfl) ⟨803780, by rfl⟩ : syracuseStep 1071707 = 1607561) B1607561
theorem B6871675 : Blo 1068616 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B1071775 : Blo 1068616 1071775 := bstep (se 1 (by rfl) ⟨803831, by rfl⟩ : syracuseStep 1071775 = 1607663) B1607663
theorem B1071943 : Blo 1068616 1071943 := bstep (se 1 (by rfl) ⟨803957, by rfl⟩ : syracuseStep 1071943 = 1607915) B1607915
theorem B1071983 : Blo 1068616 1071983 := bstep (se 1 (by rfl) ⟨803987, by rfl⟩ : syracuseStep 1071983 = 1607975) B1607975
theorem B1072039 : Blo 1068616 1072039 := bstep (se 1 (by rfl) ⟨804029, by rfl⟩ : syracuseStep 1072039 = 1608059) B1608059
theorem B1072219 : Blo 1068616 1072219 := bstep (se 1 (by rfl) ⟨804164, by rfl⟩ : syracuseStep 1072219 = 1608329) B1608329
theorem B1072335 : Blo 1068616 1072335 := bstep (se 1 (by rfl) ⟨804251, by rfl⟩ : syracuseStep 1072335 = 1608503) B1608503
theorem B1072359 : Blo 1068616 1072359 := bstep (se 1 (by rfl) ⟨804269, by rfl⟩ : syracuseStep 1072359 = 1608539) B1608539
theorem B1072455 : Blo 1068616 1072455 := bstep (se 1 (by rfl) ⟨804341, by rfl⟩ : syracuseStep 1072455 = 1608683) B1608683
theorem B8117657 : Blo 1068616 8117657 := bstep (se 2 (by rfl) ⟨3044121, by rfl⟩ : syracuseStep 8117657 = 6088243) B6088243
theorem B1072591 : Blo 1068616 1072591 := bstep (se 1 (by rfl) ⟨804443, by rfl⟩ : syracuseStep 1072591 = 1608887) B1608887
theorem B1203943 : Blo 1068616 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B3432223 : Blo 1068616 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B4120475 : Blo 1068616 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B6348995 : Blo 1068616 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B7725563 : Blo 1068616 7725563 := bstep (se 1 (by rfl) ⟨5794172, by rfl⟩ : syracuseStep 7725563 = 11588345) B11588345
theorem B3301915 : Blo 1068616 3301915 := bstep (se 1 (by rfl) ⟨2476436, by rfl⟩ : syracuseStep 3301915 = 4952873) B4952873
theorem B1205023 : Blo 1068616 1205023 := bstep (se 1 (by rfl) ⟨903767, by rfl⟩ : syracuseStep 1205023 = 1807535) B1807535
theorem B2712649 : Blo 1068616 2712649 := bstep (se 2 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 2712649 = 2034487) B2034487
theorem B79193213 : Blo 1068616 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B2713115 : Blo 1068616 2713115 := bstep (se 1 (by rfl) ⟨2034836, by rfl⟩ : syracuseStep 2713115 = 4069673) B4069673
theorem B2287595 : Blo 1068616 2287595 := bstep (se 1 (by rfl) ⟨1715696, by rfl⟩ : syracuseStep 2287595 = 3431393) B3431393
theorem B4581355 : Blo 1068616 4581355 := bstep (se 1 (by rfl) ⟨3436016, by rfl⟩ : syracuseStep 4581355 = 6872033) B6872033
theorem B1206319 : Blo 1068616 1206319 := bstep (se 1 (by rfl) ⟨904739, by rfl⟩ : syracuseStep 1206319 = 1809479) B1809479
theorem B2287739 : Blo 1068616 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B9758873 : Blo 1068616 9758873 := bstep (se 2 (by rfl) ⟨3659577, by rfl⟩ : syracuseStep 9758873 = 7319155) B7319155
theorem B6514991 : Blo 1068616 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B1206607 : Blo 1068616 1206607 := bstep (se 1 (by rfl) ⟨904955, by rfl⟩ : syracuseStep 1206607 = 1809911) B1809911
theorem B18542479 : Blo 1068616 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B3043291 : Blo 1068616 3043291 := bstep (se 1 (by rfl) ⟨2282468, by rfl⟩ : syracuseStep 3043291 = 4564937) B4564937
theorem B8123003 : Blo 1068616 8123003 := bstep (se 1 (by rfl) ⟨6092252, by rfl⟩ : syracuseStep 8123003 = 12184505) B12184505
theorem B11727773 : Blo 1068616 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B46330865 : Blo 1068616 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B9270557 : Blo 1068616 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B1602983 : Blo 1068616 1602983 := bstep (se 1 (by rfl) ⟨1202237, by rfl⟩ : syracuseStep 1602983 = 2404475) B2404475
theorem B1603163 : Blo 1068616 1603163 := bstep (se 1 (by rfl) ⟨1202372, by rfl⟩ : syracuseStep 1603163 = 2404745) B2404745
theorem B1603625 : Blo 1068616 1603625 := bstep (se 2 (by rfl) ⟨601359, by rfl⟩ : syracuseStep 1603625 = 1202719) B1202719
theorem B1603655 : Blo 1068616 1603655 := bstep (se 1 (by rfl) ⟨1202741, by rfl⟩ : syracuseStep 1603655 = 2405483) B2405483
theorem B1604039 : Blo 1068616 1604039 := bstep (se 1 (by rfl) ⟨1203029, by rfl⟩ : syracuseStep 1604039 = 2406059) B2406059
theorem B1604255 : Blo 1068616 1604255 := bstep (se 1 (by rfl) ⟨1203191, by rfl⟩ : syracuseStep 1604255 = 2406383) B2406383
theorem B1604399 : Blo 1068616 1604399 := bstep (se 1 (by rfl) ⟨1203299, by rfl⟩ : syracuseStep 1604399 = 2406599) B2406599
theorem B4062109 : Blo 1068616 4062109 := bstep (se 3 (by rfl) ⟨761645, by rfl⟩ : syracuseStep 4062109 = 1523291) B1523291
theorem B1604519 : Blo 1068616 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B2030683 : Blo 1068616 2030683 := bstep (se 1 (by rfl) ⟨1523012, by rfl⟩ : syracuseStep 2030683 = 3046025) B3046025
theorem B1604699 : Blo 1068616 1604699 := bstep (se 1 (by rfl) ⟨1203524, by rfl⟩ : syracuseStep 1604699 = 2407049) B2407049
theorem B1605071 : Blo 1068616 1605071 := bstep (se 1 (by rfl) ⟨1203803, by rfl⟩ : syracuseStep 1605071 = 2407607) B2407607
theorem B39026285 : Blo 1068616 39026285 := bstep (se 3 (by rfl) ⟨7317428, by rfl⟩ : syracuseStep 39026285 = 14634857) B14634857
theorem B1605455 : Blo 1068616 1605455 := bstep (se 1 (by rfl) ⟨1204091, by rfl⟩ : syracuseStep 1605455 = 2408183) B2408183
theorem B3047311 : Blo 1068616 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B1605575 : Blo 1068616 1605575 := bstep (se 1 (by rfl) ⟨1204181, by rfl⟩ : syracuseStep 1605575 = 2408363) B2408363
theorem B2031571 : Blo 1068616 2031571 := bstep (se 1 (by rfl) ⟨1523678, by rfl⟩ : syracuseStep 2031571 = 3047357) B3047357
theorem B4063355 : Blo 1068616 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B1605887 : Blo 1068616 1605887 := bstep (se 1 (by rfl) ⟨1204415, by rfl⟩ : syracuseStep 1605887 = 2408831) B2408831
theorem B3047699 : Blo 1068616 3047699 := bstep (se 1 (by rfl) ⟨2285774, by rfl⟩ : syracuseStep 3047699 = 4571549) B4571549
theorem B1606043 : Blo 1068616 1606043 := bstep (se 1 (by rfl) ⟨1204532, by rfl⟩ : syracuseStep 1606043 = 2409065) B2409065
theorem B6685181 : Blo 1068616 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B1606463 : Blo 1068616 1606463 := bstep (se 1 (by rfl) ⟨1204847, by rfl⟩ : syracuseStep 1606463 = 2409695) B2409695
theorem B1606607 : Blo 1068616 1606607 := bstep (se 1 (by rfl) ⟨1204955, by rfl⟩ : syracuseStep 1606607 = 2409911) B2409911
theorem B1606697 : Blo 1068616 1606697 := bstep (se 2 (by rfl) ⟨602511, by rfl⟩ : syracuseStep 1606697 = 1205023) B1205023
theorem B1606727 : Blo 1068616 1606727 := bstep (se 1 (by rfl) ⟨1205045, by rfl⟩ : syracuseStep 1606727 = 2410091) B2410091
theorem B1606907 : Blo 1068616 1606907 := bstep (se 1 (by rfl) ⟨1205180, by rfl⟩ : syracuseStep 1606907 = 2410361) B2410361
theorem B13731353 : Blo 1068616 13731353 := bstep (se 2 (by rfl) ⟨5149257, by rfl⟩ : syracuseStep 13731353 = 10298515) B10298515
theorem B1607195 : Blo 1068616 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B1804187 : Blo 1068616 1804187 := bstep (se 1 (by rfl) ⟨1353140, by rfl⟩ : syracuseStep 1804187 = 2706281) B2706281
theorem B1607579 : Blo 1068616 1607579 := bstep (se 1 (by rfl) ⟨1205684, by rfl⟩ : syracuseStep 1607579 = 2411369) B2411369
theorem B2033599 : Blo 1068616 2033599 := bstep (se 1 (by rfl) ⟨1525199, by rfl⟩ : syracuseStep 2033599 = 3050399) B3050399
theorem B1607615 : Blo 1068616 1607615 := bstep (se 1 (by rfl) ⟨1205711, by rfl⟩ : syracuseStep 1607615 = 2411423) B2411423
theorem B3475415 : Blo 1068616 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B4884455 : Blo 1068616 4884455 := bstep (se 1 (by rfl) ⟨3663341, by rfl⟩ : syracuseStep 4884455 = 7326683) B7326683
theorem B12191795 : Blo 1068616 12191795 := bstep (se 1 (by rfl) ⟨9143846, by rfl⟩ : syracuseStep 12191795 = 18287693) B18287693
theorem B6850763 : Blo 1068616 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B1608239 : Blo 1068616 1608239 := bstep (se 1 (by rfl) ⟨1206179, by rfl⟩ : syracuseStep 1608239 = 2412359) B2412359
theorem B1804943 : Blo 1068616 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B3607199 : Blo 1068616 3607199 := bstep (se 1 (by rfl) ⟨2705399, by rfl⟩ : syracuseStep 3607199 = 5410799) B5410799
theorem B2034335 : Blo 1068616 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B1608359 : Blo 1068616 1608359 := bstep (se 1 (by rfl) ⟨1206269, by rfl⟩ : syracuseStep 1608359 = 2412539) B2412539
theorem B1608425 : Blo 1068616 1608425 := bstep (se 2 (by rfl) ⟨603159, by rfl⟩ : syracuseStep 1608425 = 1206319) B1206319
theorem B1608431 : Blo 1068616 1608431 := bstep (se 1 (by rfl) ⟨1206323, by rfl⟩ : syracuseStep 1608431 = 2412647) B2412647
theorem B1608479 : Blo 1068616 1608479 := bstep (se 1 (by rfl) ⟨1206359, by rfl⟩ : syracuseStep 1608479 = 2412719) B2412719
theorem B1608809 : Blo 1068616 1608809 := bstep (se 2 (by rfl) ⟨603303, by rfl⟩ : syracuseStep 1608809 = 1206607) B1206607
theorem B29265239 : Blo 1068616 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B13176379 : Blo 1068616 13176379 := bstep (se 1 (by rfl) ⟨9882284, by rfl⟩ : syracuseStep 13176379 = 19764569) B19764569
theorem B5148319 : Blo 1068616 5148319 := bstep (se 1 (by rfl) ⟨3861239, by rfl⟩ : syracuseStep 5148319 = 7722479) B7722479
theorem B27922249 : Blo 1068616 27922249 := bstep (se 2 (by rfl) ⟨10470843, by rfl⟩ : syracuseStep 27922249 = 20941687) B20941687
theorem B2035945 : Blo 1068616 2035945 := bstep (se 2 (by rfl) ⟨763479, by rfl⟩ : syracuseStep 2035945 = 1526959) B1526959
theorem B5411771 : Blo 1068616 5411771 := bstep (se 1 (by rfl) ⟨4058828, by rfl⟩ : syracuseStep 5411771 = 8117657) B8117657
theorem B4232663 : Blo 1068616 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B5150375 : Blo 1068616 5150375 := bstep (se 1 (by rfl) ⟨3862781, by rfl⟩ : syracuseStep 5150375 = 7725563) B7725563
theorem B13735817 : Blo 1068616 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B3610655 : Blo 1068616 3610655 := bstep (se 1 (by rfl) ⟨2707991, by rfl⟩ : syracuseStep 3610655 = 5415983) B5415983
theorem B52795475 : Blo 1068616 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B12196169 : Blo 1068616 12196169 := bstep (se 2 (by rfl) ⟨4573563, by rfl⟩ : syracuseStep 12196169 = 9147127) B9147127
theorem B1808743 : Blo 1068616 1808743 := bstep (se 1 (by rfl) ⟨1356557, by rfl⟩ : syracuseStep 1808743 = 2713115) B2713115
theorem B3611087 : Blo 1068616 3611087 := bstep (se 1 (by rfl) ⟨2708315, by rfl⟩ : syracuseStep 3611087 = 5416631) B5416631
theorem B3087805 : Blo 1068616 3087805 := bstep (se 3 (by rfl) ⟨578963, by rfl⟩ : syracuseStep 3087805 = 1157927) B1157927
theorem B30876065 : Blo 1068616 30876065 := bstep (se 2 (by rfl) ⟨11578524, by rfl⟩ : syracuseStep 30876065 = 23157049) B23157049
theorem B5415335 : Blo 1068616 5415335 := bstep (se 1 (by rfl) ⟨4061501, by rfl⟩ : syracuseStep 5415335 = 8123003) B8123003
theorem B5416145 : Blo 1068616 5416145 := bstep (se 2 (by rfl) ⟨2031054, by rfl⟩ : syracuseStep 5416145 = 4062109) B4062109
theorem B3613949 : Blo 1068616 3613949 := bstep (se 3 (by rfl) ⟨677615, by rfl⟩ : syracuseStep 3613949 = 1355231) B1355231
theorem B4335215 : Blo 1068616 4335215 := bstep (se 1 (by rfl) ⟨3251411, by rfl⟩ : syracuseStep 4335215 = 6502823) B6502823
theorem B11577181 : Blo 1068616 11577181 := bstep (se 3 (by rfl) ⟨2170721, by rfl⟩ : syracuseStep 11577181 = 4341443) B4341443
theorem B4401535 : Blo 1068616 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B10987933 : Blo 1068616 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B8137583 : Blo 1068616 8137583 := bstep (se 1 (by rfl) ⟨6103187, by rfl⟩ : syracuseStep 8137583 = 12206375) B12206375
theorem B5417927 : Blo 1068616 5417927 := bstep (se 1 (by rfl) ⟨4063445, by rfl⟩ : syracuseStep 5417927 = 8126891) B8126891
theorem B25046003 : Blo 1068616 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B7711955 : Blo 1068616 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B4402553 : Blo 1068616 4402553 := bstep (se 2 (by rfl) ⟨1650957, by rfl⟩ : syracuseStep 4402553 = 3301915) B3301915
theorem B2895335 : Blo 1068616 2895335 := bstep (se 1 (by rfl) ⟨2171501, by rfl⟩ : syracuseStep 2895335 = 4343003) B4343003
theorem B4337489 : Blo 1068616 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B3616865 : Blo 1068616 3616865 := bstep (se 2 (by rfl) ⟨1356324, by rfl⟩ : syracuseStep 3616865 = 2712649) B2712649
theorem B1355879 : Blo 1068616 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B1356031 : Blo 1068616 1356031 := bstep (se 1 (by rfl) ⟨1017023, by rfl⟩ : syracuseStep 1356031 = 2034047) B2034047
theorem B3617567 : Blo 1068616 3617567 := bstep (se 1 (by rfl) ⟨2713175, by rfl⟩ : syracuseStep 3617567 = 5426351) B5426351
theorem B2405159 : Blo 1068616 2405159 := bstep (se 1 (by rfl) ⟨1803869, by rfl⟩ : syracuseStep 2405159 = 3607739) B3607739
theorem B1356583 : Blo 1068616 1356583 := bstep (se 1 (by rfl) ⟨1017437, by rfl⟩ : syracuseStep 1356583 = 2034875) B2034875
theorem B2405177 : Blo 1068616 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B2405537 : Blo 1068616 2405537 := bstep (se 2 (by rfl) ⟨902076, by rfl⟩ : syracuseStep 2405537 = 1804153) B1804153
theorem B3617999 : Blo 1068616 3617999 := bstep (se 1 (by rfl) ⟨2713499, by rfl⟩ : syracuseStep 3617999 = 5426999) B5426999
theorem B6108473 : Blo 1068616 6108473 := bstep (se 2 (by rfl) ⟨2290677, by rfl⟩ : syracuseStep 6108473 = 4581355) B4581355
theorem B2405807 : Blo 1068616 2405807 := bstep (se 1 (by rfl) ⟨1804355, by rfl⟩ : syracuseStep 2405807 = 3608711) B3608711
theorem B3618323 : Blo 1068616 3618323 := bstep (se 1 (by rfl) ⟨2713742, by rfl⟩ : syracuseStep 3618323 = 5427485) B5427485
theorem B2405915 : Blo 1068616 2405915 := bstep (se 1 (by rfl) ⟨1804436, by rfl⟩ : syracuseStep 2405915 = 3608873) B3608873
theorem B2406095 : Blo 1068616 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B18265823 : Blo 1068616 18265823 := bstep (se 1 (by rfl) ⟨13699367, by rfl⟩ : syracuseStep 18265823 = 27398735) B27398735
theorem B8140985 : Blo 1068616 8140985 := bstep (se 2 (by rfl) ⟨3052869, by rfl⟩ : syracuseStep 8140985 = 6105739) B6105739
theorem B8239319 : Blo 1068616 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B4569463 : Blo 1068616 4569463 := bstep (se 1 (by rfl) ⟨3427097, by rfl⟩ : syracuseStep 4569463 = 6854195) B6854195
theorem B2406887 : Blo 1068616 2406887 := bstep (se 1 (by rfl) ⟨1805165, by rfl⟩ : syracuseStep 2406887 = 3610331) B3610331
theorem B5782063 : Blo 1068616 5782063 := bstep (se 1 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 5782063 = 8673095) B8673095
theorem B8239745 : Blo 1068616 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B8141471 : Blo 1068616 8141471 := bstep (se 1 (by rfl) ⟨6106103, by rfl⟩ : syracuseStep 8141471 = 12212207) B12212207
theorem B4340603 : Blo 1068616 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B5422139 : Blo 1068616 5422139 := bstep (se 1 (by rfl) ⟨4066604, by rfl⟩ : syracuseStep 5422139 = 8133209) B8133209
theorem B21937513 : Blo 1068616 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B13909553 : Blo 1068616 13909553 := bstep (se 2 (by rfl) ⟨5216082, by rfl⟩ : syracuseStep 13909553 = 10432165) B10432165
theorem B3423817 : Blo 1068616 3423817 := bstep (se 2 (by rfl) ⟨1283931, by rfl⟩ : syracuseStep 3423817 = 2567863) B2567863
theorem B24723305 : Blo 1068616 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B5357789 : Blo 1068616 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B5784137 : Blo 1068616 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B8667901 : Blo 1068616 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B8143901 : Blo 1068616 8143901 := bstep (se 3 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 8143901 = 3053963) B3053963
theorem B3425561 : Blo 1068616 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B1525063 : Blo 1068616 1525063 := bstep (se 1 (by rfl) ⟨1143797, by rfl⟩ : syracuseStep 1525063 = 2287595) B2287595
theorem B1525159 : Blo 1068616 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B6505915 : Blo 1068616 6505915 := bstep (se 1 (by rfl) ⟨4879436, by rfl⟩ : syracuseStep 6505915 = 9758873) B9758873
theorem B4343327 : Blo 1068616 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B2410523 : Blo 1068616 2410523 := bstep (se 1 (by rfl) ⟨1807892, by rfl⟩ : syracuseStep 2410523 = 3615785) B3615785
theorem B2410703 : Blo 1068616 2410703 := bstep (se 1 (by rfl) ⟨1808027, by rfl⟩ : syracuseStep 2410703 = 3616055) B3616055
theorem B2411099 : Blo 1068616 2411099 := bstep (se 1 (by rfl) ⟨1808324, by rfl⟩ : syracuseStep 2411099 = 3616649) B3616649
theorem B7818515 : Blo 1068616 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B30887243 : Blo 1068616 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B29248937 : Blo 1068616 29248937 := bstep (se 2 (by rfl) ⟨10968351, by rfl⟩ : syracuseStep 29248937 = 21936703) B21936703
theorem B22269431 : Blo 1068616 22269431 := bstep (se 1 (by rfl) ⟨16702073, by rfl⟩ : syracuseStep 22269431 = 33404147) B33404147
theorem B9162233 : Blo 1068616 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B6180371 : Blo 1068616 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B3296809 : Blo 1068616 3296809 := bstep (se 2 (by rfl) ⟨1236303, by rfl⟩ : syracuseStep 3296809 = 2472607) B2472607
theorem B1068655 : Blo 1068616 1068655 := bstep (se 1 (by rfl) ⟨801491, by rfl⟩ : syracuseStep 1068655 = 1602983) B1602983
theorem B1068775 : Blo 1068616 1068775 := bstep (se 1 (by rfl) ⟨801581, by rfl⟩ : syracuseStep 1068775 = 1603163) B1603163
theorem B1069083 : Blo 1068616 1069083 := bstep (se 1 (by rfl) ⟨801812, by rfl⟩ : syracuseStep 1069083 = 1603625) B1603625
theorem B1069103 : Blo 1068616 1069103 := bstep (se 1 (by rfl) ⟨801827, by rfl⟩ : syracuseStep 1069103 = 1603655) B1603655
theorem B2707577 : Blo 1068616 2707577 := bstep (se 2 (by rfl) ⟨1015341, by rfl⟩ : syracuseStep 2707577 = 2030683) B2030683
theorem B18305189 : Blo 1068616 18305189 := bstep (se 4 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 18305189 = 3432223) B3432223
theorem B1069359 : Blo 1068616 1069359 := bstep (se 1 (by rfl) ⟨802019, by rfl⟩ : syracuseStep 1069359 = 1604039) B1604039
theorem B1069503 : Blo 1068616 1069503 := bstep (se 1 (by rfl) ⟨802127, by rfl⟩ : syracuseStep 1069503 = 1604255) B1604255
theorem B1069599 : Blo 1068616 1069599 := bstep (se 1 (by rfl) ⟨802199, by rfl⟩ : syracuseStep 1069599 = 1604399) B1604399
theorem B1069679 : Blo 1068616 1069679 := bstep (se 1 (by rfl) ⟨802259, by rfl⟩ : syracuseStep 1069679 = 1604519) B1604519
theorem B1069799 : Blo 1068616 1069799 := bstep (se 1 (by rfl) ⟨802349, by rfl⟩ : syracuseStep 1069799 = 1604699) B1604699
theorem B1070047 : Blo 1068616 1070047 := bstep (se 1 (by rfl) ⟨802535, by rfl⟩ : syracuseStep 1070047 = 1605071) B1605071
theorem B5428295 : Blo 1068616 5428295 := bstep (se 1 (by rfl) ⟨4071221, by rfl⟩ : syracuseStep 5428295 = 8142443) B8142443
theorem B1070303 : Blo 1068616 1070303 := bstep (se 1 (by rfl) ⟨802727, by rfl⟩ : syracuseStep 1070303 = 1605455) B1605455
theorem B2708761 : Blo 1068616 2708761 := bstep (se 2 (by rfl) ⟨1015785, by rfl⟩ : syracuseStep 2708761 = 2031571) B2031571
theorem B1070383 : Blo 1068616 1070383 := bstep (se 1 (by rfl) ⟨802787, by rfl⟩ : syracuseStep 1070383 = 1605575) B1605575
theorem B3528047 : Blo 1068616 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B1070623 : Blo 1068616 1070623 := bstep (se 1 (by rfl) ⟨802967, by rfl⟩ : syracuseStep 1070623 = 1605935) B1605935
theorem B1070783 : Blo 1068616 1070783 := bstep (se 1 (by rfl) ⟨803087, by rfl⟩ : syracuseStep 1070783 = 1606175) B1606175
theorem B10442459 : Blo 1068616 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B16734035 : Blo 1068616 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B1071231 : Blo 1068616 1071231 := bstep (se 1 (by rfl) ⟨803423, by rfl⟩ : syracuseStep 1071231 = 1606847) B1606847
theorem B11557079 : Blo 1068616 11557079 := bstep (se 1 (by rfl) ⟨8667809, by rfl⟩ : syracuseStep 11557079 = 17335619) B17335619
theorem B1071327 : Blo 1068616 1071327 := bstep (se 1 (by rfl) ⟨803495, by rfl⟩ : syracuseStep 1071327 = 1606991) B1606991
theorem B1071387 : Blo 1068616 1071387 := bstep (se 1 (by rfl) ⟨803540, by rfl⟩ : syracuseStep 1071387 = 1607081) B1607081
theorem B1071487 : Blo 1068616 1071487 := bstep (se 1 (by rfl) ⟨803615, by rfl⟩ : syracuseStep 1071487 = 1607231) B1607231
theorem B1071515 : Blo 1068616 1071515 := bstep (se 1 (by rfl) ⟨803636, by rfl⟩ : syracuseStep 1071515 = 1607273) B1607273
theorem B1071807 : Blo 1068616 1071807 := bstep (se 1 (by rfl) ⟨803855, by rfl⟩ : syracuseStep 1071807 = 1607711) B1607711
theorem B4578059 : Blo 1068616 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B5430077 : Blo 1068616 5430077 := bstep (se 3 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 5430077 = 2036279) B2036279
theorem B1203007 : Blo 1068616 1203007 := bstep (se 1 (by rfl) ⟨902255, by rfl⟩ : syracuseStep 1203007 = 1804511) B1804511
theorem B1071935 : Blo 1068616 1071935 := bstep (se 1 (by rfl) ⟨803951, by rfl⟩ : syracuseStep 1071935 = 1607903) B1607903
theorem B1071975 : Blo 1068616 1071975 := bstep (se 1 (by rfl) ⟨803981, by rfl⟩ : syracuseStep 1071975 = 1607963) B1607963
theorem B1301567 : Blo 1068616 1301567 := bstep (se 1 (by rfl) ⟨976175, by rfl⟩ : syracuseStep 1301567 = 1952351) B1952351
theorem B1072191 : Blo 1068616 1072191 := bstep (se 1 (by rfl) ⟨804143, by rfl⟩ : syracuseStep 1072191 = 1608287) B1608287
theorem B1072379 : Blo 1068616 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B1072411 : Blo 1068616 1072411 := bstep (se 1 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 1072411 = 1608617) B1608617
theorem B1203583 : Blo 1068616 1203583 := bstep (se 1 (by rfl) ⟨902687, by rfl⟩ : syracuseStep 1203583 = 1805375) B1805375
theorem B1072511 : Blo 1068616 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B2711009 : Blo 1068616 2711009 := bstep (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) B2033257
theorem B6087311 : Blo 1068616 6087311 := bstep (se 1 (by rfl) ⟨4565483, by rfl⟩ : syracuseStep 6087311 = 9130967) B9130967
theorem B13001957 : Blo 1068616 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B2712811 : Blo 1068616 2712811 := bstep (se 1 (by rfl) ⟨2034608, by rfl⟩ : syracuseStep 2712811 = 4069217) B4069217
theorem B15459767 : Blo 1068616 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B12183047 : Blo 1068616 12183047 := bstep (se 1 (by rfl) ⟨9137285, by rfl⟩ : syracuseStep 12183047 = 18274571) B18274571
theorem B1206139 : Blo 1068616 1206139 := bstep (se 1 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 1206139 = 1809209) B1809209
theorem B1206175 : Blo 1068616 1206175 := bstep (se 1 (by rfl) ⟨904631, by rfl⟩ : syracuseStep 1206175 = 1809263) B1809263
theorem B13723667 : Blo 1068616 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B198010979 : Blo 1068616 198010979 := bstep (se 1 (by rfl) ⟨148508234, by rfl⟩ : syracuseStep 198010979 = 297016469) B297016469
theorem B3434633 : Blo 1068616 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B2714087 : Blo 1068616 2714087 := bstep (se 1 (by rfl) ⟨2035565, by rfl⟩ : syracuseStep 2714087 = 4071131) B4071131
theorem B4057721 : Blo 1068616 4057721 := bstep (se 2 (by rfl) ⟨1521645, by rfl⟩ : syracuseStep 4057721 = 3043291) B3043291
theorem B2714249 : Blo 1068616 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B2061167 : Blo 1068616 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1603055 : Blo 1068616 1603055 := bstep (se 1 (by rfl) ⟨1202291, by rfl⟩ : syracuseStep 1603055 = 2404583) B2404583
theorem B1603175 : Blo 1068616 1603175 := bstep (se 1 (by rfl) ⟨1202381, by rfl⟩ : syracuseStep 1603175 = 2404763) B2404763
theorem B13006817 : Blo 1068616 13006817 := bstep (se 2 (by rfl) ⟨4877556, by rfl⟩ : syracuseStep 13006817 = 9755113) B9755113
theorem B1603631 : Blo 1068616 1603631 := bstep (se 1 (by rfl) ⟨1202723, by rfl⟩ : syracuseStep 1603631 = 2405447) B2405447
theorem B1603751 : Blo 1068616 1603751 := bstep (se 1 (by rfl) ⟨1202813, by rfl⟩ : syracuseStep 1603751 = 2405627) B2405627
theorem B3045671 : Blo 1068616 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B1603895 : Blo 1068616 1603895 := bstep (se 1 (by rfl) ⟨1202921, by rfl⟩ : syracuseStep 1603895 = 2405843) B2405843
theorem B1604075 : Blo 1068616 1604075 := bstep (se 1 (by rfl) ⟨1203056, by rfl⟩ : syracuseStep 1604075 = 2406113) B2406113
theorem B1604423 : Blo 1068616 1604423 := bstep (se 1 (by rfl) ⟨1203317, by rfl⟩ : syracuseStep 1604423 = 2406635) B2406635
theorem B5143915 : Blo 1068616 5143915 := bstep (se 1 (by rfl) ⟨3857936, by rfl⟩ : syracuseStep 5143915 = 7715873) B7715873
theorem B1605257 : Blo 1068616 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B1605287 : Blo 1068616 1605287 := bstep (se 1 (by rfl) ⟨1203965, by rfl⟩ : syracuseStep 1605287 = 2407931) B2407931
theorem B26017523 : Blo 1068616 26017523 := bstep (se 1 (by rfl) ⟨19513142, by rfl⟩ : syracuseStep 26017523 = 39026285) B39026285
theorem B6094601 : Blo 1068616 6094601 := bstep (se 2 (by rfl) ⟨2285475, by rfl⟩ : syracuseStep 6094601 = 4570951) B4570951
theorem B1605407 : Blo 1068616 1605407 := bstep (se 1 (by rfl) ⟨1204055, by rfl⟩ : syracuseStep 1605407 = 2408111) B2408111
theorem B1605467 : Blo 1068616 1605467 := bstep (se 1 (by rfl) ⟨1204100, by rfl⟩ : syracuseStep 1605467 = 2408201) B2408201
theorem B4063081 : Blo 1068616 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B3571859 : Blo 1068616 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B2031799 : Blo 1068616 2031799 := bstep (se 1 (by rfl) ⟨1523849, by rfl⟩ : syracuseStep 2031799 = 3047699) B3047699
theorem B4456787 : Blo 1068616 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B1607015 : Blo 1068616 1607015 := bstep (se 1 (by rfl) ⟨1205261, by rfl⟩ : syracuseStep 1607015 = 2410523) B2410523
theorem B8127863 : Blo 1068616 8127863 := bstep (se 1 (by rfl) ⟨6095897, by rfl⟩ : syracuseStep 8127863 = 12191795) B12191795
theorem B1607135 : Blo 1068616 1607135 := bstep (se 1 (by rfl) ⟨1205351, by rfl⟩ : syracuseStep 1607135 = 2410703) B2410703
theorem B1607399 : Blo 1068616 1607399 := bstep (se 1 (by rfl) ⟨1205549, by rfl⟩ : syracuseStep 1607399 = 2411099) B2411099
theorem B2033417 : Blo 1068616 2033417 := bstep (se 2 (by rfl) ⟨762531, by rfl⟩ : syracuseStep 2033417 = 1525063) B1525063
theorem B5212343 : Blo 1068616 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B19499291 : Blo 1068616 19499291 := bstep (se 1 (by rfl) ⟨14624468, by rfl⟩ : syracuseStep 19499291 = 29248937) B29248937
theorem B14846287 : Blo 1068616 14846287 := bstep (se 1 (by rfl) ⟨11134715, by rfl⟩ : syracuseStep 14846287 = 22269431) B22269431
theorem B15436241 : Blo 1068616 15436241 := bstep (se 2 (by rfl) ⟨5788590, by rfl⟩ : syracuseStep 15436241 = 11577181) B11577181
theorem B1608185 : Blo 1068616 1608185 := bstep (se 2 (by rfl) ⟨603069, by rfl⟩ : syracuseStep 1608185 = 1206139) B1206139
theorem B1608233 : Blo 1068616 1608233 := bstep (se 2 (by rfl) ⟨603087, by rfl⟩ : syracuseStep 1608233 = 1206175) B1206175
theorem B1805051 : Blo 1068616 1805051 := bstep (se 1 (by rfl) ⟨1353788, by rfl⟩ : syracuseStep 1805051 = 2707577) B2707577
theorem B5868713 : Blo 1068616 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B14650577 : Blo 1068616 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B3607847 : Blo 1068616 3607847 := bstep (se 1 (by rfl) ⟨2705885, by rfl⟩ : syracuseStep 3607847 = 5411771) B5411771
theorem B9408125 : Blo 1068616 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B2821775 : Blo 1068616 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B35196983 : Blo 1068616 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B7704719 : Blo 1068616 7704719 := bstep (se 1 (by rfl) ⟨5778539, by rfl⟩ : syracuseStep 7704719 = 11557079) B11557079
theorem B8130779 : Blo 1068616 8130779 := bstep (se 1 (by rfl) ⟨6098084, by rfl⟩ : syracuseStep 8130779 = 12196169) B12196169
theorem B3052039 : Blo 1068616 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B4395745 : Blo 1068616 4395745 := bstep (se 2 (by rfl) ⟨1648404, by rfl⟩ : syracuseStep 4395745 = 3296809) B3296809
theorem B17568505 : Blo 1068616 17568505 := bstep (se 2 (by rfl) ⟨6588189, by rfl⟩ : syracuseStep 17568505 = 13176379) B13176379
theorem B1807339 : Blo 1068616 1807339 := bstep (se 1 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 1807339 = 2711009) B2711009
theorem B37229665 : Blo 1068616 37229665 := bstep (se 2 (by rfl) ⟨13961124, by rfl⟩ : syracuseStep 37229665 = 27922249) B27922249
theorem B20584043 : Blo 1068616 20584043 := bstep (se 1 (by rfl) ⟨15438032, by rfl⟩ : syracuseStep 20584043 = 30876065) B30876065
theorem B3610223 : Blo 1068616 3610223 := bstep (se 1 (by rfl) ⟨2707667, by rfl⟩ : syracuseStep 3610223 = 5415335) B5415335
theorem B1808041 : Blo 1068616 1808041 := bstep (se 2 (by rfl) ⟨678015, by rfl⟩ : syracuseStep 1808041 = 1356031) B1356031
theorem B3610763 : Blo 1068616 3610763 := bstep (se 1 (by rfl) ⟨2708072, by rfl⟩ : syracuseStep 3610763 = 5416145) B5416145
theorem B1808777 : Blo 1068616 1808777 := bstep (se 2 (by rfl) ⟨678291, by rfl⟩ : syracuseStep 1808777 = 1356583) B1356583
theorem B9149111 : Blo 1068616 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B1809391 : Blo 1068616 1809391 := bstep (se 1 (by rfl) ⟨1357043, by rfl⟩ : syracuseStep 1809391 = 2714087) B2714087
theorem B3611681 : Blo 1068616 3611681 := bstep (se 2 (by rfl) ⟨1354380, by rfl⟩ : syracuseStep 3611681 = 2708761) B2708761
theorem B1809499 : Blo 1068616 1809499 := bstep (se 1 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 1809499 = 2714249) B2714249
theorem B3611951 : Blo 1068616 3611951 := bstep (se 1 (by rfl) ⟨2708963, by rfl⟩ : syracuseStep 3611951 = 5417927) B5417927
theorem B8134181 : Blo 1068616 8134181 := bstep (se 4 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 8134181 = 1525159) B1525159
theorem B2891659 : Blo 1068616 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B7709417 : Blo 1068616 7709417 := bstep (se 2 (by rfl) ⟨2891031, by rfl⟩ : syracuseStep 7709417 = 5782063) B5782063
theorem B4072315 : Blo 1068616 4072315 := bstep (se 1 (by rfl) ⟨3054236, by rfl⟩ : syracuseStep 4072315 = 6108473) B6108473
theorem B11740141 : Blo 1068616 11740141 := bstep (se 3 (by rfl) ⟨2201276, by rfl⟩ : syracuseStep 11740141 = 4402553) B4402553
theorem B6858553 : Blo 1068616 6858553 := bstep (se 2 (by rfl) ⟨2571957, by rfl⟩ : syracuseStep 6858553 = 5143915) B5143915
theorem B2893735 : Blo 1068616 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B3614759 : Blo 1068616 3614759 := bstep (se 1 (by rfl) ⟨2711069, by rfl⟩ : syracuseStep 3614759 = 5422139) B5422139
theorem B4565089 : Blo 1068616 4565089 := bstep (se 2 (by rfl) ⟨1711908, by rfl⟩ : syracuseStep 4565089 = 3423817) B3423817
theorem B5417441 : Blo 1068616 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B17345015 : Blo 1068616 17345015 := bstep (se 1 (by rfl) ⟨13008761, by rfl⟩ : syracuseStep 17345015 = 26017523) B26017523
theorem B3615677 : Blo 1068616 3615677 := bstep (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) B1355879
theorem B9154235 : Blo 1068616 9154235 := bstep (se 1 (by rfl) ⟨6865676, by rfl⟩ : syracuseStep 9154235 = 13731353) B13731353
theorem B2895551 : Blo 1068616 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B3256303 : Blo 1068616 3256303 := bstep (se 1 (by rfl) ⟨2442227, by rfl⟩ : syracuseStep 3256303 = 4884455) B4884455
theorem B4567175 : Blo 1068616 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B3617081 : Blo 1068616 3617081 := bstep (se 2 (by rfl) ⟨1356405, by rfl⟩ : syracuseStep 3617081 = 2712811) B2712811
theorem B2404799 : Blo 1068616 2404799 := bstep (se 1 (by rfl) ⟨1803599, by rfl⟩ : syracuseStep 2404799 = 3607199) B3607199
theorem B20591495 : Blo 1068616 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B19510159 : Blo 1068616 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B6108155 : Blo 1068616 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B12203459 : Blo 1068616 12203459 := bstep (se 1 (by rfl) ⟨9152594, by rfl⟩ : syracuseStep 12203459 = 18305189) B18305189
theorem B3618863 : Blo 1068616 3618863 := bstep (se 1 (by rfl) ⟨2714147, by rfl⟩ : syracuseStep 3618863 = 5428295) B5428295
theorem B6961639 : Blo 1068616 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B11156023 : Blo 1068616 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B9157211 : Blo 1068616 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B2407103 : Blo 1068616 2407103 := bstep (se 1 (by rfl) ⟨1805327, by rfl⟩ : syracuseStep 2407103 = 3610655) B3610655
theorem B2407391 : Blo 1068616 2407391 := bstep (se 1 (by rfl) ⟨1805543, by rfl⟩ : syracuseStep 2407391 = 3611087) B3611087
theorem B3620051 : Blo 1068616 3620051 := bstep (se 1 (by rfl) ⟨2715038, by rfl⟩ : syracuseStep 3620051 = 5430077) B5430077
theorem B6864425 : Blo 1068616 6864425 := bstep (se 2 (by rfl) ⟨2574159, by rfl⟩ : syracuseStep 6864425 = 5148319) B5148319
theorem B8667971 : Blo 1068616 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B2409299 : Blo 1068616 2409299 := bstep (se 1 (by rfl) ⟨1806974, by rfl⟩ : syracuseStep 2409299 = 3613949) B3613949
theorem B10306511 : Blo 1068616 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B132007319 : Blo 1068616 132007319 := bstep (se 1 (by rfl) ⟨99005489, by rfl⟩ : syracuseStep 132007319 = 198010979) B198010979
theorem B21972653 : Blo 1068616 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B2705147 : Blo 1068616 2705147 := bstep (se 1 (by rfl) ⟨2028860, by rfl⟩ : syracuseStep 2705147 = 4057721) B4057721
theorem B5424893 : Blo 1068616 5424893 := bstep (se 3 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 5424893 = 2034335) B2034335
theorem B5425055 : Blo 1068616 5425055 := bstep (se 1 (by rfl) ⟨4068791, by rfl⟩ : syracuseStep 5425055 = 8137583) B8137583
theorem B16697335 : Blo 1068616 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B2411243 : Blo 1068616 2411243 := bstep (se 1 (by rfl) ⟨1808432, by rfl⟩ : syracuseStep 2411243 = 3616865) B3616865
theorem B2411657 : Blo 1068616 2411657 := bstep (se 2 (by rfl) ⟨904371, by rfl⟩ : syracuseStep 2411657 = 1808743) B1808743
theorem B2411711 : Blo 1068616 2411711 := bstep (se 1 (by rfl) ⟨1808783, by rfl⟩ : syracuseStep 2411711 = 3617567) B3617567
theorem B2411999 : Blo 1068616 2411999 := bstep (se 1 (by rfl) ⟨1808999, by rfl⟩ : syracuseStep 2411999 = 3617999) B3617999
theorem B1068703 : Blo 1068616 1068703 := bstep (se 1 (by rfl) ⟨801527, by rfl⟩ : syracuseStep 1068703 = 1603055) B1603055
theorem B2412215 : Blo 1068616 2412215 := bstep (se 1 (by rfl) ⟨1809161, by rfl⟩ : syracuseStep 2412215 = 3618323) B3618323
theorem B1068783 : Blo 1068616 1068783 := bstep (se 1 (by rfl) ⟨801587, by rfl⟩ : syracuseStep 1068783 = 1603175) B1603175
theorem B12177215 : Blo 1068616 12177215 := bstep (se 1 (by rfl) ⟨9132911, by rfl⟩ : syracuseStep 12177215 = 18265823) B18265823
theorem B8671211 : Blo 1068616 8671211 := bstep (se 1 (by rfl) ⟨6503408, by rfl⟩ : syracuseStep 8671211 = 13006817) B13006817
theorem B1069087 : Blo 1068616 1069087 := bstep (se 1 (by rfl) ⟨801815, by rfl⟩ : syracuseStep 1069087 = 1603631) B1603631
theorem B1069167 : Blo 1068616 1069167 := bstep (se 1 (by rfl) ⟨801875, by rfl⟩ : syracuseStep 1069167 = 1603751) B1603751
theorem B5427323 : Blo 1068616 5427323 := bstep (se 1 (by rfl) ⟨4070492, by rfl⟩ : syracuseStep 5427323 = 8140985) B8140985
theorem B5492879 : Blo 1068616 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B1069263 : Blo 1068616 1069263 := bstep (se 1 (by rfl) ⟨801947, by rfl⟩ : syracuseStep 1069263 = 1603895) B1603895
theorem B1069383 : Blo 1068616 1069383 := bstep (se 1 (by rfl) ⟨802037, by rfl⟩ : syracuseStep 1069383 = 1604075) B1604075
theorem B5427647 : Blo 1068616 5427647 := bstep (se 1 (by rfl) ⟨4070735, by rfl⟩ : syracuseStep 5427647 = 8141471) B8141471
theorem B29250017 : Blo 1068616 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B1069615 : Blo 1068616 1069615 := bstep (se 1 (by rfl) ⟨802211, by rfl⟩ : syracuseStep 1069615 = 1604423) B1604423
theorem B4117073 : Blo 1068616 4117073 := bstep (se 2 (by rfl) ⟨1543902, by rfl⟩ : syracuseStep 4117073 = 3087805) B3087805
theorem B1070171 : Blo 1068616 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B1070191 : Blo 1068616 1070191 := bstep (se 1 (by rfl) ⟨802643, by rfl⟩ : syracuseStep 1070191 = 1605287) B1605287
theorem B1070271 : Blo 1068616 1070271 := bstep (se 1 (by rfl) ⟨802703, by rfl⟩ : syracuseStep 1070271 = 1605407) B1605407
theorem B1070311 : Blo 1068616 1070311 := bstep (se 1 (by rfl) ⟨802733, by rfl⟩ : syracuseStep 1070311 = 1605467) B1605467
theorem B2708903 : Blo 1068616 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B1070591 : Blo 1068616 1070591 := bstep (se 1 (by rfl) ⟨802943, by rfl⟩ : syracuseStep 1070591 = 1605887) B1605887
theorem B1070695 : Blo 1068616 1070695 := bstep (se 1 (by rfl) ⟨803021, by rfl⟩ : syracuseStep 1070695 = 1606043) B1606043
theorem B3856091 : Blo 1068616 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B1070975 : Blo 1068616 1070975 := bstep (se 1 (by rfl) ⟨803231, by rfl⟩ : syracuseStep 1070975 = 1606463) B1606463
theorem B1071071 : Blo 1068616 1071071 := bstep (se 1 (by rfl) ⟨803303, by rfl⟩ : syracuseStep 1071071 = 1606607) B1606607
theorem B5429267 : Blo 1068616 5429267 := bstep (se 1 (by rfl) ⟨4071950, by rfl⟩ : syracuseStep 5429267 = 8143901) B8143901
theorem B1071131 : Blo 1068616 1071131 := bstep (se 1 (by rfl) ⟨803348, by rfl⟩ : syracuseStep 1071131 = 1606697) B1606697
theorem B1071151 : Blo 1068616 1071151 := bstep (se 1 (by rfl) ⟨803363, by rfl⟩ : syracuseStep 1071151 = 1606727) B1606727
theorem B1071271 : Blo 1068616 1071271 := bstep (se 1 (by rfl) ⟨803453, by rfl⟩ : syracuseStep 1071271 = 1606907) B1606907
theorem B2283707 : Blo 1068616 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B1071463 : Blo 1068616 1071463 := bstep (se 1 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 1071463 = 1607195) B1607195
theorem B1202791 : Blo 1068616 1202791 := bstep (se 1 (by rfl) ⟨902093, by rfl⟩ : syracuseStep 1202791 = 1804187) B1804187
theorem B1071719 : Blo 1068616 1071719 := bstep (se 1 (by rfl) ⟨803789, by rfl⟩ : syracuseStep 1071719 = 1607579) B1607579
theorem B1071743 : Blo 1068616 1071743 := bstep (se 1 (by rfl) ⟨803807, by rfl⟩ : syracuseStep 1071743 = 1607615) B1607615
theorem B2316943 : Blo 1068616 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B1072159 : Blo 1068616 1072159 := bstep (se 1 (by rfl) ⟨804119, by rfl⟩ : syracuseStep 1072159 = 1608239) B1608239
theorem B1203295 : Blo 1068616 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B1072239 : Blo 1068616 1072239 := bstep (se 1 (by rfl) ⟨804179, by rfl⟩ : syracuseStep 1072239 = 1608359) B1608359
theorem B1072283 : Blo 1068616 1072283 := bstep (se 1 (by rfl) ⟨804212, by rfl⟩ : syracuseStep 1072283 = 1608425) B1608425
theorem B1072287 : Blo 1068616 1072287 := bstep (se 1 (by rfl) ⟨804215, by rfl⟩ : syracuseStep 1072287 = 1608431) B1608431
theorem B1072319 : Blo 1068616 1072319 := bstep (se 1 (by rfl) ⟨804239, by rfl⟩ : syracuseStep 1072319 = 1608479) B1608479
theorem B8674553 : Blo 1068616 8674553 := bstep (se 2 (by rfl) ⟨3252957, by rfl⟩ : syracuseStep 8674553 = 6505915) B6505915
theorem B1072539 : Blo 1068616 1072539 := bstep (se 1 (by rfl) ⟨804404, by rfl⟩ : syracuseStep 1072539 = 1608809) B1608809
theorem B5496445 : Blo 1068616 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B4120247 : Blo 1068616 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B2711465 : Blo 1068616 2711465 := bstep (se 2 (by rfl) ⟨1016799, by rfl⟩ : syracuseStep 2711465 = 2033599) B2033599
theorem B3433583 : Blo 1068616 3433583 := bstep (se 1 (by rfl) ⟨2575187, by rfl⟩ : syracuseStep 3433583 = 5150375) B5150375
theorem B46228805 : Blo 1068616 46228805 := bstep (se 4 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 46228805 = 8667901) B8667901
theorem B11560573 : Blo 1068616 11560573 := bstep (se 3 (by rfl) ⟨2167607, by rfl⟩ : syracuseStep 11560573 = 4335215) B4335215
theorem B2714593 : Blo 1068616 2714593 := bstep (se 2 (by rfl) ⟨1017972, by rfl⟩ : syracuseStep 2714593 = 2035945) B2035945
theorem B4058207 : Blo 1068616 4058207 := bstep (se 1 (by rfl) ⟨3043655, by rfl⟩ : syracuseStep 4058207 = 6087311) B6087311
theorem B8122031 : Blo 1068616 8122031 := bstep (se 1 (by rfl) ⟨6091523, by rfl⟩ : syracuseStep 8122031 = 12183047) B12183047
theorem B2289755 : Blo 1068616 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B5141303 : Blo 1068616 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B1930223 : Blo 1068616 1930223 := bstep (se 1 (by rfl) ⟨1447667, by rfl⟩ : syracuseStep 1930223 = 2895335) B2895335
theorem B3470845 : Blo 1068616 3470845 := bstep (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) B1301567
theorem B6092617 : Blo 1068616 6092617 := bstep (se 2 (by rfl) ⟨2284731, by rfl⟩ : syracuseStep 6092617 = 4569463) B4569463
theorem B1603439 : Blo 1068616 1603439 := bstep (se 1 (by rfl) ⟨1202579, by rfl⟩ : syracuseStep 1603439 = 2405159) B2405159
theorem B1603451 : Blo 1068616 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B1603691 : Blo 1068616 1603691 := bstep (se 1 (by rfl) ⟨1202768, by rfl⟩ : syracuseStep 1603691 = 2405537) B2405537
theorem B1603871 : Blo 1068616 1603871 := bstep (se 1 (by rfl) ⟨1202903, by rfl⟩ : syracuseStep 1603871 = 2405807) B2405807
theorem B1603943 : Blo 1068616 1603943 := bstep (se 1 (by rfl) ⟨1202957, by rfl⟩ : syracuseStep 1603943 = 2405915) B2405915
theorem B1604009 : Blo 1068616 1604009 := bstep (se 2 (by rfl) ⟨601503, by rfl⟩ : syracuseStep 1604009 = 1203007) B1203007
theorem B1604063 : Blo 1068616 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B2030447 : Blo 1068616 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1604591 : Blo 1068616 1604591 := bstep (se 1 (by rfl) ⟨1203443, by rfl⟩ : syracuseStep 1604591 = 2406887) B2406887
theorem B1604777 : Blo 1068616 1604777 := bstep (se 2 (by rfl) ⟨601791, by rfl⟩ : syracuseStep 1604777 = 1203583) B1203583
theorem B9273035 : Blo 1068616 9273035 := bstep (se 1 (by rfl) ⟨6954776, by rfl⟩ : syracuseStep 9273035 = 13909553) B13909553
theorem B4063067 : Blo 1068616 4063067 := bstep (se 1 (by rfl) ⟨3047300, by rfl⟩ : syracuseStep 4063067 = 6094601) B6094601
theorem B16482203 : Blo 1068616 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B1606199 : Blo 1068616 1606199 := bstep (se 1 (by rfl) ⟨1204649, by rfl⟩ : syracuseStep 1606199 = 2409299) B2409299
theorem B14648435 : Blo 1068616 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B1803431 : Blo 1068616 1803431 := bstep (se 1 (by rfl) ⟨1352573, by rfl⟩ : syracuseStep 1803431 = 2705147) B2705147
theorem B3474895 : Blo 1068616 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B10978861 : Blo 1068616 10978861 := bstep (se 3 (by rfl) ⟨2058536, by rfl⟩ : syracuseStep 10978861 = 4117073) B4117073
theorem B10290827 : Blo 1068616 10290827 := bstep (se 1 (by rfl) ⟨7718120, by rfl⟩ : syracuseStep 10290827 = 15436241) B15436241
theorem B1607495 : Blo 1068616 1607495 := bstep (se 1 (by rfl) ⟨1205621, by rfl⟩ : syracuseStep 1607495 = 2411243) B2411243
theorem B1607771 : Blo 1068616 1607771 := bstep (se 1 (by rfl) ⟨1205828, by rfl⟩ : syracuseStep 1607771 = 2411657) B2411657
theorem B1607807 : Blo 1068616 1607807 := bstep (se 1 (by rfl) ⟨1205855, by rfl⟩ : syracuseStep 1607807 = 2411711) B2411711
theorem B9767051 : Blo 1068616 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B1607999 : Blo 1068616 1607999 := bstep (se 1 (by rfl) ⟨1205999, by rfl⟩ : syracuseStep 1607999 = 2411999) B2411999
theorem B9144737 : Blo 1068616 9144737 := bstep (se 2 (by rfl) ⟨3429276, by rfl⟩ : syracuseStep 9144737 = 6858553) B6858553
theorem B1608143 : Blo 1068616 1608143 := bstep (se 1 (by rfl) ⟨1206107, by rfl⟩ : syracuseStep 1608143 = 2412215) B2412215
theorem B23464655 : Blo 1068616 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B19500011 : Blo 1068616 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B19795049 : Blo 1068616 19795049 := bstep (se 2 (by rfl) ⟨7423143, by rfl⟩ : syracuseStep 19795049 = 14846287) B14846287
theorem B12357029 : Blo 1068616 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B1805935 : Blo 1068616 1805935 := bstep (se 1 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 1805935 = 2708903) B2708903
theorem B6099407 : Blo 1068616 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B1807643 : Blo 1068616 1807643 := bstep (se 1 (by rfl) ⟨1355732, by rfl⟩ : syracuseStep 1807643 = 2711465) B2711465
theorem B4069385 : Blo 1068616 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B3611627 : Blo 1068616 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B4627793 : Blo 1068616 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B5414525 : Blo 1068616 5414525 := bstep (se 3 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 5414525 = 2030447) B2030447
theorem B5414687 : Blo 1068616 5414687 := bstep (se 1 (by rfl) ⟨4061015, by rfl⟩ : syracuseStep 5414687 = 8122031) B8122031
theorem B6102823 : Blo 1068616 6102823 := bstep (se 1 (by rfl) ⟨4577117, by rfl⟩ : syracuseStep 6102823 = 9154235) B9154235
theorem B9282185 : Blo 1068616 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B1286815 : Blo 1068616 1286815 := bstep (se 1 (by rfl) ⟨965111, by rfl⟩ : syracuseStep 1286815 = 1930223) B1930223
theorem B4072103 : Blo 1068616 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B8135639 : Blo 1068616 8135639 := bstep (se 1 (by rfl) ⟨6101729, by rfl⟩ : syracuseStep 8135639 = 12203459) B12203459
theorem B6104807 : Blo 1068616 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B10988135 : Blo 1068616 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B6106013 : Blo 1068616 6106013 := bstep (se 3 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 6106013 = 2289755) B2289755
theorem B5778647 : Blo 1068616 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B5418575 : Blo 1068616 5418575 := bstep (se 1 (by rfl) ⟨4063931, by rfl⟩ : syracuseStep 5418575 = 8127863) B8127863
theorem B3616595 : Blo 1068616 3616595 := bstep (se 1 (by rfl) ⟨2712446, by rfl⟩ : syracuseStep 3616595 = 5424893) B5424893
theorem B1355611 : Blo 1068616 1355611 := bstep (se 1 (by rfl) ⟨1016708, by rfl⟩ : syracuseStep 1355611 = 2033417) B2033417
theorem B3616703 : Blo 1068616 3616703 := bstep (se 1 (by rfl) ⟨2712527, by rfl⟩ : syracuseStep 3616703 = 5425055) B5425055
theorem B3912475 : Blo 1068616 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B15414097 : Blo 1068616 15414097 := bstep (se 2 (by rfl) ⟨5780286, by rfl⟩ : syracuseStep 15414097 = 11560573) B11560573
theorem B2405231 : Blo 1068616 2405231 := bstep (se 1 (by rfl) ⟨1803923, by rfl⟩ : syracuseStep 2405231 = 3607847) B3607847
theorem B6272083 : Blo 1068616 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B5780807 : Blo 1068616 5780807 := bstep (se 1 (by rfl) ⟨4335605, by rfl⟩ : syracuseStep 5780807 = 8671211) B8671211
theorem B22263113 : Blo 1068616 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B3618215 : Blo 1068616 3618215 := bstep (se 1 (by rfl) ⟨2713661, by rfl⟩ : syracuseStep 3618215 = 5427323) B5427323
theorem B5420519 : Blo 1068616 5420519 := bstep (se 1 (by rfl) ⟨4065389, by rfl⟩ : syracuseStep 5420519 = 8130779) B8130779
theorem B3618431 : Blo 1068616 3618431 := bstep (se 1 (by rfl) ⟨2713823, by rfl⟩ : syracuseStep 3618431 = 5427647) B5427647
theorem B2406815 : Blo 1068616 2406815 := bstep (se 1 (by rfl) ⟨1805111, by rfl⟩ : syracuseStep 2406815 = 3610223) B3610223
theorem B3619457 : Blo 1068616 3619457 := bstep (se 2 (by rfl) ⟨1357296, by rfl⟩ : syracuseStep 3619457 = 2714593) B2714593
theorem B3619511 : Blo 1068616 3619511 := bstep (se 1 (by rfl) ⟨2714633, by rfl⟩ : syracuseStep 3619511 = 5429267) B5429267
theorem B2407175 : Blo 1068616 2407175 := bstep (se 1 (by rfl) ⟨1805381, by rfl⟩ : syracuseStep 2407175 = 3610763) B3610763
theorem B1522471 : Blo 1068616 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B2407787 : Blo 1068616 2407787 := bstep (se 1 (by rfl) ⟨1805840, by rfl⟩ : syracuseStep 2407787 = 3611681) B3611681
theorem B2407967 : Blo 1068616 2407967 := bstep (se 1 (by rfl) ⟨1805975, by rfl⟩ : syracuseStep 2407967 = 3611951) B3611951
theorem B5422787 : Blo 1068616 5422787 := bstep (se 1 (by rfl) ⟨4067090, by rfl⟩ : syracuseStep 5422787 = 8134181) B8134181
theorem B4341737 : Blo 1068616 4341737 := bstep (se 2 (by rfl) ⟨1628151, by rfl⟩ : syracuseStep 4341737 = 3256303) B3256303
theorem B30819203 : Blo 1068616 30819203 := bstep (se 1 (by rfl) ⟨23114402, by rfl⟩ : syracuseStep 30819203 = 46228805) B46228805
theorem B2409785 : Blo 1068616 2409785 := bstep (se 2 (by rfl) ⟨903669, by rfl⟩ : syracuseStep 2409785 = 1807339) B1807339
theorem B2409839 : Blo 1068616 2409839 := bstep (se 1 (by rfl) ⟨1807379, by rfl⟩ : syracuseStep 2409839 = 3614759) B3614759
theorem B2410451 : Blo 1068616 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B2705471 : Blo 1068616 2705471 := bstep (se 1 (by rfl) ⟨2029103, by rfl⟩ : syracuseStep 2705471 = 4058207) B4058207
theorem B2410721 : Blo 1068616 2410721 := bstep (se 2 (by rfl) ⟨904020, by rfl⟩ : syracuseStep 2410721 = 1808041) B1808041
theorem B2411387 : Blo 1068616 2411387 := bstep (se 1 (by rfl) ⟨1808540, by rfl⟩ : syracuseStep 2411387 = 3617081) B3617081
theorem B3427535 : Blo 1068616 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B1068959 : Blo 1068616 1068959 := bstep (se 1 (by rfl) ⟨801719, by rfl⟩ : syracuseStep 1068959 = 1603439) B1603439
theorem B1068967 : Blo 1068616 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B2412521 : Blo 1068616 2412521 := bstep (se 2 (by rfl) ⟨904695, by rfl⟩ : syracuseStep 2412521 = 1809391) B1809391
theorem B2412575 : Blo 1068616 2412575 := bstep (se 1 (by rfl) ⟨1809431, by rfl⟩ : syracuseStep 2412575 = 3618863) B3618863
theorem B1069127 : Blo 1068616 1069127 := bstep (se 1 (by rfl) ⟨801845, by rfl⟩ : syracuseStep 1069127 = 1603691) B1603691
theorem B2412665 : Blo 1068616 2412665 := bstep (se 2 (by rfl) ⟨904749, by rfl⟩ : syracuseStep 2412665 = 1809499) B1809499
theorem B1069247 : Blo 1068616 1069247 := bstep (se 1 (by rfl) ⟨801935, by rfl⟩ : syracuseStep 1069247 = 1603871) B1603871
theorem B1069295 : Blo 1068616 1069295 := bstep (se 1 (by rfl) ⟨801971, by rfl⟩ : syracuseStep 1069295 = 1603943) B1603943
theorem B1069339 : Blo 1068616 1069339 := bstep (se 1 (by rfl) ⟨802004, by rfl⟩ : syracuseStep 1069339 = 1604009) B1604009
theorem B1069375 : Blo 1068616 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B7524733 : Blo 1068616 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B1069727 : Blo 1068616 1069727 := bstep (se 1 (by rfl) ⟨802295, by rfl⟩ : syracuseStep 1069727 = 1604591) B1604591
theorem B1069851 : Blo 1068616 1069851 := bstep (se 1 (by rfl) ⟨802388, by rfl⟩ : syracuseStep 1069851 = 1604777) B1604777
theorem B2413367 : Blo 1068616 2413367 := bstep (se 1 (by rfl) ⟨1810025, by rfl⟩ : syracuseStep 2413367 = 3620051) B3620051
theorem B7328593 : Blo 1068616 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B4576283 : Blo 1068616 4576283 := bstep (se 1 (by rfl) ⟨3432212, by rfl⟩ : syracuseStep 4576283 = 6864425) B6864425
theorem B6182023 : Blo 1068616 6182023 := bstep (se 1 (by rfl) ⟨4636517, by rfl⟩ : syracuseStep 6182023 = 9273035) B9273035
theorem B3855545 : Blo 1068616 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B2708711 : Blo 1068616 2708711 := bstep (se 1 (by rfl) ⟨2031533, by rfl⟩ : syracuseStep 2708711 = 4063067) B4063067
theorem B2381239 : Blo 1068616 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B2709065 : Blo 1068616 2709065 := bstep (se 2 (by rfl) ⟨1015899, by rfl⟩ : syracuseStep 2709065 = 2031799) B2031799
theorem B6871007 : Blo 1068616 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B1071343 : Blo 1068616 1071343 := bstep (se 1 (by rfl) ⟨803507, by rfl⟩ : syracuseStep 1071343 = 1607015) B1607015
theorem B88004879 : Blo 1068616 88004879 := bstep (se 1 (by rfl) ⟨66003659, by rfl⟩ : syracuseStep 88004879 = 132007319) B132007319
theorem B1071423 : Blo 1068616 1071423 := bstep (se 1 (by rfl) ⟨803567, by rfl⟩ : syracuseStep 1071423 = 1607135) B1607135
theorem B1071599 : Blo 1068616 1071599 := bstep (se 1 (by rfl) ⟨803699, by rfl⟩ : syracuseStep 1071599 = 1607399) B1607399
theorem B5429753 : Blo 1068616 5429753 := bstep (se 2 (by rfl) ⟨2036157, by rfl⟩ : syracuseStep 5429753 = 4072315) B4072315
theorem B15653521 : Blo 1068616 15653521 := bstep (se 2 (by rfl) ⟨5870070, by rfl⟩ : syracuseStep 15653521 = 11740141) B11740141
theorem B12999527 : Blo 1068616 12999527 := bstep (se 1 (by rfl) ⟨9749645, by rfl⟩ : syracuseStep 12999527 = 19499291) B19499291
theorem B1072123 : Blo 1068616 1072123 := bstep (se 1 (by rfl) ⟨804092, by rfl⟩ : syracuseStep 1072123 = 1608185) B1608185
theorem B1072155 : Blo 1068616 1072155 := bstep (se 1 (by rfl) ⟨804116, by rfl⟩ : syracuseStep 1072155 = 1608233) B1608233
theorem B1203367 : Blo 1068616 1203367 := bstep (se 1 (by rfl) ⟨902525, by rfl⟩ : syracuseStep 1203367 = 1805051) B1805051
theorem B8118143 : Blo 1068616 8118143 := bstep (se 1 (by rfl) ⟨6088607, by rfl⟩ : syracuseStep 8118143 = 12177215) B12177215
theorem B3858313 : Blo 1068616 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B5136479 : Blo 1068616 5136479 := bstep (se 1 (by rfl) ⟨3852359, by rfl⟩ : syracuseStep 5136479 = 7704719) B7704719
theorem B3661919 : Blo 1068616 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B6086785 : Blo 1068616 6086785 := bstep (se 2 (by rfl) ⟨2282544, by rfl⟩ : syracuseStep 6086785 = 4565089) B4565089
theorem B47539061 : Blo 1068616 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B13722695 : Blo 1068616 13722695 := bstep (se 1 (by rfl) ⟨10292021, by rfl⟩ : syracuseStep 13722695 = 20584043) B20584043
theorem B1205851 : Blo 1068616 1205851 := bstep (se 1 (by rfl) ⟨904388, by rfl⟩ : syracuseStep 1205851 = 1808777) B1808777
theorem B10282909 : Blo 1068616 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B2746831 : Blo 1068616 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B5139611 : Blo 1068616 5139611 := bstep (se 1 (by rfl) ⟨3854708, by rfl⟩ : syracuseStep 5139611 = 7709417) B7709417
theorem B2289055 : Blo 1068616 2289055 := bstep (se 1 (by rfl) ⟨1716791, by rfl⟩ : syracuseStep 2289055 = 3433583) B3433583
theorem B5860993 : Blo 1068616 5860993 := bstep (se 2 (by rfl) ⟨2197872, by rfl⟩ : syracuseStep 5860993 = 4395745) B4395745
theorem B23424673 : Blo 1068616 23424673 := bstep (se 2 (by rfl) ⟨8784252, by rfl⟩ : syracuseStep 23424673 = 17568505) B17568505
theorem B26013545 : Blo 1068616 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B49639553 : Blo 1068616 49639553 := bstep (se 2 (by rfl) ⟨18614832, by rfl⟩ : syracuseStep 49639553 = 37229665) B37229665
theorem B11563343 : Blo 1068616 11563343 := bstep (se 1 (by rfl) ⟨8672507, by rfl⟩ : syracuseStep 11563343 = 17345015) B17345015
theorem B8123489 : Blo 1068616 8123489 := bstep (se 2 (by rfl) ⟨3046308, by rfl⟩ : syracuseStep 8123489 = 6092617) B6092617
theorem B1930367 : Blo 1068616 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B3044783 : Blo 1068616 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B1603199 : Blo 1068616 1603199 := bstep (se 1 (by rfl) ⟨1202399, by rfl⟩ : syracuseStep 1603199 = 2404799) B2404799
theorem B13727663 : Blo 1068616 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B23132141 : Blo 1068616 23132141 := bstep (se 3 (by rfl) ⟨4337276, by rfl⟩ : syracuseStep 23132141 = 8674553) B8674553
theorem B14874697 : Blo 1068616 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B1603721 : Blo 1068616 1603721 := bstep (se 2 (by rfl) ⟨601395, by rfl⟩ : syracuseStep 1603721 = 1202791) B1202791
theorem B1604393 : Blo 1068616 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B1604735 : Blo 1068616 1604735 := bstep (se 1 (by rfl) ⟨1203551, by rfl⟩ : syracuseStep 1604735 = 2407103) B2407103
theorem B1604927 : Blo 1068616 1604927 := bstep (se 1 (by rfl) ⟨1203695, by rfl⟩ : syracuseStep 1604927 = 2407391) B2407391
theorem B79331717 : Blo 1068616 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B20546135 : Blo 1068616 20546135 := bstep (se 1 (by rfl) ⟨15409601, by rfl⟩ : syracuseStep 20546135 = 30819203) B30819203
theorem B9765623 : Blo 1068616 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B1606523 : Blo 1068616 1606523 := bstep (se 1 (by rfl) ⟨1204892, by rfl⟩ : syracuseStep 1606523 = 2409785) B2409785
theorem B1606559 : Blo 1068616 1606559 := bstep (se 1 (by rfl) ⟨1204919, by rfl⟩ : syracuseStep 1606559 = 2409839) B2409839
theorem B1606967 : Blo 1068616 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B1803647 : Blo 1068616 1803647 := bstep (se 1 (by rfl) ⟨1352735, by rfl⟩ : syracuseStep 1803647 = 2705471) B2705471
theorem B1607147 : Blo 1068616 1607147 := bstep (se 1 (by rfl) ⟨1205360, by rfl⟩ : syracuseStep 1607147 = 2410721) B2410721
theorem B6096491 : Blo 1068616 6096491 := bstep (se 1 (by rfl) ⟨4572368, by rfl⟩ : syracuseStep 6096491 = 9144737) B9144737
theorem B1607591 : Blo 1068616 1607591 := bstep (se 1 (by rfl) ⟨1205693, by rfl⟩ : syracuseStep 1607591 = 2411387) B2411387
theorem B1607801 : Blo 1068616 1607801 := bstep (se 2 (by rfl) ⟨602925, by rfl⟩ : syracuseStep 1607801 = 1205851) B1205851
theorem B1608347 : Blo 1068616 1608347 := bstep (se 1 (by rfl) ⟨1206260, by rfl⟩ : syracuseStep 1608347 = 2412521) B2412521
theorem B1608383 : Blo 1068616 1608383 := bstep (se 1 (by rfl) ⟨1206287, by rfl⟩ : syracuseStep 1608383 = 2412575) B2412575
theorem B1608443 : Blo 1068616 1608443 := bstep (se 1 (by rfl) ⟨1206332, by rfl⟩ : syracuseStep 1608443 = 2412665) B2412665
theorem B4066271 : Blo 1068616 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B1608911 : Blo 1068616 1608911 := bstep (se 1 (by rfl) ⟨1206683, by rfl⟩ : syracuseStep 1608911 = 2413367) B2413367
theorem B3050855 : Blo 1068616 3050855 := bstep (se 1 (by rfl) ⟨2288141, by rfl⟩ : syracuseStep 3050855 = 4576283) B4576283
theorem B1805807 : Blo 1068616 1805807 := bstep (se 1 (by rfl) ⟨1354355, by rfl⟩ : syracuseStep 1805807 = 2708711) B2708711
theorem B1806043 : Blo 1068616 1806043 := bstep (se 1 (by rfl) ⟨1354532, by rfl⟩ : syracuseStep 1806043 = 2709065) B2709065
theorem B3052073 : Blo 1068616 3052073 := bstep (se 2 (by rfl) ⟨1144527, by rfl⟩ : syracuseStep 3052073 = 2289055) B2289055
theorem B31232897 : Blo 1068616 31232897 := bstep (se 2 (by rfl) ⟨11712336, by rfl⟩ : syracuseStep 31232897 = 23424673) B23424673
theorem B3609683 : Blo 1068616 3609683 := bstep (se 1 (by rfl) ⟨2707262, by rfl⟩ : syracuseStep 3609683 = 5414525) B5414525
theorem B1807481 : Blo 1068616 1807481 := bstep (se 2 (by rfl) ⟨677805, by rfl⟩ : syracuseStep 1807481 = 1355611) B1355611
theorem B3609791 : Blo 1068616 3609791 := bstep (se 1 (by rfl) ⟨2707343, by rfl⟩ : syracuseStep 3609791 = 5414687) B5414687
theorem B18322685 : Blo 1068616 18322685 := bstep (se 3 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 18322685 = 6871007) B6871007
theorem B5412095 : Blo 1068616 5412095 := bstep (se 1 (by rfl) ⟨4059071, by rfl⟩ : syracuseStep 5412095 = 8118143) B8118143
theorem B10032977 : Blo 1068616 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B31692707 : Blo 1068616 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B9148463 : Blo 1068616 9148463 := bstep (se 1 (by rfl) ⟨6861347, by rfl⟩ : syracuseStep 9148463 = 13722695) B13722695
theorem B5216633 : Blo 1068616 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B20552129 : Blo 1068616 20552129 := bstep (se 2 (by rfl) ⟨7707048, by rfl⟩ : syracuseStep 20552129 = 15414097) B15414097
theorem B9771457 : Blo 1068616 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B4069871 : Blo 1068616 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B8362777 : Blo 1068616 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B4070675 : Blo 1068616 4070675 := bstep (se 1 (by rfl) ⟨3053006, by rfl⟩ : syracuseStep 4070675 = 6106013) B6106013
theorem B3612383 : Blo 1068616 3612383 := bstep (se 1 (by rfl) ⟨2709287, by rfl⟩ : syracuseStep 3612383 = 5418575) B5418575
theorem B17342363 : Blo 1068616 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B7708895 : Blo 1068616 7708895 := bstep (se 1 (by rfl) ⟨5781671, by rfl⟩ : syracuseStep 7708895 = 11563343) B11563343
theorem B5415659 : Blo 1068616 5415659 := bstep (se 1 (by rfl) ⟨4061744, by rfl⟩ : syracuseStep 5415659 = 8123489) B8123489
theorem B1286911 : Blo 1068616 1286911 := bstep (se 1 (by rfl) ⟨965183, by rfl⟩ : syracuseStep 1286911 = 1930367) B1930367
theorem B3613679 : Blo 1068616 3613679 := bstep (se 1 (by rfl) ⟨2710259, by rfl⟩ : syracuseStep 3613679 = 5420519) B5420519
theorem B9151775 : Blo 1068616 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B8137097 : Blo 1068616 8137097 := bstep (se 2 (by rfl) ⟨3051411, by rfl⟩ : syracuseStep 8137097 = 6102823) B6102823
theorem B3615191 : Blo 1068616 3615191 := bstep (se 1 (by rfl) ⟨2711393, by rfl⟩ : syracuseStep 3615191 = 5422787) B5422787
theorem B2894491 : Blo 1068616 2894491 := bstep (se 1 (by rfl) ⟨2170868, by rfl⟩ : syracuseStep 2894491 = 4341737) B4341737
theorem B1715753 : Blo 1068616 1715753 := bstep (se 2 (by rfl) ⟨643407, by rfl⟩ : syracuseStep 1715753 = 1286815) B1286815
theorem B6860551 : Blo 1068616 6860551 := bstep (se 1 (by rfl) ⟨5145413, by rfl⟩ : syracuseStep 6860551 = 10290827) B10290827
theorem B15643103 : Blo 1068616 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B4633193 : Blo 1068616 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B8238019 : Blo 1068616 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B13710545 : Blo 1068616 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B2570363 : Blo 1068616 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B58669919 : Blo 1068616 58669919 := bstep (se 1 (by rfl) ⟨44002439, by rfl⟩ : syracuseStep 58669919 = 88004879) B88004879
theorem B3619835 : Blo 1068616 3619835 := bstep (se 1 (by rfl) ⟨2714876, by rfl⟩ : syracuseStep 3619835 = 5429753) B5429753
theorem B8666351 : Blo 1068616 8666351 := bstep (se 1 (by rfl) ⟨6499763, by rfl⟩ : syracuseStep 8666351 = 12999527) B12999527
theorem B2407751 : Blo 1068616 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B2407913 : Blo 1068616 2407913 := bstep (se 2 (by rfl) ⟨902967, by rfl⟩ : syracuseStep 2407913 = 1805935) B1805935
theorem B7814657 : Blo 1068616 7814657 := bstep (se 2 (by rfl) ⟨2930496, by rfl⟩ : syracuseStep 7814657 = 5860993) B5860993
theorem B3424319 : Blo 1068616 3424319 := bstep (se 1 (by rfl) ⟨2568239, by rfl⟩ : syracuseStep 3424319 = 5136479) B5136479
theorem B2441279 : Blo 1068616 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B5423759 : Blo 1068616 5423759 := bstep (se 1 (by rfl) ⟨4067819, by rfl⟩ : syracuseStep 5423759 = 8135639) B8135639
theorem B8242697 : Blo 1068616 8242697 := bstep (se 2 (by rfl) ⟨3091011, by rfl⟩ : syracuseStep 8242697 = 6182023) B6182023
theorem B7325423 : Blo 1068616 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B3426407 : Blo 1068616 3426407 := bstep (se 1 (by rfl) ⟨2569805, by rfl⟩ : syracuseStep 3426407 = 5139611) B5139611
theorem B3852431 : Blo 1068616 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B2411063 : Blo 1068616 2411063 := bstep (se 1 (by rfl) ⟨1808297, by rfl⟩ : syracuseStep 2411063 = 3616595) B3616595
theorem B2411135 : Blo 1068616 2411135 := bstep (se 1 (by rfl) ⟨1808351, by rfl⟩ : syracuseStep 2411135 = 3616703) B3616703
theorem B12340781 : Blo 1068616 12340781 := bstep (se 3 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 12340781 = 4627793) B4627793
theorem B3853871 : Blo 1068616 3853871 := bstep (se 1 (by rfl) ⟨2890403, by rfl⟩ : syracuseStep 3853871 = 5780807) B5780807
theorem B2412143 : Blo 1068616 2412143 := bstep (se 1 (by rfl) ⟨1809107, by rfl⟩ : syracuseStep 2412143 = 3618215) B3618215
theorem B1068799 : Blo 1068616 1068799 := bstep (se 1 (by rfl) ⟨801599, by rfl⟩ : syracuseStep 1068799 = 1603199) B1603199
theorem B2412287 : Blo 1068616 2412287 := bstep (se 1 (by rfl) ⟨1809215, by rfl⟩ : syracuseStep 2412287 = 3618431) B3618431
theorem B15421427 : Blo 1068616 15421427 := bstep (se 1 (by rfl) ⟨11566070, by rfl⟩ : syracuseStep 15421427 = 23132141) B23132141
theorem B1069147 : Blo 1068616 1069147 := bstep (se 1 (by rfl) ⟨801860, by rfl⟩ : syracuseStep 1069147 = 1603721) B1603721
theorem B2412971 : Blo 1068616 2412971 := bstep (se 1 (by rfl) ⟨1809728, by rfl⟩ : syracuseStep 2412971 = 3619457) B3619457
theorem B2413007 : Blo 1068616 2413007 := bstep (se 1 (by rfl) ⟨1809755, by rfl⟩ : syracuseStep 2413007 = 3619511) B3619511
theorem B1069595 : Blo 1068616 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B1069823 : Blo 1068616 1069823 := bstep (se 1 (by rfl) ⟨802367, by rfl⟩ : syracuseStep 1069823 = 1604735) B1604735
theorem B1069951 : Blo 1068616 1069951 := bstep (se 1 (by rfl) ⟨802463, by rfl⟩ : syracuseStep 1069951 = 1604927) B1604927
theorem B8115713 : Blo 1068616 8115713 := bstep (se 2 (by rfl) ⟨3043392, by rfl⟩ : syracuseStep 8115713 = 6086785) B6086785
theorem B1070799 : Blo 1068616 1070799 := bstep (se 1 (by rfl) ⟨803099, by rfl⟩ : syracuseStep 1070799 = 1606199) B1606199
theorem B1202287 : Blo 1068616 1202287 := bstep (se 1 (by rfl) ⟨901715, by rfl⟩ : syracuseStep 1202287 = 1803431) B1803431
theorem B1071663 : Blo 1068616 1071663 := bstep (se 1 (by rfl) ⟨803747, by rfl⟩ : syracuseStep 1071663 = 1607495) B1607495
theorem B1071847 : Blo 1068616 1071847 := bstep (se 1 (by rfl) ⟨803885, by rfl⟩ : syracuseStep 1071847 = 1607771) B1607771
theorem B1071871 : Blo 1068616 1071871 := bstep (se 1 (by rfl) ⟨803903, by rfl⟩ : syracuseStep 1071871 = 1607807) B1607807
theorem B6511367 : Blo 1068616 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B1071999 : Blo 1068616 1071999 := bstep (se 1 (by rfl) ⟨803999, by rfl⟩ : syracuseStep 1071999 = 1607999) B1607999
theorem B1072095 : Blo 1068616 1072095 := bstep (se 1 (by rfl) ⟨804071, by rfl⟩ : syracuseStep 1072095 = 1608143) B1608143
theorem B13000007 : Blo 1068616 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B14638481 : Blo 1068616 14638481 := bstep (se 2 (by rfl) ⟨5489430, by rfl⟩ : syracuseStep 14638481 = 10978861) B10978861
theorem B13196699 : Blo 1068616 13196699 := bstep (se 1 (by rfl) ⟨9897524, by rfl⟩ : syracuseStep 13196699 = 19795049) B19795049
theorem B2285023 : Blo 1068616 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B3662441 : Blo 1068616 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B1205095 : Blo 1068616 1205095 := bstep (se 1 (by rfl) ⟨903821, by rfl⟩ : syracuseStep 1205095 = 1807643) B1807643
theorem B2712923 : Blo 1068616 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B6188123 : Blo 1068616 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B2714735 : Blo 1068616 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B3174985 : Blo 1068616 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B33093035 : Blo 1068616 33093035 := bstep (se 1 (by rfl) ⟨24819776, by rfl⟩ : syracuseStep 33093035 = 49639553) B49639553
theorem B1603487 : Blo 1068616 1603487 := bstep (se 1 (by rfl) ⟨1202615, by rfl⟩ : syracuseStep 1603487 = 2405231) B2405231
theorem B20871361 : Blo 1068616 20871361 := bstep (se 2 (by rfl) ⟨7826760, by rfl⟩ : syracuseStep 20871361 = 15653521) B15653521
theorem B14842075 : Blo 1068616 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B2029855 : Blo 1068616 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B2029961 : Blo 1068616 2029961 := bstep (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) B1522471
theorem B1604489 : Blo 1068616 1604489 := bstep (se 2 (by rfl) ⟨601683, by rfl⟩ : syracuseStep 1604489 = 1203367) B1203367
theorem B1604543 : Blo 1068616 1604543 := bstep (se 1 (by rfl) ⟨1203407, by rfl⟩ : syracuseStep 1604543 = 2406815) B2406815
theorem B1604783 : Blo 1068616 1604783 := bstep (se 1 (by rfl) ⟨1203587, by rfl⟩ : syracuseStep 1604783 = 2407175) B2407175
theorem B1605191 : Blo 1068616 1605191 := bstep (se 1 (by rfl) ⟨1203893, by rfl⟩ : syracuseStep 1605191 = 2407787) B2407787
theorem B1605311 : Blo 1068616 1605311 := bstep (se 1 (by rfl) ⟨1203983, by rfl⟩ : syracuseStep 1605311 = 2407967) B2407967
theorem B5144417 : Blo 1068616 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B52887811 : Blo 1068616 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B13697423 : Blo 1068616 13697423 := bstep (se 1 (by rfl) ⟨10273067, by rfl⟩ : syracuseStep 13697423 = 20546135) B20546135
theorem B4064327 : Blo 1068616 4064327 := bstep (se 1 (by rfl) ⟨3048245, by rfl⟩ : syracuseStep 4064327 = 6096491) B6096491
theorem B1606793 : Blo 1068616 1606793 := bstep (se 2 (by rfl) ⟨602547, by rfl⟩ : syracuseStep 1606793 = 1205095) B1205095
theorem B4883615 : Blo 1068616 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B41714941 : Blo 1068616 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B1607375 : Blo 1068616 1607375 := bstep (se 1 (by rfl) ⟨1205531, by rfl⟩ : syracuseStep 1607375 = 2411063) B2411063
theorem B1607423 : Blo 1068616 1607423 := bstep (se 1 (by rfl) ⟨1205567, by rfl⟩ : syracuseStep 1607423 = 2411135) B2411135
theorem B2033903 : Blo 1068616 2033903 := bstep (se 1 (by rfl) ⟨1525427, by rfl⟩ : syracuseStep 2033903 = 3050855) B3050855
theorem B8227187 : Blo 1068616 8227187 := bstep (se 1 (by rfl) ⟨6170390, by rfl⟩ : syracuseStep 8227187 = 12340781) B12340781
theorem B1608095 : Blo 1068616 1608095 := bstep (se 1 (by rfl) ⟨1206071, by rfl⟩ : syracuseStep 1608095 = 2412143) B2412143
theorem B1608191 : Blo 1068616 1608191 := bstep (se 1 (by rfl) ⟨1206143, by rfl⟩ : syracuseStep 1608191 = 2412287) B2412287
theorem B1608647 : Blo 1068616 1608647 := bstep (se 1 (by rfl) ⟨1206485, by rfl⟩ : syracuseStep 1608647 = 2412971) B2412971
theorem B1608671 : Blo 1068616 1608671 := bstep (se 1 (by rfl) ⟨1206503, by rfl⟩ : syracuseStep 1608671 = 2413007) B2413007
theorem B2034715 : Blo 1068616 2034715 := bstep (se 1 (by rfl) ⟨1526036, by rfl⟩ : syracuseStep 2034715 = 3052073) B3052073
theorem B3608063 : Blo 1068616 3608063 := bstep (se 1 (by rfl) ⟨2706047, by rfl⟩ : syracuseStep 3608063 = 5412095) B5412095
theorem B5410475 : Blo 1068616 5410475 := bstep (se 1 (by rfl) ⟨4057856, by rfl⟩ : syracuseStep 5410475 = 8115713) B8115713
theorem B6688651 : Blo 1068616 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B6098975 : Blo 1068616 6098975 := bstep (se 1 (by rfl) ⟨4574231, by rfl⟩ : syracuseStep 6098975 = 9148463) B9148463
theorem B3477755 : Blo 1068616 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B13701419 : Blo 1068616 13701419 := bstep (se 1 (by rfl) ⟨10276064, by rfl⟩ : syracuseStep 13701419 = 20552129) B20552129
theorem B9147401 : Blo 1068616 9147401 := bstep (se 2 (by rfl) ⟨3430275, by rfl⟩ : syracuseStep 9147401 = 6860551) B6860551
theorem B3610439 : Blo 1068616 3610439 := bstep (se 1 (by rfl) ⟨2707829, by rfl⟩ : syracuseStep 3610439 = 5415659) B5415659
theorem B4233313 : Blo 1068616 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B6101183 : Blo 1068616 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B1808615 : Blo 1068616 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B5413229 : Blo 1068616 5413229 := bstep (se 3 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 5413229 = 2029961) B2029961
theorem B10984025 : Blo 1068616 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B1809823 : Blo 1068616 1809823 := bstep (se 1 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 1809823 = 2714735) B2714735
theorem B27828481 : Blo 1068616 27828481 := bstep (se 2 (by rfl) ⟨10435680, by rfl⟩ : syracuseStep 27828481 = 20871361) B20871361
theorem B3088795 : Blo 1068616 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B22062023 : Blo 1068616 22062023 := bstep (se 1 (by rfl) ⟨16546517, by rfl⟩ : syracuseStep 22062023 = 33093035) B33093035
theorem B11150369 : Blo 1068616 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B1713575 : Blo 1068616 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B5777567 : Blo 1068616 5777567 := bstep (se 1 (by rfl) ⟨4333175, by rfl⟩ : syracuseStep 5777567 = 8666351) B8666351
theorem B3615839 : Blo 1068616 3615839 := bstep (se 1 (by rfl) ⟨2711879, by rfl⟩ : syracuseStep 3615839 = 5423759) B5423759
theorem B2568287 : Blo 1068616 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B2569247 : Blo 1068616 2569247 := bstep (se 1 (by rfl) ⟨1926935, by rfl⟩ : syracuseStep 2569247 = 3853871) B3853871
theorem B20821931 : Blo 1068616 20821931 := bstep (se 1 (by rfl) ⟨15616448, by rfl⟩ : syracuseStep 20821931 = 31232897) B31232897
theorem B2406455 : Blo 1068616 2406455 := bstep (se 1 (by rfl) ⟨1804841, by rfl⟩ : syracuseStep 2406455 = 3609683) B3609683
theorem B2406527 : Blo 1068616 2406527 := bstep (se 1 (by rfl) ⟨1804895, by rfl⟩ : syracuseStep 2406527 = 3609791) B3609791
theorem B6863525 : Blo 1068616 6863525 := bstep (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) B1286911
theorem B4340911 : Blo 1068616 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B8666671 : Blo 1068616 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B8797799 : Blo 1068616 8797799 := bstep (se 1 (by rfl) ⟨6598349, by rfl⟩ : syracuseStep 8797799 = 13196699) B13196699
theorem B2408057 : Blo 1068616 2408057 := bstep (se 2 (by rfl) ⟨903021, by rfl⟩ : syracuseStep 2408057 = 1806043) B1806043
theorem B2408255 : Blo 1068616 2408255 := bstep (se 1 (by rfl) ⟨1806191, by rfl⟩ : syracuseStep 2408255 = 3612383) B3612383
theorem B2441627 : Blo 1068616 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B2409119 : Blo 1068616 2409119 := bstep (se 1 (by rfl) ⟨1806839, by rfl⟩ : syracuseStep 2409119 = 3613679) B3613679
theorem B5424731 : Blo 1068616 5424731 := bstep (se 1 (by rfl) ⟨4068548, by rfl⟩ : syracuseStep 5424731 = 8137097) B8137097
theorem B2410127 : Blo 1068616 2410127 := bstep (se 1 (by rfl) ⟨1807595, by rfl⟩ : syracuseStep 2410127 = 3615191) B3615191
theorem B2706473 : Blo 1068616 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B13028609 : Blo 1068616 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B1068991 : Blo 1068616 1068991 := bstep (se 1 (by rfl) ⟨801743, by rfl⟩ : syracuseStep 1068991 = 1603487) B1603487
theorem B4575341 : Blo 1068616 4575341 := bstep (se 3 (by rfl) ⟨857876, by rfl⟩ : syracuseStep 4575341 = 1715753) B1715753
theorem B39113279 : Blo 1068616 39113279 := bstep (se 1 (by rfl) ⟨29334959, by rfl⟩ : syracuseStep 39113279 = 58669919) B58669919
theorem B1069659 : Blo 1068616 1069659 := bstep (se 1 (by rfl) ⟨802244, by rfl⟩ : syracuseStep 1069659 = 1604489) B1604489
theorem B1069695 : Blo 1068616 1069695 := bstep (se 1 (by rfl) ⟨802271, by rfl⟩ : syracuseStep 1069695 = 1604543) B1604543
theorem B2413223 : Blo 1068616 2413223 := bstep (se 1 (by rfl) ⟨1809917, by rfl⟩ : syracuseStep 2413223 = 3619835) B3619835
theorem B1069855 : Blo 1068616 1069855 := bstep (se 1 (by rfl) ⟨802391, by rfl⟩ : syracuseStep 1069855 = 1604783) B1604783
theorem B1070127 : Blo 1068616 1070127 := bstep (se 1 (by rfl) ⟨802595, by rfl⟩ : syracuseStep 1070127 = 1605191) B1605191
theorem B1070207 : Blo 1068616 1070207 := bstep (se 1 (by rfl) ⟨802655, by rfl⟩ : syracuseStep 1070207 = 1605311) B1605311
theorem B3429611 : Blo 1068616 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B2282879 : Blo 1068616 2282879 := bstep (se 1 (by rfl) ⟨1712159, by rfl⟩ : syracuseStep 2282879 = 3424319) B3424319
theorem B6510077 : Blo 1068616 6510077 := bstep (se 3 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 6510077 = 2441279) B2441279
theorem B6510415 : Blo 1068616 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B1071015 : Blo 1068616 1071015 := bstep (se 1 (by rfl) ⟨803261, by rfl⟩ : syracuseStep 1071015 = 1606523) B1606523
theorem B1071039 : Blo 1068616 1071039 := bstep (se 1 (by rfl) ⟨803279, by rfl⟩ : syracuseStep 1071039 = 1606559) B1606559
theorem B1071311 : Blo 1068616 1071311 := bstep (se 1 (by rfl) ⟨803483, by rfl⟩ : syracuseStep 1071311 = 1606967) B1606967
theorem B1202431 : Blo 1068616 1202431 := bstep (se 1 (by rfl) ⟨901823, by rfl⟩ : syracuseStep 1202431 = 1803647) B1803647
theorem B1071431 : Blo 1068616 1071431 := bstep (se 1 (by rfl) ⟨803573, by rfl⟩ : syracuseStep 1071431 = 1607147) B1607147
theorem B5495131 : Blo 1068616 5495131 := bstep (se 1 (by rfl) ⟨4121348, by rfl⟩ : syracuseStep 5495131 = 8242697) B8242697
theorem B1071727 : Blo 1068616 1071727 := bstep (se 1 (by rfl) ⟨803795, by rfl⟩ : syracuseStep 1071727 = 1607591) B1607591
theorem B2284271 : Blo 1068616 2284271 := bstep (se 1 (by rfl) ⟨1713203, by rfl⟩ : syracuseStep 2284271 = 3426407) B3426407
theorem B1071867 : Blo 1068616 1071867 := bstep (se 1 (by rfl) ⟨803900, by rfl⟩ : syracuseStep 1071867 = 1607801) B1607801
theorem B1072231 : Blo 1068616 1072231 := bstep (se 1 (by rfl) ⟨804173, by rfl⟩ : syracuseStep 1072231 = 1608347) B1608347
theorem B1072255 : Blo 1068616 1072255 := bstep (se 1 (by rfl) ⟨804191, by rfl⟩ : syracuseStep 1072255 = 1608383) B1608383
theorem B1072295 : Blo 1068616 1072295 := bstep (se 1 (by rfl) ⟨804221, by rfl⟩ : syracuseStep 1072295 = 1608443) B1608443
theorem B2710847 : Blo 1068616 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B1072607 : Blo 1068616 1072607 := bstep (se 1 (by rfl) ⟨804455, by rfl⟩ : syracuseStep 1072607 = 1608911) B1608911
theorem B1203871 : Blo 1068616 1203871 := bstep (se 1 (by rfl) ⟨902903, by rfl⟩ : syracuseStep 1203871 = 1805807) B1805807
theorem B10280951 : Blo 1068616 10280951 := bstep (se 1 (by rfl) ⟨7710713, by rfl⟩ : syracuseStep 10280951 = 15421427) B15421427
theorem B1204987 : Blo 1068616 1204987 := bstep (se 1 (by rfl) ⟨903740, by rfl⟩ : syracuseStep 1204987 = 1807481) B1807481
theorem B12215123 : Blo 1068616 12215123 := bstep (se 1 (by rfl) ⟨9161342, by rfl⟩ : syracuseStep 12215123 = 18322685) B18322685
theorem B3859321 : Blo 1068616 3859321 := bstep (se 2 (by rfl) ⟨1447245, by rfl⟩ : syracuseStep 3859321 = 2894491) B2894491
theorem B21128471 : Blo 1068616 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B2713247 : Blo 1068616 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2713783 : Blo 1068616 2713783 := bstep (se 1 (by rfl) ⟨2035337, by rfl⟩ : syracuseStep 2713783 = 4070675) B4070675
theorem B9758987 : Blo 1068616 9758987 := bstep (se 1 (by rfl) ⟨7319240, by rfl⟩ : syracuseStep 9758987 = 14638481) B14638481
theorem B11561575 : Blo 1068616 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B5139263 : Blo 1068616 5139263 := bstep (se 1 (by rfl) ⟨3854447, by rfl⟩ : syracuseStep 5139263 = 7708895) B7708895
theorem B4125415 : Blo 1068616 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B1603049 : Blo 1068616 1603049 := bstep (se 2 (by rfl) ⟨601143, by rfl⟩ : syracuseStep 1603049 = 1202287) B1202287
theorem B19789433 : Blo 1068616 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B9140363 : Blo 1068616 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B3046697 : Blo 1068616 3046697 := bstep (se 2 (by rfl) ⟨1142511, by rfl⟩ : syracuseStep 3046697 = 2285023) B2285023
theorem B1605167 : Blo 1068616 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B1605275 : Blo 1068616 1605275 := bstep (se 1 (by rfl) ⟨1203956, by rfl⟩ : syracuseStep 1605275 = 2407913) B2407913
theorem B5209771 : Blo 1068616 5209771 := bstep (se 1 (by rfl) ⟨3907328, by rfl⟩ : syracuseStep 5209771 = 7814657) B7814657
theorem B70517081 : Blo 1068616 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B1606079 : Blo 1068616 1606079 := bstep (se 1 (by rfl) ⟨1204559, by rfl⟩ : syracuseStep 1606079 = 2409119) B2409119
theorem B9274013 : Blo 1068616 9274013 := bstep (se 3 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 9274013 = 3477755) B3477755
theorem B1606649 : Blo 1068616 1606649 := bstep (se 2 (by rfl) ⟨602493, by rfl⟩ : syracuseStep 1606649 = 1204987) B1204987
theorem B1606751 : Blo 1068616 1606751 := bstep (se 1 (by rfl) ⟨1205063, by rfl⟩ : syracuseStep 1606751 = 2410127) B2410127
theorem B5145761 : Blo 1068616 5145761 := bstep (se 2 (by rfl) ⟨1929660, by rfl⟩ : syracuseStep 5145761 = 3859321) B3859321
theorem B1804315 : Blo 1068616 1804315 := bstep (se 1 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 1804315 = 2706473) B2706473
theorem B8685739 : Blo 1068616 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B3606983 : Blo 1068616 3606983 := bstep (se 1 (by rfl) ⟨2705237, by rfl⟩ : syracuseStep 3606983 = 5410475) B5410475
theorem B4065983 : Blo 1068616 4065983 := bstep (se 1 (by rfl) ⟨3049487, by rfl⟩ : syracuseStep 4065983 = 6098975) B6098975
theorem B3050227 : Blo 1068616 3050227 := bstep (se 1 (by rfl) ⟨2287670, by rfl⟩ : syracuseStep 3050227 = 4575341) B4575341
theorem B1608815 : Blo 1068616 1608815 := bstep (se 1 (by rfl) ⟨1206611, by rfl⟩ : syracuseStep 1608815 = 2413223) B2413223
theorem B6098267 : Blo 1068616 6098267 := bstep (se 1 (by rfl) ⟨4573700, by rfl⟩ : syracuseStep 6098267 = 9147401) B9147401
theorem B4067455 : Blo 1068616 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B3608819 : Blo 1068616 3608819 := bstep (se 1 (by rfl) ⟨2706614, by rfl⟩ : syracuseStep 3608819 = 5413229) B5413229
theorem B1807231 : Blo 1068616 1807231 := bstep (se 1 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 1807231 = 2710847) B2710847
theorem B8918201 : Blo 1068616 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B6853967 : Blo 1068616 6853967 := bstep (se 1 (by rfl) ⟨5140475, by rfl⟩ : syracuseStep 6853967 = 10280951) B10280951
theorem B1808831 : Blo 1068616 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B1712191 : Blo 1068616 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B5644417 : Blo 1068616 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B1712831 : Blo 1068616 1712831 := bstep (se 1 (by rfl) ⟨1284623, by rfl⟩ : syracuseStep 1712831 = 2569247) B2569247
theorem B37104641 : Blo 1068616 37104641 := bstep (se 2 (by rfl) ⟨13914240, by rfl⟩ : syracuseStep 37104641 = 27828481) B27828481
theorem B3255743 : Blo 1068616 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B3616487 : Blo 1068616 3616487 := bstep (se 1 (by rfl) ⟨2712365, by rfl⟩ : syracuseStep 3616487 = 5424731) B5424731
theorem B1355935 : Blo 1068616 1355935 := bstep (se 1 (by rfl) ⟨1016951, by rfl⟩ : syracuseStep 1355935 = 2033903) B2033903
theorem B5484791 : Blo 1068616 5484791 := bstep (se 1 (by rfl) ⟨4113593, by rfl⟩ : syracuseStep 5484791 = 8227187) B8227187
theorem B55619921 : Blo 1068616 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B29307365 : Blo 1068616 29307365 := bstep (se 4 (by rfl) ⟨2747565, by rfl⟩ : syracuseStep 29307365 = 5495131) B5495131
theorem B2405375 : Blo 1068616 2405375 := bstep (se 1 (by rfl) ⟨1804031, by rfl⟩ : syracuseStep 2405375 = 3608063) B3608063
theorem B3618377 : Blo 1068616 3618377 := bstep (se 2 (by rfl) ⟨1356891, by rfl⟩ : syracuseStep 3618377 = 2713783) B2713783
theorem B15415433 : Blo 1068616 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B1521919 : Blo 1068616 1521919 := bstep (se 1 (by rfl) ⟨1141439, by rfl⟩ : syracuseStep 1521919 = 2282879) B2282879
theorem B4340051 : Blo 1068616 4340051 := bstep (se 1 (by rfl) ⟨3255038, by rfl⟩ : syracuseStep 4340051 = 6510077) B6510077
theorem B4569533 : Blo 1068616 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B2406959 : Blo 1068616 2406959 := bstep (se 1 (by rfl) ⟨1805219, by rfl⟩ : syracuseStep 2406959 = 3610439) B3610439
theorem B1522847 : Blo 1068616 1522847 := bstep (se 1 (by rfl) ⟨1142135, by rfl⟩ : syracuseStep 1522847 = 2284271) B2284271
theorem B8143415 : Blo 1068616 8143415 := bstep (se 1 (by rfl) ⟨6107561, by rfl⟩ : syracuseStep 8143415 = 12215123) B12215123
theorem B3851711 : Blo 1068616 3851711 := bstep (se 1 (by rfl) ⟨2888783, by rfl⟩ : syracuseStep 3851711 = 5777567) B5777567
theorem B6505991 : Blo 1068616 6505991 := bstep (se 1 (by rfl) ⟨4879493, by rfl⟩ : syracuseStep 6505991 = 9758987) B9758987
theorem B3426175 : Blo 1068616 3426175 := bstep (se 1 (by rfl) ⟨2569631, by rfl⟩ : syracuseStep 3426175 = 5139263) B5139263
theorem B2410559 : Blo 1068616 2410559 := bstep (se 1 (by rfl) ⟨1807919, by rfl⟩ : syracuseStep 2410559 = 3615839) B3615839
theorem B1068699 : Blo 1068616 1068699 := bstep (se 1 (by rfl) ⟨801524, by rfl⟩ : syracuseStep 1068699 = 1603049) B1603049
theorem B13192955 : Blo 1068616 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B13881287 : Blo 1068616 13881287 := bstep (se 1 (by rfl) ⟨10410965, by rfl⟩ : syracuseStep 13881287 = 20821931) B20821931
theorem B5787881 : Blo 1068616 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B4575683 : Blo 1068616 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B2413097 : Blo 1068616 2413097 := bstep (se 2 (by rfl) ⟨904911, by rfl⟩ : syracuseStep 2413097 = 1809823) B1809823
theorem B11555561 : Blo 1068616 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B1070111 : Blo 1068616 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1070183 : Blo 1068616 1070183 := bstep (se 1 (by rfl) ⟨802637, by rfl⟩ : syracuseStep 1070183 = 1605275) B1605275
theorem B9131615 : Blo 1068616 9131615 := bstep (se 1 (by rfl) ⟨6848711, by rfl⟩ : syracuseStep 9131615 = 13697423) B13697423
theorem B1627751 : Blo 1068616 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B4118393 : Blo 1068616 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2709551 : Blo 1068616 2709551 := bstep (se 1 (by rfl) ⟨2032163, by rfl⟩ : syracuseStep 2709551 = 4064327) B4064327
theorem B1071195 : Blo 1068616 1071195 := bstep (se 1 (by rfl) ⟨803396, by rfl⟩ : syracuseStep 1071195 = 1606793) B1606793
theorem B1071583 : Blo 1068616 1071583 := bstep (se 1 (by rfl) ⟨803687, by rfl⟩ : syracuseStep 1071583 = 1607375) B1607375
theorem B1071615 : Blo 1068616 1071615 := bstep (se 1 (by rfl) ⟨803711, by rfl⟩ : syracuseStep 1071615 = 1607423) B1607423
theorem B1072063 : Blo 1068616 1072063 := bstep (se 1 (by rfl) ⟨804047, by rfl⟩ : syracuseStep 1072063 = 1608095) B1608095
theorem B1072127 : Blo 1068616 1072127 := bstep (se 1 (by rfl) ⟨804095, by rfl⟩ : syracuseStep 1072127 = 1608191) B1608191
theorem B1072431 : Blo 1068616 1072431 := bstep (se 1 (by rfl) ⟨804323, by rfl⟩ : syracuseStep 1072431 = 1608647) B1608647
theorem B1072447 : Blo 1068616 1072447 := bstep (se 1 (by rfl) ⟨804335, by rfl⟩ : syracuseStep 1072447 = 1608671) B1608671
theorem B9134279 : Blo 1068616 9134279 := bstep (se 1 (by rfl) ⟨6850709, by rfl⟩ : syracuseStep 9134279 = 13701419) B13701419
theorem B26075519 : Blo 1068616 26075519 := bstep (se 1 (by rfl) ⟨19556639, by rfl⟩ : syracuseStep 26075519 = 39113279) B39113279
theorem B2286407 : Blo 1068616 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B2712953 : Blo 1068616 2712953 := bstep (se 2 (by rfl) ⟨1017357, by rfl⟩ : syracuseStep 2712953 = 2034715) B2034715
theorem B1205743 : Blo 1068616 1205743 := bstep (se 1 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 1205743 = 1808615) B1808615
theorem B14708015 : Blo 1068616 14708015 := bstep (se 1 (by rfl) ⟨11031011, by rfl⟩ : syracuseStep 14708015 = 22062023) B22062023
theorem B7433579 : Blo 1068616 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B14085647 : Blo 1068616 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B5500553 : Blo 1068616 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B29290733 : Blo 1068616 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B8680553 : Blo 1068616 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B1603241 : Blo 1068616 1603241 := bstep (se 2 (by rfl) ⟨601215, by rfl⟩ : syracuseStep 1603241 = 1202431) B1202431
theorem B1604303 : Blo 1068616 1604303 := bstep (se 1 (by rfl) ⟨1203227, by rfl⟩ : syracuseStep 1604303 = 2406455) B2406455
theorem B1604351 : Blo 1068616 1604351 := bstep (se 1 (by rfl) ⟨1203263, by rfl⟩ : syracuseStep 1604351 = 2406527) B2406527
theorem B6093575 : Blo 1068616 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B2031131 : Blo 1068616 2031131 := bstep (se 1 (by rfl) ⟨1523348, by rfl⟩ : syracuseStep 2031131 = 3046697) B3046697
theorem B1605161 : Blo 1068616 1605161 := bstep (se 2 (by rfl) ⟨601935, by rfl⟩ : syracuseStep 1605161 = 1203871) B1203871
theorem B6946361 : Blo 1068616 6946361 := bstep (se 2 (by rfl) ⟨2604885, by rfl⟩ : syracuseStep 6946361 = 5209771) B5209771
theorem B5865199 : Blo 1068616 5865199 := bstep (se 1 (by rfl) ⟨4398899, by rfl⟩ : syracuseStep 5865199 = 8797799) B8797799
theorem B1605371 : Blo 1068616 1605371 := bstep (se 1 (by rfl) ⟨1204028, by rfl⟩ : syracuseStep 1605371 = 2408057) B2408057
theorem B1605503 : Blo 1068616 1605503 := bstep (se 1 (by rfl) ⟨1204127, by rfl⟩ : syracuseStep 1605503 = 2408255) B2408255
theorem B1607039 : Blo 1068616 1607039 := bstep (se 1 (by rfl) ⟨1205279, by rfl⟩ : syracuseStep 1607039 = 2410559) B2410559
theorem B1607657 : Blo 1068616 1607657 := bstep (se 2 (by rfl) ⟨602871, by rfl⟩ : syracuseStep 1607657 = 1205743) B1205743
theorem B4065511 : Blo 1068616 4065511 := bstep (se 1 (by rfl) ⟨3049133, by rfl⟩ : syracuseStep 4065511 = 6098267) B6098267
theorem B3050455 : Blo 1068616 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B1608731 : Blo 1068616 1608731 := bstep (se 1 (by rfl) ⟨1206548, by rfl⟩ : syracuseStep 1608731 = 2413097) B2413097
theorem B7703707 : Blo 1068616 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B4066969 : Blo 1068616 4066969 := bstep (se 2 (by rfl) ⟨1525113, by rfl⟩ : syracuseStep 4066969 = 3050227) B3050227
theorem B1085167 : Blo 1068616 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B1806367 : Blo 1068616 1806367 := bstep (se 1 (by rfl) ⟨1354775, by rfl⟩ : syracuseStep 1806367 = 2709551) B2709551
theorem B1807913 : Blo 1068616 1807913 := bstep (se 2 (by rfl) ⟨677967, by rfl⟩ : syracuseStep 1807913 = 1355935) B1355935
theorem B1808635 : Blo 1068616 1808635 := bstep (se 1 (by rfl) ⟨1356476, by rfl⟩ : syracuseStep 1808635 = 2712953) B2712953
theorem B2170495 : Blo 1068616 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B19538243 : Blo 1068616 19538243 := bstep (se 1 (by rfl) ⟨14653682, by rfl⟩ : syracuseStep 19538243 = 29307365) B29307365
theorem B2893367 : Blo 1068616 2893367 := bstep (se 1 (by rfl) ⟨2170025, by rfl⟩ : syracuseStep 2893367 = 4340051) B4340051
theorem B1354087 : Blo 1068616 1354087 := bstep (se 1 (by rfl) ⟨1015565, by rfl⟩ : syracuseStep 1354087 = 2031131) B2031131
theorem B4630907 : Blo 1068616 4630907 := bstep (se 1 (by rfl) ⟨3473180, by rfl⟩ : syracuseStep 4630907 = 6946361) B6946361
theorem B14626109 : Blo 1068616 14626109 := bstep (se 3 (by rfl) ⟨2742395, by rfl⟩ : syracuseStep 14626109 = 5484791) B5484791
theorem B2567807 : Blo 1068616 2567807 := bstep (se 1 (by rfl) ⟨1925855, by rfl⟩ : syracuseStep 2567807 = 3851711) B3851711
theorem B4337327 : Blo 1068616 4337327 := bstep (se 1 (by rfl) ⟨3252995, by rfl⟩ : syracuseStep 4337327 = 6505991) B6505991
theorem B2404655 : Blo 1068616 2404655 := bstep (se 1 (by rfl) ⟨1803491, by rfl⟩ : syracuseStep 2404655 = 3606983) B3606983
theorem B8795303 : Blo 1068616 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B4568233 : Blo 1068616 4568233 := bstep (se 2 (by rfl) ⟨1713087, by rfl⟩ : syracuseStep 4568233 = 3426175) B3426175
theorem B9254191 : Blo 1068616 9254191 := bstep (se 1 (by rfl) ⟨6940643, by rfl⟩ : syracuseStep 9254191 = 13881287) B13881287
theorem B2405753 : Blo 1068616 2405753 := bstep (se 2 (by rfl) ⟨902157, by rfl⟩ : syracuseStep 2405753 = 1804315) B1804315
theorem B2405879 : Blo 1068616 2405879 := bstep (se 1 (by rfl) ⟨1804409, by rfl⟩ : syracuseStep 2405879 = 3608819) B3608819
theorem B11580985 : Blo 1068616 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B5945467 : Blo 1068616 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B4569311 : Blo 1068616 4569311 := bstep (se 1 (by rfl) ⟨3426983, by rfl⟩ : syracuseStep 4569311 = 6853967) B6853967
theorem B5423273 : Blo 1068616 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B17383679 : Blo 1068616 17383679 := bstep (se 1 (by rfl) ⟨13037759, by rfl⟩ : syracuseStep 17383679 = 26075519) B26075519
theorem B1524271 : Blo 1068616 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B2409641 : Blo 1068616 2409641 := bstep (se 2 (by rfl) ⟨903615, by rfl⟩ : syracuseStep 2409641 = 1807231) B1807231
theorem B18270197 : Blo 1068616 18270197 := bstep (se 5 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 18270197 = 1712831) B1712831
theorem B9390431 : Blo 1068616 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B2410991 : Blo 1068616 2410991 := bstep (se 1 (by rfl) ⟨1808243, by rfl⟩ : syracuseStep 2410991 = 3616487) B3616487
theorem B37079947 : Blo 1068616 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B5787035 : Blo 1068616 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B2412251 : Blo 1068616 2412251 := bstep (se 1 (by rfl) ⟨1809188, by rfl⟩ : syracuseStep 2412251 = 3618377) B3618377
theorem B1068827 : Blo 1068616 1068827 := bstep (se 1 (by rfl) ⟨801620, by rfl⟩ : syracuseStep 1068827 = 1603241) B1603241
theorem B31281061 : Blo 1068616 31281061 := bstep (se 4 (by rfl) ⟨2932599, by rfl⟩ : syracuseStep 31281061 = 5865199) B5865199
theorem B10276955 : Blo 1068616 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B14668141 : Blo 1068616 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1069535 : Blo 1068616 1069535 := bstep (se 1 (by rfl) ⟨802151, by rfl⟩ : syracuseStep 1069535 = 1604303) B1604303
theorem B1069567 : Blo 1068616 1069567 := bstep (se 1 (by rfl) ⟨802175, by rfl⟩ : syracuseStep 1069567 = 1604351) B1604351
theorem B1070107 : Blo 1068616 1070107 := bstep (se 1 (by rfl) ⟨802580, by rfl⟩ : syracuseStep 1070107 = 1605161) B1605161
theorem B1070247 : Blo 1068616 1070247 := bstep (se 1 (by rfl) ⟨802685, by rfl⟩ : syracuseStep 1070247 = 1605371) B1605371
theorem B1070335 : Blo 1068616 1070335 := bstep (se 1 (by rfl) ⟨802751, by rfl⟩ : syracuseStep 1070335 = 1605503) B1605503
theorem B2282921 : Blo 1068616 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B7525889 : Blo 1068616 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B47011387 : Blo 1068616 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B1070719 : Blo 1068616 1070719 := bstep (se 1 (by rfl) ⟨803039, by rfl⟩ : syracuseStep 1070719 = 1606079) B1606079
theorem B5428943 : Blo 1068616 5428943 := bstep (se 1 (by rfl) ⟨4071707, by rfl⟩ : syracuseStep 5428943 = 8143415) B8143415
theorem B6182675 : Blo 1068616 6182675 := bstep (se 1 (by rfl) ⟨4637006, by rfl⟩ : syracuseStep 6182675 = 9274013) B9274013
theorem B1071099 : Blo 1068616 1071099 := bstep (se 1 (by rfl) ⟨803324, by rfl⟩ : syracuseStep 1071099 = 1606649) B1606649
theorem B1071167 : Blo 1068616 1071167 := bstep (se 1 (by rfl) ⟨803375, by rfl⟩ : syracuseStep 1071167 = 1606751) B1606751
theorem B3430507 : Blo 1068616 3430507 := bstep (se 1 (by rfl) ⟨2572880, by rfl⟩ : syracuseStep 3430507 = 5145761) B5145761
theorem B2710655 : Blo 1068616 2710655 := bstep (se 1 (by rfl) ⟨2032991, by rfl⟩ : syracuseStep 2710655 = 4065983) B4065983
theorem B1072543 : Blo 1068616 1072543 := bstep (se 1 (by rfl) ⟨804407, by rfl⟩ : syracuseStep 1072543 = 1608815) B1608815
theorem B3858587 : Blo 1068616 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B156885493 : Blo 1068616 156885493 := bstep (se 5 (by rfl) ⟨7354007, by rfl⟩ : syracuseStep 156885493 = 14708015) B14708015
theorem B6087743 : Blo 1068616 6087743 := bstep (se 1 (by rfl) ⟨4565807, by rfl⟩ : syracuseStep 6087743 = 9131615) B9131615
theorem B2745595 : Blo 1068616 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B1205887 : Blo 1068616 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B6089519 : Blo 1068616 6089519 := bstep (se 1 (by rfl) ⟨4567139, by rfl⟩ : syracuseStep 6089519 = 9134279) B9134279
theorem B24736427 : Blo 1068616 24736427 := bstep (se 1 (by rfl) ⟨18552320, by rfl⟩ : syracuseStep 24736427 = 37104641) B37104641
theorem B19527155 : Blo 1068616 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B2029225 : Blo 1068616 2029225 := bstep (se 2 (by rfl) ⟨760959, by rfl⟩ : syracuseStep 2029225 = 1521919) B1521919
theorem B4060925 : Blo 1068616 4060925 := bstep (se 3 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 4060925 = 1522847) B1522847
theorem B1603583 : Blo 1068616 1603583 := bstep (se 1 (by rfl) ⟨1202687, by rfl⟩ : syracuseStep 1603583 = 2405375) B2405375
theorem B19822877 : Blo 1068616 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B3046355 : Blo 1068616 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B1604639 : Blo 1068616 1604639 := bstep (se 1 (by rfl) ⟨1203479, by rfl⟩ : syracuseStep 1604639 = 2406959) B2406959
theorem B4062383 : Blo 1068616 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B2032361 : Blo 1068616 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B1606427 : Blo 1068616 1606427 := bstep (se 1 (by rfl) ⟨1204820, by rfl⟩ : syracuseStep 1606427 = 2409641) B2409641
theorem B6260287 : Blo 1068616 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B1607327 : Blo 1068616 1607327 := bstep (se 1 (by rfl) ⟨1205495, by rfl⟩ : syracuseStep 1607327 = 2410991) B2410991
theorem B1607849 : Blo 1068616 1607849 := bstep (se 2 (by rfl) ⟨602943, by rfl⟩ : syracuseStep 1607849 = 1205887) B1205887
theorem B1608167 : Blo 1068616 1608167 := bstep (se 1 (by rfl) ⟨1206125, by rfl⟩ : syracuseStep 1608167 = 2412251) B2412251
theorem B6851303 : Blo 1068616 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B1805449 : Blo 1068616 1805449 := bstep (se 2 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 1805449 = 1354087) B1354087
theorem B5017259 : Blo 1068616 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B4067273 : Blo 1068616 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B197759717 : Blo 1068616 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B1807103 : Blo 1068616 1807103 := bstep (se 1 (by rfl) ⟨1355327, by rfl⟩ : syracuseStep 1807103 = 2710655) B2710655
theorem B1446889 : Blo 1068616 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B3087271 : Blo 1068616 3087271 := bstep (se 1 (by rfl) ⟨2315453, by rfl⟩ : syracuseStep 3087271 = 4630907) B4630907
theorem B1711871 : Blo 1068616 1711871 := bstep (se 1 (by rfl) ⟨1283903, by rfl⟩ : syracuseStep 1711871 = 2567807) B2567807
theorem B2891551 : Blo 1068616 2891551 := bstep (se 1 (by rfl) ⟨2168663, by rfl⟩ : syracuseStep 2891551 = 4337327) B4337327
theorem B16490951 : Blo 1068616 16490951 := bstep (se 1 (by rfl) ⟨12368213, by rfl⟩ : syracuseStep 16490951 = 24736427) B24736427
theorem B11575973 : Blo 1068616 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B13018103 : Blo 1068616 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B13215251 : Blo 1068616 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B3615515 : Blo 1068616 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B5420681 : Blo 1068616 5420681 := bstep (se 2 (by rfl) ⟨2032755, by rfl⟩ : syracuseStep 5420681 = 4065511) B4065511
theorem B1521947 : Blo 1068616 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B3619295 : Blo 1068616 3619295 := bstep (se 1 (by rfl) ⟨2714471, by rfl⟩ : syracuseStep 3619295 = 5428943) B5428943
theorem B7715645 : Blo 1068616 7715645 := bstep (se 3 (by rfl) ⟨1446683, by rfl⟩ : syracuseStep 7715645 = 2893367) B2893367
theorem B10271609 : Blo 1068616 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B5422625 : Blo 1068616 5422625 := bstep (se 2 (by rfl) ⟨2033484, by rfl⟩ : syracuseStep 5422625 = 4066969) B4066969
theorem B2408489 : Blo 1068616 2408489 := bstep (se 2 (by rfl) ⟨903183, by rfl⟩ : syracuseStep 2408489 = 1806367) B1806367
theorem B2572391 : Blo 1068616 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B13025495 : Blo 1068616 13025495 := bstep (se 1 (by rfl) ⟨9769121, by rfl⟩ : syracuseStep 13025495 = 19538243) B19538243
theorem B12338921 : Blo 1068616 12338921 := bstep (se 2 (by rfl) ⟨4627095, by rfl⟩ : syracuseStep 12338921 = 9254191) B9254191
theorem B9750739 : Blo 1068616 9750739 := bstep (se 1 (by rfl) ⟨7313054, by rfl⟩ : syracuseStep 9750739 = 14626109) B14626109
theorem B2705633 : Blo 1068616 2705633 := bstep (se 2 (by rfl) ⟨1014612, by rfl⟩ : syracuseStep 2705633 = 2029225) B2029225
theorem B4574009 : Blo 1068616 4574009 := bstep (se 2 (by rfl) ⟨1715253, by rfl⟩ : syracuseStep 4574009 = 3430507) B3430507
theorem B2411513 : Blo 1068616 2411513 := bstep (se 2 (by rfl) ⟨904317, by rfl⟩ : syracuseStep 2411513 = 1808635) B1808635
theorem B2707283 : Blo 1068616 2707283 := bstep (se 1 (by rfl) ⟨2030462, by rfl⟩ : syracuseStep 2707283 = 4060925) B4060925
theorem B1069055 : Blo 1068616 1069055 := bstep (se 1 (by rfl) ⟨801791, by rfl⟩ : syracuseStep 1069055 = 1603583) B1603583
theorem B1069759 : Blo 1068616 1069759 := bstep (se 1 (by rfl) ⟨802319, by rfl⟩ : syracuseStep 1069759 = 1604639) B1604639
theorem B2708255 : Blo 1068616 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B11589119 : Blo 1068616 11589119 := bstep (se 1 (by rfl) ⟨8691839, by rfl⟩ : syracuseStep 11589119 = 17383679) B17383679
theorem B209180657 : Blo 1068616 209180657 := bstep (se 2 (by rfl) ⟨78442746, by rfl⟩ : syracuseStep 209180657 = 156885493) B156885493
theorem B1071359 : Blo 1068616 1071359 := bstep (se 1 (by rfl) ⟨803519, by rfl⟩ : syracuseStep 1071359 = 1607039) B1607039
theorem B1071771 : Blo 1068616 1071771 := bstep (se 1 (by rfl) ⟨803828, by rfl⟩ : syracuseStep 1071771 = 1607657) B1607657
theorem B12180131 : Blo 1068616 12180131 := bstep (se 1 (by rfl) ⟨9135098, by rfl⟩ : syracuseStep 12180131 = 18270197) B18270197
theorem B1072487 : Blo 1068616 1072487 := bstep (se 1 (by rfl) ⟨804365, by rfl⟩ : syracuseStep 1072487 = 1608731) B1608731
theorem B3858023 : Blo 1068616 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B1205275 : Blo 1068616 1205275 := bstep (se 1 (by rfl) ⟨903956, by rfl⟩ : syracuseStep 1205275 = 1807913) B1807913
theorem B4121783 : Blo 1068616 4121783 := bstep (se 1 (by rfl) ⟨3091337, by rfl⟩ : syracuseStep 4121783 = 6182675) B6182675
theorem B41708081 : Blo 1068616 41708081 := bstep (se 2 (by rfl) ⟨15640530, by rfl⟩ : syracuseStep 41708081 = 31281061) B31281061
theorem B19557521 : Blo 1068616 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B4058495 : Blo 1068616 4058495 := bstep (se 1 (by rfl) ⟨3043871, by rfl⟩ : syracuseStep 4058495 = 6087743) B6087743
theorem B14643173 : Blo 1068616 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B6090977 : Blo 1068616 6090977 := bstep (se 2 (by rfl) ⟨2284116, by rfl⟩ : syracuseStep 6090977 = 4568233) B4568233
theorem B4059679 : Blo 1068616 4059679 := bstep (se 1 (by rfl) ⟨3044759, by rfl⟩ : syracuseStep 4059679 = 6089519) B6089519
theorem B62681849 : Blo 1068616 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B7927289 : Blo 1068616 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B1603103 : Blo 1068616 1603103 := bstep (se 1 (by rfl) ⟨1202327, by rfl⟩ : syracuseStep 1603103 = 2404655) B2404655
theorem B61765253 : Blo 1068616 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B5863535 : Blo 1068616 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B1603835 : Blo 1068616 1603835 := bstep (se 1 (by rfl) ⟨1202876, by rfl⟩ : syracuseStep 1603835 = 2405753) B2405753
theorem B1603919 : Blo 1068616 1603919 := bstep (se 1 (by rfl) ⟨1202939, by rfl⟩ : syracuseStep 1603919 = 2405879) B2405879
theorem B3046207 : Blo 1068616 3046207 := bstep (se 1 (by rfl) ⟨2284655, by rfl⟩ : syracuseStep 3046207 = 4569311) B4569311
theorem B2030903 : Blo 1068616 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B1605659 : Blo 1068616 1605659 := bstep (se 1 (by rfl) ⟨1204244, by rfl⟩ : syracuseStep 1605659 = 2408489) B2408489
theorem B34734653 : Blo 1068616 34734653 := bstep (se 3 (by rfl) ⟨6512747, by rfl⟩ : syracuseStep 34734653 = 13025495) B13025495
theorem B8225947 : Blo 1068616 8225947 := bstep (se 1 (by rfl) ⟨6169460, by rfl⟩ : syracuseStep 8225947 = 12338921) B12338921
theorem B1607033 : Blo 1068616 1607033 := bstep (se 2 (by rfl) ⟨602637, by rfl⟩ : syracuseStep 1607033 = 1205275) B1205275
theorem B1803755 : Blo 1068616 1803755 := bstep (se 1 (by rfl) ⟨1352816, by rfl⟩ : syracuseStep 1803755 = 2705633) B2705633
theorem B3049339 : Blo 1068616 3049339 := bstep (se 1 (by rfl) ⟨2287004, by rfl⟩ : syracuseStep 3049339 = 4574009) B4574009
theorem B1607675 : Blo 1068616 1607675 := bstep (se 1 (by rfl) ⟨1205756, by rfl⟩ : syracuseStep 1607675 = 2411513) B2411513
theorem B3344839 : Blo 1068616 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B1804855 : Blo 1068616 1804855 := bstep (se 1 (by rfl) ⟨1353641, by rfl⟩ : syracuseStep 1804855 = 2707283) B2707283
theorem B1805503 : Blo 1068616 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B5412905 : Blo 1068616 5412905 := bstep (se 2 (by rfl) ⟨2029839, by rfl⟩ : syracuseStep 5412905 = 4059679) B4059679
theorem B111221549 : Blo 1068616 111221549 := bstep (se 3 (by rfl) ⟨20854040, by rfl⟩ : syracuseStep 111221549 = 41708081) B41708081
theorem B41787899 : Blo 1068616 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B3613787 : Blo 1068616 3613787 := bstep (se 1 (by rfl) ⟨2710340, by rfl⟩ : syracuseStep 3613787 = 5420681) B5420681
theorem B3909023 : Blo 1068616 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B1353935 : Blo 1068616 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B3615083 : Blo 1068616 3615083 := bstep (se 1 (by rfl) ⟨2711312, by rfl⟩ : syracuseStep 3615083 = 5422625) B5422625
theorem B1714927 : Blo 1068616 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B1354907 : Blo 1068616 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B4567535 : Blo 1068616 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B131839811 : Blo 1068616 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B2407265 : Blo 1068616 2407265 := bstep (se 2 (by rfl) ⟨902724, by rfl⟩ : syracuseStep 2407265 = 1805449) B1805449
theorem B16465445 : Blo 1068616 16465445 := bstep (se 4 (by rfl) ⟨1543635, by rfl⟩ : syracuseStep 16465445 = 3087271) B3087271
theorem B2572015 : Blo 1068616 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B84557749 : Blo 1068616 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B10993967 : Blo 1068616 10993967 := bstep (se 1 (by rfl) ⟨8245475, by rfl⟩ : syracuseStep 10993967 = 16490951) B16490951
theorem B7717315 : Blo 1068616 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B2410343 : Blo 1068616 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B2705663 : Blo 1068616 2705663 := bstep (se 1 (by rfl) ⟨2029247, by rfl⟩ : syracuseStep 2705663 = 4058495) B4058495
theorem B1068735 : Blo 1068616 1068735 := bstep (se 1 (by rfl) ⟨801551, by rfl⟩ : syracuseStep 1068735 = 1603103) B1603103
theorem B41176835 : Blo 1068616 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B1069223 : Blo 1068616 1069223 := bstep (se 1 (by rfl) ⟨801917, by rfl⟩ : syracuseStep 1069223 = 1603835) B1603835
theorem B1069279 : Blo 1068616 1069279 := bstep (se 1 (by rfl) ⟨801959, by rfl⟩ : syracuseStep 1069279 = 1603919) B1603919
theorem B2412863 : Blo 1068616 2412863 := bstep (se 1 (by rfl) ⟨1809647, by rfl⟩ : syracuseStep 2412863 = 3619295) B3619295
theorem B3855401 : Blo 1068616 3855401 := bstep (se 2 (by rfl) ⟨1445775, by rfl⟩ : syracuseStep 3855401 = 2891551) B2891551
theorem B1070951 : Blo 1068616 1070951 := bstep (se 1 (by rfl) ⟨803213, by rfl⟩ : syracuseStep 1070951 = 1606427) B1606427
theorem B1071551 : Blo 1068616 1071551 := bstep (se 1 (by rfl) ⟨803663, by rfl⟩ : syracuseStep 1071551 = 1607327) B1607327
theorem B1071899 : Blo 1068616 1071899 := bstep (se 1 (by rfl) ⟨803924, by rfl⟩ : syracuseStep 1071899 = 1607849) B1607849
theorem B1072111 : Blo 1068616 1072111 := bstep (se 1 (by rfl) ⟨804083, by rfl⟩ : syracuseStep 1072111 = 1608167) B1608167
theorem B8347049 : Blo 1068616 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B2711515 : Blo 1068616 2711515 := bstep (se 1 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 2711515 = 4067273) B4067273
theorem B13000985 : Blo 1068616 13000985 := bstep (se 2 (by rfl) ⟨4875369, by rfl⟩ : syracuseStep 13000985 = 9750739) B9750739
theorem B1204735 : Blo 1068616 1204735 := bstep (se 1 (by rfl) ⟨903551, by rfl⟩ : syracuseStep 1204735 = 1807103) B1807103
theorem B7726079 : Blo 1068616 7726079 := bstep (se 1 (by rfl) ⟨5794559, by rfl⟩ : syracuseStep 7726079 = 11589119) B11589119
theorem B139453771 : Blo 1068616 139453771 := bstep (se 1 (by rfl) ⟨104590328, by rfl⟩ : syracuseStep 139453771 = 209180657) B209180657
theorem B8120087 : Blo 1068616 8120087 := bstep (se 1 (by rfl) ⟨6090065, by rfl⟩ : syracuseStep 8120087 = 12180131) B12180131
theorem B1141247 : Blo 1068616 1141247 := bstep (se 1 (by rfl) ⟨855935, by rfl⟩ : syracuseStep 1141247 = 1711871) B1711871
theorem B8678735 : Blo 1068616 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B4058525 : Blo 1068616 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B2747855 : Blo 1068616 2747855 := bstep (se 1 (by rfl) ⟨2060891, by rfl⟩ : syracuseStep 2747855 = 4121783) B4121783
theorem B8810167 : Blo 1068616 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B1929185 : Blo 1068616 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B13038347 : Blo 1068616 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B9762115 : Blo 1068616 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B4060651 : Blo 1068616 4060651 := bstep (se 1 (by rfl) ⟨3045488, by rfl⟩ : syracuseStep 4060651 = 6090977) B6090977
theorem B4061609 : Blo 1068616 4061609 := bstep (se 2 (by rfl) ⟨1523103, by rfl⟩ : syracuseStep 4061609 = 3046207) B3046207
theorem B5143763 : Blo 1068616 5143763 := bstep (se 1 (by rfl) ⟨3857822, by rfl⟩ : syracuseStep 5143763 = 7715645) B7715645
theorem B6847739 : Blo 1068616 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B10289753 : Blo 1068616 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B1606313 : Blo 1068616 1606313 := bstep (se 2 (by rfl) ⟨602367, by rfl⟩ : syracuseStep 1606313 = 1204735) B1204735
theorem B1606895 : Blo 1068616 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B1803775 : Blo 1068616 1803775 := bstep (se 1 (by rfl) ⟨1352831, by rfl⟩ : syracuseStep 1803775 = 2705663) B2705663
theorem B4065785 : Blo 1068616 4065785 := bstep (se 2 (by rfl) ⟨1524669, by rfl⟩ : syracuseStep 4065785 = 3049339) B3049339
theorem B1608575 : Blo 1068616 1608575 := bstep (se 1 (by rfl) ⟨1206431, by rfl⟩ : syracuseStep 1608575 = 2412863) B2412863
theorem B3608603 : Blo 1068616 3608603 := bstep (se 1 (by rfl) ⟨2706452, by rfl⟩ : syracuseStep 3608603 = 5412905) B5412905
theorem B27858599 : Blo 1068616 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B3610493 : Blo 1068616 3610493 := bstep (se 3 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 3610493 = 1353935) B1353935
theorem B5150719 : Blo 1068616 5150719 := bstep (se 1 (by rfl) ⟨3863039, by rfl⟩ : syracuseStep 5150719 = 7726079) B7726079
theorem B5413391 : Blo 1068616 5413391 := bstep (se 1 (by rfl) ⟨4060043, by rfl⟩ : syracuseStep 5413391 = 8120087) B8120087
theorem B13016153 : Blo 1068616 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B5414201 : Blo 1068616 5414201 := bstep (se 2 (by rfl) ⟨2030325, by rfl⟩ : syracuseStep 5414201 = 4060651) B4060651
theorem B1286123 : Blo 1068616 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B3613085 : Blo 1068616 3613085 := bstep (se 3 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 3613085 = 1354907) B1354907
theorem B8692231 : Blo 1068616 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B87893207 : Blo 1068616 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B4565159 : Blo 1068616 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B3615353 : Blo 1068616 3615353 := bstep (se 2 (by rfl) ⟨1355757, by rfl⟩ : syracuseStep 3615353 = 2711515) B2711515
theorem B185938361 : Blo 1068616 185938361 := bstep (se 2 (by rfl) ⟨69726885, by rfl⟩ : syracuseStep 185938361 = 139453771) B139453771
theorem B2570267 : Blo 1068616 2570267 := bstep (se 1 (by rfl) ⟨1927700, by rfl⟩ : syracuseStep 2570267 = 3855401) B3855401
theorem B2406473 : Blo 1068616 2406473 := bstep (se 2 (by rfl) ⟨902427, by rfl⟩ : syracuseStep 2406473 = 1804855) B1804855
theorem B2407337 : Blo 1068616 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B11746889 : Blo 1068616 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B8667323 : Blo 1068616 8667323 := bstep (se 1 (by rfl) ⟨6500492, by rfl⟩ : syracuseStep 8667323 = 13000985) B13000985
theorem B2409191 : Blo 1068616 2409191 := bstep (se 1 (by rfl) ⟨1806893, by rfl⟩ : syracuseStep 2409191 = 3613787) B3613787
theorem B2606015 : Blo 1068616 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B2410055 : Blo 1068616 2410055 := bstep (se 1 (by rfl) ⟨1807541, by rfl⟩ : syracuseStep 2410055 = 3615083) B3615083
theorem B5785823 : Blo 1068616 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B2705683 : Blo 1068616 2705683 := bstep (se 1 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 2705683 = 4058525) B4058525
theorem B71356565 : Blo 1068616 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B2707739 : Blo 1068616 2707739 := bstep (se 1 (by rfl) ⟨2030804, by rfl⟩ : syracuseStep 2707739 = 4061609) B4061609
theorem B3429175 : Blo 1068616 3429175 := bstep (se 1 (by rfl) ⟨2571881, by rfl⟩ : syracuseStep 3429175 = 5143763) B5143763
theorem B3429353 : Blo 1068616 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B112743665 : Blo 1068616 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B1070439 : Blo 1068616 1070439 := bstep (se 1 (by rfl) ⟨802829, by rfl⟩ : syracuseStep 1070439 = 1605659) B1605659
theorem B7329311 : Blo 1068616 7329311 := bstep (se 1 (by rfl) ⟨5496983, by rfl⟩ : syracuseStep 7329311 = 10993967) B10993967
theorem B23156435 : Blo 1068616 23156435 := bstep (se 1 (by rfl) ⟨17367326, by rfl⟩ : syracuseStep 23156435 = 34734653) B34734653
theorem B1071355 : Blo 1068616 1071355 := bstep (se 1 (by rfl) ⟨803516, by rfl⟩ : syracuseStep 1071355 = 1607033) B1607033
theorem B1202503 : Blo 1068616 1202503 := bstep (se 1 (by rfl) ⟨901877, by rfl⟩ : syracuseStep 1202503 = 1803755) B1803755
theorem B1071783 : Blo 1068616 1071783 := bstep (se 1 (by rfl) ⟨803837, by rfl⟩ : syracuseStep 1071783 = 1607675) B1607675
theorem B10967929 : Blo 1068616 10967929 := bstep (se 2 (by rfl) ⟨4112973, by rfl⟩ : syracuseStep 10967929 = 8225947) B8225947
theorem B27451223 : Blo 1068616 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B2286569 : Blo 1068616 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B74147699 : Blo 1068616 74147699 := bstep (se 1 (by rfl) ⟨55610774, by rfl⟩ : syracuseStep 74147699 = 111221549) B111221549
theorem B5564699 : Blo 1068616 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B3043325 : Blo 1068616 3043325 := bstep (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) B1141247
theorem B1831903 : Blo 1068616 1831903 := bstep (se 1 (by rfl) ⟨1373927, by rfl⟩ : syracuseStep 1831903 = 2747855) B2747855
theorem B3045023 : Blo 1068616 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1604843 : Blo 1068616 1604843 := bstep (se 1 (by rfl) ⟨1203632, by rfl⟩ : syracuseStep 1604843 = 2407265) B2407265
theorem B10976963 : Blo 1068616 10976963 := bstep (se 1 (by rfl) ⟨8232722, by rfl⟩ : syracuseStep 10976963 = 16465445) B16465445
theorem B190284173 : Blo 1068616 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B1606127 : Blo 1068616 1606127 := bstep (se 1 (by rfl) ⟨1204595, by rfl⟩ : syracuseStep 1606127 = 2409191) B2409191
theorem B1606703 : Blo 1068616 1606703 := bstep (se 1 (by rfl) ⟨1205027, by rfl⟩ : syracuseStep 1606703 = 2410055) B2410055
theorem B6949373 : Blo 1068616 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B6097517 : Blo 1068616 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B1805159 : Blo 1068616 1805159 := bstep (se 1 (by rfl) ⟨1353869, by rfl⟩ : syracuseStep 1805159 = 2707739) B2707739
theorem B3607577 : Blo 1068616 3607577 := bstep (se 2 (by rfl) ⟨1352841, by rfl⟩ : syracuseStep 3607577 = 2705683) B2705683
theorem B4886207 : Blo 1068616 4886207 := bstep (se 1 (by rfl) ⟨3664655, by rfl⟩ : syracuseStep 4886207 = 7329311) B7329311
theorem B15437623 : Blo 1068616 15437623 := bstep (se 1 (by rfl) ⟨11578217, by rfl⟩ : syracuseStep 15437623 = 23156435) B23156435
theorem B3608927 : Blo 1068616 3608927 := bstep (se 1 (by rfl) ⟨2706695, by rfl⟩ : syracuseStep 3608927 = 5413391) B5413391
theorem B58495621 : Blo 1068616 58495621 := bstep (se 4 (by rfl) ⟨5483964, by rfl⟩ : syracuseStep 58495621 = 10967929) B10967929
theorem B3609467 : Blo 1068616 3609467 := bstep (se 1 (by rfl) ⟨2707100, by rfl⟩ : syracuseStep 3609467 = 5414201) B5414201
theorem B9770149 : Blo 1068616 9770149 := bstep (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) B1831903
theorem B58595471 : Blo 1068616 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B3709799 : Blo 1068616 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B117087605 : Blo 1068616 117087605 := bstep (se 5 (by rfl) ⟨5488481, by rfl⟩ : syracuseStep 117087605 = 10976963) B10976963
theorem B34709741 : Blo 1068616 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B1713511 : Blo 1068616 1713511 := bstep (se 1 (by rfl) ⟨1285133, by rfl⟩ : syracuseStep 1713511 = 2570267) B2570267
theorem B5778215 : Blo 1068616 5778215 := bstep (se 1 (by rfl) ⟨4333661, by rfl⟩ : syracuseStep 5778215 = 8667323) B8667323
theorem B6859835 : Blo 1068616 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B2405033 : Blo 1068616 2405033 := bstep (se 2 (by rfl) ⟨901887, by rfl⟩ : syracuseStep 2405033 = 1803775) B1803775
theorem B2405735 : Blo 1068616 2405735 := bstep (se 1 (by rfl) ⟨1804301, by rfl⟩ : syracuseStep 2405735 = 3608603) B3608603
theorem B2406995 : Blo 1068616 2406995 := bstep (se 1 (by rfl) ⟨1805246, by rfl⟩ : syracuseStep 2406995 = 3610493) B3610493
theorem B18300815 : Blo 1068616 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B2408723 : Blo 1068616 2408723 := bstep (se 1 (by rfl) ⟨1806542, by rfl⟩ : syracuseStep 2408723 = 3613085) B3613085
theorem B4572233 : Blo 1068616 4572233 := bstep (se 2 (by rfl) ⟨1714587, by rfl⟩ : syracuseStep 4572233 = 3429175) B3429175
theorem B49431799 : Blo 1068616 49431799 := bstep (se 1 (by rfl) ⟨37073849, by rfl⟩ : syracuseStep 49431799 = 74147699) B74147699
theorem B2410235 : Blo 1068616 2410235 := bstep (se 1 (by rfl) ⟨1807676, by rfl⟩ : syracuseStep 2410235 = 3615353) B3615353
theorem B6867625 : Blo 1068616 6867625 := bstep (se 2 (by rfl) ⟨2575359, by rfl⟩ : syracuseStep 6867625 = 5150719) B5150719
theorem B1069895 : Blo 1068616 1069895 := bstep (se 1 (by rfl) ⟨802421, by rfl⟩ : syracuseStep 1069895 = 1604843) B1604843
theorem B3429661 : Blo 1068616 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B1070875 : Blo 1068616 1070875 := bstep (se 1 (by rfl) ⟨803156, by rfl⟩ : syracuseStep 1070875 = 1606313) B1606313
theorem B11589641 : Blo 1068616 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B1071263 : Blo 1068616 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B3857215 : Blo 1068616 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B2710523 : Blo 1068616 2710523 := bstep (se 1 (by rfl) ⟨2032892, by rfl⟩ : syracuseStep 2710523 = 4065785) B4065785
theorem B1072383 : Blo 1068616 1072383 := bstep (se 1 (by rfl) ⟨804287, by rfl⟩ : syracuseStep 1072383 = 1608575) B1608575
theorem B2286235 : Blo 1068616 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B75162443 : Blo 1068616 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B18572399 : Blo 1068616 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B3043439 : Blo 1068616 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B2028883 : Blo 1068616 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B123958907 : Blo 1068616 123958907 := bstep (se 1 (by rfl) ⟨92969180, by rfl⟩ : syracuseStep 123958907 = 185938361) B185938361
theorem B1603337 : Blo 1068616 1603337 := bstep (se 2 (by rfl) ⟨601251, by rfl⟩ : syracuseStep 1603337 = 1202503) B1202503
theorem B2030015 : Blo 1068616 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B1604315 : Blo 1068616 1604315 := bstep (se 1 (by rfl) ⟨1203236, by rfl⟩ : syracuseStep 1604315 = 2406473) B2406473
theorem B1604891 : Blo 1068616 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B7831259 : Blo 1068616 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B1605815 : Blo 1068616 1605815 := bstep (se 1 (by rfl) ⟨1204361, by rfl⟩ : syracuseStep 1605815 = 2408723) B2408723
theorem B3048155 : Blo 1068616 3048155 := bstep (se 1 (by rfl) ⟨2286116, by rfl⟩ : syracuseStep 3048155 = 4572233) B4572233
theorem B1606823 : Blo 1068616 1606823 := bstep (se 1 (by rfl) ⟨1205117, by rfl⟩ : syracuseStep 1606823 = 2410235) B2410235
theorem B4065011 : Blo 1068616 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B12193253 : Blo 1068616 12193253 := bstep (se 4 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 12193253 = 2286235) B2286235
theorem B39063647 : Blo 1068616 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B1807015 : Blo 1068616 1807015 := bstep (se 1 (by rfl) ⟨1355261, by rfl⟩ : syracuseStep 1807015 = 2710523) B2710523
theorem B78058403 : Blo 1068616 78058403 := bstep (se 1 (by rfl) ⟨58543802, by rfl⟩ : syracuseStep 78058403 = 117087605) B117087605
theorem B20583497 : Blo 1068616 20583497 := bstep (se 2 (by rfl) ⟨7718811, by rfl⟩ : syracuseStep 20583497 = 15437623) B15437623
theorem B23139827 : Blo 1068616 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B77994161 : Blo 1068616 77994161 := bstep (se 2 (by rfl) ⟨29247810, by rfl⟩ : syracuseStep 77994161 = 58495621) B58495621
theorem B1353343 : Blo 1068616 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B5220839 : Blo 1068616 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B12200543 : Blo 1068616 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B126856115 : Blo 1068616 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B65909065 : Blo 1068616 65909065 := bstep (se 2 (by rfl) ⟨24715899, by rfl⟩ : syracuseStep 65909065 = 49431799) B49431799
theorem B2405051 : Blo 1068616 2405051 := bstep (se 1 (by rfl) ⟨1803788, by rfl⟩ : syracuseStep 2405051 = 3607577) B3607577
theorem B3257471 : Blo 1068616 3257471 := bstep (se 1 (by rfl) ⟨2443103, by rfl⟩ : syracuseStep 3257471 = 4886207) B4886207
theorem B2405951 : Blo 1068616 2405951 := bstep (se 1 (by rfl) ⟨1804463, by rfl⟩ : syracuseStep 2405951 = 3608927) B3608927
theorem B2406311 : Blo 1068616 2406311 := bstep (se 1 (by rfl) ⟨1804733, by rfl⟩ : syracuseStep 2406311 = 3609467) B3609467
theorem B9156833 : Blo 1068616 9156833 := bstep (se 2 (by rfl) ⟨3433812, by rfl⟩ : syracuseStep 9156833 = 6867625) B6867625
theorem B2473199 : Blo 1068616 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B18531661 : Blo 1068616 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B13026865 : Blo 1068616 13026865 := bstep (se 2 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 13026865 = 9770149) B9770149
theorem B4572881 : Blo 1068616 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B2705177 : Blo 1068616 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B3852143 : Blo 1068616 3852143 := bstep (se 1 (by rfl) ⟨2889107, by rfl⟩ : syracuseStep 3852143 = 5778215) B5778215
theorem B4573223 : Blo 1068616 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B1068891 : Blo 1068616 1068891 := bstep (se 1 (by rfl) ⟨801668, by rfl⟩ : syracuseStep 1068891 = 1603337) B1603337
theorem B1069543 : Blo 1068616 1069543 := bstep (se 1 (by rfl) ⟨802157, by rfl⟩ : syracuseStep 1069543 = 1604315) B1604315
theorem B1069927 : Blo 1068616 1069927 := bstep (se 1 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 1069927 = 1604891) B1604891
theorem B1070751 : Blo 1068616 1070751 := bstep (se 1 (by rfl) ⟨803063, by rfl⟩ : syracuseStep 1070751 = 1606127) B1606127
theorem B1071135 : Blo 1068616 1071135 := bstep (se 1 (by rfl) ⟨803351, by rfl⟩ : syracuseStep 1071135 = 1606703) B1606703
theorem B2284681 : Blo 1068616 2284681 := bstep (se 2 (by rfl) ⟨856755, by rfl⟩ : syracuseStep 2284681 = 1713511) B1713511
theorem B1203439 : Blo 1068616 1203439 := bstep (se 1 (by rfl) ⟨902579, by rfl⟩ : syracuseStep 1203439 = 1805159) B1805159
theorem B7726427 : Blo 1068616 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B12381599 : Blo 1068616 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B2028959 : Blo 1068616 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B1603355 : Blo 1068616 1603355 := bstep (se 1 (by rfl) ⟨1202516, by rfl⟩ : syracuseStep 1603355 = 2405033) B2405033
theorem B801732725 : Blo 1068616 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B1603823 : Blo 1068616 1603823 := bstep (se 1 (by rfl) ⟨1202867, by rfl⟩ : syracuseStep 1603823 = 2405735) B2405735
theorem B82639271 : Blo 1068616 82639271 := bstep (se 1 (by rfl) ⟨61979453, by rfl⟩ : syracuseStep 82639271 = 123958907) B123958907
theorem B5142953 : Blo 1068616 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B1604663 : Blo 1068616 1604663 := bstep (se 1 (by rfl) ⟨1203497, by rfl⟩ : syracuseStep 1604663 = 2406995) B2406995
theorem B2032103 : Blo 1068616 2032103 := bstep (se 1 (by rfl) ⟨1524077, by rfl⟩ : syracuseStep 2032103 = 3048155) B3048155
theorem B3048587 : Blo 1068616 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B1803451 : Blo 1068616 1803451 := bstep (se 1 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 1803451 = 2705177) B2705177
theorem B3048815 : Blo 1068616 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B24708881 : Blo 1068616 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B17369153 : Blo 1068616 17369153 := bstep (se 2 (by rfl) ⟨6513432, by rfl⟩ : syracuseStep 17369153 = 13026865) B13026865
theorem B1804457 : Blo 1068616 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B8128835 : Blo 1068616 8128835 := bstep (se 1 (by rfl) ⟨6096626, by rfl⟩ : syracuseStep 8128835 = 12193253) B12193253
theorem B52038935 : Blo 1068616 52038935 := bstep (se 1 (by rfl) ⟨39029201, by rfl⟩ : syracuseStep 52038935 = 78058403) B78058403
theorem B5150951 : Blo 1068616 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B8133695 : Blo 1068616 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B2171647 : Blo 1068616 2171647 := bstep (se 1 (by rfl) ⟨1628735, by rfl⟩ : syracuseStep 2171647 = 3257471) B3257471
theorem B1352639 : Blo 1068616 1352639 := bstep (se 1 (by rfl) ⟨1014479, by rfl⟩ : syracuseStep 1352639 = 2028959) B2028959
theorem B534488483 : Blo 1068616 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B6104555 : Blo 1068616 6104555 := bstep (se 1 (by rfl) ⟨4578416, by rfl⟩ : syracuseStep 6104555 = 9156833) B9156833
theorem B55092847 : Blo 1068616 55092847 := bstep (se 1 (by rfl) ⟨41319635, by rfl⟩ : syracuseStep 55092847 = 82639271) B82639271
theorem B1648799 : Blo 1068616 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B2568095 : Blo 1068616 2568095 := bstep (se 1 (by rfl) ⟨1926071, by rfl⟩ : syracuseStep 2568095 = 3852143) B3852143
theorem B2409353 : Blo 1068616 2409353 := bstep (se 2 (by rfl) ⟨903507, by rfl⟩ : syracuseStep 2409353 = 1807015) B1807015
theorem B13714541 : Blo 1068616 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B1068903 : Blo 1068616 1068903 := bstep (se 1 (by rfl) ⟨801677, by rfl⟩ : syracuseStep 1068903 = 1603355) B1603355
theorem B1069215 : Blo 1068616 1069215 := bstep (se 1 (by rfl) ⟨801911, by rfl⟩ : syracuseStep 1069215 = 1603823) B1603823
theorem B1069775 : Blo 1068616 1069775 := bstep (se 1 (by rfl) ⟨802331, by rfl⟩ : syracuseStep 1069775 = 1604663) B1604663
theorem B1070543 : Blo 1068616 1070543 := bstep (se 1 (by rfl) ⟨802907, by rfl⟩ : syracuseStep 1070543 = 1605815) B1605815
theorem B1071215 : Blo 1068616 1071215 := bstep (se 1 (by rfl) ⟨803411, by rfl⟩ : syracuseStep 1071215 = 1606823) B1606823
theorem B2710007 : Blo 1068616 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B26042431 : Blo 1068616 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B13722331 : Blo 1068616 13722331 := bstep (se 1 (by rfl) ⟨10291748, by rfl⟩ : syracuseStep 13722331 = 20583497) B20583497
theorem B15426551 : Blo 1068616 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B51996107 : Blo 1068616 51996107 := bstep (se 1 (by rfl) ⟨38997080, by rfl⟩ : syracuseStep 51996107 = 77994161) B77994161
theorem B87878753 : Blo 1068616 87878753 := bstep (se 2 (by rfl) ⟨32954532, by rfl⟩ : syracuseStep 87878753 = 65909065) B65909065
theorem B13922237 : Blo 1068616 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B84570743 : Blo 1068616 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B8254399 : Blo 1068616 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B1603367 : Blo 1068616 1603367 := bstep (se 1 (by rfl) ⟨1202525, by rfl⟩ : syracuseStep 1603367 = 2405051) B2405051
theorem B1603967 : Blo 1068616 1603967 := bstep (se 1 (by rfl) ⟨1202975, by rfl⟩ : syracuseStep 1603967 = 2405951) B2405951
theorem B1604207 : Blo 1068616 1604207 := bstep (se 1 (by rfl) ⟨1203155, by rfl⟩ : syracuseStep 1604207 = 2406311) B2406311
theorem B3046241 : Blo 1068616 3046241 := bstep (se 2 (by rfl) ⟨1142340, by rfl⟩ : syracuseStep 3046241 = 2284681) B2284681
theorem B1604585 : Blo 1068616 1604585 := bstep (se 2 (by rfl) ⟨601719, by rfl⟩ : syracuseStep 1604585 = 1203439) B1203439
theorem B1606235 : Blo 1068616 1606235 := bstep (se 1 (by rfl) ⟨1204676, by rfl⟩ : syracuseStep 1606235 = 2409353) B2409353
theorem B9143027 : Blo 1068616 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B2032391 : Blo 1068616 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B2032543 : Blo 1068616 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B3607037 : Blo 1068616 3607037 := bstep (se 3 (by rfl) ⟨676319, by rfl⟩ : syracuseStep 3607037 = 1352639) B1352639
theorem B1806671 : Blo 1068616 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B356325655 : Blo 1068616 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B4069703 : Blo 1068616 4069703 := bstep (se 1 (by rfl) ⟨3052277, by rfl⟩ : syracuseStep 4069703 = 6104555) B6104555
theorem B1712063 : Blo 1068616 1712063 := bstep (se 1 (by rfl) ⟨1284047, by rfl⟩ : syracuseStep 1712063 = 2568095) B2568095
theorem B1354735 : Blo 1068616 1354735 := bstep (se 1 (by rfl) ⟨1016051, by rfl⟩ : syracuseStep 1354735 = 2032103) B2032103
theorem B18296441 : Blo 1068616 18296441 := bstep (se 2 (by rfl) ⟨6861165, by rfl⟩ : syracuseStep 18296441 = 13722331) B13722331
theorem B2895529 : Blo 1068616 2895529 := bstep (se 2 (by rfl) ⟨1085823, by rfl⟩ : syracuseStep 2895529 = 2171647) B2171647
theorem B11579435 : Blo 1068616 11579435 := bstep (se 1 (by rfl) ⟨8684576, by rfl⟩ : syracuseStep 11579435 = 17369153) B17369153
theorem B5419223 : Blo 1068616 5419223 := bstep (se 1 (by rfl) ⟨4064417, by rfl⟩ : syracuseStep 5419223 = 8128835) B8128835
theorem B2404601 : Blo 1068616 2404601 := bstep (se 2 (by rfl) ⟨901725, by rfl⟩ : syracuseStep 2404601 = 1803451) B1803451
theorem B41137469 : Blo 1068616 41137469 := bstep (se 3 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 41137469 = 15426551) B15426551
theorem B5422463 : Blo 1068616 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B1099199 : Blo 1068616 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B56380495 : Blo 1068616 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B1068911 : Blo 1068616 1068911 := bstep (se 1 (by rfl) ⟨801683, by rfl⟩ : syracuseStep 1068911 = 1603367) B1603367
theorem B1069311 : Blo 1068616 1069311 := bstep (se 1 (by rfl) ⟨801983, by rfl⟩ : syracuseStep 1069311 = 1603967) B1603967
theorem B1069471 : Blo 1068616 1069471 := bstep (se 1 (by rfl) ⟨802103, by rfl⟩ : syracuseStep 1069471 = 1604207) B1604207
theorem B1069723 : Blo 1068616 1069723 := bstep (se 1 (by rfl) ⟨802292, by rfl⟩ : syracuseStep 1069723 = 1604585) B1604585
theorem B34723241 : Blo 1068616 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B16472587 : Blo 1068616 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B1202971 : Blo 1068616 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B73457129 : Blo 1068616 73457129 := bstep (se 2 (by rfl) ⟨27546423, by rfl⟩ : syracuseStep 73457129 = 55092847) B55092847
theorem B34692623 : Blo 1068616 34692623 := bstep (se 1 (by rfl) ⟨26019467, by rfl⟩ : syracuseStep 34692623 = 52038935) B52038935
theorem B3433967 : Blo 1068616 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B34664071 : Blo 1068616 34664071 := bstep (se 1 (by rfl) ⟨25998053, by rfl⟩ : syracuseStep 34664071 = 51996107) B51996107
theorem B11005865 : Blo 1068616 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B58585835 : Blo 1068616 58585835 := bstep (se 1 (by rfl) ⟨43939376, by rfl⟩ : syracuseStep 58585835 = 87878753) B87878753
theorem B2030827 : Blo 1068616 2030827 := bstep (se 1 (by rfl) ⟨1523120, by rfl⟩ : syracuseStep 2030827 = 3046241) B3046241
theorem B37125965 : Blo 1068616 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B6095351 : Blo 1068616 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B1806313 : Blo 1068616 1806313 := bstep (se 2 (by rfl) ⟨677367, by rfl⟩ : syracuseStep 1806313 = 1354735) B1354735
theorem B75173993 : Blo 1068616 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B12197627 : Blo 1068616 12197627 := bstep (se 1 (by rfl) ⟨9148220, by rfl⟩ : syracuseStep 12197627 = 18296441) B18296441
theorem B3612815 : Blo 1068616 3612815 := bstep (se 1 (by rfl) ⟨2709611, by rfl⟩ : syracuseStep 3612815 = 5419223) B5419223
theorem B21963449 : Blo 1068616 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B3134170837 : Blo 1068616 3134170837 := bstep (se 7 (by rfl) ⟨36728564, by rfl⟩ : syracuseStep 3134170837 = 73457129) B73457129
theorem B99002573 : Blo 1068616 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B3614975 : Blo 1068616 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B2404691 : Blo 1068616 2404691 := bstep (se 1 (by rfl) ⟨1803518, by rfl⟩ : syracuseStep 2404691 = 3607037) B3607037
theorem B5419709 : Blo 1068616 5419709 := bstep (se 3 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 5419709 = 2032391) B2032391
theorem B23148827 : Blo 1068616 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B2931197 : Blo 1068616 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B46218761 : Blo 1068616 46218761 := bstep (se 2 (by rfl) ⟨17332035, by rfl⟩ : syracuseStep 46218761 = 34664071) B34664071
theorem B7719623 : Blo 1068616 7719623 := bstep (se 1 (by rfl) ⟨5789717, by rfl⟩ : syracuseStep 7719623 = 11579435) B11579435
theorem B2707769 : Blo 1068616 2707769 := bstep (se 2 (by rfl) ⟨1015413, by rfl⟩ : syracuseStep 2707769 = 2030827) B2030827
theorem B1070823 : Blo 1068616 1070823 := bstep (se 1 (by rfl) ⟨803117, by rfl⟩ : syracuseStep 1070823 = 1606235) B1606235
theorem B2710057 : Blo 1068616 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B1204447 : Blo 1068616 1204447 := bstep (se 1 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 1204447 = 1806671) B1806671
theorem B2713135 : Blo 1068616 2713135 := bstep (se 1 (by rfl) ⟨2034851, by rfl⟩ : syracuseStep 2713135 = 4069703) B4069703
theorem B3860705 : Blo 1068616 3860705 := bstep (se 2 (by rfl) ⟨1447764, by rfl⟩ : syracuseStep 3860705 = 2895529) B2895529
theorem B23128415 : Blo 1068616 23128415 := bstep (se 1 (by rfl) ⟨17346311, by rfl⟩ : syracuseStep 23128415 = 34692623) B34692623
theorem B1141375 : Blo 1068616 1141375 := bstep (se 1 (by rfl) ⟨856031, by rfl⟩ : syracuseStep 1141375 = 1712063) B1712063
theorem B2289311 : Blo 1068616 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B7337243 : Blo 1068616 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B1603067 : Blo 1068616 1603067 := bstep (se 1 (by rfl) ⟨1202300, by rfl⟩ : syracuseStep 1603067 = 2404601) B2404601
theorem B475100873 : Blo 1068616 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B39057223 : Blo 1068616 39057223 := bstep (se 1 (by rfl) ⟨29292917, by rfl⟩ : syracuseStep 39057223 = 58585835) B58585835
theorem B27424979 : Blo 1068616 27424979 := bstep (se 1 (by rfl) ⟨20568734, by rfl⟩ : syracuseStep 27424979 = 41137469) B41137469
theorem B1603961 : Blo 1068616 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B1605929 : Blo 1068616 1605929 := bstep (se 2 (by rfl) ⟨602223, by rfl⟩ : syracuseStep 1605929 = 1204447) B1204447
theorem B4063567 : Blo 1068616 4063567 := bstep (se 1 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 4063567 = 6095351) B6095351
theorem B5146415 : Blo 1068616 5146415 := bstep (se 1 (by rfl) ⟨3859811, by rfl⟩ : syracuseStep 5146415 = 7719623) B7719623
theorem B1805179 : Blo 1068616 1805179 := bstep (se 1 (by rfl) ⟨1353884, by rfl⟩ : syracuseStep 1805179 = 2707769) B2707769
theorem B19565981 : Blo 1068616 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B8131751 : Blo 1068616 8131751 := bstep (se 1 (by rfl) ⟨6098813, by rfl⟩ : syracuseStep 8131751 = 12197627) B12197627
theorem B31266101 : Blo 1068616 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B66001715 : Blo 1068616 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B52076297 : Blo 1068616 52076297 := bstep (se 2 (by rfl) ⟨19528611, by rfl⟩ : syracuseStep 52076297 = 39057223) B39057223
theorem B3613139 : Blo 1068616 3613139 := bstep (se 1 (by rfl) ⟨2709854, by rfl⟩ : syracuseStep 3613139 = 5419709) B5419709
theorem B3613409 : Blo 1068616 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B30812507 : Blo 1068616 30812507 := bstep (se 1 (by rfl) ⟨23109380, by rfl⟩ : syracuseStep 30812507 = 46218761) B46218761
theorem B3617513 : Blo 1068616 3617513 := bstep (se 2 (by rfl) ⟨1356567, by rfl⟩ : syracuseStep 3617513 = 2713135) B2713135
theorem B50115995 : Blo 1068616 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B1521833 : Blo 1068616 1521833 := bstep (se 2 (by rfl) ⟨570687, by rfl⟩ : syracuseStep 1521833 = 1141375) B1141375
theorem B2408417 : Blo 1068616 2408417 := bstep (se 2 (by rfl) ⟨903156, by rfl⟩ : syracuseStep 2408417 = 1806313) B1806313
theorem B2408543 : Blo 1068616 2408543 := bstep (se 1 (by rfl) ⟨1806407, by rfl⟩ : syracuseStep 2408543 = 3612815) B3612815
theorem B2573803 : Blo 1068616 2573803 := bstep (se 1 (by rfl) ⟨1930352, by rfl⟩ : syracuseStep 2573803 = 3860705) B3860705
theorem B2409983 : Blo 1068616 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B15418943 : Blo 1068616 15418943 := bstep (se 1 (by rfl) ⟨11564207, by rfl⟩ : syracuseStep 15418943 = 23128415) B23128415
theorem B1526207 : Blo 1068616 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B1068711 : Blo 1068616 1068711 := bstep (se 1 (by rfl) ⟨801533, by rfl⟩ : syracuseStep 1068711 = 1603067) B1603067
theorem B1069307 : Blo 1068616 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B4178894449 : Blo 1068616 4178894449 := bstep (se 2 (by rfl) ⟨1567085418, by rfl⟩ : syracuseStep 4178894449 = 3134170837) B3134170837
theorem B14642299 : Blo 1068616 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B1603127 : Blo 1068616 1603127 := bstep (se 1 (by rfl) ⟨1202345, by rfl⟩ : syracuseStep 1603127 = 2404691) B2404691
theorem B316733915 : Blo 1068616 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B18283319 : Blo 1068616 18283319 := bstep (se 1 (by rfl) ⟨13712489, by rfl⟩ : syracuseStep 18283319 = 27424979) B27424979
theorem B15432551 : Blo 1068616 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B1605695 : Blo 1068616 1605695 := bstep (se 1 (by rfl) ⟨1204271, by rfl⟩ : syracuseStep 1605695 = 2408543) B2408543
theorem B1606655 : Blo 1068616 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B13043987 : Blo 1068616 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B20844067 : Blo 1068616 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B4069885 : Blo 1068616 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B5418089 : Blo 1068616 5418089 := bstep (se 2 (by rfl) ⟨2031783, by rfl⟩ : syracuseStep 5418089 = 4063567) B4063567
theorem B5421167 : Blo 1068616 5421167 := bstep (se 1 (by rfl) ⟨4065875, by rfl⟩ : syracuseStep 5421167 = 8131751) B8131751
theorem B2406905 : Blo 1068616 2406905 := bstep (se 2 (by rfl) ⟨902589, by rfl⟩ : syracuseStep 2406905 = 1805179) B1805179
theorem B34717531 : Blo 1068616 34717531 := bstep (se 1 (by rfl) ⟨26038148, by rfl⟩ : syracuseStep 34717531 = 52076297) B52076297
theorem B2408759 : Blo 1068616 2408759 := bstep (se 1 (by rfl) ⟨1806569, by rfl⟩ : syracuseStep 2408759 = 3613139) B3613139
theorem B2408939 : Blo 1068616 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B2411675 : Blo 1068616 2411675 := bstep (se 1 (by rfl) ⟨1808756, by rfl⟩ : syracuseStep 2411675 = 3617513) B3617513
theorem B33410663 : Blo 1068616 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B1068751 : Blo 1068616 1068751 := bstep (se 1 (by rfl) ⟨801563, by rfl⟩ : syracuseStep 1068751 = 1603127) B1603127
theorem B5571859265 : Blo 1068616 5571859265 := bstep (se 2 (by rfl) ⟨2089447224, by rfl⟩ : syracuseStep 5571859265 = 4178894449) B4178894449
theorem B1070619 : Blo 1068616 1070619 := bstep (se 1 (by rfl) ⟨802964, by rfl⟩ : syracuseStep 1070619 = 1605929) B1605929
theorem B10279295 : Blo 1068616 10279295 := bstep (se 1 (by rfl) ⟨7709471, by rfl⟩ : syracuseStep 10279295 = 15418943) B15418943
theorem B3430943 : Blo 1068616 3430943 := bstep (se 1 (by rfl) ⟨2573207, by rfl⟩ : syracuseStep 3430943 = 5146415) B5146415
theorem B3431737 : Blo 1068616 3431737 := bstep (se 2 (by rfl) ⟨1286901, by rfl⟩ : syracuseStep 3431737 = 2573803) B2573803
theorem B19523065 : Blo 1068616 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B44001143 : Blo 1068616 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B4058221 : Blo 1068616 4058221 := bstep (se 3 (by rfl) ⟨760916, by rfl⟩ : syracuseStep 4058221 = 1521833) B1521833
theorem B20541671 : Blo 1068616 20541671 := bstep (se 1 (by rfl) ⟨15406253, by rfl⟩ : syracuseStep 20541671 = 30812507) B30812507
theorem B211155943 : Blo 1068616 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B12188879 : Blo 1068616 12188879 := bstep (se 1 (by rfl) ⟨9141659, by rfl⟩ : syracuseStep 12188879 = 18283319) B18283319
theorem B10288367 : Blo 1068616 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B1605611 : Blo 1068616 1605611 := bstep (se 1 (by rfl) ⟨1204208, by rfl⟩ : syracuseStep 1605611 = 2408417) B2408417
theorem B1605839 : Blo 1068616 1605839 := bstep (se 1 (by rfl) ⟨1204379, by rfl⟩ : syracuseStep 1605839 = 2408759) B2408759
theorem B1605959 : Blo 1068616 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B1607783 : Blo 1068616 1607783 := bstep (se 1 (by rfl) ⟨1205837, by rfl⟩ : syracuseStep 1607783 = 2411675) B2411675
theorem B5410961 : Blo 1068616 5410961 := bstep (se 2 (by rfl) ⟨2029110, by rfl⟩ : syracuseStep 5410961 = 4058221) B4058221
theorem B6852863 : Blo 1068616 6852863 := bstep (se 1 (by rfl) ⟨5139647, by rfl⟩ : syracuseStep 6852863 = 10279295) B10279295
theorem B27792089 : Blo 1068616 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B29334095 : Blo 1068616 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B3612059 : Blo 1068616 3612059 := bstep (se 1 (by rfl) ⟨2709044, by rfl⟩ : syracuseStep 3612059 = 5418089) B5418089
theorem B3614111 : Blo 1068616 3614111 := bstep (se 1 (by rfl) ⟨2710583, by rfl⟩ : syracuseStep 3614111 = 5421167) B5421167
theorem B6858911 : Blo 1068616 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B8695991 : Blo 1068616 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B26030753 : Blo 1068616 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B5426513 : Blo 1068616 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B4575649 : Blo 1068616 4575649 := bstep (se 2 (by rfl) ⟨1715868, by rfl⟩ : syracuseStep 4575649 = 3431737) B3431737
theorem B46290041 : Blo 1068616 46290041 := bstep (se 2 (by rfl) ⟨17358765, by rfl⟩ : syracuseStep 46290041 = 34717531) B34717531
theorem B1070407 : Blo 1068616 1070407 := bstep (se 1 (by rfl) ⟨802805, by rfl⟩ : syracuseStep 1070407 = 1605611) B1605611
theorem B1070463 : Blo 1068616 1070463 := bstep (se 1 (by rfl) ⟨802847, by rfl⟩ : syracuseStep 1070463 = 1605695) B1605695
theorem B1071103 : Blo 1068616 1071103 := bstep (se 1 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 1071103 = 1606655) B1606655
theorem B22273775 : Blo 1068616 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B3714572843 : Blo 1068616 3714572843 := bstep (se 1 (by rfl) ⟨2785929632, by rfl⟩ : syracuseStep 3714572843 = 5571859265) B5571859265
theorem B2287295 : Blo 1068616 2287295 := bstep (se 1 (by rfl) ⟨1715471, by rfl⟩ : syracuseStep 2287295 = 3430943) B3430943
theorem B13694447 : Blo 1068616 13694447 := bstep (se 1 (by rfl) ⟨10270835, by rfl⟩ : syracuseStep 13694447 = 20541671) B20541671
theorem B281541257 : Blo 1068616 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B1604603 : Blo 1068616 1604603 := bstep (se 1 (by rfl) ⟨1203452, by rfl⟩ : syracuseStep 1604603 = 2406905) B2406905
theorem B8125919 : Blo 1068616 8125919 := bstep (se 1 (by rfl) ⟨6094439, by rfl⟩ : syracuseStep 8125919 = 12188879) B12188879
theorem B3607307 : Blo 1068616 3607307 := bstep (se 1 (by rfl) ⟨2705480, by rfl⟩ : syracuseStep 3607307 = 5410961) B5410961
theorem B14849183 : Blo 1068616 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B2476381895 : Blo 1068616 2476381895 := bstep (se 1 (by rfl) ⟨1857286421, by rfl⟩ : syracuseStep 2476381895 = 3714572843) B3714572843
theorem B6100865 : Blo 1068616 6100865 := bstep (se 2 (by rfl) ⟨2287824, by rfl⟩ : syracuseStep 6100865 = 4575649) B4575649
theorem B5417279 : Blo 1068616 5417279 := bstep (se 1 (by rfl) ⟨4062959, by rfl⟩ : syracuseStep 5417279 = 8125919) B8125919
theorem B3617675 : Blo 1068616 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B4568575 : Blo 1068616 4568575 := bstep (se 1 (by rfl) ⟨3426431, by rfl⟩ : syracuseStep 4568575 = 6852863) B6852863
theorem B18528059 : Blo 1068616 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B2408039 : Blo 1068616 2408039 := bstep (se 1 (by rfl) ⟨1806029, by rfl⟩ : syracuseStep 2408039 = 3612059) B3612059
theorem B2409407 : Blo 1068616 2409407 := bstep (se 1 (by rfl) ⟨1807055, by rfl⟩ : syracuseStep 2409407 = 3614111) B3614111
theorem B1524863 : Blo 1068616 1524863 := bstep (se 1 (by rfl) ⟨1143647, by rfl⟩ : syracuseStep 1524863 = 2287295) B2287295
theorem B4572607 : Blo 1068616 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B17353835 : Blo 1068616 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B9129631 : Blo 1068616 9129631 := bstep (se 1 (by rfl) ⟨6847223, by rfl⟩ : syracuseStep 9129631 = 13694447) B13694447
theorem B1069735 : Blo 1068616 1069735 := bstep (se 1 (by rfl) ⟨802301, by rfl⟩ : syracuseStep 1069735 = 1604603) B1604603
theorem B1070559 : Blo 1068616 1070559 := bstep (se 1 (by rfl) ⟨802919, by rfl⟩ : syracuseStep 1070559 = 1605839) B1605839
theorem B1070639 : Blo 1068616 1070639 := bstep (se 1 (by rfl) ⟨802979, by rfl⟩ : syracuseStep 1070639 = 1605959) B1605959
theorem B1071855 : Blo 1068616 1071855 := bstep (se 1 (by rfl) ⟨803891, by rfl⟩ : syracuseStep 1071855 = 1607783) B1607783
theorem B30860027 : Blo 1068616 30860027 := bstep (se 1 (by rfl) ⟨23145020, by rfl⟩ : syracuseStep 30860027 = 46290041) B46290041
theorem B19556063 : Blo 1068616 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B5797327 : Blo 1068616 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B187694171 : Blo 1068616 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B1606271 : Blo 1068616 1606271 := bstep (se 1 (by rfl) ⟨1204703, by rfl⟩ : syracuseStep 1606271 = 2409407) B2409407
theorem B6096809 : Blo 1068616 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B11569223 : Blo 1068616 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B4066301 : Blo 1068616 4066301 := bstep (se 3 (by rfl) ⟨762431, by rfl⟩ : syracuseStep 4066301 = 1524863) B1524863
theorem B1650921263 : Blo 1068616 1650921263 := bstep (se 1 (by rfl) ⟨1238190947, by rfl⟩ : syracuseStep 1650921263 = 2476381895) B2476381895
theorem B4067243 : Blo 1068616 4067243 := bstep (se 1 (by rfl) ⟨3050432, by rfl⟩ : syracuseStep 4067243 = 6100865) B6100865
theorem B3611519 : Blo 1068616 3611519 := bstep (se 1 (by rfl) ⟨2708639, by rfl⟩ : syracuseStep 3611519 = 5417279) B5417279
theorem B2404871 : Blo 1068616 2404871 := bstep (se 1 (by rfl) ⟨1803653, by rfl⟩ : syracuseStep 2404871 = 3607307) B3607307
theorem B39597821 : Blo 1068616 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B12172841 : Blo 1068616 12172841 := bstep (se 2 (by rfl) ⟨4564815, by rfl⟩ : syracuseStep 12172841 = 9129631) B9129631
theorem B2411783 : Blo 1068616 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B125129447 : Blo 1068616 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B49408157 : Blo 1068616 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B20573351 : Blo 1068616 20573351 := bstep (se 1 (by rfl) ⟨15430013, by rfl⟩ : syracuseStep 20573351 = 30860027) B30860027
theorem B13037375 : Blo 1068616 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B7729769 : Blo 1068616 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B6091433 : Blo 1068616 6091433 := bstep (se 2 (by rfl) ⟨2284287, by rfl⟩ : syracuseStep 6091433 = 4568575) B4568575
theorem B1605359 : Blo 1068616 1605359 := bstep (se 1 (by rfl) ⟨1204019, by rfl⟩ : syracuseStep 1605359 = 2408039) B2408039
theorem B4064539 : Blo 1068616 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B20612717 : Blo 1068616 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B1607855 : Blo 1068616 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B1100614175 : Blo 1068616 1100614175 := bstep (se 1 (by rfl) ⟨825460631, by rfl⟩ : syracuseStep 1100614175 = 1650921263) B1650921263
theorem B8691583 : Blo 1068616 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B7712815 : Blo 1068616 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B2407679 : Blo 1068616 2407679 := bstep (se 1 (by rfl) ⟨1805759, by rfl⟩ : syracuseStep 2407679 = 3611519) B3611519
theorem B13715567 : Blo 1068616 13715567 := bstep (se 1 (by rfl) ⟨10286675, by rfl⟩ : syracuseStep 13715567 = 20573351) B20573351
theorem B26398547 : Blo 1068616 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B8115227 : Blo 1068616 8115227 := bstep (se 1 (by rfl) ⟨6086420, by rfl⟩ : syracuseStep 8115227 = 12172841) B12172841
theorem B1070239 : Blo 1068616 1070239 := bstep (se 1 (by rfl) ⟨802679, by rfl⟩ : syracuseStep 1070239 = 1605359) B1605359
theorem B1070847 : Blo 1068616 1070847 := bstep (se 1 (by rfl) ⟨803135, by rfl⟩ : syracuseStep 1070847 = 1606271) B1606271
theorem B2710867 : Blo 1068616 2710867 := bstep (se 1 (by rfl) ⟨2033150, by rfl⟩ : syracuseStep 2710867 = 4066301) B4066301
theorem B2711495 : Blo 1068616 2711495 := bstep (se 1 (by rfl) ⟨2033621, by rfl⟩ : syracuseStep 2711495 = 4067243) B4067243
theorem B83419631 : Blo 1068616 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B131755085 : Blo 1068616 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B1603247 : Blo 1068616 1603247 := bstep (se 1 (by rfl) ⟨1202435, by rfl⟩ : syracuseStep 1603247 = 2404871) B2404871
theorem B4060955 : Blo 1068616 4060955 := bstep (se 1 (by rfl) ⟨3045716, by rfl⟩ : syracuseStep 4060955 = 6091433) B6091433
theorem B9143711 : Blo 1068616 9143711 := bstep (se 1 (by rfl) ⟨6857783, by rfl⟩ : syracuseStep 9143711 = 13715567) B13715567
theorem B733742783 : Blo 1068616 733742783 := bstep (se 1 (by rfl) ⟨550307087, by rfl⟩ : syracuseStep 733742783 = 1100614175) B1100614175
theorem B17599031 : Blo 1068616 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B5410151 : Blo 1068616 5410151 := bstep (se 1 (by rfl) ⟨4057613, by rfl⟩ : syracuseStep 5410151 = 8115227) B8115227
theorem B1807663 : Blo 1068616 1807663 := bstep (se 1 (by rfl) ⟨1355747, by rfl⟩ : syracuseStep 1807663 = 2711495) B2711495
theorem B55613087 : Blo 1068616 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B3614489 : Blo 1068616 3614489 := bstep (se 2 (by rfl) ⟨1355433, by rfl⟩ : syracuseStep 3614489 = 2710867) B2710867
theorem B13741811 : Blo 1068616 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B5419385 : Blo 1068616 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B87836723 : Blo 1068616 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B1068831 : Blo 1068616 1068831 := bstep (se 1 (by rfl) ⟨801623, by rfl⟩ : syracuseStep 1068831 = 1603247) B1603247
theorem B2707303 : Blo 1068616 2707303 := bstep (se 1 (by rfl) ⟨2030477, by rfl⟩ : syracuseStep 2707303 = 4060955) B4060955
theorem B11588777 : Blo 1068616 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B1071903 : Blo 1068616 1071903 := bstep (se 1 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 1071903 = 1607855) B1607855
theorem B10283753 : Blo 1068616 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B1605119 : Blo 1068616 1605119 := bstep (se 1 (by rfl) ⟨1203839, by rfl⟩ : syracuseStep 1605119 = 2407679) B2407679
theorem B6095807 : Blo 1068616 6095807 := bstep (se 1 (by rfl) ⟨4571855, by rfl⟩ : syracuseStep 6095807 = 9143711) B9143711
theorem B489161855 : Blo 1068616 489161855 := bstep (se 1 (by rfl) ⟨366871391, by rfl⟩ : syracuseStep 489161855 = 733742783) B733742783
theorem B58557815 : Blo 1068616 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B11732687 : Blo 1068616 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B3606767 : Blo 1068616 3606767 := bstep (se 1 (by rfl) ⟨2705075, by rfl⟩ : syracuseStep 3606767 = 5410151) B5410151
theorem B3609737 : Blo 1068616 3609737 := bstep (se 2 (by rfl) ⟨1353651, by rfl⟩ : syracuseStep 3609737 = 2707303) B2707303
theorem B6855835 : Blo 1068616 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B3612923 : Blo 1068616 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B37075391 : Blo 1068616 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B2409659 : Blo 1068616 2409659 := bstep (se 1 (by rfl) ⟨1807244, by rfl⟩ : syracuseStep 2409659 = 3614489) B3614489
theorem B2410217 : Blo 1068616 2410217 := bstep (se 2 (by rfl) ⟨903831, by rfl⟩ : syracuseStep 2410217 = 1807663) B1807663
theorem B9161207 : Blo 1068616 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B1070079 : Blo 1068616 1070079 := bstep (se 1 (by rfl) ⟨802559, by rfl⟩ : syracuseStep 1070079 = 1605119) B1605119
theorem B7725851 : Blo 1068616 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B4063871 : Blo 1068616 4063871 := bstep (se 1 (by rfl) ⟨3047903, by rfl⟩ : syracuseStep 4063871 = 6095807) B6095807
theorem B326107903 : Blo 1068616 326107903 := bstep (se 1 (by rfl) ⟨244580927, by rfl⟩ : syracuseStep 326107903 = 489161855) B489161855
theorem B1606439 : Blo 1068616 1606439 := bstep (se 1 (by rfl) ⟨1204829, by rfl⟩ : syracuseStep 1606439 = 2409659) B2409659
theorem B1606811 : Blo 1068616 1606811 := bstep (se 1 (by rfl) ⟨1205108, by rfl⟩ : syracuseStep 1606811 = 2410217) B2410217
theorem B5150567 : Blo 1068616 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B24716927 : Blo 1068616 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B39038543 : Blo 1068616 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B2404511 : Blo 1068616 2404511 := bstep (se 1 (by rfl) ⟨1803383, by rfl⟩ : syracuseStep 2404511 = 3606767) B3606767
theorem B6107471 : Blo 1068616 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B2406491 : Blo 1068616 2406491 := bstep (se 1 (by rfl) ⟨1804868, by rfl⟩ : syracuseStep 2406491 = 3609737) B3609737
theorem B2408615 : Blo 1068616 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B7821791 : Blo 1068616 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B9141113 : Blo 1068616 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B1605743 : Blo 1068616 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B5214527 : Blo 1068616 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B26025695 : Blo 1068616 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B4071647 : Blo 1068616 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B434810537 : Blo 1068616 434810537 := bstep (se 2 (by rfl) ⟨163053951, by rfl⟩ : syracuseStep 434810537 = 326107903) B326107903
theorem B65911805 : Blo 1068616 65911805 := bstep (se 3 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 65911805 = 24716927) B24716927
theorem B2709247 : Blo 1068616 2709247 := bstep (se 1 (by rfl) ⟨2031935, by rfl⟩ : syracuseStep 2709247 = 4063871) B4063871
theorem B1070959 : Blo 1068616 1070959 := bstep (se 1 (by rfl) ⟨803219, by rfl⟩ : syracuseStep 1070959 = 1606439) B1606439
theorem B1071207 : Blo 1068616 1071207 := bstep (se 1 (by rfl) ⟨803405, by rfl⟩ : syracuseStep 1071207 = 1606811) B1606811
theorem B3433711 : Blo 1068616 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B1603007 : Blo 1068616 1603007 := bstep (se 1 (by rfl) ⟨1202255, by rfl⟩ : syracuseStep 1603007 = 2404511) B2404511
theorem B1604327 : Blo 1068616 1604327 := bstep (se 1 (by rfl) ⟨1203245, by rfl⟩ : syracuseStep 1604327 = 2406491) B2406491
theorem B6094075 : Blo 1068616 6094075 := bstep (se 1 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 6094075 = 9141113) B9141113
theorem B3476351 : Blo 1068616 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B3612329 : Blo 1068616 3612329 := bstep (se 2 (by rfl) ⟨1354623, by rfl⟩ : syracuseStep 3612329 = 2709247) B2709247
theorem B289873691 : Blo 1068616 289873691 := bstep (se 1 (by rfl) ⟨217405268, by rfl⟩ : syracuseStep 289873691 = 434810537) B434810537
theorem B17350463 : Blo 1068616 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B1068671 : Blo 1068616 1068671 := bstep (se 1 (by rfl) ⟨801503, by rfl⟩ : syracuseStep 1068671 = 1603007) B1603007
theorem B1069551 : Blo 1068616 1069551 := bstep (se 1 (by rfl) ⟨802163, by rfl⟩ : syracuseStep 1069551 = 1604327) B1604327
theorem B1070495 : Blo 1068616 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B4578281 : Blo 1068616 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B2714431 : Blo 1068616 2714431 := bstep (se 1 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 2714431 = 4071647) B4071647
theorem B8125433 : Blo 1068616 8125433 := bstep (se 2 (by rfl) ⟨3047037, by rfl⟩ : syracuseStep 8125433 = 6094075) B6094075
theorem B43941203 : Blo 1068616 43941203 := bstep (se 1 (by rfl) ⟨32955902, by rfl⟩ : syracuseStep 43941203 = 65911805) B65911805
theorem B3052187 : Blo 1068616 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B5416955 : Blo 1068616 5416955 := bstep (se 1 (by rfl) ⟨4062716, by rfl⟩ : syracuseStep 5416955 = 8125433) B8125433
theorem B3619241 : Blo 1068616 3619241 := bstep (se 2 (by rfl) ⟨1357215, by rfl⟩ : syracuseStep 3619241 = 2714431) B2714431
theorem B2408219 : Blo 1068616 2408219 := bstep (se 1 (by rfl) ⟨1806164, by rfl⟩ : syracuseStep 2408219 = 3612329) B3612329
theorem B193249127 : Blo 1068616 193249127 := bstep (se 1 (by rfl) ⟨144936845, by rfl⟩ : syracuseStep 193249127 = 289873691) B289873691
theorem B2317567 : Blo 1068616 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B29294135 : Blo 1068616 29294135 := bstep (se 1 (by rfl) ⟨21970601, by rfl⟩ : syracuseStep 29294135 = 43941203) B43941203
theorem B11566975 : Blo 1068616 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B2034791 : Blo 1068616 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B3611303 : Blo 1068616 3611303 := bstep (se 1 (by rfl) ⟨2708477, by rfl⟩ : syracuseStep 3611303 = 5416955) B5416955
theorem B3090089 : Blo 1068616 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B2412827 : Blo 1068616 2412827 := bstep (se 1 (by rfl) ⟨1809620, by rfl⟩ : syracuseStep 2412827 = 3619241) B3619241
theorem B15422633 : Blo 1068616 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B128832751 : Blo 1068616 128832751 := bstep (se 1 (by rfl) ⟨96624563, by rfl⟩ : syracuseStep 128832751 = 193249127) B193249127
theorem B19529423 : Blo 1068616 19529423 := bstep (se 1 (by rfl) ⟨14647067, by rfl⟩ : syracuseStep 19529423 = 29294135) B29294135
theorem B1605479 : Blo 1068616 1605479 := bstep (se 1 (by rfl) ⟨1204109, by rfl⟩ : syracuseStep 1605479 = 2408219) B2408219
theorem B1608551 : Blo 1068616 1608551 := bstep (se 1 (by rfl) ⟨1206413, by rfl⟩ : syracuseStep 1608551 = 2412827) B2412827
theorem B13019615 : Blo 1068616 13019615 := bstep (se 1 (by rfl) ⟨9764711, by rfl⟩ : syracuseStep 13019615 = 19529423) B19529423
theorem B1356527 : Blo 1068616 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B8240237 : Blo 1068616 8240237 := bstep (se 3 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 8240237 = 3090089) B3090089
theorem B2407535 : Blo 1068616 2407535 := bstep (se 1 (by rfl) ⟨1805651, by rfl⟩ : syracuseStep 2407535 = 3611303) B3611303
theorem B1070319 : Blo 1068616 1070319 := bstep (se 1 (by rfl) ⟨802739, by rfl⟩ : syracuseStep 1070319 = 1605479) B1605479
theorem B10281755 : Blo 1068616 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B687108005 : Blo 1068616 687108005 := bstep (se 4 (by rfl) ⟨64416375, by rfl⟩ : syracuseStep 687108005 = 128832751) B128832751
theorem B6854503 : Blo 1068616 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B458072003 : Blo 1068616 458072003 := bstep (se 1 (by rfl) ⟨343554002, by rfl⟩ : syracuseStep 458072003 = 687108005) B687108005
theorem B3617405 : Blo 1068616 3617405 := bstep (se 3 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 3617405 = 1356527) B1356527
theorem B5493491 : Blo 1068616 5493491 := bstep (se 1 (by rfl) ⟨4120118, by rfl⟩ : syracuseStep 5493491 = 8240237) B8240237
theorem B1072367 : Blo 1068616 1072367 := bstep (se 1 (by rfl) ⟨804275, by rfl⟩ : syracuseStep 1072367 = 1608551) B1608551
theorem B8679743 : Blo 1068616 8679743 := bstep (se 1 (by rfl) ⟨6509807, by rfl⟩ : syracuseStep 8679743 = 13019615) B13019615
theorem B1605023 : Blo 1068616 1605023 := bstep (se 1 (by rfl) ⟨1203767, by rfl⟩ : syracuseStep 1605023 = 2407535) B2407535
theorem B305381335 : Blo 1068616 305381335 := bstep (se 1 (by rfl) ⟨229036001, by rfl⟩ : syracuseStep 305381335 = 458072003) B458072003
theorem B5786495 : Blo 1068616 5786495 := bstep (se 1 (by rfl) ⟨4339871, by rfl⟩ : syracuseStep 5786495 = 8679743) B8679743
theorem B2411603 : Blo 1068616 2411603 := bstep (se 1 (by rfl) ⟨1808702, by rfl⟩ : syracuseStep 2411603 = 3617405) B3617405
theorem B1070015 : Blo 1068616 1070015 := bstep (se 1 (by rfl) ⟨802511, by rfl⟩ : syracuseStep 1070015 = 1605023) B1605023
theorem B3662327 : Blo 1068616 3662327 := bstep (se 1 (by rfl) ⟨2746745, by rfl⟩ : syracuseStep 3662327 = 5493491) B5493491
theorem B9139337 : Blo 1068616 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B1607735 : Blo 1068616 1607735 := bstep (se 1 (by rfl) ⟨1205801, by rfl⟩ : syracuseStep 1607735 = 2411603) B2411603
theorem B2441551 : Blo 1068616 2441551 := bstep (se 1 (by rfl) ⟨1831163, by rfl⟩ : syracuseStep 2441551 = 3662327) B3662327
theorem B3857663 : Blo 1068616 3857663 := bstep (se 1 (by rfl) ⟨2893247, by rfl⟩ : syracuseStep 3857663 = 5786495) B5786495
theorem B6092891 : Blo 1068616 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B407175113 : Blo 1068616 407175113 := bstep (se 2 (by rfl) ⟨152690667, by rfl⟩ : syracuseStep 407175113 = 305381335) B305381335
theorem B3255401 : Blo 1068616 3255401 := bstep (se 2 (by rfl) ⟨1220775, by rfl⟩ : syracuseStep 3255401 = 2441551) B2441551
theorem B1071823 : Blo 1068616 1071823 := bstep (se 1 (by rfl) ⟨803867, by rfl⟩ : syracuseStep 1071823 = 1607735) B1607735
theorem B10287101 : Blo 1068616 10287101 := bstep (se 3 (by rfl) ⟨1928831, by rfl⟩ : syracuseStep 10287101 = 3857663) B3857663
theorem B4061927 : Blo 1068616 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B271450075 : Blo 1068616 271450075 := bstep (se 1 (by rfl) ⟨203587556, by rfl⟩ : syracuseStep 271450075 = 407175113) B407175113
theorem B6858067 : Blo 1068616 6858067 := bstep (se 1 (by rfl) ⟨5143550, by rfl⟩ : syracuseStep 6858067 = 10287101) B10287101
theorem B361933433 : Blo 1068616 361933433 := bstep (se 2 (by rfl) ⟨135725037, by rfl⟩ : syracuseStep 361933433 = 271450075) B271450075
theorem B2707951 : Blo 1068616 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B8681069 : Blo 1068616 8681069 := bstep (se 3 (by rfl) ⟨1627700, by rfl⟩ : syracuseStep 8681069 = 3255401) B3255401
theorem B9144089 : Blo 1068616 9144089 := bstep (se 2 (by rfl) ⟨3429033, by rfl⟩ : syracuseStep 9144089 = 6858067) B6858067
theorem B3610601 : Blo 1068616 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B241288955 : Blo 1068616 241288955 := bstep (se 1 (by rfl) ⟨180966716, by rfl⟩ : syracuseStep 241288955 = 361933433) B361933433
theorem B5787379 : Blo 1068616 5787379 := bstep (se 1 (by rfl) ⟨4340534, by rfl⟩ : syracuseStep 5787379 = 8681069) B8681069
theorem B160859303 : Blo 1068616 160859303 := bstep (se 1 (by rfl) ⟨120644477, by rfl⟩ : syracuseStep 160859303 = 241288955) B241288955
theorem B6096059 : Blo 1068616 6096059 := bstep (se 1 (by rfl) ⟨4572044, by rfl⟩ : syracuseStep 6096059 = 9144089) B9144089
theorem B2407067 : Blo 1068616 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B30866021 : Blo 1068616 30866021 := bstep (se 4 (by rfl) ⟨2893689, by rfl⟩ : syracuseStep 30866021 = 5787379) B5787379
theorem B4064039 : Blo 1068616 4064039 := bstep (se 1 (by rfl) ⟨3048029, by rfl⟩ : syracuseStep 4064039 = 6096059) B6096059
theorem B107239535 : Blo 1068616 107239535 := bstep (se 1 (by rfl) ⟨80429651, by rfl⟩ : syracuseStep 107239535 = 160859303) B160859303
theorem B20577347 : Blo 1068616 20577347 := bstep (se 1 (by rfl) ⟨15433010, by rfl⟩ : syracuseStep 20577347 = 30866021) B30866021
theorem B1604711 : Blo 1068616 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B13718231 : Blo 1068616 13718231 := bstep (se 1 (by rfl) ⟨10288673, by rfl⟩ : syracuseStep 13718231 = 20577347) B20577347
theorem B1069807 : Blo 1068616 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B2709359 : Blo 1068616 2709359 := bstep (se 1 (by rfl) ⟨2032019, by rfl⟩ : syracuseStep 2709359 = 4064039) B4064039
theorem B71493023 : Blo 1068616 71493023 := bstep (se 1 (by rfl) ⟨53619767, by rfl⟩ : syracuseStep 71493023 = 107239535) B107239535
theorem B9145487 : Blo 1068616 9145487 := bstep (se 1 (by rfl) ⟨6859115, by rfl⟩ : syracuseStep 9145487 = 13718231) B13718231
theorem B1806239 : Blo 1068616 1806239 := bstep (se 1 (by rfl) ⟨1354679, by rfl⟩ : syracuseStep 1806239 = 2709359) B2709359
theorem B47662015 : Blo 1068616 47662015 := bstep (se 1 (by rfl) ⟨35746511, by rfl⟩ : syracuseStep 47662015 = 71493023) B71493023
theorem B6096991 : Blo 1068616 6096991 := bstep (se 1 (by rfl) ⟨4572743, by rfl⟩ : syracuseStep 6096991 = 9145487) B9145487
theorem B63549353 : Blo 1068616 63549353 := bstep (se 2 (by rfl) ⟨23831007, by rfl⟩ : syracuseStep 63549353 = 47662015) B47662015
theorem B1204159 : Blo 1068616 1204159 := bstep (se 1 (by rfl) ⟨903119, by rfl⟩ : syracuseStep 1204159 = 1806239) B1806239
theorem B8129321 : Blo 1068616 8129321 := bstep (se 2 (by rfl) ⟨3048495, by rfl⟩ : syracuseStep 8129321 = 6096991) B6096991
theorem B42366235 : Blo 1068616 42366235 := bstep (se 1 (by rfl) ⟨31774676, by rfl⟩ : syracuseStep 42366235 = 63549353) B63549353
theorem B1605545 : Blo 1068616 1605545 := bstep (se 2 (by rfl) ⟨602079, by rfl⟩ : syracuseStep 1605545 = 1204159) B1204159
theorem B5419547 : Blo 1068616 5419547 := bstep (se 1 (by rfl) ⟨4064660, by rfl⟩ : syracuseStep 5419547 = 8129321) B8129321
theorem B1070363 : Blo 1068616 1070363 := bstep (se 1 (by rfl) ⟨802772, by rfl⟩ : syracuseStep 1070363 = 1605545) B1605545
theorem B56488313 : Blo 1068616 56488313 := bstep (se 2 (by rfl) ⟨21183117, by rfl⟩ : syracuseStep 56488313 = 42366235) B42366235
theorem B37658875 : Blo 1068616 37658875 := bstep (se 1 (by rfl) ⟨28244156, by rfl⟩ : syracuseStep 37658875 = 56488313) B56488313
theorem B3613031 : Blo 1068616 3613031 := bstep (se 1 (by rfl) ⟨2709773, by rfl⟩ : syracuseStep 3613031 = 5419547) B5419547
theorem B50211833 : Blo 1068616 50211833 := bstep (se 2 (by rfl) ⟨18829437, by rfl⟩ : syracuseStep 50211833 = 37658875) B37658875
theorem B2408687 : Blo 1068616 2408687 := bstep (se 1 (by rfl) ⟨1806515, by rfl⟩ : syracuseStep 2408687 = 3613031) B3613031
theorem B1605791 : Blo 1068616 1605791 := bstep (se 1 (by rfl) ⟨1204343, by rfl⟩ : syracuseStep 1605791 = 2408687) B2408687
theorem B133898221 : Blo 1068616 133898221 := bstep (se 3 (by rfl) ⟨25105916, by rfl⟩ : syracuseStep 133898221 = 50211833) B50211833
theorem B178530961 : Blo 1068616 178530961 := bstep (se 2 (by rfl) ⟨66949110, by rfl⟩ : syracuseStep 178530961 = 133898221) B133898221
theorem B1070527 : Blo 1068616 1070527 := bstep (se 1 (by rfl) ⟨802895, by rfl⟩ : syracuseStep 1070527 = 1605791) B1605791
theorem B238041281 : Blo 1068616 238041281 := bstep (se 2 (by rfl) ⟨89265480, by rfl⟩ : syracuseStep 238041281 = 178530961) B178530961
theorem B158694187 : Blo 1068616 158694187 := bstep (se 1 (by rfl) ⟨119020640, by rfl⟩ : syracuseStep 158694187 = 238041281) B238041281
theorem B211592249 : Blo 1068616 211592249 := bstep (se 2 (by rfl) ⟨79347093, by rfl⟩ : syracuseStep 211592249 = 158694187) B158694187
theorem B141061499 : Blo 1068616 141061499 := bstep (se 1 (by rfl) ⟨105796124, by rfl⟩ : syracuseStep 141061499 = 211592249) B211592249
theorem B94040999 : Blo 1068616 94040999 := bstep (se 1 (by rfl) ⟨70530749, by rfl⟩ : syracuseStep 94040999 = 141061499) B141061499
theorem B62693999 : Blo 1068616 62693999 := bstep (se 1 (by rfl) ⟨47020499, by rfl⟩ : syracuseStep 62693999 = 94040999) B94040999
theorem B41795999 : Blo 1068616 41795999 := bstep (se 1 (by rfl) ⟨31346999, by rfl⟩ : syracuseStep 41795999 = 62693999) B62693999
theorem B27863999 : Blo 1068616 27863999 := bstep (se 1 (by rfl) ⟨20897999, by rfl⟩ : syracuseStep 27863999 = 41795999) B41795999
theorem B18575999 : Blo 1068616 18575999 := bstep (se 1 (by rfl) ⟨13931999, by rfl⟩ : syracuseStep 18575999 = 27863999) B27863999
theorem B12383999 : Blo 1068616 12383999 := bstep (se 1 (by rfl) ⟨9287999, by rfl⟩ : syracuseStep 12383999 = 18575999) B18575999
theorem B8255999 : Blo 1068616 8255999 := bstep (se 1 (by rfl) ⟨6191999, by rfl⟩ : syracuseStep 8255999 = 12383999) B12383999
theorem B5503999 : Blo 1068616 5503999 := bstep (se 1 (by rfl) ⟨4127999, by rfl⟩ : syracuseStep 5503999 = 8255999) B8255999
theorem B7338665 : Blo 1068616 7338665 := bstep (se 2 (by rfl) ⟨2751999, by rfl⟩ : syracuseStep 7338665 = 5503999) B5503999
theorem B4892443 : Blo 1068616 4892443 := bstep (se 1 (by rfl) ⟨3669332, by rfl⟩ : syracuseStep 4892443 = 7338665) B7338665
theorem B26093029 : Blo 1068616 26093029 := bstep (se 4 (by rfl) ⟨2446221, by rfl⟩ : syracuseStep 26093029 = 4892443) B4892443
theorem B34790705 : Blo 1068616 34790705 := bstep (se 2 (by rfl) ⟨13046514, by rfl⟩ : syracuseStep 34790705 = 26093029) B26093029
theorem B23193803 : Blo 1068616 23193803 := bstep (se 1 (by rfl) ⟨17395352, by rfl⟩ : syracuseStep 23193803 = 34790705) B34790705
theorem B15462535 : Blo 1068616 15462535 := bstep (se 1 (by rfl) ⟨11596901, by rfl⟩ : syracuseStep 15462535 = 23193803) B23193803
theorem B20616713 : Blo 1068616 20616713 := bstep (se 2 (by rfl) ⟨7731267, by rfl⟩ : syracuseStep 20616713 = 15462535) B15462535
theorem B13744475 : Blo 1068616 13744475 := bstep (se 1 (by rfl) ⟨10308356, by rfl⟩ : syracuseStep 13744475 = 20616713) B20616713
theorem B9162983 : Blo 1068616 9162983 := bstep (se 1 (by rfl) ⟨6872237, by rfl⟩ : syracuseStep 9162983 = 13744475) B13744475
theorem B6108655 : Blo 1068616 6108655 := bstep (se 1 (by rfl) ⟨4581491, by rfl⟩ : syracuseStep 6108655 = 9162983) B9162983
theorem B8144873 : Blo 1068616 8144873 := bstep (se 2 (by rfl) ⟨3054327, by rfl⟩ : syracuseStep 8144873 = 6108655) B6108655
theorem B5429915 : Blo 1068616 5429915 := bstep (se 1 (by rfl) ⟨4072436, by rfl⟩ : syracuseStep 5429915 = 8144873) B8144873
theorem B3619943 : Blo 1068616 3619943 := bstep (se 1 (by rfl) ⟨2714957, by rfl⟩ : syracuseStep 3619943 = 5429915) B5429915
theorem B2413295 : Blo 1068616 2413295 := bstep (se 1 (by rfl) ⟨1809971, by rfl⟩ : syracuseStep 2413295 = 3619943) B3619943
theorem B1608863 : Blo 1068616 1608863 := bstep (se 1 (by rfl) ⟨1206647, by rfl⟩ : syracuseStep 1608863 = 2413295) B2413295
theorem B1072575 : Blo 1068616 1072575 := bstep (se 1 (by rfl) ⟨804431, by rfl⟩ : syracuseStep 1072575 = 1608863) B1608863

theorem C0 (j : ℕ) (h1 : 267154 ≤ j) (h2 : j ≤ 267853) : Blo 1068616 (4 * j + 3) := by
  interval_cases j
  · exact B1068619
  · exact B1068623
  · exact B1068627
  · exact B1068631
  · exact B1068635
  · exact B1068639
  · exact B1068643
  · exact B1068647
  · exact B1068651
  · exact B1068655
  · exact B1068659
  · exact B1068663
  · exact B1068667
  · exact B1068671
  · exact B1068675
  · exact B1068679
  · exact B1068683
  · exact B1068687
  · exact B1068691
  · exact B1068695
  · exact B1068699
  · exact B1068703
  · exact B1068707
  · exact B1068711
  · exact B1068715
  · exact B1068719
  · exact B1068723
  · exact B1068727
  · exact B1068731
  · exact B1068735
  · exact B1068739
  · exact B1068743
  · exact B1068747
  · exact B1068751
  · exact B1068755
  · exact B1068759
  · exact B1068763
  · exact B1068767
  · exact B1068771
  · exact B1068775
  · exact B1068779
  · exact B1068783
  · exact B1068787
  · exact B1068791
  · exact B1068795
  · exact B1068799
  · exact B1068803
  · exact B1068807
  · exact B1068811
  · exact B1068815
  · exact B1068819
  · exact B1068823
  · exact B1068827
  · exact B1068831
  · exact B1068835
  · exact B1068839
  · exact B1068843
  · exact B1068847
  · exact B1068851
  · exact B1068855
  · exact B1068859
  · exact B1068863
  · exact B1068867
  · exact B1068871
  · exact B1068875
  · exact B1068879
  · exact B1068883
  · exact B1068887
  · exact B1068891
  · exact B1068895
  · exact B1068899
  · exact B1068903
  · exact B1068907
  · exact B1068911
  · exact B1068915
  · exact B1068919
  · exact B1068923
  · exact B1068927
  · exact B1068931
  · exact B1068935
  · exact B1068939
  · exact B1068943
  · exact B1068947
  · exact B1068951
  · exact B1068955
  · exact B1068959
  · exact B1068963
  · exact B1068967
  · exact B1068971
  · exact B1068975
  · exact B1068979
  · exact B1068983
  · exact B1068987
  · exact B1068991
  · exact B1068995
  · exact B1068999
  · exact B1069003
  · exact B1069007
  · exact B1069011
  · exact B1069015
  · exact B1069019
  · exact B1069023
  · exact B1069027
  · exact B1069031
  · exact B1069035
  · exact B1069039
  · exact B1069043
  · exact B1069047
  · exact B1069051
  · exact B1069055
  · exact B1069059
  · exact B1069063
  · exact B1069067
  · exact B1069071
  · exact B1069075
  · exact B1069079
  · exact B1069083
  · exact B1069087
  · exact B1069091
  · exact B1069095
  · exact B1069099
  · exact B1069103
  · exact B1069107
  · exact B1069111
  · exact B1069115
  · exact B1069119
  · exact B1069123
  · exact B1069127
  · exact B1069131
  · exact B1069135
  · exact B1069139
  · exact B1069143
  · exact B1069147
  · exact B1069151
  · exact B1069155
  · exact B1069159
  · exact B1069163
  · exact B1069167
  · exact B1069171
  · exact B1069175
  · exact B1069179
  · exact B1069183
  · exact B1069187
  · exact B1069191
  · exact B1069195
  · exact B1069199
  · exact B1069203
  · exact B1069207
  · exact B1069211
  · exact B1069215
  · exact B1069219
  · exact B1069223
  · exact B1069227
  · exact B1069231
  · exact B1069235
  · exact B1069239
  · exact B1069243
  · exact B1069247
  · exact B1069251
  · exact B1069255
  · exact B1069259
  · exact B1069263
  · exact B1069267
  · exact B1069271
  · exact B1069275
  · exact B1069279
  · exact B1069283
  · exact B1069287
  · exact B1069291
  · exact B1069295
  · exact B1069299
  · exact B1069303
  · exact B1069307
  · exact B1069311
  · exact B1069315
  · exact B1069319
  · exact B1069323
  · exact B1069327
  · exact B1069331
  · exact B1069335
  · exact B1069339
  · exact B1069343
  · exact B1069347
  · exact B1069351
  · exact B1069355
  · exact B1069359
  · exact B1069363
  · exact B1069367
  · exact B1069371
  · exact B1069375
  · exact B1069379
  · exact B1069383
  · exact B1069387
  · exact B1069391
  · exact B1069395
  · exact B1069399
  · exact B1069403
  · exact B1069407
  · exact B1069411
  · exact B1069415
  · exact B1069419
  · exact B1069423
  · exact B1069427
  · exact B1069431
  · exact B1069435
  · exact B1069439
  · exact B1069443
  · exact B1069447
  · exact B1069451
  · exact B1069455
  · exact B1069459
  · exact B1069463
  · exact B1069467
  · exact B1069471
  · exact B1069475
  · exact B1069479
  · exact B1069483
  · exact B1069487
  · exact B1069491
  · exact B1069495
  · exact B1069499
  · exact B1069503
  · exact B1069507
  · exact B1069511
  · exact B1069515
  · exact B1069519
  · exact B1069523
  · exact B1069527
  · exact B1069531
  · exact B1069535
  · exact B1069539
  · exact B1069543
  · exact B1069547
  · exact B1069551
  · exact B1069555
  · exact B1069559
  · exact B1069563
  · exact B1069567
  · exact B1069571
  · exact B1069575
  · exact B1069579
  · exact B1069583
  · exact B1069587
  · exact B1069591
  · exact B1069595
  · exact B1069599
  · exact B1069603
  · exact B1069607
  · exact B1069611
  · exact B1069615
  · exact B1069619
  · exact B1069623
  · exact B1069627
  · exact B1069631
  · exact B1069635
  · exact B1069639
  · exact B1069643
  · exact B1069647
  · exact B1069651
  · exact B1069655
  · exact B1069659
  · exact B1069663
  · exact B1069667
  · exact B1069671
  · exact B1069675
  · exact B1069679
  · exact B1069683
  · exact B1069687
  · exact B1069691
  · exact B1069695
  · exact B1069699
  · exact B1069703
  · exact B1069707
  · exact B1069711
  · exact B1069715
  · exact B1069719
  · exact B1069723
  · exact B1069727
  · exact B1069731
  · exact B1069735
  · exact B1069739
  · exact B1069743
  · exact B1069747
  · exact B1069751
  · exact B1069755
  · exact B1069759
  · exact B1069763
  · exact B1069767
  · exact B1069771
  · exact B1069775
  · exact B1069779
  · exact B1069783
  · exact B1069787
  · exact B1069791
  · exact B1069795
  · exact B1069799
  · exact B1069803
  · exact B1069807
  · exact B1069811
  · exact B1069815
  · exact B1069819
  · exact B1069823
  · exact B1069827
  · exact B1069831
  · exact B1069835
  · exact B1069839
  · exact B1069843
  · exact B1069847
  · exact B1069851
  · exact B1069855
  · exact B1069859
  · exact B1069863
  · exact B1069867
  · exact B1069871
  · exact B1069875
  · exact B1069879
  · exact B1069883
  · exact B1069887
  · exact B1069891
  · exact B1069895
  · exact B1069899
  · exact B1069903
  · exact B1069907
  · exact B1069911
  · exact B1069915
  · exact B1069919
  · exact B1069923
  · exact B1069927
  · exact B1069931
  · exact B1069935
  · exact B1069939
  · exact B1069943
  · exact B1069947
  · exact B1069951
  · exact B1069955
  · exact B1069959
  · exact B1069963
  · exact B1069967
  · exact B1069971
  · exact B1069975
  · exact B1069979
  · exact B1069983
  · exact B1069987
  · exact B1069991
  · exact B1069995
  · exact B1069999
  · exact B1070003
  · exact B1070007
  · exact B1070011
  · exact B1070015
  · exact B1070019
  · exact B1070023
  · exact B1070027
  · exact B1070031
  · exact B1070035
  · exact B1070039
  · exact B1070043
  · exact B1070047
  · exact B1070051
  · exact B1070055
  · exact B1070059
  · exact B1070063
  · exact B1070067
  · exact B1070071
  · exact B1070075
  · exact B1070079
  · exact B1070083
  · exact B1070087
  · exact B1070091
  · exact B1070095
  · exact B1070099
  · exact B1070103
  · exact B1070107
  · exact B1070111
  · exact B1070115
  · exact B1070119
  · exact B1070123
  · exact B1070127
  · exact B1070131
  · exact B1070135
  · exact B1070139
  · exact B1070143
  · exact B1070147
  · exact B1070151
  · exact B1070155
  · exact B1070159
  · exact B1070163
  · exact B1070167
  · exact B1070171
  · exact B1070175
  · exact B1070179
  · exact B1070183
  · exact B1070187
  · exact B1070191
  · exact B1070195
  · exact B1070199
  · exact B1070203
  · exact B1070207
  · exact B1070211
  · exact B1070215
  · exact B1070219
  · exact B1070223
  · exact B1070227
  · exact B1070231
  · exact B1070235
  · exact B1070239
  · exact B1070243
  · exact B1070247
  · exact B1070251
  · exact B1070255
  · exact B1070259
  · exact B1070263
  · exact B1070267
  · exact B1070271
  · exact B1070275
  · exact B1070279
  · exact B1070283
  · exact B1070287
  · exact B1070291
  · exact B1070295
  · exact B1070299
  · exact B1070303
  · exact B1070307
  · exact B1070311
  · exact B1070315
  · exact B1070319
  · exact B1070323
  · exact B1070327
  · exact B1070331
  · exact B1070335
  · exact B1070339
  · exact B1070343
  · exact B1070347
  · exact B1070351
  · exact B1070355
  · exact B1070359
  · exact B1070363
  · exact B1070367
  · exact B1070371
  · exact B1070375
  · exact B1070379
  · exact B1070383
  · exact B1070387
  · exact B1070391
  · exact B1070395
  · exact B1070399
  · exact B1070403
  · exact B1070407
  · exact B1070411
  · exact B1070415
  · exact B1070419
  · exact B1070423
  · exact B1070427
  · exact B1070431
  · exact B1070435
  · exact B1070439
  · exact B1070443
  · exact B1070447
  · exact B1070451
  · exact B1070455
  · exact B1070459
  · exact B1070463
  · exact B1070467
  · exact B1070471
  · exact B1070475
  · exact B1070479
  · exact B1070483
  · exact B1070487
  · exact B1070491
  · exact B1070495
  · exact B1070499
  · exact B1070503
  · exact B1070507
  · exact B1070511
  · exact B1070515
  · exact B1070519
  · exact B1070523
  · exact B1070527
  · exact B1070531
  · exact B1070535
  · exact B1070539
  · exact B1070543
  · exact B1070547
  · exact B1070551
  · exact B1070555
  · exact B1070559
  · exact B1070563
  · exact B1070567
  · exact B1070571
  · exact B1070575
  · exact B1070579
  · exact B1070583
  · exact B1070587
  · exact B1070591
  · exact B1070595
  · exact B1070599
  · exact B1070603
  · exact B1070607
  · exact B1070611
  · exact B1070615
  · exact B1070619
  · exact B1070623
  · exact B1070627
  · exact B1070631
  · exact B1070635
  · exact B1070639
  · exact B1070643
  · exact B1070647
  · exact B1070651
  · exact B1070655
  · exact B1070659
  · exact B1070663
  · exact B1070667
  · exact B1070671
  · exact B1070675
  · exact B1070679
  · exact B1070683
  · exact B1070687
  · exact B1070691
  · exact B1070695
  · exact B1070699
  · exact B1070703
  · exact B1070707
  · exact B1070711
  · exact B1070715
  · exact B1070719
  · exact B1070723
  · exact B1070727
  · exact B1070731
  · exact B1070735
  · exact B1070739
  · exact B1070743
  · exact B1070747
  · exact B1070751
  · exact B1070755
  · exact B1070759
  · exact B1070763
  · exact B1070767
  · exact B1070771
  · exact B1070775
  · exact B1070779
  · exact B1070783
  · exact B1070787
  · exact B1070791
  · exact B1070795
  · exact B1070799
  · exact B1070803
  · exact B1070807
  · exact B1070811
  · exact B1070815
  · exact B1070819
  · exact B1070823
  · exact B1070827
  · exact B1070831
  · exact B1070835
  · exact B1070839
  · exact B1070843
  · exact B1070847
  · exact B1070851
  · exact B1070855
  · exact B1070859
  · exact B1070863
  · exact B1070867
  · exact B1070871
  · exact B1070875
  · exact B1070879
  · exact B1070883
  · exact B1070887
  · exact B1070891
  · exact B1070895
  · exact B1070899
  · exact B1070903
  · exact B1070907
  · exact B1070911
  · exact B1070915
  · exact B1070919
  · exact B1070923
  · exact B1070927
  · exact B1070931
  · exact B1070935
  · exact B1070939
  · exact B1070943
  · exact B1070947
  · exact B1070951
  · exact B1070955
  · exact B1070959
  · exact B1070963
  · exact B1070967
  · exact B1070971
  · exact B1070975
  · exact B1070979
  · exact B1070983
  · exact B1070987
  · exact B1070991
  · exact B1070995
  · exact B1070999
  · exact B1071003
  · exact B1071007
  · exact B1071011
  · exact B1071015
  · exact B1071019
  · exact B1071023
  · exact B1071027
  · exact B1071031
  · exact B1071035
  · exact B1071039
  · exact B1071043
  · exact B1071047
  · exact B1071051
  · exact B1071055
  · exact B1071059
  · exact B1071063
  · exact B1071067
  · exact B1071071
  · exact B1071075
  · exact B1071079
  · exact B1071083
  · exact B1071087
  · exact B1071091
  · exact B1071095
  · exact B1071099
  · exact B1071103
  · exact B1071107
  · exact B1071111
  · exact B1071115
  · exact B1071119
  · exact B1071123
  · exact B1071127
  · exact B1071131
  · exact B1071135
  · exact B1071139
  · exact B1071143
  · exact B1071147
  · exact B1071151
  · exact B1071155
  · exact B1071159
  · exact B1071163
  · exact B1071167
  · exact B1071171
  · exact B1071175
  · exact B1071179
  · exact B1071183
  · exact B1071187
  · exact B1071191
  · exact B1071195
  · exact B1071199
  · exact B1071203
  · exact B1071207
  · exact B1071211
  · exact B1071215
  · exact B1071219
  · exact B1071223
  · exact B1071227
  · exact B1071231
  · exact B1071235
  · exact B1071239
  · exact B1071243
  · exact B1071247
  · exact B1071251
  · exact B1071255
  · exact B1071259
  · exact B1071263
  · exact B1071267
  · exact B1071271
  · exact B1071275
  · exact B1071279
  · exact B1071283
  · exact B1071287
  · exact B1071291
  · exact B1071295
  · exact B1071299
  · exact B1071303
  · exact B1071307
  · exact B1071311
  · exact B1071315
  · exact B1071319
  · exact B1071323
  · exact B1071327
  · exact B1071331
  · exact B1071335
  · exact B1071339
  · exact B1071343
  · exact B1071347
  · exact B1071351
  · exact B1071355
  · exact B1071359
  · exact B1071363
  · exact B1071367
  · exact B1071371
  · exact B1071375
  · exact B1071379
  · exact B1071383
  · exact B1071387
  · exact B1071391
  · exact B1071395
  · exact B1071399
  · exact B1071403
  · exact B1071407
  · exact B1071411
  · exact B1071415

theorem C1 (j : ℕ) (h1 : 267854 ≤ j) (h2 : j ≤ 268153) : Blo 1068616 (4 * j + 3) := by
  interval_cases j
  · exact B1071419
  · exact B1071423
  · exact B1071427
  · exact B1071431
  · exact B1071435
  · exact B1071439
  · exact B1071443
  · exact B1071447
  · exact B1071451
  · exact B1071455
  · exact B1071459
  · exact B1071463
  · exact B1071467
  · exact B1071471
  · exact B1071475
  · exact B1071479
  · exact B1071483
  · exact B1071487
  · exact B1071491
  · exact B1071495
  · exact B1071499
  · exact B1071503
  · exact B1071507
  · exact B1071511
  · exact B1071515
  · exact B1071519
  · exact B1071523
  · exact B1071527
  · exact B1071531
  · exact B1071535
  · exact B1071539
  · exact B1071543
  · exact B1071547
  · exact B1071551
  · exact B1071555
  · exact B1071559
  · exact B1071563
  · exact B1071567
  · exact B1071571
  · exact B1071575
  · exact B1071579
  · exact B1071583
  · exact B1071587
  · exact B1071591
  · exact B1071595
  · exact B1071599
  · exact B1071603
  · exact B1071607
  · exact B1071611
  · exact B1071615
  · exact B1071619
  · exact B1071623
  · exact B1071627
  · exact B1071631
  · exact B1071635
  · exact B1071639
  · exact B1071643
  · exact B1071647
  · exact B1071651
  · exact B1071655
  · exact B1071659
  · exact B1071663
  · exact B1071667
  · exact B1071671
  · exact B1071675
  · exact B1071679
  · exact B1071683
  · exact B1071687
  · exact B1071691
  · exact B1071695
  · exact B1071699
  · exact B1071703
  · exact B1071707
  · exact B1071711
  · exact B1071715
  · exact B1071719
  · exact B1071723
  · exact B1071727
  · exact B1071731
  · exact B1071735
  · exact B1071739
  · exact B1071743
  · exact B1071747
  · exact B1071751
  · exact B1071755
  · exact B1071759
  · exact B1071763
  · exact B1071767
  · exact B1071771
  · exact B1071775
  · exact B1071779
  · exact B1071783
  · exact B1071787
  · exact B1071791
  · exact B1071795
  · exact B1071799
  · exact B1071803
  · exact B1071807
  · exact B1071811
  · exact B1071815
  · exact B1071819
  · exact B1071823
  · exact B1071827
  · exact B1071831
  · exact B1071835
  · exact B1071839
  · exact B1071843
  · exact B1071847
  · exact B1071851
  · exact B1071855
  · exact B1071859
  · exact B1071863
  · exact B1071867
  · exact B1071871
  · exact B1071875
  · exact B1071879
  · exact B1071883
  · exact B1071887
  · exact B1071891
  · exact B1071895
  · exact B1071899
  · exact B1071903
  · exact B1071907
  · exact B1071911
  · exact B1071915
  · exact B1071919
  · exact B1071923
  · exact B1071927
  · exact B1071931
  · exact B1071935
  · exact B1071939
  · exact B1071943
  · exact B1071947
  · exact B1071951
  · exact B1071955
  · exact B1071959
  · exact B1071963
  · exact B1071967
  · exact B1071971
  · exact B1071975
  · exact B1071979
  · exact B1071983
  · exact B1071987
  · exact B1071991
  · exact B1071995
  · exact B1071999
  · exact B1072003
  · exact B1072007
  · exact B1072011
  · exact B1072015
  · exact B1072019
  · exact B1072023
  · exact B1072027
  · exact B1072031
  · exact B1072035
  · exact B1072039
  · exact B1072043
  · exact B1072047
  · exact B1072051
  · exact B1072055
  · exact B1072059
  · exact B1072063
  · exact B1072067
  · exact B1072071
  · exact B1072075
  · exact B1072079
  · exact B1072083
  · exact B1072087
  · exact B1072091
  · exact B1072095
  · exact B1072099
  · exact B1072103
  · exact B1072107
  · exact B1072111
  · exact B1072115
  · exact B1072119
  · exact B1072123
  · exact B1072127
  · exact B1072131
  · exact B1072135
  · exact B1072139
  · exact B1072143
  · exact B1072147
  · exact B1072151
  · exact B1072155
  · exact B1072159
  · exact B1072163
  · exact B1072167
  · exact B1072171
  · exact B1072175
  · exact B1072179
  · exact B1072183
  · exact B1072187
  · exact B1072191
  · exact B1072195
  · exact B1072199
  · exact B1072203
  · exact B1072207
  · exact B1072211
  · exact B1072215
  · exact B1072219
  · exact B1072223
  · exact B1072227
  · exact B1072231
  · exact B1072235
  · exact B1072239
  · exact B1072243
  · exact B1072247
  · exact B1072251
  · exact B1072255
  · exact B1072259
  · exact B1072263
  · exact B1072267
  · exact B1072271
  · exact B1072275
  · exact B1072279
  · exact B1072283
  · exact B1072287
  · exact B1072291
  · exact B1072295
  · exact B1072299
  · exact B1072303
  · exact B1072307
  · exact B1072311
  · exact B1072315
  · exact B1072319
  · exact B1072323
  · exact B1072327
  · exact B1072331
  · exact B1072335
  · exact B1072339
  · exact B1072343
  · exact B1072347
  · exact B1072351
  · exact B1072355
  · exact B1072359
  · exact B1072363
  · exact B1072367
  · exact B1072371
  · exact B1072375
  · exact B1072379
  · exact B1072383
  · exact B1072387
  · exact B1072391
  · exact B1072395
  · exact B1072399
  · exact B1072403
  · exact B1072407
  · exact B1072411
  · exact B1072415
  · exact B1072419
  · exact B1072423
  · exact B1072427
  · exact B1072431
  · exact B1072435
  · exact B1072439
  · exact B1072443
  · exact B1072447
  · exact B1072451
  · exact B1072455
  · exact B1072459
  · exact B1072463
  · exact B1072467
  · exact B1072471
  · exact B1072475
  · exact B1072479
  · exact B1072483
  · exact B1072487
  · exact B1072491
  · exact B1072495
  · exact B1072499
  · exact B1072503
  · exact B1072507
  · exact B1072511
  · exact B1072515
  · exact B1072519
  · exact B1072523
  · exact B1072527
  · exact B1072531
  · exact B1072535
  · exact B1072539
  · exact B1072543
  · exact B1072547
  · exact B1072551
  · exact B1072555
  · exact B1072559
  · exact B1072563
  · exact B1072567
  · exact B1072571
  · exact B1072575
  · exact B1072579
  · exact B1072583
  · exact B1072587
  · exact B1072591
  · exact B1072595
  · exact B1072599
  · exact B1072603
  · exact B1072607
  · exact B1072611
  · exact B1072615

theorem solution (m : ℕ) (hlo : 1068616 ≤ m) (hhi : m ≤ 1072616) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 267154 ≤ j := by omega
    have hj2 : j ≤ 268153 := by omega
    have hb : Blo 1068616 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 267854 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
