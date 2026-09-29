-- Prove2me | solution 1 for syracuse_descends_range_334751_338751
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:32.39285+00:00
-- url     : https://prove2.me/submissions/48f8d766-ae97-4ad7-82c0-ba3dd96151d3

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


theorem B425989 : Blo 334751 425989 := bbase (se 4 (by rfl) ⟨39936, by rfl⟩ : syracuseStep 425989 = 79873) (by norm_num)
theorem B753677 : Blo 334751 753677 := bbase (se 3 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 753677 = 282629) (by norm_num)
theorem B852029 : Blo 334751 852029 := bbase (se 3 (by rfl) ⟨159755, by rfl⟩ : syracuseStep 852029 = 319511) (by norm_num)
theorem B753749 : Blo 334751 753749 := bbase (se 8 (by rfl) ⟨4416, by rfl⟩ : syracuseStep 753749 = 8833) (by norm_num)
theorem B753821 : Blo 334751 753821 := bbase (se 3 (by rfl) ⟨141341, by rfl⟩ : syracuseStep 753821 = 282683) (by norm_num)
theorem B426161 : Blo 334751 426161 := bbase (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) (by norm_num)
theorem B753893 : Blo 334751 753893 := bbase (se 4 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 753893 = 141355) (by norm_num)
theorem B426217 : Blo 334751 426217 := bbase (se 2 (by rfl) ⟨159831, by rfl⟩ : syracuseStep 426217 = 319663) (by norm_num)
theorem B852221 : Blo 334751 852221 := bbase (se 3 (by rfl) ⟨159791, by rfl⟩ : syracuseStep 852221 = 319583) (by norm_num)
theorem B1442053 : Blo 334751 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B753965 : Blo 334751 753965 := bbase (se 3 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 753965 = 282737) (by norm_num)
theorem B1081669 : Blo 334751 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B426313 : Blo 334751 426313 := bbase (se 2 (by rfl) ⟨159867, by rfl⟩ : syracuseStep 426313 = 319735) (by norm_num)
theorem B688493 : Blo 334751 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B754037 : Blo 334751 754037 := bbase (se 5 (by rfl) ⟨35345, by rfl⟩ : syracuseStep 754037 = 70691) (by norm_num)
theorem B360821 : Blo 334751 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B754109 : Blo 334751 754109 := bbase (se 3 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 754109 = 282791) (by norm_num)
theorem B688589 : Blo 334751 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B426485 : Blo 334751 426485 := bbase (se 5 (by rfl) ⟨19991, by rfl⟩ : syracuseStep 426485 = 39983) (by norm_num)
theorem B754181 : Blo 334751 754181 := bbase (se 4 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 754181 = 141409) (by norm_num)
theorem B426541 : Blo 334751 426541 := bbase (se 3 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 426541 = 159953) (by norm_num)
theorem B754253 : Blo 334751 754253 := bbase (se 3 (by rfl) ⟨141422, by rfl⟩ : syracuseStep 754253 = 282845) (by norm_num)
theorem B852565 : Blo 334751 852565 := bbase (se 8 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 852565 = 9991) (by norm_num)
theorem B21955157 : Blo 334751 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B426637 : Blo 334751 426637 := bbase (se 3 (by rfl) ⟨79994, by rfl⟩ : syracuseStep 426637 = 159989) (by norm_num)
theorem B754325 : Blo 334751 754325 := bbase (se 6 (by rfl) ⟨17679, by rfl⟩ : syracuseStep 754325 = 35359) (by norm_num)
theorem B852677 : Blo 334751 852677 := bbase (se 4 (by rfl) ⟨79938, by rfl⟩ : syracuseStep 852677 = 159877) (by norm_num)
theorem B754397 : Blo 334751 754397 := bbase (se 3 (by rfl) ⟨141449, by rfl⟩ : syracuseStep 754397 = 282899) (by norm_num)
theorem B1704725 : Blo 334751 1704725 := bbase (se 6 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 1704725 = 79909) (by norm_num)
theorem B754469 : Blo 334751 754469 := bbase (se 4 (by rfl) ⟨70731, by rfl⟩ : syracuseStep 754469 = 141463) (by norm_num)
theorem B361265 : Blo 334751 361265 := bbase (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) (by norm_num)
theorem B1278773 : Blo 334751 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B426809 : Blo 334751 426809 := bbase (se 2 (by rfl) ⟨160053, by rfl⟩ : syracuseStep 426809 = 320107) (by norm_num)
theorem B1737557 : Blo 334751 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B754541 : Blo 334751 754541 := bbase (se 3 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 754541 = 282953) (by norm_num)
theorem B426865 : Blo 334751 426865 := bbase (se 2 (by rfl) ⟨160074, by rfl⟩ : syracuseStep 426865 = 320149) (by norm_num)
theorem B2196341 : Blo 334751 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B852869 : Blo 334751 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721813 : Blo 334751 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B754613 : Blo 334751 754613 := bbase (se 5 (by rfl) ⟨35372, by rfl⟩ : syracuseStep 754613 = 70745) (by norm_num)
theorem B426961 : Blo 334751 426961 := bbase (se 2 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 426961 = 320221) (by norm_num)
theorem B754685 : Blo 334751 754685 := bbase (se 3 (by rfl) ⟨141503, by rfl⟩ : syracuseStep 754685 = 283007) (by norm_num)
theorem B361513 : Blo 334751 361513 := bbase (se 2 (by rfl) ⟨135567, by rfl⟩ : syracuseStep 361513 = 271135) (by norm_num)
theorem B754757 : Blo 334751 754757 := bbase (se 4 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 754757 = 141517) (by norm_num)
theorem B1279061 : Blo 334751 1279061 := bbase (se 8 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 1279061 = 14989) (by norm_num)
theorem B427133 : Blo 334751 427133 := bbase (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) (by norm_num)
theorem B754829 : Blo 334751 754829 := bbase (se 3 (by rfl) ⟨141530, by rfl⟩ : syracuseStep 754829 = 283061) (by norm_num)
theorem B427189 : Blo 334751 427189 := bbase (se 5 (by rfl) ⟨20024, by rfl⟩ : syracuseStep 427189 = 40049) (by norm_num)
theorem B754901 : Blo 334751 754901 := bbase (se 7 (by rfl) ⟨8846, by rfl⟩ : syracuseStep 754901 = 17693) (by norm_num)
theorem B853213 : Blo 334751 853213 := bbase (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) (by norm_num)
theorem B722189 : Blo 334751 722189 := bbase (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) (by norm_num)
theorem B427285 : Blo 334751 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B754973 : Blo 334751 754973 := bbase (se 3 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 754973 = 283115) (by norm_num)
theorem B918821 : Blo 334751 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B853325 : Blo 334751 853325 := bbase (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) (by norm_num)
theorem B755045 : Blo 334751 755045 := bbase (se 4 (by rfl) ⟨70785, by rfl⟩ : syracuseStep 755045 = 141571) (by norm_num)
theorem B755117 : Blo 334751 755117 := bbase (se 3 (by rfl) ⟨141584, by rfl⟩ : syracuseStep 755117 = 283169) (by norm_num)
theorem B427457 : Blo 334751 427457 := bbase (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) (by norm_num)
theorem B460261 : Blo 334751 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B755189 : Blo 334751 755189 := bbase (se 5 (by rfl) ⟨35399, by rfl⟩ : syracuseStep 755189 = 70799) (by norm_num)
theorem B427513 : Blo 334751 427513 := bbase (se 2 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 427513 = 320635) (by norm_num)
theorem B853517 : Blo 334751 853517 := bbase (se 3 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 853517 = 320069) (by norm_num)
theorem B755261 : Blo 334751 755261 := bbase (se 3 (by rfl) ⟨141611, by rfl⟩ : syracuseStep 755261 = 283223) (by norm_num)
theorem B427609 : Blo 334751 427609 := bbase (se 2 (by rfl) ⟨160353, by rfl⟩ : syracuseStep 427609 = 320707) (by norm_num)
theorem B755333 : Blo 334751 755333 := bbase (se 4 (by rfl) ⟨70812, by rfl⟩ : syracuseStep 755333 = 141625) (by norm_num)
theorem B755405 : Blo 334751 755405 := bbase (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) (by norm_num)
theorem B1443541 : Blo 334751 1443541 := bbase (se 7 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 1443541 = 33833) (by norm_num)
theorem B1443557 : Blo 334751 1443557 := bbase (se 4 (by rfl) ⟨135333, by rfl⟩ : syracuseStep 1443557 = 270667) (by norm_num)
theorem B427781 : Blo 334751 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B755477 : Blo 334751 755477 := bbase (se 6 (by rfl) ⟨17706, by rfl⟩ : syracuseStep 755477 = 35413) (by norm_num)
theorem B427837 : Blo 334751 427837 := bbase (se 3 (by rfl) ⟨80219, by rfl⟩ : syracuseStep 427837 = 160439) (by norm_num)
theorem B755549 : Blo 334751 755549 := bbase (se 3 (by rfl) ⟨141665, by rfl⟩ : syracuseStep 755549 = 283331) (by norm_num)
theorem B853861 : Blo 334751 853861 := bbase (se 4 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 853861 = 160099) (by norm_num)
theorem B3475349 : Blo 334751 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B427933 : Blo 334751 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B755621 : Blo 334751 755621 := bbase (se 4 (by rfl) ⟨70839, by rfl⟩ : syracuseStep 755621 = 141679) (by norm_num)
theorem B853973 : Blo 334751 853973 := bbase (se 7 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 853973 = 20015) (by norm_num)
theorem B755693 : Blo 334751 755693 := bbase (se 3 (by rfl) ⟨141692, by rfl⟩ : syracuseStep 755693 = 283385) (by norm_num)
theorem B526357 : Blo 334751 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B1706021 : Blo 334751 1706021 := bbase (se 4 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 1706021 = 319879) (by norm_num)
theorem B755765 : Blo 334751 755765 := bbase (se 5 (by rfl) ⟨35426, by rfl⟩ : syracuseStep 755765 = 70853) (by norm_num)
theorem B428105 : Blo 334751 428105 := bbase (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) (by norm_num)
theorem B755837 : Blo 334751 755837 := bbase (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) (by norm_num)
theorem B428161 : Blo 334751 428161 := bbase (se 2 (by rfl) ⟨160560, by rfl⟩ : syracuseStep 428161 = 321121) (by norm_num)
theorem B854165 : Blo 334751 854165 := bbase (se 6 (by rfl) ⟨20019, by rfl⟩ : syracuseStep 854165 = 40039) (by norm_num)
theorem B755909 : Blo 334751 755909 := bbase (se 4 (by rfl) ⟨70866, by rfl⟩ : syracuseStep 755909 = 141733) (by norm_num)
theorem B1542341 : Blo 334751 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B428257 : Blo 334751 428257 := bbase (se 2 (by rfl) ⟨160596, by rfl⟩ : syracuseStep 428257 = 321193) (by norm_num)
theorem B1280245 : Blo 334751 1280245 := bbase (se 5 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 1280245 = 120023) (by norm_num)
theorem B755981 : Blo 334751 755981 := bbase (se 3 (by rfl) ⟨141746, by rfl⟩ : syracuseStep 755981 = 283493) (by norm_num)
theorem B756053 : Blo 334751 756053 := bbase (se 10 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 756053 = 2215) (by norm_num)
theorem B428429 : Blo 334751 428429 := bbase (se 3 (by rfl) ⟨80330, by rfl⟩ : syracuseStep 428429 = 160661) (by norm_num)
theorem B756125 : Blo 334751 756125 := bbase (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) (by norm_num)
theorem B428485 : Blo 334751 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B756197 : Blo 334751 756197 := bbase (se 4 (by rfl) ⟨70893, by rfl⟩ : syracuseStep 756197 = 141787) (by norm_num)
theorem B854509 : Blo 334751 854509 := bbase (se 3 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 854509 = 320441) (by norm_num)
theorem B1280549 : Blo 334751 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B428581 : Blo 334751 428581 := bbase (se 4 (by rfl) ⟨40179, by rfl⟩ : syracuseStep 428581 = 80359) (by norm_num)
theorem B756269 : Blo 334751 756269 := bbase (se 3 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 756269 = 283601) (by norm_num)
theorem B854621 : Blo 334751 854621 := bbase (se 3 (by rfl) ⟨160241, by rfl⟩ : syracuseStep 854621 = 320483) (by norm_num)
theorem B756341 : Blo 334751 756341 := bbase (se 5 (by rfl) ⟨35453, by rfl⟩ : syracuseStep 756341 = 70907) (by norm_num)
theorem B2886293 : Blo 334751 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B756413 : Blo 334751 756413 := bbase (se 3 (by rfl) ⟨141827, by rfl⟩ : syracuseStep 756413 = 283655) (by norm_num)
theorem B756485 : Blo 334751 756485 := bbase (se 4 (by rfl) ⟨70920, by rfl⟩ : syracuseStep 756485 = 141841) (by norm_num)
theorem B854813 : Blo 334751 854813 := bbase (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) (by norm_num)
theorem B756557 : Blo 334751 756557 := bbase (se 3 (by rfl) ⟨141854, by rfl⟩ : syracuseStep 756557 = 283709) (by norm_num)
theorem B756629 : Blo 334751 756629 := bbase (se 6 (by rfl) ⟨17733, by rfl⟩ : syracuseStep 756629 = 35467) (by norm_num)
theorem B756701 : Blo 334751 756701 := bbase (se 3 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 756701 = 283763) (by norm_num)
theorem B756773 : Blo 334751 756773 := bbase (se 4 (by rfl) ⟨70947, by rfl⟩ : syracuseStep 756773 = 141895) (by norm_num)
theorem B756845 : Blo 334751 756845 := bbase (se 3 (by rfl) ⟨141908, by rfl⟩ : syracuseStep 756845 = 283817) (by norm_num)
theorem B855157 : Blo 334751 855157 := bbase (se 5 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 855157 = 80171) (by norm_num)
theorem B1084565 : Blo 334751 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B756917 : Blo 334751 756917 := bbase (se 5 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 756917 = 70961) (by norm_num)
theorem B855269 : Blo 334751 855269 := bbase (se 4 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 855269 = 160363) (by norm_num)
theorem B756989 : Blo 334751 756989 := bbase (se 3 (by rfl) ⟨141935, by rfl⟩ : syracuseStep 756989 = 283871) (by norm_num)
theorem B1707317 : Blo 334751 1707317 := bbase (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) (by norm_num)
theorem B691517 : Blo 334751 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B953669 : Blo 334751 953669 := bbase (se 4 (by rfl) ⟨89406, by rfl⟩ : syracuseStep 953669 = 178813) (by norm_num)
theorem B757061 : Blo 334751 757061 := bbase (se 4 (by rfl) ⟨70974, by rfl⟩ : syracuseStep 757061 = 141949) (by norm_num)
theorem B757133 : Blo 334751 757133 := bbase (se 3 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 757133 = 283925) (by norm_num)
theorem B855461 : Blo 334751 855461 := bbase (se 4 (by rfl) ⟨80199, by rfl⟩ : syracuseStep 855461 = 160399) (by norm_num)
theorem B757205 : Blo 334751 757205 := bbase (se 7 (by rfl) ⟨8873, by rfl⟩ : syracuseStep 757205 = 17747) (by norm_num)
theorem B757277 : Blo 334751 757277 := bbase (se 3 (by rfl) ⟨141989, by rfl⟩ : syracuseStep 757277 = 283979) (by norm_num)
theorem B757349 : Blo 334751 757349 := bbase (se 4 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 757349 = 142003) (by norm_num)
theorem B757421 : Blo 334751 757421 := bbase (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) (by norm_num)
theorem B757493 : Blo 334751 757493 := bbase (se 5 (by rfl) ⟨35507, by rfl⟩ : syracuseStep 757493 = 71015) (by norm_num)
theorem B855805 : Blo 334751 855805 := bbase (se 3 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 855805 = 320927) (by norm_num)
theorem B757565 : Blo 334751 757565 := bbase (se 3 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 757565 = 284087) (by norm_num)
theorem B855917 : Blo 334751 855917 := bbase (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) (by norm_num)
theorem B757637 : Blo 334751 757637 := bbase (se 4 (by rfl) ⟨71028, by rfl⟩ : syracuseStep 757637 = 142057) (by norm_num)
theorem B1445813 : Blo 334751 1445813 := bbase (se 5 (by rfl) ⟨67772, by rfl⟩ : syracuseStep 1445813 = 135545) (by norm_num)
theorem B757709 : Blo 334751 757709 := bbase (se 3 (by rfl) ⟨142070, by rfl⟩ : syracuseStep 757709 = 284141) (by norm_num)
theorem B692173 : Blo 334751 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B757781 : Blo 334751 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B856109 : Blo 334751 856109 := bbase (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) (by norm_num)
theorem B757853 : Blo 334751 757853 := bbase (se 3 (by rfl) ⟨142097, by rfl⟩ : syracuseStep 757853 = 284195) (by norm_num)
theorem B757925 : Blo 334751 757925 := bbase (se 4 (by rfl) ⟨71055, by rfl⟩ : syracuseStep 757925 = 142111) (by norm_num)
theorem B757997 : Blo 334751 757997 := bbase (se 3 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 757997 = 284249) (by norm_num)
theorem B758069 : Blo 334751 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B758141 : Blo 334751 758141 := bbase (se 3 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 758141 = 284303) (by norm_num)
theorem B856453 : Blo 334751 856453 := bbase (se 4 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 856453 = 160585) (by norm_num)
theorem B2298293 : Blo 334751 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B758213 : Blo 334751 758213 := bbase (se 4 (by rfl) ⟨71082, by rfl⟩ : syracuseStep 758213 = 142165) (by norm_num)
theorem B856565 : Blo 334751 856565 := bbase (se 5 (by rfl) ⟨40151, by rfl⟩ : syracuseStep 856565 = 80303) (by norm_num)
theorem B758285 : Blo 334751 758285 := bbase (se 3 (by rfl) ⟨142178, by rfl⟩ : syracuseStep 758285 = 284357) (by norm_num)
theorem B1708613 : Blo 334751 1708613 := bbase (se 4 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 1708613 = 320365) (by norm_num)
theorem B7246421 : Blo 334751 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B758357 : Blo 334751 758357 := bbase (se 8 (by rfl) ⟨4443, by rfl⟩ : syracuseStep 758357 = 8887) (by norm_num)
theorem B1282661 : Blo 334751 1282661 := bbase (se 4 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 1282661 = 240499) (by norm_num)
theorem B758429 : Blo 334751 758429 := bbase (se 3 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 758429 = 284411) (by norm_num)
theorem B1151653 : Blo 334751 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B856757 : Blo 334751 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B758501 : Blo 334751 758501 := bbase (se 4 (by rfl) ⟨71109, by rfl⟩ : syracuseStep 758501 = 142219) (by norm_num)
theorem B758573 : Blo 334751 758573 := bbase (se 3 (by rfl) ⟨142232, by rfl⟩ : syracuseStep 758573 = 284465) (by norm_num)
theorem B1610549 : Blo 334751 1610549 := bbase (se 5 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 1610549 = 150989) (by norm_num)
theorem B955253 : Blo 334751 955253 := bbase (se 5 (by rfl) ⟨44777, by rfl⟩ : syracuseStep 955253 = 89555) (by norm_num)
theorem B758645 : Blo 334751 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B1282949 : Blo 334751 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B758717 : Blo 334751 758717 := bbase (se 3 (by rfl) ⟨142259, by rfl⟩ : syracuseStep 758717 = 284519) (by norm_num)
theorem B1020869 : Blo 334751 1020869 := bbase (se 4 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 1020869 = 191413) (by norm_num)
theorem B758789 : Blo 334751 758789 := bbase (se 4 (by rfl) ⟨71136, by rfl⟩ : syracuseStep 758789 = 142273) (by norm_num)
theorem B857101 : Blo 334751 857101 := bbase (se 3 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 857101 = 321413) (by norm_num)
theorem B758861 : Blo 334751 758861 := bbase (se 3 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 758861 = 284573) (by norm_num)
theorem B857213 : Blo 334751 857213 := bbase (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) (by norm_num)
theorem B758933 : Blo 334751 758933 := bbase (se 6 (by rfl) ⟨17787, by rfl⟩ : syracuseStep 758933 = 35575) (by norm_num)
theorem B759005 : Blo 334751 759005 := bbase (se 3 (by rfl) ⟨142313, by rfl⟩ : syracuseStep 759005 = 284627) (by norm_num)
theorem B759077 : Blo 334751 759077 := bbase (se 4 (by rfl) ⟨71163, by rfl⟩ : syracuseStep 759077 = 142327) (by norm_num)
theorem B857405 : Blo 334751 857405 := bbase (se 3 (by rfl) ⟨160763, by rfl⟩ : syracuseStep 857405 = 321527) (by norm_num)
theorem B759149 : Blo 334751 759149 := bbase (se 3 (by rfl) ⟨142340, by rfl⟩ : syracuseStep 759149 = 284681) (by norm_num)
theorem B759221 : Blo 334751 759221 := bbase (se 5 (by rfl) ⟨35588, by rfl⟩ : syracuseStep 759221 = 71177) (by norm_num)
theorem B2168309 : Blo 334751 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B759293 : Blo 334751 759293 := bbase (se 3 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 759293 = 284735) (by norm_num)
theorem B955925 : Blo 334751 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B2889269 : Blo 334751 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B759365 : Blo 334751 759365 := bbase (se 4 (by rfl) ⟨71190, by rfl⟩ : syracuseStep 759365 = 142381) (by norm_num)
theorem B1218149 : Blo 334751 1218149 := bbase (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) (by norm_num)
theorem B759437 : Blo 334751 759437 := bbase (se 3 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 759437 = 284789) (by norm_num)
theorem B759509 : Blo 334751 759509 := bbase (se 7 (by rfl) ⟨8900, by rfl⟩ : syracuseStep 759509 = 17801) (by norm_num)
theorem B759581 : Blo 334751 759581 := bbase (se 3 (by rfl) ⟨142421, by rfl⟩ : syracuseStep 759581 = 284843) (by norm_num)
theorem B1906517 : Blo 334751 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B1709909 : Blo 334751 1709909 := bbase (se 9 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 1709909 = 10019) (by norm_num)
theorem B759653 : Blo 334751 759653 := bbase (se 4 (by rfl) ⟨71217, by rfl⟩ : syracuseStep 759653 = 142435) (by norm_num)
theorem B2463605 : Blo 334751 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B759725 : Blo 334751 759725 := bbase (se 3 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 759725 = 284897) (by norm_num)
theorem B1611701 : Blo 334751 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B956357 : Blo 334751 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B759797 : Blo 334751 759797 := bbase (se 5 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 759797 = 71231) (by norm_num)
theorem B1284133 : Blo 334751 1284133 := bbase (se 4 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 1284133 = 240775) (by norm_num)
theorem B759869 : Blo 334751 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B759941 : Blo 334751 759941 := bbase (se 4 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 759941 = 142489) (by norm_num)
theorem B1218725 : Blo 334751 1218725 := bbase (se 4 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 1218725 = 228511) (by norm_num)
theorem B760013 : Blo 334751 760013 := bbase (se 3 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 760013 = 285005) (by norm_num)
theorem B760085 : Blo 334751 760085 := bbase (se 6 (by rfl) ⟨17814, by rfl⟩ : syracuseStep 760085 = 35629) (by norm_num)
theorem B1284437 : Blo 334751 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B760157 : Blo 334751 760157 := bbase (se 3 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 760157 = 285059) (by norm_num)
theorem B760229 : Blo 334751 760229 := bbase (se 4 (by rfl) ⟨71271, by rfl⟩ : syracuseStep 760229 = 142543) (by norm_num)
theorem B760301 : Blo 334751 760301 := bbase (se 3 (by rfl) ⟨142556, by rfl⟩ : syracuseStep 760301 = 285113) (by norm_num)
theorem B760373 : Blo 334751 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B2562677 : Blo 334751 2562677 := bbase (se 5 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 2562677 = 240251) (by norm_num)
theorem B760445 : Blo 334751 760445 := bbase (se 3 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 760445 = 285167) (by norm_num)
theorem B1612469 : Blo 334751 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B957109 : Blo 334751 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B760517 : Blo 334751 760517 := bbase (se 4 (by rfl) ⟨71298, by rfl⟩ : syracuseStep 760517 = 142597) (by norm_num)
theorem B760589 : Blo 334751 760589 := bbase (se 3 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 760589 = 285221) (by norm_num)
theorem B760661 : Blo 334751 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B760733 : Blo 334751 760733 := bbase (se 3 (by rfl) ⟨142637, by rfl⟩ : syracuseStep 760733 = 285275) (by norm_num)
theorem B760805 : Blo 334751 760805 := bbase (se 4 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 760805 = 142651) (by norm_num)
theorem B760877 : Blo 334751 760877 := bbase (se 3 (by rfl) ⟨142664, by rfl⟩ : syracuseStep 760877 = 285329) (by norm_num)
theorem B1711205 : Blo 334751 1711205 := bbase (se 4 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 1711205 = 320851) (by norm_num)
theorem B760949 : Blo 334751 760949 := bbase (se 5 (by rfl) ⟨35669, by rfl⟩ : syracuseStep 760949 = 71339) (by norm_num)
theorem B1154213 : Blo 334751 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B761021 : Blo 334751 761021 := bbase (se 3 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 761021 = 285383) (by norm_num)
theorem B1252565 : Blo 334751 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B761093 : Blo 334751 761093 := bbase (se 4 (by rfl) ⟨71352, by rfl⟩ : syracuseStep 761093 = 142705) (by norm_num)
theorem B761165 : Blo 334751 761165 := bbase (se 3 (by rfl) ⟨142718, by rfl⟩ : syracuseStep 761165 = 285437) (by norm_num)
theorem B761237 : Blo 334751 761237 := bbase (se 6 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 761237 = 35683) (by norm_num)
theorem B761309 : Blo 334751 761309 := bbase (se 3 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 761309 = 285491) (by norm_num)
theorem B761381 : Blo 334751 761381 := bbase (se 4 (by rfl) ⟨71379, by rfl⟩ : syracuseStep 761381 = 142759) (by norm_num)
theorem B433721 : Blo 334751 433721 := bbase (se 2 (by rfl) ⟨162645, by rfl⟩ : syracuseStep 433721 = 325291) (by norm_num)
theorem B761453 : Blo 334751 761453 := bbase (se 3 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 761453 = 285545) (by norm_num)
theorem B761525 : Blo 334751 761525 := bbase (se 5 (by rfl) ⟨35696, by rfl⟩ : syracuseStep 761525 = 71393) (by norm_num)
theorem B335549 : Blo 334751 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B564941 : Blo 334751 564941 := bbase (se 3 (by rfl) ⟨105926, by rfl⟩ : syracuseStep 564941 = 211853) (by norm_num)
theorem B1220309 : Blo 334751 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B761597 : Blo 334751 761597 := bbase (se 3 (by rfl) ⟨142799, by rfl⟩ : syracuseStep 761597 = 285599) (by norm_num)
theorem B1154837 : Blo 334751 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B761669 : Blo 334751 761669 := bbase (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) (by norm_num)
theorem B565069 : Blo 334751 565069 := bbase (se 3 (by rfl) ⟨105950, by rfl⟩ : syracuseStep 565069 = 211901) (by norm_num)
theorem B761741 : Blo 334751 761741 := bbase (se 3 (by rfl) ⟨142826, by rfl⟩ : syracuseStep 761741 = 285653) (by norm_num)
theorem B565157 : Blo 334751 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B761813 : Blo 334751 761813 := bbase (se 7 (by rfl) ⟨8927, by rfl⟩ : syracuseStep 761813 = 17855) (by norm_num)
theorem B1220597 : Blo 334751 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B761885 : Blo 334751 761885 := bbase (se 3 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 761885 = 285707) (by norm_num)
theorem B565285 : Blo 334751 565285 := bbase (se 4 (by rfl) ⟨52995, by rfl⟩ : syracuseStep 565285 = 105991) (by norm_num)
theorem B7610453 : Blo 334751 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B761957 : Blo 334751 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B565373 : Blo 334751 565373 := bbase (se 3 (by rfl) ⟨106007, by rfl⟩ : syracuseStep 565373 = 212015) (by norm_num)
theorem B762029 : Blo 334751 762029 := bbase (se 3 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 762029 = 285761) (by norm_num)
theorem B2728181 : Blo 334751 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B762101 : Blo 334751 762101 := bbase (se 5 (by rfl) ⟨35723, by rfl⟩ : syracuseStep 762101 = 71447) (by norm_num)
theorem B565501 : Blo 334751 565501 := bbase (se 3 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 565501 = 212063) (by norm_num)
theorem B762173 : Blo 334751 762173 := bbase (se 3 (by rfl) ⟨142907, by rfl⟩ : syracuseStep 762173 = 285815) (by norm_num)
theorem B565589 : Blo 334751 565589 := bbase (se 10 (by rfl) ⟨828, by rfl⟩ : syracuseStep 565589 = 1657) (by norm_num)
theorem B1712501 : Blo 334751 1712501 := bbase (se 5 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 1712501 = 160547) (by norm_num)
theorem B565717 : Blo 334751 565717 := bbase (se 7 (by rfl) ⟨6629, by rfl⟩ : syracuseStep 565717 = 13259) (by norm_num)
theorem B5743061 : Blo 334751 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B565805 : Blo 334751 565805 := bbase (se 3 (by rfl) ⟨106088, by rfl⟩ : syracuseStep 565805 = 212177) (by norm_num)
theorem B565933 : Blo 334751 565933 := bbase (se 3 (by rfl) ⟨106112, by rfl⟩ : syracuseStep 565933 = 212225) (by norm_num)
theorem B566021 : Blo 334751 566021 := bbase (se 4 (by rfl) ⟨53064, by rfl⟩ : syracuseStep 566021 = 106129) (by norm_num)
theorem B566149 : Blo 334751 566149 := bbase (se 4 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 566149 = 106153) (by norm_num)
theorem B402349 : Blo 334751 402349 := bbase (se 3 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 402349 = 150881) (by norm_num)
theorem B566237 : Blo 334751 566237 := bbase (se 3 (by rfl) ⟨106169, by rfl⟩ : syracuseStep 566237 = 212339) (by norm_num)
theorem B566365 : Blo 334751 566365 := bbase (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) (by norm_num)
theorem B402613 : Blo 334751 402613 := bbase (se 5 (by rfl) ⟨18872, by rfl⟩ : syracuseStep 402613 = 37745) (by norm_num)
theorem B566453 : Blo 334751 566453 := bbase (se 5 (by rfl) ⟨26552, by rfl⟩ : syracuseStep 566453 = 53105) (by norm_num)
theorem B828613 : Blo 334751 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B402733 : Blo 334751 402733 := bbase (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) (by norm_num)
theorem B566581 : Blo 334751 566581 := bbase (se 5 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 566581 = 53117) (by norm_num)
theorem B566669 : Blo 334751 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B959957 : Blo 334751 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B566797 : Blo 334751 566797 := bbase (se 3 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 566797 = 212549) (by norm_num)
theorem B566885 : Blo 334751 566885 := bbase (se 4 (by rfl) ⟨53145, by rfl⟩ : syracuseStep 566885 = 106291) (by norm_num)
theorem B1713797 : Blo 334751 1713797 := bbase (se 4 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 1713797 = 321337) (by norm_num)
theorem B567013 : Blo 334751 567013 := bbase (se 4 (by rfl) ⟨53157, by rfl⟩ : syracuseStep 567013 = 106315) (by norm_num)
theorem B567101 : Blo 334751 567101 := bbase (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) (by norm_num)
theorem B567229 : Blo 334751 567229 := bbase (se 3 (by rfl) ⟨106355, by rfl⟩ : syracuseStep 567229 = 212711) (by norm_num)
theorem B567317 : Blo 334751 567317 := bbase (se 6 (by rfl) ⟨13296, by rfl⟩ : syracuseStep 567317 = 26593) (by norm_num)
theorem B403589 : Blo 334751 403589 := bbase (se 4 (by rfl) ⟨37836, by rfl⟩ : syracuseStep 403589 = 75673) (by norm_num)
theorem B567445 : Blo 334751 567445 := bbase (se 6 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 567445 = 26599) (by norm_num)
theorem B8726741 : Blo 334751 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B567533 : Blo 334751 567533 := bbase (se 3 (by rfl) ⟨106412, by rfl⟩ : syracuseStep 567533 = 212825) (by norm_num)
theorem B567661 : Blo 334751 567661 := bbase (se 3 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 567661 = 212873) (by norm_num)
theorem B502133 : Blo 334751 502133 := bbase (se 5 (by rfl) ⟨23537, by rfl⟩ : syracuseStep 502133 = 47075) (by norm_num)
theorem B3058037 : Blo 334751 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B502157 : Blo 334751 502157 := bbase (se 3 (by rfl) ⟨94154, by rfl⟩ : syracuseStep 502157 = 188309) (by norm_num)
theorem B502181 : Blo 334751 502181 := bbase (se 4 (by rfl) ⟨47079, by rfl⟩ : syracuseStep 502181 = 94159) (by norm_num)
theorem B502205 : Blo 334751 502205 := bbase (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) (by norm_num)
theorem B567749 : Blo 334751 567749 := bbase (se 4 (by rfl) ⟨53226, by rfl⟩ : syracuseStep 567749 = 106453) (by norm_num)
theorem B502229 : Blo 334751 502229 := bbase (se 7 (by rfl) ⟨5885, by rfl⟩ : syracuseStep 502229 = 11771) (by norm_num)
theorem B502253 : Blo 334751 502253 := bbase (se 3 (by rfl) ⟨94172, by rfl⟩ : syracuseStep 502253 = 188345) (by norm_num)
theorem B502277 : Blo 334751 502277 := bbase (se 4 (by rfl) ⟨47088, by rfl⟩ : syracuseStep 502277 = 94177) (by norm_num)
theorem B502301 : Blo 334751 502301 := bbase (se 3 (by rfl) ⟨94181, by rfl⟩ : syracuseStep 502301 = 188363) (by norm_num)
theorem B502325 : Blo 334751 502325 := bbase (se 5 (by rfl) ⟨23546, by rfl⟩ : syracuseStep 502325 = 47093) (by norm_num)
theorem B567877 : Blo 334751 567877 := bbase (se 4 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 567877 = 106477) (by norm_num)
theorem B502349 : Blo 334751 502349 := bbase (se 3 (by rfl) ⟨94190, by rfl⟩ : syracuseStep 502349 = 188381) (by norm_num)
theorem B502373 : Blo 334751 502373 := bbase (se 4 (by rfl) ⟨47097, by rfl⟩ : syracuseStep 502373 = 94195) (by norm_num)
theorem B961141 : Blo 334751 961141 := bbase (se 5 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 961141 = 90107) (by norm_num)
theorem B502397 : Blo 334751 502397 := bbase (se 3 (by rfl) ⟨94199, by rfl⟩ : syracuseStep 502397 = 188399) (by norm_num)
theorem B502421 : Blo 334751 502421 := bbase (se 6 (by rfl) ⟨11775, by rfl⟩ : syracuseStep 502421 = 23551) (by norm_num)
theorem B567965 : Blo 334751 567965 := bbase (se 3 (by rfl) ⟨106493, by rfl⟩ : syracuseStep 567965 = 212987) (by norm_num)
theorem B502445 : Blo 334751 502445 := bbase (se 3 (by rfl) ⟨94208, by rfl⟩ : syracuseStep 502445 = 188417) (by norm_num)
theorem B1452725 : Blo 334751 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B502469 : Blo 334751 502469 := bbase (se 4 (by rfl) ⟨47106, by rfl⟩ : syracuseStep 502469 = 94213) (by norm_num)
theorem B2730709 : Blo 334751 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B502493 : Blo 334751 502493 := bbase (se 3 (by rfl) ⟨94217, by rfl⟩ : syracuseStep 502493 = 188435) (by norm_num)
theorem B502517 : Blo 334751 502517 := bbase (se 5 (by rfl) ⟨23555, by rfl⟩ : syracuseStep 502517 = 47111) (by norm_num)
theorem B502541 : Blo 334751 502541 := bbase (se 3 (by rfl) ⟨94226, by rfl⟩ : syracuseStep 502541 = 188453) (by norm_num)
theorem B961301 : Blo 334751 961301 := bbase (se 6 (by rfl) ⟨22530, by rfl⟩ : syracuseStep 961301 = 45061) (by norm_num)
theorem B568093 : Blo 334751 568093 := bbase (se 3 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 568093 = 213035) (by norm_num)
theorem B502565 : Blo 334751 502565 := bbase (se 4 (by rfl) ⟨47115, by rfl⟩ : syracuseStep 502565 = 94231) (by norm_num)
theorem B502589 : Blo 334751 502589 := bbase (se 3 (by rfl) ⟨94235, by rfl⟩ : syracuseStep 502589 = 188471) (by norm_num)
theorem B502613 : Blo 334751 502613 := bbase (se 9 (by rfl) ⟨1472, by rfl⟩ : syracuseStep 502613 = 2945) (by norm_num)
theorem B404309 : Blo 334751 404309 := bbase (se 9 (by rfl) ⟨1184, by rfl⟩ : syracuseStep 404309 = 2369) (by norm_num)
theorem B502637 : Blo 334751 502637 := bbase (se 3 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 502637 = 188489) (by norm_num)
theorem B568181 : Blo 334751 568181 := bbase (se 5 (by rfl) ⟨26633, by rfl⟩ : syracuseStep 568181 = 53267) (by norm_num)
theorem B502661 : Blo 334751 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B502685 : Blo 334751 502685 := bbase (se 3 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 502685 = 188507) (by norm_num)
theorem B502709 : Blo 334751 502709 := bbase (se 5 (by rfl) ⟨23564, by rfl⟩ : syracuseStep 502709 = 47129) (by norm_num)
theorem B502733 : Blo 334751 502733 := bbase (se 3 (by rfl) ⟨94262, by rfl⟩ : syracuseStep 502733 = 188525) (by norm_num)
theorem B502757 : Blo 334751 502757 := bbase (se 4 (by rfl) ⟨47133, by rfl⟩ : syracuseStep 502757 = 94267) (by norm_num)
theorem B568309 : Blo 334751 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B502781 : Blo 334751 502781 := bbase (se 3 (by rfl) ⟨94271, by rfl⟩ : syracuseStep 502781 = 188543) (by norm_num)
theorem B961541 : Blo 334751 961541 := bbase (se 4 (by rfl) ⟨90144, by rfl⟩ : syracuseStep 961541 = 180289) (by norm_num)
theorem B502805 : Blo 334751 502805 := bbase (se 6 (by rfl) ⟨11784, by rfl⟩ : syracuseStep 502805 = 23569) (by norm_num)
theorem B502829 : Blo 334751 502829 := bbase (se 3 (by rfl) ⟨94280, by rfl⟩ : syracuseStep 502829 = 188561) (by norm_num)
theorem B3255349 : Blo 334751 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B502853 : Blo 334751 502853 := bbase (se 4 (by rfl) ⟨47142, by rfl⟩ : syracuseStep 502853 = 94285) (by norm_num)
theorem B568397 : Blo 334751 568397 := bbase (se 3 (by rfl) ⟨106574, by rfl⟩ : syracuseStep 568397 = 213149) (by norm_num)
theorem B502877 : Blo 334751 502877 := bbase (se 3 (by rfl) ⟨94289, by rfl⟩ : syracuseStep 502877 = 188579) (by norm_num)
theorem B502901 : Blo 334751 502901 := bbase (se 5 (by rfl) ⟨23573, by rfl⟩ : syracuseStep 502901 = 47147) (by norm_num)
theorem B404617 : Blo 334751 404617 := bbase (se 2 (by rfl) ⟨151731, by rfl⟩ : syracuseStep 404617 = 303463) (by norm_num)
theorem B502925 : Blo 334751 502925 := bbase (se 3 (by rfl) ⟨94298, by rfl⟩ : syracuseStep 502925 = 188597) (by norm_num)
theorem B502949 : Blo 334751 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B502973 : Blo 334751 502973 := bbase (se 3 (by rfl) ⟨94307, by rfl⟩ : syracuseStep 502973 = 188615) (by norm_num)
theorem B961733 : Blo 334751 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B568525 : Blo 334751 568525 := bbase (se 3 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 568525 = 213197) (by norm_num)
theorem B502997 : Blo 334751 502997 := bbase (se 7 (by rfl) ⟨5894, by rfl⟩ : syracuseStep 502997 = 11789) (by norm_num)
theorem B404713 : Blo 334751 404713 := bbase (se 2 (by rfl) ⟨151767, by rfl⟩ : syracuseStep 404713 = 303535) (by norm_num)
theorem B503021 : Blo 334751 503021 := bbase (se 3 (by rfl) ⟨94316, by rfl⟩ : syracuseStep 503021 = 188633) (by norm_num)
theorem B503045 : Blo 334751 503045 := bbase (se 4 (by rfl) ⟨47160, by rfl⟩ : syracuseStep 503045 = 94321) (by norm_num)
theorem B503069 : Blo 334751 503069 := bbase (se 3 (by rfl) ⟨94325, by rfl⟩ : syracuseStep 503069 = 188651) (by norm_num)
theorem B568613 : Blo 334751 568613 := bbase (se 4 (by rfl) ⟨53307, by rfl⟩ : syracuseStep 568613 = 106615) (by norm_num)
theorem B503093 : Blo 334751 503093 := bbase (se 5 (by rfl) ⟨23582, by rfl⟩ : syracuseStep 503093 = 47165) (by norm_num)
theorem B503117 : Blo 334751 503117 := bbase (se 3 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 503117 = 188669) (by norm_num)
theorem B503141 : Blo 334751 503141 := bbase (se 4 (by rfl) ⟨47169, by rfl⟩ : syracuseStep 503141 = 94339) (by norm_num)
theorem B404857 : Blo 334751 404857 := bbase (se 2 (by rfl) ⟨151821, by rfl⟩ : syracuseStep 404857 = 303643) (by norm_num)
theorem B503165 : Blo 334751 503165 := bbase (se 3 (by rfl) ⟨94343, by rfl⟩ : syracuseStep 503165 = 188687) (by norm_num)
theorem B503189 : Blo 334751 503189 := bbase (se 6 (by rfl) ⟨11793, by rfl⟩ : syracuseStep 503189 = 23587) (by norm_num)
theorem B568741 : Blo 334751 568741 := bbase (se 4 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 568741 = 106639) (by norm_num)
theorem B503213 : Blo 334751 503213 := bbase (se 3 (by rfl) ⟨94352, by rfl⟩ : syracuseStep 503213 = 188705) (by norm_num)
theorem B339385 : Blo 334751 339385 := bbase (se 2 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 339385 = 254539) (by norm_num)
theorem B503237 : Blo 334751 503237 := bbase (se 4 (by rfl) ⟨47178, by rfl⟩ : syracuseStep 503237 = 94357) (by norm_num)
theorem B339401 : Blo 334751 339401 := bbase (se 2 (by rfl) ⟨127275, by rfl⟩ : syracuseStep 339401 = 254551) (by norm_num)
theorem B503261 : Blo 334751 503261 := bbase (se 3 (by rfl) ⟨94361, by rfl⟩ : syracuseStep 503261 = 188723) (by norm_num)
theorem B503285 : Blo 334751 503285 := bbase (se 5 (by rfl) ⟨23591, by rfl⟩ : syracuseStep 503285 = 47183) (by norm_num)
theorem B568829 : Blo 334751 568829 := bbase (se 3 (by rfl) ⟨106655, by rfl⟩ : syracuseStep 568829 = 213311) (by norm_num)
theorem B503309 : Blo 334751 503309 := bbase (se 3 (by rfl) ⟨94370, by rfl⟩ : syracuseStep 503309 = 188741) (by norm_num)
theorem B503333 : Blo 334751 503333 := bbase (se 4 (by rfl) ⟨47187, by rfl⟩ : syracuseStep 503333 = 94375) (by norm_num)
theorem B503357 : Blo 334751 503357 := bbase (se 3 (by rfl) ⟨94379, by rfl⟩ : syracuseStep 503357 = 188759) (by norm_num)
theorem B503381 : Blo 334751 503381 := bbase (se 8 (by rfl) ⟨2949, by rfl⟩ : syracuseStep 503381 = 5899) (by norm_num)
theorem B503405 : Blo 334751 503405 := bbase (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) (by norm_num)
theorem B568957 : Blo 334751 568957 := bbase (se 3 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 568957 = 213359) (by norm_num)
theorem B503429 : Blo 334751 503429 := bbase (se 4 (by rfl) ⟨47196, by rfl⟩ : syracuseStep 503429 = 94393) (by norm_num)
theorem B503453 : Blo 334751 503453 := bbase (se 3 (by rfl) ⟨94397, by rfl⟩ : syracuseStep 503453 = 188795) (by norm_num)
theorem B503477 : Blo 334751 503477 := bbase (se 5 (by rfl) ⟨23600, by rfl⟩ : syracuseStep 503477 = 47201) (by norm_num)
theorem B503501 : Blo 334751 503501 := bbase (se 3 (by rfl) ⟨94406, by rfl⟩ : syracuseStep 503501 = 188813) (by norm_num)
theorem B569045 : Blo 334751 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B503525 : Blo 334751 503525 := bbase (se 4 (by rfl) ⟨47205, by rfl⟩ : syracuseStep 503525 = 94411) (by norm_num)
theorem B765677 : Blo 334751 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B503549 : Blo 334751 503549 := bbase (se 3 (by rfl) ⟨94415, by rfl⟩ : syracuseStep 503549 = 188831) (by norm_num)
theorem B503573 : Blo 334751 503573 := bbase (se 6 (by rfl) ⟨11802, by rfl⟩ : syracuseStep 503573 = 23605) (by norm_num)
theorem B536357 : Blo 334751 536357 := bbase (se 4 (by rfl) ⟨50283, by rfl⟩ : syracuseStep 536357 = 100567) (by norm_num)
theorem B503597 : Blo 334751 503597 := bbase (se 3 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 503597 = 188849) (by norm_num)
theorem B2043701 : Blo 334751 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B503621 : Blo 334751 503621 := bbase (se 4 (by rfl) ⟨47214, by rfl⟩ : syracuseStep 503621 = 94429) (by norm_num)
theorem B569173 : Blo 334751 569173 := bbase (se 9 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 569173 = 3335) (by norm_num)
theorem B503645 : Blo 334751 503645 := bbase (se 3 (by rfl) ⟨94433, by rfl⟩ : syracuseStep 503645 = 188867) (by norm_num)
theorem B503669 : Blo 334751 503669 := bbase (se 5 (by rfl) ⟨23609, by rfl⟩ : syracuseStep 503669 = 47219) (by norm_num)
theorem B503693 : Blo 334751 503693 := bbase (se 3 (by rfl) ⟨94442, by rfl⟩ : syracuseStep 503693 = 188885) (by norm_num)
theorem B503717 : Blo 334751 503717 := bbase (se 4 (by rfl) ⟨47223, by rfl⟩ : syracuseStep 503717 = 94447) (by norm_num)
theorem B569261 : Blo 334751 569261 := bbase (se 3 (by rfl) ⟨106736, by rfl⟩ : syracuseStep 569261 = 213473) (by norm_num)
theorem B503741 : Blo 334751 503741 := bbase (se 3 (by rfl) ⟨94451, by rfl⟩ : syracuseStep 503741 = 188903) (by norm_num)
theorem B503765 : Blo 334751 503765 := bbase (se 7 (by rfl) ⟨5903, by rfl⟩ : syracuseStep 503765 = 11807) (by norm_num)
theorem B503789 : Blo 334751 503789 := bbase (se 3 (by rfl) ⟨94460, by rfl⟩ : syracuseStep 503789 = 188921) (by norm_num)
theorem B503813 : Blo 334751 503813 := bbase (se 4 (by rfl) ⟨47232, by rfl⟩ : syracuseStep 503813 = 94465) (by norm_num)
theorem B339985 : Blo 334751 339985 := bbase (se 2 (by rfl) ⟨127494, by rfl⟩ : syracuseStep 339985 = 254989) (by norm_num)
theorem B503837 : Blo 334751 503837 := bbase (se 3 (by rfl) ⟨94469, by rfl⟩ : syracuseStep 503837 = 188939) (by norm_num)
theorem B569389 : Blo 334751 569389 := bbase (se 3 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 569389 = 213521) (by norm_num)
theorem B503861 : Blo 334751 503861 := bbase (se 5 (by rfl) ⟨23618, by rfl⟩ : syracuseStep 503861 = 47237) (by norm_num)
theorem B503885 : Blo 334751 503885 := bbase (se 3 (by rfl) ⟨94478, by rfl⟩ : syracuseStep 503885 = 188957) (by norm_num)
theorem B503909 : Blo 334751 503909 := bbase (se 4 (by rfl) ⟨47241, by rfl⟩ : syracuseStep 503909 = 94483) (by norm_num)
theorem B503933 : Blo 334751 503933 := bbase (se 3 (by rfl) ⟨94487, by rfl⟩ : syracuseStep 503933 = 188975) (by norm_num)
theorem B569477 : Blo 334751 569477 := bbase (se 4 (by rfl) ⟨53388, by rfl⟩ : syracuseStep 569477 = 106777) (by norm_num)
theorem B503957 : Blo 334751 503957 := bbase (se 6 (by rfl) ⟨11811, by rfl⟩ : syracuseStep 503957 = 23623) (by norm_num)
theorem B962725 : Blo 334751 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B503981 : Blo 334751 503981 := bbase (se 3 (by rfl) ⟨94496, by rfl⟩ : syracuseStep 503981 = 188993) (by norm_num)
theorem B504005 : Blo 334751 504005 := bbase (se 4 (by rfl) ⟨47250, by rfl⟩ : syracuseStep 504005 = 94501) (by norm_num)
theorem B504029 : Blo 334751 504029 := bbase (se 3 (by rfl) ⟨94505, by rfl⟩ : syracuseStep 504029 = 189011) (by norm_num)
theorem B504053 : Blo 334751 504053 := bbase (se 5 (by rfl) ⟨23627, by rfl⟩ : syracuseStep 504053 = 47255) (by norm_num)
theorem B569605 : Blo 334751 569605 := bbase (se 4 (by rfl) ⟨53400, by rfl⟩ : syracuseStep 569605 = 106801) (by norm_num)
theorem B504077 : Blo 334751 504077 := bbase (se 3 (by rfl) ⟨94514, by rfl⟩ : syracuseStep 504077 = 189029) (by norm_num)
theorem B504101 : Blo 334751 504101 := bbase (se 4 (by rfl) ⟨47259, by rfl⟩ : syracuseStep 504101 = 94519) (by norm_num)
theorem B504125 : Blo 334751 504125 := bbase (se 3 (by rfl) ⟨94523, by rfl⟩ : syracuseStep 504125 = 189047) (by norm_num)
theorem B504149 : Blo 334751 504149 := bbase (se 10 (by rfl) ⟨738, by rfl⟩ : syracuseStep 504149 = 1477) (by norm_num)
theorem B569693 : Blo 334751 569693 := bbase (se 3 (by rfl) ⟨106817, by rfl⟩ : syracuseStep 569693 = 213635) (by norm_num)
theorem B405857 : Blo 334751 405857 := bbase (se 2 (by rfl) ⟨152196, by rfl⟩ : syracuseStep 405857 = 304393) (by norm_num)
theorem B504173 : Blo 334751 504173 := bbase (se 3 (by rfl) ⟨94532, by rfl⟩ : syracuseStep 504173 = 189065) (by norm_num)
theorem B504197 : Blo 334751 504197 := bbase (se 4 (by rfl) ⟨47268, by rfl⟩ : syracuseStep 504197 = 94537) (by norm_num)
theorem B504221 : Blo 334751 504221 := bbase (se 3 (by rfl) ⟨94541, by rfl⟩ : syracuseStep 504221 = 189083) (by norm_num)
theorem B504245 : Blo 334751 504245 := bbase (se 5 (by rfl) ⟨23636, by rfl⟩ : syracuseStep 504245 = 47273) (by norm_num)
theorem B504269 : Blo 334751 504269 := bbase (se 3 (by rfl) ⟨94550, by rfl⟩ : syracuseStep 504269 = 189101) (by norm_num)
theorem B569821 : Blo 334751 569821 := bbase (se 3 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 569821 = 213683) (by norm_num)
theorem B504293 : Blo 334751 504293 := bbase (se 4 (by rfl) ⟨47277, by rfl⟩ : syracuseStep 504293 = 94555) (by norm_num)
theorem B504317 : Blo 334751 504317 := bbase (se 3 (by rfl) ⟨94559, by rfl⟩ : syracuseStep 504317 = 189119) (by norm_num)
theorem B504341 : Blo 334751 504341 := bbase (se 6 (by rfl) ⟨11820, by rfl⟩ : syracuseStep 504341 = 23641) (by norm_num)
theorem B504365 : Blo 334751 504365 := bbase (se 3 (by rfl) ⟨94568, by rfl⟩ : syracuseStep 504365 = 189137) (by norm_num)
theorem B569909 : Blo 334751 569909 := bbase (se 5 (by rfl) ⟨26714, by rfl⟩ : syracuseStep 569909 = 53429) (by norm_num)
theorem B504389 : Blo 334751 504389 := bbase (se 4 (by rfl) ⟨47286, by rfl⟩ : syracuseStep 504389 = 94573) (by norm_num)
theorem B340561 : Blo 334751 340561 := bbase (se 2 (by rfl) ⟨127710, by rfl⟩ : syracuseStep 340561 = 255421) (by norm_num)
theorem B504413 : Blo 334751 504413 := bbase (se 3 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 504413 = 189155) (by norm_num)
theorem B504437 : Blo 334751 504437 := bbase (se 5 (by rfl) ⟨23645, by rfl⟩ : syracuseStep 504437 = 47291) (by norm_num)
theorem B504461 : Blo 334751 504461 := bbase (se 3 (by rfl) ⟨94586, by rfl⟩ : syracuseStep 504461 = 189173) (by norm_num)
theorem B504485 : Blo 334751 504485 := bbase (se 4 (by rfl) ⟨47295, by rfl⟩ : syracuseStep 504485 = 94591) (by norm_num)
theorem B570037 : Blo 334751 570037 := bbase (se 5 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 570037 = 53441) (by norm_num)
theorem B504509 : Blo 334751 504509 := bbase (se 3 (by rfl) ⟨94595, by rfl⟩ : syracuseStep 504509 = 189191) (by norm_num)
theorem B635597 : Blo 334751 635597 := bbase (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) (by norm_num)
theorem B504533 : Blo 334751 504533 := bbase (se 7 (by rfl) ⟨5912, by rfl⟩ : syracuseStep 504533 = 11825) (by norm_num)
theorem B504557 : Blo 334751 504557 := bbase (se 3 (by rfl) ⟨94604, by rfl⟩ : syracuseStep 504557 = 189209) (by norm_num)
theorem B537349 : Blo 334751 537349 := bbase (se 4 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 537349 = 100753) (by norm_num)
theorem B504581 : Blo 334751 504581 := bbase (se 4 (by rfl) ⟨47304, by rfl⟩ : syracuseStep 504581 = 94609) (by norm_num)
theorem B570125 : Blo 334751 570125 := bbase (se 3 (by rfl) ⟨106898, by rfl⟩ : syracuseStep 570125 = 213797) (by norm_num)
theorem B1946389 : Blo 334751 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B504605 : Blo 334751 504605 := bbase (se 3 (by rfl) ⟨94613, by rfl⟩ : syracuseStep 504605 = 189227) (by norm_num)
theorem B504629 : Blo 334751 504629 := bbase (se 5 (by rfl) ⟨23654, by rfl⟩ : syracuseStep 504629 = 47309) (by norm_num)
theorem B504653 : Blo 334751 504653 := bbase (se 3 (by rfl) ⟨94622, by rfl⟩ : syracuseStep 504653 = 189245) (by norm_num)
theorem B504677 : Blo 334751 504677 := bbase (se 4 (by rfl) ⟨47313, by rfl⟩ : syracuseStep 504677 = 94627) (by norm_num)
theorem B504701 : Blo 334751 504701 := bbase (se 3 (by rfl) ⟨94631, by rfl⟩ : syracuseStep 504701 = 189263) (by norm_num)
theorem B570253 : Blo 334751 570253 := bbase (se 3 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 570253 = 213845) (by norm_num)
theorem B504725 : Blo 334751 504725 := bbase (se 6 (by rfl) ⟨11829, by rfl⟩ : syracuseStep 504725 = 23659) (by norm_num)
theorem B504749 : Blo 334751 504749 := bbase (se 3 (by rfl) ⟨94640, by rfl⟩ : syracuseStep 504749 = 189281) (by norm_num)
theorem B504773 : Blo 334751 504773 := bbase (se 4 (by rfl) ⟨47322, by rfl⟩ : syracuseStep 504773 = 94645) (by norm_num)
theorem B504797 : Blo 334751 504797 := bbase (se 3 (by rfl) ⟨94649, by rfl⟩ : syracuseStep 504797 = 189299) (by norm_num)
theorem B570341 : Blo 334751 570341 := bbase (se 4 (by rfl) ⟨53469, by rfl⟩ : syracuseStep 570341 = 106939) (by norm_num)
theorem B504821 : Blo 334751 504821 := bbase (se 5 (by rfl) ⟨23663, by rfl⟩ : syracuseStep 504821 = 47327) (by norm_num)
theorem B504845 : Blo 334751 504845 := bbase (se 3 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 504845 = 189317) (by norm_num)
theorem B406549 : Blo 334751 406549 := bbase (se 6 (by rfl) ⟨9528, by rfl⟩ : syracuseStep 406549 = 19057) (by norm_num)
theorem B504869 : Blo 334751 504869 := bbase (se 4 (by rfl) ⟨47331, by rfl⟩ : syracuseStep 504869 = 94663) (by norm_num)
theorem B504893 : Blo 334751 504893 := bbase (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) (by norm_num)
theorem B504917 : Blo 334751 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B570469 : Blo 334751 570469 := bbase (se 4 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 570469 = 106963) (by norm_num)
theorem B504941 : Blo 334751 504941 := bbase (se 3 (by rfl) ⟨94676, by rfl⟩ : syracuseStep 504941 = 189353) (by norm_num)
theorem B504965 : Blo 334751 504965 := bbase (se 4 (by rfl) ⟨47340, by rfl⟩ : syracuseStep 504965 = 94681) (by norm_num)
theorem B504989 : Blo 334751 504989 := bbase (se 3 (by rfl) ⟨94685, by rfl⟩ : syracuseStep 504989 = 189371) (by norm_num)
theorem B505013 : Blo 334751 505013 := bbase (se 5 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 505013 = 47345) (by norm_num)
theorem B570557 : Blo 334751 570557 := bbase (se 3 (by rfl) ⟨106979, by rfl⟩ : syracuseStep 570557 = 213959) (by norm_num)
theorem B537797 : Blo 334751 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B505037 : Blo 334751 505037 := bbase (se 3 (by rfl) ⟨94694, by rfl⟩ : syracuseStep 505037 = 189389) (by norm_num)
theorem B832733 : Blo 334751 832733 := bbase (se 3 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 832733 = 312275) (by norm_num)
theorem B505061 : Blo 334751 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B406765 : Blo 334751 406765 := bbase (se 3 (by rfl) ⟨76268, by rfl⟩ : syracuseStep 406765 = 152537) (by norm_num)
theorem B341233 : Blo 334751 341233 := bbase (se 2 (by rfl) ⟨127962, by rfl⟩ : syracuseStep 341233 = 255925) (by norm_num)
theorem B963829 : Blo 334751 963829 := bbase (se 5 (by rfl) ⟨45179, by rfl⟩ : syracuseStep 963829 = 90359) (by norm_num)
theorem B505085 : Blo 334751 505085 := bbase (se 3 (by rfl) ⟨94703, by rfl⟩ : syracuseStep 505085 = 189407) (by norm_num)
theorem B505109 : Blo 334751 505109 := bbase (se 6 (by rfl) ⟨11838, by rfl⟩ : syracuseStep 505109 = 23677) (by norm_num)
theorem B505133 : Blo 334751 505133 := bbase (se 3 (by rfl) ⟨94712, by rfl⟩ : syracuseStep 505133 = 189425) (by norm_num)
theorem B570685 : Blo 334751 570685 := bbase (se 3 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 570685 = 214007) (by norm_num)
theorem B505157 : Blo 334751 505157 := bbase (se 4 (by rfl) ⟨47358, by rfl⟩ : syracuseStep 505157 = 94717) (by norm_num)
theorem B505181 : Blo 334751 505181 := bbase (se 3 (by rfl) ⟨94721, by rfl⟩ : syracuseStep 505181 = 189443) (by norm_num)
theorem B1291621 : Blo 334751 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B865637 : Blo 334751 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B505205 : Blo 334751 505205 := bbase (se 5 (by rfl) ⟨23681, by rfl⟩ : syracuseStep 505205 = 47363) (by norm_num)
theorem B537997 : Blo 334751 537997 := bbase (se 3 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 537997 = 201749) (by norm_num)
theorem B505229 : Blo 334751 505229 := bbase (se 3 (by rfl) ⟨94730, by rfl⟩ : syracuseStep 505229 = 189461) (by norm_num)
theorem B570773 : Blo 334751 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B505253 : Blo 334751 505253 := bbase (se 4 (by rfl) ⟨47367, by rfl⟩ : syracuseStep 505253 = 94735) (by norm_num)
theorem B636349 : Blo 334751 636349 := bbase (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) (by norm_num)
theorem B505277 : Blo 334751 505277 := bbase (se 3 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 505277 = 189479) (by norm_num)
theorem B505301 : Blo 334751 505301 := bbase (se 7 (by rfl) ⟨5921, by rfl⟩ : syracuseStep 505301 = 11843) (by norm_num)
theorem B505325 : Blo 334751 505325 := bbase (se 3 (by rfl) ⟨94748, by rfl⟩ : syracuseStep 505325 = 189497) (by norm_num)
theorem B505349 : Blo 334751 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B570901 : Blo 334751 570901 := bbase (se 6 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 570901 = 26761) (by norm_num)
theorem B505373 : Blo 334751 505373 := bbase (se 3 (by rfl) ⟨94757, by rfl⟩ : syracuseStep 505373 = 189515) (by norm_num)
theorem B505397 : Blo 334751 505397 := bbase (se 5 (by rfl) ⟨23690, by rfl⟩ : syracuseStep 505397 = 47381) (by norm_num)
theorem B767549 : Blo 334751 767549 := bbase (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) (by norm_num)
theorem B636493 : Blo 334751 636493 := bbase (se 3 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 636493 = 238685) (by norm_num)
theorem B505421 : Blo 334751 505421 := bbase (se 3 (by rfl) ⟨94766, by rfl⟩ : syracuseStep 505421 = 189533) (by norm_num)
theorem B505445 : Blo 334751 505445 := bbase (se 4 (by rfl) ⟨47385, by rfl⟩ : syracuseStep 505445 = 94771) (by norm_num)
theorem B570989 : Blo 334751 570989 := bbase (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) (by norm_num)
theorem B505469 : Blo 334751 505469 := bbase (se 3 (by rfl) ⟨94775, by rfl⟩ : syracuseStep 505469 = 189551) (by norm_num)
theorem B538253 : Blo 334751 538253 := bbase (se 3 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 538253 = 201845) (by norm_num)
theorem B505493 : Blo 334751 505493 := bbase (se 6 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 505493 = 23695) (by norm_num)
theorem B505517 : Blo 334751 505517 := bbase (se 3 (by rfl) ⟨94784, by rfl⟩ : syracuseStep 505517 = 189569) (by norm_num)
theorem B505541 : Blo 334751 505541 := bbase (se 4 (by rfl) ⟨47394, by rfl⟩ : syracuseStep 505541 = 94789) (by norm_num)
theorem B505565 : Blo 334751 505565 := bbase (se 3 (by rfl) ⟨94793, by rfl⟩ : syracuseStep 505565 = 189587) (by norm_num)
theorem B636653 : Blo 334751 636653 := bbase (se 3 (by rfl) ⟨119372, by rfl⟩ : syracuseStep 636653 = 238745) (by norm_num)
theorem B571117 : Blo 334751 571117 := bbase (se 3 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 571117 = 214169) (by norm_num)
theorem B505589 : Blo 334751 505589 := bbase (se 5 (by rfl) ⟨23699, by rfl⟩ : syracuseStep 505589 = 47399) (by norm_num)
theorem B341749 : Blo 334751 341749 := bbase (se 5 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 341749 = 32039) (by norm_num)
theorem B505613 : Blo 334751 505613 := bbase (se 3 (by rfl) ⟨94802, by rfl⟩ : syracuseStep 505613 = 189605) (by norm_num)
theorem B3127061 : Blo 334751 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B505637 : Blo 334751 505637 := bbase (se 4 (by rfl) ⟨47403, by rfl⟩ : syracuseStep 505637 = 94807) (by norm_num)
theorem B505661 : Blo 334751 505661 := bbase (se 3 (by rfl) ⟨94811, by rfl⟩ : syracuseStep 505661 = 189623) (by norm_num)
theorem B571205 : Blo 334751 571205 := bbase (se 4 (by rfl) ⟨53550, by rfl⟩ : syracuseStep 571205 = 107101) (by norm_num)
theorem B505685 : Blo 334751 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B505709 : Blo 334751 505709 := bbase (se 3 (by rfl) ⟨94820, by rfl⟩ : syracuseStep 505709 = 189641) (by norm_num)
theorem B636797 : Blo 334751 636797 := bbase (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) (by norm_num)
theorem B505733 : Blo 334751 505733 := bbase (se 4 (by rfl) ⟨47412, by rfl⟩ : syracuseStep 505733 = 94825) (by norm_num)
theorem B505757 : Blo 334751 505757 := bbase (se 3 (by rfl) ⟨94829, by rfl⟩ : syracuseStep 505757 = 189659) (by norm_num)
theorem B505781 : Blo 334751 505781 := bbase (se 5 (by rfl) ⟨23708, by rfl⟩ : syracuseStep 505781 = 47417) (by norm_num)
theorem B571333 : Blo 334751 571333 := bbase (se 4 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 571333 = 107125) (by norm_num)
theorem B505805 : Blo 334751 505805 := bbase (se 3 (by rfl) ⟨94838, by rfl⟩ : syracuseStep 505805 = 189677) (by norm_num)
theorem B505829 : Blo 334751 505829 := bbase (se 4 (by rfl) ⟨47421, by rfl⟩ : syracuseStep 505829 = 94843) (by norm_num)
theorem B604157 : Blo 334751 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B505853 : Blo 334751 505853 := bbase (se 3 (by rfl) ⟨94847, by rfl⟩ : syracuseStep 505853 = 189695) (by norm_num)
theorem B505877 : Blo 334751 505877 := bbase (se 6 (by rfl) ⟨11856, by rfl⟩ : syracuseStep 505877 = 23713) (by norm_num)
theorem B571421 : Blo 334751 571421 := bbase (se 3 (by rfl) ⟨107141, by rfl⟩ : syracuseStep 571421 = 214283) (by norm_num)
theorem B505901 : Blo 334751 505901 := bbase (se 3 (by rfl) ⟨94856, by rfl⟩ : syracuseStep 505901 = 189713) (by norm_num)
theorem B505925 : Blo 334751 505925 := bbase (se 4 (by rfl) ⟨47430, by rfl⟩ : syracuseStep 505925 = 94861) (by norm_num)
theorem B505949 : Blo 334751 505949 := bbase (se 3 (by rfl) ⟨94865, by rfl⟩ : syracuseStep 505949 = 189731) (by norm_num)
theorem B505973 : Blo 334751 505973 := bbase (se 5 (by rfl) ⟨23717, by rfl⟩ : syracuseStep 505973 = 47435) (by norm_num)
theorem B505997 : Blo 334751 505997 := bbase (se 3 (by rfl) ⟨94874, by rfl⟩ : syracuseStep 505997 = 189749) (by norm_num)
theorem B4307093 : Blo 334751 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B637085 : Blo 334751 637085 := bbase (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) (by norm_num)
theorem B571549 : Blo 334751 571549 := bbase (se 3 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 571549 = 214331) (by norm_num)
theorem B506021 : Blo 334751 506021 := bbase (se 4 (by rfl) ⟨47439, by rfl⟩ : syracuseStep 506021 = 94879) (by norm_num)
theorem B506045 : Blo 334751 506045 := bbase (se 3 (by rfl) ⟨94883, by rfl⟩ : syracuseStep 506045 = 189767) (by norm_num)
theorem B506069 : Blo 334751 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B2570453 : Blo 334751 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B506093 : Blo 334751 506093 := bbase (se 3 (by rfl) ⟨94892, by rfl⟩ : syracuseStep 506093 = 189785) (by norm_num)
theorem B571637 : Blo 334751 571637 := bbase (se 5 (by rfl) ⟨26795, by rfl⟩ : syracuseStep 571637 = 53591) (by norm_num)
theorem B506117 : Blo 334751 506117 := bbase (se 4 (by rfl) ⟨47448, by rfl⟩ : syracuseStep 506117 = 94897) (by norm_num)
theorem B506141 : Blo 334751 506141 := bbase (se 3 (by rfl) ⟨94901, by rfl⟩ : syracuseStep 506141 = 189803) (by norm_num)
theorem B637237 : Blo 334751 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B506165 : Blo 334751 506165 := bbase (se 5 (by rfl) ⟨23726, by rfl⟩ : syracuseStep 506165 = 47453) (by norm_num)
theorem B506189 : Blo 334751 506189 := bbase (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) (by norm_num)
theorem B506213 : Blo 334751 506213 := bbase (se 4 (by rfl) ⟨47457, by rfl⟩ : syracuseStep 506213 = 94915) (by norm_num)
theorem B1227125 : Blo 334751 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B506237 : Blo 334751 506237 := bbase (se 3 (by rfl) ⟨94919, by rfl⟩ : syracuseStep 506237 = 189839) (by norm_num)
theorem B342401 : Blo 334751 342401 := bbase (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) (by norm_num)
theorem B506261 : Blo 334751 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B506285 : Blo 334751 506285 := bbase (se 3 (by rfl) ⟨94928, by rfl⟩ : syracuseStep 506285 = 189857) (by norm_num)
theorem B506309 : Blo 334751 506309 := bbase (se 4 (by rfl) ⟨47466, by rfl⟩ : syracuseStep 506309 = 94933) (by norm_num)
theorem B5257685 : Blo 334751 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B506333 : Blo 334751 506333 := bbase (se 3 (by rfl) ⟨94937, by rfl⟩ : syracuseStep 506333 = 189875) (by norm_num)
theorem B506357 : Blo 334751 506357 := bbase (se 5 (by rfl) ⟨23735, by rfl⟩ : syracuseStep 506357 = 47471) (by norm_num)
theorem B506381 : Blo 334751 506381 := bbase (se 3 (by rfl) ⟨94946, by rfl⟩ : syracuseStep 506381 = 189893) (by norm_num)
theorem B506405 : Blo 334751 506405 := bbase (se 4 (by rfl) ⟨47475, by rfl⟩ : syracuseStep 506405 = 94951) (by norm_num)
theorem B506429 : Blo 334751 506429 := bbase (se 3 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 506429 = 189911) (by norm_num)
theorem B506453 : Blo 334751 506453 := bbase (se 8 (by rfl) ⟨2967, by rfl⟩ : syracuseStep 506453 = 5935) (by norm_num)
theorem B637541 : Blo 334751 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B506477 : Blo 334751 506477 := bbase (se 3 (by rfl) ⟨94964, by rfl⟩ : syracuseStep 506477 = 189929) (by norm_num)
theorem B506501 : Blo 334751 506501 := bbase (se 4 (by rfl) ⟨47484, by rfl⟩ : syracuseStep 506501 = 94969) (by norm_num)
theorem B506525 : Blo 334751 506525 := bbase (se 3 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 506525 = 189947) (by norm_num)
theorem B506549 : Blo 334751 506549 := bbase (se 5 (by rfl) ⟨23744, by rfl⟩ : syracuseStep 506549 = 47489) (by norm_num)
theorem B506573 : Blo 334751 506573 := bbase (se 3 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 506573 = 189965) (by norm_num)
theorem B506597 : Blo 334751 506597 := bbase (se 4 (by rfl) ⟨47493, by rfl⟩ : syracuseStep 506597 = 94987) (by norm_num)
theorem B539381 : Blo 334751 539381 := bbase (se 5 (by rfl) ⟨25283, by rfl⟩ : syracuseStep 539381 = 50567) (by norm_num)
theorem B506621 : Blo 334751 506621 := bbase (se 3 (by rfl) ⟨94991, by rfl⟩ : syracuseStep 506621 = 189983) (by norm_num)
theorem B506645 : Blo 334751 506645 := bbase (se 6 (by rfl) ⟨11874, by rfl⟩ : syracuseStep 506645 = 23749) (by norm_num)
theorem B1620773 : Blo 334751 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B506669 : Blo 334751 506669 := bbase (se 3 (by rfl) ⟨95000, by rfl⟩ : syracuseStep 506669 = 190001) (by norm_num)
theorem B506693 : Blo 334751 506693 := bbase (se 4 (by rfl) ⟨47502, by rfl⟩ : syracuseStep 506693 = 95005) (by norm_num)
theorem B506717 : Blo 334751 506717 := bbase (se 3 (by rfl) ⟨95009, by rfl⟩ : syracuseStep 506717 = 190019) (by norm_num)
theorem B1358693 : Blo 334751 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B506741 : Blo 334751 506741 := bbase (se 5 (by rfl) ⟨23753, by rfl⟩ : syracuseStep 506741 = 47507) (by norm_num)
theorem B506765 : Blo 334751 506765 := bbase (se 3 (by rfl) ⟨95018, by rfl⟩ : syracuseStep 506765 = 190037) (by norm_num)
theorem B506789 : Blo 334751 506789 := bbase (se 4 (by rfl) ⟨47511, by rfl⟩ : syracuseStep 506789 = 95023) (by norm_num)
theorem B506813 : Blo 334751 506813 := bbase (se 3 (by rfl) ⟨95027, by rfl⟩ : syracuseStep 506813 = 190055) (by norm_num)
theorem B867269 : Blo 334751 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B506837 : Blo 334751 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B506861 : Blo 334751 506861 := bbase (se 3 (by rfl) ⟨95036, by rfl⟩ : syracuseStep 506861 = 190073) (by norm_num)
theorem B1850357 : Blo 334751 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B506885 : Blo 334751 506885 := bbase (se 4 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 506885 = 95041) (by norm_num)
theorem B506909 : Blo 334751 506909 := bbase (se 3 (by rfl) ⟨95045, by rfl⟩ : syracuseStep 506909 = 190091) (by norm_num)
theorem B506933 : Blo 334751 506933 := bbase (se 5 (by rfl) ⟨23762, by rfl⟩ : syracuseStep 506933 = 47525) (by norm_num)
theorem B506957 : Blo 334751 506957 := bbase (se 3 (by rfl) ⟨95054, by rfl⟩ : syracuseStep 506957 = 190109) (by norm_num)
theorem B506981 : Blo 334751 506981 := bbase (se 4 (by rfl) ⟨47529, by rfl⟩ : syracuseStep 506981 = 95059) (by norm_num)
theorem B507005 : Blo 334751 507005 := bbase (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) (by norm_num)
theorem B507029 : Blo 334751 507029 := bbase (se 6 (by rfl) ⟨11883, by rfl⟩ : syracuseStep 507029 = 23767) (by norm_num)
theorem B507053 : Blo 334751 507053 := bbase (se 3 (by rfl) ⟨95072, by rfl⟩ : syracuseStep 507053 = 190145) (by norm_num)
theorem B507077 : Blo 334751 507077 := bbase (se 4 (by rfl) ⟨47538, by rfl⟩ : syracuseStep 507077 = 95077) (by norm_num)
theorem B507101 : Blo 334751 507101 := bbase (se 3 (by rfl) ⟨95081, by rfl⟩ : syracuseStep 507101 = 190163) (by norm_num)
theorem B343261 : Blo 334751 343261 := bbase (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) (by norm_num)
theorem B539893 : Blo 334751 539893 := bbase (se 5 (by rfl) ⟨25307, by rfl⟩ : syracuseStep 539893 = 50615) (by norm_num)
theorem B507125 : Blo 334751 507125 := bbase (se 5 (by rfl) ⟨23771, by rfl⟩ : syracuseStep 507125 = 47543) (by norm_num)
theorem B343285 : Blo 334751 343285 := bbase (se 5 (by rfl) ⟨16091, by rfl⟩ : syracuseStep 343285 = 32183) (by norm_num)
theorem B507149 : Blo 334751 507149 := bbase (se 3 (by rfl) ⟨95090, by rfl⟩ : syracuseStep 507149 = 190181) (by norm_num)
theorem B507173 : Blo 334751 507173 := bbase (se 4 (by rfl) ⟨47547, by rfl⟩ : syracuseStep 507173 = 95095) (by norm_num)
theorem B507197 : Blo 334751 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B638293 : Blo 334751 638293 := bbase (se 11 (by rfl) ⟨467, by rfl⟩ : syracuseStep 638293 = 935) (by norm_num)
theorem B507221 : Blo 334751 507221 := bbase (se 11 (by rfl) ⟨371, by rfl⟩ : syracuseStep 507221 = 743) (by norm_num)
theorem B507245 : Blo 334751 507245 := bbase (se 3 (by rfl) ⟨95108, by rfl⟩ : syracuseStep 507245 = 190217) (by norm_num)
theorem B2145653 : Blo 334751 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B507269 : Blo 334751 507269 := bbase (se 4 (by rfl) ⟨47556, by rfl⟩ : syracuseStep 507269 = 95113) (by norm_num)
theorem B507293 : Blo 334751 507293 := bbase (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) (by norm_num)
theorem B507317 : Blo 334751 507317 := bbase (se 5 (by rfl) ⟨23780, by rfl⟩ : syracuseStep 507317 = 47561) (by norm_num)
theorem B507341 : Blo 334751 507341 := bbase (se 3 (by rfl) ⟨95126, by rfl⟩ : syracuseStep 507341 = 190253) (by norm_num)
theorem B638437 : Blo 334751 638437 := bbase (se 4 (by rfl) ⟨59853, by rfl⟩ : syracuseStep 638437 = 119707) (by norm_num)
theorem B507365 : Blo 334751 507365 := bbase (se 4 (by rfl) ⟨47565, by rfl⟩ : syracuseStep 507365 = 95131) (by norm_num)
theorem B1916405 : Blo 334751 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B507389 : Blo 334751 507389 := bbase (se 3 (by rfl) ⟨95135, by rfl⟩ : syracuseStep 507389 = 190271) (by norm_num)
theorem B507413 : Blo 334751 507413 := bbase (se 6 (by rfl) ⟨11892, by rfl⟩ : syracuseStep 507413 = 23785) (by norm_num)
theorem B507437 : Blo 334751 507437 := bbase (se 3 (by rfl) ⟨95144, by rfl⟩ : syracuseStep 507437 = 190289) (by norm_num)
theorem B605765 : Blo 334751 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B507461 : Blo 334751 507461 := bbase (se 4 (by rfl) ⟨47574, by rfl⟩ : syracuseStep 507461 = 95149) (by norm_num)
theorem B507485 : Blo 334751 507485 := bbase (se 3 (by rfl) ⟨95153, by rfl⟩ : syracuseStep 507485 = 190307) (by norm_num)
theorem B507509 : Blo 334751 507509 := bbase (se 5 (by rfl) ⟨23789, by rfl⟩ : syracuseStep 507509 = 47579) (by norm_num)
theorem B638597 : Blo 334751 638597 := bbase (se 4 (by rfl) ⟨59868, by rfl⟩ : syracuseStep 638597 = 119737) (by norm_num)
theorem B507533 : Blo 334751 507533 := bbase (se 3 (by rfl) ⟨95162, by rfl⟩ : syracuseStep 507533 = 190325) (by norm_num)
theorem B507557 : Blo 334751 507557 := bbase (se 4 (by rfl) ⟨47583, by rfl⟩ : syracuseStep 507557 = 95167) (by norm_num)
theorem B1130165 : Blo 334751 1130165 := bbase (se 5 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 1130165 = 105953) (by norm_num)
theorem B507581 : Blo 334751 507581 := bbase (se 3 (by rfl) ⟨95171, by rfl⟩ : syracuseStep 507581 = 190343) (by norm_num)
theorem B507605 : Blo 334751 507605 := bbase (se 7 (by rfl) ⟨5948, by rfl⟩ : syracuseStep 507605 = 11897) (by norm_num)
theorem B769765 : Blo 334751 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B507629 : Blo 334751 507629 := bbase (se 3 (by rfl) ⟨95180, by rfl⟩ : syracuseStep 507629 = 190361) (by norm_num)
theorem B507653 : Blo 334751 507653 := bbase (se 4 (by rfl) ⟨47592, by rfl⟩ : syracuseStep 507653 = 95185) (by norm_num)
theorem B638741 : Blo 334751 638741 := bbase (se 6 (by rfl) ⟨14970, by rfl⟩ : syracuseStep 638741 = 29941) (by norm_num)
theorem B540437 : Blo 334751 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B507677 : Blo 334751 507677 := bbase (se 3 (by rfl) ⟨95189, by rfl⟩ : syracuseStep 507677 = 190379) (by norm_num)
theorem B376609 : Blo 334751 376609 := bbase (se 2 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 376609 = 282457) (by norm_num)
theorem B507701 : Blo 334751 507701 := bbase (se 5 (by rfl) ⟨23798, by rfl⟩ : syracuseStep 507701 = 47597) (by norm_num)
theorem B376645 : Blo 334751 376645 := bbase (se 4 (by rfl) ⟨35310, by rfl⟩ : syracuseStep 376645 = 70621) (by norm_num)
theorem B507725 : Blo 334751 507725 := bbase (se 3 (by rfl) ⟨95198, by rfl⟩ : syracuseStep 507725 = 190397) (by norm_num)
theorem B507749 : Blo 334751 507749 := bbase (se 4 (by rfl) ⟨47601, by rfl⟩ : syracuseStep 507749 = 95203) (by norm_num)
theorem B376681 : Blo 334751 376681 := bbase (se 2 (by rfl) ⟨141255, by rfl⟩ : syracuseStep 376681 = 282511) (by norm_num)
theorem B507773 : Blo 334751 507773 := bbase (se 3 (by rfl) ⟨95207, by rfl⟩ : syracuseStep 507773 = 190415) (by norm_num)
theorem B376717 : Blo 334751 376717 := bbase (se 3 (by rfl) ⟨70634, by rfl⟩ : syracuseStep 376717 = 141269) (by norm_num)
theorem B507797 : Blo 334751 507797 := bbase (se 6 (by rfl) ⟨11901, by rfl⟩ : syracuseStep 507797 = 23803) (by norm_num)
theorem B507821 : Blo 334751 507821 := bbase (se 3 (by rfl) ⟨95216, by rfl⟩ : syracuseStep 507821 = 190433) (by norm_num)
theorem B376753 : Blo 334751 376753 := bbase (se 2 (by rfl) ⟨141282, by rfl⟩ : syracuseStep 376753 = 282565) (by norm_num)
theorem B606133 : Blo 334751 606133 := bbase (se 5 (by rfl) ⟨28412, by rfl⟩ : syracuseStep 606133 = 56825) (by norm_num)
theorem B507845 : Blo 334751 507845 := bbase (se 4 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 507845 = 95221) (by norm_num)
theorem B376789 : Blo 334751 376789 := bbase (se 7 (by rfl) ⟨4415, by rfl⟩ : syracuseStep 376789 = 8831) (by norm_num)
theorem B507869 : Blo 334751 507869 := bbase (se 3 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 507869 = 190451) (by norm_num)
theorem B507893 : Blo 334751 507893 := bbase (se 5 (by rfl) ⟨23807, by rfl⟩ : syracuseStep 507893 = 47615) (by norm_num)
theorem B376825 : Blo 334751 376825 := bbase (se 2 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 376825 = 282619) (by norm_num)
theorem B507917 : Blo 334751 507917 := bbase (se 3 (by rfl) ⟨95234, by rfl⟩ : syracuseStep 507917 = 190469) (by norm_num)
theorem B376861 : Blo 334751 376861 := bbase (se 3 (by rfl) ⟨70661, by rfl⟩ : syracuseStep 376861 = 141323) (by norm_num)
theorem B507941 : Blo 334751 507941 := bbase (se 4 (by rfl) ⟨47619, by rfl⟩ : syracuseStep 507941 = 95239) (by norm_num)
theorem B639029 : Blo 334751 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B507965 : Blo 334751 507965 := bbase (se 3 (by rfl) ⟨95243, by rfl⟩ : syracuseStep 507965 = 190487) (by norm_num)
theorem B376897 : Blo 334751 376897 := bbase (se 2 (by rfl) ⟨141336, by rfl⟩ : syracuseStep 376897 = 282673) (by norm_num)
theorem B507989 : Blo 334751 507989 := bbase (se 8 (by rfl) ⟨2976, by rfl⟩ : syracuseStep 507989 = 5953) (by norm_num)
theorem B1130597 : Blo 334751 1130597 := bbase (se 4 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 1130597 = 211987) (by norm_num)
theorem B376933 : Blo 334751 376933 := bbase (se 4 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 376933 = 70675) (by norm_num)
theorem B508013 : Blo 334751 508013 := bbase (se 3 (by rfl) ⟨95252, by rfl⟩ : syracuseStep 508013 = 190505) (by norm_num)
theorem B508037 : Blo 334751 508037 := bbase (se 4 (by rfl) ⟨47628, by rfl⟩ : syracuseStep 508037 = 95257) (by norm_num)
theorem B376969 : Blo 334751 376969 := bbase (se 2 (by rfl) ⟨141363, by rfl⟩ : syracuseStep 376969 = 282727) (by norm_num)
theorem B508061 : Blo 334751 508061 := bbase (se 3 (by rfl) ⟨95261, by rfl⟩ : syracuseStep 508061 = 190523) (by norm_num)
theorem B377005 : Blo 334751 377005 := bbase (se 3 (by rfl) ⟨70688, by rfl⟩ : syracuseStep 377005 = 141377) (by norm_num)
theorem B508085 : Blo 334751 508085 := bbase (se 5 (by rfl) ⟨23816, by rfl⟩ : syracuseStep 508085 = 47633) (by norm_num)
theorem B639181 : Blo 334751 639181 := bbase (se 3 (by rfl) ⟨119846, by rfl⟩ : syracuseStep 639181 = 239693) (by norm_num)
theorem B508109 : Blo 334751 508109 := bbase (se 3 (by rfl) ⟨95270, by rfl⟩ : syracuseStep 508109 = 190541) (by norm_num)
theorem B377041 : Blo 334751 377041 := bbase (se 2 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 377041 = 282781) (by norm_num)
theorem B377077 : Blo 334751 377077 := bbase (se 5 (by rfl) ⟨17675, by rfl⟩ : syracuseStep 377077 = 35351) (by norm_num)
theorem B409865 : Blo 334751 409865 := bbase (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) (by norm_num)
theorem B377113 : Blo 334751 377113 := bbase (se 2 (by rfl) ⟨141417, by rfl⟩ : syracuseStep 377113 = 282835) (by norm_num)
theorem B377149 : Blo 334751 377149 := bbase (se 3 (by rfl) ⟨70715, by rfl⟩ : syracuseStep 377149 = 141431) (by norm_num)
theorem B540989 : Blo 334751 540989 := bbase (se 3 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 540989 = 202871) (by norm_num)
theorem B541021 : Blo 334751 541021 := bbase (se 3 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 541021 = 202883) (by norm_num)
theorem B377185 : Blo 334751 377185 := bbase (se 2 (by rfl) ⟨141444, by rfl⟩ : syracuseStep 377185 = 282889) (by norm_num)
theorem B1622389 : Blo 334751 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B377221 : Blo 334751 377221 := bbase (se 4 (by rfl) ⟨35364, by rfl⟩ : syracuseStep 377221 = 70729) (by norm_num)
theorem B1360261 : Blo 334751 1360261 := bbase (se 4 (by rfl) ⟨127524, by rfl⟩ : syracuseStep 1360261 = 255049) (by norm_num)
theorem B377257 : Blo 334751 377257 := bbase (se 2 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 377257 = 282943) (by norm_num)
theorem B377293 : Blo 334751 377293 := bbase (se 3 (by rfl) ⟨70742, by rfl⟩ : syracuseStep 377293 = 141485) (by norm_num)
theorem B377329 : Blo 334751 377329 := bbase (se 2 (by rfl) ⟨141498, by rfl⟩ : syracuseStep 377329 = 282997) (by norm_num)
theorem B639485 : Blo 334751 639485 := bbase (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) (by norm_num)
theorem B1131029 : Blo 334751 1131029 := bbase (se 6 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 1131029 = 53017) (by norm_num)
theorem B377365 : Blo 334751 377365 := bbase (se 6 (by rfl) ⟨8844, by rfl⟩ : syracuseStep 377365 = 17689) (by norm_num)
theorem B377401 : Blo 334751 377401 := bbase (se 2 (by rfl) ⟨141525, by rfl⟩ : syracuseStep 377401 = 283051) (by norm_num)
theorem B377437 : Blo 334751 377437 := bbase (se 3 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 377437 = 141539) (by norm_num)
theorem B377473 : Blo 334751 377473 := bbase (se 2 (by rfl) ⟨141552, by rfl⟩ : syracuseStep 377473 = 283105) (by norm_num)
theorem B377509 : Blo 334751 377509 := bbase (se 4 (by rfl) ⟨35391, by rfl⟩ : syracuseStep 377509 = 70783) (by norm_num)
theorem B377545 : Blo 334751 377545 := bbase (se 2 (by rfl) ⟨141579, by rfl⟩ : syracuseStep 377545 = 283159) (by norm_num)
theorem B377581 : Blo 334751 377581 := bbase (se 3 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 377581 = 141593) (by norm_num)
theorem B377617 : Blo 334751 377617 := bbase (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) (by norm_num)
theorem B377653 : Blo 334751 377653 := bbase (se 5 (by rfl) ⟨17702, by rfl⟩ : syracuseStep 377653 = 35405) (by norm_num)
theorem B377689 : Blo 334751 377689 := bbase (se 2 (by rfl) ⟨141633, by rfl⟩ : syracuseStep 377689 = 283267) (by norm_num)
theorem B770933 : Blo 334751 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B377725 : Blo 334751 377725 := bbase (se 3 (by rfl) ⟨70823, by rfl⟩ : syracuseStep 377725 = 141647) (by norm_num)
theorem B377761 : Blo 334751 377761 := bbase (se 2 (by rfl) ⟨141660, by rfl⟩ : syracuseStep 377761 = 283321) (by norm_num)
theorem B1098677 : Blo 334751 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B1131461 : Blo 334751 1131461 := bbase (se 4 (by rfl) ⟨106074, by rfl⟩ : syracuseStep 1131461 = 212149) (by norm_num)
theorem B377797 : Blo 334751 377797 := bbase (se 4 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 377797 = 70837) (by norm_num)
theorem B377833 : Blo 334751 377833 := bbase (se 2 (by rfl) ⟨141687, by rfl⟩ : syracuseStep 377833 = 283375) (by norm_num)
theorem B377869 : Blo 334751 377869 := bbase (se 3 (by rfl) ⟨70850, by rfl⟩ : syracuseStep 377869 = 141701) (by norm_num)
theorem B377905 : Blo 334751 377905 := bbase (se 2 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 377905 = 283429) (by norm_num)
theorem B377941 : Blo 334751 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B377977 : Blo 334751 377977 := bbase (se 2 (by rfl) ⟨141741, by rfl⟩ : syracuseStep 377977 = 283483) (by norm_num)
theorem B378013 : Blo 334751 378013 := bbase (se 3 (by rfl) ⟨70877, by rfl⟩ : syracuseStep 378013 = 141755) (by norm_num)
theorem B378049 : Blo 334751 378049 := bbase (se 2 (by rfl) ⟨141768, by rfl⟩ : syracuseStep 378049 = 283537) (by norm_num)
theorem B378085 : Blo 334751 378085 := bbase (se 4 (by rfl) ⟨35445, by rfl⟩ : syracuseStep 378085 = 70891) (by norm_num)
theorem B640237 : Blo 334751 640237 := bbase (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) (by norm_num)
theorem B541949 : Blo 334751 541949 := bbase (se 3 (by rfl) ⟨101615, by rfl⟩ : syracuseStep 541949 = 203231) (by norm_num)
theorem B378121 : Blo 334751 378121 := bbase (se 2 (by rfl) ⟨141795, by rfl⟩ : syracuseStep 378121 = 283591) (by norm_num)
theorem B607517 : Blo 334751 607517 := bbase (se 3 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 607517 = 227819) (by norm_num)
theorem B378157 : Blo 334751 378157 := bbase (se 3 (by rfl) ⟨70904, by rfl⟩ : syracuseStep 378157 = 141809) (by norm_num)
theorem B378193 : Blo 334751 378193 := bbase (se 2 (by rfl) ⟨141822, by rfl⟩ : syracuseStep 378193 = 283645) (by norm_num)
theorem B1131893 : Blo 334751 1131893 := bbase (se 5 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 1131893 = 106115) (by norm_num)
theorem B378229 : Blo 334751 378229 := bbase (se 5 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 378229 = 35459) (by norm_num)
theorem B640381 : Blo 334751 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B378265 : Blo 334751 378265 := bbase (se 2 (by rfl) ⟨141849, by rfl⟩ : syracuseStep 378265 = 283699) (by norm_num)
theorem B378301 : Blo 334751 378301 := bbase (se 3 (by rfl) ⟨70931, by rfl⟩ : syracuseStep 378301 = 141863) (by norm_num)
theorem B378337 : Blo 334751 378337 := bbase (se 2 (by rfl) ⟨141876, by rfl⟩ : syracuseStep 378337 = 283753) (by norm_num)
theorem B378373 : Blo 334751 378373 := bbase (se 4 (by rfl) ⟨35472, by rfl⟩ : syracuseStep 378373 = 70945) (by norm_num)
theorem B640541 : Blo 334751 640541 := bbase (se 3 (by rfl) ⟨120101, by rfl⟩ : syracuseStep 640541 = 240203) (by norm_num)
theorem B804389 : Blo 334751 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B378409 : Blo 334751 378409 := bbase (se 2 (by rfl) ⟨141903, by rfl⟩ : syracuseStep 378409 = 283807) (by norm_num)
theorem B378445 : Blo 334751 378445 := bbase (se 3 (by rfl) ⟨70958, by rfl⟩ : syracuseStep 378445 = 141917) (by norm_num)
theorem B378481 : Blo 334751 378481 := bbase (se 2 (by rfl) ⟨141930, by rfl⟩ : syracuseStep 378481 = 283861) (by norm_num)
theorem B378517 : Blo 334751 378517 := bbase (se 6 (by rfl) ⟨8871, by rfl⟩ : syracuseStep 378517 = 17743) (by norm_num)
theorem B640685 : Blo 334751 640685 := bbase (se 3 (by rfl) ⟨120128, by rfl⟩ : syracuseStep 640685 = 240257) (by norm_num)
theorem B378553 : Blo 334751 378553 := bbase (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) (by norm_num)
theorem B476869 : Blo 334751 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B378589 : Blo 334751 378589 := bbase (se 3 (by rfl) ⟨70985, by rfl⟩ : syracuseStep 378589 = 141971) (by norm_num)
theorem B378625 : Blo 334751 378625 := bbase (se 2 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 378625 = 283969) (by norm_num)
theorem B1132325 : Blo 334751 1132325 := bbase (se 4 (by rfl) ⟨106155, by rfl⟩ : syracuseStep 1132325 = 212311) (by norm_num)
theorem B378661 : Blo 334751 378661 := bbase (se 4 (by rfl) ⟨35499, by rfl⟩ : syracuseStep 378661 = 70999) (by norm_num)
theorem B378697 : Blo 334751 378697 := bbase (se 2 (by rfl) ⟨142011, by rfl⟩ : syracuseStep 378697 = 284023) (by norm_num)
theorem B378733 : Blo 334751 378733 := bbase (se 3 (by rfl) ⟨71012, by rfl⟩ : syracuseStep 378733 = 142025) (by norm_num)
theorem B378769 : Blo 334751 378769 := bbase (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) (by norm_num)
theorem B477085 : Blo 334751 477085 := bbase (se 3 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 477085 = 178907) (by norm_num)
theorem B378805 : Blo 334751 378805 := bbase (se 5 (by rfl) ⟨17756, by rfl⟩ : syracuseStep 378805 = 35513) (by norm_num)
theorem B640973 : Blo 334751 640973 := bbase (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) (by norm_num)
theorem B378841 : Blo 334751 378841 := bbase (se 2 (by rfl) ⟨142065, by rfl⟩ : syracuseStep 378841 = 284131) (by norm_num)
theorem B378877 : Blo 334751 378877 := bbase (se 3 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 378877 = 142079) (by norm_num)
theorem B378913 : Blo 334751 378913 := bbase (se 2 (by rfl) ⟨142092, by rfl⟩ : syracuseStep 378913 = 284185) (by norm_num)
theorem B378949 : Blo 334751 378949 := bbase (se 4 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 378949 = 71053) (by norm_num)
theorem B641125 : Blo 334751 641125 := bbase (se 4 (by rfl) ⟨60105, by rfl⟩ : syracuseStep 641125 = 120211) (by norm_num)
theorem B378985 : Blo 334751 378985 := bbase (se 2 (by rfl) ⟨142119, by rfl⟩ : syracuseStep 378985 = 284239) (by norm_num)
theorem B379021 : Blo 334751 379021 := bbase (se 3 (by rfl) ⟨71066, by rfl⟩ : syracuseStep 379021 = 142133) (by norm_num)
theorem B379057 : Blo 334751 379057 := bbase (se 2 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 379057 = 284293) (by norm_num)
theorem B1132757 : Blo 334751 1132757 := bbase (se 7 (by rfl) ⟨13274, by rfl⟩ : syracuseStep 1132757 = 26549) (by norm_num)
theorem B379093 : Blo 334751 379093 := bbase (se 7 (by rfl) ⟨4442, by rfl⟩ : syracuseStep 379093 = 8885) (by norm_num)
theorem B379129 : Blo 334751 379129 := bbase (se 2 (by rfl) ⟨142173, by rfl⟩ : syracuseStep 379129 = 284347) (by norm_num)
theorem B477461 : Blo 334751 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B379165 : Blo 334751 379165 := bbase (se 3 (by rfl) ⟨71093, by rfl⟩ : syracuseStep 379165 = 142187) (by norm_num)
theorem B379201 : Blo 334751 379201 := bbase (se 2 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 379201 = 284401) (by norm_num)
theorem B379237 : Blo 334751 379237 := bbase (se 4 (by rfl) ⟨35553, by rfl⟩ : syracuseStep 379237 = 71107) (by norm_num)
theorem B379273 : Blo 334751 379273 := bbase (se 2 (by rfl) ⟨142227, by rfl⟩ : syracuseStep 379273 = 284455) (by norm_num)
theorem B641429 : Blo 334751 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B379309 : Blo 334751 379309 := bbase (se 3 (by rfl) ⟨71120, by rfl⟩ : syracuseStep 379309 = 142241) (by norm_num)
theorem B379345 : Blo 334751 379345 := bbase (se 2 (by rfl) ⟨142254, by rfl⟩ : syracuseStep 379345 = 284509) (by norm_num)
theorem B379381 : Blo 334751 379381 := bbase (se 5 (by rfl) ⟨17783, by rfl⟩ : syracuseStep 379381 = 35567) (by norm_num)
theorem B379417 : Blo 334751 379417 := bbase (se 2 (by rfl) ⟨142281, by rfl⟩ : syracuseStep 379417 = 284563) (by norm_num)
theorem B379453 : Blo 334751 379453 := bbase (se 3 (by rfl) ⟨71147, by rfl⟩ : syracuseStep 379453 = 142295) (by norm_num)
theorem B379489 : Blo 334751 379489 := bbase (se 2 (by rfl) ⟨142308, by rfl⟩ : syracuseStep 379489 = 284617) (by norm_num)
theorem B1133189 : Blo 334751 1133189 := bbase (se 4 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 1133189 = 212473) (by norm_num)
theorem B379525 : Blo 334751 379525 := bbase (se 4 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 379525 = 71161) (by norm_num)
theorem B379561 : Blo 334751 379561 := bbase (se 2 (by rfl) ⟨142335, by rfl⟩ : syracuseStep 379561 = 284671) (by norm_num)
theorem B379597 : Blo 334751 379597 := bbase (se 3 (by rfl) ⟨71174, by rfl⟩ : syracuseStep 379597 = 142349) (by norm_num)
theorem B7785173 : Blo 334751 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B379633 : Blo 334751 379633 := bbase (se 2 (by rfl) ⟨142362, by rfl⟩ : syracuseStep 379633 = 284725) (by norm_num)
theorem B379669 : Blo 334751 379669 := bbase (se 6 (by rfl) ⟨8898, by rfl⟩ : syracuseStep 379669 = 17797) (by norm_num)
theorem B379705 : Blo 334751 379705 := bbase (se 2 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 379705 = 284779) (by norm_num)
theorem B510781 : Blo 334751 510781 := bbase (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) (by norm_num)
theorem B379741 : Blo 334751 379741 := bbase (se 3 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 379741 = 142403) (by norm_num)
theorem B379777 : Blo 334751 379777 := bbase (se 2 (by rfl) ⟨142416, by rfl⟩ : syracuseStep 379777 = 284833) (by norm_num)
theorem B510853 : Blo 334751 510853 := bbase (se 4 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 510853 = 95785) (by norm_num)
theorem B871309 : Blo 334751 871309 := bbase (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) (by norm_num)
theorem B510877 : Blo 334751 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B379813 : Blo 334751 379813 := bbase (se 4 (by rfl) ⟨35607, by rfl⟩ : syracuseStep 379813 = 71215) (by norm_num)
theorem B379849 : Blo 334751 379849 := bbase (se 2 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 379849 = 284887) (by norm_num)
theorem B379885 : Blo 334751 379885 := bbase (se 3 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 379885 = 142457) (by norm_num)
theorem B379921 : Blo 334751 379921 := bbase (se 2 (by rfl) ⟨142470, by rfl⟩ : syracuseStep 379921 = 284941) (by norm_num)
theorem B1035301 : Blo 334751 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B1133621 : Blo 334751 1133621 := bbase (se 5 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 1133621 = 106277) (by norm_num)
theorem B379957 : Blo 334751 379957 := bbase (se 5 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 379957 = 35621) (by norm_num)
theorem B1723477 : Blo 334751 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B379993 : Blo 334751 379993 := bbase (se 2 (by rfl) ⟨142497, by rfl⟩ : syracuseStep 379993 = 284995) (by norm_num)
theorem B380029 : Blo 334751 380029 := bbase (se 3 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 380029 = 142511) (by norm_num)
theorem B642181 : Blo 334751 642181 := bbase (se 4 (by rfl) ⟨60204, by rfl⟩ : syracuseStep 642181 = 120409) (by norm_num)
theorem B380065 : Blo 334751 380065 := bbase (se 2 (by rfl) ⟨142524, by rfl⟩ : syracuseStep 380065 = 285049) (by norm_num)
theorem B380101 : Blo 334751 380101 := bbase (se 4 (by rfl) ⟨35634, by rfl⟩ : syracuseStep 380101 = 71269) (by norm_num)
theorem B380137 : Blo 334751 380137 := bbase (se 2 (by rfl) ⟨142551, by rfl⟩ : syracuseStep 380137 = 285103) (by norm_num)
theorem B806149 : Blo 334751 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B380173 : Blo 334751 380173 := bbase (se 3 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 380173 = 142565) (by norm_num)
theorem B642325 : Blo 334751 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B380209 : Blo 334751 380209 := bbase (se 2 (by rfl) ⟨142578, by rfl⟩ : syracuseStep 380209 = 285157) (by norm_num)
theorem B380245 : Blo 334751 380245 := bbase (se 11 (by rfl) ⟨278, by rfl⟩ : syracuseStep 380245 = 557) (by norm_num)
theorem B380281 : Blo 334751 380281 := bbase (se 2 (by rfl) ⟨142605, by rfl⟩ : syracuseStep 380281 = 285211) (by norm_num)
theorem B380317 : Blo 334751 380317 := bbase (se 3 (by rfl) ⟨71309, by rfl⟩ : syracuseStep 380317 = 142619) (by norm_num)
theorem B642485 : Blo 334751 642485 := bbase (se 5 (by rfl) ⟨30116, by rfl⟩ : syracuseStep 642485 = 60233) (by norm_num)
theorem B380353 : Blo 334751 380353 := bbase (se 2 (by rfl) ⟨142632, by rfl⟩ : syracuseStep 380353 = 285265) (by norm_num)
theorem B1134053 : Blo 334751 1134053 := bbase (se 4 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 1134053 = 212635) (by norm_num)
theorem B380389 : Blo 334751 380389 := bbase (se 4 (by rfl) ⟨35661, by rfl⟩ : syracuseStep 380389 = 71323) (by norm_num)
theorem B806381 : Blo 334751 806381 := bbase (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) (by norm_num)
theorem B609781 : Blo 334751 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B380425 : Blo 334751 380425 := bbase (se 2 (by rfl) ⟨142659, by rfl⟩ : syracuseStep 380425 = 285319) (by norm_num)
theorem B1363493 : Blo 334751 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B380461 : Blo 334751 380461 := bbase (se 3 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 380461 = 142673) (by norm_num)
theorem B642629 : Blo 334751 642629 := bbase (se 4 (by rfl) ⟨60246, by rfl⟩ : syracuseStep 642629 = 120493) (by norm_num)
theorem B380497 : Blo 334751 380497 := bbase (se 2 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 380497 = 285373) (by norm_num)
theorem B380533 : Blo 334751 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B380569 : Blo 334751 380569 := bbase (se 2 (by rfl) ⟨142713, by rfl⟩ : syracuseStep 380569 = 285427) (by norm_num)
theorem B478885 : Blo 334751 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B380605 : Blo 334751 380605 := bbase (se 3 (by rfl) ⟨71363, by rfl⟩ : syracuseStep 380605 = 142727) (by norm_num)
theorem B380641 : Blo 334751 380641 := bbase (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) (by norm_num)
theorem B380677 : Blo 334751 380677 := bbase (se 4 (by rfl) ⟨35688, by rfl⟩ : syracuseStep 380677 = 71377) (by norm_num)
theorem B380713 : Blo 334751 380713 := bbase (se 2 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 380713 = 285535) (by norm_num)
theorem B380749 : Blo 334751 380749 := bbase (se 3 (by rfl) ⟨71390, by rfl⟩ : syracuseStep 380749 = 142781) (by norm_num)
theorem B642917 : Blo 334751 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B380785 : Blo 334751 380785 := bbase (se 2 (by rfl) ⟨142794, by rfl⟩ : syracuseStep 380785 = 285589) (by norm_num)
theorem B806773 : Blo 334751 806773 := bbase (se 5 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 806773 = 75635) (by norm_num)
theorem B1134485 : Blo 334751 1134485 := bbase (se 6 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 1134485 = 53179) (by norm_num)
theorem B380821 : Blo 334751 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B380857 : Blo 334751 380857 := bbase (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) (by norm_num)
theorem B380893 : Blo 334751 380893 := bbase (se 3 (by rfl) ⟨71417, by rfl⟩ : syracuseStep 380893 = 142835) (by norm_num)
theorem B643069 : Blo 334751 643069 := bbase (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) (by norm_num)
theorem B380929 : Blo 334751 380929 := bbase (se 2 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 380929 = 285697) (by norm_num)
theorem B380965 : Blo 334751 380965 := bbase (se 4 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 380965 = 71431) (by norm_num)
theorem B381001 : Blo 334751 381001 := bbase (se 2 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 381001 = 285751) (by norm_num)
theorem B381037 : Blo 334751 381037 := bbase (se 3 (by rfl) ⟨71444, by rfl⟩ : syracuseStep 381037 = 142889) (by norm_num)
theorem B381073 : Blo 334751 381073 := bbase (se 2 (by rfl) ⟨142902, by rfl⟩ : syracuseStep 381073 = 285805) (by norm_num)
theorem B479477 : Blo 334751 479477 := bbase (se 5 (by rfl) ⟨22475, by rfl⟩ : syracuseStep 479477 = 44951) (by norm_num)
theorem B1134917 : Blo 334751 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B479557 : Blo 334751 479557 := bbase (se 4 (by rfl) ⟨44958, by rfl⟩ : syracuseStep 479557 = 89917) (by norm_num)
theorem B512381 : Blo 334751 512381 := bbase (se 3 (by rfl) ⟨96071, by rfl⟩ : syracuseStep 512381 = 192143) (by norm_num)
theorem B479677 : Blo 334751 479677 := bbase (se 3 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 479677 = 179879) (by norm_num)
theorem B479773 : Blo 334751 479773 := bbase (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) (by norm_num)
theorem B1135349 : Blo 334751 1135349 := bbase (se 5 (by rfl) ⟨53219, by rfl⟩ : syracuseStep 1135349 = 106439) (by norm_num)
theorem B971669 : Blo 334751 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B807869 : Blo 334751 807869 := bbase (se 3 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 807869 = 302951) (by norm_num)
theorem B480269 : Blo 334751 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B1430693 : Blo 334751 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B1135781 : Blo 334751 1135781 := bbase (se 4 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 1135781 = 212959) (by norm_num)
theorem B808157 : Blo 334751 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B480821 : Blo 334751 480821 := bbase (se 5 (by rfl) ⟨22538, by rfl⟩ : syracuseStep 480821 = 45077) (by norm_num)
theorem B1037893 : Blo 334751 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B1136213 : Blo 334751 1136213 := bbase (se 8 (by rfl) ⟨6657, by rfl⟩ : syracuseStep 1136213 = 13315) (by norm_num)
theorem B611933 : Blo 334751 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B1136645 : Blo 334751 1136645 := bbase (se 4 (by rfl) ⟨106560, by rfl⟩ : syracuseStep 1136645 = 213121) (by norm_num)
theorem B514181 : Blo 334751 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B1431701 : Blo 334751 1431701 := bbase (se 6 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 1431701 = 67111) (by norm_num)
theorem B547021 : Blo 334751 547021 := bbase (se 3 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 547021 = 205133) (by norm_num)
theorem B481573 : Blo 334751 481573 := bbase (se 4 (by rfl) ⟨45147, by rfl⟩ : syracuseStep 481573 = 90295) (by norm_num)
theorem B514477 : Blo 334751 514477 := bbase (se 3 (by rfl) ⟨96464, by rfl⟩ : syracuseStep 514477 = 192929) (by norm_num)
theorem B1137077 : Blo 334751 1137077 := bbase (se 5 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 1137077 = 106601) (by norm_num)
theorem B1300981 : Blo 334751 1300981 := bbase (se 5 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 1300981 = 121967) (by norm_num)
theorem B1530661 : Blo 334751 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B645965 : Blo 334751 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B1137509 : Blo 334751 1137509 := bbase (se 4 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 1137509 = 213283) (by norm_num)
theorem B547733 : Blo 334751 547733 := bbase (se 6 (by rfl) ⟨12837, by rfl⟩ : syracuseStep 547733 = 25675) (by norm_num)
theorem B679045 : Blo 334751 679045 := bbase (se 4 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 679045 = 127321) (by norm_num)
theorem B679061 : Blo 334751 679061 := bbase (se 6 (by rfl) ⟨15915, by rfl⟩ : syracuseStep 679061 = 31831) (by norm_num)
theorem B580853 : Blo 334751 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B548093 : Blo 334751 548093 := bbase (se 3 (by rfl) ⟨102767, by rfl⟩ : syracuseStep 548093 = 205535) (by norm_num)
theorem B810253 : Blo 334751 810253 := bbase (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) (by norm_num)
theorem B1137941 : Blo 334751 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B1924469 : Blo 334751 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B2547125 : Blo 334751 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B1564085 : Blo 334751 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B384545 : Blo 334751 384545 := bbase (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) (by norm_num)
theorem B613973 : Blo 334751 613973 := bbase (se 8 (by rfl) ⟨3597, by rfl⟩ : syracuseStep 613973 = 7195) (by norm_num)
theorem B2252405 : Blo 334751 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1138373 : Blo 334751 1138373 := bbase (se 4 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 1138373 = 213445) (by norm_num)
theorem B548669 : Blo 334751 548669 := bbase (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) (by norm_num)
theorem B1433477 : Blo 334751 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1695653 : Blo 334751 1695653 := bbase (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) (by norm_num)
theorem B810917 : Blo 334751 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B1138805 : Blo 334751 1138805 := bbase (se 5 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 1138805 = 106763) (by norm_num)
theorem B647317 : Blo 334751 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B385493 : Blo 334751 385493 := bbase (se 7 (by rfl) ⟨4517, by rfl⟩ : syracuseStep 385493 = 9035) (by norm_num)
theorem B1925653 : Blo 334751 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B1139237 : Blo 334751 1139237 := bbase (se 4 (by rfl) ⟨106803, by rfl⟩ : syracuseStep 1139237 = 213607) (by norm_num)
theorem B1073749 : Blo 334751 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B647765 : Blo 334751 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B516709 : Blo 334751 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B2417525 : Blo 334751 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B615325 : Blo 334751 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B1139669 : Blo 334751 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B386077 : Blo 334751 386077 := bbase (se 3 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 386077 = 144779) (by norm_num)
theorem B1696949 : Blo 334751 1696949 := bbase (se 5 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 1696949 = 159089) (by norm_num)
theorem B1140101 : Blo 334751 1140101 := bbase (se 4 (by rfl) ⟨106884, by rfl⟩ : syracuseStep 1140101 = 213769) (by norm_num)
theorem B681365 : Blo 334751 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B1369541 : Blo 334751 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B1271285 : Blo 334751 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B812693 : Blo 334751 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B1140533 : Blo 334751 1140533 := bbase (se 5 (by rfl) ⟨53462, by rfl⟩ : syracuseStep 1140533 = 106925) (by norm_num)
theorem B4319189 : Blo 334751 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B616405 : Blo 334751 616405 := bbase (se 7 (by rfl) ⟨7223, by rfl⟩ : syracuseStep 616405 = 14447) (by norm_num)
theorem B518341 : Blo 334751 518341 := bbase (se 4 (by rfl) ⟨48594, by rfl⟩ : syracuseStep 518341 = 97189) (by norm_num)
theorem B1140965 : Blo 334751 1140965 := bbase (se 4 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 1140965 = 213931) (by norm_num)
theorem B911621 : Blo 334751 911621 := bbase (se 4 (by rfl) ⟨85464, by rfl⟩ : syracuseStep 911621 = 170929) (by norm_num)
theorem B616837 : Blo 334751 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B1698245 : Blo 334751 1698245 := bbase (se 4 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 1698245 = 318421) (by norm_num)
theorem B1927637 : Blo 334751 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B453205 : Blo 334751 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B682597 : Blo 334751 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B1206917 : Blo 334751 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B1272469 : Blo 334751 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B1141397 : Blo 334751 1141397 := bbase (se 6 (by rfl) ⟨26751, by rfl⟩ : syracuseStep 1141397 = 53503) (by norm_num)
theorem B387941 : Blo 334751 387941 := bbase (se 4 (by rfl) ⟨36369, by rfl⟩ : syracuseStep 387941 = 72739) (by norm_num)
theorem B715645 : Blo 334751 715645 := bbase (se 3 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 715645 = 268367) (by norm_num)
theorem B1272773 : Blo 334751 1272773 := bbase (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) (by norm_num)
theorem B519229 : Blo 334751 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B1141829 : Blo 334751 1141829 := bbase (se 4 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 1141829 = 214093) (by norm_num)
theorem B519341 : Blo 334751 519341 := bbase (se 3 (by rfl) ⟨97376, by rfl⟩ : syracuseStep 519341 = 194753) (by norm_num)
theorem B2157749 : Blo 334751 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B453853 : Blo 334751 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B683245 : Blo 334751 683245 := bbase (se 3 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 683245 = 256217) (by norm_num)
theorem B716141 : Blo 334751 716141 := bbase (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) (by norm_num)
theorem B1142261 : Blo 334751 1142261 := bbase (se 5 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 1142261 = 107087) (by norm_num)
theorem B847381 : Blo 334751 847381 := bbase (se 6 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 847381 = 39721) (by norm_num)
theorem B847493 : Blo 334751 847493 := bbase (se 4 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 847493 = 158905) (by norm_num)
theorem B1699541 : Blo 334751 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B913157 : Blo 334751 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B847685 : Blo 334751 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B1372069 : Blo 334751 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1142693 : Blo 334751 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B2060245 : Blo 334751 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B1437749 : Blo 334751 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B553061 : Blo 334751 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B848029 : Blo 334751 848029 := bbase (se 3 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 848029 = 318011) (by norm_num)
theorem B913589 : Blo 334751 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B717029 : Blo 334751 717029 := bbase (se 4 (by rfl) ⟨67221, by rfl⟩ : syracuseStep 717029 = 134443) (by norm_num)
theorem B1831157 : Blo 334751 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B848141 : Blo 334751 848141 := bbase (se 3 (by rfl) ⟨159026, by rfl⟩ : syracuseStep 848141 = 318053) (by norm_num)
theorem B1143125 : Blo 334751 1143125 := bbase (se 10 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 1143125 = 3349) (by norm_num)
theorem B717149 : Blo 334751 717149 := bbase (se 3 (by rfl) ⟨134465, by rfl⟩ : syracuseStep 717149 = 268931) (by norm_num)
theorem B3830165 : Blo 334751 3830165 := bbase (se 6 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 3830165 = 179539) (by norm_num)
theorem B848333 : Blo 334751 848333 := bbase (se 3 (by rfl) ⟨159062, by rfl⟩ : syracuseStep 848333 = 318125) (by norm_num)
theorem B487949 : Blo 334751 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B1110629 : Blo 334751 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B1077941 : Blo 334751 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B848677 : Blo 334751 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B848789 : Blo 334751 848789 := bbase (se 6 (by rfl) ⟨19893, by rfl⟩ : syracuseStep 848789 = 39787) (by norm_num)
theorem B717781 : Blo 334751 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B1700837 : Blo 334751 1700837 := bbase (se 4 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 1700837 = 318907) (by norm_num)
theorem B1274885 : Blo 334751 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B1373237 : Blo 334751 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B848981 : Blo 334751 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B357481 : Blo 334751 357481 := bbase (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) (by norm_num)
theorem B1275173 : Blo 334751 1275173 := bbase (se 4 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 1275173 = 239095) (by norm_num)
theorem B3437909 : Blo 334751 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B357797 : Blo 334751 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B849325 : Blo 334751 849325 := bbase (se 3 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 849325 = 318497) (by norm_num)
theorem B849437 : Blo 334751 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B849629 : Blo 334751 849629 := bbase (se 3 (by rfl) ⟨159305, by rfl⟩ : syracuseStep 849629 = 318611) (by norm_num)
theorem B1439525 : Blo 334751 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B423721 : Blo 334751 423721 := bbase (se 2 (by rfl) ⟨158895, by rfl⟩ : syracuseStep 423721 = 317791) (by norm_num)
theorem B3143477 : Blo 334751 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B718669 : Blo 334751 718669 := bbase (se 3 (by rfl) ⟨134750, by rfl⟩ : syracuseStep 718669 = 269501) (by norm_num)
theorem B358241 : Blo 334751 358241 := bbase (se 2 (by rfl) ⟨134340, by rfl⟩ : syracuseStep 358241 = 268681) (by norm_num)
theorem B358301 : Blo 334751 358301 := bbase (se 3 (by rfl) ⟨67181, by rfl⟩ : syracuseStep 358301 = 134363) (by norm_num)
theorem B718789 : Blo 334751 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B423893 : Blo 334751 423893 := bbase (se 7 (by rfl) ⟨4967, by rfl⟩ : syracuseStep 423893 = 9935) (by norm_num)
theorem B423949 : Blo 334751 423949 := bbase (se 3 (by rfl) ⟨79490, by rfl⟩ : syracuseStep 423949 = 158981) (by norm_num)
theorem B1439765 : Blo 334751 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B358429 : Blo 334751 358429 := bbase (se 3 (by rfl) ⟨67205, by rfl⟩ : syracuseStep 358429 = 134411) (by norm_num)
theorem B849973 : Blo 334751 849973 := bbase (se 5 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 849973 = 79685) (by norm_num)
theorem B424045 : Blo 334751 424045 := bbase (se 3 (by rfl) ⟨79508, by rfl⟩ : syracuseStep 424045 = 159017) (by norm_num)
theorem B850085 : Blo 334751 850085 := bbase (se 4 (by rfl) ⟨79695, by rfl⟩ : syracuseStep 850085 = 159391) (by norm_num)
theorem B719045 : Blo 334751 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B1702133 : Blo 334751 1702133 := bbase (se 5 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 1702133 = 159575) (by norm_num)
theorem B2193685 : Blo 334751 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B424217 : Blo 334751 424217 := bbase (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) (by norm_num)
theorem B424273 : Blo 334751 424273 := bbase (se 2 (by rfl) ⟨159102, by rfl⟩ : syracuseStep 424273 = 318205) (by norm_num)
theorem B850277 : Blo 334751 850277 := bbase (se 4 (by rfl) ⟨79713, by rfl⟩ : syracuseStep 850277 = 159427) (by norm_num)
theorem B424369 : Blo 334751 424369 := bbase (se 2 (by rfl) ⟨159138, by rfl⟩ : syracuseStep 424369 = 318277) (by norm_num)
theorem B1276357 : Blo 334751 1276357 := bbase (se 4 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 1276357 = 239317) (by norm_num)
theorem B358873 : Blo 334751 358873 := bbase (se 2 (by rfl) ⟨134577, by rfl⟩ : syracuseStep 358873 = 269155) (by norm_num)
theorem B2423317 : Blo 334751 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B358993 : Blo 334751 358993 := bbase (se 2 (by rfl) ⟨134622, by rfl⟩ : syracuseStep 358993 = 269245) (by norm_num)
theorem B424541 : Blo 334751 424541 := bbase (se 3 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 424541 = 159203) (by norm_num)
theorem B424597 : Blo 334751 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B850621 : Blo 334751 850621 := bbase (se 3 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 850621 = 318983) (by norm_num)
theorem B555709 : Blo 334751 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B424693 : Blo 334751 424693 := bbase (se 5 (by rfl) ⟨19907, by rfl⟩ : syracuseStep 424693 = 39815) (by norm_num)
theorem B1276661 : Blo 334751 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B850733 : Blo 334751 850733 := bbase (se 3 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 850733 = 319025) (by norm_num)
theorem B457525 : Blo 334751 457525 := bbase (se 5 (by rfl) ⟨21446, by rfl⟩ : syracuseStep 457525 = 42893) (by norm_num)
theorem B359245 : Blo 334751 359245 := bbase (se 3 (by rfl) ⟨67358, by rfl⟩ : syracuseStep 359245 = 134717) (by norm_num)
theorem B359249 : Blo 334751 359249 := bbase (se 2 (by rfl) ⟨134718, by rfl⟩ : syracuseStep 359249 = 269437) (by norm_num)
theorem B424865 : Blo 334751 424865 := bbase (se 2 (by rfl) ⟨159324, by rfl⟩ : syracuseStep 424865 = 318649) (by norm_num)
theorem B424921 : Blo 334751 424921 := bbase (se 2 (by rfl) ⟨159345, by rfl⟩ : syracuseStep 424921 = 318691) (by norm_num)
theorem B850925 : Blo 334751 850925 := bbase (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) (by norm_num)
theorem B457741 : Blo 334751 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B2554901 : Blo 334751 2554901 := bbase (se 6 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 2554901 = 119761) (by norm_num)
theorem B425017 : Blo 334751 425017 := bbase (se 2 (by rfl) ⟨159381, by rfl⟩ : syracuseStep 425017 = 318763) (by norm_num)
theorem B719933 : Blo 334751 719933 := bbase (se 3 (by rfl) ⟨134987, by rfl⟩ : syracuseStep 719933 = 269975) (by norm_num)
theorem B425189 : Blo 334751 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B2718965 : Blo 334751 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B425245 : Blo 334751 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B720173 : Blo 334751 720173 := bbase (se 3 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 720173 = 270065) (by norm_num)
theorem B851269 : Blo 334751 851269 := bbase (se 4 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 851269 = 159613) (by norm_num)
theorem B425341 : Blo 334751 425341 := bbase (se 3 (by rfl) ⟨79751, by rfl⟩ : syracuseStep 425341 = 159503) (by norm_num)
theorem B359813 : Blo 334751 359813 := bbase (se 4 (by rfl) ⟨33732, by rfl⟩ : syracuseStep 359813 = 67465) (by norm_num)
theorem B851381 : Blo 334751 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B1080773 : Blo 334751 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B1703429 : Blo 334751 1703429 := bbase (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) (by norm_num)
theorem B425513 : Blo 334751 425513 := bbase (se 2 (by rfl) ⟨159567, by rfl⟩ : syracuseStep 425513 = 319135) (by norm_num)
theorem B360001 : Blo 334751 360001 := bbase (se 2 (by rfl) ⟨135000, by rfl⟩ : syracuseStep 360001 = 270001) (by norm_num)
theorem B753245 : Blo 334751 753245 := bbase (se 3 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 753245 = 282467) (by norm_num)
theorem B425569 : Blo 334751 425569 := bbase (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) (by norm_num)
theorem B1212005 : Blo 334751 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B851573 : Blo 334751 851573 := bbase (se 5 (by rfl) ⟨39917, by rfl⟩ : syracuseStep 851573 = 79835) (by norm_num)
theorem B753317 : Blo 334751 753317 := bbase (se 4 (by rfl) ⟨70623, by rfl⟩ : syracuseStep 753317 = 141247) (by norm_num)
theorem B425665 : Blo 334751 425665 := bbase (se 2 (by rfl) ⟨159624, by rfl⟩ : syracuseStep 425665 = 319249) (by norm_num)
theorem B753389 : Blo 334751 753389 := bbase (se 3 (by rfl) ⟨141260, by rfl⟩ : syracuseStep 753389 = 282521) (by norm_num)
theorem B720677 : Blo 334751 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B720685 : Blo 334751 720685 := bbase (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) (by norm_num)
theorem B753461 : Blo 334751 753461 := bbase (se 5 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 753461 = 70637) (by norm_num)
theorem B425837 : Blo 334751 425837 := bbase (se 3 (by rfl) ⟨79844, by rfl⟩ : syracuseStep 425837 = 159689) (by norm_num)
theorem B753533 : Blo 334751 753533 := bbase (se 3 (by rfl) ⟨141287, by rfl⟩ : syracuseStep 753533 = 282575) (by norm_num)
theorem B1212293 : Blo 334751 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B425893 : Blo 334751 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B753605 : Blo 334751 753605 := bbase (se 4 (by rfl) ⟨70650, by rfl⟩ : syracuseStep 753605 = 141301) (by norm_num)
theorem B851917 : Blo 334751 851917 := bbase (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) (by norm_num)
theorem B753713 : Blo 334751 753713 := bstep (se 2 (by rfl) ⟨282642, by rfl⟩ : syracuseStep 753713 = 565285) B565285
theorem B753731 : Blo 334751 753731 := bstep (se 1 (by rfl) ⟨565298, by rfl⟩ : syracuseStep 753731 = 1130597) B1130597
theorem B1704077 : Blo 334751 1704077 := bstep (se 3 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 1704077 = 639029) B639029
theorem B360659 : Blo 334751 360659 := bstep (se 1 (by rfl) ⟨270494, by rfl⟩ : syracuseStep 360659 = 540989) B540989
theorem B458995 : Blo 334751 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B852241 : Blo 334751 852241 := bstep (se 2 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 852241 = 639181) B639181
theorem B459059 : Blo 334751 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B754001 : Blo 334751 754001 := bstep (se 2 (by rfl) ⟨282750, by rfl⟩ : syracuseStep 754001 = 565501) B565501
theorem B426323 : Blo 334751 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B754019 : Blo 334751 754019 := bstep (se 1 (by rfl) ⟨565514, by rfl⟩ : syracuseStep 754019 = 1131029) B1131029
theorem B1442225 : Blo 334751 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B721361 : Blo 334751 721361 := bstep (se 2 (by rfl) ⟨270510, by rfl⟩ : syracuseStep 721361 = 541021) B541021
theorem B2163185 : Blo 334751 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B852515 : Blo 334751 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B754289 : Blo 334751 754289 := bstep (se 2 (by rfl) ⟨282858, by rfl⟩ : syracuseStep 754289 = 565717) B565717
theorem B754307 : Blo 334751 754307 := bstep (se 1 (by rfl) ⟨565730, by rfl⟩ : syracuseStep 754307 = 1131461) B1131461
theorem B1278605 : Blo 334751 1278605 := bstep (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) B479477
theorem B852707 : Blo 334751 852707 := bstep (se 1 (by rfl) ⟨639530, by rfl⟩ : syracuseStep 852707 = 1279061) B1279061
theorem B754577 : Blo 334751 754577 := bstep (se 2 (by rfl) ⟨282966, by rfl⟩ : syracuseStep 754577 = 565933) B565933
theorem B754595 : Blo 334751 754595 := bstep (se 1 (by rfl) ⟨565946, by rfl⟩ : syracuseStep 754595 = 1131893) B1131893
theorem B1082285 : Blo 334751 1082285 := bstep (se 3 (by rfl) ⟨202928, by rfl⟩ : syracuseStep 1082285 = 405857) B405857
theorem B427027 : Blo 334751 427027 := bstep (se 1 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 427027 = 640541) B640541
theorem B427123 : Blo 334751 427123 := bstep (se 1 (by rfl) ⟨320342, by rfl⟩ : syracuseStep 427123 = 640685) B640685
theorem B754865 : Blo 334751 754865 := bstep (se 2 (by rfl) ⟨283074, by rfl⟩ : syracuseStep 754865 = 566149) B566149
theorem B754883 : Blo 334751 754883 := bstep (se 1 (by rfl) ⟨566162, by rfl⟩ : syracuseStep 754883 = 1132325) B1132325
theorem B820433 : Blo 334751 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B11699653 : Blo 334751 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B755153 : Blo 334751 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B755171 : Blo 334751 755171 := bstep (se 1 (by rfl) ⟨566378, by rfl⟩ : syracuseStep 755171 = 1132757) B1132757
theorem B427619 : Blo 334751 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B853649 : Blo 334751 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B853699 : Blo 334751 853699 := bstep (se 1 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 853699 = 1280549) B1280549
theorem B755441 : Blo 334751 755441 := bstep (se 2 (by rfl) ⟨283290, by rfl⟩ : syracuseStep 755441 = 566581) B566581
theorem B755459 : Blo 334751 755459 := bstep (se 1 (by rfl) ⟨566594, by rfl⟩ : syracuseStep 755459 = 1133189) B1133189
theorem B5539637 : Blo 334751 5539637 := bstep (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) B519341
theorem B853841 : Blo 334751 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B755729 : Blo 334751 755729 := bstep (se 2 (by rfl) ⟨283398, by rfl⟩ : syracuseStep 755729 = 566797) B566797
theorem B755747 : Blo 334751 755747 := bstep (se 1 (by rfl) ⟨566810, by rfl⟩ : syracuseStep 755747 = 1133621) B1133621
theorem B723043 : Blo 334751 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B428323 : Blo 334751 428323 := bstep (se 1 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 428323 = 642485) B642485
theorem B756017 : Blo 334751 756017 := bstep (se 2 (by rfl) ⟨283506, by rfl⟩ : syracuseStep 756017 = 567013) B567013
theorem B756035 : Blo 334751 756035 := bstep (se 1 (by rfl) ⟨567026, by rfl⟩ : syracuseStep 756035 = 1134053) B1134053
theorem B428419 : Blo 334751 428419 := bstep (se 1 (by rfl) ⟨321314, by rfl⟩ : syracuseStep 428419 = 642629) B642629
theorem B2591117 : Blo 334751 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B756305 : Blo 334751 756305 := bstep (se 2 (by rfl) ⟨283614, by rfl⟩ : syracuseStep 756305 = 567229) B567229
theorem B756323 : Blo 334751 756323 := bstep (se 1 (by rfl) ⟨567242, by rfl⟩ : syracuseStep 756323 = 1134485) B1134485
theorem B821873 : Blo 334751 821873 := bstep (se 2 (by rfl) ⟨308202, by rfl⟩ : syracuseStep 821873 = 616405) B616405
theorem B1280717 : Blo 334751 1280717 := bstep (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) B480269
theorem B854833 : Blo 334751 854833 := bstep (se 2 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 854833 = 641125) B641125
theorem B2558789 : Blo 334751 2558789 := bstep (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) B479773
theorem B756593 : Blo 334751 756593 := bstep (se 2 (by rfl) ⟨283722, by rfl⟩ : syracuseStep 756593 = 567445) B567445
theorem B756611 : Blo 334751 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B691121 : Blo 334751 691121 := bstep (se 2 (by rfl) ⟨259170, by rfl⟩ : syracuseStep 691121 = 518341) B518341
theorem B1706993 : Blo 334751 1706993 := bstep (se 2 (by rfl) ⟨640122, by rfl⟩ : syracuseStep 1706993 = 1280245) B1280245
theorem B855107 : Blo 334751 855107 := bstep (se 1 (by rfl) ⟨641330, by rfl⟩ : syracuseStep 855107 = 1282661) B1282661
theorem B756881 : Blo 334751 756881 := bstep (se 2 (by rfl) ⟨283830, by rfl⟩ : syracuseStep 756881 = 567661) B567661
theorem B756899 : Blo 334751 756899 := bstep (se 1 (by rfl) ⟨567674, by rfl⟩ : syracuseStep 756899 = 1135349) B1135349
theorem B822449 : Blo 334751 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B2755781 : Blo 334751 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B855299 : Blo 334751 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B1445197 : Blo 334751 1445197 := bstep (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) B541949
theorem B757169 : Blo 334751 757169 := bstep (se 2 (by rfl) ⟨283938, by rfl⟩ : syracuseStep 757169 = 567877) B567877
theorem B953795 : Blo 334751 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B757187 : Blo 334751 757187 := bstep (se 1 (by rfl) ⟨567890, by rfl⟩ : syracuseStep 757187 = 1135781) B1135781
theorem B1281521 : Blo 334751 1281521 := bstep (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) B961141
theorem B3640945 : Blo 334751 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B1445539 : Blo 334751 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B757457 : Blo 334751 757457 := bstep (se 2 (by rfl) ⟨284046, by rfl⟩ : syracuseStep 757457 = 568093) B568093
theorem B757475 : Blo 334751 757475 := bstep (se 1 (by rfl) ⟨568106, by rfl⟩ : syracuseStep 757475 = 1136213) B1136213
theorem B954125 : Blo 334751 954125 := bstep (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) B357797
theorem B954193 : Blo 334751 954193 := bstep (se 2 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 954193 = 715645) B715645
theorem B1642403 : Blo 334751 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B757745 : Blo 334751 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B757763 : Blo 334751 757763 := bstep (se 1 (by rfl) ⟨568322, by rfl⟩ : syracuseStep 757763 = 1136645) B1136645
theorem B1380401 : Blo 334751 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B954467 : Blo 334751 954467 := bstep (se 1 (by rfl) ⟨715850, by rfl⟩ : syracuseStep 954467 = 1431701) B1431701
theorem B2297969 : Blo 334751 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B1282189 : Blo 334751 1282189 := bstep (se 3 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 1282189 = 480821) B480821
theorem B856241 : Blo 334751 856241 := bstep (se 2 (by rfl) ⟨321090, by rfl⟩ : syracuseStep 856241 = 642181) B642181
theorem B856291 : Blo 334751 856291 := bstep (se 1 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 856291 = 1284437) B1284437
theorem B758033 : Blo 334751 758033 := bstep (se 2 (by rfl) ⟨284262, by rfl⟩ : syracuseStep 758033 = 568525) B568525
theorem B758051 : Blo 334751 758051 := bstep (se 1 (by rfl) ⟨568538, by rfl⟩ : syracuseStep 758051 = 1137077) B1137077
theorem B856433 : Blo 334751 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B2167181 : Blo 334751 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B1708451 : Blo 334751 1708451 := bstep (se 1 (by rfl) ⟨1281338, by rfl⟩ : syracuseStep 1708451 = 2562677) B2562677
theorem B758321 : Blo 334751 758321 := bstep (se 2 (by rfl) ⟨284370, by rfl⟩ : syracuseStep 758321 = 568741) B568741
theorem B430643 : Blo 334751 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B758339 : Blo 334751 758339 := bstep (se 1 (by rfl) ⟨568754, by rfl⟩ : syracuseStep 758339 = 1137509) B1137509
theorem B365155 : Blo 334751 365155 := bstep (se 1 (by rfl) ⟨273866, by rfl⟩ : syracuseStep 365155 = 547733) B547733
theorem B2724677 : Blo 334751 2724677 := bstep (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) B510877
theorem B758609 : Blo 334751 758609 := bstep (se 2 (by rfl) ⟨284478, by rfl⟩ : syracuseStep 758609 = 568957) B568957
theorem B365395 : Blo 334751 365395 := bstep (se 1 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 365395 = 548093) B548093
theorem B758627 : Blo 334751 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B1282979 : Blo 334751 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B955309 : Blo 334751 955309 := bstep (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) B358241
theorem B955469 : Blo 334751 955469 := bstep (se 3 (by rfl) ⟨179150, by rfl⟩ : syracuseStep 955469 = 358301) B358301
theorem B758897 : Blo 334751 758897 := bstep (se 2 (by rfl) ⟨284586, by rfl⟩ : syracuseStep 758897 = 569173) B569173
theorem B758915 : Blo 334751 758915 := bstep (se 1 (by rfl) ⟨569186, by rfl⟩ : syracuseStep 758915 = 1138373) B1138373
theorem B1709261 : Blo 334751 1709261 := bstep (se 3 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 1709261 = 640973) B640973
theorem B365779 : Blo 334751 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B955651 : Blo 334751 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B922897 : Blo 334751 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B1611085 : Blo 334751 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B857425 : Blo 334751 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B759185 : Blo 334751 759185 := bstep (se 2 (by rfl) ⟨284694, by rfl⟩ : syracuseStep 759185 = 569389) B569389
theorem B759203 : Blo 334751 759203 := bstep (se 1 (by rfl) ⟨569402, by rfl⟩ : syracuseStep 759203 = 1138805) B1138805
theorem B1283633 : Blo 334751 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B759473 : Blo 334751 759473 := bstep (se 2 (by rfl) ⟨284802, by rfl⟩ : syracuseStep 759473 = 569605) B569605
theorem B759491 : Blo 334751 759491 := bstep (se 1 (by rfl) ⟨569618, by rfl⟩ : syracuseStep 759491 = 1139237) B1139237
theorem B431843 : Blo 334751 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B1611683 : Blo 334751 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B759761 : Blo 334751 759761 := bstep (se 2 (by rfl) ⟨284910, by rfl⟩ : syracuseStep 759761 = 569821) B569821
theorem B759779 : Blo 334751 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B760049 : Blo 334751 760049 := bstep (se 2 (by rfl) ⟨285018, by rfl⟩ : syracuseStep 760049 = 570037) B570037
theorem B760067 : Blo 334751 760067 := bstep (se 1 (by rfl) ⟨570050, by rfl⟩ : syracuseStep 760067 = 1140101) B1140101
theorem B2595185 : Blo 334751 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B760337 : Blo 334751 760337 := bstep (se 2 (by rfl) ⟨285126, by rfl⟩ : syracuseStep 760337 = 570253) B570253
theorem B760355 : Blo 334751 760355 := bstep (se 1 (by rfl) ⟨570266, by rfl⟩ : syracuseStep 760355 = 1140533) B1140533
theorem B2169413 : Blo 334751 2169413 := bstep (se 4 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 2169413 = 406765) B406765
theorem B957041 : Blo 334751 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B760625 : Blo 334751 760625 := bstep (se 2 (by rfl) ⟨285234, by rfl⟩ : syracuseStep 760625 = 570469) B570469
theorem B760643 : Blo 334751 760643 := bstep (se 1 (by rfl) ⟨570482, by rfl⟩ : syracuseStep 760643 = 1140965) B1140965
theorem B334755 : Blo 334751 334755 := bstep (se 1 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 334755 = 502133) B502133
theorem B2038691 : Blo 334751 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B334771 : Blo 334751 334771 := bstep (se 1 (by rfl) ⟨251078, by rfl⟩ : syracuseStep 334771 = 502157) B502157
theorem B334787 : Blo 334751 334787 := bstep (se 1 (by rfl) ⟨251090, by rfl⟩ : syracuseStep 334787 = 502181) B502181
theorem B334803 : Blo 334751 334803 := bstep (se 1 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 334803 = 502205) B502205
theorem B334819 : Blo 334751 334819 := bstep (se 1 (by rfl) ⟨251114, by rfl⟩ : syracuseStep 334819 = 502229) B502229
theorem B1285091 : Blo 334751 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B1285105 : Blo 334751 1285105 := bstep (se 2 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 1285105 = 963829) B963829
theorem B334835 : Blo 334751 334835 := bstep (se 1 (by rfl) ⟨251126, by rfl⟩ : syracuseStep 334835 = 502253) B502253
theorem B334851 : Blo 334751 334851 := bstep (se 1 (by rfl) ⟨251138, by rfl⟩ : syracuseStep 334851 = 502277) B502277
theorem B334867 : Blo 334751 334867 := bstep (se 1 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 334867 = 502301) B502301
theorem B334883 : Blo 334751 334883 := bstep (se 1 (by rfl) ⟨251162, by rfl⟩ : syracuseStep 334883 = 502325) B502325
theorem B334899 : Blo 334751 334899 := bstep (se 1 (by rfl) ⟨251174, by rfl⟩ : syracuseStep 334899 = 502349) B502349
theorem B334915 : Blo 334751 334915 := bstep (se 1 (by rfl) ⟨251186, by rfl⟩ : syracuseStep 334915 = 502373) B502373
theorem B760913 : Blo 334751 760913 := bstep (se 2 (by rfl) ⟨285342, by rfl⟩ : syracuseStep 760913 = 570685) B570685
theorem B334931 : Blo 334751 334931 := bstep (se 1 (by rfl) ⟨251198, by rfl⟩ : syracuseStep 334931 = 502397) B502397
theorem B334947 : Blo 334751 334947 := bstep (se 1 (by rfl) ⟨251210, by rfl⟩ : syracuseStep 334947 = 502421) B502421
theorem B760931 : Blo 334751 760931 := bstep (se 1 (by rfl) ⟨570698, by rfl⟩ : syracuseStep 760931 = 1141397) B1141397
theorem B334963 : Blo 334751 334963 := bstep (se 1 (by rfl) ⟨251222, by rfl⟩ : syracuseStep 334963 = 502445) B502445
theorem B334979 : Blo 334751 334979 := bstep (se 1 (by rfl) ⟨251234, by rfl⟩ : syracuseStep 334979 = 502469) B502469
theorem B334995 : Blo 334751 334995 := bstep (se 1 (by rfl) ⟨251246, by rfl⟩ : syracuseStep 334995 = 502493) B502493
theorem B335011 : Blo 334751 335011 := bstep (se 1 (by rfl) ⟨251258, by rfl⟩ : syracuseStep 335011 = 502517) B502517
theorem B335027 : Blo 334751 335027 := bstep (se 1 (by rfl) ⟨251270, by rfl⟩ : syracuseStep 335027 = 502541) B502541
theorem B335043 : Blo 334751 335043 := bstep (se 1 (by rfl) ⟨251282, by rfl⟩ : syracuseStep 335043 = 502565) B502565
theorem B335059 : Blo 334751 335059 := bstep (se 1 (by rfl) ⟨251294, by rfl⟩ : syracuseStep 335059 = 502589) B502589
theorem B335075 : Blo 334751 335075 := bstep (se 1 (by rfl) ⟨251306, by rfl⟩ : syracuseStep 335075 = 502613) B502613
theorem B335091 : Blo 334751 335091 := bstep (se 1 (by rfl) ⟨251318, by rfl⟩ : syracuseStep 335091 = 502637) B502637
theorem B335107 : Blo 334751 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B335123 : Blo 334751 335123 := bstep (se 1 (by rfl) ⟨251342, by rfl⟩ : syracuseStep 335123 = 502685) B502685
theorem B335139 : Blo 334751 335139 := bstep (se 1 (by rfl) ⟨251354, by rfl⟩ : syracuseStep 335139 = 502709) B502709
theorem B335155 : Blo 334751 335155 := bstep (se 1 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 335155 = 502733) B502733
theorem B335171 : Blo 334751 335171 := bstep (se 1 (by rfl) ⟨251378, by rfl⟩ : syracuseStep 335171 = 502757) B502757
theorem B335187 : Blo 334751 335187 := bstep (se 1 (by rfl) ⟨251390, by rfl⟩ : syracuseStep 335187 = 502781) B502781
theorem B335203 : Blo 334751 335203 := bstep (se 1 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 335203 = 502805) B502805
theorem B761201 : Blo 334751 761201 := bstep (se 2 (by rfl) ⟨285450, by rfl⟩ : syracuseStep 761201 = 570901) B570901
theorem B335219 : Blo 334751 335219 := bstep (se 1 (by rfl) ⟨251414, by rfl⟩ : syracuseStep 335219 = 502829) B502829
theorem B335235 : Blo 334751 335235 := bstep (se 1 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 335235 = 502853) B502853
theorem B761219 : Blo 334751 761219 := bstep (se 1 (by rfl) ⟨570914, by rfl⟩ : syracuseStep 761219 = 1141829) B1141829
theorem B335251 : Blo 334751 335251 := bstep (se 1 (by rfl) ⟨251438, by rfl⟩ : syracuseStep 335251 = 502877) B502877
theorem B335267 : Blo 334751 335267 := bstep (se 1 (by rfl) ⟨251450, by rfl⟩ : syracuseStep 335267 = 502901) B502901
theorem B1383857 : Blo 334751 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B335283 : Blo 334751 335283 := bstep (se 1 (by rfl) ⟨251462, by rfl⟩ : syracuseStep 335283 = 502925) B502925
theorem B335299 : Blo 334751 335299 := bstep (se 1 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 335299 = 502949) B502949
theorem B335315 : Blo 334751 335315 := bstep (se 1 (by rfl) ⟨251486, by rfl⟩ : syracuseStep 335315 = 502973) B502973
theorem B335331 : Blo 334751 335331 := bstep (se 1 (by rfl) ⟨251498, by rfl⟩ : syracuseStep 335331 = 502997) B502997
theorem B335347 : Blo 334751 335347 := bstep (se 1 (by rfl) ⟨251510, by rfl⟩ : syracuseStep 335347 = 503021) B503021
theorem B335363 : Blo 334751 335363 := bstep (se 1 (by rfl) ⟨251522, by rfl⟩ : syracuseStep 335363 = 503045) B503045
theorem B335379 : Blo 334751 335379 := bstep (se 1 (by rfl) ⟨251534, by rfl⟩ : syracuseStep 335379 = 503069) B503069
theorem B335395 : Blo 334751 335395 := bstep (se 1 (by rfl) ⟨251546, by rfl⟩ : syracuseStep 335395 = 503093) B503093
theorem B957997 : Blo 334751 957997 := bstep (se 3 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 957997 = 359249) B359249
theorem B335411 : Blo 334751 335411 := bstep (se 1 (by rfl) ⟨251558, by rfl⟩ : syracuseStep 335411 = 503117) B503117
theorem B335427 : Blo 334751 335427 := bstep (se 1 (by rfl) ⟨251570, by rfl⟩ : syracuseStep 335427 = 503141) B503141
theorem B335443 : Blo 334751 335443 := bstep (se 1 (by rfl) ⟨251582, by rfl⟩ : syracuseStep 335443 = 503165) B503165
theorem B335459 : Blo 334751 335459 := bstep (se 1 (by rfl) ⟨251594, by rfl⟩ : syracuseStep 335459 = 503189) B503189
theorem B335475 : Blo 334751 335475 := bstep (se 1 (by rfl) ⟨251606, by rfl⟩ : syracuseStep 335475 = 503213) B503213
theorem B335491 : Blo 334751 335491 := bstep (se 1 (by rfl) ⟨251618, by rfl⟩ : syracuseStep 335491 = 503237) B503237
theorem B761489 : Blo 334751 761489 := bstep (se 2 (by rfl) ⟨285558, by rfl⟩ : syracuseStep 761489 = 571117) B571117
theorem B335507 : Blo 334751 335507 := bstep (se 1 (by rfl) ⟨251630, by rfl⟩ : syracuseStep 335507 = 503261) B503261
theorem B335523 : Blo 334751 335523 := bstep (se 1 (by rfl) ⟨251642, by rfl⟩ : syracuseStep 335523 = 503285) B503285
theorem B761507 : Blo 334751 761507 := bstep (se 1 (by rfl) ⟨571130, by rfl⟩ : syracuseStep 761507 = 1142261) B1142261
theorem B335539 : Blo 334751 335539 := bstep (se 1 (by rfl) ⟨251654, by rfl⟩ : syracuseStep 335539 = 503309) B503309
theorem B335555 : Blo 334751 335555 := bstep (se 1 (by rfl) ⟨251666, by rfl⟩ : syracuseStep 335555 = 503333) B503333
theorem B335571 : Blo 334751 335571 := bstep (se 1 (by rfl) ⟨251678, by rfl⟩ : syracuseStep 335571 = 503357) B503357
theorem B564961 : Blo 334751 564961 := bstep (se 2 (by rfl) ⟨211860, by rfl⟩ : syracuseStep 564961 = 423721) B423721
theorem B335587 : Blo 334751 335587 := bstep (se 1 (by rfl) ⟨251690, by rfl⟩ : syracuseStep 335587 = 503381) B503381
theorem B335603 : Blo 334751 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B564995 : Blo 334751 564995 := bstep (se 1 (by rfl) ⟨423746, by rfl⟩ : syracuseStep 564995 = 847493) B847493
theorem B335619 : Blo 334751 335619 := bstep (se 1 (by rfl) ⟨251714, by rfl⟩ : syracuseStep 335619 = 503429) B503429
theorem B958225 : Blo 334751 958225 := bstep (se 2 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 958225 = 718669) B718669
theorem B335635 : Blo 334751 335635 := bstep (se 1 (by rfl) ⟨251726, by rfl⟩ : syracuseStep 335635 = 503453) B503453
theorem B335651 : Blo 334751 335651 := bstep (se 1 (by rfl) ⟨251738, by rfl⟩ : syracuseStep 335651 = 503477) B503477
theorem B335667 : Blo 334751 335667 := bstep (se 1 (by rfl) ⟨251750, by rfl⟩ : syracuseStep 335667 = 503501) B503501
theorem B335683 : Blo 334751 335683 := bstep (se 1 (by rfl) ⟨251762, by rfl⟩ : syracuseStep 335683 = 503525) B503525
theorem B335699 : Blo 334751 335699 := bstep (se 1 (by rfl) ⟨251774, by rfl⟩ : syracuseStep 335699 = 503549) B503549
theorem B335715 : Blo 334751 335715 := bstep (se 1 (by rfl) ⟨251786, by rfl⟩ : syracuseStep 335715 = 503573) B503573
theorem B335731 : Blo 334751 335731 := bstep (se 1 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 335731 = 503597) B503597
theorem B565123 : Blo 334751 565123 := bstep (se 1 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 565123 = 847685) B847685
theorem B335747 : Blo 334751 335747 := bstep (se 1 (by rfl) ⟨251810, by rfl⟩ : syracuseStep 335747 = 503621) B503621
theorem B335763 : Blo 334751 335763 := bstep (se 1 (by rfl) ⟨251822, by rfl⟩ : syracuseStep 335763 = 503645) B503645
theorem B335779 : Blo 334751 335779 := bstep (se 1 (by rfl) ⟨251834, by rfl⟩ : syracuseStep 335779 = 503669) B503669
theorem B958385 : Blo 334751 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B761777 : Blo 334751 761777 := bstep (se 2 (by rfl) ⟨285666, by rfl⟩ : syracuseStep 761777 = 571333) B571333
theorem B335795 : Blo 334751 335795 := bstep (se 1 (by rfl) ⟨251846, by rfl⟩ : syracuseStep 335795 = 503693) B503693
theorem B335811 : Blo 334751 335811 := bstep (se 1 (by rfl) ⟨251858, by rfl⟩ : syracuseStep 335811 = 503717) B503717
theorem B761795 : Blo 334751 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B335827 : Blo 334751 335827 := bstep (se 1 (by rfl) ⟨251870, by rfl⟩ : syracuseStep 335827 = 503741) B503741
theorem B335843 : Blo 334751 335843 := bstep (se 1 (by rfl) ⟨251882, by rfl⟩ : syracuseStep 335843 = 503765) B503765
theorem B335859 : Blo 334751 335859 := bstep (se 1 (by rfl) ⟨251894, by rfl⟩ : syracuseStep 335859 = 503789) B503789
theorem B335875 : Blo 334751 335875 := bstep (se 1 (by rfl) ⟨251906, by rfl⟩ : syracuseStep 335875 = 503813) B503813
theorem B565265 : Blo 334751 565265 := bstep (se 2 (by rfl) ⟨211974, by rfl⟩ : syracuseStep 565265 = 423949) B423949
theorem B335891 : Blo 334751 335891 := bstep (se 1 (by rfl) ⟨251918, by rfl⟩ : syracuseStep 335891 = 503837) B503837
theorem B335907 : Blo 334751 335907 := bstep (se 1 (by rfl) ⟨251930, by rfl⟩ : syracuseStep 335907 = 503861) B503861
theorem B958499 : Blo 334751 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B1712177 : Blo 334751 1712177 := bstep (se 2 (by rfl) ⟨642066, by rfl⟩ : syracuseStep 1712177 = 1284133) B1284133
theorem B335923 : Blo 334751 335923 := bstep (se 1 (by rfl) ⟨251942, by rfl⟩ : syracuseStep 335923 = 503885) B503885
theorem B335939 : Blo 334751 335939 := bstep (se 1 (by rfl) ⟨251954, by rfl⟩ : syracuseStep 335939 = 503909) B503909
theorem B368707 : Blo 334751 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B335955 : Blo 334751 335955 := bstep (se 1 (by rfl) ⟨251966, by rfl⟩ : syracuseStep 335955 = 503933) B503933
theorem B335971 : Blo 334751 335971 := bstep (se 1 (by rfl) ⟨251978, by rfl⟩ : syracuseStep 335971 = 503957) B503957
theorem B335987 : Blo 334751 335987 := bstep (se 1 (by rfl) ⟨251990, by rfl⟩ : syracuseStep 335987 = 503981) B503981
theorem B336003 : Blo 334751 336003 := bstep (se 1 (by rfl) ⟨252002, by rfl⟩ : syracuseStep 336003 = 504005) B504005
theorem B565393 : Blo 334751 565393 := bstep (se 2 (by rfl) ⟨212022, by rfl⟩ : syracuseStep 565393 = 424045) B424045
theorem B336019 : Blo 334751 336019 := bstep (se 1 (by rfl) ⟨252014, by rfl⟩ : syracuseStep 336019 = 504029) B504029
theorem B336035 : Blo 334751 336035 := bstep (se 1 (by rfl) ⟨252026, by rfl⟩ : syracuseStep 336035 = 504053) B504053
theorem B1220771 : Blo 334751 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B565427 : Blo 334751 565427 := bstep (se 1 (by rfl) ⟨424070, by rfl⟩ : syracuseStep 565427 = 848141) B848141
theorem B336051 : Blo 334751 336051 := bstep (se 1 (by rfl) ⟨252038, by rfl⟩ : syracuseStep 336051 = 504077) B504077
theorem B336067 : Blo 334751 336067 := bstep (se 1 (by rfl) ⟨252050, by rfl⟩ : syracuseStep 336067 = 504101) B504101
theorem B762065 : Blo 334751 762065 := bstep (se 2 (by rfl) ⟨285774, by rfl⟩ : syracuseStep 762065 = 571549) B571549
theorem B336083 : Blo 334751 336083 := bstep (se 1 (by rfl) ⟨252062, by rfl⟩ : syracuseStep 336083 = 504125) B504125
theorem B336099 : Blo 334751 336099 := bstep (se 1 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 336099 = 504149) B504149
theorem B762083 : Blo 334751 762083 := bstep (se 1 (by rfl) ⟨571562, by rfl⟩ : syracuseStep 762083 = 1143125) B1143125
theorem B336115 : Blo 334751 336115 := bstep (se 1 (by rfl) ⟨252086, by rfl⟩ : syracuseStep 336115 = 504173) B504173
theorem B336131 : Blo 334751 336131 := bstep (se 1 (by rfl) ⟨252098, by rfl⟩ : syracuseStep 336131 = 504197) B504197
theorem B729361 : Blo 334751 729361 := bstep (se 2 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 729361 = 547021) B547021
theorem B336147 : Blo 334751 336147 := bstep (se 1 (by rfl) ⟨252110, by rfl⟩ : syracuseStep 336147 = 504221) B504221
theorem B336163 : Blo 334751 336163 := bstep (se 1 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 336163 = 504245) B504245
theorem B565555 : Blo 334751 565555 := bstep (se 1 (by rfl) ⟨424166, by rfl⟩ : syracuseStep 565555 = 848333) B848333
theorem B336179 : Blo 334751 336179 := bstep (se 1 (by rfl) ⟨252134, by rfl⟩ : syracuseStep 336179 = 504269) B504269
theorem B336195 : Blo 334751 336195 := bstep (se 1 (by rfl) ⟨252146, by rfl⟩ : syracuseStep 336195 = 504293) B504293
theorem B336211 : Blo 334751 336211 := bstep (se 1 (by rfl) ⟨252158, by rfl⟩ : syracuseStep 336211 = 504317) B504317
theorem B336227 : Blo 334751 336227 := bstep (se 1 (by rfl) ⟨252170, by rfl⟩ : syracuseStep 336227 = 504341) B504341
theorem B336243 : Blo 334751 336243 := bstep (se 1 (by rfl) ⟨252182, by rfl⟩ : syracuseStep 336243 = 504365) B504365
theorem B336259 : Blo 334751 336259 := bstep (se 1 (by rfl) ⟨252194, by rfl⟩ : syracuseStep 336259 = 504389) B504389
theorem B1810829 : Blo 334751 1810829 := bstep (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) B679061
theorem B336275 : Blo 334751 336275 := bstep (se 1 (by rfl) ⟨252206, by rfl⟩ : syracuseStep 336275 = 504413) B504413
theorem B336291 : Blo 334751 336291 := bstep (se 1 (by rfl) ⟨252218, by rfl⟩ : syracuseStep 336291 = 504437) B504437
theorem B336307 : Blo 334751 336307 := bstep (se 1 (by rfl) ⟨252230, by rfl⟩ : syracuseStep 336307 = 504461) B504461
theorem B565697 : Blo 334751 565697 := bstep (se 2 (by rfl) ⟨212136, by rfl⟩ : syracuseStep 565697 = 424273) B424273
theorem B336323 : Blo 334751 336323 := bstep (se 1 (by rfl) ⟨252242, by rfl⟩ : syracuseStep 336323 = 504485) B504485
theorem B336339 : Blo 334751 336339 := bstep (se 1 (by rfl) ⟨252254, by rfl⟩ : syracuseStep 336339 = 504509) B504509
theorem B336355 : Blo 334751 336355 := bstep (se 1 (by rfl) ⟨252266, by rfl⟩ : syracuseStep 336355 = 504533) B504533
theorem B336371 : Blo 334751 336371 := bstep (se 1 (by rfl) ⟨252278, by rfl⟩ : syracuseStep 336371 = 504557) B504557
theorem B336387 : Blo 334751 336387 := bstep (se 1 (by rfl) ⟨252290, by rfl⟩ : syracuseStep 336387 = 504581) B504581
theorem B2564621 : Blo 334751 2564621 := bstep (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) B961733
theorem B336403 : Blo 334751 336403 := bstep (se 1 (by rfl) ⟨252302, by rfl⟩ : syracuseStep 336403 = 504605) B504605
theorem B336419 : Blo 334751 336419 := bstep (se 1 (by rfl) ⟨252314, by rfl⟩ : syracuseStep 336419 = 504629) B504629
theorem B336435 : Blo 334751 336435 := bstep (se 1 (by rfl) ⟨252326, by rfl⟩ : syracuseStep 336435 = 504653) B504653
theorem B565825 : Blo 334751 565825 := bstep (se 2 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 565825 = 424369) B424369
theorem B336451 : Blo 334751 336451 := bstep (se 1 (by rfl) ⟨252338, by rfl⟩ : syracuseStep 336451 = 504677) B504677
theorem B336467 : Blo 334751 336467 := bstep (se 1 (by rfl) ⟨252350, by rfl⟩ : syracuseStep 336467 = 504701) B504701
theorem B565859 : Blo 334751 565859 := bstep (se 1 (by rfl) ⟨424394, by rfl⟩ : syracuseStep 565859 = 848789) B848789
theorem B336483 : Blo 334751 336483 := bstep (se 1 (by rfl) ⟨252362, by rfl⟩ : syracuseStep 336483 = 504725) B504725
theorem B336499 : Blo 334751 336499 := bstep (se 1 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 336499 = 504749) B504749
theorem B336515 : Blo 334751 336515 := bstep (se 1 (by rfl) ⟨252386, by rfl⟩ : syracuseStep 336515 = 504773) B504773
theorem B1548941 : Blo 334751 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B7250573 : Blo 334751 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B336531 : Blo 334751 336531 := bstep (se 1 (by rfl) ⟨252398, by rfl⟩ : syracuseStep 336531 = 504797) B504797
theorem B336547 : Blo 334751 336547 := bstep (se 1 (by rfl) ⟨252410, by rfl⟩ : syracuseStep 336547 = 504821) B504821
theorem B336563 : Blo 334751 336563 := bstep (se 1 (by rfl) ⟨252422, by rfl⟩ : syracuseStep 336563 = 504845) B504845
theorem B336579 : Blo 334751 336579 := bstep (se 1 (by rfl) ⟨252434, by rfl⟩ : syracuseStep 336579 = 504869) B504869
theorem B336595 : Blo 334751 336595 := bstep (se 1 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 336595 = 504893) B504893
theorem B565987 : Blo 334751 565987 := bstep (se 1 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 565987 = 848981) B848981
theorem B336611 : Blo 334751 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B336627 : Blo 334751 336627 := bstep (se 1 (by rfl) ⟨252470, by rfl⟩ : syracuseStep 336627 = 504941) B504941
theorem B336643 : Blo 334751 336643 := bstep (se 1 (by rfl) ⟨252482, by rfl⟩ : syracuseStep 336643 = 504965) B504965
theorem B336659 : Blo 334751 336659 := bstep (se 1 (by rfl) ⟨252494, by rfl⟩ : syracuseStep 336659 = 504989) B504989
theorem B336675 : Blo 334751 336675 := bstep (se 1 (by rfl) ⟨252506, by rfl⟩ : syracuseStep 336675 = 505013) B505013
theorem B336691 : Blo 334751 336691 := bstep (se 1 (by rfl) ⟨252518, by rfl⟩ : syracuseStep 336691 = 505037) B505037
theorem B336707 : Blo 334751 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B1844045 : Blo 334751 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B336723 : Blo 334751 336723 := bstep (se 1 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 336723 = 505085) B505085
theorem B336739 : Blo 334751 336739 := bstep (se 1 (by rfl) ⟨252554, by rfl⟩ : syracuseStep 336739 = 505109) B505109
theorem B566129 : Blo 334751 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B336755 : Blo 334751 336755 := bstep (se 1 (by rfl) ⟨252566, by rfl⟩ : syracuseStep 336755 = 505133) B505133
theorem B336771 : Blo 334751 336771 := bstep (se 1 (by rfl) ⟨252578, by rfl⟩ : syracuseStep 336771 = 505157) B505157
theorem B336787 : Blo 334751 336787 := bstep (se 1 (by rfl) ⟨252590, by rfl⟩ : syracuseStep 336787 = 505181) B505181
theorem B336803 : Blo 334751 336803 := bstep (se 1 (by rfl) ⟨252602, by rfl⟩ : syracuseStep 336803 = 505205) B505205
theorem B336819 : Blo 334751 336819 := bstep (se 1 (by rfl) ⟨252614, by rfl⟩ : syracuseStep 336819 = 505229) B505229
theorem B336835 : Blo 334751 336835 := bstep (se 1 (by rfl) ⟨252626, by rfl⟩ : syracuseStep 336835 = 505253) B505253
theorem B336851 : Blo 334751 336851 := bstep (se 1 (by rfl) ⟨252638, by rfl⟩ : syracuseStep 336851 = 505277) B505277
theorem B336867 : Blo 334751 336867 := bstep (se 1 (by rfl) ⟨252650, by rfl⟩ : syracuseStep 336867 = 505301) B505301
theorem B566257 : Blo 334751 566257 := bstep (se 2 (by rfl) ⟨212346, by rfl⟩ : syracuseStep 566257 = 424693) B424693
theorem B336883 : Blo 334751 336883 := bstep (se 1 (by rfl) ⟨252662, by rfl⟩ : syracuseStep 336883 = 505325) B505325
theorem B336899 : Blo 334751 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B959501 : Blo 334751 959501 := bstep (se 3 (by rfl) ⟨179906, by rfl⟩ : syracuseStep 959501 = 359813) B359813
theorem B566291 : Blo 334751 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B336915 : Blo 334751 336915 := bstep (se 1 (by rfl) ⟨252686, by rfl⟩ : syracuseStep 336915 = 505373) B505373
theorem B336931 : Blo 334751 336931 := bstep (se 1 (by rfl) ⟨252698, by rfl⟩ : syracuseStep 336931 = 505397) B505397
theorem B2040881 : Blo 334751 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B336947 : Blo 334751 336947 := bstep (se 1 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 336947 = 505421) B505421
theorem B4138037 : Blo 334751 4138037 := bstep (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) B387941
theorem B336963 : Blo 334751 336963 := bstep (se 1 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 336963 = 505445) B505445
theorem B336979 : Blo 334751 336979 := bstep (se 1 (by rfl) ⟨252734, by rfl⟩ : syracuseStep 336979 = 505469) B505469
theorem B336995 : Blo 334751 336995 := bstep (se 1 (by rfl) ⟨252746, by rfl⟩ : syracuseStep 336995 = 505493) B505493
theorem B337011 : Blo 334751 337011 := bstep (se 1 (by rfl) ⟨252758, by rfl⟩ : syracuseStep 337011 = 505517) B505517
theorem B337027 : Blo 334751 337027 := bstep (se 1 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 337027 = 505541) B505541
theorem B566419 : Blo 334751 566419 := bstep (se 1 (by rfl) ⟨424814, by rfl⟩ : syracuseStep 566419 = 849629) B849629
theorem B337043 : Blo 334751 337043 := bstep (se 1 (by rfl) ⟨252782, by rfl⟩ : syracuseStep 337043 = 505565) B505565
theorem B337059 : Blo 334751 337059 := bstep (se 1 (by rfl) ⟨252794, by rfl⟩ : syracuseStep 337059 = 505589) B505589
theorem B337075 : Blo 334751 337075 := bstep (se 1 (by rfl) ⟨252806, by rfl⟩ : syracuseStep 337075 = 505613) B505613
theorem B959683 : Blo 334751 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B337091 : Blo 334751 337091 := bstep (se 1 (by rfl) ⟨252818, by rfl⟩ : syracuseStep 337091 = 505637) B505637
theorem B337107 : Blo 334751 337107 := bstep (se 1 (by rfl) ⟨252830, by rfl⟩ : syracuseStep 337107 = 505661) B505661
theorem B337123 : Blo 334751 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B337139 : Blo 334751 337139 := bstep (se 1 (by rfl) ⟨252854, by rfl⟩ : syracuseStep 337139 = 505709) B505709
theorem B337155 : Blo 334751 337155 := bstep (se 1 (by rfl) ⟨252866, by rfl⟩ : syracuseStep 337155 = 505733) B505733
theorem B337171 : Blo 334751 337171 := bstep (se 1 (by rfl) ⟨252878, by rfl⟩ : syracuseStep 337171 = 505757) B505757
theorem B566561 : Blo 334751 566561 := bstep (se 2 (by rfl) ⟨212460, by rfl⟩ : syracuseStep 566561 = 424921) B424921
theorem B337187 : Blo 334751 337187 := bstep (se 1 (by rfl) ⟨252890, by rfl⟩ : syracuseStep 337187 = 505781) B505781
theorem B337203 : Blo 334751 337203 := bstep (se 1 (by rfl) ⟨252902, by rfl⟩ : syracuseStep 337203 = 505805) B505805
theorem B337219 : Blo 334751 337219 := bstep (se 1 (by rfl) ⟨252914, by rfl⟩ : syracuseStep 337219 = 505829) B505829
theorem B337235 : Blo 334751 337235 := bstep (se 1 (by rfl) ⟨252926, by rfl⟩ : syracuseStep 337235 = 505853) B505853
theorem B959843 : Blo 334751 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B337251 : Blo 334751 337251 := bstep (se 1 (by rfl) ⟨252938, by rfl⟩ : syracuseStep 337251 = 505877) B505877
theorem B337267 : Blo 334751 337267 := bstep (se 1 (by rfl) ⟨252950, by rfl⟩ : syracuseStep 337267 = 505901) B505901
theorem B337283 : Blo 334751 337283 := bstep (se 1 (by rfl) ⟨252962, by rfl⟩ : syracuseStep 337283 = 505925) B505925
theorem B337299 : Blo 334751 337299 := bstep (se 1 (by rfl) ⟨252974, by rfl⟩ : syracuseStep 337299 = 505949) B505949
theorem B566689 : Blo 334751 566689 := bstep (se 2 (by rfl) ⟨212508, by rfl⟩ : syracuseStep 566689 = 425017) B425017
theorem B337315 : Blo 334751 337315 := bstep (se 1 (by rfl) ⟨252986, by rfl⟩ : syracuseStep 337315 = 505973) B505973
theorem B1025453 : Blo 334751 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B337331 : Blo 334751 337331 := bstep (se 1 (by rfl) ⟨252998, by rfl⟩ : syracuseStep 337331 = 505997) B505997
theorem B566723 : Blo 334751 566723 := bstep (se 1 (by rfl) ⟨425042, by rfl⟩ : syracuseStep 566723 = 850085) B850085
theorem B337347 : Blo 334751 337347 := bstep (se 1 (by rfl) ⟨253010, by rfl⟩ : syracuseStep 337347 = 506021) B506021
theorem B337363 : Blo 334751 337363 := bstep (se 1 (by rfl) ⟨253022, by rfl⟩ : syracuseStep 337363 = 506045) B506045
theorem B337379 : Blo 334751 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B1713635 : Blo 334751 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B1156589 : Blo 334751 1156589 := bstep (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) B433721
theorem B337395 : Blo 334751 337395 := bstep (se 1 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 337395 = 506093) B506093
theorem B337411 : Blo 334751 337411 := bstep (se 1 (by rfl) ⟨253058, by rfl⟩ : syracuseStep 337411 = 506117) B506117
theorem B1615373 : Blo 334751 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B337427 : Blo 334751 337427 := bstep (se 1 (by rfl) ⟨253070, by rfl⟩ : syracuseStep 337427 = 506141) B506141
theorem B337443 : Blo 334751 337443 := bstep (se 1 (by rfl) ⟨253082, by rfl⟩ : syracuseStep 337443 = 506165) B506165
theorem B337459 : Blo 334751 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B566851 : Blo 334751 566851 := bstep (se 1 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 566851 = 850277) B850277
theorem B337475 : Blo 334751 337475 := bstep (se 1 (by rfl) ⟨253106, by rfl⟩ : syracuseStep 337475 = 506213) B506213
theorem B337491 : Blo 334751 337491 := bstep (se 1 (by rfl) ⟨253118, by rfl⟩ : syracuseStep 337491 = 506237) B506237
theorem B337507 : Blo 334751 337507 := bstep (se 1 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 337507 = 506261) B506261
theorem B337523 : Blo 334751 337523 := bstep (se 1 (by rfl) ⟨253142, by rfl⟩ : syracuseStep 337523 = 506285) B506285
theorem B337539 : Blo 334751 337539 := bstep (se 1 (by rfl) ⟨253154, by rfl⟩ : syracuseStep 337539 = 506309) B506309
theorem B6006413 : Blo 334751 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B337555 : Blo 334751 337555 := bstep (se 1 (by rfl) ⟨253166, by rfl⟩ : syracuseStep 337555 = 506333) B506333
theorem B337571 : Blo 334751 337571 := bstep (se 1 (by rfl) ⟨253178, by rfl⟩ : syracuseStep 337571 = 506357) B506357
theorem B337587 : Blo 334751 337587 := bstep (se 1 (by rfl) ⟨253190, by rfl⟩ : syracuseStep 337587 = 506381) B506381
theorem B337603 : Blo 334751 337603 := bstep (se 1 (by rfl) ⟨253202, by rfl⟩ : syracuseStep 337603 = 506405) B506405
theorem B566993 : Blo 334751 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B337619 : Blo 334751 337619 := bstep (se 1 (by rfl) ⟨253214, by rfl⟩ : syracuseStep 337619 = 506429) B506429
theorem B337635 : Blo 334751 337635 := bstep (se 1 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 337635 = 506453) B506453
theorem B337651 : Blo 334751 337651 := bstep (se 1 (by rfl) ⟨253238, by rfl⟩ : syracuseStep 337651 = 506477) B506477
theorem B337667 : Blo 334751 337667 := bstep (se 1 (by rfl) ⟨253250, by rfl⟩ : syracuseStep 337667 = 506501) B506501
theorem B337683 : Blo 334751 337683 := bstep (se 1 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 337683 = 506525) B506525
theorem B337699 : Blo 334751 337699 := bstep (se 1 (by rfl) ⟨253274, by rfl⟩ : syracuseStep 337699 = 506549) B506549
theorem B337715 : Blo 334751 337715 := bstep (se 1 (by rfl) ⟨253286, by rfl⟩ : syracuseStep 337715 = 506573) B506573
theorem B337731 : Blo 334751 337731 := bstep (se 1 (by rfl) ⟨253298, by rfl⟩ : syracuseStep 337731 = 506597) B506597
theorem B894797 : Blo 334751 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B567121 : Blo 334751 567121 := bstep (se 2 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 567121 = 425341) B425341
theorem B337747 : Blo 334751 337747 := bstep (se 1 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 337747 = 506621) B506621
theorem B337763 : Blo 334751 337763 := bstep (se 1 (by rfl) ⟨253322, by rfl⟩ : syracuseStep 337763 = 506645) B506645
theorem B567155 : Blo 334751 567155 := bstep (se 1 (by rfl) ⟨425366, by rfl⟩ : syracuseStep 567155 = 850733) B850733
theorem B337779 : Blo 334751 337779 := bstep (se 1 (by rfl) ⟨253334, by rfl⟩ : syracuseStep 337779 = 506669) B506669
theorem B337795 : Blo 334751 337795 := bstep (se 1 (by rfl) ⟨253346, by rfl⟩ : syracuseStep 337795 = 506693) B506693
theorem B337811 : Blo 334751 337811 := bstep (se 1 (by rfl) ⟨253358, by rfl⟩ : syracuseStep 337811 = 506717) B506717
theorem B337827 : Blo 334751 337827 := bstep (se 1 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 337827 = 506741) B506741
theorem B337843 : Blo 334751 337843 := bstep (se 1 (by rfl) ⟨253382, by rfl⟩ : syracuseStep 337843 = 506765) B506765
theorem B337859 : Blo 334751 337859 := bstep (se 1 (by rfl) ⟨253394, by rfl⟩ : syracuseStep 337859 = 506789) B506789
theorem B337875 : Blo 334751 337875 := bstep (se 1 (by rfl) ⟨253406, by rfl⟩ : syracuseStep 337875 = 506813) B506813
theorem B337891 : Blo 334751 337891 := bstep (se 1 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 337891 = 506837) B506837
theorem B567283 : Blo 334751 567283 := bstep (se 1 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 567283 = 850925) B850925
theorem B337907 : Blo 334751 337907 := bstep (se 1 (by rfl) ⟨253430, by rfl⟩ : syracuseStep 337907 = 506861) B506861
theorem B337923 : Blo 334751 337923 := bstep (se 1 (by rfl) ⟨253442, by rfl⟩ : syracuseStep 337923 = 506885) B506885
theorem B337939 : Blo 334751 337939 := bstep (se 1 (by rfl) ⟨253454, by rfl⟩ : syracuseStep 337939 = 506909) B506909
theorem B337955 : Blo 334751 337955 := bstep (se 1 (by rfl) ⟨253466, by rfl⟩ : syracuseStep 337955 = 506933) B506933
theorem B337971 : Blo 334751 337971 := bstep (se 1 (by rfl) ⟨253478, by rfl⟩ : syracuseStep 337971 = 506957) B506957
theorem B337987 : Blo 334751 337987 := bstep (se 1 (by rfl) ⟨253490, by rfl⟩ : syracuseStep 337987 = 506981) B506981
theorem B338003 : Blo 334751 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B338019 : Blo 334751 338019 := bstep (se 1 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 338019 = 507029) B507029
theorem B338035 : Blo 334751 338035 := bstep (se 1 (by rfl) ⟨253526, by rfl⟩ : syracuseStep 338035 = 507053) B507053
theorem B567425 : Blo 334751 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B338051 : Blo 334751 338051 := bstep (se 1 (by rfl) ⟨253538, by rfl⟩ : syracuseStep 338051 = 507077) B507077
theorem B338067 : Blo 334751 338067 := bstep (se 1 (by rfl) ⟨253550, by rfl⟩ : syracuseStep 338067 = 507101) B507101
theorem B338083 : Blo 334751 338083 := bstep (se 1 (by rfl) ⟨253562, by rfl⟩ : syracuseStep 338083 = 507125) B507125
theorem B338099 : Blo 334751 338099 := bstep (se 1 (by rfl) ⟨253574, by rfl⟩ : syracuseStep 338099 = 507149) B507149
theorem B338115 : Blo 334751 338115 := bstep (se 1 (by rfl) ⟨253586, by rfl⟩ : syracuseStep 338115 = 507173) B507173
theorem B7317701 : Blo 334751 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B338131 : Blo 334751 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B338147 : Blo 334751 338147 := bstep (se 1 (by rfl) ⟨253610, by rfl⟩ : syracuseStep 338147 = 507221) B507221
theorem B338163 : Blo 334751 338163 := bstep (se 1 (by rfl) ⟨253622, by rfl⟩ : syracuseStep 338163 = 507245) B507245
theorem B567553 : Blo 334751 567553 := bstep (se 2 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 567553 = 425665) B425665
theorem B338179 : Blo 334751 338179 := bstep (se 1 (by rfl) ⟨253634, by rfl⟩ : syracuseStep 338179 = 507269) B507269
theorem B1714445 : Blo 334751 1714445 := bstep (se 3 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 1714445 = 642917) B642917
theorem B338195 : Blo 334751 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B567587 : Blo 334751 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B338211 : Blo 334751 338211 := bstep (se 1 (by rfl) ⟨253658, by rfl⟩ : syracuseStep 338211 = 507317) B507317
theorem B1026353 : Blo 334751 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B338227 : Blo 334751 338227 := bstep (se 1 (by rfl) ⟨253670, by rfl⟩ : syracuseStep 338227 = 507341) B507341
theorem B338243 : Blo 334751 338243 := bstep (se 1 (by rfl) ⟨253682, by rfl⟩ : syracuseStep 338243 = 507365) B507365
theorem B338259 : Blo 334751 338259 := bstep (se 1 (by rfl) ⟨253694, by rfl⟩ : syracuseStep 338259 = 507389) B507389
theorem B338275 : Blo 334751 338275 := bstep (se 1 (by rfl) ⟨253706, by rfl⟩ : syracuseStep 338275 = 507413) B507413
theorem B338291 : Blo 334751 338291 := bstep (se 1 (by rfl) ⟨253718, by rfl⟩ : syracuseStep 338291 = 507437) B507437
theorem B502145 : Blo 334751 502145 := bstep (se 2 (by rfl) ⟨188304, by rfl⟩ : syracuseStep 502145 = 376609) B376609
theorem B338307 : Blo 334751 338307 := bstep (se 1 (by rfl) ⟨253730, by rfl⟩ : syracuseStep 338307 = 507461) B507461
theorem B960913 : Blo 334751 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B502163 : Blo 334751 502163 := bstep (se 1 (by rfl) ⟨376622, by rfl⟩ : syracuseStep 502163 = 753245) B753245
theorem B338323 : Blo 334751 338323 := bstep (se 1 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 338323 = 507485) B507485
theorem B567715 : Blo 334751 567715 := bstep (se 1 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 567715 = 851573) B851573
theorem B338339 : Blo 334751 338339 := bstep (se 1 (by rfl) ⟨253754, by rfl⟩ : syracuseStep 338339 = 507509) B507509
theorem B502193 : Blo 334751 502193 := bstep (se 2 (by rfl) ⟨188322, by rfl⟩ : syracuseStep 502193 = 376645) B376645
theorem B338355 : Blo 334751 338355 := bstep (se 1 (by rfl) ⟨253766, by rfl⟩ : syracuseStep 338355 = 507533) B507533
theorem B502211 : Blo 334751 502211 := bstep (se 1 (by rfl) ⟨376658, by rfl⟩ : syracuseStep 502211 = 753317) B753317
theorem B338371 : Blo 334751 338371 := bstep (se 1 (by rfl) ⟨253778, by rfl⟩ : syracuseStep 338371 = 507557) B507557
theorem B338387 : Blo 334751 338387 := bstep (se 1 (by rfl) ⟨253790, by rfl⟩ : syracuseStep 338387 = 507581) B507581
theorem B502241 : Blo 334751 502241 := bstep (se 2 (by rfl) ⟨188340, by rfl⟩ : syracuseStep 502241 = 376681) B376681
theorem B338403 : Blo 334751 338403 := bstep (se 1 (by rfl) ⟨253802, by rfl⟩ : syracuseStep 338403 = 507605) B507605
theorem B502259 : Blo 334751 502259 := bstep (se 1 (by rfl) ⟨376694, by rfl⟩ : syracuseStep 502259 = 753389) B753389
theorem B338419 : Blo 334751 338419 := bstep (se 1 (by rfl) ⟨253814, by rfl⟩ : syracuseStep 338419 = 507629) B507629
theorem B338435 : Blo 334751 338435 := bstep (se 1 (by rfl) ⟨253826, by rfl⟩ : syracuseStep 338435 = 507653) B507653
theorem B502289 : Blo 334751 502289 := bstep (se 2 (by rfl) ⟨188358, by rfl⟩ : syracuseStep 502289 = 376717) B376717
theorem B338451 : Blo 334751 338451 := bstep (se 1 (by rfl) ⟨253838, by rfl⟩ : syracuseStep 338451 = 507677) B507677
theorem B502307 : Blo 334751 502307 := bstep (se 1 (by rfl) ⟨376730, by rfl⟩ : syracuseStep 502307 = 753461) B753461
theorem B338467 : Blo 334751 338467 := bstep (se 1 (by rfl) ⟨253850, by rfl⟩ : syracuseStep 338467 = 507701) B507701
theorem B567857 : Blo 334751 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B338483 : Blo 334751 338483 := bstep (se 1 (by rfl) ⟨253862, by rfl⟩ : syracuseStep 338483 = 507725) B507725
theorem B502337 : Blo 334751 502337 := bstep (se 2 (by rfl) ⟨188376, by rfl⟩ : syracuseStep 502337 = 376753) B376753
theorem B338499 : Blo 334751 338499 := bstep (se 1 (by rfl) ⟨253874, by rfl⟩ : syracuseStep 338499 = 507749) B507749
theorem B502355 : Blo 334751 502355 := bstep (se 1 (by rfl) ⟨376766, by rfl⟩ : syracuseStep 502355 = 753533) B753533
theorem B338515 : Blo 334751 338515 := bstep (se 1 (by rfl) ⟨253886, by rfl⟩ : syracuseStep 338515 = 507773) B507773
theorem B338531 : Blo 334751 338531 := bstep (se 1 (by rfl) ⟨253898, by rfl⟩ : syracuseStep 338531 = 507797) B507797
theorem B502385 : Blo 334751 502385 := bstep (se 2 (by rfl) ⟨188394, by rfl⟩ : syracuseStep 502385 = 376789) B376789
theorem B338547 : Blo 334751 338547 := bstep (se 1 (by rfl) ⟨253910, by rfl⟩ : syracuseStep 338547 = 507821) B507821
theorem B502403 : Blo 334751 502403 := bstep (se 1 (by rfl) ⟨376802, by rfl⟩ : syracuseStep 502403 = 753605) B753605
theorem B338563 : Blo 334751 338563 := bstep (se 1 (by rfl) ⟨253922, by rfl⟩ : syracuseStep 338563 = 507845) B507845
theorem B338579 : Blo 334751 338579 := bstep (se 1 (by rfl) ⟨253934, by rfl⟩ : syracuseStep 338579 = 507869) B507869
theorem B502433 : Blo 334751 502433 := bstep (se 2 (by rfl) ⟨188412, by rfl⟩ : syracuseStep 502433 = 376825) B376825
theorem B338595 : Blo 334751 338595 := bstep (se 1 (by rfl) ⟨253946, by rfl⟩ : syracuseStep 338595 = 507893) B507893
theorem B567985 : Blo 334751 567985 := bstep (se 2 (by rfl) ⟨212994, by rfl⟩ : syracuseStep 567985 = 425989) B425989
theorem B502451 : Blo 334751 502451 := bstep (se 1 (by rfl) ⟨376838, by rfl⟩ : syracuseStep 502451 = 753677) B753677
theorem B338611 : Blo 334751 338611 := bstep (se 1 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 338611 = 507917) B507917
theorem B338627 : Blo 334751 338627 := bstep (se 1 (by rfl) ⟨253970, by rfl⟩ : syracuseStep 338627 = 507941) B507941
theorem B502481 : Blo 334751 502481 := bstep (se 2 (by rfl) ⟨188430, by rfl⟩ : syracuseStep 502481 = 376861) B376861
theorem B568019 : Blo 334751 568019 := bstep (se 1 (by rfl) ⟨426014, by rfl⟩ : syracuseStep 568019 = 852029) B852029
theorem B338643 : Blo 334751 338643 := bstep (se 1 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 338643 = 507965) B507965
theorem B502499 : Blo 334751 502499 := bstep (se 1 (by rfl) ⟨376874, by rfl⟩ : syracuseStep 502499 = 753749) B753749
theorem B338659 : Blo 334751 338659 := bstep (se 1 (by rfl) ⟨253994, by rfl⟩ : syracuseStep 338659 = 507989) B507989
theorem B338675 : Blo 334751 338675 := bstep (se 1 (by rfl) ⟨254006, by rfl⟩ : syracuseStep 338675 = 508013) B508013
theorem B502529 : Blo 334751 502529 := bstep (se 2 (by rfl) ⟨188448, by rfl⟩ : syracuseStep 502529 = 376897) B376897
theorem B338691 : Blo 334751 338691 := bstep (se 1 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 338691 = 508037) B508037
theorem B502547 : Blo 334751 502547 := bstep (se 1 (by rfl) ⟨376910, by rfl⟩ : syracuseStep 502547 = 753821) B753821
theorem B338707 : Blo 334751 338707 := bstep (se 1 (by rfl) ⟨254030, by rfl⟩ : syracuseStep 338707 = 508061) B508061
theorem B338723 : Blo 334751 338723 := bstep (se 1 (by rfl) ⟨254042, by rfl⟩ : syracuseStep 338723 = 508085) B508085
theorem B502577 : Blo 334751 502577 := bstep (se 2 (by rfl) ⟨188466, by rfl⟩ : syracuseStep 502577 = 376933) B376933
theorem B338739 : Blo 334751 338739 := bstep (se 1 (by rfl) ⟨254054, by rfl⟩ : syracuseStep 338739 = 508109) B508109
theorem B502595 : Blo 334751 502595 := bstep (se 1 (by rfl) ⟨376946, by rfl⟩ : syracuseStep 502595 = 753893) B753893
theorem B568147 : Blo 334751 568147 := bstep (se 1 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 568147 = 852221) B852221
theorem B502625 : Blo 334751 502625 := bstep (se 2 (by rfl) ⟨188484, by rfl⟩ : syracuseStep 502625 = 376969) B376969
theorem B502643 : Blo 334751 502643 := bstep (se 1 (by rfl) ⟨376982, by rfl⟩ : syracuseStep 502643 = 753965) B753965
theorem B502673 : Blo 334751 502673 := bstep (se 2 (by rfl) ⟨188502, by rfl⟩ : syracuseStep 502673 = 377005) B377005
theorem B502691 : Blo 334751 502691 := bstep (se 1 (by rfl) ⟨377018, by rfl⟩ : syracuseStep 502691 = 754037) B754037
theorem B502721 : Blo 334751 502721 := bstep (se 2 (by rfl) ⟨188520, by rfl⟩ : syracuseStep 502721 = 377041) B377041
theorem B502739 : Blo 334751 502739 := bstep (se 1 (by rfl) ⟨377054, by rfl⟩ : syracuseStep 502739 = 754109) B754109
theorem B568289 : Blo 334751 568289 := bstep (se 2 (by rfl) ⟨213108, by rfl⟩ : syracuseStep 568289 = 426217) B426217
theorem B502769 : Blo 334751 502769 := bstep (se 2 (by rfl) ⟨188538, by rfl⟩ : syracuseStep 502769 = 377077) B377077
theorem B502787 : Blo 334751 502787 := bstep (se 1 (by rfl) ⟨377090, by rfl⟩ : syracuseStep 502787 = 754181) B754181
theorem B502817 : Blo 334751 502817 := bstep (se 2 (by rfl) ⟨188556, by rfl⟩ : syracuseStep 502817 = 377113) B377113
theorem B502835 : Blo 334751 502835 := bstep (se 1 (by rfl) ⟨377126, by rfl⟩ : syracuseStep 502835 = 754253) B754253
theorem B502865 : Blo 334751 502865 := bstep (se 2 (by rfl) ⟨188574, by rfl⟩ : syracuseStep 502865 = 377149) B377149
theorem B568417 : Blo 334751 568417 := bstep (se 2 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 568417 = 426313) B426313
theorem B502883 : Blo 334751 502883 := bstep (se 1 (by rfl) ⟨377162, by rfl⟩ : syracuseStep 502883 = 754325) B754325
theorem B502913 : Blo 334751 502913 := bstep (se 2 (by rfl) ⟨188592, by rfl⟩ : syracuseStep 502913 = 377185) B377185
theorem B568451 : Blo 334751 568451 := bstep (se 1 (by rfl) ⟨426338, by rfl⟩ : syracuseStep 568451 = 852677) B852677
theorem B502931 : Blo 334751 502931 := bstep (se 1 (by rfl) ⟨377198, by rfl⟩ : syracuseStep 502931 = 754397) B754397
theorem B502961 : Blo 334751 502961 := bstep (se 2 (by rfl) ⟨188610, by rfl⟩ : syracuseStep 502961 = 377221) B377221
theorem B1813681 : Blo 334751 1813681 := bstep (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) B1360261
theorem B502979 : Blo 334751 502979 := bstep (se 1 (by rfl) ⟨377234, by rfl⟩ : syracuseStep 502979 = 754469) B754469
theorem B503009 : Blo 334751 503009 := bstep (se 2 (by rfl) ⟨188628, by rfl⟩ : syracuseStep 503009 = 377257) B377257
theorem B1158371 : Blo 334751 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B503027 : Blo 334751 503027 := bstep (se 1 (by rfl) ⟨377270, by rfl⟩ : syracuseStep 503027 = 754541) B754541
theorem B568579 : Blo 334751 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B503057 : Blo 334751 503057 := bstep (se 2 (by rfl) ⟨188646, by rfl⟩ : syracuseStep 503057 = 377293) B377293
theorem B503075 : Blo 334751 503075 := bstep (se 1 (by rfl) ⟨377306, by rfl⟩ : syracuseStep 503075 = 754613) B754613
theorem B732451 : Blo 334751 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B503105 : Blo 334751 503105 := bstep (se 2 (by rfl) ⟨188664, by rfl⟩ : syracuseStep 503105 = 377329) B377329
theorem B503123 : Blo 334751 503123 := bstep (se 1 (by rfl) ⟨377342, by rfl⟩ : syracuseStep 503123 = 754685) B754685
theorem B1092973 : Blo 334751 1092973 := bstep (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) B409865
theorem B503153 : Blo 334751 503153 := bstep (se 2 (by rfl) ⟨188682, by rfl⟩ : syracuseStep 503153 = 377365) B377365
theorem B2567537 : Blo 334751 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B503171 : Blo 334751 503171 := bstep (se 1 (by rfl) ⟨377378, by rfl⟩ : syracuseStep 503171 = 754757) B754757
theorem B568721 : Blo 334751 568721 := bstep (se 2 (by rfl) ⟨213270, by rfl⟩ : syracuseStep 568721 = 426541) B426541
theorem B503201 : Blo 334751 503201 := bstep (se 2 (by rfl) ⟨188700, by rfl⟩ : syracuseStep 503201 = 377401) B377401
theorem B503219 : Blo 334751 503219 := bstep (se 1 (by rfl) ⟨377414, by rfl⟩ : syracuseStep 503219 = 754829) B754829
theorem B3452357 : Blo 334751 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B503249 : Blo 334751 503249 := bstep (se 2 (by rfl) ⟨188718, by rfl⟩ : syracuseStep 503249 = 377437) B377437
theorem B503267 : Blo 334751 503267 := bstep (se 1 (by rfl) ⟨377450, by rfl⟩ : syracuseStep 503267 = 754901) B754901
theorem B503297 : Blo 334751 503297 := bstep (se 2 (by rfl) ⟨188736, by rfl⟩ : syracuseStep 503297 = 377473) B377473
theorem B568849 : Blo 334751 568849 := bstep (se 2 (by rfl) ⟨213318, by rfl⟩ : syracuseStep 568849 = 426637) B426637
theorem B503315 : Blo 334751 503315 := bstep (se 1 (by rfl) ⟨377486, by rfl⟩ : syracuseStep 503315 = 754973) B754973
theorem B405011 : Blo 334751 405011 := bstep (se 1 (by rfl) ⟨303758, by rfl⟩ : syracuseStep 405011 = 607517) B607517
theorem B503345 : Blo 334751 503345 := bstep (se 2 (by rfl) ⟨188754, by rfl⟩ : syracuseStep 503345 = 377509) B377509
theorem B568883 : Blo 334751 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B503363 : Blo 334751 503363 := bstep (se 1 (by rfl) ⟨377522, by rfl⟩ : syracuseStep 503363 = 755045) B755045
theorem B503393 : Blo 334751 503393 := bstep (se 2 (by rfl) ⟨188772, by rfl⟩ : syracuseStep 503393 = 377545) B377545
theorem B503411 : Blo 334751 503411 := bstep (se 1 (by rfl) ⟨377558, by rfl⟩ : syracuseStep 503411 = 755117) B755117
theorem B962189 : Blo 334751 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B503441 : Blo 334751 503441 := bstep (se 2 (by rfl) ⟨188790, by rfl⟩ : syracuseStep 503441 = 377581) B377581
theorem B503459 : Blo 334751 503459 := bstep (se 1 (by rfl) ⟨377594, by rfl⟩ : syracuseStep 503459 = 755189) B755189
theorem B569011 : Blo 334751 569011 := bstep (se 1 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 569011 = 853517) B853517
theorem B503489 : Blo 334751 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B503507 : Blo 334751 503507 := bstep (se 1 (by rfl) ⟨377630, by rfl⟩ : syracuseStep 503507 = 755261) B755261
theorem B503537 : Blo 334751 503537 := bstep (se 2 (by rfl) ⟨188826, by rfl⟩ : syracuseStep 503537 = 377653) B377653
theorem B503555 : Blo 334751 503555 := bstep (se 1 (by rfl) ⟨377666, by rfl⟩ : syracuseStep 503555 = 755333) B755333
theorem B503585 : Blo 334751 503585 := bstep (se 2 (by rfl) ⟨188844, by rfl⟩ : syracuseStep 503585 = 377689) B377689
theorem B503603 : Blo 334751 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B569153 : Blo 334751 569153 := bstep (se 2 (by rfl) ⟨213432, by rfl⟩ : syracuseStep 569153 = 426865) B426865
theorem B962371 : Blo 334751 962371 := bstep (se 1 (by rfl) ⟨721778, by rfl⟩ : syracuseStep 962371 = 1443557) B1443557
theorem B503633 : Blo 334751 503633 := bstep (se 2 (by rfl) ⟨188862, by rfl⟩ : syracuseStep 503633 = 377725) B377725
theorem B503651 : Blo 334751 503651 := bstep (se 1 (by rfl) ⟨377738, by rfl⟩ : syracuseStep 503651 = 755477) B755477
theorem B962417 : Blo 334751 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B503681 : Blo 334751 503681 := bstep (se 2 (by rfl) ⟨188880, by rfl⟩ : syracuseStep 503681 = 377761) B377761
theorem B1027981 : Blo 334751 1027981 := bstep (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) B385493
theorem B536465 : Blo 334751 536465 := bstep (se 2 (by rfl) ⟨201174, by rfl⟩ : syracuseStep 536465 = 402349) B402349
theorem B503699 : Blo 334751 503699 := bstep (se 1 (by rfl) ⟨377774, by rfl⟩ : syracuseStep 503699 = 755549) B755549
theorem B503729 : Blo 334751 503729 := bstep (se 2 (by rfl) ⟨188898, by rfl⟩ : syracuseStep 503729 = 377797) B377797
theorem B569281 : Blo 334751 569281 := bstep (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) B426961
theorem B503747 : Blo 334751 503747 := bstep (se 1 (by rfl) ⟨377810, by rfl⟩ : syracuseStep 503747 = 755621) B755621
theorem B503777 : Blo 334751 503777 := bstep (se 2 (by rfl) ⟨188916, by rfl⟩ : syracuseStep 503777 = 377833) B377833
theorem B569315 : Blo 334751 569315 := bstep (se 1 (by rfl) ⟨426986, by rfl⟩ : syracuseStep 569315 = 853973) B853973
theorem B503795 : Blo 334751 503795 := bstep (se 1 (by rfl) ⟨377846, by rfl⟩ : syracuseStep 503795 = 755693) B755693
theorem B503825 : Blo 334751 503825 := bstep (se 2 (by rfl) ⟨188934, by rfl⟩ : syracuseStep 503825 = 377869) B377869
theorem B503843 : Blo 334751 503843 := bstep (se 1 (by rfl) ⟨377882, by rfl⟩ : syracuseStep 503843 = 755765) B755765
theorem B503873 : Blo 334751 503873 := bstep (se 2 (by rfl) ⟨188952, by rfl⟩ : syracuseStep 503873 = 377905) B377905
theorem B503891 : Blo 334751 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B569443 : Blo 334751 569443 := bstep (se 1 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 569443 = 854165) B854165
theorem B503921 : Blo 334751 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B503939 : Blo 334751 503939 := bstep (se 1 (by rfl) ⟨377954, by rfl⟩ : syracuseStep 503939 = 755909) B755909
theorem B1028227 : Blo 334751 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B503969 : Blo 334751 503969 := bstep (se 2 (by rfl) ⟨188988, by rfl⟩ : syracuseStep 503969 = 377977) B377977
theorem B503987 : Blo 334751 503987 := bstep (se 1 (by rfl) ⟨377990, by rfl⟩ : syracuseStep 503987 = 755981) B755981
theorem B504017 : Blo 334751 504017 := bstep (se 2 (by rfl) ⟨189006, by rfl⟩ : syracuseStep 504017 = 378013) B378013
theorem B504035 : Blo 334751 504035 := bstep (se 1 (by rfl) ⟨378026, by rfl⟩ : syracuseStep 504035 = 756053) B756053
theorem B569585 : Blo 334751 569585 := bstep (se 2 (by rfl) ⟨213594, by rfl⟩ : syracuseStep 569585 = 427189) B427189
theorem B504065 : Blo 334751 504065 := bstep (se 2 (by rfl) ⟨189024, by rfl⟩ : syracuseStep 504065 = 378049) B378049
theorem B2961677 : Blo 334751 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B504083 : Blo 334751 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B504113 : Blo 334751 504113 := bstep (se 2 (by rfl) ⟨189042, by rfl⟩ : syracuseStep 504113 = 378085) B378085
theorem B504131 : Blo 334751 504131 := bstep (se 1 (by rfl) ⟨378098, by rfl⟩ : syracuseStep 504131 = 756197) B756197
theorem B504161 : Blo 334751 504161 := bstep (se 2 (by rfl) ⟨189060, by rfl⟩ : syracuseStep 504161 = 378121) B378121
theorem B569713 : Blo 334751 569713 := bstep (se 2 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 569713 = 427285) B427285
theorem B504179 : Blo 334751 504179 := bstep (se 1 (by rfl) ⟨378134, by rfl⟩ : syracuseStep 504179 = 756269) B756269
theorem B536977 : Blo 334751 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B504209 : Blo 334751 504209 := bstep (se 2 (by rfl) ⟨189078, by rfl⟩ : syracuseStep 504209 = 378157) B378157
theorem B569747 : Blo 334751 569747 := bstep (se 1 (by rfl) ⟨427310, by rfl⟩ : syracuseStep 569747 = 854621) B854621
theorem B504227 : Blo 334751 504227 := bstep (se 1 (by rfl) ⟨378170, by rfl⟩ : syracuseStep 504227 = 756341) B756341
theorem B504257 : Blo 334751 504257 := bstep (se 2 (by rfl) ⟨189096, by rfl⟩ : syracuseStep 504257 = 378193) B378193
theorem B504275 : Blo 334751 504275 := bstep (se 1 (by rfl) ⟨378206, by rfl⟩ : syracuseStep 504275 = 756413) B756413
theorem B504305 : Blo 334751 504305 := bstep (se 2 (by rfl) ⟨189114, by rfl⟩ : syracuseStep 504305 = 378229) B378229
theorem B504323 : Blo 334751 504323 := bstep (se 1 (by rfl) ⟨378242, by rfl⟩ : syracuseStep 504323 = 756485) B756485
theorem B569875 : Blo 334751 569875 := bstep (se 1 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 569875 = 854813) B854813
theorem B504353 : Blo 334751 504353 := bstep (se 2 (by rfl) ⟨189132, by rfl⟩ : syracuseStep 504353 = 378265) B378265
theorem B504371 : Blo 334751 504371 := bstep (se 1 (by rfl) ⟨378278, by rfl⟩ : syracuseStep 504371 = 756557) B756557
theorem B504401 : Blo 334751 504401 := bstep (se 2 (by rfl) ⟨189150, by rfl⟩ : syracuseStep 504401 = 378301) B378301
theorem B504419 : Blo 334751 504419 := bstep (se 1 (by rfl) ⟨378314, by rfl⟩ : syracuseStep 504419 = 756629) B756629
theorem B504449 : Blo 334751 504449 := bstep (se 2 (by rfl) ⟨189168, by rfl⟩ : syracuseStep 504449 = 378337) B378337
theorem B504467 : Blo 334751 504467 := bstep (se 1 (by rfl) ⟨378350, by rfl⟩ : syracuseStep 504467 = 756701) B756701
theorem B570017 : Blo 334751 570017 := bstep (se 2 (by rfl) ⟨213756, by rfl⟩ : syracuseStep 570017 = 427513) B427513
theorem B504497 : Blo 334751 504497 := bstep (se 2 (by rfl) ⟨189186, by rfl⟩ : syracuseStep 504497 = 378373) B378373
theorem B504515 : Blo 334751 504515 := bstep (se 1 (by rfl) ⟨378386, by rfl⟩ : syracuseStep 504515 = 756773) B756773
theorem B504545 : Blo 334751 504545 := bstep (se 2 (by rfl) ⟨189204, by rfl⟩ : syracuseStep 504545 = 378409) B378409
theorem B504563 : Blo 334751 504563 := bstep (se 1 (by rfl) ⟨378422, by rfl⟩ : syracuseStep 504563 = 756845) B756845
theorem B504593 : Blo 334751 504593 := bstep (se 2 (by rfl) ⟨189222, by rfl⟩ : syracuseStep 504593 = 378445) B378445
theorem B570145 : Blo 334751 570145 := bstep (se 2 (by rfl) ⟨213804, by rfl⟩ : syracuseStep 570145 = 427609) B427609
theorem B504611 : Blo 334751 504611 := bstep (se 1 (by rfl) ⟨378458, by rfl⟩ : syracuseStep 504611 = 756917) B756917
theorem B504641 : Blo 334751 504641 := bstep (se 2 (by rfl) ⟨189240, by rfl⟩ : syracuseStep 504641 = 378481) B378481
theorem B570179 : Blo 334751 570179 := bstep (se 1 (by rfl) ⟨427634, by rfl⟩ : syracuseStep 570179 = 855269) B855269
theorem B504659 : Blo 334751 504659 := bstep (se 1 (by rfl) ⟨378494, by rfl⟩ : syracuseStep 504659 = 756989) B756989
theorem B504689 : Blo 334751 504689 := bstep (se 2 (by rfl) ⟨189258, by rfl⟩ : syracuseStep 504689 = 378517) B378517
theorem B635779 : Blo 334751 635779 := bstep (se 1 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 635779 = 953669) B953669
theorem B504707 : Blo 334751 504707 := bstep (se 1 (by rfl) ⟨378530, by rfl⟩ : syracuseStep 504707 = 757061) B757061
theorem B504737 : Blo 334751 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B635825 : Blo 334751 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B504755 : Blo 334751 504755 := bstep (se 1 (by rfl) ⟨378566, by rfl⟩ : syracuseStep 504755 = 757133) B757133
theorem B570307 : Blo 334751 570307 := bstep (se 1 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 570307 = 855461) B855461
theorem B504785 : Blo 334751 504785 := bstep (se 2 (by rfl) ⟨189294, by rfl⟩ : syracuseStep 504785 = 378589) B378589
theorem B504803 : Blo 334751 504803 := bstep (se 1 (by rfl) ⟨378602, by rfl⟩ : syracuseStep 504803 = 757205) B757205
theorem B537587 : Blo 334751 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B504833 : Blo 334751 504833 := bstep (se 2 (by rfl) ⟨189312, by rfl⟩ : syracuseStep 504833 = 378625) B378625
theorem B504851 : Blo 334751 504851 := bstep (se 1 (by rfl) ⟨378638, by rfl⟩ : syracuseStep 504851 = 757277) B757277
theorem B504881 : Blo 334751 504881 := bstep (se 2 (by rfl) ⟨189330, by rfl⟩ : syracuseStep 504881 = 378661) B378661
theorem B504899 : Blo 334751 504899 := bstep (se 1 (by rfl) ⟨378674, by rfl⟩ : syracuseStep 504899 = 757349) B757349
theorem B570449 : Blo 334751 570449 := bstep (se 2 (by rfl) ⟨213918, by rfl⟩ : syracuseStep 570449 = 427837) B427837
theorem B504929 : Blo 334751 504929 := bstep (se 2 (by rfl) ⟨189348, by rfl⟩ : syracuseStep 504929 = 378697) B378697
theorem B504947 : Blo 334751 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B1913989 : Blo 334751 1913989 := bstep (se 4 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 1913989 = 358873) B358873
theorem B504977 : Blo 334751 504977 := bstep (se 2 (by rfl) ⟨189366, by rfl⟩ : syracuseStep 504977 = 378733) B378733
theorem B504995 : Blo 334751 504995 := bstep (se 1 (by rfl) ⟨378746, by rfl⟩ : syracuseStep 504995 = 757493) B757493
theorem B505025 : Blo 334751 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B636113 : Blo 334751 636113 := bstep (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) B477085
theorem B570577 : Blo 334751 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B505043 : Blo 334751 505043 := bstep (se 1 (by rfl) ⟨378782, by rfl⟩ : syracuseStep 505043 = 757565) B757565
theorem B505073 : Blo 334751 505073 := bstep (se 2 (by rfl) ⟨189402, by rfl⟩ : syracuseStep 505073 = 378805) B378805
theorem B570611 : Blo 334751 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B505091 : Blo 334751 505091 := bstep (se 1 (by rfl) ⟨378818, by rfl⟩ : syracuseStep 505091 = 757637) B757637
theorem B505121 : Blo 334751 505121 := bstep (se 2 (by rfl) ⟨189420, by rfl⟩ : syracuseStep 505121 = 378841) B378841
theorem B963875 : Blo 334751 963875 := bstep (se 1 (by rfl) ⟨722906, by rfl⟩ : syracuseStep 963875 = 1445813) B1445813
theorem B505139 : Blo 334751 505139 := bstep (se 1 (by rfl) ⟨378854, by rfl⟩ : syracuseStep 505139 = 757709) B757709
theorem B505169 : Blo 334751 505169 := bstep (se 2 (by rfl) ⟨189438, by rfl⟩ : syracuseStep 505169 = 378877) B378877
theorem B505187 : Blo 334751 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B570739 : Blo 334751 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B505217 : Blo 334751 505217 := bstep (se 2 (by rfl) ⟨189456, by rfl⟩ : syracuseStep 505217 = 378913) B378913
theorem B505235 : Blo 334751 505235 := bstep (se 1 (by rfl) ⟨378926, by rfl⟩ : syracuseStep 505235 = 757853) B757853
theorem B505265 : Blo 334751 505265 := bstep (se 2 (by rfl) ⟨189474, by rfl⟩ : syracuseStep 505265 = 378949) B378949
theorem B505283 : Blo 334751 505283 := bstep (se 1 (by rfl) ⟨378962, by rfl⟩ : syracuseStep 505283 = 757925) B757925
theorem B505313 : Blo 334751 505313 := bstep (se 2 (by rfl) ⟨189492, by rfl⟩ : syracuseStep 505313 = 378985) B378985
theorem B505331 : Blo 334751 505331 := bstep (se 1 (by rfl) ⟨378998, by rfl⟩ : syracuseStep 505331 = 757997) B757997
theorem B570881 : Blo 334751 570881 := bstep (se 2 (by rfl) ⟨214080, by rfl⟩ : syracuseStep 570881 = 428161) B428161
theorem B505361 : Blo 334751 505361 := bstep (se 2 (by rfl) ⟨189510, by rfl⟩ : syracuseStep 505361 = 379021) B379021
theorem B505379 : Blo 334751 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B505409 : Blo 334751 505409 := bstep (se 2 (by rfl) ⟨189528, by rfl⟩ : syracuseStep 505409 = 379057) B379057
theorem B505427 : Blo 334751 505427 := bstep (se 1 (by rfl) ⟨379070, by rfl⟩ : syracuseStep 505427 = 758141) B758141
theorem B341587 : Blo 334751 341587 := bstep (se 1 (by rfl) ⟨256190, by rfl⟩ : syracuseStep 341587 = 512381) B512381
theorem B505457 : Blo 334751 505457 := bstep (se 2 (by rfl) ⟨189546, by rfl⟩ : syracuseStep 505457 = 379093) B379093
theorem B571009 : Blo 334751 571009 := bstep (se 2 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 571009 = 428257) B428257
theorem B505475 : Blo 334751 505475 := bstep (se 1 (by rfl) ⟨379106, by rfl⟩ : syracuseStep 505475 = 758213) B758213
theorem B505505 : Blo 334751 505505 := bstep (se 2 (by rfl) ⟨189564, by rfl⟩ : syracuseStep 505505 = 379129) B379129
theorem B571043 : Blo 334751 571043 := bstep (se 1 (by rfl) ⟨428282, by rfl⟩ : syracuseStep 571043 = 856565) B856565
theorem B505523 : Blo 334751 505523 := bstep (se 1 (by rfl) ⟨379142, by rfl⟩ : syracuseStep 505523 = 758285) B758285
theorem B505553 : Blo 334751 505553 := bstep (se 2 (by rfl) ⟨189582, by rfl⟩ : syracuseStep 505553 = 379165) B379165
theorem B4830947 : Blo 334751 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B505571 : Blo 334751 505571 := bstep (se 1 (by rfl) ⟨379178, by rfl⟩ : syracuseStep 505571 = 758357) B758357
theorem B505601 : Blo 334751 505601 := bstep (se 2 (by rfl) ⟨189600, by rfl⟩ : syracuseStep 505601 = 379201) B379201
theorem B505619 : Blo 334751 505619 := bstep (se 1 (by rfl) ⟨379214, by rfl⟩ : syracuseStep 505619 = 758429) B758429
theorem B571171 : Blo 334751 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B505649 : Blo 334751 505649 := bstep (se 2 (by rfl) ⟨189618, by rfl⟩ : syracuseStep 505649 = 379237) B379237
theorem B505667 : Blo 334751 505667 := bstep (se 1 (by rfl) ⟨379250, by rfl⟩ : syracuseStep 505667 = 758501) B758501
theorem B505697 : Blo 334751 505697 := bstep (se 2 (by rfl) ⟨189636, by rfl⟩ : syracuseStep 505697 = 379273) B379273
theorem B505715 : Blo 334751 505715 := bstep (se 1 (by rfl) ⟨379286, by rfl⟩ : syracuseStep 505715 = 758573) B758573
theorem B505745 : Blo 334751 505745 := bstep (se 2 (by rfl) ⟨189654, by rfl⟩ : syracuseStep 505745 = 379309) B379309
theorem B636835 : Blo 334751 636835 := bstep (se 1 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 636835 = 955253) B955253
theorem B505763 : Blo 334751 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B571313 : Blo 334751 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B505793 : Blo 334751 505793 := bstep (se 2 (by rfl) ⟨189672, by rfl⟩ : syracuseStep 505793 = 379345) B379345
theorem B538579 : Blo 334751 538579 := bstep (se 1 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 538579 = 807869) B807869
theorem B505811 : Blo 334751 505811 := bstep (se 1 (by rfl) ⟨379358, by rfl⟩ : syracuseStep 505811 = 758717) B758717
theorem B505841 : Blo 334751 505841 := bstep (se 2 (by rfl) ⟨189690, by rfl⟩ : syracuseStep 505841 = 379381) B379381
theorem B505859 : Blo 334751 505859 := bstep (se 1 (by rfl) ⟨379394, by rfl⟩ : syracuseStep 505859 = 758789) B758789
theorem B505889 : Blo 334751 505889 := bstep (se 2 (by rfl) ⟨189708, by rfl⟩ : syracuseStep 505889 = 379417) B379417
theorem B571441 : Blo 334751 571441 := bstep (se 2 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 571441 = 428581) B428581
theorem B505907 : Blo 334751 505907 := bstep (se 1 (by rfl) ⟨379430, by rfl⟩ : syracuseStep 505907 = 758861) B758861
theorem B505937 : Blo 334751 505937 := bstep (se 2 (by rfl) ⟨189726, by rfl⟩ : syracuseStep 505937 = 379453) B379453
theorem B571475 : Blo 334751 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B505955 : Blo 334751 505955 := bstep (se 1 (by rfl) ⟨379466, by rfl⟩ : syracuseStep 505955 = 758933) B758933
theorem B604273 : Blo 334751 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B505985 : Blo 334751 505985 := bstep (se 2 (by rfl) ⟨189744, by rfl⟩ : syracuseStep 505985 = 379489) B379489
theorem B506003 : Blo 334751 506003 := bstep (se 1 (by rfl) ⟨379502, by rfl⟩ : syracuseStep 506003 = 759005) B759005
theorem B506033 : Blo 334751 506033 := bstep (se 2 (by rfl) ⟨189762, by rfl⟩ : syracuseStep 506033 = 379525) B379525
theorem B506051 : Blo 334751 506051 := bstep (se 1 (by rfl) ⟨379538, by rfl⟩ : syracuseStep 506051 = 759077) B759077
theorem B571603 : Blo 334751 571603 := bstep (se 1 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 571603 = 857405) B857405
theorem B506081 : Blo 334751 506081 := bstep (se 2 (by rfl) ⟨189780, by rfl⟩ : syracuseStep 506081 = 379561) B379561
theorem B506099 : Blo 334751 506099 := bstep (se 1 (by rfl) ⟨379574, by rfl⟩ : syracuseStep 506099 = 759149) B759149
theorem B506129 : Blo 334751 506129 := bstep (se 2 (by rfl) ⟨189798, by rfl⟩ : syracuseStep 506129 = 379597) B379597
theorem B506147 : Blo 334751 506147 := bstep (se 1 (by rfl) ⟨379610, by rfl⟩ : syracuseStep 506147 = 759221) B759221
theorem B506177 : Blo 334751 506177 := bstep (se 2 (by rfl) ⟨189816, by rfl⟩ : syracuseStep 506177 = 379633) B379633
theorem B506195 : Blo 334751 506195 := bstep (se 1 (by rfl) ⟨379646, by rfl⟩ : syracuseStep 506195 = 759293) B759293
theorem B637283 : Blo 334751 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B506225 : Blo 334751 506225 := bstep (se 2 (by rfl) ⟨189834, by rfl⟩ : syracuseStep 506225 = 379669) B379669
theorem B506243 : Blo 334751 506243 := bstep (se 1 (by rfl) ⟨379682, by rfl⟩ : syracuseStep 506243 = 759365) B759365
theorem B506273 : Blo 334751 506273 := bstep (se 2 (by rfl) ⟨189852, by rfl⟩ : syracuseStep 506273 = 379705) B379705
theorem B506291 : Blo 334751 506291 := bstep (se 1 (by rfl) ⟨379718, by rfl⟩ : syracuseStep 506291 = 759437) B759437
theorem B506321 : Blo 334751 506321 := bstep (se 2 (by rfl) ⟨189870, by rfl⟩ : syracuseStep 506321 = 379741) B379741
theorem B506339 : Blo 334751 506339 := bstep (se 1 (by rfl) ⟨379754, by rfl⟩ : syracuseStep 506339 = 759509) B759509
theorem B506369 : Blo 334751 506369 := bstep (se 2 (by rfl) ⟨189888, by rfl⟩ : syracuseStep 506369 = 379777) B379777
theorem B1161745 : Blo 334751 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B506387 : Blo 334751 506387 := bstep (se 1 (by rfl) ⟨379790, by rfl⟩ : syracuseStep 506387 = 759581) B759581
theorem B506417 : Blo 334751 506417 := bstep (se 2 (by rfl) ⟨189906, by rfl⟩ : syracuseStep 506417 = 379813) B379813
theorem B506435 : Blo 334751 506435 := bstep (se 1 (by rfl) ⟨379826, by rfl⟩ : syracuseStep 506435 = 759653) B759653
theorem B506465 : Blo 334751 506465 := bstep (se 2 (by rfl) ⟨189924, by rfl⟩ : syracuseStep 506465 = 379849) B379849
theorem B506483 : Blo 334751 506483 := bstep (se 1 (by rfl) ⟨379862, by rfl⟩ : syracuseStep 506483 = 759725) B759725
theorem B637571 : Blo 334751 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B506513 : Blo 334751 506513 := bstep (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) B379885
theorem B506531 : Blo 334751 506531 := bstep (se 1 (by rfl) ⟨379898, by rfl⟩ : syracuseStep 506531 = 759797) B759797
theorem B506561 : Blo 334751 506561 := bstep (se 2 (by rfl) ⟨189960, by rfl⟩ : syracuseStep 506561 = 379921) B379921
theorem B506579 : Blo 334751 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B506609 : Blo 334751 506609 := bstep (se 2 (by rfl) ⟨189978, by rfl⟩ : syracuseStep 506609 = 379957) B379957
theorem B4340465 : Blo 334751 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B506627 : Blo 334751 506627 := bstep (se 1 (by rfl) ⟨379970, by rfl⟩ : syracuseStep 506627 = 759941) B759941
theorem B342787 : Blo 334751 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B2145037 : Blo 334751 2145037 := bstep (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) B804389
theorem B506657 : Blo 334751 506657 := bstep (se 2 (by rfl) ⟨189996, by rfl⟩ : syracuseStep 506657 = 379993) B379993
theorem B506675 : Blo 334751 506675 := bstep (se 1 (by rfl) ⟨380006, by rfl⟩ : syracuseStep 506675 = 760013) B760013
theorem B506705 : Blo 334751 506705 := bstep (se 2 (by rfl) ⟨190014, by rfl⟩ : syracuseStep 506705 = 380029) B380029
theorem B539489 : Blo 334751 539489 := bstep (se 2 (by rfl) ⟨202308, by rfl⟩ : syracuseStep 539489 = 404617) B404617
theorem B506723 : Blo 334751 506723 := bstep (se 1 (by rfl) ⟨380042, by rfl⟩ : syracuseStep 506723 = 760085) B760085
theorem B506753 : Blo 334751 506753 := bstep (se 2 (by rfl) ⟨190032, by rfl⟩ : syracuseStep 506753 = 380065) B380065
theorem B506771 : Blo 334751 506771 := bstep (se 1 (by rfl) ⟨380078, by rfl⟩ : syracuseStep 506771 = 760157) B760157
theorem B506801 : Blo 334751 506801 := bstep (se 2 (by rfl) ⟨190050, by rfl⟩ : syracuseStep 506801 = 380101) B380101
theorem B506819 : Blo 334751 506819 := bstep (se 1 (by rfl) ⟨380114, by rfl⟩ : syracuseStep 506819 = 760229) B760229
theorem B539617 : Blo 334751 539617 := bstep (se 2 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 539617 = 404713) B404713
theorem B506849 : Blo 334751 506849 := bstep (se 2 (by rfl) ⟨190068, by rfl⟩ : syracuseStep 506849 = 380137) B380137
theorem B506867 : Blo 334751 506867 := bstep (se 1 (by rfl) ⟨380150, by rfl⟩ : syracuseStep 506867 = 760301) B760301
theorem B506897 : Blo 334751 506897 := bstep (se 2 (by rfl) ⟨190086, by rfl⟩ : syracuseStep 506897 = 380173) B380173
theorem B506915 : Blo 334751 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B506945 : Blo 334751 506945 := bstep (se 2 (by rfl) ⟨190104, by rfl⟩ : syracuseStep 506945 = 380209) B380209
theorem B1915973 : Blo 334751 1915973 := bstep (se 4 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 1915973 = 359245) B359245
theorem B506963 : Blo 334751 506963 := bstep (se 1 (by rfl) ⟨380222, by rfl⟩ : syracuseStep 506963 = 760445) B760445
theorem B506993 : Blo 334751 506993 := bstep (se 2 (by rfl) ⟨190122, by rfl⟩ : syracuseStep 506993 = 380245) B380245
theorem B507011 : Blo 334751 507011 := bstep (se 1 (by rfl) ⟨380258, by rfl⟩ : syracuseStep 507011 = 760517) B760517
theorem B507041 : Blo 334751 507041 := bstep (se 2 (by rfl) ⟨190140, by rfl⟩ : syracuseStep 507041 = 380281) B380281
theorem B507059 : Blo 334751 507059 := bstep (se 1 (by rfl) ⟨380294, by rfl⟩ : syracuseStep 507059 = 760589) B760589
theorem B507089 : Blo 334751 507089 := bstep (se 2 (by rfl) ⟨190158, by rfl⟩ : syracuseStep 507089 = 380317) B380317
theorem B507107 : Blo 334751 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B507137 : Blo 334751 507137 := bstep (se 2 (by rfl) ⟨190176, by rfl⟩ : syracuseStep 507137 = 380353) B380353
theorem B507155 : Blo 334751 507155 := bstep (se 1 (by rfl) ⟨380366, by rfl⟩ : syracuseStep 507155 = 760733) B760733
theorem B507185 : Blo 334751 507185 := bstep (se 2 (by rfl) ⟨190194, by rfl⟩ : syracuseStep 507185 = 380389) B380389
theorem B507203 : Blo 334751 507203 := bstep (se 1 (by rfl) ⟨380402, by rfl⟩ : syracuseStep 507203 = 760805) B760805
theorem B507233 : Blo 334751 507233 := bstep (se 2 (by rfl) ⟨190212, by rfl⟩ : syracuseStep 507233 = 380425) B380425
theorem B1129841 : Blo 334751 1129841 := bstep (se 2 (by rfl) ⟨423690, by rfl⟩ : syracuseStep 1129841 = 847381) B847381
theorem B507251 : Blo 334751 507251 := bstep (se 1 (by rfl) ⟨380438, by rfl⟩ : syracuseStep 507251 = 760877) B760877
theorem B507281 : Blo 334751 507281 := bstep (se 2 (by rfl) ⟨190230, by rfl⟩ : syracuseStep 507281 = 380461) B380461
theorem B507299 : Blo 334751 507299 := bstep (se 1 (by rfl) ⟨380474, by rfl⟩ : syracuseStep 507299 = 760949) B760949
theorem B507329 : Blo 334751 507329 := bstep (se 2 (by rfl) ⟨190248, by rfl⟩ : syracuseStep 507329 = 380497) B380497
theorem B769475 : Blo 334751 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B507347 : Blo 334751 507347 := bstep (se 1 (by rfl) ⟨380510, by rfl⟩ : syracuseStep 507347 = 761021) B761021
theorem B835043 : Blo 334751 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B507377 : Blo 334751 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B507395 : Blo 334751 507395 := bstep (se 1 (by rfl) ⟨380546, by rfl⟩ : syracuseStep 507395 = 761093) B761093
theorem B507425 : Blo 334751 507425 := bstep (se 2 (by rfl) ⟨190284, by rfl⟩ : syracuseStep 507425 = 380569) B380569
theorem B638513 : Blo 334751 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B507443 : Blo 334751 507443 := bstep (se 1 (by rfl) ⟨380582, by rfl⟩ : syracuseStep 507443 = 761165) B761165
theorem B507473 : Blo 334751 507473 := bstep (se 2 (by rfl) ⟨190302, by rfl⟩ : syracuseStep 507473 = 380605) B380605
theorem B507491 : Blo 334751 507491 := bstep (se 1 (by rfl) ⟨380618, by rfl⟩ : syracuseStep 507491 = 761237) B761237
theorem B507521 : Blo 334751 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B507539 : Blo 334751 507539 := bstep (se 1 (by rfl) ⟨380654, by rfl⟩ : syracuseStep 507539 = 761309) B761309
theorem B507569 : Blo 334751 507569 := bstep (se 2 (by rfl) ⟨190338, by rfl⟩ : syracuseStep 507569 = 380677) B380677
theorem B507587 : Blo 334751 507587 := bstep (se 1 (by rfl) ⟨380690, by rfl⟩ : syracuseStep 507587 = 761381) B761381
theorem B507617 : Blo 334751 507617 := bstep (se 2 (by rfl) ⟨190356, by rfl⟩ : syracuseStep 507617 = 380713) B380713
theorem B409315 : Blo 334751 409315 := bstep (se 1 (by rfl) ⟨306986, by rfl⟩ : syracuseStep 409315 = 613973) B613973
theorem B507635 : Blo 334751 507635 := bstep (se 1 (by rfl) ⟨380726, by rfl⟩ : syracuseStep 507635 = 761453) B761453
theorem B507665 : Blo 334751 507665 := bstep (se 2 (by rfl) ⟨190374, by rfl⟩ : syracuseStep 507665 = 380749) B380749
theorem B507683 : Blo 334751 507683 := bstep (se 1 (by rfl) ⟨380762, by rfl⟩ : syracuseStep 507683 = 761525) B761525
theorem B376627 : Blo 334751 376627 := bstep (se 1 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 376627 = 564941) B564941
theorem B507713 : Blo 334751 507713 := bstep (se 2 (by rfl) ⟨190392, by rfl⟩ : syracuseStep 507713 = 380785) B380785
theorem B507731 : Blo 334751 507731 := bstep (se 1 (by rfl) ⟨380798, by rfl⟩ : syracuseStep 507731 = 761597) B761597
theorem B507761 : Blo 334751 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B507779 : Blo 334751 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B1130381 : Blo 334751 1130381 := bstep (se 3 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 1130381 = 423893) B423893
theorem B507809 : Blo 334751 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B507827 : Blo 334751 507827 := bstep (se 1 (by rfl) ⟨380870, by rfl⟩ : syracuseStep 507827 = 761741) B761741
theorem B1130435 : Blo 334751 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B376771 : Blo 334751 376771 := bstep (se 1 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 376771 = 565157) B565157
theorem B540611 : Blo 334751 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B507857 : Blo 334751 507857 := bstep (se 2 (by rfl) ⟨190446, by rfl⟩ : syracuseStep 507857 = 380893) B380893
theorem B507875 : Blo 334751 507875 := bstep (se 1 (by rfl) ⟨380906, by rfl⟩ : syracuseStep 507875 = 761813) B761813
theorem B507905 : Blo 334751 507905 := bstep (se 2 (by rfl) ⟨190464, by rfl⟩ : syracuseStep 507905 = 380929) B380929
theorem B507923 : Blo 334751 507923 := bstep (se 1 (by rfl) ⟨380942, by rfl⟩ : syracuseStep 507923 = 761885) B761885
theorem B507953 : Blo 334751 507953 := bstep (se 2 (by rfl) ⟨190482, by rfl⟩ : syracuseStep 507953 = 380965) B380965
theorem B507971 : Blo 334751 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B2441285 : Blo 334751 2441285 := bstep (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) B457741
theorem B376915 : Blo 334751 376915 := bstep (se 1 (by rfl) ⟨282686, by rfl⟩ : syracuseStep 376915 = 565373) B565373
theorem B508001 : Blo 334751 508001 := bstep (se 2 (by rfl) ⟨190500, by rfl⟩ : syracuseStep 508001 = 381001) B381001
theorem B508019 : Blo 334751 508019 := bstep (se 1 (by rfl) ⟨381014, by rfl⟩ : syracuseStep 508019 = 762029) B762029
theorem B508049 : Blo 334751 508049 := bstep (se 2 (by rfl) ⟨190518, by rfl⟩ : syracuseStep 508049 = 381037) B381037
theorem B1818787 : Blo 334751 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B508067 : Blo 334751 508067 := bstep (se 1 (by rfl) ⟨381050, by rfl⟩ : syracuseStep 508067 = 762101) B762101
theorem B508097 : Blo 334751 508097 := bstep (se 2 (by rfl) ⟨190536, by rfl⟩ : syracuseStep 508097 = 381073) B381073
theorem B1130705 : Blo 334751 1130705 := bstep (se 2 (by rfl) ⟨424014, by rfl⟩ : syracuseStep 1130705 = 848029) B848029
theorem B508115 : Blo 334751 508115 := bstep (se 1 (by rfl) ⟨381086, by rfl⟩ : syracuseStep 508115 = 762173) B762173
theorem B377059 : Blo 334751 377059 := bstep (se 1 (by rfl) ⟨282794, by rfl⟩ : syracuseStep 377059 = 565589) B565589
theorem B2769221 : Blo 334751 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B377203 : Blo 334751 377203 := bstep (se 1 (by rfl) ⟨282902, by rfl⟩ : syracuseStep 377203 = 565805) B565805
theorem B639409 : Blo 334751 639409 := bstep (se 2 (by rfl) ⟨239778, by rfl⟩ : syracuseStep 639409 = 479557) B479557
theorem B377347 : Blo 334751 377347 := bstep (se 1 (by rfl) ⟨283010, by rfl⟩ : syracuseStep 377347 = 566021) B566021
theorem B639569 : Blo 334751 639569 := bstep (se 2 (by rfl) ⟨239838, by rfl⟩ : syracuseStep 639569 = 479677) B479677
theorem B377491 : Blo 334751 377491 := bstep (se 1 (by rfl) ⟨283118, by rfl⟩ : syracuseStep 377491 = 566237) B566237
theorem B1131245 : Blo 334751 1131245 := bstep (se 3 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 1131245 = 424217) B424217
theorem B1131299 : Blo 334751 1131299 := bstep (se 1 (by rfl) ⟨848474, by rfl⟩ : syracuseStep 1131299 = 1696949) B1696949
theorem B377635 : Blo 334751 377635 := bstep (se 1 (by rfl) ⟨283226, by rfl⟩ : syracuseStep 377635 = 566453) B566453
theorem B377779 : Blo 334751 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B2147269 : Blo 334751 2147269 := bstep (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) B402613
theorem B639971 : Blo 334751 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B1131569 : Blo 334751 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B377923 : Blo 334751 377923 := bstep (se 1 (by rfl) ⟨283442, by rfl⟩ : syracuseStep 377923 = 566885) B566885
theorem B378067 : Blo 334751 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B1819909 : Blo 334751 1819909 := bstep (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) B341233
theorem B378211 : Blo 334751 378211 := bstep (se 1 (by rfl) ⟨283658, by rfl⟩ : syracuseStep 378211 = 567317) B567317
theorem B542065 : Blo 334751 542065 := bstep (se 2 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 542065 = 406549) B406549
theorem B476641 : Blo 334751 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B5817827 : Blo 334751 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B378355 : Blo 334751 378355 := bstep (se 1 (by rfl) ⟨283766, by rfl⟩ : syracuseStep 378355 = 567533) B567533
theorem B607747 : Blo 334751 607747 := bstep (se 1 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 607747 = 911621) B911621
theorem B1132109 : Blo 334751 1132109 := bstep (se 3 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 1132109 = 424541) B424541
theorem B1132163 : Blo 334751 1132163 := bstep (se 1 (by rfl) ⟨849122, by rfl⟩ : syracuseStep 1132163 = 1698245) B1698245
theorem B378499 : Blo 334751 378499 := bstep (se 1 (by rfl) ⟨283874, by rfl⟩ : syracuseStep 378499 = 567749) B567749
theorem B804611 : Blo 334751 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B378643 : Blo 334751 378643 := bstep (se 1 (by rfl) ⟨283982, by rfl⟩ : syracuseStep 378643 = 567965) B567965
theorem B968483 : Blo 334751 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B1722161 : Blo 334751 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B640867 : Blo 334751 640867 := bstep (se 1 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 640867 = 961301) B961301
theorem B20760461 : Blo 334751 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B1132433 : Blo 334751 1132433 := bstep (se 2 (by rfl) ⟨424662, by rfl⟩ : syracuseStep 1132433 = 849325) B849325
theorem B378787 : Blo 334751 378787 := bstep (se 1 (by rfl) ⟨284090, by rfl⟩ : syracuseStep 378787 = 568181) B568181
theorem B641027 : Blo 334751 641027 := bstep (se 1 (by rfl) ⟨480770, by rfl⟩ : syracuseStep 641027 = 961541) B961541
theorem B378931 : Blo 334751 378931 := bstep (se 1 (by rfl) ⟨284198, by rfl⟩ : syracuseStep 378931 = 568397) B568397
theorem B379075 : Blo 334751 379075 := bstep (se 1 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 379075 = 568613) B568613
theorem B477427 : Blo 334751 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B379219 : Blo 334751 379219 := bstep (se 1 (by rfl) ⟨284414, by rfl⟩ : syracuseStep 379219 = 568829) B568829
theorem B1132973 : Blo 334751 1132973 := bstep (se 3 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 1132973 = 424865) B424865
theorem B1133027 : Blo 334751 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B379363 : Blo 334751 379363 := bstep (se 1 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 379363 = 569045) B569045
theorem B510451 : Blo 334751 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B608771 : Blo 334751 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B1362467 : Blo 334751 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B379507 : Blo 334751 379507 := bstep (se 1 (by rfl) ⟨284630, by rfl⟩ : syracuseStep 379507 = 569261) B569261
theorem B477905 : Blo 334751 477905 := bstep (se 2 (by rfl) ⟨179214, by rfl⟩ : syracuseStep 477905 = 358429) B358429
theorem B1133297 : Blo 334751 1133297 := bstep (se 2 (by rfl) ⟨424986, by rfl⟩ : syracuseStep 1133297 = 849973) B849973
theorem B379651 : Blo 334751 379651 := bstep (se 1 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 379651 = 569477) B569477
theorem B609059 : Blo 334751 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B478019 : Blo 334751 478019 := bstep (se 1 (by rfl) ⟨358514, by rfl⟩ : syracuseStep 478019 = 717029) B717029
theorem B1919821 : Blo 334751 1919821 := bstep (se 3 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 1919821 = 719933) B719933
theorem B478099 : Blo 334751 478099 := bstep (se 1 (by rfl) ⟨358574, by rfl⟩ : syracuseStep 478099 = 717149) B717149
theorem B379795 : Blo 334751 379795 := bstep (se 1 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 379795 = 569693) B569693
theorem B379939 : Blo 334751 379939 := bstep (se 1 (by rfl) ⟨284954, by rfl⟩ : syracuseStep 379939 = 569909) B569909
theorem B642097 : Blo 334751 642097 := bstep (se 2 (by rfl) ⟨240786, by rfl⟩ : syracuseStep 642097 = 481573) B481573
theorem B380083 : Blo 334751 380083 := bstep (se 1 (by rfl) ⟨285062, by rfl⟩ : syracuseStep 380083 = 570125) B570125
theorem B3853493 : Blo 334751 3853493 := bstep (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) B361265
theorem B1133837 : Blo 334751 1133837 := bstep (se 3 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 1133837 = 425189) B425189
theorem B1133891 : Blo 334751 1133891 := bstep (se 1 (by rfl) ⟨850418, by rfl⟩ : syracuseStep 1133891 = 1700837) B1700837
theorem B380227 : Blo 334751 380227 := bstep (se 1 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 380227 = 570341) B570341
theorem B3231089 : Blo 334751 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B478657 : Blo 334751 478657 := bstep (se 2 (by rfl) ⟨179496, by rfl⟩ : syracuseStep 478657 = 358993) B358993
theorem B380371 : Blo 334751 380371 := bstep (se 1 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 380371 = 570557) B570557
theorem B577091 : Blo 334751 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1134161 : Blo 334751 1134161 := bstep (se 2 (by rfl) ⟨425310, by rfl⟩ : syracuseStep 1134161 = 850621) B850621
theorem B740945 : Blo 334751 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B380515 : Blo 334751 380515 := bstep (se 1 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 380515 = 570773) B570773
theorem B511699 : Blo 334751 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B610033 : Blo 334751 610033 := bstep (se 2 (by rfl) ⟨228762, by rfl⟩ : syracuseStep 610033 = 457525) B457525
theorem B380659 : Blo 334751 380659 := bstep (se 1 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 380659 = 570989) B570989
theorem B2084707 : Blo 334751 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B905069 : Blo 334751 905069 := bstep (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) B339401
theorem B380803 : Blo 334751 380803 := bstep (se 1 (by rfl) ⟨285602, by rfl⟩ : syracuseStep 380803 = 571205) B571205
theorem B1822661 : Blo 334751 1822661 := bstep (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) B341749
theorem B380947 : Blo 334751 380947 := bstep (se 1 (by rfl) ⟨285710, by rfl⟩ : syracuseStep 380947 = 571421) B571421
theorem B2871395 : Blo 334751 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B1134701 : Blo 334751 1134701 := bstep (se 3 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 1134701 = 425513) B425513
theorem B479363 : Blo 334751 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B1134755 : Blo 334751 1134755 := bstep (se 1 (by rfl) ⟨851066, by rfl⟩ : syracuseStep 1134755 = 1702133) B1702133
theorem B381091 : Blo 334751 381091 := bstep (se 1 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 381091 = 571637) B571637
theorem B905393 : Blo 334751 905393 := bstep (se 2 (by rfl) ⟨339522, by rfl⟩ : syracuseStep 905393 = 679045) B679045
theorem B1135025 : Blo 334751 1135025 := bstep (se 2 (by rfl) ⟨425634, by rfl⟩ : syracuseStep 1135025 = 851269) B851269
theorem B905795 : Blo 334751 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B578179 : Blo 334751 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B1233571 : Blo 334751 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B480001 : Blo 334751 480001 := bstep (se 2 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 480001 = 360001) B360001
theorem B1921805 : Blo 334751 1921805 := bstep (se 3 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 1921805 = 720677) B720677
theorem B480115 : Blo 334751 480115 := bstep (se 1 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 480115 = 720173) B720173
theorem B1430435 : Blo 334751 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B1135565 : Blo 334751 1135565 := bstep (se 3 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 1135565 = 425837) B425837
theorem B1135619 : Blo 334751 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B3232781 : Blo 334751 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B808003 : Blo 334751 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B808177 : Blo 334751 808177 := bstep (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) B606133
theorem B1135889 : Blo 334751 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B2807237 : Blo 334751 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B1922737 : Blo 334751 1922737 := bstep (se 2 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 1922737 = 1442053) B1442053
theorem B14636771 : Blo 334751 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B1136429 : Blo 334751 1136429 := bstep (se 3 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 1136429 = 426161) B426161
theorem B1136483 : Blo 334751 1136483 := bstep (se 1 (by rfl) ⟨852362, by rfl⟩ : syracuseStep 1136483 = 1704725) B1704725
theorem B513955 : Blo 334751 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B1464227 : Blo 334751 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1431665 : Blo 334751 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1136753 : Blo 334751 1136753 := bstep (se 2 (by rfl) ⟨426282, by rfl⟩ : syracuseStep 1136753 = 852565) B852565
theorem B481459 : Blo 334751 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B2316899 : Blo 334751 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B1137293 : Blo 334751 1137293 := bstep (se 3 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 1137293 = 426485) B426485
theorem B1137347 : Blo 334751 1137347 := bstep (se 1 (by rfl) ⟨853010, by rfl⟩ : syracuseStep 1137347 = 1706021) B1706021
theorem B1301197 : Blo 334751 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B514769 : Blo 334751 514769 := bstep (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) B386077
theorem B1137617 : Blo 334751 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B1924195 : Blo 334751 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B1138157 : Blo 334751 1138157 := bstep (se 3 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 1138157 = 426809) B426809
theorem B1138211 : Blo 334751 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B2743877 : Blo 334751 2743877 := bstep (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) B514477
theorem B1924721 : Blo 334751 1924721 := bstep (se 2 (by rfl) ⟨721770, by rfl⟩ : syracuseStep 1924721 = 1443541) B1443541
theorem B908995 : Blo 334751 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1138481 : Blo 334751 1138481 := bstep (se 2 (by rfl) ⟨426930, by rfl⟩ : syracuseStep 1138481 = 853861) B853861
theorem B1532195 : Blo 334751 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B1139021 : Blo 334751 1139021 := bstep (se 3 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 1139021 = 427133) B427133
theorem B1139075 : Blo 334751 1139075 := bstep (se 1 (by rfl) ⟨854306, by rfl⟩ : syracuseStep 1139075 = 1708613) B1708613
theorem B1434125 : Blo 334751 1434125 := bstep (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) B537797
theorem B1073699 : Blo 334751 1073699 := bstep (se 1 (by rfl) ⟨805274, by rfl⟩ : syracuseStep 1073699 = 1610549) B1610549
theorem B2155085 : Blo 334751 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B680579 : Blo 334751 680579 := bstep (se 1 (by rfl) ⟨510434, by rfl⟩ : syracuseStep 680579 = 1020869) B1020869
theorem B1139345 : Blo 334751 1139345 := bstep (se 2 (by rfl) ⟨427254, by rfl⟩ : syracuseStep 1139345 = 854509) B854509
theorem B2450189 : Blo 334751 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B910129 : Blo 334751 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B1696625 : Blo 334751 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B1926179 : Blo 334751 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B812099 : Blo 334751 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B681041 : Blo 334751 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B1139885 : Blo 334751 1139885 := bstep (se 3 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 1139885 = 427457) B427457
theorem B681137 : Blo 334751 681137 := bstep (se 2 (by rfl) ⟨255426, by rfl⟩ : syracuseStep 681137 = 510853) B510853
theorem B1271011 : Blo 334751 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B1139939 : Blo 334751 1139939 := bstep (se 1 (by rfl) ⟨854954, by rfl⟩ : syracuseStep 1139939 = 1709909) B1709909
theorem B1074467 : Blo 334751 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B812483 : Blo 334751 812483 := bstep (se 1 (by rfl) ⟨609362, by rfl⟩ : syracuseStep 812483 = 1218725) B1218725
theorem B1140209 : Blo 334751 1140209 := bstep (se 2 (by rfl) ⟨427578, by rfl⟩ : syracuseStep 1140209 = 855157) B855157
theorem B1631821 : Blo 334751 1631821 := bstep (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) B611933
theorem B910993 : Blo 334751 910993 := bstep (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) B683245
theorem B1074865 : Blo 334751 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B1074979 : Blo 334751 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B452513 : Blo 334751 452513 := bstep (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) B339385
theorem B813041 : Blo 334751 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B1140749 : Blo 334751 1140749 := bstep (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) B427781
theorem B1140803 : Blo 334751 1140803 := bstep (se 1 (by rfl) ⟨855602, by rfl⟩ : syracuseStep 1140803 = 1711205) B1711205
theorem B1698083 : Blo 334751 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B1042723 : Blo 334751 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1141073 : Blo 334751 1141073 := bstep (se 2 (by rfl) ⟨427902, by rfl⟩ : syracuseStep 1141073 = 855805) B855805
theorem B813539 : Blo 334751 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B1075697 : Blo 334751 1075697 := bstep (se 2 (by rfl) ⟨403386, by rfl⟩ : syracuseStep 1075697 = 806773) B806773
theorem B2746993 : Blo 334751 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B813731 : Blo 334751 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B453313 : Blo 334751 453313 := bstep (se 2 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 453313 = 339985) B339985
theorem B5073635 : Blo 334751 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1141613 : Blo 334751 1141613 := bstep (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) B428105
theorem B1928069 : Blo 334751 1928069 := bstep (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) B361513
theorem B1141667 : Blo 334751 1141667 := bstep (se 1 (by rfl) ⟨856250, by rfl⟩ : syracuseStep 1141667 = 1712501) B1712501
theorem B3828707 : Blo 334751 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B1076237 : Blo 334751 1076237 := bstep (se 3 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 1076237 = 403589) B403589
theorem B1698893 : Blo 334751 1698893 := bstep (se 3 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 1698893 = 637085) B637085
theorem B1141937 : Blo 334751 1141937 := bstep (se 2 (by rfl) ⟨428226, by rfl⟩ : syracuseStep 1141937 = 856453) B856453
theorem B1273229 : Blo 334751 1273229 := bstep (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) B477461
theorem B454081 : Blo 334751 454081 := bstep (se 2 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 454081 = 340561) B340561
theorem B1535537 : Blo 334751 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B454243 : Blo 334751 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B913027 : Blo 334751 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B3272333 : Blo 334751 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B847523 : Blo 334751 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B913069 : Blo 334751 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B716465 : Blo 334751 716465 := bstep (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) B537349
theorem B4419269 : Blo 334751 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B1142477 : Blo 334751 1142477 := bstep (se 3 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 1142477 = 428429) B428429
theorem B1142531 : Blo 334751 1142531 := bstep (se 1 (by rfl) ⟨856898, by rfl⟩ : syracuseStep 1142531 = 1713797) B1713797
theorem B2420549 : Blo 334751 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B1830725 : Blo 334751 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B1830853 : Blo 334751 1830853 := bstep (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) B343285
theorem B2879459 : Blo 334751 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B1142801 : Blo 334751 1142801 := bstep (se 2 (by rfl) ⟨428550, by rfl⟩ : syracuseStep 1142801 = 857101) B857101
theorem B717329 : Blo 334751 717329 := bstep (se 2 (by rfl) ⟨268998, by rfl⟩ : syracuseStep 717329 = 537997) B537997
theorem B848465 : Blo 334751 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B848515 : Blo 334751 848515 := bstep (se 1 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 848515 = 1272773) B1272773
theorem B2159237 : Blo 334751 2159237 := bstep (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) B404857
theorem B848657 : Blo 334751 848657 := bstep (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) B636493
theorem B1438499 : Blo 334751 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B1078157 : Blo 334751 1078157 := bstep (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) B404309
theorem B357571 : Blo 334751 357571 := bstep (se 1 (by rfl) ⟨268178, by rfl⟩ : syracuseStep 357571 = 536357) B536357
theorem B2454725 : Blo 334751 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B2553443 : Blo 334751 2553443 := bstep (se 1 (by rfl) ⟨1915082, by rfl⟩ : syracuseStep 2553443 = 3830165) B3830165
theorem B849649 : Blo 334751 849649 := bstep (se 2 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 849649 = 637237) B637237
theorem B718627 : Blo 334751 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B423731 : Blo 334751 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B1701809 : Blo 334751 1701809 := bstep (se 2 (by rfl) ⟨638178, by rfl⟩ : syracuseStep 1701809 = 1276357) B1276357
theorem B1734641 : Blo 334751 1734641 := bstep (se 2 (by rfl) ⟨650490, by rfl⟩ : syracuseStep 1734641 = 1300981) B1300981
theorem B849923 : Blo 334751 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B915491 : Blo 334751 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B555155 : Blo 334751 555155 := bstep (se 1 (by rfl) ⟨416366, by rfl⟩ : syracuseStep 555155 = 832733) B832733
theorem B850115 : Blo 334751 850115 := bstep (se 1 (by rfl) ⟨637586, by rfl⟩ : syracuseStep 850115 = 1275173) B1275173
theorem B2291939 : Blo 334751 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B1276145 : Blo 334751 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B358835 : Blo 334751 358835 := bstep (se 1 (by rfl) ⟨269126, by rfl⟩ : syracuseStep 358835 = 538253) B538253
theorem B424435 : Blo 334751 424435 := bstep (se 1 (by rfl) ⟨318326, by rfl⟩ : syracuseStep 424435 = 636653) B636653
theorem B2095651 : Blo 334751 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B424531 : Blo 334751 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B3505123 : Blo 334751 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B719857 : Blo 334751 719857 := bstep (se 2 (by rfl) ⟨269946, by rfl⟩ : syracuseStep 719857 = 539893) B539893
theorem B1080337 : Blo 334751 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B425027 : Blo 334751 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B851057 : Blo 334751 851057 := bstep (se 2 (by rfl) ⟨319146, by rfl⟩ : syracuseStep 851057 = 638293) B638293
theorem B851107 : Blo 334751 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B359587 : Blo 334751 359587 := bstep (se 1 (by rfl) ⟨269690, by rfl⟩ : syracuseStep 359587 = 539381) B539381
theorem B1080515 : Blo 334751 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B851249 : Blo 334751 851249 := bstep (se 2 (by rfl) ⟨319218, by rfl⟩ : syracuseStep 851249 = 638437) B638437
theorem B1703267 : Blo 334751 1703267 := bstep (se 1 (by rfl) ⟨1277450, by rfl⟩ : syracuseStep 1703267 = 2554901) B2554901
theorem B1441165 : Blo 334751 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B3079565 : Blo 334751 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B720515 : Blo 334751 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B1277603 : Blo 334751 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B425731 : Blo 334751 425731 := bstep (se 1 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 425731 = 638597) B638597
theorem B753425 : Blo 334751 753425 := bstep (se 2 (by rfl) ⟨282534, by rfl⟩ : syracuseStep 753425 = 565069) B565069
theorem B753443 : Blo 334751 753443 := bstep (se 1 (by rfl) ⟨565082, by rfl⟩ : syracuseStep 753443 = 1130165) B1130165
theorem B425827 : Blo 334751 425827 := bstep (se 1 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 425827 = 638741) B638741
theorem B491609 : Blo 334751 491609 := bstep (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) B368707
theorem B753803 : Blo 334751 753803 := bstep (se 1 (by rfl) ⟨565352, by rfl⟩ : syracuseStep 753803 = 1130705) B1130705
theorem B753857 : Blo 334751 753857 := bstep (se 2 (by rfl) ⟨282696, by rfl⟩ : syracuseStep 753857 = 565393) B565393
theorem B2425049 : Blo 334751 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B1442123 : Blo 334751 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1278301 : Blo 334751 1278301 := bstep (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) B479363
theorem B426379 : Blo 334751 426379 := bstep (se 1 (by rfl) ⟨319784, by rfl⟩ : syracuseStep 426379 = 639569) B639569
theorem B754073 : Blo 334751 754073 := bstep (se 2 (by rfl) ⟨282777, by rfl⟩ : syracuseStep 754073 = 565555) B565555
theorem B852403 : Blo 334751 852403 := bstep (se 1 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 852403 = 1278605) B1278605
theorem B754163 : Blo 334751 754163 := bstep (se 1 (by rfl) ⟨565622, by rfl⟩ : syracuseStep 754163 = 1131245) B1131245
theorem B754199 : Blo 334751 754199 := bstep (se 1 (by rfl) ⟨565649, by rfl⟩ : syracuseStep 754199 = 1131299) B1131299
theorem B852545 : Blo 334751 852545 := bstep (se 2 (by rfl) ⟨319704, by rfl⟩ : syracuseStep 852545 = 639409) B639409
theorem B721523 : Blo 334751 721523 := bstep (se 1 (by rfl) ⟨541142, by rfl⟩ : syracuseStep 721523 = 1082285) B1082285
theorem B426647 : Blo 334751 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B754379 : Blo 334751 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B754433 : Blo 334751 754433 := bstep (se 2 (by rfl) ⟨282912, by rfl⟩ : syracuseStep 754433 = 565825) B565825
theorem B754649 : Blo 334751 754649 := bstep (se 2 (by rfl) ⟨282993, by rfl⟩ : syracuseStep 754649 = 565987) B565987
theorem B754739 : Blo 334751 754739 := bstep (se 1 (by rfl) ⟨566054, by rfl⟩ : syracuseStep 754739 = 1132109) B1132109
theorem B1213505 : Blo 334751 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B754775 : Blo 334751 754775 := bstep (se 1 (by rfl) ⟨566081, by rfl⟩ : syracuseStep 754775 = 1132163) B1132163
theorem B1148107 : Blo 334751 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B754955 : Blo 334751 754955 := bstep (se 1 (by rfl) ⟨566216, by rfl⟩ : syracuseStep 754955 = 1132433) B1132433
theorem B755009 : Blo 334751 755009 := bstep (se 2 (by rfl) ⟨283128, by rfl⟩ : syracuseStep 755009 = 566257) B566257
theorem B427351 : Blo 334751 427351 := bstep (se 1 (by rfl) ⟨320513, by rfl⟩ : syracuseStep 427351 = 641027) B641027
theorem B1148381 : Blo 334751 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B755225 : Blo 334751 755225 := bstep (se 2 (by rfl) ⟨283209, by rfl⟩ : syracuseStep 755225 = 566419) B566419
theorem B1279577 : Blo 334751 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B755315 : Blo 334751 755315 := bstep (se 1 (by rfl) ⟨566486, by rfl⟩ : syracuseStep 755315 = 1132973) B1132973
theorem B755351 : Blo 334751 755351 := bstep (se 1 (by rfl) ⟨566513, by rfl⟩ : syracuseStep 755351 = 1133027) B1133027
theorem B2426545 : Blo 334751 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B4130509 : Blo 334751 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B853811 : Blo 334751 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B722753 : Blo 334751 722753 := bstep (se 2 (by rfl) ⟨271032, by rfl⟩ : syracuseStep 722753 = 542065) B542065
theorem B755531 : Blo 334751 755531 := bstep (se 1 (by rfl) ⟨566648, by rfl⟩ : syracuseStep 755531 = 1133297) B1133297
theorem B755585 : Blo 334751 755585 := bstep (se 2 (by rfl) ⟨283344, by rfl⟩ : syracuseStep 755585 = 566689) B566689
theorem B1705859 : Blo 334751 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B15599537 : Blo 334751 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B460747 : Blo 334751 460747 := bstep (se 1 (by rfl) ⟨345560, by rfl⟩ : syracuseStep 460747 = 691121) B691121
theorem B755801 : Blo 334751 755801 := bstep (se 2 (by rfl) ⟨283425, by rfl⟩ : syracuseStep 755801 = 566851) B566851
theorem B3835997 : Blo 334751 3835997 := bstep (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) B1438499
theorem B1837187 : Blo 334751 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B755891 : Blo 334751 755891 := bstep (se 1 (by rfl) ⟨566918, by rfl⟩ : syracuseStep 755891 = 1133837) B1133837
theorem B1214657 : Blo 334751 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B755927 : Blo 334751 755927 := bstep (se 1 (by rfl) ⟨566945, by rfl⟩ : syracuseStep 755927 = 1133891) B1133891
theorem B854347 : Blo 334751 854347 := bstep (se 1 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 854347 = 1281521) B1281521
theorem B756107 : Blo 334751 756107 := bstep (se 1 (by rfl) ⟨567080, by rfl⟩ : syracuseStep 756107 = 1134161) B1134161
theorem B756161 : Blo 334751 756161 := bstep (se 2 (by rfl) ⟨283560, by rfl⟩ : syracuseStep 756161 = 567121) B567121
theorem B854489 : Blo 334751 854489 := bstep (se 2 (by rfl) ⟨320433, by rfl⟩ : syracuseStep 854489 = 640867) B640867
theorem B2722405 : Blo 334751 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B1215107 : Blo 334751 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B756377 : Blo 334751 756377 := bstep (se 2 (by rfl) ⟨283641, by rfl⟩ : syracuseStep 756377 = 567283) B567283
theorem B920267 : Blo 334751 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B756467 : Blo 334751 756467 := bstep (se 1 (by rfl) ⟨567350, by rfl⟩ : syracuseStep 756467 = 1134701) B1134701
theorem B6195973 : Blo 334751 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B756503 : Blo 334751 756503 := bstep (se 1 (by rfl) ⟨567377, by rfl⟩ : syracuseStep 756503 = 1134755) B1134755
theorem B5442349 : Blo 334751 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B1444787 : Blo 334751 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B756683 : Blo 334751 756683 := bstep (se 1 (by rfl) ⟨567512, by rfl⟩ : syracuseStep 756683 = 1135025) B1135025
theorem B756737 : Blo 334751 756737 := bstep (se 2 (by rfl) ⟨283776, by rfl⟩ : syracuseStep 756737 = 567553) B567553
theorem B1281203 : Blo 334751 1281203 := bstep (se 1 (by rfl) ⟨960902, by rfl⟩ : syracuseStep 1281203 = 1921805) B1921805
theorem B1281217 : Blo 334751 1281217 := bstep (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) B960913
theorem B756953 : Blo 334751 756953 := bstep (se 2 (by rfl) ⟨283857, by rfl⟩ : syracuseStep 756953 = 567715) B567715
theorem B953623 : Blo 334751 953623 := bstep (se 1 (by rfl) ⟨715217, by rfl⟩ : syracuseStep 953623 = 1430435) B1430435
theorem B855319 : Blo 334751 855319 := bstep (se 1 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 855319 = 1282979) B1282979
theorem B757043 : Blo 334751 757043 := bstep (se 1 (by rfl) ⟨567782, by rfl⟩ : syracuseStep 757043 = 1135565) B1135565
theorem B757079 : Blo 334751 757079 := bstep (se 1 (by rfl) ⟨567809, by rfl⟩ : syracuseStep 757079 = 1135619) B1135619
theorem B757259 : Blo 334751 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B757313 : Blo 334751 757313 := bstep (se 2 (by rfl) ⟨283992, by rfl⟩ : syracuseStep 757313 = 567985) B567985
theorem B855755 : Blo 334751 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B2559761 : Blo 334751 2559761 := bstep (se 2 (by rfl) ⟨959910, by rfl⟩ : syracuseStep 2559761 = 1919821) B1919821
theorem B757529 : Blo 334751 757529 := bstep (se 2 (by rfl) ⟨284073, by rfl⟩ : syracuseStep 757529 = 568147) B568147
theorem B757619 : Blo 334751 757619 := bstep (se 1 (by rfl) ⟨568214, by rfl⟩ : syracuseStep 757619 = 1136429) B1136429
theorem B757655 : Blo 334751 757655 := bstep (se 1 (by rfl) ⟨568241, by rfl⟩ : syracuseStep 757655 = 1136483) B1136483
theorem B856129 : Blo 334751 856129 := bstep (se 2 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 856129 = 642097) B642097
theorem B954443 : Blo 334751 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B757835 : Blo 334751 757835 := bstep (se 1 (by rfl) ⟨568376, by rfl⟩ : syracuseStep 757835 = 1136753) B1136753
theorem B757889 : Blo 334751 757889 := bstep (se 2 (by rfl) ⟨284208, by rfl⟩ : syracuseStep 757889 = 568417) B568417
theorem B758105 : Blo 334751 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B1446275 : Blo 334751 1446275 := bstep (se 1 (by rfl) ⟨1084706, by rfl⟩ : syracuseStep 1446275 = 2169413) B2169413
theorem B1544599 : Blo 334751 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B758195 : Blo 334751 758195 := bstep (se 1 (by rfl) ⟨568646, by rfl⟩ : syracuseStep 758195 = 1137293) B1137293
theorem B758231 : Blo 334751 758231 := bstep (se 1 (by rfl) ⟨568673, by rfl⟩ : syracuseStep 758231 = 1137347) B1137347
theorem B1151581 : Blo 334751 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B758411 : Blo 334751 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B856727 : Blo 334751 856727 := bstep (se 1 (by rfl) ⟨642545, by rfl⟩ : syracuseStep 856727 = 1285091) B1285091
theorem B758465 : Blo 334751 758465 := bstep (se 2 (by rfl) ⟨284424, by rfl⟩ : syracuseStep 758465 = 568849) B568849
theorem B4854593 : Blo 334751 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1217369 : Blo 334751 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1217425 : Blo 334751 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B758681 : Blo 334751 758681 := bstep (se 2 (by rfl) ⟨284505, by rfl⟩ : syracuseStep 758681 = 569011) B569011
theorem B922571 : Blo 334751 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B758771 : Blo 334751 758771 := bstep (se 1 (by rfl) ⟨569078, by rfl⟩ : syracuseStep 758771 = 1138157) B1138157
theorem B758807 : Blo 334751 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B1283147 : Blo 334751 1283147 := bstep (se 1 (by rfl) ⟨962360, by rfl⟩ : syracuseStep 1283147 = 1924721) B1924721
theorem B1283161 : Blo 334751 1283161 := bstep (se 2 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 1283161 = 962371) B962371
theorem B758987 : Blo 334751 758987 := bstep (se 1 (by rfl) ⟨569240, by rfl⟩ : syracuseStep 758987 = 1138481) B1138481
theorem B759041 : Blo 334751 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B759257 : Blo 334751 759257 := bstep (se 2 (by rfl) ⟨284721, by rfl⟩ : syracuseStep 759257 = 569443) B569443
theorem B1709585 : Blo 334751 1709585 := bstep (se 2 (by rfl) ⟨641094, by rfl⟩ : syracuseStep 1709585 = 1282189) B1282189
theorem B1021463 : Blo 334751 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B759347 : Blo 334751 759347 := bstep (se 1 (by rfl) ⟨569510, by rfl⟩ : syracuseStep 759347 = 1139021) B1139021
theorem B759383 : Blo 334751 759383 := bstep (se 1 (by rfl) ⟨569537, by rfl⟩ : syracuseStep 759383 = 1139075) B1139075
theorem B1709747 : Blo 334751 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B759563 : Blo 334751 759563 := bstep (se 1 (by rfl) ⟨569672, by rfl⟩ : syracuseStep 759563 = 1139345) B1139345
theorem B759617 : Blo 334751 759617 := bstep (se 2 (by rfl) ⟨284856, by rfl⟩ : syracuseStep 759617 = 569713) B569713
theorem B1284119 : Blo 334751 1284119 := bstep (se 1 (by rfl) ⟨963089, by rfl⟩ : syracuseStep 1284119 = 1926179) B1926179
theorem B759833 : Blo 334751 759833 := bstep (se 2 (by rfl) ⟨284937, by rfl⟩ : syracuseStep 759833 = 569875) B569875
theorem B2758691 : Blo 334751 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B759923 : Blo 334751 759923 := bstep (se 1 (by rfl) ⟨569942, by rfl⟩ : syracuseStep 759923 = 1139885) B1139885
theorem B759959 : Blo 334751 759959 := bstep (se 1 (by rfl) ⟨569969, by rfl⟩ : syracuseStep 759959 = 1139939) B1139939
theorem B1644761 : Blo 334751 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B9672965 : Blo 334751 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B760139 : Blo 334751 760139 := bstep (se 1 (by rfl) ⟨570104, by rfl⟩ : syracuseStep 760139 = 1140209) B1140209
theorem B760193 : Blo 334751 760193 := bstep (se 2 (by rfl) ⟨285072, by rfl⟩ : syracuseStep 760193 = 570145) B570145
theorem B4004275 : Blo 334751 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B956893 : Blo 334751 956893 := bstep (se 3 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 956893 = 358835) B358835
theorem B596531 : Blo 334751 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B760409 : Blo 334751 760409 := bstep (se 2 (by rfl) ⟨285153, by rfl⟩ : syracuseStep 760409 = 570307) B570307
theorem B760499 : Blo 334751 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B760535 : Blo 334751 760535 := bstep (se 1 (by rfl) ⟨570401, by rfl⟩ : syracuseStep 760535 = 1140803) B1140803
theorem B4922117 : Blo 334751 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B760715 : Blo 334751 760715 := bstep (se 1 (by rfl) ⟨570536, by rfl⟩ : syracuseStep 760715 = 1141073) B1141073
theorem B334763 : Blo 334751 334763 := bstep (se 1 (by rfl) ⟨251072, by rfl⟩ : syracuseStep 334763 = 502145) B502145
theorem B334775 : Blo 334751 334775 := bstep (se 1 (by rfl) ⟨251081, by rfl⟩ : syracuseStep 334775 = 502163) B502163
theorem B760769 : Blo 334751 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B334795 : Blo 334751 334795 := bstep (se 1 (by rfl) ⟨251096, by rfl⟩ : syracuseStep 334795 = 502193) B502193
theorem B334807 : Blo 334751 334807 := bstep (se 1 (by rfl) ⟨251105, by rfl⟩ : syracuseStep 334807 = 502211) B502211
theorem B334827 : Blo 334751 334827 := bstep (se 1 (by rfl) ⟨251120, by rfl⟩ : syracuseStep 334827 = 502241) B502241
theorem B334839 : Blo 334751 334839 := bstep (se 1 (by rfl) ⟨251129, by rfl⟩ : syracuseStep 334839 = 502259) B502259
theorem B334859 : Blo 334751 334859 := bstep (se 1 (by rfl) ⟨251144, by rfl⟩ : syracuseStep 334859 = 502289) B502289
theorem B334871 : Blo 334751 334871 := bstep (se 1 (by rfl) ⟨251153, by rfl⟩ : syracuseStep 334871 = 502307) B502307
theorem B334891 : Blo 334751 334891 := bstep (se 1 (by rfl) ⟨251168, by rfl⟩ : syracuseStep 334891 = 502337) B502337
theorem B334903 : Blo 334751 334903 := bstep (se 1 (by rfl) ⟨251177, by rfl⟩ : syracuseStep 334903 = 502355) B502355
theorem B334923 : Blo 334751 334923 := bstep (se 1 (by rfl) ⟨251192, by rfl⟩ : syracuseStep 334923 = 502385) B502385
theorem B334935 : Blo 334751 334935 := bstep (se 1 (by rfl) ⟨251201, by rfl⟩ : syracuseStep 334935 = 502403) B502403
theorem B2169949 : Blo 334751 2169949 := bstep (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) B813731
theorem B334955 : Blo 334751 334955 := bstep (se 1 (by rfl) ⟨251216, by rfl⟩ : syracuseStep 334955 = 502433) B502433
theorem B334967 : Blo 334751 334967 := bstep (se 1 (by rfl) ⟨251225, by rfl⟩ : syracuseStep 334967 = 502451) B502451
theorem B334987 : Blo 334751 334987 := bstep (se 1 (by rfl) ⟨251240, by rfl⟩ : syracuseStep 334987 = 502481) B502481
theorem B334999 : Blo 334751 334999 := bstep (se 1 (by rfl) ⟨251249, by rfl⟩ : syracuseStep 334999 = 502499) B502499
theorem B760985 : Blo 334751 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B335019 : Blo 334751 335019 := bstep (se 1 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 335019 = 502529) B502529
theorem B335031 : Blo 334751 335031 := bstep (se 1 (by rfl) ⟨251273, by rfl⟩ : syracuseStep 335031 = 502547) B502547
theorem B335051 : Blo 334751 335051 := bstep (se 1 (by rfl) ⟨251288, by rfl⟩ : syracuseStep 335051 = 502577) B502577
theorem B335063 : Blo 334751 335063 := bstep (se 1 (by rfl) ⟨251297, by rfl⟩ : syracuseStep 335063 = 502595) B502595
theorem B335083 : Blo 334751 335083 := bstep (se 1 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 335083 = 502625) B502625
theorem B761075 : Blo 334751 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B335095 : Blo 334751 335095 := bstep (se 1 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 335095 = 502643) B502643
theorem B1285379 : Blo 334751 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B335115 : Blo 334751 335115 := bstep (se 1 (by rfl) ⟨251336, by rfl⟩ : syracuseStep 335115 = 502673) B502673
theorem B335127 : Blo 334751 335127 := bstep (se 1 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 335127 = 502691) B502691
theorem B761111 : Blo 334751 761111 := bstep (se 1 (by rfl) ⟨570833, by rfl⟩ : syracuseStep 761111 = 1141667) B1141667
theorem B335147 : Blo 334751 335147 := bstep (se 1 (by rfl) ⟨251360, by rfl⟩ : syracuseStep 335147 = 502721) B502721
theorem B335159 : Blo 334751 335159 := bstep (se 1 (by rfl) ⟨251369, by rfl⟩ : syracuseStep 335159 = 502739) B502739
theorem B335179 : Blo 334751 335179 := bstep (se 1 (by rfl) ⟨251384, by rfl⟩ : syracuseStep 335179 = 502769) B502769
theorem B335191 : Blo 334751 335191 := bstep (se 1 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 335191 = 502787) B502787
theorem B335211 : Blo 334751 335211 := bstep (se 1 (by rfl) ⟨251408, by rfl⟩ : syracuseStep 335211 = 502817) B502817
theorem B335223 : Blo 334751 335223 := bstep (se 1 (by rfl) ⟨251417, by rfl⟩ : syracuseStep 335223 = 502835) B502835
theorem B335243 : Blo 334751 335243 := bstep (se 1 (by rfl) ⟨251432, by rfl⟩ : syracuseStep 335243 = 502865) B502865
theorem B335255 : Blo 334751 335255 := bstep (se 1 (by rfl) ⟨251441, by rfl⟩ : syracuseStep 335255 = 502883) B502883
theorem B335275 : Blo 334751 335275 := bstep (se 1 (by rfl) ⟨251456, by rfl⟩ : syracuseStep 335275 = 502913) B502913
theorem B335287 : Blo 334751 335287 := bstep (se 1 (by rfl) ⟨251465, by rfl⟩ : syracuseStep 335287 = 502931) B502931
theorem B335307 : Blo 334751 335307 := bstep (se 1 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 335307 = 502961) B502961
theorem B761291 : Blo 334751 761291 := bstep (se 1 (by rfl) ⟨570968, by rfl⟩ : syracuseStep 761291 = 1141937) B1141937
theorem B335319 : Blo 334751 335319 := bstep (se 1 (by rfl) ⟨251489, by rfl⟩ : syracuseStep 335319 = 502979) B502979
theorem B335339 : Blo 334751 335339 := bstep (se 1 (by rfl) ⟨251504, by rfl⟩ : syracuseStep 335339 = 503009) B503009
theorem B335351 : Blo 334751 335351 := bstep (se 1 (by rfl) ⟨251513, by rfl⟩ : syracuseStep 335351 = 503027) B503027
theorem B761345 : Blo 334751 761345 := bstep (se 2 (by rfl) ⟨285504, by rfl⟩ : syracuseStep 761345 = 571009) B571009
theorem B335371 : Blo 334751 335371 := bstep (se 1 (by rfl) ⟨251528, by rfl⟩ : syracuseStep 335371 = 503057) B503057
theorem B335383 : Blo 334751 335383 := bstep (se 1 (by rfl) ⟨251537, by rfl⟩ : syracuseStep 335383 = 503075) B503075
theorem B335403 : Blo 334751 335403 := bstep (se 1 (by rfl) ⟨251552, by rfl⟩ : syracuseStep 335403 = 503105) B503105
theorem B335415 : Blo 334751 335415 := bstep (se 1 (by rfl) ⟨251561, by rfl⟩ : syracuseStep 335415 = 503123) B503123
theorem B2563649 : Blo 334751 2563649 := bstep (se 2 (by rfl) ⟨961368, by rfl⟩ : syracuseStep 2563649 = 1922737) B1922737
theorem B335435 : Blo 334751 335435 := bstep (se 1 (by rfl) ⟨251576, by rfl⟩ : syracuseStep 335435 = 503153) B503153
theorem B1711691 : Blo 334751 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B335447 : Blo 334751 335447 := bstep (se 1 (by rfl) ⟨251585, by rfl⟩ : syracuseStep 335447 = 503171) B503171
theorem B335467 : Blo 334751 335467 := bstep (se 1 (by rfl) ⟨251600, by rfl⟩ : syracuseStep 335467 = 503201) B503201
theorem B335479 : Blo 334751 335479 := bstep (se 1 (by rfl) ⟨251609, by rfl⟩ : syracuseStep 335479 = 503219) B503219
theorem B2301571 : Blo 334751 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B335499 : Blo 334751 335499 := bstep (se 1 (by rfl) ⟨251624, by rfl⟩ : syracuseStep 335499 = 503249) B503249
theorem B335511 : Blo 334751 335511 := bstep (se 1 (by rfl) ⟨251633, by rfl⟩ : syracuseStep 335511 = 503267) B503267
theorem B335531 : Blo 334751 335531 := bstep (se 1 (by rfl) ⟨251648, by rfl⟩ : syracuseStep 335531 = 503297) B503297
theorem B335543 : Blo 334751 335543 := bstep (se 1 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 335543 = 503315) B503315
theorem B335563 : Blo 334751 335563 := bstep (se 1 (by rfl) ⟨251672, by rfl⟩ : syracuseStep 335563 = 503345) B503345
theorem B1023691 : Blo 334751 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B335575 : Blo 334751 335575 := bstep (se 1 (by rfl) ⟨251681, by rfl⟩ : syracuseStep 335575 = 503363) B503363
theorem B958169 : Blo 334751 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B761561 : Blo 334751 761561 := bstep (se 2 (by rfl) ⟨285585, by rfl⟩ : syracuseStep 761561 = 571171) B571171
theorem B335595 : Blo 334751 335595 := bstep (se 1 (by rfl) ⟨251696, by rfl⟩ : syracuseStep 335595 = 503393) B503393
theorem B335607 : Blo 334751 335607 := bstep (se 1 (by rfl) ⟨251705, by rfl⟩ : syracuseStep 335607 = 503411) B503411
theorem B335627 : Blo 334751 335627 := bstep (se 1 (by rfl) ⟨251720, by rfl⟩ : syracuseStep 335627 = 503441) B503441
theorem B565015 : Blo 334751 565015 := bstep (se 1 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 565015 = 847523) B847523
theorem B335639 : Blo 334751 335639 := bstep (se 1 (by rfl) ⟨251729, by rfl⟩ : syracuseStep 335639 = 503459) B503459
theorem B335659 : Blo 334751 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B761651 : Blo 334751 761651 := bstep (se 1 (by rfl) ⟨571238, by rfl⟩ : syracuseStep 761651 = 1142477) B1142477
theorem B335671 : Blo 334751 335671 := bstep (se 1 (by rfl) ⟨251753, by rfl⟩ : syracuseStep 335671 = 503507) B503507
theorem B335691 : Blo 334751 335691 := bstep (se 1 (by rfl) ⟨251768, by rfl⟩ : syracuseStep 335691 = 503537) B503537
theorem B335703 : Blo 334751 335703 := bstep (se 1 (by rfl) ⟨251777, by rfl⟩ : syracuseStep 335703 = 503555) B503555
theorem B761687 : Blo 334751 761687 := bstep (se 1 (by rfl) ⟨571265, by rfl⟩ : syracuseStep 761687 = 1142531) B1142531
theorem B335723 : Blo 334751 335723 := bstep (se 1 (by rfl) ⟨251792, by rfl⟩ : syracuseStep 335723 = 503585) B503585
theorem B335735 : Blo 334751 335735 := bstep (se 1 (by rfl) ⟨251801, by rfl⟩ : syracuseStep 335735 = 503603) B503603
theorem B1613699 : Blo 334751 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B1220483 : Blo 334751 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B335755 : Blo 334751 335755 := bstep (se 1 (by rfl) ⟨251816, by rfl⟩ : syracuseStep 335755 = 503633) B503633
theorem B335767 : Blo 334751 335767 := bstep (se 1 (by rfl) ⟨251825, by rfl⟩ : syracuseStep 335767 = 503651) B503651
theorem B335787 : Blo 334751 335787 := bstep (se 1 (by rfl) ⟨251840, by rfl⟩ : syracuseStep 335787 = 503681) B503681
theorem B335799 : Blo 334751 335799 := bstep (se 1 (by rfl) ⟨251849, by rfl⟩ : syracuseStep 335799 = 503699) B503699
theorem B335819 : Blo 334751 335819 := bstep (se 1 (by rfl) ⟨251864, by rfl⟩ : syracuseStep 335819 = 503729) B503729
theorem B335831 : Blo 334751 335831 := bstep (se 1 (by rfl) ⟨251873, by rfl⟩ : syracuseStep 335831 = 503747) B503747
theorem B335851 : Blo 334751 335851 := bstep (se 1 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 335851 = 503777) B503777
theorem B335863 : Blo 334751 335863 := bstep (se 1 (by rfl) ⟨251897, by rfl⟩ : syracuseStep 335863 = 503795) B503795
theorem B335883 : Blo 334751 335883 := bstep (se 1 (by rfl) ⟨251912, by rfl⟩ : syracuseStep 335883 = 503825) B503825
theorem B761867 : Blo 334751 761867 := bstep (se 1 (by rfl) ⟨571400, by rfl⟩ : syracuseStep 761867 = 1142801) B1142801
theorem B335895 : Blo 334751 335895 := bstep (se 1 (by rfl) ⟨251921, by rfl⟩ : syracuseStep 335895 = 503843) B503843
theorem B335915 : Blo 334751 335915 := bstep (se 1 (by rfl) ⟨251936, by rfl⟩ : syracuseStep 335915 = 503873) B503873
theorem B335927 : Blo 334751 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B761921 : Blo 334751 761921 := bstep (se 2 (by rfl) ⟨285720, by rfl⟩ : syracuseStep 761921 = 571441) B571441
theorem B335947 : Blo 334751 335947 := bstep (se 1 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 335947 = 503921) B503921
theorem B335959 : Blo 334751 335959 := bstep (se 1 (by rfl) ⟨251969, by rfl⟩ : syracuseStep 335959 = 503939) B503939
theorem B335979 : Blo 334751 335979 := bstep (se 1 (by rfl) ⟨251984, by rfl⟩ : syracuseStep 335979 = 503969) B503969
theorem B335991 : Blo 334751 335991 := bstep (se 1 (by rfl) ⟨251993, by rfl⟩ : syracuseStep 335991 = 503987) B503987
theorem B336011 : Blo 334751 336011 := bstep (se 1 (by rfl) ⟨252008, by rfl⟩ : syracuseStep 336011 = 504017) B504017
theorem B336023 : Blo 334751 336023 := bstep (se 1 (by rfl) ⟨252017, by rfl⟩ : syracuseStep 336023 = 504035) B504035
theorem B336043 : Blo 334751 336043 := bstep (se 1 (by rfl) ⟨252032, by rfl⟩ : syracuseStep 336043 = 504065) B504065
theorem B1974451 : Blo 334751 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B336055 : Blo 334751 336055 := bstep (se 1 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 336055 = 504083) B504083
theorem B336075 : Blo 334751 336075 := bstep (se 1 (by rfl) ⟨252056, by rfl⟩ : syracuseStep 336075 = 504113) B504113
theorem B336087 : Blo 334751 336087 := bstep (se 1 (by rfl) ⟨252065, by rfl⟩ : syracuseStep 336087 = 504131) B504131
theorem B336107 : Blo 334751 336107 := bstep (se 1 (by rfl) ⟨252080, by rfl⟩ : syracuseStep 336107 = 504161) B504161
theorem B336119 : Blo 334751 336119 := bstep (se 1 (by rfl) ⟨252089, by rfl⟩ : syracuseStep 336119 = 504179) B504179
theorem B336139 : Blo 334751 336139 := bstep (se 1 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 336139 = 504209) B504209
theorem B336151 : Blo 334751 336151 := bstep (se 1 (by rfl) ⟨252113, by rfl⟩ : syracuseStep 336151 = 504227) B504227
theorem B762137 : Blo 334751 762137 := bstep (se 2 (by rfl) ⟨285801, by rfl⟩ : syracuseStep 762137 = 571603) B571603
theorem B336171 : Blo 334751 336171 := bstep (se 1 (by rfl) ⟨252128, by rfl⟩ : syracuseStep 336171 = 504257) B504257
theorem B336183 : Blo 334751 336183 := bstep (se 1 (by rfl) ⟨252137, by rfl⟩ : syracuseStep 336183 = 504275) B504275
theorem B336203 : Blo 334751 336203 := bstep (se 1 (by rfl) ⟨252152, by rfl⟩ : syracuseStep 336203 = 504305) B504305
theorem B336215 : Blo 334751 336215 := bstep (se 1 (by rfl) ⟨252161, by rfl⟩ : syracuseStep 336215 = 504323) B504323
theorem B336235 : Blo 334751 336235 := bstep (se 1 (by rfl) ⟨252176, by rfl⟩ : syracuseStep 336235 = 504353) B504353
theorem B336247 : Blo 334751 336247 := bstep (se 1 (by rfl) ⟨252185, by rfl⟩ : syracuseStep 336247 = 504371) B504371
theorem B565643 : Blo 334751 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B336267 : Blo 334751 336267 := bstep (se 1 (by rfl) ⟨252200, by rfl⟩ : syracuseStep 336267 = 504401) B504401
theorem B336279 : Blo 334751 336279 := bstep (se 1 (by rfl) ⟨252209, by rfl⟩ : syracuseStep 336279 = 504419) B504419
theorem B336299 : Blo 334751 336299 := bstep (se 1 (by rfl) ⟨252224, by rfl⟩ : syracuseStep 336299 = 504449) B504449
theorem B336311 : Blo 334751 336311 := bstep (se 1 (by rfl) ⟨252233, by rfl⟩ : syracuseStep 336311 = 504467) B504467
theorem B336331 : Blo 334751 336331 := bstep (se 1 (by rfl) ⟨252248, by rfl⟩ : syracuseStep 336331 = 504497) B504497
theorem B336343 : Blo 334751 336343 := bstep (se 1 (by rfl) ⟨252257, by rfl⟩ : syracuseStep 336343 = 504515) B504515
theorem B336363 : Blo 334751 336363 := bstep (se 1 (by rfl) ⟨252272, by rfl⟩ : syracuseStep 336363 = 504545) B504545
theorem B336375 : Blo 334751 336375 := bstep (se 1 (by rfl) ⟨252281, by rfl⟩ : syracuseStep 336375 = 504563) B504563
theorem B565771 : Blo 334751 565771 := bstep (se 1 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 565771 = 848657) B848657
theorem B336395 : Blo 334751 336395 := bstep (se 1 (by rfl) ⟨252296, by rfl⟩ : syracuseStep 336395 = 504593) B504593
theorem B336407 : Blo 334751 336407 := bstep (se 1 (by rfl) ⟨252305, by rfl⟩ : syracuseStep 336407 = 504611) B504611
theorem B336427 : Blo 334751 336427 := bstep (se 1 (by rfl) ⟨252320, by rfl⟩ : syracuseStep 336427 = 504641) B504641
theorem B336439 : Blo 334751 336439 := bstep (se 1 (by rfl) ⟨252329, by rfl⟩ : syracuseStep 336439 = 504659) B504659
theorem B336459 : Blo 334751 336459 := bstep (se 1 (by rfl) ⟨252344, by rfl⟩ : syracuseStep 336459 = 504689) B504689
theorem B336471 : Blo 334751 336471 := bstep (se 1 (by rfl) ⟨252353, by rfl⟩ : syracuseStep 336471 = 504707) B504707
theorem B336491 : Blo 334751 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B336503 : Blo 334751 336503 := bstep (se 1 (by rfl) ⟨252377, by rfl⟩ : syracuseStep 336503 = 504755) B504755
theorem B336523 : Blo 334751 336523 := bstep (se 1 (by rfl) ⟨252392, by rfl⟩ : syracuseStep 336523 = 504785) B504785
theorem B336535 : Blo 334751 336535 := bstep (se 1 (by rfl) ⟨252401, by rfl⟩ : syracuseStep 336535 = 504803) B504803
theorem B565913 : Blo 334751 565913 := bstep (se 2 (by rfl) ⟨212217, by rfl⟩ : syracuseStep 565913 = 424435) B424435
theorem B336555 : Blo 334751 336555 := bstep (se 1 (by rfl) ⟨252416, by rfl⟩ : syracuseStep 336555 = 504833) B504833
theorem B336567 : Blo 334751 336567 := bstep (se 1 (by rfl) ⟨252425, by rfl⟩ : syracuseStep 336567 = 504851) B504851
theorem B336587 : Blo 334751 336587 := bstep (se 1 (by rfl) ⟨252440, by rfl⟩ : syracuseStep 336587 = 504881) B504881
theorem B336599 : Blo 334751 336599 := bstep (se 1 (by rfl) ⟨252449, by rfl⟩ : syracuseStep 336599 = 504899) B504899
theorem B2794201 : Blo 334751 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B336619 : Blo 334751 336619 := bstep (se 1 (by rfl) ⟨252464, by rfl⟩ : syracuseStep 336619 = 504929) B504929
theorem B336631 : Blo 334751 336631 := bstep (se 1 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 336631 = 504947) B504947
theorem B336651 : Blo 334751 336651 := bstep (se 1 (by rfl) ⟨252488, by rfl⟩ : syracuseStep 336651 = 504977) B504977
theorem B336663 : Blo 334751 336663 := bstep (se 1 (by rfl) ⟨252497, by rfl⟩ : syracuseStep 336663 = 504995) B504995
theorem B566041 : Blo 334751 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B336683 : Blo 334751 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B336695 : Blo 334751 336695 := bstep (se 1 (by rfl) ⟨252521, by rfl⟩ : syracuseStep 336695 = 505043) B505043
theorem B336715 : Blo 334751 336715 := bstep (se 1 (by rfl) ⟨252536, by rfl⟩ : syracuseStep 336715 = 505073) B505073
theorem B336727 : Blo 334751 336727 := bstep (se 1 (by rfl) ⟨252545, by rfl⟩ : syracuseStep 336727 = 505091) B505091
theorem B336747 : Blo 334751 336747 := bstep (se 1 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 336747 = 505121) B505121
theorem B336759 : Blo 334751 336759 := bstep (se 1 (by rfl) ⟨252569, by rfl⟩ : syracuseStep 336759 = 505139) B505139
theorem B336779 : Blo 334751 336779 := bstep (se 1 (by rfl) ⟨252584, by rfl⟩ : syracuseStep 336779 = 505169) B505169
theorem B336791 : Blo 334751 336791 := bstep (se 1 (by rfl) ⟨252593, by rfl⟩ : syracuseStep 336791 = 505187) B505187
theorem B336811 : Blo 334751 336811 := bstep (se 1 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 336811 = 505217) B505217
theorem B336823 : Blo 334751 336823 := bstep (se 1 (by rfl) ⟨252617, by rfl⟩ : syracuseStep 336823 = 505235) B505235
theorem B336843 : Blo 334751 336843 := bstep (se 1 (by rfl) ⟨252632, by rfl⟩ : syracuseStep 336843 = 505265) B505265
theorem B336855 : Blo 334751 336855 := bstep (se 1 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 336855 = 505283) B505283
theorem B336875 : Blo 334751 336875 := bstep (se 1 (by rfl) ⟨252656, by rfl⟩ : syracuseStep 336875 = 505313) B505313
theorem B336887 : Blo 334751 336887 := bstep (se 1 (by rfl) ⟨252665, by rfl⟩ : syracuseStep 336887 = 505331) B505331
theorem B336907 : Blo 334751 336907 := bstep (se 1 (by rfl) ⟨252680, by rfl⟩ : syracuseStep 336907 = 505361) B505361
theorem B2860049 : Blo 334751 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B336919 : Blo 334751 336919 := bstep (se 1 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 336919 = 505379) B505379
theorem B336939 : Blo 334751 336939 := bstep (se 1 (by rfl) ⟨252704, by rfl⟩ : syracuseStep 336939 = 505409) B505409
theorem B336951 : Blo 334751 336951 := bstep (se 1 (by rfl) ⟨252713, by rfl⟩ : syracuseStep 336951 = 505427) B505427
theorem B336971 : Blo 334751 336971 := bstep (se 1 (by rfl) ⟨252728, by rfl⟩ : syracuseStep 336971 = 505457) B505457
theorem B336983 : Blo 334751 336983 := bstep (se 1 (by rfl) ⟨252737, by rfl⟩ : syracuseStep 336983 = 505475) B505475
theorem B337003 : Blo 334751 337003 := bstep (se 1 (by rfl) ⟨252752, by rfl⟩ : syracuseStep 337003 = 505505) B505505
theorem B337015 : Blo 334751 337015 := bstep (se 1 (by rfl) ⟨252761, by rfl⟩ : syracuseStep 337015 = 505523) B505523
theorem B337035 : Blo 334751 337035 := bstep (se 1 (by rfl) ⟨252776, by rfl⟩ : syracuseStep 337035 = 505553) B505553
theorem B3220631 : Blo 334751 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B337047 : Blo 334751 337047 := bstep (se 1 (by rfl) ⟨252785, by rfl⟩ : syracuseStep 337047 = 505571) B505571
theorem B337067 : Blo 334751 337067 := bstep (se 1 (by rfl) ⟨252800, by rfl⟩ : syracuseStep 337067 = 505601) B505601
theorem B337079 : Blo 334751 337079 := bstep (se 1 (by rfl) ⟨252809, by rfl⟩ : syracuseStep 337079 = 505619) B505619
theorem B337099 : Blo 334751 337099 := bstep (se 1 (by rfl) ⟨252824, by rfl⟩ : syracuseStep 337099 = 505649) B505649
theorem B337111 : Blo 334751 337111 := bstep (se 1 (by rfl) ⟨252833, by rfl⟩ : syracuseStep 337111 = 505667) B505667
theorem B337131 : Blo 334751 337131 := bstep (se 1 (by rfl) ⟨252848, by rfl⟩ : syracuseStep 337131 = 505697) B505697
theorem B337143 : Blo 334751 337143 := bstep (se 1 (by rfl) ⟨252857, by rfl⟩ : syracuseStep 337143 = 505715) B505715
theorem B337163 : Blo 334751 337163 := bstep (se 1 (by rfl) ⟨252872, by rfl⟩ : syracuseStep 337163 = 505745) B505745
theorem B337175 : Blo 334751 337175 := bstep (se 1 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 337175 = 505763) B505763
theorem B337195 : Blo 334751 337195 := bstep (se 1 (by rfl) ⟨252896, by rfl⟩ : syracuseStep 337195 = 505793) B505793
theorem B337207 : Blo 334751 337207 := bstep (se 1 (by rfl) ⟨252905, by rfl⟩ : syracuseStep 337207 = 505811) B505811
theorem B959809 : Blo 334751 959809 := bstep (se 2 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 959809 = 719857) B719857
theorem B1713473 : Blo 334751 1713473 := bstep (se 2 (by rfl) ⟨642552, by rfl⟩ : syracuseStep 1713473 = 1285105) B1285105
theorem B337227 : Blo 334751 337227 := bstep (se 1 (by rfl) ⟨252920, by rfl⟩ : syracuseStep 337227 = 505841) B505841
theorem B1156427 : Blo 334751 1156427 := bstep (se 1 (by rfl) ⟨867320, by rfl⟩ : syracuseStep 1156427 = 1734641) B1734641
theorem B566615 : Blo 334751 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B337239 : Blo 334751 337239 := bstep (se 1 (by rfl) ⟨252929, by rfl⟩ : syracuseStep 337239 = 505859) B505859
theorem B337259 : Blo 334751 337259 := bstep (se 1 (by rfl) ⟨252944, by rfl⟩ : syracuseStep 337259 = 505889) B505889
theorem B337271 : Blo 334751 337271 := bstep (se 1 (by rfl) ⟨252953, by rfl⟩ : syracuseStep 337271 = 505907) B505907
theorem B337291 : Blo 334751 337291 := bstep (se 1 (by rfl) ⟨252968, by rfl⟩ : syracuseStep 337291 = 505937) B505937
theorem B337303 : Blo 334751 337303 := bstep (se 1 (by rfl) ⟨252977, by rfl⟩ : syracuseStep 337303 = 505955) B505955
theorem B337323 : Blo 334751 337323 := bstep (se 1 (by rfl) ⟨252992, by rfl⟩ : syracuseStep 337323 = 505985) B505985
theorem B370103 : Blo 334751 370103 := bstep (se 1 (by rfl) ⟨277577, by rfl⟩ : syracuseStep 370103 = 555155) B555155
theorem B337335 : Blo 334751 337335 := bstep (se 1 (by rfl) ⟨253001, by rfl⟩ : syracuseStep 337335 = 506003) B506003
theorem B337355 : Blo 334751 337355 := bstep (se 1 (by rfl) ⟨253016, by rfl⟩ : syracuseStep 337355 = 506033) B506033
theorem B566743 : Blo 334751 566743 := bstep (se 1 (by rfl) ⟨425057, by rfl⟩ : syracuseStep 566743 = 850115) B850115
theorem B337367 : Blo 334751 337367 := bstep (se 1 (by rfl) ⟨253025, by rfl⟩ : syracuseStep 337367 = 506051) B506051
theorem B2565593 : Blo 334751 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B337387 : Blo 334751 337387 := bstep (se 1 (by rfl) ⟨253040, by rfl⟩ : syracuseStep 337387 = 506081) B506081
theorem B337399 : Blo 334751 337399 := bstep (se 1 (by rfl) ⟨253049, by rfl⟩ : syracuseStep 337399 = 506099) B506099
theorem B337419 : Blo 334751 337419 := bstep (se 1 (by rfl) ⟨253064, by rfl⟩ : syracuseStep 337419 = 506129) B506129
theorem B337431 : Blo 334751 337431 := bstep (se 1 (by rfl) ⟨253073, by rfl⟩ : syracuseStep 337431 = 506147) B506147
theorem B337451 : Blo 334751 337451 := bstep (se 1 (by rfl) ⟨253088, by rfl⟩ : syracuseStep 337451 = 506177) B506177
theorem B1975853 : Blo 334751 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B337463 : Blo 334751 337463 := bstep (se 1 (by rfl) ⟨253097, by rfl⟩ : syracuseStep 337463 = 506195) B506195
theorem B337483 : Blo 334751 337483 := bstep (se 1 (by rfl) ⟨253112, by rfl⟩ : syracuseStep 337483 = 506225) B506225
theorem B337495 : Blo 334751 337495 := bstep (se 1 (by rfl) ⟨253121, by rfl⟩ : syracuseStep 337495 = 506243) B506243
theorem B337515 : Blo 334751 337515 := bstep (se 1 (by rfl) ⟨253136, by rfl⟩ : syracuseStep 337515 = 506273) B506273
theorem B337527 : Blo 334751 337527 := bstep (se 1 (by rfl) ⟨253145, by rfl⟩ : syracuseStep 337527 = 506291) B506291
theorem B337547 : Blo 334751 337547 := bstep (se 1 (by rfl) ⟨253160, by rfl⟩ : syracuseStep 337547 = 506321) B506321
theorem B337559 : Blo 334751 337559 := bstep (se 1 (by rfl) ⟨253169, by rfl⟩ : syracuseStep 337559 = 506339) B506339
theorem B337579 : Blo 334751 337579 := bstep (se 1 (by rfl) ⟨253184, by rfl⟩ : syracuseStep 337579 = 506369) B506369
theorem B337591 : Blo 334751 337591 := bstep (se 1 (by rfl) ⟨253193, by rfl⟩ : syracuseStep 337591 = 506387) B506387
theorem B337611 : Blo 334751 337611 := bstep (se 1 (by rfl) ⟨253208, by rfl⟩ : syracuseStep 337611 = 506417) B506417
theorem B8726221 : Blo 334751 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B337623 : Blo 334751 337623 := bstep (se 1 (by rfl) ⟨253217, by rfl⟩ : syracuseStep 337623 = 506435) B506435
theorem B337643 : Blo 334751 337643 := bstep (se 1 (by rfl) ⟨253232, by rfl⟩ : syracuseStep 337643 = 506465) B506465
theorem B337655 : Blo 334751 337655 := bstep (se 1 (by rfl) ⟨253241, by rfl⟩ : syracuseStep 337655 = 506483) B506483
theorem B337675 : Blo 334751 337675 := bstep (se 1 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 337675 = 506513) B506513
theorem B337687 : Blo 334751 337687 := bstep (se 1 (by rfl) ⟨253265, by rfl⟩ : syracuseStep 337687 = 506531) B506531
theorem B337707 : Blo 334751 337707 := bstep (se 1 (by rfl) ⟨253280, by rfl⟩ : syracuseStep 337707 = 506561) B506561
theorem B1910573 : Blo 334751 1910573 := bstep (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) B716465
theorem B337719 : Blo 334751 337719 := bstep (se 1 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 337719 = 506579) B506579
theorem B337739 : Blo 334751 337739 := bstep (se 1 (by rfl) ⟨253304, by rfl⟩ : syracuseStep 337739 = 506609) B506609
theorem B2893643 : Blo 334751 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B337751 : Blo 334751 337751 := bstep (se 1 (by rfl) ⟨253313, by rfl⟩ : syracuseStep 337751 = 506627) B506627
theorem B337771 : Blo 334751 337771 := bstep (se 1 (by rfl) ⟨253328, by rfl⟩ : syracuseStep 337771 = 506657) B506657
theorem B337783 : Blo 334751 337783 := bstep (se 1 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 337783 = 506675) B506675
theorem B337803 : Blo 334751 337803 := bstep (se 1 (by rfl) ⟨253352, by rfl⟩ : syracuseStep 337803 = 506705) B506705
theorem B337815 : Blo 334751 337815 := bstep (se 1 (by rfl) ⟨253361, by rfl⟩ : syracuseStep 337815 = 506723) B506723
theorem B337835 : Blo 334751 337835 := bstep (se 1 (by rfl) ⟨253376, by rfl⟩ : syracuseStep 337835 = 506753) B506753
theorem B337847 : Blo 334751 337847 := bstep (se 1 (by rfl) ⟨253385, by rfl⟩ : syracuseStep 337847 = 506771) B506771
theorem B337867 : Blo 334751 337867 := bstep (se 1 (by rfl) ⟨253400, by rfl⟩ : syracuseStep 337867 = 506801) B506801
theorem B337879 : Blo 334751 337879 := bstep (se 1 (by rfl) ⟨253409, by rfl⟩ : syracuseStep 337879 = 506819) B506819
theorem B337899 : Blo 334751 337899 := bstep (se 1 (by rfl) ⟨253424, by rfl⟩ : syracuseStep 337899 = 506849) B506849
theorem B337911 : Blo 334751 337911 := bstep (se 1 (by rfl) ⟨253433, by rfl⟩ : syracuseStep 337911 = 506867) B506867
theorem B337931 : Blo 334751 337931 := bstep (se 1 (by rfl) ⟨253448, by rfl⟩ : syracuseStep 337931 = 506897) B506897
theorem B337943 : Blo 334751 337943 := bstep (se 1 (by rfl) ⟨253457, by rfl⟩ : syracuseStep 337943 = 506915) B506915
theorem B337963 : Blo 334751 337963 := bstep (se 1 (by rfl) ⟨253472, by rfl⟩ : syracuseStep 337963 = 506945) B506945
theorem B337975 : Blo 334751 337975 := bstep (se 1 (by rfl) ⟨253481, by rfl⟩ : syracuseStep 337975 = 506963) B506963
theorem B5482565 : Blo 334751 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B567371 : Blo 334751 567371 := bstep (se 1 (by rfl) ⟨425528, by rfl⟩ : syracuseStep 567371 = 851057) B851057
theorem B337995 : Blo 334751 337995 := bstep (se 1 (by rfl) ⟨253496, by rfl⟩ : syracuseStep 337995 = 506993) B506993
theorem B338007 : Blo 334751 338007 := bstep (se 1 (by rfl) ⟨253505, by rfl⟩ : syracuseStep 338007 = 507011) B507011
theorem B338027 : Blo 334751 338027 := bstep (se 1 (by rfl) ⟨253520, by rfl⟩ : syracuseStep 338027 = 507041) B507041
theorem B338039 : Blo 334751 338039 := bstep (se 1 (by rfl) ⟨253529, by rfl⟩ : syracuseStep 338039 = 507059) B507059
theorem B338059 : Blo 334751 338059 := bstep (se 1 (by rfl) ⟨253544, by rfl⟩ : syracuseStep 338059 = 507089) B507089
theorem B338071 : Blo 334751 338071 := bstep (se 1 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 338071 = 507107) B507107
theorem B338091 : Blo 334751 338091 := bstep (se 1 (by rfl) ⟨253568, by rfl⟩ : syracuseStep 338091 = 507137) B507137
theorem B338103 : Blo 334751 338103 := bstep (se 1 (by rfl) ⟨253577, by rfl⟩ : syracuseStep 338103 = 507155) B507155
theorem B567499 : Blo 334751 567499 := bstep (se 1 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 567499 = 851249) B851249
theorem B338123 : Blo 334751 338123 := bstep (se 1 (by rfl) ⟨253592, by rfl⟩ : syracuseStep 338123 = 507185) B507185
theorem B338135 : Blo 334751 338135 := bstep (se 1 (by rfl) ⟨253601, by rfl⟩ : syracuseStep 338135 = 507203) B507203
theorem B338155 : Blo 334751 338155 := bstep (se 1 (by rfl) ⟨253616, by rfl⟩ : syracuseStep 338155 = 507233) B507233
theorem B338167 : Blo 334751 338167 := bstep (se 1 (by rfl) ⟨253625, by rfl⟩ : syracuseStep 338167 = 507251) B507251
theorem B338187 : Blo 334751 338187 := bstep (se 1 (by rfl) ⟨253640, by rfl⟩ : syracuseStep 338187 = 507281) B507281
theorem B338199 : Blo 334751 338199 := bstep (se 1 (by rfl) ⟨253649, by rfl⟩ : syracuseStep 338199 = 507299) B507299
theorem B338219 : Blo 334751 338219 := bstep (se 1 (by rfl) ⟨253664, by rfl⟩ : syracuseStep 338219 = 507329) B507329
theorem B338231 : Blo 334751 338231 := bstep (se 1 (by rfl) ⟨253673, by rfl⟩ : syracuseStep 338231 = 507347) B507347
theorem B338251 : Blo 334751 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B338263 : Blo 334751 338263 := bstep (se 1 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 338263 = 507395) B507395
theorem B567641 : Blo 334751 567641 := bstep (se 2 (by rfl) ⟨212865, by rfl⟩ : syracuseStep 567641 = 425731) B425731
theorem B338283 : Blo 334751 338283 := bstep (se 1 (by rfl) ⟨253712, by rfl⟩ : syracuseStep 338283 = 507425) B507425
theorem B338295 : Blo 334751 338295 := bstep (se 1 (by rfl) ⟨253721, by rfl⟩ : syracuseStep 338295 = 507443) B507443
theorem B338315 : Blo 334751 338315 := bstep (se 1 (by rfl) ⟨253736, by rfl⟩ : syracuseStep 338315 = 507473) B507473
theorem B338327 : Blo 334751 338327 := bstep (se 1 (by rfl) ⟨253745, by rfl⟩ : syracuseStep 338327 = 507491) B507491
theorem B502169 : Blo 334751 502169 := bstep (se 2 (by rfl) ⟨188313, by rfl⟩ : syracuseStep 502169 = 376627) B376627
theorem B338347 : Blo 334751 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B338359 : Blo 334751 338359 := bstep (se 1 (by rfl) ⟨253769, by rfl⟩ : syracuseStep 338359 = 507539) B507539
theorem B338379 : Blo 334751 338379 := bstep (se 1 (by rfl) ⟨253784, by rfl⟩ : syracuseStep 338379 = 507569) B507569
theorem B338391 : Blo 334751 338391 := bstep (se 1 (by rfl) ⟨253793, by rfl⟩ : syracuseStep 338391 = 507587) B507587
theorem B567769 : Blo 334751 567769 := bstep (se 2 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 567769 = 425827) B425827
theorem B338411 : Blo 334751 338411 := bstep (se 1 (by rfl) ⟨253808, by rfl⟩ : syracuseStep 338411 = 507617) B507617
theorem B338423 : Blo 334751 338423 := bstep (se 1 (by rfl) ⟨253817, by rfl⟩ : syracuseStep 338423 = 507635) B507635
theorem B502283 : Blo 334751 502283 := bstep (se 1 (by rfl) ⟨376712, by rfl⟩ : syracuseStep 502283 = 753425) B753425
theorem B338443 : Blo 334751 338443 := bstep (se 1 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 338443 = 507665) B507665
theorem B502295 : Blo 334751 502295 := bstep (se 1 (by rfl) ⟨376721, by rfl⟩ : syracuseStep 502295 = 753443) B753443
theorem B338455 : Blo 334751 338455 := bstep (se 1 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 338455 = 507683) B507683
theorem B338475 : Blo 334751 338475 := bstep (se 1 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 338475 = 507713) B507713
theorem B338487 : Blo 334751 338487 := bstep (se 1 (by rfl) ⟨253865, by rfl⟩ : syracuseStep 338487 = 507731) B507731
theorem B338507 : Blo 334751 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B338519 : Blo 334751 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B502361 : Blo 334751 502361 := bstep (se 2 (by rfl) ⟨188385, by rfl⟩ : syracuseStep 502361 = 376771) B376771
theorem B338539 : Blo 334751 338539 := bstep (se 1 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 338539 = 507809) B507809
theorem B338551 : Blo 334751 338551 := bstep (se 1 (by rfl) ⟨253913, by rfl⟩ : syracuseStep 338551 = 507827) B507827
theorem B338571 : Blo 334751 338571 := bstep (se 1 (by rfl) ⟨253928, by rfl⟩ : syracuseStep 338571 = 507857) B507857
theorem B338583 : Blo 334751 338583 := bstep (se 1 (by rfl) ⟨253937, by rfl⟩ : syracuseStep 338583 = 507875) B507875
theorem B338603 : Blo 334751 338603 := bstep (se 1 (by rfl) ⟨253952, by rfl⟩ : syracuseStep 338603 = 507905) B507905
theorem B338615 : Blo 334751 338615 := bstep (se 1 (by rfl) ⟨253961, by rfl⟩ : syracuseStep 338615 = 507923) B507923
theorem B502475 : Blo 334751 502475 := bstep (se 1 (by rfl) ⟨376856, by rfl⟩ : syracuseStep 502475 = 753713) B753713
theorem B338635 : Blo 334751 338635 := bstep (se 1 (by rfl) ⟨253976, by rfl⟩ : syracuseStep 338635 = 507953) B507953
theorem B502487 : Blo 334751 502487 := bstep (se 1 (by rfl) ⟨376865, by rfl⟩ : syracuseStep 502487 = 753731) B753731
theorem B338647 : Blo 334751 338647 := bstep (se 1 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 338647 = 507971) B507971
theorem B338667 : Blo 334751 338667 := bstep (se 1 (by rfl) ⟨254000, by rfl⟩ : syracuseStep 338667 = 508001) B508001
theorem B338679 : Blo 334751 338679 := bstep (se 1 (by rfl) ⟨254009, by rfl⟩ : syracuseStep 338679 = 508019) B508019
theorem B338699 : Blo 334751 338699 := bstep (se 1 (by rfl) ⟨254024, by rfl⟩ : syracuseStep 338699 = 508049) B508049
theorem B338711 : Blo 334751 338711 := bstep (se 1 (by rfl) ⟨254033, by rfl⟩ : syracuseStep 338711 = 508067) B508067
theorem B502553 : Blo 334751 502553 := bstep (se 2 (by rfl) ⟨188457, by rfl⟩ : syracuseStep 502553 = 376915) B376915
theorem B338731 : Blo 334751 338731 := bstep (se 1 (by rfl) ⟨254048, by rfl⟩ : syracuseStep 338731 = 508097) B508097
theorem B338743 : Blo 334751 338743 := bstep (se 1 (by rfl) ⟨254057, by rfl⟩ : syracuseStep 338743 = 508115) B508115
theorem B1846147 : Blo 334751 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B502667 : Blo 334751 502667 := bstep (se 1 (by rfl) ⟨377000, by rfl⟩ : syracuseStep 502667 = 754001) B754001
theorem B502679 : Blo 334751 502679 := bstep (se 1 (by rfl) ⟨377009, by rfl⟩ : syracuseStep 502679 = 754019) B754019
theorem B961483 : Blo 334751 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B502745 : Blo 334751 502745 := bstep (se 2 (by rfl) ⟨188529, by rfl⟩ : syracuseStep 502745 = 377059) B377059
theorem B568343 : Blo 334751 568343 := bstep (se 1 (by rfl) ⟨426257, by rfl⟩ : syracuseStep 568343 = 852515) B852515
theorem B502859 : Blo 334751 502859 := bstep (se 1 (by rfl) ⟨377144, by rfl⟩ : syracuseStep 502859 = 754289) B754289
theorem B502871 : Blo 334751 502871 := bstep (se 1 (by rfl) ⟨377153, by rfl⟩ : syracuseStep 502871 = 754307) B754307
theorem B568471 : Blo 334751 568471 := bstep (se 1 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 568471 = 852707) B852707
theorem B502937 : Blo 334751 502937 := bstep (se 2 (by rfl) ⟨188601, by rfl⟩ : syracuseStep 502937 = 377203) B377203
theorem B961757 : Blo 334751 961757 := bstep (se 3 (by rfl) ⟨180329, by rfl⟩ : syracuseStep 961757 = 360659) B360659
theorem B503051 : Blo 334751 503051 := bstep (se 1 (by rfl) ⟨377288, by rfl⟩ : syracuseStep 503051 = 754577) B754577
theorem B503063 : Blo 334751 503063 := bstep (se 1 (by rfl) ⟨377297, by rfl⟩ : syracuseStep 503063 = 754595) B754595
theorem B503129 : Blo 334751 503129 := bstep (se 2 (by rfl) ⟨188673, by rfl⟩ : syracuseStep 503129 = 377347) B377347
theorem B503243 : Blo 334751 503243 := bstep (se 1 (by rfl) ⟨377432, by rfl⟩ : syracuseStep 503243 = 754865) B754865
theorem B503255 : Blo 334751 503255 := bstep (se 1 (by rfl) ⟨377441, by rfl⟩ : syracuseStep 503255 = 754883) B754883
theorem B1224157 : Blo 334751 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B503321 : Blo 334751 503321 := bstep (se 2 (by rfl) ⟨188745, by rfl⟩ : syracuseStep 503321 = 377491) B377491
theorem B503435 : Blo 334751 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B503447 : Blo 334751 503447 := bstep (se 1 (by rfl) ⟨377585, by rfl⟩ : syracuseStep 503447 = 755171) B755171
theorem B3878551 : Blo 334751 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B503513 : Blo 334751 503513 := bstep (se 2 (by rfl) ⟨188817, by rfl⟩ : syracuseStep 503513 = 377635) B377635
theorem B569099 : Blo 334751 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B503627 : Blo 334751 503627 := bstep (se 1 (by rfl) ⟨377720, by rfl⟩ : syracuseStep 503627 = 755441) B755441
theorem B503639 : Blo 334751 503639 := bstep (se 1 (by rfl) ⟨377729, by rfl⟩ : syracuseStep 503639 = 755459) B755459
theorem B569227 : Blo 334751 569227 := bstep (se 1 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 569227 = 853841) B853841
theorem B503705 : Blo 334751 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B2863025 : Blo 334751 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B13840307 : Blo 334751 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B503819 : Blo 334751 503819 := bstep (se 1 (by rfl) ⟨377864, by rfl⟩ : syracuseStep 503819 = 755729) B755729
theorem B503831 : Blo 334751 503831 := bstep (se 1 (by rfl) ⟨377873, by rfl⟩ : syracuseStep 503831 = 755747) B755747
theorem B569369 : Blo 334751 569369 := bstep (se 2 (by rfl) ⟨213513, by rfl⟩ : syracuseStep 569369 = 427027) B427027
theorem B503897 : Blo 334751 503897 := bstep (se 2 (by rfl) ⟨188961, by rfl⟩ : syracuseStep 503897 = 377923) B377923
theorem B569497 : Blo 334751 569497 := bstep (se 2 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 569497 = 427123) B427123
theorem B504011 : Blo 334751 504011 := bstep (se 1 (by rfl) ⟨378008, by rfl⟩ : syracuseStep 504011 = 756017) B756017
theorem B504023 : Blo 334751 504023 := bstep (se 1 (by rfl) ⟨378017, by rfl⟩ : syracuseStep 504023 = 756035) B756035
theorem B504089 : Blo 334751 504089 := bstep (se 2 (by rfl) ⟨189033, by rfl⟩ : syracuseStep 504089 = 378067) B378067
theorem B405847 : Blo 334751 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B504203 : Blo 334751 504203 := bstep (se 1 (by rfl) ⟨378152, by rfl⟩ : syracuseStep 504203 = 756305) B756305
theorem B504215 : Blo 334751 504215 := bstep (se 1 (by rfl) ⟨378161, by rfl⟩ : syracuseStep 504215 = 756323) B756323
theorem B504281 : Blo 334751 504281 := bstep (se 2 (by rfl) ⟨189105, by rfl⟩ : syracuseStep 504281 = 378211) B378211
theorem B504395 : Blo 334751 504395 := bstep (se 1 (by rfl) ⟨378296, by rfl⟩ : syracuseStep 504395 = 756593) B756593
theorem B504407 : Blo 334751 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B635521 : Blo 334751 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B504473 : Blo 334751 504473 := bstep (se 2 (by rfl) ⟨189177, by rfl⟩ : syracuseStep 504473 = 378355) B378355
theorem B570071 : Blo 334751 570071 := bstep (se 1 (by rfl) ⟨427553, by rfl⟩ : syracuseStep 570071 = 855107) B855107
theorem B504587 : Blo 334751 504587 := bstep (se 1 (by rfl) ⟨378440, by rfl⟩ : syracuseStep 504587 = 756881) B756881
theorem B2175761 : Blo 334751 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B504599 : Blo 334751 504599 := bstep (se 1 (by rfl) ⟨378449, by rfl⟩ : syracuseStep 504599 = 756899) B756899
theorem B2568995 : Blo 334751 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B570199 : Blo 334751 570199 := bstep (se 1 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 570199 = 855299) B855299
theorem B504665 : Blo 334751 504665 := bstep (se 2 (by rfl) ⟨189249, by rfl⟩ : syracuseStep 504665 = 378499) B378499
theorem B504779 : Blo 334751 504779 := bstep (se 1 (by rfl) ⟨378584, by rfl⟩ : syracuseStep 504779 = 757169) B757169
theorem B635863 : Blo 334751 635863 := bstep (se 1 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 635863 = 953795) B953795
theorem B504791 : Blo 334751 504791 := bstep (se 1 (by rfl) ⟨378593, by rfl⟩ : syracuseStep 504791 = 757187) B757187
theorem B504857 : Blo 334751 504857 := bstep (se 2 (by rfl) ⟨189321, by rfl⟩ : syracuseStep 504857 = 378643) B378643
theorem B504971 : Blo 334751 504971 := bstep (se 1 (by rfl) ⟨378728, by rfl⟩ : syracuseStep 504971 = 757457) B757457
theorem B504983 : Blo 334751 504983 := bstep (se 1 (by rfl) ⟨378737, by rfl⟩ : syracuseStep 504983 = 757475) B757475
theorem B636083 : Blo 334751 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B505049 : Blo 334751 505049 := bstep (se 2 (by rfl) ⟨189393, by rfl⟩ : syracuseStep 505049 = 378787) B378787
theorem B603379 : Blo 334751 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B505163 : Blo 334751 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B505175 : Blo 334751 505175 := bstep (se 1 (by rfl) ⟨378881, by rfl⟩ : syracuseStep 505175 = 757763) B757763
theorem B636311 : Blo 334751 636311 := bstep (se 1 (by rfl) ⟨477233, by rfl⟩ : syracuseStep 636311 = 954467) B954467
theorem B1914263 : Blo 334751 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B505241 : Blo 334751 505241 := bstep (se 2 (by rfl) ⟨189465, by rfl⟩ : syracuseStep 505241 = 378931) B378931
theorem B603595 : Blo 334751 603595 := bstep (se 1 (by rfl) ⟨452696, by rfl⟩ : syracuseStep 603595 = 905393) B905393
theorem B570827 : Blo 334751 570827 := bstep (se 1 (by rfl) ⟨428120, by rfl⟩ : syracuseStep 570827 = 856241) B856241
theorem B964057 : Blo 334751 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B505355 : Blo 334751 505355 := bstep (se 1 (by rfl) ⟨379016, by rfl⟩ : syracuseStep 505355 = 758033) B758033
theorem B505367 : Blo 334751 505367 := bstep (se 1 (by rfl) ⟨379025, by rfl⟩ : syracuseStep 505367 = 758051) B758051
theorem B570955 : Blo 334751 570955 := bstep (se 1 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 570955 = 856433) B856433
theorem B505433 : Blo 334751 505433 := bstep (se 2 (by rfl) ⟨189537, by rfl⟩ : syracuseStep 505433 = 379075) B379075
theorem B636569 : Blo 334751 636569 := bstep (se 2 (by rfl) ⟨238713, by rfl⟩ : syracuseStep 636569 = 477427) B477427
theorem B505547 : Blo 334751 505547 := bstep (se 1 (by rfl) ⟨379160, by rfl⟩ : syracuseStep 505547 = 758321) B758321
theorem B603863 : Blo 334751 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B505559 : Blo 334751 505559 := bstep (se 1 (by rfl) ⟨379169, by rfl⟩ : syracuseStep 505559 = 758339) B758339
theorem B571097 : Blo 334751 571097 := bstep (se 2 (by rfl) ⟨214161, by rfl⟩ : syracuseStep 571097 = 428323) B428323
theorem B505625 : Blo 334751 505625 := bstep (se 2 (by rfl) ⟨189609, by rfl⟩ : syracuseStep 505625 = 379219) B379219
theorem B571225 : Blo 334751 571225 := bstep (se 2 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 571225 = 428419) B428419
theorem B1947493 : Blo 334751 1947493 := bstep (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) B365155
theorem B1816451 : Blo 334751 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B505739 : Blo 334751 505739 := bstep (se 1 (by rfl) ⟨379304, by rfl⟩ : syracuseStep 505739 = 758609) B758609
theorem B505751 : Blo 334751 505751 := bstep (se 1 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 505751 = 758627) B758627
theorem B505817 : Blo 334751 505817 := bstep (se 2 (by rfl) ⟨189681, by rfl⟩ : syracuseStep 505817 = 379363) B379363
theorem B636979 : Blo 334751 636979 := bstep (se 1 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 636979 = 955469) B955469
theorem B505931 : Blo 334751 505931 := bstep (se 1 (by rfl) ⟨379448, by rfl⟩ : syracuseStep 505931 = 758897) B758897
theorem B505943 : Blo 334751 505943 := bstep (se 1 (by rfl) ⟨379457, by rfl⟩ : syracuseStep 505943 = 758915) B758915
theorem B506009 : Blo 334751 506009 := bstep (se 2 (by rfl) ⟨189753, by rfl⟩ : syracuseStep 506009 = 379507) B379507
theorem B604417 : Blo 334751 604417 := bstep (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) B453313
theorem B506123 : Blo 334751 506123 := bstep (se 1 (by rfl) ⟨379592, by rfl⟩ : syracuseStep 506123 = 759185) B759185
theorem B506135 : Blo 334751 506135 := bstep (se 1 (by rfl) ⟨379601, by rfl⟩ : syracuseStep 506135 = 759203) B759203
theorem B506201 : Blo 334751 506201 := bstep (se 2 (by rfl) ⟨189825, by rfl⟩ : syracuseStep 506201 = 379651) B379651
theorem B506315 : Blo 334751 506315 := bstep (se 1 (by rfl) ⟨379736, by rfl⟩ : syracuseStep 506315 = 759473) B759473
theorem B506327 : Blo 334751 506327 := bstep (se 1 (by rfl) ⟨379745, by rfl⟩ : syracuseStep 506327 = 759491) B759491
theorem B7485965 : Blo 334751 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B637465 : Blo 334751 637465 := bstep (se 2 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 637465 = 478099) B478099
theorem B506393 : Blo 334751 506393 := bstep (se 2 (by rfl) ⟨189897, by rfl⟩ : syracuseStep 506393 = 379795) B379795
theorem B506507 : Blo 334751 506507 := bstep (se 1 (by rfl) ⟨379880, by rfl⟩ : syracuseStep 506507 = 759761) B759761
theorem B506519 : Blo 334751 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B506585 : Blo 334751 506585 := bstep (se 2 (by rfl) ⟨189969, by rfl⟩ : syracuseStep 506585 = 379939) B379939
theorem B506699 : Blo 334751 506699 := bstep (se 1 (by rfl) ⟨380024, by rfl⟩ : syracuseStep 506699 = 760049) B760049
theorem B506711 : Blo 334751 506711 := bstep (se 1 (by rfl) ⟨380033, by rfl⟩ : syracuseStep 506711 = 760067) B760067
theorem B506777 : Blo 334751 506777 := bstep (se 2 (by rfl) ⟨190041, by rfl⟩ : syracuseStep 506777 = 380083) B380083
theorem B506891 : Blo 334751 506891 := bstep (se 1 (by rfl) ⟨380168, by rfl⟩ : syracuseStep 506891 = 760337) B760337
theorem B506903 : Blo 334751 506903 := bstep (se 1 (by rfl) ⟨380177, by rfl⟩ : syracuseStep 506903 = 760355) B760355
theorem B638027 : Blo 334751 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B506969 : Blo 334751 506969 := bstep (se 2 (by rfl) ⟨190113, by rfl⟩ : syracuseStep 506969 = 380227) B380227
theorem B1457297 : Blo 334751 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B507083 : Blo 334751 507083 := bstep (se 1 (by rfl) ⟨380312, by rfl⟩ : syracuseStep 507083 = 760625) B760625
theorem B507095 : Blo 334751 507095 := bstep (se 1 (by rfl) ⟨380321, by rfl⟩ : syracuseStep 507095 = 760643) B760643
theorem B605441 : Blo 334751 605441 := bstep (se 2 (by rfl) ⟨227040, by rfl⟩ : syracuseStep 605441 = 454081) B454081
theorem B638209 : Blo 334751 638209 := bstep (se 2 (by rfl) ⟨239328, by rfl⟩ : syracuseStep 638209 = 478657) B478657
theorem B1359127 : Blo 334751 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B507161 : Blo 334751 507161 := bstep (se 2 (by rfl) ⟨190185, by rfl⟩ : syracuseStep 507161 = 380371) B380371
theorem B2145629 : Blo 334751 2145629 := bstep (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) B804611
theorem B507275 : Blo 334751 507275 := bstep (se 1 (by rfl) ⟨380456, by rfl⟩ : syracuseStep 507275 = 760913) B760913
theorem B507287 : Blo 334751 507287 := bstep (se 1 (by rfl) ⟨380465, by rfl⟩ : syracuseStep 507287 = 760931) B760931
theorem B605657 : Blo 334751 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B507353 : Blo 334751 507353 := bstep (se 2 (by rfl) ⟨190257, by rfl⟩ : syracuseStep 507353 = 380515) B380515
theorem B1129949 : Blo 334751 1129949 := bstep (se 3 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 1129949 = 423731) B423731
theorem B507467 : Blo 334751 507467 := bstep (se 1 (by rfl) ⟨380600, by rfl⟩ : syracuseStep 507467 = 761201) B761201
theorem B507479 : Blo 334751 507479 := bstep (se 1 (by rfl) ⟨380609, by rfl⟩ : syracuseStep 507479 = 761219) B761219
theorem B507545 : Blo 334751 507545 := bstep (se 2 (by rfl) ⟨190329, by rfl⟩ : syracuseStep 507545 = 380659) B380659
theorem B507659 : Blo 334751 507659 := bstep (se 1 (by rfl) ⟨380744, by rfl⟩ : syracuseStep 507659 = 761489) B761489
theorem B507671 : Blo 334751 507671 := bstep (se 1 (by rfl) ⟨380753, by rfl⟩ : syracuseStep 507671 = 761507) B761507
theorem B376663 : Blo 334751 376663 := bstep (se 1 (by rfl) ⟨282497, by rfl⟩ : syracuseStep 376663 = 564995) B564995
theorem B507737 : Blo 334751 507737 := bstep (se 2 (by rfl) ⟨190401, by rfl⟩ : syracuseStep 507737 = 380803) B380803
theorem B18693989 : Blo 334751 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B2441137 : Blo 334751 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B638923 : Blo 334751 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B507851 : Blo 334751 507851 := bstep (se 1 (by rfl) ⟨380888, by rfl⟩ : syracuseStep 507851 = 761777) B761777
theorem B507863 : Blo 334751 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B376843 : Blo 334751 376843 := bstep (se 1 (by rfl) ⟨282632, by rfl⟩ : syracuseStep 376843 = 565265) B565265
theorem B638999 : Blo 334751 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B507929 : Blo 334751 507929 := bstep (se 2 (by rfl) ⟨190473, by rfl⟩ : syracuseStep 507929 = 380947) B380947
theorem B376951 : Blo 334751 376951 := bstep (se 1 (by rfl) ⟨282713, by rfl⟩ : syracuseStep 376951 = 565427) B565427
theorem B508043 : Blo 334751 508043 := bstep (se 1 (by rfl) ⟨381032, by rfl⟩ : syracuseStep 508043 = 762065) B762065
theorem B508055 : Blo 334751 508055 := bstep (se 1 (by rfl) ⟨381041, by rfl⟩ : syracuseStep 508055 = 762083) B762083
theorem B508121 : Blo 334751 508121 := bstep (se 2 (by rfl) ⟨190545, by rfl⟩ : syracuseStep 508121 = 381091) B381091
theorem B377131 : Blo 334751 377131 := bstep (se 1 (by rfl) ⟨282848, by rfl⟩ : syracuseStep 377131 = 565697) B565697
theorem B377239 : Blo 334751 377239 := bstep (se 1 (by rfl) ⟨282929, by rfl⟩ : syracuseStep 377239 = 565859) B565859
theorem B4833715 : Blo 334751 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B1229363 : Blo 334751 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B1131083 : Blo 334751 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B377419 : Blo 334751 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B639667 : Blo 334751 639667 := bstep (se 1 (by rfl) ⟨479750, by rfl⟩ : syracuseStep 639667 = 959501) B959501
theorem B377527 : Blo 334751 377527 := bstep (se 1 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 377527 = 566291) B566291
theorem B541399 : Blo 334751 541399 := bstep (se 1 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 541399 = 812099) B812099
theorem B1131353 : Blo 334751 1131353 := bstep (se 2 (by rfl) ⟨424257, by rfl⟩ : syracuseStep 1131353 = 848515) B848515
theorem B770905 : Blo 334751 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B377707 : Blo 334751 377707 := bstep (se 1 (by rfl) ⟨283280, by rfl⟩ : syracuseStep 377707 = 566561) B566561
theorem B639895 : Blo 334751 639895 := bstep (se 1 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 639895 = 959843) B959843
theorem B377815 : Blo 334751 377815 := bstep (se 1 (by rfl) ⟨283361, by rfl⟩ : syracuseStep 377815 = 566723) B566723
theorem B541655 : Blo 334751 541655 := bstep (se 1 (by rfl) ⟨406241, by rfl⟩ : syracuseStep 541655 = 812483) B812483
theorem B771059 : Blo 334751 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B640001 : Blo 334751 640001 := bstep (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) B480001
theorem B377995 : Blo 334751 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B640153 : Blo 334751 640153 := bstep (se 2 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 640153 = 480115) B480115
theorem B378103 : Blo 334751 378103 := bstep (se 1 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 378103 = 567155) B567155
theorem B542027 : Blo 334751 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B378283 : Blo 334751 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B1132055 : Blo 334751 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B378391 : Blo 334751 378391 := bstep (se 1 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 378391 = 567587) B567587
theorem B476761 : Blo 334751 476761 := bstep (se 2 (by rfl) ⟨178785, by rfl⟩ : syracuseStep 476761 = 357571) B357571
theorem B542359 : Blo 334751 542359 := bstep (se 1 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 542359 = 813539) B813539
theorem B378571 : Blo 334751 378571 := bstep (se 1 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 378571 = 567857) B567857
theorem B2148113 : Blo 334751 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B378679 : Blo 334751 378679 := bstep (se 1 (by rfl) ⟨284009, by rfl⟩ : syracuseStep 378679 = 568019) B568019
theorem B378859 : Blo 334751 378859 := bstep (se 1 (by rfl) ⟨284144, by rfl⟩ : syracuseStep 378859 = 568289) B568289
theorem B1132595 : Blo 334751 1132595 := bstep (se 1 (by rfl) ⟨849446, by rfl⟩ : syracuseStep 1132595 = 1698893) B1698893
theorem B378967 : Blo 334751 378967 := bstep (se 1 (by rfl) ⟨284225, by rfl⟩ : syracuseStep 378967 = 568451) B568451
theorem B1624157 : Blo 334751 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B772247 : Blo 334751 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B379147 : Blo 334751 379147 := bstep (se 1 (by rfl) ⟨284360, by rfl⟩ : syracuseStep 379147 = 568721) B568721
theorem B1132865 : Blo 334751 1132865 := bstep (se 2 (by rfl) ⟨424824, by rfl⟩ : syracuseStep 1132865 = 849649) B849649
theorem B379255 : Blo 334751 379255 := bstep (se 1 (by rfl) ⟨284441, by rfl⟩ : syracuseStep 379255 = 568883) B568883
theorem B641459 : Blo 334751 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B379435 : Blo 334751 379435 := bstep (se 1 (by rfl) ⟨284576, by rfl⟩ : syracuseStep 379435 = 569153) B569153
theorem B641611 : Blo 334751 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B1919639 : Blo 334751 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B379543 : Blo 334751 379543 := bstep (se 1 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 379543 = 569315) B569315
theorem B805697 : Blo 334751 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B379723 : Blo 334751 379723 := bstep (se 1 (by rfl) ⟨284792, by rfl⟩ : syracuseStep 379723 = 569585) B569585
theorem B1133405 : Blo 334751 1133405 := bstep (se 3 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 1133405 = 425027) B425027
theorem B641945 : Blo 334751 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B379831 : Blo 334751 379831 := bstep (se 1 (by rfl) ⟨284873, by rfl⟩ : syracuseStep 379831 = 569747) B569747
theorem B478219 : Blo 334751 478219 := bstep (se 1 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 478219 = 717329) B717329
theorem B380011 : Blo 334751 380011 := bstep (se 1 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 380011 = 570017) B570017
theorem B380119 : Blo 334751 380119 := bstep (se 1 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 380119 = 570179) B570179
theorem B380299 : Blo 334751 380299 := bstep (se 1 (by rfl) ⟨285224, by rfl⟩ : syracuseStep 380299 = 570449) B570449
theorem B380407 : Blo 334751 380407 := bstep (se 1 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 380407 = 570611) B570611
theorem B642583 : Blo 334751 642583 := bstep (se 1 (by rfl) ⟨481937, by rfl⟩ : syracuseStep 642583 = 963875) B963875
theorem B380587 : Blo 334751 380587 := bstep (se 1 (by rfl) ⟨285440, by rfl⟩ : syracuseStep 380587 = 570881) B570881
theorem B380695 : Blo 334751 380695 := bstep (se 1 (by rfl) ⟨285521, by rfl⟩ : syracuseStep 380695 = 571043) B571043
theorem B1134539 : Blo 334751 1134539 := bstep (se 1 (by rfl) ⟨850904, by rfl⟩ : syracuseStep 1134539 = 1701809) B1701809
theorem B380875 : Blo 334751 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B610327 : Blo 334751 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B380983 : Blo 334751 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B1527959 : Blo 334751 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B1134809 : Blo 334751 1134809 := bstep (se 2 (by rfl) ⟨425553, by rfl⟩ : syracuseStep 1134809 = 851107) B851107
theorem B479449 : Blo 334751 479449 := bstep (se 2 (by rfl) ⟨179793, by rfl⟩ : syracuseStep 479449 = 359587) B359587
theorem B1921553 : Blo 334751 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B1135511 : Blo 334751 1135511 := bstep (se 1 (by rfl) ⟨851633, by rfl⟩ : syracuseStep 1135511 = 1703267) B1703267
theorem B2053043 : Blo 334751 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B512983 : Blo 334751 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B545753 : Blo 334751 545753 := bstep (se 2 (by rfl) ⟨204657, by rfl⟩ : syracuseStep 545753 = 409315) B409315
theorem B480343 : Blo 334751 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B4379741 : Blo 334751 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B2872421 : Blo 334751 2872421 := bstep (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) B538579
theorem B1627523 : Blo 334751 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B1136051 : Blo 334751 1136051 := bstep (se 1 (by rfl) ⟨852038, by rfl⟩ : syracuseStep 1136051 = 1704077) B1704077
theorem B480907 : Blo 334751 480907 := bstep (se 1 (by rfl) ⟨360680, by rfl⟩ : syracuseStep 480907 = 721361) B721361
theorem B611993 : Blo 334751 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B972481 : Blo 334751 972481 := bstep (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) B729361
theorem B1136321 : Blo 334751 1136321 := bstep (se 2 (by rfl) ⟨426120, by rfl⟩ : syracuseStep 1136321 = 852241) B852241
theorem B546955 : Blo 334751 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B1136861 : Blo 334751 1136861 := bstep (se 3 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 1136861 = 426323) B426323
theorem B645655 : Blo 334751 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B3824333 : Blo 334751 3824333 := bstep (se 3 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 3824333 = 1434125) B1434125
theorem B5561189 : Blo 334751 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B1727411 : Blo 334751 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1694681 : Blo 334751 1694681 := bstep (se 2 (by rfl) ⟨635505, by rfl⟩ : syracuseStep 1694681 = 1271011) B1271011
theorem B1137995 : Blo 334751 1137995 := bstep (se 1 (by rfl) ⟨853496, by rfl⟩ : syracuseStep 1137995 = 1706993) B1706993
theorem B810329 : Blo 334751 810329 := bstep (se 2 (by rfl) ⟨303873, by rfl⟩ : syracuseStep 810329 = 607747) B607747
theorem B548299 : Blo 334751 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B1433153 : Blo 334751 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B2154059 : Blo 334751 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B1138265 : Blo 334751 1138265 := bstep (se 2 (by rfl) ⟨426849, by rfl⟩ : syracuseStep 1138265 = 853699) B853699
theorem B2875085 : Blo 334751 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B1433305 : Blo 334751 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B1531979 : Blo 334751 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B1138967 : Blo 334751 1138967 := bstep (se 1 (by rfl) ⟨854225, by rfl⟩ : syracuseStep 1138967 = 1708451) B1708451
theorem B6545933 : Blo 334751 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B1696301 : Blo 334751 1696301 := bstep (se 3 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 1696301 = 636113) B636113
theorem B2155187 : Blo 334751 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B1139507 : Blo 334751 1139507 := bstep (se 1 (by rfl) ⟨854630, by rfl⟩ : syracuseStep 1139507 = 1709261) B1709261
theorem B3662657 : Blo 334751 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B1139777 : Blo 334751 1139777 := bstep (se 2 (by rfl) ⟨427416, by rfl⟩ : syracuseStep 1139777 = 854833) B854833
theorem B9757847 : Blo 334751 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B1074455 : Blo 334751 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B976151 : Blo 334751 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1730123 : Blo 334751 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B1140317 : Blo 334751 1140317 := bstep (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) B427619
theorem B976601 : Blo 334751 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B1926929 : Blo 334751 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B14772365 : Blo 334751 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B1927385 : Blo 334751 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B682265 : Blo 334751 682265 := bstep (se 2 (by rfl) ⟨255849, by rfl⟩ : syracuseStep 682265 = 511699) B511699
theorem B813377 : Blo 334751 813377 := bstep (se 2 (by rfl) ⟨305016, by rfl⟩ : syracuseStep 813377 = 610033) B610033
theorem B1829251 : Blo 334751 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1206701 : Blo 334751 1206701 := bstep (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) B452513
theorem B1272257 : Blo 334751 1272257 := bstep (se 2 (by rfl) ⟨477096, by rfl⟩ : syracuseStep 1272257 = 954193) B954193
theorem B2779609 : Blo 334751 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B1141451 : Blo 334751 1141451 := bstep (se 1 (by rfl) ⟨856088, by rfl⟩ : syracuseStep 1141451 = 1712177) B1712177
theorem B813847 : Blo 334751 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B1370969 : Blo 334751 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B1207219 : Blo 334751 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1141721 : Blo 334751 1141721 := bstep (se 2 (by rfl) ⟨428145, by rfl⟩ : syracuseStep 1141721 = 856291) B856291
theorem B715799 : Blo 334751 715799 := bstep (se 1 (by rfl) ⟨536849, by rfl⟩ : syracuseStep 715799 = 1073699) B1073699
theorem B1436723 : Blo 334751 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B453719 : Blo 334751 453719 := bstep (se 1 (by rfl) ⟨340289, by rfl⟩ : syracuseStep 453719 = 680579) B680579
theorem B1633459 : Blo 334751 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B715969 : Blo 334751 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B454027 : Blo 334751 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B454091 : Blo 334751 454091 := bstep (se 1 (by rfl) ⟨340568, by rfl⟩ : syracuseStep 454091 = 681137) B681137
theorem B716311 : Blo 334751 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B683635 : Blo 334751 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B1142423 : Blo 334751 1142423 := bstep (se 1 (by rfl) ⟨856817, by rfl⟩ : syracuseStep 1142423 = 1713635) B1713635
theorem B1076915 : Blo 334751 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B487193 : Blo 334751 487193 := bstep (se 2 (by rfl) ⟨182697, by rfl⟩ : syracuseStep 487193 = 365395) B365395
theorem B847705 : Blo 334751 847705 := bstep (se 2 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 847705 = 635779) B635779
theorem B1273745 : Blo 334751 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B1077337 : Blo 334751 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B3633245 : Blo 334751 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B4878467 : Blo 334751 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B2551985 : Blo 334751 2551985 := bstep (se 2 (by rfl) ⟨956994, by rfl⟩ : syracuseStep 2551985 = 1913989) B1913989
theorem B1142963 : Blo 334751 1142963 := bstep (se 1 (by rfl) ⟨857222, by rfl⟩ : syracuseStep 1142963 = 1714445) B1714445
theorem B684235 : Blo 334751 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B487705 : Blo 334751 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B2191661 : Blo 334751 2191661 := bstep (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) B821873
theorem B1077569 : Blo 334751 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B717131 : Blo 334751 717131 := bstep (se 1 (by rfl) ⟨537848, by rfl⟩ : syracuseStep 717131 = 1075697) B1075697
theorem B1274201 : Blo 334751 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1700189 : Blo 334751 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B1143233 : Blo 334751 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B1274413 : Blo 334751 1274413 := bstep (se 3 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 1274413 = 477905) B477905
theorem B1372717 : Blo 334751 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B13529693 : Blo 334751 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B2552471 : Blo 334751 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B717491 : Blo 334751 717491 := bstep (se 1 (by rfl) ⟨538118, by rfl⟩ : syracuseStep 717491 = 1076237) B1076237
theorem B455449 : Blo 334751 455449 := bstep (se 2 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 455449 = 341587) B341587
theorem B1274717 : Blo 334751 1274717 := bstep (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) B478019
theorem B848819 : Blo 334751 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B2946179 : Blo 334751 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B849113 : Blo 334751 849113 := bstep (se 2 (by rfl) ⟨318417, by rfl⟩ : syracuseStep 849113 = 636835) B636835
theorem B685273 : Blo 334751 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B357643 : Blo 334751 357643 := bstep (se 1 (by rfl) ⟨268232, by rfl⟩ : syracuseStep 357643 = 536465) B536465
theorem B1439491 : Blo 334751 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B423883 : Blo 334751 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B358391 : Blo 334751 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B1734929 : Blo 334751 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B457049 : Blo 334751 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B1702295 : Blo 334751 1702295 := bstep (se 1 (by rfl) ⟨1276721, by rfl⟩ : syracuseStep 1702295 = 2553443) B2553443
theorem B2226781 : Blo 334751 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B719489 : Blo 334751 719489 := bstep (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) B539617
theorem B1440449 : Blo 334751 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B1080029 : Blo 334751 1080029 := bstep (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) B405011
theorem B850763 : Blo 334751 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B1538909 : Blo 334751 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B424855 : Blo 334751 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B359659 : Blo 334751 359659 := bstep (se 1 (by rfl) ⟨269744, by rfl⟩ : syracuseStep 359659 = 539489) B539489
theorem B1277315 : Blo 334751 1277315 := bstep (se 1 (by rfl) ⟨957986, by rfl⟩ : syracuseStep 1277315 = 1915973) B1915973
theorem B1277329 : Blo 334751 1277329 := bstep (se 2 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 1277329 = 957997) B957997
theorem B720343 : Blo 334751 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B753227 : Blo 334751 753227 := bstep (se 1 (by rfl) ⟨564920, by rfl⟩ : syracuseStep 753227 = 1129841) B1129841
theorem B1211993 : Blo 334751 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B753281 : Blo 334751 753281 := bstep (se 2 (by rfl) ⟨282480, by rfl⟩ : syracuseStep 753281 = 564961) B564961
theorem B1277633 : Blo 334751 1277633 := bstep (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) B958225
theorem B425675 : Blo 334751 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B851735 : Blo 334751 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B753497 : Blo 334751 753497 := bstep (se 2 (by rfl) ⟨282561, by rfl⟩ : syracuseStep 753497 = 565123) B565123
theorem B753587 : Blo 334751 753587 := bstep (se 1 (by rfl) ⟨565190, by rfl⟩ : syracuseStep 753587 = 1130381) B1130381
theorem B753623 : Blo 334751 753623 := bstep (se 1 (by rfl) ⟨565217, by rfl⟩ : syracuseStep 753623 = 1130435) B1130435
theorem B360407 : Blo 334751 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B425999 : Blo 334751 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B1310957 : Blo 334751 1310957 := bstep (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) B491609
theorem B819575 : Blo 334751 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B754055 : Blo 334751 754055 := bstep (se 1 (by rfl) ⟨565541, by rfl⟩ : syracuseStep 754055 = 1131083) B1131083
theorem B1704401 : Blo 334751 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B754235 : Blo 334751 754235 := bstep (se 1 (by rfl) ⟨565676, by rfl⟩ : syracuseStep 754235 = 1131353) B1131353
theorem B361103 : Blo 334751 361103 := bstep (se 1 (by rfl) ⟨270827, by rfl⟩ : syracuseStep 361103 = 541655) B541655
theorem B754361 : Blo 334751 754361 := bstep (se 2 (by rfl) ⟨282885, by rfl⟩ : syracuseStep 754361 = 565771) B565771
theorem B2917093 : Blo 334751 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B361351 : Blo 334751 361351 := bstep (se 1 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 361351 = 542027) B542027
theorem B852889 : Blo 334751 852889 := bstep (se 2 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 852889 = 639667) B639667
theorem B721865 : Blo 334751 721865 := bstep (se 2 (by rfl) ⟨270699, by rfl⟩ : syracuseStep 721865 = 541399) B541399
theorem B754703 : Blo 334751 754703 := bstep (se 1 (by rfl) ⟨566027, by rfl⟩ : syracuseStep 754703 = 1132055) B1132055
theorem B754721 : Blo 334751 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B853051 : Blo 334751 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B853193 : Blo 334751 853193 := bstep (se 2 (by rfl) ⟨319947, by rfl⟩ : syracuseStep 853193 = 639895) B639895
theorem B755063 : Blo 334751 755063 := bstep (se 1 (by rfl) ⟨566297, by rfl⟩ : syracuseStep 755063 = 1132595) B1132595
theorem B2557331 : Blo 334751 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B1082771 : Blo 334751 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B853537 : Blo 334751 853537 := bstep (se 2 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 853537 = 640153) B640153
theorem B755243 : Blo 334751 755243 := bstep (se 1 (by rfl) ⟨566432, by rfl⟩ : syracuseStep 755243 = 1132865) B1132865
theorem B36079181 : Blo 334751 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B1279745 : Blo 334751 1279745 := bstep (se 2 (by rfl) ⟨479904, by rfl⟩ : syracuseStep 1279745 = 959809) B959809
theorem B1279759 : Blo 334751 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B755603 : Blo 334751 755603 := bstep (se 1 (by rfl) ⟨566702, by rfl⟩ : syracuseStep 755603 = 1133405) B1133405
theorem B755657 : Blo 334751 755657 := bstep (se 2 (by rfl) ⟨283371, by rfl⟩ : syracuseStep 755657 = 566743) B566743
theorem B5802029 : Blo 334751 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B854135 : Blo 334751 854135 := bstep (se 1 (by rfl) ⟨640601, by rfl⟩ : syracuseStep 854135 = 1281203) B1281203
theorem B5507345 : Blo 334751 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B11634961 : Blo 334751 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B1706507 : Blo 334751 1706507 := bstep (se 1 (by rfl) ⟨1279880, by rfl⟩ : syracuseStep 1706507 = 2559761) B2559761
theorem B756359 : Blo 334751 756359 := bstep (se 1 (by rfl) ⟨567269, by rfl⟩ : syracuseStep 756359 = 1134539) B1134539
theorem B1706669 : Blo 334751 1706669 := bstep (se 3 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 1706669 = 640001) B640001
theorem B1018639 : Blo 334751 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B756539 : Blo 334751 756539 := bstep (se 1 (by rfl) ⟨567404, by rfl⟩ : syracuseStep 756539 = 1134809) B1134809
theorem B756665 : Blo 334751 756665 := bstep (se 2 (by rfl) ⟨283749, by rfl⟩ : syracuseStep 756665 = 567499) B567499
theorem B1281035 : Blo 334751 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B757007 : Blo 334751 757007 := bstep (se 1 (by rfl) ⟨567755, by rfl⟩ : syracuseStep 757007 = 1135511) B1135511
theorem B757025 : Blo 334751 757025 := bstep (se 2 (by rfl) ⟨283884, by rfl⟩ : syracuseStep 757025 = 567769) B567769
theorem B3706145 : Blo 334751 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B855431 : Blo 334751 855431 := bstep (se 1 (by rfl) ⟨641573, by rfl⟩ : syracuseStep 855431 = 1283147) B1283147
theorem B2919827 : Blo 334751 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B855481 : Blo 334751 855481 := bstep (se 2 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 855481 = 641611) B641611
theorem B1085015 : Blo 334751 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B757367 : Blo 334751 757367 := bstep (se 1 (by rfl) ⟨568025, by rfl⟩ : syracuseStep 757367 = 1136051) B1136051
theorem B8261297 : Blo 334751 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B1085129 : Blo 334751 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B757547 : Blo 334751 757547 := bstep (se 1 (by rfl) ⟨568160, by rfl⟩ : syracuseStep 757547 = 1136321) B1136321
theorem B986941 : Blo 334751 986941 := bstep (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) B370103
theorem B2461529 : Blo 334751 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1609625 : Blo 334751 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B1281977 : Blo 334751 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B856079 : Blo 334751 856079 := bstep (se 1 (by rfl) ⟨642059, by rfl⟩ : syracuseStep 856079 = 1284119) B1284119
theorem B757907 : Blo 334751 757907 := bstep (se 1 (by rfl) ⟨568430, by rfl⟩ : syracuseStep 757907 = 1136861) B1136861
theorem B757961 : Blo 334751 757961 := bstep (se 2 (by rfl) ⟨284235, by rfl⟩ : syracuseStep 757961 = 568471) B568471
theorem B1708289 : Blo 334751 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B3281411 : Blo 334751 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B59609621 : Blo 334751 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B3707459 : Blo 334751 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B955081 : Blo 334751 955081 := bstep (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) B716311
theorem B856777 : Blo 334751 856777 := bstep (se 2 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 856777 = 642583) B642583
theorem B856919 : Blo 334751 856919 := bstep (se 1 (by rfl) ⟨642689, by rfl⟩ : syracuseStep 856919 = 1285379) B1285379
theorem B758663 : Blo 334751 758663 := bstep (se 1 (by rfl) ⟨568997, by rfl⟩ : syracuseStep 758663 = 1137995) B1137995
theorem B955435 : Blo 334751 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B1709099 : Blo 334751 1709099 := bstep (se 1 (by rfl) ⟨1281824, by rfl⟩ : syracuseStep 1709099 = 2563649) B2563649
theorem B758843 : Blo 334751 758843 := bstep (se 1 (by rfl) ⟨569132, by rfl⟩ : syracuseStep 758843 = 1138265) B1138265
theorem B758969 : Blo 334751 758969 := bstep (se 2 (by rfl) ⟨284613, by rfl⟩ : syracuseStep 758969 = 569227) B569227
theorem B955709 : Blo 334751 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B1021319 : Blo 334751 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B759311 : Blo 334751 759311 := bstep (se 1 (by rfl) ⟨569483, by rfl⟩ : syracuseStep 759311 = 1138967) B1138967
theorem B759329 : Blo 334751 759329 := bstep (se 2 (by rfl) ⟨284748, by rfl⟩ : syracuseStep 759329 = 569497) B569497
theorem B4363955 : Blo 334751 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B759671 : Blo 334751 759671 := bstep (se 1 (by rfl) ⟨569753, by rfl⟩ : syracuseStep 759671 = 1139507) B1139507
theorem B1906699 : Blo 334751 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B759851 : Blo 334751 759851 := bstep (se 1 (by rfl) ⟨569888, by rfl⟩ : syracuseStep 759851 = 1139777) B1139777
theorem B1218797 : Blo 334751 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B1710395 : Blo 334751 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B1317235 : Blo 334751 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1153415 : Blo 334751 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B760211 : Blo 334751 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B760265 : Blo 334751 760265 := bstep (se 2 (by rfl) ⟨285099, by rfl⟩ : syracuseStep 760265 = 570199) B570199
theorem B1710557 : Blo 334751 1710557 := bstep (se 3 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 1710557 = 641459) B641459
theorem B1284619 : Blo 334751 1284619 := bstep (se 1 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 1284619 = 1926929) B1926929
theorem B1710881 : Blo 334751 1710881 := bstep (se 2 (by rfl) ⟨641580, by rfl⟩ : syracuseStep 1710881 = 1283161) B1283161
theorem B1284923 : Blo 334751 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B334779 : Blo 334751 334779 := bstep (se 1 (by rfl) ⟨251084, by rfl⟩ : syracuseStep 334779 = 502169) B502169
theorem B334855 : Blo 334751 334855 := bstep (se 1 (by rfl) ⟨251141, by rfl⟩ : syracuseStep 334855 = 502283) B502283
theorem B334863 : Blo 334751 334863 := bstep (se 1 (by rfl) ⟨251147, by rfl⟩ : syracuseStep 334863 = 502295) B502295
theorem B334907 : Blo 334751 334907 := bstep (se 1 (by rfl) ⟨251180, by rfl⟩ : syracuseStep 334907 = 502361) B502361
theorem B334983 : Blo 334751 334983 := bstep (se 1 (by rfl) ⟨251237, by rfl⟩ : syracuseStep 334983 = 502475) B502475
theorem B760967 : Blo 334751 760967 := bstep (se 1 (by rfl) ⟨570725, by rfl⟩ : syracuseStep 760967 = 1141451) B1141451
theorem B334991 : Blo 334751 334991 := bstep (se 1 (by rfl) ⟨251243, by rfl⟩ : syracuseStep 334991 = 502487) B502487
theorem B335035 : Blo 334751 335035 := bstep (se 1 (by rfl) ⟨251276, by rfl⟩ : syracuseStep 335035 = 502553) B502553
theorem B335111 : Blo 334751 335111 := bstep (se 1 (by rfl) ⟨251333, by rfl⟩ : syracuseStep 335111 = 502667) B502667
theorem B335119 : Blo 334751 335119 := bstep (se 1 (by rfl) ⟨251339, by rfl⟩ : syracuseStep 335119 = 502679) B502679
theorem B1285409 : Blo 334751 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B335163 : Blo 334751 335163 := bstep (se 1 (by rfl) ⟨251372, by rfl⟩ : syracuseStep 335163 = 502745) B502745
theorem B761147 : Blo 334751 761147 := bstep (se 1 (by rfl) ⟨570860, by rfl⟩ : syracuseStep 761147 = 1141721) B1141721
theorem B957815 : Blo 334751 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B335239 : Blo 334751 335239 := bstep (se 1 (by rfl) ⟨251429, by rfl⟩ : syracuseStep 335239 = 502859) B502859
theorem B335247 : Blo 334751 335247 := bstep (se 1 (by rfl) ⟨251435, by rfl⟩ : syracuseStep 335247 = 502871) B502871
theorem B761273 : Blo 334751 761273 := bstep (se 2 (by rfl) ⟨285477, by rfl⟩ : syracuseStep 761273 = 570955) B570955
theorem B335291 : Blo 334751 335291 := bstep (se 1 (by rfl) ⟨251468, by rfl⟩ : syracuseStep 335291 = 502937) B502937
theorem B335367 : Blo 334751 335367 := bstep (se 1 (by rfl) ⟨251525, by rfl⟩ : syracuseStep 335367 = 503051) B503051
theorem B335375 : Blo 334751 335375 := bstep (se 1 (by rfl) ⟨251531, by rfl⟩ : syracuseStep 335375 = 503063) B503063
theorem B335419 : Blo 334751 335419 := bstep (se 1 (by rfl) ⟨251564, by rfl⟩ : syracuseStep 335419 = 503129) B503129
theorem B335495 : Blo 334751 335495 := bstep (se 1 (by rfl) ⟨251621, by rfl⟩ : syracuseStep 335495 = 503243) B503243
theorem B335503 : Blo 334751 335503 := bstep (se 1 (by rfl) ⟨251627, by rfl⟩ : syracuseStep 335503 = 503255) B503255
theorem B335547 : Blo 334751 335547 := bstep (se 1 (by rfl) ⟨251660, by rfl⟩ : syracuseStep 335547 = 503321) B503321
theorem B3219173 : Blo 334751 3219173 := bstep (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) B603595
theorem B2924261 : Blo 334751 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B1711853 : Blo 334751 1711853 := bstep (se 3 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 1711853 = 641945) B641945
theorem B335623 : Blo 334751 335623 := bstep (se 1 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 335623 = 503435) B503435
theorem B335631 : Blo 334751 335631 := bstep (se 1 (by rfl) ⟨251723, by rfl⟩ : syracuseStep 335631 = 503447) B503447
theorem B761615 : Blo 334751 761615 := bstep (se 1 (by rfl) ⟨571211, by rfl⟩ : syracuseStep 761615 = 1142423) B1142423
theorem B761633 : Blo 334751 761633 := bstep (se 2 (by rfl) ⟨285612, by rfl⟩ : syracuseStep 761633 = 571225) B571225
theorem B3841829 : Blo 334751 3841829 := bstep (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) B720343
theorem B335675 : Blo 334751 335675 := bstep (se 1 (by rfl) ⟨251756, by rfl⟩ : syracuseStep 335675 = 503513) B503513
theorem B335751 : Blo 334751 335751 := bstep (se 1 (by rfl) ⟨251813, by rfl⟩ : syracuseStep 335751 = 503627) B503627
theorem B335759 : Blo 334751 335759 := bstep (se 1 (by rfl) ⟨251819, by rfl⟩ : syracuseStep 335759 = 503639) B503639
theorem B565177 : Blo 334751 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B335803 : Blo 334751 335803 := bstep (se 1 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 335803 = 503705) B503705
theorem B1908683 : Blo 334751 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B335879 : Blo 334751 335879 := bstep (se 1 (by rfl) ⟨251909, by rfl⟩ : syracuseStep 335879 = 503819) B503819
theorem B335887 : Blo 334751 335887 := bstep (se 1 (by rfl) ⟨251915, by rfl⟩ : syracuseStep 335887 = 503831) B503831
theorem B335931 : Blo 334751 335931 := bstep (se 1 (by rfl) ⟨251948, by rfl⟩ : syracuseStep 335931 = 503897) B503897
theorem B3252311 : Blo 334751 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B761975 : Blo 334751 761975 := bstep (se 1 (by rfl) ⟨571481, by rfl⟩ : syracuseStep 761975 = 1142963) B1142963
theorem B336007 : Blo 334751 336007 := bstep (se 1 (by rfl) ⟨252005, by rfl⟩ : syracuseStep 336007 = 504011) B504011
theorem B336015 : Blo 334751 336015 := bstep (se 1 (by rfl) ⟨252011, by rfl⟩ : syracuseStep 336015 = 504023) B504023
theorem B336059 : Blo 334751 336059 := bstep (se 1 (by rfl) ⟨252044, by rfl⟩ : syracuseStep 336059 = 504089) B504089
theorem B336135 : Blo 334751 336135 := bstep (se 1 (by rfl) ⟨252101, by rfl⟩ : syracuseStep 336135 = 504203) B504203
theorem B336143 : Blo 334751 336143 := bstep (se 1 (by rfl) ⟨252107, by rfl⟩ : syracuseStep 336143 = 504215) B504215
theorem B762155 : Blo 334751 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B336187 : Blo 334751 336187 := bstep (se 1 (by rfl) ⟨252140, by rfl⟩ : syracuseStep 336187 = 504281) B504281
theorem B336263 : Blo 334751 336263 := bstep (se 1 (by rfl) ⟨252197, by rfl⟩ : syracuseStep 336263 = 504395) B504395
theorem B336271 : Blo 334751 336271 := bstep (se 1 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 336271 = 504407) B504407
theorem B336315 : Blo 334751 336315 := bstep (se 1 (by rfl) ⟨252236, by rfl⟩ : syracuseStep 336315 = 504473) B504473
theorem B336391 : Blo 334751 336391 := bstep (se 1 (by rfl) ⟨252293, by rfl⟩ : syracuseStep 336391 = 504587) B504587
theorem B336399 : Blo 334751 336399 := bstep (se 1 (by rfl) ⟨252299, by rfl⟩ : syracuseStep 336399 = 504599) B504599
theorem B1712663 : Blo 334751 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B336443 : Blo 334751 336443 := bstep (se 1 (by rfl) ⟨252332, by rfl⟩ : syracuseStep 336443 = 504665) B504665
theorem B565879 : Blo 334751 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B336519 : Blo 334751 336519 := bstep (se 1 (by rfl) ⟨252389, by rfl⟩ : syracuseStep 336519 = 504779) B504779
theorem B336527 : Blo 334751 336527 := bstep (se 1 (by rfl) ⟨252395, by rfl⟩ : syracuseStep 336527 = 504791) B504791
theorem B336571 : Blo 334751 336571 := bstep (se 1 (by rfl) ⟨252428, by rfl⟩ : syracuseStep 336571 = 504857) B504857
theorem B860873 : Blo 334751 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B336647 : Blo 334751 336647 := bstep (se 1 (by rfl) ⟨252485, by rfl⟩ : syracuseStep 336647 = 504971) B504971
theorem B336655 : Blo 334751 336655 := bstep (se 1 (by rfl) ⟨252491, by rfl⟩ : syracuseStep 336655 = 504983) B504983
theorem B2892581 : Blo 334751 2892581 := bstep (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) B542359
theorem B566075 : Blo 334751 566075 := bstep (se 1 (by rfl) ⟨424556, by rfl⟩ : syracuseStep 566075 = 849113) B849113
theorem B336699 : Blo 334751 336699 := bstep (se 1 (by rfl) ⟨252524, by rfl⟩ : syracuseStep 336699 = 505049) B505049
theorem B336775 : Blo 334751 336775 := bstep (se 1 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 336775 = 505163) B505163
theorem B336783 : Blo 334751 336783 := bstep (se 1 (by rfl) ⟨252587, by rfl⟩ : syracuseStep 336783 = 505175) B505175
theorem B336827 : Blo 334751 336827 := bstep (se 1 (by rfl) ⟨252620, by rfl⟩ : syracuseStep 336827 = 505241) B505241
theorem B336903 : Blo 334751 336903 := bstep (se 1 (by rfl) ⟨252677, by rfl⟩ : syracuseStep 336903 = 505355) B505355
theorem B336911 : Blo 334751 336911 := bstep (se 1 (by rfl) ⟨252683, by rfl⟩ : syracuseStep 336911 = 505367) B505367
theorem B336955 : Blo 334751 336955 := bstep (se 1 (by rfl) ⟨252716, by rfl⟩ : syracuseStep 336955 = 505433) B505433
theorem B337031 : Blo 334751 337031 := bstep (se 1 (by rfl) ⟨252773, by rfl⟩ : syracuseStep 337031 = 505547) B505547
theorem B402575 : Blo 334751 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B337039 : Blo 334751 337039 := bstep (se 1 (by rfl) ⟨252779, by rfl⟩ : syracuseStep 337039 = 505559) B505559
theorem B337083 : Blo 334751 337083 := bstep (se 1 (by rfl) ⟨252812, by rfl⟩ : syracuseStep 337083 = 505625) B505625
theorem B566473 : Blo 334751 566473 := bstep (se 2 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 566473 = 424855) B424855
theorem B1615085 : Blo 334751 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B337159 : Blo 334751 337159 := bstep (se 1 (by rfl) ⟨252869, by rfl⟩ : syracuseStep 337159 = 505739) B505739
theorem B337167 : Blo 334751 337167 := bstep (se 1 (by rfl) ⟨252875, by rfl⟩ : syracuseStep 337167 = 505751) B505751
theorem B337211 : Blo 334751 337211 := bstep (se 1 (by rfl) ⟨252908, by rfl⟩ : syracuseStep 337211 = 505817) B505817
theorem B337287 : Blo 334751 337287 := bstep (se 1 (by rfl) ⟨252965, by rfl⟩ : syracuseStep 337287 = 505931) B505931
theorem B337295 : Blo 334751 337295 := bstep (se 1 (by rfl) ⟨252971, by rfl⟩ : syracuseStep 337295 = 505943) B505943
theorem B337339 : Blo 334751 337339 := bstep (se 1 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 337339 = 506009) B506009
theorem B2893265 : Blo 334751 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B337415 : Blo 334751 337415 := bstep (se 1 (by rfl) ⟨253061, by rfl⟩ : syracuseStep 337415 = 506123) B506123
theorem B1156619 : Blo 334751 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B337423 : Blo 334751 337423 := bstep (se 1 (by rfl) ⟨253067, by rfl⟩ : syracuseStep 337423 = 506135) B506135
theorem B337467 : Blo 334751 337467 := bstep (se 1 (by rfl) ⟨253100, by rfl⟩ : syracuseStep 337467 = 506201) B506201
theorem B337543 : Blo 334751 337543 := bstep (se 1 (by rfl) ⟨253157, by rfl⟩ : syracuseStep 337543 = 506315) B506315
theorem B337551 : Blo 334751 337551 := bstep (se 1 (by rfl) ⟨253163, by rfl⟩ : syracuseStep 337551 = 506327) B506327
theorem B4990643 : Blo 334751 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B337595 : Blo 334751 337595 := bstep (se 1 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 337595 = 506393) B506393
theorem B1812169 : Blo 334751 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B337671 : Blo 334751 337671 := bstep (se 1 (by rfl) ⟨253253, by rfl⟩ : syracuseStep 337671 = 506507) B506507
theorem B337679 : Blo 334751 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B960299 : Blo 334751 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B337723 : Blo 334751 337723 := bstep (se 1 (by rfl) ⟨253292, by rfl⟩ : syracuseStep 337723 = 506585) B506585
theorem B18425717 : Blo 334751 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B567175 : Blo 334751 567175 := bstep (se 1 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 567175 = 850763) B850763
theorem B337799 : Blo 334751 337799 := bstep (se 1 (by rfl) ⟨253349, by rfl⟩ : syracuseStep 337799 = 506699) B506699
theorem B337807 : Blo 334751 337807 := bstep (se 1 (by rfl) ⟨253355, by rfl⟩ : syracuseStep 337807 = 506711) B506711
theorem B1025939 : Blo 334751 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B337851 : Blo 334751 337851 := bstep (se 1 (by rfl) ⟨253388, by rfl⟩ : syracuseStep 337851 = 506777) B506777
theorem B337927 : Blo 334751 337927 := bstep (se 1 (by rfl) ⟨253445, by rfl⟩ : syracuseStep 337927 = 506891) B506891
theorem B337935 : Blo 334751 337935 := bstep (se 1 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 337935 = 506903) B506903
theorem B337979 : Blo 334751 337979 := bstep (se 1 (by rfl) ⟨253484, by rfl⟩ : syracuseStep 337979 = 506969) B506969
theorem B338055 : Blo 334751 338055 := bstep (se 1 (by rfl) ⟨253541, by rfl⟩ : syracuseStep 338055 = 507083) B507083
theorem B338063 : Blo 334751 338063 := bstep (se 1 (by rfl) ⟨253547, by rfl⟩ : syracuseStep 338063 = 507095) B507095
theorem B403627 : Blo 334751 403627 := bstep (se 1 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 403627 = 605441) B605441
theorem B338107 : Blo 334751 338107 := bstep (se 1 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 338107 = 507161) B507161
theorem B338183 : Blo 334751 338183 := bstep (se 1 (by rfl) ⟨253637, by rfl⟩ : syracuseStep 338183 = 507275) B507275
theorem B338191 : Blo 334751 338191 := bstep (se 1 (by rfl) ⟨253643, by rfl⟩ : syracuseStep 338191 = 507287) B507287
theorem B1911073 : Blo 334751 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B338235 : Blo 334751 338235 := bstep (se 1 (by rfl) ⟨253676, by rfl⟩ : syracuseStep 338235 = 507353) B507353
theorem B502151 : Blo 334751 502151 := bstep (se 1 (by rfl) ⟨376613, by rfl⟩ : syracuseStep 502151 = 753227) B753227
theorem B338311 : Blo 334751 338311 := bstep (se 1 (by rfl) ⟨253733, by rfl⟩ : syracuseStep 338311 = 507467) B507467
theorem B338319 : Blo 334751 338319 := bstep (se 1 (by rfl) ⟨253739, by rfl⟩ : syracuseStep 338319 = 507479) B507479
theorem B502187 : Blo 334751 502187 := bstep (se 1 (by rfl) ⟨376640, by rfl⟩ : syracuseStep 502187 = 753281) B753281
theorem B338363 : Blo 334751 338363 := bstep (se 1 (by rfl) ⟨253772, by rfl⟩ : syracuseStep 338363 = 507545) B507545
theorem B502217 : Blo 334751 502217 := bstep (se 2 (by rfl) ⟨188331, by rfl⟩ : syracuseStep 502217 = 376663) B376663
theorem B338439 : Blo 334751 338439 := bstep (se 1 (by rfl) ⟨253829, by rfl⟩ : syracuseStep 338439 = 507659) B507659
theorem B567823 : Blo 334751 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B338447 : Blo 334751 338447 := bstep (se 1 (by rfl) ⟨253835, by rfl⟩ : syracuseStep 338447 = 507671) B507671
theorem B502331 : Blo 334751 502331 := bstep (se 1 (by rfl) ⟨376748, by rfl⟩ : syracuseStep 502331 = 753497) B753497
theorem B338491 : Blo 334751 338491 := bstep (se 1 (by rfl) ⟨253868, by rfl⟩ : syracuseStep 338491 = 507737) B507737
theorem B961085 : Blo 334751 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B3254849 : Blo 334751 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B12462659 : Blo 334751 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B502391 : Blo 334751 502391 := bstep (se 1 (by rfl) ⟨376793, by rfl⟩ : syracuseStep 502391 = 753587) B753587
theorem B338567 : Blo 334751 338567 := bstep (se 1 (by rfl) ⟨253925, by rfl⟩ : syracuseStep 338567 = 507851) B507851
theorem B502415 : Blo 334751 502415 := bstep (se 1 (by rfl) ⟨376811, by rfl⟩ : syracuseStep 502415 = 753623) B753623
theorem B338575 : Blo 334751 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B502457 : Blo 334751 502457 := bstep (se 2 (by rfl) ⟨188421, by rfl⟩ : syracuseStep 502457 = 376843) B376843
theorem B338619 : Blo 334751 338619 := bstep (se 1 (by rfl) ⟨253964, by rfl⟩ : syracuseStep 338619 = 507929) B507929
theorem B502535 : Blo 334751 502535 := bstep (se 1 (by rfl) ⟨376901, by rfl⟩ : syracuseStep 502535 = 753803) B753803
theorem B338695 : Blo 334751 338695 := bstep (se 1 (by rfl) ⟨254021, by rfl⟩ : syracuseStep 338695 = 508043) B508043
theorem B338703 : Blo 334751 338703 := bstep (se 1 (by rfl) ⟨254027, by rfl⟩ : syracuseStep 338703 = 508055) B508055
theorem B502571 : Blo 334751 502571 := bstep (se 1 (by rfl) ⟨376928, by rfl⟩ : syracuseStep 502571 = 753857) B753857
theorem B1616699 : Blo 334751 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B338747 : Blo 334751 338747 := bstep (se 1 (by rfl) ⟨254060, by rfl⟩ : syracuseStep 338747 = 508121) B508121
theorem B502601 : Blo 334751 502601 := bstep (se 2 (by rfl) ⟨188475, by rfl⟩ : syracuseStep 502601 = 376951) B376951
theorem B961415 : Blo 334751 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B2632601 : Blo 334751 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B502715 : Blo 334751 502715 := bstep (se 1 (by rfl) ⟨377036, by rfl⟩ : syracuseStep 502715 = 754073) B754073
theorem B502775 : Blo 334751 502775 := bstep (se 1 (by rfl) ⟨377081, by rfl⟩ : syracuseStep 502775 = 754163) B754163
theorem B502799 : Blo 334751 502799 := bstep (se 1 (by rfl) ⟨377099, by rfl⟩ : syracuseStep 502799 = 754199) B754199
theorem B568363 : Blo 334751 568363 := bstep (se 1 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 568363 = 852545) B852545
theorem B502841 : Blo 334751 502841 := bstep (se 2 (by rfl) ⟨188565, by rfl⟩ : syracuseStep 502841 = 377131) B377131
theorem B502919 : Blo 334751 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B502955 : Blo 334751 502955 := bstep (se 1 (by rfl) ⟨377216, by rfl⟩ : syracuseStep 502955 = 754433) B754433
theorem B568505 : Blo 334751 568505 := bstep (se 2 (by rfl) ⟨213189, by rfl⟩ : syracuseStep 568505 = 426379) B426379
theorem B502985 : Blo 334751 502985 := bstep (se 2 (by rfl) ⟨188619, by rfl⟩ : syracuseStep 502985 = 377239) B377239
theorem B503099 : Blo 334751 503099 := bstep (se 1 (by rfl) ⟨377324, by rfl⟩ : syracuseStep 503099 = 754649) B754649
theorem B503159 : Blo 334751 503159 := bstep (se 1 (by rfl) ⟨377369, by rfl⟩ : syracuseStep 503159 = 754739) B754739
theorem B503183 : Blo 334751 503183 := bstep (se 1 (by rfl) ⟨377387, by rfl⟩ : syracuseStep 503183 = 754775) B754775
theorem B503225 : Blo 334751 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B503303 : Blo 334751 503303 := bstep (se 1 (by rfl) ⟨377477, by rfl⟩ : syracuseStep 503303 = 754955) B754955
theorem B1912349 : Blo 334751 1912349 := bstep (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) B717131
theorem B503339 : Blo 334751 503339 := bstep (se 1 (by rfl) ⟨377504, by rfl⟩ : syracuseStep 503339 = 755009) B755009
theorem B503369 : Blo 334751 503369 := bstep (se 2 (by rfl) ⟨188763, by rfl⟩ : syracuseStep 503369 = 377527) B377527
theorem B765587 : Blo 334751 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B503483 : Blo 334751 503483 := bstep (se 1 (by rfl) ⟨377612, by rfl⟩ : syracuseStep 503483 = 755225) B755225
theorem B503543 : Blo 334751 503543 := bstep (se 1 (by rfl) ⟨377657, by rfl⟩ : syracuseStep 503543 = 755315) B755315
theorem B503567 : Blo 334751 503567 := bstep (se 1 (by rfl) ⟨377675, by rfl⟩ : syracuseStep 503567 = 755351) B755351
theorem B1027873 : Blo 334751 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B503609 : Blo 334751 503609 := bstep (se 2 (by rfl) ⟨188853, by rfl⟩ : syracuseStep 503609 = 377707) B377707
theorem B569207 : Blo 334751 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B503687 : Blo 334751 503687 := bstep (se 1 (by rfl) ⟨377765, by rfl⟩ : syracuseStep 503687 = 755531) B755531
theorem B503723 : Blo 334751 503723 := bstep (se 1 (by rfl) ⟨377792, by rfl⟩ : syracuseStep 503723 = 755585) B755585
theorem B503753 : Blo 334751 503753 := bstep (se 2 (by rfl) ⟨188907, by rfl⟩ : syracuseStep 503753 = 377815) B377815
theorem B10399691 : Blo 334751 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B503867 : Blo 334751 503867 := bstep (se 1 (by rfl) ⟨377900, by rfl⟩ : syracuseStep 503867 = 755801) B755801
theorem B1224791 : Blo 334751 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B503927 : Blo 334751 503927 := bstep (se 1 (by rfl) ⟨377945, by rfl⟩ : syracuseStep 503927 = 755891) B755891
theorem B503951 : Blo 334751 503951 := bstep (se 1 (by rfl) ⟨377963, by rfl⟩ : syracuseStep 503951 = 755927) B755927
theorem B503993 : Blo 334751 503993 := bstep (se 2 (by rfl) ⟨188997, by rfl⟩ : syracuseStep 503993 = 377995) B377995
theorem B504071 : Blo 334751 504071 := bstep (se 1 (by rfl) ⟨378053, by rfl⟩ : syracuseStep 504071 = 756107) B756107
theorem B504107 : Blo 334751 504107 := bstep (se 1 (by rfl) ⟨378080, by rfl⟩ : syracuseStep 504107 = 756161) B756161
theorem B569659 : Blo 334751 569659 := bstep (se 1 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 569659 = 854489) B854489
theorem B504137 : Blo 334751 504137 := bstep (se 2 (by rfl) ⟨189051, by rfl⟩ : syracuseStep 504137 = 378103) B378103
theorem B504251 : Blo 334751 504251 := bstep (se 1 (by rfl) ⟨378188, by rfl⟩ : syracuseStep 504251 = 756377) B756377
theorem B569801 : Blo 334751 569801 := bstep (se 2 (by rfl) ⟨213675, by rfl⟩ : syracuseStep 569801 = 427351) B427351
theorem B504311 : Blo 334751 504311 := bstep (se 1 (by rfl) ⟨378233, by rfl⟩ : syracuseStep 504311 = 756467) B756467
theorem B504335 : Blo 334751 504335 := bstep (se 1 (by rfl) ⟨378251, by rfl⟩ : syracuseStep 504335 = 756503) B756503
theorem B537131 : Blo 334751 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B504377 : Blo 334751 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B963191 : Blo 334751 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B504455 : Blo 334751 504455 := bstep (se 1 (by rfl) ⟨378341, by rfl⟩ : syracuseStep 504455 = 756683) B756683
theorem B504491 : Blo 334751 504491 := bstep (se 1 (by rfl) ⟨378368, by rfl⟩ : syracuseStep 504491 = 756737) B756737
theorem B504521 : Blo 334751 504521 := bstep (se 2 (by rfl) ⟨189195, by rfl⟩ : syracuseStep 504521 = 378391) B378391
theorem B635681 : Blo 334751 635681 := bstep (se 2 (by rfl) ⟨238380, by rfl⟩ : syracuseStep 635681 = 476761) B476761
theorem B8237861 : Blo 334751 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B504635 : Blo 334751 504635 := bstep (se 1 (by rfl) ⟨378476, by rfl⟩ : syracuseStep 504635 = 756953) B756953
theorem B504695 : Blo 334751 504695 := bstep (se 1 (by rfl) ⟨378521, by rfl⟩ : syracuseStep 504695 = 757043) B757043
theorem B504719 : Blo 334751 504719 := bstep (se 1 (by rfl) ⟨378539, by rfl⟩ : syracuseStep 504719 = 757079) B757079
theorem B504761 : Blo 334751 504761 := bstep (se 2 (by rfl) ⟨189285, by rfl⟩ : syracuseStep 504761 = 378571) B378571
theorem B504839 : Blo 334751 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B504875 : Blo 334751 504875 := bstep (se 1 (by rfl) ⟨378656, by rfl⟩ : syracuseStep 504875 = 757313) B757313
theorem B504905 : Blo 334751 504905 := bstep (se 2 (by rfl) ⟨189339, by rfl⟩ : syracuseStep 504905 = 378679) B378679
theorem B570503 : Blo 334751 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B505019 : Blo 334751 505019 := bstep (se 1 (by rfl) ⟨378764, by rfl⟩ : syracuseStep 505019 = 757529) B757529
theorem B1455341 : Blo 334751 1455341 := bstep (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) B545753
theorem B505079 : Blo 334751 505079 := bstep (se 1 (by rfl) ⟨378809, by rfl⟩ : syracuseStep 505079 = 757619) B757619
theorem B505103 : Blo 334751 505103 := bstep (se 1 (by rfl) ⟨378827, by rfl⟩ : syracuseStep 505103 = 757655) B757655
theorem B505145 : Blo 334751 505145 := bstep (se 2 (by rfl) ⟨189429, by rfl⟩ : syracuseStep 505145 = 378859) B378859
theorem B505223 : Blo 334751 505223 := bstep (se 1 (by rfl) ⟨378917, by rfl⟩ : syracuseStep 505223 = 757835) B757835
theorem B505259 : Blo 334751 505259 := bstep (se 1 (by rfl) ⟨378944, by rfl⟩ : syracuseStep 505259 = 757889) B757889
theorem B505289 : Blo 334751 505289 := bstep (se 2 (by rfl) ⟨189483, by rfl⟩ : syracuseStep 505289 = 378967) B378967
theorem B505403 : Blo 334751 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B964183 : Blo 334751 964183 := bstep (se 1 (by rfl) ⟨723137, by rfl⟩ : syracuseStep 964183 = 1446275) B1446275
theorem B505463 : Blo 334751 505463 := bstep (se 1 (by rfl) ⟨379097, by rfl⟩ : syracuseStep 505463 = 758195) B758195
theorem B505487 : Blo 334751 505487 := bstep (se 1 (by rfl) ⟨379115, by rfl⟩ : syracuseStep 505487 = 758231) B758231
theorem B505529 : Blo 334751 505529 := bstep (se 2 (by rfl) ⟨189573, by rfl⟩ : syracuseStep 505529 = 379147) B379147
theorem B505607 : Blo 334751 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B571151 : Blo 334751 571151 := bstep (se 1 (by rfl) ⟨428363, by rfl⟩ : syracuseStep 571151 = 856727) B856727
theorem B505643 : Blo 334751 505643 := bstep (se 1 (by rfl) ⟨379232, by rfl⟩ : syracuseStep 505643 = 758465) B758465
theorem B505673 : Blo 334751 505673 := bstep (se 2 (by rfl) ⟨189627, by rfl⟩ : syracuseStep 505673 = 379255) B379255
theorem B2439001 : Blo 334751 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B505787 : Blo 334751 505787 := bstep (se 1 (by rfl) ⟨379340, by rfl⟩ : syracuseStep 505787 = 758681) B758681
theorem B505847 : Blo 334751 505847 := bstep (se 1 (by rfl) ⟨379385, by rfl⟩ : syracuseStep 505847 = 758771) B758771
theorem B505871 : Blo 334751 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B505913 : Blo 334751 505913 := bstep (se 2 (by rfl) ⟨189717, by rfl⟩ : syracuseStep 505913 = 379435) B379435
theorem B1914947 : Blo 334751 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B505991 : Blo 334751 505991 := bstep (se 1 (by rfl) ⟨379493, by rfl⟩ : syracuseStep 505991 = 758987) B758987
theorem B506027 : Blo 334751 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B506057 : Blo 334751 506057 := bstep (se 2 (by rfl) ⟨189771, by rfl⟩ : syracuseStep 506057 = 379543) B379543
theorem B506171 : Blo 334751 506171 := bstep (se 1 (by rfl) ⟨379628, by rfl⟩ : syracuseStep 506171 = 759257) B759257
theorem B506231 : Blo 334751 506231 := bstep (se 1 (by rfl) ⟨379673, by rfl⟩ : syracuseStep 506231 = 759347) B759347
theorem B506255 : Blo 334751 506255 := bstep (se 1 (by rfl) ⟨379691, by rfl⟩ : syracuseStep 506255 = 759383) B759383
theorem B7256465 : Blo 334751 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B506297 : Blo 334751 506297 := bstep (se 2 (by rfl) ⟨189861, by rfl⟩ : syracuseStep 506297 = 379723) B379723
theorem B506375 : Blo 334751 506375 := bstep (se 1 (by rfl) ⟨379781, by rfl⟩ : syracuseStep 506375 = 759563) B759563
theorem B506411 : Blo 334751 506411 := bstep (se 1 (by rfl) ⟨379808, by rfl⟩ : syracuseStep 506411 = 759617) B759617
theorem B506441 : Blo 334751 506441 := bstep (se 2 (by rfl) ⟨189915, by rfl⟩ : syracuseStep 506441 = 379831) B379831
theorem B637625 : Blo 334751 637625 := bstep (se 2 (by rfl) ⟨239109, by rfl⟩ : syracuseStep 637625 = 478219) B478219
theorem B506555 : Blo 334751 506555 := bstep (se 1 (by rfl) ⟨379916, by rfl⟩ : syracuseStep 506555 = 759833) B759833
theorem B506615 : Blo 334751 506615 := bstep (se 1 (by rfl) ⟨379961, by rfl⟩ : syracuseStep 506615 = 759923) B759923
theorem B506639 : Blo 334751 506639 := bstep (se 1 (by rfl) ⟨379979, by rfl⟩ : syracuseStep 506639 = 759959) B759959
theorem B506681 : Blo 334751 506681 := bstep (se 2 (by rfl) ⟨190005, by rfl⟩ : syracuseStep 506681 = 380011) B380011
theorem B1096507 : Blo 334751 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B506759 : Blo 334751 506759 := bstep (se 1 (by rfl) ⟨380069, by rfl⟩ : syracuseStep 506759 = 760139) B760139
theorem B2177945 : Blo 334751 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B506795 : Blo 334751 506795 := bstep (se 1 (by rfl) ⟨380096, by rfl⟩ : syracuseStep 506795 = 760193) B760193
theorem B506825 : Blo 334751 506825 := bstep (se 2 (by rfl) ⟨190059, by rfl⟩ : syracuseStep 506825 = 380119) B380119
theorem B506939 : Blo 334751 506939 := bstep (se 1 (by rfl) ⟨380204, by rfl⟩ : syracuseStep 506939 = 760409) B760409
theorem B506999 : Blo 334751 506999 := bstep (se 1 (by rfl) ⟨380249, by rfl⟩ : syracuseStep 506999 = 760499) B760499
theorem B507023 : Blo 334751 507023 := bstep (se 1 (by rfl) ⟨380267, by rfl⟩ : syracuseStep 507023 = 760535) B760535
theorem B605369 : Blo 334751 605369 := bstep (se 2 (by rfl) ⟨227013, by rfl⟩ : syracuseStep 605369 = 454027) B454027
theorem B507065 : Blo 334751 507065 := bstep (se 2 (by rfl) ⟨190149, by rfl⟩ : syracuseStep 507065 = 380299) B380299
theorem B2604269 : Blo 334751 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B507143 : Blo 334751 507143 := bstep (se 1 (by rfl) ⟨380357, by rfl⟩ : syracuseStep 507143 = 760715) B760715
theorem B507179 : Blo 334751 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B1129787 : Blo 334751 1129787 := bstep (se 1 (by rfl) ⟨847340, by rfl⟩ : syracuseStep 1129787 = 1694681) B1694681
theorem B507209 : Blo 334751 507209 := bstep (se 2 (by rfl) ⟨190203, by rfl⟩ : syracuseStep 507209 = 380407) B380407
theorem B507323 : Blo 334751 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B507383 : Blo 334751 507383 := bstep (se 1 (by rfl) ⟨380537, by rfl⟩ : syracuseStep 507383 = 761075) B761075
theorem B507407 : Blo 334751 507407 := bstep (se 1 (by rfl) ⟨380555, by rfl⟩ : syracuseStep 507407 = 761111) B761111
theorem B507449 : Blo 334751 507449 := bstep (se 2 (by rfl) ⟨190293, by rfl⟩ : syracuseStep 507449 = 380587) B380587
theorem B507527 : Blo 334751 507527 := bstep (se 1 (by rfl) ⟨380645, by rfl⟩ : syracuseStep 507527 = 761291) B761291
theorem B507563 : Blo 334751 507563 := bstep (se 1 (by rfl) ⟨380672, by rfl⟩ : syracuseStep 507563 = 761345) B761345
theorem B507593 : Blo 334751 507593 := bstep (se 2 (by rfl) ⟨190347, by rfl⟩ : syracuseStep 507593 = 380695) B380695
theorem B1130273 : Blo 334751 1130273 := bstep (se 2 (by rfl) ⟨423852, by rfl⟩ : syracuseStep 1130273 = 847705) B847705
theorem B1916723 : Blo 334751 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B638779 : Blo 334751 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B507707 : Blo 334751 507707 := bstep (se 1 (by rfl) ⟨380780, by rfl⟩ : syracuseStep 507707 = 761561) B761561
theorem B507767 : Blo 334751 507767 := bstep (se 1 (by rfl) ⟨380825, by rfl⟩ : syracuseStep 507767 = 761651) B761651
theorem B507791 : Blo 334751 507791 := bstep (se 1 (by rfl) ⟨380843, by rfl⟩ : syracuseStep 507791 = 761687) B761687
theorem B507833 : Blo 334751 507833 := bstep (se 2 (by rfl) ⟨190437, by rfl⟩ : syracuseStep 507833 = 380875) B380875
theorem B507911 : Blo 334751 507911 := bstep (se 1 (by rfl) ⟨380933, by rfl⟩ : syracuseStep 507911 = 761867) B761867
theorem B507947 : Blo 334751 507947 := bstep (se 1 (by rfl) ⟨380960, by rfl⟩ : syracuseStep 507947 = 761921) B761921
theorem B507977 : Blo 334751 507977 := bstep (se 2 (by rfl) ⟨190491, by rfl⟩ : syracuseStep 507977 = 380983) B380983
theorem B7356509 : Blo 334751 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B508091 : Blo 334751 508091 := bstep (se 1 (by rfl) ⟨381068, by rfl⟩ : syracuseStep 508091 = 762137) B762137
theorem B377095 : Blo 334751 377095 := bstep (se 1 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 377095 = 565643) B565643
theorem B639265 : Blo 334751 639265 := bstep (se 2 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 639265 = 479449) B479449
theorem B1130867 : Blo 334751 1130867 := bstep (se 1 (by rfl) ⟨848150, by rfl⟩ : syracuseStep 1130867 = 1696301) B1696301
theorem B377275 : Blo 334751 377275 := bstep (se 1 (by rfl) ⟨282956, by rfl⟩ : syracuseStep 377275 = 565913) B565913
theorem B541129 : Blo 334751 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B2441771 : Blo 334751 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B2147087 : Blo 334751 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B6505231 : Blo 334751 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B770951 : Blo 334751 770951 := bstep (se 1 (by rfl) ⟨578213, by rfl⟩ : syracuseStep 770951 = 1156427) B1156427
theorem B377743 : Blo 334751 377743 := bstep (se 1 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 377743 = 566615) B566615
theorem B3818501 : Blo 334751 3818501 := bstep (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) B715969
theorem B607265 : Blo 334751 607265 := bstep (se 2 (by rfl) ⟨227724, by rfl⟩ : syracuseStep 607265 = 455449) B455449
theorem B1623233 : Blo 334751 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B1918181 : Blo 334751 1918181 := bstep (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) B359659
theorem B3655043 : Blo 334751 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B378247 : Blo 334751 378247 := bstep (se 1 (by rfl) ⟨283685, by rfl⟩ : syracuseStep 378247 = 567371) B567371
theorem B9848243 : Blo 334751 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B640457 : Blo 334751 640457 := bstep (se 2 (by rfl) ⟨240171, by rfl⟩ : syracuseStep 640457 = 480343) B480343
theorem B1590749 : Blo 334751 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B542251 : Blo 334751 542251 := bstep (se 1 (by rfl) ⟨406688, by rfl⟩ : syracuseStep 542251 = 813377) B813377
theorem B378427 : Blo 334751 378427 := bstep (se 1 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 378427 = 567641) B567641
theorem B804467 : Blo 334751 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B804505 : Blo 334751 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B1918637 : Blo 334751 1918637 := bstep (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) B719489
theorem B476857 : Blo 334751 476857 := bstep (se 2 (by rfl) ⟨178821, by rfl⟩ : syracuseStep 476857 = 357643) B357643
theorem B477199 : Blo 334751 477199 := bstep (se 1 (by rfl) ⟨357899, by rfl⟩ : syracuseStep 477199 = 715799) B715799
theorem B378895 : Blo 334751 378895 := bstep (se 1 (by rfl) ⟨284171, by rfl⟩ : syracuseStep 378895 = 568343) B568343
theorem B641171 : Blo 334751 641171 := bstep (se 1 (by rfl) ⟨480878, by rfl⟩ : syracuseStep 641171 = 961757) B961757
theorem B641209 : Blo 334751 641209 := bstep (se 2 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 641209 = 480907) B480907
theorem B1296641 : Blo 334751 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B1919321 : Blo 334751 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B379399 : Blo 334751 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B9226871 : Blo 334751 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B379579 : Blo 334751 379579 := bstep (se 1 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 379579 = 569369) B569369
theorem B1461107 : Blo 334751 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B1133459 : Blo 334751 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B805889 : Blo 334751 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B478327 : Blo 334751 478327 := bstep (se 1 (by rfl) ⟨358745, by rfl⟩ : syracuseStep 478327 = 717491) B717491
theorem B380047 : Blo 334751 380047 := bstep (se 1 (by rfl) ⟨285035, by rfl⟩ : syracuseStep 380047 = 570071) B570071
theorem B2969041 : Blo 334751 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B380551 : Blo 334751 380551 := bstep (se 1 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 380551 = 570827) B570827
theorem B380731 : Blo 334751 380731 := bstep (se 1 (by rfl) ⟨285548, by rfl⟩ : syracuseStep 380731 = 571097) B571097
theorem B1134863 : Blo 334751 1134863 := bstep (se 1 (by rfl) ⟨851147, by rfl⟩ : syracuseStep 1134863 = 1702295) B1702295
theorem B2871773 : Blo 334751 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B1135133 : Blo 334751 1135133 := bstep (se 3 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 1135133 = 425675) B425675
theorem B1299181 : Blo 334751 1299181 := bstep (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) B487193
theorem B971531 : Blo 334751 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B3068761 : Blo 334751 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1430419 : Blo 334751 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B1364921 : Blo 334751 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B807995 : Blo 334751 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B2545181 : Blo 334751 2545181 := bstep (se 3 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 2545181 = 954443) B954443
theorem B481015 : Blo 334751 481015 := bstep (se 1 (by rfl) ⟨360761, by rfl⟩ : syracuseStep 481015 = 721523) B721523
theorem B6444953 : Blo 334751 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B1136537 : Blo 334751 1136537 := bstep (se 2 (by rfl) ⟨426201, by rfl⟩ : syracuseStep 1136537 = 852403) B852403
theorem B809003 : Blo 334751 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B1432075 : Blo 334751 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B481835 : Blo 334751 481835 := bstep (se 1 (by rfl) ⟨361376, by rfl⟩ : syracuseStep 481835 = 722753) B722753
theorem B1137239 : Blo 334751 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B514831 : Blo 334751 514831 := bstep (se 1 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 514831 = 772247) B772247
theorem B809771 : Blo 334751 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B1530809 : Blo 334751 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B1137725 : Blo 334751 1137725 := bstep (se 3 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 1137725 = 426647) B426647
theorem B810071 : Blo 334751 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B613511 : Blo 334751 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B3235393 : Blo 334751 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B2056157 : Blo 334751 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B1139129 : Blo 334751 1139129 := bstep (se 2 (by rfl) ⟨427173, by rfl⟩ : syracuseStep 1139129 = 854347) B854347
theorem B3236395 : Blo 334751 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B811579 : Blo 334751 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B1368695 : Blo 334751 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B615047 : Blo 334751 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B3629873 : Blo 334751 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1139723 : Blo 334751 1139723 := bstep (se 1 (by rfl) ⟨854792, by rfl⟩ : syracuseStep 1139723 = 1709585) B1709585
theorem B680975 : Blo 334751 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B1139831 : Blo 334751 1139831 := bstep (se 1 (by rfl) ⟨854873, by rfl⟩ : syracuseStep 1139831 = 1709747) B1709747
theorem B6448643 : Blo 334751 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B1271497 : Blo 334751 1271497 := bstep (se 2 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 1271497 = 953623) B953623
theorem B1140425 : Blo 334751 1140425 := bstep (se 2 (by rfl) ⟨427659, by rfl⟩ : syracuseStep 1140425 = 855319) B855319
theorem B1631981 : Blo 334751 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B2549555 : Blo 334751 2549555 := bstep (se 1 (by rfl) ⟨1912166, by rfl⟩ : syracuseStep 2549555 = 3824333) B3824333
theorem B1632209 : Blo 334751 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B4843637 : Blo 334751 4843637 := bstep (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) B454091
theorem B911513 : Blo 334751 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B5171401 : Blo 334751 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B1436039 : Blo 334751 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1141127 : Blo 334751 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B1075799 : Blo 334751 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B813655 : Blo 334751 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B813769 : Blo 334751 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B1141505 : Blo 334751 1141505 := bstep (se 2 (by rfl) ⟨428064, by rfl⟩ : syracuseStep 1141505 = 856129) B856129
theorem B1436449 : Blo 334751 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B912313 : Blo 334751 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B650273 : Blo 334751 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B1436791 : Blo 334751 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1699217 : Blo 334751 1699217 := bstep (se 2 (by rfl) ⟨637206, by rfl⟩ : syracuseStep 1699217 = 1274413) B1274413
theorem B1830289 : Blo 334751 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1535441 : Blo 334751 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B847361 : Blo 334751 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B716303 : Blo 334751 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B650767 : Blo 334751 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B1142315 : Blo 334751 1142315 := bstep (se 1 (by rfl) ⟨856736, by rfl⟩ : syracuseStep 1142315 = 1713473) B1713473
theorem B1273715 : Blo 334751 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B1929095 : Blo 334751 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B847817 : Blo 334751 847817 := bstep (se 2 (by rfl) ⟨317931, by rfl⟩ : syracuseStep 847817 = 635863) B635863
theorem B683977 : Blo 334751 683977 := bstep (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) B512983
theorem B454843 : Blo 334751 454843 := bstep (se 1 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 454843 = 682265) B682265
theorem B913697 : Blo 334751 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B848171 : Blo 334751 848171 := bstep (se 1 (by rfl) ⟨636128, by rfl⟩ : syracuseStep 848171 = 1272257) B1272257
theorem B913979 : Blo 334751 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B849163 : Blo 334751 849163 := bstep (se 1 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 849163 = 1273745) B1273745
theorem B2422163 : Blo 334751 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B849305 : Blo 334751 849305 := bstep (se 2 (by rfl) ⟨318489, by rfl⟩ : syracuseStep 849305 = 636979) B636979
theorem B1701323 : Blo 334751 1701323 := bstep (se 1 (by rfl) ⟨1275992, by rfl⟩ : syracuseStep 1701323 = 2551985) B2551985
theorem B718379 : Blo 334751 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B849467 : Blo 334751 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B1209917 : Blo 334751 1209917 := bstep (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) B453719
theorem B1701647 : Blo 334751 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B849811 : Blo 334751 849811 := bstep (se 1 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 849811 = 1274717) B1274717
theorem B5339033 : Blo 334751 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1275857 : Blo 334751 1275857 := bstep (se 2 (by rfl) ⟨478446, by rfl⟩ : syracuseStep 1275857 = 956893) B956893
theorem B849953 : Blo 334751 849953 := bstep (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) B637465
theorem B1964119 : Blo 334751 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B424055 : Blo 334751 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B2160877 : Blo 334751 2160877 := bstep (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) B810329
theorem B424207 : Blo 334751 424207 := bstep (se 1 (by rfl) ⟨318155, by rfl⟩ : syracuseStep 424207 = 636311) B636311
theorem B1276175 : Blo 334751 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B424379 : Blo 334751 424379 := bstep (se 1 (by rfl) ⟨318284, by rfl⟩ : syracuseStep 424379 = 636569) B636569
theorem B1210967 : Blo 334751 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B850945 : Blo 334751 850945 := bstep (se 2 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 850945 = 638209) B638209
theorem B720019 : Blo 334751 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B1703105 : Blo 334751 1703105 := bstep (se 2 (by rfl) ⟨638664, by rfl⟩ : syracuseStep 1703105 = 1277329) B1277329
theorem B10386629 : Blo 334751 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B425351 : Blo 334751 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B851543 : Blo 334751 851543 := bstep (se 1 (by rfl) ⟨638657, by rfl⟩ : syracuseStep 851543 = 1277315) B1277315
theorem B753299 : Blo 334751 753299 := bstep (se 1 (by rfl) ⟨564974, by rfl⟩ : syracuseStep 753299 = 1129949) B1129949
theorem B753353 : Blo 334751 753353 := bstep (se 2 (by rfl) ⟨282507, by rfl⟩ : syracuseStep 753353 = 565015) B565015
theorem B2457317 : Blo 334751 2457317 := bstep (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) B460747
theorem B851755 : Blo 334751 851755 := bstep (se 1 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 851755 = 1277633) B1277633
theorem B851897 : Blo 334751 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B753911 : Blo 334751 753911 := bstep (se 1 (by rfl) ⟨565433, by rfl⟩ : syracuseStep 753911 = 1130867) B1130867
theorem B852353 : Blo 334751 852353 := bstep (se 2 (by rfl) ⟨319632, by rfl⟩ : syracuseStep 852353 = 639265) B639265
theorem B721505 : Blo 334751 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B1082105 : Blo 334751 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B1082155 : Blo 334751 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B1278787 : Blo 334751 1278787 := bstep (se 1 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 1278787 = 1918181) B1918181
theorem B754505 : Blo 334751 754505 := bstep (se 2 (by rfl) ⟨282939, by rfl⟩ : syracuseStep 754505 = 565879) B565879
theorem B1704887 : Blo 334751 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B721847 : Blo 334751 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B426971 : Blo 334751 426971 := bstep (se 1 (by rfl) ⟨320228, by rfl⟩ : syracuseStep 426971 = 640457) B640457
theorem B24052787 : Blo 334751 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1279091 : Blo 334751 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B853163 : Blo 334751 853163 := bstep (se 1 (by rfl) ⟨639872, by rfl⟩ : syracuseStep 853163 = 1279745) B1279745
theorem B8750429 : Blo 334751 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B3868019 : Blo 334751 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B427447 : Blo 334751 427447 := bstep (se 1 (by rfl) ⟨320585, by rfl⟩ : syracuseStep 427447 = 641171) B641171
theorem B3671563 : Blo 334751 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1279547 : Blo 334751 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B755297 : Blo 334751 755297 := bstep (se 2 (by rfl) ⟨283236, by rfl⟩ : syracuseStep 755297 = 566473) B566473
theorem B1640125 : Blo 334751 1640125 := bstep (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) B615047
theorem B755639 : Blo 334751 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B854023 : Blo 334751 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B723001 : Blo 334751 723001 := bstep (se 2 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 723001 = 542251) B542251
theorem B1706345 : Blo 334751 1706345 := bstep (se 2 (by rfl) ⟨639879, by rfl⟩ : syracuseStep 1706345 = 1279759) B1279759
theorem B723343 : Blo 334751 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B5507531 : Blo 334751 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B723419 : Blo 334751 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B756233 : Blo 334751 756233 := bstep (se 2 (by rfl) ⟨283587, by rfl⟩ : syracuseStep 756233 = 567175) B567175
theorem B854651 : Blo 334751 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B756575 : Blo 334751 756575 := bstep (se 1 (by rfl) ⟨567431, by rfl⟩ : syracuseStep 756575 = 1134863) B1134863
theorem B854945 : Blo 334751 854945 := bstep (se 2 (by rfl) ⟨320604, by rfl⟩ : syracuseStep 854945 = 641209) B641209
theorem B756755 : Blo 334751 756755 := bstep (se 1 (by rfl) ⟨567566, by rfl⟩ : syracuseStep 756755 = 1135133) B1135133
theorem B757097 : Blo 334751 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B1084873 : Blo 334751 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B6459101 : Blo 334751 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B1216417 : Blo 334751 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B4296635 : Blo 334751 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B757691 : Blo 334751 757691 := bstep (se 1 (by rfl) ⟨568268, by rfl⟩ : syracuseStep 757691 = 1136537) B1136537
theorem B757817 : Blo 334751 757817 := bstep (se 2 (by rfl) ⟨284181, by rfl⟩ : syracuseStep 757817 = 568363) B568363
theorem B758159 : Blo 334751 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B856615 : Blo 334751 856615 := bstep (se 1 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 856615 = 1284923) B1284923
theorem B1020539 : Blo 334751 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B758483 : Blo 334751 758483 := bstep (se 1 (by rfl) ⟨568862, by rfl⟩ : syracuseStep 758483 = 1137725) B1137725
theorem B856939 : Blo 334751 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B1315921 : Blo 334751 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B2561219 : Blo 334751 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B2168207 : Blo 334751 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B759419 : Blo 334751 759419 := bstep (se 1 (by rfl) ⟨569564, by rfl⟩ : syracuseStep 759419 = 1139129) B1139129
theorem B759545 : Blo 334751 759545 := bstep (se 2 (by rfl) ⟨284829, by rfl⟩ : syracuseStep 759545 = 569659) B569659
theorem B759815 : Blo 334751 759815 := bstep (se 1 (by rfl) ⟨569861, by rfl⟩ : syracuseStep 759815 = 1139723) B1139723
theorem B759887 : Blo 334751 759887 := bstep (se 1 (by rfl) ⟨569915, by rfl⟩ : syracuseStep 759887 = 1139831) B1139831
theorem B4299095 : Blo 334751 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B760283 : Blo 334751 760283 := bstep (se 1 (by rfl) ⟨570212, by rfl⟩ : syracuseStep 760283 = 1140425) B1140425
theorem B1087987 : Blo 334751 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B1907225 : Blo 334751 1907225 := bstep (se 2 (by rfl) ⟨715209, by rfl⟩ : syracuseStep 1907225 = 1430419) B1430419
theorem B1284893 : Blo 334751 1284893 := bstep (se 3 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 1284893 = 481835) B481835
theorem B334767 : Blo 334751 334767 := bstep (se 1 (by rfl) ⟨251075, by rfl⟩ : syracuseStep 334767 = 502151) B502151
theorem B957359 : Blo 334751 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B760751 : Blo 334751 760751 := bstep (se 1 (by rfl) ⟨570563, by rfl⟩ : syracuseStep 760751 = 1141127) B1141127
theorem B334791 : Blo 334751 334791 := bstep (se 1 (by rfl) ⟨251093, by rfl⟩ : syracuseStep 334791 = 502187) B502187
theorem B334811 : Blo 334751 334811 := bstep (se 1 (by rfl) ⟨251108, by rfl⟩ : syracuseStep 334811 = 502217) B502217
theorem B334887 : Blo 334751 334887 := bstep (se 1 (by rfl) ⟨251165, by rfl⟩ : syracuseStep 334887 = 502331) B502331
theorem B2169899 : Blo 334751 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B334927 : Blo 334751 334927 := bstep (se 1 (by rfl) ⟨251195, by rfl⟩ : syracuseStep 334927 = 502391) B502391
theorem B334943 : Blo 334751 334943 := bstep (se 1 (by rfl) ⟨251207, by rfl⟩ : syracuseStep 334943 = 502415) B502415
theorem B334971 : Blo 334751 334971 := bstep (se 1 (by rfl) ⟨251228, by rfl⟩ : syracuseStep 334971 = 502457) B502457
theorem B761003 : Blo 334751 761003 := bstep (se 1 (by rfl) ⟨570752, by rfl⟩ : syracuseStep 761003 = 1141505) B1141505
theorem B335023 : Blo 334751 335023 := bstep (se 1 (by rfl) ⟨251267, by rfl⟩ : syracuseStep 335023 = 502535) B502535
theorem B335047 : Blo 334751 335047 := bstep (se 1 (by rfl) ⟨251285, by rfl⟩ : syracuseStep 335047 = 502571) B502571
theorem B335067 : Blo 334751 335067 := bstep (se 1 (by rfl) ⟨251300, by rfl⟩ : syracuseStep 335067 = 502601) B502601
theorem B335143 : Blo 334751 335143 := bstep (se 1 (by rfl) ⟨251357, by rfl⟩ : syracuseStep 335143 = 502715) B502715
theorem B335183 : Blo 334751 335183 := bstep (se 1 (by rfl) ⟨251387, by rfl⟩ : syracuseStep 335183 = 502775) B502775
theorem B335199 : Blo 334751 335199 := bstep (se 1 (by rfl) ⟨251399, by rfl⟩ : syracuseStep 335199 = 502799) B502799
theorem B335227 : Blo 334751 335227 := bstep (se 1 (by rfl) ⟨251420, by rfl⟩ : syracuseStep 335227 = 502841) B502841
theorem B335279 : Blo 334751 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B9182645 : Blo 334751 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B335303 : Blo 334751 335303 := bstep (se 1 (by rfl) ⟨251477, by rfl⟩ : syracuseStep 335303 = 502955) B502955
theorem B1285577 : Blo 334751 1285577 := bstep (se 2 (by rfl) ⟨482091, by rfl⟩ : syracuseStep 1285577 = 964183) B964183
theorem B335323 : Blo 334751 335323 := bstep (se 1 (by rfl) ⟨251492, by rfl⟩ : syracuseStep 335323 = 502985) B502985
theorem B335399 : Blo 334751 335399 := bstep (se 1 (by rfl) ⟨251549, by rfl⟩ : syracuseStep 335399 = 503099) B503099
theorem B335439 : Blo 334751 335439 := bstep (se 1 (by rfl) ⟨251579, by rfl⟩ : syracuseStep 335439 = 503159) B503159
theorem B335455 : Blo 334751 335455 := bstep (se 1 (by rfl) ⟨251591, by rfl⟩ : syracuseStep 335455 = 503183) B503183
theorem B335483 : Blo 334751 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B564907 : Blo 334751 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B335535 : Blo 334751 335535 := bstep (se 1 (by rfl) ⟨251651, by rfl⟩ : syracuseStep 335535 = 503303) B503303
theorem B335559 : Blo 334751 335559 := bstep (se 1 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 335559 = 503339) B503339
theorem B761543 : Blo 334751 761543 := bstep (se 1 (by rfl) ⟨571157, by rfl⟩ : syracuseStep 761543 = 1142315) B1142315
theorem B335579 : Blo 334751 335579 := bstep (se 1 (by rfl) ⟨251684, by rfl⟩ : syracuseStep 335579 = 503369) B503369
theorem B7020269 : Blo 334751 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B3252001 : Blo 334751 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B335655 : Blo 334751 335655 := bstep (se 1 (by rfl) ⟨251741, by rfl⟩ : syracuseStep 335655 = 503483) B503483
theorem B335695 : Blo 334751 335695 := bstep (se 1 (by rfl) ⟨251771, by rfl⟩ : syracuseStep 335695 = 503543) B503543
theorem B335711 : Blo 334751 335711 := bstep (se 1 (by rfl) ⟨251783, by rfl⟩ : syracuseStep 335711 = 503567) B503567
theorem B335739 : Blo 334751 335739 := bstep (se 1 (by rfl) ⟨251804, by rfl⟩ : syracuseStep 335739 = 503609) B503609
theorem B335791 : Blo 334751 335791 := bstep (se 1 (by rfl) ⟨251843, by rfl⟩ : syracuseStep 335791 = 503687) B503687
theorem B1286063 : Blo 334751 1286063 := bstep (se 1 (by rfl) ⟨964547, by rfl⟩ : syracuseStep 1286063 = 1929095) B1929095
theorem B335815 : Blo 334751 335815 := bstep (se 1 (by rfl) ⟨251861, by rfl⟩ : syracuseStep 335815 = 503723) B503723
theorem B565211 : Blo 334751 565211 := bstep (se 1 (by rfl) ⟨423908, by rfl⟩ : syracuseStep 565211 = 847817) B847817
theorem B335835 : Blo 334751 335835 := bstep (se 1 (by rfl) ⟨251876, by rfl⟩ : syracuseStep 335835 = 503753) B503753
theorem B335911 : Blo 334751 335911 := bstep (se 1 (by rfl) ⟨251933, by rfl⟩ : syracuseStep 335911 = 503867) B503867
theorem B335951 : Blo 334751 335951 := bstep (se 1 (by rfl) ⟨251963, by rfl⟩ : syracuseStep 335951 = 503927) B503927
theorem B335967 : Blo 334751 335967 := bstep (se 1 (by rfl) ⟨251975, by rfl⟩ : syracuseStep 335967 = 503951) B503951
theorem B335995 : Blo 334751 335995 := bstep (se 1 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 335995 = 503993) B503993
theorem B336047 : Blo 334751 336047 := bstep (se 1 (by rfl) ⟨252035, by rfl⟩ : syracuseStep 336047 = 504071) B504071
theorem B565447 : Blo 334751 565447 := bstep (se 1 (by rfl) ⟨424085, by rfl⟩ : syracuseStep 565447 = 848171) B848171
theorem B336071 : Blo 334751 336071 := bstep (se 1 (by rfl) ⟨252053, by rfl⟩ : syracuseStep 336071 = 504107) B504107
theorem B336091 : Blo 334751 336091 := bstep (se 1 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 336091 = 504137) B504137
theorem B336167 : Blo 334751 336167 := bstep (se 1 (by rfl) ⟨252125, by rfl⟩ : syracuseStep 336167 = 504251) B504251
theorem B336207 : Blo 334751 336207 := bstep (se 1 (by rfl) ⟨252155, by rfl⟩ : syracuseStep 336207 = 504311) B504311
theorem B336223 : Blo 334751 336223 := bstep (se 1 (by rfl) ⟨252167, by rfl⟩ : syracuseStep 336223 = 504335) B504335
theorem B565609 : Blo 334751 565609 := bstep (se 2 (by rfl) ⟨212103, by rfl⟩ : syracuseStep 565609 = 424207) B424207
theorem B336251 : Blo 334751 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B336303 : Blo 334751 336303 := bstep (se 1 (by rfl) ⟨252227, by rfl⟩ : syracuseStep 336303 = 504455) B504455
theorem B336327 : Blo 334751 336327 := bstep (se 1 (by rfl) ⟨252245, by rfl⟩ : syracuseStep 336327 = 504491) B504491
theorem B336347 : Blo 334751 336347 := bstep (se 1 (by rfl) ⟨252260, by rfl⟩ : syracuseStep 336347 = 504521) B504521
theorem B336423 : Blo 334751 336423 := bstep (se 1 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 336423 = 504635) B504635
theorem B336463 : Blo 334751 336463 := bstep (se 1 (by rfl) ⟨252347, by rfl⟩ : syracuseStep 336463 = 504695) B504695
theorem B336479 : Blo 334751 336479 := bstep (se 1 (by rfl) ⟨252359, by rfl⟩ : syracuseStep 336479 = 504719) B504719
theorem B336507 : Blo 334751 336507 := bstep (se 1 (by rfl) ⟨252380, by rfl⟩ : syracuseStep 336507 = 504761) B504761
theorem B336559 : Blo 334751 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B1909433 : Blo 334751 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B1712825 : Blo 334751 1712825 := bstep (se 2 (by rfl) ⟨642309, by rfl⟩ : syracuseStep 1712825 = 1284619) B1284619
theorem B336583 : Blo 334751 336583 := bstep (se 1 (by rfl) ⟨252437, by rfl⟩ : syracuseStep 336583 = 504875) B504875
theorem B336603 : Blo 334751 336603 := bstep (se 1 (by rfl) ⟨252452, by rfl⟩ : syracuseStep 336603 = 504905) B504905
theorem B336679 : Blo 334751 336679 := bstep (se 1 (by rfl) ⟨252509, by rfl⟩ : syracuseStep 336679 = 505019) B505019
theorem B336719 : Blo 334751 336719 := bstep (se 1 (by rfl) ⟨252539, by rfl⟩ : syracuseStep 336719 = 505079) B505079
theorem B336735 : Blo 334751 336735 := bstep (se 1 (by rfl) ⟨252551, by rfl⟩ : syracuseStep 336735 = 505103) B505103
theorem B336763 : Blo 334751 336763 := bstep (se 1 (by rfl) ⟨252572, by rfl⟩ : syracuseStep 336763 = 505145) B505145
theorem B336815 : Blo 334751 336815 := bstep (se 1 (by rfl) ⟨252611, by rfl⟩ : syracuseStep 336815 = 505223) B505223
theorem B566203 : Blo 334751 566203 := bstep (se 1 (by rfl) ⟨424652, by rfl⟩ : syracuseStep 566203 = 849305) B849305
theorem B336839 : Blo 334751 336839 := bstep (se 1 (by rfl) ⟨252629, by rfl⟩ : syracuseStep 336839 = 505259) B505259
theorem B336859 : Blo 334751 336859 := bstep (se 1 (by rfl) ⟨252644, by rfl⟩ : syracuseStep 336859 = 505289) B505289
theorem B566311 : Blo 334751 566311 := bstep (se 1 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 566311 = 849467) B849467
theorem B336935 : Blo 334751 336935 := bstep (se 1 (by rfl) ⟨252701, by rfl⟩ : syracuseStep 336935 = 505403) B505403
theorem B336975 : Blo 334751 336975 := bstep (se 1 (by rfl) ⟨252731, by rfl⟩ : syracuseStep 336975 = 505463) B505463
theorem B336991 : Blo 334751 336991 := bstep (se 1 (by rfl) ⟨252743, by rfl⟩ : syracuseStep 336991 = 505487) B505487
theorem B337019 : Blo 334751 337019 := bstep (se 1 (by rfl) ⟨252764, by rfl⟩ : syracuseStep 337019 = 505529) B505529
theorem B337071 : Blo 334751 337071 := bstep (se 1 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 337071 = 505607) B505607
theorem B337095 : Blo 334751 337095 := bstep (se 1 (by rfl) ⟨252821, by rfl⟩ : syracuseStep 337095 = 505643) B505643
theorem B337115 : Blo 334751 337115 := bstep (se 1 (by rfl) ⟨252836, by rfl⟩ : syracuseStep 337115 = 505673) B505673
theorem B337191 : Blo 334751 337191 := bstep (se 1 (by rfl) ⟨252893, by rfl⟩ : syracuseStep 337191 = 505787) B505787
theorem B337231 : Blo 334751 337231 := bstep (se 1 (by rfl) ⟨252923, by rfl⟩ : syracuseStep 337231 = 505847) B505847
theorem B337247 : Blo 334751 337247 := bstep (se 1 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 337247 = 505871) B505871
theorem B566635 : Blo 334751 566635 := bstep (se 1 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 566635 = 849953) B849953
theorem B337275 : Blo 334751 337275 := bstep (se 1 (by rfl) ⟨252956, by rfl⟩ : syracuseStep 337275 = 505913) B505913
theorem B1910141 : Blo 334751 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B337327 : Blo 334751 337327 := bstep (se 1 (by rfl) ⟨252995, by rfl⟩ : syracuseStep 337327 = 505991) B505991
theorem B337351 : Blo 334751 337351 := bstep (se 1 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 337351 = 506027) B506027
theorem B337371 : Blo 334751 337371 := bstep (se 1 (by rfl) ⟨253028, by rfl⟩ : syracuseStep 337371 = 506057) B506057
theorem B5481989 : Blo 334751 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B960025 : Blo 334751 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B337447 : Blo 334751 337447 := bstep (se 1 (by rfl) ⟨253085, by rfl⟩ : syracuseStep 337447 = 506171) B506171
theorem B337487 : Blo 334751 337487 := bstep (se 1 (by rfl) ⟨253115, by rfl⟩ : syracuseStep 337487 = 506231) B506231
theorem B337503 : Blo 334751 337503 := bstep (se 1 (by rfl) ⟨253127, by rfl⟩ : syracuseStep 337503 = 506255) B506255
theorem B337531 : Blo 334751 337531 := bstep (se 1 (by rfl) ⟨253148, by rfl⟩ : syracuseStep 337531 = 506297) B506297
theorem B337583 : Blo 334751 337583 := bstep (se 1 (by rfl) ⟨253187, by rfl⟩ : syracuseStep 337583 = 506375) B506375
theorem B337607 : Blo 334751 337607 := bstep (se 1 (by rfl) ⟨253205, by rfl⟩ : syracuseStep 337607 = 506411) B506411
theorem B337627 : Blo 334751 337627 := bstep (se 1 (by rfl) ⟨253220, by rfl⟩ : syracuseStep 337627 = 506441) B506441
theorem B337703 : Blo 334751 337703 := bstep (se 1 (by rfl) ⟨253277, by rfl⟩ : syracuseStep 337703 = 506555) B506555
theorem B337743 : Blo 334751 337743 := bstep (se 1 (by rfl) ⟨253307, by rfl⟩ : syracuseStep 337743 = 506615) B506615
theorem B337759 : Blo 334751 337759 := bstep (se 1 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 337759 = 506639) B506639
theorem B337787 : Blo 334751 337787 := bstep (se 1 (by rfl) ⟨253340, by rfl⟩ : syracuseStep 337787 = 506681) B506681
theorem B337839 : Blo 334751 337839 := bstep (se 1 (by rfl) ⟨253379, by rfl⟩ : syracuseStep 337839 = 506759) B506759
theorem B1451963 : Blo 334751 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B337863 : Blo 334751 337863 := bstep (se 1 (by rfl) ⟨253397, by rfl⟩ : syracuseStep 337863 = 506795) B506795
theorem B337883 : Blo 334751 337883 := bstep (se 1 (by rfl) ⟨253412, by rfl⟩ : syracuseStep 337883 = 506825) B506825
theorem B337959 : Blo 334751 337959 := bstep (se 1 (by rfl) ⟨253469, by rfl⟩ : syracuseStep 337959 = 506939) B506939
theorem B337999 : Blo 334751 337999 := bstep (se 1 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 337999 = 506999) B506999
theorem B338015 : Blo 334751 338015 := bstep (se 1 (by rfl) ⟨253511, by rfl⟩ : syracuseStep 338015 = 507023) B507023
theorem B403579 : Blo 334751 403579 := bstep (se 1 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 403579 = 605369) B605369
theorem B338043 : Blo 334751 338043 := bstep (se 1 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 338043 = 507065) B507065
theorem B6924419 : Blo 334751 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B338095 : Blo 334751 338095 := bstep (se 1 (by rfl) ⟨253571, by rfl⟩ : syracuseStep 338095 = 507143) B507143
theorem B17410229 : Blo 334751 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B338119 : Blo 334751 338119 := bstep (se 1 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 338119 = 507179) B507179
theorem B338139 : Blo 334751 338139 := bstep (se 1 (by rfl) ⟨253604, by rfl⟩ : syracuseStep 338139 = 507209) B507209
theorem B6564077 : Blo 334751 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B338215 : Blo 334751 338215 := bstep (se 1 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 338215 = 507323) B507323
theorem B338255 : Blo 334751 338255 := bstep (se 1 (by rfl) ⟨253691, by rfl⟩ : syracuseStep 338255 = 507383) B507383
theorem B338271 : Blo 334751 338271 := bstep (se 1 (by rfl) ⟨253703, by rfl⟩ : syracuseStep 338271 = 507407) B507407
theorem B338299 : Blo 334751 338299 := bstep (se 1 (by rfl) ⟨253724, by rfl⟩ : syracuseStep 338299 = 507449) B507449
theorem B567695 : Blo 334751 567695 := bstep (se 1 (by rfl) ⟨425771, by rfl⟩ : syracuseStep 567695 = 851543) B851543
theorem B338351 : Blo 334751 338351 := bstep (se 1 (by rfl) ⟨253763, by rfl⟩ : syracuseStep 338351 = 507527) B507527
theorem B502199 : Blo 334751 502199 := bstep (se 1 (by rfl) ⟨376649, by rfl⟩ : syracuseStep 502199 = 753299) B753299
theorem B338375 : Blo 334751 338375 := bstep (se 1 (by rfl) ⟨253781, by rfl⟩ : syracuseStep 338375 = 507563) B507563
theorem B502235 : Blo 334751 502235 := bstep (se 1 (by rfl) ⟨376676, by rfl⟩ : syracuseStep 502235 = 753353) B753353
theorem B338395 : Blo 334751 338395 := bstep (se 1 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 338395 = 507593) B507593
theorem B338471 : Blo 334751 338471 := bstep (se 1 (by rfl) ⟨253853, by rfl⟩ : syracuseStep 338471 = 507707) B507707
theorem B338511 : Blo 334751 338511 := bstep (se 1 (by rfl) ⟨253883, by rfl⟩ : syracuseStep 338511 = 507767) B507767
theorem B338527 : Blo 334751 338527 := bstep (se 1 (by rfl) ⟨253895, by rfl⟩ : syracuseStep 338527 = 507791) B507791
theorem B567931 : Blo 334751 567931 := bstep (se 1 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 567931 = 851897) B851897
theorem B338555 : Blo 334751 338555 := bstep (se 1 (by rfl) ⟨253916, by rfl⟩ : syracuseStep 338555 = 507833) B507833
theorem B338607 : Blo 334751 338607 := bstep (se 1 (by rfl) ⟨253955, by rfl⟩ : syracuseStep 338607 = 507911) B507911
theorem B338631 : Blo 334751 338631 := bstep (se 1 (by rfl) ⟨253973, by rfl⟩ : syracuseStep 338631 = 507947) B507947
theorem B338651 : Blo 334751 338651 := bstep (se 1 (by rfl) ⟨253988, by rfl⟩ : syracuseStep 338651 = 507977) B507977
theorem B338727 : Blo 334751 338727 := bstep (se 1 (by rfl) ⟨254045, by rfl⟩ : syracuseStep 338727 = 508091) B508091
theorem B502703 : Blo 334751 502703 := bstep (se 1 (by rfl) ⟨377027, by rfl⟩ : syracuseStep 502703 = 754055) B754055
theorem B502793 : Blo 334751 502793 := bstep (se 2 (by rfl) ⟨188547, by rfl⟩ : syracuseStep 502793 = 377095) B377095
theorem B502823 : Blo 334751 502823 := bstep (se 1 (by rfl) ⟨377117, by rfl⟩ : syracuseStep 502823 = 754235) B754235
theorem B502907 : Blo 334751 502907 := bstep (se 1 (by rfl) ⟨377180, by rfl⟩ : syracuseStep 502907 = 754361) B754361
theorem B503033 : Blo 334751 503033 := bstep (se 2 (by rfl) ⟨188637, by rfl⟩ : syracuseStep 503033 = 377275) B377275
theorem B503135 : Blo 334751 503135 := bstep (se 1 (by rfl) ⟨377351, by rfl⟩ : syracuseStep 503135 = 754703) B754703
theorem B503147 : Blo 334751 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B404843 : Blo 334751 404843 := bstep (se 1 (by rfl) ⟨303632, by rfl⟩ : syracuseStep 404843 = 607265) B607265
theorem B568795 : Blo 334751 568795 := bstep (se 1 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 568795 = 853193) B853193
theorem B503375 : Blo 334751 503375 := bstep (se 1 (by rfl) ⟨377531, by rfl⟩ : syracuseStep 503375 = 755063) B755063
theorem B2436695 : Blo 334751 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B6565495 : Blo 334751 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B1060499 : Blo 334751 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B503495 : Blo 334751 503495 := bstep (se 1 (by rfl) ⟨377621, by rfl⟩ : syracuseStep 503495 = 755243) B755243
theorem B536311 : Blo 334751 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B503657 : Blo 334751 503657 := bstep (se 2 (by rfl) ⟨188871, by rfl⟩ : syracuseStep 503657 = 377743) B377743
theorem B503735 : Blo 334751 503735 := bstep (se 1 (by rfl) ⟨377801, by rfl⟩ : syracuseStep 503735 = 755603) B755603
theorem B503771 : Blo 334751 503771 := bstep (se 1 (by rfl) ⟨377828, by rfl⟩ : syracuseStep 503771 = 755657) B755657
theorem B569423 : Blo 334751 569423 := bstep (se 1 (by rfl) ⟨427067, by rfl⟩ : syracuseStep 569423 = 854135) B854135
theorem B864427 : Blo 334751 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B3649853 : Blo 334751 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B2568509 : Blo 334751 2568509 := bstep (se 3 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 2568509 = 963191) B963191
theorem B962941 : Blo 334751 962941 := bstep (se 3 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 962941 = 361103) B361103
theorem B504239 : Blo 334751 504239 := bstep (se 1 (by rfl) ⟨378179, by rfl⟩ : syracuseStep 504239 = 756359) B756359
theorem B504329 : Blo 334751 504329 := bstep (se 2 (by rfl) ⟨189123, by rfl⟩ : syracuseStep 504329 = 378247) B378247
theorem B504359 : Blo 334751 504359 := bstep (se 1 (by rfl) ⟨378269, by rfl⟩ : syracuseStep 504359 = 756539) B756539
theorem B504443 : Blo 334751 504443 := bstep (se 1 (by rfl) ⟨378332, by rfl⟩ : syracuseStep 504443 = 756665) B756665
theorem B504569 : Blo 334751 504569 := bstep (se 2 (by rfl) ⟨189213, by rfl⟩ : syracuseStep 504569 = 378427) B378427
theorem B9679661 : Blo 334751 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B504671 : Blo 334751 504671 := bstep (se 1 (by rfl) ⟨378503, by rfl⟩ : syracuseStep 504671 = 757007) B757007
theorem B504683 : Blo 334751 504683 := bstep (se 1 (by rfl) ⟨378512, by rfl⟩ : syracuseStep 504683 = 757025) B757025
theorem B2470763 : Blo 334751 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B570287 : Blo 334751 570287 := bstep (se 1 (by rfl) ⟨427715, by rfl⟩ : syracuseStep 570287 = 855431) B855431
theorem B1946551 : Blo 334751 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B504911 : Blo 334751 504911 := bstep (se 1 (by rfl) ⟨378683, by rfl⟩ : syracuseStep 504911 = 757367) B757367
theorem B505031 : Blo 334751 505031 := bstep (se 1 (by rfl) ⟨378773, by rfl⟩ : syracuseStep 505031 = 757547) B757547
theorem B570719 : Blo 334751 570719 := bstep (se 1 (by rfl) ⟨428039, by rfl⟩ : syracuseStep 570719 = 856079) B856079
theorem B636265 : Blo 334751 636265 := bstep (se 2 (by rfl) ⟨238599, by rfl⟩ : syracuseStep 636265 = 477199) B477199
theorem B505193 : Blo 334751 505193 := bstep (se 2 (by rfl) ⟨189447, by rfl⟩ : syracuseStep 505193 = 378895) B378895
theorem B505271 : Blo 334751 505271 := bstep (se 1 (by rfl) ⟨378953, by rfl⟩ : syracuseStep 505271 = 757907) B757907
theorem B505307 : Blo 334751 505307 := bstep (se 1 (by rfl) ⟨378980, by rfl⟩ : syracuseStep 505307 = 757961) B757961
theorem B538169 : Blo 334751 538169 := bstep (se 2 (by rfl) ⟨201813, by rfl⟩ : syracuseStep 538169 = 403627) B403627
theorem B6895201 : Blo 334751 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B1914515 : Blo 334751 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B15513281 : Blo 334751 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B2471639 : Blo 334751 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B571279 : Blo 334751 571279 := bstep (se 1 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 571279 = 856919) B856919
theorem B505775 : Blo 334751 505775 := bstep (se 1 (by rfl) ⟨379331, by rfl⟩ : syracuseStep 505775 = 758663) B758663
theorem B3880909 : Blo 334751 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B505865 : Blo 334751 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B538663 : Blo 334751 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B505895 : Blo 334751 505895 := bstep (se 1 (by rfl) ⟨379421, by rfl⟩ : syracuseStep 505895 = 758843) B758843
theorem B505979 : Blo 334751 505979 := bstep (se 1 (by rfl) ⟨379484, by rfl⟩ : syracuseStep 505979 = 758969) B758969
theorem B637139 : Blo 334751 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B506105 : Blo 334751 506105 := bstep (se 2 (by rfl) ⟨189789, by rfl⟩ : syracuseStep 506105 = 379579) B379579
theorem B506207 : Blo 334751 506207 := bstep (se 1 (by rfl) ⟨379655, by rfl⟩ : syracuseStep 506207 = 759311) B759311
theorem B506219 : Blo 334751 506219 := bstep (se 1 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 506219 = 759329) B759329
theorem B1915265 : Blo 334751 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B4340101 : Blo 334751 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B506447 : Blo 334751 506447 := bstep (se 1 (by rfl) ⟨379835, by rfl⟩ : syracuseStep 506447 = 759671) B759671
theorem B539335 : Blo 334751 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B506567 : Blo 334751 506567 := bstep (se 1 (by rfl) ⟨379925, by rfl⟩ : syracuseStep 506567 = 759851) B759851
theorem B637769 : Blo 334751 637769 := bstep (se 2 (by rfl) ⟨239163, by rfl⟩ : syracuseStep 637769 = 478327) B478327
theorem B1915721 : Blo 334751 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B506729 : Blo 334751 506729 := bstep (se 2 (by rfl) ⟨190023, by rfl⟩ : syracuseStep 506729 = 380047) B380047
theorem B768943 : Blo 334751 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B506807 : Blo 334751 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B506843 : Blo 334751 506843 := bstep (se 1 (by rfl) ⟨380132, by rfl⟩ : syracuseStep 506843 = 760265) B760265
theorem B5848037 : Blo 334751 5848037 := bstep (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) B1096507
theorem B2440385 : Blo 334751 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B867689 : Blo 334751 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B540047 : Blo 334751 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B409007 : Blo 334751 409007 := bstep (se 1 (by rfl) ⟨306755, by rfl⟩ : syracuseStep 409007 = 613511) B613511
theorem B507311 : Blo 334751 507311 := bstep (se 1 (by rfl) ⟨380483, by rfl⟩ : syracuseStep 507311 = 760967) B760967
theorem B507401 : Blo 334751 507401 := bstep (se 2 (by rfl) ⟨190275, by rfl⟩ : syracuseStep 507401 = 380551) B380551
theorem B507431 : Blo 334751 507431 := bstep (se 1 (by rfl) ⟨380573, by rfl⟩ : syracuseStep 507431 = 761147) B761147
theorem B638543 : Blo 334751 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B507515 : Blo 334751 507515 := bstep (se 1 (by rfl) ⟨380636, by rfl⟩ : syracuseStep 507515 = 761273) B761273
theorem B507641 : Blo 334751 507641 := bstep (se 2 (by rfl) ⟨190365, by rfl⟩ : syracuseStep 507641 = 380731) B380731
theorem B2146115 : Blo 334751 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B1949507 : Blo 334751 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B507743 : Blo 334751 507743 := bstep (se 1 (by rfl) ⟨380807, by rfl⟩ : syracuseStep 507743 = 761615) B761615
theorem B507755 : Blo 334751 507755 := bstep (se 1 (by rfl) ⟨380816, by rfl⟩ : syracuseStep 507755 = 761633) B761633
theorem B507983 : Blo 334751 507983 := bstep (se 1 (by rfl) ⟨380987, by rfl⟩ : syracuseStep 507983 = 761975) B761975
theorem B508103 : Blo 334751 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B606457 : Blo 334751 606457 := bstep (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) B454843
theorem B1130813 : Blo 334751 1130813 := bstep (se 3 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 1130813 = 424055) B424055
theorem B377383 : Blo 334751 377383 := bstep (se 1 (by rfl) ⟨283037, by rfl⟩ : syracuseStep 377383 = 566075) B566075
theorem B771079 : Blo 334751 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B3327095 : Blo 334751 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1131677 : Blo 334751 1131677 := bstep (se 3 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 1131677 = 424379) B424379
theorem B640199 : Blo 334751 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B3229091 : Blo 334751 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B607675 : Blo 334751 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B2868797 : Blo 334751 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1132217 : Blo 334751 1132217 := bstep (se 2 (by rfl) ⟨424581, by rfl⟩ : syracuseStep 1132217 = 849163) B849163
theorem B640723 : Blo 334751 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B8308439 : Blo 334751 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B640943 : Blo 334751 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B379003 : Blo 334751 379003 := bstep (se 1 (by rfl) ⟨284252, by rfl⟩ : syracuseStep 379003 = 568505) B568505
theorem B1132811 : Blo 334751 1132811 := bstep (se 1 (by rfl) ⟨849608, by rfl⟩ : syracuseStep 1132811 = 1699217) B1699217
theorem B641353 : Blo 334751 641353 := bstep (se 2 (by rfl) ⟨240507, by rfl⟩ : syracuseStep 641353 = 481015) B481015
theorem B510391 : Blo 334751 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B1133081 : Blo 334751 1133081 := bstep (se 2 (by rfl) ⟨424905, by rfl⟩ : syracuseStep 1133081 = 849811) B849811
theorem B379471 : Blo 334751 379471 := bstep (se 1 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 379471 = 569207) B569207
theorem B6933127 : Blo 334751 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B2149037 : Blo 334751 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B2542265 : Blo 334751 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B609131 : Blo 334751 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B379867 : Blo 334751 379867 := bstep (se 1 (by rfl) ⟨284900, by rfl⟩ : syracuseStep 379867 = 569801) B569801
theorem B609319 : Blo 334751 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B1756313 : Blo 334751 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B5491907 : Blo 334751 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B380335 : Blo 334751 380335 := bstep (se 1 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 380335 = 570503) B570503
theorem B2543237 : Blo 334751 2543237 := bstep (se 4 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 2543237 = 476857) B476857
theorem B1134215 : Blo 334751 1134215 := bstep (se 1 (by rfl) ⟨850661, by rfl⟩ : syracuseStep 1134215 = 1701323) B1701323
theorem B1134269 : Blo 334751 1134269 := bstep (se 3 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 1134269 = 425351) B425351
theorem B478919 : Blo 334751 478919 := bstep (se 1 (by rfl) ⟨359189, by rfl⟩ : syracuseStep 478919 = 718379) B718379
theorem B806611 : Blo 334751 806611 := bstep (se 1 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 806611 = 1209917) B1209917
theorem B1134431 : Blo 334751 1134431 := bstep (se 1 (by rfl) ⟨850823, by rfl⟩ : syracuseStep 1134431 = 1701647) B1701647
theorem B380767 : Blo 334751 380767 := bstep (se 1 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 380767 = 571151) B571151
theorem B3559355 : Blo 334751 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B1134593 : Blo 334751 1134593 := bstep (se 2 (by rfl) ⟨425472, by rfl⟩ : syracuseStep 1134593 = 850945) B850945
theorem B4837643 : Blo 334751 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B807311 : Blo 334751 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B4313857 : Blo 334751 4313857 := bstep (se 2 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 4313857 = 3235393) B3235393
theorem B1135403 : Blo 334751 1135403 := bstep (se 1 (by rfl) ⟨851552, by rfl⟩ : syracuseStep 1135403 = 1703105) B1703105
theorem B1135673 : Blo 334751 1135673 := bstep (se 2 (by rfl) ⟨425877, by rfl⟩ : syracuseStep 1135673 = 851755) B851755
theorem B1135997 : Blo 334751 1135997 := bstep (se 3 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 1135997 = 425999) B425999
theorem B4904339 : Blo 334751 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B546383 : Blo 334751 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B1136267 : Blo 334751 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B1627847 : Blo 334751 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B513967 : Blo 334751 513967 := bstep (se 1 (by rfl) ⟨385475, by rfl⟩ : syracuseStep 513967 = 770951) B770951
theorem B481243 : Blo 334751 481243 := bstep (se 1 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 481243 = 721865) B721865
theorem B2545667 : Blo 334751 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B4315193 : Blo 334751 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B3889457 : Blo 334751 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B8673641 : Blo 334751 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B481801 : Blo 334751 481801 := bstep (se 2 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 481801 = 361351) B361351
theorem B1137185 : Blo 334751 1137185 := bstep (se 2 (by rfl) ⟨426444, by rfl⟩ : syracuseStep 1137185 = 852889) B852889
theorem B1137401 : Blo 334751 1137401 := bstep (se 2 (by rfl) ⟨426525, by rfl⟩ : syracuseStep 1137401 = 853051) B853051
theorem B1432349 : Blo 334751 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B1137671 : Blo 334751 1137671 := bstep (se 1 (by rfl) ⟨853253, by rfl⟩ : syracuseStep 1137671 = 1706507) B1706507
theorem B6151247 : Blo 334751 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1137779 : Blo 334751 1137779 := bstep (se 1 (by rfl) ⟨853334, by rfl⟩ : syracuseStep 1137779 = 1706669) B1706669
theorem B974071 : Blo 334751 974071 := bstep (se 1 (by rfl) ⟨730553, by rfl⟩ : syracuseStep 974071 = 1461107) B1461107
theorem B5725565 : Blo 334751 5725565 := bstep (se 3 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 5725565 = 2147087) B2147087
theorem B1138049 : Blo 334751 1138049 := bstep (se 2 (by rfl) ⟨426768, by rfl⟩ : syracuseStep 1138049 = 853537) B853537
theorem B1072673 : Blo 334751 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1695329 : Blo 334751 1695329 := bstep (se 2 (by rfl) ⟨635748, by rfl⟩ : syracuseStep 1695329 = 1271497) B1271497
theorem B2416225 : Blo 334751 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1073083 : Blo 334751 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1138859 : Blo 334751 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B39739747 : Blo 334751 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B1073533 : Blo 334751 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B2548097 : Blo 334751 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B647687 : Blo 334751 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B909947 : Blo 334751 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B1139399 : Blo 334751 1139399 := bstep (se 1 (by rfl) ⟨854549, by rfl⟩ : syracuseStep 1139399 = 1709099) B1709099
theorem B680879 : Blo 334751 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B1696787 : Blo 334751 1696787 := bstep (se 1 (by rfl) ⟨1272590, by rfl⟩ : syracuseStep 1696787 = 2545181) B2545181
theorem B2909303 : Blo 334751 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B5432741 : Blo 334751 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B812531 : Blo 334751 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1140263 : Blo 334751 1140263 := bstep (se 1 (by rfl) ⟨855197, by rfl⟩ : syracuseStep 1140263 = 1710395) B1710395
theorem B1140371 : Blo 334751 1140371 := bstep (se 1 (by rfl) ⟨855278, by rfl⟩ : syracuseStep 1140371 = 1710557) B1710557
theorem B1140587 : Blo 334751 1140587 := bstep (se 1 (by rfl) ⟨855440, by rfl⟩ : syracuseStep 1140587 = 1710881) B1710881
theorem B1140641 : Blo 334751 1140641 := bstep (se 2 (by rfl) ⟨427740, by rfl⟩ : syracuseStep 1140641 = 855481) B855481
theorem B3958721 : Blo 334751 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1141235 : Blo 334751 1141235 := bstep (se 1 (by rfl) ⟨855926, by rfl⟩ : syracuseStep 1141235 = 1711853) B1711853
theorem B911969 : Blo 334751 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B1272455 : Blo 334751 1272455 := bstep (se 1 (by rfl) ⟨954341, by rfl⟩ : syracuseStep 1272455 = 1908683) B1908683
theorem B1370771 : Blo 334751 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B1141775 : Blo 334751 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B1928387 : Blo 334751 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B453983 : Blo 334751 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B1076723 : Blo 334751 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1273441 : Blo 334751 1273441 := bstep (se 2 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 1273441 = 955081) B955081
theorem B1142369 : Blo 334751 1142369 := bstep (se 2 (by rfl) ⟨428388, by rfl⟩ : syracuseStep 1142369 = 856777) B856777
theorem B1928843 : Blo 334751 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1732241 : Blo 334751 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B4091681 : Blo 334751 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B1699703 : Blo 334751 1699703 := bstep (se 1 (by rfl) ⟨1274777, by rfl⟩ : syracuseStep 1699703 = 2549555) B2549555
theorem B12283811 : Blo 334751 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B683959 : Blo 334751 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1273913 : Blo 334751 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B1077799 : Blo 334751 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B2159389 : Blo 334751 2159389 := bstep (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) B809771
theorem B1274899 : Blo 334751 1274899 := bstep (se 1 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 1274899 = 1912349) B1912349
theorem B849143 : Blo 334751 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B816527 : Blo 334751 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B1734061 : Blo 334751 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B2618825 : Blo 334751 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2881169 : Blo 334751 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B423787 : Blo 334751 423787 := bstep (se 1 (by rfl) ⟨317840, by rfl⟩ : syracuseStep 423787 = 635681) B635681
theorem B6944717 : Blo 334751 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B686441 : Blo 334751 686441 := bstep (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) B514831
theorem B4094509 : Blo 334751 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B850571 : Blo 334751 850571 := bstep (se 1 (by rfl) ⟨637928, by rfl⟩ : syracuseStep 850571 = 1275857) B1275857
theorem B1276631 : Blo 334751 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B850783 : Blo 334751 850783 := bstep (se 1 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 850783 = 1276175) B1276175
theorem B425083 : Blo 334751 425083 := bstep (se 1 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 425083 = 637625) B637625
theorem B55934165 : Blo 334751 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B6552845 : Blo 334751 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B753191 : Blo 334751 753191 := bstep (se 1 (by rfl) ⟨564893, by rfl⟩ : syracuseStep 753191 = 1129787) B1129787
theorem B851705 : Blo 334751 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B753515 : Blo 334751 753515 := bstep (se 1 (by rfl) ⟨565136, by rfl⟩ : syracuseStep 753515 = 1130273) B1130273
theorem B1277815 : Blo 334751 1277815 := bstep (se 1 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 1277815 = 1916723) B1916723
theorem B753569 : Blo 334751 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B753875 : Blo 334751 753875 := bstep (se 1 (by rfl) ⟨565406, by rfl⟩ : syracuseStep 753875 = 1130813) B1130813
theorem B753929 : Blo 334751 753929 := bstep (se 2 (by rfl) ⟨282723, by rfl⟩ : syracuseStep 753929 = 565447) B565447
theorem B52986329 : Blo 334751 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B754145 : Blo 334751 754145 := bstep (se 2 (by rfl) ⟨282804, by rfl⟩ : syracuseStep 754145 = 565609) B565609
theorem B721403 : Blo 334751 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B852727 : Blo 334751 852727 := bstep (se 1 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 852727 = 1279091) B1279091
theorem B754451 : Blo 334751 754451 := bstep (se 1 (by rfl) ⟨565838, by rfl⟩ : syracuseStep 754451 = 1131677) B1131677
theorem B426799 : Blo 334751 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B5833619 : Blo 334751 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B853031 : Blo 334751 853031 := bstep (se 1 (by rfl) ⟨639773, by rfl⟩ : syracuseStep 853031 = 1279547) B1279547
theorem B1442873 : Blo 334751 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B1705049 : Blo 334751 1705049 := bstep (se 2 (by rfl) ⟨639393, by rfl⟩ : syracuseStep 1705049 = 1278787) B1278787
theorem B754811 : Blo 334751 754811 := bstep (se 1 (by rfl) ⟨566108, by rfl⟩ : syracuseStep 754811 = 1132217) B1132217
theorem B5538959 : Blo 334751 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B754937 : Blo 334751 754937 := bstep (se 2 (by rfl) ⟨283101, by rfl⟩ : syracuseStep 754937 = 566203) B566203
theorem B427295 : Blo 334751 427295 := bstep (se 1 (by rfl) ⟨320471, by rfl⟩ : syracuseStep 427295 = 640943) B640943
theorem B755081 : Blo 334751 755081 := bstep (se 2 (by rfl) ⟨283155, by rfl⟩ : syracuseStep 755081 = 566311) B566311
theorem B755207 : Blo 334751 755207 := bstep (se 1 (by rfl) ⟨566405, by rfl⟩ : syracuseStep 755207 = 1132811) B1132811
theorem B3671687 : Blo 334751 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B755387 : Blo 334751 755387 := bstep (se 1 (by rfl) ⟨566540, by rfl⟩ : syracuseStep 755387 = 1133081) B1133081
theorem B755513 : Blo 334751 755513 := bstep (se 2 (by rfl) ⟨283317, by rfl⟩ : syracuseStep 755513 = 566635) B566635
theorem B1280033 : Blo 334751 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B854297 : Blo 334751 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B2722085 : Blo 334751 2722085 := bstep (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) B510391
theorem B756143 : Blo 334751 756143 := bstep (se 1 (by rfl) ⟨567107, by rfl⟩ : syracuseStep 756143 = 1134215) B1134215
theorem B756179 : Blo 334751 756179 := bstep (se 1 (by rfl) ⟨567134, by rfl⟩ : syracuseStep 756179 = 1134269) B1134269
theorem B756287 : Blo 334751 756287 := bstep (se 1 (by rfl) ⟨567215, by rfl⟩ : syracuseStep 756287 = 1134431) B1134431
theorem B756395 : Blo 334751 756395 := bstep (se 1 (by rfl) ⟨567296, by rfl⟩ : syracuseStep 756395 = 1134593) B1134593
theorem B855137 : Blo 334751 855137 := bstep (se 2 (by rfl) ⟨320676, by rfl⟩ : syracuseStep 855137 = 641353) B641353
theorem B756935 : Blo 334751 756935 := bstep (se 1 (by rfl) ⟨567701, by rfl⟩ : syracuseStep 756935 = 1135403) B1135403
theorem B757115 : Blo 334751 757115 := bstep (se 1 (by rfl) ⟨567836, by rfl⟩ : syracuseStep 757115 = 1135673) B1135673
theorem B1707479 : Blo 334751 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B757241 : Blo 334751 757241 := bstep (se 2 (by rfl) ⟨283965, by rfl⟩ : syracuseStep 757241 = 567931) B567931
theorem B9244169 : Blo 334751 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B757331 : Blo 334751 757331 := bstep (se 1 (by rfl) ⟨567998, by rfl⟩ : syracuseStep 757331 = 1135997) B1135997
theorem B1445471 : Blo 334751 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B757511 : Blo 334751 757511 := bstep (se 1 (by rfl) ⟨568133, by rfl⟩ : syracuseStep 757511 = 1136267) B1136267
theorem B1085231 : Blo 334751 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B6983533 : Blo 334751 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B2166749 : Blo 334751 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B2592971 : Blo 334751 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B758123 : Blo 334751 758123 := bstep (se 1 (by rfl) ⟨568592, by rfl⟩ : syracuseStep 758123 = 1137185) B1137185
theorem B758267 : Blo 334751 758267 := bstep (se 1 (by rfl) ⟨568700, by rfl⟩ : syracuseStep 758267 = 1137401) B1137401
theorem B954899 : Blo 334751 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B856595 : Blo 334751 856595 := bstep (se 1 (by rfl) ⟨642446, by rfl⟩ : syracuseStep 856595 = 1284893) B1284893
theorem B1446497 : Blo 334751 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B758393 : Blo 334751 758393 := bstep (se 2 (by rfl) ⟨284397, by rfl⟩ : syracuseStep 758393 = 568795) B568795
theorem B758447 : Blo 334751 758447 := bstep (se 1 (by rfl) ⟨568835, by rfl⟩ : syracuseStep 758447 = 1137671) B1137671
theorem B1446599 : Blo 334751 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B4100831 : Blo 334751 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B758519 : Blo 334751 758519 := bstep (se 1 (by rfl) ⟨568889, by rfl⟩ : syracuseStep 758519 = 1137779) B1137779
theorem B8753993 : Blo 334751 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B758699 : Blo 334751 758699 := bstep (se 1 (by rfl) ⟨569024, by rfl⟩ : syracuseStep 758699 = 1138049) B1138049
theorem B857051 : Blo 334751 857051 := bstep (se 1 (by rfl) ⟨642788, by rfl⟩ : syracuseStep 857051 = 1285577) B1285577
theorem B3871901 : Blo 334751 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B857375 : Blo 334751 857375 := bstep (se 1 (by rfl) ⟨643031, by rfl⟩ : syracuseStep 857375 = 1286063) B1286063
theorem B759239 : Blo 334751 759239 := bstep (se 1 (by rfl) ⟨569429, by rfl⟩ : syracuseStep 759239 = 1138859) B1138859
theorem B1152569 : Blo 334751 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B759599 : Blo 334751 759599 := bstep (se 1 (by rfl) ⟨569699, by rfl⟩ : syracuseStep 759599 = 1139399) B1139399
theorem B1283921 : Blo 334751 1283921 := bstep (se 2 (by rfl) ⟨481470, by rfl⟩ : syracuseStep 1283921 = 962941) B962941
theorem B1939535 : Blo 334751 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B760175 : Blo 334751 760175 := bstep (se 1 (by rfl) ⟨570131, by rfl⟩ : syracuseStep 760175 = 1140263) B1140263
theorem B760247 : Blo 334751 760247 := bstep (se 1 (by rfl) ⟨570185, by rfl⟩ : syracuseStep 760247 = 1140371) B1140371
theorem B760391 : Blo 334751 760391 := bstep (se 1 (by rfl) ⟨570293, by rfl⟩ : syracuseStep 760391 = 1140587) B1140587
theorem B2595401 : Blo 334751 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B760427 : Blo 334751 760427 := bstep (se 1 (by rfl) ⟨570320, by rfl⟩ : syracuseStep 760427 = 1140641) B1140641
theorem B11606819 : Blo 334751 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B334799 : Blo 334751 334799 := bstep (se 1 (by rfl) ⟨251099, by rfl⟩ : syracuseStep 334799 = 502199) B502199
theorem B334823 : Blo 334751 334823 := bstep (se 1 (by rfl) ⟨251117, by rfl⟩ : syracuseStep 334823 = 502235) B502235
theorem B760823 : Blo 334751 760823 := bstep (se 1 (by rfl) ⟨570617, by rfl⟩ : syracuseStep 760823 = 1141235) B1141235
theorem B335135 : Blo 334751 335135 := bstep (se 1 (by rfl) ⟨251351, by rfl⟩ : syracuseStep 335135 = 502703) B502703
theorem B335195 : Blo 334751 335195 := bstep (se 1 (by rfl) ⟨251396, by rfl⟩ : syracuseStep 335195 = 502793) B502793
theorem B761183 : Blo 334751 761183 := bstep (se 1 (by rfl) ⟨570887, by rfl⟩ : syracuseStep 761183 = 1141775) B1141775
theorem B335215 : Blo 334751 335215 := bstep (se 1 (by rfl) ⟨251411, by rfl⟩ : syracuseStep 335215 = 502823) B502823
theorem B335271 : Blo 334751 335271 := bstep (se 1 (by rfl) ⟨251453, by rfl⟩ : syracuseStep 335271 = 502907) B502907
theorem B1285591 : Blo 334751 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B335355 : Blo 334751 335355 := bstep (se 1 (by rfl) ⟨251516, by rfl⟩ : syracuseStep 335355 = 503033) B503033
theorem B335423 : Blo 334751 335423 := bstep (se 1 (by rfl) ⟨251567, by rfl⟩ : syracuseStep 335423 = 503135) B503135
theorem B335431 : Blo 334751 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B335583 : Blo 334751 335583 := bstep (se 1 (by rfl) ⟨251687, by rfl⟩ : syracuseStep 335583 = 503375) B503375
theorem B761579 : Blo 334751 761579 := bstep (se 1 (by rfl) ⟨571184, by rfl⟩ : syracuseStep 761579 = 1142369) B1142369
theorem B1285895 : Blo 334751 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B1154827 : Blo 334751 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B335663 : Blo 334751 335663 := bstep (se 1 (by rfl) ⟨251747, by rfl⟩ : syracuseStep 335663 = 503495) B503495
theorem B565049 : Blo 334751 565049 := bstep (se 2 (by rfl) ⟨211893, by rfl⟩ : syracuseStep 565049 = 423787) B423787
theorem B761705 : Blo 334751 761705 := bstep (se 2 (by rfl) ⟨285639, by rfl⟩ : syracuseStep 761705 = 571279) B571279
theorem B335771 : Blo 334751 335771 := bstep (se 1 (by rfl) ⟨251828, by rfl⟩ : syracuseStep 335771 = 503657) B503657
theorem B335823 : Blo 334751 335823 := bstep (se 1 (by rfl) ⟨251867, by rfl⟩ : syracuseStep 335823 = 503735) B503735
theorem B335847 : Blo 334751 335847 := bstep (se 1 (by rfl) ⟨251885, by rfl⟩ : syracuseStep 335847 = 503771) B503771
theorem B2433235 : Blo 334751 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1712339 : Blo 334751 1712339 := bstep (se 1 (by rfl) ⟨1284254, by rfl⟩ : syracuseStep 1712339 = 2568509) B2568509
theorem B336159 : Blo 334751 336159 := bstep (se 1 (by rfl) ⟨252119, by rfl⟩ : syracuseStep 336159 = 504239) B504239
theorem B336219 : Blo 334751 336219 := bstep (se 1 (by rfl) ⟨252164, by rfl⟩ : syracuseStep 336219 = 504329) B504329
theorem B336239 : Blo 334751 336239 := bstep (se 1 (by rfl) ⟨252179, by rfl⟩ : syracuseStep 336239 = 504359) B504359
theorem B336295 : Blo 334751 336295 := bstep (se 1 (by rfl) ⟨252221, by rfl⟩ : syracuseStep 336295 = 504443) B504443
theorem B336379 : Blo 334751 336379 := bstep (se 1 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 336379 = 504569) B504569
theorem B336447 : Blo 334751 336447 := bstep (se 1 (by rfl) ⟨252335, by rfl⟩ : syracuseStep 336447 = 504671) B504671
theorem B336455 : Blo 334751 336455 := bstep (se 1 (by rfl) ⟨252341, by rfl⟩ : syracuseStep 336455 = 504683) B504683
theorem B1647175 : Blo 334751 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B1450649 : Blo 334751 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B336607 : Blo 334751 336607 := bstep (se 1 (by rfl) ⟨252455, by rfl⟩ : syracuseStep 336607 = 504911) B504911
theorem B336687 : Blo 334751 336687 := bstep (se 1 (by rfl) ⟨252515, by rfl⟩ : syracuseStep 336687 = 505031) B505031
theorem B566095 : Blo 334751 566095 := bstep (se 1 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 566095 = 849143) B849143
theorem B336795 : Blo 334751 336795 := bstep (se 1 (by rfl) ⟨252596, by rfl⟩ : syracuseStep 336795 = 505193) B505193
theorem B336847 : Blo 334751 336847 := bstep (se 1 (by rfl) ⟨252635, by rfl⟩ : syracuseStep 336847 = 505271) B505271
theorem B336871 : Blo 334751 336871 := bstep (se 1 (by rfl) ⟨252653, by rfl⟩ : syracuseStep 336871 = 505307) B505307
theorem B1090685 : Blo 334751 1090685 := bstep (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) B409007
theorem B1025257 : Blo 334751 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B337183 : Blo 334751 337183 := bstep (se 1 (by rfl) ⟨252887, by rfl⟩ : syracuseStep 337183 = 505775) B505775
theorem B4629811 : Blo 334751 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B337243 : Blo 334751 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B337263 : Blo 334751 337263 := bstep (se 1 (by rfl) ⟨252947, by rfl⟩ : syracuseStep 337263 = 505895) B505895
theorem B337319 : Blo 334751 337319 := bstep (se 1 (by rfl) ⟨252989, by rfl⟩ : syracuseStep 337319 = 505979) B505979
theorem B566777 : Blo 334751 566777 := bstep (se 2 (by rfl) ⟨212541, by rfl⟩ : syracuseStep 566777 = 425083) B425083
theorem B337403 : Blo 334751 337403 := bstep (se 1 (by rfl) ⟨253052, by rfl⟩ : syracuseStep 337403 = 506105) B506105
theorem B337471 : Blo 334751 337471 := bstep (se 1 (by rfl) ⟨253103, by rfl⟩ : syracuseStep 337471 = 506207) B506207
theorem B337479 : Blo 334751 337479 := bstep (se 1 (by rfl) ⟨253109, by rfl⟩ : syracuseStep 337479 = 506219) B506219
theorem B2827997 : Blo 334751 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B337631 : Blo 334751 337631 := bstep (se 1 (by rfl) ⟨253223, by rfl⟩ : syracuseStep 337631 = 506447) B506447
theorem B567047 : Blo 334751 567047 := bstep (se 1 (by rfl) ⟨425285, by rfl⟩ : syracuseStep 567047 = 850571) B850571
theorem B337711 : Blo 334751 337711 := bstep (se 1 (by rfl) ⟨253283, by rfl⟩ : syracuseStep 337711 = 506567) B506567
theorem B337819 : Blo 334751 337819 := bstep (se 1 (by rfl) ⟨253364, by rfl⟩ : syracuseStep 337819 = 506729) B506729
theorem B337871 : Blo 334751 337871 := bstep (se 1 (by rfl) ⟨253403, by rfl⟩ : syracuseStep 337871 = 506807) B506807
theorem B337895 : Blo 334751 337895 := bstep (se 1 (by rfl) ⟨253421, by rfl⟩ : syracuseStep 337895 = 506843) B506843
theorem B3221633 : Blo 334751 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B4368563 : Blo 334751 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B338207 : Blo 334751 338207 := bstep (se 1 (by rfl) ⟨253655, by rfl⟩ : syracuseStep 338207 = 507311) B507311
theorem B338267 : Blo 334751 338267 := bstep (se 1 (by rfl) ⟨253700, by rfl⟩ : syracuseStep 338267 = 507401) B507401
theorem B502127 : Blo 334751 502127 := bstep (se 1 (by rfl) ⟨376595, by rfl⟩ : syracuseStep 502127 = 753191) B753191
theorem B338287 : Blo 334751 338287 := bstep (se 1 (by rfl) ⟨253715, by rfl⟩ : syracuseStep 338287 = 507431) B507431
theorem B4336001 : Blo 334751 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B338343 : Blo 334751 338343 := bstep (se 1 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 338343 = 507515) B507515
theorem B567803 : Blo 334751 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B338427 : Blo 334751 338427 := bstep (se 1 (by rfl) ⟨253820, by rfl⟩ : syracuseStep 338427 = 507641) B507641
theorem B338495 : Blo 334751 338495 := bstep (se 1 (by rfl) ⟨253871, by rfl⟩ : syracuseStep 338495 = 507743) B507743
theorem B502343 : Blo 334751 502343 := bstep (se 1 (by rfl) ⟨376757, by rfl⟩ : syracuseStep 502343 = 753515) B753515
theorem B338503 : Blo 334751 338503 := bstep (se 1 (by rfl) ⟨253877, by rfl⟩ : syracuseStep 338503 = 507755) B507755
theorem B502379 : Blo 334751 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B338655 : Blo 334751 338655 := bstep (se 1 (by rfl) ⟨253991, by rfl⟩ : syracuseStep 338655 = 507983) B507983
theorem B338735 : Blo 334751 338735 := bstep (se 1 (by rfl) ⟨254051, by rfl⟩ : syracuseStep 338735 = 508103) B508103
theorem B502607 : Blo 334751 502607 := bstep (se 1 (by rfl) ⟨376955, by rfl⟩ : syracuseStep 502607 = 753911) B753911
theorem B568235 : Blo 334751 568235 := bstep (se 1 (by rfl) ⟨426176, by rfl⟩ : syracuseStep 568235 = 852353) B852353
theorem B503003 : Blo 334751 503003 := bstep (se 1 (by rfl) ⟨377252, by rfl⟩ : syracuseStep 503003 = 754505) B754505
theorem B16035191 : Blo 334751 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B503177 : Blo 334751 503177 := bstep (se 2 (by rfl) ⟨188691, by rfl⟩ : syracuseStep 503177 = 377383) B377383
theorem B568775 : Blo 334751 568775 := bstep (se 1 (by rfl) ⟨426581, by rfl⟩ : syracuseStep 568775 = 853163) B853163
theorem B1912531 : Blo 334751 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B503531 : Blo 334751 503531 := bstep (se 1 (by rfl) ⟨377648, by rfl⟩ : syracuseStep 503531 = 755297) B755297
theorem B503759 : Blo 334751 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B1028105 : Blo 334751 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B504155 : Blo 334751 504155 := bstep (se 1 (by rfl) ⟨378116, by rfl⟩ : syracuseStep 504155 = 756233) B756233
theorem B569767 : Blo 334751 569767 := bstep (se 1 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 569767 = 854651) B854651
theorem B504383 : Blo 334751 504383 := bstep (se 1 (by rfl) ⟨378287, by rfl⟩ : syracuseStep 504383 = 756575) B756575
theorem B569929 : Blo 334751 569929 := bstep (se 2 (by rfl) ⟨213723, by rfl⟩ : syracuseStep 569929 = 427447) B427447
theorem B569963 : Blo 334751 569963 := bstep (se 1 (by rfl) ⟨427472, by rfl⟩ : syracuseStep 569963 = 854945) B854945
theorem B504503 : Blo 334751 504503 := bstep (se 1 (by rfl) ⟨378377, by rfl⟩ : syracuseStep 504503 = 756755) B756755
theorem B4895417 : Blo 334751 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B504731 : Blo 334751 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B4306067 : Blo 334751 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B2864423 : Blo 334751 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B505127 : Blo 334751 505127 := bstep (se 1 (by rfl) ⟨378845, by rfl⟩ : syracuseStep 505127 = 757691) B757691
theorem B2372903 : Blo 334751 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B505211 : Blo 334751 505211 := bstep (se 1 (by rfl) ⟨378908, by rfl⟩ : syracuseStep 505211 = 757817) B757817
theorem B964001 : Blo 334751 964001 := bstep (se 2 (by rfl) ⟨361500, by rfl⟩ : syracuseStep 964001 = 723001) B723001
theorem B538105 : Blo 334751 538105 := bstep (se 2 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 538105 = 403579) B403579
theorem B505337 : Blo 334751 505337 := bstep (se 2 (by rfl) ⟨189501, by rfl⟩ : syracuseStep 505337 = 379003) B379003
theorem B3225095 : Blo 334751 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B538207 : Blo 334751 538207 := bstep (se 1 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 538207 = 807311) B807311
theorem B505439 : Blo 334751 505439 := bstep (se 1 (by rfl) ⟨379079, by rfl⟩ : syracuseStep 505439 = 758159) B758159
theorem B505655 : Blo 334751 505655 := bstep (se 1 (by rfl) ⟨379241, by rfl⟩ : syracuseStep 505655 = 758483) B758483
theorem B964457 : Blo 334751 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B505961 : Blo 334751 505961 := bstep (se 2 (by rfl) ⟨189735, by rfl⟩ : syracuseStep 505961 = 379471) B379471
theorem B2177405 : Blo 334751 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B506279 : Blo 334751 506279 := bstep (se 1 (by rfl) ⟨379709, by rfl⟩ : syracuseStep 506279 = 759419) B759419
theorem B506363 : Blo 334751 506363 := bstep (se 1 (by rfl) ⟨379772, by rfl⟩ : syracuseStep 506363 = 759545) B759545
theorem B506489 : Blo 334751 506489 := bstep (se 2 (by rfl) ⟨189933, by rfl⟩ : syracuseStep 506489 = 379867) B379867
theorem B506543 : Blo 334751 506543 := bstep (se 1 (by rfl) ⟨379907, by rfl⟩ : syracuseStep 506543 = 759815) B759815
theorem B506591 : Blo 334751 506591 := bstep (se 1 (by rfl) ⟨379943, by rfl⟩ : syracuseStep 506591 = 759887) B759887
theorem B52312949 : Blo 334751 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B1457021 : Blo 334751 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B2866063 : Blo 334751 2866063 := bstep (se 1 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 2866063 = 4299095) B4299095
theorem B5782427 : Blo 334751 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B506855 : Blo 334751 506855 := bstep (se 1 (by rfl) ⟨380141, by rfl⟩ : syracuseStep 506855 = 760283) B760283
theorem B507113 : Blo 334751 507113 := bstep (se 2 (by rfl) ⟨190167, by rfl⟩ : syracuseStep 507113 = 380335) B380335
theorem B507167 : Blo 334751 507167 := bstep (se 1 (by rfl) ⟨380375, by rfl⟩ : syracuseStep 507167 = 760751) B760751
theorem B507335 : Blo 334751 507335 := bstep (se 1 (by rfl) ⟨380501, by rfl⟩ : syracuseStep 507335 = 761003) B761003
theorem B3817043 : Blo 334751 3817043 := bstep (se 1 (by rfl) ⟨2862782, by rfl⟩ : syracuseStep 3817043 = 5725565) B5725565
theorem B1130219 : Blo 334751 1130219 := bstep (se 1 (by rfl) ⟨847664, by rfl⟩ : syracuseStep 1130219 = 1695329) B1695329
theorem B507689 : Blo 334751 507689 := bstep (se 2 (by rfl) ⟨190383, by rfl⟩ : syracuseStep 507689 = 380767) B380767
theorem B507695 : Blo 334751 507695 := bstep (se 1 (by rfl) ⟨380771, by rfl⟩ : syracuseStep 507695 = 761543) B761543
theorem B1621889 : Blo 334751 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B376807 : Blo 334751 376807 := bstep (se 1 (by rfl) ⟨282605, by rfl⟩ : syracuseStep 376807 = 565211) B565211
theorem B606631 : Blo 334751 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B1131191 : Blo 334751 1131191 := bstep (se 1 (by rfl) ⟨848393, by rfl⟩ : syracuseStep 1131191 = 1696787) B1696787
theorem B3621827 : Blo 334751 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B5751809 : Blo 334751 5751809 := bstep (se 2 (by rfl) ⟨2156928, by rfl⟩ : syracuseStep 5751809 = 4313857) B4313857
theorem B3654659 : Blo 334751 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B2639147 : Blo 334751 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B1754561 : Blo 334751 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B4376051 : Blo 334751 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B378463 : Blo 334751 378463 := bstep (se 1 (by rfl) ⟨283847, by rfl⟩ : syracuseStep 378463 = 567695) B567695
theorem B607979 : Blo 334751 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B2312081 : Blo 334751 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B9193601 : Blo 334751 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B26364149 : Blo 334751 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1624349 : Blo 334751 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B1624463 : Blo 334751 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B1133135 : Blo 334751 1133135 := bstep (se 1 (by rfl) ⟨849851, by rfl⟩ : syracuseStep 1133135 = 1699703) B1699703
theorem B641657 : Blo 334751 641657 := bstep (se 2 (by rfl) ⟨240621, by rfl⟩ : syracuseStep 641657 = 481243) B481243
theorem B379615 : Blo 334751 379615 := bstep (se 1 (by rfl) ⟨284711, by rfl⟩ : syracuseStep 379615 = 569423) B569423
theorem B5786801 : Blo 334751 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B380191 : Blo 334751 380191 := bstep (se 1 (by rfl) ⟨285143, by rfl⟩ : syracuseStep 380191 = 570287) B570287
theorem B642401 : Blo 334751 642401 := bstep (se 2 (by rfl) ⟨240900, by rfl⟩ : syracuseStep 642401 = 481801) B481801
theorem B5459345 : Blo 334751 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B380479 : Blo 334751 380479 := bstep (se 1 (by rfl) ⟨285359, by rfl⟩ : syracuseStep 380479 = 570719) B570719
theorem B1920779 : Blo 334751 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B1134377 : Blo 334751 1134377 := bstep (se 2 (by rfl) ⟨425391, by rfl⟩ : syracuseStep 1134377 = 850783) B850783
theorem B10342187 : Blo 334751 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B1298761 : Blo 334751 1298761 := bstep (se 2 (by rfl) ⟨487035, by rfl⟩ : syracuseStep 1298761 = 974071) B974071
theorem B1626923 : Blo 334751 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B578459 : Blo 334751 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B1430743 : Blo 334751 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B1299671 : Blo 334751 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B1430777 : Blo 334751 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B1431377 : Blo 334751 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B1136591 : Blo 334751 1136591 := bstep (se 1 (by rfl) ⟨852443, by rfl⟩ : syracuseStep 1136591 = 1704887) B1704887
theorem B481231 : Blo 334751 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B2218063 : Blo 334751 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B2578679 : Blo 334751 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B2152727 : Blo 334751 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B3234437 : Blo 334751 3234437 := bstep (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) B606457
theorem B1727165 : Blo 334751 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B1137563 : Blo 334751 1137563 := bstep (se 1 (by rfl) ⟨853172, by rfl⟩ : syracuseStep 1137563 = 1706345) B1706345
theorem B1924013 : Blo 334751 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B482279 : Blo 334751 482279 := bstep (se 1 (by rfl) ⟨361709, by rfl⟩ : syracuseStep 482279 = 723419) B723419
theorem B1432691 : Blo 334751 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1694843 : Blo 334751 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B810233 : Blo 334751 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B1170875 : Blo 334751 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B3661271 : Blo 334751 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2186833 : Blo 334751 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1695491 : Blo 334751 1695491 := bstep (se 1 (by rfl) ⟨1271618, by rfl⟩ : syracuseStep 1695491 = 2543237) B2543237
theorem B1138589 : Blo 334751 1138589 := bstep (se 3 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 1138589 = 426971) B426971
theorem B1138697 : Blo 334751 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B680359 : Blo 334751 680359 := bstep (se 1 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 680359 = 1020539) B1020539
theorem B1697111 : Blo 334751 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B2876795 : Blo 334751 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B812425 : Blo 334751 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B1435117 : Blo 334751 1435117 := bstep (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) B538169
theorem B1271483 : Blo 334751 1271483 := bstep (se 1 (by rfl) ⟨953612, by rfl⟩ : syracuseStep 1271483 = 1907225) B1907225
theorem B1697921 : Blo 334751 1697921 := bstep (se 2 (by rfl) ⟨636720, by rfl⟩ : syracuseStep 1697921 = 1273441) B1273441
theorem B1075481 : Blo 334751 1075481 := bstep (se 2 (by rfl) ⟨403305, by rfl⟩ : syracuseStep 1075481 = 806611) B806611
theorem B6121763 : Blo 334751 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B715081 : Blo 334751 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B715115 : Blo 334751 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B4680179 : Blo 334751 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B911945 : Blo 334751 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1698731 : Blo 334751 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B1272955 : Blo 334751 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B1141883 : Blo 334751 1141883 := bstep (se 1 (by rfl) ⟨856412, by rfl⟩ : syracuseStep 1141883 = 1712825) B1712825
theorem B453919 : Blo 334751 453919 := bstep (se 1 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 453919 = 680879) B680879
theorem B1437065 : Blo 334751 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B1142153 : Blo 334751 1142153 := bstep (se 2 (by rfl) ⟨428307, by rfl⟩ : syracuseStep 1142153 = 856615) B856615
theorem B1273427 : Blo 334751 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B1830509 : Blo 334751 1830509 := bstep (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) B686441
theorem B2879185 : Blo 334751 2879185 := bstep (se 2 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 2879185 = 2159389) B2159389
theorem B1142585 : Blo 334751 1142585 := bstep (se 2 (by rfl) ⟨428469, by rfl⟩ : syracuseStep 1142585 = 856939) B856939
theorem B1699865 : Blo 334751 1699865 := bstep (se 2 (by rfl) ⟨637449, by rfl⟩ : syracuseStep 1699865 = 1274899) B1274899
theorem B4616279 : Blo 334751 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B848303 : Blo 334751 848303 := bstep (se 1 (by rfl) ⟨636227, by rfl⟩ : syracuseStep 848303 = 1272455) B1272455
theorem B913847 : Blo 334751 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B848353 : Blo 334751 848353 := bstep (se 2 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 848353 = 636265) B636265
theorem B717815 : Blo 334751 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B2552957 : Blo 334751 2552957 := bstep (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) B957359
theorem B685289 : Blo 334751 685289 := bstep (se 2 (by rfl) ⟨256983, by rfl⟩ : syracuseStep 685289 = 513967) B513967
theorem B5174545 : Blo 334751 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B8189207 : Blo 334751 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B849275 : Blo 334751 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B718217 : Blo 334751 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B6453107 : Blo 334751 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B149157773 : Blo 334751 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1210621 : Blo 334751 1210621 := bstep (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) B453983
theorem B719113 : Blo 334751 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B1079581 : Blo 334751 1079581 := bstep (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) B404843
theorem B1440125 : Blo 334751 1440125 := bstep (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) B540047
theorem B1276343 : Blo 334751 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B424759 : Blo 334751 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B1702781 : Blo 334751 1702781 := bstep (se 3 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 1702781 = 638543) B638543
theorem B1276843 : Blo 334751 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B851087 : Blo 334751 851087 := bstep (se 1 (by rfl) ⟨638315, by rfl⟩ : syracuseStep 851087 = 1276631) B1276631
theorem B1277117 : Blo 334751 1277117 := bstep (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) B478919
theorem B425179 : Blo 334751 425179 := bstep (se 1 (by rfl) ⟨318884, by rfl⟩ : syracuseStep 425179 = 637769) B637769
theorem B1277147 : Blo 334751 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B3898691 : Blo 334751 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B10911149 : Blo 334751 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B753209 : Blo 334751 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B1703753 : Blo 334751 1703753 := bstep (se 2 (by rfl) ⟨638907, by rfl⟩ : syracuseStep 1703753 = 1277815) B1277815
theorem B3244313 : Blo 334751 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B35324219 : Blo 334751 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B754127 : Blo 334751 754127 := bstep (se 1 (by rfl) ⟨565595, by rfl⟩ : syracuseStep 754127 = 1131191) B1131191
theorem B3834539 : Blo 334751 3834539 := bstep (se 1 (by rfl) ⟨2875904, by rfl⟩ : syracuseStep 3834539 = 5751809) B5751809
theorem B2196233 : Blo 334751 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B2917367 : Blo 334751 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B754793 : Blo 334751 754793 := bstep (se 2 (by rfl) ⟨283047, by rfl⟩ : syracuseStep 754793 = 566095) B566095
theorem B1541387 : Blo 334751 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B853355 : Blo 334751 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B6129067 : Blo 334751 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B1082899 : Blo 334751 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B1082975 : Blo 334751 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B755423 : Blo 334751 755423 := bstep (se 1 (by rfl) ⟨566567, by rfl⟩ : syracuseStep 755423 = 1133135) B1133135
theorem B427771 : Blo 334751 427771 := bstep (se 1 (by rfl) ⟨320828, by rfl⟩ : syracuseStep 427771 = 641657) B641657
theorem B1083233 : Blo 334751 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B428267 : Blo 334751 428267 := bstep (se 1 (by rfl) ⟨321200, by rfl⟩ : syracuseStep 428267 = 642401) B642401
theorem B3639563 : Blo 334751 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B6162779 : Blo 334751 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B1542557 : Blo 334751 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1280519 : Blo 334751 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B756251 : Blo 334751 756251 := bstep (se 1 (by rfl) ⟨567188, by rfl⟩ : syracuseStep 756251 = 1134377) B1134377
theorem B723487 : Blo 334751 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B1444499 : Blo 334751 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B10325069 : Blo 334751 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B953441 : Blo 334751 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B5835995 : Blo 334751 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B953851 : Blo 334751 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B954251 : Blo 334751 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B855947 : Blo 334751 855947 := bstep (se 1 (by rfl) ⟨641960, by rfl⟩ : syracuseStep 855947 = 1283921) B1283921
theorem B757727 : Blo 334751 757727 := bstep (se 1 (by rfl) ⟨568295, by rfl⟩ : syracuseStep 757727 = 1136591) B1136591
theorem B1151443 : Blo 334751 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B758375 : Blo 334751 758375 := bstep (se 1 (by rfl) ⟨568781, by rfl⟩ : syracuseStep 758375 = 1137563) B1137563
theorem B1282675 : Blo 334751 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B955127 : Blo 334751 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B3838913 : Blo 334751 3838913 := bstep (se 2 (by rfl) ⟨1439592, by rfl⟩ : syracuseStep 3838913 = 2879185) B2879185
theorem B9311377 : Blo 334751 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B857263 : Blo 334751 857263 := bstep (se 1 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 857263 = 1285895) B1285895
theorem B759059 : Blo 334751 759059 := bstep (se 1 (by rfl) ⟨569294, by rfl⟩ : syracuseStep 759059 = 1138589) B1138589
theorem B759131 : Blo 334751 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B759689 : Blo 334751 759689 := bstep (se 2 (by rfl) ⟨284883, by rfl⟩ : syracuseStep 759689 = 569767) B569767
theorem B759905 : Blo 334751 759905 := bstep (se 2 (by rfl) ⟨284964, by rfl⟩ : syracuseStep 759905 = 569929) B569929
theorem B1906973 : Blo 334751 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B2431853 : Blo 334751 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B334751 : Blo 334751 334751 := bstep (se 1 (by rfl) ⟨251063, by rfl⟩ : syracuseStep 334751 = 502127) B502127
theorem B2890667 : Blo 334751 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B1907657 : Blo 334751 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B3120119 : Blo 334751 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B334895 : Blo 334751 334895 := bstep (se 1 (by rfl) ⟨251171, by rfl⟩ : syracuseStep 334895 = 502343) B502343
theorem B334919 : Blo 334751 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B335071 : Blo 334751 335071 := bstep (se 1 (by rfl) ⟨251303, by rfl⟩ : syracuseStep 335071 = 502607) B502607
theorem B761255 : Blo 334751 761255 := bstep (se 1 (by rfl) ⟨570941, by rfl⟩ : syracuseStep 761255 = 1141883) B1141883
theorem B335335 : Blo 334751 335335 := bstep (se 1 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 335335 = 503003) B503003
theorem B10690127 : Blo 334751 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B335451 : Blo 334751 335451 := bstep (se 1 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 335451 = 503177) B503177
theorem B958043 : Blo 334751 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B761435 : Blo 334751 761435 := bstep (se 1 (by rfl) ⟨571076, by rfl⟩ : syracuseStep 761435 = 1142153) B1142153
theorem B1220339 : Blo 334751 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B335687 : Blo 334751 335687 := bstep (se 1 (by rfl) ⟨251765, by rfl⟩ : syracuseStep 335687 = 503531) B503531
theorem B761723 : Blo 334751 761723 := bstep (se 1 (by rfl) ⟨571292, by rfl⟩ : syracuseStep 761723 = 1142585) B1142585
theorem B1286077 : Blo 334751 1286077 := bstep (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) B482279
theorem B335839 : Blo 334751 335839 := bstep (se 1 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 335839 = 503759) B503759
theorem B2957417 : Blo 334751 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B336103 : Blo 334751 336103 := bstep (se 1 (by rfl) ⟨252077, by rfl⟩ : syracuseStep 336103 = 504155) B504155
theorem B565535 : Blo 334751 565535 := bstep (se 1 (by rfl) ⟨424151, by rfl⟩ : syracuseStep 565535 = 848303) B848303
theorem B1614161 : Blo 334751 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B958817 : Blo 334751 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B336255 : Blo 334751 336255 := bstep (se 1 (by rfl) ⟨252191, by rfl⟩ : syracuseStep 336255 = 504383) B504383
theorem B336335 : Blo 334751 336335 := bstep (se 1 (by rfl) ⟨252251, by rfl⟩ : syracuseStep 336335 = 504503) B504503
theorem B336487 : Blo 334751 336487 := bstep (se 1 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 336487 = 504731) B504731
theorem B1909615 : Blo 334751 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B336751 : Blo 334751 336751 := bstep (se 1 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 336751 = 505127) B505127
theorem B1581935 : Blo 334751 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B566183 : Blo 334751 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B336807 : Blo 334751 336807 := bstep (se 1 (by rfl) ⟨252605, by rfl⟩ : syracuseStep 336807 = 505211) B505211
theorem B336891 : Blo 334751 336891 := bstep (se 1 (by rfl) ⟨252668, by rfl⟩ : syracuseStep 336891 = 505337) B505337
theorem B336959 : Blo 334751 336959 := bstep (se 1 (by rfl) ⟨252719, by rfl⟩ : syracuseStep 336959 = 505439) B505439
theorem B566345 : Blo 334751 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B3122333 : Blo 334751 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B337103 : Blo 334751 337103 := bstep (se 1 (by rfl) ⟨252827, by rfl⟩ : syracuseStep 337103 = 505655) B505655
theorem B4302071 : Blo 334751 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B337307 : Blo 334751 337307 := bstep (se 1 (by rfl) ⟨252980, by rfl⟩ : syracuseStep 337307 = 505961) B505961
theorem B1451603 : Blo 334751 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B960083 : Blo 334751 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B337519 : Blo 334751 337519 := bstep (se 1 (by rfl) ⟨253139, by rfl⟩ : syracuseStep 337519 = 506279) B506279
theorem B566905 : Blo 334751 566905 := bstep (se 2 (by rfl) ⟨212589, by rfl⟩ : syracuseStep 566905 = 425179) B425179
theorem B337575 : Blo 334751 337575 := bstep (se 1 (by rfl) ⟨253181, by rfl⟩ : syracuseStep 337575 = 506363) B506363
theorem B337659 : Blo 334751 337659 := bstep (se 1 (by rfl) ⟨253244, by rfl⟩ : syracuseStep 337659 = 506489) B506489
theorem B337695 : Blo 334751 337695 := bstep (se 1 (by rfl) ⟨253271, by rfl⟩ : syracuseStep 337695 = 506543) B506543
theorem B337727 : Blo 334751 337727 := bstep (se 1 (by rfl) ⟨253295, by rfl⟩ : syracuseStep 337727 = 506591) B506591
theorem B34875299 : Blo 334751 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B1714121 : Blo 334751 1714121 := bstep (se 2 (by rfl) ⟨642795, by rfl⟩ : syracuseStep 1714121 = 1285591) B1285591
theorem B337903 : Blo 334751 337903 := bstep (se 1 (by rfl) ⟨253427, by rfl⟩ : syracuseStep 337903 = 506855) B506855
theorem B567391 : Blo 334751 567391 := bstep (se 1 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 567391 = 851087) B851087
theorem B338075 : Blo 334751 338075 := bstep (se 1 (by rfl) ⟨253556, by rfl⟩ : syracuseStep 338075 = 507113) B507113
theorem B338111 : Blo 334751 338111 := bstep (se 1 (by rfl) ⟨253583, by rfl⟩ : syracuseStep 338111 = 507167) B507167
theorem B2599127 : Blo 334751 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B338223 : Blo 334751 338223 := bstep (se 1 (by rfl) ⟨253667, by rfl⟩ : syracuseStep 338223 = 507335) B507335
theorem B502139 : Blo 334751 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B2566565 : Blo 334751 2566565 := bstep (se 4 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 2566565 = 481231) B481231
theorem B338459 : Blo 334751 338459 := bstep (se 1 (by rfl) ⟨253844, by rfl⟩ : syracuseStep 338459 = 507689) B507689
theorem B338463 : Blo 334751 338463 := bstep (se 1 (by rfl) ⟨253847, by rfl⟩ : syracuseStep 338463 = 507695) B507695
theorem B502409 : Blo 334751 502409 := bstep (se 2 (by rfl) ⟨188403, by rfl⟩ : syracuseStep 502409 = 376807) B376807
theorem B502583 : Blo 334751 502583 := bstep (se 1 (by rfl) ⟨376937, by rfl⟩ : syracuseStep 502583 = 753875) B753875
theorem B502619 : Blo 334751 502619 := bstep (se 1 (by rfl) ⟨376964, by rfl⟩ : syracuseStep 502619 = 753929) B753929
theorem B502763 : Blo 334751 502763 := bstep (se 1 (by rfl) ⟨377072, by rfl⟩ : syracuseStep 502763 = 754145) B754145
theorem B502967 : Blo 334751 502967 := bstep (se 1 (by rfl) ⟨377225, by rfl⟩ : syracuseStep 502967 = 754451) B754451
theorem B2436439 : Blo 334751 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B568687 : Blo 334751 568687 := bstep (se 1 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 568687 = 853031) B853031
theorem B503207 : Blo 334751 503207 := bstep (se 1 (by rfl) ⟨377405, by rfl⟩ : syracuseStep 503207 = 754811) B754811
theorem B503291 : Blo 334751 503291 := bstep (se 1 (by rfl) ⟨377468, by rfl⟩ : syracuseStep 503291 = 754937) B754937
theorem B503387 : Blo 334751 503387 := bstep (se 1 (by rfl) ⟨377540, by rfl⟩ : syracuseStep 503387 = 755081) B755081
theorem B503471 : Blo 334751 503471 := bstep (se 1 (by rfl) ⟨377603, by rfl⟩ : syracuseStep 503471 = 755207) B755207
theorem B569065 : Blo 334751 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B503591 : Blo 334751 503591 := bstep (se 1 (by rfl) ⟨377693, by rfl⟩ : syracuseStep 503591 = 755387) B755387
theorem B405319 : Blo 334751 405319 := bstep (se 1 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 405319 = 607979) B607979
theorem B503675 : Blo 334751 503675 := bstep (se 1 (by rfl) ⟨377756, by rfl⟩ : syracuseStep 503675 = 755513) B755513
theorem B17576099 : Blo 334751 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B569531 : Blo 334751 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B1814723 : Blo 334751 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B504095 : Blo 334751 504095 := bstep (se 1 (by rfl) ⟨378071, by rfl⟩ : syracuseStep 504095 = 756143) B756143
theorem B504119 : Blo 334751 504119 := bstep (se 1 (by rfl) ⟨378089, by rfl⟩ : syracuseStep 504119 = 756179) B756179
theorem B504191 : Blo 334751 504191 := bstep (se 1 (by rfl) ⟨378143, by rfl⟩ : syracuseStep 504191 = 756287) B756287
theorem B6926725 : Blo 334751 6926725 := bstep (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) B1298761
theorem B6173081 : Blo 334751 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B504263 : Blo 334751 504263 := bstep (se 1 (by rfl) ⟨378197, by rfl⟩ : syracuseStep 504263 = 756395) B756395
theorem B13054445 : Blo 334751 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B1913489 : Blo 334751 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B570091 : Blo 334751 570091 := bstep (se 1 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 570091 = 855137) B855137
theorem B4338461 : Blo 334751 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B504617 : Blo 334751 504617 := bstep (se 2 (by rfl) ⟨189231, by rfl⟩ : syracuseStep 504617 = 378463) B378463
theorem B504623 : Blo 334751 504623 := bstep (se 1 (by rfl) ⟨378467, by rfl⟩ : syracuseStep 504623 = 756935) B756935
theorem B504743 : Blo 334751 504743 := bstep (se 1 (by rfl) ⟨378557, by rfl⟩ : syracuseStep 504743 = 757115) B757115
theorem B504827 : Blo 334751 504827 := bstep (se 1 (by rfl) ⟨378620, by rfl⟩ : syracuseStep 504827 = 757241) B757241
theorem B504887 : Blo 334751 504887 := bstep (se 1 (by rfl) ⟨378665, by rfl⟩ : syracuseStep 504887 = 757331) B757331
theorem B963647 : Blo 334751 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B505007 : Blo 334751 505007 := bstep (se 1 (by rfl) ⟨378755, by rfl⟩ : syracuseStep 505007 = 757511) B757511
theorem B6894791 : Blo 334751 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B3847661 : Blo 334751 3847661 := bstep (se 3 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 3847661 = 1442873) B1442873
theorem B505415 : Blo 334751 505415 := bstep (se 1 (by rfl) ⟨379061, by rfl⟩ : syracuseStep 505415 = 758123) B758123
theorem B505511 : Blo 334751 505511 := bstep (se 1 (by rfl) ⟨379133, by rfl⟩ : syracuseStep 505511 = 758267) B758267
theorem B636599 : Blo 334751 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B571063 : Blo 334751 571063 := bstep (se 1 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 571063 = 856595) B856595
theorem B964331 : Blo 334751 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B505595 : Blo 334751 505595 := bstep (se 1 (by rfl) ⟨379196, by rfl⟩ : syracuseStep 505595 = 758393) B758393
theorem B505631 : Blo 334751 505631 := bstep (se 1 (by rfl) ⟨379223, by rfl⟩ : syracuseStep 505631 = 758447) B758447
theorem B964399 : Blo 334751 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B2733887 : Blo 334751 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B505679 : Blo 334751 505679 := bstep (se 1 (by rfl) ⟨379259, by rfl⟩ : syracuseStep 505679 = 758519) B758519
theorem B505799 : Blo 334751 505799 := bstep (se 1 (by rfl) ⟨379349, by rfl⟩ : syracuseStep 505799 = 758699) B758699
theorem B571367 : Blo 334751 571367 := bstep (se 1 (by rfl) ⟨428525, by rfl⟩ : syracuseStep 571367 = 857051) B857051
theorem B866447 : Blo 334751 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B571583 : Blo 334751 571583 := bstep (se 1 (by rfl) ⟨428687, by rfl⟩ : syracuseStep 571583 = 857375) B857375
theorem B506153 : Blo 334751 506153 := bstep (se 2 (by rfl) ⟨189807, by rfl⟩ : syracuseStep 506153 = 379615) B379615
theorem B506159 : Blo 334751 506159 := bstep (se 1 (by rfl) ⟨379619, by rfl⟩ : syracuseStep 506159 = 759239) B759239
theorem B768379 : Blo 334751 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B506399 : Blo 334751 506399 := bstep (se 1 (by rfl) ⟨379799, by rfl⟩ : syracuseStep 506399 = 759599) B759599
theorem B1293023 : Blo 334751 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B1719119 : Blo 334751 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B506783 : Blo 334751 506783 := bstep (se 1 (by rfl) ⟨380087, by rfl⟩ : syracuseStep 506783 = 760175) B760175
theorem B506831 : Blo 334751 506831 := bstep (se 1 (by rfl) ⟨380123, by rfl⟩ : syracuseStep 506831 = 760247) B760247
theorem B605225 : Blo 334751 605225 := bstep (se 2 (by rfl) ⟨226959, by rfl⟩ : syracuseStep 605225 = 453919) B453919
theorem B506921 : Blo 334751 506921 := bstep (se 2 (by rfl) ⟨190095, by rfl⟩ : syracuseStep 506921 = 380191) B380191
theorem B506927 : Blo 334751 506927 := bstep (se 1 (by rfl) ⟨380195, by rfl⟩ : syracuseStep 506927 = 760391) B760391
theorem B506951 : Blo 334751 506951 := bstep (se 1 (by rfl) ⟨380213, by rfl⟩ : syracuseStep 506951 = 760427) B760427
theorem B9747701 : Blo 334751 9747701 := bstep (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) B913847
theorem B507215 : Blo 334751 507215 := bstep (se 1 (by rfl) ⟨380411, by rfl⟩ : syracuseStep 507215 = 760823) B760823
theorem B1129895 : Blo 334751 1129895 := bstep (se 1 (by rfl) ⟨847421, by rfl⟩ : syracuseStep 1129895 = 1694843) B1694843
theorem B507305 : Blo 334751 507305 := bstep (se 2 (by rfl) ⟨190239, by rfl⟩ : syracuseStep 507305 = 380479) B380479
theorem B540155 : Blo 334751 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B507455 : Blo 334751 507455 := bstep (se 1 (by rfl) ⟨380591, by rfl⟩ : syracuseStep 507455 = 761183) B761183
theorem B2440847 : Blo 334751 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B507719 : Blo 334751 507719 := bstep (se 1 (by rfl) ⟨380789, by rfl⟩ : syracuseStep 507719 = 761579) B761579
theorem B1130327 : Blo 334751 1130327 := bstep (se 1 (by rfl) ⟨847745, by rfl⟩ : syracuseStep 1130327 = 1695491) B1695491
theorem B376699 : Blo 334751 376699 := bstep (se 1 (by rfl) ⟨282524, by rfl⟩ : syracuseStep 376699 = 565049) B565049
theorem B507803 : Blo 334751 507803 := bstep (se 1 (by rfl) ⟨380852, by rfl⟩ : syracuseStep 507803 = 761705) B761705
theorem B967099 : Blo 334751 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1131137 : Blo 334751 1131137 := bstep (se 2 (by rfl) ⟨424176, by rfl⟩ : syracuseStep 1131137 = 848353) B848353
theorem B1131407 : Blo 334751 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B1917863 : Blo 334751 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B377851 : Blo 334751 377851 := bstep (se 1 (by rfl) ⟨283388, by rfl⟩ : syracuseStep 377851 = 566777) B566777
theorem B1885331 : Blo 334751 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B378031 : Blo 334751 378031 := bstep (se 1 (by rfl) ⟨283523, by rfl⟩ : syracuseStep 378031 = 567047) B567047
theorem B2147755 : Blo 334751 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B1131947 : Blo 334751 1131947 := bstep (se 1 (by rfl) ⟨848960, by rfl⟩ : syracuseStep 1131947 = 1697921) B1697921
theorem B4081175 : Blo 334751 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B378535 : Blo 334751 378535 := bstep (se 1 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 378535 = 567803) B567803
theorem B6899393 : Blo 334751 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B1132487 : Blo 334751 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B378823 : Blo 334751 378823 := bstep (se 1 (by rfl) ⟨284117, by rfl⟩ : syracuseStep 378823 = 568235) B568235
theorem B30951517 : Blo 334751 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B379183 : Blo 334751 379183 := bstep (se 1 (by rfl) ⟨284387, by rfl⟩ : syracuseStep 379183 = 568775) B568775
theorem B1133243 : Blo 334751 1133243 := bstep (se 1 (by rfl) ⟨849932, by rfl⟩ : syracuseStep 1133243 = 1699865) B1699865
theorem B379975 : Blo 334751 379975 := bstep (se 1 (by rfl) ⟨284981, by rfl⟩ : syracuseStep 379975 = 569963) B569963
theorem B2870437 : Blo 334751 2870437 := bstep (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) B538207
theorem B478543 : Blo 334751 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B2870711 : Blo 334751 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B5459471 : Blo 334751 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B478811 : Blo 334751 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B642667 : Blo 334751 642667 := bstep (se 1 (by rfl) ⟨482000, by rfl⟩ : syracuseStep 642667 = 964001) B964001
theorem B2150063 : Blo 334751 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B3821417 : Blo 334751 3821417 := bstep (se 2 (by rfl) ⟨1433031, by rfl⟩ : syracuseStep 3821417 = 2866063) B2866063
theorem B642971 : Blo 334751 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B99438515 : Blo 334751 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B1135187 : Blo 334751 1135187 := bstep (se 1 (by rfl) ⟨851390, by rfl⟩ : syracuseStep 1135187 = 1702781) B1702781
theorem B971347 : Blo 334751 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B3854951 : Blo 334751 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B2544695 : Blo 334751 2544695 := bstep (se 1 (by rfl) ⟨1908521, by rfl⟩ : syracuseStep 2544695 = 3817043) B3817043
theorem B1135835 : Blo 334751 1135835 := bstep (se 1 (by rfl) ⟨851876, by rfl⟩ : syracuseStep 1135835 = 1703753) B1703753
theorem B480935 : Blo 334751 480935 := bstep (se 1 (by rfl) ⟨360701, by rfl⟩ : syracuseStep 480935 = 721403) B721403
theorem B907145 : Blo 334751 907145 := bstep (se 2 (by rfl) ⟨340179, by rfl⟩ : syracuseStep 907145 = 680359) B680359
theorem B808841 : Blo 334751 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B3889079 : Blo 334751 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B2414551 : Blo 334751 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B1136699 : Blo 334751 1136699 := bstep (se 1 (by rfl) ⟨852524, by rfl⟩ : syracuseStep 1136699 = 1705049) B1705049
theorem B3692639 : Blo 334751 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B1136969 : Blo 334751 1136969 := bstep (se 2 (by rfl) ⟨426363, by rfl⟩ : syracuseStep 1136969 = 852727) B852727
theorem B1367009 : Blo 334751 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B3857867 : Blo 334751 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B1138319 : Blo 334751 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B1728647 : Blo 334751 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B2908493 : Blo 334751 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B1139453 : Blo 334751 1139453 := bstep (se 3 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 1139453 = 427295) B427295
theorem B7037725 : Blo 334751 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B4678829 : Blo 334751 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1697273 : Blo 334751 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1435151 : Blo 334751 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B9791165 : Blo 334751 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1730267 : Blo 334751 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B2156291 : Blo 334751 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B2550041 : Blo 334751 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B1141559 : Blo 334751 1141559 := bstep (se 1 (by rfl) ⟨856169, by rfl⟩ : syracuseStep 1141559 = 1712339) B1712339
theorem B847655 : Blo 334751 847655 := bstep (se 1 (by rfl) ⟨635741, by rfl⟩ : syracuseStep 847655 = 1271483) B1271483
theorem B2912375 : Blo 334751 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B716987 : Blo 334751 716987 := bstep (se 1 (by rfl) ⟨537740, by rfl⟩ : syracuseStep 716987 = 1075481) B1075481
theorem B717473 : Blo 334751 717473 := bstep (se 2 (by rfl) ⟨269052, by rfl⟩ : syracuseStep 717473 = 538105) B538105
theorem B848951 : Blo 334751 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B685403 : Blo 334751 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B3077519 : Blo 334751 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B1439441 : Blo 334751 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B1701971 : Blo 334751 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B456859 : Blo 334751 456859 := bstep (se 1 (by rfl) ⟨342644, by rfl⟩ : syracuseStep 456859 = 685289) B685289
theorem B1702457 : Blo 334751 1702457 := bstep (se 2 (by rfl) ⟨638421, by rfl⟩ : syracuseStep 1702457 = 1276843) B1276843
theorem B850895 : Blo 334751 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B2915777 : Blo 334751 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B851411 : Blo 334751 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B851431 : Blo 334751 851431 := bstep (se 1 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 851431 = 1277147) B1277147
theorem B7274099 : Blo 334751 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1539769 : Blo 334751 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B753479 : Blo 334751 753479 := bstep (se 1 (by rfl) ⟨565109, by rfl⟩ : syracuseStep 753479 = 1130219) B1130219
theorem B1081259 : Blo 334751 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B2162875 : Blo 334751 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B754091 : Blo 334751 754091 := bstep (se 1 (by rfl) ⟨565568, by rfl⟩ : syracuseStep 754091 = 1131137) B1131137
theorem B2556359 : Blo 334751 2556359 := bstep (se 1 (by rfl) ⟨1917269, by rfl⟩ : syracuseStep 2556359 = 3834539) B3834539
theorem B754271 : Blo 334751 754271 := bstep (se 1 (by rfl) ⟨565703, by rfl⟩ : syracuseStep 754271 = 1131407) B1131407
theorem B1278575 : Blo 334751 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2556845 : Blo 334751 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B754631 : Blo 334751 754631 := bstep (se 1 (by rfl) ⟨565973, by rfl⟩ : syracuseStep 754631 = 1131947) B1131947
theorem B2720783 : Blo 334751 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B722155 : Blo 334751 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B754991 : Blo 334751 754991 := bstep (se 1 (by rfl) ⟨566243, by rfl⟩ : syracuseStep 754991 = 1132487) B1132487
theorem B2426375 : Blo 334751 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B853679 : Blo 334751 853679 := bstep (se 1 (by rfl) ⟨640259, by rfl⟩ : syracuseStep 853679 = 1280519) B1280519
theorem B755495 : Blo 334751 755495 := bstep (se 1 (by rfl) ⟨566621, by rfl⟩ : syracuseStep 755495 = 1133243) B1133243
theorem B1443865 : Blo 334751 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B6883379 : Blo 334751 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B755873 : Blo 334751 755873 := bstep (se 2 (by rfl) ⟨283452, by rfl⟩ : syracuseStep 755873 = 566905) B566905
theorem B3639647 : Blo 334751 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B428647 : Blo 334751 428647 := bstep (se 1 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 428647 = 642971) B642971
theorem B66292343 : Blo 334751 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B756521 : Blo 334751 756521 := bstep (se 2 (by rfl) ⟨283695, by rfl⟩ : syracuseStep 756521 = 567391) B567391
theorem B756791 : Blo 334751 756791 := bstep (se 1 (by rfl) ⟨567593, by rfl⟩ : syracuseStep 756791 = 1135187) B1135187
theorem B2559275 : Blo 334751 2559275 := bstep (se 1 (by rfl) ⟨1919456, by rfl⟩ : syracuseStep 2559275 = 3838913) B3838913
theorem B757223 : Blo 334751 757223 := bstep (se 1 (by rfl) ⟨567917, by rfl⟩ : syracuseStep 757223 = 1135835) B1135835
theorem B2592719 : Blo 334751 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B757799 : Blo 334751 757799 := bstep (se 1 (by rfl) ⟨568349, by rfl⟩ : syracuseStep 757799 = 1136699) B1136699
theorem B2461759 : Blo 334751 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B757979 : Blo 334751 757979 := bstep (se 1 (by rfl) ⟨568484, by rfl⟩ : syracuseStep 757979 = 1136969) B1136969
theorem B2887933 : Blo 334751 2887933 := bstep (se 3 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 2887933 = 1082975) B1082975
theorem B1282493 : Blo 334751 1282493 := bstep (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) B480935
theorem B3248585 : Blo 334751 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B758249 : Blo 334751 758249 := bstep (se 2 (by rfl) ⟨284343, by rfl⟩ : syracuseStep 758249 = 568687) B568687
theorem B856889 : Blo 334751 856889 := bstep (se 2 (by rfl) ⟨321333, by rfl⟩ : syracuseStep 856889 = 642667) B642667
theorem B758753 : Blo 334751 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B758879 : Blo 334751 758879 := bstep (se 1 (by rfl) ⟨569159, by rfl⟩ : syracuseStep 758879 = 1138319) B1138319
theorem B1971611 : Blo 334751 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1152431 : Blo 334751 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1938995 : Blo 334751 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B759635 : Blo 334751 759635 := bstep (se 1 (by rfl) ⟨569726, by rfl⟩ : syracuseStep 759635 = 1139453) B1139453
theorem B3119219 : Blo 334751 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1710233 : Blo 334751 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B760121 : Blo 334751 760121 := bstep (se 2 (by rfl) ⟨285045, by rfl⟩ : syracuseStep 760121 = 570091) B570091
theorem B956767 : Blo 334751 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B1153511 : Blo 334751 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B334759 : Blo 334751 334759 := bstep (se 1 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 334759 = 502139) B502139
theorem B1711043 : Blo 334751 1711043 := bstep (se 1 (by rfl) ⟨1283282, by rfl⟩ : syracuseStep 1711043 = 2566565) B2566565
theorem B334939 : Blo 334751 334939 := bstep (se 1 (by rfl) ⟨251204, by rfl⟩ : syracuseStep 334939 = 502409) B502409
theorem B335055 : Blo 334751 335055 := bstep (se 1 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 335055 = 502583) B502583
theorem B761039 : Blo 334751 761039 := bstep (se 1 (by rfl) ⟨570779, by rfl⟩ : syracuseStep 761039 = 1141559) B1141559
theorem B335079 : Blo 334751 335079 := bstep (se 1 (by rfl) ⟨251309, by rfl⟩ : syracuseStep 335079 = 502619) B502619
theorem B335175 : Blo 334751 335175 := bstep (se 1 (by rfl) ⟨251381, by rfl⟩ : syracuseStep 335175 = 502763) B502763
theorem B335311 : Blo 334751 335311 := bstep (se 1 (by rfl) ⟨251483, by rfl⟩ : syracuseStep 335311 = 502967) B502967
theorem B761417 : Blo 334751 761417 := bstep (se 2 (by rfl) ⟨285531, by rfl⟩ : syracuseStep 761417 = 571063) B571063
theorem B335471 : Blo 334751 335471 := bstep (se 1 (by rfl) ⟨251603, by rfl⟩ : syracuseStep 335471 = 503207) B503207
theorem B335527 : Blo 334751 335527 := bstep (se 1 (by rfl) ⟨251645, by rfl⟩ : syracuseStep 335527 = 503291) B503291
theorem B335591 : Blo 334751 335591 := bstep (se 1 (by rfl) ⟨251693, by rfl⟩ : syracuseStep 335591 = 503387) B503387
theorem B1285865 : Blo 334751 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B335647 : Blo 334751 335647 := bstep (se 1 (by rfl) ⟨251735, by rfl⟩ : syracuseStep 335647 = 503471) B503471
theorem B565103 : Blo 334751 565103 := bstep (se 1 (by rfl) ⟨423827, by rfl⟩ : syracuseStep 565103 = 847655) B847655
theorem B335727 : Blo 334751 335727 := bstep (se 1 (by rfl) ⟨251795, by rfl⟩ : syracuseStep 335727 = 503591) B503591
theorem B335783 : Blo 334751 335783 := bstep (se 1 (by rfl) ⟨251837, by rfl⟩ : syracuseStep 335783 = 503675) B503675
theorem B3219401 : Blo 334751 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B1941583 : Blo 334751 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B336063 : Blo 334751 336063 := bstep (se 1 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 336063 = 504095) B504095
theorem B336079 : Blo 334751 336079 := bstep (se 1 (by rfl) ⟨252059, by rfl⟩ : syracuseStep 336079 = 504119) B504119
theorem B336127 : Blo 334751 336127 := bstep (se 1 (by rfl) ⟨252095, by rfl⟩ : syracuseStep 336127 = 504191) B504191
theorem B336175 : Blo 334751 336175 := bstep (se 1 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 336175 = 504263) B504263
theorem B1024505 : Blo 334751 1024505 := bstep (se 2 (by rfl) ⟨384189, by rfl⟩ : syracuseStep 1024505 = 768379) B768379
theorem B2892307 : Blo 334751 2892307 := bstep (se 1 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 2892307 = 4338461) B4338461
theorem B336411 : Blo 334751 336411 := bstep (se 1 (by rfl) ⟨252308, by rfl⟩ : syracuseStep 336411 = 504617) B504617
theorem B336415 : Blo 334751 336415 := bstep (se 1 (by rfl) ⟨252311, by rfl⟩ : syracuseStep 336415 = 504623) B504623
theorem B336495 : Blo 334751 336495 := bstep (se 1 (by rfl) ⟨252371, by rfl⟩ : syracuseStep 336495 = 504743) B504743
theorem B336551 : Blo 334751 336551 := bstep (se 1 (by rfl) ⟨252413, by rfl⟩ : syracuseStep 336551 = 504827) B504827
theorem B565967 : Blo 334751 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B336591 : Blo 334751 336591 := bstep (se 1 (by rfl) ⟨252443, by rfl⟩ : syracuseStep 336591 = 504887) B504887
theorem B336671 : Blo 334751 336671 := bstep (se 1 (by rfl) ⟨252503, by rfl⟩ : syracuseStep 336671 = 505007) B505007
theorem B4596527 : Blo 334751 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B2565107 : Blo 334751 2565107 := bstep (se 1 (by rfl) ⟨1923830, by rfl⟩ : syracuseStep 2565107 = 3847661) B3847661
theorem B336943 : Blo 334751 336943 := bstep (se 1 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 336943 = 505415) B505415
theorem B337007 : Blo 334751 337007 := bstep (se 1 (by rfl) ⟨252755, by rfl⟩ : syracuseStep 337007 = 505511) B505511
theorem B959627 : Blo 334751 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B337063 : Blo 334751 337063 := bstep (se 1 (by rfl) ⟨252797, by rfl⟩ : syracuseStep 337063 = 505595) B505595
theorem B337087 : Blo 334751 337087 := bstep (se 1 (by rfl) ⟨252815, by rfl⟩ : syracuseStep 337087 = 505631) B505631
theorem B337119 : Blo 334751 337119 := bstep (se 1 (by rfl) ⟨252839, by rfl⟩ : syracuseStep 337119 = 505679) B505679
theorem B337199 : Blo 334751 337199 := bstep (se 1 (by rfl) ⟨252899, by rfl⟩ : syracuseStep 337199 = 505799) B505799
theorem B337435 : Blo 334751 337435 := bstep (se 1 (by rfl) ⟨253076, by rfl⟩ : syracuseStep 337435 = 506153) B506153
theorem B337439 : Blo 334751 337439 := bstep (se 1 (by rfl) ⟨253079, by rfl⟩ : syracuseStep 337439 = 506159) B506159
theorem B337599 : Blo 334751 337599 := bstep (se 1 (by rfl) ⟨253199, by rfl⟩ : syracuseStep 337599 = 506399) B506399
theorem B862015 : Blo 334751 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B337855 : Blo 334751 337855 := bstep (se 1 (by rfl) ⟨253391, by rfl⟩ : syracuseStep 337855 = 506783) B506783
theorem B567263 : Blo 334751 567263 := bstep (se 1 (by rfl) ⟨425447, by rfl⟩ : syracuseStep 567263 = 850895) B850895
theorem B337887 : Blo 334751 337887 := bstep (se 1 (by rfl) ⟨253415, by rfl⟩ : syracuseStep 337887 = 506831) B506831
theorem B403483 : Blo 334751 403483 := bstep (se 1 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 403483 = 605225) B605225
theorem B337947 : Blo 334751 337947 := bstep (se 1 (by rfl) ⟨253460, by rfl⟩ : syracuseStep 337947 = 506921) B506921
theorem B337951 : Blo 334751 337951 := bstep (se 1 (by rfl) ⟨253463, by rfl⟩ : syracuseStep 337951 = 506927) B506927
theorem B337967 : Blo 334751 337967 := bstep (se 1 (by rfl) ⟨253475, by rfl⟩ : syracuseStep 337967 = 506951) B506951
theorem B6498467 : Blo 334751 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B338143 : Blo 334751 338143 := bstep (se 1 (by rfl) ⟨253607, by rfl⟩ : syracuseStep 338143 = 507215) B507215
theorem B338203 : Blo 334751 338203 := bstep (se 1 (by rfl) ⟨253652, by rfl⟩ : syracuseStep 338203 = 507305) B507305
theorem B1943851 : Blo 334751 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B567607 : Blo 334751 567607 := bstep (se 1 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 567607 = 851411) B851411
theorem B338303 : Blo 334751 338303 := bstep (se 1 (by rfl) ⟨253727, by rfl⟩ : syracuseStep 338303 = 507455) B507455
theorem B502265 : Blo 334751 502265 := bstep (se 2 (by rfl) ⟨188349, by rfl⟩ : syracuseStep 502265 = 376699) B376699
theorem B502319 : Blo 334751 502319 := bstep (se 1 (by rfl) ⟨376739, by rfl⟩ : syracuseStep 502319 = 753479) B753479
theorem B338479 : Blo 334751 338479 := bstep (se 1 (by rfl) ⟨253859, by rfl⟩ : syracuseStep 338479 = 507719) B507719
theorem B1714769 : Blo 334751 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B338535 : Blo 334751 338535 := bstep (se 1 (by rfl) ⟨253901, by rfl⟩ : syracuseStep 338535 = 507803) B507803
theorem B502751 : Blo 334751 502751 := bstep (se 1 (by rfl) ⟨377063, by rfl⟩ : syracuseStep 502751 = 754127) B754127
theorem B1289465 : Blo 334751 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B1944911 : Blo 334751 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B503195 : Blo 334751 503195 := bstep (se 1 (by rfl) ⟨377396, by rfl⟩ : syracuseStep 503195 = 754793) B754793
theorem B1256887 : Blo 334751 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B2436581 : Blo 334751 2436581 := bstep (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) B456859
theorem B1027591 : Blo 334751 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B568903 : Blo 334751 568903 := bstep (se 1 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 568903 = 853355) B853355
theorem B9383633 : Blo 334751 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B4599595 : Blo 334751 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B503615 : Blo 334751 503615 := bstep (se 1 (by rfl) ⟨377711, by rfl⟩ : syracuseStep 503615 = 755423) B755423
theorem B503801 : Blo 334751 503801 := bstep (se 2 (by rfl) ⟨188925, by rfl⟩ : syracuseStep 503801 = 377851) B377851
theorem B4108519 : Blo 334751 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B504041 : Blo 334751 504041 := bstep (se 2 (by rfl) ⟨189015, by rfl⟩ : syracuseStep 504041 = 378031) B378031
theorem B1028371 : Blo 334751 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B504167 : Blo 334751 504167 := bstep (se 1 (by rfl) ⟨378125, by rfl⟩ : syracuseStep 504167 = 756251) B756251
theorem B962999 : Blo 334751 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B2863673 : Blo 334751 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B8172089 : Blo 334751 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B635627 : Blo 334751 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B504713 : Blo 334751 504713 := bstep (se 2 (by rfl) ⟨189267, by rfl⟩ : syracuseStep 504713 = 378535) B378535
theorem B1913807 : Blo 334751 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B570361 : Blo 334751 570361 := bstep (se 2 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 570361 = 427771) B427771
theorem B636167 : Blo 334751 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B570631 : Blo 334751 570631 := bstep (se 1 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 570631 = 855947) B855947
theorem B505097 : Blo 334751 505097 := bstep (se 2 (by rfl) ⟨189411, by rfl⟩ : syracuseStep 505097 = 378823) B378823
theorem B505151 : Blo 334751 505151 := bstep (se 1 (by rfl) ⟨378863, by rfl⟩ : syracuseStep 505151 = 757727) B757727
theorem B41268689 : Blo 334751 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B505577 : Blo 334751 505577 := bstep (se 2 (by rfl) ⟨189591, by rfl⟩ : syracuseStep 505577 = 379183) B379183
theorem B505583 : Blo 334751 505583 := bstep (se 1 (by rfl) ⟨379187, by rfl⟩ : syracuseStep 505583 = 758375) B758375
theorem B2569967 : Blo 334751 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B636751 : Blo 334751 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B964649 : Blo 334751 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B506039 : Blo 334751 506039 := bstep (se 1 (by rfl) ⟨379529, by rfl⟩ : syracuseStep 506039 = 759059) B759059
theorem B506087 : Blo 334751 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B604763 : Blo 334751 604763 := bstep (se 1 (by rfl) ⟨453572, by rfl⟩ : syracuseStep 604763 = 907145) B907145
theorem B539227 : Blo 334751 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B506459 : Blo 334751 506459 := bstep (se 1 (by rfl) ⟨379844, by rfl⟩ : syracuseStep 506459 = 759689) B759689
theorem B506603 : Blo 334751 506603 := bstep (se 1 (by rfl) ⟨379952, by rfl⟩ : syracuseStep 506603 = 759905) B759905
theorem B506633 : Blo 334751 506633 := bstep (se 2 (by rfl) ⟨189987, by rfl⟩ : syracuseStep 506633 = 379975) B379975
theorem B638057 : Blo 334751 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B1621235 : Blo 334751 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2080079 : Blo 334751 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B507503 : Blo 334751 507503 := bstep (se 1 (by rfl) ⟨380627, by rfl⟩ : syracuseStep 507503 = 761255) B761255
theorem B2571911 : Blo 334751 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B7126751 : Blo 334751 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B638695 : Blo 334751 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B507623 : Blo 334751 507623 := bstep (se 1 (by rfl) ⟨380717, by rfl⟩ : syracuseStep 507623 = 761435) B761435
theorem B540425 : Blo 334751 540425 := bstep (se 2 (by rfl) ⟨202659, by rfl⟩ : syracuseStep 540425 = 405319) B405319
theorem B507815 : Blo 334751 507815 := bstep (se 1 (by rfl) ⟨380861, by rfl⟩ : syracuseStep 507815 = 761723) B761723
theorem B377023 : Blo 334751 377023 := bstep (se 1 (by rfl) ⟨282767, by rfl⟩ : syracuseStep 377023 = 565535) B565535
theorem B377455 : Blo 334751 377455 := bstep (se 1 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 377455 = 566183) B566183
theorem B377563 : Blo 334751 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B2081555 : Blo 334751 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B1295129 : Blo 334751 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B2868047 : Blo 334751 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1131515 : Blo 334751 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B967735 : Blo 334751 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B640055 : Blo 334751 640055 := bstep (se 1 (by rfl) ⟨480041, by rfl⟩ : syracuseStep 640055 = 960083) B960083
theorem B23250199 : Blo 334751 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B11717399 : Blo 334751 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B477991 : Blo 334751 477991 := bstep (se 1 (by rfl) ⟨358493, by rfl⟩ : syracuseStep 477991 = 716987) B716987
theorem B379687 : Blo 334751 379687 := bstep (se 1 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 379687 = 569531) B569531
theorem B4115387 : Blo 334751 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B8702963 : Blo 334751 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B478315 : Blo 334751 478315 := bstep (se 1 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 478315 = 717473) B717473
theorem B642431 : Blo 334751 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B642887 : Blo 334751 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B1822591 : Blo 334751 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B380911 : Blo 334751 380911 := bstep (se 1 (by rfl) ⟨285683, by rfl⟩ : syracuseStep 380911 = 571367) B571367
theorem B1134647 : Blo 334751 1134647 := bstep (se 1 (by rfl) ⟨850985, by rfl⟩ : syracuseStep 1134647 = 1701971) B1701971
theorem B577631 : Blo 334751 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B381055 : Blo 334751 381055 := bstep (se 1 (by rfl) ⟨285791, by rfl⟩ : syracuseStep 381055 = 571583) B571583
theorem B1134971 : Blo 334751 1134971 := bstep (se 1 (by rfl) ⟨851228, by rfl⟩ : syracuseStep 1134971 = 1702457) B1702457
theorem B1135241 : Blo 334751 1135241 := bstep (se 2 (by rfl) ⟨425715, by rfl⟩ : syracuseStep 1135241 = 851431) B851431
theorem B2053025 : Blo 334751 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B1627231 : Blo 334751 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B1464155 : Blo 334751 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B94197917 : Blo 334751 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B2546153 : Blo 334751 2546153 := bstep (se 2 (by rfl) ⟨954807, by rfl⟩ : syracuseStep 2546153 = 1909615) B1909615
theorem B3890663 : Blo 334751 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B4218493 : Blo 334751 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B1433375 : Blo 334751 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B2547611 : Blo 334751 2547611 := bstep (se 1 (by rfl) ⟨1910708, by rfl⟩ : syracuseStep 2547611 = 3821417) B3821417
theorem B1696463 : Blo 334751 1696463 := bstep (se 1 (by rfl) ⟨1272347, by rfl⟩ : syracuseStep 1696463 = 2544695) B2544695
theorem B32826869 : Blo 334751 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1271315 : Blo 334751 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B3827249 : Blo 334751 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B1697597 : Blo 334751 1697597 := bstep (se 3 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 1697597 = 636599) B636599
theorem B26109773 : Blo 334751 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1927111 : Blo 334751 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B1271771 : Blo 334751 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B911339 : Blo 334751 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B1271801 : Blo 334751 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B813559 : Blo 334751 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B1076107 : Blo 334751 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B9235633 : Blo 334751 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B1535257 : Blo 334751 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1142045 : Blo 334751 1142045 := bstep (se 3 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 1142045 = 428267) B428267
theorem B1437527 : Blo 334751 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B1142747 : Blo 334751 1142747 := bstep (se 1 (by rfl) ⟨857060, by rfl⟩ : syracuseStep 1142747 = 1714121) B1714121
theorem B1732751 : Blo 334751 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B1700027 : Blo 334751 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B12415169 : Blo 334751 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1143017 : Blo 334751 1143017 := bstep (se 2 (by rfl) ⟨428631, by rfl⟩ : syracuseStep 1143017 = 857263) B857263
theorem B1209815 : Blo 334751 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B1275659 : Blo 334751 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B456935 : Blo 334751 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B1440413 : Blo 334751 1440413 := bstep (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) B540155
theorem B1276829 : Blo 334751 1276829 := bstep (se 3 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 1276829 = 478811) B478811
theorem B1146079 : Blo 334751 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B753263 : Blo 334751 753263 := bstep (se 1 (by rfl) ⟨564947, by rfl⟩ : syracuseStep 753263 = 1129895) B1129895
theorem B4849399 : Blo 334751 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B753551 : Blo 334751 753551 := bstep (se 1 (by rfl) ⟨565163, by rfl⟩ : syracuseStep 753551 = 1130327) B1130327
theorem B720839 : Blo 334751 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B2588777 : Blo 334751 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B21921941 : Blo 334751 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B2883833 : Blo 334751 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1540349 : Blo 334751 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B1704239 : Blo 334751 1704239 := bstep (se 1 (by rfl) ⟨1278179, by rfl⟩ : syracuseStep 1704239 = 2556359) B2556359
theorem B852383 : Blo 334751 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1704563 : Blo 334751 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B754343 : Blo 334751 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B426703 : Blo 334751 426703 := bstep (se 1 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 426703 = 640055) B640055
theorem B4588919 : Blo 334751 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B2426431 : Blo 334751 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B31000265 : Blo 334751 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B5801975 : Blo 334751 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B12257405 : Blo 334751 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B1706183 : Blo 334751 1706183 := bstep (se 1 (by rfl) ⟨1279637, by rfl⟩ : syracuseStep 1706183 = 2559275) B2559275
theorem B1149353 : Blo 334751 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B428591 : Blo 334751 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B756431 : Blo 334751 756431 := bstep (se 1 (by rfl) ⟨567323, by rfl⟩ : syracuseStep 756431 = 1134647) B1134647
theorem B756647 : Blo 334751 756647 := bstep (se 1 (by rfl) ⟨567485, by rfl⟩ : syracuseStep 756647 = 1134971) B1134971
theorem B854995 : Blo 334751 854995 := bstep (se 1 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 854995 = 1282493) B1282493
theorem B2165723 : Blo 334751 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B2591801 : Blo 334751 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B756809 : Blo 334751 756809 := bstep (se 2 (by rfl) ⟨283803, by rfl⟩ : syracuseStep 756809 = 567607) B567607
theorem B756827 : Blo 334751 756827 := bstep (se 1 (by rfl) ⟨567620, by rfl⟩ : syracuseStep 756827 = 1135241) B1135241
theorem B1084745 : Blo 334751 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B1314407 : Blo 334751 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B758537 : Blo 334751 758537 := bstep (se 2 (by rfl) ⟨284451, by rfl⟩ : syracuseStep 758537 = 568903) B568903
theorem B2593775 : Blo 334751 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B6132793 : Blo 334751 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B857243 : Blo 334751 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B955583 : Blo 334751 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B5478025 : Blo 334751 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B1218493 : Blo 334751 1218493 := bstep (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) B456935
theorem B1710071 : Blo 334751 1710071 := bstep (se 1 (by rfl) ⟨1282553, by rfl⟩ : syracuseStep 1710071 = 2565107) B2565107
theorem B17406515 : Blo 334751 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B760481 : Blo 334751 760481 := bstep (se 2 (by rfl) ⟨285180, by rfl⟩ : syracuseStep 760481 = 570361) B570361
theorem B4332311 : Blo 334751 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B2169641 : Blo 334751 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B334843 : Blo 334751 334843 := bstep (se 1 (by rfl) ⟨251132, by rfl⟩ : syracuseStep 334843 = 502265) B502265
theorem B760841 : Blo 334751 760841 := bstep (se 2 (by rfl) ⟨285315, by rfl⟩ : syracuseStep 760841 = 570631) B570631
theorem B334879 : Blo 334751 334879 := bstep (se 1 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 334879 = 502319) B502319
theorem B335167 : Blo 334751 335167 := bstep (se 1 (by rfl) ⟨251375, by rfl⟩ : syracuseStep 335167 = 502751) B502751
theorem B859643 : Blo 334751 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B761363 : Blo 334751 761363 := bstep (se 1 (by rfl) ⟨571022, by rfl⟩ : syracuseStep 761363 = 1142045) B1142045
theorem B335463 : Blo 334751 335463 := bstep (se 1 (by rfl) ⟨251597, by rfl⟩ : syracuseStep 335463 = 503195) B503195
theorem B335743 : Blo 334751 335743 := bstep (se 1 (by rfl) ⟨251807, by rfl⟩ : syracuseStep 335743 = 503615) B503615
theorem B958351 : Blo 334751 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B761831 : Blo 334751 761831 := bstep (se 1 (by rfl) ⟨571373, by rfl⟩ : syracuseStep 761831 = 1142747) B1142747
theorem B335867 : Blo 334751 335867 := bstep (se 1 (by rfl) ⟨251900, by rfl⟩ : syracuseStep 335867 = 503801) B503801
theorem B1155167 : Blo 334751 1155167 := bstep (se 1 (by rfl) ⟨866375, by rfl⟩ : syracuseStep 1155167 = 1732751) B1732751
theorem B336027 : Blo 334751 336027 := bstep (se 1 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 336027 = 504041) B504041
theorem B762011 : Blo 334751 762011 := bstep (se 1 (by rfl) ⟨571508, by rfl⟩ : syracuseStep 762011 = 1143017) B1143017
theorem B336111 : Blo 334751 336111 := bstep (se 1 (by rfl) ⟨252083, by rfl⟩ : syracuseStep 336111 = 504167) B504167
theorem B1909115 : Blo 334751 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B5448059 : Blo 334751 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B336475 : Blo 334751 336475 := bstep (se 1 (by rfl) ⟨252356, by rfl⟩ : syracuseStep 336475 = 504713) B504713
theorem B336731 : Blo 334751 336731 := bstep (se 1 (by rfl) ⟨252548, by rfl⟩ : syracuseStep 336731 = 505097) B505097
theorem B336767 : Blo 334751 336767 := bstep (se 1 (by rfl) ⟨252575, by rfl⟩ : syracuseStep 336767 = 505151) B505151
theorem B1713149 : Blo 334751 1713149 := bstep (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) B642431
theorem B337051 : Blo 334751 337051 := bstep (se 1 (by rfl) ⟨252788, by rfl⟩ : syracuseStep 337051 = 505577) B505577
theorem B337055 : Blo 334751 337055 := bstep (se 1 (by rfl) ⟨252791, by rfl⟩ : syracuseStep 337055 = 505583) B505583
theorem B1713311 : Blo 334751 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B337359 : Blo 334751 337359 := bstep (se 1 (by rfl) ⟨253019, by rfl⟩ : syracuseStep 337359 = 506039) B506039
theorem B337391 : Blo 334751 337391 := bstep (se 1 (by rfl) ⟨253043, by rfl⟩ : syracuseStep 337391 = 506087) B506087
theorem B403175 : Blo 334751 403175 := bstep (se 1 (by rfl) ⟨302381, by rfl⟩ : syracuseStep 403175 = 604763) B604763
theorem B337639 : Blo 334751 337639 := bstep (se 1 (by rfl) ⟨253229, by rfl⟩ : syracuseStep 337639 = 506459) B506459
theorem B960275 : Blo 334751 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B337735 : Blo 334751 337735 := bstep (se 1 (by rfl) ⟨253301, by rfl⟩ : syracuseStep 337735 = 506603) B506603
theorem B337755 : Blo 334751 337755 := bstep (se 1 (by rfl) ⟨253316, by rfl⟩ : syracuseStep 337755 = 506633) B506633
theorem B1386719 : Blo 334751 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B6465865 : Blo 334751 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B502175 : Blo 334751 502175 := bstep (se 1 (by rfl) ⟨376631, by rfl⟩ : syracuseStep 502175 = 753263) B753263
theorem B338335 : Blo 334751 338335 := bstep (se 1 (by rfl) ⟨253751, by rfl⟩ : syracuseStep 338335 = 507503) B507503
theorem B1714607 : Blo 334751 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B338415 : Blo 334751 338415 := bstep (se 1 (by rfl) ⟨253811, by rfl⟩ : syracuseStep 338415 = 507623) B507623
theorem B502367 : Blo 334751 502367 := bstep (se 1 (by rfl) ⟨376775, by rfl⟩ : syracuseStep 502367 = 753551) B753551
theorem B338543 : Blo 334751 338543 := bstep (se 1 (by rfl) ⟨253907, by rfl⟩ : syracuseStep 338543 = 507815) B507815
theorem B502697 : Blo 334751 502697 := bstep (se 2 (by rfl) ⟨188511, by rfl⟩ : syracuseStep 502697 = 377023) B377023
theorem B502727 : Blo 334751 502727 := bstep (se 1 (by rfl) ⟨377045, by rfl⟩ : syracuseStep 502727 = 754091) B754091
theorem B502847 : Blo 334751 502847 := bstep (se 1 (by rfl) ⟨377135, by rfl⟩ : syracuseStep 502847 = 754271) B754271
theorem B1387703 : Blo 334751 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B863419 : Blo 334751 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B1912031 : Blo 334751 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B503087 : Blo 334751 503087 := bstep (se 1 (by rfl) ⟨377315, by rfl⟩ : syracuseStep 503087 = 754631) B754631
theorem B1813855 : Blo 334751 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B503273 : Blo 334751 503273 := bstep (se 2 (by rfl) ⟨188727, by rfl⟩ : syracuseStep 503273 = 377455) B377455
theorem B503327 : Blo 334751 503327 := bstep (se 1 (by rfl) ⟨377495, by rfl⟩ : syracuseStep 503327 = 754991) B754991
theorem B503417 : Blo 334751 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B1617583 : Blo 334751 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B569119 : Blo 334751 569119 := bstep (se 1 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 569119 = 853679) B853679
theorem B503663 : Blo 334751 503663 := bstep (se 1 (by rfl) ⟨377747, by rfl⟩ : syracuseStep 503663 = 755495) B755495
theorem B1290313 : Blo 334751 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B503915 : Blo 334751 503915 := bstep (se 1 (by rfl) ⟨377936, by rfl⟩ : syracuseStep 503915 = 755873) B755873
theorem B962873 : Blo 334751 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B7811599 : Blo 334751 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B504347 : Blo 334751 504347 := bstep (se 1 (by rfl) ⟨378260, by rfl⟩ : syracuseStep 504347 = 756521) B756521
theorem B504527 : Blo 334751 504527 := bstep (se 1 (by rfl) ⟨378395, by rfl⟩ : syracuseStep 504527 = 756791) B756791
theorem B504815 : Blo 334751 504815 := bstep (se 1 (by rfl) ⟨378611, by rfl⟩ : syracuseStep 504815 = 757223) B757223
theorem B2569481 : Blo 334751 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B505199 : Blo 334751 505199 := bstep (se 1 (by rfl) ⟨378899, by rfl⟩ : syracuseStep 505199 = 757799) B757799
theorem B537977 : Blo 334751 537977 := bstep (se 2 (by rfl) ⟨201741, by rfl⟩ : syracuseStep 537977 = 403483) B403483
theorem B505319 : Blo 334751 505319 := bstep (se 1 (by rfl) ⟨378989, by rfl⟩ : syracuseStep 505319 = 757979) B757979
theorem B505499 : Blo 334751 505499 := bstep (se 1 (by rfl) ⟨379124, by rfl⟩ : syracuseStep 505499 = 758249) B758249
theorem B571259 : Blo 334751 571259 := bstep (se 1 (by rfl) ⟨428444, by rfl⟩ : syracuseStep 571259 = 856889) B856889
theorem B505835 : Blo 334751 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B505919 : Blo 334751 505919 := bstep (se 1 (by rfl) ⟨379439, by rfl⟩ : syracuseStep 505919 = 758879) B758879
theorem B571529 : Blo 334751 571529 := bstep (se 2 (by rfl) ⟨214323, by rfl⟩ : syracuseStep 571529 = 428647) B428647
theorem B768287 : Blo 334751 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B1292663 : Blo 334751 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B637321 : Blo 334751 637321 := bstep (se 2 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 637321 = 477991) B477991
theorem B506249 : Blo 334751 506249 := bstep (se 2 (by rfl) ⟨189843, by rfl⟩ : syracuseStep 506249 = 379687) B379687
theorem B506423 : Blo 334751 506423 := bstep (se 1 (by rfl) ⟨379817, by rfl⟩ : syracuseStep 506423 = 759635) B759635
theorem B2079479 : Blo 334751 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B62798611 : Blo 334751 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B506747 : Blo 334751 506747 := bstep (se 1 (by rfl) ⟨380060, by rfl⟩ : syracuseStep 506747 = 760121) B760121
theorem B769007 : Blo 334751 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B507359 : Blo 334751 507359 := bstep (se 1 (by rfl) ⟨380519, by rfl⟩ : syracuseStep 507359 = 761039) B761039
theorem B507611 : Blo 334751 507611 := bstep (se 1 (by rfl) ⟨380708, by rfl⟩ : syracuseStep 507611 = 761417) B761417
theorem B376735 : Blo 334751 376735 := bstep (se 1 (by rfl) ⟨282551, by rfl⟩ : syracuseStep 376735 = 565103) B565103
theorem B2146267 : Blo 334751 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B507881 : Blo 334751 507881 := bstep (se 2 (by rfl) ⟨190455, by rfl⟩ : syracuseStep 507881 = 380911) B380911
theorem B2572397 : Blo 334751 2572397 := bstep (se 3 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 2572397 = 964649) B964649
theorem B508073 : Blo 334751 508073 := bstep (se 2 (by rfl) ⟨190527, by rfl⟩ : syracuseStep 508073 = 381055) B381055
theorem B3850577 : Blo 334751 3850577 := bstep (se 2 (by rfl) ⟨1443966, by rfl⟩ : syracuseStep 3850577 = 2887933) B2887933
theorem B1130975 : Blo 334751 1130975 := bstep (se 1 (by rfl) ⟨848231, by rfl⟩ : syracuseStep 1130975 = 1696463) B1696463
theorem B377311 : Blo 334751 377311 := bstep (se 1 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 377311 = 565967) B565967
theorem B639751 : Blo 334751 639751 := bstep (se 1 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 639751 = 959627) B959627
theorem B6112421 : Blo 334751 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B1131731 : Blo 334751 1131731 := bstep (se 1 (by rfl) ⟨848798, by rfl⟩ : syracuseStep 1131731 = 1697597) B1697597
theorem B378175 : Blo 334751 378175 := bstep (se 1 (by rfl) ⟨283631, by rfl⟩ : syracuseStep 378175 = 567263) B567263
theorem B607559 : Blo 334751 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B1296607 : Blo 334751 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B6703397 : Blo 334751 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1624387 : Blo 334751 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B1133351 : Blo 334751 1133351 := bstep (se 1 (by rfl) ⟨850013, by rfl⟩ : syracuseStep 1133351 = 1700027) B1700027
theorem B8276779 : Blo 334751 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B641999 : Blo 334751 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B27512459 : Blo 334751 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B806543 : Blo 334751 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B9720485 : Blo 334751 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B5624657 : Blo 334751 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1922237 : Blo 334751 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B13129381 : Blo 334751 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B3856409 : Blo 334751 3856409 := bstep (se 2 (by rfl) ⟨1446153, by rfl⟩ : syracuseStep 3856409 = 2892307) B2892307
theorem B44194895 : Blo 334751 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B1695005 : Blo 334751 1695005 := bstep (se 3 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 1695005 = 635627) B635627
theorem B2743591 : Blo 334751 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B1728479 : Blo 334751 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1925153 : Blo 334751 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1368683 : Blo 334751 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B1434809 : Blo 334751 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B976103 : Blo 334751 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B1140155 : Blo 334751 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B12314177 : Blo 334751 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B1697435 : Blo 334751 1697435 := bstep (se 1 (by rfl) ⟨1273076, by rfl⟩ : syracuseStep 1697435 = 2546153) B2546153
theorem B1140695 : Blo 334751 1140695 := bstep (se 1 (by rfl) ⟨855521, by rfl⟩ : syracuseStep 1140695 = 1711043) B1711043
theorem B1698407 : Blo 334751 1698407 := bstep (se 1 (by rfl) ⟨1273805, by rfl⟩ : syracuseStep 1698407 = 2547611) B2547611
theorem B683003 : Blo 334751 683003 := bstep (se 1 (by rfl) ⟨512252, by rfl⟩ : syracuseStep 683003 = 1024505) B1024505
theorem B1371161 : Blo 334751 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B2551013 : Blo 334751 2551013 := bstep (se 4 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 2551013 = 478315) B478315
theorem B21884579 : Blo 334751 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B847543 : Blo 334751 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B2551499 : Blo 334751 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B847847 : Blo 334751 847847 := bstep (se 1 (by rfl) ⟨635885, by rfl⟩ : syracuseStep 847847 = 1271771) B1271771
theorem B847867 : Blo 334751 847867 := bstep (se 1 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 847867 = 1271801) B1271801
theorem B8188037 : Blo 334751 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B1143179 : Blo 334751 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B849001 : Blo 334751 849001 := bstep (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) B636751
theorem B6255755 : Blo 334751 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B1701485 : Blo 334751 1701485 := bstep (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) B638057
theorem B1275689 : Blo 334751 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B1275871 : Blo 334751 1275871 := bstep (se 1 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 1275871 = 1913807) B1913807
theorem B718969 : Blo 334751 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B424111 : Blo 334751 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B850439 : Blo 334751 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B19004669 : Blo 334751 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B851219 : Blo 334751 851219 := bstep (se 1 (by rfl) ⟨638414, by rfl⟩ : syracuseStep 851219 = 1276829) B1276829
theorem B1080823 : Blo 334751 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B851593 : Blo 334751 851593 := bstep (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) B638695
theorem B360283 : Blo 334751 360283 := bstep (se 1 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 360283 = 540425) B540425
theorem B14614627 : Blo 334751 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B753983 : Blo 334751 753983 := bstep (se 1 (by rfl) ⟨565487, by rfl⟩ : syracuseStep 753983 = 1130975) B1130975
theorem B6881669 : Blo 334751 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B754487 : Blo 334751 754487 := bstep (se 1 (by rfl) ⟨565865, by rfl⟩ : syracuseStep 754487 = 1131731) B1131731
theorem B853001 : Blo 334751 853001 := bstep (se 2 (by rfl) ⟨319875, by rfl⟩ : syracuseStep 853001 = 639751) B639751
theorem B3867983 : Blo 334751 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B755567 : Blo 334751 755567 := bstep (se 1 (by rfl) ⟨566675, by rfl⟩ : syracuseStep 755567 = 1133351) B1133351
theorem B427999 : Blo 334751 427999 := bstep (se 1 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 427999 = 641999) B641999
theorem B1443815 : Blo 334751 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B723163 : Blo 334751 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B2165849 : Blo 334751 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B8621153 : Blo 334751 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B1281491 : Blo 334751 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B1151225 : Blo 334751 1151225 := bstep (se 2 (by rfl) ⟨431709, by rfl⟩ : syracuseStep 1151225 = 863419) B863419
theorem B11604343 : Blo 334751 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B2888207 : Blo 334751 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B1446427 : Blo 334751 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B2560733 : Blo 334751 2560733 := bstep (se 3 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 2560733 = 960275) B960275
theorem B29463263 : Blo 334751 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B758825 : Blo 334751 758825 := bstep (se 2 (by rfl) ⟨284559, by rfl⟩ : syracuseStep 758825 = 569119) B569119
theorem B1152319 : Blo 334751 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B1283435 : Blo 334751 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B956539 : Blo 334751 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B760103 : Blo 334751 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B3447101 : Blo 334751 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B760463 : Blo 334751 760463 := bstep (se 1 (by rfl) ⟨570347, by rfl⟩ : syracuseStep 760463 = 1140695) B1140695
theorem B924479 : Blo 334751 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B334783 : Blo 334751 334783 := bstep (se 1 (by rfl) ⟨251087, by rfl⟩ : syracuseStep 334783 = 502175) B502175
theorem B334911 : Blo 334751 334911 := bstep (se 1 (by rfl) ⟨251183, by rfl⟩ : syracuseStep 334911 = 502367) B502367
theorem B335131 : Blo 334751 335131 := bstep (se 1 (by rfl) ⟨251348, by rfl⟩ : syracuseStep 335131 = 502697) B502697
theorem B335151 : Blo 334751 335151 := bstep (se 1 (by rfl) ⟨251363, by rfl⟩ : syracuseStep 335151 = 502727) B502727
theorem B335231 : Blo 334751 335231 := bstep (se 1 (by rfl) ⟨251423, by rfl⟩ : syracuseStep 335231 = 502847) B502847
theorem B335391 : Blo 334751 335391 := bstep (se 1 (by rfl) ⟨251543, by rfl⟩ : syracuseStep 335391 = 503087) B503087
theorem B17505841 : Blo 334751 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B335515 : Blo 334751 335515 := bstep (se 1 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 335515 = 503273) B503273
theorem B335551 : Blo 334751 335551 := bstep (se 1 (by rfl) ⟨251663, by rfl⟩ : syracuseStep 335551 = 503327) B503327
theorem B335611 : Blo 334751 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B14589719 : Blo 334751 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B335775 : Blo 334751 335775 := bstep (se 1 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 335775 = 503663) B503663
theorem B565231 : Blo 334751 565231 := bstep (se 1 (by rfl) ⟨423923, by rfl⟩ : syracuseStep 565231 = 847847) B847847
theorem B335943 : Blo 334751 335943 := bstep (se 1 (by rfl) ⟨251957, by rfl⟩ : syracuseStep 335943 = 503915) B503915
theorem B958625 : Blo 334751 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B565481 : Blo 334751 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B762119 : Blo 334751 762119 := bstep (se 1 (by rfl) ⟨571589, by rfl⟩ : syracuseStep 762119 = 1143179) B1143179
theorem B336231 : Blo 334751 336231 := bstep (se 1 (by rfl) ⟨252173, by rfl⟩ : syracuseStep 336231 = 504347) B504347
theorem B336351 : Blo 334751 336351 := bstep (se 1 (by rfl) ⟨252263, by rfl⟩ : syracuseStep 336351 = 504527) B504527
theorem B336543 : Blo 334751 336543 := bstep (se 1 (by rfl) ⟨252407, by rfl⟩ : syracuseStep 336543 = 504815) B504815
theorem B4170503 : Blo 334751 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1712987 : Blo 334751 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B336799 : Blo 334751 336799 := bstep (se 1 (by rfl) ⟨252599, by rfl⟩ : syracuseStep 336799 = 505199) B505199
theorem B336879 : Blo 334751 336879 := bstep (se 1 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 336879 = 505319) B505319
theorem B83731481 : Blo 334751 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B336999 : Blo 334751 336999 := bstep (se 1 (by rfl) ⟨252749, by rfl⟩ : syracuseStep 336999 = 505499) B505499
theorem B337223 : Blo 334751 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B337279 : Blo 334751 337279 := bstep (se 1 (by rfl) ⟨252959, by rfl⟩ : syracuseStep 337279 = 505919) B505919
theorem B337499 : Blo 334751 337499 := bstep (se 1 (by rfl) ⟨253124, by rfl⟩ : syracuseStep 337499 = 506249) B506249
theorem B566959 : Blo 334751 566959 := bstep (se 1 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 566959 = 850439) B850439
theorem B337615 : Blo 334751 337615 := bstep (se 1 (by rfl) ⟨253211, by rfl⟩ : syracuseStep 337615 = 506423) B506423
theorem B1386319 : Blo 334751 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B337831 : Blo 334751 337831 := bstep (se 1 (by rfl) ⟨253373, by rfl⟩ : syracuseStep 337831 = 506747) B506747
theorem B567479 : Blo 334751 567479 := bstep (se 1 (by rfl) ⟨425609, by rfl⟩ : syracuseStep 567479 = 851219) B851219
theorem B338239 : Blo 334751 338239 := bstep (se 1 (by rfl) ⟨253679, by rfl⟩ : syracuseStep 338239 = 507359) B507359
theorem B338407 : Blo 334751 338407 := bstep (se 1 (by rfl) ⟨253805, by rfl⟩ : syracuseStep 338407 = 507611) B507611
theorem B502313 : Blo 334751 502313 := bstep (se 2 (by rfl) ⟨188367, by rfl⟩ : syracuseStep 502313 = 376735) B376735
theorem B2861689 : Blo 334751 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B338587 : Blo 334751 338587 := bstep (se 1 (by rfl) ⟨253940, by rfl⟩ : syracuseStep 338587 = 507881) B507881
theorem B1714931 : Blo 334751 1714931 := bstep (se 1 (by rfl) ⟨1286198, by rfl⟩ : syracuseStep 1714931 = 2572397) B2572397
theorem B338715 : Blo 334751 338715 := bstep (se 1 (by rfl) ⟨254036, by rfl⟩ : syracuseStep 338715 = 508073) B508073
theorem B1026899 : Blo 334751 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B2567051 : Blo 334751 2567051 := bstep (se 1 (by rfl) ⟨1925288, by rfl⟩ : syracuseStep 2567051 = 3850577) B3850577
theorem B568255 : Blo 334751 568255 := bstep (se 1 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 568255 = 852383) B852383
theorem B502895 : Blo 334751 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B503081 : Blo 334751 503081 := bstep (se 2 (by rfl) ⟨188655, by rfl⟩ : syracuseStep 503081 = 377311) B377311
theorem B4074947 : Blo 334751 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B3059279 : Blo 334751 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B568937 : Blo 334751 568937 := bstep (se 2 (by rfl) ⟨213351, by rfl⟩ : syracuseStep 568937 = 426703) B426703
theorem B8171603 : Blo 334751 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B4468931 : Blo 334751 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B766235 : Blo 334751 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B504233 : Blo 334751 504233 := bstep (se 2 (by rfl) ⟨189087, by rfl⟩ : syracuseStep 504233 = 378175) B378175
theorem B504287 : Blo 334751 504287 := bstep (se 1 (by rfl) ⟨378215, by rfl⟩ : syracuseStep 504287 = 756431) B756431
theorem B504431 : Blo 334751 504431 := bstep (se 1 (by rfl) ⟨378323, by rfl⟩ : syracuseStep 504431 = 756647) B756647
theorem B504539 : Blo 334751 504539 := bstep (se 1 (by rfl) ⟨378404, by rfl⟩ : syracuseStep 504539 = 756809) B756809
theorem B504551 : Blo 334751 504551 := bstep (se 1 (by rfl) ⟨378413, by rfl⟩ : syracuseStep 504551 = 756827) B756827
theorem B537695 : Blo 334751 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B505691 : Blo 334751 505691 := bstep (se 1 (by rfl) ⟨379268, by rfl⟩ : syracuseStep 505691 = 758537) B758537
theorem B3749771 : Blo 334751 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B571495 : Blo 334751 571495 := bstep (se 1 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 571495 = 857243) B857243
theorem B637055 : Blo 334751 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B1620157 : Blo 334751 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B2570939 : Blo 334751 2570939 := bstep (se 1 (by rfl) ⟨1928204, by rfl⟩ : syracuseStep 2570939 = 3856409) B3856409
theorem B506987 : Blo 334751 506987 := bstep (se 1 (by rfl) ⟨380240, by rfl⟩ : syracuseStep 506987 = 760481) B760481
theorem B507227 : Blo 334751 507227 := bstep (se 1 (by rfl) ⟨380420, by rfl⟩ : syracuseStep 507227 = 760841) B760841
theorem B1130003 : Blo 334751 1130003 := bstep (se 1 (by rfl) ⟨847502, by rfl⟩ : syracuseStep 1130003 = 1695005) B1695005
theorem B1130057 : Blo 334751 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B573095 : Blo 334751 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B507575 : Blo 334751 507575 := bstep (se 1 (by rfl) ⟨380681, by rfl⟩ : syracuseStep 507575 = 761363) B761363
theorem B507887 : Blo 334751 507887 := bstep (se 1 (by rfl) ⟨380915, by rfl⟩ : syracuseStep 507887 = 761831) B761831
theorem B1130489 : Blo 334751 1130489 := bstep (se 2 (by rfl) ⟨423933, by rfl⟩ : syracuseStep 1130489 = 847867) B847867
theorem B770111 : Blo 334751 770111 := bstep (se 1 (by rfl) ⟨577583, by rfl⟩ : syracuseStep 770111 = 1155167) B1155167
theorem B508007 : Blo 334751 508007 := bstep (se 1 (by rfl) ⟨381005, by rfl⟩ : syracuseStep 508007 = 762011) B762011
theorem B8209451 : Blo 334751 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B1131623 : Blo 334751 1131623 := bstep (se 1 (by rfl) ⟨848717, by rfl⟩ : syracuseStep 1131623 = 1697435) B1697435
theorem B8177057 : Blo 334751 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B1132001 : Blo 334751 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B1132271 : Blo 334751 1132271 := bstep (se 1 (by rfl) ⟨849203, by rfl⟩ : syracuseStep 1132271 = 1698407) B1698407
theorem B1624657 : Blo 334751 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B2050685 : Blo 334751 2050685 := bstep (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) B769007
theorem B5458691 : Blo 334751 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B641915 : Blo 334751 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B1134323 : Blo 334751 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B380839 : Blo 334751 380839 := bstep (se 1 (by rfl) ⟨285629, by rfl⟩ : syracuseStep 380839 = 571259) B571259
theorem B381019 : Blo 334751 381019 := bstep (se 1 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 381019 = 571529) B571529
theorem B512191 : Blo 334751 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B3658121 : Blo 334751 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B12669779 : Blo 334751 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B1135457 : Blo 334751 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B480377 : Blo 334751 480377 := bstep (se 2 (by rfl) ⟨180141, by rfl⟩ : syracuseStep 480377 = 360283) B360283
theorem B1725851 : Blo 334751 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B1922555 : Blo 334751 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1136159 : Blo 334751 1136159 := bstep (se 1 (by rfl) ⟨852119, by rfl⟩ : syracuseStep 1136159 = 1704239) B1704239
theorem B1136375 : Blo 334751 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B20666843 : Blo 334751 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B1137455 : Blo 334751 1137455 := bstep (se 1 (by rfl) ⟨853091, by rfl⟩ : syracuseStep 1137455 = 1706183) B1706183
theorem B1727867 : Blo 334751 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B3235241 : Blo 334751 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B876271 : Blo 334751 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B18341639 : Blo 334751 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B1728809 : Blo 334751 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B6480323 : Blo 334751 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B1729183 : Blo 334751 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B11035705 : Blo 334751 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1139993 : Blo 334751 1139993 := bstep (se 2 (by rfl) ⟨427497, by rfl⟩ : syracuseStep 1139993 = 854995) B854995
theorem B1140047 : Blo 334751 1140047 := bstep (se 1 (by rfl) ⟨855035, by rfl⟩ : syracuseStep 1140047 = 1710071) B1710071
theorem B2418473 : Blo 334751 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B1075133 : Blo 334751 1075133 := bstep (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) B403175
theorem B2156777 : Blo 334751 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B1272743 : Blo 334751 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B3632039 : Blo 334751 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B912455 : Blo 334751 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B1142099 : Blo 334751 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B10415465 : Blo 334751 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1142207 : Blo 334751 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B650735 : Blo 334751 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B1142909 : Blo 334751 1142909 := bstep (se 3 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 1142909 = 428591) B428591
theorem B1143071 : Blo 334751 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B455335 : Blo 334751 455335 := bstep (se 1 (by rfl) ⟨341501, by rfl⟩ : syracuseStep 455335 = 683003) B683003
theorem B914107 : Blo 334751 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B1274687 : Blo 334751 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B1700675 : Blo 334751 1700675 := bstep (se 1 (by rfl) ⟨1275506, by rfl⟩ : syracuseStep 1700675 = 2551013) B2551013
theorem B7304033 : Blo 334751 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B1700999 : Blo 334751 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B1701161 : Blo 334751 1701161 := bstep (se 2 (by rfl) ⟨637935, by rfl⟩ : syracuseStep 1701161 = 1275871) B1275871
theorem B3700541 : Blo 334751 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B849761 : Blo 334751 849761 := bstep (se 2 (by rfl) ⟨318660, by rfl⟩ : syracuseStep 849761 = 637321) B637321
theorem B358651 : Blo 334751 358651 := bstep (se 1 (by rfl) ⟨268988, by rfl⟩ : syracuseStep 358651 = 537977) B537977
theorem B850459 : Blo 334751 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B1441097 : Blo 334751 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B1277801 : Blo 334751 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B4587779 : Blo 334751 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B5472967 : Blo 334751 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B754415 : Blo 334751 754415 := bstep (se 1 (by rfl) ⟨565811, by rfl⟩ : syracuseStep 754415 = 1131623) B1131623
theorem B754667 : Blo 334751 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B754847 : Blo 334751 754847 := bstep (se 1 (by rfl) ⟨566135, by rfl⟩ : syracuseStep 754847 = 1132271) B1132271
theorem B14714273 : Blo 334751 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B3639127 : Blo 334751 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B427943 : Blo 334751 427943 := bstep (se 1 (by rfl) ⟨320957, by rfl⟩ : syracuseStep 427943 = 641915) B641915
theorem B1443899 : Blo 334751 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B755945 : Blo 334751 755945 := bstep (se 2 (by rfl) ⟨283479, by rfl⟩ : syracuseStep 755945 = 566959) B566959
theorem B854327 : Blo 334751 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B756215 : Blo 334751 756215 := bstep (se 1 (by rfl) ⟨567161, by rfl⟩ : syracuseStep 756215 = 1134323) B1134323
theorem B1281005 : Blo 334751 1281005 := bstep (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) B480377
theorem B1707155 : Blo 334751 1707155 := bstep (se 1 (by rfl) ⟨1280366, by rfl⟩ : syracuseStep 1707155 = 2560733) B2560733
theorem B756971 : Blo 334751 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B2166209 : Blo 334751 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B2428453 : Blo 334751 2428453 := bstep (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) B455335
theorem B855623 : Blo 334751 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B1150567 : Blo 334751 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B1281703 : Blo 334751 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B757439 : Blo 334751 757439 := bstep (se 1 (by rfl) ⟨568079, by rfl⟩ : syracuseStep 757439 = 1136159) B1136159
theorem B757583 : Blo 334751 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B757673 : Blo 334751 757673 := bstep (se 2 (by rfl) ⟨284127, by rfl⟩ : syracuseStep 757673 = 568255) B568255
theorem B758303 : Blo 334751 758303 := bstep (se 1 (by rfl) ⟨568727, by rfl⟩ : syracuseStep 758303 = 1137455) B1137455
theorem B1151911 : Blo 334751 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B9999389 : Blo 334751 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B12227759 : Blo 334751 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B1152539 : Blo 334751 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B15472457 : Blo 334751 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B759995 : Blo 334751 759995 := bstep (se 1 (by rfl) ⟨569996, by rfl⟩ : syracuseStep 759995 = 1139993) B1139993
theorem B760031 : Blo 334751 760031 := bstep (se 1 (by rfl) ⟨570023, by rfl⟩ : syracuseStep 760031 = 1140047) B1140047
theorem B1218809 : Blo 334751 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B1612315 : Blo 334751 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B334875 : Blo 334751 334875 := bstep (se 1 (by rfl) ⟨251156, by rfl⟩ : syracuseStep 334875 = 502313) B502313
theorem B1711367 : Blo 334751 1711367 := bstep (se 1 (by rfl) ⟨1283525, by rfl⟩ : syracuseStep 1711367 = 2567051) B2567051
theorem B335263 : Blo 334751 335263 := bstep (se 1 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 335263 = 502895) B502895
theorem B335387 : Blo 334751 335387 := bstep (se 1 (by rfl) ⟨251540, by rfl⟩ : syracuseStep 335387 = 503081) B503081
theorem B761399 : Blo 334751 761399 := bstep (se 1 (by rfl) ⟨571049, by rfl⟩ : syracuseStep 761399 = 1142099) B1142099
theorem B761471 : Blo 334751 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B2039519 : Blo 334751 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B5447735 : Blo 334751 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B761939 : Blo 334751 761939 := bstep (se 1 (by rfl) ⟨571454, by rfl⟩ : syracuseStep 761939 = 1142909) B1142909
theorem B761993 : Blo 334751 761993 := bstep (se 2 (by rfl) ⟨285747, by rfl⟩ : syracuseStep 761993 = 571495) B571495
theorem B762047 : Blo 334751 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B336155 : Blo 334751 336155 := bstep (se 1 (by rfl) ⟨252116, by rfl⟩ : syracuseStep 336155 = 504233) B504233
theorem B336191 : Blo 334751 336191 := bstep (se 1 (by rfl) ⟨252143, by rfl⟩ : syracuseStep 336191 = 504287) B504287
theorem B336287 : Blo 334751 336287 := bstep (se 1 (by rfl) ⟨252215, by rfl⟩ : syracuseStep 336287 = 504431) B504431
theorem B336359 : Blo 334751 336359 := bstep (se 1 (by rfl) ⟨252269, by rfl⟩ : syracuseStep 336359 = 504539) B504539
theorem B336367 : Blo 334751 336367 := bstep (se 1 (by rfl) ⟨252275, by rfl⟩ : syracuseStep 336367 = 504551) B504551
theorem B10953589 : Blo 334751 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B2467027 : Blo 334751 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B337127 : Blo 334751 337127 := bstep (se 1 (by rfl) ⟨252845, by rfl⟩ : syracuseStep 337127 = 505691) B505691
theorem B566507 : Blo 334751 566507 := bstep (se 1 (by rfl) ⟨424880, by rfl⟩ : syracuseStep 566507 = 849761) B849761
theorem B1713959 : Blo 334751 1713959 := bstep (se 1 (by rfl) ⟨1285469, by rfl⟩ : syracuseStep 1713959 = 2570939) B2570939
theorem B23341121 : Blo 334751 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B337991 : Blo 334751 337991 := bstep (se 1 (by rfl) ⟨253493, by rfl⟩ : syracuseStep 337991 = 506987) B506987
theorem B960731 : Blo 334751 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B338151 : Blo 334751 338151 := bstep (se 1 (by rfl) ⟨253613, by rfl⟩ : syracuseStep 338151 = 507227) B507227
theorem B338383 : Blo 334751 338383 := bstep (se 1 (by rfl) ⟨253787, by rfl⟩ : syracuseStep 338383 = 507575) B507575
theorem B338591 : Blo 334751 338591 := bstep (se 1 (by rfl) ⟨253943, by rfl⟩ : syracuseStep 338591 = 507887) B507887
theorem B338671 : Blo 334751 338671 := bstep (se 1 (by rfl) ⟨254003, by rfl⟩ : syracuseStep 338671 = 508007) B508007
theorem B502655 : Blo 334751 502655 := bstep (se 1 (by rfl) ⟨376991, by rfl⟩ : syracuseStep 502655 = 753983) B753983
theorem B502991 : Blo 334751 502991 := bstep (se 1 (by rfl) ⟨377243, by rfl⟩ : syracuseStep 502991 = 754487) B754487
theorem B568667 : Blo 334751 568667 := bstep (se 1 (by rfl) ⟨426500, by rfl⟩ : syracuseStep 568667 = 853001) B853001
theorem B2305577 : Blo 334751 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B5451371 : Blo 334751 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B503711 : Blo 334751 503711 := bstep (se 1 (by rfl) ⟨377783, by rfl⟩ : syracuseStep 503711 = 755567) B755567
theorem B1912805 : Blo 334751 1912805 := bstep (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) B358651
theorem B962543 : Blo 334751 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B5747435 : Blo 334751 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B1848425 : Blo 334751 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B570665 : Blo 334751 570665 := bstep (se 2 (by rfl) ⟨213999, by rfl⟩ : syracuseStep 570665 = 427999) B427999
theorem B767483 : Blo 334751 767483 := bstep (se 1 (by rfl) ⟨575612, by rfl⟩ : syracuseStep 767483 = 1151225) B1151225
theorem B2438747 : Blo 334751 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B964217 : Blo 334751 964217 := bstep (se 2 (by rfl) ⟨361581, by rfl⟩ : syracuseStep 964217 = 723163) B723163
theorem B19642175 : Blo 334751 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B505883 : Blo 334751 505883 := bstep (se 1 (by rfl) ⟨379412, by rfl⟩ : syracuseStep 505883 = 758825) B758825
theorem B3815585 : Blo 334751 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B506735 : Blo 334751 506735 := bstep (se 1 (by rfl) ⟨380051, by rfl⟩ : syracuseStep 506735 = 760103) B760103
theorem B13777895 : Blo 334751 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B506975 : Blo 334751 506975 := bstep (se 1 (by rfl) ⟨380231, by rfl⟩ : syracuseStep 506975 = 760463) B760463
theorem B2867021 : Blo 334751 2867021 := bstep (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) B1075133
theorem B507785 : Blo 334751 507785 := bstep (se 2 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 507785 = 380839) B380839
theorem B639083 : Blo 334751 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B508025 : Blo 334751 508025 := bstep (se 2 (by rfl) ⟨190509, by rfl⟩ : syracuseStep 508025 = 381019) B381019
theorem B376987 : Blo 334751 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B508079 : Blo 334751 508079 := bstep (se 1 (by rfl) ⟨381059, by rfl⟩ : syracuseStep 508079 = 762119) B762119
theorem B55820987 : Blo 334751 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B9192269 : Blo 334751 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B378319 : Blo 334751 378319 := bstep (se 1 (by rfl) ⟨283739, by rfl⟩ : syracuseStep 378319 = 567479) B567479
theorem B608303 : Blo 334751 608303 := bstep (se 1 (by rfl) ⟨456227, by rfl⟩ : syracuseStep 608303 = 912455) B912455
theorem B379291 : Blo 334751 379291 := bstep (se 1 (by rfl) ⟨284468, by rfl⟩ : syracuseStep 379291 = 568937) B568937
theorem B510823 : Blo 334751 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B1133783 : Blo 334751 1133783 := bstep (se 1 (by rfl) ⟨850337, by rfl⟩ : syracuseStep 1133783 = 1700675) B1700675
theorem B4869355 : Blo 334751 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B1133945 : Blo 334751 1133945 := bstep (se 2 (by rfl) ⟨425229, by rfl⟩ : syracuseStep 1133945 = 850459) B850459
theorem B1133999 : Blo 334751 1133999 := bstep (se 1 (by rfl) ⟨850499, by rfl⟩ : syracuseStep 1133999 = 1700999) B1700999
theorem B1134107 : Blo 334751 1134107 := bstep (se 1 (by rfl) ⟨850580, by rfl⟩ : syracuseStep 1134107 = 1701161) B1701161
theorem B1528253 : Blo 334751 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B1168361 : Blo 334751 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B513407 : Blo 334751 513407 := bstep (se 1 (by rfl) ⟨385055, by rfl⟩ : syracuseStep 513407 = 770111) B770111
theorem B19486169 : Blo 334751 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B2578655 : Blo 334751 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1367123 : Blo 334751 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B1925471 : Blo 334751 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B8446519 : Blo 334751 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B616319 : Blo 334751 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B2156827 : Blo 334751 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B6941173 : Blo 334751 6941173 := bstep (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) B650735
theorem B9726479 : Blo 334751 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B682921 : Blo 334751 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B4320215 : Blo 334751 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B2780335 : Blo 334751 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B1141991 : Blo 334751 1141991 := bstep (se 1 (by rfl) ⟨856493, by rfl⟩ : syracuseStep 1141991 = 1712987) B1712987
theorem B1928569 : Blo 334751 1928569 := bstep (se 2 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 1928569 = 1446427) B1446427
theorem B1437851 : Blo 334751 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1536425 : Blo 334751 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B1143287 : Blo 334751 1143287 := bstep (se 1 (by rfl) ⟨857465, by rfl⟩ : syracuseStep 1143287 = 1714931) B1714931
theorem B848495 : Blo 334751 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B2421359 : Blo 334751 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B6943643 : Blo 334751 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B2716631 : Blo 334751 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B2979287 : Blo 334751 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1275385 : Blo 334751 1275385 := bstep (se 2 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 1275385 = 956539) B956539
theorem B2160209 : Blo 334751 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B849791 : Blo 334751 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B358463 : Blo 334751 358463 := bstep (se 1 (by rfl) ⟨268847, by rfl⟩ : syracuseStep 358463 = 537695) B537695
theorem B424703 : Blo 334751 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B753335 : Blo 334751 753335 := bstep (se 1 (by rfl) ⟨565001, by rfl⟩ : syracuseStep 753335 = 1130003) B1130003
theorem B753371 : Blo 334751 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B851867 : Blo 334751 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B753641 : Blo 334751 753641 := bstep (se 2 (by rfl) ⟨282615, by rfl⟩ : syracuseStep 753641 = 565231) B565231
theorem B753659 : Blo 334751 753659 := bstep (se 1 (by rfl) ⟨565244, by rfl⟩ : syracuseStep 753659 = 1130489) B1130489
theorem B426055 : Blo 334751 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B6128179 : Blo 334751 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B854003 : Blo 334751 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B755855 : Blo 334751 755855 := bstep (se 1 (by rfl) ⟨566891, by rfl⟩ : syracuseStep 755855 = 1133783) B1133783
theorem B755963 : Blo 334751 755963 := bstep (se 1 (by rfl) ⟨566972, by rfl⟩ : syracuseStep 755963 = 1133945) B1133945
theorem B755999 : Blo 334751 755999 := bstep (se 1 (by rfl) ⟨566999, by rfl⟩ : syracuseStep 755999 = 1133999) B1133999
theorem B1444139 : Blo 334751 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B756071 : Blo 334751 756071 := bstep (se 1 (by rfl) ⟨567053, by rfl⟩ : syracuseStep 756071 = 1134107) B1134107
theorem B4852169 : Blo 334751 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B1018835 : Blo 334751 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B6492473 : Blo 334751 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B3642245 : Blo 334751 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1708937 : Blo 334751 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B955901 : Blo 334751 955901 := bstep (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) B358463
theorem B1283647 : Blo 334751 1283647 := bstep (se 1 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 1283647 = 1925471) B1925471
theorem B335103 : Blo 334751 335103 := bstep (se 1 (by rfl) ⟨251327, by rfl⟩ : syracuseStep 335103 = 502655) B502655
theorem B335327 : Blo 334751 335327 := bstep (se 1 (by rfl) ⟨251495, by rfl⟩ : syracuseStep 335327 = 502991) B502991
theorem B761327 : Blo 334751 761327 := bstep (se 1 (by rfl) ⟨570995, by rfl⟩ : syracuseStep 761327 = 1141991) B1141991
theorem B36741053 : Blo 334751 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B335807 : Blo 334751 335807 := bstep (se 1 (by rfl) ⟨251855, by rfl⟩ : syracuseStep 335807 = 503711) B503711
theorem B958567 : Blo 334751 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B3645661 : Blo 334751 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B1024283 : Blo 334751 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B762191 : Blo 334751 762191 := bstep (se 1 (by rfl) ⟨571643, by rfl⟩ : syracuseStep 762191 = 1143287) B1143287
theorem B565663 : Blo 334751 565663 := bstep (se 1 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 565663 = 848495) B848495
theorem B1614239 : Blo 334751 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B6136357 : Blo 334751 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B4629095 : Blo 334751 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1811087 : Blo 334751 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B566527 : Blo 334751 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B337255 : Blo 334751 337255 := bstep (se 1 (by rfl) ⟨252941, by rfl⟩ : syracuseStep 337255 = 505883) B505883
theorem B337823 : Blo 334751 337823 := bstep (se 1 (by rfl) ⟨253367, by rfl⟩ : syracuseStep 337823 = 506735) B506735
theorem B337983 : Blo 334751 337983 := bstep (se 1 (by rfl) ⟨253487, by rfl⟩ : syracuseStep 337983 = 506975) B506975
theorem B502223 : Blo 334751 502223 := bstep (se 1 (by rfl) ⟨376667, by rfl⟩ : syracuseStep 502223 = 753335) B753335
theorem B502247 : Blo 334751 502247 := bstep (se 1 (by rfl) ⟨376685, by rfl⟩ : syracuseStep 502247 = 753371) B753371
theorem B1911347 : Blo 334751 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B338523 : Blo 334751 338523 := bstep (se 1 (by rfl) ⟨253892, by rfl⟩ : syracuseStep 338523 = 507785) B507785
theorem B567911 : Blo 334751 567911 := bstep (se 1 (by rfl) ⟨425933, by rfl⟩ : syracuseStep 567911 = 851867) B851867
theorem B502427 : Blo 334751 502427 := bstep (se 1 (by rfl) ⟨376820, by rfl⟩ : syracuseStep 502427 = 753641) B753641
theorem B502439 : Blo 334751 502439 := bstep (se 1 (by rfl) ⟨376829, by rfl⟩ : syracuseStep 502439 = 753659) B753659
theorem B338683 : Blo 334751 338683 := bstep (se 1 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 338683 = 508025) B508025
theorem B338719 : Blo 334751 338719 := bstep (se 1 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 338719 = 508079) B508079
theorem B3058519 : Blo 334751 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B502649 : Blo 334751 502649 := bstep (se 2 (by rfl) ⟨188493, by rfl⟩ : syracuseStep 502649 = 376987) B376987
theorem B502943 : Blo 334751 502943 := bstep (se 1 (by rfl) ⟨377207, by rfl⟩ : syracuseStep 502943 = 754415) B754415
theorem B503111 : Blo 334751 503111 := bstep (se 1 (by rfl) ⟨377333, by rfl⟩ : syracuseStep 503111 = 754667) B754667
theorem B503231 : Blo 334751 503231 := bstep (se 1 (by rfl) ⟨377423, by rfl⟩ : syracuseStep 503231 = 754847) B754847
theorem B9809515 : Blo 334751 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B405535 : Blo 334751 405535 := bstep (se 1 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 405535 = 608303) B608303
theorem B962599 : Blo 334751 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B503963 : Blo 334751 503963 := bstep (se 1 (by rfl) ⟨377972, by rfl⟩ : syracuseStep 503963 = 755945) B755945
theorem B569551 : Blo 334751 569551 := bstep (se 1 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 569551 = 854327) B854327
theorem B3289369 : Blo 334751 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B504143 : Blo 334751 504143 := bstep (se 1 (by rfl) ⟨378107, by rfl⟩ : syracuseStep 504143 = 756215) B756215
theorem B504425 : Blo 334751 504425 := bstep (se 2 (by rfl) ⟨189159, by rfl⟩ : syracuseStep 504425 = 378319) B378319
theorem B504647 : Blo 334751 504647 := bstep (se 1 (by rfl) ⟨378485, by rfl⟩ : syracuseStep 504647 = 756971) B756971
theorem B570415 : Blo 334751 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B504959 : Blo 334751 504959 := bstep (se 1 (by rfl) ⟨378719, by rfl⟩ : syracuseStep 504959 = 757439) B757439
theorem B505055 : Blo 334751 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B505115 : Blo 334751 505115 := bstep (se 1 (by rfl) ⟨378836, by rfl⟩ : syracuseStep 505115 = 757673) B757673
theorem B4929133 : Blo 334751 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B505535 : Blo 334751 505535 := bstep (se 1 (by rfl) ⟨379151, by rfl⟩ : syracuseStep 505535 = 758303) B758303
theorem B505721 : Blo 334751 505721 := bstep (se 2 (by rfl) ⟨189645, by rfl⟩ : syracuseStep 505721 = 379291) B379291
theorem B9254897 : Blo 334751 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B6666259 : Blo 334751 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B342271 : Blo 334751 342271 := bstep (se 1 (by rfl) ⟨256703, by rfl⟩ : syracuseStep 342271 = 513407) B513407
theorem B12990779 : Blo 334751 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B768359 : Blo 334751 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B506663 : Blo 334751 506663 := bstep (se 1 (by rfl) ⟨379997, by rfl⟩ : syracuseStep 506663 = 759995) B759995
theorem B1719103 : Blo 334751 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B506687 : Blo 334751 506687 := bstep (se 1 (by rfl) ⟨380015, by rfl⟩ : syracuseStep 506687 = 760031) B760031
theorem B2571425 : Blo 334751 2571425 := bstep (se 2 (by rfl) ⟨964284, by rfl⟩ : syracuseStep 2571425 = 1928569) B1928569
theorem B6143525 : Blo 334751 6143525 := bstep (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) B1151911
theorem B507599 : Blo 334751 507599 := bstep (se 1 (by rfl) ⟨380699, by rfl⟩ : syracuseStep 507599 = 761399) B761399
theorem B507647 : Blo 334751 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B1359679 : Blo 334751 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B507959 : Blo 334751 507959 := bstep (se 1 (by rfl) ⟨380969, by rfl⟩ : syracuseStep 507959 = 761939) B761939
theorem B507995 : Blo 334751 507995 := bstep (se 1 (by rfl) ⟨380996, by rfl⟩ : syracuseStep 507995 = 761993) B761993
theorem B508031 : Blo 334751 508031 := bstep (se 1 (by rfl) ⟨381023, by rfl⟩ : syracuseStep 508031 = 762047) B762047
theorem B377671 : Blo 334751 377671 := bstep (se 1 (by rfl) ⟨283253, by rfl⟩ : syracuseStep 377671 = 566507) B566507
theorem B14828453 : Blo 334751 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B410879 : Blo 334751 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B640487 : Blo 334751 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B1132541 : Blo 334751 1132541 := bstep (se 3 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 1132541 = 424703) B424703
theorem B379111 : Blo 334751 379111 := bstep (se 1 (by rfl) ⟨284333, by rfl⟩ : syracuseStep 379111 = 568667) B568667
theorem B641695 : Blo 334751 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B2149753 : Blo 334751 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B380443 : Blo 334751 380443 := bstep (se 1 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 380443 = 570665) B570665
theorem B1986191 : Blo 334751 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B511655 : Blo 334751 511655 := bstep (se 1 (by rfl) ⟨383741, by rfl⟩ : syracuseStep 511655 = 767483) B767483
theorem B1625831 : Blo 334751 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B642811 : Blo 334751 642811 := bstep (se 1 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 642811 = 964217) B964217
theorem B13094783 : Blo 334751 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B2543723 : Blo 334751 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B37213991 : Blo 334751 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B11262025 : Blo 334751 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B7297289 : Blo 334751 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B14604785 : Blo 334751 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B1138103 : Blo 334751 1138103 := bstep (se 1 (by rfl) ⟨853577, by rfl⟩ : syracuseStep 1138103 = 1707155) B1707155
theorem B2875769 : Blo 334751 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B778907 : Blo 334751 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B8151839 : Blo 334751 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B681097 : Blo 334751 681097 := bstep (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) B510823
theorem B10314971 : Blo 334751 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B812539 : Blo 334751 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B5760557 : Blo 334751 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B3237937 : Blo 334751 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1140911 : Blo 334751 1140911 := bstep (se 1 (by rfl) ⟨855683, by rfl⟩ : syracuseStep 1140911 = 1711367) B1711367
theorem B1141181 : Blo 334751 1141181 := bstep (se 3 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 1141181 = 427943) B427943
theorem B3631823 : Blo 334751 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B1142639 : Blo 334751 1142639 := bstep (se 1 (by rfl) ⟨856979, by rfl⟩ : syracuseStep 1142639 = 1713959) B1713959
theorem B15560747 : Blo 334751 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B6484319 : Blo 334751 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B2880143 : Blo 334751 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B1700513 : Blo 334751 1700513 := bstep (se 2 (by rfl) ⟨637692, by rfl⟩ : syracuseStep 1700513 = 1275385) B1275385
theorem B1537051 : Blo 334751 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B3634247 : Blo 334751 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B1275203 : Blo 334751 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B3831623 : Blo 334751 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B1278089 : Blo 334751 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B17268997 : Blo 334751 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B754217 : Blo 334751 754217 := bstep (se 2 (by rfl) ⟨282831, by rfl⟩ : syracuseStep 754217 = 565663) B565663
theorem B755027 : Blo 334751 755027 := bstep (se 1 (by rfl) ⟨566270, by rfl⟩ : syracuseStep 755027 = 1132541) B1132541
theorem B755369 : Blo 334751 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B1083385 : Blo 334751 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B1083887 : Blo 334751 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B4328315 : Blo 334751 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B2428163 : Blo 334751 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B855593 : Blo 334751 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B24809327 : Blo 334751 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1707965 : Blo 334751 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B9736523 : Blo 334751 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B758735 : Blo 334751 758735 := bstep (se 1 (by rfl) ⟨569051, by rfl⟩ : syracuseStep 758735 = 1138103) B1138103
theorem B857081 : Blo 334751 857081 := bstep (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) B642811
theorem B1283465 : Blo 334751 1283465 := bstep (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) B962599
theorem B759401 : Blo 334751 759401 := bstep (se 2 (by rfl) ⟨284775, by rfl⟩ : syracuseStep 759401 = 569551) B569551
theorem B3086063 : Blo 334751 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B3840371 : Blo 334751 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B760553 : Blo 334751 760553 := bstep (se 2 (by rfl) ⟨285207, by rfl⟩ : syracuseStep 760553 = 570415) B570415
theorem B760607 : Blo 334751 760607 := bstep (se 1 (by rfl) ⟨570455, by rfl⟩ : syracuseStep 760607 = 1140911) B1140911
theorem B760787 : Blo 334751 760787 := bstep (se 1 (by rfl) ⟨570590, by rfl⟩ : syracuseStep 760787 = 1141181) B1141181
theorem B334815 : Blo 334751 334815 := bstep (se 1 (by rfl) ⟨251111, by rfl⟩ : syracuseStep 334815 = 502223) B502223
theorem B334831 : Blo 334751 334831 := bstep (se 1 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 334831 = 502247) B502247
theorem B334951 : Blo 334751 334951 := bstep (se 1 (by rfl) ⟨251213, by rfl⟩ : syracuseStep 334951 = 502427) B502427
theorem B334959 : Blo 334751 334959 := bstep (se 1 (by rfl) ⟨251219, by rfl⟩ : syracuseStep 334959 = 502439) B502439
theorem B335099 : Blo 334751 335099 := bstep (se 1 (by rfl) ⟨251324, by rfl⟩ : syracuseStep 335099 = 502649) B502649
theorem B1711529 : Blo 334751 1711529 := bstep (se 2 (by rfl) ⟨641823, by rfl⟩ : syracuseStep 1711529 = 1283647) B1283647
theorem B335295 : Blo 334751 335295 := bstep (se 1 (by rfl) ⟨251471, by rfl⟩ : syracuseStep 335295 = 502943) B502943
theorem B335407 : Blo 334751 335407 := bstep (se 1 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 335407 = 503111) B503111
theorem B335487 : Blo 334751 335487 := bstep (se 1 (by rfl) ⟨251615, by rfl⟩ : syracuseStep 335487 = 503231) B503231
theorem B761759 : Blo 334751 761759 := bstep (se 1 (by rfl) ⟨571319, by rfl⟩ : syracuseStep 761759 = 1142639) B1142639
theorem B8888345 : Blo 334751 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B15016033 : Blo 334751 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B335975 : Blo 334751 335975 := bstep (se 1 (by rfl) ⟨251981, by rfl⟩ : syracuseStep 335975 = 503963) B503963
theorem B336095 : Blo 334751 336095 := bstep (se 1 (by rfl) ⟨252071, by rfl⟩ : syracuseStep 336095 = 504143) B504143
theorem B336283 : Blo 334751 336283 := bstep (se 1 (by rfl) ⟨252212, by rfl⟩ : syracuseStep 336283 = 504425) B504425
theorem B336431 : Blo 334751 336431 := bstep (se 1 (by rfl) ⟨252323, by rfl⟩ : syracuseStep 336431 = 504647) B504647
theorem B336639 : Blo 334751 336639 := bstep (se 1 (by rfl) ⟨252479, by rfl⟩ : syracuseStep 336639 = 504959) B504959
theorem B336703 : Blo 334751 336703 := bstep (se 1 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 336703 = 505055) B505055
theorem B336743 : Blo 334751 336743 := bstep (se 1 (by rfl) ⟨252557, by rfl⟩ : syracuseStep 336743 = 505115) B505115
theorem B337023 : Blo 334751 337023 := bstep (se 1 (by rfl) ⟨252767, by rfl⟩ : syracuseStep 337023 = 505535) B505535
theorem B337147 : Blo 334751 337147 := bstep (se 1 (by rfl) ⟨252860, by rfl⟩ : syracuseStep 337147 = 505721) B505721
theorem B6169931 : Blo 334751 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B8660519 : Blo 334751 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B337775 : Blo 334751 337775 := bstep (se 1 (by rfl) ⟨253331, by rfl⟩ : syracuseStep 337775 = 506663) B506663
theorem B337791 : Blo 334751 337791 := bstep (se 1 (by rfl) ⟨253343, by rfl⟩ : syracuseStep 337791 = 506687) B506687
theorem B1714283 : Blo 334751 1714283 := bstep (se 1 (by rfl) ⟨1285712, by rfl⟩ : syracuseStep 1714283 = 2571425) B2571425
theorem B1812905 : Blo 334751 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B338399 : Blo 334751 338399 := bstep (se 1 (by rfl) ⟨253799, by rfl⟩ : syracuseStep 338399 = 507599) B507599
theorem B338431 : Blo 334751 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B338639 : Blo 334751 338639 := bstep (se 1 (by rfl) ⟨253979, by rfl⟩ : syracuseStep 338639 = 507959) B507959
theorem B338663 : Blo 334751 338663 := bstep (se 1 (by rfl) ⟨253997, by rfl⟩ : syracuseStep 338663 = 507995) B507995
theorem B338687 : Blo 334751 338687 := bstep (se 1 (by rfl) ⟨254015, by rfl⟩ : syracuseStep 338687 = 508031) B508031
theorem B568073 : Blo 334751 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B4860881 : Blo 334751 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B2731421 : Blo 334751 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B503561 : Blo 334751 503561 := bstep (se 2 (by rfl) ⟨188835, by rfl⟩ : syracuseStep 503561 = 377671) B377671
theorem B569335 : Blo 334751 569335 := bstep (se 1 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 569335 = 854003) B854003
theorem B503903 : Blo 334751 503903 := bstep (se 1 (by rfl) ⟨377927, by rfl⟩ : syracuseStep 503903 = 755855) B755855
theorem B503975 : Blo 334751 503975 := bstep (se 1 (by rfl) ⟨377981, by rfl⟩ : syracuseStep 503975 = 755963) B755963
theorem B503999 : Blo 334751 503999 := bstep (se 1 (by rfl) ⟨377999, by rfl⟩ : syracuseStep 503999 = 755999) B755999
theorem B962759 : Blo 334751 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B504047 : Blo 334751 504047 := bstep (se 1 (by rfl) ⟨378035, by rfl⟩ : syracuseStep 504047 = 756071) B756071
theorem B2077085 : Blo 334751 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B1324127 : Blo 334751 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B8729855 : Blo 334751 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B32683621 : Blo 334751 32683621 := bstep (se 4 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 32683621 = 6128179) B6128179
theorem B505481 : Blo 334751 505481 := bstep (se 2 (by rfl) ⟨189555, by rfl⟩ : syracuseStep 505481 = 379111) B379111
theorem B1095677 : Blo 334751 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B4078025 : Blo 334751 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B4864859 : Blo 334751 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B2866337 : Blo 334751 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B507257 : Blo 334751 507257 := bstep (se 2 (by rfl) ⟨190221, by rfl⟩ : syracuseStep 507257 = 380443) B380443
theorem B507551 : Blo 334751 507551 := bstep (se 1 (by rfl) ⟨380663, by rfl⟩ : syracuseStep 507551 = 761327) B761327
theorem B24494035 : Blo 334751 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B540713 : Blo 334751 540713 := bstep (se 2 (by rfl) ⟨202767, by rfl⟩ : syracuseStep 540713 = 405535) B405535
theorem B508127 : Blo 334751 508127 := bstep (se 1 (by rfl) ⟨381095, by rfl⟩ : syracuseStep 508127 = 762191) B762191
theorem B1917179 : Blo 334751 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B2049401 : Blo 334751 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B378607 : Blo 334751 378607 := bstep (se 1 (by rfl) ⟨283955, by rfl⟩ : syracuseStep 378607 = 567911) B567911
theorem B6572177 : Blo 334751 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B10373831 : Blo 334751 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B1920095 : Blo 334751 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B1133675 : Blo 334751 1133675 := bstep (se 1 (by rfl) ⟨850256, by rfl⟩ : syracuseStep 1133675 = 1700513) B1700513
theorem B52317413 : Blo 334751 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B512239 : Blo 334751 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B1364413 : Blo 334751 1364413 := bstep (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) B511655
theorem B9885635 : Blo 334751 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B8181809 : Blo 334751 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B1825445 : Blo 334751 1825445 := bstep (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) B342271
theorem B908129 : Blo 334751 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B3234779 : Blo 334751 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B679223 : Blo 334751 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B1695815 : Blo 334751 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B1139291 : Blo 334751 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B2549069 : Blo 334751 2549069 := bstep (se 3 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 2549069 = 955901) B955901
theorem B1076159 : Blo 334751 1076159 := bstep (se 1 (by rfl) ⟨807119, by rfl⟩ : syracuseStep 1076159 = 1614239) B1614239
theorem B4385825 : Blo 334751 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B1207391 : Blo 334751 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B5434559 : Blo 334751 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B6876647 : Blo 334751 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B1274231 : Blo 334751 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B2421215 : Blo 334751 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B4322879 : Blo 334751 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2422831 : Blo 334751 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B850135 : Blo 334751 850135 := bstep (se 1 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 850135 = 1275203) B1275203
theorem B2292137 : Blo 334751 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B2554415 : Blo 334751 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B4095683 : Blo 334751 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B852059 : Blo 334751 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B1441901 : Blo 334751 1441901 := bstep (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) B540713
theorem B20021377 : Blo 334751 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B1278119 : Blo 334751 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B5538893 : Blo 334751 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B722591 : Blo 334751 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B6915887 : Blo 334751 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B2885543 : Blo 334751 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B1280063 : Blo 334751 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B755783 : Blo 334751 755783 := bstep (se 1 (by rfl) ⟨566837, by rfl⟩ : syracuseStep 755783 = 1133675) B1133675
theorem B6491015 : Blo 334751 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B855643 : Blo 334751 855643 := bstep (se 1 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 855643 = 1283465) B1283465
theorem B6590423 : Blo 334751 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B2560247 : Blo 334751 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B1216963 : Blo 334751 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B759113 : Blo 334751 759113 := bstep (se 2 (by rfl) ⟨284667, by rfl⟩ : syracuseStep 759113 = 569335) B569335
theorem B759527 : Blo 334751 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B5773679 : Blo 334751 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B2923883 : Blo 334751 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B335707 : Blo 334751 335707 := bstep (se 1 (by rfl) ⟨251780, by rfl⟩ : syracuseStep 335707 = 503561) B503561
theorem B335935 : Blo 334751 335935 := bstep (se 1 (by rfl) ⟨251951, by rfl⟩ : syracuseStep 335935 = 503903) B503903
theorem B335983 : Blo 334751 335983 := bstep (se 1 (by rfl) ⟨251987, by rfl⟩ : syracuseStep 335983 = 503975) B503975
theorem B335999 : Blo 334751 335999 := bstep (se 1 (by rfl) ⟨251999, by rfl⟩ : syracuseStep 335999 = 503999) B503999
theorem B336031 : Blo 334751 336031 := bstep (se 1 (by rfl) ⟨252023, by rfl⟩ : syracuseStep 336031 = 504047) B504047
theorem B3219709 : Blo 334751 3219709 := bstep (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) B1207391
theorem B1614143 : Blo 334751 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B1811261 : Blo 334751 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B7283789 : Blo 334751 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B336987 : Blo 334751 336987 := bstep (se 1 (by rfl) ⟨252740, by rfl⟩ : syracuseStep 336987 = 505481) B505481
theorem B730451 : Blo 334751 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B1910891 : Blo 334751 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B338171 : Blo 334751 338171 := bstep (se 1 (by rfl) ⟨253628, by rfl⟩ : syracuseStep 338171 = 507257) B507257
theorem B338367 : Blo 334751 338367 := bstep (se 1 (by rfl) ⟨253775, by rfl⟩ : syracuseStep 338367 = 507551) B507551
theorem B2730455 : Blo 334751 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B5778053 : Blo 334751 5778053 := bstep (se 4 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 5778053 = 1083385) B1083385
theorem B338751 : Blo 334751 338751 := bstep (se 1 (by rfl) ⟨254063, by rfl⟩ : syracuseStep 338751 = 508127) B508127
theorem B502811 : Blo 334751 502811 := bstep (se 1 (by rfl) ⟨377108, by rfl⟩ : syracuseStep 502811 = 754217) B754217
theorem B503351 : Blo 334751 503351 := bstep (se 1 (by rfl) ⟨377513, by rfl⟩ : syracuseStep 503351 = 755027) B755027
theorem B503579 : Blo 334751 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B34878275 : Blo 334751 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B1618775 : Blo 334751 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B504809 : Blo 334751 504809 := bstep (se 2 (by rfl) ⟨189303, by rfl⟩ : syracuseStep 504809 = 378607) B378607
theorem B570395 : Blo 334751 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B505823 : Blo 334751 505823 := bstep (se 1 (by rfl) ⟨379367, by rfl⟩ : syracuseStep 505823 = 758735) B758735
theorem B571387 : Blo 334751 571387 := bstep (se 1 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 571387 = 857081) B857081
theorem B506267 : Blo 334751 506267 := bstep (se 1 (by rfl) ⟨379700, by rfl⟩ : syracuseStep 506267 = 759401) B759401
theorem B5454539 : Blo 334751 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B507035 : Blo 334751 507035 := bstep (se 1 (by rfl) ⟨380276, by rfl⟩ : syracuseStep 507035 = 760553) B760553
theorem B507071 : Blo 334751 507071 := bstep (se 1 (by rfl) ⟨380303, by rfl⟩ : syracuseStep 507071 = 760607) B760607
theorem B507191 : Blo 334751 507191 := bstep (se 1 (by rfl) ⟨380393, by rfl⟩ : syracuseStep 507191 = 760787) B760787
theorem B507839 : Blo 334751 507839 := bstep (se 1 (by rfl) ⟨380879, by rfl⟩ : syracuseStep 507839 = 761759) B761759
theorem B1130543 : Blo 334751 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B1819217 : Blo 334751 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B4113287 : Blo 334751 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B378715 : Blo 334751 378715 := bstep (se 1 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 378715 = 568073) B568073
theorem B3623039 : Blo 334751 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B3230441 : Blo 334751 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B641839 : Blo 334751 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B1133513 : Blo 334751 1133513 := bstep (se 2 (by rfl) ⟨425067, by rfl⟩ : syracuseStep 1133513 = 850135) B850135
theorem B5819903 : Blo 334751 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B1528091 : Blo 334751 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B32658713 : Blo 334751 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B23025329 : Blo 334751 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1366267 : Blo 334751 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B4381451 : Blo 334751 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B16539551 : Blo 334751 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B1138643 : Blo 334751 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B3531005 : Blo 334751 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B2057375 : Blo 334751 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B2156519 : Blo 334751 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B1141019 : Blo 334751 1141019 := bstep (se 1 (by rfl) ⟨855764, by rfl⟩ : syracuseStep 1141019 = 1711529) B1711529
theorem B5925563 : Blo 334751 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B682985 : Blo 334751 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B1699379 : Blo 334751 1699379 := bstep (se 1 (by rfl) ⟨1274534, by rfl⟩ : syracuseStep 1699379 = 2549069) B2549069
theorem B1142855 : Blo 334751 1142855 := bstep (se 1 (by rfl) ⟨857141, by rfl⟩ : syracuseStep 1142855 = 1714283) B1714283
theorem B1208603 : Blo 334751 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B717439 : Blo 334751 717439 := bstep (se 1 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 717439 = 1076159) B1076159
theorem B3240587 : Blo 334751 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B43578161 : Blo 334751 43578161 := bstep (se 2 (by rfl) ⟨16341810, by rfl⟩ : syracuseStep 43578161 = 32683621) B32683621
theorem B2421677 : Blo 334751 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B4584431 : Blo 334751 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B849487 : Blo 334751 849487 := bstep (se 1 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 849487 = 1274231) B1274231
theorem B2881919 : Blo 334751 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B2718683 : Blo 334751 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B1702943 : Blo 334751 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B3243239 : Blo 334751 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B753695 : Blo 334751 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B852079 : Blo 334751 852079 := bstep (se 1 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 852079 = 1278119) B1278119
theorem B4292945 : Blo 334751 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B59081525 : Blo 334751 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B853375 : Blo 334751 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B4851245 : Blo 334751 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B4327343 : Blo 334751 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B755675 : Blo 334751 755675 := bstep (se 1 (by rfl) ⟨566756, by rfl⟩ : syracuseStep 755675 = 1133513) B1133513
theorem B6490469 : Blo 334751 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B4393615 : Blo 334751 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B1706831 : Blo 334751 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B1018727 : Blo 334751 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B855785 : Blo 334751 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B2920967 : Blo 334751 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B759095 : Blo 334751 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B4855859 : Blo 334751 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B956585 : Blo 334751 956585 := bstep (se 2 (by rfl) ⟨358719, by rfl⟩ : syracuseStep 956585 = 717439) B717439
theorem B760679 : Blo 334751 760679 := bstep (se 1 (by rfl) ⟨570509, by rfl⟩ : syracuseStep 760679 = 1141019) B1141019
theorem B335207 : Blo 334751 335207 := bstep (se 1 (by rfl) ⟨251405, by rfl⟩ : syracuseStep 335207 = 502811) B502811
theorem B335567 : Blo 334751 335567 := bstep (se 1 (by rfl) ⟨251675, by rfl⟩ : syracuseStep 335567 = 503351) B503351
theorem B335719 : Blo 334751 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B761849 : Blo 334751 761849 := bstep (se 2 (by rfl) ⟨285693, by rfl⟩ : syracuseStep 761849 = 571387) B571387
theorem B761903 : Blo 334751 761903 := bstep (se 1 (by rfl) ⟨571427, by rfl⟩ : syracuseStep 761903 = 1142855) B1142855
theorem B1614451 : Blo 334751 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B336539 : Blo 334751 336539 := bstep (se 1 (by rfl) ⟨252404, by rfl⟩ : syracuseStep 336539 = 504809) B504809
theorem B3056287 : Blo 334751 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B337215 : Blo 334751 337215 := bstep (se 1 (by rfl) ⟨252911, by rfl⟩ : syracuseStep 337215 = 505823) B505823
theorem B337511 : Blo 334751 337511 := bstep (se 1 (by rfl) ⟨253133, by rfl⟩ : syracuseStep 337511 = 506267) B506267
theorem B1812455 : Blo 334751 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B338023 : Blo 334751 338023 := bstep (se 1 (by rfl) ⟨253517, by rfl⟩ : syracuseStep 338023 = 507035) B507035
theorem B338047 : Blo 334751 338047 := bstep (se 1 (by rfl) ⟨253535, by rfl⟩ : syracuseStep 338047 = 507071) B507071
theorem B338127 : Blo 334751 338127 := bstep (se 1 (by rfl) ⟨253595, by rfl⟩ : syracuseStep 338127 = 507191) B507191
theorem B338559 : Blo 334751 338559 := bstep (se 1 (by rfl) ⟨253919, by rfl⟩ : syracuseStep 338559 = 507839) B507839
theorem B568039 : Blo 334751 568039 := bstep (se 1 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 568039 = 852059) B852059
theorem B961267 : Blo 334751 961267 := bstep (se 1 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 961267 = 1441901) B1441901
theorem B503855 : Blo 334751 503855 := bstep (se 1 (by rfl) ⟨377891, by rfl⟩ : syracuseStep 503855 = 755783) B755783
theorem B3879935 : Blo 334751 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B504953 : Blo 334751 504953 := bstep (se 2 (by rfl) ⟨189357, by rfl⟩ : syracuseStep 504953 = 378715) B378715
theorem B21772475 : Blo 334751 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B506075 : Blo 334751 506075 := bstep (se 1 (by rfl) ⟨379556, by rfl⟩ : syracuseStep 506075 = 759113) B759113
theorem B15350219 : Blo 334751 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B506351 : Blo 334751 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B3849119 : Blo 334751 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B1949255 : Blo 334751 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B11026367 : Blo 334751 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1820303 : Blo 334751 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B3852035 : Blo 334751 3852035 := bstep (se 1 (by rfl) ⟨2889026, by rfl⟩ : syracuseStep 3852035 = 5778053) B5778053
theorem B3950375 : Blo 334751 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B1132649 : Blo 334751 1132649 := bstep (se 2 (by rfl) ⟨424743, by rfl⟩ : syracuseStep 1132649 = 849487) B849487
theorem B1132919 : Blo 334751 1132919 := bstep (se 1 (by rfl) ⟨849689, by rfl⟩ : syracuseStep 1132919 = 1699379) B1699379
theorem B1821293 : Blo 334751 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B805735 : Blo 334751 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1821689 : Blo 334751 1821689 := bstep (se 2 (by rfl) ⟨683133, by rfl⟩ : syracuseStep 1821689 = 1366267) B1366267
theorem B29052107 : Blo 334751 29052107 := bstep (se 1 (by rfl) ⟨21789080, by rfl⟩ : syracuseStep 29052107 = 43578161) B43578161
theorem B23252183 : Blo 334751 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B380263 : Blo 334751 380263 := bstep (se 1 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 380263 = 570395) B570395
theorem B1921279 : Blo 334751 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B1135295 : Blo 334751 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B26695169 : Blo 334751 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B2742191 : Blo 334751 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B481727 : Blo 334751 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B4610591 : Blo 334751 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B1923695 : Blo 334751 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B2415359 : Blo 334751 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B2153627 : Blo 334751 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B1140857 : Blo 334751 1140857 := bstep (se 2 (by rfl) ⟨427821, by rfl⟩ : syracuseStep 1140857 = 855643) B855643
theorem B2354003 : Blo 334751 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1076095 : Blo 334751 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B1207507 : Blo 334751 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B1371583 : Blo 334751 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B486967 : Blo 334751 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B1437679 : Blo 334751 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B1273927 : Blo 334751 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B2160391 : Blo 334751 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B1079183 : Blo 334751 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B3636359 : Blo 334751 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B2162159 : Blo 334751 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B39387683 : Blo 334751 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B1213535 : Blo 334751 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B2884895 : Blo 334751 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B755099 : Blo 334751 755099 := bstep (se 1 (by rfl) ⟨566324, by rfl⟩ : syracuseStep 755099 = 1132649) B1132649
theorem B4326979 : Blo 334751 4326979 := bstep (se 1 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 4326979 = 6490469) B6490469
theorem B755279 : Blo 334751 755279 := bstep (se 1 (by rfl) ⟨566459, by rfl⟩ : syracuseStep 755279 = 1132919) B1132919
theorem B1214195 : Blo 334751 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B1214459 : Blo 334751 1214459 := bstep (se 1 (by rfl) ⟨910844, by rfl⟩ : syracuseStep 1214459 = 1821689) B1821689
theorem B19368071 : Blo 334751 19368071 := bstep (se 1 (by rfl) ⟨14526053, by rfl⟩ : syracuseStep 19368071 = 29052107) B29052107
theorem B15501455 : Blo 334751 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B756863 : Blo 334751 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B757385 : Blo 334751 757385 := bstep (se 2 (by rfl) ⟨284019, by rfl⟩ : syracuseStep 757385 = 568039) B568039
theorem B1281689 : Blo 334751 1281689 := bstep (se 2 (by rfl) ⟨480633, by rfl⟩ : syracuseStep 1281689 = 961267) B961267
theorem B17796779 : Blo 334751 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B1610009 : Blo 334751 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B1282463 : Blo 334751 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B2561705 : Blo 334751 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B1284605 : Blo 334751 1284605 := bstep (se 3 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 1284605 = 481727) B481727
theorem B760571 : Blo 334751 760571 := bstep (se 1 (by rfl) ⟨570428, by rfl⟩ : syracuseStep 760571 = 1140857) B1140857
theorem B335903 : Blo 334751 335903 := bstep (se 1 (by rfl) ⟨251927, by rfl⟩ : syracuseStep 335903 = 503855) B503855
theorem B336635 : Blo 334751 336635 := bstep (se 1 (by rfl) ⟨252476, by rfl⟩ : syracuseStep 336635 = 504953) B504953
theorem B25109365 : Blo 334751 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B337383 : Blo 334751 337383 := bstep (se 1 (by rfl) ⟨253037, by rfl⟩ : syracuseStep 337383 = 506075) B506075
theorem B10233479 : Blo 334751 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B337567 : Blo 334751 337567 := bstep (se 1 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 337567 = 506351) B506351
theorem B2566079 : Blo 334751 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B7350911 : Blo 334751 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B502463 : Blo 334751 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2861963 : Blo 334751 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B4075049 : Blo 334751 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B2568023 : Blo 334751 2568023 := bstep (se 1 (by rfl) ⟨1926017, by rfl⟩ : syracuseStep 2568023 = 3852035) B3852035
theorem B503783 : Blo 334751 503783 := bstep (se 1 (by rfl) ⟨377837, by rfl⟩ : syracuseStep 503783 = 755675) B755675
theorem B570523 : Blo 334751 570523 := bstep (se 1 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 570523 = 855785) B855785
theorem B1947311 : Blo 334751 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B506063 : Blo 334751 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B637723 : Blo 334751 637723 := bstep (se 1 (by rfl) ⟨478292, by rfl⟩ : syracuseStep 637723 = 956585) B956585
theorem B507017 : Blo 334751 507017 := bstep (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) B380263
theorem B507119 : Blo 334751 507119 := bstep (se 1 (by rfl) ⟨380339, by rfl⟩ : syracuseStep 507119 = 760679) B760679
theorem B1916905 : Blo 334751 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B507899 : Blo 334751 507899 := bstep (se 1 (by rfl) ⟨380924, by rfl⟩ : syracuseStep 507899 = 761849) B761849
theorem B507935 : Blo 334751 507935 := bstep (se 1 (by rfl) ⟨380951, by rfl⟩ : syracuseStep 507935 = 761903) B761903
theorem B6440957 : Blo 334751 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B1299503 : Blo 334751 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B1136105 : Blo 334751 1136105 := bstep (se 2 (by rfl) ⟨426039, by rfl⟩ : syracuseStep 1136105 = 852079) B852079
theorem B2152601 : Blo 334751 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B3234163 : Blo 334751 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B1137833 : Blo 334751 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B1137887 : Blo 334751 1137887 := bstep (se 1 (by rfl) ⟨853415, by rfl⟩ : syracuseStep 1137887 = 1706831) B1706831
theorem B679151 : Blo 334751 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B5858153 : Blo 334751 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B1074313 : Blo 334751 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B1434793 : Blo 334751 1434793 := bstep (se 2 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 1434793 = 1076095) B1076095
theorem B1828127 : Blo 334751 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B3237239 : Blo 334751 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B3073727 : Blo 334751 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B1828777 : Blo 334751 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B649289 : Blo 334751 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B1435751 : Blo 334751 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1698569 : Blo 334751 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B1208303 : Blo 334751 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B2880521 : Blo 334751 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B42137333 : Blo 334751 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B2586623 : Blo 334751 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B719455 : Blo 334751 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B14514983 : Blo 334751 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B2424239 : Blo 334751 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B1441439 : Blo 334751 1441439 := bstep (se 1 (by rfl) ⟨1081079, by rfl⟩ : syracuseStep 1441439 = 2162159) B2162159
theorem B4293971 : Blo 334751 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B12912047 : Blo 334751 12912047 := bstep (se 1 (by rfl) ⟨9684035, by rfl⟩ : syracuseStep 12912047 = 19368071) B19368071
theorem B5769305 : Blo 334751 5769305 := bstep (se 2 (by rfl) ⟨2163489, by rfl⟩ : syracuseStep 5769305 = 4326979) B4326979
theorem B854459 : Blo 334751 854459 := bstep (se 1 (by rfl) ⟨640844, by rfl⟩ : syracuseStep 854459 = 1281689) B1281689
theorem B11864519 : Blo 334751 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B854975 : Blo 334751 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B757403 : Blo 334751 757403 := bstep (se 1 (by rfl) ⟨568052, by rfl⟩ : syracuseStep 757403 = 1136105) B1136105
theorem B1707803 : Blo 334751 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B856403 : Blo 334751 856403 := bstep (se 1 (by rfl) ⟨642302, by rfl⟩ : syracuseStep 856403 = 1284605) B1284605
theorem B758555 : Blo 334751 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B758591 : Blo 334751 758591 := bstep (se 1 (by rfl) ⟨568943, by rfl⟩ : syracuseStep 758591 = 1137887) B1137887
theorem B3905435 : Blo 334751 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B6822319 : Blo 334751 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1710719 : Blo 334751 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B432859 : Blo 334751 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B957167 : Blo 334751 957167 := bstep (se 1 (by rfl) ⟨717875, by rfl⟩ : syracuseStep 957167 = 1435751) B1435751
theorem B760697 : Blo 334751 760697 := bstep (se 2 (by rfl) ⟨285261, by rfl⟩ : syracuseStep 760697 = 570523) B570523
theorem B334975 : Blo 334751 334975 := bstep (se 1 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 334975 = 502463) B502463
theorem B1907975 : Blo 334751 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B12951413 : Blo 334751 12951413 := bstep (se 5 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 12951413 = 1214195) B1214195
theorem B1712015 : Blo 334751 1712015 := bstep (se 1 (by rfl) ⟨1284011, by rfl⟩ : syracuseStep 1712015 = 2568023) B2568023
theorem B335855 : Blo 334751 335855 := bstep (se 1 (by rfl) ⟨251891, by rfl⟩ : syracuseStep 335855 = 503783) B503783
theorem B1811069 : Blo 334751 1811069 := bstep (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) B679151
theorem B959273 : Blo 334751 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B28091555 : Blo 334751 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B337375 : Blo 334751 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B9676655 : Blo 334751 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B338011 : Blo 334751 338011 := bstep (se 1 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 338011 = 507017) B507017
theorem B338079 : Blo 334751 338079 := bstep (se 1 (by rfl) ⟨253559, by rfl⟩ : syracuseStep 338079 = 507119) B507119
theorem B1616159 : Blo 334751 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B960959 : Blo 334751 960959 := bstep (se 1 (by rfl) ⟨720719, by rfl⟩ : syracuseStep 960959 = 1441439) B1441439
theorem B338599 : Blo 334751 338599 := bstep (se 1 (by rfl) ⟨253949, by rfl⟩ : syracuseStep 338599 = 507899) B507899
theorem B338623 : Blo 334751 338623 := bstep (se 1 (by rfl) ⟨253967, by rfl⟩ : syracuseStep 338623 = 507935) B507935
theorem B26258455 : Blo 334751 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B503399 : Blo 334751 503399 := bstep (se 1 (by rfl) ⟨377549, by rfl⟩ : syracuseStep 503399 = 755099) B755099
theorem B503519 : Blo 334751 503519 := bstep (se 1 (by rfl) ⟨377639, by rfl⟩ : syracuseStep 503519 = 755279) B755279
theorem B10334303 : Blo 334751 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B1913057 : Blo 334751 1913057 := bstep (se 2 (by rfl) ⟨717396, by rfl⟩ : syracuseStep 1913057 = 1434793) B1434793
theorem B504575 : Blo 334751 504575 := bstep (se 1 (by rfl) ⟨378431, by rfl⟩ : syracuseStep 504575 = 756863) B756863
theorem B504923 : Blo 334751 504923 := bstep (se 1 (by rfl) ⟨378692, by rfl⟩ : syracuseStep 504923 = 757385) B757385
theorem B2438369 : Blo 334751 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B866335 : Blo 334751 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B507047 : Blo 334751 507047 := bstep (se 1 (by rfl) ⟨380285, by rfl⟩ : syracuseStep 507047 = 760571) B760571
theorem B2049151 : Blo 334751 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B4900607 : Blo 334751 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B1132379 : Blo 334751 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B805535 : Blo 334751 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B4312217 : Blo 334751 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B1920347 : Blo 334751 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B1298207 : Blo 334751 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B809023 : Blo 334751 809023 := bstep (se 1 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 809023 = 1213535) B1213535
theorem B1923263 : Blo 334751 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B33479153 : Blo 334751 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B809639 : Blo 334751 809639 := bstep (se 1 (by rfl) ⟨607229, by rfl⟩ : syracuseStep 809639 = 1214459) B1214459
theorem B1432417 : Blo 334751 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1073339 : Blo 334751 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B4875005 : Blo 334751 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B1435067 : Blo 334751 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B2158159 : Blo 334751 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B2716699 : Blo 334751 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B850297 : Blo 334751 850297 := bstep (se 2 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 850297 = 637723) B637723
theorem B2555873 : Blo 334751 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B27590645 : Blo 334751 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B754919 : Blo 334751 754919 := bstep (se 1 (by rfl) ⟨566189, by rfl⟩ : syracuseStep 754919 = 1132379) B1132379
theorem B1280231 : Blo 334751 1280231 := bstep (se 1 (by rfl) ⟨960173, by rfl⟩ : syracuseStep 1280231 = 1920347) B1920347
theorem B1282175 : Blo 334751 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B22319435 : Blo 334751 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B3250003 : Blo 334751 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B956711 : Blo 334751 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B335599 : Blo 334751 335599 := bstep (se 1 (by rfl) ⟨251699, by rfl⟩ : syracuseStep 335599 = 503399) B503399
theorem B335679 : Blo 334751 335679 := bstep (se 1 (by rfl) ⟨251759, by rfl⟩ : syracuseStep 335679 = 503519) B503519
theorem B1155113 : Blo 334751 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B6889535 : Blo 334751 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B336383 : Blo 334751 336383 := bstep (se 1 (by rfl) ⟨252287, by rfl⟩ : syracuseStep 336383 = 504575) B504575
theorem B336615 : Blo 334751 336615 := bstep (se 1 (by rfl) ⟨252461, by rfl⟩ : syracuseStep 336615 = 504923) B504923
theorem B1909889 : Blo 334751 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B338031 : Blo 334751 338031 := bstep (se 1 (by rfl) ⟨253523, by rfl⟩ : syracuseStep 338031 = 507047) B507047
theorem B18393763 : Blo 334751 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B2862647 : Blo 334751 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B3846203 : Blo 334751 3846203 := bstep (se 1 (by rfl) ⟨2884652, by rfl⟩ : syracuseStep 3846203 = 5769305) B5769305
theorem B2732201 : Blo 334751 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B569639 : Blo 334751 569639 := bstep (se 1 (by rfl) ⟨427229, by rfl⟩ : syracuseStep 569639 = 854459) B854459
theorem B7909679 : Blo 334751 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B537023 : Blo 334751 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B569983 : Blo 334751 569983 := bstep (se 1 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 569983 = 854975) B854975
theorem B504935 : Blo 334751 504935 := bstep (se 1 (by rfl) ⟨378701, by rfl⟩ : syracuseStep 504935 = 757403) B757403
theorem B570935 : Blo 334751 570935 := bstep (se 1 (by rfl) ⟨428201, by rfl⟩ : syracuseStep 570935 = 856403) B856403
theorem B505703 : Blo 334751 505703 := bstep (se 1 (by rfl) ⟨379277, by rfl⟩ : syracuseStep 505703 = 758555) B758555
theorem B505727 : Blo 334751 505727 := bstep (se 1 (by rfl) ⟨379295, by rfl⟩ : syracuseStep 505727 = 758591) B758591
theorem B35011273 : Blo 334751 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B539759 : Blo 334751 539759 := bstep (se 1 (by rfl) ⟨404819, by rfl⟩ : syracuseStep 539759 = 809639) B809639
theorem B638111 : Blo 334751 638111 := bstep (se 1 (by rfl) ⟨478583, by rfl⟩ : syracuseStep 638111 = 957167) B957167
theorem B507131 : Blo 334751 507131 := bstep (se 1 (by rfl) ⟨380348, by rfl⟩ : syracuseStep 507131 = 760697) B760697
theorem B8634275 : Blo 334751 8634275 := bstep (se 1 (by rfl) ⟨6475706, by rfl⟩ : syracuseStep 8634275 = 12951413) B12951413
theorem B639515 : Blo 334751 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B4309757 : Blo 334751 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B18727703 : Blo 334751 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B3622265 : Blo 334751 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B640639 : Blo 334751 640639 := bstep (se 1 (by rfl) ⟨480479, by rfl⟩ : syracuseStep 640639 = 960959) B960959
theorem B1133729 : Blo 334751 1133729 := bstep (se 2 (by rfl) ⟨425148, by rfl⟩ : syracuseStep 1133729 = 850297) B850297
theorem B9096425 : Blo 334751 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1625579 : Blo 334751 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B577145 : Blo 334751 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B3461885 : Blo 334751 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B8608031 : Blo 334751 8608031 := bstep (se 1 (by rfl) ⟨6456023, by rfl⟩ : syracuseStep 8608031 = 12912047) B12912047
theorem B3267071 : Blo 334751 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B2874811 : Blo 334751 2874811 := bstep (se 1 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 2874811 = 4312217) B4312217
theorem B1138535 : Blo 334751 1138535 := bstep (se 1 (by rfl) ⟨853901, by rfl⟩ : syracuseStep 1138535 = 1707803) B1707803
theorem B1140479 : Blo 334751 1140479 := bstep (se 1 (by rfl) ⟨855359, by rfl⟩ : syracuseStep 1140479 = 1710719) B1710719
theorem B2877545 : Blo 334751 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B1271983 : Blo 334751 1271983 := bstep (se 1 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 1271983 = 1907975) B1907975
theorem B10414493 : Blo 334751 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1141343 : Blo 334751 1141343 := bstep (se 1 (by rfl) ⟨856007, by rfl⟩ : syracuseStep 1141343 = 1712015) B1712015
theorem B715559 : Blo 334751 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B1207379 : Blo 334751 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B6451103 : Blo 334751 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B1799333 : Blo 334751 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B1078697 : Blo 334751 1078697 := bstep (se 2 (by rfl) ⟨404511, by rfl⟩ : syracuseStep 1078697 = 809023) B809023
theorem B1275371 : Blo 334751 1275371 := bstep (se 1 (by rfl) ⟨956528, by rfl⟩ : syracuseStep 1275371 = 1913057) B1913057
theorem B1703915 : Blo 334751 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B12485135 : Blo 334751 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B1705373 : Blo 334751 1705373 := bstep (se 3 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 1705373 = 639515) B639515
theorem B853487 : Blo 334751 853487 := bstep (se 1 (by rfl) ⟨640115, by rfl⟩ : syracuseStep 853487 = 1280231) B1280231
theorem B755819 : Blo 334751 755819 := bstep (se 1 (by rfl) ⟨566864, by rfl⟩ : syracuseStep 755819 = 1133729) B1133729
theorem B6064283 : Blo 334751 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B854185 : Blo 334751 854185 := bstep (se 2 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 854185 = 640639) B640639
theorem B1083719 : Blo 334751 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B854783 : Blo 334751 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B14879623 : Blo 334751 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B5738687 : Blo 334751 5738687 := bstep (se 1 (by rfl) ⟨4304015, by rfl⟩ : syracuseStep 5738687 = 8608031) B8608031
theorem B759023 : Blo 334751 759023 := bstep (se 1 (by rfl) ⟨569267, by rfl⟩ : syracuseStep 759023 = 1138535) B1138535
theorem B4593023 : Blo 334751 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B759977 : Blo 334751 759977 := bstep (se 2 (by rfl) ⟨284991, by rfl⟩ : syracuseStep 759977 = 569983) B569983
theorem B760319 : Blo 334751 760319 := bstep (se 1 (by rfl) ⟨570239, by rfl⟩ : syracuseStep 760319 = 1140479) B1140479
theorem B760895 : Blo 334751 760895 := bstep (se 1 (by rfl) ⟨570671, by rfl⟩ : syracuseStep 760895 = 1141343) B1141343
theorem B1908157 : Blo 334751 1908157 := bstep (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) B715559
theorem B1908431 : Blo 334751 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B4333337 : Blo 334751 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B4300735 : Blo 334751 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B2564135 : Blo 334751 2564135 := bstep (se 1 (by rfl) ⟨1923101, by rfl⟩ : syracuseStep 2564135 = 3846203) B3846203
theorem B336623 : Blo 334751 336623 := bstep (se 1 (by rfl) ⟨252467, by rfl⟩ : syracuseStep 336623 = 504935) B504935
theorem B337135 : Blo 334751 337135 := bstep (se 1 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 337135 = 505703) B505703
theorem B337151 : Blo 334751 337151 := bstep (se 1 (by rfl) ⟨252863, by rfl⟩ : syracuseStep 337151 = 505727) B505727
theorem B338087 : Blo 334751 338087 := bstep (se 1 (by rfl) ⟨253565, by rfl⟩ : syracuseStep 338087 = 507131) B507131
theorem B503279 : Blo 334751 503279 := bstep (se 1 (by rfl) ⟨377459, by rfl⟩ : syracuseStep 503279 = 754919) B754919
theorem B2307923 : Blo 334751 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B24525017 : Blo 334751 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B637807 : Blo 334751 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B2178047 : Blo 334751 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B770075 : Blo 334751 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B1918363 : Blo 334751 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B804919 : Blo 334751 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B1821467 : Blo 334751 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B379759 : Blo 334751 379759 := bstep (se 1 (by rfl) ⟨284819, by rfl⟩ : syracuseStep 379759 = 569639) B569639
theorem B1199555 : Blo 334751 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B46681697 : Blo 334751 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B380623 : Blo 334751 380623 := bstep (se 1 (by rfl) ⟨285467, by rfl⟩ : syracuseStep 380623 = 570935) B570935
theorem B5756183 : Blo 334751 5756183 := bstep (se 1 (by rfl) ⟨4317137, by rfl⟩ : syracuseStep 5756183 = 8634275) B8634275
theorem B1135943 : Blo 334751 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B2873171 : Blo 334751 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B2414843 : Blo 334751 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1695977 : Blo 334751 1695977 := bstep (se 2 (by rfl) ⟨635991, by rfl⟩ : syracuseStep 1695977 = 1271983) B1271983
theorem B1273259 : Blo 334751 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B6942995 : Blo 334751 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B5273119 : Blo 334751 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B358015 : Blo 334751 358015 := bstep (se 1 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 358015 = 537023) B537023
theorem B719131 : Blo 334751 719131 := bstep (se 1 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 719131 = 1078697) B1078697
theorem B850247 : Blo 334751 850247 := bstep (se 1 (by rfl) ⟨637685, by rfl⟩ : syracuseStep 850247 = 1275371) B1275371
theorem B1539053 : Blo 334751 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B3833081 : Blo 334751 3833081 := bstep (se 2 (by rfl) ⟨1437405, by rfl⟩ : syracuseStep 3833081 = 2874811) B2874811
theorem B359839 : Blo 334751 359839 := bstep (se 1 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 359839 = 539759) B539759
theorem B425407 : Blo 334751 425407 := bstep (se 1 (by rfl) ⟨319055, by rfl⟩ : syracuseStep 425407 = 638111) B638111
theorem B33293693 : Blo 334751 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B2557817 : Blo 334751 2557817 := bstep (se 2 (by rfl) ⟨959181, by rfl⟩ : syracuseStep 2557817 = 1918363) B1918363
theorem B3837455 : Blo 334751 3837455 := bstep (se 1 (by rfl) ⟨2878091, by rfl⟩ : syracuseStep 3837455 = 5756183) B5756183
theorem B757295 : Blo 334751 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B1609895 : Blo 334751 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B2888891 : Blo 334751 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B1709423 : Blo 334751 1709423 := bstep (se 1 (by rfl) ⟨1282067, by rfl⟩ : syracuseStep 1709423 = 2564135) B2564135
theorem B2889917 : Blo 334751 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B4857245 : Blo 334751 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B335519 : Blo 334751 335519 := bstep (se 1 (by rfl) ⟨251639, by rfl⟩ : syracuseStep 335519 = 503279) B503279
theorem B5808125 : Blo 334751 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B28123301 : Blo 334751 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4628663 : Blo 334751 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B958841 : Blo 334751 958841 := bstep (se 2 (by rfl) ⟨359565, by rfl⟩ : syracuseStep 958841 = 719131) B719131
theorem B566831 : Blo 334751 566831 := bstep (se 1 (by rfl) ⟨425123, by rfl⟩ : syracuseStep 566831 = 850247) B850247
theorem B567209 : Blo 334751 567209 := bstep (se 2 (by rfl) ⟨212703, by rfl⟩ : syracuseStep 567209 = 425407) B425407
theorem B1026035 : Blo 334751 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B568991 : Blo 334751 568991 := bstep (se 1 (by rfl) ⟨426743, by rfl⟩ : syracuseStep 568991 = 853487) B853487
theorem B503879 : Blo 334751 503879 := bstep (se 1 (by rfl) ⟨377909, by rfl⟩ : syracuseStep 503879 = 755819) B755819
theorem B4042855 : Blo 334751 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B569855 : Blo 334751 569855 := bstep (se 1 (by rfl) ⟨427391, by rfl⟩ : syracuseStep 569855 = 854783) B854783
theorem B799703 : Blo 334751 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B506015 : Blo 334751 506015 := bstep (se 1 (by rfl) ⟨379511, by rfl⟩ : syracuseStep 506015 = 759023) B759023
theorem B3062015 : Blo 334751 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B506345 : Blo 334751 506345 := bstep (se 2 (by rfl) ⟨189879, by rfl⟩ : syracuseStep 506345 = 379759) B379759
theorem B19839497 : Blo 334751 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1915447 : Blo 334751 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B506651 : Blo 334751 506651 := bstep (se 1 (by rfl) ⟨379988, by rfl⟩ : syracuseStep 506651 = 759977) B759977
theorem B506879 : Blo 334751 506879 := bstep (se 1 (by rfl) ⟨380159, by rfl⟩ : syracuseStep 506879 = 760319) B760319
theorem B507263 : Blo 334751 507263 := bstep (se 1 (by rfl) ⟨380447, by rfl⟩ : syracuseStep 507263 = 760895) B760895
theorem B507497 : Blo 334751 507497 := bstep (se 2 (by rfl) ⟨190311, by rfl⟩ : syracuseStep 507497 = 380623) B380623
theorem B1130651 : Blo 334751 1130651 := bstep (se 1 (by rfl) ⟨847988, by rfl⟩ : syracuseStep 1130651 = 1695977) B1695977
theorem B477353 : Blo 334751 477353 := bstep (se 2 (by rfl) ⟨179007, by rfl⟩ : syracuseStep 477353 = 358015) B358015
theorem B479785 : Blo 334751 479785 := bstep (se 2 (by rfl) ⟨179919, by rfl⟩ : syracuseStep 479785 = 359839) B359839
theorem B2544209 : Blo 334751 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B513383 : Blo 334751 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B1136915 : Blo 334751 1136915 := bstep (se 1 (by rfl) ⟨852686, by rfl⟩ : syracuseStep 1136915 = 1705373) B1705373
theorem B31121131 : Blo 334751 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B1073225 : Blo 334751 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B3825791 : Blo 334751 3825791 := bstep (se 1 (by rfl) ⟨2869343, by rfl⟩ : syracuseStep 3825791 = 5738687) B5738687
theorem B1138913 : Blo 334751 1138913 := bstep (se 2 (by rfl) ⟨427092, by rfl⟩ : syracuseStep 1138913 = 854185) B854185
theorem B1272287 : Blo 334751 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B848839 : Blo 334751 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B850409 : Blo 334751 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B1538615 : Blo 334751 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B16350011 : Blo 334751 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B2555387 : Blo 334751 2555387 := bstep (se 1 (by rfl) ⟨1916540, by rfl⟩ : syracuseStep 2555387 = 3833081) B3833081
theorem B5734313 : Blo 334751 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B753767 : Blo 334751 753767 := bstep (se 1 (by rfl) ⟨565325, by rfl⟩ : syracuseStep 753767 = 1130651) B1130651
theorem B1705211 : Blo 334751 1705211 := bstep (se 1 (by rfl) ⟨1278908, by rfl⟩ : syracuseStep 1705211 = 2557817) B2557817
theorem B2558303 : Blo 334751 2558303 := bstep (se 1 (by rfl) ⟨1918727, by rfl⟩ : syracuseStep 2558303 = 3837455) B3837455
theorem B757943 : Blo 334751 757943 := bstep (se 1 (by rfl) ⟨568457, by rfl⟩ : syracuseStep 757943 = 1136915) B1136915
theorem B3872083 : Blo 334751 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B18748867 : Blo 334751 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B3085775 : Blo 334751 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B759275 : Blo 334751 759275 := bstep (se 1 (by rfl) ⟨569456, by rfl⟩ : syracuseStep 759275 = 1138913) B1138913
theorem B4102973 : Blo 334751 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B335919 : Blo 334751 335919 := bstep (se 1 (by rfl) ⟨251939, by rfl⟩ : syracuseStep 335919 = 503879) B503879
theorem B533135 : Blo 334751 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B337343 : Blo 334751 337343 := bstep (se 1 (by rfl) ⟨253007, by rfl⟩ : syracuseStep 337343 = 506015) B506015
theorem B2041343 : Blo 334751 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B566939 : Blo 334751 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B337563 : Blo 334751 337563 := bstep (se 1 (by rfl) ⟨253172, by rfl⟩ : syracuseStep 337563 = 506345) B506345
theorem B337767 : Blo 334751 337767 := bstep (se 1 (by rfl) ⟨253325, by rfl⟩ : syracuseStep 337767 = 506651) B506651
theorem B337919 : Blo 334751 337919 := bstep (se 1 (by rfl) ⟨253439, by rfl⟩ : syracuseStep 337919 = 506879) B506879
theorem B338175 : Blo 334751 338175 := bstep (se 1 (by rfl) ⟨253631, by rfl⟩ : syracuseStep 338175 = 507263) B507263
theorem B41494841 : Blo 334751 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B338331 : Blo 334751 338331 := bstep (se 1 (by rfl) ⟨253748, by rfl⟩ : syracuseStep 338331 = 507497) B507497
theorem B22195795 : Blo 334751 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B504863 : Blo 334751 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B5390473 : Blo 334751 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B639227 : Blo 334751 639227 := bstep (se 1 (by rfl) ⟨479420, by rfl⟩ : syracuseStep 639227 = 958841) B958841
theorem B639713 : Blo 334751 639713 := bstep (se 2 (by rfl) ⟨239892, by rfl⟩ : syracuseStep 639713 = 479785) B479785
theorem B377887 : Blo 334751 377887 := bstep (se 1 (by rfl) ⟨283415, by rfl⟩ : syracuseStep 377887 = 566831) B566831
theorem B1131785 : Blo 334751 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B378139 : Blo 334751 378139 := bstep (se 1 (by rfl) ⟨283604, by rfl⟩ : syracuseStep 378139 = 567209) B567209
theorem B52905325 : Blo 334751 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B379327 : Blo 334751 379327 := bstep (se 1 (by rfl) ⟨284495, by rfl⟩ : syracuseStep 379327 = 568991) B568991
theorem B379903 : Blo 334751 379903 := bstep (se 1 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 379903 = 569855) B569855
theorem B10900007 : Blo 334751 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B3822875 : Blo 334751 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B1073263 : Blo 334751 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B1696139 : Blo 334751 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B1925927 : Blo 334751 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B1139615 : Blo 334751 1139615 := bstep (se 1 (by rfl) ⟨854711, by rfl⟩ : syracuseStep 1139615 = 1709423) B1709423
theorem B1369021 : Blo 334751 1369021 := bstep (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) B513383
theorem B1926611 : Blo 334751 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B3238163 : Blo 334751 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B715483 : Blo 334751 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B2550527 : Blo 334751 2550527 := bstep (se 1 (by rfl) ⟨1912895, by rfl⟩ : syracuseStep 2550527 = 3825791) B3825791
theorem B1272941 : Blo 334751 1272941 := bstep (se 3 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 1272941 = 477353) B477353
theorem B684023 : Blo 334751 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B848191 : Blo 334751 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B2553929 : Blo 334751 2553929 := bstep (se 2 (by rfl) ⟨957723, by rfl⟩ : syracuseStep 2553929 = 1915447) B1915447
theorem B1703591 : Blo 334751 1703591 := bstep (se 1 (by rfl) ⟨1277693, by rfl⟩ : syracuseStep 1703591 = 2555387) B2555387
theorem B426151 : Blo 334751 426151 := bstep (se 1 (by rfl) ⟨319613, by rfl⟩ : syracuseStep 426151 = 639227) B639227
theorem B426475 : Blo 334751 426475 := bstep (se 1 (by rfl) ⟨319856, by rfl⟩ : syracuseStep 426475 = 639713) B639713
theorem B754523 : Blo 334751 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B1705535 : Blo 334751 1705535 := bstep (se 1 (by rfl) ⟨1279151, by rfl⟩ : syracuseStep 1705535 = 2558303) B2558303
theorem B953977 : Blo 334751 953977 := bstep (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) B715483
theorem B29594393 : Blo 334751 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B1283951 : Blo 334751 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B759743 : Blo 334751 759743 := bstep (se 1 (by rfl) ⟨569807, by rfl⟩ : syracuseStep 759743 = 1139615) B1139615
theorem B1284407 : Blo 334751 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B27663227 : Blo 334751 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B336575 : Blo 334751 336575 := bstep (se 1 (by rfl) ⟨252431, by rfl⟩ : syracuseStep 336575 = 504863) B504863
theorem B502511 : Blo 334751 502511 := bstep (se 1 (by rfl) ⟨376883, by rfl⟩ : syracuseStep 502511 = 753767) B753767
theorem B7187297 : Blo 334751 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B503849 : Blo 334751 503849 := bstep (se 2 (by rfl) ⟨188943, by rfl⟩ : syracuseStep 503849 = 377887) B377887
theorem B504185 : Blo 334751 504185 := bstep (se 2 (by rfl) ⟨189069, by rfl⟩ : syracuseStep 504185 = 378139) B378139
theorem B505295 : Blo 334751 505295 := bstep (se 1 (by rfl) ⟨378971, by rfl⟩ : syracuseStep 505295 = 757943) B757943
theorem B505769 : Blo 334751 505769 := bstep (se 2 (by rfl) ⟨189663, by rfl⟩ : syracuseStep 505769 = 379327) B379327
theorem B506183 : Blo 334751 506183 := bstep (se 1 (by rfl) ⟨379637, by rfl⟩ : syracuseStep 506183 = 759275) B759275
theorem B506537 : Blo 334751 506537 := bstep (se 2 (by rfl) ⟨189951, by rfl⟩ : syracuseStep 506537 = 379903) B379903
theorem B2735315 : Blo 334751 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B1130759 : Blo 334751 1130759 := bstep (se 1 (by rfl) ⟨848069, by rfl⟩ : syracuseStep 1130759 = 1696139) B1696139
theorem B1130921 : Blo 334751 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B1360895 : Blo 334751 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B377959 : Blo 334751 377959 := bstep (se 1 (by rfl) ⟨283469, by rfl⟩ : syracuseStep 377959 = 566939) B566939
theorem B5162777 : Blo 334751 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B1135727 : Blo 334751 1135727 := bstep (se 1 (by rfl) ⟨851795, by rfl⟩ : syracuseStep 1135727 = 1703591) B1703591
theorem B1824061 : Blo 334751 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B1431017 : Blo 334751 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B1136807 : Blo 334751 1136807 := bstep (se 1 (by rfl) ⟨852605, by rfl⟩ : syracuseStep 1136807 = 1705211) B1705211
theorem B1825361 : Blo 334751 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B70540433 : Blo 334751 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B7266671 : Blo 334751 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B2548583 : Blo 334751 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B2057183 : Blo 334751 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B355423 : Blo 334751 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B2158775 : Blo 334751 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B1700351 : Blo 334751 1700351 := bstep (se 1 (by rfl) ⟨1275263, by rfl⟩ : syracuseStep 1700351 = 2550527) B2550527
theorem B24998489 : Blo 334751 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B848627 : Blo 334751 848627 := bstep (se 1 (by rfl) ⟨636470, by rfl⟩ : syracuseStep 848627 = 1272941) B1272941
theorem B1702619 : Blo 334751 1702619 := bstep (se 1 (by rfl) ⟨1276964, by rfl⟩ : syracuseStep 1702619 = 2553929) B2553929
theorem B753839 : Blo 334751 753839 := bstep (se 1 (by rfl) ⟨565379, by rfl⟩ : syracuseStep 753839 = 1130759) B1130759
theorem B753947 : Blo 334751 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B3441851 : Blo 334751 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B19729595 : Blo 334751 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B757151 : Blo 334751 757151 := bstep (se 1 (by rfl) ⟨567863, by rfl⟩ : syracuseStep 757151 = 1135727) B1135727
theorem B954011 : Blo 334751 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B855967 : Blo 334751 855967 := bstep (se 1 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 855967 = 1283951) B1283951
theorem B757871 : Blo 334751 757871 := bstep (se 1 (by rfl) ⟨568403, by rfl⟩ : syracuseStep 757871 = 1136807) B1136807
theorem B856271 : Blo 334751 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B1216907 : Blo 334751 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B47026955 : Blo 334751 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B2432081 : Blo 334751 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B335007 : Blo 334751 335007 := bstep (se 1 (by rfl) ⟨251255, by rfl⟩ : syracuseStep 335007 = 502511) B502511
theorem B335899 : Blo 334751 335899 := bstep (se 1 (by rfl) ⟨251924, by rfl⟩ : syracuseStep 335899 = 503849) B503849
theorem B336123 : Blo 334751 336123 := bstep (se 1 (by rfl) ⟨252092, by rfl⟩ : syracuseStep 336123 = 504185) B504185
theorem B565751 : Blo 334751 565751 := bstep (se 1 (by rfl) ⟨424313, by rfl⟩ : syracuseStep 565751 = 848627) B848627
theorem B336863 : Blo 334751 336863 := bstep (se 1 (by rfl) ⟨252647, by rfl⟩ : syracuseStep 336863 = 505295) B505295
theorem B337179 : Blo 334751 337179 := bstep (se 1 (by rfl) ⟨252884, by rfl⟩ : syracuseStep 337179 = 505769) B505769
theorem B337455 : Blo 334751 337455 := bstep (se 1 (by rfl) ⟨253091, by rfl⟩ : syracuseStep 337455 = 506183) B506183
theorem B337691 : Blo 334751 337691 := bstep (se 1 (by rfl) ⟨253268, by rfl⟩ : syracuseStep 337691 = 506537) B506537
theorem B568201 : Blo 334751 568201 := bstep (se 2 (by rfl) ⟨213075, by rfl⟩ : syracuseStep 568201 = 426151) B426151
theorem B503015 : Blo 334751 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B568633 : Blo 334751 568633 := bstep (se 2 (by rfl) ⟨213237, by rfl⟩ : syracuseStep 568633 = 426475) B426475
theorem B503945 : Blo 334751 503945 := bstep (se 2 (by rfl) ⟨188979, by rfl⟩ : syracuseStep 503945 = 377959) B377959
theorem B506495 : Blo 334751 506495 := bstep (se 1 (by rfl) ⟨379871, by rfl⟩ : syracuseStep 506495 = 759743) B759743
theorem B473897 : Blo 334751 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B1133567 : Blo 334751 1133567 := bstep (se 1 (by rfl) ⟨850175, by rfl⟩ : syracuseStep 1133567 = 1700351) B1700351
theorem B16665659 : Blo 334751 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B76664501 : Blo 334751 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B1135079 : Blo 334751 1135079 := bstep (se 1 (by rfl) ⟨851309, by rfl⟩ : syracuseStep 1135079 = 1702619) B1702619
theorem B1823543 : Blo 334751 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B1137023 : Blo 334751 1137023 := bstep (se 1 (by rfl) ⟨852767, by rfl⟩ : syracuseStep 1137023 = 1705535) B1705535
theorem B3629053 : Blo 334751 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B18442151 : Blo 334751 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B1271969 : Blo 334751 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B4844447 : Blo 334751 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B1699055 : Blo 334751 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B1371455 : Blo 334751 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B1439183 : Blo 334751 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B2294567 : Blo 334751 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B755711 : Blo 334751 755711 := bstep (se 1 (by rfl) ⟨566783, by rfl⟩ : syracuseStep 755711 = 1133567) B1133567
theorem B11110439 : Blo 334751 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B756719 : Blo 334751 756719 := bstep (se 1 (by rfl) ⟨567539, by rfl⟩ : syracuseStep 756719 = 1135079) B1135079
theorem B1215695 : Blo 334751 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B757601 : Blo 334751 757601 := bstep (se 2 (by rfl) ⟨284100, by rfl⟩ : syracuseStep 757601 = 568201) B568201
theorem B758015 : Blo 334751 758015 := bstep (se 1 (by rfl) ⟨568511, by rfl⟩ : syracuseStep 758015 = 1137023) B1137023
theorem B758177 : Blo 334751 758177 := bstep (se 2 (by rfl) ⟨284316, by rfl⟩ : syracuseStep 758177 = 568633) B568633
theorem B12294767 : Blo 334751 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B335343 : Blo 334751 335343 := bstep (se 1 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 335343 = 503015) B503015
theorem B335963 : Blo 334751 335963 := bstep (se 1 (by rfl) ⟨251972, by rfl⟩ : syracuseStep 335963 = 503945) B503945
theorem B959455 : Blo 334751 959455 := bstep (se 1 (by rfl) ⟨719591, by rfl⟩ : syracuseStep 959455 = 1439183) B1439183
theorem B337663 : Blo 334751 337663 := bstep (se 1 (by rfl) ⟨253247, by rfl⟩ : syracuseStep 337663 = 506495) B506495
theorem B502559 : Blo 334751 502559 := bstep (se 1 (by rfl) ⟨376919, by rfl⟩ : syracuseStep 502559 = 753839) B753839
theorem B502631 : Blo 334751 502631 := bstep (se 1 (by rfl) ⟨376973, by rfl⟩ : syracuseStep 502631 = 753947) B753947
theorem B13153063 : Blo 334751 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B504767 : Blo 334751 504767 := bstep (se 1 (by rfl) ⟨378575, by rfl⟩ : syracuseStep 504767 = 757151) B757151
theorem B636007 : Blo 334751 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B505247 : Blo 334751 505247 := bstep (se 1 (by rfl) ⟨378935, by rfl⟩ : syracuseStep 505247 = 757871) B757871
theorem B570847 : Blo 334751 570847 := bstep (se 1 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 570847 = 856271) B856271
theorem B1621387 : Blo 334751 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B377167 : Blo 334751 377167 := bstep (se 1 (by rfl) ⟨282875, by rfl⟩ : syracuseStep 377167 = 565751) B565751
theorem B3229631 : Blo 334751 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B1263725 : Blo 334751 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B1132703 : Blo 334751 1132703 := bstep (se 1 (by rfl) ⟨849527, by rfl⟩ : syracuseStep 1132703 = 1699055) B1699055
theorem B4838737 : Blo 334751 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B51109667 : Blo 334751 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B811271 : Blo 334751 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B31351303 : Blo 334751 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B1141289 : Blo 334751 1141289 := bstep (se 2 (by rfl) ⟨427983, by rfl⟩ : syracuseStep 1141289 = 855967) B855967
theorem B847979 : Blo 334751 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B914303 : Blo 334751 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B1279273 : Blo 334751 1279273 := bstep (se 2 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 1279273 = 959455) B959455
theorem B7406959 : Blo 334751 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B755135 : Blo 334751 755135 := bstep (se 1 (by rfl) ⟨566351, by rfl⟩ : syracuseStep 755135 = 1132703) B1132703
theorem B8196511 : Blo 334751 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B17537417 : Blo 334751 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B760859 : Blo 334751 760859 := bstep (se 1 (by rfl) ⟨570644, by rfl⟩ : syracuseStep 760859 = 1141289) B1141289
theorem B335039 : Blo 334751 335039 := bstep (se 1 (by rfl) ⟨251279, by rfl⟩ : syracuseStep 335039 = 502559) B502559
theorem B335087 : Blo 334751 335087 := bstep (se 1 (by rfl) ⟨251315, by rfl⟩ : syracuseStep 335087 = 502631) B502631
theorem B761129 : Blo 334751 761129 := bstep (se 2 (by rfl) ⟨285423, by rfl⟩ : syracuseStep 761129 = 570847) B570847
theorem B565319 : Blo 334751 565319 := bstep (se 1 (by rfl) ⟨423989, by rfl⟩ : syracuseStep 565319 = 847979) B847979
theorem B336511 : Blo 334751 336511 := bstep (se 1 (by rfl) ⟨252383, by rfl⟩ : syracuseStep 336511 = 504767) B504767
theorem B336831 : Blo 334751 336831 := bstep (se 1 (by rfl) ⟨252623, by rfl⟩ : syracuseStep 336831 = 505247) B505247
theorem B502889 : Blo 334751 502889 := bstep (se 2 (by rfl) ⟨188583, by rfl⟩ : syracuseStep 502889 = 377167) B377167
theorem B503807 : Blo 334751 503807 := bstep (se 1 (by rfl) ⟨377855, by rfl⟩ : syracuseStep 503807 = 755711) B755711
theorem B504479 : Blo 334751 504479 := bstep (se 1 (by rfl) ⟨378359, by rfl⟩ : syracuseStep 504479 = 756719) B756719
theorem B505067 : Blo 334751 505067 := bstep (se 1 (by rfl) ⟨378800, by rfl⟩ : syracuseStep 505067 = 757601) B757601
theorem B505343 : Blo 334751 505343 := bstep (se 1 (by rfl) ⟨379007, by rfl⟩ : syracuseStep 505343 = 758015) B758015
theorem B505451 : Blo 334751 505451 := bstep (se 1 (by rfl) ⟨379088, by rfl⟩ : syracuseStep 505451 = 758177) B758177
theorem B540847 : Blo 334751 540847 := bstep (se 1 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 540847 = 811271) B811271
theorem B609535 : Blo 334751 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B1529711 : Blo 334751 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B2153087 : Blo 334751 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B842483 : Blo 334751 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B167206949 : Blo 334751 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B34073111 : Blo 334751 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B848009 : Blo 334751 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B6451649 : Blo 334751 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B8647397 : Blo 334751 8647397 := bstep (se 4 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 8647397 = 1621387) B1621387
theorem B3241853 : Blo 334751 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B2884517 : Blo 334751 2884517 := bstep (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) B540847
theorem B1705697 : Blo 334751 1705697 := bstep (se 2 (by rfl) ⟨639636, by rfl⟩ : syracuseStep 1705697 = 1279273) B1279273
theorem B1019807 : Blo 334751 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B561655 : Blo 334751 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B3250853 : Blo 334751 3250853 := bstep (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) B609535
theorem B22715407 : Blo 334751 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B335259 : Blo 334751 335259 := bstep (se 1 (by rfl) ⟨251444, by rfl⟩ : syracuseStep 335259 = 502889) B502889
theorem B335871 : Blo 334751 335871 := bstep (se 1 (by rfl) ⟨251903, by rfl⟩ : syracuseStep 335871 = 503807) B503807
theorem B565339 : Blo 334751 565339 := bstep (se 1 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 565339 = 848009) B848009
theorem B4301099 : Blo 334751 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B336319 : Blo 334751 336319 := bstep (se 1 (by rfl) ⟨252239, by rfl⟩ : syracuseStep 336319 = 504479) B504479
theorem B336711 : Blo 334751 336711 := bstep (se 1 (by rfl) ⟨252533, by rfl⟩ : syracuseStep 336711 = 505067) B505067
theorem B336895 : Blo 334751 336895 := bstep (se 1 (by rfl) ⟨252671, by rfl⟩ : syracuseStep 336895 = 505343) B505343
theorem B336967 : Blo 334751 336967 := bstep (se 1 (by rfl) ⟨252725, by rfl⟩ : syracuseStep 336967 = 505451) B505451
theorem B503423 : Blo 334751 503423 := bstep (se 1 (by rfl) ⟨377567, by rfl⟩ : syracuseStep 503423 = 755135) B755135
theorem B9875945 : Blo 334751 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B507239 : Blo 334751 507239 := bstep (se 1 (by rfl) ⟨380429, by rfl⟩ : syracuseStep 507239 = 760859) B760859
theorem B507419 : Blo 334751 507419 := bstep (se 1 (by rfl) ⟨380564, by rfl⟩ : syracuseStep 507419 = 761129) B761129
theorem B376879 : Blo 334751 376879 := bstep (se 1 (by rfl) ⟨282659, by rfl⟩ : syracuseStep 376879 = 565319) B565319
theorem B10928681 : Blo 334751 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B11691611 : Blo 334751 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1435391 : Blo 334751 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B111471299 : Blo 334751 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B5764931 : Blo 334751 5764931 := bstep (se 1 (by rfl) ⟨4323698, by rfl⟩ : syracuseStep 5764931 = 8647397) B8647397
theorem B2161235 : Blo 334751 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B753785 : Blo 334751 753785 := bstep (se 2 (by rfl) ⟨282669, by rfl⟩ : syracuseStep 753785 = 565339) B565339
theorem B2167235 : Blo 334751 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B956927 : Blo 334751 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B335615 : Blo 334751 335615 := bstep (se 1 (by rfl) ⟨251711, by rfl⟩ : syracuseStep 335615 = 503423) B503423
theorem B3843287 : Blo 334751 3843287 := bstep (se 1 (by rfl) ⟨2882465, by rfl⟩ : syracuseStep 3843287 = 5764931) B5764931
theorem B30287209 : Blo 334751 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B338159 : Blo 334751 338159 := bstep (se 1 (by rfl) ⟨253619, by rfl⟩ : syracuseStep 338159 = 507239) B507239
theorem B338279 : Blo 334751 338279 := bstep (se 1 (by rfl) ⟨253709, by rfl⟩ : syracuseStep 338279 = 507419) B507419
theorem B502505 : Blo 334751 502505 := bstep (se 2 (by rfl) ⟨188439, by rfl⟩ : syracuseStep 502505 = 376879) B376879
theorem B7285787 : Blo 334751 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B2867399 : Blo 334751 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B1923011 : Blo 334751 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B1137131 : Blo 334751 1137131 := bstep (se 1 (by rfl) ⟨852848, by rfl⟩ : syracuseStep 1137131 = 1705697) B1705697
theorem B26335853 : Blo 334751 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B679871 : Blo 334751 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B748873 : Blo 334751 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B7794407 : Blo 334751 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B74314199 : Blo 334751 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B1440823 : Blo 334751 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B1444823 : Blo 334751 1444823 := bstep (se 1 (by rfl) ⟨1083617, by rfl⟩ : syracuseStep 1444823 = 2167235) B2167235
theorem B1282007 : Blo 334751 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B758087 : Blo 334751 758087 := bstep (se 1 (by rfl) ⟨568565, by rfl⟩ : syracuseStep 758087 = 1137131) B1137131
theorem B2562191 : Blo 334751 2562191 := bstep (se 1 (by rfl) ⟨1921643, by rfl⟩ : syracuseStep 2562191 = 3843287) B3843287
theorem B335003 : Blo 334751 335003 := bstep (se 1 (by rfl) ⟨251252, by rfl⟩ : syracuseStep 335003 = 502505) B502505
theorem B4857191 : Blo 334751 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B1812989 : Blo 334751 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B502523 : Blo 334751 502523 := bstep (se 1 (by rfl) ⟨376892, by rfl⟩ : syracuseStep 502523 = 753785) B753785
theorem B1911599 : Blo 334751 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B40382945 : Blo 334751 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B637951 : Blo 334751 637951 := bstep (se 1 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 637951 = 956927) B956927
theorem B998497 : Blo 334751 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B5196271 : Blo 334751 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B1921097 : Blo 334751 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B17557235 : Blo 334751 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B49542799 : Blo 334751 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B854671 : Blo 334751 854671 := bstep (se 1 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 854671 = 1282007) B1282007
theorem B1280731 : Blo 334751 1280731 := bstep (se 1 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 1280731 = 1921097) B1921097
theorem B1708127 : Blo 334751 1708127 := bstep (se 1 (by rfl) ⟨1281095, by rfl⟩ : syracuseStep 1708127 = 2562191) B2562191
theorem B11704823 : Blo 334751 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B335015 : Blo 334751 335015 := bstep (se 1 (by rfl) ⟨251261, by rfl⟩ : syracuseStep 335015 = 502523) B502523
theorem B963215 : Blo 334751 963215 := bstep (se 1 (by rfl) ⟨722411, by rfl⟩ : syracuseStep 963215 = 1444823) B1444823
theorem B505391 : Blo 334751 505391 := bstep (se 1 (by rfl) ⟨379043, by rfl⟩ : syracuseStep 505391 = 758087) B758087
theorem B6928361 : Blo 334751 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B4834637 : Blo 334751 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B26921963 : Blo 334751 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1331329 : Blo 334751 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B3238127 : Blo 334751 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B1274399 : Blo 334751 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B66057065 : Blo 334751 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B850601 : Blo 334751 850601 := bstep (se 2 (by rfl) ⟨318975, by rfl⟩ : syracuseStep 850601 = 637951) B637951
theorem B1707641 : Blo 334751 1707641 := bstep (se 2 (by rfl) ⟨640365, by rfl⟩ : syracuseStep 1707641 = 1280731) B1280731
theorem B7803215 : Blo 334751 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B1775105 : Blo 334751 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B336927 : Blo 334751 336927 := bstep (se 1 (by rfl) ⟨252695, by rfl⟩ : syracuseStep 336927 = 505391) B505391
theorem B567067 : Blo 334751 567067 := bstep (se 1 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 567067 = 850601) B850601
theorem B3223091 : Blo 334751 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B642143 : Blo 334751 642143 := bstep (se 1 (by rfl) ⟨481607, by rfl⟩ : syracuseStep 642143 = 963215) B963215
theorem B17947975 : Blo 334751 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1138751 : Blo 334751 1138751 := bstep (se 1 (by rfl) ⟨854063, by rfl⟩ : syracuseStep 1138751 = 1708127) B1708127
theorem B1139561 : Blo 334751 1139561 := bstep (se 2 (by rfl) ⟨427335, by rfl⟩ : syracuseStep 1139561 = 854671) B854671
theorem B2158751 : Blo 334751 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B849599 : Blo 334751 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B44038043 : Blo 334751 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B4618907 : Blo 334751 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B428095 : Blo 334751 428095 := bstep (se 1 (by rfl) ⟨321071, by rfl⟩ : syracuseStep 428095 = 642143) B642143
theorem B756089 : Blo 334751 756089 := bstep (se 2 (by rfl) ⟨283533, by rfl⟩ : syracuseStep 756089 = 567067) B567067
theorem B1183403 : Blo 334751 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B759167 : Blo 334751 759167 := bstep (se 1 (by rfl) ⟨569375, by rfl⟩ : syracuseStep 759167 = 1138751) B1138751
theorem B759707 : Blo 334751 759707 := bstep (se 1 (by rfl) ⟨569780, by rfl⟩ : syracuseStep 759707 = 1139561) B1139561
theorem B566399 : Blo 334751 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B8594909 : Blo 334751 8594909 := bstep (se 3 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 8594909 = 3223091) B3223091
theorem B23930633 : Blo 334751 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B1138427 : Blo 334751 1138427 := bstep (se 1 (by rfl) ⟨853820, by rfl⟩ : syracuseStep 1138427 = 1707641) B1707641
theorem B5202143 : Blo 334751 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B1439167 : Blo 334751 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B29358695 : Blo 334751 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B3079271 : Blo 334751 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B788935 : Blo 334751 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B758951 : Blo 334751 758951 := bstep (se 1 (by rfl) ⟨569213, by rfl⟩ : syracuseStep 758951 = 1138427) B1138427
theorem B19572463 : Blo 334751 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B504059 : Blo 334751 504059 := bstep (se 1 (by rfl) ⟨378044, by rfl⟩ : syracuseStep 504059 = 756089) B756089
theorem B570793 : Blo 334751 570793 := bstep (se 2 (by rfl) ⟨214047, by rfl⟩ : syracuseStep 570793 = 428095) B428095
theorem B506111 : Blo 334751 506111 := bstep (se 1 (by rfl) ⟨379583, by rfl⟩ : syracuseStep 506111 = 759167) B759167
theorem B506471 : Blo 334751 506471 := bstep (se 1 (by rfl) ⟨379853, by rfl⟩ : syracuseStep 506471 = 759707) B759707
theorem B377599 : Blo 334751 377599 := bstep (se 1 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 377599 = 566399) B566399
theorem B1918889 : Blo 334751 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B2052847 : Blo 334751 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B3468095 : Blo 334751 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B5729939 : Blo 334751 5729939 := bstep (se 1 (by rfl) ⟨4297454, by rfl⟩ : syracuseStep 5729939 = 8594909) B8594909
theorem B15953755 : Blo 334751 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B1279259 : Blo 334751 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B1051913 : Blo 334751 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B10948517 : Blo 334751 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B21271673 : Blo 334751 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B761057 : Blo 334751 761057 := bstep (se 2 (by rfl) ⟨285396, by rfl⟩ : syracuseStep 761057 = 570793) B570793
theorem B336039 : Blo 334751 336039 := bstep (se 1 (by rfl) ⟨252029, by rfl⟩ : syracuseStep 336039 = 504059) B504059
theorem B337407 : Blo 334751 337407 := bstep (se 1 (by rfl) ⟨253055, by rfl⟩ : syracuseStep 337407 = 506111) B506111
theorem B337647 : Blo 334751 337647 := bstep (se 1 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 337647 = 506471) B506471
theorem B503465 : Blo 334751 503465 := bstep (se 2 (by rfl) ⟨188799, by rfl⟩ : syracuseStep 503465 = 377599) B377599
theorem B26096617 : Blo 334751 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B505967 : Blo 334751 505967 := bstep (se 1 (by rfl) ⟨379475, by rfl⟩ : syracuseStep 505967 = 758951) B758951
theorem B2312063 : Blo 334751 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B3819959 : Blo 334751 3819959 := bstep (se 1 (by rfl) ⟨2864969, by rfl⟩ : syracuseStep 3819959 = 5729939) B5729939
theorem B852839 : Blo 334751 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B1541375 : Blo 334751 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B56724461 : Blo 334751 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B335643 : Blo 334751 335643 := bstep (se 1 (by rfl) ⟨251732, by rfl⟩ : syracuseStep 335643 = 503465) B503465
theorem B337311 : Blo 334751 337311 := bstep (se 1 (by rfl) ⟨252983, by rfl⟩ : syracuseStep 337311 = 505967) B505967
theorem B507371 : Blo 334751 507371 := bstep (se 1 (by rfl) ⟨380528, by rfl⟩ : syracuseStep 507371 = 761057) B761057
theorem B2805101 : Blo 334751 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B2546639 : Blo 334751 2546639 := bstep (se 1 (by rfl) ⟨1909979, by rfl⟩ : syracuseStep 2546639 = 3819959) B3819959
theorem B7299011 : Blo 334751 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B34795489 : Blo 334751 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B37816307 : Blo 334751 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B1870067 : Blo 334751 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B338247 : Blo 334751 338247 := bstep (se 1 (by rfl) ⟨253685, by rfl⟩ : syracuseStep 338247 = 507371) B507371
theorem B568559 : Blo 334751 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B1027583 : Blo 334751 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B4866007 : Blo 334751 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B1697759 : Blo 334751 1697759 := bstep (se 1 (by rfl) ⟨1273319, by rfl⟩ : syracuseStep 1697759 = 2546639) B2546639
theorem B46393985 : Blo 334751 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B4986845 : Blo 334751 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B25210871 : Blo 334751 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1131839 : Blo 334751 1131839 := bstep (se 1 (by rfl) ⟨848879, by rfl⟩ : syracuseStep 1131839 = 1697759) B1697759
theorem B123717293 : Blo 334751 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B379039 : Blo 334751 379039 := bstep (se 1 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 379039 = 568559) B568559
theorem B685055 : Blo 334751 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B6488009 : Blo 334751 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B754559 : Blo 334751 754559 := bstep (se 1 (by rfl) ⟨565919, by rfl⟩ : syracuseStep 754559 = 1131839) B1131839
theorem B82478195 : Blo 334751 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B505385 : Blo 334751 505385 := bstep (se 2 (by rfl) ⟨189519, by rfl⟩ : syracuseStep 505385 = 379039) B379039
theorem B3324563 : Blo 334751 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B1826813 : Blo 334751 1826813 := bstep (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) B685055
theorem B16807247 : Blo 334751 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B4325339 : Blo 334751 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B54985463 : Blo 334751 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B1217875 : Blo 334751 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B336923 : Blo 334751 336923 := bstep (se 1 (by rfl) ⟨252692, by rfl⟩ : syracuseStep 336923 = 505385) B505385
theorem B503039 : Blo 334751 503039 := bstep (se 1 (by rfl) ⟨377279, by rfl⟩ : syracuseStep 503039 = 754559) B754559
theorem B2216375 : Blo 334751 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B11204831 : Blo 334751 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B2883559 : Blo 334751 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B335359 : Blo 334751 335359 := bstep (se 1 (by rfl) ⟨251519, by rfl⟩ : syracuseStep 335359 = 503039) B503039
theorem B3844745 : Blo 334751 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B1623833 : Blo 334751 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B36656975 : Blo 334751 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B94565333 : Blo 334751 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B7469887 : Blo 334751 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1082555 : Blo 334751 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B2563163 : Blo 334751 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B252174221 : Blo 334751 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B24437983 : Blo 334751 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B9959849 : Blo 334751 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B721703 : Blo 334751 721703 := bstep (se 1 (by rfl) ⟨541277, by rfl⟩ : syracuseStep 721703 = 1082555) B1082555
theorem B1708775 : Blo 334751 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B32583977 : Blo 334751 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B168116147 : Blo 334751 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B6639899 : Blo 334751 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B112077431 : Blo 334751 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B17706397 : Blo 334751 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B481135 : Blo 334751 481135 := bstep (se 1 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 481135 = 721703) B721703
theorem B1139183 : Blo 334751 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B21722651 : Blo 334751 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B759455 : Blo 334751 759455 := bstep (se 1 (by rfl) ⟨569591, by rfl⟩ : syracuseStep 759455 = 1139183) B1139183
theorem B74718287 : Blo 334751 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B23608529 : Blo 334751 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B641513 : Blo 334751 641513 := bstep (se 2 (by rfl) ⟨240567, by rfl⟩ : syracuseStep 641513 = 481135) B481135
theorem B14481767 : Blo 334751 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B427675 : Blo 334751 427675 := bstep (se 1 (by rfl) ⟨320756, by rfl⟩ : syracuseStep 427675 = 641513) B641513
theorem B49812191 : Blo 334751 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B15739019 : Blo 334751 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B506303 : Blo 334751 506303 := bstep (se 1 (by rfl) ⟨379727, by rfl⟩ : syracuseStep 506303 = 759455) B759455
theorem B9654511 : Blo 334751 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B10492679 : Blo 334751 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B337535 : Blo 334751 337535 := bstep (se 1 (by rfl) ⟨253151, by rfl⟩ : syracuseStep 337535 = 506303) B506303
theorem B570233 : Blo 334751 570233 := bstep (se 2 (by rfl) ⟨213837, by rfl⟩ : syracuseStep 570233 = 427675) B427675
theorem B33208127 : Blo 334751 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B12872681 : Blo 334751 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B6995119 : Blo 334751 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B380155 : Blo 334751 380155 := bstep (se 1 (by rfl) ⟨285116, by rfl⟩ : syracuseStep 380155 = 570233) B570233
theorem B22138751 : Blo 334751 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B8581787 : Blo 334751 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B14759167 : Blo 334751 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B506873 : Blo 334751 506873 := bstep (se 2 (by rfl) ⟨190077, by rfl⟩ : syracuseStep 506873 = 380155) B380155
theorem B5721191 : Blo 334751 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B9326825 : Blo 334751 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B337915 : Blo 334751 337915 := bstep (se 1 (by rfl) ⟨253436, by rfl⟩ : syracuseStep 337915 = 506873) B506873
theorem B3814127 : Blo 334751 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B19678889 : Blo 334751 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B6217883 : Blo 334751 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B13119259 : Blo 334751 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B4145255 : Blo 334751 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B2542751 : Blo 334751 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B2763503 : Blo 334751 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1695167 : Blo 334751 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B17492345 : Blo 334751 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1842335 : Blo 334751 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1130111 : Blo 334751 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B11661563 : Blo 334751 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B7774375 : Blo 334751 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B1228223 : Blo 334751 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B753407 : Blo 334751 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B502271 : Blo 334751 502271 := bstep (se 1 (by rfl) ⟨376703, by rfl⟩ : syracuseStep 502271 = 753407) B753407
theorem B10365833 : Blo 334751 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B3275261 : Blo 334751 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B334847 : Blo 334751 334847 := bstep (se 1 (by rfl) ⟨251135, by rfl⟩ : syracuseStep 334847 = 502271) B502271
theorem B2183507 : Blo 334751 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B6910555 : Blo 334751 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B9214073 : Blo 334751 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B1455671 : Blo 334751 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B6142715 : Blo 334751 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B3881789 : Blo 334751 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B4095143 : Blo 334751 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2587859 : Blo 334751 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B2730095 : Blo 334751 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B1725239 : Blo 334751 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B4600637 : Blo 334751 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B1820063 : Blo 334751 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1213375 : Blo 334751 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B3067091 : Blo 334751 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B1617833 : Blo 334751 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B2044727 : Blo 334751 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B1363151 : Blo 334751 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B4314221 : Blo 334751 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B908767 : Blo 334751 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B2876147 : Blo 334751 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B1917431 : Blo 334751 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B1211689 : Blo 334751 1211689 := bstep (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) B908767
theorem B1278287 : Blo 334751 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B1615585 : Blo 334751 1615585 := bstep (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) B1211689
theorem B852191 : Blo 334751 852191 := bstep (se 1 (by rfl) ⟨639143, by rfl⟩ : syracuseStep 852191 = 1278287) B1278287
theorem B2154113 : Blo 334751 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B568127 : Blo 334751 568127 := bstep (se 1 (by rfl) ⟨426095, by rfl⟩ : syracuseStep 568127 = 852191) B852191
theorem B1436075 : Blo 334751 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B957383 : Blo 334751 957383 := bstep (se 1 (by rfl) ⟨718037, by rfl⟩ : syracuseStep 957383 = 1436075) B1436075
theorem B378751 : Blo 334751 378751 := bstep (se 1 (by rfl) ⟨284063, by rfl⟩ : syracuseStep 378751 = 568127) B568127
theorem B505001 : Blo 334751 505001 := bstep (se 2 (by rfl) ⟨189375, by rfl⟩ : syracuseStep 505001 = 378751) B378751
theorem B638255 : Blo 334751 638255 := bstep (se 1 (by rfl) ⟨478691, by rfl⟩ : syracuseStep 638255 = 957383) B957383
theorem B336667 : Blo 334751 336667 := bstep (se 1 (by rfl) ⟨252500, by rfl⟩ : syracuseStep 336667 = 505001) B505001
theorem B425503 : Blo 334751 425503 := bstep (se 1 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 425503 = 638255) B638255
theorem B567337 : Blo 334751 567337 := bstep (se 2 (by rfl) ⟨212751, by rfl⟩ : syracuseStep 567337 = 425503) B425503
theorem B756449 : Blo 334751 756449 := bstep (se 2 (by rfl) ⟨283668, by rfl⟩ : syracuseStep 756449 = 567337) B567337
theorem B504299 : Blo 334751 504299 := bstep (se 1 (by rfl) ⟨378224, by rfl⟩ : syracuseStep 504299 = 756449) B756449
theorem B336199 : Blo 334751 336199 := bstep (se 1 (by rfl) ⟨252149, by rfl⟩ : syracuseStep 336199 = 504299) B504299

theorem C0 (j : ℕ) (h1 : 83687 ≤ j) (h2 : j ≤ 84386) : Blo 334751 (4 * j + 3) := by
  interval_cases j
  · exact B334751
  · exact B334755
  · exact B334759
  · exact B334763
  · exact B334767
  · exact B334771
  · exact B334775
  · exact B334779
  · exact B334783
  · exact B334787
  · exact B334791
  · exact B334795
  · exact B334799
  · exact B334803
  · exact B334807
  · exact B334811
  · exact B334815
  · exact B334819
  · exact B334823
  · exact B334827
  · exact B334831
  · exact B334835
  · exact B334839
  · exact B334843
  · exact B334847
  · exact B334851
  · exact B334855
  · exact B334859
  · exact B334863
  · exact B334867
  · exact B334871
  · exact B334875
  · exact B334879
  · exact B334883
  · exact B334887
  · exact B334891
  · exact B334895
  · exact B334899
  · exact B334903
  · exact B334907
  · exact B334911
  · exact B334915
  · exact B334919
  · exact B334923
  · exact B334927
  · exact B334931
  · exact B334935
  · exact B334939
  · exact B334943
  · exact B334947
  · exact B334951
  · exact B334955
  · exact B334959
  · exact B334963
  · exact B334967
  · exact B334971
  · exact B334975
  · exact B334979
  · exact B334983
  · exact B334987
  · exact B334991
  · exact B334995
  · exact B334999
  · exact B335003
  · exact B335007
  · exact B335011
  · exact B335015
  · exact B335019
  · exact B335023
  · exact B335027
  · exact B335031
  · exact B335035
  · exact B335039
  · exact B335043
  · exact B335047
  · exact B335051
  · exact B335055
  · exact B335059
  · exact B335063
  · exact B335067
  · exact B335071
  · exact B335075
  · exact B335079
  · exact B335083
  · exact B335087
  · exact B335091
  · exact B335095
  · exact B335099
  · exact B335103
  · exact B335107
  · exact B335111
  · exact B335115
  · exact B335119
  · exact B335123
  · exact B335127
  · exact B335131
  · exact B335135
  · exact B335139
  · exact B335143
  · exact B335147
  · exact B335151
  · exact B335155
  · exact B335159
  · exact B335163
  · exact B335167
  · exact B335171
  · exact B335175
  · exact B335179
  · exact B335183
  · exact B335187
  · exact B335191
  · exact B335195
  · exact B335199
  · exact B335203
  · exact B335207
  · exact B335211
  · exact B335215
  · exact B335219
  · exact B335223
  · exact B335227
  · exact B335231
  · exact B335235
  · exact B335239
  · exact B335243
  · exact B335247
  · exact B335251
  · exact B335255
  · exact B335259
  · exact B335263
  · exact B335267
  · exact B335271
  · exact B335275
  · exact B335279
  · exact B335283
  · exact B335287
  · exact B335291
  · exact B335295
  · exact B335299
  · exact B335303
  · exact B335307
  · exact B335311
  · exact B335315
  · exact B335319
  · exact B335323
  · exact B335327
  · exact B335331
  · exact B335335
  · exact B335339
  · exact B335343
  · exact B335347
  · exact B335351
  · exact B335355
  · exact B335359
  · exact B335363
  · exact B335367
  · exact B335371
  · exact B335375
  · exact B335379
  · exact B335383
  · exact B335387
  · exact B335391
  · exact B335395
  · exact B335399
  · exact B335403
  · exact B335407
  · exact B335411
  · exact B335415
  · exact B335419
  · exact B335423
  · exact B335427
  · exact B335431
  · exact B335435
  · exact B335439
  · exact B335443
  · exact B335447
  · exact B335451
  · exact B335455
  · exact B335459
  · exact B335463
  · exact B335467
  · exact B335471
  · exact B335475
  · exact B335479
  · exact B335483
  · exact B335487
  · exact B335491
  · exact B335495
  · exact B335499
  · exact B335503
  · exact B335507
  · exact B335511
  · exact B335515
  · exact B335519
  · exact B335523
  · exact B335527
  · exact B335531
  · exact B335535
  · exact B335539
  · exact B335543
  · exact B335547
  · exact B335551
  · exact B335555
  · exact B335559
  · exact B335563
  · exact B335567
  · exact B335571
  · exact B335575
  · exact B335579
  · exact B335583
  · exact B335587
  · exact B335591
  · exact B335595
  · exact B335599
  · exact B335603
  · exact B335607
  · exact B335611
  · exact B335615
  · exact B335619
  · exact B335623
  · exact B335627
  · exact B335631
  · exact B335635
  · exact B335639
  · exact B335643
  · exact B335647
  · exact B335651
  · exact B335655
  · exact B335659
  · exact B335663
  · exact B335667
  · exact B335671
  · exact B335675
  · exact B335679
  · exact B335683
  · exact B335687
  · exact B335691
  · exact B335695
  · exact B335699
  · exact B335703
  · exact B335707
  · exact B335711
  · exact B335715
  · exact B335719
  · exact B335723
  · exact B335727
  · exact B335731
  · exact B335735
  · exact B335739
  · exact B335743
  · exact B335747
  · exact B335751
  · exact B335755
  · exact B335759
  · exact B335763
  · exact B335767
  · exact B335771
  · exact B335775
  · exact B335779
  · exact B335783
  · exact B335787
  · exact B335791
  · exact B335795
  · exact B335799
  · exact B335803
  · exact B335807
  · exact B335811
  · exact B335815
  · exact B335819
  · exact B335823
  · exact B335827
  · exact B335831
  · exact B335835
  · exact B335839
  · exact B335843
  · exact B335847
  · exact B335851
  · exact B335855
  · exact B335859
  · exact B335863
  · exact B335867
  · exact B335871
  · exact B335875
  · exact B335879
  · exact B335883
  · exact B335887
  · exact B335891
  · exact B335895
  · exact B335899
  · exact B335903
  · exact B335907
  · exact B335911
  · exact B335915
  · exact B335919
  · exact B335923
  · exact B335927
  · exact B335931
  · exact B335935
  · exact B335939
  · exact B335943
  · exact B335947
  · exact B335951
  · exact B335955
  · exact B335959
  · exact B335963
  · exact B335967
  · exact B335971
  · exact B335975
  · exact B335979
  · exact B335983
  · exact B335987
  · exact B335991
  · exact B335995
  · exact B335999
  · exact B336003
  · exact B336007
  · exact B336011
  · exact B336015
  · exact B336019
  · exact B336023
  · exact B336027
  · exact B336031
  · exact B336035
  · exact B336039
  · exact B336043
  · exact B336047
  · exact B336051
  · exact B336055
  · exact B336059
  · exact B336063
  · exact B336067
  · exact B336071
  · exact B336075
  · exact B336079
  · exact B336083
  · exact B336087
  · exact B336091
  · exact B336095
  · exact B336099
  · exact B336103
  · exact B336107
  · exact B336111
  · exact B336115
  · exact B336119
  · exact B336123
  · exact B336127
  · exact B336131
  · exact B336135
  · exact B336139
  · exact B336143
  · exact B336147
  · exact B336151
  · exact B336155
  · exact B336159
  · exact B336163
  · exact B336167
  · exact B336171
  · exact B336175
  · exact B336179
  · exact B336183
  · exact B336187
  · exact B336191
  · exact B336195
  · exact B336199
  · exact B336203
  · exact B336207
  · exact B336211
  · exact B336215
  · exact B336219
  · exact B336223
  · exact B336227
  · exact B336231
  · exact B336235
  · exact B336239
  · exact B336243
  · exact B336247
  · exact B336251
  · exact B336255
  · exact B336259
  · exact B336263
  · exact B336267
  · exact B336271
  · exact B336275
  · exact B336279
  · exact B336283
  · exact B336287
  · exact B336291
  · exact B336295
  · exact B336299
  · exact B336303
  · exact B336307
  · exact B336311
  · exact B336315
  · exact B336319
  · exact B336323
  · exact B336327
  · exact B336331
  · exact B336335
  · exact B336339
  · exact B336343
  · exact B336347
  · exact B336351
  · exact B336355
  · exact B336359
  · exact B336363
  · exact B336367
  · exact B336371
  · exact B336375
  · exact B336379
  · exact B336383
  · exact B336387
  · exact B336391
  · exact B336395
  · exact B336399
  · exact B336403
  · exact B336407
  · exact B336411
  · exact B336415
  · exact B336419
  · exact B336423
  · exact B336427
  · exact B336431
  · exact B336435
  · exact B336439
  · exact B336443
  · exact B336447
  · exact B336451
  · exact B336455
  · exact B336459
  · exact B336463
  · exact B336467
  · exact B336471
  · exact B336475
  · exact B336479
  · exact B336483
  · exact B336487
  · exact B336491
  · exact B336495
  · exact B336499
  · exact B336503
  · exact B336507
  · exact B336511
  · exact B336515
  · exact B336519
  · exact B336523
  · exact B336527
  · exact B336531
  · exact B336535
  · exact B336539
  · exact B336543
  · exact B336547
  · exact B336551
  · exact B336555
  · exact B336559
  · exact B336563
  · exact B336567
  · exact B336571
  · exact B336575
  · exact B336579
  · exact B336583
  · exact B336587
  · exact B336591
  · exact B336595
  · exact B336599
  · exact B336603
  · exact B336607
  · exact B336611
  · exact B336615
  · exact B336619
  · exact B336623
  · exact B336627
  · exact B336631
  · exact B336635
  · exact B336639
  · exact B336643
  · exact B336647
  · exact B336651
  · exact B336655
  · exact B336659
  · exact B336663
  · exact B336667
  · exact B336671
  · exact B336675
  · exact B336679
  · exact B336683
  · exact B336687
  · exact B336691
  · exact B336695
  · exact B336699
  · exact B336703
  · exact B336707
  · exact B336711
  · exact B336715
  · exact B336719
  · exact B336723
  · exact B336727
  · exact B336731
  · exact B336735
  · exact B336739
  · exact B336743
  · exact B336747
  · exact B336751
  · exact B336755
  · exact B336759
  · exact B336763
  · exact B336767
  · exact B336771
  · exact B336775
  · exact B336779
  · exact B336783
  · exact B336787
  · exact B336791
  · exact B336795
  · exact B336799
  · exact B336803
  · exact B336807
  · exact B336811
  · exact B336815
  · exact B336819
  · exact B336823
  · exact B336827
  · exact B336831
  · exact B336835
  · exact B336839
  · exact B336843
  · exact B336847
  · exact B336851
  · exact B336855
  · exact B336859
  · exact B336863
  · exact B336867
  · exact B336871
  · exact B336875
  · exact B336879
  · exact B336883
  · exact B336887
  · exact B336891
  · exact B336895
  · exact B336899
  · exact B336903
  · exact B336907
  · exact B336911
  · exact B336915
  · exact B336919
  · exact B336923
  · exact B336927
  · exact B336931
  · exact B336935
  · exact B336939
  · exact B336943
  · exact B336947
  · exact B336951
  · exact B336955
  · exact B336959
  · exact B336963
  · exact B336967
  · exact B336971
  · exact B336975
  · exact B336979
  · exact B336983
  · exact B336987
  · exact B336991
  · exact B336995
  · exact B336999
  · exact B337003
  · exact B337007
  · exact B337011
  · exact B337015
  · exact B337019
  · exact B337023
  · exact B337027
  · exact B337031
  · exact B337035
  · exact B337039
  · exact B337043
  · exact B337047
  · exact B337051
  · exact B337055
  · exact B337059
  · exact B337063
  · exact B337067
  · exact B337071
  · exact B337075
  · exact B337079
  · exact B337083
  · exact B337087
  · exact B337091
  · exact B337095
  · exact B337099
  · exact B337103
  · exact B337107
  · exact B337111
  · exact B337115
  · exact B337119
  · exact B337123
  · exact B337127
  · exact B337131
  · exact B337135
  · exact B337139
  · exact B337143
  · exact B337147
  · exact B337151
  · exact B337155
  · exact B337159
  · exact B337163
  · exact B337167
  · exact B337171
  · exact B337175
  · exact B337179
  · exact B337183
  · exact B337187
  · exact B337191
  · exact B337195
  · exact B337199
  · exact B337203
  · exact B337207
  · exact B337211
  · exact B337215
  · exact B337219
  · exact B337223
  · exact B337227
  · exact B337231
  · exact B337235
  · exact B337239
  · exact B337243
  · exact B337247
  · exact B337251
  · exact B337255
  · exact B337259
  · exact B337263
  · exact B337267
  · exact B337271
  · exact B337275
  · exact B337279
  · exact B337283
  · exact B337287
  · exact B337291
  · exact B337295
  · exact B337299
  · exact B337303
  · exact B337307
  · exact B337311
  · exact B337315
  · exact B337319
  · exact B337323
  · exact B337327
  · exact B337331
  · exact B337335
  · exact B337339
  · exact B337343
  · exact B337347
  · exact B337351
  · exact B337355
  · exact B337359
  · exact B337363
  · exact B337367
  · exact B337371
  · exact B337375
  · exact B337379
  · exact B337383
  · exact B337387
  · exact B337391
  · exact B337395
  · exact B337399
  · exact B337403
  · exact B337407
  · exact B337411
  · exact B337415
  · exact B337419
  · exact B337423
  · exact B337427
  · exact B337431
  · exact B337435
  · exact B337439
  · exact B337443
  · exact B337447
  · exact B337451
  · exact B337455
  · exact B337459
  · exact B337463
  · exact B337467
  · exact B337471
  · exact B337475
  · exact B337479
  · exact B337483
  · exact B337487
  · exact B337491
  · exact B337495
  · exact B337499
  · exact B337503
  · exact B337507
  · exact B337511
  · exact B337515
  · exact B337519
  · exact B337523
  · exact B337527
  · exact B337531
  · exact B337535
  · exact B337539
  · exact B337543
  · exact B337547

theorem C1 (j : ℕ) (h1 : 84387 ≤ j) (h2 : j ≤ 84687) : Blo 334751 (4 * j + 3) := by
  interval_cases j
  · exact B337551
  · exact B337555
  · exact B337559
  · exact B337563
  · exact B337567
  · exact B337571
  · exact B337575
  · exact B337579
  · exact B337583
  · exact B337587
  · exact B337591
  · exact B337595
  · exact B337599
  · exact B337603
  · exact B337607
  · exact B337611
  · exact B337615
  · exact B337619
  · exact B337623
  · exact B337627
  · exact B337631
  · exact B337635
  · exact B337639
  · exact B337643
  · exact B337647
  · exact B337651
  · exact B337655
  · exact B337659
  · exact B337663
  · exact B337667
  · exact B337671
  · exact B337675
  · exact B337679
  · exact B337683
  · exact B337687
  · exact B337691
  · exact B337695
  · exact B337699
  · exact B337703
  · exact B337707
  · exact B337711
  · exact B337715
  · exact B337719
  · exact B337723
  · exact B337727
  · exact B337731
  · exact B337735
  · exact B337739
  · exact B337743
  · exact B337747
  · exact B337751
  · exact B337755
  · exact B337759
  · exact B337763
  · exact B337767
  · exact B337771
  · exact B337775
  · exact B337779
  · exact B337783
  · exact B337787
  · exact B337791
  · exact B337795
  · exact B337799
  · exact B337803
  · exact B337807
  · exact B337811
  · exact B337815
  · exact B337819
  · exact B337823
  · exact B337827
  · exact B337831
  · exact B337835
  · exact B337839
  · exact B337843
  · exact B337847
  · exact B337851
  · exact B337855
  · exact B337859
  · exact B337863
  · exact B337867
  · exact B337871
  · exact B337875
  · exact B337879
  · exact B337883
  · exact B337887
  · exact B337891
  · exact B337895
  · exact B337899
  · exact B337903
  · exact B337907
  · exact B337911
  · exact B337915
  · exact B337919
  · exact B337923
  · exact B337927
  · exact B337931
  · exact B337935
  · exact B337939
  · exact B337943
  · exact B337947
  · exact B337951
  · exact B337955
  · exact B337959
  · exact B337963
  · exact B337967
  · exact B337971
  · exact B337975
  · exact B337979
  · exact B337983
  · exact B337987
  · exact B337991
  · exact B337995
  · exact B337999
  · exact B338003
  · exact B338007
  · exact B338011
  · exact B338015
  · exact B338019
  · exact B338023
  · exact B338027
  · exact B338031
  · exact B338035
  · exact B338039
  · exact B338043
  · exact B338047
  · exact B338051
  · exact B338055
  · exact B338059
  · exact B338063
  · exact B338067
  · exact B338071
  · exact B338075
  · exact B338079
  · exact B338083
  · exact B338087
  · exact B338091
  · exact B338095
  · exact B338099
  · exact B338103
  · exact B338107
  · exact B338111
  · exact B338115
  · exact B338119
  · exact B338123
  · exact B338127
  · exact B338131
  · exact B338135
  · exact B338139
  · exact B338143
  · exact B338147
  · exact B338151
  · exact B338155
  · exact B338159
  · exact B338163
  · exact B338167
  · exact B338171
  · exact B338175
  · exact B338179
  · exact B338183
  · exact B338187
  · exact B338191
  · exact B338195
  · exact B338199
  · exact B338203
  · exact B338207
  · exact B338211
  · exact B338215
  · exact B338219
  · exact B338223
  · exact B338227
  · exact B338231
  · exact B338235
  · exact B338239
  · exact B338243
  · exact B338247
  · exact B338251
  · exact B338255
  · exact B338259
  · exact B338263
  · exact B338267
  · exact B338271
  · exact B338275
  · exact B338279
  · exact B338283
  · exact B338287
  · exact B338291
  · exact B338295
  · exact B338299
  · exact B338303
  · exact B338307
  · exact B338311
  · exact B338315
  · exact B338319
  · exact B338323
  · exact B338327
  · exact B338331
  · exact B338335
  · exact B338339
  · exact B338343
  · exact B338347
  · exact B338351
  · exact B338355
  · exact B338359
  · exact B338363
  · exact B338367
  · exact B338371
  · exact B338375
  · exact B338379
  · exact B338383
  · exact B338387
  · exact B338391
  · exact B338395
  · exact B338399
  · exact B338403
  · exact B338407
  · exact B338411
  · exact B338415
  · exact B338419
  · exact B338423
  · exact B338427
  · exact B338431
  · exact B338435
  · exact B338439
  · exact B338443
  · exact B338447
  · exact B338451
  · exact B338455
  · exact B338459
  · exact B338463
  · exact B338467
  · exact B338471
  · exact B338475
  · exact B338479
  · exact B338483
  · exact B338487
  · exact B338491
  · exact B338495
  · exact B338499
  · exact B338503
  · exact B338507
  · exact B338511
  · exact B338515
  · exact B338519
  · exact B338523
  · exact B338527
  · exact B338531
  · exact B338535
  · exact B338539
  · exact B338543
  · exact B338547
  · exact B338551
  · exact B338555
  · exact B338559
  · exact B338563
  · exact B338567
  · exact B338571
  · exact B338575
  · exact B338579
  · exact B338583
  · exact B338587
  · exact B338591
  · exact B338595
  · exact B338599
  · exact B338603
  · exact B338607
  · exact B338611
  · exact B338615
  · exact B338619
  · exact B338623
  · exact B338627
  · exact B338631
  · exact B338635
  · exact B338639
  · exact B338643
  · exact B338647
  · exact B338651
  · exact B338655
  · exact B338659
  · exact B338663
  · exact B338667
  · exact B338671
  · exact B338675
  · exact B338679
  · exact B338683
  · exact B338687
  · exact B338691
  · exact B338695
  · exact B338699
  · exact B338703
  · exact B338707
  · exact B338711
  · exact B338715
  · exact B338719
  · exact B338723
  · exact B338727
  · exact B338731
  · exact B338735
  · exact B338739
  · exact B338743
  · exact B338747
  · exact B338751

theorem solution (m : ℕ) (hlo : 334751 ≤ m) (hhi : m ≤ 338751) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 83687 ≤ j := by omega
    have hj2 : j ≤ 84687 := by omega
    have hb : Blo 334751 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 84387 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
