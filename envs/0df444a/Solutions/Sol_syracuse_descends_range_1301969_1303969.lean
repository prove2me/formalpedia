-- Prove2me | solution 1 for syracuse_descends_range_1301969_1303969
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:27.71945+00:00
-- url     : https://prove2.me/submissions/73578bb0-9fab-4bf7-a92d-d44a12ee20a8

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


theorem B4399109 : Blo 1301969 4399109 := bbase (se 4 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 4399109 = 824833) (by norm_num)
theorem B2932757 : Blo 1301969 2932757 := bbase (se 6 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 2932757 = 137473) (by norm_num)
theorem B1466401 : Blo 1301969 1466401 := bbase (se 2 (by rfl) ⟨549900, by rfl⟩ : syracuseStep 1466401 = 1099801) (by norm_num)
theorem B1466437 : Blo 1301969 1466437 := bbase (se 4 (by rfl) ⟨137478, by rfl⟩ : syracuseStep 1466437 = 274957) (by norm_num)
theorem B30097493 : Blo 1301969 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B2932829 : Blo 1301969 2932829 := bbase (se 3 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 2932829 = 1099811) (by norm_num)
theorem B1466473 : Blo 1301969 1466473 := bbase (se 2 (by rfl) ⟨549927, by rfl⟩ : syracuseStep 1466473 = 1099855) (by norm_num)
theorem B1466509 : Blo 1301969 1466509 := bbase (se 3 (by rfl) ⟨274970, by rfl⟩ : syracuseStep 1466509 = 549941) (by norm_num)
theorem B5562533 : Blo 1301969 5562533 := bbase (se 4 (by rfl) ⟨521487, by rfl⟩ : syracuseStep 5562533 = 1042975) (by norm_num)
theorem B2932901 : Blo 1301969 2932901 := bbase (se 4 (by rfl) ⟨274959, by rfl⟩ : syracuseStep 2932901 = 549919) (by norm_num)
theorem B1466545 : Blo 1301969 1466545 := bbase (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) (by norm_num)
theorem B2474165 : Blo 1301969 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B1466581 : Blo 1301969 1466581 := bbase (se 7 (by rfl) ⟨17186, by rfl⟩ : syracuseStep 1466581 = 34373) (by norm_num)
theorem B2932973 : Blo 1301969 2932973 := bbase (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) (by norm_num)
theorem B10027253 : Blo 1301969 10027253 := bbase (se 5 (by rfl) ⟨470027, by rfl⟩ : syracuseStep 10027253 = 940055) (by norm_num)
theorem B1466617 : Blo 1301969 1466617 := bbase (se 2 (by rfl) ⟨549981, by rfl⟩ : syracuseStep 1466617 = 1099963) (by norm_num)
theorem B1466653 : Blo 1301969 1466653 := bbase (se 3 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 1466653 = 549995) (by norm_num)
theorem B2933045 : Blo 1301969 2933045 := bbase (se 5 (by rfl) ⟨137486, by rfl⟩ : syracuseStep 2933045 = 274973) (by norm_num)
theorem B1466689 : Blo 1301969 1466689 := bbase (se 2 (by rfl) ⟨550008, by rfl⟩ : syracuseStep 1466689 = 1100017) (by norm_num)
theorem B3760453 : Blo 1301969 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B2474317 : Blo 1301969 2474317 := bbase (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) (by norm_num)
theorem B1810765 : Blo 1301969 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B1466725 : Blo 1301969 1466725 := bbase (se 4 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 1466725 = 275011) (by norm_num)
theorem B2933117 : Blo 1301969 2933117 := bbase (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) (by norm_num)
theorem B1466761 : Blo 1301969 1466761 := bbase (se 2 (by rfl) ⟨550035, by rfl⟩ : syracuseStep 1466761 = 1100071) (by norm_num)
theorem B1466797 : Blo 1301969 1466797 := bbase (se 3 (by rfl) ⟨275024, by rfl⟩ : syracuseStep 1466797 = 550049) (by norm_num)
theorem B4399541 : Blo 1301969 4399541 := bbase (se 5 (by rfl) ⟨206228, by rfl⟩ : syracuseStep 4399541 = 412457) (by norm_num)
theorem B2933189 : Blo 1301969 2933189 := bbase (se 4 (by rfl) ⟨274986, by rfl⟩ : syracuseStep 2933189 = 549973) (by norm_num)
theorem B1466833 : Blo 1301969 1466833 := bbase (se 2 (by rfl) ⟨550062, by rfl⟩ : syracuseStep 1466833 = 1100125) (by norm_num)
theorem B1466869 : Blo 1301969 1466869 := bbase (se 5 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 1466869 = 137519) (by norm_num)
theorem B2933261 : Blo 1301969 2933261 := bbase (se 3 (by rfl) ⟨549986, by rfl⟩ : syracuseStep 2933261 = 1099973) (by norm_num)
theorem B1466905 : Blo 1301969 1466905 := bbase (se 2 (by rfl) ⟨550089, by rfl⟩ : syracuseStep 1466905 = 1100179) (by norm_num)
theorem B1466941 : Blo 1301969 1466941 := bbase (se 3 (by rfl) ⟨275051, by rfl⟩ : syracuseStep 1466941 = 550103) (by norm_num)
theorem B2933333 : Blo 1301969 2933333 := bbase (se 8 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 2933333 = 34375) (by norm_num)
theorem B2474621 : Blo 1301969 2474621 := bbase (se 3 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 2474621 = 927983) (by norm_num)
theorem B6259349 : Blo 1301969 6259349 := bbase (se 6 (by rfl) ⟨146703, by rfl⟩ : syracuseStep 6259349 = 293407) (by norm_num)
theorem B2933405 : Blo 1301969 2933405 := bbase (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) (by norm_num)
theorem B7922357 : Blo 1301969 7922357 := bbase (se 5 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 7922357 = 742721) (by norm_num)
theorem B2933477 : Blo 1301969 2933477 := bbase (se 4 (by rfl) ⟨275013, by rfl⟩ : syracuseStep 2933477 = 550027) (by norm_num)
theorem B2933549 : Blo 1301969 2933549 := bbase (se 3 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 2933549 = 1100081) (by norm_num)
theorem B1565525 : Blo 1301969 1565525 := bbase (se 9 (by rfl) ⟨4586, by rfl⟩ : syracuseStep 1565525 = 9173) (by norm_num)
theorem B4399973 : Blo 1301969 4399973 := bbase (se 4 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 4399973 = 824995) (by norm_num)
theorem B1409909 : Blo 1301969 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B2933621 : Blo 1301969 2933621 := bbase (se 5 (by rfl) ⟨137513, by rfl⟩ : syracuseStep 2933621 = 275027) (by norm_num)
theorem B2933693 : Blo 1301969 2933693 := bbase (se 3 (by rfl) ⟨550067, by rfl⟩ : syracuseStep 2933693 = 1100135) (by norm_num)
theorem B2933765 : Blo 1301969 2933765 := bbase (se 4 (by rfl) ⟨275040, by rfl⟩ : syracuseStep 2933765 = 550081) (by norm_num)
theorem B4949045 : Blo 1301969 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B2933837 : Blo 1301969 2933837 := bbase (se 3 (by rfl) ⟨550094, by rfl⟩ : syracuseStep 2933837 = 1100189) (by norm_num)
theorem B9389141 : Blo 1301969 9389141 := bbase (se 8 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 9389141 = 110029) (by norm_num)
theorem B1565833 : Blo 1301969 1565833 := bbase (se 2 (by rfl) ⟨587187, by rfl⟩ : syracuseStep 1565833 = 1174375) (by norm_num)
theorem B2933909 : Blo 1301969 2933909 := bbase (se 6 (by rfl) ⟨68763, by rfl⟩ : syracuseStep 2933909 = 137527) (by norm_num)
theorem B4695205 : Blo 1301969 4695205 := bbase (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) (by norm_num)
theorem B1320145 : Blo 1301969 1320145 := bbase (se 2 (by rfl) ⟨495054, by rfl⟩ : syracuseStep 1320145 = 990109) (by norm_num)
theorem B3130589 : Blo 1301969 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B3130597 : Blo 1301969 3130597 := bbase (se 4 (by rfl) ⟨293493, by rfl⟩ : syracuseStep 3130597 = 586987) (by norm_num)
theorem B6595829 : Blo 1301969 6595829 := bbase (se 5 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 6595829 = 618359) (by norm_num)
theorem B4400405 : Blo 1301969 4400405 := bbase (se 6 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 4400405 = 206269) (by norm_num)
theorem B4949333 : Blo 1301969 4949333 := bbase (se 12 (by rfl) ⟨1812, by rfl⟩ : syracuseStep 4949333 = 3625) (by norm_num)
theorem B1647965 : Blo 1301969 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B2860397 : Blo 1301969 2860397 := bbase (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) (by norm_num)
theorem B2475373 : Blo 1301969 2475373 := bbase (se 3 (by rfl) ⟨464132, by rfl⟩ : syracuseStep 2475373 = 928265) (by norm_num)
theorem B1648021 : Blo 1301969 1648021 := bbase (se 6 (by rfl) ⟨38625, by rfl⟩ : syracuseStep 1648021 = 77251) (by norm_num)
theorem B2860469 : Blo 1301969 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B5014981 : Blo 1301969 5014981 := bbase (se 4 (by rfl) ⟨470154, by rfl⟩ : syracuseStep 5014981 = 940309) (by norm_num)
theorem B3761605 : Blo 1301969 3761605 := bbase (se 4 (by rfl) ⟨352650, by rfl⟩ : syracuseStep 3761605 = 705301) (by norm_num)
theorem B1648117 : Blo 1301969 1648117 := bbase (se 5 (by rfl) ⟨77255, by rfl⟩ : syracuseStep 1648117 = 154511) (by norm_num)
theorem B1566217 : Blo 1301969 1566217 := bbase (se 2 (by rfl) ⟨587331, by rfl⟩ : syracuseStep 1566217 = 1174663) (by norm_num)
theorem B1566221 : Blo 1301969 1566221 := bbase (se 3 (by rfl) ⟨293666, by rfl⟩ : syracuseStep 1566221 = 587333) (by norm_num)
theorem B2229805 : Blo 1301969 2229805 := bbase (se 3 (by rfl) ⟨418088, by rfl⟩ : syracuseStep 2229805 = 836177) (by norm_num)
theorem B22259285 : Blo 1301969 22259285 := bbase (se 8 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 22259285 = 260851) (by norm_num)
theorem B3712661 : Blo 1301969 3712661 := bbase (se 6 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 3712661 = 174031) (by norm_num)
theorem B1648289 : Blo 1301969 1648289 := bbase (se 2 (by rfl) ⟨618108, by rfl⟩ : syracuseStep 1648289 = 1236217) (by norm_num)
theorem B6874789 : Blo 1301969 6874789 := bbase (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) (by norm_num)
theorem B2197165 : Blo 1301969 2197165 := bbase (se 3 (by rfl) ⟨411968, by rfl⟩ : syracuseStep 2197165 = 823937) (by norm_num)
theorem B4400837 : Blo 1301969 4400837 := bbase (se 4 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 4400837 = 825157) (by norm_num)
theorem B1648345 : Blo 1301969 1648345 := bbase (se 2 (by rfl) ⟨618129, by rfl⟩ : syracuseStep 1648345 = 1236259) (by norm_num)
theorem B3761909 : Blo 1301969 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B2197253 : Blo 1301969 2197253 := bbase (se 4 (by rfl) ⟨205992, by rfl⟩ : syracuseStep 2197253 = 411985) (by norm_num)
theorem B3172141 : Blo 1301969 3172141 := bbase (se 3 (by rfl) ⟨594776, by rfl⟩ : syracuseStep 3172141 = 1189553) (by norm_num)
theorem B1648441 : Blo 1301969 1648441 := bbase (se 2 (by rfl) ⟨618165, by rfl⟩ : syracuseStep 1648441 = 1236331) (by norm_num)
theorem B21137237 : Blo 1301969 21137237 := bbase (se 9 (by rfl) ⟨61925, by rfl⟩ : syracuseStep 21137237 = 123851) (by norm_num)
theorem B2197381 : Blo 1301969 2197381 := bbase (se 4 (by rfl) ⟨206004, by rfl⟩ : syracuseStep 2197381 = 412009) (by norm_num)
theorem B2197469 : Blo 1301969 2197469 := bbase (se 3 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 2197469 = 824051) (by norm_num)
theorem B1648613 : Blo 1301969 1648613 := bbase (se 4 (by rfl) ⟨154557, by rfl⟩ : syracuseStep 1648613 = 309115) (by norm_num)
theorem B1648669 : Blo 1301969 1648669 := bbase (se 3 (by rfl) ⟨309125, by rfl⟩ : syracuseStep 1648669 = 618251) (by norm_num)
theorem B6260773 : Blo 1301969 6260773 := bbase (se 4 (by rfl) ⟨586947, by rfl⟩ : syracuseStep 6260773 = 1173895) (by norm_num)
theorem B2197597 : Blo 1301969 2197597 := bbase (se 3 (by rfl) ⟨412049, by rfl⟩ : syracuseStep 2197597 = 824099) (by norm_num)
theorem B2230373 : Blo 1301969 2230373 := bbase (se 4 (by rfl) ⟨209097, by rfl⟩ : syracuseStep 2230373 = 418195) (by norm_num)
theorem B1648765 : Blo 1301969 1648765 := bbase (se 3 (by rfl) ⟨309143, by rfl⟩ : syracuseStep 1648765 = 618287) (by norm_num)
theorem B4171925 : Blo 1301969 4171925 := bbase (se 6 (by rfl) ⟨97779, by rfl⟩ : syracuseStep 4171925 = 195559) (by norm_num)
theorem B2197685 : Blo 1301969 2197685 := bbase (se 5 (by rfl) ⟨103016, by rfl⟩ : syracuseStep 2197685 = 206033) (by norm_num)
theorem B3131597 : Blo 1301969 3131597 := bbase (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) (by norm_num)
theorem B2509093 : Blo 1301969 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B1648937 : Blo 1301969 1648937 := bbase (se 2 (by rfl) ⟨618351, by rfl⟩ : syracuseStep 1648937 = 1236703) (by norm_num)
theorem B2197813 : Blo 1301969 2197813 := bbase (se 5 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 2197813 = 206045) (by norm_num)
theorem B3344717 : Blo 1301969 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B1648993 : Blo 1301969 1648993 := bbase (se 2 (by rfl) ⟨618372, by rfl⟩ : syracuseStep 1648993 = 1236745) (by norm_num)
theorem B1853813 : Blo 1301969 1853813 := bbase (se 5 (by rfl) ⟨86897, by rfl⟩ : syracuseStep 1853813 = 173795) (by norm_num)
theorem B1321337 : Blo 1301969 1321337 := bbase (se 2 (by rfl) ⟨495501, by rfl⟩ : syracuseStep 1321337 = 991003) (by norm_num)
theorem B2197901 : Blo 1301969 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B3295637 : Blo 1301969 3295637 := bbase (se 6 (by rfl) ⟨77241, by rfl⟩ : syracuseStep 3295637 = 154483) (by norm_num)
theorem B1649089 : Blo 1301969 1649089 := bbase (se 2 (by rfl) ⟨618408, by rfl⟩ : syracuseStep 1649089 = 1236817) (by norm_num)
theorem B4950517 : Blo 1301969 4950517 := bbase (se 5 (by rfl) ⟨232055, by rfl⟩ : syracuseStep 4950517 = 464111) (by norm_num)
theorem B6597125 : Blo 1301969 6597125 := bbase (se 4 (by rfl) ⟨618480, by rfl⟩ : syracuseStep 6597125 = 1236961) (by norm_num)
theorem B2198029 : Blo 1301969 2198029 := bbase (se 3 (by rfl) ⟨412130, by rfl⟩ : syracuseStep 2198029 = 824261) (by norm_num)
theorem B9390613 : Blo 1301969 9390613 := bbase (se 6 (by rfl) ⟨220092, by rfl⟩ : syracuseStep 9390613 = 440185) (by norm_num)
theorem B3295829 : Blo 1301969 3295829 := bbase (se 8 (by rfl) ⟨19311, by rfl⟩ : syracuseStep 3295829 = 38623) (by norm_num)
theorem B2198117 : Blo 1301969 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B1649261 : Blo 1301969 1649261 := bbase (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) (by norm_num)
theorem B1649317 : Blo 1301969 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B2198245 : Blo 1301969 2198245 := bbase (se 4 (by rfl) ⟨206085, by rfl⟩ : syracuseStep 2198245 = 412171) (by norm_num)
theorem B4696805 : Blo 1301969 4696805 := bbase (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) (by norm_num)
theorem B1649413 : Blo 1301969 1649413 := bbase (se 4 (by rfl) ⟨154632, by rfl⟩ : syracuseStep 1649413 = 309265) (by norm_num)
theorem B12684053 : Blo 1301969 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B4950821 : Blo 1301969 4950821 := bbase (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) (by norm_num)
theorem B2198333 : Blo 1301969 2198333 := bbase (se 3 (by rfl) ⟨412187, by rfl⟩ : syracuseStep 2198333 = 824375) (by norm_num)
theorem B3345293 : Blo 1301969 3345293 := bbase (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) (by norm_num)
theorem B3296173 : Blo 1301969 3296173 := bbase (se 3 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 3296173 = 1236065) (by norm_num)
theorem B1649585 : Blo 1301969 1649585 := bbase (se 2 (by rfl) ⟨618594, by rfl⟩ : syracuseStep 1649585 = 1237189) (by norm_num)
theorem B2198461 : Blo 1301969 2198461 := bbase (se 3 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 2198461 = 824423) (by norm_num)
theorem B3132365 : Blo 1301969 3132365 := bbase (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) (by norm_num)
theorem B1649641 : Blo 1301969 1649641 := bbase (se 2 (by rfl) ⟨618615, by rfl⟩ : syracuseStep 1649641 = 1237231) (by norm_num)
theorem B2640917 : Blo 1301969 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B2198549 : Blo 1301969 2198549 := bbase (se 6 (by rfl) ⟨51528, by rfl⟩ : syracuseStep 2198549 = 103057) (by norm_num)
theorem B3296285 : Blo 1301969 3296285 := bbase (se 3 (by rfl) ⟨618053, by rfl⟩ : syracuseStep 3296285 = 1236107) (by norm_num)
theorem B1649737 : Blo 1301969 1649737 := bbase (se 2 (by rfl) ⟨618651, by rfl⟩ : syracuseStep 1649737 = 1237303) (by norm_num)
theorem B2198677 : Blo 1301969 2198677 := bbase (se 6 (by rfl) ⟨51531, by rfl⟩ : syracuseStep 2198677 = 103063) (by norm_num)
theorem B1952957 : Blo 1301969 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B1952981 : Blo 1301969 1952981 := bbase (se 7 (by rfl) ⟨22886, by rfl⟩ : syracuseStep 1952981 = 45773) (by norm_num)
theorem B3296477 : Blo 1301969 3296477 := bbase (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) (by norm_num)
theorem B4173029 : Blo 1301969 4173029 := bbase (se 4 (by rfl) ⟨391221, by rfl⟩ : syracuseStep 4173029 = 782443) (by norm_num)
theorem B1953005 : Blo 1301969 1953005 := bbase (se 3 (by rfl) ⟨366188, by rfl⟩ : syracuseStep 1953005 = 732377) (by norm_num)
theorem B2198765 : Blo 1301969 2198765 := bbase (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) (by norm_num)
theorem B1649909 : Blo 1301969 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B1953029 : Blo 1301969 1953029 := bbase (se 4 (by rfl) ⟨183096, by rfl⟩ : syracuseStep 1953029 = 366193) (by norm_num)
theorem B1953053 : Blo 1301969 1953053 := bbase (se 3 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 1953053 = 732395) (by norm_num)
theorem B1649965 : Blo 1301969 1649965 := bbase (se 3 (by rfl) ⟨309368, by rfl⟩ : syracuseStep 1649965 = 618737) (by norm_num)
theorem B1953077 : Blo 1301969 1953077 := bbase (se 5 (by rfl) ⟨91550, by rfl⟩ : syracuseStep 1953077 = 183101) (by norm_num)
theorem B1953101 : Blo 1301969 1953101 := bbase (se 3 (by rfl) ⟨366206, by rfl⟩ : syracuseStep 1953101 = 732413) (by norm_num)
theorem B1953125 : Blo 1301969 1953125 := bbase (se 4 (by rfl) ⟨183105, by rfl⟩ : syracuseStep 1953125 = 366211) (by norm_num)
theorem B2198893 : Blo 1301969 2198893 := bbase (se 3 (by rfl) ⟨412292, by rfl⟩ : syracuseStep 2198893 = 824585) (by norm_num)
theorem B4394357 : Blo 1301969 4394357 := bbase (se 5 (by rfl) ⟨205985, by rfl⟩ : syracuseStep 4394357 = 411971) (by norm_num)
theorem B5942645 : Blo 1301969 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B1953149 : Blo 1301969 1953149 := bbase (se 3 (by rfl) ⟨366215, by rfl⟩ : syracuseStep 1953149 = 732431) (by norm_num)
theorem B1650061 : Blo 1301969 1650061 := bbase (se 3 (by rfl) ⟨309386, by rfl⟩ : syracuseStep 1650061 = 618773) (by norm_num)
theorem B1953173 : Blo 1301969 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B18787733 : Blo 1301969 18787733 := bbase (se 6 (by rfl) ⟨440337, by rfl⟩ : syracuseStep 18787733 = 880675) (by norm_num)
theorem B1953197 : Blo 1301969 1953197 := bbase (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) (by norm_num)
theorem B1953221 : Blo 1301969 1953221 := bbase (se 4 (by rfl) ⟨183114, by rfl⟩ : syracuseStep 1953221 = 366229) (by norm_num)
theorem B2198981 : Blo 1301969 2198981 := bbase (se 4 (by rfl) ⟨206154, by rfl⟩ : syracuseStep 2198981 = 412309) (by norm_num)
theorem B1953245 : Blo 1301969 1953245 := bbase (se 3 (by rfl) ⟨366233, by rfl⟩ : syracuseStep 1953245 = 732467) (by norm_num)
theorem B1953269 : Blo 1301969 1953269 := bbase (se 5 (by rfl) ⟨91559, by rfl⟩ : syracuseStep 1953269 = 183119) (by norm_num)
theorem B1953293 : Blo 1301969 1953293 := bbase (se 3 (by rfl) ⟨366242, by rfl⟩ : syracuseStep 1953293 = 732485) (by norm_num)
theorem B1953317 : Blo 1301969 1953317 := bbase (se 4 (by rfl) ⟨183123, by rfl⟩ : syracuseStep 1953317 = 366247) (by norm_num)
theorem B3296821 : Blo 1301969 3296821 := bbase (se 5 (by rfl) ⟨154538, by rfl⟩ : syracuseStep 3296821 = 309077) (by norm_num)
theorem B1650233 : Blo 1301969 1650233 := bbase (se 2 (by rfl) ⟨618837, by rfl⟩ : syracuseStep 1650233 = 1237675) (by norm_num)
theorem B1953341 : Blo 1301969 1953341 := bbase (se 3 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 1953341 = 732503) (by norm_num)
theorem B2199109 : Blo 1301969 2199109 := bbase (se 4 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 2199109 = 412333) (by norm_num)
theorem B2821709 : Blo 1301969 2821709 := bbase (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) (by norm_num)
theorem B1953365 : Blo 1301969 1953365 := bbase (se 8 (by rfl) ⟨11445, by rfl⟩ : syracuseStep 1953365 = 22891) (by norm_num)
theorem B1953389 : Blo 1301969 1953389 := bbase (se 3 (by rfl) ⟨366260, by rfl⟩ : syracuseStep 1953389 = 732521) (by norm_num)
theorem B1650289 : Blo 1301969 1650289 := bbase (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) (by norm_num)
theorem B1953413 : Blo 1301969 1953413 := bbase (se 4 (by rfl) ⟨183132, by rfl⟩ : syracuseStep 1953413 = 366265) (by norm_num)
theorem B1953437 : Blo 1301969 1953437 := bbase (se 3 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 1953437 = 732539) (by norm_num)
theorem B2199197 : Blo 1301969 2199197 := bbase (se 3 (by rfl) ⟨412349, by rfl⟩ : syracuseStep 2199197 = 824699) (by norm_num)
theorem B3296933 : Blo 1301969 3296933 := bbase (se 4 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 3296933 = 618175) (by norm_num)
theorem B1953461 : Blo 1301969 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B2641589 : Blo 1301969 2641589 := bbase (se 5 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 2641589 = 247649) (by norm_num)
theorem B1953485 : Blo 1301969 1953485 := bbase (se 3 (by rfl) ⟨366278, by rfl⟩ : syracuseStep 1953485 = 732557) (by norm_num)
theorem B1953509 : Blo 1301969 1953509 := bbase (se 4 (by rfl) ⟨183141, by rfl⟩ : syracuseStep 1953509 = 366283) (by norm_num)
theorem B1953533 : Blo 1301969 1953533 := bbase (se 3 (by rfl) ⟨366287, by rfl⟩ : syracuseStep 1953533 = 732575) (by norm_num)
theorem B1855237 : Blo 1301969 1855237 := bbase (se 4 (by rfl) ⟨173928, by rfl⟩ : syracuseStep 1855237 = 347857) (by norm_num)
theorem B1953557 : Blo 1301969 1953557 := bbase (se 6 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 1953557 = 91573) (by norm_num)
theorem B6598421 : Blo 1301969 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B2199325 : Blo 1301969 2199325 := bbase (se 3 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 2199325 = 824747) (by norm_num)
theorem B4394789 : Blo 1301969 4394789 := bbase (se 4 (by rfl) ⟨412011, by rfl⟩ : syracuseStep 4394789 = 824023) (by norm_num)
theorem B1953581 : Blo 1301969 1953581 := bbase (se 3 (by rfl) ⟨366296, by rfl⟩ : syracuseStep 1953581 = 732593) (by norm_num)
theorem B1953605 : Blo 1301969 1953605 := bbase (se 4 (by rfl) ⟨183150, by rfl⟩ : syracuseStep 1953605 = 366301) (by norm_num)
theorem B1953629 : Blo 1301969 1953629 := bbase (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) (by norm_num)
theorem B2346853 : Blo 1301969 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B3297125 : Blo 1301969 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B1953653 : Blo 1301969 1953653 := bbase (se 5 (by rfl) ⟨91577, by rfl⟩ : syracuseStep 1953653 = 183155) (by norm_num)
theorem B2199413 : Blo 1301969 2199413 := bbase (se 5 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 2199413 = 206195) (by norm_num)
theorem B1953677 : Blo 1301969 1953677 := bbase (se 3 (by rfl) ⟨366314, by rfl⟩ : syracuseStep 1953677 = 732629) (by norm_num)
theorem B9392021 : Blo 1301969 9392021 := bbase (se 6 (by rfl) ⟨220125, by rfl⟩ : syracuseStep 9392021 = 440251) (by norm_num)
theorem B1953701 : Blo 1301969 1953701 := bbase (se 4 (by rfl) ⟨183159, by rfl⟩ : syracuseStep 1953701 = 366319) (by norm_num)
theorem B1953725 : Blo 1301969 1953725 := bbase (se 3 (by rfl) ⟨366323, by rfl⟩ : syracuseStep 1953725 = 732647) (by norm_num)
theorem B1486793 : Blo 1301969 1486793 := bbase (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) (by norm_num)
theorem B1953749 : Blo 1301969 1953749 := bbase (se 7 (by rfl) ⟨22895, by rfl⟩ : syracuseStep 1953749 = 45791) (by norm_num)
theorem B1953773 : Blo 1301969 1953773 := bbase (se 3 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 1953773 = 732665) (by norm_num)
theorem B2199541 : Blo 1301969 2199541 := bbase (se 5 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 2199541 = 206207) (by norm_num)
theorem B1953797 : Blo 1301969 1953797 := bbase (se 4 (by rfl) ⟨183168, by rfl⟩ : syracuseStep 1953797 = 366337) (by norm_num)
theorem B1953821 : Blo 1301969 1953821 := bbase (se 3 (by rfl) ⟨366341, by rfl⟩ : syracuseStep 1953821 = 732683) (by norm_num)
theorem B7041077 : Blo 1301969 7041077 := bbase (se 5 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 7041077 = 660101) (by norm_num)
theorem B1953845 : Blo 1301969 1953845 := bbase (se 5 (by rfl) ⟨91586, by rfl⟩ : syracuseStep 1953845 = 183173) (by norm_num)
theorem B1953869 : Blo 1301969 1953869 := bbase (se 3 (by rfl) ⟨366350, by rfl⟩ : syracuseStep 1953869 = 732701) (by norm_num)
theorem B2199629 : Blo 1301969 2199629 := bbase (se 3 (by rfl) ⟨412430, by rfl⟩ : syracuseStep 2199629 = 824861) (by norm_num)
theorem B1953893 : Blo 1301969 1953893 := bbase (se 4 (by rfl) ⟨183177, by rfl⟩ : syracuseStep 1953893 = 366355) (by norm_num)
theorem B1953917 : Blo 1301969 1953917 := bbase (se 3 (by rfl) ⟨366359, by rfl⟩ : syracuseStep 1953917 = 732719) (by norm_num)
theorem B1953941 : Blo 1301969 1953941 := bbase (se 6 (by rfl) ⟨45795, by rfl⟩ : syracuseStep 1953941 = 91591) (by norm_num)
theorem B1953965 : Blo 1301969 1953965 := bbase (se 3 (by rfl) ⟨366368, by rfl⟩ : syracuseStep 1953965 = 732737) (by norm_num)
theorem B3297469 : Blo 1301969 3297469 := bbase (se 3 (by rfl) ⟨618275, by rfl⟩ : syracuseStep 3297469 = 1236551) (by norm_num)
theorem B1953989 : Blo 1301969 1953989 := bbase (se 4 (by rfl) ⟨183186, by rfl⟩ : syracuseStep 1953989 = 366373) (by norm_num)
theorem B2199757 : Blo 1301969 2199757 := bbase (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) (by norm_num)
theorem B4395221 : Blo 1301969 4395221 := bbase (se 7 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 4395221 = 103013) (by norm_num)
theorem B1954013 : Blo 1301969 1954013 := bbase (se 3 (by rfl) ⟨366377, by rfl⟩ : syracuseStep 1954013 = 732755) (by norm_num)
theorem B2642149 : Blo 1301969 2642149 := bbase (se 4 (by rfl) ⟨247701, by rfl⟩ : syracuseStep 2642149 = 495403) (by norm_num)
theorem B1954037 : Blo 1301969 1954037 := bbase (se 5 (by rfl) ⟨91595, by rfl⟩ : syracuseStep 1954037 = 183191) (by norm_num)
theorem B1954061 : Blo 1301969 1954061 := bbase (se 3 (by rfl) ⟨366386, by rfl⟩ : syracuseStep 1954061 = 732773) (by norm_num)
theorem B1880341 : Blo 1301969 1880341 := bbase (se 6 (by rfl) ⟨44070, by rfl⟩ : syracuseStep 1880341 = 88141) (by norm_num)
theorem B1954085 : Blo 1301969 1954085 := bbase (se 4 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 1954085 = 366391) (by norm_num)
theorem B2642213 : Blo 1301969 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B2199845 : Blo 1301969 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B3297581 : Blo 1301969 3297581 := bbase (se 3 (by rfl) ⟨618296, by rfl⟩ : syracuseStep 3297581 = 1236593) (by norm_num)
theorem B1954109 : Blo 1301969 1954109 := bbase (se 3 (by rfl) ⟨366395, by rfl⟩ : syracuseStep 1954109 = 732791) (by norm_num)
theorem B1954133 : Blo 1301969 1954133 := bbase (se 10 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 1954133 = 5725) (by norm_num)
theorem B5566805 : Blo 1301969 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1855829 : Blo 1301969 1855829 := bbase (se 10 (by rfl) ⟨2718, by rfl⟩ : syracuseStep 1855829 = 5437) (by norm_num)
theorem B1954157 : Blo 1301969 1954157 := bbase (se 3 (by rfl) ⟨366404, by rfl⟩ : syracuseStep 1954157 = 732809) (by norm_num)
theorem B2781557 : Blo 1301969 2781557 := bbase (se 5 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 2781557 = 260771) (by norm_num)
theorem B1954181 : Blo 1301969 1954181 := bbase (se 4 (by rfl) ⟨183204, by rfl⟩ : syracuseStep 1954181 = 366409) (by norm_num)
theorem B1954205 : Blo 1301969 1954205 := bbase (se 3 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 1954205 = 732827) (by norm_num)
theorem B2347429 : Blo 1301969 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B1855909 : Blo 1301969 1855909 := bbase (se 4 (by rfl) ⟨173991, by rfl⟩ : syracuseStep 1855909 = 347983) (by norm_num)
theorem B2199973 : Blo 1301969 2199973 := bbase (se 4 (by rfl) ⟨206247, by rfl⟩ : syracuseStep 2199973 = 412495) (by norm_num)
theorem B1954229 : Blo 1301969 1954229 := bbase (se 5 (by rfl) ⟨91604, by rfl⟩ : syracuseStep 1954229 = 183209) (by norm_num)
theorem B1954253 : Blo 1301969 1954253 := bbase (se 3 (by rfl) ⟨366422, by rfl⟩ : syracuseStep 1954253 = 732845) (by norm_num)
theorem B1954277 : Blo 1301969 1954277 := bbase (se 4 (by rfl) ⟨183213, by rfl⟩ : syracuseStep 1954277 = 366427) (by norm_num)
theorem B2781677 : Blo 1301969 2781677 := bbase (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) (by norm_num)
theorem B3297773 : Blo 1301969 3297773 := bbase (se 3 (by rfl) ⟨618332, by rfl⟩ : syracuseStep 3297773 = 1236665) (by norm_num)
theorem B1954301 : Blo 1301969 1954301 := bbase (se 3 (by rfl) ⟨366431, by rfl⟩ : syracuseStep 1954301 = 732863) (by norm_num)
theorem B2200061 : Blo 1301969 2200061 := bbase (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) (by norm_num)
theorem B1954325 : Blo 1301969 1954325 := bbase (se 6 (by rfl) ⟨45804, by rfl⟩ : syracuseStep 1954325 = 91609) (by norm_num)
theorem B1856029 : Blo 1301969 1856029 := bbase (se 3 (by rfl) ⟨348005, by rfl⟩ : syracuseStep 1856029 = 696011) (by norm_num)
theorem B1954349 : Blo 1301969 1954349 := bbase (se 3 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 1954349 = 732881) (by norm_num)
theorem B1954373 : Blo 1301969 1954373 := bbase (se 4 (by rfl) ⟨183222, by rfl⟩ : syracuseStep 1954373 = 366445) (by norm_num)
theorem B1954397 : Blo 1301969 1954397 := bbase (se 3 (by rfl) ⟨366449, by rfl⟩ : syracuseStep 1954397 = 732899) (by norm_num)
theorem B1954421 : Blo 1301969 1954421 := bbase (se 5 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 1954421 = 183227) (by norm_num)
theorem B1856125 : Blo 1301969 1856125 := bbase (se 3 (by rfl) ⟨348023, by rfl⟩ : syracuseStep 1856125 = 696047) (by norm_num)
theorem B2200189 : Blo 1301969 2200189 := bbase (se 3 (by rfl) ⟨412535, by rfl⟩ : syracuseStep 2200189 = 825071) (by norm_num)
theorem B4395653 : Blo 1301969 4395653 := bbase (se 4 (by rfl) ⟨412092, by rfl⟩ : syracuseStep 4395653 = 824185) (by norm_num)
theorem B1954445 : Blo 1301969 1954445 := bbase (se 3 (by rfl) ⟨366458, by rfl⟩ : syracuseStep 1954445 = 732917) (by norm_num)
theorem B2257565 : Blo 1301969 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B2257573 : Blo 1301969 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B1954469 : Blo 1301969 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B1954493 : Blo 1301969 1954493 := bbase (se 3 (by rfl) ⟨366467, by rfl⟩ : syracuseStep 1954493 = 732935) (by norm_num)
theorem B1954517 : Blo 1301969 1954517 := bbase (se 7 (by rfl) ⟨22904, by rfl⟩ : syracuseStep 1954517 = 45809) (by norm_num)
theorem B2200277 : Blo 1301969 2200277 := bbase (se 7 (by rfl) ⟨25784, by rfl⟩ : syracuseStep 2200277 = 51569) (by norm_num)
theorem B1954541 : Blo 1301969 1954541 := bbase (se 3 (by rfl) ⟨366476, by rfl⟩ : syracuseStep 1954541 = 732953) (by norm_num)
theorem B1954565 : Blo 1301969 1954565 := bbase (se 4 (by rfl) ⟨183240, by rfl⟩ : syracuseStep 1954565 = 366481) (by norm_num)
theorem B1954589 : Blo 1301969 1954589 := bbase (se 3 (by rfl) ⟨366485, by rfl⟩ : syracuseStep 1954589 = 732971) (by norm_num)
theorem B2929445 : Blo 1301969 2929445 := bbase (se 4 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 2929445 = 549271) (by norm_num)
theorem B1954613 : Blo 1301969 1954613 := bbase (se 5 (by rfl) ⟨91622, by rfl⟩ : syracuseStep 1954613 = 183245) (by norm_num)
theorem B3298117 : Blo 1301969 3298117 := bbase (se 4 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 3298117 = 618397) (by norm_num)
theorem B1954637 : Blo 1301969 1954637 := bbase (se 3 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 1954637 = 732989) (by norm_num)
theorem B2200405 : Blo 1301969 2200405 := bbase (se 9 (by rfl) ⟨6446, by rfl⟩ : syracuseStep 2200405 = 12893) (by norm_num)
theorem B1954661 : Blo 1301969 1954661 := bbase (se 4 (by rfl) ⟨183249, by rfl⟩ : syracuseStep 1954661 = 366499) (by norm_num)
theorem B2929517 : Blo 1301969 2929517 := bbase (se 3 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 2929517 = 1098569) (by norm_num)
theorem B1954685 : Blo 1301969 1954685 := bbase (se 3 (by rfl) ⟨366503, by rfl⟩ : syracuseStep 1954685 = 733007) (by norm_num)
theorem B1954709 : Blo 1301969 1954709 := bbase (se 6 (by rfl) ⟨45813, by rfl⟩ : syracuseStep 1954709 = 91627) (by norm_num)
theorem B1954733 : Blo 1301969 1954733 := bbase (se 3 (by rfl) ⟨366512, by rfl⟩ : syracuseStep 1954733 = 733025) (by norm_num)
theorem B2929589 : Blo 1301969 2929589 := bbase (se 5 (by rfl) ⟨137324, by rfl⟩ : syracuseStep 2929589 = 274649) (by norm_num)
theorem B3298229 : Blo 1301969 3298229 := bbase (se 5 (by rfl) ⟨154604, by rfl⟩ : syracuseStep 3298229 = 309209) (by norm_num)
theorem B1954757 : Blo 1301969 1954757 := bbase (se 4 (by rfl) ⟨183258, by rfl⟩ : syracuseStep 1954757 = 366517) (by norm_num)
theorem B1954781 : Blo 1301969 1954781 := bbase (se 3 (by rfl) ⟨366521, by rfl⟩ : syracuseStep 1954781 = 733043) (by norm_num)
theorem B1954805 : Blo 1301969 1954805 := bbase (se 5 (by rfl) ⟨91631, by rfl⟩ : syracuseStep 1954805 = 183263) (by norm_num)
theorem B2929661 : Blo 1301969 2929661 := bbase (se 3 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 2929661 = 1098623) (by norm_num)
theorem B1954829 : Blo 1301969 1954829 := bbase (se 3 (by rfl) ⟨366530, by rfl⟩ : syracuseStep 1954829 = 733061) (by norm_num)
theorem B1954853 : Blo 1301969 1954853 := bbase (se 4 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 1954853 = 366535) (by norm_num)
theorem B6599717 : Blo 1301969 6599717 := bbase (se 4 (by rfl) ⟨618723, by rfl⟩ : syracuseStep 6599717 = 1237447) (by norm_num)
theorem B3707957 : Blo 1301969 3707957 := bbase (se 5 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 3707957 = 347621) (by norm_num)
theorem B4396085 : Blo 1301969 4396085 := bbase (se 5 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 4396085 = 412133) (by norm_num)
theorem B8352821 : Blo 1301969 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B1954877 : Blo 1301969 1954877 := bbase (se 3 (by rfl) ⟨366539, by rfl⟩ : syracuseStep 1954877 = 733079) (by norm_num)
theorem B2929733 : Blo 1301969 2929733 := bbase (se 4 (by rfl) ⟨274662, by rfl⟩ : syracuseStep 2929733 = 549325) (by norm_num)
theorem B1954901 : Blo 1301969 1954901 := bbase (se 8 (by rfl) ⟨11454, by rfl⟩ : syracuseStep 1954901 = 22909) (by norm_num)
theorem B2782309 : Blo 1301969 2782309 := bbase (se 4 (by rfl) ⟨260841, by rfl⟩ : syracuseStep 2782309 = 521683) (by norm_num)
theorem B4174949 : Blo 1301969 4174949 := bbase (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) (by norm_num)
theorem B1954925 : Blo 1301969 1954925 := bbase (se 3 (by rfl) ⟨366548, by rfl⟩ : syracuseStep 1954925 = 733097) (by norm_num)
theorem B1856621 : Blo 1301969 1856621 := bbase (se 3 (by rfl) ⟨348116, by rfl⟩ : syracuseStep 1856621 = 696233) (by norm_num)
theorem B8909941 : Blo 1301969 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B3298421 : Blo 1301969 3298421 := bbase (se 5 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 3298421 = 309227) (by norm_num)
theorem B2675837 : Blo 1301969 2675837 := bbase (se 3 (by rfl) ⟨501719, by rfl⟩ : syracuseStep 2675837 = 1003439) (by norm_num)
theorem B1954949 : Blo 1301969 1954949 := bbase (se 4 (by rfl) ⟨183276, by rfl⟩ : syracuseStep 1954949 = 366553) (by norm_num)
theorem B2929805 : Blo 1301969 2929805 := bbase (se 3 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 2929805 = 1098677) (by norm_num)
theorem B14840981 : Blo 1301969 14840981 := bbase (se 6 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 14840981 = 695671) (by norm_num)
theorem B1954973 : Blo 1301969 1954973 := bbase (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) (by norm_num)
theorem B1954997 : Blo 1301969 1954997 := bbase (se 5 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 1954997 = 183281) (by norm_num)
theorem B1955021 : Blo 1301969 1955021 := bbase (se 3 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 1955021 = 733133) (by norm_num)
theorem B2929877 : Blo 1301969 2929877 := bbase (se 7 (by rfl) ⟨34334, by rfl⟩ : syracuseStep 2929877 = 68669) (by norm_num)
theorem B1955045 : Blo 1301969 1955045 := bbase (se 4 (by rfl) ⟨183285, by rfl⟩ : syracuseStep 1955045 = 366571) (by norm_num)
theorem B1955069 : Blo 1301969 1955069 := bbase (se 3 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 1955069 = 733151) (by norm_num)
theorem B4945157 : Blo 1301969 4945157 := bbase (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) (by norm_num)
theorem B1955093 : Blo 1301969 1955093 := bbase (se 6 (by rfl) ⟨45822, by rfl⟩ : syracuseStep 1955093 = 91645) (by norm_num)
theorem B2929949 : Blo 1301969 2929949 := bbase (se 3 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 2929949 = 1098731) (by norm_num)
theorem B1955117 : Blo 1301969 1955117 := bbase (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) (by norm_num)
theorem B1955141 : Blo 1301969 1955141 := bbase (se 4 (by rfl) ⟨183294, by rfl⟩ : syracuseStep 1955141 = 366589) (by norm_num)
theorem B1955165 : Blo 1301969 1955165 := bbase (se 3 (by rfl) ⟨366593, by rfl⟩ : syracuseStep 1955165 = 733187) (by norm_num)
theorem B2930021 : Blo 1301969 2930021 := bbase (se 4 (by rfl) ⟨274689, by rfl⟩ : syracuseStep 2930021 = 549379) (by norm_num)
theorem B1955189 : Blo 1301969 1955189 := bbase (se 5 (by rfl) ⟨91649, by rfl⟩ : syracuseStep 1955189 = 183299) (by norm_num)
theorem B1955213 : Blo 1301969 1955213 := bbase (se 3 (by rfl) ⟨366602, by rfl⟩ : syracuseStep 1955213 = 733205) (by norm_num)
theorem B1955237 : Blo 1301969 1955237 := bbase (se 4 (by rfl) ⟨183303, by rfl⟩ : syracuseStep 1955237 = 366607) (by norm_num)
theorem B2930093 : Blo 1301969 2930093 := bbase (se 3 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 2930093 = 1098785) (by norm_num)
theorem B1955261 : Blo 1301969 1955261 := bbase (se 3 (by rfl) ⟨366611, by rfl⟩ : syracuseStep 1955261 = 733223) (by norm_num)
theorem B6591941 : Blo 1301969 6591941 := bbase (se 4 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 6591941 = 1235989) (by norm_num)
theorem B3298765 : Blo 1301969 3298765 := bbase (se 3 (by rfl) ⟨618518, by rfl⟩ : syracuseStep 3298765 = 1237037) (by norm_num)
theorem B1955285 : Blo 1301969 1955285 := bbase (se 7 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 1955285 = 45827) (by norm_num)
theorem B2086373 : Blo 1301969 2086373 := bbase (se 4 (by rfl) ⟨195597, by rfl⟩ : syracuseStep 2086373 = 391195) (by norm_num)
theorem B4396517 : Blo 1301969 4396517 := bbase (se 4 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 4396517 = 824347) (by norm_num)
theorem B1955309 : Blo 1301969 1955309 := bbase (se 3 (by rfl) ⟨366620, by rfl⟩ : syracuseStep 1955309 = 733241) (by norm_num)
theorem B2930165 : Blo 1301969 2930165 := bbase (se 5 (by rfl) ⟨137351, by rfl⟩ : syracuseStep 2930165 = 274703) (by norm_num)
theorem B1955333 : Blo 1301969 1955333 := bbase (se 4 (by rfl) ⟨183312, by rfl⟩ : syracuseStep 1955333 = 366625) (by norm_num)
theorem B1955357 : Blo 1301969 1955357 := bbase (se 3 (by rfl) ⟨366629, by rfl⟩ : syracuseStep 1955357 = 733259) (by norm_num)
theorem B4945445 : Blo 1301969 4945445 := bbase (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) (by norm_num)
theorem B1955381 : Blo 1301969 1955381 := bbase (se 5 (by rfl) ⟨91658, by rfl⟩ : syracuseStep 1955381 = 183317) (by norm_num)
theorem B2930237 : Blo 1301969 2930237 := bbase (se 3 (by rfl) ⟨549419, by rfl⟩ : syracuseStep 2930237 = 1098839) (by norm_num)
theorem B3298877 : Blo 1301969 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B1955405 : Blo 1301969 1955405 := bbase (se 3 (by rfl) ⟨366638, by rfl⟩ : syracuseStep 1955405 = 733277) (by norm_num)
theorem B2086501 : Blo 1301969 2086501 := bbase (se 4 (by rfl) ⟨195609, by rfl⟩ : syracuseStep 2086501 = 391219) (by norm_num)
theorem B1955429 : Blo 1301969 1955429 := bbase (se 4 (by rfl) ⟨183321, by rfl⟩ : syracuseStep 1955429 = 366643) (by norm_num)
theorem B1955453 : Blo 1301969 1955453 := bbase (se 3 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 1955453 = 733295) (by norm_num)
theorem B2930309 : Blo 1301969 2930309 := bbase (se 4 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 2930309 = 549433) (by norm_num)
theorem B12523157 : Blo 1301969 12523157 := bbase (se 6 (by rfl) ⟨293511, by rfl⟩ : syracuseStep 12523157 = 587023) (by norm_num)
theorem B1955477 : Blo 1301969 1955477 := bbase (se 6 (by rfl) ⟨45831, by rfl⟩ : syracuseStep 1955477 = 91663) (by norm_num)
theorem B2086565 : Blo 1301969 2086565 := bbase (se 4 (by rfl) ⟨195615, by rfl⟩ : syracuseStep 2086565 = 391231) (by norm_num)
theorem B1955501 : Blo 1301969 1955501 := bbase (se 3 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 1955501 = 733313) (by norm_num)
theorem B1955525 : Blo 1301969 1955525 := bbase (se 4 (by rfl) ⟨183330, by rfl⟩ : syracuseStep 1955525 = 366661) (by norm_num)
theorem B2930381 : Blo 1301969 2930381 := bbase (se 3 (by rfl) ⟨549446, by rfl⟩ : syracuseStep 2930381 = 1098893) (by norm_num)
theorem B3708629 : Blo 1301969 3708629 := bbase (se 7 (by rfl) ⟨43460, by rfl⟩ : syracuseStep 3708629 = 86921) (by norm_num)
theorem B1955549 : Blo 1301969 1955549 := bbase (se 3 (by rfl) ⟨366665, by rfl⟩ : syracuseStep 1955549 = 733331) (by norm_num)
theorem B1955573 : Blo 1301969 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B2143997 : Blo 1301969 2143997 := bbase (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) (by norm_num)
theorem B3299069 : Blo 1301969 3299069 := bbase (se 3 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 3299069 = 1237151) (by norm_num)
theorem B4888325 : Blo 1301969 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B2348813 : Blo 1301969 2348813 := bbase (se 3 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 2348813 = 880805) (by norm_num)
theorem B1955597 : Blo 1301969 1955597 := bbase (se 3 (by rfl) ⟨366674, by rfl⟩ : syracuseStep 1955597 = 733349) (by norm_num)
theorem B2930453 : Blo 1301969 2930453 := bbase (se 6 (by rfl) ⟨68682, by rfl⟩ : syracuseStep 2930453 = 137365) (by norm_num)
theorem B12048149 : Blo 1301969 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B1955621 : Blo 1301969 1955621 := bbase (se 4 (by rfl) ⟨183339, by rfl⟩ : syracuseStep 1955621 = 366679) (by norm_num)
theorem B1955645 : Blo 1301969 1955645 := bbase (se 3 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 1955645 = 733367) (by norm_num)
theorem B7518037 : Blo 1301969 7518037 := bbase (se 9 (by rfl) ⟨22025, by rfl⟩ : syracuseStep 7518037 = 44051) (by norm_num)
theorem B1955669 : Blo 1301969 1955669 := bbase (se 9 (by rfl) ⟨5729, by rfl⟩ : syracuseStep 1955669 = 11459) (by norm_num)
theorem B2930525 : Blo 1301969 2930525 := bbase (se 3 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 2930525 = 1098947) (by norm_num)
theorem B2471789 : Blo 1301969 2471789 := bbase (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) (by norm_num)
theorem B1955693 : Blo 1301969 1955693 := bbase (se 3 (by rfl) ⟨366692, by rfl⟩ : syracuseStep 1955693 = 733385) (by norm_num)
theorem B1955717 : Blo 1301969 1955717 := bbase (se 4 (by rfl) ⟨183348, by rfl⟩ : syracuseStep 1955717 = 366697) (by norm_num)
theorem B4396949 : Blo 1301969 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B1955741 : Blo 1301969 1955741 := bbase (se 3 (by rfl) ⟨366701, by rfl⟩ : syracuseStep 1955741 = 733403) (by norm_num)
theorem B2930597 : Blo 1301969 2930597 := bbase (se 4 (by rfl) ⟨274743, by rfl⟩ : syracuseStep 2930597 = 549487) (by norm_num)
theorem B1390505 : Blo 1301969 1390505 := bbase (se 2 (by rfl) ⟨521439, by rfl⟩ : syracuseStep 1390505 = 1042879) (by norm_num)
theorem B1955765 : Blo 1301969 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B1955789 : Blo 1301969 1955789 := bbase (se 3 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 1955789 = 733421) (by norm_num)
theorem B1505233 : Blo 1301969 1505233 := bbase (se 2 (by rfl) ⟨564462, by rfl⟩ : syracuseStep 1505233 = 1128925) (by norm_num)
theorem B22566869 : Blo 1301969 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2783197 : Blo 1301969 2783197 := bbase (se 3 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 2783197 = 1043699) (by norm_num)
theorem B1390565 : Blo 1301969 1390565 := bbase (se 4 (by rfl) ⟨130365, by rfl⟩ : syracuseStep 1390565 = 260731) (by norm_num)
theorem B1955813 : Blo 1301969 1955813 := bbase (se 4 (by rfl) ⟨183357, by rfl⟩ : syracuseStep 1955813 = 366715) (by norm_num)
theorem B2930669 : Blo 1301969 2930669 := bbase (se 3 (by rfl) ⟨549500, by rfl⟩ : syracuseStep 2930669 = 1099001) (by norm_num)
theorem B2471933 : Blo 1301969 2471933 := bbase (se 3 (by rfl) ⟨463487, by rfl⟩ : syracuseStep 2471933 = 926975) (by norm_num)
theorem B1955837 : Blo 1301969 1955837 := bbase (se 3 (by rfl) ⟨366719, by rfl⟩ : syracuseStep 1955837 = 733439) (by norm_num)
theorem B1955861 : Blo 1301969 1955861 := bbase (se 6 (by rfl) ⟨45840, by rfl⟩ : syracuseStep 1955861 = 91681) (by norm_num)
theorem B1980445 : Blo 1301969 1980445 := bbase (se 3 (by rfl) ⟨371333, by rfl⟩ : syracuseStep 1980445 = 742667) (by norm_num)
theorem B1955885 : Blo 1301969 1955885 := bbase (se 3 (by rfl) ⟨366728, by rfl⟩ : syracuseStep 1955885 = 733457) (by norm_num)
theorem B2930741 : Blo 1301969 2930741 := bbase (se 5 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 2930741 = 274757) (by norm_num)
theorem B5568581 : Blo 1301969 5568581 := bbase (se 4 (by rfl) ⟨522054, by rfl⟩ : syracuseStep 5568581 = 1044109) (by norm_num)
theorem B1955909 : Blo 1301969 1955909 := bbase (se 4 (by rfl) ⟨183366, by rfl⟩ : syracuseStep 1955909 = 366733) (by norm_num)
theorem B2783317 : Blo 1301969 2783317 := bbase (se 8 (by rfl) ⟨16308, by rfl⟩ : syracuseStep 2783317 = 32617) (by norm_num)
theorem B3299413 : Blo 1301969 3299413 := bbase (se 8 (by rfl) ⟨19332, by rfl⟩ : syracuseStep 3299413 = 38665) (by norm_num)
theorem B1955933 : Blo 1301969 1955933 := bbase (se 3 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 1955933 = 733475) (by norm_num)
theorem B1390693 : Blo 1301969 1390693 := bbase (se 4 (by rfl) ⟨130377, by rfl⟩ : syracuseStep 1390693 = 260755) (by norm_num)
theorem B2930813 : Blo 1301969 2930813 := bbase (se 3 (by rfl) ⟨549527, by rfl⟩ : syracuseStep 2930813 = 1099055) (by norm_num)
theorem B3709061 : Blo 1301969 3709061 := bbase (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) (by norm_num)
theorem B2930885 : Blo 1301969 2930885 := bbase (se 4 (by rfl) ⟨274770, by rfl⟩ : syracuseStep 2930885 = 549541) (by norm_num)
theorem B3299525 : Blo 1301969 3299525 := bbase (se 4 (by rfl) ⟨309330, by rfl⟩ : syracuseStep 3299525 = 618661) (by norm_num)
theorem B2930957 : Blo 1301969 2930957 := bbase (se 3 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 2930957 = 1099109) (by norm_num)
theorem B2472221 : Blo 1301969 2472221 := bbase (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) (by norm_num)
theorem B5568821 : Blo 1301969 5568821 := bbase (se 5 (by rfl) ⟨261038, by rfl⟩ : syracuseStep 5568821 = 522077) (by norm_num)
theorem B6601013 : Blo 1301969 6601013 := bbase (se 5 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 6601013 = 618845) (by norm_num)
theorem B4397381 : Blo 1301969 4397381 := bbase (se 4 (by rfl) ⟨412254, by rfl⟩ : syracuseStep 4397381 = 824509) (by norm_num)
theorem B2931029 : Blo 1301969 2931029 := bbase (se 10 (by rfl) ⟨4293, by rfl⟩ : syracuseStep 2931029 = 8587) (by norm_num)
theorem B2783573 : Blo 1301969 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B3299717 : Blo 1301969 3299717 := bbase (se 4 (by rfl) ⟨309348, by rfl⟩ : syracuseStep 3299717 = 618697) (by norm_num)
theorem B3340693 : Blo 1301969 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B2931101 : Blo 1301969 2931101 := bbase (se 3 (by rfl) ⟨549581, by rfl⟩ : syracuseStep 2931101 = 1099163) (by norm_num)
theorem B1464745 : Blo 1301969 1464745 := bbase (se 2 (by rfl) ⟨549279, by rfl⟩ : syracuseStep 1464745 = 1098559) (by norm_num)
theorem B2472373 : Blo 1301969 2472373 := bbase (se 5 (by rfl) ⟨115892, by rfl⟩ : syracuseStep 2472373 = 231785) (by norm_num)
theorem B1464781 : Blo 1301969 1464781 := bbase (se 3 (by rfl) ⟨274646, by rfl⟩ : syracuseStep 1464781 = 549293) (by norm_num)
theorem B4692437 : Blo 1301969 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B2931173 : Blo 1301969 2931173 := bbase (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) (by norm_num)
theorem B1464817 : Blo 1301969 1464817 := bbase (se 2 (by rfl) ⟨549306, by rfl⟩ : syracuseStep 1464817 = 1098613) (by norm_num)
theorem B4176373 : Blo 1301969 4176373 := bbase (se 5 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 4176373 = 391535) (by norm_num)
theorem B1464853 : Blo 1301969 1464853 := bbase (se 6 (by rfl) ⟨34332, by rfl⟩ : syracuseStep 1464853 = 68665) (by norm_num)
theorem B1391137 : Blo 1301969 1391137 := bbase (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) (by norm_num)
theorem B2931245 : Blo 1301969 2931245 := bbase (se 3 (by rfl) ⟨549608, by rfl⟩ : syracuseStep 2931245 = 1099217) (by norm_num)
theorem B1464889 : Blo 1301969 1464889 := bbase (se 2 (by rfl) ⟨549333, by rfl⟩ : syracuseStep 1464889 = 1098667) (by norm_num)
theorem B1464925 : Blo 1301969 1464925 := bbase (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) (by norm_num)
theorem B2931317 : Blo 1301969 2931317 := bbase (se 5 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 2931317 = 274811) (by norm_num)
theorem B1464961 : Blo 1301969 1464961 := bbase (se 2 (by rfl) ⟨549360, by rfl⟩ : syracuseStep 1464961 = 1098721) (by norm_num)
theorem B1391257 : Blo 1301969 1391257 := bbase (se 2 (by rfl) ⟨521721, by rfl⟩ : syracuseStep 1391257 = 1043443) (by norm_num)
theorem B1464997 : Blo 1301969 1464997 := bbase (se 4 (by rfl) ⟨137343, by rfl⟩ : syracuseStep 1464997 = 274687) (by norm_num)
theorem B2931389 : Blo 1301969 2931389 := bbase (se 3 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 2931389 = 1099271) (by norm_num)
theorem B4946629 : Blo 1301969 4946629 := bbase (se 4 (by rfl) ⟨463746, by rfl⟩ : syracuseStep 4946629 = 927493) (by norm_num)
theorem B1465033 : Blo 1301969 1465033 := bbase (se 2 (by rfl) ⟨549387, by rfl⟩ : syracuseStep 1465033 = 1098775) (by norm_num)
theorem B4455125 : Blo 1301969 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B6593237 : Blo 1301969 6593237 := bbase (se 7 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 6593237 = 154529) (by norm_num)
theorem B3300061 : Blo 1301969 3300061 := bbase (se 3 (by rfl) ⟨618761, by rfl⟩ : syracuseStep 3300061 = 1237523) (by norm_num)
theorem B2472677 : Blo 1301969 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B2972389 : Blo 1301969 2972389 := bbase (se 4 (by rfl) ⟨278661, by rfl⟩ : syracuseStep 2972389 = 557323) (by norm_num)
theorem B1465069 : Blo 1301969 1465069 := bbase (se 3 (by rfl) ⟨274700, by rfl⟩ : syracuseStep 1465069 = 549401) (by norm_num)
theorem B4692725 : Blo 1301969 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B4397813 : Blo 1301969 4397813 := bbase (se 5 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 4397813 = 412295) (by norm_num)
theorem B2931461 : Blo 1301969 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B1465105 : Blo 1301969 1465105 := bbase (se 2 (by rfl) ⟨549414, by rfl⟩ : syracuseStep 1465105 = 1098829) (by norm_num)
theorem B1465141 : Blo 1301969 1465141 := bbase (se 5 (by rfl) ⟨68678, by rfl⟩ : syracuseStep 1465141 = 137357) (by norm_num)
theorem B2931533 : Blo 1301969 2931533 := bbase (se 3 (by rfl) ⟨549662, by rfl⟩ : syracuseStep 2931533 = 1099325) (by norm_num)
theorem B3300173 : Blo 1301969 3300173 := bbase (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) (by norm_num)
theorem B1465177 : Blo 1301969 1465177 := bbase (se 2 (by rfl) ⟨549441, by rfl⟩ : syracuseStep 1465177 = 1098883) (by norm_num)
theorem B3709813 : Blo 1301969 3709813 := bbase (se 5 (by rfl) ⟨173897, by rfl⟩ : syracuseStep 3709813 = 347795) (by norm_num)
theorem B1465213 : Blo 1301969 1465213 := bbase (se 3 (by rfl) ⟨274727, by rfl⟩ : syracuseStep 1465213 = 549455) (by norm_num)
theorem B2931605 : Blo 1301969 2931605 := bbase (se 6 (by rfl) ⟨68709, by rfl⟩ : syracuseStep 2931605 = 137419) (by norm_num)
theorem B1391509 : Blo 1301969 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B1391513 : Blo 1301969 1391513 := bbase (se 2 (by rfl) ⟨521817, by rfl⟩ : syracuseStep 1391513 = 1043635) (by norm_num)
theorem B1465249 : Blo 1301969 1465249 := bbase (se 2 (by rfl) ⟨549468, by rfl⟩ : syracuseStep 1465249 = 1098937) (by norm_num)
theorem B4176821 : Blo 1301969 4176821 := bbase (se 5 (by rfl) ⟨195788, by rfl⟩ : syracuseStep 4176821 = 391577) (by norm_num)
theorem B1465285 : Blo 1301969 1465285 := bbase (se 4 (by rfl) ⟨137370, by rfl⟩ : syracuseStep 1465285 = 274741) (by norm_num)
theorem B2087885 : Blo 1301969 2087885 := bbase (se 3 (by rfl) ⟨391478, by rfl⟩ : syracuseStep 2087885 = 782957) (by norm_num)
theorem B2931677 : Blo 1301969 2931677 := bbase (se 3 (by rfl) ⟨549689, by rfl⟩ : syracuseStep 2931677 = 1099379) (by norm_num)
theorem B1465321 : Blo 1301969 1465321 := bbase (se 2 (by rfl) ⟨549495, by rfl⟩ : syracuseStep 1465321 = 1098991) (by norm_num)
theorem B4946933 : Blo 1301969 4946933 := bbase (se 5 (by rfl) ⟨231887, by rfl⟩ : syracuseStep 4946933 = 463775) (by norm_num)
theorem B1465357 : Blo 1301969 1465357 := bbase (se 3 (by rfl) ⟨274754, by rfl⟩ : syracuseStep 1465357 = 549509) (by norm_num)
theorem B3300365 : Blo 1301969 3300365 := bbase (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) (by norm_num)
theorem B2931749 : Blo 1301969 2931749 := bbase (se 4 (by rfl) ⟨274851, by rfl⟩ : syracuseStep 2931749 = 549703) (by norm_num)
theorem B1465393 : Blo 1301969 1465393 := bbase (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) (by norm_num)
theorem B2088013 : Blo 1301969 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B1465429 : Blo 1301969 1465429 := bbase (se 8 (by rfl) ⟨8586, by rfl⟩ : syracuseStep 1465429 = 17173) (by norm_num)
theorem B2505829 : Blo 1301969 2505829 := bbase (se 4 (by rfl) ⟨234921, by rfl⟩ : syracuseStep 2505829 = 469843) (by norm_num)
theorem B2931821 : Blo 1301969 2931821 := bbase (se 3 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 2931821 = 1099433) (by norm_num)
theorem B1465465 : Blo 1301969 1465465 := bbase (se 2 (by rfl) ⟨549549, by rfl⟩ : syracuseStep 1465465 = 1099099) (by norm_num)
theorem B1465501 : Blo 1301969 1465501 := bbase (se 3 (by rfl) ⟨274781, by rfl⟩ : syracuseStep 1465501 = 549563) (by norm_num)
theorem B4398245 : Blo 1301969 4398245 := bbase (se 4 (by rfl) ⟨412335, by rfl⟩ : syracuseStep 4398245 = 824671) (by norm_num)
theorem B1760437 : Blo 1301969 1760437 := bbase (se 5 (by rfl) ⟨82520, by rfl⟩ : syracuseStep 1760437 = 165041) (by norm_num)
theorem B2931893 : Blo 1301969 2931893 := bbase (se 5 (by rfl) ⟨137432, by rfl⟩ : syracuseStep 2931893 = 274865) (by norm_num)
theorem B1465537 : Blo 1301969 1465537 := bbase (se 2 (by rfl) ⟨549576, by rfl⟩ : syracuseStep 1465537 = 1099153) (by norm_num)
theorem B2227397 : Blo 1301969 2227397 := bbase (se 4 (by rfl) ⟨208818, by rfl⟩ : syracuseStep 2227397 = 417637) (by norm_num)
theorem B2784461 : Blo 1301969 2784461 := bbase (se 3 (by rfl) ⟨522086, by rfl⟩ : syracuseStep 2784461 = 1044173) (by norm_num)
theorem B1465573 : Blo 1301969 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B2931965 : Blo 1301969 2931965 := bbase (se 3 (by rfl) ⟨549743, by rfl⟩ : syracuseStep 2931965 = 1099487) (by norm_num)
theorem B1465609 : Blo 1301969 1465609 := bbase (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) (by norm_num)
theorem B1465645 : Blo 1301969 1465645 := bbase (se 3 (by rfl) ⟨274808, by rfl⟩ : syracuseStep 1465645 = 549617) (by norm_num)
theorem B2932037 : Blo 1301969 2932037 := bbase (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) (by norm_num)
theorem B1465681 : Blo 1301969 1465681 := bbase (se 2 (by rfl) ⟨549630, by rfl⟩ : syracuseStep 1465681 = 1099261) (by norm_num)
theorem B38083925 : Blo 1301969 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B1465717 : Blo 1301969 1465717 := bbase (se 5 (by rfl) ⟨68705, by rfl⟩ : syracuseStep 1465717 = 137411) (by norm_num)
theorem B2932109 : Blo 1301969 2932109 := bbase (se 3 (by rfl) ⟨549770, by rfl⟩ : syracuseStep 2932109 = 1099541) (by norm_num)
theorem B1465753 : Blo 1301969 1465753 := bbase (se 2 (by rfl) ⟨549657, by rfl⟩ : syracuseStep 1465753 = 1099315) (by norm_num)
theorem B3390893 : Blo 1301969 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B1465789 : Blo 1301969 1465789 := bbase (se 3 (by rfl) ⟨274835, by rfl⟩ : syracuseStep 1465789 = 549671) (by norm_num)
theorem B2784701 : Blo 1301969 2784701 := bbase (se 3 (by rfl) ⟨522131, by rfl⟩ : syracuseStep 2784701 = 1044263) (by norm_num)
theorem B1392077 : Blo 1301969 1392077 := bbase (se 3 (by rfl) ⟨261014, by rfl⟩ : syracuseStep 1392077 = 522029) (by norm_num)
theorem B2473429 : Blo 1301969 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B2932181 : Blo 1301969 2932181 := bbase (se 7 (by rfl) ⟨34361, by rfl⟩ : syracuseStep 2932181 = 68723) (by norm_num)
theorem B1465825 : Blo 1301969 1465825 := bbase (se 2 (by rfl) ⟨549684, by rfl⟩ : syracuseStep 1465825 = 1099369) (by norm_num)
theorem B1465861 : Blo 1301969 1465861 := bbase (se 4 (by rfl) ⟨137424, by rfl⟩ : syracuseStep 1465861 = 274849) (by norm_num)
theorem B9895445 : Blo 1301969 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B2932253 : Blo 1301969 2932253 := bbase (se 3 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 2932253 = 1099595) (by norm_num)
theorem B1465897 : Blo 1301969 1465897 := bbase (se 2 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 1465897 = 1099423) (by norm_num)
theorem B1465933 : Blo 1301969 1465933 := bbase (se 3 (by rfl) ⟨274862, by rfl⟩ : syracuseStep 1465933 = 549725) (by norm_num)
theorem B4398677 : Blo 1301969 4398677 := bbase (se 8 (by rfl) ⟨25773, by rfl⟩ : syracuseStep 4398677 = 51547) (by norm_num)
theorem B2473573 : Blo 1301969 2473573 := bbase (se 4 (by rfl) ⟨231897, by rfl⟩ : syracuseStep 2473573 = 463795) (by norm_num)
theorem B2932325 : Blo 1301969 2932325 := bbase (se 4 (by rfl) ⟨274905, by rfl⟩ : syracuseStep 2932325 = 549811) (by norm_num)
theorem B1465969 : Blo 1301969 1465969 := bbase (se 2 (by rfl) ⟨549738, by rfl⟩ : syracuseStep 1465969 = 1099477) (by norm_num)
theorem B1392265 : Blo 1301969 1392265 := bbase (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) (by norm_num)
theorem B1564309 : Blo 1301969 1564309 := bbase (se 6 (by rfl) ⟨36663, by rfl⟩ : syracuseStep 1564309 = 73327) (by norm_num)
theorem B1466005 : Blo 1301969 1466005 := bbase (se 6 (by rfl) ⟨34359, by rfl⟩ : syracuseStep 1466005 = 68719) (by norm_num)
theorem B1982117 : Blo 1301969 1982117 := bbase (se 4 (by rfl) ⟨185823, by rfl⟩ : syracuseStep 1982117 = 371647) (by norm_num)
theorem B2932397 : Blo 1301969 2932397 := bbase (se 3 (by rfl) ⟨549824, by rfl⟩ : syracuseStep 2932397 = 1099649) (by norm_num)
theorem B5086901 : Blo 1301969 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B1466041 : Blo 1301969 1466041 := bbase (se 2 (by rfl) ⟨549765, by rfl⟩ : syracuseStep 1466041 = 1099531) (by norm_num)
theorem B1466077 : Blo 1301969 1466077 := bbase (se 3 (by rfl) ⟨274889, by rfl⟩ : syracuseStep 1466077 = 549779) (by norm_num)
theorem B2932469 : Blo 1301969 2932469 := bbase (se 5 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 2932469 = 274919) (by norm_num)
theorem B1466113 : Blo 1301969 1466113 := bbase (se 2 (by rfl) ⟨549792, by rfl⟩ : syracuseStep 1466113 = 1099585) (by norm_num)
theorem B2473733 : Blo 1301969 2473733 := bbase (se 4 (by rfl) ⟨231912, by rfl⟩ : syracuseStep 2473733 = 463825) (by norm_num)
theorem B17841941 : Blo 1301969 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B1466149 : Blo 1301969 1466149 := bbase (se 4 (by rfl) ⟨137451, by rfl⟩ : syracuseStep 1466149 = 274903) (by norm_num)
theorem B2932541 : Blo 1301969 2932541 := bbase (se 3 (by rfl) ⟨549851, by rfl⟩ : syracuseStep 2932541 = 1099703) (by norm_num)
theorem B1466185 : Blo 1301969 1466185 := bbase (se 2 (by rfl) ⟨549819, by rfl⟩ : syracuseStep 1466185 = 1099639) (by norm_num)
theorem B1466221 : Blo 1301969 1466221 := bbase (se 3 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 1466221 = 549833) (by norm_num)
theorem B3129205 : Blo 1301969 3129205 := bbase (se 5 (by rfl) ⟨146681, by rfl⟩ : syracuseStep 3129205 = 293363) (by norm_num)
theorem B7421813 : Blo 1301969 7421813 := bbase (se 5 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 7421813 = 695795) (by norm_num)
theorem B2932613 : Blo 1301969 2932613 := bbase (se 4 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 2932613 = 549865) (by norm_num)
theorem B1466257 : Blo 1301969 1466257 := bbase (se 2 (by rfl) ⟨549846, by rfl⟩ : syracuseStep 1466257 = 1099693) (by norm_num)
theorem B2473877 : Blo 1301969 2473877 := bbase (se 6 (by rfl) ⟨57981, by rfl⟩ : syracuseStep 2473877 = 115963) (by norm_num)
theorem B9887669 : Blo 1301969 9887669 := bbase (se 5 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 9887669 = 926969) (by norm_num)
theorem B1466293 : Blo 1301969 1466293 := bbase (se 5 (by rfl) ⟨68732, by rfl⟩ : syracuseStep 1466293 = 137465) (by norm_num)
theorem B2932685 : Blo 1301969 2932685 := bbase (se 3 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 2932685 = 1099757) (by norm_num)
theorem B1466329 : Blo 1301969 1466329 := bbase (se 2 (by rfl) ⟨549873, by rfl⟩ : syracuseStep 1466329 = 1099747) (by norm_num)
theorem B6594533 : Blo 1301969 6594533 := bbase (se 4 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 6594533 = 1236475) (by norm_num)
theorem B2228197 : Blo 1301969 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B1564645 : Blo 1301969 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B1466365 : Blo 1301969 1466365 := bbase (se 3 (by rfl) ⟨274943, by rfl⟩ : syracuseStep 1466365 = 549887) (by norm_num)
theorem B1302531 : Blo 1301969 1302531 := bstep (se 1 (by rfl) ⟨976898, by rfl⟩ : syracuseStep 1302531 = 1953797) B1953797
theorem B2932739 : Blo 1301969 2932739 := bstep (se 1 (by rfl) ⟨2199554, by rfl⟩ : syracuseStep 2932739 = 4399109) B4399109
theorem B1302547 : Blo 1301969 1302547 := bstep (se 1 (by rfl) ⟨976910, by rfl⟩ : syracuseStep 1302547 = 1953821) B1953821
theorem B4694051 : Blo 1301969 4694051 := bstep (se 1 (by rfl) ⟨3520538, by rfl⟩ : syracuseStep 4694051 = 7041077) B7041077
theorem B1302563 : Blo 1301969 1302563 := bstep (se 1 (by rfl) ⟨976922, by rfl⟩ : syracuseStep 1302563 = 1953845) B1953845
theorem B8347697 : Blo 1301969 8347697 := bstep (se 2 (by rfl) ⟨3130386, by rfl⟩ : syracuseStep 8347697 = 6260773) B6260773
theorem B1302579 : Blo 1301969 1302579 := bstep (se 1 (by rfl) ⟨976934, by rfl⟩ : syracuseStep 1302579 = 1953869) B1953869
theorem B1466419 : Blo 1301969 1466419 := bstep (se 1 (by rfl) ⟨1099814, by rfl⟩ : syracuseStep 1466419 = 2199629) B2199629
theorem B1302595 : Blo 1301969 1302595 := bstep (se 1 (by rfl) ⟨976946, by rfl⟩ : syracuseStep 1302595 = 1953893) B1953893
theorem B1302611 : Blo 1301969 1302611 := bstep (se 1 (by rfl) ⟨976958, by rfl⟩ : syracuseStep 1302611 = 1953917) B1953917
theorem B1302627 : Blo 1301969 1302627 := bstep (se 1 (by rfl) ⟨976970, by rfl⟩ : syracuseStep 1302627 = 1953941) B1953941
theorem B3711089 : Blo 1301969 3711089 := bstep (se 2 (by rfl) ⟨1391658, by rfl⟩ : syracuseStep 3711089 = 2783317) B2783317
theorem B4399217 : Blo 1301969 4399217 := bstep (se 2 (by rfl) ⟨1649706, by rfl⟩ : syracuseStep 4399217 = 3299413) B3299413
theorem B1302643 : Blo 1301969 1302643 := bstep (se 1 (by rfl) ⟨976982, by rfl⟩ : syracuseStep 1302643 = 1953965) B1953965
theorem B1302659 : Blo 1301969 1302659 := bstep (se 1 (by rfl) ⟨976994, by rfl⟩ : syracuseStep 1302659 = 1953989) B1953989
theorem B1302675 : Blo 1301969 1302675 := bstep (se 1 (by rfl) ⟨977006, by rfl⟩ : syracuseStep 1302675 = 1954013) B1954013
theorem B1302691 : Blo 1301969 1302691 := bstep (se 1 (by rfl) ⟨977018, by rfl⟩ : syracuseStep 1302691 = 1954037) B1954037
theorem B1302707 : Blo 1301969 1302707 := bstep (se 1 (by rfl) ⟨977030, by rfl⟩ : syracuseStep 1302707 = 1954061) B1954061
theorem B1302723 : Blo 1301969 1302723 := bstep (se 1 (by rfl) ⟨977042, by rfl⟩ : syracuseStep 1302723 = 1954085) B1954085
theorem B1761475 : Blo 1301969 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B1466563 : Blo 1301969 1466563 := bstep (se 1 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 1466563 = 2199845) B2199845
theorem B1302739 : Blo 1301969 1302739 := bstep (se 1 (by rfl) ⟨977054, by rfl⟩ : syracuseStep 1302739 = 1954109) B1954109
theorem B1302755 : Blo 1301969 1302755 := bstep (se 1 (by rfl) ⟨977066, by rfl⟩ : syracuseStep 1302755 = 1954133) B1954133
theorem B3711203 : Blo 1301969 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B1302771 : Blo 1301969 1302771 := bstep (se 1 (by rfl) ⟨977078, by rfl⟩ : syracuseStep 1302771 = 1954157) B1954157
theorem B1302787 : Blo 1301969 1302787 := bstep (se 1 (by rfl) ⟨977090, by rfl⟩ : syracuseStep 1302787 = 1954181) B1954181
theorem B11133197 : Blo 1301969 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B5947661 : Blo 1301969 5947661 := bstep (se 3 (by rfl) ⟨1115186, by rfl⟩ : syracuseStep 5947661 = 2230373) B2230373
theorem B2933009 : Blo 1301969 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B1302803 : Blo 1301969 1302803 := bstep (se 1 (by rfl) ⟨977102, by rfl⟩ : syracuseStep 1302803 = 1954205) B1954205
theorem B1302819 : Blo 1301969 1302819 := bstep (se 1 (by rfl) ⟨977114, by rfl⟩ : syracuseStep 1302819 = 1954229) B1954229
theorem B2933027 : Blo 1301969 2933027 := bstep (se 1 (by rfl) ⟨2199770, by rfl⟩ : syracuseStep 2933027 = 4399541) B4399541
theorem B3522865 : Blo 1301969 3522865 := bstep (se 2 (by rfl) ⟨1321074, by rfl⟩ : syracuseStep 3522865 = 2642149) B2642149
theorem B1302835 : Blo 1301969 1302835 := bstep (se 1 (by rfl) ⟨977126, by rfl⟩ : syracuseStep 1302835 = 1954253) B1954253
theorem B1302851 : Blo 1301969 1302851 := bstep (se 1 (by rfl) ⟨977138, by rfl⟩ : syracuseStep 1302851 = 1954277) B1954277
theorem B1302867 : Blo 1301969 1302867 := bstep (se 1 (by rfl) ⟨977150, by rfl⟩ : syracuseStep 1302867 = 1954301) B1954301
theorem B1466707 : Blo 1301969 1466707 := bstep (se 1 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 1466707 = 2200061) B2200061
theorem B1302883 : Blo 1301969 1302883 := bstep (se 1 (by rfl) ⟨977162, by rfl⟩ : syracuseStep 1302883 = 1954325) B1954325
theorem B1302899 : Blo 1301969 1302899 := bstep (se 1 (by rfl) ⟨977174, by rfl⟩ : syracuseStep 1302899 = 1954349) B1954349
theorem B1302915 : Blo 1301969 1302915 := bstep (se 1 (by rfl) ⟨977186, by rfl⟩ : syracuseStep 1302915 = 1954373) B1954373
theorem B11125133 : Blo 1301969 11125133 := bstep (se 3 (by rfl) ⟨2085962, by rfl⟩ : syracuseStep 11125133 = 4171925) B4171925
theorem B1302931 : Blo 1301969 1302931 := bstep (se 1 (by rfl) ⟨977198, by rfl⟩ : syracuseStep 1302931 = 1954397) B1954397
theorem B1302947 : Blo 1301969 1302947 := bstep (se 1 (by rfl) ⟨977210, by rfl⟩ : syracuseStep 1302947 = 1954421) B1954421
theorem B5013937 : Blo 1301969 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B1302963 : Blo 1301969 1302963 := bstep (se 1 (by rfl) ⟨977222, by rfl⟩ : syracuseStep 1302963 = 1954445) B1954445
theorem B1302979 : Blo 1301969 1302979 := bstep (se 1 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 1302979 = 1954469) B1954469
theorem B1302995 : Blo 1301969 1302995 := bstep (se 1 (by rfl) ⟨977246, by rfl⟩ : syracuseStep 1302995 = 1954493) B1954493
theorem B1303011 : Blo 1301969 1303011 := bstep (se 1 (by rfl) ⟨977258, by rfl⟩ : syracuseStep 1303011 = 1954517) B1954517
theorem B1466851 : Blo 1301969 1466851 := bstep (se 1 (by rfl) ⟨1100138, by rfl⟩ : syracuseStep 1466851 = 2200277) B2200277
theorem B1303027 : Blo 1301969 1303027 := bstep (se 1 (by rfl) ⟨977270, by rfl⟩ : syracuseStep 1303027 = 1954541) B1954541
theorem B1303043 : Blo 1301969 1303043 := bstep (se 1 (by rfl) ⟨977282, by rfl⟩ : syracuseStep 1303043 = 1954565) B1954565
theorem B5939725 : Blo 1301969 5939725 := bstep (se 3 (by rfl) ⟨1113698, by rfl⟩ : syracuseStep 5939725 = 2227397) B2227397
theorem B1303059 : Blo 1301969 1303059 := bstep (se 1 (by rfl) ⟨977294, by rfl⟩ : syracuseStep 1303059 = 1954589) B1954589
theorem B1303075 : Blo 1301969 1303075 := bstep (se 1 (by rfl) ⟨977306, by rfl⟩ : syracuseStep 1303075 = 1954613) B1954613
theorem B3129905 : Blo 1301969 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B2474545 : Blo 1301969 2474545 := bstep (se 2 (by rfl) ⟨927954, by rfl⟩ : syracuseStep 2474545 = 1855909) B1855909
theorem B1303091 : Blo 1301969 1303091 := bstep (se 1 (by rfl) ⟨977318, by rfl⟩ : syracuseStep 1303091 = 1954637) B1954637
theorem B2933297 : Blo 1301969 2933297 := bstep (se 2 (by rfl) ⟨1099986, by rfl⟩ : syracuseStep 2933297 = 2199973) B2199973
theorem B1303107 : Blo 1301969 1303107 := bstep (se 1 (by rfl) ⟨977330, by rfl⟩ : syracuseStep 1303107 = 1954661) B1954661
theorem B2933315 : Blo 1301969 2933315 := bstep (se 1 (by rfl) ⟨2199986, by rfl⟩ : syracuseStep 2933315 = 4399973) B4399973
theorem B1303123 : Blo 1301969 1303123 := bstep (se 1 (by rfl) ⟨977342, by rfl⟩ : syracuseStep 1303123 = 1954685) B1954685
theorem B1303139 : Blo 1301969 1303139 := bstep (se 1 (by rfl) ⟨977354, by rfl⟩ : syracuseStep 1303139 = 1954709) B1954709
theorem B1303155 : Blo 1301969 1303155 := bstep (se 1 (by rfl) ⟨977366, by rfl⟩ : syracuseStep 1303155 = 1954733) B1954733
theorem B1303171 : Blo 1301969 1303171 := bstep (se 1 (by rfl) ⟨977378, by rfl⟩ : syracuseStep 1303171 = 1954757) B1954757
theorem B26739341 : Blo 1301969 26739341 := bstep (se 3 (by rfl) ⟨5013626, by rfl⟩ : syracuseStep 26739341 = 10027253) B10027253
theorem B4399757 : Blo 1301969 4399757 := bstep (se 3 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 4399757 = 1649909) B1649909
theorem B1303187 : Blo 1301969 1303187 := bstep (se 1 (by rfl) ⟨977390, by rfl⟩ : syracuseStep 1303187 = 1954781) B1954781
theorem B1303203 : Blo 1301969 1303203 := bstep (se 1 (by rfl) ⟨977402, by rfl⟩ : syracuseStep 1303203 = 1954805) B1954805
theorem B1303219 : Blo 1301969 1303219 := bstep (se 1 (by rfl) ⟨977414, by rfl⟩ : syracuseStep 1303219 = 1954829) B1954829
theorem B1303235 : Blo 1301969 1303235 := bstep (se 1 (by rfl) ⟨977426, by rfl⟩ : syracuseStep 1303235 = 1954853) B1954853
theorem B4399811 : Blo 1301969 4399811 := bstep (se 1 (by rfl) ⟨3299858, by rfl⟩ : syracuseStep 4399811 = 6599717) B6599717
theorem B2474705 : Blo 1301969 2474705 := bstep (se 2 (by rfl) ⟨928014, by rfl⟩ : syracuseStep 2474705 = 1856029) B1856029
theorem B1303251 : Blo 1301969 1303251 := bstep (se 1 (by rfl) ⟨977438, by rfl⟩ : syracuseStep 1303251 = 1954877) B1954877
theorem B6259427 : Blo 1301969 6259427 := bstep (se 1 (by rfl) ⟨4694570, by rfl⟩ : syracuseStep 6259427 = 9389141) B9389141
theorem B1303267 : Blo 1301969 1303267 := bstep (se 1 (by rfl) ⟨977450, by rfl⟩ : syracuseStep 1303267 = 1954901) B1954901
theorem B1303283 : Blo 1301969 1303283 := bstep (se 1 (by rfl) ⟨977462, by rfl⟩ : syracuseStep 1303283 = 1954925) B1954925
theorem B1303299 : Blo 1301969 1303299 := bstep (se 1 (by rfl) ⟨977474, by rfl⟩ : syracuseStep 1303299 = 1954949) B1954949
theorem B1303315 : Blo 1301969 1303315 := bstep (se 1 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 1303315 = 1954973) B1954973
theorem B1303331 : Blo 1301969 1303331 := bstep (se 1 (by rfl) ⟨977498, by rfl⟩ : syracuseStep 1303331 = 1954997) B1954997
theorem B1303347 : Blo 1301969 1303347 := bstep (se 1 (by rfl) ⟨977510, by rfl⟩ : syracuseStep 1303347 = 1955021) B1955021
theorem B1303363 : Blo 1301969 1303363 := bstep (se 1 (by rfl) ⟨977522, by rfl⟩ : syracuseStep 1303363 = 1955045) B1955045
theorem B2933585 : Blo 1301969 2933585 := bstep (se 2 (by rfl) ⟨1100094, by rfl⟩ : syracuseStep 2933585 = 2200189) B2200189
theorem B1303379 : Blo 1301969 1303379 := bstep (se 1 (by rfl) ⟨977534, by rfl⟩ : syracuseStep 1303379 = 1955069) B1955069
theorem B1303395 : Blo 1301969 1303395 := bstep (se 1 (by rfl) ⟨977546, by rfl⟩ : syracuseStep 1303395 = 1955093) B1955093
theorem B2933603 : Blo 1301969 2933603 := bstep (se 1 (by rfl) ⟨2200202, by rfl⟩ : syracuseStep 2933603 = 4400405) B4400405
theorem B1303411 : Blo 1301969 1303411 := bstep (se 1 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 1303411 = 1955117) B1955117
theorem B1303427 : Blo 1301969 1303427 := bstep (se 1 (by rfl) ⟨977570, by rfl⟩ : syracuseStep 1303427 = 1955141) B1955141
theorem B4948877 : Blo 1301969 4948877 := bstep (se 3 (by rfl) ⟨927914, by rfl⟩ : syracuseStep 4948877 = 1855829) B1855829
theorem B1303443 : Blo 1301969 1303443 := bstep (se 1 (by rfl) ⟨977582, by rfl⟩ : syracuseStep 1303443 = 1955165) B1955165
theorem B1303459 : Blo 1301969 1303459 := bstep (se 1 (by rfl) ⟨977594, by rfl⟩ : syracuseStep 1303459 = 1955189) B1955189
theorem B6595505 : Blo 1301969 6595505 := bstep (se 2 (by rfl) ⟨2473314, by rfl⟩ : syracuseStep 6595505 = 4946629) B4946629
theorem B1303475 : Blo 1301969 1303475 := bstep (se 1 (by rfl) ⟨977606, by rfl⟩ : syracuseStep 1303475 = 1955213) B1955213
theorem B1303491 : Blo 1301969 1303491 := bstep (se 1 (by rfl) ⟨977618, by rfl⟩ : syracuseStep 1303491 = 1955237) B1955237
theorem B9388997 : Blo 1301969 9388997 := bstep (se 4 (by rfl) ⟨880218, by rfl⟩ : syracuseStep 9388997 = 1760437) B1760437
theorem B4400081 : Blo 1301969 4400081 := bstep (se 2 (by rfl) ⟨1650030, by rfl⟩ : syracuseStep 4400081 = 3300061) B3300061
theorem B1303507 : Blo 1301969 1303507 := bstep (se 1 (by rfl) ⟨977630, by rfl⟩ : syracuseStep 1303507 = 1955261) B1955261
theorem B1303523 : Blo 1301969 1303523 := bstep (se 1 (by rfl) ⟨977642, by rfl⟩ : syracuseStep 1303523 = 1955285) B1955285
theorem B3523565 : Blo 1301969 3523565 := bstep (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) B1321337
theorem B1303539 : Blo 1301969 1303539 := bstep (se 1 (by rfl) ⟨977654, by rfl⟩ : syracuseStep 1303539 = 1955309) B1955309
theorem B1303555 : Blo 1301969 1303555 := bstep (se 1 (by rfl) ⟨977666, by rfl⟩ : syracuseStep 1303555 = 1955333) B1955333
theorem B1303571 : Blo 1301969 1303571 := bstep (se 1 (by rfl) ⟨977678, by rfl⟩ : syracuseStep 1303571 = 1955357) B1955357
theorem B1303587 : Blo 1301969 1303587 := bstep (se 1 (by rfl) ⟨977690, by rfl⟩ : syracuseStep 1303587 = 1955381) B1955381
theorem B1303603 : Blo 1301969 1303603 := bstep (se 1 (by rfl) ⟨977702, by rfl⟩ : syracuseStep 1303603 = 1955405) B1955405
theorem B1303619 : Blo 1301969 1303619 := bstep (se 1 (by rfl) ⟨977714, by rfl⟩ : syracuseStep 1303619 = 1955429) B1955429
theorem B1303635 : Blo 1301969 1303635 := bstep (se 1 (by rfl) ⟨977726, by rfl⟩ : syracuseStep 1303635 = 1955453) B1955453
theorem B8348771 : Blo 1301969 8348771 := bstep (se 1 (by rfl) ⟨6261578, by rfl⟩ : syracuseStep 8348771 = 12523157) B12523157
theorem B1303651 : Blo 1301969 1303651 := bstep (se 1 (by rfl) ⟨977738, by rfl⟩ : syracuseStep 1303651 = 1955477) B1955477
theorem B2475107 : Blo 1301969 2475107 := bstep (se 1 (by rfl) ⟨1856330, by rfl⟩ : syracuseStep 2475107 = 3712661) B3712661
theorem B2933873 : Blo 1301969 2933873 := bstep (se 2 (by rfl) ⟨1100202, by rfl⟩ : syracuseStep 2933873 = 2200405) B2200405
theorem B1303667 : Blo 1301969 1303667 := bstep (se 1 (by rfl) ⟨977750, by rfl⟩ : syracuseStep 1303667 = 1955501) B1955501
theorem B1303683 : Blo 1301969 1303683 := bstep (se 1 (by rfl) ⟨977762, by rfl⟩ : syracuseStep 1303683 = 1955525) B1955525
theorem B2933891 : Blo 1301969 2933891 := bstep (se 1 (by rfl) ⟨2200418, by rfl⟩ : syracuseStep 2933891 = 4400837) B4400837
theorem B1303699 : Blo 1301969 1303699 := bstep (se 1 (by rfl) ⟨977774, by rfl⟩ : syracuseStep 1303699 = 1955549) B1955549
theorem B2507939 : Blo 1301969 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B1303715 : Blo 1301969 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B1565875 : Blo 1301969 1565875 := bstep (se 1 (by rfl) ⟨1174406, by rfl⟩ : syracuseStep 1565875 = 2348813) B2348813
theorem B1303731 : Blo 1301969 1303731 := bstep (se 1 (by rfl) ⟨977798, by rfl⟩ : syracuseStep 1303731 = 1955597) B1955597
theorem B1303747 : Blo 1301969 1303747 := bstep (se 1 (by rfl) ⟨977810, by rfl⟩ : syracuseStep 1303747 = 1955621) B1955621
theorem B3712205 : Blo 1301969 3712205 := bstep (se 3 (by rfl) ⟨696038, by rfl⟩ : syracuseStep 3712205 = 1392077) B1392077
theorem B1303763 : Blo 1301969 1303763 := bstep (se 1 (by rfl) ⟨977822, by rfl⟩ : syracuseStep 1303763 = 1955645) B1955645
theorem B14091491 : Blo 1301969 14091491 := bstep (se 1 (by rfl) ⟨10568618, by rfl⟩ : syracuseStep 14091491 = 21137237) B21137237
theorem B1303779 : Blo 1301969 1303779 := bstep (se 1 (by rfl) ⟨977834, by rfl⟩ : syracuseStep 1303779 = 1955669) B1955669
theorem B1647859 : Blo 1301969 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B1303795 : Blo 1301969 1303795 := bstep (se 1 (by rfl) ⟨977846, by rfl⟩ : syracuseStep 1303795 = 1955693) B1955693
theorem B1303811 : Blo 1301969 1303811 := bstep (se 1 (by rfl) ⟨977858, by rfl⟩ : syracuseStep 1303811 = 1955717) B1955717
theorem B1303827 : Blo 1301969 1303827 := bstep (se 1 (by rfl) ⟨977870, by rfl⟩ : syracuseStep 1303827 = 1955741) B1955741
theorem B1303843 : Blo 1301969 1303843 := bstep (se 1 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 1303843 = 1955765) B1955765
theorem B1303859 : Blo 1301969 1303859 := bstep (se 1 (by rfl) ⟨977894, by rfl⟩ : syracuseStep 1303859 = 1955789) B1955789
theorem B1303875 : Blo 1301969 1303875 := bstep (se 1 (by rfl) ⟨977906, by rfl⟩ : syracuseStep 1303875 = 1955813) B1955813
theorem B1647955 : Blo 1301969 1647955 := bstep (se 1 (by rfl) ⟨1235966, by rfl⟩ : syracuseStep 1647955 = 2471933) B2471933
theorem B1303891 : Blo 1301969 1303891 := bstep (se 1 (by rfl) ⟨977918, by rfl⟩ : syracuseStep 1303891 = 1955837) B1955837
theorem B1303907 : Blo 1301969 1303907 := bstep (se 1 (by rfl) ⟨977930, by rfl⟩ : syracuseStep 1303907 = 1955861) B1955861
theorem B1303923 : Blo 1301969 1303923 := bstep (se 1 (by rfl) ⟨977942, by rfl⟩ : syracuseStep 1303923 = 1955885) B1955885
theorem B3712387 : Blo 1301969 3712387 := bstep (se 1 (by rfl) ⟨2784290, by rfl⟩ : syracuseStep 3712387 = 5568581) B5568581
theorem B1303939 : Blo 1301969 1303939 := bstep (se 1 (by rfl) ⟨977954, by rfl⟩ : syracuseStep 1303939 = 1955909) B1955909
theorem B1303955 : Blo 1301969 1303955 := bstep (se 1 (by rfl) ⟨977966, by rfl⟩ : syracuseStep 1303955 = 1955933) B1955933
theorem B10028485 : Blo 1301969 10028485 := bstep (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) B1880341
theorem B4400621 : Blo 1301969 4400621 := bstep (se 3 (by rfl) ⟨825116, by rfl⟩ : syracuseStep 4400621 = 1650233) B1650233
theorem B11879921 : Blo 1301969 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B3712547 : Blo 1301969 3712547 := bstep (se 1 (by rfl) ⟨2784410, by rfl⟩ : syracuseStep 3712547 = 5568821) B5568821
theorem B4400675 : Blo 1301969 4400675 := bstep (se 1 (by rfl) ⟨3300506, by rfl⟩ : syracuseStep 4400675 = 6601013) B6601013
theorem B6260273 : Blo 1301969 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B2229811 : Blo 1301969 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B16918085 : Blo 1301969 16918085 := bstep (se 4 (by rfl) ⟨1586070, by rfl⟩ : syracuseStep 16918085 = 3172141) B3172141
theorem B2197091 : Blo 1301969 2197091 := bstep (se 1 (by rfl) ⟨1647818, by rfl⟩ : syracuseStep 2197091 = 3295637) B3295637
theorem B2197219 : Blo 1301969 2197219 := bstep (se 1 (by rfl) ⟨1647914, by rfl⟩ : syracuseStep 2197219 = 3295829) B3295829
theorem B5564173 : Blo 1301969 5564173 := bstep (se 3 (by rfl) ⟨1043282, by rfl⟩ : syracuseStep 5564173 = 2086565) B2086565
theorem B5285645 : Blo 1301969 5285645 := bstep (se 3 (by rfl) ⟨991058, by rfl⟩ : syracuseStep 5285645 = 1982117) B1982117
theorem B1648451 : Blo 1301969 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B8456035 : Blo 1301969 8456035 := bstep (se 1 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 8456035 = 12684053) B12684053
theorem B2197361 : Blo 1301969 2197361 := bstep (se 2 (by rfl) ⟨824010, by rfl⟩ : syracuseStep 2197361 = 1648021) B1648021
theorem B6686641 : Blo 1301969 6686641 := bstep (se 2 (by rfl) ⟨2507490, by rfl⟩ : syracuseStep 6686641 = 5014981) B5014981
theorem B2230195 : Blo 1301969 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B2197489 : Blo 1301969 2197489 := bstep (se 2 (by rfl) ⟨824058, by rfl⟩ : syracuseStep 2197489 = 1648117) B1648117
theorem B2197523 : Blo 1301969 2197523 := bstep (se 1 (by rfl) ⟨1648142, by rfl⟩ : syracuseStep 2197523 = 3296285) B3296285
theorem B2197651 : Blo 1301969 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B25389283 : Blo 1301969 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B2197793 : Blo 1301969 2197793 := bstep (se 2 (by rfl) ⟨824172, by rfl⟩ : syracuseStep 2197793 = 1648345) B1648345
theorem B6596963 : Blo 1301969 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B2197921 : Blo 1301969 2197921 := bstep (se 2 (by rfl) ⟨824220, by rfl⟩ : syracuseStep 2197921 = 1648441) B1648441
theorem B2197955 : Blo 1301969 2197955 := bstep (se 1 (by rfl) ⟨1648466, by rfl⟩ : syracuseStep 2197955 = 3296933) B3296933
theorem B4172273 : Blo 1301969 4172273 := bstep (se 2 (by rfl) ⟨1564602, by rfl⟩ : syracuseStep 4172273 = 3129205) B3129205
theorem B1649155 : Blo 1301969 1649155 := bstep (se 1 (by rfl) ⟨1236866, by rfl⟩ : syracuseStep 1649155 = 2473733) B2473733
theorem B2198083 : Blo 1301969 2198083 := bstep (se 1 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 2198083 = 3297125) B3297125
theorem B6261347 : Blo 1301969 6261347 := bstep (se 1 (by rfl) ⟨4696010, by rfl⟩ : syracuseStep 6261347 = 9392021) B9392021
theorem B1649251 : Blo 1301969 1649251 := bstep (se 1 (by rfl) ⟨1236938, by rfl⟩ : syracuseStep 1649251 = 2473877) B2473877
theorem B2640593 : Blo 1301969 2640593 := bstep (se 2 (by rfl) ⟨990222, by rfl⟩ : syracuseStep 2640593 = 1980445) B1980445
theorem B2198225 : Blo 1301969 2198225 := bstep (se 2 (by rfl) ⟨824334, by rfl⟩ : syracuseStep 2198225 = 1648669) B1648669
theorem B20064995 : Blo 1301969 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B1854257 : Blo 1301969 1854257 := bstep (se 2 (by rfl) ⟨695346, by rfl⟩ : syracuseStep 1854257 = 1390693) B1390693
theorem B16706357 : Blo 1301969 16706357 := bstep (se 5 (by rfl) ⟨783110, by rfl⟩ : syracuseStep 16706357 = 1566221) B1566221
theorem B2198353 : Blo 1301969 2198353 := bstep (se 2 (by rfl) ⟨824382, by rfl⟩ : syracuseStep 2198353 = 1648765) B1648765
theorem B2198387 : Blo 1301969 2198387 := bstep (se 1 (by rfl) ⟨1648790, by rfl⟩ : syracuseStep 2198387 = 3297581) B3297581
theorem B1854371 : Blo 1301969 1854371 := bstep (se 1 (by rfl) ⟨1390778, by rfl⟩ : syracuseStep 1854371 = 2781557) B2781557
theorem B4950989 : Blo 1301969 4950989 := bstep (se 3 (by rfl) ⟨928310, by rfl⟩ : syracuseStep 4950989 = 1856621) B1856621
theorem B1854451 : Blo 1301969 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B2198515 : Blo 1301969 2198515 := bstep (se 1 (by rfl) ⟨1648886, by rfl⟩ : syracuseStep 2198515 = 3297773) B3297773
theorem B3345457 : Blo 1301969 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B1649747 : Blo 1301969 1649747 := bstep (se 1 (by rfl) ⟨1237310, by rfl⟩ : syracuseStep 1649747 = 2474621) B2474621
theorem B4172899 : Blo 1301969 4172899 := bstep (se 1 (by rfl) ⟨3129674, by rfl⟩ : syracuseStep 4172899 = 6259349) B6259349
theorem B2198657 : Blo 1301969 2198657 := bstep (se 2 (by rfl) ⟨824496, by rfl⟩ : syracuseStep 2198657 = 1648993) B1648993
theorem B6597773 : Blo 1301969 6597773 := bstep (se 3 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 6597773 = 2474165) B2474165
theorem B1952963 : Blo 1301969 1952963 := bstep (se 1 (by rfl) ⟨1464722, by rfl⟩ : syracuseStep 1952963 = 2929445) B2929445
theorem B7425229 : Blo 1301969 7425229 := bstep (se 3 (by rfl) ⟨1392230, by rfl⟩ : syracuseStep 7425229 = 2784461) B2784461
theorem B1952993 : Blo 1301969 1952993 := bstep (se 2 (by rfl) ⟨732372, by rfl⟩ : syracuseStep 1952993 = 1464745) B1464745
theorem B3296497 : Blo 1301969 3296497 := bstep (se 2 (by rfl) ⟨1236186, by rfl⟩ : syracuseStep 3296497 = 2472373) B2472373
theorem B1953011 : Blo 1301969 1953011 := bstep (se 1 (by rfl) ⟨1464758, by rfl⟩ : syracuseStep 1953011 = 2929517) B2929517
theorem B2198785 : Blo 1301969 2198785 := bstep (se 2 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 2198785 = 1649089) B1649089
theorem B1953041 : Blo 1301969 1953041 := bstep (se 2 (by rfl) ⟨732390, by rfl⟩ : syracuseStep 1953041 = 1464781) B1464781
theorem B1953059 : Blo 1301969 1953059 := bstep (se 1 (by rfl) ⟨1464794, by rfl⟩ : syracuseStep 1953059 = 2929589) B2929589
theorem B2198819 : Blo 1301969 2198819 := bstep (se 1 (by rfl) ⟨1649114, by rfl⟩ : syracuseStep 2198819 = 3298229) B3298229
theorem B1953089 : Blo 1301969 1953089 := bstep (se 2 (by rfl) ⟨732408, by rfl⟩ : syracuseStep 1953089 = 1464817) B1464817
theorem B9899333 : Blo 1301969 9899333 := bstep (se 4 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 9899333 = 1856125) B1856125
theorem B1953107 : Blo 1301969 1953107 := bstep (se 1 (by rfl) ⟨1464830, by rfl⟩ : syracuseStep 1953107 = 2929661) B2929661
theorem B1953137 : Blo 1301969 1953137 := bstep (se 2 (by rfl) ⟨732426, by rfl⟩ : syracuseStep 1953137 = 1464853) B1464853
theorem B12520817 : Blo 1301969 12520817 := bstep (se 2 (by rfl) ⟨4695306, by rfl⟩ : syracuseStep 12520817 = 9390613) B9390613
theorem B1953155 : Blo 1301969 1953155 := bstep (se 1 (by rfl) ⟨1464866, by rfl⟩ : syracuseStep 1953155 = 2929733) B2929733
theorem B1953185 : Blo 1301969 1953185 := bstep (se 2 (by rfl) ⟨732444, by rfl⟩ : syracuseStep 1953185 = 1464889) B1464889
theorem B2198947 : Blo 1301969 2198947 := bstep (se 1 (by rfl) ⟨1649210, by rfl⟩ : syracuseStep 2198947 = 3298421) B3298421
theorem B1953203 : Blo 1301969 1953203 := bstep (se 1 (by rfl) ⟨1464902, by rfl⟩ : syracuseStep 1953203 = 2929805) B2929805
theorem B1953233 : Blo 1301969 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B1953251 : Blo 1301969 1953251 := bstep (se 1 (by rfl) ⟨1464938, by rfl⟩ : syracuseStep 1953251 = 2929877) B2929877
theorem B1953281 : Blo 1301969 1953281 := bstep (se 2 (by rfl) ⟨732480, by rfl⟩ : syracuseStep 1953281 = 1464961) B1464961
theorem B3296771 : Blo 1301969 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B1953299 : Blo 1301969 1953299 := bstep (se 1 (by rfl) ⟨1464974, by rfl⟩ : syracuseStep 1953299 = 2929949) B2929949
theorem B1855009 : Blo 1301969 1855009 := bstep (se 2 (by rfl) ⟨695628, by rfl⟩ : syracuseStep 1855009 = 1391257) B1391257
theorem B3010097 : Blo 1301969 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B1953329 : Blo 1301969 1953329 := bstep (se 2 (by rfl) ⟨732498, by rfl⟩ : syracuseStep 1953329 = 1464997) B1464997
theorem B2199089 : Blo 1301969 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B1953347 : Blo 1301969 1953347 := bstep (se 1 (by rfl) ⟨1465010, by rfl⟩ : syracuseStep 1953347 = 2930021) B2930021
theorem B4394573 : Blo 1301969 4394573 := bstep (se 3 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 4394573 = 1647965) B1647965
theorem B1953377 : Blo 1301969 1953377 := bstep (se 2 (by rfl) ⟨732516, by rfl⟩ : syracuseStep 1953377 = 1465033) B1465033
theorem B1953395 : Blo 1301969 1953395 := bstep (se 1 (by rfl) ⟨1465046, by rfl⟩ : syracuseStep 1953395 = 2930093) B2930093
theorem B4394627 : Blo 1301969 4394627 := bstep (se 1 (by rfl) ⟨3295970, by rfl⟩ : syracuseStep 4394627 = 6591941) B6591941
theorem B4943501 : Blo 1301969 4943501 := bstep (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) B1853813
theorem B1953425 : Blo 1301969 1953425 := bstep (se 2 (by rfl) ⟨732534, by rfl⟩ : syracuseStep 1953425 = 1465069) B1465069
theorem B1953443 : Blo 1301969 1953443 := bstep (se 1 (by rfl) ⟨1465082, by rfl⟩ : syracuseStep 1953443 = 2930165) B2930165
theorem B2199217 : Blo 1301969 2199217 := bstep (se 2 (by rfl) ⟨824706, by rfl⟩ : syracuseStep 2199217 = 1649413) B1649413
theorem B1953473 : Blo 1301969 1953473 := bstep (se 2 (by rfl) ⟨732552, by rfl⟩ : syracuseStep 1953473 = 1465105) B1465105
theorem B3296963 : Blo 1301969 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B1953491 : Blo 1301969 1953491 := bstep (se 1 (by rfl) ⟨1465118, by rfl⟩ : syracuseStep 1953491 = 2930237) B2930237
theorem B2199251 : Blo 1301969 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B14839523 : Blo 1301969 14839523 := bstep (se 1 (by rfl) ⟨11129642, by rfl⟩ : syracuseStep 14839523 = 22259285) B22259285
theorem B1953521 : Blo 1301969 1953521 := bstep (se 2 (by rfl) ⟨732570, by rfl⟩ : syracuseStep 1953521 = 1465141) B1465141
theorem B1953539 : Blo 1301969 1953539 := bstep (se 1 (by rfl) ⟨1465154, by rfl⟩ : syracuseStep 1953539 = 2930309) B2930309
theorem B7040773 : Blo 1301969 7040773 := bstep (se 4 (by rfl) ⟨660072, by rfl⟩ : syracuseStep 7040773 = 1320145) B1320145
theorem B1953569 : Blo 1301969 1953569 := bstep (se 2 (by rfl) ⟨732588, by rfl⟩ : syracuseStep 1953569 = 1465177) B1465177
theorem B1953587 : Blo 1301969 1953587 := bstep (se 1 (by rfl) ⟨1465190, by rfl⟩ : syracuseStep 1953587 = 2930381) B2930381
theorem B1953617 : Blo 1301969 1953617 := bstep (se 2 (by rfl) ⟨732606, by rfl⟩ : syracuseStep 1953617 = 1465213) B1465213
theorem B1429331 : Blo 1301969 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B2199379 : Blo 1301969 2199379 := bstep (se 1 (by rfl) ⟨1649534, by rfl⟩ : syracuseStep 2199379 = 3299069) B3299069
theorem B1953635 : Blo 1301969 1953635 := bstep (se 1 (by rfl) ⟨1465226, by rfl⟩ : syracuseStep 1953635 = 2930453) B2930453
theorem B1953665 : Blo 1301969 1953665 := bstep (se 2 (by rfl) ⟨732624, by rfl⟩ : syracuseStep 1953665 = 1465249) B1465249
theorem B4394897 : Blo 1301969 4394897 := bstep (se 2 (by rfl) ⟨1648086, by rfl⟩ : syracuseStep 4394897 = 3296173) B3296173
theorem B1953683 : Blo 1301969 1953683 := bstep (se 1 (by rfl) ⟨1465262, by rfl⟩ : syracuseStep 1953683 = 2930525) B2930525
theorem B1953713 : Blo 1301969 1953713 := bstep (se 2 (by rfl) ⟨732642, by rfl⟩ : syracuseStep 1953713 = 1465285) B1465285
theorem B1953731 : Blo 1301969 1953731 := bstep (se 1 (by rfl) ⟨1465298, by rfl⟩ : syracuseStep 1953731 = 2930597) B2930597
theorem B1953761 : Blo 1301969 1953761 := bstep (se 2 (by rfl) ⟨732660, by rfl⟩ : syracuseStep 1953761 = 1465321) B1465321
theorem B2199521 : Blo 1301969 2199521 := bstep (se 2 (by rfl) ⟨824820, by rfl⟩ : syracuseStep 2199521 = 1649641) B1649641
theorem B15044579 : Blo 1301969 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B1953779 : Blo 1301969 1953779 := bstep (se 1 (by rfl) ⟨1465334, by rfl⟩ : syracuseStep 1953779 = 2930669) B2930669
theorem B1953809 : Blo 1301969 1953809 := bstep (se 2 (by rfl) ⟨732678, by rfl⟩ : syracuseStep 1953809 = 1465357) B1465357
theorem B1953827 : Blo 1301969 1953827 := bstep (se 1 (by rfl) ⟨1465370, by rfl⟩ : syracuseStep 1953827 = 2930741) B2930741
theorem B1953857 : Blo 1301969 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B1953875 : Blo 1301969 1953875 := bstep (se 1 (by rfl) ⟨1465406, by rfl⟩ : syracuseStep 1953875 = 2930813) B2930813
theorem B2199649 : Blo 1301969 2199649 := bstep (se 2 (by rfl) ⟨824868, by rfl⟩ : syracuseStep 2199649 = 1649737) B1649737
theorem B1953905 : Blo 1301969 1953905 := bstep (se 2 (by rfl) ⟨732714, by rfl⟩ : syracuseStep 1953905 = 1465429) B1465429
theorem B1953923 : Blo 1301969 1953923 := bstep (se 1 (by rfl) ⟨1465442, by rfl⟩ : syracuseStep 1953923 = 2930885) B2930885
theorem B2199683 : Blo 1301969 2199683 := bstep (se 1 (by rfl) ⟨1649762, by rfl⟩ : syracuseStep 2199683 = 3299525) B3299525
theorem B1953953 : Blo 1301969 1953953 := bstep (se 2 (by rfl) ⟨732732, by rfl⟩ : syracuseStep 1953953 = 1465465) B1465465
theorem B1953971 : Blo 1301969 1953971 := bstep (se 1 (by rfl) ⟨1465478, by rfl⟩ : syracuseStep 1953971 = 2930957) B2930957
theorem B1954001 : Blo 1301969 1954001 := bstep (se 2 (by rfl) ⟨732750, by rfl⟩ : syracuseStep 1954001 = 1465501) B1465501
theorem B1954019 : Blo 1301969 1954019 := bstep (se 1 (by rfl) ⟨1465514, by rfl⟩ : syracuseStep 1954019 = 2931029) B2931029
theorem B1855715 : Blo 1301969 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B1954049 : Blo 1301969 1954049 := bstep (se 2 (by rfl) ⟨732768, by rfl⟩ : syracuseStep 1954049 = 1465537) B1465537
theorem B2199811 : Blo 1301969 2199811 := bstep (se 1 (by rfl) ⟨1649858, by rfl⟩ : syracuseStep 2199811 = 3299717) B3299717
theorem B1954067 : Blo 1301969 1954067 := bstep (se 1 (by rfl) ⟨1465550, by rfl⟩ : syracuseStep 1954067 = 2931101) B2931101
theorem B1954097 : Blo 1301969 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B4174129 : Blo 1301969 4174129 := bstep (se 2 (by rfl) ⟨1565298, by rfl⟩ : syracuseStep 4174129 = 3130597) B3130597
theorem B1954115 : Blo 1301969 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B1954145 : Blo 1301969 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B1954163 : Blo 1301969 1954163 := bstep (se 1 (by rfl) ⟨1465622, by rfl⟩ : syracuseStep 1954163 = 2931245) B2931245
theorem B1954193 : Blo 1301969 1954193 := bstep (se 2 (by rfl) ⟨732822, by rfl⟩ : syracuseStep 1954193 = 1465645) B1465645
theorem B2199953 : Blo 1301969 2199953 := bstep (se 2 (by rfl) ⟨824982, by rfl⟩ : syracuseStep 2199953 = 1649965) B1649965
theorem B1954211 : Blo 1301969 1954211 := bstep (se 1 (by rfl) ⟨1465658, by rfl⟩ : syracuseStep 1954211 = 2931317) B2931317
theorem B4395437 : Blo 1301969 4395437 := bstep (se 3 (by rfl) ⟨824144, by rfl⟩ : syracuseStep 4395437 = 1648289) B1648289
theorem B1954241 : Blo 1301969 1954241 := bstep (se 2 (by rfl) ⟨732840, by rfl⟩ : syracuseStep 1954241 = 1465681) B1465681
theorem B1954259 : Blo 1301969 1954259 := bstep (se 1 (by rfl) ⟨1465694, by rfl⟩ : syracuseStep 1954259 = 2931389) B2931389
theorem B2970083 : Blo 1301969 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B4395491 : Blo 1301969 4395491 := bstep (se 1 (by rfl) ⟨3296618, by rfl⟩ : syracuseStep 4395491 = 6593237) B6593237
theorem B1954289 : Blo 1301969 1954289 := bstep (se 2 (by rfl) ⟨732858, by rfl⟩ : syracuseStep 1954289 = 1465717) B1465717
theorem B1954307 : Blo 1301969 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B2200081 : Blo 1301969 2200081 := bstep (se 2 (by rfl) ⟨825030, by rfl⟩ : syracuseStep 2200081 = 1650061) B1650061
theorem B1954337 : Blo 1301969 1954337 := bstep (se 2 (by rfl) ⟨732876, by rfl⟩ : syracuseStep 1954337 = 1465753) B1465753
theorem B1954355 : Blo 1301969 1954355 := bstep (se 1 (by rfl) ⟨1465766, by rfl⟩ : syracuseStep 1954355 = 2931533) B2931533
theorem B2200115 : Blo 1301969 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B30511669 : Blo 1301969 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1954385 : Blo 1301969 1954385 := bstep (se 2 (by rfl) ⟨732894, by rfl⟩ : syracuseStep 1954385 = 1465789) B1465789
theorem B1954403 : Blo 1301969 1954403 := bstep (se 1 (by rfl) ⟨1465802, by rfl⟩ : syracuseStep 1954403 = 2931605) B2931605
theorem B3297905 : Blo 1301969 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B1954433 : Blo 1301969 1954433 := bstep (se 2 (by rfl) ⟨732912, by rfl⟩ : syracuseStep 1954433 = 1465825) B1465825
theorem B1954451 : Blo 1301969 1954451 := bstep (se 1 (by rfl) ⟨1465838, by rfl⟩ : syracuseStep 1954451 = 2931677) B2931677
theorem B3297955 : Blo 1301969 3297955 := bstep (se 1 (by rfl) ⟨2473466, by rfl⟩ : syracuseStep 3297955 = 4946933) B4946933
theorem B1954481 : Blo 1301969 1954481 := bstep (se 2 (by rfl) ⟨732930, by rfl⟩ : syracuseStep 1954481 = 1465861) B1465861
theorem B2200243 : Blo 1301969 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B1954499 : Blo 1301969 1954499 := bstep (se 1 (by rfl) ⟨1465874, by rfl⟩ : syracuseStep 1954499 = 2931749) B2931749
theorem B1954529 : Blo 1301969 1954529 := bstep (se 2 (by rfl) ⟨732948, by rfl⟩ : syracuseStep 1954529 = 1465897) B1465897
theorem B4395761 : Blo 1301969 4395761 := bstep (se 2 (by rfl) ⟨1648410, by rfl⟩ : syracuseStep 4395761 = 3296821) B3296821
theorem B1954547 : Blo 1301969 1954547 := bstep (se 1 (by rfl) ⟨1465910, by rfl⟩ : syracuseStep 1954547 = 2931821) B2931821
theorem B1954577 : Blo 1301969 1954577 := bstep (se 2 (by rfl) ⟨732966, by rfl⟩ : syracuseStep 1954577 = 1465933) B1465933
theorem B1954595 : Blo 1301969 1954595 := bstep (se 1 (by rfl) ⟨1465946, by rfl⟩ : syracuseStep 1954595 = 2931893) B2931893
theorem B2782001 : Blo 1301969 2782001 := bstep (se 2 (by rfl) ⟨1043250, by rfl⟩ : syracuseStep 2782001 = 2086501) B2086501
theorem B3298097 : Blo 1301969 3298097 := bstep (se 2 (by rfl) ⟨1236786, by rfl⟩ : syracuseStep 3298097 = 2473573) B2473573
theorem B1954625 : Blo 1301969 1954625 := bstep (se 2 (by rfl) ⟨732984, by rfl⟩ : syracuseStep 1954625 = 1465969) B1465969
theorem B2200385 : Blo 1301969 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B2782019 : Blo 1301969 2782019 := bstep (se 1 (by rfl) ⟨2086514, by rfl⟩ : syracuseStep 2782019 = 4173029) B4173029
theorem B1954643 : Blo 1301969 1954643 := bstep (se 1 (by rfl) ⟨1465982, by rfl⟩ : syracuseStep 1954643 = 2931965) B2931965
theorem B1856353 : Blo 1301969 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B2085745 : Blo 1301969 2085745 := bstep (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) B1564309
theorem B1954673 : Blo 1301969 1954673 := bstep (se 2 (by rfl) ⟨733002, by rfl⟩ : syracuseStep 1954673 = 1466005) B1466005
theorem B1954691 : Blo 1301969 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B4174733 : Blo 1301969 4174733 := bstep (se 3 (by rfl) ⟨782762, by rfl⟩ : syracuseStep 4174733 = 1565525) B1565525
theorem B2929553 : Blo 1301969 2929553 := bstep (se 2 (by rfl) ⟨1098582, by rfl⟩ : syracuseStep 2929553 = 2197165) B2197165
theorem B1954721 : Blo 1301969 1954721 := bstep (se 2 (by rfl) ⟨733020, by rfl⟩ : syracuseStep 1954721 = 1466041) B1466041
theorem B2929571 : Blo 1301969 2929571 := bstep (se 1 (by rfl) ⟨2197178, by rfl⟩ : syracuseStep 2929571 = 4394357) B4394357
theorem B3961763 : Blo 1301969 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B1954739 : Blo 1301969 1954739 := bstep (se 1 (by rfl) ⟨1466054, by rfl⟩ : syracuseStep 1954739 = 2932109) B2932109
theorem B1954769 : Blo 1301969 1954769 := bstep (se 2 (by rfl) ⟨733038, by rfl⟩ : syracuseStep 1954769 = 1466077) B1466077
theorem B1856467 : Blo 1301969 1856467 := bstep (se 1 (by rfl) ⟨1392350, by rfl⟩ : syracuseStep 1856467 = 2784701) B2784701
theorem B1954787 : Blo 1301969 1954787 := bstep (se 1 (by rfl) ⟨1466090, by rfl⟩ : syracuseStep 1954787 = 2932181) B2932181
theorem B1954817 : Blo 1301969 1954817 := bstep (se 2 (by rfl) ⟨733056, by rfl⟩ : syracuseStep 1954817 = 1466113) B1466113
theorem B1954835 : Blo 1301969 1954835 := bstep (se 1 (by rfl) ⟨1466126, by rfl⟩ : syracuseStep 1954835 = 2932253) B2932253
theorem B1954865 : Blo 1301969 1954865 := bstep (se 2 (by rfl) ⟨733074, by rfl⟩ : syracuseStep 1954865 = 1466149) B1466149
theorem B1881139 : Blo 1301969 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B1954883 : Blo 1301969 1954883 := bstep (se 1 (by rfl) ⟨1466162, by rfl⟩ : syracuseStep 1954883 = 2932325) B2932325
theorem B1954913 : Blo 1301969 1954913 := bstep (se 2 (by rfl) ⟨733092, by rfl⟩ : syracuseStep 1954913 = 1466185) B1466185
theorem B3708013 : Blo 1301969 3708013 := bstep (se 3 (by rfl) ⟨695252, by rfl⟩ : syracuseStep 3708013 = 1390505) B1390505
theorem B10024049 : Blo 1301969 10024049 := bstep (se 2 (by rfl) ⟨3759018, by rfl⟩ : syracuseStep 10024049 = 7518037) B7518037
theorem B1954931 : Blo 1301969 1954931 := bstep (se 1 (by rfl) ⟨1466198, by rfl⟩ : syracuseStep 1954931 = 2932397) B2932397
theorem B1954961 : Blo 1301969 1954961 := bstep (se 2 (by rfl) ⟨733110, by rfl⟩ : syracuseStep 1954961 = 1466221) B1466221
theorem B1954979 : Blo 1301969 1954979 := bstep (se 1 (by rfl) ⟨1466234, by rfl⟩ : syracuseStep 1954979 = 2932469) B2932469
theorem B2929841 : Blo 1301969 2929841 := bstep (se 2 (by rfl) ⟨1098690, by rfl⟩ : syracuseStep 2929841 = 2197381) B2197381
theorem B1955009 : Blo 1301969 1955009 := bstep (se 2 (by rfl) ⟨733128, by rfl⟩ : syracuseStep 1955009 = 1466257) B1466257
theorem B2929859 : Blo 1301969 2929859 := bstep (se 1 (by rfl) ⟨2197394, by rfl⟩ : syracuseStep 2929859 = 4394789) B4394789
theorem B8352973 : Blo 1301969 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1955027 : Blo 1301969 1955027 := bstep (se 1 (by rfl) ⟨1466270, by rfl⟩ : syracuseStep 1955027 = 2932541) B2932541
theorem B1955057 : Blo 1301969 1955057 := bstep (se 2 (by rfl) ⟨733146, by rfl⟩ : syracuseStep 1955057 = 1466293) B1466293
theorem B1955075 : Blo 1301969 1955075 := bstep (se 1 (by rfl) ⟨1466306, by rfl⟩ : syracuseStep 1955075 = 2932613) B2932613
theorem B3708173 : Blo 1301969 3708173 := bstep (se 3 (by rfl) ⟨695282, by rfl⟩ : syracuseStep 3708173 = 1390565) B1390565
theorem B4396301 : Blo 1301969 4396301 := bstep (se 3 (by rfl) ⟨824306, by rfl⟩ : syracuseStep 4396301 = 1648613) B1648613
theorem B1955105 : Blo 1301969 1955105 := bstep (se 2 (by rfl) ⟨733164, by rfl⟩ : syracuseStep 1955105 = 1466329) B1466329
theorem B6591779 : Blo 1301969 6591779 := bstep (se 1 (by rfl) ⟨4943834, by rfl⟩ : syracuseStep 6591779 = 9887669) B9887669
theorem B2086193 : Blo 1301969 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B2970929 : Blo 1301969 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B1955123 : Blo 1301969 1955123 := bstep (se 1 (by rfl) ⟨1466342, by rfl⟩ : syracuseStep 1955123 = 2932685) B2932685
theorem B4396355 : Blo 1301969 4396355 := bstep (se 1 (by rfl) ⟨3297266, by rfl⟩ : syracuseStep 4396355 = 6594533) B6594533
theorem B1955153 : Blo 1301969 1955153 := bstep (se 2 (by rfl) ⟨733182, by rfl⟩ : syracuseStep 1955153 = 1466365) B1466365
theorem B1955171 : Blo 1301969 1955171 := bstep (se 1 (by rfl) ⟨1466378, by rfl⟩ : syracuseStep 1955171 = 2932757) B2932757
theorem B1955201 : Blo 1301969 1955201 := bstep (se 2 (by rfl) ⟨733200, by rfl⟩ : syracuseStep 1955201 = 1466401) B1466401
theorem B1955219 : Blo 1301969 1955219 := bstep (se 1 (by rfl) ⟨1466414, by rfl⟩ : syracuseStep 1955219 = 2932829) B2932829
theorem B1955249 : Blo 1301969 1955249 := bstep (se 2 (by rfl) ⟨733218, by rfl⟩ : syracuseStep 1955249 = 1466437) B1466437
theorem B3708355 : Blo 1301969 3708355 := bstep (se 1 (by rfl) ⟨2781266, by rfl⟩ : syracuseStep 3708355 = 5562533) B5562533
theorem B1955267 : Blo 1301969 1955267 := bstep (se 1 (by rfl) ⟨1466450, by rfl⟩ : syracuseStep 1955267 = 2932901) B2932901
theorem B2930129 : Blo 1301969 2930129 := bstep (se 2 (by rfl) ⟨1098798, by rfl⟩ : syracuseStep 2930129 = 2197597) B2197597
theorem B1955297 : Blo 1301969 1955297 := bstep (se 2 (by rfl) ⟨733236, by rfl⟩ : syracuseStep 1955297 = 1466473) B1466473
theorem B2930147 : Blo 1301969 2930147 := bstep (se 1 (by rfl) ⟨2197610, by rfl⟩ : syracuseStep 2930147 = 4395221) B4395221
theorem B1955315 : Blo 1301969 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B7419397 : Blo 1301969 7419397 := bstep (se 4 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 7419397 = 1391137) B1391137
theorem B1955345 : Blo 1301969 1955345 := bstep (se 2 (by rfl) ⟨733254, by rfl⟩ : syracuseStep 1955345 = 1466509) B1466509
theorem B1955363 : Blo 1301969 1955363 := bstep (se 1 (by rfl) ⟨1466522, by rfl⟩ : syracuseStep 1955363 = 2933045) B2933045
theorem B1955393 : Blo 1301969 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B4396625 : Blo 1301969 4396625 := bstep (se 2 (by rfl) ⟨1648734, by rfl⟩ : syracuseStep 4396625 = 3297469) B3297469
theorem B1955411 : Blo 1301969 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B1955441 : Blo 1301969 1955441 := bstep (se 2 (by rfl) ⟨733290, by rfl⟩ : syracuseStep 1955441 = 1466581) B1466581
theorem B1955459 : Blo 1301969 1955459 := bstep (se 1 (by rfl) ⟨1466594, by rfl⟩ : syracuseStep 1955459 = 2933189) B2933189
theorem B1955489 : Blo 1301969 1955489 := bstep (se 2 (by rfl) ⟨733308, by rfl⟩ : syracuseStep 1955489 = 1466617) B1466617
theorem B1955507 : Blo 1301969 1955507 := bstep (se 1 (by rfl) ⟨1466630, by rfl⟩ : syracuseStep 1955507 = 2933261) B2933261
theorem B1955537 : Blo 1301969 1955537 := bstep (se 2 (by rfl) ⟨733326, by rfl⟩ : syracuseStep 1955537 = 1466653) B1466653
theorem B1955555 : Blo 1301969 1955555 := bstep (se 1 (by rfl) ⟨1466666, by rfl⟩ : syracuseStep 1955555 = 2933333) B2933333
theorem B2930417 : Blo 1301969 2930417 := bstep (se 2 (by rfl) ⟨1098906, by rfl⟩ : syracuseStep 2930417 = 2197813) B2197813
theorem B1955585 : Blo 1301969 1955585 := bstep (se 2 (by rfl) ⟨733344, by rfl⟩ : syracuseStep 1955585 = 1466689) B1466689
theorem B2930435 : Blo 1301969 2930435 := bstep (se 1 (by rfl) ⟨2197826, by rfl⟩ : syracuseStep 2930435 = 4395653) B4395653
theorem B3299089 : Blo 1301969 3299089 := bstep (se 2 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 3299089 = 2474317) B2474317
theorem B1955603 : Blo 1301969 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B5281571 : Blo 1301969 5281571 := bstep (se 1 (by rfl) ⟨3961178, by rfl⟩ : syracuseStep 5281571 = 7922357) B7922357
theorem B1955633 : Blo 1301969 1955633 := bstep (se 2 (by rfl) ⟨733362, by rfl⟩ : syracuseStep 1955633 = 1466725) B1466725
theorem B1955651 : Blo 1301969 1955651 := bstep (se 1 (by rfl) ⟨1466738, by rfl⟩ : syracuseStep 1955651 = 2933477) B2933477
theorem B1955681 : Blo 1301969 1955681 := bstep (se 2 (by rfl) ⟨733380, by rfl⟩ : syracuseStep 1955681 = 1466761) B1466761
theorem B1955699 : Blo 1301969 1955699 := bstep (se 1 (by rfl) ⟨1466774, by rfl⟩ : syracuseStep 1955699 = 2933549) B2933549
theorem B1955729 : Blo 1301969 1955729 := bstep (se 2 (by rfl) ⟨733398, by rfl⟩ : syracuseStep 1955729 = 1466797) B1466797
theorem B1955747 : Blo 1301969 1955747 := bstep (se 1 (by rfl) ⟨1466810, by rfl⟩ : syracuseStep 1955747 = 2933621) B2933621
theorem B1955777 : Blo 1301969 1955777 := bstep (se 2 (by rfl) ⟨733416, by rfl⟩ : syracuseStep 1955777 = 1466833) B1466833
theorem B1955795 : Blo 1301969 1955795 := bstep (se 1 (by rfl) ⟨1466846, by rfl⟩ : syracuseStep 1955795 = 2933693) B2933693
theorem B5568497 : Blo 1301969 5568497 := bstep (se 2 (by rfl) ⟨2088186, by rfl⟩ : syracuseStep 5568497 = 4176373) B4176373
theorem B6600689 : Blo 1301969 6600689 := bstep (se 2 (by rfl) ⟨2475258, by rfl⟩ : syracuseStep 6600689 = 4950517) B4950517
theorem B1955825 : Blo 1301969 1955825 := bstep (se 2 (by rfl) ⟨733434, by rfl⟩ : syracuseStep 1955825 = 1466869) B1466869
theorem B1955843 : Blo 1301969 1955843 := bstep (se 1 (by rfl) ⟨1466882, by rfl⟩ : syracuseStep 1955843 = 2933765) B2933765
theorem B2930705 : Blo 1301969 2930705 := bstep (se 2 (by rfl) ⟨1099014, by rfl⟩ : syracuseStep 2930705 = 2198029) B2198029
theorem B1955873 : Blo 1301969 1955873 := bstep (se 2 (by rfl) ⟨733452, by rfl⟩ : syracuseStep 1955873 = 1466905) B1466905
theorem B2471971 : Blo 1301969 2471971 := bstep (se 1 (by rfl) ⟨1853978, by rfl⟩ : syracuseStep 2471971 = 3707957) B3707957
theorem B2930723 : Blo 1301969 2930723 := bstep (se 1 (by rfl) ⟨2198042, by rfl⟩ : syracuseStep 2930723 = 4396085) B4396085
theorem B3299363 : Blo 1301969 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B5568547 : Blo 1301969 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B1955891 : Blo 1301969 1955891 := bstep (se 1 (by rfl) ⟨1466918, by rfl⟩ : syracuseStep 1955891 = 2933837) B2933837
theorem B6592589 : Blo 1301969 6592589 := bstep (se 3 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 6592589 = 2472221) B2472221
theorem B1955921 : Blo 1301969 1955921 := bstep (se 2 (by rfl) ⟨733470, by rfl⟩ : syracuseStep 1955921 = 1466941) B1466941
theorem B1783891 : Blo 1301969 1783891 := bstep (se 1 (by rfl) ⟨1337918, by rfl⟩ : syracuseStep 1783891 = 2675837) B2675837
theorem B9893987 : Blo 1301969 9893987 := bstep (se 1 (by rfl) ⟨7420490, by rfl⟩ : syracuseStep 9893987 = 14840981) B14840981
theorem B1955939 : Blo 1301969 1955939 := bstep (se 1 (by rfl) ⟨1466954, by rfl⟩ : syracuseStep 1955939 = 2933909) B2933909
theorem B4397165 : Blo 1301969 4397165 := bstep (se 3 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 4397165 = 1648937) B1648937
theorem B2087059 : Blo 1301969 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B4397219 : Blo 1301969 4397219 := bstep (se 1 (by rfl) ⟨3297914, by rfl⟩ : syracuseStep 4397219 = 6595829) B6595829
theorem B3299555 : Blo 1301969 3299555 := bstep (se 1 (by rfl) ⟨2474666, by rfl⟩ : syracuseStep 3299555 = 4949333) B4949333
theorem B1906931 : Blo 1301969 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B2930993 : Blo 1301969 2930993 := bstep (se 2 (by rfl) ⟨1099122, by rfl⟩ : syracuseStep 2930993 = 2198245) B2198245
theorem B3963185 : Blo 1301969 3963185 := bstep (se 2 (by rfl) ⟨1486194, by rfl⟩ : syracuseStep 3963185 = 2972389) B2972389
theorem B1390915 : Blo 1301969 1390915 := bstep (se 1 (by rfl) ⟨1043186, by rfl⟩ : syracuseStep 1390915 = 2086373) B2086373
theorem B2931011 : Blo 1301969 2931011 := bstep (se 1 (by rfl) ⟨2198258, by rfl⟩ : syracuseStep 2931011 = 4396517) B4396517
theorem B4397489 : Blo 1301969 4397489 := bstep (se 2 (by rfl) ⟨1649058, by rfl⟩ : syracuseStep 4397489 = 3298117) B3298117
theorem B2472419 : Blo 1301969 2472419 := bstep (se 1 (by rfl) ⟨1854314, by rfl⟩ : syracuseStep 2472419 = 3708629) B3708629
theorem B4946417 : Blo 1301969 4946417 := bstep (se 2 (by rfl) ⟨1854906, by rfl⟩ : syracuseStep 4946417 = 3709813) B3709813
theorem B1464835 : Blo 1301969 1464835 := bstep (se 1 (by rfl) ⟨1098626, by rfl⟩ : syracuseStep 1464835 = 2197253) B2197253
theorem B3258883 : Blo 1301969 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B15039029 : Blo 1301969 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B2931281 : Blo 1301969 2931281 := bstep (se 2 (by rfl) ⟨1099230, by rfl⟩ : syracuseStep 2931281 = 2198461) B2198461
theorem B2931299 : Blo 1301969 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B1464979 : Blo 1301969 1464979 := bstep (se 1 (by rfl) ⟨1098734, by rfl⟩ : syracuseStep 1464979 = 2197469) B2197469
theorem B2472707 : Blo 1301969 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B2784017 : Blo 1301969 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B1465123 : Blo 1301969 1465123 := bstep (se 1 (by rfl) ⟨1098842, by rfl⟩ : syracuseStep 1465123 = 2197685) B2197685
theorem B3341105 : Blo 1301969 3341105 := bstep (se 2 (by rfl) ⟨1252914, by rfl⟩ : syracuseStep 3341105 = 2505829) B2505829
theorem B3709745 : Blo 1301969 3709745 := bstep (se 2 (by rfl) ⟨1391154, by rfl⟩ : syracuseStep 3709745 = 2782309) B2782309
theorem B2087731 : Blo 1301969 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B2087777 : Blo 1301969 2087777 := bstep (se 2 (by rfl) ⟨782916, by rfl⟩ : syracuseStep 2087777 = 1565833) B1565833
theorem B2931569 : Blo 1301969 2931569 := bstep (se 2 (by rfl) ⟨1099338, by rfl⟩ : syracuseStep 2931569 = 2198677) B2198677
theorem B2931587 : Blo 1301969 2931587 := bstep (se 1 (by rfl) ⟨2198690, by rfl⟩ : syracuseStep 2931587 = 4397381) B4397381
theorem B1465267 : Blo 1301969 1465267 := bstep (se 1 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 1465267 = 2197901) B2197901
theorem B4398029 : Blo 1301969 4398029 := bstep (se 3 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 4398029 = 1649261) B1649261
theorem B3128291 : Blo 1301969 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B4398083 : Blo 1301969 4398083 := bstep (se 1 (by rfl) ⟨3298562, by rfl⟩ : syracuseStep 4398083 = 6597125) B6597125
theorem B1465411 : Blo 1301969 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B9657413 : Blo 1301969 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B6020173 : Blo 1301969 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B13565069 : Blo 1301969 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B2931857 : Blo 1301969 2931857 := bstep (se 2 (by rfl) ⟨1099446, by rfl⟩ : syracuseStep 2931857 = 2198893) B2198893
theorem B3300497 : Blo 1301969 3300497 := bstep (se 2 (by rfl) ⟨1237686, by rfl⟩ : syracuseStep 3300497 = 2475373) B2475373
theorem B3128483 : Blo 1301969 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B2931875 : Blo 1301969 2931875 := bstep (se 1 (by rfl) ⟨2198906, by rfl⟩ : syracuseStep 2931875 = 4397813) B4397813
theorem B3300547 : Blo 1301969 3300547 := bstep (se 1 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 3300547 = 4950821) B4950821
theorem B1465555 : Blo 1301969 1465555 := bstep (se 1 (by rfl) ⟨1099166, by rfl⟩ : syracuseStep 1465555 = 2198333) B2198333
theorem B12524813 : Blo 1301969 12524813 := bstep (se 3 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 12524813 = 4696805) B4696805
theorem B4398353 : Blo 1301969 4398353 := bstep (se 2 (by rfl) ⟨1649382, by rfl⟩ : syracuseStep 4398353 = 3298765) B3298765
theorem B2784547 : Blo 1301969 2784547 := bstep (se 1 (by rfl) ⟨2088410, by rfl⟩ : syracuseStep 2784547 = 4176821) B4176821
theorem B1391923 : Blo 1301969 1391923 := bstep (se 1 (by rfl) ⟨1043942, by rfl⟩ : syracuseStep 1391923 = 2087885) B2087885
theorem B2088289 : Blo 1301969 2088289 := bstep (se 2 (by rfl) ⟨783108, by rfl⟩ : syracuseStep 2088289 = 1566217) B1566217
theorem B1760611 : Blo 1301969 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B1465699 : Blo 1301969 1465699 := bstep (se 1 (by rfl) ⟨1099274, by rfl⟩ : syracuseStep 1465699 = 2198549) B2198549
theorem B32128397 : Blo 1301969 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B2973073 : Blo 1301969 2973073 := bstep (se 2 (by rfl) ⟨1114902, by rfl⟩ : syracuseStep 2973073 = 2229805) B2229805
theorem B2932145 : Blo 1301969 2932145 := bstep (se 2 (by rfl) ⟨1099554, by rfl⟩ : syracuseStep 2932145 = 2199109) B2199109
theorem B2932163 : Blo 1301969 2932163 := bstep (se 1 (by rfl) ⟨2199122, by rfl⟩ : syracuseStep 2932163 = 4398245) B4398245
theorem B17817029 : Blo 1301969 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B7421381 : Blo 1301969 7421381 := bstep (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) B1391509
theorem B1301971 : Blo 1301969 1301971 := bstep (se 1 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 1301971 = 1952957) B1952957
theorem B1301987 : Blo 1301969 1301987 := bstep (se 1 (by rfl) ⟨976490, by rfl⟩ : syracuseStep 1301987 = 1952981) B1952981
theorem B1302003 : Blo 1301969 1302003 := bstep (se 1 (by rfl) ⟨976502, by rfl⟩ : syracuseStep 1302003 = 1953005) B1953005
theorem B1465843 : Blo 1301969 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B1302019 : Blo 1301969 1302019 := bstep (se 1 (by rfl) ⟨976514, by rfl⟩ : syracuseStep 1302019 = 1953029) B1953029
theorem B1302035 : Blo 1301969 1302035 := bstep (se 1 (by rfl) ⟨976526, by rfl⟩ : syracuseStep 1302035 = 1953053) B1953053
theorem B1302051 : Blo 1301969 1302051 := bstep (se 1 (by rfl) ⟨976538, by rfl⟩ : syracuseStep 1302051 = 1953077) B1953077
theorem B9166385 : Blo 1301969 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B1302067 : Blo 1301969 1302067 := bstep (se 1 (by rfl) ⟨976550, by rfl⟩ : syracuseStep 1302067 = 1953101) B1953101
theorem B1302083 : Blo 1301969 1302083 := bstep (se 1 (by rfl) ⟨976562, by rfl⟩ : syracuseStep 1302083 = 1953125) B1953125
theorem B1302099 : Blo 1301969 1302099 := bstep (se 1 (by rfl) ⟨976574, by rfl⟩ : syracuseStep 1302099 = 1953149) B1953149
theorem B1302115 : Blo 1301969 1302115 := bstep (se 1 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 1302115 = 1953173) B1953173
theorem B12525155 : Blo 1301969 12525155 := bstep (se 1 (by rfl) ⟨9393866, by rfl⟩ : syracuseStep 12525155 = 18787733) B18787733
theorem B1302131 : Blo 1301969 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B2260595 : Blo 1301969 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B1302147 : Blo 1301969 1302147 := bstep (se 1 (by rfl) ⟨976610, by rfl⟩ : syracuseStep 1302147 = 1953221) B1953221
theorem B1465987 : Blo 1301969 1465987 := bstep (se 1 (by rfl) ⟨1099490, by rfl⟩ : syracuseStep 1465987 = 2198981) B2198981
theorem B1302163 : Blo 1301969 1302163 := bstep (se 1 (by rfl) ⟨976622, by rfl⟩ : syracuseStep 1302163 = 1953245) B1953245
theorem B1302179 : Blo 1301969 1302179 := bstep (se 1 (by rfl) ⟨976634, by rfl⟩ : syracuseStep 1302179 = 1953269) B1953269
theorem B2473649 : Blo 1301969 2473649 := bstep (se 2 (by rfl) ⟨927618, by rfl⟩ : syracuseStep 2473649 = 1855237) B1855237
theorem B1302195 : Blo 1301969 1302195 := bstep (se 1 (by rfl) ⟨976646, by rfl⟩ : syracuseStep 1302195 = 1953293) B1953293
theorem B1302211 : Blo 1301969 1302211 := bstep (se 1 (by rfl) ⟨976658, by rfl⟩ : syracuseStep 1302211 = 1953317) B1953317
theorem B20061893 : Blo 1301969 20061893 := bstep (se 4 (by rfl) ⟨1880802, by rfl⟩ : syracuseStep 20061893 = 3761605) B3761605
theorem B2932433 : Blo 1301969 2932433 := bstep (se 2 (by rfl) ⟨1099662, by rfl⟩ : syracuseStep 2932433 = 2199325) B2199325
theorem B1302227 : Blo 1301969 1302227 := bstep (se 1 (by rfl) ⟨976670, by rfl⟩ : syracuseStep 1302227 = 1953341) B1953341
theorem B1302243 : Blo 1301969 1302243 := bstep (se 1 (by rfl) ⟨976682, by rfl⟩ : syracuseStep 1302243 = 1953365) B1953365
theorem B2932451 : Blo 1301969 2932451 := bstep (se 1 (by rfl) ⟨2199338, by rfl⟩ : syracuseStep 2932451 = 4398677) B4398677
theorem B3710701 : Blo 1301969 3710701 := bstep (se 3 (by rfl) ⟨695756, by rfl⟩ : syracuseStep 3710701 = 1391513) B1391513
theorem B1302259 : Blo 1301969 1302259 := bstep (se 1 (by rfl) ⟨976694, by rfl⟩ : syracuseStep 1302259 = 1953389) B1953389
theorem B1302275 : Blo 1301969 1302275 := bstep (se 1 (by rfl) ⟨976706, by rfl⟩ : syracuseStep 1302275 = 1953413) B1953413
theorem B8027909 : Blo 1301969 8027909 := bstep (se 4 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 8027909 = 1505233) B1505233
theorem B1302291 : Blo 1301969 1302291 := bstep (se 1 (by rfl) ⟨976718, by rfl⟩ : syracuseStep 1302291 = 1953437) B1953437
theorem B1466131 : Blo 1301969 1466131 := bstep (se 1 (by rfl) ⟨1099598, by rfl⟩ : syracuseStep 1466131 = 2199197) B2199197
theorem B1302307 : Blo 1301969 1302307 := bstep (se 1 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 1302307 = 1953461) B1953461
theorem B1761059 : Blo 1301969 1761059 := bstep (se 1 (by rfl) ⟨1320794, by rfl⟩ : syracuseStep 1761059 = 2641589) B2641589
theorem B4398893 : Blo 1301969 4398893 := bstep (se 3 (by rfl) ⟨824792, by rfl⟩ : syracuseStep 4398893 = 1649585) B1649585
theorem B3129137 : Blo 1301969 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B1302323 : Blo 1301969 1302323 := bstep (se 1 (by rfl) ⟨976742, by rfl⟩ : syracuseStep 1302323 = 1953485) B1953485
theorem B1302339 : Blo 1301969 1302339 := bstep (se 1 (by rfl) ⟨976754, by rfl⟩ : syracuseStep 1302339 = 1953509) B1953509
theorem B1302355 : Blo 1301969 1302355 := bstep (se 1 (by rfl) ⟨976766, by rfl⟩ : syracuseStep 1302355 = 1953533) B1953533
theorem B1302371 : Blo 1301969 1302371 := bstep (se 1 (by rfl) ⟨976778, by rfl⟩ : syracuseStep 1302371 = 1953557) B1953557
theorem B4398947 : Blo 1301969 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B11894627 : Blo 1301969 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B3964781 : Blo 1301969 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B1302387 : Blo 1301969 1302387 := bstep (se 1 (by rfl) ⟨976790, by rfl⟩ : syracuseStep 1302387 = 1953581) B1953581
theorem B1302403 : Blo 1301969 1302403 := bstep (se 1 (by rfl) ⟨976802, by rfl⟩ : syracuseStep 1302403 = 1953605) B1953605
theorem B1302419 : Blo 1301969 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B1302435 : Blo 1301969 1302435 := bstep (se 1 (by rfl) ⟨976826, by rfl⟩ : syracuseStep 1302435 = 1953653) B1953653
theorem B4947875 : Blo 1301969 4947875 := bstep (se 1 (by rfl) ⟨3710906, by rfl⟩ : syracuseStep 4947875 = 7421813) B7421813
theorem B1466275 : Blo 1301969 1466275 := bstep (se 1 (by rfl) ⟨1099706, by rfl⟩ : syracuseStep 1466275 = 2199413) B2199413
theorem B1302451 : Blo 1301969 1302451 := bstep (se 1 (by rfl) ⟨976838, by rfl⟩ : syracuseStep 1302451 = 1953677) B1953677
theorem B1302467 : Blo 1301969 1302467 := bstep (se 1 (by rfl) ⟨976850, by rfl⟩ : syracuseStep 1302467 = 1953701) B1953701
theorem B3710929 : Blo 1301969 3710929 := bstep (se 2 (by rfl) ⟨1391598, by rfl⟩ : syracuseStep 3710929 = 2783197) B2783197
theorem B1302483 : Blo 1301969 1302483 := bstep (se 1 (by rfl) ⟨976862, by rfl⟩ : syracuseStep 1302483 = 1953725) B1953725
theorem B1302499 : Blo 1301969 1302499 := bstep (se 1 (by rfl) ⟨976874, by rfl⟩ : syracuseStep 1302499 = 1953749) B1953749
theorem B2932721 : Blo 1301969 2932721 := bstep (se 2 (by rfl) ⟨1099770, by rfl⟩ : syracuseStep 2932721 = 2199541) B2199541
theorem B1302515 : Blo 1301969 1302515 := bstep (se 1 (by rfl) ⟨976886, by rfl⟩ : syracuseStep 1302515 = 1953773) B1953773
theorem B1302539 : Blo 1301969 1302539 := bstep (se 1 (by rfl) ⟨976904, by rfl⟩ : syracuseStep 1302539 = 1953809) B1953809
theorem B3129367 : Blo 1301969 3129367 := bstep (se 1 (by rfl) ⟨2347025, by rfl⟩ : syracuseStep 3129367 = 4694051) B4694051
theorem B1302551 : Blo 1301969 1302551 := bstep (se 1 (by rfl) ⟨976913, by rfl⟩ : syracuseStep 1302551 = 1953827) B1953827
theorem B1302571 : Blo 1301969 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B1302583 : Blo 1301969 1302583 := bstep (se 1 (by rfl) ⟨976937, by rfl⟩ : syracuseStep 1302583 = 1953875) B1953875
theorem B1302603 : Blo 1301969 1302603 := bstep (se 1 (by rfl) ⟨976952, by rfl⟩ : syracuseStep 1302603 = 1953905) B1953905
theorem B2474059 : Blo 1301969 2474059 := bstep (se 1 (by rfl) ⟨1855544, by rfl⟩ : syracuseStep 2474059 = 3711089) B3711089
theorem B2932811 : Blo 1301969 2932811 := bstep (se 1 (by rfl) ⟨2199608, by rfl⟩ : syracuseStep 2932811 = 4399217) B4399217
theorem B1302615 : Blo 1301969 1302615 := bstep (se 1 (by rfl) ⟨976961, by rfl⟩ : syracuseStep 1302615 = 1953923) B1953923
theorem B1466455 : Blo 1301969 1466455 := bstep (se 1 (by rfl) ⟨1099841, by rfl⟩ : syracuseStep 1466455 = 2199683) B2199683
theorem B1302635 : Blo 1301969 1302635 := bstep (se 1 (by rfl) ⟨976976, by rfl⟩ : syracuseStep 1302635 = 1953953) B1953953
theorem B1302647 : Blo 1301969 1302647 := bstep (se 1 (by rfl) ⟨976985, by rfl⟩ : syracuseStep 1302647 = 1953971) B1953971
theorem B2932865 : Blo 1301969 2932865 := bstep (se 2 (by rfl) ⟨1099824, by rfl⟩ : syracuseStep 2932865 = 2199649) B2199649
theorem B1302667 : Blo 1301969 1302667 := bstep (se 1 (by rfl) ⟨977000, by rfl⟩ : syracuseStep 1302667 = 1954001) B1954001
theorem B1302679 : Blo 1301969 1302679 := bstep (se 1 (by rfl) ⟨977009, by rfl⟩ : syracuseStep 1302679 = 1954019) B1954019
theorem B2474135 : Blo 1301969 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B1302699 : Blo 1301969 1302699 := bstep (se 1 (by rfl) ⟨977024, by rfl⟩ : syracuseStep 1302699 = 1954049) B1954049
theorem B7422131 : Blo 1301969 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B3965107 : Blo 1301969 3965107 := bstep (se 1 (by rfl) ⟨2973830, by rfl⟩ : syracuseStep 3965107 = 5947661) B5947661
theorem B1302711 : Blo 1301969 1302711 := bstep (se 1 (by rfl) ⟨977033, by rfl⟩ : syracuseStep 1302711 = 1954067) B1954067
theorem B1302731 : Blo 1301969 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B1302743 : Blo 1301969 1302743 := bstep (se 1 (by rfl) ⟨977057, by rfl⟩ : syracuseStep 1302743 = 1954115) B1954115
theorem B4399325 : Blo 1301969 4399325 := bstep (se 3 (by rfl) ⟨824873, by rfl⟩ : syracuseStep 4399325 = 1649747) B1649747
theorem B1302763 : Blo 1301969 1302763 := bstep (se 1 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 1302763 = 1954145) B1954145
theorem B1302775 : Blo 1301969 1302775 := bstep (se 1 (by rfl) ⟨977081, by rfl⟩ : syracuseStep 1302775 = 1954163) B1954163
theorem B1302795 : Blo 1301969 1302795 := bstep (se 1 (by rfl) ⟨977096, by rfl⟩ : syracuseStep 1302795 = 1954193) B1954193
theorem B1466635 : Blo 1301969 1466635 := bstep (se 1 (by rfl) ⟨1099976, by rfl⟩ : syracuseStep 1466635 = 2199953) B2199953
theorem B1302807 : Blo 1301969 1302807 := bstep (se 1 (by rfl) ⟨977105, by rfl⟩ : syracuseStep 1302807 = 1954211) B1954211
theorem B1302827 : Blo 1301969 1302827 := bstep (se 1 (by rfl) ⟨977120, by rfl⟩ : syracuseStep 1302827 = 1954241) B1954241
theorem B1302839 : Blo 1301969 1302839 := bstep (se 1 (by rfl) ⟨977129, by rfl⟩ : syracuseStep 1302839 = 1954259) B1954259
theorem B1302859 : Blo 1301969 1302859 := bstep (se 1 (by rfl) ⟨977144, by rfl⟩ : syracuseStep 1302859 = 1954289) B1954289
theorem B1302871 : Blo 1301969 1302871 := bstep (se 1 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 1302871 = 1954307) B1954307
theorem B2933081 : Blo 1301969 2933081 := bstep (se 2 (by rfl) ⟨1099905, by rfl⟩ : syracuseStep 2933081 = 2199811) B2199811
theorem B1302891 : Blo 1301969 1302891 := bstep (se 1 (by rfl) ⟨977168, by rfl⟩ : syracuseStep 1302891 = 1954337) B1954337
theorem B1302903 : Blo 1301969 1302903 := bstep (se 1 (by rfl) ⟨977177, by rfl⟩ : syracuseStep 1302903 = 1954355) B1954355
theorem B1466743 : Blo 1301969 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B1302923 : Blo 1301969 1302923 := bstep (se 1 (by rfl) ⟨977192, by rfl⟩ : syracuseStep 1302923 = 1954385) B1954385
theorem B1302935 : Blo 1301969 1302935 := bstep (se 1 (by rfl) ⟨977201, by rfl⟩ : syracuseStep 1302935 = 1954403) B1954403
theorem B1302955 : Blo 1301969 1302955 := bstep (se 1 (by rfl) ⟨977216, by rfl⟩ : syracuseStep 1302955 = 1954433) B1954433
theorem B17826227 : Blo 1301969 17826227 := bstep (se 1 (by rfl) ⟨13369670, by rfl⟩ : syracuseStep 17826227 = 26739341) B26739341
theorem B2933171 : Blo 1301969 2933171 := bstep (se 1 (by rfl) ⟨2199878, by rfl⟩ : syracuseStep 2933171 = 4399757) B4399757
theorem B1302967 : Blo 1301969 1302967 := bstep (se 1 (by rfl) ⟨977225, by rfl⟩ : syracuseStep 1302967 = 1954451) B1954451
theorem B1302987 : Blo 1301969 1302987 := bstep (se 1 (by rfl) ⟨977240, by rfl⟩ : syracuseStep 1302987 = 1954481) B1954481
theorem B1302999 : Blo 1301969 1302999 := bstep (se 1 (by rfl) ⟨977249, by rfl⟩ : syracuseStep 1302999 = 1954499) B1954499
theorem B2933207 : Blo 1301969 2933207 := bstep (se 1 (by rfl) ⟨2199905, by rfl⟩ : syracuseStep 2933207 = 4399811) B4399811
theorem B1303019 : Blo 1301969 1303019 := bstep (se 1 (by rfl) ⟨977264, by rfl⟩ : syracuseStep 1303019 = 1954529) B1954529
theorem B1303031 : Blo 1301969 1303031 := bstep (se 1 (by rfl) ⟨977273, by rfl⟩ : syracuseStep 1303031 = 1954547) B1954547
theorem B1303051 : Blo 1301969 1303051 := bstep (se 1 (by rfl) ⟨977288, by rfl⟩ : syracuseStep 1303051 = 1954577) B1954577
theorem B1303063 : Blo 1301969 1303063 := bstep (se 1 (by rfl) ⟨977297, by rfl⟩ : syracuseStep 1303063 = 1954595) B1954595
theorem B1303083 : Blo 1301969 1303083 := bstep (se 1 (by rfl) ⟨977312, by rfl⟩ : syracuseStep 1303083 = 1954625) B1954625
theorem B1466923 : Blo 1301969 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B1303095 : Blo 1301969 1303095 := bstep (se 1 (by rfl) ⟨977321, by rfl⟩ : syracuseStep 1303095 = 1954643) B1954643
theorem B6685249 : Blo 1301969 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B1303115 : Blo 1301969 1303115 := bstep (se 1 (by rfl) ⟨977336, by rfl⟩ : syracuseStep 1303115 = 1954673) B1954673
theorem B1303127 : Blo 1301969 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B4948573 : Blo 1301969 4948573 := bstep (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) B1855715
theorem B1303147 : Blo 1301969 1303147 := bstep (se 1 (by rfl) ⟨977360, by rfl⟩ : syracuseStep 1303147 = 1954721) B1954721
theorem B1303159 : Blo 1301969 1303159 := bstep (se 1 (by rfl) ⟨977369, by rfl⟩ : syracuseStep 1303159 = 1954739) B1954739
theorem B6259331 : Blo 1301969 6259331 := bstep (se 1 (by rfl) ⟨4694498, by rfl⟩ : syracuseStep 6259331 = 9388997) B9388997
theorem B1303179 : Blo 1301969 1303179 := bstep (se 1 (by rfl) ⟨977384, by rfl⟩ : syracuseStep 1303179 = 1954769) B1954769
theorem B2933387 : Blo 1301969 2933387 := bstep (se 1 (by rfl) ⟨2200040, by rfl⟩ : syracuseStep 2933387 = 4400081) B4400081
theorem B1303191 : Blo 1301969 1303191 := bstep (se 1 (by rfl) ⟨977393, by rfl⟩ : syracuseStep 1303191 = 1954787) B1954787
theorem B1303211 : Blo 1301969 1303211 := bstep (se 1 (by rfl) ⟨977408, by rfl⟩ : syracuseStep 1303211 = 1954817) B1954817
theorem B1303223 : Blo 1301969 1303223 := bstep (se 1 (by rfl) ⟨977417, by rfl⟩ : syracuseStep 1303223 = 1954835) B1954835
theorem B2933441 : Blo 1301969 2933441 := bstep (se 2 (by rfl) ⟨1100040, by rfl⟩ : syracuseStep 2933441 = 2200081) B2200081
theorem B1303243 : Blo 1301969 1303243 := bstep (se 1 (by rfl) ⟨977432, by rfl⟩ : syracuseStep 1303243 = 1954865) B1954865
theorem B1303255 : Blo 1301969 1303255 := bstep (se 1 (by rfl) ⟨977441, by rfl⟩ : syracuseStep 1303255 = 1954883) B1954883
theorem B1303275 : Blo 1301969 1303275 := bstep (se 1 (by rfl) ⟨977456, by rfl⟩ : syracuseStep 1303275 = 1954913) B1954913
theorem B40682225 : Blo 1301969 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B1303287 : Blo 1301969 1303287 := bstep (se 1 (by rfl) ⟨977465, by rfl⟩ : syracuseStep 1303287 = 1954931) B1954931
theorem B1303307 : Blo 1301969 1303307 := bstep (se 1 (by rfl) ⟨977480, by rfl⟩ : syracuseStep 1303307 = 1954961) B1954961
theorem B1671959 : Blo 1301969 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B1303319 : Blo 1301969 1303319 := bstep (se 1 (by rfl) ⟨977489, by rfl⟩ : syracuseStep 1303319 = 1954979) B1954979
theorem B1303339 : Blo 1301969 1303339 := bstep (se 1 (by rfl) ⟨977504, by rfl⟩ : syracuseStep 1303339 = 1955009) B1955009
theorem B5563181 : Blo 1301969 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B2474803 : Blo 1301969 2474803 := bstep (se 1 (by rfl) ⟨1856102, by rfl⟩ : syracuseStep 2474803 = 3712205) B3712205
theorem B1303351 : Blo 1301969 1303351 := bstep (se 1 (by rfl) ⟨977513, by rfl⟩ : syracuseStep 1303351 = 1955027) B1955027
theorem B1303371 : Blo 1301969 1303371 := bstep (se 1 (by rfl) ⟨977528, by rfl⟩ : syracuseStep 1303371 = 1955057) B1955057
theorem B1303383 : Blo 1301969 1303383 := bstep (se 1 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 1303383 = 1955075) B1955075
theorem B1303403 : Blo 1301969 1303403 := bstep (se 1 (by rfl) ⟨977552, by rfl⟩ : syracuseStep 1303403 = 1955105) B1955105
theorem B1303415 : Blo 1301969 1303415 := bstep (se 1 (by rfl) ⟨977561, by rfl⟩ : syracuseStep 1303415 = 1955123) B1955123
theorem B1303435 : Blo 1301969 1303435 := bstep (se 1 (by rfl) ⟨977576, by rfl⟩ : syracuseStep 1303435 = 1955153) B1955153
theorem B1303447 : Blo 1301969 1303447 := bstep (se 1 (by rfl) ⟨977585, by rfl⟩ : syracuseStep 1303447 = 1955171) B1955171
theorem B2933657 : Blo 1301969 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1303467 : Blo 1301969 1303467 := bstep (se 1 (by rfl) ⟨977600, by rfl⟩ : syracuseStep 1303467 = 1955201) B1955201
theorem B1303479 : Blo 1301969 1303479 := bstep (se 1 (by rfl) ⟨977609, by rfl⟩ : syracuseStep 1303479 = 1955219) B1955219
theorem B1303499 : Blo 1301969 1303499 := bstep (se 1 (by rfl) ⟨977624, by rfl⟩ : syracuseStep 1303499 = 1955249) B1955249
theorem B1303511 : Blo 1301969 1303511 := bstep (se 1 (by rfl) ⟨977633, by rfl⟩ : syracuseStep 1303511 = 1955267) B1955267
theorem B1303531 : Blo 1301969 1303531 := bstep (se 1 (by rfl) ⟨977648, by rfl⟩ : syracuseStep 1303531 = 1955297) B1955297
theorem B2933747 : Blo 1301969 2933747 := bstep (se 1 (by rfl) ⟨2200310, by rfl⟩ : syracuseStep 2933747 = 4400621) B4400621
theorem B1303543 : Blo 1301969 1303543 := bstep (se 1 (by rfl) ⟨977657, by rfl⟩ : syracuseStep 1303543 = 1955315) B1955315
theorem B1303563 : Blo 1301969 1303563 := bstep (se 1 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 1303563 = 1955345) B1955345
theorem B1303575 : Blo 1301969 1303575 := bstep (se 1 (by rfl) ⟨977681, by rfl⟩ : syracuseStep 1303575 = 1955363) B1955363
theorem B2475031 : Blo 1301969 2475031 := bstep (se 1 (by rfl) ⟨1856273, by rfl⟩ : syracuseStep 2475031 = 3712547) B3712547
theorem B2933783 : Blo 1301969 2933783 := bstep (se 1 (by rfl) ⟨2200337, by rfl⟩ : syracuseStep 2933783 = 4400675) B4400675
theorem B1303595 : Blo 1301969 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B1303607 : Blo 1301969 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B1303627 : Blo 1301969 1303627 := bstep (se 1 (by rfl) ⟨977720, by rfl⟩ : syracuseStep 1303627 = 1955441) B1955441
theorem B1303639 : Blo 1301969 1303639 := bstep (se 1 (by rfl) ⟨977729, by rfl⟩ : syracuseStep 1303639 = 1955459) B1955459
theorem B1303659 : Blo 1301969 1303659 := bstep (se 1 (by rfl) ⟨977744, by rfl⟩ : syracuseStep 1303659 = 1955489) B1955489
theorem B1303671 : Blo 1301969 1303671 := bstep (se 1 (by rfl) ⟨977753, by rfl⟩ : syracuseStep 1303671 = 1955507) B1955507
theorem B2475137 : Blo 1301969 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B1303691 : Blo 1301969 1303691 := bstep (se 1 (by rfl) ⟨977768, by rfl⟩ : syracuseStep 1303691 = 1955537) B1955537
theorem B1303703 : Blo 1301969 1303703 := bstep (se 1 (by rfl) ⟨977777, by rfl⟩ : syracuseStep 1303703 = 1955555) B1955555
theorem B1303723 : Blo 1301969 1303723 := bstep (se 1 (by rfl) ⟨977792, by rfl⟩ : syracuseStep 1303723 = 1955585) B1955585
theorem B3523763 : Blo 1301969 3523763 := bstep (se 1 (by rfl) ⟨2642822, by rfl⟩ : syracuseStep 3523763 = 5285645) B5285645
theorem B1303735 : Blo 1301969 1303735 := bstep (se 1 (by rfl) ⟨977801, by rfl⟩ : syracuseStep 1303735 = 1955603) B1955603
theorem B1303755 : Blo 1301969 1303755 := bstep (se 1 (by rfl) ⟨977816, by rfl⟩ : syracuseStep 1303755 = 1955633) B1955633
theorem B1303767 : Blo 1301969 1303767 := bstep (se 1 (by rfl) ⟨977825, by rfl⟩ : syracuseStep 1303767 = 1955651) B1955651
theorem B1303787 : Blo 1301969 1303787 := bstep (se 1 (by rfl) ⟨977840, by rfl⟩ : syracuseStep 1303787 = 1955681) B1955681
theorem B1303799 : Blo 1301969 1303799 := bstep (se 1 (by rfl) ⟨977849, by rfl⟩ : syracuseStep 1303799 = 1955699) B1955699
theorem B1303819 : Blo 1301969 1303819 := bstep (se 1 (by rfl) ⟨977864, by rfl⟩ : syracuseStep 1303819 = 1955729) B1955729
theorem B1303831 : Blo 1301969 1303831 := bstep (se 1 (by rfl) ⟨977873, by rfl⟩ : syracuseStep 1303831 = 1955747) B1955747
theorem B2475289 : Blo 1301969 2475289 := bstep (se 2 (by rfl) ⟨928233, by rfl⟩ : syracuseStep 2475289 = 1856467) B1856467
theorem B1303851 : Blo 1301969 1303851 := bstep (se 1 (by rfl) ⟨977888, by rfl⟩ : syracuseStep 1303851 = 1955777) B1955777
theorem B1303863 : Blo 1301969 1303863 := bstep (se 1 (by rfl) ⟨977897, by rfl⟩ : syracuseStep 1303863 = 1955795) B1955795
theorem B3712331 : Blo 1301969 3712331 := bstep (se 1 (by rfl) ⟨2784248, by rfl⟩ : syracuseStep 3712331 = 5568497) B5568497
theorem B4400459 : Blo 1301969 4400459 := bstep (se 1 (by rfl) ⟨3300344, by rfl⟩ : syracuseStep 4400459 = 6600689) B6600689
theorem B1303883 : Blo 1301969 1303883 := bstep (se 1 (by rfl) ⟨977912, by rfl⟩ : syracuseStep 1303883 = 1955825) B1955825
theorem B1303895 : Blo 1301969 1303895 := bstep (se 1 (by rfl) ⟨977921, by rfl⟩ : syracuseStep 1303895 = 1955843) B1955843
theorem B1303915 : Blo 1301969 1303915 := bstep (se 1 (by rfl) ⟨977936, by rfl⟩ : syracuseStep 1303915 = 1955873) B1955873
theorem B1303927 : Blo 1301969 1303927 := bstep (se 1 (by rfl) ⟨977945, by rfl⟩ : syracuseStep 1303927 = 1955891) B1955891
theorem B1303947 : Blo 1301969 1303947 := bstep (se 1 (by rfl) ⟨977960, by rfl⟩ : syracuseStep 1303947 = 1955921) B1955921
theorem B6595991 : Blo 1301969 6595991 := bstep (se 1 (by rfl) ⟨4946993, by rfl⟩ : syracuseStep 6595991 = 9893987) B9893987
theorem B1303959 : Blo 1301969 1303959 := bstep (se 1 (by rfl) ⟨977969, by rfl⟩ : syracuseStep 1303959 = 1955939) B1955939
theorem B2508185 : Blo 1301969 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B5563865 : Blo 1301969 5563865 := bstep (se 2 (by rfl) ⟨2086449, by rfl⟩ : syracuseStep 5563865 = 4172899) B4172899
theorem B4400729 : Blo 1301969 4400729 := bstep (se 2 (by rfl) ⟨1650273, by rfl⟩ : syracuseStep 4400729 = 3300547) B3300547
theorem B16696925 : Blo 1301969 16696925 := bstep (se 3 (by rfl) ⟨3130673, by rfl⟩ : syracuseStep 16696925 = 6261347) B6261347
theorem B7423589 : Blo 1301969 7423589 := bstep (se 4 (by rfl) ⟨695961, by rfl⟩ : syracuseStep 7423589 = 1391923) B1391923
theorem B1648279 : Blo 1301969 1648279 := bstep (se 1 (by rfl) ⟨1236209, by rfl⟩ : syracuseStep 1648279 = 2472419) B2472419
theorem B2197145 : Blo 1301969 2197145 := bstep (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) B1647859
theorem B3712729 : Blo 1301969 3712729 := bstep (se 2 (by rfl) ⟨1392273, by rfl⟩ : syracuseStep 3712729 = 2784547) B2784547
theorem B2197273 : Blo 1301969 2197273 := bstep (se 2 (by rfl) ⟨823977, by rfl⟩ : syracuseStep 2197273 = 1647955) B1647955
theorem B4949849 : Blo 1301969 4949849 := bstep (se 2 (by rfl) ⟨1856193, by rfl⟩ : syracuseStep 4949849 = 3712387) B3712387
theorem B13371313 : Blo 1301969 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B7424045 : Blo 1301969 7424045 := bstep (se 3 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 7424045 = 2784017) B2784017
theorem B14084189 : Blo 1301969 14084189 := bstep (se 3 (by rfl) ⟨2640785, by rfl⟩ : syracuseStep 14084189 = 5281571) B5281571
theorem B4696157 : Blo 1301969 4696157 := bstep (se 3 (by rfl) ⟨880529, by rfl⟩ : syracuseStep 4696157 = 1761059) B1761059
theorem B8349875 : Blo 1301969 8349875 := bstep (se 1 (by rfl) ⟨6262406, by rfl⟩ : syracuseStep 8349875 = 12524813) B12524813
theorem B3811549 : Blo 1301969 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B2197847 : Blo 1301969 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B8350103 : Blo 1301969 8350103 := bstep (se 1 (by rfl) ⟨6262577, by rfl⟩ : syracuseStep 8350103 = 12525155) B12525155
theorem B3295667 : Blo 1301969 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B1649099 : Blo 1301969 1649099 := bstep (se 1 (by rfl) ⟨1236824, by rfl⟩ : syracuseStep 1649099 = 2473649) B2473649
theorem B2197975 : Blo 1301969 2197975 := bstep (se 1 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 2197975 = 3296963) B3296963
theorem B11274713 : Blo 1301969 11274713 := bstep (se 2 (by rfl) ⟨4228017, by rfl⟩ : syracuseStep 11274713 = 8456035) B8456035
theorem B5351939 : Blo 1301969 5351939 := bstep (se 1 (by rfl) ⟨4013954, by rfl⟩ : syracuseStep 5351939 = 8027909) B8027909
theorem B8915521 : Blo 1301969 8915521 := bstep (se 2 (by rfl) ⟨3343320, by rfl⟩ : syracuseStep 8915521 = 6686641) B6686641
theorem B10029719 : Blo 1301969 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B5565131 : Blo 1301969 5565131 := bstep (se 1 (by rfl) ⟨4173848, by rfl⟩ : syracuseStep 5565131 = 8347697) B8347697
theorem B3295961 : Blo 1301969 3295961 := bstep (se 2 (by rfl) ⟨1235985, by rfl⟩ : syracuseStep 3295961 = 2471971) B2471971
theorem B7424729 : Blo 1301969 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B2378521 : Blo 1301969 2378521 := bstep (se 2 (by rfl) ⟨891945, by rfl⟩ : syracuseStep 2378521 = 1783891) B1783891
theorem B7416755 : Blo 1301969 7416755 := bstep (se 1 (by rfl) ⟨5562566, by rfl⟩ : syracuseStep 7416755 = 11125133) B11125133
theorem B33852377 : Blo 1301969 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B5565505 : Blo 1301969 5565505 := bstep (se 2 (by rfl) ⟨2087064, by rfl⟩ : syracuseStep 5565505 = 4174129) B4174129
theorem B4697153 : Blo 1301969 4697153 := bstep (se 2 (by rfl) ⟨1761432, by rfl⟩ : syracuseStep 4697153 = 3522865) B3522865
theorem B32107589 : Blo 1301969 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B2198603 : Blo 1301969 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B8342621 : Blo 1301969 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B1649803 : Blo 1301969 1649803 := bstep (se 1 (by rfl) ⟨1237352, by rfl⟩ : syracuseStep 1649803 = 2474705) B2474705
theorem B4172951 : Blo 1301969 4172951 := bstep (se 1 (by rfl) ⟨3129713, by rfl⟩ : syracuseStep 4172951 = 6259427) B6259427
theorem B1854667 : Blo 1301969 1854667 := bstep (se 1 (by rfl) ⟨1391000, by rfl⟩ : syracuseStep 1854667 = 2782001) B2782001
theorem B2198731 : Blo 1301969 2198731 := bstep (se 1 (by rfl) ⟨1649048, by rfl⟩ : syracuseStep 2198731 = 3298097) B3298097
theorem B1854679 : Blo 1301969 1854679 := bstep (se 1 (by rfl) ⟨1391009, by rfl⟩ : syracuseStep 1854679 = 2782019) B2782019
theorem B1953035 : Blo 1301969 1953035 := bstep (se 1 (by rfl) ⟨1464776, by rfl⟩ : syracuseStep 1953035 = 2929553) B2929553
theorem B1953047 : Blo 1301969 1953047 := bstep (se 1 (by rfl) ⟨1464785, by rfl⟩ : syracuseStep 1953047 = 2929571) B2929571
theorem B2641175 : Blo 1301969 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B1953113 : Blo 1301969 1953113 := bstep (se 2 (by rfl) ⟨732417, by rfl⟩ : syracuseStep 1953113 = 1464835) B1464835
theorem B4345177 : Blo 1301969 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B2198873 : Blo 1301969 2198873 := bstep (se 2 (by rfl) ⟨824577, by rfl⟩ : syracuseStep 2198873 = 1649155) B1649155
theorem B5565847 : Blo 1301969 5565847 := bstep (se 1 (by rfl) ⟨4174385, by rfl⟩ : syracuseStep 5565847 = 8348771) B8348771
theorem B1650071 : Blo 1301969 1650071 := bstep (se 1 (by rfl) ⟨1237553, by rfl⟩ : syracuseStep 1650071 = 2475107) B2475107
theorem B1953227 : Blo 1301969 1953227 := bstep (se 1 (by rfl) ⟨1464920, by rfl⟩ : syracuseStep 1953227 = 2929841) B2929841
theorem B1953239 : Blo 1301969 1953239 := bstep (se 1 (by rfl) ⟨1464929, by rfl⟩ : syracuseStep 1953239 = 2929859) B2929859
theorem B2199001 : Blo 1301969 2199001 := bstep (se 2 (by rfl) ⟨824625, by rfl⟩ : syracuseStep 2199001 = 1649251) B1649251
theorem B4394519 : Blo 1301969 4394519 := bstep (se 1 (by rfl) ⟨3295889, by rfl⟩ : syracuseStep 4394519 = 6591779) B6591779
theorem B1953305 : Blo 1301969 1953305 := bstep (se 2 (by rfl) ⟨732489, by rfl⟩ : syracuseStep 1953305 = 1464979) B1464979
theorem B8351333 : Blo 1301969 8351333 := bstep (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) B1565875
theorem B1953419 : Blo 1301969 1953419 := bstep (se 1 (by rfl) ⟨1465064, by rfl⟩ : syracuseStep 1953419 = 2930129) B2930129
theorem B1953431 : Blo 1301969 1953431 := bstep (se 1 (by rfl) ⟨1465073, by rfl⟩ : syracuseStep 1953431 = 2930147) B2930147
theorem B4173515 : Blo 1301969 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B1953497 : Blo 1301969 1953497 := bstep (se 2 (by rfl) ⟨732561, by rfl⟩ : syracuseStep 1953497 = 1465123) B1465123
theorem B2780993 : Blo 1301969 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B1953611 : Blo 1301969 1953611 := bstep (se 1 (by rfl) ⟨1465208, by rfl⟩ : syracuseStep 1953611 = 2930417) B2930417
theorem B1953623 : Blo 1301969 1953623 := bstep (se 1 (by rfl) ⟨1465217, by rfl⟩ : syracuseStep 1953623 = 2930435) B2930435
theorem B1953689 : Blo 1301969 1953689 := bstep (se 2 (by rfl) ⟨732633, by rfl⟩ : syracuseStep 1953689 = 1465267) B1465267
theorem B1953803 : Blo 1301969 1953803 := bstep (se 1 (by rfl) ⟨1465352, by rfl⟩ : syracuseStep 1953803 = 2930705) B2930705
theorem B1953815 : Blo 1301969 1953815 := bstep (se 1 (by rfl) ⟨1465361, by rfl⟩ : syracuseStep 1953815 = 2930723) B2930723
theorem B2199575 : Blo 1301969 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B4395059 : Blo 1301969 4395059 := bstep (se 1 (by rfl) ⟨3296294, by rfl⟩ : syracuseStep 4395059 = 6592589) B6592589
theorem B4460609 : Blo 1301969 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B1953881 : Blo 1301969 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B4944017 : Blo 1301969 4944017 := bstep (se 2 (by rfl) ⟨1854006, by rfl⟩ : syracuseStep 4944017 = 3708013) B3708013
theorem B2199703 : Blo 1301969 2199703 := bstep (se 1 (by rfl) ⟨1649777, by rfl⟩ : syracuseStep 2199703 = 3299555) B3299555
theorem B1953995 : Blo 1301969 1953995 := bstep (se 1 (by rfl) ⟨1465496, by rfl⟩ : syracuseStep 1953995 = 2930993) B2930993
theorem B2642123 : Blo 1301969 2642123 := bstep (se 1 (by rfl) ⟨1981592, by rfl⟩ : syracuseStep 2642123 = 3963185) B3963185
theorem B1954007 : Blo 1301969 1954007 := bstep (se 1 (by rfl) ⟨1465505, by rfl⟩ : syracuseStep 1954007 = 2931011) B2931011
theorem B11137297 : Blo 1301969 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B9900305 : Blo 1301969 9900305 := bstep (se 2 (by rfl) ⟨3712614, by rfl⟩ : syracuseStep 9900305 = 7425229) B7425229
theorem B1954073 : Blo 1301969 1954073 := bstep (se 2 (by rfl) ⟨732777, by rfl⟩ : syracuseStep 1954073 = 1465555) B1465555
theorem B4395329 : Blo 1301969 4395329 := bstep (se 2 (by rfl) ⟨1648248, by rfl⟩ : syracuseStep 4395329 = 3296497) B3296497
theorem B2781515 : Blo 1301969 2781515 := bstep (se 1 (by rfl) ⟨2086136, by rfl⟩ : syracuseStep 2781515 = 4172273) B4172273
theorem B3297611 : Blo 1301969 3297611 := bstep (se 1 (by rfl) ⟨2473208, by rfl⟩ : syracuseStep 3297611 = 4946417) B4946417
theorem B7418213 : Blo 1301969 7418213 := bstep (se 4 (by rfl) ⟨695457, by rfl⟩ : syracuseStep 7418213 = 1390915) B1390915
theorem B1954187 : Blo 1301969 1954187 := bstep (se 1 (by rfl) ⟨1465640, by rfl⟩ : syracuseStep 1954187 = 2931281) B2931281
theorem B1954199 : Blo 1301969 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B2347481 : Blo 1301969 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B1954265 : Blo 1301969 1954265 := bstep (se 2 (by rfl) ⟨732849, by rfl⟩ : syracuseStep 1954265 = 1465699) B1465699
theorem B11137571 : Blo 1301969 11137571 := bstep (se 1 (by rfl) ⟨8353178, by rfl⟩ : syracuseStep 11137571 = 16706357) B16706357
theorem B1954379 : Blo 1301969 1954379 := bstep (se 1 (by rfl) ⟨1465784, by rfl⟩ : syracuseStep 1954379 = 2931569) B2931569
theorem B1954391 : Blo 1301969 1954391 := bstep (se 1 (by rfl) ⟨1465793, by rfl⟩ : syracuseStep 1954391 = 2931587) B2931587
theorem B4944473 : Blo 1301969 4944473 := bstep (se 2 (by rfl) ⟨1854177, by rfl⟩ : syracuseStep 4944473 = 3708355) B3708355
theorem B2085527 : Blo 1301969 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B1954457 : Blo 1301969 1954457 := bstep (se 2 (by rfl) ⟨732921, by rfl⟩ : syracuseStep 1954457 = 1465843) B1465843
theorem B9892529 : Blo 1301969 9892529 := bstep (se 2 (by rfl) ⟨3709698, by rfl⟩ : syracuseStep 9892529 = 7419397) B7419397
theorem B1954571 : Blo 1301969 1954571 := bstep (se 1 (by rfl) ⟨1465928, by rfl⟩ : syracuseStep 1954571 = 2931857) B2931857
theorem B2200331 : Blo 1301969 2200331 := bstep (se 1 (by rfl) ⟨1650248, by rfl⟩ : syracuseStep 2200331 = 3300497) B3300497
theorem B1954583 : Blo 1301969 1954583 := bstep (se 1 (by rfl) ⟨1465937, by rfl⟩ : syracuseStep 1954583 = 2931875) B2931875
theorem B4944685 : Blo 1301969 4944685 := bstep (se 3 (by rfl) ⟨927128, by rfl⟩ : syracuseStep 4944685 = 1854257) B1854257
theorem B1954649 : Blo 1301969 1954649 := bstep (se 2 (by rfl) ⟨732993, by rfl⟩ : syracuseStep 1954649 = 1465987) B1465987
theorem B4395869 : Blo 1301969 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B6599555 : Blo 1301969 6599555 := bstep (se 1 (by rfl) ⟨4949666, by rfl⟩ : syracuseStep 6599555 = 9899333) B9899333
theorem B21418931 : Blo 1301969 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B1954763 : Blo 1301969 1954763 := bstep (se 1 (by rfl) ⟨1466072, by rfl⟩ : syracuseStep 1954763 = 2932145) B2932145
theorem B1954775 : Blo 1301969 1954775 := bstep (se 1 (by rfl) ⟨1466081, by rfl⟩ : syracuseStep 1954775 = 2932163) B2932163
theorem B2929625 : Blo 1301969 2929625 := bstep (se 2 (by rfl) ⟨1098609, by rfl⟩ : syracuseStep 2929625 = 2197219) B2197219
theorem B7418897 : Blo 1301969 7418897 := bstep (se 2 (by rfl) ⟨2782086, by rfl⟩ : syracuseStep 7418897 = 5564173) B5564173
theorem B1954841 : Blo 1301969 1954841 := bstep (se 2 (by rfl) ⟨733065, by rfl⟩ : syracuseStep 1954841 = 1466131) B1466131
theorem B2929715 : Blo 1301969 2929715 := bstep (se 1 (by rfl) ⟨2197286, by rfl⟩ : syracuseStep 2929715 = 4394573) B4394573
theorem B2929751 : Blo 1301969 2929751 := bstep (se 1 (by rfl) ⟨2197313, by rfl⟩ : syracuseStep 2929751 = 4394627) B4394627
theorem B4944989 : Blo 1301969 4944989 := bstep (se 3 (by rfl) ⟨927185, by rfl⟩ : syracuseStep 4944989 = 1854371) B1854371
theorem B13374595 : Blo 1301969 13374595 := bstep (se 1 (by rfl) ⟨10030946, by rfl⟩ : syracuseStep 13374595 = 20061893) B20061893
theorem B1954955 : Blo 1301969 1954955 := bstep (se 1 (by rfl) ⟨1466216, by rfl⟩ : syracuseStep 1954955 = 2932433) B2932433
theorem B9893015 : Blo 1301969 9893015 := bstep (se 1 (by rfl) ⟨7419761, by rfl⟩ : syracuseStep 9893015 = 14839523) B14839523
theorem B1954967 : Blo 1301969 1954967 := bstep (se 1 (by rfl) ⟨1466225, by rfl⟩ : syracuseStep 1954967 = 2932451) B2932451
theorem B2086091 : Blo 1301969 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B1955033 : Blo 1301969 1955033 := bstep (se 2 (by rfl) ⟨733137, by rfl⟩ : syracuseStep 1955033 = 1466275) B1466275
theorem B2643187 : Blo 1301969 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B2929931 : Blo 1301969 2929931 := bstep (se 1 (by rfl) ⟨2197448, by rfl⟩ : syracuseStep 2929931 = 4394897) B4394897
theorem B3298583 : Blo 1301969 3298583 := bstep (se 1 (by rfl) ⟨2473937, by rfl⟩ : syracuseStep 3298583 = 4947875) B4947875
theorem B2929985 : Blo 1301969 2929985 := bstep (se 2 (by rfl) ⟨1098744, by rfl⟩ : syracuseStep 2929985 = 2197489) B2197489
theorem B1955147 : Blo 1301969 1955147 := bstep (se 1 (by rfl) ⟨1466360, by rfl⟩ : syracuseStep 1955147 = 2932721) B2932721
theorem B1955159 : Blo 1301969 1955159 := bstep (se 1 (by rfl) ⟨1466369, by rfl⟩ : syracuseStep 1955159 = 2932739) B2932739
theorem B1955225 : Blo 1301969 1955225 := bstep (se 2 (by rfl) ⟨733209, by rfl⟩ : syracuseStep 1955225 = 1466419) B1466419
theorem B1955339 : Blo 1301969 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B1955351 : Blo 1301969 1955351 := bstep (se 1 (by rfl) ⟨1466513, by rfl⟩ : syracuseStep 1955351 = 2933027) B2933027
theorem B2930201 : Blo 1301969 2930201 := bstep (se 2 (by rfl) ⟨1098825, by rfl⟩ : syracuseStep 2930201 = 2197651) B2197651
theorem B2782745 : Blo 1301969 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B2348633 : Blo 1301969 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B1955417 : Blo 1301969 1955417 := bstep (se 2 (by rfl) ⟨733281, by rfl⟩ : syracuseStep 1955417 = 1466563) B1466563
theorem B2930291 : Blo 1301969 2930291 := bstep (se 1 (by rfl) ⟨2197718, by rfl⟩ : syracuseStep 2930291 = 4395437) B4395437
theorem B1980055 : Blo 1301969 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B2930327 : Blo 1301969 2930327 := bstep (se 1 (by rfl) ⟨2197745, by rfl⟩ : syracuseStep 2930327 = 4395491) B4395491
theorem B2086603 : Blo 1301969 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1955531 : Blo 1301969 1955531 := bstep (se 1 (by rfl) ⟨1466648, by rfl⟩ : syracuseStep 1955531 = 2933297) B2933297
theorem B1955543 : Blo 1301969 1955543 := bstep (se 1 (by rfl) ⟨1466657, by rfl⟩ : syracuseStep 1955543 = 2933315) B2933315
theorem B1955609 : Blo 1301969 1955609 := bstep (se 2 (by rfl) ⟨733353, by rfl⟩ : syracuseStep 1955609 = 1466707) B1466707
theorem B2930507 : Blo 1301969 2930507 := bstep (se 1 (by rfl) ⟨2197880, by rfl⟩ : syracuseStep 2930507 = 4395761) B4395761
theorem B2930561 : Blo 1301969 2930561 := bstep (se 2 (by rfl) ⟨1098960, by rfl⟩ : syracuseStep 2930561 = 2197921) B2197921
theorem B1955723 : Blo 1301969 1955723 := bstep (se 1 (by rfl) ⟨1466792, by rfl⟩ : syracuseStep 1955723 = 2933585) B2933585
theorem B1955735 : Blo 1301969 1955735 := bstep (se 1 (by rfl) ⟨1466801, by rfl⟩ : syracuseStep 1955735 = 2933603) B2933603
theorem B2783155 : Blo 1301969 2783155 := bstep (se 1 (by rfl) ⟨2087366, by rfl⟩ : syracuseStep 2783155 = 4174733) B4174733
theorem B3299251 : Blo 1301969 3299251 := bstep (se 1 (by rfl) ⟨2474438, by rfl⟩ : syracuseStep 3299251 = 4948877) B4948877
theorem B4397003 : Blo 1301969 4397003 := bstep (se 1 (by rfl) ⟨3297752, by rfl⟩ : syracuseStep 4397003 = 6595505) B6595505
theorem B1955801 : Blo 1301969 1955801 := bstep (se 2 (by rfl) ⟨733425, by rfl⟩ : syracuseStep 1955801 = 1466851) B1466851
theorem B5085149 : Blo 1301969 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B2349043 : Blo 1301969 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B7919633 : Blo 1301969 7919633 := bstep (se 2 (by rfl) ⟨2969862, by rfl⟩ : syracuseStep 7919633 = 5939725) B5939725
theorem B3299393 : Blo 1301969 3299393 := bstep (se 2 (by rfl) ⟨1237272, by rfl⟩ : syracuseStep 3299393 = 2474545) B2474545
theorem B6682699 : Blo 1301969 6682699 := bstep (se 1 (by rfl) ⟨5012024, by rfl⟩ : syracuseStep 6682699 = 10024049) B10024049
theorem B1955915 : Blo 1301969 1955915 := bstep (se 1 (by rfl) ⟨1466936, by rfl⟩ : syracuseStep 1955915 = 2933873) B2933873
theorem B1955927 : Blo 1301969 1955927 := bstep (se 1 (by rfl) ⟨1466945, by rfl⟩ : syracuseStep 1955927 = 2933891) B2933891
theorem B2930777 : Blo 1301969 2930777 := bstep (se 2 (by rfl) ⟨1099041, by rfl⟩ : syracuseStep 2930777 = 2198083) B2198083
theorem B9394327 : Blo 1301969 9394327 := bstep (se 1 (by rfl) ⟨7045745, by rfl⟩ : syracuseStep 9394327 = 14091491) B14091491
theorem B2472115 : Blo 1301969 2472115 := bstep (se 1 (by rfl) ⟨1854086, by rfl⟩ : syracuseStep 2472115 = 3708173) B3708173
theorem B2930867 : Blo 1301969 2930867 := bstep (se 1 (by rfl) ⟨2198150, by rfl⟩ : syracuseStep 2930867 = 4396301) B4396301
theorem B1980619 : Blo 1301969 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B2930903 : Blo 1301969 2930903 := bstep (se 1 (by rfl) ⟨2198177, by rfl⟩ : syracuseStep 2930903 = 4396355) B4396355
theorem B4397273 : Blo 1301969 4397273 := bstep (se 2 (by rfl) ⟨1648977, by rfl⟩ : syracuseStep 4397273 = 3297955) B3297955
theorem B7919947 : Blo 1301969 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B11278723 : Blo 1301969 11278723 := bstep (se 1 (by rfl) ⟨8459042, by rfl⟩ : syracuseStep 11278723 = 16918085) B16918085
theorem B2931083 : Blo 1301969 2931083 := bstep (se 1 (by rfl) ⟨2198312, by rfl⟩ : syracuseStep 2931083 = 4396625) B4396625
theorem B47569301 : Blo 1301969 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B1464727 : Blo 1301969 1464727 := bstep (se 1 (by rfl) ⟨1098545, by rfl⟩ : syracuseStep 1464727 = 2197091) B2197091
theorem B2783641 : Blo 1301969 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B2931137 : Blo 1301969 2931137 := bstep (se 2 (by rfl) ⟨1099176, by rfl⟩ : syracuseStep 2931137 = 2198353) B2198353
theorem B1464907 : Blo 1301969 1464907 := bstep (se 1 (by rfl) ⟨1098680, by rfl⟩ : syracuseStep 1464907 = 2197361) B2197361
theorem B2472601 : Blo 1301969 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B2931353 : Blo 1301969 2931353 := bstep (se 2 (by rfl) ⟨1099257, by rfl⟩ : syracuseStep 2931353 = 2198515) B2198515
theorem B1465015 : Blo 1301969 1465015 := bstep (se 1 (by rfl) ⟨1098761, by rfl⟩ : syracuseStep 1465015 = 2197523) B2197523
theorem B37550789 : Blo 1301969 37550789 := bstep (se 4 (by rfl) ⟨3520386, by rfl⟩ : syracuseStep 37550789 = 7040773) B7040773
theorem B2931443 : Blo 1301969 2931443 := bstep (se 1 (by rfl) ⟨2198582, by rfl⟩ : syracuseStep 2931443 = 4397165) B4397165
theorem B2931479 : Blo 1301969 2931479 := bstep (se 1 (by rfl) ⟨2198609, by rfl⟩ : syracuseStep 2931479 = 4397219) B4397219
theorem B1465195 : Blo 1301969 1465195 := bstep (se 1 (by rfl) ⟨1098896, by rfl⟩ : syracuseStep 1465195 = 2197793) B2197793
theorem B4397975 : Blo 1301969 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B2931659 : Blo 1301969 2931659 := bstep (se 1 (by rfl) ⟨2198744, by rfl⟩ : syracuseStep 2931659 = 4397489) B4397489
theorem B1465303 : Blo 1301969 1465303 := bstep (se 1 (by rfl) ⟨1098977, by rfl⟩ : syracuseStep 1465303 = 2197955) B2197955
theorem B6028253 : Blo 1301969 6028253 := bstep (se 3 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 6028253 = 2260595) B2260595
theorem B2931713 : Blo 1301969 2931713 := bstep (se 2 (by rfl) ⟨1099392, by rfl⟩ : syracuseStep 2931713 = 2198785) B2198785
theorem B10026019 : Blo 1301969 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B2784385 : Blo 1301969 2784385 := bstep (se 2 (by rfl) ⟨1044144, by rfl⟩ : syracuseStep 2784385 = 2088289) B2088289
theorem B1760395 : Blo 1301969 1760395 := bstep (se 1 (by rfl) ⟨1320296, by rfl⟩ : syracuseStep 1760395 = 2640593) B2640593
theorem B1465483 : Blo 1301969 1465483 := bstep (se 1 (by rfl) ⟨1099112, by rfl⟩ : syracuseStep 1465483 = 2198225) B2198225
theorem B13376663 : Blo 1301969 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B3964097 : Blo 1301969 3964097 := bstep (se 2 (by rfl) ⟨1486536, by rfl⟩ : syracuseStep 3964097 = 2973073) B2973073
theorem B2227403 : Blo 1301969 2227403 := bstep (se 1 (by rfl) ⟨1670552, by rfl⟩ : syracuseStep 2227403 = 3341105) B3341105
theorem B2473163 : Blo 1301969 2473163 := bstep (se 1 (by rfl) ⟨1854872, by rfl⟩ : syracuseStep 2473163 = 3709745) B3709745
theorem B2931929 : Blo 1301969 2931929 := bstep (se 2 (by rfl) ⟨1099473, by rfl⟩ : syracuseStep 2931929 = 2198947) B2198947
theorem B1391851 : Blo 1301969 1391851 := bstep (se 1 (by rfl) ⟨1043888, by rfl⟩ : syracuseStep 1391851 = 2087777) B2087777
theorem B1465591 : Blo 1301969 1465591 := bstep (se 1 (by rfl) ⟨1099193, by rfl⟩ : syracuseStep 1465591 = 2198387) B2198387
theorem B2932019 : Blo 1301969 2932019 := bstep (se 1 (by rfl) ⟨2199014, by rfl⟩ : syracuseStep 2932019 = 4398029) B4398029
theorem B3300659 : Blo 1301969 3300659 := bstep (se 1 (by rfl) ⟨2475494, by rfl⟩ : syracuseStep 3300659 = 4950989) B4950989
theorem B2932055 : Blo 1301969 2932055 := bstep (se 1 (by rfl) ⟨2199041, by rfl⟩ : syracuseStep 2932055 = 4398083) B4398083
theorem B6593885 : Blo 1301969 6593885 := bstep (se 3 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 6593885 = 2472707) B2472707
theorem B2473345 : Blo 1301969 2473345 := bstep (se 2 (by rfl) ⟨927504, by rfl⟩ : syracuseStep 2473345 = 1855009) B1855009
theorem B6438275 : Blo 1301969 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B1465771 : Blo 1301969 1465771 := bstep (se 1 (by rfl) ⟨1099328, by rfl⟩ : syracuseStep 1465771 = 2198657) B2198657
theorem B4398515 : Blo 1301969 4398515 := bstep (se 1 (by rfl) ⟨3298886, by rfl⟩ : syracuseStep 4398515 = 6597773) B6597773
theorem B9043379 : Blo 1301969 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B1301975 : Blo 1301969 1301975 := bstep (se 1 (by rfl) ⟨976481, by rfl⟩ : syracuseStep 1301975 = 1952963) B1952963
theorem B1301995 : Blo 1301969 1301995 := bstep (se 1 (by rfl) ⟨976496, by rfl⟩ : syracuseStep 1301995 = 1952993) B1952993
theorem B1302007 : Blo 1301969 1302007 := bstep (se 1 (by rfl) ⟨976505, by rfl⟩ : syracuseStep 1302007 = 1953011) B1953011
theorem B1302027 : Blo 1301969 1302027 := bstep (se 1 (by rfl) ⟨976520, by rfl⟩ : syracuseStep 1302027 = 1953041) B1953041
theorem B2932235 : Blo 1301969 2932235 := bstep (se 1 (by rfl) ⟨2199176, by rfl⟩ : syracuseStep 2932235 = 4398353) B4398353
theorem B1302039 : Blo 1301969 1302039 := bstep (se 1 (by rfl) ⟨976529, by rfl⟩ : syracuseStep 1302039 = 1953059) B1953059
theorem B1465879 : Blo 1301969 1465879 := bstep (se 1 (by rfl) ⟨1099409, by rfl⟩ : syracuseStep 1465879 = 2198819) B2198819
theorem B1302059 : Blo 1301969 1302059 := bstep (se 1 (by rfl) ⟨976544, by rfl⟩ : syracuseStep 1302059 = 1953089) B1953089
theorem B1302071 : Blo 1301969 1302071 := bstep (se 1 (by rfl) ⟨976553, by rfl⟩ : syracuseStep 1302071 = 1953107) B1953107
theorem B2932289 : Blo 1301969 2932289 := bstep (se 2 (by rfl) ⟨1099608, by rfl⟩ : syracuseStep 2932289 = 2199217) B2199217
theorem B1302091 : Blo 1301969 1302091 := bstep (se 1 (by rfl) ⟨976568, by rfl⟩ : syracuseStep 1302091 = 1953137) B1953137
theorem B8347211 : Blo 1301969 8347211 := bstep (se 1 (by rfl) ⟨6260408, by rfl⟩ : syracuseStep 8347211 = 12520817) B12520817
theorem B1302103 : Blo 1301969 1302103 := bstep (se 1 (by rfl) ⟨976577, by rfl⟩ : syracuseStep 1302103 = 1953155) B1953155
theorem B1302123 : Blo 1301969 1302123 := bstep (se 1 (by rfl) ⟨976592, by rfl⟩ : syracuseStep 1302123 = 1953185) B1953185
theorem B1302135 : Blo 1301969 1302135 := bstep (se 1 (by rfl) ⟨976601, by rfl⟩ : syracuseStep 1302135 = 1953203) B1953203
theorem B11878019 : Blo 1301969 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B4947587 : Blo 1301969 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B1302155 : Blo 1301969 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B4947601 : Blo 1301969 4947601 := bstep (se 2 (by rfl) ⟨1855350, by rfl⟩ : syracuseStep 4947601 = 3710701) B3710701
theorem B1302167 : Blo 1301969 1302167 := bstep (se 1 (by rfl) ⟨976625, by rfl⟩ : syracuseStep 1302167 = 1953251) B1953251
theorem B1302187 : Blo 1301969 1302187 := bstep (se 1 (by rfl) ⟨976640, by rfl⟩ : syracuseStep 1302187 = 1953281) B1953281
theorem B1302199 : Blo 1301969 1302199 := bstep (se 1 (by rfl) ⟨976649, by rfl⟩ : syracuseStep 1302199 = 1953299) B1953299
theorem B4398785 : Blo 1301969 4398785 := bstep (se 2 (by rfl) ⟨1649544, by rfl⟩ : syracuseStep 4398785 = 3299089) B3299089
theorem B2006731 : Blo 1301969 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B1302219 : Blo 1301969 1302219 := bstep (se 1 (by rfl) ⟨976664, by rfl⟩ : syracuseStep 1302219 = 1953329) B1953329
theorem B1466059 : Blo 1301969 1466059 := bstep (se 1 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 1466059 = 2199089) B2199089
theorem B6110923 : Blo 1301969 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B1302231 : Blo 1301969 1302231 := bstep (se 1 (by rfl) ⟨976673, by rfl⟩ : syracuseStep 1302231 = 1953347) B1953347
theorem B1302251 : Blo 1301969 1302251 := bstep (se 1 (by rfl) ⟨976688, by rfl⟩ : syracuseStep 1302251 = 1953377) B1953377
theorem B1302263 : Blo 1301969 1302263 := bstep (se 1 (by rfl) ⟨976697, by rfl⟩ : syracuseStep 1302263 = 1953395) B1953395
theorem B1302283 : Blo 1301969 1302283 := bstep (se 1 (by rfl) ⟨976712, by rfl⟩ : syracuseStep 1302283 = 1953425) B1953425
theorem B1302295 : Blo 1301969 1302295 := bstep (se 1 (by rfl) ⟨976721, by rfl⟩ : syracuseStep 1302295 = 1953443) B1953443
theorem B2932505 : Blo 1301969 2932505 := bstep (se 2 (by rfl) ⟨1099689, by rfl⟩ : syracuseStep 2932505 = 2199379) B2199379
theorem B1302315 : Blo 1301969 1302315 := bstep (se 1 (by rfl) ⟨976736, by rfl⟩ : syracuseStep 1302315 = 1953473) B1953473
theorem B1302327 : Blo 1301969 1302327 := bstep (se 1 (by rfl) ⟨976745, by rfl⟩ : syracuseStep 1302327 = 1953491) B1953491
theorem B1466167 : Blo 1301969 1466167 := bstep (se 1 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 1466167 = 2199251) B2199251
theorem B1302347 : Blo 1301969 1302347 := bstep (se 1 (by rfl) ⟨976760, by rfl⟩ : syracuseStep 1302347 = 1953521) B1953521
theorem B1302359 : Blo 1301969 1302359 := bstep (se 1 (by rfl) ⟨976769, by rfl⟩ : syracuseStep 1302359 = 1953539) B1953539
theorem B1302379 : Blo 1301969 1302379 := bstep (se 1 (by rfl) ⟨976784, by rfl⟩ : syracuseStep 1302379 = 1953569) B1953569
theorem B2932595 : Blo 1301969 2932595 := bstep (se 1 (by rfl) ⟨2199446, by rfl⟩ : syracuseStep 2932595 = 4398893) B4398893
theorem B1302391 : Blo 1301969 1302391 := bstep (se 1 (by rfl) ⟨976793, by rfl⟩ : syracuseStep 1302391 = 1953587) B1953587
theorem B1302411 : Blo 1301969 1302411 := bstep (se 1 (by rfl) ⟨976808, by rfl⟩ : syracuseStep 1302411 = 1953617) B1953617
theorem B1302423 : Blo 1301969 1302423 := bstep (se 1 (by rfl) ⟨976817, by rfl⟩ : syracuseStep 1302423 = 1953635) B1953635
theorem B2932631 : Blo 1301969 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B2973593 : Blo 1301969 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B7929751 : Blo 1301969 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B1302443 : Blo 1301969 1302443 := bstep (se 1 (by rfl) ⟨976832, by rfl⟩ : syracuseStep 1302443 = 1953665) B1953665
theorem B1302455 : Blo 1301969 1302455 := bstep (se 1 (by rfl) ⟨976841, by rfl⟩ : syracuseStep 1302455 = 1953683) B1953683
theorem B4947905 : Blo 1301969 4947905 := bstep (se 2 (by rfl) ⟨1855464, by rfl⟩ : syracuseStep 4947905 = 3710929) B3710929
theorem B1302475 : Blo 1301969 1302475 := bstep (se 1 (by rfl) ⟨976856, by rfl⟩ : syracuseStep 1302475 = 1953713) B1953713
theorem B1302487 : Blo 1301969 1302487 := bstep (se 1 (by rfl) ⟨976865, by rfl⟩ : syracuseStep 1302487 = 1953731) B1953731
theorem B1302507 : Blo 1301969 1302507 := bstep (se 1 (by rfl) ⟨976880, by rfl⟩ : syracuseStep 1302507 = 1953761) B1953761
theorem B1466347 : Blo 1301969 1466347 := bstep (se 1 (by rfl) ⟨1099760, by rfl⟩ : syracuseStep 1466347 = 2199521) B2199521
theorem B1302519 : Blo 1301969 1302519 := bstep (se 1 (by rfl) ⟨976889, by rfl⟩ : syracuseStep 1302519 = 1953779) B1953779
theorem B1302535 : Blo 1301969 1302535 := bstep (se 1 (by rfl) ⟨976901, by rfl⟩ : syracuseStep 1302535 = 1953803) B1953803
theorem B1302543 : Blo 1301969 1302543 := bstep (se 1 (by rfl) ⟨976907, by rfl⟩ : syracuseStep 1302543 = 1953815) B1953815
theorem B1466383 : Blo 1301969 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B1302587 : Blo 1301969 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B4948087 : Blo 1301969 4948087 := bstep (se 1 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 4948087 = 7422131) B7422131
theorem B1302663 : Blo 1301969 1302663 := bstep (se 1 (by rfl) ⟨976997, by rfl⟩ : syracuseStep 1302663 = 1953995) B1953995
theorem B1761415 : Blo 1301969 1761415 := bstep (se 1 (by rfl) ⟨1321061, by rfl⟩ : syracuseStep 1761415 = 2642123) B2642123
theorem B1302671 : Blo 1301969 1302671 := bstep (se 1 (by rfl) ⟨977003, by rfl⟩ : syracuseStep 1302671 = 1954007) B1954007
theorem B2932883 : Blo 1301969 2932883 := bstep (se 1 (by rfl) ⟨2199662, by rfl⟩ : syracuseStep 2932883 = 4399325) B4399325
theorem B11894957 : Blo 1301969 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B1302715 : Blo 1301969 1302715 := bstep (se 1 (by rfl) ⟨977036, by rfl⟩ : syracuseStep 1302715 = 1954073) B1954073
theorem B12525769 : Blo 1301969 12525769 := bstep (se 2 (by rfl) ⟨4697163, by rfl⟩ : syracuseStep 12525769 = 9394327) B9394327
theorem B2932937 : Blo 1301969 2932937 := bstep (se 2 (by rfl) ⟨1099851, by rfl⟩ : syracuseStep 2932937 = 2199703) B2199703
theorem B1302791 : Blo 1301969 1302791 := bstep (se 1 (by rfl) ⟨977093, by rfl⟩ : syracuseStep 1302791 = 1954187) B1954187
theorem B1302799 : Blo 1301969 1302799 := bstep (se 1 (by rfl) ⟨977099, by rfl⟩ : syracuseStep 1302799 = 1954199) B1954199
theorem B1564987 : Blo 1301969 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B1302843 : Blo 1301969 1302843 := bstep (se 1 (by rfl) ⟨977132, by rfl⟩ : syracuseStep 1302843 = 1954265) B1954265
theorem B1302919 : Blo 1301969 1302919 := bstep (se 1 (by rfl) ⟨977189, by rfl⟩ : syracuseStep 1302919 = 1954379) B1954379
theorem B1302927 : Blo 1301969 1302927 := bstep (se 1 (by rfl) ⟨977195, by rfl⟩ : syracuseStep 1302927 = 1954391) B1954391
theorem B1302971 : Blo 1301969 1302971 := bstep (se 1 (by rfl) ⟨977228, by rfl⟩ : syracuseStep 1302971 = 1954457) B1954457
theorem B6595019 : Blo 1301969 6595019 := bstep (se 1 (by rfl) ⟨4946264, by rfl⟩ : syracuseStep 6595019 = 9892529) B9892529
theorem B1303047 : Blo 1301969 1303047 := bstep (se 1 (by rfl) ⟨977285, by rfl⟩ : syracuseStep 1303047 = 1954571) B1954571
theorem B1466887 : Blo 1301969 1466887 := bstep (se 1 (by rfl) ⟨1100165, by rfl⟩ : syracuseStep 1466887 = 2200331) B2200331
theorem B1303055 : Blo 1301969 1303055 := bstep (se 1 (by rfl) ⟨977291, by rfl⟩ : syracuseStep 1303055 = 1954583) B1954583
theorem B3711521 : Blo 1301969 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B1303099 : Blo 1301969 1303099 := bstep (se 1 (by rfl) ⟨977324, by rfl⟩ : syracuseStep 1303099 = 1954649) B1954649
theorem B4399703 : Blo 1301969 4399703 := bstep (se 1 (by rfl) ⟨3299777, by rfl⟩ : syracuseStep 4399703 = 6599555) B6599555
theorem B1303175 : Blo 1301969 1303175 := bstep (se 1 (by rfl) ⟨977381, by rfl⟩ : syracuseStep 1303175 = 1954763) B1954763
theorem B1303183 : Blo 1301969 1303183 := bstep (se 1 (by rfl) ⟨977387, by rfl⟩ : syracuseStep 1303183 = 1954775) B1954775
theorem B1303227 : Blo 1301969 1303227 := bstep (se 1 (by rfl) ⟨977420, by rfl⟩ : syracuseStep 1303227 = 1954841) B1954841
theorem B8913665 : Blo 1301969 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B11887361 : Blo 1301969 11887361 := bstep (se 2 (by rfl) ⟨4457760, by rfl⟩ : syracuseStep 11887361 = 8915521) B8915521
theorem B1303303 : Blo 1301969 1303303 := bstep (se 1 (by rfl) ⟨977477, by rfl⟩ : syracuseStep 1303303 = 1954955) B1954955
theorem B6595343 : Blo 1301969 6595343 := bstep (se 1 (by rfl) ⟨4946507, by rfl⟩ : syracuseStep 6595343 = 9893015) B9893015
theorem B1303311 : Blo 1301969 1303311 := bstep (se 1 (by rfl) ⟨977483, by rfl⟩ : syracuseStep 1303311 = 1954967) B1954967
theorem B10560293 : Blo 1301969 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B1303355 : Blo 1301969 1303355 := bstep (se 1 (by rfl) ⟨977516, by rfl⟩ : syracuseStep 1303355 = 1955033) B1955033
theorem B1303431 : Blo 1301969 1303431 := bstep (se 1 (by rfl) ⟨977573, by rfl⟩ : syracuseStep 1303431 = 1955147) B1955147
theorem B2474887 : Blo 1301969 2474887 := bstep (se 1 (by rfl) ⟨1856165, by rfl⟩ : syracuseStep 2474887 = 3712331) B3712331
theorem B2933639 : Blo 1301969 2933639 := bstep (se 1 (by rfl) ⟨2200229, by rfl⟩ : syracuseStep 2933639 = 4400459) B4400459
theorem B1303439 : Blo 1301969 1303439 := bstep (se 1 (by rfl) ⟨977579, by rfl⟩ : syracuseStep 1303439 = 1955159) B1955159
theorem B1303483 : Blo 1301969 1303483 := bstep (se 1 (by rfl) ⟨977612, by rfl⟩ : syracuseStep 1303483 = 1955225) B1955225
theorem B1303559 : Blo 1301969 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B1303567 : Blo 1301969 1303567 := bstep (se 1 (by rfl) ⟨977675, by rfl⟩ : syracuseStep 1303567 = 1955351) B1955351
theorem B3171361 : Blo 1301969 3171361 := bstep (se 2 (by rfl) ⟨1189260, by rfl⟩ : syracuseStep 3171361 = 2378521) B2378521
theorem B1303611 : Blo 1301969 1303611 := bstep (se 1 (by rfl) ⟨977708, by rfl⟩ : syracuseStep 1303611 = 1955417) B1955417
theorem B2933819 : Blo 1301969 2933819 := bstep (se 1 (by rfl) ⟨2200364, by rfl⟩ : syracuseStep 2933819 = 4400729) B4400729
theorem B4400189 : Blo 1301969 4400189 := bstep (se 3 (by rfl) ⟨825035, by rfl⟩ : syracuseStep 4400189 = 1650071) B1650071
theorem B4949059 : Blo 1301969 4949059 := bstep (se 1 (by rfl) ⟨3711794, by rfl⟩ : syracuseStep 4949059 = 7423589) B7423589
theorem B1303687 : Blo 1301969 1303687 := bstep (se 1 (by rfl) ⟨977765, by rfl⟩ : syracuseStep 1303687 = 1955531) B1955531
theorem B1303695 : Blo 1301969 1303695 := bstep (se 1 (by rfl) ⟨977771, by rfl⟩ : syracuseStep 1303695 = 1955543) B1955543
theorem B1303739 : Blo 1301969 1303739 := bstep (se 1 (by rfl) ⟨977804, by rfl⟩ : syracuseStep 1303739 = 1955609) B1955609
theorem B1303815 : Blo 1301969 1303815 := bstep (se 1 (by rfl) ⟨977861, by rfl⟩ : syracuseStep 1303815 = 1955723) B1955723
theorem B1303823 : Blo 1301969 1303823 := bstep (se 1 (by rfl) ⟨977867, by rfl⟩ : syracuseStep 1303823 = 1955735) B1955735
theorem B1303867 : Blo 1301969 1303867 := bstep (se 1 (by rfl) ⟨977900, by rfl⟩ : syracuseStep 1303867 = 1955801) B1955801
theorem B4949363 : Blo 1301969 4949363 := bstep (se 1 (by rfl) ⟨3712022, by rfl⟩ : syracuseStep 4949363 = 7424045) B7424045
theorem B1303943 : Blo 1301969 1303943 := bstep (se 1 (by rfl) ⟨977957, by rfl⟩ : syracuseStep 1303943 = 1955915) B1955915
theorem B1303951 : Blo 1301969 1303951 := bstep (se 1 (by rfl) ⟨977963, by rfl⟩ : syracuseStep 1303951 = 1955927) B1955927
theorem B9389459 : Blo 1301969 9389459 := bstep (se 1 (by rfl) ⟨7042094, by rfl⟩ : syracuseStep 9389459 = 14084189) B14084189
theorem B3130771 : Blo 1301969 3130771 := bstep (se 1 (by rfl) ⟨2348078, by rfl⟩ : syracuseStep 3130771 = 4696157) B4696157
theorem B3712513 : Blo 1301969 3712513 := bstep (se 2 (by rfl) ⟨1392192, by rfl⟩ : syracuseStep 3712513 = 2784385) B2784385
theorem B31712867 : Blo 1301969 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B2197111 : Blo 1301969 2197111 := bstep (se 1 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 2197111 = 3295667) B3295667
theorem B3524249 : Blo 1301969 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B42239717 : Blo 1301969 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B6686479 : Blo 1301969 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B5793569 : Blo 1301969 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B2197307 : Blo 1301969 2197307 := bstep (se 1 (by rfl) ⟨1647980, by rfl⟩ : syracuseStep 2197307 = 3295961) B3295961
theorem B4949819 : Blo 1301969 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B3131435 : Blo 1301969 3131435 := bstep (se 1 (by rfl) ⟨2348576, by rfl⟩ : syracuseStep 3131435 = 4697153) B4697153
theorem B4458557 : Blo 1301969 4458557 := bstep (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) B1671959
theorem B1484935 : Blo 1301969 1484935 := bstep (se 1 (by rfl) ⟨1113701, by rfl⟩ : syracuseStep 1484935 = 2227403) B2227403
theorem B1648775 : Blo 1301969 1648775 := bstep (se 1 (by rfl) ⟨1236581, by rfl⟩ : syracuseStep 1648775 = 2473163) B2473163
theorem B7415981 : Blo 1301969 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B6596801 : Blo 1301969 6596801 := bstep (se 2 (by rfl) ⟨2473800, by rfl⟩ : syracuseStep 6596801 = 4947601) B4947601
theorem B2197705 : Blo 1301969 2197705 := bstep (se 2 (by rfl) ⟨824139, by rfl⟩ : syracuseStep 2197705 = 1648279) B1648279
theorem B4950305 : Blo 1301969 4950305 := bstep (se 2 (by rfl) ⟨1856364, by rfl⟩ : syracuseStep 4950305 = 3712729) B3712729
theorem B54241589 : Blo 1301969 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B5564807 : Blo 1301969 5564807 := bstep (se 1 (by rfl) ⟨4173605, by rfl⟩ : syracuseStep 5564807 = 8347211) B8347211
theorem B50112917 : Blo 1301969 50112917 := bstep (se 6 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 50112917 = 2349043) B2349043
theorem B57117149 : Blo 1301969 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B17828417 : Blo 1301969 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B4172489 : Blo 1301969 4172489 := bstep (se 2 (by rfl) ⟨1564683, by rfl⟩ : syracuseStep 4172489 = 3129367) B3129367
theorem B3296011 : Blo 1301969 3296011 := bstep (se 1 (by rfl) ⟨2472008, by rfl⟩ : syracuseStep 3296011 = 4944017) B4944017
theorem B1649423 : Blo 1301969 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B1854343 : Blo 1301969 1854343 := bstep (se 1 (by rfl) ⟨1390757, by rfl⟩ : syracuseStep 1854343 = 2781515) B2781515
theorem B2198407 : Blo 1301969 2198407 := bstep (se 1 (by rfl) ⟨1648805, by rfl⟩ : syracuseStep 2198407 = 3297611) B3297611
theorem B3296153 : Blo 1301969 3296153 := bstep (se 2 (by rfl) ⟨1236057, by rfl⟩ : syracuseStep 3296153 = 2472115) B2472115
theorem B5286809 : Blo 1301969 5286809 := bstep (se 2 (by rfl) ⟨1982553, by rfl⟩ : syracuseStep 5286809 = 3965107) B3965107
theorem B5082065 : Blo 1301969 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B7425047 : Blo 1301969 7425047 := bstep (se 1 (by rfl) ⟨5568785, by rfl⟩ : syracuseStep 7425047 = 11137571) B11137571
theorem B3296315 : Blo 1301969 3296315 := bstep (se 1 (by rfl) ⟨2472236, by rfl⟩ : syracuseStep 3296315 = 4944473) B4944473
theorem B4172887 : Blo 1301969 4172887 := bstep (se 1 (by rfl) ⟨3129665, by rfl⟩ : syracuseStep 4172887 = 6259331) B6259331
theorem B10570925 : Blo 1301969 10570925 := bstep (se 3 (by rfl) ⟨1982048, by rfl⟩ : syracuseStep 10570925 = 3964097) B3964097
theorem B1952969 : Blo 1301969 1952969 := bstep (se 2 (by rfl) ⟨732363, by rfl⟩ : syracuseStep 1952969 = 1464727) B1464727
theorem B1953083 : Blo 1301969 1953083 := bstep (se 1 (by rfl) ⟨1464812, by rfl⟩ : syracuseStep 1953083 = 2929625) B2929625
theorem B1953143 : Blo 1301969 1953143 := bstep (se 1 (by rfl) ⟨1464857, by rfl⟩ : syracuseStep 1953143 = 2929715) B2929715
theorem B1953167 : Blo 1301969 1953167 := bstep (se 1 (by rfl) ⟨1464875, by rfl⟩ : syracuseStep 1953167 = 2929751) B2929751
theorem B3296659 : Blo 1301969 3296659 := bstep (se 1 (by rfl) ⟨2472494, by rfl⟩ : syracuseStep 3296659 = 4944989) B4944989
theorem B1953209 : Blo 1301969 1953209 := bstep (se 2 (by rfl) ⟨732453, by rfl⟩ : syracuseStep 1953209 = 1464907) B1464907
theorem B6598097 : Blo 1301969 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B1953287 : Blo 1301969 1953287 := bstep (se 1 (by rfl) ⟨1464965, by rfl⟩ : syracuseStep 1953287 = 2929931) B2929931
theorem B2199055 : Blo 1301969 2199055 := bstep (se 1 (by rfl) ⟨1649291, by rfl⟩ : syracuseStep 2199055 = 3298583) B3298583
theorem B3296801 : Blo 1301969 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B1953323 : Blo 1301969 1953323 := bstep (se 1 (by rfl) ⟨1464992, by rfl⟩ : syracuseStep 1953323 = 2929985) B2929985
theorem B1953353 : Blo 1301969 1953353 := bstep (se 2 (by rfl) ⟨732507, by rfl⟩ : syracuseStep 1953353 = 1465015) B1465015
theorem B1953467 : Blo 1301969 1953467 := bstep (se 1 (by rfl) ⟨1465100, by rfl⟩ : syracuseStep 1953467 = 2930201) B2930201
theorem B1855163 : Blo 1301969 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B11128549 : Blo 1301969 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B9891557 : Blo 1301969 9891557 := bstep (se 4 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 9891557 = 1854667) B1854667
theorem B10563301 : Blo 1301969 10563301 := bstep (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) B1980619
theorem B6688493 : Blo 1301969 6688493 := bstep (se 3 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 6688493 = 2508185) B2508185
theorem B1953527 : Blo 1301969 1953527 := bstep (se 1 (by rfl) ⟨1465145, by rfl⟩ : syracuseStep 1953527 = 2930291) B2930291
theorem B1953551 : Blo 1301969 1953551 := bstep (se 1 (by rfl) ⟨1465163, by rfl⟩ : syracuseStep 1953551 = 2930327) B2930327
theorem B1953593 : Blo 1301969 1953593 := bstep (se 2 (by rfl) ⟨732597, by rfl⟩ : syracuseStep 1953593 = 1465195) B1465195
theorem B1953671 : Blo 1301969 1953671 := bstep (se 1 (by rfl) ⟨1465253, by rfl⟩ : syracuseStep 1953671 = 2930507) B2930507
theorem B1953707 : Blo 1301969 1953707 := bstep (se 1 (by rfl) ⟨1465280, by rfl⟩ : syracuseStep 1953707 = 2930561) B2930561
theorem B1953737 : Blo 1301969 1953737 := bstep (se 2 (by rfl) ⟨732651, by rfl⟩ : syracuseStep 1953737 = 1465303) B1465303
theorem B5279755 : Blo 1301969 5279755 := bstep (se 1 (by rfl) ⟨3959816, by rfl⟩ : syracuseStep 5279755 = 7919633) B7919633
theorem B2199595 : Blo 1301969 2199595 := bstep (se 1 (by rfl) ⟨1649696, by rfl⟩ : syracuseStep 2199595 = 3299393) B3299393
theorem B1953851 : Blo 1301969 1953851 := bstep (se 1 (by rfl) ⟨1465388, by rfl⟩ : syracuseStep 1953851 = 2930777) B2930777
theorem B1953911 : Blo 1301969 1953911 := bstep (se 1 (by rfl) ⟨1465433, by rfl⟩ : syracuseStep 1953911 = 2930867) B2930867
theorem B5566583 : Blo 1301969 5566583 := bstep (se 1 (by rfl) ⟨4174937, by rfl⟩ : syracuseStep 5566583 = 8349875) B8349875
theorem B1953935 : Blo 1301969 1953935 := bstep (se 1 (by rfl) ⟨1465451, by rfl⟩ : syracuseStep 1953935 = 2930903) B2930903
theorem B2347193 : Blo 1301969 2347193 := bstep (se 2 (by rfl) ⟨880197, by rfl⟩ : syracuseStep 2347193 = 1760395) B1760395
theorem B1953977 : Blo 1301969 1953977 := bstep (se 2 (by rfl) ⟨732741, by rfl⟩ : syracuseStep 1953977 = 1465483) B1465483
theorem B2199737 : Blo 1301969 2199737 := bstep (se 2 (by rfl) ⟨824901, by rfl⟩ : syracuseStep 2199737 = 1649803) B1649803
theorem B6263021 : Blo 1301969 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B1954055 : Blo 1301969 1954055 := bstep (se 1 (by rfl) ⟨1465541, by rfl⟩ : syracuseStep 1954055 = 2931083) B2931083
theorem B5566735 : Blo 1301969 5566735 := bstep (se 1 (by rfl) ⟨4175051, by rfl⟩ : syracuseStep 5566735 = 8350103) B8350103
theorem B1954091 : Blo 1301969 1954091 := bstep (se 1 (by rfl) ⟨1465568, by rfl⟩ : syracuseStep 1954091 = 2931137) B2931137
theorem B1855801 : Blo 1301969 1855801 := bstep (se 2 (by rfl) ⟨695925, by rfl⟩ : syracuseStep 1855801 = 1391851) B1391851
theorem B7516475 : Blo 1301969 7516475 := bstep (se 1 (by rfl) ⟨5637356, by rfl⟩ : syracuseStep 7516475 = 11274713) B11274713
theorem B1954121 : Blo 1301969 1954121 := bstep (se 2 (by rfl) ⟨732795, by rfl⟩ : syracuseStep 1954121 = 1465591) B1465591
theorem B3567959 : Blo 1301969 3567959 := bstep (se 1 (by rfl) ⟨2675969, by rfl⟩ : syracuseStep 3567959 = 5351939) B5351939
theorem B1954235 : Blo 1301969 1954235 := bstep (se 1 (by rfl) ⟨1465676, by rfl⟩ : syracuseStep 1954235 = 2931353) B2931353
theorem B1954295 : Blo 1301969 1954295 := bstep (se 1 (by rfl) ⟨1465721, by rfl⟩ : syracuseStep 1954295 = 2931443) B2931443
theorem B3297793 : Blo 1301969 3297793 := bstep (se 2 (by rfl) ⟨1236672, by rfl⟩ : syracuseStep 3297793 = 2473345) B2473345
theorem B1954319 : Blo 1301969 1954319 := bstep (se 1 (by rfl) ⟨1465739, by rfl⟩ : syracuseStep 1954319 = 2931479) B2931479
theorem B1954361 : Blo 1301969 1954361 := bstep (se 2 (by rfl) ⟨732885, by rfl⟩ : syracuseStep 1954361 = 1465771) B1465771
theorem B4944503 : Blo 1301969 4944503 := bstep (se 1 (by rfl) ⟨3708377, by rfl⟩ : syracuseStep 4944503 = 7416755) B7416755
theorem B1954439 : Blo 1301969 1954439 := bstep (se 1 (by rfl) ⟨1465829, by rfl⟩ : syracuseStep 1954439 = 2931659) B2931659
theorem B4018835 : Blo 1301969 4018835 := bstep (se 1 (by rfl) ⟨3014126, by rfl⟩ : syracuseStep 4018835 = 6028253) B6028253
theorem B1954475 : Blo 1301969 1954475 := bstep (se 1 (by rfl) ⟨1465856, by rfl⟩ : syracuseStep 1954475 = 2931713) B2931713
theorem B1954505 : Blo 1301969 1954505 := bstep (se 2 (by rfl) ⟨732939, by rfl⟩ : syracuseStep 1954505 = 1465879) B1465879
theorem B2781967 : Blo 1301969 2781967 := bstep (se 1 (by rfl) ⟨2086475, by rfl⟩ : syracuseStep 2781967 = 4172951) B4172951
theorem B8917775 : Blo 1301969 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B1954619 : Blo 1301969 1954619 := bstep (se 1 (by rfl) ⟨1465964, by rfl⟩ : syracuseStep 1954619 = 2931929) B2931929
theorem B1954679 : Blo 1301969 1954679 := bstep (se 1 (by rfl) ⟨1466009, by rfl⟩ : syracuseStep 1954679 = 2932019) B2932019
theorem B2200439 : Blo 1301969 2200439 := bstep (se 1 (by rfl) ⟨1650329, by rfl⟩ : syracuseStep 2200439 = 3300659) B3300659
theorem B1954703 : Blo 1301969 1954703 := bstep (se 1 (by rfl) ⟨1466027, by rfl⟩ : syracuseStep 1954703 = 2932055) B2932055
theorem B4395923 : Blo 1301969 4395923 := bstep (se 1 (by rfl) ⟨3296942, by rfl⟩ : syracuseStep 4395923 = 6593885) B6593885
theorem B2675641 : Blo 1301969 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B1954745 : Blo 1301969 1954745 := bstep (se 2 (by rfl) ⟨733029, by rfl⟩ : syracuseStep 1954745 = 1466059) B1466059
theorem B8147897 : Blo 1301969 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B1954823 : Blo 1301969 1954823 := bstep (se 1 (by rfl) ⟨1466117, by rfl⟩ : syracuseStep 1954823 = 2932235) B2932235
theorem B2929679 : Blo 1301969 2929679 := bstep (se 1 (by rfl) ⟨2197259, by rfl⟩ : syracuseStep 2929679 = 4394519) B4394519
theorem B2929697 : Blo 1301969 2929697 := bstep (se 2 (by rfl) ⟨1098636, by rfl⟩ : syracuseStep 2929697 = 2197273) B2197273
theorem B1954859 : Blo 1301969 1954859 := bstep (se 1 (by rfl) ⟨1466144, by rfl⟩ : syracuseStep 1954859 = 2932289) B2932289
theorem B5567555 : Blo 1301969 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B1954889 : Blo 1301969 1954889 := bstep (se 2 (by rfl) ⟨733083, by rfl⟩ : syracuseStep 1954889 = 1466167) B1466167
theorem B7918679 : Blo 1301969 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B3298391 : Blo 1301969 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B2782343 : Blo 1301969 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B1955003 : Blo 1301969 1955003 := bstep (se 1 (by rfl) ⟨1466252, by rfl⟩ : syracuseStep 1955003 = 2932505) B2932505
theorem B10573001 : Blo 1301969 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B90273005 : Blo 1301969 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B1955063 : Blo 1301969 1955063 := bstep (se 1 (by rfl) ⟨1466297, by rfl⟩ : syracuseStep 1955063 = 2932595) B2932595
theorem B1955087 : Blo 1301969 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B3298603 : Blo 1301969 3298603 := bstep (se 1 (by rfl) ⟨2473952, by rfl⟩ : syracuseStep 3298603 = 4947905) B4947905
theorem B1955129 : Blo 1301969 1955129 := bstep (se 2 (by rfl) ⟨733173, by rfl⟩ : syracuseStep 1955129 = 1466347) B1466347
theorem B2930039 : Blo 1301969 2930039 := bstep (se 1 (by rfl) ⟨2197529, by rfl⟩ : syracuseStep 2930039 = 4395059) B4395059
theorem B1955207 : Blo 1301969 1955207 := bstep (se 1 (by rfl) ⟨1466405, by rfl⟩ : syracuseStep 1955207 = 2932811) B2932811
theorem B1955243 : Blo 1301969 1955243 := bstep (se 1 (by rfl) ⟨1466432, by rfl⟩ : syracuseStep 1955243 = 2932865) B2932865
theorem B3298745 : Blo 1301969 3298745 := bstep (se 2 (by rfl) ⟨1237029, by rfl⟩ : syracuseStep 3298745 = 2474059) B2474059
theorem B1955273 : Blo 1301969 1955273 := bstep (se 2 (by rfl) ⟨733227, by rfl⟩ : syracuseStep 1955273 = 1466455) B1466455
theorem B6600203 : Blo 1301969 6600203 := bstep (se 1 (by rfl) ⟨4950152, by rfl⟩ : syracuseStep 6600203 = 9900305) B9900305
theorem B2930219 : Blo 1301969 2930219 := bstep (se 1 (by rfl) ⟨2197664, by rfl⟩ : syracuseStep 2930219 = 4395329) B4395329
theorem B1955387 : Blo 1301969 1955387 := bstep (se 1 (by rfl) ⟨1466540, by rfl⟩ : syracuseStep 1955387 = 2933081) B2933081
theorem B4945475 : Blo 1301969 4945475 := bstep (se 1 (by rfl) ⟨3709106, by rfl⟩ : syracuseStep 4945475 = 7418213) B7418213
theorem B11884151 : Blo 1301969 11884151 := bstep (se 1 (by rfl) ⟨8913113, by rfl⟩ : syracuseStep 11884151 = 17826227) B17826227
theorem B1955447 : Blo 1301969 1955447 := bstep (se 1 (by rfl) ⟨1466585, by rfl⟩ : syracuseStep 1955447 = 2933171) B2933171
theorem B1955471 : Blo 1301969 1955471 := bstep (se 1 (by rfl) ⟨1466603, by rfl⟩ : syracuseStep 1955471 = 2933207) B2933207
theorem B6600365 : Blo 1301969 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B1955513 : Blo 1301969 1955513 := bstep (se 2 (by rfl) ⟨733317, by rfl⟩ : syracuseStep 1955513 = 1466635) B1466635
theorem B14849729 : Blo 1301969 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B35641061 : Blo 1301969 35641061 := bstep (se 4 (by rfl) ⟨3341349, by rfl⟩ : syracuseStep 35641061 = 6682699) B6682699
theorem B1955591 : Blo 1301969 1955591 := bstep (se 1 (by rfl) ⟨1466693, by rfl⟩ : syracuseStep 1955591 = 2933387) B2933387
theorem B1955627 : Blo 1301969 1955627 := bstep (se 1 (by rfl) ⟨1466720, by rfl⟩ : syracuseStep 1955627 = 2933441) B2933441
theorem B1955657 : Blo 1301969 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B27121483 : Blo 1301969 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B15038297 : Blo 1301969 15038297 := bstep (se 2 (by rfl) ⟨5639361, by rfl⟩ : syracuseStep 15038297 = 11278723) B11278723
theorem B2930579 : Blo 1301969 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B1955771 : Blo 1301969 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B2930633 : Blo 1301969 2930633 := bstep (se 2 (by rfl) ⟨1098987, by rfl⟩ : syracuseStep 2930633 = 2197975) B2197975
theorem B1955831 : Blo 1301969 1955831 := bstep (se 1 (by rfl) ⟨1466873, by rfl⟩ : syracuseStep 1955831 = 2933747) B2933747
theorem B4945931 : Blo 1301969 4945931 := bstep (se 1 (by rfl) ⟨3709448, by rfl⟩ : syracuseStep 4945931 = 7418897) B7418897
theorem B1955855 : Blo 1301969 1955855 := bstep (se 1 (by rfl) ⟨1466891, by rfl⟩ : syracuseStep 1955855 = 2933783) B2933783
theorem B1955897 : Blo 1301969 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B2349175 : Blo 1301969 2349175 := bstep (se 1 (by rfl) ⟨1761881, by rfl⟩ : syracuseStep 2349175 = 3523763) B3523763
theorem B1390727 : Blo 1301969 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B4397327 : Blo 1301969 4397327 := bstep (se 1 (by rfl) ⟨3297995, by rfl⟩ : syracuseStep 4397327 = 6595991) B6595991
theorem B3709243 : Blo 1301969 3709243 := bstep (se 1 (by rfl) ⟨2781932, by rfl⟩ : syracuseStep 3709243 = 5563865) B5563865
theorem B6592913 : Blo 1301969 6592913 := bstep (se 2 (by rfl) ⟨2472342, by rfl⟩ : syracuseStep 6592913 = 4944685) B4944685
theorem B11131283 : Blo 1301969 11131283 := bstep (se 1 (by rfl) ⟨8348462, by rfl⟩ : syracuseStep 11131283 = 16696925) B16696925
theorem B3299737 : Blo 1301969 3299737 := bstep (se 2 (by rfl) ⟨1237401, by rfl⟩ : syracuseStep 3299737 = 2474803) B2474803
theorem B1464763 : Blo 1301969 1464763 := bstep (se 1 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 1464763 = 2197145) B2197145
theorem B4397597 : Blo 1301969 4397597 := bstep (se 3 (by rfl) ⟨824549, by rfl⟩ : syracuseStep 4397597 = 1649099) B1649099
theorem B3299899 : Blo 1301969 3299899 := bstep (se 1 (by rfl) ⟨2474924, by rfl⟩ : syracuseStep 3299899 = 4949849) B4949849
theorem B2931335 : Blo 1301969 2931335 := bstep (se 1 (by rfl) ⟨2198501, by rfl⟩ : syracuseStep 2931335 = 4397003) B4397003
theorem B3300041 : Blo 1301969 3300041 := bstep (se 2 (by rfl) ⟨1237515, by rfl⟩ : syracuseStep 3300041 = 2475031) B2475031
theorem B13368025 : Blo 1301969 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B7420673 : Blo 1301969 7420673 := bstep (se 2 (by rfl) ⟨2782752, by rfl⟩ : syracuseStep 7420673 = 5565505) B5565505
theorem B2931515 : Blo 1301969 2931515 := bstep (se 1 (by rfl) ⟨2198636, by rfl⟩ : syracuseStep 2931515 = 4397273) B4397273
theorem B17832793 : Blo 1301969 17832793 := bstep (se 2 (by rfl) ⟨6687297, by rfl⟩ : syracuseStep 17832793 = 13374595) B13374595
theorem B1465231 : Blo 1301969 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B2931641 : Blo 1301969 2931641 := bstep (se 2 (by rfl) ⟨1099365, by rfl⟩ : syracuseStep 2931641 = 2198731) B2198731
theorem B2472905 : Blo 1301969 2472905 := bstep (se 2 (by rfl) ⟨927339, by rfl⟩ : syracuseStep 2472905 = 1854679) B1854679
theorem B3300385 : Blo 1301969 3300385 := bstep (se 2 (by rfl) ⟨1237644, by rfl⟩ : syracuseStep 3300385 = 2475289) B2475289
theorem B5561405 : Blo 1301969 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B25033859 : Blo 1301969 25033859 := bstep (se 1 (by rfl) ⟨18775394, by rfl⟩ : syracuseStep 25033859 = 37550789) B37550789
theorem B3710087 : Blo 1301969 3710087 := bstep (se 1 (by rfl) ⟨2782565, by rfl⟩ : syracuseStep 3710087 = 5565131) B5565131
theorem B7421129 : Blo 1301969 7421129 := bstep (se 2 (by rfl) ⟨2782923, by rfl⟩ : syracuseStep 7421129 = 5565847) B5565847
theorem B2931983 : Blo 1301969 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B2932001 : Blo 1301969 2932001 := bstep (se 2 (by rfl) ⟨1099500, by rfl⟩ : syracuseStep 2932001 = 2199001) B2199001
theorem B21405059 : Blo 1301969 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B1465735 : Blo 1301969 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B5561747 : Blo 1301969 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B14835149 : Blo 1301969 14835149 := bstep (se 3 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 14835149 = 5563181) B5563181
theorem B1302023 : Blo 1301969 1302023 := bstep (se 1 (by rfl) ⟨976517, by rfl⟩ : syracuseStep 1302023 = 1953035) B1953035
theorem B1302031 : Blo 1301969 1302031 := bstep (se 1 (by rfl) ⟨976523, by rfl⟩ : syracuseStep 1302031 = 1953047) B1953047
theorem B1760783 : Blo 1301969 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B1302075 : Blo 1301969 1302075 := bstep (se 1 (by rfl) ⟨976556, by rfl⟩ : syracuseStep 1302075 = 1953113) B1953113
theorem B1465915 : Blo 1301969 1465915 := bstep (se 1 (by rfl) ⟨1099436, by rfl⟩ : syracuseStep 1465915 = 2198873) B2198873
theorem B4292183 : Blo 1301969 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B2932343 : Blo 1301969 2932343 := bstep (se 1 (by rfl) ⟨2199257, by rfl⟩ : syracuseStep 2932343 = 4398515) B4398515
theorem B6028919 : Blo 1301969 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B1302151 : Blo 1301969 1302151 := bstep (se 1 (by rfl) ⟨976613, by rfl⟩ : syracuseStep 1302151 = 1953227) B1953227
theorem B1302159 : Blo 1301969 1302159 := bstep (se 1 (by rfl) ⟨976619, by rfl⟩ : syracuseStep 1302159 = 1953239) B1953239
theorem B1302203 : Blo 1301969 1302203 := bstep (se 1 (by rfl) ⟨976652, by rfl⟩ : syracuseStep 1302203 = 1953305) B1953305
theorem B1302279 : Blo 1301969 1302279 := bstep (se 1 (by rfl) ⟨976709, by rfl⟩ : syracuseStep 1302279 = 1953419) B1953419
theorem B1302287 : Blo 1301969 1302287 := bstep (se 1 (by rfl) ⟨976715, by rfl⟩ : syracuseStep 1302287 = 1953431) B1953431
theorem B2932523 : Blo 1301969 2932523 := bstep (se 1 (by rfl) ⟨2199392, by rfl⟩ : syracuseStep 2932523 = 4398785) B4398785
theorem B1302331 : Blo 1301969 1302331 := bstep (se 1 (by rfl) ⟨976748, by rfl⟩ : syracuseStep 1302331 = 1953497) B1953497
theorem B1302407 : Blo 1301969 1302407 := bstep (se 1 (by rfl) ⟨976805, by rfl⟩ : syracuseStep 1302407 = 1953611) B1953611
theorem B1302415 : Blo 1301969 1302415 := bstep (se 1 (by rfl) ⟨976811, by rfl⟩ : syracuseStep 1302415 = 1953623) B1953623
theorem B3710873 : Blo 1301969 3710873 := bstep (se 2 (by rfl) ⟨1391577, by rfl⟩ : syracuseStep 3710873 = 2783155) B2783155
theorem B4399001 : Blo 1301969 4399001 := bstep (se 2 (by rfl) ⟨1649625, by rfl⟩ : syracuseStep 4399001 = 3299251) B3299251
theorem B1302459 : Blo 1301969 1302459 := bstep (se 1 (by rfl) ⟨976844, by rfl⟩ : syracuseStep 1302459 = 1953689) B1953689
theorem B1982395 : Blo 1301969 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B1302567 : Blo 1301969 1302567 := bstep (se 1 (by rfl) ⟨976925, by rfl⟩ : syracuseStep 1302567 = 1953851) B1953851
theorem B2932793 : Blo 1301969 2932793 := bstep (se 2 (by rfl) ⟨1099797, by rfl⟩ : syracuseStep 2932793 = 2199595) B2199595
theorem B1302607 : Blo 1301969 1302607 := bstep (se 1 (by rfl) ⟨976955, by rfl⟩ : syracuseStep 1302607 = 1953911) B1953911
theorem B3711055 : Blo 1301969 3711055 := bstep (se 1 (by rfl) ⟨2783291, by rfl⟩ : syracuseStep 3711055 = 5566583) B5566583
theorem B1302623 : Blo 1301969 1302623 := bstep (se 1 (by rfl) ⟨976967, by rfl⟩ : syracuseStep 1302623 = 1953935) B1953935
theorem B7929971 : Blo 1301969 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B1564795 : Blo 1301969 1564795 := bstep (se 1 (by rfl) ⟨1173596, by rfl⟩ : syracuseStep 1564795 = 2347193) B2347193
theorem B1302651 : Blo 1301969 1302651 := bstep (se 1 (by rfl) ⟨976988, by rfl⟩ : syracuseStep 1302651 = 1953977) B1953977
theorem B1466491 : Blo 1301969 1466491 := bstep (se 1 (by rfl) ⟨1099868, by rfl⟩ : syracuseStep 1466491 = 2199737) B2199737
theorem B31678613 : Blo 1301969 31678613 := bstep (se 6 (by rfl) ⟨742467, by rfl⟩ : syracuseStep 31678613 = 1484935) B1484935
theorem B1302703 : Blo 1301969 1302703 := bstep (se 1 (by rfl) ⟨977027, by rfl⟩ : syracuseStep 1302703 = 1954055) B1954055
theorem B1302727 : Blo 1301969 1302727 := bstep (se 1 (by rfl) ⟨977045, by rfl⟩ : syracuseStep 1302727 = 1954091) B1954091
theorem B1302747 : Blo 1301969 1302747 := bstep (se 1 (by rfl) ⟨977060, by rfl⟩ : syracuseStep 1302747 = 1954121) B1954121
theorem B1302823 : Blo 1301969 1302823 := bstep (se 1 (by rfl) ⟨977117, by rfl⟩ : syracuseStep 1302823 = 1954235) B1954235
theorem B1302863 : Blo 1301969 1302863 := bstep (se 1 (by rfl) ⟨977147, by rfl⟩ : syracuseStep 1302863 = 1954295) B1954295
theorem B1302879 : Blo 1301969 1302879 := bstep (se 1 (by rfl) ⟨977159, by rfl⟩ : syracuseStep 1302879 = 1954319) B1954319
theorem B7422313 : Blo 1301969 7422313 := bstep (se 2 (by rfl) ⟨2783367, by rfl⟩ : syracuseStep 7422313 = 5566735) B5566735
theorem B1302907 : Blo 1301969 1302907 := bstep (se 1 (by rfl) ⟨977180, by rfl⟩ : syracuseStep 1302907 = 1954361) B1954361
theorem B2933135 : Blo 1301969 2933135 := bstep (se 1 (by rfl) ⟨2199851, by rfl⟩ : syracuseStep 2933135 = 4399703) B4399703
theorem B2474401 : Blo 1301969 2474401 := bstep (se 2 (by rfl) ⟨927900, by rfl⟩ : syracuseStep 2474401 = 1855801) B1855801
theorem B1302959 : Blo 1301969 1302959 := bstep (se 1 (by rfl) ⟨977219, by rfl⟩ : syracuseStep 1302959 = 1954439) B1954439
theorem B2679223 : Blo 1301969 2679223 := bstep (se 1 (by rfl) ⟨2009417, by rfl⟩ : syracuseStep 2679223 = 4018835) B4018835
theorem B1302983 : Blo 1301969 1302983 := bstep (se 1 (by rfl) ⟨977237, by rfl⟩ : syracuseStep 1302983 = 1954475) B1954475
theorem B28189133 : Blo 1301969 28189133 := bstep (se 3 (by rfl) ⟨5285462, by rfl⟩ : syracuseStep 28189133 = 10570925) B10570925
theorem B1303003 : Blo 1301969 1303003 := bstep (se 1 (by rfl) ⟨977252, by rfl⟩ : syracuseStep 1303003 = 1954505) B1954505
theorem B4399649 : Blo 1301969 4399649 := bstep (se 2 (by rfl) ⟨1649868, by rfl⟩ : syracuseStep 4399649 = 3299737) B3299737
theorem B1303079 : Blo 1301969 1303079 := bstep (se 1 (by rfl) ⟨977309, by rfl⟩ : syracuseStep 1303079 = 1954619) B1954619
theorem B1303119 : Blo 1301969 1303119 := bstep (se 1 (by rfl) ⟨977339, by rfl⟩ : syracuseStep 1303119 = 1954679) B1954679
theorem B1466959 : Blo 1301969 1466959 := bstep (se 1 (by rfl) ⟨1100219, by rfl⟩ : syracuseStep 1466959 = 2200439) B2200439
theorem B1303135 : Blo 1301969 1303135 := bstep (se 1 (by rfl) ⟨977351, by rfl⟩ : syracuseStep 1303135 = 1954703) B1954703
theorem B1303163 : Blo 1301969 1303163 := bstep (se 1 (by rfl) ⟨977372, by rfl⟩ : syracuseStep 1303163 = 1954745) B1954745
theorem B5431931 : Blo 1301969 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B1303215 : Blo 1301969 1303215 := bstep (se 1 (by rfl) ⟨977411, by rfl⟩ : syracuseStep 1303215 = 1954823) B1954823
theorem B1303239 : Blo 1301969 1303239 := bstep (se 1 (by rfl) ⟨977429, by rfl⟩ : syracuseStep 1303239 = 1954859) B1954859
theorem B2933459 : Blo 1301969 2933459 := bstep (se 1 (by rfl) ⟨2200094, by rfl⟩ : syracuseStep 2933459 = 4400189) B4400189
theorem B1303259 : Blo 1301969 1303259 := bstep (se 1 (by rfl) ⟨977444, by rfl⟩ : syracuseStep 1303259 = 1954889) B1954889
theorem B4399865 : Blo 1301969 4399865 := bstep (se 2 (by rfl) ⟨1649949, by rfl⟩ : syracuseStep 4399865 = 3299899) B3299899
theorem B1303335 : Blo 1301969 1303335 := bstep (se 1 (by rfl) ⟨977501, by rfl⟩ : syracuseStep 1303335 = 1955003) B1955003
theorem B1303375 : Blo 1301969 1303375 := bstep (se 1 (by rfl) ⟨977531, by rfl⟩ : syracuseStep 1303375 = 1955063) B1955063
theorem B1303391 : Blo 1301969 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B1303419 : Blo 1301969 1303419 := bstep (se 1 (by rfl) ⟨977564, by rfl⟩ : syracuseStep 1303419 = 1955129) B1955129
theorem B1303471 : Blo 1301969 1303471 := bstep (se 1 (by rfl) ⟨977603, by rfl⟩ : syracuseStep 1303471 = 1955207) B1955207
theorem B6259639 : Blo 1301969 6259639 := bstep (se 1 (by rfl) ⟨4694729, by rfl⟩ : syracuseStep 6259639 = 9389459) B9389459
theorem B1303495 : Blo 1301969 1303495 := bstep (se 1 (by rfl) ⟨977621, by rfl⟩ : syracuseStep 1303495 = 1955243) B1955243
theorem B1303515 : Blo 1301969 1303515 := bstep (se 1 (by rfl) ⟨977636, by rfl⟩ : syracuseStep 1303515 = 1955273) B1955273
theorem B4400135 : Blo 1301969 4400135 := bstep (se 1 (by rfl) ⟨3300101, by rfl⟩ : syracuseStep 4400135 = 6600203) B6600203
theorem B1303591 : Blo 1301969 1303591 := bstep (se 1 (by rfl) ⟨977693, by rfl⟩ : syracuseStep 1303591 = 1955387) B1955387
theorem B7922767 : Blo 1301969 7922767 := bstep (se 1 (by rfl) ⟨5942075, by rfl⟩ : syracuseStep 7922767 = 11884151) B11884151
theorem B1303631 : Blo 1301969 1303631 := bstep (se 1 (by rfl) ⟨977723, by rfl⟩ : syracuseStep 1303631 = 1955447) B1955447
theorem B1303647 : Blo 1301969 1303647 := bstep (se 1 (by rfl) ⟨977735, by rfl⟩ : syracuseStep 1303647 = 1955471) B1955471
theorem B4400243 : Blo 1301969 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B1303675 : Blo 1301969 1303675 := bstep (se 1 (by rfl) ⟨977756, by rfl⟩ : syracuseStep 1303675 = 1955513) B1955513
theorem B1303727 : Blo 1301969 1303727 := bstep (se 1 (by rfl) ⟨977795, by rfl⟩ : syracuseStep 1303727 = 1955591) B1955591
theorem B1303751 : Blo 1301969 1303751 := bstep (se 1 (by rfl) ⟨977813, by rfl⟩ : syracuseStep 1303751 = 1955627) B1955627
theorem B1303771 : Blo 1301969 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B1303847 : Blo 1301969 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1303887 : Blo 1301969 1303887 := bstep (se 1 (by rfl) ⟨977915, by rfl⟩ : syracuseStep 1303887 = 1955831) B1955831
theorem B1303903 : Blo 1301969 1303903 := bstep (se 1 (by rfl) ⟨977927, by rfl⟩ : syracuseStep 1303903 = 1955855) B1955855
theorem B1303931 : Blo 1301969 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B4695421 : Blo 1301969 4695421 := bstep (se 3 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 4695421 = 1760783) B1760783
theorem B4228481 : Blo 1301969 4228481 := bstep (se 2 (by rfl) ⟨1585680, by rfl⟩ : syracuseStep 4228481 = 3171361) B3171361
theorem B4400513 : Blo 1301969 4400513 := bstep (se 2 (by rfl) ⟨1650192, by rfl⟩ : syracuseStep 4400513 = 3300385) B3300385
theorem B35661221 : Blo 1301969 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B9897389 : Blo 1301969 9897389 := bstep (se 3 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 9897389 = 3711521) B3711521
theorem B5563849 : Blo 1301969 5563849 := bstep (se 2 (by rfl) ⟨2086443, by rfl⟩ : syracuseStep 5563849 = 4172887) B4172887
theorem B33408611 : Blo 1301969 33408611 := bstep (se 1 (by rfl) ⟨25056458, by rfl⟩ : syracuseStep 33408611 = 50112917) B50112917
theorem B38078099 : Blo 1301969 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B2197435 : Blo 1301969 2197435 := bstep (se 1 (by rfl) ⟨1648076, by rfl⟩ : syracuseStep 2197435 = 3296153) B3296153
theorem B3524539 : Blo 1301969 3524539 := bstep (se 1 (by rfl) ⟨2643404, by rfl⟩ : syracuseStep 3524539 = 5286809) B5286809
theorem B1648603 : Blo 1301969 1648603 := bstep (se 1 (by rfl) ⟨1236452, by rfl⟩ : syracuseStep 1648603 = 2472905) B2472905
theorem B4950017 : Blo 1301969 4950017 := bstep (se 2 (by rfl) ⟨1856256, by rfl⟩ : syracuseStep 4950017 = 3712513) B3712513
theorem B4950031 : Blo 1301969 4950031 := bstep (se 1 (by rfl) ⟨3712523, by rfl⟩ : syracuseStep 4950031 = 7425047) B7425047
theorem B2197543 : Blo 1301969 2197543 := bstep (se 1 (by rfl) ⟨1648157, by rfl⟩ : syracuseStep 2197543 = 3296315) B3296315
theorem B16689239 : Blo 1301969 16689239 := bstep (se 1 (by rfl) ⟨12516929, by rfl⟩ : syracuseStep 16689239 = 25033859) B25033859
theorem B14084401 : Blo 1301969 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B14838065 : Blo 1301969 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B9890099 : Blo 1301969 9890099 := bstep (se 1 (by rfl) ⟨7417574, by rfl⟩ : syracuseStep 9890099 = 14835149) B14835149
theorem B2197867 : Blo 1301969 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2861455 : Blo 1301969 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B36161977 : Blo 1301969 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B4458995 : Blo 1301969 4458995 := bstep (se 1 (by rfl) ⟨3344246, by rfl⟩ : syracuseStep 4458995 = 6688493) B6688493
theorem B7039673 : Blo 1301969 7039673 := bstep (se 2 (by rfl) ⟨2639877, by rfl⟩ : syracuseStep 7039673 = 5279755) B5279755
theorem B6597449 : Blo 1301969 6597449 := bstep (se 2 (by rfl) ⟨2474043, by rfl⟩ : syracuseStep 6597449 = 4948087) B4948087
theorem B3132233 : Blo 1301969 3132233 := bstep (se 2 (by rfl) ⟨1174587, by rfl⟩ : syracuseStep 3132233 = 2349175) B2349175
theorem B14846813 : Blo 1301969 14846813 := bstep (se 3 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 14846813 = 5567555) B5567555
theorem B2378639 : Blo 1301969 2378639 := bstep (se 1 (by rfl) ⟨1783979, by rfl⟩ : syracuseStep 2378639 = 3567959) B3567959
theorem B3296335 : Blo 1301969 3296335 := bstep (se 1 (by rfl) ⟨2472251, by rfl⟩ : syracuseStep 3296335 = 4944503) B4944503
theorem B5942443 : Blo 1301969 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B7924907 : Blo 1301969 7924907 := bstep (se 1 (by rfl) ⟨5943680, by rfl⟩ : syracuseStep 7924907 = 11887361) B11887361
theorem B7040195 : Blo 1301969 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B1953017 : Blo 1301969 1953017 := bstep (se 2 (by rfl) ⟨732381, by rfl⟩ : syracuseStep 1953017 = 1464763) B1464763
theorem B1953119 : Blo 1301969 1953119 := bstep (se 1 (by rfl) ⟨1464839, by rfl⟩ : syracuseStep 1953119 = 2929679) B2929679
theorem B1953131 : Blo 1301969 1953131 := bstep (se 1 (by rfl) ⟨1464848, by rfl⟩ : syracuseStep 1953131 = 2929697) B2929697
theorem B2198927 : Blo 1301969 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B1854895 : Blo 1301969 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B7048667 : Blo 1301969 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B60182003 : Blo 1301969 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B1953359 : Blo 1301969 1953359 := bstep (se 1 (by rfl) ⟨1465019, by rfl⟩ : syracuseStep 1953359 = 2930039) B2930039
theorem B2199163 : Blo 1301969 2199163 := bstep (se 1 (by rfl) ⟨1649372, by rfl⟩ : syracuseStep 2199163 = 3298745) B3298745
theorem B4394681 : Blo 1301969 4394681 := bstep (se 2 (by rfl) ⟨1648005, by rfl⟩ : syracuseStep 4394681 = 3296011) B3296011
theorem B1953479 : Blo 1301969 1953479 := bstep (se 1 (by rfl) ⟨1465109, by rfl⟩ : syracuseStep 1953479 = 2930219) B2930219
theorem B3296983 : Blo 1301969 3296983 := bstep (se 1 (by rfl) ⟨2472737, by rfl⟩ : syracuseStep 3296983 = 4945475) B4945475
theorem B23777057 : Blo 1301969 23777057 := bstep (se 2 (by rfl) ⟨8916396, by rfl⟩ : syracuseStep 23777057 = 17832793) B17832793
theorem B9899819 : Blo 1301969 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B28159811 : Blo 1301969 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B23760707 : Blo 1301969 23760707 := bstep (se 1 (by rfl) ⟨17820530, by rfl⟩ : syracuseStep 23760707 = 35641061) B35641061
theorem B1953641 : Blo 1301969 1953641 := bstep (se 2 (by rfl) ⟨732615, by rfl⟩ : syracuseStep 1953641 = 1465231) B1465231
theorem B3862379 : Blo 1301969 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B3567521 : Blo 1301969 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B1953719 : Blo 1301969 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B1953755 : Blo 1301969 1953755 := bstep (se 1 (by rfl) ⟨1465316, by rfl⟩ : syracuseStep 1953755 = 2930633) B2930633
theorem B3297287 : Blo 1301969 3297287 := bstep (se 1 (by rfl) ⟨2472965, by rfl⟩ : syracuseStep 3297287 = 4945931) B4945931
theorem B6598745 : Blo 1301969 6598745 := bstep (se 2 (by rfl) ⟨2474529, by rfl⟩ : syracuseStep 6598745 = 4949059) B4949059
theorem B4943987 : Blo 1301969 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B4395275 : Blo 1301969 4395275 := bstep (se 1 (by rfl) ⟨3296456, by rfl⟩ : syracuseStep 4395275 = 6592913) B6592913
theorem B1954223 : Blo 1301969 1954223 := bstep (se 1 (by rfl) ⟨1465667, by rfl⟩ : syracuseStep 1954223 = 2931335) B2931335
theorem B2781659 : Blo 1301969 2781659 := bstep (se 1 (by rfl) ⟨2086244, by rfl⟩ : syracuseStep 2781659 = 4172489) B4172489
theorem B2200027 : Blo 1301969 2200027 := bstep (se 1 (by rfl) ⟨1650020, by rfl⟩ : syracuseStep 2200027 = 3300041) B3300041
theorem B1954313 : Blo 1301969 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B4395545 : Blo 1301969 4395545 := bstep (se 2 (by rfl) ⟨1648329, by rfl⟩ : syracuseStep 4395545 = 3296659) B3296659
theorem B4174361 : Blo 1301969 4174361 := bstep (se 2 (by rfl) ⟨1565385, by rfl⟩ : syracuseStep 4174361 = 3130771) B3130771
theorem B1954343 : Blo 1301969 1954343 := bstep (se 1 (by rfl) ⟨1465757, by rfl⟩ : syracuseStep 1954343 = 2931515) B2931515
theorem B1954427 : Blo 1301969 1954427 := bstep (se 1 (by rfl) ⟨1465820, by rfl⟩ : syracuseStep 1954427 = 2931641) B2931641
theorem B3388043 : Blo 1301969 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B3707603 : Blo 1301969 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B1954553 : Blo 1301969 1954553 := bstep (se 2 (by rfl) ⟨732957, by rfl⟩ : syracuseStep 1954553 = 1465915) B1465915
theorem B2929481 : Blo 1301969 2929481 := bstep (se 2 (by rfl) ⟨1098555, by rfl⟩ : syracuseStep 2929481 = 2197111) B2197111
theorem B1954655 : Blo 1301969 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B1954667 : Blo 1301969 1954667 := bstep (se 1 (by rfl) ⟨1466000, by rfl⟩ : syracuseStep 1954667 = 2932001) B2932001
theorem B3707831 : Blo 1301969 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B1954895 : Blo 1301969 1954895 := bstep (se 1 (by rfl) ⟨1466171, by rfl⟩ : syracuseStep 1954895 = 2932343) B2932343
theorem B4019279 : Blo 1301969 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B1955015 : Blo 1301969 1955015 := bstep (se 1 (by rfl) ⟨1466261, by rfl⟩ : syracuseStep 1955015 = 2932523) B2932523
theorem B2643193 : Blo 1301969 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B1955177 : Blo 1301969 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B1955255 : Blo 1301969 1955255 := bstep (se 1 (by rfl) ⟨1466441, by rfl⟩ : syracuseStep 1955255 = 2932883) B2932883
theorem B1955291 : Blo 1301969 1955291 := bstep (se 1 (by rfl) ⟨1466468, by rfl⟩ : syracuseStep 1955291 = 2932937) B2932937
theorem B5010983 : Blo 1301969 5010983 := bstep (se 1 (by rfl) ⟨3758237, by rfl⟩ : syracuseStep 5010983 = 7516475) B7516475
theorem B21116477 : Blo 1301969 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B2930273 : Blo 1301969 2930273 := bstep (se 2 (by rfl) ⟨1098852, by rfl⟩ : syracuseStep 2930273 = 2197705) B2197705
theorem B16701025 : Blo 1301969 16701025 := bstep (se 2 (by rfl) ⟨6262884, by rfl⟩ : syracuseStep 16701025 = 12525769) B12525769
theorem B4396679 : Blo 1301969 4396679 := bstep (se 1 (by rfl) ⟨3297509, by rfl⟩ : syracuseStep 4396679 = 6595019) B6595019
theorem B3708605 : Blo 1301969 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B4396733 : Blo 1301969 4396733 := bstep (se 3 (by rfl) ⟨824387, by rfl⟩ : syracuseStep 4396733 = 1648775) B1648775
theorem B4945657 : Blo 1301969 4945657 := bstep (se 2 (by rfl) ⟨1854621, by rfl⟩ : syracuseStep 4945657 = 3709243) B3709243
theorem B2086649 : Blo 1301969 2086649 := bstep (se 2 (by rfl) ⟨782493, by rfl⟩ : syracuseStep 2086649 = 1564987) B1564987
theorem B4396895 : Blo 1301969 4396895 := bstep (se 1 (by rfl) ⟨3297671, by rfl⟩ : syracuseStep 4396895 = 6595343) B6595343
theorem B5945183 : Blo 1301969 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B1955759 : Blo 1301969 1955759 := bstep (se 1 (by rfl) ⟨1466819, by rfl⟩ : syracuseStep 1955759 = 2933639) B2933639
theorem B2930615 : Blo 1301969 2930615 := bstep (se 1 (by rfl) ⟨2197961, by rfl⟩ : syracuseStep 2930615 = 4395923) B4395923
theorem B16701389 : Blo 1301969 16701389 := bstep (se 3 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 16701389 = 6263021) B6263021
theorem B4397057 : Blo 1301969 4397057 := bstep (se 2 (by rfl) ⟨1648896, by rfl⟩ : syracuseStep 4397057 = 3297793) B3297793
theorem B1955849 : Blo 1301969 1955849 := bstep (se 2 (by rfl) ⟨733443, by rfl⟩ : syracuseStep 1955849 = 1466887) B1466887
theorem B9394213 : Blo 1301969 9394213 := bstep (se 4 (by rfl) ⟨880707, by rfl⟩ : syracuseStep 9394213 = 1761415) B1761415
theorem B1955879 : Blo 1301969 1955879 := bstep (se 1 (by rfl) ⟨1466909, by rfl⟩ : syracuseStep 1955879 = 2933819) B2933819
theorem B144644237 : Blo 1301969 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B3299575 : Blo 1301969 3299575 := bstep (se 1 (by rfl) ⟨2474681, by rfl⟩ : syracuseStep 3299575 = 4949363) B4949363
theorem B17824033 : Blo 1301969 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B3709289 : Blo 1301969 3709289 := bstep (se 2 (by rfl) ⟨1390983, by rfl⟩ : syracuseStep 3709289 = 2781967) B2781967
theorem B21141911 : Blo 1301969 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B2349499 : Blo 1301969 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B2472457 : Blo 1301969 2472457 := bstep (se 2 (by rfl) ⟨927171, by rfl⟩ : syracuseStep 2472457 = 1854343) B1854343
theorem B2931209 : Blo 1301969 2931209 := bstep (se 2 (by rfl) ⟨1099203, by rfl⟩ : syracuseStep 2931209 = 2198407) B2198407
theorem B3299849 : Blo 1301969 3299849 := bstep (se 2 (by rfl) ⟨1237443, by rfl⟩ : syracuseStep 3299849 = 2474887) B2474887
theorem B1464871 : Blo 1301969 1464871 := bstep (se 1 (by rfl) ⟨1098653, by rfl⟩ : syracuseStep 1464871 = 2197307) B2197307
theorem B3299879 : Blo 1301969 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B10025531 : Blo 1301969 10025531 := bstep (se 1 (by rfl) ⟨7519148, by rfl⟩ : syracuseStep 10025531 = 15038297) B15038297
theorem B2087623 : Blo 1301969 2087623 := bstep (se 1 (by rfl) ⟨1565717, by rfl⟩ : syracuseStep 2087623 = 3131435) B3131435
theorem B2972371 : Blo 1301969 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B4397867 : Blo 1301969 4397867 := bstep (se 1 (by rfl) ⟨3298400, by rfl⟩ : syracuseStep 4397867 = 6596801) B6596801
theorem B2931551 : Blo 1301969 2931551 := bstep (se 1 (by rfl) ⟨2198663, by rfl⟩ : syracuseStep 2931551 = 4397327) B4397327
theorem B3300203 : Blo 1301969 3300203 := bstep (se 1 (by rfl) ⟨2475152, by rfl⟩ : syracuseStep 3300203 = 4950305) B4950305
theorem B3709871 : Blo 1301969 3709871 := bstep (se 1 (by rfl) ⟨2782403, by rfl⟩ : syracuseStep 3709871 = 5564807) B5564807
theorem B7420855 : Blo 1301969 7420855 := bstep (se 1 (by rfl) ⟨5565641, by rfl⟩ : syracuseStep 7420855 = 11131283) B11131283
theorem B2931731 : Blo 1301969 2931731 := bstep (se 1 (by rfl) ⟨2198798, by rfl⟩ : syracuseStep 2931731 = 4397597) B4397597
theorem B11885611 : Blo 1301969 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B4398137 : Blo 1301969 4398137 := bstep (se 2 (by rfl) ⟨1649301, by rfl⟩ : syracuseStep 4398137 = 3298603) B3298603
theorem B4947101 : Blo 1301969 4947101 := bstep (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) B1855163
theorem B4947115 : Blo 1301969 4947115 := bstep (se 1 (by rfl) ⟨3710336, by rfl⟩ : syracuseStep 4947115 = 7420673) B7420673
theorem B2932073 : Blo 1301969 2932073 := bstep (se 2 (by rfl) ⟨1099527, by rfl⟩ : syracuseStep 2932073 = 2199055) B2199055
theorem B4398461 : Blo 1301969 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B2473391 : Blo 1301969 2473391 := bstep (se 1 (by rfl) ⟨1855043, by rfl⟩ : syracuseStep 2473391 = 3710087) B3710087
theorem B1301979 : Blo 1301969 1301979 := bstep (se 1 (by rfl) ⟨976484, by rfl⟩ : syracuseStep 1301979 = 1952969) B1952969
theorem B4947419 : Blo 1301969 4947419 := bstep (se 1 (by rfl) ⟨3710564, by rfl⟩ : syracuseStep 4947419 = 7421129) B7421129
theorem B1302055 : Blo 1301969 1302055 := bstep (se 1 (by rfl) ⟨976541, by rfl⟩ : syracuseStep 1302055 = 1953083) B1953083
theorem B1302095 : Blo 1301969 1302095 := bstep (se 1 (by rfl) ⟨976571, by rfl⟩ : syracuseStep 1302095 = 1953143) B1953143
theorem B14270039 : Blo 1301969 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B1302111 : Blo 1301969 1302111 := bstep (se 1 (by rfl) ⟨976583, by rfl⟩ : syracuseStep 1302111 = 1953167) B1953167
theorem B1302139 : Blo 1301969 1302139 := bstep (se 1 (by rfl) ⟨976604, by rfl⟩ : syracuseStep 1302139 = 1953209) B1953209
theorem B4398731 : Blo 1301969 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B1302191 : Blo 1301969 1302191 := bstep (se 1 (by rfl) ⟨976643, by rfl⟩ : syracuseStep 1302191 = 1953287) B1953287
theorem B1302215 : Blo 1301969 1302215 := bstep (se 1 (by rfl) ⟨976661, by rfl⟩ : syracuseStep 1302215 = 1953323) B1953323
theorem B1302235 : Blo 1301969 1302235 := bstep (se 1 (by rfl) ⟨976676, by rfl⟩ : syracuseStep 1302235 = 1953353) B1953353
theorem B1302311 : Blo 1301969 1302311 := bstep (se 1 (by rfl) ⟨976733, by rfl⟩ : syracuseStep 1302311 = 1953467) B1953467
theorem B6594371 : Blo 1301969 6594371 := bstep (se 1 (by rfl) ⟨4945778, by rfl⟩ : syracuseStep 6594371 = 9891557) B9891557
theorem B1302351 : Blo 1301969 1302351 := bstep (se 1 (by rfl) ⟨976763, by rfl⟩ : syracuseStep 1302351 = 1953527) B1953527
theorem B1302367 : Blo 1301969 1302367 := bstep (se 1 (by rfl) ⟨976775, by rfl⟩ : syracuseStep 1302367 = 1953551) B1953551
theorem B1302395 : Blo 1301969 1302395 := bstep (se 1 (by rfl) ⟨976796, by rfl⟩ : syracuseStep 1302395 = 1953593) B1953593
theorem B1302447 : Blo 1301969 1302447 := bstep (se 1 (by rfl) ⟨976835, by rfl⟩ : syracuseStep 1302447 = 1953671) B1953671
theorem B2473915 : Blo 1301969 2473915 := bstep (se 1 (by rfl) ⟨1855436, by rfl⟩ : syracuseStep 2473915 = 3710873) B3710873
theorem B2932667 : Blo 1301969 2932667 := bstep (se 1 (by rfl) ⟨2199500, by rfl⟩ : syracuseStep 2932667 = 4399001) B4399001
theorem B1302471 : Blo 1301969 1302471 := bstep (se 1 (by rfl) ⟨976853, by rfl⟩ : syracuseStep 1302471 = 1953707) B1953707
theorem B1302491 : Blo 1301969 1302491 := bstep (se 1 (by rfl) ⟨976868, by rfl⟩ : syracuseStep 1302491 = 1953737) B1953737
theorem B12525617 : Blo 1301969 12525617 := bstep (se 2 (by rfl) ⟨4697106, by rfl⟩ : syracuseStep 12525617 = 9394213) B9394213
theorem B4399163 : Blo 1301969 4399163 := bstep (se 1 (by rfl) ⟨3299372, by rfl⟩ : syracuseStep 4399163 = 6598745) B6598745
theorem B21119075 : Blo 1301969 21119075 := bstep (se 1 (by rfl) ⟨15839306, by rfl⟩ : syracuseStep 21119075 = 31678613) B31678613
theorem B4948073 : Blo 1301969 4948073 := bstep (se 2 (by rfl) ⟨1855527, by rfl⟩ : syracuseStep 4948073 = 3711055) B3711055
theorem B1302815 : Blo 1301969 1302815 := bstep (se 1 (by rfl) ⟨977111, by rfl⟩ : syracuseStep 1302815 = 1954223) B1954223
theorem B18792755 : Blo 1301969 18792755 := bstep (se 1 (by rfl) ⟨14094566, by rfl⟩ : syracuseStep 18792755 = 28189133) B28189133
theorem B4399433 : Blo 1301969 4399433 := bstep (se 2 (by rfl) ⟨1649787, by rfl⟩ : syracuseStep 4399433 = 3299575) B3299575
theorem B1302875 : Blo 1301969 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B2933099 : Blo 1301969 2933099 := bstep (se 1 (by rfl) ⟨2199824, by rfl⟩ : syracuseStep 2933099 = 4399649) B4399649
theorem B1302895 : Blo 1301969 1302895 := bstep (se 1 (by rfl) ⟨977171, by rfl⟩ : syracuseStep 1302895 = 1954343) B1954343
theorem B1302951 : Blo 1301969 1302951 := bstep (se 1 (by rfl) ⟨977213, by rfl⟩ : syracuseStep 1302951 = 1954427) B1954427
theorem B3621287 : Blo 1301969 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B9896417 : Blo 1301969 9896417 := bstep (se 2 (by rfl) ⟨3711156, by rfl⟩ : syracuseStep 9896417 = 7422313) B7422313
theorem B1303035 : Blo 1301969 1303035 := bstep (se 1 (by rfl) ⟨977276, by rfl⟩ : syracuseStep 1303035 = 1954553) B1954553
theorem B2933243 : Blo 1301969 2933243 := bstep (se 1 (by rfl) ⟨2199932, by rfl⟩ : syracuseStep 2933243 = 4399865) B4399865
theorem B1303103 : Blo 1301969 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B1303111 : Blo 1301969 1303111 := bstep (se 1 (by rfl) ⟨977333, by rfl⟩ : syracuseStep 1303111 = 1954667) B1954667
theorem B3572297 : Blo 1301969 3572297 := bstep (se 2 (by rfl) ⟨1339611, by rfl⟩ : syracuseStep 3572297 = 2679223) B2679223
theorem B2933369 : Blo 1301969 2933369 := bstep (se 2 (by rfl) ⟨1100013, by rfl⟩ : syracuseStep 2933369 = 2200027) B2200027
theorem B2933423 : Blo 1301969 2933423 := bstep (se 1 (by rfl) ⟨2200067, by rfl⟩ : syracuseStep 2933423 = 4400135) B4400135
theorem B1303263 : Blo 1301969 1303263 := bstep (se 1 (by rfl) ⟨977447, by rfl⟩ : syracuseStep 1303263 = 1954895) B1954895
theorem B2933495 : Blo 1301969 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B1303343 : Blo 1301969 1303343 := bstep (se 1 (by rfl) ⟨977507, by rfl⟩ : syracuseStep 1303343 = 1955015) B1955015
theorem B1303451 : Blo 1301969 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B2933675 : Blo 1301969 2933675 := bstep (se 1 (by rfl) ⟨2200256, by rfl⟩ : syracuseStep 2933675 = 4400513) B4400513
theorem B23774147 : Blo 1301969 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B1303503 : Blo 1301969 1303503 := bstep (se 1 (by rfl) ⟨977627, by rfl⟩ : syracuseStep 1303503 = 1955255) B1955255
theorem B1303527 : Blo 1301969 1303527 := bstep (se 1 (by rfl) ⟨977645, by rfl⟩ : syracuseStep 1303527 = 1955291) B1955291
theorem B1303839 : Blo 1301969 1303839 := bstep (se 1 (by rfl) ⟨977879, by rfl⟩ : syracuseStep 1303839 = 1955759) B1955759
theorem B11134259 : Blo 1301969 11134259 := bstep (se 1 (by rfl) ⟨8350694, by rfl⟩ : syracuseStep 11134259 = 16701389) B16701389
theorem B1303899 : Blo 1301969 1303899 := bstep (se 1 (by rfl) ⟨977924, by rfl⟩ : syracuseStep 1303899 = 1955849) B1955849
theorem B1303919 : Blo 1301969 1303919 := bstep (se 1 (by rfl) ⟨977939, by rfl⟩ : syracuseStep 1303919 = 1955879) B1955879
theorem B11126159 : Blo 1301969 11126159 := bstep (se 1 (by rfl) ⟨8344619, by rfl⟩ : syracuseStep 11126159 = 16689239) B16689239
theorem B96429491 : Blo 1301969 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B95061509 : Blo 1301969 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B7923257 : Blo 1301969 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B6596153 : Blo 1301969 6596153 := bstep (se 2 (by rfl) ⟨2473557, by rfl⟩ : syracuseStep 6596153 = 4947115) B4947115
theorem B3524257 : Blo 1301969 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B9889613 : Blo 1301969 9889613 := bstep (se 3 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 9889613 = 3708605) B3708605
theorem B6260561 : Blo 1301969 6260561 := bstep (se 2 (by rfl) ⟨2347710, by rfl⟩ : syracuseStep 6260561 = 4695421) B4695421
theorem B9897875 : Blo 1301969 9897875 := bstep (se 1 (by rfl) ⟨7423406, by rfl⟩ : syracuseStep 9897875 = 14846813) B14846813
theorem B22268033 : Blo 1301969 22268033 := bstep (se 2 (by rfl) ⟨8350512, by rfl⟩ : syracuseStep 22268033 = 16701025) B16701025
theorem B1648927 : Blo 1301969 1648927 := bstep (se 1 (by rfl) ⟨1236695, by rfl⟩ : syracuseStep 1648927 = 2473391) B2473391
theorem B9513359 : Blo 1301969 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B9513389 : Blo 1301969 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B2574919 : Blo 1301969 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B2198137 : Blo 1301969 2198137 := bstep (se 2 (by rfl) ⟨824301, by rfl⟩ : syracuseStep 2198137 = 1648603) B1648603
theorem B2198191 : Blo 1301969 2198191 := bstep (se 1 (by rfl) ⟨1648643, by rfl⟩ : syracuseStep 2198191 = 3297287) B3297287
theorem B3295991 : Blo 1301969 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B5286647 : Blo 1301969 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B10718077 : Blo 1301969 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B18779201 : Blo 1301969 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B1952987 : Blo 1301969 1952987 := bstep (se 1 (by rfl) ⟨1464740, by rfl⟩ : syracuseStep 1952987 = 2929481) B2929481
theorem B3132665 : Blo 1301969 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B3296609 : Blo 1301969 3296609 := bstep (se 2 (by rfl) ⟨1236228, by rfl⟩ : syracuseStep 3296609 = 2472457) B2472457
theorem B1953161 : Blo 1301969 1953161 := bstep (se 2 (by rfl) ⟨732435, by rfl⟩ : syracuseStep 1953161 = 1464871) B1464871
theorem B6598259 : Blo 1301969 6598259 := bstep (se 1 (by rfl) ⟨4948694, by rfl⟩ : syracuseStep 6598259 = 9897389) B9897389
theorem B11275949 : Blo 1301969 11275949 := bstep (se 3 (by rfl) ⟨2114240, by rfl⟩ : syracuseStep 11275949 = 4228481) B4228481
theorem B14077651 : Blo 1301969 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B1953515 : Blo 1301969 1953515 := bstep (se 1 (by rfl) ⟨1465136, by rfl⟩ : syracuseStep 1953515 = 2930273) B2930273
theorem B7417757 : Blo 1301969 7417757 := bstep (se 3 (by rfl) ⟨1390829, by rfl⟩ : syracuseStep 7417757 = 2781659) B2781659
theorem B18796445 : Blo 1301969 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B1953743 : Blo 1301969 1953743 := bstep (se 1 (by rfl) ⟨1465307, by rfl⟩ : syracuseStep 1953743 = 2930615) B2930615
theorem B15847481 : Blo 1301969 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B4395113 : Blo 1301969 4395113 := bstep (se 2 (by rfl) ⟨1648167, by rfl⟩ : syracuseStep 4395113 = 3296335) B3296335
theorem B10563689 : Blo 1301969 10563689 := bstep (se 2 (by rfl) ⟨3961383, by rfl⟩ : syracuseStep 10563689 = 7922767) B7922767
theorem B9892043 : Blo 1301969 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B14094607 : Blo 1301969 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B1954139 : Blo 1301969 1954139 := bstep (se 1 (by rfl) ⟨1465604, by rfl⟩ : syracuseStep 1954139 = 2931209) B2931209
theorem B2199899 : Blo 1301969 2199899 := bstep (se 1 (by rfl) ⟨1649924, by rfl⟩ : syracuseStep 2199899 = 3299849) B3299849
theorem B2199919 : Blo 1301969 2199919 := bstep (se 1 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 2199919 = 3299879) B3299879
theorem B1954367 : Blo 1301969 1954367 := bstep (se 1 (by rfl) ⟨1465775, by rfl⟩ : syracuseStep 1954367 = 2931551) B2931551
theorem B2200135 : Blo 1301969 2200135 := bstep (se 1 (by rfl) ⟨1650101, by rfl⟩ : syracuseStep 2200135 = 3300203) B3300203
theorem B1585759 : Blo 1301969 1585759 := bstep (se 1 (by rfl) ⟨1189319, by rfl⟩ : syracuseStep 1585759 = 2378639) B2378639
theorem B7418465 : Blo 1301969 7418465 := bstep (se 2 (by rfl) ⟨2781924, by rfl⟩ : syracuseStep 7418465 = 5563849) B5563849
theorem B1954487 : Blo 1301969 1954487 := bstep (se 1 (by rfl) ⟨1465865, by rfl⟩ : syracuseStep 1954487 = 2931731) B2931731
theorem B3298067 : Blo 1301969 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B63361885 : Blo 1301969 63361885 := bstep (se 3 (by rfl) ⟨11880353, by rfl⟩ : syracuseStep 63361885 = 23760707) B23760707
theorem B1954715 : Blo 1301969 1954715 := bstep (se 1 (by rfl) ⟨1466036, by rfl⟩ : syracuseStep 1954715 = 2932073) B2932073
theorem B4395977 : Blo 1301969 4395977 := bstep (se 2 (by rfl) ⟨1648491, by rfl⟩ : syracuseStep 4395977 = 3296983) B3296983
theorem B3298279 : Blo 1301969 3298279 := bstep (se 1 (by rfl) ⟨2473709, by rfl⟩ : syracuseStep 3298279 = 4947419) B4947419
theorem B40121335 : Blo 1301969 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B2929787 : Blo 1301969 2929787 := bstep (se 1 (by rfl) ⟨2197340, by rfl⟩ : syracuseStep 2929787 = 4394681) B4394681
theorem B6599879 : Blo 1301969 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B18773207 : Blo 1301969 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B4396247 : Blo 1301969 4396247 := bstep (se 1 (by rfl) ⟨3297185, by rfl⟩ : syracuseStep 4396247 = 6594371) B6594371
theorem B2929913 : Blo 1301969 2929913 := bstep (se 2 (by rfl) ⟨1098717, by rfl⟩ : syracuseStep 2929913 = 2197435) B2197435
theorem B3298553 : Blo 1301969 3298553 := bstep (se 2 (by rfl) ⟨1236957, by rfl⟩ : syracuseStep 3298553 = 2473915) B2473915
theorem B4699385 : Blo 1301969 4699385 := bstep (se 2 (by rfl) ⟨1762269, by rfl⟩ : syracuseStep 4699385 = 3524539) B3524539
theorem B1955111 : Blo 1301969 1955111 := bstep (se 1 (by rfl) ⟨1466333, by rfl⟩ : syracuseStep 1955111 = 2932667) B2932667
theorem B6600041 : Blo 1301969 6600041 := bstep (se 2 (by rfl) ⟨2475015, by rfl⟩ : syracuseStep 6600041 = 4950031) B4950031
theorem B1955195 : Blo 1301969 1955195 := bstep (se 1 (by rfl) ⟨1466396, by rfl⟩ : syracuseStep 1955195 = 2932793) B2932793
theorem B2930057 : Blo 1301969 2930057 := bstep (se 2 (by rfl) ⟨1098771, by rfl⟩ : syracuseStep 2930057 = 2197543) B2197543
theorem B2086393 : Blo 1301969 2086393 := bstep (se 2 (by rfl) ⟨782397, by rfl⟩ : syracuseStep 2086393 = 1564795) B1564795
theorem B1955321 : Blo 1301969 1955321 := bstep (se 2 (by rfl) ⟨733245, by rfl⟩ : syracuseStep 1955321 = 1466491) B1466491
theorem B2930183 : Blo 1301969 2930183 := bstep (se 1 (by rfl) ⟨2197637, by rfl⟩ : syracuseStep 2930183 = 4395275) B4395275
theorem B1955423 : Blo 1301969 1955423 := bstep (se 1 (by rfl) ⟨1466567, by rfl⟩ : syracuseStep 1955423 = 2933135) B2933135
theorem B2930363 : Blo 1301969 2930363 := bstep (se 1 (by rfl) ⟨2197772, by rfl⟩ : syracuseStep 2930363 = 4395545) B4395545
theorem B2782907 : Blo 1301969 2782907 := bstep (se 1 (by rfl) ⟨2087180, by rfl⟩ : syracuseStep 2782907 = 4174361) B4174361
theorem B2258695 : Blo 1301969 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B2471735 : Blo 1301969 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B1955639 : Blo 1301969 1955639 := bstep (se 1 (by rfl) ⟨1466729, by rfl⟩ : syracuseStep 1955639 = 2933459) B2933459
theorem B2930489 : Blo 1301969 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B3815273 : Blo 1301969 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B3299201 : Blo 1301969 3299201 := bstep (se 2 (by rfl) ⟨1237200, by rfl⟩ : syracuseStep 3299201 = 2474401) B2474401
theorem B48215969 : Blo 1301969 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B2471887 : Blo 1301969 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B1955945 : Blo 1301969 1955945 := bstep (se 2 (by rfl) ⟨733479, by rfl⟩ : syracuseStep 1955945 = 1466959) B1466959
theorem B2783497 : Blo 1301969 2783497 := bstep (se 2 (by rfl) ⟨1043811, by rfl⟩ : syracuseStep 2783497 = 2087623) B2087623
theorem B3963161 : Blo 1301969 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B3340655 : Blo 1301969 3340655 := bstep (se 1 (by rfl) ⟨2505491, by rfl⟩ : syracuseStep 3340655 = 5010983) B5010983
theorem B22272407 : Blo 1301969 22272407 := bstep (se 1 (by rfl) ⟨16704305, by rfl⟩ : syracuseStep 22272407 = 33408611) B33408611
theorem B2931119 : Blo 1301969 2931119 := bstep (se 1 (by rfl) ⟨2198339, by rfl⟩ : syracuseStep 2931119 = 4396679) B4396679
theorem B25385399 : Blo 1301969 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B2931155 : Blo 1301969 2931155 := bstep (se 1 (by rfl) ⟨2198366, by rfl⟩ : syracuseStep 2931155 = 4396733) B4396733
theorem B1391099 : Blo 1301969 1391099 := bstep (se 1 (by rfl) ⟨1043324, by rfl⟩ : syracuseStep 1391099 = 2086649) B2086649
theorem B2931263 : Blo 1301969 2931263 := bstep (se 1 (by rfl) ⟨2198447, by rfl⟩ : syracuseStep 2931263 = 4396895) B4396895
theorem B3963455 : Blo 1301969 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B8346185 : Blo 1301969 8346185 := bstep (se 2 (by rfl) ⟨3129819, by rfl⟩ : syracuseStep 8346185 = 6259639) B6259639
theorem B9894473 : Blo 1301969 9894473 := bstep (se 2 (by rfl) ⟨3710427, by rfl⟩ : syracuseStep 9894473 = 7420855) B7420855
theorem B2931371 : Blo 1301969 2931371 := bstep (se 1 (by rfl) ⟨2198528, by rfl⟩ : syracuseStep 2931371 = 4397057) B4397057
theorem B3300011 : Blo 1301969 3300011 := bstep (se 1 (by rfl) ⟨2475008, by rfl⟩ : syracuseStep 3300011 = 4950017) B4950017
theorem B6593399 : Blo 1301969 6593399 := bstep (se 1 (by rfl) ⟨4945049, by rfl⟩ : syracuseStep 6593399 = 9890099) B9890099
theorem B2472859 : Blo 1301969 2472859 := bstep (se 1 (by rfl) ⟨1854644, by rfl⟩ : syracuseStep 2472859 = 3709289) B3709289
theorem B2972663 : Blo 1301969 2972663 := bstep (se 1 (by rfl) ⟨2229497, by rfl⟩ : syracuseStep 2972663 = 4458995) B4458995
theorem B6683687 : Blo 1301969 6683687 := bstep (se 1 (by rfl) ⟨5012765, by rfl⟩ : syracuseStep 6683687 = 10025531) B10025531
theorem B4693115 : Blo 1301969 4693115 := bstep (se 1 (by rfl) ⟨3519836, by rfl⟩ : syracuseStep 4693115 = 7039673) B7039673
theorem B2931911 : Blo 1301969 2931911 := bstep (se 1 (by rfl) ⟨2198933, by rfl⟩ : syracuseStep 2931911 = 4397867) B4397867
theorem B4398299 : Blo 1301969 4398299 := bstep (se 1 (by rfl) ⟨3298724, by rfl⟩ : syracuseStep 4398299 = 6597449) B6597449
theorem B2088155 : Blo 1301969 2088155 := bstep (se 1 (by rfl) ⟨1566116, by rfl⟩ : syracuseStep 2088155 = 3132233) B3132233
theorem B2473193 : Blo 1301969 2473193 := bstep (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) B1854895
theorem B2473247 : Blo 1301969 2473247 := bstep (se 1 (by rfl) ⟨1854935, by rfl⟩ : syracuseStep 2473247 = 3709871) B3709871
theorem B2932091 : Blo 1301969 2932091 := bstep (se 1 (by rfl) ⟨2199068, by rfl⟩ : syracuseStep 2932091 = 4398137) B4398137
theorem B5283271 : Blo 1301969 5283271 := bstep (se 1 (by rfl) ⟨3962453, by rfl⟩ : syracuseStep 5283271 = 7924907) B7924907
theorem B4693463 : Blo 1301969 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B2932217 : Blo 1301969 2932217 := bstep (se 2 (by rfl) ⟨1099581, by rfl⟩ : syracuseStep 2932217 = 2199163) B2199163
theorem B1302011 : Blo 1301969 1302011 := bstep (se 1 (by rfl) ⟨976508, by rfl⟩ : syracuseStep 1302011 = 1953017) B1953017
theorem B1302079 : Blo 1301969 1302079 := bstep (se 1 (by rfl) ⟨976559, by rfl⟩ : syracuseStep 1302079 = 1953119) B1953119
theorem B1302087 : Blo 1301969 1302087 := bstep (se 1 (by rfl) ⟨976565, by rfl⟩ : syracuseStep 1302087 = 1953131) B1953131
theorem B2932307 : Blo 1301969 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B1465951 : Blo 1301969 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B6594209 : Blo 1301969 6594209 := bstep (se 2 (by rfl) ⟨2472828, by rfl⟩ : syracuseStep 6594209 = 4945657) B4945657
theorem B1302239 : Blo 1301969 1302239 := bstep (se 1 (by rfl) ⟨976679, by rfl⟩ : syracuseStep 1302239 = 1953359) B1953359
theorem B2932487 : Blo 1301969 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B1302319 : Blo 1301969 1302319 := bstep (se 1 (by rfl) ⟨976739, by rfl⟩ : syracuseStep 1302319 = 1953479) B1953479
theorem B15851371 : Blo 1301969 15851371 := bstep (se 1 (by rfl) ⟨11888528, by rfl⟩ : syracuseStep 15851371 = 23777057) B23777057
theorem B1302427 : Blo 1301969 1302427 := bstep (se 1 (by rfl) ⟨976820, by rfl⟩ : syracuseStep 1302427 = 1953641) B1953641
theorem B1302479 : Blo 1301969 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B1302503 : Blo 1301969 1302503 := bstep (se 1 (by rfl) ⟨976877, by rfl⟩ : syracuseStep 1302503 = 1953755) B1953755
theorem B2932775 : Blo 1301969 2932775 := bstep (se 1 (by rfl) ⟨2199581, by rfl⟩ : syracuseStep 2932775 = 4399163) B4399163
theorem B6594695 : Blo 1301969 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B2932955 : Blo 1301969 2932955 := bstep (se 1 (by rfl) ⟨2199716, by rfl⟩ : syracuseStep 2932955 = 4399433) B4399433
theorem B1302759 : Blo 1301969 1302759 := bstep (se 1 (by rfl) ⟨977069, by rfl⟩ : syracuseStep 1302759 = 1954139) B1954139
theorem B1466599 : Blo 1301969 1466599 := bstep (se 1 (by rfl) ⟨1099949, by rfl⟩ : syracuseStep 1466599 = 2199899) B2199899
theorem B3711329 : Blo 1301969 3711329 := bstep (se 2 (by rfl) ⟨1391748, by rfl⟩ : syracuseStep 3711329 = 2783497) B2783497
theorem B18792809 : Blo 1301969 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B1302911 : Blo 1301969 1302911 := bstep (se 1 (by rfl) ⟨977183, by rfl⟩ : syracuseStep 1302911 = 1954367) B1954367
theorem B1302991 : Blo 1301969 1302991 := bstep (se 1 (by rfl) ⟨977243, by rfl⟩ : syracuseStep 1302991 = 1954487) B1954487
theorem B2933225 : Blo 1301969 2933225 := bstep (se 2 (by rfl) ⟨1099959, by rfl⟩ : syracuseStep 2933225 = 2199919) B2199919
theorem B1303143 : Blo 1301969 1303143 := bstep (se 1 (by rfl) ⟨977357, by rfl⟩ : syracuseStep 1303143 = 1954715) B1954715
theorem B6595181 : Blo 1301969 6595181 := bstep (se 3 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 6595181 = 2473193) B2473193
theorem B2933513 : Blo 1301969 2933513 := bstep (se 2 (by rfl) ⟨1100067, by rfl⟩ : syracuseStep 2933513 = 2200135) B2200135
theorem B2114345 : Blo 1301969 2114345 := bstep (se 2 (by rfl) ⟨792879, by rfl⟩ : syracuseStep 2114345 = 1585759) B1585759
theorem B4399919 : Blo 1301969 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B1303407 : Blo 1301969 1303407 := bstep (se 1 (by rfl) ⟨977555, by rfl⟩ : syracuseStep 1303407 = 1955111) B1955111
theorem B7422839 : Blo 1301969 7422839 := bstep (se 1 (by rfl) ⟨5567129, by rfl⟩ : syracuseStep 7422839 = 11134259) B11134259
theorem B4400027 : Blo 1301969 4400027 := bstep (se 1 (by rfl) ⟨3300020, by rfl⟩ : syracuseStep 4400027 = 6600041) B6600041
theorem B1303463 : Blo 1301969 1303463 := bstep (se 1 (by rfl) ⟨977597, by rfl⟩ : syracuseStep 1303463 = 1955195) B1955195
theorem B1303547 : Blo 1301969 1303547 := bstep (se 1 (by rfl) ⟨977660, by rfl⟩ : syracuseStep 1303547 = 1955321) B1955321
theorem B63374339 : Blo 1301969 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B1303615 : Blo 1301969 1303615 := bstep (se 1 (by rfl) ⟨977711, by rfl⟩ : syracuseStep 1303615 = 1955423) B1955423
theorem B1303759 : Blo 1301969 1303759 := bstep (se 1 (by rfl) ⟨977819, by rfl⟩ : syracuseStep 1303759 = 1955639) B1955639
theorem B53495113 : Blo 1301969 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B1303963 : Blo 1301969 1303963 := bstep (se 1 (by rfl) ⟨977972, by rfl⟩ : syracuseStep 1303963 = 1955945) B1955945
theorem B14845355 : Blo 1301969 14845355 := bstep (se 1 (by rfl) ⟨11134016, by rfl⟩ : syracuseStep 14845355 = 22268033) B22268033
theorem B6342239 : Blo 1301969 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B6342259 : Blo 1301969 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B5564123 : Blo 1301969 5564123 := bstep (se 1 (by rfl) ⟨4173092, by rfl⟩ : syracuseStep 5564123 = 8346185) B8346185
theorem B6596315 : Blo 1301969 6596315 := bstep (se 1 (by rfl) ⟨4947236, by rfl⟩ : syracuseStep 6596315 = 9894473) B9894473
theorem B2197327 : Blo 1301969 2197327 := bstep (se 1 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 2197327 = 3295991) B3295991
theorem B3524431 : Blo 1301969 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B12519467 : Blo 1301969 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B1648831 : Blo 1301969 1648831 := bstep (se 1 (by rfl) ⟨1236623, by rfl⟩ : syracuseStep 1648831 = 2473247) B2473247
theorem B2197739 : Blo 1301969 2197739 := bstep (se 1 (by rfl) ⟨1648304, by rfl⟩ : syracuseStep 2197739 = 3296609) B3296609
theorem B18770201 : Blo 1301969 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B3295849 : Blo 1301969 3295849 := bstep (se 2 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 3295849 = 2471887) B2471887
theorem B8350411 : Blo 1301969 8350411 := bstep (se 1 (by rfl) ⟨6262808, by rfl⟩ : syracuseStep 8350411 = 12525617) B12525617
theorem B12528503 : Blo 1301969 12528503 := bstep (se 1 (by rfl) ⟨9396377, by rfl⟩ : syracuseStep 12528503 = 18792755) B18792755
theorem B6597611 : Blo 1301969 6597611 := bstep (se 1 (by rfl) ⟨4948208, by rfl⟩ : syracuseStep 6597611 = 9896417) B9896417
theorem B13732901 : Blo 1301969 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B2198569 : Blo 1301969 2198569 := bstep (se 2 (by rfl) ⟨824463, by rfl⟩ : syracuseStep 2198569 = 1648927) B1648927
theorem B2198711 : Blo 1301969 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B1953191 : Blo 1301969 1953191 := bstep (se 1 (by rfl) ⟨1464893, by rfl⟩ : syracuseStep 1953191 = 2929787) B2929787
theorem B1953275 : Blo 1301969 1953275 := bstep (se 1 (by rfl) ⟨1464956, by rfl⟩ : syracuseStep 1953275 = 2929913) B2929913
theorem B2199035 : Blo 1301969 2199035 := bstep (se 1 (by rfl) ⟨1649276, by rfl⟩ : syracuseStep 2199035 = 3298553) B3298553
theorem B3132923 : Blo 1301969 3132923 := bstep (se 1 (by rfl) ⟨2349692, by rfl⟩ : syracuseStep 3132923 = 4699385) B4699385
theorem B1953371 : Blo 1301969 1953371 := bstep (se 1 (by rfl) ⟨1465028, by rfl⟩ : syracuseStep 1953371 = 2930057) B2930057
theorem B7417439 : Blo 1301969 7417439 := bstep (se 1 (by rfl) ⟨5563079, by rfl⟩ : syracuseStep 7417439 = 11126159) B11126159
theorem B64286327 : Blo 1301969 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B1953455 : Blo 1301969 1953455 := bstep (se 1 (by rfl) ⟨1465091, by rfl⟩ : syracuseStep 1953455 = 2930183) B2930183
theorem B1953575 : Blo 1301969 1953575 := bstep (se 1 (by rfl) ⟨1465181, by rfl⟩ : syracuseStep 1953575 = 2930363) B2930363
theorem B1855271 : Blo 1301969 1855271 := bstep (se 1 (by rfl) ⟨1391453, by rfl⟩ : syracuseStep 1855271 = 2782907) B2782907
theorem B14290769 : Blo 1301969 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B3297145 : Blo 1301969 3297145 := bstep (se 2 (by rfl) ⟨1236429, by rfl⟩ : syracuseStep 3297145 = 2472859) B2472859
theorem B1953659 : Blo 1301969 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B4173707 : Blo 1301969 4173707 := bstep (se 1 (by rfl) ⟨3130280, by rfl⟩ : syracuseStep 4173707 = 6260561) B6260561
theorem B2199467 : Blo 1301969 2199467 := bstep (se 1 (by rfl) ⟨1649600, by rfl⟩ : syracuseStep 2199467 = 3299201) B3299201
theorem B6598583 : Blo 1301969 6598583 := bstep (se 1 (by rfl) ⟨4948937, by rfl⟩ : syracuseStep 6598583 = 9897875) B9897875
theorem B12046373 : Blo 1301969 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B2642107 : Blo 1301969 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B14848271 : Blo 1301969 14848271 := bstep (se 1 (by rfl) ⟨11136203, by rfl⟩ : syracuseStep 14848271 = 22272407) B22272407
theorem B1954079 : Blo 1301969 1954079 := bstep (se 1 (by rfl) ⟨1465559, by rfl⟩ : syracuseStep 1954079 = 2931119) B2931119
theorem B1954103 : Blo 1301969 1954103 := bstep (se 1 (by rfl) ⟨1465577, by rfl⟩ : syracuseStep 1954103 = 2931155) B2931155
theorem B1954175 : Blo 1301969 1954175 := bstep (se 1 (by rfl) ⟨1465631, by rfl⟩ : syracuseStep 1954175 = 2931263) B2931263
theorem B2642303 : Blo 1301969 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B1954247 : Blo 1301969 1954247 := bstep (se 1 (by rfl) ⟨1465685, by rfl⟩ : syracuseStep 1954247 = 2931371) B2931371
theorem B2200007 : Blo 1301969 2200007 := bstep (se 1 (by rfl) ⟨1650005, by rfl⟩ : syracuseStep 2200007 = 3300011) B3300011
theorem B4395599 : Blo 1301969 4395599 := bstep (se 1 (by rfl) ⟨3296699, by rfl⟩ : syracuseStep 4395599 = 6593399) B6593399
theorem B2781857 : Blo 1301969 2781857 := bstep (se 2 (by rfl) ⟨1043196, by rfl⟩ : syracuseStep 2781857 = 2086393) B2086393
theorem B1954601 : Blo 1301969 1954601 := bstep (se 2 (by rfl) ⟨732975, by rfl⟩ : syracuseStep 1954601 = 1465951) B1465951
theorem B1954607 : Blo 1301969 1954607 := bstep (se 1 (by rfl) ⟨1465955, by rfl⟩ : syracuseStep 1954607 = 2931911) B2931911
theorem B6591293 : Blo 1301969 6591293 := bstep (se 3 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 6591293 = 2471735) B2471735
theorem B4699009 : Blo 1301969 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B1954727 : Blo 1301969 1954727 := bstep (se 1 (by rfl) ⟨1466045, by rfl⟩ : syracuseStep 1954727 = 2932091) B2932091
theorem B1954811 : Blo 1301969 1954811 := bstep (se 1 (by rfl) ⟨1466108, by rfl⟩ : syracuseStep 1954811 = 2932217) B2932217
theorem B28177445 : Blo 1301969 28177445 := bstep (se 4 (by rfl) ⟨2641635, by rfl⟩ : syracuseStep 28177445 = 5283271) B5283271
theorem B1954871 : Blo 1301969 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B4396139 : Blo 1301969 4396139 := bstep (se 1 (by rfl) ⟨3297104, by rfl⟩ : syracuseStep 4396139 = 6594209) B6594209
theorem B7517299 : Blo 1301969 7517299 := bstep (se 1 (by rfl) ⟨5637974, by rfl⟩ : syracuseStep 7517299 = 11275949) B11275949
theorem B1954991 : Blo 1301969 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B4945171 : Blo 1301969 4945171 := bstep (se 1 (by rfl) ⟨3708878, by rfl⟩ : syracuseStep 4945171 = 7417757) B7417757
theorem B12530963 : Blo 1301969 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B10564987 : Blo 1301969 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B14079383 : Blo 1301969 14079383 := bstep (se 1 (by rfl) ⟨10559537, by rfl⟩ : syracuseStep 14079383 = 21119075) B21119075
theorem B2930075 : Blo 1301969 2930075 := bstep (se 1 (by rfl) ⟨2197556, by rfl⟩ : syracuseStep 2930075 = 4395113) B4395113
theorem B7042459 : Blo 1301969 7042459 := bstep (se 1 (by rfl) ⟨5281844, by rfl⟩ : syracuseStep 7042459 = 10563689) B10563689
theorem B3298715 : Blo 1301969 3298715 := bstep (se 1 (by rfl) ⟨2474036, by rfl⟩ : syracuseStep 3298715 = 4948073) B4948073
theorem B1955399 : Blo 1301969 1955399 := bstep (se 1 (by rfl) ⟨1466549, by rfl⟩ : syracuseStep 1955399 = 2933099) B2933099
theorem B2414191 : Blo 1301969 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B1955495 : Blo 1301969 1955495 := bstep (se 1 (by rfl) ⟨1466621, by rfl⟩ : syracuseStep 1955495 = 2933243) B2933243
theorem B2381531 : Blo 1301969 2381531 := bstep (se 1 (by rfl) ⟨1786148, by rfl⟩ : syracuseStep 2381531 = 3572297) B3572297
theorem B4945643 : Blo 1301969 4945643 := bstep (se 1 (by rfl) ⟨3709232, by rfl⟩ : syracuseStep 4945643 = 7418465) B7418465
theorem B1955579 : Blo 1301969 1955579 := bstep (se 1 (by rfl) ⟨1466684, by rfl⟩ : syracuseStep 1955579 = 2933369) B2933369
theorem B1955615 : Blo 1301969 1955615 := bstep (se 1 (by rfl) ⟨1466711, by rfl⟩ : syracuseStep 1955615 = 2933423) B2933423
theorem B1955663 : Blo 1301969 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B1955783 : Blo 1301969 1955783 := bstep (se 1 (by rfl) ⟨1466837, by rfl⟩ : syracuseStep 1955783 = 2933675) B2933675
theorem B15849431 : Blo 1301969 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B2930651 : Blo 1301969 2930651 := bstep (se 1 (by rfl) ⟨2197988, by rfl⟩ : syracuseStep 2930651 = 4395977) B4395977
theorem B12515471 : Blo 1301969 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B2930831 : Blo 1301969 2930831 := bstep (se 1 (by rfl) ⟨2198123, by rfl⟩ : syracuseStep 2930831 = 4396247) B4396247
theorem B2930849 : Blo 1301969 2930849 := bstep (se 2 (by rfl) ⟨1099068, by rfl⟩ : syracuseStep 2930849 = 2198137) B2198137
theorem B2930921 : Blo 1301969 2930921 := bstep (se 2 (by rfl) ⟨1099095, by rfl⟩ : syracuseStep 2930921 = 2198191) B2198191
theorem B5282171 : Blo 1301969 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B4397435 : Blo 1301969 4397435 := bstep (se 1 (by rfl) ⟨3298076, by rfl⟩ : syracuseStep 4397435 = 6596153) B6596153
theorem B84482513 : Blo 1301969 84482513 := bstep (se 2 (by rfl) ⟨31680942, by rfl⟩ : syracuseStep 84482513 = 63361885) B63361885
theorem B6593075 : Blo 1301969 6593075 := bstep (se 1 (by rfl) ⟨4944806, by rfl⟩ : syracuseStep 6593075 = 9889613) B9889613
theorem B32143979 : Blo 1301969 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B4397705 : Blo 1301969 4397705 := bstep (se 2 (by rfl) ⟨1649139, by rfl⟩ : syracuseStep 4397705 = 3298279) B3298279
theorem B3709597 : Blo 1301969 3709597 := bstep (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) B1391099
theorem B2227103 : Blo 1301969 2227103 := bstep (se 1 (by rfl) ⟨1670327, by rfl⟩ : syracuseStep 2227103 = 3340655) B3340655
theorem B16923599 : Blo 1301969 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B1981775 : Blo 1301969 1981775 := bstep (se 1 (by rfl) ⟨1486331, by rfl⟩ : syracuseStep 1981775 = 2972663) B2972663
theorem B4455791 : Blo 1301969 4455791 := bstep (se 1 (by rfl) ⟨3341843, by rfl⟩ : syracuseStep 4455791 = 6683687) B6683687
theorem B3128743 : Blo 1301969 3128743 := bstep (se 1 (by rfl) ⟨2346557, by rfl⟩ : syracuseStep 3128743 = 4693115) B4693115
theorem B1301991 : Blo 1301969 1301991 := bstep (se 1 (by rfl) ⟨976493, by rfl⟩ : syracuseStep 1301991 = 1952987) B1952987
theorem B2932199 : Blo 1301969 2932199 := bstep (se 1 (by rfl) ⟨2199149, by rfl⟩ : syracuseStep 2932199 = 4398299) B4398299
theorem B1392103 : Blo 1301969 1392103 := bstep (se 1 (by rfl) ⟨1044077, by rfl⟩ : syracuseStep 1392103 = 2088155) B2088155
theorem B2088443 : Blo 1301969 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B1302107 : Blo 1301969 1302107 := bstep (se 1 (by rfl) ⟨976580, by rfl⟩ : syracuseStep 1302107 = 1953161) B1953161
theorem B10174061 : Blo 1301969 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B3128975 : Blo 1301969 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B4398839 : Blo 1301969 4398839 := bstep (se 1 (by rfl) ⟨3299129, by rfl⟩ : syracuseStep 4398839 = 6598259) B6598259
theorem B21135161 : Blo 1301969 21135161 := bstep (se 2 (by rfl) ⟨7925685, by rfl⟩ : syracuseStep 21135161 = 15851371) B15851371
theorem B1302343 : Blo 1301969 1302343 := bstep (se 1 (by rfl) ⟨976757, by rfl⟩ : syracuseStep 1302343 = 1953515) B1953515
theorem B1302495 : Blo 1301969 1302495 := bstep (se 1 (by rfl) ⟨976871, by rfl⟩ : syracuseStep 1302495 = 1953743) B1953743
theorem B1302719 : Blo 1301969 1302719 := bstep (se 1 (by rfl) ⟨977039, by rfl⟩ : syracuseStep 1302719 = 1954079) B1954079
theorem B1302735 : Blo 1301969 1302735 := bstep (se 1 (by rfl) ⟨977051, by rfl⟩ : syracuseStep 1302735 = 1954103) B1954103
theorem B2474219 : Blo 1301969 2474219 := bstep (se 1 (by rfl) ⟨1855664, by rfl⟩ : syracuseStep 2474219 = 3711329) B3711329
theorem B3522809 : Blo 1301969 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B1302783 : Blo 1301969 1302783 := bstep (se 1 (by rfl) ⟨977087, by rfl⟩ : syracuseStep 1302783 = 1954175) B1954175
theorem B1761535 : Blo 1301969 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B1302831 : Blo 1301969 1302831 := bstep (se 1 (by rfl) ⟨977123, by rfl⟩ : syracuseStep 1302831 = 1954247) B1954247
theorem B1466671 : Blo 1301969 1466671 := bstep (se 1 (by rfl) ⟨1100003, by rfl⟩ : syracuseStep 1466671 = 2200007) B2200007
theorem B1303067 : Blo 1301969 1303067 := bstep (se 1 (by rfl) ⟨977300, by rfl⟩ : syracuseStep 1303067 = 1954601) B1954601
theorem B1303071 : Blo 1301969 1303071 := bstep (se 1 (by rfl) ⟨977303, by rfl⟩ : syracuseStep 1303071 = 1954607) B1954607
theorem B2933279 : Blo 1301969 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B4948559 : Blo 1301969 4948559 := bstep (se 1 (by rfl) ⟨3711419, by rfl⟩ : syracuseStep 4948559 = 7422839) B7422839
theorem B2933351 : Blo 1301969 2933351 := bstep (se 1 (by rfl) ⟨2200013, by rfl⟩ : syracuseStep 2933351 = 4400027) B4400027
theorem B1303151 : Blo 1301969 1303151 := bstep (se 1 (by rfl) ⟨977363, by rfl⟩ : syracuseStep 1303151 = 1954727) B1954727
theorem B1303207 : Blo 1301969 1303207 := bstep (se 1 (by rfl) ⟨977405, by rfl⟩ : syracuseStep 1303207 = 1954811) B1954811
theorem B18784963 : Blo 1301969 18784963 := bstep (se 1 (by rfl) ⟨14088722, by rfl⟩ : syracuseStep 18784963 = 28177445) B28177445
theorem B1303247 : Blo 1301969 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B1303327 : Blo 1301969 1303327 := bstep (se 1 (by rfl) ⟨977495, by rfl⟩ : syracuseStep 1303327 = 1954991) B1954991
theorem B11133881 : Blo 1301969 11133881 := bstep (se 2 (by rfl) ⟨4175205, by rfl⟩ : syracuseStep 11133881 = 8350411) B8350411
theorem B9896903 : Blo 1301969 9896903 := bstep (se 1 (by rfl) ⟨7422677, by rfl⟩ : syracuseStep 9896903 = 14845355) B14845355
theorem B1303599 : Blo 1301969 1303599 := bstep (se 1 (by rfl) ⟨977699, by rfl⟩ : syracuseStep 1303599 = 1955399) B1955399
theorem B4228159 : Blo 1301969 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B1303663 : Blo 1301969 1303663 := bstep (se 1 (by rfl) ⟨977747, by rfl⟩ : syracuseStep 1303663 = 1955495) B1955495
theorem B1303719 : Blo 1301969 1303719 := bstep (se 1 (by rfl) ⟨977789, by rfl⟩ : syracuseStep 1303719 = 1955579) B1955579
theorem B1303743 : Blo 1301969 1303743 := bstep (se 1 (by rfl) ⟨977807, by rfl⟩ : syracuseStep 1303743 = 1955615) B1955615
theorem B1303775 : Blo 1301969 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B1303855 : Blo 1301969 1303855 := bstep (se 1 (by rfl) ⟨977891, by rfl⟩ : syracuseStep 1303855 = 1955783) B1955783
theorem B56321675 : Blo 1301969 56321675 := bstep (se 1 (by rfl) ⟨42241256, by rfl⟩ : syracuseStep 56321675 = 84482513) B84482513
theorem B9389945 : Blo 1301969 9389945 := bstep (se 2 (by rfl) ⟨3521229, by rfl⟩ : syracuseStep 9389945 = 7042459) B7042459
theorem B4171657 : Blo 1301969 4171657 := bstep (se 2 (by rfl) ⟨1564371, by rfl⟩ : syracuseStep 4171657 = 3128743) B3128743
theorem B1484735 : Blo 1301969 1484735 := bstep (se 1 (by rfl) ⟨1113551, by rfl⟩ : syracuseStep 1484735 = 2227103) B2227103
theorem B11282399 : Blo 1301969 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B5638253 : Blo 1301969 5638253 := bstep (se 3 (by rfl) ⟨1057172, by rfl⟩ : syracuseStep 5638253 = 2114345) B2114345
theorem B8456345 : Blo 1301969 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B1321183 : Blo 1301969 1321183 := bstep (se 1 (by rfl) ⟨990887, by rfl⟩ : syracuseStep 1321183 = 1981775) B1981775
theorem B8030915 : Blo 1301969 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B9898847 : Blo 1301969 9898847 := bstep (se 1 (by rfl) ⟨7424135, by rfl⟩ : syracuseStep 9898847 = 14848271) B14848271
theorem B12528539 : Blo 1301969 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B2198441 : Blo 1301969 2198441 := bstep (se 2 (by rfl) ⟨824415, by rfl⟩ : syracuseStep 2198441 = 1648831) B1648831
theorem B1854571 : Blo 1301969 1854571 := bstep (se 1 (by rfl) ⟨1390928, by rfl⟩ : syracuseStep 1854571 = 2781857) B2781857
theorem B4394195 : Blo 1301969 4394195 := bstep (se 1 (by rfl) ⟨3295646, by rfl⟩ : syracuseStep 4394195 = 6591293) B6591293
theorem B4394465 : Blo 1301969 4394465 := bstep (se 2 (by rfl) ⟨1647924, by rfl⟩ : syracuseStep 4394465 = 3295849) B3295849
theorem B1953383 : Blo 1301969 1953383 := bstep (se 1 (by rfl) ⟨1465037, by rfl⟩ : syracuseStep 1953383 = 2930075) B2930075
theorem B2199143 : Blo 1301969 2199143 := bstep (se 1 (by rfl) ⟨1649357, by rfl⟩ : syracuseStep 2199143 = 3298715) B3298715
theorem B3297095 : Blo 1301969 3297095 := bstep (se 1 (by rfl) ⟨2472821, by rfl⟩ : syracuseStep 3297095 = 4945643) B4945643
theorem B1953767 : Blo 1301969 1953767 := bstep (se 1 (by rfl) ⟨1465325, by rfl⟩ : syracuseStep 1953767 = 2930651) B2930651
theorem B8343647 : Blo 1301969 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B1953887 : Blo 1301969 1953887 := bstep (se 1 (by rfl) ⟨1465415, by rfl⟩ : syracuseStep 1953887 = 2930831) B2930831
theorem B1953899 : Blo 1301969 1953899 := bstep (se 1 (by rfl) ⟨1465424, by rfl⟩ : syracuseStep 1953899 = 2930849) B2930849
theorem B10023065 : Blo 1301969 10023065 := bstep (se 2 (by rfl) ⟨3758649, by rfl⟩ : syracuseStep 10023065 = 7517299) B7517299
theorem B1953947 : Blo 1301969 1953947 := bstep (se 1 (by rfl) ⟨1465460, by rfl⟩ : syracuseStep 1953947 = 2930921) B2930921
theorem B12513467 : Blo 1301969 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B4395383 : Blo 1301969 4395383 := bstep (se 1 (by rfl) ⟨3296537, by rfl⟩ : syracuseStep 4395383 = 6593075) B6593075
theorem B14086649 : Blo 1301969 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B8352335 : Blo 1301969 8352335 := bstep (se 1 (by rfl) ⟨6264251, by rfl⟩ : syracuseStep 8352335 = 12528503) B12528503
theorem B1856137 : Blo 1301969 1856137 := bstep (se 2 (by rfl) ⟨696051, by rfl⟩ : syracuseStep 1856137 = 1392103) B1392103
theorem B9155267 : Blo 1301969 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B2970527 : Blo 1301969 2970527 := bstep (se 1 (by rfl) ⟨2227895, by rfl⟩ : syracuseStep 2970527 = 4455791) B4455791
theorem B1954799 : Blo 1301969 1954799 := bstep (se 1 (by rfl) ⟨1466099, by rfl⟩ : syracuseStep 1954799 = 2932199) B2932199
theorem B11129885 : Blo 1301969 11129885 := bstep (se 3 (by rfl) ⟨2086853, by rfl⟩ : syracuseStep 11129885 = 4173707) B4173707
theorem B4944959 : Blo 1301969 4944959 := bstep (se 1 (by rfl) ⟨3708719, by rfl⟩ : syracuseStep 4944959 = 7417439) B7417439
theorem B42857551 : Blo 1301969 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B2085983 : Blo 1301969 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B2929769 : Blo 1301969 2929769 := bstep (se 2 (by rfl) ⟨1098663, by rfl⟩ : syracuseStep 2929769 = 2197327) B2197327
theorem B4699241 : Blo 1301969 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B4396193 : Blo 1301969 4396193 := bstep (se 2 (by rfl) ⟨1648572, by rfl⟩ : syracuseStep 4396193 = 3297145) B3297145
theorem B168998237 : Blo 1301969 168998237 := bstep (se 3 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 168998237 = 63374339) B63374339
theorem B1955183 : Blo 1301969 1955183 := bstep (se 1 (by rfl) ⟨1466387, by rfl⟩ : syracuseStep 1955183 = 2932775) B2932775
theorem B4396463 : Blo 1301969 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1955303 : Blo 1301969 1955303 := bstep (se 1 (by rfl) ⟨1466477, by rfl⟩ : syracuseStep 1955303 = 2932955) B2932955
theorem B1955465 : Blo 1301969 1955465 := bstep (se 2 (by rfl) ⟨733299, by rfl⟩ : syracuseStep 1955465 = 1466599) B1466599
theorem B1955483 : Blo 1301969 1955483 := bstep (se 1 (by rfl) ⟨1466612, by rfl⟩ : syracuseStep 1955483 = 2933225) B2933225
theorem B2930399 : Blo 1301969 2930399 := bstep (se 1 (by rfl) ⟨2197799, by rfl⟩ : syracuseStep 2930399 = 4395599) B4395599
theorem B4396787 : Blo 1301969 4396787 := bstep (se 1 (by rfl) ⟨3297590, by rfl⟩ : syracuseStep 4396787 = 6595181) B6595181
theorem B1955675 : Blo 1301969 1955675 := bstep (se 1 (by rfl) ⟨1466756, by rfl⟩ : syracuseStep 1955675 = 2933513) B2933513
theorem B2930759 : Blo 1301969 2930759 := bstep (se 1 (by rfl) ⟨2198069, by rfl⟩ : syracuseStep 2930759 = 4396139) B4396139
theorem B8353975 : Blo 1301969 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B4946129 : Blo 1301969 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B9386255 : Blo 1301969 9386255 := bstep (se 1 (by rfl) ⟨7039691, by rfl⟩ : syracuseStep 9386255 = 14079383) B14079383
theorem B3709415 : Blo 1301969 3709415 := bstep (se 1 (by rfl) ⟨2782061, by rfl⟩ : syracuseStep 3709415 = 5564123) B5564123
theorem B4397543 : Blo 1301969 4397543 := bstep (se 1 (by rfl) ⟨3298157, by rfl⟩ : syracuseStep 4397543 = 6596315) B6596315
theorem B6265345 : Blo 1301969 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B10566287 : Blo 1301969 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B5569181 : Blo 1301969 5569181 := bstep (se 3 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 5569181 = 2088443) B2088443
theorem B8354461 : Blo 1301969 8354461 := bstep (se 3 (by rfl) ⟨1566461, by rfl⟩ : syracuseStep 8354461 = 3132923) B3132923
theorem B8346311 : Blo 1301969 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B2931425 : Blo 1301969 2931425 := bstep (se 2 (by rfl) ⟨1099284, by rfl⟩ : syracuseStep 2931425 = 2198569) B2198569
theorem B1465159 : Blo 1301969 1465159 := bstep (se 1 (by rfl) ⟨1098869, by rfl⟩ : syracuseStep 1465159 = 2197739) B2197739
theorem B3521447 : Blo 1301969 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B2931623 : Blo 1301969 2931623 := bstep (se 1 (by rfl) ⟨2198717, by rfl⟩ : syracuseStep 2931623 = 4397435) B4397435
theorem B6593561 : Blo 1301969 6593561 := bstep (se 2 (by rfl) ⟨2472585, by rfl⟩ : syracuseStep 6593561 = 4945171) B4945171
theorem B21429319 : Blo 1301969 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B2931803 : Blo 1301969 2931803 := bstep (se 1 (by rfl) ⟨2198852, by rfl⟩ : syracuseStep 2931803 = 4397705) B4397705
theorem B71326817 : Blo 1301969 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B4398407 : Blo 1301969 4398407 := bstep (se 1 (by rfl) ⟨3298805, by rfl⟩ : syracuseStep 4398407 = 6597611) B6597611
theorem B4947389 : Blo 1301969 4947389 := bstep (se 3 (by rfl) ⟨927635, by rfl⟩ : syracuseStep 4947389 = 1855271) B1855271
theorem B1465807 : Blo 1301969 1465807 := bstep (se 1 (by rfl) ⟨1099355, by rfl⟩ : syracuseStep 1465807 = 2198711) B2198711
theorem B3218921 : Blo 1301969 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B38108717 : Blo 1301969 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B1302127 : Blo 1301969 1302127 := bstep (se 1 (by rfl) ⟨976595, by rfl⟩ : syracuseStep 1302127 = 1953191) B1953191
theorem B25402997 : Blo 1301969 25402997 := bstep (se 5 (by rfl) ⟨1190765, by rfl⟩ : syracuseStep 25402997 = 2381531) B2381531
theorem B1302183 : Blo 1301969 1302183 := bstep (se 1 (by rfl) ⟨976637, by rfl⟩ : syracuseStep 1302183 = 1953275) B1953275
theorem B1466023 : Blo 1301969 1466023 := bstep (se 1 (by rfl) ⟨1099517, by rfl⟩ : syracuseStep 1466023 = 2199035) B2199035
theorem B1302247 : Blo 1301969 1302247 := bstep (se 1 (by rfl) ⟨976685, by rfl⟩ : syracuseStep 1302247 = 1953371) B1953371
theorem B6782707 : Blo 1301969 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B1302303 : Blo 1301969 1302303 := bstep (se 1 (by rfl) ⟨976727, by rfl⟩ : syracuseStep 1302303 = 1953455) B1953455
theorem B2932559 : Blo 1301969 2932559 := bstep (se 1 (by rfl) ⟨2199419, by rfl⟩ : syracuseStep 2932559 = 4398839) B4398839
theorem B1302383 : Blo 1301969 1302383 := bstep (se 1 (by rfl) ⟨976787, by rfl⟩ : syracuseStep 1302383 = 1953575) B1953575
theorem B14090107 : Blo 1301969 14090107 := bstep (se 1 (by rfl) ⟨10567580, by rfl⟩ : syracuseStep 14090107 = 21135161) B21135161
theorem B1302439 : Blo 1301969 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B1466311 : Blo 1301969 1466311 := bstep (se 1 (by rfl) ⟨1099733, by rfl⟩ : syracuseStep 1466311 = 2199467) B2199467
theorem B4399055 : Blo 1301969 4399055 := bstep (se 1 (by rfl) ⟨3299291, by rfl⟩ : syracuseStep 4399055 = 6598583) B6598583
theorem B5562431 : Blo 1301969 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B1302591 : Blo 1301969 1302591 := bstep (se 1 (by rfl) ⟨976943, by rfl⟩ : syracuseStep 1302591 = 1953887) B1953887
theorem B1302599 : Blo 1301969 1302599 := bstep (se 1 (by rfl) ⟨976949, by rfl⟩ : syracuseStep 1302599 = 1953899) B1953899
theorem B1302631 : Blo 1301969 1302631 := bstep (se 1 (by rfl) ⟨976973, by rfl⟩ : syracuseStep 1302631 = 1953947) B1953947
theorem B228573605 : Blo 1301969 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B6103511 : Blo 1301969 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B7422587 : Blo 1301969 7422587 := bstep (se 1 (by rfl) ⟨5566940, by rfl⟩ : syracuseStep 7422587 = 11133881) B11133881
theorem B1303199 : Blo 1301969 1303199 := bstep (se 1 (by rfl) ⟨977399, by rfl⟩ : syracuseStep 1303199 = 1954799) B1954799
theorem B2474849 : Blo 1301969 2474849 := bstep (se 2 (by rfl) ⟨928068, by rfl⟩ : syracuseStep 2474849 = 1856137) B1856137
theorem B112665491 : Blo 1301969 112665491 := bstep (se 1 (by rfl) ⟨84499118, by rfl⟩ : syracuseStep 112665491 = 168998237) B168998237
theorem B1303455 : Blo 1301969 1303455 := bstep (se 1 (by rfl) ⟨977591, by rfl⟩ : syracuseStep 1303455 = 1955183) B1955183
theorem B1303535 : Blo 1301969 1303535 := bstep (se 1 (by rfl) ⟨977651, by rfl⟩ : syracuseStep 1303535 = 1955303) B1955303
theorem B1303643 : Blo 1301969 1303643 := bstep (se 1 (by rfl) ⟨977732, by rfl⟩ : syracuseStep 1303643 = 1955465) B1955465
theorem B1303655 : Blo 1301969 1303655 := bstep (se 1 (by rfl) ⟨977741, by rfl⟩ : syracuseStep 1303655 = 1955483) B1955483
theorem B7046309 : Blo 1301969 7046309 := bstep (se 4 (by rfl) ⟨660591, by rfl⟩ : syracuseStep 7046309 = 1321183) B1321183
theorem B1303783 : Blo 1301969 1303783 := bstep (se 1 (by rfl) ⟨977837, by rfl⟩ : syracuseStep 1303783 = 1955675) B1955675
theorem B7521599 : Blo 1301969 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B5637545 : Blo 1301969 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B5637563 : Blo 1301969 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B3712787 : Blo 1301969 3712787 := bstep (se 1 (by rfl) ⟨2784590, by rfl⟩ : syracuseStep 3712787 = 5569181) B5569181
theorem B5564207 : Blo 1301969 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B25405811 : Blo 1301969 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B16935331 : Blo 1301969 16935331 := bstep (se 1 (by rfl) ⟨12701498, by rfl⟩ : syracuseStep 16935331 = 25402997) B25402997
theorem B18786809 : Blo 1301969 18786809 := bstep (se 2 (by rfl) ⟨7045053, by rfl⟩ : syracuseStep 18786809 = 14090107) B14090107
theorem B3959293 : Blo 1301969 3959293 := bstep (se 3 (by rfl) ⟨742367, by rfl⟩ : syracuseStep 3959293 = 1484735) B1484735
theorem B2198063 : Blo 1301969 2198063 := bstep (se 1 (by rfl) ⟨1648547, by rfl⟩ : syracuseStep 2198063 = 3297095) B3297095
theorem B1649479 : Blo 1301969 1649479 := bstep (se 1 (by rfl) ⟨1237109, by rfl⟩ : syracuseStep 1649479 = 2474219) B2474219
theorem B15035341 : Blo 1301969 15035341 := bstep (se 3 (by rfl) ⟨2819126, by rfl⟩ : syracuseStep 15035341 = 5638253) B5638253
theorem B9391099 : Blo 1301969 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B33369245 : Blo 1301969 33369245 := bstep (se 3 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 33369245 = 12513467) B12513467
theorem B6597935 : Blo 1301969 6597935 := bstep (se 1 (by rfl) ⟨4948451, by rfl⟩ : syracuseStep 6597935 = 9896903) B9896903
theorem B3296639 : Blo 1301969 3296639 := bstep (se 1 (by rfl) ⟨2472479, by rfl⟩ : syracuseStep 3296639 = 4944959) B4944959
theorem B1953179 : Blo 1301969 1953179 := bstep (se 1 (by rfl) ⟨1464884, by rfl⟩ : syracuseStep 1953179 = 2929769) B2929769
theorem B3132827 : Blo 1301969 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B25046617 : Blo 1301969 25046617 := bstep (se 2 (by rfl) ⟨9392481, by rfl⟩ : syracuseStep 25046617 = 18784963) B18784963
theorem B37547783 : Blo 1301969 37547783 := bstep (se 1 (by rfl) ⟨28160837, by rfl⟩ : syracuseStep 37547783 = 56321675) B56321675
theorem B1953545 : Blo 1301969 1953545 := bstep (se 2 (by rfl) ⟨732579, by rfl⟩ : syracuseStep 1953545 = 1465159) B1465159
theorem B1953599 : Blo 1301969 1953599 := bstep (se 1 (by rfl) ⟨1465199, by rfl⟩ : syracuseStep 1953599 = 2930399) B2930399
theorem B1953839 : Blo 1301969 1953839 := bstep (se 1 (by rfl) ⟨1465379, by rfl⟩ : syracuseStep 1953839 = 2930759) B2930759
theorem B3297419 : Blo 1301969 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B5353943 : Blo 1301969 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B1954283 : Blo 1301969 1954283 := bstep (se 1 (by rfl) ⟨1465712, by rfl⟩ : syracuseStep 1954283 = 2931425) B2931425
theorem B6599231 : Blo 1301969 6599231 := bstep (se 1 (by rfl) ⟨4949423, by rfl⟩ : syracuseStep 6599231 = 9898847) B9898847
theorem B8352359 : Blo 1301969 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B1954409 : Blo 1301969 1954409 := bstep (se 2 (by rfl) ⟨732903, by rfl⟩ : syracuseStep 1954409 = 1465807) B1465807
theorem B2347631 : Blo 1301969 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B1954415 : Blo 1301969 1954415 := bstep (se 1 (by rfl) ⟨1465811, by rfl⟩ : syracuseStep 1954415 = 2931623) B2931623
theorem B4395707 : Blo 1301969 4395707 := bstep (se 1 (by rfl) ⟨3296780, by rfl⟩ : syracuseStep 4395707 = 6593561) B6593561
theorem B1954535 : Blo 1301969 1954535 := bstep (se 1 (by rfl) ⟨1465901, by rfl⟩ : syracuseStep 1954535 = 2931803) B2931803
theorem B47551211 : Blo 1301969 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B2929463 : Blo 1301969 2929463 := bstep (se 1 (by rfl) ⟨2197097, by rfl⟩ : syracuseStep 2929463 = 4394195) B4394195
theorem B1954697 : Blo 1301969 1954697 := bstep (se 2 (by rfl) ⟨733011, by rfl⟩ : syracuseStep 1954697 = 1466023) B1466023
theorem B3298259 : Blo 1301969 3298259 := bstep (se 1 (by rfl) ⟨2473694, by rfl⟩ : syracuseStep 3298259 = 4947389) B4947389
theorem B2929643 : Blo 1301969 2929643 := bstep (se 1 (by rfl) ⟨2197232, by rfl⟩ : syracuseStep 2929643 = 4394465) B4394465
theorem B25039853 : Blo 1301969 25039853 := bstep (se 3 (by rfl) ⟨4694972, by rfl⟩ : syracuseStep 25039853 = 9389945) B9389945
theorem B1955039 : Blo 1301969 1955039 := bstep (se 1 (by rfl) ⟨1466279, by rfl⟩ : syracuseStep 1955039 = 2932559) B2932559
theorem B1955081 : Blo 1301969 1955081 := bstep (se 2 (by rfl) ⟨733155, by rfl⟩ : syracuseStep 1955081 = 1466311) B1466311
theorem B6682043 : Blo 1301969 6682043 := bstep (se 1 (by rfl) ⟨5011532, by rfl⟩ : syracuseStep 6682043 = 10023065) B10023065
theorem B11138633 : Blo 1301969 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B2930255 : Blo 1301969 2930255 := bstep (se 1 (by rfl) ⟨2197691, by rfl⟩ : syracuseStep 2930255 = 4395383) B4395383
theorem B2348713 : Blo 1301969 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B1955519 : Blo 1301969 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B3299039 : Blo 1301969 3299039 := bstep (se 1 (by rfl) ⟨2474279, by rfl⟩ : syracuseStep 3299039 = 4948559) B4948559
theorem B5568223 : Blo 1301969 5568223 := bstep (se 1 (by rfl) ⟨4176167, by rfl⟩ : syracuseStep 5568223 = 8352335) B8352335
theorem B1955561 : Blo 1301969 1955561 := bstep (se 2 (by rfl) ⟨733335, by rfl⟩ : syracuseStep 1955561 = 1466671) B1466671
theorem B1955567 : Blo 1301969 1955567 := bstep (se 1 (by rfl) ⟨1466675, by rfl⟩ : syracuseStep 1955567 = 2933351) B2933351
theorem B9394157 : Blo 1301969 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B8353793 : Blo 1301969 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B7419923 : Blo 1301969 7419923 := bstep (se 1 (by rfl) ⟨5564942, by rfl⟩ : syracuseStep 7419923 = 11129885) B11129885
theorem B1390655 : Blo 1301969 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B2930795 : Blo 1301969 2930795 := bstep (se 1 (by rfl) ⟨2198096, by rfl⟩ : syracuseStep 2930795 = 4396193) B4396193
theorem B11139281 : Blo 1301969 11139281 := bstep (se 2 (by rfl) ⟨4177230, by rfl⟩ : syracuseStep 11139281 = 8354461) B8354461
theorem B2930975 : Blo 1301969 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B2931191 : Blo 1301969 2931191 := bstep (se 1 (by rfl) ⟨2198393, by rfl⟩ : syracuseStep 2931191 = 4396787) B4396787
theorem B36174437 : Blo 1301969 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B28572425 : Blo 1301969 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B2472761 : Blo 1301969 2472761 := bstep (se 2 (by rfl) ⟨927285, by rfl⟩ : syracuseStep 2472761 = 1854571) B1854571
theorem B6257503 : Blo 1301969 6257503 := bstep (se 1 (by rfl) ⟨4693127, by rfl⟩ : syracuseStep 6257503 = 9386255) B9386255
theorem B2472943 : Blo 1301969 2472943 := bstep (se 1 (by rfl) ⟨1854707, by rfl⟩ : syracuseStep 2472943 = 3709415) B3709415
theorem B2931695 : Blo 1301969 2931695 := bstep (se 1 (by rfl) ⟨2198771, by rfl⟩ : syracuseStep 2931695 = 4397543) B4397543
theorem B7044191 : Blo 1301969 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B1465627 : Blo 1301969 1465627 := bstep (se 1 (by rfl) ⟨1099220, by rfl⟩ : syracuseStep 1465627 = 2198441) B2198441
theorem B2932271 : Blo 1301969 2932271 := bstep (se 1 (by rfl) ⟨2199203, by rfl⟩ : syracuseStep 2932271 = 4398407) B4398407
theorem B2145947 : Blo 1301969 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B1302255 : Blo 1301969 1302255 := bstep (se 1 (by rfl) ⟨976691, by rfl⟩ : syracuseStep 1302255 = 1953383) B1953383
theorem B1466095 : Blo 1301969 1466095 := bstep (se 1 (by rfl) ⟨1099571, by rfl⟩ : syracuseStep 1466095 = 2199143) B2199143
theorem B7921405 : Blo 1301969 7921405 := bstep (se 3 (by rfl) ⟨1485263, by rfl⟩ : syracuseStep 7921405 = 2970527) B2970527
theorem B5562209 : Blo 1301969 5562209 := bstep (se 2 (by rfl) ⟨2085828, by rfl⟩ : syracuseStep 5562209 = 4171657) B4171657
theorem B2932703 : Blo 1301969 2932703 := bstep (se 1 (by rfl) ⟨2199527, by rfl⟩ : syracuseStep 2932703 = 4399055) B4399055
theorem B1302511 : Blo 1301969 1302511 := bstep (se 1 (by rfl) ⟨976883, by rfl⟩ : syracuseStep 1302511 = 1953767) B1953767
theorem B1302559 : Blo 1301969 1302559 := bstep (se 1 (by rfl) ⟨976919, by rfl⟩ : syracuseStep 1302559 = 1953839) B1953839
theorem B1302855 : Blo 1301969 1302855 := bstep (se 1 (by rfl) ⟨977141, by rfl⟩ : syracuseStep 1302855 = 1954283) B1954283
theorem B4399487 : Blo 1301969 4399487 := bstep (se 1 (by rfl) ⟨3299615, by rfl⟩ : syracuseStep 4399487 = 6599231) B6599231
theorem B1302939 : Blo 1301969 1302939 := bstep (se 1 (by rfl) ⟨977204, by rfl⟩ : syracuseStep 1302939 = 1954409) B1954409
theorem B1565087 : Blo 1301969 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B1302943 : Blo 1301969 1302943 := bstep (se 1 (by rfl) ⟨977207, by rfl⟩ : syracuseStep 1302943 = 1954415) B1954415
theorem B4948391 : Blo 1301969 4948391 := bstep (se 1 (by rfl) ⟨3711293, by rfl⟩ : syracuseStep 4948391 = 7422587) B7422587
theorem B1303023 : Blo 1301969 1303023 := bstep (se 1 (by rfl) ⟨977267, by rfl⟩ : syracuseStep 1303023 = 1954535) B1954535
theorem B1303131 : Blo 1301969 1303131 := bstep (se 1 (by rfl) ⟨977348, by rfl⟩ : syracuseStep 1303131 = 1954697) B1954697
theorem B1303359 : Blo 1301969 1303359 := bstep (se 1 (by rfl) ⟨977519, by rfl⟩ : syracuseStep 1303359 = 1955039) B1955039
theorem B1303387 : Blo 1301969 1303387 := bstep (se 1 (by rfl) ⟨977540, by rfl⟩ : syracuseStep 1303387 = 1955081) B1955081
theorem B5014399 : Blo 1301969 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B1303679 : Blo 1301969 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B1303707 : Blo 1301969 1303707 := bstep (se 1 (by rfl) ⟨977780, by rfl⟩ : syracuseStep 1303707 = 1955561) B1955561
theorem B1303711 : Blo 1301969 1303711 := bstep (se 1 (by rfl) ⟨977783, by rfl⟩ : syracuseStep 1303711 = 1955567) B1955567
theorem B2475191 : Blo 1301969 2475191 := bstep (se 1 (by rfl) ⟨1856393, by rfl⟩ : syracuseStep 2475191 = 3712787) B3712787
theorem B20047121 : Blo 1301969 20047121 := bstep (se 2 (by rfl) ⟨7517670, by rfl⟩ : syracuseStep 20047121 = 15035341) B15035341
theorem B19048283 : Blo 1301969 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B1648507 : Blo 1301969 1648507 := bstep (se 1 (by rfl) ⟨1236380, by rfl⟩ : syracuseStep 1648507 = 2472761) B2472761
theorem B4696127 : Blo 1301969 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B3131617 : Blo 1301969 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B2197759 : Blo 1301969 2197759 := bstep (se 1 (by rfl) ⟨1648319, by rfl⟩ : syracuseStep 2197759 = 3296639) B3296639
theorem B7424297 : Blo 1301969 7424297 := bstep (se 2 (by rfl) ⟨2784111, by rfl⟩ : syracuseStep 7424297 = 5568223) B5568223
theorem B10561873 : Blo 1301969 10561873 := bstep (se 2 (by rfl) ⟨3960702, by rfl⟩ : syracuseStep 10561873 = 7921405) B7921405
theorem B22276781 : Blo 1301969 22276781 := bstep (se 3 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 22276781 = 8353793) B8353793
theorem B2198279 : Blo 1301969 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B152382403 : Blo 1301969 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B1952975 : Blo 1301969 1952975 := bstep (se 1 (by rfl) ⟨1464731, by rfl⟩ : syracuseStep 1952975 = 2929463) B2929463
theorem B22580441 : Blo 1301969 22580441 := bstep (se 2 (by rfl) ⟨8467665, by rfl⟩ : syracuseStep 22580441 = 16935331) B16935331
theorem B1649899 : Blo 1301969 1649899 := bstep (se 1 (by rfl) ⟨1237424, by rfl⟩ : syracuseStep 1649899 = 2474849) B2474849
theorem B2198839 : Blo 1301969 2198839 := bstep (se 1 (by rfl) ⟨1649129, by rfl⟩ : syracuseStep 2198839 = 3298259) B3298259
theorem B1953095 : Blo 1301969 1953095 := bstep (se 1 (by rfl) ⟨1464821, by rfl⟩ : syracuseStep 1953095 = 2929643) B2929643
theorem B5279057 : Blo 1301969 5279057 := bstep (se 2 (by rfl) ⟨1979646, by rfl⟩ : syracuseStep 5279057 = 3959293) B3959293
theorem B7425755 : Blo 1301969 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B1953503 : Blo 1301969 1953503 := bstep (se 1 (by rfl) ⟨1465127, by rfl⟩ : syracuseStep 1953503 = 2930255) B2930255
theorem B2199305 : Blo 1301969 2199305 := bstep (se 2 (by rfl) ⟨824739, by rfl⟩ : syracuseStep 2199305 = 1649479) B1649479
theorem B8343337 : Blo 1301969 8343337 := bstep (se 2 (by rfl) ⟨3128751, by rfl⟩ : syracuseStep 8343337 = 6257503) B6257503
theorem B2199359 : Blo 1301969 2199359 := bstep (se 1 (by rfl) ⟨1649519, by rfl⟩ : syracuseStep 2199359 = 3299039) B3299039
theorem B3297257 : Blo 1301969 3297257 := bstep (se 2 (by rfl) ⟨1236471, by rfl⟩ : syracuseStep 3297257 = 2472943) B2472943
theorem B6262771 : Blo 1301969 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B12521465 : Blo 1301969 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B1953863 : Blo 1301969 1953863 := bstep (se 1 (by rfl) ⟨1465397, by rfl⟩ : syracuseStep 1953863 = 2930795) B2930795
theorem B7426187 : Blo 1301969 7426187 := bstep (se 1 (by rfl) ⟨5569640, by rfl⟩ : syracuseStep 7426187 = 11139281) B11139281
theorem B1953983 : Blo 1301969 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B16937207 : Blo 1301969 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B1954127 : Blo 1301969 1954127 := bstep (se 1 (by rfl) ⟨1465595, by rfl⟩ : syracuseStep 1954127 = 2931191) B2931191
theorem B1954169 : Blo 1301969 1954169 := bstep (se 2 (by rfl) ⟨732813, by rfl⟩ : syracuseStep 1954169 = 1465627) B1465627
theorem B5722525 : Blo 1301969 5722525 := bstep (se 3 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 5722525 = 2145947) B2145947
theorem B1954463 : Blo 1301969 1954463 := bstep (se 1 (by rfl) ⟨1465847, by rfl⟩ : syracuseStep 1954463 = 2931695) B2931695
theorem B22246163 : Blo 1301969 22246163 := bstep (se 1 (by rfl) ⟨16684622, by rfl⟩ : syracuseStep 22246163 = 33369245) B33369245
theorem B33395489 : Blo 1301969 33395489 := bstep (se 2 (by rfl) ⟨12523308, by rfl⟩ : syracuseStep 33395489 = 25046617) B25046617
theorem B1954793 : Blo 1301969 1954793 := bstep (se 2 (by rfl) ⟨733047, by rfl⟩ : syracuseStep 1954793 = 1466095) B1466095
theorem B1954847 : Blo 1301969 1954847 := bstep (se 1 (by rfl) ⟨1466135, by rfl⟩ : syracuseStep 1954847 = 2932271) B2932271
theorem B25031855 : Blo 1301969 25031855 := bstep (se 1 (by rfl) ⟨18773891, by rfl⟩ : syracuseStep 25031855 = 37547783) B37547783
theorem B3708139 : Blo 1301969 3708139 := bstep (se 1 (by rfl) ⟨2781104, by rfl⟩ : syracuseStep 3708139 = 5562209) B5562209
theorem B1955135 : Blo 1301969 1955135 := bstep (se 1 (by rfl) ⟨1466351, by rfl⟩ : syracuseStep 1955135 = 2932703) B2932703
theorem B3708287 : Blo 1301969 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B3708413 : Blo 1301969 3708413 := bstep (se 3 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 3708413 = 1390655) B1390655
theorem B4069007 : Blo 1301969 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B5568239 : Blo 1301969 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B18790157 : Blo 1301969 18790157 := bstep (se 3 (by rfl) ⟨3523154, by rfl⟩ : syracuseStep 18790157 = 7046309) B7046309
theorem B2930471 : Blo 1301969 2930471 := bstep (se 1 (by rfl) ⟨2197853, by rfl⟩ : syracuseStep 2930471 = 4395707) B4395707
theorem B31700807 : Blo 1301969 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B75110327 : Blo 1301969 75110327 := bstep (se 1 (by rfl) ⟨56332745, by rfl⟩ : syracuseStep 75110327 = 112665491) B112665491
theorem B16693235 : Blo 1301969 16693235 := bstep (se 1 (by rfl) ⟨12519926, by rfl⟩ : syracuseStep 16693235 = 25039853) B25039853
theorem B3758363 : Blo 1301969 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B3758375 : Blo 1301969 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B4454695 : Blo 1301969 4454695 := bstep (se 1 (by rfl) ⟨3341021, by rfl⟩ : syracuseStep 4454695 = 6682043) B6682043
theorem B3709471 : Blo 1301969 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B14277181 : Blo 1301969 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B4946615 : Blo 1301969 4946615 := bstep (se 1 (by rfl) ⟨3709961, by rfl⟩ : syracuseStep 4946615 = 7419923) B7419923
theorem B12524539 : Blo 1301969 12524539 := bstep (se 1 (by rfl) ⟨9393404, by rfl⟩ : syracuseStep 12524539 = 18786809) B18786809
theorem B1465375 : Blo 1301969 1465375 := bstep (se 1 (by rfl) ⟨1099031, by rfl⟩ : syracuseStep 1465375 = 2198063) B2198063
theorem B24116291 : Blo 1301969 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B4398623 : Blo 1301969 4398623 := bstep (se 1 (by rfl) ⟨3298967, by rfl⟩ : syracuseStep 4398623 = 6597935) B6597935
theorem B1302119 : Blo 1301969 1302119 := bstep (se 1 (by rfl) ⟨976589, by rfl⟩ : syracuseStep 1302119 = 1953179) B1953179
theorem B2088551 : Blo 1301969 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B1302363 : Blo 1301969 1302363 := bstep (se 1 (by rfl) ⟨976772, by rfl⟩ : syracuseStep 1302363 = 1953545) B1953545
theorem B1302399 : Blo 1301969 1302399 := bstep (se 1 (by rfl) ⟨976799, by rfl⟩ : syracuseStep 1302399 = 1953599) B1953599
theorem B1302575 : Blo 1301969 1302575 := bstep (se 1 (by rfl) ⟨976931, by rfl⟩ : syracuseStep 1302575 = 1953863) B1953863
theorem B1302655 : Blo 1301969 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B1302751 : Blo 1301969 1302751 := bstep (se 1 (by rfl) ⟨977063, by rfl⟩ : syracuseStep 1302751 = 1954127) B1954127
theorem B1302779 : Blo 1301969 1302779 := bstep (se 1 (by rfl) ⟨977084, by rfl⟩ : syracuseStep 1302779 = 1954169) B1954169
theorem B2932991 : Blo 1301969 2932991 := bstep (se 1 (by rfl) ⟨2199743, by rfl⟩ : syracuseStep 2932991 = 4399487) B4399487
theorem B1302975 : Blo 1301969 1302975 := bstep (se 1 (by rfl) ⟨977231, by rfl⟩ : syracuseStep 1302975 = 1954463) B1954463
theorem B14082497 : Blo 1301969 14082497 := bstep (se 2 (by rfl) ⟨5280936, by rfl⟩ : syracuseStep 14082497 = 10561873) B10561873
theorem B1303195 : Blo 1301969 1303195 := bstep (se 1 (by rfl) ⟨977396, by rfl⟩ : syracuseStep 1303195 = 1954793) B1954793
theorem B1303231 : Blo 1301969 1303231 := bstep (se 1 (by rfl) ⟨977423, by rfl⟩ : syracuseStep 1303231 = 1954847) B1954847
theorem B16687903 : Blo 1301969 16687903 := bstep (se 1 (by rfl) ⟨12515927, by rfl⟩ : syracuseStep 16687903 = 25031855) B25031855
theorem B1303423 : Blo 1301969 1303423 := bstep (se 1 (by rfl) ⟨977567, by rfl⟩ : syracuseStep 1303423 = 1955135) B1955135
theorem B2712671 : Blo 1301969 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B3712159 : Blo 1301969 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B6685865 : Blo 1301969 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B12526771 : Blo 1301969 12526771 := bstep (se 1 (by rfl) ⟨9395078, by rfl⟩ : syracuseStep 12526771 = 18790157) B18790157
theorem B12698855 : Blo 1301969 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B3130751 : Blo 1301969 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B4949531 : Blo 1301969 4949531 := bstep (se 1 (by rfl) ⟨3712148, by rfl⟩ : syracuseStep 4949531 = 7424297) B7424297
theorem B23758373 : Blo 1301969 23758373 := bstep (se 4 (by rfl) ⟨2227347, by rfl⟩ : syracuseStep 23758373 = 4454695) B4454695
theorem B812706149 : Blo 1301969 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B4950503 : Blo 1301969 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B2198009 : Blo 1301969 2198009 := bstep (se 2 (by rfl) ⟨824253, by rfl⟩ : syracuseStep 2198009 = 1648507) B1648507
theorem B8350361 : Blo 1301969 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B2198171 : Blo 1301969 2198171 := bstep (se 1 (by rfl) ⟨1648628, by rfl⟩ : syracuseStep 2198171 = 3297257) B3297257
theorem B4950791 : Blo 1301969 4950791 := bstep (se 1 (by rfl) ⟨3713093, by rfl⟩ : syracuseStep 4950791 = 7426187) B7426187
theorem B11291471 : Blo 1301969 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B14830775 : Blo 1301969 14830775 := bstep (se 1 (by rfl) ⟨11123081, by rfl⟩ : syracuseStep 14830775 = 22246163) B22246163
theorem B7630033 : Blo 1301969 7630033 := bstep (se 2 (by rfl) ⟨2861262, by rfl⟩ : syracuseStep 7630033 = 5722525) B5722525
theorem B1650127 : Blo 1301969 1650127 := bstep (se 1 (by rfl) ⟨1237595, by rfl⟩ : syracuseStep 1650127 = 2475191) B2475191
theorem B13364747 : Blo 1301969 13364747 := bstep (se 1 (by rfl) ⟨10023560, by rfl⟩ : syracuseStep 13364747 = 20047121) B20047121
theorem B1953647 : Blo 1301969 1953647 := bstep (se 1 (by rfl) ⟨1465235, by rfl⟩ : syracuseStep 1953647 = 2930471) B2930471
theorem B50073551 : Blo 1301969 50073551 := bstep (se 1 (by rfl) ⟨37555163, by rfl⟩ : syracuseStep 50073551 = 75110327) B75110327
theorem B11128823 : Blo 1301969 11128823 := bstep (se 1 (by rfl) ⟨8346617, by rfl⟩ : syracuseStep 11128823 = 16693235) B16693235
theorem B16699385 : Blo 1301969 16699385 := bstep (se 2 (by rfl) ⟨6262269, by rfl⟩ : syracuseStep 16699385 = 12524539) B12524539
theorem B1953833 : Blo 1301969 1953833 := bstep (se 2 (by rfl) ⟨732687, by rfl⟩ : syracuseStep 1953833 = 1465375) B1465375
theorem B4944185 : Blo 1301969 4944185 := bstep (se 2 (by rfl) ⟨1854069, by rfl⟩ : syracuseStep 4944185 = 3708139) B3708139
theorem B2199865 : Blo 1301969 2199865 := bstep (se 2 (by rfl) ⟨824949, by rfl⟩ : syracuseStep 2199865 = 1649899) B1649899
theorem B3297743 : Blo 1301969 3297743 := bstep (se 1 (by rfl) ⟨2473307, by rfl⟩ : syracuseStep 3297743 = 4946615) B4946615
theorem B16077527 : Blo 1301969 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B15053627 : Blo 1301969 15053627 := bstep (se 1 (by rfl) ⟨11290220, by rfl⟩ : syracuseStep 15053627 = 22580441) B22580441
theorem B3519371 : Blo 1301969 3519371 := bstep (se 1 (by rfl) ⟨2639528, by rfl⟩ : syracuseStep 3519371 = 5279057) B5279057
theorem B3298927 : Blo 1301969 3298927 := bstep (se 1 (by rfl) ⟨2474195, by rfl⟩ : syracuseStep 3298927 = 4948391) B4948391
theorem B4175489 : Blo 1301969 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B2930345 : Blo 1301969 2930345 := bstep (se 2 (by rfl) ⟨1098879, by rfl⟩ : syracuseStep 2930345 = 2197759) B2197759
theorem B22263659 : Blo 1301969 22263659 := bstep (se 1 (by rfl) ⟨16697744, by rfl⟩ : syracuseStep 22263659 = 33395489) B33395489
theorem B4945961 : Blo 1301969 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B19036241 : Blo 1301969 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B2472191 : Blo 1301969 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B2472275 : Blo 1301969 2472275 := bstep (se 1 (by rfl) ⟨1854206, by rfl⟩ : syracuseStep 2472275 = 3708413) B3708413
theorem B21133871 : Blo 1301969 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B8347643 : Blo 1301969 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B2505575 : Blo 1301969 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B2505583 : Blo 1301969 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B5569469 : Blo 1301969 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B16694261 : Blo 1301969 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B2931785 : Blo 1301969 2931785 := bstep (se 2 (by rfl) ⟨1099419, by rfl⟩ : syracuseStep 2931785 = 2198839) B2198839
theorem B14851187 : Blo 1301969 14851187 := bstep (se 1 (by rfl) ⟨11138390, by rfl⟩ : syracuseStep 14851187 = 22276781) B22276781
theorem B1465519 : Blo 1301969 1465519 := bstep (se 1 (by rfl) ⟨1099139, by rfl⟩ : syracuseStep 1465519 = 2198279) B2198279
theorem B1301983 : Blo 1301969 1301983 := bstep (se 1 (by rfl) ⟨976487, by rfl⟩ : syracuseStep 1301983 = 1952975) B1952975
theorem B1302063 : Blo 1301969 1302063 := bstep (se 1 (by rfl) ⟨976547, by rfl⟩ : syracuseStep 1302063 = 1953095) B1953095
theorem B2932415 : Blo 1301969 2932415 := bstep (se 1 (by rfl) ⟨2199311, by rfl⟩ : syracuseStep 2932415 = 4398623) B4398623
theorem B11124449 : Blo 1301969 11124449 := bstep (se 2 (by rfl) ⟨4171668, by rfl⟩ : syracuseStep 11124449 = 8343337) B8343337
theorem B1302335 : Blo 1301969 1302335 := bstep (se 1 (by rfl) ⟨976751, by rfl⟩ : syracuseStep 1302335 = 1953503) B1953503
theorem B1466203 : Blo 1301969 1466203 := bstep (se 1 (by rfl) ⟨1099652, by rfl⟩ : syracuseStep 1466203 = 2199305) B2199305
theorem B1466239 : Blo 1301969 1466239 := bstep (se 1 (by rfl) ⟨1099679, by rfl⟩ : syracuseStep 1466239 = 2199359) B2199359
theorem B1302555 : Blo 1301969 1302555 := bstep (se 1 (by rfl) ⟨976916, by rfl⟩ : syracuseStep 1302555 = 1953833) B1953833
theorem B9388331 : Blo 1301969 9388331 := bstep (se 1 (by rfl) ⟨7041248, by rfl⟩ : syracuseStep 9388331 = 14082497) B14082497
theorem B2933153 : Blo 1301969 2933153 := bstep (se 2 (by rfl) ⟨1099932, by rfl⟩ : syracuseStep 2933153 = 2199865) B2199865
theorem B10035751 : Blo 1301969 10035751 := bstep (se 1 (by rfl) ⟨7526813, by rfl⟩ : syracuseStep 10035751 = 15053627) B15053627
theorem B4457243 : Blo 1301969 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B8348669 : Blo 1301969 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B22250537 : Blo 1301969 22250537 := bstep (se 2 (by rfl) ⟨8343951, by rfl⟩ : syracuseStep 22250537 = 16687903) B16687903
theorem B12690827 : Blo 1301969 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B1648127 : Blo 1301969 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B4949545 : Blo 1301969 4949545 := bstep (se 2 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 4949545 = 3712159) B3712159
theorem B1648183 : Blo 1301969 1648183 := bstep (se 1 (by rfl) ⟨1236137, by rfl⟩ : syracuseStep 1648183 = 2472275) B2472275
theorem B541804099 : Blo 1301969 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B3712979 : Blo 1301969 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B7416299 : Blo 1301969 7416299 := bstep (se 1 (by rfl) ⟨5562224, by rfl⟩ : syracuseStep 7416299 = 11124449) B11124449
theorem B5565095 : Blo 1301969 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B3296123 : Blo 1301969 3296123 := bstep (se 1 (by rfl) ⟨2472092, by rfl⟩ : syracuseStep 3296123 = 4944185) B4944185
theorem B2198495 : Blo 1301969 2198495 := bstep (se 1 (by rfl) ⟨1648871, by rfl⟩ : syracuseStep 2198495 = 3297743) B3297743
theorem B10718351 : Blo 1301969 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B2346247 : Blo 1301969 2346247 := bstep (se 1 (by rfl) ⟨1759685, by rfl⟩ : syracuseStep 2346247 = 3519371) B3519371
theorem B8465903 : Blo 1301969 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B15838915 : Blo 1301969 15838915 := bstep (se 1 (by rfl) ⟨11879186, by rfl⟩ : syracuseStep 15838915 = 23758373) B23758373
theorem B11132923 : Blo 1301969 11132923 := bstep (se 1 (by rfl) ⟨8349692, by rfl⟩ : syracuseStep 11132923 = 16699385) B16699385
theorem B1953563 : Blo 1301969 1953563 := bstep (se 1 (by rfl) ⟨1465172, by rfl⟩ : syracuseStep 1953563 = 2930345) B2930345
theorem B3297307 : Blo 1301969 3297307 := bstep (se 1 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 3297307 = 4945961) B4945961
theorem B1954025 : Blo 1301969 1954025 := bstep (se 2 (by rfl) ⟨732759, by rfl⟩ : syracuseStep 1954025 = 1465519) B1465519
theorem B5566907 : Blo 1301969 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B2200169 : Blo 1301969 2200169 := bstep (se 2 (by rfl) ⟨825063, by rfl⟩ : syracuseStep 2200169 = 1650127) B1650127
theorem B11129507 : Blo 1301969 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B1954523 : Blo 1301969 1954523 := bstep (se 1 (by rfl) ⟨1465892, by rfl⟩ : syracuseStep 1954523 = 2931785) B2931785
theorem B9900791 : Blo 1301969 9900791 := bstep (se 1 (by rfl) ⟨7425593, by rfl⟩ : syracuseStep 9900791 = 14851187) B14851187
theorem B6681533 : Blo 1301969 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B8909831 : Blo 1301969 8909831 := bstep (se 1 (by rfl) ⟨6682373, by rfl⟩ : syracuseStep 8909831 = 13364747) B13364747
theorem B1954937 : Blo 1301969 1954937 := bstep (se 2 (by rfl) ⟨733101, by rfl⟩ : syracuseStep 1954937 = 1466203) B1466203
theorem B1954943 : Blo 1301969 1954943 := bstep (se 1 (by rfl) ⟨1466207, by rfl⟩ : syracuseStep 1954943 = 2932415) B2932415
theorem B1954985 : Blo 1301969 1954985 := bstep (se 2 (by rfl) ⟨733119, by rfl⟩ : syracuseStep 1954985 = 1466239) B1466239
theorem B7419215 : Blo 1301969 7419215 := bstep (se 1 (by rfl) ⟨5564411, by rfl⟩ : syracuseStep 7419215 = 11128823) B11128823
theorem B1955327 : Blo 1301969 1955327 := bstep (se 1 (by rfl) ⟨1466495, by rfl⟩ : syracuseStep 1955327 = 2932991) B2932991
theorem B1808447 : Blo 1301969 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B3299687 : Blo 1301969 3299687 := bstep (se 1 (by rfl) ⟨2474765, by rfl⟩ : syracuseStep 3299687 = 4949531) B4949531
theorem B2783659 : Blo 1301969 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B3340777 : Blo 1301969 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B14842439 : Blo 1301969 14842439 := bstep (se 1 (by rfl) ⟨11131829, by rfl⟩ : syracuseStep 14842439 = 22263659) B22263659
theorem B16702361 : Blo 1301969 16702361 := bstep (se 2 (by rfl) ⟨6263385, by rfl⟩ : syracuseStep 16702361 = 12526771) B12526771
theorem B10173377 : Blo 1301969 10173377 := bstep (se 2 (by rfl) ⟨3815016, by rfl⟩ : syracuseStep 10173377 = 7630033) B7630033
theorem B3300335 : Blo 1301969 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B1465339 : Blo 1301969 1465339 := bstep (se 1 (by rfl) ⟨1099004, by rfl⟩ : syracuseStep 1465339 = 2198009) B2198009
theorem B14089247 : Blo 1301969 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B1465447 : Blo 1301969 1465447 := bstep (se 1 (by rfl) ⟨1099085, by rfl⟩ : syracuseStep 1465447 = 2198171) B2198171
theorem B3300527 : Blo 1301969 3300527 := bstep (se 1 (by rfl) ⟨2475395, by rfl⟩ : syracuseStep 3300527 = 4950791) B4950791
theorem B7527647 : Blo 1301969 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B9887183 : Blo 1301969 9887183 := bstep (se 1 (by rfl) ⟨7415387, by rfl⟩ : syracuseStep 9887183 = 14830775) B14830775
theorem B4398569 : Blo 1301969 4398569 := bstep (se 2 (by rfl) ⟨1649463, by rfl⟩ : syracuseStep 4398569 = 3298927) B3298927
theorem B1302431 : Blo 1301969 1302431 := bstep (se 1 (by rfl) ⟨976823, by rfl⟩ : syracuseStep 1302431 = 1953647) B1953647
theorem B33382367 : Blo 1301969 33382367 := bstep (se 1 (by rfl) ⟨25036775, by rfl⟩ : syracuseStep 33382367 = 50073551) B50073551
theorem B1302683 : Blo 1301969 1302683 := bstep (se 1 (by rfl) ⟨977012, by rfl⟩ : syracuseStep 1302683 = 1954025) B1954025
theorem B6258887 : Blo 1301969 6258887 := bstep (se 1 (by rfl) ⟨4694165, by rfl⟩ : syracuseStep 6258887 = 9388331) B9388331
theorem B3711271 : Blo 1301969 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B1466779 : Blo 1301969 1466779 := bstep (se 1 (by rfl) ⟨1100084, by rfl⟩ : syracuseStep 1466779 = 2200169) B2200169
theorem B1303015 : Blo 1301969 1303015 := bstep (se 1 (by rfl) ⟨977261, by rfl⟩ : syracuseStep 1303015 = 1954523) B1954523
theorem B3711545 : Blo 1301969 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B5939887 : Blo 1301969 5939887 := bstep (se 1 (by rfl) ⟨4454915, by rfl⟩ : syracuseStep 5939887 = 8909831) B8909831
theorem B1303291 : Blo 1301969 1303291 := bstep (se 1 (by rfl) ⟨977468, by rfl⟩ : syracuseStep 1303291 = 1954937) B1954937
theorem B1303295 : Blo 1301969 1303295 := bstep (se 1 (by rfl) ⟨977471, by rfl⟩ : syracuseStep 1303295 = 1954943) B1954943
theorem B1303323 : Blo 1301969 1303323 := bstep (se 1 (by rfl) ⟨977492, by rfl⟩ : syracuseStep 1303323 = 1954985) B1954985
theorem B1303551 : Blo 1301969 1303551 := bstep (se 1 (by rfl) ⟨977663, by rfl⟩ : syracuseStep 1303551 = 1955327) B1955327
theorem B2197415 : Blo 1301969 2197415 := bstep (se 1 (by rfl) ⟨1648061, by rfl⟩ : syracuseStep 2197415 = 3296123) B3296123
theorem B11134907 : Blo 1301969 11134907 := bstep (se 1 (by rfl) ⟨8351180, by rfl⟩ : syracuseStep 11134907 = 16702361) B16702361
theorem B2197577 : Blo 1301969 2197577 := bstep (se 2 (by rfl) ⟨824091, by rfl⟩ : syracuseStep 2197577 = 1648183) B1648183
theorem B722405465 : Blo 1301969 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B7145567 : Blo 1301969 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B5565779 : Blo 1301969 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B13381001 : Blo 1301969 13381001 := bstep (se 2 (by rfl) ⟨5017875, by rfl⟩ : syracuseStep 13381001 = 10035751) B10035751
theorem B1953785 : Blo 1301969 1953785 := bstep (se 2 (by rfl) ⟨732669, by rfl⟩ : syracuseStep 1953785 = 1465339) B1465339
theorem B4395005 : Blo 1301969 4395005 := bstep (se 3 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 4395005 = 1648127) B1648127
theorem B1953929 : Blo 1301969 1953929 := bstep (se 2 (by rfl) ⟨732723, by rfl⟩ : syracuseStep 1953929 = 1465447) B1465447
theorem B2199791 : Blo 1301969 2199791 := bstep (se 1 (by rfl) ⟨1649843, by rfl⟩ : syracuseStep 2199791 = 3299687) B3299687
theorem B4944199 : Blo 1301969 4944199 := bstep (se 1 (by rfl) ⟨3708149, by rfl⟩ : syracuseStep 4944199 = 7416299) B7416299
theorem B2200223 : Blo 1301969 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B9392831 : Blo 1301969 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B6599393 : Blo 1301969 6599393 := bstep (se 2 (by rfl) ⟨2474772, by rfl⟩ : syracuseStep 6599393 = 4949545) B4949545
theorem B2200351 : Blo 1301969 2200351 := bstep (se 1 (by rfl) ⟨1650263, by rfl⟩ : syracuseStep 2200351 = 3300527) B3300527
theorem B5018431 : Blo 1301969 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B14843897 : Blo 1301969 14843897 := bstep (se 2 (by rfl) ⟨5566461, by rfl⟩ : syracuseStep 14843897 = 11132923) B11132923
theorem B6591455 : Blo 1301969 6591455 := bstep (se 1 (by rfl) ⟨4943591, by rfl⟩ : syracuseStep 6591455 = 9887183) B9887183
theorem B9901277 : Blo 1301969 9901277 := bstep (se 3 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 9901277 = 3712979) B3712979
theorem B22254911 : Blo 1301969 22254911 := bstep (se 1 (by rfl) ⟨16691183, by rfl⟩ : syracuseStep 22254911 = 33382367) B33382367
theorem B4396409 : Blo 1301969 4396409 := bstep (se 2 (by rfl) ⟨1648653, by rfl⟩ : syracuseStep 4396409 = 3297307) B3297307
theorem B4822525 : Blo 1301969 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B1955435 : Blo 1301969 1955435 := bstep (se 1 (by rfl) ⟨1466576, by rfl⟩ : syracuseStep 1955435 = 2933153) B2933153
theorem B7419671 : Blo 1301969 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B6600527 : Blo 1301969 6600527 := bstep (se 1 (by rfl) ⟨4950395, by rfl⟩ : syracuseStep 6600527 = 9900791) B9900791
theorem B2971495 : Blo 1301969 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B4454369 : Blo 1301969 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B14833691 : Blo 1301969 14833691 := bstep (se 1 (by rfl) ⟨11125268, by rfl⟩ : syracuseStep 14833691 = 22250537) B22250537
theorem B4946143 : Blo 1301969 4946143 := bstep (se 1 (by rfl) ⟨3709607, by rfl⟩ : syracuseStep 4946143 = 7419215) B7419215
theorem B8460551 : Blo 1301969 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B3128329 : Blo 1301969 3128329 := bstep (se 2 (by rfl) ⟨1173123, by rfl⟩ : syracuseStep 3128329 = 2346247) B2346247
theorem B9894959 : Blo 1301969 9894959 := bstep (se 1 (by rfl) ⟨7421219, by rfl⟩ : syracuseStep 9894959 = 14842439) B14842439
theorem B3710063 : Blo 1301969 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B6782251 : Blo 1301969 6782251 := bstep (se 1 (by rfl) ⟨5086688, by rfl⟩ : syracuseStep 6782251 = 10173377) B10173377
theorem B1465663 : Blo 1301969 1465663 := bstep (se 1 (by rfl) ⟨1099247, by rfl⟩ : syracuseStep 1465663 = 2198495) B2198495
theorem B21118553 : Blo 1301969 21118553 := bstep (se 2 (by rfl) ⟨7919457, by rfl⟩ : syracuseStep 21118553 = 15838915) B15838915
theorem B2932379 : Blo 1301969 2932379 := bstep (se 1 (by rfl) ⟨2199284, by rfl⟩ : syracuseStep 2932379 = 4398569) B4398569
theorem B5643935 : Blo 1301969 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B17817421 : Blo 1301969 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B1302375 : Blo 1301969 1302375 := bstep (se 1 (by rfl) ⟨976781, by rfl⟩ : syracuseStep 1302375 = 1953563) B1953563
theorem B1302619 : Blo 1301969 1302619 := bstep (se 1 (by rfl) ⟨976964, by rfl⟩ : syracuseStep 1302619 = 1953929) B1953929
theorem B1466527 : Blo 1301969 1466527 := bstep (se 1 (by rfl) ⟨1099895, by rfl⟩ : syracuseStep 1466527 = 2199791) B2199791
theorem B6594857 : Blo 1301969 6594857 := bstep (se 2 (by rfl) ⟨2473071, by rfl⟩ : syracuseStep 6594857 = 4946143) B4946143
theorem B2474363 : Blo 1301969 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B4948361 : Blo 1301969 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B1466815 : Blo 1301969 1466815 := bstep (se 1 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 1466815 = 2200223) B2200223
theorem B4399595 : Blo 1301969 4399595 := bstep (se 1 (by rfl) ⟨3299696, by rfl⟩ : syracuseStep 4399595 = 6599393) B6599393
theorem B14836607 : Blo 1301969 14836607 := bstep (se 1 (by rfl) ⟨11127455, by rfl⟩ : syracuseStep 14836607 = 22254911) B22254911
theorem B2933801 : Blo 1301969 2933801 := bstep (se 2 (by rfl) ⟨1100175, by rfl⟩ : syracuseStep 2933801 = 2200351) B2200351
theorem B1303623 : Blo 1301969 1303623 := bstep (se 1 (by rfl) ⟨977717, by rfl⟩ : syracuseStep 1303623 = 1955435) B1955435
theorem B4400351 : Blo 1301969 4400351 := bstep (se 1 (by rfl) ⟨3300263, by rfl⟩ : syracuseStep 4400351 = 6600527) B6600527
theorem B7423271 : Blo 1301969 7423271 := bstep (se 1 (by rfl) ⟨5567453, by rfl⟩ : syracuseStep 7423271 = 11134907) B11134907
theorem B4171105 : Blo 1301969 4171105 := bstep (se 2 (by rfl) ⟨1564164, by rfl⟩ : syracuseStep 4171105 = 3128329) B3128329
theorem B9889127 : Blo 1301969 9889127 := bstep (se 1 (by rfl) ⟨7416845, by rfl⟩ : syracuseStep 9889127 = 14833691) B14833691
theorem B6596639 : Blo 1301969 6596639 := bstep (se 1 (by rfl) ⟨4947479, by rfl⟩ : syracuseStep 6596639 = 9894959) B9894959
theorem B3762623 : Blo 1301969 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B4172591 : Blo 1301969 4172591 := bstep (se 1 (by rfl) ⟨3129443, by rfl⟩ : syracuseStep 4172591 = 6258887) B6258887
theorem B6261887 : Blo 1301969 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B4394303 : Blo 1301969 4394303 := bstep (se 1 (by rfl) ⟨3295727, by rfl⟩ : syracuseStep 4394303 = 6591455) B6591455
theorem B2969579 : Blo 1301969 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B481603643 : Blo 1301969 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B4763711 : Blo 1301969 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B5640367 : Blo 1301969 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B1954217 : Blo 1301969 1954217 := bstep (se 2 (by rfl) ⟨732831, by rfl⟩ : syracuseStep 1954217 = 1465663) B1465663
theorem B15847973 : Blo 1301969 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B14079035 : Blo 1301969 14079035 := bstep (se 1 (by rfl) ⟨10559276, by rfl⟩ : syracuseStep 14079035 = 21118553) B21118553
theorem B1954919 : Blo 1301969 1954919 := bstep (se 1 (by rfl) ⟨1466189, by rfl⟩ : syracuseStep 1954919 = 2932379) B2932379
theorem B2930003 : Blo 1301969 2930003 := bstep (se 1 (by rfl) ⟨2197502, by rfl⟩ : syracuseStep 2930003 = 4395005) B4395005
theorem B9893501 : Blo 1301969 9893501 := bstep (se 3 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 9893501 = 3710063) B3710063
theorem B6592265 : Blo 1301969 6592265 := bstep (se 2 (by rfl) ⟨2472099, by rfl⟩ : syracuseStep 6592265 = 4944199) B4944199
theorem B1955705 : Blo 1301969 1955705 := bstep (se 2 (by rfl) ⟨733389, by rfl⟩ : syracuseStep 1955705 = 1466779) B1466779
theorem B9895931 : Blo 1301969 9895931 := bstep (se 1 (by rfl) ⟨7421948, by rfl⟩ : syracuseStep 9895931 = 14843897) B14843897
theorem B6600851 : Blo 1301969 6600851 := bstep (se 1 (by rfl) ⟨4950638, by rfl⟩ : syracuseStep 6600851 = 9901277) B9901277
theorem B7919849 : Blo 1301969 7919849 := bstep (se 2 (by rfl) ⟨2969943, by rfl⟩ : syracuseStep 7919849 = 5939887) B5939887
theorem B2930939 : Blo 1301969 2930939 := bstep (se 1 (by rfl) ⟨2198204, by rfl⟩ : syracuseStep 2930939 = 4396409) B4396409
theorem B6691241 : Blo 1301969 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B4946447 : Blo 1301969 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B1464943 : Blo 1301969 1464943 := bstep (se 1 (by rfl) ⟨1098707, by rfl⟩ : syracuseStep 1464943 = 2197415) B2197415
theorem B1465051 : Blo 1301969 1465051 := bstep (se 1 (by rfl) ⟨1098788, by rfl⟩ : syracuseStep 1465051 = 2197577) B2197577
theorem B9043001 : Blo 1301969 9043001 := bstep (se 2 (by rfl) ⟨3391125, by rfl⟩ : syracuseStep 9043001 = 6782251) B6782251
theorem B6430033 : Blo 1301969 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B3710519 : Blo 1301969 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B8920667 : Blo 1301969 8920667 := bstep (se 1 (by rfl) ⟨6690500, by rfl⟩ : syracuseStep 8920667 = 13381001) B13381001
theorem B23756561 : Blo 1301969 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B1302523 : Blo 1301969 1302523 := bstep (se 1 (by rfl) ⟨976892, by rfl⟩ : syracuseStep 1302523 = 1953785) B1953785
theorem B321069095 : Blo 1301969 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B37544093 : Blo 1301969 37544093 := bstep (se 3 (by rfl) ⟨7039517, by rfl⟩ : syracuseStep 37544093 = 14079035) B14079035
theorem B7520489 : Blo 1301969 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B1302811 : Blo 1301969 1302811 := bstep (se 1 (by rfl) ⟨977108, by rfl⟩ : syracuseStep 1302811 = 1954217) B1954217
theorem B2933063 : Blo 1301969 2933063 := bstep (se 1 (by rfl) ⟨2199797, by rfl⟩ : syracuseStep 2933063 = 4399595) B4399595
theorem B1303279 : Blo 1301969 1303279 := bstep (se 1 (by rfl) ⟨977459, by rfl⟩ : syracuseStep 1303279 = 1954919) B1954919
theorem B2933567 : Blo 1301969 2933567 := bstep (se 1 (by rfl) ⟨2200175, by rfl⟩ : syracuseStep 2933567 = 4400351) B4400351
theorem B4948847 : Blo 1301969 4948847 := bstep (se 1 (by rfl) ⟨3711635, by rfl⟩ : syracuseStep 4948847 = 7423271) B7423271
theorem B6595667 : Blo 1301969 6595667 := bstep (se 1 (by rfl) ⟨4946750, by rfl⟩ : syracuseStep 6595667 = 9893501) B9893501
theorem B1303803 : Blo 1301969 1303803 := bstep (se 1 (by rfl) ⟨977852, by rfl⟩ : syracuseStep 1303803 = 1955705) B1955705
theorem B4400567 : Blo 1301969 4400567 := bstep (se 1 (by rfl) ⟨3300425, by rfl⟩ : syracuseStep 4400567 = 6600851) B6600851
theorem B2508415 : Blo 1301969 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B11126909 : Blo 1301969 11126909 := bstep (se 3 (by rfl) ⟨2086295, by rfl⟩ : syracuseStep 11126909 = 4172591) B4172591
theorem B15837707 : Blo 1301969 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B6597287 : Blo 1301969 6597287 := bstep (se 1 (by rfl) ⟨4947965, by rfl⟩ : syracuseStep 6597287 = 9895931) B9895931
theorem B1649575 : Blo 1301969 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B9891071 : Blo 1301969 9891071 := bstep (se 1 (by rfl) ⟨7418303, by rfl⟩ : syracuseStep 9891071 = 14836607) B14836607
theorem B1953257 : Blo 1301969 1953257 := bstep (se 2 (by rfl) ⟨732471, by rfl⟩ : syracuseStep 1953257 = 1464943) B1464943
theorem B1953335 : Blo 1301969 1953335 := bstep (se 1 (by rfl) ⟨1465001, by rfl⟩ : syracuseStep 1953335 = 2930003) B2930003
theorem B1953401 : Blo 1301969 1953401 := bstep (se 2 (by rfl) ⟨732525, by rfl⟩ : syracuseStep 1953401 = 1465051) B1465051
theorem B4394843 : Blo 1301969 4394843 := bstep (se 1 (by rfl) ⟨3296132, by rfl⟩ : syracuseStep 4394843 = 6592265) B6592265
theorem B5279899 : Blo 1301969 5279899 := bstep (se 1 (by rfl) ⟨3959924, by rfl⟩ : syracuseStep 5279899 = 7919849) B7919849
theorem B1953959 : Blo 1301969 1953959 := bstep (se 1 (by rfl) ⟨1465469, by rfl⟩ : syracuseStep 1953959 = 2930939) B2930939
theorem B4460827 : Blo 1301969 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B3297631 : Blo 1301969 3297631 := bstep (se 1 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 3297631 = 4946447) B4946447
theorem B8573377 : Blo 1301969 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B4174591 : Blo 1301969 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B2929535 : Blo 1301969 2929535 := bstep (se 1 (by rfl) ⟨2197151, by rfl⟩ : syracuseStep 2929535 = 4394303) B4394303
theorem B7918877 : Blo 1301969 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B3175807 : Blo 1301969 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B4396571 : Blo 1301969 4396571 := bstep (se 1 (by rfl) ⟨3297428, by rfl⟩ : syracuseStep 4396571 = 6594857) B6594857
theorem B1955369 : Blo 1301969 1955369 := bstep (se 2 (by rfl) ⟨733263, by rfl⟩ : syracuseStep 1955369 = 1466527) B1466527
theorem B3298907 : Blo 1301969 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B10565315 : Blo 1301969 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B1955753 : Blo 1301969 1955753 := bstep (se 2 (by rfl) ⟨733407, by rfl⟩ : syracuseStep 1955753 = 1466815) B1466815
theorem B1955867 : Blo 1301969 1955867 := bstep (se 1 (by rfl) ⟨1466900, by rfl⟩ : syracuseStep 1955867 = 2933801) B2933801
theorem B6592751 : Blo 1301969 6592751 := bstep (se 1 (by rfl) ⟨4944563, by rfl⟩ : syracuseStep 6592751 = 9889127) B9889127
theorem B4397759 : Blo 1301969 4397759 := bstep (se 1 (by rfl) ⟨3298319, by rfl⟩ : syracuseStep 4397759 = 6596639) B6596639
theorem B5561473 : Blo 1301969 5561473 := bstep (se 2 (by rfl) ⟨2085552, by rfl⟩ : syracuseStep 5561473 = 4171105) B4171105
theorem B6028667 : Blo 1301969 6028667 := bstep (se 1 (by rfl) ⟨4521500, by rfl⟩ : syracuseStep 6028667 = 9043001) B9043001
theorem B2473679 : Blo 1301969 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B5947111 : Blo 1301969 5947111 := bstep (se 1 (by rfl) ⟨4460333, by rfl⟩ : syracuseStep 5947111 = 8920667) B8920667
theorem B1302639 : Blo 1301969 1302639 := bstep (se 1 (by rfl) ⟨976979, by rfl⟩ : syracuseStep 1302639 = 1953959) B1953959
theorem B5013659 : Blo 1301969 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B5947769 : Blo 1301969 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B13378213 : Blo 1301969 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B2933711 : Blo 1301969 2933711 := bstep (se 1 (by rfl) ⟨2200283, by rfl⟩ : syracuseStep 2933711 = 4400567) B4400567
theorem B1303579 : Blo 1301969 1303579 := bstep (se 1 (by rfl) ⟨977684, by rfl⟩ : syracuseStep 1303579 = 1955369) B1955369
theorem B1303835 : Blo 1301969 1303835 := bstep (se 1 (by rfl) ⟨977876, by rfl⟩ : syracuseStep 1303835 = 1955753) B1955753
theorem B1303911 : Blo 1301969 1303911 := bstep (se 1 (by rfl) ⟨977933, by rfl⟩ : syracuseStep 1303911 = 1955867) B1955867
theorem B7415297 : Blo 1301969 7415297 := bstep (se 2 (by rfl) ⟨2780736, by rfl⟩ : syracuseStep 7415297 = 5561473) B5561473
theorem B6596477 : Blo 1301969 6596477 := bstep (se 3 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 6596477 = 2473679) B2473679
theorem B25029395 : Blo 1301969 25029395 := bstep (se 1 (by rfl) ⟨18772046, by rfl⟩ : syracuseStep 25029395 = 37544093) B37544093
theorem B7039865 : Blo 1301969 7039865 := bstep (se 2 (by rfl) ⟨2639949, by rfl⟩ : syracuseStep 7039865 = 5279899) B5279899
theorem B1953023 : Blo 1301969 1953023 := bstep (se 1 (by rfl) ⟨1464767, by rfl⟩ : syracuseStep 1953023 = 2929535) B2929535
theorem B11431169 : Blo 1301969 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B5279251 : Blo 1301969 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B5566121 : Blo 1301969 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B2199271 : Blo 1301969 2199271 := bstep (se 1 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 2199271 = 3298907) B3298907
theorem B2199433 : Blo 1301969 2199433 := bstep (se 2 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 2199433 = 1649575) B1649575
theorem B7417939 : Blo 1301969 7417939 := bstep (se 1 (by rfl) ⟨5563454, by rfl⟩ : syracuseStep 7417939 = 11126909) B11126909
theorem B4395167 : Blo 1301969 4395167 := bstep (se 1 (by rfl) ⟨3296375, by rfl⟩ : syracuseStep 4395167 = 6592751) B6592751
theorem B4019111 : Blo 1301969 4019111 := bstep (se 1 (by rfl) ⟨3014333, by rfl⟩ : syracuseStep 4019111 = 6028667) B6028667
theorem B2929895 : Blo 1301969 2929895 := bstep (se 1 (by rfl) ⟨2197421, by rfl⟩ : syracuseStep 2929895 = 4394843) B4394843
theorem B214046063 : Blo 1301969 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B1955375 : Blo 1301969 1955375 := bstep (se 1 (by rfl) ⟨1466531, by rfl⟩ : syracuseStep 1955375 = 2933063) B2933063
theorem B4396841 : Blo 1301969 4396841 := bstep (se 2 (by rfl) ⟨1648815, by rfl⟩ : syracuseStep 4396841 = 3297631) B3297631
theorem B1955711 : Blo 1301969 1955711 := bstep (se 1 (by rfl) ⟨1466783, by rfl⟩ : syracuseStep 1955711 = 2933567) B2933567
theorem B3299231 : Blo 1301969 3299231 := bstep (se 1 (by rfl) ⟨2474423, by rfl⟩ : syracuseStep 3299231 = 4948847) B4948847
theorem B4397111 : Blo 1301969 4397111 := bstep (se 1 (by rfl) ⟨3297833, by rfl⟩ : syracuseStep 4397111 = 6595667) B6595667
theorem B2931047 : Blo 1301969 2931047 := bstep (se 1 (by rfl) ⟨2198285, by rfl⟩ : syracuseStep 2931047 = 4396571) B4396571
theorem B7043543 : Blo 1301969 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B31717925 : Blo 1301969 31717925 := bstep (se 4 (by rfl) ⟨2973555, by rfl⟩ : syracuseStep 31717925 = 5947111) B5947111
theorem B10558471 : Blo 1301969 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B4398191 : Blo 1301969 4398191 := bstep (se 1 (by rfl) ⟨3298643, by rfl⟩ : syracuseStep 4398191 = 6597287) B6597287
theorem B2931839 : Blo 1301969 2931839 := bstep (se 1 (by rfl) ⟨2198879, by rfl⟩ : syracuseStep 2931839 = 4397759) B4397759
theorem B4234409 : Blo 1301969 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B6594047 : Blo 1301969 6594047 := bstep (se 1 (by rfl) ⟨4945535, by rfl⟩ : syracuseStep 6594047 = 9891071) B9891071
theorem B1302171 : Blo 1301969 1302171 := bstep (se 1 (by rfl) ⟨976628, by rfl⟩ : syracuseStep 1302171 = 1953257) B1953257
theorem B1302223 : Blo 1301969 1302223 := bstep (se 1 (by rfl) ⟨976667, by rfl⟩ : syracuseStep 1302223 = 1953335) B1953335
theorem B1302267 : Blo 1301969 1302267 := bstep (se 1 (by rfl) ⟨976700, by rfl⟩ : syracuseStep 1302267 = 1953401) B1953401
theorem B3342439 : Blo 1301969 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B2679407 : Blo 1301969 2679407 := bstep (se 1 (by rfl) ⟨2009555, by rfl⟩ : syracuseStep 2679407 = 4019111) B4019111
theorem B142697375 : Blo 1301969 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B15860717 : Blo 1301969 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B1303583 : Blo 1301969 1303583 := bstep (se 1 (by rfl) ⟨977687, by rfl⟩ : syracuseStep 1303583 = 1955375) B1955375
theorem B1303807 : Blo 1301969 1303807 := bstep (se 1 (by rfl) ⟨977855, by rfl⟩ : syracuseStep 1303807 = 1955711) B1955711
theorem B4695695 : Blo 1301969 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B21145283 : Blo 1301969 21145283 := bstep (se 1 (by rfl) ⟨15858962, by rfl⟩ : syracuseStep 21145283 = 31717925) B31717925
theorem B7039001 : Blo 1301969 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B7620779 : Blo 1301969 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B9890585 : Blo 1301969 9890585 := bstep (se 2 (by rfl) ⟨3708969, by rfl⟩ : syracuseStep 9890585 = 7417939) B7417939
theorem B1953263 : Blo 1301969 1953263 := bstep (se 1 (by rfl) ⟨1464947, by rfl⟩ : syracuseStep 1953263 = 2929895) B2929895
theorem B17837617 : Blo 1301969 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B4943531 : Blo 1301969 4943531 := bstep (se 1 (by rfl) ⟨3707648, by rfl⟩ : syracuseStep 4943531 = 7415297) B7415297
theorem B2199487 : Blo 1301969 2199487 := bstep (se 1 (by rfl) ⟨1649615, by rfl⟩ : syracuseStep 2199487 = 3299231) B3299231
theorem B14077961 : Blo 1301969 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B1954031 : Blo 1301969 1954031 := bstep (se 1 (by rfl) ⟨1465523, by rfl⟩ : syracuseStep 1954031 = 2931047) B2931047
theorem B1954559 : Blo 1301969 1954559 := bstep (se 1 (by rfl) ⟨1465919, by rfl⟩ : syracuseStep 1954559 = 2931839) B2931839
theorem B2822939 : Blo 1301969 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B4396031 : Blo 1301969 4396031 := bstep (se 1 (by rfl) ⟨3297023, by rfl⟩ : syracuseStep 4396031 = 6594047) B6594047
theorem B2930111 : Blo 1301969 2930111 := bstep (se 1 (by rfl) ⟨2197583, by rfl⟩ : syracuseStep 2930111 = 4395167) B4395167
theorem B1955807 : Blo 1301969 1955807 := bstep (se 1 (by rfl) ⟨1466855, by rfl⟩ : syracuseStep 1955807 = 2933711) B2933711
theorem B2931227 : Blo 1301969 2931227 := bstep (se 1 (by rfl) ⟨2198420, by rfl⟩ : syracuseStep 2931227 = 4396841) B4396841
theorem B4397651 : Blo 1301969 4397651 := bstep (se 1 (by rfl) ⟨3298238, by rfl⟩ : syracuseStep 4397651 = 6596477) B6596477
theorem B2931407 : Blo 1301969 2931407 := bstep (se 1 (by rfl) ⟨2198555, by rfl⟩ : syracuseStep 2931407 = 4397111) B4397111
theorem B16686263 : Blo 1301969 16686263 := bstep (se 1 (by rfl) ⟨12514697, by rfl⟩ : syracuseStep 16686263 = 25029395) B25029395
theorem B4693243 : Blo 1301969 4693243 := bstep (se 1 (by rfl) ⟨3519932, by rfl⟩ : syracuseStep 4693243 = 7039865) B7039865
theorem B2932127 : Blo 1301969 2932127 := bstep (se 1 (by rfl) ⟨2199095, by rfl⟩ : syracuseStep 2932127 = 4398191) B4398191
theorem B1302015 : Blo 1301969 1302015 := bstep (se 1 (by rfl) ⟨976511, by rfl⟩ : syracuseStep 1302015 = 1953023) B1953023
theorem B2932361 : Blo 1301969 2932361 := bstep (se 2 (by rfl) ⟨1099635, by rfl⟩ : syracuseStep 2932361 = 2199271) B2199271
theorem B3710747 : Blo 1301969 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B2932577 : Blo 1301969 2932577 := bstep (se 2 (by rfl) ⟨1099716, by rfl⟩ : syracuseStep 2932577 = 2199433) B2199433
theorem B4456585 : Blo 1301969 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B1302687 : Blo 1301969 1302687 := bstep (se 1 (by rfl) ⟨977015, by rfl⟩ : syracuseStep 1302687 = 1954031) B1954031
theorem B1786271 : Blo 1301969 1786271 := bstep (se 1 (by rfl) ⟨1339703, by rfl⟩ : syracuseStep 1786271 = 2679407) B2679407
theorem B1303039 : Blo 1301969 1303039 := bstep (se 1 (by rfl) ⟨977279, by rfl⟩ : syracuseStep 1303039 = 1954559) B1954559
theorem B3130463 : Blo 1301969 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B1303871 : Blo 1301969 1303871 := bstep (se 1 (by rfl) ⟨977903, by rfl⟩ : syracuseStep 1303871 = 1955807) B1955807
theorem B5080519 : Blo 1301969 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B23783489 : Blo 1301969 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B3295687 : Blo 1301969 3295687 := bstep (se 1 (by rfl) ⟨2471765, by rfl⟩ : syracuseStep 3295687 = 4943531) B4943531
theorem B1953407 : Blo 1301969 1953407 := bstep (se 1 (by rfl) ⟨1465055, by rfl⟩ : syracuseStep 1953407 = 2930111) B2930111
theorem B1954151 : Blo 1301969 1954151 := bstep (se 1 (by rfl) ⟨1465613, by rfl⟩ : syracuseStep 1954151 = 2931227) B2931227
theorem B1954271 : Blo 1301969 1954271 := bstep (se 1 (by rfl) ⟨1465703, by rfl⟩ : syracuseStep 1954271 = 2931407) B2931407
theorem B1954751 : Blo 1301969 1954751 := bstep (se 1 (by rfl) ⟨1466063, by rfl⟩ : syracuseStep 1954751 = 2932127) B2932127
theorem B1954907 : Blo 1301969 1954907 := bstep (se 1 (by rfl) ⟨1466180, by rfl⟩ : syracuseStep 1954907 = 2932361) B2932361
theorem B1955051 : Blo 1301969 1955051 := bstep (se 1 (by rfl) ⟨1466288, by rfl⟩ : syracuseStep 1955051 = 2932577) B2932577
theorem B9385307 : Blo 1301969 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B1881959 : Blo 1301969 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B95131583 : Blo 1301969 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B10573811 : Blo 1301969 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B2930687 : Blo 1301969 2930687 := bstep (se 1 (by rfl) ⟨2198015, by rfl⟩ : syracuseStep 2930687 = 4396031) B4396031
theorem B14096855 : Blo 1301969 14096855 := bstep (se 1 (by rfl) ⟨10572641, by rfl⟩ : syracuseStep 14096855 = 21145283) B21145283
theorem B4692667 : Blo 1301969 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B6257657 : Blo 1301969 6257657 := bstep (se 2 (by rfl) ⟨2346621, by rfl⟩ : syracuseStep 6257657 = 4693243) B4693243
theorem B2931767 : Blo 1301969 2931767 := bstep (se 1 (by rfl) ⟨2198825, by rfl⟩ : syracuseStep 2931767 = 4397651) B4397651
theorem B6593723 : Blo 1301969 6593723 := bstep (se 1 (by rfl) ⟨4945292, by rfl⟩ : syracuseStep 6593723 = 9890585) B9890585
theorem B11124175 : Blo 1301969 11124175 := bstep (se 1 (by rfl) ⟨8343131, by rfl⟩ : syracuseStep 11124175 = 16686263) B16686263
theorem B1302175 : Blo 1301969 1302175 := bstep (se 1 (by rfl) ⟨976631, by rfl⟩ : syracuseStep 1302175 = 1953263) B1953263
theorem B2473831 : Blo 1301969 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B2932649 : Blo 1301969 2932649 := bstep (se 2 (by rfl) ⟨1099743, by rfl⟩ : syracuseStep 2932649 = 2199487) B2199487
theorem B1302767 : Blo 1301969 1302767 := bstep (se 1 (by rfl) ⟨977075, by rfl⟩ : syracuseStep 1302767 = 1954151) B1954151
theorem B1302847 : Blo 1301969 1302847 := bstep (se 1 (by rfl) ⟨977135, by rfl⟩ : syracuseStep 1302847 = 1954271) B1954271
theorem B1303167 : Blo 1301969 1303167 := bstep (se 1 (by rfl) ⟨977375, by rfl⟩ : syracuseStep 1303167 = 1954751) B1954751
theorem B1303271 : Blo 1301969 1303271 := bstep (se 1 (by rfl) ⟨977453, by rfl⟩ : syracuseStep 1303271 = 1954907) B1954907
theorem B1303367 : Blo 1301969 1303367 := bstep (se 1 (by rfl) ⟨977525, by rfl⟩ : syracuseStep 1303367 = 1955051) B1955051
theorem B4171771 : Blo 1301969 4171771 := bstep (se 1 (by rfl) ⟨3128828, by rfl⟩ : syracuseStep 4171771 = 6257657) B6257657
theorem B4394249 : Blo 1301969 4394249 := bstep (se 2 (by rfl) ⟨1647843, by rfl⟩ : syracuseStep 4394249 = 3295687) B3295687
theorem B23768453 : Blo 1301969 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B4763389 : Blo 1301969 4763389 := bstep (se 3 (by rfl) ⟨893135, by rfl⟩ : syracuseStep 4763389 = 1786271) B1786271
theorem B7049207 : Blo 1301969 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B1953791 : Blo 1301969 1953791 := bstep (se 1 (by rfl) ⟨1465343, by rfl⟩ : syracuseStep 1953791 = 2930687) B2930687
theorem B15855659 : Blo 1301969 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B14832233 : Blo 1301969 14832233 := bstep (se 2 (by rfl) ⟨5562087, by rfl⟩ : syracuseStep 14832233 = 11124175) B11124175
theorem B1954511 : Blo 1301969 1954511 := bstep (se 1 (by rfl) ⟨1465883, by rfl⟩ : syracuseStep 1954511 = 2931767) B2931767
theorem B4395815 : Blo 1301969 4395815 := bstep (se 1 (by rfl) ⟨3296861, by rfl⟩ : syracuseStep 4395815 = 6593723) B6593723
theorem B5018557 : Blo 1301969 5018557 := bstep (se 3 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 5018557 = 1881959) B1881959
theorem B3298441 : Blo 1301969 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B1955099 : Blo 1301969 1955099 := bstep (se 1 (by rfl) ⟨1466324, by rfl⟩ : syracuseStep 1955099 = 2932649) B2932649
theorem B2086975 : Blo 1301969 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B6256871 : Blo 1301969 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B6256889 : Blo 1301969 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B37591613 : Blo 1301969 37591613 := bstep (se 3 (by rfl) ⟨7048427, by rfl⟩ : syracuseStep 37591613 = 14096855) B14096855
theorem B63421055 : Blo 1301969 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B6774025 : Blo 1301969 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B1302271 : Blo 1301969 1302271 := bstep (se 1 (by rfl) ⟨976703, by rfl⟩ : syracuseStep 1302271 = 1953407) B1953407
theorem B9888155 : Blo 1301969 9888155 := bstep (se 1 (by rfl) ⟨7416116, by rfl⟩ : syracuseStep 9888155 = 14832233) B14832233
theorem B1303007 : Blo 1301969 1303007 := bstep (se 1 (by rfl) ⟨977255, by rfl⟩ : syracuseStep 1303007 = 1954511) B1954511
theorem B1303399 : Blo 1301969 1303399 := bstep (se 1 (by rfl) ⟨977549, by rfl⟩ : syracuseStep 1303399 = 1955099) B1955099
theorem B4171247 : Blo 1301969 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B4171259 : Blo 1301969 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B25061075 : Blo 1301969 25061075 := bstep (se 1 (by rfl) ⟨18795806, by rfl⟩ : syracuseStep 25061075 = 37591613) B37591613
theorem B42280703 : Blo 1301969 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B15845635 : Blo 1301969 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B6351185 : Blo 1301969 6351185 := bstep (se 2 (by rfl) ⟨2381694, by rfl⟩ : syracuseStep 6351185 = 4763389) B4763389
theorem B10570439 : Blo 1301969 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B9032033 : Blo 1301969 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B2929499 : Blo 1301969 2929499 := bstep (se 1 (by rfl) ⟨2197124, by rfl⟩ : syracuseStep 2929499 = 4394249) B4394249
theorem B4699471 : Blo 1301969 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B11130533 : Blo 1301969 11130533 := bstep (se 4 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 11130533 = 2086975) B2086975
theorem B2930543 : Blo 1301969 2930543 := bstep (se 1 (by rfl) ⟨2197907, by rfl⟩ : syracuseStep 2930543 = 4395815) B4395815
theorem B6691409 : Blo 1301969 6691409 := bstep (se 2 (by rfl) ⟨2509278, by rfl⟩ : syracuseStep 6691409 = 5018557) B5018557
theorem B4397921 : Blo 1301969 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B5562361 : Blo 1301969 5562361 := bstep (se 2 (by rfl) ⟨2085885, by rfl⟩ : syracuseStep 5562361 = 4171771) B4171771
theorem B1302527 : Blo 1301969 1302527 := bstep (se 1 (by rfl) ⟨976895, by rfl⟩ : syracuseStep 1302527 = 1953791) B1953791
theorem B21127513 : Blo 1301969 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B24085421 : Blo 1301969 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B7046959 : Blo 1301969 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B7416481 : Blo 1301969 7416481 := bstep (se 2 (by rfl) ⟨2781180, by rfl⟩ : syracuseStep 7416481 = 5562361) B5562361
theorem B1952999 : Blo 1301969 1952999 := bstep (se 1 (by rfl) ⟨1464749, by rfl⟩ : syracuseStep 1952999 = 2929499) B2929499
theorem B2780831 : Blo 1301969 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B2780839 : Blo 1301969 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B16707383 : Blo 1301969 16707383 := bstep (se 1 (by rfl) ⟨12530537, by rfl⟩ : syracuseStep 16707383 = 25061075) B25061075
theorem B1953695 : Blo 1301969 1953695 := bstep (se 1 (by rfl) ⟨1465271, by rfl⟩ : syracuseStep 1953695 = 2930543) B2930543
theorem B4460939 : Blo 1301969 4460939 := bstep (se 1 (by rfl) ⟨3345704, by rfl⟩ : syracuseStep 4460939 = 6691409) B6691409
theorem B6592103 : Blo 1301969 6592103 := bstep (se 1 (by rfl) ⟨4944077, by rfl⟩ : syracuseStep 6592103 = 9888155) B9888155
theorem B7420355 : Blo 1301969 7420355 := bstep (se 1 (by rfl) ⟨5565266, by rfl⟩ : syracuseStep 7420355 = 11130533) B11130533
theorem B28187135 : Blo 1301969 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B4234123 : Blo 1301969 4234123 := bstep (se 1 (by rfl) ⟨3175592, by rfl⟩ : syracuseStep 4234123 = 6351185) B6351185
theorem B6265961 : Blo 1301969 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B2931947 : Blo 1301969 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B2973959 : Blo 1301969 2973959 := bstep (se 1 (by rfl) ⟨2230469, by rfl⟩ : syracuseStep 2973959 = 4460939) B4460939
theorem B16056947 : Blo 1301969 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B9888641 : Blo 1301969 9888641 := bstep (se 2 (by rfl) ⟨3708240, by rfl⟩ : syracuseStep 9888641 = 7416481) B7416481
theorem B5645497 : Blo 1301969 5645497 := bstep (se 2 (by rfl) ⟨2117061, by rfl⟩ : syracuseStep 5645497 = 4234123) B4234123
theorem B7415549 : Blo 1301969 7415549 := bstep (se 3 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 7415549 = 2780831) B2780831
theorem B4394735 : Blo 1301969 4394735 := bstep (se 1 (by rfl) ⟨3296051, by rfl⟩ : syracuseStep 4394735 = 6592103) B6592103
theorem B1954631 : Blo 1301969 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B3707785 : Blo 1301969 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B11138255 : Blo 1301969 11138255 := bstep (se 1 (by rfl) ⟨8353691, by rfl⟩ : syracuseStep 11138255 = 16707383) B16707383
theorem B28170017 : Blo 1301969 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B4946903 : Blo 1301969 4946903 := bstep (se 1 (by rfl) ⟨3710177, by rfl⟩ : syracuseStep 4946903 = 7420355) B7420355
theorem B18791423 : Blo 1301969 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B4177307 : Blo 1301969 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B1301999 : Blo 1301969 1301999 := bstep (se 1 (by rfl) ⟨976499, by rfl⟩ : syracuseStep 1301999 = 1952999) B1952999
theorem B9395945 : Blo 1301969 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B1302463 : Blo 1301969 1302463 := bstep (se 1 (by rfl) ⟨976847, by rfl⟩ : syracuseStep 1302463 = 1953695) B1953695
theorem B1982639 : Blo 1301969 1982639 := bstep (se 1 (by rfl) ⟨1486979, by rfl⟩ : syracuseStep 1982639 = 2973959) B2973959
theorem B1303087 : Blo 1301969 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B12527615 : Blo 1301969 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B7425503 : Blo 1301969 7425503 := bstep (se 1 (by rfl) ⟨5569127, by rfl⟩ : syracuseStep 7425503 = 11138255) B11138255
theorem B4943699 : Blo 1301969 4943699 := bstep (se 1 (by rfl) ⟨3707774, by rfl⟩ : syracuseStep 4943699 = 7415549) B7415549
theorem B4943713 : Blo 1301969 4943713 := bstep (se 2 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 4943713 = 3707785) B3707785
theorem B18780011 : Blo 1301969 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B3297935 : Blo 1301969 3297935 := bstep (se 1 (by rfl) ⟨2473451, by rfl⟩ : syracuseStep 3297935 = 4946903) B4946903
theorem B6263963 : Blo 1301969 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B2929823 : Blo 1301969 2929823 := bstep (se 1 (by rfl) ⟨2197367, by rfl⟩ : syracuseStep 2929823 = 4394735) B4394735
theorem B10704631 : Blo 1301969 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B6592427 : Blo 1301969 6592427 := bstep (se 1 (by rfl) ⟨4944320, by rfl⟩ : syracuseStep 6592427 = 9888641) B9888641
theorem B7527329 : Blo 1301969 7527329 := bstep (se 2 (by rfl) ⟨2822748, by rfl⟩ : syracuseStep 7527329 = 5645497) B5645497
theorem B2784871 : Blo 1301969 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B14852645 : Blo 1301969 14852645 := bstep (se 4 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 14852645 = 2784871) B2784871
theorem B4950335 : Blo 1301969 4950335 := bstep (se 1 (by rfl) ⟨3712751, by rfl⟩ : syracuseStep 4950335 = 7425503) B7425503
theorem B14272841 : Blo 1301969 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B3295799 : Blo 1301969 3295799 := bstep (se 1 (by rfl) ⟨2471849, by rfl⟩ : syracuseStep 3295799 = 4943699) B4943699
theorem B12520007 : Blo 1301969 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B1321759 : Blo 1301969 1321759 := bstep (se 1 (by rfl) ⟨991319, by rfl⟩ : syracuseStep 1321759 = 1982639) B1982639
theorem B2198623 : Blo 1301969 2198623 := bstep (se 1 (by rfl) ⟨1648967, by rfl⟩ : syracuseStep 2198623 = 3297935) B3297935
theorem B1953215 : Blo 1301969 1953215 := bstep (se 1 (by rfl) ⟨1464911, by rfl⟩ : syracuseStep 1953215 = 2929823) B2929823
theorem B4394951 : Blo 1301969 4394951 := bstep (se 1 (by rfl) ⟨3296213, by rfl⟩ : syracuseStep 4394951 = 6592427) B6592427
theorem B8351743 : Blo 1301969 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B5018219 : Blo 1301969 5018219 := bstep (se 1 (by rfl) ⟨3763664, by rfl⟩ : syracuseStep 5018219 = 7527329) B7527329
theorem B6591617 : Blo 1301969 6591617 := bstep (se 2 (by rfl) ⟨2471856, by rfl⟩ : syracuseStep 6591617 = 4943713) B4943713
theorem B4175975 : Blo 1301969 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B1762345 : Blo 1301969 1762345 := bstep (se 2 (by rfl) ⟨660879, by rfl⟩ : syracuseStep 1762345 = 1321759) B1321759
theorem B2197199 : Blo 1301969 2197199 := bstep (se 1 (by rfl) ⟨1647899, by rfl⟩ : syracuseStep 2197199 = 3295799) B3295799
theorem B11135657 : Blo 1301969 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B3345479 : Blo 1301969 3345479 := bstep (se 1 (by rfl) ⟨2509109, by rfl⟩ : syracuseStep 3345479 = 5018219) B5018219
theorem B4394411 : Blo 1301969 4394411 := bstep (se 1 (by rfl) ⟨3295808, by rfl⟩ : syracuseStep 4394411 = 6591617) B6591617
theorem B9515227 : Blo 1301969 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B2929967 : Blo 1301969 2929967 := bstep (se 1 (by rfl) ⟨2197475, by rfl⟩ : syracuseStep 2929967 = 4394951) B4394951
theorem B9901763 : Blo 1301969 9901763 := bstep (se 1 (by rfl) ⟨7426322, by rfl⟩ : syracuseStep 9901763 = 14852645) B14852645
theorem B2783983 : Blo 1301969 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B2931497 : Blo 1301969 2931497 := bstep (se 2 (by rfl) ⟨1099311, by rfl⟩ : syracuseStep 2931497 = 2198623) B2198623
theorem B3300223 : Blo 1301969 3300223 := bstep (se 1 (by rfl) ⟨2475167, by rfl⟩ : syracuseStep 3300223 = 4950335) B4950335
theorem B8346671 : Blo 1301969 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B1302143 : Blo 1301969 1302143 := bstep (se 1 (by rfl) ⟨976607, by rfl⟩ : syracuseStep 1302143 = 1953215) B1953215
theorem B3711977 : Blo 1301969 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B4400297 : Blo 1301969 4400297 := bstep (se 2 (by rfl) ⟨1650111, by rfl⟩ : syracuseStep 4400297 = 3300223) B3300223
theorem B7423771 : Blo 1301969 7423771 := bstep (se 1 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 7423771 = 11135657) B11135657
theorem B5564447 : Blo 1301969 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B2230319 : Blo 1301969 2230319 := bstep (se 1 (by rfl) ⟨1672739, by rfl⟩ : syracuseStep 2230319 = 3345479) B3345479
theorem B1953311 : Blo 1301969 1953311 := bstep (se 1 (by rfl) ⟨1464983, by rfl⟩ : syracuseStep 1953311 = 2929967) B2929967
theorem B1954331 : Blo 1301969 1954331 := bstep (se 1 (by rfl) ⟨1465748, by rfl⟩ : syracuseStep 1954331 = 2931497) B2931497
theorem B2929607 : Blo 1301969 2929607 := bstep (se 1 (by rfl) ⟨2197205, by rfl⟩ : syracuseStep 2929607 = 4394411) B4394411
theorem B12686969 : Blo 1301969 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B6601175 : Blo 1301969 6601175 := bstep (se 1 (by rfl) ⟨4950881, by rfl⟩ : syracuseStep 6601175 = 9901763) B9901763
theorem B1464799 : Blo 1301969 1464799 := bstep (se 1 (by rfl) ⟨1098599, by rfl⟩ : syracuseStep 1464799 = 2197199) B2197199
theorem B2349793 : Blo 1301969 2349793 := bstep (se 2 (by rfl) ⟨881172, by rfl⟩ : syracuseStep 2349793 = 1762345) B1762345
theorem B1302887 : Blo 1301969 1302887 := bstep (se 1 (by rfl) ⟨977165, by rfl⟩ : syracuseStep 1302887 = 1954331) B1954331
theorem B2474651 : Blo 1301969 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B2933531 : Blo 1301969 2933531 := bstep (se 1 (by rfl) ⟨2200148, by rfl⟩ : syracuseStep 2933531 = 4400297) B4400297
theorem B4400783 : Blo 1301969 4400783 := bstep (se 1 (by rfl) ⟨3300587, by rfl⟩ : syracuseStep 4400783 = 6601175) B6601175
theorem B9898361 : Blo 1301969 9898361 := bstep (se 2 (by rfl) ⟨3711885, by rfl⟩ : syracuseStep 9898361 = 7423771) B7423771
theorem B1953065 : Blo 1301969 1953065 := bstep (se 2 (by rfl) ⟨732399, by rfl⟩ : syracuseStep 1953065 = 1464799) B1464799
theorem B1953071 : Blo 1301969 1953071 := bstep (se 1 (by rfl) ⟨1464803, by rfl⟩ : syracuseStep 1953071 = 2929607) B2929607
theorem B8457979 : Blo 1301969 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B1486879 : Blo 1301969 1486879 := bstep (se 1 (by rfl) ⟨1115159, by rfl⟩ : syracuseStep 1486879 = 2230319) B2230319
theorem B12532229 : Blo 1301969 12532229 := bstep (se 4 (by rfl) ⟨1174896, by rfl⟩ : syracuseStep 12532229 = 2349793) B2349793
theorem B3709631 : Blo 1301969 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B1302207 : Blo 1301969 1302207 := bstep (se 1 (by rfl) ⟨976655, by rfl⟩ : syracuseStep 1302207 = 1953311) B1953311
theorem B7930021 : Blo 1301969 7930021 := bstep (se 4 (by rfl) ⟨743439, by rfl⟩ : syracuseStep 7930021 = 1486879) B1486879
theorem B2933855 : Blo 1301969 2933855 := bstep (se 1 (by rfl) ⟨2200391, by rfl⟩ : syracuseStep 2933855 = 4400783) B4400783
theorem B6598907 : Blo 1301969 6598907 := bstep (se 1 (by rfl) ⟨4949180, by rfl⟩ : syracuseStep 6598907 = 9898361) B9898361
theorem B6599069 : Blo 1301969 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B11277305 : Blo 1301969 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B1955687 : Blo 1301969 1955687 := bstep (se 1 (by rfl) ⟨1466765, by rfl⟩ : syracuseStep 1955687 = 2933531) B2933531
theorem B8354819 : Blo 1301969 8354819 := bstep (se 1 (by rfl) ⟨6266114, by rfl⟩ : syracuseStep 8354819 = 12532229) B12532229
theorem B2473087 : Blo 1301969 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B1302043 : Blo 1301969 1302043 := bstep (se 1 (by rfl) ⟨976532, by rfl⟩ : syracuseStep 1302043 = 1953065) B1953065
theorem B1302047 : Blo 1301969 1302047 := bstep (se 1 (by rfl) ⟨976535, by rfl⟩ : syracuseStep 1302047 = 1953071) B1953071
theorem B4399271 : Blo 1301969 4399271 := bstep (se 1 (by rfl) ⟨3299453, by rfl⟩ : syracuseStep 4399271 = 6598907) B6598907
theorem B4399379 : Blo 1301969 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B1303791 : Blo 1301969 1303791 := bstep (se 1 (by rfl) ⟨977843, by rfl⟩ : syracuseStep 1303791 = 1955687) B1955687
theorem B3297449 : Blo 1301969 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B10573361 : Blo 1301969 10573361 := bstep (se 2 (by rfl) ⟨3965010, by rfl⟩ : syracuseStep 10573361 = 7930021) B7930021
theorem B7518203 : Blo 1301969 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B1955903 : Blo 1301969 1955903 := bstep (se 1 (by rfl) ⟨1466927, by rfl⟩ : syracuseStep 1955903 = 2933855) B2933855
theorem B5569879 : Blo 1301969 5569879 := bstep (se 1 (by rfl) ⟨4177409, by rfl⟩ : syracuseStep 5569879 = 8354819) B8354819
theorem B2932847 : Blo 1301969 2932847 := bstep (se 1 (by rfl) ⟨2199635, by rfl⟩ : syracuseStep 2932847 = 4399271) B4399271
theorem B2932919 : Blo 1301969 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B1303935 : Blo 1301969 1303935 := bstep (se 1 (by rfl) ⟨977951, by rfl⟩ : syracuseStep 1303935 = 1955903) B1955903
theorem B2198299 : Blo 1301969 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B7048907 : Blo 1301969 7048907 := bstep (se 1 (by rfl) ⟨5286680, by rfl⟩ : syracuseStep 7048907 = 10573361) B10573361
theorem B7426505 : Blo 1301969 7426505 := bstep (se 2 (by rfl) ⟨2784939, by rfl⟩ : syracuseStep 7426505 = 5569879) B5569879
theorem B5012135 : Blo 1301969 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B4951003 : Blo 1301969 4951003 := bstep (se 1 (by rfl) ⟨3713252, by rfl⟩ : syracuseStep 4951003 = 7426505) B7426505
theorem B4699271 : Blo 1301969 4699271 := bstep (se 1 (by rfl) ⟨3524453, by rfl⟩ : syracuseStep 4699271 = 7048907) B7048907
theorem B1955231 : Blo 1301969 1955231 := bstep (se 1 (by rfl) ⟨1466423, by rfl⟩ : syracuseStep 1955231 = 2932847) B2932847
theorem B1955279 : Blo 1301969 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B2931065 : Blo 1301969 2931065 := bstep (se 2 (by rfl) ⟨1099149, by rfl⟩ : syracuseStep 2931065 = 2198299) B2198299
theorem B3341423 : Blo 1301969 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B1303487 : Blo 1301969 1303487 := bstep (se 1 (by rfl) ⟨977615, by rfl⟩ : syracuseStep 1303487 = 1955231) B1955231
theorem B1303519 : Blo 1301969 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B3132847 : Blo 1301969 3132847 := bstep (se 1 (by rfl) ⟨2349635, by rfl⟩ : syracuseStep 3132847 = 4699271) B4699271
theorem B1954043 : Blo 1301969 1954043 := bstep (se 1 (by rfl) ⟨1465532, by rfl⟩ : syracuseStep 1954043 = 2931065) B2931065
theorem B8910461 : Blo 1301969 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B6601337 : Blo 1301969 6601337 := bstep (se 2 (by rfl) ⟨2475501, by rfl⟩ : syracuseStep 6601337 = 4951003) B4951003
theorem B1302695 : Blo 1301969 1302695 := bstep (se 1 (by rfl) ⟨977021, by rfl⟩ : syracuseStep 1302695 = 1954043) B1954043
theorem B5940307 : Blo 1301969 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B4400891 : Blo 1301969 4400891 := bstep (se 1 (by rfl) ⟨3300668, by rfl⟩ : syracuseStep 4400891 = 6601337) B6601337
theorem B4177129 : Blo 1301969 4177129 := bstep (se 2 (by rfl) ⟨1566423, by rfl⟩ : syracuseStep 4177129 = 3132847) B3132847
theorem B2933927 : Blo 1301969 2933927 := bstep (se 1 (by rfl) ⟨2200445, by rfl⟩ : syracuseStep 2933927 = 4400891) B4400891
theorem B7920409 : Blo 1301969 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B5569505 : Blo 1301969 5569505 := bstep (se 2 (by rfl) ⟨2088564, by rfl⟩ : syracuseStep 5569505 = 4177129) B4177129
theorem B10560545 : Blo 1301969 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B3713003 : Blo 1301969 3713003 := bstep (se 1 (by rfl) ⟨2784752, by rfl⟩ : syracuseStep 3713003 = 5569505) B5569505
theorem B1955951 : Blo 1301969 1955951 := bstep (se 1 (by rfl) ⟨1466963, by rfl⟩ : syracuseStep 1955951 = 2933927) B2933927
theorem B2475335 : Blo 1301969 2475335 := bstep (se 1 (by rfl) ⟨1856501, by rfl⟩ : syracuseStep 2475335 = 3713003) B3713003
theorem B1303967 : Blo 1301969 1303967 := bstep (se 1 (by rfl) ⟨977975, by rfl⟩ : syracuseStep 1303967 = 1955951) B1955951
theorem B7040363 : Blo 1301969 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B1650223 : Blo 1301969 1650223 := bstep (se 1 (by rfl) ⟨1237667, by rfl⟩ : syracuseStep 1650223 = 2475335) B2475335
theorem B18774301 : Blo 1301969 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B2200297 : Blo 1301969 2200297 := bstep (se 2 (by rfl) ⟨825111, by rfl⟩ : syracuseStep 2200297 = 1650223) B1650223
theorem B25032401 : Blo 1301969 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B2933729 : Blo 1301969 2933729 := bstep (se 2 (by rfl) ⟨1100148, by rfl⟩ : syracuseStep 2933729 = 2200297) B2200297
theorem B16688267 : Blo 1301969 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B11125511 : Blo 1301969 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B1955819 : Blo 1301969 1955819 := bstep (se 1 (by rfl) ⟨1466864, by rfl⟩ : syracuseStep 1955819 = 2933729) B2933729
theorem B1303879 : Blo 1301969 1303879 := bstep (se 1 (by rfl) ⟨977909, by rfl⟩ : syracuseStep 1303879 = 1955819) B1955819
theorem B7417007 : Blo 1301969 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B4944671 : Blo 1301969 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B3296447 : Blo 1301969 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B2197631 : Blo 1301969 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B1465087 : Blo 1301969 1465087 := bstep (se 1 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 1465087 = 2197631) B2197631
theorem B1953449 : Blo 1301969 1953449 := bstep (se 2 (by rfl) ⟨732543, by rfl⟩ : syracuseStep 1953449 = 1465087) B1465087
theorem B1302299 : Blo 1301969 1302299 := bstep (se 1 (by rfl) ⟨976724, by rfl⟩ : syracuseStep 1302299 = 1953449) B1953449

theorem C0 (j : ℕ) (h1 : 325492 ≤ j) (h2 : j ≤ 325991) : Blo 1301969 (4 * j + 3) := by
  interval_cases j
  · exact B1301971
  · exact B1301975
  · exact B1301979
  · exact B1301983
  · exact B1301987
  · exact B1301991
  · exact B1301995
  · exact B1301999
  · exact B1302003
  · exact B1302007
  · exact B1302011
  · exact B1302015
  · exact B1302019
  · exact B1302023
  · exact B1302027
  · exact B1302031
  · exact B1302035
  · exact B1302039
  · exact B1302043
  · exact B1302047
  · exact B1302051
  · exact B1302055
  · exact B1302059
  · exact B1302063
  · exact B1302067
  · exact B1302071
  · exact B1302075
  · exact B1302079
  · exact B1302083
  · exact B1302087
  · exact B1302091
  · exact B1302095
  · exact B1302099
  · exact B1302103
  · exact B1302107
  · exact B1302111
  · exact B1302115
  · exact B1302119
  · exact B1302123
  · exact B1302127
  · exact B1302131
  · exact B1302135
  · exact B1302139
  · exact B1302143
  · exact B1302147
  · exact B1302151
  · exact B1302155
  · exact B1302159
  · exact B1302163
  · exact B1302167
  · exact B1302171
  · exact B1302175
  · exact B1302179
  · exact B1302183
  · exact B1302187
  · exact B1302191
  · exact B1302195
  · exact B1302199
  · exact B1302203
  · exact B1302207
  · exact B1302211
  · exact B1302215
  · exact B1302219
  · exact B1302223
  · exact B1302227
  · exact B1302231
  · exact B1302235
  · exact B1302239
  · exact B1302243
  · exact B1302247
  · exact B1302251
  · exact B1302255
  · exact B1302259
  · exact B1302263
  · exact B1302267
  · exact B1302271
  · exact B1302275
  · exact B1302279
  · exact B1302283
  · exact B1302287
  · exact B1302291
  · exact B1302295
  · exact B1302299
  · exact B1302303
  · exact B1302307
  · exact B1302311
  · exact B1302315
  · exact B1302319
  · exact B1302323
  · exact B1302327
  · exact B1302331
  · exact B1302335
  · exact B1302339
  · exact B1302343
  · exact B1302347
  · exact B1302351
  · exact B1302355
  · exact B1302359
  · exact B1302363
  · exact B1302367
  · exact B1302371
  · exact B1302375
  · exact B1302379
  · exact B1302383
  · exact B1302387
  · exact B1302391
  · exact B1302395
  · exact B1302399
  · exact B1302403
  · exact B1302407
  · exact B1302411
  · exact B1302415
  · exact B1302419
  · exact B1302423
  · exact B1302427
  · exact B1302431
  · exact B1302435
  · exact B1302439
  · exact B1302443
  · exact B1302447
  · exact B1302451
  · exact B1302455
  · exact B1302459
  · exact B1302463
  · exact B1302467
  · exact B1302471
  · exact B1302475
  · exact B1302479
  · exact B1302483
  · exact B1302487
  · exact B1302491
  · exact B1302495
  · exact B1302499
  · exact B1302503
  · exact B1302507
  · exact B1302511
  · exact B1302515
  · exact B1302519
  · exact B1302523
  · exact B1302527
  · exact B1302531
  · exact B1302535
  · exact B1302539
  · exact B1302543
  · exact B1302547
  · exact B1302551
  · exact B1302555
  · exact B1302559
  · exact B1302563
  · exact B1302567
  · exact B1302571
  · exact B1302575
  · exact B1302579
  · exact B1302583
  · exact B1302587
  · exact B1302591
  · exact B1302595
  · exact B1302599
  · exact B1302603
  · exact B1302607
  · exact B1302611
  · exact B1302615
  · exact B1302619
  · exact B1302623
  · exact B1302627
  · exact B1302631
  · exact B1302635
  · exact B1302639
  · exact B1302643
  · exact B1302647
  · exact B1302651
  · exact B1302655
  · exact B1302659
  · exact B1302663
  · exact B1302667
  · exact B1302671
  · exact B1302675
  · exact B1302679
  · exact B1302683
  · exact B1302687
  · exact B1302691
  · exact B1302695
  · exact B1302699
  · exact B1302703
  · exact B1302707
  · exact B1302711
  · exact B1302715
  · exact B1302719
  · exact B1302723
  · exact B1302727
  · exact B1302731
  · exact B1302735
  · exact B1302739
  · exact B1302743
  · exact B1302747
  · exact B1302751
  · exact B1302755
  · exact B1302759
  · exact B1302763
  · exact B1302767
  · exact B1302771
  · exact B1302775
  · exact B1302779
  · exact B1302783
  · exact B1302787
  · exact B1302791
  · exact B1302795
  · exact B1302799
  · exact B1302803
  · exact B1302807
  · exact B1302811
  · exact B1302815
  · exact B1302819
  · exact B1302823
  · exact B1302827
  · exact B1302831
  · exact B1302835
  · exact B1302839
  · exact B1302843
  · exact B1302847
  · exact B1302851
  · exact B1302855
  · exact B1302859
  · exact B1302863
  · exact B1302867
  · exact B1302871
  · exact B1302875
  · exact B1302879
  · exact B1302883
  · exact B1302887
  · exact B1302891
  · exact B1302895
  · exact B1302899
  · exact B1302903
  · exact B1302907
  · exact B1302911
  · exact B1302915
  · exact B1302919
  · exact B1302923
  · exact B1302927
  · exact B1302931
  · exact B1302935
  · exact B1302939
  · exact B1302943
  · exact B1302947
  · exact B1302951
  · exact B1302955
  · exact B1302959
  · exact B1302963
  · exact B1302967
  · exact B1302971
  · exact B1302975
  · exact B1302979
  · exact B1302983
  · exact B1302987
  · exact B1302991
  · exact B1302995
  · exact B1302999
  · exact B1303003
  · exact B1303007
  · exact B1303011
  · exact B1303015
  · exact B1303019
  · exact B1303023
  · exact B1303027
  · exact B1303031
  · exact B1303035
  · exact B1303039
  · exact B1303043
  · exact B1303047
  · exact B1303051
  · exact B1303055
  · exact B1303059
  · exact B1303063
  · exact B1303067
  · exact B1303071
  · exact B1303075
  · exact B1303079
  · exact B1303083
  · exact B1303087
  · exact B1303091
  · exact B1303095
  · exact B1303099
  · exact B1303103
  · exact B1303107
  · exact B1303111
  · exact B1303115
  · exact B1303119
  · exact B1303123
  · exact B1303127
  · exact B1303131
  · exact B1303135
  · exact B1303139
  · exact B1303143
  · exact B1303147
  · exact B1303151
  · exact B1303155
  · exact B1303159
  · exact B1303163
  · exact B1303167
  · exact B1303171
  · exact B1303175
  · exact B1303179
  · exact B1303183
  · exact B1303187
  · exact B1303191
  · exact B1303195
  · exact B1303199
  · exact B1303203
  · exact B1303207
  · exact B1303211
  · exact B1303215
  · exact B1303219
  · exact B1303223
  · exact B1303227
  · exact B1303231
  · exact B1303235
  · exact B1303239
  · exact B1303243
  · exact B1303247
  · exact B1303251
  · exact B1303255
  · exact B1303259
  · exact B1303263
  · exact B1303267
  · exact B1303271
  · exact B1303275
  · exact B1303279
  · exact B1303283
  · exact B1303287
  · exact B1303291
  · exact B1303295
  · exact B1303299
  · exact B1303303
  · exact B1303307
  · exact B1303311
  · exact B1303315
  · exact B1303319
  · exact B1303323
  · exact B1303327
  · exact B1303331
  · exact B1303335
  · exact B1303339
  · exact B1303343
  · exact B1303347
  · exact B1303351
  · exact B1303355
  · exact B1303359
  · exact B1303363
  · exact B1303367
  · exact B1303371
  · exact B1303375
  · exact B1303379
  · exact B1303383
  · exact B1303387
  · exact B1303391
  · exact B1303395
  · exact B1303399
  · exact B1303403
  · exact B1303407
  · exact B1303411
  · exact B1303415
  · exact B1303419
  · exact B1303423
  · exact B1303427
  · exact B1303431
  · exact B1303435
  · exact B1303439
  · exact B1303443
  · exact B1303447
  · exact B1303451
  · exact B1303455
  · exact B1303459
  · exact B1303463
  · exact B1303467
  · exact B1303471
  · exact B1303475
  · exact B1303479
  · exact B1303483
  · exact B1303487
  · exact B1303491
  · exact B1303495
  · exact B1303499
  · exact B1303503
  · exact B1303507
  · exact B1303511
  · exact B1303515
  · exact B1303519
  · exact B1303523
  · exact B1303527
  · exact B1303531
  · exact B1303535
  · exact B1303539
  · exact B1303543
  · exact B1303547
  · exact B1303551
  · exact B1303555
  · exact B1303559
  · exact B1303563
  · exact B1303567
  · exact B1303571
  · exact B1303575
  · exact B1303579
  · exact B1303583
  · exact B1303587
  · exact B1303591
  · exact B1303595
  · exact B1303599
  · exact B1303603
  · exact B1303607
  · exact B1303611
  · exact B1303615
  · exact B1303619
  · exact B1303623
  · exact B1303627
  · exact B1303631
  · exact B1303635
  · exact B1303639
  · exact B1303643
  · exact B1303647
  · exact B1303651
  · exact B1303655
  · exact B1303659
  · exact B1303663
  · exact B1303667
  · exact B1303671
  · exact B1303675
  · exact B1303679
  · exact B1303683
  · exact B1303687
  · exact B1303691
  · exact B1303695
  · exact B1303699
  · exact B1303703
  · exact B1303707
  · exact B1303711
  · exact B1303715
  · exact B1303719
  · exact B1303723
  · exact B1303727
  · exact B1303731
  · exact B1303735
  · exact B1303739
  · exact B1303743
  · exact B1303747
  · exact B1303751
  · exact B1303755
  · exact B1303759
  · exact B1303763
  · exact B1303767
  · exact B1303771
  · exact B1303775
  · exact B1303779
  · exact B1303783
  · exact B1303787
  · exact B1303791
  · exact B1303795
  · exact B1303799
  · exact B1303803
  · exact B1303807
  · exact B1303811
  · exact B1303815
  · exact B1303819
  · exact B1303823
  · exact B1303827
  · exact B1303831
  · exact B1303835
  · exact B1303839
  · exact B1303843
  · exact B1303847
  · exact B1303851
  · exact B1303855
  · exact B1303859
  · exact B1303863
  · exact B1303867
  · exact B1303871
  · exact B1303875
  · exact B1303879
  · exact B1303883
  · exact B1303887
  · exact B1303891
  · exact B1303895
  · exact B1303899
  · exact B1303903
  · exact B1303907
  · exact B1303911
  · exact B1303915
  · exact B1303919
  · exact B1303923
  · exact B1303927
  · exact B1303931
  · exact B1303935
  · exact B1303939
  · exact B1303943
  · exact B1303947
  · exact B1303951
  · exact B1303955
  · exact B1303959
  · exact B1303963
  · exact B1303967

theorem solution (m : ℕ) (hlo : 1301969 ≤ m) (hhi : m ≤ 1303969) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 325492 ≤ j := by omega
    have hj2 : j ≤ 325991 := by omega
    have hb : Blo 1301969 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
