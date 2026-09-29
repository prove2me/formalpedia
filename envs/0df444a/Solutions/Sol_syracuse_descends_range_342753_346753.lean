-- Prove2me | solution 1 for syracuse_descends_range_342753_346753
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:34.353203+00:00
-- url     : https://prove2.me/submissions/c6744613-5a32-49c6-87d6-2f1191e93fe5

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


theorem B622741 : Blo 342753 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B1474757 : Blo 342753 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B983285 : Blo 342753 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B1245509 : Blo 342753 1245509 := bbase (se 4 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 1245509 = 233533) (by norm_num)
theorem B491933 : Blo 342753 491933 := bbase (se 3 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 491933 = 184475) (by norm_num)
theorem B1737125 : Blo 342753 1737125 := bbase (se 4 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 1737125 = 325711) (by norm_num)
theorem B655789 : Blo 342753 655789 := bbase (se 3 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 655789 = 245921) (by norm_num)
theorem B655933 : Blo 342753 655933 := bbase (se 3 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 655933 = 245975) (by norm_num)
theorem B1311349 : Blo 342753 1311349 := bbase (se 5 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 1311349 = 122939) (by norm_num)
theorem B6292181 : Blo 342753 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B656093 : Blo 342753 656093 := bbase (se 3 (by rfl) ⟨123017, by rfl⟩ : syracuseStep 656093 = 246035) (by norm_num)
theorem B394069 : Blo 342753 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B656237 : Blo 342753 656237 := bbase (se 3 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 656237 = 246089) (by norm_num)
theorem B1311653 : Blo 342753 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B623533 : Blo 342753 623533 := bbase (se 3 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 623533 = 233825) (by norm_num)
theorem B492485 : Blo 342753 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B787573 : Blo 342753 787573 := bbase (se 5 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 787573 = 73835) (by norm_num)
theorem B656525 : Blo 342753 656525 := bbase (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) (by norm_num)
theorem B5276821 : Blo 342753 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B623837 : Blo 342753 623837 := bbase (se 3 (by rfl) ⟨116969, by rfl⟩ : syracuseStep 623837 = 233939) (by norm_num)
theorem B591077 : Blo 342753 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B656677 : Blo 342753 656677 := bbase (se 4 (by rfl) ⟨61563, by rfl⟩ : syracuseStep 656677 = 123127) (by norm_num)
theorem B1574213 : Blo 342753 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B984469 : Blo 342753 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B624125 : Blo 342753 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B984629 : Blo 342753 984629 := bbase (se 5 (by rfl) ⟨46154, by rfl⟩ : syracuseStep 984629 = 92309) (by norm_num)
theorem B656981 : Blo 342753 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B1738421 : Blo 342753 1738421 := bbase (se 5 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 1738421 = 162977) (by norm_num)
theorem B493237 : Blo 342753 493237 := bbase (se 5 (by rfl) ⟨23120, by rfl⟩ : syracuseStep 493237 = 46241) (by norm_num)
theorem B984869 : Blo 342753 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B985061 : Blo 342753 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B2197525 : Blo 342753 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B788741 : Blo 342753 788741 := bbase (se 4 (by rfl) ⟨73944, by rfl⟩ : syracuseStep 788741 = 147889) (by norm_num)
theorem B2787605 : Blo 342753 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B526637 : Blo 342753 526637 := bbase (se 3 (by rfl) ⟨98744, by rfl⟩ : syracuseStep 526637 = 197489) (by norm_num)
theorem B657733 : Blo 342753 657733 := bbase (se 4 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 657733 = 123325) (by norm_num)
theorem B1477045 : Blo 342753 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1051093 : Blo 342753 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B657877 : Blo 342753 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B526933 : Blo 342753 526933 := bbase (se 8 (by rfl) ⟨3087, by rfl⟩ : syracuseStep 526933 = 6175) (by norm_num)
theorem B658037 : Blo 342753 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B658181 : Blo 342753 658181 := bbase (se 4 (by rfl) ⟨61704, by rfl⟩ : syracuseStep 658181 = 123409) (by norm_num)
theorem B1739717 : Blo 342753 1739717 := bbase (se 4 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 1739717 = 326197) (by norm_num)
theorem B986053 : Blo 342753 986053 := bbase (se 4 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 986053 = 184885) (by norm_num)
theorem B1313765 : Blo 342753 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B1314053 : Blo 342753 1314053 := bbase (se 4 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 1314053 = 246385) (by norm_num)
theorem B2624885 : Blo 342753 2624885 := bbase (se 5 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 2624885 = 246083) (by norm_num)
theorem B1248709 : Blo 342753 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B1576421 : Blo 342753 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B822917 : Blo 342753 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B888461 : Blo 342753 888461 := bbase (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) (by norm_num)
theorem B397153 : Blo 342753 397153 := bbase (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) (by norm_num)
theorem B1118069 : Blo 342753 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B757621 : Blo 342753 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B1478533 : Blo 342753 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1478549 : Blo 342753 1478549 := bbase (se 6 (by rfl) ⟨34653, by rfl⟩ : syracuseStep 1478549 = 69307) (by norm_num)
theorem B430057 : Blo 342753 430057 := bbase (se 2 (by rfl) ⟨161271, by rfl⟩ : syracuseStep 430057 = 322543) (by norm_num)
theorem B987157 : Blo 342753 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B1741013 : Blo 342753 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B3313973 : Blo 342753 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B1315237 : Blo 342753 1315237 := bbase (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) (by norm_num)
theorem B463277 : Blo 342753 463277 := bbase (se 3 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 463277 = 173729) (by norm_num)
theorem B1249717 : Blo 342753 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B823765 : Blo 342753 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B463325 : Blo 342753 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B823861 : Blo 342753 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B1315541 : Blo 342753 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B2495285 : Blo 342753 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B1971125 : Blo 342753 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B824381 : Blo 342753 824381 := bbase (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) (by norm_num)
theorem B2495573 : Blo 342753 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B463973 : Blo 342753 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B1742309 : Blo 342753 1742309 := bbase (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) (by norm_num)
theorem B824909 : Blo 342753 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B366169 : Blo 342753 366169 := bbase (se 2 (by rfl) ⟨137313, by rfl⟩ : syracuseStep 366169 = 274627) (by norm_num)
theorem B366229 : Blo 342753 366229 := bbase (se 6 (by rfl) ⟨8583, by rfl⟩ : syracuseStep 366229 = 17167) (by norm_num)
theorem B825149 : Blo 342753 825149 := bbase (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) (by norm_num)
theorem B2201525 : Blo 342753 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B366545 : Blo 342753 366545 := bbase (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) (by norm_num)
theorem B1972309 : Blo 342753 1972309 := bbase (se 8 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 1972309 = 23113) (by norm_num)
theorem B1480805 : Blo 342753 1480805 := bbase (se 4 (by rfl) ⟨138825, by rfl⟩ : syracuseStep 1480805 = 277651) (by norm_num)
theorem B366989 : Blo 342753 366989 := bbase (se 3 (by rfl) ⟨68810, by rfl⟩ : syracuseStep 366989 = 137621) (by norm_num)
theorem B367049 : Blo 342753 367049 := bbase (se 2 (by rfl) ⟨137643, by rfl⟩ : syracuseStep 367049 = 275287) (by norm_num)
theorem B662069 : Blo 342753 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B367177 : Blo 342753 367177 := bbase (se 2 (by rfl) ⟨137691, by rfl⟩ : syracuseStep 367177 = 275383) (by norm_num)
theorem B1743605 : Blo 342753 1743605 := bbase (se 5 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 1743605 = 163463) (by norm_num)
theorem B1579925 : Blo 342753 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B2956277 : Blo 342753 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B367621 : Blo 342753 367621 := bbase (se 4 (by rfl) ⟨34464, by rfl⟩ : syracuseStep 367621 = 68929) (by norm_num)
theorem B367741 : Blo 342753 367741 := bbase (se 3 (by rfl) ⟨68951, by rfl⟩ : syracuseStep 367741 = 137903) (by norm_num)
theorem B38083925 : Blo 342753 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B367993 : Blo 342753 367993 := bbase (se 2 (by rfl) ⟨137997, by rfl⟩ : syracuseStep 367993 = 275995) (by norm_num)
theorem B367997 : Blo 342753 367997 := bbase (se 3 (by rfl) ⟨68999, by rfl⟩ : syracuseStep 367997 = 137999) (by norm_num)
theorem B990677 : Blo 342753 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B826861 : Blo 342753 826861 := bbase (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) (by norm_num)
theorem B1121861 : Blo 342753 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B433937 : Blo 342753 433937 := bbase (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) (by norm_num)
theorem B466741 : Blo 342753 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B433993 : Blo 342753 433993 := bbase (se 2 (by rfl) ⟨162747, by rfl⟩ : syracuseStep 433993 = 325495) (by norm_num)
theorem B434089 : Blo 342753 434089 := bbase (se 2 (by rfl) ⟨162783, by rfl⟩ : syracuseStep 434089 = 325567) (by norm_num)
theorem B368561 : Blo 342753 368561 := bbase (se 2 (by rfl) ⟨138210, by rfl⟩ : syracuseStep 368561 = 276421) (by norm_num)
theorem B1744901 : Blo 342753 1744901 := bbase (se 4 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 1744901 = 327169) (by norm_num)
theorem B1974293 : Blo 342753 1974293 := bbase (se 6 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 1974293 = 92545) (by norm_num)
theorem B696349 : Blo 342753 696349 := bbase (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) (by norm_num)
theorem B434261 : Blo 342753 434261 := bbase (se 8 (by rfl) ⟨2544, by rfl⟩ : syracuseStep 434261 = 5089) (by norm_num)
theorem B368749 : Blo 342753 368749 := bbase (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) (by norm_num)
theorem B434317 : Blo 342753 434317 := bbase (se 3 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 434317 = 162869) (by norm_num)
theorem B434413 : Blo 342753 434413 := bbase (se 3 (by rfl) ⟨81452, by rfl⟩ : syracuseStep 434413 = 162905) (by norm_num)
theorem B2662741 : Blo 342753 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B434585 : Blo 342753 434585 := bbase (se 2 (by rfl) ⟨162969, by rfl⟩ : syracuseStep 434585 = 325939) (by norm_num)
theorem B434641 : Blo 342753 434641 := bbase (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) (by norm_num)
theorem B1581605 : Blo 342753 1581605 := bbase (se 4 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 1581605 = 296551) (by norm_num)
theorem B434737 : Blo 342753 434737 := bbase (se 2 (by rfl) ⟨163026, by rfl⟩ : syracuseStep 434737 = 326053) (by norm_num)
theorem B1647221 : Blo 342753 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B434909 : Blo 342753 434909 := bbase (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) (by norm_num)
theorem B434965 : Blo 342753 434965 := bbase (se 6 (by rfl) ⟨10194, by rfl⟩ : syracuseStep 434965 = 20389) (by norm_num)
theorem B795413 : Blo 342753 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B435061 : Blo 342753 435061 := bbase (se 5 (by rfl) ⟨20393, by rfl⟩ : syracuseStep 435061 = 40787) (by norm_num)
theorem B828301 : Blo 342753 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B369569 : Blo 342753 369569 := bbase (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) (by norm_num)
theorem B435233 : Blo 342753 435233 := bbase (se 2 (by rfl) ⟨163212, by rfl⟩ : syracuseStep 435233 = 326425) (by norm_num)
theorem B435289 : Blo 342753 435289 := bbase (se 2 (by rfl) ⟨163233, by rfl⟩ : syracuseStep 435289 = 326467) (by norm_num)
theorem B992405 : Blo 342753 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B435385 : Blo 342753 435385 := bbase (se 2 (by rfl) ⟨163269, by rfl⟩ : syracuseStep 435385 = 326539) (by norm_num)
theorem B1746197 : Blo 342753 1746197 := bbase (se 6 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 1746197 = 81853) (by norm_num)
theorem B370013 : Blo 342753 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B435557 : Blo 342753 435557 := bbase (se 4 (by rfl) ⟨40833, by rfl⟩ : syracuseStep 435557 = 81667) (by norm_num)
theorem B435613 : Blo 342753 435613 := bbase (se 3 (by rfl) ⟨81677, by rfl⟩ : syracuseStep 435613 = 163355) (by norm_num)
theorem B828917 : Blo 342753 828917 := bbase (se 5 (by rfl) ⟨38855, by rfl⟩ : syracuseStep 828917 = 77711) (by norm_num)
theorem B435709 : Blo 342753 435709 := bbase (se 3 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 435709 = 163391) (by norm_num)
theorem B370261 : Blo 342753 370261 := bbase (se 8 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 370261 = 4339) (by norm_num)
theorem B435881 : Blo 342753 435881 := bbase (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) (by norm_num)
theorem B829109 : Blo 342753 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B435937 : Blo 342753 435937 := bbase (se 2 (by rfl) ⟨163476, by rfl⟩ : syracuseStep 435937 = 326953) (by norm_num)
theorem B436033 : Blo 342753 436033 := bbase (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) (by norm_num)
theorem B1156949 : Blo 342753 1156949 := bbase (se 9 (by rfl) ⟨3389, by rfl⟩ : syracuseStep 1156949 = 6779) (by norm_num)
theorem B2959253 : Blo 342753 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B829397 : Blo 342753 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B436205 : Blo 342753 436205 := bbase (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) (by norm_num)
theorem B436261 : Blo 342753 436261 := bbase (se 4 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 436261 = 81799) (by norm_num)
theorem B436357 : Blo 342753 436357 := bbase (se 4 (by rfl) ⟨40908, by rfl⟩ : syracuseStep 436357 = 81817) (by norm_num)
theorem B1157381 : Blo 342753 1157381 := bbase (se 4 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 1157381 = 217009) (by norm_num)
theorem B698653 : Blo 342753 698653 := bbase (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) (by norm_num)
theorem B436529 : Blo 342753 436529 := bbase (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) (by norm_num)
theorem B436585 : Blo 342753 436585 := bbase (se 2 (by rfl) ⟨163719, by rfl⟩ : syracuseStep 436585 = 327439) (by norm_num)
theorem B567685 : Blo 342753 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B666037 : Blo 342753 666037 := bbase (se 5 (by rfl) ⟨31220, by rfl⟩ : syracuseStep 666037 = 62441) (by norm_num)
theorem B436681 : Blo 342753 436681 := bbase (se 2 (by rfl) ⟨163755, by rfl⟩ : syracuseStep 436681 = 327511) (by norm_num)
theorem B1747493 : Blo 342753 1747493 := bbase (se 4 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 1747493 = 327655) (by norm_num)
theorem B436853 : Blo 342753 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B436909 : Blo 342753 436909 := bbase (se 3 (by rfl) ⟨81920, by rfl⟩ : syracuseStep 436909 = 163841) (by norm_num)
theorem B1157813 : Blo 342753 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B437005 : Blo 342753 437005 := bbase (se 3 (by rfl) ⟨81938, by rfl⟩ : syracuseStep 437005 = 163877) (by norm_num)
theorem B994069 : Blo 342753 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B699205 : Blo 342753 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B1682309 : Blo 342753 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B437177 : Blo 342753 437177 := bbase (se 2 (by rfl) ⟨163941, by rfl⟩ : syracuseStep 437177 = 327883) (by norm_num)
theorem B2632661 : Blo 342753 2632661 := bbase (se 7 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 2632661 = 61703) (by norm_num)
theorem B437233 : Blo 342753 437233 := bbase (se 2 (by rfl) ⟨163962, by rfl⟩ : syracuseStep 437233 = 327925) (by norm_num)
theorem B437329 : Blo 342753 437329 := bbase (se 2 (by rfl) ⟨163998, by rfl⟩ : syracuseStep 437329 = 327997) (by norm_num)
theorem B732253 : Blo 342753 732253 := bbase (se 3 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 732253 = 274595) (by norm_num)
theorem B1158245 : Blo 342753 1158245 := bbase (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) (by norm_num)
theorem B437501 : Blo 342753 437501 := bbase (se 3 (by rfl) ⟨82031, by rfl⟩ : syracuseStep 437501 = 164063) (by norm_num)
theorem B437557 : Blo 342753 437557 := bbase (se 5 (by rfl) ⟨20510, by rfl⟩ : syracuseStep 437557 = 41021) (by norm_num)
theorem B5680469 : Blo 342753 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B699781 : Blo 342753 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B437653 : Blo 342753 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B699853 : Blo 342753 699853 := bbase (se 3 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 699853 = 262445) (by norm_num)
theorem B1158677 : Blo 342753 1158677 := bbase (se 6 (by rfl) ⟨27156, by rfl⟩ : syracuseStep 1158677 = 54313) (by norm_num)
theorem B437825 : Blo 342753 437825 := bbase (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) (by norm_num)
theorem B437881 : Blo 342753 437881 := bbase (se 2 (by rfl) ⟨164205, by rfl⟩ : syracuseStep 437881 = 328411) (by norm_num)
theorem B437977 : Blo 342753 437977 := bbase (se 2 (by rfl) ⟨164241, by rfl⟩ : syracuseStep 437977 = 328483) (by norm_num)
theorem B6598421 : Blo 342753 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B1748789 : Blo 342753 1748789 := bbase (se 5 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 1748789 = 163949) (by norm_num)
theorem B2207573 : Blo 342753 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B438149 : Blo 342753 438149 := bbase (se 4 (by rfl) ⟨41076, by rfl⟩ : syracuseStep 438149 = 82153) (by norm_num)
theorem B831397 : Blo 342753 831397 := bbase (se 4 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 831397 = 155887) (by norm_num)
theorem B438205 : Blo 342753 438205 := bbase (se 3 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 438205 = 164327) (by norm_num)
theorem B1159109 : Blo 342753 1159109 := bbase (se 4 (by rfl) ⟨108666, by rfl⟩ : syracuseStep 1159109 = 217333) (by norm_num)
theorem B733141 : Blo 342753 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B438301 : Blo 342753 438301 := bbase (se 3 (by rfl) ⟨82181, by rfl⟩ : syracuseStep 438301 = 164363) (by norm_num)
theorem B897173 : Blo 342753 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B438473 : Blo 342753 438473 := bbase (se 2 (by rfl) ⟨164427, by rfl⟩ : syracuseStep 438473 = 328855) (by norm_num)
theorem B438529 : Blo 342753 438529 := bbase (se 2 (by rfl) ⟨164448, by rfl⟩ : syracuseStep 438529 = 328897) (by norm_num)
theorem B1323317 : Blo 342753 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B438625 : Blo 342753 438625 := bbase (se 2 (by rfl) ⟨164484, by rfl⟩ : syracuseStep 438625 = 328969) (by norm_num)
theorem B1159541 : Blo 342753 1159541 := bbase (se 5 (by rfl) ⟨54353, by rfl⟩ : syracuseStep 1159541 = 108707) (by norm_num)
theorem B930197 : Blo 342753 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B733637 : Blo 342753 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B438797 : Blo 342753 438797 := bbase (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) (by norm_num)
theorem B700949 : Blo 342753 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B438853 : Blo 342753 438853 := bbase (se 4 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 438853 = 82285) (by norm_num)
theorem B373469 : Blo 342753 373469 := bbase (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) (by norm_num)
theorem B996101 : Blo 342753 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B1159973 : Blo 342753 1159973 := bbase (se 4 (by rfl) ⟨108747, by rfl⟩ : syracuseStep 1159973 = 217495) (by norm_num)
theorem B930629 : Blo 342753 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B1750085 : Blo 342753 1750085 := bbase (se 4 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 1750085 = 328141) (by norm_num)
theorem B1160405 : Blo 342753 1160405 := bbase (se 7 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 1160405 = 27197) (by norm_num)
theorem B832781 : Blo 342753 832781 := bbase (se 3 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 832781 = 312293) (by norm_num)
theorem B734525 : Blo 342753 734525 := bbase (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) (by norm_num)
theorem B734645 : Blo 342753 734645 := bbase (se 5 (by rfl) ⟨34436, by rfl⟩ : syracuseStep 734645 = 68873) (by norm_num)
theorem B1160837 : Blo 342753 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B472717 : Blo 342753 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B931829 : Blo 342753 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B735277 : Blo 342753 735277 := bbase (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) (by norm_num)
theorem B1161269 : Blo 342753 1161269 := bbase (se 5 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 1161269 = 108869) (by norm_num)
theorem B1751381 : Blo 342753 1751381 := bbase (se 10 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 1751381 = 5131) (by norm_num)
theorem B1161701 : Blo 342753 1161701 := bbase (se 4 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 1161701 = 217819) (by norm_num)
theorem B1653509 : Blo 342753 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B1653605 : Blo 342753 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1162133 : Blo 342753 1162133 := bbase (se 6 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 1162133 = 54475) (by norm_num)
theorem B736165 : Blo 342753 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B736285 : Blo 342753 736285 := bbase (se 3 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 736285 = 276107) (by norm_num)
theorem B1621061 : Blo 342753 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B1719413 : Blo 342753 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B441517 : Blo 342753 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B736541 : Blo 342753 736541 := bbase (se 3 (by rfl) ⟨138101, by rfl⟩ : syracuseStep 736541 = 276203) (by norm_num)
theorem B1162565 : Blo 342753 1162565 := bbase (se 4 (by rfl) ⟨108990, by rfl⟩ : syracuseStep 1162565 = 217981) (by norm_num)
theorem B867773 : Blo 342753 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B2473429 : Blo 342753 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B4996565 : Blo 342753 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B769517 : Blo 342753 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B1752677 : Blo 342753 1752677 := bbase (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) (by norm_num)
theorem B1162997 : Blo 342753 1162997 := bbase (se 5 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 1162997 = 109031) (by norm_num)
theorem B868117 : Blo 342753 868117 := bbase (se 6 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 868117 = 40693) (by norm_num)
theorem B409469 : Blo 342753 409469 := bbase (se 3 (by rfl) ⟨76775, by rfl⟩ : syracuseStep 409469 = 153551) (by norm_num)
theorem B868229 : Blo 342753 868229 := bbase (se 4 (by rfl) ⟨81396, by rfl⟩ : syracuseStep 868229 = 162793) (by norm_num)
theorem B3162037 : Blo 342753 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B868421 : Blo 342753 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B3129461 : Blo 342753 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B737429 : Blo 342753 737429 := bbase (se 6 (by rfl) ⟨17283, by rfl⟩ : syracuseStep 737429 = 34567) (by norm_num)
theorem B1163429 : Blo 342753 1163429 := bbase (se 4 (by rfl) ⟨109071, by rfl⟩ : syracuseStep 1163429 = 218143) (by norm_num)
theorem B999749 : Blo 342753 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B737669 : Blo 342753 737669 := bbase (se 4 (by rfl) ⟨69156, by rfl⟩ : syracuseStep 737669 = 138313) (by norm_num)
theorem B868765 : Blo 342753 868765 := bbase (se 3 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 868765 = 325787) (by norm_num)
theorem B639389 : Blo 342753 639389 := bbase (se 3 (by rfl) ⟨119885, by rfl⟩ : syracuseStep 639389 = 239771) (by norm_num)
theorem B3228149 : Blo 342753 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B868877 : Blo 342753 868877 := bbase (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) (by norm_num)
theorem B442913 : Blo 342753 442913 := bbase (se 2 (by rfl) ⟨166092, by rfl⟩ : syracuseStep 442913 = 332185) (by norm_num)
theorem B1163861 : Blo 342753 1163861 := bbase (se 8 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 1163861 = 13639) (by norm_num)
theorem B869069 : Blo 342753 869069 := bbase (se 3 (by rfl) ⟨162950, by rfl⟩ : syracuseStep 869069 = 325901) (by norm_num)
theorem B1655525 : Blo 342753 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1753973 : Blo 342753 1753973 := bbase (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) (by norm_num)
theorem B738173 : Blo 342753 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B738181 : Blo 342753 738181 := bbase (se 4 (by rfl) ⟨69204, by rfl⟩ : syracuseStep 738181 = 138409) (by norm_num)
theorem B1164293 : Blo 342753 1164293 := bbase (se 4 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 1164293 = 218305) (by norm_num)
theorem B869413 : Blo 342753 869413 := bbase (se 4 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 869413 = 163015) (by norm_num)
theorem B967717 : Blo 342753 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B869525 : Blo 342753 869525 := bbase (se 6 (by rfl) ⟨20379, by rfl⟩ : syracuseStep 869525 = 40759) (by norm_num)
theorem B5883029 : Blo 342753 5883029 := bbase (se 6 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 5883029 = 275767) (by norm_num)
theorem B1098917 : Blo 342753 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B771245 : Blo 342753 771245 := bbase (se 3 (by rfl) ⟨144608, by rfl⟩ : syracuseStep 771245 = 289217) (by norm_num)
theorem B771317 : Blo 342753 771317 := bbase (se 5 (by rfl) ⟨36155, by rfl⟩ : syracuseStep 771317 = 72311) (by norm_num)
theorem B4179221 : Blo 342753 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B771389 : Blo 342753 771389 := bbase (se 3 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 771389 = 289271) (by norm_num)
theorem B869717 : Blo 342753 869717 := bbase (se 12 (by rfl) ⟨318, by rfl⟩ : syracuseStep 869717 = 637) (by norm_num)
theorem B3327317 : Blo 342753 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B771461 : Blo 342753 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B1164725 : Blo 342753 1164725 := bbase (se 5 (by rfl) ⟨54596, by rfl⟩ : syracuseStep 1164725 = 109193) (by norm_num)
theorem B771533 : Blo 342753 771533 := bbase (se 3 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 771533 = 289325) (by norm_num)
theorem B2213365 : Blo 342753 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B771605 : Blo 342753 771605 := bbase (se 6 (by rfl) ⟨18084, by rfl⟩ : syracuseStep 771605 = 36169) (by norm_num)
theorem B771677 : Blo 342753 771677 := bbase (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) (by norm_num)
theorem B378469 : Blo 342753 378469 := bbase (se 4 (by rfl) ⟨35481, by rfl⟩ : syracuseStep 378469 = 70963) (by norm_num)
theorem B771749 : Blo 342753 771749 := bbase (se 4 (by rfl) ⟨72351, by rfl⟩ : syracuseStep 771749 = 144703) (by norm_num)
theorem B870061 : Blo 342753 870061 := bbase (se 3 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 870061 = 326273) (by norm_num)
theorem B771821 : Blo 342753 771821 := bbase (se 3 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 771821 = 289433) (by norm_num)
theorem B444169 : Blo 342753 444169 := bbase (se 2 (by rfl) ⟨166563, by rfl⟩ : syracuseStep 444169 = 333127) (by norm_num)
theorem B870173 : Blo 342753 870173 := bbase (se 3 (by rfl) ⟨163157, by rfl⟩ : syracuseStep 870173 = 326315) (by norm_num)
theorem B771893 : Blo 342753 771893 := bbase (se 5 (by rfl) ⟨36182, by rfl⟩ : syracuseStep 771893 = 72365) (by norm_num)
theorem B1165157 : Blo 342753 1165157 := bbase (se 4 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 1165157 = 218467) (by norm_num)
theorem B771965 : Blo 342753 771965 := bbase (se 3 (by rfl) ⟨144743, by rfl⟩ : syracuseStep 771965 = 289487) (by norm_num)
theorem B772037 : Blo 342753 772037 := bbase (se 4 (by rfl) ⟨72378, by rfl⟩ : syracuseStep 772037 = 144757) (by norm_num)
theorem B870365 : Blo 342753 870365 := bbase (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) (by norm_num)
theorem B739309 : Blo 342753 739309 := bbase (se 3 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 739309 = 277241) (by norm_num)
theorem B772109 : Blo 342753 772109 := bbase (se 3 (by rfl) ⟨144770, by rfl⟩ : syracuseStep 772109 = 289541) (by norm_num)
theorem B772181 : Blo 342753 772181 := bbase (se 8 (by rfl) ⟨4524, by rfl⟩ : syracuseStep 772181 = 9049) (by norm_num)
theorem B1656949 : Blo 342753 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1755269 : Blo 342753 1755269 := bbase (se 4 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 1755269 = 329113) (by norm_num)
theorem B772253 : Blo 342753 772253 := bbase (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) (by norm_num)
theorem B772325 : Blo 342753 772325 := bbase (se 4 (by rfl) ⟨72405, by rfl⟩ : syracuseStep 772325 = 144811) (by norm_num)
theorem B1165589 : Blo 342753 1165589 := bbase (se 6 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 1165589 = 54637) (by norm_num)
theorem B772397 : Blo 342753 772397 := bbase (se 3 (by rfl) ⟨144824, by rfl⟩ : syracuseStep 772397 = 289649) (by norm_num)
theorem B870709 : Blo 342753 870709 := bbase (se 5 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 870709 = 81629) (by norm_num)
theorem B739685 : Blo 342753 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B772469 : Blo 342753 772469 := bbase (se 5 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 772469 = 72419) (by norm_num)
theorem B870821 : Blo 342753 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B772541 : Blo 342753 772541 := bbase (se 3 (by rfl) ⟨144851, by rfl⟩ : syracuseStep 772541 = 289703) (by norm_num)
theorem B2804213 : Blo 342753 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B772613 : Blo 342753 772613 := bbase (se 4 (by rfl) ⟨72432, by rfl⟩ : syracuseStep 772613 = 144865) (by norm_num)
theorem B772685 : Blo 342753 772685 := bbase (se 3 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 772685 = 289757) (by norm_num)
theorem B871013 : Blo 342753 871013 := bbase (se 4 (by rfl) ⟨81657, by rfl⟩ : syracuseStep 871013 = 163315) (by norm_num)
theorem B412301 : Blo 342753 412301 := bbase (se 3 (by rfl) ⟨77306, by rfl⟩ : syracuseStep 412301 = 154613) (by norm_num)
theorem B772757 : Blo 342753 772757 := bbase (se 6 (by rfl) ⟨18111, by rfl⟩ : syracuseStep 772757 = 36223) (by norm_num)
theorem B1166021 : Blo 342753 1166021 := bbase (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) (by norm_num)
theorem B772829 : Blo 342753 772829 := bbase (se 3 (by rfl) ⟨144905, by rfl⟩ : syracuseStep 772829 = 289811) (by norm_num)
theorem B772901 : Blo 342753 772901 := bbase (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) (by norm_num)
theorem B772973 : Blo 342753 772973 := bbase (se 3 (by rfl) ⟨144932, by rfl⟩ : syracuseStep 772973 = 289865) (by norm_num)
theorem B773045 : Blo 342753 773045 := bbase (se 5 (by rfl) ⟨36236, by rfl⟩ : syracuseStep 773045 = 72473) (by norm_num)
theorem B871357 : Blo 342753 871357 := bbase (se 3 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 871357 = 326759) (by norm_num)
theorem B412609 : Blo 342753 412609 := bbase (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) (by norm_num)
theorem B773117 : Blo 342753 773117 := bbase (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) (by norm_num)
theorem B412709 : Blo 342753 412709 := bbase (se 4 (by rfl) ⟨38691, by rfl⟩ : syracuseStep 412709 = 77383) (by norm_num)
theorem B871469 : Blo 342753 871469 := bbase (se 3 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 871469 = 326801) (by norm_num)
theorem B773189 : Blo 342753 773189 := bbase (se 4 (by rfl) ⟨72486, by rfl⟩ : syracuseStep 773189 = 144973) (by norm_num)
theorem B1166453 : Blo 342753 1166453 := bbase (se 5 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 1166453 = 109355) (by norm_num)
theorem B773261 : Blo 342753 773261 := bbase (se 3 (by rfl) ⟨144986, by rfl⟩ : syracuseStep 773261 = 289973) (by norm_num)
theorem B773333 : Blo 342753 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B871661 : Blo 342753 871661 := bbase (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) (by norm_num)
theorem B773405 : Blo 342753 773405 := bbase (se 3 (by rfl) ⟨145013, by rfl⟩ : syracuseStep 773405 = 290027) (by norm_num)
theorem B1101109 : Blo 342753 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B773477 : Blo 342753 773477 := bbase (se 4 (by rfl) ⟨72513, by rfl⟩ : syracuseStep 773477 = 145027) (by norm_num)
theorem B1953173 : Blo 342753 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B773549 : Blo 342753 773549 := bbase (se 3 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 773549 = 290081) (by norm_num)
theorem B413113 : Blo 342753 413113 := bbase (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) (by norm_num)
theorem B773621 : Blo 342753 773621 := bbase (se 5 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 773621 = 72527) (by norm_num)
theorem B1166885 : Blo 342753 1166885 := bbase (se 4 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 1166885 = 218791) (by norm_num)
theorem B347689 : Blo 342753 347689 := bbase (se 2 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 347689 = 260767) (by norm_num)
theorem B773693 : Blo 342753 773693 := bbase (se 3 (by rfl) ⟨145067, by rfl⟩ : syracuseStep 773693 = 290135) (by norm_num)
theorem B872005 : Blo 342753 872005 := bbase (se 4 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 872005 = 163501) (by norm_num)
theorem B773765 : Blo 342753 773765 := bbase (se 4 (by rfl) ⟨72540, by rfl⟩ : syracuseStep 773765 = 145081) (by norm_num)
theorem B872117 : Blo 342753 872117 := bbase (se 5 (by rfl) ⟨40880, by rfl⟩ : syracuseStep 872117 = 81761) (by norm_num)
theorem B773837 : Blo 342753 773837 := bbase (se 3 (by rfl) ⟨145094, by rfl⟩ : syracuseStep 773837 = 290189) (by norm_num)
theorem B773909 : Blo 342753 773909 := bbase (se 6 (by rfl) ⟨18138, by rfl⟩ : syracuseStep 773909 = 36277) (by norm_num)
theorem B413497 : Blo 342753 413497 := bbase (se 2 (by rfl) ⟨155061, by rfl⟩ : syracuseStep 413497 = 310123) (by norm_num)
theorem B347977 : Blo 342753 347977 := bbase (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) (by norm_num)
theorem B773981 : Blo 342753 773981 := bbase (se 3 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 773981 = 290243) (by norm_num)
theorem B872309 : Blo 342753 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B774053 : Blo 342753 774053 := bbase (se 4 (by rfl) ⟨72567, by rfl⟩ : syracuseStep 774053 = 145135) (by norm_num)
theorem B1167317 : Blo 342753 1167317 := bbase (se 7 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 1167317 = 27359) (by norm_num)
theorem B1396709 : Blo 342753 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B774125 : Blo 342753 774125 := bbase (se 3 (by rfl) ⟨145148, by rfl⟩ : syracuseStep 774125 = 290297) (by norm_num)
theorem B446485 : Blo 342753 446485 := bbase (se 6 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 446485 = 20929) (by norm_num)
theorem B774197 : Blo 342753 774197 := bbase (se 5 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 774197 = 72581) (by norm_num)
theorem B1101941 : Blo 342753 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B774269 : Blo 342753 774269 := bbase (se 3 (by rfl) ⟨145175, by rfl⟩ : syracuseStep 774269 = 290351) (by norm_num)
theorem B2609333 : Blo 342753 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B774341 : Blo 342753 774341 := bbase (se 4 (by rfl) ⟨72594, by rfl⟩ : syracuseStep 774341 = 145189) (by norm_num)
theorem B872653 : Blo 342753 872653 := bbase (se 3 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 872653 = 327245) (by norm_num)
theorem B774413 : Blo 342753 774413 := bbase (se 3 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 774413 = 290405) (by norm_num)
theorem B1397045 : Blo 342753 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B872765 : Blo 342753 872765 := bbase (se 3 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 872765 = 327287) (by norm_num)
theorem B774485 : Blo 342753 774485 := bbase (se 10 (by rfl) ⟨1134, by rfl⟩ : syracuseStep 774485 = 2269) (by norm_num)
theorem B1167749 : Blo 342753 1167749 := bbase (se 4 (by rfl) ⟨109476, by rfl⟩ : syracuseStep 1167749 = 218953) (by norm_num)
theorem B774557 : Blo 342753 774557 := bbase (se 3 (by rfl) ⟨145229, by rfl⟩ : syracuseStep 774557 = 290459) (by norm_num)
theorem B348629 : Blo 342753 348629 := bbase (se 7 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 348629 = 8171) (by norm_num)
theorem B774629 : Blo 342753 774629 := bbase (se 4 (by rfl) ⟨72621, by rfl⟩ : syracuseStep 774629 = 145243) (by norm_num)
theorem B872957 : Blo 342753 872957 := bbase (se 3 (by rfl) ⟨163679, by rfl⟩ : syracuseStep 872957 = 327359) (by norm_num)
theorem B774701 : Blo 342753 774701 := bbase (se 3 (by rfl) ⟨145256, by rfl⟩ : syracuseStep 774701 = 290513) (by norm_num)
theorem B774773 : Blo 342753 774773 := bbase (se 5 (by rfl) ⟨36317, by rfl⟩ : syracuseStep 774773 = 72635) (by norm_num)
theorem B414353 : Blo 342753 414353 := bbase (se 2 (by rfl) ⟨155382, by rfl⟩ : syracuseStep 414353 = 310765) (by norm_num)
theorem B774845 : Blo 342753 774845 := bbase (se 3 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 774845 = 290567) (by norm_num)
theorem B348929 : Blo 342753 348929 := bbase (se 2 (by rfl) ⟨130848, by rfl⟩ : syracuseStep 348929 = 261697) (by norm_num)
theorem B774917 : Blo 342753 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B1168181 : Blo 342753 1168181 := bbase (se 5 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 1168181 = 109517) (by norm_num)
theorem B774989 : Blo 342753 774989 := bbase (se 3 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 774989 = 290621) (by norm_num)
theorem B3298133 : Blo 342753 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B873301 : Blo 342753 873301 := bbase (se 9 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 873301 = 5117) (by norm_num)
theorem B775061 : Blo 342753 775061 := bbase (se 6 (by rfl) ⟨18165, by rfl⟩ : syracuseStep 775061 = 36331) (by norm_num)
theorem B578461 : Blo 342753 578461 := bbase (se 3 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 578461 = 216923) (by norm_num)
theorem B873413 : Blo 342753 873413 := bbase (se 4 (by rfl) ⟨81882, by rfl⟩ : syracuseStep 873413 = 163765) (by norm_num)
theorem B414661 : Blo 342753 414661 := bbase (se 4 (by rfl) ⟨38874, by rfl⟩ : syracuseStep 414661 = 77749) (by norm_num)
theorem B775133 : Blo 342753 775133 := bbase (se 3 (by rfl) ⟨145337, by rfl⟩ : syracuseStep 775133 = 290675) (by norm_num)
theorem B578549 : Blo 342753 578549 := bbase (se 5 (by rfl) ⟨27119, by rfl⟩ : syracuseStep 578549 = 54239) (by norm_num)
theorem B775205 : Blo 342753 775205 := bbase (se 4 (by rfl) ⟨72675, by rfl⟩ : syracuseStep 775205 = 145351) (by norm_num)
theorem B775277 : Blo 342753 775277 := bbase (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) (by norm_num)
theorem B578677 : Blo 342753 578677 := bbase (se 5 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 578677 = 54251) (by norm_num)
theorem B873605 : Blo 342753 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B414877 : Blo 342753 414877 := bbase (se 3 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 414877 = 155579) (by norm_num)
theorem B775349 : Blo 342753 775349 := bbase (se 5 (by rfl) ⟨36344, by rfl⟩ : syracuseStep 775349 = 72689) (by norm_num)
theorem B578765 : Blo 342753 578765 := bbase (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) (by norm_num)
theorem B4183253 : Blo 342753 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B1168613 : Blo 342753 1168613 := bbase (se 4 (by rfl) ⟨109557, by rfl⟩ : syracuseStep 1168613 = 219115) (by norm_num)
theorem B775421 : Blo 342753 775421 := bbase (se 3 (by rfl) ⟨145391, by rfl⟩ : syracuseStep 775421 = 290783) (by norm_num)
theorem B775493 : Blo 342753 775493 := bbase (se 4 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 775493 = 145405) (by norm_num)
theorem B578893 : Blo 342753 578893 := bbase (se 3 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 578893 = 217085) (by norm_num)
theorem B349537 : Blo 342753 349537 := bbase (se 2 (by rfl) ⟨131076, by rfl⟩ : syracuseStep 349537 = 262153) (by norm_num)
theorem B775565 : Blo 342753 775565 := bbase (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) (by norm_num)
theorem B578981 : Blo 342753 578981 := bbase (se 4 (by rfl) ⟨54279, by rfl⟩ : syracuseStep 578981 = 108559) (by norm_num)
theorem B775637 : Blo 342753 775637 := bbase (se 7 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 775637 = 18179) (by norm_num)
theorem B873949 : Blo 342753 873949 := bbase (se 3 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 873949 = 327731) (by norm_num)
theorem B775709 : Blo 342753 775709 := bbase (se 3 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 775709 = 290891) (by norm_num)
theorem B579109 : Blo 342753 579109 := bbase (se 4 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 579109 = 108583) (by norm_num)
theorem B874061 : Blo 342753 874061 := bbase (se 3 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 874061 = 327773) (by norm_num)
theorem B775781 : Blo 342753 775781 := bbase (se 4 (by rfl) ⟨72729, by rfl⟩ : syracuseStep 775781 = 145459) (by norm_num)
theorem B579197 : Blo 342753 579197 := bbase (se 3 (by rfl) ⟨108599, by rfl⟩ : syracuseStep 579197 = 217199) (by norm_num)
theorem B1169045 : Blo 342753 1169045 := bbase (se 6 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 1169045 = 54799) (by norm_num)
theorem B775853 : Blo 342753 775853 := bbase (se 3 (by rfl) ⟨145472, by rfl⟩ : syracuseStep 775853 = 290945) (by norm_num)
theorem B775925 : Blo 342753 775925 := bbase (se 5 (by rfl) ⟨36371, by rfl⟩ : syracuseStep 775925 = 72743) (by norm_num)
theorem B415477 : Blo 342753 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B579325 : Blo 342753 579325 := bbase (se 3 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 579325 = 217247) (by norm_num)
theorem B710405 : Blo 342753 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B874253 : Blo 342753 874253 := bbase (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) (by norm_num)
theorem B710453 : Blo 342753 710453 := bbase (se 5 (by rfl) ⟨33302, by rfl⟩ : syracuseStep 710453 = 66605) (by norm_num)
theorem B775997 : Blo 342753 775997 := bbase (se 3 (by rfl) ⟨145499, by rfl⟩ : syracuseStep 775997 = 290999) (by norm_num)
theorem B579413 : Blo 342753 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B382837 : Blo 342753 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B776069 : Blo 342753 776069 := bbase (se 4 (by rfl) ⟨72756, by rfl⟩ : syracuseStep 776069 = 145513) (by norm_num)
theorem B1103813 : Blo 342753 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B776141 : Blo 342753 776141 := bbase (se 3 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 776141 = 291053) (by norm_num)
theorem B579541 : Blo 342753 579541 := bbase (se 7 (by rfl) ⟨6791, by rfl⟩ : syracuseStep 579541 = 13583) (by norm_num)
theorem B776213 : Blo 342753 776213 := bbase (se 6 (by rfl) ⟨18192, by rfl⟩ : syracuseStep 776213 = 36385) (by norm_num)
theorem B579629 : Blo 342753 579629 := bbase (se 3 (by rfl) ⟨108680, by rfl⟩ : syracuseStep 579629 = 217361) (by norm_num)
theorem B1169477 : Blo 342753 1169477 := bbase (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) (by norm_num)
theorem B514133 : Blo 342753 514133 := bbase (se 8 (by rfl) ⟨3012, by rfl⟩ : syracuseStep 514133 = 6025) (by norm_num)
theorem B776285 : Blo 342753 776285 := bbase (se 3 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 776285 = 291107) (by norm_num)
theorem B874597 : Blo 342753 874597 := bbase (se 4 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 874597 = 163987) (by norm_num)
theorem B514157 : Blo 342753 514157 := bbase (se 3 (by rfl) ⟨96404, by rfl⟩ : syracuseStep 514157 = 192809) (by norm_num)
theorem B514181 : Blo 342753 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B514205 : Blo 342753 514205 := bbase (se 3 (by rfl) ⟨96413, by rfl⟩ : syracuseStep 514205 = 192827) (by norm_num)
theorem B776357 : Blo 342753 776357 := bbase (se 4 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 776357 = 145567) (by norm_num)
theorem B579757 : Blo 342753 579757 := bbase (se 3 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 579757 = 217409) (by norm_num)
theorem B514229 : Blo 342753 514229 := bbase (se 5 (by rfl) ⟨24104, by rfl⟩ : syracuseStep 514229 = 48209) (by norm_num)
theorem B514253 : Blo 342753 514253 := bbase (se 3 (by rfl) ⟨96422, by rfl⟩ : syracuseStep 514253 = 192845) (by norm_num)
theorem B874709 : Blo 342753 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B514277 : Blo 342753 514277 := bbase (se 4 (by rfl) ⟨48213, by rfl⟩ : syracuseStep 514277 = 96427) (by norm_num)
theorem B776429 : Blo 342753 776429 := bbase (se 3 (by rfl) ⟨145580, by rfl⟩ : syracuseStep 776429 = 291161) (by norm_num)
theorem B514301 : Blo 342753 514301 := bbase (se 3 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 514301 = 192863) (by norm_num)
theorem B579845 : Blo 342753 579845 := bbase (se 4 (by rfl) ⟨54360, by rfl⟩ : syracuseStep 579845 = 108721) (by norm_num)
theorem B514325 : Blo 342753 514325 := bbase (se 6 (by rfl) ⟨12054, by rfl⟩ : syracuseStep 514325 = 24109) (by norm_num)
theorem B514349 : Blo 342753 514349 := bbase (se 3 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 514349 = 192881) (by norm_num)
theorem B776501 : Blo 342753 776501 := bbase (se 5 (by rfl) ⟨36398, by rfl⟩ : syracuseStep 776501 = 72797) (by norm_num)
theorem B514373 : Blo 342753 514373 := bbase (se 4 (by rfl) ⟨48222, by rfl⟩ : syracuseStep 514373 = 96445) (by norm_num)
theorem B514397 : Blo 342753 514397 := bbase (se 3 (by rfl) ⟨96449, by rfl⟩ : syracuseStep 514397 = 192899) (by norm_num)
theorem B514421 : Blo 342753 514421 := bbase (se 5 (by rfl) ⟨24113, by rfl⟩ : syracuseStep 514421 = 48227) (by norm_num)
theorem B776573 : Blo 342753 776573 := bbase (se 3 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 776573 = 291215) (by norm_num)
theorem B579973 : Blo 342753 579973 := bbase (se 4 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 579973 = 108745) (by norm_num)
theorem B514445 : Blo 342753 514445 := bbase (se 3 (by rfl) ⟨96458, by rfl⟩ : syracuseStep 514445 = 192917) (by norm_num)
theorem B874901 : Blo 342753 874901 := bbase (se 6 (by rfl) ⟨20505, by rfl⟩ : syracuseStep 874901 = 41011) (by norm_num)
theorem B514469 : Blo 342753 514469 := bbase (se 4 (by rfl) ⟨48231, by rfl⟩ : syracuseStep 514469 = 96463) (by norm_num)
theorem B514493 : Blo 342753 514493 := bbase (se 3 (by rfl) ⟨96467, by rfl⟩ : syracuseStep 514493 = 192935) (by norm_num)
theorem B776645 : Blo 342753 776645 := bbase (se 4 (by rfl) ⟨72810, by rfl⟩ : syracuseStep 776645 = 145621) (by norm_num)
theorem B514517 : Blo 342753 514517 := bbase (se 7 (by rfl) ⟨6029, by rfl⟩ : syracuseStep 514517 = 12059) (by norm_num)
theorem B580061 : Blo 342753 580061 := bbase (se 3 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 580061 = 217523) (by norm_num)
theorem B514541 : Blo 342753 514541 := bbase (se 3 (by rfl) ⟨96476, by rfl⟩ : syracuseStep 514541 = 192953) (by norm_num)
theorem B1169909 : Blo 342753 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B514565 : Blo 342753 514565 := bbase (se 4 (by rfl) ⟨48240, by rfl⟩ : syracuseStep 514565 = 96481) (by norm_num)
theorem B776717 : Blo 342753 776717 := bbase (se 3 (by rfl) ⟨145634, by rfl⟩ : syracuseStep 776717 = 291269) (by norm_num)
theorem B514589 : Blo 342753 514589 := bbase (se 3 (by rfl) ⟨96485, by rfl⟩ : syracuseStep 514589 = 192971) (by norm_num)
theorem B514613 : Blo 342753 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B514637 : Blo 342753 514637 := bbase (se 3 (by rfl) ⟨96494, by rfl⟩ : syracuseStep 514637 = 192989) (by norm_num)
theorem B776789 : Blo 342753 776789 := bbase (se 8 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 776789 = 9103) (by norm_num)
theorem B580189 : Blo 342753 580189 := bbase (se 3 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 580189 = 217571) (by norm_num)
theorem B514661 : Blo 342753 514661 := bbase (se 4 (by rfl) ⟨48249, by rfl⟩ : syracuseStep 514661 = 96499) (by norm_num)
theorem B514685 : Blo 342753 514685 := bbase (se 3 (by rfl) ⟨96503, by rfl⟩ : syracuseStep 514685 = 193007) (by norm_num)
theorem B514709 : Blo 342753 514709 := bbase (se 6 (by rfl) ⟨12063, by rfl⟩ : syracuseStep 514709 = 24127) (by norm_num)
theorem B776861 : Blo 342753 776861 := bbase (se 3 (by rfl) ⟨145661, by rfl⟩ : syracuseStep 776861 = 291323) (by norm_num)
theorem B514733 : Blo 342753 514733 := bbase (se 3 (by rfl) ⟨96512, by rfl⟩ : syracuseStep 514733 = 193025) (by norm_num)
theorem B580277 : Blo 342753 580277 := bbase (se 5 (by rfl) ⟨27200, by rfl⟩ : syracuseStep 580277 = 54401) (by norm_num)
theorem B514757 : Blo 342753 514757 := bbase (se 4 (by rfl) ⟨48258, by rfl⟩ : syracuseStep 514757 = 96517) (by norm_num)
theorem B514781 : Blo 342753 514781 := bbase (se 3 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 514781 = 193043) (by norm_num)
theorem B776933 : Blo 342753 776933 := bbase (se 4 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 776933 = 145675) (by norm_num)
theorem B875245 : Blo 342753 875245 := bbase (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) (by norm_num)
theorem B514805 : Blo 342753 514805 := bbase (se 5 (by rfl) ⟨24131, by rfl⟩ : syracuseStep 514805 = 48263) (by norm_num)
theorem B514829 : Blo 342753 514829 := bbase (se 3 (by rfl) ⟨96530, by rfl⟩ : syracuseStep 514829 = 193061) (by norm_num)
theorem B449293 : Blo 342753 449293 := bbase (se 3 (by rfl) ⟨84242, by rfl⟩ : syracuseStep 449293 = 168485) (by norm_num)
theorem B351005 : Blo 342753 351005 := bbase (se 3 (by rfl) ⟨65813, by rfl⟩ : syracuseStep 351005 = 131627) (by norm_num)
theorem B514853 : Blo 342753 514853 := bbase (se 4 (by rfl) ⟨48267, by rfl⟩ : syracuseStep 514853 = 96535) (by norm_num)
theorem B777005 : Blo 342753 777005 := bbase (se 3 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 777005 = 291377) (by norm_num)
theorem B580405 : Blo 342753 580405 := bbase (se 5 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 580405 = 54413) (by norm_num)
theorem B514877 : Blo 342753 514877 := bbase (se 3 (by rfl) ⟨96539, by rfl⟩ : syracuseStep 514877 = 193079) (by norm_num)
theorem B514901 : Blo 342753 514901 := bbase (se 9 (by rfl) ⟨1508, by rfl⟩ : syracuseStep 514901 = 3017) (by norm_num)
theorem B875357 : Blo 342753 875357 := bbase (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) (by norm_num)
theorem B514925 : Blo 342753 514925 := bbase (se 3 (by rfl) ⟨96548, by rfl⟩ : syracuseStep 514925 = 193097) (by norm_num)
theorem B777077 : Blo 342753 777077 := bbase (se 5 (by rfl) ⟨36425, by rfl⟩ : syracuseStep 777077 = 72851) (by norm_num)
theorem B514949 : Blo 342753 514949 := bbase (se 4 (by rfl) ⟨48276, by rfl⟩ : syracuseStep 514949 = 96553) (by norm_num)
theorem B580493 : Blo 342753 580493 := bbase (se 3 (by rfl) ⟨108842, by rfl⟩ : syracuseStep 580493 = 217685) (by norm_num)
theorem B842645 : Blo 342753 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B514973 : Blo 342753 514973 := bbase (se 3 (by rfl) ⟨96557, by rfl⟩ : syracuseStep 514973 = 193115) (by norm_num)
theorem B514997 : Blo 342753 514997 := bbase (se 5 (by rfl) ⟨24140, by rfl⟩ : syracuseStep 514997 = 48281) (by norm_num)
theorem B777149 : Blo 342753 777149 := bbase (se 3 (by rfl) ⟨145715, by rfl⟩ : syracuseStep 777149 = 291431) (by norm_num)
theorem B515021 : Blo 342753 515021 := bbase (se 3 (by rfl) ⟨96566, by rfl⟩ : syracuseStep 515021 = 193133) (by norm_num)
theorem B515045 : Blo 342753 515045 := bbase (se 4 (by rfl) ⟨48285, by rfl⟩ : syracuseStep 515045 = 96571) (by norm_num)
theorem B515069 : Blo 342753 515069 := bbase (se 3 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 515069 = 193151) (by norm_num)
theorem B777221 : Blo 342753 777221 := bbase (se 4 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 777221 = 145729) (by norm_num)
theorem B580621 : Blo 342753 580621 := bbase (se 3 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 580621 = 217733) (by norm_num)
theorem B515093 : Blo 342753 515093 := bbase (se 6 (by rfl) ⟨12072, by rfl⟩ : syracuseStep 515093 = 24145) (by norm_num)
theorem B351253 : Blo 342753 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B875549 : Blo 342753 875549 := bbase (se 3 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 875549 = 328331) (by norm_num)
theorem B515117 : Blo 342753 515117 := bbase (se 3 (by rfl) ⟨96584, by rfl⟩ : syracuseStep 515117 = 193169) (by norm_num)
theorem B515141 : Blo 342753 515141 := bbase (se 4 (by rfl) ⟨48294, by rfl⟩ : syracuseStep 515141 = 96589) (by norm_num)
theorem B777293 : Blo 342753 777293 := bbase (se 3 (by rfl) ⟨145742, by rfl⟩ : syracuseStep 777293 = 291485) (by norm_num)
theorem B515165 : Blo 342753 515165 := bbase (se 3 (by rfl) ⟨96593, by rfl⟩ : syracuseStep 515165 = 193187) (by norm_num)
theorem B580709 : Blo 342753 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B515189 : Blo 342753 515189 := bbase (se 5 (by rfl) ⟨24149, by rfl⟩ : syracuseStep 515189 = 48299) (by norm_num)
theorem B515213 : Blo 342753 515213 := bbase (se 3 (by rfl) ⟨96602, by rfl⟩ : syracuseStep 515213 = 193205) (by norm_num)
theorem B777365 : Blo 342753 777365 := bbase (se 6 (by rfl) ⟨18219, by rfl⟩ : syracuseStep 777365 = 36439) (by norm_num)
theorem B515237 : Blo 342753 515237 := bbase (se 4 (by rfl) ⟨48303, by rfl⟩ : syracuseStep 515237 = 96607) (by norm_num)
theorem B515261 : Blo 342753 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B515285 : Blo 342753 515285 := bbase (se 7 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 515285 = 12077) (by norm_num)
theorem B777437 : Blo 342753 777437 := bbase (se 3 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 777437 = 291539) (by norm_num)
theorem B580837 : Blo 342753 580837 := bbase (se 4 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 580837 = 108907) (by norm_num)
theorem B515309 : Blo 342753 515309 := bbase (se 3 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 515309 = 193241) (by norm_num)
theorem B1760501 : Blo 342753 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B515333 : Blo 342753 515333 := bbase (se 4 (by rfl) ⟨48312, by rfl⟩ : syracuseStep 515333 = 96625) (by norm_num)
theorem B515357 : Blo 342753 515357 := bbase (se 3 (by rfl) ⟨96629, by rfl⟩ : syracuseStep 515357 = 193259) (by norm_num)
theorem B777509 : Blo 342753 777509 := bbase (se 4 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 777509 = 145783) (by norm_num)
theorem B515381 : Blo 342753 515381 := bbase (se 5 (by rfl) ⟨24158, by rfl⟩ : syracuseStep 515381 = 48317) (by norm_num)
theorem B580925 : Blo 342753 580925 := bbase (se 3 (by rfl) ⟨108923, by rfl⟩ : syracuseStep 580925 = 217847) (by norm_num)
theorem B515405 : Blo 342753 515405 := bbase (se 3 (by rfl) ⟨96638, by rfl⟩ : syracuseStep 515405 = 193277) (by norm_num)
theorem B1465685 : Blo 342753 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B515429 : Blo 342753 515429 := bbase (se 4 (by rfl) ⟨48321, by rfl⟩ : syracuseStep 515429 = 96643) (by norm_num)
theorem B777581 : Blo 342753 777581 := bbase (se 3 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 777581 = 291593) (by norm_num)
theorem B875893 : Blo 342753 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B515453 : Blo 342753 515453 := bbase (se 3 (by rfl) ⟨96647, by rfl⟩ : syracuseStep 515453 = 193295) (by norm_num)
theorem B515477 : Blo 342753 515477 := bbase (se 6 (by rfl) ⟨12081, by rfl⟩ : syracuseStep 515477 = 24163) (by norm_num)
theorem B515501 : Blo 342753 515501 := bbase (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) (by norm_num)
theorem B777653 : Blo 342753 777653 := bbase (se 5 (by rfl) ⟨36452, by rfl⟩ : syracuseStep 777653 = 72905) (by norm_num)
theorem B581053 : Blo 342753 581053 := bbase (se 3 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 581053 = 217895) (by norm_num)
theorem B515525 : Blo 342753 515525 := bbase (se 4 (by rfl) ⟨48330, by rfl⟩ : syracuseStep 515525 = 96661) (by norm_num)
theorem B515549 : Blo 342753 515549 := bbase (se 3 (by rfl) ⟨96665, by rfl⟩ : syracuseStep 515549 = 193331) (by norm_num)
theorem B876005 : Blo 342753 876005 := bbase (se 4 (by rfl) ⟨82125, by rfl⟩ : syracuseStep 876005 = 164251) (by norm_num)
theorem B515573 : Blo 342753 515573 := bbase (se 5 (by rfl) ⟨24167, by rfl⟩ : syracuseStep 515573 = 48335) (by norm_num)
theorem B777725 : Blo 342753 777725 := bbase (se 3 (by rfl) ⟨145823, by rfl⟩ : syracuseStep 777725 = 291647) (by norm_num)
theorem B515597 : Blo 342753 515597 := bbase (se 3 (by rfl) ⟨96674, by rfl⟩ : syracuseStep 515597 = 193349) (by norm_num)
theorem B581141 : Blo 342753 581141 := bbase (se 6 (by rfl) ⟨13620, by rfl⟩ : syracuseStep 581141 = 27241) (by norm_num)
theorem B3923477 : Blo 342753 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B515621 : Blo 342753 515621 := bbase (se 4 (by rfl) ⟨48339, by rfl⟩ : syracuseStep 515621 = 96679) (by norm_num)
theorem B515645 : Blo 342753 515645 := bbase (se 3 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 515645 = 193367) (by norm_num)
theorem B777797 : Blo 342753 777797 := bbase (se 4 (by rfl) ⟨72918, by rfl⟩ : syracuseStep 777797 = 145837) (by norm_num)
theorem B1302101 : Blo 342753 1302101 := bbase (se 8 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 1302101 = 15259) (by norm_num)
theorem B515669 : Blo 342753 515669 := bbase (se 8 (by rfl) ⟨3021, by rfl⟩ : syracuseStep 515669 = 6043) (by norm_num)
theorem B515693 : Blo 342753 515693 := bbase (se 3 (by rfl) ⟨96692, by rfl⟩ : syracuseStep 515693 = 193385) (by norm_num)
theorem B515717 : Blo 342753 515717 := bbase (se 4 (by rfl) ⟨48348, by rfl⟩ : syracuseStep 515717 = 96697) (by norm_num)
theorem B777869 : Blo 342753 777869 := bbase (se 3 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 777869 = 291701) (by norm_num)
theorem B581269 : Blo 342753 581269 := bbase (se 6 (by rfl) ⟨13623, by rfl⟩ : syracuseStep 581269 = 27247) (by norm_num)
theorem B2219669 : Blo 342753 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B515741 : Blo 342753 515741 := bbase (se 3 (by rfl) ⟨96701, by rfl⟩ : syracuseStep 515741 = 193403) (by norm_num)
theorem B876197 : Blo 342753 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B515765 : Blo 342753 515765 := bbase (se 5 (by rfl) ⟨24176, by rfl⟩ : syracuseStep 515765 = 48353) (by norm_num)
theorem B515789 : Blo 342753 515789 := bbase (se 3 (by rfl) ⟨96710, by rfl⟩ : syracuseStep 515789 = 193421) (by norm_num)
theorem B777941 : Blo 342753 777941 := bbase (se 7 (by rfl) ⟨9116, by rfl⟩ : syracuseStep 777941 = 18233) (by norm_num)
theorem B515813 : Blo 342753 515813 := bbase (se 4 (by rfl) ⟨48357, by rfl⟩ : syracuseStep 515813 = 96715) (by norm_num)
theorem B581357 : Blo 342753 581357 := bbase (se 3 (by rfl) ⟨109004, by rfl⟩ : syracuseStep 581357 = 218009) (by norm_num)
theorem B515837 : Blo 342753 515837 := bbase (se 3 (by rfl) ⟨96719, by rfl⟩ : syracuseStep 515837 = 193439) (by norm_num)
theorem B515861 : Blo 342753 515861 := bbase (se 6 (by rfl) ⟨12090, by rfl⟩ : syracuseStep 515861 = 24181) (by norm_num)
theorem B778013 : Blo 342753 778013 := bbase (se 3 (by rfl) ⟨145877, by rfl⟩ : syracuseStep 778013 = 291755) (by norm_num)
theorem B515885 : Blo 342753 515885 := bbase (se 3 (by rfl) ⟨96728, by rfl⟩ : syracuseStep 515885 = 193457) (by norm_num)
theorem B515909 : Blo 342753 515909 := bbase (se 4 (by rfl) ⟨48366, by rfl⟩ : syracuseStep 515909 = 96733) (by norm_num)
theorem B515933 : Blo 342753 515933 := bbase (se 3 (by rfl) ⟨96737, by rfl⟩ : syracuseStep 515933 = 193475) (by norm_num)
theorem B778085 : Blo 342753 778085 := bbase (se 4 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 778085 = 145891) (by norm_num)
theorem B581485 : Blo 342753 581485 := bbase (se 3 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 581485 = 218057) (by norm_num)
theorem B1302389 : Blo 342753 1302389 := bbase (se 5 (by rfl) ⟨61049, by rfl⟩ : syracuseStep 1302389 = 122099) (by norm_num)
theorem B515957 : Blo 342753 515957 := bbase (se 5 (by rfl) ⟨24185, by rfl⟩ : syracuseStep 515957 = 48371) (by norm_num)
theorem B515981 : Blo 342753 515981 := bbase (se 3 (by rfl) ⟨96746, by rfl⟩ : syracuseStep 515981 = 193493) (by norm_num)
theorem B516005 : Blo 342753 516005 := bbase (se 4 (by rfl) ⟨48375, by rfl⟩ : syracuseStep 516005 = 96751) (by norm_num)
theorem B778157 : Blo 342753 778157 := bbase (se 3 (by rfl) ⟨145904, by rfl⟩ : syracuseStep 778157 = 291809) (by norm_num)
theorem B516029 : Blo 342753 516029 := bbase (se 3 (by rfl) ⟨96755, by rfl⟩ : syracuseStep 516029 = 193511) (by norm_num)
theorem B581573 : Blo 342753 581573 := bbase (se 4 (by rfl) ⟨54522, by rfl⟩ : syracuseStep 581573 = 109045) (by norm_num)
theorem B516053 : Blo 342753 516053 := bbase (se 7 (by rfl) ⟨6047, by rfl⟩ : syracuseStep 516053 = 12095) (by norm_num)
theorem B516077 : Blo 342753 516077 := bbase (se 3 (by rfl) ⟨96764, by rfl⟩ : syracuseStep 516077 = 193529) (by norm_num)
theorem B778229 : Blo 342753 778229 := bbase (se 5 (by rfl) ⟨36479, by rfl⟩ : syracuseStep 778229 = 72959) (by norm_num)
theorem B876541 : Blo 342753 876541 := bbase (se 3 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 876541 = 328703) (by norm_num)
theorem B516101 : Blo 342753 516101 := bbase (se 4 (by rfl) ⟨48384, by rfl⟩ : syracuseStep 516101 = 96769) (by norm_num)
theorem B516125 : Blo 342753 516125 := bbase (se 3 (by rfl) ⟨96773, by rfl⟩ : syracuseStep 516125 = 193547) (by norm_num)
theorem B516149 : Blo 342753 516149 := bbase (se 5 (by rfl) ⟨24194, by rfl⟩ : syracuseStep 516149 = 48389) (by norm_num)
theorem B778301 : Blo 342753 778301 := bbase (se 3 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 778301 = 291863) (by norm_num)
theorem B1564741 : Blo 342753 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B581701 : Blo 342753 581701 := bbase (se 4 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 581701 = 109069) (by norm_num)
theorem B516173 : Blo 342753 516173 := bbase (se 3 (by rfl) ⟨96782, by rfl⟩ : syracuseStep 516173 = 193565) (by norm_num)
theorem B516197 : Blo 342753 516197 := bbase (se 4 (by rfl) ⟨48393, by rfl⟩ : syracuseStep 516197 = 96787) (by norm_num)
theorem B876653 : Blo 342753 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B516221 : Blo 342753 516221 := bbase (se 3 (by rfl) ⟨96791, by rfl⟩ : syracuseStep 516221 = 193583) (by norm_num)
theorem B778373 : Blo 342753 778373 := bbase (se 4 (by rfl) ⟨72972, by rfl⟩ : syracuseStep 778373 = 145945) (by norm_num)
theorem B516245 : Blo 342753 516245 := bbase (se 6 (by rfl) ⟨12099, by rfl⟩ : syracuseStep 516245 = 24199) (by norm_num)
theorem B581789 : Blo 342753 581789 := bbase (se 3 (by rfl) ⟨109085, by rfl⟩ : syracuseStep 581789 = 218171) (by norm_num)
theorem B516269 : Blo 342753 516269 := bbase (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) (by norm_num)
theorem B516293 : Blo 342753 516293 := bbase (se 4 (by rfl) ⟨48402, by rfl⟩ : syracuseStep 516293 = 96805) (by norm_num)
theorem B778445 : Blo 342753 778445 := bbase (se 3 (by rfl) ⟨145958, by rfl⟩ : syracuseStep 778445 = 291917) (by norm_num)
theorem B516317 : Blo 342753 516317 := bbase (se 3 (by rfl) ⟨96809, by rfl⟩ : syracuseStep 516317 = 193619) (by norm_num)
theorem B516341 : Blo 342753 516341 := bbase (se 5 (by rfl) ⟨24203, by rfl⟩ : syracuseStep 516341 = 48407) (by norm_num)
theorem B516365 : Blo 342753 516365 := bbase (se 3 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 516365 = 193637) (by norm_num)
theorem B778517 : Blo 342753 778517 := bbase (se 6 (by rfl) ⟨18246, by rfl⟩ : syracuseStep 778517 = 36493) (by norm_num)
theorem B581917 : Blo 342753 581917 := bbase (se 3 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 581917 = 218219) (by norm_num)
theorem B516389 : Blo 342753 516389 := bbase (se 4 (by rfl) ⟨48411, by rfl⟩ : syracuseStep 516389 = 96823) (by norm_num)
theorem B876845 : Blo 342753 876845 := bbase (se 3 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 876845 = 328817) (by norm_num)
theorem B516413 : Blo 342753 516413 := bbase (se 3 (by rfl) ⟨96827, by rfl⟩ : syracuseStep 516413 = 193655) (by norm_num)
theorem B1466693 : Blo 342753 1466693 := bbase (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) (by norm_num)
theorem B516437 : Blo 342753 516437 := bbase (se 10 (by rfl) ⟨756, by rfl⟩ : syracuseStep 516437 = 1513) (by norm_num)
theorem B778589 : Blo 342753 778589 := bbase (se 3 (by rfl) ⟨145985, by rfl⟩ : syracuseStep 778589 = 291971) (by norm_num)
theorem B516461 : Blo 342753 516461 := bbase (se 3 (by rfl) ⟨96836, by rfl⟩ : syracuseStep 516461 = 193673) (by norm_num)
theorem B582005 : Blo 342753 582005 := bbase (se 5 (by rfl) ⟨27281, by rfl⟩ : syracuseStep 582005 = 54563) (by norm_num)
theorem B516485 : Blo 342753 516485 := bbase (se 4 (by rfl) ⟨48420, by rfl⟩ : syracuseStep 516485 = 96841) (by norm_num)
theorem B516509 : Blo 342753 516509 := bbase (se 3 (by rfl) ⟨96845, by rfl⟩ : syracuseStep 516509 = 193691) (by norm_num)
theorem B778661 : Blo 342753 778661 := bbase (se 4 (by rfl) ⟨72999, by rfl⟩ : syracuseStep 778661 = 145999) (by norm_num)
theorem B516533 : Blo 342753 516533 := bbase (se 5 (by rfl) ⟨24212, by rfl⟩ : syracuseStep 516533 = 48425) (by norm_num)
theorem B516557 : Blo 342753 516557 := bbase (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) (by norm_num)
theorem B516581 : Blo 342753 516581 := bbase (se 4 (by rfl) ⟨48429, by rfl⟩ : syracuseStep 516581 = 96859) (by norm_num)
theorem B778733 : Blo 342753 778733 := bbase (se 3 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 778733 = 292025) (by norm_num)
theorem B1237493 : Blo 342753 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B582133 : Blo 342753 582133 := bbase (se 5 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 582133 = 54575) (by norm_num)
theorem B516605 : Blo 342753 516605 := bbase (se 3 (by rfl) ⟨96863, by rfl⟩ : syracuseStep 516605 = 193727) (by norm_num)
theorem B516629 : Blo 342753 516629 := bbase (se 6 (by rfl) ⟨12108, by rfl⟩ : syracuseStep 516629 = 24217) (by norm_num)
theorem B516653 : Blo 342753 516653 := bbase (se 3 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 516653 = 193745) (by norm_num)
theorem B778805 : Blo 342753 778805 := bbase (se 5 (by rfl) ⟨36506, by rfl⟩ : syracuseStep 778805 = 73013) (by norm_num)
theorem B516677 : Blo 342753 516677 := bbase (se 4 (by rfl) ⟨48438, by rfl⟩ : syracuseStep 516677 = 96877) (by norm_num)
theorem B1008197 : Blo 342753 1008197 := bbase (se 4 (by rfl) ⟨94518, by rfl⟩ : syracuseStep 1008197 = 189037) (by norm_num)
theorem B385609 : Blo 342753 385609 := bbase (se 2 (by rfl) ⟨144603, by rfl⟩ : syracuseStep 385609 = 289207) (by norm_num)
theorem B582221 : Blo 342753 582221 := bbase (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) (by norm_num)
theorem B516701 : Blo 342753 516701 := bbase (se 3 (by rfl) ⟨96881, by rfl⟩ : syracuseStep 516701 = 193763) (by norm_num)
theorem B385645 : Blo 342753 385645 := bbase (se 3 (by rfl) ⟨72308, by rfl⟩ : syracuseStep 385645 = 144617) (by norm_num)
theorem B516725 : Blo 342753 516725 := bbase (se 5 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 516725 = 48443) (by norm_num)
theorem B778877 : Blo 342753 778877 := bbase (se 3 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 778877 = 292079) (by norm_num)
theorem B1237637 : Blo 342753 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B877189 : Blo 342753 877189 := bbase (se 4 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 877189 = 164473) (by norm_num)
theorem B516749 : Blo 342753 516749 := bbase (se 3 (by rfl) ⟨96890, by rfl⟩ : syracuseStep 516749 = 193781) (by norm_num)
theorem B385681 : Blo 342753 385681 := bbase (se 2 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 385681 = 289261) (by norm_num)
theorem B1106581 : Blo 342753 1106581 := bbase (se 6 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 1106581 = 51871) (by norm_num)
theorem B516773 : Blo 342753 516773 := bbase (se 4 (by rfl) ⟨48447, by rfl⟩ : syracuseStep 516773 = 96895) (by norm_num)
theorem B385717 : Blo 342753 385717 := bbase (se 5 (by rfl) ⟨18080, by rfl⟩ : syracuseStep 385717 = 36161) (by norm_num)
theorem B516797 : Blo 342753 516797 := bbase (se 3 (by rfl) ⟨96899, by rfl⟩ : syracuseStep 516797 = 193799) (by norm_num)
theorem B778949 : Blo 342753 778949 := bbase (se 4 (by rfl) ⟨73026, by rfl⟩ : syracuseStep 778949 = 146053) (by norm_num)
theorem B582349 : Blo 342753 582349 := bbase (se 3 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 582349 = 218381) (by norm_num)
theorem B516821 : Blo 342753 516821 := bbase (se 7 (by rfl) ⟨6056, by rfl⟩ : syracuseStep 516821 = 12113) (by norm_num)
theorem B385753 : Blo 342753 385753 := bbase (se 2 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 385753 = 289315) (by norm_num)
theorem B516845 : Blo 342753 516845 := bbase (se 3 (by rfl) ⟨96908, by rfl⟩ : syracuseStep 516845 = 193817) (by norm_num)
theorem B877301 : Blo 342753 877301 := bbase (se 5 (by rfl) ⟨41123, by rfl⟩ : syracuseStep 877301 = 82247) (by norm_num)
theorem B385789 : Blo 342753 385789 := bbase (se 3 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 385789 = 144671) (by norm_num)
theorem B516869 : Blo 342753 516869 := bbase (se 4 (by rfl) ⟨48456, by rfl⟩ : syracuseStep 516869 = 96913) (by norm_num)
theorem B779021 : Blo 342753 779021 := bbase (se 3 (by rfl) ⟨146066, by rfl⟩ : syracuseStep 779021 = 292133) (by norm_num)
theorem B516893 : Blo 342753 516893 := bbase (se 3 (by rfl) ⟨96917, by rfl⟩ : syracuseStep 516893 = 193835) (by norm_num)
theorem B385825 : Blo 342753 385825 := bbase (se 2 (by rfl) ⟨144684, by rfl⟩ : syracuseStep 385825 = 289369) (by norm_num)
theorem B582437 : Blo 342753 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B516917 : Blo 342753 516917 := bbase (se 5 (by rfl) ⟨24230, by rfl⟩ : syracuseStep 516917 = 48461) (by norm_num)
theorem B385861 : Blo 342753 385861 := bbase (se 4 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 385861 = 72349) (by norm_num)
theorem B516941 : Blo 342753 516941 := bbase (se 3 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 516941 = 193853) (by norm_num)
theorem B1663829 : Blo 342753 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B779093 : Blo 342753 779093 := bbase (se 9 (by rfl) ⟨2282, by rfl⟩ : syracuseStep 779093 = 4565) (by norm_num)
theorem B516965 : Blo 342753 516965 := bbase (se 4 (by rfl) ⟨48465, by rfl⟩ : syracuseStep 516965 = 96931) (by norm_num)
theorem B385897 : Blo 342753 385897 := bbase (se 2 (by rfl) ⟨144711, by rfl⟩ : syracuseStep 385897 = 289423) (by norm_num)
theorem B516989 : Blo 342753 516989 := bbase (se 3 (by rfl) ⟨96935, by rfl⟩ : syracuseStep 516989 = 193871) (by norm_num)
theorem B385933 : Blo 342753 385933 := bbase (se 3 (by rfl) ⟨72362, by rfl⟩ : syracuseStep 385933 = 144725) (by norm_num)
theorem B517013 : Blo 342753 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B779165 : Blo 342753 779165 := bbase (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) (by norm_num)
theorem B582565 : Blo 342753 582565 := bbase (se 4 (by rfl) ⟨54615, by rfl⟩ : syracuseStep 582565 = 109231) (by norm_num)
theorem B517037 : Blo 342753 517037 := bbase (se 3 (by rfl) ⟨96944, by rfl⟩ : syracuseStep 517037 = 193889) (by norm_num)
theorem B385969 : Blo 342753 385969 := bbase (se 2 (by rfl) ⟨144738, by rfl⟩ : syracuseStep 385969 = 289477) (by norm_num)
theorem B877493 : Blo 342753 877493 := bbase (se 5 (by rfl) ⟨41132, by rfl⟩ : syracuseStep 877493 = 82265) (by norm_num)
theorem B517061 : Blo 342753 517061 := bbase (se 4 (by rfl) ⟨48474, by rfl⟩ : syracuseStep 517061 = 96949) (by norm_num)
theorem B386005 : Blo 342753 386005 := bbase (se 7 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 386005 = 9047) (by norm_num)
theorem B517085 : Blo 342753 517085 := bbase (se 3 (by rfl) ⟨96953, by rfl⟩ : syracuseStep 517085 = 193907) (by norm_num)
theorem B779237 : Blo 342753 779237 := bbase (se 4 (by rfl) ⟨73053, by rfl⟩ : syracuseStep 779237 = 146107) (by norm_num)
theorem B517109 : Blo 342753 517109 := bbase (se 5 (by rfl) ⟨24239, by rfl⟩ : syracuseStep 517109 = 48479) (by norm_num)
theorem B386041 : Blo 342753 386041 := bbase (se 2 (by rfl) ⟨144765, by rfl⟩ : syracuseStep 386041 = 289531) (by norm_num)
theorem B582653 : Blo 342753 582653 := bbase (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) (by norm_num)
theorem B517133 : Blo 342753 517133 := bbase (se 3 (by rfl) ⟨96962, by rfl⟩ : syracuseStep 517133 = 193925) (by norm_num)
theorem B1303573 : Blo 342753 1303573 := bbase (se 6 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 1303573 = 61105) (by norm_num)
theorem B386077 : Blo 342753 386077 := bbase (se 3 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 386077 = 144779) (by norm_num)
theorem B517157 : Blo 342753 517157 := bbase (se 4 (by rfl) ⟨48483, by rfl⟩ : syracuseStep 517157 = 96967) (by norm_num)
theorem B779309 : Blo 342753 779309 := bbase (se 3 (by rfl) ⟨146120, by rfl⟩ : syracuseStep 779309 = 292241) (by norm_num)
theorem B517181 : Blo 342753 517181 := bbase (se 3 (by rfl) ⟨96971, by rfl⟩ : syracuseStep 517181 = 193943) (by norm_num)
theorem B386113 : Blo 342753 386113 := bbase (se 2 (by rfl) ⟨144792, by rfl⟩ : syracuseStep 386113 = 289585) (by norm_num)
theorem B517205 : Blo 342753 517205 := bbase (se 8 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 517205 = 6061) (by norm_num)
theorem B386149 : Blo 342753 386149 := bbase (se 4 (by rfl) ⟨36201, by rfl⟩ : syracuseStep 386149 = 72403) (by norm_num)
theorem B517229 : Blo 342753 517229 := bbase (se 3 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 517229 = 193961) (by norm_num)
theorem B779381 : Blo 342753 779381 := bbase (se 5 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 779381 = 73067) (by norm_num)
theorem B582781 : Blo 342753 582781 := bbase (se 3 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 582781 = 218543) (by norm_num)
theorem B517253 : Blo 342753 517253 := bbase (se 4 (by rfl) ⟨48492, by rfl⟩ : syracuseStep 517253 = 96985) (by norm_num)
theorem B386185 : Blo 342753 386185 := bbase (se 2 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 386185 = 289639) (by norm_num)
theorem B517277 : Blo 342753 517277 := bbase (se 3 (by rfl) ⟨96989, by rfl⟩ : syracuseStep 517277 = 193979) (by norm_num)
theorem B386221 : Blo 342753 386221 := bbase (se 3 (by rfl) ⟨72416, by rfl⟩ : syracuseStep 386221 = 144833) (by norm_num)
theorem B517301 : Blo 342753 517301 := bbase (se 5 (by rfl) ⟨24248, by rfl⟩ : syracuseStep 517301 = 48497) (by norm_num)
theorem B779453 : Blo 342753 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B517325 : Blo 342753 517325 := bbase (se 3 (by rfl) ⟨96998, by rfl⟩ : syracuseStep 517325 = 193997) (by norm_num)
theorem B386257 : Blo 342753 386257 := bbase (se 2 (by rfl) ⟨144846, by rfl⟩ : syracuseStep 386257 = 289693) (by norm_num)
theorem B582869 : Blo 342753 582869 := bbase (se 7 (by rfl) ⟨6830, by rfl⟩ : syracuseStep 582869 = 13661) (by norm_num)
theorem B517349 : Blo 342753 517349 := bbase (se 4 (by rfl) ⟨48501, by rfl⟩ : syracuseStep 517349 = 97003) (by norm_num)
theorem B1500389 : Blo 342753 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B386293 : Blo 342753 386293 := bbase (se 5 (by rfl) ⟨18107, by rfl⟩ : syracuseStep 386293 = 36215) (by norm_num)
theorem B517373 : Blo 342753 517373 := bbase (se 3 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 517373 = 194015) (by norm_num)
theorem B779525 : Blo 342753 779525 := bbase (se 4 (by rfl) ⟨73080, by rfl⟩ : syracuseStep 779525 = 146161) (by norm_num)
theorem B517397 : Blo 342753 517397 := bbase (se 6 (by rfl) ⟨12126, by rfl⟩ : syracuseStep 517397 = 24253) (by norm_num)
theorem B386329 : Blo 342753 386329 := bbase (se 2 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 386329 = 289747) (by norm_num)
theorem B517421 : Blo 342753 517421 := bbase (se 3 (by rfl) ⟨97016, by rfl⟩ : syracuseStep 517421 = 194033) (by norm_num)
theorem B386365 : Blo 342753 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B1303877 : Blo 342753 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B517445 : Blo 342753 517445 := bbase (se 4 (by rfl) ⟨48510, by rfl⟩ : syracuseStep 517445 = 97021) (by norm_num)
theorem B779597 : Blo 342753 779597 := bbase (se 3 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 779597 = 292349) (by norm_num)
theorem B582997 : Blo 342753 582997 := bbase (se 12 (by rfl) ⟨213, by rfl⟩ : syracuseStep 582997 = 427) (by norm_num)
theorem B517469 : Blo 342753 517469 := bbase (se 3 (by rfl) ⟨97025, by rfl⟩ : syracuseStep 517469 = 194051) (by norm_num)
theorem B386401 : Blo 342753 386401 := bbase (se 2 (by rfl) ⟨144900, by rfl⟩ : syracuseStep 386401 = 289801) (by norm_num)
theorem B550253 : Blo 342753 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B517493 : Blo 342753 517493 := bbase (se 5 (by rfl) ⟨24257, by rfl⟩ : syracuseStep 517493 = 48515) (by norm_num)
theorem B386437 : Blo 342753 386437 := bbase (se 4 (by rfl) ⟨36228, by rfl⟩ : syracuseStep 386437 = 72457) (by norm_num)
theorem B517517 : Blo 342753 517517 := bbase (se 3 (by rfl) ⟨97034, by rfl⟩ : syracuseStep 517517 = 194069) (by norm_num)
theorem B779669 : Blo 342753 779669 := bbase (se 6 (by rfl) ⟨18273, by rfl⟩ : syracuseStep 779669 = 36547) (by norm_num)
theorem B517541 : Blo 342753 517541 := bbase (se 4 (by rfl) ⟨48519, by rfl⟩ : syracuseStep 517541 = 97039) (by norm_num)
theorem B386473 : Blo 342753 386473 := bbase (se 2 (by rfl) ⟨144927, by rfl⟩ : syracuseStep 386473 = 289855) (by norm_num)
theorem B583085 : Blo 342753 583085 := bbase (se 3 (by rfl) ⟨109328, by rfl⟩ : syracuseStep 583085 = 218657) (by norm_num)
theorem B517565 : Blo 342753 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B386509 : Blo 342753 386509 := bbase (se 3 (by rfl) ⟨72470, by rfl⟩ : syracuseStep 386509 = 144941) (by norm_num)
theorem B517589 : Blo 342753 517589 := bbase (se 7 (by rfl) ⟨6065, by rfl⟩ : syracuseStep 517589 = 12131) (by norm_num)
theorem B779741 : Blo 342753 779741 := bbase (se 3 (by rfl) ⟨146201, by rfl⟩ : syracuseStep 779741 = 292403) (by norm_num)
theorem B517613 : Blo 342753 517613 := bbase (se 3 (by rfl) ⟨97052, by rfl⟩ : syracuseStep 517613 = 194105) (by norm_num)
theorem B386545 : Blo 342753 386545 := bbase (se 2 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 386545 = 289909) (by norm_num)
theorem B517637 : Blo 342753 517637 := bbase (se 4 (by rfl) ⟨48528, by rfl⟩ : syracuseStep 517637 = 97057) (by norm_num)
theorem B386581 : Blo 342753 386581 := bbase (se 6 (by rfl) ⟨9060, by rfl⟩ : syracuseStep 386581 = 18121) (by norm_num)
theorem B517661 : Blo 342753 517661 := bbase (se 3 (by rfl) ⟨97061, by rfl⟩ : syracuseStep 517661 = 194123) (by norm_num)
theorem B779813 : Blo 342753 779813 := bbase (se 4 (by rfl) ⟨73107, by rfl⟩ : syracuseStep 779813 = 146215) (by norm_num)
theorem B583213 : Blo 342753 583213 := bbase (se 3 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 583213 = 218705) (by norm_num)
theorem B517685 : Blo 342753 517685 := bbase (se 5 (by rfl) ⟨24266, by rfl⟩ : syracuseStep 517685 = 48533) (by norm_num)
theorem B386617 : Blo 342753 386617 := bbase (se 2 (by rfl) ⟨144981, by rfl⟩ : syracuseStep 386617 = 289963) (by norm_num)
theorem B517709 : Blo 342753 517709 := bbase (se 3 (by rfl) ⟨97070, by rfl⟩ : syracuseStep 517709 = 194141) (by norm_num)
theorem B386653 : Blo 342753 386653 := bbase (se 3 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 386653 = 144995) (by norm_num)
theorem B517733 : Blo 342753 517733 := bbase (se 4 (by rfl) ⟨48537, by rfl⟩ : syracuseStep 517733 = 97075) (by norm_num)
theorem B779885 : Blo 342753 779885 := bbase (se 3 (by rfl) ⟨146228, by rfl⟩ : syracuseStep 779885 = 292457) (by norm_num)
theorem B517757 : Blo 342753 517757 := bbase (se 3 (by rfl) ⟨97079, by rfl⟩ : syracuseStep 517757 = 194159) (by norm_num)
theorem B386689 : Blo 342753 386689 := bbase (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) (by norm_num)
theorem B583301 : Blo 342753 583301 := bbase (se 4 (by rfl) ⟨54684, by rfl⟩ : syracuseStep 583301 = 109369) (by norm_num)
theorem B517781 : Blo 342753 517781 := bbase (se 6 (by rfl) ⟨12135, by rfl⟩ : syracuseStep 517781 = 24271) (by norm_num)
theorem B386725 : Blo 342753 386725 := bbase (se 4 (by rfl) ⟨36255, by rfl⟩ : syracuseStep 386725 = 72511) (by norm_num)
theorem B517805 : Blo 342753 517805 := bbase (se 3 (by rfl) ⟨97088, by rfl⟩ : syracuseStep 517805 = 194177) (by norm_num)
theorem B779957 : Blo 342753 779957 := bbase (se 5 (by rfl) ⟨36560, by rfl⟩ : syracuseStep 779957 = 73121) (by norm_num)
theorem B517829 : Blo 342753 517829 := bbase (se 4 (by rfl) ⟨48546, by rfl⟩ : syracuseStep 517829 = 97093) (by norm_num)
theorem B386761 : Blo 342753 386761 := bbase (se 2 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 386761 = 290071) (by norm_num)
theorem B517853 : Blo 342753 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B386797 : Blo 342753 386797 := bbase (se 3 (by rfl) ⟨72524, by rfl⟩ : syracuseStep 386797 = 145049) (by norm_num)
theorem B517877 : Blo 342753 517877 := bbase (se 5 (by rfl) ⟨24275, by rfl⟩ : syracuseStep 517877 = 48551) (by norm_num)
theorem B780029 : Blo 342753 780029 := bbase (se 3 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 780029 = 292511) (by norm_num)
theorem B583429 : Blo 342753 583429 := bbase (se 4 (by rfl) ⟨54696, by rfl⟩ : syracuseStep 583429 = 109393) (by norm_num)
theorem B517901 : Blo 342753 517901 := bbase (se 3 (by rfl) ⟨97106, by rfl⟩ : syracuseStep 517901 = 194213) (by norm_num)
theorem B386833 : Blo 342753 386833 := bbase (se 2 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 386833 = 290125) (by norm_num)
theorem B517925 : Blo 342753 517925 := bbase (se 4 (by rfl) ⟨48555, by rfl⟩ : syracuseStep 517925 = 97111) (by norm_num)
theorem B550709 : Blo 342753 550709 := bbase (se 5 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 550709 = 51629) (by norm_num)
theorem B386869 : Blo 342753 386869 := bbase (se 5 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 386869 = 36269) (by norm_num)
theorem B517949 : Blo 342753 517949 := bbase (se 3 (by rfl) ⟨97115, by rfl⟩ : syracuseStep 517949 = 194231) (by norm_num)
theorem B780101 : Blo 342753 780101 := bbase (se 4 (by rfl) ⟨73134, by rfl⟩ : syracuseStep 780101 = 146269) (by norm_num)
theorem B517973 : Blo 342753 517973 := bbase (se 9 (by rfl) ⟨1517, by rfl⟩ : syracuseStep 517973 = 3035) (by norm_num)
theorem B386905 : Blo 342753 386905 := bbase (se 2 (by rfl) ⟨145089, by rfl⟩ : syracuseStep 386905 = 290179) (by norm_num)
theorem B583517 : Blo 342753 583517 := bbase (se 3 (by rfl) ⟨109409, by rfl⟩ : syracuseStep 583517 = 218819) (by norm_num)
theorem B517997 : Blo 342753 517997 := bbase (se 3 (by rfl) ⟨97124, by rfl⟩ : syracuseStep 517997 = 194249) (by norm_num)
theorem B386941 : Blo 342753 386941 := bbase (se 3 (by rfl) ⟨72551, by rfl⟩ : syracuseStep 386941 = 145103) (by norm_num)
theorem B518021 : Blo 342753 518021 := bbase (se 4 (by rfl) ⟨48564, by rfl⟩ : syracuseStep 518021 = 97129) (by norm_num)
theorem B1402757 : Blo 342753 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B780173 : Blo 342753 780173 := bbase (se 3 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 780173 = 292565) (by norm_num)
theorem B518045 : Blo 342753 518045 := bbase (se 3 (by rfl) ⟨97133, by rfl⟩ : syracuseStep 518045 = 194267) (by norm_num)
theorem B386977 : Blo 342753 386977 := bbase (se 2 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 386977 = 290233) (by norm_num)
theorem B518069 : Blo 342753 518069 := bbase (se 5 (by rfl) ⟨24284, by rfl⟩ : syracuseStep 518069 = 48569) (by norm_num)
theorem B387013 : Blo 342753 387013 := bbase (se 4 (by rfl) ⟨36282, by rfl⟩ : syracuseStep 387013 = 72565) (by norm_num)
theorem B518093 : Blo 342753 518093 := bbase (se 3 (by rfl) ⟨97142, by rfl⟩ : syracuseStep 518093 = 194285) (by norm_num)
theorem B583645 : Blo 342753 583645 := bbase (se 3 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 583645 = 218867) (by norm_num)
theorem B518117 : Blo 342753 518117 := bbase (se 4 (by rfl) ⟨48573, by rfl⟩ : syracuseStep 518117 = 97147) (by norm_num)
theorem B387049 : Blo 342753 387049 := bbase (se 2 (by rfl) ⟨145143, by rfl⟩ : syracuseStep 387049 = 290287) (by norm_num)
theorem B518141 : Blo 342753 518141 := bbase (se 3 (by rfl) ⟨97151, by rfl⟩ : syracuseStep 518141 = 194303) (by norm_num)
theorem B387085 : Blo 342753 387085 := bbase (se 3 (by rfl) ⟨72578, by rfl⟩ : syracuseStep 387085 = 145157) (by norm_num)
theorem B518165 : Blo 342753 518165 := bbase (se 6 (by rfl) ⟨12144, by rfl⟩ : syracuseStep 518165 = 24289) (by norm_num)
theorem B1337381 : Blo 342753 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B518189 : Blo 342753 518189 := bbase (se 3 (by rfl) ⟨97160, by rfl⟩ : syracuseStep 518189 = 194321) (by norm_num)
theorem B387121 : Blo 342753 387121 := bbase (se 2 (by rfl) ⟨145170, by rfl⟩ : syracuseStep 387121 = 290341) (by norm_num)
theorem B1468469 : Blo 342753 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B583733 : Blo 342753 583733 := bbase (se 5 (by rfl) ⟨27362, by rfl⟩ : syracuseStep 583733 = 54725) (by norm_num)
theorem B518213 : Blo 342753 518213 := bbase (se 4 (by rfl) ⟨48582, by rfl⟩ : syracuseStep 518213 = 97165) (by norm_num)
theorem B387157 : Blo 342753 387157 := bbase (se 8 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 387157 = 4537) (by norm_num)
theorem B518237 : Blo 342753 518237 := bbase (se 3 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 518237 = 194339) (by norm_num)
theorem B976997 : Blo 342753 976997 := bbase (se 4 (by rfl) ⟨91593, by rfl⟩ : syracuseStep 976997 = 183187) (by norm_num)
theorem B518261 : Blo 342753 518261 := bbase (se 5 (by rfl) ⟨24293, by rfl⟩ : syracuseStep 518261 = 48587) (by norm_num)
theorem B387193 : Blo 342753 387193 := bbase (se 2 (by rfl) ⟨145197, by rfl⟩ : syracuseStep 387193 = 290395) (by norm_num)
theorem B518285 : Blo 342753 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B387229 : Blo 342753 387229 := bbase (se 3 (by rfl) ⟨72605, by rfl⟩ : syracuseStep 387229 = 145211) (by norm_num)
theorem B518309 : Blo 342753 518309 := bbase (se 4 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 518309 = 97183) (by norm_num)
theorem B583861 : Blo 342753 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B518333 : Blo 342753 518333 := bbase (se 3 (by rfl) ⟨97187, by rfl⟩ : syracuseStep 518333 = 194375) (by norm_num)
theorem B387265 : Blo 342753 387265 := bbase (se 2 (by rfl) ⟨145224, by rfl⟩ : syracuseStep 387265 = 290449) (by norm_num)
theorem B518357 : Blo 342753 518357 := bbase (se 7 (by rfl) ⟨6074, by rfl⟩ : syracuseStep 518357 = 12149) (by norm_num)
theorem B387301 : Blo 342753 387301 := bbase (se 4 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 387301 = 72619) (by norm_num)
theorem B518381 : Blo 342753 518381 := bbase (se 3 (by rfl) ⟨97196, by rfl⟩ : syracuseStep 518381 = 194393) (by norm_num)
theorem B518405 : Blo 342753 518405 := bbase (se 4 (by rfl) ⟨48600, by rfl⟩ : syracuseStep 518405 = 97201) (by norm_num)
theorem B387337 : Blo 342753 387337 := bbase (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) (by norm_num)
theorem B583949 : Blo 342753 583949 := bbase (se 3 (by rfl) ⟨109490, by rfl⟩ : syracuseStep 583949 = 218981) (by norm_num)
theorem B518429 : Blo 342753 518429 := bbase (se 3 (by rfl) ⟨97205, by rfl⟩ : syracuseStep 518429 = 194411) (by norm_num)
theorem B387373 : Blo 342753 387373 := bbase (se 3 (by rfl) ⟨72632, by rfl⟩ : syracuseStep 387373 = 145265) (by norm_num)
theorem B518453 : Blo 342753 518453 := bbase (se 5 (by rfl) ⟨24302, by rfl⟩ : syracuseStep 518453 = 48605) (by norm_num)
theorem B518477 : Blo 342753 518477 := bbase (se 3 (by rfl) ⟨97214, by rfl⟩ : syracuseStep 518477 = 194429) (by norm_num)
theorem B387409 : Blo 342753 387409 := bbase (se 2 (by rfl) ⟨145278, by rfl⟩ : syracuseStep 387409 = 290557) (by norm_num)
theorem B518501 : Blo 342753 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B387445 : Blo 342753 387445 := bbase (se 5 (by rfl) ⟨18161, by rfl⟩ : syracuseStep 387445 = 36323) (by norm_num)
theorem B518525 : Blo 342753 518525 := bbase (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) (by norm_num)
theorem B584077 : Blo 342753 584077 := bbase (se 3 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 584077 = 219029) (by norm_num)
theorem B518549 : Blo 342753 518549 := bbase (se 6 (by rfl) ⟨12153, by rfl⟩ : syracuseStep 518549 = 24307) (by norm_num)
theorem B387481 : Blo 342753 387481 := bbase (se 2 (by rfl) ⟨145305, by rfl⟩ : syracuseStep 387481 = 290611) (by norm_num)
theorem B518573 : Blo 342753 518573 := bbase (se 3 (by rfl) ⟨97232, by rfl⟩ : syracuseStep 518573 = 194465) (by norm_num)
theorem B1173941 : Blo 342753 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B387517 : Blo 342753 387517 := bbase (se 3 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 387517 = 145319) (by norm_num)
theorem B518597 : Blo 342753 518597 := bbase (se 4 (by rfl) ⟨48618, by rfl⟩ : syracuseStep 518597 = 97237) (by norm_num)
theorem B518621 : Blo 342753 518621 := bbase (se 3 (by rfl) ⟨97241, by rfl⟩ : syracuseStep 518621 = 194483) (by norm_num)
theorem B387553 : Blo 342753 387553 := bbase (se 2 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 387553 = 290665) (by norm_num)
theorem B584165 : Blo 342753 584165 := bbase (se 4 (by rfl) ⟨54765, by rfl⟩ : syracuseStep 584165 = 109531) (by norm_num)
theorem B518645 : Blo 342753 518645 := bbase (se 5 (by rfl) ⟨24311, by rfl⟩ : syracuseStep 518645 = 48623) (by norm_num)
theorem B387589 : Blo 342753 387589 := bbase (se 4 (by rfl) ⟨36336, by rfl⟩ : syracuseStep 387589 = 72673) (by norm_num)
theorem B518669 : Blo 342753 518669 := bbase (se 3 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 518669 = 194501) (by norm_num)
theorem B518693 : Blo 342753 518693 := bbase (se 4 (by rfl) ⟨48627, by rfl⟩ : syracuseStep 518693 = 97255) (by norm_num)
theorem B387625 : Blo 342753 387625 := bbase (se 2 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 387625 = 290719) (by norm_num)
theorem B518717 : Blo 342753 518717 := bbase (se 3 (by rfl) ⟨97259, by rfl⟩ : syracuseStep 518717 = 194519) (by norm_num)
theorem B387661 : Blo 342753 387661 := bbase (se 3 (by rfl) ⟨72686, by rfl⟩ : syracuseStep 387661 = 145373) (by norm_num)
theorem B518741 : Blo 342753 518741 := bbase (se 8 (by rfl) ⟨3039, by rfl⟩ : syracuseStep 518741 = 6079) (by norm_num)
theorem B584293 : Blo 342753 584293 := bbase (se 4 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 584293 = 109555) (by norm_num)
theorem B518765 : Blo 342753 518765 := bbase (se 3 (by rfl) ⟨97268, by rfl⟩ : syracuseStep 518765 = 194537) (by norm_num)
theorem B387697 : Blo 342753 387697 := bbase (se 2 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 387697 = 290773) (by norm_num)
theorem B518789 : Blo 342753 518789 := bbase (se 4 (by rfl) ⟨48636, by rfl⟩ : syracuseStep 518789 = 97273) (by norm_num)
theorem B387733 : Blo 342753 387733 := bbase (se 6 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 387733 = 18175) (by norm_num)
theorem B518813 : Blo 342753 518813 := bbase (se 3 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 518813 = 194555) (by norm_num)
theorem B518837 : Blo 342753 518837 := bbase (se 5 (by rfl) ⟨24320, by rfl⟩ : syracuseStep 518837 = 48641) (by norm_num)
theorem B387769 : Blo 342753 387769 := bbase (se 2 (by rfl) ⟨145413, by rfl⟩ : syracuseStep 387769 = 290827) (by norm_num)
theorem B584381 : Blo 342753 584381 := bbase (se 3 (by rfl) ⟨109571, by rfl⟩ : syracuseStep 584381 = 219143) (by norm_num)
theorem B518861 : Blo 342753 518861 := bbase (se 3 (by rfl) ⟨97286, by rfl⟩ : syracuseStep 518861 = 194573) (by norm_num)
theorem B387805 : Blo 342753 387805 := bbase (se 3 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 387805 = 145427) (by norm_num)
theorem B518885 : Blo 342753 518885 := bbase (se 4 (by rfl) ⟨48645, by rfl⟩ : syracuseStep 518885 = 97291) (by norm_num)
theorem B518909 : Blo 342753 518909 := bbase (se 3 (by rfl) ⟨97295, by rfl⟩ : syracuseStep 518909 = 194591) (by norm_num)
theorem B387841 : Blo 342753 387841 := bbase (se 2 (by rfl) ⟨145440, by rfl⟩ : syracuseStep 387841 = 290881) (by norm_num)
theorem B551701 : Blo 342753 551701 := bbase (se 6 (by rfl) ⟨12930, by rfl⟩ : syracuseStep 551701 = 25861) (by norm_num)
theorem B518933 : Blo 342753 518933 := bbase (se 6 (by rfl) ⟨12162, by rfl⟩ : syracuseStep 518933 = 24325) (by norm_num)
theorem B387877 : Blo 342753 387877 := bbase (se 4 (by rfl) ⟨36363, by rfl⟩ : syracuseStep 387877 = 72727) (by norm_num)
theorem B518957 : Blo 342753 518957 := bbase (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) (by norm_num)
theorem B584509 : Blo 342753 584509 := bbase (se 3 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 584509 = 219191) (by norm_num)
theorem B518981 : Blo 342753 518981 := bbase (se 4 (by rfl) ⟨48654, by rfl⟩ : syracuseStep 518981 = 97309) (by norm_num)
theorem B387913 : Blo 342753 387913 := bbase (se 2 (by rfl) ⟨145467, by rfl⟩ : syracuseStep 387913 = 290935) (by norm_num)
theorem B519005 : Blo 342753 519005 := bbase (se 3 (by rfl) ⟨97313, by rfl⟩ : syracuseStep 519005 = 194627) (by norm_num)
theorem B387949 : Blo 342753 387949 := bbase (se 3 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 387949 = 145481) (by norm_num)
theorem B519029 : Blo 342753 519029 := bbase (se 5 (by rfl) ⟨24329, by rfl⟩ : syracuseStep 519029 = 48659) (by norm_num)
theorem B519053 : Blo 342753 519053 := bbase (se 3 (by rfl) ⟨97322, by rfl⟩ : syracuseStep 519053 = 194645) (by norm_num)
theorem B387985 : Blo 342753 387985 := bbase (se 2 (by rfl) ⟨145494, by rfl⟩ : syracuseStep 387985 = 290989) (by norm_num)
theorem B584597 : Blo 342753 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B519077 : Blo 342753 519077 := bbase (se 4 (by rfl) ⟨48663, by rfl⟩ : syracuseStep 519077 = 97327) (by norm_num)
theorem B388021 : Blo 342753 388021 := bbase (se 5 (by rfl) ⟨18188, by rfl⟩ : syracuseStep 388021 = 36377) (by norm_num)
theorem B519101 : Blo 342753 519101 := bbase (se 3 (by rfl) ⟨97331, by rfl⟩ : syracuseStep 519101 = 194663) (by norm_num)
theorem B519125 : Blo 342753 519125 := bbase (se 7 (by rfl) ⟨6083, by rfl⟩ : syracuseStep 519125 = 12167) (by norm_num)
theorem B388057 : Blo 342753 388057 := bbase (se 2 (by rfl) ⟨145521, by rfl⟩ : syracuseStep 388057 = 291043) (by norm_num)
theorem B519149 : Blo 342753 519149 := bbase (se 3 (by rfl) ⟨97340, by rfl⟩ : syracuseStep 519149 = 194681) (by norm_num)
theorem B388093 : Blo 342753 388093 := bbase (se 3 (by rfl) ⟨72767, by rfl⟩ : syracuseStep 388093 = 145535) (by norm_num)
theorem B519173 : Blo 342753 519173 := bbase (se 4 (by rfl) ⟨48672, by rfl⟩ : syracuseStep 519173 = 97345) (by norm_num)
theorem B584725 : Blo 342753 584725 := bbase (se 6 (by rfl) ⟨13704, by rfl⟩ : syracuseStep 584725 = 27409) (by norm_num)
theorem B519197 : Blo 342753 519197 := bbase (se 3 (by rfl) ⟨97349, by rfl⟩ : syracuseStep 519197 = 194699) (by norm_num)
theorem B388129 : Blo 342753 388129 := bbase (se 2 (by rfl) ⟨145548, by rfl⟩ : syracuseStep 388129 = 291097) (by norm_num)
theorem B519221 : Blo 342753 519221 := bbase (se 5 (by rfl) ⟨24338, by rfl⟩ : syracuseStep 519221 = 48677) (by norm_num)
theorem B388165 : Blo 342753 388165 := bbase (se 4 (by rfl) ⟨36390, by rfl⟩ : syracuseStep 388165 = 72781) (by norm_num)
theorem B519245 : Blo 342753 519245 := bbase (se 3 (by rfl) ⟨97358, by rfl⟩ : syracuseStep 519245 = 194717) (by norm_num)
theorem B519269 : Blo 342753 519269 := bbase (se 4 (by rfl) ⟨48681, by rfl⟩ : syracuseStep 519269 = 97363) (by norm_num)
theorem B388201 : Blo 342753 388201 := bbase (se 2 (by rfl) ⟨145575, by rfl⟩ : syracuseStep 388201 = 291151) (by norm_num)
theorem B584813 : Blo 342753 584813 := bbase (se 3 (by rfl) ⟨109652, by rfl⟩ : syracuseStep 584813 = 219305) (by norm_num)
theorem B519293 : Blo 342753 519293 := bbase (se 3 (by rfl) ⟨97367, by rfl⟩ : syracuseStep 519293 = 194735) (by norm_num)
theorem B388237 : Blo 342753 388237 := bbase (se 3 (by rfl) ⟨72794, by rfl⟩ : syracuseStep 388237 = 145589) (by norm_num)
theorem B519317 : Blo 342753 519317 := bbase (se 6 (by rfl) ⟨12171, by rfl⟩ : syracuseStep 519317 = 24343) (by norm_num)
theorem B519341 : Blo 342753 519341 := bbase (se 3 (by rfl) ⟨97376, by rfl⟩ : syracuseStep 519341 = 194753) (by norm_num)
theorem B388273 : Blo 342753 388273 := bbase (se 2 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 388273 = 291205) (by norm_num)
theorem B421049 : Blo 342753 421049 := bbase (se 2 (by rfl) ⟨157893, by rfl⟩ : syracuseStep 421049 = 315787) (by norm_num)
theorem B519365 : Blo 342753 519365 := bbase (se 4 (by rfl) ⟨48690, by rfl⟩ : syracuseStep 519365 = 97381) (by norm_num)
theorem B388309 : Blo 342753 388309 := bbase (se 7 (by rfl) ⟨4550, by rfl⟩ : syracuseStep 388309 = 9101) (by norm_num)
theorem B519389 : Blo 342753 519389 := bbase (se 3 (by rfl) ⟨97385, by rfl⟩ : syracuseStep 519389 = 194771) (by norm_num)
theorem B584941 : Blo 342753 584941 := bbase (se 3 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 584941 = 219353) (by norm_num)
theorem B519413 : Blo 342753 519413 := bbase (se 5 (by rfl) ⟨24347, by rfl⟩ : syracuseStep 519413 = 48695) (by norm_num)
theorem B388345 : Blo 342753 388345 := bbase (se 2 (by rfl) ⟨145629, by rfl⟩ : syracuseStep 388345 = 291259) (by norm_num)
theorem B519437 : Blo 342753 519437 := bbase (se 3 (by rfl) ⟨97394, by rfl⟩ : syracuseStep 519437 = 194789) (by norm_num)
theorem B3534101 : Blo 342753 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B388381 : Blo 342753 388381 := bbase (se 3 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 388381 = 145643) (by norm_num)
theorem B519461 : Blo 342753 519461 := bbase (se 4 (by rfl) ⟨48699, by rfl⟩ : syracuseStep 519461 = 97399) (by norm_num)
theorem B421165 : Blo 342753 421165 := bbase (se 3 (by rfl) ⟨78968, by rfl⟩ : syracuseStep 421165 = 157937) (by norm_num)
theorem B519485 : Blo 342753 519485 := bbase (se 3 (by rfl) ⟨97403, by rfl⟩ : syracuseStep 519485 = 194807) (by norm_num)
theorem B388417 : Blo 342753 388417 := bbase (se 2 (by rfl) ⟨145656, by rfl⟩ : syracuseStep 388417 = 291313) (by norm_num)
theorem B585029 : Blo 342753 585029 := bbase (se 4 (by rfl) ⟨54846, by rfl⟩ : syracuseStep 585029 = 109693) (by norm_num)
theorem B519509 : Blo 342753 519509 := bbase (se 11 (by rfl) ⟨380, by rfl⟩ : syracuseStep 519509 = 761) (by norm_num)
theorem B388453 : Blo 342753 388453 := bbase (se 4 (by rfl) ⟨36417, by rfl⟩ : syracuseStep 388453 = 72835) (by norm_num)
theorem B519533 : Blo 342753 519533 := bbase (se 3 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 519533 = 194825) (by norm_num)
theorem B1305989 : Blo 342753 1305989 := bbase (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) (by norm_num)
theorem B519557 : Blo 342753 519557 := bbase (se 4 (by rfl) ⟨48708, by rfl⟩ : syracuseStep 519557 = 97417) (by norm_num)
theorem B388489 : Blo 342753 388489 := bbase (se 2 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 388489 = 291367) (by norm_num)
theorem B552349 : Blo 342753 552349 := bbase (se 3 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 552349 = 207131) (by norm_num)
theorem B519581 : Blo 342753 519581 := bbase (se 3 (by rfl) ⟨97421, by rfl⟩ : syracuseStep 519581 = 194843) (by norm_num)
theorem B781733 : Blo 342753 781733 := bbase (se 4 (by rfl) ⟨73287, by rfl⟩ : syracuseStep 781733 = 146575) (by norm_num)
theorem B388525 : Blo 342753 388525 := bbase (se 3 (by rfl) ⟨72848, by rfl⟩ : syracuseStep 388525 = 145697) (by norm_num)
theorem B519605 : Blo 342753 519605 := bbase (se 5 (by rfl) ⟨24356, by rfl⟩ : syracuseStep 519605 = 48713) (by norm_num)
theorem B1174981 : Blo 342753 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B945605 : Blo 342753 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B519629 : Blo 342753 519629 := bbase (se 3 (by rfl) ⟨97430, by rfl⟩ : syracuseStep 519629 = 194861) (by norm_num)
theorem B388561 : Blo 342753 388561 := bbase (se 2 (by rfl) ⟨145710, by rfl⟩ : syracuseStep 388561 = 291421) (by norm_num)
theorem B1109477 : Blo 342753 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B519653 : Blo 342753 519653 := bbase (se 4 (by rfl) ⟨48717, by rfl⟩ : syracuseStep 519653 = 97435) (by norm_num)
theorem B388597 : Blo 342753 388597 := bbase (se 5 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 388597 = 36431) (by norm_num)
theorem B519677 : Blo 342753 519677 := bbase (se 3 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 519677 = 194879) (by norm_num)
theorem B519701 : Blo 342753 519701 := bbase (se 6 (by rfl) ⟨12180, by rfl⟩ : syracuseStep 519701 = 24361) (by norm_num)
theorem B388633 : Blo 342753 388633 := bbase (se 2 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 388633 = 291475) (by norm_num)
theorem B519725 : Blo 342753 519725 := bbase (se 3 (by rfl) ⟨97448, by rfl⟩ : syracuseStep 519725 = 194897) (by norm_num)
theorem B2780725 : Blo 342753 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B388669 : Blo 342753 388669 := bbase (se 3 (by rfl) ⟨72875, by rfl⟩ : syracuseStep 388669 = 145751) (by norm_num)
theorem B519749 : Blo 342753 519749 := bbase (se 4 (by rfl) ⟨48726, by rfl⟩ : syracuseStep 519749 = 97453) (by norm_num)
theorem B650845 : Blo 342753 650845 := bbase (se 3 (by rfl) ⟨122033, by rfl⟩ : syracuseStep 650845 = 244067) (by norm_num)
theorem B519773 : Blo 342753 519773 := bbase (se 3 (by rfl) ⟨97457, by rfl⟩ : syracuseStep 519773 = 194915) (by norm_num)
theorem B388705 : Blo 342753 388705 := bbase (se 2 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 388705 = 291529) (by norm_num)
theorem B519797 : Blo 342753 519797 := bbase (se 5 (by rfl) ⟨24365, by rfl⟩ : syracuseStep 519797 = 48731) (by norm_num)
theorem B388741 : Blo 342753 388741 := bbase (se 4 (by rfl) ⟨36444, by rfl⟩ : syracuseStep 388741 = 72889) (by norm_num)
theorem B519821 : Blo 342753 519821 := bbase (se 3 (by rfl) ⟨97466, by rfl⟩ : syracuseStep 519821 = 194933) (by norm_num)
theorem B978581 : Blo 342753 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B1306277 : Blo 342753 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B519845 : Blo 342753 519845 := bbase (se 4 (by rfl) ⟨48735, by rfl⟩ : syracuseStep 519845 = 97471) (by norm_num)
theorem B388777 : Blo 342753 388777 := bbase (se 2 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 388777 = 291583) (by norm_num)
theorem B519869 : Blo 342753 519869 := bbase (se 3 (by rfl) ⟨97475, by rfl⟩ : syracuseStep 519869 = 194951) (by norm_num)
theorem B388813 : Blo 342753 388813 := bbase (se 3 (by rfl) ⟨72902, by rfl⟩ : syracuseStep 388813 = 145805) (by norm_num)
theorem B519893 : Blo 342753 519893 := bbase (se 7 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 519893 = 12185) (by norm_num)
theorem B618221 : Blo 342753 618221 := bbase (se 3 (by rfl) ⟨115916, by rfl⟩ : syracuseStep 618221 = 231833) (by norm_num)
theorem B519917 : Blo 342753 519917 := bbase (se 3 (by rfl) ⟨97484, by rfl⟩ : syracuseStep 519917 = 194969) (by norm_num)
theorem B388849 : Blo 342753 388849 := bbase (se 2 (by rfl) ⟨145818, by rfl⟩ : syracuseStep 388849 = 291637) (by norm_num)
theorem B519941 : Blo 342753 519941 := bbase (se 4 (by rfl) ⟨48744, by rfl⟩ : syracuseStep 519941 = 97489) (by norm_num)
theorem B2617109 : Blo 342753 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B388885 : Blo 342753 388885 := bbase (se 6 (by rfl) ⟨9114, by rfl⟩ : syracuseStep 388885 = 18229) (by norm_num)
theorem B519965 : Blo 342753 519965 := bbase (se 3 (by rfl) ⟨97493, by rfl⟩ : syracuseStep 519965 = 194987) (by norm_num)
theorem B519989 : Blo 342753 519989 := bbase (se 5 (by rfl) ⟨24374, by rfl⟩ : syracuseStep 519989 = 48749) (by norm_num)
theorem B388921 : Blo 342753 388921 := bbase (se 2 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 388921 = 291691) (by norm_num)
theorem B520013 : Blo 342753 520013 := bbase (se 3 (by rfl) ⟨97502, by rfl⟩ : syracuseStep 520013 = 195005) (by norm_num)
theorem B388957 : Blo 342753 388957 := bbase (se 3 (by rfl) ⟨72929, by rfl⟩ : syracuseStep 388957 = 145859) (by norm_num)
theorem B520037 : Blo 342753 520037 := bbase (se 4 (by rfl) ⟨48753, by rfl⟩ : syracuseStep 520037 = 97507) (by norm_num)
theorem B520061 : Blo 342753 520061 := bbase (se 3 (by rfl) ⟨97511, by rfl⟩ : syracuseStep 520061 = 195023) (by norm_num)
theorem B388993 : Blo 342753 388993 := bbase (se 2 (by rfl) ⟨145872, by rfl⟩ : syracuseStep 388993 = 291745) (by norm_num)
theorem B651149 : Blo 342753 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B520085 : Blo 342753 520085 := bbase (se 6 (by rfl) ⟨12189, by rfl⟩ : syracuseStep 520085 = 24379) (by norm_num)
theorem B389029 : Blo 342753 389029 := bbase (se 4 (by rfl) ⟨36471, by rfl⟩ : syracuseStep 389029 = 72943) (by norm_num)
theorem B520109 : Blo 342753 520109 := bbase (se 3 (by rfl) ⟨97520, by rfl⟩ : syracuseStep 520109 = 195041) (by norm_num)
theorem B389065 : Blo 342753 389065 := bbase (se 2 (by rfl) ⟨145899, by rfl⟩ : syracuseStep 389065 = 291799) (by norm_num)
theorem B389101 : Blo 342753 389101 := bbase (se 3 (by rfl) ⟨72956, by rfl⟩ : syracuseStep 389101 = 145913) (by norm_num)
theorem B389137 : Blo 342753 389137 := bbase (se 2 (by rfl) ⟨145926, by rfl⟩ : syracuseStep 389137 = 291853) (by norm_num)
theorem B880661 : Blo 342753 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B389173 : Blo 342753 389173 := bbase (se 5 (by rfl) ⟨18242, by rfl⟩ : syracuseStep 389173 = 36485) (by norm_num)
theorem B389209 : Blo 342753 389209 := bbase (se 2 (by rfl) ⟨145953, by rfl⟩ : syracuseStep 389209 = 291907) (by norm_num)
theorem B389245 : Blo 342753 389245 := bbase (se 3 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 389245 = 145967) (by norm_num)
theorem B389281 : Blo 342753 389281 := bbase (se 2 (by rfl) ⟨145980, by rfl⟩ : syracuseStep 389281 = 291961) (by norm_num)
theorem B1896629 : Blo 342753 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B389317 : Blo 342753 389317 := bbase (se 4 (by rfl) ⟨36498, by rfl⟩ : syracuseStep 389317 = 72997) (by norm_num)
theorem B422101 : Blo 342753 422101 := bbase (se 7 (by rfl) ⟨4946, by rfl⟩ : syracuseStep 422101 = 9893) (by norm_num)
theorem B389353 : Blo 342753 389353 := bbase (se 2 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 389353 = 292015) (by norm_num)
theorem B389389 : Blo 342753 389389 := bbase (se 3 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 389389 = 146021) (by norm_num)
theorem B389425 : Blo 342753 389425 := bbase (se 2 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 389425 = 292069) (by norm_num)
theorem B979253 : Blo 342753 979253 := bbase (se 5 (by rfl) ⟨45902, by rfl⟩ : syracuseStep 979253 = 91805) (by norm_num)
theorem B553277 : Blo 342753 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B389461 : Blo 342753 389461 := bbase (se 10 (by rfl) ⟨570, by rfl⟩ : syracuseStep 389461 = 1141) (by norm_num)
theorem B389497 : Blo 342753 389497 := bbase (se 2 (by rfl) ⟨146061, by rfl⟩ : syracuseStep 389497 = 292123) (by norm_num)
theorem B389533 : Blo 342753 389533 := bbase (se 3 (by rfl) ⟨73037, by rfl⟩ : syracuseStep 389533 = 146075) (by norm_num)
theorem B389569 : Blo 342753 389569 := bbase (se 2 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 389569 = 292177) (by norm_num)
theorem B2093525 : Blo 342753 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B389605 : Blo 342753 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B389641 : Blo 342753 389641 := bbase (se 2 (by rfl) ⟨146115, by rfl⟩ : syracuseStep 389641 = 292231) (by norm_num)
theorem B389677 : Blo 342753 389677 := bbase (se 3 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 389677 = 146129) (by norm_num)
theorem B389713 : Blo 342753 389713 := bbase (se 2 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 389713 = 292285) (by norm_num)
theorem B389749 : Blo 342753 389749 := bbase (se 5 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 389749 = 36539) (by norm_num)
theorem B651901 : Blo 342753 651901 := bbase (se 3 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 651901 = 244463) (by norm_num)
theorem B389785 : Blo 342753 389785 := bbase (se 2 (by rfl) ⟨146169, by rfl⟩ : syracuseStep 389785 = 292339) (by norm_num)
theorem B389821 : Blo 342753 389821 := bbase (se 3 (by rfl) ⟨73091, by rfl⟩ : syracuseStep 389821 = 146183) (by norm_num)
theorem B7533269 : Blo 342753 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B389857 : Blo 342753 389857 := bbase (se 2 (by rfl) ⟨146196, by rfl⟩ : syracuseStep 389857 = 292393) (by norm_num)
theorem B979685 : Blo 342753 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B488197 : Blo 342753 488197 := bbase (se 4 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 488197 = 91537) (by norm_num)
theorem B553733 : Blo 342753 553733 := bbase (se 4 (by rfl) ⟨51912, by rfl⟩ : syracuseStep 553733 = 103825) (by norm_num)
theorem B389893 : Blo 342753 389893 := bbase (se 4 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 389893 = 73105) (by norm_num)
theorem B652045 : Blo 342753 652045 := bbase (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) (by norm_num)
theorem B1766165 : Blo 342753 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B389929 : Blo 342753 389929 := bbase (se 2 (by rfl) ⟨146223, by rfl⟩ : syracuseStep 389929 = 292447) (by norm_num)
theorem B1307461 : Blo 342753 1307461 := bbase (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) (by norm_num)
theorem B389965 : Blo 342753 389965 := bbase (se 3 (by rfl) ⟨73118, by rfl⟩ : syracuseStep 389965 = 146237) (by norm_num)
theorem B390001 : Blo 342753 390001 := bbase (se 2 (by rfl) ⟨146250, by rfl⟩ : syracuseStep 390001 = 292501) (by norm_num)
theorem B390037 : Blo 342753 390037 := bbase (se 6 (by rfl) ⟨9141, by rfl⟩ : syracuseStep 390037 = 18283) (by norm_num)
theorem B652205 : Blo 342753 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B390073 : Blo 342753 390073 := bbase (se 2 (by rfl) ⟨146277, by rfl⟩ : syracuseStep 390073 = 292555) (by norm_num)
theorem B619525 : Blo 342753 619525 := bbase (se 4 (by rfl) ⟨58080, by rfl⟩ : syracuseStep 619525 = 116161) (by norm_num)
theorem B1963061 : Blo 342753 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B652349 : Blo 342753 652349 := bbase (se 3 (by rfl) ⟨122315, by rfl⟩ : syracuseStep 652349 = 244631) (by norm_num)
theorem B488533 : Blo 342753 488533 := bbase (se 8 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 488533 = 5725) (by norm_num)
theorem B1307765 : Blo 342753 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B1045781 : Blo 342753 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B488749 : Blo 342753 488749 := bbase (se 3 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 488749 = 183281) (by norm_num)
theorem B652637 : Blo 342753 652637 := bbase (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) (by norm_num)
theorem B980437 : Blo 342753 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B652789 : Blo 342753 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B2979413 : Blo 342753 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B489125 : Blo 342753 489125 := bbase (se 4 (by rfl) ⟨45855, by rfl⟩ : syracuseStep 489125 = 91711) (by norm_num)
theorem B653093 : Blo 342753 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B555149 : Blo 342753 555149 := bbase (se 3 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 555149 = 208181) (by norm_num)
theorem B620765 : Blo 342753 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B1472741 : Blo 342753 1472741 := bbase (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) (by norm_num)
theorem B555373 : Blo 342753 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B784781 : Blo 342753 784781 := bbase (se 3 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 784781 = 294293) (by norm_num)
theorem B1997237 : Blo 342753 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B653845 : Blo 342753 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B588421 : Blo 342753 588421 := bbase (se 4 (by rfl) ⟨55164, by rfl⟩ : syracuseStep 588421 = 110329) (by norm_num)
theorem B653989 : Blo 342753 653989 := bbase (se 4 (by rfl) ⟨61311, by rfl⟩ : syracuseStep 653989 = 122623) (by norm_num)
theorem B391889 : Blo 342753 391889 := bbase (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) (by norm_num)
theorem B654149 : Blo 342753 654149 := bbase (se 4 (by rfl) ⟨61326, by rfl⟩ : syracuseStep 654149 = 122653) (by norm_num)
theorem B654293 : Blo 342753 654293 := bbase (se 7 (by rfl) ⟨7667, by rfl⟩ : syracuseStep 654293 = 15335) (by norm_num)
theorem B490549 : Blo 342753 490549 := bbase (se 5 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 490549 = 45989) (by norm_num)
theorem B1735829 : Blo 342753 1735829 := bbase (se 6 (by rfl) ⟨40683, by rfl⟩ : syracuseStep 1735829 = 81367) (by norm_num)
theorem B1309877 : Blo 342753 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B654581 : Blo 342753 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B392473 : Blo 342753 392473 := bbase (se 2 (by rfl) ⟨147177, by rfl⟩ : syracuseStep 392473 = 294355) (by norm_num)
theorem B654733 : Blo 342753 654733 := bbase (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) (by norm_num)
theorem B1310165 : Blo 342753 1310165 := bbase (se 7 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 1310165 = 30707) (by norm_num)
theorem B425489 : Blo 342753 425489 := bbase (se 2 (by rfl) ⟨159558, by rfl⟩ : syracuseStep 425489 = 319117) (by norm_num)
theorem B3309173 : Blo 342753 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B491141 : Blo 342753 491141 := bbase (se 4 (by rfl) ⟨46044, by rfl⟩ : syracuseStep 491141 = 92089) (by norm_num)
theorem B655037 : Blo 342753 655037 := bbase (se 3 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 655037 = 245639) (by norm_num)
theorem B491221 : Blo 342753 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B589565 : Blo 342753 589565 := bbase (se 3 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 589565 = 221087) (by norm_num)
theorem B491341 : Blo 342753 491341 := bbase (se 3 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 491341 = 184253) (by norm_num)
theorem B491437 : Blo 342753 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B1474517 : Blo 342753 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B983171 : Blo 342753 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B491665 : Blo 342753 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B655523 : Blo 342753 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B491779 : Blo 342753 491779 := bstep (se 1 (by rfl) ⟨368834, by rfl⟩ : syracuseStep 491779 = 737669) B737669
theorem B1966477 : Blo 342753 1966477 := bstep (se 3 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 1966477 = 737429) B737429
theorem B4194787 : Blo 342753 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B1475405 : Blo 342753 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B2786147 : Blo 342753 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1475441 : Blo 342753 1475441 := bstep (se 2 (by rfl) ⟨553290, by rfl⟩ : syracuseStep 1475441 = 1106581) B1106581
theorem B656419 : Blo 342753 656419 := bstep (se 1 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 656419 = 984629) B984629
theorem B4949045 : Blo 342753 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B1311821 : Blo 342753 1311821 := bstep (se 3 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 1311821 = 491933) B491933
theorem B525425 : Blo 342753 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B984241 : Blo 342753 984241 := bstep (se 2 (by rfl) ⟨369090, by rfl⟩ : syracuseStep 984241 = 738181) B738181
theorem B656579 : Blo 342753 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B1738097 : Blo 342753 1738097 := bstep (se 2 (by rfl) ⟨651786, by rfl⟩ : syracuseStep 1738097 = 1303573) B1303573
theorem B1181101 : Blo 342753 1181101 := bstep (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) B442913
theorem B1050097 : Blo 342753 1050097 := bstep (se 2 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 1050097 = 787573) B787573
theorem B525827 : Blo 342753 525827 := bstep (se 1 (by rfl) ⟨394370, by rfl⟩ : syracuseStep 525827 = 788741) B788741
theorem B493123 : Blo 342753 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B4392589 : Blo 342753 4392589 := bstep (se 3 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 4392589 = 1647221) B1647221
theorem B1869475 : Blo 342753 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B1312625 : Blo 342753 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B2951153 : Blo 342753 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B657649 : Blo 342753 657649 := bstep (se 2 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 657649 = 493237) B493237
theorem B1050947 : Blo 342753 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1968461 : Blo 342753 1968461 := bstep (se 3 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 1968461 = 738173) B738173
theorem B985517 : Blo 342753 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B592307 : Blo 342753 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B1313293 : Blo 342753 1313293 := bstep (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) B492485
theorem B985699 : Blo 342753 985699 := bstep (se 1 (by rfl) ⟨739274, by rfl⟩ : syracuseStep 985699 = 1478549) B1478549
theorem B985745 : Blo 342753 985745 := bstep (se 2 (by rfl) ⟨369654, by rfl⟩ : syracuseStep 985745 = 739309) B739309
theorem B1739555 : Blo 342753 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B4393925 : Blo 342753 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B756913 : Blo 342753 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B2198755 : Blo 342753 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B1969393 : Blo 342753 1969393 := bstep (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) B1477045
theorem B888049 : Blo 342753 888049 := bstep (se 2 (by rfl) ⟨333018, by rfl⟩ : syracuseStep 888049 = 666037) B666037
theorem B1576205 : Blo 342753 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B1314083 : Blo 342753 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B2788835 : Blo 342753 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B4197901 : Blo 342753 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B1740365 : Blo 342753 1740365 := bstep (se 3 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 1740365 = 652637) B652637
theorem B1314737 : Blo 342753 1314737 := bstep (se 2 (by rfl) ⟨493026, by rfl⟩ : syracuseStep 1314737 = 986053) B986053
theorem B987203 : Blo 342753 987203 := bstep (se 1 (by rfl) ⟨740402, by rfl⟩ : syracuseStep 987203 = 1480805) B1480805
theorem B2199757 : Blo 342753 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B561763 : Blo 342753 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 342753 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B1970851 : Blo 342753 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B463585 : Blo 342753 463585 := bstep (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) B347689
theorem B3707633 : Blo 342753 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B463969 : Blo 342753 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B1479779 : Blo 342753 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B1971377 : Blo 342753 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B2626829 : Blo 342753 2626829 := bstep (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) B985061
theorem B1316195 : Blo 342753 1316195 := bstep (se 1 (by rfl) ⟨987146, by rfl⟩ : syracuseStep 1316195 = 1974293) B1974293
theorem B595313 : Blo 342753 595313 := bstep (se 2 (by rfl) ⟨223242, by rfl⟩ : syracuseStep 595313 = 446485) B446485
theorem B1316209 : Blo 342753 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B562801 : Blo 342753 562801 := bstep (se 2 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 562801 = 422101) B422101
theorem B824995 : Blo 342753 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B1054403 : Blo 342753 1054403 := bstep (se 1 (by rfl) ⟨790802, by rfl⟩ : syracuseStep 1054403 = 1581605) B1581605
theorem B530275 : Blo 342753 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B1743281 : Blo 342753 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B367139 : Blo 342753 367139 := bstep (se 1 (by rfl) ⟨275354, by rfl⟩ : syracuseStep 367139 = 550709) B550709
theorem B1972835 : Blo 342753 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B826033 : Blo 342753 826033 := bstep (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) B619525
theorem B891587 : Blo 342753 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B466049 : Blo 342753 466049 := bstep (se 2 (by rfl) ⟨174768, by rfl⟩ : syracuseStep 466049 = 349537) B349537
theorem B1121539 : Blo 342753 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B630289 : Blo 342753 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B4398947 : Blo 342753 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B1744739 : Blo 342753 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B434099 : Blo 342753 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B598115 : Blo 342753 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B2629745 : Blo 342753 2629745 := bstep (se 2 (by rfl) ⟨986154, by rfl⟩ : syracuseStep 2629745 = 1972309) B1972309
theorem B3744053 : Blo 342753 3744053 := bstep (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) B351005
theorem B467299 : Blo 342753 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B1974725 : Blo 342753 1974725 := bstep (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) B370261
theorem B5022179 : Blo 342753 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B1122797 : Blo 342753 1122797 := bstep (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) B421049
theorem B664067 : Blo 342753 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B369155 : Blo 342753 369155 := bstep (se 1 (by rfl) ⟨276866, by rfl⟩ : syracuseStep 369155 = 553733) B553733
theorem B434803 : Blo 342753 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B4694669 : Blo 342753 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B1745549 : Blo 342753 1745549 := bstep (se 3 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 1745549 = 654581) B654581
theorem B434899 : Blo 342753 434899 := bstep (se 1 (by rfl) ⟨326174, by rfl⟩ : syracuseStep 434899 = 652349) B652349
theorem B697187 : Blo 342753 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B599057 : Blo 342753 599057 := bstep (se 2 (by rfl) ⟨224646, by rfl⟩ : syracuseStep 599057 = 449293) B449293
theorem B435395 : Blo 342753 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B468337 : Blo 342753 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B2368901 : Blo 342753 2368901 := bstep (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) B444169
theorem B370099 : Blo 342753 370099 := bstep (se 1 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 370099 = 555149) B555149
theorem B2991629 : Blo 342753 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B436099 : Blo 342753 436099 := bstep (se 1 (by rfl) ⟨327074, by rfl⟩ : syracuseStep 436099 = 654149) B654149
theorem B436195 : Blo 342753 436195 := bstep (se 1 (by rfl) ⟨327146, by rfl⟩ : syracuseStep 436195 = 654293) B654293
theorem B1157165 : Blo 342753 1157165 := bstep (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) B433937
theorem B1157219 : Blo 342753 1157219 := bstep (se 1 (by rfl) ⟨867914, by rfl⟩ : syracuseStep 1157219 = 1735829) B1735829
theorem B1091917 : Blo 342753 1091917 := bstep (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) B409469
theorem B1157489 : Blo 342753 1157489 := bstep (se 2 (by rfl) ⟨434058, by rfl⟩ : syracuseStep 1157489 = 868117) B868117
theorem B2206115 : Blo 342753 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B436691 : Blo 342753 436691 := bstep (se 1 (by rfl) ⟨327518, by rfl⟩ : syracuseStep 436691 = 655037) B655037
theorem B928465 : Blo 342753 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B830321 : Blo 342753 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B830339 : Blo 342753 830339 := bstep (se 1 (by rfl) ⟨622754, by rfl⟩ : syracuseStep 830339 = 1245509) B1245509
theorem B1158029 : Blo 342753 1158029 := bstep (se 3 (by rfl) ⟨217130, by rfl⟩ : syracuseStep 1158029 = 434261) B434261
theorem B1158083 : Blo 342753 1158083 := bstep (se 1 (by rfl) ⟨868562, by rfl⟩ : syracuseStep 1158083 = 1737125) B1737125
theorem B3550321 : Blo 342753 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B5057677 : Blo 342753 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B437395 : Blo 342753 437395 := bstep (se 1 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 437395 = 656093) B656093
theorem B1158353 : Blo 342753 1158353 := bstep (se 2 (by rfl) ⟨434382, by rfl⟩ : syracuseStep 1158353 = 868765) B868765
theorem B437491 : Blo 342753 437491 := bstep (se 1 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 437491 = 656237) B656237
theorem B732611 : Blo 342753 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B1748465 : Blo 342753 1748465 := bstep (se 2 (by rfl) ⟨655674, by rfl⟩ : syracuseStep 1748465 = 1311349) B1311349
theorem B2665997 : Blo 342753 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B437987 : Blo 342753 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B1158893 : Blo 342753 1158893 := bstep (se 3 (by rfl) ⟨217292, by rfl⟩ : syracuseStep 1158893 = 434585) B434585
theorem B1158947 : Blo 342753 1158947 := bstep (se 1 (by rfl) ⟨869210, by rfl⟩ : syracuseStep 1158947 = 1738421) B1738421
theorem B929677 : Blo 342753 929677 := bstep (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) B348629
theorem B831377 : Blo 342753 831377 := bstep (se 2 (by rfl) ⟨311766, by rfl⟩ : syracuseStep 831377 = 623533) B623533
theorem B1159217 : Blo 342753 1159217 := bstep (se 2 (by rfl) ⟨434706, by rfl⟩ : syracuseStep 1159217 = 869413) B869413
theorem B1290289 : Blo 342753 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B438691 : Blo 342753 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B438787 : Blo 342753 438787 := bstep (se 1 (by rfl) ⟨329090, by rfl⟩ : syracuseStep 438787 = 658181) B658181
theorem B1159757 : Blo 342753 1159757 := bstep (se 3 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 1159757 = 434909) B434909
theorem B995917 : Blo 342753 995917 := bstep (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) B373469
theorem B1159811 : Blo 342753 1159811 := bstep (se 1 (by rfl) ⟨869858, by rfl⟩ : syracuseStep 1159811 = 1739717) B1739717
theorem B504625 : Blo 342753 504625 := bstep (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) B378469
theorem B1160081 : Blo 342753 1160081 := bstep (se 2 (by rfl) ⟨435030, by rfl⟩ : syracuseStep 1160081 = 870061) B870061
theorem B1749923 : Blo 342753 1749923 := bstep (se 1 (by rfl) ⟨1312442, by rfl⟩ : syracuseStep 1749923 = 2624885) B2624885
theorem B931139 : Blo 342753 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B2930033 : Blo 342753 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B734627 : Blo 342753 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B1160621 : Blo 342753 1160621 := bstep (se 3 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 1160621 = 435233) B435233
theorem B1160675 : Blo 342753 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B2209265 : Blo 342753 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B2209315 : Blo 342753 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1750733 : Blo 342753 1750733 := bstep (se 3 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 1750733 = 656525) B656525
theorem B931537 : Blo 342753 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B1160945 : Blo 342753 1160945 := bstep (se 2 (by rfl) ⟨435354, by rfl⟩ : syracuseStep 1160945 = 870709) B870709
theorem B702577 : Blo 342753 702577 := bstep (se 2 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 702577 = 526933) B526933
theorem B1161485 : Blo 342753 1161485 := bstep (se 3 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 1161485 = 435557) B435557
theorem B3946805 : Blo 342753 3946805 := bstep (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) B370013
theorem B1161539 : Blo 342753 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B1325425 : Blo 342753 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932273 : Blo 342753 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B473603 : Blo 342753 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B473635 : Blo 342753 473635 := bstep (se 1 (by rfl) ⟨355226, by rfl⟩ : syracuseStep 473635 = 710453) B710453
theorem B1161809 : Blo 342753 1161809 := bstep (se 2 (by rfl) ⟨435678, by rfl⟩ : syracuseStep 1161809 = 871357) B871357
theorem B735875 : Blo 342753 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B342755 : Blo 342753 342755 := bstep (se 1 (by rfl) ⟨257066, by rfl⟩ : syracuseStep 342755 = 514133) B514133
theorem B342771 : Blo 342753 342771 := bstep (se 1 (by rfl) ⟨257078, by rfl⟩ : syracuseStep 342771 = 514157) B514157
theorem B342787 : Blo 342753 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B342803 : Blo 342753 342803 := bstep (se 1 (by rfl) ⟨257102, by rfl⟩ : syracuseStep 342803 = 514205) B514205
theorem B342819 : Blo 342753 342819 := bstep (se 1 (by rfl) ⟨257114, by rfl⟩ : syracuseStep 342819 = 514229) B514229
theorem B342835 : Blo 342753 342835 := bstep (se 1 (by rfl) ⟨257126, by rfl⟩ : syracuseStep 342835 = 514253) B514253
theorem B342851 : Blo 342753 342851 := bstep (se 1 (by rfl) ⟨257138, by rfl⟩ : syracuseStep 342851 = 514277) B514277
theorem B342867 : Blo 342753 342867 := bstep (se 1 (by rfl) ⟨257150, by rfl⟩ : syracuseStep 342867 = 514301) B514301
theorem B342883 : Blo 342753 342883 := bstep (se 1 (by rfl) ⟨257162, by rfl⟩ : syracuseStep 342883 = 514325) B514325
theorem B342899 : Blo 342753 342899 := bstep (se 1 (by rfl) ⟨257174, by rfl⟩ : syracuseStep 342899 = 514349) B514349
theorem B342915 : Blo 342753 342915 := bstep (se 1 (by rfl) ⟨257186, by rfl⟩ : syracuseStep 342915 = 514373) B514373
theorem B342931 : Blo 342753 342931 := bstep (se 1 (by rfl) ⟨257198, by rfl⟩ : syracuseStep 342931 = 514397) B514397
theorem B342947 : Blo 342753 342947 := bstep (se 1 (by rfl) ⟨257210, by rfl⟩ : syracuseStep 342947 = 514421) B514421
theorem B342963 : Blo 342753 342963 := bstep (se 1 (by rfl) ⟨257222, by rfl⟩ : syracuseStep 342963 = 514445) B514445
theorem B342979 : Blo 342753 342979 := bstep (se 1 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 342979 = 514469) B514469
theorem B342995 : Blo 342753 342995 := bstep (se 1 (by rfl) ⟨257246, by rfl⟩ : syracuseStep 342995 = 514493) B514493
theorem B343011 : Blo 342753 343011 := bstep (se 1 (by rfl) ⟨257258, by rfl⟩ : syracuseStep 343011 = 514517) B514517
theorem B343027 : Blo 342753 343027 := bstep (se 1 (by rfl) ⟨257270, by rfl⟩ : syracuseStep 343027 = 514541) B514541
theorem B343043 : Blo 342753 343043 := bstep (se 1 (by rfl) ⟨257282, by rfl⟩ : syracuseStep 343043 = 514565) B514565
theorem B343059 : Blo 342753 343059 := bstep (se 1 (by rfl) ⟨257294, by rfl⟩ : syracuseStep 343059 = 514589) B514589
theorem B343075 : Blo 342753 343075 := bstep (se 1 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 343075 = 514613) B514613
theorem B441379 : Blo 342753 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B343091 : Blo 342753 343091 := bstep (se 1 (by rfl) ⟨257318, by rfl⟩ : syracuseStep 343091 = 514637) B514637
theorem B343107 : Blo 342753 343107 := bstep (se 1 (by rfl) ⟨257330, by rfl⟩ : syracuseStep 343107 = 514661) B514661
theorem B343123 : Blo 342753 343123 := bstep (se 1 (by rfl) ⟨257342, by rfl⟩ : syracuseStep 343123 = 514685) B514685
theorem B343139 : Blo 342753 343139 := bstep (se 1 (by rfl) ⟨257354, by rfl⟩ : syracuseStep 343139 = 514709) B514709
theorem B1162349 : Blo 342753 1162349 := bstep (se 3 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 1162349 = 435881) B435881
theorem B343155 : Blo 342753 343155 := bstep (se 1 (by rfl) ⟨257366, by rfl⟩ : syracuseStep 343155 = 514733) B514733
theorem B343171 : Blo 342753 343171 := bstep (se 1 (by rfl) ⟨257378, by rfl⟩ : syracuseStep 343171 = 514757) B514757
theorem B343187 : Blo 342753 343187 := bstep (se 1 (by rfl) ⟨257390, by rfl⟩ : syracuseStep 343187 = 514781) B514781
theorem B343203 : Blo 342753 343203 := bstep (se 1 (by rfl) ⟨257402, by rfl⟩ : syracuseStep 343203 = 514805) B514805
theorem B1162403 : Blo 342753 1162403 := bstep (se 1 (by rfl) ⟨871802, by rfl⟩ : syracuseStep 1162403 = 1743605) B1743605
theorem B933041 : Blo 342753 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B343219 : Blo 342753 343219 := bstep (se 1 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 343219 = 514829) B514829
theorem B343235 : Blo 342753 343235 := bstep (se 1 (by rfl) ⟨257426, by rfl⟩ : syracuseStep 343235 = 514853) B514853
theorem B736465 : Blo 342753 736465 := bstep (se 2 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 736465 = 552349) B552349
theorem B343251 : Blo 342753 343251 := bstep (se 1 (by rfl) ⟨257438, by rfl⟩ : syracuseStep 343251 = 514877) B514877
theorem B343267 : Blo 342753 343267 := bstep (se 1 (by rfl) ⟨257450, by rfl⟩ : syracuseStep 343267 = 514901) B514901
theorem B343283 : Blo 342753 343283 := bstep (se 1 (by rfl) ⟨257462, by rfl⟩ : syracuseStep 343283 = 514925) B514925
theorem B343299 : Blo 342753 343299 := bstep (se 1 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 343299 = 514949) B514949
theorem B933137 : Blo 342753 933137 := bstep (se 2 (by rfl) ⟨349926, by rfl⟩ : syracuseStep 933137 = 699853) B699853
theorem B343315 : Blo 342753 343315 := bstep (se 1 (by rfl) ⟨257486, by rfl⟩ : syracuseStep 343315 = 514973) B514973
theorem B343331 : Blo 342753 343331 := bstep (se 1 (by rfl) ⟨257498, by rfl⟩ : syracuseStep 343331 = 514997) B514997
theorem B343347 : Blo 342753 343347 := bstep (se 1 (by rfl) ⟨257510, by rfl⟩ : syracuseStep 343347 = 515021) B515021
theorem B343363 : Blo 342753 343363 := bstep (se 1 (by rfl) ⟨257522, by rfl⟩ : syracuseStep 343363 = 515045) B515045
theorem B343379 : Blo 342753 343379 := bstep (se 1 (by rfl) ⟨257534, by rfl⟩ : syracuseStep 343379 = 515069) B515069
theorem B343395 : Blo 342753 343395 := bstep (se 1 (by rfl) ⟨257546, by rfl⟩ : syracuseStep 343395 = 515093) B515093
theorem B343411 : Blo 342753 343411 := bstep (se 1 (by rfl) ⟨257558, by rfl⟩ : syracuseStep 343411 = 515117) B515117
theorem B343427 : Blo 342753 343427 := bstep (se 1 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 343427 = 515141) B515141
theorem B343443 : Blo 342753 343443 := bstep (se 1 (by rfl) ⟨257582, by rfl⟩ : syracuseStep 343443 = 515165) B515165
theorem B343459 : Blo 342753 343459 := bstep (se 1 (by rfl) ⟨257594, by rfl⟩ : syracuseStep 343459 = 515189) B515189
theorem B1162673 : Blo 342753 1162673 := bstep (se 2 (by rfl) ⟨436002, by rfl⟩ : syracuseStep 1162673 = 872005) B872005
theorem B343475 : Blo 342753 343475 := bstep (se 1 (by rfl) ⟨257606, by rfl⟩ : syracuseStep 343475 = 515213) B515213
theorem B343491 : Blo 342753 343491 := bstep (se 1 (by rfl) ⟨257618, by rfl⟩ : syracuseStep 343491 = 515237) B515237
theorem B867793 : Blo 342753 867793 := bstep (se 2 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 867793 = 650845) B650845
theorem B343507 : Blo 342753 343507 := bstep (se 1 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 343507 = 515261) B515261
theorem B343523 : Blo 342753 343523 := bstep (se 1 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 343523 = 515285) B515285
theorem B343539 : Blo 342753 343539 := bstep (se 1 (by rfl) ⟨257654, by rfl⟩ : syracuseStep 343539 = 515309) B515309
theorem B343555 : Blo 342753 343555 := bstep (se 1 (by rfl) ⟨257666, by rfl⟩ : syracuseStep 343555 = 515333) B515333
theorem B343571 : Blo 342753 343571 := bstep (se 1 (by rfl) ⟨257678, by rfl⟩ : syracuseStep 343571 = 515357) B515357
theorem B343587 : Blo 342753 343587 := bstep (se 1 (by rfl) ⟨257690, by rfl⟩ : syracuseStep 343587 = 515381) B515381
theorem B343603 : Blo 342753 343603 := bstep (se 1 (by rfl) ⟨257702, by rfl⟩ : syracuseStep 343603 = 515405) B515405
theorem B343619 : Blo 342753 343619 := bstep (se 1 (by rfl) ⟨257714, by rfl⟩ : syracuseStep 343619 = 515429) B515429
theorem B343635 : Blo 342753 343635 := bstep (se 1 (by rfl) ⟨257726, by rfl⟩ : syracuseStep 343635 = 515453) B515453
theorem B343651 : Blo 342753 343651 := bstep (se 1 (by rfl) ⟨257738, by rfl⟩ : syracuseStep 343651 = 515477) B515477
theorem B343667 : Blo 342753 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B343683 : Blo 342753 343683 := bstep (se 1 (by rfl) ⟨257762, by rfl⟩ : syracuseStep 343683 = 515525) B515525
theorem B343699 : Blo 342753 343699 := bstep (se 1 (by rfl) ⟨257774, by rfl⟩ : syracuseStep 343699 = 515549) B515549
theorem B343715 : Blo 342753 343715 := bstep (se 1 (by rfl) ⟨257786, by rfl⟩ : syracuseStep 343715 = 515573) B515573
theorem B343731 : Blo 342753 343731 := bstep (se 1 (by rfl) ⟨257798, by rfl⟩ : syracuseStep 343731 = 515597) B515597
theorem B343747 : Blo 342753 343747 := bstep (se 1 (by rfl) ⟨257810, by rfl⟩ : syracuseStep 343747 = 515621) B515621
theorem B343763 : Blo 342753 343763 := bstep (se 1 (by rfl) ⟨257822, by rfl⟩ : syracuseStep 343763 = 515645) B515645
theorem B868067 : Blo 342753 868067 := bstep (se 1 (by rfl) ⟨651050, by rfl⟩ : syracuseStep 868067 = 1302101) B1302101
theorem B343779 : Blo 342753 343779 := bstep (se 1 (by rfl) ⟨257834, by rfl⟩ : syracuseStep 343779 = 515669) B515669
theorem B343795 : Blo 342753 343795 := bstep (se 1 (by rfl) ⟨257846, by rfl⟩ : syracuseStep 343795 = 515693) B515693
theorem B343811 : Blo 342753 343811 := bstep (se 1 (by rfl) ⟨257858, by rfl⟩ : syracuseStep 343811 = 515717) B515717
theorem B343827 : Blo 342753 343827 := bstep (se 1 (by rfl) ⟨257870, by rfl⟩ : syracuseStep 343827 = 515741) B515741
theorem B343843 : Blo 342753 343843 := bstep (se 1 (by rfl) ⟨257882, by rfl⟩ : syracuseStep 343843 = 515765) B515765
theorem B343859 : Blo 342753 343859 := bstep (se 1 (by rfl) ⟨257894, by rfl⟩ : syracuseStep 343859 = 515789) B515789
theorem B343875 : Blo 342753 343875 := bstep (se 1 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 343875 = 515813) B515813
theorem B343891 : Blo 342753 343891 := bstep (se 1 (by rfl) ⟨257918, by rfl⟩ : syracuseStep 343891 = 515837) B515837
theorem B343907 : Blo 342753 343907 := bstep (se 1 (by rfl) ⟨257930, by rfl⟩ : syracuseStep 343907 = 515861) B515861
theorem B343923 : Blo 342753 343923 := bstep (se 1 (by rfl) ⟨257942, by rfl⟩ : syracuseStep 343923 = 515885) B515885
theorem B343939 : Blo 342753 343939 := bstep (se 1 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 343939 = 515909) B515909
theorem B2211725 : Blo 342753 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B343955 : Blo 342753 343955 := bstep (se 1 (by rfl) ⟨257966, by rfl⟩ : syracuseStep 343955 = 515933) B515933
theorem B868259 : Blo 342753 868259 := bstep (se 1 (by rfl) ⟨651194, by rfl⟩ : syracuseStep 868259 = 1302389) B1302389
theorem B343971 : Blo 342753 343971 := bstep (se 1 (by rfl) ⟨257978, by rfl⟩ : syracuseStep 343971 = 515957) B515957
theorem B343987 : Blo 342753 343987 := bstep (se 1 (by rfl) ⟨257990, by rfl⟩ : syracuseStep 343987 = 515981) B515981
theorem B344003 : Blo 342753 344003 := bstep (se 1 (by rfl) ⟨258002, by rfl⟩ : syracuseStep 344003 = 516005) B516005
theorem B1163213 : Blo 342753 1163213 := bstep (se 3 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 1163213 = 436205) B436205
theorem B344019 : Blo 342753 344019 := bstep (se 1 (by rfl) ⟨258014, by rfl⟩ : syracuseStep 344019 = 516029) B516029
theorem B573409 : Blo 342753 573409 := bstep (se 2 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 573409 = 430057) B430057
theorem B344035 : Blo 342753 344035 := bstep (se 1 (by rfl) ⟨258026, by rfl⟩ : syracuseStep 344035 = 516053) B516053
theorem B344051 : Blo 342753 344051 := bstep (se 1 (by rfl) ⟨258038, by rfl⟩ : syracuseStep 344051 = 516077) B516077
theorem B344067 : Blo 342753 344067 := bstep (se 1 (by rfl) ⟨258050, by rfl⟩ : syracuseStep 344067 = 516101) B516101
theorem B1163267 : Blo 342753 1163267 := bstep (se 1 (by rfl) ⟨872450, by rfl⟩ : syracuseStep 1163267 = 1744901) B1744901
theorem B344083 : Blo 342753 344083 := bstep (se 1 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 344083 = 516125) B516125
theorem B344099 : Blo 342753 344099 := bstep (se 1 (by rfl) ⟨258074, by rfl⟩ : syracuseStep 344099 = 516149) B516149
theorem B344115 : Blo 342753 344115 := bstep (se 1 (by rfl) ⟨258086, by rfl⟩ : syracuseStep 344115 = 516173) B516173
theorem B344131 : Blo 342753 344131 := bstep (se 1 (by rfl) ⟨258098, by rfl⟩ : syracuseStep 344131 = 516197) B516197
theorem B344147 : Blo 342753 344147 := bstep (se 1 (by rfl) ⟨258110, by rfl⟩ : syracuseStep 344147 = 516221) B516221
theorem B344163 : Blo 342753 344163 := bstep (se 1 (by rfl) ⟨258122, by rfl⟩ : syracuseStep 344163 = 516245) B516245
theorem B344179 : Blo 342753 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B344195 : Blo 342753 344195 := bstep (se 1 (by rfl) ⟨258146, by rfl⟩ : syracuseStep 344195 = 516293) B516293
theorem B344211 : Blo 342753 344211 := bstep (se 1 (by rfl) ⟨258158, by rfl⟩ : syracuseStep 344211 = 516317) B516317
theorem B344227 : Blo 342753 344227 := bstep (se 1 (by rfl) ⟨258170, by rfl⟩ : syracuseStep 344227 = 516341) B516341
theorem B344243 : Blo 342753 344243 := bstep (se 1 (by rfl) ⟨258182, by rfl⟩ : syracuseStep 344243 = 516365) B516365
theorem B4538549 : Blo 342753 4538549 := bstep (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) B425489
theorem B344259 : Blo 342753 344259 := bstep (se 1 (by rfl) ⟨258194, by rfl⟩ : syracuseStep 344259 = 516389) B516389
theorem B344275 : Blo 342753 344275 := bstep (se 1 (by rfl) ⟨258206, by rfl⟩ : syracuseStep 344275 = 516413) B516413
theorem B344291 : Blo 342753 344291 := bstep (se 1 (by rfl) ⟨258218, by rfl⟩ : syracuseStep 344291 = 516437) B516437
theorem B344307 : Blo 342753 344307 := bstep (se 1 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 344307 = 516461) B516461
theorem B344323 : Blo 342753 344323 := bstep (se 1 (by rfl) ⟨258242, by rfl⟩ : syracuseStep 344323 = 516485) B516485
theorem B1163537 : Blo 342753 1163537 := bstep (se 2 (by rfl) ⟨436326, by rfl⟩ : syracuseStep 1163537 = 872653) B872653
theorem B344339 : Blo 342753 344339 := bstep (se 1 (by rfl) ⟨258254, by rfl⟩ : syracuseStep 344339 = 516509) B516509
theorem B344355 : Blo 342753 344355 := bstep (se 1 (by rfl) ⟨258266, by rfl⟩ : syracuseStep 344355 = 516533) B516533
theorem B344371 : Blo 342753 344371 := bstep (se 1 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 344371 = 516557) B516557
theorem B344387 : Blo 342753 344387 := bstep (se 1 (by rfl) ⟨258290, by rfl⟩ : syracuseStep 344387 = 516581) B516581
theorem B344403 : Blo 342753 344403 := bstep (se 1 (by rfl) ⟨258302, by rfl⟩ : syracuseStep 344403 = 516605) B516605
theorem B344419 : Blo 342753 344419 := bstep (se 1 (by rfl) ⟨258314, by rfl⟩ : syracuseStep 344419 = 516629) B516629
theorem B344435 : Blo 342753 344435 := bstep (se 1 (by rfl) ⟨258326, by rfl⟩ : syracuseStep 344435 = 516653) B516653
theorem B344451 : Blo 342753 344451 := bstep (se 1 (by rfl) ⟨258338, by rfl⟩ : syracuseStep 344451 = 516677) B516677
theorem B672131 : Blo 342753 672131 := bstep (se 1 (by rfl) ⟨504098, by rfl⟩ : syracuseStep 672131 = 1008197) B1008197
theorem B344467 : Blo 342753 344467 := bstep (se 1 (by rfl) ⟨258350, by rfl⟩ : syracuseStep 344467 = 516701) B516701
theorem B344483 : Blo 342753 344483 := bstep (se 1 (by rfl) ⟨258362, by rfl⟩ : syracuseStep 344483 = 516725) B516725
theorem B344499 : Blo 342753 344499 := bstep (se 1 (by rfl) ⟨258374, by rfl⟩ : syracuseStep 344499 = 516749) B516749
theorem B344515 : Blo 342753 344515 := bstep (se 1 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 344515 = 516773) B516773
theorem B344531 : Blo 342753 344531 := bstep (se 1 (by rfl) ⟨258398, by rfl⟩ : syracuseStep 344531 = 516797) B516797
theorem B344547 : Blo 342753 344547 := bstep (se 1 (by rfl) ⟨258410, by rfl⟩ : syracuseStep 344547 = 516821) B516821
theorem B344563 : Blo 342753 344563 := bstep (se 1 (by rfl) ⟨258422, by rfl⟩ : syracuseStep 344563 = 516845) B516845
theorem B344579 : Blo 342753 344579 := bstep (se 1 (by rfl) ⟨258434, by rfl⟩ : syracuseStep 344579 = 516869) B516869
theorem B344595 : Blo 342753 344595 := bstep (se 1 (by rfl) ⟨258446, by rfl⟩ : syracuseStep 344595 = 516893) B516893
theorem B344611 : Blo 342753 344611 := bstep (se 1 (by rfl) ⟨258458, by rfl⟩ : syracuseStep 344611 = 516917) B516917
theorem B1753649 : Blo 342753 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B344627 : Blo 342753 344627 := bstep (se 1 (by rfl) ⟨258470, by rfl⟩ : syracuseStep 344627 = 516941) B516941
theorem B344643 : Blo 342753 344643 := bstep (se 1 (by rfl) ⟨258482, by rfl⟩ : syracuseStep 344643 = 516965) B516965
theorem B344659 : Blo 342753 344659 := bstep (se 1 (by rfl) ⟨258494, by rfl⟩ : syracuseStep 344659 = 516989) B516989
theorem B344675 : Blo 342753 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B1098353 : Blo 342753 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B344691 : Blo 342753 344691 := bstep (se 1 (by rfl) ⟨258518, by rfl⟩ : syracuseStep 344691 = 517037) B517037
theorem B344707 : Blo 342753 344707 := bstep (se 1 (by rfl) ⟨258530, by rfl⟩ : syracuseStep 344707 = 517061) B517061
theorem B344723 : Blo 342753 344723 := bstep (se 1 (by rfl) ⟨258542, by rfl⟩ : syracuseStep 344723 = 517085) B517085
theorem B344739 : Blo 342753 344739 := bstep (se 1 (by rfl) ⟨258554, by rfl⟩ : syracuseStep 344739 = 517109) B517109
theorem B344755 : Blo 342753 344755 := bstep (se 1 (by rfl) ⟨258566, by rfl⟩ : syracuseStep 344755 = 517133) B517133
theorem B344771 : Blo 342753 344771 := bstep (se 1 (by rfl) ⟨258578, by rfl⟩ : syracuseStep 344771 = 517157) B517157
theorem B344787 : Blo 342753 344787 := bstep (se 1 (by rfl) ⟨258590, by rfl⟩ : syracuseStep 344787 = 517181) B517181
theorem B344803 : Blo 342753 344803 := bstep (se 1 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 344803 = 517205) B517205
theorem B344819 : Blo 342753 344819 := bstep (se 1 (by rfl) ⟨258614, by rfl⟩ : syracuseStep 344819 = 517229) B517229
theorem B344835 : Blo 342753 344835 := bstep (se 1 (by rfl) ⟨258626, by rfl⟩ : syracuseStep 344835 = 517253) B517253
theorem B344851 : Blo 342753 344851 := bstep (se 1 (by rfl) ⟨258638, by rfl⟩ : syracuseStep 344851 = 517277) B517277
theorem B344867 : Blo 342753 344867 := bstep (se 1 (by rfl) ⟨258650, by rfl⟩ : syracuseStep 344867 = 517301) B517301
theorem B1164077 : Blo 342753 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B344883 : Blo 342753 344883 := bstep (se 1 (by rfl) ⟨258662, by rfl⟩ : syracuseStep 344883 = 517325) B517325
theorem B344899 : Blo 342753 344899 := bstep (se 1 (by rfl) ⟨258674, by rfl⟩ : syracuseStep 344899 = 517349) B517349
theorem B1000259 : Blo 342753 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B869201 : Blo 342753 869201 := bstep (se 2 (by rfl) ⟨325950, by rfl⟩ : syracuseStep 869201 = 651901) B651901
theorem B344915 : Blo 342753 344915 := bstep (se 1 (by rfl) ⟨258686, by rfl⟩ : syracuseStep 344915 = 517373) B517373
theorem B1164131 : Blo 342753 1164131 := bstep (se 1 (by rfl) ⟨873098, by rfl⟩ : syracuseStep 1164131 = 1746197) B1746197
theorem B344931 : Blo 342753 344931 := bstep (se 1 (by rfl) ⟨258698, by rfl⟩ : syracuseStep 344931 = 517397) B517397
theorem B344947 : Blo 342753 344947 := bstep (se 1 (by rfl) ⟨258710, by rfl⟩ : syracuseStep 344947 = 517421) B517421
theorem B869251 : Blo 342753 869251 := bstep (se 1 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 869251 = 1303877) B1303877
theorem B344963 : Blo 342753 344963 := bstep (se 1 (by rfl) ⟨258722, by rfl⟩ : syracuseStep 344963 = 517445) B517445
theorem B344979 : Blo 342753 344979 := bstep (se 1 (by rfl) ⟨258734, by rfl⟩ : syracuseStep 344979 = 517469) B517469
theorem B344995 : Blo 342753 344995 := bstep (se 1 (by rfl) ⟨258746, by rfl⟩ : syracuseStep 344995 = 517493) B517493
theorem B345011 : Blo 342753 345011 := bstep (se 1 (by rfl) ⟨258758, by rfl⟩ : syracuseStep 345011 = 517517) B517517
theorem B345027 : Blo 342753 345027 := bstep (se 1 (by rfl) ⟨258770, by rfl⟩ : syracuseStep 345027 = 517541) B517541
theorem B345043 : Blo 342753 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B345059 : Blo 342753 345059 := bstep (se 1 (by rfl) ⟨258794, by rfl⟩ : syracuseStep 345059 = 517589) B517589
theorem B345075 : Blo 342753 345075 := bstep (se 1 (by rfl) ⟨258806, by rfl⟩ : syracuseStep 345075 = 517613) B517613
theorem B345091 : Blo 342753 345091 := bstep (se 1 (by rfl) ⟨258818, by rfl⟩ : syracuseStep 345091 = 517637) B517637
theorem B869393 : Blo 342753 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B345107 : Blo 342753 345107 := bstep (se 1 (by rfl) ⟨258830, by rfl⟩ : syracuseStep 345107 = 517661) B517661
theorem B345123 : Blo 342753 345123 := bstep (se 1 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 345123 = 517685) B517685
theorem B345139 : Blo 342753 345139 := bstep (se 1 (by rfl) ⟨258854, by rfl⟩ : syracuseStep 345139 = 517709) B517709
theorem B345155 : Blo 342753 345155 := bstep (se 1 (by rfl) ⟨258866, by rfl⟩ : syracuseStep 345155 = 517733) B517733
theorem B345171 : Blo 342753 345171 := bstep (se 1 (by rfl) ⟨258878, by rfl⟩ : syracuseStep 345171 = 517757) B517757
theorem B345187 : Blo 342753 345187 := bstep (se 1 (by rfl) ⟨258890, by rfl⟩ : syracuseStep 345187 = 517781) B517781
theorem B1164401 : Blo 342753 1164401 := bstep (se 2 (by rfl) ⟨436650, by rfl⟩ : syracuseStep 1164401 = 873301) B873301
theorem B345203 : Blo 342753 345203 := bstep (se 1 (by rfl) ⟨258902, by rfl⟩ : syracuseStep 345203 = 517805) B517805
theorem B345219 : Blo 342753 345219 := bstep (se 1 (by rfl) ⟨258914, by rfl⟩ : syracuseStep 345219 = 517829) B517829
theorem B345235 : Blo 342753 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B345251 : Blo 342753 345251 := bstep (se 1 (by rfl) ⟨258938, by rfl⟩ : syracuseStep 345251 = 517877) B517877
theorem B345267 : Blo 342753 345267 := bstep (se 1 (by rfl) ⟨258950, by rfl⟩ : syracuseStep 345267 = 517901) B517901
theorem B345283 : Blo 342753 345283 := bstep (se 1 (by rfl) ⟨258962, by rfl⟩ : syracuseStep 345283 = 517925) B517925
theorem B771281 : Blo 342753 771281 := bstep (se 2 (by rfl) ⟨289230, by rfl⟩ : syracuseStep 771281 = 578461) B578461
theorem B345299 : Blo 342753 345299 := bstep (se 1 (by rfl) ⟨258974, by rfl⟩ : syracuseStep 345299 = 517949) B517949
theorem B27280597 : Blo 342753 27280597 := bstep (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) B639389
theorem B771299 : Blo 342753 771299 := bstep (se 1 (by rfl) ⟨578474, by rfl⟩ : syracuseStep 771299 = 1156949) B1156949
theorem B345315 : Blo 342753 345315 := bstep (se 1 (by rfl) ⟨258986, by rfl⟩ : syracuseStep 345315 = 517973) B517973
theorem B345331 : Blo 342753 345331 := bstep (se 1 (by rfl) ⟨258998, by rfl⟩ : syracuseStep 345331 = 517997) B517997
theorem B345347 : Blo 342753 345347 := bstep (se 1 (by rfl) ⟨259010, by rfl⟩ : syracuseStep 345347 = 518021) B518021
theorem B935171 : Blo 342753 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B345363 : Blo 342753 345363 := bstep (se 1 (by rfl) ⟨259022, by rfl⟩ : syracuseStep 345363 = 518045) B518045
theorem B345379 : Blo 342753 345379 := bstep (se 1 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 345379 = 518069) B518069
theorem B345395 : Blo 342753 345395 := bstep (se 1 (by rfl) ⟨259046, by rfl⟩ : syracuseStep 345395 = 518093) B518093
theorem B345411 : Blo 342753 345411 := bstep (se 1 (by rfl) ⟨259058, by rfl⟩ : syracuseStep 345411 = 518117) B518117
theorem B345427 : Blo 342753 345427 := bstep (se 1 (by rfl) ⟨259070, by rfl⟩ : syracuseStep 345427 = 518141) B518141
theorem B345443 : Blo 342753 345443 := bstep (se 1 (by rfl) ⟨259082, by rfl⟩ : syracuseStep 345443 = 518165) B518165
theorem B345459 : Blo 342753 345459 := bstep (se 1 (by rfl) ⟨259094, by rfl⟩ : syracuseStep 345459 = 518189) B518189
theorem B345475 : Blo 342753 345475 := bstep (se 1 (by rfl) ⟨259106, by rfl⟩ : syracuseStep 345475 = 518213) B518213
theorem B345491 : Blo 342753 345491 := bstep (se 1 (by rfl) ⟨259118, by rfl⟩ : syracuseStep 345491 = 518237) B518237
theorem B345507 : Blo 342753 345507 := bstep (se 1 (by rfl) ⟨259130, by rfl⟩ : syracuseStep 345507 = 518261) B518261
theorem B345523 : Blo 342753 345523 := bstep (se 1 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 345523 = 518285) B518285
theorem B345539 : Blo 342753 345539 := bstep (se 1 (by rfl) ⟨259154, by rfl⟩ : syracuseStep 345539 = 518309) B518309
theorem B345555 : Blo 342753 345555 := bstep (se 1 (by rfl) ⟨259166, by rfl⟩ : syracuseStep 345555 = 518333) B518333
theorem B345571 : Blo 342753 345571 := bstep (se 1 (by rfl) ⟨259178, by rfl⟩ : syracuseStep 345571 = 518357) B518357
theorem B771569 : Blo 342753 771569 := bstep (se 2 (by rfl) ⟨289338, by rfl⟩ : syracuseStep 771569 = 578677) B578677
theorem B345587 : Blo 342753 345587 := bstep (se 1 (by rfl) ⟨259190, by rfl⟩ : syracuseStep 345587 = 518381) B518381
theorem B771587 : Blo 342753 771587 := bstep (se 1 (by rfl) ⟨578690, by rfl⟩ : syracuseStep 771587 = 1157381) B1157381
theorem B345603 : Blo 342753 345603 := bstep (se 1 (by rfl) ⟨259202, by rfl⟩ : syracuseStep 345603 = 518405) B518405
theorem B345619 : Blo 342753 345619 := bstep (se 1 (by rfl) ⟨259214, by rfl⟩ : syracuseStep 345619 = 518429) B518429
theorem B345635 : Blo 342753 345635 := bstep (se 1 (by rfl) ⟨259226, by rfl⟩ : syracuseStep 345635 = 518453) B518453
theorem B345651 : Blo 342753 345651 := bstep (se 1 (by rfl) ⟨259238, by rfl⟩ : syracuseStep 345651 = 518477) B518477
theorem B345667 : Blo 342753 345667 := bstep (se 1 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 345667 = 518501) B518501
theorem B2246213 : Blo 342753 2246213 := bstep (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) B421165
theorem B345683 : Blo 342753 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B345699 : Blo 342753 345699 := bstep (se 1 (by rfl) ⟨259274, by rfl⟩ : syracuseStep 345699 = 518549) B518549
theorem B345715 : Blo 342753 345715 := bstep (se 1 (by rfl) ⟨259286, by rfl⟩ : syracuseStep 345715 = 518573) B518573
theorem B345731 : Blo 342753 345731 := bstep (se 1 (by rfl) ⟨259298, by rfl⟩ : syracuseStep 345731 = 518597) B518597
theorem B1164941 : Blo 342753 1164941 := bstep (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) B436853
theorem B345747 : Blo 342753 345747 := bstep (se 1 (by rfl) ⟨259310, by rfl⟩ : syracuseStep 345747 = 518621) B518621
theorem B345763 : Blo 342753 345763 := bstep (se 1 (by rfl) ⟨259322, by rfl⟩ : syracuseStep 345763 = 518645) B518645
theorem B345779 : Blo 342753 345779 := bstep (se 1 (by rfl) ⟨259334, by rfl⟩ : syracuseStep 345779 = 518669) B518669
theorem B1164995 : Blo 342753 1164995 := bstep (se 1 (by rfl) ⟨873746, by rfl⟩ : syracuseStep 1164995 = 1747493) B1747493
theorem B345795 : Blo 342753 345795 := bstep (se 1 (by rfl) ⟨259346, by rfl⟩ : syracuseStep 345795 = 518693) B518693
theorem B1099469 : Blo 342753 1099469 := bstep (se 3 (by rfl) ⟨206150, by rfl⟩ : syracuseStep 1099469 = 412301) B412301
theorem B345811 : Blo 342753 345811 := bstep (se 1 (by rfl) ⟨259358, by rfl⟩ : syracuseStep 345811 = 518717) B518717
theorem B345827 : Blo 342753 345827 := bstep (se 1 (by rfl) ⟨259370, by rfl⟩ : syracuseStep 345827 = 518741) B518741
theorem B345843 : Blo 342753 345843 := bstep (se 1 (by rfl) ⟨259382, by rfl⟩ : syracuseStep 345843 = 518765) B518765
theorem B345859 : Blo 342753 345859 := bstep (se 1 (by rfl) ⟨259394, by rfl⟩ : syracuseStep 345859 = 518789) B518789
theorem B771857 : Blo 342753 771857 := bstep (se 2 (by rfl) ⟨289446, by rfl⟩ : syracuseStep 771857 = 578893) B578893
theorem B345875 : Blo 342753 345875 := bstep (se 1 (by rfl) ⟨259406, by rfl⟩ : syracuseStep 345875 = 518813) B518813
theorem B771875 : Blo 342753 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B345891 : Blo 342753 345891 := bstep (se 1 (by rfl) ⟨259418, by rfl⟩ : syracuseStep 345891 = 518837) B518837
theorem B345907 : Blo 342753 345907 := bstep (se 1 (by rfl) ⟨259430, by rfl⟩ : syracuseStep 345907 = 518861) B518861
theorem B345923 : Blo 342753 345923 := bstep (se 1 (by rfl) ⟨259442, by rfl⟩ : syracuseStep 345923 = 518885) B518885
theorem B345939 : Blo 342753 345939 := bstep (se 1 (by rfl) ⟨259454, by rfl⟩ : syracuseStep 345939 = 518909) B518909
theorem B345955 : Blo 342753 345955 := bstep (se 1 (by rfl) ⟨259466, by rfl⟩ : syracuseStep 345955 = 518933) B518933
theorem B345971 : Blo 342753 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B345987 : Blo 342753 345987 := bstep (se 1 (by rfl) ⟨259490, by rfl⟩ : syracuseStep 345987 = 518981) B518981
theorem B346003 : Blo 342753 346003 := bstep (se 1 (by rfl) ⟨259502, by rfl⟩ : syracuseStep 346003 = 519005) B519005
theorem B346019 : Blo 342753 346019 := bstep (se 1 (by rfl) ⟨259514, by rfl⟩ : syracuseStep 346019 = 519029) B519029
theorem B346035 : Blo 342753 346035 := bstep (se 1 (by rfl) ⟨259526, by rfl⟩ : syracuseStep 346035 = 519053) B519053
theorem B346051 : Blo 342753 346051 := bstep (se 1 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 346051 = 519077) B519077
theorem B1165265 : Blo 342753 1165265 := bstep (se 2 (by rfl) ⟨436974, by rfl⟩ : syracuseStep 1165265 = 873949) B873949
theorem B346067 : Blo 342753 346067 := bstep (se 1 (by rfl) ⟨259550, by rfl⟩ : syracuseStep 346067 = 519101) B519101
theorem B346083 : Blo 342753 346083 := bstep (se 1 (by rfl) ⟨259562, by rfl⟩ : syracuseStep 346083 = 519125) B519125
theorem B1755107 : Blo 342753 1755107 := bstep (se 1 (by rfl) ⟨1316330, by rfl⟩ : syracuseStep 1755107 = 2632661) B2632661
theorem B870385 : Blo 342753 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B346099 : Blo 342753 346099 := bstep (se 1 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 346099 = 519149) B519149
theorem B346115 : Blo 342753 346115 := bstep (se 1 (by rfl) ⟨259586, by rfl⟩ : syracuseStep 346115 = 519173) B519173
theorem B346131 : Blo 342753 346131 := bstep (se 1 (by rfl) ⟨259598, by rfl⟩ : syracuseStep 346131 = 519197) B519197
theorem B346147 : Blo 342753 346147 := bstep (se 1 (by rfl) ⟨259610, by rfl⟩ : syracuseStep 346147 = 519221) B519221
theorem B772145 : Blo 342753 772145 := bstep (se 2 (by rfl) ⟨289554, by rfl⟩ : syracuseStep 772145 = 579109) B579109
theorem B346163 : Blo 342753 346163 := bstep (se 1 (by rfl) ⟨259622, by rfl⟩ : syracuseStep 346163 = 519245) B519245
theorem B772163 : Blo 342753 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B346179 : Blo 342753 346179 := bstep (se 1 (by rfl) ⟨259634, by rfl⟩ : syracuseStep 346179 = 519269) B519269
theorem B346195 : Blo 342753 346195 := bstep (se 1 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 346195 = 519293) B519293
theorem B346211 : Blo 342753 346211 := bstep (se 1 (by rfl) ⟨259658, by rfl⟩ : syracuseStep 346211 = 519317) B519317
theorem B346227 : Blo 342753 346227 := bstep (se 1 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 346227 = 519341) B519341
theorem B346243 : Blo 342753 346243 := bstep (se 1 (by rfl) ⟨259682, by rfl⟩ : syracuseStep 346243 = 519365) B519365
theorem B346259 : Blo 342753 346259 := bstep (se 1 (by rfl) ⟨259694, by rfl⟩ : syracuseStep 346259 = 519389) B519389
theorem B346275 : Blo 342753 346275 := bstep (se 1 (by rfl) ⟨259706, by rfl⟩ : syracuseStep 346275 = 519413) B519413
theorem B346291 : Blo 342753 346291 := bstep (se 1 (by rfl) ⟨259718, by rfl⟩ : syracuseStep 346291 = 519437) B519437
theorem B346307 : Blo 342753 346307 := bstep (se 1 (by rfl) ⟨259730, by rfl⟩ : syracuseStep 346307 = 519461) B519461
theorem B346323 : Blo 342753 346323 := bstep (se 1 (by rfl) ⟨259742, by rfl⟩ : syracuseStep 346323 = 519485) B519485
theorem B3786979 : Blo 342753 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B346339 : Blo 342753 346339 := bstep (se 1 (by rfl) ⟨259754, by rfl⟩ : syracuseStep 346339 = 519509) B519509
theorem B346355 : Blo 342753 346355 := bstep (se 1 (by rfl) ⟨259766, by rfl⟩ : syracuseStep 346355 = 519533) B519533
theorem B870659 : Blo 342753 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B346371 : Blo 342753 346371 := bstep (se 1 (by rfl) ⟨259778, by rfl⟩ : syracuseStep 346371 = 519557) B519557
theorem B346387 : Blo 342753 346387 := bstep (se 1 (by rfl) ⟨259790, by rfl⟩ : syracuseStep 346387 = 519581) B519581
theorem B346403 : Blo 342753 346403 := bstep (se 1 (by rfl) ⟨259802, by rfl⟩ : syracuseStep 346403 = 519605) B519605
theorem B346419 : Blo 342753 346419 := bstep (se 1 (by rfl) ⟨259814, by rfl⟩ : syracuseStep 346419 = 519629) B519629
theorem B739651 : Blo 342753 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B346435 : Blo 342753 346435 := bstep (se 1 (by rfl) ⟨259826, by rfl⟩ : syracuseStep 346435 = 519653) B519653
theorem B772433 : Blo 342753 772433 := bstep (se 2 (by rfl) ⟨289662, by rfl⟩ : syracuseStep 772433 = 579325) B579325
theorem B346451 : Blo 342753 346451 := bstep (se 1 (by rfl) ⟨259838, by rfl⟩ : syracuseStep 346451 = 519677) B519677
theorem B772451 : Blo 342753 772451 := bstep (se 1 (by rfl) ⟨579338, by rfl⟩ : syracuseStep 772451 = 1158677) B1158677
theorem B346467 : Blo 342753 346467 := bstep (se 1 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 346467 = 519701) B519701
theorem B346483 : Blo 342753 346483 := bstep (se 1 (by rfl) ⟨259862, by rfl⟩ : syracuseStep 346483 = 519725) B519725
theorem B346499 : Blo 342753 346499 := bstep (se 1 (by rfl) ⟨259874, by rfl⟩ : syracuseStep 346499 = 519749) B519749
theorem B346515 : Blo 342753 346515 := bstep (se 1 (by rfl) ⟨259886, by rfl⟩ : syracuseStep 346515 = 519773) B519773
theorem B346531 : Blo 342753 346531 := bstep (se 1 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 346531 = 519797) B519797
theorem B346547 : Blo 342753 346547 := bstep (se 1 (by rfl) ⟨259910, by rfl⟩ : syracuseStep 346547 = 519821) B519821
theorem B870851 : Blo 342753 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B346563 : Blo 342753 346563 := bstep (se 1 (by rfl) ⟨259922, by rfl⟩ : syracuseStep 346563 = 519845) B519845
theorem B346579 : Blo 342753 346579 := bstep (se 1 (by rfl) ⟨259934, by rfl⟩ : syracuseStep 346579 = 519869) B519869
theorem B346595 : Blo 342753 346595 := bstep (se 1 (by rfl) ⟨259946, by rfl⟩ : syracuseStep 346595 = 519893) B519893
theorem B1165805 : Blo 342753 1165805 := bstep (se 3 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 1165805 = 437177) B437177
theorem B510449 : Blo 342753 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B412147 : Blo 342753 412147 := bstep (se 1 (by rfl) ⟨309110, by rfl⟩ : syracuseStep 412147 = 618221) B618221
theorem B346611 : Blo 342753 346611 := bstep (se 1 (by rfl) ⟨259958, by rfl⟩ : syracuseStep 346611 = 519917) B519917
theorem B346627 : Blo 342753 346627 := bstep (se 1 (by rfl) ⟨259970, by rfl⟩ : syracuseStep 346627 = 519941) B519941
theorem B346643 : Blo 342753 346643 := bstep (se 1 (by rfl) ⟨259982, by rfl⟩ : syracuseStep 346643 = 519965) B519965
theorem B1165859 : Blo 342753 1165859 := bstep (se 1 (by rfl) ⟨874394, by rfl⟩ : syracuseStep 1165859 = 1748789) B1748789
theorem B346659 : Blo 342753 346659 := bstep (se 1 (by rfl) ⟨259994, by rfl⟩ : syracuseStep 346659 = 519989) B519989
theorem B346675 : Blo 342753 346675 := bstep (se 1 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 346675 = 520013) B520013
theorem B346691 : Blo 342753 346691 := bstep (se 1 (by rfl) ⟨260018, by rfl⟩ : syracuseStep 346691 = 520037) B520037
theorem B346707 : Blo 342753 346707 := bstep (se 1 (by rfl) ⟨260030, by rfl⟩ : syracuseStep 346707 = 520061) B520061
theorem B346723 : Blo 342753 346723 := bstep (se 1 (by rfl) ⟨260042, by rfl⟩ : syracuseStep 346723 = 520085) B520085
theorem B772721 : Blo 342753 772721 := bstep (se 2 (by rfl) ⟨289770, by rfl⟩ : syracuseStep 772721 = 579541) B579541
theorem B346739 : Blo 342753 346739 := bstep (se 1 (by rfl) ⟨260054, by rfl⟩ : syracuseStep 346739 = 520109) B520109
theorem B772739 : Blo 342753 772739 := bstep (se 1 (by rfl) ⟨579554, by rfl⟩ : syracuseStep 772739 = 1159109) B1159109
theorem B3721909 : Blo 342753 3721909 := bstep (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) B348929
theorem B1100557 : Blo 342753 1100557 := bstep (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) B412709
theorem B1166129 : Blo 342753 1166129 := bstep (se 2 (by rfl) ⟨437298, by rfl⟩ : syracuseStep 1166129 = 874597) B874597
theorem B773009 : Blo 342753 773009 := bstep (se 2 (by rfl) ⟨289878, by rfl⟩ : syracuseStep 773009 = 579757) B579757
theorem B773027 : Blo 342753 773027 := bstep (se 1 (by rfl) ⟨579770, by rfl⟩ : syracuseStep 773027 = 1159541) B1159541
theorem B1395683 : Blo 342753 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B740497 : Blo 342753 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B773297 : Blo 342753 773297 := bstep (se 2 (by rfl) ⟨289986, by rfl⟩ : syracuseStep 773297 = 579973) B579973
theorem B773315 : Blo 342753 773315 := bstep (se 1 (by rfl) ⟨579986, by rfl⟩ : syracuseStep 773315 = 1159973) B1159973
theorem B1166669 : Blo 342753 1166669 := bstep (se 3 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 1166669 = 437501) B437501
theorem B871793 : Blo 342753 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B1166723 : Blo 342753 1166723 := bstep (se 1 (by rfl) ⟨875042, by rfl⟩ : syracuseStep 1166723 = 1750085) B1750085
theorem B871843 : Blo 342753 871843 := bstep (se 1 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 871843 = 1307765) B1307765
theorem B773585 : Blo 342753 773585 := bstep (se 2 (by rfl) ⟨290094, by rfl⟩ : syracuseStep 773585 = 580189) B580189
theorem B773603 : Blo 342753 773603 := bstep (se 1 (by rfl) ⟨580202, by rfl⟩ : syracuseStep 773603 = 1160405) B1160405
theorem B871985 : Blo 342753 871985 := bstep (se 2 (by rfl) ⟨326994, by rfl⟩ : syracuseStep 871985 = 653989) B653989
theorem B1166993 : Blo 342753 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B1986275 : Blo 342753 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B773873 : Blo 342753 773873 := bstep (se 2 (by rfl) ⟨290202, by rfl⟩ : syracuseStep 773873 = 580405) B580405
theorem B773891 : Blo 342753 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B2084621 : Blo 342753 2084621 := bstep (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) B781733
theorem B2641805 : Blo 342753 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B774161 : Blo 342753 774161 := bstep (se 2 (by rfl) ⟨290310, by rfl⟩ : syracuseStep 774161 = 580621) B580621
theorem B774179 : Blo 342753 774179 := bstep (se 1 (by rfl) ⟨580634, by rfl⟩ : syracuseStep 774179 = 1161269) B1161269
theorem B413843 : Blo 342753 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B1167533 : Blo 342753 1167533 := bstep (se 3 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 1167533 = 437825) B437825
theorem B1167587 : Blo 342753 1167587 := bstep (se 1 (by rfl) ⟨875690, by rfl⟩ : syracuseStep 1167587 = 1751381) B1751381
theorem B1331491 : Blo 342753 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B774449 : Blo 342753 774449 := bstep (se 2 (by rfl) ⟨290418, by rfl⟩ : syracuseStep 774449 = 580837) B580837
theorem B774467 : Blo 342753 774467 := bstep (se 1 (by rfl) ⟨580850, by rfl⟩ : syracuseStep 774467 = 1161701) B1161701
theorem B1167857 : Blo 342753 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B1102339 : Blo 342753 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B2118149 : Blo 342753 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B872977 : Blo 342753 872977 := bstep (se 2 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 872977 = 654733) B654733
theorem B1102403 : Blo 342753 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B774737 : Blo 342753 774737 := bstep (se 2 (by rfl) ⟨290526, by rfl⟩ : syracuseStep 774737 = 581053) B581053
theorem B774755 : Blo 342753 774755 := bstep (se 1 (by rfl) ⟨581066, by rfl⟩ : syracuseStep 774755 = 1162133) B1162133
theorem B3297905 : Blo 342753 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B1102481 : Blo 342753 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B873251 : Blo 342753 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B775025 : Blo 342753 775025 := bstep (se 2 (by rfl) ⟨290634, by rfl⟩ : syracuseStep 775025 = 581269) B581269
theorem B775043 : Blo 342753 775043 := bstep (se 1 (by rfl) ⟨581282, by rfl⟩ : syracuseStep 775043 = 1162565) B1162565
theorem B578515 : Blo 342753 578515 := bstep (se 1 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 578515 = 867773) B867773
theorem B873443 : Blo 342753 873443 := bstep (se 1 (by rfl) ⟨655082, by rfl⟩ : syracuseStep 873443 = 1310165) B1310165
theorem B3331043 : Blo 342753 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B513011 : Blo 342753 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B1168397 : Blo 342753 1168397 := bstep (se 3 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 1168397 = 438149) B438149
theorem B1168451 : Blo 342753 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B578657 : Blo 342753 578657 := bstep (se 2 (by rfl) ⟨216996, by rfl⟩ : syracuseStep 578657 = 433993) B433993
theorem B775313 : Blo 342753 775313 := bstep (se 2 (by rfl) ⟨290742, by rfl⟩ : syracuseStep 775313 = 581485) B581485
theorem B775331 : Blo 342753 775331 := bstep (se 1 (by rfl) ⟨581498, by rfl⟩ : syracuseStep 775331 = 1162997) B1162997
theorem B578785 : Blo 342753 578785 := bstep (se 2 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 578785 = 434089) B434089
theorem B4216049 : Blo 342753 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B578819 : Blo 342753 578819 := bstep (se 1 (by rfl) ⟨434114, by rfl⟩ : syracuseStep 578819 = 868229) B868229
theorem B1168721 : Blo 342753 1168721 := bstep (se 2 (by rfl) ⟨438270, by rfl⟩ : syracuseStep 1168721 = 876541) B876541
theorem B578947 : Blo 342753 578947 := bstep (se 1 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 578947 = 868421) B868421
theorem B2086307 : Blo 342753 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B775601 : Blo 342753 775601 := bstep (se 2 (by rfl) ⟨290850, by rfl⟩ : syracuseStep 775601 = 581701) B581701
theorem B775619 : Blo 342753 775619 := bstep (se 1 (by rfl) ⟨581714, by rfl⟩ : syracuseStep 775619 = 1163429) B1163429
theorem B579089 : Blo 342753 579089 := bstep (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) B434317
theorem B579217 : Blo 342753 579217 := bstep (se 2 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 579217 = 434413) B434413
theorem B2152099 : Blo 342753 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B579251 : Blo 342753 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B8345285 : Blo 342753 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B775889 : Blo 342753 775889 := bstep (se 2 (by rfl) ⟨290958, by rfl⟩ : syracuseStep 775889 = 581917) B581917
theorem B775907 : Blo 342753 775907 := bstep (se 1 (by rfl) ⟨581930, by rfl⟩ : syracuseStep 775907 = 1163861) B1163861
theorem B579379 : Blo 342753 579379 := bstep (se 1 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 579379 = 869069) B869069
theorem B1169261 : Blo 342753 1169261 := bstep (se 3 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 1169261 = 438473) B438473
theorem B874385 : Blo 342753 874385 := bstep (se 2 (by rfl) ⟨327894, by rfl⟩ : syracuseStep 874385 = 655789) B655789
theorem B1169315 : Blo 342753 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B579521 : Blo 342753 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B874435 : Blo 342753 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B776177 : Blo 342753 776177 := bstep (se 2 (by rfl) ⟨291066, by rfl⟩ : syracuseStep 776177 = 582133) B582133
theorem B776195 : Blo 342753 776195 := bstep (se 1 (by rfl) ⟨582146, by rfl⟩ : syracuseStep 776195 = 1164293) B1164293
theorem B579649 : Blo 342753 579649 := bstep (se 2 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 579649 = 434737) B434737
theorem B874577 : Blo 342753 874577 := bstep (se 2 (by rfl) ⟨327966, by rfl⟩ : syracuseStep 874577 = 655933) B655933
theorem B514145 : Blo 342753 514145 := bstep (se 2 (by rfl) ⟨192804, by rfl⟩ : syracuseStep 514145 = 385609) B385609
theorem B579683 : Blo 342753 579683 := bstep (se 1 (by rfl) ⟨434762, by rfl⟩ : syracuseStep 579683 = 869525) B869525
theorem B3922019 : Blo 342753 3922019 := bstep (se 1 (by rfl) ⟨2941514, by rfl⟩ : syracuseStep 3922019 = 5883029) B5883029
theorem B514163 : Blo 342753 514163 := bstep (se 1 (by rfl) ⟨385622, by rfl⟩ : syracuseStep 514163 = 771245) B771245
theorem B3528845 : Blo 342753 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B3725453 : Blo 342753 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B514193 : Blo 342753 514193 := bstep (se 2 (by rfl) ⟨192822, by rfl⟩ : syracuseStep 514193 = 385645) B385645
theorem B415891 : Blo 342753 415891 := bstep (se 1 (by rfl) ⟨311918, by rfl⟩ : syracuseStep 415891 = 623837) B623837
theorem B514211 : Blo 342753 514211 := bstep (se 1 (by rfl) ⟨385658, by rfl⟩ : syracuseStep 514211 = 771317) B771317
theorem B1169585 : Blo 342753 1169585 := bstep (se 2 (by rfl) ⟨438594, by rfl⟩ : syracuseStep 1169585 = 877189) B877189
theorem B514241 : Blo 342753 514241 := bstep (se 2 (by rfl) ⟨192840, by rfl⟩ : syracuseStep 514241 = 385681) B385681
theorem B514259 : Blo 342753 514259 := bstep (se 1 (by rfl) ⟨385694, by rfl⟩ : syracuseStep 514259 = 771389) B771389
theorem B579811 : Blo 342753 579811 := bstep (se 1 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 579811 = 869717) B869717
theorem B2218211 : Blo 342753 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B514289 : Blo 342753 514289 := bstep (se 2 (by rfl) ⟨192858, by rfl⟩ : syracuseStep 514289 = 385717) B385717
theorem B514307 : Blo 342753 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B776465 : Blo 342753 776465 := bstep (se 2 (by rfl) ⟨291174, by rfl⟩ : syracuseStep 776465 = 582349) B582349
theorem B514337 : Blo 342753 514337 := bstep (se 2 (by rfl) ⟨192876, by rfl⟩ : syracuseStep 514337 = 385753) B385753
theorem B776483 : Blo 342753 776483 := bstep (se 1 (by rfl) ⟨582362, by rfl⟩ : syracuseStep 776483 = 1164725) B1164725
theorem B514355 : Blo 342753 514355 := bstep (se 1 (by rfl) ⟨385766, by rfl⟩ : syracuseStep 514355 = 771533) B771533
theorem B514385 : Blo 342753 514385 := bstep (se 2 (by rfl) ⟨192894, by rfl⟩ : syracuseStep 514385 = 385789) B385789
theorem B416083 : Blo 342753 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B514403 : Blo 342753 514403 := bstep (se 1 (by rfl) ⟨385802, by rfl⟩ : syracuseStep 514403 = 771605) B771605
theorem B579953 : Blo 342753 579953 := bstep (se 2 (by rfl) ⟨217482, by rfl⟩ : syracuseStep 579953 = 434965) B434965
theorem B514433 : Blo 342753 514433 := bstep (se 2 (by rfl) ⟨192912, by rfl⟩ : syracuseStep 514433 = 385825) B385825
theorem B514451 : Blo 342753 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B514481 : Blo 342753 514481 := bstep (se 2 (by rfl) ⟨192930, by rfl⟩ : syracuseStep 514481 = 385861) B385861
theorem B514499 : Blo 342753 514499 := bstep (se 1 (by rfl) ⟨385874, by rfl⟩ : syracuseStep 514499 = 771749) B771749
theorem B1235405 : Blo 342753 1235405 := bstep (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) B463277
theorem B514529 : Blo 342753 514529 := bstep (se 2 (by rfl) ⟨192948, by rfl⟩ : syracuseStep 514529 = 385897) B385897
theorem B580081 : Blo 342753 580081 := bstep (se 2 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 580081 = 435061) B435061
theorem B514547 : Blo 342753 514547 := bstep (se 1 (by rfl) ⟨385910, by rfl⟩ : syracuseStep 514547 = 771821) B771821
theorem B514577 : Blo 342753 514577 := bstep (se 2 (by rfl) ⟨192966, by rfl⟩ : syracuseStep 514577 = 385933) B385933
theorem B1104401 : Blo 342753 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B580115 : Blo 342753 580115 := bstep (se 1 (by rfl) ⟨435086, by rfl⟩ : syracuseStep 580115 = 870173) B870173
theorem B514595 : Blo 342753 514595 := bstep (se 1 (by rfl) ⟨385946, by rfl⟩ : syracuseStep 514595 = 771893) B771893
theorem B776753 : Blo 342753 776753 := bstep (se 2 (by rfl) ⟨291282, by rfl⟩ : syracuseStep 776753 = 582565) B582565
theorem B514625 : Blo 342753 514625 := bstep (se 2 (by rfl) ⟨192984, by rfl⟩ : syracuseStep 514625 = 385969) B385969
theorem B776771 : Blo 342753 776771 := bstep (se 1 (by rfl) ⟨582578, by rfl⟩ : syracuseStep 776771 = 1165157) B1165157
theorem B1235533 : Blo 342753 1235533 := bstep (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) B463325
theorem B514643 : Blo 342753 514643 := bstep (se 1 (by rfl) ⟨385982, by rfl⟩ : syracuseStep 514643 = 771965) B771965
theorem B514673 : Blo 342753 514673 := bstep (se 2 (by rfl) ⟨193002, by rfl⟩ : syracuseStep 514673 = 386005) B386005
theorem B514691 : Blo 342753 514691 := bstep (se 1 (by rfl) ⟨386018, by rfl⟩ : syracuseStep 514691 = 772037) B772037
theorem B580243 : Blo 342753 580243 := bstep (se 1 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 580243 = 870365) B870365
theorem B514721 : Blo 342753 514721 := bstep (se 2 (by rfl) ⟨193020, by rfl⟩ : syracuseStep 514721 = 386041) B386041
theorem B514739 : Blo 342753 514739 := bstep (se 1 (by rfl) ⟨386054, by rfl⟩ : syracuseStep 514739 = 772109) B772109
theorem B1170125 : Blo 342753 1170125 := bstep (se 3 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 1170125 = 438797) B438797
theorem B514769 : Blo 342753 514769 := bstep (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) B386077
theorem B514787 : Blo 342753 514787 := bstep (se 1 (by rfl) ⟨386090, by rfl⟩ : syracuseStep 514787 = 772181) B772181
theorem B514817 : Blo 342753 514817 := bstep (se 2 (by rfl) ⟨193056, by rfl⟩ : syracuseStep 514817 = 386113) B386113
theorem B1170179 : Blo 342753 1170179 := bstep (se 1 (by rfl) ⟨877634, by rfl⟩ : syracuseStep 1170179 = 1755269) B1755269
theorem B514835 : Blo 342753 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B580385 : Blo 342753 580385 := bstep (se 2 (by rfl) ⟨217644, by rfl⟩ : syracuseStep 580385 = 435289) B435289
theorem B514865 : Blo 342753 514865 := bstep (se 2 (by rfl) ⟨193074, by rfl⟩ : syracuseStep 514865 = 386149) B386149
theorem B514883 : Blo 342753 514883 := bstep (se 1 (by rfl) ⟨386162, by rfl⟩ : syracuseStep 514883 = 772325) B772325
theorem B777041 : Blo 342753 777041 := bstep (se 2 (by rfl) ⟨291390, by rfl⟩ : syracuseStep 777041 = 582781) B582781
theorem B514913 : Blo 342753 514913 := bstep (se 2 (by rfl) ⟨193092, by rfl⟩ : syracuseStep 514913 = 386185) B386185
theorem B1858403 : Blo 342753 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B777059 : Blo 342753 777059 := bstep (se 1 (by rfl) ⟨582794, by rfl⟩ : syracuseStep 777059 = 1165589) B1165589
theorem B7035761 : Blo 342753 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B514931 : Blo 342753 514931 := bstep (se 1 (by rfl) ⟨386198, by rfl⟩ : syracuseStep 514931 = 772397) B772397
theorem B351091 : Blo 342753 351091 := bstep (se 1 (by rfl) ⟨263318, by rfl⟩ : syracuseStep 351091 = 526637) B526637
theorem B514961 : Blo 342753 514961 := bstep (se 2 (by rfl) ⟨193110, by rfl⟩ : syracuseStep 514961 = 386221) B386221
theorem B580513 : Blo 342753 580513 := bstep (se 2 (by rfl) ⟨217692, by rfl⟩ : syracuseStep 580513 = 435385) B435385
theorem B514979 : Blo 342753 514979 := bstep (se 1 (by rfl) ⟨386234, by rfl⟩ : syracuseStep 514979 = 772469) B772469
theorem B515009 : Blo 342753 515009 := bstep (se 2 (by rfl) ⟨193128, by rfl⟩ : syracuseStep 515009 = 386257) B386257
theorem B580547 : Blo 342753 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B515027 : Blo 342753 515027 := bstep (se 1 (by rfl) ⟨386270, by rfl⟩ : syracuseStep 515027 = 772541) B772541
theorem B515057 : Blo 342753 515057 := bstep (se 2 (by rfl) ⟨193146, by rfl⟩ : syracuseStep 515057 = 386293) B386293
theorem B515075 : Blo 342753 515075 := bstep (se 1 (by rfl) ⟨386306, by rfl⟩ : syracuseStep 515075 = 772613) B772613
theorem B3300365 : Blo 342753 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B515105 : Blo 342753 515105 := bstep (se 2 (by rfl) ⟨193164, by rfl⟩ : syracuseStep 515105 = 386329) B386329
theorem B1104941 : Blo 342753 1104941 := bstep (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) B414353
theorem B875569 : Blo 342753 875569 := bstep (se 2 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 875569 = 656677) B656677
theorem B515123 : Blo 342753 515123 := bstep (se 1 (by rfl) ⟨386342, by rfl⟩ : syracuseStep 515123 = 772685) B772685
theorem B580675 : Blo 342753 580675 := bstep (se 1 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 580675 = 871013) B871013
theorem B515153 : Blo 342753 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B515171 : Blo 342753 515171 := bstep (se 1 (by rfl) ⟨386378, by rfl⟩ : syracuseStep 515171 = 772757) B772757
theorem B777329 : Blo 342753 777329 := bstep (se 2 (by rfl) ⟨291498, by rfl⟩ : syracuseStep 777329 = 582997) B582997
theorem B515201 : Blo 342753 515201 := bstep (se 2 (by rfl) ⟨193200, by rfl⟩ : syracuseStep 515201 = 386401) B386401
theorem B777347 : Blo 342753 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B515219 : Blo 342753 515219 := bstep (se 1 (by rfl) ⟨386414, by rfl⟩ : syracuseStep 515219 = 772829) B772829
theorem B515249 : Blo 342753 515249 := bstep (se 2 (by rfl) ⟨193218, by rfl⟩ : syracuseStep 515249 = 386437) B386437
theorem B515267 : Blo 342753 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B580817 : Blo 342753 580817 := bstep (se 2 (by rfl) ⟨217806, by rfl⟩ : syracuseStep 580817 = 435613) B435613
theorem B515297 : Blo 342753 515297 := bstep (se 2 (by rfl) ⟨193236, by rfl⟩ : syracuseStep 515297 = 386473) B386473
theorem B515315 : Blo 342753 515315 := bstep (se 1 (by rfl) ⟨386486, by rfl⟩ : syracuseStep 515315 = 772973) B772973
theorem B4414733 : Blo 342753 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B515345 : Blo 342753 515345 := bstep (se 2 (by rfl) ⟨193254, by rfl⟩ : syracuseStep 515345 = 386509) B386509
theorem B515363 : Blo 342753 515363 := bstep (se 1 (by rfl) ⟨386522, by rfl⟩ : syracuseStep 515363 = 773045) B773045
theorem B515393 : Blo 342753 515393 := bstep (se 2 (by rfl) ⟨193272, by rfl⟩ : syracuseStep 515393 = 386545) B386545
theorem B875843 : Blo 342753 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B580945 : Blo 342753 580945 := bstep (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) B435709
theorem B515411 : Blo 342753 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B515441 : Blo 342753 515441 := bstep (se 2 (by rfl) ⟨193290, by rfl⟩ : syracuseStep 515441 = 386581) B386581
theorem B580979 : Blo 342753 580979 := bstep (se 1 (by rfl) ⟨435734, by rfl⟩ : syracuseStep 580979 = 871469) B871469
theorem B515459 : Blo 342753 515459 := bstep (se 1 (by rfl) ⟨386594, by rfl⟩ : syracuseStep 515459 = 773189) B773189
theorem B4709773 : Blo 342753 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B777617 : Blo 342753 777617 := bstep (se 2 (by rfl) ⟨291606, by rfl⟩ : syracuseStep 777617 = 583213) B583213
theorem B515489 : Blo 342753 515489 := bstep (se 2 (by rfl) ⟨193308, by rfl⟩ : syracuseStep 515489 = 386617) B386617
theorem B777635 : Blo 342753 777635 := bstep (se 1 (by rfl) ⟨583226, by rfl⟩ : syracuseStep 777635 = 1166453) B1166453
theorem B515507 : Blo 342753 515507 := bstep (se 1 (by rfl) ⟨386630, by rfl⟩ : syracuseStep 515507 = 773261) B773261
theorem B515537 : Blo 342753 515537 := bstep (se 2 (by rfl) ⟨193326, by rfl⟩ : syracuseStep 515537 = 386653) B386653
theorem B515555 : Blo 342753 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B581107 : Blo 342753 581107 := bstep (se 1 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 581107 = 871661) B871661
theorem B515585 : Blo 342753 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B876035 : Blo 342753 876035 := bstep (se 1 (by rfl) ⟨657026, by rfl⟩ : syracuseStep 876035 = 1314053) B1314053
theorem B2481677 : Blo 342753 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B515603 : Blo 342753 515603 := bstep (se 1 (by rfl) ⟨386702, by rfl⟩ : syracuseStep 515603 = 773405) B773405
theorem B515633 : Blo 342753 515633 := bstep (se 2 (by rfl) ⟨193362, by rfl⟩ : syracuseStep 515633 = 386725) B386725
theorem B515651 : Blo 342753 515651 := bstep (se 1 (by rfl) ⟨386738, by rfl⟩ : syracuseStep 515651 = 773477) B773477
theorem B515681 : Blo 342753 515681 := bstep (se 2 (by rfl) ⟨193380, by rfl⟩ : syracuseStep 515681 = 386761) B386761
theorem B1302115 : Blo 342753 1302115 := bstep (se 1 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 1302115 = 1953173) B1953173
theorem B515699 : Blo 342753 515699 := bstep (se 1 (by rfl) ⟨386774, by rfl⟩ : syracuseStep 515699 = 773549) B773549
theorem B581249 : Blo 342753 581249 := bstep (se 2 (by rfl) ⟨217968, by rfl⟩ : syracuseStep 581249 = 435937) B435937
theorem B515729 : Blo 342753 515729 := bstep (se 2 (by rfl) ⟨193398, by rfl⟩ : syracuseStep 515729 = 386797) B386797
theorem B515747 : Blo 342753 515747 := bstep (se 1 (by rfl) ⟨386810, by rfl⟩ : syracuseStep 515747 = 773621) B773621
theorem B777905 : Blo 342753 777905 := bstep (se 2 (by rfl) ⟨291714, by rfl⟩ : syracuseStep 777905 = 583429) B583429
theorem B515777 : Blo 342753 515777 := bstep (se 2 (by rfl) ⟨193416, by rfl⟩ : syracuseStep 515777 = 386833) B386833
theorem B777923 : Blo 342753 777923 := bstep (se 1 (by rfl) ⟨583442, by rfl⟩ : syracuseStep 777923 = 1166885) B1166885
theorem B515795 : Blo 342753 515795 := bstep (se 1 (by rfl) ⟨386846, by rfl⟩ : syracuseStep 515795 = 773693) B773693
theorem B515825 : Blo 342753 515825 := bstep (se 2 (by rfl) ⟨193434, by rfl⟩ : syracuseStep 515825 = 386869) B386869
theorem B581377 : Blo 342753 581377 := bstep (se 2 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 581377 = 436033) B436033
theorem B515843 : Blo 342753 515843 := bstep (se 1 (by rfl) ⟨386882, by rfl⟩ : syracuseStep 515843 = 773765) B773765
theorem B515873 : Blo 342753 515873 := bstep (se 2 (by rfl) ⟨193452, by rfl⟩ : syracuseStep 515873 = 386905) B386905
theorem B581411 : Blo 342753 581411 := bstep (se 1 (by rfl) ⟨436058, by rfl⟩ : syracuseStep 581411 = 872117) B872117
theorem B515891 : Blo 342753 515891 := bstep (se 1 (by rfl) ⟨386918, by rfl⟩ : syracuseStep 515891 = 773837) B773837
theorem B515921 : Blo 342753 515921 := bstep (se 2 (by rfl) ⟨193470, by rfl⟩ : syracuseStep 515921 = 386941) B386941
theorem B515939 : Blo 342753 515939 := bstep (se 1 (by rfl) ⟨386954, by rfl⟩ : syracuseStep 515939 = 773909) B773909
theorem B515969 : Blo 342753 515969 := bstep (se 2 (by rfl) ⟨193488, by rfl⟩ : syracuseStep 515969 = 386977) B386977
theorem B515987 : Blo 342753 515987 := bstep (se 1 (by rfl) ⟨386990, by rfl⟩ : syracuseStep 515987 = 773981) B773981
theorem B745379 : Blo 342753 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B581539 : Blo 342753 581539 := bstep (se 1 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 581539 = 872309) B872309
theorem B516017 : Blo 342753 516017 := bstep (se 2 (by rfl) ⟨193506, by rfl⟩ : syracuseStep 516017 = 387013) B387013
theorem B516035 : Blo 342753 516035 := bstep (se 1 (by rfl) ⟨387026, by rfl⟩ : syracuseStep 516035 = 774053) B774053
theorem B778193 : Blo 342753 778193 := bstep (se 2 (by rfl) ⟨291822, by rfl⟩ : syracuseStep 778193 = 583645) B583645
theorem B516065 : Blo 342753 516065 := bstep (se 2 (by rfl) ⟨193524, by rfl⟩ : syracuseStep 516065 = 387049) B387049
theorem B778211 : Blo 342753 778211 := bstep (se 1 (by rfl) ⟨583658, by rfl⟩ : syracuseStep 778211 = 1167317) B1167317
theorem B516083 : Blo 342753 516083 := bstep (se 1 (by rfl) ⟨387062, by rfl⟩ : syracuseStep 516083 = 774125) B774125
theorem B516113 : Blo 342753 516113 := bstep (se 2 (by rfl) ⟨193542, by rfl⟩ : syracuseStep 516113 = 387085) B387085
theorem B516131 : Blo 342753 516131 := bstep (se 1 (by rfl) ⟨387098, by rfl⟩ : syracuseStep 516131 = 774197) B774197
theorem B581681 : Blo 342753 581681 := bstep (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) B436261
theorem B516161 : Blo 342753 516161 := bstep (se 2 (by rfl) ⟨193560, by rfl⟩ : syracuseStep 516161 = 387121) B387121
theorem B516179 : Blo 342753 516179 := bstep (se 1 (by rfl) ⟨387134, by rfl⟩ : syracuseStep 516179 = 774269) B774269
theorem B516209 : Blo 342753 516209 := bstep (se 2 (by rfl) ⟨193578, by rfl⟩ : syracuseStep 516209 = 387157) B387157
theorem B516227 : Blo 342753 516227 := bstep (se 1 (by rfl) ⟨387170, by rfl⟩ : syracuseStep 516227 = 774341) B774341
theorem B516257 : Blo 342753 516257 := bstep (se 2 (by rfl) ⟨193596, by rfl⟩ : syracuseStep 516257 = 387193) B387193
theorem B581809 : Blo 342753 581809 := bstep (se 2 (by rfl) ⟨218178, by rfl⟩ : syracuseStep 581809 = 436357) B436357
theorem B516275 : Blo 342753 516275 := bstep (se 1 (by rfl) ⟨387206, by rfl⟩ : syracuseStep 516275 = 774413) B774413
theorem B516305 : Blo 342753 516305 := bstep (se 2 (by rfl) ⟨193614, by rfl⟩ : syracuseStep 516305 = 387229) B387229
theorem B581843 : Blo 342753 581843 := bstep (se 1 (by rfl) ⟨436382, by rfl⟩ : syracuseStep 581843 = 872765) B872765
theorem B516323 : Blo 342753 516323 := bstep (se 1 (by rfl) ⟨387242, by rfl⟩ : syracuseStep 516323 = 774485) B774485
theorem B778481 : Blo 342753 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B516353 : Blo 342753 516353 := bstep (se 2 (by rfl) ⟨193632, by rfl⟩ : syracuseStep 516353 = 387265) B387265
theorem B778499 : Blo 342753 778499 := bstep (se 1 (by rfl) ⟨583874, by rfl⟩ : syracuseStep 778499 = 1167749) B1167749
theorem B516371 : Blo 342753 516371 := bstep (se 1 (by rfl) ⟨387278, by rfl⟩ : syracuseStep 516371 = 774557) B774557
theorem B516401 : Blo 342753 516401 := bstep (se 2 (by rfl) ⟨193650, by rfl⟩ : syracuseStep 516401 = 387301) B387301
theorem B516419 : Blo 342753 516419 := bstep (se 1 (by rfl) ⟨387314, by rfl⟩ : syracuseStep 516419 = 774629) B774629
theorem B581971 : Blo 342753 581971 := bstep (se 1 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 581971 = 872957) B872957
theorem B516449 : Blo 342753 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B516467 : Blo 342753 516467 := bstep (se 1 (by rfl) ⟨387350, by rfl⟩ : syracuseStep 516467 = 774701) B774701
theorem B2646413 : Blo 342753 2646413 := bstep (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) B992405
theorem B516497 : Blo 342753 516497 := bstep (se 2 (by rfl) ⟨193686, by rfl⟩ : syracuseStep 516497 = 387373) B387373
theorem B516515 : Blo 342753 516515 := bstep (se 1 (by rfl) ⟨387386, by rfl⟩ : syracuseStep 516515 = 774773) B774773
theorem B876977 : Blo 342753 876977 := bstep (se 2 (by rfl) ⟨328866, by rfl⟩ : syracuseStep 876977 = 657733) B657733
theorem B516545 : Blo 342753 516545 := bstep (se 2 (by rfl) ⟨193704, by rfl⟩ : syracuseStep 516545 = 387409) B387409
theorem B516563 : Blo 342753 516563 := bstep (se 1 (by rfl) ⟨387422, by rfl⟩ : syracuseStep 516563 = 774845) B774845
theorem B582113 : Blo 342753 582113 := bstep (se 2 (by rfl) ⟨218292, by rfl⟩ : syracuseStep 582113 = 436585) B436585
theorem B877027 : Blo 342753 877027 := bstep (se 1 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 877027 = 1315541) B1315541
theorem B516593 : Blo 342753 516593 := bstep (se 2 (by rfl) ⟨193722, by rfl⟩ : syracuseStep 516593 = 387445) B387445
theorem B516611 : Blo 342753 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B778769 : Blo 342753 778769 := bstep (se 2 (by rfl) ⟨292038, by rfl⟩ : syracuseStep 778769 = 584077) B584077
theorem B516641 : Blo 342753 516641 := bstep (se 2 (by rfl) ⟨193740, by rfl⟩ : syracuseStep 516641 = 387481) B387481
theorem B778787 : Blo 342753 778787 := bstep (se 1 (by rfl) ⟨584090, by rfl⟩ : syracuseStep 778787 = 1168181) B1168181
theorem B1663523 : Blo 342753 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B516659 : Blo 342753 516659 := bstep (se 1 (by rfl) ⟨387494, by rfl⟩ : syracuseStep 516659 = 774989) B774989
theorem B516689 : Blo 342753 516689 := bstep (se 2 (by rfl) ⟨193758, by rfl⟩ : syracuseStep 516689 = 387517) B387517
theorem B582241 : Blo 342753 582241 := bstep (se 2 (by rfl) ⟨218340, by rfl⟩ : syracuseStep 582241 = 436681) B436681
theorem B516707 : Blo 342753 516707 := bstep (se 1 (by rfl) ⟨387530, by rfl⟩ : syracuseStep 516707 = 775061) B775061
theorem B1401457 : Blo 342753 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B877169 : Blo 342753 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B516737 : Blo 342753 516737 := bstep (se 2 (by rfl) ⟨193776, by rfl⟩ : syracuseStep 516737 = 387553) B387553
theorem B582275 : Blo 342753 582275 := bstep (se 1 (by rfl) ⟨436706, by rfl⟩ : syracuseStep 582275 = 873413) B873413
theorem B516755 : Blo 342753 516755 := bstep (se 1 (by rfl) ⟨387566, by rfl⟩ : syracuseStep 516755 = 775133) B775133
theorem B385699 : Blo 342753 385699 := bstep (se 1 (by rfl) ⟨289274, by rfl⟩ : syracuseStep 385699 = 578549) B578549
theorem B516785 : Blo 342753 516785 := bstep (se 2 (by rfl) ⟨193794, by rfl⟩ : syracuseStep 516785 = 387589) B387589
theorem B516803 : Blo 342753 516803 := bstep (se 1 (by rfl) ⟨387602, by rfl⟩ : syracuseStep 516803 = 775205) B775205
theorem B549587 : Blo 342753 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B516833 : Blo 342753 516833 := bstep (se 2 (by rfl) ⟨193812, by rfl⟩ : syracuseStep 516833 = 387625) B387625
theorem B1663715 : Blo 342753 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B516851 : Blo 342753 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B582403 : Blo 342753 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B516881 : Blo 342753 516881 := bstep (se 2 (by rfl) ⟨193830, by rfl⟩ : syracuseStep 516881 = 387661) B387661
theorem B516899 : Blo 342753 516899 := bstep (se 1 (by rfl) ⟨387674, by rfl⟩ : syracuseStep 516899 = 775349) B775349
theorem B779057 : Blo 342753 779057 := bstep (se 2 (by rfl) ⟨292146, by rfl⟩ : syracuseStep 779057 = 584293) B584293
theorem B385843 : Blo 342753 385843 := bstep (se 1 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 385843 = 578765) B578765
theorem B516929 : Blo 342753 516929 := bstep (se 2 (by rfl) ⟨193848, by rfl⟩ : syracuseStep 516929 = 387697) B387697
theorem B779075 : Blo 342753 779075 := bstep (se 1 (by rfl) ⟨584306, by rfl⟩ : syracuseStep 779075 = 1168613) B1168613
theorem B516947 : Blo 342753 516947 := bstep (se 1 (by rfl) ⟨387710, by rfl⟩ : syracuseStep 516947 = 775421) B775421
theorem B516977 : Blo 342753 516977 := bstep (se 2 (by rfl) ⟨193866, by rfl⟩ : syracuseStep 516977 = 387733) B387733
theorem B516995 : Blo 342753 516995 := bstep (se 1 (by rfl) ⟨387746, by rfl⟩ : syracuseStep 516995 = 775493) B775493
theorem B582545 : Blo 342753 582545 := bstep (se 2 (by rfl) ⟨218454, by rfl⟩ : syracuseStep 582545 = 436909) B436909
theorem B517025 : Blo 342753 517025 := bstep (se 2 (by rfl) ⟨193884, by rfl⟩ : syracuseStep 517025 = 387769) B387769
theorem B517043 : Blo 342753 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B385987 : Blo 342753 385987 := bstep (se 1 (by rfl) ⟨289490, by rfl⟩ : syracuseStep 385987 = 578981) B578981
theorem B1467341 : Blo 342753 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B517073 : Blo 342753 517073 := bstep (se 2 (by rfl) ⟨193902, by rfl⟩ : syracuseStep 517073 = 387805) B387805
theorem B517091 : Blo 342753 517091 := bstep (se 1 (by rfl) ⟨387818, by rfl⟩ : syracuseStep 517091 = 775637) B775637
theorem B517121 : Blo 342753 517121 := bstep (se 2 (by rfl) ⟨193920, by rfl⟩ : syracuseStep 517121 = 387841) B387841
theorem B582673 : Blo 342753 582673 := bstep (se 2 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 582673 = 437005) B437005
theorem B517139 : Blo 342753 517139 := bstep (se 1 (by rfl) ⟨387854, by rfl⟩ : syracuseStep 517139 = 775709) B775709
theorem B517169 : Blo 342753 517169 := bstep (se 2 (by rfl) ⟨193938, by rfl⟩ : syracuseStep 517169 = 387877) B387877
theorem B582707 : Blo 342753 582707 := bstep (se 1 (by rfl) ⟨437030, by rfl⟩ : syracuseStep 582707 = 874061) B874061
theorem B517187 : Blo 342753 517187 := bstep (se 1 (by rfl) ⟨387890, by rfl⟩ : syracuseStep 517187 = 775781) B775781
theorem B779345 : Blo 342753 779345 := bstep (se 2 (by rfl) ⟨292254, by rfl⟩ : syracuseStep 779345 = 584509) B584509
theorem B386131 : Blo 342753 386131 := bstep (se 1 (by rfl) ⟨289598, by rfl⟩ : syracuseStep 386131 = 579197) B579197
theorem B517217 : Blo 342753 517217 := bstep (se 2 (by rfl) ⟨193956, by rfl⟩ : syracuseStep 517217 = 387913) B387913
theorem B779363 : Blo 342753 779363 := bstep (se 1 (by rfl) ⟨584522, by rfl⟩ : syracuseStep 779363 = 1169045) B1169045
theorem B517235 : Blo 342753 517235 := bstep (se 1 (by rfl) ⟨387926, by rfl⟩ : syracuseStep 517235 = 775853) B775853
theorem B517265 : Blo 342753 517265 := bstep (se 2 (by rfl) ⟨193974, by rfl⟩ : syracuseStep 517265 = 387949) B387949
theorem B517283 : Blo 342753 517283 := bstep (se 1 (by rfl) ⟨387962, by rfl⟩ : syracuseStep 517283 = 775925) B775925
theorem B582835 : Blo 342753 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B517313 : Blo 342753 517313 := bstep (se 2 (by rfl) ⟨193992, by rfl⟩ : syracuseStep 517313 = 387985) B387985
theorem B550099 : Blo 342753 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B517331 : Blo 342753 517331 := bstep (se 1 (by rfl) ⟨387998, by rfl⟩ : syracuseStep 517331 = 775997) B775997
theorem B386275 : Blo 342753 386275 := bstep (se 1 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 386275 = 579413) B579413
theorem B517361 : Blo 342753 517361 := bstep (se 2 (by rfl) ⟨194010, by rfl⟩ : syracuseStep 517361 = 388021) B388021
theorem B550145 : Blo 342753 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B517379 : Blo 342753 517379 := bstep (se 1 (by rfl) ⟨388034, by rfl⟩ : syracuseStep 517379 = 776069) B776069
theorem B517409 : Blo 342753 517409 := bstep (se 2 (by rfl) ⟨194028, by rfl⟩ : syracuseStep 517409 = 388057) B388057
theorem B1467683 : Blo 342753 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B517427 : Blo 342753 517427 := bstep (se 1 (by rfl) ⟨388070, by rfl⟩ : syracuseStep 517427 = 776141) B776141
theorem B582977 : Blo 342753 582977 := bstep (se 2 (by rfl) ⟨218616, by rfl⟩ : syracuseStep 582977 = 437233) B437233
theorem B517457 : Blo 342753 517457 := bstep (se 2 (by rfl) ⟨194046, by rfl⟩ : syracuseStep 517457 = 388093) B388093
theorem B517475 : Blo 342753 517475 := bstep (se 1 (by rfl) ⟨388106, by rfl⟩ : syracuseStep 517475 = 776213) B776213
theorem B779633 : Blo 342753 779633 := bstep (se 2 (by rfl) ⟨292362, by rfl⟩ : syracuseStep 779633 = 584725) B584725
theorem B386419 : Blo 342753 386419 := bstep (se 1 (by rfl) ⟨289814, by rfl⟩ : syracuseStep 386419 = 579629) B579629
theorem B517505 : Blo 342753 517505 := bstep (se 2 (by rfl) ⟨194064, by rfl⟩ : syracuseStep 517505 = 388129) B388129
theorem B779651 : Blo 342753 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B517523 : Blo 342753 517523 := bstep (se 1 (by rfl) ⟨388142, by rfl⟩ : syracuseStep 517523 = 776285) B776285
theorem B517553 : Blo 342753 517553 := bstep (se 2 (by rfl) ⟨194082, by rfl⟩ : syracuseStep 517553 = 388165) B388165
theorem B583105 : Blo 342753 583105 := bstep (se 2 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 583105 = 437329) B437329
theorem B517571 : Blo 342753 517571 := bstep (se 1 (by rfl) ⟨388178, by rfl⟩ : syracuseStep 517571 = 776357) B776357
theorem B2942405 : Blo 342753 2942405 := bstep (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) B551701
theorem B976337 : Blo 342753 976337 := bstep (se 2 (by rfl) ⟨366126, by rfl⟩ : syracuseStep 976337 = 732253) B732253
theorem B517601 : Blo 342753 517601 := bstep (se 2 (by rfl) ⟨194100, by rfl⟩ : syracuseStep 517601 = 388201) B388201
theorem B583139 : Blo 342753 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B517619 : Blo 342753 517619 := bstep (se 1 (by rfl) ⟨388214, by rfl⟩ : syracuseStep 517619 = 776429) B776429
theorem B386563 : Blo 342753 386563 := bstep (se 1 (by rfl) ⟨289922, by rfl⟩ : syracuseStep 386563 = 579845) B579845
theorem B517649 : Blo 342753 517649 := bstep (se 2 (by rfl) ⟨194118, by rfl⟩ : syracuseStep 517649 = 388237) B388237
theorem B517667 : Blo 342753 517667 := bstep (se 1 (by rfl) ⟨388250, by rfl⟩ : syracuseStep 517667 = 776501) B776501
theorem B517697 : Blo 342753 517697 := bstep (se 2 (by rfl) ⟨194136, by rfl⟩ : syracuseStep 517697 = 388273) B388273
theorem B517715 : Blo 342753 517715 := bstep (se 1 (by rfl) ⟨388286, by rfl⟩ : syracuseStep 517715 = 776573) B776573
theorem B583267 : Blo 342753 583267 := bstep (se 1 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 583267 = 874901) B874901
theorem B517745 : Blo 342753 517745 := bstep (se 2 (by rfl) ⟨194154, by rfl⟩ : syracuseStep 517745 = 388309) B388309
theorem B517763 : Blo 342753 517763 := bstep (se 1 (by rfl) ⟨388322, by rfl⟩ : syracuseStep 517763 = 776645) B776645
theorem B779921 : Blo 342753 779921 := bstep (se 2 (by rfl) ⟨292470, by rfl⟩ : syracuseStep 779921 = 584941) B584941
theorem B386707 : Blo 342753 386707 := bstep (se 1 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 386707 = 580061) B580061
theorem B517793 : Blo 342753 517793 := bstep (se 2 (by rfl) ⟨194172, by rfl⟩ : syracuseStep 517793 = 388345) B388345
theorem B779939 : Blo 342753 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B517811 : Blo 342753 517811 := bstep (se 1 (by rfl) ⟨388358, by rfl⟩ : syracuseStep 517811 = 776717) B776717
theorem B517841 : Blo 342753 517841 := bstep (se 2 (by rfl) ⟨194190, by rfl⟩ : syracuseStep 517841 = 388381) B388381
theorem B517859 : Blo 342753 517859 := bstep (se 1 (by rfl) ⟨388394, by rfl⟩ : syracuseStep 517859 = 776789) B776789
theorem B1468145 : Blo 342753 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B583409 : Blo 342753 583409 := bstep (se 2 (by rfl) ⟨218778, by rfl⟩ : syracuseStep 583409 = 437557) B437557
theorem B517889 : Blo 342753 517889 := bstep (se 2 (by rfl) ⟨194208, by rfl⟩ : syracuseStep 517889 = 388417) B388417
theorem B1304333 : Blo 342753 1304333 := bstep (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) B489125
theorem B517907 : Blo 342753 517907 := bstep (se 1 (by rfl) ⟨388430, by rfl⟩ : syracuseStep 517907 = 776861) B776861
theorem B386851 : Blo 342753 386851 := bstep (se 1 (by rfl) ⟨290138, by rfl⟩ : syracuseStep 386851 = 580277) B580277
theorem B517937 : Blo 342753 517937 := bstep (se 2 (by rfl) ⟨194226, by rfl⟩ : syracuseStep 517937 = 388453) B388453
theorem B517955 : Blo 342753 517955 := bstep (se 1 (by rfl) ⟨388466, by rfl⟩ : syracuseStep 517955 = 776933) B776933
theorem B517985 : Blo 342753 517985 := bstep (se 2 (by rfl) ⟨194244, by rfl⟩ : syracuseStep 517985 = 388489) B388489
theorem B583537 : Blo 342753 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B518003 : Blo 342753 518003 := bstep (se 1 (by rfl) ⟨388502, by rfl⟩ : syracuseStep 518003 = 777005) B777005
theorem B518033 : Blo 342753 518033 := bstep (se 2 (by rfl) ⟨194262, by rfl⟩ : syracuseStep 518033 = 388525) B388525
theorem B583571 : Blo 342753 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B550817 : Blo 342753 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B518051 : Blo 342753 518051 := bstep (se 1 (by rfl) ⟨388538, by rfl⟩ : syracuseStep 518051 = 777077) B777077
theorem B1566641 : Blo 342753 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1664945 : Blo 342753 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B386995 : Blo 342753 386995 := bstep (se 1 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 386995 = 580493) B580493
theorem B518081 : Blo 342753 518081 := bstep (se 2 (by rfl) ⟨194280, by rfl⟩ : syracuseStep 518081 = 388561) B388561
theorem B518099 : Blo 342753 518099 := bstep (se 1 (by rfl) ⟨388574, by rfl⟩ : syracuseStep 518099 = 777149) B777149
theorem B518129 : Blo 342753 518129 := bstep (se 2 (by rfl) ⟨194298, by rfl⟩ : syracuseStep 518129 = 388597) B388597
theorem B518147 : Blo 342753 518147 := bstep (se 1 (by rfl) ⟨388610, by rfl⟩ : syracuseStep 518147 = 777221) B777221
theorem B583699 : Blo 342753 583699 := bstep (se 1 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 583699 = 875549) B875549
theorem B518177 : Blo 342753 518177 := bstep (se 2 (by rfl) ⟨194316, by rfl⟩ : syracuseStep 518177 = 388633) B388633
theorem B518195 : Blo 342753 518195 := bstep (se 1 (by rfl) ⟨388646, by rfl⟩ : syracuseStep 518195 = 777293) B777293
theorem B387139 : Blo 342753 387139 := bstep (se 1 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 387139 = 580709) B580709
theorem B518225 : Blo 342753 518225 := bstep (se 2 (by rfl) ⟨194334, by rfl⟩ : syracuseStep 518225 = 388669) B388669
theorem B518243 : Blo 342753 518243 := bstep (se 1 (by rfl) ⟨388682, by rfl⟩ : syracuseStep 518243 = 777365) B777365
theorem B518273 : Blo 342753 518273 := bstep (se 2 (by rfl) ⟨194352, by rfl⟩ : syracuseStep 518273 = 388705) B388705
theorem B518291 : Blo 342753 518291 := bstep (se 1 (by rfl) ⟨388718, by rfl⟩ : syracuseStep 518291 = 777437) B777437
theorem B583841 : Blo 342753 583841 := bstep (se 2 (by rfl) ⟨218940, by rfl⟩ : syracuseStep 583841 = 437881) B437881
theorem B518321 : Blo 342753 518321 := bstep (se 2 (by rfl) ⟨194370, by rfl⟩ : syracuseStep 518321 = 388741) B388741
theorem B518339 : Blo 342753 518339 := bstep (se 1 (by rfl) ⟨388754, by rfl⟩ : syracuseStep 518339 = 777509) B777509
theorem B387283 : Blo 342753 387283 := bstep (se 1 (by rfl) ⟨290462, by rfl⟩ : syracuseStep 387283 = 580925) B580925
theorem B518369 : Blo 342753 518369 := bstep (se 2 (by rfl) ⟨194388, by rfl⟩ : syracuseStep 518369 = 388777) B388777
theorem B977123 : Blo 342753 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B25389283 : Blo 342753 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B518387 : Blo 342753 518387 := bstep (se 1 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 518387 = 777581) B777581
theorem B518417 : Blo 342753 518417 := bstep (se 2 (by rfl) ⟨194406, by rfl⟩ : syracuseStep 518417 = 388813) B388813
theorem B583969 : Blo 342753 583969 := bstep (se 2 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 583969 = 437977) B437977
theorem B518435 : Blo 342753 518435 := bstep (se 1 (by rfl) ⟨388826, by rfl⟩ : syracuseStep 518435 = 777653) B777653
theorem B518465 : Blo 342753 518465 := bstep (se 2 (by rfl) ⟨194424, by rfl⟩ : syracuseStep 518465 = 388849) B388849
theorem B584003 : Blo 342753 584003 := bstep (se 1 (by rfl) ⟨438002, by rfl⟩ : syracuseStep 584003 = 876005) B876005
theorem B518483 : Blo 342753 518483 := bstep (se 1 (by rfl) ⟨388862, by rfl⟩ : syracuseStep 518483 = 777725) B777725
theorem B387427 : Blo 342753 387427 := bstep (se 1 (by rfl) ⟨290570, by rfl⟩ : syracuseStep 387427 = 581141) B581141
theorem B2615651 : Blo 342753 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B518513 : Blo 342753 518513 := bstep (se 2 (by rfl) ⟨194442, by rfl⟩ : syracuseStep 518513 = 388885) B388885
theorem B518531 : Blo 342753 518531 := bstep (se 1 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 518531 = 777797) B777797
theorem B551329 : Blo 342753 551329 := bstep (se 2 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 551329 = 413497) B413497
theorem B518561 : Blo 342753 518561 := bstep (se 2 (by rfl) ⟨194460, by rfl⟩ : syracuseStep 518561 = 388921) B388921
theorem B518579 : Blo 342753 518579 := bstep (se 1 (by rfl) ⟨388934, by rfl⟩ : syracuseStep 518579 = 777869) B777869
theorem B584131 : Blo 342753 584131 := bstep (se 1 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 584131 = 876197) B876197
theorem B518609 : Blo 342753 518609 := bstep (se 2 (by rfl) ⟨194478, by rfl⟩ : syracuseStep 518609 = 388957) B388957
theorem B518627 : Blo 342753 518627 := bstep (se 1 (by rfl) ⟨388970, by rfl⟩ : syracuseStep 518627 = 777941) B777941
theorem B1010161 : Blo 342753 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B387571 : Blo 342753 387571 := bstep (se 1 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 387571 = 581357) B581357
theorem B518657 : Blo 342753 518657 := bstep (se 2 (by rfl) ⟨194496, by rfl⟩ : syracuseStep 518657 = 388993) B388993
theorem B518675 : Blo 342753 518675 := bstep (se 1 (by rfl) ⟨389006, by rfl⟩ : syracuseStep 518675 = 778013) B778013
theorem B977453 : Blo 342753 977453 := bstep (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) B366545
theorem B518705 : Blo 342753 518705 := bstep (se 2 (by rfl) ⟨194514, by rfl⟩ : syracuseStep 518705 = 389029) B389029
theorem B1108529 : Blo 342753 1108529 := bstep (se 2 (by rfl) ⟨415698, by rfl⟩ : syracuseStep 1108529 = 831397) B831397
theorem B518723 : Blo 342753 518723 := bstep (se 1 (by rfl) ⟨389042, by rfl⟩ : syracuseStep 518723 = 778085) B778085
theorem B584273 : Blo 342753 584273 := bstep (se 2 (by rfl) ⟨219102, by rfl⟩ : syracuseStep 584273 = 438205) B438205
theorem B518753 : Blo 342753 518753 := bstep (se 2 (by rfl) ⟨194532, by rfl⟩ : syracuseStep 518753 = 389065) B389065
theorem B977521 : Blo 342753 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B518771 : Blo 342753 518771 := bstep (se 1 (by rfl) ⟨389078, by rfl⟩ : syracuseStep 518771 = 778157) B778157
theorem B387715 : Blo 342753 387715 := bstep (se 1 (by rfl) ⟨290786, by rfl⟩ : syracuseStep 387715 = 581573) B581573
theorem B2484877 : Blo 342753 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B518801 : Blo 342753 518801 := bstep (se 2 (by rfl) ⟨194550, by rfl⟩ : syracuseStep 518801 = 389101) B389101
theorem B518819 : Blo 342753 518819 := bstep (se 1 (by rfl) ⟨389114, by rfl⟩ : syracuseStep 518819 = 778229) B778229
theorem B518849 : Blo 342753 518849 := bstep (se 2 (by rfl) ⟨194568, by rfl⟩ : syracuseStep 518849 = 389137) B389137
theorem B1960645 : Blo 342753 1960645 := bstep (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) B367621
theorem B584401 : Blo 342753 584401 := bstep (se 2 (by rfl) ⟨219150, by rfl⟩ : syracuseStep 584401 = 438301) B438301
theorem B518867 : Blo 342753 518867 := bstep (se 1 (by rfl) ⟨389150, by rfl⟩ : syracuseStep 518867 = 778301) B778301
theorem B518897 : Blo 342753 518897 := bstep (se 2 (by rfl) ⟨194586, by rfl⟩ : syracuseStep 518897 = 389173) B389173
theorem B584435 : Blo 342753 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B518915 : Blo 342753 518915 := bstep (se 1 (by rfl) ⟨389186, by rfl⟩ : syracuseStep 518915 = 778373) B778373
theorem B387859 : Blo 342753 387859 := bstep (se 1 (by rfl) ⟨290894, by rfl⟩ : syracuseStep 387859 = 581789) B581789
theorem B518945 : Blo 342753 518945 := bstep (se 2 (by rfl) ⟨194604, by rfl⟩ : syracuseStep 518945 = 389209) B389209
theorem B518963 : Blo 342753 518963 := bstep (se 1 (by rfl) ⟨389222, by rfl⟩ : syracuseStep 518963 = 778445) B778445
theorem B518993 : Blo 342753 518993 := bstep (se 2 (by rfl) ⟨194622, by rfl⟩ : syracuseStep 518993 = 389245) B389245
theorem B519011 : Blo 342753 519011 := bstep (se 1 (by rfl) ⟨389258, by rfl⟩ : syracuseStep 519011 = 778517) B778517
theorem B584563 : Blo 342753 584563 := bstep (se 1 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 584563 = 876845) B876845
theorem B519041 : Blo 342753 519041 := bstep (se 2 (by rfl) ⟨194640, by rfl⟩ : syracuseStep 519041 = 389281) B389281
theorem B977795 : Blo 342753 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B519059 : Blo 342753 519059 := bstep (se 1 (by rfl) ⟨389294, by rfl⟩ : syracuseStep 519059 = 778589) B778589
theorem B388003 : Blo 342753 388003 := bstep (se 1 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 388003 = 582005) B582005
theorem B519089 : Blo 342753 519089 := bstep (se 2 (by rfl) ⟨194658, by rfl⟩ : syracuseStep 519089 = 389317) B389317
theorem B519107 : Blo 342753 519107 := bstep (se 1 (by rfl) ⟨389330, by rfl⟩ : syracuseStep 519107 = 778661) B778661
theorem B519137 : Blo 342753 519137 := bstep (se 2 (by rfl) ⟨194676, by rfl⟩ : syracuseStep 519137 = 389353) B389353
theorem B519155 : Blo 342753 519155 := bstep (se 1 (by rfl) ⟨389366, by rfl⟩ : syracuseStep 519155 = 778733) B778733
theorem B584705 : Blo 342753 584705 := bstep (se 2 (by rfl) ⟨219264, by rfl⟩ : syracuseStep 584705 = 438529) B438529
theorem B519185 : Blo 342753 519185 := bstep (se 2 (by rfl) ⟨194694, by rfl⟩ : syracuseStep 519185 = 389389) B389389
theorem B519203 : Blo 342753 519203 := bstep (se 1 (by rfl) ⟨389402, by rfl⟩ : syracuseStep 519203 = 778805) B778805
theorem B388147 : Blo 342753 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B519233 : Blo 342753 519233 := bstep (se 2 (by rfl) ⟨194712, by rfl⟩ : syracuseStep 519233 = 389425) B389425
theorem B519251 : Blo 342753 519251 := bstep (se 1 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 519251 = 778877) B778877
theorem B519281 : Blo 342753 519281 := bstep (se 2 (by rfl) ⟨194730, by rfl⟩ : syracuseStep 519281 = 389461) B389461
theorem B584833 : Blo 342753 584833 := bstep (se 2 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 584833 = 438625) B438625
theorem B519299 : Blo 342753 519299 := bstep (se 1 (by rfl) ⟨389474, by rfl⟩ : syracuseStep 519299 = 778949) B778949
theorem B519329 : Blo 342753 519329 := bstep (se 2 (by rfl) ⟨194748, by rfl⟩ : syracuseStep 519329 = 389497) B389497
theorem B584867 : Blo 342753 584867 := bstep (se 1 (by rfl) ⟨438650, by rfl⟩ : syracuseStep 584867 = 877301) B877301
theorem B519347 : Blo 342753 519347 := bstep (se 1 (by rfl) ⟨389510, by rfl⟩ : syracuseStep 519347 = 779021) B779021
theorem B388291 : Blo 342753 388291 := bstep (se 1 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 388291 = 582437) B582437
theorem B519377 : Blo 342753 519377 := bstep (se 2 (by rfl) ⟨194766, by rfl⟩ : syracuseStep 519377 = 389533) B389533
theorem B1109219 : Blo 342753 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B519395 : Blo 342753 519395 := bstep (se 1 (by rfl) ⟨389546, by rfl⟩ : syracuseStep 519395 = 779093) B779093
theorem B1666289 : Blo 342753 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B519425 : Blo 342753 519425 := bstep (se 2 (by rfl) ⟨194784, by rfl⟩ : syracuseStep 519425 = 389569) B389569
theorem B519443 : Blo 342753 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B584995 : Blo 342753 584995 := bstep (se 1 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 584995 = 877493) B877493
theorem B519473 : Blo 342753 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B519491 : Blo 342753 519491 := bstep (se 1 (by rfl) ⟨389618, by rfl⟩ : syracuseStep 519491 = 779237) B779237
theorem B388435 : Blo 342753 388435 := bstep (se 1 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 388435 = 582653) B582653
theorem B519521 : Blo 342753 519521 := bstep (se 2 (by rfl) ⟨194820, by rfl⟩ : syracuseStep 519521 = 389641) B389641
theorem B519539 : Blo 342753 519539 := bstep (se 1 (by rfl) ⟨389654, by rfl⟩ : syracuseStep 519539 = 779309) B779309
theorem B519569 : Blo 342753 519569 := bstep (se 2 (by rfl) ⟨194838, by rfl⟩ : syracuseStep 519569 = 389677) B389677
theorem B519587 : Blo 342753 519587 := bstep (se 1 (by rfl) ⟨389690, by rfl⟩ : syracuseStep 519587 = 779381) B779381
theorem B585137 : Blo 342753 585137 := bstep (se 2 (by rfl) ⟨219426, by rfl⟩ : syracuseStep 585137 = 438853) B438853
theorem B519617 : Blo 342753 519617 := bstep (se 2 (by rfl) ⟨194856, by rfl⟩ : syracuseStep 519617 = 389713) B389713
theorem B519635 : Blo 342753 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B388579 : Blo 342753 388579 := bstep (se 1 (by rfl) ⟨291434, by rfl⟩ : syracuseStep 388579 = 582869) B582869
theorem B519665 : Blo 342753 519665 := bstep (se 2 (by rfl) ⟨194874, by rfl⟩ : syracuseStep 519665 = 389749) B389749
theorem B519683 : Blo 342753 519683 := bstep (se 1 (by rfl) ⟨389762, by rfl⟩ : syracuseStep 519683 = 779525) B779525
theorem B519713 : Blo 342753 519713 := bstep (se 2 (by rfl) ⟨194892, by rfl⟩ : syracuseStep 519713 = 389785) B389785
theorem B519731 : Blo 342753 519731 := bstep (se 1 (by rfl) ⟨389798, by rfl⟩ : syracuseStep 519731 = 779597) B779597
theorem B519761 : Blo 342753 519761 := bstep (se 2 (by rfl) ⟨194910, by rfl⟩ : syracuseStep 519761 = 389821) B389821
theorem B519779 : Blo 342753 519779 := bstep (se 1 (by rfl) ⟨389834, by rfl⟩ : syracuseStep 519779 = 779669) B779669
theorem B388723 : Blo 342753 388723 := bstep (se 1 (by rfl) ⟨291542, by rfl⟩ : syracuseStep 388723 = 583085) B583085
theorem B519809 : Blo 342753 519809 := bstep (se 2 (by rfl) ⟨194928, by rfl⟩ : syracuseStep 519809 = 389857) B389857
theorem B519827 : Blo 342753 519827 := bstep (se 1 (by rfl) ⟨389870, by rfl⟩ : syracuseStep 519827 = 779741) B779741
theorem B552611 : Blo 342753 552611 := bstep (se 1 (by rfl) ⟨414458, by rfl⟩ : syracuseStep 552611 = 828917) B828917
theorem B650929 : Blo 342753 650929 := bstep (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) B488197
theorem B519857 : Blo 342753 519857 := bstep (se 2 (by rfl) ⟨194946, by rfl⟩ : syracuseStep 519857 = 389893) B389893
theorem B519875 : Blo 342753 519875 := bstep (se 1 (by rfl) ⟨389906, by rfl⟩ : syracuseStep 519875 = 779813) B779813
theorem B978637 : Blo 342753 978637 := bstep (se 3 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 978637 = 366989) B366989
theorem B519905 : Blo 342753 519905 := bstep (se 2 (by rfl) ⟨194964, by rfl⟩ : syracuseStep 519905 = 389929) B389929
theorem B519923 : Blo 342753 519923 := bstep (se 1 (by rfl) ⟨389942, by rfl⟩ : syracuseStep 519923 = 779885) B779885
theorem B388867 : Blo 342753 388867 := bstep (se 1 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 388867 = 583301) B583301
theorem B519953 : Blo 342753 519953 := bstep (se 2 (by rfl) ⟨194982, by rfl⟩ : syracuseStep 519953 = 389965) B389965
theorem B552739 : Blo 342753 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B519971 : Blo 342753 519971 := bstep (se 1 (by rfl) ⟨389978, by rfl⟩ : syracuseStep 519971 = 779957) B779957
theorem B520001 : Blo 342753 520001 := bstep (se 2 (by rfl) ⟨195000, by rfl⟩ : syracuseStep 520001 = 390001) B390001
theorem B520019 : Blo 342753 520019 := bstep (se 1 (by rfl) ⟨390014, by rfl⟩ : syracuseStep 520019 = 780029) B780029
theorem B978797 : Blo 342753 978797 := bstep (se 3 (by rfl) ⟨183524, by rfl⟩ : syracuseStep 978797 = 367049) B367049
theorem B520049 : Blo 342753 520049 := bstep (se 2 (by rfl) ⟨195018, by rfl⟩ : syracuseStep 520049 = 390037) B390037
theorem B520067 : Blo 342753 520067 := bstep (se 1 (by rfl) ⟨390050, by rfl⟩ : syracuseStep 520067 = 780101) B780101
theorem B389011 : Blo 342753 389011 := bstep (se 1 (by rfl) ⟨291758, by rfl⟩ : syracuseStep 389011 = 583517) B583517
theorem B520097 : Blo 342753 520097 := bstep (se 2 (by rfl) ⟨195036, by rfl⟩ : syracuseStep 520097 = 390073) B390073
theorem B552881 : Blo 342753 552881 := bstep (se 2 (by rfl) ⟨207330, by rfl⟩ : syracuseStep 552881 = 414661) B414661
theorem B520115 : Blo 342753 520115 := bstep (se 1 (by rfl) ⟨390086, by rfl⟩ : syracuseStep 520115 = 780173) B780173
theorem B978979 : Blo 342753 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B389155 : Blo 342753 389155 := bstep (se 1 (by rfl) ⟨291866, by rfl⟩ : syracuseStep 389155 = 583733) B583733
theorem B651331 : Blo 342753 651331 := bstep (se 1 (by rfl) ⟨488498, by rfl⟩ : syracuseStep 651331 = 976997) B976997
theorem B651377 : Blo 342753 651377 := bstep (se 2 (by rfl) ⟨244266, by rfl⟩ : syracuseStep 651377 = 488533) B488533
theorem B389299 : Blo 342753 389299 := bstep (se 1 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 389299 = 583949) B583949
theorem B553169 : Blo 342753 553169 := bstep (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) B414877
theorem B782627 : Blo 342753 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B389443 : Blo 342753 389443 := bstep (se 1 (by rfl) ⟨292082, by rfl⟩ : syracuseStep 389443 = 584165) B584165
theorem B651665 : Blo 342753 651665 := bstep (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) B488749
theorem B389587 : Blo 342753 389587 := bstep (se 1 (by rfl) ⟨292190, by rfl⟩ : syracuseStep 389587 = 584381) B584381
theorem B1045037 : Blo 342753 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B389731 : Blo 342753 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B1307249 : Blo 342753 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B1962629 : Blo 342753 1962629 := bstep (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) B367993
theorem B389875 : Blo 342753 389875 := bstep (se 1 (by rfl) ⟨292406, by rfl⟩ : syracuseStep 389875 = 584813) B584813
theorem B488225 : Blo 342753 488225 := bstep (se 2 (by rfl) ⟨183084, by rfl⟩ : syracuseStep 488225 = 366169) B366169
theorem B2356067 : Blo 342753 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B488305 : Blo 342753 488305 := bstep (se 2 (by rfl) ⟨183114, by rfl⟩ : syracuseStep 488305 = 366229) B366229
theorem B390019 : Blo 342753 390019 := bstep (se 1 (by rfl) ⟨292514, by rfl⟩ : syracuseStep 390019 = 585029) B585029
theorem B553969 : Blo 342753 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B652387 : Blo 342753 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B1471715 : Blo 342753 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B587107 : Blo 342753 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B980369 : Blo 342753 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B652835 : Blo 342753 652835 := bstep (se 1 (by rfl) ⟨489626, by rfl⟩ : syracuseStep 652835 = 979253) B979253
theorem B620131 : Blo 342753 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B489091 : Blo 342753 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B653123 : Blo 342753 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B1308707 : Blo 342753 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B489569 : Blo 342753 489569 := bstep (se 2 (by rfl) ⟨183588, by rfl⟩ : syracuseStep 489569 = 367177) B367177
theorem B784561 : Blo 342753 784561 := bstep (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) B588421
theorem B555187 : Blo 342753 555187 := bstep (se 1 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 555187 = 832781) B832781
theorem B489683 : Blo 342753 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B489763 : Blo 342753 489763 := bstep (se 1 (by rfl) ⟨367322, by rfl⟩ : syracuseStep 489763 = 734645) B734645
theorem B981325 : Blo 342753 981325 := bstep (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) B367997
theorem B2521613 : Blo 342753 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B981553 : Blo 342753 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B981713 : Blo 342753 981713 := bstep (se 2 (by rfl) ⟨368142, by rfl⟩ : syracuseStep 981713 = 736285) B736285
theorem B654065 : Blo 342753 654065 := bstep (se 2 (by rfl) ⟨245274, by rfl⟩ : syracuseStep 654065 = 490549) B490549
theorem B981827 : Blo 342753 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B490321 : Blo 342753 490321 := bstep (se 2 (by rfl) ⟨183870, by rfl⟩ : syracuseStep 490321 = 367741) B367741
theorem B588689 : Blo 342753 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B523187 : Blo 342753 523187 := bstep (se 1 (by rfl) ⟨392390, by rfl⟩ : syracuseStep 523187 = 784781) B784781
theorem B2489285 : Blo 342753 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B1309709 : Blo 342753 1309709 := bstep (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) B491141
theorem B2194445 : Blo 342753 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B523297 : Blo 342753 523297 := bstep (se 2 (by rfl) ⟨196236, by rfl⟩ : syracuseStep 523297 = 392473) B392473
theorem B1572173 : Blo 342753 1572173 := bstep (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) B589565
theorem B1080707 : Blo 342753 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B1146275 : Blo 342753 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B491027 : Blo 342753 491027 := bstep (se 1 (by rfl) ⟨368270, by rfl⟩ : syracuseStep 491027 = 736541) B736541
theorem B2620997 : Blo 342753 2620997 := bstep (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) B491437
theorem B654961 : Blo 342753 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B655121 : Blo 342753 655121 := bstep (se 2 (by rfl) ⟨245670, by rfl⟩ : syracuseStep 655121 = 491341) B491341
theorem B982829 : Blo 342753 982829 := bstep (se 3 (by rfl) ⟨184280, by rfl⟩ : syracuseStep 982829 = 368561) B368561
theorem B983011 : Blo 342753 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B655447 : Blo 342753 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B655553 : Blo 342753 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B655705 : Blo 342753 655705 := bstep (se 2 (by rfl) ⟨245889, by rfl⟩ : syracuseStep 655705 = 491779) B491779
theorem B623065 : Blo 342753 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B2621969 : Blo 342753 2621969 := bstep (se 2 (by rfl) ⟨983238, by rfl⟩ : syracuseStep 2621969 = 1966477) B1966477
theorem B1475117 : Blo 342753 1475117 := bstep (se 3 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 1475117 = 553169) B553169
theorem B983603 : Blo 342753 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B983627 : Blo 342753 983627 := bstep (se 1 (by rfl) ⟨737720, by rfl⟩ : syracuseStep 983627 = 1475441) B1475441
theorem B1868609 : Blo 342753 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B623447 : Blo 342753 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B1737773 : Blo 342753 1737773 := bstep (se 3 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 1737773 = 651665) B651665
theorem B1967435 : Blo 342753 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B984413 : Blo 342753 984413 := bstep (se 3 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 984413 = 369155) B369155
theorem B1312307 : Blo 342753 1312307 := bstep (se 1 (by rfl) ⟨984230, by rfl⟩ : syracuseStep 1312307 = 1968461) B1968461
theorem B1312321 : Blo 342753 1312321 := bstep (se 2 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 1312321 = 984241) B984241
theorem B36374129 : Blo 342753 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B657011 : Blo 342753 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B394871 : Blo 342753 394871 := bstep (se 1 (by rfl) ⟨296153, by rfl⟩ : syracuseStep 394871 = 592307) B592307
theorem B657163 : Blo 342753 657163 := bstep (se 1 (by rfl) ⟨492872, by rfl⟩ : syracuseStep 657163 = 985745) B985745
theorem B624449 : Blo 342753 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B1574801 : Blo 342753 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B493465 : Blo 342753 493465 := bstep (se 2 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 493465 = 370099) B370099
theorem B657497 : Blo 342753 657497 := bstep (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) B493123
theorem B1050803 : Blo 342753 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B2492633 : Blo 342753 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B2198117 : Blo 342753 2198117 := bstep (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) B412147
theorem B658135 : Blo 342753 658135 := bstep (se 1 (by rfl) ⟨493601, by rfl⟩ : syracuseStep 658135 = 987203) B987203
theorem B33852377 : Blo 342753 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B5049305 : Blo 342753 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1412099 : Blo 342753 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B2198603 : Blo 342753 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B986201 : Blo 342753 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B1346881 : Blo 342753 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B986519 : Blo 342753 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B1314251 : Blo 342753 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1314265 : Blo 342753 1314265 := bstep (se 2 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 1314265 = 985699) B985699
theorem B3313169 : Blo 342753 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B396875 : Blo 342753 396875 := bstep (se 1 (by rfl) ⟨297656, by rfl⟩ : syracuseStep 396875 = 595313) B595313
theorem B4951813 : Blo 342753 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B1478807 : Blo 342753 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B987329 : Blo 342753 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B823603 : Blo 342753 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B2625857 : Blo 342753 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B1315223 : Blo 342753 1315223 := bstep (se 1 (by rfl) ⟨986417, by rfl⟩ : syracuseStep 1315223 = 1972835) B1972835
theorem B594391 : Blo 342753 594391 := bstep (se 1 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 594391 = 891587) B891587
theorem B4690507 : Blo 342753 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B2200243 : Blo 342753 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B1741661 : Blo 342753 1741661 := bstep (se 3 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 1741661 = 653123) B653123
theorem B2954501 : Blo 342753 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B496919 : Blo 342753 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B5051765 : Blo 342753 5051765 := bstep (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) B473603
theorem B2496035 : Blo 342753 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1316483 : Blo 342753 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B3348119 : Blo 342753 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1775321 : Blo 342753 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B366391 : Blo 342753 366391 := bstep (se 1 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 366391 = 549587) B549587
theorem B464791 : Blo 342753 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B399371 : Blo 342753 399371 := bstep (se 1 (by rfl) ⟨299528, by rfl⟩ : syracuseStep 399371 = 599057) B599057
theorem B366763 : Blo 342753 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B2627801 : Blo 342753 2627801 := bstep (se 2 (by rfl) ⟨985425, by rfl⟩ : syracuseStep 2627801 = 1970851) B1970851
theorem B1579267 : Blo 342753 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B367211 : Blo 342753 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B1743767 : Blo 342753 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B826841 : Blo 342753 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B4955741 : Blo 342753 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B1777331 : Blo 342753 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B368407 : Blo 342753 368407 := bstep (se 1 (by rfl) ⟨276305, by rfl⟩ : syracuseStep 368407 = 552611) B552611
theorem B368587 : Blo 342753 368587 := bstep (se 1 (by rfl) ⟨276440, by rfl⟩ : syracuseStep 368587 = 552881) B552881
theorem B434251 : Blo 342753 434251 := bstep (se 1 (by rfl) ⟨325688, by rfl⟩ : syracuseStep 434251 = 651377) B651377
theorem B696691 : Blo 342753 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B2957917 : Blo 342753 2957917 := bstep (se 3 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 2957917 = 1109219) B1109219
theorem B1647377 : Blo 342753 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B435223 : Blo 342753 435223 := bstep (se 1 (by rfl) ⟨326417, by rfl⟩ : syracuseStep 435223 = 652835) B652835
theorem B468121 : Blo 342753 468121 := bstep (se 2 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 468121 = 351091) B351091
theorem B697729 : Blo 342753 697729 := bstep (se 2 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 697729 = 523297) B523297
theorem B2631203 : Blo 342753 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B1681075 : Blo 342753 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B436043 : Blo 342753 436043 := bstep (se 1 (by rfl) ⟨327032, by rfl⟩ : syracuseStep 436043 = 654065) B654065
theorem B1157057 : Blo 342753 1157057 := bstep (se 2 (by rfl) ⟨433896, by rfl⟩ : syracuseStep 1157057 = 867793) B867793
theorem B764183 : Blo 342753 764183 := bstep (se 1 (by rfl) ⟨573137, by rfl⟩ : syracuseStep 764183 = 1146275) B1146275
theorem B1747331 : Blo 342753 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B1157597 : Blo 342753 1157597 := bstep (se 3 (by rfl) ⟨217049, by rfl⟩ : syracuseStep 1157597 = 434099) B434099
theorem B3058181 : Blo 342753 3058181 := bstep (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) B573409
theorem B436747 : Blo 342753 436747 := bstep (se 1 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 436747 = 655121) B655121
theorem B437015 : Blo 342753 437015 := bstep (se 1 (by rfl) ⟨327761, by rfl⟩ : syracuseStep 437015 = 655523) B655523
theorem B732235 : Blo 342753 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B12102797 : Blo 342753 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B666839 : Blo 342753 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B437719 : Blo 342753 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B1158731 : Blo 342753 1158731 := bstep (se 1 (by rfl) ⟨869048, by rfl⟩ : syracuseStep 1158731 = 1738097) B1738097
theorem B732979 : Blo 342753 732979 := bstep (se 1 (by rfl) ⟨549734, by rfl⟩ : syracuseStep 732979 = 1099469) B1099469
theorem B1159001 : Blo 342753 1159001 := bstep (se 2 (by rfl) ⟨434625, by rfl⟩ : syracuseStep 1159001 = 869251) B869251
theorem B700631 : Blo 342753 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B733465 : Blo 342753 733465 := bstep (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) B550099
theorem B1159703 : Blo 342753 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B2929283 : Blo 342753 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B930455 : Blo 342753 930455 := bstep (se 1 (by rfl) ⟨697841, by rfl⟩ : syracuseStep 930455 = 1395683) B1395683
theorem B1160243 : Blo 342753 1160243 := bstep (se 1 (by rfl) ⟨870182, by rfl⟩ : syracuseStep 1160243 = 1740365) B1740365
theorem B1324183 : Blo 342753 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B1160513 : Blo 342753 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B40416853 : Blo 342753 40416853 := bstep (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) B473635
theorem B734935 : Blo 342753 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B734987 : Blo 342753 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B1455889 : Blo 342753 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B2471755 : Blo 342753 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B1161053 : Blo 342753 1161053 := bstep (se 3 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 1161053 = 435395) B435395
theorem B1751057 : Blo 342753 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B1751219 : Blo 342753 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B4962545 : Blo 342753 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B1390871 : Blo 342753 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B702935 : Blo 342753 702935 := bstep (se 1 (by rfl) ⟨527201, by rfl⟩ : syracuseStep 702935 = 1054403) B1054403
theorem B342763 : Blo 342753 342763 := bstep (se 1 (by rfl) ⟨257072, by rfl⟩ : syracuseStep 342763 = 514145) B514145
theorem B342775 : Blo 342753 342775 := bstep (se 1 (by rfl) ⟨257081, by rfl⟩ : syracuseStep 342775 = 514163) B514163
theorem B342795 : Blo 342753 342795 := bstep (se 1 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 342795 = 514193) B514193
theorem B342807 : Blo 342753 342807 := bstep (se 1 (by rfl) ⟨257105, by rfl⟩ : syracuseStep 342807 = 514211) B514211
theorem B342827 : Blo 342753 342827 := bstep (se 1 (by rfl) ⟨257120, by rfl⟩ : syracuseStep 342827 = 514241) B514241
theorem B342839 : Blo 342753 342839 := bstep (se 1 (by rfl) ⟨257129, by rfl⟩ : syracuseStep 342839 = 514259) B514259
theorem B4733761 : Blo 342753 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B342859 : Blo 342753 342859 := bstep (se 1 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 342859 = 514289) B514289
theorem B342871 : Blo 342753 342871 := bstep (se 1 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 342871 = 514307) B514307
theorem B342891 : Blo 342753 342891 := bstep (se 1 (by rfl) ⟨257168, by rfl⟩ : syracuseStep 342891 = 514337) B514337
theorem B342903 : Blo 342753 342903 := bstep (se 1 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 342903 = 514355) B514355
theorem B342923 : Blo 342753 342923 := bstep (se 1 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 342923 = 514385) B514385
theorem B342935 : Blo 342753 342935 := bstep (se 1 (by rfl) ⟨257201, by rfl⟩ : syracuseStep 342935 = 514403) B514403
theorem B342955 : Blo 342753 342955 := bstep (se 1 (by rfl) ⟨257216, by rfl⟩ : syracuseStep 342955 = 514433) B514433
theorem B342967 : Blo 342753 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B342987 : Blo 342753 342987 := bstep (se 1 (by rfl) ⟨257240, by rfl⟩ : syracuseStep 342987 = 514481) B514481
theorem B1162187 : Blo 342753 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B342999 : Blo 342753 342999 := bstep (se 1 (by rfl) ⟨257249, by rfl⟩ : syracuseStep 342999 = 514499) B514499
theorem B2931673 : Blo 342753 2931673 := bstep (se 2 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 2931673 = 2198755) B2198755
theorem B343019 : Blo 342753 343019 := bstep (se 1 (by rfl) ⟨257264, by rfl⟩ : syracuseStep 343019 = 514529) B514529
theorem B343031 : Blo 342753 343031 := bstep (se 1 (by rfl) ⟨257273, by rfl⟩ : syracuseStep 343031 = 514547) B514547
theorem B343051 : Blo 342753 343051 := bstep (se 1 (by rfl) ⟨257288, by rfl⟩ : syracuseStep 343051 = 514577) B514577
theorem B343063 : Blo 342753 343063 := bstep (se 1 (by rfl) ⟨257297, by rfl⟩ : syracuseStep 343063 = 514595) B514595
theorem B343083 : Blo 342753 343083 := bstep (se 1 (by rfl) ⟨257312, by rfl⟩ : syracuseStep 343083 = 514625) B514625
theorem B343095 : Blo 342753 343095 := bstep (se 1 (by rfl) ⟨257321, by rfl⟩ : syracuseStep 343095 = 514643) B514643
theorem B343115 : Blo 342753 343115 := bstep (se 1 (by rfl) ⟨257336, by rfl⟩ : syracuseStep 343115 = 514673) B514673
theorem B343127 : Blo 342753 343127 := bstep (se 1 (by rfl) ⟨257345, by rfl⟩ : syracuseStep 343127 = 514691) B514691
theorem B343147 : Blo 342753 343147 := bstep (se 1 (by rfl) ⟨257360, by rfl⟩ : syracuseStep 343147 = 514721) B514721
theorem B343159 : Blo 342753 343159 := bstep (se 1 (by rfl) ⟨257369, by rfl⟩ : syracuseStep 343159 = 514739) B514739
theorem B343179 : Blo 342753 343179 := bstep (se 1 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 343179 = 514769) B514769
theorem B343191 : Blo 342753 343191 := bstep (se 1 (by rfl) ⟨257393, by rfl⟩ : syracuseStep 343191 = 514787) B514787
theorem B343211 : Blo 342753 343211 := bstep (se 1 (by rfl) ⟨257408, by rfl⟩ : syracuseStep 343211 = 514817) B514817
theorem B343223 : Blo 342753 343223 := bstep (se 1 (by rfl) ⟨257417, by rfl⟩ : syracuseStep 343223 = 514835) B514835
theorem B343243 : Blo 342753 343243 := bstep (se 1 (by rfl) ⟨257432, by rfl⟩ : syracuseStep 343243 = 514865) B514865
theorem B343255 : Blo 342753 343255 := bstep (se 1 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 343255 = 514883) B514883
theorem B1162457 : Blo 342753 1162457 := bstep (se 2 (by rfl) ⟨435921, by rfl⟩ : syracuseStep 1162457 = 871843) B871843
theorem B343275 : Blo 342753 343275 := bstep (se 1 (by rfl) ⟨257456, by rfl⟩ : syracuseStep 343275 = 514913) B514913
theorem B343287 : Blo 342753 343287 := bstep (se 1 (by rfl) ⟨257465, by rfl⟩ : syracuseStep 343287 = 514931) B514931
theorem B343307 : Blo 342753 343307 := bstep (se 1 (by rfl) ⟨257480, by rfl⟩ : syracuseStep 343307 = 514961) B514961
theorem B343319 : Blo 342753 343319 := bstep (se 1 (by rfl) ⟨257489, by rfl⟩ : syracuseStep 343319 = 514979) B514979
theorem B343339 : Blo 342753 343339 := bstep (se 1 (by rfl) ⟨257504, by rfl⟩ : syracuseStep 343339 = 515009) B515009
theorem B343351 : Blo 342753 343351 := bstep (se 1 (by rfl) ⟨257513, by rfl⟩ : syracuseStep 343351 = 515027) B515027
theorem B343371 : Blo 342753 343371 := bstep (se 1 (by rfl) ⟨257528, by rfl⟩ : syracuseStep 343371 = 515057) B515057
theorem B343383 : Blo 342753 343383 := bstep (se 1 (by rfl) ⟨257537, by rfl⟩ : syracuseStep 343383 = 515075) B515075
theorem B343403 : Blo 342753 343403 := bstep (se 1 (by rfl) ⟨257552, by rfl⟩ : syracuseStep 343403 = 515105) B515105
theorem B736627 : Blo 342753 736627 := bstep (se 1 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 736627 = 1104941) B1104941
theorem B343415 : Blo 342753 343415 := bstep (se 1 (by rfl) ⟨257561, by rfl⟩ : syracuseStep 343415 = 515123) B515123
theorem B343435 : Blo 342753 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B343447 : Blo 342753 343447 := bstep (se 1 (by rfl) ⟨257585, by rfl⟩ : syracuseStep 343447 = 515171) B515171
theorem B343467 : Blo 342753 343467 := bstep (se 1 (by rfl) ⟨257600, by rfl⟩ : syracuseStep 343467 = 515201) B515201
theorem B343479 : Blo 342753 343479 := bstep (se 1 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 343479 = 515219) B515219
theorem B343499 : Blo 342753 343499 := bstep (se 1 (by rfl) ⟨257624, by rfl⟩ : syracuseStep 343499 = 515249) B515249
theorem B343511 : Blo 342753 343511 := bstep (se 1 (by rfl) ⟨257633, by rfl⟩ : syracuseStep 343511 = 515267) B515267
theorem B343531 : Blo 342753 343531 := bstep (se 1 (by rfl) ⟨257648, by rfl⟩ : syracuseStep 343531 = 515297) B515297
theorem B343543 : Blo 342753 343543 := bstep (se 1 (by rfl) ⟨257657, by rfl⟩ : syracuseStep 343543 = 515315) B515315
theorem B343563 : Blo 342753 343563 := bstep (se 1 (by rfl) ⟨257672, by rfl⟩ : syracuseStep 343563 = 515345) B515345
theorem B343575 : Blo 342753 343575 := bstep (se 1 (by rfl) ⟨257681, by rfl⟩ : syracuseStep 343575 = 515363) B515363
theorem B343595 : Blo 342753 343595 := bstep (se 1 (by rfl) ⟨257696, by rfl⟩ : syracuseStep 343595 = 515393) B515393
theorem B343607 : Blo 342753 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B867905 : Blo 342753 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B343627 : Blo 342753 343627 := bstep (se 1 (by rfl) ⟨257720, by rfl⟩ : syracuseStep 343627 = 515441) B515441
theorem B343639 : Blo 342753 343639 := bstep (se 1 (by rfl) ⟨257729, by rfl⟩ : syracuseStep 343639 = 515459) B515459
theorem B343659 : Blo 342753 343659 := bstep (se 1 (by rfl) ⟨257744, by rfl⟩ : syracuseStep 343659 = 515489) B515489
theorem B343671 : Blo 342753 343671 := bstep (se 1 (by rfl) ⟨257753, by rfl⟩ : syracuseStep 343671 = 515507) B515507
theorem B343691 : Blo 342753 343691 := bstep (se 1 (by rfl) ⟨257768, by rfl⟩ : syracuseStep 343691 = 515537) B515537
theorem B343703 : Blo 342753 343703 := bstep (se 1 (by rfl) ⟨257777, by rfl⟩ : syracuseStep 343703 = 515555) B515555
theorem B343723 : Blo 342753 343723 := bstep (se 1 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 343723 = 515585) B515585
theorem B1654451 : Blo 342753 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B343735 : Blo 342753 343735 := bstep (se 1 (by rfl) ⟨257801, by rfl⟩ : syracuseStep 343735 = 515603) B515603
theorem B343755 : Blo 342753 343755 := bstep (se 1 (by rfl) ⟨257816, by rfl⟩ : syracuseStep 343755 = 515633) B515633
theorem B343767 : Blo 342753 343767 := bstep (se 1 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 343767 = 515651) B515651
theorem B736985 : Blo 342753 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B343787 : Blo 342753 343787 := bstep (se 1 (by rfl) ⟨257840, by rfl⟩ : syracuseStep 343787 = 515681) B515681
theorem B343799 : Blo 342753 343799 := bstep (se 1 (by rfl) ⟨257849, by rfl⟩ : syracuseStep 343799 = 515699) B515699
theorem B343819 : Blo 342753 343819 := bstep (se 1 (by rfl) ⟨257864, by rfl⟩ : syracuseStep 343819 = 515729) B515729
theorem B343831 : Blo 342753 343831 := bstep (se 1 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 343831 = 515747) B515747
theorem B343851 : Blo 342753 343851 := bstep (se 1 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 343851 = 515777) B515777
theorem B343863 : Blo 342753 343863 := bstep (se 1 (by rfl) ⟨257897, by rfl⟩ : syracuseStep 343863 = 515795) B515795
theorem B343883 : Blo 342753 343883 := bstep (se 1 (by rfl) ⟨257912, by rfl⟩ : syracuseStep 343883 = 515825) B515825
theorem B343895 : Blo 342753 343895 := bstep (se 1 (by rfl) ⟨257921, by rfl⟩ : syracuseStep 343895 = 515843) B515843
theorem B343915 : Blo 342753 343915 := bstep (se 1 (by rfl) ⟨257936, by rfl⟩ : syracuseStep 343915 = 515873) B515873
theorem B343927 : Blo 342753 343927 := bstep (se 1 (by rfl) ⟨257945, by rfl⟩ : syracuseStep 343927 = 515891) B515891
theorem B343947 : Blo 342753 343947 := bstep (se 1 (by rfl) ⟨257960, by rfl⟩ : syracuseStep 343947 = 515921) B515921
theorem B2932631 : Blo 342753 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B343959 : Blo 342753 343959 := bstep (se 1 (by rfl) ⟨257969, by rfl⟩ : syracuseStep 343959 = 515939) B515939
theorem B1163159 : Blo 342753 1163159 := bstep (se 1 (by rfl) ⟨872369, by rfl⟩ : syracuseStep 1163159 = 1744739) B1744739
theorem B343979 : Blo 342753 343979 := bstep (se 1 (by rfl) ⟨257984, by rfl⟩ : syracuseStep 343979 = 515969) B515969
theorem B343991 : Blo 342753 343991 := bstep (se 1 (by rfl) ⟨257993, by rfl⟩ : syracuseStep 343991 = 515987) B515987
theorem B344011 : Blo 342753 344011 := bstep (se 1 (by rfl) ⟨258008, by rfl⟩ : syracuseStep 344011 = 516017) B516017
theorem B344023 : Blo 342753 344023 := bstep (se 1 (by rfl) ⟨258017, by rfl⟩ : syracuseStep 344023 = 516035) B516035
theorem B344043 : Blo 342753 344043 := bstep (se 1 (by rfl) ⟨258032, by rfl⟩ : syracuseStep 344043 = 516065) B516065
theorem B344055 : Blo 342753 344055 := bstep (se 1 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 344055 = 516083) B516083
theorem B344075 : Blo 342753 344075 := bstep (se 1 (by rfl) ⟨258056, by rfl⟩ : syracuseStep 344075 = 516113) B516113
theorem B344087 : Blo 342753 344087 := bstep (se 1 (by rfl) ⟨258065, by rfl⟩ : syracuseStep 344087 = 516131) B516131
theorem B344107 : Blo 342753 344107 := bstep (se 1 (by rfl) ⟨258080, by rfl⟩ : syracuseStep 344107 = 516161) B516161
theorem B344119 : Blo 342753 344119 := bstep (se 1 (by rfl) ⟨258089, by rfl⟩ : syracuseStep 344119 = 516179) B516179
theorem B1720385 : Blo 342753 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B344139 : Blo 342753 344139 := bstep (se 1 (by rfl) ⟨258104, by rfl⟩ : syracuseStep 344139 = 516209) B516209
theorem B1753163 : Blo 342753 1753163 := bstep (se 1 (by rfl) ⟨1314872, by rfl⟩ : syracuseStep 1753163 = 2629745) B2629745
theorem B344151 : Blo 342753 344151 := bstep (se 1 (by rfl) ⟨258113, by rfl⟩ : syracuseStep 344151 = 516227) B516227
theorem B868441 : Blo 342753 868441 := bstep (se 2 (by rfl) ⟨325665, by rfl⟩ : syracuseStep 868441 = 651331) B651331
theorem B344171 : Blo 342753 344171 := bstep (se 1 (by rfl) ⟨258128, by rfl⟩ : syracuseStep 344171 = 516257) B516257
theorem B344183 : Blo 342753 344183 := bstep (se 1 (by rfl) ⟨258137, by rfl⟩ : syracuseStep 344183 = 516275) B516275
theorem B344203 : Blo 342753 344203 := bstep (se 1 (by rfl) ⟨258152, by rfl⟩ : syracuseStep 344203 = 516305) B516305
theorem B344215 : Blo 342753 344215 := bstep (se 1 (by rfl) ⟨258161, by rfl⟩ : syracuseStep 344215 = 516323) B516323
theorem B344235 : Blo 342753 344235 := bstep (se 1 (by rfl) ⟨258176, by rfl⟩ : syracuseStep 344235 = 516353) B516353
theorem B344247 : Blo 342753 344247 := bstep (se 1 (by rfl) ⟨258185, by rfl⟩ : syracuseStep 344247 = 516371) B516371
theorem B344267 : Blo 342753 344267 := bstep (se 1 (by rfl) ⟨258200, by rfl⟩ : syracuseStep 344267 = 516401) B516401
theorem B344279 : Blo 342753 344279 := bstep (se 1 (by rfl) ⟨258209, by rfl⟩ : syracuseStep 344279 = 516419) B516419
theorem B344299 : Blo 342753 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B344311 : Blo 342753 344311 := bstep (se 1 (by rfl) ⟨258233, by rfl⟩ : syracuseStep 344311 = 516467) B516467
theorem B344331 : Blo 342753 344331 := bstep (se 1 (by rfl) ⟨258248, by rfl⟩ : syracuseStep 344331 = 516497) B516497
theorem B2933009 : Blo 342753 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B344343 : Blo 342753 344343 := bstep (se 1 (by rfl) ⟨258257, by rfl⟩ : syracuseStep 344343 = 516515) B516515
theorem B344363 : Blo 342753 344363 := bstep (se 1 (by rfl) ⟨258272, by rfl⟩ : syracuseStep 344363 = 516545) B516545
theorem B344375 : Blo 342753 344375 := bstep (se 1 (by rfl) ⟨258281, by rfl⟩ : syracuseStep 344375 = 516563) B516563
theorem B344395 : Blo 342753 344395 := bstep (se 1 (by rfl) ⟨258296, by rfl⟩ : syracuseStep 344395 = 516593) B516593
theorem B344407 : Blo 342753 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B442711 : Blo 342753 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B344427 : Blo 342753 344427 := bstep (se 1 (by rfl) ⟨258320, by rfl⟩ : syracuseStep 344427 = 516641) B516641
theorem B344439 : Blo 342753 344439 := bstep (se 1 (by rfl) ⟨258329, by rfl⟩ : syracuseStep 344439 = 516659) B516659
theorem B344459 : Blo 342753 344459 := bstep (se 1 (by rfl) ⟨258344, by rfl⟩ : syracuseStep 344459 = 516689) B516689
theorem B344471 : Blo 342753 344471 := bstep (se 1 (by rfl) ⟨258353, by rfl⟩ : syracuseStep 344471 = 516707) B516707
theorem B344491 : Blo 342753 344491 := bstep (se 1 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 344491 = 516737) B516737
theorem B3129779 : Blo 342753 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B1163699 : Blo 342753 1163699 := bstep (se 1 (by rfl) ⟨872774, by rfl⟩ : syracuseStep 1163699 = 1745549) B1745549
theorem B344503 : Blo 342753 344503 := bstep (se 1 (by rfl) ⟨258377, by rfl⟩ : syracuseStep 344503 = 516755) B516755
theorem B344523 : Blo 342753 344523 := bstep (se 1 (by rfl) ⟨258392, by rfl⟩ : syracuseStep 344523 = 516785) B516785
theorem B344535 : Blo 342753 344535 := bstep (se 1 (by rfl) ⟨258401, by rfl⟩ : syracuseStep 344535 = 516803) B516803
theorem B344555 : Blo 342753 344555 := bstep (se 1 (by rfl) ⟨258416, by rfl⟩ : syracuseStep 344555 = 516833) B516833
theorem B344567 : Blo 342753 344567 := bstep (se 1 (by rfl) ⟨258425, by rfl⟩ : syracuseStep 344567 = 516851) B516851
theorem B344587 : Blo 342753 344587 := bstep (se 1 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 344587 = 516881) B516881
theorem B344599 : Blo 342753 344599 := bstep (se 1 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 344599 = 516899) B516899
theorem B344619 : Blo 342753 344619 := bstep (se 1 (by rfl) ⟨258464, by rfl⟩ : syracuseStep 344619 = 516929) B516929
theorem B344631 : Blo 342753 344631 := bstep (se 1 (by rfl) ⟨258473, by rfl⟩ : syracuseStep 344631 = 516947) B516947
theorem B344651 : Blo 342753 344651 := bstep (se 1 (by rfl) ⟨258488, by rfl⟩ : syracuseStep 344651 = 516977) B516977
theorem B344663 : Blo 342753 344663 := bstep (se 1 (by rfl) ⟨258497, by rfl⟩ : syracuseStep 344663 = 516995) B516995
theorem B344683 : Blo 342753 344683 := bstep (se 1 (by rfl) ⟨258512, by rfl⟩ : syracuseStep 344683 = 517025) B517025
theorem B344695 : Blo 342753 344695 := bstep (se 1 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 344695 = 517043) B517043
theorem B344715 : Blo 342753 344715 := bstep (se 1 (by rfl) ⟨258536, by rfl⟩ : syracuseStep 344715 = 517073) B517073
theorem B344727 : Blo 342753 344727 := bstep (se 1 (by rfl) ⟨258545, by rfl⟩ : syracuseStep 344727 = 517091) B517091
theorem B344747 : Blo 342753 344747 := bstep (se 1 (by rfl) ⟨258560, by rfl⟩ : syracuseStep 344747 = 517121) B517121
theorem B344759 : Blo 342753 344759 := bstep (se 1 (by rfl) ⟨258569, by rfl⟩ : syracuseStep 344759 = 517139) B517139
theorem B1163969 : Blo 342753 1163969 := bstep (se 2 (by rfl) ⟨436488, by rfl⟩ : syracuseStep 1163969 = 872977) B872977
theorem B344779 : Blo 342753 344779 := bstep (se 1 (by rfl) ⟨258584, by rfl⟩ : syracuseStep 344779 = 517169) B517169
theorem B344791 : Blo 342753 344791 := bstep (se 1 (by rfl) ⟨258593, by rfl⟩ : syracuseStep 344791 = 517187) B517187
theorem B344811 : Blo 342753 344811 := bstep (se 1 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 344811 = 517217) B517217
theorem B344823 : Blo 342753 344823 := bstep (se 1 (by rfl) ⟨258617, by rfl⟩ : syracuseStep 344823 = 517235) B517235
theorem B344843 : Blo 342753 344843 := bstep (se 1 (by rfl) ⟨258632, by rfl⟩ : syracuseStep 344843 = 517265) B517265
theorem B1327889 : Blo 342753 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B344855 : Blo 342753 344855 := bstep (se 1 (by rfl) ⟨258641, by rfl⟩ : syracuseStep 344855 = 517283) B517283
theorem B344875 : Blo 342753 344875 := bstep (se 1 (by rfl) ⟨258656, by rfl⟩ : syracuseStep 344875 = 517313) B517313
theorem B344887 : Blo 342753 344887 := bstep (se 1 (by rfl) ⟨258665, by rfl⟩ : syracuseStep 344887 = 517331) B517331
theorem B344907 : Blo 342753 344907 := bstep (se 1 (by rfl) ⟨258680, by rfl⟩ : syracuseStep 344907 = 517361) B517361
theorem B344919 : Blo 342753 344919 := bstep (se 1 (by rfl) ⟨258689, by rfl⟩ : syracuseStep 344919 = 517379) B517379
theorem B344939 : Blo 342753 344939 := bstep (se 1 (by rfl) ⟨258704, by rfl⟩ : syracuseStep 344939 = 517409) B517409
theorem B344951 : Blo 342753 344951 := bstep (se 1 (by rfl) ⟨258713, by rfl⟩ : syracuseStep 344951 = 517427) B517427
theorem B344971 : Blo 342753 344971 := bstep (se 1 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 344971 = 517457) B517457
theorem B344983 : Blo 342753 344983 := bstep (se 1 (by rfl) ⟨258737, by rfl⟩ : syracuseStep 344983 = 517475) B517475
theorem B345003 : Blo 342753 345003 := bstep (se 1 (by rfl) ⟨258752, by rfl⟩ : syracuseStep 345003 = 517505) B517505
theorem B345015 : Blo 342753 345015 := bstep (se 1 (by rfl) ⟨258761, by rfl⟩ : syracuseStep 345015 = 517523) B517523
theorem B345035 : Blo 342753 345035 := bstep (se 1 (by rfl) ⟨258776, by rfl⟩ : syracuseStep 345035 = 517553) B517553
theorem B345047 : Blo 342753 345047 := bstep (se 1 (by rfl) ⟨258785, by rfl⟩ : syracuseStep 345047 = 517571) B517571
theorem B345067 : Blo 342753 345067 := bstep (se 1 (by rfl) ⟨258800, by rfl⟩ : syracuseStep 345067 = 517601) B517601
theorem B345079 : Blo 342753 345079 := bstep (se 1 (by rfl) ⟨258809, by rfl⟩ : syracuseStep 345079 = 517619) B517619
theorem B345099 : Blo 342753 345099 := bstep (se 1 (by rfl) ⟨258824, by rfl⟩ : syracuseStep 345099 = 517649) B517649
theorem B345111 : Blo 342753 345111 := bstep (se 1 (by rfl) ⟨258833, by rfl⟩ : syracuseStep 345111 = 517667) B517667
theorem B345131 : Blo 342753 345131 := bstep (se 1 (by rfl) ⟨258848, by rfl⟩ : syracuseStep 345131 = 517697) B517697
theorem B345143 : Blo 342753 345143 := bstep (se 1 (by rfl) ⟨258857, by rfl⟩ : syracuseStep 345143 = 517715) B517715
theorem B672833 : Blo 342753 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B345163 : Blo 342753 345163 := bstep (se 1 (by rfl) ⟨258872, by rfl⟩ : syracuseStep 345163 = 517745) B517745
theorem B345175 : Blo 342753 345175 := bstep (se 1 (by rfl) ⟨258881, by rfl⟩ : syracuseStep 345175 = 517763) B517763
theorem B345195 : Blo 342753 345195 := bstep (se 1 (by rfl) ⟨258896, by rfl⟩ : syracuseStep 345195 = 517793) B517793
theorem B345207 : Blo 342753 345207 := bstep (se 1 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 345207 = 517811) B517811
theorem B345227 : Blo 342753 345227 := bstep (se 1 (by rfl) ⟨258920, by rfl⟩ : syracuseStep 345227 = 517841) B517841
theorem B345239 : Blo 342753 345239 := bstep (se 1 (by rfl) ⟨258929, by rfl⟩ : syracuseStep 345239 = 517859) B517859
theorem B345259 : Blo 342753 345259 := bstep (se 1 (by rfl) ⟨258944, by rfl⟩ : syracuseStep 345259 = 517889) B517889
theorem B869555 : Blo 342753 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B345271 : Blo 342753 345271 := bstep (se 1 (by rfl) ⟨258953, by rfl⟩ : syracuseStep 345271 = 517907) B517907
theorem B345291 : Blo 342753 345291 := bstep (se 1 (by rfl) ⟨258968, by rfl⟩ : syracuseStep 345291 = 517937) B517937
theorem B345303 : Blo 342753 345303 := bstep (se 1 (by rfl) ⟨258977, by rfl⟩ : syracuseStep 345303 = 517955) B517955
theorem B1164509 : Blo 342753 1164509 := bstep (se 3 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 1164509 = 436691) B436691
theorem B345323 : Blo 342753 345323 := bstep (se 1 (by rfl) ⟨258992, by rfl⟩ : syracuseStep 345323 = 517985) B517985
theorem B345335 : Blo 342753 345335 := bstep (se 1 (by rfl) ⟨259001, by rfl⟩ : syracuseStep 345335 = 518003) B518003
theorem B4736261 : Blo 342753 4736261 := bstep (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) B888049
theorem B345355 : Blo 342753 345355 := bstep (se 1 (by rfl) ⟨259016, by rfl⟩ : syracuseStep 345355 = 518033) B518033
theorem B345367 : Blo 342753 345367 := bstep (se 1 (by rfl) ⟨259025, by rfl⟩ : syracuseStep 345367 = 518051) B518051
theorem B771353 : Blo 342753 771353 := bstep (se 2 (by rfl) ⟨289257, by rfl⟩ : syracuseStep 771353 = 578515) B578515
theorem B345387 : Blo 342753 345387 := bstep (se 1 (by rfl) ⟨259040, by rfl⟩ : syracuseStep 345387 = 518081) B518081
theorem B1361197 : Blo 342753 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B345399 : Blo 342753 345399 := bstep (se 1 (by rfl) ⟨259049, by rfl⟩ : syracuseStep 345399 = 518099) B518099
theorem B345419 : Blo 342753 345419 := bstep (se 1 (by rfl) ⟨259064, by rfl⟩ : syracuseStep 345419 = 518129) B518129
theorem B345431 : Blo 342753 345431 := bstep (se 1 (by rfl) ⟨259073, by rfl⟩ : syracuseStep 345431 = 518147) B518147
theorem B345451 : Blo 342753 345451 := bstep (se 1 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 345451 = 518177) B518177
theorem B771443 : Blo 342753 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B345463 : Blo 342753 345463 := bstep (se 1 (by rfl) ⟨259097, by rfl⟩ : syracuseStep 345463 = 518195) B518195
theorem B345483 : Blo 342753 345483 := bstep (se 1 (by rfl) ⟨259112, by rfl⟩ : syracuseStep 345483 = 518225) B518225
theorem B771479 : Blo 342753 771479 := bstep (se 1 (by rfl) ⟨578609, by rfl⟩ : syracuseStep 771479 = 1157219) B1157219
theorem B345495 : Blo 342753 345495 := bstep (se 1 (by rfl) ⟨259121, by rfl⟩ : syracuseStep 345495 = 518243) B518243
theorem B345515 : Blo 342753 345515 := bstep (se 1 (by rfl) ⟨259136, by rfl⟩ : syracuseStep 345515 = 518273) B518273
theorem B345527 : Blo 342753 345527 := bstep (se 1 (by rfl) ⟨259145, by rfl⟩ : syracuseStep 345527 = 518291) B518291
theorem B345547 : Blo 342753 345547 := bstep (se 1 (by rfl) ⟨259160, by rfl⟩ : syracuseStep 345547 = 518321) B518321
theorem B345559 : Blo 342753 345559 := bstep (se 1 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 345559 = 518339) B518339
theorem B869849 : Blo 342753 869849 := bstep (se 2 (by rfl) ⟨326193, by rfl⟩ : syracuseStep 869849 = 652387) B652387
theorem B345579 : Blo 342753 345579 := bstep (se 1 (by rfl) ⟨259184, by rfl⟩ : syracuseStep 345579 = 518369) B518369
theorem B345591 : Blo 342753 345591 := bstep (se 1 (by rfl) ⟨259193, by rfl⟩ : syracuseStep 345591 = 518387) B518387
theorem B345611 : Blo 342753 345611 := bstep (se 1 (by rfl) ⟨259208, by rfl⟩ : syracuseStep 345611 = 518417) B518417
theorem B345623 : Blo 342753 345623 := bstep (se 1 (by rfl) ⟨259217, by rfl⟩ : syracuseStep 345623 = 518435) B518435
theorem B345643 : Blo 342753 345643 := bstep (se 1 (by rfl) ⟨259232, by rfl⟩ : syracuseStep 345643 = 518465) B518465
theorem B345655 : Blo 342753 345655 := bstep (se 1 (by rfl) ⟨259241, by rfl⟩ : syracuseStep 345655 = 518483) B518483
theorem B771659 : Blo 342753 771659 := bstep (se 1 (by rfl) ⟨578744, by rfl⟩ : syracuseStep 771659 = 1157489) B1157489
theorem B345675 : Blo 342753 345675 := bstep (se 1 (by rfl) ⟨259256, by rfl⟩ : syracuseStep 345675 = 518513) B518513
theorem B345687 : Blo 342753 345687 := bstep (se 1 (by rfl) ⟨259265, by rfl⟩ : syracuseStep 345687 = 518531) B518531
theorem B345707 : Blo 342753 345707 := bstep (se 1 (by rfl) ⟨259280, by rfl⟩ : syracuseStep 345707 = 518561) B518561
theorem B345719 : Blo 342753 345719 := bstep (se 1 (by rfl) ⟨259289, by rfl⟩ : syracuseStep 345719 = 518579) B518579
theorem B771713 : Blo 342753 771713 := bstep (se 2 (by rfl) ⟨289392, by rfl⟩ : syracuseStep 771713 = 578785) B578785
theorem B345739 : Blo 342753 345739 := bstep (se 1 (by rfl) ⟨259304, by rfl⟩ : syracuseStep 345739 = 518609) B518609
theorem B345751 : Blo 342753 345751 := bstep (se 1 (by rfl) ⟨259313, by rfl⟩ : syracuseStep 345751 = 518627) B518627
theorem B345771 : Blo 342753 345771 := bstep (se 1 (by rfl) ⟨259328, by rfl⟩ : syracuseStep 345771 = 518657) B518657
theorem B345783 : Blo 342753 345783 := bstep (se 1 (by rfl) ⟨259337, by rfl⟩ : syracuseStep 345783 = 518675) B518675
theorem B345803 : Blo 342753 345803 := bstep (se 1 (by rfl) ⟨259352, by rfl⟩ : syracuseStep 345803 = 518705) B518705
theorem B739019 : Blo 342753 739019 := bstep (se 1 (by rfl) ⟨554264, by rfl⟩ : syracuseStep 739019 = 1108529) B1108529
theorem B345815 : Blo 342753 345815 := bstep (se 1 (by rfl) ⟨259361, by rfl⟩ : syracuseStep 345815 = 518723) B518723
theorem B345835 : Blo 342753 345835 := bstep (se 1 (by rfl) ⟨259376, by rfl⟩ : syracuseStep 345835 = 518753) B518753
theorem B345847 : Blo 342753 345847 := bstep (se 1 (by rfl) ⟨259385, by rfl⟩ : syracuseStep 345847 = 518771) B518771
theorem B345867 : Blo 342753 345867 := bstep (se 1 (by rfl) ⟨259400, by rfl⟩ : syracuseStep 345867 = 518801) B518801
theorem B345879 : Blo 342753 345879 := bstep (se 1 (by rfl) ⟨259409, by rfl⟩ : syracuseStep 345879 = 518819) B518819
theorem B345899 : Blo 342753 345899 := bstep (se 1 (by rfl) ⟨259424, by rfl⟩ : syracuseStep 345899 = 518849) B518849
theorem B345911 : Blo 342753 345911 := bstep (se 1 (by rfl) ⟨259433, by rfl⟩ : syracuseStep 345911 = 518867) B518867
theorem B1754945 : Blo 342753 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B345931 : Blo 342753 345931 := bstep (se 1 (by rfl) ⟨259448, by rfl⟩ : syracuseStep 345931 = 518897) B518897
theorem B345943 : Blo 342753 345943 := bstep (se 1 (by rfl) ⟨259457, by rfl⟩ : syracuseStep 345943 = 518915) B518915
theorem B771929 : Blo 342753 771929 := bstep (se 2 (by rfl) ⟨289473, by rfl⟩ : syracuseStep 771929 = 578947) B578947
theorem B3131237 : Blo 342753 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B345963 : Blo 342753 345963 := bstep (se 1 (by rfl) ⟨259472, by rfl⟩ : syracuseStep 345963 = 518945) B518945
theorem B345975 : Blo 342753 345975 := bstep (se 1 (by rfl) ⟨259481, by rfl⟩ : syracuseStep 345975 = 518963) B518963
theorem B345995 : Blo 342753 345995 := bstep (se 1 (by rfl) ⟨259496, by rfl⟩ : syracuseStep 345995 = 518993) B518993
theorem B346007 : Blo 342753 346007 := bstep (se 1 (by rfl) ⟨259505, by rfl⟩ : syracuseStep 346007 = 519011) B519011
theorem B346027 : Blo 342753 346027 := bstep (se 1 (by rfl) ⟨259520, by rfl⟩ : syracuseStep 346027 = 519041) B519041
theorem B772019 : Blo 342753 772019 := bstep (se 1 (by rfl) ⟨579014, by rfl⟩ : syracuseStep 772019 = 1158029) B1158029
theorem B346039 : Blo 342753 346039 := bstep (se 1 (by rfl) ⟨259529, by rfl⟩ : syracuseStep 346039 = 519059) B519059
theorem B346059 : Blo 342753 346059 := bstep (se 1 (by rfl) ⟨259544, by rfl⟩ : syracuseStep 346059 = 519089) B519089
theorem B772055 : Blo 342753 772055 := bstep (se 1 (by rfl) ⟨579041, by rfl⟩ : syracuseStep 772055 = 1158083) B1158083
theorem B346071 : Blo 342753 346071 := bstep (se 1 (by rfl) ⟨259553, by rfl⟩ : syracuseStep 346071 = 519107) B519107
theorem B346091 : Blo 342753 346091 := bstep (se 1 (by rfl) ⟨259568, by rfl⟩ : syracuseStep 346091 = 519137) B519137
theorem B346103 : Blo 342753 346103 := bstep (se 1 (by rfl) ⟨259577, by rfl⟩ : syracuseStep 346103 = 519155) B519155
theorem B346123 : Blo 342753 346123 := bstep (se 1 (by rfl) ⟨259592, by rfl⟩ : syracuseStep 346123 = 519185) B519185
theorem B346135 : Blo 342753 346135 := bstep (se 1 (by rfl) ⟨259601, by rfl⟩ : syracuseStep 346135 = 519203) B519203
theorem B346155 : Blo 342753 346155 := bstep (se 1 (by rfl) ⟨259616, by rfl⟩ : syracuseStep 346155 = 519233) B519233
theorem B346167 : Blo 342753 346167 := bstep (se 1 (by rfl) ⟨259625, by rfl⟩ : syracuseStep 346167 = 519251) B519251
theorem B346187 : Blo 342753 346187 := bstep (se 1 (by rfl) ⟨259640, by rfl⟩ : syracuseStep 346187 = 519281) B519281
theorem B346199 : Blo 342753 346199 := bstep (se 1 (by rfl) ⟨259649, by rfl⟩ : syracuseStep 346199 = 519299) B519299
theorem B346219 : Blo 342753 346219 := bstep (se 1 (by rfl) ⟨259664, by rfl⟩ : syracuseStep 346219 = 519329) B519329
theorem B346231 : Blo 342753 346231 := bstep (se 1 (by rfl) ⟨259673, by rfl⟩ : syracuseStep 346231 = 519347) B519347
theorem B772235 : Blo 342753 772235 := bstep (se 1 (by rfl) ⟨579176, by rfl⟩ : syracuseStep 772235 = 1158353) B1158353
theorem B346251 : Blo 342753 346251 := bstep (se 1 (by rfl) ⟨259688, by rfl⟩ : syracuseStep 346251 = 519377) B519377
theorem B346263 : Blo 342753 346263 := bstep (se 1 (by rfl) ⟨259697, by rfl⟩ : syracuseStep 346263 = 519395) B519395
theorem B346283 : Blo 342753 346283 := bstep (se 1 (by rfl) ⟨259712, by rfl⟩ : syracuseStep 346283 = 519425) B519425
theorem B346295 : Blo 342753 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B772289 : Blo 342753 772289 := bstep (se 2 (by rfl) ⟨289608, by rfl⟩ : syracuseStep 772289 = 579217) B579217
theorem B346315 : Blo 342753 346315 := bstep (se 1 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 346315 = 519473) B519473
theorem B346327 : Blo 342753 346327 := bstep (se 1 (by rfl) ⟨259745, by rfl⟩ : syracuseStep 346327 = 519491) B519491
theorem B1099993 : Blo 342753 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B2869465 : Blo 342753 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B346347 : Blo 342753 346347 := bstep (se 1 (by rfl) ⟨259760, by rfl⟩ : syracuseStep 346347 = 519521) B519521
theorem B346359 : Blo 342753 346359 := bstep (se 1 (by rfl) ⟨259769, by rfl⟩ : syracuseStep 346359 = 519539) B519539
theorem B346379 : Blo 342753 346379 := bstep (se 1 (by rfl) ⟨259784, by rfl⟩ : syracuseStep 346379 = 519569) B519569
theorem B346391 : Blo 342753 346391 := bstep (se 1 (by rfl) ⟨259793, by rfl⟩ : syracuseStep 346391 = 519587) B519587
theorem B346411 : Blo 342753 346411 := bstep (se 1 (by rfl) ⟨259808, by rfl⟩ : syracuseStep 346411 = 519617) B519617
theorem B346423 : Blo 342753 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B1165643 : Blo 342753 1165643 := bstep (se 1 (by rfl) ⟨874232, by rfl⟩ : syracuseStep 1165643 = 1748465) B1748465
theorem B346443 : Blo 342753 346443 := bstep (se 1 (by rfl) ⟨259832, by rfl⟩ : syracuseStep 346443 = 519665) B519665
theorem B346455 : Blo 342753 346455 := bstep (se 1 (by rfl) ⟨259841, by rfl⟩ : syracuseStep 346455 = 519683) B519683
theorem B346475 : Blo 342753 346475 := bstep (se 1 (by rfl) ⟨259856, by rfl⟩ : syracuseStep 346475 = 519713) B519713
theorem B346487 : Blo 342753 346487 := bstep (se 1 (by rfl) ⟨259865, by rfl⟩ : syracuseStep 346487 = 519731) B519731
theorem B346507 : Blo 342753 346507 := bstep (se 1 (by rfl) ⟨259880, by rfl⟩ : syracuseStep 346507 = 519761) B519761
theorem B346519 : Blo 342753 346519 := bstep (se 1 (by rfl) ⟨259889, by rfl⟩ : syracuseStep 346519 = 519779) B519779
theorem B772505 : Blo 342753 772505 := bstep (se 2 (by rfl) ⟨289689, by rfl⟩ : syracuseStep 772505 = 579379) B579379
theorem B346539 : Blo 342753 346539 := bstep (se 1 (by rfl) ⟨259904, by rfl⟩ : syracuseStep 346539 = 519809) B519809
theorem B346551 : Blo 342753 346551 := bstep (se 1 (by rfl) ⟨259913, by rfl⟩ : syracuseStep 346551 = 519827) B519827
theorem B346571 : Blo 342753 346571 := bstep (se 1 (by rfl) ⟨259928, by rfl⟩ : syracuseStep 346571 = 519857) B519857
theorem B346583 : Blo 342753 346583 := bstep (se 1 (by rfl) ⟨259937, by rfl⟩ : syracuseStep 346583 = 519875) B519875
theorem B707033 : Blo 342753 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B346603 : Blo 342753 346603 := bstep (se 1 (by rfl) ⟨259952, by rfl⟩ : syracuseStep 346603 = 519905) B519905
theorem B772595 : Blo 342753 772595 := bstep (se 1 (by rfl) ⟨579446, by rfl⟩ : syracuseStep 772595 = 1158893) B1158893
theorem B346615 : Blo 342753 346615 := bstep (se 1 (by rfl) ⟨259961, by rfl⟩ : syracuseStep 346615 = 519923) B519923
theorem B346635 : Blo 342753 346635 := bstep (se 1 (by rfl) ⟨259976, by rfl⟩ : syracuseStep 346635 = 519953) B519953
theorem B772631 : Blo 342753 772631 := bstep (se 1 (by rfl) ⟨579473, by rfl⟩ : syracuseStep 772631 = 1158947) B1158947
theorem B346647 : Blo 342753 346647 := bstep (se 1 (by rfl) ⟨259985, by rfl⟩ : syracuseStep 346647 = 519971) B519971
theorem B346667 : Blo 342753 346667 := bstep (se 1 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 346667 = 520001) B520001
theorem B346679 : Blo 342753 346679 := bstep (se 1 (by rfl) ⟨260009, by rfl⟩ : syracuseStep 346679 = 520019) B520019
theorem B346699 : Blo 342753 346699 := bstep (se 1 (by rfl) ⟨260024, by rfl⟩ : syracuseStep 346699 = 520049) B520049
theorem B346711 : Blo 342753 346711 := bstep (se 1 (by rfl) ⟨260033, by rfl⟩ : syracuseStep 346711 = 520067) B520067
theorem B1165913 : Blo 342753 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B346731 : Blo 342753 346731 := bstep (se 1 (by rfl) ⟨260048, by rfl⟩ : syracuseStep 346731 = 520097) B520097
theorem B346743 : Blo 342753 346743 := bstep (se 1 (by rfl) ⟨260057, by rfl⟩ : syracuseStep 346743 = 520115) B520115
theorem B772811 : Blo 342753 772811 := bstep (se 1 (by rfl) ⟨579608, by rfl⟩ : syracuseStep 772811 = 1159217) B1159217
theorem B772865 : Blo 342753 772865 := bstep (se 2 (by rfl) ⟨289824, by rfl⟩ : syracuseStep 772865 = 579649) B579649
theorem B936769 : Blo 342753 936769 := bstep (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) B702577
theorem B740249 : Blo 342753 740249 := bstep (se 2 (by rfl) ⟨277593, by rfl⟩ : syracuseStep 740249 = 555187) B555187
theorem B773081 : Blo 342753 773081 := bstep (se 2 (by rfl) ⟨289905, by rfl⟩ : syracuseStep 773081 = 579811) B579811
theorem B773171 : Blo 342753 773171 := bstep (se 1 (by rfl) ⟨579878, by rfl⟩ : syracuseStep 773171 = 1159757) B1159757
theorem B871499 : Blo 342753 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B773207 : Blo 342753 773207 := bstep (se 1 (by rfl) ⟨579905, by rfl⟩ : syracuseStep 773207 = 1159811) B1159811
theorem B773387 : Blo 342753 773387 := bstep (se 1 (by rfl) ⟨580040, by rfl⟩ : syracuseStep 773387 = 1160081) B1160081
theorem B1166615 : Blo 342753 1166615 := bstep (se 1 (by rfl) ⟨874961, by rfl⟩ : syracuseStep 1166615 = 1749923) B1749923
theorem B4443437 : Blo 342753 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B773441 : Blo 342753 773441 := bstep (se 2 (by rfl) ⟨290040, by rfl⟩ : syracuseStep 773441 = 580081) B580081
theorem B773657 : Blo 342753 773657 := bstep (se 2 (by rfl) ⟨290121, by rfl⟩ : syracuseStep 773657 = 580243) B580243
theorem B1101377 : Blo 342753 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B1953355 : Blo 342753 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B773747 : Blo 342753 773747 := bstep (se 1 (by rfl) ⟨580310, by rfl⟩ : syracuseStep 773747 = 1160621) B1160621
theorem B773783 : Blo 342753 773783 := bstep (se 1 (by rfl) ⟨580337, by rfl⟩ : syracuseStep 773783 = 1160675) B1160675
theorem B1167155 : Blo 342753 1167155 := bstep (se 1 (by rfl) ⟨875366, by rfl⟩ : syracuseStep 1167155 = 1750733) B1750733
theorem B773963 : Blo 342753 773963 := bstep (se 1 (by rfl) ⟨580472, by rfl⟩ : syracuseStep 773963 = 1160945) B1160945
theorem B1953629 : Blo 342753 1953629 := bstep (se 3 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 1953629 = 732611) B732611
theorem B774017 : Blo 342753 774017 := bstep (se 2 (by rfl) ⟨290256, by rfl⟩ : syracuseStep 774017 = 580513) B580513
theorem B872471 : Blo 342753 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B1167425 : Blo 342753 1167425 := bstep (se 2 (by rfl) ⟨437784, by rfl⟩ : syracuseStep 1167425 = 875569) B875569
theorem B774233 : Blo 342753 774233 := bstep (se 2 (by rfl) ⟨290337, by rfl⟩ : syracuseStep 774233 = 580675) B580675
theorem B774323 : Blo 342753 774323 := bstep (se 1 (by rfl) ⟨580742, by rfl⟩ : syracuseStep 774323 = 1161485) B1161485
theorem B774359 : Blo 342753 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B1495385 : Blo 342753 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B774539 : Blo 342753 774539 := bstep (se 1 (by rfl) ⟨580904, by rfl⟩ : syracuseStep 774539 = 1161809) B1161809
theorem B774593 : Blo 342753 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B6279697 : Blo 342753 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B1167965 : Blo 342753 1167965 := bstep (se 3 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 1167965 = 437987) B437987
theorem B348791 : Blo 342753 348791 := bstep (se 1 (by rfl) ⟨261593, by rfl⟩ : syracuseStep 348791 = 523187) B523187
theorem B1659523 : Blo 342753 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B774809 : Blo 342753 774809 := bstep (se 2 (by rfl) ⟨290553, by rfl⟩ : syracuseStep 774809 = 581107) B581107
theorem B873139 : Blo 342753 873139 := bstep (se 1 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 873139 = 1309709) B1309709
theorem B1462963 : Blo 342753 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B840385 : Blo 342753 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B5558989 : Blo 342753 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B774899 : Blo 342753 774899 := bstep (se 1 (by rfl) ⟨581174, by rfl⟩ : syracuseStep 774899 = 1162349) B1162349
theorem B774935 : Blo 342753 774935 := bstep (se 1 (by rfl) ⟨581201, by rfl⟩ : syracuseStep 774935 = 1162403) B1162403
theorem B873281 : Blo 342753 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B775115 : Blo 342753 775115 := bstep (se 1 (by rfl) ⟨581336, by rfl⟩ : syracuseStep 775115 = 1162673) B1162673
theorem B775169 : Blo 342753 775169 := bstep (se 2 (by rfl) ⟨290688, by rfl⟩ : syracuseStep 775169 = 581377) B581377
theorem B578711 : Blo 342753 578711 := bstep (se 1 (by rfl) ⟨434033, by rfl⟩ : syracuseStep 578711 = 868067) B868067
theorem B775385 : Blo 342753 775385 := bstep (se 2 (by rfl) ⟨290769, by rfl⟩ : syracuseStep 775385 = 581539) B581539
theorem B578839 : Blo 342753 578839 := bstep (se 1 (by rfl) ⟨434129, by rfl⟩ : syracuseStep 578839 = 868259) B868259
theorem B775475 : Blo 342753 775475 := bstep (se 1 (by rfl) ⟨581606, by rfl⟩ : syracuseStep 775475 = 1163213) B1163213
theorem B775511 : Blo 342753 775511 := bstep (se 1 (by rfl) ⟨581633, by rfl⟩ : syracuseStep 775511 = 1163267) B1163267
theorem B775691 : Blo 342753 775691 := bstep (se 1 (by rfl) ⟨581768, by rfl⟩ : syracuseStep 775691 = 1163537) B1163537
theorem B775745 : Blo 342753 775745 := bstep (se 2 (by rfl) ⟨290904, by rfl⟩ : syracuseStep 775745 = 581809) B581809
theorem B448087 : Blo 342753 448087 := bstep (se 1 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 448087 = 672131) B672131
theorem B1594973 : Blo 342753 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B1169099 : Blo 342753 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B1103581 : Blo 342753 1103581 := bstep (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) B413843
theorem B775961 : Blo 342753 775961 := bstep (se 2 (by rfl) ⟨290985, by rfl⟩ : syracuseStep 775961 = 581971) B581971
theorem B776051 : Blo 342753 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B579467 : Blo 342753 579467 := bstep (se 1 (by rfl) ⟨434600, by rfl⟩ : syracuseStep 579467 = 869201) B869201
theorem B1857431 : Blo 342753 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B776087 : Blo 342753 776087 := bstep (se 1 (by rfl) ⟨582065, by rfl⟩ : syracuseStep 776087 = 1164131) B1164131
theorem B5593049 : Blo 342753 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B1169369 : Blo 342753 1169369 := bstep (se 2 (by rfl) ⟨438513, by rfl⟩ : syracuseStep 1169369 = 877027) B877027
theorem B579595 : Blo 342753 579595 := bstep (se 1 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 579595 = 869393) B869393
theorem B3299363 : Blo 342753 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B874547 : Blo 342753 874547 := bstep (se 1 (by rfl) ⟨655910, by rfl⟩ : syracuseStep 874547 = 1311821) B1311821
theorem B776267 : Blo 342753 776267 := bstep (se 1 (by rfl) ⟨582200, by rfl⟩ : syracuseStep 776267 = 1164401) B1164401
theorem B776321 : Blo 342753 776321 := bstep (se 2 (by rfl) ⟨291120, by rfl⟩ : syracuseStep 776321 = 582241) B582241
theorem B514187 : Blo 342753 514187 := bstep (se 1 (by rfl) ⟨385640, by rfl⟩ : syracuseStep 514187 = 771281) B771281
theorem B514199 : Blo 342753 514199 := bstep (se 1 (by rfl) ⟨385649, by rfl⟩ : syracuseStep 514199 = 771299) B771299
theorem B579737 : Blo 342753 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B514265 : Blo 342753 514265 := bstep (se 2 (by rfl) ⟨192849, by rfl⟩ : syracuseStep 514265 = 385699) B385699
theorem B579865 : Blo 342753 579865 := bstep (se 2 (by rfl) ⟨217449, by rfl⟩ : syracuseStep 579865 = 434899) B434899
theorem B514379 : Blo 342753 514379 := bstep (se 1 (by rfl) ⟨385784, by rfl⟩ : syracuseStep 514379 = 771569) B771569
theorem B514391 : Blo 342753 514391 := bstep (se 1 (by rfl) ⟨385793, by rfl⟩ : syracuseStep 514391 = 771587) B771587
theorem B350551 : Blo 342753 350551 := bstep (se 1 (by rfl) ⟨262913, by rfl⟩ : syracuseStep 350551 = 525827) B525827
theorem B776537 : Blo 342753 776537 := bstep (se 2 (by rfl) ⟨291201, by rfl⟩ : syracuseStep 776537 = 582403) B582403
theorem B1497475 : Blo 342753 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B514457 : Blo 342753 514457 := bstep (se 2 (by rfl) ⟨192921, by rfl⟩ : syracuseStep 514457 = 385843) B385843
theorem B776627 : Blo 342753 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B776663 : Blo 342753 776663 := bstep (se 1 (by rfl) ⟨582497, by rfl⟩ : syracuseStep 776663 = 1164995) B1164995
theorem B514571 : Blo 342753 514571 := bstep (se 1 (by rfl) ⟨385928, by rfl⟩ : syracuseStep 514571 = 771857) B771857
theorem B514583 : Blo 342753 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B875083 : Blo 342753 875083 := bstep (se 1 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 875083 = 1312625) B1312625
theorem B514649 : Blo 342753 514649 := bstep (se 2 (by rfl) ⟨192993, by rfl⟩ : syracuseStep 514649 = 385987) B385987
theorem B776843 : Blo 342753 776843 := bstep (se 1 (by rfl) ⟨582632, by rfl⟩ : syracuseStep 776843 = 1165265) B1165265
theorem B1170071 : Blo 342753 1170071 := bstep (se 1 (by rfl) ⟨877553, by rfl⟩ : syracuseStep 1170071 = 1755107) B1755107
theorem B776897 : Blo 342753 776897 := bstep (se 2 (by rfl) ⟨291336, by rfl⟩ : syracuseStep 776897 = 582673) B582673
theorem B514763 : Blo 342753 514763 := bstep (se 1 (by rfl) ⟨386072, by rfl⟩ : syracuseStep 514763 = 772145) B772145
theorem B514775 : Blo 342753 514775 := bstep (se 1 (by rfl) ⟨386081, by rfl⟩ : syracuseStep 514775 = 772163) B772163
theorem B875225 : Blo 342753 875225 := bstep (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) B656419
theorem B514841 : Blo 342753 514841 := bstep (se 2 (by rfl) ⟨193065, by rfl⟩ : syracuseStep 514841 = 386131) B386131
theorem B580439 : Blo 342753 580439 := bstep (se 1 (by rfl) ⟨435329, by rfl⟩ : syracuseStep 580439 = 870659) B870659
theorem B514955 : Blo 342753 514955 := bstep (se 1 (by rfl) ⟨386216, by rfl⟩ : syracuseStep 514955 = 772433) B772433
theorem B514967 : Blo 342753 514967 := bstep (se 1 (by rfl) ⟨386225, by rfl⟩ : syracuseStep 514967 = 772451) B772451
theorem B777113 : Blo 342753 777113 := bstep (se 2 (by rfl) ⟨291417, by rfl⟩ : syracuseStep 777113 = 582835) B582835
theorem B580567 : Blo 342753 580567 := bstep (se 1 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 580567 = 870851) B870851
theorem B515033 : Blo 342753 515033 := bstep (se 2 (by rfl) ⟨193137, by rfl⟩ : syracuseStep 515033 = 386275) B386275
theorem B777203 : Blo 342753 777203 := bstep (se 1 (by rfl) ⟨582902, by rfl⟩ : syracuseStep 777203 = 1165805) B1165805
theorem B777239 : Blo 342753 777239 := bstep (se 1 (by rfl) ⟨582929, by rfl⟩ : syracuseStep 777239 = 1165859) B1165859
theorem B515147 : Blo 342753 515147 := bstep (se 1 (by rfl) ⟨386360, by rfl⟩ : syracuseStep 515147 = 772721) B772721
theorem B515159 : Blo 342753 515159 := bstep (se 1 (by rfl) ⟨386369, by rfl⟩ : syracuseStep 515159 = 772739) B772739
theorem B515225 : Blo 342753 515225 := bstep (se 2 (by rfl) ⟨193209, by rfl⟩ : syracuseStep 515225 = 386419) B386419
theorem B777419 : Blo 342753 777419 := bstep (se 1 (by rfl) ⟨583064, by rfl⟩ : syracuseStep 777419 = 1166129) B1166129
theorem B777473 : Blo 342753 777473 := bstep (se 2 (by rfl) ⟨291552, by rfl⟩ : syracuseStep 777473 = 583105) B583105
theorem B515339 : Blo 342753 515339 := bstep (se 1 (by rfl) ⟨386504, by rfl⟩ : syracuseStep 515339 = 773009) B773009
theorem B515351 : Blo 342753 515351 := bstep (se 1 (by rfl) ⟨386513, by rfl⟩ : syracuseStep 515351 = 773027) B773027
theorem B1400129 : Blo 342753 1400129 := bstep (se 2 (by rfl) ⟨525048, by rfl⟩ : syracuseStep 1400129 = 1050097) B1050097
theorem B515417 : Blo 342753 515417 := bstep (se 2 (by rfl) ⟨193281, by rfl⟩ : syracuseStep 515417 = 386563) B386563
theorem B1301933 : Blo 342753 1301933 := bstep (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) B488225
theorem B515531 : Blo 342753 515531 := bstep (se 1 (by rfl) ⟨386648, by rfl⟩ : syracuseStep 515531 = 773297) B773297
theorem B515543 : Blo 342753 515543 := bstep (se 1 (by rfl) ⟨386657, by rfl⟩ : syracuseStep 515543 = 773315) B773315
theorem B777689 : Blo 342753 777689 := bstep (se 2 (by rfl) ⟨291633, by rfl⟩ : syracuseStep 777689 = 583267) B583267
theorem B2940421 : Blo 342753 2940421 := bstep (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) B551329
theorem B5856785 : Blo 342753 5856785 := bstep (se 2 (by rfl) ⟨2196294, by rfl⟩ : syracuseStep 5856785 = 4392589) B4392589
theorem B876055 : Blo 342753 876055 := bstep (se 1 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 876055 = 1314083) B1314083
theorem B515609 : Blo 342753 515609 := bstep (se 2 (by rfl) ⟨193353, by rfl⟩ : syracuseStep 515609 = 386707) B386707
theorem B777779 : Blo 342753 777779 := bstep (se 1 (by rfl) ⟨583334, by rfl⟩ : syracuseStep 777779 = 1166669) B1166669
theorem B581195 : Blo 342753 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B777815 : Blo 342753 777815 := bstep (se 1 (by rfl) ⟨583361, by rfl⟩ : syracuseStep 777815 = 1166723) B1166723
theorem B515723 : Blo 342753 515723 := bstep (se 1 (by rfl) ⟨386792, by rfl⟩ : syracuseStep 515723 = 773585) B773585
theorem B515735 : Blo 342753 515735 := bstep (se 1 (by rfl) ⟨386801, by rfl⟩ : syracuseStep 515735 = 773603) B773603
theorem B581323 : Blo 342753 581323 := bstep (se 1 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 581323 = 871985) B871985
theorem B515801 : Blo 342753 515801 := bstep (se 2 (by rfl) ⟨193425, by rfl⟩ : syracuseStep 515801 = 386851) B386851
theorem B777995 : Blo 342753 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B778049 : Blo 342753 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B515915 : Blo 342753 515915 := bstep (se 1 (by rfl) ⟨386936, by rfl⟩ : syracuseStep 515915 = 773873) B773873
theorem B515927 : Blo 342753 515927 := bstep (se 1 (by rfl) ⟨386945, by rfl⟩ : syracuseStep 515927 = 773891) B773891
theorem B581465 : Blo 342753 581465 := bstep (se 2 (by rfl) ⟨218049, by rfl⟩ : syracuseStep 581465 = 436099) B436099
theorem B515993 : Blo 342753 515993 := bstep (se 2 (by rfl) ⟨193497, by rfl⟩ : syracuseStep 515993 = 386995) B386995
theorem B1761203 : Blo 342753 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B876491 : Blo 342753 876491 := bstep (se 1 (by rfl) ⟨657368, by rfl⟩ : syracuseStep 876491 = 1314737) B1314737
theorem B581593 : Blo 342753 581593 := bstep (se 2 (by rfl) ⟨218097, by rfl⟩ : syracuseStep 581593 = 436195) B436195
theorem B1368029 : Blo 342753 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B516107 : Blo 342753 516107 := bstep (se 1 (by rfl) ⟨387080, by rfl⟩ : syracuseStep 516107 = 774161) B774161
theorem B516119 : Blo 342753 516119 := bstep (se 1 (by rfl) ⟨387089, by rfl⟩ : syracuseStep 516119 = 774179) B774179
theorem B778265 : Blo 342753 778265 := bstep (se 2 (by rfl) ⟨291849, by rfl⟩ : syracuseStep 778265 = 583699) B583699
theorem B516185 : Blo 342753 516185 := bstep (se 2 (by rfl) ⟨193569, by rfl⟩ : syracuseStep 516185 = 387139) B387139
theorem B778355 : Blo 342753 778355 := bstep (se 1 (by rfl) ⟨583766, by rfl⟩ : syracuseStep 778355 = 1167533) B1167533
theorem B778391 : Blo 342753 778391 := bstep (se 1 (by rfl) ⟨583793, by rfl⟩ : syracuseStep 778391 = 1167587) B1167587
theorem B516299 : Blo 342753 516299 := bstep (se 1 (by rfl) ⟨387224, by rfl⟩ : syracuseStep 516299 = 774449) B774449
theorem B516311 : Blo 342753 516311 := bstep (se 1 (by rfl) ⟨387233, by rfl⟩ : syracuseStep 516311 = 774467) B774467
theorem B516377 : Blo 342753 516377 := bstep (se 2 (by rfl) ⟨193641, by rfl⟩ : syracuseStep 516377 = 387283) B387283
theorem B1401133 : Blo 342753 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B876865 : Blo 342753 876865 := bstep (se 2 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 876865 = 657649) B657649
theorem B778571 : Blo 342753 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B8348021 : Blo 342753 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B778625 : Blo 342753 778625 := bstep (se 2 (by rfl) ⟨291984, by rfl⟩ : syracuseStep 778625 = 583969) B583969
theorem B516491 : Blo 342753 516491 := bstep (se 1 (by rfl) ⟨387368, by rfl⟩ : syracuseStep 516491 = 774737) B774737
theorem B516503 : Blo 342753 516503 := bstep (se 1 (by rfl) ⟨387377, by rfl⟩ : syracuseStep 516503 = 774755) B774755
theorem B516569 : Blo 342753 516569 := bstep (se 2 (by rfl) ⟨193713, by rfl⟩ : syracuseStep 516569 = 387427) B387427
theorem B582167 : Blo 342753 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B516683 : Blo 342753 516683 := bstep (se 1 (by rfl) ⟨387512, by rfl⟩ : syracuseStep 516683 = 775025) B775025
theorem B516695 : Blo 342753 516695 := bstep (se 1 (by rfl) ⟨387521, by rfl⟩ : syracuseStep 516695 = 775043) B775043
theorem B778841 : Blo 342753 778841 := bstep (se 2 (by rfl) ⟨292065, by rfl⟩ : syracuseStep 778841 = 584131) B584131
theorem B582295 : Blo 342753 582295 := bstep (se 1 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 582295 = 873443) B873443
theorem B2220695 : Blo 342753 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B516761 : Blo 342753 516761 := bstep (se 2 (by rfl) ⟨193785, by rfl⟩ : syracuseStep 516761 = 387571) B387571
theorem B778931 : Blo 342753 778931 := bstep (se 1 (by rfl) ⟨584198, by rfl⟩ : syracuseStep 778931 = 1168397) B1168397
theorem B778967 : Blo 342753 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B385771 : Blo 342753 385771 := bstep (se 1 (by rfl) ⟨289328, by rfl⟩ : syracuseStep 385771 = 578657) B578657
theorem B516875 : Blo 342753 516875 := bstep (se 1 (by rfl) ⟨387656, by rfl⟩ : syracuseStep 516875 = 775313) B775313
theorem B516887 : Blo 342753 516887 := bstep (se 1 (by rfl) ⟨387665, by rfl⟩ : syracuseStep 516887 = 775331) B775331
theorem B1303361 : Blo 342753 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B2810699 : Blo 342753 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B385879 : Blo 342753 385879 := bstep (se 1 (by rfl) ⟨289409, by rfl⟩ : syracuseStep 385879 = 578819) B578819
theorem B516953 : Blo 342753 516953 := bstep (se 2 (by rfl) ⟨193857, by rfl⟩ : syracuseStep 516953 = 387715) B387715
theorem B779147 : Blo 342753 779147 := bstep (se 1 (by rfl) ⟨584360, by rfl⟩ : syracuseStep 779147 = 1168721) B1168721
theorem B877463 : Blo 342753 877463 := bstep (se 1 (by rfl) ⟨658097, by rfl⟩ : syracuseStep 877463 = 1316195) B1316195
theorem B2614193 : Blo 342753 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B779201 : Blo 342753 779201 := bstep (se 2 (by rfl) ⟨292200, by rfl⟩ : syracuseStep 779201 = 584401) B584401
theorem B517067 : Blo 342753 517067 := bstep (se 1 (by rfl) ⟨387800, by rfl⟩ : syracuseStep 517067 = 775601) B775601
theorem B517079 : Blo 342753 517079 := bstep (se 1 (by rfl) ⟨387809, by rfl⟩ : syracuseStep 517079 = 775619) B775619
theorem B386059 : Blo 342753 386059 := bstep (se 1 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 386059 = 579089) B579089
theorem B1467409 : Blo 342753 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B517145 : Blo 342753 517145 := bstep (se 2 (by rfl) ⟨193929, by rfl⟩ : syracuseStep 517145 = 387859) B387859
theorem B1959005 : Blo 342753 1959005 := bstep (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) B734627
theorem B386167 : Blo 342753 386167 := bstep (se 1 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 386167 = 579251) B579251
theorem B5563523 : Blo 342753 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B517259 : Blo 342753 517259 := bstep (se 1 (by rfl) ⟨387944, by rfl⟩ : syracuseStep 517259 = 775889) B775889
theorem B517271 : Blo 342753 517271 := bstep (se 1 (by rfl) ⟨387953, by rfl⟩ : syracuseStep 517271 = 775907) B775907
theorem B779417 : Blo 342753 779417 := bstep (se 2 (by rfl) ⟨292281, by rfl⟩ : syracuseStep 779417 = 584563) B584563
theorem B517337 : Blo 342753 517337 := bstep (se 2 (by rfl) ⟨194001, by rfl⟩ : syracuseStep 517337 = 388003) B388003
theorem B779507 : Blo 342753 779507 := bstep (se 1 (by rfl) ⟨584630, by rfl⟩ : syracuseStep 779507 = 1169261) B1169261
theorem B582923 : Blo 342753 582923 := bstep (se 1 (by rfl) ⟨437192, by rfl⟩ : syracuseStep 582923 = 874385) B874385
theorem B779543 : Blo 342753 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B386347 : Blo 342753 386347 := bstep (se 1 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 386347 = 579521) B579521
theorem B517451 : Blo 342753 517451 := bstep (se 1 (by rfl) ⟨388088, by rfl⟩ : syracuseStep 517451 = 776177) B776177
theorem B517463 : Blo 342753 517463 := bstep (se 1 (by rfl) ⟨388097, by rfl⟩ : syracuseStep 517463 = 776195) B776195
theorem B583051 : Blo 342753 583051 := bstep (se 1 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 583051 = 874577) B874577
theorem B386455 : Blo 342753 386455 := bstep (se 1 (by rfl) ⟨289841, by rfl⟩ : syracuseStep 386455 = 579683) B579683
theorem B2614679 : Blo 342753 2614679 := bstep (se 1 (by rfl) ⟨1961009, by rfl⟩ : syracuseStep 2614679 = 3922019) B3922019
theorem B517529 : Blo 342753 517529 := bstep (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) B388147
theorem B2352563 : Blo 342753 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B2483635 : Blo 342753 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B779723 : Blo 342753 779723 := bstep (se 1 (by rfl) ⟨584792, by rfl⟩ : syracuseStep 779723 = 1169585) B1169585
theorem B779777 : Blo 342753 779777 := bstep (se 2 (by rfl) ⟨292416, by rfl⟩ : syracuseStep 779777 = 584833) B584833
theorem B517643 : Blo 342753 517643 := bstep (se 1 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 517643 = 776465) B776465
theorem B6743569 : Blo 342753 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B517655 : Blo 342753 517655 := bstep (se 1 (by rfl) ⟨388241, by rfl⟩ : syracuseStep 517655 = 776483) B776483
theorem B583193 : Blo 342753 583193 := bstep (se 2 (by rfl) ⟨218697, by rfl⟩ : syracuseStep 583193 = 437395) B437395
theorem B1009217 : Blo 342753 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B386635 : Blo 342753 386635 := bstep (se 1 (by rfl) ⟨289976, by rfl⟩ : syracuseStep 386635 = 579953) B579953
theorem B517721 : Blo 342753 517721 := bstep (se 2 (by rfl) ⟨194145, by rfl⟩ : syracuseStep 517721 = 388291) B388291
theorem B583321 : Blo 342753 583321 := bstep (se 2 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 583321 = 437491) B437491
theorem B386743 : Blo 342753 386743 := bstep (se 1 (by rfl) ⟨290057, by rfl⟩ : syracuseStep 386743 = 580115) B580115
theorem B517835 : Blo 342753 517835 := bstep (se 1 (by rfl) ⟨388376, by rfl⟩ : syracuseStep 517835 = 776753) B776753
theorem B517847 : Blo 342753 517847 := bstep (se 1 (by rfl) ⟨388385, by rfl⟩ : syracuseStep 517847 = 776771) B776771
theorem B779993 : Blo 342753 779993 := bstep (se 2 (by rfl) ⟨292497, by rfl⟩ : syracuseStep 779993 = 584995) B584995
theorem B517913 : Blo 342753 517913 := bstep (se 2 (by rfl) ⟨194217, by rfl⟩ : syracuseStep 517913 = 388435) B388435
theorem B780083 : Blo 342753 780083 := bstep (se 1 (by rfl) ⟨585062, by rfl⟩ : syracuseStep 780083 = 1170125) B1170125
theorem B780119 : Blo 342753 780119 := bstep (se 1 (by rfl) ⟨585089, by rfl⟩ : syracuseStep 780119 = 1170179) B1170179
theorem B386923 : Blo 342753 386923 := bstep (se 1 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 386923 = 580385) B580385
theorem B518027 : Blo 342753 518027 := bstep (se 1 (by rfl) ⟨388520, by rfl⟩ : syracuseStep 518027 = 777041) B777041
theorem B518039 : Blo 342753 518039 := bstep (se 1 (by rfl) ⟨388529, by rfl⟩ : syracuseStep 518039 = 777059) B777059
theorem B387031 : Blo 342753 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B518105 : Blo 342753 518105 := bstep (se 2 (by rfl) ⟨194289, by rfl⟩ : syracuseStep 518105 = 388579) B388579
theorem B5597201 : Blo 342753 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B518219 : Blo 342753 518219 := bstep (se 1 (by rfl) ⟨388664, by rfl⟩ : syracuseStep 518219 = 777329) B777329
theorem B518231 : Blo 342753 518231 := bstep (se 1 (by rfl) ⟨388673, by rfl⟩ : syracuseStep 518231 = 777347) B777347
theorem B387211 : Blo 342753 387211 := bstep (se 1 (by rfl) ⟨290408, by rfl⟩ : syracuseStep 387211 = 580817) B580817
theorem B518297 : Blo 342753 518297 := bstep (se 2 (by rfl) ⟨194361, by rfl⟩ : syracuseStep 518297 = 388723) B388723
theorem B2943155 : Blo 342753 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B583895 : Blo 342753 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B387319 : Blo 342753 387319 := bstep (se 1 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 387319 = 580979) B580979
theorem B518411 : Blo 342753 518411 := bstep (se 1 (by rfl) ⟨388808, by rfl⟩ : syracuseStep 518411 = 777617) B777617
theorem B1304849 : Blo 342753 1304849 := bstep (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) B978637
theorem B518423 : Blo 342753 518423 := bstep (se 1 (by rfl) ⟨388817, by rfl⟩ : syracuseStep 518423 = 777635) B777635
theorem B584023 : Blo 342753 584023 := bstep (se 1 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 584023 = 876035) B876035
theorem B518489 : Blo 342753 518489 := bstep (se 2 (by rfl) ⟨194433, by rfl⟩ : syracuseStep 518489 = 388867) B388867
theorem B387499 : Blo 342753 387499 := bstep (se 1 (by rfl) ⟨290624, by rfl⟩ : syracuseStep 387499 = 581249) B581249
theorem B518603 : Blo 342753 518603 := bstep (se 1 (by rfl) ⟨388952, by rfl⟩ : syracuseStep 518603 = 777905) B777905
theorem B518615 : Blo 342753 518615 := bstep (se 1 (by rfl) ⟨388961, by rfl⟩ : syracuseStep 518615 = 777923) B777923
theorem B1239569 : Blo 342753 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B387607 : Blo 342753 387607 := bstep (se 1 (by rfl) ⟨290705, by rfl⟩ : syracuseStep 387607 = 581411) B581411
theorem B518681 : Blo 342753 518681 := bstep (se 2 (by rfl) ⟨194505, by rfl⟩ : syracuseStep 518681 = 389011) B389011
theorem B518795 : Blo 342753 518795 := bstep (se 1 (by rfl) ⟨389096, by rfl⟩ : syracuseStep 518795 = 778193) B778193
theorem B518807 : Blo 342753 518807 := bstep (se 1 (by rfl) ⟨389105, by rfl⟩ : syracuseStep 518807 = 778211) B778211
theorem B387787 : Blo 342753 387787 := bstep (se 1 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 387787 = 581681) B581681
theorem B1305305 : Blo 342753 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B518873 : Blo 342753 518873 := bstep (se 2 (by rfl) ⟨194577, by rfl⟩ : syracuseStep 518873 = 389155) B389155
theorem B387895 : Blo 342753 387895 := bstep (se 1 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 387895 = 581843) B581843
theorem B518987 : Blo 342753 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B518999 : Blo 342753 518999 := bstep (se 1 (by rfl) ⟨389249, by rfl⟩ : syracuseStep 518999 = 778499) B778499
theorem B519065 : Blo 342753 519065 := bstep (se 2 (by rfl) ⟨194649, by rfl⟩ : syracuseStep 519065 = 389299) B389299
theorem B1305517 : Blo 342753 1305517 := bstep (se 3 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 1305517 = 489569) B489569
theorem B1764275 : Blo 342753 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B584651 : Blo 342753 584651 := bstep (se 1 (by rfl) ⟨438488, by rfl⟩ : syracuseStep 584651 = 876977) B876977
theorem B388075 : Blo 342753 388075 := bstep (se 1 (by rfl) ⟨291056, by rfl⟩ : syracuseStep 388075 = 582113) B582113
theorem B748531 : Blo 342753 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B519179 : Blo 342753 519179 := bstep (se 1 (by rfl) ⟨389384, by rfl⟩ : syracuseStep 519179 = 778769) B778769
theorem B519191 : Blo 342753 519191 := bstep (se 1 (by rfl) ⟨389393, by rfl⟩ : syracuseStep 519191 = 778787) B778787
theorem B1109015 : Blo 342753 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B584779 : Blo 342753 584779 := bstep (se 1 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 584779 = 877169) B877169
theorem B388183 : Blo 342753 388183 := bstep (se 1 (by rfl) ⟨291137, by rfl⟩ : syracuseStep 388183 = 582275) B582275
theorem B519257 : Blo 342753 519257 := bstep (se 2 (by rfl) ⟨194721, by rfl⟩ : syracuseStep 519257 = 389443) B389443
theorem B1109143 : Blo 342753 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B519371 : Blo 342753 519371 := bstep (se 1 (by rfl) ⟨389528, by rfl⟩ : syracuseStep 519371 = 779057) B779057
theorem B519383 : Blo 342753 519383 := bstep (se 1 (by rfl) ⟨389537, by rfl⟩ : syracuseStep 519383 = 779075) B779075
theorem B584921 : Blo 342753 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B1305821 : Blo 342753 1305821 := bstep (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) B489683
theorem B388363 : Blo 342753 388363 := bstep (se 1 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 388363 = 582545) B582545
theorem B519449 : Blo 342753 519449 := bstep (se 2 (by rfl) ⟨194793, by rfl⟩ : syracuseStep 519449 = 389587) B389587
theorem B978227 : Blo 342753 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B1469785 : Blo 342753 1469785 := bstep (se 2 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 1469785 = 1102339) B1102339
theorem B585049 : Blo 342753 585049 := bstep (se 2 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 585049 = 438787) B438787
theorem B388471 : Blo 342753 388471 := bstep (se 1 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 388471 = 582707) B582707
theorem B519563 : Blo 342753 519563 := bstep (se 1 (by rfl) ⟨389672, by rfl⟩ : syracuseStep 519563 = 779345) B779345
theorem B519575 : Blo 342753 519575 := bstep (se 1 (by rfl) ⟨389681, by rfl⟩ : syracuseStep 519575 = 779363) B779363
theorem B749017 : Blo 342753 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 342753 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B519641 : Blo 342753 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B978455 : Blo 342753 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B388651 : Blo 342753 388651 := bstep (se 1 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 388651 = 582977) B582977
theorem B519755 : Blo 342753 519755 := bstep (se 1 (by rfl) ⟨389816, by rfl⟩ : syracuseStep 519755 = 779633) B779633
theorem B519767 : Blo 342753 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B618113 : Blo 342753 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B1961603 : Blo 342753 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B650891 : Blo 342753 650891 := bstep (se 1 (by rfl) ⟨488168, by rfl⟩ : syracuseStep 650891 = 976337) B976337
theorem B388759 : Blo 342753 388759 := bstep (se 1 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 388759 = 583139) B583139
theorem B519833 : Blo 342753 519833 := bstep (se 2 (by rfl) ⟨194937, by rfl⟩ : syracuseStep 519833 = 389875) B389875
theorem B1994419 : Blo 342753 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B519947 : Blo 342753 519947 := bstep (se 1 (by rfl) ⟨389960, by rfl⟩ : syracuseStep 519947 = 779921) B779921
theorem B519959 : Blo 342753 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B651073 : Blo 342753 651073 := bstep (se 2 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 651073 = 488305) B488305
theorem B978763 : Blo 342753 978763 := bstep (se 1 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 978763 = 1468145) B1468145
theorem B388939 : Blo 342753 388939 := bstep (se 1 (by rfl) ⟨291704, by rfl⟩ : syracuseStep 388939 = 583409) B583409
theorem B520025 : Blo 342753 520025 := bstep (se 2 (by rfl) ⟨195009, by rfl⟩ : syracuseStep 520025 = 390019) B390019
theorem B389047 : Blo 342753 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B1044427 : Blo 342753 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B1109963 : Blo 342753 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B2945069 : Blo 342753 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B979037 : Blo 342753 979037 := bstep (se 3 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 979037 = 367139) B367139
theorem B389227 : Blo 342753 389227 := bstep (se 1 (by rfl) ⟨291920, by rfl⟩ : syracuseStep 389227 = 583841) B583841
theorem B618625 : Blo 342753 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B651415 : Blo 342753 651415 := bstep (se 1 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 651415 = 977123) B977123
theorem B389335 : Blo 342753 389335 := bstep (se 1 (by rfl) ⟨292001, by rfl⟩ : syracuseStep 389335 = 584003) B584003
theorem B1470743 : Blo 342753 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B651635 : Blo 342753 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B389515 : Blo 342753 389515 := bstep (se 1 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 389515 = 584273) B584273
theorem B389623 : Blo 342753 389623 := bstep (se 1 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 389623 = 584435) B584435
theorem B553547 : Blo 342753 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B651863 : Blo 342753 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B553559 : Blo 342753 553559 := bstep (se 1 (by rfl) ⟨415169, by rfl⟩ : syracuseStep 553559 = 830339) B830339
theorem B389803 : Blo 342753 389803 := bstep (se 1 (by rfl) ⟨292352, by rfl⟩ : syracuseStep 389803 = 584705) B584705
theorem B2945753 : Blo 342753 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B389911 : Blo 342753 389911 := bstep (se 1 (by rfl) ⟨292433, by rfl⟩ : syracuseStep 389911 = 584867) B584867
theorem B750401 : Blo 342753 750401 := bstep (se 2 (by rfl) ⟨281400, by rfl⟩ : syracuseStep 750401 = 562801) B562801
theorem B652121 : Blo 342753 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B1242049 : Blo 342753 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B390091 : Blo 342753 390091 := bstep (se 1 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 390091 = 585137) B585137
theorem B652531 : Blo 342753 652531 := bstep (se 1 (by rfl) ⟨489398, by rfl⟩ : syracuseStep 652531 = 978797) B978797
theorem B554251 : Blo 342753 554251 := bstep (se 1 (by rfl) ⟨415688, by rfl⟩ : syracuseStep 554251 = 831377) B831377
theorem B554521 : Blo 342753 554521 := bstep (se 2 (by rfl) ⟨207945, by rfl⟩ : syracuseStep 554521 = 415891) B415891
theorem B1046081 : Blo 342753 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B1242797 : Blo 342753 1242797 := bstep (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) B466049
theorem B653017 : Blo 342753 653017 := bstep (se 2 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 653017 = 489763) B489763
theorem B1308419 : Blo 342753 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B1308433 : Blo 342753 1308433 := bstep (se 2 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 1308433 = 981325) B981325
theorem B554777 : Blo 342753 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B1767233 : Blo 342753 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B1570711 : Blo 342753 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1308737 : Blo 342753 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B981143 : Blo 342753 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B620759 : Blo 342753 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B653579 : Blo 342753 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B1472843 : Blo 342753 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B2881885 : Blo 342753 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B653761 : Blo 342753 653761 := bstep (se 2 (by rfl) ⟨245160, by rfl⟩ : syracuseStep 653761 = 490321) B490321
theorem B7436893 : Blo 342753 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B588505 : Blo 342753 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B1309405 : Blo 342753 1309405 := bstep (se 3 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 1309405 = 491027) B491027
theorem B981953 : Blo 342753 981953 := bstep (se 2 (by rfl) ⟨368232, by rfl⟩ : syracuseStep 981953 = 736465) B736465
theorem B621515 : Blo 342753 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B490583 : Blo 342753 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B654475 : Blo 342753 654475 := bstep (se 1 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 654475 = 981713) B981713
theorem B654551 : Blo 342753 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B392459 : Blo 342753 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B622027 : Blo 342753 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B1736153 : Blo 342753 1736153 := bstep (se 2 (by rfl) ⟨651057, by rfl⟩ : syracuseStep 1736153 = 1302115) B1302115
theorem B622091 : Blo 342753 622091 := bstep (se 1 (by rfl) ⟨466568, by rfl⟩ : syracuseStep 622091 = 933137) B933137
theorem B1048115 : Blo 342753 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B655219 : Blo 342753 655219 := bstep (se 1 (by rfl) ⟨491414, by rfl⟩ : syracuseStep 655219 = 982829) B982829
theorem B1474483 : Blo 342753 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1310681 : Blo 342753 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B1146923 : Blo 342753 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B4259957 : Blo 342753 4259957 := bstep (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) B399371
theorem B983411 : Blo 342753 983411 := bstep (se 1 (by rfl) ⟨737558, by rfl⟩ : syracuseStep 983411 = 1475117) B1475117
theorem B655751 : Blo 342753 655751 := bstep (se 1 (by rfl) ⟨491813, by rfl⟩ : syracuseStep 655751 = 983627) B983627
theorem B1868177 : Blo 342753 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B885259 : Blo 342753 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B1311623 : Blo 342753 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B656275 : Blo 342753 656275 := bstep (se 1 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 656275 = 984413) B984413
theorem B24249419 : Blo 342753 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B492679 : Blo 342753 492679 := bstep (se 1 (by rfl) ⟨369509, by rfl⟩ : syracuseStep 492679 = 739019) B739019
theorem B1049867 : Blo 342753 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B2622941 : Blo 342753 2622941 := bstep (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) B983603
theorem B624161 : Blo 342753 624161 := bstep (se 2 (by rfl) ⟨234060, by rfl⟩ : syracuseStep 624161 = 468121) B468121
theorem B1476157 : Blo 342753 1476157 := bstep (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) B553559
theorem B2361125 : Blo 342753 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B1869605 : Blo 342753 1869605 := bstep (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) B350551
theorem B3311513 : Blo 342753 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B493499 : Blo 342753 493499 := bstep (se 1 (by rfl) ⟨370124, by rfl⟩ : syracuseStep 493499 = 740249) B740249
theorem B657467 : Blo 342753 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B4982957 : Blo 342753 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B657953 : Blo 342753 657953 := bstep (se 2 (by rfl) ⟨246732, by rfl⟩ : syracuseStep 657953 = 493465) B493465
theorem B985871 : Blo 342753 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B658219 : Blo 342753 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B1969667 : Blo 342753 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B13471373 : Blo 342753 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1249025 : Blo 342753 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B1183547 : Blo 342753 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B1740689 : Blo 342753 1740689 := bstep (se 2 (by rfl) ⟨652758, by rfl⟩ : syracuseStep 1740689 = 1305517) B1305517
theorem B2199575 : Blo 342753 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B2789549 : Blo 342753 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B2691245 : Blo 342753 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1478857 : Blo 342753 1478857 := bstep (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) B1109143
theorem B3314125 : Blo 342753 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B2659225 : Blo 342753 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B3904523 : Blo 342753 3904523 := bstep (se 1 (by rfl) ⟨2928392, by rfl⟩ : syracuseStep 3904523 = 5856785) B5856785
theorem B1184887 : Blo 342753 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B824833 : Blo 342753 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1480463 : Blo 342753 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1873799 : Blo 342753 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B792521 : Blo 342753 792521 := bstep (se 2 (by rfl) ⟨297195, by rfl⟩ : syracuseStep 792521 = 594391) B594391
theorem B1742795 : Blo 342753 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B1743119 : Blo 342753 1743119 := bstep (se 1 (by rfl) ⟨1307339, by rfl⟩ : syracuseStep 1743119 = 2614679) B2614679
theorem B7411985 : Blo 342753 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B2038787 : Blo 342753 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B826379 : Blo 342753 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B8068531 : Blo 342753 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B597449 : Blo 342753 597449 := bstep (se 2 (by rfl) ⟨224043, by rfl⟩ : syracuseStep 597449 = 448087) B448087
theorem B1744577 : Blo 342753 1744577 := bstep (se 2 (by rfl) ⟨654216, by rfl⟩ : syracuseStep 1744577 = 1308433) B1308433
theorem B1941185 : Blo 342753 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B433927 : Blo 342753 433927 := bstep (se 1 (by rfl) ⟨325445, by rfl⟩ : syracuseStep 433927 = 650891) B650891
theorem B467087 : Blo 342753 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B434423 : Blo 342753 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B2105689 : Blo 342753 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B369031 : Blo 342753 369031 := bstep (se 1 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 369031 = 553547) B553547
theorem B434575 : Blo 342753 434575 := bstep (se 1 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 434575 = 651863) B651863
theorem B3842513 : Blo 342753 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B500267 : Blo 342753 500267 := bstep (se 1 (by rfl) ⟨375200, by rfl⟩ : syracuseStep 500267 = 750401) B750401
theorem B434747 : Blo 342753 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B1778237 : Blo 342753 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B1745873 : Blo 342753 1745873 := bstep (se 2 (by rfl) ⟨654702, by rfl⟩ : syracuseStep 1745873 = 1309405) B1309405
theorem B2630717 : Blo 342753 2630717 := bstep (se 3 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 2630717 = 986519) B986519
theorem B369851 : Blo 342753 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B3908897 : Blo 342753 3908897 := bstep (se 2 (by rfl) ⟨1465836, by rfl⟩ : syracuseStep 3908897 = 2931673) B2931673
theorem B435719 : Blo 342753 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B927247 : Blo 342753 927247 := bstep (se 1 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 927247 = 1390871) B1390871
theorem B1058333 : Blo 342753 1058333 := bstep (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) B396875
theorem B468623 : Blo 342753 468623 := bstep (se 1 (by rfl) ⟨351467, by rfl⟩ : syracuseStep 468623 = 702935) B702935
theorem B829369 : Blo 342753 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B436367 : Blo 342753 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B1157435 : Blo 342753 1157435 := bstep (se 1 (by rfl) ⟨868076, by rfl⟩ : syracuseStep 1157435 = 1736153) B1736153
theorem B698743 : Blo 342753 698743 := bstep (se 1 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 698743 = 1048115) B1048115
theorem B2959901 : Blo 342753 2959901 := bstep (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) B1109963
theorem B3648077 : Blo 342753 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1157921 : Blo 342753 1157921 := bstep (se 2 (by rfl) ⟨434220, by rfl⟩ : syracuseStep 1157921 = 868441) B868441
theorem B1747979 : Blo 342753 1747979 := bstep (se 1 (by rfl) ⟨1310984, by rfl⟩ : syracuseStep 1747979 = 2621969) B2621969
theorem B928921 : Blo 342753 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B1748141 : Blo 342753 1748141 := bstep (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) B655553
theorem B830753 : Blo 342753 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B1158515 : Blo 342753 1158515 := bstep (se 1 (by rfl) ⟨868886, by rfl⟩ : syracuseStep 1158515 = 1737773) B1737773
theorem B3943889 : Blo 342753 3943889 := bstep (se 2 (by rfl) ⟨1478958, by rfl⟩ : syracuseStep 3943889 = 2957917) B2957917
theorem B3157507 : Blo 342753 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B700535 : Blo 342753 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B3911813 : Blo 342753 3911813 := bstep (se 4 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 3911813 = 733465) B733465
theorem B1814929 : Blo 342753 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B930305 : Blo 342753 930305 := bstep (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) B697729
theorem B8991425 : Blo 342753 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B1749761 : Blo 342753 1749761 := bstep (se 2 (by rfl) ⟨656160, by rfl⟩ : syracuseStep 1749761 = 1312321) B1312321
theorem B2962291 : Blo 342753 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B2241433 : Blo 342753 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B2208779 : Blo 342753 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B1750571 : Blo 342753 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B996923 : Blo 342753 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B1161107 : Blo 342753 1161107 := bstep (se 1 (by rfl) ⟨870830, by rfl⟩ : syracuseStep 1161107 = 1741661) B1741661
theorem B1325117 : Blo 342753 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B1063315 : Blo 342753 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B342791 : Blo 342753 342791 := bstep (se 1 (by rfl) ⟨257093, by rfl⟩ : syracuseStep 342791 = 514187) B514187
theorem B342799 : Blo 342753 342799 := bstep (se 1 (by rfl) ⟨257099, by rfl⟩ : syracuseStep 342799 = 514199) B514199
theorem B342843 : Blo 342753 342843 := bstep (se 1 (by rfl) ⟨257132, by rfl⟩ : syracuseStep 342843 = 514265) B514265
theorem B1751867 : Blo 342753 1751867 := bstep (se 1 (by rfl) ⟨1313900, by rfl⟩ : syracuseStep 1751867 = 2627801) B2627801
theorem B342919 : Blo 342753 342919 := bstep (se 1 (by rfl) ⟨257189, by rfl⟩ : syracuseStep 342919 = 514379) B514379
theorem B342927 : Blo 342753 342927 := bstep (se 1 (by rfl) ⟨257195, by rfl⟩ : syracuseStep 342927 = 514391) B514391
theorem B342971 : Blo 342753 342971 := bstep (se 1 (by rfl) ⟨257228, by rfl⟩ : syracuseStep 342971 = 514457) B514457
theorem B1752029 : Blo 342753 1752029 := bstep (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) B657011
theorem B343047 : Blo 342753 343047 := bstep (se 1 (by rfl) ⟨257285, by rfl⟩ : syracuseStep 343047 = 514571) B514571
theorem B343055 : Blo 342753 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B343099 : Blo 342753 343099 := bstep (se 1 (by rfl) ⟨257324, by rfl⟩ : syracuseStep 343099 = 514649) B514649
theorem B8928317 : Blo 342753 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B343175 : Blo 342753 343175 := bstep (se 1 (by rfl) ⟨257381, by rfl⟩ : syracuseStep 343175 = 514763) B514763
theorem B343183 : Blo 342753 343183 := bstep (se 1 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 343183 = 514775) B514775
theorem B343227 : Blo 342753 343227 := bstep (se 1 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 343227 = 514841) B514841
theorem B343303 : Blo 342753 343303 := bstep (se 1 (by rfl) ⟨257477, by rfl⟩ : syracuseStep 343303 = 514955) B514955
theorem B343311 : Blo 342753 343311 := bstep (se 1 (by rfl) ⟨257483, by rfl⟩ : syracuseStep 343311 = 514967) B514967
theorem B1162511 : Blo 342753 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B998689 : Blo 342753 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B1752353 : Blo 342753 1752353 := bstep (se 2 (by rfl) ⟨657132, by rfl⟩ : syracuseStep 1752353 = 1314265) B1314265
theorem B343355 : Blo 342753 343355 := bstep (se 1 (by rfl) ⟨257516, by rfl⟩ : syracuseStep 343355 = 515033) B515033
theorem B343431 : Blo 342753 343431 := bstep (se 1 (by rfl) ⟨257573, by rfl⟩ : syracuseStep 343431 = 515147) B515147
theorem B343439 : Blo 342753 343439 := bstep (se 1 (by rfl) ⟨257579, by rfl⟩ : syracuseStep 343439 = 515159) B515159
theorem B2604473 : Blo 342753 2604473 := bstep (se 2 (by rfl) ⟨976677, by rfl⟩ : syracuseStep 2604473 = 1953355) B1953355
theorem B343483 : Blo 342753 343483 := bstep (se 1 (by rfl) ⟨257612, by rfl⟩ : syracuseStep 343483 = 515225) B515225
theorem B343559 : Blo 342753 343559 := bstep (se 1 (by rfl) ⟨257669, by rfl⟩ : syracuseStep 343559 = 515339) B515339
theorem B343567 : Blo 342753 343567 := bstep (se 1 (by rfl) ⟨257675, by rfl⟩ : syracuseStep 343567 = 515351) B515351
theorem B1162781 : Blo 342753 1162781 := bstep (se 3 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 1162781 = 436043) B436043
theorem B933419 : Blo 342753 933419 := bstep (se 1 (by rfl) ⟨700064, by rfl⟩ : syracuseStep 933419 = 1400129) B1400129
theorem B343611 : Blo 342753 343611 := bstep (se 1 (by rfl) ⟨257708, by rfl⟩ : syracuseStep 343611 = 515417) B515417
theorem B867955 : Blo 342753 867955 := bstep (se 1 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 867955 = 1301933) B1301933
theorem B343687 : Blo 342753 343687 := bstep (se 1 (by rfl) ⟨257765, by rfl⟩ : syracuseStep 343687 = 515531) B515531
theorem B343695 : Blo 342753 343695 := bstep (se 1 (by rfl) ⟨257771, by rfl⟩ : syracuseStep 343695 = 515543) B515543
theorem B6602417 : Blo 342753 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B343739 : Blo 342753 343739 := bstep (se 1 (by rfl) ⟨257804, by rfl⟩ : syracuseStep 343739 = 515609) B515609
theorem B868097 : Blo 342753 868097 := bstep (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) B651073
theorem B343815 : Blo 342753 343815 := bstep (se 1 (by rfl) ⟨257861, by rfl⟩ : syracuseStep 343815 = 515723) B515723
theorem B343823 : Blo 342753 343823 := bstep (se 1 (by rfl) ⟨257867, by rfl⟩ : syracuseStep 343823 = 515735) B515735
theorem B343867 : Blo 342753 343867 := bstep (se 1 (by rfl) ⟨257900, by rfl⟩ : syracuseStep 343867 = 515801) B515801
theorem B343943 : Blo 342753 343943 := bstep (se 1 (by rfl) ⟨257957, by rfl⟩ : syracuseStep 343943 = 515915) B515915
theorem B343951 : Blo 342753 343951 := bstep (se 1 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 343951 = 515927) B515927
theorem B1392569 : Blo 342753 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B343995 : Blo 342753 343995 := bstep (se 1 (by rfl) ⟨257996, by rfl⟩ : syracuseStep 343995 = 515993) B515993
theorem B344071 : Blo 342753 344071 := bstep (se 1 (by rfl) ⟨258053, by rfl⟩ : syracuseStep 344071 = 516107) B516107
theorem B344079 : Blo 342753 344079 := bstep (se 1 (by rfl) ⟨258059, by rfl⟩ : syracuseStep 344079 = 516119) B516119
theorem B344123 : Blo 342753 344123 := bstep (se 1 (by rfl) ⟨258092, by rfl⟩ : syracuseStep 344123 = 516185) B516185
theorem B344199 : Blo 342753 344199 := bstep (se 1 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 344199 = 516299) B516299
theorem B344207 : Blo 342753 344207 := bstep (se 1 (by rfl) ⟨258155, by rfl⟩ : syracuseStep 344207 = 516311) B516311
theorem B344251 : Blo 342753 344251 := bstep (se 1 (by rfl) ⟨258188, by rfl⟩ : syracuseStep 344251 = 516377) B516377
theorem B868553 : Blo 342753 868553 := bstep (se 2 (by rfl) ⟨325707, by rfl⟩ : syracuseStep 868553 = 651415) B651415
theorem B1753325 : Blo 342753 1753325 := bstep (se 3 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 1753325 = 657497) B657497
theorem B344327 : Blo 342753 344327 := bstep (se 1 (by rfl) ⟨258245, by rfl⟩ : syracuseStep 344327 = 516491) B516491
theorem B344335 : Blo 342753 344335 := bstep (se 1 (by rfl) ⟨258251, by rfl⟩ : syracuseStep 344335 = 516503) B516503
theorem B344379 : Blo 342753 344379 := bstep (se 1 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 344379 = 516569) B516569
theorem B344455 : Blo 342753 344455 := bstep (se 1 (by rfl) ⟨258341, by rfl⟩ : syracuseStep 344455 = 516683) B516683
theorem B344463 : Blo 342753 344463 := bstep (se 1 (by rfl) ⟨258347, by rfl⟩ : syracuseStep 344463 = 516695) B516695
theorem B1098137 : Blo 342753 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B344507 : Blo 342753 344507 := bstep (se 1 (by rfl) ⟨258380, by rfl⟩ : syracuseStep 344507 = 516761) B516761
theorem B344583 : Blo 342753 344583 := bstep (se 1 (by rfl) ⟨258437, by rfl⟩ : syracuseStep 344583 = 516875) B516875
theorem B1098251 : Blo 342753 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B344591 : Blo 342753 344591 := bstep (se 1 (by rfl) ⟨258443, by rfl⟩ : syracuseStep 344591 = 516887) B516887
theorem B868907 : Blo 342753 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B344635 : Blo 342753 344635 := bstep (se 1 (by rfl) ⟨258476, by rfl⟩ : syracuseStep 344635 = 516953) B516953
theorem B344711 : Blo 342753 344711 := bstep (se 1 (by rfl) ⟨258533, by rfl⟩ : syracuseStep 344711 = 517067) B517067
theorem B344719 : Blo 342753 344719 := bstep (se 1 (by rfl) ⟨258539, by rfl⟩ : syracuseStep 344719 = 517079) B517079
theorem B344763 : Blo 342753 344763 := bstep (se 1 (by rfl) ⟨258572, by rfl⟩ : syracuseStep 344763 = 517145) B517145
theorem B8372929 : Blo 342753 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B344839 : Blo 342753 344839 := bstep (se 1 (by rfl) ⟨258629, by rfl⟩ : syracuseStep 344839 = 517259) B517259
theorem B344847 : Blo 342753 344847 := bstep (se 1 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 344847 = 517271) B517271
theorem B344891 : Blo 342753 344891 := bstep (se 1 (by rfl) ⟨258668, by rfl⟩ : syracuseStep 344891 = 517337) B517337
theorem B2212697 : Blo 342753 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B344967 : Blo 342753 344967 := bstep (se 1 (by rfl) ⟨258725, by rfl⟩ : syracuseStep 344967 = 517451) B517451
theorem B344975 : Blo 342753 344975 := bstep (se 1 (by rfl) ⟨258731, by rfl⟩ : syracuseStep 344975 = 517463) B517463
theorem B2933657 : Blo 342753 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1164185 : Blo 342753 1164185 := bstep (se 2 (by rfl) ⟨436569, by rfl⟩ : syracuseStep 1164185 = 873139) B873139
theorem B1950617 : Blo 342753 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B345019 : Blo 342753 345019 := bstep (se 1 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 345019 = 517529) B517529
theorem B345095 : Blo 342753 345095 := bstep (se 1 (by rfl) ⟨258821, by rfl⟩ : syracuseStep 345095 = 517643) B517643
theorem B345103 : Blo 342753 345103 := bstep (se 1 (by rfl) ⟨258827, by rfl⟩ : syracuseStep 345103 = 517655) B517655
theorem B1754135 : Blo 342753 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B345147 : Blo 342753 345147 := bstep (se 1 (by rfl) ⟨258860, by rfl⟩ : syracuseStep 345147 = 517721) B517721
theorem B345223 : Blo 342753 345223 := bstep (se 1 (by rfl) ⟨258917, by rfl⟩ : syracuseStep 345223 = 517835) B517835
theorem B345231 : Blo 342753 345231 := bstep (se 1 (by rfl) ⟨258923, by rfl⟩ : syracuseStep 345231 = 517847) B517847
theorem B345275 : Blo 342753 345275 := bstep (se 1 (by rfl) ⟨258956, by rfl⟩ : syracuseStep 345275 = 517913) B517913
theorem B1885421 : Blo 342753 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B3720437 : Blo 342753 3720437 := bstep (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) B348791
theorem B4211957 : Blo 342753 4211957 := bstep (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) B394871
theorem B1656065 : Blo 342753 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B345351 : Blo 342753 345351 := bstep (se 1 (by rfl) ⟨259013, by rfl⟩ : syracuseStep 345351 = 518027) B518027
theorem B345359 : Blo 342753 345359 := bstep (se 1 (by rfl) ⟨259019, by rfl⟩ : syracuseStep 345359 = 518039) B518039
theorem B771371 : Blo 342753 771371 := bstep (se 1 (by rfl) ⟨578528, by rfl⟩ : syracuseStep 771371 = 1157057) B1157057
theorem B345403 : Blo 342753 345403 := bstep (se 1 (by rfl) ⟨259052, by rfl⟩ : syracuseStep 345403 = 518105) B518105
theorem B345479 : Blo 342753 345479 := bstep (se 1 (by rfl) ⟨259109, by rfl⟩ : syracuseStep 345479 = 518219) B518219
theorem B345487 : Blo 342753 345487 := bstep (se 1 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 345487 = 518231) B518231
theorem B345531 : Blo 342753 345531 := bstep (se 1 (by rfl) ⟨259148, by rfl⟩ : syracuseStep 345531 = 518297) B518297
theorem B345607 : Blo 342753 345607 := bstep (se 1 (by rfl) ⟨259205, by rfl⟩ : syracuseStep 345607 = 518411) B518411
theorem B869899 : Blo 342753 869899 := bstep (se 1 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 869899 = 1304849) B1304849
theorem B509455 : Blo 342753 509455 := bstep (se 1 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 509455 = 764183) B764183
theorem B345615 : Blo 342753 345615 := bstep (se 1 (by rfl) ⟨259211, by rfl⟩ : syracuseStep 345615 = 518423) B518423
theorem B345659 : Blo 342753 345659 := bstep (se 1 (by rfl) ⟨259244, by rfl⟩ : syracuseStep 345659 = 518489) B518489
theorem B1164887 : Blo 342753 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B345735 : Blo 342753 345735 := bstep (se 1 (by rfl) ⟨259301, by rfl⟩ : syracuseStep 345735 = 518603) B518603
theorem B345743 : Blo 342753 345743 := bstep (se 1 (by rfl) ⟨259307, by rfl⟩ : syracuseStep 345743 = 518615) B518615
theorem B771731 : Blo 342753 771731 := bstep (se 1 (by rfl) ⟨578798, by rfl⟩ : syracuseStep 771731 = 1157597) B1157597
theorem B870041 : Blo 342753 870041 := bstep (se 2 (by rfl) ⟨326265, by rfl⟩ : syracuseStep 870041 = 652531) B652531
theorem B739001 : Blo 342753 739001 := bstep (se 2 (by rfl) ⟨277125, by rfl⟩ : syracuseStep 739001 = 554251) B554251
theorem B345787 : Blo 342753 345787 := bstep (se 1 (by rfl) ⟨259340, by rfl⟩ : syracuseStep 345787 = 518681) B518681
theorem B771785 : Blo 342753 771785 := bstep (se 2 (by rfl) ⟨289419, by rfl⟩ : syracuseStep 771785 = 578839) B578839
theorem B345863 : Blo 342753 345863 := bstep (se 1 (by rfl) ⟨259397, by rfl⟩ : syracuseStep 345863 = 518795) B518795
theorem B345871 : Blo 342753 345871 := bstep (se 1 (by rfl) ⟨259403, by rfl⟩ : syracuseStep 345871 = 518807) B518807
theorem B870203 : Blo 342753 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B345915 : Blo 342753 345915 := bstep (se 1 (by rfl) ⟨259436, by rfl⟩ : syracuseStep 345915 = 518873) B518873
theorem B345991 : Blo 342753 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B345999 : Blo 342753 345999 := bstep (se 1 (by rfl) ⟨259499, by rfl⟩ : syracuseStep 345999 = 518999) B518999
theorem B346043 : Blo 342753 346043 := bstep (se 1 (by rfl) ⟨259532, by rfl⟩ : syracuseStep 346043 = 519065) B519065
theorem B346119 : Blo 342753 346119 := bstep (se 1 (by rfl) ⟨259589, by rfl⟩ : syracuseStep 346119 = 519179) B519179
theorem B346127 : Blo 342753 346127 := bstep (se 1 (by rfl) ⟨259595, by rfl⟩ : syracuseStep 346127 = 519191) B519191
theorem B739343 : Blo 342753 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B739361 : Blo 342753 739361 := bstep (se 2 (by rfl) ⟨277260, by rfl⟩ : syracuseStep 739361 = 554521) B554521
theorem B346171 : Blo 342753 346171 := bstep (se 1 (by rfl) ⟨259628, by rfl⟩ : syracuseStep 346171 = 519257) B519257
theorem B1165373 : Blo 342753 1165373 := bstep (se 3 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 1165373 = 437015) B437015
theorem B53889137 : Blo 342753 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B346247 : Blo 342753 346247 := bstep (se 1 (by rfl) ⟨259685, by rfl⟩ : syracuseStep 346247 = 519371) B519371
theorem B346255 : Blo 342753 346255 := bstep (se 1 (by rfl) ⟨259691, by rfl⟩ : syracuseStep 346255 = 519383) B519383
theorem B870547 : Blo 342753 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B346299 : Blo 342753 346299 := bstep (se 1 (by rfl) ⟨259724, by rfl⟩ : syracuseStep 346299 = 519449) B519449
theorem B346375 : Blo 342753 346375 := bstep (se 1 (by rfl) ⟨259781, by rfl⟩ : syracuseStep 346375 = 519563) B519563
theorem B346383 : Blo 342753 346383 := bstep (se 1 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 346383 = 519575) B519575
theorem B870689 : Blo 342753 870689 := bstep (se 2 (by rfl) ⟨326508, by rfl⟩ : syracuseStep 870689 = 653017) B653017
theorem B936251 : Blo 342753 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B346427 : Blo 342753 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B772487 : Blo 342753 772487 := bstep (se 1 (by rfl) ⟨579365, by rfl⟩ : syracuseStep 772487 = 1158731) B1158731
theorem B346503 : Blo 342753 346503 := bstep (se 1 (by rfl) ⟨259877, by rfl⟩ : syracuseStep 346503 = 519755) B519755
theorem B346511 : Blo 342753 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B412075 : Blo 342753 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B3295673 : Blo 342753 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B346555 : Blo 342753 346555 := bstep (se 1 (by rfl) ⟨259916, by rfl⟩ : syracuseStep 346555 = 519833) B519833
theorem B4704733 : Blo 342753 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B346631 : Blo 342753 346631 := bstep (se 1 (by rfl) ⟨259973, by rfl⟩ : syracuseStep 346631 = 519947) B519947
theorem B346639 : Blo 342753 346639 := bstep (se 1 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 346639 = 519959) B519959
theorem B772667 : Blo 342753 772667 := bstep (se 1 (by rfl) ⟨579500, by rfl⟩ : syracuseStep 772667 = 1159001) B1159001
theorem B346683 : Blo 342753 346683 := bstep (se 1 (by rfl) ⟨260012, by rfl⟩ : syracuseStep 346683 = 520025) B520025
theorem B772793 : Blo 342753 772793 := bstep (se 2 (by rfl) ⟨289797, by rfl⟩ : syracuseStep 772793 = 579595) B579595
theorem B773135 : Blo 342753 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B773153 : Blo 342753 773153 := bstep (se 2 (by rfl) ⟨289932, by rfl⟩ : syracuseStep 773153 = 579865) B579865
theorem B1952855 : Blo 342753 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B871681 : Blo 342753 871681 := bstep (se 2 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 871681 = 653761) B653761
theorem B773495 : Blo 342753 773495 := bstep (se 1 (by rfl) ⟨580121, by rfl⟩ : syracuseStep 773495 = 1160243) B1160243
theorem B1166777 : Blo 342753 1166777 := bstep (se 2 (by rfl) ⟨437541, by rfl⟩ : syracuseStep 1166777 = 875083) B875083
theorem B9915857 : Blo 342753 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B773675 : Blo 342753 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B6311681 : Blo 342753 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B872279 : Blo 342753 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B774035 : Blo 342753 774035 := bstep (se 1 (by rfl) ⟨580526, by rfl⟩ : syracuseStep 774035 = 1161053) B1161053
theorem B774089 : Blo 342753 774089 := bstep (se 2 (by rfl) ⟨290283, by rfl⟩ : syracuseStep 774089 = 580567) B580567
theorem B1167371 : Blo 342753 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B872491 : Blo 342753 872491 := bstep (se 1 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 872491 = 1308737) B1308737
theorem B1167479 : Blo 342753 1167479 := bstep (se 1 (by rfl) ⟨875609, by rfl⟩ : syracuseStep 1167479 = 1751219) B1751219
theorem B413839 : Blo 342753 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B2937005 : Blo 342753 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B872633 : Blo 342753 872633 := bstep (se 2 (by rfl) ⟨327237, by rfl⟩ : syracuseStep 872633 = 654475) B654475
theorem B774791 : Blo 342753 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B414343 : Blo 342753 414343 := bstep (se 1 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 414343 = 621515) B621515
theorem B3920561 : Blo 342753 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B1168073 : Blo 342753 1168073 := bstep (se 2 (by rfl) ⟨438027, by rfl⟩ : syracuseStep 1168073 = 876055) B876055
theorem B774971 : Blo 342753 774971 := bstep (se 1 (by rfl) ⟨581228, by rfl⟩ : syracuseStep 774971 = 1162457) B1162457
theorem B775097 : Blo 342753 775097 := bstep (se 2 (by rfl) ⟨290661, by rfl⟩ : syracuseStep 775097 = 581323) B581323
theorem B414727 : Blo 342753 414727 := bstep (se 1 (by rfl) ⟨311045, by rfl⟩ : syracuseStep 414727 = 622091) B622091
theorem B578603 : Blo 342753 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B1102967 : Blo 342753 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B873625 : Blo 342753 873625 := bstep (se 2 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 873625 = 655219) B655219
theorem B1955087 : Blo 342753 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B775439 : Blo 342753 775439 := bstep (se 1 (by rfl) ⟨581579, by rfl⟩ : syracuseStep 775439 = 1163159) B1163159
theorem B775457 : Blo 342753 775457 := bstep (se 2 (by rfl) ⟨290796, by rfl⟩ : syracuseStep 775457 = 581593) B581593
theorem B873787 : Blo 342753 873787 := bstep (se 1 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 873787 = 1310681) B1310681
theorem B1168775 : Blo 342753 1168775 := bstep (se 1 (by rfl) ⟨876581, by rfl⟩ : syracuseStep 1168775 = 1753163) B1753163
theorem B579001 : Blo 342753 579001 := bstep (se 2 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 579001 = 434251) B434251
theorem B873929 : Blo 342753 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B1955339 : Blo 342753 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B2086519 : Blo 342753 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B775799 : Blo 342753 775799 := bstep (se 1 (by rfl) ⟨581849, by rfl⟩ : syracuseStep 775799 = 1163699) B1163699
theorem B1169153 : Blo 342753 1169153 := bstep (se 2 (by rfl) ⟨438432, by rfl⟩ : syracuseStep 1169153 = 876865) B876865
theorem B874273 : Blo 342753 874273 := bstep (se 2 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 874273 = 655705) B655705
theorem B775979 : Blo 342753 775979 := bstep (se 1 (by rfl) ⟨581984, by rfl⟩ : syracuseStep 775979 = 1163969) B1163969
theorem B415631 : Blo 342753 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B579703 : Blo 342753 579703 := bstep (se 1 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 579703 = 869555) B869555
theorem B776339 : Blo 342753 776339 := bstep (se 1 (by rfl) ⟨582254, by rfl⟩ : syracuseStep 776339 = 1164509) B1164509
theorem B514235 : Blo 342753 514235 := bstep (se 1 (by rfl) ⟨385676, by rfl⟩ : syracuseStep 514235 = 771353) B771353
theorem B776393 : Blo 342753 776393 := bstep (se 2 (by rfl) ⟨291147, by rfl⟩ : syracuseStep 776393 = 582295) B582295
theorem B514295 : Blo 342753 514295 := bstep (se 1 (by rfl) ⟨385721, by rfl⟩ : syracuseStep 514295 = 771443) B771443
theorem B514319 : Blo 342753 514319 := bstep (se 1 (by rfl) ⟨385739, by rfl⟩ : syracuseStep 514319 = 771479) B771479
theorem B514361 : Blo 342753 514361 := bstep (se 2 (by rfl) ⟨192885, by rfl⟩ : syracuseStep 514361 = 385771) B385771
theorem B579899 : Blo 342753 579899 := bstep (se 1 (by rfl) ⟨434924, by rfl⟩ : syracuseStep 579899 = 869849) B869849
theorem B874871 : Blo 342753 874871 := bstep (se 1 (by rfl) ⟨656153, by rfl⟩ : syracuseStep 874871 = 1312307) B1312307
theorem B514439 : Blo 342753 514439 := bstep (se 1 (by rfl) ⟨385829, by rfl⟩ : syracuseStep 514439 = 771659) B771659
theorem B514475 : Blo 342753 514475 := bstep (se 1 (by rfl) ⟨385856, by rfl⟩ : syracuseStep 514475 = 771713) B771713
theorem B514505 : Blo 342753 514505 := bstep (se 2 (by rfl) ⟨192939, by rfl⟩ : syracuseStep 514505 = 385879) B385879
theorem B1169963 : Blo 342753 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B514619 : Blo 342753 514619 := bstep (se 1 (by rfl) ⟨385964, by rfl⟩ : syracuseStep 514619 = 771929) B771929
theorem B514679 : Blo 342753 514679 := bstep (se 1 (by rfl) ⟨386009, by rfl⟩ : syracuseStep 514679 = 772019) B772019
theorem B514703 : Blo 342753 514703 := bstep (se 1 (by rfl) ⟨386027, by rfl⟩ : syracuseStep 514703 = 772055) B772055
theorem B514745 : Blo 342753 514745 := bstep (se 2 (by rfl) ⟨193029, by rfl⟩ : syracuseStep 514745 = 386059) B386059
theorem B1956545 : Blo 342753 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B580297 : Blo 342753 580297 := bstep (se 2 (by rfl) ⟨217611, by rfl⟩ : syracuseStep 580297 = 435223) B435223
theorem B514823 : Blo 342753 514823 := bstep (se 1 (by rfl) ⟨386117, by rfl⟩ : syracuseStep 514823 = 772235) B772235
theorem B514859 : Blo 342753 514859 := bstep (se 1 (by rfl) ⟨386144, by rfl⟩ : syracuseStep 514859 = 772289) B772289
theorem B1661755 : Blo 342753 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B514889 : Blo 342753 514889 := bstep (se 2 (by rfl) ⟨193083, by rfl⟩ : syracuseStep 514889 = 386167) B386167
theorem B777095 : Blo 342753 777095 := bstep (se 1 (by rfl) ⟨582821, by rfl⟩ : syracuseStep 777095 = 1165643) B1165643
theorem B515003 : Blo 342753 515003 := bstep (se 1 (by rfl) ⟨386252, by rfl⟩ : syracuseStep 515003 = 772505) B772505
theorem B515063 : Blo 342753 515063 := bstep (se 1 (by rfl) ⟨386297, by rfl⟩ : syracuseStep 515063 = 772595) B772595
theorem B515087 : Blo 342753 515087 := bstep (se 1 (by rfl) ⟨386315, by rfl⟩ : syracuseStep 515087 = 772631) B772631
theorem B515129 : Blo 342753 515129 := bstep (se 2 (by rfl) ⟨193173, by rfl⟩ : syracuseStep 515129 = 386347) B386347
theorem B777275 : Blo 342753 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B1465411 : Blo 342753 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B515207 : Blo 342753 515207 := bstep (se 1 (by rfl) ⟨386405, by rfl⟩ : syracuseStep 515207 = 772811) B772811
theorem B515243 : Blo 342753 515243 := bstep (se 1 (by rfl) ⟨386432, by rfl⟩ : syracuseStep 515243 = 772865) B772865
theorem B777401 : Blo 342753 777401 := bstep (se 2 (by rfl) ⟨291525, by rfl⟩ : syracuseStep 777401 = 583051) B583051
theorem B515273 : Blo 342753 515273 := bstep (se 2 (by rfl) ⟨193227, by rfl⟩ : syracuseStep 515273 = 386455) B386455
theorem B515387 : Blo 342753 515387 := bstep (se 1 (by rfl) ⟨386540, by rfl⟩ : syracuseStep 515387 = 773081) B773081
theorem B3366203 : Blo 342753 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B941399 : Blo 342753 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B515447 : Blo 342753 515447 := bstep (se 1 (by rfl) ⟨386585, by rfl⟩ : syracuseStep 515447 = 773171) B773171
theorem B1465735 : Blo 342753 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B580999 : Blo 342753 580999 := bstep (se 1 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 580999 = 871499) B871499
theorem B515471 : Blo 342753 515471 := bstep (se 1 (by rfl) ⟨386603, by rfl⟩ : syracuseStep 515471 = 773207) B773207
theorem B515513 : Blo 342753 515513 := bstep (se 2 (by rfl) ⟨193317, by rfl⟩ : syracuseStep 515513 = 386635) B386635
theorem B515591 : Blo 342753 515591 := bstep (se 1 (by rfl) ⟨386693, by rfl⟩ : syracuseStep 515591 = 773387) B773387
theorem B777743 : Blo 342753 777743 := bstep (se 1 (by rfl) ⟨583307, by rfl⟩ : syracuseStep 777743 = 1166615) B1166615
theorem B777761 : Blo 342753 777761 := bstep (se 2 (by rfl) ⟨291660, by rfl⟩ : syracuseStep 777761 = 583321) B583321
theorem B515627 : Blo 342753 515627 := bstep (se 1 (by rfl) ⟨386720, by rfl⟩ : syracuseStep 515627 = 773441) B773441
theorem B515657 : Blo 342753 515657 := bstep (se 2 (by rfl) ⟨193371, by rfl⟩ : syracuseStep 515657 = 386743) B386743
theorem B876167 : Blo 342753 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B876217 : Blo 342753 876217 := bstep (se 2 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 876217 = 657163) B657163
theorem B515771 : Blo 342753 515771 := bstep (se 1 (by rfl) ⟨386828, by rfl⟩ : syracuseStep 515771 = 773657) B773657
theorem B515831 : Blo 342753 515831 := bstep (se 1 (by rfl) ⟨386873, by rfl⟩ : syracuseStep 515831 = 773747) B773747
theorem B515855 : Blo 342753 515855 := bstep (se 1 (by rfl) ⟨386891, by rfl⟩ : syracuseStep 515855 = 773783) B773783
theorem B515897 : Blo 342753 515897 := bstep (se 2 (by rfl) ⟨193461, by rfl⟩ : syracuseStep 515897 = 386923) B386923
theorem B778103 : Blo 342753 778103 := bstep (se 1 (by rfl) ⟨583577, by rfl⟩ : syracuseStep 778103 = 1167155) B1167155
theorem B515975 : Blo 342753 515975 := bstep (se 1 (by rfl) ⟨386981, by rfl⟩ : syracuseStep 515975 = 773963) B773963
theorem B1302419 : Blo 342753 1302419 := bstep (se 1 (by rfl) ⟨976814, by rfl⟩ : syracuseStep 1302419 = 1953629) B1953629
theorem B516011 : Blo 342753 516011 := bstep (se 1 (by rfl) ⟨387008, by rfl⟩ : syracuseStep 516011 = 774017) B774017
theorem B516041 : Blo 342753 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B581647 : Blo 342753 581647 := bstep (se 1 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 581647 = 872471) B872471
theorem B778283 : Blo 342753 778283 := bstep (se 1 (by rfl) ⟨583712, by rfl⟩ : syracuseStep 778283 = 1167425) B1167425
theorem B516155 : Blo 342753 516155 := bstep (se 1 (by rfl) ⟨387116, by rfl⟩ : syracuseStep 516155 = 774233) B774233
theorem B516215 : Blo 342753 516215 := bstep (se 1 (by rfl) ⟨387161, by rfl⟩ : syracuseStep 516215 = 774323) B774323
theorem B516239 : Blo 342753 516239 := bstep (se 1 (by rfl) ⟨387179, by rfl⟩ : syracuseStep 516239 = 774359) B774359
theorem B1794221 : Blo 342753 1794221 := bstep (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) B672833
theorem B516281 : Blo 342753 516281 := bstep (se 2 (by rfl) ⟨193605, by rfl⟩ : syracuseStep 516281 = 387211) B387211
theorem B516359 : Blo 342753 516359 := bstep (se 1 (by rfl) ⟨387269, by rfl⟩ : syracuseStep 516359 = 774539) B774539
theorem B876815 : Blo 342753 876815 := bstep (se 1 (by rfl) ⟨657611, by rfl⟩ : syracuseStep 876815 = 1315223) B1315223
theorem B1466657 : Blo 342753 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B3825953 : Blo 342753 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B516395 : Blo 342753 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B516425 : Blo 342753 516425 := bstep (se 2 (by rfl) ⟨193659, by rfl⟩ : syracuseStep 516425 = 387319) B387319
theorem B14836061 : Blo 342753 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B778643 : Blo 342753 778643 := bstep (se 1 (by rfl) ⟨583982, by rfl⟩ : syracuseStep 778643 = 1167965) B1167965
theorem B516539 : Blo 342753 516539 := bstep (se 1 (by rfl) ⟨387404, by rfl⟩ : syracuseStep 516539 = 774809) B774809
theorem B778697 : Blo 342753 778697 := bstep (se 2 (by rfl) ⟨292011, by rfl⟩ : syracuseStep 778697 = 584023) B584023
theorem B516599 : Blo 342753 516599 := bstep (se 1 (by rfl) ⟨387449, by rfl⟩ : syracuseStep 516599 = 774899) B774899
theorem B516623 : Blo 342753 516623 := bstep (se 1 (by rfl) ⟨387467, by rfl⟩ : syracuseStep 516623 = 774935) B774935
theorem B582187 : Blo 342753 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B516665 : Blo 342753 516665 := bstep (se 2 (by rfl) ⟨193749, by rfl⟩ : syracuseStep 516665 = 387499) B387499
theorem B516743 : Blo 342753 516743 := bstep (se 1 (by rfl) ⟨387557, by rfl⟩ : syracuseStep 516743 = 775115) B775115
theorem B516779 : Blo 342753 516779 := bstep (se 1 (by rfl) ⟨387584, by rfl⟩ : syracuseStep 516779 = 775169) B775169
theorem B582329 : Blo 342753 582329 := bstep (se 2 (by rfl) ⟨218373, by rfl⟩ : syracuseStep 582329 = 436747) B436747
theorem B516809 : Blo 342753 516809 := bstep (se 2 (by rfl) ⟨193803, by rfl⟩ : syracuseStep 516809 = 387607) B387607
theorem B385807 : Blo 342753 385807 := bstep (se 1 (by rfl) ⟨289355, by rfl⟩ : syracuseStep 385807 = 578711) B578711
theorem B516923 : Blo 342753 516923 := bstep (se 1 (by rfl) ⟨387692, by rfl⟩ : syracuseStep 516923 = 775385) B775385
theorem B516983 : Blo 342753 516983 := bstep (se 1 (by rfl) ⟨387737, by rfl⟩ : syracuseStep 516983 = 775475) B775475
theorem B517007 : Blo 342753 517007 := bstep (se 1 (by rfl) ⟨387755, by rfl⟩ : syracuseStep 517007 = 775511) B775511
theorem B517049 : Blo 342753 517049 := bstep (se 2 (by rfl) ⟨193893, by rfl⟩ : syracuseStep 517049 = 387787) B387787
theorem B877513 : Blo 342753 877513 := bstep (se 2 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 877513 = 658135) B658135
theorem B4482053 : Blo 342753 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B517127 : Blo 342753 517127 := bstep (se 1 (by rfl) ⟨387845, by rfl⟩ : syracuseStep 517127 = 775691) B775691
theorem B1664023 : Blo 342753 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B517163 : Blo 342753 517163 := bstep (se 1 (by rfl) ⟨387872, by rfl⟩ : syracuseStep 517163 = 775745) B775745
theorem B517193 : Blo 342753 517193 := bstep (se 2 (by rfl) ⟨193947, by rfl⟩ : syracuseStep 517193 = 387895) B387895
theorem B877655 : Blo 342753 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B779399 : Blo 342753 779399 := bstep (se 1 (by rfl) ⟨584549, by rfl⟩ : syracuseStep 779399 = 1169099) B1169099
theorem B517307 : Blo 342753 517307 := bstep (se 1 (by rfl) ⟨387980, by rfl⟩ : syracuseStep 517307 = 775961) B775961
theorem B517367 : Blo 342753 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B386311 : Blo 342753 386311 := bstep (se 1 (by rfl) ⟨289733, by rfl⟩ : syracuseStep 386311 = 579467) B579467
theorem B1238287 : Blo 342753 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B517391 : Blo 342753 517391 := bstep (se 1 (by rfl) ⟨388043, by rfl⟩ : syracuseStep 517391 = 776087) B776087
theorem B517433 : Blo 342753 517433 := bstep (se 2 (by rfl) ⟨194037, by rfl⟩ : syracuseStep 517433 = 388075) B388075
theorem B3728699 : Blo 342753 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B779579 : Blo 342753 779579 := bstep (se 1 (by rfl) ⟨584684, by rfl⟩ : syracuseStep 779579 = 1169369) B1169369
theorem B583031 : Blo 342753 583031 := bstep (se 1 (by rfl) ⟨437273, by rfl⟩ : syracuseStep 583031 = 874547) B874547
theorem B517511 : Blo 342753 517511 := bstep (se 1 (by rfl) ⟨388133, by rfl⟩ : syracuseStep 517511 = 776267) B776267
theorem B517547 : Blo 342753 517547 := bstep (se 1 (by rfl) ⟨388160, by rfl⟩ : syracuseStep 517547 = 776321) B776321
theorem B976313 : Blo 342753 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B779705 : Blo 342753 779705 := bstep (se 2 (by rfl) ⟨292389, by rfl⟩ : syracuseStep 779705 = 584779) B584779
theorem B386491 : Blo 342753 386491 := bstep (se 1 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 386491 = 579737) B579737
theorem B517577 : Blo 342753 517577 := bstep (se 2 (by rfl) ⟨194091, by rfl⟩ : syracuseStep 517577 = 388183) B388183
theorem B517691 : Blo 342753 517691 := bstep (se 1 (by rfl) ⟨388268, by rfl⟩ : syracuseStep 517691 = 776537) B776537
theorem B517751 : Blo 342753 517751 := bstep (se 1 (by rfl) ⟨388313, by rfl⟩ : syracuseStep 517751 = 776627) B776627
theorem B517775 : Blo 342753 517775 := bstep (se 1 (by rfl) ⟨388331, by rfl⟩ : syracuseStep 517775 = 776663) B776663
theorem B517817 : Blo 342753 517817 := bstep (se 2 (by rfl) ⟨194181, by rfl⟩ : syracuseStep 517817 = 388363) B388363
theorem B1795841 : Blo 342753 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B517895 : Blo 342753 517895 := bstep (se 1 (by rfl) ⟨388421, by rfl⟩ : syracuseStep 517895 = 776843) B776843
theorem B780047 : Blo 342753 780047 := bstep (se 1 (by rfl) ⟨585035, by rfl⟩ : syracuseStep 780047 = 1170071) B1170071
theorem B1959713 : Blo 342753 1959713 := bstep (se 2 (by rfl) ⟨734892, by rfl⟩ : syracuseStep 1959713 = 1469785) B1469785
theorem B780065 : Blo 342753 780065 := bstep (se 2 (by rfl) ⟨292524, by rfl⟩ : syracuseStep 780065 = 585049) B585049
theorem B517931 : Blo 342753 517931 := bstep (se 1 (by rfl) ⟨388448, by rfl⟩ : syracuseStep 517931 = 776897) B776897
theorem B583483 : Blo 342753 583483 := bstep (se 1 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 583483 = 875225) B875225
theorem B517961 : Blo 342753 517961 := bstep (se 2 (by rfl) ⟨194235, by rfl⟩ : syracuseStep 517961 = 388471) B388471
theorem B386959 : Blo 342753 386959 := bstep (se 1 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 386959 = 580439) B580439
theorem B518075 : Blo 342753 518075 := bstep (se 1 (by rfl) ⟨388556, by rfl⟩ : syracuseStep 518075 = 777113) B777113
theorem B583625 : Blo 342753 583625 := bstep (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) B437719
theorem B518135 : Blo 342753 518135 := bstep (se 1 (by rfl) ⟨388601, by rfl⟩ : syracuseStep 518135 = 777203) B777203
theorem B518159 : Blo 342753 518159 := bstep (se 1 (by rfl) ⟨388619, by rfl⟩ : syracuseStep 518159 = 777239) B777239
theorem B518201 : Blo 342753 518201 := bstep (se 2 (by rfl) ⟨194325, by rfl⟩ : syracuseStep 518201 = 388651) B388651
theorem B518279 : Blo 342753 518279 := bstep (se 1 (by rfl) ⟨388709, by rfl⟩ : syracuseStep 518279 = 777419) B777419
theorem B518315 : Blo 342753 518315 := bstep (se 1 (by rfl) ⟨388736, by rfl⟩ : syracuseStep 518315 = 777473) B777473
theorem B1665197 : Blo 342753 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B518345 : Blo 342753 518345 := bstep (se 2 (by rfl) ⟨194379, by rfl⟩ : syracuseStep 518345 = 388759) B388759
theorem B8349965 : Blo 342753 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B551227 : Blo 342753 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B518459 : Blo 342753 518459 := bstep (se 1 (by rfl) ⟨388844, by rfl⟩ : syracuseStep 518459 = 777689) B777689
theorem B518519 : Blo 342753 518519 := bstep (se 1 (by rfl) ⟨388889, by rfl⟩ : syracuseStep 518519 = 777779) B777779
theorem B387463 : Blo 342753 387463 := bstep (se 1 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 387463 = 581195) B581195
theorem B518543 : Blo 342753 518543 := bstep (se 1 (by rfl) ⟨388907, by rfl⟩ : syracuseStep 518543 = 777815) B777815
theorem B3303827 : Blo 342753 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B977305 : Blo 342753 977305 := bstep (se 2 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 977305 = 732979) B732979
theorem B1305017 : Blo 342753 1305017 := bstep (se 2 (by rfl) ⟨489381, by rfl⟩ : syracuseStep 1305017 = 978763) B978763
theorem B518585 : Blo 342753 518585 := bstep (se 2 (by rfl) ⟨194469, by rfl⟩ : syracuseStep 518585 = 388939) B388939
theorem B518663 : Blo 342753 518663 := bstep (se 1 (by rfl) ⟨388997, by rfl⟩ : syracuseStep 518663 = 777995) B777995
theorem B518699 : Blo 342753 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B387643 : Blo 342753 387643 := bstep (se 1 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 387643 = 581465) B581465
theorem B518729 : Blo 342753 518729 := bstep (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) B389047
theorem B3992165 : Blo 342753 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B1174135 : Blo 342753 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B584327 : Blo 342753 584327 := bstep (se 1 (by rfl) ⟨438245, by rfl⟩ : syracuseStep 584327 = 876491) B876491
theorem B518843 : Blo 342753 518843 := bstep (se 1 (by rfl) ⟨389132, by rfl⟩ : syracuseStep 518843 = 778265) B778265
theorem B518903 : Blo 342753 518903 := bstep (se 1 (by rfl) ⟨389177, by rfl⟩ : syracuseStep 518903 = 778355) B778355
theorem B518927 : Blo 342753 518927 := bstep (se 1 (by rfl) ⟨389195, by rfl⟩ : syracuseStep 518927 = 778391) B778391
theorem B518969 : Blo 342753 518969 := bstep (se 2 (by rfl) ⟨194613, by rfl⟩ : syracuseStep 518969 = 389227) B389227
theorem B519047 : Blo 342753 519047 := bstep (se 1 (by rfl) ⟨389285, by rfl⟩ : syracuseStep 519047 = 778571) B778571
theorem B5565347 : Blo 342753 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B519083 : Blo 342753 519083 := bstep (se 1 (by rfl) ⟨389312, by rfl⟩ : syracuseStep 519083 = 778625) B778625
theorem B519113 : Blo 342753 519113 := bstep (se 2 (by rfl) ⟨194667, by rfl⟩ : syracuseStep 519113 = 389335) B389335
theorem B388111 : Blo 342753 388111 := bstep (se 1 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 388111 = 582167) B582167
theorem B519227 : Blo 342753 519227 := bstep (se 1 (by rfl) ⟨389420, by rfl⟩ : syracuseStep 519227 = 778841) B778841
theorem B519287 : Blo 342753 519287 := bstep (se 1 (by rfl) ⟨389465, by rfl⟩ : syracuseStep 519287 = 778931) B778931
theorem B519311 : Blo 342753 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B519353 : Blo 342753 519353 := bstep (se 2 (by rfl) ⟨194757, by rfl⟩ : syracuseStep 519353 = 389515) B389515
theorem B519431 : Blo 342753 519431 := bstep (se 1 (by rfl) ⟨389573, by rfl⟩ : syracuseStep 519431 = 779147) B779147
theorem B584975 : Blo 342753 584975 := bstep (se 1 (by rfl) ⟨438731, by rfl⟩ : syracuseStep 584975 = 877463) B877463
theorem B519467 : Blo 342753 519467 := bstep (se 1 (by rfl) ⟨389600, by rfl⟩ : syracuseStep 519467 = 779201) B779201
theorem B519497 : Blo 342753 519497 := bstep (se 2 (by rfl) ⟨194811, by rfl⟩ : syracuseStep 519497 = 389623) B389623
theorem B1306003 : Blo 342753 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B6254009 : Blo 342753 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B519611 : Blo 342753 519611 := bstep (se 1 (by rfl) ⟨389708, by rfl⟩ : syracuseStep 519611 = 779417) B779417
theorem B519671 : Blo 342753 519671 := bstep (se 1 (by rfl) ⟨389753, by rfl⟩ : syracuseStep 519671 = 779507) B779507
theorem B388615 : Blo 342753 388615 := bstep (se 1 (by rfl) ⟨291461, by rfl⟩ : syracuseStep 388615 = 582923) B582923
theorem B519695 : Blo 342753 519695 := bstep (se 1 (by rfl) ⟨389771, by rfl⟩ : syracuseStep 519695 = 779543) B779543
theorem B519737 : Blo 342753 519737 := bstep (se 2 (by rfl) ⟨194901, by rfl⟩ : syracuseStep 519737 = 389803) B389803
theorem B1568375 : Blo 342753 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B519815 : Blo 342753 519815 := bstep (se 1 (by rfl) ⟨389861, by rfl⟩ : syracuseStep 519815 = 779723) B779723
theorem B519851 : Blo 342753 519851 := bstep (se 1 (by rfl) ⟨389888, by rfl⟩ : syracuseStep 519851 = 779777) B779777
theorem B388795 : Blo 342753 388795 := bstep (se 1 (by rfl) ⟨291596, by rfl⟩ : syracuseStep 388795 = 583193) B583193
theorem B519881 : Blo 342753 519881 := bstep (se 2 (by rfl) ⟨194955, by rfl⟩ : syracuseStep 519881 = 389911) B389911
theorem B519995 : Blo 342753 519995 := bstep (se 1 (by rfl) ⟨389996, by rfl⟩ : syracuseStep 519995 = 779993) B779993
theorem B520055 : Blo 342753 520055 := bstep (se 1 (by rfl) ⟨390041, by rfl⟩ : syracuseStep 520055 = 780083) B780083
theorem B520079 : Blo 342753 520079 := bstep (se 1 (by rfl) ⟨390059, by rfl⟩ : syracuseStep 520079 = 780119) B780119
theorem B520121 : Blo 342753 520121 := bstep (se 2 (by rfl) ⟨195045, by rfl⟩ : syracuseStep 520121 = 390091) B390091
theorem B3731467 : Blo 342753 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B1962103 : Blo 342753 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B389263 : Blo 342753 389263 := bstep (se 1 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 389263 = 583895) B583895
theorem B1765577 : Blo 342753 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B979229 : Blo 342753 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B389767 : Blo 342753 389767 := bstep (se 1 (by rfl) ⟨292325, by rfl⟩ : syracuseStep 389767 = 584651) B584651
theorem B389947 : Blo 342753 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B652151 : Blo 342753 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B979913 : Blo 342753 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B1471441 : Blo 342753 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B652303 : Blo 342753 652303 := bstep (se 1 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 652303 = 978455) B978455
theorem B488521 : Blo 342753 488521 := bstep (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) B366391
theorem B1307735 : Blo 342753 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B619721 : Blo 342753 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B2094281 : Blo 342753 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B90273005 : Blo 342753 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B1963379 : Blo 342753 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B652691 : Blo 342753 652691 := bstep (se 1 (by rfl) ⟨489518, by rfl⟩ : syracuseStep 652691 = 979037) B979037
theorem B980495 : Blo 342753 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B489017 : Blo 342753 489017 := bstep (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) B366763
theorem B1308221 : Blo 342753 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B620303 : Blo 342753 620303 := bstep (se 1 (by rfl) ⟨465227, by rfl⟩ : syracuseStep 620303 = 930455) B930455
theorem B1963835 : Blo 342753 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B1996633 : Blo 342753 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B1046557 : Blo 342753 1046557 := bstep (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) B392459
theorem B784673 : Blo 342753 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B489991 : Blo 342753 489991 := bstep (se 1 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 489991 = 734987) B734987
theorem B1178155 : Blo 342753 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B654095 : Blo 342753 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B1964837 : Blo 342753 1964837 := bstep (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) B368407
theorem B3308363 : Blo 342753 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B981895 : Blo 342753 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B982169 : Blo 342753 982169 := bstep (se 2 (by rfl) ⟨368313, by rfl⟩ : syracuseStep 982169 = 736627) B736627
theorem B1965293 : Blo 342753 1965293 := bstep (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) B736985
theorem B654635 : Blo 342753 654635 := bstep (se 1 (by rfl) ⟨490976, by rfl⟩ : syracuseStep 654635 = 981953) B981953
theorem B1965977 : Blo 342753 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B491449 : Blo 342753 491449 := bstep (se 2 (by rfl) ⟨184293, by rfl⟩ : syracuseStep 491449 = 368587) B368587
theorem B5865533 : Blo 342753 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B655607 : Blo 342753 655607 := bstep (se 1 (by rfl) ⟨491705, by rfl⟩ : syracuseStep 655607 = 983411) B983411
theorem B1245451 : Blo 342753 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1868093 : Blo 342753 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B1245565 : Blo 342753 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B492041 : Blo 342753 492041 := bstep (se 2 (by rfl) ⟨184515, by rfl⟩ : syracuseStep 492041 = 369031) B369031
theorem B1180345 : Blo 342753 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B1574083 : Blo 342753 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B1246403 : Blo 342753 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B492895 : Blo 342753 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B492907 : Blo 342753 492907 := bstep (se 1 (by rfl) ⟨369680, by rfl⟩ : syracuseStep 492907 = 739361) B739361
theorem B656905 : Blo 342753 656905 := bstep (se 2 (by rfl) ⟨246339, by rfl⟩ : syracuseStep 656905 = 492679) B492679
theorem B624167 : Blo 342753 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B2197115 : Blo 342753 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B657247 : Blo 342753 657247 := bstep (se 1 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 657247 = 985871) B985871
theorem B1968209 : Blo 342753 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B5900525 : Blo 342753 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B1739069 : Blo 342753 1739069 := bstep (se 3 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 1739069 = 652151) B652151
theorem B1313111 : Blo 342753 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B789031 : Blo 342753 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B986269 : Blo 342753 986269 := bstep (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) B369851
theorem B986975 : Blo 342753 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B1249199 : Blo 342753 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B528347 : Blo 342753 528347 := bstep (se 1 (by rfl) ⟨396260, by rfl⟩ : syracuseStep 528347 = 792521) B792521
theorem B2822221 : Blo 342753 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B1249661 : Blo 342753 1249661 := bstep (se 3 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 1249661 = 468623) B468623
theorem B1970669 : Blo 342753 1970669 := bstep (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) B739001
theorem B1741337 : Blo 342753 1741337 := bstep (se 2 (by rfl) ⟨653001, by rfl⟩ : syracuseStep 1741337 = 1306003) B1306003
theorem B627599 : Blo 342753 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B398299 : Blo 342753 398299 := bstep (se 1 (by rfl) ⟨298724, by rfl⟩ : syracuseStep 398299 = 597449) B597449
theorem B1315997 : Blo 342753 1315997 := bstep (se 3 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 1315997 = 493499) B493499
theorem B1971809 : Blo 342753 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B2561675 : Blo 342753 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B1185491 : Blo 342753 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B2988035 : Blo 342753 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B3545633 : Blo 342753 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B2202551 : Blo 342753 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B1973267 : Blo 342753 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B2432051 : Blo 342753 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B2661443 : Blo 342753 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B3710231 : Blo 342753 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B1744253 : Blo 342753 1744253 := bstep (se 3 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 1744253 = 654095) B654095
theorem B4169339 : Blo 342753 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B2629259 : Blo 342753 2629259 := bstep (se 1 (by rfl) ⟨1971944, by rfl⟩ : syracuseStep 2629259 = 3943889) B3943889
theorem B1417753 : Blo 342753 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B435127 : Blo 342753 435127 := bstep (se 1 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 435127 = 652691) B652691
theorem B664615 : Blo 342753 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B35923661 : Blo 342753 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B2205575 : Blo 342753 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B10758041 : Blo 342753 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B1157273 : Blo 342753 1157273 := bstep (se 2 (by rfl) ⟨433977, by rfl⟩ : syracuseStep 1157273 = 867955) B867955
theorem B436423 : Blo 342753 436423 := bstep (se 1 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 436423 = 654635) B654635
theorem B4401611 : Blo 342753 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B928379 : Blo 342753 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B764615 : Blo 342753 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B437167 : Blo 342753 437167 := bstep (se 1 (by rfl) ⟨327875, by rfl⟩ : syracuseStep 437167 = 655751) B655751
theorem B732091 : Blo 342753 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B732167 : Blo 342753 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B1158461 : Blo 342753 1158461 := bstep (se 3 (by rfl) ⟨217211, by rfl⟩ : syracuseStep 1158461 = 434423) B434423
theorem B16166279 : Blo 342753 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B699911 : Blo 342753 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B1748627 : Blo 342753 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B2207675 : Blo 342753 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B438311 : Blo 342753 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B35926091 : Blo 342753 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B3321971 : Blo 342753 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B1159325 : Blo 342753 1159325 := bstep (se 3 (by rfl) ⟨217373, by rfl⟩ : syracuseStep 1159325 = 434747) B434747
theorem B1651049 : Blo 342753 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B438635 : Blo 342753 438635 := bstep (se 1 (by rfl) ⟨328976, by rfl⟩ : syracuseStep 438635 = 657953) B657953
theorem B1159865 : Blo 342753 1159865 := bstep (se 2 (by rfl) ⟨434949, by rfl⟩ : syracuseStep 1159865 = 869899) B869899
theorem B9679621 : Blo 342753 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B4207787 : Blo 342753 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B1160459 : Blo 342753 1160459 := bstep (se 1 (by rfl) ⟨870344, by rfl⟩ : syracuseStep 1160459 = 1740689) B1740689
theorem B1160729 : Blo 342753 1160729 := bstep (se 2 (by rfl) ⟨435273, by rfl⟩ : syracuseStep 1160729 = 870547) B870547
theorem B734969 : Blo 342753 734969 := bstep (se 2 (by rfl) ⟨275613, by rfl⟩ : syracuseStep 734969 = 551227) B551227
theorem B931657 : Blo 342753 931657 := bstep (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) B698743
theorem B5027789 : Blo 342753 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B6272977 : Blo 342753 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B2603015 : Blo 342753 2603015 := bstep (se 1 (by rfl) ⟨1952261, by rfl⟩ : syracuseStep 2603015 = 3904523) B3904523
theorem B735311 : Blo 342753 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B2603501 : Blo 342753 2603501 := bstep (se 3 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 2603501 = 976313) B976313
theorem B1161863 : Blo 342753 1161863 := bstep (se 1 (by rfl) ⟨871397, by rfl⟩ : syracuseStep 1161863 = 1742795) B1742795
theorem B1161917 : Blo 342753 1161917 := bstep (se 3 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 1161917 = 435719) B435719
theorem B342823 : Blo 342753 342823 := bstep (se 1 (by rfl) ⟨257117, by rfl⟩ : syracuseStep 342823 = 514235) B514235
theorem B342863 : Blo 342753 342863 := bstep (se 1 (by rfl) ⟨257147, by rfl⟩ : syracuseStep 342863 = 514295) B514295
theorem B342879 : Blo 342753 342879 := bstep (se 1 (by rfl) ⟨257159, by rfl⟩ : syracuseStep 342879 = 514319) B514319
theorem B1162079 : Blo 342753 1162079 := bstep (se 1 (by rfl) ⟨871559, by rfl⟩ : syracuseStep 1162079 = 1743119) B1743119
theorem B342907 : Blo 342753 342907 := bstep (se 1 (by rfl) ⟨257180, by rfl⟩ : syracuseStep 342907 = 514361) B514361
theorem B342959 : Blo 342753 342959 := bstep (se 1 (by rfl) ⟨257219, by rfl⟩ : syracuseStep 342959 = 514439) B514439
theorem B342983 : Blo 342753 342983 := bstep (se 1 (by rfl) ⟨257237, by rfl⟩ : syracuseStep 342983 = 514475) B514475
theorem B343003 : Blo 342753 343003 := bstep (se 1 (by rfl) ⟨257252, by rfl⟩ : syracuseStep 343003 = 514505) B514505
theorem B1162241 : Blo 342753 1162241 := bstep (se 2 (by rfl) ⟨435840, by rfl⟩ : syracuseStep 1162241 = 871681) B871681
theorem B343079 : Blo 342753 343079 := bstep (se 1 (by rfl) ⟨257309, by rfl⟩ : syracuseStep 343079 = 514619) B514619
theorem B343119 : Blo 342753 343119 := bstep (se 1 (by rfl) ⟨257339, by rfl⟩ : syracuseStep 343119 = 514679) B514679
theorem B343135 : Blo 342753 343135 := bstep (se 1 (by rfl) ⟨257351, by rfl⟩ : syracuseStep 343135 = 514703) B514703
theorem B343163 : Blo 342753 343163 := bstep (se 1 (by rfl) ⟨257372, by rfl⟩ : syracuseStep 343163 = 514745) B514745
theorem B343215 : Blo 342753 343215 := bstep (se 1 (by rfl) ⟨257411, by rfl⟩ : syracuseStep 343215 = 514823) B514823
theorem B343239 : Blo 342753 343239 := bstep (se 1 (by rfl) ⟨257429, by rfl⟩ : syracuseStep 343239 = 514859) B514859
theorem B343259 : Blo 342753 343259 := bstep (se 1 (by rfl) ⟨257444, by rfl⟩ : syracuseStep 343259 = 514889) B514889
theorem B343335 : Blo 342753 343335 := bstep (se 1 (by rfl) ⟨257501, by rfl⟩ : syracuseStep 343335 = 515003) B515003
theorem B343375 : Blo 342753 343375 := bstep (se 1 (by rfl) ⟨257531, by rfl⟩ : syracuseStep 343375 = 515063) B515063
theorem B1359191 : Blo 342753 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B343391 : Blo 342753 343391 := bstep (se 1 (by rfl) ⟨257543, by rfl⟩ : syracuseStep 343391 = 515087) B515087
theorem B343419 : Blo 342753 343419 := bstep (se 1 (by rfl) ⟨257564, by rfl⟩ : syracuseStep 343419 = 515129) B515129
theorem B343471 : Blo 342753 343471 := bstep (se 1 (by rfl) ⟨257603, by rfl⟩ : syracuseStep 343471 = 515207) B515207
theorem B343495 : Blo 342753 343495 := bstep (se 1 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 343495 = 515243) B515243
theorem B343515 : Blo 342753 343515 := bstep (se 1 (by rfl) ⟨257636, by rfl⟩ : syracuseStep 343515 = 515273) B515273
theorem B343591 : Blo 342753 343591 := bstep (se 1 (by rfl) ⟨257693, by rfl⟩ : syracuseStep 343591 = 515387) B515387
theorem B343631 : Blo 342753 343631 := bstep (se 1 (by rfl) ⟨257723, by rfl⟩ : syracuseStep 343631 = 515447) B515447
theorem B343647 : Blo 342753 343647 := bstep (se 1 (by rfl) ⟨257735, by rfl⟩ : syracuseStep 343647 = 515471) B515471
theorem B343675 : Blo 342753 343675 := bstep (se 1 (by rfl) ⟨257756, by rfl⟩ : syracuseStep 343675 = 515513) B515513
theorem B343727 : Blo 342753 343727 := bstep (se 1 (by rfl) ⟨257795, by rfl⟩ : syracuseStep 343727 = 515591) B515591
theorem B343751 : Blo 342753 343751 := bstep (se 1 (by rfl) ⟨257813, by rfl⟩ : syracuseStep 343751 = 515627) B515627
theorem B343771 : Blo 342753 343771 := bstep (se 1 (by rfl) ⟨257828, by rfl⟩ : syracuseStep 343771 = 515657) B515657
theorem B343847 : Blo 342753 343847 := bstep (se 1 (by rfl) ⟨257885, by rfl⟩ : syracuseStep 343847 = 515771) B515771
theorem B1163051 : Blo 342753 1163051 := bstep (se 1 (by rfl) ⟨872288, by rfl⟩ : syracuseStep 1163051 = 1744577) B1744577
theorem B1294123 : Blo 342753 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B343887 : Blo 342753 343887 := bstep (se 1 (by rfl) ⟨257915, by rfl⟩ : syracuseStep 343887 = 515831) B515831
theorem B343903 : Blo 342753 343903 := bstep (se 1 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 343903 = 515855) B515855
theorem B343931 : Blo 342753 343931 := bstep (se 1 (by rfl) ⟨257948, by rfl⟩ : syracuseStep 343931 = 515897) B515897
theorem B343983 : Blo 342753 343983 := bstep (se 1 (by rfl) ⟨257987, by rfl⟩ : syracuseStep 343983 = 515975) B515975
theorem B868279 : Blo 342753 868279 := bstep (se 1 (by rfl) ⟨651209, by rfl⟩ : syracuseStep 868279 = 1302419) B1302419
theorem B344007 : Blo 342753 344007 := bstep (se 1 (by rfl) ⟨258005, by rfl⟩ : syracuseStep 344007 = 516011) B516011
theorem B344027 : Blo 342753 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B2211877 : Blo 342753 2211877 := bstep (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) B414727
theorem B344103 : Blo 342753 344103 := bstep (se 1 (by rfl) ⟨258077, by rfl⟩ : syracuseStep 344103 = 516155) B516155
theorem B1163321 : Blo 342753 1163321 := bstep (se 2 (by rfl) ⟨436245, by rfl⟩ : syracuseStep 1163321 = 872491) B872491
theorem B344143 : Blo 342753 344143 := bstep (se 1 (by rfl) ⟨258107, by rfl⟩ : syracuseStep 344143 = 516215) B516215
theorem B344159 : Blo 342753 344159 := bstep (se 1 (by rfl) ⟨258119, by rfl⟩ : syracuseStep 344159 = 516239) B516239
theorem B1196147 : Blo 342753 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B344187 : Blo 342753 344187 := bstep (se 1 (by rfl) ⟨258140, by rfl⟩ : syracuseStep 344187 = 516281) B516281
theorem B344239 : Blo 342753 344239 := bstep (se 1 (by rfl) ⟨258179, by rfl⟩ : syracuseStep 344239 = 516359) B516359
theorem B344263 : Blo 342753 344263 := bstep (se 1 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 344263 = 516395) B516395
theorem B344283 : Blo 342753 344283 := bstep (se 1 (by rfl) ⟨258212, by rfl⟩ : syracuseStep 344283 = 516425) B516425
theorem B344359 : Blo 342753 344359 := bstep (se 1 (by rfl) ⟨258269, by rfl⟩ : syracuseStep 344359 = 516539) B516539
theorem B344399 : Blo 342753 344399 := bstep (se 1 (by rfl) ⟨258299, by rfl⟩ : syracuseStep 344399 = 516599) B516599
theorem B344415 : Blo 342753 344415 := bstep (se 1 (by rfl) ⟨258311, by rfl⟩ : syracuseStep 344415 = 516623) B516623
theorem B344443 : Blo 342753 344443 := bstep (se 1 (by rfl) ⟨258332, by rfl⟩ : syracuseStep 344443 = 516665) B516665
theorem B1163645 : Blo 342753 1163645 := bstep (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) B436367
theorem B2605445 : Blo 342753 2605445 := bstep (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) B488521
theorem B344495 : Blo 342753 344495 := bstep (se 1 (by rfl) ⟨258371, by rfl⟩ : syracuseStep 344495 = 516743) B516743
theorem B344519 : Blo 342753 344519 := bstep (se 1 (by rfl) ⟨258389, by rfl⟩ : syracuseStep 344519 = 516779) B516779
theorem B344539 : Blo 342753 344539 := bstep (se 1 (by rfl) ⟨258404, by rfl⟩ : syracuseStep 344539 = 516809) B516809
theorem B344615 : Blo 342753 344615 := bstep (se 1 (by rfl) ⟨258461, by rfl⟩ : syracuseStep 344615 = 516923) B516923
theorem B344655 : Blo 342753 344655 := bstep (se 1 (by rfl) ⟨258491, by rfl⟩ : syracuseStep 344655 = 516983) B516983
theorem B344671 : Blo 342753 344671 := bstep (se 1 (by rfl) ⟨258503, by rfl⟩ : syracuseStep 344671 = 517007) B517007
theorem B344699 : Blo 342753 344699 := bstep (se 1 (by rfl) ⟨258524, by rfl⟩ : syracuseStep 344699 = 517049) B517049
theorem B1163915 : Blo 342753 1163915 := bstep (se 1 (by rfl) ⟨872936, by rfl⟩ : syracuseStep 1163915 = 1745873) B1745873
theorem B344751 : Blo 342753 344751 := bstep (se 1 (by rfl) ⟨258563, by rfl⟩ : syracuseStep 344751 = 517127) B517127
theorem B344775 : Blo 342753 344775 := bstep (se 1 (by rfl) ⟨258581, by rfl⟩ : syracuseStep 344775 = 517163) B517163
theorem B1753811 : Blo 342753 1753811 := bstep (se 1 (by rfl) ⟨1315358, by rfl⟩ : syracuseStep 1753811 = 2630717) B2630717
theorem B344795 : Blo 342753 344795 := bstep (se 1 (by rfl) ⟨258596, by rfl⟩ : syracuseStep 344795 = 517193) B517193
theorem B344871 : Blo 342753 344871 := bstep (se 1 (by rfl) ⟨258653, by rfl⟩ : syracuseStep 344871 = 517307) B517307
theorem B344911 : Blo 342753 344911 := bstep (se 1 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 344911 = 517367) B517367
theorem B344927 : Blo 342753 344927 := bstep (se 1 (by rfl) ⟨258695, by rfl⟩ : syracuseStep 344927 = 517391) B517391
theorem B2605931 : Blo 342753 2605931 := bstep (se 1 (by rfl) ⟨1954448, by rfl⟩ : syracuseStep 2605931 = 3908897) B3908897
theorem B344955 : Blo 342753 344955 := bstep (se 1 (by rfl) ⟨258716, by rfl⟩ : syracuseStep 344955 = 517433) B517433
theorem B345007 : Blo 342753 345007 := bstep (se 1 (by rfl) ⟨258755, by rfl⟩ : syracuseStep 345007 = 517511) B517511
theorem B345031 : Blo 342753 345031 := bstep (se 1 (by rfl) ⟨258773, by rfl⟩ : syracuseStep 345031 = 517547) B517547
theorem B345051 : Blo 342753 345051 := bstep (se 1 (by rfl) ⟨258788, by rfl⟩ : syracuseStep 345051 = 517577) B517577
theorem B345127 : Blo 342753 345127 := bstep (se 1 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 345127 = 517691) B517691
theorem B345167 : Blo 342753 345167 := bstep (se 1 (by rfl) ⟨258875, by rfl⟩ : syracuseStep 345167 = 517751) B517751
theorem B345183 : Blo 342753 345183 := bstep (se 1 (by rfl) ⟨258887, by rfl⟩ : syracuseStep 345183 = 517775) B517775
theorem B345211 : Blo 342753 345211 := bstep (se 1 (by rfl) ⟨258908, by rfl⟩ : syracuseStep 345211 = 517817) B517817
theorem B3949721 : Blo 342753 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B1197227 : Blo 342753 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B345263 : Blo 342753 345263 := bstep (se 1 (by rfl) ⟨258947, by rfl⟩ : syracuseStep 345263 = 517895) B517895
theorem B345287 : Blo 342753 345287 := bstep (se 1 (by rfl) ⟨258965, by rfl⟩ : syracuseStep 345287 = 517931) B517931
theorem B345307 : Blo 342753 345307 := bstep (se 1 (by rfl) ⟨258980, by rfl⟩ : syracuseStep 345307 = 517961) B517961
theorem B345383 : Blo 342753 345383 := bstep (se 1 (by rfl) ⟨259037, by rfl⟩ : syracuseStep 345383 = 518075) B518075
theorem B345423 : Blo 342753 345423 := bstep (se 1 (by rfl) ⟨259067, by rfl⟩ : syracuseStep 345423 = 518135) B518135
theorem B345439 : Blo 342753 345439 := bstep (se 1 (by rfl) ⟨259079, by rfl⟩ : syracuseStep 345439 = 518159) B518159
theorem B869737 : Blo 342753 869737 := bstep (se 2 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 869737 = 652303) B652303
theorem B345467 : Blo 342753 345467 := bstep (se 1 (by rfl) ⟨259100, by rfl⟩ : syracuseStep 345467 = 518201) B518201
theorem B345519 : Blo 342753 345519 := bstep (se 1 (by rfl) ⟨259139, by rfl⟩ : syracuseStep 345519 = 518279) B518279
theorem B345543 : Blo 342753 345543 := bstep (se 1 (by rfl) ⟨259157, by rfl⟩ : syracuseStep 345543 = 518315) B518315
theorem B345563 : Blo 342753 345563 := bstep (se 1 (by rfl) ⟨259172, by rfl⟩ : syracuseStep 345563 = 518345) B518345
theorem B1164833 : Blo 342753 1164833 := bstep (se 2 (by rfl) ⟨436812, by rfl⟩ : syracuseStep 1164833 = 873625) B873625
theorem B771623 : Blo 342753 771623 := bstep (se 1 (by rfl) ⟨578717, by rfl⟩ : syracuseStep 771623 = 1157435) B1157435
theorem B345639 : Blo 342753 345639 := bstep (se 1 (by rfl) ⟨259229, by rfl⟩ : syracuseStep 345639 = 518459) B518459
theorem B345679 : Blo 342753 345679 := bstep (se 1 (by rfl) ⟨259259, by rfl⟩ : syracuseStep 345679 = 518519) B518519
theorem B345695 : Blo 342753 345695 := bstep (se 1 (by rfl) ⟨259271, by rfl⟩ : syracuseStep 345695 = 518543) B518543
theorem B870011 : Blo 342753 870011 := bstep (se 1 (by rfl) ⟨652508, by rfl⟩ : syracuseStep 870011 = 1305017) B1305017
theorem B345723 : Blo 342753 345723 := bstep (se 1 (by rfl) ⟨259292, by rfl⟩ : syracuseStep 345723 = 518585) B518585
theorem B345775 : Blo 342753 345775 := bstep (se 1 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 345775 = 518663) B518663
theorem B345799 : Blo 342753 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B345819 : Blo 342753 345819 := bstep (se 1 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 345819 = 518729) B518729
theorem B1165049 : Blo 342753 1165049 := bstep (se 2 (by rfl) ⟨436893, by rfl⟩ : syracuseStep 1165049 = 873787) B873787
theorem B345895 : Blo 342753 345895 := bstep (se 1 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 345895 = 518843) B518843
theorem B345935 : Blo 342753 345935 := bstep (se 1 (by rfl) ⟨259451, by rfl⟩ : syracuseStep 345935 = 518903) B518903
theorem B345951 : Blo 342753 345951 := bstep (se 1 (by rfl) ⟨259463, by rfl⟩ : syracuseStep 345951 = 518927) B518927
theorem B771947 : Blo 342753 771947 := bstep (se 1 (by rfl) ⟨578960, by rfl⟩ : syracuseStep 771947 = 1157921) B1157921
theorem B345979 : Blo 342753 345979 := bstep (se 1 (by rfl) ⟨259484, by rfl⟩ : syracuseStep 345979 = 518969) B518969
theorem B772001 : Blo 342753 772001 := bstep (se 2 (by rfl) ⟨289500, by rfl⟩ : syracuseStep 772001 = 579001) B579001
theorem B346031 : Blo 342753 346031 := bstep (se 1 (by rfl) ⟨259523, by rfl⟩ : syracuseStep 346031 = 519047) B519047
theorem B346055 : Blo 342753 346055 := bstep (se 1 (by rfl) ⟨259541, by rfl⟩ : syracuseStep 346055 = 519083) B519083
theorem B346075 : Blo 342753 346075 := bstep (se 1 (by rfl) ⟨259556, by rfl⟩ : syracuseStep 346075 = 519113) B519113
theorem B1099777 : Blo 342753 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B1165319 : Blo 342753 1165319 := bstep (se 1 (by rfl) ⟨873989, by rfl⟩ : syracuseStep 1165319 = 1747979) B1747979
theorem B346151 : Blo 342753 346151 := bstep (se 1 (by rfl) ⟨259613, by rfl⟩ : syracuseStep 346151 = 519227) B519227
theorem B346191 : Blo 342753 346191 := bstep (se 1 (by rfl) ⟨259643, by rfl⟩ : syracuseStep 346191 = 519287) B519287
theorem B346207 : Blo 342753 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B1165427 : Blo 342753 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B346235 : Blo 342753 346235 := bstep (se 1 (by rfl) ⟨259676, by rfl⟩ : syracuseStep 346235 = 519353) B519353
theorem B346287 : Blo 342753 346287 := bstep (se 1 (by rfl) ⟨259715, by rfl⟩ : syracuseStep 346287 = 519431) B519431
theorem B346311 : Blo 342753 346311 := bstep (se 1 (by rfl) ⟨259733, by rfl⟩ : syracuseStep 346311 = 519467) B519467
theorem B346331 : Blo 342753 346331 := bstep (se 1 (by rfl) ⟨259748, by rfl⟩ : syracuseStep 346331 = 519497) B519497
theorem B772343 : Blo 342753 772343 := bstep (se 1 (by rfl) ⟨579257, by rfl⟩ : syracuseStep 772343 = 1158515) B1158515
theorem B346407 : Blo 342753 346407 := bstep (se 1 (by rfl) ⟨259805, by rfl⟩ : syracuseStep 346407 = 519611) B519611
theorem B346447 : Blo 342753 346447 := bstep (se 1 (by rfl) ⟨259835, by rfl⟩ : syracuseStep 346447 = 519671) B519671
theorem B346463 : Blo 342753 346463 := bstep (se 1 (by rfl) ⟨259847, by rfl⟩ : syracuseStep 346463 = 519695) B519695
theorem B346491 : Blo 342753 346491 := bstep (se 1 (by rfl) ⟨259868, by rfl⟩ : syracuseStep 346491 = 519737) B519737
theorem B1165697 : Blo 342753 1165697 := bstep (se 2 (by rfl) ⟨437136, by rfl⟩ : syracuseStep 1165697 = 874273) B874273
theorem B346543 : Blo 342753 346543 := bstep (se 1 (by rfl) ⟨259907, by rfl⟩ : syracuseStep 346543 = 519815) B519815
theorem B346567 : Blo 342753 346567 := bstep (se 1 (by rfl) ⟨259925, by rfl⟩ : syracuseStep 346567 = 519851) B519851
theorem B346587 : Blo 342753 346587 := bstep (se 1 (by rfl) ⟨259940, by rfl⟩ : syracuseStep 346587 = 519881) B519881
theorem B346663 : Blo 342753 346663 := bstep (se 1 (by rfl) ⟨259997, by rfl⟩ : syracuseStep 346663 = 519995) B519995
theorem B346703 : Blo 342753 346703 := bstep (se 1 (by rfl) ⟨260027, by rfl⟩ : syracuseStep 346703 = 520055) B520055
theorem B346719 : Blo 342753 346719 := bstep (se 1 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 346719 = 520079) B520079
theorem B346747 : Blo 342753 346747 := bstep (se 1 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 346747 = 520121) B520121
theorem B1395409 : Blo 342753 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B2607875 : Blo 342753 2607875 := bstep (se 1 (by rfl) ⟨1955906, by rfl⟩ : syracuseStep 2607875 = 3911813) B3911813
theorem B772937 : Blo 342753 772937 := bstep (se 2 (by rfl) ⟨289851, by rfl⟩ : syracuseStep 772937 = 579703) B579703
theorem B1166507 : Blo 342753 1166507 := bstep (se 1 (by rfl) ⟨874880, by rfl⟩ : syracuseStep 1166507 = 1749761) B1749761
theorem B871823 : Blo 342753 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B413147 : Blo 342753 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B1396187 : Blo 342753 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B60182003 : Blo 342753 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B773729 : Blo 342753 773729 := bstep (se 2 (by rfl) ⟨290148, by rfl⟩ : syracuseStep 773729 = 580297) B580297
theorem B1167047 : Blo 342753 1167047 := bstep (se 1 (by rfl) ⟨875285, by rfl⟩ : syracuseStep 1167047 = 1750571) B1750571
theorem B872147 : Blo 342753 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B2215673 : Blo 342753 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B774071 : Blo 342753 774071 := bstep (se 1 (by rfl) ⟨580553, by rfl⟩ : syracuseStep 774071 = 1161107) B1161107
theorem B1953881 : Blo 342753 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B1331585 : Blo 342753 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B1954313 : Blo 342753 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B774665 : Blo 342753 774665 := bstep (se 2 (by rfl) ⟨290499, by rfl⟩ : syracuseStep 774665 = 580999) B580999
theorem B1167911 : Blo 342753 1167911 := bstep (se 1 (by rfl) ⟨875933, by rfl⟩ : syracuseStep 1167911 = 1751867) B1751867
theorem B1168019 : Blo 342753 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B3330733 : Blo 342753 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B5952211 : Blo 342753 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B775007 : Blo 342753 775007 := bstep (se 1 (by rfl) ⟨581255, by rfl⟩ : syracuseStep 775007 = 1162511) B1162511
theorem B1168235 : Blo 342753 1168235 := bstep (se 1 (by rfl) ⟨876176, by rfl⟩ : syracuseStep 1168235 = 1752353) B1752353
theorem B1168289 : Blo 342753 1168289 := bstep (se 2 (by rfl) ⟨438108, by rfl⟩ : syracuseStep 1168289 = 876217) B876217
theorem B578569 : Blo 342753 578569 := bstep (se 2 (by rfl) ⟨216963, by rfl⟩ : syracuseStep 578569 = 433927) B433927
theorem B775187 : Blo 342753 775187 := bstep (se 1 (by rfl) ⟨581390, by rfl⟩ : syracuseStep 775187 = 1162781) B1162781
theorem B578731 : Blo 342753 578731 := bstep (se 1 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 578731 = 868097) B868097
theorem B775529 : Blo 342753 775529 := bstep (se 2 (by rfl) ⟨290823, by rfl⟩ : syracuseStep 775529 = 581647) B581647
theorem B579035 : Blo 342753 579035 := bstep (se 1 (by rfl) ⟨434276, by rfl⟩ : syracuseStep 579035 = 868553) B868553
theorem B1168883 : Blo 342753 1168883 := bstep (se 1 (by rfl) ⟨876662, by rfl⟩ : syracuseStep 1168883 = 1753325) B1753325
theorem B579271 : Blo 342753 579271 := bstep (se 1 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 579271 = 868907) B868907
theorem B2807585 : Blo 342753 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B579433 : Blo 342753 579433 := bstep (se 2 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 579433 = 434575) B434575
theorem B874415 : Blo 342753 874415 := bstep (se 1 (by rfl) ⟨655811, by rfl⟩ : syracuseStep 874415 = 1311623) B1311623
theorem B1955771 : Blo 342753 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B776123 : Blo 342753 776123 := bstep (se 1 (by rfl) ⟨582092, by rfl⟩ : syracuseStep 776123 = 1164185) B1164185
theorem B1300411 : Blo 342753 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B1169423 : Blo 342753 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B776249 : Blo 342753 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B2611277 : Blo 342753 2611277 := bstep (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) B979229
theorem B2480291 : Blo 342753 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B1104043 : Blo 342753 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B514247 : Blo 342753 514247 := bstep (se 1 (by rfl) ⟨385685, by rfl⟩ : syracuseStep 514247 = 771371) B771371
theorem B11163905 : Blo 342753 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B514409 : Blo 342753 514409 := bstep (se 2 (by rfl) ⟨192903, by rfl⟩ : syracuseStep 514409 = 385807) B385807
theorem B416107 : Blo 342753 416107 := bstep (se 1 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 416107 = 624161) B624161
theorem B776591 : Blo 342753 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B514487 : Blo 342753 514487 := bstep (se 1 (by rfl) ⟨385865, by rfl⟩ : syracuseStep 514487 = 771731) B771731
theorem B580027 : Blo 342753 580027 := bstep (se 1 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 580027 = 870041) B870041
theorem B514523 : Blo 342753 514523 := bstep (se 1 (by rfl) ⟨385892, by rfl⟩ : syracuseStep 514523 = 771785) B771785
theorem B875033 : Blo 342753 875033 := bstep (se 2 (by rfl) ⟨328137, by rfl⟩ : syracuseStep 875033 = 656275) B656275
theorem B580135 : Blo 342753 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B45439541 : Blo 342753 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B1170017 : Blo 342753 1170017 := bstep (se 2 (by rfl) ⟨438756, by rfl⟩ : syracuseStep 1170017 = 877513) B877513
theorem B2218697 : Blo 342753 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B776915 : Blo 342753 776915 := bstep (se 1 (by rfl) ⟨582686, by rfl⟩ : syracuseStep 776915 = 1165373) B1165373
theorem B1334045 : Blo 342753 1334045 := bstep (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) B500267
theorem B580459 : Blo 342753 580459 := bstep (se 1 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 580459 = 870689) B870689
theorem B514991 : Blo 342753 514991 := bstep (se 1 (by rfl) ⟨386243, by rfl⟩ : syracuseStep 514991 = 772487) B772487
theorem B515081 : Blo 342753 515081 := bstep (se 2 (by rfl) ⟨193155, by rfl⟩ : syracuseStep 515081 = 386311) B386311
theorem B515111 : Blo 342753 515111 := bstep (se 1 (by rfl) ⟨386333, by rfl⟩ : syracuseStep 515111 = 772667) B772667
theorem B515195 : Blo 342753 515195 := bstep (se 1 (by rfl) ⟨386396, by rfl⟩ : syracuseStep 515195 = 772793) B772793
theorem B515321 : Blo 342753 515321 := bstep (se 2 (by rfl) ⟨193245, by rfl⟩ : syracuseStep 515321 = 386491) B386491
theorem B515423 : Blo 342753 515423 := bstep (se 1 (by rfl) ⟨386567, by rfl⟩ : syracuseStep 515423 = 773135) B773135
theorem B1236329 : Blo 342753 1236329 := bstep (se 2 (by rfl) ⟨463623, by rfl⟩ : syracuseStep 1236329 = 927247) B927247
theorem B515435 : Blo 342753 515435 := bstep (se 1 (by rfl) ⟨386576, by rfl⟩ : syracuseStep 515435 = 773153) B773153
theorem B1301903 : Blo 342753 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B515663 : Blo 342753 515663 := bstep (se 1 (by rfl) ⟨386747, by rfl⟩ : syracuseStep 515663 = 773495) B773495
theorem B777851 : Blo 342753 777851 := bstep (se 1 (by rfl) ⟨583388, by rfl⟩ : syracuseStep 777851 = 1166777) B1166777
theorem B6610571 : Blo 342753 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B515783 : Blo 342753 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B777977 : Blo 342753 777977 := bstep (se 2 (by rfl) ⟨291741, by rfl⟩ : syracuseStep 777977 = 583483) B583483
theorem B515945 : Blo 342753 515945 := bstep (se 2 (by rfl) ⟨193479, by rfl⟩ : syracuseStep 515945 = 386959) B386959
theorem B581519 : Blo 342753 581519 := bstep (se 1 (by rfl) ⟨436139, by rfl⟩ : syracuseStep 581519 = 872279) B872279
theorem B1105825 : Blo 342753 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B516023 : Blo 342753 516023 := bstep (se 1 (by rfl) ⟨387017, by rfl⟩ : syracuseStep 516023 = 774035) B774035
theorem B516059 : Blo 342753 516059 := bstep (se 1 (by rfl) ⟨387044, by rfl⟩ : syracuseStep 516059 = 774089) B774089
theorem B778247 : Blo 342753 778247 := bstep (se 1 (by rfl) ⟨583685, by rfl⟩ : syracuseStep 778247 = 1167371) B1167371
theorem B778319 : Blo 342753 778319 := bstep (se 1 (by rfl) ⟨583739, by rfl⟩ : syracuseStep 778319 = 1167479) B1167479
theorem B1958003 : Blo 342753 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1859699 : Blo 342753 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B1794163 : Blo 342753 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B581755 : Blo 342753 581755 := bstep (se 1 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 581755 = 872633) B872633
theorem B6283493 : Blo 342753 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B516527 : Blo 342753 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B2613707 : Blo 342753 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B778715 : Blo 342753 778715 := bstep (se 1 (by rfl) ⟨584036, by rfl⟩ : syracuseStep 778715 = 1168073) B1168073
theorem B516617 : Blo 342753 516617 := bstep (se 2 (by rfl) ⟨193731, by rfl⟩ : syracuseStep 516617 = 387463) B387463
theorem B1303073 : Blo 342753 1303073 := bstep (se 2 (by rfl) ⟨488652, by rfl⟩ : syracuseStep 1303073 = 977305) B977305
theorem B516647 : Blo 342753 516647 := bstep (se 1 (by rfl) ⟨387485, by rfl⟩ : syracuseStep 516647 = 774971) B774971
theorem B549433 : Blo 342753 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B516731 : Blo 342753 516731 := bstep (se 1 (by rfl) ⟨387548, by rfl⟩ : syracuseStep 516731 = 775097) B775097
theorem B11231885 : Blo 342753 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B385735 : Blo 342753 385735 := bstep (se 1 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 385735 = 578603) B578603
theorem B516857 : Blo 342753 516857 := bstep (se 2 (by rfl) ⟨193821, by rfl⟩ : syracuseStep 516857 = 387643) B387643
theorem B1565513 : Blo 342753 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B1303391 : Blo 342753 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B516959 : Blo 342753 516959 := bstep (se 1 (by rfl) ⟨387719, by rfl⟩ : syracuseStep 516959 = 775439) B775439
theorem B516971 : Blo 342753 516971 := bstep (se 1 (by rfl) ⟨387728, by rfl⟩ : syracuseStep 516971 = 775457) B775457
theorem B779183 : Blo 342753 779183 := bstep (se 1 (by rfl) ⟨584387, by rfl⟩ : syracuseStep 779183 = 1168775) B1168775
theorem B582619 : Blo 342753 582619 := bstep (se 1 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 582619 = 873929) B873929
theorem B1303559 : Blo 342753 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B877625 : Blo 342753 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B517199 : Blo 342753 517199 := bstep (se 1 (by rfl) ⟨387899, by rfl⟩ : syracuseStep 517199 = 775799) B775799
theorem B779435 : Blo 342753 779435 := bstep (se 1 (by rfl) ⟨584576, by rfl⟩ : syracuseStep 779435 = 1169153) B1169153
theorem B517319 : Blo 342753 517319 := bstep (se 1 (by rfl) ⟨387989, by rfl⟩ : syracuseStep 517319 = 775979) B775979
theorem B517481 : Blo 342753 517481 := bstep (se 2 (by rfl) ⟨194055, by rfl⟩ : syracuseStep 517481 = 388111) B388111
theorem B517559 : Blo 342753 517559 := bstep (se 1 (by rfl) ⟨388169, by rfl⟩ : syracuseStep 517559 = 776339) B776339
theorem B517595 : Blo 342753 517595 := bstep (se 1 (by rfl) ⟨388196, by rfl⟩ : syracuseStep 517595 = 776393) B776393
theorem B1304045 : Blo 342753 1304045 := bstep (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) B489017
theorem B4941323 : Blo 342753 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B1238561 : Blo 342753 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B386599 : Blo 342753 386599 := bstep (se 1 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 386599 = 579899) B579899
theorem B583247 : Blo 342753 583247 := bstep (se 1 (by rfl) ⟨437435, by rfl⟩ : syracuseStep 583247 = 874871) B874871
theorem B779975 : Blo 342753 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B1304363 : Blo 342753 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B518063 : Blo 342753 518063 := bstep (se 1 (by rfl) ⟨388547, by rfl⟩ : syracuseStep 518063 = 777095) B777095
theorem B550919 : Blo 342753 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B518153 : Blo 342753 518153 := bstep (se 2 (by rfl) ⟨194307, by rfl⟩ : syracuseStep 518153 = 388615) B388615
theorem B518183 : Blo 342753 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B518267 : Blo 342753 518267 := bstep (se 1 (by rfl) ⟨388700, by rfl⟩ : syracuseStep 518267 = 777401) B777401
theorem B11954309 : Blo 342753 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B518393 : Blo 342753 518393 := bstep (se 2 (by rfl) ⟨194397, by rfl⟩ : syracuseStep 518393 = 388795) B388795
theorem B518495 : Blo 342753 518495 := bstep (se 1 (by rfl) ⟨388871, by rfl⟩ : syracuseStep 518495 = 777743) B777743
theorem B518507 : Blo 342753 518507 := bstep (se 1 (by rfl) ⟨388880, by rfl⟩ : syracuseStep 518507 = 777761) B777761
theorem B1108349 : Blo 342753 1108349 := bstep (se 3 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 1108349 = 415631) B415631
theorem B584111 : Blo 342753 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B518735 : Blo 342753 518735 := bstep (se 1 (by rfl) ⟨389051, by rfl⟩ : syracuseStep 518735 = 778103) B778103
theorem B4975289 : Blo 342753 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B518855 : Blo 342753 518855 := bstep (se 1 (by rfl) ⟨389141, by rfl⟩ : syracuseStep 518855 = 778283) B778283
theorem B2616137 : Blo 342753 2616137 := bstep (se 2 (by rfl) ⟨981051, by rfl⟩ : syracuseStep 2616137 = 1962103) B1962103
theorem B3533645 : Blo 342753 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B584543 : Blo 342753 584543 := bstep (se 1 (by rfl) ⟨438407, by rfl⟩ : syracuseStep 584543 = 876815) B876815
theorem B551785 : Blo 342753 551785 := bstep (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) B413839
theorem B519017 : Blo 342753 519017 := bstep (se 2 (by rfl) ⟨194631, by rfl⟩ : syracuseStep 519017 = 389263) B389263
theorem B977771 : Blo 342753 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B2550635 : Blo 342753 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B9890707 : Blo 342753 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B519095 : Blo 342753 519095 := bstep (se 1 (by rfl) ⟨389321, by rfl⟩ : syracuseStep 519095 = 778643) B778643
theorem B519131 : Blo 342753 519131 := bstep (se 1 (by rfl) ⟨389348, by rfl⟩ : syracuseStep 519131 = 778697) B778697
theorem B388219 : Blo 342753 388219 := bstep (se 1 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 388219 = 582329) B582329
theorem B4418833 : Blo 342753 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B6319397 : Blo 342753 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B585103 : Blo 342753 585103 := bstep (se 1 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 585103 = 877655) B877655
theorem B519599 : Blo 342753 519599 := bstep (se 1 (by rfl) ⟨389699, by rfl⟩ : syracuseStep 519599 = 779399) B779399
theorem B552457 : Blo 342753 552457 := bstep (se 2 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 552457 = 414343) B414343
theorem B519689 : Blo 342753 519689 := bstep (se 2 (by rfl) ⟨194883, by rfl⟩ : syracuseStep 519689 = 389767) B389767
theorem B2485799 : Blo 342753 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B519719 : Blo 342753 519719 := bstep (se 1 (by rfl) ⟨389789, by rfl⟩ : syracuseStep 519719 = 779579) B779579
theorem B388687 : Blo 342753 388687 := bstep (se 1 (by rfl) ⟨291515, by rfl⟩ : syracuseStep 388687 = 583031) B583031
theorem B519803 : Blo 342753 519803 := bstep (se 1 (by rfl) ⟨389852, by rfl⟩ : syracuseStep 519803 = 779705) B779705
theorem B519929 : Blo 342753 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B520031 : Blo 342753 520031 := bstep (se 1 (by rfl) ⟨390023, by rfl⟩ : syracuseStep 520031 = 780047) B780047
theorem B1306475 : Blo 342753 1306475 := bstep (se 1 (by rfl) ⟨979856, by rfl⟩ : syracuseStep 1306475 = 1959713) B1959713
theorem B520043 : Blo 342753 520043 := bstep (se 1 (by rfl) ⟨390032, by rfl⟩ : syracuseStep 520043 = 780065) B780065
theorem B1961921 : Blo 342753 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B389083 : Blo 342753 389083 := bstep (se 1 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 389083 = 583625) B583625
theorem B1110131 : Blo 342753 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B5566643 : Blo 342753 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B389551 : Blo 342753 389551 := bstep (se 1 (by rfl) ⟨292163, by rfl⟩ : syracuseStep 389551 = 584327) B584327
theorem B2782025 : Blo 342753 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B389983 : Blo 342753 389983 := bstep (se 1 (by rfl) ⟨292487, by rfl⟩ : syracuseStep 389983 = 584975) B584975
theorem B553835 : Blo 342753 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B1045583 : Blo 342753 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B16840037 : Blo 342753 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B2717093 : Blo 342753 2717093 := bstep (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) B509455
theorem B1177051 : Blo 342753 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B6616565 : Blo 342753 6616565 := bstep (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) B620303
theorem B620203 : Blo 342753 620203 := bstep (se 1 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 620203 = 930305) B930305
theorem B5994283 : Blo 342753 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B653275 : Blo 342753 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B1472519 : Blo 342753 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B653321 : Blo 342753 653321 := bstep (se 2 (by rfl) ⟨244995, by rfl⟩ : syracuseStep 653321 = 489991) B489991
theorem B8976541 : Blo 342753 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B1308919 : Blo 342753 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B653663 : Blo 342753 653663 := bstep (se 1 (by rfl) ⟨490247, by rfl⟩ : syracuseStep 653663 = 980495) B980495
theorem B1309193 : Blo 342753 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B1309223 : Blo 342753 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B523115 : Blo 342753 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B10648709 : Blo 342753 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B1309891 : Blo 342753 1309891 := bstep (se 1 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 1309891 = 1964837) B1964837
theorem B654779 : Blo 342753 654779 := bstep (se 1 (by rfl) ⟨491084, by rfl⟩ : syracuseStep 654779 = 982169) B982169
theorem B1310195 : Blo 342753 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B1736315 : Blo 342753 1736315 := bstep (se 1 (by rfl) ⟨1302236, by rfl⟩ : syracuseStep 1736315 = 2604473) B2604473
theorem B622279 : Blo 342753 622279 := bstep (se 1 (by rfl) ⟨466709, by rfl⟩ : syracuseStep 622279 = 933419) B933419
theorem B655265 : Blo 342753 655265 := bstep (se 2 (by rfl) ⟨245724, by rfl⟩ : syracuseStep 655265 = 491449) B491449
theorem B1310651 : Blo 342753 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B2949169 : Blo 342753 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B2392217 : Blo 342753 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1245395 : Blo 342753 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B1736963 : Blo 342753 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B1737287 : Blo 342753 1737287 := bstep (se 1 (by rfl) ⟨1302965, by rfl⟩ : syracuseStep 1737287 = 2605931) B2605931
theorem B1573793 : Blo 342753 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B1312109 : Blo 342753 1312109 := bstep (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) B492041
theorem B886153 : Blo 342753 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B1312139 : Blo 342753 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B3933683 : Blo 342753 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B657209 : Blo 342753 657209 := bstep (se 2 (by rfl) ⟨246453, by rfl⟩ : syracuseStep 657209 = 492907) B492907
theorem B1738583 : Blo 342753 1738583 := bstep (se 1 (by rfl) ⟨1303937, by rfl⟩ : syracuseStep 1738583 = 2607875) B2607875
theorem B1476893 : Blo 342753 1476893 := bstep (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) B553835
theorem B1673597 : Blo 342753 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B1477115 : Blo 342753 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B657983 : Blo 342753 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B887723 : Blo 342753 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B1313779 : Blo 342753 1313779 := bstep (se 1 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 1313779 = 1970669) B1970669
theorem B1314539 : Blo 342753 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B790327 : Blo 342753 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1871723 : Blo 342753 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B1740851 : Blo 342753 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B7442603 : Blo 342753 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B1315025 : Blo 342753 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B2363755 : Blo 342753 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B1479131 : Blo 342753 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B889363 : Blo 342753 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B1315511 : Blo 342753 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B1774295 : Blo 342753 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B824219 : Blo 342753 824219 := bstep (se 1 (by rfl) ⟨618164, by rfl⟩ : syracuseStep 824219 = 1236329) B1236329
theorem B13407437 : Blo 342753 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1742471 : Blo 342753 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B8395109 : Blo 342753 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B825707 : Blo 342753 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B531065 : Blo 342753 531065 := bstep (se 2 (by rfl) ⟨199149, by rfl⟩ : syracuseStep 531065 = 398299) B398299
theorem B3316859 : Blo 342753 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2628773 : Blo 342753 2628773 := bstep (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) B492895
theorem B1744091 : Blo 342753 1744091 := bstep (se 1 (by rfl) ⟨1308068, by rfl⟩ : syracuseStep 1744091 = 2616137) B2616137
theorem B826937 : Blo 342753 826937 := bstep (se 2 (by rfl) ⟨310101, by rfl⟩ : syracuseStep 826937 = 620203) B620203
theorem B466607 : Blo 342753 466607 := bstep (se 1 (by rfl) ⟨349955, by rfl⟩ : syracuseStep 466607 = 699911) B699911
theorem B8363969 : Blo 342753 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B3711095 : Blo 342753 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B11968721 : Blo 342753 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1745225 : Blo 342753 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B697055 : Blo 342753 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B16851725 : Blo 342753 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B1811395 : Blo 342753 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B435547 : Blo 342753 435547 := bstep (se 1 (by rfl) ⟨326660, by rfl⟩ : syracuseStep 435547 = 653321) B653321
theorem B435775 : Blo 342753 435775 := bstep (se 1 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 435775 = 653663) B653663
theorem B1746521 : Blo 342753 1746521 := bstep (se 2 (by rfl) ⟨654945, by rfl⟩ : syracuseStep 1746521 = 1309891) B1309891
theorem B829705 : Blo 342753 829705 := bstep (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) B622279
theorem B436519 : Blo 342753 436519 := bstep (se 1 (by rfl) ⟨327389, by rfl⟩ : syracuseStep 436519 = 654779) B654779
theorem B1157543 : Blo 342753 1157543 := bstep (se 1 (by rfl) ⟨868157, by rfl⟩ : syracuseStep 1157543 = 1736315) B1736315
theorem B1157705 : Blo 342753 1157705 := bstep (se 2 (by rfl) ⟨434139, by rfl⟩ : syracuseStep 1157705 = 868279) B868279
theorem B436843 : Blo 342753 436843 := bstep (se 1 (by rfl) ⟨327632, by rfl⟩ : syracuseStep 436843 = 655265) B655265
theorem B3910355 : Blo 342753 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B437071 : Blo 342753 437071 := bstep (se 1 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 437071 = 655607) B655607
theorem B3189725 : Blo 342753 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B15051845 : Blo 342753 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B732577 : Blo 342753 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B2633147 : Blo 342753 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B830935 : Blo 342753 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B1159379 : Blo 342753 1159379 := bstep (se 1 (by rfl) ⟨869534, by rfl⟩ : syracuseStep 1159379 = 1739069) B1739069
theorem B1159649 : Blo 342753 1159649 := bstep (se 2 (by rfl) ⟨434868, by rfl⟩ : syracuseStep 1159649 = 869737) B869737
theorem B930791 : Blo 342753 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B40121335 : Blo 342753 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B832799 : Blo 342753 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B4208165 : Blo 342753 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B833107 : Blo 342753 833107 := bstep (se 1 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 833107 = 1249661) B1249661
theorem B1160891 : Blo 342753 1160891 := bstep (se 1 (by rfl) ⟨870668, by rfl⟩ : syracuseStep 1160891 = 1741337) B1741337
theorem B3192605 : Blo 342753 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B735713 : Blo 342753 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B13187609 : Blo 342753 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B1653527 : Blo 342753 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B342831 : Blo 342753 342831 := bstep (se 1 (by rfl) ⟨257123, by rfl⟩ : syracuseStep 342831 = 514247) B514247
theorem B342939 : Blo 342753 342939 := bstep (se 1 (by rfl) ⟨257204, by rfl⟩ : syracuseStep 342939 = 514409) B514409
theorem B342991 : Blo 342753 342991 := bstep (se 1 (by rfl) ⟨257243, by rfl⟩ : syracuseStep 342991 = 514487) B514487
theorem B343015 : Blo 342753 343015 := bstep (se 1 (by rfl) ⟨257261, by rfl⟩ : syracuseStep 343015 = 514523) B514523
theorem B30293027 : Blo 342753 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B343327 : Blo 342753 343327 := bstep (se 1 (by rfl) ⟨257495, by rfl⟩ : syracuseStep 343327 = 514991) B514991
theorem B343387 : Blo 342753 343387 := bstep (se 1 (by rfl) ⟨257540, by rfl⟩ : syracuseStep 343387 = 515081) B515081
theorem B736609 : Blo 342753 736609 := bstep (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) B552457
theorem B343407 : Blo 342753 343407 := bstep (se 1 (by rfl) ⟨257555, by rfl⟩ : syracuseStep 343407 = 515111) B515111
theorem B1621367 : Blo 342753 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B343463 : Blo 342753 343463 := bstep (se 1 (by rfl) ⟨257597, by rfl⟩ : syracuseStep 343463 = 515195) B515195
theorem B343547 : Blo 342753 343547 := bstep (se 1 (by rfl) ⟨257660, by rfl⟩ : syracuseStep 343547 = 515321) B515321
theorem B2473487 : Blo 342753 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B343615 : Blo 342753 343615 := bstep (se 1 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 343615 = 515423) B515423
theorem B343623 : Blo 342753 343623 := bstep (se 1 (by rfl) ⟨257717, by rfl⟩ : syracuseStep 343623 = 515435) B515435
theorem B1162835 : Blo 342753 1162835 := bstep (se 1 (by rfl) ⟨872126, by rfl⟩ : syracuseStep 1162835 = 1744253) B1744253
theorem B867935 : Blo 342753 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B343775 : Blo 342753 343775 := bstep (se 1 (by rfl) ⟨257831, by rfl⟩ : syracuseStep 343775 = 515663) B515663
theorem B4407047 : Blo 342753 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B1752839 : Blo 342753 1752839 := bstep (se 1 (by rfl) ⟨1314629, by rfl⟩ : syracuseStep 1752839 = 2629259) B2629259
theorem B343855 : Blo 342753 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B343963 : Blo 342753 343963 := bstep (se 1 (by rfl) ⟨257972, by rfl⟩ : syracuseStep 343963 = 515945) B515945
theorem B344015 : Blo 342753 344015 := bstep (se 1 (by rfl) ⟨258011, by rfl⟩ : syracuseStep 344015 = 516023) B516023
theorem B344039 : Blo 342753 344039 := bstep (se 1 (by rfl) ⟨258029, by rfl⟩ : syracuseStep 344039 = 516059) B516059
theorem B344351 : Blo 342753 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B344411 : Blo 342753 344411 := bstep (se 1 (by rfl) ⟨258308, by rfl⟩ : syracuseStep 344411 = 516617) B516617
theorem B868715 : Blo 342753 868715 := bstep (se 1 (by rfl) ⟨651536, by rfl⟩ : syracuseStep 868715 = 1303073) B1303073
theorem B344431 : Blo 342753 344431 := bstep (se 1 (by rfl) ⟨258323, by rfl⟩ : syracuseStep 344431 = 516647) B516647
theorem B344487 : Blo 342753 344487 := bstep (se 1 (by rfl) ⟨258365, by rfl⟩ : syracuseStep 344487 = 516731) B516731
theorem B7487923 : Blo 342753 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B344571 : Blo 342753 344571 := bstep (se 1 (by rfl) ⟨258428, by rfl⟩ : syracuseStep 344571 = 516857) B516857
theorem B868927 : Blo 342753 868927 := bstep (se 1 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 868927 = 1303391) B1303391
theorem B344639 : Blo 342753 344639 := bstep (se 1 (by rfl) ⟨258479, by rfl⟩ : syracuseStep 344639 = 516959) B516959
theorem B344647 : Blo 342753 344647 := bstep (se 1 (by rfl) ⟨258485, by rfl⟩ : syracuseStep 344647 = 516971) B516971
theorem B869039 : Blo 342753 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B344799 : Blo 342753 344799 := bstep (se 1 (by rfl) ⟨258599, by rfl⟩ : syracuseStep 344799 = 517199) B517199
theorem B344879 : Blo 342753 344879 := bstep (se 1 (by rfl) ⟨258659, by rfl⟩ : syracuseStep 344879 = 517319) B517319
theorem B4440977 : Blo 342753 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B344987 : Blo 342753 344987 := bstep (se 1 (by rfl) ⟨258740, by rfl⟩ : syracuseStep 344987 = 517481) B517481
theorem B345039 : Blo 342753 345039 := bstep (se 1 (by rfl) ⟨258779, by rfl⟩ : syracuseStep 345039 = 517559) B517559
theorem B345063 : Blo 342753 345063 := bstep (se 1 (by rfl) ⟨258797, by rfl⟩ : syracuseStep 345063 = 517595) B517595
theorem B869363 : Blo 342753 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B3294215 : Blo 342753 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B869575 : Blo 342753 869575 := bstep (se 1 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 869575 = 1304363) B1304363
theorem B345375 : Blo 342753 345375 := bstep (se 1 (by rfl) ⟨259031, by rfl⟩ : syracuseStep 345375 = 518063) B518063
theorem B345435 : Blo 342753 345435 := bstep (se 1 (by rfl) ⟨259076, by rfl⟩ : syracuseStep 345435 = 518153) B518153
theorem B771425 : Blo 342753 771425 := bstep (se 2 (by rfl) ⟨289284, by rfl⟩ : syracuseStep 771425 = 578569) B578569
theorem B345455 : Blo 342753 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B345511 : Blo 342753 345511 := bstep (se 1 (by rfl) ⟨259133, by rfl⟩ : syracuseStep 345511 = 518267) B518267
theorem B771515 : Blo 342753 771515 := bstep (se 1 (by rfl) ⟨578636, by rfl⟩ : syracuseStep 771515 = 1157273) B1157273
theorem B345595 : Blo 342753 345595 := bstep (se 1 (by rfl) ⟨259196, by rfl⟩ : syracuseStep 345595 = 518393) B518393
theorem B771641 : Blo 342753 771641 := bstep (se 2 (by rfl) ⟨289365, by rfl⟩ : syracuseStep 771641 = 578731) B578731
theorem B345663 : Blo 342753 345663 := bstep (se 1 (by rfl) ⟨259247, by rfl⟩ : syracuseStep 345663 = 518495) B518495
theorem B345671 : Blo 342753 345671 := bstep (se 1 (by rfl) ⟨259253, by rfl⟩ : syracuseStep 345671 = 518507) B518507
theorem B738899 : Blo 342753 738899 := bstep (se 1 (by rfl) ⟨554174, by rfl⟩ : syracuseStep 738899 = 1108349) B1108349
theorem B2934407 : Blo 342753 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2475677 : Blo 342753 2475677 := bstep (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) B928379
theorem B345823 : Blo 342753 345823 := bstep (se 1 (by rfl) ⟨259367, by rfl⟩ : syracuseStep 345823 = 518735) B518735
theorem B509743 : Blo 342753 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B345903 : Blo 342753 345903 := bstep (se 1 (by rfl) ⟨259427, by rfl⟩ : syracuseStep 345903 = 518855) B518855
theorem B346011 : Blo 342753 346011 := bstep (se 1 (by rfl) ⟨259508, by rfl⟩ : syracuseStep 346011 = 519017) B519017
theorem B346063 : Blo 342753 346063 := bstep (se 1 (by rfl) ⟨259547, by rfl⟩ : syracuseStep 346063 = 519095) B519095
theorem B346087 : Blo 342753 346087 := bstep (se 1 (by rfl) ⟨259565, by rfl⟩ : syracuseStep 346087 = 519131) B519131
theorem B9423053 : Blo 342753 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B772307 : Blo 342753 772307 := bstep (se 1 (by rfl) ⟨579230, by rfl⟩ : syracuseStep 772307 = 1158461) B1158461
theorem B772361 : Blo 342753 772361 := bstep (se 2 (by rfl) ⟨289635, by rfl⟩ : syracuseStep 772361 = 579271) B579271
theorem B2607389 : Blo 342753 2607389 := bstep (se 3 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 2607389 = 977771) B977771
theorem B346399 : Blo 342753 346399 := bstep (se 1 (by rfl) ⟨259799, by rfl⟩ : syracuseStep 346399 = 519599) B519599
theorem B346459 : Blo 342753 346459 := bstep (se 1 (by rfl) ⟨259844, by rfl⟩ : syracuseStep 346459 = 519689) B519689
theorem B1657199 : Blo 342753 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B346479 : Blo 342753 346479 := bstep (se 1 (by rfl) ⟨259859, by rfl⟩ : syracuseStep 346479 = 519719) B519719
theorem B346535 : Blo 342753 346535 := bstep (se 1 (by rfl) ⟨259901, by rfl⟩ : syracuseStep 346535 = 519803) B519803
theorem B1165751 : Blo 342753 1165751 := bstep (se 1 (by rfl) ⟨874313, by rfl⟩ : syracuseStep 1165751 = 1748627) B1748627
theorem B772577 : Blo 342753 772577 := bstep (se 2 (by rfl) ⟨289716, by rfl⟩ : syracuseStep 772577 = 579433) B579433
theorem B346619 : Blo 342753 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B346687 : Blo 342753 346687 := bstep (se 1 (by rfl) ⟨260015, by rfl⟩ : syracuseStep 346687 = 520031) B520031
theorem B870983 : Blo 342753 870983 := bstep (se 1 (by rfl) ⟨653237, by rfl⟩ : syracuseStep 870983 = 1306475) B1306475
theorem B346695 : Blo 342753 346695 := bstep (se 1 (by rfl) ⟨260021, by rfl⟩ : syracuseStep 346695 = 520043) B520043
theorem B871033 : Blo 342753 871033 := bstep (se 2 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 871033 = 653275) B653275
theorem B2214647 : Blo 342753 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B740087 : Blo 342753 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B772883 : Blo 342753 772883 := bstep (se 1 (by rfl) ⟨579662, by rfl⟩ : syracuseStep 772883 = 1159325) B1159325
theorem B1100699 : Blo 342753 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B773243 : Blo 342753 773243 := bstep (se 1 (by rfl) ⟨579932, by rfl⟩ : syracuseStep 773243 = 1159865) B1159865
theorem B1854683 : Blo 342753 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B773369 : Blo 342753 773369 := bstep (se 2 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 773369 = 580027) B580027
theorem B773513 : Blo 342753 773513 := bstep (se 2 (by rfl) ⟨290067, by rfl⟩ : syracuseStep 773513 = 580135) B580135
theorem B2805191 : Blo 342753 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B773639 : Blo 342753 773639 := bstep (se 1 (by rfl) ⟨580229, by rfl⟩ : syracuseStep 773639 = 1160459) B1160459
theorem B3624509 : Blo 342753 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B11226691 : Blo 342753 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B4411043 : Blo 342753 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B773819 : Blo 342753 773819 := bstep (se 1 (by rfl) ⟨580364, by rfl⟩ : syracuseStep 773819 = 1160729) B1160729
theorem B773945 : Blo 342753 773945 := bstep (se 2 (by rfl) ⟨290229, by rfl⟩ : syracuseStep 773945 = 580459) B580459
theorem B1101725 : Blo 342753 1101725 := bstep (se 3 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 1101725 = 413147) B413147
theorem B872795 : Blo 342753 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B872815 : Blo 342753 872815 := bstep (se 1 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 872815 = 1309223) B1309223
theorem B774575 : Blo 342753 774575 := bstep (se 1 (by rfl) ⟨580931, by rfl⟩ : syracuseStep 774575 = 1161863) B1161863
theorem B774611 : Blo 342753 774611 := bstep (se 1 (by rfl) ⟨580958, by rfl⟩ : syracuseStep 774611 = 1161917) B1161917
theorem B774719 : Blo 342753 774719 := bstep (se 1 (by rfl) ⟨581039, by rfl⟩ : syracuseStep 774719 = 1162079) B1162079
theorem B348743 : Blo 342753 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B774827 : Blo 342753 774827 := bstep (se 1 (by rfl) ⟨581120, by rfl⟩ : syracuseStep 774827 = 1162241) B1162241
theorem B7099139 : Blo 342753 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B873463 : Blo 342753 873463 := bstep (se 1 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 873463 = 1310195) B1310195
theorem B1725497 : Blo 342753 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B775367 : Blo 342753 775367 := bstep (se 1 (by rfl) ⟨581525, by rfl⟩ : syracuseStep 775367 = 1163051) B1163051
theorem B873767 : Blo 342753 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B775547 : Blo 342753 775547 := bstep (se 1 (by rfl) ⟨581660, by rfl⟩ : syracuseStep 775547 = 1163321) B1163321
theorem B1168829 : Blo 342753 1168829 := bstep (se 3 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 1168829 = 438311) B438311
theorem B775673 : Blo 342753 775673 := bstep (se 2 (by rfl) ⟨290877, by rfl⟩ : syracuseStep 775673 = 581755) B581755
theorem B775763 : Blo 342753 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B1660601 : Blo 342753 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B775943 : Blo 342753 775943 := bstep (se 1 (by rfl) ⟨581957, by rfl⟩ : syracuseStep 775943 = 1163915) B1163915
theorem B1169207 : Blo 342753 1169207 := bstep (se 1 (by rfl) ⟨876905, by rfl⟩ : syracuseStep 1169207 = 1753811) B1753811
theorem B1660753 : Blo 342753 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B514313 : Blo 342753 514313 := bstep (se 2 (by rfl) ⟨192867, by rfl⟩ : syracuseStep 514313 = 385735) B385735
theorem B1169693 : Blo 342753 1169693 := bstep (se 3 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 1169693 = 438635) B438635
theorem B776555 : Blo 342753 776555 := bstep (se 1 (by rfl) ⟨582416, by rfl⟩ : syracuseStep 776555 = 1164833) B1164833
theorem B514415 : Blo 342753 514415 := bstep (se 1 (by rfl) ⟨385811, by rfl⟩ : syracuseStep 514415 = 771623) B771623
theorem B416111 : Blo 342753 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B1464743 : Blo 342753 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B580007 : Blo 342753 580007 := bstep (se 1 (by rfl) ⟨435005, by rfl⟩ : syracuseStep 580007 = 870011) B870011
theorem B776699 : Blo 342753 776699 := bstep (se 1 (by rfl) ⟨582524, by rfl⟩ : syracuseStep 776699 = 1165049) B1165049
theorem B514631 : Blo 342753 514631 := bstep (se 1 (by rfl) ⟨385973, by rfl⟩ : syracuseStep 514631 = 771947) B771947
theorem B580169 : Blo 342753 580169 := bstep (se 2 (by rfl) ⟨217563, by rfl⟩ : syracuseStep 580169 = 435127) B435127
theorem B514667 : Blo 342753 514667 := bstep (se 1 (by rfl) ⟨386000, by rfl⟩ : syracuseStep 514667 = 772001) B772001
theorem B776825 : Blo 342753 776825 := bstep (se 2 (by rfl) ⟨291309, by rfl⟩ : syracuseStep 776825 = 582619) B582619
theorem B776879 : Blo 342753 776879 := bstep (se 1 (by rfl) ⟨582659, by rfl⟩ : syracuseStep 776879 = 1165319) B1165319
theorem B776951 : Blo 342753 776951 := bstep (se 1 (by rfl) ⟨582713, by rfl⟩ : syracuseStep 776951 = 1165427) B1165427
theorem B514895 : Blo 342753 514895 := bstep (se 1 (by rfl) ⟨386171, by rfl⟩ : syracuseStep 514895 = 772343) B772343
theorem B875407 : Blo 342753 875407 := bstep (se 1 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 875407 = 1313111) B1313111
theorem B777131 : Blo 342753 777131 := bstep (se 1 (by rfl) ⟨582848, by rfl⟩ : syracuseStep 777131 = 1165697) B1165697
theorem B515291 : Blo 342753 515291 := bstep (se 1 (by rfl) ⟨386468, by rfl⟩ : syracuseStep 515291 = 772937) B772937
theorem B2219237 : Blo 342753 2219237 := bstep (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) B416107
theorem B875873 : Blo 342753 875873 := bstep (se 2 (by rfl) ⟨328452, by rfl⟩ : syracuseStep 875873 = 656905) B656905
theorem B515465 : Blo 342753 515465 := bstep (se 2 (by rfl) ⟨193299, by rfl⟩ : syracuseStep 515465 = 386599) B386599
theorem B777671 : Blo 342753 777671 := bstep (se 1 (by rfl) ⟨583253, by rfl⟩ : syracuseStep 777671 = 1166507) B1166507
theorem B581215 : Blo 342753 581215 := bstep (se 1 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 581215 = 871823) B871823
theorem B515819 : Blo 342753 515819 := bstep (se 1 (by rfl) ⟨386864, by rfl⟩ : syracuseStep 515819 = 773729) B773729
theorem B876329 : Blo 342753 876329 := bstep (se 2 (by rfl) ⟨328623, by rfl⟩ : syracuseStep 876329 = 657247) B657247
theorem B778031 : Blo 342753 778031 := bstep (se 1 (by rfl) ⟨583523, by rfl⟩ : syracuseStep 778031 = 1167047) B1167047
theorem B581431 : Blo 342753 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B516047 : Blo 342753 516047 := bstep (se 1 (by rfl) ⟨387035, by rfl⟩ : syracuseStep 516047 = 774071) B774071
theorem B352231 : Blo 342753 352231 := bstep (se 1 (by rfl) ⟨264173, by rfl⟩ : syracuseStep 352231 = 528347) B528347
theorem B1466369 : Blo 342753 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B1302587 : Blo 342753 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B7561349 : Blo 342753 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B581897 : Blo 342753 581897 := bstep (se 2 (by rfl) ⟨218211, by rfl⟩ : syracuseStep 581897 = 436423) B436423
theorem B1302875 : Blo 342753 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B516443 : Blo 342753 516443 := bstep (se 1 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 516443 = 774665) B774665
theorem B778607 : Blo 342753 778607 := bstep (se 1 (by rfl) ⟨583955, by rfl⟩ : syracuseStep 778607 = 1167911) B1167911
theorem B778679 : Blo 342753 778679 := bstep (se 1 (by rfl) ⟨584009, by rfl⟩ : syracuseStep 778679 = 1168019) B1168019
theorem B516671 : Blo 342753 516671 := bstep (se 1 (by rfl) ⟨387503, by rfl⟩ : syracuseStep 516671 = 775007) B775007
theorem B778823 : Blo 342753 778823 := bstep (se 1 (by rfl) ⟨584117, by rfl⟩ : syracuseStep 778823 = 1168235) B1168235
theorem B778859 : Blo 342753 778859 := bstep (se 1 (by rfl) ⟨584144, by rfl⟩ : syracuseStep 778859 = 1168289) B1168289
theorem B516791 : Blo 342753 516791 := bstep (se 1 (by rfl) ⟨387593, by rfl⟩ : syracuseStep 516791 = 775187) B775187
theorem B877331 : Blo 342753 877331 := bstep (se 1 (by rfl) ⟨657998, by rfl⟩ : syracuseStep 877331 = 1315997) B1315997
theorem B517019 : Blo 342753 517019 := bstep (se 1 (by rfl) ⟨387764, by rfl⟩ : syracuseStep 517019 = 775529) B775529
theorem B1860545 : Blo 342753 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B386023 : Blo 342753 386023 := bstep (se 1 (by rfl) ⟨289517, by rfl⟩ : syracuseStep 386023 = 579035) B579035
theorem B779255 : Blo 342753 779255 := bstep (se 1 (by rfl) ⟨584441, by rfl⟩ : syracuseStep 779255 = 1168883) B1168883
theorem B31745125 : Blo 342753 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B582889 : Blo 342753 582889 := bstep (se 2 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 582889 = 437167) B437167
theorem B976121 : Blo 342753 976121 := bstep (se 2 (by rfl) ⟨366045, by rfl⟩ : syracuseStep 976121 = 732091) B732091
theorem B582943 : Blo 342753 582943 := bstep (se 1 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 582943 = 874415) B874415
theorem B1303847 : Blo 342753 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B517415 : Blo 342753 517415 := bstep (se 1 (by rfl) ⟨388061, by rfl⟩ : syracuseStep 517415 = 776123) B776123
theorem B1992023 : Blo 342753 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B779615 : Blo 342753 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B517499 : Blo 342753 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B517625 : Blo 342753 517625 := bstep (se 2 (by rfl) ⟨194109, by rfl⟩ : syracuseStep 517625 = 388219) B388219
theorem B517727 : Blo 342753 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B583355 : Blo 342753 583355 := bstep (se 1 (by rfl) ⟨437516, by rfl⟩ : syracuseStep 583355 = 875033) B875033
theorem B5891777 : Blo 342753 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B780011 : Blo 342753 780011 := bstep (se 1 (by rfl) ⟨585008, by rfl⟩ : syracuseStep 780011 = 1170017) B1170017
theorem B517943 : Blo 342753 517943 := bstep (se 1 (by rfl) ⟨388457, by rfl⟩ : syracuseStep 517943 = 776915) B776915
theorem B780137 : Blo 342753 780137 := bstep (se 2 (by rfl) ⟨292551, by rfl⟩ : syracuseStep 780137 = 585103) B585103
theorem B1468367 : Blo 342753 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B518249 : Blo 342753 518249 := bstep (se 2 (by rfl) ⟨194343, by rfl⟩ : syracuseStep 518249 = 388687) B388687
theorem B2779559 : Blo 342753 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B518567 : Blo 342753 518567 := bstep (se 1 (by rfl) ⟨388925, by rfl⟩ : syracuseStep 518567 = 777851) B777851
theorem B518651 : Blo 342753 518651 := bstep (se 1 (by rfl) ⟨388988, by rfl⟩ : syracuseStep 518651 = 777977) B777977
theorem B387679 : Blo 342753 387679 := bstep (se 1 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 387679 = 581519) B581519
theorem B518777 : Blo 342753 518777 := bstep (se 2 (by rfl) ⟨194541, by rfl⟩ : syracuseStep 518777 = 389083) B389083
theorem B518831 : Blo 342753 518831 := bstep (se 1 (by rfl) ⟨389123, by rfl⟩ : syracuseStep 518831 = 778247) B778247
theorem B1469117 : Blo 342753 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B518879 : Blo 342753 518879 := bstep (se 1 (by rfl) ⟨389159, by rfl⟩ : syracuseStep 518879 = 778319) B778319
theorem B1305335 : Blo 342753 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1239799 : Blo 342753 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B4188995 : Blo 342753 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B519143 : Blo 342753 519143 := bstep (se 1 (by rfl) ⟨389357, by rfl⟩ : syracuseStep 519143 = 778715) B778715
theorem B31878157 : Blo 342753 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B1043675 : Blo 342753 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B519401 : Blo 342753 519401 := bstep (se 2 (by rfl) ⟨194775, by rfl⟩ : syracuseStep 519401 = 389551) B389551
theorem B519455 : Blo 342753 519455 := bstep (se 1 (by rfl) ⟨389591, by rfl⟩ : syracuseStep 519455 = 779183) B779183
theorem B585083 : Blo 342753 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B519623 : Blo 342753 519623 := bstep (se 1 (by rfl) ⟨389717, by rfl⟩ : syracuseStep 519623 = 779435) B779435
theorem B12906161 : Blo 342753 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B388831 : Blo 342753 388831 := bstep (se 1 (by rfl) ⟨291623, by rfl⟩ : syracuseStep 388831 = 583247) B583247
theorem B519977 : Blo 342753 519977 := bstep (se 2 (by rfl) ⟨194991, by rfl⟩ : syracuseStep 519977 = 389983) B389983
theorem B519983 : Blo 342753 519983 := bstep (se 1 (by rfl) ⟨389987, by rfl⟩ : syracuseStep 519983 = 779975) B779975
theorem B23949107 : Blo 342753 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1470383 : Blo 342753 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B7172027 : Blo 342753 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B27324533 : Blo 342753 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B389407 : Blo 342753 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B389695 : Blo 342753 389695 := bstep (se 1 (by rfl) ⟨292271, by rfl⟩ : syracuseStep 389695 = 584543) B584543
theorem B1700423 : Blo 342753 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1569401 : Blo 342753 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B488111 : Blo 342753 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B10777519 : Blo 342753 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B7992377 : Blo 342753 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B1242209 : Blo 342753 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B1733881 : Blo 342753 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B1471783 : Blo 342753 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B1307947 : Blo 342753 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B23950727 : Blo 342753 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1472057 : Blo 342753 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B489979 : Blo 342753 489979 := bstep (se 1 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 489979 = 734969) B734969
theorem B1735343 : Blo 342753 1735343 := bstep (se 1 (by rfl) ⟨1301507, by rfl⟩ : syracuseStep 1735343 = 2603015) B2603015
theorem B981679 : Blo 342753 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B490207 : Blo 342753 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B1735667 : Blo 342753 1735667 := bstep (se 1 (by rfl) ⟨1301750, by rfl⟩ : syracuseStep 1735667 = 2603501) B2603501
theorem B1474433 : Blo 342753 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B3932225 : Blo 342753 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B1049195 : Blo 342753 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B2196143 : Blo 342753 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B2622455 : Blo 342753 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B492599 : Blo 342753 492599 := bstep (se 1 (by rfl) ⟨369449, by rfl⟩ : syracuseStep 492599 = 738899) B738899
theorem B1738259 : Blo 342753 1738259 := bstep (se 1 (by rfl) ⟨1303694, by rfl⟩ : syracuseStep 1738259 = 2607389) B2607389
theorem B984595 : Blo 342753 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B1115731 : Blo 342753 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B984743 : Blo 342753 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B1476431 : Blo 342753 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B493391 : Blo 342753 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B1181537 : Blo 342753 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B591815 : Blo 342753 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B1870127 : Blo 342753 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B1247815 : Blo 342753 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B986087 : Blo 342753 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B1182863 : Blo 342753 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1150331 : Blo 342753 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B42504209 : Blo 342753 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B1479491 : Blo 342753 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B57480101 : Blo 342753 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B5575979 : Blo 342753 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B3151673 : Blo 342753 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B1185817 : Blo 342753 1185817 := bstep (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) B889363
theorem B3905981 : Blo 342753 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B1743929 : Blo 342753 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B2792663 : Blo 342753 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B695783 : Blo 342753 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B15966071 : Blo 342753 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B828139 : Blo 342753 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B15967151 : Blo 342753 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B8791739 : Blo 342753 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B8857349 : Blo 342753 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B1156895 : Blo 342753 1156895 := bstep (se 1 (by rfl) ⟨867671, by rfl⟩ : syracuseStep 1156895 = 1735343) B1735343
theorem B1157111 : Blo 342753 1157111 := bstep (se 1 (by rfl) ⟨867833, by rfl⟩ : syracuseStep 1157111 = 1735667) B1735667
theorem B20195351 : Blo 342753 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B1648991 : Blo 342753 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B1878565 : Blo 342753 1878565 := bstep (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) B352231
theorem B830263 : Blo 342753 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B1157975 : Blo 342753 1157975 := bstep (se 1 (by rfl) ⟨868481, by rfl⟩ : syracuseStep 1157975 = 1736963) B1736963
theorem B1158191 : Blo 342753 1158191 := bstep (se 1 (by rfl) ⟨868643, by rfl⟩ : syracuseStep 1158191 = 1737287) B1737287
theorem B2960651 : Blo 342753 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1158569 : Blo 342753 1158569 := bstep (se 2 (by rfl) ⟨434463, by rfl⟩ : syracuseStep 1158569 = 868927) B868927
theorem B1650451 : Blo 342753 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B438139 : Blo 342753 438139 := bstep (se 1 (by rfl) ⟨328604, by rfl⟩ : syracuseStep 438139 = 657209) B657209
theorem B1159055 : Blo 342753 1159055 := bstep (se 1 (by rfl) ⟨869291, by rfl⟩ : syracuseStep 1159055 = 1738583) B1738583
theorem B929981 : Blo 342753 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B1159433 : Blo 342753 1159433 := bstep (se 2 (by rfl) ⟨434787, by rfl⟩ : syracuseStep 1159433 = 869575) B869575
theorem B733799 : Blo 342753 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B734483 : Blo 342753 734483 := bstep (se 1 (by rfl) ⟨550862, by rfl⟩ : syracuseStep 734483 = 1101725) B1101725
theorem B1160567 : Blo 342753 1160567 := bstep (se 1 (by rfl) ⟨870425, by rfl⟩ : syracuseStep 1160567 = 1740851) B1740851
theorem B4961735 : Blo 342753 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B4732759 : Blo 342753 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B1161377 : Blo 342753 1161377 := bstep (se 2 (by rfl) ⟨435516, by rfl⟩ : syracuseStep 1161377 = 871033) B871033
theorem B1653065 : Blo 342753 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1161647 : Blo 342753 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1751705 : Blo 342753 1751705 := bstep (se 2 (by rfl) ⟨656889, by rfl⟩ : syracuseStep 1751705 = 1313779) B1313779
theorem B342875 : Blo 342753 342875 := bstep (se 1 (by rfl) ⟨257156, by rfl⟩ : syracuseStep 342875 = 514313) B514313
theorem B342943 : Blo 342753 342943 := bstep (se 1 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 342943 = 514415) B514415
theorem B343087 : Blo 342753 343087 := bstep (se 1 (by rfl) ⟨257315, by rfl⟩ : syracuseStep 343087 = 514631) B514631
theorem B343111 : Blo 342753 343111 := bstep (se 1 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 343111 = 514667) B514667
theorem B343263 : Blo 342753 343263 := bstep (se 1 (by rfl) ⟨257447, by rfl⟩ : syracuseStep 343263 = 514895) B514895
theorem B2211239 : Blo 342753 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B1752515 : Blo 342753 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B343527 : Blo 342753 343527 := bstep (se 1 (by rfl) ⟨257645, by rfl⟩ : syracuseStep 343527 = 515291) B515291
theorem B1162727 : Blo 342753 1162727 := bstep (se 1 (by rfl) ⟨872045, by rfl⟩ : syracuseStep 1162727 = 1744091) B1744091
theorem B343643 : Blo 342753 343643 := bstep (se 1 (by rfl) ⟨257732, by rfl⟩ : syracuseStep 343643 = 515465) B515465
theorem B343879 : Blo 342753 343879 := bstep (se 1 (by rfl) ⟨257909, by rfl⟩ : syracuseStep 343879 = 515819) B515819
theorem B344031 : Blo 342753 344031 := bstep (se 1 (by rfl) ⟨258023, by rfl⟩ : syracuseStep 344031 = 516047) B516047
theorem B868391 : Blo 342753 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B2474063 : Blo 342753 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B7979147 : Blo 342753 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1163483 : Blo 342753 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B868583 : Blo 342753 868583 := bstep (se 1 (by rfl) ⟨651437, by rfl⟩ : syracuseStep 868583 = 1302875) B1302875
theorem B344295 : Blo 342753 344295 := bstep (se 1 (by rfl) ⟨258221, by rfl⟩ : syracuseStep 344295 = 516443) B516443
theorem B344447 : Blo 342753 344447 := bstep (se 1 (by rfl) ⟨258335, by rfl⟩ : syracuseStep 344447 = 516671) B516671
theorem B344527 : Blo 342753 344527 := bstep (se 1 (by rfl) ⟨258395, by rfl⟩ : syracuseStep 344527 = 516791) B516791
theorem B1163753 : Blo 342753 1163753 := bstep (se 2 (by rfl) ⟨436407, by rfl⟩ : syracuseStep 1163753 = 872815) B872815
theorem B344679 : Blo 342753 344679 := bstep (se 1 (by rfl) ⟨258509, by rfl⟩ : syracuseStep 344679 = 517019) B517019
theorem B869231 : Blo 342753 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B344943 : Blo 342753 344943 := bstep (se 1 (by rfl) ⟨258707, by rfl⟩ : syracuseStep 344943 = 517415) B517415
theorem B1328015 : Blo 342753 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B344999 : Blo 342753 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B345083 : Blo 342753 345083 := bstep (se 1 (by rfl) ⟨258812, by rfl⟩ : syracuseStep 345083 = 517625) B517625
theorem B1164347 : Blo 342753 1164347 := bstep (se 1 (by rfl) ⟨873260, by rfl⟩ : syracuseStep 1164347 = 1746521) B1746521
theorem B345151 : Blo 342753 345151 := bstep (se 1 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 345151 = 517727) B517727
theorem B345295 : Blo 342753 345295 := bstep (se 1 (by rfl) ⟨258971, by rfl⟩ : syracuseStep 345295 = 517943) B517943
theorem B53495113 : Blo 342753 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B1164617 : Blo 342753 1164617 := bstep (se 2 (by rfl) ⟨436731, by rfl⟩ : syracuseStep 1164617 = 873463) B873463
theorem B345499 : Blo 342753 345499 := bstep (se 1 (by rfl) ⟨259124, by rfl⟩ : syracuseStep 345499 = 518249) B518249
theorem B1754621 : Blo 342753 1754621 := bstep (se 3 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 1754621 = 657983) B657983
theorem B1853039 : Blo 342753 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B771695 : Blo 342753 771695 := bstep (se 1 (by rfl) ⟨578771, by rfl⟩ : syracuseStep 771695 = 1157543) B1157543
theorem B345711 : Blo 342753 345711 := bstep (se 1 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 345711 = 518567) B518567
theorem B2311841 : Blo 342753 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B345767 : Blo 342753 345767 := bstep (se 1 (by rfl) ⟨259325, by rfl⟩ : syracuseStep 345767 = 518651) B518651
theorem B771803 : Blo 342753 771803 := bstep (se 1 (by rfl) ⟨578852, by rfl⟩ : syracuseStep 771803 = 1157705) B1157705
theorem B345851 : Blo 342753 345851 := bstep (se 1 (by rfl) ⟨259388, by rfl⟩ : syracuseStep 345851 = 518777) B518777
theorem B345887 : Blo 342753 345887 := bstep (se 1 (by rfl) ⟨259415, by rfl⟩ : syracuseStep 345887 = 518831) B518831
theorem B2606903 : Blo 342753 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B345919 : Blo 342753 345919 := bstep (se 1 (by rfl) ⟨259439, by rfl⟩ : syracuseStep 345919 = 518879) B518879
theorem B3917645 : Blo 342753 3917645 := bstep (se 3 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 3917645 = 1469117) B1469117
theorem B870223 : Blo 342753 870223 := bstep (se 1 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 870223 = 1305335) B1305335
theorem B346095 : Blo 342753 346095 := bstep (se 1 (by rfl) ⟨259571, by rfl⟩ : syracuseStep 346095 = 519143) B519143
theorem B346267 : Blo 342753 346267 := bstep (se 1 (by rfl) ⟨259700, by rfl⟩ : syracuseStep 346267 = 519401) B519401
theorem B346303 : Blo 342753 346303 := bstep (se 1 (by rfl) ⟨259727, by rfl⟩ : syracuseStep 346303 = 519455) B519455
theorem B1755431 : Blo 342753 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B346415 : Blo 342753 346415 := bstep (se 1 (by rfl) ⟨259811, by rfl⟩ : syracuseStep 346415 = 519623) B519623
theorem B8604107 : Blo 342753 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B346651 : Blo 342753 346651 := bstep (se 1 (by rfl) ⟨259988, by rfl⟩ : syracuseStep 346651 = 519977) B519977
theorem B346655 : Blo 342753 346655 := bstep (se 1 (by rfl) ⟨259991, by rfl⟩ : syracuseStep 346655 = 519983) B519983
theorem B772919 : Blo 342753 772919 := bstep (se 1 (by rfl) ⟨579689, by rfl⟩ : syracuseStep 772919 = 1159379) B1159379
theorem B773099 : Blo 342753 773099 := bstep (se 1 (by rfl) ⟨579824, by rfl⟩ : syracuseStep 773099 = 1159649) B1159649
theorem B1133615 : Blo 342753 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B5328251 : Blo 342753 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B2805443 : Blo 342753 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B773927 : Blo 342753 773927 := bstep (se 1 (by rfl) ⟨580445, by rfl⟩ : syracuseStep 773927 = 1160891) B1160891
theorem B1167209 : Blo 342753 1167209 := bstep (se 2 (by rfl) ⟨437703, by rfl⟩ : syracuseStep 1167209 = 875407) B875407
theorem B4215077 : Blo 342753 4215077 := bstep (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) B790327
theorem B1102351 : Blo 342753 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B774953 : Blo 342753 774953 := bstep (se 2 (by rfl) ⟨290607, by rfl⟩ : syracuseStep 774953 = 581215) B581215
theorem B775223 : Blo 342753 775223 := bstep (se 1 (by rfl) ⟨581417, by rfl⟩ : syracuseStep 775223 = 1162835) B1162835
theorem B578623 : Blo 342753 578623 := bstep (se 1 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 578623 = 867935) B867935
theorem B775241 : Blo 342753 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B2938031 : Blo 342753 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B1168559 : Blo 342753 1168559 := bstep (se 1 (by rfl) ⟨876419, by rfl⟩ : syracuseStep 1168559 = 1752839) B1752839
theorem B1594811 : Blo 342753 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B579143 : Blo 342753 579143 := bstep (se 1 (by rfl) ⟨434357, by rfl⟩ : syracuseStep 579143 = 868715) B868715
theorem B579359 : Blo 342753 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B9983897 : Blo 342753 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B579575 : Blo 342753 579575 := bstep (se 1 (by rfl) ⟨434681, by rfl⟩ : syracuseStep 579575 = 869363) B869363
theorem B514283 : Blo 342753 514283 := bstep (se 1 (by rfl) ⟨385712, by rfl⟩ : syracuseStep 514283 = 771425) B771425
theorem B874739 : Blo 342753 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B874759 : Blo 342753 874759 := bstep (se 1 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 874759 = 1312139) B1312139
theorem B514343 : Blo 342753 514343 := bstep (se 1 (by rfl) ⟨385757, by rfl⟩ : syracuseStep 514343 = 771515) B771515
theorem B514427 : Blo 342753 514427 := bstep (se 1 (by rfl) ⟨385820, by rfl⟩ : syracuseStep 514427 = 771641) B771641
theorem B1956271 : Blo 342753 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B2415193 : Blo 342753 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B514697 : Blo 342753 514697 := bstep (se 2 (by rfl) ⟨193011, by rfl⟩ : syracuseStep 514697 = 386023) B386023
theorem B42326833 : Blo 342753 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B6282035 : Blo 342753 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B514871 : Blo 342753 514871 := bstep (se 1 (by rfl) ⟨386153, by rfl⟩ : syracuseStep 514871 = 772307) B772307
theorem B514907 : Blo 342753 514907 := bstep (se 1 (by rfl) ⟨386180, by rfl⟩ : syracuseStep 514907 = 772361) B772361
theorem B777167 : Blo 342753 777167 := bstep (se 1 (by rfl) ⟨582875, by rfl⟩ : syracuseStep 777167 = 1165751) B1165751
theorem B777185 : Blo 342753 777185 := bstep (se 2 (by rfl) ⟨291444, by rfl⟩ : syracuseStep 777185 = 582889) B582889
theorem B515051 : Blo 342753 515051 := bstep (se 1 (by rfl) ⟨386288, by rfl⟩ : syracuseStep 515051 = 772577) B772577
theorem B777257 : Blo 342753 777257 := bstep (se 2 (by rfl) ⟨291471, by rfl⟩ : syracuseStep 777257 = 582943) B582943
theorem B580655 : Blo 342753 580655 := bstep (se 1 (by rfl) ⟨435491, by rfl⟩ : syracuseStep 580655 = 870983) B870983
theorem B580729 : Blo 342753 580729 := bstep (se 2 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 580729 = 435547) B435547
theorem B1301629 : Blo 342753 1301629 := bstep (se 3 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 1301629 = 488111) B488111
theorem B515255 : Blo 342753 515255 := bstep (se 1 (by rfl) ⟨386441, by rfl⟩ : syracuseStep 515255 = 772883) B772883
theorem B515495 : Blo 342753 515495 := bstep (se 1 (by rfl) ⟨386621, by rfl⟩ : syracuseStep 515495 = 773243) B773243
theorem B581033 : Blo 342753 581033 := bstep (se 2 (by rfl) ⟨217887, by rfl⟩ : syracuseStep 581033 = 435775) B435775
theorem B1236455 : Blo 342753 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B515579 : Blo 342753 515579 := bstep (se 1 (by rfl) ⟨386684, by rfl⟩ : syracuseStep 515579 = 773369) B773369
theorem B515675 : Blo 342753 515675 := bstep (se 1 (by rfl) ⟨386756, by rfl⟩ : syracuseStep 515675 = 773513) B773513
theorem B515759 : Blo 342753 515759 := bstep (se 1 (by rfl) ⟨386819, by rfl⟩ : syracuseStep 515759 = 773639) B773639
theorem B2416339 : Blo 342753 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B679657 : Blo 342753 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B2940695 : Blo 342753 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B515879 : Blo 342753 515879 := bstep (se 1 (by rfl) ⟨386909, by rfl⟩ : syracuseStep 515879 = 773819) B773819
theorem B876359 : Blo 342753 876359 := bstep (se 1 (by rfl) ⟨657269, by rfl⟩ : syracuseStep 876359 = 1314539) B1314539
theorem B515963 : Blo 342753 515963 := bstep (se 1 (by rfl) ⟨386972, by rfl⟩ : syracuseStep 515963 = 773945) B773945
theorem B2482109 : Blo 342753 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B2613221 : Blo 342753 2613221 := bstep (se 4 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 2613221 = 489979) B489979
theorem B876683 : Blo 342753 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B581863 : Blo 342753 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B516383 : Blo 342753 516383 := bstep (se 1 (by rfl) ⟨387287, by rfl⟩ : syracuseStep 516383 = 774575) B774575
theorem B516407 : Blo 342753 516407 := bstep (se 1 (by rfl) ⟨387305, by rfl⟩ : syracuseStep 516407 = 774611) B774611
theorem B1106273 : Blo 342753 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B516479 : Blo 342753 516479 := bstep (se 1 (by rfl) ⟨387359, by rfl⟩ : syracuseStep 516479 = 774719) B774719
theorem B582025 : Blo 342753 582025 := bstep (se 2 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 582025 = 436519) B436519
theorem B516551 : Blo 342753 516551 := bstep (se 1 (by rfl) ⟨387413, by rfl⟩ : syracuseStep 516551 = 774827) B774827
theorem B877007 : Blo 342753 877007 := bstep (se 1 (by rfl) ⟨657755, by rfl⟩ : syracuseStep 877007 = 1315511) B1315511
theorem B549479 : Blo 342753 549479 := bstep (se 1 (by rfl) ⟨412109, by rfl⟩ : syracuseStep 549479 = 824219) B824219
theorem B2220797 : Blo 342753 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B516905 : Blo 342753 516905 := bstep (se 2 (by rfl) ⟨193839, by rfl⟩ : syracuseStep 516905 = 387679) B387679
theorem B516911 : Blo 342753 516911 := bstep (se 1 (by rfl) ⟨387683, by rfl⟩ : syracuseStep 516911 = 775367) B775367
theorem B8938291 : Blo 342753 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B582457 : Blo 342753 582457 := bstep (se 2 (by rfl) ⟨218421, by rfl⟩ : syracuseStep 582457 = 436843) B436843
theorem B582511 : Blo 342753 582511 := bstep (se 1 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 582511 = 873767) B873767
theorem B517031 : Blo 342753 517031 := bstep (se 1 (by rfl) ⟨387773, by rfl⟩ : syracuseStep 517031 = 775547) B775547
theorem B779219 : Blo 342753 779219 := bstep (se 1 (by rfl) ⟨584414, by rfl⟩ : syracuseStep 779219 = 1168829) B1168829
theorem B517115 : Blo 342753 517115 := bstep (se 1 (by rfl) ⟨387836, by rfl⟩ : syracuseStep 517115 = 775673) B775673
theorem B517175 : Blo 342753 517175 := bstep (se 1 (by rfl) ⟨387881, by rfl⟩ : syracuseStep 517175 = 775763) B775763
theorem B582761 : Blo 342753 582761 := bstep (se 2 (by rfl) ⟨218535, by rfl⟩ : syracuseStep 582761 = 437071) B437071
theorem B1107067 : Blo 342753 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B517295 : Blo 342753 517295 := bstep (se 1 (by rfl) ⟨387971, by rfl⟩ : syracuseStep 517295 = 775943) B775943
theorem B779471 : Blo 342753 779471 := bstep (se 1 (by rfl) ⟨584603, by rfl⟩ : syracuseStep 779471 = 1169207) B1169207
theorem B779795 : Blo 342753 779795 := bstep (se 1 (by rfl) ⟨584846, by rfl⟩ : syracuseStep 779795 = 1169693) B1169693
theorem B5596739 : Blo 342753 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B550471 : Blo 342753 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B517703 : Blo 342753 517703 := bstep (se 1 (by rfl) ⟨388277, by rfl⟩ : syracuseStep 517703 = 776555) B776555
theorem B386671 : Blo 342753 386671 := bstep (se 1 (by rfl) ⟨290003, by rfl⟩ : syracuseStep 386671 = 580007) B580007
theorem B517799 : Blo 342753 517799 := bstep (se 1 (by rfl) ⟨388349, by rfl⟩ : syracuseStep 517799 = 776699) B776699
theorem B386779 : Blo 342753 386779 := bstep (se 1 (by rfl) ⟨290084, by rfl⟩ : syracuseStep 386779 = 580169) B580169
theorem B354043 : Blo 342753 354043 := bstep (se 1 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 354043 = 531065) B531065
theorem B517883 : Blo 342753 517883 := bstep (se 1 (by rfl) ⟨388412, by rfl⟩ : syracuseStep 517883 = 776825) B776825
theorem B517919 : Blo 342753 517919 := bstep (se 1 (by rfl) ⟨388439, by rfl⟩ : syracuseStep 517919 = 776879) B776879
theorem B517967 : Blo 342753 517967 := bstep (se 1 (by rfl) ⟨388475, by rfl⟩ : syracuseStep 517967 = 776951) B776951
theorem B976769 : Blo 342753 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B518087 : Blo 342753 518087 := bstep (se 1 (by rfl) ⟨388565, by rfl⟩ : syracuseStep 518087 = 777131) B777131
theorem B1107913 : Blo 342753 1107913 := bstep (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) B830935
theorem B14968921 : Blo 342753 14968921 := bstep (se 2 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 14968921 = 11226691) B11226691
theorem B583915 : Blo 342753 583915 := bstep (se 1 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 583915 = 875873) B875873
theorem B518441 : Blo 342753 518441 := bstep (se 2 (by rfl) ⟨194415, by rfl⟩ : syracuseStep 518441 = 388831) B388831
theorem B518447 : Blo 342753 518447 := bstep (se 1 (by rfl) ⟨388835, by rfl⟩ : syracuseStep 518447 = 777671) B777671
theorem B551291 : Blo 342753 551291 := bstep (se 1 (by rfl) ⟨413468, by rfl⟩ : syracuseStep 551291 = 826937) B826937
theorem B584219 : Blo 342753 584219 := bstep (se 1 (by rfl) ⟨438164, by rfl⟩ : syracuseStep 584219 = 876329) B876329
theorem B518687 : Blo 342753 518687 := bstep (se 1 (by rfl) ⟨389015, by rfl⟩ : syracuseStep 518687 = 778031) B778031
theorem B977579 : Blo 342753 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B5040899 : Blo 342753 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B387931 : Blo 342753 387931 := bstep (se 1 (by rfl) ⟨290948, by rfl⟩ : syracuseStep 387931 = 581897) B581897
theorem B519071 : Blo 342753 519071 := bstep (se 1 (by rfl) ⟨389303, by rfl⟩ : syracuseStep 519071 = 778607) B778607
theorem B519119 : Blo 342753 519119 := bstep (se 1 (by rfl) ⟨389339, by rfl⟩ : syracuseStep 519119 = 778679) B778679
theorem B519209 : Blo 342753 519209 := bstep (se 2 (by rfl) ⟨194703, by rfl⟩ : syracuseStep 519209 = 389407) B389407
theorem B519215 : Blo 342753 519215 := bstep (se 1 (by rfl) ⟨389411, by rfl⟩ : syracuseStep 519215 = 778823) B778823
theorem B519239 : Blo 342753 519239 := bstep (se 1 (by rfl) ⟨389429, by rfl⟩ : syracuseStep 519239 = 778859) B778859
theorem B11234483 : Blo 342753 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B584887 : Blo 342753 584887 := bstep (se 1 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 584887 = 877331) B877331
theorem B1240363 : Blo 342753 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B519503 : Blo 342753 519503 := bstep (se 1 (by rfl) ⟨389627, by rfl⟩ : syracuseStep 519503 = 779255) B779255
theorem B519593 : Blo 342753 519593 := bstep (se 2 (by rfl) ⟨194847, by rfl⟩ : syracuseStep 519593 = 389695) B389695
theorem B650747 : Blo 342753 650747 := bstep (se 1 (by rfl) ⟨488060, by rfl⟩ : syracuseStep 650747 = 976121) B976121
theorem B519743 : Blo 342753 519743 := bstep (se 1 (by rfl) ⟨389807, by rfl⟩ : syracuseStep 519743 = 779615) B779615
theorem B4419197 : Blo 342753 4419197 := bstep (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) B1657199
theorem B1109629 : Blo 342753 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B388903 : Blo 342753 388903 := bstep (se 1 (by rfl) ⟨291677, by rfl⟩ : syracuseStep 388903 = 583355) B583355
theorem B3927851 : Blo 342753 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B520007 : Blo 342753 520007 := bstep (se 1 (by rfl) ⟨390005, by rfl⟩ : syracuseStep 520007 = 780011) B780011
theorem B520091 : Blo 342753 520091 := bstep (se 1 (by rfl) ⟨390068, by rfl⟩ : syracuseStep 520091 = 780137) B780137
theorem B978911 : Blo 342753 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B1962377 : Blo 342753 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B2126483 : Blo 342753 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B1110809 : Blo 342753 1110809 := bstep (se 2 (by rfl) ⟨416553, by rfl⟩ : syracuseStep 1110809 = 833107) B833107
theorem B390055 : Blo 342753 390055 := bstep (se 1 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 390055 = 585083) B585083
theorem B7435253 : Blo 342753 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B980255 : Blo 342753 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B4781351 : Blo 342753 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B18216355 : Blo 342753 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B40138253 : Blo 342753 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B1046267 : Blo 342753 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B1308905 : Blo 342753 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B653609 : Blo 342753 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B981371 : Blo 342753 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B2128403 : Blo 342753 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B490475 : Blo 342753 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B1244285 : Blo 342753 1244285 := bstep (se 3 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 1244285 = 466607) B466607
theorem B982145 : Blo 342753 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B1080911 : Blo 342753 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B982955 : Blo 342753 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B2621483 : Blo 342753 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B885343 : Blo 342753 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B1541227 : Blo 342753 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B656495 : Blo 342753 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B1737935 : Blo 342753 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B984287 : Blo 342753 984287 := bstep (se 1 (by rfl) ⟨738215, by rfl⟩ : syracuseStep 984287 = 1476431) B1476431
theorem B787691 : Blo 342753 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B394543 : Blo 342753 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B1476089 : Blo 342753 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B1246751 : Blo 342753 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B5736071 : Blo 342753 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B657391 : Blo 342753 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B1312793 : Blo 342753 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B755743 : Blo 342753 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B1870295 : Blo 342753 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B1477217 : Blo 342753 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B19958561 : Blo 342753 19958561 := bstep (se 2 (by rfl) ⟨7484460, by rfl⟩ : syracuseStep 19958561 = 14968921) B14968921
theorem B1313597 : Blo 342753 1313597 := bstep (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) B492599
theorem B12881029 : Blo 342753 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B986327 : Blo 342753 986327 := bstep (se 1 (by rfl) ⟨739745, by rfl⟩ : syracuseStep 986327 = 1479491) B1479491
theorem B2101115 : Blo 342753 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B6655931 : Blo 342753 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B1315709 : Blo 342753 1315709 := bstep (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) B493391
theorem B824303 : Blo 342753 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B463855 : Blo 342753 463855 := bstep (se 1 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 463855 = 695783) B695783
theorem B2200601 : Blo 342753 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B1742147 : Blo 342753 1742147 := bstep (se 1 (by rfl) ⟨1306610, by rfl⟩ : syracuseStep 1742147 = 2613221) B2613221
theorem B366319 : Blo 342753 366319 := bstep (se 1 (by rfl) ⟨274739, by rfl⟩ : syracuseStep 366319 = 549479) B549479
theorem B1480531 : Blo 342753 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1742957 : Blo 342753 1742957 := bstep (se 3 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 1742957 = 653609) B653609
theorem B5904899 : Blo 342753 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B5675741 : Blo 342753 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B24288473 : Blo 342753 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B1973767 : Blo 342753 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B433831 : Blo 342753 433831 := bstep (se 1 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 433831 = 650747) B650747
theorem B1581089 : Blo 342753 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B3154301 : Blo 342753 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B1417655 : Blo 342753 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B4956835 : Blo 342753 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B3187567 : Blo 342753 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B56435777 : Blo 342753 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B697511 : Blo 342753 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B829523 : Blo 342753 829523 := bstep (se 1 (by rfl) ⟨622142, by rfl⟩ : syracuseStep 829523 = 1244285) B1244285
theorem B3221785 : Blo 342753 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B1649375 : Blo 342753 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B5319431 : Blo 342753 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B699463 : Blo 342753 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B1748303 : Blo 342753 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B1158839 : Blo 342753 1158839 := bstep (se 1 (by rfl) ⟨869129, by rfl⟩ : syracuseStep 1158839 = 1738259) B1738259
theorem B733961 : Blo 342753 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1487641 : Blo 342753 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B3552167 : Blo 342753 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B472057 : Blo 342753 472057 := bstep (se 2 (by rfl) ⟨177021, by rfl⟩ : syracuseStep 472057 = 354043) B354043
theorem B1160297 : Blo 342753 1160297 := bstep (se 2 (by rfl) ⟨435111, by rfl⟩ : syracuseStep 1160297 = 870223) B870223
theorem B38320067 : Blo 342753 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B2504753 : Blo 342753 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1063207 : Blo 342753 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B12270197 : Blo 342753 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B342855 : Blo 342753 342855 := bstep (se 1 (by rfl) ⟨257141, by rfl⟩ : syracuseStep 342855 = 514283) B514283
theorem B342895 : Blo 342753 342895 := bstep (se 1 (by rfl) ⟨257171, by rfl⟩ : syracuseStep 342895 = 514343) B514343
theorem B342951 : Blo 342753 342951 := bstep (se 1 (by rfl) ⟨257213, by rfl⟩ : syracuseStep 342951 = 514427) B514427
theorem B2603987 : Blo 342753 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B1653817 : Blo 342753 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B343131 : Blo 342753 343131 := bstep (se 1 (by rfl) ⟨257348, by rfl⟩ : syracuseStep 343131 = 514697) B514697
theorem B343247 : Blo 342753 343247 := bstep (se 1 (by rfl) ⟨257435, by rfl⟩ : syracuseStep 343247 = 514871) B514871
theorem B343271 : Blo 342753 343271 := bstep (se 1 (by rfl) ⟨257453, by rfl⟩ : syracuseStep 343271 = 514907) B514907
theorem B343367 : Blo 342753 343367 := bstep (se 1 (by rfl) ⟨257525, by rfl⟩ : syracuseStep 343367 = 515051) B515051
theorem B1162619 : Blo 342753 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B343503 : Blo 342753 343503 := bstep (se 1 (by rfl) ⟨257627, by rfl⟩ : syracuseStep 343503 = 515255) B515255
theorem B343663 : Blo 342753 343663 := bstep (se 1 (by rfl) ⟨257747, by rfl⟩ : syracuseStep 343663 = 515495) B515495
theorem B343719 : Blo 342753 343719 := bstep (se 1 (by rfl) ⟨257789, by rfl⟩ : syracuseStep 343719 = 515579) B515579
theorem B343783 : Blo 342753 343783 := bstep (se 1 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 343783 = 515675) B515675
theorem B343839 : Blo 342753 343839 := bstep (se 1 (by rfl) ⟨257879, by rfl⟩ : syracuseStep 343839 = 515759) B515759
theorem B343919 : Blo 342753 343919 := bstep (se 1 (by rfl) ⟨257939, by rfl⟩ : syracuseStep 343919 = 515879) B515879
theorem B343975 : Blo 342753 343975 := bstep (se 1 (by rfl) ⟨257981, by rfl⟩ : syracuseStep 343975 = 515963) B515963
theorem B1654739 : Blo 342753 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B344255 : Blo 342753 344255 := bstep (se 1 (by rfl) ⟨258191, by rfl⟩ : syracuseStep 344255 = 516383) B516383
theorem B344271 : Blo 342753 344271 := bstep (se 1 (by rfl) ⟨258203, by rfl⟩ : syracuseStep 344271 = 516407) B516407
theorem B737515 : Blo 342753 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B344319 : Blo 342753 344319 := bstep (se 1 (by rfl) ⟨258239, by rfl⟩ : syracuseStep 344319 = 516479) B516479
theorem B344367 : Blo 342753 344367 := bstep (se 1 (by rfl) ⟨258275, by rfl⟩ : syracuseStep 344367 = 516551) B516551
theorem B344603 : Blo 342753 344603 := bstep (se 1 (by rfl) ⟨258452, by rfl⟩ : syracuseStep 344603 = 516905) B516905
theorem B344607 : Blo 342753 344607 := bstep (se 1 (by rfl) ⟨258455, by rfl⟩ : syracuseStep 344607 = 516911) B516911
theorem B344687 : Blo 342753 344687 := bstep (se 1 (by rfl) ⟨258515, by rfl⟩ : syracuseStep 344687 = 517031) B517031
theorem B344743 : Blo 342753 344743 := bstep (se 1 (by rfl) ⟨258557, by rfl⟩ : syracuseStep 344743 = 517115) B517115
theorem B344783 : Blo 342753 344783 := bstep (se 1 (by rfl) ⟨258587, by rfl⟩ : syracuseStep 344783 = 517175) B517175
theorem B344863 : Blo 342753 344863 := bstep (se 1 (by rfl) ⟨258647, by rfl⟩ : syracuseStep 344863 = 517295) B517295
theorem B345135 : Blo 342753 345135 := bstep (se 1 (by rfl) ⟨258851, by rfl⟩ : syracuseStep 345135 = 517703) B517703
theorem B345199 : Blo 342753 345199 := bstep (se 1 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 345199 = 517799) B517799
theorem B345255 : Blo 342753 345255 := bstep (se 1 (by rfl) ⟨258941, by rfl⟩ : syracuseStep 345255 = 517883) B517883
theorem B771263 : Blo 342753 771263 := bstep (se 1 (by rfl) ⟨578447, by rfl⟩ : syracuseStep 771263 = 1156895) B1156895
theorem B345279 : Blo 342753 345279 := bstep (se 1 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 345279 = 517919) B517919
theorem B345311 : Blo 342753 345311 := bstep (se 1 (by rfl) ⟨258983, by rfl⟩ : syracuseStep 345311 = 517967) B517967
theorem B345391 : Blo 342753 345391 := bstep (se 1 (by rfl) ⟨259043, by rfl⟩ : syracuseStep 345391 = 518087) B518087
theorem B771407 : Blo 342753 771407 := bstep (se 1 (by rfl) ⟨578555, by rfl⟩ : syracuseStep 771407 = 1157111) B1157111
theorem B771497 : Blo 342753 771497 := bstep (se 2 (by rfl) ⟨289311, by rfl⟩ : syracuseStep 771497 = 578623) B578623
theorem B345627 : Blo 342753 345627 := bstep (se 1 (by rfl) ⟨259220, by rfl⟩ : syracuseStep 345627 = 518441) B518441
theorem B345631 : Blo 342753 345631 := bstep (se 1 (by rfl) ⟨259223, by rfl⟩ : syracuseStep 345631 = 518447) B518447
theorem B1099327 : Blo 342753 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B345791 : Blo 342753 345791 := bstep (se 1 (by rfl) ⟨259343, by rfl⟩ : syracuseStep 345791 = 518687) B518687
theorem B3360599 : Blo 342753 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B771983 : Blo 342753 771983 := bstep (se 1 (by rfl) ⟨578987, by rfl⟩ : syracuseStep 771983 = 1157975) B1157975
theorem B346047 : Blo 342753 346047 := bstep (se 1 (by rfl) ⟨259535, by rfl⟩ : syracuseStep 346047 = 519071) B519071
theorem B346079 : Blo 342753 346079 := bstep (se 1 (by rfl) ⟨259559, by rfl⟩ : syracuseStep 346079 = 519119) B519119
theorem B346139 : Blo 342753 346139 := bstep (se 1 (by rfl) ⟨259604, by rfl⟩ : syracuseStep 346139 = 519209) B519209
theorem B772127 : Blo 342753 772127 := bstep (se 1 (by rfl) ⟨579095, by rfl⟩ : syracuseStep 772127 = 1158191) B1158191
theorem B346143 : Blo 342753 346143 := bstep (se 1 (by rfl) ⟨259607, by rfl⟩ : syracuseStep 346143 = 519215) B519215
theorem B346159 : Blo 342753 346159 := bstep (se 1 (by rfl) ⟨259619, by rfl⟩ : syracuseStep 346159 = 519239) B519239
theorem B7489655 : Blo 342753 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B346335 : Blo 342753 346335 := bstep (se 1 (by rfl) ⟨259751, by rfl⟩ : syracuseStep 346335 = 519503) B519503
theorem B772379 : Blo 342753 772379 := bstep (se 1 (by rfl) ⟨579284, by rfl⟩ : syracuseStep 772379 = 1158569) B1158569
theorem B346395 : Blo 342753 346395 := bstep (se 1 (by rfl) ⟨259796, by rfl⟩ : syracuseStep 346395 = 519593) B519593
theorem B346495 : Blo 342753 346495 := bstep (se 1 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 346495 = 519743) B519743
theorem B6310345 : Blo 342753 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B346671 : Blo 342753 346671 := bstep (se 1 (by rfl) ⟨260003, by rfl⟩ : syracuseStep 346671 = 520007) B520007
theorem B772703 : Blo 342753 772703 := bstep (se 1 (by rfl) ⟨579527, by rfl⟩ : syracuseStep 772703 = 1159055) B1159055
theorem B346727 : Blo 342753 346727 := bstep (se 1 (by rfl) ⟨260045, by rfl⟩ : syracuseStep 346727 = 520091) B520091
theorem B772955 : Blo 342753 772955 := bstep (se 1 (by rfl) ⟨579716, by rfl⟩ : syracuseStep 772955 = 1159433) B1159433
theorem B1166345 : Blo 342753 1166345 := bstep (se 2 (by rfl) ⟨437379, by rfl⟩ : syracuseStep 1166345 = 874759) B874759
theorem B740539 : Blo 342753 740539 := bstep (se 1 (by rfl) ⟨555404, by rfl⟩ : syracuseStep 740539 = 1110809) B1110809
theorem B2608361 : Blo 342753 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B5918021 : Blo 342753 5918021 := bstep (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) B1109629
theorem B773711 : Blo 342753 773711 := bstep (se 1 (by rfl) ⟨580283, by rfl⟩ : syracuseStep 773711 = 1160567) B1160567
theorem B26758835 : Blo 342753 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B774251 : Blo 342753 774251 := bstep (se 1 (by rfl) ⟨580688, by rfl⟩ : syracuseStep 774251 = 1161377) B1161377
theorem B872603 : Blo 342753 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B774305 : Blo 342753 774305 := bstep (se 2 (by rfl) ⟨290364, by rfl⟩ : syracuseStep 774305 = 580729) B580729
theorem B1102043 : Blo 342753 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B774431 : Blo 342753 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B1167803 : Blo 342753 1167803 := bstep (se 1 (by rfl) ⟨875852, by rfl⟩ : syracuseStep 1167803 = 1751705) B1751705
theorem B1168343 : Blo 342753 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B906209 : Blo 342753 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B775151 : Blo 342753 775151 := bstep (se 1 (by rfl) ⟨581363, by rfl⟩ : syracuseStep 775151 = 1162727) B1162727
theorem B578927 : Blo 342753 578927 := bstep (se 1 (by rfl) ⟨434195, by rfl⟩ : syracuseStep 578927 = 868391) B868391
theorem B775655 : Blo 342753 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B579055 : Blo 342753 579055 := bstep (se 1 (by rfl) ⟨434291, by rfl⟩ : syracuseStep 579055 = 868583) B868583
theorem B775817 : Blo 342753 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B775835 : Blo 342753 775835 := bstep (se 1 (by rfl) ⟨581876, by rfl⟩ : syracuseStep 775835 = 1163753) B1163753
theorem B1464095 : Blo 342753 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B776033 : Blo 342753 776033 := bstep (se 2 (by rfl) ⟨291012, by rfl⟩ : syracuseStep 776033 = 582025) B582025
theorem B579487 : Blo 342753 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B776231 : Blo 342753 776231 := bstep (se 1 (by rfl) ⟨582173, by rfl⟩ : syracuseStep 776231 = 1164347) B1164347
theorem B776411 : Blo 342753 776411 := bstep (se 1 (by rfl) ⟨582308, by rfl⟩ : syracuseStep 776411 = 1164617) B1164617
theorem B1104185 : Blo 342753 1104185 := bstep (se 2 (by rfl) ⟨414069, by rfl⟩ : syracuseStep 1104185 = 828139) B828139
theorem B1169747 : Blo 342753 1169747 := bstep (se 1 (by rfl) ⟨877310, by rfl⟩ : syracuseStep 1169747 = 1754621) B1754621
theorem B11917721 : Blo 342753 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B1235359 : Blo 342753 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B514463 : Blo 342753 514463 := bstep (se 1 (by rfl) ⟨385847, by rfl⟩ : syracuseStep 514463 = 771695) B771695
theorem B776609 : Blo 342753 776609 := bstep (se 2 (by rfl) ⟨291228, by rfl⟩ : syracuseStep 776609 = 582457) B582457
theorem B514535 : Blo 342753 514535 := bstep (se 1 (by rfl) ⟨385901, by rfl⟩ : syracuseStep 514535 = 771803) B771803
theorem B776681 : Blo 342753 776681 := bstep (se 2 (by rfl) ⟨291255, by rfl⟩ : syracuseStep 776681 = 582511) B582511
theorem B2611763 : Blo 342753 2611763 := bstep (se 1 (by rfl) ⟨1958822, by rfl⟩ : syracuseStep 2611763 = 3917645) B3917645
theorem B1170287 : Blo 342753 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B1956797 : Blo 342753 1956797 := bstep (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) B733799
theorem B71326817 : Blo 342753 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B515279 : Blo 342753 515279 := bstep (se 1 (by rfl) ⟨386459, by rfl⟩ : syracuseStep 515279 = 772919) B772919
theorem B515399 : Blo 342753 515399 := bstep (se 1 (by rfl) ⟨386549, by rfl⟩ : syracuseStep 515399 = 773099) B773099
theorem B515561 : Blo 342753 515561 := bstep (se 2 (by rfl) ⟨193335, by rfl⟩ : syracuseStep 515561 = 386671) B386671
theorem B515705 : Blo 342753 515705 := bstep (se 2 (by rfl) ⟨193389, by rfl⟩ : syracuseStep 515705 = 386779) B386779
theorem B515951 : Blo 342753 515951 := bstep (se 1 (by rfl) ⟨386963, by rfl⟩ : syracuseStep 515951 = 773927) B773927
theorem B778139 : Blo 342753 778139 := bstep (se 1 (by rfl) ⟨583604, by rfl⟩ : syracuseStep 778139 = 1167209) B1167209
theorem B28336139 : Blo 342753 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B2810051 : Blo 342753 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B778553 : Blo 342753 778553 := bstep (se 2 (by rfl) ⟨291957, by rfl⟩ : syracuseStep 778553 = 583915) B583915
theorem B516635 : Blo 342753 516635 := bstep (se 1 (by rfl) ⟨387476, by rfl⟩ : syracuseStep 516635 = 774953) B774953
theorem B516815 : Blo 342753 516815 := bstep (se 1 (by rfl) ⟨387611, by rfl⟩ : syracuseStep 516815 = 775223) B775223
theorem B516827 : Blo 342753 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B1663753 : Blo 342753 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B14869277 : Blo 342753 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B1958687 : Blo 342753 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B779039 : Blo 342753 779039 := bstep (se 1 (by rfl) ⟨584279, by rfl⟩ : syracuseStep 779039 = 1168559) B1168559
theorem B386095 : Blo 342753 386095 := bstep (se 1 (by rfl) ⟨289571, by rfl⟩ : syracuseStep 386095 = 579143) B579143
theorem B1107017 : Blo 342753 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B517241 : Blo 342753 517241 := bstep (se 2 (by rfl) ⟨193965, by rfl⟩ : syracuseStep 517241 = 387931) B387931
theorem B386239 : Blo 342753 386239 := bstep (se 1 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 386239 = 579359) B579359
theorem B386383 : Blo 342753 386383 := bstep (se 1 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 386383 = 579575) B579575
theorem B583159 : Blo 342753 583159 := bstep (se 1 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 583159 = 874739) B874739
theorem B779849 : Blo 342753 779849 := bstep (se 2 (by rfl) ⟨292443, by rfl⟩ : syracuseStep 779849 = 584887) B584887
theorem B4188023 : Blo 342753 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B518111 : Blo 342753 518111 := bstep (se 1 (by rfl) ⟨388583, by rfl⟩ : syracuseStep 518111 = 777167) B777167
theorem B518123 : Blo 342753 518123 := bstep (se 1 (by rfl) ⟨388592, by rfl⟩ : syracuseStep 518123 = 777185) B777185
theorem B518171 : Blo 342753 518171 := bstep (se 1 (by rfl) ⟨388628, by rfl⟩ : syracuseStep 518171 = 777257) B777257
theorem B387103 : Blo 342753 387103 := bstep (se 1 (by rfl) ⟨290327, by rfl⟩ : syracuseStep 387103 = 580655) B580655
theorem B1861775 : Blo 342753 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B387355 : Blo 342753 387355 := bstep (se 1 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 387355 = 581033) B581033
theorem B518537 : Blo 342753 518537 := bstep (se 2 (by rfl) ⟨194451, by rfl⟩ : syracuseStep 518537 = 388903) B388903
theorem B584185 : Blo 342753 584185 := bstep (se 2 (by rfl) ⟨219069, by rfl⟩ : syracuseStep 584185 = 438139) B438139
theorem B1960463 : Blo 342753 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B584239 : Blo 342753 584239 := bstep (se 1 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 584239 = 876359) B876359
theorem B10644047 : Blo 342753 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B584455 : Blo 342753 584455 := bstep (se 1 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 584455 = 876683) B876683
theorem B584671 : Blo 342753 584671 := bstep (se 1 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 584671 = 877007) B877007
theorem B10644767 : Blo 342753 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B519479 : Blo 342753 519479 := bstep (se 1 (by rfl) ⟨389609, by rfl⟩ : syracuseStep 519479 = 779219) B779219
theorem B1469801 : Blo 342753 1469801 := bstep (se 2 (by rfl) ⟨551175, by rfl⟩ : syracuseStep 1469801 = 1102351) B1102351
theorem B388507 : Blo 342753 388507 := bstep (se 1 (by rfl) ⟨291380, by rfl⟩ : syracuseStep 388507 = 582761) B582761
theorem B519647 : Blo 342753 519647 := bstep (se 1 (by rfl) ⟨389735, by rfl⟩ : syracuseStep 519647 = 779471) B779471
theorem B1470109 : Blo 342753 1470109 := bstep (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) B551291
theorem B519863 : Blo 342753 519863 := bstep (se 1 (by rfl) ⟨389897, by rfl⟩ : syracuseStep 519863 = 779795) B779795
theorem B3731159 : Blo 342753 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B5861159 : Blo 342753 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B520073 : Blo 342753 520073 := bstep (se 2 (by rfl) ⟨195027, by rfl⟩ : syracuseStep 520073 = 390055) B390055
theorem B651179 : Blo 342753 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B13463567 : Blo 342753 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B389479 : Blo 342753 389479 := bstep (se 1 (by rfl) ⟨292109, by rfl⟩ : syracuseStep 389479 = 584219) B584219
theorem B651719 : Blo 342753 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B2946131 : Blo 342753 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B2618567 : Blo 342753 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B1307933 : Blo 342753 1307933 := bstep (se 3 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 1307933 = 490475) B490475
theorem B652607 : Blo 342753 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B619987 : Blo 342753 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B1308251 : Blo 342753 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B2619053 : Blo 342753 2619053 := bstep (se 3 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 2619053 = 982145) B982145
theorem B489655 : Blo 342753 489655 := bstep (se 1 (by rfl) ⟨367241, by rfl⟩ : syracuseStep 489655 = 734483) B734483
theorem B653503 : Blo 342753 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B3307823 : Blo 342753 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B1735505 : Blo 342753 1735505 := bstep (se 2 (by rfl) ⟨650814, by rfl⟩ : syracuseStep 1735505 = 1301629) B1301629
theorem B2882429 : Blo 342753 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B654247 : Blo 342753 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B1474159 : Blo 342753 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B655303 : Blo 342753 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B983353 : Blo 342753 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B1180457 : Blo 342753 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B656191 : Blo 342753 656191 := bstep (se 1 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 656191 = 984287) B984287
theorem B525127 : Blo 342753 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B984059 : Blo 342753 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B526057 : Blo 342753 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B984811 : Blo 342753 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B13305707 : Blo 342753 13305707 := bstep (se 1 (by rfl) ⟨9979280, by rfl⟩ : syracuseStep 13305707 = 19958561) B19958561
theorem B657551 : Blo 342753 657551 := bstep (se 1 (by rfl) ⟨493163, by rfl⟩ : syracuseStep 657551 = 986327) B986327
theorem B1738907 : Blo 342753 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B2198141 : Blo 342753 2198141 := bstep (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) B824303
theorem B4295713 : Blo 342753 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B17174705 : Blo 342753 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B987385 : Blo 342753 987385 := bstep (se 2 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 987385 = 740539) B740539
theorem B3936599 : Blo 342753 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B1741175 : Blo 342753 1741175 := bstep (se 1 (by rfl) ⟨1305881, by rfl⟩ : syracuseStep 1741175 = 2611763) B2611763
theorem B47551211 : Blo 342753 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B16192315 : Blo 342753 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B1873367 : Blo 342753 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B2102867 : Blo 342753 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B37623851 : Blo 342753 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B4987453 : Blo 342753 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B2792015 : Blo 342753 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B3546287 : Blo 342753 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B826649 : Blo 342753 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B1974041 : Blo 342753 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B3907439 : Blo 342753 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B434479 : Blo 342753 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B1417609 : Blo 342753 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B1647145 : Blo 342753 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B2368111 : Blo 342753 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B1745711 : Blo 342753 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B435071 : Blo 342753 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B1746035 : Blo 342753 1746035 := bstep (se 1 (by rfl) ⟨1309526, by rfl⟩ : syracuseStep 1746035 = 2619053) B2619053
theorem B2205089 : Blo 342753 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B2205215 : Blo 342753 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B1157003 : Blo 342753 1157003 := bstep (se 1 (by rfl) ⟨867752, by rfl⟩ : syracuseStep 1157003 = 1735505) B1735505
theorem B2631689 : Blo 342753 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B1747655 : Blo 342753 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B437663 : Blo 342753 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B1158623 : Blo 342753 1158623 := bstep (se 1 (by rfl) ⟨868967, by rfl⟩ : syracuseStep 1158623 = 1737935) B1737935
theorem B831167 : Blo 342753 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B2240399 : Blo 342753 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B4993103 : Blo 342753 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B3945347 : Blo 342753 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B17839223 : Blo 342753 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B4437287 : Blo 342753 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B604139 : Blo 342753 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B1161431 : Blo 342753 1161431 := bstep (se 1 (by rfl) ⟨871073, by rfl⟩ : syracuseStep 1161431 = 1742147) B1742147
theorem B1161971 : Blo 342753 1161971 := bstep (se 1 (by rfl) ⟨871478, by rfl⟩ : syracuseStep 1161971 = 1742957) B1742957
theorem B932617 : Blo 342753 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B736123 : Blo 342753 736123 := bstep (se 1 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 736123 = 1104185) B1104185
theorem B7945147 : Blo 342753 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B342975 : Blo 342753 342975 := bstep (se 1 (by rfl) ⟨257231, by rfl⟩ : syracuseStep 342975 = 514463) B514463
theorem B343023 : Blo 342753 343023 := bstep (se 1 (by rfl) ⟨257267, by rfl⟩ : syracuseStep 343023 = 514535) B514535
theorem B3783827 : Blo 342753 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B343519 : Blo 342753 343519 := bstep (se 1 (by rfl) ⟨257639, by rfl⟩ : syracuseStep 343519 = 515279) B515279
theorem B343599 : Blo 342753 343599 := bstep (se 1 (by rfl) ⟨257699, by rfl⟩ : syracuseStep 343599 = 515399) B515399
theorem B343707 : Blo 342753 343707 := bstep (se 1 (by rfl) ⟨257780, by rfl⟩ : syracuseStep 343707 = 515561) B515561
theorem B343803 : Blo 342753 343803 := bstep (se 1 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 343803 = 515705) B515705
theorem B343967 : Blo 342753 343967 := bstep (se 1 (by rfl) ⟨257975, by rfl⟩ : syracuseStep 343967 = 515951) B515951
theorem B18890759 : Blo 342753 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B344423 : Blo 342753 344423 := bstep (se 1 (by rfl) ⟨258317, by rfl⟩ : syracuseStep 344423 = 516635) B516635
theorem B344543 : Blo 342753 344543 := bstep (se 1 (by rfl) ⟨258407, by rfl⟩ : syracuseStep 344543 = 516815) B516815
theorem B344551 : Blo 342753 344551 := bstep (se 1 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 344551 = 516827) B516827
theorem B9912851 : Blo 342753 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B738011 : Blo 342753 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B344827 : Blo 342753 344827 := bstep (se 1 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 344827 = 517241) B517241
theorem B1983521 : Blo 342753 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B345407 : Blo 342753 345407 := bstep (se 1 (by rfl) ⟨259055, by rfl⟩ : syracuseStep 345407 = 518111) B518111
theorem B345415 : Blo 342753 345415 := bstep (se 1 (by rfl) ⟨259061, by rfl⟩ : syracuseStep 345415 = 518123) B518123
theorem B345447 : Blo 342753 345447 := bstep (se 1 (by rfl) ⟨259085, by rfl⟩ : syracuseStep 345447 = 518171) B518171
theorem B345691 : Blo 342753 345691 := bstep (se 1 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 345691 = 518537) B518537
theorem B32720525 : Blo 342753 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B7096031 : Blo 342753 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B1099583 : Blo 342753 1099583 := bstep (se 1 (by rfl) ⟨824687, by rfl⟩ : syracuseStep 1099583 = 1649375) B1649375
theorem B772073 : Blo 342753 772073 := bstep (se 2 (by rfl) ⟨289527, by rfl⟩ : syracuseStep 772073 = 579055) B579055
theorem B7096511 : Blo 342753 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B346319 : Blo 342753 346319 := bstep (se 1 (by rfl) ⟨259739, by rfl⟩ : syracuseStep 346319 = 519479) B519479
theorem B1165535 : Blo 342753 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B346431 : Blo 342753 346431 := bstep (se 1 (by rfl) ⟨259823, by rfl⟩ : syracuseStep 346431 = 519647) B519647
theorem B772559 : Blo 342753 772559 := bstep (se 1 (by rfl) ⟨579419, by rfl⟩ : syracuseStep 772559 = 1158839) B1158839
theorem B346575 : Blo 342753 346575 := bstep (se 1 (by rfl) ⟨259931, by rfl⟩ : syracuseStep 346575 = 519863) B519863
theorem B772649 : Blo 342753 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B346715 : Blo 342753 346715 := bstep (se 1 (by rfl) ⟨260036, by rfl⟩ : syracuseStep 346715 = 520073) B520073
theorem B871337 : Blo 342753 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B773531 : Blo 342753 773531 := bstep (se 1 (by rfl) ⟨580148, by rfl⟩ : syracuseStep 773531 = 1160297) B1160297
theorem B871955 : Blo 342753 871955 := bstep (se 1 (by rfl) ⟨653966, by rfl⟩ : syracuseStep 871955 = 1307933) B1307933
theorem B872167 : Blo 342753 872167 := bstep (se 1 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 872167 = 1308251) B1308251
theorem B872329 : Blo 342753 872329 := bstep (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) B654247
theorem B25546711 : Blo 342753 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1921619 : Blo 342753 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B578441 : Blo 342753 578441 := bstep (se 2 (by rfl) ⟨216915, by rfl⟩ : syracuseStep 578441 = 433831) B433831
theorem B775079 : Blo 342753 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B873737 : Blo 342753 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B1103159 : Blo 342753 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B16864949 : Blo 342753 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B2938781 : Blo 342753 2938781 := bstep (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) B1102043
theorem B514175 : Blo 342753 514175 := bstep (se 1 (by rfl) ⟨385631, by rfl⟩ : syracuseStep 514175 = 771263) B771263
theorem B6609113 : Blo 342753 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B514271 : Blo 342753 514271 := bstep (se 1 (by rfl) ⟨385703, by rfl⟩ : syracuseStep 514271 = 771407) B771407
theorem B514331 : Blo 342753 514331 := bstep (se 1 (by rfl) ⟨385748, by rfl⟩ : syracuseStep 514331 = 771497) B771497
theorem B2218337 : Blo 342753 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B3824047 : Blo 342753 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B4250089 : Blo 342753 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B514655 : Blo 342753 514655 := bstep (se 1 (by rfl) ⟨385991, by rfl⟩ : syracuseStep 514655 = 771983) B771983
theorem B875195 : Blo 342753 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B514751 : Blo 342753 514751 := bstep (se 1 (by rfl) ⟨386063, by rfl⟩ : syracuseStep 514751 = 772127) B772127
theorem B514793 : Blo 342753 514793 := bstep (se 2 (by rfl) ⟨193047, by rfl⟩ : syracuseStep 514793 = 386095) B386095
theorem B2054969 : Blo 342753 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B514919 : Blo 342753 514919 := bstep (se 1 (by rfl) ⟨386189, by rfl⟩ : syracuseStep 514919 = 772379) B772379
theorem B514985 : Blo 342753 514985 := bstep (se 2 (by rfl) ⟨193119, by rfl⟩ : syracuseStep 514985 = 386239) B386239
theorem B515135 : Blo 342753 515135 := bstep (se 1 (by rfl) ⟨386351, by rfl⟩ : syracuseStep 515135 = 772703) B772703
theorem B515177 : Blo 342753 515177 := bstep (se 2 (by rfl) ⟨193191, by rfl⟩ : syracuseStep 515177 = 386383) B386383
theorem B875731 : Blo 342753 875731 := bstep (se 1 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 875731 = 1313597) B1313597
theorem B515303 : Blo 342753 515303 := bstep (se 1 (by rfl) ⟨386477, by rfl⟩ : syracuseStep 515303 = 772955) B772955
theorem B777545 : Blo 342753 777545 := bstep (se 2 (by rfl) ⟨291579, by rfl⟩ : syracuseStep 777545 = 583159) B583159
theorem B777563 : Blo 342753 777563 := bstep (se 1 (by rfl) ⟨583172, by rfl⟩ : syracuseStep 777563 = 1166345) B1166345
theorem B1957229 : Blo 342753 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B1465769 : Blo 342753 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B515807 : Blo 342753 515807 := bstep (se 1 (by rfl) ⟨386855, by rfl⟩ : syracuseStep 515807 = 773711) B773711
theorem B1400743 : Blo 342753 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B876521 : Blo 342753 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B516137 : Blo 342753 516137 := bstep (se 2 (by rfl) ⟨193551, by rfl⟩ : syracuseStep 516137 = 387103) B387103
theorem B1007657 : Blo 342753 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B516167 : Blo 342753 516167 := bstep (se 1 (by rfl) ⟨387125, by rfl⟩ : syracuseStep 516167 = 774251) B774251
theorem B581735 : Blo 342753 581735 := bstep (se 1 (by rfl) ⟨436301, by rfl⟩ : syracuseStep 581735 = 872603) B872603
theorem B516203 : Blo 342753 516203 := bstep (se 1 (by rfl) ⟨387152, by rfl⟩ : syracuseStep 516203 = 774305) B774305
theorem B516287 : Blo 342753 516287 := bstep (se 1 (by rfl) ⟨387215, by rfl⟩ : syracuseStep 516287 = 774431) B774431
theorem B778535 : Blo 342753 778535 := bstep (se 1 (by rfl) ⟨583901, by rfl⟩ : syracuseStep 778535 = 1167803) B1167803
theorem B516473 : Blo 342753 516473 := bstep (se 2 (by rfl) ⟨193677, by rfl⟩ : syracuseStep 516473 = 387355) B387355
theorem B1860029 : Blo 342753 1860029 := bstep (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) B697511
theorem B877139 : Blo 342753 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B8413793 : Blo 342753 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B778895 : Blo 342753 778895 := bstep (se 1 (by rfl) ⟨584171, by rfl⟩ : syracuseStep 778895 = 1168343) B1168343
theorem B516767 : Blo 342753 516767 := bstep (se 1 (by rfl) ⟨387575, by rfl⟩ : syracuseStep 516767 = 775151) B775151
theorem B778913 : Blo 342753 778913 := bstep (se 2 (by rfl) ⟨292092, by rfl⟩ : syracuseStep 778913 = 584185) B584185
theorem B1467067 : Blo 342753 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B778985 : Blo 342753 778985 := bstep (se 2 (by rfl) ⟨292119, by rfl⟩ : syracuseStep 778985 = 584239) B584239
theorem B385951 : Blo 342753 385951 := bstep (se 1 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 385951 = 578927) B578927
theorem B517103 : Blo 342753 517103 := bstep (se 1 (by rfl) ⟨387827, by rfl⟩ : syracuseStep 517103 = 775655) B775655
theorem B779273 : Blo 342753 779273 := bstep (se 2 (by rfl) ⟨292227, by rfl⟩ : syracuseStep 779273 = 584455) B584455
theorem B517211 : Blo 342753 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B517223 : Blo 342753 517223 := bstep (se 1 (by rfl) ⟨387917, by rfl⟩ : syracuseStep 517223 = 775835) B775835
theorem B976063 : Blo 342753 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B517355 : Blo 342753 517355 := bstep (se 1 (by rfl) ⟨388016, by rfl⟩ : syracuseStep 517355 = 776033) B776033
theorem B779561 : Blo 342753 779561 := bstep (se 2 (by rfl) ⟨292335, by rfl⟩ : syracuseStep 779561 = 584671) B584671
theorem B517487 : Blo 342753 517487 := bstep (se 1 (by rfl) ⟨388115, by rfl⟩ : syracuseStep 517487 = 776231) B776231
theorem B517607 : Blo 342753 517607 := bstep (se 1 (by rfl) ⟨388205, by rfl⟩ : syracuseStep 517607 = 776411) B776411
theorem B779831 : Blo 342753 779831 := bstep (se 1 (by rfl) ⟨584873, by rfl⟩ : syracuseStep 779831 = 1169747) B1169747
theorem B517739 : Blo 342753 517739 := bstep (se 1 (by rfl) ⟨388304, by rfl⟩ : syracuseStep 517739 = 776609) B776609
theorem B517787 : Blo 342753 517787 := bstep (se 1 (by rfl) ⟨388340, by rfl⟩ : syracuseStep 517787 = 776681) B776681
theorem B518009 : Blo 342753 518009 := bstep (se 2 (by rfl) ⟨194253, by rfl⟩ : syracuseStep 518009 = 388507) B388507
theorem B780191 : Blo 342753 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B1304531 : Blo 342753 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B1960145 : Blo 342753 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B518759 : Blo 342753 518759 := bstep (se 1 (by rfl) ⟨389069, by rfl⟩ : syracuseStep 518759 = 778139) B778139
theorem B2517637 : Blo 342753 2517637 := bstep (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) B472057
theorem B519035 : Blo 342753 519035 := bstep (se 1 (by rfl) ⟨389276, by rfl⟩ : syracuseStep 519035 = 778553) B778553
theorem B945103 : Blo 342753 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B519305 : Blo 342753 519305 := bstep (se 2 (by rfl) ⟨194739, by rfl⟩ : syracuseStep 519305 = 389479) B389479
theorem B1305791 : Blo 342753 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B519359 : Blo 342753 519359 := bstep (se 1 (by rfl) ⟨389519, by rfl⟩ : syracuseStep 519359 = 779039) B779039
theorem B519899 : Blo 342753 519899 := bstep (se 1 (by rfl) ⟨389924, by rfl⟩ : syracuseStep 519899 = 779849) B779849
theorem B618473 : Blo 342753 618473 := bstep (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) B463855
theorem B553015 : Blo 342753 553015 := bstep (se 1 (by rfl) ⟨414761, by rfl⟩ : syracuseStep 553015 = 829523) B829523
theorem B1241183 : Blo 342753 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1306975 : Blo 342753 1306975 := bstep (se 1 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 1306975 = 1960463) B1960463
theorem B979867 : Blo 342753 979867 := bstep (se 1 (by rfl) ⟨734900, by rfl⟩ : syracuseStep 979867 = 1469801) B1469801
theorem B488425 : Blo 342753 488425 := bstep (se 2 (by rfl) ⟨183159, by rfl⟩ : syracuseStep 488425 = 366319) B366319
theorem B2487439 : Blo 342753 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B8975711 : Blo 342753 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B652873 : Blo 342753 652873 := bstep (se 2 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 652873 = 489655) B489655
theorem B1964087 : Blo 342753 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B1669835 : Blo 342753 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1735991 : Blo 342753 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B1965545 : Blo 342753 1965545 := bstep (se 2 (by rfl) ⟨737079, by rfl⟩ : syracuseStep 1965545 = 1474159) B1474159
theorem B1736477 : Blo 342753 1736477 := bstep (se 3 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 1736477 = 651179) B651179
theorem B3309821 : Blo 342753 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B1311137 : Blo 342753 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B492007 : Blo 342753 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B786971 : Blo 342753 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B656039 : Blo 342753 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B2196193 : Blo 342753 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B1313081 : Blo 342753 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B2624399 : Blo 342753 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B1281079 : Blo 342753 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B1248911 : Blo 342753 1248911 := bstep (se 1 (by rfl) ⟨936683, by rfl⟩ : syracuseStep 1248911 = 1873367) B1873367
theorem B11243299 : Blo 342753 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B1478891 : Blo 342753 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B2364191 : Blo 342753 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B42374117 : Blo 342753 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1316027 : Blo 342753 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1611037 : Blo 342753 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B1316513 : Blo 342753 1316513 := bstep (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) B987385
theorem B5609195 : Blo 342753 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B1742633 : Blo 342753 1742633 := bstep (se 2 (by rfl) ⟨653487, by rfl⟩ : syracuseStep 1742633 = 1306975) B1306975
theorem B2630231 : Blo 342753 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B2958191 : Blo 342753 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1157327 : Blo 342753 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B1157651 : Blo 342753 1157651 := bstep (se 1 (by rfl) ⟨868238, by rfl⟩ : syracuseStep 1157651 = 1736477) B1736477
theorem B1649261 : Blo 342753 1649261 := bstep (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) B618473
theorem B12593839 : Blo 342753 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B1322347 : Blo 342753 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B3157481 : Blo 342753 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B700169 : Blo 342753 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B4730687 : Blo 342753 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B733055 : Blo 342753 733055 := bstep (se 1 (by rfl) ⟨549791, by rfl⟩ : syracuseStep 733055 = 1099583) B1099583
theorem B438367 : Blo 342753 438367 := bstep (se 1 (by rfl) ⟨328775, by rfl⟩ : syracuseStep 438367 = 657551) B657551
theorem B1159271 : Blo 342753 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B1160189 : Blo 342753 1160189 := bstep (se 3 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 1160189 = 435071) B435071
theorem B1160783 : Blo 342753 1160783 := bstep (se 1 (by rfl) ⟨870587, by rfl⟩ : syracuseStep 1160783 = 1741175) B1741175
theorem B31700807 : Blo 342753 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B3356849 : Blo 342753 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B1260137 : Blo 342753 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B25082567 : Blo 342753 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B342783 : Blo 342753 342783 := bstep (se 1 (by rfl) ⟨257087, by rfl⟩ : syracuseStep 342783 = 514175) B514175
theorem B4406075 : Blo 342753 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B342847 : Blo 342753 342847 := bstep (se 1 (by rfl) ⟨257135, by rfl⟩ : syracuseStep 342847 = 514271) B514271
theorem B342887 : Blo 342753 342887 := bstep (se 1 (by rfl) ⟨257165, by rfl⟩ : syracuseStep 342887 = 514331) B514331
theorem B343103 : Blo 342753 343103 := bstep (se 1 (by rfl) ⟨257327, by rfl⟩ : syracuseStep 343103 = 514655) B514655
theorem B343167 : Blo 342753 343167 := bstep (se 1 (by rfl) ⟨257375, by rfl⟩ : syracuseStep 343167 = 514751) B514751
theorem B343195 : Blo 342753 343195 := bstep (se 1 (by rfl) ⟨257396, by rfl⟩ : syracuseStep 343195 = 514793) B514793
theorem B343279 : Blo 342753 343279 := bstep (se 1 (by rfl) ⟨257459, by rfl⟩ : syracuseStep 343279 = 514919) B514919
theorem B343323 : Blo 342753 343323 := bstep (se 1 (by rfl) ⟨257492, by rfl⟩ : syracuseStep 343323 = 514985) B514985
theorem B343423 : Blo 342753 343423 := bstep (se 1 (by rfl) ⟨257567, by rfl⟩ : syracuseStep 343423 = 515135) B515135
theorem B343451 : Blo 342753 343451 := bstep (se 1 (by rfl) ⟨257588, by rfl⟩ : syracuseStep 343451 = 515177) B515177
theorem B343535 : Blo 342753 343535 := bstep (se 1 (by rfl) ⟨257651, by rfl⟩ : syracuseStep 343535 = 515303) B515303
theorem B1162889 : Blo 342753 1162889 := bstep (se 2 (by rfl) ⟨436083, by rfl⟩ : syracuseStep 1162889 = 872167) B872167
theorem B343871 : Blo 342753 343871 := bstep (se 1 (by rfl) ⟨257903, by rfl⟩ : syracuseStep 343871 = 515807) B515807
theorem B1163105 : Blo 342753 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B2604959 : Blo 342753 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B34062281 : Blo 342753 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B344091 : Blo 342753 344091 := bstep (se 1 (by rfl) ⟨258068, by rfl⟩ : syracuseStep 344091 = 516137) B516137
theorem B671771 : Blo 342753 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B344111 : Blo 342753 344111 := bstep (se 1 (by rfl) ⟨258083, by rfl⟩ : syracuseStep 344111 = 516167) B516167
theorem B344135 : Blo 342753 344135 := bstep (se 1 (by rfl) ⟨258101, by rfl⟩ : syracuseStep 344135 = 516203) B516203
theorem B737353 : Blo 342753 737353 := bstep (se 2 (by rfl) ⟨276507, by rfl⟩ : syracuseStep 737353 = 553015) B553015
theorem B344191 : Blo 342753 344191 := bstep (se 1 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 344191 = 516287) B516287
theorem B344315 : Blo 342753 344315 := bstep (se 1 (by rfl) ⟨258236, by rfl⟩ : syracuseStep 344315 = 516473) B516473
theorem B344511 : Blo 342753 344511 := bstep (se 1 (by rfl) ⟨258383, by rfl⟩ : syracuseStep 344511 = 516767) B516767
theorem B18924029 : Blo 342753 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1163807 : Blo 342753 1163807 := bstep (se 1 (by rfl) ⟨872855, by rfl⟩ : syracuseStep 1163807 = 1745711) B1745711
theorem B344735 : Blo 342753 344735 := bstep (se 1 (by rfl) ⟨258551, by rfl⟩ : syracuseStep 344735 = 517103) B517103
theorem B344807 : Blo 342753 344807 := bstep (se 1 (by rfl) ⟨258605, by rfl⟩ : syracuseStep 344807 = 517211) B517211
theorem B344815 : Blo 342753 344815 := bstep (se 1 (by rfl) ⟨258611, by rfl⟩ : syracuseStep 344815 = 517223) B517223
theorem B1164023 : Blo 342753 1164023 := bstep (se 1 (by rfl) ⟨873017, by rfl⟩ : syracuseStep 1164023 = 1746035) B1746035
theorem B344903 : Blo 342753 344903 := bstep (se 1 (by rfl) ⟨258677, by rfl⟩ : syracuseStep 344903 = 517355) B517355
theorem B344991 : Blo 342753 344991 := bstep (se 1 (by rfl) ⟨258743, by rfl⟩ : syracuseStep 344991 = 517487) B517487
theorem B345071 : Blo 342753 345071 := bstep (se 1 (by rfl) ⟨258803, by rfl⟩ : syracuseStep 345071 = 517607) B517607
theorem B345159 : Blo 342753 345159 := bstep (se 1 (by rfl) ⟨258869, by rfl⟩ : syracuseStep 345159 = 517739) B517739
theorem B345191 : Blo 342753 345191 := bstep (se 1 (by rfl) ⟨258893, by rfl⟩ : syracuseStep 345191 = 517787) B517787
theorem B345339 : Blo 342753 345339 := bstep (se 1 (by rfl) ⟨259004, by rfl⟩ : syracuseStep 345339 = 518009) B518009
theorem B771335 : Blo 342753 771335 := bstep (se 1 (by rfl) ⟨578501, by rfl⟩ : syracuseStep 771335 = 1157003) B1157003
theorem B869687 : Blo 342753 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B1754459 : Blo 342753 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B345839 : Blo 342753 345839 := bstep (se 1 (by rfl) ⟨259379, by rfl⟩ : syracuseStep 345839 = 518759) B518759
theorem B1165103 : Blo 342753 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B346023 : Blo 342753 346023 := bstep (se 1 (by rfl) ⟨259517, by rfl⟩ : syracuseStep 346023 = 519035) B519035
theorem B346203 : Blo 342753 346203 := bstep (se 1 (by rfl) ⟨259652, by rfl⟩ : syracuseStep 346203 = 519305) B519305
theorem B870497 : Blo 342753 870497 := bstep (se 2 (by rfl) ⟨326436, by rfl⟩ : syracuseStep 870497 = 652873) B652873
theorem B870527 : Blo 342753 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B346239 : Blo 342753 346239 := bstep (se 1 (by rfl) ⟨259679, by rfl⟩ : syracuseStep 346239 = 519359) B519359
theorem B772415 : Blo 342753 772415 := bstep (se 1 (by rfl) ⟨579311, by rfl⟩ : syracuseStep 772415 = 1158623) B1158623
theorem B346599 : Blo 342753 346599 := bstep (se 1 (by rfl) ⟨259949, by rfl⟩ : syracuseStep 346599 = 519899) B519899
theorem B1493599 : Blo 342753 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B3328735 : Blo 342753 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B5098729 : Blo 342753 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B5983807 : Blo 342753 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1167101 : Blo 342753 1167101 := bstep (se 3 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 1167101 = 437663) B437663
theorem B2805637 : Blo 342753 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B774287 : Blo 342753 774287 := bstep (se 1 (by rfl) ⟨580715, by rfl⟩ : syracuseStep 774287 = 1161431) B1161431
theorem B1167641 : Blo 342753 1167641 := bstep (se 2 (by rfl) ⟨437865, by rfl⟩ : syracuseStep 1167641 = 875731) B875731
theorem B774647 : Blo 342753 774647 := bstep (se 1 (by rfl) ⟨580985, by rfl⟩ : syracuseStep 774647 = 1161971) B1161971
theorem B6608567 : Blo 342753 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B579305 : Blo 342753 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B1890145 : Blo 342753 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B1956089 : Blo 342753 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B874921 : Blo 342753 874921 := bstep (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) B656191
theorem B21813683 : Blo 342753 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B514601 : Blo 342753 514601 := bstep (se 2 (by rfl) ⟨192975, by rfl⟩ : syracuseStep 514601 = 385951) B385951
theorem B8870471 : Blo 342753 8870471 := bstep (se 1 (by rfl) ⟨6652853, by rfl⟩ : syracuseStep 8870471 = 13305707) B13305707
theorem B514715 : Blo 342753 514715 := bstep (se 1 (by rfl) ⟨386036, by rfl⟩ : syracuseStep 514715 = 772073) B772073
theorem B777023 : Blo 342753 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B1301417 : Blo 342753 1301417 := bstep (se 2 (by rfl) ⟨488031, by rfl⟩ : syracuseStep 1301417 = 976063) B976063
theorem B515039 : Blo 342753 515039 := bstep (se 1 (by rfl) ⟨386279, by rfl⟩ : syracuseStep 515039 = 772559) B772559
theorem B515099 : Blo 342753 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B1465427 : Blo 342753 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B183196853 : Blo 342753 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B580891 : Blo 342753 580891 := bstep (se 1 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 580891 = 871337) B871337
theorem B515687 : Blo 342753 515687 := bstep (se 1 (by rfl) ⟨386765, by rfl⟩ : syracuseStep 515687 = 773531) B773531
theorem B581303 : Blo 342753 581303 := bstep (se 1 (by rfl) ⟨435977, by rfl⟩ : syracuseStep 581303 = 871955) B871955
theorem B22667141 : Blo 342753 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B385627 : Blo 342753 385627 := bstep (se 1 (by rfl) ⟨289220, by rfl⟩ : syracuseStep 385627 = 578441) B578441
theorem B516719 : Blo 342753 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B2941757 : Blo 342753 2941757 := bstep (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) B1103159
theorem B582491 : Blo 342753 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B1401911 : Blo 342753 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B1959187 : Blo 342753 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B5727617 : Blo 342753 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B4973957 : Blo 342753 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B1861343 : Blo 342753 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B583463 : Blo 342753 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B1369979 : Blo 342753 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B551099 : Blo 342753 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B518363 : Blo 342753 518363 := bstep (se 1 (by rfl) ⟨388772, by rfl⟩ : syracuseStep 518363 = 777545) B777545
theorem B518375 : Blo 342753 518375 := bstep (se 1 (by rfl) ⟨388781, by rfl⟩ : syracuseStep 518375 = 777563) B777563
theorem B1304819 : Blo 342753 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B977179 : Blo 342753 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B584347 : Blo 342753 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B387823 : Blo 342753 387823 := bstep (se 1 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 387823 = 581735) B581735
theorem B519023 : Blo 342753 519023 := bstep (se 1 (by rfl) ⟨389267, by rfl⟩ : syracuseStep 519023 = 778535) B778535
theorem B1240019 : Blo 342753 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B584759 : Blo 342753 584759 := bstep (se 1 (by rfl) ⟨438569, by rfl⟩ : syracuseStep 584759 = 877139) B877139
theorem B519263 : Blo 342753 519263 := bstep (se 1 (by rfl) ⟨389447, by rfl⟩ : syracuseStep 519263 = 778895) B778895
theorem B519275 : Blo 342753 519275 := bstep (se 1 (by rfl) ⟨389456, by rfl⟩ : syracuseStep 519275 = 778913) B778913
theorem B519323 : Blo 342753 519323 := bstep (se 1 (by rfl) ⟨389492, by rfl⟩ : syracuseStep 519323 = 778985) B778985
theorem B519515 : Blo 342753 519515 := bstep (se 1 (by rfl) ⟨389636, by rfl⟩ : syracuseStep 519515 = 779273) B779273
theorem B13266341 : Blo 342753 13266341 := bstep (se 4 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 13266341 = 2487439) B2487439
theorem B519707 : Blo 342753 519707 := bstep (se 1 (by rfl) ⟨389780, by rfl⟩ : syracuseStep 519707 = 779561) B779561
theorem B1470059 : Blo 342753 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1470143 : Blo 342753 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B519887 : Blo 342753 519887 := bstep (se 1 (by rfl) ⟨389915, by rfl⟩ : syracuseStep 519887 = 779831) B779831
theorem B21589753 : Blo 342753 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1306489 : Blo 342753 1306489 := bstep (se 2 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 1306489 = 979867) B979867
theorem B520127 : Blo 342753 520127 := bstep (se 1 (by rfl) ⟨390095, by rfl⟩ : syracuseStep 520127 = 780191) B780191
theorem B651233 : Blo 342753 651233 := bstep (se 2 (by rfl) ⟨244212, by rfl⟩ : syracuseStep 651233 = 488425) B488425
theorem B1306763 : Blo 342753 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B4452893 : Blo 342753 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B554111 : Blo 342753 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B11892815 : Blo 342753 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B6649937 : Blo 342753 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B981497 : Blo 342753 981497 := bstep (se 2 (by rfl) ⟨368061, by rfl⟩ : syracuseStep 981497 = 736123) B736123
theorem B1309391 : Blo 342753 1309391 := bstep (se 1 (by rfl) ⟨982043, by rfl⟩ : syracuseStep 1309391 = 1964087) B1964087
theorem B2522551 : Blo 342753 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1310363 : Blo 342753 1310363 := bstep (se 1 (by rfl) ⟨982772, by rfl⟩ : syracuseStep 1310363 = 1965545) B1965545
theorem B1867657 : Blo 342753 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B983137 : Blo 342753 983137 := bstep (se 2 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 983137 = 737353) B737353
theorem B12616019 : Blo 342753 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B524647 : Blo 342753 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B656009 : Blo 342753 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B985927 : Blo 342753 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B1576127 : Blo 342753 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B28249411 : Blo 342753 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B3739463 : Blo 342753 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B122131235 : Blo 342753 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B1741985 : Blo 342753 1741985 := bstep (se 2 (by rfl) ⟨653244, by rfl⟩ : syracuseStep 1741985 = 1306489) B1306489
theorem B3740849 : Blo 342753 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B8951597 : Blo 342753 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B1972127 : Blo 342753 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B3315971 : Blo 342753 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B58169821 : Blo 342753 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B367399 : Blo 342753 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B826679 : Blo 342753 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B3153791 : Blo 342753 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B434155 : Blo 342753 434155 := bstep (se 1 (by rfl) ⟨325616, by rfl⟩ : syracuseStep 434155 = 651233) B651233
theorem B369407 : Blo 342753 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B4433291 : Blo 342753 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B16721711 : Blo 342753 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B2206547 : Blo 342753 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B2928257 : Blo 342753 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B1749437 : Blo 342753 1749437 := bstep (se 3 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 1749437 = 656039) B656039
theorem B1749599 : Blo 342753 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B832607 : Blo 342753 832607 := bstep (se 1 (by rfl) ⟨624455, by rfl⟩ : syracuseStep 832607 = 1248911) B1248911
theorem B16791785 : Blo 342753 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B4438313 : Blo 342753 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B4405711 : Blo 342753 4405711 := bstep (se 1 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 4405711 = 6608567) B6608567
theorem B1161755 : Blo 342753 1161755 := bstep (se 1 (by rfl) ⟨871316, by rfl⟩ : syracuseStep 1161755 = 1742633) B1742633
theorem B6798305 : Blo 342753 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B343067 : Blo 342753 343067 := bstep (se 1 (by rfl) ⟨257300, by rfl⟩ : syracuseStep 343067 = 514601) B514601
theorem B5913647 : Blo 342753 5913647 := bstep (se 1 (by rfl) ⟨4435235, by rfl⟩ : syracuseStep 5913647 = 8870471) B8870471
theorem B343143 : Blo 342753 343143 := bstep (se 1 (by rfl) ⟨257357, by rfl⟩ : syracuseStep 343143 = 514715) B514715
theorem B867611 : Blo 342753 867611 := bstep (se 1 (by rfl) ⟨650708, by rfl⟩ : syracuseStep 867611 = 1301417) B1301417
theorem B343359 : Blo 342753 343359 := bstep (se 1 (by rfl) ⟨257519, by rfl⟩ : syracuseStep 343359 = 515039) B515039
theorem B343399 : Blo 342753 343399 := bstep (se 1 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 343399 = 515099) B515099
theorem B7978409 : Blo 342753 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B28786337 : Blo 342753 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B14991065 : Blo 342753 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B343791 : Blo 342753 343791 := bstep (se 1 (by rfl) ⟨257843, by rfl⟩ : syracuseStep 343791 = 515687) B515687
theorem B6832421 : Blo 342753 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B1753487 : Blo 342753 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B344479 : Blo 342753 344479 := bstep (se 1 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 344479 = 516719) B516719
theorem B934607 : Blo 342753 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B3818411 : Blo 342753 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B771551 : Blo 342753 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B345575 : Blo 342753 345575 := bstep (se 1 (by rfl) ⟨259181, by rfl⟩ : syracuseStep 345575 = 518363) B518363
theorem B345583 : Blo 342753 345583 := bstep (se 1 (by rfl) ⟨259187, by rfl⟩ : syracuseStep 345583 = 518375) B518375
theorem B869879 : Blo 342753 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B771767 : Blo 342753 771767 := bstep (se 1 (by rfl) ⟨578825, by rfl⟩ : syracuseStep 771767 = 1157651) B1157651
theorem B2148049 : Blo 342753 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1099507 : Blo 342753 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B346015 : Blo 342753 346015 := bstep (se 1 (by rfl) ⟨259511, by rfl⟩ : syracuseStep 346015 = 519023) B519023
theorem B346175 : Blo 342753 346175 := bstep (se 1 (by rfl) ⟨259631, by rfl⟩ : syracuseStep 346175 = 519263) B519263
theorem B346183 : Blo 342753 346183 := bstep (se 1 (by rfl) ⟨259637, by rfl⟩ : syracuseStep 346183 = 519275) B519275
theorem B346215 : Blo 342753 346215 := bstep (se 1 (by rfl) ⟨259661, by rfl⟩ : syracuseStep 346215 = 519323) B519323
theorem B346343 : Blo 342753 346343 := bstep (se 1 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 346343 = 519515) B519515
theorem B346471 : Blo 342753 346471 := bstep (se 1 (by rfl) ⟨259853, by rfl⟩ : syracuseStep 346471 = 519707) B519707
theorem B346591 : Blo 342753 346591 := bstep (se 1 (by rfl) ⟨259943, by rfl⟩ : syracuseStep 346591 = 519887) B519887
theorem B346751 : Blo 342753 346751 := bstep (se 1 (by rfl) ⟨260063, by rfl⟩ : syracuseStep 346751 = 520127) B520127
theorem B772847 : Blo 342753 772847 := bstep (se 1 (by rfl) ⟨579635, by rfl⟩ : syracuseStep 772847 = 1159271) B1159271
theorem B871175 : Blo 342753 871175 := bstep (se 1 (by rfl) ⟨653381, by rfl⟩ : syracuseStep 871175 = 1306763) B1306763
theorem B2968595 : Blo 342753 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1166561 : Blo 342753 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B773459 : Blo 342753 773459 := bstep (se 1 (by rfl) ⟨580094, by rfl⟩ : syracuseStep 773459 = 1160189) B1160189
theorem B773855 : Blo 342753 773855 := bstep (se 1 (by rfl) ⟨580391, by rfl⟩ : syracuseStep 773855 = 1160783) B1160783
theorem B774521 : Blo 342753 774521 := bstep (se 2 (by rfl) ⟨290445, by rfl⟩ : syracuseStep 774521 = 580891) B580891
theorem B840091 : Blo 342753 840091 := bstep (se 1 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 840091 = 1260137) B1260137
theorem B872927 : Blo 342753 872927 := bstep (se 1 (by rfl) ⟨654695, by rfl⟩ : syracuseStep 872927 = 1309391) B1309391
theorem B10080773 : Blo 342753 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B2937383 : Blo 342753 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B3363401 : Blo 342753 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B1954813 : Blo 342753 1954813 := bstep (se 3 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 1954813 = 733055) B733055
theorem B60445709 : Blo 342753 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B775259 : Blo 342753 775259 := bstep (se 1 (by rfl) ⟨581444, by rfl⟩ : syracuseStep 775259 = 1162889) B1162889
theorem B873575 : Blo 342753 873575 := bstep (se 1 (by rfl) ⟨655181, by rfl⟩ : syracuseStep 873575 = 1310363) B1310363
theorem B775403 : Blo 342753 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B1791389 : Blo 342753 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B874091 : Blo 342753 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B775871 : Blo 342753 775871 := bstep (se 1 (by rfl) ⟨581903, by rfl⟩ : syracuseStep 775871 = 1163807) B1163807
theorem B776015 : Blo 342753 776015 := bstep (se 1 (by rfl) ⟨582011, by rfl⟩ : syracuseStep 776015 = 1164023) B1164023
theorem B514169 : Blo 342753 514169 := bstep (se 2 (by rfl) ⟨192813, by rfl⟩ : syracuseStep 514169 = 385627) B385627
theorem B514223 : Blo 342753 514223 := bstep (se 1 (by rfl) ⟨385667, by rfl⟩ : syracuseStep 514223 = 771335) B771335
theorem B579791 : Blo 342753 579791 := bstep (se 1 (by rfl) ⟨434843, by rfl⟩ : syracuseStep 579791 = 869687) B869687
theorem B1169639 : Blo 342753 1169639 := bstep (se 1 (by rfl) ⟨877229, by rfl⟩ : syracuseStep 1169639 = 1754459) B1754459
theorem B776735 : Blo 342753 776735 := bstep (se 1 (by rfl) ⟨582551, by rfl⟩ : syracuseStep 776735 = 1165103) B1165103
theorem B580331 : Blo 342753 580331 := bstep (se 1 (by rfl) ⟨435248, by rfl⟩ : syracuseStep 580331 = 870497) B870497
theorem B580351 : Blo 342753 580351 := bstep (se 1 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 580351 = 870527) B870527
theorem B875387 : Blo 342753 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B514943 : Blo 342753 514943 := bstep (se 1 (by rfl) ⟨386207, by rfl⟩ : syracuseStep 514943 = 772415) B772415
theorem B2612249 : Blo 342753 2612249 := bstep (se 2 (by rfl) ⟨979593, by rfl⟩ : syracuseStep 2612249 = 1959187) B1959187
theorem B778067 : Blo 342753 778067 := bstep (se 1 (by rfl) ⟨583550, by rfl⟩ : syracuseStep 778067 = 1167101) B1167101
theorem B516191 : Blo 342753 516191 := bstep (se 1 (by rfl) ⟨387143, by rfl⟩ : syracuseStep 516191 = 774287) B774287
theorem B778427 : Blo 342753 778427 := bstep (se 1 (by rfl) ⟨583820, by rfl⟩ : syracuseStep 778427 = 1167641) B1167641
theorem B516431 : Blo 342753 516431 := bstep (se 1 (by rfl) ⟨387323, by rfl⟩ : syracuseStep 516431 = 774647) B774647
theorem B1302905 : Blo 342753 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B877351 : Blo 342753 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B1991465 : Blo 342753 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B779129 : Blo 342753 779129 := bstep (se 2 (by rfl) ⟨292173, by rfl⟩ : syracuseStep 779129 = 584347) B584347
theorem B517097 : Blo 342753 517097 := bstep (se 2 (by rfl) ⟨193911, by rfl⟩ : syracuseStep 517097 = 387823) B387823
theorem B877675 : Blo 342753 877675 := bstep (se 1 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 877675 = 1316513) B1316513
theorem B386203 : Blo 342753 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B1304059 : Blo 342753 1304059 := bstep (se 1 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 1304059 = 1956089) B1956089
theorem B1763129 : Blo 342753 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B518015 : Blo 342753 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B976951 : Blo 342753 976951 := bstep (se 1 (by rfl) ⟨732713, by rfl⟩ : syracuseStep 976951 = 1465427) B1465427
theorem B387535 : Blo 342753 387535 := bstep (se 1 (by rfl) ⟨290651, by rfl⟩ : syracuseStep 387535 = 581303) B581303
theorem B584489 : Blo 342753 584489 := bstep (se 2 (by rfl) ⟨219183, by rfl⟩ : syracuseStep 584489 = 438367) B438367
theorem B1961171 : Blo 342753 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B388327 : Blo 342753 388327 := bstep (se 1 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 388327 = 582491) B582491
theorem B1240895 : Blo 342753 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B388975 : Blo 342753 388975 := bstep (se 1 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 388975 = 583463) B583463
theorem B913319 : Blo 342753 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B389839 : Blo 342753 389839 := bstep (se 1 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 389839 = 584759) B584759
theorem B8844227 : Blo 342753 8844227 := bstep (se 1 (by rfl) ⟨6633170, by rfl⟩ : syracuseStep 8844227 = 13266341) B13266341
theorem B980039 : Blo 342753 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B980095 : Blo 342753 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B7468469 : Blo 342753 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B21133871 : Blo 342753 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B8419949 : Blo 342753 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B7928543 : Blo 342753 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B654331 : Blo 342753 654331 := bstep (se 1 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 654331 = 981497) B981497
theorem B2490209 : Blo 342753 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1736639 : Blo 342753 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B22708187 : Blo 342753 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B1310849 : Blo 342753 1310849 := bstep (se 2 (by rfl) ⟨491568, by rfl⟩ : syracuseStep 1310849 = 983137) B983137
theorem B4554947 : Blo 342753 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B623071 : Blo 342753 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B1738745 : Blo 342753 1738745 := bstep (se 2 (by rfl) ⟨652029, by rfl⟩ : syracuseStep 1738745 = 1304059) B1304059
theorem B985085 : Blo 342753 985085 := bstep (se 3 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 985085 = 369407) B369407
theorem B1050751 : Blo 342753 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B2492975 : Blo 342753 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B6720515 : Blo 342753 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B2493899 : Blo 342753 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B1314569 : Blo 342753 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B5967731 : Blo 342753 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B1314751 : Blo 342753 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B1741499 : Blo 342753 1741499 := bstep (se 1 (by rfl) ⟨1306124, by rfl⟩ : syracuseStep 1741499 = 2612249) B2612249
theorem B2102527 : Blo 342753 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B1120121 : Blo 342753 1120121 := bstep (se 2 (by rfl) ⟨420045, by rfl⟩ : syracuseStep 1120121 = 840091) B840091
theorem B2955527 : Blo 342753 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B11147807 : Blo 342753 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B827263 : Blo 342753 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B5874281 : Blo 342753 5874281 := bstep (se 2 (by rfl) ⟨2202855, by rfl⟩ : syracuseStep 5874281 = 4405711) B4405711
theorem B2958875 : Blo 342753 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B5613299 : Blo 342753 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B5285695 : Blo 342753 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B4532203 : Blo 342753 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B3942431 : Blo 342753 3942431 := bstep (se 1 (by rfl) ⟨2956823, by rfl⟩ : syracuseStep 3942431 = 5913647) B5913647
theorem B5318939 : Blo 342753 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B1157759 : Blo 342753 1157759 := bstep (se 1 (by rfl) ⟨868319, by rfl⟩ : syracuseStep 1157759 = 1736639) B1736639
theorem B437339 : Blo 342753 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B699529 : Blo 342753 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B1979063 : Blo 342753 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B2864065 : Blo 342753 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1161323 : Blo 342753 1161323 := bstep (se 1 (by rfl) ⟨870992, by rfl⟩ : syracuseStep 1161323 = 1741985) B1741985
theorem B1194259 : Blo 342753 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B342779 : Blo 342753 342779 := bstep (se 1 (by rfl) ⟨257084, by rfl⟩ : syracuseStep 342779 = 514169) B514169
theorem B342815 : Blo 342753 342815 := bstep (se 1 (by rfl) ⟨257111, by rfl⟩ : syracuseStep 342815 = 514223) B514223
theorem B2210647 : Blo 342753 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B37665881 : Blo 342753 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B343295 : Blo 342753 343295 := bstep (se 1 (by rfl) ⟨257471, by rfl⟩ : syracuseStep 343295 = 514943) B514943
theorem B344127 : Blo 342753 344127 := bstep (se 1 (by rfl) ⟨258095, by rfl⟩ : syracuseStep 344127 = 516191) B516191
theorem B344287 : Blo 342753 344287 := bstep (se 1 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 344287 = 516431) B516431
theorem B868603 : Blo 342753 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B1327643 : Blo 342753 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B344731 : Blo 342753 344731 := bstep (se 1 (by rfl) ⟨258548, by rfl⟩ : syracuseStep 344731 = 517097) B517097
theorem B345343 : Blo 342753 345343 := bstep (se 1 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 345343 = 518015) B518015
theorem B2606417 : Blo 342753 2606417 := bstep (se 2 (by rfl) ⟨977406, by rfl⟩ : syracuseStep 2606417 = 1954813) B1954813
theorem B1952171 : Blo 342753 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B608879 : Blo 342753 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B1166291 : Blo 342753 1166291 := bstep (se 1 (by rfl) ⟨874718, by rfl⟩ : syracuseStep 1166291 = 1749437) B1749437
theorem B1166399 : Blo 342753 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B773801 : Blo 342753 773801 := bstep (se 2 (by rfl) ⟨290175, by rfl⟩ : syracuseStep 773801 = 580351) B580351
theorem B872441 : Blo 342753 872441 := bstep (se 2 (by rfl) ⟨327165, by rfl⟩ : syracuseStep 872441 = 654331) B654331
theorem B11194523 : Blo 342753 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B774503 : Blo 342753 774503 := bstep (se 1 (by rfl) ⟨580877, by rfl⟩ : syracuseStep 774503 = 1161755) B1161755
theorem B578407 : Blo 342753 578407 := bstep (se 1 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 578407 = 867611) B867611
theorem B19190891 : Blo 342753 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B1660139 : Blo 342753 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B578873 : Blo 342753 578873 := bstep (se 2 (by rfl) ⟨217077, by rfl⟩ : syracuseStep 578873 = 434155) B434155
theorem B8410679 : Blo 342753 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B1168991 : Blo 342753 1168991 := bstep (se 1 (by rfl) ⟨876743, by rfl⟩ : syracuseStep 1168991 = 1753487) B1753487
theorem B2545607 : Blo 342753 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B514367 : Blo 342753 514367 := bstep (se 1 (by rfl) ⟨385775, by rfl⟩ : syracuseStep 514367 = 771551) B771551
theorem B579919 : Blo 342753 579919 := bstep (se 1 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 579919 = 869879) B869879
theorem B1169801 : Blo 342753 1169801 := bstep (se 2 (by rfl) ⟨438675, by rfl⟩ : syracuseStep 1169801 = 877351) B877351
theorem B514511 : Blo 342753 514511 := bstep (se 1 (by rfl) ⟨385883, by rfl⟩ : syracuseStep 514511 = 771767) B771767
theorem B1170233 : Blo 342753 1170233 := bstep (se 2 (by rfl) ⟨438837, by rfl⟩ : syracuseStep 1170233 = 877675) B877675
theorem B8969069 : Blo 342753 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B514937 : Blo 342753 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B515231 : Blo 342753 515231 := bstep (se 1 (by rfl) ⟨386423, by rfl⟩ : syracuseStep 515231 = 772847) B772847
theorem B580783 : Blo 342753 580783 := bstep (se 1 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 580783 = 871175) B871175
theorem B777707 : Blo 342753 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B515639 : Blo 342753 515639 := bstep (se 1 (by rfl) ⟨386729, by rfl⟩ : syracuseStep 515639 = 773459) B773459
theorem B1466009 : Blo 342753 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B515903 : Blo 342753 515903 := bstep (se 1 (by rfl) ⟨386927, by rfl⟩ : syracuseStep 515903 = 773855) B773855
theorem B1302601 : Blo 342753 1302601 := bstep (se 2 (by rfl) ⟨488475, by rfl⟩ : syracuseStep 1302601 = 976951) B976951
theorem B516347 : Blo 342753 516347 := bstep (se 1 (by rfl) ⟨387260, by rfl⟩ : syracuseStep 516347 = 774521) B774521
theorem B581951 : Blo 342753 581951 := bstep (se 1 (by rfl) ⟨436463, by rfl⟩ : syracuseStep 581951 = 872927) B872927
theorem B1958255 : Blo 342753 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B81420823 : Blo 342753 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B516713 : Blo 342753 516713 := bstep (se 2 (by rfl) ⟨193767, by rfl⟩ : syracuseStep 516713 = 387535) B387535
theorem B40297139 : Blo 342753 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B516839 : Blo 342753 516839 := bstep (se 1 (by rfl) ⟨387629, by rfl⟩ : syracuseStep 516839 = 775259) B775259
theorem B582383 : Blo 342753 582383 := bstep (se 1 (by rfl) ⟨436787, by rfl⟩ : syracuseStep 582383 = 873575) B873575
theorem B516935 : Blo 342753 516935 := bstep (se 1 (by rfl) ⟨387701, by rfl⟩ : syracuseStep 516935 = 775403) B775403
theorem B582727 : Blo 342753 582727 := bstep (se 1 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 582727 = 874091) B874091
theorem B517247 : Blo 342753 517247 := bstep (se 1 (by rfl) ⟨387935, by rfl⟩ : syracuseStep 517247 = 775871) B775871
theorem B517343 : Blo 342753 517343 := bstep (se 1 (by rfl) ⟨388007, by rfl⟩ : syracuseStep 517343 = 776015) B776015
theorem B386527 : Blo 342753 386527 := bstep (se 1 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 386527 = 579791) B579791
theorem B779759 : Blo 342753 779759 := bstep (se 1 (by rfl) ⟨584819, by rfl⟩ : syracuseStep 779759 = 1169639) B1169639
theorem B1959461 : Blo 342753 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B517769 : Blo 342753 517769 := bstep (se 2 (by rfl) ⟨194163, by rfl⟩ : syracuseStep 517769 = 388327) B388327
theorem B517823 : Blo 342753 517823 := bstep (se 1 (by rfl) ⟨388367, by rfl⟩ : syracuseStep 517823 = 776735) B776735
theorem B386887 : Blo 342753 386887 := bstep (se 1 (by rfl) ⟨290165, by rfl⟩ : syracuseStep 386887 = 580331) B580331
theorem B583591 : Blo 342753 583591 := bstep (se 1 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 583591 = 875387) B875387
theorem B551119 : Blo 342753 551119 := bstep (se 1 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 551119 = 826679) B826679
theorem B518633 : Blo 342753 518633 := bstep (se 2 (by rfl) ⟨194487, by rfl⟩ : syracuseStep 518633 = 388975) B388975
theorem B518711 : Blo 342753 518711 := bstep (se 1 (by rfl) ⟨389033, by rfl⟩ : syracuseStep 518711 = 778067) B778067
theorem B518951 : Blo 342753 518951 := bstep (se 1 (by rfl) ⟨389213, by rfl⟩ : syracuseStep 518951 = 778427) B778427
theorem B519419 : Blo 342753 519419 := bstep (se 1 (by rfl) ⟨389564, by rfl⟩ : syracuseStep 519419 = 779129) B779129
theorem B519785 : Blo 342753 519785 := bstep (se 2 (by rfl) ⟨194919, by rfl⟩ : syracuseStep 519785 = 389839) B389839
theorem B1175419 : Blo 342753 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B1306793 : Blo 342753 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B389659 : Blo 342753 389659 := bstep (se 1 (by rfl) ⟨292244, by rfl⟩ : syracuseStep 389659 = 584489) B584489
theorem B1471031 : Blo 342753 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B1307447 : Blo 342753 1307447 := bstep (se 1 (by rfl) ⟨980585, by rfl⟩ : syracuseStep 1307447 = 1961171) B1961171
theorem B77559761 : Blo 342753 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B5896151 : Blo 342753 5896151 := bstep (se 1 (by rfl) ⟨4422113, by rfl⟩ : syracuseStep 5896151 = 8844227) B8844227
theorem B653359 : Blo 342753 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B555071 : Blo 342753 555071 := bstep (se 1 (by rfl) ⟨416303, by rfl⟩ : syracuseStep 555071 = 832607) B832607
theorem B4978979 : Blo 342753 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B14089247 : Blo 342753 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B9994043 : Blo 342753 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B15138791 : Blo 342753 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B1736801 : Blo 342753 1736801 := bstep (se 2 (by rfl) ⟨651300, by rfl⟩ : syracuseStep 1736801 = 1302601) B1302601
theorem B885095 : Blo 342753 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B5604005 : Blo 342753 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B108561097 : Blo 342753 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B1737611 : Blo 342753 1737611 := bstep (se 1 (by rfl) ⟨1303208, by rfl⟩ : syracuseStep 1737611 = 2606417) B2606417
theorem B656723 : Blo 342753 656723 := bstep (se 1 (by rfl) ⟨492542, by rfl⟩ : syracuseStep 656723 = 985085) B985085
theorem B7047593 : Blo 342753 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B5607119 : Blo 342753 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1970351 : Blo 342753 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B1480189 : Blo 342753 1480189 := bstep (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) B555071
theorem B1972583 : Blo 342753 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B3742199 : Blo 342753 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B2628287 : Blo 342753 2628287 := bstep (se 1 (by rfl) ⟨1971215, by rfl⟩ : syracuseStep 2628287 = 3942431) B3942431
theorem B3545959 : Blo 342753 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B1319375 : Blo 342753 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B3319319 : Blo 342753 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B25110587 : Blo 342753 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B6662695 : Blo 342753 6662695 := bstep (se 1 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 6662695 = 9994043) B9994043
theorem B1158137 : Blo 342753 1158137 := bstep (se 2 (by rfl) ⟨434301, by rfl⟩ : syracuseStep 1158137 = 868603) B868603
theorem B1159163 : Blo 342753 1159163 := bstep (se 1 (by rfl) ⟨869372, by rfl⟩ : syracuseStep 1159163 = 1738745) B1738745
theorem B405919 : Blo 342753 405919 := bstep (se 1 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 405919 = 608879) B608879
theorem B3323045 : Blo 342753 3323045 := bstep (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) B623071
theorem B3978487 : Blo 342753 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B6042937 : Blo 342753 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B734825 : Blo 342753 734825 := bstep (se 2 (by rfl) ⟨275559, by rfl⟩ : syracuseStep 734825 = 551119) B551119
theorem B1160999 : Blo 342753 1160999 := bstep (se 1 (by rfl) ⟨870749, by rfl⟩ : syracuseStep 1160999 = 1741499) B1741499
theorem B932705 : Blo 342753 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B342911 : Blo 342753 342911 := bstep (se 1 (by rfl) ⟨257183, by rfl⟩ : syracuseStep 342911 = 514367) B514367
theorem B343007 : Blo 342753 343007 := bstep (se 1 (by rfl) ⟨257255, by rfl⟩ : syracuseStep 343007 = 514511) B514511
theorem B5979379 : Blo 342753 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B343291 : Blo 342753 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B343487 : Blo 342753 343487 := bstep (se 1 (by rfl) ⟨257615, by rfl⟩ : syracuseStep 343487 = 515231) B515231
theorem B343759 : Blo 342753 343759 := bstep (se 1 (by rfl) ⟨257819, by rfl⟩ : syracuseStep 343759 = 515639) B515639
theorem B343935 : Blo 342753 343935 := bstep (se 1 (by rfl) ⟨257951, by rfl⟩ : syracuseStep 343935 = 515903) B515903
theorem B1753001 : Blo 342753 1753001 := bstep (se 2 (by rfl) ⟨657375, by rfl⟩ : syracuseStep 1753001 = 1314751) B1314751
theorem B344231 : Blo 342753 344231 := bstep (se 1 (by rfl) ⟨258173, by rfl⟩ : syracuseStep 344231 = 516347) B516347
theorem B3916187 : Blo 342753 3916187 := bstep (se 1 (by rfl) ⟨2937140, by rfl⟩ : syracuseStep 3916187 = 5874281) B5874281
theorem B344475 : Blo 342753 344475 := bstep (se 1 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 344475 = 516713) B516713
theorem B344559 : Blo 342753 344559 := bstep (se 1 (by rfl) ⟨258419, by rfl⟩ : syracuseStep 344559 = 516839) B516839
theorem B344623 : Blo 342753 344623 := bstep (se 1 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 344623 = 516935) B516935
theorem B344831 : Blo 342753 344831 := bstep (se 1 (by rfl) ⟨258623, by rfl⟩ : syracuseStep 344831 = 517247) B517247
theorem B344895 : Blo 342753 344895 := bstep (se 1 (by rfl) ⟨258671, by rfl⟩ : syracuseStep 344895 = 517343) B517343
theorem B345179 : Blo 342753 345179 := bstep (se 1 (by rfl) ⟨258884, by rfl⟩ : syracuseStep 345179 = 517769) B517769
theorem B345215 : Blo 342753 345215 := bstep (se 1 (by rfl) ⟨258911, by rfl⟩ : syracuseStep 345215 = 517823) B517823
theorem B771209 : Blo 342753 771209 := bstep (se 2 (by rfl) ⟨289203, by rfl⟩ : syracuseStep 771209 = 578407) B578407
theorem B3818753 : Blo 342753 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B345755 : Blo 342753 345755 := bstep (se 1 (by rfl) ⟨259316, by rfl⟩ : syracuseStep 345755 = 518633) B518633
theorem B2803369 : Blo 342753 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B345807 : Blo 342753 345807 := bstep (se 1 (by rfl) ⟨259355, by rfl⟩ : syracuseStep 345807 = 518711) B518711
theorem B771839 : Blo 342753 771839 := bstep (se 1 (by rfl) ⟨578879, by rfl⟩ : syracuseStep 771839 = 1157759) B1157759
theorem B345967 : Blo 342753 345967 := bstep (se 1 (by rfl) ⟨259475, by rfl⟩ : syracuseStep 345967 = 518951) B518951
theorem B346279 : Blo 342753 346279 := bstep (se 1 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 346279 = 519419) B519419
theorem B346523 : Blo 342753 346523 := bstep (se 1 (by rfl) ⟨259892, by rfl⟩ : syracuseStep 346523 = 519785) B519785
theorem B871145 : Blo 342753 871145 := bstep (se 2 (by rfl) ⟨326679, by rfl⟩ : syracuseStep 871145 = 653359) B653359
theorem B871195 : Blo 342753 871195 := bstep (se 1 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 871195 = 1306793) B1306793
theorem B1166237 : Blo 342753 1166237 := bstep (se 3 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 1166237 = 437339) B437339
theorem B1592345 : Blo 342753 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B773225 : Blo 342753 773225 := bstep (se 2 (by rfl) ⟨289959, by rfl⟩ : syracuseStep 773225 = 579919) B579919
theorem B871631 : Blo 342753 871631 := bstep (se 1 (by rfl) ⟨653723, by rfl⟩ : syracuseStep 871631 = 1307447) B1307447
theorem B774215 : Blo 342753 774215 := bstep (se 1 (by rfl) ⟨580661, by rfl⟩ : syracuseStep 774215 = 1161323) B1161323
theorem B774377 : Blo 342753 774377 := bstep (se 2 (by rfl) ⟨290391, by rfl⟩ : syracuseStep 774377 = 580783) B580783
theorem B4412069 : Blo 342753 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B9392831 : Blo 342753 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B873899 : Blo 342753 873899 := bstep (se 1 (by rfl) ⟨655424, by rfl⟩ : syracuseStep 873899 = 1310849) B1310849
theorem B3036631 : Blo 342753 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B776969 : Blo 342753 776969 := bstep (se 2 (by rfl) ⟨291363, by rfl⟩ : syracuseStep 776969 = 582727) B582727
theorem B1301447 : Blo 342753 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B515369 : Blo 342753 515369 := bstep (se 2 (by rfl) ⟨193263, by rfl⟩ : syracuseStep 515369 = 386527) B386527
theorem B777527 : Blo 342753 777527 := bstep (se 1 (by rfl) ⟨583145, by rfl⟩ : syracuseStep 777527 = 1166291) B1166291
theorem B4480343 : Blo 342753 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B777599 : Blo 342753 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B1662599 : Blo 342753 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B515849 : Blo 342753 515849 := bstep (se 2 (by rfl) ⟨193443, by rfl⟩ : syracuseStep 515849 = 386887) B386887
theorem B515867 : Blo 342753 515867 := bstep (se 1 (by rfl) ⟨386900, by rfl⟩ : syracuseStep 515867 = 773801) B773801
theorem B876379 : Blo 342753 876379 := bstep (se 1 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 876379 = 1314569) B1314569
theorem B778121 : Blo 342753 778121 := bstep (se 2 (by rfl) ⟨291795, by rfl⟩ : syracuseStep 778121 = 583591) B583591
theorem B581627 : Blo 342753 581627 := bstep (se 1 (by rfl) ⟨436220, by rfl⟩ : syracuseStep 581627 = 872441) B872441
theorem B7463015 : Blo 342753 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B516335 : Blo 342753 516335 := bstep (se 1 (by rfl) ⟨387251, by rfl⟩ : syracuseStep 516335 = 774503) B774503
theorem B51175709 : Blo 342753 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B1106759 : Blo 342753 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B385915 : Blo 342753 385915 := bstep (se 1 (by rfl) ⟨289436, by rfl⟩ : syracuseStep 385915 = 578873) B578873
theorem B779327 : Blo 342753 779327 := bstep (se 1 (by rfl) ⟨584495, by rfl⟩ : syracuseStep 779327 = 1168991) B1168991
theorem B746747 : Blo 342753 746747 := bstep (se 1 (by rfl) ⟨560060, by rfl⟩ : syracuseStep 746747 = 1120121) B1120121
theorem B1697071 : Blo 342753 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B779867 : Blo 342753 779867 := bstep (se 1 (by rfl) ⟨584900, by rfl⟩ : syracuseStep 779867 = 1169801) B1169801
theorem B7431871 : Blo 342753 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B780155 : Blo 342753 780155 := bstep (se 1 (by rfl) ⟨585116, by rfl⟩ : syracuseStep 780155 = 1170233) B1170233
theorem B518471 : Blo 342753 518471 := bstep (se 1 (by rfl) ⟨388853, by rfl⟩ : syracuseStep 518471 = 777707) B777707
theorem B977339 : Blo 342753 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B1567225 : Blo 342753 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B387967 : Blo 342753 387967 := bstep (se 1 (by rfl) ⟨290975, by rfl⟩ : syracuseStep 387967 = 581951) B581951
theorem B1305503 : Blo 342753 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B26864759 : Blo 342753 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B388255 : Blo 342753 388255 := bstep (se 1 (by rfl) ⟨291191, by rfl⟩ : syracuseStep 388255 = 582383) B582383
theorem B519545 : Blo 342753 519545 := bstep (se 2 (by rfl) ⟨194829, by rfl⟩ : syracuseStep 519545 = 389659) B389659
theorem B519839 : Blo 342753 519839 := bstep (se 1 (by rfl) ⟨389879, by rfl⟩ : syracuseStep 519839 = 779759) B779759
theorem B1306307 : Blo 342753 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B6647933 : Blo 342753 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B980687 : Blo 342753 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B2947529 : Blo 342753 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B51706507 : Blo 342753 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B3930767 : Blo 342753 3930767 := bstep (se 1 (by rfl) ⟨2948075, by rfl⟩ : syracuseStep 3930767 = 5896151) B5896151
theorem B10092527 : Blo 342753 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B590063 : Blo 342753 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B2262761 : Blo 342753 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B14944013 : Blo 342753 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B3737825 : Blo 342753 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B3738079 : Blo 342753 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B1313567 : Blo 342753 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B6261887 : Blo 342753 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B8883593 : Blo 342753 8883593 := bstep (se 2 (by rfl) ⟨3331347, by rfl⟩ : syracuseStep 8883593 = 6662695) B6662695
theorem B1315055 : Blo 342753 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B2494799 : Blo 342753 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B2986895 : Blo 342753 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B34117139 : Blo 342753 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B497831 : Blo 342753 497831 := bstep (se 1 (by rfl) ⟨373373, by rfl⟩ : syracuseStep 497831 = 746747) B746747
theorem B1973585 : Blo 342753 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B4431955 : Blo 342753 4431955 := bstep (se 1 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 4431955 = 6647933) B6647933
theorem B4727945 : Blo 342753 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B7972505 : Blo 342753 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B6728351 : Blo 342753 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B1157867 : Blo 342753 1157867 := bstep (se 1 (by rfl) ⟨868400, by rfl⟩ : syracuseStep 1157867 = 1736801) B1736801
theorem B1158407 : Blo 342753 1158407 := bstep (se 1 (by rfl) ⟨868805, by rfl⟩ : syracuseStep 1158407 = 1737611) B1737611
theorem B437815 : Blo 342753 437815 := bstep (se 1 (by rfl) ⟨328361, by rfl⟩ : syracuseStep 437815 = 656723) B656723
theorem B144748129 : Blo 342753 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B3518333 : Blo 342753 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B4698395 : Blo 342753 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B9909161 : Blo 342753 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B1161593 : Blo 342753 1161593 := bstep (se 2 (by rfl) ⟨435597, by rfl⟩ : syracuseStep 1161593 = 871195) B871195
theorem B1752191 : Blo 342753 1752191 := bstep (se 1 (by rfl) ⟨1314143, by rfl⟩ : syracuseStep 1752191 = 2628287) B2628287
theorem B867631 : Blo 342753 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B343579 : Blo 342753 343579 := bstep (se 1 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 343579 = 515369) B515369
theorem B343899 : Blo 342753 343899 := bstep (se 1 (by rfl) ⟨257924, by rfl⟩ : syracuseStep 343899 = 515849) B515849
theorem B343911 : Blo 342753 343911 := bstep (se 1 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 343911 = 515867) B515867
theorem B66961565 : Blo 342753 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B344223 : Blo 342753 344223 := bstep (se 1 (by rfl) ⟨258167, by rfl⟩ : syracuseStep 344223 = 516335) B516335
theorem B541225 : Blo 342753 541225 := bstep (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) B405919
theorem B737839 : Blo 342753 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B2212879 : Blo 342753 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B345647 : Blo 342753 345647 := bstep (se 1 (by rfl) ⟨259235, by rfl⟩ : syracuseStep 345647 = 518471) B518471
theorem B870335 : Blo 342753 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B4048841 : Blo 342753 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B772091 : Blo 342753 772091 := bstep (se 1 (by rfl) ⟨579068, by rfl⟩ : syracuseStep 772091 = 1158137) B1158137
theorem B17909839 : Blo 342753 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B346363 : Blo 342753 346363 := bstep (se 1 (by rfl) ⟨259772, by rfl⟩ : syracuseStep 346363 = 519545) B519545
theorem B346559 : Blo 342753 346559 := bstep (se 1 (by rfl) ⟨259919, by rfl⟩ : syracuseStep 346559 = 519839) B519839
theorem B870871 : Blo 342753 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B772775 : Blo 342753 772775 := bstep (se 1 (by rfl) ⟨579581, by rfl⟩ : syracuseStep 772775 = 1159163) B1159163
theorem B4246253 : Blo 342753 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B2215363 : Blo 342753 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B773999 : Blo 342753 773999 := bstep (se 1 (by rfl) ⟨580499, by rfl⟩ : syracuseStep 773999 = 1160999) B1160999
theorem B1168505 : Blo 342753 1168505 := bstep (se 2 (by rfl) ⟨438189, by rfl⟩ : syracuseStep 1168505 = 876379) B876379
theorem B1168667 : Blo 342753 1168667 := bstep (se 1 (by rfl) ⟨876500, by rfl⟩ : syracuseStep 1168667 = 1753001) B1753001
theorem B2610791 : Blo 342753 2610791 := bstep (se 1 (by rfl) ⟨1958093, by rfl⟩ : syracuseStep 2610791 = 3916187) B3916187
theorem B514139 : Blo 342753 514139 := bstep (se 1 (by rfl) ⟨385604, by rfl⟩ : syracuseStep 514139 = 771209) B771209
theorem B2545835 : Blo 342753 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B514553 : Blo 342753 514553 := bstep (se 2 (by rfl) ⟨192957, by rfl⟩ : syracuseStep 514553 = 385915) B385915
theorem B514559 : Blo 342753 514559 := bstep (se 1 (by rfl) ⟨385919, by rfl⟩ : syracuseStep 514559 = 771839) B771839
theorem B580763 : Blo 342753 580763 := bstep (se 1 (by rfl) ⟨435572, by rfl⟩ : syracuseStep 580763 = 871145) B871145
theorem B777491 : Blo 342753 777491 := bstep (se 1 (by rfl) ⟨583118, by rfl⟩ : syracuseStep 777491 = 1166237) B1166237
theorem B515483 : Blo 342753 515483 := bstep (se 1 (by rfl) ⟨386612, by rfl⟩ : syracuseStep 515483 = 773225) B773225
theorem B581087 : Blo 342753 581087 := bstep (se 1 (by rfl) ⟨435815, by rfl⟩ : syracuseStep 581087 = 871631) B871631
theorem B516143 : Blo 342753 516143 := bstep (se 1 (by rfl) ⟨387107, by rfl⟩ : syracuseStep 516143 = 774215) B774215
theorem B516251 : Blo 342753 516251 := bstep (se 1 (by rfl) ⟨387188, by rfl⟩ : syracuseStep 516251 = 774377) B774377
theorem B2941379 : Blo 342753 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B2089633 : Blo 342753 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B582599 : Blo 342753 582599 := bstep (se 1 (by rfl) ⟨436949, by rfl⟩ : syracuseStep 582599 = 873899) B873899
theorem B517289 : Blo 342753 517289 := bstep (se 2 (by rfl) ⟨193983, by rfl⟩ : syracuseStep 517289 = 387967) B387967
theorem B517673 : Blo 342753 517673 := bstep (se 2 (by rfl) ⟨194127, by rfl⟩ : syracuseStep 517673 = 388255) B388255
theorem B517979 : Blo 342753 517979 := bstep (se 1 (by rfl) ⟨388484, by rfl⟩ : syracuseStep 517979 = 776969) B776969
theorem B2615165 : Blo 342753 2615165 := bstep (se 3 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 2615165 = 980687) B980687
theorem B518351 : Blo 342753 518351 := bstep (se 1 (by rfl) ⟨388763, by rfl⟩ : syracuseStep 518351 = 777527) B777527
theorem B518399 : Blo 342753 518399 := bstep (se 1 (by rfl) ⟨388799, by rfl⟩ : syracuseStep 518399 = 777599) B777599
theorem B1108399 : Blo 342753 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B518747 : Blo 342753 518747 := bstep (se 1 (by rfl) ⟨389060, by rfl⟩ : syracuseStep 518747 = 778121) B778121
theorem B387751 : Blo 342753 387751 := bstep (se 1 (by rfl) ⟨290813, by rfl⟩ : syracuseStep 387751 = 581627) B581627
theorem B4975343 : Blo 342753 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B519551 : Blo 342753 519551 := bstep (se 1 (by rfl) ⟨389663, by rfl⟩ : syracuseStep 519551 = 779327) B779327
theorem B519911 : Blo 342753 519911 := bstep (se 1 (by rfl) ⟨389933, by rfl⟩ : syracuseStep 519911 = 779867) B779867
theorem B520103 : Blo 342753 520103 := bstep (se 1 (by rfl) ⟨390077, by rfl⟩ : syracuseStep 520103 = 780155) B780155
theorem B651559 : Blo 342753 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B5304649 : Blo 342753 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B8057249 : Blo 342753 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B68942009 : Blo 342753 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B489883 : Blo 342753 489883 := bstep (se 1 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 489883 = 734825) B734825
theorem B1965019 : Blo 342753 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B2620511 : Blo 342753 2620511 := bstep (se 1 (by rfl) ⟨1965383, by rfl⟩ : syracuseStep 2620511 = 3930767) B3930767
theorem B621803 : Blo 342753 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B1573501 : Blo 342753 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B2786177 : Blo 342753 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B1508507 : Blo 342753 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B9962675 : Blo 342753 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B2950505 : Blo 342753 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B2491883 : Blo 342753 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B5310197 : Blo 342753 5310197 := bstep (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) B497831
theorem B7965053 : Blo 342753 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B2886533 : Blo 342753 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B3935141 : Blo 342753 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B1477865 : Blo 342753 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B4984105 : Blo 342753 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B22744759 : Blo 342753 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B1740527 : Blo 342753 1740527 := bstep (se 1 (by rfl) ⟨1305395, by rfl⟩ : syracuseStep 1740527 = 2610791) B2610791
theorem B2953817 : Blo 342753 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B1315723 : Blo 342753 1315723 := bstep (se 1 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 1315723 = 1973585) B1973585
theorem B6788893 : Blo 342753 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B3151963 : Blo 342753 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B5315003 : Blo 342753 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B1743443 : Blo 342753 1743443 := bstep (se 1 (by rfl) ⟨1307582, by rfl⟩ : syracuseStep 1743443 = 2615165) B2615165
theorem B3316895 : Blo 342753 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B1156841 : Blo 342753 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B1747007 : Blo 342753 1747007 := bstep (se 1 (by rfl) ⟨1310255, by rfl⟩ : syracuseStep 1747007 = 2620511) B2620511
theorem B44641043 : Blo 342753 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B5909273 : Blo 342753 5909273 := bstep (se 2 (by rfl) ⟨2215977, by rfl⟩ : syracuseStep 5909273 = 4431955) B4431955
theorem B2699227 : Blo 342753 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2830835 : Blo 342753 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B4174591 : Blo 342753 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1161161 : Blo 342753 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B342759 : Blo 342753 342759 := bstep (se 1 (by rfl) ⟨257069, by rfl⟩ : syracuseStep 342759 = 514139) B514139
theorem B343035 : Blo 342753 343035 := bstep (se 1 (by rfl) ⟨257276, by rfl⟩ : syracuseStep 343035 = 514553) B514553
theorem B343039 : Blo 342753 343039 := bstep (se 1 (by rfl) ⟨257279, by rfl⟩ : syracuseStep 343039 = 514559) B514559
theorem B343655 : Blo 342753 343655 := bstep (se 1 (by rfl) ⟨257741, by rfl⟩ : syracuseStep 343655 = 515483) B515483
theorem B344095 : Blo 342753 344095 := bstep (se 1 (by rfl) ⟨258071, by rfl⟩ : syracuseStep 344095 = 516143) B516143
theorem B344167 : Blo 342753 344167 := bstep (se 1 (by rfl) ⟨258125, by rfl⟩ : syracuseStep 344167 = 516251) B516251
theorem B868745 : Blo 342753 868745 := bstep (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) B651559
theorem B344859 : Blo 342753 344859 := bstep (se 1 (by rfl) ⟨258644, by rfl⟩ : syracuseStep 344859 = 517289) B517289
theorem B345115 : Blo 342753 345115 := bstep (se 1 (by rfl) ⟨258836, by rfl⟩ : syracuseStep 345115 = 517673) B517673
theorem B345319 : Blo 342753 345319 := bstep (se 1 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 345319 = 517979) B517979
theorem B345567 : Blo 342753 345567 := bstep (se 1 (by rfl) ⟨259175, by rfl⟩ : syracuseStep 345567 = 518351) B518351
theorem B345599 : Blo 342753 345599 := bstep (se 1 (by rfl) ⟨259199, by rfl⟩ : syracuseStep 345599 = 518399) B518399
theorem B345831 : Blo 342753 345831 := bstep (se 1 (by rfl) ⟨259373, by rfl⟩ : syracuseStep 345831 = 518747) B518747
theorem B17942269 : Blo 342753 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B771911 : Blo 342753 771911 := bstep (se 1 (by rfl) ⟨578933, by rfl⟩ : syracuseStep 771911 = 1157867) B1157867
theorem B772271 : Blo 342753 772271 := bstep (se 1 (by rfl) ⟨579203, by rfl⟩ : syracuseStep 772271 = 1158407) B1158407
theorem B346367 : Blo 342753 346367 := bstep (se 1 (by rfl) ⟨259775, by rfl⟩ : syracuseStep 346367 = 519551) B519551
theorem B346607 : Blo 342753 346607 := bstep (se 1 (by rfl) ⟨259955, by rfl⟩ : syracuseStep 346607 = 519911) B519911
theorem B2345555 : Blo 342753 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B346735 : Blo 342753 346735 := bstep (se 1 (by rfl) ⟨260051, by rfl⟩ : syracuseStep 346735 = 520103) B520103
theorem B3132263 : Blo 342753 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B6606107 : Blo 342753 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B1658141 : Blo 342753 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B45961339 : Blo 342753 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B774395 : Blo 342753 774395 := bstep (se 1 (by rfl) ⟨580796, by rfl⟩ : syracuseStep 774395 = 1161593) B1161593
theorem B1168127 : Blo 342753 1168127 := bstep (se 1 (by rfl) ⟨876095, by rfl⟩ : syracuseStep 1168127 = 1752191) B1752191
theorem B580223 : Blo 342753 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B514727 : Blo 342753 514727 := bstep (se 1 (by rfl) ⟨386045, by rfl⟩ : syracuseStep 514727 = 772091) B772091
theorem B515183 : Blo 342753 515183 := bstep (se 1 (by rfl) ⟨386387, by rfl⟩ : syracuseStep 515183 = 772775) B772775
theorem B875711 : Blo 342753 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B5922395 : Blo 342753 5922395 := bstep (se 1 (by rfl) ⟨4441796, by rfl⟩ : syracuseStep 5922395 = 8883593) B8883593
theorem B515999 : Blo 342753 515999 := bstep (se 1 (by rfl) ⟨386999, by rfl⟩ : syracuseStep 515999 = 773999) B773999
theorem B23879785 : Blo 342753 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B876703 : Blo 342753 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B1663199 : Blo 342753 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B779003 : Blo 342753 779003 := bstep (se 1 (by rfl) ⟨584252, by rfl⟩ : syracuseStep 779003 = 1168505) B1168505
theorem B779111 : Blo 342753 779111 := bstep (se 1 (by rfl) ⟨584333, by rfl⟩ : syracuseStep 779111 = 1168667) B1168667
theorem B517001 : Blo 342753 517001 := bstep (se 2 (by rfl) ⟨193875, by rfl⟩ : syracuseStep 517001 = 387751) B387751
theorem B583753 : Blo 342753 583753 := bstep (se 2 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 583753 = 437815) B437815
theorem B387175 : Blo 342753 387175 := bstep (se 1 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 387175 = 580763) B580763
theorem B192997505 : Blo 342753 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B518327 : Blo 342753 518327 := bstep (se 1 (by rfl) ⟨388745, by rfl⟩ : syracuseStep 518327 = 777491) B777491
theorem B387391 : Blo 342753 387391 := bstep (se 1 (by rfl) ⟨290543, by rfl⟩ : syracuseStep 387391 = 581087) B581087
theorem B1960919 : Blo 342753 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B7072865 : Blo 342753 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B388399 : Blo 342753 388399 := bstep (se 1 (by rfl) ⟨291299, by rfl⟩ : syracuseStep 388399 = 582599) B582599
theorem B5371499 : Blo 342753 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B653177 : Blo 342753 653177 := bstep (se 2 (by rfl) ⟨244941, by rfl⟩ : syracuseStep 653177 = 489883) B489883
theorem B2620025 : Blo 342753 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B2098001 : Blo 342753 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B1967003 : Blo 342753 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B3540131 : Blo 342753 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B5310035 : Blo 342753 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B2623427 : Blo 342753 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B23923025 : Blo 342753 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B1969211 : Blo 342753 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B3543335 : Blo 342753 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B61281785 : Blo 342753 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B514660013 : Blo 342753 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B29760695 : Blo 342753 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B3939515 : Blo 342753 3939515 := bstep (se 1 (by rfl) ⟨2954636, by rfl⟩ : syracuseStep 3939515 = 5909273) B5909273
theorem B9051857 : Blo 342753 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B4202617 : Blo 342753 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B3940973 : Blo 342753 3940973 := bstep (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) B1477865
theorem B3580999 : Blo 342753 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B435451 : Blo 342753 435451 := bstep (se 1 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 435451 = 653177) B653177
theorem B1746683 : Blo 342753 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B14395877 : Blo 342753 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B7548893 : Blo 342753 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B4404071 : Blo 342753 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B1160351 : Blo 342753 1160351 := bstep (se 1 (by rfl) ⟨870263, by rfl⟩ : syracuseStep 1160351 = 1740527) B1740527
theorem B1162295 : Blo 342753 1162295 := bstep (se 1 (by rfl) ⟨871721, by rfl⟩ : syracuseStep 1162295 = 1743443) B1743443
theorem B343151 : Blo 342753 343151 := bstep (se 1 (by rfl) ⟨257363, by rfl⟩ : syracuseStep 343151 = 514727) B514727
theorem B343455 : Blo 342753 343455 := bstep (se 1 (by rfl) ⟨257591, by rfl⟩ : syracuseStep 343455 = 515183) B515183
theorem B2211263 : Blo 342753 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B30326345 : Blo 342753 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B3948263 : Blo 342753 3948263 := bstep (se 1 (by rfl) ⟨2961197, by rfl⟩ : syracuseStep 3948263 = 5922395) B5922395
theorem B343999 : Blo 342753 343999 := bstep (se 1 (by rfl) ⟨257999, by rfl⟩ : syracuseStep 343999 = 515999) B515999
theorem B344667 : Blo 342753 344667 := bstep (se 1 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 344667 = 517001) B517001
theorem B771227 : Blo 342753 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B1754297 : Blo 342753 1754297 := bstep (se 2 (by rfl) ⟨657861, by rfl⟩ : syracuseStep 1754297 = 1315723) B1315723
theorem B1164671 : Blo 342753 1164671 := bstep (se 1 (by rfl) ⟨873503, by rfl⟩ : syracuseStep 1164671 = 1747007) B1747007
theorem B345551 : Blo 342753 345551 := bstep (se 1 (by rfl) ⟨259163, by rfl⟩ : syracuseStep 345551 = 518327) B518327
theorem B774107 : Blo 342753 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B31839713 : Blo 342753 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B1168937 : Blo 342753 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B579163 : Blo 342753 579163 := bstep (se 1 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 579163 = 868745) B868745
theorem B1857451 : Blo 342753 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B1005671 : Blo 342753 1005671 := bstep (se 1 (by rfl) ⟨754253, by rfl⟩ : syracuseStep 1005671 = 1508507) B1508507
theorem B6641783 : Blo 342753 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B1661255 : Blo 342753 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B514607 : Blo 342753 514607 := bstep (se 1 (by rfl) ⟨385955, by rfl⟩ : syracuseStep 514607 = 771911) B771911
theorem B514847 : Blo 342753 514847 := bstep (se 1 (by rfl) ⟨386135, by rfl⟩ : syracuseStep 514847 = 772271) B772271
theorem B2088175 : Blo 342753 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B1924355 : Blo 342753 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1105427 : Blo 342753 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B778337 : Blo 342753 778337 := bstep (se 2 (by rfl) ⟨291876, by rfl⟩ : syracuseStep 778337 = 583753) B583753
theorem B516233 : Blo 342753 516233 := bstep (se 2 (by rfl) ⟨193587, by rfl⟩ : syracuseStep 516233 = 387175) B387175
theorem B516263 : Blo 342753 516263 := bstep (se 1 (by rfl) ⟨387197, by rfl⟩ : syracuseStep 516263 = 774395) B774395
theorem B516521 : Blo 342753 516521 := bstep (se 2 (by rfl) ⟨193695, by rfl⟩ : syracuseStep 516521 = 387391) B387391
theorem B778751 : Blo 342753 778751 := bstep (se 1 (by rfl) ⟨584063, by rfl⟩ : syracuseStep 778751 = 1168127) B1168127
theorem B6645473 : Blo 342753 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B517865 : Blo 342753 517865 := bstep (se 2 (by rfl) ⟨194199, by rfl⟩ : syracuseStep 517865 = 388399) B388399
theorem B386815 : Blo 342753 386815 := bstep (se 1 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 386815 = 580223) B580223
theorem B583807 : Blo 342753 583807 := bstep (se 1 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 583807 = 875711) B875711
theorem B1108799 : Blo 342753 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B519335 : Blo 342753 519335 := bstep (se 1 (by rfl) ⟨389501, by rfl⟩ : syracuseStep 519335 = 779003) B779003
theorem B519407 : Blo 342753 519407 := bstep (se 1 (by rfl) ⟨389555, by rfl⟩ : syracuseStep 519407 = 779111) B779111
theorem B5566121 : Blo 342753 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B6254813 : Blo 342753 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B1307279 : Blo 342753 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B4715243 : Blo 342753 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B5603489 : Blo 342753 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B1311335 : Blo 342753 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B2360087 : Blo 342753 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B3540023 : Blo 342753 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1312807 : Blo 342753 1312807 := bstep (se 1 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 1312807 = 1969211) B1969211
theorem B2362223 : Blo 342753 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B163418093 : Blo 342753 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B4427855 : Blo 342753 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B2626343 : Blo 342753 2626343 := bstep (se 1 (by rfl) ⟨1969757, by rfl⟩ : syracuseStep 2626343 = 3939515) B3939515
theorem B6034571 : Blo 342753 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B2627315 : Blo 342753 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B4430315 : Blo 342753 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B3710747 : Blo 342753 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B4169875 : Blo 342753 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B2632175 : Blo 342753 2632175 := bstep (se 1 (by rfl) ⟨1974131, by rfl⟩ : syracuseStep 2632175 = 3948263) B3948263
theorem B1748951 : Blo 342753 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B670447 : Blo 342753 670447 := bstep (se 1 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 670447 = 1005671) B1005671
theorem B343071 : Blo 342753 343071 := bstep (se 1 (by rfl) ⟨257303, by rfl⟩ : syracuseStep 343071 = 514607) B514607
theorem B343231 : Blo 342753 343231 := bstep (se 1 (by rfl) ⟨257423, by rfl⟩ : syracuseStep 343231 = 514847) B514847
theorem B19840463 : Blo 342753 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B736951 : Blo 342753 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B344155 : Blo 342753 344155 := bstep (se 1 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 344155 = 516233) B516233
theorem B344175 : Blo 342753 344175 := bstep (se 1 (by rfl) ⟨258131, by rfl⟩ : syracuseStep 344175 = 516263) B516263
theorem B344347 : Blo 342753 344347 := bstep (se 1 (by rfl) ⟨258260, by rfl⟩ : syracuseStep 344347 = 516521) B516521
theorem B345243 : Blo 342753 345243 := bstep (se 1 (by rfl) ⟨258932, by rfl⟩ : syracuseStep 345243 = 517865) B517865
theorem B1164455 : Blo 342753 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B739199 : Blo 342753 739199 := bstep (se 1 (by rfl) ⟨554399, by rfl⟩ : syracuseStep 739199 = 1108799) B1108799
theorem B346223 : Blo 342753 346223 := bstep (se 1 (by rfl) ⟨259667, by rfl⟩ : syracuseStep 346223 = 519335) B519335
theorem B772217 : Blo 342753 772217 := bstep (se 2 (by rfl) ⟨289581, by rfl⟩ : syracuseStep 772217 = 579163) B579163
theorem B346271 : Blo 342753 346271 := bstep (se 1 (by rfl) ⟨259703, by rfl⟩ : syracuseStep 346271 = 519407) B519407
theorem B2476601 : Blo 342753 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B5032595 : Blo 342753 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B871519 : Blo 342753 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B2936047 : Blo 342753 2936047 := bstep (se 1 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 2936047 = 4404071) B4404071
theorem B5131613 : Blo 342753 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B773567 : Blo 342753 773567 := bstep (se 1 (by rfl) ⟨580175, by rfl⟩ : syracuseStep 773567 = 1160351) B1160351
theorem B774863 : Blo 342753 774863 := bstep (se 1 (by rfl) ⟨581147, by rfl⟩ : syracuseStep 774863 = 1162295) B1162295
theorem B1398667 : Blo 342753 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B514151 : Blo 342753 514151 := bstep (se 1 (by rfl) ⟨385613, by rfl⟩ : syracuseStep 514151 = 771227) B771227
theorem B1169531 : Blo 342753 1169531 := bstep (se 1 (by rfl) ⟨877148, by rfl⟩ : syracuseStep 1169531 = 1754297) B1754297
theorem B776447 : Blo 342753 776447 := bstep (se 1 (by rfl) ⟨582335, by rfl⟩ : syracuseStep 776447 = 1164671) B1164671
theorem B15948683 : Blo 342753 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B580601 : Blo 342753 580601 := bstep (se 2 (by rfl) ⟨217725, by rfl⟩ : syracuseStep 580601 = 435451) B435451
theorem B515753 : Blo 342753 515753 := bstep (se 2 (by rfl) ⟨193407, by rfl⟩ : syracuseStep 515753 = 386815) B386815
theorem B516071 : Blo 342753 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B778409 : Blo 342753 778409 := bstep (se 2 (by rfl) ⟨291903, by rfl⟩ : syracuseStep 778409 = 583807) B583807
theorem B21226475 : Blo 342753 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B779291 : Blo 342753 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B343106675 : Blo 342753 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B1107503 : Blo 342753 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B518891 : Blo 342753 518891 := bstep (se 1 (by rfl) ⟨389168, by rfl⟩ : syracuseStep 518891 = 778337) B778337
theorem B519167 : Blo 342753 519167 := bstep (se 1 (by rfl) ⟨389375, by rfl⟩ : syracuseStep 519167 = 778751) B778751
theorem B19098661 : Blo 342753 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B9597251 : Blo 342753 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B3143495 : Blo 342753 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B2784233 : Blo 342753 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B1474175 : Blo 342753 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B20217563 : Blo 342753 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B3735659 : Blo 342753 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B1573391 : Blo 342753 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B2360015 : Blo 342753 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B25592669 : Blo 342753 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B492799 : Blo 342753 492799 := bstep (se 1 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 492799 = 739199) B739199
theorem B1574815 : Blo 342753 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B2951903 : Blo 342753 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B25464881 : Blo 342753 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B2953543 : Blo 342753 2953543 := bstep (se 1 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 2953543 = 4430315) B4430315
theorem B893929 : Blo 342753 893929 := bstep (se 2 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 893929 = 670447) B670447
theorem B13478375 : Blo 342753 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B1651067 : Blo 342753 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B3355063 : Blo 342753 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B56603933 : Blo 342753 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B1750409 : Blo 342753 1750409 := bstep (se 2 (by rfl) ⟨656403, by rfl⟩ : syracuseStep 1750409 = 1312807) B1312807
theorem B1750895 : Blo 342753 1750895 := bstep (se 1 (by rfl) ⟨1313171, by rfl⟩ : syracuseStep 1750895 = 2626343) B2626343
theorem B1751543 : Blo 342753 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B342767 : Blo 342753 342767 := bstep (se 1 (by rfl) ⟨257075, by rfl⟩ : syracuseStep 342767 = 514151) B514151
theorem B1162025 : Blo 342753 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B3914729 : Blo 342753 3914729 := bstep (se 2 (by rfl) ⟨1468023, by rfl⟩ : syracuseStep 3914729 = 2936047) B2936047
theorem B10632455 : Blo 342753 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B343835 : Blo 342753 343835 := bstep (se 1 (by rfl) ⟨257876, by rfl⟩ : syracuseStep 343835 = 515753) B515753
theorem B2473831 : Blo 342753 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B344047 : Blo 342753 344047 := bstep (se 1 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 344047 = 516071) B516071
theorem B228737783 : Blo 342753 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B738335 : Blo 342753 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B1754783 : Blo 342753 1754783 := bstep (se 1 (by rfl) ⟨1316087, by rfl⟩ : syracuseStep 1754783 = 2632175) B2632175
theorem B345927 : Blo 342753 345927 := bstep (se 1 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 345927 = 518891) B518891
theorem B346111 : Blo 342753 346111 := bstep (se 1 (by rfl) ⟨259583, by rfl⟩ : syracuseStep 346111 = 519167) B519167
theorem B1165967 : Blo 342753 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B13684301 : Blo 342753 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B1856155 : Blo 342753 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B13226975 : Blo 342753 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B5559833 : Blo 342753 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B874223 : Blo 342753 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B776303 : Blo 342753 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B514811 : Blo 342753 514811 := bstep (se 1 (by rfl) ⟨386108, by rfl⟩ : syracuseStep 514811 = 772217) B772217
theorem B515711 : Blo 342753 515711 := bstep (se 1 (by rfl) ⟨386783, by rfl⟩ : syracuseStep 515711 = 773567) B773567
theorem B108945395 : Blo 342753 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B516575 : Blo 342753 516575 := bstep (se 1 (by rfl) ⟨387431, by rfl⟩ : syracuseStep 516575 = 774863) B774863
theorem B4023047 : Blo 342753 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B779687 : Blo 342753 779687 := bstep (se 1 (by rfl) ⟨584765, by rfl⟩ : syracuseStep 779687 = 1169531) B1169531
theorem B517631 : Blo 342753 517631 := bstep (se 1 (by rfl) ⟨388223, by rfl⟩ : syracuseStep 517631 = 776447) B776447
theorem B387067 : Blo 342753 387067 := bstep (se 1 (by rfl) ⟨290300, by rfl⟩ : syracuseStep 387067 = 580601) B580601
theorem B8382653 : Blo 342753 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B518939 : Blo 342753 518939 := bstep (se 1 (by rfl) ⟨389204, by rfl⟩ : syracuseStep 518939 = 778409) B778409
theorem B519527 : Blo 342753 519527 := bstep (se 1 (by rfl) ⟨389645, by rfl⟩ : syracuseStep 519527 = 779291) B779291
theorem B1864889 : Blo 342753 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B982601 : Blo 342753 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B982783 : Blo 342753 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B2490439 : Blo 342753 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B1573343 : Blo 342753 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B4195709 : Blo 342753 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B657065 : Blo 342753 657065 := bstep (se 2 (by rfl) ⟨246399, by rfl⟩ : syracuseStep 657065 = 492799) B492799
theorem B1967935 : Blo 342753 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B17893669 : Blo 342753 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B2099753 : Blo 342753 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B16976587 : Blo 342753 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B1968893 : Blo 342753 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B8817983 : Blo 342753 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B3706555 : Blo 342753 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B3938057 : Blo 342753 3938057 := bstep (se 2 (by rfl) ⟨1476771, by rfl⟩ : syracuseStep 3938057 = 2953543) B2953543
theorem B8985583 : Blo 342753 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B7088303 : Blo 342753 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B1191905 : Blo 342753 1191905 := bstep (se 2 (by rfl) ⟨446964, by rfl⟩ : syracuseStep 1191905 = 893929) B893929
theorem B10728125 : Blo 342753 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B9122867 : Blo 342753 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B343207 : Blo 342753 343207 := bstep (se 1 (by rfl) ⟨257405, by rfl⟩ : syracuseStep 343207 = 514811) B514811
theorem B343807 : Blo 342753 343807 := bstep (se 1 (by rfl) ⟨257855, by rfl⟩ : syracuseStep 343807 = 515711) B515711
theorem B72630263 : Blo 342753 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B344383 : Blo 342753 344383 := bstep (se 1 (by rfl) ⟨258287, by rfl⟩ : syracuseStep 344383 = 516575) B516575
theorem B2474873 : Blo 342753 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B345087 : Blo 342753 345087 := bstep (se 1 (by rfl) ⟨258815, by rfl⟩ : syracuseStep 345087 = 517631) B517631
theorem B5588435 : Blo 342753 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B345959 : Blo 342753 345959 := bstep (se 1 (by rfl) ⟨259469, by rfl⟩ : syracuseStep 345959 = 518939) B518939
theorem B346351 : Blo 342753 346351 := bstep (se 1 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 346351 = 519527) B519527
theorem B1100711 : Blo 342753 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B37735955 : Blo 342753 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B1166939 : Blo 342753 1166939 := bstep (se 1 (by rfl) ⟨875204, by rfl⟩ : syracuseStep 1166939 = 1750409) B1750409
theorem B1167263 : Blo 342753 1167263 := bstep (se 1 (by rfl) ⟨875447, by rfl⟩ : syracuseStep 1167263 = 1750895) B1750895
theorem B1167695 : Blo 342753 1167695 := bstep (se 1 (by rfl) ⟨875771, by rfl⟩ : syracuseStep 1167695 = 1751543) B1751543
theorem B774683 : Blo 342753 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B2609819 : Blo 342753 2609819 := bstep (se 1 (by rfl) ⟨1957364, by rfl⟩ : syracuseStep 2609819 = 3914729) B3914729
theorem B3298441 : Blo 342753 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B152491855 : Blo 342753 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B17061779 : Blo 342753 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B1169855 : Blo 342753 1169855 := bstep (se 1 (by rfl) ⟨877391, by rfl⟩ : syracuseStep 1169855 = 1754783) B1754783
theorem B777311 : Blo 342753 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B516089 : Blo 342753 516089 := bstep (se 2 (by rfl) ⟨193533, by rfl⟩ : syracuseStep 516089 = 387067) B387067
theorem B582815 : Blo 342753 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B517535 : Blo 342753 517535 := bstep (se 1 (by rfl) ⟨388151, by rfl⟩ : syracuseStep 517535 = 776303) B776303
theorem B519791 : Blo 342753 519791 := bstep (se 1 (by rfl) ⟨389843, by rfl⟩ : syracuseStep 519791 = 779687) B779687
theorem B1243259 : Blo 342753 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B1310377 : Blo 342753 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B655067 : Blo 342753 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B1048895 : Blo 342753 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B1312595 : Blo 342753 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B2623913 : Blo 342753 2623913 := bstep (se 2 (by rfl) ⟨983967, by rfl⟩ : syracuseStep 2623913 = 1967935) B1967935
theorem B23858225 : Blo 342753 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B1739879 : Blo 342753 1739879 := bstep (se 1 (by rfl) ⟨1304909, by rfl⟩ : syracuseStep 1739879 = 2609819) B2609819
theorem B2625371 : Blo 342753 2625371 := bstep (se 1 (by rfl) ⟨1969028, by rfl⟩ : syracuseStep 2625371 = 3938057) B3938057
theorem B11374519 : Blo 342753 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B4725535 : Blo 342753 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B4397921 : Blo 342753 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B794603 : Blo 342753 794603 := bstep (se 1 (by rfl) ⟨595952, by rfl⟩ : syracuseStep 794603 = 1191905) B1191905
theorem B7152083 : Blo 342753 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B828839 : Blo 342753 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B1746845 : Blo 342753 1746845 := bstep (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) B655067
theorem B1747169 : Blo 342753 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B3320585 : Blo 342753 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B1649915 : Blo 342753 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B2797139 : Blo 342753 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B438043 : Blo 342753 438043 := bstep (se 1 (by rfl) ⟨328532, by rfl⟩ : syracuseStep 438043 = 657065) B657065
theorem B733807 : Blo 342753 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B5878655 : Blo 342753 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B47923109 : Blo 342753 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B344059 : Blo 342753 344059 := bstep (se 1 (by rfl) ⟨258044, by rfl⟩ : syracuseStep 344059 = 516089) B516089
theorem B345023 : Blo 342753 345023 := bstep (se 1 (by rfl) ⟨258767, by rfl⟩ : syracuseStep 345023 = 517535) B517535
theorem B346527 : Blo 342753 346527 := bstep (se 1 (by rfl) ⟨259895, by rfl⟩ : syracuseStep 346527 = 519791) B519791
theorem B6081911 : Blo 342753 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B48420175 : Blo 342753 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B3725623 : Blo 342753 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B1399835 : Blo 342753 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B25157303 : Blo 342753 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B777959 : Blo 342753 777959 := bstep (se 1 (by rfl) ⟨583469, by rfl⟩ : syracuseStep 777959 = 1166939) B1166939
theorem B778175 : Blo 342753 778175 := bstep (se 1 (by rfl) ⟨583631, by rfl⟩ : syracuseStep 778175 = 1167263) B1167263
theorem B778463 : Blo 342753 778463 := bstep (se 1 (by rfl) ⟨583847, by rfl⟩ : syracuseStep 778463 = 1167695) B1167695
theorem B516455 : Blo 342753 516455 := bstep (se 1 (by rfl) ⟨387341, by rfl⟩ : syracuseStep 516455 = 774683) B774683
theorem B22635449 : Blo 342753 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B779903 : Blo 342753 779903 := bstep (se 1 (by rfl) ⟨584927, by rfl⟩ : syracuseStep 779903 = 1169855) B1169855
theorem B518207 : Blo 342753 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B4942073 : Blo 342753 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B388543 : Blo 342753 388543 := bstep (se 1 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 388543 = 582815) B582815
theorem B203322473 : Blo 342753 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B529735 : Blo 342753 529735 := bstep (se 1 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 529735 = 794603) B794603
theorem B64560233 : Blo 342753 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B6300713 : Blo 342753 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B699263 : Blo 342753 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B1749275 : Blo 342753 1749275 := bstep (se 1 (by rfl) ⟨1311956, by rfl⟩ : syracuseStep 1749275 = 2623913) B2623913
theorem B15905483 : Blo 342753 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B1159919 : Blo 342753 1159919 := bstep (se 1 (by rfl) ⟨869939, by rfl⟩ : syracuseStep 1159919 = 1739879) B1739879
theorem B1750247 : Blo 342753 1750247 := bstep (se 1 (by rfl) ⟨1312685, by rfl⟩ : syracuseStep 1750247 = 2625371) B2625371
theorem B2210237 : Blo 342753 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B2931947 : Blo 342753 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B933223 : Blo 342753 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B344303 : Blo 342753 344303 := bstep (se 1 (by rfl) ⟨258227, by rfl⟩ : syracuseStep 344303 = 516455) B516455
theorem B4768055 : Blo 342753 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B15090299 : Blo 342753 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B1164563 : Blo 342753 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B345471 : Blo 342753 345471 := bstep (se 1 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 345471 = 518207) B518207
theorem B1164779 : Blo 342753 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B3294715 : Blo 342753 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B2213723 : Blo 342753 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B1099943 : Blo 342753 1099943 := bstep (se 1 (by rfl) ⟨824957, by rfl⟩ : syracuseStep 1099943 = 1649915) B1649915
theorem B4967497 : Blo 342753 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B3919103 : Blo 342753 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B135548315 : Blo 342753 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B7459037 : Blo 342753 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B875063 : Blo 342753 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B4054607 : Blo 342753 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B518057 : Blo 342753 518057 := bstep (se 2 (by rfl) ⟨194271, by rfl⟩ : syracuseStep 518057 = 388543) B388543
theorem B584057 : Blo 342753 584057 := bstep (se 2 (by rfl) ⟨219021, by rfl⟩ : syracuseStep 584057 = 438043) B438043
theorem B16771535 : Blo 342753 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B518639 : Blo 342753 518639 := bstep (se 1 (by rfl) ⟨388979, by rfl⟩ : syracuseStep 518639 = 777959) B777959
theorem B15166025 : Blo 342753 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B518783 : Blo 342753 518783 := bstep (se 1 (by rfl) ⟨389087, by rfl⟩ : syracuseStep 518783 = 778175) B778175
theorem B518975 : Blo 342753 518975 := bstep (se 1 (by rfl) ⟨389231, by rfl⟩ : syracuseStep 518975 = 778463) B778463
theorem B978409 : Blo 342753 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B519935 : Blo 342753 519935 := bstep (se 1 (by rfl) ⟨389951, by rfl⟩ : syracuseStep 519935 = 779903) B779903
theorem B31948739 : Blo 342753 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B3178703 : Blo 342753 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B10060199 : Blo 342753 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B1475815 : Blo 342753 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B4392953 : Blo 342753 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B6623329 : Blo 342753 6623329 := bstep (se 2 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 6623329 = 4967497) B4967497
theorem B11181023 : Blo 342753 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B466175 : Blo 342753 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B733295 : Blo 342753 733295 := bstep (se 1 (by rfl) ⟨549971, by rfl⟩ : syracuseStep 733295 = 1099943) B1099943
theorem B43040155 : Blo 342753 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B2703071 : Blo 342753 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B345371 : Blo 342753 345371 := bstep (se 1 (by rfl) ⟨259028, by rfl⟩ : syracuseStep 345371 = 518057) B518057
theorem B345759 : Blo 342753 345759 := bstep (se 1 (by rfl) ⟨259319, by rfl⟩ : syracuseStep 345759 = 518639) B518639
theorem B10110683 : Blo 342753 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B345855 : Blo 342753 345855 := bstep (se 1 (by rfl) ⟨259391, by rfl⟩ : syracuseStep 345855 = 518783) B518783
theorem B706313 : Blo 342753 706313 := bstep (se 2 (by rfl) ⟨264867, by rfl⟩ : syracuseStep 706313 = 529735) B529735
theorem B345983 : Blo 342753 345983 := bstep (se 1 (by rfl) ⟨259487, by rfl⟩ : syracuseStep 345983 = 518975) B518975
theorem B346623 : Blo 342753 346623 := bstep (se 1 (by rfl) ⟨259967, by rfl⟩ : syracuseStep 346623 = 519935) B519935
theorem B1166183 : Blo 342753 1166183 := bstep (se 1 (by rfl) ⟨874637, by rfl⟩ : syracuseStep 1166183 = 1749275) B1749275
theorem B10603655 : Blo 342753 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B773279 : Blo 342753 773279 := bstep (se 1 (by rfl) ⟨579959, by rfl⟩ : syracuseStep 773279 = 1159919) B1159919
theorem B1166831 : Blo 342753 1166831 := bstep (se 1 (by rfl) ⟨875123, by rfl⟩ : syracuseStep 1166831 = 1750247) B1750247
theorem B1954631 : Blo 342753 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B776375 : Blo 342753 776375 := bstep (se 1 (by rfl) ⟨582281, by rfl⟩ : syracuseStep 776375 = 1164563) B1164563
theorem B776519 : Blo 342753 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B2612735 : Blo 342753 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B90365543 : Blo 342753 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B16801901 : Blo 342753 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B4972691 : Blo 342753 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B583375 : Blo 342753 583375 := bstep (se 1 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 583375 = 875063) B875063
theorem B1304545 : Blo 342753 1304545 := bstep (se 2 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 1304545 = 978409) B978409
theorem B389371 : Blo 342753 389371 := bstep (se 1 (by rfl) ⟨292028, by rfl⟩ : syracuseStep 389371 = 584057) B584057
theorem B1473491 : Blo 342753 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1244297 : Blo 342753 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B21299159 : Blo 342753 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B1967753 : Blo 342753 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B1739393 : Blo 342753 1739393 := bstep (se 2 (by rfl) ⟨652272, by rfl⟩ : syracuseStep 1739393 = 1304545) B1304545
theorem B1741823 : Blo 342753 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B3315127 : Blo 342753 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B57386873 : Blo 342753 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B829531 : Blo 342753 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B56797757 : Blo 342753 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B470875 : Blo 342753 470875 := bstep (se 1 (by rfl) ⟨353156, by rfl⟩ : syracuseStep 470875 = 706313) B706313
theorem B2928635 : Blo 342753 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B7454015 : Blo 342753 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B60243695 : Blo 342753 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B8831105 : Blo 342753 8831105 := bstep (se 2 (by rfl) ⟨3311664, by rfl⟩ : syracuseStep 8831105 = 6623329) B6623329
theorem B2119135 : Blo 342753 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B6706799 : Blo 342753 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B6740455 : Blo 342753 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B777455 : Blo 342753 777455 := bstep (se 1 (by rfl) ⟨583091, by rfl⟩ : syracuseStep 777455 = 1166183) B1166183
theorem B7069103 : Blo 342753 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B515519 : Blo 342753 515519 := bstep (se 1 (by rfl) ⟨386639, by rfl⟩ : syracuseStep 515519 = 773279) B773279
theorem B777833 : Blo 342753 777833 := bstep (se 2 (by rfl) ⟨291687, by rfl⟩ : syracuseStep 777833 = 583375) B583375
theorem B777887 : Blo 342753 777887 := bstep (se 1 (by rfl) ⟨583415, by rfl⟩ : syracuseStep 777887 = 1166831) B1166831
theorem B1303087 : Blo 342753 1303087 := bstep (se 1 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 1303087 = 1954631) B1954631
theorem B517583 : Blo 342753 517583 := bstep (se 1 (by rfl) ⟨388187, by rfl⟩ : syracuseStep 517583 = 776375) B776375
theorem B517679 : Blo 342753 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B11201267 : Blo 342753 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B519161 : Blo 342753 519161 := bstep (se 2 (by rfl) ⟨194685, by rfl⟩ : syracuseStep 519161 = 389371) B389371
theorem B3929309 : Blo 342753 3929309 := bstep (se 3 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 3929309 = 1473491) B1473491
theorem B488863 : Blo 342753 488863 := bstep (se 1 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 488863 = 733295) B733295
theorem B1243133 : Blo 342753 1243133 := bstep (se 3 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 1243133 = 466175) B466175
theorem B1802047 : Blo 342753 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B4424165 : Blo 342753 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B1737449 : Blo 342753 1737449 := bstep (se 2 (by rfl) ⟨651543, by rfl⟩ : syracuseStep 1737449 = 1303087) B1303087
theorem B1311835 : Blo 342753 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B627833 : Blo 342753 627833 := bstep (se 2 (by rfl) ⟨235437, by rfl⟩ : syracuseStep 627833 = 470875) B470875
theorem B2825513 : Blo 342753 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B8987273 : Blo 342753 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B828755 : Blo 342753 828755 := bstep (se 1 (by rfl) ⟨621566, by rfl⟩ : syracuseStep 828755 = 1243133) B1243133
theorem B2402729 : Blo 342753 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B1159595 : Blo 342753 1159595 := bstep (se 1 (by rfl) ⟨869696, by rfl⟩ : syracuseStep 1159595 = 1739393) B1739393
theorem B1161215 : Blo 342753 1161215 := bstep (se 1 (by rfl) ⟨870911, by rfl⟩ : syracuseStep 1161215 = 1741823) B1741823
theorem B4471199 : Blo 342753 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B343679 : Blo 342753 343679 := bstep (se 1 (by rfl) ⟨257759, by rfl⟩ : syracuseStep 343679 = 515519) B515519
theorem B345055 : Blo 342753 345055 := bstep (se 1 (by rfl) ⟨258791, by rfl⟩ : syracuseStep 345055 = 517583) B517583
theorem B345119 : Blo 342753 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B38257915 : Blo 342753 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B37865171 : Blo 342753 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B346107 : Blo 342753 346107 := bstep (se 1 (by rfl) ⟨259580, by rfl⟩ : syracuseStep 346107 = 519161) B519161
theorem B1952423 : Blo 342753 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B4969343 : Blo 342753 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B40162463 : Blo 342753 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B5887403 : Blo 342753 5887403 := bstep (se 1 (by rfl) ⟨4415552, by rfl⟩ : syracuseStep 5887403 = 8831105) B8831105
theorem B518303 : Blo 342753 518303 := bstep (se 1 (by rfl) ⟨388727, by rfl⟩ : syracuseStep 518303 = 777455) B777455
theorem B4712735 : Blo 342753 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B518555 : Blo 342753 518555 := bstep (se 1 (by rfl) ⟨388916, by rfl⟩ : syracuseStep 518555 = 777833) B777833
theorem B518591 : Blo 342753 518591 := bstep (se 1 (by rfl) ⟨388943, by rfl⟩ : syracuseStep 518591 = 777887) B777887
theorem B7467511 : Blo 342753 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B651817 : Blo 342753 651817 := bstep (se 2 (by rfl) ⟨244431, by rfl⟩ : syracuseStep 651817 = 488863) B488863
theorem B4420169 : Blo 342753 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B2619539 : Blo 342753 2619539 := bstep (se 1 (by rfl) ⟨1964654, by rfl⟩ : syracuseStep 2619539 = 3929309) B3929309
theorem B2949443 : Blo 342753 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B3312895 : Blo 342753 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B26774975 : Blo 342753 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B1746359 : Blo 342753 1746359 := bstep (se 1 (by rfl) ⟨1309769, by rfl⟩ : syracuseStep 1746359 = 2619539) B2619539
theorem B1158299 : Blo 342753 1158299 := bstep (se 1 (by rfl) ⟨868724, by rfl⟩ : syracuseStep 1158299 = 1737449) B1737449
theorem B25243447 : Blo 342753 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B1749113 : Blo 342753 1749113 := bstep (se 2 (by rfl) ⟨655917, by rfl⟩ : syracuseStep 1749113 = 1311835) B1311835
theorem B1883675 : Blo 342753 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B869089 : Blo 342753 869089 := bstep (se 2 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 869089 = 651817) B651817
theorem B345535 : Blo 342753 345535 := bstep (se 1 (by rfl) ⟨259151, by rfl⟩ : syracuseStep 345535 = 518303) B518303
theorem B345703 : Blo 342753 345703 := bstep (se 1 (by rfl) ⟨259277, by rfl⟩ : syracuseStep 345703 = 518555) B518555
theorem B345727 : Blo 342753 345727 := bstep (se 1 (by rfl) ⟨259295, by rfl⟩ : syracuseStep 345727 = 518591) B518591
theorem B773063 : Blo 342753 773063 := bstep (se 1 (by rfl) ⟨579797, by rfl⟩ : syracuseStep 773063 = 1159595) B1159595
theorem B774143 : Blo 342753 774143 := bstep (se 1 (by rfl) ⟨580607, by rfl⟩ : syracuseStep 774143 = 1161215) B1161215
theorem B51010553 : Blo 342753 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B1301615 : Blo 342753 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B418555 : Blo 342753 418555 := bstep (se 1 (by rfl) ⟨313916, by rfl⟩ : syracuseStep 418555 = 627833) B627833
theorem B3924935 : Blo 342753 3924935 := bstep (se 1 (by rfl) ⟨2943701, by rfl⟩ : syracuseStep 3924935 = 5887403) B5887403
theorem B5991515 : Blo 342753 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B9956681 : Blo 342753 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B552503 : Blo 342753 552503 := bstep (se 1 (by rfl) ⟨414377, by rfl⟩ : syracuseStep 552503 = 828755) B828755
theorem B3141823 : Blo 342753 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B1601819 : Blo 342753 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B2946779 : Blo 342753 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B2980799 : Blo 342753 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B1966295 : Blo 342753 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B558073 : Blo 342753 558073 := bstep (se 2 (by rfl) ⟨209277, by rfl⟩ : syracuseStep 558073 = 418555) B418555
theorem B33657929 : Blo 342753 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B368335 : Blo 342753 368335 := bstep (se 1 (by rfl) ⟨276251, by rfl⟩ : syracuseStep 368335 = 552503) B552503
theorem B1255783 : Blo 342753 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B1158785 : Blo 342753 1158785 := bstep (se 2 (by rfl) ⟨434544, by rfl⟩ : syracuseStep 1158785 = 869089) B869089
theorem B867743 : Blo 342753 867743 := bstep (se 1 (by rfl) ⟨650807, by rfl⟩ : syracuseStep 867743 = 1301615) B1301615
theorem B1164239 : Blo 342753 1164239 := bstep (se 1 (by rfl) ⟨873179, by rfl⟩ : syracuseStep 1164239 = 1746359) B1746359
theorem B772199 : Blo 342753 772199 := bstep (se 1 (by rfl) ⟨579149, by rfl⟩ : syracuseStep 772199 = 1158299) B1158299
theorem B6637787 : Blo 342753 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B1166075 : Blo 342753 1166075 := bstep (se 1 (by rfl) ⟨874556, by rfl⟩ : syracuseStep 1166075 = 1749113) B1749113
theorem B1067879 : Blo 342753 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B1987199 : Blo 342753 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B515375 : Blo 342753 515375 := bstep (se 1 (by rfl) ⟨386531, by rfl⟩ : syracuseStep 515375 = 773063) B773063
theorem B17849983 : Blo 342753 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B516095 : Blo 342753 516095 := bstep (se 1 (by rfl) ⟨387071, by rfl⟩ : syracuseStep 516095 = 774143) B774143
theorem B4417193 : Blo 342753 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B34007035 : Blo 342753 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B4189097 : Blo 342753 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B2616623 : Blo 342753 2616623 := bstep (se 1 (by rfl) ⟨1962467, by rfl⟩ : syracuseStep 2616623 = 3924935) B3924935
theorem B3994343 : Blo 342753 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B1964519 : Blo 342753 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B1310863 : Blo 342753 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B4425191 : Blo 342753 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B1674377 : Blo 342753 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B2792731 : Blo 342753 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B1744415 : Blo 342753 1744415 := bstep (se 1 (by rfl) ⟨1308311, by rfl⟩ : syracuseStep 1744415 = 2616623) B2616623
theorem B2662895 : Blo 342753 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B23799977 : Blo 342753 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B1324799 : Blo 342753 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B343583 : Blo 342753 343583 := bstep (se 1 (by rfl) ⟨257687, by rfl⟩ : syracuseStep 343583 = 515375) B515375
theorem B344063 : Blo 342753 344063 := bstep (se 1 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 344063 = 516095) B516095
theorem B772523 : Blo 342753 772523 := bstep (se 1 (by rfl) ⟨579392, by rfl⟩ : syracuseStep 772523 = 1158785) B1158785
theorem B578495 : Blo 342753 578495 := bstep (se 1 (by rfl) ⟨433871, by rfl⟩ : syracuseStep 578495 = 867743) B867743
theorem B776159 : Blo 342753 776159 := bstep (se 1 (by rfl) ⟨582119, by rfl⟩ : syracuseStep 776159 = 1164239) B1164239
theorem B514799 : Blo 342753 514799 := bstep (se 1 (by rfl) ⟨386099, by rfl⟩ : syracuseStep 514799 = 772199) B772199
theorem B777383 : Blo 342753 777383 := bstep (se 1 (by rfl) ⟨583037, by rfl⟩ : syracuseStep 777383 = 1166075) B1166075
theorem B711919 : Blo 342753 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B45342713 : Blo 342753 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B22438619 : Blo 342753 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B2976389 : Blo 342753 2976389 := bstep (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) B558073
theorem B2944795 : Blo 342753 2944795 := bstep (se 1 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 2944795 = 4417193) B4417193
theorem B1309679 : Blo 342753 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B491113 : Blo 342753 491113 := bstep (se 2 (by rfl) ⟨184167, by rfl⟩ : syracuseStep 491113 = 368335) B368335
theorem B2950127 : Blo 342753 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B1116251 : Blo 342753 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B15866651 : Blo 342753 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B1747817 : Blo 342753 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B343199 : Blo 342753 343199 := bstep (se 1 (by rfl) ⟨257399, by rfl⟩ : syracuseStep 343199 = 514799) B514799
theorem B1162943 : Blo 342753 1162943 := bstep (se 1 (by rfl) ⟨872207, by rfl⟩ : syracuseStep 1162943 = 1744415) B1744415
theorem B30228475 : Blo 342753 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B14959079 : Blo 342753 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B1984259 : Blo 342753 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B3723641 : Blo 342753 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B873119 : Blo 342753 873119 := bstep (se 1 (by rfl) ⟨654839, by rfl⟩ : syracuseStep 873119 = 1309679) B1309679
theorem B7101053 : Blo 342753 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B515015 : Blo 342753 515015 := bstep (se 1 (by rfl) ⟨386261, by rfl⟩ : syracuseStep 515015 = 772523) B772523
theorem B385663 : Blo 342753 385663 := bstep (se 1 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 385663 = 578495) B578495
theorem B517439 : Blo 342753 517439 := bstep (se 1 (by rfl) ⟨388079, by rfl⟩ : syracuseStep 517439 = 776159) B776159
theorem B518255 : Blo 342753 518255 := bstep (se 1 (by rfl) ⟨388691, by rfl⟩ : syracuseStep 518255 = 777383) B777383
theorem B3926393 : Blo 342753 3926393 := bstep (se 2 (by rfl) ⟨1472397, by rfl⟩ : syracuseStep 3926393 = 2944795) B2944795
theorem B883199 : Blo 342753 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B949225 : Blo 342753 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B654817 : Blo 342753 654817 := bstep (se 2 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 654817 = 491113) B491113
theorem B1966751 : Blo 342753 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B42311069 : Blo 342753 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B9972719 : Blo 342753 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B1322839 : Blo 342753 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B4734035 : Blo 342753 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B343343 : Blo 342753 343343 := bstep (se 1 (by rfl) ⟨257507, by rfl⟩ : syracuseStep 343343 = 515015) B515015
theorem B344959 : Blo 342753 344959 := bstep (se 1 (by rfl) ⟨258719, by rfl⟩ : syracuseStep 344959 = 517439) B517439
theorem B345503 : Blo 342753 345503 := bstep (se 1 (by rfl) ⟨259127, by rfl⟩ : syracuseStep 345503 = 518255) B518255
theorem B1165211 : Blo 342753 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B1265633 : Blo 342753 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B873089 : Blo 342753 873089 := bstep (se 2 (by rfl) ⟨327408, by rfl⟩ : syracuseStep 873089 = 654817) B654817
theorem B775295 : Blo 342753 775295 := bstep (se 1 (by rfl) ⟨581471, by rfl⟩ : syracuseStep 775295 = 1162943) B1162943
theorem B514217 : Blo 342753 514217 := bstep (se 2 (by rfl) ⟨192831, by rfl⟩ : syracuseStep 514217 = 385663) B385663
theorem B744167 : Blo 342753 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B2482427 : Blo 342753 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B582079 : Blo 342753 582079 := bstep (se 1 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 582079 = 873119) B873119
theorem B2617595 : Blo 342753 2617595 := bstep (se 1 (by rfl) ⟨1963196, by rfl⟩ : syracuseStep 2617595 = 3926393) B3926393
theorem B588799 : Blo 342753 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B40304633 : Blo 342753 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B1311167 : Blo 342753 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B1745063 : Blo 342753 1745063 := bstep (se 1 (by rfl) ⟨1308797, by rfl⟩ : syracuseStep 1745063 = 2617595) B2617595
theorem B3156023 : Blo 342753 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B342811 : Blo 342753 342811 := bstep (se 1 (by rfl) ⟨257108, by rfl⟩ : syracuseStep 342811 = 514217) B514217
theorem B1654951 : Blo 342753 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B1984445 : Blo 342753 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B776105 : Blo 342753 776105 := bstep (se 2 (by rfl) ⟨291039, by rfl⟩ : syracuseStep 776105 = 582079) B582079
theorem B776807 : Blo 342753 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B843755 : Blo 342753 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B582059 : Blo 342753 582059 := bstep (se 1 (by rfl) ⟨436544, by rfl⟩ : syracuseStep 582059 = 873089) B873089
theorem B516863 : Blo 342753 516863 := bstep (se 1 (by rfl) ⟨387647, by rfl⟩ : syracuseStep 516863 = 775295) B775295
theorem B28207379 : Blo 342753 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B1763785 : Blo 342753 1763785 := bstep (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) B1322839
theorem B6648479 : Blo 342753 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B785065 : Blo 342753 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B107479021 : Blo 342753 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B2104015 : Blo 342753 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B4432319 : Blo 342753 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B143305361 : Blo 342753 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B2206601 : Blo 342753 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B1322963 : Blo 342753 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B1163375 : Blo 342753 1163375 := bstep (se 1 (by rfl) ⟨872531, by rfl⟩ : syracuseStep 1163375 = 1745063) B1745063
theorem B344575 : Blo 342753 344575 := bstep (se 1 (by rfl) ⟨258431, by rfl⟩ : syracuseStep 344575 = 516863) B516863
theorem B2250013 : Blo 342753 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B874111 : Blo 342753 874111 := bstep (se 1 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 874111 = 1311167) B1311167
theorem B2351713 : Blo 342753 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B517403 : Blo 342753 517403 := bstep (se 1 (by rfl) ⟨388052, by rfl⟩ : syracuseStep 517403 = 776105) B776105
theorem B517871 : Blo 342753 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B388039 : Blo 342753 388039 := bstep (se 1 (by rfl) ⟨291029, by rfl⟩ : syracuseStep 388039 = 582059) B582059
theorem B18804919 : Blo 342753 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B1046753 : Blo 342753 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B25073225 : Blo 342753 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B2954879 : Blo 342753 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B697835 : Blo 342753 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B344935 : Blo 342753 344935 := bstep (se 1 (by rfl) ⟨258701, by rfl⟩ : syracuseStep 344935 = 517403) B517403
theorem B345247 : Blo 342753 345247 := bstep (se 1 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 345247 = 517871) B517871
theorem B3000017 : Blo 342753 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B95536907 : Blo 342753 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1165481 : Blo 342753 1165481 := bstep (se 2 (by rfl) ⟨437055, by rfl⟩ : syracuseStep 1165481 = 874111) B874111
theorem B2805353 : Blo 342753 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B775583 : Blo 342753 775583 := bstep (se 1 (by rfl) ⟨581687, by rfl⟩ : syracuseStep 775583 = 1163375) B1163375
theorem B3135617 : Blo 342753 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B517385 : Blo 342753 517385 := bstep (se 2 (by rfl) ⟨194019, by rfl⟩ : syracuseStep 517385 = 388039) B388039
theorem B1471067 : Blo 342753 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B881975 : Blo 342753 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B1870235 : Blo 342753 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B16715483 : Blo 342753 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B1969919 : Blo 342753 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B8000045 : Blo 342753 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B344923 : Blo 342753 344923 := bstep (se 1 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 344923 = 517385) B517385
theorem B63691271 : Blo 342753 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B776987 : Blo 342753 776987 := bstep (se 1 (by rfl) ⟨582740, by rfl⟩ : syracuseStep 776987 = 1165481) B1165481
theorem B517055 : Blo 342753 517055 := bstep (se 1 (by rfl) ⟨387791, by rfl⟩ : syracuseStep 517055 = 775583) B775583
theorem B1860893 : Blo 342753 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B2090411 : Blo 342753 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B980711 : Blo 342753 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B587983 : Blo 342753 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B1246823 : Blo 342753 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B11143655 : Blo 342753 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B1313279 : Blo 342753 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B344703 : Blo 342753 344703 := bstep (se 1 (by rfl) ⟨258527, by rfl⟩ : syracuseStep 344703 = 517055) B517055
theorem B1393607 : Blo 342753 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B5333363 : Blo 342753 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B42460847 : Blo 342753 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B517991 : Blo 342753 517991 := bstep (se 1 (by rfl) ⟨388493, by rfl⟩ : syracuseStep 517991 = 776987) B776987
theorem B1240595 : Blo 342753 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B783977 : Blo 342753 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B653807 : Blo 342753 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B827063 : Blo 342753 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B435871 : Blo 342753 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B929071 : Blo 342753 929071 := bstep (se 1 (by rfl) ⟨696803, by rfl⟩ : syracuseStep 929071 = 1393607) B1393607
theorem B831215 : Blo 342753 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B3555575 : Blo 342753 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B345327 : Blo 342753 345327 := bstep (se 1 (by rfl) ⟨258995, by rfl⟩ : syracuseStep 345327 = 517991) B517991
theorem B7429103 : Blo 342753 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B875519 : Blo 342753 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B2090605 : Blo 342753 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B28307231 : Blo 342753 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B2787473 : Blo 342753 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B4952735 : Blo 342753 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B2370383 : Blo 342753 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B581161 : Blo 342753 581161 := bstep (se 2 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 581161 = 435871) B435871
theorem B1238761 : Blo 342753 1238761 := bstep (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) B929071
theorem B583679 : Blo 342753 583679 := bstep (se 1 (by rfl) ⟨437759, by rfl⟩ : syracuseStep 583679 = 875519) B875519
theorem B551375 : Blo 342753 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B554143 : Blo 342753 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B18871487 : Blo 342753 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B367583 : Blo 342753 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B1580255 : Blo 342753 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B1651681 : Blo 342753 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B738857 : Blo 342753 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B774881 : Blo 342753 774881 := bstep (se 2 (by rfl) ⟨290580, by rfl⟩ : syracuseStep 774881 = 581161) B581161
theorem B1858315 : Blo 342753 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B3301823 : Blo 342753 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B389119 : Blo 342753 389119 := bstep (se 1 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 389119 = 583679) B583679
theorem B12580991 : Blo 342753 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B492571 : Blo 342753 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B1053503 : Blo 342753 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B2202241 : Blo 342753 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B2477753 : Blo 342753 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B8804861 : Blo 342753 8804861 := bstep (se 3 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 8804861 = 3301823) B3301823
theorem B516587 : Blo 342753 516587 := bstep (se 1 (by rfl) ⟨387440, by rfl⟩ : syracuseStep 516587 = 774881) B774881
theorem B518825 : Blo 342753 518825 := bstep (se 2 (by rfl) ⟨194559, by rfl⟩ : syracuseStep 518825 = 389119) B389119
theorem B980221 : Blo 342753 980221 := bstep (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) B367583
theorem B8387327 : Blo 342753 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B656761 : Blo 342753 656761 := bstep (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) B492571
theorem B5869907 : Blo 342753 5869907 := bstep (se 1 (by rfl) ⟨4402430, by rfl⟩ : syracuseStep 5869907 = 8804861) B8804861
theorem B1651835 : Blo 342753 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B702335 : Blo 342753 702335 := bstep (se 1 (by rfl) ⟨526751, by rfl⟩ : syracuseStep 702335 = 1053503) B1053503
theorem B344391 : Blo 342753 344391 := bstep (se 1 (by rfl) ⟨258293, by rfl⟩ : syracuseStep 344391 = 516587) B516587
theorem B345883 : Blo 342753 345883 := bstep (se 1 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 345883 = 518825) B518825
theorem B2936321 : Blo 342753 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B5591551 : Blo 342753 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B1306961 : Blo 342753 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B468223 : Blo 342753 468223 := bstep (se 1 (by rfl) ⟨351167, by rfl⟩ : syracuseStep 468223 = 702335) B702335
theorem B3913271 : Blo 342753 3913271 := bstep (se 1 (by rfl) ⟨2934953, by rfl⟩ : syracuseStep 3913271 = 5869907) B5869907
theorem B7455401 : Blo 342753 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B871307 : Blo 342753 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B1101223 : Blo 342753 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B875681 : Blo 342753 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B1957547 : Blo 342753 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B2497189 : Blo 342753 2497189 := bstep (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) B468223
theorem B2608847 : Blo 342753 2608847 := bstep (se 1 (by rfl) ⟨1956635, by rfl⟩ : syracuseStep 2608847 = 3913271) B3913271
theorem B4970267 : Blo 342753 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B580871 : Blo 342753 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B1468297 : Blo 342753 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B583787 : Blo 342753 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B1305031 : Blo 342753 1305031 := bstep (se 1 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 1305031 = 1957547) B1957547
theorem B1739231 : Blo 342753 1739231 := bstep (se 1 (by rfl) ⟨1304423, by rfl⟩ : syracuseStep 1739231 = 2608847) B2608847
theorem B1740041 : Blo 342753 1740041 := bstep (se 2 (by rfl) ⟨652515, by rfl⟩ : syracuseStep 1740041 = 1305031) B1305031
theorem B3313511 : Blo 342753 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B3329585 : Blo 342753 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B1957729 : Blo 342753 1957729 := bstep (se 2 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 1957729 = 1468297) B1468297
theorem B387247 : Blo 342753 387247 := bstep (se 1 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 387247 = 580871) B580871
theorem B389191 : Blo 342753 389191 := bstep (se 1 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 389191 = 583787) B583787
theorem B1159487 : Blo 342753 1159487 := bstep (se 1 (by rfl) ⟨869615, by rfl⟩ : syracuseStep 1159487 = 1739231) B1739231
theorem B1160027 : Blo 342753 1160027 := bstep (se 1 (by rfl) ⟨870020, by rfl⟩ : syracuseStep 1160027 = 1740041) B1740041
theorem B2209007 : Blo 342753 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B2610305 : Blo 342753 2610305 := bstep (se 2 (by rfl) ⟨978864, by rfl⟩ : syracuseStep 2610305 = 1957729) B1957729
theorem B2219723 : Blo 342753 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B516329 : Blo 342753 516329 := bstep (se 2 (by rfl) ⟨193623, by rfl⟩ : syracuseStep 516329 = 387247) B387247
theorem B518921 : Blo 342753 518921 := bstep (se 2 (by rfl) ⟨194595, by rfl⟩ : syracuseStep 518921 = 389191) B389191
theorem B1740203 : Blo 342753 1740203 := bstep (se 1 (by rfl) ⟨1305152, by rfl⟩ : syracuseStep 1740203 = 2610305) B2610305
theorem B1479815 : Blo 342753 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B344219 : Blo 342753 344219 := bstep (se 1 (by rfl) ⟨258164, by rfl⟩ : syracuseStep 344219 = 516329) B516329
theorem B345947 : Blo 342753 345947 := bstep (se 1 (by rfl) ⟨259460, by rfl⟩ : syracuseStep 345947 = 518921) B518921
theorem B772991 : Blo 342753 772991 := bstep (se 1 (by rfl) ⟨579743, by rfl⟩ : syracuseStep 772991 = 1159487) B1159487
theorem B773351 : Blo 342753 773351 := bstep (se 1 (by rfl) ⟨580013, by rfl⟩ : syracuseStep 773351 = 1160027) B1160027
theorem B1472671 : Blo 342753 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B986543 : Blo 342753 986543 := bstep (se 1 (by rfl) ⟨739907, by rfl⟩ : syracuseStep 986543 = 1479815) B1479815
theorem B1160135 : Blo 342753 1160135 := bstep (se 1 (by rfl) ⟨870101, by rfl⟩ : syracuseStep 1160135 = 1740203) B1740203
theorem B515327 : Blo 342753 515327 := bstep (se 1 (by rfl) ⟨386495, by rfl⟩ : syracuseStep 515327 = 772991) B772991
theorem B515567 : Blo 342753 515567 := bstep (se 1 (by rfl) ⟨386675, by rfl⟩ : syracuseStep 515567 = 773351) B773351
theorem B1963561 : Blo 342753 1963561 := bstep (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) B1472671
theorem B657695 : Blo 342753 657695 := bstep (se 1 (by rfl) ⟨493271, by rfl⟩ : syracuseStep 657695 = 986543) B986543
theorem B343551 : Blo 342753 343551 := bstep (se 1 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 343551 = 515327) B515327
theorem B343711 : Blo 342753 343711 := bstep (se 1 (by rfl) ⟨257783, by rfl⟩ : syracuseStep 343711 = 515567) B515567
theorem B773423 : Blo 342753 773423 := bstep (se 1 (by rfl) ⟨580067, by rfl⟩ : syracuseStep 773423 = 1160135) B1160135
theorem B2618081 : Blo 342753 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B1745387 : Blo 342753 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B438463 : Blo 342753 438463 := bstep (se 1 (by rfl) ⟨328847, by rfl⟩ : syracuseStep 438463 = 657695) B657695
theorem B515615 : Blo 342753 515615 := bstep (se 1 (by rfl) ⟨386711, by rfl⟩ : syracuseStep 515615 = 773423) B773423
theorem B343743 : Blo 342753 343743 := bstep (se 1 (by rfl) ⟨257807, by rfl⟩ : syracuseStep 343743 = 515615) B515615
theorem B1163591 : Blo 342753 1163591 := bstep (se 1 (by rfl) ⟨872693, by rfl⟩ : syracuseStep 1163591 = 1745387) B1745387
theorem B584617 : Blo 342753 584617 := bstep (se 2 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 584617 = 438463) B438463
theorem B775727 : Blo 342753 775727 := bstep (se 1 (by rfl) ⟨581795, by rfl⟩ : syracuseStep 775727 = 1163591) B1163591
theorem B779489 : Blo 342753 779489 := bstep (se 2 (by rfl) ⟨292308, by rfl⟩ : syracuseStep 779489 = 584617) B584617
theorem B517151 : Blo 342753 517151 := bstep (se 1 (by rfl) ⟨387863, by rfl⟩ : syracuseStep 517151 = 775727) B775727
theorem B519659 : Blo 342753 519659 := bstep (se 1 (by rfl) ⟨389744, by rfl⟩ : syracuseStep 519659 = 779489) B779489
theorem B344767 : Blo 342753 344767 := bstep (se 1 (by rfl) ⟨258575, by rfl⟩ : syracuseStep 344767 = 517151) B517151
theorem B346439 : Blo 342753 346439 := bstep (se 1 (by rfl) ⟨259829, by rfl⟩ : syracuseStep 346439 = 519659) B519659

theorem C0 (j : ℕ) (h1 : 85688 ≤ j) (h2 : j ≤ 86387) : Blo 342753 (4 * j + 3) := by
  interval_cases j
  · exact B342755
  · exact B342759
  · exact B342763
  · exact B342767
  · exact B342771
  · exact B342775
  · exact B342779
  · exact B342783
  · exact B342787
  · exact B342791
  · exact B342795
  · exact B342799
  · exact B342803
  · exact B342807
  · exact B342811
  · exact B342815
  · exact B342819
  · exact B342823
  · exact B342827
  · exact B342831
  · exact B342835
  · exact B342839
  · exact B342843
  · exact B342847
  · exact B342851
  · exact B342855
  · exact B342859
  · exact B342863
  · exact B342867
  · exact B342871
  · exact B342875
  · exact B342879
  · exact B342883
  · exact B342887
  · exact B342891
  · exact B342895
  · exact B342899
  · exact B342903
  · exact B342907
  · exact B342911
  · exact B342915
  · exact B342919
  · exact B342923
  · exact B342927
  · exact B342931
  · exact B342935
  · exact B342939
  · exact B342943
  · exact B342947
  · exact B342951
  · exact B342955
  · exact B342959
  · exact B342963
  · exact B342967
  · exact B342971
  · exact B342975
  · exact B342979
  · exact B342983
  · exact B342987
  · exact B342991
  · exact B342995
  · exact B342999
  · exact B343003
  · exact B343007
  · exact B343011
  · exact B343015
  · exact B343019
  · exact B343023
  · exact B343027
  · exact B343031
  · exact B343035
  · exact B343039
  · exact B343043
  · exact B343047
  · exact B343051
  · exact B343055
  · exact B343059
  · exact B343063
  · exact B343067
  · exact B343071
  · exact B343075
  · exact B343079
  · exact B343083
  · exact B343087
  · exact B343091
  · exact B343095
  · exact B343099
  · exact B343103
  · exact B343107
  · exact B343111
  · exact B343115
  · exact B343119
  · exact B343123
  · exact B343127
  · exact B343131
  · exact B343135
  · exact B343139
  · exact B343143
  · exact B343147
  · exact B343151
  · exact B343155
  · exact B343159
  · exact B343163
  · exact B343167
  · exact B343171
  · exact B343175
  · exact B343179
  · exact B343183
  · exact B343187
  · exact B343191
  · exact B343195
  · exact B343199
  · exact B343203
  · exact B343207
  · exact B343211
  · exact B343215
  · exact B343219
  · exact B343223
  · exact B343227
  · exact B343231
  · exact B343235
  · exact B343239
  · exact B343243
  · exact B343247
  · exact B343251
  · exact B343255
  · exact B343259
  · exact B343263
  · exact B343267
  · exact B343271
  · exact B343275
  · exact B343279
  · exact B343283
  · exact B343287
  · exact B343291
  · exact B343295
  · exact B343299
  · exact B343303
  · exact B343307
  · exact B343311
  · exact B343315
  · exact B343319
  · exact B343323
  · exact B343327
  · exact B343331
  · exact B343335
  · exact B343339
  · exact B343343
  · exact B343347
  · exact B343351
  · exact B343355
  · exact B343359
  · exact B343363
  · exact B343367
  · exact B343371
  · exact B343375
  · exact B343379
  · exact B343383
  · exact B343387
  · exact B343391
  · exact B343395
  · exact B343399
  · exact B343403
  · exact B343407
  · exact B343411
  · exact B343415
  · exact B343419
  · exact B343423
  · exact B343427
  · exact B343431
  · exact B343435
  · exact B343439
  · exact B343443
  · exact B343447
  · exact B343451
  · exact B343455
  · exact B343459
  · exact B343463
  · exact B343467
  · exact B343471
  · exact B343475
  · exact B343479
  · exact B343483
  · exact B343487
  · exact B343491
  · exact B343495
  · exact B343499
  · exact B343503
  · exact B343507
  · exact B343511
  · exact B343515
  · exact B343519
  · exact B343523
  · exact B343527
  · exact B343531
  · exact B343535
  · exact B343539
  · exact B343543
  · exact B343547
  · exact B343551
  · exact B343555
  · exact B343559
  · exact B343563
  · exact B343567
  · exact B343571
  · exact B343575
  · exact B343579
  · exact B343583
  · exact B343587
  · exact B343591
  · exact B343595
  · exact B343599
  · exact B343603
  · exact B343607
  · exact B343611
  · exact B343615
  · exact B343619
  · exact B343623
  · exact B343627
  · exact B343631
  · exact B343635
  · exact B343639
  · exact B343643
  · exact B343647
  · exact B343651
  · exact B343655
  · exact B343659
  · exact B343663
  · exact B343667
  · exact B343671
  · exact B343675
  · exact B343679
  · exact B343683
  · exact B343687
  · exact B343691
  · exact B343695
  · exact B343699
  · exact B343703
  · exact B343707
  · exact B343711
  · exact B343715
  · exact B343719
  · exact B343723
  · exact B343727
  · exact B343731
  · exact B343735
  · exact B343739
  · exact B343743
  · exact B343747
  · exact B343751
  · exact B343755
  · exact B343759
  · exact B343763
  · exact B343767
  · exact B343771
  · exact B343775
  · exact B343779
  · exact B343783
  · exact B343787
  · exact B343791
  · exact B343795
  · exact B343799
  · exact B343803
  · exact B343807
  · exact B343811
  · exact B343815
  · exact B343819
  · exact B343823
  · exact B343827
  · exact B343831
  · exact B343835
  · exact B343839
  · exact B343843
  · exact B343847
  · exact B343851
  · exact B343855
  · exact B343859
  · exact B343863
  · exact B343867
  · exact B343871
  · exact B343875
  · exact B343879
  · exact B343883
  · exact B343887
  · exact B343891
  · exact B343895
  · exact B343899
  · exact B343903
  · exact B343907
  · exact B343911
  · exact B343915
  · exact B343919
  · exact B343923
  · exact B343927
  · exact B343931
  · exact B343935
  · exact B343939
  · exact B343943
  · exact B343947
  · exact B343951
  · exact B343955
  · exact B343959
  · exact B343963
  · exact B343967
  · exact B343971
  · exact B343975
  · exact B343979
  · exact B343983
  · exact B343987
  · exact B343991
  · exact B343995
  · exact B343999
  · exact B344003
  · exact B344007
  · exact B344011
  · exact B344015
  · exact B344019
  · exact B344023
  · exact B344027
  · exact B344031
  · exact B344035
  · exact B344039
  · exact B344043
  · exact B344047
  · exact B344051
  · exact B344055
  · exact B344059
  · exact B344063
  · exact B344067
  · exact B344071
  · exact B344075
  · exact B344079
  · exact B344083
  · exact B344087
  · exact B344091
  · exact B344095
  · exact B344099
  · exact B344103
  · exact B344107
  · exact B344111
  · exact B344115
  · exact B344119
  · exact B344123
  · exact B344127
  · exact B344131
  · exact B344135
  · exact B344139
  · exact B344143
  · exact B344147
  · exact B344151
  · exact B344155
  · exact B344159
  · exact B344163
  · exact B344167
  · exact B344171
  · exact B344175
  · exact B344179
  · exact B344183
  · exact B344187
  · exact B344191
  · exact B344195
  · exact B344199
  · exact B344203
  · exact B344207
  · exact B344211
  · exact B344215
  · exact B344219
  · exact B344223
  · exact B344227
  · exact B344231
  · exact B344235
  · exact B344239
  · exact B344243
  · exact B344247
  · exact B344251
  · exact B344255
  · exact B344259
  · exact B344263
  · exact B344267
  · exact B344271
  · exact B344275
  · exact B344279
  · exact B344283
  · exact B344287
  · exact B344291
  · exact B344295
  · exact B344299
  · exact B344303
  · exact B344307
  · exact B344311
  · exact B344315
  · exact B344319
  · exact B344323
  · exact B344327
  · exact B344331
  · exact B344335
  · exact B344339
  · exact B344343
  · exact B344347
  · exact B344351
  · exact B344355
  · exact B344359
  · exact B344363
  · exact B344367
  · exact B344371
  · exact B344375
  · exact B344379
  · exact B344383
  · exact B344387
  · exact B344391
  · exact B344395
  · exact B344399
  · exact B344403
  · exact B344407
  · exact B344411
  · exact B344415
  · exact B344419
  · exact B344423
  · exact B344427
  · exact B344431
  · exact B344435
  · exact B344439
  · exact B344443
  · exact B344447
  · exact B344451
  · exact B344455
  · exact B344459
  · exact B344463
  · exact B344467
  · exact B344471
  · exact B344475
  · exact B344479
  · exact B344483
  · exact B344487
  · exact B344491
  · exact B344495
  · exact B344499
  · exact B344503
  · exact B344507
  · exact B344511
  · exact B344515
  · exact B344519
  · exact B344523
  · exact B344527
  · exact B344531
  · exact B344535
  · exact B344539
  · exact B344543
  · exact B344547
  · exact B344551
  · exact B344555
  · exact B344559
  · exact B344563
  · exact B344567
  · exact B344571
  · exact B344575
  · exact B344579
  · exact B344583
  · exact B344587
  · exact B344591
  · exact B344595
  · exact B344599
  · exact B344603
  · exact B344607
  · exact B344611
  · exact B344615
  · exact B344619
  · exact B344623
  · exact B344627
  · exact B344631
  · exact B344635
  · exact B344639
  · exact B344643
  · exact B344647
  · exact B344651
  · exact B344655
  · exact B344659
  · exact B344663
  · exact B344667
  · exact B344671
  · exact B344675
  · exact B344679
  · exact B344683
  · exact B344687
  · exact B344691
  · exact B344695
  · exact B344699
  · exact B344703
  · exact B344707
  · exact B344711
  · exact B344715
  · exact B344719
  · exact B344723
  · exact B344727
  · exact B344731
  · exact B344735
  · exact B344739
  · exact B344743
  · exact B344747
  · exact B344751
  · exact B344755
  · exact B344759
  · exact B344763
  · exact B344767
  · exact B344771
  · exact B344775
  · exact B344779
  · exact B344783
  · exact B344787
  · exact B344791
  · exact B344795
  · exact B344799
  · exact B344803
  · exact B344807
  · exact B344811
  · exact B344815
  · exact B344819
  · exact B344823
  · exact B344827
  · exact B344831
  · exact B344835
  · exact B344839
  · exact B344843
  · exact B344847
  · exact B344851
  · exact B344855
  · exact B344859
  · exact B344863
  · exact B344867
  · exact B344871
  · exact B344875
  · exact B344879
  · exact B344883
  · exact B344887
  · exact B344891
  · exact B344895
  · exact B344899
  · exact B344903
  · exact B344907
  · exact B344911
  · exact B344915
  · exact B344919
  · exact B344923
  · exact B344927
  · exact B344931
  · exact B344935
  · exact B344939
  · exact B344943
  · exact B344947
  · exact B344951
  · exact B344955
  · exact B344959
  · exact B344963
  · exact B344967
  · exact B344971
  · exact B344975
  · exact B344979
  · exact B344983
  · exact B344987
  · exact B344991
  · exact B344995
  · exact B344999
  · exact B345003
  · exact B345007
  · exact B345011
  · exact B345015
  · exact B345019
  · exact B345023
  · exact B345027
  · exact B345031
  · exact B345035
  · exact B345039
  · exact B345043
  · exact B345047
  · exact B345051
  · exact B345055
  · exact B345059
  · exact B345063
  · exact B345067
  · exact B345071
  · exact B345075
  · exact B345079
  · exact B345083
  · exact B345087
  · exact B345091
  · exact B345095
  · exact B345099
  · exact B345103
  · exact B345107
  · exact B345111
  · exact B345115
  · exact B345119
  · exact B345123
  · exact B345127
  · exact B345131
  · exact B345135
  · exact B345139
  · exact B345143
  · exact B345147
  · exact B345151
  · exact B345155
  · exact B345159
  · exact B345163
  · exact B345167
  · exact B345171
  · exact B345175
  · exact B345179
  · exact B345183
  · exact B345187
  · exact B345191
  · exact B345195
  · exact B345199
  · exact B345203
  · exact B345207
  · exact B345211
  · exact B345215
  · exact B345219
  · exact B345223
  · exact B345227
  · exact B345231
  · exact B345235
  · exact B345239
  · exact B345243
  · exact B345247
  · exact B345251
  · exact B345255
  · exact B345259
  · exact B345263
  · exact B345267
  · exact B345271
  · exact B345275
  · exact B345279
  · exact B345283
  · exact B345287
  · exact B345291
  · exact B345295
  · exact B345299
  · exact B345303
  · exact B345307
  · exact B345311
  · exact B345315
  · exact B345319
  · exact B345323
  · exact B345327
  · exact B345331
  · exact B345335
  · exact B345339
  · exact B345343
  · exact B345347
  · exact B345351
  · exact B345355
  · exact B345359
  · exact B345363
  · exact B345367
  · exact B345371
  · exact B345375
  · exact B345379
  · exact B345383
  · exact B345387
  · exact B345391
  · exact B345395
  · exact B345399
  · exact B345403
  · exact B345407
  · exact B345411
  · exact B345415
  · exact B345419
  · exact B345423
  · exact B345427
  · exact B345431
  · exact B345435
  · exact B345439
  · exact B345443
  · exact B345447
  · exact B345451
  · exact B345455
  · exact B345459
  · exact B345463
  · exact B345467
  · exact B345471
  · exact B345475
  · exact B345479
  · exact B345483
  · exact B345487
  · exact B345491
  · exact B345495
  · exact B345499
  · exact B345503
  · exact B345507
  · exact B345511
  · exact B345515
  · exact B345519
  · exact B345523
  · exact B345527
  · exact B345531
  · exact B345535
  · exact B345539
  · exact B345543
  · exact B345547
  · exact B345551

theorem C1 (j : ℕ) (h1 : 86388 ≤ j) (h2 : j ≤ 86687) : Blo 342753 (4 * j + 3) := by
  interval_cases j
  · exact B345555
  · exact B345559
  · exact B345563
  · exact B345567
  · exact B345571
  · exact B345575
  · exact B345579
  · exact B345583
  · exact B345587
  · exact B345591
  · exact B345595
  · exact B345599
  · exact B345603
  · exact B345607
  · exact B345611
  · exact B345615
  · exact B345619
  · exact B345623
  · exact B345627
  · exact B345631
  · exact B345635
  · exact B345639
  · exact B345643
  · exact B345647
  · exact B345651
  · exact B345655
  · exact B345659
  · exact B345663
  · exact B345667
  · exact B345671
  · exact B345675
  · exact B345679
  · exact B345683
  · exact B345687
  · exact B345691
  · exact B345695
  · exact B345699
  · exact B345703
  · exact B345707
  · exact B345711
  · exact B345715
  · exact B345719
  · exact B345723
  · exact B345727
  · exact B345731
  · exact B345735
  · exact B345739
  · exact B345743
  · exact B345747
  · exact B345751
  · exact B345755
  · exact B345759
  · exact B345763
  · exact B345767
  · exact B345771
  · exact B345775
  · exact B345779
  · exact B345783
  · exact B345787
  · exact B345791
  · exact B345795
  · exact B345799
  · exact B345803
  · exact B345807
  · exact B345811
  · exact B345815
  · exact B345819
  · exact B345823
  · exact B345827
  · exact B345831
  · exact B345835
  · exact B345839
  · exact B345843
  · exact B345847
  · exact B345851
  · exact B345855
  · exact B345859
  · exact B345863
  · exact B345867
  · exact B345871
  · exact B345875
  · exact B345879
  · exact B345883
  · exact B345887
  · exact B345891
  · exact B345895
  · exact B345899
  · exact B345903
  · exact B345907
  · exact B345911
  · exact B345915
  · exact B345919
  · exact B345923
  · exact B345927
  · exact B345931
  · exact B345935
  · exact B345939
  · exact B345943
  · exact B345947
  · exact B345951
  · exact B345955
  · exact B345959
  · exact B345963
  · exact B345967
  · exact B345971
  · exact B345975
  · exact B345979
  · exact B345983
  · exact B345987
  · exact B345991
  · exact B345995
  · exact B345999
  · exact B346003
  · exact B346007
  · exact B346011
  · exact B346015
  · exact B346019
  · exact B346023
  · exact B346027
  · exact B346031
  · exact B346035
  · exact B346039
  · exact B346043
  · exact B346047
  · exact B346051
  · exact B346055
  · exact B346059
  · exact B346063
  · exact B346067
  · exact B346071
  · exact B346075
  · exact B346079
  · exact B346083
  · exact B346087
  · exact B346091
  · exact B346095
  · exact B346099
  · exact B346103
  · exact B346107
  · exact B346111
  · exact B346115
  · exact B346119
  · exact B346123
  · exact B346127
  · exact B346131
  · exact B346135
  · exact B346139
  · exact B346143
  · exact B346147
  · exact B346151
  · exact B346155
  · exact B346159
  · exact B346163
  · exact B346167
  · exact B346171
  · exact B346175
  · exact B346179
  · exact B346183
  · exact B346187
  · exact B346191
  · exact B346195
  · exact B346199
  · exact B346203
  · exact B346207
  · exact B346211
  · exact B346215
  · exact B346219
  · exact B346223
  · exact B346227
  · exact B346231
  · exact B346235
  · exact B346239
  · exact B346243
  · exact B346247
  · exact B346251
  · exact B346255
  · exact B346259
  · exact B346263
  · exact B346267
  · exact B346271
  · exact B346275
  · exact B346279
  · exact B346283
  · exact B346287
  · exact B346291
  · exact B346295
  · exact B346299
  · exact B346303
  · exact B346307
  · exact B346311
  · exact B346315
  · exact B346319
  · exact B346323
  · exact B346327
  · exact B346331
  · exact B346335
  · exact B346339
  · exact B346343
  · exact B346347
  · exact B346351
  · exact B346355
  · exact B346359
  · exact B346363
  · exact B346367
  · exact B346371
  · exact B346375
  · exact B346379
  · exact B346383
  · exact B346387
  · exact B346391
  · exact B346395
  · exact B346399
  · exact B346403
  · exact B346407
  · exact B346411
  · exact B346415
  · exact B346419
  · exact B346423
  · exact B346427
  · exact B346431
  · exact B346435
  · exact B346439
  · exact B346443
  · exact B346447
  · exact B346451
  · exact B346455
  · exact B346459
  · exact B346463
  · exact B346467
  · exact B346471
  · exact B346475
  · exact B346479
  · exact B346483
  · exact B346487
  · exact B346491
  · exact B346495
  · exact B346499
  · exact B346503
  · exact B346507
  · exact B346511
  · exact B346515
  · exact B346519
  · exact B346523
  · exact B346527
  · exact B346531
  · exact B346535
  · exact B346539
  · exact B346543
  · exact B346547
  · exact B346551
  · exact B346555
  · exact B346559
  · exact B346563
  · exact B346567
  · exact B346571
  · exact B346575
  · exact B346579
  · exact B346583
  · exact B346587
  · exact B346591
  · exact B346595
  · exact B346599
  · exact B346603
  · exact B346607
  · exact B346611
  · exact B346615
  · exact B346619
  · exact B346623
  · exact B346627
  · exact B346631
  · exact B346635
  · exact B346639
  · exact B346643
  · exact B346647
  · exact B346651
  · exact B346655
  · exact B346659
  · exact B346663
  · exact B346667
  · exact B346671
  · exact B346675
  · exact B346679
  · exact B346683
  · exact B346687
  · exact B346691
  · exact B346695
  · exact B346699
  · exact B346703
  · exact B346707
  · exact B346711
  · exact B346715
  · exact B346719
  · exact B346723
  · exact B346727
  · exact B346731
  · exact B346735
  · exact B346739
  · exact B346743
  · exact B346747
  · exact B346751

theorem solution (m : ℕ) (hlo : 342753 ≤ m) (hhi : m ≤ 346753) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 85688 ≤ j := by omega
    have hj2 : j ≤ 86687 := by omega
    have hb : Blo 342753 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 86388 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
